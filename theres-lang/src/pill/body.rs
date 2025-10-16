mod private {
    use crate::pill::access::Access;

    crate::newtyped_index!(Local, LocalMap, LocalVec, LocalsRef);

    pub type Locals<'il> = LocalVec<super::LocalData<'il>>;

    impl Local {
        pub(super) fn ret_place() -> Local {
            Local::ZERO
        }

        pub(super) fn ret_access() -> Access<'static> {
            Self::ret_place().into()
        }
    }

    impl From<Local> for Access<'_> {
        fn from(value: Local) -> Self {
            Access::base(value)
        }
    }
}

use std::collections::HashMap;

use crate::air::AirId;
use crate::eair::types::{Block, Expr, ExprKind};
use crate::pill;
use crate::pill::access::{Access, AccessBuilder};
use crate::pill::cfg::{BlockExit, Imm, Operand, Rvalue, Stmt};
use crate::session::Session;

pub use private::Local;
use private::Locals;

struct LocalData<'il> {
    mutbl: Constant,
    ty: Ty<'il>,
}

use crate::{
    air::node::Constant,
    eair::types::LocalId as EairLocal,
    pill::cfg::{BasicBlock, Cfg},
    span::Span,
    types::ty::Ty,
};

pub struct Pill<'il> {
    span: Span,
    arg_count: usize,
    cfg: Cfg<'il>,
    locals: Locals<'il>,
}

struct PillBuilder<'il> {
    cx: &'il Session<'il>,
    cfg: Cfg<'il>,
    locals: Locals<'il>,
    map: HashMap<EairLocal, Local>,
    captures: HashMap<AirId, Local>,
}

impl<'il> PillBuilder<'il> {
    fn lower_block() -> (BasicBlock, ()) {
        todo!()
    }

    #[allow(clippy::too_many_lines)]
    fn as_operand(&mut self, expr: &Expr<'il>, bb: BasicBlock) -> (BasicBlock, Operand<'il>) {
        match &expr.kind {
            ExprKind::Call { callee, args } => {
                let (bb, fun) = self.as_operand(callee, bb);
                let ret = self.temporary(expr.ty);
                let mut call_args = Vec::with_capacity(args.len());

                let mut current_bb = bb;
                for arg in *args {
                    let (bb, op) = self.as_operand(arg, current_bb);
                    call_args.push(op);
                    current_bb = bb;
                }

                let stmt = Stmt::Call {
                    fun,
                    ret,
                    args: call_args,
                };

                self.cfg.push_stmt(current_bb, stmt);
                (current_bb, Operand::Use(Access::base(ret)))
            }

            ExprKind::Binary { lhs, rhs, op } => {
                let (bb, lhs) = self.as_operand(lhs, bb);
                let (bb, rhs) = self.as_operand(rhs, bb);

                let dest = self.temporary(expr.ty).into();

                let op = (*op).into();
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest,
                        src: Rvalue::Binary { op, lhs, rhs },
                    },
                );

                (bb, Operand::Use(dest))
            }

            ExprKind::Assign {
                lvalue,
                rvalue,
                // USE THIS!
                from_lowering: _,
            } => {
                let (bb, rvalue) = self.as_rvalue(rvalue, bb);
                let (bb, lvalue) = self.as_access_full(lvalue, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: lvalue,
                        src: rvalue,
                    },
                );

                (bb, Operand::Imm(Imm::empty(self.cx, self.cx.nil())))
            }

            ExprKind::Unary { operand, op } => {
                let (bb, val) = self.as_operand(operand, bb);
                let dest = self.temporary(expr.ty).into();

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest,
                        src: Rvalue::Unary {
                            op: match *op {
                                crate::ast::UnaryOp::Negation => pill::op::UnOp::Neg,
                                crate::ast::UnaryOp::Not => pill::op::UnOp::Not,
                            },
                            val,
                        },
                    },
                );

                (bb, Operand::Use(dest))
            }

            ExprKind::If {
                cond,
                true_,
                false_,
            } => {
                let tmp = self.temporary(expr.ty).into();
                let (bb, cond) = self.as_operand(cond, bb);

                let bb_true = self.cfg.new_block();
                let bb_false = self.cfg.new_block();

                self.cfg.end_block(
                    bb,
                    BlockExit::Branch {
                        val: cond,
                        true_: bb_true,
                        false_: bb_false,
                    },
                );

                let bb_end = self.cfg.new_block();

                let (bb_true_end, cond_succ) = self.as_rvalue(true_, bb_true);
                let (bb_false_end, cond_fail) = match false_ {
                    None => (bb_end, None),
                    Some(expr) => {
                        let (bb_false_end, cond_fail) = self.as_rvalue(expr, bb_false);
                        (bb_false_end, Some(cond_fail))
                    }
                };

                self.cfg.push_stmt(
                    bb_true_end,
                    Stmt::Assign {
                        dest: tmp,
                        src: cond_succ,
                    },
                );

                if let Some(cond_fail) = cond_fail {
                    self.cfg.push_stmt(
                        bb_false_end,
                        Stmt::Assign {
                            dest: tmp,
                            src: cond_fail,
                        },
                    );
                }

                self.cfg.end_block(bb_true_end, BlockExit::Goto(bb_end));
                self.cfg.end_block(bb_false_end, BlockExit::Goto(bb_end));

                (bb_end, Operand::Use(tmp))
            }

            ExprKind::Return(expr) => {
                let op = Operand::Imm(Imm::empty(self.cx, self.cx.ty_diverge()));
                let mut bb = bb;
                if let Some(expr) = expr {
                    let (next_bb, ret) = self.as_rvalue(expr, bb);
                    self.cfg.push_stmt(
                        bb,
                        Stmt::Assign {
                            dest: Local::ret_access(),
                            src: ret,
                        },
                    );

                    bb = next_bb;
                }

                self.cfg.end_block(bb, BlockExit::Goto(BasicBlock::DUMMY));

                (bb, op)
            }

            ExprKind::Block(block) => {
                let dest = self.temporary(expr.ty).into();
                let mut cursor = bb;
                let exprs = block.exprs();
                for (ix, expr) in exprs.iter().enumerate() {
                    let (bb, op) = self.as_rvalue(expr, cursor);
                    cursor = bb;

                    if ix == exprs.len() - 1 {
                        self.cfg.push_stmt(cursor, Stmt::Assign { dest, src: op });
                    }
                }

                (cursor, Operand::Use(dest))
            }

            ExprKind::Loop(body) => {
                let loop_start = self.cfg.new_block();
                self.cfg.end_block(bb, BlockExit::Goto(loop_start));

                let dest = self.temporary(expr.ty);
                let bb = self.process_block(dest, body, loop_start);

                self.cfg.end_block(bb, BlockExit::Goto(loop_start));
                let loop_end = self.cfg.new_block();

                (loop_end, Operand::Imm(Imm::empty(self.cx, self.cx.nil())))
            }

            _ => todo!(),
        }
    }

    fn process_block(&mut self, dest: Local, block: &Block<'il>, bb: BasicBlock) -> BasicBlock {
        let dest = dest.into();
        let mut cursor = bb;
        let exprs = block.exprs();

        for (ix, expr) in exprs.iter().enumerate() {
            let (bb, op) = self.as_rvalue(expr, cursor);
            cursor = bb;

            if ix == exprs.len() - 1 {
                self.cfg.push_stmt(cursor, Stmt::Assign { dest, src: op });
            }
        }

        cursor
    }

    fn as_rvalue(&mut self, _expr: &Expr<'il>, _bb: BasicBlock) -> (BasicBlock, Rvalue<'il>) {
        todo!()
    }

    fn as_access_full(&mut self, expr: &Expr<'il>, bb: BasicBlock) -> (BasicBlock, Access<'il>) {
        let (bb, mut builder) = self.as_access(expr, bb);
        (bb, builder.finish(self.cx))
    }

    fn as_access(
        &mut self,
        _expr: &Expr<'il>,
        _bb: BasicBlock,
    ) -> (BasicBlock, AccessBuilder<'il>) {
        todo!()
    }

    fn temporary(&mut self, _ty: Ty<'il>) -> Local {
        todo!()
    }
}
