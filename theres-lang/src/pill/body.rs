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
use crate::air::node::AirLiteral;
use crate::eair::types::{Block, Expr, ExprKind, LogicalOp};
use crate::pill;
use crate::pill::access::{Access, AccessBuilder};
use crate::pill::cfg::{AdtKind, BlockExit, Imm, Operand, Rvalue, Stmt};
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
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
    current_loop_end: Option<BasicBlock>,
}

impl<'il> PillBuilder<'il> {
    fn lower_block() -> (BasicBlock, ()) {
        todo!()
    }

    #[allow(clippy::too_many_lines)]
    fn as_operand(&mut self, expr: &Expr<'il>, bb: BasicBlock) -> (BasicBlock, Operand<'il>) {
        match &expr.kind {
            ExprKind::Lambda => {
                let ty = expr.ty;
                let lambda = ty.expect_lambda();
                let upvars = self.cx.upvars_of(lambda.did);
                let tmp = self.temporary(expr.ty);

                let rvalue = Rvalue::Adt {
                    def: AdtKind::Lambda(lambda),
                    args: upvars
                        .iter()
                        .map(|air_id| {
                            let local = *self.captures.get(air_id).unwrap();
                            Operand::Use(local.into())
                        })
                        .collect(),
                };

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: rvalue,
                    },
                );

                (bb, Operand::Use(tmp.into()))
            }

            ExprKind::Adt { def, fields } => {
                let tmp = self.temporary(expr.ty);

                let mut args = Vec::with_capacity(fields.len());

                let mut cursor = bb;
                for expr in *fields {
                    let (new_bb, op) = self.as_operand(expr, cursor);
                    cursor = new_bb;
                    args.push(op);
                }

                let rvalue = Rvalue::Adt {
                    def: AdtKind::Def(*def),
                    args,
                };

                self.cfg.push_stmt(
                    cursor,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: rvalue,
                    },
                );

                (cursor, Operand::Use(tmp.into()))
            }

            ExprKind::Lit(lit) => {
                let scalar = match lit {
                    AirLiteral::Str(..) => todo!("idfk"),
                    AirLiteral::Bool(val) => Scalar::new_bool(*val),
                    AirLiteral::Float(val) => Scalar::new_f64(*val),
                    AirLiteral::Uint(val) => Scalar::new_u64(*val),
                    AirLiteral::Int(val) => Scalar::new_i64(*val),
                };

                (bb, Operand::Imm(Imm::scalar(self.cx, scalar, expr.ty)))
            }

            ExprKind::Local(local) => {
                let lowered_local = *self.map.get(local).unwrap();
                (bb, Operand::Use(lowered_local.into()))
            }

            ExprKind::Index { base, idx } => {
                let (bb, mut base) = self.as_access(base, bb);

                let (bb, idx) = self.as_operand(idx, bb);
                let len = self.temporary(self.cx.u64()).into();
                let eval = self.temporary(self.cx.bool()).into();

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: len,
                        src: Rvalue::Length(base.finish(self.cx)),
                    },
                );

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: eval,
                        src: Rvalue::Binary {
                            op: BinOp::Lt,
                            lhs: idx,
                            rhs: Operand::Use(len),
                        },
                    },
                );

                self.cfg.push_stmt(bb, Stmt::CheckCond(Operand::Use(eval)));

                base.index(idx);
                (bb, Operand::Use(base.finish(self.cx)))
            }

            ExprKind::Upvar { upvar } => {
                let local = self.captures.get(upvar).unwrap();
                (bb, Operand::Use((*local).into()))
            }

            ExprKind::Field { base, field_idx } => {
                let (bb, mut acc) = self.as_access(base, bb);
                acc.field(*field_idx);

                (bb, Operand::Use(acc.finish(self.cx)))
            }

            ExprKind::Logical { lhs, rhs, op } => {
                let (short_case_ret, negate, binop) = match op {
                    LogicalOp::And => (
                        Imm::scalar(self.cx, Scalar::new_bool(false), self.cx.bool()),
                        true,
                        BinOp::BitAnd,
                    ),

                    LogicalOp::Or => (
                        Imm::scalar(self.cx, Scalar::new_bool(true), self.cx.bool()),
                        false,
                        BinOp::BitOr,
                    ),
                };

                let tmp = self.temporary(self.cx.bool());

                let (bb, lhs) = self.as_operand(lhs, bb);
                let lhs_true = self.cfg.new_block();
                let lhs_false = self.cfg.new_block();
                let end_bb = self.cfg.new_block();

                let cond = if negate {
                    Rvalue::Unary {
                        op: UnOp::Not,
                        val: lhs,
                    }
                } else {
                    Rvalue::Regular(lhs)
                };

                let eval = self.temporary(self.cx.bool());
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: eval.into(),
                        src: cond,
                    },
                );
                self.cfg.end_block(
                    bb,
                    BlockExit::Branch {
                        val: Operand::Use(eval.into()),
                        true_: lhs_true,
                        false_: lhs_false,
                    },
                );
                self.cfg.push_stmt(
                    lhs_true,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: Rvalue::Regular(Operand::Imm(short_case_ret)),
                    },
                );
                self.cfg.end_block(lhs_true, BlockExit::Goto(end_bb));

                let (lhs_false, val) = self.as_operand(rhs, lhs_false);

                self.cfg.push_stmt(
                    lhs_true,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: Rvalue::Binary {
                            op: binop,
                            lhs,
                            rhs: val,
                        },
                    },
                );

                self.cfg.end_block(lhs_false, BlockExit::Goto(end_bb));
                (end_bb, Operand::Use(tmp.into()))
            }

            ExprKind::List(exprs) => {
                let tmp = self.temporary(expr.ty);
                let mut members = Vec::with_capacity(exprs.len());

                let mut cursor = bb;
                for expr in *exprs {
                    let (bb, op) = self.as_operand(expr, cursor);
                    members.push(op);
                    cursor = bb;
                }

                let rvalue = Rvalue::List(members);
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: rvalue,
                    },
                );

                (cursor, Operand::Use(tmp.into()))
            }

            ExprKind::Empty => (bb, Operand::Imm(Imm::empty(self.cx, expr.ty))),

            ExprKind::Break => {
                let goto = self.current_loop_end.expect("break outside loop!");

                self.cfg.end_block(bb, BlockExit::Goto(goto));
                (
                    goto,
                    Operand::Imm(Imm::empty(self.cx, self.cx.ty_diverge())),
                )
            }

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
                let loop_end = self.cfg.new_block();
                self.current_loop_end.replace(loop_end);

                let dest = self.temporary(expr.ty);
                let bb = self.process_block(dest, body, loop_start);

                self.cfg.end_block(bb, BlockExit::Goto(loop_start));

                self.current_loop_end.take();
                (loop_end, Operand::Imm(Imm::empty(self.cx, self.cx.nil())))
            }
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

    fn as_access(&mut self, expr: &Expr<'il>, bb: BasicBlock) -> (BasicBlock, AccessBuilder<'il>) {
        match expr.kind {
            ExprKind::Field { base, field_idx } => {
                let (bb, mut base) = self.as_access(base, bb);

                base.field(field_idx);
                (bb, base)
            }

            ExprKind::Index { base, idx } => {
                // dedup
                let (bb, mut base) = self.as_access(base, bb);

                let (bb, idx) = self.as_operand(idx, bb);
                let len = self.temporary(self.cx.u64()).into();
                let eval = self.temporary(self.cx.bool()).into();

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: len,
                        src: Rvalue::Length(base.finish(self.cx)),
                    },
                );

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: eval,
                        src: Rvalue::Binary {
                            op: BinOp::Lt,
                            lhs: idx,
                            rhs: Operand::Use(len),
                        },
                    },
                );

                self.cfg.push_stmt(bb, Stmt::CheckCond(Operand::Use(eval)));

                base.index(idx);
                (bb, base)
            }

            _ => {
                let tmp = self.temporary(expr.ty);
                let (bb, src) = self.as_operand(expr, bb);
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: tmp.into(),
                        src: Rvalue::Regular(src),
                    },
                );
                (bb, AccessBuilder::new(self.cx.arena(), tmp))
            }
        }
    }

    fn temporary(&mut self, _ty: Ty<'il>) -> Local {
        todo!()
    }
}
