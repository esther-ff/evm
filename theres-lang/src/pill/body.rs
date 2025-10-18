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
use std::io::{self, Write};
use std::panic::Location;

use crate::air::AirId;
use crate::air::def::DefId;
use crate::air::node::AirLiteral;
use crate::ast;
use crate::eair::types::{Block, BodyKind, Eair, Expr, ExprKind, LogicalOp};
use crate::pill::access::{Access, AccessBuilder};
use crate::pill::cfg::{AdtKind, BlockExit, Imm, Operand, Rvalue, Stmt};
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
use crate::session::{Session, cx};
use crate::symbols::SymbolId;
use crate::types::ty::TyKind;

pub use private::Local;
use private::Locals;

#[derive(Debug)]
pub struct LocalData<'il> {
    mutbl: Constant,
    ty: Ty<'il>,
    origin: LocalOrigin,
}

#[derive(Debug)]
enum LocalOrigin {
    Temporary,
    User(SymbolId),
}

impl<'il> LocalData<'il> {
    pub fn new(mutbl: Constant, ty: Ty<'il>) -> Self {
        Self {
            mutbl,
            ty,
            origin: LocalOrigin::Temporary,
        }
    }

    pub fn new_user(mutbl: Constant, ty: Ty<'il>, name: SymbolId) -> Self {
        Self {
            mutbl,
            ty,
            origin: LocalOrigin::User(name),
        }
    }
}

use crate::{
    air::node::Constant,
    eair::types::LocalId as EairLocal,
    pill::cfg::{BasicBlock, Cfg},
    span::Span,
    types::ty::Ty,
};

#[derive(Debug)]
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
    captures: HashMap<AirId, Access<'il>>,
    current_loop_end: Option<BasicBlock>,
}

impl<'il> PillBuilder<'il> {
    #[allow(clippy::too_many_lines)]
    #[track_caller]
    fn as_operand(&mut self, expr: &Expr<'il>, mut bb: BasicBlock) -> (BasicBlock, Operand<'il>) {
        match &expr.kind {
            ExprKind::Lit(lit) => {
                use crate::air::def::IntTy;
                #[allow(clippy::cast_possible_truncation)]
                let scalar = match (lit, *expr.ty) {
                    (AirLiteral::Uint(val), TyKind::Int(size)) => match size {
                        IntTy::N8 => Scalar::new_u8(*val as u8),
                        IntTy::N16 => Scalar::new_u16(*val as u16),
                        IntTy::N32 => Scalar::new_u32(*val as u32),
                        IntTy::N64 => Scalar::new_u64(*val),
                    },

                    (AirLiteral::Int(val), TyKind::Int(size)) => match size {
                        IntTy::N8 => Scalar::new_i8(*val as i8),
                        IntTy::N16 => Scalar::new_i16(*val as i16),
                        IntTy::N32 => Scalar::new_i32(*val as i32),
                        IntTy::N64 => Scalar::new_i64(*val),
                    },

                    (AirLiteral::Bool(val), TyKind::Bool) => Scalar::new_bool(*val),

                    (AirLiteral::Float(val), TyKind::Float) => Scalar::new_f32(*val as f32),
                    (AirLiteral::Float(val), TyKind::Double) => Scalar::new_f64(*val),

                    _ => unreachable!("what the holy FUCK??"),
                };

                (bb, Operand::Imm(Imm::scalar(self.cx, scalar, expr.ty)))
            }

            ExprKind::Local(loc) => (bb, Operand::Use(self.map[loc].into())),

            ExprKind::Upvar { upvar } => (bb, Operand::Use(self.captures[upvar])),
            ExprKind::Index { base, idx } => {
                let mut acc;
                (bb, acc) = self.as_access(base, bb);
                let op;
                (bb, op) = self.as_operand(idx, bb);
                acc.index(op);
                (bb, Operand::Use(acc.finish(self.cx)))
            }

            ExprKind::Field { base, field_idx } => {
                let mut acc;
                (bb, acc) = self.as_access(base, bb);
                acc.field(*field_idx);
                (bb, Operand::Use(acc.finish(self.cx)))
            }

            ExprKind::Empty => (bb, Operand::Imm(Imm::empty(self.cx, expr.ty))),

            _ => {
                println!("{:?}", expr.kind);
                let tmp = self.temporary(expr.ty);
                bb = self.lower_expr_into(expr, bb, tmp);

                (bb, Operand::Use(tmp.into()))
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    #[track_caller]
    fn lower_expr_into(&mut self, expr: &Expr<'il>, mut bb: BasicBlock, into: Local) -> BasicBlock {
        match &expr.kind {
            ExprKind::Lambda => {
                let ty = expr.ty;
                let lambda = ty.expect_lambda();
                let upvars = self.cx.upvars_of(lambda.did);

                let rvalue = Rvalue::Adt {
                    def: AdtKind::Lambda(lambda),
                    args: upvars
                        .iter()
                        .map(|air_id| {
                            let local = *self.captures.get(air_id).unwrap();
                            Operand::Use(local)
                        })
                        .collect(),
                };

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: rvalue,
                    },
                );

                bb
            }

            ExprKind::Semi(inner) => {
                if inner.ty.is_nil() {
                    return self.lower_expr_into(inner, bb, into);
                }

                let tmp = self.temporary(inner.ty);
                bb = self.lower_expr_into(inner, bb, tmp);
                self.cfg.push_stmt(bb, Stmt::LocalLive(into));
                bb
            }

            ExprKind::Adt { def, fields } => {
                let mut args = Vec::with_capacity(fields.len());

                for expr in *fields {
                    let op;
                    (bb, op) = self.as_operand(expr, bb);
                    args.push(op);
                }

                let rvalue = Rvalue::Adt {
                    def: AdtKind::Def(*def),
                    args,
                };

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: rvalue,
                    },
                );

                bb
            }

            ExprKind::Lit(lit) => {
                let scalar = match lit {
                    AirLiteral::Str(..) => todo!("idfk"),
                    AirLiteral::Bool(val) => Scalar::new_bool(*val),
                    AirLiteral::Float(val) => Scalar::new_f64(*val),
                    AirLiteral::Uint(val) => Scalar::new_u64(*val),
                    AirLiteral::Int(val) => Scalar::new_i64(*val),
                };

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Imm(Imm::scalar(self.cx, scalar, expr.ty))),
                    },
                );

                bb
            }

            ExprKind::Local(local) => {
                let lowered_local = *self.map.get(local).unwrap();
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Use(lowered_local.into())),
                    },
                );
                bb
            }

            ExprKind::Index { base, idx } => {
                let mut acc;
                (bb, acc) = self.process_index(base, idx, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Use(acc.finish(self.cx))),
                    },
                );
                bb
            }

            ExprKind::Upvar { upvar } => {
                let local = self.captures.get(upvar).unwrap();

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Use(*local)),
                    },
                );
                bb
            }

            ExprKind::Field { base, field_idx } => {
                let mut acc;
                (bb, acc) = self.as_access(base, bb);
                acc.field(*field_idx);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Use(acc.finish(self.cx))),
                    },
                );

                bb
            }

            ExprKind::Logical { lhs, rhs, op } => self.process_logical_op(lhs, rhs, bb, into, *op),

            ExprKind::List(exprs) => self.process_list(into, exprs, bb),

            ExprKind::Empty => {
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Imm(Imm::empty(self.cx, expr.ty))),
                    },
                );

                bb
            }

            ExprKind::Break => {
                let goto = self.current_loop_end.expect("break outside loop!");

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Imm(Imm::empty(
                            self.cx,
                            self.cx.ty_diverge(),
                        ))),
                    },
                );

                self.cfg.end_block(bb, BlockExit::Goto(goto));
                goto
            }

            ExprKind::Call { callee, args } => {
                let fun;
                (bb, fun) = self.as_operand(callee, bb);
                let ret = into;
                let mut call_args = Vec::with_capacity(args.len());

                for arg in *args {
                    let op;
                    (bb, op) = self.as_operand(arg, bb);
                    call_args.push(op);
                }

                let stmt = Stmt::Call {
                    fun,
                    ret: ret.into(),
                    args: call_args,
                };

                self.cfg.push_stmt(bb, stmt);
                bb
            }

            ExprKind::Binary { lhs, rhs, op } => {
                let l_lhs;
                let l_rhs;
                (bb, l_lhs) = self.as_operand(lhs, bb);
                (bb, l_rhs) = self.as_operand(rhs, bb);

                let op = (*op).into();
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Binary {
                            op,
                            lhs: l_lhs,
                            rhs: l_rhs,
                        },
                    },
                );

                bb
            }

            ExprKind::Assign {
                lvalue: lhs,
                rvalue: rhs,
                // USE THIS!
                from_lowering: _,
            } => {
                if let ExprKind::Local(loc) = lhs.kind
                    && let ExprKind::Call { callee, args } = rhs.kind
                {
                    let fun;
                    (bb, fun) = self.as_operand(callee, bb);
                    let mut call_args = Vec::with_capacity(args.len());

                    for arg in args {
                        let op;
                        (bb, op) = self.as_operand(arg, bb);
                        call_args.push(op);
                    }

                    let stmt = Stmt::Call {
                        fun,
                        ret: self.map[&loc].into(),
                        args: call_args,
                    };

                    self.cfg.push_stmt(bb, stmt);
                    return bb;
                }

                let rvalue;
                let lvalue;
                (bb, rvalue) = self.as_rvalue(rhs, bb);
                (bb, lvalue) = self.as_access_full(lhs, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: lvalue,
                        src: rvalue,
                    },
                );

                if !into.is_dummy() {
                    self.cfg.push_stmt(bb, Stmt::LocalLive(into));
                }

                bb
            }

            ExprKind::Unary { operand, op } => {
                let val;
                (bb, val) = self.as_operand(operand, bb);
                let dest = into.into();
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest,
                        src: Rvalue::Unary {
                            op: match *op {
                                ast::UnaryOp::Negation => UnOp::Neg,
                                ast::UnaryOp::Not => UnOp::Not,
                            },
                            val,
                        },
                    },
                );

                bb
            }

            ExprKind::If {
                cond,
                true_,
                false_,
            } => self.process_if_expr(into, cond, true_, *false_, bb),

            ExprKind::Return(expr) => {
                if let Some(expr) = expr {
                    let ret;
                    (bb, ret) = self.as_rvalue(expr, bb);
                    self.cfg.push_stmt(
                        bb,
                        Stmt::Assign {
                            dest: Local::ret_access(),
                            src: ret,
                        },
                    );
                }

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: into.into(),
                        src: Rvalue::Regular(Operand::Imm(Imm::empty(
                            self.cx,
                            self.cx.ty_diverge(),
                        ))),
                    },
                );

                self.cfg.end_block(bb, BlockExit::Goto(BasicBlock::DUMMY));

                bb
            }

            ExprKind::Block(block) => self.process_block(into, block, bb),

            ExprKind::Loop(body) => {
                let dest = into;
                let loop_start = self.cfg.new_block();
                self.cfg.end_block(bb, BlockExit::Goto(loop_start));
                let loop_end = self.cfg.new_block();
                self.current_loop_end.replace(loop_end);

                let bb = self.process_block(dest, body, loop_start);

                self.cfg.end_block(bb, BlockExit::Goto(loop_start));

                self.current_loop_end.take();

                self.cfg.push_stmt(loop_end, Stmt::LocalLive(into));
                loop_end
            }
        }
    }

    fn process_if_expr(
        &mut self,
        local: Local,
        cond: &Expr<'il>,
        true_: &Expr<'il>,
        false_: Option<&Expr<'il>>,
        bb: BasicBlock,
    ) -> BasicBlock {
        let local = local.into();
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
                dest: local,
                src: cond_succ,
            },
        );

        if let Some(cond_fail) = cond_fail {
            self.cfg.push_stmt(
                bb_false_end,
                Stmt::Assign {
                    dest: local,
                    src: cond_fail,
                },
            );
        }

        self.cfg.end_block(bb_true_end, BlockExit::Goto(bb_end));
        self.cfg.end_block(bb_false_end, BlockExit::Goto(bb_end));

        bb_end
    }

    fn process_bin_op(
        &mut self,
        lhs: &Expr<'il>,
        rhs: &Expr<'il>,
        op: BinOp,
        mut bb: BasicBlock,
        local: Local,
    ) -> BasicBlock {
        let (new_bb, lhs) = self.as_operand(lhs, bb);
        bb = new_bb;
        let (new_bb, rhs) = self.as_operand(rhs, bb);
        bb = new_bb;

        let dest = local.into();

        self.cfg.push_stmt(
            bb,
            Stmt::Assign {
                dest,
                src: Rvalue::Binary { op, lhs, rhs },
            },
        );

        bb
    }

    fn process_logical_op(
        &mut self,
        lhs: &Expr<'il>,
        rhs: &Expr<'il>,
        bb: BasicBlock,
        tmp: Local,
        op: LogicalOp,
    ) -> BasicBlock {
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
        end_bb
    }

    fn process_list(&mut self, tmp: Local, exprs: &[Expr<'il>], mut bb: BasicBlock) -> BasicBlock {
        let mut members = Vec::with_capacity(exprs.len());
        let start = bb;
        for expr in exprs {
            let op;
            (bb, op) = self.as_operand(expr, bb);
            members.push(op);
        }

        let rvalue = Rvalue::List(members);
        self.cfg.push_stmt(
            start,
            Stmt::Assign {
                dest: tmp.into(),
                src: rvalue,
            },
        );

        bb
    }

    fn process_block(&mut self, dest: Local, block: &Block<'il>, mut bb: BasicBlock) -> BasicBlock {
        let dest = dest.into();
        let exprs = block.exprs();

        dbg!(block);

        for (ix, expr) in exprs.iter().enumerate() {
            if ix == exprs.len() - 1 {
                let op;
                (bb, op) = self.as_rvalue(expr, bb);

                // if let ExprKind::Semi(inner) = expr.kind {
                //     let tmp = self.temporary(inner.ty);
                //     bb = self.lower_expr_into(inner, bb, tmp);
                //     self.cfg.push_stmt(
                //         bb,
                //         Stmt::Assign {
                //             dest: tmp.into(),
                //             src: Rvalue::Regular(Operand::Imm(Imm::empty(self.cx, self.cx.nil()))),
                //         },
                //     );
                //     break;
                // }

                self.cfg.push_stmt(bb, Stmt::Assign { dest, src: op });
                break;
            }

            #[allow(clippy::single_match_else)]
            match expr.kind {
                ExprKind::Assign { .. } => bb = self.lower_expr_into(expr, bb, Local::DUMMY),

                ExprKind::Semi(inner) => {
                    let tmp = self.temporary(inner.ty);
                    bb = self.lower_expr_into(inner, bb, tmp);
                }

                _ => {
                    println!("ignored expr: {expr:#?}, it's ty: {}", expr.ty);
                    let tmp = self.temporary(expr.ty);
                    dbg!(tmp);
                    bb = self.lower_expr_into(expr, bb, tmp);
                }
            }
        }

        bb
    }

    fn process_index(
        &mut self,
        base: &Expr<'il>,
        idx: &Expr<'il>,
        bb: BasicBlock,
    ) -> (BasicBlock, AccessBuilder<'il>) {
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

    #[track_caller]
    fn as_rvalue(&mut self, expr: &Expr<'il>, mut bb: BasicBlock) -> (BasicBlock, Rvalue<'il>) {
        match expr.kind {
            ExprKind::Binary { lhs, rhs, op } => {
                let l_lhs;
                (bb, l_lhs) = self.as_operand(lhs, bb);
                let l_rhs;
                (bb, l_rhs) = self.as_operand(rhs, bb);

                (
                    bb,
                    Rvalue::Binary {
                        op: op.into(),
                        lhs: l_lhs,
                        rhs: l_rhs,
                    },
                )
            }

            ExprKind::Adt { def, fields } => {
                let mut args = Vec::with_capacity(fields.len());
                for field in fields {
                    let val;
                    (bb, val) = self.as_operand(field, bb);
                    args.push(val);
                }

                (
                    bb,
                    Rvalue::Adt {
                        def: AdtKind::Def(def),
                        args,
                    },
                )
            }

            ExprKind::Lambda => {
                let ty = expr.ty;
                let lambda = ty.expect_lambda();
                let upvars = self.cx.upvars_of(lambda.did);

                let rvalue = Rvalue::Adt {
                    def: AdtKind::Lambda(lambda),
                    args: upvars
                        .iter()
                        .map(|air_id| {
                            let local = *self.captures.get(air_id).unwrap();
                            Operand::Use(local)
                        })
                        .collect(),
                };

                (bb, rvalue)
            }

            ExprKind::Unary { operand, op } => {
                let (bb, val) = self.as_operand(operand, bb);
                (
                    bb,
                    Rvalue::Unary {
                        op: match op {
                            ast::UnaryOp::Negation => UnOp::Neg,
                            ast::UnaryOp::Not => UnOp::Not,
                        },
                        val,
                    },
                )
            }

            ExprKind::Semi(inner) => {
                println!("Semi! at {}", Location::caller());
                let tmp = self.temporary(inner.ty);
                bb = self.lower_expr_into(inner, bb, tmp);
                (
                    bb,
                    Rvalue::Regular(Operand::Imm(Imm::empty(self.cx, self.cx.nil()))),
                )
            }

            ExprKind::Field { .. } | ExprKind::Index { .. } => {
                let acc;
                (bb, acc) = self.as_access_full(expr, bb);

                (bb, Rvalue::Regular(Operand::Use(acc)))
            }

            _ => {
                println!("expr to as_rvalue: {expr:?} ");
                let (bb, op) = self.as_operand(expr, bb);

                (bb, Rvalue::Regular(op))
            }
        }
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

            ExprKind::Index { base, idx } => self.process_index(base, idx, bb),

            ExprKind::Local(loc) => (bb, AccessBuilder::new(self.cx.arena(), self.map[&loc])),

            ExprKind::Upvar { upvar } => (
                bb,
                AccessBuilder::new(self.cx.arena(), self.captures[&upvar].get_base()),
            ),

            _ => {
                println!("expr to as_access: {expr:?}");
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

    #[track_caller]
    #[inline]
    fn temporary(&mut self, ty: Ty<'il>) -> Local {
        let id = self.locals.push(LocalData {
            mutbl: Constant::Yes,
            ty,
            origin: LocalOrigin::Temporary,
        });

        println!(
            "loc: {} id: {}, ty: {}",
            Location::caller(),
            id.to_usize(),
            ty
        );
        id
    }
}

pub fn build_pill<'cx>(cx: &'cx Session<'cx>, body: &Eair<'cx>, did: DefId) -> Pill<'cx> {
    let mut captures = HashMap::new();
    let cap = body.params.len() + body.locals.len() + 1;
    let mut locals = Locals::new_from_vec(Vec::with_capacity(cap));

    let body_entry = body
        .entry
        .as_ref()
        .expect("body should have an entry point!");
    let _ = locals.push(LocalData {
        mutbl: Constant::Yes,
        ty: body_entry.ty,
        origin: LocalOrigin::Temporary,
    });

    let mut extra = 0;
    // fix! after trestig :3
    if let BodyKind::Lambda = body.kind {
        extra += 1;
        let ty = cx.def_type_of(did);
        let upvars = cx.upvars_of(did);
        let env = locals.push(LocalData {
            mutbl: Constant::No,
            ty,
            origin: LocalOrigin::Temporary,
        });
        locals.reserve(upvars.len() + 1);

        let parent = cx.air_get_parent(did);
        let types = cx.typeck(parent);

        for var in upvars {
            let ty = types.node_ty(*var);
            let acc = Access::base(env);

            let _ = locals.push(LocalData {
                mutbl: Constant::Yes,
                ty,
                origin: LocalOrigin::Temporary,
            });

            captures.insert(*var, acc);
        }
    }

    for _param in body.params.iter() {
        todo!()
    }

    let mut map = HashMap::with_capacity(body.locals.len());
    for (local, data) in body.locals.iter().enumerate() {
        assert!(data.ty().maybe_infer().is_none());
        let id = locals.push((*data).into());
        map.insert(EairLocal::new_usize(local), id);
    }

    let mut builder = PillBuilder {
        cx,
        cfg: Cfg::new(),
        locals,
        captures,
        map,
        current_loop_end: None,
    };

    let block = builder.cfg.new_block();
    // dbg!(body_entry);
    let bb = builder.lower_expr_into(body_entry, block, Local::ZERO);
    builder.cfg.end_block(bb, BlockExit::Return);

    Pill {
        span: body.span,
        arg_count: body.params.len() + extra,
        cfg: builder.cfg,
        locals: builder.locals,
    }
}

pub fn dump_pill(w: &mut dyn Write, pill: &Pill<'_>, did: DefId) -> io::Result<()> {
    const INDENT: &str = "      ";

    write!(w, "fun {}(", cx(|cx| cx.name_of(did)))?;

    if let Some(args) = pill.locals.as_slice().get(1..pill.arg_count) {
        for (ix, arg) in args.iter().enumerate() {
            write!(
                w,
                "{mutbl} _{ix}: {ty}",
                ty = arg.ty,
                mutbl = match arg.mutbl {
                    Constant::Yes => "mut",
                    Constant::No => "const",
                }
            )?;

            if ix != args.len() - 1 {
                write!(w, " ,")?;
            }
        }
    }

    writeln!(w, ") => {ty} {{", ty = pill.locals[Local::ZERO].ty)?;

    if let Some(args) = pill.locals.as_slice().get(pill.arg_count..) {
        for (ix, arg) in args
            .iter()
            .chain(std::iter::once(&pill.locals[Local::ZERO]))
            .enumerate()
        {
            write!(
                w,
                "    let {mutbl} _{ix}: {ty}",
                ty = arg.ty,
                mutbl = match arg.mutbl {
                    Constant::Yes => "mut",
                    Constant::No => "const",
                }
            )?;

            if let LocalOrigin::User(v) = arg.origin {
                write!(w, " ({})", v.get_interned())?;
            }

            writeln!(w)?;
        }
    }

    writeln!(w)?;

    for (id, bb) in pill.cfg.blocks() {
        writeln!(w, "    bb{}:", id.to_usize())?;

        for stmt in bb.stmts() {
            match stmt {
                Stmt::Call { fun, ret, args } => {
                    if args.is_empty() {
                        writeln!(w, "{INDENT}Call ({fun:#?}) => {ret:?}")
                    } else {
                        writeln!(w, "{INDENT}Call ({fun:#?}) {args:?} => {ret:?}")
                    }?;
                }

                Stmt::Nop => writeln!(w, "{INDENT}Nop")?,

                Stmt::Assign { dest, src } => writeln!(w, "{INDENT}{dest:?} = {src:?}")?,

                Stmt::CheckCond(cond) => writeln!(w, "{INDENT}CheckCond({cond:?})")?,

                Stmt::LocalLive(local) => writeln!(w, "{INDENT}Live(_{})", local.to_usize())?,
            }
        }

        writeln!(w)?;
        write!(w, "{INDENT}exit: ")?;

        if let Some(exit) = bb.exit() {
            match exit {
                BlockExit::Goto(b) => writeln!(w, "goto bb{}", b.to_usize()),
                BlockExit::Branch { val, true_, false_ } => writeln!(
                    w,
                    "branch ({val:?}) {{ true: bb{true_bb}, false: bb{false_bb} }}",
                    true_bb = true_.to_usize(),
                    false_bb = false_.to_usize()
                ),
                BlockExit::Return => writeln!(w, "return"),
            }
        } else {
            write!(w, "{INDENT}<broken: no exit!>")
        }?;

        writeln!(w)?;
    }

    writeln!(w, "}}")
}
