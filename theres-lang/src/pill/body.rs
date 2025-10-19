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

use std::collections::{HashMap, HashSet};
use std::io::{self, Write};

use crate::air::AirId;
use crate::air::def::DefId;
use crate::air::node::{AirLiteral, Constant};
use crate::ast;
use crate::eair::types::{
    Block, BodyKind, Expr, ExprKind, LocalId as EairLocal, LogicalOp, ParamId,
};
use crate::pill::access::{Access, AccessBuilder};
use crate::pill::cfg::{AdtKind, BasicBlock, BlockExitKind, Cfg, Imm, Operand, Rvalue, StmtKind};
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
use crate::session::{Session, cx};
use crate::span::Span;
use crate::symbols::SymbolId;
use crate::types::ty::{Ty, TyKind};

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
    Param(Option<SymbolId>),
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
    params: HashMap<ParamId, Local>,
    alive: HashSet<Local>,
}

impl<'il> PillBuilder<'il> {
    fn live(&mut self, bb: BasicBlock, local: Local, span: Span) {
        if !local.is_dummy() && !self.alive.contains(&local) {
            self.cfg.live(bb, span, local);
            self.alive.insert(local);
        }
    }

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

                (
                    bb,
                    Operand::Imm(Imm::scalar(self.cx, scalar, expr.ty, expr.span)),
                )
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

            ExprKind::Empty => (bb, Operand::Imm(Imm::empty(self.cx, expr.ty, expr.span))),

            _ => {
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
            ExprKind::Param(..) => todo!(),
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

                self.cfg.assign(bb, into.into(), rvalue, expr.span);

                bb
            }

            ExprKind::Semi(inner) => {
                if inner.ty.is_nil() {
                    return self.lower_expr_into(inner, bb, into);
                }

                let tmp = self.temporary(inner.ty);
                bb = self.lower_expr_into(inner, bb, tmp);
                self.cfg.live(bb, expr.span, into);
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

                self.cfg.assign(bb, into.into(), rvalue, expr.span);

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

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Imm(Imm::scalar(
                        self.cx, scalar, expr.ty, expr.span,
                    ))),
                    expr.span,
                );

                bb
            }

            ExprKind::Local(local) => {
                let lowered_local = *self.map.get(local).unwrap();
                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Use(lowered_local.into())),
                    expr.span,
                );
                bb
            }

            ExprKind::Index { base, idx } => {
                let mut acc;
                (bb, acc) = self.process_index(base, idx, bb);

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Use(acc.finish(self.cx))),
                    expr.span,
                );
                bb
            }

            ExprKind::Upvar { upvar } => {
                let local = self.captures.get(upvar).unwrap();

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Use(*local)),
                    expr.span,
                );
                bb
            }

            ExprKind::Field { base, field_idx } => {
                let mut acc;
                (bb, acc) = self.as_access(base, bb);
                acc.field(*field_idx);

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Use(acc.finish(self.cx))),
                    expr.span,
                );

                bb
            }

            ExprKind::Logical { lhs, rhs, op } => self.process_logical_op(lhs, rhs, bb, into, *op),

            ExprKind::List(exprs) => self.process_list(into, exprs, bb, expr.span),

            ExprKind::Empty => {
                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Imm(Imm::empty(self.cx, expr.ty, expr.span))),
                    expr.span,
                );

                bb
            }

            // TODO: dedup somewhere too
            ExprKind::Break => {
                let goto = self.current_loop_end.expect("break outside loop!");

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Imm(Imm::empty(
                        self.cx,
                        self.cx.types.diverges,
                        expr.span,
                    ))),
                    expr.span,
                );

                self.cfg.goto(bb, goto, expr.span);
                goto
            }

            // TODO: dedup with the special case in assign
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

                self.cfg.call(bb, fun, call_args, ret.into(), expr.span);

                self.live(bb, ret, expr.span);
                bb
            }

            ExprKind::Binary { lhs, rhs, op } => {
                let l_lhs;
                let l_rhs;
                (bb, l_lhs) = self.as_operand(lhs, bb);
                (bb, l_rhs) = self.as_operand(rhs, bb);

                let op = (*op).into();
                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Binary {
                        op,
                        lhs: l_lhs,
                        rhs: l_rhs,
                    },
                    expr.span,
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

                    self.cfg
                        .call(bb, fun, call_args, self.map[&loc].into(), rhs.span);
                    self.live(bb, self.map[&loc], rhs.span);
                    return bb;
                }

                let rvalue;
                let lvalue;
                (bb, rvalue) = self.as_rvalue(rhs, bb);
                (bb, lvalue) = self.as_access_full(lhs, bb);

                self.cfg.assign(bb, lvalue, rvalue, expr.span);

                if let ExprKind::Local(loc) = lhs.kind {
                    self.live(bb, self.map[&loc], expr.span);
                }

                bb
            }

            ExprKind::Unary { operand, op } => {
                let val;
                (bb, val) = self.as_operand(operand, bb);
                let dest = into.into();
                self.cfg.assign(
                    bb,
                    dest,
                    Rvalue::Unary {
                        op: match *op {
                            ast::UnaryOp::Negation => UnOp::Neg,
                            ast::UnaryOp::Not => UnOp::Not,
                        },
                        val,
                    },
                    expr.span,
                );

                bb
            }

            ExprKind::If {
                cond,
                true_,
                false_,
            } => self.process_if_expr(into, cond, true_, *false_, bb),

            ExprKind::Return(ret_expr) => {
                if let Some(expr) = ret_expr {
                    let ret;
                    (bb, ret) = self.as_rvalue(expr, bb);
                    self.cfg.assign(bb, Local::ret_access(), ret, expr.span);
                }

                self.cfg.assign(
                    bb,
                    into.into(),
                    Rvalue::Regular(Operand::Imm(Imm::empty(
                        self.cx,
                        self.cx.types.diverges,
                        expr.span,
                    ))),
                    expr.span,
                );

                self.cfg.live(bb, expr.span, Local::ret_place());
                self.cfg.dummy_goto(bb, expr.span);

                bb
            }

            ExprKind::Block(block) => self.process_block(into, block, bb),

            ExprKind::Loop(body) => {
                let dest = into;
                let loop_start = self.cfg.new_block();
                self.cfg.goto(bb, loop_start, expr.span);
                let loop_end = self.cfg.new_block();
                self.current_loop_end.replace(loop_end);

                let bb = self.process_block(dest, body, loop_start);

                self.cfg.goto(bb, loop_start, expr.span);
                self.current_loop_end.take();
                self.cfg.live(bb, Span::DUMMY, into);
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
        let cond_span = cond.span;
        let loc = local;
        let local = local.into();
        let (bb, cond) = self.as_operand(cond, bb);

        let bb_true = self.cfg.new_block();
        let bb_false = self.cfg.new_block();

        self.cfg.branch(bb, cond, bb_true, bb_false, cond_span);

        let bb_end = self.cfg.new_block();

        let (bb_true_end, cond_succ) = self.as_rvalue(true_, bb_true);
        let (bb_false_end, cond_fail) = match false_ {
            None => (bb_end, None),
            Some(expr) => {
                let (bb_false_end, cond_fail) = self.as_rvalue(expr, bb_false);
                (bb_false_end, Some(cond_fail))
            }
        };

        self.cfg.assign(bb_true_end, local, cond_succ, true_.span);

        if let Some(cond_fail) = cond_fail {
            self.cfg
                .assign(bb_false_end, local, cond_fail, false_.unwrap().span);
        }

        self.cfg.live(bb_end, Span::DUMMY, loc);
        self.cfg.goto(bb_true_end, bb_end, Span::DUMMY);
        self.cfg.goto(bb_false_end, bb_end, Span::DUMMY);

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
        let span = Span::between(lhs.span, rhs.span);
        let (new_bb, lhs) = self.as_operand(lhs, bb);
        bb = new_bb;
        let (new_bb, rhs) = self.as_operand(rhs, bb);
        bb = new_bb;

        let dest = local.into();

        self.cfg
            .assign(bb, dest, Rvalue::Binary { op, lhs, rhs }, span);

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
                Imm::scalar(
                    self.cx,
                    Scalar::new_bool(false),
                    self.cx.types.bool,
                    Span::DUMMY,
                ),
                true,
                BinOp::BitAnd,
            ),

            LogicalOp::Or => (
                Imm::scalar(
                    self.cx,
                    Scalar::new_bool(true),
                    self.cx.types.bool,
                    Span::DUMMY,
                ),
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

        let eval = self.temporary(self.cx.types.bool);
        self.cfg.assign(bb, eval.into(), cond, Span::DUMMY);

        self.live(bb, eval, Span::DUMMY);
        self.cfg.branch(
            bb,
            Operand::Use(eval.into()),
            lhs_true,
            lhs_false,
            Span::DUMMY,
        );

        self.cfg.assign(
            lhs_true,
            tmp.into(),
            Rvalue::Regular(Operand::Imm(short_case_ret)),
            Span::DUMMY,
        );

        self.cfg.goto(lhs_true, end_bb, Span::DUMMY);
        let (lhs_false, val) = self.as_operand(rhs, lhs_false);

        self.cfg.assign(
            lhs_false,
            tmp.into(),
            Rvalue::Binary {
                op: binop,
                lhs,
                rhs: val,
            },
            Span::DUMMY,
        );

        self.live(end_bb, tmp, Span::DUMMY);
        self.cfg.goto(lhs_false, end_bb, Span::DUMMY);
        end_bb
    }

    fn process_list(
        &mut self,
        tmp: Local,
        exprs: &[Expr<'il>],
        mut bb: BasicBlock,
        span: Span,
    ) -> BasicBlock {
        let mut members = Vec::with_capacity(exprs.len());
        for expr in exprs {
            let op;
            (bb, op) = self.as_operand(expr, bb);
            members.push(op);
        }

        let rvalue = Rvalue::List(members);
        self.cfg.assign(bb, tmp.into(), rvalue, span);
        bb
    }

    fn process_block(&mut self, dest: Local, block: &Block<'il>, mut bb: BasicBlock) -> BasicBlock {
        let dest = dest.into();
        let exprs = block.exprs();

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

                self.cfg.assign(bb, dest, op, expr.span);
                break;
            }

            #[allow(clippy::single_match_else)]
            match expr.kind {
                ExprKind::Assign { .. } => bb = self.lower_expr_into(expr, bb, Local::DUMMY),

                ExprKind::Semi(inner) => {
                    let tmp = self.temporary(inner.ty);
                    bb = self.lower_expr_into(inner, bb, tmp);
                    self.live(bb, tmp, inner.span);
                }

                _ => {
                    let tmp = self.temporary(expr.ty);
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
        let span = Span::between(base.span, idx.span);
        let idx_span = idx.span;
        let (bb, mut base) = self.as_access(base, bb);

        let (bb, idx) = self.as_operand(idx, bb);
        let len = self.temporary(self.cx.types.u64).into();
        let eval = self.temporary(self.cx.types.bool).into();

        self.cfg
            .assign(bb, len, Rvalue::Length(base.finish(self.cx)), idx_span);

        self.cfg.assign(
            bb,
            eval,
            Rvalue::Binary {
                op: BinOp::Lt,
                lhs: idx,
                rhs: Operand::Use(len),
            },
            idx_span,
        );

        self.cfg.check(bb, Operand::Use(eval), span);

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
                let tmp = self.temporary(inner.ty);
                bb = self.lower_expr_into(inner, bb, tmp);
                (
                    bb,
                    Rvalue::Regular(Operand::Imm(Imm::empty(
                        self.cx,
                        self.cx.types.nil,
                        inner.span,
                    ))),
                )
            }

            ExprKind::Field { .. } | ExprKind::Index { .. } => {
                let acc;
                (bb, acc) = self.as_access_full(expr, bb);

                (bb, Rvalue::Regular(Operand::Use(acc)))
            }

            _ => {
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
                let tmp = self.temporary(expr.ty);
                let (bb, src) = self.as_operand(expr, bb);
                self.cfg
                    .assign(bb, tmp.into(), Rvalue::Regular(src), Span::DUMMY);

                (bb, AccessBuilder::new(self.cx.arena(), tmp))
            }
        }
    }

    #[track_caller]
    #[inline]
    fn temporary(&mut self, ty: Ty<'il>) -> Local {
        self.locals.push(LocalData {
            mutbl: Constant::Yes,
            ty,
            origin: LocalOrigin::Temporary,
        })

        // println!(
        //     "loc: {} id: {}, ty: {}",
        //     Location::caller(),
        //     id.to_usize(),
        //     ty
        // );
    }
}

pub fn build_pill<'cx>(cx: &'cx Session<'cx>, did: DefId) -> &'cx Pill<'cx> {
    let body = cx.build_eair(did);
    let mut captures = HashMap::new();
    let mut cfg = Cfg::new();
    let mut alive = HashSet::with_capacity(body.params.len());
    let mut arg_count = body.params.len();
    let mut locals = Locals::new_from_vec(Vec::with_capacity(arg_count + 1));
    let mut params = HashMap::with_capacity(body.params.len() + 1);

    let body_entry = body
        .entry
        .as_ref()
        .expect("body should have an entry point!");

    let ret_place = locals.push(LocalData {
        mutbl: Constant::No,
        ty: body_entry.ty,
        origin: LocalOrigin::Temporary,
    });

    let block = cfg.new_block();

    if let BodyKind::Lambda = body.kind {
        let ty = cx.def_type_of(did);
        let upvars = cx.upvars_of(did);
        let env = locals.push(LocalData {
            mutbl: Constant::No,
            ty,
            origin: LocalOrigin::Temporary,
        });

        cfg.live(block, Span::DUMMY, env);

        // let parent = cx.air_get_parent(did);
        // let types = cx.typeck(parent);

        captures.reserve(upvars.len());
        for var in upvars {
            // let ty = types.node_ty(*var);
            let acc = Access::base(env);
            captures.insert(*var, acc);
        }

        arg_count += 1;
    }

    for (ix, param) in body.params.iter().enumerate() {
        let param_local = locals.push(LocalData {
            mutbl: Constant::No,
            ty: param.ty(),
            origin: LocalOrigin::Param(param.name()),
        });
        cfg.live(block, Span::DUMMY, param_local);
        alive.insert(param_local);
        params.insert(ParamId::new_usize(ix), param_local);
    }

    locals.reserve(body.locals.len());
    let mut map = HashMap::with_capacity(body.locals.len());
    for (local, data) in body.locals.iter().enumerate() {
        assert!(data.ty().maybe_infer().is_none());
        let id = locals.push((*data).into());
        map.insert(EairLocal::new_usize(local), id);
    }

    let mut builder = PillBuilder {
        cx,
        cfg,
        locals,
        captures,
        map,
        current_loop_end: None,
        params,
        alive,
    };

    let bb = builder.lower_expr_into(body_entry, block, ret_place);
    let entry_span = body_entry.span;
    let span = Span::new(
        entry_span.end() - 1,
        entry_span.end(),
        entry_span.line,
        entry_span.sourceid,
    );

    builder.cfg.live(bb, span, ret_place);
    builder.cfg.bb_return(bb, span);

    let body = Pill {
        span: body.span,
        arg_count,
        cfg: builder.cfg,
        locals: builder.locals,
    };

    let alloc = cx.arena().alloc(body);

    if cx.flags().dump_pill {
        let w = std::io::stdout();
        let mut lock = w.lock();
        dump_pill(&mut lock, alloc, did).expect("writing to stdout failed!");
    }

    alloc
}

#[allow(clippy::too_many_lines)]
fn dump_pill(w: &mut dyn Write, pill: &Pill<'_>, did: DefId) -> io::Result<()> {
    const INDENT: &str = "      ";
    enum State {
        Params,
        Locals,
    }

    write!(w, "fun {}(", cx(|cx| cx.name_of(did)))?;
    let mut state = State::Params;
    let mut arg_count = pill.arg_count;
    for (ix, local) in pill
        .locals
        .inner()
        .get(1..)
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        match state {
            State::Params => {
                if arg_count == 1 {
                    state = State::Locals;
                }

                write!(
                    w,
                    "{mutbl} _{num}: {ty}",
                    ty = local.ty,
                    mutbl = match local.mutbl {
                        Constant::Yes => "mut",
                        Constant::No => "const",
                    },
                    num = ix + 1
                )?;

                if let LocalOrigin::Param(name) = local.origin {
                    match name {
                        None => write!(w, "<lambda env>"),
                        Some(sym) => write!(w, " ({})", sym.get_interned()),
                    }?;
                }

                if arg_count != 1 {
                    write!(w, " ,")?;
                } else if arg_count == 1 {
                    writeln!(w, ") => {ty} {{", ty = pill.locals[Local::ZERO].ty)?;

                    writeln!(
                        w,
                        "    let mut _0: {ty}",
                        ty = pill.locals.first().unwrap().ty,
                    )?;
                }

                arg_count -= 1;
            }

            State::Locals => {
                write!(
                    w,
                    "    let {mutbl} _{ix}: {ty}",
                    ty = local.ty,
                    mutbl = match local.mutbl {
                        Constant::Yes => "mut",
                        Constant::No => "const",
                    },
                    ix = if ix == 0 { 0 } else { ix + pill.arg_count }
                )?;

                if let LocalOrigin::User(v) = local.origin {
                    write!(w, " ({})", v.get_interned())?;
                }

                writeln!(w)?;
            }
        }
    }

    writeln!(w)?;

    for (id, bb) in pill.cfg.blocks() {
        writeln!(w, "    bb{}:", id.to_usize())?;

        for stmt in bb.stmts() {
            match stmt.kind() {
                StmtKind::Call { fun, ret, args } => {
                    if args.is_empty() {
                        writeln!(w, "{INDENT}Call ({fun:#?}) => {ret:?}")
                    } else {
                        writeln!(w, "{INDENT}Call ({fun:#?}) {args:?} => {ret:?}")
                    }?;
                }

                StmtKind::Nop => writeln!(w, "{INDENT}Nop")?,

                StmtKind::Assign { dest, src } => writeln!(w, "{INDENT}{dest:?} = {src:?}")?,

                StmtKind::CheckCond(cond) => writeln!(w, "{INDENT}CheckCond({cond:?})")?,

                StmtKind::LocalLive(local) => writeln!(w, "{INDENT}Live(_{})", local.to_usize())?,
            }
        }

        writeln!(w)?;
        write!(w, "{INDENT}")?;

        if let Some(exit) = bb.exit() {
            match exit.kind() {
                BlockExitKind::Goto(b) => writeln!(w, "goto bb{}", b.to_usize()),
                BlockExitKind::Branch { val, true_, false_ } => writeln!(
                    w,
                    "branch ({val:?}) {{ true: bb{true_bb}, false: bb{false_bb} }}",
                    true_bb = true_.to_usize(),
                    false_bb = false_.to_usize()
                ),
                BlockExitKind::Return => writeln!(w, "return"),
            }
        } else {
            write!(w, "{INDENT}<broken: no exit!>")
        }?;

        if id.to_usize() != pill.cfg.len() - 1 {
            writeln!(w)?;
        }
    }

    writeln!(w, "}}")
}
