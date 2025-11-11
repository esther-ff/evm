// temp
#![allow(irrefutable_let_patterns)]

use crate::air::def::{DefId, DefType, Resolved};
use crate::air::node::{
    AirLiteral, BindItem, BindItemKind, Block, Expr, ExprKind, Lambda, Local, Path, Stmt, StmtKind,
    ThingKind, Universe,
};
use crate::air::visitor::AirVisitor;
use crate::air::{AirId, node};
use crate::ast::{BinOp, UnaryOp};
use crate::session::Session;
use crate::span::Span;
use crate::symbols::SymbolId;
use crate::types::ty::{InferKind, InferTy, LambdaEnv, ParamTy, Ty, TyKind, TypingError};

use std::collections::HashMap;
use std::mem;
use std::panic::Location;

crate::newtyped_index!(FieldId, FieldMap, FieldVec, FieldSlice);
crate::newtyped_index!(InferId, InferMap, InferVec, InferSlice);

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum Obligation {
    /// Type must be able to be negated via `!`
    Neg,
}

pub struct FunCx<'ty> {
    s: &'ty Session<'ty>,
    fn_ret_ty: Option<Ty<'ty>>,
    node_type: HashMap<AirId, Ty<'ty>>,

    ty_var_types: HashMap<InferId, Ty<'ty>>,
    ty_var_origins: HashMap<InferId, Span>,
    infer_ty_counter: u32,

    resolved_method_calls: HashMap<AirId, DefId>,
    local_tys: HashMap<AirId, Ty<'ty>>,

    obligations: HashMap<InferId, Vec<Obligation>>,
}

pub struct UnifyError;

impl<'ty> FunCx<'ty> {
    #[track_caller]
    fn new_infer_var(&mut self, kind: InferKind, span: Span) -> Ty<'ty> {
        let vid = InferId::new(self.infer_ty_counter);
        assert!(self.ty_var_origins.insert(vid, span).is_none());

        log::debug!(
            "new infer var {vid:#?}, called at {loc}",
            loc = Location::caller()
        );

        self.infer_ty_counter += 1;
        self.s.intern_ty(TyKind::InferTy(InferTy { vid, kind }))
    }

    fn obligation_for(&mut self, vid: InferId, oblig: Obligation) {
        if let Some(entry) = self.obligations.get_mut(&vid) {
            return entry.push(oblig);
        }

        self.obligations.insert(vid, vec![oblig]);
    }

    fn process_obligs_of_ty(&mut self, vid: InferId, concrete_ty: Ty<'_>) {
        let Some(obligs) = self.obligations.get_mut(&vid) else {
            return;
        };

        let obligations = mem::take(obligs);

        // if we get more just do a match
        // rn it's just `Neg`
        for _obligation in &obligations {
            if let Some(inferty) = concrete_ty.maybe_infer() {
                self.obligation_for(inferty.vid, Obligation::Neg);
                continue;
            }

            if !concrete_ty.is_signed_int() {
                todo!("only signed ints can be neg")
            }
        }

        *self.obligations.get_mut(&vid).unwrap() = obligations;
    }

    fn unify(&mut self, expected: Ty<'ty>, got: Ty<'ty>) -> Result<(), UnifyError> {
        log::trace!("entered `unify` expected={expected:?} got={got:?}");
        match (*expected, *got) {
            (TyKind::Bool, TyKind::Bool)
            | (TyKind::Float, TyKind::Float)
            | (TyKind::Double, TyKind::Double)
            | (TyKind::Nil, TyKind::Nil) |
            // diverges can be coerced to any type
            // because that computation never happens
            (_, TyKind::Diverges) => {}

            (TyKind::Instance(l), TyKind::Instance(r)) if l == r => {}

            (TyKind::Uint(size_l), TyKind::Uint(size_r))
            | (TyKind::Int(size_l), TyKind::Int(size_r))
                if size_l == size_r => {}

            (TyKind::Array(ty_left), TyKind::Array(ty_right)) => self.unify(ty_left, ty_right)?,

            (TyKind::InferTy(infer), concrete) | (concrete, TyKind::InferTy(infer)) => {
                // log::trace!("unifying infer and a concrete ty {infer:#?}, {concrete:#?}");

                if infer.is_integer() && !concrete.is_integer_like()
                || infer.is_float() && !concrete.is_float_like() {
                    return Err(UnifyError)
                }

                if let Some(inner) = concrete.maybe_infer() && infer.vid == inner.vid {
                    return Ok(())
                }

                let concrete_ref = self.s.intern_ty(concrete);
                self.process_obligs_of_ty(infer.vid, concrete_ref);

                if let Some(ty) = self.ty_var_types.get(&infer.vid) {
                    return self.unify(*ty, concrete_ref)
                }

                log::debug!("unified ty var {infer:#?} and concrete {concrete:#?}");

                self.ty_var_types.insert(infer.vid, concrete_ref);
            }

            (TyKind::Param { kind: ParamTy::Fun { inputs, output }, .. }, TyKind::Lambda(env)) | (TyKind::Lambda(env), TyKind::Param { kind: ParamTy::Fun { inputs, output }, .. }) => {
                self.unify(output, env.output)?;

                if inputs.len() != env.all_inputs.len() {
                    return Err(UnifyError)
                }

                for (left, right) in inputs.iter().zip(env.all_inputs) {
                    self.unify(*left, *right)?;
                }
            }

            (TyKind::Error, _) | (_, TyKind::Error) => return Ok(()),

            _ => return Err(UnifyError),
        }

        Ok(())
    }

    fn ty_var_ty(&self, ty: Ty<'ty>) -> Ty<'ty> {
        let mut infer = ty.maybe_infer().unwrap();
        let mut cursor = ty;

        loop {
            match self.ty_var_types.get(&infer.vid) {
                None => return cursor,
                Some(resolved_ty) => match resolved_ty.maybe_infer() {
                    None => return *resolved_ty,
                    Some(infer_ty) => {
                        cursor = *resolved_ty;
                        infer = infer_ty;
                    }
                },
            }
        }
    }

    fn type_mismatch_err(&self, expected: Ty<'ty>, got: Ty<'ty>, span: Span) {
        self.s
            .diag()
            .emit_err(TypingError::TypeMismatch(expected, got), span);
    }

    fn typeck_local(&mut self, local: &Local<'_>) -> Ty<'ty> {
        log::trace!("------ entering `typeck_local` for {}", local.name.interned);
        if let Some(local_ty) = self.local_tys.get(&local.air_id) {
            return *local_ty;
        }

        log::trace!("----- typeck'ing local {}", local.name.interned);
        let init_ty = local.init.map(|expr| self.type_of(expr));

        match (local.ty, init_ty) {
            (None, Some(ty)) => {
                self.local_tys.insert(local.air_id, ty);
                ty
            }

            (Some(air_ty), Some(ty)) => {
                let lowered = self.s.lower_ty(air_ty);
                if self.unify(lowered, ty).is_err() {
                    self.type_mismatch_err(lowered, ty, air_ty.span);
                }

                self.local_tys.insert(local.air_id, ty);

                lowered
            }

            (Some(air_ty), None) => {
                let lowered = self.s.lower_ty(air_ty);
                self.local_tys.insert(local.air_id, lowered);
                lowered
            }

            (None, None) => self.new_infer_var(InferKind::Regular, local.name.span),
        }
    }

    fn typeck_stmt(&mut self, stmt: &Stmt<'_>) {
        match stmt.kind {
            StmtKind::Local(local) => {
                let local_ty = self.typeck_local(local);
                self.node_type.insert(local.air_id, local_ty);
            }

            StmtKind::Thing(..) => {} // we typeck them separately

            StmtKind::Expr(expr) => {
                let _ = self.typeck_expr(expr);
            }
        }
    }

    #[track_caller]
    #[allow(clippy::too_many_lines)]
    fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        log::trace!("entering `typeck_expr`");
        let ty = match expr.kind {
            ExprKind::Lambda(lambda) => self.typeck_lambda(lambda, expr.span),
            ExprKind::Literal(lit) => self.typeck_expr_literal(lit),
            ExprKind::Binary { lhs, rhs, op } => self.typeck_expr_bin_op(lhs, rhs, op),
            ExprKind::Unary { target, op } => self.typeck_expr_un_op(target, op),
            ExprKind::Path(path) => self.typeck_expr_path(path),
            ExprKind::Block(block) => self.typeck_block(block),
            ExprKind::Field { src, field } => self.typeck_expr_field(src, field),
            ExprKind::List(exprs) => self.typeck_expr_list(exprs, expr.span),
            ExprKind::Break => self.s.types.diverges,
            ExprKind::Loop { body } => {
                self.typeck_block(body);
                self.s.types.nil
            }

            ExprKind::Index {
                index,
                indexed_thing,
            } => self.typeck_expr_index(indexed_thing, index, expr.span),

            ExprKind::Assign { variable, value } => {
                let variable_ty = self.type_of(variable);
                let value_ty = self.type_of(value);

                if self.unify(variable_ty, value_ty).is_err() {
                    self.s.diag().emit_err(
                        TypingError::TypeMismatch(variable_ty, value_ty),
                        Span::between(variable.span, value.span),
                    );
                }

                self.s.types.nil
            }

            ExprKind::If {
                condition,
                block,
                else_,
            } => self.typeck_expr_if(condition, block, else_),

            ExprKind::Call { function, args } => {
                let callable = self.type_of(function);
                match *callable {
                    TyKind::FnDef(did) => {
                        let sig = self.s.fn_sig_for(did);
                        dbg!(sig);
                        self.verify_arguments_for_call(sig.inputs, args, expr.span);
                        sig.output
                    }

                    TyKind::Lambda(env) => {
                        self.verify_arguments_for_call(env.all_inputs, args, expr.span);
                        env.output
                    }

                    TyKind::Param {
                        kind: ParamTy::Fun { inputs, output },
                        ..
                    } => {
                        self.verify_arguments_for_call(inputs, args, expr.span);
                        output
                    }

                    TyKind::Error => self.s.types.err,

                    _ => {
                        self.s
                            .diag()
                            .emit_err(TypingError::CallingNotFn { offender: callable }, expr.span);

                        self.s.types.err
                    }
                }
            }

            ExprKind::Return { expr: ret_expr } => {
                let ty = ret_expr.map_or(self.s.types.nil, |elm| self.type_of(elm));

                let ret_ty = self
                    .fn_ret_ty
                    .expect("return should only be present in function");

                if self.unify(ret_ty, ty).is_err() {
                    self.type_mismatch_err(ret_ty, ty, ret_expr.map_or(expr.span, |s| s.span));
                }

                self.s.types.diverges
            }

            ExprKind::AssignWithOp {
                variable,
                value,
                op,
            } => {
                let variable_ty = self.type_of(variable);
                let expr_ty = self.type_of(value);

                if self.unify(variable_ty, expr_ty).is_err() {
                    todo!("No binary op ({op:?}) for {variable_ty:?} and {expr_ty:?}")
                }

                self.s.types.nil
            }

            // ExprKind::CommaSep(exprs) => exprs
            //     .iter()
            //     .fold(None, |state, expr| {
            //         if state.is_none() {
            //             return Some(self.type_of(expr));
            //         }
            //         self.type_of(expr);
            //         state
            //     })
            //     .expect("cannot fail as comma'd exprs have >1 exprs!"),
            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => self.typeck_expr_meth_call(receiver, method, args, expr.air_id),
        };

        self.node_type.insert(expr.air_id, ty);
        ty
    }

    fn typeck_expr_bin_op(&mut self, lhs: &Expr<'_>, rhs: &Expr<'_>, op: BinOp) -> Ty<'ty> {
        let ty_lhs = self.type_of(lhs);
        let ty_rhs = self.type_of(rhs);

        if self.unify(ty_lhs, ty_rhs).is_err() {
            self.s.diag().emit_err(
                TypingError::NoBinaryOp {
                    lhs: (ty_lhs),
                    rhs: (ty_rhs),
                },
                Span::between(lhs.span, rhs.span),
            );

            return self.s.types.err;
        }

        if let BinOp::LogicalOr | BinOp::LogicalAnd | BinOp::NotEquality | BinOp::Equality = op {
            self.s.types.bool
        } else {
            ty_lhs
        }
    }

    fn typeck_expr_un_op(&mut self, target: &Expr<'_>, op: UnaryOp) -> Ty<'ty> {
        let ty = self.type_of(target);
        match op {
            UnaryOp::Deref => {
                if !ty.is_ref() {
                    self.s
                        .diag()
                        .emit_err(TypingError::NoUnaryOp { on: (ty) }, target.span);

                    return self.s.types.err;
                }

                ty.peel_ref()
            }

            UnaryOp::AddrOf => self.s.intern_ty(TyKind::Ref(ty)),

            UnaryOp::Negation => match *ty {
                TyKind::Int(..) => ty,
                TyKind::InferTy(infer) => {
                    self.obligation_for(infer.id(), Obligation::Neg);
                    ty
                }
                _ => {
                    self.s
                        .diag()
                        .emit_err(TypingError::NoUnaryOp { on: (ty) }, target.span);
                    self.s.types.err
                }
            },

            UnaryOp::Not => match *ty {
                TyKind::Int(..) | TyKind::Bool | TyKind::Uint(..) => ty,
                _ => {
                    self.s
                        .diag()
                        .emit_err(TypingError::NoUnaryOp { on: (ty) }, target.span);
                    self.s.types.err
                }
            },
        }
    }

    fn typeck_expr_index(
        &mut self,
        indexed_thing: &Expr<'_>,
        index: &Expr<'_>,
        expr_span: Span,
    ) -> Ty<'ty> {
        let src_ty = self.type_of(indexed_thing);

        let TyKind::Array(inner_ty) = *src_ty else {
            self.s
                .diag()
                .emit_err(TypingError::NoIndexOp { on: (src_ty) }, expr_span);

            return self.s.types.err;
        };

        let index_ty = self.type_of(index);

        if self.unify(self.s.types.u64, index_ty).is_err() {
            self.type_mismatch_err(self.s.types.u64, index_ty, expr_span);
        }

        inner_ty
    }

    fn typeck_expr_literal(&mut self, lit: AirLiteral) -> Ty<'ty> {
        match lit {
            AirLiteral::Bool(..) => self.s.types.bool,
            AirLiteral::Uint(..) | AirLiteral::Int(..) => {
                self.new_infer_var(InferKind::Integer, Span::DUMMY)
            }

            AirLiteral::Str(_sym) => todo!("idk how to type strings yet"),

            AirLiteral::Float(..) => self.new_infer_var(InferKind::Float, Span::DUMMY),
        }
    }

    fn typeck_lambda(&mut self, lambda: &Lambda<'_>, expr_span: Span) -> Ty<'ty> {
        let env = LambdaEnv {
            all_inputs: self
                .s
                .arena()
                .alloc_from_iter(lambda.inputs.iter().map(|param| {
                    let param_ty = if let node::TyKind::Infer = param.ty.kind {
                        self.new_infer_var(InferKind::Regular, param.name.span)
                    } else {
                        self.s.lower_ty(param.ty)
                    };

                    self.node_type.insert(param.air_id, param_ty);
                    param_ty
                })),
            output: lambda
                .output
                .map_or(self.new_infer_var(InferKind::Regular, expr_span), |ty| {
                    self.s.lower_ty(&ty)
                }),
            did: lambda.did,
            span: expr_span,
        };

        let body = self.s.air_body_via_id(lambda.body);
        let output_ty = self.type_of(body);

        if self.unify(env.output, output_ty).is_err() {
            self.s
                .diag()
                .emit_err(TypingError::TypeMismatch(env.output, output_ty), body.span);
        }

        let ptr = self.s.arena().alloc(env);
        self.s.intern_ty(TyKind::Lambda(ptr))
    }

    fn typeck_expr_if(
        &mut self,
        condition: &Expr<'_>,
        block: &Block<'_>,
        else_: Option<&Expr<'_>>,
    ) -> Ty<'ty> {
        let cond = self.type_of(condition);
        if *cond != TyKind::Bool {
            self.type_mismatch_err(self.s.types.bool, cond, condition.span);
        }

        let block_ty = self.typeck_block(block);
        if let Some(else_block) = else_ {
            let ty = self.type_of(else_block);

            if self.unify(block_ty, ty).is_err() {
                self.type_mismatch_err(block_ty, ty, else_block.span);
            }

            block_ty
        } else {
            self.s.types.nil
        }
    }

    fn typeck_expr_field(&mut self, src: &Expr<'_>, field_name: SymbolId) -> Ty<'ty> {
        let src_ty = self.type_of(src);
        if src_ty.is_error() {
            return self.s.types.err;
        }

        let err = if let TyKind::Instance(def) = *src_ty {
            if let Some(found) = def.fields.iter().find(|(_, f)| f.name == field_name) {
                return self.s.def_type_of(found.1.def_id);
            }

            TypingError::NoField {
                on: src_ty,
                field_name,
            }
        } else {
            TypingError::NotInstance { got: src_ty }
        };

        self.s.diag().emit_err(err, src.span);
        self.s.types.err
    }

    fn typeck_expr_path(&mut self, path: &Path<'_>) -> Ty<'ty> {
        if path.segments.iter().filter(|x| !x.res.is_err()).count() == path.segments.len() {
            let res = path.res;

            match res {
                Resolved::Def(def_id, DefType::Fun) => self.s.intern_ty(TyKind::FnDef(def_id)),

                Resolved::Def(ctor_def_id, DefType::AdtCtor) => {
                    self.s.intern_ty(TyKind::FnDef(ctor_def_id))
                }

                Resolved::Local(air_id) => *self.node_type.get(&air_id).unwrap(),

                Resolved::Err => self.s.types.err,

                _ => unreachable!("what the fuck?"),
            }
        } else {
            todo!()
        }
    }

    fn typeck_expr_list(&mut self, exprs: &[Expr<'_>], span: Span) -> Ty<'ty> {
        if exprs.is_empty() {
            return self
                .s
                .intern_ty(TyKind::Array(self.new_infer_var(InferKind::Regular, span)));
        }

        exprs
            .iter()
            .fold(None, |state, expr| {
                let Some(ty) = state else {
                    return Some(self.type_of(expr));
                };

                let expr_ty = self.type_of(expr);
                if self.unify(ty, expr_ty).is_err() {
                    self.type_mismatch_err(ty, expr_ty, expr.span);
                }

                state
            })
            .map_or_else(
                || unreachable!(),
                |output| self.s.intern_ty(TyKind::Array(output)),
            )
    }

    fn typeck_expr_meth_call(
        &mut self,
        receiver: &Expr<'_>,
        method_name: SymbolId,
        args: &[Expr<'_>],
        expr_air_id: AirId,
    ) -> Ty<'ty> {
        let recv_ty = self.type_of(receiver);
        if recv_ty.is_error() {
            return self.s.types.err;
        }

        let binds = self.s.binds_for_type(recv_ty);
        let Some((def_id, _, span)) = binds
            .iter()
            .filter_map(|item| {
                let BindItemKind::Fun { sig: _, name } = item.kind else {
                    return None;
                };

                Some((item.def_id, name, item.span))
            })
            .find(|(_, name, _)| name == &method_name)
        else {
            self.s.diag().emit_err(
                TypingError::MethodNotFound {
                    on_ty: (recv_ty),
                    method_name,
                },
                receiver.span,
            );
            return self.s.types.err;
        };

        self.resolved_method_calls.insert(expr_air_id, def_id);

        self.verify_arguments_for_method_call(
            def_id,
            core::iter::once(receiver).chain(args.iter()),
            args.len() + 1,
            span,
        )
    }

    fn typeck_block(&mut self, block: &Block<'_>) -> Ty<'ty> {
        log::trace!("typeck_block");

        for stmt in block.stmts {
            self.typeck_stmt(stmt);
        }

        block
            .expr
            .map_or(self.s.types.nil, |expr| self.type_of(expr))
    }

    fn type_of(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        if let Some(ty) = self.node_type.get(&expr.air_id) {
            return *ty;
        }

        let expr_ty = self.typeck_expr(expr);
        self.node_type.insert(expr.air_id, expr_ty);
        expr_ty
    }

    fn verify_arguments_for_call(&mut self, inputs: &[Ty<'ty>], args: &[Expr<'_>], span: Span) {
        let amount_of_args = inputs.len();
        let given_args = args.len();

        let mut sig_tys = inputs.iter().copied();
        let mut call_tys = args.iter();

        if amount_of_args != given_args {
            self.s.diag().emit_err(
                TypingError::WrongArgumentAmnt {
                    amount_given: given_args,
                    amount_req: amount_of_args,
                },
                span,
            );
        }

        let mut ix = 0;
        loop {
            match (
                sig_tys.next(),
                call_tys.next().map(|expr| self.type_of(expr)),
            ) {
                (Some(sig_ty), Some(call_ty)) => {
                    if self.unify(sig_ty, call_ty).is_err() {
                        self.s.diag().emit_err(
                            TypingError::WrongArgumentTy {
                                expected: sig_ty,
                                got: call_ty,
                                arg_idx: ix,
                            },
                            span,
                        );
                    }
                }
                (Some(..), None) | (None, Some(..)) => {}
                (None, None) => break,
            }
            ix += 1;
        }
    }

    fn verify_arguments_for_method_call<'a>(
        &mut self,
        def_id: DefId,
        args: impl IntoIterator<Item = &'a Expr<'a>>,
        given_args: usize,
        span: Span,
    ) -> Ty<'ty> {
        let sig = self.s.fn_sig_for(def_id);
        let amount_of_args = sig.inputs.len();

        let mut sig_tys = self.s.fn_sig_for(def_id).inputs.iter().copied();
        let mut call_tys = args.into_iter();

        if amount_of_args != given_args {
            self.s.diag().emit_err(
                TypingError::WrongArgumentAmnt {
                    amount_given: given_args,
                    amount_req: amount_of_args,
                },
                dbg!(span),
            );
        }

        let mut ix = 0;
        loop {
            match (
                sig_tys.next(),
                call_tys.next().map(|expr| self.type_of(expr)),
            ) {
                (Some(sig_ty), Some(call_ty)) => {
                    if self.unify(sig_ty, call_ty).is_err() {
                        self.s.diag().emit_err(
                            TypingError::WrongArgumentTy {
                                expected: sig_ty,
                                got: call_ty,
                                arg_idx: ix,
                            },
                            span,
                        );
                    }
                }
                (Some(..), None) | (None, Some(..)) => {}
                (None, None) => break,
            }
            ix += 1;
        }

        sig.output
    }
}

#[derive(Debug)]
pub struct TypeTable<'ty> {
    air_node_tys: HashMap<AirId, Ty<'ty>>,
    resolved_method_calls: HashMap<AirId, DefId>,
    lambda_types: HashMap<DefId, Ty<'ty>>,
}

impl<'ty> TypeTable<'ty> {
    pub fn new() -> Self {
        Self {
            air_node_tys: HashMap::new(),
            resolved_method_calls: HashMap::new(),
            lambda_types: HashMap::new(),
        }
    }

    pub fn type_of(&self, expr: &Expr<'_>) -> Ty<'ty> {
        log::trace!("`type_of` executed");
        self.air_node_tys
            .get(&expr.air_id)
            .copied()
            .expect("expr given to `type_of` has no type assoc'd with it")
    }

    pub fn node_ty(&self, air_id: AirId) -> Ty<'ty> {
        match self.air_node_tys.get(&air_id) {
            None => panic!("{air_id} has no type associated with it!"),
            Some(ty) => *ty,
        }
    }

    pub fn resolve_method(&self, id: AirId) -> DefId {
        self.resolved_method_calls
            .get(&id)
            .copied()
            .expect("hir id given to `resolve_method` was invalid")
    }

    pub fn lambda_type(&self, did: DefId) -> Ty<'ty> {
        self.lambda_types[&did]
    }
}

struct TyCollector<'ty> {
    table: TypeTable<'ty>,
    sess: &'ty Session<'ty>,
    cx: FunCx<'ty>,
}

impl<'ty> TyCollector<'ty> {
    fn visit(mut self, expr: &Expr<'_>) -> TypeTable<'ty> {
        self.visit_expr(expr);
        self.table.resolved_method_calls = self.cx.resolved_method_calls;
        self.table
    }

    fn resolve_type_variable(&self, ty: Ty<'ty>) -> Ty<'ty> {
        match *ty {
            TyKind::InferTy(..) => match *self.cx.ty_var_ty(ty) {
                TyKind::InferTy(inner) => match inner.kind {
                    InferKind::Float => self.sess.types.f64,
                    InferKind::Integer => self.sess.types.i64,
                    InferKind::Regular => {
                        dbg!(ty, inner);
                        let loc = self.cx.ty_var_origins.get(&inner.vid).copied().unwrap();
                        self.sess.diag().emit_err(TypingError::InferFail, loc);
                        self.sess.types.err
                    }
                },

                any => self.sess.intern_ty(any),
            },

            // get rid maybe?
            TyKind::Array(inner) if inner.maybe_infer().is_some() => self
                .sess
                .intern_ty(TyKind::Array(self.resolve_type_variable(inner))),

            _ => ty,
        }
    }
}

impl<'vis> AirVisitor<'vis> for TyCollector<'_> {
    type Result = ();

    fn visit_local(&mut self, local: &'vis Local<'vis>) -> Self::Result {
        let val = self
            .cx
            .local_tys
            .get(&local.air_id)
            .expect("Trying to get type of a local that isn't there?");

        let ty = match **val {
            TyKind::InferTy(..) => match *self.cx.ty_var_ty(*val) {
                TyKind::InferTy(inner) => match inner.kind {
                    InferKind::Float => self.sess.types.f64,
                    InferKind::Integer => self.sess.types.i64,
                    InferKind::Regular => {
                        let loc = self.cx.ty_var_origins.get(&inner.vid).copied().unwrap();
                        self.sess.diag().emit_err(TypingError::InferFail, loc);
                        self.sess.types.err
                    }
                },

                any => self.sess.intern_ty(any),
            },

            _ => *val,
        };

        self.table.air_node_tys.insert(local.air_id, ty);
    }

    fn visit_stmt(&mut self, stmt: &'vis Stmt<'vis>) -> Self::Result {
        match stmt.kind {
            StmtKind::Expr(expr) => self.visit_expr(expr),
            StmtKind::Local(loc) => {
                self.visit_local(loc);
                if let Some(expr) = loc.init {
                    self.visit_expr(expr);
                }
            }

            StmtKind::Thing(..) => (),
        }
    }

    fn visit_expr(&mut self, expr: &'vis Expr<'vis>) -> Self::Result {
        let ty = self.cx.type_of(expr);
        let expr_id = if let ExprKind::Lambda(lambda) = expr.kind {
            for ele in lambda.inputs {
                let param_ty = self.cx.node_type[&ele.air_id];

                self.table
                    .air_node_tys
                    .insert(ele.air_id, self.resolve_type_variable(param_ty));
            }

            let body = self.sess.air_body_via_id(lambda.body);
            self.visit_expr(body);

            Some(lambda.expr_air_id)
        } else {
            None
        };

        let ty = match *ty {
            TyKind::InferTy(..) => match *self.cx.ty_var_ty(ty) {
                TyKind::InferTy(inner) => match inner.kind {
                    InferKind::Float => self.sess.types.f64,
                    InferKind::Integer => self.sess.types.i64,
                    InferKind::Regular => {
                        let loc = self.cx.ty_var_origins.get(&inner.vid).copied().unwrap();
                        self.sess.diag().emit_err(TypingError::InferFail, loc);
                        self.sess.types.err
                    }
                },

                any => self.sess.intern_ty(any),
            },

            TyKind::Lambda(lambda) => {
                let ty = if lambda
                    .all_inputs
                    .iter()
                    .any(|ty| ty.maybe_infer().is_some())
                {
                    let all_inputs = self.sess.arena().alloc_from_iter(
                        lambda
                            .all_inputs
                            .iter()
                            .map(|ty| self.resolve_type_variable(*ty)),
                    );

                    // dbg!(self.sess.fn_sig_for(lambda.did));
                    let env = self.sess.arena().alloc(LambdaEnv {
                        all_inputs,
                        output: self.resolve_type_variable(lambda.output),
                        did: lambda.did,
                        span: lambda.span,
                    });

                    self.sess.intern_ty(TyKind::Lambda(env))
                } else {
                    ty
                };

                self.table.lambda_types.insert(lambda.did, ty);
                if let Some(air_id) = expr_id {
                    self.table.air_node_tys.insert(air_id, ty);
                }

                ty
            }

            TyKind::Array(inner) => self
                .sess
                .intern_ty(TyKind::Array(self.resolve_type_variable(inner))),

            _ => ty,
        };

        self.table.air_node_tys.insert(expr.air_id, ty);
        crate::air::visitor::walk_expr(self, expr);
    }
}

pub fn typeck<'cx>(cx: &'cx Session<'cx>, did: DefId) -> &'cx TypeTable<'cx> {
    let (air_sig, _) = cx.air_get_fn(did);
    let body = cx.air_body_via_id(air_sig.body);
    let ty_sig = cx.fn_sig_for(did);

    let mut table = TypeTable::new();
    let node_type: HashMap<_, _> = air_sig
        .arguments
        .iter()
        .zip(ty_sig.inputs)
        .map(|(param, ty)| {
            assert!(table.air_node_tys.insert(param.air_id, *ty).is_none());
            (param.air_id, *ty)
        })
        .collect();

    let mut fcx = FunCx {
        s: cx,
        fn_ret_ty: Some(ty_sig.output),
        node_type,
        ty_var_types: HashMap::new(),
        ty_var_origins: HashMap::new(),
        infer_ty_counter: 0,
        resolved_method_calls: HashMap::new(),
        local_tys: HashMap::new(),
        obligations: HashMap::new(),
    };

    let actual_ret_ty = fcx.typeck_expr(body);

    if fcx.unify(ty_sig.output, actual_ret_ty).is_err() {
        fcx.type_mismatch_err(ty_sig.output, actual_ret_ty, air_sig.span);
    }

    let table = TyCollector {
        cx: fcx,
        table,
        sess: cx,
    }
    .visit(body);

    cx.arena().alloc(table)
}

pub fn binds_for_type<'cx>(cx: &'cx Session<'cx>, ty: Ty<'cx>) -> &'cx [BindItem<'cx>] {
    use crate::air::node;

    cx.arena().alloc_from_iter(
        cx.air_map()
            .nodes()
            .into_iter()
            .filter_map(node::Node::get_thing)
            .filter_map(node::Thing::get_bind)
            .filter_map(|bind| {
                let bind_ty = cx.lower_ty(bind.with);
                if ty == bind_ty {
                    Some(bind.items)
                } else {
                    // attempt rough equality

                    match (*ty, *bind_ty) {
                        // add instances with generics later :3
                        (TyKind::Array(l), TyKind::Array(r)) if r.is_param() => Some(bind.items),
                        (TyKind::Array(l), TyKind::Array(r)) if l == r => Some(bind.items),
                        _ => None,
                    }
                }
            })
            .flatten()
            .copied(),
    )
}

pub fn typeck_universe<'a>(session: &'a Session<'a>, universe: &'a Universe<'a>) {
    for thing in universe.things {
        match thing.kind {
            ThingKind::Fn { name: _, sig: _ } => {
                let _table = session.typeck(thing.def_id);
            }

            ThingKind::Bind(bind) => {
                for item in bind.items {
                    if let BindItemKind::Fun { sig: _, name: _ } = item.kind {
                        let _table = session.typeck(item.def_id);
                    }
                }
            }
            _ => {}
        }
    }
}
