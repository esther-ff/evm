use crate::ast::{BinOp, UnaryOp, VisitorResult};
use crate::hir::def::{BodyId, DefId, DefType, Resolved};
use crate::hir::lowering_ast::HirId;
use crate::hir::node::{
    BindItemKind, Block, Expr, ExprKind, HirLiteral, Local, Node, Path, Stmt, StmtKind, Thing,
    ThingKind, Universe,
};
use crate::hir::visitor::HirVisitor;
use crate::lexer::Span;
use crate::session::{Session, SymbolId};
use crate::try_visit;
use crate::types::ty::{InferKind, InferTy, Ty, TyKind, TypingError};

use std::cell::RefCell;
use std::collections::HashMap;

crate::newtyped_index!(FieldId, FieldMap, FieldVec, FieldSlice);
crate::newtyped_index!(InferId, InferMap, InferVec, InferSlice);

#[derive(Debug, Clone, Copy)]
pub enum CallKind<'ty> {
    Method(Ty<'ty>),
    Regular,
}

/// Gathers and interns stuff like
/// function signatures, instance declarations
/// and etc...
pub struct ItemGatherer<'a> {
    sess: &'a Session<'a>,
}

impl<'ty> ItemGatherer<'ty> {
    pub fn new(sess: &'ty Session<'ty>) -> Self {
        Self { sess }
    }
}

impl<'vis> HirVisitor<'vis> for ItemGatherer<'_> {
    type Result = ();

    fn visit_thing(&mut self, thing: &'vis Thing<'vis>) -> Self::Result {
        match thing.kind {
            ThingKind::Fn { name: _, sig } => {
                self.sess.lower_fn_sig(*sig, thing.def_id);

                // We have to traverse the fn body for nested functions
                let body = self.sess.hir_ref().get_body(sig.body);
                self.visit_expr(body);
            }

            ThingKind::Instance {
                fields: _,
                name: _,
                ctor_id: (_, ctor_id),
            } => {
                self.sess.instance_def(thing.def_id);
                self.sess.reify_fn_sig_for_ctor_of(ctor_id);
            }

            ThingKind::Bind(bind) => {
                for bind_item in bind.items {
                    if let BindItemKind::Fun { sig, name: _ } = bind_item.kind {
                        self.sess.lower_fn_sig(*sig, bind_item.def_id);
                    }
                    self.visit_bind_item(bind_item);
                }
            }

            ThingKind::Realm { name: _, things } => {
                for i in things {
                    self.visit_thing(i);
                }
            }

            ThingKind::Global { .. } => (),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum Obligation {
    /// Type must be able to be negated via `!`
    Neg,
}

pub struct FunCx<'ty> {
    s: &'ty Session<'ty>,

    fn_ret_ty: Option<Ty<'ty>>,

    node_type: HashMap<HirId, Ty<'ty>>,

    ty_var_types: HashMap<InferId, Ty<'ty>>,

    infer_ty_counter: u32,

    resolved_method_calls: HashMap<HirId, DefId>,

    local_tys: HashMap<HirId, Ty<'ty>>,

    obligations: RefCell<HashMap<InferId, Vec<Obligation>>>,
}

pub struct UnifyError;

impl<'ty> FunCx<'ty> {
    pub fn new(s: &'ty Session<'ty>) -> Self {
        Self {
            s,
            ty_var_types: HashMap::new(),
            infer_ty_counter: 0,
            fn_ret_ty: None,
            node_type: HashMap::new(),
            resolved_method_calls: HashMap::new(),
            local_tys: HashMap::new(),
            obligations: RefCell::new(HashMap::default()),
        }
    }

    pub fn start(&mut self, sig_id: DefId, body: BodyId) {
        let sig = self.s.fn_sig_for(sig_id);
        self.fn_ret_ty = Some(sig.output);

        let body = self.s.hir_ref().get_body(body);
        let fn_sig_span = self.s.hir_ref().expect_fn(sig_id).0.span;

        let actual_ret_ty = self.typeck_expr(body);

        if self.unify(sig.output, actual_ret_ty).is_err() {
            self.type_mismatch_err(sig.output, actual_ret_ty, fn_sig_span);
        }
    }

    fn new_infer_var(&mut self, kind: InferKind) -> Ty<'ty> {
        let id = self.infer_ty_counter;
        self.infer_ty_counter += 1;

        self.s.intern_ty(TyKind::InferTy(InferTy {
            vid: InferId::new(id),
            kind,
        }))
    }

    fn obligation_for(&self, vid: InferId, oblig: Obligation) {
        let mut map = self.obligations.borrow_mut();
        if let Some(entry) = map.get_mut(&vid) {
            return entry.push(oblig);
        }

        map.insert(vid, vec![oblig]);
    }

    fn process_obligs_of_ty(&self, vid: InferId, concrete_ty: Ty<'_>) {
        let map = self.obligations.borrow();
        let Some(obligs) = map.get(&vid) else { return };

        // if we get more just do a match
        // rn it's just `Neg`
        for _obligation in obligs {
            if let Some(inferty) = concrete_ty.maybe_infer() {
                self.obligation_for(inferty.vid, Obligation::Neg);
                continue;
            }

            if !concrete_ty.is_signed_int() {
                todo!("only signed ints can be neg")
            }
        }
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
                log::trace!("unifying infer and a concrete ty {infer:#?}, {concrete:#?}");

                if infer.is_integer() && !concrete.is_integer_like()
                || infer.is_float() && !concrete.is_float_like() {
                    return Err(UnifyError)
                }

                let concrete_ref = self.s.intern_ty(concrete);
                self.process_obligs_of_ty(infer.vid, concrete_ref);

                if let Some(ty) = self.ty_var_types.get(&infer.vid) {
                    return self.unify(*ty, concrete_ref)
                }

                self.ty_var_types.insert(infer.vid, concrete_ref);
            }

            (TyKind::Error, _) | (_, TyKind::Error) => return Ok(()),

            _ => return Err(UnifyError),
        }

        Ok(())
    }

    // probably might recurse REALLY DEEP!
    fn ty_var_ty(&self, id: InferId) -> Option<Ty<'ty>> {
        log::trace!("`ty_var_ty` enter");
        let ret = match self.ty_var_types.get(&id) {
            None => None,
            Some(ty) => match **ty {
                TyKind::InferTy(infer) => self.ty_var_ty(infer.vid),
                _ => Some(*ty),
            },
        };

        log::trace!("`ty_var_end`");
        ret
    }

    fn type_mismatch_err(&self, expected: Ty<'ty>, got: Ty<'ty>, span: Span) {
        self.s.diag().emit_err(
            TypingError::TypeMismatch(self.s.stringify_ty(expected), self.s.stringify_ty(got)),
            span,
        );
    }

    fn typeck_local(&mut self, local: &Local<'_>) -> Ty<'ty> {
        log::trace!("entering `typeck_local`");
        if let Some(local_ty) = self.local_tys.get(&local.hir_id) {
            return *local_ty;
        }

        let init_ty = local.init.map(|expr| self.typeck_expr(expr));
        let local_decl_ty = self.s.lower_ty(local.ty);

        if let Some(ty) = init_ty
            && let Err(..) = self.unify(ty, local_decl_ty)
        {
            self.type_mismatch_err(local_decl_ty, ty, local.ty.span);
        }

        self.local_tys.insert(local.hir_id, local_decl_ty);
        local_decl_ty
    }

    fn typeck_stmt(&mut self, stmt: &Stmt<'_>) {
        match stmt.kind {
            StmtKind::Local(local) => {
                let _ = self.typeck_local(local);
            }

            StmtKind::Thing(..) => {} // we typeck them separately

            StmtKind::Expr(expr) => {
                let _ = self.typeck_expr(expr);
            }
        }
    }

    fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        log::trace!("entering `typeck_expr`");
        let ty = match expr.kind {
            ExprKind::Literal(lit) => self.typeck_expr_literal(lit),
            ExprKind::Binary { lhs, rhs, op } => self.typeck_expr_bin_op(lhs, rhs, op),
            ExprKind::Unary { target, op } => self.typeck_expr_un_op(target, op),
            ExprKind::Paren { inner } => self.type_of(inner),
            ExprKind::Path(path) => self.typeck_expr_path(path),
            ExprKind::Block(block) => self.typeck_block(block),
            ExprKind::Field { src, field } => self.typeck_expr_field(src, field),
            ExprKind::List(exprs) => self.typeck_expr_list(exprs),
            ExprKind::Break => self.s.ty_diverge(),
            ExprKind::Loop { body, reason: _ } => {
                self.typeck_block(body);
                self.s.nil()
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
                        TypingError::TypeMismatch(
                            self.s.stringify_ty(variable_ty),
                            self.s.stringify_ty(value_ty),
                        ),
                        Span::between(variable.span, value.span),
                    );
                }

                self.s.nil()
            }

            ExprKind::If {
                condition,
                block,
                else_ifs,
                otherwise,
            } => self.typeck_expr_if(condition, block, else_ifs, otherwise),

            ExprKind::Call { function, args } => {
                let callable = self.type_of(function);

                let TyKind::FnDef(def_id) = *callable.0 else {
                    self.s.diag().emit_err(
                        TypingError::CallingNotFn {
                            offender: self.s.stringify_ty(callable), // not sure?
                        },
                        expr.span,
                    );

                    return self.s.ty_err();
                };

                self.verify_arguments_for_call(def_id, args, expr.span)
            }

            ExprKind::Return { expr: ret_expr } => {
                let ty = ret_expr.map_or(self.s.nil(), |elm| self.type_of(elm));

                let ret_ty = self
                    .fn_ret_ty
                    .expect("return should only be present in function");

                if self.unify(ret_ty, ty).is_err() {
                    self.type_mismatch_err(ret_ty, ty, ret_expr.map_or(expr.span, |s| s.span));
                }

                self.s.ty_diverge()
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

                self.s.nil()
            }

            ExprKind::CommaSep(exprs) => exprs
                .iter()
                .fold(None, |state, expr| {
                    if state.is_none() {
                        return Some(self.type_of(expr));
                    }
                    self.type_of(expr);
                    state
                })
                .expect("cannot fail as comma'd exprs have >1 exprs!"),

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => self.typeck_expr_meth_call(receiver, method, args, expr.hir_id),
        };

        self.node_type.insert(expr.hir_id, ty);
        ty
    }

    fn typeck_expr_bin_op(&mut self, lhs: &Expr<'_>, rhs: &Expr<'_>, op: BinOp) -> Ty<'ty> {
        let ty_lhs = self.type_of(lhs);
        let ty_rhs = self.type_of(rhs);

        if self.unify(ty_lhs, ty_rhs).is_err() {
            self.s.diag().emit_err(
                TypingError::NoBinaryOp {
                    lhs: self.s.stringify_ty(ty_lhs),
                    rhs: self.s.stringify_ty(ty_rhs),
                },
                Span::between(lhs.span, rhs.span),
            );

            return self.s.ty_err();
        }

        if let BinOp::LogicalOr | BinOp::LogicalAnd | BinOp::NotEquality | BinOp::Equality = op {
            self.s.bool()
        } else {
            ty_lhs
        }
    }

    fn typeck_expr_un_op(&mut self, target: &Expr<'_>, _op: UnaryOp) -> Ty<'ty> {
        let ty = self.type_of(target);

        if let TyKind::Bool = *ty {
            return ty;
        }

        match ty.0 {
            TyKind::Bool | TyKind::Int(..) => (),
            TyKind::InferTy(inferty) if inferty.is_integer() => {
                self.obligation_for(inferty.id(), Obligation::Neg);
                return ty;
            }
            _ => return ty,
        }

        self.s.diag().emit_err(
            TypingError::NoUnaryOp {
                on: self.s.stringify_ty(ty),
            },
            target.span,
        );

        self.s.ty_err()
    }

    fn typeck_expr_index(
        &mut self,
        indexed_thing: &Expr<'_>,
        index: &Expr<'_>,
        expr_span: Span,
    ) -> Ty<'ty> {
        let src_ty = self.type_of(indexed_thing);

        let TyKind::Array(inner_ty) = src_ty.0 else {
            self.s.diag().emit_err(
                TypingError::NoIndexOp {
                    on: self.s.stringify_ty(src_ty),
                },
                expr_span,
            );

            return self.s.ty_err();
        };

        let index_ty = self.type_of(index);

        if self.unify(self.s.u64(), index_ty).is_err() {
            self.type_mismatch_err(self.s.u64(), index_ty, expr_span);
        }

        *inner_ty
    }

    fn typeck_expr_literal(&mut self, lit: HirLiteral) -> Ty<'ty> {
        match lit {
            HirLiteral::Bool(..) => self.s.bool(),
            HirLiteral::Uint(..) | HirLiteral::Int(..) => {
                let new = self.new_infer_var(InferKind::Integer);
                log::trace!("new infer ty for integer: {new:?}");
                new
            }

            HirLiteral::Str(_sym) => todo!("idk how to type strings yet"),

            HirLiteral::Float(..) => self.new_infer_var(InferKind::Float),
        }
    }

    fn typeck_expr_if(
        &mut self,
        condition: &Expr<'_>,
        block: &Block<'_>,
        else_ifs: &[(Block<'_>, Expr<'_>)],
        otherwise: Option<&Block<'_>>,
    ) -> Ty<'ty> {
        let cond_ty = self.type_of(condition);
        if *cond_ty != TyKind::Bool {
            self.type_mismatch_err(self.s.bool(), cond_ty, condition.span);
        }

        let ret_ty = self.typeck_block(block);

        if otherwise.is_none() && self.unify(ret_ty, self.s.nil()).is_err() {
            self.s.diag().emit_err(
                TypingError::TypeMismatch(self.s.stringify_ty(ret_ty), "nil".into()),
                block.span,
            );
        }

        for (block, elsif) in else_ifs {
            let block_ty = self.typeck_block(block);
            if self.unify(block_ty, ret_ty).is_err() {
                self.s.diag().emit_err(
                    TypingError::TypeMismatch(
                        self.s.stringify_ty(block_ty),
                        self.s.stringify_ty(ret_ty),
                    ),
                    Span::between(block.span, elsif.span),
                );
            }

            let elsif_ty = self.type_of(elsif);

            if *elsif_ty != TyKind::Bool {
                self.s.diag().emit_err(
                    TypingError::TypeMismatch("bool".into(), self.s.stringify_ty(elsif_ty)),
                    elsif.span,
                );
            }
        }

        let Some(otherwise_block) = otherwise else {
            return self.s.nil();
        };

        let block_ty = self.typeck_block(otherwise_block);

        if self.unify(ret_ty, block_ty).is_err() {
            self.s.diag().emit_err(
                TypingError::TypeMismatch(
                    self.s.stringify_ty(block_ty),
                    self.s.stringify_ty(ret_ty),
                ),
                otherwise_block.span,
            );
        }

        ret_ty
    }

    fn typeck_expr_field(&mut self, src: &Expr<'_>, field_name: SymbolId) -> Ty<'ty> {
        let src_ty = self.type_of(src);
        let err = if let TyKind::Instance(def) = src_ty.0 {
            if let Some(found) = def.fields.iter().find(|f| f.name == field_name) {
                return self.s.def_type_of(found.def_id);
            }

            TypingError::NoField {
                on: self.s.stringify_ty(src_ty),
                field_name,
            }
        } else {
            TypingError::NotInstance {
                got: self.s.stringify_ty(src_ty),
            }
        };

        self.s.diag().emit_err(err, src.span);
        self.s.ty_err()
    }

    #[track_caller]
    fn typeck_expr_path(&mut self, path: &Path<'_>) -> Ty<'ty> {
        let res = path.res;

        match res {
            Resolved::Def(def_id, DefType::Fun) => self.s.intern_ty(TyKind::FnDef(def_id)),

            Resolved::Def(ctor_def_id, DefType::AdtCtor) => {
                self.s.intern_ty(TyKind::FnDef(ctor_def_id))
            }

            Resolved::Local(hir_id) => {
                let hir = self.s.hir_ref();

                match hir.get_node(hir_id) {
                    Node::Local(local) => self.typeck_local(local),
                    Node::FnParam(param) => self.s.lower_ty(param.ty),

                    _ => todo!(),
                }
            }

            Resolved::Def(def_id, DefType::Const) => self.s.def_type_of(def_id),

            Resolved::Err => self.s.ty_err(),

            _ => unreachable!("what the fuck?"),
        }
    }

    fn typeck_expr_list(&mut self, exprs: &[Expr<'_>]) -> Ty<'ty> {
        if exprs.is_empty() {
            return self
                .s
                .intern_ty(TyKind::Array(self.new_infer_var(InferKind::Regular)));
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
        method: SymbolId,
        args: &[Expr<'_>],
        expr_hir_id: HirId,
    ) -> Ty<'ty> {
        let recv_ty = self.type_of(receiver);
        let mut ret_ty = self.s.ty_err();

        self.s.binds_for_ty(recv_ty, |binds| {
            let Some((def_id, _, span)) = binds
                .iter()
                .flat_map(|x| x.items.iter())
                .filter_map(|item| {
                    let BindItemKind::Fun { sig: _, name } = item.kind else {
                        return None;
                    };

                    Some((item.def_id, name, item.span))
                })
                .find(|(_, name, _)| name == &method)
            else {
                self.s.diag().emit_err(
                    TypingError::MethodNotFound {
                        on_ty: self.s.stringify_ty(recv_ty),
                        method_name: method.get_interned().to_string().into(),
                    },
                    receiver.span,
                );
                return;
            };

            self.resolved_method_calls.insert(expr_hir_id, def_id);

            ret_ty = self.verify_arguments_for_method_call(
                def_id,
                core::iter::once(receiver).chain(args.iter()),
                args.len() + 1,
                span,
            );
        });

        ret_ty
    }

    fn typeck_block(&mut self, block: &Block<'_>) -> Ty<'ty> {
        log::trace!("typeck_block");

        for stmt in block.stmts {
            self.typeck_stmt(stmt);
        }

        block.expr.map_or(self.s.nil(), |expr| self.type_of(expr))
    }

    fn type_of(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        if let Some(ty) = self.node_type.get(&expr.hir_id) {
            return *ty;
        }

        let expr_ty = self.typeck_expr(expr);
        self.node_type.insert(expr.hir_id, expr_ty);
        expr_ty
    }

    #[track_caller]
    fn verify_arguments_for_call(
        &mut self,
        def_id: DefId,
        args: &[Expr<'_>],
        span: Span,
    ) -> Ty<'ty> {
        let sig = self.s.fn_sig_for(def_id);

        let amount_of_args = sig.inputs.len();
        let given_args = args.len();

        let mut sig_tys = self.s.fn_sig_for(def_id).inputs.iter().copied();

        let mut call_tys = args.iter();

        if amount_of_args != given_args {
            self.s.diag().emit_err(
                TypingError::WrongArgumentAmnt {
                    amount_given: given_args,
                    amount_req: amount_of_args,
                },
                dbg!(span),
            );
        }

        loop {
            match (
                sig_tys.next(),
                call_tys.next().map(|expr| self.typeck_expr(expr)),
            ) {
                (Some(sig_ty), Some(call_ty)) => {
                    if self.unify(sig_ty, call_ty).is_err() {
                        self.type_mismatch_err(sig_ty, call_ty, span);
                    }
                }
                (Some(..), None) | (None, Some(..)) => {}
                (None, None) => break,
            }
        }

        sig.output
    }

    #[track_caller]
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

        loop {
            match (
                sig_tys.next(),
                call_tys.next().map(|expr| self.typeck_expr(expr)),
            ) {
                (Some(sig_ty), Some(call_ty)) => {
                    if self.unify(sig_ty, call_ty).is_err() {
                        self.type_mismatch_err(sig_ty, call_ty, span);
                    }
                }
                (Some(..), None) | (None, Some(..)) => {}
                (None, None) => break,
            }
        }

        sig.output
    }
}

#[derive(Debug)]
pub struct TypeTable<'ty> {
    expr_tys: HashMap<HirId, Ty<'ty>>,
    resolved_method_calls: HashMap<HirId, DefId>,
    local_variables: HashMap<HirId, Ty<'ty>>,
}

impl<'ty> TypeTable<'ty> {
    pub fn new() -> Self {
        Self {
            expr_tys: HashMap::new(),
            resolved_method_calls: HashMap::new(),
            local_variables: HashMap::new(),
        }
    }

    #[track_caller]
    #[inline]
    pub fn type_of(&self, expr: Expr<'_>) -> Ty<'ty> {
        log::trace!("`type_of` executed");
        self.expr_tys
            .get(&expr.hir_id)
            .copied()
            .expect("expr given to `type_of` has no type assoc'd with it")
    }

    #[track_caller]
    #[inline]
    pub fn local_var_ty(&self, id: HirId) -> Ty<'ty> {
        self.local_variables
            .get(&id)
            .copied()
            .expect("hir id given to `local_var_ty` has no type assoc'd with it")
    }

    #[track_caller]
    #[inline]
    pub fn resolve_method(&self, id: HirId) -> DefId {
        self.resolved_method_calls
            .get(&id)
            .copied()
            .expect("hir id given to `resolve_method` was invalid")
    }
}

pub struct TyCollector<'ty> {
    table: TypeTable<'ty>,
    sess: &'ty Session<'ty>,
    cx: FunCx<'ty>,
}

impl<'ty> TyCollector<'ty> {
    pub fn new(cx: FunCx<'ty>, sess: &'ty Session<'ty>) -> Self {
        Self {
            table: TypeTable::new(),
            cx,
            sess,
        }
    }

    pub fn visit(mut self, expr: &Expr<'_>) -> TypeTable<'ty> {
        self.visit_expr(expr);

        let _ = core::mem::replace(
            &mut self.table.resolved_method_calls,
            self.cx.resolved_method_calls,
        );

        let _ = core::mem::replace(&mut self.table.local_variables, self.cx.local_tys);

        self.table
    }
}

impl<'vis> HirVisitor<'vis> for TyCollector<'_> {
    type Result = ();

    fn visit_local(&mut self, local: &'vis Local<'vis>) -> Self::Result {
        let val = self
            .cx
            .local_tys
            .get(&local.hir_id)
            .expect("Trying to get type of a local that isn't there?");
        self.table.local_variables.insert(local.hir_id, *val);
    }

    fn visit_stmt(&mut self, stmt: &'vis Stmt<'vis>) -> Self::Result {
        if let StmtKind::Expr(expr) = stmt.kind {
            self.visit_expr(expr);
        }

        match stmt.kind {
            StmtKind::Expr(expr) => self.visit_expr(expr),
            StmtKind::Local(loc) => {
                if let Some(expr) = loc.init {
                    self.visit_expr(expr);
                }
            }

            StmtKind::Thing(..) => (),
        }
    }

    fn visit_expr(&mut self, expr: &'vis Expr<'vis>) -> Self::Result {
        let ty = self.cx.type_of(expr);

        match *ty {
            TyKind::InferTy(infer) => {
                let Some(infer_resolved) = self.cx.ty_var_ty(infer.vid) else {
                    let insert_ty = match infer.kind {
                        InferKind::Float => self.sess.f64(),
                        InferKind::Integer => self.sess.i32(),
                        InferKind::Regular => todo!("regular variables aren't used yet"),
                    };

                    self.table.expr_tys.insert(expr.hir_id, insert_ty);
                    return;
                };

                self.table.expr_tys.insert(expr.hir_id, infer_resolved);
            }

            _ => {
                self.table.expr_tys.insert(expr.hir_id, ty);
            }
        }

        match &expr.kind {
            ExprKind::Binary { lhs, rhs, op: _ } => {
                self.visit_expr(lhs);
                self.visit_expr(rhs);
            }

            ExprKind::Unary { target, op: _ } => self.visit_expr(target),

            ExprKind::Paren { inner } => self.visit_expr(inner),

            ExprKind::Assign { variable, value }
            | ExprKind::AssignWithOp {
                variable,
                value,
                op: _,
            } => {
                self.visit_expr(variable);
                self.visit_expr(value);
            }

            ExprKind::Call { function, args } => {
                self.visit_expr(function);
                crate::visit_iter!(v: self, m: visit_expr, *args);
            }

            ExprKind::MethodCall {
                receiver,
                method: _,
                args,
            } => try_visit!(
                self.visit_expr(receiver),
                crate::visit_iter!(v: self, m: visit_expr, *args)
            ),

            ExprKind::Block(block) => {
                crate::visit_iter!(v: self, m: visit_stmt, block.stmts);
                log::debug!("block stmts: {:#?}", block.stmts);
                crate::maybe_visit!(v: self, m: visit_expr, block.expr);
            }

            ExprKind::If {
                condition,
                block,
                else_ifs,
                otherwise,
            } => {
                self.visit_expr(condition);
                self.visit_block(block);

                for (block, expr) in *else_ifs {
                    self.visit_block(block);
                    self.visit_expr(expr);
                }

                crate::maybe_visit!(v: self, m: visit_block, otherwise);
            }

            ExprKind::Return { expr } => crate::maybe_visit!(v: self, m: visit_expr, expr),

            ExprKind::Field { src, field: _ } => self.visit_expr(src),

            ExprKind::Loop { body, reason: _ } => self.visit_block(body),

            ExprKind::List(exprs) => {
                crate::visit_iter!(v: self, m: visit_expr, *exprs);
            }

            ExprKind::Index {
                index,
                indexed_thing,
            } => {
                self.visit_expr(index);
                self.visit_expr(indexed_thing);
            }

            ExprKind::CommaSep(exprs) => crate::visit_iter!(v: self, m: visit_expr, *exprs),

            ExprKind::Path(path) => self.visit_path(path),

            ExprKind::Literal(..) | ExprKind::Break => Self::Result::normal(),
        }
    }
}

pub fn typeck_universe<'a>(session: &'a Session<'a>, universe: &'a Universe<'a>) {
    log::trace!("typeck_universe");
    ItemGatherer::new(session).visit_universe(universe);

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

    log::trace!("typeck_universe exited");
}
