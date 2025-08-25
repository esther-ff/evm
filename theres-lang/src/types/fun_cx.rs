use crate::ast::VisitorResult;
use crate::hir::def::{BodyId, DefId, DefType, Resolved};
use crate::hir::lowering_ast::HirId;
use crate::hir::node::{
    BindItemKind, Block, Expr, ExprKind, HirLiteral, Local, Node, Stmt, StmtKind, Thing, ThingKind,
    Universe,
};
use crate::hir::visitor::HirVisitor;
use crate::lexer::Span;
use crate::session::Session;
use crate::try_visit;
use crate::types::ty::{InferKind, InferTy, Ty, TyKind, TypingError};
use std::collections::HashMap;

crate::newtyped_index!(FieldId, FieldMap, FieldVec, FieldSlice);
crate::newtyped_index!(InferId, InferMap, InferVec, InferSlice);

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

            ThingKind::Instance { fields: _, name: _ } => {
                self.sess.instance_def(thing.def_id);
            } // Nothing to do

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

pub struct FunCx<'ty> {
    s: &'ty Session<'ty>,

    fn_ret_ty: Option<Ty<'ty>>,

    node_type: HashMap<HirId, Ty<'ty>>,

    ty_var_types: HashMap<InferId, Ty<'ty>>,

    infer_ty_counter: u32,

    resolved_method_calls: HashMap<HirId, DefId>,

    local_tys: HashMap<HirId, Ty<'ty>>,
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

                if infer.is_integer() && !concrete.is_integer_like() || infer.is_float() && !concrete.is_float_like() {
                    return Err(UnifyError)
                    
                }
                match self.ty_var_types.get(&infer.vid) {
                    None => {
                        self.ty_var_types
                            .insert(infer.vid, self.s.intern_ty(concrete));
                    }

                    Some(ty) => return self.unify(*ty, self.s.intern_ty(concrete)),
                }
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
            StmtKind::Thing(..) => {} // we typeck them later
            StmtKind::Expr(expr) => {
                let _ = self.typeck_expr(expr);
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        log::trace!("entering `typeck_expr`");
        let ty = match expr.kind {
            ExprKind::Literal(lit) => match lit {
                HirLiteral::Bool(..) => self.s.bool(),
                HirLiteral::Uint(..) | HirLiteral::Int(..) => {
                    let new = self.new_infer_var(InferKind::Integer);
                    log::trace!("new infer ty for integer: {new:?}");
                    new
                }

                HirLiteral::Str(_sym) => todo!("idk how to type strings yet Ok!"),

                HirLiteral::Float(..) => self.new_infer_var(InferKind::Float),
            },

            ExprKind::Binary { lhs, rhs, op: _ } => {
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

                ty_lhs
            }

            ExprKind::Unary { target, op: _ } => {
                let ty = self.type_of(target);

                if let TyKind::Bool | TyKind::Uint(..) | TyKind::Int(..) = *ty {
                    return ty;
                }

                self.s.diag().emit_err(
                    TypingError::NoUnaryOp {
                        on: self.s.stringify_ty(ty),
                    },
                    target.span,
                );

                self.s.ty_err()
            }

            ExprKind::Paren { inner } => self.type_of(inner),

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
            } => {
                let cond_ty = self.type_of(condition);
                if *cond_ty != TyKind::Bool {
                    self.type_mismatch_err(self.s.bool(), cond_ty, condition.span);
                }

                let ret_ty = self.typeck_block(block);

                for (block, elsif) in else_ifs {
                    let block_ty = self.typeck_block(block);
                    if block_ty != ret_ty {
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

                if let Some(otherwise_block) = otherwise
                    && self.typeck_block(otherwise_block) != ret_ty
                {
                    let block_ty = self.typeck_block(otherwise_block);

                    if ret_ty != block_ty {
                        self.s.diag().emit_err(
                            TypingError::TypeMismatch(
                                self.s.stringify_ty(block_ty),
                                self.s.stringify_ty(ret_ty),
                            ),
                            otherwise_block.span,
                        );
                    }
                }

                ret_ty
            }

            ExprKind::Call { function, args } => {
                let callable = self.type_of(function);

                let TyKind::FnDef(def_id) = *callable.0 else {
                    self.s.diag().emit_err(
                        TypingError::CallingNotFn {
                            offender: "".into(), // not sure?
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

            ExprKind::Field {
                src,
                field: field_name,
            } => {
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

            ExprKind::Loop { body, reason: _ } => {
                self.typeck_block(body);
                self.s.nil()
            }

            ExprKind::Block(block) => self.typeck_block(block),

            ExprKind::Index {
                index,
                indexed_thing,
            } => {
                let src_ty = self.type_of(indexed_thing);

                let TyKind::Array(inner_ty) = src_ty.0 else {
                    self.s.diag().emit_err(
                        TypingError::NoIndexOp {
                            on: self.s.stringify_ty(src_ty),
                        },
                        expr.span,
                    );

                    return self.s.ty_err();
                };

                let index_ty = self.type_of(index);

                if self.unify(self.s.u64(), index_ty).is_err() {
                    self.type_mismatch_err(self.s.u64(), index_ty, expr.span);
                }

                *inner_ty
            }

            ExprKind::Path(path) => {
                let res = path.res;

                match res {
                    Resolved::Def(def_id, DefType::Fun) => self.s.intern_ty(TyKind::FnDef(def_id)),

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

            ExprKind::Break => self.s.ty_diverge(),

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
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

                    self.resolved_method_calls.insert(expr.hir_id, def_id);

                    ret_ty = self.verify_arguments_for_call(def_id, args, span);
                });

                ret_ty
            }

            ExprKind::Array {
                ty_of_array,
                init,
                size,
            } => {
                let size_ty = self.type_of(size);
                if self.s.u64() != size_ty {
                    self.type_mismatch_err(self.s.u64(), size_ty, expr.span);
                }

                let array_ty = self.s.lower_ty(ty_of_array);

                for expr in init {
                    let expr_ty = self.type_of(expr);

                    if expr_ty != array_ty {
                        self.type_mismatch_err(array_ty, expr_ty, expr.span);
                    }
                }

                self.s.intern_ty(TyKind::Array(array_ty))
            }
        };

        self.node_type.insert(expr.hir_id, ty);
        ty
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
                span,
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
                // log::debug!("block stmts: {:#?}", block.stmts);
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

            ExprKind::Array {
                ty_of_array,
                init,
                size,
            } => {
                self.visit_ty(ty_of_array);
                crate::visit_iter!(v: self, m: visit_expr, *init);
                self.visit_expr(size);
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
                    if let BindItemKind::Fun { sig: _, name:_ } = item.kind {
                        let _table = session.typeck(item.def_id);
                    }
                }
            }
            _ => {}
        }
    }

    log::trace!("typeck_universe exited");
}
