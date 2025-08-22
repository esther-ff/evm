use std::borrow::Cow;
use std::collections::HashMap;
use std::panic::Location;

use crate::errors::TheresError;
use crate::hir;
use crate::hir::def::{BodyId, DefId, DefType, IntTy, Resolved};
use crate::hir::lowering_ast::HirId;
use crate::hir::node::{
    self, Bind, BindItemKind, Block, Constant, Expr, ExprKind, HirLiteral, Local, Stmt, StmtKind,
    Thing, ThingKind, Universe,
};
use crate::hir::visitor::HirVisitor;
use crate::lexer::Span;
use crate::session::{Pooled, Session, SymbolId};
crate::newtyped_index!(FieldId, FieldMap, FieldVec, FieldSlice);
crate::newtyped_index!(InferId, InferMap, InferVec, InferSlice);

/// Interned type.
pub type Ty<'ty> = Pooled<'ty, TyKind<'ty>>;

/// Interned instance data.
pub type Instance<'ty> = Pooled<'ty, InstanceDef<'ty>>;

/// Interned Function signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnSig<'ty> {
    pub inputs: &'ty [Ty<'ty>],
    pub output: Ty<'ty>,
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
        println!("ItemGatherer `visit_thing` {}", thing.def_id);
        match thing.kind {
            ThingKind::Fn { name: _, sig } => {
                self.sess.lower_fn_sig(*sig, thing.def_id);
            }

            ThingKind::Instance { fields: _, name: _ } => {
                self.sess.instance_def(thing.def_id);
            } // Nothing to do

            ThingKind::Bind(bind) => {
                for bind_item in bind.items {
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind<'ty> {
    Bool,
    Uint(IntTy),
    Int(IntTy),

    Float,
    Double,

    /// Instances somehow idk lol !
    Instance(Instance<'ty>),

    /// fun(ty) -> ty
    Fn {
        inputs: &'ty [Ty<'ty>],
        output: Ty<'ty>,
    },

    /// Anon type of function def
    FnDef(DefId),

    /// `[ty]`
    Array(Ty<'ty>),

    /// nil.
    Nil,

    /// Type wasn't properly formed.
    Error,

    /// Diverging computation
    Diverges,

    /// For inference
    InferTy(InferTy),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InferTy {
    pub vid: InferId,
    pub kind: InferKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InferKind {
    Float,
    Integer,
    Regular,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceDef<'ty> {
    pub fields: &'ty FieldSlice<FieldDef>,
    pub name: SymbolId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldDef {
    pub mutable: Constant,
    pub name: SymbolId,
    pub def_id: DefId,
}

#[derive(Debug, Clone)]
pub enum TypingError {
    TypeMismatch(Cow<'static, str>, Cow<'static, str>),

    NoIndexOp {
        on: Cow<'static, str>,
    },

    NoUnaryOp {
        on: Cow<'static, str>,
    },

    NoBinaryOp {
        lhs: Cow<'static, str>,
        rhs: Cow<'static, str>,
    },

    CallingNotFn {
        offender: Cow<'static, str>,
    },

    WrongArgumentTy {
        expected: Cow<'static, str>,
        got: Cow<'static, str>,
        arg_idx: usize,
    },

    WrongArgumentAmnt {
        amount_given: usize,
        amount_req: usize,
    },

    NoField {
        on: Cow<'static, str>,
        field_name: SymbolId,
    },

    NotInstance {
        got: Cow<'static, str>,
    },

    MethodNotFound {
        on_ty: Cow<'static, str>,
        method_name: Cow<'static, str>,
    },
}

impl TheresError for TypingError {
    fn phase() -> &'static str {
        "typing"
    }

    #[track_caller]
    fn span(&self) -> Span {
        unimplemented!("loc: {}", Location::caller())
    }

    fn message(&self) -> Cow<'static, str> {
        match self {
            TypingError::TypeMismatch(expected, got) => {
                format!("Expected type: {expected}, got: {got}")
            }
            TypingError::NoIndexOp { on } => format!("No index operation for type: {on}"),
            TypingError::NoUnaryOp { on } => format!("No unary operation for type: {on}"),
            TypingError::NoBinaryOp { lhs, rhs } => {
                format!("No binary operation like that for type {lhs} and {rhs}")
            }
            TypingError::CallingNotFn { offender } => format!("Attempting to call type {offender}"),
            TypingError::WrongArgumentTy {
                expected,
                got,
                arg_idx,
            } => format!("Argument {arg_idx} has type {got}, but expected type was: {expected}"),
            TypingError::WrongArgumentAmnt {
                amount_given,
                amount_req,
            } => {
                format!("Invalid amount of arguments, got: {amount_given}, expected: {amount_req}")
            }
            TypingError::NotInstance { got } => {
                format!("Attempted to access a field on type {got}")
            }
            TypingError::NoField { on, field_name } => {
                format!("There is no field {field_name} on type {on}")
            }
            TypingError::MethodNotFound { on_ty, method_name } => {
                format!("No method named {method_name} present on type {on_ty}")
            }
        }
        .into()
    }

    fn amount_of_extra_lines() -> usize {
        2
    }
}

enum Constraint<'ty> {
    Equals { left: Ty<'ty>, right: Ty<'ty> },
}

pub struct FunCx<'ty> {
    s: &'ty Session<'ty>,
    fn_ret_ty: Option<Ty<'ty>>,

    node_type: HashMap<HirId, Ty<'ty>>,

    ty_var_types: HashMap<InferId, Ty<'ty>>,

    infer_ty_counter: u32,

    constraints: Vec<Constraint<'ty>>,
}

pub struct UnifyError;

impl<'ty> FunCx<'ty> {
    fn new(s: &'ty Session<'ty>) -> Self {
        Self {
            s,
            ty_var_types: HashMap::new(),
            infer_ty_counter: 0,
            fn_ret_ty: None,
            node_type: HashMap::new(),
            constraints: vec![],
        }
    }

    fn start(&mut self, sig: FnSig<'ty>, body: BodyId) {
        self.fn_ret_ty = Some(sig.output);

        let body = self.s.hir_ref().get_body(body);

        let actual_ret_ty = self.typeck_expr(body);

        if self.unify(sig.output, actual_ret_ty).is_err() {
            todo!("Fun return type doesn't unify with the actual one")
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

    fn unify(&mut self, left: Ty<'ty>, right: Ty<'ty>) -> Result<(), UnifyError> {
        match (*left, *right) {
            (TyKind::Bool, TyKind::Bool)
            | (TyKind::Float, TyKind::Float)
            | (TyKind::Double, TyKind::Double) => {}

            (TyKind::Instance(l), TyKind::Instance(r)) if l == r => {}

            (TyKind::Uint(size_l), TyKind::Uint(size_r))
            | (TyKind::Int(size_l), TyKind::Int(size_r))
                if size_l == size_r => {}

            (TyKind::Array(ty_left), TyKind::Array(ty_right)) => self.unify(ty_left, ty_right)?,

            (TyKind::InferTy(infer), concrete) | (concrete, TyKind::InferTy(infer)) => {
                match self.ty_var_types.get(&infer.vid) {
                    None => {
                        self.ty_var_types
                            .insert(infer.vid, self.s.intern_ty(concrete));
                    }

                    Some(ty) => return self.unify(*ty, self.s.intern_ty(concrete)),
                }
            }

            _ => return Err(UnifyError),
        }

        Ok(())
    }

    fn type_mismatch_err(&self, expected: Ty<'ty>, got: Ty<'ty>, span: Span) {
        self.s.diag().emit_err(
            TypingError::TypeMismatch(self.s.stringify_ty(expected), self.s.stringify_ty(got)),
            span,
        );
    }

    pub fn typeck_local(&mut self, local: &Local<'_>) -> Ty<'ty> {
        let init_ty = local.init.map(|expr| self.typeck_expr(expr));
        let local_decl_ty = self.s.lower_ty(local.ty);

        if let Some(ty) = init_ty
            && let Err(..) = self.unify(ty, local_decl_ty)
        {
            self.type_mismatch_err(local_decl_ty, ty, local.ty.span);
        }

        local_decl_ty
    }

    pub fn typeck_stmt(&mut self, stmt: &Stmt<'_>) {
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
    pub fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        match expr.kind {
            ExprKind::Literal(lit) => match lit {
                HirLiteral::Bool(..) => self.s.bool(),
                HirLiteral::Uint(..) | HirLiteral::Int(..) => {
                    self.new_infer_var(InferKind::Integer)
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

                dbg!(function, callable);

                let TyKind::FnDef(def_id) = *callable.0 else {
                    self.s.diag().emit_err(
                        TypingError::CallingNotFn {
                            offender: "".into(), // not sure?
                        },
                        expr.span,
                    );

                    return self.s.ty_err();
                };

                dbg!(def_id);

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
                    Resolved::Def(def_id, DefType::Fun) => {
                        self.s.intern_ty(dbg!(TyKind::FnDef(def_id)))
                    }

                    Resolved::Local(hir_id) => {
                        let hir = self.s.hir_ref();
                        self.typeck_local(hir.get_local(hir_id))
                    }

                    Resolved::Def(def_id, DefType::Const) => self.s.def_type_of(def_id),

                    any => unreachable!("what the fuck? {any:?}"),
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
        }
    }

    pub fn typeck_block(&mut self, block: &Block<'_>) -> Ty<'ty> {
        for stmt in block.stmts {
            self.typeck_stmt(stmt);
        }

        block.expr.map_or(self.s.nil(), |expr| self.type_of(expr))
    }

    pub fn type_of(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
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

pub struct TypeEnv<'ty> {
    sess: &'ty Session<'ty>,
    expr_to_ty: HashMap<HirId, Ty<'ty>>,

    current_fn_ret_ty: Option<Ty<'ty>>,
}

impl<'ty> TypeEnv<'ty> {
    pub fn new(sess: &'ty Session<'ty>) -> Self {
        Self {
            sess,
            current_fn_ret_ty: None,
            expr_to_ty: HashMap::new(),
        }
    }

    pub fn typeck_universe(&mut self, universe: &'ty Universe<'ty>) {
        for thing in universe.things {
            self.typeck_thing(thing);
        }
    }

    pub fn type_of(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        if let Some(ty) = self.expr_to_ty.get(&expr.hir_id) {
            return *ty;
        }

        let expr_ty = self.typeck_expr(expr);
        self.expr_to_ty.insert(expr.hir_id, expr_ty);
        expr_ty
    }

    pub fn typeck_thing(&mut self, thing: &Thing<'_>) {
        match thing.kind {
            ThingKind::Fn { name: _, sig } => self.typeck_fn(sig),
            ThingKind::Realm { name: _, things } => {
                for thing in things {
                    self.typeck_thing(thing);
                }
            }
            ThingKind::Instance { fields: _, name: _ } => (), // do nothing for now

            ThingKind::Global {
                mutability: _,
                name: _,
                init,
                ty,
            } => {
                let decl_ty = self.sess.lower_ty(ty);
                let expr_ty = self.type_of(init);

                if decl_ty == expr_ty {
                    self.sess.diag().emit_err(
                        TypingError::TypeMismatch(
                            self.sess.stringify_ty(decl_ty),
                            self.sess.stringify_ty(decl_ty),
                        ),
                        ty.span,
                    );
                }
            }

            ThingKind::Bind(ref bind) => self.typeck_bind(bind),
        }
    }

    pub fn typeck_bind(&mut self, bind: &Bind<'_>) {
        for item in bind.items {
            match item.kind {
                BindItemKind::Fun { sig, name: _ } => self.typeck_fn(sig),

                BindItemKind::Const { ty, expr, sym: _ } => {
                    let const_decl_ty = self.sess.lower_ty(ty);
                    let expr_ty = self.typeck_expr(expr);

                    if expr_ty != const_decl_ty {
                        self.sess.diag().emit_err(
                            TypingError::TypeMismatch(
                                self.sess.stringify_ty(const_decl_ty),
                                self.sess.stringify_ty(expr_ty),
                            ),
                            ty.span,
                        );
                    }
                }
            }
        }
    }

    pub fn typeck_fn(&mut self, sig: &node::FnSig<'_>) {
        let body = self.sess.hir(|h| h.get_body(sig.body));
        let return_type = self.sess.lower_ty(sig.return_type);

        let ty = self.typeck_expr(body);

        let left = self.sess.stringify_ty(return_type);
        let right = self.sess.stringify_ty(ty);

        if return_type != ty {
            self.sess
                .diag()
                .emit_err(TypingError::TypeMismatch(left, right), sig.span);
        }
    }

    #[allow(clippy::too_many_lines)]
    pub fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        match expr.kind {
            ExprKind::Literal(lit) => match lit {
                HirLiteral::Bool(..) => self.sess.bool(),
                HirLiteral::Uint(..) | HirLiteral::Int(..) => todo!(),

                HirLiteral::Str(_sym) => todo!("idk how to type strings yet Ok!"),

                HirLiteral::Float(..) => self.sess.f64(),
            },

            ExprKind::Binary { lhs, rhs, op: _ } => {
                let ty_lhs = self.type_of(lhs);
                let ty_rhs = self.type_of(rhs);

                #[allow(clippy::match_same_arms)] // todo
                match (*ty_lhs, *ty_rhs) {
                    (TyKind::Uint(int_l), TyKind::Uint(int_r)) if int_l == int_r => ty_lhs,
                    (TyKind::Int(int_l), TyKind::Int(int_r)) if int_l == int_r => ty_lhs,
                    (TyKind::Float, TyKind::Float) => ty_lhs,
                    (TyKind::Double, TyKind::Double) => ty_lhs,
                    (_, _) => {
                        self.sess.diag().emit_err(
                            TypingError::NoBinaryOp {
                                lhs: self.sess.stringify_ty(ty_lhs),
                                rhs: self.sess.stringify_ty(ty_rhs),
                            },
                            Span::between(lhs.span, rhs.span),
                        );

                        self.sess.ty_err()
                    }
                }
            }

            ExprKind::Unary { target, op: _ } => {
                let ty = self.type_of(target);

                if let TyKind::Bool | TyKind::Uint(..) | TyKind::Int(..) = *ty {
                    return ty;
                }

                self.sess.diag().emit_err(
                    TypingError::NoUnaryOp {
                        on: self.sess.stringify_ty(ty),
                    },
                    target.span,
                );

                self.sess.ty_err()
            }

            ExprKind::Paren { inner } => self.type_of(inner),

            ExprKind::Assign { variable, value } => {
                let variable_ty = self.type_of(variable);
                let value_ty = self.type_of(value);

                if variable_ty != value_ty {
                    self.sess.diag().emit_err(
                        TypingError::TypeMismatch(
                            self.sess.stringify_ty(variable_ty),
                            self.sess.stringify_ty(value_ty),
                        ),
                        Span::between(variable.span, value.span),
                    );
                }

                self.sess.nil()
            }

            ExprKind::If {
                condition,
                block,
                else_ifs,
                otherwise,
            } => {
                let cond_ty = self.type_of(condition);
                if *cond_ty != TyKind::Bool {
                    self.type_mismatch_err(self.sess.bool(), cond_ty, condition.span);
                }

                let ret_ty = self.typeck_block(block);

                for (block, elsif) in else_ifs {
                    let block_ty = self.typeck_block(block);
                    if block_ty != ret_ty {
                        self.sess.diag().emit_err(
                            TypingError::TypeMismatch(
                                self.sess.stringify_ty(block_ty),
                                self.sess.stringify_ty(ret_ty),
                            ),
                            Span::between(block.span, elsif.span),
                        );
                    }

                    let elsif_ty = self.type_of(elsif);

                    if *elsif_ty != TyKind::Bool {
                        self.sess.diag().emit_err(
                            TypingError::TypeMismatch(
                                "bool".into(),
                                self.sess.stringify_ty(elsif_ty),
                            ),
                            elsif.span,
                        );
                    }
                }

                if let Some(otherwise_block) = otherwise
                    && self.typeck_block(otherwise_block) != ret_ty
                {
                    let block_ty = self.typeck_block(otherwise_block);

                    if ret_ty != block_ty {
                        self.sess.diag().emit_err(
                            TypingError::TypeMismatch(
                                self.sess.stringify_ty(block_ty),
                                self.sess.stringify_ty(ret_ty),
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
                    self.sess.diag().emit_err(
                        TypingError::CallingNotFn {
                            offender: "".into(), // not sure?
                        },
                        expr.span,
                    );

                    return self.sess.ty_err();
                };

                self.verify_arguments_for_call(def_id, args, expr.span)
            }

            ExprKind::Return { expr: ret_expr } => {
                let ty = ret_expr.map_or(self.sess.nil(), |elm| self.type_of(elm));

                let ret_ty = self
                    .current_fn_ret_ty
                    .expect("return should only be present in function");

                if ret_ty != ty {
                    self.type_mismatch_err(ret_ty, ty, ret_expr.map_or(expr.span, |s| s.span));
                }

                self.sess.ty_diverge()
            }

            ExprKind::AssignWithOp {
                variable,
                value,
                op,
            } => {
                let variable_ty = self.type_of(variable);
                let expr_ty = self.type_of(value);

                match (*variable_ty, *expr_ty) {
                    (TyKind::Uint(int_l), TyKind::Uint(int_r)) if int_l == int_r => expr_ty,

                    (TyKind::Double, TyKind::Double)
                    | (TyKind::Float, TyKind::Float)
                    | (TyKind::Int(..), TyKind::Int(..)) => expr_ty,
                    (left, right) => todo!("No binary op ({op:?}) for {left:?} and {right:?}"),
                };

                self.sess.nil()
            }

            ExprKind::Field {
                src,
                field: field_name,
            } => {
                let src_ty = self.type_of(src);
                let err = if let TyKind::Instance(def) = src_ty.0 {
                    if let Some(found) = def.fields.iter().find(|f| f.name == field_name) {
                        return self.sess.def_type_of(found.def_id);
                    }

                    TypingError::NoField {
                        on: self.sess.stringify_ty(src_ty),
                        field_name,
                    }
                } else {
                    TypingError::NotInstance {
                        got: self.sess.stringify_ty(src_ty),
                    }
                };

                self.sess.diag().emit_err(err, src.span);
                self.sess.ty_err()
            }

            ExprKind::Loop { body, reason: _ } => {
                self.typeck_block(body);
                self.sess.nil()
            }

            ExprKind::Block(block) => self.typeck_block(block),

            ExprKind::Index {
                index,
                indexed_thing,
            } => {
                let src_ty = self.type_of(indexed_thing);

                let TyKind::Array(inner_ty) = src_ty.0 else {
                    self.sess.diag().emit_err(
                        TypingError::NoIndexOp {
                            on: self.sess.stringify_ty(src_ty),
                        },
                        expr.span,
                    );

                    return self.sess.ty_err();
                };

                let index_ty = self.type_of(index);

                if self.sess.u64() != index_ty {
                    self.type_mismatch_err(self.sess.u64(), index_ty, expr.span);
                }

                *inner_ty
            }

            ExprKind::Path(path) => {
                let res = path.res;

                match res {
                    Resolved::Def(def_id, DefType::Fun) => {
                        self.sess.intern_ty(TyKind::FnDef(def_id))
                    }

                    Resolved::Local(hir_id) => {
                        let hir = self.sess.hir_ref();
                        self.typeck_local(hir.get_local(hir_id))
                    }

                    Resolved::Def(def_id, DefType::Const) => self.sess.def_type_of(def_id),

                    any => unreachable!("what the fuck? {any:?}"),
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

            ExprKind::Break => self.sess.ty_diverge(),

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_ty = self.type_of(receiver);
                let mut ret_ty = self.sess.ty_err();

                self.sess.binds_for_ty(recv_ty, |binds| {
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
                        self.sess.diag().emit_err(
                            TypingError::MethodNotFound {
                                on_ty: self.sess.stringify_ty(recv_ty),
                                method_name: method.get_interned().to_string().into(),
                            },
                            receiver.span,
                        );
                        return;
                    };

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
                if self.sess.u64() != size_ty {
                    self.type_mismatch_err(self.sess.u64(), size_ty, expr.span);
                }

                let array_ty = self.sess.lower_ty(ty_of_array);

                for expr in init {
                    let expr_ty = self.type_of(expr);

                    if expr_ty != array_ty {
                        self.type_mismatch_err(array_ty, expr_ty, expr.span);
                    }
                }

                self.sess.intern_ty(TyKind::Array(array_ty))
            }
        }
    }

    pub fn typeck_block(&mut self, block: &Block<'_>) -> Ty<'ty> {
        for stmt in block.stmts {
            self.typeck_stmt(stmt);
        }

        block
            .expr
            .map_or(self.sess.nil(), |expr| self.type_of(expr))
    }

    pub fn typeck_stmt(&mut self, stmt: &Stmt<'_>) {
        match stmt.kind {
            StmtKind::Local(local) => {
                let _ = self.typeck_local(local);
            }
            StmtKind::Thing(thing) => self.typeck_thing(thing),
            StmtKind::Expr(expr) => {
                let _ = self.typeck_expr(expr);
            }
        }
    }

    pub fn typeck_local(&mut self, local: &Local<'_>) -> Ty<'ty> {
        let init_ty = local.init.map(|expr| self.typeck_expr(expr));
        let local_decl_ty = self.sess.lower_ty(local.ty);

        if let Some(ty) = init_ty
            && ty != local_decl_ty
        {
            self.type_mismatch_err(local_decl_ty, ty, local.ty.span);
        }

        local_decl_ty
    }

    fn type_mismatch_err(&self, expected: Ty<'ty>, got: Ty<'ty>, span: Span) {
        self.sess.diag().emit_err(
            TypingError::TypeMismatch(
                self.sess.stringify_ty(expected),
                self.sess.stringify_ty(got),
            ),
            span,
        );
    }

    fn verify_arguments_for_call(
        &mut self,
        def_id: DefId,
        args: &[Expr<'_>],
        span: Span,
    ) -> Ty<'ty> {
        let sig = self.sess.fn_sig_for(def_id);

        let amount_of_args = sig.inputs.len();
        let given_args = args.len();

        let mut sig_tys = self.sess.fn_sig_for(def_id).inputs.iter().copied();

        let mut call_tys = args.iter();

        if amount_of_args != given_args {
            self.sess.diag().emit_err(
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
                    if sig_ty != call_ty {
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

pub fn typeck_universe<'a>(session: &'a Session<'a>, universe: &'a Universe<'a>) -> TypeEnv<'a> {
    ItemGatherer::new(session).visit_universe(universe);

    session.hir(|map| {
        println!("DEFID 8");
        dbg!(map.get_def(hir::def::def_id(8)));
        //
    });

    // let mut env = TypeEnv::new(session);

    // env.typeck_universe(universe);

    for thing in universe.things {
        println!("item: {}", thing.def_id);
    }

    for thing in universe.things {
        if let ThingKind::Fn { name: _, sig } = thing.kind {
            let mut cx = FunCx::new(session);

            cx.start(session.fn_sig_for(thing.def_id), sig.body);
        }
    }

    todo!()
}
