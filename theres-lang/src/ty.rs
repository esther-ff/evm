use std::{cmp::Ordering, collections::HashMap, panic::Location};

use crate::{
    errors::TheresError,
    hir::{
        def::{DefId, DefType, IntTy, Resolved},
        lowering_ast::HirId,
        node::{
            Bind, BindItemKind, Block, Constant, Expr, ExprKind, FnSig, HirLiteral, Local, Stmt,
            StmtKind, Thing, ThingKind, Universe,
        },
    },
    session::{Pooled, Session, SymbolId},
};

/// Interned type.
pub type Ty<'ty> = Pooled<'ty, TyKind<'ty>>;

/// Interned instance data.
pub type Instance<'ty> = Pooled<'ty, InstanceDef<'ty>>;

crate::newtyped_index!(FieldId, FieldMap, FieldVec, FieldSlice);

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

    /// Diverging!
    ///
    /// Computation that never happens due to something
    /// like an abort.
    ///
    /// Unifies with any type
    Diverges,

    /// Type wasn't properly formed.
    Error,
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
    TypeMismatch {
        expected: String,
        got: String,
    },

    NoIndexOp {
        on: String,
    },

    NoUnaryOp {
        on: String,
    },

    NoBinaryOp {
        lhs: String,
        rhs: String,
    },

    CallingNotFn {
        offender: String,
    },

    WrongArgumentTy {
        expected: String,
        got: String,
        arg_idx: usize,
    },

    WrongArgumentAmnt {
        amount: usize,
    },

    NoField {
        on: String,
        field_name: SymbolId,
    },

    NotInstance {
        got: String,
    },
}

impl TheresError for TypingError {
    fn phase() -> &'static str {
        "typing"
    }

    fn span(&self) -> crate::lexer::Span {
        unimplemented!()
    }

    fn message(&self) -> std::borrow::Cow<'static, str> {
        "type mismatch".into()
    }

    fn amount_of_extra_lines() -> usize {
        2
    }
}

pub struct TypeEnv<'ty> {
    sess: &'ty Session<'ty>,
    expr_to_ty: HashMap<&'ty Expr<'ty>, Ty<'ty>>,
    hir_id_to_ty: HashMap<HirId, Ty<'ty>>,
    self_ty: Option<Ty<'ty>>,

    current_fn_ret_ty: Option<Ty<'ty>>,
}

impl<'ty> TypeEnv<'ty> {
    pub fn new(sess: &'ty Session<'ty>) -> Self {
        Self {
            sess,
            current_fn_ret_ty: None,
            expr_to_ty: HashMap::new(),
            hir_id_to_ty: HashMap::new(),
            self_ty: None,
        }
    }

    pub fn set_self_ty(&mut self, ty: Ty<'ty>) {
        self.self_ty.replace(ty);
    }

    #[track_caller]
    pub fn get_self_ty(&mut self) -> Ty<'ty> {
        self.self_ty.unwrap_or_else(|| {
            unreachable!(
                "self type should be present or shouldn't be used\n loc:{:#?}",
                Location::caller()
            )
        })
    }

    pub fn typeck_universe(&mut self, universe: &'ty Universe<'ty>) {
        for thing in universe.things {
            self.typeck_thing(thing);
        }
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
                let decl_ty = self
                    .sess
                    .lower_ty(ty, || unreachable!("no method self in globals"));
                let expr_ty = self.typeck_expr(init);

                if decl_ty == expr_ty {
                    todo!("type in declared global is wrong")
                }
            }

            ThingKind::Bind(ref bind) => self.typeck_bind(bind),
        }
    }

    pub fn typeck_bind(&mut self, bind: &Bind<'_>) {
        let bind_self_ty = self.sess.lower_ty(bind.with, || self.get_self_ty());
        self.self_ty.replace(bind_self_ty);

        for item in bind.items {
            match item.kind {
                BindItemKind::Fun { sig, name: _ } => self.typeck_fn(sig),

                BindItemKind::Const { ty, expr, sym: _ } => {
                    let const_decl_ty = self.sess.lower_ty(ty, || self.get_self_ty());
                    let expr_ty = self.typeck_expr(expr);

                    if expr_ty != const_decl_ty {
                        todo!("type mismatch")
                    }
                }
            }
        }
    }

    pub fn typeck_fn(&mut self, sig: &FnSig<'_>) {
        let body = self.sess.hir(|h| h.get_body(sig.body));
        let return_type = self.sess.lower_ty(sig.return_type, || self.get_self_ty());

        let ty = self.typeck_expr(body);

        if return_type != ty {
            todo!("fn ret type doesn't unify with body ty")
        }
    }

    #[allow(clippy::too_many_lines)]
    pub fn typeck_expr(&mut self, expr: &Expr<'_>) -> Ty<'ty> {
        match expr.kind {
            ExprKind::Literal(lit) => match lit {
                HirLiteral::Bool(..) => self.sess.bool(),
                HirLiteral::Uint(num) => match num_to_int_ty(num) {
                    IntTy::N8 => self.sess.u8(),
                    IntTy::N16 => self.sess.u16(),
                    IntTy::N32 => self.sess.u32(),
                    IntTy::N64 => self.sess.u64(),
                },

                HirLiteral::Int(num) => match num_to_int_ty(num.cast_unsigned()) {
                    IntTy::N8 => self.sess.i8(),
                    IntTy::N16 => self.sess.i16(),
                    IntTy::N32 => self.sess.i32(),
                    IntTy::N64 => self.sess.i64(),
                },

                HirLiteral::Str(_sym) => todo!("idk how to type strings yet Ok!"),

                HirLiteral::Float(_float) => self.sess.f64(),
            },

            ExprKind::Binary { lhs, rhs, op } => {
                let ty_lhs = self.typeck_expr(lhs);
                let ty_rhs = self.typeck_expr(rhs);

                match (*ty_lhs, *ty_rhs) {
                    (TyKind::Uint(int_l), TyKind::Uint(int_r)) if int_l == int_r => ty_lhs,
                    (TyKind::Int(..), TyKind::Int(..)) => todo!(),
                    (TyKind::Float, TyKind::Float) => todo!(),
                    (TyKind::Double, TyKind::Double) => todo!(),
                    (left, right) => todo!("No binary op ({op:?}) for {left:?} and {right:?}"),
                }
            }

            ExprKind::Unary { target, op } => {
                let ty = self.typeck_expr(target);

                if let TyKind::Bool | TyKind::Uint(..) | TyKind::Int(..) = *ty {
                    return ty;
                }

                todo!("no unary op ({op:?}) for {ty:?}");
            }

            ExprKind::Paren { inner } => self.typeck_expr(inner),

            ExprKind::Assign { variable, value } => {
                if self.typeck_expr(variable) != self.typeck_expr(value) {
                    todo!("can't assign {value:?} to {variable:?}")
                }

                self.sess.nil()
            }

            ExprKind::If {
                condition,
                block,
                else_ifs,
                otherwise,
            } => {
                if *self.typeck_expr(condition) != TyKind::Bool {
                    todo!("if cond can only be bool")
                }

                let ret_ty = self.typeck_block(block);

                for (block, elsif) in else_ifs {
                    if self.typeck_block(block) != ret_ty {
                        todo!("else if block has invalid type compared to {ret_ty:?}")
                    }

                    if *self.typeck_expr(elsif) != TyKind::Bool {
                        todo!("else if in if cond can only be bool")
                    }
                }

                if let Some(otherwise_block) = otherwise
                    && self.typeck_block(otherwise_block) != ret_ty
                {
                    todo!("otherwise block has diff type than original block")
                }

                ret_ty
            }

            ExprKind::Call { function, args } => {
                let callable = self.typeck_expr(function);

                let TyKind::FnDef(def_id) = callable.0 else {
                    todo!("calling not a function")
                };

                let hir = self.sess.hir_ref();
                let (sig, name) = hir.expect_fn(*def_id);

                for (param, arg) in sig.arguments.iter().zip(args.iter()) {
                    let param_ty = self.sess.lower_ty(param.ty, || self.get_self_ty());
                    let arg_ty = self.typeck_expr(arg);

                    if param_ty != arg_ty {
                        todo!(
                            "parameter has wrong type in fn: {}",
                            name.interned.get_interned()
                        )
                    }
                }

                self.sess.lower_ty(sig.return_type, || self.get_self_ty())
            }

            ExprKind::Return { expr } => {
                let ty = expr.map_or(self.sess.nil(), |elm| self.typeck_expr(elm));

                let ret_ty = self
                    .current_fn_ret_ty
                    .expect("return should only be present in function");

                if ret_ty != ty {
                    todo!("return expr's ty is wrong compared to function ret ty")
                }

                self.sess.ty_diverge()
            }

            ExprKind::AssignWithOp {
                variable,
                value,
                op,
            } => {
                let variable_ty = self.typeck_expr(variable);
                let expr_ty = self.typeck_expr(value);

                match (*variable_ty, *expr_ty) {
                    (TyKind::Uint(int_l), TyKind::Uint(int_r)) if int_l == int_r => expr_ty,

                    (TyKind::Double, TyKind::Double)
                    | (TyKind::Float, TyKind::Float)
                    | (TyKind::Int(..), TyKind::Int(..)) => expr_ty,
                    (left, right) => todo!("No binary op ({op:?}) for {left:?} and {right:?}"),
                };

                self.sess.nil()
            }

            ExprKind::Field { src, field } => {
                let src_ty = self.typeck_expr(src);

                if let TyKind::Instance(def) = src_ty.0 {
                    if let Some(found) = def.fields.iter().find(|f| f.name == field) {
                        return self.sess.def_type_of(found.def_id);
                    }

                    todo!("error: field named like {} not found", field.get_interned())
                } else {
                    todo!("src was not an instance but: {src:#?}")
                }
            }

            ExprKind::Loop { .. } => self.sess.nil(),

            ExprKind::Block(block) => self.typeck_block(block),

            ExprKind::Index {
                index,
                indexed_thing,
            } => {
                let src_ty = self.typeck_expr(indexed_thing);

                let TyKind::Array(inner_ty) = src_ty.0 else {
                    todo!("indexed thing is not an array!")
                };

                if self.sess.u64() != self.typeck_expr(index) {
                    todo!("index only by u64")
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

                    any => todo!("what the fuck? {any:?}"),
                }
            }

            ExprKind::CommaSep(exprs) => exprs
                .iter()
                .fold(None, |state, expr| {
                    if state.is_none() {
                        return Some(self.typeck_expr(expr));
                    }
                    self.typeck_expr(expr);
                    state
                })
                .expect("cannot fail as comma'd exprs have >1 exprs!"),

            ExprKind::Break => self.sess.ty_diverge(),

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_ty = self.typeck_expr(receiver);
                let mut ret_ty = self.sess.ty_err();

                self.sess.binds_for_ty(recv_ty, |binds| {
                    let Some((res_sig, _res_name)) = binds
                        .iter()
                        .flat_map(|x| x.items.iter())
                        .filter_map(|item| {
                            let BindItemKind::Fun { sig, name } = item.kind else {
                                return None;
                            };

                            Some((sig, name))
                        })
                        .find(|(_, name)| name == &method)
                    else {
                        return;
                    };

                    let self_ty = self.get_self_ty();
                    let mut sigs = res_sig
                        .arguments
                        .iter()
                        .map(|param| self.sess.lower_ty(param.ty, || self_ty));

                    let mut call_tys = args.iter().map(|expr| self.typeck_expr(expr));

                    let amount_of_args = res_sig.arguments.len();
                    let given_args = args.len();

                    match amount_of_args.cmp(&given_args) {
                        Ordering::Less => todo!("function call has less arguments than needed"),
                        Ordering::Greater => todo!("function call has more arguments than needed"),
                        Ordering::Equal => (),
                    }

                    let mut ix = 1;
                    loop {
                        match (sigs.next(), call_tys.next()) {
                            (Some(sig_ty), Some(call_ty)) => {
                                if sig_ty != call_ty {
                                    todo!("argument {ix} had wrong type")
                                }

                                ix += 1;
                            }
                            (Some(..), None) | (None, Some(..)) => {
                                ix += 1;
                                continue;
                            }
                            (None, None) => break,
                        }

                        ix += 1;
                    }

                    ret_ty = self
                        .sess
                        .lower_ty(res_sig.return_type, || todo!("method self"));
                });

                ret_ty
            }

            ExprKind::Array {
                ty_of_array,
                init,
                size,
            } => {
                if self.sess.u64() != self.typeck_expr(size) {
                    todo!("type for array size isn't u64")
                }

                let array_ty = self.sess.lower_ty(ty_of_array, || self.get_self_ty());

                for expr in init {
                    let expr_ty = self.typeck_expr(expr);

                    if expr_ty != array_ty {
                        todo!("ty: {expr_ty:?} is incompatible with {array_ty:?}")
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
            .map_or(self.sess.nil(), |expr| self.typeck_expr(expr))
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
        let local_decl_ty = self.sess.lower_ty(local.ty, || self.get_self_ty());

        if let Some(ty) = init_ty
            && ty != local_decl_ty
        {
            todo!("ty is wrong")
        }

        init_ty.unwrap_or(local_decl_ty)
    }
}

#[allow(clippy::checked_conversions, clippy::cast_lossless)]
fn num_to_int_ty(num: u64) -> IntTy {
    if num <= u8::MAX as u64 {
        IntTy::N8
    } else if num <= u16::MAX as u64 {
        IntTy::N16
    } else if num <= u32::MAX as u64 {
        IntTy::N32
    } else {
        IntTy::N64
    }
}
