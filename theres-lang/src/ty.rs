use std::collections::HashMap;

use crate::{
    hir::{
        self,
        def::{DefId, IntTy},
        lowering_ast::HirId,
        node::{Constant, Expr, ExprKind, HirLiteral, Thing, ThingKind},
    },
    id::IdxSlice,
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

pub struct TypeEnv<'ty> {
    s: &'ty Session<'ty>,
    expr_to_ty: HashMap<&'ty Expr<'ty>, Ty<'ty>>,
    hir_id_to_ty: HashMap<HirId, Ty<'ty>>,
    self_ty: Option<Ty<'ty>>,
}

impl<'ty> TypeEnv<'ty> {
    pub fn new(s: &'ty Session<'ty>) -> Self {
        Self {
            s,
            expr_to_ty: HashMap::new(),
            hir_id_to_ty: HashMap::new(),
            self_ty: None,
        }
    }

    pub fn typeck_fn(&mut self, fun: &'ty ThingKind<'ty>) {
        let ThingKind::Fn { name: _, sig } = fun else {
            panic!("not fn thing-kind")
        };

        let body = self.s.hir(|h| h.get_body(sig.body));
        let return_type = self.s.lower_ty(sig.return_type, || {
            self.self_ty.unwrap_or_else(|| todo!("error!"))
        });
    }

    pub fn typeck_expr(&mut self, expr: &'ty Expr<'ty>) {
        match expr.kind {
            ExprKind::Literal(lit) => match lit {
                HirLiteral::Bool(..) => self.s.bool(),

                _ => todo!(),
            },

            _ => todo!(),
        };
    }
}
