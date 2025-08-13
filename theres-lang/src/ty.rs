use crate::{
    hir::{
        def::{DefId, IntTy},
        node::Constant,
    },
    session::{Pooled, SymbolId},
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceDef<'ty> {
    fields: &'ty FieldSlice<FieldDef>,
    name: SymbolId,
    def_id: DefId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldDef {
    mutable: Constant,
    name: SymbolId,
    def_id: DefId,
}
