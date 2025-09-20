crate::newtyped_index!(DefId, DefMap, DefVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);

// debug dogshit
pub fn def_id(i: u32) -> DefId {
    DefId { private: i }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefType {
    /// Function.
    Fun,

    /// Instance.
    Instance,

    /// Realm.
    Realm,

    /// Associated constant, might get removed.
    Const,

    /// Field of an instance.
    Field,

    /// Bind
    Bind,

    /// Associated item of a bind
    BindItem,

    /// Constructor of an `instance`
    AdtCtor,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum IntTy {
    N8,
    N16,
    N32,
    N64,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub enum PrimTy {
    Uint(IntTy),
    Int(IntTy),

    /// f32
    Float,
    /// f64
    Double,

    Nil,
    Bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Resolved<Id> {
    Def(DefId, DefType),
    Local(Id),
    Prim(PrimTy),

    Err,
}

impl<Id> Resolved<Id> {
    pub fn is_err(&self) -> bool {
        matches!(self, Resolved::Err)
    }
}
