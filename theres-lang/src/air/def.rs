use crate::{air::name_res::Namespace, symbols::SymbolId};

crate::newtyped_index!(DefId, DefMap, DefVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);

// debug dogshit
pub fn def_id(i: u32) -> DefId {
    DefId { private: i }
}

#[derive(Clone, Copy)]
pub enum DefPathSeg {
    TypeNs(SymbolId),
    ValueNs(SymbolId),
    BindBlock,
    Lambda,
}

#[derive(Clone)]
pub struct DefPath {
    segments: Vec<DefPathSeg>,
}

impl DefPath {
    pub fn new() -> Self {
        Self { segments: vec![] }
    }

    pub fn pop(&mut self) {
        self.segments.pop();
    }

    pub fn push_lambda(&mut self) {
        self.segments.push(DefPathSeg::Lambda);
    }

    pub fn push_bind(&mut self) {
        self.segments.push(DefPathSeg::BindBlock);
    }

    pub fn push_ns(&mut self, sym: SymbolId, ns: Namespace) {
        self.segments.push(match ns {
            Namespace::Types => DefPathSeg::TypeNs(sym),
            Namespace::Values => DefPathSeg::ValueNs(sym),
        });
    }

    pub fn inner(&self) -> &[DefPathSeg] {
        &self.segments
    }
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

    /// Enviroment of a lambda
    Lambda,
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
