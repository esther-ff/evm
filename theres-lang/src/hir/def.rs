use std::collections::HashMap;

use crate::ast::Name;
use crate::hir::node;
use crate::id::IdxVec;
use crate::session::SymbolId;

crate::newtyped_index!(DefId, DefMap, DefVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefType {
    Fun,
    Instance,
    Interface,
    Realm,
    Const,
    Field,
    Bind,
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

pub struct Definitions<'hir> {
    defs: HashMap<SymbolId, (DefType, DefId)>,
    fn_to_body: HashMap<DefId, BodyId>,
    bodies: BodyVec<&'hir node::Expr<'hir>>,

    id: u32,
}

impl Definitions<'_> {
    pub fn new() -> Self {
        Self {
            defs: HashMap::new(),
            fn_to_body: HashMap::new(),
            bodies: IdxVec::new(),
            id: 0,
        }
    }

    pub fn register_defn(&mut self, kind: DefType, name: SymbolId) -> DefId {
        let id = self.id();
        self.defs.insert(name, (kind, id));
        id
    }

    pub fn get_def_via_name(&self, name: SymbolId) -> Option<(DefType, DefId)> {
        self.defs.get(&name).copied()
    }

    fn id(&mut self) -> DefId {
        let id = DefId::new(self.id);
        self.id += 1;
        id
    }
}
