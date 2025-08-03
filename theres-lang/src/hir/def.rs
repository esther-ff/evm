use std::collections::HashMap;

use crate::ast::Name;
use crate::hir::lowering_ast::HirId;
use crate::hir::{self, node};
use crate::id::IdxVec;
use crate::lexer::Span;

crate::newtyped_index!(DefId, DefMap, DefVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefType {
    Fun,
    Instance,
    Interface,
    Realm,
    Const,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Resolved<Id> {
    Def(DefId, DefType),
    Local(Id),
    Prim(PrimTy),

    Err,
}

pub struct AssocConst {
    span: Span,
    name: Name,
    ty: Ty,
}

pub struct Instance {
    name: Name,
    fields: Vec<Field>,
    constants: Vec<AssocConst>,
    methods: Vec<DefId>,
    span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mutability {
    None,
    Mutable,
}

pub struct Field {
    name: Name,
    ty: Ty,
    mutable: Mutability,
    span: Span,
}

pub struct FunArg {
    name: Name,
    ty: Ty,
}

pub struct Fn {
    name: Name,
    args: Vec<FunArg>,
    ret_ty: Ty,
    body: BodyId,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Ty {
    span: Span,
    name: Name,
    kind: TyKind,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum TyKind {
    /// Regular named type like `i32`
    Regular,

    // todo:
    // function types later
    // generics
    // path?
    /// For use in methods,
    MethodSelf,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct FnBody(pub(crate) hir::expr::Block);

pub struct Definitions<'hir> {
    map_instance: HashMap<DefId, Instance>,
    map_fun: HashMap<DefId, Fn>,

    fn_to_body: HashMap<DefId, BodyId>,
    bodies: BodyVec<&'hir node::Expr<'hir>>,

    def_id_to_hir_id: DefMap<HirId>,

    id: u32,
}

impl<'hir> Definitions<'hir> {
    pub fn new() -> Self {
        Self {
            map_instance: HashMap::new(),
            map_fun: HashMap::new(),
            fn_to_body: HashMap::new(),
            bodies: IdxVec::new(),
            def_id_to_hir_id: HashMap::new(),

            id: 0,
        }
    }

    pub fn new_id(&mut self) -> DefId {
        let id = DefId { private: self.id };
        self.id += 1;
        id
    }

    pub fn register_body(&mut self, expr: &'hir node::Expr<'hir>, def_id: DefId) -> BodyId {
        let body_id = self.bodies.push(expr);
        self.fn_to_body.insert(def_id, body_id);
        body_id
    }

    pub fn map_def_id_to_hir(&mut self, def_id: DefId, hir_id: HirId) {
        self.def_id_to_hir_id.insert(def_id, hir_id);
    }
}
