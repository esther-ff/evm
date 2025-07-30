use std::collections::HashMap;

use crate::ast::{self, Arg, FnDecl, FnSig, Name};
use crate::hir;
use crate::lexer::Span;
use crate::session::SymbolId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefType {
    Fun,
    Instance,
    Interface,
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Resolved<Id> {
    Def(DefId, DefType),
    Local(Id),
    Prim(PrimTy),

    Err,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefId {
    private: u32,
}

impl DefId {
    pub const DUMMY: Self = Self { private: u32::MAX };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BodyId {
    pub(crate) private: u32,
}

impl BodyId {
    pub const DUMMY: Self = Self { private: u32::MAX };
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

pub struct Definitions {
    map_instance: HashMap<DefId, Instance>,
    map_fun: HashMap<DefId, Fn>,

    fn_to_body: HashMap<DefId, BodyId>,
    bodies: Vec<FnBody>,
    id: u32,
}

impl Definitions {
    pub fn new() -> Self {
        Self {
            map_instance: HashMap::new(),
            map_fun: HashMap::new(),
            fn_to_body: HashMap::new(),
            bodies: Vec::new(),

            id: 0,
        }
    }

    pub fn new_id(&mut self) -> DefId {
        let id = DefId { private: self.id };
        self.id += 1;
        id
    }
}
