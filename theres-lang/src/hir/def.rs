use std::collections::HashMap;

use crate::ast::{self, Arg, FnDecl, FnSig, Name};
use crate::hir;
use crate::lexer::Span;
use crate::session::SymbolId;

pub enum DefType {
    Fun,
    Instance,
    Interface,
}

pub enum Resolved {
    Def(DefId, DefType),
    Local,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefId {
    private: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BodyId {
    pub(crate) private: u32,
}

impl BodyId {
    pub const DUMMY: Self = Self { private: u32::MAX };
}

pub struct Interface {}

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
    map_interface: HashMap<DefId, Interface>,
    map_fun: HashMap<DefId, Fn>,

    fn_to_body: HashMap<DefId, BodyId>,
    bodies: Vec<FnBody>,
    id: u32,
}

impl Definitions {
    pub fn new() -> Self {
        Self {
            map_instance: HashMap::new(),
            map_interface: HashMap::new(),
            map_fun: HashMap::new(),
            fn_to_body: HashMap::new(),
            bodies: Vec::new(),

            id: 0,
        }
    }

    pub fn insert_interface(&mut self, _intrf: &ast::Interface) -> DefId {
        todo!("Interface to def")
    }

    pub fn insert_instance(&mut self, inst: &ast::Instance) -> DefId {
        let ast::Instance {
            name,
            span,
            fields,
            assoc: _,
            generics,
        } = inst;

        if generics.params.len() != 0 {
            todo!("todo! generics")
        }

        let new_instance = Instance {
            span: *span,
            name: *name,
            constants: Vec::new(),
            methods: Vec::new(),
            fields: fields
                .iter()
                .map(
                    |ast::Field {
                         constant,
                         name,
                         ty,
                         span,
                     }| {
                        let mutable = if *constant {
                            Mutability::None
                        } else {
                            Mutability::Mutable
                        };

                        Field {
                            mutable,
                            name: *name,
                            ty: lower_ast_ty_to_hir_ty(ty),
                            span: *span,
                        }
                    },
                )
                .collect::<Vec<_>>(),
        };

        let id = self.new_id();
        self.map_instance.insert(id, new_instance);
        id
    }

    pub fn insert_fn(&mut self, fun: &FnDecl) -> DefId {
        let FnDecl {
            sig,
            block: _,
            span: _,
        } = fun;

        let FnSig {
            name,
            args,
            ret_type,
            span: _,
        } = sig;

        let fn_args = args
            .args
            .iter()
            .map(|Arg { ident, ty }| {
                let new_ty = lower_ast_ty_to_hir_ty(&ty);
                FunArg {
                    name: *ident,
                    ty: new_ty,
                }
            })
            .collect::<Vec<_>>();

        let hir_fn = Fn {
            args: fn_args,
            ret_ty: lower_ast_ty_to_hir_ty(&ret_type),
            name: *name,
            body: BodyId::DUMMY,
        };

        let id = self.new_id();
        self.map_fun.insert(id, hir_fn);
        id
    }

    pub fn connect_fn_body_to_parent(&mut self, body: FnBody, fn_id: DefId) {
        self.map_fun
            .get_mut(&fn_id)
            .expect("function referenced doesn't exist")
            .body
            .private = self.bodies.len() as u32;
        self.bodies.push(body)
    }

    fn new_id(&mut self) -> DefId {
        let id = DefId { private: self.id };

        self.id += 1;

        id
    }
}

pub fn lower_ast_ty_to_hir_ty(ty: &ast::Ty) -> Ty {
    let ast::Ty { span, kind } = ty;

    match kind {
        ast::TyKind::Regular(sym) => {
            let name = Name::new(*sym, *span);

            Ty {
                kind: TyKind::Regular,
                span: *span,
                name,
            }
        }

        ast::TyKind::MethodSelf => Ty {
            kind: TyKind::MethodSelf,
            span: *span,
            name: Name::new(SymbolId::DUMMY, *span),
        },

        _ => todo!("unsupported yet!"),
    }
}
