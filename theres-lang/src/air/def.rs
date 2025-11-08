use crate::{air::name_res::Namespace, symbols::SymbolId};

crate::newtyped_index!(DefId, DefMap, DefVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);

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

    /// Field of an instance.
    Field,

    /// Bind
    Bind,

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

pub fn name_of<'cx>(cx: &'cx crate::session::Session<'cx>, did: DefId) -> &'cx std::sync::Arc<str> {
    use std::fmt::Write as _;
    let path = cx.air_map().def_path(did);

    // Heuristic: ~8 characters average per segment.
    // Might be dumb!!
    let mut string = String::with_capacity(path.inner().len() << 8);
    for (ix, seg) in path.inner().iter().enumerate() {
        if ix != 0 && ix & 1 != 0 {
            string.push_str("::");
        }

        match seg {
            DefPathSeg::TypeNs(sym) | DefPathSeg::ValueNs(sym) => {
                if *sym == SymbolId::DUMMY {
                    string.push_str("<dummy>");
                    continue;
                }
                string.push_str(sym.get_interned());
            }
            DefPathSeg::Lambda => string.push_str("{lambda}"),
            DefPathSeg::BindBlock => {
                let parent = cx.air_get_parent(did);
                let parent_def = cx.air_get_bind(parent);
                write!(
                    &mut string,
                    "<bind {ty}>",
                    ty = cx.lower_ty(parent_def.with)
                )
                .expect("writing to memory is infallible");
            }
        }
    }

    cx.arena().alloc(string.into())
}

pub fn def_type_of<'cx>(
    cx: &'cx crate::session::Session<'cx>,
    def_id: DefId,
) -> crate::types::ty::Ty<'cx> {
    use crate::air::node::{BindItemKind, Node, ThingKind};
    use crate::types::ty::TyKind;

    match cx.air_get_def(def_id) {
        Node::Thing(thing) => match thing.kind {
            ThingKind::Fn { .. } => cx.intern_ty(TyKind::FnDef(def_id)),
            ThingKind::Instance { .. } => cx.intern_ty(TyKind::Instance(cx.instance_def(def_id))),

            ThingKind::Realm { .. } => panic!("A realm doesn't have a type!"),
            ThingKind::Bind { .. } => panic!("A bind doesn't have a type!"),
        },

        Node::Field(field) => cx.lower_ty(field.ty),

        Node::BindItem(item) => match item.kind {
            BindItemKind::Fun { .. } => cx.intern_ty(TyKind::FnDef(def_id)),
            // BindItemKind::Const { ty, .. } => cx.lower_ty(ty),
        },

        any => panic!("Can't express type for {any:?}"),
    }
}
