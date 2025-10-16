use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::ptr::{from_ref, null};

use crate::air::def::{BodyId, DefId, DefType, IntTy, PrimTy, Resolved};
use crate::air::node::{self, BindItemKind, Field, Node, ThingKind};
use crate::air::{AirId, AirMap};
use crate::arena::Arena;
use crate::ast::Name;
use crate::driver::Flags;
use crate::errors::DiagEmitter;
use crate::id::IdxSlice;
use crate::pooled::{Pool, Pooled};
use crate::sources::{SourceId, Sources};
use crate::symbols::SymbolId;
use crate::types::ty::{FieldDef, FnSig, Instance, InstanceDef, Ty, TyKind};

thread_local! {
    pub static GLOBAL_CTXT: Cell<*const ()> = const {
        Cell::new(null())
    }
}

pub fn cx<'cx, F, R>(f: F) -> R
where
    F: FnOnce(&'cx Session<'cx>) -> R,
{
    let ptr = GLOBAL_CTXT.get();
    assert!(!ptr.is_null());
    f(unsafe { &*(ptr.cast()) })
}

pub struct Session<'sess> {
    arena: &'sess Arena,
    air_map: AirMap<'sess>,
    pub(crate) types: RefCell<Pool<'sess, TyKind<'sess>>>,
    instances: RefCell<Pool<'sess, InstanceDef<'sess>>>,
    def_id_to_instance_interned: RefCell<HashMap<DefId, Instance<'sess>>>,

    diags: &'sess DiagEmitter<'sess>,
    flags: Flags,
    sources: &'sess Sources,
}

impl<'sess> Session<'sess> {
    pub fn new(
        diags: &'sess DiagEmitter<'sess>,
        flags: Flags,
        sources: &'sess Sources,
        arena: &'sess Arena,
        air_map: AirMap<'sess>,
    ) -> Self {
        Self {
            arena,
            def_id_to_instance_interned: RefCell::new(HashMap::new()),
            air_map,
            types: RefCell::new(Pool::new()),
            instances: RefCell::new(Pool::new()),
            diags,
            flags,
            sources,
        }
    }

    pub fn enter<F>(&'sess self, work: F)
    where
        F: FnOnce(&'sess Self),
    {
        GLOBAL_CTXT.with(|cell| {
            cell.set(from_ref(self).cast());
            work(self);
            cell.set(null());
        });
    }

    pub fn dump_air_mode(&self) -> crate::driver::HirDump {
        self.flags.dump_hir
    }

    pub fn should_dump_ast(&self) -> bool {
        self.flags.dump_ast
    }

    pub fn file_name(&self, id: SourceId) -> &str {
        self.sources.get_by_source_id(id).name()
    }

    pub fn diag(&self) -> &'sess DiagEmitter<'_> {
        self.diags
    }

    pub fn arena(&self) -> &Arena {
        self.arena
    }

    pub fn intern_instance_def(&'sess self, def: InstanceDef<'sess>) -> Instance<'sess> {
        let mut instances = self.instances.borrow_mut();
        if let Some(pooled) = instances.get(&def).copied() {
            return pooled;
        }

        let new = Pooled(self.arena().alloc(def));
        instances.insert(def, new);
        new
    }

    pub fn def_type(&self, did: DefId) -> DefType {
        self.air_map.def_type(did)
    }

    pub fn air_get_def(&self, did: DefId) -> &Node<'_> {
        self.air_map.get_def(did)
    }

    pub fn air_get_instance_of_ctor(&'sess self, did: DefId) -> DefId {
        self.air_map.get_instance_of_ctor(did)
    }

    pub fn air_get_fn(&self, did: DefId) -> (&node::FnSig<'_>, SymbolId) {
        self.air_map.expect_fn(did)
    }

    pub fn air_get_instance(&self, did: DefId) -> (&[node::Field<'_>], Name) {
        self.air_map.expect_instance(did)
    }

    pub fn air_get_lambda(&self, did: DefId) -> &node::Lambda<'_> {
        self.air_map.expect_lambda(did)
    }

    pub fn air_body(&self, did: DefId) -> &node::Expr<'_> {
        self.air_map.body_of(did)
    }

    pub fn air_body_via_id(&self, bid: BodyId) -> &node::Expr<'_> {
        self.air_map.get_body(bid)
    }

    pub fn air_get_parent(&self, did: DefId) -> DefId {
        self.air_map.parent(did)
    }

    pub fn upvars_of(&'sess self, did: DefId) -> &'sess HashSet<AirId> {
        crate::air::passes::upvar_analysis::analyze_upvars(self, did)
    }

    pub fn def_type_of(&'sess self, def_id: DefId) -> Ty<'sess> {
        log::trace!("def_type_of def_id={def_id}");
        match self.air_get_def(def_id) {
            Node::Thing(thing) => match thing.kind {
                ThingKind::Fn { .. } => self.intern_ty(TyKind::FnDef(def_id)),
                ThingKind::Instance {
                    fields,
                    name,
                    ctor_id: _,
                } => self.intern_ty(TyKind::Instance(
                    self.intern_instance_def(self.gen_instance_def(fields, name.interned)),
                )),

                ThingKind::Realm { .. } => panic!("A realm doesn't have a type!"),
                ThingKind::Bind { .. } => panic!("A bind doesn't have a type!"),
            },

            Node::Field(field) => self.lower_ty(field.ty),

            Node::BindItem(item) => match item.kind {
                BindItemKind::Fun { .. } => self.intern_ty(TyKind::FnDef(def_id)),
                // BindItemKind::Const { ty, .. } => self.lower_ty(ty),
            },

            any => panic!("Can't express type for {any:?}"),
        }
    }

    pub fn fn_sig_for(&'sess self, def_id: DefId) -> FnSig<'sess> {
        match self.def_type(def_id) {
            DefType::Fun => {
                let (sig, _) = self.air_get_fn(def_id);

                FnSig {
                    inputs: self
                        .arena()
                        .alloc_from_iter(sig.arguments.iter().map(|param| self.lower_ty(param.ty))),

                    output: self.lower_ty(sig.return_type),
                }
            }

            DefType::AdtCtor => {
                let instance = self.air_get_instance_of_ctor(def_id);
                let instance_def = self.instance_def(instance);

                FnSig {
                    inputs: self.arena().alloc_from_iter(
                        instance_def
                            .fields
                            .iter()
                            .map(|field| self.def_type_of(field.def_id)),
                    ),

                    output: self.def_type_of(instance),
                }
            }

            any => panic!("can't express a signature for {any:#?}"),
        }
    }

    pub fn is_ctor_fn(&self, def_id: DefId) -> bool {
        self.air_map.is_ctor(def_id)
    }

    /// This is so fucking stupid
    pub fn binds_for_ty<F, R>(&'sess self, ty: Ty<'sess>, work: F) -> R
    where
        F: FnOnce(Vec<node::Bind<'_>>) -> R,
    {
        work(
            self.air_map
                .nodes()
                .into_iter()
                .filter_map(node::Node::get_thing)
                .filter_map(node::Thing::get_bind)
                .filter(|b| self.lower_ty(b.with) == ty)
                .collect(),
        )
    }

    pub fn instance_def(&'sess self, def_id: DefId) -> Instance<'sess> {
        if let Some(v) = self.def_id_to_instance_interned.borrow().get(&def_id) {
            return *v;
        }

        let (fields, name) = self.air_get_instance(def_id);

        let instance_def = InstanceDef {
            fields: IdxSlice::new(self.arena.alloc_from_iter(fields.iter().map(|field| {
                FieldDef {
                    def_id: field.def_id,
                    name: field.name.interned,
                    mutable: field.mutability,
                }
            }))),
            name: name.interned,
        };

        let mut instances = self.instances.borrow_mut();
        if let Some(pooled) = instances.get(&instance_def).copied() {
            return pooled;
        }

        let new = Pooled(self.arena().alloc(instance_def));
        instances.insert(instance_def, new);
        new
    }

    pub fn lower_ty<'a>(&'sess self, ty: &node::Ty<'a>) -> Ty<'sess>
    where
        'sess: 'a,
    {
        let tykind = match ty.kind {
            node::TyKind::Fun { inputs, output } => TyKind::Fn {
                inputs: self
                    .arena
                    .alloc_from_iter(inputs.iter().map(|this| self.lower_ty(this))),
                output: output.map_or_else(|| self.nil(), |this| self.lower_ty(this)),
            },
            node::TyKind::Infer => panic!("lowered an Infer ty"),
            node::TyKind::Err => TyKind::Error,
            node::TyKind::Array(array_ty) => TyKind::Array(self.lower_ty(array_ty)),
            node::TyKind::Path(path) => match path.res {
                Resolved::Prim(prim) => match prim {
                    PrimTy::Uint(size) => TyKind::Uint(size),
                    PrimTy::Int(size) => TyKind::Int(size),
                    PrimTy::Double => TyKind::Double,
                    PrimTy::Float => TyKind::Float,
                    PrimTy::Nil => TyKind::Nil,
                    PrimTy::Bool => TyKind::Bool,
                },

                Resolved::Def(def_id, def_ty) => match def_ty {
                    DefType::Instance => return self.def_type_of(def_id),
                    DefType::AdtCtor => TyKind::FnDef(def_id),

                    _ => unreachable!(),
                },

                Resolved::Err => return self.ty_err(),
                Resolved::Local(..) => {
                    unreachable!()
                }
            },
        };

        self.intern_ty(tykind)
    }

    fn gen_instance_def(&'sess self, fields: &[Field<'_>], name: SymbolId) -> InstanceDef<'sess> {
        InstanceDef {
            fields: IdxSlice::new(self.arena().alloc_from_iter(fields.iter().map(|field| {
                FieldDef {
                    def_id: field.def_id,
                    name: field.name.interned,
                    mutable: field.mutability,
                }
            }))),
            name,
        }
    }
}

macro_rules! type_fns {
    ($($name:ident -> $kind:expr),*) => {
        $(
            pub fn $name(&'ty self) -> Ty<'ty> {
                self.intern_ty($kind)
            }
        )*
    };
}

impl<'ty> Session<'ty> {
    type_fns!(
        u8 -> TyKind::Uint(IntTy::N8),
        u16 -> TyKind::Uint(IntTy::N16),
        u32 -> TyKind::Uint(IntTy::N32),
        u64 -> TyKind::Uint(IntTy::N64),
        i8 -> TyKind::Int(IntTy::N8),
        i16 -> TyKind::Int(IntTy::N16),
        i32 -> TyKind::Int(IntTy::N32),
        i64 -> TyKind::Int(IntTy::N64),
        f32 -> TyKind::Float,
        f64 -> TyKind::Double,
        nil -> TyKind::Nil,
        ty_err -> TyKind::Error,
        ty_diverge -> TyKind::Diverges,

        bool -> TyKind::Bool
    );
}
