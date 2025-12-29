use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::ptr::{from_ref, null};
use std::sync::Arc;

use crate::eair::{Eair, build_eair};
use crate::pill::body::{Pill, build_pill};
use crate::typing::fun_cx::FieldSlice;
use crate::typing::fun_cx::{TypeTable, typeck};
use crate::typing::ty::{FnSig, Instance, InstanceDef, ParamTy, Ty, TyKind, instance_def};
use lychee_air::lowering_ast::{AirId, AirMap};
use lychee_air::node::{self, Node};
use lychee_ast::Name;
use lychee_util::arena::Arena;
use lychee_util::def::{BodyId, DefId, DefType, IntTy, PrimTy, Resolved};
use lychee_util::errors::DiagEmitter;
use lychee_util::flags::Flags;
use lychee_util::pooled::Pool;
use lychee_util::sources::{SourceId, Sources};
use lychee_util::symbols::SymbolId;

thread_local! {
    pub static GLOBAL_CTXT: Cell<*const ()> = const {
        Cell::new(null())
    }
}

#[track_caller]
pub fn cx<'cx, F, R>(f: F) -> R
where
    F: FnOnce(&'cx Session<'cx>) -> R,
{
    let ptr = GLOBAL_CTXT.get();
    assert!(!ptr.is_null());
    f(unsafe { &*(ptr.cast()) })
}

#[allow(dead_code)]
pub struct Types<'ty> {
    pub nil: Ty<'ty>,
    pub bool: Ty<'ty>,

    pub u8: Ty<'ty>,
    pub u16: Ty<'ty>,
    pub u32: Ty<'ty>,
    pub u64: Ty<'ty>,

    pub i8: Ty<'ty>,
    pub i16: Ty<'ty>,
    pub i32: Ty<'ty>,
    pub i64: Ty<'ty>,

    pub f32: Ty<'ty>,
    pub f64: Ty<'ty>,

    pub err: Ty<'ty>,
    pub diverges: Ty<'ty>,
}

lychee_util::cache! {
    [lock: std::cell::RefCell]

    #[doc = "Returns the name of a definition specified by the `did` parameter."]
    pub fn name_of(&'cx! self, did: DefId) -> &'cx Arc<str> {
        name_of
    }

    #[doc = "Type-checks the given definition specified by `did`"]
    pub fn typeck(&'cx! self, did: DefId) -> &'cx TypeTable<'cx> {
        typeck
    }

    #[doc = "Creates and interns `Instance` for given `DefId` of an instance"]
    pub fn instance_def(&'cx! self, did: DefId) -> Instance<'cx> {
        instance_def
    }

    #[doc = "Expresses a type for the given definition at `DefId`"]
    pub fn def_type_of(&'cx! self, did: DefId) -> Ty<'cx> {
        def_type_of
    }

    #[doc = "Expresses a function signature for the given definition at `DefId`"]
    pub fn fn_sig_for(&'cx! self, did: DefId) -> FnSig<'cx> {
        crate::typing::ty::fn_sig_for
    }

    #[doc = "Builds an EAIR body for the specified `DefId`"]
    pub fn build_eair(&'cx! self, did: DefId) -> &'cx Eair<'cx> {
        build_eair
    }

    /// Builds a PILL body for the specified `DefId`
    pub fn build_pill(&'cx! self, did: DefId) -> &'cx Pill<'cx> {
        build_pill
    }

    /// Gathers the fields of a lambda's environment
    pub fn lambda_env_fields(&'cx! self, did: DefId) -> &'cx FieldSlice<(Ty<'cx>, AirId)> {
        crate::typing::ty::lambda_env_fields
    }

    /// Gathers `bind`s for a type.
    pub fn binds_for_type(&'cx! self, ty: Ty<'cx>) -> &'cx [node::BindItem<'cx>] {
        crate::typing::fun_cx::binds_for_type
    }
}

pub struct Session<'sess> {
    arena: &'sess Arena,
    sources: &'sess Sources,
    air_map: AirMap<'sess>,

    pub(crate) interned_types: RefCell<Pool<'sess, TyKind<'sess>>>,
    instances: RefCell<Pool<'sess, InstanceDef<'sess>>>,

    diags: &'sess DiagEmitter<'sess>,
    flags: Flags,

    pub types: Types<'sess>,
    cache: Cache<'sess>,
}

impl<'cx> Session<'cx> {
    pub fn new(
        diags: &'cx DiagEmitter<'cx>,
        flags: Flags,
        sources: &'cx Sources,
        arena: &'cx Arena,
        air_map: AirMap<'cx>,
    ) -> Self {
        let mut pool = Pool::new();

        let types = Types {
            nil: Ty(pool.pool(TyKind::Nil, arena)),
            bool: Ty(pool.pool(TyKind::Bool, arena)),
            u8: Ty(pool.pool(TyKind::Uint(IntTy::N8), arena)),
            u16: Ty(pool.pool(TyKind::Uint(IntTy::N16), arena)),
            u32: Ty(pool.pool(TyKind::Uint(IntTy::N32), arena)),
            u64: Ty(pool.pool(TyKind::Uint(IntTy::N64), arena)),
            i8: Ty(pool.pool(TyKind::Int(IntTy::N8), arena)),
            i16: Ty(pool.pool(TyKind::Int(IntTy::N16), arena)),
            i32: Ty(pool.pool(TyKind::Int(IntTy::N32), arena)),
            i64: Ty(pool.pool(TyKind::Int(IntTy::N64), arena)),
            f32: Ty(pool.pool(TyKind::Float, arena)),
            f64: Ty(pool.pool(TyKind::Double, arena)),
            err: Ty(pool.pool(TyKind::Error, arena)),
            diverges: Ty(pool.pool(TyKind::Diverges, arena)),
        };

        Self {
            arena,
            air_map,
            interned_types: RefCell::new(pool),
            instances: RefCell::new(Pool::new()),
            diags,
            flags,
            sources,
            types,
            cache: Cache::new(),
        }
    }

    pub fn enter<F>(&'cx self, work: F)
    where
        F: FnOnce(&'cx Self),
    {
        GLOBAL_CTXT.with(|cell| {
            cell.set(from_ref(self).cast());
            work(self);
            cell.set(null());
        });
    }

    pub fn air_map(&self) -> &AirMap<'_> {
        &self.air_map
    }

    pub fn flags(&self) -> &Flags {
        &self.flags
    }

    pub fn file_name(&self, id: SourceId) -> &str {
        self.sources.get_by_source_id(id).name()
    }

    pub fn diag(&self) -> &'cx DiagEmitter<'_> {
        self.diags
    }

    pub fn arena(&self) -> &Arena {
        self.arena
    }

    pub fn intern_instance_def(&'cx self, def: InstanceDef<'cx>) -> Instance<'cx> {
        self.instances.borrow_mut().pool(def, self.arena())
    }

    pub fn def_type(&self, did: DefId) -> DefType {
        self.air_map.def_type(did)
    }

    pub fn air_get_def(&self, did: DefId) -> &Node<'_> {
        self.air_map.get_def(did)
    }

    pub fn air_get_instance_of_ctor(&'cx self, did: DefId) -> DefId {
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

    pub fn air_get_bind(&self, did: DefId) -> &node::Bind<'_> {
        self.air_map.expect_bind(did)
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

    pub fn upvars_of(&'cx self, did: DefId) -> &'cx HashSet<AirId> {
        crate::passes::upvar_analysis::analyze_upvars(self, did)
    }

    pub fn is_native_fn(&'cx self, did: DefId) -> bool {
        self.def_type(did) == DefType::NativeFn
    }

    pub fn lower_ty<'a>(&'cx self, ty: &node::Ty<'a>) -> Ty<'cx>
    where
        'cx: 'a,
    {
        let tykind = match ty.kind {
            node::TyKind::Fun { inputs, output } => TyKind::Param {
                span: ty.span,
                kind: ParamTy::Fun {
                    inputs: self
                        .arena
                        .alloc_from_iter(inputs.iter().map(|this| self.lower_ty(this))),
                    output: output.map_or(self.types.nil, |this| self.lower_ty(this)),
                },
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

                Resolved::Err => return self.types.err,
                Resolved::Local(..) | Resolved::Label { .. } => {
                    unreachable!()
                }
            },
        };

        self.intern_ty(tykind)
    }
}

pub fn name_of<'cx>(cx: &'cx crate::session::Session<'cx>, did: DefId) -> &'cx std::sync::Arc<str> {
    use lychee_util::def::DefPathSeg;
    use std::fmt::Write as _;

    if cx.is_native_fn(did) {
        let lychee_air::node::Node::NativeItem(fun) = cx.air_get_def(did) else {
            unreachable!()
        };

        return cx
            .arena()
            .alloc(fun.name.interned.get_interned().to_string().into());
    }

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
                    string.truncate(string.len() - 2);
                    continue;
                }
                string.push_str(sym.get_interned());
            }
            DefPathSeg::Lambda => {
                let parent = cx.air_get_parent(did);
                let span = cx.air_get_lambda(did).span;
                string.push_str(cx.name_of(parent));
                write!(&mut string, "::{{lambda@{span}}}").unwrap();
            }
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

pub fn def_type_of<'cx>(cx: &'cx Session<'cx>, def_id: DefId) -> Ty<'cx> {
    use crate::typing::ty::TyKind;
    use lychee_air::node::{BindItemKind, Node, ThingKind};

    match cx.air_get_def(def_id) {
        Node::Thing(thing) => match thing.kind {
            ThingKind::Fn { .. } => cx.intern_ty(TyKind::FnDef(def_id)),
            ThingKind::Instance { .. } => cx.intern_ty(TyKind::Instance(cx.instance_def(def_id))),

            ThingKind::Realm { .. } => panic!("A realm doesn't have a type!"),
            ThingKind::Bind { .. } => panic!("A bind doesn't have a type!"),
            ThingKind::Native { .. } => panic!("A native block doesn't have a type!"),
        },

        Node::Field(field) => cx.lower_ty(field.ty),

        Node::BindItem(item) => match item.kind {
            BindItemKind::Fun { .. } => cx.intern_ty(TyKind::FnDef(def_id)),
            // BindItemKind::Const { ty, .. } => cx.lower_ty(ty),
        },

        any => panic!("Can't express type for {any:?}"),
    }
}
