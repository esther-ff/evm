use std::borrow::Cow;
use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::ops::Deref;
use std::ptr;
use std::sync::{LazyLock, Mutex};

use crate::arena::Arena;
use crate::driver::{Flags, HirDump};
use crate::errors::DiagEmitter;
use crate::hir::def::{DefId, DefType, IntTy, PrimTy, Resolved};
use crate::hir::lowering_ast::HirMap;
use crate::hir::node::{self, BindItemKind, Field, Node, ThingKind};
use crate::id::{IdxSlice, IdxVec};
use crate::ty::{FieldDef, FnSig, InferKind, Instance, InstanceDef, Ty, TyKind};

pub static SYMBOL_INTERNER: LazyLock<Mutex<GlobalInterner>> =
    LazyLock::new(|| Mutex::new(GlobalInterner::new()));

pub struct GlobalInterner {
    arena: Arena,
    map: HashMap<&'static str, SymbolId>,
    storage: SymbolVec<&'static str>,
}

impl GlobalInterner {
    pub fn new() -> Self {
        let map: HashMap<_, _> = SymbolId::BASE_SYMBOLS
            .into_iter()
            .enumerate()
            .map(|(k, v)| (v, SymbolId::new_usize(k)))
            .collect();

        Self {
            map,
            storage: IdxVec::new_from_vec(SymbolId::BASE_SYMBOLS.to_vec()),
            arena: Arena::new(),
        }
    }

    pub fn pre_interned(&mut self) {
        for sym in SymbolId::BASE_SYMBOLS {
            self.intern(sym);
        }
    }

    pub fn intern(&mut self, str: &str) -> SymbolId {
        if let Some(present) = self.map.get(str) {
            return *present;
        }

        #[allow(clippy::ref_as_ptr)]
        let new_str: &'static str = unsafe { &*(self.arena.alloc_string(str) as *const str) };

        let id = self.storage.future_id();

        self.map.insert(new_str, id);
        self.storage.push(new_str);

        id
    }
}

crate::newtyped_index!(SymbolId, SymbolMap, SymbolVec);

macro_rules! interned_consts {
    ($($name:ident -> $id:expr ),*) => {
        $(
            pub const fn $name() -> SymbolId {
                SymbolId { private: $id }
            }
        )*
    };
}

impl SymbolId {
    const BASE_SYMBOLS: [&str; 12] = [
        "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "nil", "bool",
    ];

    // keep in touch with `BASE_SYMBOLS`
    interned_consts!(
        u8  -> 0,
        u16 -> 1,
        u32 -> 2,
        u64 -> 3,
        i8  -> 4,
        i16 -> 5,
        i32 -> 6,
        i64 -> 7,
        f32 -> 8,
        f64 -> 9,
        nil -> 10,
        bool -> 11
    );

    pub fn get_interned(&self) -> &str {
        let interner = SYMBOL_INTERNER.lock().unwrap();
        interner.storage[self.private as usize]
    }

    pub fn intern(sym: &str) -> Self {
        SYMBOL_INTERNER.lock().unwrap().intern(sym)
    }
}

#[derive(Debug, PartialOrd, Eq, Ord, Hash)]
pub struct Pooled<'a, T>(pub &'a T);

impl<T> Copy for Pooled<'_, T> {}

impl<T> Clone for Pooled<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<T: Sync> Sync for Pooled<'_, T> {}
unsafe impl<T: Send> Send for Pooled<'_, T> {}

impl<T> Deref for Pooled<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T> PartialEq for Pooled<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

type Pool<'a, T> = HashMap<T, Pooled<'a, T>>;

pub struct Session<'sess> {
    arena: Arena,

    hir_map: RefCell<HirMap<'sess>>,

    types: RefCell<Pool<'sess, TyKind<'sess>>>,
    instances: RefCell<Pool<'sess, InstanceDef<'sess>>>,

    def_id_to_instance_interned: RefCell<HashMap<DefId, Instance<'sess>>>,

    fn_sigs: RefCell<HashMap<DefId, FnSig<'sess>>>,

    diags: &'sess DiagEmitter<'sess>,

    flags: Flags,
}

impl<'sess> Session<'sess> {
    pub fn new(diags: &'sess DiagEmitter<'sess>, flags: Flags) -> Self {
        Self {
            arena: Arena::new(),
            def_id_to_instance_interned: RefCell::new(HashMap::new()),
            hir_map: RefCell::new(HirMap::new()),
            types: RefCell::new(Pool::new()),
            instances: RefCell::new(Pool::new()),
            fn_sigs: RefCell::new(HashMap::new()),
            diags,
            flags,
        }
    }

    pub fn dump_hir_mode(&self) -> HirDump {
        self.flags.dump_hir
    }

    pub fn should_dump_ast(&self) -> bool {
        self.flags.dump_ast
    }

    pub fn enter<F, R>(&'sess self, work: F) -> R
    where
        F: FnOnce(&'sess Self) -> R,
    {
        work(self)
    }

    pub fn diag(&self) -> &'sess DiagEmitter<'_> {
        self.diags
    }

    pub fn hir_mut<F, R>(&'sess self, f: F) -> R
    where
        F: FnOnce(&mut HirMap<'sess>) -> R,
    {
        f(&mut self.hir_map.borrow_mut())
    }

    pub fn hir<F, R>(&'sess self, f: F) -> R
    where
        F: FnOnce(&HirMap<'sess>) -> R,
    {
        f(&self.hir_map.borrow())
    }

    pub fn hir_ref(&self) -> Ref<'_, HirMap<'sess>> {
        self.hir_map.borrow()
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn intern_ty(&'sess self, ty: TyKind<'sess>) -> Ty<'sess> {
        let mut tys = self.types.borrow_mut();
        if let Some(pooled) = tys.get(&ty).copied() {
            return pooled;
        }

        let new = Pooled(self.arena().alloc(ty));
        tys.insert(ty, new);
        new
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

    pub fn def_type_of(&'sess self, def_id: DefId) -> Ty<'sess> {
        self.hir(|map| match map.get_def(def_id) {
            Node::Thing(thing) => match thing.kind {
                ThingKind::Fn { .. } => self.intern_ty(TyKind::FnDef(def_id)),
                ThingKind::Instance { fields, name } => self.intern_ty(TyKind::Instance(
                    self.intern_instance_def(self.gen_instance_def(fields, name.interned)),
                )),

                ThingKind::Global { ty, .. } => self.lower_ty(ty),

                ThingKind::Realm { .. } => panic!("A realm doesn't have a type!"),
                ThingKind::Bind { .. } => panic!("A bind doesn't have a type!"),
            },

            Node::Field(field) => self.lower_ty(field.ty),

            Node::BindItem(item) => match item.kind {
                BindItemKind::Fun { .. } => self.intern_ty(TyKind::FnDef(def_id)),
                BindItemKind::Const { ty, .. } => self.lower_ty(ty),
            },

            any => panic!("Can't express type for {any:?}"),
        })
    }

    pub fn fn_sig_for(&'sess self, def_id: DefId) -> FnSig<'sess> {
        self.fn_sigs
            .borrow()
            .get(&def_id)
            .copied()
            .unwrap_or_else(|| panic!("No fn sig for def id: {def_id}"))
    }

    pub fn lower_fn_sig(&'sess self, sig: node::FnSig<'_>, def_id: DefId) {
        let sig = FnSig {
            inputs: self
                .arena()
                .alloc_from_iter(sig.arguments.iter().map(|param| self.lower_ty(param.ty))),

            output: self.lower_ty(sig.return_type),
        };

        self.fn_sigs.borrow_mut().insert(def_id, sig);
    }

    pub fn binds_for_ty<F, R>(&'sess self, ty: Ty<'sess>, work: F) -> R
    where
        F: FnOnce(Vec<node::Bind<'_>>) -> R,
    {
        let hir = self.hir_ref();
        work(
            hir.nodes()
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

        let hir = self.hir_ref();
        let (fields, name) = hir.expect_instance(def_id);

        let instance_def = InstanceDef {
            fields: IdxSlice::new(self.arena().alloc_from_iter(fields.iter().map(|field| {
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
            node::TyKind::MethodSelf => todo!("get rid of this"),
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
                    any => panic!("Can't type: {any:?}"),
                },

                Resolved::Err => panic!("Tried to resolve a `Resolved::Err`"),
                Resolved::Local(..) => {
                    panic!("Tried to lower type with a local inside of it's path")
                }
            },
        };

        self.intern_ty(tykind)
    }

    pub fn stringify_ty(&'sess self, ty: Ty<'sess>) -> Cow<'static, str> {
        let mut buf = String::new();

        match ty.0 {
            TyKind::Bool => Cow::Borrowed("bool"),
            TyKind::Uint(size) => match size {
                IntTy::N8 => Cow::Borrowed("u8"),
                IntTy::N16 => Cow::Borrowed("u16"),
                IntTy::N32 => Cow::Borrowed("u32"),
                IntTy::N64 => Cow::Borrowed("u64"),
            },
            TyKind::Int(size) => match size {
                IntTy::N8 => Cow::Borrowed("i8"),
                IntTy::N16 => Cow::Borrowed("i16"),
                IntTy::N32 => Cow::Borrowed("i32"),
                IntTy::N64 => Cow::Borrowed("i64"),
            },
            TyKind::Float => Cow::Borrowed("f32"),
            TyKind::Double => Cow::Borrowed("f64"),
            TyKind::Nil => Cow::Borrowed("Nil"),
            TyKind::Error => Cow::Borrowed("error!"),

            TyKind::Diverges => Cow::Borrowed("Diverges"),

            any => {
                self.stringfy_string_helper(&mut buf, *any);
                Cow::Owned(buf)
            }
        }
    }

    fn stringfy_string_helper(&'sess self, buf: &mut String, ty: TyKind<'sess>) {
        let push = match ty {
            TyKind::Bool => "bool",
            TyKind::Uint(size) => match size {
                IntTy::N8 => "u8",
                IntTy::N16 => "u16",
                IntTy::N32 => "u32",
                IntTy::N64 => "u64",
            },
            TyKind::Int(size) => match size {
                IntTy::N8 => "i8",
                IntTy::N16 => "i16",
                IntTy::N32 => "i32",
                IntTy::N64 => "i64",
            },
            TyKind::Float => "f32",
            TyKind::Double => "f64",
            TyKind::Nil => "Nil",

            TyKind::Diverges => "Diverges",

            TyKind::Array(ty) => {
                buf.push('[');
                self.stringfy_string_helper(buf, *ty);
                buf.push(']');
                return;
            }

            TyKind::Fn { inputs, output } => {
                buf.push_str("fun(");
                for (ix, i) in inputs.iter().enumerate() {
                    self.stringfy_string_helper(buf, **i);

                    if ix != inputs.len() {
                        buf.push_str(", ");
                    }
                }
                buf.push(')');
                buf.push_str("=> ");
                self.stringfy_string_helper(buf, *output);

                return;
            }

            TyKind::Instance(def) => {
                buf.push_str(def.name.get_interned());
                return;
            }

            TyKind::FnDef(def_id) => {
                let hir = self.hir_ref();
                let (sig, name) = hir.expect_fn(def_id);
                let _ = write!(buf, "fun {}(", name.interned.get_interned());

                for (ix, param) in sig.arguments.iter().enumerate() {
                    // i'll handle this later ok!
                    let ty = self.lower_ty(param.ty);
                    self.stringfy_string_helper(buf, *ty);

                    if ix != sig.arguments.len() {
                        buf.push_str(", ");
                    }
                }

                buf.push(')');
                buf.push_str("=> ");
                self.stringfy_string_helper(buf, *self.lower_ty(sig.return_type));

                return;
            }

            TyKind::Error => "error",

            TyKind::InferTy(infer) => {
                return match infer.kind {
                    InferKind::Float => write!(buf, "{{float: {}?}}", infer.vid.to_usize()),
                    InferKind::Integer => {
                        write!(buf, "{{integer: {}?}}", infer.vid.to_usize())
                    }
                    InferKind::Regular => write!(buf, "{}?", infer.vid.to_usize()),
                }
                .expect("writing to a `String` never fails");
            }
        };

        buf.push_str(push);
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
