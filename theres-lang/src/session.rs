use std::{
    borrow::Borrow,
    cell::RefCell,
    hash::Hash,
    ops::Deref,
    ptr,
    sync::{LazyLock, Mutex},
};

use hashbrown::HashMap;
use hashbrown::hash_map::EntryRef;

use crate::{
    arena::Arena,
    hir::{
        def::{DefId, DefType, IntTy, PrimTy, Resolved},
        lowering_ast::HirMap,
        node::{self, Field, Node, ThingKind},
    },
    id::{IdxSlice, IdxVec},
    lexer::LexError,
    parser::ParseError,
    ty::{FieldDef, Instance, InstanceDef, Ty, TyKind},
};

pub static DIAG_CTXT: LazyLock<Mutex<DiagnosticCtxt>> =
    LazyLock::new(|| Mutex::new(DiagnosticCtxt::new()));

pub struct DiagnosticCtxt {
    lex_errors: Vec<LexError>,
    parse_errors: Vec<ParseError>,
}

impl DiagnosticCtxt {
    pub fn new() -> Self {
        Self {
            lex_errors: Vec::new(),
            parse_errors: Vec::new(),
        }
    }
    pub fn push_lex_error(&mut self, err: LexError) {
        self.lex_errors.push(err);
    }

    pub fn push_parse_error(&mut self, err: ParseError) {
        self.parse_errors.push(err);
    }

    pub fn errored(&self) -> bool {
        !(self.parse_errors.is_empty() || self.lex_errors.is_empty())
    }

    pub fn parse_errors(&self) -> &[ParseError] {
        &self.parse_errors
    }

    pub fn lex_errors(&self) -> &[LexError] {
        &self.lex_errors
    }
}

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
        println!("interning: {:#?}", str);
        if let Some(present) = self.map.get(str) {
            return *present;
        }

        #[allow(clippy::ref_as_ptr)]
        let new_str: &'static str = unsafe { &*(self.arena.alloc_string(str) as *const str) };

        println!("interned: {new_str:#?}");

        let id = self.storage.future_id();

        self.map.insert(new_str, id);
        self.storage.push(new_str);

        dbg!(&self.storage);

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
pub struct Pooled<'a, T>(&'a T);

impl<T> Copy for Pooled<'_, T> {}

impl<T> Clone for Pooled<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<T: Sync> Sync for Pooled<'_, T> {}
unsafe impl<T: Send> Send for Pooled<'_, T> {}

impl<'a, T> Deref for Pooled<'a, T> {
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

// pub struct Pool<'a, T> {
//     map: HashMap<Pooled<'a, T>, ()>,
// }

// impl<T> Borrow<T> for Pooled<'_, T> {
//     fn borrow(&self) -> &T {
//         self.0
//     }
// }

// impl<'a, T: Hash + Eq> Pool<'a, T> {
//     #[allow(clippy::new_without_default)]
//     pub fn new() -> Self {
//         Self {
//             map: HashMap::new(),
//         }
//     }

//     pub fn intern<F>(&mut self, item: T, mk: F) -> Pooled<'a, T>
//     where
//         F: FnOnce(T) -> Pooled<'a, T>,
//     {
//         match self.map.entry_ref(&item) {
//             EntryRef::Vacant(_vacant) => {
//                 let interned = mk(item);
//                 self.map.insert(interned, ());

//                 interned
//             }

//             EntryRef::Occupied(occup) => Pooled(occup.key().0),
//         }
//     }
// }

type Pool<'a, T> = std::collections::HashMap<T, Pooled<'a, T>>;

pub struct Session<'sess> {
    arena: Arena,

    hir_map: RefCell<HirMap<'sess>>,

    types: RefCell<Pool<'sess, TyKind<'sess>>>,
    instances: RefCell<Pool<'sess, InstanceDef<'sess>>>,
}

impl<'sess> Session<'sess> {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            hir_map: RefCell::new(HirMap::new()),
            types: RefCell::new(Pool::new()),
            instances: RefCell::new(Pool::new()),
        }
    }

    pub fn enter<F, R>(&'sess self, work: F) -> R
    where
        F: FnOnce(&'sess Self) -> R,
    {
        work(self)
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

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    // pub fn intern_ty(&'sess self, ty: TyKind<'sess>) -> Ty<'sess> {
    //     self.types
    //         .borrow_mut()
    //         .intern(ty, |item| Pooled(self.arena().alloc(item)))
    // }

    // pub fn intern_instance_def(&'sess self, def: InstanceDef<'sess>) -> Instance<'sess> {
    //     self.instances
    //         .borrow_mut()
    //         .intern(def, |item| Pooled(self.arena().alloc(item)))
    // }

    pub fn intern_ty(&'sess self, ty: TyKind<'sess>) -> Ty<'sess> {
        match self.types.borrow_mut().get(&ty) {
            Some(r) => *r,
            None => Pooled(self.arena().alloc(ty)),
        }
    }

    pub fn intern_instance_def(&'sess self, def: InstanceDef<'sess>) -> Instance<'sess> {
        match self.instances.borrow_mut().get(&def) {
            Some(r) => *r,
            None => Pooled(self.arena().alloc(def)),
        }
    }

    pub fn def_type_of(&'sess self, def_id: DefId) -> Ty<'sess> {
        self.hir(|map| match map.get_def(def_id) {
            Node::Thing(thing) => match thing.kind {
                ThingKind::Fn { .. } => self.intern_ty(TyKind::FnDef(def_id)),
                ThingKind::Instance { fields, name } => self.intern_ty(TyKind::Instance(
                    self.intern_instance_def(self.gen_instance_def(fields, name.interned)),
                )),

                ThingKind::Global { ty, .. } => {
                    self.lower_ty(ty, || unreachable!("`Self` in global item"))
                }

                ThingKind::Realm { .. } => panic!("A realm doesn't have a type!"),
                ThingKind::Bind { .. } => panic!("A bind doesn't have a type!"),
            },

            Node::Field(field) => self.hir(|map| {
                self.lower_ty(field.ty, || {
                    let instance_id = map.get_instance_of_field(field.def_id);
                    self.def_type_of(instance_id)
                })
            }),

            any => panic!("Can't express type for {any:?}"),
        })
    }

    pub fn lower_ty<F>(&'sess self, ty: &node::Ty<'_>, method_self: F) -> Ty<'sess>
    where
        F: FnOnce() -> Ty<'sess>,
    {
        let tykind = match ty.kind {
            node::TyKind::MethodSelf => return method_self(),
            node::TyKind::Array(array_ty) => TyKind::Array(self.lower_ty(array_ty, method_self)),
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

        bool -> TyKind::Bool
    );
}
