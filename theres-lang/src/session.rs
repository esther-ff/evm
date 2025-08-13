use std::{
    cell::RefCell,
    collections::HashMap,
    ptr,
    sync::{LazyLock, Mutex},
};

use crate::{
    arena::Arena,
    hir::{
        def::{DefId, Definitions},
        lowering_ast::{HirId, HirMap},
    },
    id::IdxVec,
    lexer::LexError,
    parser::ParseError,
    ty::{Instance, InstanceDef, Ty, TyKind},
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

impl<T> PartialEq for Pooled<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

pub struct Session<'sess> {
    dropless_arena: Arena,

    hir_map: RefCell<HirMap<'sess>>,

    types: RefCell<HashMap<TyKind<'sess>, Ty<'sess>>>,
    instances: RefCell<HashMap<InstanceDef<'sess>, Instance<'sess>>>,
}

impl<'sess> Session<'sess> {
    pub fn new() -> Self {
        Self {
            hir_map: RefCell::new(HirMap::new()),
            dropless_arena: Arena::new(),

            types: RefCell::new(HashMap::new()),

            instances: RefCell::new(HashMap::new()),
        }
    }

    pub fn enter<F, R>(&'sess self, f: F) -> R
    where
        F: FnOnce(&'sess Self) -> R,
    {
        f(self)
    }

    pub fn hir<F, R>(&'sess self, f: F) -> R
    where
        F: FnOnce(&mut HirMap<'sess>) -> R,
    {
        f(&mut self.hir_map.borrow_mut())
    }

    pub fn arena(&self) -> &Arena {
        &self.dropless_arena
    }

    pub fn intern_ty(&'sess self, ty: TyKind<'sess>) -> Ty<'sess> {
        let mut map = self.types.borrow_mut();
        match map.get(&ty) {
            None => {
                let pooled = Pooled(self.arena().alloc(ty));
                map.insert(ty, pooled);
                pooled
            }

            Some(pooled_ptr) => *pooled_ptr,
        }
    }

    pub fn intern_instance_def(&'sess self, def: InstanceDef<'sess>) -> Instance<'sess> {
        let mut map = self.instances.borrow_mut();
        match map.get(&def) {
            None => {
                let pooled = Pooled(self.arena().alloc(def));
                map.insert(def, pooled);
                pooled
            }

            Some(pooled_ptr) => *pooled_ptr,
        }
    }
}
