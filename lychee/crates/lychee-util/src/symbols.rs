use crate::arena::Arena;
use crate::id::{IdxVec, IndexId};

use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::sync::{LazyLock, Mutex};

type Interner = LazyLock<Mutex<SymbolInterner>>;

static SYMBOL_INTERNER: Interner = LazyLock::new(|| Mutex::new(SymbolInterner::new()));

struct SymbolInterner {
    arena: Arena,
    map: HashMap<&'static str, SymbolId>,
    storage: IdxVec<SymbolId, &'static str>,
}

impl SymbolInterner {
    fn new() -> Self {
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

    fn intern(&mut self, str: &str) -> SymbolId {
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId {
    inner: u32,
}

impl IndexId for SymbolId {
    fn new(n: usize) -> Self {
        Self::new_usize(n)
    }

    fn idx(&self) -> usize {
        self.inner as usize
    }

    fn own_name() -> &'static str {
        "SymbolId"
    }
}

impl Debug for SymbolId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self == Self::DUMMY {
            return write!(f, "<dummy!>");
        }

        write!(f, "\"{}\"@{}", self.get_interned(), self.inner)
    }
}

impl Display for SymbolId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Debug>::fmt(self, f)
    }
}

macro_rules! interned_consts {
    ($($name:ident -> $id:expr ),*) => {
        $(
            pub const fn $name() -> SymbolId {
                SymbolId { inner: $id }
            }
        )*
    };
}

impl SymbolId {
    const BASE_SYMBOLS: [&str; 14] = [
        "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "nil", "bool", "self",
        "main",
    ];

    pub const DUMMY: Self = Self { inner: u32::MAX };

    fn new(inner: u32) -> Self {
        Self { inner }
    }

    fn new_usize(inner: usize) -> Self {
        Self::new(inner.try_into().unwrap())
    }

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
        bool -> 11,
        self_ -> 12,
        main -> 13
    );

    #[track_caller]
    pub fn get_interned(&self) -> &str {
        // debug_assert!(
        //     self != &Self::DUMMY,
        //     "tried to get the interned value of a dummy `SymbolId`"
        // );

        let interner = SYMBOL_INTERNER.lock().unwrap();
        interner.storage.get(*self).unwrap_or(&"<dummy!>")
    }

    #[track_caller]
    #[inline]
    pub fn intern(sym: &str) -> Self {
        SYMBOL_INTERNER.lock().unwrap().intern(sym)
    }
}
