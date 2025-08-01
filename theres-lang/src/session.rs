use std::{collections::HashMap, mem::transmute};

use crate::arena::Arena;

// #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct SymbolId {
//     private: u32,
// }

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
    const BASE_SYMBOLS: [&str; 11] = [
        "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "nil",
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
        nil -> 10
    );
}

pub struct Interner {
    arena: Arena,
    map: HashMap<&'static str, SymbolId>,
    storage: Vec<&'static str>,
}

impl Interner {
    pub fn new() -> Self {
        let mut me = Self {
            map: HashMap::new(),
            storage: Vec::new(),
            arena: Arena::new(),
        };

        me.pre_interned();

        me
    }

    pub fn pre_interned(&mut self) {
        for sym in SymbolId::BASE_SYMBOLS {
            self.intern(sym);
        }
    }

    pub fn intern(&mut self, str: &str) -> SymbolId {
        if let Some(present) = self.map.get(str) {
            return *present;
        };

        // Safety:
        //
        // The Arena is in the interner
        let new_str: &'static str = unsafe { transmute(self.arena.alloc_string(str)) };

        let id = SymbolId {
            private: self.storage.len() as u32,
        };

        self.map.insert(new_str, id);
        self.storage.push(new_str);

        id
    }
}

pub struct Session {
    /// Interner
    interner: Interner,
}

impl Session {
    pub fn new() -> Self {
        Self {
            interner: Interner::new(),
        }
    }

    pub fn intern_string(&mut self, str: &str) -> SymbolId {
        self.interner.intern(str)
    }

    pub fn get_string(&self, id: SymbolId) -> &str {
        self.interner.storage[id.private as usize]
    }

    pub fn debug_symbol_id_string(&self) -> &HashMap<&'static str, SymbolId> {
        &self.interner.map
    }
}
