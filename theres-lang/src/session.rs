use std::{collections::HashMap, mem::transmute};

use crate::arena::Arena;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId {
    private: u32,
}

impl SymbolId {
    pub const DUMMY: Self = Self { private: u32::MAX };
}

pub struct Interner {
    map: HashMap<&'static str, SymbolId>,
    storage: Vec<&'static str>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            storage: Vec::new(),
        }
    }

    pub fn intern(&mut self, str: &str, arena: &Arena) -> SymbolId {
        if let Some(present) = self.map.get(str) {
            return *present;
        };

        // Safety:
        //
        // The interner will live shorter than the entire session
        let new_str: &'static str = unsafe { transmute(arena.alloc_string(str)) };
        let id = SymbolId {
            private: self.storage.len() as u32,
        };

        self.map.insert(new_str, id);
        self.storage.push(new_str);

        id
    }
}

pub struct Session {
    /// Arena for anything
    /// that doesn't impl `Drop`
    arena: Arena,

    /// Interner
    interner: Interner,
}

impl Session {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            interner: Interner::new(),
        }
    }

    pub fn intern_string(&mut self, str: &str) -> SymbolId {
        self.interner.intern(str, &self.arena)
    }

    pub fn get_string(&self, id: SymbolId) -> &str {
        self.interner.storage[id.private as usize]
    }
}
