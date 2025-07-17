use std::collections::HashMap;

use crate::arena::Arena;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId {
    private: u32,
}

pub struct Session {
    /// Arena for anything
    /// that doesn't impl `Drop`
    arena: Arena,

    /// Stores SymbolId to ptr relations
    symbols: HashMap<SymbolId, *const str>,

    /// Next id
    symbol_id_counter: u32,
}

impl Session {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            symbols: HashMap::new(),
            symbol_id_counter: 0,
        }
    }

    pub fn intern_string(&mut self, str: &str) -> SymbolId {
        let id = self.new_symbol_id();
        let reff = self.arena.alloc_string(str);

        let _ = self.symbols.insert(id, reff as *const str);

        id
    }

    pub fn get_string(&self, id: SymbolId) -> &str {
        let ptr = self
            .symbols
            .get(&id)
            .expect("symbol ids only originate from the session");

        // SAFETY: This pointer is stored in a hashmap
        // only managed by this `Session`, it was created following
        // a string being interned, therefore it is a valid pointer
        // that has it's lifetime bound to the session's lifetime.
        unsafe { &(**ptr) }
    }

    fn new_symbol_id(&mut self) -> SymbolId {
        let old = SymbolId {
            private: self.symbol_id_counter,
        };
        self.symbol_id_counter += 1;

        old
    }
}
