use crate::hir::def::Definitions;

pub struct Context {
    pub defs: Definitions,
}

impl Context {
    pub fn new() -> Self {
        Self {
            defs: Definitions::new(),
        }
    }
}
