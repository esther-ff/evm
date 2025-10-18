use std::fmt::Debug;

use crate::arena::Arena;
use crate::pill::body::Local;
use crate::pill::cfg::Operand;
use crate::session::Session;
use crate::types::fun_cx::FieldId;

pub struct AccessBuilder<'il> {
    base: Local,
    modifs: Vec<AccessKind<'il>, &'il Arena>,
}

impl<'il> AccessBuilder<'il> {
    pub fn new(arena: &'il Arena, base: Local) -> Self {
        Self {
            base,
            modifs: Vec::new_in(arena),
        }
    }

    pub fn index(&mut self, idx: Operand<'il>) {
        self.modifs.push(AccessKind::Index(idx));
    }

    pub fn field(&mut self, field: FieldId) {
        self.modifs.push(AccessKind::Field(field));
    }

    pub fn finish(&mut self, cx: &'il Session<'il>) -> Access<'il> {
        Access {
            base: self.base,
            modifs: cx.arena().alloc_from_iter(self.modifs.iter().copied()),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum AccessKind<'il> {
    Index(Operand<'il>),
    Field(FieldId),
}

#[derive(Copy, Clone)]
pub struct Access<'il> {
    base: Local,
    modifs: &'il [AccessKind<'il>],
}

impl Access<'_> {
    pub fn base(base: Local) -> Self {
        Self { base, modifs: &[] }
    }

    pub fn get_base(&self) -> Local {
        self.base
    }
}

impl Debug for Access<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.base.to_usize())?;

        for kind in self.modifs {
            match kind {
                AccessKind::Index(_idx) => write!(f, "[idx?]")?,
                AccessKind::Field(id) => write!(f, ".f{}", id.to_usize())?,
            }
        }

        Ok(())
    }
}
