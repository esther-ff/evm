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

#[derive(Copy, Clone)]
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
}
