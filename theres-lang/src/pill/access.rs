use crate::arena::Arena;
use crate::pill::body::Local;
use crate::pill::cfg::Operand;
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

impl<'il> Access<'il> {
    pub fn base(base: Local) -> Self {
        Self { base, modifs: &[] }
    }
}
