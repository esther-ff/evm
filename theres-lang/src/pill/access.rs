use std::fmt::Debug;

use crate::arena::Arena;
use crate::pill::body::Local;
use crate::pill::cfg::Operand;
use crate::session::Session;
use crate::types::fun_cx::FieldId;
use crate::types::ty::Ty;

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

    pub fn deref(&mut self) {
        self.modifs.push(AccessKind::Deref);
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
pub enum AccessKind<'il> {
    Index(Operand<'il>),
    Field(FieldId),
    Deref,
}

#[derive(Copy, Clone)]
pub struct Access<'il> {
    base: Local,
    pub(super) modifs: &'il [AccessKind<'il>],
}

impl<'il> Access<'il> {
    pub fn base(base: Local) -> Self {
        Self { base, modifs: &[] }
    }

    pub fn get_base(&self) -> Local {
        self.base
    }

    pub fn only_local(&self) -> Option<Local> {
        if self.modifs.is_empty() {
            return Some(self.base);
        }

        None
    }

    pub fn modifs(&self) -> &[AccessKind<'il>] {
        self.modifs
    }

    pub fn deduct_type(&self, cx: &'il crate::session::Session<'il>, mut base: Ty<'il>) -> Ty<'il> {
        if base.maybe_lambda().is_some() {
            return base;
        }

        for ele in self.modifs {
            base = match ele {
                AccessKind::Index(..) => base.index(),
                AccessKind::Field(f) => match base.maybe_lambda() {
                    None => base.field(cx, *f),
                    Some(lambda) => cx.lambda_env_fields(lambda.did).get(*f).unwrap().0,
                },
                AccessKind::Deref => base.peel_ref(),
            }
        }

        base
    }
}

impl Debug for Access<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l{}", self.base.to_usize())?;

        for kind in self.modifs {
            match kind {
                AccessKind::Index(_idx) => write!(f, "[idx?]")?,
                AccessKind::Deref => write!(f, "*")?,
                AccessKind::Field(id) => write!(f, ".f{}", id.to_usize())?,
            }
        }

        Ok(())
    }
}
