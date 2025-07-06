use crate::gc::{Gc, ToHeap};
use crate::instruction::ProgramCounter;
use std::sync::Arc;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Value<'gc> {
    Object(Gc<'gc, Object>),
    Number(u32),
    Nil,
    Function(FnRef),
}

impl<'gc> ToHeap<'gc> for Value<'gc> {
    fn trace<V: crate::gc::Trace<'gc>>(&self, _val: &mut V) {
        if let Value::Object(_obj) = self {
            // todo
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct FnRef(pub u32);

impl FnRef {
    /// a `FnRef` pointing to the function at index 0
    /// which should be the `main` function.
    pub const MAIN_FN: FnRef = FnRef(0);
}

pub(crate) struct Functions(Vec<Func>);

impl Functions {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn insert(&mut self, f: Func) {
        self.0.push(f);
    }

    pub fn get(&self, fn_ref: FnRef) -> Option<&Func> {
        self.0.get(fn_ref.0 as usize)
    }
}

pub(crate) struct Func {
    jump_ip: ProgramCounter,
    name: Arc<str>,
    arity: u16,
}

impl Func {
    pub(crate) fn new<A>(jump_ip: u32, name: A, arity: u16) -> Self
    where
        A: Into<Arc<str>>,
    {
        Self {
            name: name.into(),
            jump_ip: ProgramCounter(jump_ip),
            arity,
        }
    }

    pub(crate) fn name(&self) -> &Arc<str> {
        &self.name
    }

    pub(crate) fn arity(&self) -> u16 {
        self.arity
    }

    pub(crate) fn jump_ip(&self) -> ProgramCounter {
        self.jump_ip
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Object {
    // todo!
}

pub(crate) struct Objects {
    storage: Vec<Object>,
}

impl Objects {
    pub(crate) fn new() -> Self {
        Self {
            storage: Vec::new(),
        }
    }

    pub(crate) fn get(&mut self, idx: usize) -> Option<&mut Object> {
        self.storage.get_mut(idx)
    }

    pub(crate) fn insert(&mut self, obj: Object) {
        self.storage.push(obj);
    }
}
