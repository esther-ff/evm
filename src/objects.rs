use crate::gc::{Gc, ToHeap};
use crate::instruction::ProgramCounter;
use std::sync::Arc;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Value<'gc> {
    Object(Gc<'gc, Object>),
    Number(u32),
    Function(FnRef),

    /// Cursed being!
    /// Go back to your caves of zeroes
    /// Mx. NonNull and Ms. NonZero
    /// may send you back to your place
    ///
    /// To the fronts of Gandesa,
    /// to the Inn to remind you
    ///
    /// with the first meal, of the shrapnel
    /// at Jarama
    ///
    /// and with the second meal, of the memories
    /// at Belchite.
    Nil,
}

impl<'gc> Value<'gc> {
    pub fn assert_num(self) -> Option<u32> {
        if let Value::Number(num) = self {
            return Some(num);
        }

        None
    }
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Array {
    // ... todo!
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayType {
    U32 = 0,
    U64 = 1,
    F32 = 2,
    F64 = 3,
    Ref = 4,
}

#[derive(Debug)]
pub struct Instance {
    // todo...
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstanceId(pub u16);
