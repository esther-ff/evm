use crate::{gc::ToHeap, objects::Value, stack::Stack};

const MAX_GLOBALS_PER_VM: usize = 1024;

#[derive(Debug, Clone, Copy)]
pub struct GlobalId(pub u32);

#[derive(Debug)]
pub struct Globals<'g> {
    storage: Stack<MAX_GLOBALS_PER_VM, Value<'g>>,
}

impl<'g> Globals<'g> {
    pub fn new() -> Self {
        Self {
            storage: Stack::new(),
        }
    }

    pub fn add(&mut self, item: Value<'g>) -> Option<GlobalId> {
        if self.storage.push(item).is_err() {
            return None;
        }

        let ptr = self.storage.stack_pointer();

        #[allow(clippy::cast_possible_truncation)]
        Some(GlobalId(ptr as u32))
    }

    pub fn get(&self, id: GlobalId) -> Option<Value<'g>> {
        self.storage.buffer().get(id.0 as usize).copied()
    }

    /// Returns `None` if the operation wasn't successful
    /// otherwise returns `Some` with the old value.
    pub fn set(&mut self, id: GlobalId, replace: Value<'g>) -> Option<Value<'g>> {
        let slot = self.storage.buffer_mut().get_mut(id.0 as usize)?;

        let old = Some(*slot);
        *slot = replace;

        old
    }
}

impl<'gc> ToHeap<'gc> for Globals<'gc> {
    fn trace<V: crate::gc::Trace<'gc>>(&self, val: &mut V) {
        self.storage.trace(val);
    }
}
