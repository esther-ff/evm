use super::gc::Gc;

/// Trait for types
/// that can be inside `Gc` pointers
/// and that could contain `Gc` pointers.
pub trait ToHeap<'gc> {
    const NEEDS_TO_BE_TRACED: bool = true;

    fn trace<V: Trace<'gc>>(&self, val: &mut V) {
        assert!(
            !Self::NEEDS_TO_BE_TRACED,
            "the implementation of this trait is lacking a function to trace it's objects"
        );

        let _ = val;
    }
}

/// This trait is implemented for types
/// that can trace down objects allocated
/// in the arena
pub trait Trace<'gc> {
    fn trace_gc(&mut self, gc: Gc<'gc, ()>);

    fn trace<Item: ToHeap<'gc> + ?Sized>(&mut self, value: &Item)
    where
        Self: Sized,
    {
        if Item::NEEDS_TO_BE_TRACED {
            value.trace(self);
        }
    }
}

/// Trait for any type that can be used as an additional root
pub trait ExtraRoot<'gc>: ToHeap<'gc> {
    fn trace<V: Trace<'gc>>(&self, t: &mut V) {
        <Self as ToHeap<'gc>>::trace(self, t);
    }
}
