use super::context::MutPeriod;
use super::context::{GcBox, TypedGcBox};
use super::traits::{ToHeap, Trace};
use super::write_barrier::Mutation;

use core::borrow::Borrow;
use core::cell::Cell;
use core::cell::{Ref, RefMut};
use core::convert::AsRef;
use core::fmt::{Debug, Display};
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;
use std::cell::RefCell;

/// A pointer to memory taken up by type `T`
/// managed by the garbage collector.
pub struct Gc<'gc, T: ?Sized + 'gc> {
    ptr: NonNull<TypedGcBox<T>>,

    _invariance: PhantomData<&'gc mut Cell<()>>,
}

impl<'gc, T: ?Sized + 'gc> Copy for Gc<'gc, T> {}

impl<'gc, T: ?Sized + 'gc> Clone for Gc<'gc, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'gc, T: ToHeap<'gc> + 'gc> Gc<'gc, T> {
    pub fn new(mutcx: &MutPeriod<'gc>, data: T) -> Gc<'gc, T> {
        Gc {
            ptr: mutcx.allocate(data),
            _invariance: PhantomData,
        }
    }
}

impl<'gc, T: ?Sized + 'gc> Gc<'gc, T> {
    /// Returns a refernece to the data inside
    /// however with a lifetime bound to the entire callback
    /// for the heap.
    pub fn get_ref(self) -> &'gc T {
        unsafe { &self.ptr.as_ref().data }
    }

    /// Turns the `Gc` into a `Gcbox`
    pub unsafe fn get_gc_box(&self) -> GcBox {
        let ptr = self.ptr.cast::<TypedGcBox<()>>();

        GcBox::new(ptr)
    }

    /// Erases the type of the pointer inside this
    /// `Gc`, used for `Collect` implementations.
    fn erase_type(self) -> Gc<'gc, ()> {
        Gc::<()> {
            ptr: self.ptr.cast::<TypedGcBox<()>>(),
            _invariance: PhantomData,
        }
    }

    /// Creates a write barrier to this `Gc` and returns a `Mutation`
    /// which represents a "session" during which mutation of the
    /// data inside is safe (the session stretches through the entire closure inside the heap)
    fn get_barrier(ptr: Self, period: &MutPeriod<'gc>) -> &'gc Mutation<T> {
        unsafe { period.barrier(ptr.get_gc_box()) };

        Mutation::from_ref(ptr.get_ref())
    }
}

type MutResult<'gc, T, E = core::cell::BorrowMutError> = core::result::Result<RefMut<'gc, T>, E>;
type CellResult<'gc, T, E = core::cell::BorrowError> = core::result::Result<Ref<'gc, T>, E>;

impl<'gc, T: 'gc> Gc<'gc, RefCell<T>> {
    pub fn borrow(self, period: &'gc MutPeriod<'gc>) -> Ref<'gc, T> {
        self.try_borrow(period).unwrap()
    }

    pub fn try_borrow(self, period: &'gc MutPeriod<'gc>) -> CellResult<T> {
        let mutation = Gc::<'gc, RefCell<T>>::get_barrier(self, period);

        mutation.deref().try_borrow()
    }

    pub fn borrow_mut(self, period: &'gc MutPeriod<'gc>) -> RefMut<'gc, T> {
        self.try_borrow_mut(period).unwrap()
    }

    pub fn try_borrow_mut(self, period: &'gc MutPeriod<'gc>) -> MutResult<T> {
        let mutation = Gc::<'gc, RefCell<T>>::get_barrier(self, period);

        mutation.deref().try_borrow_mut()
    }
}

impl<'gc, T: 'gc + ?Sized> ToHeap<'gc> for Gc<'gc, T> {
    fn trace<Tr: Trace<'gc>>(&self, val: &mut Tr) {
        println!("meow");
        val.trace_gc(self.erase_type());
    }
}

impl<'gc, T: 'gc + ?Sized> Deref for Gc<'gc, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl<'gc, T: 'gc + ?Sized> AsRef<T> for Gc<'gc, T> {
    fn as_ref(&self) -> &T {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl<'gc, T: 'gc + ?Sized> Borrow<T> for Gc<'gc, T> {
    fn borrow(&self) -> &T {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl<'gc, T: 'gc + ?Sized + Debug> Debug for Gc<'gc, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

impl<'gc, T: 'gc + ?Sized + Display> Display for Gc<'gc, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}
