mod context;
mod envelope;
mod gc;
mod heap;
mod impls;
mod traits;
mod write_barrier;

pub use gc::Gc;
pub use heap::{Heap, RootItem};
pub use traits::{ToHeap, Trace};

pub struct RootableShim<T: ?Sized>(core::marker::PhantomData<T>);

impl<'r, T: ?Sized + RootItem<'r>> RootItem<'r> for RootableShim<T> {
    type Root = <T as RootItem<'r>>::Root;
}

#[macro_export]
macro_rules! RootType {
    ($lf:lifetime, $ty:ty) => {
        $crate::gc::RootableShim<dyn for<$lf> $crate::gc::RootItem<$lf, Root = $ty>>
    };

    (NoGc, $ty:ty) => {
        RootType!('__gc, Gc<'__gc, $ty>)
    };

    (Gc, $ty:ty) => {
        RootType!('__gc, $ty)
    }
}
