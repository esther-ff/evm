mod context;
mod gc;
mod heap;
mod impls;
mod traits;
mod write_barrier;

pub use gc::Gc;
pub use heap::{Heap, RootItem};
pub use traits::{ToHeap, Trace};

struct RootableShim<T: ?Sized>(core::marker::PhantomData<T>);

impl<'r, T: ?Sized + RootItem<'r>> RootItem<'r> for RootableShim<T> {
    type Root = <T as RootItem<'r>>::Root;
}

#[macro_export]
macro_rules! RootType {
    ($lf:lifetime, $ty:ty) => {
        $crate::RootableShim<dyn for<$lf> $crate::RootItem<$lf, Root = $ty>>
    };

    (Gc, $ty:ty) => {
        RootType!('__gc, Gc<'__gc, $ty>)
    }
}
