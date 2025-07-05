use super::context::{Cx, MutPeriod};
use crate::gc::ToHeap;

use core::ptr;

pub trait RootItem<'a> {
    type Root: ?Sized + 'a;
}

type Root<'lf, R> = <R as RootItem<'lf>>::Root;

pub struct Heap<R>
where
    R: for<'root> RootItem<'root>,
{
    context: Cx,
    root: Root<'static, R>,
}

impl<R> Heap<R>
where
    R: for<'root> RootItem<'root>,
    for<'root> Root<'root, R>: Sized,
{
    pub fn new<F>(init: F) -> Heap<R>
    where
        F: for<'gc> FnOnce(&MutPeriod<'gc>) -> Root<'gc, R>,
    {
        // unsafe {
        let context = Cx::new();
        // let period: &'static MutPeriod<'_> = &*ptr::from_ref(context.to_mut_period());
        let root: Root<'static, R> = init(context.to_mut_period());

        Heap { context, root }
        // }
    }

    pub fn enter<Mut, Ret>(&mut self, f: Mut) -> Ret
    where
        Mut: for<'gc> FnOnce(&'gc MutPeriod<'gc>, &Root<'gc, R>) -> Ret,
    {
        unsafe {
            let period: &'static MutPeriod<'_> = &*ptr::from_ref(self.context.to_mut_period());

            f(period, &self.root)
        }
    }

    pub fn enter_mut<Mut, Ret>(&mut self, f: Mut) -> Ret
    where
        Mut: for<'gc> FnOnce(&'gc MutPeriod<'gc>, &mut Root<'gc, R>) -> Ret,
    {
        unsafe {
            self.context.mark_root_for_tracing();
            let period: &'static MutPeriod<'_> = &*ptr::from_ref(self.context.to_mut_period());
            // let root: &'static mut Root<'_, R> = &mut *(&mut self.root as *mut _);

            f(period, &mut self.root)
        }
    }
}

impl<R> Heap<R>
where
    R: for<'root> RootItem<'root>,
    for<'root> Root<'root, R>: ToHeap<'root>,
{
    pub fn do_garbage_collection(&mut self) {
        self.context.gc_cycle(&self.root);
    }
}
