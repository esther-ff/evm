use super::context::{Cx, MutPeriod};
use crate::gc::ToHeap;

use core::ptr;

pub trait RootItem<'a> {
    type Root: ?Sized + 'a;
}

type Root<'lf, R> = <R as RootItem<'lf>>::Root;

pub struct Heap<R, E>
where
    R: for<'root> RootItem<'root>,
    E: for<'root> RootItem<'root> + Sized,
    <E as RootItem<'static>>::Root: Sized,
{
    context: Cx,
    extra: Option<Root<'static, E>>,
    root: Root<'static, R>,
}

impl<R, E> Heap<R, E>
where
    R: for<'root> RootItem<'root>,
    for<'root> Root<'root, R>: Sized,
    E: for<'root> RootItem<'root>,
    for<'root> Root<'root, E>: Sized,
{
    pub fn new<F>(init: F) -> Heap<R, E>
    where
        F: for<'gc> FnOnce(&MutPeriod<'gc>) -> Root<'gc, R>,
    {
        // unsafe {
        let context = Cx::new();
        // let period: &'static MutPeriod<'_> = &*ptr::from_ref(context.to_mut_period());
        let root: Root<'static, R> = init(context.to_mut_period());

        Heap {
            context,
            root,
            extra: None,
        }
        // }
    }

    pub fn new_extra<F1, F2>(init: F1, init_extra: F2) -> Heap<R, E>
    where
        F1: for<'gc> FnOnce(&MutPeriod<'gc>) -> Root<'gc, R>,
        F2: for<'gc> FnOnce(&MutPeriod<'gc>) -> Root<'gc, E>,
    {
        let context = Cx::new();
        let root: Root<'static, R> = init(context.to_mut_period());
        let extra_root: Root<'static, E> = init_extra(context.to_mut_period());

        Heap {
            context,
            root,
            extra: Some(extra_root),
        }
    }

    pub fn enter<Mut, Ret>(&mut self, f: Mut) -> Ret
    where
        Mut: for<'gc> FnOnce(
            &'gc MutPeriod<'gc>,
            &'gc Root<'gc, R>,
            Option<&'gc Root<'gc, E>>,
        ) -> Ret,
    {
        unsafe {
            let period: &'static MutPeriod<'_> = &*ptr::from_ref(self.context.to_mut_period());
            let root: &'static Root<'static, R> = &*ptr::from_ref(&self.root);
            let extra: Option<&'static Root<'static, E>> =
                self.extra.as_ref().map(|root| &*ptr::from_ref(root));

            f(period, root, extra)
        }
    }

    pub fn enter_mut<Mut, Ret>(&mut self, f: Mut) -> Ret
    where
        Mut: for<'gc> FnOnce(
            &'gc MutPeriod<'gc>,
            &mut Root<'gc, R>,
            Option<&'gc mut Root<'gc, E>>,
        ) -> Ret,
    {
        unsafe {
            self.context.mark_root_for_tracing();
            let period: &'static MutPeriod<'_> = &*ptr::from_ref(self.context.to_mut_period());
            let extra: Option<&'static mut Root<'static, E>> =
                self.extra.as_mut().map(|root| &mut *ptr::from_mut(root));

            f(period, &mut self.root, extra)
        }
    }
}

impl<R, E> Heap<R, E>
where
    R: for<'root> RootItem<'root>,
    for<'root> Root<'root, R>: ToHeap<'root>,
    E: for<'root> RootItem<'root>,
    for<'root> Root<'root, R>: ToHeap<'root>,
    <E as RootItem<'static>>::Root: Sized + ToHeap<'static>,
{
    pub fn do_garbage_collection(&mut self) {
        self.context.gc_cycle(&self.root);

        if let Some(ref extra) = self.extra {
            self.context.gc_cycle(extra);
        }
    }
}
