#![warn(clippy::pedantic)]

mod context;
mod gc;
mod heap;
mod traits;
mod write_barrier;

use std::cell::RefCell;

use gc::Gc;
use heap::Heap;
use traits::{ToHeap, Trace};

use crate::heap::RootItem;

#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
enum Object<'gc, T> {
    Number(f64),
    Ptr(Gc<'gc, T>),
    Nil,
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Object<'gc, T> {
    const NEEDS_TO_BE_TRACED: bool = true;

    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        if let Object::Ptr(gc) = self {
            gc.trace(val);
        }
    }
}

struct Stack<'gc, T: ToHeap<'gc>> {
    buf: RefCell<[Object<'gc, T>; 4]>,
}

impl<'gc, T: ToHeap<'gc> + Copy> Stack<'gc, T> {
    fn new() -> Self {
        Self {
            buf: RefCell::new([Object::Nil; 4]),
        }
    }
}

impl ToHeap<'_> for i32 {
    const NEEDS_TO_BE_TRACED: bool = false;
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Stack<'gc, T> {
    const NEEDS_TO_BE_TRACED: bool = true;

    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        for item in self.buf.borrow().iter() {
            item.trace(val);
        }
    }
}

struct RootableShim<T: ?Sized>(core::marker::PhantomData<T>);

impl<'r, T: ?Sized + RootItem<'r>> RootItem<'r> for RootableShim<T> {
    type Root = <T as RootItem<'r>>::Root;
}

macro_rules! RootType {
    ($lf:lifetime, $ty:ty) => {
        $crate::RootableShim<dyn for<$lf> $crate::RootItem<$lf, Root = $ty>>
    };

    (Gc, $ty:ty) => {
        RootType!('__gc, Gc<'__gc, $ty>)
    }
}

fn main() {
    let mut heap = Heap::<RootType![Gc, Stack<'__gc, i32>]>::new(|m| Gc::new(m, Stack::new()));

    heap.enter_mut(|period, root| {
        let mut buf = root.buf.borrow_mut();

        for item in buf.iter_mut() {
            *item = Object::Ptr(Gc::new(period, 4_i32));
        }
    });

    heap.enter_mut(|_period, root| {
        let mut buf = root.buf.borrow_mut();

        for item in buf.iter_mut() {
            *item = Object::Nil;
        }
    });

    heap.do_garbage_collection();

    heap.enter(|p, _| {
        dbg!(p.metrics());
    });

    heap.do_garbage_collection();

    heap.enter(|p, _| {
        dbg!(p.metrics());
    });
}
