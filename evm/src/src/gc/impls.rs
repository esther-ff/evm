use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use crate::gc::{ToHeap, Trace};

macro_rules! static_type_impls {
    ($($ty:ty),*) => {
        $(
            impl<'gc> ToHeap<'gc> for $ty {
                const NEEDS_TO_BE_TRACED: bool = false;
            }
        )*
    };
}

static_type_impls!(
    u8,
    u16,
    u32,
    u64,
    u128,
    i8,
    i16,
    i32,
    i64,
    i128,
    // f16,
    f32,
    f64,
    // f128,
    str,
    Box<str>,
    Arc<str>,
    Rc<str>,
    String,
    CString,
    CStr,
    Box<CStr>,
    Arc<CStr>,
    Rc<CStr>,
    Path,
    Box<Path>,
    Arc<Path>,
    Rc<Path>,
    PathBuf
);

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for [T] {
    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        for item in self {
            item.trace(val);
        }
    }
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Arc<T> {
    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        self.as_ref().trace(val);
    }
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Rc<T> {
    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        self.as_ref().trace(val);
    }
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Box<T> {
    fn trace<A: Trace<'gc>>(&self, val: &mut A) {
        (**self).trace(val);
    }
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for Vec<T> {
    fn trace<V: Trace<'gc>>(&self, val: &mut V) {
        for item in self {
            item.trace(val);
        }
    }
}

impl<'gc, K, V> ToHeap<'gc> for HashMap<K, V>
where
    K: ToHeap<'gc>,
    V: ToHeap<'gc>,
{
    fn trace<Tr: Trace<'gc>>(&self, val: &mut Tr) {
        for key in self.keys() {
            key.trace(val);
        }

        for value in self.values() {
            value.trace(val);
        }
    }
}

impl<'gc, T: ToHeap<'gc>> ToHeap<'gc> for RefCell<T> {
    fn trace<V: Trace<'gc>>(&self, val: &mut V) {
        self.borrow().trace(val);
    }
}
