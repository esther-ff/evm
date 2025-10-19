#![allow(clippy::zero_sized_map_values)]
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result};
use std::hash::Hash;
use std::ops::Deref;
use std::ptr::eq;

use crate::arena::Arena;

#[derive(Clone, Copy, Hash, PartialEq, PartialOrd, Ord, Eq)]
struct Zst;

pub struct Pool<'a, T> {
    set: HashMap<&'a T, Zst>,
}

impl<'a, T: Eq + Hash + Clone> Pool<'a, T> {
    pub(crate) fn new() -> Self {
        Self {
            set: HashMap::new(),
        }
    }

    pub(crate) fn pool<A>(&mut self, value: A, arena: &'a Arena) -> Pooled<'a, T>
    where
        A: Borrow<T>,
    {
        if let Some(val) = self.set.get_key_value(value.borrow()) {
            return Pooled(val.0);
        }

        let alloc = arena.alloc(value.borrow().clone());
        self.set.insert(alloc, Zst);
        Pooled(alloc)
    }
}

#[derive(PartialOrd, Eq, Ord, Hash)]
pub struct Pooled<'a, T>(pub &'a T);

impl<T> Copy for Pooled<'_, T> {}
impl<T> Clone for Pooled<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Debug> Debug for Pooled<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

impl<T: Display> Display for Pooled<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

unsafe impl<T: Sync> Sync for Pooled<'_, T> {}
unsafe impl<T: Send> Send for Pooled<'_, T> {}

impl<T> Deref for Pooled<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T> PartialEq for Pooled<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        eq(self.0, other.0)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    pub fn pool() {
        #[derive(Debug, Copy, Clone, Hash, PartialEq, PartialOrd, Ord, Eq)]
        pub struct Test {
            a: u128,
            b: u128,
        }

        let arena = crate::arena::Arena::new();
        let mut pool: super::Pool<'_, Test> = super::Pool::new();

        let a = pool.pool(Test { a: 0, b: 23 }, &arena);
        let b = pool.pool(Test { a: 0, b: 23 }, &arena);
        let c = pool.pool(Test { a: 1, b: 23 }, &arena);
        dbg!(a, b);
        println!("{:p} {:p} {:p}", a.0, b.0, c.0);
    }
}
