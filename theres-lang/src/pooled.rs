use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result};
use std::ops::Deref;
use std::ptr::eq;

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

pub type Pool<'a, T> = HashMap<T, Pooled<'a, T>>;
