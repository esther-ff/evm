use std::{
    fmt::{Debug, Formatter, Result},
    iter::Enumerate,
    marker::PhantomData,
    ops::{Deref, DerefMut, Index, IndexMut},
};

pub trait IndexId: Copy + Clone {
    fn new(n: usize) -> Self;
    fn idx(&self) -> usize;
    fn own_name() -> &'static str;
}

#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdxSlice<I, T> {
    _boo: core::marker::PhantomData<I>,
    inner: [T],
}

impl<I: IndexId, T> IdxSlice<I, T> {
    pub fn new(slice: &[T]) -> &Self {
        unsafe { &*(core::ptr::from_ref(slice) as *const Self) }
    }

    pub fn new_mut(slice: &mut [T]) -> &mut Self {
        unsafe { &mut *(core::ptr::from_mut(slice) as *mut Self) }
    }

    pub fn iter_mut(&mut self) -> IdxIter<I, std::slice::IterMut<'_, T>> {
        IdxIter {
            inner: self.inner.iter_mut().enumerate(),
            _id: PhantomData,
        }
    }

    pub fn iter(&self) -> IdxIter<I, std::slice::Iter<'_, T>> {
        IdxIter {
            inner: self.inner.iter().enumerate(),
            _id: PhantomData,
        }
    }
}

impl<I: IndexId, T> IdxSlice<I, T> {
    pub fn get(&self, id: I) -> Option<&T> {
        self.inner.get(id.idx())
    }

    pub fn get_mut(&mut self, id: I) -> Option<&mut T> {
        self.inner.get_mut(id.idx())
    }
}

impl<I, T: Debug> Debug for IdxSlice<I, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<I, T> Deref for IdxSlice<I, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<I, T> DerefMut for IdxSlice<I, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<'lf, I: IndexId, T> IntoIterator for &'lf IdxSlice<I, T> {
    type Item = (I, &'lf T);
    type IntoIter = IdxIter<I, std::slice::Iter<'lf, T>>;

    fn into_iter(self) -> Self::IntoIter {
        IdxIter {
            inner: self.inner.iter().enumerate(),
            _id: core::marker::PhantomData,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdxVec<I, T> {
    inner: Vec<T>,
    _boo: PhantomData<I>,
}

impl<I, T> IdxVec<I, T> {
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            _boo: PhantomData,
        }
    }

    pub fn reserve(&mut self, size: usize) {
        self.inner.reserve(size);
    }

    pub fn new_from_vec(vec: Vec<T>) -> Self {
        Self {
            _boo: PhantomData,
            inner: vec,
        }
    }
}

impl<I: IndexId, T> IdxVec<I, T> {
    pub fn push(&mut self, val: T) -> I {
        let id = self.inner.len();
        self.inner.push(val);
        I::new(id)
    }

    pub fn future_id(&self) -> I {
        let id = self.inner.len();
        I::new(id)
    }

    pub fn get(&self, id: I) -> Option<&T> {
        self.inner.get(id.idx())
    }

    pub fn inner(&self) -> &[T] {
        &self.inner
    }
}

impl<I, T: Debug> Debug for IdxVec<I, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<I: IndexId, T> Deref for IdxVec<I, T> {
    type Target = IdxSlice<I, T>;

    fn deref(&self) -> &Self::Target {
        IdxSlice::new(&self.inner)
    }
}

impl<I: IndexId, T> DerefMut for IdxVec<I, T> {
    fn deref_mut(&mut self) -> &mut IdxSlice<I, T> {
        IdxSlice::new_mut(&mut self.inner)
    }
}

impl<I, T> Default for IdxVec<I, T> {
    fn default() -> Self {
        Self::new_from_vec(vec![])
    }
}

impl<I: IndexId, T> Index<I> for IdxVec<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.inner[index.idx()]
    }
}

impl<I: IndexId, T> IndexMut<I> for IdxVec<I, T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        &mut self.inner[index.idx()]
    }
}

impl<I: IndexId, T> IntoIterator for IdxVec<I, T> {
    type Item = (I, T);
    type IntoIter = IdxIter<I, std::vec::IntoIter<T>>;

    fn into_iter(self) -> Self::IntoIter {
        IdxIter {
            inner: self.inner.into_iter().enumerate(),
            _id: core::marker::PhantomData,
        }
    }
}

pub struct IdxIter<I: IndexId, Iter: Iterator> {
    inner: Enumerate<Iter>,
    _id: core::marker::PhantomData<I>,
}

impl<I: IndexId, T> Iterator for IdxIter<I, std::vec::IntoIter<T>> {
    type Item = (I, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (I::new(k), v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'lt, I: IndexId, T> Iterator for IdxIter<I, std::slice::Iter<'lt, T>> {
    type Item = (I, &'lt T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (I::new(k), v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'lt, I: IndexId, T> Iterator for IdxIter<I, std::slice::IterMut<'lt, T>> {
    type Item = (I, &'lt mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (I::new(k), v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[macro_export]
macro_rules! newtyped_index {
    ($name:ident, $map:ident, $vec:ident, $slice:ident) => {
        $crate::newtyped_index!($name, $map, $vec);

        #[allow(dead_code)]
        pub type $slice<T> = $crate::id::IdxSlice<$name, T>;
    };

    ($name:ident, $map:ident, $vec:ident) => {
        #[allow(dead_code)]
        pub type $map<T> = ::std::collections::HashMap<$name, T>;

        #[allow(dead_code)]
        pub type $vec<T> = $crate::id::IdxVec<$name, T>;

        #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
        pub struct $name {
            private: u32,
        }

        impl $name {
            #[allow(dead_code)]
            pub const ZERO: Self = Self { private: 0_u32 };
            #[allow(dead_code)]
            pub const DUMMY: Self = Self { private: u32::MAX };

            // pub fn as_u32(&self) -> u32 {
            //     self.private
            // }

            #[allow(dead_code)]
            pub const fn new(private: u32) -> Self {
                Self { private }
            }

            #[allow(dead_code)]
            pub fn new_usize(i: usize) -> Self {
                Self::new(i.try_into().expect("id overflow"))
            }

            #[allow(dead_code)]
            pub const fn to_usize(self) -> usize {
                self.private as usize
            }

            #[allow(dead_code)]
            pub fn is_dummy(self) -> bool {
                self == Self::DUMMY
            }
        }

        impl $crate::id::IndexId for $name {
            fn new(a: usize) -> Self {
                $name::new(a.try_into().expect("id overflow"))
            }

            fn idx(&self) -> usize {
                self.private as usize
            }

            fn own_name() -> &'static str {
                stringify!($name)
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, "{}#{}", stringify!($name), self.private)
            }
        }

        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, "{}#{}", stringify!($name), self.private)
            }
        }
    };
}
