pub trait IndexId: Copy + Clone {
    fn new(n: usize) -> Self;
    fn idx(&self) -> usize;
    fn own_name() -> &'static str;
    fn is_dummy(&self) -> bool;
}

#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdxSlice<I, T> {
    _boo: core::marker::PhantomData<I>,
    inner: [T],
}

impl<I, T> IdxSlice<I, T> {
    pub fn new(slice: &[T]) -> &Self {
        unsafe { &*(core::ptr::from_ref(slice) as *const Self) }
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

impl<I, T: core::fmt::Debug> core::fmt::Debug for IdxSlice<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        core::fmt::Debug::fmt(&self.inner, f)
    }
}

impl<I, T> core::ops::Deref for IdxSlice<I, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'lf, I, T> IntoIterator for &'lf IdxSlice<I, T> {
    type Item = &'lf T;
    type IntoIter = std::slice::Iter<'lf, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdxVec<I, T> {
    inner: Vec<T>,
    _boo: core::marker::PhantomData<I>,
}

impl<I, T> IdxVec<I, T> {
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            _boo: core::marker::PhantomData,
        }
    }

    // pub fn new_with_capacity(cap: usize) -> Self {
    //     Self {
    //         inner: Vec::with_capacity(cap),
    //         _boo: core::marker::PhantomData,
    //     }
    // }

    pub fn new_from_vec(vec: Vec<T>) -> Self {
        Self {
            _boo: core::marker::PhantomData,
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

    pub fn get_mut(&mut self, id: I) -> Option<&mut T> {
        self.inner.get_mut(id.idx())
    }

    // pub fn to_slice(&self) -> &IdxSlice<I, T> {
    //     IdxSlice::new(self.inner.as_slice())
    // }

    // pub fn inner(&self) -> &[T] {
    //     &self.inner
    // }

    // pub fn len(&self) -> usize {
    //     self.inner.len()
    // }
}

// impl<I: IndexId, T: Copy> IdxVec<I, T> {
//     pub fn get_copied(&self, id: I) -> Option<T> {
//         self.get(id).copied()
//     }
// }

impl<I, T: core::fmt::Debug> core::fmt::Debug for IdxVec<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        core::fmt::Debug::fmt(&self.inner, f)
    }
}

impl<I, T> core::ops::Deref for IdxVec<I, T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<I, T> IntoIterator for IdxVec<I, T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

#[macro_export]
macro_rules! newtyped_index {
    ($name:ident, $map:ident, $vec:ident, $slice:ident) => {
        $crate::newtyped_index!($name, $map, $vec);

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
            fn new(private: u32) -> Self {
                Self { private }
            }

            #[allow(dead_code)]
            fn new_usize(i: usize) -> Self {
                Self::new(i.try_into().expect("id overflow"))
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

            fn is_dummy(&self) -> bool {
                self == &Self::DUMMY
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
