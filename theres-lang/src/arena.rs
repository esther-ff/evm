#![allow(clippy::mut_from_ref, clippy::ref_as_ptr, clippy::inline_always)]

use std::{
    alloc::Layout,
    cell::{Cell, RefCell},
    mem::MaybeUninit,
    ptr::NonNull,
};

const CHUNK_SIZE: usize = 1024 * 64;
const BIG_CHUNK_SIZE: usize = 1024 * 1024 * 4;

pub struct Chunk<T = u8> {
    memory: NonNull<[MaybeUninit<T>]>,
}

impl<T> Chunk<T> {
    fn new() -> Self {
        let ptr: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(CHUNK_SIZE);

        unsafe {
            Self {
                memory: NonNull::new_unchecked(Box::leak(ptr) as *mut [MaybeUninit<T>]),
            }
        }
    }

    fn new_big_chunk() -> Self {
        let ptr: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(BIG_CHUNK_SIZE);

        unsafe {
            Self {
                memory: NonNull::new_unchecked(Box::leak(ptr) as *mut [MaybeUninit<T>]),
            }
        }
    }

    fn start(&self) -> *mut u8 {
        self.memory.as_ptr().cast::<u8>()
    }

    fn end(&self) -> *mut u8 {
        unsafe { self.start().add(self.memory.len()) }
    }
}

impl<T> Drop for Chunk<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.memory.as_ptr())) }
    }
}

pub struct Arena {
    start: Cell<*mut u8>,
    end: Cell<*mut u8>,

    chunks: RefCell<Vec<Chunk>>,
}

unsafe impl Sync for Arena {}
unsafe impl Send for Arena {}

impl Arena {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        use core::ptr::null_mut;

        Self {
            start: Cell::new(null_mut()),
            end: Cell::new(null_mut()),
            chunks: RefCell::new(vec![]),
        }
    }

    #[inline]
    pub fn alloc_from_iter<T>(&self, iterable: impl IntoIterator<Item = T>) -> &[T] {
        let iter = iterable.into_iter();

        let size_hint = iter.size_hint();

        match size_hint {
            (0, None | Some(0)) => &mut [],
            (lower, None) => self.write_from_iter(iter, lower),
            (_, Some(higher)) => self.write_from_iter(iter, higher),
        }
    }

    #[inline]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc<T>(&self, val: T) -> &T {
        unsafe {
            let ptr = self.alloc_raw(Layout::new::<T>()).cast::<T>();
            ptr.write(val);

            &mut *ptr
        }
    }

    #[inline]
    pub fn alloc_string(&self, s: &str) -> &str {
        let string = self.alloc_from_iter(s.bytes());
        let ret = unsafe { core::str::from_utf8_unchecked(string) };
        debug_assert!(s == ret);
        ret
    }

    fn alloc_raw(&self, layout: Layout) -> *mut u8 {
        assert!(layout.size() != 0, "ZST alloc!");

        loop {
            let start = self.start.get().addr();
            let current_end = self.end.get();

            let bytes = layout.size();

            if let Some(subbed) = current_end.addr().checked_sub(bytes) {
                let new_end = align_down(subbed, layout.align());

                if start <= new_end {
                    let aligned_end = current_end.with_addr(new_end);
                    self.end.set(aligned_end);
                    return aligned_end;
                }
            }

            self.grow(layout);
        }
    }

    #[allow(clippy::mut_from_ref)]
    fn write_from_iter<T>(&self, iter: impl Iterator<Item = T>, bound: usize) -> &mut [T] {
        let alloc = self
            .alloc_raw(Layout::array::<T>(bound).unwrap())
            .cast::<T>();

        let mut len = 0;

        for (ix, item) in iter.enumerate() {
            unsafe {
                len = ix;
                alloc.add(ix).write(item);
            }
        }

        unsafe { core::slice::from_raw_parts_mut(alloc, len + 1) }
    }

    #[cold]
    fn grow(&self, layout: Layout) {
        let chunk = if layout.size() <= CHUNK_SIZE {
            Chunk::new()
        } else {
            Chunk::new_big_chunk()
        };

        self.start.set(chunk.start());

        let end = chunk.end().map_addr(|x| align_down(x, align_of::<usize>()));
        self.end.set(end);

        self.chunks.borrow_mut().push(chunk);
    }
}

#[inline(always)]
const fn align_down(addr: usize, align: usize) -> usize {
    addr & (!(align - 1))
}

// fn align_up(addr: usize, align: usize) -> usize {
//     (addr + align - 1) & !(align - 1)
// }

#[cfg(test)]
mod tests {
    use super::Arena;

    #[test]
    fn small_iter() {
        let arena = Arena::new();

        arena.alloc_from_iter(std::iter::repeat_n(64_u8, 500));
    }

    #[test]
    fn small() {
        let arena = Arena::new();

        arena.alloc([0u8; 1564]);
    }
    #[test]
    fn big_iter() {
        let arena = Arena::new();

        arena.alloc_from_iter(std::iter::repeat_n(64_u32, 500_000));
    }

    #[test]
    fn big() {
        let arena = Arena::new();

        #[allow(clippy::large_stack_arrays)]
        arena.alloc([0u8; 1_564_123]);
    }

    #[test]
    fn string() {
        let arena = Arena::new();

        let string = arena.alloc_string(":3 :3 :3 :3");

        assert!(string == ":3 :3 :3 :3");
    }
}
