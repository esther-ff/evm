const PAGE_SIZE: usize = 1024 * 32;

use std::alloc::{self, Layout, dealloc};
use std::cell::{Cell, RefCell};
use std::marker::PhantomData;
use std::ops::{Drop, Index, IndexMut};

#[derive(Debug)]
struct Page {
    original_ptr: *const u8,
}

impl Page {
    fn new() -> Page {
        let layout = Layout::array::<u8>(PAGE_SIZE).expect("infallible");

        unsafe {
            let ptr = alloc::alloc(layout);

            if ptr.is_null() {
                alloc::handle_alloc_error(layout)
            }

            Self { original_ptr: ptr }
        }
    }
}

impl Drop for Page {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::array::<u8>(PAGE_SIZE).expect("infallible");
            dealloc(self.original_ptr.cast_mut(), layout);
        }
    }
}

#[derive(Debug)]
pub struct Arena {
    upper: Cell<*const u8>,
    current: Cell<*const u8>,
    lower: Cell<*const u8>,

    pages: RefCell<Vec<Page>>,
}

impl Arena {
    pub fn new() -> Arena {
        let page = Page::new();

        let upper = page.original_ptr.wrapping_add(PAGE_SIZE);
        let low = page.original_ptr;
        Self {
            pages: RefCell::new(vec![page]),
            upper: Cell::new(upper),
            current: Cell::new(upper),

            lower: Cell::new(low),
        }
    }

    pub fn alloc<T>(&self, data: T) -> &T {
        let ptr = self.alloc_raw(Layout::new::<T>()).cast::<T>();

        unsafe {
            std::ptr::write(ptr, data);
            &*(ptr)
        }
    }

    pub fn alloc_slice<A, B>(&self, arr: &A) -> &[B]
    where
        A: AsRef<[B]> + ?Sized,
        B: Copy,
    {
        let target = arr.as_ref();

        let ptr =
            self.alloc_raw(Layout::array::<B>(target.len()).expect("invalid layout")) as *mut B;
        let saved = ptr;

        unsafe {
            std::ptr::copy_nonoverlapping(target.as_ptr(), ptr, target.len());

            std::slice::from_raw_parts(saved, target.len())
        }
    }

    pub fn alloc_string(&self, val: &str) -> &str {
        let slice = self.alloc_slice(val);

        unsafe { std::str::from_utf8_unchecked(slice) }
    }

    fn new_page(&self) {
        let page = Page::new();

        let upper = page.original_ptr.wrapping_add(PAGE_SIZE);
        let low = page.original_ptr;

        self.upper.replace(upper);
        self.lower.replace(low);
        self.current.replace(upper);

        self.pages.borrow_mut().push(page);
    }

    fn alloc_raw(&self, layout: Layout) -> *mut u8 {
        assert!(PAGE_SIZE > layout.size());
        if self.current.get() as usize - layout.size() < self.lower.get() as usize {
            // we need a new page
            self.new_page();
        }

        let current_ptr = self.current.get();
        let new = current_ptr.wrapping_sub(layout.size());

        self.current.replace(new);

        let new_ptr = new.with_addr(new as usize & (!(layout.align() - 1)));
        new_ptr.cast_mut()
    }
}

pub struct TypedArena<T, I: Id> {
    chunks: Vec<Chunk<T>>,
    chunk_pos: usize,

    _marker: PhantomData<I>,
}

const CHUNK_SIZE: usize = 128;

pub struct Chunk<T> {
    inner: Vec<T>,
}

impl<T> Chunk<T> {
    pub fn new() -> Self {
        Self {
            inner: Vec::with_capacity(CHUNK_SIZE),
        }
    }

    pub fn alloc(&mut self, item: T) -> Result<(), T> {
        if self.inner.len() == CHUNK_SIZE - 1 {
            return Err(item);
        }

        self.inner.push(item);

        Ok(())
    }
}

pub trait Id {
    fn get_inside_chunk_index(&self) -> usize;
    fn get_arena_chunk_index(&self) -> usize;
    fn new(chunk_index: usize, vec_index: usize) -> Self;
}

impl<T, I: Id> TypedArena<T, I> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
            chunks: vec![Chunk::new()],
            chunk_pos: 0,
        }
    }

    pub fn alloc(&mut self, item: T) -> I {
        let current_chunk = self.get_current_chunk();
        match current_chunk.alloc(item) {
            Ok(()) => {
                let chunk_index = current_chunk.inner.len() - 1;
                let current_pos = self.chunks.len();

                I::new(chunk_index, current_pos)
            }

            Err(item) => {
                let mut new_chunk = Chunk::new();
                let res = new_chunk.alloc(item);
                debug_assert!(res.is_ok());

                let chunk_index = 0;
                let current_pos = self.chunks.len() + 1;

                self.chunks.push(new_chunk);

                I::new(chunk_index, current_pos)
            }
        }
    }

    pub fn get(&self, id: I) -> Option<&T> {
        let chunk_pos = id.get_arena_chunk_index();
        let vec_pos = id.get_inside_chunk_index();

        self.chunks
            .get(chunk_pos)
            .and_then(|chunk| chunk.inner.get(vec_pos))
    }

    pub fn get_mut(&mut self, id: I) -> Option<&mut T> {
        let chunk_pos = id.get_arena_chunk_index();
        let vec_pos = id.get_inside_chunk_index();

        self.chunks
            .get_mut(chunk_pos)
            .and_then(|chunk| chunk.inner.get_mut(vec_pos))
    }

    fn get_current_chunk(&mut self) -> &mut Chunk<T> {
        &mut self.chunks[self.chunk_pos]
    }
}

impl<T, I: Id> Index<I> for TypedArena<T, I> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        let chunk_index = index.get_arena_chunk_index();
        let chunk_inside_ix = index.get_inside_chunk_index();

        match self.get(index) {
            Some(val) => val,

            None => {
                panic!(
                    "item not found at chunk {chunk_index}, at pos {chunk_inside_ix} while indexing arena",
                )
            }
        }
    }
}

impl<T, I: Id> IndexMut<I> for TypedArena<T, I> {
    fn index_mut(&mut self, index: I) -> &mut T {
        let chunk_index = index.get_arena_chunk_index();
        let chunk_inside_ix = index.get_inside_chunk_index();

        match self.get_mut(index) {
            Some(val) => val,

            None => {
                panic!(
                    "item not found at chunk {chunk_index}, at pos {chunk_inside_ix} while indexing arena",
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::arena::Arena;

    #[test]
    fn single_alloc() {
        let value = 42;

        let arena = Arena::new();

        dbg!(&arena);

        let reff = arena.alloc(value);

        dbg!(reff);
    }

    #[test]
    fn slice_alloc() {
        let value = [42, 21, 32, 411, 4];

        let arena = Arena::new();

        dbg!(&arena);

        let _reff = arena.alloc_slice(&value);
    }

    #[test]
    fn slice_str() {
        let value = "our children will hold their fists high";
        let value1 = "meow woof wrff awrff :3";

        dbg!(value.len());
        dbg!(value1.len());
        let arena = Arena::new();

        dbg!(arena.upper.get() as usize);

        let _reff = arena.alloc_string(value);
        let _reff1 = arena.alloc_string(value1);

        dbg!(_reff);

        dbg!(_reff.as_ptr() as usize);
        dbg!(_reff1.as_ptr() as usize);

        dbg!(_reff1);

        dbg!(_reff);
    }
    #[test]
    fn big_alloc() {
        let value = [2u8; 31000];

        let arena = Arena::new();

        dbg!(&arena);

        let _reff = arena.alloc_slice(&value);

        let _reff1 = arena.alloc_slice(&value);
    }
}
