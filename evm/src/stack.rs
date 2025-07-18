use std::fmt::Debug;
use std::mem::MaybeUninit;

use crate::gc::ToHeap;
use crate::objects::Value;
use crate::vm::VmRuntimeError;

// pub type StackRef<'a, const N: usize> = core::cell::Ref<'a, Stack<N, Value<'a>>>;
// pub type StackRefMut<'a, const N: usize> = core::cell::RefMut<'a, Stack<N, Value<'a>>>;

pub type StackRef<'a, const N: usize> = &'a Stack<N, Value<'a>>;
pub type StackRefMut<'a, const N: usize> = &'a mut Stack<N, Value<'a>>;
type Result<T, E = StackError> = core::result::Result<T, E>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum StackError {
    StackOverflow,
    StackUnderflow,
}

impl From<StackError> for VmRuntimeError {
    fn from(value: StackError) -> Self {
        match value {
            StackError::StackOverflow => VmRuntimeError::StackOverflow,
            StackError::StackUnderflow => VmRuntimeError::StackTooLow,
        }
    }
}

/// A simple stack used as the VM's stack
/// for executing instructions
pub struct Stack<const SIZE: usize, T: Copy> {
    pointer: usize,
    buf: [MaybeUninit<T>; SIZE],
}

impl<const SIZE: usize, T: Debug + Copy> Debug for Stack<SIZE, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.buffer().iter()).finish()
    }
}

impl<const SIZE: usize, T: Copy> Stack<SIZE, T> {
    /// Creates a new stack filled with `SIZE` slots of
    /// `MaybeUninit<T>`
    pub fn new() -> Self {
        Self {
            buf: [const { MaybeUninit::uninit() }; SIZE],
            pointer: 0,
        }
    }

    /// Pushes a value onto the stack
    /// incrementing the stack pointer
    pub fn push(&mut self, item: T) -> Result<()> {
        if self.pointer == SIZE {
            return Err(StackError::StackUnderflow);
        }

        self.buf[self.pointer].write(item);

        self.pointer += 1;

        Ok(())
    }

    /// Pops a value off the stack
    /// decrementing the stack pointer
    pub fn pop(&mut self) -> Result<T> {
        if self.pointer == 0 {
            return Err(StackError::StackUnderflow);
        }

        let val = unsafe { self.buf[self.pointer].assume_init() };
        self.pointer -= 1;

        Ok(val)
    }

    /// Returns the stack pointer
    pub fn stack_pointer(&self) -> usize {
        self.pointer
    }

    /// Returns the amount of unallocated space
    pub fn free(&self) -> usize {
        self.buf.len() - self.pointer
    }

    /// Returns the buffer as an immutable slice
    /// mostly used for debugging
    pub fn buffer(&self) -> &[T] {
        unsafe { &*(&raw const self.buf[..self.pointer] as *const [T]) }
    }

    /// Returns the buffer as an immutable slice
    /// mostly used for debugging
    pub fn buffer_mut(&mut self) -> &mut [T] {
        unsafe { &mut *(&raw mut self.buf[..self.pointer] as *mut [T]) }
    }
}

impl<const SIZE: usize> Stack<SIZE, Value<'_>> {
    /// Duplicate a value
    pub fn duplicate(&mut self) -> Result<()> {
        if self.pointer == SIZE {
            return Err(StackError::StackOverflow);
        }

        let val = unsafe { self.buf[self.pointer].assume_init() };
        self.push(val)
    }

    /// Put a u32 on the stack
    pub fn push_u32(&mut self, val: u32) -> Result<()> {
        self.push(Value::Number(val))
    }

    /// Put a f32 on the stack
    pub fn push_f32(&mut self, val: f32) -> Result<()> {
        let target = val.to_bits();
        self.push(Value::Number(target))
    }
    /// Put a u64 on the stack
    pub fn push_u64(&mut self, val: u64) -> Result<()> {
        let target = val.to_ne_bytes();

        let higher: [u8; 4] = target[0..4].try_into().expect("slice is 4-wide");
        let lower: [u8; 4] = target[4..8].try_into().expect("slice is 4-wide");

        self.push_u32(u32::from_ne_bytes(lower))?;
        self.push_u32(u32::from_ne_bytes(higher))?;

        Ok(())
    }

    /// Put a f64 on the stack
    pub fn push_f64(&mut self, val: f64) -> Result<()> {
        let target = val.to_bits();

        self.push_u64(target)
    }
}

impl<'gc, const SIZE: usize, T: ToHeap<'gc> + Copy> ToHeap<'gc> for Stack<SIZE, T> {
    fn trace<V: crate::gc::Trace<'gc>>(&self, val: &mut V) {
        for item in self.buffer() {
            item.trace(val);
        }
    }
}
