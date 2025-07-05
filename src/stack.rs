use std::fmt::Debug;
use std::mem::MaybeUninit;

use crate::objects::Value;
use crate::vm::VmRuntimeError;

type Result<T, E = StackError> = core::result::Result<T, E>;

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
        write!(f, "Stack: \n")?;
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

impl<const SIZE: usize> Stack<SIZE, Value> {
    /// Duplicate a value
    pub fn duplicate(&mut self) -> Result<()> {
        if self.pointer == SIZE {
            return Err(StackError::StackOverflow);
        }

        let val = unsafe { self.buf[self.pointer].assume_init() };
        self.push(val)
    }
}
