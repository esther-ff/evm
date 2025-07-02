use super::objects::Value;

type Result<T, E = StackError> = core::result::Result<T, E>;

enum StackError {
    StackOverflow,
    StackUnderflow,
}

pub(crate) struct Stack<const SIZE: usize> {
    pointer: usize,
    buf: [Value; SIZE],
}

impl<const SIZE: usize> Stack<SIZE> {
    pub(crate) fn new() -> Self {
        Self {
            buf: [Value::Nil; SIZE],
            pointer: 0,
        }
    }

    pub(crate) fn push(&mut self, item: Value) -> Result<()> {
        if self.pointer == SIZE {
            return Err(StackError::StackUnderflow);
        }

        self.buf[self.pointer] = item;
        self.pointer += 1;

        Ok(())
    }

    pub(crate) fn pop(&mut self) -> Result<Value> {
        if self.pointer == 0 {
            return Err(StackError::StackUnderflow);
        }

        let val = self.buf[self.pointer];
        self.pointer -= 1;

        Ok(val)
    }
}
