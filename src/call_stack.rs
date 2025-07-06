use crate::objects::{FnRef, Functions};

use crate::{
    instruction::ProgramCounter,
    objects::Value,
    stack::{self, Stack},
};

const MAX_LOCAL_VARIABLES: usize = 512;
const MAX_CALL_STACK_DEPTH: usize = size_of::<Value>() * 256;

/// inside a stack frame.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct LocalVariable(u32);

impl LocalVariable {
    pub fn new(addr: u32) -> Self {
        Self(addr)
    }

    pub fn load<'a, const N: usize>(self, stack: &Stack<N, Value<'a>>) -> Option<Value<'a>> {
        stack.buffer().get(self.0 as usize).copied()
    }

    pub fn store<'a, const N: usize>(
        self,
        stack: &mut Stack<N, Value<'a>>,
        value: Value<'a>,
    ) -> bool {
        if let Some(old) = stack.buffer_mut().get_mut(self.0 as usize) {
            *old = value;
            return true;
        }

        false
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalId(pub u32);

impl LocalId {
    /// Id for the `main` function.
    pub const LOCAL_ID_FN_MAIN: Self = Self(0);
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Ord, Eq)]
struct LocalVars {
    locals: [LocalVariable; MAX_LOCAL_VARIABLES],
    len: usize,
}

impl LocalVars {
    pub fn push(&mut self, local: LocalVariable) -> bool {
        if self.len == MAX_LOCAL_VARIABLES - 1 {
            return false;
        }

        self.locals[self.len] = local;
        self.len += 1;
        true
    }

    pub fn get(&self, idx: LocalId) -> Option<LocalVariable> {
        self.locals.get(idx.0 as usize).copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct Frame {
    /// Name of the function that started
    /// this call frame
    function: FnRef,

    /// Local variables
    locals: LocalVars,

    /// Instruction pointer before the `Call`
    /// instruction was executed
    previous_ip: ProgramCounter,
}

impl Frame {
    pub fn new(function: FnRef, ip: ProgramCounter) -> Self {
        Self {
            locals: LocalVars {
                locals: [LocalVariable(0); MAX_LOCAL_VARIABLES],
                len: 0,
            },

            function,

            previous_ip: ip,
        }
    }

    pub fn allocate_local<const N: usize>(&mut self, stack: &mut Stack<N, Value>) -> bool {
        #[allow(clippy::cast_possible_truncation)]
        let local = LocalVariable::new(stack.stack_pointer() as u32);
        self.locals.push(local)
    }

    pub fn load_local<'a, const N: usize>(
        &self,
        id: LocalId,
        stack: &Stack<N, Value<'a>>,
    ) -> Option<Value<'a>> {
        self.locals.get(id).and_then(|var| var.load(&stack))
    }

    pub fn store_local<'a, const N: usize>(
        &self,
        id: LocalId,
        stack: &mut Stack<N, Value<'a>>,
        value: Value<'a>,
    ) -> bool {
        if let Some(local) = self.locals.get(id) {
            return local.store(stack, value);
        }

        false
    }

    pub fn name<'a>(&self, functions: &'a Functions) -> &'a str {
        functions
            .get(self.function)
            .expect("function should be present, as it is in the frame's field")
            .name()
    }

    pub fn previous_ip(&self) -> ProgramCounter {
        self.previous_ip
    }

    pub fn return_address(&self) -> ProgramCounter {
        let mut counter = self.previous_ip;

        counter.0 += 1;

        counter
    }
}

#[derive(Debug)]
pub struct CallStack {
    frames: Stack<MAX_CALL_STACK_DEPTH, Frame>,
}

impl CallStack {
    pub fn new() -> Self {
        Self {
            frames: Stack::new(),
        }
    }

    pub fn current_frame(&self) -> Option<&Frame> {
        self.frames.buffer().last()
    }

    pub fn current_frame_mut(&mut self) -> Option<&mut Frame> {
        self.frames.buffer_mut().last_mut()
    }

    pub fn current_frame_assert(&self) -> &Frame {
        self.frames.buffer().last().unwrap_or_else(|| {
            unreachable!("function `main` should have initialized atleast one call frame")
        })
    }

    pub fn current_frame_mut_assert(&mut self) -> &mut Frame {
        self.frames.buffer_mut().last_mut().unwrap_or_else(|| {
            unreachable!("function `main` should have initialized atleast one call frame")
        })
    }

    pub fn new_frame(&mut self, fnref: FnRef, ip: ProgramCounter) -> Result<(), stack::StackError> {
        self.frames.push(Frame::new(fnref, ip))
    }

    pub fn len(&self) -> usize {
        self.frames.stack_pointer()
    }
}
