#![warn(clippy::pedantic)]
use std::collections::HashMap;

use crate::bytecode::{BytecodeCompiler, BytecodeError};
use crate::call_stack::{CallStack, Frame};
use crate::instruction::{Instr, Instructions};
use crate::objects::{FnRef, Functions, Objects, Value};
use crate::stack::Stack;

const LOCAL_VARS_PER_FRAME: usize = 255;
const MAX_STACK_SIZE: usize = 64;

pub type Operand = u32;
pub type Result<T, E = VmRuntimeError> = core::result::Result<T, E>;

#[derive(Debug)]
pub enum VmRuntimeError {
    StackTooLow,
    StackOverflow,

    VariableNotFound(u64),
    TooMuchLocalVariables,
    LocalVariableMissing(usize),

    MissingFn(u64),
    Bytecode(BytecodeError),
}

impl core::fmt::Display for VmRuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use VmRuntimeError::*;

        match self {
            StackTooLow => write!(
                f,
                "the stack wasn't occupied enough to execute this operation"
            ),
            StackOverflow => write!(f, "the machine overflowed it's stack"),
            VariableNotFound(idx) => write!(f, "global variable at index: @{idx} was not found"),
            TooMuchLocalVariables => write!(
                f,
                "the amount of local variables exceeded {LOCAL_VARS_PER_FRAME}"
            ),
            LocalVariableMissing(idx) => write!(
                f,
                "attempted to access a local variable at index: #{idx} which was not found"
            ),
            MissingFn(idx) => write!(f, "this executable has no main function (at index {idx})"),

            Bytecode(err) => err.fmt(f),
        }
    }
}

struct VmFlags {
    equal: bool,
    greater: bool,
    lesser: bool,
}

impl VmFlags {
    fn consume_eq(&mut self) -> bool {
        let old = self.equal;
        self.equal = false;
        old
    }

    fn consume_le(&mut self) -> bool {
        let old = self.lesser;
        self.lesser = false;
        old
    }

    fn consume_gr(&mut self) -> bool {
        let old = self.greater;
        self.greater = false;
        old
    }
}

struct Variable {
    content: Box<[u8]>,
    var_size: usize,
}

impl Variable {
    fn test_variable() -> Self {
        Self {
            content: Box::new([255, 255, 255, 255]),
            var_size: 4,
        }
    }

    fn new(val: &[u8]) -> Self {
        Self {
            content: val.to_vec().into_boxed_slice(),
            var_size: val.len(),
        }
    }

    fn write_to(&mut self, bytes: &[u8]) {
        self.content.copy_from_slice(bytes);
    }
}

struct Variables {
    map: HashMap<u64, Variable>,
    size: usize,
}

impl Variables {
    fn new<A>(extra: A) -> Self
    where
        A: Into<Option<Vec<Variable>>>,
    {
        Self {
            map: match extra.into() {
                None => HashMap::with_capacity(64),
                Some(vec) => vec
                    .into_iter()
                    .enumerate()
                    .map(|(key, value)| (key as u64, value))
                    .collect::<HashMap<u64, Variable>>(),
            },
            size: 0,
        }
    }

    fn push(&mut self, id: u64, var: Variable) {
        self.map.insert(id, var);
    }

    fn is_here(&self, id: u64) -> bool {
        self.map.contains_key(&id)
    }

    fn get(&self, id: u64) -> Result<&Variable> {
        if let Some(v) = self.map.get(&id) {
            Ok(v)
        } else {
            Err(VmRuntimeError::VariableNotFound(id))
        }
    }

    fn get_mut(&mut self, id: u64) -> Result<&mut Variable> {
        if let Some(v) = self.map.get_mut(&id) {
            Ok(v)
        } else {
            Err(VmRuntimeError::VariableNotFound(id))
        }
    }
}

pub struct Vm {
    /// Main VM stack
    stack: Stack<MAX_STACK_SIZE, Value>,

    /// Stream of pre-compiled instructions
    instructions: Instructions,

    /// Flags
    cmp_flags: VmFlags,

    /// Global variables
    variables: Variables,

    /// Functions
    fns: Functions,

    /// Call stack
    call_stack: CallStack,

    /// Any allocated object
    objects: Objects,
}

impl Vm {
    pub fn new(code: &[u8]) -> Result<Self> {
        let mut parser = BytecodeCompiler::new(code);
        let (objects, instructions, fns) = parser.read_evm_bytecode().unwrap();

        let mut vm = Self {
            stack: Stack::new(),
            instructions,
            fns,

            cmp_flags: VmFlags {
                equal: false,
                greater: false,
                lesser: false,
            },

            variables: Variables::new(vec![Variable::test_variable()]),
            call_stack: CallStack::new(),
            objects,
        };

        vm.call_instruction(FnRef::MAIN_FN)?;

        Ok(vm)
    }

    fn current_frame(&self) -> &Frame {
        let Some(frame) = self.call_stack.current_frame() else {
            unreachable!("there should be atleast the frame present for the `main` function");
        };

        frame
    }

    fn current_frame_mut(&mut self) -> &mut Frame {
        let Some(frame) = self.call_stack.current_frame_mut() else {
            unreachable!("there should be atleast the frame present for the `main` function");
        };

        frame
    }

    fn debug_report<A>(&self, opcode: A, show_stack: bool)
    where
        A: Into<Option<Instr>>,
    {
        let op = opcode.into();
        #[cfg(debug_assertions)]
        println!(
            "[vm] (instruction: {op:?}) | stack ptr: {} | instr ptr: {} | stack left: {} |",
            self.stack.stack_pointer(),
            self.instructions.ip().0,
            self.stack.free()
        );
        println!(
            "[vm] flags: eq: {}, gt: {}, le: {}",
            self.cmp_flags.equal, self.cmp_flags.greater, self.cmp_flags.lesser
        );

        let mut pointer = String::from("[\n");

        for (ix, val) in self.stack.buffer().iter().enumerate() {
            use std::fmt::Write;
            write!(&mut pointer, "{val:>6?}").unwrap();

            if ix == self.stack.stack_pointer() {
                pointer.push_str(" <--- STACK POINTER\n");
            } else {
                pointer.push('\n');
            }
        }

        pointer.push_str("]\n");

        println!("call stack: {:?}", &self.call_stack);

        if show_stack {
            println!("stack after instruction: {pointer}");
        }
    }

    fn interpret_one(&mut self) -> Result<bool, VmRuntimeError> {
        use Instr::*;

        let mut vm_continue = true;
        let Some(op) = self.instructions.next() else {
            return Ok(false);
        };

        match op {
            Add => self.math(|x, y| x + y)?,

            Sub => self.math(|x, y| x - y)?,

            Mul => self.math(|x, y| x * y)?,

            Div => self.math(|x, y| x / y)?,

            Push(item) => self.stack.push(Value::Number(item))?,

            CmpVal => {
                // let lhs = self.stack.pop()?;
                // let rhs = self.stack.pop()?;

                // match rhs.cmp(&lhs) {
                //     Ordering::Less => self.cmp_flags.lesser = true,
                //     Ordering::Greater => self.cmp_flags.greater = true,
                //     Ordering::Equal => self.cmp_flags.equal = true,
                // }
                todo!();
            }

            CmpObj => {
                panic!("to be removed");
            }

            Jump(ip) => {
                self.instructions.jump(ip);
            }

            JumpIfEq(ip) => {
                if self.cmp_flags.consume_eq() {
                    self.instructions.jump(ip);
                }
            }

            JumpIfGr(ip) => {
                if self.cmp_flags.consume_gr() {
                    self.instructions.jump(ip);
                }
            }

            JumpIfLe(ip) => {
                if self.cmp_flags.consume_le() {
                    self.instructions.jump(ip);
                }
            }

            Call(function) => self.call_instruction(function)?,

            Return => {
                let program_counter = self.current_frame().return_address();

                self.instructions.jump(program_counter);
            }

            Load(local_id) => {
                let Some(local) = self.current_frame().load_local(local_id, &self.stack) else {
                    return Err(VmRuntimeError::LocalVariableMissing(0)); // todo
                };

                self.stack.push(local)?;
            }

            Store(local_id) => {
                fn store<const N: usize>(
                    stack: &mut Stack<N, Value>,
                    frame: &mut Frame,
                    new_value: Value,
                    local_id: crate::call_stack::LocalId,
                ) -> bool {
                    frame.store_local(local_id, stack, new_value)
                }

                let new_value = self.stack.pop()?;

                if !store(
                    &mut self.stack,
                    self.call_stack.current_frame_mut().expect(
                        "infallible: function `main` should have established a frame already",
                    ),
                    new_value,
                    local_id,
                ) {
                    return Err(VmRuntimeError::LocalVariableMissing(0)); // todo
                }
            }

            AllocLocal => {
                fn alloc_local<const N: usize>(
                    stack: &mut Stack<N, Value>,
                    frame: &mut Frame,
                ) -> bool {
                    frame.allocate_local(stack)
                }

                if !alloc_local(
                    &mut self.stack,
                    self.call_stack.current_frame_mut().expect(
                        "infallible: function `main` should have established a frame already",
                    ),
                ) {
                    panic!("couldn't allocate a local variable!") // todo?
                }
            }

            Dup => {
                self.stack.duplicate()?;
            }

            End => vm_continue = false,
        }

        self.debug_report(op, true);

        Ok(vm_continue)
    }

    fn interpret_all(&mut self) -> Result<()> {
        self.debug_report(None, false);
        while self.interpret_one()? {}

        Ok(())
    }

    fn math<F>(&mut self, op: F) -> Result<(), VmRuntimeError>
    where
        F: FnOnce(u32, u32) -> u32,
    {
        let lhs = self.stack.pop()?;
        let rhs = self.stack.pop()?;

        let val = match (lhs, rhs) {
            (Value::Number(x), Value::Number(y)) => Value::Number(op(x, y)),

            _ => todo!(),
        };

        self.stack.push(val)?;

        Ok(())
    }

    fn call_instruction(&mut self, fn_idx: FnRef) -> Result<()> {
        let Some(function) = self.fns.get(fn_idx) else {
            let err = VmRuntimeError::MissingFn(fn_idx.0.into());
            return Err(err);
        };

        self.call_stack.new_frame(fn_idx, self.instructions.ip())?;

        self.instructions.jump(function.jump_ip());
        Ok(())
    }
}
