use std::collections::HashMap;

use crate::RootType;

use crate::bytecode::{BytecodeError, Parser};
use crate::call_stack::{CallStack, Frame, LocalId};
use crate::gc::Heap;
use crate::globals::Globals;
use crate::instruction::{Instr, Instructions};
use crate::objects::{FnRef, Functions, Objects, Value};
use crate::stack::Stack;

const LOCAL_VARS_PER_FRAME: usize = 255;
const MAX_STACK_SIZE: usize = 64;

pub type Operand = u32;
pub type Result<T, E = VmRuntimeError> = core::result::Result<T, E>;
type RootStack =
    Heap<RootType![Gc, Stack<MAX_STACK_SIZE, Value<'__gc>>], RootType![Gc, Globals<'__gc>]>;

pub enum VmRuntimeError {
    StackTooLow,
    StackOverflow,

    VariableNotFound(u64),
    TooMuchLocalVariables,
    LocalVariableMissing(LocalId),

    MissingFn(FnRef),
    Bytecode(BytecodeError),
}

impl core::fmt::Display for VmRuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use VmRuntimeError::{
            Bytecode, LocalVariableMissing, MissingFn, StackOverflow, StackTooLow,
            TooMuchLocalVariables, VariableNotFound,
        };

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
                "attempted to access a local variable at index: #{} which was not found",
                idx.0
            ),
            MissingFn(idx) => write!(
                f,
                "this executable has no main function (at index {})",
                idx.0
            ),

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
    stack: RootStack,

    /// Stream of pre-compiled instructions
    instructions: Instructions,

    /// Flags
    cmp_flags: VmFlags,

    /// Functions
    fns: Functions,

    /// Call stack
    call_stack: CallStack,

    /// Any allocated object
    objects: Objects,
}

impl Vm {
    pub fn new(code: &[u8]) -> Result<Self> {
        let mut parser = Parser::new(code);
        let (instructions, fns) = parser.compile_bytecode().unwrap();

        let mut vm = Self {
            stack: Heap::new_extra(|_period| Stack::new(), |_| Globals::new()),
            instructions,
            fns,

            cmp_flags: VmFlags {
                equal: false,
                greater: false,
                lesser: false,
            },

            call_stack: CallStack::new(),
            objects: Objects::new(),
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

    #[cfg(debug_assertions)]
    fn debug_report<A>(&mut self, opcode: A, show_stack: bool)
    where
        A: Into<Option<Instr>>,
    {
        let (stack_ptr, free) = self
            .stack
            .enter(|_, stack, _| (stack.stack_pointer(), stack.free()));

        match opcode.into() {
            None => {
                println!(
                    "[vm] start | stack ptr: {} | instr ptr: {} | stack left: {} |",
                    stack_ptr,
                    self.instructions.ip().0,
                    free
                );
            }

            Some(op) => {
                println!(
                    "[vm] (instruction: {op:?}) | stack ptr: {} | instr ptr: {} | stack left: {} |",
                    stack_ptr,
                    self.instructions.ip().0,
                    free
                );
            }
        }
        println!(
            "[vm] flags: eq: {}, gt: {}, le: {}",
            self.cmp_flags.equal, self.cmp_flags.greater, self.cmp_flags.lesser
        );

        let mut pointer = String::from("[\n");

        self.stack.enter(|_, stack, _| {
            for (ix, val) in stack.buffer().iter().enumerate() {
                use std::fmt::Write;
                write!(&mut pointer, "{val:>6?}").unwrap();

                if ix == stack.stack_pointer() {
                    pointer.push_str(" <--- STACK POINTER\n");
                } else {
                    pointer.push('\n');
                }
            }
        });

        pointer.push_str("]\n");

        println!("call stack: {:?}", &self.call_stack);

        if show_stack {
            println!("stack after instruction: {pointer}");
        }
    }

    #[allow(clippy::too_many_lines)]
    fn interpret_one(&mut self) -> Result<bool, VmRuntimeError> {
        use Instr::{
            Add, AllocLocal, Call, Cmp, ConstUint32, Div, Dup, End, Jump, JumpIfEq, JumpIfGr,
            JumpIfLe, Load, Mul, Return, Store, Sub,
        };

        let mut vm_continue = true;
        let Some(op) = self.instructions.next() else {
            return Ok(false);
        };

        match op {
            Add => self.stack.enter_mut(|_, stack, _| {
                let lhs = stack.pop()?;
                let rhs = stack.pop()?;

                let val = Vm::math(|x, y| x + y, lhs, rhs);

                stack.push(val)
            })?,

            Sub => self.stack.enter_mut(|_, stack, _| {
                let lhs = stack.pop()?;
                let rhs = stack.pop()?;

                let val = Vm::math(|x, y| x + y, lhs, rhs);

                stack.push(val)
            })?,

            Mul => self.stack.enter_mut(|_, stack, _| {
                let lhs = stack.pop()?;
                let rhs = stack.pop()?;

                let val = Vm::math(|x, y| x * y, lhs, rhs);

                stack.push(val)
            })?,

            Div => self.stack.enter_mut(|_, stack, _| {
                let lhs = stack.pop()?;
                let rhs = stack.pop()?;

                let val = Vm::math(|x, y| x / y, lhs, rhs);

                stack.push(val)
            })?,

            ConstUint32(item) => self
                .stack
                .enter_mut(|_, stack, _| stack.push(Value::Number(item)))?,

            Cmp => {
                // let lhs = self.stack.pop()?;
                // let rhs = self.stack.pop()?;

                // match rhs.cmp(&lhs) {
                //     Ordering::Less => self.cmp_flags.lesser = true,
                //     Ordering::Greater => self.cmp_flags.greater = true,
                //     Ordering::Equal => self.cmp_flags.equal = true,
                // }
                todo!();
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
                fn load(
                    callstack: &mut CallStack,
                    stack: &mut RootStack,
                    local_id: LocalId,
                ) -> Result<(), VmRuntimeError> {
                    stack.enter_mut(|_, stack, _| {
                        if let Some(val) = callstack
                            .current_frame_mut_assert()
                            .load_local(local_id, stack)
                        {
                            stack.push(val).map_err(Into::into)
                        } else {
                            Err(VmRuntimeError::LocalVariableMissing(local_id))
                        }
                    })
                }

                load(&mut self.call_stack, &mut self.stack, local_id)?;
            }

            Store(local_id) => {
                let frame = self.call_stack.current_frame_mut_assert();

                self.stack.enter_mut(|_, stack, _| {
                    let new_value = stack.pop().map_err(Into::<VmRuntimeError>::into)?;

                    let output = frame.store_local(local_id, stack, new_value);

                    if !output {
                        return Err(VmRuntimeError::LocalVariableMissing(
                            LocalId::LOCAL_ID_FN_MAIN,
                        )); // todo
                    }

                    Ok(())
                })?;
            }

            AllocLocal => {
                fn alloc_local<const N: usize>(
                    stack: &mut Stack<N, Value>,
                    frame: &mut Frame,
                ) -> bool {
                    frame.allocate_local(stack)
                }

                self.stack.enter_mut(|_, stack, _| {
                    if !alloc_local(stack, self.call_stack.current_frame_mut_assert()) {
                        todo!("couldn't allocate a local variable!") // todo?
                    }
                });
            }

            Dup => {
                self.stack.enter_mut(|_, stack, _| stack.duplicate())?;
            }

            End => vm_continue = false,
        }

        #[cfg(debug_assertions)]
        self.debug_report(op, true);

        Ok(vm_continue)
    }

    fn interpret_all(&mut self) -> Result<()> {
        #[cfg(debug_assertions)]
        self.debug_report(None, false);

        while self.interpret_one()? {}

        Ok(())
    }

    fn math<'a, F>(op: F, lhs: Value<'a>, rhs: Value<'a>) -> Value<'a>
    where
        F: FnOnce(u32, u32) -> u32,
    {
        match (lhs, rhs) {
            (Value::Number(x), Value::Number(y)) => Value::Number(op(x, y)),

            _ => todo!(),
        }
    }

    fn call_instruction(&mut self, fnref: FnRef) -> Result<()> {
        let Some(function) = self.fns.get(fnref) else {
            let err = VmRuntimeError::MissingFn(fnref);
            return Err(err);
        };

        self.call_stack.new_frame(fnref, self.instructions.ip())?;

        self.instructions.jump(function.jump_ip());
        Ok(())
    }
}
