use crate::RootType;
use crate::bytecode::{BytecodeError, Parser};
use crate::call_stack::{CallStack, Frame, LocalId};
use crate::gc::Heap;
use crate::globals::Globals;
use crate::instruction::{Instr, Instructions};
use crate::objects::{FnRef, Functions, Objects, Value};
use crate::stack::Stack;
use crate::vm_math::{MathError, f32_math, f64_math, u32_math, u64_math};

const LOCAL_VARS_PER_FRAME: usize = 255;
pub const MAX_STACK_SIZE: usize = 64;

/// `$op_type`: primitive type to use for this
/// `$op_function`: function for the operation in the stdlib
/// `$math_error_expr`: closure returning an error
/// `$push_function`: function to push the value onto the stack
/// `$math_function`: function to do the math using the stack
/// `$stack`: identifier of the stack
macro_rules! vm_math {
    ($op_function:expr, $math_error_expr:expr, $push_function:ident, $math_function:ident, $stack:expr, $error_check:expr) => {
        match $stack.enter_mut(|_, stack, _| {
            let output = $math_function(stack, $op_function, $math_error_expr).map_err(|x| x)?;
            stack.$push_function(output).map_err(Into::into)
        }) {
            Ok(_) => return Ok(false),

            Err(err) => {
                if ($error_check)(err) {
                    todo!("handle overflows")
                }

                todo!();
            }
        }
    };
}
pub type Operand = u32;
pub type Result<T, E = VmRuntimeError> = core::result::Result<T, E>;
type RootStack =
    Heap<RootType![Gc, Stack<MAX_STACK_SIZE, Value<'__gc>>], RootType![Gc, Globals<'__gc>]>;

#[derive(Debug)]
pub enum VmRuntimeError {
    StackTooLow,
    StackOverflow,

    VariableNotFound(u64),
    TooMuchLocalVariables,
    LocalVariableMissing(LocalId),

    MissingFn(FnRef),
    Bytecode(BytecodeError),

    Math(MathError),
}

impl core::fmt::Display for VmRuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use VmRuntimeError::{
            Bytecode, LocalVariableMissing, Math, MissingFn, StackOverflow, StackTooLow,
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

            Math(err) => err.fmt(f),
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

pub struct Vm {
    /// Main VM stack
    /// contains global variables
    /// and the actual stack.
    ///
    /// This is due to GC requirements.
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
        let parser = Parser::new(code);
        let (instructions, fns) = parser.compile_bytecode()?;

        let mut vm = Self {
            stack: Heap::new_extra(|_| Stack::new(), |_| Globals::new()),
            fns,
            instructions,
            call_stack: CallStack::new(),
            objects: Objects::new(),
            cmp_flags: VmFlags {
                equal: false,
                greater: false,
                lesser: false,
            },
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
        #[allow(clippy::enum_glob_use)]
        use Instr::*;

        let mut vm_continue = true;
        let Some(op) = self.instructions.next() else {
            return Ok(false);
        };

        match op {
            IAdd => {
                vm_math!(
                    u32::checked_add,
                    || MathError::Overflow,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }
            ISub => {
                vm_math!(
                    u32::checked_sub,
                    || MathError::Underflow,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_underflow()
                );
            }
            IMul => {
                vm_math!(
                    u32::checked_mul,
                    || MathError::Overflow,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }
            IDiv => {
                vm_math!(
                    u32::checked_div_euclid,
                    || MathError::DivisionByZero,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_div_by_zero()
                );
            }
            IShl => {
                vm_math!(
                    u32::checked_shl,
                    || MathError::Overflow,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            IShr => {
                vm_math!(
                    u32::checked_shr,
                    || MathError::DivisionByZero,
                    push_u32,
                    u32_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            LAdd => {
                vm_math!(
                    u64::checked_add,
                    || MathError::Overflow,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            LSub => {
                vm_math!(
                    u64::checked_sub,
                    || MathError::Underflow,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_underflow()
                );
            }

            LMul => {
                vm_math!(
                    u64::checked_mul,
                    || MathError::Overflow,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            LDiv => {
                vm_math!(
                    u64::checked_div_euclid,
                    || MathError::DivisionByZero,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_div_by_zero()
                );
            }

            LShl => {
                vm_math!(
                    |lhs, rhs| u64::checked_shl(lhs, rhs as u32),
                    || MathError::Overflow,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            LShr => {
                vm_math!(
                    |lhs, rhs| u64::checked_shr(lhs, rhs as u32),
                    || MathError::DivisionByZero,
                    push_u64,
                    u64_math,
                    self.stack,
                    |ret: MathError| ret.is_overflow()
                );
            }

            FAdd => {
                vm_math!(
                    |x, y| Some(x + y),
                    || MathError::Overflow,
                    push_f32,
                    f32_math,
                    self.stack,
                    |_: MathError| false
                );
            }
            FSub => {
                vm_math!(
                    |x, y| Some(x - y),
                    || MathError::Underflow,
                    push_f32,
                    f32_math,
                    self.stack,
                    |_: MathError| false
                );
            }
            FMul => {
                vm_math!(
                    |x, y| Some(x * y),
                    || MathError::Overflow,
                    push_f32,
                    f32_math,
                    self.stack,
                    |_: MathError| false
                );
            }
            FDiv => {
                vm_math!(
                    |x, y| Some(x / y),
                    || MathError::DivisionByZero,
                    push_f32,
                    f32_math,
                    self.stack,
                    |_: MathError| false
                );
            }

            DAdd => {
                vm_math!(
                    |x, y| Some(x + y),
                    || unreachable!(),
                    push_f64,
                    f64_math,
                    self.stack,
                    |_: MathError| false
                );
            }

            DSub => {
                vm_math!(
                    |x, y| Some(x - y),
                    || unreachable!(),
                    push_f64,
                    f64_math,
                    self.stack,
                    |_: MathError| false
                );
            }

            DMul => {
                vm_math!(
                    |x, y| Some(x * y),
                    || unreachable!(),
                    push_f64,
                    f64_math,
                    self.stack,
                    |_: MathError| false
                );
            }

            DDiv => {
                vm_math!(
                    |x, y| Some(x / y),
                    || unreachable!(),
                    push_f64,
                    f64_math,
                    self.stack,
                    |_: MathError| false
                );
            }

            IConst(item) => self.stack.enter_mut(|_, stack, _| stack.push_u32(item))?,
            LConst(item) => self.stack.enter_mut(|_, stack, _| stack.push_u64(item))?,
            FConst(item) => self.stack.enter_mut(|_, stack, _| stack.push_f32(item))?,
            DConst(item) => self.stack.enter_mut(|_, stack, _| stack.push_f64(item))?,

            Cmp => {
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

            NativeCall => todo!("nativecall"),
            New(instance) => todo!("instances: {instance:?}"),
            NewArray(ty) => todo!("arrays of {ty:?}"),
            Invoke => todo!("invoking instance methods"),

            Pop => self
                .stack
                .enter_mut(|_, stack, _| stack.pop().map(|_| ()))?,

            Throw => todo!("throws"),
            Catch => todo!("catching"),

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

    pub fn interpret_all(&mut self) -> Result<()> {
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

        let sp = self.stack.enter(|_, root, _| root.stack_pointer());

        self.call_stack
            .new_frame(fnref, self.instructions.ip(), sp)?;

        self.instructions.jump(function.jump_ip());
        Ok(())
    }
}
