mod alloc;
mod bytecode;
mod instruction;
mod objects;
mod stack;

use objects::Objects;
use std::{array::TryFromSliceError, cmp::Ordering, collections::HashMap};

const MAX_STACK_SIZE: usize = 64;
const NUM_OPERAND_SIZE_BYTES: usize = 8;
const LOCAL_VARS_PER_FRAME: usize = 255;

type Opcode = u8;
type Result<T, E = VmRuntimeError> = core::result::Result<T, E>;

// macro_rules! binop {
//             ($op:tt, $name:ident, $self:ident) => {{
//                 let lhs: u64 = $self.stack.stack_pop_u64()?;
//                 let rhs: u64 = $self.stack.stack_pop_u64()?;

//                 dbg!(lhs, rhs);
//                 let bytes = (lhs $op rhs).to_ne_bytes();

//                 $self.stack.stack_push(&bytes)?;
//             }};
//         }

// macro_rules! store_impl {
//     ($self:ident, $stack_local_store:ident, $stack_pop:ident) => {
//         $self.ip += 1;

//         let old_sp = $self.stack.sp;
//         let value = $self.stack.$stack_pop()?;
//         let Some(idx) = $self.reader.get($self.ip) else {
//             return Err(VmRuntimeError::MissingOperand);
//         };

//         let frames = $self.last_frame();
//         match frames.get_local_addr(idx as usize) {
//             // we've got the local
//             Ok(local_addr) => $self.stack.$stack_local_store(local_addr, value)?,

//             // zoinks.... let's make one OKAY?
//             Err(err) => match err {
//                 VmRuntimeError::LocalVariableMissing(_) => {
//                     frames.push_local(old_sp)?;
//                 }
//                 err => return Err(err),
//             },
//         }
//     };
// }

// macro_rules! load_impl {
//     ($self:ident, $stack_local_load:ident) => {
//         $self.ip += 1;

//         let Some(idx) = $self.reader.get($self.ip) else {
//             return Err(VmRuntimeError::MissingOperand);
//         };

//         let item = $self.last_frame().get_local_addr(idx as usize)?;
//         let resolved = $self.stack.$stack_local_load(item)?;

//         $self.stack.stack_push(&resolved.to_ne_bytes())?;
//     };
// }

macro_rules! jump_impl {
    ($self:ident, $consume_flag:ident) => {
        let ptr: u64 = u64::from_ne_bytes(
            $self
                .stack
                .stack_pop(NUM_OPERAND_SIZE_BYTES)?
                .try_into()
                .unwrap(),
        );

        if $self.cmp_flags.$consume_flag() {
            $self.ip = ptr as usize;
        }
    };
}

#[derive(Debug)]
enum VmRuntimeError {
    StackTooLow,
    StackOverflow,

    VariableNotFound(u64),
    TooMuchLocalVariables,
    LocalVariableMissing(usize),

    MissingFn(u64),
    Bytecode(bytecode::BytecodeError),
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
                Some(vec) => {
                    HashMap::from_iter(vec.into_iter().enumerate().map(|(x, y)| (x as u64, y)))
                }
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

#[derive(Debug)]
struct Stack {
    stack: [u8; MAX_STACK_SIZE],
    sp: usize,
}

impl Stack {
    fn stack_pop_u64(&mut self) -> Result<u64> {
        dbg!(Ok(u64::from_ne_bytes(
            self.stack_pop(8)?
                .try_into()
                .unwrap_or_else(|_| unreachable!()),
        )))
    }

    fn stack_local_load_u64(&self, addr: LocalVarAddr) -> Result<u64> {
        let addr = addr.0;
        println!(
            "Loading u64 from addr {}, range {}..{}, sp is {}",
            addr,
            addr - 8,
            addr,
            self.sp
        );
        match self
            .stack
            .get(addr - 8..addr)
            .map(TryInto::try_into)
            .map(|x: Result<[u8; 8], TryFromSliceError>| x.expect("infallible"))
            .map(u64::from_ne_bytes)
        {
            None => panic!("attempted to dig into local variable without space for it"),

            Some(val) => Ok(val),
        }
    }

    fn stack_local_store_u64(&mut self, addr: LocalVarAddr, src: u64) -> Result<()> {
        let addr = addr.0;

        println!(
            "Storing u64 {} at addr {}, range {}..{}",
            src,
            addr,
            addr - 8,
            addr
        );
        println!("Current sp: {}", self.sp);
        dbg!(addr);
        match self.stack.get_mut(addr - 8..addr) {
            None => panic!("attempted to dig into local variable without space for it"),

            Some(val) => val.copy_from_slice(&src.to_ne_bytes()),
        }

        Ok(())
    }

    fn stack_local_load_u8(&self, addr: LocalVarAddr) -> Result<u8> {
        match self.stack.get(addr.0) {
            None => panic!("attempted to dig into local variable without space for it"),

            Some(val) => Ok(*val),
        }
    }

    fn stack_local_store_u8(&mut self, addr: LocalVarAddr, src: u8) -> Result<()> {
        match self.stack.get_mut(addr.0) {
            None => panic!("attempted to dig into local variable without space for it"),

            Some(val) => *val = src,
        }

        Ok(())
    }

    fn stack_pop_u8(&mut self) -> Result<u8> {
        self.stack_pop(1).map(|arr| arr[0])
    }

    fn stack_left(&self) -> usize {
        self.stack.len() - self.sp
    }

    fn stack_push(&mut self, bytes: &[u8]) -> Result<(), VmRuntimeError> {
        let len = bytes.len();

        println!(
            "Pushing {} bytes at sp {}, will move sp to {}",
            len,
            self.sp,
            self.sp + len
        );
        if len + self.sp > MAX_STACK_SIZE {
            return Err(VmRuntimeError::StackOverflow);
        }

        self.stack[self.sp..self.sp + len].copy_from_slice(bytes);

        self.sp += len;
        Ok(())
    }

    fn stack_pop(&mut self, amount: usize) -> Result<&[u8]> {
        println!(
            "Popping {} bytes from sp {}, will move sp to {}",
            amount,
            self.sp,
            self.sp - amount
        );
        let old_stack_ptr = self.sp;

        if self.sp < amount {
            return Err(VmRuntimeError::StackTooLow);
        }

        self.sp -= amount;
        Ok(&self.stack[self.sp..old_stack_ptr])
    }

    fn stack_dup(&mut self, amount: usize) -> Result<()> {
        fn inner_stack_dup(ptr: &mut usize, arr: &mut [u8], amount: usize) {
            let old = *ptr;
            *ptr += amount;

            dbg!(old);
            let (left, right) = arr.split_at_mut(old);

            dbg!((&left, &right));

            right[..amount].copy_from_slice(&left[..amount]);
        }

        if amount + self.sp > self.stack.len() {
            return Err(VmRuntimeError::StackOverflow);
        } else if amount > self.stack_left() {
            return Err(VmRuntimeError::StackTooLow);
        }

        inner_stack_dup(&mut self.sp, &mut self.stack, amount);

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
struct LocalVarAddr(usize);

struct Frame {
    locals: [LocalVarAddr; 255],
    _stack_ptr: usize,
    len: usize,
    fn_name: String,
}

impl core::fmt::Debug for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CallFrame({}): (", self.fn_name)?;

        for (ix, local) in self.locals[..self.len].iter().enumerate() {
            write!(f, " {local:?}")?;

            if ix != self.len {
                write!(f, ",")?
            };

            write!(f, " ")?
        }

        write!(f, ")")
    }
}

impl Frame {
    fn new(_stack_ptr: usize, fn_name: String) -> Self {
        Self {
            locals: [LocalVarAddr(0); LOCAL_VARS_PER_FRAME],
            len: 0,
            _stack_ptr,
            fn_name,
        }
    }

    fn push_local(&mut self, sp: usize) -> Result<()> {
        if self.len >= LOCAL_VARS_PER_FRAME {
            return Err(VmRuntimeError::TooMuchLocalVariables);
        }

        self.locals[self.len] = LocalVarAddr(sp);
        dbg!(sp);
        self.len += 1;

        Ok(())
    }

    fn get_local_addr(&mut self, idx: usize) -> Result<LocalVarAddr> {
        if idx >= self.len {
            return Err(VmRuntimeError::LocalVariableMissing(idx));
        }

        match self.locals.get(idx) {
            None => Err(VmRuntimeError::LocalVariableMissing(idx)),

            Some(v) => Ok(*v),
        }
    }
}

struct Vm<'v> {
    stack: Stack,
    ip: usize,
    reader: bytecode::BytecodeCompiler<'v>,
    cmp_flags: VmFlags,
    variables: Variables,
    frames: Vec<Frame>,
    objects: Objects,
}

fn main() {}

// impl<'v> Vm<'v> {
//     fn new(code: &'v [u8]) -> Result<Self> {
//         let mut parser = bytecode::Bytecode::new(code);
//         let objs = parser.read_evm_bytecode()?;

//         let mut vm = Self {
//             stack: Stack {
//                 sp: 0,
//                 stack: [0; MAX_STACK_SIZE],
//             },

//             ip: 0,
//             reader: BytecodeReader::new(code),
//             cmp_flags: VmFlags {
//                 equal: false,
//                 greater: false,
//                 lesser: false,
//             },

//             variables: Variables::new(vec![Variable::test_variable()]),
//             frames: vec![],
//             objects: objs,
//         };

//         vm.call_instruction(Op::Call, 0)?;

//         Ok(vm)
//     }

//     fn last_frame(&mut self) -> &mut Frame {
//         self.frames
//             .last_mut()
//             .unwrap_or_else(|| unreachable!("there must be atleast one frame"))
//     }

// fn debug_report<A>(&self, opcode: A, show_stack: bool)
// where
//     A: Into<Option<Op>>,
// {
//     let op = opcode.into();
//     #[cfg(debug_assertions)]
//     println!(
//         "[vm] (instruction: {op:?}) | stack ptr: {} | instr ptr: {} | stack left: {} |",
//         self.stack.sp,
//         self.ip,
//         self.stack.stack.len() - self.stack.sp
//     );
//     println!(
//         "[vm] flags: eq: {}, gt: {}, le: {}",
//         self.cmp_flags.equal, self.cmp_flags.greater, self.cmp_flags.lesser
//     );

//     let mut pointer = String::from("[\n");

//     for (ix, byte) in self.stack.stack.into_iter().enumerate() {
//         use std::fmt::Write;
//         write!(&mut pointer, "{byte:>6}").unwrap();

//         if ix == self.stack.sp {
//             pointer.push_str(" <--- STACK POINTER\n");
//         } else {
//             pointer.push('\n')
//         }
//     }

//     pointer.push_str("]\n");

//     println!("frames: {:?}", &self.frames);

//     if show_stack {
//         println!("stack after instruction: {pointer}");
//     }
// }

// fn interpret_one(&mut self) -> Result<bool, VmRuntimeError> {
//     use Op::*;

//     let mut vm_continue = true;
//     let Some(op) = self.reader.get_op(self.ip) else {
//         return Ok(false);
//     };
//     let op = op?;

//     match op {
//         Add => {
//             binop!(+, Add, self)
//         }

//         Sub => {
//             binop!(-, Sub, self)
//         }

//         Mul => {
//             binop!(*, Mul, self)
//         }

//         Div => {
//             binop!(/, Div, self)
//         }

//         Push => {
//             self.push_instruction()?;
//         }

//         CmpVal => {
//             let lhs = self.stack.stack_pop_u64()?;
//             let rhs = self.stack.stack_pop_u64()?;

//             match rhs.cmp(&lhs) {
//                 Ordering::Less => self.cmp_flags.lesser = true,
//                 Ordering::Greater => self.cmp_flags.greater = true,
//                 Ordering::Equal => self.cmp_flags.equal = true,
//             }
//         }

//         CmpObj => {}

//         Jump => {
//             let ptr = self.stack.stack_pop_u64()?;
//             self.ip = ptr as usize;
//         }

//         JumpIfEq => {
//             jump_impl!(self, consume_eq);
//         }

//         JumpIfGr => {
//             jump_impl!(self, consume_gr);
//         }

//         JumpIfLe => {
//             jump_impl!(self, consume_le);
//         }

//         Call => {
//             let Some(val) = self
//                 .reader
//                 .src
//                 .get(self.ip + 1..self.ip + 9)
//                 .map(|x| TryInto::try_into(x).unwrap())
//                 .map(u64::from_ne_bytes)
//             else {
//                 return Err(VmRuntimeError::MissingOperand);
//             };

//             self.call_instruction(op, val as usize)?
//         }

//         Return => {
//             let addr = self.stack.stack_pop_u64()?;
//             self.ip = addr as usize;
//         }

//         LoadU64 => {
//             load_impl!(self, stack_local_load_u64);
//         }

//         StoreU64 => {
//             store_impl!(self, stack_local_store_u64, stack_pop_u64);
//         }

//         LoadU8 => {
//             load_impl!(self, stack_local_load_u8);
//         }

//         StoreU8 => {
//             store_impl!(self, stack_local_store_u8, stack_pop_u8);
//         }

//         AllocLocal => {
//             self.ip += 1;
//             let Some(size) = self.reader.get(self.ip).map(|size| size as usize) else {
//                 return Err(VmRuntimeError::MissingOperand);
//             };

//             if size == 0 {
//                 return Ok(true);
//             }

//             if self.stack.stack_left() < size {
//                 return Err(VmRuntimeError::StackOverflow);
//             }

//             self.stack.sp += size;
//             let save_sp = self.stack.sp;
//             self.last_frame().push_local(save_sp)?;
//         }

//         Dup => {
//             let size = self.stack.stack_pop_u64()?;
//             self.stack.stack_dup(size as usize)?;
//         }

//         End => vm_continue = false,
//     }

//     self.debug_report(op, true);
//     self.ip += 1;

//     Ok(vm_continue)
// }

// fn interpret_all(&mut self) -> Result<()> {
//     self.debug_report(None, false);
//     while self.interpret_one()? {}

//     Ok(())
// }

//     fn call_instruction(&mut self, op: Op, val: usize) -> Result<()> {
//         let Some(inner) = self.objects.get(val) else {
//             return Err(VmRuntimeError::MissingFn(val as u64));
//         };

//         if let Some(func) = inner.get_fn() {
//             let frame = Frame::new(self.stack.sp, func.name().to_string());

//             self.frames.push(frame);
//             self.stack
//                 .stack_push(&u64::to_ne_bytes(self.ip as u64 + 2))?; // return address
//             self.ip = func.jump_ip();
//         } else {
//             return Err(VmRuntimeError::InvalidType(op));
//         }

//         Ok(())
//     }

//     fn push_instruction(&mut self) -> Result<()> {
//         if let Some(val) = self
//             .reader
//             .src
//             .get(self.ip + 1..self.ip + 9)
//             .map(TryInto::try_into)
//             .map(|x| x.unwrap())
//         {
//             dbg!(val);
//             self.stack.stack_push(val)?;
//         } else {
//             return Err(VmRuntimeError::MissingOperand);
//         };

//         self.ip += 8;

//         Ok(())
//     }
// }

// fn main() -> Result<()> {
//     #[rustfmt::skip]
//     let bytecode = [
//         101, 118, 109, 32, 58, 51, // "evm :3" marker
//         1, 1, // function def marker
//         109, 97, 105, 110, 0, // name

//         0, 0, 0, 0, 0, 0, 0, 0, // index
//         0, 0, // arity

//         // actual body
//         18, 8,
//         18, 8,
//         4, 2, 2, 2, 2, 2, 2, 2, 2,
//         15, 0,
//         4, 2, 2, 2, 2, 2, 2, 2, 2,
//         15, 1,
//         14, 0,
//         14, 1,
//         0,
//         15, 1,
//         14, 1,
//         4, 3, 3, 3, 3, 3, 3, 3, 3,
//         5,
//         4, 0, 255, 255, 255, 255, 255, 255, 255,
//         8,
//         // end of body
//         255,

//         // function def end marker
//         255, 254, 255, 254,
//     ];

//     let mut vm = Vm::new(&bytecode)?;

//     vm.interpret_all()?;

//     Ok(())
//     // vm.interpret_one().unwrap();
//     // vm.interpret_one().unwrap();
//     // vm.interpret_one().unwrap();
//     //

//     // vm.interpret_all().unwrap();
// }
