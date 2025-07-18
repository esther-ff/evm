use crate::bytecode::Buffer;
use crate::call_stack::LocalId;
use crate::objects::{ArrayType, FnRef, InstanceId};
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub(crate) enum Instr {
    IAdd,
    ISub,
    IMul,
    IDiv,
    IShl,
    IShr,
    IConst(u32),

    LAdd,
    LSub,
    LMul,
    LDiv,
    LShl,
    LShr,
    LConst(u64),

    FAdd,
    FSub,
    FMul,
    FDiv,
    FConst(f32),

    DAdd,
    DSub,
    DMul,
    DDiv,
    DConst(f64),

    Call(FnRef),
    Return,

    JumpIfGr(ProgramCounter),
    JumpIfEq(ProgramCounter),
    JumpIfLe(ProgramCounter),
    Jump(ProgramCounter),

    Cmp,
    Dup,

    New(InstanceId),     // create instance, todo
    NewArray(ArrayType), // create array of type (specified)

    Invoke,     // invoke method on instance
    NativeCall, // invoke native function somehow?

    Pop,

    Load(LocalId),
    Store(LocalId),

    Throw,
    Catch,

    AllocLocal,

    End,
}

impl Instr {
    pub fn from_buffer(buf: &mut Buffer<'_>) -> Option<Instr> {
        use Instr::*;

        match buf.next()? {
            // u32
            0 => IAdd,
            1 => ISub,
            3 => IMul,
            4 => IDiv,
            5 => IShl,
            6 => IShr,
            7 => IConst(buf.next_u32()?),

            // u64
            8 => LAdd,
            9 => LSub,
            10 => LMul,
            11 => LDiv,
            12 => LShl,
            13 => LShr,
            14 => LConst(buf.next_u64()?),

            // f32
            15 => FAdd,
            16 => FSub,
            17 => FMul,
            18 => FDiv,
            19 => FConst(buf.next_f32()?),

            // f64
            20 => DAdd,
            21 => DSub,
            22 => DMul,
            23 => DDiv,
            24 => DConst(buf.next_f64()?),

            25 => Call(buf.next_u32().map(FnRef)?),
            26 => Return,

            27 => Jump(buf.next_u32().map(ProgramCounter)?),
            28 => JumpIfGr(buf.next_u32().map(ProgramCounter)?),
            29 => JumpIfEq(buf.next_u32().map(ProgramCounter)?),
            30 => JumpIfLe(buf.next_u32().map(ProgramCounter)?),

            31 => Cmp,

            32 => Dup,

            33 => New(buf.next_u16().map(InstanceId)?), // create instance, todo

            34 => NewArray(ArrayType::Ref), // create array of type (specified)

            35 => Invoke,     // invoke method on instance
            36 => NativeCall, // invoke native function somehow?

            37 => Pop,

            38 => Throw,
            39 => Catch,

            40 => Load(buf.next_u16().map(LocalId)?),
            41 => Store(buf.next_u16().map(LocalId)?),

            42 => AllocLocal,

            255 => End,

            _ => return None,
        }
        .into()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProgramCounter(pub(crate) u32);

impl ProgramCounter {
    pub fn new(ip: u32) -> Self {
        Self(ip)
    }
}

#[derive(Debug)]
pub(crate) struct Instructions {
    stream: Vec<Instr>,
    instr_ptr: u32,
}

impl Instructions {
    pub(crate) fn from_vec(stream: Vec<Instr>) -> Self {
        Self {
            stream,
            instr_ptr: 0,
        }
    }

    pub(crate) fn next(&mut self) -> Option<Instr> {
        let val = self.stream.get(self.instr_ptr as usize).copied();
        self.instr_ptr += 1;
        val
    }

    pub(crate) fn jump(&mut self, new_ip: ProgramCounter) {
        self.instr_ptr += new_ip.0;
    }

    pub(crate) fn len(&self) -> usize {
        self.stream.len()
    }

    pub fn ip(&self) -> ProgramCounter {
        ProgramCounter(self.instr_ptr)
    }

    pub fn buf(&self) -> &[Instr] {
        &self.stream
    }
}
