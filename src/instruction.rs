use crate::bytecode::Buffer;
use crate::call_stack::LocalId;
use crate::objects::FnRef;
use crate::vm::Operand;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Instr {
    Add,
    Sub,
    Mul,
    Div,
    ConstUint32(Operand),
    Call(FnRef),
    Return,
    JumpIfGr(ProgramCounter),
    JumpIfEq(ProgramCounter),
    JumpIfLe(ProgramCounter),
    Jump(ProgramCounter),
    Cmp,
    Dup,

    Load(LocalId),
    Store(LocalId),

    AllocLocal,

    End,
}

impl Instr {
    pub fn from_buffer(buf: &mut Buffer<'_>) -> Option<Instr> {
        use Instr::*;

        match buf.next()? {
            // Add
            0 => Add,

            1 => Sub,

            3 => Mul,

            4 => Div,

            5 => ConstUint32(buf.next_u32()?),

            6 => Call(buf.next_u32().map(FnRef)?),

            7 => Return,

            8 => Jump(buf.next_u32().map(ProgramCounter)?),

            9 => JumpIfGr(buf.next_u32().map(ProgramCounter)?),

            10 => JumpIfEq(buf.next_u32().map(ProgramCounter)?),

            11 => JumpIfLe(buf.next_u32().map(ProgramCounter)?),

            12 => Cmp,

            13 => Dup,

            14 => Load(buf.next_u32().map(LocalId)?),

            15 => Store(buf.next_u32().map(LocalId)?),

            16 => AllocLocal,

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
}
