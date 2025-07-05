use crate::call_stack::LocalId;
use crate::objects::FnRef;
use crate::vm::Operand;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Instr {
    Add,
    Sub,
    Mul,
    Div,
    Push(Operand),
    Call(FnRef),
    Return,
    JumpIfGr(ProgramCounter),
    JumpIfEq(ProgramCounter),
    JumpIfLe(ProgramCounter),
    Jump(ProgramCounter),
    CmpVal,
    CmpObj,
    Dup,

    Load(LocalId),
    Store(LocalId),

    AllocLocal,

    End,
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
    instr_ptr: usize,
}

impl Instructions {
    pub(crate) fn from_vec(stream: Vec<Instr>) -> Self {
        Self {
            stream,
            instr_ptr: 0,
        }
    }

    pub(crate) fn next(&mut self) -> Option<Instr> {
        let val = self.stream.get(self.instr_ptr).copied();
        self.instr_ptr += 1;
        val
    }

    pub(crate) fn jump(&mut self, new_ip: ProgramCounter) {
        self.instr_ptr += new_ip.0 as usize
    }

    pub(crate) fn len(&self) -> usize {
        self.stream.len()
    }

    pub fn ip(&self) -> ProgramCounter {
        ProgramCounter(self.instr_ptr as u32)
    }
}
