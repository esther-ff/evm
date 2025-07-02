type Op = u64;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Instr {
    Add,
    Sub,
    Mul,
    Div,
    Push(Op),
    Call(Op),
    Return,
    JumpIfGr(Op),
    JumpIfEq(Op),
    JumpIfLe(Op),
    Jump(Op),
    CmpVal,
    CmpObj,
    Dup,

    Load(Op),
    Store(Op),

    AllocLocal,

    End,
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

    pub(crate) fn jump(&mut self, new_ip: usize) {
        self.instr_ptr += new_ip
    }

    pub(crate) fn len(&self) -> usize {
        self.stream.len()
    }
}
