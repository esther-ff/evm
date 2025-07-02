use super::VmRuntimeError;
use super::instruction::{Instr, Instructions};
use super::objects::{Func, Functions, Objects};

use core::fmt::Display;

type Result<T, E = BytecodeError> = core::result::Result<T, E>;

const EVM_MARKER: &[u8] = b"evm :3";
const FN_DECL: &[u8] = &[1, 1];

#[non_exhaustive]
#[derive(Debug)]
pub(crate) enum BytecodeError {
    Invalid,

    // functions
    FnParse { reason: &'static str, offset: usize },

    InvalidInstruction { offset: usize, instr: u8 },

    MissingOperand { offset: usize, instr: u8 },
}

impl From<BytecodeError> for VmRuntimeError {
    fn from(value: BytecodeError) -> Self {
        VmRuntimeError::Bytecode(value)
    }
}

impl Display for BytecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid => write!(f, "something went wrong"),
            Self::FnParse { reason, offset } => write!(
                f,
                "error during parsing function\nreason: {reason}\nat offset {offset} in file"
            ),
            Self::InvalidInstruction { offset, instr } => write!(
                f,
                "invalid instruction encountered ({instr}) at offset {offset} in data"
            ),
            Self::MissingOperand { offset, instr } => write!(
                f,
                "missing operands for instruction encountered at ({offset}) for instruction {instr}"
            ),
        }
    }
}

pub(crate) struct BytecodeCompiler<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> BytecodeCompiler<'a> {
    pub(crate) fn new(src: &'a [u8]) -> Self {
        Self { src, pos: 0 }
    }

    pub(crate) fn read_evm_bytecode(&mut self) -> Result<(Objects, Instructions, Functions)> {
        let mut objs = Objects::new();
        let mut instructions = Vec::new();
        let mut fns = Functions::new();

        if !self.validate_header() {
            return Err(BytecodeError::Invalid);
        } else {
            self.pos += EVM_MARKER.len()
        }

        if let Some(arr) = self.src.get(self.pos..self.pos + 2) {
            self.pos += 2;

            match arr {
                FN_DECL => self.parse_fn_decl(&mut objs, &mut instructions, &mut fns)?,

                _ => todo!(),
            }
        }

        Ok((objs, Instructions::from_vec(instructions), fns))
    }

    fn validate_header(&self) -> bool {
        debug_assert!(self.pos == 0);

        self.src
            .get(self.pos..6)
            .is_some_and(|arr| arr == EVM_MARKER)
    }

    fn parse_fn_decl(
        &mut self,
        objs: &mut Objects,
        instrs: &mut Vec<Instr>,
        fns: &mut Functions,
    ) -> Result<()> {
        let mut fn_name_ix_end = self.pos;

        for byte in &self.src[self.pos..] {
            if *byte == b'\0' {
                break;
            }

            fn_name_ix_end += 1
        }

        let Some(fn_name) = core::str::from_utf8(&self.src[self.pos..fn_name_ix_end])
            .ok()
            .map(|x| x.to_string())
        else {
            return Err(BytecodeError::FnParse {
                reason: "invalid utf-8 in function name",
                offset: fn_name_ix_end,
            });
        };

        self.pos = fn_name_ix_end;

        let Some(_index) = self
            .src
            .get(self.pos..self.pos + 8)
            .and_then(|slice| TryInto::try_into(slice).ok())
            .map(u64::from_ne_bytes)
        else {
            return Err(BytecodeError::FnParse {
                reason: "invalid index (lacking bytes)",
                offset: self.pos + 8,
            });
        };

        self.pos += 8;

        let Some(arity) = self
            .src
            .get(self.pos + 1..self.pos + 3)
            .and_then(|slice| TryInto::try_into(slice).ok())
            .map(u16::from_ne_bytes)
        else {
            return Err(BytecodeError::FnParse {
                reason: "invalid arity (lacking bytes)",
                offset: self.pos + 2,
            });
        };

        self.pos += 2;
        let jump_up = self.pos + 1;

        let (fn_start, mut fn_end) = (self.pos + 1, 0);
        let fn_def = Func::new(jump_up, fn_name, arity);
        fns.insert(fn_def);

        for byte in &self.src[self.pos..] {
            self.pos += 1;
            if *byte == 255 {
                let Some(arr) = self.src.get(self.pos - 1..self.pos + 3) else {
                    return Err(BytecodeError::FnParse {
                        reason: "end of function, with not enough ending bytes",
                        offset: self.pos,
                    });
                };

                if arr == [255, 254, 255, 254] {
                    fn_end = self.pos - 1;
                    self.pos += 4;

                    break;
                }

                continue;
            }
        }

        // dbg!(self.src[fn_start]);

        self.compile_bytecode(&self.src[fn_start..fn_end], instrs)
    }

    fn compile_bytecode(&mut self, bytecode: &[u8], instrs: &mut Vec<Instr>) -> Result<()> {
        dbg!(bytecode);
        let mut pos = 0;
        macro_rules! operand_op {
            ($num:expr, $self:ident, $op:ident) => {{
                let old = pos;
                pos += 8;
                let Some(bytes) = $self
                    .src
                    .get(old..pos)
                    .map(|x| TryInto::try_into(x).unwrap())
                else {
                    return Err(BytecodeError::MissingOperand {
                        offset: pos + $self.pos,
                        instr: $num,
                    });
                };

                Instr::$op(u64::from_ne_bytes(bytes))
            }};
        }
        while bytecode.len() > pos {
            let val = match bytecode[pos] {
                0 => Instr::Add,
                1 => Instr::Sub,
                2 => Instr::Mul,

                3 => Instr::Div,

                4 => {
                    let old = pos;
                    pos += 8;

                    let Some(bytes) = self
                        .src
                        .get(old..pos)
                        .map(|x| TryInto::try_into(x).unwrap())
                    else {
                        return Err(BytecodeError::MissingOperand {
                            offset: pos + self.pos,
                            instr: 4,
                        });
                    };

                    Instr::Push(u64::from_ne_bytes(bytes))
                }

                5 => Instr::CmpVal,
                6 => Instr::CmpObj,

                7 => operand_op!(7, self, Jump),
                8 => operand_op!(8, self, JumpIfGr),
                9 => operand_op!(9, self, JumpIfEq),
                10 => operand_op!(10, self, JumpIfLe),

                11 => operand_op!(11, self, Call),
                12 => Instr::Return,

                13 => Instr::Dup,

                14 => operand_op!(14, self, Load),
                15 => operand_op!(15, self, Store),
                16 => Instr::AllocLocal,

                255 => Instr::End,

                any => {
                    return Err(BytecodeError::InvalidInstruction {
                        offset: pos + self.pos,
                        instr: any,
                    });
                }
            };

            pos += 1;

            instrs.push(val);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::objects::FnRef;

    use super::*;

    #[test]
    fn fn_decl() {
        let mut bytecode = Vec::new();
        bytecode.extend_from_slice(b"evm :3"); // header
        bytecode.extend_from_slice(&[1, 1]); // fn decl marker
        bytecode.extend_from_slice(b"main\0"); // name with nul byte
        bytecode.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0]); // index
        bytecode.extend_from_slice(&[1, 0]); // arity
        bytecode.extend_from_slice(&[255]); // end
        bytecode.extend_from_slice(&[255, 254, 255, 254]); // end of function decl

        dbg!(&bytecode);

        let mut parser = BytecodeCompiler::new(&bytecode);

        let (mut objs, instrs, fns) = parser.read_evm_bytecode().unwrap();
        dbg!(instrs);

        // let first_obj = objs.map(0, |x| match x {
        //     RtObjectInner::Fn(fndef) => {
        //         assert_eq!(fndef.name(), "main");
        //         assert_eq!(fndef.arity(), 1);
        //         assert_eq!(fndef.jump_ip(), 23);
        //     }

        //     _ => panic!("invalid type, not function"),
        // });

        let fndef = fns.get(FnRef(0)).unwrap();

        assert_eq!(fndef.name(), "main");
        assert_eq!(fndef.arity(), 1);
        assert_eq!(fndef.jump_ip(), 23);
    }
}
