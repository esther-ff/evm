use super::instruction::{Instr, Instructions};
use super::objects::{Func, Functions};
use crate::vm::VmRuntimeError;

use core::fmt::Display;
use core::ops::ControlFlow;
use std::str::Utf8Error;

type EndResult = Result<(Instructions, Functions), BytecodeError>;
type Result<T, E = BytecodeError> = core::result::Result<T, E>;

const EVM_MARKER: &[u8] = b"evm :3";

#[non_exhaustive]
#[derive(Debug)]
pub(crate) enum BytecodeError {
    InvalidHeader,

    FnParse { reason: &'static str, offset: usize },

    InvalidInstruction { offset: usize, instr: u8 },

    MissingOperand { offset: usize, instr: u8 },

    InvalidSection,

    InvalidUtf8 { bytes: Vec<u8>, inner: Utf8Error },
}

impl From<BytecodeError> for VmRuntimeError {
    fn from(value: BytecodeError) -> Self {
        VmRuntimeError::Bytecode(value)
    }
}

impl Display for BytecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidHeader => write!(f, "invalid header"),
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

            Self::InvalidSection => write!(f, "invalid section header detected by the parser"),

            Self::InvalidUtf8 { bytes, inner } => write!(f, "bytes: {bytes:?}, error: {inner}"),
        }
    }
}

pub struct Buffer<'a> {
    buf: &'a [u8],
    pos: usize,

    sub_buffer_pos: usize,
}

impl<'a> Buffer<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            pos: 0,
            sub_buffer_pos: 0,
        }
    }

    pub fn peek(&self) -> Option<u8> {
        self.buf.get(self.pos).copied()
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn eof(&self) -> bool {
        self.pos >= self.buf.len()
    }

    pub fn advance(&mut self, len: usize) {
        self.pos += len;
    }

    pub fn check_for(&self, pat: &[u8]) -> bool {
        let len = pat.len();
        let Some(slice) = self.buf.get(self.pos..self.pos + len) else {
            return false;
        };

        slice == pat
    }

    pub fn next(&mut self) -> Option<u8> {
        let val = self.buf.get(self.pos).copied();
        self.pos += 1;
        val
    }

    pub fn next2(&mut self) -> Option<[u8; 2]> {
        let val = self
            .buf
            .get(self.pos..self.pos + 2)
            .map(TryInto::try_into)
            .and_then(Result::ok);

        self.pos += 2;
        val
    }

    pub fn next_u32(&mut self) -> Option<u32> {
        let val = self
            .buf
            .get(self.pos..self.pos + 4)
            .map(TryInto::try_into)
            .and_then(Result::ok)
            .map(u32::from_ne_bytes);

        self.pos += 4;
        val
    }

    pub fn next_u16(&mut self) -> Option<u16> {
        let val = self
            .buf
            .get(self.pos..self.pos + 2)
            .map(TryInto::try_into)
            .and_then(Result::ok)
            .map(u16::from_ne_bytes);

        self.pos += 2;
        val
    }

    pub fn next_pair_u8_u32(&mut self) -> Option<(u8, u32)> {
        let byte = self.next();
        let next = self.next_u32();

        byte.zip(next)
    }

    pub fn sub_buffer<'b>(&'b mut self, end: usize) -> Option<Buffer<'b>>
    where
        'a: 'b,
    {
        if self.pos + end >= self.buf.len() {
            return None;
        }

        let old_pos = self.pos;
        self.pos += end;

        Some(Buffer {
            buf: &self.buf[old_pos..self.pos],
            pos: 0,
            sub_buffer_pos: self.pos,
        })
    }

    pub fn offset(&self) -> usize {
        self.sub_buffer_pos
    }
}

pub(crate) struct Parser<'a> {
    src: Buffer<'a>,
    instructions: Vec<Instr>,
    functions: Functions,

    earlier_ip: u32,
}

enum Section {
    Functions,
    Instances,
    Constants,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(src: &'a [u8]) -> Self {
        Self {
            src: Buffer {
                buf: src,
                pos: 0,
                sub_buffer_pos: 0,
            },
            instructions: Vec::new(),
            functions: Functions::new(),

            earlier_ip: 0,
        }
    }

    pub fn compile_bytecode(mut self) -> EndResult {
        if self.validate_header() {
            self.src.advance(EVM_MARKER.len());
        } else {
            return Err(BytecodeError::InvalidHeader);
        }

        loop {
            if let ControlFlow::Break(result) = self.read_evm_bytecode_section() {
                return result
                    .map(|()| (Instructions::from_vec(self.instructions), self.functions));
            }
        }
    }

    fn read_evm_bytecode_section(&mut self) -> ControlFlow<Result<()>> {
        let Some(section) = self.determine_section() else {
            let err = Err(BytecodeError::InvalidSection);
            return ControlFlow::Break(err);
        };

        let ret = match section {
            Section::Functions => Self::parse_fn_decl(
                &mut self.src,
                &mut self.instructions,
                &mut self.functions,
                &mut self.earlier_ip,
            ),

            Section::Constants => todo!(),

            Section::Instances => todo!(),
        };

        if ret.is_err() {
            return ControlFlow::Break(ret);
        } else if self.src.eof() {
            return ControlFlow::Break(Ok(()));
        }

        ControlFlow::Continue(())
    }

    fn validate_header(&self) -> bool {
        debug_assert!(self.src.pos() == 0);

        self.src.check_for(EVM_MARKER)
    }

    fn determine_section(&mut self) -> Option<Section> {
        const FN_DECL: [u8; 2] = [1, 1];
        const CONST_DECL: [u8; 2] = [2, 2];
        const INSTANCE_DECL: [u8; 2] = [3, 3];

        match self.src.next2()? {
            FN_DECL => Section::Functions,
            CONST_DECL => Section::Constants,
            INSTANCE_DECL => Section::Instances,

            _ => return None,
        }
        .into()
    }

    fn parse_fn_decl(
        buffer: &mut Buffer<'_>,
        instrs: &mut Vec<Instr>,
        fns: &mut Functions,
        previous_ip: &mut u32,
    ) -> Result<()> {
        let pos = buffer.pos() + 4;

        let Some((mut bytecode, ip)) = buffer
            .next_u32()
            .and_then(|offset| buffer.sub_buffer(offset as usize).zip(Some(*previous_ip)))
        else {
            todo!("length error");
        };

        compile_fn_bytecode(&mut bytecode, instrs, pos, previous_ip)?;

        let Some(name_buf) = buffer
            .next_u32()
            .and_then(|offset| buffer.sub_buffer(offset as usize))
        else {
            todo!("length error");
        };

        let name = core::str::from_utf8(name_buf.buf)
            .map(ToString::to_string)
            .map_err(|err| BytecodeError::InvalidUtf8 {
                bytes: name_buf.buf.to_vec(),
                inner: err,
            })?;

        let Some(arity) = buffer.next2().map(u16::from_ne_bytes) else {
            todo!("length error");
        };

        let Some(metadata_len) = buffer.next_u32().map(|var| var as usize) else {
            todo!("length error");
        };

        let mut _metadata = None;

        if let Some(ref mut metadata_buf) = buffer.sub_buffer(metadata_len)
            && !metadata_buf.buf.is_empty()
        {
            _metadata = process_metadata(metadata_buf)?.into();
        } else if metadata_len != 0 {
            todo!("length error");
        }

        let decl = Func::new(ip, name, arity);
        fns.insert(decl);

        Ok(())
    }
}

fn compile_fn_bytecode(
    bytecode: &mut Buffer<'_>,
    instrs: &mut Vec<Instr>,
    original_pos: usize,
    previous: &mut u32,
) -> Result<()> {
    while !bytecode.eof() {
        let Some(instr) = Instr::from_buffer(bytecode) else {
            return Err(BytecodeError::InvalidInstruction {
                offset: bytecode.pos() + original_pos,
                instr: bytecode.peek().unwrap(),
            });
        };

        *previous += 1;

        instrs.push(instr);
    }

    *previous += 1;

    Ok(())
}

fn process_metadata(_buf: &mut Buffer<'_>) -> Result<()> {
    todo!("process metadata");
}

pub(crate) mod testing {
    use super::Buffer;
    use crate::instruction::Instr;
    pub fn create_fn_bytecode(dest: &mut Vec<u8>, name: &str, instructions: &[u8], arity: u16) {
        // assumes the header is there
        dest.extend_from_slice(&[1, 1]);

        #[allow(clippy::cast_possible_truncation)]
        dest.extend_from_slice(&u32::to_ne_bytes(instructions.len() as u32));
        dest.extend_from_slice(instructions);

        #[allow(clippy::cast_possible_truncation)]
        dest.extend_from_slice(&u32::to_ne_bytes(name.len() as u32));
        dest.extend_from_slice(name.as_bytes());
        dest.extend_from_slice(&u16::to_ne_bytes(arity));
        dest.extend_from_slice(&[0, 0, 0, 0]); // no metadata
    }

    pub fn gen_instructions(bytes: &[u8]) -> Vec<Instr> {
        let mut vec = Vec::new();
        let mut buf = Buffer::new(bytes);

        while !buf.eof() {
            let Some(instr) = Instr::from_buffer(&mut buf) else {
                panic!("invalid instruction in test")
            };

            vec.push(instr);
        }

        vec
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        bytecode::{Buffer, Parser},
        instruction::Instr,
        objects::FnRef,
    };

    use super::testing::{create_fn_bytecode, gen_instructions};

    #[test]
    fn fn_decls() {
        let mut bc = vec![101, 118, 109, 32, 58, 51];
        #[rustfmt::skip]
        let instructions = &[
           5, 0, 0, 0, 1,
           5, 0, 1, 1, 0,
           0,
           5, 1, 1, 1, 1,
           12,
           11, 0, 0, 0, 0,
           7,
        ];

        create_fn_bytecode(&mut bc, "vie", instructions, 16);
        create_fn_bytecode(&mut bc, "mort", instructions, 12);

        let parser = Parser::new(&bc);
        let (instr, fns) = parser.compile_bytecode().unwrap();

        let first_fn = fns.get(FnRef(0)).unwrap();
        let second_fn = fns.get(FnRef(1)).unwrap();
        let cmp = gen_instructions(instructions);

        // first instruction set
        assert_eq!(
            cmp.as_slice(),
            &instr.buf()[..second_fn.jump_ip().0 as usize - 1],
            "instructions were not equal"
        );

        // second instruction set
        assert_eq!(
            cmp.as_slice(),
            &instr.buf()[second_fn.jump_ip().0 as usize - 1..],
            "instructions were not equal"
        );

        // names
        assert_eq!(first_fn.name().as_ref(), "vie", "name wasn't equal");
        assert_eq!(second_fn.name().as_ref(), "mort", "name wasn't equal");

        // arity
        assert_eq!(first_fn.arity(), 16, "arity wasn't equal");
        assert_eq!(second_fn.arity(), 12, "arity wasn't equal");
    }
}
