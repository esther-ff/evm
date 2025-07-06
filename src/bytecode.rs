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
}

impl<'a> Buffer<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
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
            .inspect(|x| {
                dbg!(x);
            })
            .map(u32::from_ne_bytes);

        self.pos += 4;
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

        Some(Buffer::new(&self.buf[old_pos..self.pos]))
    }
}

pub(crate) struct Parser<'a> {
    src: Buffer<'a>,
    instructions: Vec<Instr>,
    functions: Functions,
}

enum Section {
    Functions,
    Instances,
    Constants,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(src: &'a [u8]) -> Self {
        Self {
            src: Buffer { buf: src, pos: 0 },
            instructions: Vec::new(),
            functions: Functions::new(),
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
            Section::Functions => {
                Self::parse_fn_decl(&mut self.src, &mut self.instructions, &mut self.functions)
            }

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
    ) -> Result<()> {
        let pos = buffer.pos() + 4;
        dbg!(&buffer.buf[buffer.pos()..]);
        let Some((mut bytecode, ip)) = buffer.next_u32().and_then(|offset| {
            buffer
                .sub_buffer(dbg!(offset) as usize)
                .zip(Some(offset - 1))
        }) else {
            todo!("length error");
        };

        compile_fn_bytecode(&mut bytecode, instrs, pos)?;

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

        dbg!(&buffer.buf[buffer.pos()..]);

        let Some(metadata_len) = buffer.next_u32().map(|var| var as usize) else {
            todo!("length error");
        };

        let mut _metadata = None;

        if let Some(ref mut metadata_buf) = buffer.sub_buffer(metadata_len) {
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
) -> Result<()> {
    while !bytecode.eof() {
        let Some(instr) = Instr::from_buffer(bytecode) else {
            return Err(BytecodeError::InvalidInstruction {
                offset: bytecode.pos() + original_pos,
                instr: bytecode.peek().unwrap(),
            });
        };

        instrs.push(instr);
    }

    Ok(())
}

fn process_metadata(_buf: &mut Buffer<'_>) -> Result<()> {
    todo!("process metadata");
}

#[cfg(test)]
mod tests {
    use crate::{bytecode::Parser, instruction::ProgramCounter, objects::FnRef};

    #[test]
    fn fn_decl() {
        let bytecode = [
            101, 118, 109, 32, 58, 51, 1, 1, 1, 0, 0, 0, 255, 4, 0, 0, 0, 109, 97, 105, 110, 0, 0,
            0, 0, 0, 0,
        ];

        dbg!(&bytecode);

        let mut parser = Parser::new(&bytecode);

        let sections = parser.compile_bytecode().unwrap();

        dbg!(sections);
    }
}
