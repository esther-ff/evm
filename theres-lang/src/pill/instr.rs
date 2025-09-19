use crate::ast::{BinOp, UnaryOp};
use crate::hir::def::DefId;
use crate::pill::body::{AltarId, LabelId};
use crate::pill::scalar::Scalar;
use crate::types::fun_cx::FieldId;
use crate::types::ty::Instance;

use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter, Result};

#[derive(Clone, Copy)]
pub enum Operand {
    Immediate(Scalar),
    Variable(AltarId),
}

impl Debug for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Operand::Variable(altar) => write!(f, "_{alt}", alt = altar.to_usize()),
            Operand::Immediate(scalar) => write!(f, "imm({scalar:?})"),
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        <Self as Debug>::fmt(self, f)
    }
}

trait Sealed {}
#[derive(Debug, Clone, Copy)]
pub struct Full;

impl Sealed for Infallible {}
impl Sealed for Full {}

#[allow(private_bounds)]
#[derive(Clone)]
pub enum Instruction<'il, Id = Infallible, S: Sealed = Infallible> {
    Binary(BinOp, Operand, Operand, AltarId),
    Unary(UnaryOp, Operand, AltarId),
    Index {
        place: Operand,
        idx: Operand,
        result: AltarId,
    },
    Assign(AltarId, Operand),
    Construct(Instance<'il>, Vec<Operand>, AltarId),
    Field {
        src: Operand,
        field_idx: FieldId,
        result: AltarId,
    },
    Call(DefId, Vec<Operand>, AltarId),

    Return(S),
    Goto(Id, S),
    Branch(Operand, Id, Id, S),

    Nop,
}

impl<Id: Debug, S: Sealed> Debug for Instruction<'_, Id, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Binary(op, lhs, rhs, altar) => {
                write!(
                    f,
                    "_{var} = {op}({lhs:#?}, {rhs:#?})",
                    var = altar.to_usize()
                )
            }

            Self::Field {
                src,
                field_idx,
                result,
            } => write!(f, "_{result} = field({src}, {field_idx})"),

            Self::Unary(op, operand, altar) => {
                write!(f, "_{var} = {op}({operand:#?})", var = altar.to_usize())
            }

            Self::Index { place, idx, result } => {
                write!(f, "_{var} = {place:?}[{idx:?}]", var = result.to_usize())
            }

            Self::Construct(def, operands, result) => write!(
                f,
                "_{var} = construct({:?}, {:?})",
                def.name.get_interned(),
                operands,
                var = result.to_usize(),
            ),

            Self::Goto(id, _) => write!(f, "goto {id:?}"),

            Self::Return(..) => write!(f, "return"),

            Self::Assign(altar, op) => write!(f, "_{alt} = {op:?}", alt = altar.to_usize()),

            // Self::Switch(op, targets, otherwise, ..) => {
            //     write!(f, "switch {op:?}: {targets:?} ({otherwise:?})")
            // }
            Self::Call(def, args, altar) => {
                write!(f, "_{alt} = call: {def} ({args:?})", alt = altar.to_usize())
            }

            Self::Nop => write!(f, "nop"),

            Self::Branch(op, true_, false_, ..) => {
                write!(f, "branch {op:?} true: {true_:?} false: {false_:?}")
            }
        }
    }
}

impl<Id: Debug, S: Sealed> Display for Instruction<'_, Id, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        <Self as Debug>::fmt(self, f)
    }
}

pub type Instr<'il> = Instruction<'il, LabelId, Full>;

pub struct InstrStream<'il> {
    tac: Vec<Instr<'il>>,
}

impl<'il> InstrStream<'il> {
    pub fn new() -> Self {
        Self { tac: vec![] }
    }

    pub fn emit_call(&mut self, fun: DefId, args: Vec<Operand>, place: AltarId) {
        self.tac.push(Instruction::Call(fun, args, place));
    }

    pub fn emit_branch(&mut self, op: Operand, true_: LabelId, false_: LabelId) {
        self.tac.push(Instruction::Branch(op, true_, false_, Full));
    }

    pub fn emit_goto(&mut self, label: LabelId) {
        self.tac.push(Instruction::Goto(label, Full));
    }

    pub fn emit_bin_op(&mut self, op: BinOp, lhs: Operand, rhs: Operand, result: AltarId) {
        self.tac.push(Instruction::Binary(op, lhs, rhs, result));
    }
    pub fn emit_un_op(&mut self, op: UnaryOp, val: Operand, place: AltarId) {
        self.tac.push(Instruction::Unary(op, val, place));
    }

    pub fn emit_assign(&mut self, lvalue: AltarId, rvalue: Operand) {
        self.tac.push(Instruction::Assign(lvalue, rvalue));
    }

    pub fn emit_index(&mut self, place: Operand, idx: Operand, result: AltarId) {
        self.tac.push(Instruction::Index { place, idx, result });
    }

    pub fn emit_constr(&mut self, def: Instance<'il>, args: Vec<Operand>, result: AltarId) {
        self.tac.push(Instruction::Construct(def, args, result));
    }

    pub fn emit_return(&mut self) {
        self.tac.push(Instruction::Return(Full));
    }

    pub fn tac(&self) -> &[Instr<'il>] {
        &self.tac
    }
}
