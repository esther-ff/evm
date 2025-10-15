mod private {
    crate::newtyped_index!(BasicBlock, U, BasicBlocks, A);
}

pub use private::BasicBlock;

use crate::pill::body::Local;

use crate::types::ty::Ty;
use crate::{
    ast::{BinOp, UnaryOp},
    pill::scalar::Scalar,
    types::ty::Instance,
};

pub enum ImmKind {
    Scalar(Scalar),
    Empty,
}

pub struct Imm<'il> {
    kind: ImmKind,
    ty: Ty<'il>,
}

impl<'il> Imm<'il> {
    pub fn empty(ty: Ty<'il>) -> Self {
        Self {
            kind: ImmKind::Empty,
            ty,
        }
    }

    pub fn scalar(scalar: Scalar, ty: Ty<'il>) -> Self {
        Self {
            kind: ImmKind::Scalar(scalar),
            ty,
        }
    }
}

pub enum Operand<'il> {
    Imm(Imm<'il>),
    UseLocal(Local),
}

pub enum BlockExit<'il> {
    Goto(BasicBlock),
    Branch {
        val: Operand<'il>,
        true_: BasicBlock,
        false_: BasicBlock,
    },
    Return,
}

pub enum Rvalue<'il> {
    Binary {
        op: BinOp,
        lhs: Operand<'il>,
        rhs: Operand<'il>,
    },

    Unary {
        op: UnaryOp,
        val: Operand<'il>,
    },

    Regular(Operand<'il>),

    Make {
        def: Instance<'il>,
        args: Vec<Operand<'il>>,
    },
}

#[non_exhaustive]
pub enum Stmt<'il> {
    Assign {
        dest: Local,
        src: Rvalue<'il>,
    },

    Call {
        fun: Operand<'il>,
        ret: Local,
        args: Vec<Operand<'il>>,
    },

    // TailCall {
    //     fun: Operand,
    //     ret: AltarId,
    //     args: Vec<Operand>,
    // }
    Nop,

    LocalLive(Local),
}

struct BbData<'il> {
    stmts: Vec<Stmt<'il>>,
    exit: Option<BlockExit<'il>>,
}

pub struct Cfg<'il> {
    bbs: private::BasicBlocks<BbData<'il>>,
}

impl<'il> Cfg<'il> {
    pub fn new() -> Self {
        Self {
            bbs: private::BasicBlocks::new(),
        }
    }

    pub fn end_block(&mut self, bb: BasicBlock, exit: BlockExit<'il>) {
        debug_assert!(self.bbs[bb].exit.is_none());
        self.bbs[bb].exit.replace(exit);
    }

    pub fn push_stmt(&mut self, bb: BasicBlock, stmt: Stmt<'il>) {
        self.bbs[bb].stmts.push(stmt);
    }

    pub fn new_block(&mut self) -> BasicBlock {
        self.bbs.push(BbData {
            stmts: vec![],
            exit: None,
        })
    }

    pub fn cur(&self) -> BasicBlock {
        let len = self.bbs.len();
        assert!(len != 0);
        BasicBlock::new_usize(len.saturating_sub(1))
    }
}
