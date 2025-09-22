mod private {
    crate::newtyped_index!(BasicBlock, U, BasicBlocks, A);
}

pub use private::BasicBlock;

use crate::{
    air::def::DefId,
    ast::{BinOp, UnaryOp},
    pill::{body::AltarId, instr::Operand},
    types::ty::Instance,
};

pub enum BlockExit {
    Goto(BasicBlock),
    Branch(BasicBlock),
    Return,
}

pub enum Rvalue<'il> {
    Binary {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },

    Unary {
        op: UnaryOp,
        val: Operand,
    },

    Regular(Operand),

    Make {
        def: Instance<'il>,
        args: Vec<Operand>,
    },
}

#[non_exhaustive]
pub enum Stmt<'il> {
    Assign {
        dest: AltarId,
        src: Rvalue<'il>,
    },

    Call {
        fun: DefId,
        ret: AltarId,
        args: Vec<Operand>,
    },

    Nop,

    LocalLive(AltarId),
}

struct BbData<'il> {
    stmts: Vec<Stmt<'il>>,
    exit: Option<BlockExit>,
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

    pub fn end_block(&mut self, bb: BasicBlock, exit: BlockExit) {
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
