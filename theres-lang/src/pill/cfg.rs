mod private {
    crate::newtyped_index!(BasicBlock, U, BasicBlocks, A);
}

pub use private::BasicBlock;

use crate::pill::access::Access;
use crate::pill::body::Local;
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
use crate::session::Session;
use crate::types::ty::Ty;
use crate::types::ty::{Instance, LambdaEnv};

pub enum ImmKind {
    Scalar(Scalar),
    Empty,
}

pub struct Imm<'il> {
    kind: ImmKind,
    ty: Ty<'il>,
}

impl<'il> Imm<'il> {
    pub fn empty(cx: &'il Session<'il>, ty: Ty<'il>) -> &'il Self {
        let this = Self {
            kind: ImmKind::Empty,
            ty,
        };

        cx.arena().alloc(this)
    }

    pub fn scalar(cx: &'il Session<'il>, scalar: Scalar, ty: Ty<'il>) -> &'il Self {
        let this = Self {
            kind: ImmKind::Scalar(scalar),
            ty,
        };

        cx.arena().alloc(this)
    }
}

#[derive(Copy, Clone)]
pub enum Operand<'il> {
    Imm(&'il Imm<'il>),
    Use(Access<'il>),
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

pub enum AdtKind<'il> {
    Def(Instance<'il>),
    Lambda(LambdaEnv<'il>),
}

pub enum Rvalue<'il> {
    Binary {
        op: BinOp,
        lhs: Operand<'il>,
        rhs: Operand<'il>,
    },

    Unary {
        op: UnOp,
        val: Operand<'il>,
    },

    Regular(Operand<'il>),

    Adt {
        def: AdtKind<'il>,
        args: Vec<Operand<'il>>,
    },

    List(Vec<Operand<'il>>),

    Length(Access<'il>),
}

#[non_exhaustive]
pub enum Stmt<'il> {
    Assign {
        dest: Access<'il>,
        src: Rvalue<'il>,
    },

    Call {
        fun: Operand<'il>,
        ret: Local,
        args: Vec<Operand<'il>>,
    },

    CheckCond(Operand<'il>),

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
