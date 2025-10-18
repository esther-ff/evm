mod private {
    crate::newtyped_index!(BasicBlock, U, BasicBlocks, A);
}

use std::fmt::Debug;

pub use private::BasicBlock;

use crate::air::def::IntTy;
use crate::pill::access::Access;
use crate::pill::body::Local;
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
use crate::session::{Session, cx};
use crate::types::ty::{Instance, LambdaEnv};
use crate::types::ty::{Ty, TyKind};

#[derive(Debug, Clone, Copy)]
pub enum ImmKind {
    Scalar(Scalar),
    Empty,
}

#[derive(Clone, Copy)]
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

impl Debug for Imm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            ImmKind::Scalar(scalar) => match *self.ty {
                TyKind::Uint(size) => match size {
                    IntTy::N8 => write!(f, "{val}_u8", val = scalar.to_u8()),
                    IntTy::N16 => write!(f, "{val}_u16", val = scalar.to_u16()),
                    IntTy::N32 => write!(f, "{val}_u32", val = scalar.to_u32()),
                    IntTy::N64 => write!(f, "{val}_u64", val = scalar.to_u64()),
                },

                TyKind::Int(size) => match size {
                    IntTy::N8 => write!(f, "{val}_i8", val = scalar.to_i8()),
                    IntTy::N16 => write!(f, "{val}_i16", val = scalar.to_i16()),
                    IntTy::N32 => write!(f, "{val}_i32", val = scalar.to_i32()),
                    IntTy::N64 => write!(f, "{val}_i64", val = scalar.to_i64()),
                },

                TyKind::Bool => write!(f, "{}", scalar.to_bool()),

                TyKind::Float => write!(f, "{}_f32", scalar.to_f32()),
                TyKind::Double => write!(f, "{}_f64", scalar.to_f64()),

                _ => write!(f, "<broken: {}>", self.ty),
            },

            ImmKind::Empty => write!(f, "Empty::<{ty}>", ty = self.ty),
        }
    }
}

#[derive(Copy, Clone)]
pub enum Operand<'il> {
    Imm(&'il Imm<'il>),
    Use(Access<'il>),
}

impl Debug for Operand<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Imm(inner) => write!(f, "imm {inner:?}"),
            Operand::Use(val) => val.fmt(f),
        }
    }
}

#[derive(Debug)]
pub enum BlockExit<'il> {
    Goto(BasicBlock),
    Branch {
        val: Operand<'il>,
        true_: BasicBlock,
        false_: BasicBlock,
    },
    Return,
}

#[derive(Debug, Clone, Copy)]
pub enum AdtKind<'il> {
    Def(Instance<'il>),
    Lambda(LambdaEnv<'il>),
}

#[derive(Clone)]
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

impl Debug for Rvalue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Adt { def, args } => {
                match def {
                    AdtKind::Def(def) => write!(f, "{}", def.name.get_interned()),
                    AdtKind::Lambda(env) => cx(|cx| {
                        let lambda = cx.air_get_lambda(env.did);
                        write!(f, "{{lambda <=> {span}}}", span = lambda.span)
                    }),
                }?;

                if args.is_empty() {
                    Ok(())
                } else {
                    write!(f, " {{")?;

                    for (ix, arg) in args.iter().enumerate() {
                        write!(f, " {ix}: {arg:?}")?;
                    }

                    write!(f, " }}")
                }
            }

            Self::List(list) => write!(f, "{list:?}"),

            Self::Binary { op, lhs, rhs } => write!(f, "{op:?}({lhs:?}, {rhs:?})"),

            Self::Unary { op, val } => write!(f, "{op:?}({val:?})"),

            Self::Length(val) => write!(f, "Length({val:?})"),

            Self::Regular(op) => op.fmt(f),
        }
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Stmt<'il> {
    Assign {
        dest: Access<'il>,
        src: Rvalue<'il>,
    },

    Call {
        fun: Operand<'il>,
        ret: Access<'il>,
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

#[derive(Debug)]
pub struct BbData<'il> {
    stmts: Vec<Stmt<'il>>,
    exit: Option<BlockExit<'il>>,
}

impl<'il> BbData<'il> {
    pub fn stmts(&self) -> &[Stmt<'il>] {
        &self.stmts
    }

    pub fn exit(&self) -> Option<&BlockExit<'il>> {
        self.exit.as_ref()
    }
}

#[derive(Debug)]
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

    pub fn blocks(&'il self) -> impl Iterator<Item = (BasicBlock, &'il BbData<'il>)> {
        self.bbs
            .iter()
            .enumerate()
            .map(|(ix, bb)| (BasicBlock::new_usize(ix), bb))
    }
}
