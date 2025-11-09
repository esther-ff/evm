mod private {
    crate::newtyped_index!(BasicBlock, U, BasicBlocks, A);
}

use std::fmt::Debug;

use crate::pill::body::LocalsRef;
pub use private::BasicBlock;

use crate::air::def::IntTy;
use crate::pill::access::Access;
use crate::pill::body::Local;
use crate::pill::op::{BinOp, UnOp};
use crate::pill::scalar::Scalar;
use crate::session::{Session, cx};
use crate::span::Span;
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
    _span: Span,
}

impl<'il> Imm<'il> {
    pub fn ty(&self) -> Ty<'il> {
        self.ty
    }

    pub fn empty(cx: &'il Session<'il>, ty: Ty<'il>, span: Span) -> &'il Self {
        let this = Self {
            kind: ImmKind::Empty,
            ty,
            _span: span,
        };

        cx.arena().alloc(this)
    }

    pub fn scalar(cx: &'il Session<'il>, scalar: Scalar, ty: Ty<'il>, span: Span) -> &'il Self {
        let this = Self {
            kind: ImmKind::Scalar(scalar),
            ty,
            _span: span,
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

            ImmKind::Empty => write!(f, "{{{ty}}}", ty = self.ty),
        }
    }
}

#[derive(Copy, Clone)]
pub enum Operand<'il> {
    Imm(&'il Imm<'il>),
    Use(Access<'il>),
}

impl<'il> Operand<'il> {
    pub fn maybe_use(&self) -> Option<Access<'il>> {
        match self {
            Self::Imm { .. } => None,
            Self::Use(inner) => Some(*inner),
        }
    }

    pub fn ty(&self, data: &LocalsRef<'il>, cx: &'il Session<'il>) -> Ty<'il> {
        match self {
            Operand::Imm(imm) => imm.ty,
            Operand::Use(acc) => acc.deduct_type(cx, data.get(acc.get_base()).unwrap().ty()),
        }
    }
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
pub enum BlockExitKind<'il> {
    Goto(BasicBlock),
    Branch {
        val: Operand<'il>,
        true_: BasicBlock,
        false_: BasicBlock,
    },
    Return,
}

#[derive(Debug)]
pub struct BlockExit<'il> {
    span: Span,
    kind: BlockExitKind<'il>,
}

impl<'il> BlockExit<'il> {
    pub(super) fn new(kind: BlockExitKind<'il>, span: Span) -> Self {
        Self { span, kind }
    }

    pub fn kind(&self) -> &BlockExitKind<'il> {
        &self.kind
    }

    pub fn span(&self) -> Span {
        self.span
    }
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

    AddrOf(Access<'il>),
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

            Self::AddrOf(inner) => write!(f, "&{inner:?}"),

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
pub enum StmtKind<'il> {
    Assign {
        dest: Access<'il>,
        src: Rvalue<'il>,
        bypass_const: bool,
    },

    Call {
        fun: Operand<'il>,
        ret: Access<'il>,
        args: Vec<Operand<'il>>,
    },

    CheckCond(Operand<'il>),

    LocalLive(Local),
}

#[derive(Debug)]
pub struct Stmt<'il> {
    kind: StmtKind<'il>,
    span: Span,
}

impl<'il> Stmt<'il> {
    pub fn kind(&self) -> &StmtKind<'il> {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut StmtKind<'il> {
        &mut self.kind
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn new(kind: StmtKind<'il>, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug)]
pub struct BbData<'il> {
    predecessors: Vec<BasicBlock>,
    stmts: Vec<Stmt<'il>>,
    pub(super) exit: Option<BlockExit<'il>>,
}

impl<'il> BbData<'il> {
    pub fn stmts(&self) -> &[Stmt<'il>] {
        &self.stmts
    }

    pub fn stmts_mut(&mut self) -> &mut [Stmt<'il>] {
        &mut self.stmts
    }

    pub fn exit(&self) -> Option<&BlockExit<'il>> {
        self.exit.as_ref()
    }

    pub fn exit_mut(&mut self) -> &mut BlockExit<'il> {
        self.exit.as_mut().unwrap()
    }

    pub fn predecessors(&self) -> &[BasicBlock] {
        &self.predecessors
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

    pub fn live(&mut self, bb: BasicBlock, span: Span, local: Local) {
        self.push_stmt(
            bb,
            Stmt {
                kind: StmtKind::LocalLive(local),
                span,
            },
        );
    }

    pub fn assign(&mut self, bb: BasicBlock, dest: Access<'il>, src: Rvalue<'il>, span: Span) {
        self.push_stmt(
            bb,
            Stmt {
                kind: StmtKind::Assign {
                    dest,
                    src,
                    bypass_const: false,
                },
                span,
            },
        );
    }

    pub fn call(
        &mut self,
        bb: BasicBlock,
        fun: Operand<'il>,
        args: Vec<Operand<'il>>,
        ret: Access<'il>,
        span: Span,
    ) {
        self.push_stmt(
            bb,
            Stmt {
                kind: StmtKind::Call { fun, ret, args },
                span,
            },
        );
    }

    pub fn check(&mut self, bb: BasicBlock, cond: Operand<'il>, span: Span) {
        self.push_stmt(
            bb,
            Stmt {
                kind: StmtKind::CheckCond(cond),
                span,
            },
        );
    }

    pub fn goto(&mut self, bb: BasicBlock, target: BasicBlock, span: Span) {
        self.bbs[target].predecessors.push(bb);
        self.bbs[bb].exit.replace(BlockExit {
            span,
            kind: BlockExitKind::Goto(target),
        });
    }

    pub fn bb_return(&mut self, bb: BasicBlock, span: Span) {
        self.bbs[bb].exit.replace(BlockExit {
            span,
            kind: BlockExitKind::Return,
        });
    }

    pub fn dummy_goto(&mut self, bb: BasicBlock, span: Span) {
        self.goto(bb, BasicBlock::DUMMY, span);
    }

    pub fn branch(
        &mut self,
        bb: BasicBlock,
        val: Operand<'il>,
        true_: BasicBlock,
        false_: BasicBlock,
        span: Span,
    ) {
        self.bbs[true_].predecessors.push(bb);
        self.bbs[false_].predecessors.push(bb);
        self.bbs[bb].exit.replace(BlockExit {
            span,
            kind: BlockExitKind::Branch { val, true_, false_ },
        });
    }

    pub fn push_stmt(&mut self, bb: BasicBlock, stmt: Stmt<'il>) {
        self.bbs[bb].stmts.push(stmt);
    }

    pub fn new_block(&mut self) -> BasicBlock {
        self.bbs.push(BbData {
            predecessors: vec![],
            stmts: vec![],
            exit: None,
        })
    }

    pub fn blocks(&'il self) -> impl Iterator<Item = (BasicBlock, &'il BbData<'il>)> {
        self.bbs.iter()
    }

    pub fn blocks_mut(&mut self) -> impl Iterator<Item = (BasicBlock, &mut BbData<'il>)> {
        self.bbs.iter_mut()
    }

    pub fn len(&self) -> usize {
        self.bbs.len()
    }
}
