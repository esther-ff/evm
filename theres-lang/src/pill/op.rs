#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
    Shl,
    Shr,
    Mod,
    BitOr,
    BitAnd,
    BitXor,
    Eq,
    Ne,
    Gr,
    Ge,
    Lt,
    Le,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnOp {
    Neg,
    Not,
}
