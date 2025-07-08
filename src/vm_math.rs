// use std::ops::ControlFlow;

use std::fmt::{Debug, Display};

use crate::objects::Value;
use crate::stack::{Stack, StackError};

pub type MathResult<T, E = MathError> = core::result::Result<T, E>;
use crate::vm::{MAX_STACK_SIZE, VmRuntimeError};

#[derive(Debug, Clone, Copy)]
pub enum MathError {
    Overflow,
    Underflow,
    DivisionByZero,
    ValueNotNumber,
    StackError(StackError),
}

impl Display for MathError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ret = match self {
            Self::Overflow => "overflow occurred",
            &Self::Underflow => "underflow occured",
            &Self::DivisionByZero => "division by zero",
            &Self::ValueNotNumber => "value wasn't a number",

            &Self::StackError(err) => return err.fmt(f),
        };

        f.write_str(ret)
    }
}

impl From<StackError> for MathError {
    fn from(value: StackError) -> Self {
        MathError::StackError(value)
    }
}

impl From<MathError> for VmRuntimeError {
    fn from(value: MathError) -> Self {
        VmRuntimeError::Math(value)
    }
}

impl MathError {
    pub fn is_overflow(&self) -> bool {
        matches!(self, MathError::Overflow)
    }
    pub fn is_underflow(&self) -> bool {
        matches!(self, MathError::Underflow)
    }

    pub fn is_div_by_zero(&self) -> bool {
        matches!(self, MathError::DivisionByZero)
    }
}

/// Function for operations on `u32`
pub fn u32_math<'a, F, Err>(
    stack: &mut Stack<MAX_STACK_SIZE, Value<'a>>,
    op: F,
    err: Err,
    // check: C,
) -> MathResult<u32>
where
    F: FnOnce(u32, u32) -> Option<u32>,
    Err: FnOnce() -> MathError,
    // C: FnOnce(u32, u32) -> ControlFlow<MathResult<u32>>,
{
    let lhs = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let rhs = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;

    // if let ControlFlow::Break(ret) = check(lhs, rhs) {
    //     return ret;
    // }

    op(lhs, rhs).ok_or_else(err)
}

/// Function for operations on `u64`
pub fn u64_math<'a, F, Err>(
    stack: &mut Stack<MAX_STACK_SIZE, Value<'a>>,
    op: F,
    err: Err,
    // check: C,
) -> MathResult<u64>
where
    F: FnOnce(u64, u64) -> Option<u64>,
    Err: FnOnce() -> MathError,
    // C: FnOnce(u64, u64) -> ControlFlow<MathResult<u64>>,
{
    let lhs_lower = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let lhs_higher = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let rhs_lower = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let rhs_higher = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;

    let lhs: u64 = (lhs_higher as u64) << 32 | lhs_lower as u64;
    let rhs: u64 = (rhs_higher as u64) << 32 | rhs_lower as u64;

    // if let ControlFlow::Break(ret) = check(lhs, rhs) {
    //     return ret;
    // }

    op(lhs, rhs).ok_or_else(err)
}

/// Operations on `f32`
/// This does contain a check function
/// as `f32` operations cannot have any
/// "emergency"
pub fn f32_math<'a, F, Err>(
    stack: &mut Stack<MAX_STACK_SIZE, Value<'a>>,
    op: F,
    err: Err,
) -> MathResult<f32>
where
    F: FnOnce(f32, f32) -> Option<f32>,
    Err: FnOnce() -> MathError,
{
    let lhs = stack
        .pop()?
        .assert_num()
        .ok_or(MathError::ValueNotNumber)
        .map(f32::from_bits)?;

    let rhs = stack
        .pop()?
        .assert_num()
        .ok_or(MathError::ValueNotNumber)
        .map(f32::from_bits)?;

    op(lhs, rhs).ok_or_else(err)
}

/// Operations on `f64`
/// This does contain a check function
/// as `f64` operations cannot have any
/// "emergency"
pub fn f64_math<'a, F, Err>(
    stack: &mut Stack<MAX_STACK_SIZE, Value<'a>>,
    op: F,
    err: Err,
) -> MathResult<f64>
where
    F: FnOnce(f64, f64) -> Option<f64>,
    Err: FnOnce() -> MathError,
{
    let lhs_lower = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let lhs_higher = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let rhs_lower = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;
    let rhs_higher = stack.pop()?.assert_num().ok_or(MathError::ValueNotNumber)?;

    let lhs: f64 = f64::from_bits((lhs_higher as u64) << 32 | lhs_lower as u64);
    let rhs: f64 = f64::from_bits((rhs_higher as u64) << 32 | rhs_lower as u64);

    op(lhs, rhs).ok_or_else(err)
}
