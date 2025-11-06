use crate::errors::TheresError;

#[derive(Copy, Clone)]
pub enum PillError {
    InvalidAssign,
    LocalNotInitialized,
}

impl TheresError for PillError {
    fn message(&self) -> std::borrow::Cow<'static, str> {
        match self {
            Self::InvalidAssign => "cannot assign to this expression",
            Self::LocalNotInitialized => "used variable is uninitialized",
        }
        .into()
    }
}
