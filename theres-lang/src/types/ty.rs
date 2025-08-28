use crate::errors::TheresError;
use crate::hir::def::{DefId, IntTy};
use crate::hir::node::Constant;
use crate::session::{Pooled, Session, SymbolId};
use crate::types::fun_cx::{FieldSlice, InferId};
use std::borrow::Cow;

/// Interned type for a particular something.
pub type Ty<'ty> = Pooled<'ty, TyKind<'ty>>;

/// Interned data about an instance.
pub type Instance<'ty> = Pooled<'ty, InstanceDef<'ty>>;

/// Interned function signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnSig<'ty> {
    pub inputs: &'ty [Ty<'ty>],
    pub output: Ty<'ty>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind<'ty> {
    Bool,
    Uint(IntTy),
    Int(IntTy),

    Float,
    Double,

    /// Instances somehow idk lol !
    Instance(Instance<'ty>),

    /// fun(ty) -> ty
    Fn {
        inputs: &'ty [Ty<'ty>],
        output: Ty<'ty>,
    },

    /// Anon type of function def
    FnDef(DefId),

    /// `[ty]`
    Array(Ty<'ty>),

    /// nil.
    Nil,

    /// Type wasn't properly formed.
    Error,

    /// Diverging computation
    Diverges,

    /// For inference
    InferTy(InferTy),
}

impl TyKind<'_> {
    pub fn is_integer_like(self) -> bool {
        matches!(
            self,
            TyKind::Uint(..)
                | TyKind::Int(..)
                | TyKind::InferTy(InferTy {
                    kind: InferKind::Integer,
                    ..
                })
        )
    }

    pub fn is_float_like(self) -> bool {
        matches!(
            self,
            TyKind::Float
                | TyKind::Double
                | TyKind::InferTy(InferTy {
                    kind: InferKind::Float,
                    ..
                })
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InferTy {
    pub vid: InferId,
    pub kind: InferKind,
}

impl InferTy {
    pub fn is_regular(self) -> bool {
        self.kind == InferKind::Regular
    }

    pub fn is_float(self) -> bool {
        self.kind == InferKind::Float
    }

    pub fn is_integer(self) -> bool {
        self.kind == InferKind::Integer
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InferKind {
    Float,
    Integer,
    Regular,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceDef<'ty> {
    pub fields: &'ty FieldSlice<FieldDef>,
    pub name: SymbolId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldDef {
    pub mutable: Constant,
    pub name: SymbolId,
    pub def_id: DefId,
}

#[derive(Debug, Clone)]
pub enum TypingError {
    TypeMismatch(Cow<'static, str>, Cow<'static, str>),

    NoIndexOp {
        on: Cow<'static, str>,
    },

    NoUnaryOp {
        on: Cow<'static, str>,
    },

    NoBinaryOp {
        lhs: Cow<'static, str>,
        rhs: Cow<'static, str>,
    },

    CallingNotFn {
        offender: Cow<'static, str>,
    },

    WrongArgumentTy {
        expected: Cow<'static, str>,
        got: Cow<'static, str>,
        arg_idx: usize,
    },

    WrongArgumentAmnt {
        amount_given: usize,
        amount_req: usize,
    },

    NoField {
        on: Cow<'static, str>,
        field_name: SymbolId,
    },

    NotInstance {
        got: Cow<'static, str>,
    },

    MethodNotFound {
        on_ty: Cow<'static, str>,
        method_name: Cow<'static, str>,
    },
}

impl TheresError for TypingError {
    fn phase() -> &'static str {
        "typing"
    }

    fn message(&self) -> Cow<'static, str> {
        match self {
            TypingError::TypeMismatch(expected, got) => {
                format!("Expected type: {expected}, got: {got}")
            }
            TypingError::NoIndexOp { on } => format!("No index operation for type: {on}"),
            TypingError::NoUnaryOp { on } => format!("No unary operation for type: {on}"),
            TypingError::NoBinaryOp { lhs, rhs } => {
                format!("No binary operation like that for type {lhs} and {rhs}")
            }
            TypingError::CallingNotFn { offender } => format!("Attempting to call type {offender}"),
            TypingError::WrongArgumentTy {
                expected,
                got,
                arg_idx,
            } => format!("Argument {arg_idx} has type {got}, but expected type was: {expected}"),
            TypingError::WrongArgumentAmnt {
                amount_given,
                amount_req,
            } => {
                format!("Invalid amount of arguments, got: {amount_given}, expected: {amount_req}")
            }
            TypingError::NotInstance { got } => {
                format!("Attempted to access a field on type {got}")
            }
            TypingError::NoField { on, field_name } => {
                format!(
                    "There is no field {} on type {on}",
                    field_name.get_interned()
                )
            }
            TypingError::MethodNotFound { on_ty, method_name } => {
                format!("No method named {method_name} present on type {on_ty}")
            }
        }
        .into()
    }
}

pub fn display_ty<'a>(session: &'a Session<'a>, ty: Ty<'a>) -> Cow<'static, str> {
    let mut buf = String::new();

    match ty.0 {
        TyKind::Bool => Cow::Borrowed("bool"),
        TyKind::Uint(size) => match size {
            IntTy::N8 => Cow::Borrowed("u8"),
            IntTy::N16 => Cow::Borrowed("u16"),
            IntTy::N32 => Cow::Borrowed("u32"),
            IntTy::N64 => Cow::Borrowed("u64"),
        },
        TyKind::Int(size) => match size {
            IntTy::N8 => Cow::Borrowed("i8"),
            IntTy::N16 => Cow::Borrowed("i16"),
            IntTy::N32 => Cow::Borrowed("i32"),
            IntTy::N64 => Cow::Borrowed("i64"),
        },
        TyKind::Float => Cow::Borrowed("f32"),
        TyKind::Double => Cow::Borrowed("f64"),
        TyKind::Nil => Cow::Borrowed("Nil"),
        TyKind::Error => Cow::Borrowed("{type error!}"),

        TyKind::Diverges => Cow::Borrowed("Diverges"),

        any => {
            stringfy_string_helper(session, &mut buf, *any);
            Cow::Owned(buf)
        }
    }
}

fn stringfy_string_helper<'a>(session: &'a Session<'a>, buf: &mut String, ty: TyKind<'a>) {
    use std::fmt::Write;

    let push = match ty {
        TyKind::Bool => "bool",
        TyKind::Uint(size) => match size {
            IntTy::N8 => "u8",
            IntTy::N16 => "u16",
            IntTy::N32 => "u32",
            IntTy::N64 => "u64",
        },
        TyKind::Int(size) => match size {
            IntTy::N8 => "i8",
            IntTy::N16 => "i16",
            IntTy::N32 => "i32",
            IntTy::N64 => "i64",
        },
        TyKind::Float => "f32",
        TyKind::Double => "f64",
        TyKind::Nil => "Nil",

        TyKind::Diverges => "Diverges",

        TyKind::Array(ty) => {
            buf.push('[');
            stringfy_string_helper(session, buf, *ty);
            buf.push(']');
            return;
        }

        TyKind::Fn { inputs, output } => {
            buf.push_str("fun(");
            for (ix, i) in inputs.iter().enumerate() {
                stringfy_string_helper(session, buf, **i);

                if ix != inputs.len() {
                    buf.push_str(", ");
                }
            }
            buf.push(')');
            buf.push_str("=> ");
            stringfy_string_helper(session, buf, *output);

            return;
        }

        TyKind::Instance(def) => {
            buf.push_str(def.name.get_interned());
            return;
        }

        TyKind::FnDef(def_id) => {
            let sig = session.fn_sig_for(def_id);
            let _ = write!(buf, "fun (",);

            for (ix, ty) in sig.inputs.iter().enumerate() {
                stringfy_string_helper(session, buf, **ty);

                if ix == sig.inputs.len() {
                    buf.push_str(", ");
                }
            }

            buf.push(')');
            buf.push_str(" => ");
            stringfy_string_helper(session, buf, *sig.output);

            return;
        }

        TyKind::Error => "{type error!}",

        TyKind::InferTy(infer) => {
            return match infer.kind {
                InferKind::Float => write!(buf, "{{float: {}?}}", infer.vid.to_usize()),
                InferKind::Integer => {
                    write!(buf, "{{integer: {}?}}", infer.vid.to_usize())
                }
                InferKind::Regular => write!(buf, "{}?", infer.vid.to_usize()),
            }
            .expect("writing to a `String` never fails");
        }
    };

    buf.push_str(push);
}
