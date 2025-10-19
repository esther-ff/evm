use crate::air::def::{DefId, IntTy};
use crate::air::node::Constant;
use crate::errors::{Phase, TheresError};
use crate::pooled::Pooled;
use crate::session::cx;
use crate::span::Span;
use crate::symbols::SymbolId;
use crate::types::fun_cx::{FieldSlice, InferId};
use core::panic;
use std::borrow::Cow;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Deref;

/// Interned type for a particular something.

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty<'ty>(pub Pooled<'ty, TyKind<'ty>>);

impl Debug for Ty<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<'ty> Deref for Ty<'ty> {
    type Target = TyKind<'ty>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Interned data about an instance.
pub type Instance<'ty> = Pooled<'ty, InstanceDef<'ty>>;

/// Interned function signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnSig<'ty> {
    pub inputs: &'ty [Ty<'ty>],
    pub output: Ty<'ty>,
}

impl Display for FnSig<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("fun(")?;
        for (ix, ty) in self.inputs.iter().enumerate() {
            <Ty<'_> as Display>::fmt(ty, f)?;
            if ix != self.inputs.len() - 1 {
                f.write_str(", ")?;
            }
        }
        write!(f, ") => {}", self.output)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LambdaEnv<'ty> {
    pub all_inputs: &'ty [Ty<'ty>],
    pub output: Ty<'ty>,
    pub did: DefId,
    pub span: Span,
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

    Lambda(&'ty LambdaEnv<'ty>),
}

impl<'ty> TyKind<'ty> {
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

    pub fn is_error(self) -> bool {
        matches!(self, TyKind::Error)
    }

    pub fn is_signed_int(self) -> bool {
        matches!(self, TyKind::Int(..))
    }

    pub fn maybe_infer(self) -> Option<InferTy> {
        if let TyKind::InferTy(i) = self {
            return Some(i);
        }

        None
    }

    pub fn is_nil(self) -> bool {
        matches!(self, TyKind::Nil)
    }

    #[track_caller]
    pub fn expect_instance(&self) -> Instance<'ty> {
        let TyKind::Instance(def) = *self else {
            panic!("expected instance but got different ty!")
        };

        def
    }

    #[track_caller]
    pub fn expect_lambda(&self) -> LambdaEnv<'ty> {
        let TyKind::Lambda(env) = *self else {
            panic!("expected lambda but got different ty!")
        };

        *env
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

    pub fn id(self) -> InferId {
        self.vid
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
pub enum TypingError<'ty> {
    TypeMismatch(Ty<'ty>, Ty<'ty>),

    NoIndexOp {
        on: Ty<'ty>,
    },

    NoUnaryOp {
        on: Ty<'ty>,
    },

    NoBinaryOp {
        lhs: Ty<'ty>,
        rhs: Ty<'ty>,
    },

    CallingNotFn {
        offender: Ty<'ty>,
    },

    WrongArgumentTy {
        expected: Ty<'ty>,
        got: Ty<'ty>,
        arg_idx: usize,
    },

    WrongArgumentAmnt {
        amount_given: usize,
        amount_req: usize,
    },

    NoField {
        on: Ty<'ty>,
        field_name: SymbolId,
    },

    NotInstance {
        got: Ty<'ty>,
    },

    MethodNotFound {
        on_ty: Ty<'ty>,
        method_name: Cow<'static, str>,
    },

    InferFail,
}

impl TheresError for TypingError<'_> {
    fn phase() -> Phase {
        Phase::TypeCk
    }

    fn message(&self) -> Cow<'static, str> {
        match self {
            TypingError::TypeMismatch(expected, got) => {
                format!("Expected type: {expected}, got: {got}")
            }
            TypingError::InferFail => "inference failed!".into(),
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

impl Display for Ty<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match **self {
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
            TyKind::Nil => "nil",
            TyKind::Error => "{type error!}",

            TyKind::Diverges => "diverges",

            TyKind::Fn { inputs, output } => {
                write!(f, "fun(")?;
                for (ix, ty) in inputs.iter().enumerate() {
                    write!(f, "{ty}")?;
                    if ix != inputs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                return write!(f, ") => {output}");
            }

            TyKind::Instance(def) => {
                return write!(f, "{}", def.name.get_interned());
            }

            TyKind::Array(ty) => {
                return write!(f, "[{ty}]");
            }

            TyKind::FnDef(did) => {
                use crate::session::Session;

                fn inner<'cx>(cx: &'cx Session<'cx>, f: &mut Formatter, did: DefId) -> fmt::Result {
                    let sym = cx.air_get_fn(did).1;
                    let typed_sig = cx.fn_sig_for(did);
                    write!(f, "fun {name}(", name = sym.get_interned())?;

                    for (ix, ty) in typed_sig.inputs.iter().enumerate() {
                        write!(f, "{ty}")?;
                        if ix != typed_sig.inputs.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }

                    write!(f, ") => {}", typed_sig.output)
                }

                return cx(|cx| inner(cx, f, did));
            }

            TyKind::InferTy(infer) => {
                return match infer.kind {
                    InferKind::Float => write!(f, "?{}:f", infer.vid.to_usize()),
                    InferKind::Integer => write!(f, "?{}:i", infer.vid.to_usize()),
                    InferKind::Regular => write!(f, "?{}:t", infer.vid.to_usize()),
                };
            }

            TyKind::Lambda(lambda) => {
                return cx(|cx| {
                    let lambda = cx.air_get_lambda(lambda.did);
                    write!(f, "{{lambda <=> {span}}}", span = lambda.span)
                });
            }
        };

        f.write_str(str)
    }
}

impl<'cx> crate::session::Session<'cx> {
    pub fn intern_ty(&'cx self, ty: TyKind<'cx>) -> Ty<'cx> {
        let ty = self.interned_types.borrow_mut().pool(ty, self.arena());
        Ty(ty)
    }
}
