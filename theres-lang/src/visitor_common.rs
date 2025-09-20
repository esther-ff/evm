use core::ops::ControlFlow;

pub trait VisitorResult {
    type Return;

    fn normal() -> Self;

    fn into_flow(self) -> ControlFlow<Self::Return>;

    fn into_branch(p: Self::Return) -> Self;
}

impl VisitorResult for () {
    type Return = ();

    fn into_flow(self) -> ControlFlow<Self::Return> {
        ControlFlow::Continue(())
    }

    fn normal() -> Self {}

    fn into_branch((): Self::Return) -> Self {}
}

impl<T> VisitorResult for std::ops::ControlFlow<T> {
    type Return = T;

    fn into_flow(self) -> ControlFlow<Self::Return> {
        self
    }

    fn into_branch(p: Self::Return) -> Self {
        Self::Break(p)
    }

    fn normal() -> Self {
        ControlFlow::Continue(())
    }
}

#[macro_export]
macro_rules! try_visit {
    ($($e:expr),*) => {
        {

        $(
            match $e.into_flow() {
                ::core::ops::ControlFlow::Continue(()) => (),

                ::core::ops::ControlFlow::Break(p) => return $crate::visitor_common::VisitorResult::into_branch(p)

            };



       )*

       Self::Result::normal()
        }
    };
}

#[macro_export]
macro_rules! maybe_visit {
    (v: $v:expr, m: $m: ident, $($e:expr),*) => {$(
       {
        if let Some(thing) = $e {

            $crate::try_visit!($v.$m(thing));

            Self::Result::normal()
        } else {
            Self::Result::normal()
        }
    }
    )*};
}

#[macro_export]
macro_rules! visit_iter {
    (v: $v:expr, m: $m:ident, $($i:expr),*) => {
        $(
            {
                for entry in $i {
                    try_visit!($v.$m(entry));
                }

                Self::Result::normal()
            }
        )*
    };
}
