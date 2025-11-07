use std::borrow::Cow;
use std::cell::RefCell;
use std::panic::Location;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::sources::Sources;
use crate::span::Span;

pub trait TheresError: Copy {
    /// Message describing the error
    fn message(&self) -> Cow<'static, str>;
}

pub struct DiagEmitter<'a> {
    inner: RefCell<DiagEmitterInner<'a>>,
}

impl<'a> DiagEmitter<'a> {
    pub fn new(srcs: &'a Sources) -> Self {
        Self {
            inner: RefCell::new(DiagEmitterInner::new(srcs)),
        }
    }

    #[track_caller]
    pub fn emit_err(&self, err: impl TheresError, span: Span) {
        log::trace!("`emit_err` triggered at loc: {}", Location::caller());
        self.inner.borrow_mut().emit_err(err, span);
    }

    pub fn errors_emitted(&self) -> bool {
        self.inner.borrow().err_amount > 0
    }

    // pub fn wipe_errors(&self) {
    //     self.inner.borrow_mut().err_amount = 0;
    // }
}

pub struct DiagEmitterInner<'a> {
    srcs: &'a Sources,
    err_amount: usize,
}

impl<'a> DiagEmitterInner<'a> {
    fn new(srcs: &'a Sources) -> Self {
        Self {
            srcs,
            err_amount: 0,
        }
    }

    fn emit_err(&mut self, err: impl TheresError, span: Span) {
        let diag = Diagnostic::error()
            .with_message(err.message())
            .with_label(Label::primary(
                span.sourceid.to_usize(),
                (span.start as usize)..(span.end as usize),
            ));
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        codespan_reporting::term::emit_to_write_style(
            &mut writer.lock(),
            &config,
            self.srcs.files(),
            &diag,
        )
        .unwrap();
    }
}

// fn _longest_line_number_from_origin(origin: usize, jump: usize) -> u32 {
//     let mut up = origin;

//     for _ in 0..jump {
//         let tmp = up.saturating_sub(1);
//         up = cmp::max(up, tmp);
//     }

//     let mut down = origin;

//     for _ in 0..jump {
//         let tmp = down.saturating_add(1);
//         down = cmp::max(up, tmp);
//     }

//     let len_upper = up.checked_ilog10().unwrap_or(2) + 1;
//     let down_upper = down.checked_ilog10().unwrap_or(2) + 1;

//     cmp::max(len_upper, down_upper)
// }
