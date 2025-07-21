use std::{borrow::Cow, cmp, io};

use crate::{
    lexer::{LexError, Span},
    parser::ParseError,
    sources::SourceFile,
};

pub trait TheresError {
    /// Phase of compilation the error was found in
    /// like "lexing" or "parsing"
    fn phase() -> &'static str;

    /// Span of the error
    fn span(&self) -> Span;

    /// Message describing the error
    fn message(&self) -> Cow<'static, str>;

    /// Amount of extra lines to show from the line
    /// where the error originated
    ///
    /// Default is 2
    fn amount_of_extra_lines() -> usize {
        2
    }
}

impl TheresError for ParseError {
    fn phase() -> &'static str {
        "parsing"
    }

    fn span(&self) -> Span {
        self.token_span
    }

    fn message(&self) -> Cow<'static, str> {
        match self.kind {
            crate::parser::ParseErrorKind::Expected { what, got } => {
                format!("expected {what} but got: {got:?}").into()
            }

            crate::parser::ParseErrorKind::ExpectedUnknown { what } => format!("got {what}").into(),

            crate::parser::ParseErrorKind::EndOfFile => "unexpected end-of-file".into(),

            crate::parser::ParseErrorKind::WrongUnaryOp { offender } => {
                format!("can't execute {offender:?} as unary operator").into()
            }
        }
    }
}

impl TheresError for LexError {
    fn phase() -> &'static str {
        "lexing"
    }

    fn span(&self) -> Span {
        self.span
    }

    fn message(&self) -> Cow<'static, str> {
        dbg!(self);
        "error occured, todo! this message!".into()
    }
}

pub struct Message {
    msg: Cow<'static, str>,
    attached_to: Span,
}

impl Message {
    pub fn print_to<O>(&self, indent: usize, writer: &mut O) -> io::Result<()>
    where
        O: io::Write,
    {
        let msg_indent = self.attached_to.end() - self.attached_to.start();
        writeln!(writer, "{:<indent$}| ", " ")?;
        write!(writer, "{:<indent$}| ", " ")?;
        writeln!(writer, "{msg:>msg_indent$}", msg = self.msg)
    }
}

pub struct ErrorLine<'a> {
    line_number: usize,
    content: &'a str,
    msg: Option<Message>,
}

impl<'a> ErrorLine<'a> {
    pub fn new(msg: Option<Message>, content: &'a str, line_number: usize) -> Self {
        Self {
            msg,
            content,
            line_number,
        }
    }
    pub fn print_to<O>(&self, indent: usize, writer: &mut O) -> io::Result<()>
    where
        O: io::Write,
    {
        writeln!(
            writer,
            "{line_nr:<indent$}| {content}",
            line_nr = self.line_number,
            content = self.content
        )?;

        if let Some(ref msg) = self.msg {
            msg.print_to(indent, writer)?;
        }

        Ok(())
    }
}

pub struct Errors<'e, T, O> {
    errs: &'e [T],
    writer: &'e mut O,
}

impl<'e, T, O> Errors<'e, T, O> {
    pub fn new(errs: &'e [T], writer: &'e mut O) -> Self {
        Self { writer, errs }
    }
}

impl<'e, T, O> Errors<'e, T, O>
where
    T: TheresError,
    O: io::Write,
{
    pub fn print_all(&mut self, srcs: &SourceFile) -> io::Result<()> {
        for err in self.errs {
            self.print_one(err, srcs)?;
        }

        Ok(())
    }

    fn print_one(&mut self, err: &T, srcs: &SourceFile) -> io::Result<()> {
        let origin = err.span().line as usize;
        let Some(lines) = srcs.get_lines_above_below(origin, T::amount_of_extra_lines()) else {
            panic!("cannot print out error in `print_one`, span is not present in the error")
        };

        let indent = longest_line_number_from_origin(origin, T::amount_of_extra_lines());

        dbg!(indent);
        dbg!(origin);
        writeln!(self.writer, "error during {}:", T::phase())?;
        for (ix, line) in lines.iter().enumerate().map(|(ix, line)| {
            (
                ix + (origin.saturating_sub(T::amount_of_extra_lines())),
                line,
            )
        }) {
            let msg = if ix == origin {
                let msg = Message {
                    msg: err.message(),
                    attached_to: err.span(),
                };

                Some(msg)
            } else {
                None
            };

            let errline = ErrorLine::new(msg, line, ix);

            errline.print_to(indent as usize, self.writer)?;
        }

        Ok(())
    }
}

fn longest_line_number_from_origin(origin: usize, jump: usize) -> u32 {
    let mut up = origin;

    for _ in 0..jump {
        let tmp = up.saturating_sub(1);
        up = cmp::max(up, tmp)
    }

    dbg!(up);

    let mut down = origin;

    for _ in 0..jump {
        let tmp = down.saturating_add(1);
        down = cmp::max(up, tmp)
    }

    dbg!(down);
    let len_upper = up.checked_ilog10().unwrap_or(2) + 1;
    let down_upper = down.checked_ilog10().unwrap_or(2) + 1;

    cmp::max(len_upper, down_upper)
}
