use std::{
    borrow::Cow,
    cell::RefCell,
    cmp,
    io::{self, BufWriter, Stderr, Write},
};

use crate::{
    lexer::{LexError, Span},
    parser::{ParseError, ParseErrorKind},
    sources::{SourceFile, SourceId, Sources},
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
            ParseErrorKind::Expected { what, got } => {
                format!("expected {what} but got: {got:?}").into()
            }

            ParseErrorKind::ExpectedUnknown { what } => format!("got {what}").into(),

            ParseErrorKind::EndOfFile => "unexpected end-of-file".into(),

            ParseErrorKind::WrongUnaryOp { offender } => {
                format!("can't execute {offender:?} as unary operator").into()
            }

            ParseErrorKind::FunctionWithoutBody => {
                "this function is supposed to have a body".into()
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
        writeln!(writer, "{msg:>msg_indent$}", msg = self.msg)?;

        writeln!(writer, "{:<indent$}| ", " ")
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
            line_number,

            content,
            msg,
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

pub struct DiagEmitter<'a> {
    inner: RefCell<DiagEmitterInner<'a>>,
}

impl<'a> DiagEmitter<'a> {
    pub fn new(srcs: &'a Sources) -> Self {
        Self {
            inner: RefCell::new(DiagEmitterInner::new(srcs)),
        }
    }

    pub fn emit_err(&self, err: impl TheresError, span: Span) {
        self.inner
            .borrow_mut()
            .emit_err(err, span)
            .expect("writing to `stderr` failed!");
    }

    pub fn errors_emitted(&self) -> bool {
        self.inner.borrow().err_amount > 0
    }
}

pub struct DiagEmitterInner<'a> {
    stderr: BufWriter<Stderr>,
    err_amount: usize,
    srcs: &'a Sources,
}

impl<'a> DiagEmitterInner<'a> {
    fn new(srcs: &'a Sources) -> Self {
        Self {
            stderr: BufWriter::new(std::io::stderr()),
            err_amount: 0,
            srcs,
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn emit_err<T: TheresError>(&mut self, err: T, span: Span) -> io::Result<()> {
        let origin = span.line as usize;
        let extra_lines = T::amount_of_extra_lines();
        let line_nr_offset = origin.saturating_sub(extra_lines);
        let lines = self.get_lines(span.sourceid, origin, extra_lines);
        let indent = longest_line_number_from_origin(origin, extra_lines) as usize;

        writeln!(self.stderr, "{} error! aaaah!", T::phase())?;

        for (ix, line) in lines.iter().enumerate() {
            let line_number = ix + line_nr_offset;
            if line_number == origin {
                print_to(
                    line_number,
                    line,
                    indent,
                    &mut self.stderr,
                    Some(Message {
                        msg: err.message(),
                        attached_to: span,
                    }),
                )
                .expect("writing to writer failed!");

                continue;
            }

            print_to(line_number, line, indent, &mut self.stderr, None)
                .expect("writing to writer failed!");
        }

        self.err_amount += 1;

        writeln!(self.stderr).unwrap();

        Ok(())
    }

    fn get_lines(&self, id: SourceId, line_origin: usize, extra: usize) -> Vec<&'a str> {
        self.srcs
            .get_by_source_id(id)
            .get_lines_above_below(line_origin, extra)
            .expect("Given line number isn't present in the source file")
    }
}

pub struct Errors<'e, T, O> {
    errs: &'e [T],
    writer: &'e mut O,
}

impl<'e, T, O> Errors<'e, T, O> {
    pub fn new(errs: &'e [T], writer: &'e mut O) -> Self {
        Self { errs, writer }
    }
}

impl<T, O> Errors<'_, T, O>
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

            // this is going to be removed anyway so yeah
            let _ = print_to(ix, line, indent as usize, &mut self.writer, msg);
        }

        Ok(())
    }
}

fn longest_line_number_from_origin(origin: usize, jump: usize) -> u32 {
    let mut up = origin;

    for _ in 0..jump {
        let tmp = up.saturating_sub(1);
        up = cmp::max(up, tmp);
    }

    let mut down = origin;

    for _ in 0..jump {
        let tmp = down.saturating_add(1);
        down = cmp::max(up, tmp);
    }

    let len_upper = up.checked_ilog10().unwrap_or(2) + 1;
    let down_upper = down.checked_ilog10().unwrap_or(2) + 1;

    cmp::max(len_upper, down_upper)
}

fn print_to<O>(
    line_nr: usize,
    content: &str,
    indent: usize,
    writer: &mut O,
    msg: Option<Message>,
) -> io::Result<()>
where
    O: io::Write,
{
    writeln!(writer, "{line_nr:<indent$}| {content}",)?;

    msg.map_or(Ok(()), |m| m.print_to(indent, writer))
}
