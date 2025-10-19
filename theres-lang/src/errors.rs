use std::borrow::Cow;
use std::cell::RefCell;
use std::cmp;
use std::fmt::Display;
use std::io::{self, BufWriter, Stderr};
use std::panic::Location;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::session::cx;
use crate::sources::{SourceId, Sources};
use crate::span::Span;

pub enum Phase {
    Lexing,
    Parsing,
    NameResolution,
    LoweringAst,
    TypeCk,
    LoweringHir,
}

impl Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Lexing => "lexing",
            Self::Parsing => "parsing",
            Self::NameResolution => "name resolution",
            Self::LoweringAst => "lowering the ast",
            Self::TypeCk => "type checking",
            Self::LoweringHir => "lowering the hir",
        };

        write!(f, "{str}")
    }
}

pub trait TheresError {
    /// Phase of compilation the error was found in
    /// like "lexing" or "parsing"
    fn phase() -> Phase;

    /// Message describing the error
    fn message(&self) -> Cow<'static, str>;
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
        let msg_indent = self
            .attached_to
            .end()
            .saturating_sub(self.attached_to.start()) as usize;
        writeln!(writer, "{:<indent$}| ", " ")?;
        write!(writer, "{:<indent$}| ", " ")?;
        writeln!(writer, "{msg:>msg_indent$}", msg = self.msg)?;

        writeln!(writer, "{:<indent$}| ", " ")
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

    #[track_caller]
    pub fn emit_err(&self, err: impl TheresError, span: Span) {
        log::trace!("`emit_err` triggered at loc: {}", Location::caller());
        self.inner.borrow_mut().emit_err(err, span);
    }

    pub fn errors_emitted(&self) -> bool {
        self.inner.borrow().err_amount > 0
    }

    pub fn wipe_errors(&self) {
        self.inner.borrow_mut().err_amount = 0;
    }
}

pub struct DiagEmitterInner<'a> {
    stderr: BufWriter<Stderr>,
    err_amount: usize,
    srcs: &'a Sources,
}

const EXTRA_LINES: usize = 2;

impl<'a> DiagEmitterInner<'a> {
    fn new(srcs: &'a Sources) -> Self {
        Self {
            stderr: BufWriter::new(std::io::stderr()),
            err_amount: 0,
            srcs,
        }
    }

    // #[allow(clippy::needless_pass_by_value)]
    // #[track_caller]
    // fn emit_err<T: TheresError>(&mut self, err: T, span: Span) -> io::Result<()> {
    // let origin = span.line as usize;
    // let line_nr_offset = origin.saturating_sub(EXTRA_LINES);
    // let lines = self.get_lines(span.sourceid, origin, EXTRA_LINES);
    // let indent = longest_line_number_from_origin(origin, EXTRA_LINES) as usize;

    // writeln!(self.stderr, "{} error! aaaah!", T::phase())?;

    // for (ix, line) in lines.iter().enumerate() {
    //     let line_number = ix + line_nr_offset;
    //     if line_number == origin {
    //         print_to(
    //             line_number,
    //             line,
    //             indent,
    //             &mut self.stderr,
    //             Some(Message {
    //                 msg: err.message(),
    //                 attached_to: span,
    //             }),
    //         )
    //         .expect("writing to writer failed!");

    //         continue;
    //     }

    //     print_to(line_number, line, indent, &mut self.stderr, None)
    //         .expect("writing to writer failed!");
    // }

    // self.err_amount += 1;

    // writeln!(self.stderr).unwrap();

    // // later remove
    // self.stderr.flush()?;

    // Ok(())
    // }

    #[allow(clippy::needless_pass_by_value)]
    #[allow(clippy::unused_self)]
    fn emit_err(&mut self, err: impl TheresError, span: Span) {
        let diag = Diagnostic::error()
            .with_message(err.message())
            .with_label(Label::primary(
                span.sourceid.to_usize(),
                (span.start as usize)..(span.end as usize),
            ));
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        cx(|cx| {
            codespan_reporting::term::emit_to_write_style(
                &mut writer.lock(),
                &config,
                cx.sources().files(),
                &diag,
            )
            .unwrap();
        });
    }

    fn get_lines(&self, id: SourceId, line_origin: usize, extra: usize) -> Vec<&'a str> {
        self.srcs
            .get_by_source_id(id)
            .get_lines_above_below(line_origin, extra)
            .expect("Given line number isn't present in the source file")
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
