use std::{
    cell::Cell,
    io::{Stderr, Write, stderr, stdout},
    path::Path,
    sync::RwLock,
};

use crate::{
    ast::Universe,
    ast_pretty_printer::PrettyPrinter,
    errors::DiagEmitter,
    hir,
    lexer::{Lexemes, Lexer},
    parser::Parser,
    session::Session,
    sources::{FileManager, SourceId, Sources},
    ty::typeck_universe,
};

use log::{Level, Log};

pub const LOG_AMOUNT_TO_RELEASE: usize = 10;

pub struct LogBuffer {
    buffer: Vec<u8>,
    indices: Vec<(usize, usize)>,
    buffered_logs: usize,
}

impl Write for LogBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let start = self.indices.last().map_or(0, |(_, end)| *end);
        let end = start + buf.len();

        self.indices.push((start, end));
        self.buffer.extend_from_slice(buf);

        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub struct TheresLog {
    stderr: Stderr,
    log_level: Level,
    log_buffer: RwLock<LogBuffer>,
}

impl TheresLog {
    pub fn setup(log_level: Level) {
        let me = TheresLog {
            stderr: stderr(),

            log_level,

            log_buffer: RwLock::new(LogBuffer {
                buffer: Vec::with_capacity(4096),
                indices: Vec::with_capacity(4096),

                buffered_logs: 0,
            }),
        };

        log::set_boxed_logger(Box::new(me)).expect("failed to set up logging!");
        log::set_max_level(log::LevelFilter::Trace);
    }

    fn flush_buffers(&self) -> bool {
        let mut stderr = self.stderr.lock();
        let reader = self.log_buffer.read().unwrap();
        let mut should_clear_buffers = false;

        if reader.buffered_logs >= LOG_AMOUNT_TO_RELEASE {
            for (start, end) in reader.indices.iter().copied() {
                let data = reader
                    .buffer
                    .get(start..end)
                    .expect("indices given were invalid!");

                stderr.write_all(data).expect("stderr writing failed.");
            }

            should_clear_buffers = true;
        }

        should_clear_buffers
    }
}

impl Log for TheresLog {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        metadata.level() <= self.log_level
    }

    fn log(&self, record: &log::Record) {
        let should_clear_buffers = self.flush_buffers();
        let mut writer = self.log_buffer.write().unwrap();

        if should_clear_buffers {
            writer.buffer.clear();
            writer.indices.clear();
        }

        let _ = writeln!(
            self.stderr.lock(),
            "{} @ ({filename}@{line}): {msg}",
            record.level(),
            line = record.line().unwrap_or(0),
            filename = record.file().unwrap_or("<anon>"),
            msg = record.args()
        );
    }

    fn flush(&self) {
        let mut stderr = self.stderr.lock();
        let reader = self.log_buffer.read().unwrap();
        for (start, end) in reader.indices.iter().copied() {
            let data = reader
                .buffer
                .get(start..end)
                .expect("indices given were invalid!");

            stderr.write_all(data).expect("stderr writing failed.");
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum HirDump {
    All,
    OnlyItems,
    None,
}

#[derive(Debug, Clone, Copy)]
#[allow(clippy::struct_field_names)]
pub struct Flags {
    pub dump_hir: HirDump,
    pub dump_ast: bool,
    pub dump_types: bool,
    pub log_level: Level,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Compilation {
    Error,
    Ok,
}

pub struct Compiler {
    sources: Sources,

    state: Cell<Compilation>,

    flags: Flags,
}

impl Compiler {
    pub fn new(manager: impl FileManager + 'static, flags: Flags) -> Self {
        Self {
            sources: Sources::new(Box::new(manager)),
            state: Cell::new(Compilation::Ok),
            flags,
        }
    }

    pub fn start<A>(&mut self, main: A)
    where
        A: AsRef<Path>,
    {
        TheresLog::setup(self.flags.log_level);

        let Ok(src) = self.sources.open(main.as_ref()) else {
            eprintln!("Failed to open file: {}", main.as_ref().display());
            return;
        };

        let diags = DiagEmitter::new(&self.sources);
        let session = Session::new(&diags, self.flags);
        let lexemes = self.lex(src, &diags);
        let ast = self.parse_to_ast(lexemes, &diags);

        session.enter(|session| {
            let uni = hir::lower_universe(session, &ast);
            typeck_universe(session, uni);
        });
    }

    fn lex<'a>(&'a self, src: SourceId, diag: &'a DiagEmitter<'a>) -> Lexemes {
        let lexemes = {
            let lexer = Lexer::new(self.sources.get_by_source_id(src).data(), src, diag);
            lexer.lex()
        };

        if diag.errors_emitted() {
            self.state.set(Compilation::Error);
        }

        lexemes
    }

    fn parse_to_ast<'a>(&self, lexemes: Lexemes, diag: &'a DiagEmitter<'a>) -> Universe {
        let decls = Parser::new(lexemes, diag).parse();

        if diag.errors_emitted() {
            self.state.set(Compilation::Error);
        }

        let mut stdout = stdout();

        if self.flags.dump_ast {
            let mut p = PrettyPrinter::new(&mut stdout);
            p.travel(&decls);
        }

        decls
    }
}

impl Drop for Compiler {
    fn drop(&mut self) {
        log::logger().flush();
    }
}
