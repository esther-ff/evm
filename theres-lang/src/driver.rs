use crate::air;
use crate::air::check;
use crate::arena::Arena;
use crate::ast::PrettyPrinter;
use crate::ast::Universe;
use crate::errors::DiagEmitter;
use crate::lexer::{Lexemes, Lexer};
use crate::session::Session;
use crate::sources::{FileManager, SourceId, Sources};
use crate::types::fun_cx::typeck_universe;

use std::io::{Stderr, Write, stderr, stdout};
use std::path::Path;
use std::sync::Mutex;

use log::{Level, Log};

struct TheresLog {
    stderr: Stderr,
    log_level: Level,

    log_file_string: Mutex<(String, u32)>,
}

impl TheresLog {
    fn setup(log_level: Level) {
        let me = TheresLog {
            stderr: stderr(),
            log_level,
            log_file_string: Mutex::new((String::new(), 0)),
        };

        log::set_boxed_logger(Box::new(me)).expect("failed to set up logging!");
        log::set_max_level(log::LevelFilter::Trace);
    }

    fn log_inner(&self, record: &log::Record) -> std::io::Result<()> {
        if !self.enabled(record.metadata()) {
            return Ok(());
        }

        let mut cached = self.log_file_string.lock().unwrap();
        let mut stderr = self.stderr.lock();
        let filename = record.file().unwrap_or("<anon>");
        let line_nr = record.line().unwrap_or_default();

        if cached.0.as_str() != filename && cached.1 != line_nr {
            writeln!(
                stderr,
                "\n({filename} @ line {line}):",
                line = record.line().unwrap_or(0),
            )?;

            cached.0.clear();
            cached.0.push_str(filename);
            cached.1 = line_nr;
            drop(cached);
        }

        writeln!(stderr, "{}: {msg}", record.level(), msg = record.args())
    }
}

impl Log for TheresLog {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        metadata.level() <= self.log_level
    }

    fn log(&self, record: &log::Record) {
        self.log_inner(record).expect("logging failed!");
    }

    fn flush(&self) {}
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
    pub dump_eair: bool,
    pub dump_pill: bool,
    pub log_level: Level,
}

pub struct Compiler {
    sources: Sources,
    flags: Flags,
}

impl Compiler {
    pub fn new(manager: impl FileManager + 'static, flags: Flags) -> Self {
        Self {
            sources: Sources::new(Box::new(manager)),
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
        let lexemes = self.lex(src, &diags);
        let ast = self.parse_to_ast(lexemes, &diags);
        let arena = Arena::new();
        let (uni, map) = air::lower_universe(&arena, &diags, &ast);

        Session::new(&diags, self.flags, &self.sources, &arena, map).enter(|session| {
            air::dump_air(&mut stdout(), self.flags.dump_hir, uni, session.air_map()).unwrap();
            typeck_universe(session, uni);
            let main_did = check::check_for_main(session, uni).expect("todo: no main lmao!");

            if diags.errors_emitted() {
                return;
            }

            let pill = session.build_pill(main_did);
            crate::pill::dataflow::analyze_maybe_init_variables(pill.cfg());

            if diags.errors_emitted() {
                return;
            }

            let to_build = crate::pill::collect_build::collect_build_items(session, main_did);
            dbg!(to_build);
        });
    }

    fn lex<'a>(&'a self, src: SourceId, diag: &'a DiagEmitter<'a>) -> Lexemes {
        Lexer::new(self.sources.get_by_source_id(src).data(), src, diag).lex()
    }

    fn parse_to_ast<'a>(&self, lexemes: Lexemes, diag: &'a DiagEmitter<'a>) -> Universe {
        let decls = crate::parser::parse(lexemes, diag);

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
