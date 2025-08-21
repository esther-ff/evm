use std::{
    cell::Cell,
    io::{self, stdout},
    path::Path,
};

use crate::{
    ast::Universe,
    ast_pretty_printer::PrettyPrinter,
    errors::{DiagEmitter, Errors},
    hir,
    lexer::{Lexemes, Lexer},
    parser::Parser,
    session::{Session, DIAG_CTXT},
    sources::{FileManager, SourceFile, SourceId, Sources},
    ty::typeck_universe,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Compilation {
    Error,
    Ok,
}

pub struct Compiler {
    sources: Sources,

    state: Cell<Compilation>,
}

impl Compiler {
    pub fn new(manager: impl FileManager + 'static) -> Self {
        Self {
            sources: Sources::new(Box::new(manager)),
            state: Cell::new(Compilation::Ok),
        }
    }

    pub fn start<A>(&mut self, main: A)
    where
        A: AsRef<Path>,
    {
        let src = self
            .sources
            .open(main.as_ref())
            .expect("failed to open main file");

        let diags = DiagEmitter::new(&self.sources);
        let session = Session::new(&diags);
        let lexemes = self.lex(src);
        let ast = self.parse_to_ast(lexemes);

        session.enter(|session| {
            let uni = hir::lower_universe(session, &ast);
            typeck_universe(session, uni);

            // emit_errors(&src).unwrap();
        });
    }

    fn lex(&self, src: SourceId) -> Lexemes {
        let lexemes = {
            let lexer = Lexer::new(self.sources.get_by_source_id(src).data(), src);
            lexer.lex()
        };

        if DIAG_CTXT.lock().unwrap().errored() {
            self.state.set(Compilation::Error);
        }

        lexemes
    }

    fn parse_to_ast(&self, lexemes: Lexemes) -> Universe {
        let decls = Parser::new(lexemes).parse();

        if DIAG_CTXT.lock().unwrap().errored() {
            self.state.set(Compilation::Error);
        }

        let mut stdout = stdout();
        let mut p = PrettyPrinter::new(&mut stdout);
        p.travel(&decls);

        decls
    }
}

pub fn emit_errors(src: &SourceFile) -> io::Result<()> {
    let mut stdout = io::stdout();

    let diag = DIAG_CTXT.lock().unwrap();
    let mut errs = Errors::new(diag.lex_errors(), &mut stdout);

    errs.print_all(src)?;
    let mut errs = Errors::new(diag.parse_errors(), &mut stdout);

    errs.print_all(src)?;

    Ok(())
}
