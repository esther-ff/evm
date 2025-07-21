use std::{io, path::Path};

use crate::{
    errors::Errors,
    lexer::{LexError, Lexer},
    parser::{ParseError, Parser},
    session::Session,
    sources::{FileManager, SourceFile, Sources},
};

pub struct Compiler<T: FileManager> {
    session: Session,
    sources: Sources<T>,
    context: (),

    lex_errors: Vec<LexError>,
    parse_errors: Vec<ParseError>,

    failed: bool,
}

impl<T: FileManager> Compiler<T> {
    pub fn new(manager: T) -> Self {
        Self {
            sources: Sources::new(manager),
            context: (),
            parse_errors: Vec::new(),
            lex_errors: Vec::new(),
            session: Session::new(),
            failed: false,
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

        let lexemes =
            Lexer::new(src.data(), src.source_id(), &mut self.lex_errors).lex(&mut self.session);

        if !self.lex_errors.is_empty() {
            self.failed = true;
        }

        let decls = Parser::new(lexemes, &mut self.parse_errors).parse();

        if !self.parse_errors.is_empty() {
            self.failed = true;
        }

        dbg!(&self.parse_errors);

        self.emit_errors(&src).unwrap();

        if !self.failed {
            dbg!(decls);
        }
    }

    pub fn emit_errors(&mut self, src: &SourceFile) -> io::Result<()> {
        let mut stdout = io::stdout();
        let mut errs = Errors::new(&self.lex_errors, &mut stdout);

        errs.print_all(src)?;
        let mut errs = Errors::new(&self.parse_errors, &mut stdout);

        errs.print_all(src)?;

        Ok(())
    }
}
