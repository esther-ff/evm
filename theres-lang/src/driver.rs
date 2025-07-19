use std::path::Path;

use crate::{
    lexer::{LexError, Lexer},
    parser::{ParseError, Parser},
    session::Session,
    sources::{FileManager, Sources},
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
            todo!("emit errors");
        }

        let decls = Parser::new(lexemes, &mut self.parse_errors).parse();

        if !self.parse_errors.is_empty() {
            self.failed = true;
            todo!("emit errors");
        }

        dbg!(decls);
    }
}
