use crate::{
    parser::{ParseError, ParseErrorKind},
    session::{Session, SymbolId},
    sources::SourceId,
};

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum TokenKind {
    LeftParen,
    RightParen,

    LeftSqBracket,
    RightSqBracket,

    LeftArrowBracket,
    RightArrowBracket,

    LeftCurlyBracket,
    RightCurlyBracket,

    Identifier(SymbolId),

    LeftArrow,
    RightArrow,

    Plus,
    Minus,
    Modulo,
    Star,
    Slash,
    Backslash,
    Underscore,
    ShiftLeft,
    ShiftRight,

    Equals,
    NotEqual,

    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ShlAssign,
    ShrAssign,
    ModAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,

    GtEq, // >=
    LtEq, // =<

    Xor,    // ^
    BitOr,  // |
    BitAnd, // &

    LogicalAnd, // &&
    LogicalOr,  // ||

    Dot,
    ExclamationMark,
    QuestionMark,

    FloatLiteral(f64),
    IntegerLiteral(i64),
    StringLiteral(SymbolId),

    Semicolon,
    Comma,
    Colon,
    Path, // '::'

    // Keywords
    Let,
    Instance,
    Function,
    Import,
    If,
    Else,
    Then,
    Inline,
    Native,
    Const,
    Match,
    Default,
    True,
    False,
    Global,
    For,
    While,
    Until,
    Loop,
    Return,
    SelfArg,
    In,

    Eof,
}

macro_rules! operators {
    (Bitwise, $char:expr, $lexer:expr, $with_eq:ident, $not_eq:ident) => {{
        if $lexer.chars.next_char() == Some($char) {
            let span = $lexer.new_span($lexer.chars.position, $lexer.chars.position + 1);
            let token = Token::new(span, TokenKind::LogicalAnd);
            $lexer.tokens.push(token);
            continue;
        }

        operators!($lexer, $with_eq, $not_eq)
    }};

    ($lexer:expr, $with_eq:ident, $not_eq:ident) => {{
        let start = $lexer.chars.position;
        if $lexer.is_assign_op() {
            let span = $lexer.new_span(start, $lexer.chars.position + 1);
            $lexer.tokens.push(Token::new(span, TokenKind::$with_eq));
            continue;
        }

        let span = $lexer.new_span(start, $lexer.chars.position + 1);
        $lexer.tokens.push(Token::new(span, TokenKind::$not_eq))
    }};
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: u32,
    pub sourceid: SourceId,
}

impl Span {
    pub fn new(start: usize, end: usize, line: u32, sourceid: SourceId) -> Self {
        Self {
            start,
            end,
            line,
            sourceid,
        }
    }

    pub fn start(&self) -> usize {
        self.start
    }
    pub fn end(&self) -> usize {
        self.end
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(span: Span, kind: TokenKind) -> Self {
        Self { span, kind }
    }

    pub fn is_eof(&self) -> bool {
        self.kind == TokenKind::Eof
    }

    pub fn to_err_if_eof(self) -> Result<Token, ParseError> {
        if !self.is_eof() {
            return Ok(self);
        }

        let err = ParseError {
            token_span: self.span,
            kind: ParseErrorKind::EndOfFile,
        };

        Err(err)
    }
}

pub struct Reader<'a> {
    file: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    pub fn new(file: &'a [u8]) -> Self {
        Self { file, position: 0 }
    }

    pub fn peek_char(&self) -> Option<char> {
        self.peek_char_by(0)
    }
    pub fn peek_char_by(&self, by: usize) -> Option<char> {
        self.file.get(self.position + by).copied().map(Into::into)
    }

    pub fn next_char(&mut self) -> Option<char> {
        let val = self.peek_char();
        self.position += 1;
        val
    }

    pub fn advance(&mut self, by: usize) {
        self.position += by;
    }

    pub fn get_str(&self, start: usize, end: usize) -> Option<&str> {
        self.file
            .get(start..end)
            .map(core::str::from_utf8)
            .transpose()
            .ok()
            .flatten()
    }
}

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Clone, Copy)]
pub enum LexErrorKind {
    InvalidFloatLiteral,
    InvalidHexLiteral,
    InvalidOctalLiteral,
    LackingEndForStringLiteral,
    UnknownChar(char),
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct LexError {
    pub kind: LexErrorKind,
    pub span: Span,
}

pub struct Lexemes {
    pos: usize,
    tokens: Vec<Token>,
    last_token: Option<Token>,

    pub source_id: SourceId,
}

impl Lexemes {
    pub fn new(tokens: Vec<Token>, source_id: SourceId) -> Self {
        Self {
            last_token: None,
            tokens,
            pos: 0,
            source_id,
        }
    }

    pub fn peek_token(&self) -> Token {
        if self.is_empty() {
            return self.eof_token();
        }

        self.tokens
            .get(self.pos)
            .copied()
            .expect("above check guarantees this doesn't panic")
    }

    pub fn next_token(&mut self) -> Token {
        let ret = self.peek_token();
        self.pos += 1;
        self.last_token.replace(ret);
        ret
    }

    pub fn previous(&self) -> Token {
        assert!(self.pos != 0, "tried to get previous token at pos 0!");
        if self.tokens.len() <= self.pos {
            return self.eof_token();
        }

        self.tokens[self.pos - 1]
    }

    pub fn back(&mut self) {
        self.pos -= 1;
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.len() <= self.pos
    }

    pub fn advance(&mut self) {
        self.pos += 1
    }

    fn eof_token(&self) -> Token {
        let span = self.last_token.unwrap().span;
        Token::new(span, TokenKind::Eof)
    }
}

pub struct Lexer<'a> {
    chars: Reader<'a>,
    tokens: Vec<Token>,
    errors: &'a mut Vec<LexError>,

    current_line: u32,

    sourceid: SourceId,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a [u8], sourceid: SourceId, errors: &'a mut Vec<LexError>) -> Self {
        Self {
            tokens: Vec::new(),
            chars: Reader::new(input),
            errors,
            current_line: 0,
            sourceid,
        }
    }

    pub fn new_span(&self, start: usize, end: usize) -> Span {
        Span::new(start, end, self.current_line, self.sourceid)
    }

    pub fn get_str_from_span(&self, span: Span) -> Option<&str> {
        self.chars.get_str(span.start, span.end)
    }

    pub fn lex(mut self, session: &mut Session) -> Lexemes {
        while let Some(char) = self.chars.next_char() {
            match char {
                '(' => self.add_token_basic(TokenKind::LeftParen),
                ')' => self.add_token_basic(TokenKind::RightParen),

                '[' => self.add_token_basic(TokenKind::LeftSqBracket),
                ']' => self.add_token_basic(TokenKind::RightSqBracket),

                '{' => self.add_token_basic(TokenKind::LeftCurlyBracket),
                '}' => self.add_token_basic(TokenKind::RightCurlyBracket),

                ';' => self.add_token_basic(TokenKind::Semicolon),
                ':' => {
                    let start = self.chars.position;
                    if self.consume_if(':') {
                        self.add_token(self.new_span(start, self.chars.position), TokenKind::Path);
                        continue;
                    }

                    self.add_token_basic(TokenKind::Colon);
                }

                ',' => self.add_token_basic(TokenKind::Comma),
                '!' => {
                    let start = self.chars.position;
                    if self.consume_if('=') {
                        self.add_token(
                            self.new_span(start, self.chars.position),
                            TokenKind::NotEqual,
                        );
                        continue;
                    }

                    self.add_token_basic(TokenKind::ExclamationMark)
                }
                '?' => self.add_token_basic(TokenKind::QuestionMark),
                '.' => self.add_token_basic(TokenKind::Dot),

                '+' => {
                    operators!(self, AddAssign, Plus);
                }
                '-' => {
                    operators!(self, SubAssign, Minus);
                }
                '*' => {
                    operators!(self, MulAssign, Star);
                }
                '/' => {
                    operators!(self, DivAssign, Slash);
                }
                '%' => {
                    operators!(self, ModAssign, Modulo);
                }
                '&' => {
                    operators!(Bitwise, '&', self, BitAndAssign, BitAnd)
                }
                '|' => {
                    operators!(Bitwise, '&', self, BitOrAssign, BitOr)
                }

                '^' => {
                    operators!(self, BitXorAssign, Xor)
                }

                '=' => {
                    let Some(char) = self.chars.peek_char() else {
                        let span = self.new_span(self.chars.position, self.chars.position + 1);
                        let token = Token::new(span, TokenKind::Assign);
                        self.tokens.push(token);
                        continue;
                    };

                    let kind = match char {
                        '=' => TokenKind::Equals,
                        '>' => TokenKind::RightArrow,
                        '<' => TokenKind::LtEq,
                        _ => {
                            let span = self.new_span(self.chars.position, self.chars.position + 2);
                            let token = Token::new(span, TokenKind::Assign);
                            self.tokens.push(token);
                            continue;
                        }
                    };

                    let span = self.new_span(self.chars.position, self.chars.position + 2);
                    let token = Token::new(span, kind);

                    self.chars.advance(1);

                    self.tokens.push(token)
                }

                '>' => {
                    let token = if let Some(char) = self.chars.peek_char()
                        && char == '='
                    {
                        let span = self.new_span(self.chars.position, self.chars.position + 2);
                        self.chars.advance(1);
                        Token::new(span, TokenKind::GtEq)
                    } else if let Some('>') = self.chars.peek_char() {
                        let mut kind = TokenKind::ShiftRight;
                        let mut tok_span =
                            self.new_span(self.chars.position, self.chars.position + 2);

                        if let Some('=') = self.chars.peek_char_by(1) {
                            tok_span.end += 1;
                            kind = TokenKind::ShrAssign;
                            self.chars.advance(2);
                        } else {
                            self.chars.advance(1);
                        }

                        Token::new(tok_span, kind)
                    } else {
                        let span = self.new_span(self.chars.position, self.chars.position + 1);
                        Token::new(span, TokenKind::RightArrowBracket)
                    };

                    self.tokens.push(token);
                }

                '<' => {
                    let token = if let Some(char) = self.chars.peek_char()
                        && char == '='
                    {
                        let span = self.new_span(self.chars.position, self.chars.position + 2);
                        self.chars.advance(1);
                        Token::new(span, TokenKind::LeftArrow)
                    } else if let Some('<') = self.chars.peek_char() {
                        let mut kind = TokenKind::ShiftLeft;
                        let mut tok_span =
                            self.new_span(self.chars.position, self.chars.position + 2);

                        if let Some('=') = self.chars.peek_char_by(1) {
                            tok_span.end += 1;
                            kind = TokenKind::ShlAssign;
                            self.chars.advance(2);
                        } else {
                            self.chars.advance(1);
                        }

                        Token::new(tok_span, kind)
                    } else {
                        let span = self.new_span(self.chars.position, self.chars.position + 1);
                        Token::new(span, TokenKind::LeftArrowBracket)
                    };

                    self.tokens.push(token);
                }

                cap if (cap == '"') | (cap == '\'') => {
                    self.string_literal(cap, session);
                }

                '0' if self.consume_if('x') => {
                    self.hex_literal();
                }

                '0' if self.consume_if('x') => {
                    self.octal_literal();
                }

                ch if ch.is_ascii_digit() => {
                    self.integer_literal();
                }

                '\n' => self.current_line += 1,

                '#' => self.skip_all_filter(|x| x != '\n'),

                target if target == '_' || target.is_alphabetic() => {
                    let start = self.chars.position - 1;
                    self.skip_all_filter(|x| x.is_alphanumeric() || x == '_');

                    let string = self
                        .chars
                        .get_str(start, self.chars.position)
                        .expect("string should be present");

                    let span = self.new_span(start, self.chars.position);

                    let kind = if let Some(kw) = check_for_keyword(string) {
                        kw
                    } else {
                        let id = session.intern_string(string);

                        TokenKind::Identifier(id)
                    };

                    let token = Token::new(span, kind);
                    self.tokens.push(token)
                }

                '_' => self.add_token_basic(TokenKind::Underscore),

                '\\' => self.add_token_basic(TokenKind::Backslash),

                ' ' | '\t' => {}

                any => {
                    let start = self.chars.position - 1;
                    self.skip_all_filter(|x| x == any);

                    self.add_error(
                        self.new_span(start, self.chars.position),
                        LexErrorKind::UnknownChar(any),
                    );
                }
            }
        }

        Lexemes::new(self.tokens, self.sourceid)
    }

    fn string_literal(&mut self, quote: char, session: &mut Session) {
        debug_assert!((quote == '\'') | (quote == '"'));
        let mut finished_quote = false;

        let literal_start = self.chars.position;
        let mut literal_end = 0;

        while let Some(char) = self.chars.next_char() {
            if char == quote {
                finished_quote = true;
                literal_end = self.chars.position + 1;
                break;
            }
        }

        if !finished_quote {
            let span = self.new_span(literal_start, self.chars.position + 1);
            self.add_error(span, LexErrorKind::LackingEndForStringLiteral);
            return;
        }

        debug_assert!(literal_end != 0);

        let span = self.new_span(literal_start, literal_end);
        let id = session.intern_string(self.get_str_from_span(span).expect("should be valid"));

        let token = Token::new(span, TokenKind::StringLiteral(id));
        self.tokens.push(token)
    }

    fn float_literal(&mut self, start: usize) {
        while let Some(char) = self.chars.next_char() {
            if !char.is_ascii_digit() {
                let span = self.new_span(start, self.chars.position + 1);
                self.add_error(span, LexErrorKind::InvalidFloatLiteral);
                self.skip_all_filter(|x| !x.is_whitespace());
            }
        }

        let span = self.new_span(start, self.chars.position + 1);
        let string = self
            .get_literal_str(start, self.chars.position)
            .expect("couldn't retrieve the string");

        let Ok(float) = string.parse::<f64>() else {
            self.add_error(span, LexErrorKind::InvalidFloatLiteral);
            return;
        };

        self.add_token(span, TokenKind::FloatLiteral(float));
    }

    fn integer_literal(&mut self) {
        self.chars.position -= 1;
        let start = self.chars.position;

        while let Some(next) = self.chars.next_char() {
            if self.consume_if('.') {
                return self.float_literal(start);
            } else if !next.is_ascii_digit() {
                self.chars.position -= 1;
                break;
            }
        }

        let span = self.new_span(start, self.chars.position + 1);
        let num = self
            .get_literal_str(start, self.chars.position)
            .expect("couldn't get this string")
            .parse::<i64>()
            .expect("loop above ensures this never fails");

        self.add_token(span, TokenKind::IntegerLiteral(num));
    }

    fn parse_literal_radix(&mut self, radix: u32, err_kind: LexErrorKind) {
        let start = self.chars.position;
        self.skip_all_filter(|x| x.is_digit(radix));

        let literal = self.get_literal_str(start, self.chars.position).unwrap();

        let Ok(val) = i64::from_str_radix(literal, radix) else {
            let span = self.new_span(start, self.chars.position);
            self.add_error(span, err_kind);
            return;
        };

        self.add_token(
            self.new_span(start, self.chars.position + 1),
            TokenKind::IntegerLiteral(val),
        );
    }

    fn octal_literal(&mut self) {
        self.parse_literal_radix(8, LexErrorKind::InvalidOctalLiteral);
    }

    fn hex_literal(&mut self) {
        self.parse_literal_radix(16, LexErrorKind::InvalidHexLiteral);
    }

    fn is_assign_op(&mut self) -> bool {
        let boolean = self.chars.peek_char() == Some('=');
        if boolean {
            self.chars.advance(1);
        }
        boolean
    }

    fn consume_if(&mut self, target: char) -> bool {
        let is_there = self.chars.peek_char().is_some_and(|val| val == target);

        if is_there {
            self.chars.advance(1);
        }

        is_there
    }

    fn skip_all_filter<F>(&mut self, f: F)
    where
        F: Fn(char) -> bool,
    {
        while let Some(ch) = self.chars.peek_char() {
            if !f(ch) {
                break;
            }

            self.chars.position += 1;
        }
    }

    fn add_token(&mut self, span: Span, kind: TokenKind) {
        self.tokens.push(Token::new(span, kind))
    }

    fn add_token_basic(&mut self, kind: TokenKind) {
        let span = self.new_span(self.chars.position, self.chars.position + 1);
        self.add_token(span, kind);
    }

    fn add_error(&mut self, span: Span, kind: LexErrorKind) {
        self.errors.push(LexError { kind, span })
    }

    fn get_literal_str(&self, start: usize, end: usize) -> Option<&str> {
        self.chars.get_str(start, end)
    }
}

fn check_for_keyword(ident: &str) -> Option<TokenKind> {
    use TokenKind::{
        Const, Default, Else, False, For, Function, Global, If, Import, In, Inline, Instance, Let,
        Loop, Match, Native, Return, SelfArg, Then, True, Until, While,
    };
    match ident {
        "let" => Let,
        "import" => Import,
        "instance" => Instance,
        "fun" => Function,
        "if" => If,
        "then" => Then,
        "else" => Else,
        "inline" => Inline,
        "native" => Native,
        "const" => Const,
        "match" => Match,
        "default" => Default,
        "true" => True,
        "false" => False,
        "global" => Global,
        "for" => For,
        "while" => While,
        "loop" => Loop,
        "until" => Until,
        "return" => Return,
        "self" => SelfArg,
        "in" => In,

        _ => return None,
    }
    .into()
}

#[cfg(test)]
mod tests {
    use super::{Lexer, TokenKind};
    use crate::session::Session;
    use crate::sources::SourceId;

    #[test]
    fn rust_like() {
        let mut errors = Vec::new();
        let lexer = Lexer::new(b"let meow: i32 = 123", SourceId::DUMMY, &mut errors);
        let mut session = Session::new();

        let mut lexer = lexer.lex(&mut session);

        assert_eq!(lexer.next_token().kind, TokenKind::Let);
        assert!(matches!(lexer.next_token().kind, TokenKind::Identifier(..)));
        assert_eq!(lexer.next_token().kind, TokenKind::Colon);
        assert!(matches!(lexer.next_token().kind, TokenKind::Identifier(..)));
        assert_eq!(lexer.next_token().kind, TokenKind::Assign);
        assert_eq!(lexer.next_token().kind, TokenKind::IntegerLiteral(123));
    }
}
