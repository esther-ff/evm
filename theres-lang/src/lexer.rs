use crate::errors::{DiagEmitter, Phase, TheresError};
use crate::sources::SourceId;
use crate::symbols::SymbolId;
use std::borrow::Cow;
use std::fmt::Display;

impl TheresError for LexError {
    fn phase() -> Phase {
        Phase::Lexing
    }

    fn message(&self) -> Cow<'static, str> {
        match self {
            LexError::InvalidFloatLiteral => "the float literal is invalid",
            LexError::InvalidHexLiteral => "the hex literal is invalid",
            LexError::InvalidOctalLiteral => "the octal literal is invalid",
            LexError::LackingEndForStringLiteral => "unterminated string literal",
            LexError::UnknownChar(ch) => return format!("unknown character: {ch}").into(),
        }
        .into()
    }
}

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
    If,
    Else,
    Then,
    Const,
    True,
    False,
    For,
    While,
    Until,
    Loop,
    Return,
    SelfArg,
    Realm,
    Bind,
    Break,
    With,
    In,

    Eof,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[allow(clippy::enum_glob_use)]
        use TokenKind::*;

        let w = match self {
            In => "in",
            LeftParen => "(",
            With => "with",
            RightParen => ")",
            LeftSqBracket => "[",
            RightSqBracket => "]",
            LeftArrowBracket => "<",
            RightArrowBracket => ">",
            LeftArrow => "<=",
            RightArrow => "=>",
            LeftCurlyBracket => "{",
            Plus => "+",
            Minus => "-",
            Modulo => "%",
            Star => "*",
            Slash => "/",
            Backslash => "\\",
            Underscore => "_",
            ShiftLeft => "<<",
            ShiftRight => ">>",

            Equals => "==",
            NotEqual => "!=",

            Assign => "=",
            AddAssign => "+=",
            SubAssign => "-=",
            MulAssign => "*=",
            DivAssign => "/=",
            ShlAssign => "<<=",
            ShrAssign => "=>>",
            ModAssign => "%=",
            BitAndAssign => "&=",
            BitOrAssign => "|=",
            BitXorAssign => "^=",

            GtEq => ">=", // >=
            LtEq => "=<", // =<

            Xor => "^",    // ^
            BitOr => "|",  // |
            BitAnd => "&", // &

            LogicalAnd => "&&", // &&
            LogicalOr => "||",  // ||

            Dot => ".",
            ExclamationMark => "!",
            QuestionMark => "?",

            FloatLiteral(..) => "a float literal",
            IntegerLiteral(..) => "an integer literal",
            StringLiteral(sym) => return write!(f, "\"{}\"", sym.get_interned()),
            Identifier(sym) => sym.get_interned(),

            Semicolon => ";",
            Comma => ",",
            Colon => ":",
            Path => "::", // '::'

            // Keywords
            Let => "let",
            Instance => "instance",
            Function => "fun",
            If => "if",
            Else => "else",
            Then => "then",
            Const => "const",
            True => "true",
            False => "false",
            For => "for",
            While => "while",
            Until => "until",
            Loop => "loop",
            Return => "return",
            SelfArg => "self",
            Realm => "realm",
            Bind => "bind",

            Eof => "<eof>",
            RightCurlyBracket => "}",
            Break => "break",
        };

        write!(f, "{w}")
    }
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

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub sourceid: SourceId,
}

impl Span {
    pub const DUMMY: Self = Self {
        start: u32::MAX,
        end: u32::MAX,
        line: u32::MAX,
        sourceid: SourceId::DUMMY,
    };

    pub fn new(start: u32, end: u32, line: u32, sourceid: SourceId) -> Self {
        Self {
            start,
            end,
            line,
            sourceid,
        }
    }

    pub fn start(&self) -> u32 {
        self.start
    }

    pub fn end(&self) -> u32 {
        self.end
    }

    #[track_caller]
    pub fn between(left: Self, right: Self) -> Span {
        debug_assert!(left.sourceid == right.sourceid);
        Span::new(left.start, right.end, right.line, right.sourceid)
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(span: Span, kind: TokenKind) -> Self {
        Self { kind, span }
    }

    pub fn is_eof(&self) -> bool {
        self.kind == TokenKind::Eof
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
pub enum LexError {
    InvalidFloatLiteral,
    InvalidHexLiteral,
    InvalidOctalLiteral,
    LackingEndForStringLiteral,
    UnknownChar(char),
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

    pub fn is_empty(&self) -> bool {
        self.tokens.len() <= self.pos
    }

    pub fn advance(&mut self) {
        self.pos += 1;
    }

    fn eof_token(&self) -> Token {
        let span = self.last_token.unwrap().span;
        Token::new(span, TokenKind::Eof)
    }
}

pub struct Lexer<'a> {
    chars: Reader<'a>,
    tokens: Vec<Token>,

    current_line: u32,

    sourceid: SourceId,

    diag: &'a DiagEmitter<'a>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a [u8], sourceid: SourceId, diag: &'a DiagEmitter<'a>) -> Self {
        Self {
            tokens: Vec::new(),
            chars: Reader::new(input),
            current_line: 1,
            sourceid,
            diag,
        }
    }

    pub fn new_span(&self, start: usize, end: usize) -> Span {
        Span::new(start as u32, end as u32, self.current_line, self.sourceid)
    }

    pub fn get_str_from_span(&self, span: Span) -> Option<&str> {
        self.chars.get_str(span.start as usize, span.end as usize)
    }

    pub fn lex(mut self) -> Lexemes {
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
                    self.handle_exclamation();
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
                    operators!(Bitwise, '&', self, BitAndAssign, BitAnd);
                }
                '|' => {
                    operators!(Bitwise, '&', self, BitOrAssign, BitOr);
                }

                '^' => {
                    operators!(self, BitXorAssign, Xor);
                }

                '=' => {
                    self.handle_equals();
                }

                '<' => {
                    self.handle_left_arrow_bracket();
                }

                '>' => {
                    self.handle_right_arrow_bracket();
                }

                cap if (cap == '"') | (cap == '\'') => {
                    self.string_literal(cap);
                }

                '0' if self.consume_if('x') => {
                    self.hex_literal();
                }

                '0' if self.consume_if('o') => {
                    self.octal_literal();
                }

                ch if ch.is_ascii_digit() => {
                    self.number_literal();
                }

                '\n' => self.current_line += 1,

                '#' => self.skip_all_filter(|x| x != '\n'),

                target if target == '_' || target.is_alphabetic() => {
                    self.handle_identifier();
                }

                '_' => self.add_token_basic(TokenKind::Underscore),

                '\\' => self.add_token_basic(TokenKind::Backslash),

                ' ' | '\t' => {}

                any => {
                    self.lex_error(any);
                }
            }
        }

        Lexemes::new(self.tokens, self.sourceid)
    }

    #[inline]
    fn lex_error(&mut self, any: char) {
        let start = self.chars.position - 1;
        self.skip_all_filter(|x| x == any);

        self.error(
            self.new_span(start, self.chars.position),
            LexError::UnknownChar(any),
        );
    }

    #[inline]
    fn number_literal(&mut self) {
        let start = self.chars.position - 1;

        while let Some(ch) = self.chars.next_char() {
            if ch == '.' {
                return self.inner_float_literal(start);
            } else if !ch.is_ascii_digit() {
                self.chars.position -= 1;
                break;
            }
        }

        let Some(literal_str) = self.chars.get_str(start, self.chars.position) else {
            unreachable!()
        };

        let literal = literal_str
            .parse::<i64>()
            .expect("this isn't supposed to fail");

        self.add_token(
            self.new_span(start, self.chars.position),
            TokenKind::IntegerLiteral(literal),
        );
    }

    #[inline]
    fn inner_float_literal(&mut self, start: usize) {
        while let Some(ch) = self.chars.peek_char() {
            if !ch.is_ascii_digit() {
                break;
            }

            self.chars.position += 1;
        }

        let Some(literal_str) = self.chars.get_str(start, self.chars.position) else {
            unreachable!()
        };

        let float: f64 = literal_str.parse().expect("shouldn't fail");

        self.add_token(
            self.new_span(start, self.chars.position),
            TokenKind::FloatLiteral(float),
        );
    }

    fn handle_identifier(&mut self) {
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
            let id = SymbolId::intern(string);

            TokenKind::Identifier(id)
        };

        let token = Token::new(span, kind);
        self.tokens.push(token);
    }

    fn handle_exclamation(&mut self) {
        let start = self.chars.position;
        if self.consume_if('=') {
            self.add_token(
                self.new_span(start, self.chars.position),
                TokenKind::NotEqual,
            );
            return;
        }

        self.add_token_basic(TokenKind::ExclamationMark);
    }

    fn handle_equals(&mut self) {
        let Some(char) = self.chars.peek_char() else {
            let span = self.new_span(self.chars.position, self.chars.position + 1);
            let token = Token::new(span, TokenKind::Assign);
            self.tokens.push(token);
            return;
        };

        let kind = match char {
            '=' => TokenKind::Equals,
            '>' => TokenKind::RightArrow,
            '<' => TokenKind::LtEq,
            _ => {
                let span = self.new_span(self.chars.position, self.chars.position + 2);
                let token = Token::new(span, TokenKind::Assign);
                self.tokens.push(token);
                return;
            }
        };

        let span = self.new_span(self.chars.position, self.chars.position + 2);
        let token = Token::new(span, kind);

        self.chars.advance(1);

        self.tokens.push(token);
    }

    fn handle_left_arrow_bracket(&mut self) {
        let token = if let Some(char) = self.chars.peek_char()
            && char == '='
        {
            let span = self.new_span(self.chars.position, self.chars.position + 2);
            self.chars.advance(1);
            Token::new(span, TokenKind::LeftArrow)
        } else if let Some('<') = self.chars.peek_char() {
            let mut kind = TokenKind::ShiftLeft;
            let mut tok_span = self.new_span(self.chars.position, self.chars.position + 2);

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

    fn handle_right_arrow_bracket(&mut self) {
        let token = if let Some(char) = self.chars.peek_char()
            && char == '='
        {
            let span = self.new_span(self.chars.position, self.chars.position + 2);
            self.chars.advance(1);
            Token::new(span, TokenKind::GtEq)
        } else if let Some('>') = self.chars.peek_char() {
            let mut kind = TokenKind::ShiftRight;
            let mut tok_span = self.new_span(self.chars.position, self.chars.position + 2);

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

    fn string_literal(&mut self, quote: char) {
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
            self.error(span, LexError::LackingEndForStringLiteral);
            return;
        }

        debug_assert!(literal_end != 0);

        let span = self.new_span(literal_start, literal_end);
        let id = SymbolId::intern(self.get_str_from_span(span).expect("should be valid"));

        let token = Token::new(span, TokenKind::StringLiteral(id));
        self.tokens.push(token);
    }

    fn parse_literal_radix(&mut self, radix: u32, err_kind: LexError) {
        let start = self.chars.position;
        self.skip_all_filter(|x| x.is_digit(radix));

        let literal = self.get_literal_str(start, self.chars.position).unwrap();
        let Ok(val) = i64::from_str_radix(literal, radix) else {
            let span = self.new_span(start, self.chars.position);
            self.error(span, err_kind);
            return;
        };

        self.add_token(
            self.new_span(start, self.chars.position + 1),
            TokenKind::IntegerLiteral(val),
        );
    }

    fn octal_literal(&mut self) {
        self.parse_literal_radix(8, LexError::InvalidOctalLiteral);
    }

    fn hex_literal(&mut self) {
        self.parse_literal_radix(16, LexError::InvalidHexLiteral);
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
        self.tokens.push(Token::new(span, kind));
    }

    fn add_token_basic(&mut self, kind: TokenKind) {
        let span = self.new_span(self.chars.position, self.chars.position + 1);
        self.add_token(span, kind);
    }

    fn get_literal_str(&self, start: usize, end: usize) -> Option<&str> {
        dbg!(end - start);
        self.chars.get_str(start, end)
    }

    fn error(&self, span: Span, err: LexError) {
        self.diag.emit_err(err, span);
    }
}

fn check_for_keyword(ident: &str) -> Option<TokenKind> {
    use TokenKind::{
        Bind, Const, Else, False, For, Function, If, Instance, Let, Loop, Realm, Return, SelfArg,
        Then, True, Until, While, With,
    };

    match ident {
        "with" => With,
        "let" => Let,
        "instance" => Instance,
        "fun" => Function,
        "if" => If,
        "then" => Then,
        "else" => Else,
        "const" => Const,
        "true" => True,
        "false" => False,
        "for" => For,
        "while" => While,
        "loop" => Loop,
        "until" => Until,
        "return" => Return,
        "self" => SelfArg,
        "realm" => Realm,
        "bind" => Bind,

        _ => return None,
    }
    .into()
}
