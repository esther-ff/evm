use std::panic::Location;

use crate::ast::*;
use crate::lexer::{Lexemes, Span, Token, TokenKind};
use crate::session::SymbolId;

type Result<T, E = ParseError> = core::result::Result<T, E>;

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub enum ParseErrorKind {
    EndOfFile,
    Expected { what: &'static str, got: TokenKind },
    ExpectedUnknown { what: &'static str },
    WrongUnaryOp { offender: Token },
    FunctionWithoutBody,
}

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub struct ParseError {
    pub token_span: Span,
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub fn new(token_span: Span, kind: ParseErrorKind) -> Self {
        Self { token_span, kind }
    }
}

pub enum FunctionPart {
    Signature(FnSig),
    Full(FnDecl),
}

pub struct Parser<'a> {
    lexemes: Lexemes,

    errors: &'a mut Vec<ParseError>,
    decls: Vec<AstDef>,
}

impl<'a> Parser<'a> {
    pub fn new(lexemes: Lexemes, errors: &'a mut Vec<ParseError>) -> Self {
        Self {
            lexemes,
            errors,

            decls: Vec::new(),
        }
    }

    pub fn has_errored(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn errors(&self) -> &[ParseError] {
        self.errors
    }

    pub fn decls(&self) -> &[AstDef] {
        &self.decls
    }

    pub fn parse(mut self) -> Vec<AstDef> {
        while !self.lexemes.is_empty() {
            match self.declaration() {
                Err(err) => self.errors.push(err),
                Ok(decl) => self.decls.push(AstDef::new(decl)),
            }
        }

        self.decls
    }

    fn declaration(&mut self) -> Result<DefKind> {
        let tok = self.lexemes.peek_token();

        let decl = match tok.kind {
            TokenKind::Function => self.function_declaration()?,
            TokenKind::Global => self.global_variable_decl()?,
            TokenKind::Instance => self.instance_decl()?,
            TokenKind::Interface => self.interface_decl()?,
            TokenKind::Apply => self.apply_interface()?,
            TokenKind::Eof => return tok.to_err_if_eof().map(|_| unreachable!()),

            any => {
                let err = ParseErrorKind::Expected {
                    what: "`fun`, `global`, `instance`, `inteface` or `apply`",
                    got: any,
                };

                return self.error_out(err, tok.span);
            }
        };

        Ok(decl)
    }

    pub fn ty(&mut self) -> Result<Ty> {
        let tok = self.lexemes.peek_token();
        match tok.kind {
            TokenKind::Function => self.parse_function_type(),
            TokenKind::LeftSqBracket => self.parse_array_type(),

            TokenKind::Identifier(ident) => {
                self.lexemes.advance();

                let tok2 = self.lexemes.peek_token();
                if tok2.kind != TokenKind::LeftArrowBracket {
                    let ty = Ty {
                        kind: TyKind::Regular(ident),
                        span: tok.span,
                    };

                    return Ok(ty);
                };

                self.lexemes.advance();
                todo!("parsing generics in types")
            }

            any => {
                let err = ParseErrorKind::Expected {
                    what: "a function type, array or regular type",
                    got: any,
                };

                let span = self.lexemes.peek_token().span;
                self.lexemes.advance();

                self.error_out(err, span)
            }
        }
    }

    pub fn parse_function_type(&mut self) -> Result<Ty> {
        let fun_ident = self.expect_token(TokenKind::Function)?;
        self.expect_token(TokenKind::LeftParen)?;

        let mut types = vec![self.ty()?];

        while self.consume_if(TokenKind::Comma) {
            types.push(self.ty()?);
        }
        self.expect_token(TokenKind::RightParen)?;
        self.expect_token(TokenKind::RightArrow)?;

        let ret = self.ty().map(Box::new)?;
        let end = ret.span.end();

        Ok(Ty {
            kind: TyKind::Fn {
                args: types,
                ret: Some(ret),
            },
            span: self.new_span(fun_ident.span.start, end, 0),
        })
    }

    pub fn parse_array_type(&mut self) -> Result<Ty> {
        let left_sq = self.expect_token(TokenKind::LeftSqBracket)?;
        let ty = self.ty().map(Box::new)?;

        let right_sq = self.expect_token(TokenKind::RightSqBracket)?;

        Ok(Ty {
            kind: TyKind::Array(ty),
            span: self.new_span(left_sq.span.start(), right_sq.span.end(), 0),
        })
    }

    fn function_signature(&mut self) -> Result<FnSig> {
        let start_span = self.expect_token(TokenKind::Function)?.span.start();
        let name = self.expect_ident_as_name()?;
        self.expect_token(TokenKind::LeftParen)?;

        let fun_args = self.fun_args()?;

        self.expect_token(TokenKind::RightParen)?;
        self.expect_token(TokenKind::RightArrow)?;

        let ret_type = self.ty()?;

        let span = self.new_span(start_span, ret_type.span.end(), 0);
        Ok(FnSig::new(name, span, ret_type, fun_args))
    }

    fn function_declaration(&mut self) -> Result<DefKind> {
        match self.function()? {
            FunctionPart::Full(decl) => Ok(DefKind::Function(decl)),

            FunctionPart::Signature(sig) => {
                self.error_out(ParseErrorKind::FunctionWithoutBody, sig.span)
            }
        }
    }

    fn function(&mut self) -> Result<FunctionPart> {
        let sig = self.function_signature()?;

        let maybe_block = if self.lexemes.peek_token().kind == TokenKind::LeftCurlyBracket {
            Some(self.block()?)
        } else {
            None
        };

        match maybe_block {
            Some(block) => {
                let span = self.new_span(sig.span.end(), block.span.end(), 0);
                let fndecl = FnDecl { block, sig, span };
                Ok(FunctionPart::Full(fndecl))
            }

            None => Ok(FunctionPart::Signature(sig)),
        }
    }

    fn fun_args(&mut self) -> Result<Vec<Arg>> {
        let mut args = Vec::new();

        if let Some(self_arg) = self.fn_self_arg() {
            args.push(self_arg)
        }

        if self.lexemes.peek_token().kind != TokenKind::RightParen {
            args.push(self.arg()?);

            while self.consume_if(TokenKind::Comma) {
                args.push(self.arg()?)
            }
        }

        Ok(args)
    }

    fn arg(&mut self) -> Result<Arg> {
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::Colon)?;
        let ty = self.ty()?;

        Ok(Arg::new(name, ty))
    }

    fn fn_self_arg(&mut self) -> Option<Arg> {
        let tok = self.lexemes.peek_token();

        if tok.is_eof() {
            return None;
        }

        if tok.kind == TokenKind::SelfArg {
            self.lexemes.advance();

            let second_tok = self.lexemes.peek_token();

            if second_tok.kind == TokenKind::Comma {
                self.lexemes.advance();
            }

            let arg = Arg::new(
                Name::new(SymbolId::DUMMY, tok.span),
                Ty {
                    kind: TyKind::MethodSelf,
                    span: tok.span,
                },
            );

            return Some(arg);
        }

        None
    }

    fn fn_call_args(&mut self) -> Result<Vec<Expr>> {
        if self.lexemes.peek_token().kind == TokenKind::RightParen {
            return Ok(Vec::new());
        }

        let mut args = vec![self.expression()?];

        while self.consume_if(TokenKind::Comma) {
            args.push(self.expression()?);
        }

        Ok(args)
    }

    fn instance_decl(&mut self) -> Result<DefKind> {
        let keyword = self.expect_token(TokenKind::Instance)?;
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::LeftCurlyBracket)?;

        let fields = self.instance_fields()?;

        let rcurly = self.expect_token(TokenKind::RightCurlyBracket)?;
        let assoc = if self.consume_if(TokenKind::With) {
            Some(self.block()?)
        } else {
            None
        };

        let span_end = assoc.as_ref().map_or(rcurly.span.end(), |x| x.span.end());
        let span = self.new_span(keyword.span.start(), span_end, 0);
        Ok(DefKind::instance(name, span, fields, assoc))
    }

    fn instance_fields(&mut self) -> Result<Vec<Field>> {
        fn one_field(me: &mut Parser<'_>) -> Result<Field> {
            let span_start = me.lexemes.peek_token().span.start();
            let is_const = me.consume_if(TokenKind::Const);
            let field_name = me.expect_ident_as_name()?;

            me.expect_token(TokenKind::Colon)?;

            let ty = me.ty()?;
            let field_span = me.new_span(span_start, ty.span.end(), 0);

            Ok(Field::new(is_const, field_name, ty, field_span))
        }

        let peeked = self.lexemes.peek_token();
        if peeked.kind == TokenKind::RightCurlyBracket {
            return Ok(Vec::new());
        }

        let mut fields = vec![one_field(self)?];
        while self.consume_if(TokenKind::Comma) {
            if self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
                fields.push(one_field(self)?)
            }
        }

        Ok(fields)
    }

    pub fn interface_decl(&mut self) -> Result<DefKind> {
        let kw = self.expect_token(TokenKind::Interface)?;
        let name = self.expect_ident_as_name()?;
        self.expect_token(TokenKind::LeftCurlyBracket)?;
        let mut entries = Vec::new();
        while self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
            entries.push(self.interface_entry()?);
        }

        let rcurly = self.expect_token(TokenKind::RightCurlyBracket)?;

        Ok(DefKind::interface(
            name,
            self.new_span(kw.span.start(), rcurly.span.end(), 0),
            entries,
        ))
    }

    fn interface_entry(&mut self) -> Result<InterfaceEntry> {
        let ret = match self.lexemes.peek_token().kind {
            TokenKind::Let | TokenKind::Const => {
                self.local_variable_stmt().map(InterfaceEntry::Const)?
            }

            TokenKind::Function => match self.function()? {
                FunctionPart::Signature(sig) => InterfaceEntry::TemplateFn(sig),
                FunctionPart::Full(fndecl) => InterfaceEntry::ProvidedFn(fndecl),
            },

            TokenKind::Eof => {
                return self.error_out(ParseErrorKind::EndOfFile, self.lexemes.peek_token().span);
            }

            any => {
                let err = ParseErrorKind::Expected {
                    what: "a function signature, body or associated constant",
                    got: any,
                };

                return self.error_out(err, self.lexemes.peek_token().span);
            }
        };

        Ok(ret)
    }

    fn apply_interface(&mut self) -> Result<DefKind> {
        let apply = self.expect_token(TokenKind::Apply)?;
        let interface_name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::For)?;

        let receiver = self.ty()?;
        let mut entries = Vec::new();

        self.expect_token(TokenKind::LeftCurlyBracket)?;
        while self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
            entries.push(self.interface_entry()?);
        }

        let rcurly = self.expect_token(TokenKind::RightCurlyBracket)?;

        dbg!(self.lexemes.peek_token());
        Ok(DefKind::Apply(Apply::new(
            interface_name,
            receiver,
            self.new_span(apply.span.start(), rcurly.span.end(), 0),
            entries,
        )))
    }

    fn local_variable_stmt(&mut self) -> Result<VariableStmt> {
        let tok = self.lexemes.next_token().to_err_if_eof()?;

        let mode = match tok.kind {
            TokenKind::Const => VarMode::Const,
            TokenKind::Let => VarMode::Let,

            _ => {
                let err = self.error_out(
                    ParseErrorKind::Expected {
                        what: "a variable declaration",
                        got: tok.kind,
                    },
                    tok.span,
                );
                return err;
            }
        };

        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::Colon)?;

        let ty = self.ty()?;
        let tok = self.lexemes.peek_token().to_err_if_eof()?;

        let initializer: Option<Expr> = if tok.kind == TokenKind::Semicolon {
            None
        } else {
            self.expect_token(TokenKind::Assign)?;
            self.expression()?.into()
        };

        Ok(VariableStmt::new(mode, name, initializer, ty))
    }

    fn global_variable_decl(&mut self) -> Result<DefKind> {
        self.expect_token(TokenKind::Global)?;

        let constant = self.lexemes.peek_token().to_err_if_eof()?.kind == TokenKind::Const;
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::Colon)?;

        let ty = self.ty()?;
        let tok = self.lexemes.peek_token().to_err_if_eof()?;

        self.expect_token(TokenKind::Assign)?;

        let initializer: Option<Expr> = if tok.kind == TokenKind::Semicolon {
            None
        } else {
            self.expression()?.into()
        };

        Ok(DefKind::global(name, initializer, ty, constant))
    }

    fn statement(&mut self) -> Result<Stmt> {
        let tok = self.lexemes.peek_token().to_err_if_eof()?;

        let stmt = match tok.kind {
            TokenKind::LeftCurlyBracket => Stmt::Block(self.block()?),
            TokenKind::Let | TokenKind::Const => Stmt::LocalVar(self.local_variable_stmt()?),
            TokenKind::Function | TokenKind::Global => {
                Stmt::Definition(AstDef::new(self.declaration()?))
            }
            _ => Stmt::Expr(self.expression()?),
        };

        let _ = self.expect_token(TokenKind::Semicolon)?;

        Ok(stmt)
    }

    fn block(&mut self) -> Result<Block> {
        let span_start = self.expect_token(TokenKind::LeftCurlyBracket)?.span.start();

        let mut stmts = Vec::new();
        while self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
            stmts.push(self.statement()?);
        }

        let span_end = self.expect_token(TokenKind::RightCurlyBracket)?.span.end();
        Ok(Block::new(stmts, self.new_span(span_start, span_end, 0)))
    }

    fn expression(&mut self) -> Result<Expr> {
        self.assignment()
    }

    pub fn if_expr(&mut self) -> Result<Expr> {
        let begin = self.expect_token(TokenKind::If)?;
        let expr = self.expression()?;

        let first_block = self.block()?;

        let mut end = first_block.span.end();
        let mut else_ifs = Vec::new();
        let mut otherwise = None;

        // just an `if <expr> <block>`
        if !self.consume_if(TokenKind::Else) {
            return Ok(Expr::new(
                ExprType::If {
                    cond: Box::new(expr),
                    if_block: first_block,
                    else_ifs,
                    otherwise,
                },
                self.new_span(begin.span.start(), end, 0),
            ));
        };

        // just an `if <expr> <block> else <block>`
        if !self.consume_if(TokenKind::If) {
            otherwise = Some(self.block()?);
            return Ok(Expr::new(
                ExprType::If {
                    cond: Box::new(expr),
                    if_block: first_block,
                    else_ifs,
                    otherwise,
                },
                self.new_span(begin.span.start(), end, 0),
            ));
        }

        // `if <expr> <block> else if <expr> <block> ... (else <block>)?`
        let cond = self.expression()?;
        let block = self.block()?;
        else_ifs.push(ElseIf::new(cond, block));

        while self.consume_if(TokenKind::Else) && self.consume_if(TokenKind::If) {
            let cond = self.expression()?;
            let block = self.block()?;
            end = block.span.end();
            else_ifs.push(ElseIf::new(cond, block));
        }

        if self.lexemes.previous().kind == TokenKind::Else {
            let block = self.block()?;
            end = block.span.end();
            otherwise.replace(block);
        }

        Ok(Expr::new(
            ExprType::If {
                cond: Box::new(expr),
                if_block: first_block,
                else_ifs,
                otherwise,
            },
            self.new_span(begin.span.start(), end, 0),
        ))
    }

    pub fn loop_expr(&mut self) -> Result<Expr> {
        let loop_ident = self.expect_token(TokenKind::Loop)?;
        let body = self.block()?;
        let span = self.new_span(loop_ident.span.start(), body.span.end(), 0);

        Ok(Expr::new(ExprType::Loop { body }, span))
    }

    pub fn for_loop(&mut self) -> Result<Expr> {
        let for_ident = self.expect_token(TokenKind::For)?;
        let pat = self.pat()?;

        self.expect_token(TokenKind::In)?;

        let iterable = self.expression().map(Box::new)?;

        let body = self.block()?;
        let span = self.new_span(for_ident.span.start(), body.span.end(), 0);

        Ok(Expr::new(
            ExprType::For {
                iterable,
                pat,
                body,
            },
            span,
        ))
    }

    pub fn pat(&mut self) -> Result<Pat> {
        let token = self.expect_any_token()?;

        if token.kind == TokenKind::Underscore {
            return Ok(Pat::new(PatType::Wild, token.span));
        }

        if let TokenKind::Identifier(id) = token.kind {
            let name = Name::new(id, token.span);
            return Ok(Pat::new(PatType::Ident { name }, token.span));
        }

        if token.kind != TokenKind::LeftParen {
            return self.error_out(
                ParseErrorKind::Expected {
                    what: "a left parenthesis",
                    got: token.kind,
                },
                token.span,
            );
        }

        let pat = self.pat()?;
        let mut pats = vec![pat];
        while self.lexemes.peek_token().kind != TokenKind::RightParen {
            self.expect_token(TokenKind::Comma)?;
            pats.push(self.pat()?);
        }

        let right_paren = self.expect_token(TokenKind::RightParen)?;
        let span = self.new_span(token.span.start(), right_paren.span.end(), 0);

        Ok(Pat::new(PatType::Tuple { pats }, span))
    }

    pub fn while_expr(&mut self) -> Result<Expr> {
        let while_ident = self.expect_token(TokenKind::While)?;
        let cond = self.expression().map(Box::new)?;

        let body = self.block()?;
        let span = self.new_span(while_ident.span.start(), body.span.end(), 0);

        Ok(Expr::new(ExprType::While { cond, body }, span))
    }

    pub fn until_expr(&mut self) -> Result<Expr> {
        let until_ident = self.expect_token(TokenKind::Until)?;
        let cond = self.expression().map(Box::new)?;
        let body = self.block()?;
        let span = self.new_span(until_ident.span.start(), body.span.end(), 0);

        Ok(Expr::new(ExprType::Until { cond, body }, span))
    }

    pub fn lambda_expr(&mut self) -> Result<Expr> {
        let slash = self.expect_token(TokenKind::Backslash)?;

        let pat = self.pat()?;
        let mut args = vec![pat];
        while self.consume_if(TokenKind::Comma) {
            args.push(self.pat()?)
        }

        self.expect_token(TokenKind::RightArrow)?;

        let body = if self.lexemes.peek_token().kind == TokenKind::LeftCurlyBracket {
            LambdaBody::Block(self.block()?)
        } else {
            LambdaBody::Expr(self.expression().map(Box::new)?)
        };

        let span = self.new_span(slash.span.start(), body.span().end(), 0);

        Ok(Expr {
            ty: ExprType::Lambda { args, body },
            span,
        })
    }

    pub fn array_expr(&mut self) -> Result<Expr> {
        let left_sq = self.expect_token(TokenKind::LeftSqBracket)?;
        let size = self.primary().map(Box::new)?;
        self.expect_token(TokenKind::RightSqBracket)?;
        let ty = self.ty()?;

        let span_start = left_sq.span.start();
        let mut span_end = ty.span.end();

        let mut inits: Vec<Expr> = Vec::new();

        if self.consume_if(TokenKind::LeftCurlyBracket) {
            // parse the initializers
            inits.push(self.expression()?);

            while self.consume_if(TokenKind::Comma) {
                inits.push(self.expression()?)
            }

            let end = self.expect_token(TokenKind::RightCurlyBracket)?;
            span_end = end.span.end();
        };

        Ok(Expr::new(
            ExprType::ArrayDecl {
                size,
                ty,
                initialize: inits,
            },
            self.new_span(span_start, span_end, 0),
        ))
    }

    fn assignment(&mut self) -> Result<Expr> {
        let lvalue = self.bitwise_or()?;

        let tok = self.lexemes.peek_token();
        let mode = match tok.kind {
            TokenKind::Assign => AssignMode::Regular,
            TokenKind::AddAssign => AssignMode::Add,
            TokenKind::SubAssign => AssignMode::Sub,
            TokenKind::MulAssign => AssignMode::Mul,
            TokenKind::DivAssign => AssignMode::Div,
            TokenKind::ShlAssign => AssignMode::Shl,
            TokenKind::ShrAssign => AssignMode::Shr,
            TokenKind::ModAssign => AssignMode::Mod,
            TokenKind::BitXorAssign => AssignMode::Xor,
            TokenKind::BitOrAssign => AssignMode::Or,
            TokenKind::BitAndAssign => AssignMode::And,

            TokenKind::Eof => return tok.to_err_if_eof().map(|_| unreachable!()),
            _ => return Ok(lvalue),
        };

        self.lexemes.advance();

        let rvalue = self.assignment()?;
        let span = self.new_span(lvalue.span.start(), rvalue.span.end(), 0);

        let expr_ty = ExprType::Assign {
            lvalue: Box::new(lvalue),
            rvalue: Box::new(rvalue),
            mode,
        };

        Ok(Expr::new(expr_ty, span))
    }

    fn bitwise_or(&mut self) -> Result<Expr> {
        let mut lhs = self.bitwise_xor()?;

        let start = lhs.span.start();

        while self.consume_if(TokenKind::BitOr) {
            let rhs = self.bitwise_xor()?;
            let span = self.new_span(start, rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitOr,
            };

            lhs = Expr::new(expr_ty, span);
        }

        Ok(lhs)
    }

    fn bitwise_xor(&mut self) -> Result<Expr> {
        let mut lhs = self.bitwise_and()?;
        let start = lhs.span.start();

        while self.consume_if(TokenKind::Xor) {
            let rhs = self.bitwise_and()?;
            let span = self.new_span(start, rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitXor,
            };

            lhs = Expr::new(expr_ty, span);
        }

        Ok(lhs)
    }

    fn bitwise_and(&mut self) -> Result<Expr> {
        let mut lhs = self.logic_or()?;
        let start = lhs.span.start();

        while self.consume_if(TokenKind::BitAnd) {
            let rhs = self.logic_or()?;
            let span = self.new_span(start, rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitAnd,
            };

            lhs = Expr::new(expr_ty, span);
        }

        Ok(lhs)
    }

    fn logic_or(&mut self) -> Result<Expr> {
        let mut lhs = self.logic_and()?;
        let start = lhs.span.start();

        while self.consume_if(TokenKind::LogicalOr) {
            let rhs = self.logic_and()?;
            let span = self.new_span(start, rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::LogicalOr,
            };

            lhs = Expr::new(expr_ty, span);
        }

        Ok(lhs)
    }

    fn logic_and(&mut self) -> Result<Expr> {
        let mut lhs = self.equality()?;
        let start = lhs.span.start();

        while self.consume_if(TokenKind::LogicalAnd) {
            let rhs = self.equality()?;
            let span = self.new_span(start, rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::LogicalAnd,
            };

            lhs = Expr::new(expr_ty, span);
        }

        Ok(lhs)
    }

    fn equality(&mut self) -> Result<Expr> {
        let mut lhs = self.comparison()?;

        while self.consume_if(TokenKind::NotEqual) || self.consume_if(TokenKind::Equals) {
            let tkn = self.lexemes.previous();
            let op = match tkn.kind {
                TokenKind::NotEqual => BinOp::NotEquality,
                TokenKind::Equals => BinOp::Equality,
                _ => unreachable!(),
            };

            let rhs = self.comparison()?;
            let span = self.new_span(lhs.span.start(), rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span)
        }

        Ok(lhs)
    }

    fn comparison(&mut self) -> Result<Expr> {
        let mut lhs = self.bit_shifts()?;
        while self.consume_if(TokenKind::GtEq)
            || self.consume_if(TokenKind::RightArrowBracket)
            || self.consume_if(TokenKind::LeftArrowBracket)
            || self.consume_if(TokenKind::LtEq)
        {
            let tkn = self.lexemes.previous();
            let op = match tkn.kind {
                TokenKind::GtEq => BinOp::GreaterOrEq,
                TokenKind::RightArrowBracket => BinOp::Greater,
                TokenKind::LeftArrowBracket => BinOp::Lesser,
                TokenKind::LtEq => BinOp::LesserOrEq,

                _ => unreachable!(),
            };

            let rhs = self.bit_shifts()?;
            let span = self.new_span(lhs.span.start(), rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span)
        }

        Ok(lhs)
    }

    fn bit_shifts(&mut self) -> Result<Expr> {
        let mut lhs = self.term()?;

        while self.consume_if(TokenKind::ShiftLeft) || self.consume_if(TokenKind::ShiftRight) {
            let op = match self.lexemes.previous().kind {
                TokenKind::ShiftLeft => BinOp::Shl,
                TokenKind::ShiftRight => BinOp::Shr,

                _ => unreachable!(),
            };

            let rhs = self.term().map(Box::new)?;
            let span = self.new_span(lhs.span.start(), rhs.span.end(), 0);

            lhs = Expr::new(
                ExprType::BinaryExpr {
                    lhs: Box::new(lhs),
                    rhs,
                    op,
                },
                span,
            )
        }

        Ok(lhs)
    }

    fn term(&mut self) -> Result<Expr> {
        let mut lhs = self.factor()?;

        while self.consume_if(TokenKind::Plus) || self.consume_if(TokenKind::Minus) {
            let tkn = self.lexemes.previous();
            let op = match tkn.kind {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,

                _ => unreachable!(),
            };

            let rhs = self.factor()?;
            let span = self.new_span(lhs.span.start(), rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span)
        }

        Ok(lhs)
    }
    fn factor(&mut self) -> Result<Expr> {
        let mut lhs = self.unary()?;

        while self.consume_if(TokenKind::Slash) || self.consume_if(TokenKind::Star) {
            let tkn = self.lexemes.previous();
            let op = match tkn.kind {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,

                _ => unreachable!(),
            };

            let rhs = self.unary()?;
            let span = self.new_span(lhs.span.start(), rhs.span.end(), 0);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span)
        }

        Ok(lhs)
    }
    fn unary(&mut self) -> Result<Expr> {
        if self.consume_if(TokenKind::ExclamationMark) || self.consume_if(TokenKind::Minus) {
            let tok = self.lexemes.previous();

            let op = match tok.kind {
                TokenKind::ExclamationMark => UnaryOp::Not,
                TokenKind::Minus => UnaryOp::Negation,
                _ => {
                    let span = tok.span;
                    return self.error_out(ParseErrorKind::WrongUnaryOp { offender: tok }, span);
                }
            };

            let primary = self.unary()?;
            let span = self.new_span(tok.span.start(), primary.span.end(), 0);
            let expr_ty = ExprType::UnaryExpr {
                op,
                target: Box::new(primary),
            };

            return Ok(Expr::new(expr_ty, span));
        };

        self.field_access_or_method_call()
    }

    fn field_access_or_method_call(&mut self) -> Result<Expr> {
        let mut lvalue = self.fun_call()?;

        while self.consume_if(TokenKind::Dot) {
            let span_start = lvalue.span.start();
            let field = self.expect_ident_as_name()?;
            let mut span_end = field.span.end();

            let exprty = if self.consume_if(TokenKind::LeftParen) {
                // we are in a method call
                let args = self.fn_call_args()?;
                let rparen = self.expect_token(TokenKind::RightParen)?;
                span_end = rparen.span.end();

                ExprType::MethodCall {
                    args,
                    name: field,
                    receiver: Box::new(lvalue),
                }
            } else {
                ExprType::FieldAccess {
                    source: Box::new(lvalue),
                    field,
                }
            };

            lvalue = Expr::new(exprty, self.new_span(span_start, span_end, 0));
        }

        Ok(lvalue)
    }

    fn fun_call(&mut self) -> Result<Expr> {
        let callee = self.primary()?;

        if self.consume_if(TokenKind::LeftParen) {
            let mut args = vec![];

            if self.lexemes.peek_token().kind != TokenKind::RightParen {
                args.push(self.expression()?);
                while self.consume_if(TokenKind::Comma) {
                    args.push(self.expression()?);
                }
            }

            let end_paren = self.expect_token(TokenKind::RightParen)?;
            let span = self.new_span(callee.span.start(), end_paren.span.end(), 0);

            return Ok(Expr::new(
                ExprType::FunCall {
                    callee: Box::new(callee),
                    args,
                },
                span,
            ));
        }

        Ok(callee)
    }

    fn primary(&mut self) -> Result<Expr> {
        let token = self.lexemes.peek_token().to_err_if_eof()?;

        let mut span = token.span;

        let expr = match token.kind {
            TokenKind::Return => {
                self.lexemes.advance();
                // might be bad
                let ret = if matches!(
                    self.lexemes.peek_token().kind,
                    TokenKind::Semicolon | TokenKind::RightParen | TokenKind::RightSqBracket
                ) {
                    None
                } else {
                    Some(self.expression()?)
                }
                .map(Box::new);

                let end = ret.as_ref().map_or(span.end(), |tok| tok.span.end());

                return Ok(Expr::new(
                    ExprType::Return { ret },
                    self.new_span(span.start(), end, 0),
                ));
            }
            TokenKind::If => return self.if_expr(),
            TokenKind::Loop => return self.loop_expr(),
            TokenKind::For => return self.for_loop(),
            TokenKind::While => return self.while_expr(),
            TokenKind::Until => return self.until_expr(),
            TokenKind::LeftSqBracket => return self.array_expr(),
            TokenKind::Backslash => return self.lambda_expr(),

            TokenKind::IntegerLiteral(num) => Some(ExprType::Constant(ConstantExpr::Int(num))),
            TokenKind::FloatLiteral(num) => Some(ExprType::Constant(ConstantExpr::Float(num))),
            TokenKind::StringLiteral(interned) => {
                let strexpr = ConstantExpr::Str(interned);

                Some(ExprType::Constant(strexpr))
            }
            TokenKind::False => Some(ExprType::Constant(ConstantExpr::Bool(false))),
            TokenKind::True => Some(ExprType::Constant(ConstantExpr::Bool(true))),

            TokenKind::LeftParen => {
                self.lexemes.advance();
                let expr = self.expression()?;

                let token = self.lexemes.peek_token();
                if token.kind == TokenKind::RightParen {
                    span = self.new_span(span.start(), token.span.end(), 0);
                    Some(ExprType::Group(Box::new(expr)))
                } else {
                    return self.error_out(
                        ParseErrorKind::ExpectedUnknown {
                            what: "a right parenthesis",
                        },
                        span,
                    );
                }
            }

            TokenKind::Identifier(id) => Some(ExprType::Variable {
                name: Name::new(id, token.span),
            }),

            any => {
                return self.error_out(
                    ParseErrorKind::Expected {
                        what: "a literal, left parenthesis or an ident",
                        got: any,
                    },
                    token.span,
                );
            }
        };

        self.lexemes.advance();

        if let Some(expr_ty) = expr {
            return Ok(Expr::new(expr_ty, span));
        }

        self.error_out(
            ParseErrorKind::ExpectedUnknown {
                what: "an expression",
            },
            token.span,
        )
    }

    fn consume_if(&mut self, kind: TokenKind) -> bool {
        let tok = self.lexemes.peek_token();

        if tok.is_eof() {
            return false;
        }

        if tok.kind == kind {
            let _ = self.lexemes.next_token();
            return true;
        }

        false
    }

    fn new_span(&self, start: usize, end: usize, _line: u32) -> Span {
        Span::new(
            start,
            end,
            self.lexemes.peek_token().span.line,
            self.lexemes.source_id,
        )
    }

    fn expect_ident_as_name(&mut self) -> Result<Name, ParseError> {
        let tok = self.lexemes.next_token();
        if tok.is_eof() {
            return tok.to_err_if_eof().map(|_| unreachable!());
        }

        if let TokenKind::Identifier(id) = tok.kind {
            Ok(Name::new(id, tok.span))
        } else {
            let str: &'static str = Box::leak(format!("{:#?}", tok.kind).into_boxed_str());
            let kind = ParseErrorKind::Expected {
                what: str,
                got: tok.kind,
            };

            self.error_out(kind, tok.span)
        }
    }

    // except eof
    fn expect_any_token(&mut self) -> Result<Token, ParseError> {
        let tok = self.lexemes.next_token();
        if tok.is_eof() {
            return tok.to_err_if_eof();
        }

        Ok(tok)
    }

    // except eof
    fn expect_token(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        let tok = self.expect_any_token()?;

        if tok.kind != kind {
            // bad code
            let str: &'static str = Box::leak(format!("{kind:#?}").into_boxed_str());
            let kind = ParseErrorKind::Expected {
                what: str,
                got: tok.kind,
            };

            return self.error_out(kind, tok.span);
        }

        Ok(tok)
    }

    #[track_caller]
    fn error_out<T>(&mut self, kind: ParseErrorKind, span: Span) -> Result<T, ParseError> {
        let err = ParseError::new(span, kind);

        println!("erroring it out! at {}", Location::caller());
        loop {
            let next = self.lexemes.peek_token();

            if next.kind == TokenKind::Semicolon {
                self.lexemes.advance();
                break;
            }

            if matches!(
                next.kind,
                TokenKind::Let
                    | TokenKind::Instance
                    | TokenKind::Const
                    | TokenKind::Function
                    | TokenKind::For
                    | TokenKind::Until
                    | TokenKind::While
                    | TokenKind::Loop
                    | TokenKind::Return
                    | TokenKind::If
                    | TokenKind::Eof
            ) {
                break;
            }

            self.lexemes.advance();
        }

        Err(err)
    }
}
