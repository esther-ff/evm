use crate::arena::TypedArena;
use crate::ast::*;
use crate::lexer::{Lexemes, Span, Token, TokenKind};

type Result<T, E = ParseError> = core::result::Result<T, E>;

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub enum ParseErrorKind {
    EndOfFile,
    Expected { what: &'static str, got: TokenKind },
    ExpectedUnknown { what: &'static str },
    WrongUnaryOp { offender: Token },
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

pub struct Parser<'a> {
    lexemes: Lexemes,

    errors: &'a mut Vec<ParseError>,
    arena: TypedArena<AstDef, AstId>,
    decls: Vec<AstDef>,
}

impl<'a> Parser<'a> {
    pub fn new(lexemes: Lexemes, errors: &'a mut Vec<ParseError>) -> Self {
        Self {
            lexemes,
            errors,
            arena: TypedArena::new(),

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
            TokenKind::Eof => return tok.to_err_if_eof().map(|_| unreachable!()),

            any => {
                let err = ParseErrorKind::Expected {
                    what: "`fun` or `global`",
                    got: any,
                };
                return self.error_out(err, tok.span);
            }
        };

        Ok(decl)
    }

    pub fn ty(&mut self) -> Result<Ty> {
        todo!()
    }

    fn function_declaration(&mut self) -> Result<DefKind> {
        let start_span = self.expect_token(TokenKind::Function)?.span.start();
        let name = self.expect_ident_as_name()?;
        self.expect_token(TokenKind::LeftParen)?;
        let fun_args = self.fun_args()?;

        self.expect_token(TokenKind::RightParen)?;
        self.expect_token(TokenKind::RightArrow)?;

        let ret_type = self.ty()?;
        let block = self.block()?;

        let span = self.new_span(start_span, block.span.end(), 0);
        Ok(DefKind::function(name, fun_args, block, ret_type, span))
    }

    fn fun_args(&mut self) -> Result<FnArgs> {
        let has_self = self.self_arg();

        let mut args = Vec::new();

        while self.lexemes.peek_token().kind != TokenKind::RightParen {
            args.push(self.arg()?);

            if self.lexemes.peek_token().kind == TokenKind::Comma {
                self.lexemes.advance();
            };
        }

        Ok(FnArgs { has_self, args })
    }

    fn arg(&mut self) -> Result<Arg> {
        let name = self.expect_ident_as_name()?;
        self.expect_token(TokenKind::Colon)?;
        let ty = self.ty()?;

        Ok(Arg::new(name, ty))
    }

    fn self_arg(&mut self) -> bool {
        let tok = self.lexemes.peek_token();

        if tok.is_eof() {
            return false;
        }

        if tok.kind == TokenKind::SelfArg {
            self.lexemes.advance();

            let second_tok = self.lexemes.peek_token();

            if second_tok.kind == TokenKind::Comma {
                self.lexemes.advance();
                return true;
            }

            self.lexemes.back();
        }

        false
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

        self.field_access()
    }

    // fn special(&mut self) -> Result<Expr> {
    //     let lhs = self.primary()?;

    //     match self.lexemes.peek_token().kind {
    //         TokenKind::LeftParen => self.fun_call(lhs),
    //         TokenKind::Dot => self.field_access(lhs),

    //         _ => Ok(lhs),
    //     }
    // }

    fn field_access(&mut self) -> Result<Expr> {
        let lvalue = self.fun_call()?;

        if self.consume_if(TokenKind::Dot) {
            let span_start = lvalue.span.start();
            let expr = self.fun_call()?;

            let mut span_end = expr.span.end();
            let mut exprty = ExprType::FieldAccess {
                source: Box::new(lvalue),
                field: Box::new(expr),
            };

            while self.consume_if(TokenKind::Dot) {
                let field = self.fun_call().map(Box::new)?;
                span_end = field.span.end();

                let span = self.new_span(span_start, span_end, 0);
                let old_expr = Expr::new(exprty, span);

                exprty = ExprType::FieldAccess {
                    source: Box::new(old_expr),
                    field,
                }
            }

            return Ok(Expr::new(exprty, self.new_span(span_start, span_end, 0)));
        };

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

    fn error_out<T>(&mut self, kind: ParseErrorKind, span: Span) -> Result<T, ParseError> {
        let err = ParseError::new(span, kind);

        loop {
            if self.lexemes.previous().kind == TokenKind::Semicolon {
                break;
            }

            let next = self.lexemes.next_token();
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
            ) {
                break;
            }
        }

        Err(err)
    }
}
