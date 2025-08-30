use std::panic::Location;

#[allow(clippy::wildcard_imports)]
use crate::ast::*;
use crate::errors::DiagEmitter;
use crate::lexer::{Lexemes, Span, Token, TokenKind};
use crate::session::SymbolId;

macro_rules! t {
    ($ident:ident) => {
        TokenKind::$ident
    };
}

crate::newtyped_index!(AstId, AstIdMap, AstIdVec);

type Result<T, E = ParseError> = core::result::Result<T, E>;

pub enum ParseOutput {
    Failed,
    Normal,
}

#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
pub enum ParseError {
    EndOfFile,
    Expected { what: TokenKind, got: TokenKind },
    ExpectedDecl { got: TokenKind },
    ExpectedUnknown { what: &'static str },
    ExpectedExpr,
    WrongUnaryOp { offender: Token },
    MalformedType,
    FunctionWithoutBody,
    ExpectedConstVar,
    InvalidPattern,
}

pub enum FunctionPart {
    Signature(FnSig),
    Full(FnDecl),
}

pub enum ExprOrStmt {
    Stmt(Stmt),
    Expr(Expr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VariableReq {
    None,
    ConstAndInit,
}

pub struct Parser<'a> {
    lexemes: Lexemes,

    id: u32,
    decls: Vec<Thing>,

    diag: &'a DiagEmitter<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexemes: Lexemes, diag: &'a DiagEmitter<'a>) -> Self {
        Self {
            lexemes,
            id: 0,
            diag,

            decls: Vec::new(),
        }
    }

    fn new_id(&mut self) -> AstId {
        let id = AstId::new(self.id);
        self.id += 1;
        id
    }

    pub fn parse(mut self) -> Universe {
        let universe_id = self.new_id();

        while !self.lexemes.is_empty() {
            let id = self.new_id();
            match self.declaration() {
                Err(..) => {}
                Ok(decl) => self.decls.push(Thing::new(decl, id)),
            }
        }

        Universe {
            id: universe_id,
            thingies: self.decls,
            span: Span::DUMMY,
        }
    }

    fn declaration(&mut self) -> Result<ThingKind> {
        let tok = self.lexemes.peek_token();

        log::trace!("declaration tok={tok:#?}");
        let decl = match tok.kind {
            TokenKind::Function => ThingKind::Function(self.function_declaration()?),
            TokenKind::Global => self.global_variable_decl()?,
            TokenKind::Instance => self.instance_decl()?,
            TokenKind::Interface => unimplemented!(),
            TokenKind::Bind => ThingKind::Bind(self.bind_decl()?),
            TokenKind::Realm => self.realm_decl()?,
            TokenKind::Eof => return tok.to_err_if_eof().map(|_| unreachable!()),

            got => {
                return self.error_out(ParseError::ExpectedDecl { got }, tok.span);
            }
        };

        Ok(decl)
    }

    fn realm_decl(&mut self) -> Result<ThingKind> {
        let kw = self.expect_token(TokenKind::Realm)?;
        let name = self.expect_ident_as_name()?;
        let mut items = Vec::new();

        self.expect(t!(LeftCurlyBracket));

        while self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
            let kind = self.declaration()?;
            let thing = Thing {
                id: self.new_id(),
                kind,
            };
            items.push(thing);
        }

        let rcurly = self.expect(t!(RightCurlyBracket));

        let realm = Realm {
            id: self.new_id(),
            items,
            name,
            span: Span::between(kw.span, rcurly.span),
        };

        Ok(ThingKind::Realm(realm))
    }

    fn ty(&mut self) -> Result<Ty> {
        let id = self.new_id();
        let tok = self.lexemes.peek_token();
        match tok.kind {
            TokenKind::Function => self.parse_function_type(),
            TokenKind::LeftSqBracket => self.parse_array_type(),

            TokenKind::Identifier(..) => {
                let tok2 = self.lexemes.peek_token();
                if tok2.kind != TokenKind::LeftArrowBracket {
                    let ty = Ty {
                        id,
                        kind: self.path().map(TyKind::Path).unwrap_or(TyKind::Err),
                        span: tok.span,
                    };

                    return Ok(ty);
                }
                self.lexemes.advance();

                let mut ty_params = vec![self.ty()?];
                while self.consume_if(TokenKind::Comma) {
                    ty_params.push(self.ty()?);
                }

                todo!("generics");
            }

            _ => {
                let span = self.lexemes.peek_token().span;
                self.lexemes.advance();

                self.error_out(ParseError::MalformedType, span)
            }
        }
    }

    fn path(&mut self) -> Result<Path> {
        let mut segments = vec![self.path_segment()?];

        while self.consume_if(TokenKind::Path) {
            segments.push(self.path_segment()?);
        }

        let span = Span::between(segments[0].span, segments.last().unwrap().span);

        Ok(Path {
            path: segments,
            span,
            id: self.new_id(),
        })
    }

    fn path_segment(&mut self) -> Result<PathSeg> {
        let name = self.expect_ident_as_name()?;

        Ok(PathSeg {
            name,
            span: name.span,
            id: self.new_id(),
        })
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

        Ok(Ty {
            span: Span::between(fun_ident.span, ret.span),
            kind: TyKind::Fn {
                args: types,
                ret: Some(ret),
            },
            id: self.new_id(),
        })
    }

    pub fn parse_array_type(&mut self) -> Result<Ty> {
        let left_sq = self.expect_token(TokenKind::LeftSqBracket)?;
        let ty = self.ty().map(Box::new)?;

        let right_sq = self.expect_token(TokenKind::RightSqBracket)?;

        Ok(Ty {
            kind: TyKind::Array(ty),
            span: Span::between(left_sq.span, right_sq.span),
            id: self.new_id(),
        })
    }

    fn function_signature(&mut self) -> Result<FnSig> {
        let start_span = self.expect_token(TokenKind::Function)?.span;
        let name = self.expect_ident_as_name()?;
        self.expect_token(TokenKind::LeftParen)?;

        let fun_args = self.fun_args()?;

        self.expect_token(TokenKind::RightParen)?;
        self.expect_token(TokenKind::RightArrow)?;

        let ret_type = self.ty()?;

        let span = Span::between(start_span, ret_type.span);
        Ok(FnSig::new(name, span, ret_type, fun_args, self.new_id()))
    }

    fn function_declaration(&mut self) -> Result<FnDecl> {
        match self.function()? {
            FunctionPart::Full(decl) => Ok(decl),

            FunctionPart::Signature(sig) => {
                self.error_out(ParseError::FunctionWithoutBody, sig.span)
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
                let span = Span::between(sig.span, block.span);
                let id = self.new_id();
                let fndecl = FnDecl {
                    sig,
                    block,
                    span,
                    id,
                };
                Ok(FunctionPart::Full(fndecl))
            }

            None => Ok(FunctionPart::Signature(sig)),
        }
    }

    fn fun_args(&mut self) -> Result<Vec<Arg>> {
        let mut args = Vec::new();

        if let Some(self_arg) = self.fn_self_arg() {
            args.push(self_arg);
        }

        if self.lexemes.peek_token().kind != TokenKind::RightParen {
            args.push(self.arg()?);

            while self.consume_if(TokenKind::Comma) {
                args.push(self.arg()?);
            }
        }

        Ok(args)
    }

    fn arg(&mut self) -> Result<Arg> {
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::Colon)?;
        let ty = self.ty()?;
        let id = self.new_id();
        Ok(Arg::new(name, ty, id))
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
                Name::new(SymbolId::self_(), tok.span),
                Ty {
                    id: self.new_id(),
                    kind: TyKind::MethodSelf,
                    span: tok.span,
                },
                self.new_id(),
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

    fn bind_decl(&mut self) -> Result<Bind> {
        let keyword = self.expect_token(TokenKind::Bind)?;
        let ty = self.ty()?;
        self.expect_token(TokenKind::With)?;

        // mask as interface
        let mask = if self.lexemes.peek_token().kind == TokenKind::LeftParen {
            None
        } else {
            Some(self.path()?)
        };

        self.expect_token(TokenKind::LeftParen)?;

        let mut items = vec![];
        while !self.consume_if(TokenKind::RightParen) {
            items.push(self.bind_item()?);
        }

        Ok(Bind {
            victim: ty,
            mask,
            items,
            span: Span::between(keyword.span, self.lexemes.previous().span),
            id: self.new_id(),
        })
    }

    fn bind_item(&mut self) -> Result<BindItem> {
        let kind = match self.lexemes.peek_token().kind {
            TokenKind::Function => BindItemKind::Fun(self.function_declaration()?),
            TokenKind::Const => {
                BindItemKind::Const(self.local_variable_stmt(VariableReq::ConstAndInit)?)
            }
            _ => todo!(),
        };

        Ok(BindItem {
            kind,
            id: self.new_id(),
        })
    }

    fn instance_decl(&mut self) -> Result<ThingKind> {
        let keyword = self.expect(TokenKind::Instance);
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::LeftParen)?;

        let fields = self.instance_fields()?;
        let rcurly = self.expect(TokenKind::RightParen);
        let span = Span::between(keyword.span, rcurly.span);

        Ok(ThingKind::instance(
            name,
            span,
            fields,
            self.new_id(),
            self.new_id(),
        ))
    }

    fn instance_fields(&mut self) -> Result<Vec<Field>> {
        fn one_field(me: &mut Parser) -> Result<Field> {
            let span_start = me.lexemes.peek_token().span;
            let is_const = me.consume_if(TokenKind::Const);
            let field_name = me.expect_ident_as_name()?;

            me.expect_token(TokenKind::Colon)?;

            let ty = me.ty()?;
            let field_span = Span::between(span_start, ty.span);

            Ok(Field::new(
                is_const,
                field_name,
                ty,
                field_span,
                me.new_id(),
            ))
        }

        let peeked = self.lexemes.peek_token();
        if peeked.kind == TokenKind::RightCurlyBracket {
            return Ok(Vec::new());
        }

        let mut fields = vec![one_field(self)?];
        while self.consume_if(TokenKind::Comma) {
            if self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
                fields.push(one_field(self)?);
            }
        }

        Ok(fields)
    }

    fn local_variable_stmt(&mut self, req: VariableReq) -> Result<VariableStmt> {
        let tok = self.lexemes.next_token().to_err_if_eof()?;

        let mode = match tok.kind {
            TokenKind::Const => VarMode::Const,
            TokenKind::Let => {
                if req == VariableReq::ConstAndInit {
                    self.diag.emit_err(ParseError::ExpectedConstVar, tok.span);
                }

                VarMode::Let
            }

            _ => {
                return self.error_out(
                    ParseError::Expected {
                        what: TokenKind::Let,
                        got: tok.kind,
                    },
                    tok.span,
                );
            }
        };

        let name = self.expect_ident_as_name()?;

        self.expect(t!(Colon));

        let ty = self.ty()?;
        let tok = self.lexemes.peek_token().to_err_if_eof()?;

        let initializer: Option<Expr> = if tok.kind == TokenKind::Semicolon {
            self.lexemes.advance();
            None
        } else {
            self.expect(t!(Assign));

            let expr = self.expression()?.into();

            self.expect(t!(Semicolon));
            expr
        };

        if req == VariableReq::ConstAndInit && initializer.is_none() {
            return self.error_out(ParseError::ExpectedExpr, tok.span);
        }

        Ok(VariableStmt::new(
            mode,
            name,
            initializer,
            ty,
            self.new_id(),
        ))
    }

    fn global_variable_decl(&mut self) -> Result<ThingKind> {
        self.expect_token(TokenKind::Global)?;

        let constant = self.lexemes.peek_token().to_err_if_eof()?.kind == TokenKind::Const;
        let name = self.expect_ident_as_name()?;

        self.expect_token(TokenKind::Colon)?;

        let ty = self.ty()?;
        self.expect_token(TokenKind::Assign)?;

        let init = self.expression()?;
        self.expect_token(TokenKind::Semicolon)?;

        Ok(ThingKind::global(name, init, ty, constant, self.new_id()))
    }

    fn statement(&mut self) -> Result<ExprOrStmt> {
        let tok = self.lexemes.peek_token().to_err_if_eof()?;
        let id = self.new_id();
        let stmt = match tok.kind {
            TokenKind::Let | TokenKind::Const => {
                StmtKind::LocalVar(self.local_variable_stmt(VariableReq::None)?)
            }

            TokenKind::Function | TokenKind::Global => {
                StmtKind::Thing(Thing::new(self.declaration()?, id))
            }

            _ => {
                let expr = self.expression()?;

                if self.consume_if(TokenKind::Semicolon) {
                    StmtKind::Expr(expr)
                } else {
                    let ret = ExprOrStmt::Expr(expr);
                    return Ok(ret);
                }
            }
        };

        let span = stmt.span();

        let stmt = Stmt {
            kind: stmt,
            span,
            id: self.new_id(),
        };

        Ok(ExprOrStmt::Stmt(stmt))
    }

    fn block(&mut self) -> Result<Block> {
        let span_start = self.expect(t!(LeftCurlyBracket)).span;
        let mut stmts = Vec::new();
        let mut expr = None;

        while self.lexemes.peek_token().kind != TokenKind::RightCurlyBracket {
            match self.statement()? {
                ExprOrStmt::Stmt(stmt) => stmts.push(stmt),

                ExprOrStmt::Expr(e) => {
                    expr = Some(e);
                    break;
                }
            }
        }

        let span_end = self.expect(t!(RightCurlyBracket)).span;

        let span = Span::between(span_start, span_end);

        Ok(Block::new(stmts, span, self.new_id(), expr))
    }

    fn expression(&mut self) -> Result<Expr> {
        self.assignment()
    }

    pub fn if_expr(&mut self) -> Result<Expr> {
        let begin = self.expect_token(TokenKind::If)?;
        let expr = self.expression()?;

        let first_block = self.block()?;

        let mut end = first_block.span;
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
                Span::between(begin.span, end),
                self.new_id(),
            ));
        }

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
                Span::between(begin.span, end),
                self.new_id(),
            ));
        }

        // `if <expr> <block> else if <expr> <block> ... (else <block>)?`
        let cond = self.expression()?;
        let block = self.block()?;
        else_ifs.push(ElseIf::new(cond, block));

        while self.consume_if(TokenKind::Else) && self.consume_if(TokenKind::If) {
            let cond = self.expression()?;
            let block = self.block()?;
            end = block.span;
            else_ifs.push(ElseIf::new(cond, block));
        }

        if self.lexemes.previous().kind == TokenKind::Else {
            let block = self.block()?;
            end = block.span;
            otherwise.replace(block);
        }

        Ok(Expr::new(
            ExprType::If {
                cond: Box::new(expr),
                if_block: first_block,
                else_ifs,
                otherwise,
            },
            Span::between(begin.span, end),
            self.new_id(),
        ))
    }

    pub fn loop_expr(&mut self) -> Result<Expr> {
        let loop_ident = self.expect_token(TokenKind::Loop)?;
        let body = self.block()?;
        let span = Span::between(loop_ident.span, body.span);

        Ok(Expr::new(ExprType::Loop { body }, span, self.new_id()))
    }

    pub fn for_loop(&mut self) -> Result<Expr> {
        let for_ident = self.expect_token(TokenKind::For)?;
        let pat = self.pat()?;

        self.expect_token(TokenKind::In)?;

        let iterable = self.expression().map(Box::new)?;

        let body = self.block()?;
        let span = Span::between(for_ident.span, body.span);

        Ok(Expr::new(
            ExprType::For {
                iterable,
                pat,
                body,
            },
            span,
            self.new_id(),
        ))
    }

    pub fn pat(&mut self) -> Result<Pat> {
        let token = self.expect_any_token()?;
        let pat = match token.kind {
            TokenKind::Underscore => Pat::new(PatType::Wild, token.span),

            TokenKind::Identifier(id) => {
                let name = Name::new(id, token.span);
                Pat::new(PatType::Ident { name }, token.span)
            }

            TokenKind::LeftParen => {
                let pat = self.pat()?;
                let mut pats = vec![pat];

                while self.lexemes.peek_token().kind != TokenKind::RightParen {
                    self.expect_token(TokenKind::Comma)?;
                    pats.push(self.pat()?);
                }

                let right_paren = self.expect(t!(RightParen));

                Pat::new(
                    PatType::Tuple { pats },
                    Span::between(token.span, right_paren.span),
                )
            }

            _ => return self.error_out(ParseError::InvalidPattern, token.span),
        };

        Ok(pat)
    }

    pub fn while_expr(&mut self) -> Result<Expr> {
        let while_ident = self.expect_token(TokenKind::While)?;
        let cond = self.expression().map(Box::new)?;

        let body = self.block()?;
        let span = Span::between(while_ident.span, body.span);

        Ok(Expr::new(
            ExprType::While { cond, body },
            span,
            self.new_id(),
        ))
    }

    pub fn until_expr(&mut self) -> Result<Expr> {
        let until_ident = self.expect_token(TokenKind::Until)?;
        let cond = self.expression().map(Box::new)?;
        let body = self.block()?;
        let span = Span::between(until_ident.span, body.span);

        Ok(Expr::new(
            ExprType::Until { cond, body },
            span,
            self.new_id(),
        ))
    }

    pub fn lambda_expr(&mut self) -> Result<Expr> {
        let slash = self.expect(TokenKind::Backslash);

        let pat = self.pat()?;
        let mut args = vec![pat];
        while self.consume_if(TokenKind::Comma) {
            args.push(self.pat()?);
        }

        self.expect(TokenKind::RightArrow);

        let body = if self.lexemes.peek_token().kind == TokenKind::LeftCurlyBracket {
            LambdaBody::Block(self.block()?)
        } else {
            LambdaBody::Expr(self.expression().map(Box::new)?)
        };

        let span = Span::between(slash.span, body.span());

        Ok(Expr {
            ty: ExprType::Lambda { args, body },
            id: self.new_id(),
            span,
        })
    }

    pub fn list_expr(&mut self) -> Result<Expr> {
        let left_sq = self.expect_token(TokenKind::LeftSqBracket)?;
        let mut exprs = vec![];

        loop {
            if self.lexemes.peek_token().kind == TokenKind::RightSqBracket {
                break;
            } else if self.lexemes.previous().kind != TokenKind::LeftSqBracket {
                self.expect(t!(Comma));
            }

            exprs.push(self.expression()?);
        }

        let right_sq = self.expect(TokenKind::RightSqBracket);

        Ok(Expr::new(
            ExprType::List(exprs),
            Span::between(left_sq.span, right_sq.span),
            self.new_id(),
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
        let span = Span::between(lvalue.span, rvalue.span);

        let expr_ty = ExprType::Assign {
            lvalue: Box::new(lvalue),
            rvalue: Box::new(rvalue),
            mode,
        };

        Ok(Expr::new(expr_ty, span, self.new_id()))
    }

    fn bitwise_or(&mut self) -> Result<Expr> {
        let mut lhs = self.bitwise_xor()?;

        let start = lhs.span;

        while self.consume_if(TokenKind::BitOr) {
            let rhs = self.bitwise_xor()?;
            let span = Span::between(start, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitOr,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
        }

        Ok(lhs)
    }

    fn bitwise_xor(&mut self) -> Result<Expr> {
        let mut lhs = self.bitwise_and()?;
        let start = lhs.span;

        while self.consume_if(TokenKind::Xor) {
            let rhs = self.bitwise_and()?;
            let span = Span::between(start, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitXor,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
        }

        Ok(lhs)
    }

    fn bitwise_and(&mut self) -> Result<Expr> {
        let mut lhs = self.logic_or()?;
        let start = lhs.span;

        while self.consume_if(TokenKind::BitAnd) {
            let rhs = self.logic_or()?;
            let span = Span::between(start, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::BitAnd,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
        }

        Ok(lhs)
    }

    fn logic_or(&mut self) -> Result<Expr> {
        let mut lhs = self.logic_and()?;
        let start = lhs.span;

        while self.consume_if(TokenKind::LogicalOr) {
            let rhs = self.logic_and()?;
            let span = Span::between(start, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::LogicalOr,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
        }

        Ok(lhs)
    }

    fn logic_and(&mut self) -> Result<Expr> {
        let mut lhs = self.equality()?;
        let start = lhs.span;

        while self.consume_if(TokenKind::LogicalAnd) {
            let rhs = self.equality()?;
            let span = Span::between(start, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: BinOp::LogicalAnd,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
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
            let span = Span::between(lhs.span, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
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
            let span = Span::between(lhs.span, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
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
            let span = Span::between(lhs.span, rhs.span);

            lhs = Expr::new(
                ExprType::BinaryExpr {
                    lhs: Box::new(lhs),
                    rhs,
                    op,
                },
                span,
                self.new_id(),
            );
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
            let span = Span::between(lhs.span, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
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
            let span = Span::between(lhs.span, rhs.span);
            let expr_ty = ExprType::BinaryExpr {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };

            lhs = Expr::new(expr_ty, span, self.new_id());
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
                    return self.error_out(ParseError::WrongUnaryOp { offender: tok }, span);
                }
            };

            let primary = self.unary()?;
            let span = Span::between(tok.span, primary.span);
            let expr_ty = ExprType::UnaryExpr {
                op,
                target: Box::new(primary),
            };

            return Ok(Expr::new(expr_ty, span, self.new_id()));
        }

        self.index_expr()
    }

    fn index_expr(&mut self) -> Result<Expr> {
        let mut expr = self.field_access_or_method_call()?;

        while self.consume_if(t!(LeftSqBracket)) {
            let index = self.expression().map(Box::new)?;
            let rbrkt = self.expect(t!(RightSqBracket));
            let span = expr.span;

            expr = Expr::new(
                ExprType::Index {
                    indexed: Box::new(expr),
                    index,
                },
                Span::between(span, rbrkt.span),
                self.new_id(),
            );
        }

        Ok(expr)
    }

    fn field_access_or_method_call(&mut self) -> Result<Expr> {
        let tok = self.lexemes.peek_token();
        let mut lvalue = if let TokenKind::SelfArg = tok.kind {
            self.lexemes.advance();
            Expr::new(
                ExprType::Path(Path {
                    path: vec![PathSeg {
                        name: Name {
                            interned: SymbolId::self_(),
                            span: tok.span,
                        },
                        span: tok.span,
                        id: self.new_id(),
                    }],
                    id: self.new_id(),
                    span: tok.span,
                }),
                tok.span,
                self.new_id(),
            )
        } else {
            self.fun_call()?
        };

        while self.consume_if(TokenKind::Dot) {
            let span_start = lvalue.span;
            let field = self.expect_ident_as_name()?;
            let mut span_end = field.span;

            let exprty = if self.consume_if(TokenKind::LeftParen) {
                // we are in a method call
                let args = self.fn_call_args()?;
                let rparen = self.expect_token(TokenKind::RightParen)?;
                span_end = rparen.span;

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

            lvalue = Expr::new(exprty, Span::between(span_start, span_end), self.new_id());
        }

        Ok(lvalue)
    }

    #[track_caller]
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
            let span = Span::between(callee.span, end_paren.span);

            return Ok(Expr::new(
                ExprType::FunCall {
                    callee: Box::new(callee),
                    args,
                },
                span,
                self.new_id(),
            ));
        }

        Ok(callee)
    }

    fn return_expr(&mut self, tok: Token) -> Result<Expr> {
        let span = tok.span;
        self.lexemes.advance();
        let ret = if matches!(
            self.lexemes.peek_token().kind,
            TokenKind::Semicolon | TokenKind::RightParen | TokenKind::RightSqBracket
        ) {
            None
        } else {
            Some(self.expression()?)
        }
        .map(Box::new);

        let end = ret.as_ref().map_or(span, |tok| tok.span);

        Ok(Expr::new(
            ExprType::Return { ret },
            Span::between(span, end),
            self.new_id(),
        ))
    }

    fn primary(&mut self) -> Result<Expr> {
        let token = self.lexemes.peek_token().to_err_if_eof()?;

        match token.kind {
            TokenKind::Return => self.return_expr(token),

            TokenKind::If => self.if_expr(),
            TokenKind::Loop => self.loop_expr(),
            TokenKind::For => self.for_loop(),
            TokenKind::While => self.while_expr(),
            TokenKind::Until => self.until_expr(),
            TokenKind::LeftSqBracket => self.list_expr(),
            TokenKind::Backslash => self.lambda_expr(),

            TokenKind::IntegerLiteral(..)
            | TokenKind::FloatLiteral(..)
            | TokenKind::False
            | TokenKind::True
            | TokenKind::StringLiteral(..) => Ok(self.literals(token.kind)),
            TokenKind::LeftParen => self.group_exprs(),
            TokenKind::Identifier(..) => self.path_expr(),

            TokenKind::LeftCurlyBracket => {
                let block = self.block()?;
                let block_span = block.span;

                Ok(Expr::new(ExprType::Block(block), block_span, self.new_id()))
            }

            _ => self.error_out(ParseError::ExpectedExpr, token.span),
        }
    }

    fn literals(&mut self, tkn: TokenKind) -> Expr {
        let actual = self.lexemes.next_token();

        let expr_ty = match tkn {
            TokenKind::IntegerLiteral(num) => ExprType::Constant(ConstantExpr::Int(num)),
            TokenKind::FloatLiteral(num) => ExprType::Constant(ConstantExpr::Float(num)),
            TokenKind::StringLiteral(interned) => {
                let strexpr = ConstantExpr::Str(interned);

                ExprType::Constant(strexpr)
            }
            TokenKind::False => ExprType::Constant(ConstantExpr::Bool(false)),
            TokenKind::True => ExprType::Constant(ConstantExpr::Bool(true)),

            _ => unreachable!(),
        };

        Expr::new(expr_ty, actual.span, self.new_id())
    }

    fn group_exprs(&mut self) -> Result<Expr> {
        let lparen = self.lexemes.next_token();
        let expr = self.expression()?;
        let rparen = self.expect(t!(RightParen));

        Ok(Expr::new(
            ExprType::Group(Box::new(expr)),
            Span::between(lparen.span, rparen.span),
            self.new_id(),
        ))
    }

    fn path_expr(&mut self) -> Result<Expr> {
        let path = self.path()?;
        let mut span = path.span;
        let mut ty = ExprType::Path(path);

        if self.consume_if(t!(LeftSqBracket)) {
            let idx = self.expression()?;
            let tok = self.expect(t!(RightSqBracket));

            ty = ExprType::Index {
                indexed: Box::new(Expr::new(ty, span, self.new_id())),
                index: Box::new(idx),
            };

            span = Span::between(span, tok.span);
        }

        Ok(Expr::new(ty, span, self.new_id()))
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

    fn expect_ident_as_name(&mut self) -> Result<Name, ParseError> {
        let tok = self.lexemes.next_token();
        if tok.is_eof() {
            return tok.to_err_if_eof().map(|_| unreachable!());
        }

        if let TokenKind::Identifier(id) = tok.kind {
            Ok(Name::new(id, tok.span))
        } else {
            let kind = ParseError::Expected {
                what: TokenKind::Identifier(SymbolId::DUMMY),
                got: tok.kind,
            };

            self.error_out(kind, tok.span)
        }
    }

    fn expect(&mut self, exp: TokenKind) -> Token {
        let next = self.lexemes.peek_token();

        if next.kind == exp {
            self.lexemes.advance();
            return next;
        }

        self.diag.emit_err(
            ParseError::Expected {
                what: exp,
                got: next.kind,
            },
            next.span,
        );

        Token::new(next.span, exp)
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
    #[track_caller]
    fn expect_token(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        let tok = self.expect_any_token()?;

        if tok.kind != kind {
            let kind = ParseError::Expected {
                what: kind,
                got: tok.kind,
            };

            return self.error_out(kind, tok.span);
        }

        Ok(tok)
    }

    #[track_caller]
    fn error_out<T>(&mut self, kind: ParseError, span: Span) -> Result<T, ParseError> {
        log::error!("`error_out` called at {}", Location::caller());
        let mut end_span = None;

        while !self.lexemes.is_empty() {
            if self.lexemes.previous().kind == TokenKind::Semicolon {
                end_span = Some(self.lexemes.previous().span);
                break;
            }

            match self.lexemes.peek_token().kind {
                TokenKind::RightSqBracket | TokenKind::RightParen | TokenKind::Eof => {
                    self.lexemes.advance();
                    break;
                }

                _ => self.lexemes.advance(),
            }
        }

        self.diag
            .emit_err(kind, end_span.map_or(span, |end| Span::between(span, end)));

        Err(kind)
    }
}
