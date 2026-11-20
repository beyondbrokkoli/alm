use crate::ast::{BinOp, CtorKey, Expr, Loc, NodeId, Stmt, UnOp};
use crate::diag::Diagnostic;
use crate::elaborate::TupleTarget;
use crate::lexer::Token;
use crate::shape::BOUNDS_FAIL_THRESHOLD;
use crate::source::SourceFile;
use crate::surface::Surface;
use std::collections::BTreeSet;
use std::iter::Peekable;

pub struct ParseError(pub Diagnostic);

pub const MAX_EXPR_DEPTH: usize = 1024;

struct Tokens<'a> {
    inner: Peekable<std::vec::IntoIter<(Token<'a>, usize)>>,
    last_off: usize,
}

impl<'a> Tokens<'a> {
    fn next(&mut self) -> Option<Token<'a>> {
        self.inner.next().map(|(t, off)| {
            self.last_off = off;
            t
        })
    }
    fn peek(&mut self) -> Option<&Token<'a>> {
        self.inner.peek().map(|(t, _)| t)
    }
    fn peek_off(&mut self) -> Option<usize> {
        self.inner.peek().map(|(_, off)| *off)
    }
}

pub struct Parser<'a> {
    tokens: Tokens<'a>,
    pub diagnostics: Vec<Diagnostic>,
    depth: usize,
    /// The one newline-table owner (Class A2): mirror kept a private
    /// copy here; here the `SourceFile` the tokens borrowed from owns
    /// it and the line math is the same.
    source: &'a SourceFile,
    /// [surface] Read at two named seams only: the ctor-key mint
    /// (`index_base`) and the for-desugar latch
    /// (`for_limit_inclusive`). P3: no private copy of either fact.
    surface: &'a Surface,
}

impl<'a> Parser<'a> {
    pub fn new(
        tokens: Vec<(Token<'a>, usize)>,
        source: &'a SourceFile,
        surface: &'a Surface,
    ) -> Self {
        Self {
            tokens: Tokens {
                inner: tokens.into_iter().peekable(),
                last_off: 0,
            },
            diagnostics: Vec::new(),
            depth: 0,
            source,
            surface,
        }
    }

    fn line_of(&self, off: usize) -> usize {
        self.source.line_of(off)
    }

    fn col_of(&self, off: usize) -> usize {
        self.source.line_col(off).1
    }

    fn err_line(&mut self) -> usize {
        match self.tokens.peek_off() {
            Some(off) => self.line_of(off),
            None => self.line_of(self.tokens.last_off),
        }
    }

    fn expect(&mut self, expected: Token<'a>) -> Result<(), ParseError> {
        let next = self.tokens.next();
        if next != Some(expected.clone()) {
            return Err(ParseError(Diagnostic::syntax(format!(
                "Expected {:?}, got {:?}",
                expected, next
            ))));
        }
        Ok(())
    }

    pub fn parse_program(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        while self.tokens.peek().is_some() {
            match self.parse_stmt() {
                Ok(stmt) => stmts.push(stmt),
                Err(e) => {
                    let line = self.err_line();
                    self.diagnostics.push(e.0.with_site(Some(line)));
                    break;
                }
            }
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        let off = self.tokens.peek_off().unwrap_or(self.tokens.last_off);
        let at = Loc {
            line: self.line_of(off) as u32,
            col: self.col_of(off) as u32,
        };
        self.parse_stmt_inner(at)
    }

    fn parse_stmt_inner(&mut self, at: Loc) -> Result<Stmt, ParseError> {
        match self.tokens.peek().cloned() {
            Some(Token::Local) => {
                self.tokens.next();
                if matches!(self.tokens.peek(), Some(Token::Function)) {
                    self.tokens.next();
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "Expected function name after 'local function'",
                            )));
                        }
                    };
                    let expr = self.parse_fn_literal()?;
                    return Ok(Stmt::LocalDecl {
                        names: vec![name],
                        exprs: vec![expr],
                        loc: at,
                        id: NodeId::mint(),
                    });
                }
                let mut names = Vec::new();
                loop {
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "Expected variable name after 'local'",
                            )));
                        }
                    };
                    names.push(name);
                    if matches!(self.tokens.peek(), Some(Token::Comma)) {
                        self.tokens.next();
                    } else {
                        break;
                    }
                }

                let mut exprs = Vec::new();
                if matches!(self.tokens.peek(), Some(Token::Assign)) {
                    self.tokens.next();
                    exprs.push(self.parse_expr()?);
                    while matches!(self.tokens.peek(), Some(Token::Comma)) {
                        self.tokens.next();
                        exprs.push(self.parse_expr()?);
                    }
                    if exprs.len() != names.len() {
                        return Err(ParseError(Diagnostic::syntax(format!(
                            "'local' binds {} names to {} values — counts must match",
                            names.len(),
                            exprs.len()
                        ))));
                    }
                }

                Ok(Stmt::LocalDecl {
                    names,
                    exprs,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::While) => {
                self.tokens.next();
                let condition = self.parse_expr()?;
                self.expect(Token::Do)?;

                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;

                Ok(Stmt::While {
                    condition,
                    body,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::For) => {
                self.tokens.next();
                let var = match self.tokens.next() {
                    Some(Token::Identifier(n)) => n.to_string(),
                    _ => {
                        return Err(ParseError(Diagnostic::syntax(
                            "Expected loop variable name after 'for'",
                        )));
                    }
                };
                self.expect(Token::Assign)?;
                let start = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let limit = self.parse_expr()?;
                if matches!(start, Expr::Float { .. }) || matches!(limit, Expr::Float { .. }) {
                    return Err(ParseError(Diagnostic::syntax(
                        "for-loop bounds must be integers",
                    )));
                }
                if matches!(self.tokens.peek(), Some(Token::Comma)) {
                    return Err(ParseError(Diagnostic::syntax(
                        "for-step is not in the dialect — 'for i = a, b do' has start and limit only",
                    )));
                }
                self.expect(Token::Do)?;

                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;

                if Self::body_assigns_to(&body, &var) {
                    return Err(ParseError(Diagnostic::syntax(format!(
                        "cannot assign to for-loop variable '{var}'"
                    ))));
                }

                // [for-limit] The latch reads the surface here and only
                // here; the guard never learns the mode exists.
                Ok(crate::elaborate::desugar_numeric_for(
                    at,
                    var,
                    start,
                    limit,
                    body,
                    self.surface.for_limit_inclusive(),
                ))
            }
            Some(Token::Break) => {
                self.tokens.next();
                Ok(Stmt::Break {
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::If) => {
                self.tokens.next();
                let condition = self.parse_expr()?;
                self.expect(Token::Then)?;

                let mut then_body = Vec::new();
                while self.peek_not_block_end() {
                    then_body.push(self.parse_stmt()?);
                }

                let mut else_body = Vec::new();
                match self.tokens.peek().cloned() {
                    Some(Token::ElseIf) => {
                        else_body.push(self.parse_elseif_chain()?);
                    }
                    Some(Token::Else) => {
                        self.tokens.next();
                        while self.peek_not_block_end() {
                            else_body.push(self.parse_stmt()?);
                        }
                        self.expect(Token::End)?;
                    }
                    Some(Token::End) => {
                        self.tokens.next();
                    }
                    _ => {
                        return Err(ParseError(Diagnostic::syntax(
                            "Expected 'else', 'elseif' or 'end' after if body",
                        )));
                    }
                }

                Ok(Stmt::If {
                    condition,
                    then_body,
                    else_body,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::Do) => {
                self.tokens.next();
                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;
                Ok(Stmt::Do {
                    body,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::Print) => {
                self.tokens.next();
                self.expect(Token::LeftParen)?;
                let mut exprs = Vec::new();
                if !matches!(self.tokens.peek(), Some(Token::RightParen)) {
                    exprs.push(self.parse_expr()?);
                    while matches!(self.tokens.peek(), Some(Token::Comma)) {
                        self.tokens.next();
                        exprs.push(self.parse_expr()?);
                    }
                }
                self.expect(Token::RightParen)?;
                Ok(Stmt::Print {
                    exprs,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::Return) => {
                self.tokens.next();
                let value = match self.tokens.peek() {
                    Some(
                        Token::Integer(_)
                        | Token::Float(_)
                        | Token::String(_)
                        | Token::True
                        | Token::False
                        | Token::Nil
                        | Token::Identifier(_)
                        | Token::LeftBrace
                        | Token::LeftParen
                        | Token::Len
                        | Token::Not
                        | Token::Minus,
                    ) => Some(self.parse_expr()?),
                    _ => None,
                };
                Ok(Stmt::Return {
                    value,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::Function) => {
                self.tokens.next();
                let name = self.parse_fn_stmt_name()?;
                let expr = self.parse_fn_literal()?;
                Ok(Stmt::Assignment {
                    name,
                    expr,
                    loc: at,
                    id: NodeId::mint(),
                })
            }
            Some(Token::Identifier(_)) => {
                let lhs = self.parse_expr()?;
                if matches!(self.tokens.peek(), Some(Token::Comma)) {
                    return self.parse_tuple_assign(at, lhs);
                }
                if matches!(self.tokens.peek(), Some(Token::Assign)) {
                    self.tokens.next();
                    let rhs = self.parse_expr()?;
                    match lhs {
                        Expr::Identifier { name, .. } => Ok(Stmt::Assignment {
                            name,
                            expr: rhs,
                            loc: at,
                            id: NodeId::mint(),
                        }),
                        Expr::Field { obj, name, .. } => Ok(Stmt::IndexAssign {
                            obj: *obj,
                            key: Expr::String {
                                value: name,
                                id: NodeId::mint(),
                            },
                            value: rhs,
                            loc: at,
                            id: NodeId::mint(),
                        }),
                        Expr::Index { obj, key, .. } => Ok(Stmt::IndexAssign {
                            obj: *obj,
                            key: *key,
                            value: rhs,
                            loc: at,
                            id: NodeId::mint(),
                        }),
                        _ => Err(ParseError(Diagnostic::syntax("Invalid assignment target"))),
                    }
                } else if matches!(lhs, Expr::Call { .. }) {
                    Ok(Stmt::Expr {
                        expr: lhs,
                        loc: at,
                        id: NodeId::mint(),
                    })
                } else if let Expr::Identifier { name, .. } = &lhs {
                    if name == "continue" {
                        Err(ParseError(Diagnostic::syntax(
                            "continue is not in the dialect — guard the \
                             rest of the body with 'if' instead",
                        )))
                    } else {
                        Err(ParseError(Diagnostic::syntax(
                            "Expected '=' (assignment) or '()' (call) after \
                             expression statement",
                        )))
                    }
                } else {
                    Err(ParseError(Diagnostic::syntax(
                        "Expected '=' (assignment) or '()' (call) after \
                         expression statement",
                    )))
                }
            }
            _ => Err(ParseError(Diagnostic::syntax(format!(
                "Unexpected statement starting with {:?}",
                self.tokens.peek()
            )))),
        }
    }

    fn parse_tuple_assign(&mut self, at: Loc, first: Expr) -> Result<Stmt, ParseError> {
        let mut targets = vec![first];
        while matches!(self.tokens.peek(), Some(Token::Comma)) {
            self.tokens.next();
            targets.push(self.parse_expr()?);
        }
        self.expect(Token::Assign)?;
        let mut values = Vec::new();
        values.push(self.parse_expr()?);
        while matches!(self.tokens.peek(), Some(Token::Comma)) {
            self.tokens.next();
            values.push(self.parse_expr()?);
        }
        if values.len() != targets.len() {
            return Err(ParseError(Diagnostic::syntax(format!(
                "tuple assignment binds {} targets to {} values — counts must match",
                targets.len(),
                values.len()
            ))));
        }
        // A name target rebinds through the latch like any plain '='
        // (T2); the checker's scope law still demands the declaration,
        // at the header's line.
        let mut slots = Vec::with_capacity(targets.len());
        for target in targets {
            match target {
                Expr::Index { obj, key, .. } => slots.push(TupleTarget::Cell {
                    obj: *obj,
                    key: *key,
                }),
                Expr::Field { obj, name, .. } => {
                    slots.push(TupleTarget::Cell {
                        obj: *obj,
                        key: Expr::String {
                            value: name,
                            id: NodeId::mint(),
                        },
                    });
                }
                Expr::Identifier { name, .. } => slots.push(TupleTarget::Name(name)),
                _ => {
                    return Err(ParseError(Diagnostic::syntax(
                        "tuple assignment targets cells or names — 't[k]', 't.k', or a \
                         declared name",
                    )));
                }
            }
        }
        Ok(crate::elaborate::desugar_tuple_assign(at, slots, values))
    }

    fn peek_not_block_end(&mut self) -> bool {
        !matches!(
            self.tokens.peek(),
            Some(Token::End) | Some(Token::Else) | Some(Token::ElseIf) | None
        )
    }

    fn parse_fn_stmt_name(&mut self) -> Result<String, ParseError> {
        let mut name = match self.tokens.next() {
            Some(Token::Identifier(n)) => n.to_string(),
            _ => {
                return Err(ParseError(Diagnostic::syntax(
                    "Expected function name after 'function'",
                )));
            }
        };
        loop {
            match self.tokens.peek() {
                Some(Token::Dot) => {
                    self.tokens.next();
                    match self.tokens.next() {
                        Some(Token::Identifier(seg)) => {
                            name.push('.');
                            name.push_str(seg);
                        }
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "Expected name segment after '.' in function \
                                 declaration",
                            )));
                        }
                    }
                }
                Some(Token::Colon) => {
                    return Err(ParseError(Diagnostic::syntax(format!(
                        "'function {name}:...' — colon methods are not surface; \
                         declare 'function {name}.<method>(receiver, ...)' and pass the \
                         receiver as an explicit first parameter"
                    ))));
                }
                _ => return Ok(name),
            }
        }
    }

    fn body_assigns_to(stmts: &[Stmt], var: &str) -> bool {
        for s in stmts {
            match s {
                Stmt::LocalDecl { names, .. } if names.iter().any(|n| n == var) => {
                    return false;
                }
                Stmt::Assignment { name, .. } if name == var => return true,
                Stmt::Do { body, .. } | Stmt::While { body, .. } => {
                    if Self::body_assigns_to(body, var) {
                        return true;
                    }
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } if Self::body_assigns_to(then_body, var)
                    || Self::body_assigns_to(else_body, var) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    fn parse_elseif_chain(&mut self) -> Result<Stmt, ParseError> {
        let off = self.tokens.peek_off().unwrap_or(self.tokens.last_off);
        let at = Loc {
            line: self.line_of(off) as u32,
            col: self.col_of(off) as u32,
        };
        self.expect(Token::ElseIf)?;
        let condition = self.parse_expr()?;
        self.expect(Token::Then)?;

        let mut then_body = Vec::new();
        while self.peek_not_block_end() {
            then_body.push(self.parse_stmt()?);
        }

        let mut else_body = Vec::new();
        match self.tokens.peek().cloned() {
            Some(Token::ElseIf) => {
                else_body.push(self.parse_elseif_chain()?);
            }
            Some(Token::Else) => {
                self.tokens.next();
                while self.peek_not_block_end() {
                    else_body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;
            }
            Some(Token::End) => {
                self.tokens.next();
            }
            _ => {
                return Err(ParseError(Diagnostic::syntax(
                    "Expected 'else', 'elseif' or 'end' after elseif body",
                )));
            }
        }

        Ok(Stmt::If {
            condition,
            then_body,
            else_body,
            loc: at,
            id: NodeId::mint(),
        })
    }

    fn with_depth<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, ParseError>,
    ) -> Result<R, ParseError> {
        self.depth += 1;
        if self.depth > MAX_EXPR_DEPTH {
            self.depth -= 1;
            return Err(ParseError(Diagnostic::syntax(format!(
                "expression nesting too deep (limit {MAX_EXPR_DEPTH} — alm's \
                 static analyses are finite; deeper source is rejected, not crashed on)"
            ))));
        }
        let r = f(self);
        self.depth -= 1;
        r
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.with_depth(|p| p.parse_or())
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;
        while let Some(Token::Or) = self.tokens.peek() {
            self.tokens.next();
            let right = self.parse_and()?;
            left = Expr::BinaryOp {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
                id: NodeId::mint(),
            };
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;
        while let Some(Token::And) = self.tokens.peek() {
            self.tokens.next();
            let right = self.parse_comparison()?;
            left = Expr::BinaryOp {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
                id: NodeId::mint(),
            };
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_concat()?;

        let op = match self.tokens.peek() {
            Some(Token::LessThan) => BinOp::LessThan,
            Some(Token::LessEq) => BinOp::LessEq,
            Some(Token::GreaterThan) => BinOp::GreaterThan,
            Some(Token::GreaterEq) => BinOp::GreaterEq,
            Some(Token::Equal) => BinOp::Equal,
            Some(Token::NotEqual) => BinOp::NotEqual,
            _ => return Ok(left),
        };
        self.tokens.next();
        let right = self.parse_term()?;
        Ok(Expr::BinaryOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
            id: NodeId::mint(),
        })
    }

    // `..` sits between comparison and +/- in Lua's precedence table.
    // Lua makes it right-associative; for pure concatenation the fold
    // order is immaterial, so this rides the same left-fold shape as
    // the arithmetic levels and the checker flattens the chain.
    fn parse_concat(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_term()?;

        while let Some(Token::DotDot) = self.tokens.peek() {
            self.tokens.next();
            let right = self.parse_term()?;
            left = Expr::BinaryOp {
                op: BinOp::Concat,
                left: Box::new(left),
                right: Box::new(right),
                id: NodeId::mint(),
            };
        }
        Ok(left)
    }

    fn parse_term(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_factor()?;

        while let Some(Token::Plus) | Some(Token::Minus) = self.tokens.peek() {
            let op = match self.tokens.next().unwrap() {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                _ => unreachable!(),
            };
            let right = self.parse_factor()?;
            left = Expr::BinaryOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
                id: NodeId::mint(),
            };
        }
        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_unary()?;

        while let Some(Token::Star)
        | Some(Token::Slash)
        | Some(Token::DoubleSlash)
        | Some(Token::Percent) = self.tokens.peek()
        {
            let op = match self.tokens.next().unwrap() {
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
                Token::DoubleSlash => BinOp::IntDiv,
                Token::Percent => BinOp::Mod,
                _ => unreachable!(),
            };
            let right = self.parse_unary()?;
            left = Expr::BinaryOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
                id: NodeId::mint(),
            };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match self.tokens.peek().cloned() {
            Some(Token::Minus) => {
                self.tokens.next();
                let expr = self.parse_unary()?;
                Ok(Expr::UnaryOp {
                    op: UnOp::Neg,
                    expr: Box::new(expr),
                    id: NodeId::mint(),
                })
            }
            Some(Token::Not) => {
                self.tokens.next();
                let expr = self.parse_unary()?;
                Ok(Expr::UnaryOp {
                    op: UnOp::Not,
                    expr: Box::new(expr),
                    id: NodeId::mint(),
                })
            }
            Some(Token::Len) => {
                self.tokens.next();
                let expr = self.parse_unary()?;
                Ok(Expr::UnaryOp {
                    op: UnOp::Len,
                    expr: Box::new(expr),
                    id: NodeId::mint(),
                })
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.tokens.peek() {
                Some(Token::LeftBracket) => {
                    self.tokens.next();
                    let key = self.parse_expr()?;
                    self.expect(Token::RightBracket)?;
                    expr = Expr::Index {
                        obj: Box::new(expr),
                        key: Box::new(key),
                        id: NodeId::mint(),
                    };
                }
                Some(Token::Dot) => {
                    self.tokens.next();
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "expected a name after '.'",
                            )));
                        }
                    };
                    expr = Expr::Field {
                        obj: Box::new(expr),
                        name,
                        id: NodeId::mint(),
                    };
                }
                Some(Token::LeftParen) => {
                    self.tokens.next();
                    let mut args = Vec::new();
                    if !matches!(self.tokens.peek(), Some(Token::RightParen)) {
                        args.push(self.parse_expr()?);
                        while matches!(self.tokens.peek(), Some(Token::Comma)) {
                            self.tokens.next();
                            args.push(self.parse_expr()?);
                        }
                    }
                    self.expect(Token::RightParen)?;
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        args,
                        id: NodeId::mint(),
                    };
                }
                _ => return Ok(expr),
            }
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.tokens.next() {
            Some(Token::Integer(val)) => Ok(Expr::Integer {
                value: val,
                id: NodeId::mint(),
            }),
            Some(Token::Float(val)) => Ok(Expr::Float {
                value: val,
                id: NodeId::mint(),
            }),
            Some(Token::True) => Ok(Expr::Boolean {
                value: true,
                id: NodeId::mint(),
            }),
            Some(Token::False) => Ok(Expr::Boolean {
                value: false,
                id: NodeId::mint(),
            }),
            Some(Token::Nil) => Ok(Expr::Nil { id: NodeId::mint() }),
            Some(Token::LeftBrace) => self.parse_table_ctor(),
            Some(Token::String(s)) => Ok(Expr::String {
                value: s.trim_matches('"').to_string(),
                id: NodeId::mint(),
            }),
            Some(Token::Identifier(name)) => {
                if name == "sys_alloc_count" && matches!(self.tokens.peek(), Some(Token::LeftParen))
                {
                    self.tokens.next();
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::SysAllocCount { id: NodeId::mint() });
                }
                if name == "sys_exec_count" && matches!(self.tokens.peek(), Some(Token::LeftParen))
                {
                    self.tokens.next();
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::SysExecCount { id: NodeId::mint() });
                }
                if name == "require" && matches!(self.tokens.peek(), Some(Token::LeftParen)) {
                    self.tokens.next();
                    let module = match self.tokens.next() {
                        Some(Token::String(module)) => module,
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "require takes one string literal — \
                                 require(\"ffi\"), require(\"async\"), and \
                                 require(\"dotted.path\") are the shapes the \
                                 dialect provides",
                            )));
                        }
                    };
                    let name = module.trim_matches('"');
                    match name {
                        "ffi" => {}
                        "async" => {
                            self.expect(Token::RightParen)?;
                            return Ok(Expr::AsyncModule { id: NodeId::mint() });
                        }
                        // any other string names a module of the source
                        // tree — it parses as an ordinary call and the
                        // pipeline's require splice resolves it against
                        // --module-root (M3). `bit` is that pass's named
                        // rejection until M5.
                        other => {
                            self.expect(Token::RightParen)?;
                            return Ok(Expr::Call {
                                callee: Box::new(Expr::Identifier {
                                    name: "require".to_string(),
                                    id: NodeId::mint(),
                                }),
                                args: vec![Expr::String {
                                    value: other.to_string(),
                                    id: NodeId::mint(),
                                }],
                                id: NodeId::mint(),
                            });
                        }
                    }
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::FfiModule { id: NodeId::mint() });
                }
                Ok(Expr::Identifier {
                    name: name.to_string(),
                    id: NodeId::mint(),
                })
            }
            Some(Token::LeftParen) => {
                let inner = self.parse_expr()?;
                self.expect(Token::RightParen)?;
                Ok(inner)
            }
            Some(Token::Function) => self.parse_fn_literal(),
            _ => Err(ParseError(Diagnostic::syntax("Expected expression"))),
        }
    }

    fn parse_fn_literal(&mut self) -> Result<Expr, ParseError> {
        self.expect(Token::LeftParen)?;
        let mut params = Vec::new();
        if !matches!(self.tokens.peek(), Some(Token::RightParen)) {
            loop {
                if matches!(self.tokens.peek(), Some(Token::Dot) | Some(Token::DotDot)) {
                    return Err(ParseError(Diagnostic::syntax(
                        "the dialect has no varargs — \
                         name your parameters",
                    )));
                }
                let name = match self.tokens.next() {
                    Some(Token::Identifier(n)) => n.to_string(),
                    _ => {
                        return Err(ParseError(Diagnostic::syntax(
                            "Expected parameter name in function header",
                        )));
                    }
                };
                if params.contains(&name) {
                    return Err(ParseError(Diagnostic::syntax(format!(
                        "duplicate parameter '{name}'"
                    ))));
                }
                params.push(name);
                if matches!(self.tokens.peek(), Some(Token::Comma)) {
                    self.tokens.next();
                } else {
                    break;
                }
            }
        }
        self.expect(Token::RightParen)?;
        let mut body = Vec::new();
        while self.tokens.peek() != Some(&Token::End) {
            if self.tokens.peek().is_none() {
                return Err(ParseError(Diagnostic::syntax(
                    "'function' body not closed by 'end'",
                )));
            }
            body.push(self.parse_stmt()?);
        }
        self.expect(Token::End)?;
        Ok(Expr::Function {
            params,
            body,
            id: NodeId::mint(),
        })
    }

    fn parse_table_ctor(&mut self) -> Result<Expr, ParseError> {
        let line = self.line_of(self.tokens.last_off);
        if matches!(self.tokens.peek(), Some(Token::RightBrace)) {
            self.tokens.next();
            return Ok(Expr::TableCtor {
                entries: Vec::new(),
                line: line as u32,
                id: NodeId::mint(),
            });
        }

        let mut entries: Vec<(CtorKey, Expr)> = Vec::new();
        let mut slots: BTreeSet<i64> = BTreeSet::new();
        let mut names: BTreeSet<String> = BTreeSet::new();
        let mut next_pos: i64 = 0;
        loop {
            let (key, value) = self.parse_ctor_entry(&mut next_pos)?;
            let record_name = match &key {
                CtorKey::Str(n) => Some(n.as_str()),
                CtorKey::Expr(Expr::String { value: s, .. }) => Some(s.as_str()),
                _ => None,
            };
            match &key {
                CtorKey::Const { slot, .. } => {
                    if !slots.insert(*slot) {
                        // [index-base] The dedup set holds physical
                        // slots; the message renders the user's key
                        // (`slot + index_base`), which is what the
                        // writer spelled and where a positional entry
                        // sits under the surface base.
                        return Err(ParseError(Diagnostic::syntax(format!(
                            "duplicate index {} in constructor — each slot may \
                             be written once (last-wins is not alm's rule)",
                            slot + self.surface.index_base()
                        ))));
                    }
                    if !names.is_empty() {
                        return Err(ParseError(Diagnostic::syntax(
                            "mixed array and record constructor elements — a \
                             constructor is an array or a record, never both",
                        )));
                    }
                }
                CtorKey::Str(_) | CtorKey::Expr(_) if record_name.is_some() => {
                    let name = record_name.unwrap();
                    if !names.insert(name.to_string()) {
                        return Err(ParseError(Diagnostic::syntax(format!(
                            "duplicate key '{name}' in constructor — each field may \
                             be written once (last-wins is not alm's rule)"
                        ))));
                    }
                    if !slots.is_empty() {
                        return Err(ParseError(Diagnostic::syntax(
                            "mixed array and record constructor elements — a \
                             constructor is an array or a record, never both",
                        )));
                    }
                }
                _ => {}
            }
            entries.push((key, value));
            if matches!(self.tokens.peek(), Some(Token::Comma)) {
                self.tokens.next();
                if matches!(self.tokens.peek(), Some(Token::RightBrace)) {
                    break;
                }
            } else {
                break;
            }
        }
        self.expect(Token::RightBrace)?;
        Ok(Expr::TableCtor {
            entries,
            line: line as u32,
            id: NodeId::mint(),
        })
    }

    fn parse_ctor_entry(&mut self, next_pos: &mut i64) -> Result<(CtorKey, Expr), ParseError> {
        if matches!(self.tokens.peek(), Some(Token::LeftBracket)) {
            self.tokens.next();
            let key = self.parse_expr()?;
            self.expect(Token::RightBracket)?;
            self.expect(Token::Assign)?;
            let value = self.parse_expr()?;
            match key {
                Expr::Integer { value: k, .. } => {
                    // [index-base] The mint choke point: a literal key
                    // shifts to physical space here and only here; a
                    // `Const` is never seam-shifted later. The bounds
                    // check reads the shifted value.
                    let slot = match k.checked_sub(self.surface.index_base()) {
                        Some(slot) => slot,
                        None => {
                            return Err(ParseError(Diagnostic::bounds("table index overflow")));
                        }
                    };
                    if slot >= BOUNDS_FAIL_THRESHOLD {
                        return Err(ParseError(Diagnostic::bounds("table index overflow")));
                    }
                    Ok((
                        CtorKey::Const {
                            slot,
                            positional: false,
                        },
                        value,
                    ))
                }
                _ => Ok((CtorKey::Expr(key), value)),
            }
        } else {
            let value = self.parse_expr()?;
            match self.tokens.peek() {
                Some(Token::Assign) => {
                    let name = match &value {
                        Expr::Identifier { name: n, .. } => n.clone(),
                        _ => {
                            return Err(ParseError(Diagnostic::syntax(
                                "expected identifier before '='",
                            )));
                        }
                    };
                    self.tokens.next();
                    let v = self.parse_expr()?;
                    Ok((CtorKey::Str(name), v))
                }
                _ => {
                    let slot = *next_pos;
                    *next_pos += 1;
                    // [index-base] Positional entries mint physical
                    // `0..k-1` in every base and never shift;
                    // `positional` is provenance only (P8).
                    Ok((
                        CtorKey::Const {
                            slot,
                            positional: true,
                        },
                        value,
                    ))
                }
            }
        }
    }
}
