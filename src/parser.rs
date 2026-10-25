use crate::ast::{BinOp, CtorKey, Expr, Stmt, UnOp};
use crate::lexer::Token;
use crate::shape::BOUNDS_FAIL_THRESHOLD;
use std::collections::BTreeSet;
use std::iter::Peekable;

pub struct ParseError(pub String);

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
    pub diagnostics: Vec<String>,
    depth: usize,
    newlines: Vec<usize>,
    pub stmt_line_seq: Vec<usize>,
    pub stmt_col_seq: Vec<usize>,
    pub ctor_line_seq: Vec<usize>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<(Token<'a>, usize)>, source: &str) -> Self {
        Self {
            tokens: Tokens {
                inner: tokens.into_iter().peekable(),
                last_off: 0,
            },
            diagnostics: Vec::new(),
            depth: 0,
            newlines: source
                .bytes()
                .enumerate()
                .filter(|(_, b)| *b == b'\n')
                .map(|(i, _)| i)
                .collect(),
            stmt_line_seq: Vec::new(),
            stmt_col_seq: Vec::new(),
            ctor_line_seq: Vec::new(),
        }
    }

    fn line_of(&self, off: usize) -> usize {
        1 + self.newlines.partition_point(|&n| n < off)
    }

    fn col_of(&self, off: usize) -> usize {
        match self
            .line_of(off)
            .checked_sub(2)
            .and_then(|i| self.newlines.get(i))
        {
            Some(&nl) => off - nl,
            None => off + 1,
        }
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
            return Err(ParseError(format!(
                "Syntax Error: Expected {:?}, got {:?}",
                expected, next
            )));
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
                    self.diagnostics.push(format!("line {line}: {}", e.0));
                    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_GHOST_BAIL_PARSER);
                    break;
                }
            }
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        let off = self.tokens.peek_off().unwrap_or(self.tokens.last_off);
        self.stmt_line_seq.push(self.line_of(off));
        self.stmt_col_seq.push(self.col_of(off));
        self.parse_stmt_inner()
    }

    fn parse_stmt_inner(&mut self) -> Result<Stmt, ParseError> {
        match self.tokens.peek().cloned() {
            Some(Token::Local) => {
                self.tokens.next();
                // `local function f(...) ... end` — the named-sugar local
                // flavor: desugars to the plain LocalDecl binding shape
                // (no new semantics)
                if matches!(self.tokens.peek(), Some(Token::Function)) {
                    self.tokens.next();
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(
                                "Syntax Error: Expected function name after 'local function'"
                                    .into(),
                            ));
                        }
                    };
                    let expr = self.parse_fn_literal()?;
                    return Ok(Stmt::LocalDecl {
                        names: vec![name],
                        exprs: vec![expr],
                    });
                }
                let mut names = Vec::new();
                loop {
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(
                                "Syntax Error: Expected variable name after 'local'".into(),
                            ));
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
                        return Err(ParseError(format!(
                            "Syntax Error: 'local' binds {} names to {} values — counts must match",
                            names.len(),
                            exprs.len()
                        )));
                    }
                }

                Ok(Stmt::LocalDecl { names, exprs })
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

                Ok(Stmt::While { condition, body })
            }
            Some(Token::For) => {
                // parse_stmt pushed one seq entry for the desugared Stmt::Do.
                // record_stmt_lines consumes entries in AST pre-order, so the
                // synthesized LocalDecl, While, and inner-body Do need their
                // own entries BEFORE the body parses, and the synthetic
                // i = i + 1 one after — all pointing at the for header,
                // desugared code reports there.
                let for_line = *self.stmt_line_seq.last().unwrap_or(&1);
                let for_col = *self.stmt_col_seq.last().unwrap_or(&1);
                self.stmt_line_seq.push(for_line);
                self.stmt_line_seq.push(for_line);
                self.stmt_line_seq.push(for_line);
                self.stmt_col_seq.push(for_col);
                self.stmt_col_seq.push(for_col);
                self.stmt_col_seq.push(for_col);

                self.tokens.next();
                let var = match self.tokens.next() {
                    Some(Token::Identifier(n)) => n.to_string(),
                    _ => {
                        return Err(ParseError(
                            "Syntax Error: Expected loop variable name after 'for'".into(),
                        ));
                    }
                };
                self.expect(Token::Assign)?;
                let start = self.parse_expr()?;
                self.expect(Token::Comma)?;
                let limit = self.parse_expr()?;
                self.expect(Token::Do)?;

                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;

                self.stmt_line_seq.push(for_line);
                self.stmt_col_seq.push(for_col);

                if Self::body_assigns_to(&body, &var) {
                    return Err(ParseError(format!(
                        "Syntax Error: cannot assign to for-loop variable '{var}'"
                    )));
                }

                // Desugar: for i = a, b do B end is half-open (a ..< b) and
                // becomes Do[ local i = a, While i < b { Do[ B ]; i = i + 1 } ]
                // so the existing while phi/fill machinery handles everything.
                // The user body rides its own inner scope: a `local i` in B
                // shadows the counter only inside B, so the synthetic
                // increment after it still reaches the counter (without the
                // wrap it would increment the shadow — an infinite loop).
                // Analysis walks the desugared tree, so *const Stmt keys
                // stay consistent.
                let increment = Stmt::Assignment {
                    name: var.clone(),
                    expr: Expr::BinaryOp {
                        op: BinOp::Add,
                        left: Box::new(Expr::Identifier(var.clone())),
                        right: Box::new(Expr::Integer(1)),
                    },
                };
                Ok(Stmt::Do {
                    body: vec![
                        Stmt::LocalDecl {
                            names: vec![var.clone()],
                            exprs: vec![start],
                        },
                        Stmt::While {
                            condition: Expr::BinaryOp {
                                op: BinOp::LessThan,
                                left: Box::new(Expr::Identifier(var)),
                                right: Box::new(limit),
                            },
                            body: vec![Stmt::Do { body }, increment],
                        },
                    ],
                })
            }
            Some(Token::Break) => {
                self.tokens.next();
                Ok(Stmt::Break)
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
                        return Err(ParseError(
                            "Syntax Error: Expected 'else', 'elseif' or 'end' after if body".into(),
                        ));
                    }
                }

                Ok(Stmt::If {
                    condition,
                    then_body,
                    else_body,
                })
            }
            Some(Token::Do) => {
                self.tokens.next();
                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;
                Ok(Stmt::Do { body })
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
                Ok(Stmt::Print { exprs })
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
                Ok(Stmt::Return { value })
            }
            Some(Token::Function) => {
                // D4 surface sugar, pure desugar — no new semantics:
                // `function f(args) body end` and `function A.b(args)
                // body end` become today's fn-ASSIGNMENT shape — a
                // REDEFINITION (the Lexical Law: last textual definition
                // wins), so a second declaration rebinds rather than
                // redeclares. The dotted name rides as ONE string key
                // (the fn maps are String-keyed); deeper chains `A.B.c`
                // fall out the same way. The desugar is 1 AST stmt per
                // parse_stmt call, so the stmt_line_seq pre-push stays
                // exact (H5).
                self.tokens.next();
                let name = self.parse_fn_stmt_name()?;
                let expr = self.parse_fn_literal()?;
                Ok(Stmt::Assignment { name, expr })
            }
            Some(Token::Identifier(_)) => {
                let lhs = self.parse_expr()?;
                if matches!(self.tokens.peek(), Some(Token::Assign)) {
                    self.tokens.next();
                    let rhs = self.parse_expr()?;
                    match lhs {
                        Expr::Identifier(name) => Ok(Stmt::Assignment { name, expr: rhs }),
                        Expr::Field { obj, name } => {
                            // dot write sugar desugars to a string-keyed
                            // index at parse time (the checker later
                            // rejects a non-table receiver)
                            alm_rt::trace::compiler_trace_signal(
                                alm_rt::trace::TRACE_PARSE_STRKEY_DOT,
                            );
                            Ok(Stmt::IndexAssign {
                                obj: *obj,
                                key: Expr::String(name),
                                value: rhs,
                            })
                        }
                        Expr::Index { obj, key } => Ok(Stmt::IndexAssign {
                            obj: *obj,
                            key: *key,
                            value: rhs,
                        }),
                        _ => Err(ParseError("Syntax Error: Invalid assignment target".into())),
                    }
                } else if matches!(lhs, Expr::Call { .. }) {
                    Ok(Stmt::Expr { expr: lhs })
                } else {
                    Err(ParseError(
                        "Syntax Error: Expected '=' (assignment) or '()' (call) after \
                         expression statement"
                            .into(),
                    ))
                }
            }
            _ => Err(ParseError(format!(
                "Syntax Error: Unexpected statement starting with {:?}",
                self.tokens.peek()
            ))),
        }
    }

    fn peek_not_block_end(&mut self) -> bool {
        !matches!(
            self.tokens.peek(),
            Some(Token::End) | Some(Token::Else) | Some(Token::ElseIf) | None
        )
    }

    /// The statement-sugar name: `f`, `A.b`, `A.B.c` — one dotted
    /// string. Colon methods reject with their dedicated message.
    fn parse_fn_stmt_name(&mut self) -> Result<String, ParseError> {
        let mut name = match self.tokens.next() {
            Some(Token::Identifier(n)) => n.to_string(),
            _ => {
                return Err(ParseError(
                    "Syntax Error: Expected function name after 'function'".into(),
                ));
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
                            return Err(ParseError(
                                "Syntax Error: Expected name segment after '.' in function \
                                 declaration"
                                    .into(),
                            ));
                        }
                    }
                }
                Some(Token::Colon) => {
                    return Err(ParseError(format!(
                        "Syntax Error: 'function {name}:...' — colon methods are not surface; \
                         declare 'function {name}.<method>(receiver, ...)' and pass the \
                         receiver as an explicit first parameter"
                    )));
                }
                _ => return Ok(name),
            }
        }
    }

    /// Unlike has_break, assignments to the loop variable are rejected even
    /// from nested While bodies (they still mutate the outer loop var), and a
    /// LocalDecl of the same name shadows it for the rest of its block.
    fn body_assigns_to(stmts: &[Stmt], var: &str) -> bool {
        for s in stmts {
            match s {
                Stmt::LocalDecl { names, .. } if names.iter().any(|n| n == var) => {
                    return false;
                }
                Stmt::Assignment { name, .. } if name == var => return true,
                Stmt::Do { body } | Stmt::While { body, .. } => {
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
        self.stmt_line_seq.push(self.line_of(off));
        self.stmt_col_seq.push(self.col_of(off));
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
                return Err(ParseError(
                    "Syntax Error: Expected 'else', 'elseif' or 'end' after elseif body".into(),
                ));
            }
        }

        Ok(Stmt::If {
            condition,
            then_body,
            else_body,
        })
    }

    fn with_depth<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, ParseError>,
    ) -> Result<R, ParseError> {
        self.depth += 1;
        if self.depth > MAX_EXPR_DEPTH {
            self.depth -= 1;
            return Err(ParseError(format!(
                "Syntax Error: expression nesting too deep (limit {MAX_EXPR_DEPTH} — alm's \
                 static analyses are finite; deeper source is rejected, not crashed on)"
            )));
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
            };
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_term()?;

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
        })
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
                })
            }
            Some(Token::Not) => {
                self.tokens.next();
                let expr = self.parse_unary()?;
                Ok(Expr::UnaryOp {
                    op: UnOp::Not,
                    expr: Box::new(expr),
                })
            }
            Some(Token::Len) => {
                self.tokens.next();
                let expr = self.parse_unary()?;
                Ok(Expr::UnaryOp {
                    op: UnOp::Len,
                    expr: Box::new(expr),
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
                    };
                }
                Some(Token::Dot) => {
                    self.tokens.next();
                    let name = match self.tokens.next() {
                        Some(Token::Identifier(n)) => n.to_string(),
                        _ => {
                            return Err(ParseError(
                                "Syntax Error: expected a name after '.'".into(),
                            ));
                        }
                    };
                    expr = Expr::Field {
                        obj: Box::new(expr),
                        name,
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
                    };
                }
                _ => return Ok(expr),
            }
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.tokens.next() {
            Some(Token::Integer(val)) => Ok(Expr::Integer(val)),
            Some(Token::Float(val)) => Ok(Expr::Float(val)),
            Some(Token::True) => Ok(Expr::Boolean(true)),
            Some(Token::False) => Ok(Expr::Boolean(false)),
            Some(Token::Nil) => Ok(Expr::Nil),
            Some(Token::LeftBrace) => self.parse_table_ctor(),
            Some(Token::String(s)) => Ok(Expr::String(s.trim_matches('"').to_string())),
            Some(Token::Identifier(name)) => {
                if name == "sys_alloc_count" && matches!(self.tokens.peek(), Some(Token::LeftParen))
                {
                    self.tokens.next();
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::SysAllocCount);
                }
                if name == "sys_exec_count" && matches!(self.tokens.peek(), Some(Token::LeftParen))
                {
                    self.tokens.next();
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::SysExecCount);
                }
                if name == "require" && matches!(self.tokens.peek(), Some(Token::LeftParen)) {
                    self.tokens.next();
                    let module = match self.tokens.next() {
                        Some(Token::String(module)) => module,
                        _ => {
                            return Err(ParseError(
                                "Syntax Error: require takes one string literal — \
                                 require(\"ffi\") and require(\"coroutine\") are the \
                                 modules the dialect provides"
                                    .into(),
                            ));
                        }
                    };
                    let name = module.trim_matches('"');
                    match name {
                        "ffi" => {}
                        "coroutine" => {
                            self.expect(Token::RightParen)?;
                            return Ok(Expr::CoroModule);
                        }
                        other => {
                            return Err(ParseError(format!(
                                "Syntax Error: require(\"{other}\") — the dialect provides \
                                 only require(\"ffi\") (the mocked LuaJIT ffi surface) and \
                                 require(\"coroutine\") (the OS-thread parody of Lua's \
                                 cooperative coroutines)"
                            )));
                        }
                    }
                    self.expect(Token::RightParen)?;
                    return Ok(Expr::FfiModule);
                }
                Ok(Expr::Identifier(name.to_string()))
            }
            Some(Token::LeftParen) => {
                let inner = self.parse_expr()?;
                self.expect(Token::RightParen)?;
                Ok(inner)
            }
            Some(Token::Function) => self.parse_fn_literal(),
            _ => Err(ParseError("Syntax Error: Expected expression".into())),
        }
    }

    /// The one fn-literal producer: everything after the `function`
    /// keyword — `(params) body end`. Shared by the expression face and
    /// the D4 statement sugar.
    fn parse_fn_literal(&mut self) -> Result<Expr, ParseError> {
        self.expect(Token::LeftParen)?;
        let mut params = Vec::new();
        if !matches!(self.tokens.peek(), Some(Token::RightParen)) {
            loop {
                if matches!(self.tokens.peek(), Some(Token::Dot)) {
                    return Err(ParseError(
                        "Syntax Error: the dialect has no varargs — \
                         name your parameters"
                            .into(),
                    ));
                }
                let name = match self.tokens.next() {
                    Some(Token::Identifier(n)) => n.to_string(),
                    _ => {
                        return Err(ParseError(
                            "Syntax Error: Expected parameter name in function header".into(),
                        ));
                    }
                };
                if params.contains(&name) {
                    return Err(ParseError(format!(
                        "Syntax Error: duplicate parameter '{name}'"
                    )));
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
                return Err(ParseError(
                    "Syntax Error: 'function' body not closed by 'end'".into(),
                ));
            }
            body.push(self.parse_stmt()?);
        }
        self.expect(Token::End)?;
        Ok(Expr::Function { params, body })
    }

    fn parse_table_ctor(&mut self) -> Result<Expr, ParseError> {
        self.ctor_line_seq.push(self.line_of(self.tokens.last_off));
        if matches!(self.tokens.peek(), Some(Token::RightBrace)) {
            self.tokens.next();
            alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_TBL_EMPTY);
            return Ok(Expr::TableCtor(Vec::new()));
        }

        let mut entries: Vec<(CtorKey, Expr)> = Vec::new();
        let mut slots: BTreeSet<i64> = BTreeSet::new();
        // Record field identity: a named key and a literal-string expr key
        // name the same field, so both dedupe through one set. (A dynamic
        // expr key's type is the checker's call — see its TableCtor arm.)
        let mut names: BTreeSet<String> = BTreeSet::new();
        let mut next_pos: i64 = 0;
        loop {
            let (key, value) = self.parse_ctor_entry(&mut next_pos)?;
            let record_name = match &key {
                CtorKey::Str(n) => Some(n.as_str()),
                CtorKey::Expr(Expr::String(s)) => Some(s.as_str()),
                _ => None,
            };
            match &key {
                CtorKey::Const(slot) => {
                    if !slots.insert(*slot) {
                        return Err(ParseError(format!(
                            "Syntax Error: duplicate index {slot} in constructor — each slot may \
                             be written once (last-wins is not alm's rule)"
                        )));
                    }
                    if !names.is_empty() {
                        return Err(ParseError(
                            "Syntax Error: mixed array and record constructor elements — a \
                             constructor is an array or a record, never both"
                                .into(),
                        ));
                    }
                }
                CtorKey::Str(_) | CtorKey::Expr(_) if record_name.is_some() => {
                    let name = record_name.unwrap();
                    if !names.insert(name.to_string()) {
                        return Err(ParseError(format!(
                            "Syntax Error: duplicate key '{name}' in constructor — each field may \
                             be written once (last-wins is not alm's rule)"
                        )));
                    }
                    if !slots.is_empty() {
                        return Err(ParseError(
                            "Syntax Error: mixed array and record constructor elements — a \
                             constructor is an array or a record, never both"
                                .into(),
                        ));
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
        alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_TBL_CTOR);
        Ok(Expr::TableCtor(entries))
    }

    fn parse_ctor_entry(&mut self, next_pos: &mut i64) -> Result<(CtorKey, Expr), ParseError> {
        if matches!(self.tokens.peek(), Some(Token::LeftBracket)) {
            self.tokens.next();
            let key = self.parse_expr()?;
            self.expect(Token::RightBracket)?;
            self.expect(Token::Assign)?;
            let value = self.parse_expr()?;
            match key {
                Expr::Integer(k) => {
                    if k >= BOUNDS_FAIL_THRESHOLD {
                        return Err(ParseError(
                            "Table Bounds Error: table index overflow".into(),
                        ));
                    }
                    Ok((CtorKey::Const(k), value))
                }
                _ => {
                    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_TBL_EXPR_KEY);
                    Ok((CtorKey::Expr(key), value))
                }
            }
        } else {
            let value = self.parse_expr()?;
            match self.tokens.peek() {
                Some(Token::Assign) => {
                    let name = match &value {
                        Expr::Identifier(n) => n.clone(),
                        _ => {
                            return Err(ParseError(
                                "Syntax Error: expected identifier before '='".into(),
                            ));
                        }
                    };
                    self.tokens.next(); // consume '='
                    let v = self.parse_expr()?;
                    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_STRKEY_NAMED);
                    Ok((CtorKey::Str(name), v))
                }
                _ => {
                    let slot = *next_pos;
                    *next_pos += 1;
                    Ok((CtorKey::Const(slot), value))
                }
            }
        }
    }
}
