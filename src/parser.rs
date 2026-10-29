use crate::ast::{BinOp, CtorKey, Expr, Loc, Stmt, UnOp};
use crate::diag::Diagnostic;
use crate::lexer::Token;
use crate::shape::BOUNDS_FAIL_THRESHOLD;
use std::collections::BTreeSet;
use std::iter::Peekable;

/// A parse rejection — always the Syntax face; `parse_program` stamps
/// the site off the token stream (H11: the line rides the Diagnostic,
/// one formatter renders it).
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
    newlines: Vec<usize>,
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
                    // the ONE site-stamp: the parser knows the offending
                    // line from the token stream; render derives the rest
                    let line = self.err_line();
                    self.diagnostics.push(e.0.with_site(Some(line)));
                    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_GHOST_BAIL_PARSER);
                    break;
                }
            }
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        let off = self.tokens.peek_off().unwrap_or(self.tokens.last_off);
        // The stamp rides the node from birth (H5): captured once,
        // handed to whatever Stmt this parse mints — desugars copy it
        // instead of re-deriving anything. There is no second
        // representation to keep in step.
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
                // `local function f(...) ... end` — the named-sugar local
                // flavor: desugars to the plain LocalDecl binding shape
                // (no new semantics)
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
                })
            }
            Some(Token::For) => {
                // R7's law, structural since H5: the desugar's six
                // statements (block Do, counter decl, for$limit latch
                // decl, While, inner-body Do, synthetic increment) all
                // carry `at` — the for header's stamp — so desugared
                // code reports there. The shape lives in the pure
                // elaborator (elaborate.rs, H8); the census
                // (analysis.rs) pins it on every compile.
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
                // Checked at the bound's own token so the reported line is
                // the header, not the body's `end` (a float that arrives
                // through a name still meets the checker's mixed-operand
                // law at the same header line).
                if matches!(start, Expr::Float(_)) || matches!(limit, Expr::Float(_)) {
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

                // Desugar: the pure elaborator owns the shape (H8).
                Ok(crate::elaborate::desugar_numeric_for(
                    at, var, start, limit, body,
                ))
            }
            Some(Token::Break) => {
                self.tokens.next();
                Ok(Stmt::Break { loc: at })
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
                })
            }
            Some(Token::Do) => {
                self.tokens.next();
                let mut body = Vec::new();
                while self.tokens.peek() != Some(&Token::End) {
                    body.push(self.parse_stmt()?);
                }
                self.expect(Token::End)?;
                Ok(Stmt::Do { body, loc: at })
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
                Ok(Stmt::Print { exprs, loc: at })
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
                Ok(Stmt::Return { value, loc: at })
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
                // parse_stmt call, stamped `at` like every 1:1 sugar
                // (H5).
                self.tokens.next();
                let name = self.parse_fn_stmt_name()?;
                let expr = self.parse_fn_literal()?;
                Ok(Stmt::Assignment {
                    name,
                    expr,
                    loc: at,
                })
            }
            Some(Token::Identifier(_)) => {
                let lhs = self.parse_expr()?;
                if matches!(self.tokens.peek(), Some(Token::Comma)) {
                    // a comma after a leading target expr can only be
                    // the multi-target tuple sugar — plain statements
                    // never continue with a comma
                    return self.parse_tuple_assign(at, lhs);
                }
                if matches!(self.tokens.peek(), Some(Token::Assign)) {
                    self.tokens.next();
                    let rhs = self.parse_expr()?;
                    match lhs {
                        Expr::Identifier(name) => Ok(Stmt::Assignment {
                            name,
                            expr: rhs,
                            loc: at,
                        }),
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
                                loc: at,
                            })
                        }
                        Expr::Index { obj, key } => Ok(Stmt::IndexAssign {
                            obj: *obj,
                            key: *key,
                            value: rhs,
                            loc: at,
                        }),
                        _ => Err(ParseError(Diagnostic::syntax("Invalid assignment target"))),
                    }
                } else if matches!(lhs, Expr::Call { .. }) {
                    Ok(Stmt::Expr { expr: lhs, loc: at })
                } else if let Expr::Identifier(name) = &lhs {
                    if name == "continue" {
                        // C3's named rejection: 'continue' parses as a
                        // bare NAME, so the generic statement error used
                        // to answer it. The dialect's loop verbs are
                        // 'break' and the loop condition — name the word
                        // (the for-step diagnostic's style).
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

    /// Multi-target tuple assignment (RESIDUALS row 3, ruled parallel
    /// 2026-10-28, probe-first — the sequential face silently
    /// miscomputes the swap idiom): `t[k], t[k], … = v, v, …`.
    /// Targets are CELLS — bracket or dot; a bare name among them is
    /// a named refusal (the multi-name surface is `local`, the
    /// rebinding surface is plain `=`). Counts must match, the
    /// local-decl discipline. The shape is the pure elaborator's
    /// (elaborate.rs); this half only parses, validates, and hands
    /// over the pieces.
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
        let mut cells = Vec::with_capacity(targets.len());
        for target in targets {
            match target {
                Expr::Index { obj, key } => cells.push((*obj, *key)),
                Expr::Field { obj, name } => {
                    // dot targets convert to the string-keyed store
                    // here, the single-assign path's twin (the trace
                    // signal fires at the parse site; the elaborator
                    // stays pure)
                    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_STRKEY_DOT);
                    cells.push((*obj, Expr::String(name)));
                }
                Expr::Identifier(name) => {
                    return Err(ParseError(Diagnostic::syntax(format!(
                        "cannot tuple-assign the name '{name}' — tuple assignment \
                         targets cells ('t[k]' or 't.k'); names rebind through plain '=' or \
                         'local'"
                    ))));
                }
                _ => {
                    return Err(ParseError(Diagnostic::syntax(
                        "tuple assignment targets cells — 't[k]' or 't.k'",
                    )));
                }
            }
        }
        Ok(crate::elaborate::desugar_tuple_assign(at, cells, values))
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

    /// Unlike has_break, assignments to the loop variable are rejected even
    /// from nested While bodies (they still mutate the outer loop var), and a
    /// LocalDecl of the same name shadows it for the rest of its block.
    /// Pinned by for_var_nested_while_rejected.
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
        // The elseif's nested If is stamped at its own leading token.
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
                            return Err(ParseError(Diagnostic::syntax(
                                "expected a name after '.'",
                            )));
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
                            return Err(ParseError(Diagnostic::syntax(
                                "require takes one string literal — \
                                 require(\"ffi\") and require(\"coroutine\") are the \
                                 modules the dialect provides",
                            )));
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
                            return Err(ParseError(Diagnostic::syntax(format!(
                                "require(\"{other}\") — the dialect provides \
                                 only require(\"ffi\") (the mocked LuaJIT ffi surface) and \
                                 require(\"coroutine\") (the OS-thread parody of Lua's \
                                 cooperative coroutines)"
                            ))));
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
            _ => Err(ParseError(Diagnostic::syntax("Expected expression"))),
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
        Ok(Expr::Function { params, body })
    }

    fn parse_table_ctor(&mut self) -> Result<Expr, ParseError> {
        // The ctor's birth line: the `{` is the last consumed token, so
        // last_off IS the `{` — captured once at entry and stamped on
        // the node (H5: attribution rides the node; there is no
        // parallel push to keep in step).
        let line = self.line_of(self.tokens.last_off);
        if matches!(self.tokens.peek(), Some(Token::RightBrace)) {
            self.tokens.next();
            alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_TBL_EMPTY);
            return Ok(Expr::TableCtor {
                entries: Vec::new(),
                line: line as u32,
            });
        }

        let mut entries: Vec<(CtorKey, Expr)> = Vec::new();
        let mut slots: BTreeSet<i64> = BTreeSet::new();
        // Record field identity: a named key and a literal-string expr key
        // name the same field, so both dedupe through one set. (A dynamic
        // expr key's type is the checker's call — see its TableCtor arm.)
        // Pinned by ctor_dup_key_spellings_rejected.
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
                        return Err(ParseError(Diagnostic::syntax(format!(
                            "duplicate index {slot} in constructor — each slot may \
                             be written once (last-wins is not alm's rule)"
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
        alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_PARSE_TBL_CTOR);
        Ok(Expr::TableCtor {
            entries,
            line: line as u32,
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
                Expr::Integer(k) => {
                    if k >= BOUNDS_FAIL_THRESHOLD {
                        return Err(ParseError(Diagnostic::bounds("table index overflow")));
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
                            return Err(ParseError(Diagnostic::syntax(
                                "expected identifier before '='",
                            )));
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
