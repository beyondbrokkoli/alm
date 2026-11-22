use super::super::constraints::UnknownStore;
use super::type_helpers::type_name;
use super::{CdefRow, Checker, ScalarElem};
use crate::ast::{Expr, UnOp};
use crate::diag::Diagnostic;
use crate::shape::facts::{FfiMint, FfiVerb};
use crate::shape::ty::Ty;

/// Parse one cdef declaration string into registry rows. The grammar
/// for this milestone is the scalar tier: `type name;`, `type
/// name[N];`, plus struct/union/typedef declarations that register a
/// name only (elem = None — `ffi.new` over them rejects by name).
/// Returns `(name, row)` pairs; `Err(text)` names the first fragment
/// that could not be parsed.
fn parse_cdef(text: &str) -> Result<Vec<(String, CdefRow)>, String> {
    let mut rows = Vec::new();
    for frag in split_decls(text) {
        let frag = frag.trim();
        if frag.is_empty() {
            continue;
        }
        // A struct/union declaration registers its tag only; the body
        // is later milestones' business (elem = None rejects ffi.new).
        if let Some(rest) = frag.strip_prefix("struct ") {
            let name = rest.split_whitespace().next().unwrap_or("").trim();
            if name.is_empty() {
                return Err(frag.to_string());
            }
            rows.push((
                name.to_string(),
                CdefRow {
                    elem: None,
                    capacity: None,
                },
            ));
            continue;
        }
        if let Some(rest) = frag.strip_prefix("union ") {
            let name = rest.split_whitespace().next().unwrap_or("").trim();
            if name.is_empty() {
                return Err(frag.to_string());
            }
            rows.push((
                name.to_string(),
                CdefRow {
                    elem: None,
                    capacity: None,
                },
            ));
            continue;
        }
        // A function declaration registers its name only — the drive
        // seam is the cdef'd-function lane's consumer; `ffi.new` over
        // it rejects by name like any non-scalar row.
        if frag.contains('(') {
            let head = frag.split('(').next().unwrap_or("").trim();
            let name = head
                .split_whitespace()
                .next_back()
                .unwrap_or("")
                .trim_matches('*');
            if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err(frag.to_string());
            }
            rows.push((
                name.to_string(),
                CdefRow {
                    elem: None,
                    capacity: None,
                },
            ));
            continue;
        }
        if frag.starts_with("typedef ") {
            // `typedef <something> name;` — the declared name is the
            // last token; the base type may be scalar or aggregate.
            let toks: Vec<&str> = frag.split_whitespace().collect();
            if toks.len() < 3 {
                return Err(frag.to_string());
            }
            let name = toks[toks.len() - 1];
            let elem = scalar_elem_of(&toks[1..toks.len() - 1]);
            rows.push((
                name.to_string(),
                CdefRow {
                    elem,
                    capacity: None,
                },
            ));
            continue;
        }
        // Scalar declaration: `type name` or `type name[N]` (the
        // `double[100]` array spelling rides the same bracket).
        let (head, bracket) = match frag.find('[') {
            Some(i) => (&frag[..i], Some(&frag[i..])),
            None => (frag, None),
        };
        let toks: Vec<&str> = head.split_whitespace().collect();
        if toks.len() != 2 {
            // The anonymous array spelling `double[100];` registers
            // under its own full text — `ffi.new("double[100]")` names
            // it back verbatim.
            if toks.len() == 1 && bracket.is_some() {
                let elem = scalar_elem_of(&toks[..1]).ok_or_else(|| frag.to_string())?;
                let n = bracket_capacity(bracket).ok_or_else(|| frag.to_string())?;
                rows.push((
                    frag.to_string(),
                    CdefRow {
                        elem: Some(elem),
                        capacity: Some(n),
                    },
                ));
                continue;
            }
            return Err(frag.to_string());
        }
        let Some(elem) = scalar_elem_of(&toks[..1]) else {
            return Err(frag.to_string());
        };
        let name = toks[1];
        let capacity = match bracket {
            None => None,
            Some(b) => Some(bracket_capacity(Some(b)).ok_or_else(|| frag.to_string())?),
        };
        rows.push((
            name.to_string(),
            CdefRow {
                elem: Some(elem),
                capacity,
            },
        ));
    }
    Ok(rows)
}

/// The declared capacity inside a `[N]` bracket — positive, literal.
fn bracket_capacity(bracket: Option<&str>) -> Option<i64> {
    let inner = bracket?.strip_prefix('[')?.strip_suffix(']')?;
    let n: i64 = inner.trim().parse().ok()?;
    (n > 0).then_some(n)
}

/// Split a cdef string on top-level ';' only — braces nest (struct
/// and union bodies carry their own ';' separators, which belong to
/// the body, not the declaration list).
fn split_decls(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut cur = String::new();
    for ch in text.chars() {
        match ch {
            '{' => {
                depth += 1;
                cur.push(ch);
            }
            '}' => {
                depth = depth.saturating_sub(1);
                cur.push(ch);
            }
            ';' if depth == 0 => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur);
    }
    out.into_iter().map(|f| f.trim().to_string()).collect()
}

/// Map a C scalar spelling onto the cdef grammar's scalar tier. The
/// token list allows multi-word spellings (`unsigned long long`).
fn scalar_elem_of(toks: &[&str]) -> Option<ScalarElem> {
    match toks {
        ["char"]
        | ["short"]
        | ["int"]
        | ["long"]
        | ["unsigned"]
        | ["unsigned", "char"]
        | ["unsigned", "short"]
        | ["unsigned", "int"]
        | ["unsigned", "long"]
        | ["long", "long"]
        | ["unsigned", "long", "long"]
        | ["signed"]
        | ["size_t"]
        | ["int8_t"]
        | ["int16_t"]
        | ["int32_t"]
        | ["int64_t"]
        | ["uint8_t"]
        | ["uint16_t"]
        | ["uint32_t"]
        | ["uint64_t"] => Some(ScalarElem::Int),
        ["float"] | ["double"] => Some(ScalarElem::Flt),
        ["bool"] | ["_Bool"] => Some(ScalarElem::Bool),
        _ => None,
    }
}

impl Checker {
    pub(super) fn check_ffi_call(
        &mut self,
        lat: &mut UnknownStore,
        call: &Expr,
        obj: &Expr,
        name: &str,
        args: &[Expr],
    ) -> Result<Ty, Diagnostic> {
        let base = match obj {
            Expr::Identifier { name: n, .. } => n.clone(),
            _ => {
                return Err(Diagnostic::ty(
                    "the ffi surface's '.' base must be a name — a bound \
                     module or library handle",
                ));
            }
        };
        let raw = self.check_expr(lat, obj)?;
        let bt = lat.resolve(&raw);
        match bt {
            Ty::Ffi => match name {
                "load" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("ffi.load takes exactly one path"));
                    }
                    let t = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&t);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Str)?;
                        Ty::Str
                    } else {
                        t
                    };
                    match t {
                        Ty::Str => {
                            self.record_verb(call, FfiVerb::Load);
                            Ok(Ty::FfiLib)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "ffi.load's path is a String, got {}",
                            type_name(&other)
                        ))),
                    }
                }
                "cdef" => Err(Diagnostic::ty(
                    "ffi.cdef is a statement verb — call it on its own line; its \
                     nothing cannot bind",
                )),
                "new" => {
                    if args.is_empty() || args.len() > 2 {
                        return Err(Diagnostic::ty(
                            "ffi.new takes a declared name and an optional \
                             integer literal capacity",
                        ));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Str)?;
                        Ty::Str
                    } else {
                        t
                    };
                    let name = match (&args[0], &t) {
                        (Expr::String { value, .. }, Ty::Str) => value.clone(),
                        (_, Ty::Str) => {
                            return Err(Diagnostic::ty(
                                "ffi.new names its declaration by a string \
                                 literal — the name is a compile-time fact",
                            ));
                        }
                        (_, other) => {
                            return Err(Diagnostic::ty(format!(
                                "ffi.new's declaration name is a String, got {}",
                                type_name(other)
                            )));
                        }
                    };
                    let Some(row) = self.cdef_registry.get(&name).cloned() else {
                        return Err(Diagnostic::ty(format!(
                            "ffi.new: no declaration named '{name}' — ffi.cdef it first"
                        )));
                    };
                    let Some(elem) = row.elem else {
                        return Err(Diagnostic::ty(format!(
                            "ffi.new over '{name}': flat scalar arrays first — \
                             '{name}' is not a scalar kind"
                        )));
                    };
                    let capacity = if args.len() == 2 {
                        match &args[1] {
                            Expr::Integer { value: n, .. } if *n > 0 => *n,
                            Expr::Integer { value: n, .. } => {
                                return Err(Diagnostic::ty(format!(
                                    "ffi.new's capacity is a positive integer \
                                     literal, got {n}"
                                )));
                            }
                            Expr::UnaryOp {
                                op: UnOp::Neg,
                                expr: inner,
                                ..
                            } if matches!(inner.as_ref(), Expr::Integer { .. }) => {
                                return Err(Diagnostic::ty(
                                    "ffi.new's capacity is a positive integer \
                                     literal, got a negative literal",
                                ));
                            }
                            _ => {
                                return Err(Diagnostic::ty(
                                    "ffi.new's capacity is an integer literal, \
                                     got a non-literal expression",
                                ));
                            }
                        }
                    } else {
                        match row.capacity {
                            Some(n) => n,
                            None => {
                                return Err(Diagnostic::ty(format!(
                                    "ffi.new over '{name}': the declaration \
                                     carries no capacity — pass one: \
                                     ffi.new(\"{name}\", n)"
                                )));
                            }
                        }
                    };
                    self.record_verb(call, FfiVerb::New { name });
                    self.ffi_mints.insert(
                        call.id(),
                        FfiMint {
                            name: String::new(),
                            elem: elem.ty(),
                            capacity,
                        },
                    );
                    Ok(Ty::Tbl(Box::new(elem.ty())))
                }
                "sizeof" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("ffi.sizeof takes exactly one declared name"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Str)?;
                        Ty::Str
                    } else {
                        t
                    };
                    let name = match (&args[0], &t) {
                        (Expr::String { value, .. }, Ty::Str) => value.clone(),
                        (_, Ty::Str) => {
                            return Err(Diagnostic::ty(
                                "ffi.sizeof names its declaration by a string \
                                 literal — the name is a compile-time fact",
                            ));
                        }
                        (_, other) => {
                            return Err(Diagnostic::ty(format!(
                                "ffi.sizeof's declaration name is a String, got {}",
                                type_name(other)
                            )));
                        }
                    };
                    let Some(row) = self.cdef_registry.get(&name) else {
                        return Err(Diagnostic::ty(format!(
                            "ffi.sizeof: no declaration named '{name}' — ffi.cdef \
                             it first"
                        )));
                    };
                    let Some(elem) = row.elem else {
                        return Err(Diagnostic::ty(format!(
                            "ffi.sizeof over '{name}': flat scalar arrays first — \
                             '{name}' is not a scalar kind"
                        )));
                    };
                    // bytes_of is the one law: capacity when declared,
                    // the elem's esize otherwise.
                    let bytes = row.capacity.map_or(elem.esize(), |n| {
                        n.checked_mul(elem.esize()).unwrap_or(i64::MAX)
                    });
                    self.record_verb(call, FfiVerb::Sizeof { bytes });
                    Ok(Ty::Int)
                }
                "arg_kind" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("ffi.arg_kind takes exactly one library"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    match t {
                        Ty::FfiLib => {
                            self.record_verb(call, FfiVerb::ArgKind);
                            Ok(Ty::Int)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "ffi.arg_kind takes a library handle, got {}",
                            type_name(&other)
                        ))),
                    }
                }
                _ => Err(Diagnostic::ty(format!(
                    "unknown ffi member '{name}' — load, cdef, arg_kind, new, sizeof"
                ))),
            },
            Ty::Async => match name {
                "create" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("async.create takes exactly one library"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    match t {
                        Ty::FfiLib => {
                            self.record_verb(call, FfiVerb::AsyncCreate);
                            Ok(Ty::Int)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "async.create takes a library handle, got {}",
                            type_name(&other),
                        ))),
                    }
                }
                "resume" => {
                    if args.len() != 2 {
                        return Err(Diagnostic::ty(
                            "async.resume takes a async handle and one \
                             table — the spawn inputs (its first three cells ride the \
                             worker's boundary)",
                        ));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Int)?;
                        Ty::Int
                    } else {
                        t
                    };
                    match t {
                        Ty::Int => {}
                        other => {
                            return Err(Diagnostic::ty(format!(
                                "async.resume's first argument is a \
                                 async handle, got {}",
                                type_name(&other)
                            )));
                        }
                    }
                    let raw = self.check_expr(lat, &args[1])?;
                    let t = lat.resolve(&raw);
                    match t {
                        Ty::Tbl(_) => {
                            if self.carries_closure(&args[1]) {
                                return Err(Diagnostic::ty(
                                    "a closure cannot cross a module \
                                         boundary — the spawn table marshals flat cells only",
                                ));
                            }
                            self.record_verb(call, FfiVerb::AsyncResume);
                            Ok(Ty::Int)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "async.resume's second argument is the input \
                                 table, got {}",
                            type_name(&other),
                        ))),
                    }
                }
                "yield" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("async.yield takes exactly one integer"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Int)?;
                        Ty::Int
                    } else {
                        t
                    };
                    match t {
                        Ty::Int => {
                            self.record_verb(call, FfiVerb::AsyncYield);
                            Ok(Ty::Int)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "async.yield streams one integer, got {}",
                            type_name(&other),
                        ))),
                    }
                }
                "status" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("async.status takes exactly one async"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Int)?;
                        Ty::Int
                    } else {
                        t
                    };
                    match t {
                        Ty::Int => {
                            self.record_verb(call, FfiVerb::AsyncStatus);
                            Ok(Ty::Str)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "async.status takes a async handle, got {}",
                            type_name(&other),
                        ))),
                    }
                }
                "close" => {
                    if args.len() != 1 {
                        return Err(Diagnostic::ty("async.close takes exactly one async"));
                    }
                    let raw = self.check_expr(lat, &args[0])?;
                    let t = lat.resolve(&raw);
                    let t = if let Ty::Unknown(id) = t {
                        lat.bind(id, Ty::Int)?;
                        Ty::Int
                    } else {
                        t
                    };
                    match t {
                        Ty::Int => {
                            self.record_verb(call, FfiVerb::AsyncClose);
                            Ok(Ty::Int)
                        }
                        other => Err(Diagnostic::ty(format!(
                            "async.close takes a async handle, got {}",
                            type_name(&other),
                        ))),
                    }
                }
                _ => Err(Diagnostic::ty(format!(
                    "unknown async member '{name}' — create, resume, yield, \
                     status, close"
                ))),
            },
            Ty::FfiLib => Err(Diagnostic::ty(format!(
                "{base}.{name} is the drive verb — a statement on its own line; \
                 the module's result stays in the module's world, nothing comes back to bind"
            ))),
            _ => Err(Diagnostic::ty(format!(
                "'{base}' is not a module surface — '.' is the ffi/async \
                 surface's, tables use '[]'"
            ))),
        }
    }

    pub(super) fn check_ffi_verb(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
    ) -> Result<bool, Diagnostic> {
        let Expr::Call { callee, args, .. } = expr else {
            return Ok(false);
        };
        let Expr::Field { obj, name, .. } = callee.as_ref() else {
            return Ok(false);
        };
        let Expr::Identifier { name: base, .. } = obj.as_ref() else {
            return Ok(false);
        };
        let raw = self.check_expr(lat, obj)?;
        let bt = lat.resolve(&raw);
        match (&bt, name.as_str()) {
            (Ty::Ffi, "cdef") => {
                if args.len() != 1 {
                    return Err(Diagnostic::ty(
                        "ffi.cdef takes exactly one declaration string",
                    ));
                }
                let raw = self.check_expr(lat, &args[0])?;
                let t = lat.resolve(&raw);
                match (&args[0], &t) {
                    (Expr::String { value, .. }, Ty::Str) => {
                        // W4: the declaration string is load-bearing —
                        // parsed into registry rows at the choke point.
                        match parse_cdef(value) {
                            Ok(rows) => {
                                for (name, row) in rows {
                                    self.cdef_registry.insert(name, row);
                                }
                                self.record_verb(expr, FfiVerb::Cdef);
                                Ok(true)
                            }
                            Err(bad) => Err(Diagnostic::ty(format!(
                                "ffi.cdef cannot parse '{bad}': expected a \
                                 scalar, array, or struct/union declaration"
                            ))),
                        }
                    }
                    (_, Ty::Str) => Err(Diagnostic::ty(
                        "ffi.cdef's declaration is a compile-time string literal",
                    )),
                    (_, other) => Err(Diagnostic::ty(format!(
                        "ffi.cdef's declaration is a String, got {}",
                        type_name(other)
                    ))),
                }
            }
            (Ty::FfiLib, _) => {
                if args.len() != 1 {
                    return Err(Diagnostic::ty(format!(
                        "the drive call .{name} takes exactly one table — the \
                         boundary the module reads"
                    )));
                }
                let raw = self.check_expr(lat, &args[0])?;
                let t = lat.resolve(&raw);
                match t {
                    Ty::Tbl(_) => {
                        if self.carries_closure(&args[0]) {
                            return Err(Diagnostic::ty(
                                "a closure cannot cross a module boundary — \
                                 the drive table marshals flat cells only",
                            ));
                        }
                        self.record_verb(
                            expr,
                            FfiVerb::Drive {
                                base: base.clone(),
                                sym: name.clone(),
                            },
                        );
                        Ok(true)
                    }
                    other => Err(Diagnostic::ty(format!(
                        "the drive call .{name} takes one table, got {}",
                        type_name(&other)
                    ))),
                }
            }
            _ => Ok(false),
        }
    }
}
