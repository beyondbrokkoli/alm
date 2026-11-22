use super::super::constraints::UnknownStore;
use super::Checker;
use super::type_helpers::type_name;
use crate::ast::{Expr, NodeId};
use crate::diag::Diagnostic;
use crate::shape::ty::Ty;
use crate::shape::{is_ghost, is_root};
use std::collections::BTreeMap;

impl Checker {
    pub(super) fn check_condition(
        &mut self,
        lat: &mut UnknownStore,
        condition: &Expr,
        kw: &str,
    ) -> Result<(), Diagnostic> {
        let ty = self.check_expr(lat, condition)?;
        let ty = self.pin_bool(lat, &ty)?;
        if ty != Ty::Bool {
            let note = self.any_provenance_note(lat, &ty, condition);
            return Err(Diagnostic::ty(format!(
                "'{}' condition must be a Boolean, got {}{}",
                kw,
                type_name(&ty),
                note.unwrap_or_default()
            )));
        }
        Ok(())
    }

    pub(super) fn create_closure(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        name: &str,
        ptr: NodeId,
    ) -> Result<Ty, Diagnostic> {
        if self.inline_stack.contains(&ptr) {
            return Err(Diagnostic::ty(format!(
                "'{name}' cannot escape its own expansion — \
                 a closure cannot capture itself"
            )));
        }
        if self.cond_depth > 0 {
            return Err(Diagnostic::ty(format!(
                "'{name}' cannot be created inside a conditional arm \
                 or loop body — creations are straight-line (V1)"
            )));
        }
        let caps = self.ctx.fn_captures.get(&ptr).cloned().unwrap_or_default();
        // The face resolution reads each capture at its RECORDED DEPTH
        // (var_type_at_depth) — the boundary-root binding is the same
        // object from every site, and a creation-site same-name shadow
        // must never lend its type to the face the way an innermost
        // read would (v2's mint-inside-shadow, Bug 4's Str shadow
        // false-reject). Deeper captures resolve positionally on the
        // definer's continuation — the same standing invariant the
        // mint's read_var_at trusts — so the face's type and the
        // lowerer's cell store read the SAME binding by construction.
        // The loop keeps the first error verbatim.
        let depths = self.ctx.fn_capture_depths.get(&ptr).cloned();
        let mut face: BTreeMap<String, Ty> = BTreeMap::new();
        let mut face_err: Option<Diagnostic> = None;
        for cap in &caps {
            let resolved = match depths.as_ref().and_then(|m| m.get(cap)) {
                Some(&d) => self.var_type_at_depth(lat, cap, d),
                None => self.var_type(lat, cap),
            };
            match resolved {
                Ok(ty) => {
                    face.insert(cap.clone(), lat.resolve(&ty));
                }
                Err(err) => {
                    face_err = Some(err);
                    break;
                }
            }
        }
        if let Some(err) = face_err {
            return Err(err);
        }
        match self.env_faces.get(&ptr) {
            None => {
                // The face's binding depths ride beside it: captures
                // are fixed body text, so the first creation site
                // stamps what every site must agree on. The lowerer
                // keys env sharing and cell stores on these — same
                // name, different depth means two bindings, two envs
                // (Closure Finding A).
                self.env_face_depths.insert(
                    ptr,
                    self.ctx
                        .fn_capture_depths
                        .get(&ptr)
                        .cloned()
                        .unwrap_or_default(),
                );
                self.env_faces.insert(ptr, face);
            }
            Some(prev) => {
                for (n, t) in &face {
                    match prev.get(n) {
                        Some(p) => {
                            lat.unify(p, t)?;
                        }
                        None => {
                            panic!(
                                "'{name}' has no capture '{n}' at an earlier \
                                 creation site — captures are fixed body \
                                 text: one body, one face set, and \
                                 env_faces is inserted before any \
                                 Ty::Closure escapes",
                            );
                        }
                    }
                }
            }
        }
        // The mint no longer arms a box-identity seam: the lowerer's
        // write-through discipline keeps every minted cell in sync with
        // the definer's binding, so a creation is not a storage fork —
        // it is the view the judge sees (one variable, shared by
        // reference).
        self.shadow_pair().creation_envs.insert(expr.id(), ptr);
        Ok(Ty::Closure(ptr))
    }

    pub(super) fn reject_face_extraction(expr: &Expr, ty: &Ty) -> Result<(), Diagnostic> {
        if matches!(expr, Expr::Field { .. }) && matches!(ty, Ty::Closure(_)) {
            return Err(Diagnostic::ty(
                "the face rides the field — a closure field cannot be \
                 extracted into a name; call it through the record",
            ));
        }
        Ok(())
    }

    pub(super) fn closure_field_fn(&self, obj: &Expr, field: &str) -> Option<NodeId> {
        let Expr::Identifier { name: n, .. } = obj else {
            return None;
        };
        let bind = self.snap.binds.get(n)?;
        // A severed binding (the creation-capture law moved a captured
        // table into its env — reachable for depth-0 tables too since
        // the Finding B fix lets top-level bindings be captured) keeps
        // its site identity in the severed map, not in aliases. The
        // field resolution reads both faces.
        let mut sites: Vec<usize> = bind.aliases.iter().copied().collect();
        if let Some(severed) = self.snap.severed.get(n) {
            sites.extend(severed.iter().copied());
        }
        for s in sites.iter() {
            if !is_root(s)
                && !is_ghost(s)
                && let Some(ptr) = self.closure_fields.get(&(*s, field.to_string()))
            {
                return Some(*ptr);
            }
        }
        None
    }

    pub(super) fn carries_closure(&self, expr: &Expr) -> bool {
        if let Expr::Identifier { name: n, .. } = expr
            && let Some(bind) = self.snap.binds.get(n)
        {
            let mut sites: Vec<usize> = bind.aliases.iter().copied().collect();
            if let Some(severed) = self.snap.severed.get(n) {
                sites.extend(severed.iter().copied());
            }
            return sites.iter().any(|s| {
                !is_root(s) && !is_ghost(s) && self.closure_fields.keys().any(|(site, _)| site == s)
            });
        }
        false
    }
}
