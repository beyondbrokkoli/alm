use super::super::constraints::UnknownStore;
use super::type_helpers::{body_has_valued_return, type_name};
use super::{Checker, ReturnCtx};
use crate::ast::{Expr, NodeId};
use crate::diag::Diagnostic;
use crate::shape::facts::{InstanceId, InstanceInfo};
use crate::shape::ty::Ty;
use std::collections::{BTreeMap, BTreeSet};

impl Checker {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand_call(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        callee: &Expr,
        name: &str,
        fn_ptr: NodeId,
        call_through: bool,
        args: &[Expr],
    ) -> Result<Ty, Diagnostic> {
        if self.inline_stack.contains(&fn_ptr) {
            return Err(Diagnostic::ty(format!(
                "'{name}' is recursive — inline closures expand at \
                 their call sites, so a call chain may not reach back into itself"
            )));
        }
        // Direct-call capture visibility. A depth-0 capture always
        // passes: the boundary-root scope sits at the base of every
        // stack this checker and the lowerer ever hold, so the capture
        // is present at ANY call site (the Finding B lexical fix — the
        // expansion declares the capture as a view of the root below).
        // A deeper capture must resolve in the caller's context: the
        // direct surface has no env, so the expansion would read the
        // caller's same-named binding, which is the captured binding
        // only inside the definer's lexical continuation.
        if !call_through
            && let Some(caps) = self.ctx.fn_captures.get(&fn_ptr)
            && !caps.is_empty()
        {
            let depths = self.ctx.fn_capture_depths.get(&fn_ptr);
            for cap in caps {
                if depths.is_some_and(|m| m.get(cap) == Some(&0)) {
                    continue;
                }
                if self.frames_resolve(cap).is_none()
                    && self.active_env_override(cap).is_none()
                    && self.active_env_face(cap).is_none()
                {
                    return Err(Diagnostic::ty(format!(
                        "'{name}' is a closure — call it through its value"
                    )));
                }
            }
        }
        let def = self.fn_defs.get(&fn_ptr).cloned().expect(
            "'{name}' holds no function body — fn_defs feeds every \
             resolver; the checker records every accepted fn's literal",
        );
        if args.len() != def.params.len() {
            return Err(Diagnostic::ty(format!(
                "'{name}' takes {} argument(s), got {}",
                def.params.len(),
                args.len()
            )));
        }
        let mut arg_tys = Vec::with_capacity(args.len());
        let stmt_position = std::mem::take(&mut self.stmt_position_call);
        for a in args {
            arg_tys.push(self.check_expr(lat, a)?);
        }

        match &def.signature {
            None => {
                if let Some(d) = self.fn_defs.get_mut(&fn_ptr) {
                    d.signature = Some(arg_tys.clone());
                }
            }
            Some(fixed) => {
                for (i, (f, a)) in fixed.iter().zip(arg_tys.iter()).enumerate() {
                    let both_closures = matches!(lat.resolve(f), Ty::Closure(_))
                        && matches!(lat.resolve(a), Ty::Closure(_));
                    if both_closures || lat.unify(f, a).is_ok() {
                        continue;
                    }
                    let want = type_name(&lat.resolve(f));
                    let got = type_name(&lat.resolve(a));
                    return Err(Diagnostic::ty(format!(
                        "argument {} of '{name}' is {got} where \
                                 the first call fixed {want} — calls are monomorphic",
                        i + 1
                    )));
                }
            }
        }

        let body = def.body();

        if !stmt_position && !body_has_valued_return(body) {
            return Err(Diagnostic::ty(format!(
                "'{name}' is an expansion with no return — \
                 it produces no value"
            )));
        }

        let call_ptr = expr.id();

        let env_face = if call_through {
            match self.env_faces.get(&fn_ptr) {
                Some(face) => face
                    .iter()
                    .map(|(n, t)| (n.clone(), lat.resolve(t)))
                    .collect(),
                None => {
                    panic!(
                        "'{name}' dispatches with no recorded env — program \
                         order guarantees the creation precedes the \
                         dispatch (env_faces is stamped at creation)",
                    );
                }
            }
        } else {
            BTreeMap::new()
        };

        self.inline_stack.push(fn_ptr);
        self.expansion_frame_bases.push(self.frames.len());
        self.expansion_params.push(def.params.clone());
        let instance = self.mint_instance();
        let break_base = self.expansion_break_bases.last().copied().unwrap_or(0) + self.loop_depth;
        self.expansion_break_bases.push(break_base);
        self.instances.insert(
            instance,
            InstanceInfo {
                call: Some(call_ptr),
                fn_node: Some(fn_ptr),
                params: def.params.clone(),
                body: body.to_vec(),
                frame_base: self.frames.len(),
                break_base,
                env_face: if call_through {
                    Some(env_face.clone())
                } else {
                    None
                },
                ret: None,
                children: BTreeMap::new(),
                creation_envs: BTreeMap::new(),
                closure_calls: BTreeSet::new(),
                index_key_lanes: BTreeMap::new(),
                access_elems: BTreeMap::new(),
            },
        );
        self.instance_stack.push(instance);
        self.expansion_envs
            .push(if call_through { Some(env_face) } else { None });
        self.env_overrides.push(BTreeMap::new());
        self.begin_scope();
        for (p, aty) in def.params.iter().zip(arg_tys) {
            let pty = lat.fresh();
            self.declare_var(lat, p.clone(), pty.clone())?;
            lat.unify(&pty, &aty)?;
        }
        // The direct surface's captures become CAPTURE VIEWS in the
        // expansion frame — for ALL depths now (the d == 0 filter
        // retires): declared at their recorded walk depth
        // (var_type_at_depth — the mint's face types ride the env on
        // the through-value surface instead), they shadow every
        // caller frame's same-named binding for the body's reads,
        // mirroring the lowerer's capture views. A param wins (fresh
        // storage — judge semantics), and any capture the body
        // declares over shadows naturally. A capture whose binding
        // this stack did not reconstruct (no entry at its recorded
        // depth) keeps the dynamic innermost reads — the definer's
        // continuation is not on this surface. The entry dies with
        // its frame; the monomorphic law keeps the owner's type
        // identical, so no fold-back is owed.
        if !call_through && let Some(depths) = self.ctx.fn_capture_depths.get(&fn_ptr).cloned() {
            for (n, &d) in &depths {
                if def.params.contains(n) {
                    continue;
                }
                let ty = match self.var_type_at_depth(lat, n, d) {
                    Ok(ty) => ty,
                    Err(_) => continue,
                };
                let frame = self.frames.last_mut().expect(
                    "begin_scope just pushed the expansion's frame — \
                     the capture declaration cannot outlive it",
                );
                frame.types.insert(n.clone(), ty);
                frame.captures.insert(n.clone());
            }
        }
        self.push_return_ctx(def.ret.clone());
        let saved_loop_depth = std::mem::replace(&mut self.loop_depth, 0);
        self.check_block(lat, body);
        self.loop_depth = saved_loop_depth;
        let ret = match self.return_ctxs.pop() {
            Some(ReturnCtx::Internal(ty)) => lat.resolve(&ty),
            _ => unreachable!("push_return_ctx just pushed an Internal context"),
        };
        self.end_scope();
        self.inline_stack.pop();
        self.expansion_frame_bases.pop();
        self.expansion_params.pop();
        self.instance_stack.pop();
        self.expansion_break_bases.pop();
        self.expansion_envs.pop();
        self.env_overrides.pop();

        self.call_fns.entry(call_ptr).or_default().insert(fn_ptr);
        let owner = self
            .instance_stack
            .first()
            .copied()
            .unwrap_or(InstanceId::ROOT);
        if let Some(owner_rec) = self.instances.get_mut(&owner) {
            owner_rec
                .children
                .entry(call_ptr)
                .or_default()
                .insert(instance);
        }
        if let Some(rec) = self.instances.get_mut(&instance) {
            rec.ret = Some(ret.clone());
        }
        let _ = callee;
        Ok(ret)
    }
}
