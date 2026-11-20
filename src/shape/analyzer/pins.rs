use super::*;

#[derive(Clone)]
enum ScalarView {
    Unknown(usize),
    Scalar(Ty),
    Other,
}

impl Analyzer {
    fn node_view(&self, expr: &Expr) -> Option<usize> {
        match expr {
            Expr::Identifier { name, .. } => self.name_node(name),
            Expr::Index { obj, .. } | Expr::Field { obj, .. } => match obj.as_ref() {
                Expr::Identifier { .. } => self.read_elem_node(obj),
                Expr::Call { .. } => self.call_read_node(obj),
                // C: a read through any other base has no single node
                _ => None,
            },
            Expr::Call { .. } => self.call_value_node(expr),
            // C: literals, operators, ctors, and the module faces have no
            // lattice node to view
            Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::TableCtor { .. }
            | Expr::BinaryOp { .. }
            | Expr::UnaryOp { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. }
            | Expr::Function { .. } => None,
        }
    }

    fn name_node(&self, name: &str) -> Option<usize> {
        self.walk.scalar_node(name)
    }

    fn single_pending_head(&self, sites: impl Iterator<Item = usize>) -> Option<usize> {
        let mut heads: BTreeSet<usize> = BTreeSet::new();
        for s in sites {
            if self.lattice.site_elem[s] != Pending {
                return None;
            }
            match self.lattice.unknowns.resolve(&Ty::Unknown(s)) {
                Ty::Unknown(head) => {
                    heads.insert(head);
                }
                _ => return None,
            }
        }
        match heads.len() {
            1 => heads.iter().next().copied(),
            _ => None,
        }
    }

    fn read_elem_node(&self, base: &Expr) -> Option<usize> {
        let Expr::Identifier { name, .. } = base else {
            return None;
        };
        let Ok((_, bind)) = self.resolve(name) else {
            return None;
        };
        if bind.aliases.contains(&NULL_ROOT) || bind.aliases.contains(&MOVED_ROOT) {
            return None;
        }
        if bind.aliases.contains(&BOUNDARY_ROOT) {
            return Some(self.lattice.unknowns.boundary_seed());
        }
        if !matches!(bind.ty, Tbl(_)) {
            return None;
        }
        let real = bind
            .aliases
            .iter()
            .copied()
            .filter(|s| !is_root(s) && !is_ghost(s));
        self.single_pending_head(real)
    }

    fn call_value_node(&self, expr: &Expr) -> Option<usize> {
        let (fn_ptr, shape) = self.call_shape(expr)?;
        if matches!(shape.ty, Pending) {
            self.lattice.unknowns.fn_ret_node(fn_ptr)
        } else {
            None
        }
    }

    fn call_read_node(&self, call: &Expr) -> Option<usize> {
        let (_, shape) = self.call_shape(call)?;
        match &shape.ty {
            Tbl(inner) if matches!(**inner, Pending) => {
                let real = shape
                    .aliases
                    .iter()
                    .copied()
                    .filter(|s| !is_root(s) && !is_ghost(s));
                self.single_pending_head(real)
            }
            _ => None,
        }
    }

    fn call_shape(&self, expr: &Expr) -> Option<(NodeId, &TableShape)> {
        let Expr::Call { callee, .. } = expr else {
            return None;
        };
        let Expr::Identifier { name, .. } = callee.as_ref() else {
            return None;
        };
        let fn_ptr = self.resolve_fn(name)?;
        let shape = self.fn_ret_shapes.get(&fn_ptr)?;
        Some((fn_ptr, shape))
    }

    fn scalar_view(&self, expr: &Expr, walk_ty: &Ty) -> ScalarView {
        if let Some(node) = self.node_view(expr) {
            return match self.lattice.unknowns.resolve(&Ty::Unknown(node)) {
                Ty::Unknown(head) => ScalarView::Unknown(head),
                t if pinned_scalar(&t) => ScalarView::Scalar(t),
                _ => ScalarView::Other,
            };
        }
        match walk_ty {
            t if pinned_scalar(t) => ScalarView::Scalar(t.clone()),
            _ => ScalarView::Other,
        }
    }

    fn pins_armed(&self, rec: Gate) -> bool {
        rec.on() && self.walk_pins && self.fn_walk.is_empty()
    }

    pub(super) fn computed_arith_scalar(
        &mut self,
        rec: Gate,
        l: &Expr,
        lt: &Ty,
        r: &Expr,
        rt: &Ty,
    ) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        let num = |e: &Expr, t: &Ty| match self.scalar_view(e, t) {
            ScalarView::Scalar(k) if matches!(k, Int | Flt) => Some(k),
            _ => None,
        };
        match (num(l, lt), num(r, rt)) {
            (Some(a), Some(b)) if a == b => {
                self.pin_derived_exprs.insert(l.id());
                self.pin_derived_exprs.insert(r.id());
                Some(a)
            }
            _ => None,
        }
    }

    pub(super) fn computed_div_scalar(
        &mut self,
        rec: Gate,
        l: &Expr,
        lt: &Ty,
        r: &Expr,
        rt: &Ty,
    ) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        let num = |e: &Expr, t: &Ty| matches!(self.scalar_view(e, t), ScalarView::Scalar(k) if matches!(k, Int | Flt));
        if num(l, lt) && num(r, rt) {
            self.pin_derived_exprs.insert(l.id());
            self.pin_derived_exprs.insert(r.id());
            Some(Flt)
        } else {
            None
        }
    }

    pub(super) fn computed_neg_scalar(&mut self, rec: Gate, e: &Expr, t: &Ty) -> Option<Ty> {
        if !self.pins_armed(rec) {
            return None;
        }
        match self.scalar_view(e, t) {
            ScalarView::Scalar(k) if matches!(k, Int | Flt) => {
                self.pin_derived_exprs.insert(e.id());
                Some(k)
            }
            _ => None,
        }
    }

    pub(super) fn rhs_pin_derived(&self, expr: &Expr) -> bool {
        if self.pin_derived_exprs.contains(&expr.id()) {
            return true;
        }
        match expr {
            Expr::Identifier { name, .. } => self.pin_justified_names.contains(name),
            Expr::BinaryOp { left, right, .. } => {
                self.rhs_pin_derived(left) || self.rhs_pin_derived(right)
            }
            Expr::UnaryOp { expr, .. } => self.rhs_pin_derived(expr),
            Expr::Index { obj, key, .. } => self.rhs_pin_derived(obj) || self.rhs_pin_derived(key),
            Expr::Field { obj, .. } => self.rhs_pin_derived(obj),
            Expr::Call { callee, args, .. } => {
                self.rhs_pin_derived(callee) || args.iter().any(|a| self.rhs_pin_derived(a))
            }
            Expr::TableCtor { entries, .. } => entries.iter().any(|(_, e)| self.rhs_pin_derived(e)),
            // C: leaves and module faces derive from no pin
            Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. }
            | Expr::Function { .. } => false,
        }
    }

    pub(super) fn pin_bool_use(&mut self, rec: Gate, expr: &Expr, walk_ty: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        if let ScalarView::Unknown(head) = self.scalar_view(expr, walk_ty) {
            let _ = self.lattice.unknowns.bind(head, Bool);
        }
    }

    pub(super) fn pin_int_use(&mut self, rec: Gate, expr: &Expr, walk_ty: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        if let ScalarView::Unknown(head) = self.scalar_view(expr, walk_ty) {
            let _ = self.lattice.unknowns.bind(head, Int);
        }
    }

    pub(super) fn pin_numeric_pair(&mut self, rec: Gate, l: &Expr, lt: &Ty, r: &Expr, rt: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        let lv = self.scalar_view(l, lt);
        let rv = self.scalar_view(r, rt);
        let num = |v: &ScalarView| matches!(v, ScalarView::Scalar(t) if matches!(*t, Int | Flt));
        match (&lv, &rv) {
            (a, b) if num(a) && num(b) => {}
            (ScalarView::Scalar(t), ScalarView::Unknown(head)) if num(&lv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(head), ScalarView::Scalar(t)) if num(&rv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(a), ScalarView::Unknown(b)) => {
                let _ = self.lattice.unknowns.bind(*a, Int);
                let _ = self.lattice.unknowns.bind(*b, Int);
            }
            _ => {}
        }
    }

    pub(super) fn pin_scalar_pair(&mut self, rec: Gate, l: &Expr, lt: &Ty, r: &Expr, rt: &Ty) {
        if !self.pins_armed(rec) {
            return;
        }
        let lv = self.scalar_view(l, lt);
        let rv = self.scalar_view(r, rt);
        let scalar = |v: &ScalarView| matches!(v, ScalarView::Scalar(t) if pinned_scalar(t));
        match (&lv, &rv) {
            (ScalarView::Scalar(t), ScalarView::Unknown(head)) if scalar(&lv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            (ScalarView::Unknown(head), ScalarView::Scalar(t)) if scalar(&rv) => {
                let _ = self.lattice.unknowns.bind(*head, t.clone());
            }
            _ => {}
        }
    }

    pub(super) fn note_decl_scalar_node(&mut self, name: &str, rhs: &Expr) {
        let entry = self.node_view(rhs);
        // The decl's pre-bind sits innermost — the node face lands on
        // the binding it belongs to (today: an innermost rider write).
        if let Some((_, bind)) = self.walk.binding_at_mut(name) {
            bind.scalar_node = entry;
        }
    }

    pub(super) fn note_assign_scalar_node(&mut self, name: &str, rhs: &Expr) {
        let entry = self.node_view(rhs);
        // A scalar node rides its name's binding depth: binding_at_mut
        // IS the home scan (today: an rposition over the master scopes
        // with an innermost fallback — the T2 ghost's second
        // birthplace). A name bound nowhere finds no binding and no
        // face is written, exactly as the old fallback's rider entry
        // lived only to die with the undeclared rejection.
        if let Some((_, bind)) = self.walk.binding_at_mut(name) {
            bind.scalar_node = entry;
        }
    }
}
