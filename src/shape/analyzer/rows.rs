use super::*;
pub(super) fn deepfree_children(
    lattice: &LatticeState,
    own: &OwnershipState,
    reads: &ReadSideState,
    site: usize,
) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    let mut level = BTreeSet::from([site]);
    let mut seen = BTreeSet::new();
    while let Some(&s) = level.iter().next() {
        level.remove(&s);
        if !seen.insert(s) {
            continue;
        }
        let flagged = lattice.child_sites.contains_key(&s) || own.stored_ctor_parents.contains(&s);
        if !flagged {
            continue;
        }
        for src in [&lattice.child_sites, &reads.row_links] {
            if let Some(kids) = src.get(&s) {
                for &k in kids {
                    if !is_root(&k) && out.insert(k) {
                        level.insert(k);
                    }
                }
            }
        }
    }
    out
}

pub(super) fn origin_housed(
    scopes: &[BTreeMap<String, TableShape>],
    lattice: &LatticeState,
    own: &OwnershipState,
    reads: &ReadSideState,
    origin: usize,
    skip_depth: usize,
    skip_name: &str,
) -> bool {
    for (d, scope) in scopes.iter().enumerate() {
        for (n, ts) in scope {
            if d == skip_depth && n == skip_name {
                continue;
            }
            if ts.aliases.contains(&origin) {
                return true;
            }
            for &s in ts.aliases.iter().filter(|s| !is_root(s)) {
                if deepfree_children(lattice, own, reads, s).contains(&origin) {
                    return true;
                }
            }
        }
    }
    false
}

pub(super) fn release_set(
    lattice: &LatticeState,
    own: &OwnershipState,
    reads: &ReadSideState,
    node: usize,
) -> BTreeSet<usize> {
    let mut s = deepfree_children(lattice, own, reads, node);
    s.insert(node);
    s
}

pub(super) fn borrowers_of(
    scopes: &[BTreeMap<String, TableShape>],
    release: &BTreeSet<usize>,
    upto: usize,
    skip_depth: usize,
    skip_name: &str,
) -> Vec<String> {
    let mut out = Vec::new();
    for (d, scope) in scopes[..upto].iter().enumerate() {
        for (n, ts) in scope {
            if d == skip_depth && n == skip_name {
                continue;
            }
            if value_kind(&ts.ty) {
                continue;
            }
            if ts.lineage.keys().any(|o| release.contains(o)) {
                out.push(n.clone());
            }
        }
    }
    out
}

pub(super) fn ghost_origin_covered(
    lattice: &LatticeState,
    covered: &BTreeSet<usize>,
    origin: usize,
) -> bool {
    covered.contains(&origin)
        || lattice
            .ghost_mints
            .get(&origin)
            .is_some_and(|m| m.bases.iter().any(|b| covered.contains(b)))
}

pub(super) fn holds_reaches(holds: &HoldsState, from: usize, to: usize) -> bool {
    if from == to {
        return true;
    }
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![from];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        if let Some(next) = holds.hold_edges.get(&x) {
            for &y in next {
                if y == to {
                    return true;
                }
                stack.push(y);
            }
        }
    }
    false
}

impl Analyzer {
    pub(super) fn proj_node(&self, n: usize) -> Option<usize> {
        if is_ghost(&n) {
            self.lattice.ghost_site.get(&n).copied()
        } else if !is_root(&n) {
            Some(n)
        } else {
            None
        }
    }

    pub(super) fn ghost_base_closure(&self, g: usize, out: &mut BTreeSet<usize>) {
        if let Some(m) = self.lattice.ghost_mints.get(&g) {
            for &b in &m.bases {
                if out.insert(b) && is_ghost(&b) {
                    self.ghost_base_closure(b, out);
                }
            }
        }
    }

    pub(super) fn birth_closure(&self, site: usize) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let mut level = BTreeSet::from([site]);
        let mut seen = BTreeSet::new();
        while let Some(&s) = level.iter().next() {
            level.remove(&s);
            if !seen.insert(s) {
                continue;
            }
            if let Some(kids) = self.lattice.child_sites.get(&s) {
                for &k in kids {
                    if !is_root(&k) && out.insert(k) {
                        level.insert(k);
                    }
                }
            }
        }
        out
    }

    pub(super) fn row_links_closure(&self, site: usize) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let mut level = BTreeSet::from([site]);
        let mut seen = BTreeSet::new();
        while let Some(&s) = level.iter().next() {
            level.remove(&s);
            if !seen.insert(s) {
                continue;
            }
            if let Some(kids) = self.reads.row_links.get(&s) {
                for &k in kids {
                    if !is_root(&k) && out.insert(k) {
                        level.insert(k);
                    }
                }
            }
        }
        out
    }

    pub(super) fn node_release(&self, node: usize) -> BTreeSet<usize> {
        let mut s = release_set(&self.lattice, &self.own, &self.reads, node);
        if is_ghost(&node)
            && let Some(&b) = self.lattice.ghost_site.get(&node)
        {
            s.extend(release_set(&self.lattice, &self.own, &self.reads, b));
            s.insert(b);
        }
        s
    }

    pub(super) fn harm_set(&self, node: usize) -> BTreeSet<usize> {
        let mut s = release_set(&self.lattice, &self.own, &self.reads, node);
        let mut origins: BTreeSet<usize> = BTreeSet::new();
        for &g in &self.lattice.housed_ghosts {
            if let Some(&b) = self.lattice.ghost_site.get(&g)
                && s.contains(&b)
            {
                self.ghost_base_closure(g, &mut origins);
            }
        }
        s.extend(origins);
        s
    }

    pub(super) fn mark_claimed(&mut self, node: usize, keeps: &[super::facts::Keep]) {
        let (_, claim) = self.housed_in_release(node);
        if claim.is_empty() {
            return;
        }
        let mut spared: BTreeSet<usize> = BTreeSet::new();
        for k in keeps {
            match k {
                super::facts::Keep::Ghost(g) => {
                    if let Some(&b) = self.lattice.ghost_site.get(g) {
                        spared.insert(b);
                    }
                }
                super::facts::Keep::Name(n) => {
                    if let Ok((_, ts)) = self.resolve(None, n)
                        && let Some(&g) = ts.aliases.iter().find(|s| is_ghost(s))
                        && let Some(&b) = self.lattice.ghost_site.get(&g)
                    {
                        spared.insert(b);
                    }
                }
            }
        }
        for g in claim {
            if let Some(&b) = self.lattice.ghost_site.get(&g)
                && !spared.contains(&b)
            {
                self.lattice.claimed_ghosts.insert(g);
            }
        }
    }

    pub(super) fn housed_in_release(&self, node: usize) -> (Vec<usize>, Vec<usize>) {
        let release = release_set(&self.lattice, &self.own, &self.reads, node);
        let housing = self.row_links_closure(node);
        let mut spare = Vec::new();
        let mut claim = Vec::new();
        for &g in &self.lattice.housed_ghosts {
            let Some(&b) = self.lattice.ghost_site.get(&g) else {
                continue;
            };
            if housing.contains(&b) {
                claim.push(g);
            } else if release.contains(&b) {
                spare.push(g);
            }
        }
        (spare, claim)
    }

    pub(super) fn ghost_row_elem(&self, ghost: usize) -> Ty {
        let Some(mint) = self.lattice.ghost_mints.get(&ghost) else {
            return Pending;
        };
        let mut r = Pending;
        for &b in &mint.bases {
            if is_ghost(&b) {
                r = join_ty(&r, &self.ghost_row_elem(b));
            } else if !is_root(&b)
                && let Tbl(inner) = &self.lattice.site_elem[b]
            {
                r = join_ty(&r, inner.as_ref());
            }
        }
        r
    }

    pub(super) fn same_row(&self, a: usize, b: usize) -> bool {
        if a == b {
            return true;
        }
        match (
            self.lattice.ghost_mints.get(&a),
            self.lattice.ghost_mints.get(&b),
        ) {
            (Some(ma), Some(mb)) => ma.key == mb.key && !ma.bases.is_disjoint(&mb.bases),
            _ => false,
        }
    }

    pub(super) fn check_row_ownership(
        &self,
        name: &str,
        depth: usize,
        shape: &TableShape,
        moved_srcs: &[(usize, String)],
    ) -> Result<(), ShapeError> {
        let new_ghosts: Vec<usize> = shape.aliases.iter().copied().filter(is_ghost).collect();
        if new_ghosts.is_empty() {
            return Ok(());
        }
        for (d, scope) in self.walk.scopes.iter().enumerate() {
            for (n, ts) in scope {
                if d == depth && n == name {
                    continue;
                }
                if moved_srcs.iter().any(|(md, m)| *md == d && m == n) {
                    continue;
                }
                for &old in &new_ghosts {
                    if ts
                        .aliases
                        .iter()
                        .any(|&g| is_ghost(&g) && self.same_row(old, g))
                    {
                        return Err(ShapeError(Diagnostic::lifetime(format!(
                            "the row read into '{name}' is already owned by \
                             '{n}' — one row has exactly one owning binding; read it through \
                             '{n}' instead"
                        ))));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn check_row_housing(&self, g: usize, value: &Expr) -> Result<(), ShapeError> {
        let skip = match value {
            Expr::Identifier(n) => Some(n.as_str()),
            _ => None,
        };
        for scope in &self.walk.scopes {
            for (n, ts) in scope {
                if Some(n.as_str()) == skip {
                    continue;
                }
                for &og in ts.aliases.iter().filter(|s| is_ghost(s)) {
                    if self.same_row(g, og) {
                        return Err(ShapeError(Diagnostic::lifetime(format!(
                            "the row read is already owned by '{n}' — one \
                             row has exactly one housing; store it through '{n}' instead"
                        ))));
                    }
                }
            }
        }
        for &h in &self.lattice.housed_ghosts {
            if h != g && self.same_row(g, h) {
                return Err(ShapeError(Diagnostic::lifetime(
                    "the row read is already housed in another cell — \
                     one row has exactly one housing",
                )));
            }
        }
        Ok(())
    }

    pub(super) fn reachable_rows(&self, origin: usize, depth: usize) -> BTreeSet<usize> {
        let mut level = BTreeSet::from([origin]);
        for _ in 0..depth {
            let mut next = BTreeSet::new();
            for s in &level {
                if let Some(kids) = self.lattice.child_sites.get(s) {
                    next.extend(kids.iter().copied());
                }
                if let Some(kids) = self.reads.row_links.get(s) {
                    next.extend(kids.iter().copied());
                }
            }
            level = next;
        }
        level
    }
}
