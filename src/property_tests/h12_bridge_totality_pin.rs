
/// H12 pin 3 — the bridge's totality: every pair key in the six maps
/// is bridged, every bridge key has its pair, every instance is
/// reachable from ROOT through the children maps, and R1's arithmetic
/// holds at depth two under loops (the ABSOLUTE break base — the
/// lowerer's twin check fires over this same shape via the full
/// pipeline below).
#[test]
fn h12_bridge_totality_pin() {
    let source = "\
local t = {}
t[\"k\"] = 7
local function Get(s) return t[s] end
local function Twice() return Get(\"k\") + Get(\"k\") end
local base = 1
local function Add1(x) return x + base end
local function Drive(f, n) return f(n) end
print(Twice())
print(Twice())
print(Drive(Add1, 5))
local function Inner(x) return x + 1 end
local function Outer(x)
    while x < 10 do
        x = Inner(x)
    end
    return x
end
while base < 3 do
    base = base + 1
    local q = Twice()
    local r = Outer(base)
end
local rec = { fn = Add1 }
local z = rec.fn(2)
local function Maker(k)
    local function GetK() return k end
    return GetK
end
local gk = Maker(7)
local w = gk()
";
    let ast = parse_parts(source);
    let ctx = analysis::build_context(&ast);
    let shape = crate::shape::analyze_with(&ctx, true);
    assert!(
        shape.diagnostics.is_empty(),
        "H12 pin source must analyze clean: {:?}",
        crate::property_tests::diags_text(&shape.diagnostics)
    );

    // T1: every pair key in the six maps is bridged (and its owner is
    // a real record)
    let bridged = |expr: NodeId, site: NodeId| {
        let owner = *shape
            .instance_of
            .get(&(expr, site))
            .unwrap_or_else(|| panic!("pair ({expr:?}, {site:?}) has no bridge entry"));
        assert!(
            shape.instances.contains_key(&owner),
            "the bridge names a real instance for ({expr:?}, {site:?})"
        );
        owner
    };
    for (expr, site) in shape.call_defs.keys() {
        bridged(*expr, *site);
    }
    for (expr, site) in shape.call_rets.keys() {
        bridged(*expr, *site);
    }
    for (expr, site) in shape.index_key_lanes.keys() {
        bridged(*expr, *site);
    }
    for (expr, site) in shape.access_elems.keys() {
        bridged(*expr, *site);
    }
    for (expr, site) in shape.creation_envs.keys() {
        bridged(*expr, *site);
    }
    for (expr, site) in &shape.closure_calls {
        bridged(*expr, *site);
    }

    // T2: every bridge key has its pair — the bridge invents nothing
    for (expr, site) in shape.instance_of.keys() {
        assert!(
            shape.call_defs.contains_key(&(*expr, *site))
                || shape.call_rets.contains_key(&(*expr, *site))
                || shape.index_key_lanes.contains_key(&(*expr, *site))
                || shape.access_elems.contains_key(&(*expr, *site))
                || shape.creation_envs.contains_key(&(*expr, *site))
                || shape.closure_calls.contains(&(*expr, *site)),
            "bridge entry ({expr:?}, {site:?}) has no pair in any map"
        );
    }

    // T3: clean compile — every instance reachable from ROOT
    let mut reached = std::collections::BTreeSet::from([crate::shape::InstanceId::ROOT]);
    for rec in shape.instances.values() {
        reached.extend(rec.children.values().flatten().copied());
    }
    for &k in shape.instances.keys() {
        assert!(
            reached.contains(&k),
            "instance {k:?} is unreachable from ROOT on a clean compile"
        );
    }
    let only_child = |owner: crate::shape::InstanceId, call: NodeId| {
        *shape.instances[&owner].children[&call]
            .iter()
            .next()
            .unwrap()
    };

    // the ROOT convention (R2): nobody's call, nobody's callee, the
    // top-level facts' owner
    let root = &shape.instances[&crate::shape::InstanceId::ROOT];
    assert!(root.call.is_none() && root.fn_node.is_none() && root.ret.is_none());
    assert_eq!(root.frame_base, 0);
    assert_eq!(root.break_base, 0);
    assert!(root.params.is_empty() && root.body.is_empty());
    assert!(
        !root.creation_envs.is_empty(),
        "the creation site bridges to ROOT"
    );

    // the FIELD-callee closure dispatch (closure_calls' own face): a
    // record field pinned to a closure singleton, called at top level
    // — the pair self-keys, the owner is ROOT, the dispatch's instance
    // carries the RESOLVED env face (Add1 captures base — a face with
    // one cell)
    let rec_fn_call = match &ast[14] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("the last statement binds the field dispatch"),
    };
    assert!(
        shape.closure_calls.contains(&(rec_fn_call, rec_fn_call)),
        "the field dispatch rides closure_calls"
    );
    assert_eq!(
        shape.instance_of[&(rec_fn_call, rec_fn_call)],
        crate::shape::InstanceId::ROOT,
        "a top-level self-pair bridges to ROOT"
    );
    assert!(
        root.closure_calls.contains(&rec_fn_call),
        "ROOT's shadow carries the dispatch"
    );
    let k_disp = *root.children[&rec_fn_call].iter().next().unwrap();
    let add1_lit = match &ast[5] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("Add1's literal is the sixth statement"),
    };
    let disp_rec = &shape.instances[&k_disp];
    assert_eq!(
        disp_rec.fn_node,
        Some(add1_lit),
        "the record's field pins Add1"
    );
    let face = disp_rec
        .env_face
        .as_ref()
        .expect("the call-through records its env face");
    assert!(
        face.is_empty(),
        "a top-level fn literal captures nothing — the flat module \
         resolves top-level names late: {face:?}"
    );

    // the factory shape (escape_factory_env's family): GetK is defined
    // INSIDE Maker, captures k, escapes as a value at a DEPTH-ONE
    // creation site (its pair keys against Maker's call — the owner is
    // kMaker), and the later dispatch through gk carries the RESOLVED
    // face — R3's sharpest form: a non-empty env on an instance record
    let maker_call = match &ast[16] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("gk binds Maker's call"),
    };
    let k_maker = only_child(crate::shape::InstanceId::ROOT, maker_call);
    let getk_value = {
        let maker_body = match &ast[15] {
            Stmt::LocalDecl { exprs, .. } => match &exprs[0] {
                Expr::Function { body, .. } => body,
                _ => panic!("Maker binds a fn literal"),
            },
            _ => panic!("Maker's declaration is the sixteenth statement"),
        };
        match &maker_body[1] {
            Stmt::Return {
                value: Some(value @ Expr::Identifier { .. }),
                ..
            } => value.id(),
            _ => panic!("Maker returns the GetK value read"),
        }
    };
    assert_eq!(
        shape.instance_of[&(getk_value, maker_call)],
        k_maker,
        "the creation site's pair keys against the ENCLOSING expansion"
    );
    assert_eq!(
        shape.instances[&k_maker].creation_envs[&getk_value],
        match &ast[15] {
            Stmt::LocalDecl { exprs, .. } => match &exprs[0] {
                Expr::Function { body, .. } => match &body[0] {
                    Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
                    _ => panic!("GetK's literal is Maker's first body statement"),
                },
                _ => panic!(),
            },
            _ => panic!(),
        },
        "the owner's creation_envs shadow names the escaping literal"
    );
    let gk_call = match &ast[17] {
        Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
        _ => panic!("w binds the dispatch"),
    };
    let k_gk = only_child(crate::shape::InstanceId::ROOT, gk_call);
    let gk_rec = &shape.instances[&k_gk];
    let face = gk_rec
        .env_face
        .as_ref()
        .expect("the factory dispatch records its env face");
    assert_eq!(
        face.len(),
        1,
        "R3: GetK's capture rides the instance — one cell"
    );
    assert_eq!(
        face.get("k"),
        Some(&crate::shape::Ty::Int),
        "the resolved face carries k's cell type"
    );

    // R1's arithmetic at depth two under loops: the Outer call inside
    // the top-level while mints at ABSOLUTE base 1; the Inner call
    // inside OUTER's while mints at ABSOLUTE base 2 (enclosing base 1
    // + Outer-relative depth 1) — the naive relative read would say 1
    let fn_body = |stmt: usize| match &ast[stmt] {
        Stmt::LocalDecl { exprs, .. } => match &exprs[0] {
            Expr::Function { body, .. } => body,
            _ => panic!("the local binds a fn literal"),
        },
        _ => panic!("the statement declares a fn"),
    };
    let outer_call_in_loop = match &ast[12] {
        Stmt::While { body, .. } => match &body[2] {
            Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
            _ => panic!("the loop's third statement binds Outer's call"),
        },
        _ => panic!("the final statement is the top-level while"),
    };
    let k_outer_loop = only_child(crate::shape::InstanceId::ROOT, outer_call_in_loop);
    assert_eq!(
        shape.instances[&k_outer_loop].break_base, 1,
        "a call inside one top-level loop mints at absolute base 1"
    );
    let inner_call = match &fn_body(11)[0] {
        Stmt::While { body, .. } => match &body[0] {
            Stmt::Assignment { expr, .. } => match expr {
                Expr::Call { .. } => expr.id(),
                _ => panic!("Outer's loop assigns Inner's call"),
            },
            _ => panic!("Outer's loop opens with the assignment"),
        },
        _ => panic!("Outer's body opens with the while"),
    };
    let k_inner_loop = only_child(k_outer_loop, inner_call);
    assert_eq!(
        shape.instances[&k_inner_loop].break_base, 2,
        "R1: enclosing base 1 + Outer-relative depth 1 — the ABSOLUTE \
         base, the lowerer's break_ctxs.len() twin"
    );
    assert_eq!(
        shape.instances[&k_inner_loop].frame_base, 3,
        "frames: the top loop's scope, Outer's expansion scope, and \
         Outer's while scope below"
    );

    // the full pipeline over the same shape: the lowerer's twin check
    // (ruling R1) fires at every expansion entry in debug — a break
    // base disagreement surfaces here as a panic
    assert!(
        compile_exe(source).is_ok(),
        "the lowerer lowers this shape clean — the twin check holds"
    );

    // Pin Twice()'s inline call-site expansion via `local q = Twice()`
    // (the second statement inside the top-level while loop at ast[12])
    let loop_twice_call = match &ast[12] {
        Stmt::While { body, .. } => match &body[1] {
            Stmt::LocalDecl { exprs, .. } => exprs[0].id(),
            _ => panic!("the loop's second statement binds Twice's call"),
        },
        _ => panic!("ast[12] is the top-level while"),
    };
    let k_twice = only_child(crate::shape::InstanceId::ROOT, loop_twice_call);
    let twice_rec = &shape.instances[&k_twice];
    assert_eq!(
        twice_rec.children.len(),
        2,
        "Twice() expands two distinct call sites for Get(\"k\") + Get(\"k\")"
    );
}
