use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn die(line_no: usize, raw: &str, msg: String) -> ! {
    panic!("trace_signals.txt:{line_no}: {msg}\n  > {raw}")
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn take_field(line: &str) -> (&str, &str) {
    let line = line.trim_start();
    match line.find(char::is_whitespace) {
        Some(at) => (&line[..at], &line[at..]),
        None => (line, ""),
    }
}

/// Compile the C11 async substrate (async) into ONE shared object under
/// target/<profile>/ — the process-global alm state must live in a .so so
/// the loader guarantees a single copy per process no matter how many alm
/// artifacts link it. Every artifact the compiler emits gains
/// DT_NEEDED libalm_async.so (see main.rs's clang link line).
fn build_async_core() {
    const SOURCES: [&str; 8] = [
        "sys_sync.c",
        "state_globals.c",
        "mailbox.c",
        "ring_stream.c",
        "mailbox_accessors.c",
        "alm_tenant.c",
        "alm_coro.c",
        "str_pool.c",
    ];

    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let c_dir = manifest.join("async");
    // OUT_DIR = target/<profile>/build/<pkg>/<hash>/out (layout varies across
    // cargo versions) — walk up to the "build" dir, its parent is the profile
    let target_profile = {
        let out = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR is set by cargo"));
        let build_dir = out
            .ancestors()
            .find(|p| p.file_name().is_some_and(|n| n == "build"))
            .expect("OUT_DIR lives under target/<profile>/build/");
        build_dir
            .parent()
            .expect("build/ has a parent")
            .to_path_buf()
    };

    let cc = env::var("CC").unwrap_or_else(|_| "clang".into());
    let so = target_profile.join("libalm_async.so");
    let mut cmd = std::process::Command::new(&cc);
    cmd.arg("-shared")
        .arg("-fPIC")
        .arg("-O2")
        // gnu11, not c11: the substrate calls POSIX (usleep, ftruncate, mmap)
        .arg("-std=gnu11")
        .arg("-Wall")
        .arg("-Wextra")
        .arg(format!("-I{}", c_dir.display()));
    for src in SOURCES {
        cmd.arg(c_dir.join(src));
        println!("cargo:rerun-if-changed=async/{src}");
    }
    cmd.arg("-lpthread").arg("-o").arg(&so);
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("failed to spawn {cc} for libalm_async.so: {e}"));
    if !status.success() {
        panic!("building libalm_async.so failed");
    }

    // the alm bin (and its rlib link) resolves the vx_* surface from here;
    // the rpath keeps the compiler's own dev-loop host able to dlopen the
    // artifacts it just built, which DT_NEEDED this .so
    println!(
        "cargo:rustc-link-search=native={}",
        target_profile.display()
    );
    println!("cargo:rustc-link-lib=dylib=alm_async");
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        target_profile.display()
    );
}

fn main() {
    println!("cargo:rerun-if-changed=trace_signals.txt");
    build_async_core();
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR is set by cargo");
    let ssot = fs::read_to_string("trace_signals.txt")
        .expect("trace_signals.txt (the signal SSOT) must sit next to Cargo.toml");

    let mut seen_slots = BTreeSet::new();
    let mut seen_names = BTreeSet::new();
    let mut signals: Vec<(u8, String, String, String)> = Vec::new();

    for (idx, raw) in ssot.lines().enumerate() {
        let line_no = idx + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (slot_str, rest) = take_field(line);
        let (name, rest) = take_field(rest);
        let (owner, rest) = take_field(rest);
        let meaning = rest.trim();
        if slot_str.is_empty() || name.is_empty() || owner.is_empty() || meaning.is_empty() {
            die(
                line_no,
                raw,
                "expected `<slot> <NAME> <owner> <meaning>`".into(),
            );
        }
        let slot: u8 = match slot_str.parse() {
            Ok(s) => s,
            Err(_) => die(line_no, raw, format!("slot `{slot_str}` is not a u8")),
        };
        if !seen_slots.insert(slot) {
            die(line_no, raw, format!("slot {slot} double-booked"));
        }
        if !seen_names.insert(name) {
            die(line_no, raw, format!("name {name} declared twice"));
        }
        if name.is_empty()
            || !name
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        {
            die(line_no, raw, format!("NAME `{name}` must be A-Z, 0-9, _"));
        }
        if owner.chars().any(char::is_whitespace) {
            die(line_no, raw, "owner must be a single token".into());
        }
        if meaning.is_empty() {
            die(line_no, raw, "meaning must not be empty".into());
        }
        signals.push((
            slot,
            name.to_string(),
            owner.to_string(),
            meaning.to_string(),
        ));
    }
    if signals.is_empty() {
        panic!("trace_signals.txt declares no signals");
    }
    signals.sort_by_key(|s| s.0);

    let mut rust = String::from(
        "// @generated by build.rs from trace_signals.txt — edit the SSOT, not this file.\n\n",
    );
    for (slot, name, owner, meaning) in &signals {
        rust.push_str(&format!(
            "#[doc = \"{} ({})\"]\n",
            escape(meaning),
            escape(owner)
        ));
        rust.push_str("#[allow(dead_code)]\n");
        rust.push_str(&format!("pub const TRACE_{name}: u8 = {slot};\n\n"));
    }

    fs::write(Path::new(&out_dir).join("trace_signals.rs"), rust)
        .expect("write generated trace_signals.rs");
}
