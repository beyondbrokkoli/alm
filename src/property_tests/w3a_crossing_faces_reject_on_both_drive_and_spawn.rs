
/// W3a's Data Transfer Contract, drive and spawn faces (the pin-owed
/// register, census §3 cluster B row 19): a closure-carrying table may
/// not cross a module boundary — the env pointer is this module's heap
/// state. The `return` face is pinned by escape_no_crossing; the drive
/// call and coroutine.resume faces ride the ffi surface, so the ONE
/// pipeline (H10) pins them at both of its gates: .so opts refuse the
/// surface itself at `Stage::Ffi` (packaging policy — the drift this
/// fold surfaced: the harness's old private walk had no such gate),
/// and exe opts — where the surface is legal — reach analysis and
/// reject on the TYPE discipline.
#[test]
fn w3a_crossing_faces_reject_on_both_drive_and_spawn() {
    let drive_face = r#"
        local ffi = require("ffi")
        ffi.cdef("void* alm_exec(void*);")
        local lib = ffi.load(arg[0])
        local function Tick() return 1 end
        local pkt = { step = Tick, seed = 3 }
        lib.alm_exec(pkt)
    "#;
    let spawn_face = r#"
        local coroutine = require("coroutine")
        local ffi = require("ffi")
        ffi.cdef("void* alm_exec(void*);")
        local lib = ffi.load(arg[0])
        local co = coroutine.create(lib)
        local function Tick() return 1 end
        local pkt = { step = Tick, seed = 3 }
        coroutine.resume(co, pkt)
    "#;
    for (label, source, needle) in [
        (
            "drive",
            drive_face,
            "a closure cannot cross a module boundary — the drive table marshals flat \
             cells only",
        ),
        (
            "spawn",
            spawn_face,
            "a closure cannot cross a module boundary — the spawn table marshals flat \
             cells only",
        ),
    ] {
        // the .so-opts face: the packaging gate precedes the type
        // discipline in the one pipeline
        match compile(source) {
            Err((Stage::Ffi, diags)) => {
                assert!(
                    diags
                        .iter()
                        .any(|d| d.render().contains("ffi surface")
                            && d.render().contains("--exe-only")),
                    "the {label} face's .so-opts rejection lost the gate text: {}",
                    diags_text(&diags)
                );
            }
            other => panic!(
                "the {label} ffi face must reject at the ffi gate under .so opts: {}",
                match other {
                    Ok(_) => "accepted".to_string(),
                    Err((s, d)) => format!("{}: {}", s.name(), diags_text(&d)),
                }
            ),
        }
        // the exe-opts face: the surface is legal, the crossing rejects
        // at analysis
        match compile_exe(source) {
            Err((Stage::Analyze, diags)) => {
                assert!(
                    diags.iter().any(|d| d.render().contains(needle)),
                    "the {label} face rejected with the wrong text: {}",
                    diags_text(&diags)
                );
            }
            other => panic!(
                "the {label} crossing face did not reject at analysis under exe opts: {}",
                match other {
                    Ok(_) => "accepted".to_string(),
                    Err((s, d)) => format!("{}: {}", s.name(), diags_text(&d)),
                }
            ),
        }
    }
}
