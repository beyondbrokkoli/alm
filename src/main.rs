use alm::diag::Diagnostic;
use alm::dump::{render_ast, render_shape};
use alm::lexer::{self, LexOutput};
use alm::pipeline::{analyze_stage, front};
use alm::source::SourceFile;
use alm::surface::{Flag, Surface};
use std::path::PathBuf;
use std::process::ExitCode;

const HELP: &str = "\
Usage: alm [--index-base=0|1] [--for-limit=exclusive|inclusive] [--module-root=DIR] [--exe|--lib] <mode> <file.lua>

Modes:
  (none)          run the front end, the require splice, the shape
                  walk + checker, and the ffi gate. Failures render
                  the diagnostics on stderr, exit 1; a clean compile
                  exits 0 silently (the compile-success print arrives
                  with the backend layers).
  --dump-tokens   lex only; one token per line as `<kind> <start>..<end>`
                  (byte spans).
  --dump-ast      parse and print the post-desugar AST, one node per
                  line: statement `@line` attribution, constructor
                  slots with positional/explicit provenance, and the
                  desugar latches (`for$limit`, tuple temps).
  --dump-shape    walk and print the shape facts: one site per line with
                  its element type and layout verdict, plus the
                  ownership, ghost, fn-face, and checker fact families.

Flags must come before the source file; they resolve once into the
surface and are read at named seams only. --module-root anchors the
module tree for dotted requires (require(\"a.b\") resolves to
DIR/a/b.lua) — pipeline configuration, not a surface law. --exe links
a standalone executable and --lib a shared library (the default; the
linking itself arrives with the backend layers — the ffi gate reads
the mode now: ffi.load is --exe-only).";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let mut surface = Surface::default();
    let mut dump: Option<&str> = None;
    let mut module_root: Option<PathBuf> = None;
    // [ffi] The link mode, parsed like --module-root (pipeline
    // configuration): the ffi gate reads it now; the linking itself is
    // L9's. mirror's law — last flag wins, no refusal for repeats.
    let mut standalone = false;
    let mut source: Option<&String> = None;
    for arg in args {
        if source.is_some() {
            // Boundary words after the source file arrive with the
            // boundary host (L10); accepted and unused until then.
            continue;
        }
        if arg == "--help" || arg == "-h" {
            println!("{HELP}");
            return Ok(());
        }
        if arg == "--dump-tokens" || arg == "--dump-ast" || arg == "--dump-shape" {
            if dump.is_some() {
                return Err(
                    "alm compiler error: pick one of --dump-tokens, --dump-ast or --dump-shape"
                        .into(),
                );
            }
            dump = Some(arg);
            continue;
        }
        if arg == "--exe" {
            standalone = true;
            continue;
        }
        if arg == "--lib" {
            standalone = false;
            continue;
        }
        if let Some(raw) = arg.strip_prefix("--module-root=") {
            // Pipeline configuration, parsed beside the [surface]
            // flags with mirror's exact refusal wording — it anchors a
            // filesystem tree, so it never rides `Surface`.
            if raw.is_empty() {
                return Err(
                    "alm compiler error: --module-root requires a directory path \
                     (require(\"a.b\") resolves to DIR/a/b.lua — the flag anchors the tree)"
                        .into(),
                );
            }
            module_root = Some(raw.into());
            continue;
        }
        if arg.starts_with('-') {
            Flag::parse(arg)?.apply(&mut surface);
            continue;
        }
        source = Some(arg);
    }

    let Some(path) = source else {
        return Err(
            "alm compiler error: Usage: alm [flags] (--dump-tokens | --dump-ast | --dump-shape) <file.lua> (see --help)"
                .into(),
        );
    };
    let src = read_source(path)?;

    match dump {
        Some("--dump-tokens") => {
            let out = lexer::lex(&src);
            if let Some(err) = out.error {
                // Front-end rendering parity: exactly what mirror prints
                // for a refused match, down to the diagnostic wording.
                return Err(Diagnostic::syntax(err.text)
                    .with_site(Some(err.line))
                    .render());
            }
            let stdout = std::io::stdout();
            dump_tokens(&out, &mut stdout.lock())
                .map_err(|e| format!("alm compiler error: failed to write token dump: {e}"))
        }
        Some("--dump-ast") => {
            // --dump-ast: parse failures render exactly like the
            // compiler's (all diagnostics, mirror's fail_build shape).
            let out = front(&src, &surface);
            if !out.is_ok() {
                fail_build(&out.diagnostics);
            }
            let text = render_ast(&out.ast);
            let stdout = std::io::stdout();
            write_all(&text, &mut stdout.lock())
                .map_err(|e| format!("alm compiler error: failed to write AST dump: {e}"))
        }
        Some(_) => {
            // --dump-shape: refusals at any of the stages render
            // exactly like the compiler's.
            let out = match analyze_stage(&src, &surface, module_root.as_deref(), true, standalone)
            {
                Ok(out) => out,
                Err((_, diags)) => fail_build(&diags),
            };
            let text = render_shape(&out.facts, &out.ast);
            let stdout = std::io::stdout();
            write_all(&text, &mut stdout.lock())
                .map_err(|e| format!("alm compiler error: failed to write shape dump: {e}"))
        }
        None => match analyze_stage(&src, &surface, module_root.as_deref(), true, standalone) {
            Ok(_) => Ok(()),
            Err((_, diags)) => fail_build(&diags),
        },
    }
}

/// mirror's `fail_build` (main.rs @ 87aca4c): every diagnostic rendered
/// to stderr, then exit 1. The trace poke it also performs lands with
/// the trace layer, not the front end.
fn fail_build(diags: &[Diagnostic]) -> ! {
    for d in diags {
        eprintln!("{}", d.render());
    }
    std::process::exit(1);
}

// Read-failure wording matches mirror's main so a missing file looks
// identical in both compilers.
fn read_source(path: &str) -> Result<SourceFile, String> {
    SourceFile::read(path).map_err(|e| {
        let cwd = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        format!(
            "alm compiler error: Failed to read source file '{}'\n  Current directory: {cwd}\n  System error: {}",
            e.path, e.source
        )
    })
}

fn write_all(text: &str, w: &mut impl std::io::Write) -> std::io::Result<()> {
    w.write_all(text.as_bytes())
}

fn dump_tokens(out: &LexOutput<'_>, w: &mut impl std::io::Write) -> std::io::Result<()> {
    for (token, span) in &out.tokens {
        writeln!(w, "{token:?} {}..{}", span.start, span.end)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dump(text: &str) -> String {
        let src = SourceFile::new("t.lua", text);
        let out = lexer::lex(&src);
        let mut buf = Vec::new();
        dump_tokens(&out, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn dump_format_is_one_token_per_line_with_byte_spans() {
        assert_eq!(dump("local x"), "Local 0..5\nIdentifier(\"x\") 6..7\n");
    }

    #[test]
    fn dump_includes_string_payloads_verbatim() {
        assert_eq!(dump(r#""a b""#), "String(\"\\\"a b\\\"\") 0..5\n");
    }

    #[test]
    fn help_arg_succeeds() {
        assert!(run(&["--help".to_string()]).is_ok());
    }

    #[test]
    fn no_source_file_is_a_usage_error() {
        let err = run(&[]).unwrap_err();
        assert!(err.starts_with("alm compiler error: Usage:"), "{err}");
    }

    #[test]
    fn unknown_flag_refusal_is_mirror_wording() {
        let err = run(&["--nope".to_string(), "x.lua".to_string()]).unwrap_err();
        assert_eq!(
            err,
            "alm compiler error: Unknown flag '--nope'. Flags must come before the source file."
        );
    }

    #[test]
    fn surface_flag_refusal_is_mirror_wording() {
        let err = run(&["--index-base=7".to_string(), "x.lua".to_string()]).unwrap_err();
        assert_eq!(
            err,
            "alm compiler error: --index-base must be 0 or 1, got '7' \
             (the machinery is base-parametric; the surface is a toggle)"
        );
    }

    #[test]
    fn missing_file_matches_mirror_read_failure_wording() {
        let err = run(&["--dump-tokens".to_string(), "no/such/file.lua".to_string()]).unwrap_err();
        assert!(
            err.starts_with("alm compiler error: Failed to read source file 'no/such/file.lua'\n  Current directory: "),
            "{err}"
        );
        assert!(err.contains("\n  System error: "), "{err}");
    }

    #[test]
    fn lex_refusal_renders_as_the_front_end_would() {
        let src_file = std::env::temp_dir().join("alm_l1_refusal_smoke.lua");
        std::fs::write(&src_file, "local t = 1\nlocal x = `oops\n").unwrap();
        let err = run(&["--dump-tokens".to_string(), src_file.display().to_string()]).unwrap_err();
        assert_eq!(err, "line 2: Syntax Error: Lexer error");
        let _ = std::fs::remove_file(&src_file);
    }

    #[test]
    fn both_dump_modes_at_once_is_a_usage_error() {
        let err = run(&[
            "--dump-tokens".to_string(),
            "--dump-ast".to_string(),
            "x.lua".to_string(),
        ])
        .unwrap_err();
        assert_eq!(
            err,
            "alm compiler error: pick one of --dump-tokens, --dump-ast or --dump-shape"
        );
    }

    #[test]
    fn empty_module_root_refusal_is_mirror_wording() {
        let err = run(&["--module-root=".to_string(), "x.lua".to_string()]).unwrap_err();
        assert_eq!(
            err,
            "alm compiler error: --module-root requires a directory path \
             (require(\"a.b\") resolves to DIR/a/b.lua — the flag anchors the tree)"
        );
    }
}
