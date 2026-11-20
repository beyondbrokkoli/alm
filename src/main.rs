use alm::diag::Diagnostic;
use alm::lexer::{self, LexOutput};
use alm::source::SourceFile;
use std::process::ExitCode;

const HELP: &str = "\
Usage: alm --dump-tokens <file.lua>

Lex a source file and print one token per line as `<kind> <start>..<end>`
(byte spans). Lex refusals render exactly as the compiler's front end
reports them (`line N: Syntax Error: …`) on stderr, exit 1.";

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
    let path = match args {
        [flag, path] if flag == "--dump-tokens" => path.as_str(),
        [flag] if flag == "--help" || flag == "-h" => {
            println!("{HELP}");
            return Ok(());
        }
        _ => {
            return Err(
                "alm compiler error: Usage: alm --dump-tokens <file.lua> (see --help)".into(),
            );
        }
    };

    // Read-failure wording matches mirror's main so a missing file looks
    // identical in both compilers.
    let src = SourceFile::read(path).map_err(|e| {
        let cwd = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        format!(
            "alm compiler error: Failed to read source file '{}'\n  Current directory: {cwd}\n  System error: {}",
            e.path, e.source
        )
    })?;

    let out = lexer::lex(&src);
    if let Some(err) = out.error {
        // Front-end rendering parity: exactly what mirror prints for a
        // refused match, down to the wording of the diagnostic.
        return Err(Diagnostic::syntax(err.text)
            .with_site(Some(err.line))
            .render());
    }

    let stdout = std::io::stdout();
    dump_tokens(&out, &mut stdout.lock())
        .map_err(|e| format!("alm compiler error: failed to write token dump: {e}"))
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
    fn wrong_args_are_a_usage_error() {
        let err = run(&[]).unwrap_err();
        assert!(err.starts_with("alm compiler error: Usage:"), "{err}");
        let err = run(&["--nope".to_string(), "x.lua".to_string()]).unwrap_err();
        assert!(err.starts_with("alm compiler error: Usage:"), "{err}");
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
}
