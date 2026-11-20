use std::fmt;
use std::path::Path;

/// An in-memory source file with its newline offsets precomputed.
///
/// Ported improvement (Class A2 in REBASE_PLAN.md §3.1): mirror counts
/// newlines per diagnostic in pipeline.rs and keeps a second, private
/// newline table inside the parser. Here one owner holds the table and
/// both call sites (today only the lexer; the parser at L2) read it.
/// The arithmetic is unchanged — `line_of(off)` is `1 +` the number of
/// newline bytes strictly before `off`, byte offsets throughout.
pub struct SourceFile {
    path: String,
    text: String,
    /// Byte offsets of every `\n` in `text`, ascending.
    newlines: Vec<usize>,
}

/// Reading a source file failed. The CLI renders this with mirror's
/// wording (path, current directory, system error) so failure output
/// stays comparable across the two compilers.
#[derive(Debug)]
pub struct ReadError {
    pub path: String,
    pub source: std::io::Error,
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.source)
    }
}

impl SourceFile {
    pub fn new(path: impl Into<String>, text: impl Into<String>) -> Self {
        let text = text.into();
        let newlines = text
            .bytes()
            .enumerate()
            .filter(|(_, b)| *b == b'\n')
            .map(|(i, _)| i)
            .collect();
        SourceFile {
            path: path.into(),
            text,
            newlines,
        }
    }

    pub fn read(path: impl AsRef<Path>) -> Result<Self, ReadError> {
        let path = path.as_ref();
        let display = path.display().to_string();
        let text = std::fs::read_to_string(path).map_err(|source| ReadError {
            path: display.clone(),
            source,
        })?;
        Ok(Self::new(display, text))
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    /// 1-based line of a byte offset. Same math as the mirror front end
    /// (pipeline.rs counts `\n` in `text[..off]`; the parser's newline
    /// vec partitions on `< off`) — both equal this.
    pub fn line_of(&self, off: usize) -> usize {
        1 + self.newlines.partition_point(|&n| n < off)
    }

    /// 1-based line and column of a byte offset. The column counts
    /// bytes since the previous newline (or file start); the mirror
    /// front end does not render columns yet, so this is additive
    /// surface for later diagnostic layers, not a parity concern.
    pub fn line_col(&self, off: usize) -> (usize, usize) {
        let line = self.line_of(off);
        let bol = if line == 1 {
            0
        } else {
            self.newlines[line - 2] + 1
        };
        (line, off - bol + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::SourceFile;

    #[test]
    fn line_of_counts_newlines_strictly_before_the_offset() {
        let src = SourceFile::new("t.lua", "a\nbb\nccc");
        assert_eq!(src.line_of(0), 1);
        assert_eq!(src.line_of(1), 1); // the first \n itself belongs to line 1
        assert_eq!(src.line_of(2), 2);
        assert_eq!(src.line_of(4), 2); // the second \n belongs to line 2
        assert_eq!(src.line_of(5), 3);
        assert_eq!(src.line_of(src.text().len()), 3);
    }

    #[test]
    fn line_of_on_empty_and_blank_files() {
        assert_eq!(SourceFile::new("e.lua", "").line_of(0), 1);
        // Strictly-before semantics: the byte AT a newline offset is
        // already past that newline (mirror's count over [..off] agrees).
        assert_eq!(SourceFile::new("n.lua", "\n\n\n").line_of(0), 1);
        assert_eq!(SourceFile::new("n.lua", "\n\n\n").line_of(1), 2);
        assert_eq!(SourceFile::new("n.lua", "\n\n\n").line_of(2), 3);
        assert_eq!(SourceFile::new("n.lua", "\n\n\n").line_of(3), 4);
        assert_eq!(SourceFile::new("n.lua", "\n\n\n").line_of(4), 4);
    }

    #[test]
    fn line_col_counts_bytes_from_line_start() {
        let src = SourceFile::new("t.lua", "ab\ncd");
        assert_eq!(src.line_col(0), (1, 1));
        assert_eq!(src.line_col(1), (1, 2));
        assert_eq!(src.line_col(3), (2, 1));
        assert_eq!(src.line_col(4), (2, 2));
    }

    #[test]
    fn crlf_lines_count_by_the_lone_newline_byte() {
        // Parity: only `\n` breaks lines, so a `\r` is an ordinary
        // (skipped-whitespace) byte — mirror's counting is identical.
        let src = SourceFile::new("t.lua", "a\r\nb");
        assert_eq!(src.line_of(0), 1);
        assert_eq!(src.line_of(2), 1);
        assert_eq!(src.line_of(3), 2);
        assert_eq!(src.line_col(3), (2, 1));
    }

    #[test]
    fn read_reports_the_path_and_system_error() {
        let err = match SourceFile::read("no/such/file.lua") {
            Ok(_) => panic!("reading a missing file cannot succeed"),
            Err(e) => e,
        };
        assert_eq!(err.path, "no/such/file.lua");
        assert!(err.source.kind() == std::io::ErrorKind::NotFound);
    }
}
