/// Byte range in the source file.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    pub fn to(self, other: Span) -> Span {
        Span { start: self.start.min(other.start), end: self.end.max(other.end) }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    pub help: Option<String>,
}

impl Diag {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Diag { severity: Severity::Error, span, message: message.into(), help: None }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Diag { severity: Severity::Warning, span, message: message.into(), help: None }
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// 1-based line and column of `pos`.
    pub fn line_col(src: &str, pos: usize) -> (usize, usize) {
        let pos = pos.min(src.len());
        let line = src[..pos].matches('\n').count() + 1;
        let col = pos - src[..pos].rfind('\n').map_or(0, |i| i + 1) + 1;
        (line, col)
    }

    /// Renders the diagnostic with the offending source line and a caret underline.
    pub fn render(&self, file: &str, src: &str) -> String {
        let (line, col) = Self::line_col(src, self.span.start);
        let text = src.lines().nth(line - 1).unwrap_or("");
        let width = (self.span.end.saturating_sub(self.span.start)).clamp(1, text.len().saturating_sub(col - 1).max(1));
        let kind = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
        };
        let gutter = line.to_string().len();
        let mut out = format!(
            "{kind}: {}\n{:gutter$}--> {file}:{line}:{col}\n{:gutter$} |\n{line} | {text}\n{:gutter$} | {}{}\n",
            self.message,
            "",
            "",
            "",
            " ".repeat(col - 1),
            "^".repeat(width),
        );
        if let Some(h) = &self.help {
            out.push_str(&format!("{:gutter$} = help: {h}\n", ""));
        }
        out
    }
}
