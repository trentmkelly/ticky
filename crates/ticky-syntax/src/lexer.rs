//! Python-style tokenizer: produces INDENT/DEDENT/NEWLINE tokens from leading whitespace,
//! and joins lines implicitly inside brackets.

use crate::diag::{Diag, Span};

#[derive(Clone, PartialEq, Debug)]
pub enum Tok {
    Name(String),
    Int(i64),
    Str(String),
    Op(&'static str),
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

// Longest first, so `//=` wins over `//` and `/`.
const OPS: &[&str] = &[
    "**=", "//=", "<<=", ">>=", "**", "//", "<<", ">>", "<=", ">=", "==", "!=", "+=", "-=", "*=", "/=", "%=",
    "&=", "|=", "^=", "->", "+", "-", "*", "/", "%", "&", "|", "^", "~", "<", ">", "(", ")", "[", "]", "{",
    "}", ",", ":", ".", ";", "@", "=",
];

pub fn lex(src: &str) -> Result<Vec<Token>, Diag> {
    let bytes = src.as_bytes();
    let mut toks: Vec<Token> = Vec::new();
    let mut indents = vec![0usize];
    let mut depth = 0usize; // bracket nesting
    let mut i = 0usize;
    let mut at_line_start = true;

    while i < bytes.len() {
        if at_line_start && depth == 0 {
            // Measure indentation; skip blank and comment-only lines entirely.
            let start = i;
            let mut width = 0;
            while i < bytes.len() && (bytes[i] == b' ' || bytes[i] == b'\t') {
                if bytes[i] == b'\t' {
                    return Err(Diag::error(Span::new(i, i + 1), "tabs are not allowed for indentation")
                        .with_help("indent with spaces (4 per level is conventional)"));
                }
                width += 1;
                i += 1;
            }
            if i >= bytes.len() {
                break;
            }
            if bytes[i] == b'\n' || bytes[i] == b'\r' || bytes[i] == b'#' {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                i += 1;
                continue;
            }
            at_line_start = false;
            let top = *indents.last().unwrap();
            if width > top {
                indents.push(width);
                toks.push(Token { tok: Tok::Indent, span: Span::new(start, i) });
            } else {
                while width < *indents.last().unwrap() {
                    indents.pop();
                    toks.push(Token { tok: Tok::Dedent, span: Span::new(i, i) });
                }
                if width != *indents.last().unwrap() {
                    return Err(Diag::error(Span::new(start, i), "unindent does not match any outer indentation level"));
                }
            }
        }

        let c = bytes[i];
        match c {
            b' ' | b'\t' | b'\r' => i += 1,
            b'#' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'\\' if bytes.get(i + 1) == Some(&b'\n') => i += 2,
            b'\n' => {
                if depth == 0 {
                    if !matches!(toks.last().map(|t| &t.tok), Some(Tok::Newline) | None) {
                        toks.push(Token { tok: Tok::Newline, span: Span::new(i, i + 1) });
                    }
                    at_line_start = true;
                }
                i += 1;
            }
            b'0'..=b'9' => {
                let start = i;
                let (radix, digits_start) = match (c, bytes.get(i + 1).map(|b| b.to_ascii_lowercase())) {
                    (b'0', Some(b'x')) => (16, i + 2),
                    (b'0', Some(b'b')) => (2, i + 2),
                    (b'0', Some(b'o')) => (8, i + 2),
                    _ => (10, i),
                };
                i = digits_start;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let text: String = src[digits_start..i].chars().filter(|c| *c != '_').collect();
                let span = Span::new(start, i);
                let v = i64::from_str_radix(&text, radix)
                    .map_err(|_| Diag::error(span, format!("invalid integer literal `{}`", &src[start..i])))?;
                if v > u32::MAX as i64 {
                    return Err(Diag::error(span, "integer literal does not fit in 32 bits"));
                }
                toks.push(Token { tok: Tok::Int(v), span });
            }
            b'"' | b'\'' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                loop {
                    match bytes.get(i) {
                        None | Some(b'\n') => {
                            return Err(Diag::error(Span::new(start, i), "unterminated string"));
                        }
                        Some(&q) if q == c => {
                            i += 1;
                            break;
                        }
                        Some(b'\\') => {
                            let esc = bytes.get(i + 1).copied().unwrap_or(b'\\');
                            s.push(match esc {
                                b'n' => '\n',
                                b't' => '\t',
                                other => other as char,
                            });
                            i += 2;
                        }
                        Some(_) => {
                            let ch = src[i..].chars().next().unwrap();
                            s.push(ch);
                            i += ch.len_utf8();
                        }
                    }
                }
                toks.push(Token { tok: Tok::Str(s), span: Span::new(start, i) });
            }
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                toks.push(Token { tok: Tok::Name(src[start..i].to_string()), span: Span::new(start, i) });
            }
            _ => {
                let op = OPS.iter().find(|op| src[i..].starts_with(**op)).ok_or_else(|| {
                    let ch = src[i..].chars().next().unwrap();
                    Diag::error(Span::new(i, i + ch.len_utf8()), format!("unexpected character `{ch}`"))
                })?;
                match *op {
                    "(" | "[" | "{" => depth += 1,
                    ")" | "]" | "}" => depth = depth.saturating_sub(1),
                    _ => {}
                }
                toks.push(Token { tok: Tok::Op(op), span: Span::new(i, i + op.len()) });
                i += op.len();
            }
        }
    }
    let end = src.len();
    if !matches!(toks.last().map(|t| &t.tok), Some(Tok::Newline) | None) {
        toks.push(Token { tok: Tok::Newline, span: Span::new(end, end) });
    }
    while indents.len() > 1 {
        indents.pop();
        toks.push(Token { tok: Tok::Dedent, span: Span::new(end, end) });
    }
    toks.push(Token { tok: Tok::Eof, span: Span::new(end, end) });
    Ok(toks)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<Tok> {
        lex(src).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn indentation() {
        let t = kinds("if x:\n    y = 1\n\n    # c\nz = 0x1_0\n");
        assert_eq!(
            t,
            vec![
                Tok::Name("if".into()),
                Tok::Name("x".into()),
                Tok::Op(":"),
                Tok::Newline,
                Tok::Indent,
                Tok::Name("y".into()),
                Tok::Op("="),
                Tok::Int(1),
                Tok::Newline,
                Tok::Dedent,
                Tok::Name("z".into()),
                Tok::Op("="),
                Tok::Int(16),
                Tok::Newline,
                Tok::Eof
            ]
        );
    }

    #[test]
    fn brackets_join_lines() {
        let t = kinds("x = (1 +\n  2)\n");
        assert!(!t[..t.len() - 2].contains(&Tok::Newline));
    }
}
