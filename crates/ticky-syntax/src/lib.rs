//! Lexer, parser and AST for Ticky's Python-like syntax.

pub mod ast;
pub mod diag;
pub mod lexer;
pub mod parser;

pub use diag::{Diag, Severity, Span};
pub use parser::parse;
