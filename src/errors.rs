use miette::Diagnostic;
use thiserror::Error;

use crate::lexer::TokenKind;

#[derive(Debug, Error)]
/// Error returned from DataRowIterator
pub enum RunError<T> {
    /// Driver error
    #[error("Driver error")]
    Driver(#[from] T),
    /// Runtime error
    #[error("Runtime error")]
    Runtime(anyhow::Error),
}

#[derive(Debug, Error, Diagnostic)]
pub(crate) enum ParseErrorKind {
    #[error("Unexpected EOF")]
    UnexpectedEof,
    #[error("Unexpected token. Expected {expected_kind:?} but found {found_kind:?}")]
    NotExpectedToken {
        expected_kind: TokenKind,
        found_kind: TokenKind,
    },
    #[error("Unexpected token in expression")]
    UnexpectedToken { kind: TokenKind },
    #[error("Unknown token")]
    UnknownToken,
    #[error("Expected a signal name")]
    ExpectedSignalName,
    #[error("Expected a number but found a {kind:?} token")]
    ExpectedNumber { kind: TokenKind },
    #[error("Could not parse number")]
    NumberParseError(#[source] std::num::ParseIntError),
    #[error("Number of bits cannot exceed 64")]
    TooManyBits,
    #[error("Expected a new line at the end of statement")]
    ExpectedNewLine,
    #[error("Expected C, X or Z but found {ident}")]
    ExpectedCXZ { ident: String },
    #[error("Unexpected End token at top level")]
    UnexpectedEndAtTopLevel,
}

#[derive(Debug, Error, Diagnostic)]
#[error("Parse error")]
#[diagnostic()]
/// Error returned by test case parser
pub struct ParseError {
    #[source]
    pub(crate) kind: ParseErrorKind,
    /// Error location
    #[label("here")]
    pub at: logos::Span,
}

pub fn test() -> ParseError {
    ParseError {
        kind: ParseErrorKind::NotExpectedToken {
            expected_kind: TokenKind::And,
            found_kind: TokenKind::Def,
        },
        at: 4..6,
    }
}
