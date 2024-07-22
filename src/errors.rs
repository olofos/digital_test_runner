use miette::Diagnostic;
use thiserror::Error;

use crate::lexer::TokenKind;

#[derive(Debug, Error)]
/// Error returned from DataRowIterator
pub enum RuntimeError<T> {
    /// Driver error
    #[error("Driver error")]
    Driver(#[from] T),
    /// Runtime error
    #[error("Runtime error")]
    Runtime(#[source] RuntimeErrorKind),
}

/// Possible internal runtime errors
#[derive(Debug, Error)]
pub enum RuntimeErrorKind {
    /// If the driver returns a non-empty [Vec] of outputs
    /// it should always have the same number of elements.
    #[error("Wrong number of outputs. Expected {0} but got {1}")]
    WrongNumberOfOutputs(usize, usize),
    /// If the driver returns a non-empty [Vec] of outputs
    /// the signals should always appear in the same order
    #[error("The order of the outputs must not change.")]
    WrongOutputOrder,
}

#[derive(Debug, Error, Diagnostic)]
pub(super) enum ParseErrorKind {
    #[error("Unexpected EOF")]
    UnexpectedEof,
    #[error("Unexpected token. Expected {expected_kind:?} but found {found_kind:?}")]
    NotExpectedToken {
        expected_kind: TokenKind,
        found_kind: TokenKind,
    },
    #[error("Unexpected token {kind:?}")]
    UnexpectedToken { kind: TokenKind },
    #[error("Unknown token")]
    UnknownToken,

    #[error("Expected a number but found a {kind:?} token")]
    ExpectedNumber { kind: TokenKind },
    #[error("Could not parse number")]
    NumberParseError(#[from] std::num::ParseIntError),
    #[error("Number of bits cannot exceed 64")]
    TooManyBits,
    #[error("Expected a new line at the end of statement")]
    ExpectedNewLine,
    #[error("Expected C, X or Z but found {ident}")]
    ExpectedCXZ { ident: String },
    #[error("Unexpected End token at top level")]
    UnexpectedEndAtTopLevel,
    #[error("Wrong number of entries in data row. Expected {expected} but found {found}")]
    DataRowWithWrongNumberOfSignals { expected: usize, found: usize },
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

#[derive(Debug, Error, Diagnostic)]
#[diagnostic(transparent)]
#[error(transparent)]
/// Error while loading dig file
pub struct DigFileError(#[from] pub(crate) DigFileErrorKind);

#[derive(Debug, Error, Diagnostic)]
#[diagnostic()]
pub(crate) enum DigFileErrorKind {
    #[error("XML parsing error")]
    XMLError(#[source] roxmltree::Error, #[label("here")] logos::Span),
    #[error("Could not parse empty test")]
    EmptyTest,
    #[error("Signals {0} found in tests but not found in circuit")]
    MissingSignals(String),
}
