use miette::{Diagnostic, NamedSource};
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

#[derive(Debug, Error, Diagnostic, PartialEq, Eq)]
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
    #[error("Expected a constant expression")]
    ExpectedConst,
    #[error("Function {ident} not found")]
    FunctionNotFound { ident: String },
    #[error("Wrong number of arguments. Expeted {expected} but found {found}")]
    WrongNumberOfArguments { expected: usize, found: usize },
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
    #[source_code]
    pub(crate) source_code: Option<NamedSource<String>>,
}

impl ParseError {
    pub(crate) fn with_source(self, source: NamedSource<String>) -> Self {
        Self {
            source_code: Some(source),
            ..self
        }
    }
}

/// Error returned by [ParsedTestCase::with_signals]
#[derive(Debug, Error, Diagnostic)]
#[error("Signal mismatch")]
#[diagnostic()]
pub struct SignalError(
    #[source]
    #[diagnostic_source]
    pub(crate) SignalErrorKind,
);

impl SignalError {
    pub(crate) fn with_source(self, source: NamedSource<String>) -> Self {
        let kind = match self.0 {
            SignalErrorKind::UnknownSignals {
                signals,
                at,
                source_code: _,
            } => SignalErrorKind::UnknownSignals {
                signals,
                at,
                source_code: Some(source),
            },
            SignalErrorKind::NotAnInput {
                name,
                at,
                signal_span,
                source_code: _,
            } => SignalErrorKind::NotAnInput {
                name,
                at,
                signal_span,
                source_code: Some(source),
            },
            SignalErrorKind::NotAnOutput {
                name,
                at,
                signal_span,
                source_code: _,
            } => SignalErrorKind::NotAnOutput {
                name,
                at,
                signal_span,
                source_code: Some(source),
            },
            SignalErrorKind::UnknownVariableOrSignal {
                name,
                at,
                source_code: _,
            } => SignalErrorKind::UnknownVariableOrSignal {
                name,
                at,
                source_code: Some(source),
            },
        };
        Self(kind)
    }
}

#[derive(Debug, Error, Diagnostic)]
pub(crate) enum SignalErrorKind {
    #[error("Unknown signals: {signals}")]
    #[diagnostic()]
    UnknownSignals {
        signals: String,
        #[label(collection, "here")]
        at: Vec<logos::Span>,
        #[source_code]
        source_code: Option<NamedSource<String>>,
    },
    #[error("Expected {name} to be an input")]
    #[diagnostic()]
    NotAnInput {
        name: String,
        #[label("used as input here")]
        at: logos::Span,
        #[label("signal")]
        signal_span: logos::Span,
        #[source_code]
        source_code: Option<NamedSource<String>>,
    },
    #[error("Expected {name} to be an output")]
    #[diagnostic()]
    NotAnOutput {
        name: String,
        #[label("used as output here")]
        at: logos::Span,
        #[label("signal")]
        signal_span: logos::Span,
        #[source_code]
        source_code: Option<NamedSource<String>>,
    },
    #[error("Unknown variable or signal {name}")]
    #[diagnostic()]
    UnknownVariableOrSignal {
        name: String,
        #[label("here")]
        at: logos::Span,
        #[source_code]
        source_code: Option<NamedSource<String>>,
    },
}

/// Error returned from [dig::File::load_test] and [dig::File::load_test_by_name]
#[derive(Debug, Error, Diagnostic)]
pub enum FileLoadError {
    /// Numerical test number out of bounds
    #[error("Trying to load test case #{number}, but file only contains {len} test cases")]
    #[allow(missing_docs)]
    IndexOutOfBounds { number: usize, len: usize },
    /// Could not find test by name
    #[error("Could not find test case \"{0}\"")]
    TestNotFound(String),
    /// Parse error
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseError(#[from] ParseError),
    /// Signals do not match what is expected in the test
    #[error(transparent)]
    #[diagnostic(transparent)]
    SignalError(#[from] SignalError),
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
