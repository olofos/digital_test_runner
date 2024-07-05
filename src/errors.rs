use thiserror::Error;

use crate::{ExpectedValue, OutputValue, Signal};
#[allow(unused_imports)]
use crate::{TestCase, TestDriver};

/// Error returned by [TestCase::run]
#[derive(Error, Debug)]
pub enum RunError<T> {
    /// Forwarded from the [TestDriver::Error]
    #[error("driver error")]
    DriverError(#[from] T),
    /// A list of rows with failed assertions
    #[error("failed assertions")]
    AssertionError(Vec<FailedTestAssertions>),
}

/// Represents a single failed assertion in a test
#[derive(Debug)]
pub struct FailedTestAssertion {
    /// Expected output value
    pub expected: ExpectedValue,
    /// Actual output value
    pub found: OutputValue,
    /// Output signal corresponding to the values
    pub signal: Signal,
}

/// A collection of assertion errors found in a single row of the test
#[derive(Debug)]
pub struct FailedTestAssertions {
    /// List of errors
    pub errors: Vec<FailedTestAssertion>,
    /// Line number in test source code
    pub line: usize,
}
