use std::{collections::HashMap, fmt::Display};

use crate::{ExpectedValue, OutputValue, Signal};
#[allow(unused_imports)]
use crate::{TestCase, TestDriver};

/// Error returned by [TestCase::run]
#[derive(Debug)]
pub enum RunError<T> {
    /// Forwarded from the [TestDriver::Error]
    Driver(T),
    /// Failed test assertions
    Assertion {
        /// A list of rows with failed assertions
        rows: Vec<FailedRowAssertions>,
    },
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
pub struct FailedRowAssertions {
    /// List of errors
    pub errors: Vec<FailedTestAssertion>,
    /// Line number in test source code
    pub line: usize,
    /// Current value of all variables
    pub vars: HashMap<String, i64>,
}

impl<T> Display for RunError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::Driver(_) => write!(f, "Driver error"),
            RunError::Assertion { rows } => {
                writeln!(f, "Failed assertions:")?;
                for row in rows {
                    writeln!(f, "{row}")?;
                }
                Ok(())
            }
        }
    }
}

impl Display for FailedRowAssertions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Line {}", self.line)?;
        for error in &self.errors {
            writeln!(f, "{error}")?;
        }

        Ok(())
    }
}

impl Display for FailedTestAssertion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: expected {} but found {}",
            self.signal.name, self.expected, self.found
        )
    }
}

impl<T> RunError<T> {
    pub(crate) fn assertion(rows: Vec<FailedRowAssertions>) -> Self {
        Self::Assertion { rows }
    }
}

impl<T: std::error::Error + 'static> std::error::Error for RunError<T> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            RunError::Driver(err) => Some(err),
            RunError::Assertion { .. } => None,
        }
    }
}

impl<T> From<T> for RunError<T> {
    fn from(value: T) -> Self {
        RunError::Driver(value)
    }
}
