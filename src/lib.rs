#![deny(missing_debug_implementations, nonstandard_style)]
#![warn(missing_docs, unreachable_pub, rust_2018_idioms, unused_qualifications)]
#![allow(clippy::result_large_err, rustdoc::redundant_explicit_links)]

//! Parse and run tests used in [hnemann's Digital](https://github.com/hneemann/Digital) logic designer and circuit simulator.
//! Tests give a simple description of the inputs and expected resulting outputs of a digital circuit.
//! This crate allows these tests to be reused to test other implementations of the same circuit, either in a different simulator
//! or in hardware.
//!
//! ## Usage
//!
//! The simplest way of loading a test is to load a `.dig` file and then load a particular test by number or by name
//! ```
//! use digital_test_runner::{dig,TestCase};
//!
//! # let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
//! # let n = 0;
//! let dig_file = dig::File::open(path).unwrap();
//! let test_case = dig_file.load_test(n).unwrap();
//! ```
//! To actually run the test we need a driver which is implementing the [TestDriver](crate::TestDriver) trait.
//! This trait describes the communication between the test runner and the device under test.
//! ```
//! # use digital_test_runner::{dig,TestCase,static_test};
//! # let test_case = dig::File::open(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig")).unwrap().load_test(0).unwrap();
//! # let mut driver = static_test::Driver;
//! let mut it = test_case.run_iter(&mut driver).unwrap();
//! ```
//!
//! The [TestDriver](crate::TestDriver) trait has a single required method, `write_input_and_read_output`,
//! which takes a list of values for the input signals and should return a list of output values read from the output signals.
//! Before reading the outputs the driver should wait for the output signals to settle.
//! The list of output values should always be given in the same order for each invocation of `write_input_and_read_output`.
//! There are two reasons for this requirement. It enables some optimisations, but, more importantly,
//! it means that some errors, such as missing output values read by the test program, can be detected already when the iterator is created.
//! To do this, the [TestCase::run_iter](crate::TestCase::run_iter) constructor writes the default value of all inputs and reads the corresponding outputs before returning the iterator.
//!
//! If the goal is to translate the test to a different language, a trivial driver is provided in [static_test::Driver](crate::static_test::Driver).
//! This driver does not provide any output data, but the runner still gives a list of inputs and expected outputs.
//! This only works for simple "static" tests, that is, test which do not directly read the value of any output signals.
//!
//! ## Comparison with Digital
//!
//! Here are some known differences in how test cases are interpreted by this crate compared to with what the original Digital program does:
//! - The `program`, `memory` and `init` statements are currently not supported.
//! - If the test directly references the value of an output signal in an expression and the device under test outputs a high impedence `Z` value for that signal this crate will give an error. Digital instead randomly assigns a high or low value to the signal when evaluating the expression.
//! - This crate is less strict when evaluating expressions for loop bounds. Digital requires the bound in `loop` and `repeat` statements to be a constant, while this crate accepts any expression. Note that the bound is evaluated once when entering the loop, not on each iteration.

/// Load tests from a dig file
pub mod dig;
pub mod errors;
/// Static tests
pub mod static_test;

mod data_row_iterator;
mod eval_context;
mod expr;
mod framed_map;
mod lexer;
mod parsed_test_case;
mod parser;
mod stmt;
mod tests;
mod value;

use errors::LoadTestError;
use expr::Expr;

pub use crate::data_row_iterator::DataRowIterator;
pub use crate::parsed_test_case::ParsedTestCase;
pub use crate::value::{ExpectedValue, InputValue, OutputValue};

use crate::errors::IterationError;
use crate::eval_context::EvalContext;
use crate::stmt::{DataEntry, Stmt, StmtIterator};
use std::{fmt::Display, str::FromStr};

/// Communicate with the device under test
pub trait TestDriver {
    /// Error returned by the driver
    type Error: std::error::Error + 'static;

    /// Write `input` to the device under test and return the resulting output values
    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error>;

    /// Write `input` to the device under test
    ///
    /// By default this simply calls [Self::write_input_and_read_output] and ignores the output.
    /// An optimised driver can directly implement this method to avoid reading the output which might be costly.
    fn write_input(&mut self, inputs: &[InputEntry<'_>]) -> Result<(), Self::Error> {
        self.write_input_and_read_output(inputs).map(|_| ())
    }
}

/// Encapsulates a virtual signal
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirtualExpr {
    expr: Box<Expr>,
}

/// Represents the direction of a signal
///
/// The direction is specified relative to the device under test, which means that an `Input` signal is an output from the test
/// which is sent to an input port of the DUT. `Input` and `Bidirectional` signals specify a default value which is used if the
/// test itself does not override it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum SignalType {
    Input { default: InputValue },
    Output,
    Bidirectional { default: InputValue },
    Virtual { expr: VirtualExpr },
}

/// Represent a input or output signal of the device under test
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    /// Name of the signal
    pub name: String,
    /// Bit width of the signal
    pub bits: usize,
    /// The type of the signal
    pub typ: SignalType,
}

/// Represents a fully specified test case
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    stmts: Vec<Stmt>,
    /// List of input and output signals for the device under test
    ///
    /// Not all signals are necessarily involved in the test
    pub signals: Vec<Signal>,
    /// List of inputs which links signals to test entries
    input_indices: Vec<EntryIndex>,
    /// List of expected values which links signals to test entries
    expected_indices: Vec<EntryIndex>,
    /// Each entry is an index into [Self::signals] and
    /// indicates that that signal is an output from which
    /// the test directly reads the value
    read_outputs: Vec<usize>,
}

/// A single row of input values, output values and expected values
///
/// If the test does not check the output at this line (which happens
/// in the middle of a clock cycle denoted by a `C` in the test source),
/// the `outputs` list will be empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRow<'a> {
    /// List of input values
    pub inputs: Vec<InputEntry<'a>>,
    /// List of output values together with the expected value
    pub outputs: Vec<OutputResultEntry<'a>>,
    /// Line number of the test source code
    pub line: usize,
}

/// An input value sent to a specific signal
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct InputEntry<'a> {
    pub signal: &'a Signal,
    pub value: InputValue,
    /// Did this input value change since the last row?
    pub changed: bool,
}

/// An output value read from a specific signal
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct OutputEntry<'a> {
    pub signal: &'a Signal,
    pub value: OutputValue,
}

/// Represents the expected output value from a specific signal
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct ExpectedEntry<'a> {
    pub signal: &'a Signal,
    pub value: ExpectedValue,
}

/// An output value read from a specific signal and the expected value
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub struct OutputResultEntry<'a> {
    pub signal: &'a Signal,
    pub output: OutputValue,
    pub expected: ExpectedValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EntryIndex {
    Entry {
        entry_index: usize,
        signal_index: usize,
    },
    Default {
        signal_index: usize,
    },
}

impl<'a> OutputResultEntry<'a> {
    /// Does the output value match the expected value?
    pub fn check(&self) -> bool {
        self.expected.check(self.output)
    }

    /// Is the expected value non-trivial?
    pub fn is_checked(&self) -> bool {
        self.expected != ExpectedValue::X
    }
}

impl dig::File {
    /// Load a test by index
    pub fn load_test(&self, n: usize) -> Result<TestCase, LoadTestError> {
        if n >= self.test_cases.len() {
            Err(LoadTestError::IndexOutOfBounds {
                number: n,
                len: self.test_cases.len(),
            })
        } else {
            Ok(ParsedTestCase::from_str(&self.test_cases[n].source)
                .map_err(|err| err.with_source(self.test_cases[n].named_source()))?
                .with_signals(self.signals.clone())
                .map_err(|err| err.with_source(self.test_cases[n].named_source()))?)
        }
    }

    /// Load a test by name
    pub fn load_test_by_name(&self, name: &str) -> Result<TestCase, LoadTestError> {
        if let Some(n) = self
            .test_cases
            .iter()
            .position(|test_case| test_case.name == name)
        {
            self.load_test(n)
        } else {
            Err(LoadTestError::TestNotFound(name.to_string()))
        }
    }
}

impl<'a> DataRow<'a> {
    /// Returns an iterator over data entries that fail their tests
    pub fn failing_outputs(&'a self) -> impl Iterator<Item = &'a OutputResultEntry<'a>> {
        self.outputs.iter().filter(|res| !res.check())
    }
}

impl TestCase {
    /// Run the test dynamically using `driver` for commnicating with the device under test
    ///
    /// This function returns an iterator over the resulting data rows.
    ///
    /// Before starting the test all inputs are set to their default values.
    pub fn run_iter<'a, 'b, T: TestDriver>(
        &'a self,
        driver: &'b mut T,
    ) -> Result<DataRowIterator<'a, 'b, T>, IterationError<T::Error>> {
        DataRowIterator::try_new(self, driver)
    }
}

impl Signal {
    /// Construct an `Output` signal
    pub fn output(name: impl Into<String>, bits: usize) -> Self {
        Self {
            name: name.into(),
            bits,
            typ: SignalType::Output,
        }
    }

    /// Construct an `Input` signal
    pub fn input(name: impl Into<String>, bits: usize, default: impl Into<InputValue>) -> Self {
        Self {
            name: name.into(),
            bits,
            typ: SignalType::Input {
                default: default.into(),
            },
        }
    }

    /// Construct a `Bidirectional` signal
    pub fn bidirectional(
        name: impl Into<String>,
        bits: usize,
        default: impl Into<InputValue>,
    ) -> Self {
        Self {
            name: name.into(),
            bits,
            typ: SignalType::Bidirectional {
                default: default.into(),
            },
        }
    }

    /// Is this signal bidirectional?
    pub fn is_bidirectional(&self) -> bool {
        matches!(self.typ, SignalType::Bidirectional { default: _ })
    }

    /// Is this test an input (including bidirectional signals)?
    pub fn is_input(&self) -> bool {
        matches!(
            self.typ,
            SignalType::Input { .. } | SignalType::Bidirectional { .. }
        )
    }

    /// Is this test an output (including bidirectional signals)?
    pub fn is_output(&self) -> bool {
        matches!(
            self.typ,
            SignalType::Output | SignalType::Bidirectional { .. }
        )
    }

    /// Extract the default value of an `Input` or `Bidirectional` signal.
    ///
    /// Returns `None` if the signal is an `Output`
    pub fn default_value(&self) -> Option<InputValue> {
        match self.typ {
            SignalType::Input { default } | SignalType::Bidirectional { default } => Some(default),
            SignalType::Output | SignalType::Virtual { .. } => None,
        }
    }
}

impl Display for VirtualExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expr)
    }
}

impl Display for Signal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.typ {
            SignalType::Input { default } => {
                write!(f, "{}({}:{})", self.name, self.bits, default)
            }
            SignalType::Output => write!(f, "{}({})", self.name, self.bits),
            SignalType::Bidirectional { default } => {
                write!(f, "{}[{}:{}]", self.name, self.bits, default)
            }
            SignalType::Virtual { expr: value } => {
                write!(f, "{}[{}={}]", self.name, self.bits, value)
            }
        }
    }
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let signal_names = self
            .signals
            .iter()
            .map(|s| format!("{s}"))
            .collect::<Vec<_>>()
            .join(" ");

        writeln!(f, "{signal_names}")?;
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}
