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
//! # fn main() -> miette::Result<()> {
//! # let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
//! # let n = 0;
//! let dig_file = dig::File::open(path).unwrap();
//! let test_case = dig_file.load_test(n).unwrap();
//! # Ok(())
//! # }
//! ```
//! To actually run the test we need a driver which is implementing the [TestDriver](crate::TestDriver) trait.
//! This trait describes the communication between the test runner and the device under test.
//! Once we have a driver we can use the [TestCase::try_iter](crate::TestCase::try_iter) function to obtain an iterator over the rows of the test.
//! Since both the driver and the test itself can fail during the execution of the test, each row is wrapped in  a `Result`.
//! Once we unwrap the row we can examine it to find for example if all output signals matched the expected values.
//! ```
//! # fn main() -> miette::Result<()> {
//! # use digital_test_runner::{dig,TestCase,static_test};
//! # let test_case = dig::File::open(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig")).unwrap().load_test(0).unwrap();
//! # let mut driver = static_test::Driver;
//! for row in test_case.try_iter(&mut driver)? {
//!     let row = row?;
//!     for entry in row.failing_outputs() {
//!         println!("{}: {} expected {} but found {}", row.line, entry.signal.name, entry.expected, entry.output);
//!     }
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ### Implementing a driver
//!
//! The [TestDriver](crate::TestDriver) trait has a single required method, `write_input_and_read_output`,
//! which takes a list of values for the input signals which should be written to the device under test.
//! The driver should then wait for the output signals to settle, read them back and return a list of the read output values.
//!
//! The list of output values should always be given in the same order for each invocation of `write_input_and_read_output`.
//! This allows us to detect some errors, such as missing output values read by the test program, already when the iterator is constructed.
//! To do this, the [TestCase::try_iter](crate::TestCase::try_iter) constructor writes the default value of all inputs and reads the corresponding outputs before constructing the iterator.
//!
//! Since `write_input_and_read_output` performs some form of IO it can potentially fail.
//! Hence, the trait comes with an associated error type `TestDriver::Error`, which should implement [std::error::Error](https://doc.rust-lang.org/stable/core/error/trait.Error.html).
//!
//! The [TestDriver](crate::TestDriver) trait has a second provided method `write_input` which is called when some input should be written to the device under test,
//! but the test does not care about the resulting output. By default this is implemented by calling `write_input_and_read_output` and discarding the output,
//! but a driver can implement its own version of `write_input` as an optimization if reading the output values is costly.
//!
//! ### Static tests
//!
//! For "static" tests, that is, test which do not directly read the value of any output signals,
//! it is possible to run the test without implementing a driver using the [TestCase::try_iter_static](crate::TestCase::try_iter_static) method.
//! Without a driver there is no way of directly communicating with the device under test.
//! In particular, we only know the values of input signals and the expected values for the output signals,
//! but not what the actual output values are.
//! However, if the goal is to translate the test to a different language the input and expected output values is all we need
//! and this simpler API can come in handy.
//! ```
//! # fn main() -> miette::Result<()> {
//! # use digital_test_runner::{dig,TestCase};
//! # let test_case = dig::File::open(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig")).unwrap().load_test(0).unwrap();
//! for row in test_case.try_iter_static()? {
//!     let row = row?;
//!     for input in row.inputs {
//!         print!("{} ", input.value);
//!     }
//!     print!("| ");
//!     for expected in row.expected {
//!         print!("{} ", expected.value);
//!     }
//!     println!("");
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ### Manually loading a test
//!
//! Instead of reading a test from a `dig` file it can be constructed directly from its source code.
//! However, the `dig` file does not only provide us with the source code for the test, but also with a description of the input and output signals.
//! By just parsing the source code we get a [ParsedTestCase](crate::parsed_test_case::ParsedTestCase).
//! To turn this into a full [TestCase](crate::TestCase) we need to provide a list of [Signal](crate::Signal)s
//! to the [ParsedTestCase::with_signals](crate::parsed_test_case::ParsedTestCase::with_signals) method.
//! For an example of this setup see the complete example below.
//!
//! ### Inputs and outputs
//!
//! This crate deals a lot with "inputs" and "outputs". These words are always used with respect to the device under test.
//! Hence, an input is a value that is written from the test runner to the DUT, and an output is read from the DUT by the test runner.
//!
//! ### Values
//!
//! This crate provides several value types:
//! - [InputValue](crate::value::InputValue): A value written to the DUT
//! - [OutputValue](crate::value::OutputValue): A value read from the DUT
//! - [ExpectedValue](crate::value::ExpectedValue): An expected value provided by the test and compared to an output value
//!
//! These values are defined as enums and all have two variants in common: a `Value(i64)` which represents an actual integer value, and a `Z` which represents a high impedance state.
//! Note that this is a simpler value model than what is available in for example Verilog, since either all or none of the bits making up the value are high impedance.
//!
//! Additionally, the [OutputValue](crate::value::OutputValue) and [ExpectedValue](crate::value::ExpectedValue) both have `X` variants.
//! For an expected value, `X` represents that the test does not care about what the output value is.
//! Such an expected value *always* checks as equal to the output value.
//! For an output value `X` represents an unknown value, and can be returned by the driver if a value cannot be read
//! (though if the value can never be read it is probably better to just leave it out of the returned list of output values).
//! Such a value will *never* checks as equal to the expected value, unless the expected value is also `X`.
//!
//! ### Complete example
//!
//! Here is a complete example where a test is loaded from source, with the signals manually defined, as well as a simple driver.
//! In this simple example the driver is not communicating with a device under test, but simply implementing the logic itself.
//! Like this crate, this example uses [miette](https://crates.io/crates/miette) for error handling.
//!
//! For a larger example, including a driver that does communicate with the device under test, see the `examples/` directory of the source code.
//! ```
//! use digital_test_runner::{InputEntry, InputValue, OutputEntry, OutputValue, ParsedTestCase, Signal, TestDriver};
//!
//! // Error type for driver
//! #[derive(Debug)]
//! struct Error(&'static str);
//! impl std::fmt::Display for Error {
//!     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//!         write!(f, "{}", self.0)
//!     }
//! }
//! impl std::error::Error for Error {}
//!
//! // Implement driver
//! struct Driver(Signal);
//!
//! impl TestDriver for Driver {
//!     type Error = Error;
//!
//!     fn write_input_and_read_output(
//!         &mut self,
//!         inputs: &[InputEntry<'_>],
//!     ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
//!         let input = inputs.get(0).ok_or(Error("No input"))?;
//!         let value = input.value.value().ok_or(Error("Unexpected Z"))?;
//!         let value = if value == 0 { 1 } else { 0 };
//!         Ok(vec![OutputEntry {
//!             signal: &self.0,
//!             value: value.into(),
//!         }])
//!     }
//! }
//!
//! fn main() -> miette::Result<()> {
//!     let source = r#"
//!       A B
//!       0 1
//!       1 0
//!     "#;
//!
//!     let parsed_test: ParsedTestCase = source.parse()?;
//!
//!     let signals = vec![Signal::input("A", 1, 0), Signal::output("B", 1)];
//!     let testcase = parsed_test.with_signals(signals)?;
//!
//!     let mut driver = Driver(Signal::output("B", 1));
//!     for row in testcase.try_iter(&mut driver)? {
//!         for output in row?.outputs {
//!             assert!(output.check());
//!         }
//!     }
//!
//!     Ok(())
//! }

//! ```
//!
//! ## Comparison with Digital
//!
//! Here are some known differences in how test cases are interpreted by this crate compared to with what the original Digital program does:
//! - The `program`, `memory` and `init` statements are currently not supported.
//! - If the test directly references the value of an output signal in an expression and the device under test outputs a high impedance `Z` value for that signal this crate will give an error.
//!   Digital instead randomly assigns a high or low value to the signal when evaluating the expression.
//! - This crate is less strict when evaluating expressions for loop bounds.
//!   Digital requires the bound in `loop` and `repeat` statements to be a constant, while this crate accepts any expression.
//!   Note that the bound is evaluated once when entering the loop, not on each iteration.

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
///
/// The main function of interest is `write_input_and_read_output` which should write the provided inputs to the device under test (DUT),
/// wait for the outputs to stabilize, and then read the output values and return a them to the caller.
///
/// We have chosen to use a single function `write_input_and_read_output` for both input and output, instead of more generic `write_input` and `read_output` functions,
/// since knowing that the output is only ever read right after some input was provided can simplify implementing the driver.
/// For example a simple driver can work over a simple serial interface, where it writes the inputs to the DUT (maybe through some sort of test bed) and then get the resulting outputs back.
pub trait TestDriver {
    /// Error returned by the driver
    type Error: std::error::Error + 'static;

    /// Write `input` to the device under test and return the resulting output values
    ///
    /// The list of output values should always be returned in the same order.
    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error>;

    /// Write `input` to the device under test
    ///
    /// By default this simply calls [Self::write_input_and_read_output] and ignores the output.
    /// An optimized driver can directly implement this method to avoid reading the output which might be costly.
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
    /// Run the test dynamically using `driver` for communicating with the device under test
    ///
    /// This function returns an iterator over the resulting data rows.
    ///
    /// Before starting the test all inputs are set to their default values.
    pub fn try_iter<'a, 'b, T: TestDriver>(
        &'a self,
        driver: &'b mut T,
    ) -> Result<DataRowIterator<'a, 'b, T>, IterationError<T::Error>> {
        DataRowIterator::try_new(self, driver)
    }

    #[deprecated = "method renamed to try_iter"]
    /// Run the test dynamically using `driver` for communicating with the device under test
    pub fn run_iter<'a, 'b, T: TestDriver>(
        &'a self,
        driver: &'b mut T,
    ) -> Result<DataRowIterator<'a, 'b, T>, IterationError<T::Error>> {
        self.try_iter(driver)
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
    /// Returns `None` if the signal is an `Output` or a `Virtual` signal.
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
