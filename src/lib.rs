#![deny(missing_debug_implementations, nonstandard_style)]
#![warn(missing_docs, unreachable_pub, rust_2018_idioms, unused_qualifications)]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),"/README.md"))]

/// Load tests from a dig file
pub mod dig;
/// Error types
pub mod errors;
/// Static tests
pub mod static_test;

mod data_row_iterator;
mod eval_context;
mod expr;
mod framed_map;
mod lexer;
mod parser;
mod stmt;
mod value;

use errors::{LoadTestError, SignalError, SignalErrorKind};

pub use crate::data_row_iterator::DataRowIterator;
pub use crate::value::{ExpectedValue, InputValue, OutputValue};

use crate::errors::RuntimeError;
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

/// Represents the direction of a signal
///
/// The direction is specified relative to the device under test, which means that an `Input` signal is an output from the test
/// which is sent to an input port of the DUT. `Input` and `Bidirectional` signals specify a default value which is used if the
/// test itself does not override it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum SignalDirection {
    Input { default: InputValue },
    Output,
    Bidirectional { default: InputValue },
}

/// Represent a input or output signal of the device under test
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    /// Name of the signal
    pub name: String,
    /// Bit width of the signal
    pub bits: usize,
    /// The type of the signal
    pub dir: SignalDirection,
}

/// Represents a test case as obtained directly from the test source code
///
/// To get a full runnable [TestCase], the input and output signals have to be specified using
/// the `with_signals` method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTestCase {
    stmts: Vec<Stmt>,
    /// List of signal names appearing in the test
    pub signals: Vec<String>,
    signal_spans: Vec<logos::Span>,
    expected_inputs: Vec<(String, logos::Span)>,
    read_outputs: Vec<(String, logos::Span)>,
}

/// Represents a fully specified test case
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    stmts: Vec<Stmt>,
    /// List of input and output signals for the device under test
    ///
    /// Not all signals are necessarily involved in the test
    pub signals: Vec<Signal>,
    input_indices: Vec<EntryIndex>,
    expected_indices: Vec<EntryIndex>,
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

impl EntryIndex {
    pub(crate) fn signal_index(&self) -> usize {
        match self {
            EntryIndex::Entry {
                entry_index: _,
                signal_index,
            } => *signal_index,
            EntryIndex::Default { signal_index } => *signal_index,
        }
    }

    pub(crate) fn indexes(&self, entry_index: usize) -> bool {
        match self {
            EntryIndex::Entry {
                entry_index: i,
                signal_index: _,
            } => *i == entry_index,
            EntryIndex::Default { signal_index: _ } => false,
        }
    }
}

impl ParsedTestCase {
    /// Construct a complete test case by supplying a description of the
    /// input and expected signals of the device under test
    #[allow(clippy::result_large_err)]
    pub fn with_signals(self, signals: Vec<Signal>) -> Result<TestCase, SignalError> {
        let mut input_indices: Vec<EntryIndex> = vec![];
        let mut expected_indices = vec![];
        let mut read_outputs = vec![];

        for (signal_index, signal) in signals.iter().enumerate() {
            let index = self
                .signals
                .iter()
                .position(|signal_name| signal_name == &signal.name);

            let index_out = self
                .signals
                .iter()
                .position(|signal_name| signal_name == &(signal.name.clone() + "_out"));

            match signal.dir {
                SignalDirection::Input { .. } | SignalDirection::Bidirectional { .. } => {
                    input_indices.push(match &index {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
                SignalDirection::Output => {}
            }

            match signal.dir {
                SignalDirection::Input { .. } => {}
                SignalDirection::Bidirectional { .. } => {
                    expected_indices.push(match &index_out {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
                SignalDirection::Output => {
                    expected_indices.push(match &index {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
            }
        }

        let missing_signals = self
            .signals
            .iter()
            .enumerate()
            .filter_map(|(entry_index, signal_name)| {
                if !input_indices
                    .iter()
                    .chain(&expected_indices)
                    .any(|entry| entry.indexes(entry_index))
                {
                    Some(signal_name.to_owned())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if !missing_signals.is_empty() {
            let at = missing_signals
                .iter()
                .map(|name| {
                    let i = self
                        .signals
                        .iter()
                        .position(|sig_name| sig_name == name)
                        .unwrap();
                    self.signal_spans[i].clone()
                })
                .collect::<Vec<_>>();
            return Err(SignalError(SignalErrorKind::UnknownSignals {
                signals: missing_signals.join(", "),
                at,
                source_code: None,
            }));
        }

        for (name, at) in self.expected_inputs {
            if !signals.iter().any(|sig| sig.name == name && sig.is_input()) {
                if let Some(i) = self.signals.iter().position(|sig_name| sig_name == &name) {
                    let signal_span = self.signal_spans[i].clone();
                    return Err(SignalError(SignalErrorKind::NotAnInput {
                        name,
                        at,
                        signal_span,
                        source_code: None,
                    }));
                } else {
                    return Err(SignalError(SignalErrorKind::UnknownVariableOrSignal {
                        name,
                        at,
                        source_code: None,
                    }));
                }
            }
        }

        for (name, at) in self.read_outputs {
            if let Some(i) = signals
                .iter()
                .position(|sig| sig.name == name && sig.is_output())
            {
                read_outputs.push(i);
            } else {
                if let Some(i) = self.signals.iter().position(|sig_name| sig_name == &name) {
                    let signal_span = self.signal_spans[i].clone();
                    return Err(SignalError(SignalErrorKind::NotAnOutput {
                        name,
                        at,
                        signal_span,
                        source_code: None,
                    }));
                } else {
                    return Err(SignalError(SignalErrorKind::UnknownVariableOrSignal {
                        name,
                        at,
                        source_code: None,
                    }));
                }
            }
        }

        Ok(TestCase {
            stmts: self.stmts,
            signals,
            input_indices,
            expected_indices,
            read_outputs,
        })
    }
}

impl dig::File {
    /// Load a test by index
    #[allow(clippy::result_large_err)]
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
    #[allow(clippy::result_large_err)]
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
    ) -> Result<DataRowIterator<'a, 'b, T>, RuntimeError<T::Error>> {
        DataRowIterator::try_new(self, driver)
    }
}

impl FromStr for ParsedTestCase {
    type Err = errors::ParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parser::parse_testcase(input)
    }
}

impl Signal {
    /// Construct an `Output` signal
    pub fn output(name: impl Into<String>, bits: usize) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Output,
        }
    }

    /// Construct an `Input` signal
    pub fn input(name: impl Into<String>, bits: usize, default: InputValue) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Input { default },
        }
    }

    /// Is this signal bidirectional?
    pub fn is_bidirectional(&self) -> bool {
        matches!(self.dir, SignalDirection::Bidirectional { default: _ })
    }

    /// Is this test an input (including bidirectional signals)?
    pub fn is_input(&self) -> bool {
        matches!(
            self.dir,
            SignalDirection::Input { .. } | SignalDirection::Bidirectional { .. }
        )
    }

    /// Is this test an output (including bidirectional signals)?
    pub fn is_output(&self) -> bool {
        matches!(
            self.dir,
            SignalDirection::Output | SignalDirection::Bidirectional { .. }
        )
    }

    /// Extract the default value of an `Input` or `Bidirectional` signal.
    ///
    /// Returns `None` if the signal is an `Output`
    pub fn default_value(&self) -> Option<InputValue> {
        match self.dir {
            SignalDirection::Input { default } | SignalDirection::Bidirectional { default } => {
                Some(default)
            }
            SignalDirection::Output => None,
        }
    }
}

impl Display for Signal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.dir {
            SignalDirection::Input { default } => {
                write!(f, "{}({}:{})", self.name, self.bits, default)
            }
            SignalDirection::Output => write!(f, "{}({})", self.name, self.bits),
            SignalDirection::Bidirectional { default } => {
                write!(f, "{}[{}:{}]", self.name, self.bits, default)
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

#[cfg(test)]
mod tests {
    use super::*;
    use static_test::Driver;

    struct TableDriver<'a> {
        outputs: Vec<Vec<OutputEntry<'a>>>,
    }

    #[derive(Debug, thiserror::Error)]
    #[error("Error")]
    struct TableDriverError;

    impl<'a> TestDriver for TableDriver<'a> {
        type Error = TableDriverError;

        fn write_input_and_read_output(
            &mut self,
            _inputs: &[InputEntry<'_>],
        ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
            self.outputs.pop().ok_or(TableDriverError)
        }
    }

    impl<'a> TableDriver<'a> {
        fn new(data: &[Vec<(&'a Signal, i64)>]) -> Self {
            let mut outputs: Vec<Vec<OutputEntry<'a>>> = data
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|(signal, value)| OutputEntry {
                            signal,
                            value: OutputValue::Value(*value),
                        })
                        .collect()
                })
                .collect();
            outputs.reverse();
            Self { outputs }
        }
    }

    #[test]
    fn run_works() -> miette::Result<()> {
        let input = r"
BUS-CLK S         A        B        N ALU-~RESET ALU-AUX   OUT           FLAG DLEN DSUM

let ADD = 0;
let OR  = 1;
let XOR = 2;
let AND = 3;

0       0         0        0        0 0          0         X             X    X    X
0       0         0        0        0 1          0         X             X    X    X

loop (a,2)
loop (b,2)
0       (OR)      (a)      (b)      0 1          0         (a|b)         X    X    X
0       (AND)     (a)      (b)      0 1          0         (a&b)         X    X    X
0       (XOR)     (a)      (b)      0 1          0         (a^b)         X    X    X
0       (ADD)     (a)      (b)      0 1          0         (a+b)         X    X    X
end loop
end loop

";
        let known_inputs = ["BUS-CLK", "S", "A", "B", "N", "ALU-~RESET", "ALU-AUX"]
            .into_iter()
            .map(|name| Signal {
                name: String::from(name),
                bits: 1,
                dir: SignalDirection::Input {
                    default: InputValue::Value(0),
                },
            });
        let known_outputs = ["OUT", "FLAG", "DLEN", "DSUM"]
            .into_iter()
            .map(|name| Signal {
                name: String::from(name),
                bits: 1,
                dir: SignalDirection::Output,
            })
            .collect::<Vec<_>>();
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;
        let mut driver = Driver;
        let it = testcase.run_iter(&mut driver)?;
        for row in it {
            let row = row.unwrap();
            for input in row.inputs {
                print!("{} ", input.value);
            }
            print!("| ");
            for output in row.outputs {
                print!("{} ", output.expected);
            }
            println!()
        }

        Ok(())
    }

    #[test]
    fn can_parse_directional_signal() -> miette::Result<()> {
        let input = r"
A A_out
1 X
Z 1";
        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Bidirectional {
                default: InputValue::Value(0),
            },
        });

        let known_signals = Vec::from_iter(known_inputs);
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let mut driver = Driver;
        let it = testcase.run_iter(&mut driver)?;
        let result: Vec<_> = it.collect::<Result<_, _>>().unwrap();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].inputs[0].signal.name, "A");
        assert_eq!(result[0].outputs[0].signal.name, "A");
        assert_eq!(result[1].inputs[0].signal.name, "A");
        assert_eq!(result[1].outputs[0].signal.name, "A");

        assert_eq!(result[0].inputs[0].value, InputValue::Value(1));
        assert_eq!(result[0].outputs[0].expected, ExpectedValue::X);

        assert_eq!(result[1].inputs[0].value, InputValue::Z);
        assert_eq!(result[1].outputs[0].expected, ExpectedValue::Value(1));

        Ok(())
    }

    #[test]
    fn iter_with_c_works() -> miette::Result<()> {
        let input = r"
    CLK IN OUT
    C 0 0
    ";

        let expanded_input = r"
    CLK IN OUT
    0 0 X
    1 0 X
    0 0 0
    ";
        let known_inputs = ["CLK", "IN"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["OUT"]
            .into_iter()
            .map(|name| Signal {
                name: String::from(name),
                bits: 1,
                dir: SignalDirection::Output,
            })
            .collect::<Vec<_>>();
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

        let mut driver = Driver;
        let rows = testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        for (row, expanded) in rows.into_iter().zip(expanded_rows) {
            assert_eq!(row.inputs, expanded.inputs);
            for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
                assert_eq!(got.expected, expected.expected);
            }
        }

        Ok(())
    }

    #[test]
    fn iter_with_x_works() -> miette::Result<()> {
        let input = r"
    A B OUT
    X X 0
    ";

        let expanded_input = r"
    A B OUT
    0 0 0
    1 0 0
    0 1 0
    1 1 0
    ";
        let known_inputs = ["A", "B"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["OUT"]
            .into_iter()
            .map(|name| Signal {
                name: String::from(name),
                bits: 1,
                dir: SignalDirection::Output,
            })
            .collect::<Vec<_>>();
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

        let mut driver = Driver;
        let rows = testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        for (row, expanded) in rows.into_iter().zip(expanded_rows) {
            assert_eq!(row.inputs, expanded.inputs);
            for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
                assert_eq!(got.expected, expected.expected);
            }
        }
        Ok(())
    }

    #[test]
    fn iter_with_x_and_c_works() -> miette::Result<()> {
        let input = r"
    CLK A OUT
    C X 0
    ";

        let expanded_input = r"
    CLK A OUT
    0 0 X
    1 0 X
    0 0 0
    0 1 X
    1 1 X
    0 1 0
    ";
        let known_inputs = ["CLK", "A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["OUT"]
            .into_iter()
            .map(|name| Signal {
                name: String::from(name),
                bits: 1,
                dir: SignalDirection::Output,
            })
            .collect::<Vec<_>>();
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

        let mut driver = Driver;
        let rows = testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)?
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        for (row, expanded) in rows.into_iter().zip(expanded_rows) {
            assert_eq!(row.inputs, expanded.inputs);
            for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
                assert_eq!(got.expected, expected.expected);
            }
        }

        Ok(())
    }

    #[test]
    fn with_signals_returns_error_for_missing_signal() -> miette::Result<()> {
        let input = r"
    A B C
    0 0 0
    ";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase_result = ParsedTestCase::from_str(input)?.with_signals(known_signals);

        assert!(testcase_result.is_err());

        Ok(())
    }

    #[test]
    fn works_if_not_all_outputs_are_given() -> miette::Result<()> {
        let input = r"
    A B C
    0 0 0
    0 0 0
    ";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let signal = Signal {
            name: String::from("B"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal = &signal;

        let mut driver =
            TableDriver::new(&[vec![(signal, 0)], vec![(signal, 0)], vec![(signal, 0)]]);

        for row in testcase.run_iter(&mut driver)? {
            let _ = row.unwrap();
        }

        Ok(())
    }

    #[test]
    fn gives_error_if_outputs_change_order() -> miette::Result<()> {
        let input = r"
    A B C
    0 0 1
    1 1 0
    ";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let signal_b = Signal {
            name: String::from("B"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_b = &signal_b;

        let signal_c = Signal {
            name: String::from("C"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_c = &signal_c;

        let mut driver = TableDriver::new(&[
            vec![(signal_b, 0), (signal_c, 1)],
            vec![(signal_c, 0), (signal_b, 1)],
        ]);

        let mut it = testcase.run_iter(&mut driver)?;
        assert!(it.next().unwrap().is_err());

        Ok(())
    }

    #[test]
    fn gives_error_if_outputs_changes_length() -> miette::Result<()> {
        let input = r"
    A B C
    0 0 1
    1 1 0
    ";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let signal_b = Signal {
            name: String::from("B"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_b = &signal_b;

        let signal_c = Signal {
            name: String::from("C"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_c = &signal_c;

        let mut driver =
            TableDriver::new(&[vec![(signal_b, 0), (signal_c, 1)], vec![(signal_b, 0)]]);

        let mut it = testcase.run_iter(&mut driver)?;
        assert!(it.next().unwrap().is_err());

        Ok(())
    }

    #[test]
    fn gives_error_if_outputs_changes_length_2() -> miette::Result<()> {
        let input = r"
    A B C
    0 0 1
    1 1 0
    ";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let signal_b = Signal {
            name: String::from("B"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_b = &signal_b;

        let signal_c = Signal {
            name: String::from("C"),
            bits: 1,
            dir: SignalDirection::Output,
        };
        let signal_c = &signal_c;

        let mut driver =
            TableDriver::new(&[vec![(signal_b, 0)], vec![(signal_b, 0), (signal_c, 1)]]);

        let mut it = testcase.run_iter(&mut driver)?;
        assert!(it.next().unwrap().is_err());

        Ok(())
    }

    #[test]
    fn gives_error_for_c_if_not_an_input() -> miette::Result<()> {
        let input = r"
    A B
    0 c
";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let Err(err) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
            panic!("Should have failed")
        };

        assert!(matches!(err.0, SignalErrorKind::NotAnInput { .. }));

        Ok(())
    }

    #[test]
    fn gives_error_for_reading_value_if_not_an_output() -> miette::Result<()> {
        let input = r"
    A B
    0 (A)
";

        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let Err(err) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
            panic!("Should have failed")
        };

        assert!(matches!(err.0, SignalErrorKind::NotAnOutput { .. }));

        Ok(())
    }

    #[test]
    fn test_missing_ouput() -> miette::Result<()> {
        let input = r"
A B C
0 X X
1 X (B)";
        let known_inputs = ["A"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Input {
                default: InputValue::Value(0),
            },
        });
        let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let mut driver = Driver;
        let Err(err) = testcase.run_iter(&mut driver) else {
            panic!("Should have failed")
        };
        assert!(matches!(
            err,
            RuntimeError::Runtime(errors::RuntimeErrorKind::MissingOutputs { .. })
        ));

        Ok(())
    }
}
