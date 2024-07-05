#![deny(missing_debug_implementations, nonstandard_style)]
#![warn(missing_docs, unreachable_pub, rust_2018_idioms)]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),"/README.md"))]

/// Load tests from a dig file
pub mod dig;
/// Error types
pub mod errors;

mod check;
mod eval_context;
mod expr;
mod framed_map;
mod lexer;
mod parser;
mod stmt;
mod value;

use stmt::RowResult;

pub use crate::value::{ExpectedValue, InputValue, OutputValue};

use crate::check::TestCheck;
use crate::errors::{FailedTestAssertion, FailedTestAssertions, RunError};
use crate::eval_context::EvalContext;
use crate::stmt::{DataEntry, Stmt, StmtIterator};
use std::{fmt::Display, str::FromStr};

/// Communicate with the device under test
pub trait TestDriver {
    /// Error returned by the driver
    type Error;

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
}

/// Represents a fully specified test case
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase<'a> {
    stmts: Vec<Stmt>,
    /// List of input and output signals for the device under test
    ///
    /// Not all signals are necessarily involved in the test
    pub signals: &'a [Signal],
    input_indices: Vec<EntryIndex>,
    output_indices: Vec<EntryIndex>,
}

/// An iterator over the data rows of a static test case
#[derive(Debug)]
pub struct TestCaseIterator<'a> {
    iter: StmtIterator<'a>,
    ctx: EvalContext,
    signals: &'a [Signal],
    input_indices: &'a [EntryIndex],
    output_indices: &'a [EntryIndex],
    prev: Option<Vec<DataEntry>>,
    cache: Vec<(RowResult, Option<bool>)>,
}

/// A single row of input values and expected output values
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRow<'a> {
    /// List of input values
    pub inputs: Vec<InputEntry<'a>>,
    /// List of expected output values
    pub outputs: Vec<ExpectedEntry<'a>>,
    /// Line number of the test source code
    pub line: usize,
    update_output: bool,
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

    pub(crate) fn is_entry(&self) -> bool {
        matches!(self, EntryIndex::Entry { .. })
    }
}

impl<'a> DataRow<'a> {
    /// Iterator over those inputs that changed compared to the previous row
    pub fn changed_inputs(&self) -> impl Iterator<Item = &InputEntry<'_>> {
        self.inputs.iter().filter(|entry| entry.changed)
    }

    /// Iterator over the non-trivial expected outputs
    pub fn checked_outputs(&self) -> impl Iterator<Item = &ExpectedEntry<'_>> {
        self.outputs
            .iter()
            .filter(|entry| !matches!(entry.value, ExpectedValue::X))
    }
}

impl<'a> TestCaseIterator<'a> {
    fn entry_is_input(&self, entry_index: usize) -> bool {
        self.input_indices
            .iter()
            .any(|entry| entry.indexes(entry_index))
    }

    fn expand_x(&mut self) {
        loop {
            let (row_result, _) = self.cache.last().unwrap();

            let Some(x_index) =
                row_result
                    .entries
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(i, entry)| {
                        if entry == &DataEntry::X && self.entry_is_input(i) {
                            Some(i)
                        } else {
                            None
                        }
                    })
            else {
                break;
            };
            let (mut row_result, _) = self.cache.pop().unwrap();
            row_result.entries[x_index] = DataEntry::Number(1);
            self.cache.push((row_result.clone(), None));
            row_result.entries[x_index] = DataEntry::Number(0);
            self.cache.push((row_result, None));
        }
    }

    fn expand_c(&mut self) {
        let (mut row_result, _) = self.cache.pop().unwrap();

        let c_indices = row_result
            .entries
            .iter()
            .enumerate()
            .filter_map(|(i, entry)| {
                if entry == &DataEntry::C && self.entry_is_input(i) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if c_indices.is_empty() {
            self.cache.push((row_result, Some(true)));
        } else {
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), Some(true)));
            for entry_index in self.output_indices {
                match entry_index {
                    EntryIndex::Entry {
                        entry_index,
                        signal_index: _,
                    } => row_result.entries[*entry_index] = DataEntry::X,
                    EntryIndex::Default { signal_index: _ } => continue,
                }
            }
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(1);
            }
            self.cache.push((row_result.clone(), Some(false)));
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), Some(false)));
        }
    }

    fn generate_input_entries(
        &self,
        stmt_entries: &[DataEntry],
        changed: &[bool],
    ) -> Vec<InputEntry<'a>> {
        let mut inputs = Vec::with_capacity(self.input_indices.len());
        for index in self.input_indices {
            let entry = match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        DataEntry::Number(n) => InputValue::Value(n & ((1 << signal.bits) - 1)),
                        DataEntry::Z => InputValue::Z,
                        _ => unreachable!(),
                    };
                    let changed = changed[*entry_index];
                    InputEntry {
                        signal,
                        value,
                        changed,
                    }
                }
                EntryIndex::Default { signal_index } => {
                    let signal = &self.signals[*signal_index];
                    InputEntry {
                        signal,
                        value: signal.default_value().unwrap(),
                        changed: false,
                    }
                }
            };
            inputs.push(entry);
        }
        inputs
    }

    fn generate_output_entries(&self, stmt_entries: &[DataEntry]) -> Vec<ExpectedEntry<'a>> {
        let mut outputs = Vec::with_capacity(self.output_indices.len());

        for index in self.output_indices {
            let entry = match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        DataEntry::Number(n) => ExpectedValue::Value(n & ((1 << signal.bits) - 1)),
                        DataEntry::Z => ExpectedValue::Z,
                        DataEntry::X => ExpectedValue::X,
                        _ => unreachable!(),
                    };
                    ExpectedEntry { signal, value }
                }
                EntryIndex::Default { signal_index } => {
                    let signal = &self.signals[*signal_index];
                    ExpectedEntry {
                        signal,
                        value: ExpectedValue::X,
                    }
                }
            };
            outputs.push(entry);
        }
        outputs
    }

    fn check_changed_entries(&self, stmt_entries: &[DataEntry]) -> Vec<bool> {
        if self.prev.is_some() {
            stmt_entries
                .iter()
                .zip(self.prev.as_ref().unwrap())
                .map(|(new, old)| new != old)
                .collect()
        } else {
            vec![true; stmt_entries.len()]
        }
    }
}

impl<'a> Iterator for TestCaseIterator<'a> {
    type Item = DataRow<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cache.is_empty() {
            let row_result = self.iter.next_with_context(&mut self.ctx)?;
            self.cache.push((row_result, None));
        }

        self.expand_x();
        self.expand_c();

        let (row_result, update_output) = self.cache.pop().unwrap();

        let changed = self.check_changed_entries(&row_result.entries);
        self.prev = Some(row_result.entries.clone());

        let inputs = self.generate_input_entries(&row_result.entries, &changed);
        let outputs = self.generate_output_entries(&row_result.entries);

        Some(DataRow {
            inputs,
            outputs,
            line: row_result.line,
            update_output: update_output.unwrap(),
        })
    }
}

impl ParsedTestCase {
    /// Construct a complete test case by supplying a description of the
    /// input and output signals of the device under test
    pub fn with_signals(self, signals: &[Signal]) -> anyhow::Result<TestCase<'_>> {
        let mut input_indices = vec![];
        let mut output_indices = vec![];

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
                    output_indices.push(match &index_out {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
                SignalDirection::Output => {
                    output_indices.push(match &index {
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
                    .chain(&output_indices)
                    .any(|entry| entry.indexes(entry_index))
                {
                    Some(signal_name.to_owned())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if !missing_signals.is_empty() {
            anyhow::bail!(
                "No description provided of signals {}",
                missing_signals.join(", ")
            )
        }

        self.stmts
            .check(&signals, &input_indices, &output_indices)?;

        Ok(TestCase {
            stmts: self.stmts,
            signals,
            input_indices,
            output_indices,
        })
    }
}

impl dig::File {
    /// Load a test by index
    pub fn load_test(&self, n: usize) -> anyhow::Result<TestCase<'_>> {
        if n >= self.test_cases.len() {
            anyhow::bail!(
                "Trying to load test case #{n}, but file only contains {} test cases",
                self.test_cases.len()
            );
        }
        ParsedTestCase::from_str(&self.test_cases[n].source)?.with_signals(&self.signals)
    }

    /// Load a test by name
    pub fn load_test_by_name(&self, name: &str) -> anyhow::Result<TestCase<'_>> {
        if let Some(n) = self
            .test_cases
            .iter()
            .position(|test_case| test_case.name == name)
        {
            self.load_test(n)
        } else {
            anyhow::bail!("Could not find test case \"{name}\"");
        }
    }
}

impl<'a> TestCase<'a> {
    /// Run the test using `driver` to handle input to and output from the device under test.
    pub fn run<T: TestDriver>(&self, driver: &mut T) -> Result<(), RunError<T::Error>> {
        let mut iter = TestCaseIterator {
            iter: StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
            signals: &self.signals,
            input_indices: &self.input_indices,
            output_indices: &self.output_indices,
            prev: None,
            cache: vec![],
        };

        let mut errors = vec![];

        while let Some(row) = iter.next() {
            if row.update_output {
                let outputs = driver.write_input_and_read_output(&row.inputs)?;
                let expected: Vec<_> = row.outputs.iter().map(|entry| entry.value).collect();

                let row_errors = expected
                    .iter()
                    .zip(&outputs)
                    .filter_map(|(e, o)| {
                        if e.check(o.value) {
                            None
                        } else {
                            Some(FailedTestAssertion {
                                expected: *e,
                                found: o.value,
                                signal: o.signal.clone(),
                            })
                        }
                    })
                    .collect::<Vec<_>>();
                if !row_errors.is_empty() {
                    errors.push(FailedTestAssertions {
                        errors: row_errors,
                        line: row.line,
                    });
                }

                iter.ctx.set_outputs(outputs);
            } else {
                driver.write_input(&row.inputs)?;
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(RunError::AssertionError(errors))
        }
    }

    /// Get an iterator over the data rows of the test
    ///
    /// This is only possible if the test is *static*, which means that the test does no depend on the output produced by the device under test.
    /// For a more general *dynamic* test the [TestCase::run] function should be used in combination with a driver implementing the [TestDriver] trait.
    pub fn try_iter(&self) -> anyhow::Result<TestCaseIterator<'_>> {
        if self
            .stmts
            .check(&self.signals, &self.input_indices, &self.output_indices)
            .unwrap()
        {
            Ok(TestCaseIterator {
                iter: StmtIterator::new(&self.stmts),
                ctx: EvalContext::new(),
                signals: &self.signals,
                input_indices: &self.input_indices,
                output_indices: &self.output_indices,
                prev: None,
                cache: vec![],
            })
        } else {
            Err(anyhow::anyhow!("Not a static test"))
        }
    }

    /// Return a `DataRow` where the input values all take their default values
    /// and there are no expectations put on the outputs
    pub fn default_row(&self) -> DataRow<'_> {
        let inputs =
            self.signals
                .iter()
                .filter_map(|signal| match signal.dir {
                    SignalDirection::Input { default }
                    | SignalDirection::Bidirectional { default } => Some(InputEntry {
                        signal,
                        value: default,
                        changed: true,
                    }),
                    SignalDirection::Output => None,
                })
                .collect::<Vec<_>>();

        let outputs = vec![];

        DataRow {
            inputs,
            outputs,
            line: 0,
            update_output: true,
        }
    }
}

impl FromStr for ParsedTestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parser::parse_testcase(input)
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

impl<'a> Display for TestCase<'a> {
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

    #[test]
    fn run_works() -> anyhow::Result<()> {
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
            });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;
        for row in testcase.try_iter()? {
            for input in row.inputs {
                print!("{} ", input.value);
            }
            print!("| ");
            for output in row.outputs {
                print!("{} ", output.value);
            }
            println!()
        }

        Ok(())
    }

    #[test]
    fn can_parse_directional_signal() -> anyhow::Result<()> {
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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;

        let result: Vec<DataRow<'_>> = testcase.try_iter()?.collect();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].inputs[0].signal.name, "A");
        assert_eq!(result[0].outputs[0].signal.name, "A");
        assert_eq!(result[1].inputs[0].signal.name, "A");
        assert_eq!(result[1].outputs[0].signal.name, "A");

        assert_eq!(result[0].inputs[0].value, InputValue::Value(1));
        assert_eq!(result[0].outputs[0].value, ExpectedValue::X);

        assert_eq!(result[1].inputs[0].value, InputValue::Z);
        assert_eq!(result[1].outputs[0].value, ExpectedValue::Value(1));

        Ok(())
    }

    #[test]
    fn iter_with_c_works() -> anyhow::Result<()> {
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
        let known_outputs = ["OUT"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(&known_signals)?;

        let input_rows: Vec<_> = testcase.try_iter()?.map(|r| r.inputs).collect();
        let input_expanded_rows: Vec<_> = expanded_testcase.try_iter()?.map(|r| r.inputs).collect();

        assert_eq!(input_rows, input_expanded_rows);

        let output_rows: Vec<_> = testcase.try_iter()?.map(|r| r.outputs).collect();
        let output_expanded_rows: Vec<_> =
            expanded_testcase.try_iter()?.map(|r| r.outputs).collect();

        assert_eq!(output_rows, output_expanded_rows);

        Ok(())
    }

    #[test]
    fn iter_with_x_works() -> anyhow::Result<()> {
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
        let known_outputs = ["OUT"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(&known_signals)?;

        let input_rows: Vec<_> = testcase.try_iter()?.map(|r| r.inputs).collect();
        let input_expanded_rows: Vec<_> = expanded_testcase.try_iter()?.map(|r| r.inputs).collect();

        assert_eq!(input_rows, input_expanded_rows);

        let output_rows: Vec<_> = testcase.try_iter()?.map(|r| r.outputs).collect();
        let output_expanded_rows: Vec<_> =
            expanded_testcase.try_iter()?.map(|r| r.outputs).collect();

        assert_eq!(output_rows, output_expanded_rows);

        Ok(())
    }

    #[test]
    fn iter_with_x_and_c_works() -> anyhow::Result<()> {
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
        let known_outputs = ["OUT"].into_iter().map(|name| Signal {
            name: String::from(name),
            bits: 1,
            dir: SignalDirection::Output,
        });
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(&known_signals)?;

        let input_rows: Vec<_> = testcase.try_iter()?.map(|r| r.inputs).collect();
        let input_expanded_rows: Vec<_> = expanded_testcase.try_iter()?.map(|r| r.inputs).collect();

        assert_eq!(input_rows, input_expanded_rows);

        let output_rows: Vec<_> = testcase.try_iter()?.map(|r| r.outputs).collect();
        let output_expanded_rows: Vec<_> =
            expanded_testcase.try_iter()?.map(|r| r.outputs).collect();

        assert_eq!(output_rows, output_expanded_rows);

        Ok(())
    }

    #[test]
    fn with_signals_returns_error_for_missing_signal() -> anyhow::Result<()> {
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
        let testcase_result = ParsedTestCase::from_str(input)?.with_signals(&known_signals);

        assert!(testcase_result.is_err());

        Ok(())
    }
}
