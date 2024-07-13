#![deny(missing_debug_implementations, nonstandard_style)]
#![warn(missing_docs, unreachable_pub, rust_2018_idioms, unused_qualifications)]
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

use stmt::DataEntries;

pub use crate::value::{ExpectedValue, InputValue, OutputValue};

use crate::check::TestCheck;
use crate::eval_context::EvalContext;
use crate::stmt::{DataEntry, Stmt, StmtIterator};
use std::collections::HashMap;
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
    expected_indices: Vec<EntryIndex>,
}

#[derive(Debug)]
/// An iterator over the test results for a dynamic test
pub struct DataRowIterator<'a, 'b, T> {
    iter: StmtIterator<'a>,
    ctx: EvalContext,
    signals: &'a [Signal],
    input_indices: &'a [EntryIndex],
    expected_indices: &'a [EntryIndex],
    prev: Option<Vec<DataEntry>>,
    cache: Vec<(DataEntries, bool)>,
    driver: &'b mut T,
}

/// A single row of input values and expected output values
#[derive(Debug, Clone, PartialEq, Eq)]
struct TestDataRow<'a> {
    /// List of input values
    inputs: Vec<InputEntry<'a>>,
    /// List of expected output values
    expected: Vec<ExpectedEntry<'a>>,
    /// Line number of the test source code
    line: usize,
    update_output: bool,
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

    pub(crate) fn is_entry(&self) -> bool {
        matches!(self, EntryIndex::Entry { .. })
    }
}

impl<'a> TestDataRow<'a> {
    /// Iterator over those inputs that changed compared to the previous row
    pub fn changed_inputs(&self) -> impl Iterator<Item = &InputEntry<'_>> {
        self.inputs.iter().filter(|entry| entry.changed)
    }

    /// Iterator over the non-trivial expected outputs
    pub fn checked_outputs(&self) -> impl Iterator<Item = &ExpectedEntry<'_>> {
        self.expected
            .iter()
            .filter(|entry| !matches!(entry.value, ExpectedValue::X))
    }
}

impl<'a, 'b, T> DataRowIterator<'a, 'b, T> {
    fn entry_is_input(&self, entry_index: usize) -> bool {
        self.input_indices
            .iter()
            .any(|entry| entry.indexes(entry_index))
    }

    fn expand_x(&mut self) {
        loop {
            let (row_result, check_output) = self
                .cache
                .last()
                .expect("cache should be refilled before calling expand_x");
            let check_output = *check_output;

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
            self.cache.push((row_result.clone(), check_output));
            row_result.entries[x_index] = DataEntry::Number(0);
            self.cache.push((row_result, check_output));
        }
    }

    fn expand_c(&mut self) {
        let (mut row_result, check_output) = self
            .cache
            .pop()
            .expect("cache should be refilled before calling expand_c");

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
            self.cache.push((row_result, check_output));
        } else {
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), true));
            for entry_index in self.expected_indices {
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
            self.cache.push((row_result.clone(), false));
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), false));
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

    fn generate_expected_entries(&self, stmt_entries: &[DataEntry]) -> Vec<ExpectedEntry<'a>> {
        let mut expected = Vec::with_capacity(self.expected_indices.len());

        for index in self.expected_indices {
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
            expected.push(entry);
        }
        expected
    }

    fn check_changed_entries(&self, stmt_entries: &[DataEntry]) -> Vec<bool> {
        if let Some(prev) = &self.prev {
            stmt_entries
                .iter()
                .zip(prev)
                .map(|(new, old)| new != old)
                .collect()
        } else {
            vec![true; stmt_entries.len()]
        }
    }
}

// impl<'a> Iterator for DataRowIterator<'a> {
//     type Item = DataRow<'a>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.cache.is_empty() {
//             let row_result = self.iter.next_with_context(&mut self.ctx).unwrap()?;
//             self.cache.push((row_result, true));
//         }

//         self.expand_x();
//         self.expand_c();

//         let (row_result, update_output) = self.cache.pop().unwrap();

//         let changed = self.check_changed_entries(&row_result.entries);
//         self.prev = Some(row_result.entries.clone());

//         let inputs = self.generate_input_entries(&row_result.entries, &changed);
//         let expected = self.generate_expected_entries(&row_result.entries);

//         Some(DataRow {
//             inputs,
//             expected,
//             line: row_result.line,
//             update_output,
//         })
//     }
// }

impl ParsedTestCase {
    /// Construct a complete test case by supplying a description of the
    /// input and expected signals of the device under test
    pub fn with_signals(self, signals: &[Signal]) -> anyhow::Result<TestCase<'_>> {
        let mut input_indices = vec![];
        let mut expected_indices = vec![];

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
            anyhow::bail!(
                "No description provided of signals {}",
                missing_signals.join(", ")
            )
        }

        self.stmts
            .check(signals, &input_indices, &expected_indices)?;

        Ok(TestCase {
            stmts: self.stmts,
            signals,
            input_indices,
            expected_indices,
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

impl<'a, 'b, T: TestDriver> DataRowIterator<'a, 'b, T> {
    fn next_row(&mut self, row: TestDataRow<'a>) -> Result<DataRow<'a>, T::Error> {
        let outputs = if row.update_output {
            let outputs = self.driver.write_input_and_read_output(&row.inputs)?;
            self.ctx.set_outputs(&outputs);

            row.expected
                .into_iter()
                .zip(outputs)
                .map(|(e, o)| OutputResultEntry {
                    expected: e.value,
                    output: o.value,
                    signal: e.signal,
                })
                .collect()
        } else {
            self.driver.write_input(&row.inputs)?;
            vec![]
        };
        Ok(DataRow {
            inputs: row.inputs,
            outputs,
            line: row.line,
        })
    }

    /// The current value of all variables
    pub fn vars(&self) -> HashMap<String, i64> {
        self.ctx.vars()
    }
}

impl<'a, 'b, T: TestDriver> Iterator for DataRowIterator<'a, 'b, T> {
    type Item = Result<DataRow<'a>, T::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cache.is_empty() {
            let row_result = self.iter.next_with_context(&mut self.ctx).unwrap()?;
            self.cache.push((row_result, true));
        }

        self.expand_x();
        self.expand_c();

        let (row_result, update_output) = self.cache.pop().unwrap();

        let changed = self.check_changed_entries(&row_result.entries);
        self.prev = Some(row_result.entries.clone());

        let inputs = self.generate_input_entries(&row_result.entries, &changed);
        let expected = self.generate_expected_entries(&row_result.entries);

        let row = TestDataRow {
            inputs,
            expected,
            line: row_result.line,
            update_output,
        };

        Some(self.next_row(row))
    }
}

impl<'a> DataRow<'a> {
    /// Returns an iterator over data entries that fail their tests
    pub fn failing_outputs(&'a self) -> impl Iterator<Item = &'a OutputResultEntry<'a>> {
        self.outputs.iter().filter(|res| !res.check())
    }
}

impl<'a> TestCase<'a> {
    /// Run the test dynamically using `driver` for commnicating with the device under test
    ///
    /// This function returns an iterator over the resulting data rows
    pub fn run_iter<'b, T>(&'a self, driver: &'b mut T) -> DataRowIterator<'a, 'b, T> {
        DataRowIterator {
            iter: StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
            signals: self.signals,
            input_indices: &self.input_indices,
            expected_indices: &self.expected_indices,
            prev: None,
            cache: vec![],
            driver,
        }
    }

    /// Return a `DataRow` where the input values all take their default values
    /// and there are no expectations put on the outputs
    pub fn default_row(&self) -> TestDataRow<'_> {
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

        let expected = vec![];

        TestDataRow {
            inputs,
            expected,
            line: 0,
            update_output: true,
        }
    }
}

impl FromStr for ParsedTestCase {
    type Err = anyhow::Error;

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

    struct Driver {
        outputs: Vec<Signal>,
    }
    impl TestDriver for Driver {
        type Error = ();

        fn write_input_and_read_output(
            &mut self,
            _inputs: &[InputEntry<'_>],
        ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
            Ok(self
                .outputs
                .iter()
                .map(|signal| OutputEntry {
                    signal,
                    value: OutputValue::X,
                })
                .collect())
        }
    }

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
            })
            .collect::<Vec<_>>();
        let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(&known_signals)?;
        let mut driver = Driver {
            outputs: known_outputs,
        };
        let it = testcase.run_iter(&mut driver);
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

        let mut driver = Driver {
            outputs: known_signals.clone(),
        };
        let it = testcase.run_iter(&mut driver);
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

        let mut driver = Driver {
            outputs: known_signals.clone(),
        };
        let rows = testcase
            .run_iter(&mut driver)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)
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

        let mut driver = Driver {
            outputs: known_signals.clone(),
        };
        let rows = testcase
            .run_iter(&mut driver)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)
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

        let mut driver = Driver {
            outputs: known_signals.clone(),
        };
        let rows = testcase
            .run_iter(&mut driver)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let expanded_rows: Vec<_> = expanded_testcase
            .run_iter(&mut driver)
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
