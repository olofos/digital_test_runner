mod check;
pub mod dig;
mod eval_context;
mod expr;
mod framed_map;
mod lexer;
mod parser;
mod stmt;
mod value;

pub use crate::value::{InputValue, OutputValue, Value};

use check::TestCheck;
use dig::DigFile;
use eval_context::EvalContext;
use std::{fmt::Display, str::FromStr};

pub trait TestDriver {
    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry],
    ) -> anyhow::Result<Vec<OutputEntry>>;

    fn write_input(&mut self, inputs: &[InputEntry]) -> anyhow::Result<()> {
        let _ = self.write_input_and_read_output(inputs)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignalDirection {
    Input { default: InputValue },
    Output,
    Bidirectional { default: InputValue },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    pub name: String,
    pub bits: usize,
    pub dir: SignalDirection,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTestCase {
    stmts: Vec<stmt::Stmt>,
    pub signals: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    stmts: Vec<stmt::Stmt>,
    pub signals: Vec<Signal>,
    input_indices: Vec<EntryIndex>,
    output_indices: Vec<EntryIndex>,
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

#[derive(Debug)]
pub struct TestCaseIterator<'a> {
    iter: crate::stmt::StmtIterator<'a>,
    ctx: EvalContext,
    signals: &'a [Signal],
    input_indices: &'a [EntryIndex],
    output_indices: &'a [EntryIndex],
    prev: Option<Vec<stmt::DataEntry>>,
    cache: Vec<(Vec<stmt::DataEntry>, bool)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRow<'a> {
    pub inputs: Vec<InputEntry<'a>>,
    pub outputs: Vec<OutputEntry<'a>>,
    update_output: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputEntry<'a> {
    pub signal: &'a Signal,
    pub value: InputValue,
    pub changed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputEntry<'a> {
    pub signal: &'a Signal,
    pub value: OutputValue,
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
    pub fn changed_inputs(&self) -> impl Iterator<Item = &InputEntry> {
        self.inputs.iter().filter(|entry| entry.changed)
    }

    pub fn checked_outputs(&self) -> impl Iterator<Item = &OutputEntry> {
        self.outputs
            .iter()
            .filter(|entry| !matches!(entry.value, OutputValue::X))
    }
}

impl<'a> TestCaseIterator<'a> {
    fn entry_is_input(&self, entry_index: usize) -> bool {
        self.input_indices
            .iter()
            .any(|entry| entry.indexes(entry_index))
    }

    fn entry_is_output(&self, entry_index: usize) -> bool {
        self.output_indices
            .iter()
            .any(|entry| entry.indexes(entry_index))
    }
}

impl<'a> Iterator for TestCaseIterator<'a> {
    type Item = DataRow<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cache.is_empty() {
            let stmt_entries = self.iter.next_with_context(&mut self.ctx)?;

            let x_positions: Vec<usize> = stmt_entries
                .iter()
                .enumerate()
                .filter_map(|(i, entry)| {
                    if entry == &stmt::DataEntry::X && self.entry_is_input(i) {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect();

            let len = x_positions.len();
            if len > 0 {
                for n in (0..(1 << len)).rev() {
                    let mut entries = stmt_entries.clone();
                    for (bit_index, entry_index) in x_positions.iter().enumerate() {
                        entries[*entry_index] = stmt::DataEntry::Number((n >> bit_index) & 1);
                    }
                    self.cache.push((entries, true));
                }
            } else {
                self.cache.push((stmt_entries, true));
            }
        }

        let (mut stmt_entries, mut update_output) = self.cache.pop()?;

        let has_c = stmt_entries
            .iter()
            .enumerate()
            .any(|(i, entry)| entry == &stmt::DataEntry::C && self.entry_is_input(i));

        if has_c {
            let mut entries = stmt_entries.clone();

            for entry in entries.iter_mut() {
                if *entry == stmt::DataEntry::C {
                    *entry = stmt::DataEntry::Number(0);
                }
            }
            self.cache.push((entries, true));

            let mut entries = stmt_entries.clone();

            for (i, entry) in entries.iter_mut().enumerate() {
                if self.entry_is_output(i) {
                    *entry = stmt::DataEntry::X;
                } else if *entry == stmt::DataEntry::C {
                    *entry = stmt::DataEntry::Number(1);
                }
            }
            self.cache.push((entries, false));

            for (i, entry) in stmt_entries.iter_mut().enumerate() {
                if self.entry_is_output(i) {
                    *entry = stmt::DataEntry::X;
                } else if *entry == stmt::DataEntry::C {
                    *entry = stmt::DataEntry::Number(0);
                }
            }

            update_output = false;
        }

        let changed = if self.prev.is_some() {
            stmt_entries
                .iter()
                .zip(self.prev.as_ref().unwrap())
                .map(|(new, old)| new != old)
                .collect()
        } else {
            vec![true; stmt_entries.len()]
        };
        self.prev = Some(stmt_entries.clone());

        let mut inputs = Vec::with_capacity(self.input_indices.len());
        let mut outputs = Vec::with_capacity(self.output_indices.len());

        for index in self.input_indices {
            let entry = match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        stmt::DataEntry::Number(n) => {
                            InputValue::Value(n & ((1 << signal.bits) - 1))
                        }
                        stmt::DataEntry::Z => InputValue::Z,
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

        for index in self.output_indices {
            let entry = match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        stmt::DataEntry::Number(n) => {
                            OutputValue::Value(n & ((1 << signal.bits) - 1))
                        }
                        stmt::DataEntry::Z => OutputValue::Z,
                        stmt::DataEntry::X => OutputValue::X,
                        _ => unreachable!(),
                    };
                    OutputEntry { signal, value }
                }
                EntryIndex::Default { signal_index } => {
                    let signal = &self.signals[*signal_index];
                    OutputEntry {
                        signal,
                        value: OutputValue::X,
                    }
                }
            };
            outputs.push(entry);
        }

        Some(DataRow {
            inputs,
            outputs,
            update_output,
        })
    }
}

impl ParsedTestCase {
    pub fn with_signals(self, signals: Vec<Signal>) -> anyhow::Result<TestCase> {
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

impl DigFile {
    pub fn load_test(&self, n: usize) -> anyhow::Result<TestCase> {
        if n >= self.test_cases.len() {
            anyhow::bail!(
                "Trying to load test case #{n}, but file only contains {} test cases",
                self.test_cases.len()
            );
        }
        ParsedTestCase::from_str(&self.test_cases[n].test_data)?.with_signals(self.signals.clone())
    }
}

impl TestCase {
    pub fn run(&self, driver: &mut impl TestDriver) -> anyhow::Result<()> {
        let mut iter = TestCaseIterator {
            iter: crate::stmt::StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
            signals: &self.signals,
            input_indices: &self.input_indices,
            output_indices: &self.output_indices,
            prev: None,
            cache: vec![],
        };

        while let Some(row) = iter.next() {
            if row.update_output {
                let outputs = driver.write_input_and_read_output(&row.inputs)?;
                let expected: Vec<_> = row.outputs.iter().map(|entry| entry.value).collect();

                expected.iter().zip(&outputs).for_each(|(e, o)| {
                    if !e.check(o.value) {
                        eprintln!("Error: {} != {}", o.value, e);
                    }
                });

                iter.ctx.set_outputs(outputs);
            } else {
                driver.write_input(&row.inputs)?;
            }
        }
        Ok(())
    }

    pub fn try_iter(&self) -> anyhow::Result<TestCaseIterator> {
        if self
            .stmts
            .check(&self.signals, &self.input_indices, &self.output_indices)?
        {
            Ok(TestCaseIterator {
                iter: crate::stmt::StmtIterator::new(&self.stmts),
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

    pub fn default_row(&self) -> DataRow {
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
    pub fn output(name: impl Into<String>, bits: usize) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Output,
        }
    }

    pub fn input(name: impl Into<String>, bits: usize, default: InputValue) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Input { default },
        }
    }

    pub fn is_bidirectional(&self) -> bool {
        matches!(self.dir, SignalDirection::Bidirectional { default: _ })
    }

    pub fn is_input(&self) -> bool {
        matches!(
            self.dir,
            SignalDirection::Input { .. } | SignalDirection::Bidirectional { .. }
        )
    }

    pub fn is_output(&self) -> bool {
        matches!(
            self.dir,
            SignalDirection::Output | SignalDirection::Bidirectional { .. }
        )
    }

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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;
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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

        let result: Vec<DataRow> = testcase.try_iter()?.collect();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].inputs[0].signal.name, "A");
        assert_eq!(result[0].outputs[0].signal.name, "A");
        assert_eq!(result[1].inputs[0].signal.name, "A");
        assert_eq!(result[1].outputs[0].signal.name, "A");

        assert_eq!(result[0].inputs[0].value, InputValue::Value(1));
        assert_eq!(result[0].outputs[0].value, OutputValue::X);

        assert_eq!(result[1].inputs[0].value, InputValue::Z);
        assert_eq!(result[1].outputs[0].value, OutputValue::Value(1));

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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

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
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

        let expanded_testcase =
            ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

        let input_rows: Vec<_> = testcase.try_iter()?.map(|r| r.inputs).collect();
        let input_expanded_rows: Vec<_> = expanded_testcase.try_iter()?.map(|r| r.inputs).collect();

        assert_eq!(input_rows, input_expanded_rows);

        let output_rows: Vec<_> = testcase.try_iter()?.map(|r| r.outputs).collect();
        let output_expanded_rows: Vec<_> =
            expanded_testcase.try_iter()?.map(|r| r.outputs).collect();

        assert_eq!(output_rows, output_expanded_rows);

        Ok(())
    }
}
