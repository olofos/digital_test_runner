pub mod dig;
mod eval_context;
mod expr;
mod parse;
mod stmt;
mod value;

pub use crate::value::{InputValue, OutputValue, Value};

use eval_context::EvalContext;
use std::{fmt::Display, str::FromStr};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputSignal<'a> {
    pub name: &'a str,
    pub bits: u8,
    pub default: InputValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputSignal<'a> {
    pub name: &'a str,
    pub bits: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignalDirection {
    Input { default: InputValue },
    Output,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    pub name: String,
    pub bits: u8,
    pub dir: SignalDirection,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase<T> {
    stmts: Vec<stmt::Stmt>,
    pub signals: Vec<T>,
}

#[derive(Debug)]
pub struct TestCaseIterator<'a> {
    iter: crate::stmt::StmtIterator<'a>,
    ctx: EvalContext,
    signals: &'a Vec<Signal>,
    prev: Option<Vec<stmt::DataEntry>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRow<'a> {
    pub entries: Vec<DataEntry<'a, Value>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataEntry<'a, T> {
    pub name: &'a str,
    pub bits: u8,
    pub value: T,
    pub changed: bool,
}

impl<'a> IntoIterator for DataRow<'a> {
    type Item = DataEntry<'a, Value>;

    type IntoIter = std::vec::IntoIter<DataEntry<'a, Value>>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'a DataRow<'b> {
    type Item = &'a DataEntry<'b, Value>;

    type IntoIter = std::slice::Iter<'a, DataEntry<'b, Value>>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

impl<'a> DataRow<'a> {
    pub fn iter(&self) -> std::slice::Iter<'_, DataEntry<'_, Value>> {
        self.entries.iter()
    }

    pub fn inputs(&self) -> impl Iterator<Item = DataEntry<'_, InputValue>> {
        self.entries.iter().filter_map(|entry| match entry.value {
            Value::InputValue(value) => Some(DataEntry {
                name: entry.name,
                bits: entry.bits,
                changed: entry.changed,
                value,
            }),
            Value::OutputValue(_) => None,
        })
    }

    pub fn changed_inputs(&self) -> impl Iterator<Item = DataEntry<'_, InputValue>> {
        self.inputs().filter(|entry| entry.changed)
    }

    pub fn outputs(&self) -> impl Iterator<Item = DataEntry<'_, OutputValue>> {
        self.entries.iter().filter_map(|entry| match entry.value {
            Value::OutputValue(value) => Some(DataEntry {
                name: entry.name,
                bits: entry.bits,
                changed: entry.changed,
                value,
            }),
            Value::InputValue(_) => None,
        })
    }
}

impl<'a> Display for DataEntry<'a, Value> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            Value::InputValue(value) => write!(f, "{value}"),
            Value::OutputValue(value) => write!(f, "{value}"),
        }
    }
}

impl<'a> DataEntry<'a, Value> {
    fn new(entry: stmt::DataEntry, signal: &'a Signal, changed: bool) -> Self {
        let value = match &signal.dir {
            SignalDirection::Input { default: _ } => Value::InputValue(match entry {
                stmt::DataEntry::Number(n) => InputValue::Value(n & ((1 << signal.bits) - 1)),
                stmt::DataEntry::Z => InputValue::Z,
                _ => unreachable!(),
            }),
            SignalDirection::Output => Value::OutputValue(match entry {
                stmt::DataEntry::Number(n) => OutputValue::Value(n & ((1 << signal.bits) - 1)),
                stmt::DataEntry::Z => OutputValue::Z,
                stmt::DataEntry::X => OutputValue::X,
                _ => unreachable!(),
            }),
        };
        Self {
            name: &signal.name,
            bits: signal.bits,
            value,
            changed,
        }
    }

    pub fn is_input(&self) -> bool {
        matches!(self.value, Value::InputValue(_))
    }

    pub fn is_output(&self) -> bool {
        matches!(self.value, Value::OutputValue(_))
    }
}

impl<'a> Iterator for TestCaseIterator<'a> {
    type Item = DataRow<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.prev.is_none() {
            let (default, entries) = self
                .signals
                .iter()
                .map(|signal| {
                    let entry = match &signal.dir {
                        SignalDirection::Input { default } => match default {
                            InputValue::Value(n) => stmt::DataEntry::Number(*n),
                            InputValue::Z => stmt::DataEntry::Z,
                        },

                        &SignalDirection::Output => stmt::DataEntry::X,
                    };
                    (entry.clone(), DataEntry::new(entry, signal, true))
                })
                .unzip();
            self.prev = Some(default);

            return Some(DataRow { entries });
        }
        let stmt_entries = self.iter.next_with_context(&mut self.ctx)?;
        let changed: Vec<_> = stmt_entries
            .iter()
            .zip(self.prev.as_ref().unwrap())
            .map(|(new, old)| new != old)
            .collect();
        self.prev = Some(stmt_entries.clone());
        let entries = stmt_entries
            .into_iter()
            .zip(self.signals)
            .zip(changed)
            .map(|((entry, signal), changed)| DataEntry::new(entry, signal, changed))
            .collect();
        Some(DataRow { entries })
    }
}

impl Display for Signal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.dir {
            SignalDirection::Input { default } => {
                write!(f, "{}({}:{})", self.name, self.bits, default)
            }
            SignalDirection::Output => write!(f, "{}({})", self.name, self.bits),
        }
    }
}

impl<T: Display> Display for TestCase<T> {
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

impl TestCase<String> {
    pub fn try_from_test(src: &str) -> anyhow::Result<TestCase<String>> {
        src.parse()
    }

    pub fn with_signals(self, signals: &[Signal]) -> anyhow::Result<TestCase<Signal>> {
        let signals = self
            .signals
            .into_iter()
            .map(|sig_name| {
                signals
                    .iter()
                    .find(|sig| sig.name == sig_name)
                    .cloned()
                    .ok_or(anyhow::anyhow!("Could not find signal {sig_name}"))
            })
            .collect::<anyhow::Result<Vec<_>>>()?;

        Ok(TestCase {
            stmts: self.stmts,
            signals,
        })
    }
}

impl TestCase<Signal> {
    pub fn try_from_dig(dig: &crate::dig::DigFile, n: usize) -> anyhow::Result<TestCase<Signal>> {
        if n >= dig.test_cases.len() {
            anyhow::bail!(
                "Trying to load test case #{n}, but file only contains {} test cases",
                dig.test_cases.len()
            );
        }
        TestCase::try_from_test(&dig.test_cases[n].test_data)?.with_signals(&dig.signals)
    }

    pub fn iter(&self) -> TestCaseIterator {
        TestCaseIterator {
            iter: crate::stmt::StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
            signals: &self.signals,
            prev: None,
        }
    }
}

impl<'a> IntoIterator for &'a TestCase<Signal> {
    type Item = DataRow<'a>;

    type IntoIter = TestCaseIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromStr for TestCase<String> {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
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
        let testcase = TestCase::try_from_test(input)?.with_signals(&known_signals)?;
        for row in &testcase {
            for entry in row {
                print!("{entry} ");
            }
            println!()
        }

        Ok(())
    }
}
