mod check;
pub mod dig;
mod eval_context;
mod expr;
mod framed_map;
mod parse;
mod stmt;
mod value;

pub use crate::value::{InputValue, OutputValue, Value};

use check::TestCheck;
use eval_context::EvalContext;
use std::{fmt::Display, marker::PhantomData, str::FromStr};

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

mod private {
    pub trait Sealed {}
}

pub trait TestType: private::Sealed {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticTest;
pub struct DynamicTest;

impl private::Sealed for StaticTest {}
impl private::Sealed for DynamicTest {}
impl TestType for StaticTest {}
impl TestType for DynamicTest {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase<T, S: TestType> {
    stmts: Vec<stmt::Stmt>,
    pub signals: Vec<T>,
    phantom: PhantomData<S>,
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

impl TestCase<String, DynamicTest> {
    pub fn try_from_test(src: &str) -> anyhow::Result<TestCase<String, DynamicTest>> {
        src.parse()
    }

    pub fn with_signals(self, signals: &[Signal]) -> anyhow::Result<TestCase<Signal, DynamicTest>> {
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

        self.stmts.check(&signals)?;

        Ok(TestCase {
            stmts: self.stmts,
            signals,
            phantom: PhantomData,
        })
    }
}

impl TestCase<Signal, DynamicTest> {
    pub fn try_from_dig(
        dig: &crate::dig::DigFile,
        n: usize,
    ) -> anyhow::Result<TestCase<Signal, DynamicTest>> {
        if n >= dig.test_cases.len() {
            anyhow::bail!(
                "Trying to load test case #{n}, but file only contains {} test cases",
                dig.test_cases.len()
            );
        }
        TestCase::try_from_test(&dig.test_cases[n].test_data)?.with_signals(&dig.signals)
    }

    pub fn get_static(self) -> anyhow::Result<TestCase<Signal, StaticTest>> {
        if self.stmts.check(&self.signals)? {
            return Ok(TestCase {
                stmts: self.stmts,
                signals: self.signals,
                phantom: PhantomData,
            });
        }
        anyhow::bail!("Test is not static")
    }
}

impl TestCase<Signal, StaticTest> {
    pub fn iter(&self) -> TestCaseIterator {
        TestCaseIterator {
            iter: crate::stmt::StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
            signals: &self.signals,
            prev: None,
        }
    }
}

impl<'a> IntoIterator for &'a TestCase<Signal, StaticTest> {
    type Item = DataRow<'a>;

    type IntoIter = TestCaseIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromStr for TestCase<String, DynamicTest> {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

impl Signal {
    pub fn output(name: impl Into<String>, bits: u8) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Output,
        }
    }

    pub fn input(name: impl Into<String>, bits: u8, default: InputValue) -> Self {
        Self {
            name: name.into(),
            bits,
            dir: SignalDirection::Input { default },
        }
    }

    pub fn is_output(&self) -> bool {
        matches!(self.dir, SignalDirection::Output)
    }

    pub fn is_input(&self) -> bool {
        matches!(self.dir, SignalDirection::Input { default: _ })
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

impl<T: Display, S: TestType> Display for TestCase<T, S> {
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
        let testcase = TestCase::try_from_test(input)?
            .with_signals(&known_signals)?
            .get_static()?;
        for row in &testcase {
            for entry in row {
                print!("{entry} ");
            }
            println!()
        }

        Ok(())
    }
}
