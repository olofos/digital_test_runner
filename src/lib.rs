pub mod dig;
mod eval_context;
mod expr;
mod parse;
mod stmt;

use std::{fmt::Display, str::FromStr};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum InputValue {
    Value(i64),
    Z,
    // Expr(expr::Expr),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum OutputValue {
    Value(i64),
    Z,
    X,
    // Expr(expr::Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputSignal {
    pub name: String,
    pub bits: u8,
    pub default: InputValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputSignal {
    pub name: String,
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
}

impl<'a> Iterator for TestCaseIterator<'a> {
    type Item = Vec<DataEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.iter.next_with_context(&mut self.ctx)?;
        Some(value)
    }
}

impl Display for InputValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputValue::Value(n) => write!(f, "{n}"),
            InputValue::Z => write!(f, "Z"),
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
        }
    }
}

impl<'a> IntoIterator for &'a TestCase<Signal> {
    type Item = Vec<DataEntry>;

    type IntoIter = TestCaseIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        TestCaseIterator {
            iter: crate::stmt::StmtIterator::new(&self.stmts),
            ctx: EvalContext::new(),
        }
    }
}

impl FromStr for TestCase<String> {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

// impl TestCase {
//     pub fn run(&self) -> Vec<stmt::ResultRow> {
//         let mut ctx = eval_context::EvalContext::new();
//         self.stmts
//             .iter()
//             .flat_map(|stmt| stmt.run(&mut ctx))
//             .collect::<Vec<_>>()
//     }
// }

use eval_context::EvalContext;
use stmt::DataEntry;
pub use stmt::DataResult;

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
