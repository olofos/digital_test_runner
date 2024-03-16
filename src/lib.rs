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
pub struct TestCase {
    stmts: Vec<stmt::OrderedStmt>,
    inputs: Vec<InputSignal>,
    outputs: Vec<OutputSignal>,
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let input_names = self.inputs.iter().map(|s| s.name.clone());
        let output_names = self.outputs.iter().map(|s| s.name.clone());

        let names = input_names
            .chain(output_names)
            .collect::<Vec<_>>()
            .join(" ");

        writeln!(f, "{names}")?;
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTestCase {
    pub(crate) signal_names: Vec<String>,
    pub(crate) stmts: Vec<stmt::Stmt>,
}

impl FromStr for ParsedTestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

impl Display for ParsedTestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names = self.signal_names.join(" ");

        writeln!(f, "{names}")?;
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

impl TestCase {
    pub fn run(&self) -> Vec<stmt::ResultRow> {
        let mut ctx = eval_context::EvalContext::new();
        self.stmts
            .iter()
            .flat_map(|stmt| stmt.run(&mut ctx))
            .collect::<Vec<_>>()
    }
}

impl ParsedTestCase {
    pub fn try_into_test_case(
        self,
        known_inputs: &[InputSignal],
        known_outputs: &[OutputSignal],
    ) -> anyhow::Result<TestCase> {
        let mut inputs: Vec<InputSignal> = vec![];
        let mut outputs: Vec<OutputSignal> = vec![];

        let mut input_indices: Vec<usize> = vec![];
        let mut output_indices: Vec<usize> = vec![];

        for (i, signal_name) in self.signal_names.into_iter().enumerate() {
            if let Some(input) = known_inputs
                .iter()
                .find(|signal| signal.name == signal_name)
            {
                inputs.push(input.clone());
                input_indices.push(i);
            } else if let Some(output) = known_outputs
                .iter()
                .find(|signal| signal.name == signal_name)
            {
                outputs.push(output.clone());
                output_indices.push(i);
            } else {
                anyhow::bail!("Unknown signal {signal_name}");
            }
        }

        let stmts = stmt::expand_bits(self.stmts);
        let stmts = stmt::expand_input_x(stmts, &input_indices);
        let stmts = stmt::expand_input_c(stmts, &input_indices, &output_indices);
        let stmts = stmt::reorder(stmts, &input_indices, &output_indices);

        Ok(TestCase {
            stmts,
            inputs,
            outputs,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_works() {
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
            .map(|name| InputSignal {
                name: String::from(name),
                bits: 1,
                default: InputValue::Value(0),
            })
            .collect::<Vec<_>>();
        let known_outputs = ["OUT", "FLAG", "DLEN", "DSUM"]
            .into_iter()
            .map(|name| OutputSignal {
                name: String::from(name),
                bits: 1,
            })
            .collect::<Vec<_>>();
        let testcase: ParsedTestCase = input.parse().unwrap();
        let testcase = testcase
            .try_into_test_case(&known_inputs, &known_outputs)
            .unwrap();
        let result = testcase.run();
        for row in result {
            println!("{row}");
        }
    }
}
