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
    stmts: Vec<stmt::Stmt>,
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

impl ParsedTestCase {
    pub fn run(&self) -> Vec<Vec<stmt::DataResult>> {
        let mut ctx = eval_context::EvalContext::new();
        self.stmts
            .iter()
            .flat_map(|stmt| stmt.run(&mut ctx))
            .collect::<Vec<_>>()
    }

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
        let stmts = stmt::reorder(stmts, &input_indices, &output_indices);

        Ok(TestCase {
            stmts,
            inputs,
            outputs,
        })
    }
}
