pub mod dig;
mod eval_context;
mod expr;
mod parse;
mod stmt;

use std::str::FromStr;

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

pub struct TestCase {
    pub(crate) signal_names: Vec<String>,
    pub(crate) stmts: Vec<stmt::Stmt>,
}

impl FromStr for TestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

impl TestCase {
    pub fn run(&self) -> Vec<Vec<stmt::DataResult>> {
        let mut ctx = eval_context::EvalContext::new();
        self.stmts
            .iter()
            .map(|stmt| stmt.run(&mut ctx))
            .flatten()
            .collect::<Vec<_>>()
    }
}
