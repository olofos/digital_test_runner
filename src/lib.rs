pub mod dig;
mod eval_context;
mod expr;
mod testcase;

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

pub use testcase::TestCase;
