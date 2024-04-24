use std::fmt::Display;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum InputValue {
    Value(i64),
    Z,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum OutputValue {
    Value(i64),
    Z,
    X,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Value {
    InputValue(InputValue),
    OutputValue(OutputValue),
}

impl OutputValue {
    pub fn is_x(&self) -> bool {
        matches!(self, OutputValue::X)
    }

    pub fn value(&self) -> Option<i64> {
        match self {
            OutputValue::Value(n) => Some(*n),
            OutputValue::Z | OutputValue::X => None,
        }
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

impl Display for OutputValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputValue::Value(n) => write!(f, "{n}"),
            OutputValue::Z => write!(f, "Z"),
            OutputValue::X => write!(f, "X"),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::InputValue(v) => write!(f, "{v}"),
            Value::OutputValue(v) => write!(f, "{v}"),
        }
    }
}