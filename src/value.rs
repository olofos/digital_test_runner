use std::fmt::{Binary, Display};

/// Represent a single input value
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum InputValue {
    /// A driven signal with a particular value
    Value(i64),
    /// A high-Z signal
    Z,
}

/// Represent a single output value
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum OutputValue {
    /// A driven signal with a particular value
    Value(i64),
    /// A high-Z signal
    Z,
    /// An unknown value
    X,
}

/// Represent an expected output value
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum ExpectedValue {
    /// A driven signal with a particular value
    Value(i64),
    /// A high-Z signal
    Z,
    /// Don't care: match any output value
    X,
}

impl OutputValue {
    /// Check if the output value matches the expected value
    ///
    /// See [ExpectedValue::check]
    pub fn check(&self, other: ExpectedValue) -> bool {
        other.check(*self)
    }
}

impl ExpectedValue {
    /// Check if the output value matches the expected value
    ///
    /// The values are essentially compared for equality,
    /// except an expected value of `X` matches any output value
    pub fn check(&self, other: impl Into<OutputValue>) -> bool {
        let other = other.into();

        match self {
            ExpectedValue::Value(n) => matches!(other, OutputValue::Value(m) if *n == m),
            ExpectedValue::Z => matches!(other, OutputValue::Z),
            ExpectedValue::X => true,
        }
    }
}

impl From<i64> for InputValue {
    fn from(value: i64) -> Self {
        Self::Value(value)
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

impl From<i64> for OutputValue {
    fn from(value: i64) -> Self {
        Self::Value(value)
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

impl Display for ExpectedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpectedValue::Value(n) => write!(f, "{n}"),
            ExpectedValue::Z => write!(f, "Z"),
            ExpectedValue::X => write!(f, "X"),
        }
    }
}

impl Binary for InputValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputValue::Value(n) => Binary::fmt(&n, f),
            InputValue::Z => {
                if let Some(width) = f.width() {
                    write!(f, "{}", "z".repeat(width))
                } else {
                    write!(f, "z")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(ExpectedValue::Z, OutputValue::Z)]
    #[case(ExpectedValue::Value(0), OutputValue::Value(0))]
    #[case(ExpectedValue::Value(1), OutputValue::Value(1))]
    #[case(ExpectedValue::X, OutputValue::Value(0))]
    #[case(ExpectedValue::X, OutputValue::Z)]
    #[case(ExpectedValue::X, OutputValue::X)]
    fn check_returns_true_as_expected(
        #[case] expected: ExpectedValue,
        #[case] output: OutputValue,
    ) {
        assert!(expected.check(output));
        assert!(output.check(expected));
    }

    #[rstest]
    #[case(ExpectedValue::Z, OutputValue::Value(0))]
    #[case(ExpectedValue::Z, OutputValue::Value(1))]
    #[case(ExpectedValue::Value(0), OutputValue::Z)]
    #[case(ExpectedValue::Value(1), OutputValue::Z)]
    #[case(ExpectedValue::Value(0), OutputValue::Value(1))]
    #[case(ExpectedValue::Value(1), OutputValue::Value(0))]
    #[case(ExpectedValue::Z, OutputValue::X)]
    #[case(ExpectedValue::Value(0), OutputValue::X)]
    #[case(ExpectedValue::Value(1), OutputValue::X)]
    fn check_returns_false_as_expected(
        #[case] expected: ExpectedValue,
        #[case] output: OutputValue,
    ) {
        assert!(!expected.check(output));
        assert!(!output.check(expected));
    }
}
