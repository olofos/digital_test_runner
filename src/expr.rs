use crate::eval_context::EvalContext;
use std::{fmt::Display, str::FromStr};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    Or,
    Xor,
    And,
    ShiftLeft,
    ShiftRight,
    Plus,
    Minus,
    Times,
    Divide,
    Reminder,
}

impl FromStr for BinOp {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "=" => Ok(Self::Equal),
            "!=" => Ok(Self::NotEqual),
            ">" => Ok(Self::GreaterThan),
            "<" => Ok(Self::LessThan),
            ">=" => Ok(Self::GreaterThanOrEqual),
            "<=" => Ok(Self::LessThanOrEqual),
            "|" => Ok(Self::Or),
            "^" => Ok(Self::Xor),
            "&" => Ok(Self::And),
            "<<" => Ok(Self::ShiftLeft),
            ">>" => Ok(Self::ShiftRight),
            "+" => Ok(Self::Plus),
            "-" => Ok(Self::Minus),
            "*" => Ok(Self::Times),
            "/" => Ok(Self::Divide),
            "%" => Ok(Self::Reminder),
            _ => Err(anyhow::anyhow!("Unknown bin op {}", s)),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Equal => "=",
            Self::NotEqual => "!=",
            Self::GreaterThan => ">",
            Self::LessThan => "<",
            Self::GreaterThanOrEqual => ">=",
            Self::LessThanOrEqual => "<=",
            Self::Or => "|",
            Self::Xor => "^",
            Self::And => "&",
            Self::ShiftLeft => "<<",
            Self::ShiftRight => ">>",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Times => "*",
            Self::Divide => "/",
            Self::Reminder => "%",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOp {
    Minus,
    LogicalNot,
    BinaryNot,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Minus => "-",
            Self::LogicalNot => "!",
            Self::BinaryNot => "~",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Number(i64),
    Variable(String),
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Func {
        name: String,
        args: Vec<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::Variable(s) => write!(f, "{s}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::UnaryOp { op, expr } => write!(f, "{op}{expr}"),
            Self::Func { name, args } => {
                let args = args
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{name}({args})")
            }
        }
    }
}

impl Expr {
    pub fn eval(&self, ctx: &EvalContext) -> anyhow::Result<i64> {
        match self {
            Self::Number(n) => Ok(*n),
            Self::Variable(name) => ctx
                .get(name)
                .ok_or(anyhow::anyhow!("Variable {name} not found")),
            Self::UnaryOp { op, expr } => {
                let val = expr.eval(ctx)?;
                match op {
                    UnaryOp::BinaryNot => Ok(!val),
                    UnaryOp::LogicalNot => Ok(if val == 0 { 1 } else { 0 }),
                    UnaryOp::Minus => Ok(-val),
                }
            }
            Self::BinOp { op, left, right } => {
                let left = left.eval(ctx)?;
                let right = right.eval(ctx)?;
                match op {
                    BinOp::Equal => Ok(if left == right { 1 } else { 0 }),
                    BinOp::NotEqual => Ok(if left != right { 1 } else { 0 }),
                    BinOp::GreaterThan => Ok(if left > right { 1 } else { 0 }),
                    BinOp::LessThan => Ok(if left < right { 1 } else { 0 }),
                    BinOp::GreaterThanOrEqual => Ok(if left >= right { 1 } else { 0 }),
                    BinOp::LessThanOrEqual => Ok(if left <= right { 1 } else { 0 }),
                    BinOp::Or => Ok(left | right),
                    BinOp::Xor => Ok(left ^ right),
                    BinOp::And => Ok(left & right),
                    BinOp::ShiftLeft => Ok(left << right),
                    BinOp::ShiftRight => Ok(left >> right),
                    BinOp::Plus => Ok(left + right),
                    BinOp::Minus => Ok(left - right),
                    BinOp::Times => Ok(left * right),
                    BinOp::Divide => Ok(left / right),
                    BinOp::Reminder => Ok(left % right),
                }
            }
            Self::Func { name, args } => match name.as_str() {
                "random" => {
                    if args.len() == 1 {
                        let max = args[0].eval(ctx)?;
                        Ok(ctx.random(1..max))
                    } else {
                        anyhow::bail!("The function 'random' takes one argument")
                    }
                }
                "ite" => {
                    if args.len() == 3 {
                        let test = args[0].eval(ctx)?;
                        if test == 0 {
                            Ok(args[2].eval(ctx)?)
                        } else {
                            Ok(args[1].eval(ctx)?)
                        }
                    } else {
                        anyhow::bail!("The function 'lte' takes three arguments")
                    }
                }
                "signExt" => anyhow::bail!("The function '{name}' is currently not implemented"),
                _ => anyhow::bail!("Unknown function '{name}'"),
            },
        }
    }
}
