use std::{fmt::Display, mem, str::FromStr};

use nom::{
    branch::alt,
    bytes::complete::{tag, tag_no_case},
    character::complete::{alpha1, alphanumeric1, digit0, hex_digit1, oct_digit0, one_of},
    combinator::{map, map_res, recognize},
    error::ParseError,
    multi::{many0, many1},
    sequence::{delimited, preceded, tuple},
    IResult, Parser,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinOp {
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

impl BinOp {
    fn precedence(&self) -> u8 {
        match self {
            Self::Equal => 7,
            Self::NotEqual => 7,
            Self::GreaterThan => 7,
            Self::LessThan => 7,
            Self::GreaterThanOrEqual => 7,
            Self::LessThanOrEqual => 7,
            Self::Or => 6,
            Self::Xor => 5,
            Self::And => 4,
            Self::ShiftLeft => 3,
            Self::ShiftRight => 3,
            Self::Plus => 2,
            Self::Minus => 2,
            Self::Times => 1,
            Self::Divide => 1,
            Self::Reminder => 1,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum UnaryOp {
    Minus,
    LogicalNot,
    BitNot,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Minus => "-",
            Self::LogicalNot => "!",
            Self::BitNot => "~",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
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
        params: Vec<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::Variable(s) => write!(f, "{s}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::UnaryOp { op, expr } => write!(f, "{op}{expr}"),
            Self::Func { name, params } => {
                let params = params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{name}({params})")
            }
        }
    }
}

fn ws<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl Parser<&'a str, O, E>
where
    F: Parser<&'a str, O, E>,
{
    delimited(many0(one_of(" \t")), inner, many0(one_of(" \t")))
}

/// Used to parse strings of binary operators.
/// We construct a separate tree of only the binary operators on the same level, so that we don't recurse into expressions in brackets
#[derive(Debug, Clone)]
enum BinOpTree {
    Atom(Expr),
    BinOp {
        op: BinOp,
        left: Box<BinOpTree>,
        right: Box<BinOpTree>,
    },
    Dummy,
}

impl Display for BinOpTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(expr) => write!(f, "{expr}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::Dummy => write!(f, "DUMMY"),
        }
    }
}

impl BinOpTree {
    fn add(&mut self, new_op: BinOp, new_expr: Expr) {
        if let Self::BinOp { op, left: _, right } = self {
            if new_op.precedence() < op.precedence() {
                right.add(new_op, new_expr);
                return;
            }
        };
        let left = mem::replace(self, Self::Dummy);
        *self = Self::BinOp {
            op: new_op,
            left: Box::new(left),
            right: Box::new(Self::Atom(new_expr)),
        }
    }

    fn to_expr(self) -> Expr {
        match self {
            Self::Atom(expr) => expr,
            Self::BinOp { op, left, right } => Expr::BinOp {
                op,
                left: Box::new(left.to_expr()),
                right: Box::new(right.to_expr()),
            },
            Self::Dummy => unreachable!(),
        }
    }
}

fn expr(i: &str) -> IResult<&str, Expr> {
    let (i, (first, rest)) = tuple((
        ws(factor),
        many0(tuple((
            map_res(
                alt((
                    tag("="),
                    tag("!="),
                    tag(">"),
                    tag("<"),
                    tag(">="),
                    tag("<="),
                    tag("|"),
                    tag("^"),
                    tag("&"),
                    tag("<<"),
                    tag(">>"),
                    tag("+"),
                    tag("-"),
                    tag("*"),
                    tag("/"),
                    tag("%"),
                )),
                |s: &str| s.parse::<BinOp>(),
            ),
            ws(factor),
        ))),
    ))(i)?;

    let mut tree = BinOpTree::Atom(first);
    for (op, expr) in rest {
        tree.add(op, expr);
    }

    Ok((i, tree.to_expr()))
}

fn factor(i: &str) -> IResult<&str, Expr> {
    alt((
        map(preceded(tag("-"), factor), |expr| Expr::UnaryOp {
            op: UnaryOp::Minus,
            expr: Box::new(expr),
        }),
        map(preceded(tag("!"), factor), |expr| Expr::UnaryOp {
            op: UnaryOp::LogicalNot,
            expr: Box::new(expr),
        }),
        map(preceded(tag("~"), factor), |expr| Expr::UnaryOp {
            op: UnaryOp::BitNot,
            expr: Box::new(expr),
        }),
        number,
        map(
            tuple((identifier, delimited(tag("("), many0(expr), tag(")")))),
            |(name, params)| Expr::Func { name, params },
        ),
        map(identifier, Expr::Variable),
        delimited(tag("("), expr, tag(")")),
    ))(i)
}

fn number(i: &str) -> IResult<&str, Expr> {
    map(
        alt((
            map_res(preceded(tag_no_case("0x"), hex_digit1), |src| {
                i64::from_str_radix(src, 16)
            }),
            map_res(
                preceded(tag_no_case("0b"), recognize(many1(one_of("01")))),
                |src| i64::from_str_radix(src, 2),
            ),
            map_res(recognize(tuple((one_of("123456789"), digit0))), |src| {
                i64::from_str_radix(src, 10)
            }),
            map_res(recognize(tuple((tag("0"), oct_digit0))), |src| {
                i64::from_str_radix(src, 8)
            }),
        )),
        |n| Expr::Number(n),
    )(i)
}

fn identifier(i: &str) -> IResult<&str, String> {
    let (i, s) = recognize(tuple((
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_")))),
    )))(i)?;
    Ok((i, s.to_owned()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("1", 1)]
    #[case("1234", 1234)]
    #[case("0", 0)]
    #[case("010", 8)]
    #[case("0xFF", 255)]
    #[case("0Xff", 255)]
    #[case("0b1010", 10)]
    #[case("0B1010", 10)]
    fn number_works(#[case] input: &str, #[case] num: i64) {
        let (_, expr) = number(input).unwrap();
        assert_eq!(expr, Expr::Number(num))
    }

    #[rstest]
    #[case("A")]
    #[case("A1")]
    #[case("_")]
    #[case("_1_a_A")]
    fn identifier_works(#[case] input: &str) {
        let (_, id) = identifier(input).unwrap();
        assert_eq!(id, String::from(input))
    }

    #[rstest]
    #[case("1", "1")]
    #[case("a", "a")]
    #[case("1+2", "(1 + 2)")]
    #[case("1 + 2", "(1 + 2)")]
    #[case("1 + 2*3 + 4", "((1 + (2 * 3)) + 4)")]
    #[case("f(1)", "f(1)")]
    #[case("-1", "-1")]
    #[case("f(1+2)*f(3)", "(f((1 + 2)) * f(3))")]
    #[case("1 + 2 * 3 = 4 + 5", "((1 + (2 * 3)) = (4 + 5))")]
    #[case("1*2/3*4", "(((1 * 2) / 3) * 4)")]
    fn expr_works(#[case] input: &str, #[case] result: &str) {
        let (_, expr) = expr(input).unwrap();
        assert_eq!(format!("{expr}"), result);
    }
}
