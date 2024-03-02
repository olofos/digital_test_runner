use rand::{rngs::StdRng, Rng, SeedableRng};
use std::{fmt::Display, mem, str::FromStr};

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, tag_no_case},
    character::complete::{alpha1, alphanumeric1, digit0, hex_digit1, newline, oct_digit0, one_of},
    combinator::{complete, eof, map, map_res, opt, recognize, value},
    error::ParseError,
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    Finish, IResult, Parser,
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
    let (i, (first, rest)) = pair(
        ws(factor),
        many0(pair(
            map_res(
                alt((
                    tag("!="),
                    tag(">="),
                    tag("<="),
                    tag("<<"),
                    tag(">>"),
                    tag("="),
                    tag(">"),
                    tag("<"),
                    tag("|"),
                    tag("^"),
                    tag("&"),
                    tag("+"),
                    tag("-"),
                    tag("*"),
                    tag("/"),
                    tag("%"),
                )),
                |s: &str| s.parse::<BinOp>(),
            ),
            ws(factor),
        )),
    )(i)?;

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
        map(number, |n| Expr::Number(n)),
        map(
            pair(
                identifier,
                delimited(tag("("), separated_list0(tag(","), expr), tag(")")),
            ),
            |(name, params)| Expr::Func { name, params },
        ),
        map(identifier, Expr::Variable),
        delimited(tag("("), expr, tag(")")),
    ))(i)
}

fn number(i: &str) -> IResult<&str, i64> {
    alt((
        map_res(preceded(tag_no_case("0x"), hex_digit1), |src| {
            i64::from_str_radix(src, 16)
        }),
        map_res(
            preceded(tag_no_case("0b"), recognize(many1(one_of("01")))),
            |src| i64::from_str_radix(src, 2),
        ),
        map_res(recognize(pair(one_of("123456789"), digit0)), |src| {
            i64::from_str_radix(src, 10)
        }),
        map_res(recognize(pair(tag("0"), oct_digit0)), |src| {
            i64::from_str_radix(src, 8)
        }),
    ))(i)
}

fn identifier(i: &str) -> IResult<&str, String> {
    let (i, s) = recognize(pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_")))),
    ))(i)?;
    Ok((i, s.to_owned()))
}

impl Expr {
    fn eval(&self, ctx: &mut EvalContext) -> anyhow::Result<i64> {
        match self {
            Self::Number(n) => Ok(*n),
            Self::Variable(name) => ctx
                .get(name)
                .ok_or(anyhow::anyhow!("Variable {name} not found")),
            Self::UnaryOp { op, expr } => {
                let val = expr.eval(ctx)?;
                match op {
                    UnaryOp::BitNot => Ok(!val),
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
            Self::Func { name, params } => match name.as_str() {
                "random" => {
                    if params.len() == 1 {
                        let max = params[0].eval(ctx)?;
                        Ok(ctx.rng.gen_range(1..max))
                    } else {
                        anyhow::bail!("The function 'random' takes one parameter")
                    }
                }
                "ite" => {
                    if params.len() == 3 {
                        let test = params[0].eval(ctx)?;
                        if test == 0 {
                            Ok(params[2].eval(ctx)?)
                        } else {
                            Ok(params[1].eval(ctx)?)
                        }
                    } else {
                        anyhow::bail!("The function 'lte' takes three parameters")
                    }
                }
                "signExt" => anyhow::bail!("The function '{name}' is currently not implemented"),
                _ => anyhow::bail!("Unknown function '{name}'"),
            },
        }
    }
}

#[derive(Debug)]
struct EvalContext {
    values: Vec<(String, i64)>,
    frame_stack: Vec<usize>,
    rng: StdRng,
}

impl EvalContext {
    fn new() -> Self {
        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::from_entropy(),
        }
    }

    fn with_seed(seed: u64) -> Self {
        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::seed_from_u64(seed),
        }
    }

    fn push_frame(&mut self) {
        self.frame_stack.push(self.values.len())
    }

    fn pop_frame(&mut self) {
        let len = self.frame_stack.pop().unwrap_or(0);
        self.values.truncate(len);
    }

    fn set(&mut self, name: &str, value: i64) {
        let frame_start = *self.frame_stack.last().unwrap_or(&0);
        if let Some((_, entry_value)) = self.values[frame_start..]
            .iter_mut()
            .find(|entry| entry.0 == name)
        {
            *entry_value = value;
        } else {
            self.values.push((name.to_owned(), value));
        }
    }

    fn get(&self, name: &str) -> Option<i64> {
        self.values
            .iter()
            .rev()
            .find(|entry| entry.0 == name)
            .map(|entry| entry.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Stmt {
    Let {
        name: String,
        expr: Expr,
    },
    DataRow(Vec<DataEntry>),
    Loop {
        variable: String,
        max: i64,
        stmts: Vec<Stmt>,
    },
}

impl Stmt {
    fn run(&self, ctx: &mut EvalContext) {
        match self {
            Self::Let { name, expr } => {
                let value = expr.eval(ctx).unwrap();
                ctx.set(name, value);
            }
            Self::DataRow(entries) => {
                let data = entries
                    .iter()
                    .map(|entry| entry.run(ctx))
                    .collect::<Vec<_>>()
                    .join(" ");
                println!("{data}");
            }
            Self::Loop {
                variable,
                max,
                stmts,
            } => {
                ctx.push_frame();
                for i in 0..*max {
                    ctx.set(variable, i);
                    for stmt in stmts {
                        stmt.run(ctx);
                    }
                }
                ctx.pop_frame();
            }
        }
    }
}

fn stmt(i: &str) -> IResult<&str, Stmt> {
    delimited(
        many0(one_of(" \t")),
        alt((let_stmt, loop_stmt, repeat, data_row, declare, while_stmt)),
        eol,
    )(i)
}

fn comment(i: &str) -> IResult<&str, ()> {
    value((), pair(tag("#"), is_not("\r\n")))(i)
}

fn eol(i: &str) -> IResult<&str, ()> {
    value(
        (),
        many1(tuple((many0(one_of(" \t")), opt(comment), newline))),
    )(i)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DataEntry {
    Number(i64),
    Expr(Expr),
    Bits { number: u64, expr: Expr },
    X,
    Z,
}

impl DataEntry {
    fn run(&self, ctx: &mut EvalContext) -> String {
        match self {
            Self::Number(n) => format!("{n}"),
            Self::Expr(expr) => format!("{}", expr.eval(ctx).unwrap()),
            Self::Bits { number, expr } => {
                let value = expr.eval(ctx).unwrap();
                (0..*number)
                    .rev()
                    .map(|n| format!("{}", (value >> n) & 1))
                    .collect::<Vec<_>>()
                    .join(" ")
            }
            Self::X => String::from("X"),
            Self::Z => String::from("Z"),
        }
    }
}

fn data_entry(i: &str) -> IResult<&str, DataEntry> {
    alt((
        map(number, DataEntry::Number),
        map(delimited(tag("("), expr, tag(")")), DataEntry::Expr),
        value(DataEntry::X, tag_no_case("x")),
        value(DataEntry::Z, tag_no_case("z")),
        map(
            delimited(
                pair(tag("bits"), ws(tag("("))),
                separated_pair(ws(number), tag(","), expr),
                tag(")"),
            ),
            |(number, expr)| DataEntry::Bits {
                number: number as u64,
                expr,
            },
        ),
    ))(i)
}

fn data_row(i: &str) -> IResult<&str, Stmt> {
    map(
        separated_list1(many1(one_of(" \t")), data_entry),
        Stmt::DataRow,
    )(i)
}

fn let_stmt(i: &str) -> IResult<&str, Stmt> {
    map(
        pair(
            preceded(tag("let"), ws(identifier)),
            delimited(tag("="), expr, tag(";")),
        ),
        |(name, expr)| Stmt::Let { name, expr },
    )(i)
}

fn loop_stmt(i: &str) -> IResult<&str, Stmt> {
    let (i, (variable, max)) = delimited(
        pair(tag("loop"), ws(tag("("))),
        separated_pair(identifier, ws(tag(",")), number),
        pair(ws(tag(")")), eol),
    )(i)?;
    let (i, stmts) = many0(stmt)(i)?;
    let (i, _) = pair(many0(one_of(" \t")), tag("end loop"))(i)?;

    Ok((
        i,
        Stmt::Loop {
            variable,
            max,
            stmts,
        },
    ))
}

fn repeat(i: &str) -> IResult<&str, Stmt> {
    let (i, max) = delimited(pair(tag("repeat"), ws(tag("("))), number, ws(tag(")")))(i)?;
    let (i, stmt) = data_row(i)?;
    Ok((
        i,
        Stmt::Loop {
            variable: String::from("n"),
            max,
            stmts: vec![stmt],
        },
    ))
}

fn declare(i: &str) -> IResult<&str, Stmt> {
    let (i, (name, expr)) = pair(
        preceded(tag("let"), ws(identifier)),
        delimited(tag("="), expr, tag(";")),
    )(i)?;

    let (_i, _name, _expr) = (i, name, expr);

    unimplemented!()
}

fn while_stmt(i: &str) -> IResult<&str, Stmt> {
    let (i, expr) = delimited(
        pair(tag("while"), ws(tag("("))),
        expr,
        pair(ws(tag(")")), eol),
    )(i)?;
    let (i, stmts) = many0(stmt)(i)?;
    let (i, _) = pair(many0(one_of(" \t")), tag("end while"))(i)?;

    let (_i, _expr, _stmts) = (i, expr, stmts);

    unimplemented!()
}

fn header(i: &str) -> IResult<&str, Vec<String>> {
    let (i, _) = many0(eol)(i)?;
    let (i, _) = many0(one_of(" \t"))(i)?;
    let (i, signals) = separated_list1(
        many1(one_of(" \t")),
        map(recognize(is_not(" \r\r\n")), String::from),
    )(i)?;
    let (i, _) = eol(i)?;

    Ok((i, signals))
}

fn testcase(i: &str) -> IResult<&str, TestCase> {
    let (i, signals) = header(i)?;
    let (i, stmts) = many1(stmt)(i)?;
    let (i, _) = pair(many0(eol), eof)(i)?;

    Ok((i, TestCase { signals, stmts }))
}

pub struct TestCase {
    signals: Vec<String>,
    stmts: Vec<Stmt>,
}

impl FromStr for TestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let (_, testcase) = testcase(input).map_err(|e| e.to_owned()).finish()?;
        Ok(testcase)
    }
}

impl TestCase {
    pub fn run(&self) {
        let mut ctx = EvalContext::new();
        for stmt in &self.stmts {
            stmt.run(&mut ctx);
        }
    }
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
        assert_eq!(expr, num)
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
    #[case("f(1,2)", "f(1,2)")]
    #[case("f(1 , 2)", "f(1,2)")]
    #[case("-1", "-1")]
    #[case("f(1+2)*f(3)", "(f((1 + 2)) * f(3))")]
    #[case("1 + 2 * 3 = 4 + 5", "((1 + (2 * 3)) = (4 + 5))")]
    #[case("1*2/3*4", "(((1 * 2) / 3) * 4)")]
    #[case("1=2", "(1 = 2)")]
    #[case("1>2", "(1 > 2)")]
    #[case("1<2", "(1 < 2)")]
    #[case("1>=2", "(1 >= 2)")]
    #[case("1<=2", "(1 <= 2)")]
    #[case("1&2", "(1 & 2)")]
    #[case("1^2", "(1 ^ 2)")]
    #[case("1|2", "(1 | 2)")]
    #[case("1+2", "(1 + 2)")]
    #[case("1-2", "(1 - 2)")]
    #[case("1*2", "(1 * 2)")]
    #[case("1/2", "(1 / 2)")]
    #[case("1%2", "(1 % 2)")]
    fn expr_works(#[case] input: &str, #[case] result: &str) {
        let (i, expr) = expr(input).unwrap();
        assert_eq!(i, "");
        assert_eq!(format!("{expr}"), result);
    }

    #[test]
    fn eval_context_works() {
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.set("a", 4);
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.push_frame();
        ctx.set("a", 5);
        ctx.set("b", 6);
        assert_eq!(ctx.get("a"), Some(5));
        assert_eq!(ctx.get("b"), Some(6));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.pop_frame();
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
    }

    #[rstest]
    #[case("1+2", 3)]
    #[case("1+2+3", 6)]
    #[case("2*3", 6)]
    #[case("1+2+3=2*3", 1)]
    #[case("1+2+3=b*c", 1)]
    fn eval_works(#[case] input: &str, #[case] value: i64) {
        let (i, expr) = expr(input).unwrap();
        assert_eq!(i, "");
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[rstest]
    #[case("7=3", 0)]
    #[case("7!=3", 1)]
    #[case("7<3", 0)]
    #[case("7>3", 1)]
    #[case("7<=3", 0)]
    #[case("7>=3", 1)]
    #[case("7<<3", 56)]
    #[case("7>>3", 0)]
    #[case("7+3", 10)]
    #[case("7-3", 4)]
    #[case("7*3", 21)]
    #[case("7/3", 2)]
    #[case("7%3", 1)]
    fn eval_works_for_binop(#[case] input: &str, #[case] value: i64) {
        let (i, expr) = expr(input).unwrap();
        assert_eq!(i, "");
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[rstest]
    #[case("-3", -3)]
    #[case("~3", !3)]
    #[case("!3", 0)]
    fn eval_works_for_unart_op(#[case] input: &str, #[case] value: i64) {
        let (i, expr) = expr(input).unwrap();
        assert_eq!(i, "");
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[test]
    fn eval_random_works() {
        let (i, expr) = expr("random(10)").unwrap();
        assert_eq!(i, "");
        let mut ctx = EvalContext::with_seed(0);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 1);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 6);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 3);
    }

    #[rstest]
    #[case("ite(0,2,3)", 3)]
    #[case("ite(1,2,3)", 2)]
    fn eval_ite_works(#[case] input: &str, #[case] value: i64) {
        let (i, expr) = expr(input).unwrap();
        assert_eq!(i, "");
        let mut ctx = EvalContext::new();
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[test]
    fn stmt_let_works() {
        let (i, stmt) = let_stmt("let a = 1;").unwrap();
        assert_eq!(i, "");
        assert_eq!(
            stmt,
            Stmt::Let {
                name: String::from("a"),
                expr: Expr::Number(1)
            }
        )
    }

    #[rstest]
    #[case("1", DataEntry::Number(1))]
    #[case("x", DataEntry::X)]
    #[case("X", DataEntry::X)]
    #[case("z", DataEntry::Z)]
    #[case("Z", DataEntry::Z)]
    #[case("(1)", DataEntry::Expr(Expr::Number(1)))]
    #[case("bits(1,2)", DataEntry::Bits { number: 1, expr: Expr::Number(2)})]
    fn data_entry_works(#[case] input: &str, #[case] result: DataEntry) {
        let (i, entry) = data_entry(input).unwrap();
        assert_eq!(i, "");
        assert_eq!(entry, result);
    }

    #[test]
    fn data_row_works() {
        let (i, row) = data_row("1 (a+b) X\tZ\t\tbits(1,3*7)").unwrap();
        assert_eq!(i, "");
        match row {
            Stmt::DataRow(entries) => assert_eq!(entries.len(), 5),
            _ => panic!("Expected a data row"),
        }
    }

    #[test]
    fn can_parse_simple_program() {
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
        let testcase: TestCase = input.parse().unwrap();
        assert_eq!(testcase.signals.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);
    }

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
        let testcase: TestCase = input.parse().unwrap();
        testcase.run();
    }
}
