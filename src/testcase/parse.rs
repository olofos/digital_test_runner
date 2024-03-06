use std::fmt::Display;

use crate::expr::{BinOp, Expr, UnaryOp};
use crate::testcase::{DataEntry, Stmt, TestCase};

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, tag_no_case},
    character::complete::{alpha1, alphanumeric1, digit0, hex_digit1, newline, oct_digit0, one_of},
    combinator::{eof, map, map_res, opt, recognize, value},
    error::ParseError,
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    Finish, IResult, Parser,
};

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
        let left = std::mem::replace(self, Self::Dummy);
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

fn ws<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl Parser<&'a str, O, E>
where
    F: Parser<&'a str, O, E>,
{
    delimited(many0(one_of(" \t")), inner, many0(one_of(" \t")))
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

fn comment(i: &str) -> IResult<&str, ()> {
    value((), pair(tag("#"), is_not("\r\n")))(i)
}

fn eol(i: &str) -> IResult<&str, ()> {
    value(
        (),
        many1(tuple((many0(one_of(" \t")), opt(comment), newline))),
    )(i)
}

fn stmt(i: &str) -> IResult<&str, Stmt> {
    delimited(
        many0(one_of(" \t")),
        alt((
            let_stmt,
            loop_stmt,
            repeat,
            data_row,
            declare,
            while_stmt,
            reset_random,
        )),
        eol,
    )(i)
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

fn reset_random(i: &str) -> IResult<&str, Stmt> {
    let (i, _) = pair(tag("resetRandom"), ws(tag(";")))(i)?;
    Ok((i, Stmt::ResetRandom))
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

    Ok((
        i,
        TestCase {
            signal_names: signals,
            stmts,
        },
    ))
}

pub fn parse(input: &str) -> Result<TestCase, anyhow::Error> {
    let (_, testcase) = testcase(input).map_err(|e| e.to_owned()).finish()?;
    Ok(testcase)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testcase::EvalContext;
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
        assert_eq!(testcase.signal_names.len(), 11);
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