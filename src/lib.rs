use nom::{
    branch::alt,
    bytes::complete::{tag, tag_no_case},
    character::complete::{
        alpha1, alphanumeric1, digit0, hex_digit1, oct_digit0, oct_digit1, one_of,
    },
    combinator::{map, map_res, recognize, value},
    error::ParseError,
    multi::{many0, many1},
    number,
    sequence::{delimited, preceded, separated_pair, tuple},
    IResult, Parser,
};

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum UnaryOp {
    Minus,
    LogicalNot,
    BitNot,
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Number(u64),
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

fn ws<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl Parser<&'a str, O, E>
where
    F: Parser<&'a str, O, E>,
{
    delimited(many0(one_of(" \t")), inner, many0(one_of(" \t")))
}

fn expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn or_expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn xor_expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn and_expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn shift_expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn arithm_expr(i: &str) -> IResult<&str, Expr> {
    todo!()
}

fn term(i: &str) -> IResult<&str, Expr> {
    alt((
        map(separated_pair(term, tag("*"), factor), |(l, r)| {
            Expr::BinOp {
                op: BinOp::Times,
                left: Box::new(l),
                right: Box::new(r),
            }
        }),
        map(separated_pair(term, tag("/"), factor), |(l, r)| {
            Expr::BinOp {
                op: BinOp::Divide,
                left: Box::new(l),
                right: Box::new(r),
            }
        }),
        map(separated_pair(term, tag("%"), factor), |(l, r)| {
            Expr::BinOp {
                op: BinOp::Reminder,
                left: Box::new(l),
                right: Box::new(r),
            }
        }),
        factor,
    ))(i)
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
                u64::from_str_radix(src, 16)
            }),
            map_res(
                preceded(tag_no_case("0b"), recognize(many1(one_of("01")))),
                |src| u64::from_str_radix(src, 2),
            ),
            map_res(recognize(tuple((one_of("123456789"), digit0))), |src| {
                u64::from_str_radix(src, 10)
            }),
            map_res(recognize(tuple((tag("0"), oct_digit0))), |src| {
                u64::from_str_radix(src, 8)
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
    fn number_works(#[case] input: &str, #[case] num: u64) {
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

    // #[rstest]
    // #[case("1*2")]
    #[test]
    // fn term_works(#[case] input: &str) {
    fn term_works() {
        let (_, expr) = term("1/2/3").unwrap();
        dbg!(expr);
    }
}
