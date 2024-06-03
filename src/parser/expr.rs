use crate::{
    expr::{BinOp, Expr, UnaryOp},
    lexer::{Lexer, TokenKind},
    parser::binoptree::BinOpTree,
};
use anyhow::Result;

impl From<TokenKind> for UnaryOp {
    fn from(value: TokenKind) -> Self {
        match value {
            TokenKind::Minus => UnaryOp::Minus,
            TokenKind::LogicalNot => UnaryOp::LogicalNot,
            TokenKind::BinaryNot => UnaryOp::BinaryNot,
            _ => unreachable!(),
        }
    }
}

impl TokenKind {
    fn is_binary_op(&self) -> bool {
        matches!(
            self,
            TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Times
                | TokenKind::Divide
                | TokenKind::Reminder
                | TokenKind::LogicalNot
                | TokenKind::BinaryNot
                | TokenKind::Xor
                | TokenKind::And
                | TokenKind::Or
                | TokenKind::ShiftLeft
                | TokenKind::ShiftRight
                | TokenKind::Equal
                | TokenKind::NotEqual
                | TokenKind::LessThanOrEqual
                | TokenKind::GreaterThanOrEqual
                | TokenKind::LessThan
                | TokenKind::GreaterThan
        )
    }
}

impl From<TokenKind> for BinOp {
    fn from(value: TokenKind) -> Self {
        match value {
            TokenKind::Plus => BinOp::Plus,
            TokenKind::Minus => BinOp::Minus,
            TokenKind::Times => BinOp::Times,
            TokenKind::Divide => BinOp::Divide,
            TokenKind::Reminder => BinOp::Reminder,
            TokenKind::Xor => BinOp::Xor,
            TokenKind::And => BinOp::And,
            TokenKind::Or => BinOp::Or,
            TokenKind::ShiftLeft => BinOp::ShiftLeft,
            TokenKind::ShiftRight => BinOp::ShiftRight,
            TokenKind::Equal => BinOp::Equal,
            TokenKind::NotEqual => BinOp::NotEqual,
            TokenKind::LessThanOrEqual => BinOp::LessThanOrEqual,
            TokenKind::GreaterThanOrEqual => BinOp::GreaterThanOrEqual,
            TokenKind::LessThan => BinOp::LessThan,
            TokenKind::GreaterThan => BinOp::GreaterThan,
            _ => unreachable!(),
        }
    }
}

fn parse_expr(lex: &mut Lexer) -> Result<Expr> {
    let first = parse_factor(lex)?;
    let mut tree = BinOpTree::Atom(first);

    while lex.peek().is_binary_op() {
        let new_op = lex.get()?.kind.into();
        let new_expr = parse_factor(lex)?;
        tree.add(new_op, new_expr)
    }

    Ok(tree.into())
}

fn parse_factor(lex: &mut Lexer) -> Result<Expr> {
    match lex.peek() {
        TokenKind::DecInt | TokenKind::HexInt | TokenKind::OctInt | TokenKind::BinInt => {
            let tok = lex.get()?;
            let literal = lex.text(&tok);
            let (literal, radix) = match &tok.kind {
                TokenKind::DecInt => (literal, 10),
                TokenKind::HexInt => (&literal[2..], 16),
                TokenKind::OctInt => (literal, 8),
                TokenKind::BinInt => (&literal[2..], 2),
                _ => unreachable!(),
            };
            let n = i64::from_str_radix(literal, radix).unwrap();
            Ok(Expr::Number(n))
        }
        TokenKind::Ident => {
            let name = {
                let tok = lex.get()?;
                lex.text(&tok).to_string()
            };
            if lex.at(TokenKind::LParen) {
                let mut args = vec![];
                loop {
                    lex.skip();
                    args.push(parse_expr(lex)?);
                    if !lex.at(TokenKind::Comma) {
                        break;
                    }
                }
                lex.consume(TokenKind::RParen)?;
                Ok(Expr::Func { name, args })
            } else {
                Ok(Expr::Variable(name))
            }
        }
        kind @ (TokenKind::Minus | TokenKind::LogicalNot | TokenKind::BinaryNot) => {
            lex.skip();
            let factor = parse_factor(lex)?;
            Ok(Expr::UnaryOp {
                op: UnaryOp::from(kind),
                expr: Box::new(factor),
            })
        }
        TokenKind::LParen => {
            lex.skip();
            let expr = parse_expr(lex)?;
            lex.consume(TokenKind::RParen)?;
            Ok(expr)
        }
        kind => Err(anyhow::anyhow!(
            "Unexpected token {kind:?} when parsing factor"
        )),
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
        let mut lex = Lexer::new(input);
        let expr = parse_factor(&mut lex).unwrap();
        assert_eq!(expr, Expr::Number(num));
        assert_eq!(lex.peek(), TokenKind::Eof);
    }

    #[test]
    fn unary_minus_works() {
        let input = "-2";
        let mut lex = Lexer::new(input);
        let expr = parse_factor(&mut lex).unwrap();
        assert_eq!(
            expr,
            Expr::UnaryOp {
                op: UnaryOp::Minus,
                expr: Box::new(Expr::Number(2))
            }
        );
        assert_eq!(lex.peek(), TokenKind::Eof);
    }

    #[rstest]
    #[case("abc", Expr::Variable("abc".into()))]
    #[case("A1", Expr::Variable("A1".into()))]
    #[case("_", Expr::Variable("_".into()))]
    #[case("_1_a_A", Expr::Variable("_1_a_A".into()))]
    #[case("f(1)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1)] })]
    #[case("f(1,a)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1),Expr::Variable("a".into())] })]
    fn identifier_works(#[case] input: &str, #[case] expected: Expr) {
        let mut lex = Lexer::new(input);
        let expr = parse_factor(&mut lex).unwrap();
        assert_eq!(expr, expected);
        assert_eq!(lex.peek(), TokenKind::Eof);
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
        let mut lex = Lexer::new(input);
        let expr = parse_expr(&mut lex).unwrap();
        assert_eq!(format!("{expr}"), result);
    }
}
