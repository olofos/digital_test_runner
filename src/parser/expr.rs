use crate::{
    expr::{Expr, UnaryOp},
    lexer::{Lexer, TokenKind},
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

fn parse_expr(lex: &mut Lexer) -> Result<Expr> {
    parse_factor(lex)
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
        _ => todo!(),
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
        assert_eq!(expr, Expr::Number(num))
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
        )
    }

    #[rstest]
    #[case("abc", Expr::Variable("abc".into()))]
    #[case("f(1)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1)] })]
    #[case("f(1,a)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1),Expr::Variable("a".into())] })]
    fn identifier_works(#[case] input: &str, #[case] expected: Expr) {
        let mut lex = Lexer::new(input);
        let expr = parse_factor(&mut lex).unwrap();
        assert_eq!(expr, expected);
    }
}
