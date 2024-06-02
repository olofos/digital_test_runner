use crate::{expr::Expr, lexer::Lexer, lexer::TokenKind};
use anyhow::Result;

fn parse_expression(lex: &mut Lexer) -> Result<Expr> {
    // let Some(peeked) = lex.peek() else {
    //     match lex.next() {
    //         Some(Ok(_)) => unreachable!(),
    //         Some(Err(err)) => anyhow::bail!("Tokenizer error: {err:?}"),
    //         None => anyhow::bail!("Unexpected EOF"),
    //     }
    // };
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
                lex.skip();
                let mut params = vec![];
                while !lex.at(TokenKind::RParen) {
                    let expr = parse_expression(lex)?;
                    params.push(expr);
                    if lex.at(TokenKind::Comma) {
                        lex.skip();
                    } else if !lex.at(TokenKind::RParen) {
                        anyhow::bail!("Expected ',' or ')' but found '{:?}'", lex.peek());
                    }
                }
                Ok(Expr::Func { name, params })
            } else {
                Ok(Expr::Variable(name))
            }
        }
        _ => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval_context::EvalContext;
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
        let expr = parse_expression(&mut lex).unwrap();
        assert_eq!(expr, Expr::Number(num))
    }

    #[rstest]
    #[case("abc", Expr::Variable("abc".into()))]
    #[case("f()", Expr::Func { name: "f".into(), params: vec![] })]
    #[case("f(1,2)", Expr::Func { name: "f".into(), params: vec![Expr::Number(1),Expr::Number(2)] })]
    #[case("f(1,2,)", Expr::Func { name: "f".into(), params: vec![Expr::Number(1),Expr::Number(2)] })]
    fn identifier_works(#[case] input: &str, #[case] expected: Expr) {
        let mut lex = Lexer::new(input);
        let expr = parse_expression(&mut lex).unwrap();
        assert_eq!(expr, expected);
    }
}
