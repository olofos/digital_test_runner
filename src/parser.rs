use crate::{expr::Expr, lexer::Lexer, lexer::TokenKind};

fn parse_number(lex: &mut Lexer) -> Expr {
    match lex.peek() {
        Some(TokenKind::DecInt)
        | Some(TokenKind::HexInt)
        | Some(TokenKind::OctInt)
        | Some(TokenKind::BinInt) => {
            let tok = lex.next().unwrap().unwrap();
            let literal = lex.text(&tok);
            let (literal, radix) = match &tok.kind {
                TokenKind::DecInt => (literal, 10),
                TokenKind::HexInt => (&literal[2..], 16),
                TokenKind::OctInt => (literal, 8),
                TokenKind::BinInt => (&literal[2..], 2),
                _ => unreachable!(),
            };
            let n = i64::from_str_radix(literal, radix).unwrap();
            Expr::Number(n)
        }
        Some(_) => todo!(),
        None => todo!(),
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
        let expr = parse_number(&mut lex);
        assert_eq!(expr, Expr::Number(num))
    }
}
