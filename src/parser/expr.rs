use crate::{
    errors::{ParseError, ParseErrorKind},
    expr::{BinOp, Expr, UnaryOp, FUNC_TABLE},
    lexer::TokenKind,
    parser::{binoptree::BinOpTree, Parser},
};

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

impl<'a> Parser<'a> {
    pub(crate) fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let first = self.parse_factor()?;
        let mut tree = BinOpTree::Atom(first);

        while self.peek().is_binary_op() {
            let new_op = self.get()?.kind.into();
            let new_expr = self.parse_factor()?;
            tree.add(new_op, new_expr)
        }

        Ok(tree.into())
    }

    pub(super) fn parse_number(&mut self) -> Result<i64, ParseError> {
        let tok = self.get()?;
        let literal = self.text(&tok);
        let (literal, radix) = match &tok.kind {
            TokenKind::DecInt => (literal, 10),
            TokenKind::HexInt => (&literal[2..], 16),
            TokenKind::OctInt => (literal, 8),
            TokenKind::BinInt => (&literal[2..], 2),
            &kind => {
                return Err(tok.error(ParseErrorKind::ExpectedNumber { kind }));
            }
        };
        let n = i64::from_str_radix(literal, radix).map_err(|err| tok.error(err.into()))?;
        Ok(n)
    }

    fn parse_factor(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            TokenKind::DecInt | TokenKind::HexInt | TokenKind::OctInt | TokenKind::BinInt => {
                let n = self.parse_number()?;
                Ok(Expr::Number(n))
            }
            TokenKind::Ident => {
                let ident_tok = self.get()?;
                let name = self.text(&ident_tok);

                if self.at(TokenKind::LParen) {
                    let Some(func_entry) = FUNC_TABLE.get(name) else {
                        return Err(ident_tok.error(ParseErrorKind::FunctionNotFound {
                            ident: name.to_string(),
                        }));
                    };

                    let mut args = vec![];
                    loop {
                        self.skip();
                        args.push(self.parse_expr()?);
                        if !self.at(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;

                    if args.len() != func_entry.number_of_args {
                        Err(ParseError {
                            kind: ParseErrorKind::WrongNumberOfArguments {
                                expected: func_entry.number_of_args,
                                found: args.len(),
                            },
                            at: ident_tok.span.start..self.peek_span().start,
                            source_code: None,
                        })
                    } else {
                        Ok(Expr::Func {
                            name: name.to_string(),
                            args,
                        })
                    }
                } else {
                    if !self.vars.contains(name) {
                        self.expected_outputs.entry(name).or_insert(ident_tok.span);
                    }
                    Ok(Expr::Variable(name.to_string()))
                }
            }
            kind @ (TokenKind::Minus | TokenKind::LogicalNot | TokenKind::BinaryNot) => {
                self.skip();
                let factor = self.parse_factor()?;
                Ok(Expr::UnaryOp {
                    op: UnaryOp::from(kind),
                    expr: Box::new(factor),
                })
            }
            TokenKind::LParen => {
                self.skip();
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                Ok(expr)
            }
            kind => {
                let tok = self.get()?;
                Err(tok.error(ParseErrorKind::UnexpectedToken { kind }))
            }
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
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_factor().unwrap();
        assert_eq!(expr, Expr::Number(num));
        assert_eq!(parser.peek(), TokenKind::Eof);
    }

    #[test]
    fn unary_minus_works() {
        let input = "-2";
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_factor().unwrap();
        assert_eq!(
            expr,
            Expr::UnaryOp {
                op: UnaryOp::Minus,
                expr: Box::new(Expr::Number(2))
            }
        );
        assert_eq!(parser.peek(), TokenKind::Eof);
    }

    #[rstest]
    #[case("abc", Expr::Variable("abc".into()))]
    #[case("A1", Expr::Variable("A1".into()))]
    #[case("_", Expr::Variable("_".into()))]
    #[case("_1_a_A", Expr::Variable("_1_a_A".into()))]
    #[case("random(1)", Expr::Func { name: "random".into(), args: vec![Expr::Number(1)] })]
    #[case("signExt(1,a)", Expr::Func { name: "signExt".into(), args: vec![Expr::Number(1),Expr::Variable("a".into())] })]
    fn identifier_works(#[case] input: &str, #[case] expected: Expr) {
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_factor().unwrap();
        assert_eq!(expr, expected);
        assert_eq!(parser.peek(), TokenKind::Eof);
    }

    #[rstest]
    #[case("1", "1")]
    #[case("a", "a")]
    #[case("1+2", "(1 + 2)")]
    #[case("1 + 2", "(1 + 2)")]
    #[case("1 + 2*3 + 4", "((1 + (2 * 3)) + 4)")]
    #[case("random(1)", "random(1)")]
    #[case("signExt(1,2)", "signExt(1,2)")]
    #[case("signExt(1 , 2)", "signExt(1,2)")]
    #[case("-1", "-1")]
    #[case("random(1+2)*random(3)", "(random((1 + 2)) * random(3))")]
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
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_expr().unwrap();
        assert_eq!(format!("{expr}"), result);
    }

    #[test]
    fn returns_error_for_unknown_function() {
        let input = "f(1)";
        let mut parser = Parser::new(input, &[]);
        let Err(err) = parser.parse_expr() else {
            panic!("Expected an error, but got none");
        };

        assert_eq!(
            err.kind,
            ParseErrorKind::FunctionNotFound { ident: "f".into() }
        );
    }

    #[test]
    fn returns_error_for_wrong_number_of_arguments() {
        let input = "random(1,2,3)";
        let mut parser = Parser::new(input, &[]);
        let Err(err) = parser.parse_expr() else {
            panic!("Expected an error, but got none");
        };

        assert_eq!(
            err.kind,
            ParseErrorKind::WrongNumberOfArguments {
                expected: 1,
                found: 3
            }
        );
    }
}
