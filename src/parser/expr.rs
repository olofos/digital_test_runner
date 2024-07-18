use crate::{
    errors::{ParseError, ParseErrorKind},
    expr::{BinOp, Expr, UnaryOp},
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

    pub(crate) fn parse_number(&mut self) -> Result<i64, ParseError> {
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
        let n = i64::from_str_radix(literal, radix)
            .map_err(|err| tok.error(ParseErrorKind::NumberParseError(err)))?;
        Ok(n)
    }

    fn parse_factor(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            TokenKind::DecInt | TokenKind::HexInt | TokenKind::OctInt | TokenKind::BinInt => {
                let n = self.parse_number()?;
                Ok(Expr::Number(n))
            }
            TokenKind::Ident => {
                let name = {
                    let tok = self.get()?;
                    self.text(&tok).to_string()
                };
                if self.at(TokenKind::LParen) {
                    let mut args = vec![];
                    loop {
                        self.skip();
                        args.push(self.parse_expr()?);
                        if !self.at(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    Ok(Expr::Func { name, args })
                } else {
                    Ok(Expr::Variable(name))
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
                Err(tok.error(ParseErrorKind::UnexpectedTokenInExpr { kind }))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::eval_context::EvalContext;

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
        let mut parser = Parser::new(input);
        let expr = parser.parse_factor().unwrap();
        assert_eq!(expr, Expr::Number(num));
        assert_eq!(parser.peek(), TokenKind::Eof);
    }

    #[test]
    fn unary_minus_works() {
        let input = "-2";
        let mut parser = Parser::new(input);
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
    #[case("f(1)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1)] })]
    #[case("f(1,a)", Expr::Func { name: "f".into(), args: vec![Expr::Number(1),Expr::Variable("a".into())] })]
    fn identifier_works(#[case] input: &str, #[case] expected: Expr) {
        let mut parser = Parser::new(input);
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
        let mut parser = Parser::new(input);
        let expr = parser.parse_expr().unwrap();
        assert_eq!(format!("{expr}"), result);
    }

    #[rstest]
    #[case("1+2", 3)]
    #[case("1+2+3", 6)]
    #[case("2*3", 6)]
    #[case("1+2+3=2*3", 1)]
    #[case("1+2+3=b*c", 1)]
    fn eval_works(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input);
        let expr = parser.parse_expr().unwrap();
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
        let mut parser = Parser::new(input);
        let expr = parser.parse_expr().unwrap();
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
    fn eval_works_for_unary_op(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[test]
    fn eval_random_works() {
        let mut parser = Parser::new("random(10)");
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::with_seed(0);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 1);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 6);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 3);
    }

    #[rstest]
    #[case("ite(0,2,3)", 3)]
    #[case("ite(1,2,3)", 2)]
    fn eval_ite_works(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }
}
