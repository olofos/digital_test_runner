use crate::{
    errors::{ParseError, ParseErrorKind},
    lexer::TokenKind,
    parser::Parser,
    stmt::{DataEntry, Stmt},
};

impl<'a> Parser<'a> {
    pub(crate) fn parse_stmt_block(
        &mut self,
        end_token: Option<TokenKind>,
    ) -> Result<Vec<Stmt>, ParseError> {
        let mut block = vec![];

        loop {
            match self.peek() {
                TokenKind::LParen
                | TokenKind::Bits
                | TokenKind::Ident
                | TokenKind::DecInt
                | TokenKind::HexInt
                | TokenKind::BinInt
                | TokenKind::OctInt => {
                    let data = self.parse_data_row()?;

                    block.push(Stmt::DataRow {
                        data,
                        line: self.line,
                    });
                }

                TokenKind::Loop => {
                    self.skip();
                    self.expect(TokenKind::LParen)?;
                    let variable = {
                        let token = self.expect(TokenKind::Ident)?;
                        self.text(&token).to_string()
                    };
                    self.expect(TokenKind::Comma)?;
                    let max = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    self.expect(TokenKind::Eol)?;
                    let inner = self.parse_stmt_block(Some(TokenKind::Loop))?;

                    block.push(Stmt::Loop {
                        variable,
                        max,
                        inner,
                    });
                }
                TokenKind::Repeat => {
                    self.skip();
                    self.expect(TokenKind::LParen)?;
                    let max = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    let data = self.parse_data_row()?;
                    let stmt = Stmt::DataRow {
                        data,
                        line: self.line,
                    };
                    block.push(Stmt::Loop {
                        variable: "n".into(),
                        max,
                        inner: vec![stmt],
                    });
                }
                TokenKind::Let => {
                    self.skip();
                    let name = {
                        let token = self.expect(TokenKind::Ident)?;
                        self.text(&token).to_string()
                    };
                    self.expect(TokenKind::Equal)?;
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::Semi)?;
                    block.push(Stmt::Let { name, expr });
                }
                TokenKind::ResetRandom => {
                    self.skip();
                    self.expect(TokenKind::Semi)?;
                    block.push(Stmt::ResetRandom);
                }
                TokenKind::While => {
                    self.skip();
                    self.expect(TokenKind::LParen)?;
                    let condition = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    self.expect(TokenKind::Eol)?;
                    let inner = self.parse_stmt_block(Some(TokenKind::While))?;
                    block.push(Stmt::While { condition, inner });
                }
                TokenKind::Declare => todo!(),
                TokenKind::Program => todo!(),
                TokenKind::Init => todo!(),
                TokenKind::Memory => todo!(),
                TokenKind::Def => todo!(),
                TokenKind::Call => todo!(),

                TokenKind::End => {
                    if let Some(kind) = end_token {
                        self.skip();
                        self.expect(kind)?;
                        break;
                    } else {
                        let tok = self.get()?;
                        return Err(tok.error(ParseErrorKind::UnexpectedEndAtTopLevel));
                    }
                }

                TokenKind::Eof => {
                    let tok = self.get()?;
                    if end_token.is_some() {
                        return Err(tok.error(ParseErrorKind::UnexpectedEof));
                    }
                    break;
                }
                TokenKind::Eol => {}
                _ => {
                    Err(self.get()?.error(ParseErrorKind::UnknownToken))?;
                }
            }
            if self.at(TokenKind::Eof) {
                break;
            } else if self.at(TokenKind::Eol) {
                self.skip();
            } else {
                let tok = self.get()?;
                return Err(tok.error(ParseErrorKind::ExpectedNewLine));
            }
        }
        Ok(block)
    }

    fn parse_data_row(&mut self) -> Result<Vec<DataEntry>, ParseError> {
        let mut data = vec![];
        let mut signal_index = 0;
        let row_start = self.peek_span().start;

        loop {
            match self.peek() {
                TokenKind::LParen => {
                    self.skip();
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    data.push(DataEntry::Expr(expr));
                    signal_index += 1;
                }
                TokenKind::Bits => {
                    self.skip();
                    self.expect(TokenKind::LParen)?;
                    let number = {
                        let at = self.peek_span();
                        let n = self.parse_number()?;
                        if n > 64 {
                            return Err(ParseError {
                                kind: ParseErrorKind::TooManyBits,
                                at,
                            });
                        }
                        n as u8
                    };
                    self.expect(TokenKind::Comma)?;
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    data.push(DataEntry::Bits { number, expr });
                    signal_index += number as usize;
                }
                TokenKind::Ident => {
                    let token = self.get()?;
                    match self.text(&token) {
                        "c" | "C" => {
                            self.expected_inputs
                                .entry(&self.signals[signal_index])
                                .or_insert(token.span);
                            data.push(DataEntry::C);
                        }
                        "x" | "X" => data.push(DataEntry::X),
                        "z" | "Z" => data.push(DataEntry::Z),
                        ident => {
                            return Err(token.error(ParseErrorKind::ExpectedCXZ {
                                ident: ident.to_string(),
                            }))
                        }
                    }
                    signal_index += 1;
                }
                TokenKind::DecInt | TokenKind::HexInt | TokenKind::BinInt | TokenKind::OctInt => {
                    let n = self.parse_number()?;
                    data.push(DataEntry::Number(n));
                    signal_index += 1;
                }
                TokenKind::Eol | TokenKind::Eof => break,
                kind => {
                    let tok = self.get()?;
                    return Err(tok.error(ParseErrorKind::UnexpectedToken { kind }));
                }
            }
        }
        let row_end = self.peek_span().start;

        if signal_index != self.signals.len() {
            return Err(ParseError {
                kind: ParseErrorKind::DataRowWithWrongNumberOfSignals {
                    expected: self.signals.len(),
                    found: signal_index,
                },
                at: row_start..row_end,
            });
        }

        Ok(data)
    }
}

#[cfg(test)]
mod test {
    use crate::expr::Expr;
    use crate::parser::Parser;
    use crate::stmt::Stmt;

    #[test]
    fn can_parse_let_stmt() {
        let input = "let a = 1;\n";
        let mut parser = Parser::new(input, &[]);
        let block = parser.parse_stmt_block(None).unwrap();
        assert_eq!(
            block,
            vec![Stmt::Let {
                name: "a".into(),
                expr: Expr::Number(1)
            }]
        )
    }

    #[test]
    fn can_parse_empty_line() {
        let input = "let a = 1;\n\nlet b = 2;\n";
        let mut parser = Parser::new(input, &[]);
        parser.parse_stmt_block(None).unwrap();
    }

    #[test]
    fn can_parse_loop_stmt() {
        let input = "loop(n,3)\nlet a = 1;\nend loop\n";
        let mut parser = Parser::new(input, &[]);
        let block = parser.parse_stmt_block(None).unwrap();
        let Stmt::Loop {
            variable,
            max,
            inner,
        } = &block[0]
        else {
            panic!("Expected a loop stmt");
        };
        assert_eq!(variable, &String::from("n"));
        assert_eq!(max, &Expr::Number(3));
        assert_eq!(
            inner,
            &vec![Stmt::Let {
                name: "a".into(),
                expr: Expr::Number(1)
            }]
        )
    }

    #[test]
    fn can_parse_data_row() {
        let signals = ["a", "b", "c", "d", "e", "f", "g"]
            .into_iter()
            .map(String::from)
            .collect::<Vec<_>>();
        let mut parser = Parser::new("1 (a+b) X\tZ\t\tbits(3,3)", &signals);
        let data = parser.parse_data_row().unwrap();
        assert_eq!(data.len(), 5);
    }

    #[test]
    fn can_parse_a_simple_program() {
        let input = r#"let ADD = 0;
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
repeat(3) 0 (ADD) (a)      (b)      0 1          0         (a+b)         X    X    X
end loop
end loop
"#;
        let signals = [
            "BUS-CLK",
            "S",
            "A",
            "B",
            "N",
            "ALU-~RESET",
            "ALU-AUX",
            "OUT",
            "FLAG",
            "DLEN",
            "DSUM",
        ]
        .into_iter()
        .map(String::from)
        .collect::<Vec<_>>();
        let mut parser = Parser::new(input, &signals);
        parser.parse_stmt_block(None).unwrap();
    }

    #[test]
    fn gives_error_on_wrong_number_of_signals_in_data_row() {
        let signals = vec!["a".to_string(), "b".to_string()];
        let mut parser = Parser::new("1 1 1\n", &signals);
        let result = parser.parse_stmt_block(None);
        assert!(result.is_err());
    }
}
