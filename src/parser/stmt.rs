use crate::{
    errors::ParseErrorKind,
    lexer::TokenKind,
    parser::Parser,
    stmt::{DataEntry, Stmt},
};

impl<'a> Parser<'a> {
    pub(crate) fn parse_stmt_block(
        &mut self,
        end_token: Option<TokenKind>,
    ) -> anyhow::Result<Vec<Stmt>> {
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
                        anyhow::bail!("Unexpected End token at top level");
                    }
                }

                TokenKind::Eof => {
                    self.skip();
                    if end_token.is_some() {
                        anyhow::bail!("Unexpected EOF in inner block");
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
                anyhow::bail!(
                    "Expected a new line at the end of statement on line {}",
                    self.line
                );
            }
        }
        Ok(block)
    }

    fn parse_data_row(&mut self) -> anyhow::Result<Vec<DataEntry>> {
        let mut data = vec![];
        loop {
            match self.peek() {
                TokenKind::LParen => {
                    self.skip();
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    data.push(DataEntry::Expr(expr))
                }
                TokenKind::Bits => {
                    self.skip();
                    self.expect(TokenKind::LParen)?;
                    let number = {
                        let n = self.parse_number()?;
                        if n > 64 {
                            anyhow::bail!("Number of bits cannot exceed 64");
                        }
                        n as u8
                    };
                    self.expect(TokenKind::Comma)?;
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    data.push(DataEntry::Bits { number, expr })
                }
                TokenKind::Ident => {
                    let token = self.get()?;
                    match self.text(&token) {
                        "c" | "C" => data.push(DataEntry::C),
                        "x" | "X" => data.push(DataEntry::X),
                        "z" | "Z" => data.push(DataEntry::Z),
                        ident => anyhow::bail!("Expected C, X or Z but found {ident}"),
                    }
                }
                TokenKind::DecInt | TokenKind::HexInt | TokenKind::BinInt | TokenKind::OctInt => {
                    let n = self.parse_number()?;
                    data.push(DataEntry::Number(n));
                }
                TokenKind::Eol | TokenKind::Eof => break,
                kind => anyhow::bail!("Unexpected token {kind:?} while parsing data"),
            }
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
        let mut parser = Parser::new(input);
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
        let mut parser = Parser::new(input);
        parser.parse_stmt_block(None).unwrap();
    }

    #[test]
    fn can_parse_loop_stmt() {
        let input = "loop(n,3)\nlet a = 1;\nend loop\n";
        let mut parser = Parser::new(input);
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
        let mut parser = Parser::new("1 (a+b) X\tZ\t\tbits(1,3*7)");
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
        let mut parser = Parser::new(input);
        parser.parse_stmt_block(None).unwrap();
    }
}
