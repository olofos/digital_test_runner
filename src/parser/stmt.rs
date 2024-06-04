use crate::{
    lexer::{Lexer, TokenKind},
    stmt::{DataEntry, Stmt},
};

use super::expr::{parse_expr, parse_number};

pub(crate) fn parse_stmt_block(
    lex: &mut Lexer,
    end_token: Option<TokenKind>,
) -> anyhow::Result<Vec<Stmt>> {
    let mut block = vec![];

    loop {
        match lex.peek() {
            TokenKind::LParen
            | TokenKind::Bits
            | TokenKind::Ident
            | TokenKind::DecInt
            | TokenKind::HexInt
            | TokenKind::BinInt
            | TokenKind::OctInt => {
                let data = parse_data_row(lex)?;
                block.push(Stmt::DataRow {
                    data,
                    line: lex.line,
                });
            }

            TokenKind::Loop => {
                lex.skip();
                lex.expect(TokenKind::LParen)?;
                let variable = {
                    let token = lex.expect(TokenKind::Ident)?;
                    lex.text(&token).to_string()
                };
                lex.expect(TokenKind::Comma)?;
                let max = parse_expr(lex)?;
                lex.expect(TokenKind::RParen)?;
                lex.expect(TokenKind::Eol)?;
                let inner = parse_stmt_block(lex, Some(TokenKind::Loop))?;

                block.push(Stmt::Loop {
                    variable,
                    max,
                    inner,
                });
            }
            TokenKind::Repeat => {
                lex.skip();
                lex.expect(TokenKind::LParen)?;
                let max = parse_expr(lex)?;
                lex.expect(TokenKind::RParen)?;
                let data = parse_data_row(lex)?;
                let stmt = Stmt::DataRow {
                    data,
                    line: lex.line,
                };
                block.push(Stmt::Loop {
                    variable: "n".into(),
                    max,
                    inner: vec![stmt],
                });
            }
            TokenKind::Let => {
                lex.skip();
                let name = {
                    let token = lex.expect(TokenKind::Ident)?;
                    lex.text(&token).to_string()
                };
                lex.expect(TokenKind::Equal)?;
                let expr = parse_expr(lex)?;
                lex.expect(TokenKind::Semi)?;
                block.push(Stmt::Let { name, expr });
            }
            TokenKind::ResetRandom => {
                lex.skip();
                lex.expect(TokenKind::Semi)?;
                block.push(Stmt::ResetRandom);
            }
            TokenKind::While => {
                lex.skip();
                lex.expect(TokenKind::LParen)?;
                let _expr = parse_expr(lex)?;
                lex.expect(TokenKind::RParen)?;
                lex.expect(TokenKind::Eol)?;
                let _inner = parse_stmt_block(lex, Some(TokenKind::While))?;
                unimplemented!("While stmt is not implemented")
            }
            TokenKind::Declare => todo!(),
            TokenKind::Program => todo!(),
            TokenKind::Init => todo!(),
            TokenKind::Memory => todo!(),
            TokenKind::Def => todo!(),
            TokenKind::Call => todo!(),

            TokenKind::End => {
                if let Some(kind) = end_token {
                    lex.skip();
                    lex.expect(kind)?;
                    break;
                } else {
                    anyhow::bail!("Unexpected End token at top level");
                }
            }

            TokenKind::Eof => {
                lex.skip();
                if end_token.is_some() {
                    anyhow::bail!("Unexpected EOF in inner block");
                }
                break;
            }
            TokenKind::Eol => {}
            _ => todo!(),
        }
        if lex.at(TokenKind::Eof) {
            break;
        } else if lex.at(TokenKind::Eol) {
            lex.skip();
        } else {
            anyhow::bail!(
                "Expected a new line at the end of statement on line {}",
                lex.line
            );
        }
    }
    Ok(block)
}

fn parse_data_row(lex: &mut Lexer) -> anyhow::Result<Vec<DataEntry>> {
    let mut data = vec![];
    loop {
        match lex.peek() {
            TokenKind::LParen => {
                lex.skip();
                let expr = parse_expr(lex)?;
                lex.expect(TokenKind::RParen)?;
                data.push(DataEntry::Expr(expr))
            }
            TokenKind::Bits => {
                lex.skip();
                lex.expect(TokenKind::LParen)?;
                let number = {
                    let n = parse_number(lex)?;
                    if n > 255 {
                        anyhow::bail!("Number of bits cannot exceed 255");
                    }
                    n as u8
                };
                lex.expect(TokenKind::Comma)?;
                let expr = parse_expr(lex)?;
                lex.expect(TokenKind::RParen)?;
                data.push(DataEntry::Bits { number, expr })
            }
            TokenKind::Ident => {
                let token = lex.get()?;
                match lex.text(&token) {
                    "c" | "C" => data.push(DataEntry::C),
                    "x" | "X" => data.push(DataEntry::X),
                    "z" | "Z" => data.push(DataEntry::Z),
                    ident => anyhow::bail!("Expected C, X or Z but found {ident}"),
                }
            }
            TokenKind::DecInt | TokenKind::HexInt | TokenKind::BinInt | TokenKind::OctInt => {
                let n = parse_number(lex)?;
                data.push(DataEntry::Number(n));
            }
            TokenKind::Eol | TokenKind::Eof => break,
            kind => anyhow::bail!("Unexpected token {kind:?} while parsing data"),
        }
    }
    Ok(data)
}

#[cfg(test)]
mod test {
    use crate::expr::Expr;
    use crate::lexer::Lexer;
    use crate::stmt::Stmt;

    use super::{parse_data_row, parse_stmt_block};

    #[test]
    fn can_parse_let_stmt() {
        let input = "let a = 1;\n";
        let mut lex = Lexer::new(input);
        let block = parse_stmt_block(&mut lex, None).unwrap();
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
        let mut lex = Lexer::new(input);
        parse_stmt_block(&mut lex, None).unwrap();
    }

    #[test]
    fn can_parse_loop_stmt() {
        let input = "loop(n,3)\nlet a = 1;\nend loop\n";
        let mut lex = Lexer::new(input);
        let block = parse_stmt_block(&mut lex, None).unwrap();
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
        let mut lex = Lexer::new("1 (a+b) X\tZ\t\tbits(1,3*7)");
        let data = parse_data_row(&mut lex).unwrap();
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
        let mut lex = Lexer::new(input);
        parse_stmt_block(&mut lex, None).unwrap();
    }
}
