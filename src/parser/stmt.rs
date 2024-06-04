use crate::{
    lexer::{Lexer, TokenKind},
    stmt::Stmt,
};

use super::expr::parse_expr;

fn parse_stmt_block(lex: &mut Lexer, end_token: Option<TokenKind>) -> anyhow::Result<Vec<Stmt>> {
    let mut block = vec![];

    loop {
        match lex.peek() {
            TokenKind::LParen
            | TokenKind::Bits
            | TokenKind::Ident
            | TokenKind::DecInt
            | TokenKind::HexInt
            | TokenKind::BinInt
            | TokenKind::OctInt => todo!(),

            TokenKind::Loop => todo!(),
            TokenKind::Repeat => todo!(),
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
            TokenKind::While => todo!(),
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
            TokenKind::Eol => {
                lex.skip();
            }
            _ => todo!(),
        }
        if lex.at(TokenKind::Eof) {
            break;
        } else if lex.at(TokenKind::Eol) {
            lex.skip();
        } else {
            anyhow::bail!("Expected a new line at the end of statement")
        }
    }
    Ok(block)
}

#[cfg(test)]
mod test {
    use crate::expr::{BinOp, Expr};
    use crate::lexer::Lexer;
    use crate::stmt::Stmt;
    use crate::{DynamicTest, TestCase};

    use super::parse_stmt_block;

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
}
