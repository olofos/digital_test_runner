mod token;

pub(crate) use token::{HeaderTokenKind, TokenKind};

use std::iter::Peekable;

use logos::Logos;
use token::Token;

struct TokenIter<'a> {
    iter: logos::SpannedIter<'a, TokenKind>,
    eof: bool,
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some((Ok(kind), span)) => Some(Token { kind, span }),
            Some((Err(_), span)) => Some(Token {
                kind: TokenKind::Error,
                span,
            }),
            None if !self.eof => {
                self.eof = true;
                Some(Token {
                    kind: TokenKind::Eof,
                    span: self.iter.span(),
                })
            }
            None => None,
        }
    }
}

#[derive()]
pub(crate) struct Lexer<'a> {
    lex: Peekable<TokenIter<'a>>,
    input: &'a str,
    pub line: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let iter = TokenIter {
            iter: TokenKind::lexer(input).spanned(),
            eof: false,
        };
        Self {
            lex: iter.peekable(),
            input,
            line: 0,
        }
    }

    pub fn get(&mut self) -> anyhow::Result<Token> {
        let Some(tok) = self.lex.next() else {
            anyhow::bail!("Unexpected EOF on line {}", self.line);
        };
        if tok.kind == TokenKind::Eol {
            self.line += 1;
        }
        Ok(tok)
    }

    pub fn peek(&mut self) -> TokenKind {
        self.lex
            .peek()
            .expect("peek should not be called after EOF is found")
            .kind
    }

    pub fn at(&mut self, kind: TokenKind) -> bool {
        self.peek() == kind
    }

    pub fn skip(&mut self) {
        self.get()
            .expect("skip should not be called after EOF is found");
    }

    pub fn consume(&mut self, kind: TokenKind) -> anyhow::Result<()> {
        let tok = self.get()?;
        if tok.kind != kind {
            anyhow::bail!("Expected a {kind:?} token but found {:?}", tok.kind);
        }

        Ok(())
    }

    pub fn text(&self, token: &Token) -> &'a str {
        &self.input[token.span.clone()]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn token_iter_gives_correct_eof_span() {
        let input = "a";
        let iter = TokenKind::lexer(input).spanned();
        let mut iter = TokenIter { iter, eof: false };

        assert_eq!(
            iter.next(),
            Some(Token {
                kind: TokenKind::Ident,
                span: 0..1
            })
        );
        assert_eq!(
            iter.next(),
            Some(Token {
                kind: TokenKind::Eof,
                span: 1..1
            })
        );
        assert_eq!(iter.next(), None);
    }
}
