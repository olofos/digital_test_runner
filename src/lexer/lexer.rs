use std::iter::Peekable;

use logos::Logos;

use super::token::{Token, TokenKind};

#[derive()]
pub(crate) struct Lexer<'a> {
    lex: Peekable<logos::SpannedIter<'a, TokenKind>>,
    input: &'a str,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            lex: TokenKind::lexer(input).spanned().peekable(),
            input,
        }
    }

    pub fn peek(&mut self) -> Option<&TokenKind> {
        let (result, _) = self.lex.peek()?;
        result.as_ref().ok()
    }

    pub fn text(&self, token: &Token) -> &'a str {
        &self.input[token.span.clone()]
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, <TokenKind as Logos<'a>>::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.lex
            .next()
            .map(|(result, span)| result.map(|kind| Token { kind, span }))
    }
}
