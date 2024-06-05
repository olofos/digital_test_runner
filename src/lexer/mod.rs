mod token;

pub(crate) use token::{HeaderTokenKind, Token, TokenKind};

use logos::{Lexer, Logos, SpannedIter};

pub(crate) struct TokenIter<'a> {
    iter: SpannedIter<'a, TokenKind>,
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

impl<'a> TokenIter<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            iter: TokenKind::lexer(input).spanned(),
            eof: false,
        }
    }
}

impl<'a, T> From<Lexer<'a, T>> for TokenIter<'a>
where
    T: Logos<'a, Source = str>,
    T::Extras: Into<()>,
{
    fn from(iter: Lexer<'a, T>) -> Self {
        let iter = iter.morph();
        let iter = iter.spanned();
        Self { iter, eof: false }
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
