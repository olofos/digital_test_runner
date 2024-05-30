use logos::Logos;

#[derive(Logos, Clone, Debug, PartialEq, Eq)]
pub(crate) enum HeaderTokenKind {
    #[regex(r"[^ \t\r\f\n]+")]
    SignalName,
    #[regex(r"[ \t\r\f]+", logos::skip)]
    WS,
    #[token("\n")]
    Eol,
}

#[derive(Logos, Clone, Debug, PartialEq, Eq)]
pub(crate) enum TokenKind {
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Times,
    #[token("/")]
    Slash,
    #[token("!")]
    Negate,
    #[token("^")]
    Xor,
    #[token("&")]
    And,
    #[token("|")]
    Or,
    #[token("<<")]
    ShiftL,
    #[token(">>")]
    ShiftR,
    #[token("=")]
    Eq,
    #[token("!=")]
    Neq,
    #[token("<=")]
    Leq,
    #[token(">=")]
    Geq,
    #[token("<")]
    Less,
    #[token(">")]
    Greate,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[token("end")]
    End,
    #[token("loop")]
    Loop,
    #[token("repeat")]
    Repeat,
    #[token("bits")]
    Bits,
    #[token("let")]
    Let,
    #[token("resetRandom")]
    ResetRandom,
    #[token("while")]
    While,
    #[token("declare")]
    Declare,
    #[token("program")]
    Program,
    #[token("init")]
    Init,
    #[token("memory")]
    Memory,
    #[token("def")]
    Def,
    #[token("call")]
    Call,
    #[regex(r"[A-Za-z]([A-Za-z]|_|\d)*")]
    Ident,
    #[regex("[1-9][0-9]*")]
    DecInt,
    #[regex("0[xX][0-9a-fA-F]+")]
    HexInt,
    #[regex("0[bB][01]+")]
    BinInt,
    #[regex("0[0-7]*")]
    OctInt,
    #[regex(r"[ \t\r\f]+", logos::skip)]
    WS,
    #[regex(r"#[^\n]*", logos::skip)]
    Comment,
    #[token("\n")]
    Eol,
}

pub(crate) struct Token {
    pub kind: TokenKind,
    pub span: logos::Span,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let input = "let a = 1;###\n";
        let mut lex = TokenKind::lexer(input);

        let expected = vec![
            (TokenKind::Let, "let"),
            (TokenKind::Ident, "a"),
            (TokenKind::Eq, "="),
            (TokenKind::DecInt, "1"),
            (TokenKind::Semi, ";"),
            (TokenKind::Eol, "\n"),
        ];

        let mut result = vec![];

        while let Some(Ok(token)) = lex.next() {
            result.push((token, lex.slice()));
        }

        assert_eq!(result, expected);
    }
}
