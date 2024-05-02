use logos::Logos;

#[derive(Logos, Debug, PartialEq, Eq)]
pub(crate) enum Token {
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
    #[regex("0x[0-9a-fA-F]+")]
    HexInt,
    #[regex("0b[01]+")]
    BinInt,
    #[regex("0[0-7]*")]
    OctInt,
    #[regex(r"[ \t\r\f]+")]
    WS,
    #[regex(r"#[^\n]*\n")]
    Comment,
    #[token("\n")]
    Eol,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let input = "let a = 1;";
        let mut lex = Token::lexer(input);

        let expected = vec![
            (Token::Let, "let"),
            (Token::WS, " "),
            (Token::Ident, "a"),
            (Token::WS, " "),
            (Token::Eq, "="),
            (Token::WS, " "),
            (Token::DecInt, "1"),
            (Token::Semi, ";"),
        ];

        let mut it = expected.into_iter();
        while let Some(Ok(token)) = lex.next() {
            assert_eq!((token, &input[lex.span()]), it.next().unwrap());
        }
    }
}
