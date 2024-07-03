mod binoptree;
mod expr;
mod stmt;

use crate::{
    lexer::{HeaderTokenKind, Token, TokenIter, TokenKind},
    ParsedTestCase,
};
use logos::{Lexer, Logos};
use std::iter::Peekable;

pub(crate) struct HeaderParser<'a> {
    input: &'a str,
    iter: Lexer<'a, HeaderTokenKind>,
    line: usize,
}

struct Parser<'a> {
    input: &'a str,
    iter: Peekable<TokenIter<'a>>,
    line: usize,
}

impl<'a> From<HeaderParser<'a>> for Parser<'a> {
    fn from(HeaderParser { input, iter, line }: HeaderParser<'a>) -> Self {
        let iter = TokenIter::from(iter).peekable();
        Parser { input, iter, line }
    }
}

impl<'a> HeaderParser<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        let iter: Lexer<'_, HeaderTokenKind> = HeaderTokenKind::lexer(input);
        let line = 1;
        Self { input, iter, line }
    }

    pub(crate) fn parse(&mut self) -> anyhow::Result<Vec<String>> {
        let mut signals: Vec<String> = vec![];
        loop {
            match self.iter.next() {
                Some(Ok(HeaderTokenKind::SignalName)) => signals.push(self.iter.slice().into()),
                Some(Ok(HeaderTokenKind::Eol)) => {
                    self.line += 1;
                    if !signals.is_empty() {
                        return Ok(signals);
                    }
                }
                Some(Ok(HeaderTokenKind::WS)) => unreachable!(),
                Some(Err(_)) => {
                    anyhow::bail!(
                        "Expected signal name, found {}",
                        &self.input[self.iter.span()]
                    )
                }
                None => anyhow::bail!("Unexpected EOF while parsing header"),
            }
        }
    }
}

impl<'a> Parser<'a> {
    #[allow(dead_code)]
    pub(crate) fn new(input: &'a str) -> Self {
        let iter = TokenIter::new(input);
        Self {
            iter: iter.peekable(),
            input,
            line: 1,
        }
    }

    pub(crate) fn get(&mut self) -> anyhow::Result<Token> {
        let Some(tok) = self.iter.next() else {
            anyhow::bail!("Unexpected EOF on line {}", self.line);
        };
        if tok.kind == TokenKind::Eol {
            self.line += 1;
        }
        Ok(tok)
    }

    pub(crate) fn peek(&mut self) -> TokenKind {
        self.iter
            .peek()
            .expect("peek should not be called after EOF is found")
            .kind
    }

    pub(crate) fn at(&mut self, kind: TokenKind) -> bool {
        self.peek() == kind
    }

    pub(crate) fn skip(&mut self) {
        self.get()
            .expect("skip should not be called after EOF is found");
    }

    pub(crate) fn expect(&mut self, kind: TokenKind) -> anyhow::Result<Token> {
        let tok = self.get()?;
        if tok.kind != kind {
            anyhow::bail!("Expected a {kind:?} token but found {:?}", tok.kind);
        }

        Ok(tok)
    }

    pub(crate) fn text(&self, token: &Token) -> &'a str {
        &self.input[token.span.clone()]
    }
}

pub(crate) fn parse_testcase(input: &str) -> anyhow::Result<ParsedTestCase> {
    let mut parser = HeaderParser::new(input);
    let signals = parser.parse()?;

    let mut parser = Parser::from(parser);
    let stmts = parser.parse_stmt_block(None)?;

    let test_case = ParsedTestCase { stmts, signals };
    Ok(test_case)
}

#[cfg(test)]
mod test {
    use crate::{parser::parse_testcase, stmt::Stmt, ParsedTestCase};

    #[test]
    fn can_parse_simple_program() {
        let input = r"
BUS-CLK S         A        B        N ALU-~RESET ALU-AUX   OUT           FLAG DLEN DSUM

let ADD = 0;
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
0       (ADD)     (a)      (b)      0 1          0         (a+b)         X    X    X
end loop
end loop

";
        let testcase: ParsedTestCase = parse_testcase(input).unwrap();
        assert_eq!(testcase.signals.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);
        let Stmt::DataRow { data: _, line } = &testcase.stmts[4] else {
            panic!();
        };
        assert_eq!(*line, 9);
    }
}
