mod binoptree;
mod expr;
mod stmt;

use crate::{
    errors::{ParseError, ParseErrorKind},
    framed_map::FramedSet,
    lexer::{HeaderTokenKind, Token, TokenIter, TokenKind},
    ParsedTestCase,
};
use logos::{Lexer, Logos};
use std::{collections::HashMap, iter::Peekable};

pub(crate) struct HeaderParser<'a> {
    input: &'a str,
    iter: Lexer<'a, HeaderTokenKind>,
    line: usize,
}

pub(crate) struct Parser<'a> {
    input: &'a str,
    iter: Peekable<TokenIter<'a>>,
    line: usize,
    signals: &'a [String],
    expected_inputs: HashMap<&'a str, logos::Span>,
    expected_outputs: HashMap<&'a str, logos::Span>,
    vars: FramedSet<&'a str>,
}

impl Token {
    fn error(&self, kind: ParseErrorKind) -> ParseError {
        ParseError {
            kind,
            at: self.span.clone(),
        }
    }
}

impl<'a> HeaderParser<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        let iter: Lexer<'_, HeaderTokenKind> = HeaderTokenKind::lexer(input);
        let line = 1;
        Self { input, iter, line }
    }

    pub(crate) fn parse(&mut self) -> Result<Vec<String>, ParseError> {
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
                Some(Err(_)) => unreachable!(),
                None => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        at: self.iter.span(),
                    })
                }
            }
        }
    }
}

impl<'a> Parser<'a> {
    #[cfg(test)]
    pub(crate) fn new(input: &'a str, signals: &'a [String]) -> Self {
        let iter = TokenIter::new(input);
        Self {
            iter: iter.peekable(),
            input,
            line: 1,
            signals,
            expected_inputs: HashMap::new(),
            expected_outputs: HashMap::new(),
            vars: FramedSet::new(),
        }
    }

    fn from(HeaderParser { input, iter, line }: HeaderParser<'a>, signals: &'a [String]) -> Self {
        let iter = TokenIter::from(iter).peekable();
        Parser {
            input,
            iter,
            line,
            signals,
            expected_inputs: HashMap::new(),
            expected_outputs: HashMap::new(),
            vars: FramedSet::new(),
        }
    }

    fn get(&mut self) -> Result<Token, ParseError> {
        let Some(tok) = self.iter.next() else {
            let end = self.input.len();
            return Err(ParseError {
                kind: ParseErrorKind::UnexpectedEof,
                at: end..end,
            });
        };
        if tok.kind == TokenKind::Eol {
            self.line += 1;
        }
        Ok(tok)
    }

    fn peek(&mut self) -> TokenKind {
        self.iter
            .peek()
            .expect("peek should not be called after EOF is found")
            .kind
    }

    fn peek_span(&mut self) -> std::ops::Range<usize> {
        self.iter
            .peek()
            .expect("peek should not be called after EOF is found")
            .span
            .clone()
    }

    fn at(&mut self, kind: TokenKind) -> bool {
        self.peek() == kind
    }

    fn skip(&mut self) {
        self.get()
            .expect("skip should not be called after EOF is found");
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        let tok = self.get()?;
        if tok.kind != kind {
            Err(tok.error(ParseErrorKind::NotExpectedToken {
                expected_kind: kind,
                found_kind: tok.kind,
            }))
        } else {
            Ok(tok)
        }
    }

    fn text(&self, token: &Token) -> &'a str {
        &self.input[token.span.clone()]
    }
}

pub(crate) fn parse_testcase(input: &str) -> Result<ParsedTestCase, ParseError> {
    let mut parser = HeaderParser::new(input);
    let signals = parser.parse()?;

    let mut parser = Parser::from(parser, &signals);
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

    #[test]
    fn test_error() -> anyhow::Result<()> {
        let input = r"
A B

let a ( 2;
1 2
";
        let Err(err) = parse_testcase(input) else {
            panic!("Expected an error")
        };
        println!("{err:?}");
        println!("{err}");
        Ok(())
    }
}
