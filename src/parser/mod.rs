#![allow(clippy::single_range_in_vec_init)]

mod binoptree;
mod expr;
mod stmt;

use crate::{
    errors::{ParseError, ParseErrorKind},
    expr::Expr,
    framed_map::FramedSet,
    lexer::{HeaderTokenKind, Token, TokenIter, TokenKind},
    parsed_test_case::VirtualSignal,
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
    virtual_signals: HashMap<&'a str, (logos::Span, Expr)>,
    expected_inputs: HashMap<&'a str, logos::Span>,
    expected_outputs: HashMap<&'a str, logos::Span>,
    vars: FramedSet<&'a str>,
}

pub(crate) struct ParseResult {
    pub(crate) expected_inputs: Vec<(String, logos::Span)>,
    pub(crate) read_outputs: Vec<(String, logos::Span)>,
    pub(crate) virtual_signals: Vec<(VirtualSignal, logos::Span)>,
}

impl Token {
    fn error(&self, kind: ParseErrorKind) -> ParseError {
        ParseError {
            kind,
            at: vec![self.span.clone()],
            source_code: None,
        }
    }
}

impl<'a> HeaderParser<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        let iter: Lexer<'_, HeaderTokenKind> = HeaderTokenKind::lexer(input);
        let line = 1;
        Self { input, iter, line }
    }

    pub(crate) fn parse(&mut self) -> Result<(Vec<String>, Vec<logos::Span>), ParseError> {
        let mut signals: Vec<String> = vec![];
        let mut spans: Vec<logos::Span> = vec![];
        loop {
            match self.iter.next() {
                Some(Ok(HeaderTokenKind::SignalName)) => {
                    let name = self.iter.slice().into();
                    let span = self.iter.span();
                    if let Some(i) = signals.iter().position(|n| n == &name) {
                        return Err(ParseError {
                            kind: ParseErrorKind::DuplicateSignal { name },
                            at: vec![spans[i].clone(), span],
                            source_code: None,
                        });
                    }
                    signals.push(name);
                    spans.push(span);
                }
                Some(Ok(HeaderTokenKind::Eol)) => {
                    self.line += 1;
                    if !signals.is_empty() {
                        return Ok((signals, spans));
                    }
                }
                Some(Ok(HeaderTokenKind::WS)) => unreachable!(),
                Some(Err(_)) => unreachable!(),
                None => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        at: vec![self.iter.span()],
                        source_code: None,
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
            virtual_signals: HashMap::new(),
            expected_inputs: HashMap::new(),
            expected_outputs: HashMap::new(),
            vars: FramedSet::new(),
        }
    }

    pub(crate) fn from(
        HeaderParser { input, iter, line }: HeaderParser<'a>,
        signals: &'a [String],
    ) -> Self {
        let iter = TokenIter::from(iter).peekable();
        Parser {
            input,
            iter,
            line,
            signals,
            virtual_signals: HashMap::new(),
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
                at: vec![end..end],
                source_code: None,
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

    pub(crate) fn finish(self) -> ParseResult {
        let mut expected_inputs = self
            .expected_inputs
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect::<Vec<_>>();

        expected_inputs.sort_by(|(_, a), (_, b)| a.start.cmp(&b.start));

        let mut read_outputs = self
            .expected_outputs
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect::<Vec<_>>();

        read_outputs.sort_by(|(_, a), (_, b)| a.start.cmp(&b.start));

        let virtual_signals = self
            .virtual_signals
            .into_iter()
            .map(|(name, (span, expr))| {
                (
                    VirtualSignal {
                        name: name.to_string(),
                        expr,
                    },
                    span,
                )
            })
            .collect();

        ParseResult {
            expected_inputs,
            read_outputs,
            virtual_signals,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{stmt::Stmt, ParsedTestCase};

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
        let testcase = ParsedTestCase::parse(input).unwrap();
        assert_eq!(testcase.signals.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);
        let Stmt::DataRow { data: _, line } = &testcase.stmts[4] else {
            panic!();
        };
        assert_eq!(*line, 9);
    }

    #[test]
    fn test_error() -> miette::Result<()> {
        let input = r"
A B

let a ( 2;
1 2
";
        let Err(err) = ParsedTestCase::parse(input) else {
            panic!("Expected an error")
        };
        println!("{err:?}");
        println!("{err}");
        Ok(())
    }
}
