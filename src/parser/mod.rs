mod binoptree;
mod expr;
mod stmt;

use crate::{
    lexer::{HeaderTokenKind, Lexer},
    DynamicTest, TestCase,
};
use logos::Logos;
use stmt::parse_stmt_block;

pub(crate) fn parse_testcase(input: &str) -> anyhow::Result<TestCase<String, DynamicTest>> {
    let mut lex: logos::Lexer<HeaderTokenKind> = HeaderTokenKind::lexer(input);
    let mut signals: Vec<String> = vec![];
    while let Some(kind) = lex.next() {
        match kind {
            Ok(HeaderTokenKind::SignalName) => signals.push(lex.slice().into()),
            Ok(HeaderTokenKind::Eol) => {
                if signals.len() > 0 {
                    break;
                }
            }
            Ok(HeaderTokenKind::WS) => unreachable!(),
            Err(_) => unimplemented!(),
        }
    }

    let mut lex: Lexer = lex.into();
    let stmts = parse_stmt_block(&mut lex, None)?;

    let test_case = TestCase {
        stmts,
        signals,
        phantom: std::marker::PhantomData,
    };
    Ok(test_case)
}

#[cfg(test)]
mod test {
    use crate::{parser::parse_testcase, stmt::Stmt, DynamicTest, TestCase};

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
        // let testcase: TestCase<String, DynamicTest> = input.parse().unwrap();
        let testcase: TestCase<String, DynamicTest> = parse_testcase(input).unwrap();
        assert_eq!(testcase.signals.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);
        let Stmt::DataRow { data: _, line } = &testcase.stmts[4] else {
            panic!();
        };
        assert_eq!(*line, 9);
    }
}
