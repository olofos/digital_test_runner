#![cfg(test)]

use super::*;
use crate::ParsedTestCase;

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
    let testcase: ParsedTestCase = input.parse().unwrap();
    assert_eq!(testcase.signals.len(), 11);
    assert_eq!(testcase.stmts.len(), 7);
}

#[test]
fn can_iterate_simple_program() {
    let input = r"
A B
0 0
0 1
1 0
1 1
";

    let expectation = vec![[0, 0], [0, 1], [1, 0], [1, 1]]
        .into_iter()
        .map(|v| v.into_iter().map(DataEntry::Number).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let testcase: ParsedTestCase = input.parse().unwrap();

    let mut ctx = EvalContext::new();
    let mut result = vec![];
    let mut iter = StmtIterator::new(&testcase.stmts);
    while let Some(row) = iter.next_with_context(&mut ctx).unwrap() {
        result.push(row.entries);
    }
    assert_eq!(result, expectation)
}

#[test]
fn bits_works() {
    let input = r"
Q2 Q1 Q0 
loop (n,8)
bits(3,n)
end loop
";

    let expectation = vec![
        [0, 0, 0],
        [0, 0, 1],
        [0, 1, 0],
        [0, 1, 1],
        [1, 0, 0],
        [1, 0, 1],
        [1, 1, 0],
        [1, 1, 1],
    ]
    .into_iter()
    .map(|v| v.into_iter().map(DataEntry::Number).collect::<Vec<_>>())
    .collect::<Vec<_>>();

    let testcase: ParsedTestCase = input.parse().unwrap();

    let mut ctx = EvalContext::new();
    let mut result = vec![];
    let mut iter = StmtIterator::new(&testcase.stmts);
    while let Some(row) = iter.next_with_context(&mut ctx).unwrap() {
        result.push(row.entries);
    }
    assert_eq!(result, expectation)
}

#[test]
fn can_iterate_program_with_loop() {
    let input = r"
A B
let n = 2;
bits(2,n)
loop(n,4)
bits(2,n)
end loop
bits(2,n)
";

    let expectation = vec![[1, 0], [0, 0], [0, 1], [1, 0], [1, 1], [1, 0]]
        .into_iter()
        .map(|v| v.into_iter().map(DataEntry::Number).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let testcase: ParsedTestCase = input.parse().unwrap();

    let mut ctx = EvalContext::new();
    let mut result = vec![];
    let mut iter = StmtIterator::new(&testcase.stmts);
    while let Some(row) = iter.next_with_context(&mut ctx).unwrap() {
        result.push(row.entries);
    }
    assert_eq!(result, expectation)
}

#[test]
fn can_iterate_program_with_while() {
    let input = r"
A B
let n = 0;
while(n<4)
bits(2,n)
let n = n+1;
end while
";

    let expectation = vec![[0, 0], [0, 1], [1, 0], [1, 1]]
        .into_iter()
        .map(|v| v.into_iter().map(DataEntry::Number).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let testcase: ParsedTestCase = input.parse().unwrap();

    let mut ctx = EvalContext::new();
    let mut result = vec![];
    let mut iter = StmtIterator::new(&testcase.stmts);
    while let Some(row) = iter.next_with_context(&mut ctx).unwrap() {
        result.push(row.entries);
    }
    assert_eq!(result, expectation)
}
