use std::mem;

use crate::eval_context::EvalContext;
use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stmt {
    Let {
        name: String,
        expr: Expr,
    },
    DataRow {
        data: Vec<DataEntry>,
        line: usize,
    },
    Loop {
        variable: String,
        max: Expr,
        inner: Vec<Stmt>,
    },
    While {
        condition: Expr,
        inner: Vec<Stmt>,
    },
    ResetRandom,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DataEntry {
    Number(i64),
    Expr(Expr),
    Bits { number: u8, expr: Expr },
    X,
    Z,
    C,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DataEntries {
    pub(crate) entries: Vec<DataEntry>,
    pub(crate) line: usize,
}

#[derive(Debug)]
struct LoopState<'a> {
    variable: &'a str,
    max: i64,
    stmts: &'a [Stmt],
}

#[derive(Debug)]
struct WhileState<'a> {
    condition: &'a Expr,
    stmts: &'a [Stmt],
}

#[derive(Debug)]
enum StmtIteratorState<'a> {
    Iterate,
    StartLoop(LoopState<'a>),
    StartIterateInner(LoopState<'a>),
    IterateInner {
        inner_iterator: Box<StmtIterator<'a>>,
        loop_state: LoopState<'a>,
    },
    EndIterateInner(LoopState<'a>),
    StartWhile(WhileState<'a>),
    WhileIterateInner {
        inner_iterator: Box<StmtIterator<'a>>,
        while_state: WhileState<'a>,
    },
}

#[derive(Debug)]
pub(crate) struct StmtIterator<'a> {
    stmt_iter: std::slice::Iter<'a, Stmt>,
    inner_state: StmtIteratorState<'a>,
}

impl<'a> LoopState<'a> {
    fn take(&mut self) -> Self {
        mem::replace(
            self,
            LoopState {
                variable: "",
                max: 0,
                stmts: &[],
            },
        )
    }
}

impl<'a> WhileState<'a> {
    fn take(&mut self) -> Self {
        mem::replace(
            self,
            WhileState {
                condition: &Expr::Number(0),
                stmts: &[],
            },
        )
    }
}

impl<'a> StmtIterator<'a> {
    pub(crate) fn new(stmts: &'a [Stmt]) -> Self {
        Self {
            stmt_iter: stmts.iter(),
            inner_state: StmtIteratorState::Iterate,
        }
    }
    pub(crate) fn next_with_context(&mut self, ctx: &mut EvalContext) -> Option<DataEntries> {
        loop {
            match &mut self.inner_state {
                StmtIteratorState::Iterate => match self.stmt_iter.next()? {
                    Stmt::Let { name, expr } => ctx.set(name, expr.eval(ctx).unwrap()),
                    Stmt::DataRow { data, line } => {
                        return Some(DataEntries {
                            entries: data.iter().flat_map(|entry| entry.eval(ctx)).collect(),
                            line: *line,
                        })
                    }
                    Stmt::Loop {
                        variable,
                        max,
                        inner,
                    } => {
                        self.inner_state = StmtIteratorState::StartLoop(LoopState {
                            variable,
                            max: max.eval(ctx).unwrap(),
                            stmts: inner,
                        })
                    }
                    Stmt::ResetRandom => ctx.reset_random_seed(),
                    Stmt::While { condition, inner } => {
                        self.inner_state = StmtIteratorState::StartWhile(WhileState {
                            condition,
                            stmts: inner,
                        })
                    }
                },
                StmtIteratorState::IterateInner {
                    inner_iterator,
                    loop_state,
                } => {
                    if let Some(result) = inner_iterator.next_with_context(ctx) {
                        return Some(result);
                    }
                    self.inner_state = StmtIteratorState::EndIterateInner(loop_state.take())
                }
                StmtIteratorState::StartLoop(loop_state) => {
                    ctx.push_frame();
                    ctx.set(loop_state.variable, 0);
                    self.inner_state = StmtIteratorState::StartIterateInner(loop_state.take());
                }
                StmtIteratorState::StartIterateInner(loop_state) => {
                    let loop_state = loop_state.take();
                    let inner_iterator = Box::new(StmtIterator {
                        stmt_iter: loop_state.stmts.iter(),
                        inner_state: StmtIteratorState::Iterate,
                    });
                    self.inner_state = StmtIteratorState::IterateInner {
                        inner_iterator,
                        loop_state,
                    };
                }
                StmtIteratorState::EndIterateInner(loop_state) => {
                    let value = ctx.get(loop_state.variable).unwrap() + 1;
                    if value < loop_state.max {
                        ctx.set(loop_state.variable, value);
                        self.inner_state = StmtIteratorState::StartIterateInner(loop_state.take());
                    } else {
                        ctx.pop_frame();
                        self.inner_state = StmtIteratorState::Iterate;
                    }
                }
                StmtIteratorState::StartWhile(while_state) => {
                    let cond = while_state.condition.eval(ctx).unwrap();
                    if cond == 0 {
                        self.inner_state = StmtIteratorState::Iterate;
                    } else {
                        let while_state = while_state.take();
                        let inner_iterator = Box::new(StmtIterator {
                            stmt_iter: while_state.stmts.iter(),
                            inner_state: StmtIteratorState::Iterate,
                        });
                        self.inner_state = StmtIteratorState::WhileIterateInner {
                            inner_iterator,
                            while_state,
                        }
                    }
                }
                StmtIteratorState::WhileIterateInner {
                    inner_iterator,
                    while_state,
                } => {
                    if let Some(result) = inner_iterator.next_with_context(ctx) {
                        return Some(result);
                    }
                    self.inner_state = StmtIteratorState::StartWhile(while_state.take())
                }
            }
        }
    }
}

impl DataEntry {
    fn eval(&self, ctx: &mut EvalContext) -> Vec<DataEntry> {
        match self {
            Self::Expr(expr) => vec![Self::Number(expr.eval(ctx).unwrap())],
            Self::Bits { number, expr } => {
                let value = expr.eval(ctx).unwrap();
                (0..*number)
                    .rev()
                    .map(|n| Self::Number((value >> n) & 1))
                    .collect::<Vec<_>>()
            }
            Self::X | Self::Z | Self::C | Self::Number(_) => vec![self.clone()],
        }
    }
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let { name, expr } => {
                write!(f, "let {name} = {expr};")
            }
            Self::Loop {
                variable,
                max,
                inner,
            } => {
                writeln!(f, "loop({variable},{max})")?;
                for stmt in inner.iter() {
                    writeln!(f, "{stmt}")?;
                }
                write!(f, "end loop")
            }
            Self::ResetRandom => {
                write!(f, "resetRandom;")
            }
            Self::DataRow { data, line: _ } => {
                for entry in data {
                    write!(f, "{} ", entry)?;
                }
                Ok(())
            }
            Self::While { condition, inner } => {
                writeln!(f, "while({condition})")?;
                for stmt in inner.iter() {
                    writeln!(f, "{stmt}")?;
                }
                write!(f, "end while")
            }
        }
    }
}

impl std::fmt::Display for DataEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(n) => {
                write!(f, "{n}")
            }
            Self::Expr(expr) => {
                write!(f, "({expr})")
            }
            Self::Bits { number, expr } => {
                write!(f, "bits({number},{expr})")
            }
            Self::X => {
                write!(f, "X")
            }
            Self::Z => {
                write!(f, "Z")
            }
            Self::C => {
                write!(f, "C")
            }
        }
    }
}

#[cfg(test)]
mod tests {
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
        while let Some(row) = iter.next_with_context(&mut ctx) {
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
        while let Some(row) = iter.next_with_context(&mut ctx) {
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
        while let Some(row) = iter.next_with_context(&mut ctx) {
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
        while let Some(row) = iter.next_with_context(&mut ctx) {
            result.push(row.entries);
        }
        assert_eq!(result, expectation)
    }
}
