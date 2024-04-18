use crate::eval_context::{self, EvalContext};
use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stmt {
    Let {
        name: String,
        expr: Expr,
    },
    DataRow {
        data: Vec<DataEntry>,
        line: u32,
    },
    Loop {
        variable: String,
        max: i64,
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
pub enum DataResult {
    Number(i64),
    X,
    Z,
}

#[derive(Debug)]
pub(crate) struct StmtInnerIteratorState<'a> {
    variable: &'a str,
    value: i64,
    max: i64,
    inner_iter: Box<StmtInnerIterator<'a>>,
    stmts: &'a [Stmt],
}

#[derive(Debug)]
pub(crate) struct StmtInnerIterator<'a> {
    stmt_iter: std::slice::Iter<'a, Stmt>,
    inner_state: Option<StmtInnerIteratorState<'a>>,
}

#[derive(Debug)]
pub(crate) struct StmtIterator<'a> {
    iter: StmtInnerIterator<'a>,
    ctx: &'a mut EvalContext,
}

impl<'a> Iterator for StmtIterator<'a> {
    type Item = Vec<DataEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next_with_context(self.ctx)
    }
}

impl<'a> StmtIterator<'a> {
    fn new(stmts: &'a [Stmt], ctx: &'a mut EvalContext) -> Self {
        let iter = StmtInnerIterator {
            stmt_iter: stmts.iter(),
            inner_state: None,
        };
        Self { iter, ctx }
    }
}

impl<'a> StmtInnerIterator<'a> {
    fn handle_inner_state(&mut self, ctx: &mut EvalContext) -> Option<Vec<DataEntry>> {
        let Some(StmtInnerIteratorState {
            variable,
            value,
            max,
            inner_iter,
            stmts,
        }) = &mut self.inner_state
        else {
            panic!()
        };

        if let Some(result) = inner_iter.next_with_context(ctx) {
            return Some(result);
        }

        *value += 1;
        if value < max {
            ctx.set(variable, *value);
            **inner_iter = StmtInnerIterator {
                stmt_iter: stmts.iter(),
                inner_state: None,
            };
        } else {
            ctx.pop_frame();
            self.inner_state = None;
        }

        None
    }

    fn enter_loop(
        ctx: &mut EvalContext,
        variable: &'a str,
        max: i64,
        inner: &'a [Stmt],
    ) -> Option<StmtInnerIteratorState<'a>> {
        ctx.push_frame();
        ctx.set(variable, 0);
        Some(StmtInnerIteratorState {
            variable,
            value: 0,
            max,
            inner_iter: Box::new(StmtInnerIterator {
                stmt_iter: inner.iter(),
                inner_state: None,
            }),
            stmts: inner,
        })
    }

    fn next_with_context(&mut self, ctx: &mut EvalContext) -> Option<Vec<DataEntry>> {
        loop {
            if self.inner_state.is_some() {
                if let Some(result) = self.handle_inner_state(ctx) {
                    return Some(result);
                }
            } else {
                match self.stmt_iter.next()? {
                    Stmt::Let { name, expr } => ctx.set(name, expr.eval(ctx).unwrap()),
                    Stmt::ResetRandom => ctx.reset_random_seed(),
                    Stmt::DataRow { data, line: _ } => {
                        return Some(data.iter().flat_map(|entry| entry.eval(ctx)).collect())
                    }
                    Stmt::Loop {
                        variable,
                        max,
                        inner,
                    } => {
                        self.inner_state = Self::enter_loop(ctx, variable, *max, inner);
                    }
                }
            }
        }
    }
}

impl Stmt {
    pub(crate) fn emit_lines(
        &self,
        ctx: &mut EvalContext,
        emit_line: &mut impl FnMut(Vec<DataEntry>, u32) -> (),
    ) -> anyhow::Result<()> {
        match self {
            Self::Let { name, expr } => {
                let value = expr.eval(ctx).unwrap();
                ctx.set(name, value);
            }
            Self::DataRow { data, line } => {
                let mut result = vec![];
                for entry in data {
                    result.extend(entry.eval(ctx));
                }
                emit_line(result, *line);
            }
            Self::Loop {
                variable,
                max,
                inner,
            } => {
                let mut ctx = ctx.new_frame();

                for i in 0..*max {
                    ctx.set(variable, i);
                    for stmt in inner {
                        stmt.emit_lines(&mut ctx, emit_line)?;
                    }
                }
            }
            Self::ResetRandom => {
                ctx.reset_random_seed();
            }
        }

        Ok(())
    }
}

impl DataEntry {
    fn eval(&self, ctx: &mut EvalContext) -> Vec<DataEntry> {
        match self {
            Self::Expr(expr) => vec![Self::Number(expr.eval(ctx).unwrap())],
            Self::Bits { number, expr } => {
                let value = expr.eval(ctx).unwrap();
                (0..*number)
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
                for stmt in inner.iter().take(inner.len() - 1) {
                    writeln!(f, "{stmt}")?;
                }
                if let Some(stmt) = inner.last() {
                    write!(f, "{stmt}")?;
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
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResultRow {
    pub inputs: Vec<DataResult>,
    pub outputs: Vec<DataResult>,
    pub line: u32,
}

impl std::fmt::Display for ResultRow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: ", self.line)?;
        let s = self
            .inputs
            .iter()
            .map(|entry| match entry {
                DataResult::Number(n) => format!("{n}"),
                DataResult::X => String::from("X"),
                DataResult::Z => String::from("Z"),
            })
            .collect::<Vec<_>>()
            .join(" ");

        write!(f, "[ {s} ]")?;
        write!(f, " ")?;

        let s = self
            .outputs
            .iter()
            .map(|entry| match entry {
                DataResult::Number(n) => format!("{n}"),
                DataResult::X => String::from("X"),
                DataResult::Z => String::from("Z"),
            })
            .collect::<Vec<_>>()
            .join(" ");
        write!(f, "[ {s} ]")
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
        assert_eq!(testcase.signal_names.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);

        let mut ctx = EvalContext::new();
        for stmt in &testcase.stmts {
            stmt.emit_lines(&mut ctx, &mut |result, line| {
                let s = result
                    .iter()
                    .map(|r| format!("{r}"))
                    .collect::<Vec<_>>()
                    .join(" ");
                println!("{line:2}: {s}");
            })
            .unwrap();
        }
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

        let testcase: ParsedTestCase = input.parse().unwrap();
        assert_eq!(testcase.signal_names.len(), 2);
        assert_eq!(testcase.stmts.len(), 4);

        let mut iter = StmtInnerIterator {
            stmt_iter: testcase.stmts.iter(),
            inner_state: None,
        };
        let mut ctx = EvalContext::new();

        assert_eq!(
            iter.next_with_context(&mut ctx),
            Some(vec![DataEntry::Number(0), DataEntry::Number(0),])
        );
        assert_eq!(
            iter.next_with_context(&mut ctx),
            Some(vec![DataEntry::Number(0), DataEntry::Number(1)])
        );
        assert_eq!(
            iter.next_with_context(&mut ctx),
            Some(vec![DataEntry::Number(1), DataEntry::Number(0)])
        );
        assert_eq!(
            iter.next_with_context(&mut ctx),
            Some(vec![DataEntry::Number(1), DataEntry::Number(1)])
        );
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

        let expectation = vec![[0, 1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 1]]
            .into_iter()
            .map(|v| v.into_iter().map(DataEntry::Number).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let testcase: ParsedTestCase = input.parse().unwrap();

        let mut ctx = EvalContext::new();
        let result = Vec::from_iter(StmtIterator::new(&testcase.stmts, &mut ctx));
        assert_eq!(result, expectation)
    }
}
