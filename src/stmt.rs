use crate::eval_context::{self, EvalContext};
use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stmt {
    Block {
        stmts: Vec<Stmt>,
    },
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
        inner: Box<Stmt>,
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
pub(crate) enum StmtInnerIterator<'a> {
    Block {
        stmt_iter: std::slice::Iter<'a, Stmt>,
        inner_iter: Option<Box<StmtInnerIterator<'a>>>,
    },
    Simple {
        stmt: &'a Stmt,
    },
    Loop {
        variable: &'a str,
        inner: &'a Stmt,
        value: i64,
        max: i64,
        inner_iter: Option<Box<StmtInnerIterator<'a>>>,
    },
    Empty,
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

impl Stmt {
    pub(crate) fn iter<'a>(&'a self, ctx: &'a mut EvalContext) -> StmtIterator {
        StmtIterator {
            iter: self.inner_iter(),
            ctx,
        }
    }

    pub(crate) fn inner_iter<'a>(&'a self) -> StmtInnerIterator {
        match self {
            Stmt::DataRow { .. } | Stmt::Let { .. } | Stmt::ResetRandom => {
                StmtInnerIterator::Simple { stmt: self }
            }
            Stmt::Block { stmts } => {
                let stmt_iter = stmts.iter();
                StmtInnerIterator::Block {
                    stmt_iter,
                    inner_iter: None,
                }
            }
            Stmt::Loop {
                variable,
                max,
                inner,
            } => StmtInnerIterator::Loop {
                value: 0,
                max: *max,
                inner_iter: None,
                variable: &variable,
                inner,
            },
        }
    }
}

impl<'a> StmtInnerIterator<'a> {
    fn next_with_context<'c>(&'c mut self, ctx: &mut EvalContext) -> Option<Vec<DataEntry>> {
        match self {
            StmtInnerIterator::Block {
                stmt_iter,
                inner_iter,
            } => loop {
                if let Some(it) = inner_iter {
                    if let Some(val) = it.next_with_context(ctx) {
                        return Some(val);
                    } else {
                        *inner_iter = None;
                    }
                } else {
                    if let Some(stmt) = stmt_iter.next() {
                        *inner_iter = Some(Box::new(stmt.inner_iter()));
                    } else {
                        return None;
                    }
                }
            },
            StmtInnerIterator::Simple { stmt } => {
                let result = match stmt {
                    Stmt::Loop { .. } | Stmt::Block { .. } => unreachable!(),
                    Stmt::Let { name, expr } => {
                        let value = expr.eval(ctx).unwrap();
                        ctx.set(name, value);
                        None
                    }
                    Stmt::DataRow { data, line: _ } => {
                        let mut result = vec![];
                        for entry in data {
                            result.extend(entry.eval(ctx));
                        }
                        Some(result)
                    }
                    Stmt::ResetRandom => {
                        ctx.reset_random_seed();
                        None
                    }
                };
                *self = StmtInnerIterator::Empty;
                result
            }
            StmtInnerIterator::Empty => None,
            StmtInnerIterator::Loop {
                variable,
                value,
                max,
                inner,
                inner_iter,
            } => {
                if inner_iter.is_none() && *value == 0 {
                    ctx.push_frame();
                }
                loop {
                    if let Some(it) = inner_iter {
                        if let Some(value) = it.next_with_context(ctx) {
                            return Some(value);
                        } else {
                            *inner_iter = None;
                            *value += 1;
                        }
                    } else {
                        if value < max {
                            *inner_iter = Some(Box::new(inner.inner_iter()));
                            ctx.set(variable, *value)
                        } else {
                            ctx.pop_frame();
                            return None;
                        }
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
            Self::Block { stmts } => {
                for stmt in stmts {
                    stmt.emit_lines(ctx, emit_line)?;
                }
            }
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
                    inner.emit_lines(&mut ctx, emit_line)?;
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
            Self::Block { stmts } => {
                for stmt in stmts.iter().take(stmts.len() - 1) {
                    writeln!(f, "{stmt}")?;
                }
                if let Some(stmt) = stmts.last() {
                    write!(f, "{stmt}")?;
                }
                Ok(())
            }
            Self::Let { name, expr } => {
                write!(f, "let {name} = {expr};")
            }
            Self::Loop {
                variable,
                max,
                inner,
            } => {
                writeln!(f, "loop({variable},{max})")?;
                writeln!(f, "{inner}")?;
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

        let block = Stmt::Block {
            stmts: testcase.stmts,
        };
        let mut iter = block.inner_iter();
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
loop(n,4)
bits(2,n)
end loop
";

        let testcase: ParsedTestCase = input.parse().unwrap();
        assert_eq!(testcase.signal_names.len(), 2);

        let block = Stmt::Block {
            stmts: testcase.stmts,
        };
        let mut ctx = EvalContext::new();
        let mut iter = block.iter(&mut ctx);

        assert_eq!(
            iter.next(),
            Some(vec![DataEntry::Number(0), DataEntry::Number(0),])
        );
        assert_eq!(
            iter.next(),
            Some(vec![DataEntry::Number(0), DataEntry::Number(1)])
        );
        assert_eq!(
            iter.next(),
            Some(vec![DataEntry::Number(1), DataEntry::Number(0)])
        );
        assert_eq!(
            iter.next(),
            Some(vec![DataEntry::Number(1), DataEntry::Number(1)])
        );
    }
}
