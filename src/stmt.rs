use crate::eval_context::EvalContext;
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
}
