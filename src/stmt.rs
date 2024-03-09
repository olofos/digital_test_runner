use crate::eval_context::EvalContext;
use crate::expr::Expr;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stmt {
    Let {
        name: String,
        expr: Expr,
    },
    DataRow(Vec<DataEntry>),
    Loop {
        variable: String,
        max: i64,
        stmts: Vec<Stmt>,
    },
    ResetRandom,
}

impl Stmt {
    fn run(&self, ctx: &mut EvalContext) -> Vec<Vec<DataResult>> {
        match self {
            Self::Let { name, expr } => {
                let value = expr.eval(ctx).unwrap();
                ctx.set(name, value);
                vec![]
            }
            Self::DataRow(entries) => {
                let data = entries
                    .iter()
                    .map(|entry| entry.run(ctx))
                    .flatten()
                    .collect::<Vec<_>>();
                vec![data]
            }
            Self::Loop {
                variable,
                max,
                stmts,
            } => {
                ctx.push_frame();
                let mut result = vec![];
                for i in 0..*max {
                    ctx.set(variable, i);
                    for stmt in stmts {
                        result.extend(stmt.run(ctx));
                    }
                }
                ctx.pop_frame();
                result
            }
            Self::ResetRandom => {
                ctx.reset_random_seed();
                vec![]
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DataEntry {
    Number(i64),
    Expr(Expr),
    Bits { number: u64, expr: Expr },
    X,
    Z,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataResult {
    Number(i64),
    X,
    Z,
}

impl DataEntry {
    fn run(&self, ctx: &mut EvalContext) -> Vec<DataResult> {
        match self {
            Self::Number(n) => vec![DataResult::Number(*n)],
            Self::Expr(expr) => vec![DataResult::Number(expr.eval(ctx).unwrap())],
            Self::Bits { number, expr } => {
                let value = expr.eval(ctx).unwrap();
                (0..*number)
                    .rev()
                    .map(|n| DataResult::Number((value >> n) & 1))
                    .collect::<Vec<_>>()
            }
            Self::X => vec![DataResult::X],
            Self::Z => vec![DataResult::Z],
        }
    }
}

pub struct TestCase {
    pub(crate) signal_names: Vec<String>,
    pub(crate) stmts: Vec<Stmt>,
}

impl FromStr for TestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

impl TestCase {
    pub fn run(&self) -> Vec<Vec<DataResult>> {
        let mut ctx = EvalContext::new();
        self.stmts
            .iter()
            .map(|stmt| stmt.run(&mut ctx))
            .flatten()
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let testcase: TestCase = input.parse().unwrap();
        assert_eq!(testcase.signal_names.len(), 11);
        assert_eq!(testcase.stmts.len(), 7);
    }

    #[test]
    fn run_works() {
        let input = r"
BUS-CLK S         A        B        N ALU-~RESET ALU-AUX   OUT           FLAG DLEN DSUM

let ADD = 0;
let OR  = 1;
let XOR = 2;
let AND = 3;

0       0      0        0        0 0          0         X             X    X    X
0       0      0        0        0 1          0         X             X    X    X

loop (a,2)
loop (b,2)
0       (OR)      (a)      (b)      0 1          0         (a|b)         X    X    X
0       (AND)     (a)      (b)      0 1          0         (a&b)         X    X    X
0       (XOR)     (a)      (b)      0 1          0         (a^b)         X    X    X
0       (ADD)     (a)      (b)      0 1          0         (a+b)         X    X    X
end loop
end loop

";
        let testcase: TestCase = input.parse().unwrap();
        let result = testcase.run();
        for row in result {
            let s = row
                .iter()
                .map(|entry| match entry {
                    DataResult::Number(n) => format!("{n}"),
                    DataResult::X => String::from("X"),
                    DataResult::Z => String::from("Z"),
                })
                .collect::<Vec<_>>()
                .join(" ");
            println!("{s}");
        }
    }
}
