use crate::eval_context::EvalContext;
use crate::expr::{BinOp, Expr};

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

fn expand_bits(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let mut result = Vec::with_capacity(stmts.len());
    let mut temp_number = 0;

    for stmt in stmts {
        match stmt {
            Stmt::Loop {
                variable,
                max,
                stmts,
            } => result.push(Stmt::Loop {
                variable,
                max,
                stmts: expand_bits(stmts),
            }),
            Stmt::DataRow(orig_entries) => {
                let mut entries = Vec::with_capacity(orig_entries.len());
                let mut vars: Vec<(String, Expr)> = vec![];
                for entry in orig_entries {
                    match entry {
                        DataEntry::Bits { number, expr } => {
                            let name = format!("#{temp_number}");
                            temp_number += 1;
                            vars.push((name.clone(), expr));
                            for i in 0..number {
                                let left = Expr::BinOp {
                                    op: BinOp::ShiftRight,
                                    left: Box::new(Expr::Variable(name.clone())),
                                    right: Box::new(Expr::Number(i as i64)),
                                };
                                let expr = Expr::BinOp {
                                    op: BinOp::And,
                                    left: Box::new(left),
                                    right: Box::new(Expr::Number(1)),
                                };
                                entries.push(DataEntry::Expr(expr));
                            }
                        }
                        _ => entries.push(entry),
                    }
                }
                for (name, expr) in vars {
                    result.push(Stmt::Let { name, expr });
                }
                result.push(Stmt::DataRow(entries))
            }
            _ => result.push(stmt),
        }
    }

    result
}

impl Stmt {
    pub(crate) fn run(&self, ctx: &mut EvalContext) -> Vec<Vec<DataResult>> {
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

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let { name, expr } => {
                write!(f, "let {name} = {expr};")
            }
            Self::Loop {
                variable,
                max,
                stmts,
            } => {
                writeln!(f, "loop({variable},{max})")?;
                for stmt in stmts {
                    writeln!(f, "  {stmt}")?;
                }
                write!(f, "end loop")
            }
            Self::ResetRandom => {
                write!(f, "resetRandom;")
            }
            Self::DataRow(entries) => {
                let s = entries
                    .iter()
                    .map(|entry| format!("{entry}"))
                    .collect::<Vec<_>>()
                    .join(" ");
                write!(f, "{s}")
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
        let testcase: ParsedTestCase = input.parse().unwrap();
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

    #[test]
    fn expand_bits_works() {
        let input = r#"A B C D
bits(2,0b10) bits(2,0b10)
bits(4,0b1010)
"#;
        let testcase: ParsedTestCase = input.parse().unwrap();
        let expanded = expand_bits(testcase.stmts);
        assert_eq!(expanded.len(), 5);
        assert!(matches!(expanded[0], Stmt::Let { name: _, expr: _ }));
        assert!(matches!(expanded[1], Stmt::Let { name: _, expr: _ }));
        match &expanded[2] {
            Stmt::DataRow(entries) => {
                assert_eq!(entries.len(), 4);
            }
            _ => panic!("Expected a data row"),
        }
        assert!(matches!(expanded[3], Stmt::Let { name: _, expr: _ }));
        match &expanded[4] {
            Stmt::DataRow(entries) => {
                assert_eq!(entries.len(), 4);
            }
            _ => panic!("Expected a data row"),
        }
        for stmt in expanded {
            println!("{stmt}");
        }
    }
}
