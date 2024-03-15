use crate::eval_context::EvalContext;
use crate::expr::{BinOp, Expr};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Stmt {
    Let {
        name: String,
        expr: Expr,
        line: u32,
    },
    DataRow {
        entries: Vec<DataEntry>,
        line: u32,
    },
    Loop {
        variable: String,
        max: i64,
        stmts: Vec<Stmt>,
        line: u32,
    },
    ResetRandom {
        line: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OrderedStmt {
    Let {
        name: String,
        expr: Expr,
        line: u32,
    },
    DataRow {
        inputs: Vec<DataEntry>,
        outputs: Vec<DataEntry>,
        line: u32,
    },
    Loop {
        variable: String,
        max: i64,
        stmts: Vec<OrderedStmt>,
        line: u32,
    },
    ResetRandom {
        line: u32,
    },
}

pub(crate) fn map_data_rows(
    stmts: Vec<Stmt>,
    mut f: impl FnMut(Vec<DataEntry>, u32) -> Vec<Stmt> + Clone,
) -> Vec<Stmt> {
    let mut result = Vec::with_capacity(stmts.len());

    for stmt in stmts {
        match stmt {
            Stmt::Loop {
                variable,
                max,
                stmts,
                line,
            } => result.push(Stmt::Loop {
                variable,
                max,
                stmts: map_data_rows(stmts, f.clone()),
                line,
            }),
            Stmt::DataRow {
                entries: orig_entries,
                line,
            } => {
                result.extend(f(orig_entries, line));
            }
            _ => result.push(stmt),
        }
    }

    result
}

pub(crate) fn expand_bits(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let mut temp_number = 0;

    map_data_rows(stmts, move |orig_entries, line| {
        let mut entries = Vec::with_capacity(orig_entries.len());
        let mut vars: Vec<(String, Expr)> = vec![];
        let mut result = vec![];
        for entry in orig_entries {
            match entry {
                DataEntry::Bits { number, expr } => {
                    let name = format!("#{temp_number}");
                    temp_number += 1;
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
                    vars.push((name, expr));
                }
                _ => entries.push(entry),
            }
        }
        for (name, expr) in vars {
            result.push(Stmt::Let { name, expr, line });
        }
        result.push(Stmt::DataRow { entries, line });
        result
    })
}

pub(crate) fn expand_input_x(stmts: Vec<Stmt>, input_indices: &[usize]) -> Vec<Stmt> {
    map_data_rows(stmts, |orig_entries, line| {
        let x_positions = input_indices
            .iter()
            .filter_map(|&i| {
                if orig_entries[i] == DataEntry::X {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        let mut row_result = vec![orig_entries; 1 << x_positions.len()];

        for (x_index, pos) in x_positions.into_iter().enumerate() {
            for (row_index, row) in row_result.iter_mut().enumerate() {
                row[pos] = DataEntry::Number(((row_index >> x_index) & 1) as i64);
            }
        }
        row_result
            .into_iter()
            .map(|entries| Stmt::DataRow { entries, line })
            .collect()
    })
}

pub(crate) fn expand_input_c(
    stmts: Vec<Stmt>,
    input_indices: &[usize],
    output_indices: &[usize],
) -> Vec<Stmt> {
    map_data_rows(stmts, |orig_entries, line| {
        let c_positions = input_indices
            .iter()
            .filter_map(|&i| {
                if orig_entries[i] == DataEntry::C {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if c_positions.is_empty() {
            return vec![Stmt::DataRow {
                entries: orig_entries,
                line,
            }];
        }

        let mut row_result = vec![orig_entries; 3];

        for i in c_positions {
            row_result[0][i] = DataEntry::Number(0);
            row_result[1][i] = DataEntry::Number(1);
            row_result[2][i] = DataEntry::Number(0);
        }

        for &i in output_indices {
            row_result[0][i] = DataEntry::X;
            row_result[1][i] = DataEntry::X;
        }

        row_result
            .into_iter()
            .map(|entries| Stmt::DataRow { entries, line })
            .collect()
    })
}

fn to_ordered(stmts: Vec<Stmt>, input_len: usize) -> Vec<OrderedStmt> {
    let mut result = Vec::with_capacity(stmts.len());

    for stmt in stmts {
        result.push(match stmt {
            Stmt::Let { name, expr, line } => OrderedStmt::Let { name, expr, line },
            Stmt::ResetRandom { line } => OrderedStmt::ResetRandom { line },
            Stmt::Loop {
                variable,
                max,
                stmts,
                line,
            } => OrderedStmt::Loop {
                variable,
                max,
                stmts: to_ordered(stmts, input_len),
                line,
            },
            Stmt::DataRow { mut entries, line } => {
                let outputs = entries.split_off(input_len);
                let inputs = entries;
                OrderedStmt::DataRow {
                    inputs,
                    outputs,
                    line,
                }
            }
        });
    }

    result
}

pub(crate) fn reorder(
    stmts: Vec<Stmt>,
    input_indices: &[usize],
    output_indices: &[usize],
) -> Vec<OrderedStmt> {
    let stmts = map_data_rows(stmts, |mut orig_entries, line| {
        let dummy = DataEntry::X;
        if orig_entries.len() != input_indices.len() + output_indices.len() {
            panic!("Wrong length data row");
        }
        let mut entries = Vec::with_capacity(orig_entries.len());
        for &i in input_indices {
            entries.push(std::mem::replace(&mut orig_entries[i], dummy.clone()));
        }
        for &i in output_indices {
            entries.push(std::mem::replace(&mut orig_entries[i], dummy.clone()));
        }

        vec![Stmt::DataRow { entries, line }]
    });

    to_ordered(stmts, input_indices.len())
}

impl Stmt {
    pub(crate) fn run(&self, ctx: &mut EvalContext) -> Vec<Vec<DataResult>> {
        match self {
            Self::Let {
                name,
                expr,
                line: _,
            } => {
                let value = expr.eval(ctx).unwrap();
                ctx.set(name, value);
                vec![]
            }
            Self::DataRow { entries, line: _ } => {
                let data = entries
                    .iter()
                    .flat_map(|entry| entry.run(ctx))
                    .collect::<Vec<_>>();
                vec![data]
            }
            Self::Loop {
                variable,
                max,
                stmts,
                line: _,
            } => ctx.new_frame(|ctx| {
                let mut result = vec![];
                for i in 0..*max {
                    ctx.set(variable, i);
                    for stmt in stmts {
                        result.extend(stmt.run(ctx));
                    }
                }
                result
            }),
            Self::ResetRandom { line: _ } => {
                ctx.reset_random_seed();
                vec![]
            }
        }
    }
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let {
                name,
                expr,
                line: _,
            } => {
                write!(f, "let {name} = {expr};")
            }
            Self::Loop {
                variable,
                max,
                stmts,
                line: _,
            } => {
                writeln!(f, "loop({variable},{max})")?;
                for stmt in stmts {
                    writeln!(f, "{stmt}")?;
                }
                write!(f, "end loop")
            }
            Self::ResetRandom { line: _ } => {
                write!(f, "resetRandom;")
            }
            Self::DataRow { entries, line: _ } => {
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

impl std::fmt::Display for OrderedStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let {
                name,
                expr,
                line: _,
            } => {
                write!(f, "let {name} = {expr};")
            }
            Self::Loop {
                variable,
                max,
                stmts,
                line: _,
            } => {
                writeln!(f, "loop({variable},{max})")?;
                for stmt in stmts {
                    writeln!(f, "{stmt}")?;
                }
                write!(f, "end loop")
            }
            Self::ResetRandom { line: _ } => {
                write!(f, "resetRandom;")
            }
            Self::DataRow {
                inputs,
                outputs,
                line: _,
            } => {
                let s = inputs
                    .iter()
                    .chain(outputs.iter())
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
    C,
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
            Self::C => unimplemented!(),
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
        assert!(matches!(expanded[0], Stmt::Let { .. }));
        assert!(matches!(expanded[1], Stmt::Let { .. }));
        match &expanded[2] {
            Stmt::DataRow { entries, .. } => {
                assert_eq!(entries.len(), 4);
            }
            _ => panic!("Expected a data row"),
        }
        assert!(matches!(expanded[3], Stmt::Let { .. }));
        match &expanded[4] {
            Stmt::DataRow { entries, .. } => {
                assert_eq!(entries.len(), 4);
            }
            _ => panic!("Expected a data row"),
        }
        for stmt in expanded {
            println!("{stmt}");
        }
    }

    #[test]
    fn reorder_works() {
        let input = "A B C D\n0 0 0 0\n0 0 0 1\n0 0 1 0\n0 0 1 1\n0 1 0 0\n0 1 0 1\n0 1 1 0\n0 1 1 1\n1 0 0 0\n1 0 0 1\n1 0 1 0\n1 0 1 1\n1 1 0 0\n1 1 0 1\n1 1 1 0\n1 1 1 1\n";
        let testcase: ParsedTestCase = input.parse().unwrap();

        let input_expected = "A C B D\n0 0 0 0\n0 0 0 1\n0 1 0 0\n0 1 0 1\n0 0 1 0\n0 0 1 1\n0 1 1 0\n0 1 1 1\n1 0 0 0\n1 0 0 1\n1 1 0 0\n1 1 0 1\n1 0 1 0\n1 0 1 1\n1 1 1 0\n1 1 1 1\n";
        let expected = input_expected.parse::<ParsedTestCase>().unwrap().stmts;
        let stmts = reorder(testcase.stmts.clone(), &[0, 2], &[1, 3]);
        for (stmt, expected) in stmts.into_iter().zip(expected.into_iter()) {
            assert_eq!(format!("{stmt}"), format!("{expected}"));
        }

        let input_expected = "B D C A\n0 0 0 0\n0 1 0 0\n0 0 1 0\n0 1 1 0\n1 0 0 0\n1 1 0 0\n1 0 1 0\n1 1 1 0\n0 0 0 1\n0 1 0 1\n0 0 1 1\n0 1 1 1\n1 0 0 1\n1 1 0 1\n1 0 1 1\n1 1 1 1\n";
        let expected = input_expected.parse::<ParsedTestCase>().unwrap().stmts;
        let stmts = reorder(testcase.stmts.clone(), &[1, 3], &[2, 0]);
        for (stmt, expected) in stmts.into_iter().zip(expected.into_iter()) {
            assert_eq!(format!("{stmt}"), format!("{expected}"));
        }
    }

    #[test]
    fn expand_input_x_works() {
        let input = r#"A B C D
X 0 X 0
"#;
        let testcase: ParsedTestCase = input.parse().unwrap();
        let expanded = expand_input_x(testcase.stmts, &[0, 2]);
        assert_eq!(expanded.len(), 4);
        assert_eq!(
            expanded,
            vec![
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(0),
                        DataEntry::Number(0),
                        DataEntry::Number(0),
                        DataEntry::Number(0)
                    ],
                    line: 2
                },
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(1),
                        DataEntry::Number(0),
                        DataEntry::Number(0),
                        DataEntry::Number(0)
                    ],
                    line: 2
                },
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(0),
                        DataEntry::Number(0),
                        DataEntry::Number(1),
                        DataEntry::Number(0)
                    ],
                    line: 2
                },
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(1),
                        DataEntry::Number(0),
                        DataEntry::Number(1),
                        DataEntry::Number(0)
                    ],
                    line: 2
                }
            ]
        );
    }

    #[test]
    fn expand_input_c_works() {
        let input = r#"A B C D
C 0 1 1
"#;
        let testcase: ParsedTestCase = input.parse().unwrap();
        let expanded = expand_input_c(testcase.stmts, &[0, 2], &[1, 3]);
        assert_eq!(expanded.len(), 3);
        assert_eq!(
            expanded,
            vec![
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(0),
                        DataEntry::X,
                        DataEntry::Number(1),
                        DataEntry::X
                    ],
                    line: 2
                },
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(1),
                        DataEntry::X,
                        DataEntry::Number(1),
                        DataEntry::X
                    ],
                    line: 2
                },
                Stmt::DataRow {
                    entries: vec![
                        DataEntry::Number(0),
                        DataEntry::Number(0),
                        DataEntry::Number(1),
                        DataEntry::Number(1)
                    ],
                    line: 2
                },
            ]
        );
    }
}
