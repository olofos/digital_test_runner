use crate::expr::{Expr, FUNC_TABLE};
use crate::framed_map::FramedSet;
use crate::stmt::{DataEntry, Stmt};
use crate::{EntryIndex, Signal};

#[derive(Debug)]
pub(crate) struct CheckContext<'a> {
    vars: FramedSet<String>,
    signals: &'a [Signal],
    input_indices: &'a [EntryIndex],
    expected_indices: &'a [EntryIndex],
    pub(crate) is_static: bool,
}

pub(crate) trait TestCheck<'a> {
    fn check(
        &self,
        signals: &'a [Signal],
        input_indices: &'a [EntryIndex],
        expected_indices: &'a [EntryIndex],
    ) -> anyhow::Result<bool>;
}

impl<'a> TestCheck<'a> for Vec<Stmt> {
    fn check(
        &self,
        signals: &'a [Signal],
        input_indices: &'a [EntryIndex],
        expected_indices: &'a [EntryIndex],
    ) -> anyhow::Result<bool> {
        let mut ctx = CheckContext::new(signals, input_indices, expected_indices);
        for stmt in self {
            stmt.check(&mut ctx)?;
        }
        Ok(ctx.is_static)
    }
}

impl<'a> CheckContext<'a> {
    pub(crate) fn new(
        signals: &'a [Signal],
        input_indices: &'a [EntryIndex],
        expected_indices: &'a [EntryIndex],
    ) -> Self {
        Self {
            vars: FramedSet::new(),
            signals,
            input_indices,
            expected_indices,
            is_static: true,
        }
    }

    fn define_var(&mut self, name: &String) {
        self.vars.insert(name)
    }

    fn check_var(&mut self, name: &String) -> anyhow::Result<()> {
        if !self.vars.contains(name) {
            if self
                .expected_indices
                .iter()
                .any(|index| self.signals[index.signal_index()].name == *name)
            {
                self.is_static = false;
            } else {
                anyhow::bail!("Unknown variable {name}");
            }
        }
        Ok(())
    }
}

impl Stmt {
    pub(crate) fn check(&self, ctx: &mut CheckContext<'_>) -> anyhow::Result<()> {
        match self {
            Stmt::Let { name, expr } => {
                expr.check(ctx)?;
                ctx.define_var(name);
            }
            Stmt::DataRow { data, line } => {
                let mut entry_index = 0;
                for entry in data {
                    entry_index += match entry {
                        DataEntry::Number(_) | DataEntry::X | DataEntry::Z => 1,
                        DataEntry::C => {
                            if !ctx
                                .input_indices
                                .iter()
                                .any(|entry| entry.indexes(entry_index))
                            {
                                let signal_index = ctx
                                    .expected_indices
                                    .iter()
                                    .find(|entry| entry.indexes(entry_index))
                                    .unwrap()
                                    .signal_index();
                                anyhow::bail!(
                                    "Unexpected C for output signal {} on line {line}",
                                    ctx.signals[signal_index].name
                                );
                            }
                            1
                        }
                        DataEntry::Expr(expr) => {
                            expr.check(ctx)?;
                            1
                        }
                        DataEntry::Bits { number, expr } => {
                            expr.check(ctx)?;
                            *number as usize
                        }
                    }
                }
            }
            Stmt::Loop {
                variable,
                max: _,
                inner,
            } => {
                ctx.vars.push_frame();
                ctx.define_var(variable);
                for stmt in inner {
                    stmt.check(ctx)?;
                }
                ctx.vars.pop_frame();
            }
            Stmt::ResetRandom => {}
            Stmt::While { condition, inner } => {
                condition.check(ctx)?;
                for stmt in inner {
                    stmt.check(ctx)?;
                }
            }
        }
        Ok(())
    }
}

impl Expr {
    pub(crate) fn check(&self, ctx: &mut CheckContext<'_>) -> anyhow::Result<()> {
        match self {
            Expr::Number(_) => {}
            Expr::Variable(var) => {
                ctx.check_var(var)?;
            }
            Expr::BinOp { op: _, left, right } => {
                left.check(ctx)?;
                right.check(ctx)?;
            }
            Expr::UnaryOp { op: _, expr } => {
                expr.check(ctx)?;
            }
            Expr::Func { name, args } => {
                let Some(expected_args_len) =
                    FUNC_TABLE.get(name).map(|entry| entry.number_of_args)
                else {
                    anyhow::bail!("Unknown function {name}");
                };

                if args.len() != expected_args_len {
                    anyhow::bail!(
                        "Function {name} has {expected_args_len} arguments but got {}",
                        args.len()
                    );
                }

                for expr in args {
                    expr.check(ctx)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InputValue, ParsedTestCase};
    use rstest::rstest;

    fn output_signal(name: impl Into<String>, bits: usize) -> Signal {
        Signal {
            name: name.into(),
            bits,
            dir: crate::SignalDirection::Output,
        }
    }

    fn input_signal(name: impl Into<String>, bits: usize, default: InputValue) -> Signal {
        Signal {
            name: name.into(),
            bits,
            dir: crate::SignalDirection::Input { default },
        }
    }

    fn make_entry_indices(signals: &[Signal]) -> (Vec<EntryIndex>, Vec<EntryIndex>) {
        let mut input_indices = vec![];
        let mut expected_indices = vec![];
        for (index, signal) in signals.iter().enumerate() {
            match signal.dir {
                crate::SignalDirection::Input { .. } => input_indices.push(EntryIndex::Entry {
                    entry_index: index,
                    signal_index: index,
                }),
                crate::SignalDirection::Output => expected_indices.push(EntryIndex::Entry {
                    entry_index: index,
                    signal_index: index,
                }),
                crate::SignalDirection::Bidirectional { .. } => unimplemented!(),
            }
        }
        (input_indices, expected_indices)
    }

    #[rstest]
    #[case("A B\n(1+f(1)) 1\n")]
    #[case("A B\n(C) 1\n")]
    #[case("A B\n(A) 1\n")]
    #[case("A B\nloop (C,2)\n1 1\nend loop\n(C) 1\n")]
    #[case("A B\nbits(2,D)\n")]
    #[case("A B\n1 C\n")]
    #[case("A B\nlet x = random(1,2,3);\n")]
    fn check_returns_error(#[case] input: &str) {
        let testcase: ParsedTestCase = input.parse().unwrap();
        let signals = vec![
            input_signal("A", 1, InputValue::Value(1)),
            output_signal("B", 1),
        ];
        let (input_indices, expected_indices) = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &input_indices, &expected_indices);
        let result: anyhow::Result<Vec<_>> = testcase
            .stmts
            .into_iter()
            .map(|stmt| stmt.check(&mut ctx))
            .collect();
        assert!(result.is_err());
    }

    #[test]
    fn check_works() {
        let input = r#"
    A B
    let C = 1;
    let D = 2;
    (B+C) 1
    loop (n,1+1)
    let E = 1;
    (n+C) (D+E)
    end loop
    (C) (D)
    C 1
    "#;
        let testcase: ParsedTestCase = input.parse().unwrap();
        let signals = vec![
            input_signal("A", 1, InputValue::Value(1)),
            output_signal("B", 1),
        ];

        let (input_indices, expected_indices) = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &input_indices, &expected_indices);
        for stmt in testcase.stmts {
            stmt.check(&mut ctx).unwrap();
        }
    }

    #[test]
    fn check_sets_is_static_to_true_for_static_test() {
        let input = r"
    A B
    loop (B,1)
    (B) (B)
    end loop
    ";
        let testcase: ParsedTestCase = input.parse().unwrap();
        let signals = vec![
            input_signal("A", 1, InputValue::Value(1)),
            output_signal("B", 1),
        ];

        let (input_indices, expected_indices) = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &input_indices, &expected_indices);
        for stmt in testcase.stmts {
            stmt.check(&mut ctx).unwrap();
        }
        assert!(ctx.is_static);
    }

    #[test]
    fn check_sets_is_static_to_false_for_dynamic_test() {
        let input = r"
    A B
    loop (B,1)
    (B) (B)
    end loop
    (B) (B)
    ";
        let testcase: ParsedTestCase = input.parse().unwrap();
        let signals = vec![
            input_signal("A", 1, InputValue::Value(1)),
            output_signal("B", 1),
        ];

        let (input_indices, expected_indices) = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &input_indices, &expected_indices);
        for stmt in testcase.stmts {
            stmt.check(&mut ctx).unwrap();
        }
        assert!(!ctx.is_static);
    }
}
