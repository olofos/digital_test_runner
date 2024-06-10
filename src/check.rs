use crate::expr::{Expr, FUNC_TABLE};
use crate::framed_map::FramedSet;
use crate::stmt::{DataEntry, Stmt};
use crate::{EntryIndex, Signal};

#[derive(Debug)]
pub(crate) struct CheckContext<'a> {
    vars: FramedSet<String>,
    signals: &'a [Signal],
    entry_indices: &'a [EntryIndex],
    pub is_static: bool,
}

pub trait TestCheck<'a> {
    fn check(&self, signals: &'a [Signal], entry_indices: &'a [EntryIndex])
        -> anyhow::Result<bool>;
}

impl<'a> TestCheck<'a> for Vec<Stmt> {
    fn check(
        &self,
        signals: &'a [Signal],
        entry_indices: &'a [EntryIndex],
    ) -> anyhow::Result<bool> {
        let mut ctx = CheckContext::new(signals, entry_indices);
        for stmt in self {
            stmt.check(&mut ctx)?;
        }
        Ok(ctx.is_static)
    }
}

impl<'a> CheckContext<'a> {
    pub fn new(signals: &'a [Signal], entry_indices: &'a [EntryIndex]) -> Self {
        Self {
            vars: FramedSet::new(),
            signals,
            entry_indices,
            is_static: true,
        }
    }

    fn define_var(&mut self, name: &String) {
        self.vars.insert(name)
    }

    fn check_var(&mut self, name: &String) -> anyhow::Result<()> {
        if !self.vars.contains(name) {
            if self
                .entry_indices
                .iter()
                .any(|entry| entry.is_output() && self.signals[entry.index].name == *name)
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
    pub(crate) fn check(&self, ctx: &mut CheckContext) -> anyhow::Result<()> {
        match self {
            Stmt::Let { name, expr } => {
                expr.check(ctx)?;
                ctx.define_var(name);
            }
            Stmt::DataRow { data, line } => {
                let mut index = 0;
                for entry in data {
                    index += match entry {
                        DataEntry::Number(_) | DataEntry::X | DataEntry::Z => 1,
                        DataEntry::C => {
                            if !ctx.entry_indices[index].is_input() {
                                anyhow::bail!(
                                    "Unexpected C for output signal {} on line {line}",
                                    ctx.signals[ctx.entry_indices[index].index].name
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
                if index != ctx.entry_indices.len() {
                    anyhow::bail!(
                        "Error on line {line}: expected {} entries but found {index}",
                        ctx.entry_indices.len()
                    );
                }
            }
            Stmt::Loop {
                variable,
                max,
                inner,
            } => {
                if !max.is_const() {
                    anyhow::bail!("Loop bound for {variable} should be constant");
                }
                ctx.vars.push_frame();
                ctx.define_var(variable);
                for stmt in inner {
                    stmt.check(ctx)?;
                }
                ctx.vars.pop_frame();
            }
            Stmt::ResetRandom => {}
        }
        Ok(())
    }
}

impl Expr {
    pub(crate) fn check(&self, ctx: &mut CheckContext) -> anyhow::Result<()> {
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

    fn is_const(&self) -> bool {
        match self {
            Expr::Number(_) => true,
            Expr::Variable(_) => false,
            Expr::BinOp { op: _, left, right } => left.is_const() && right.is_const(),
            Expr::UnaryOp { op: _, expr } => expr.is_const(),
            Expr::Func { name: _, args: _ } => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EntryDirection, InputValue, ParsedTestCase};
    use rstest::rstest;

    fn output_signal(name: impl Into<String>, bits: u8) -> Signal {
        Signal {
            name: name.into(),
            bits,
            dir: crate::SignalDirection::Output,
        }
    }

    fn input_signal(name: impl Into<String>, bits: u8, default: InputValue) -> Signal {
        Signal {
            name: name.into(),
            bits,
            dir: crate::SignalDirection::Input { default },
        }
    }

    fn make_entry_indices(signals: &[Signal]) -> Vec<EntryIndex> {
        signals
            .iter()
            .enumerate()
            .map(|(index, sig)| {
                let dir = match sig.dir {
                    crate::SignalDirection::Input { .. } => EntryDirection::Input,
                    crate::SignalDirection::Output => EntryDirection::Output,
                    crate::SignalDirection::Bidirectional { .. } => unimplemented!(),
                };
                EntryIndex { index, dir }
            })
            .collect::<Vec<_>>()
    }

    #[rstest]
    #[case("A B\n1 1 1\n")]
    #[case("A B\nbits(2,11) 1\n")]
    #[case("A B\n(1+f(1)) 1\n")]
    #[case("A B\n(C) 1\n")]
    #[case("A B\n(A) 1\n")]
    #[case("A B\nloop (C,2)\n1 1\nend loop\n(C) 1\n")]
    #[case("A B\nbits(2,D)\n")]
    #[case("A B\n1 C\n")]
    #[case("A B\nlet x = random(1,2,3);\n")]
    #[case("A B\nlet m = 2;\nloop (i,m)\nend loop\n")]
    fn check_returns_error(#[case] input: &str) {
        let testcase: ParsedTestCase = input.parse().unwrap();
        let signals = vec![
            input_signal("A", 1, InputValue::Value(1)),
            output_signal("B", 1),
        ];
        let entry_indices = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &entry_indices);
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

        let entry_indices = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &entry_indices);
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

        let entry_indices = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &entry_indices);
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

        let entry_indices = make_entry_indices(&signals);
        let mut ctx = CheckContext::new(&signals, &entry_indices);
        for stmt in testcase.stmts {
            stmt.check(&mut ctx).unwrap();
        }
        assert!(!ctx.is_static);
    }
}
