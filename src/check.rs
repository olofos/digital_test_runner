use crate::expr::Expr;
use crate::framed_map::FramedSet;
use crate::stmt::{DataEntry, Stmt};
use crate::Signal;

#[derive(Debug)]
pub(crate) struct CheckContext<'a> {
    vars: FramedSet<String>,
    signals: &'a [Signal],
}

impl<'a> CheckContext<'a> {
    fn new(signals: &'a [Signal]) -> Self {
        Self {
            vars: Default::default(),
            signals,
        }
    }

    fn define_var(&mut self, name: &String) {
        self.vars.insert(name)
    }

    fn check_var(&mut self, name: &String) -> anyhow::Result<()> {
        if !self.vars.contains(name) {
            if !self
                .signals
                .iter()
                .any(|sig| sig.is_output() && sig.name == *name)
            {
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
                            if !ctx.signals[index].is_input() {
                                anyhow::bail!(
                                    "Unexpected C for output signal {} on line {line}",
                                    ctx.signals[index].name
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
                if index != ctx.signals.len() {
                    anyhow::bail!(
                        "Error on line {line}: expected {} entries but found {index}",
                        ctx.signals.len()
                    );
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
        }
        Ok(())
    }
}

const FUNC_TABLE: &[(&str, usize)] = &[("ite", 3), ("random", 1), ("signExt", 1)];

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
            Expr::Func { name, params } => {
                let Some(expected_param_len) =
                    FUNC_TABLE.iter().find_map(
                        |(func_name, len)| if *func_name == name { Some(*len) } else { None },
                    )
                else {
                    anyhow::bail!("Unknown function {name}");
                };

                if params.len() != expected_param_len {
                    anyhow::bail!(
                        "Function {name} has {expected_param_len} parameters but got {}",
                        params.len()
                    );
                }

                for expr in params {
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
    use crate::{InputValue, TestCase};
    use rstest::rstest;

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
    fn check_returns_error(#[case] input: &str) {
        let testcase: TestCase<String> = input.parse().unwrap();
        let signals = vec![
            Signal::input("A", 1, InputValue::Value(1)),
            Signal::output("B", 1),
        ];

        let mut ctx = CheckContext::new(&signals);
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
loop (n,2)
let E = 1;
(n+C) (D+E)
end loop
(C) (D)
C 1
"#;
        let testcase: TestCase<String> = input.parse().unwrap();
        let signals = vec![
            Signal::input("A", 1, InputValue::Value(1)),
            Signal::output("B", 1),
        ];

        let mut ctx = CheckContext::new(&signals);
        for stmt in testcase.stmts {
            stmt.check(&mut ctx).unwrap();
        }
    }
}
