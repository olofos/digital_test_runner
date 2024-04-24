use std::collections::HashSet;

use crate::expr::Expr;
use crate::framed_map::FramedSet;
use crate::stmt::{DataEntry, Stmt};
use crate::Signal;

#[derive(Debug)]
pub(crate) struct CheckContext<'a> {
    vars: FramedSet<String>,
    unknown_vars: HashSet<String>,
    signals: &'a [Signal],
}

impl<'a> CheckContext<'a> {
    fn new(signals: &'a [Signal]) -> Self {
        Self {
            vars: Default::default(),
            unknown_vars: Default::default(),
            signals,
        }
    }

    fn define_var(&mut self, name: &String) {
        self.vars.insert(name)
    }

    fn access_var(&mut self, name: &String) {
        if !self.vars.contains(name) {
            self.unknown_vars.insert(name.clone());
        }
    }
}

impl Stmt {
    pub(crate) fn check(&self, ctx: &mut CheckContext) -> anyhow::Result<()> {
        match self {
            Stmt::Let { name, expr } => {
                expr.check(ctx)?;
                ctx.define_var(name)
            }
            Stmt::DataRow { data, line } => {
                for entry in data {
                    match entry {
                        DataEntry::Number(_) | DataEntry::X | DataEntry::Z | DataEntry::C => {}
                        DataEntry::Expr(expr) => expr.check(ctx)?,
                        DataEntry::Bits { number: _, expr } => expr.check(ctx)?,
                    }
                }
                let len: usize = data
                    .iter()
                    .map(|entry| match entry {
                        DataEntry::Number(_)
                        | DataEntry::Expr(_)
                        | DataEntry::X
                        | DataEntry::Z
                        | DataEntry::C => 1,
                        DataEntry::Bits { number, expr: _ } => *number as usize,
                    })
                    .sum();
                if len != ctx.signals.len() {
                    anyhow::bail!(
                        "Error on line {line}: expected {} entries but found {len}",
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

impl Expr {
    pub(crate) fn check(&self, ctx: &mut CheckContext) -> anyhow::Result<()> {
        match self {
            Expr::Number(_) => {}
            Expr::Variable(var) => {
                ctx.access_var(var);
            }
            Expr::BinOp { op: _, left, right } => {
                left.check(ctx)?;
                right.check(ctx)?;
            }
            Expr::UnaryOp { op: _, expr } => {
                expr.check(ctx)?;
            }
            Expr::Func { name, params } => {
                if !["ite", "random", "signExt"].contains(&name.as_str()) {
                    anyhow::bail!("Unknown function {name}");
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
    fn check_returns_error(#[case] input: &str) {
        let testcase: TestCase<String> = input.parse().unwrap();
        let signals = vec![
            Signal::input("A", 1, InputValue::Value(1)),
            Signal::output("B", 1),
        ];

        let mut ctx = CheckContext::new(&signals);
        let result = testcase.stmts[0].check(&mut ctx);
        assert!(result.is_err())
    }

    #[test]
    fn check_works() {
        let input = r#"
A B
let C = 1;
let D = 2;
(A+C) 1
loop (n,2)
let E = 1;
(n+C) (D+E)
end loop
(n) 1
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
        assert_eq!(
            ctx.unknown_vars,
            HashSet::from_iter(["A", "n"].into_iter().map(String::from))
        )
    }
}
