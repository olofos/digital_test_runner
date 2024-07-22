use crate::eval_context::EvalContext;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOp {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    Or,
    Xor,
    And,
    ShiftLeft,
    ShiftRight,
    Plus,
    Minus,
    Times,
    Divide,
    Reminder,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Equal => "=",
            Self::NotEqual => "!=",
            Self::GreaterThan => ">",
            Self::LessThan => "<",
            Self::GreaterThanOrEqual => ">=",
            Self::LessThanOrEqual => "<=",
            Self::Or => "|",
            Self::Xor => "^",
            Self::And => "&",
            Self::ShiftLeft => "<<",
            Self::ShiftRight => ">>",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Times => "*",
            Self::Divide => "/",
            Self::Reminder => "%",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UnaryOp {
    Minus,
    LogicalNot,
    BinaryNot,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Minus => "-",
            Self::LogicalNot => "!",
            Self::BinaryNot => "~",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expr {
    Number(i64),
    Variable(String),
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Func {
        name: String,
        args: Vec<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::Variable(s) => write!(f, "{s}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::UnaryOp { op, expr } => write!(f, "{op}{expr}"),
            Self::Func { name, args } => {
                let args = args
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{name}({args})")
            }
        }
    }
}

pub(crate) struct FuncTableEntry {
    pub(crate) name: &'static str,
    pub(crate) number_of_args: usize,
    f: fn(&EvalContext, &[Expr]) -> i64,
}

pub(crate) struct FuncTable {
    entries: &'static [FuncTableEntry],
}

impl FuncTable {
    pub(crate) fn get(&self, name: &str) -> Option<&FuncTableEntry> {
        self.entries.iter().find(|entry| entry.name == name)
    }
}

pub(crate) const FUNC_TABLE: FuncTable = FuncTable {
    entries: &[
        FuncTableEntry {
            name: "random",
            number_of_args: 1,
            f: func_random,
        },
        FuncTableEntry {
            name: "ite",
            number_of_args: 3,
            f: func_ite,
        },
        FuncTableEntry {
            name: "signExt",
            number_of_args: 2,
            f: func_sign_ext,
        },
    ],
};

fn func_random(ctx: &EvalContext, args: &[Expr]) -> i64 {
    let max = args[0].eval(ctx);
    ctx.random(1..max)
}

fn func_ite(ctx: &EvalContext, args: &[Expr]) -> i64 {
    let test = args[0].eval(ctx);
    if test == 0 {
        args[2].eval(ctx)
    } else {
        args[1].eval(ctx)
    }
}

fn func_sign_ext(_ctx: &EvalContext, _args: &[Expr]) -> i64 {
    todo!("signExt")
}

impl Expr {
    pub(crate) fn eval(&self, ctx: &EvalContext) -> i64 {
        match self {
            Self::Number(n) => *n,
            Self::Variable(name) => ctx
                .get(name)
                .expect("Variable {name} not found. This should have been found at parse time"),
            Self::UnaryOp { op, expr } => {
                let val = expr.eval(ctx);
                match op {
                    UnaryOp::BinaryNot => !val,
                    UnaryOp::LogicalNot => {
                        if val == 0 {
                            1
                        } else {
                            0
                        }
                    }
                    UnaryOp::Minus => -val,
                }
            }
            Self::BinOp { op, left, right } => {
                let left = left.eval(ctx);
                let right = right.eval(ctx);
                match op {
                    BinOp::Equal => {
                        if left == right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::NotEqual => {
                        if left != right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::GreaterThan => {
                        if left > right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::LessThan => {
                        if left < right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::GreaterThanOrEqual => {
                        if left >= right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::LessThanOrEqual => {
                        if left <= right {
                            1
                        } else {
                            0
                        }
                    }
                    BinOp::Or => left | right,
                    BinOp::Xor => left ^ right,
                    BinOp::And => left & right,
                    BinOp::ShiftLeft => left << right,
                    BinOp::ShiftRight => left >> right,
                    BinOp::Plus => left + right,
                    BinOp::Minus => left - right,
                    BinOp::Times => left * right,
                    BinOp::Divide => left / right,
                    BinOp::Reminder => left % right,
                }
            }
            Self::Func { name, args } => {
                let Some(entry) = FUNC_TABLE.get(name) else {
                    panic!(
                        "Function '{name}' not found. This should have been found at parse time"
                    );
                };
                if entry.number_of_args != args.len() {
                    panic!(
                        "The function '{name}' takes {} arguments, but {} were found. This should have been found at parse time",
                        entry.number_of_args,
                        args.len()
                    );
                }
                (entry.f)(ctx, args)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::eval_context::EvalContext;
    use crate::parser::Parser;

    use rstest::rstest;
    #[rstest]
    #[case("1+2", 3)]
    #[case("1+2+3", 6)]
    #[case("2*3", 6)]
    #[case("1+2+3=2*3", 1)]
    #[case("1+2+3=b*c", 1)]
    fn eval_works(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input, 1);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx), value);
    }

    #[rstest]
    #[case("7=3", 0)]
    #[case("7!=3", 1)]
    #[case("7<3", 0)]
    #[case("7>3", 1)]
    #[case("7<=3", 0)]
    #[case("7>=3", 1)]
    #[case("7<<3", 56)]
    #[case("7>>3", 0)]
    #[case("7+3", 10)]
    #[case("7-3", 4)]
    #[case("7*3", 21)]
    #[case("7/3", 2)]
    #[case("7%3", 1)]
    fn eval_works_for_binop(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input, 1);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx), value);
    }

    #[rstest]
    #[case("-3", -3)]
    #[case("~3", !3)]
    #[case("!3", 0)]
    fn eval_works_for_unary_op(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input, 1);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx), value);
    }

    #[test]
    fn eval_random_works() {
        let mut parser = Parser::new("random(10)", 1);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::with_seed(0);
        assert_eq!(expr.eval(&mut ctx), 1);
        assert_eq!(expr.eval(&mut ctx), 6);
        assert_eq!(expr.eval(&mut ctx), 3);
    }

    #[rstest]
    #[case("ite(0,2,3)", 3)]
    #[case("ite(1,2,3)", 2)]
    fn eval_ite_works(#[case] input: &str, #[case] value: i64) {
        let mut parser = Parser::new(input, 1);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        assert_eq!(expr.eval(&mut ctx), value);
    }
}
