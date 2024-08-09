use crate::{errors::ExprError, eval_context::EvalContext};
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

impl BinOp {
    fn eval(&self, left: i64, right: i64) -> i64 {
        match self {
            Self::Equal => (left == right) as i64,
            Self::NotEqual => (left != right) as i64,
            Self::GreaterThan => (left > right) as i64,
            Self::LessThan => (left < right) as i64,
            Self::GreaterThanOrEqual => (left >= right) as i64,
            Self::LessThanOrEqual => (left <= right) as i64,
            Self::Or => left | right,
            Self::Xor => left ^ right,
            Self::And => left & right,
            Self::ShiftLeft => left << right,
            Self::ShiftRight => left >> right,
            Self::Plus => left + right,
            Self::Minus => left - right,
            Self::Times => left * right,
            Self::Divide => left / right,
            Self::Reminder => left % right,
        }
    }
}

impl UnaryOp {
    fn eval(&self, val: i64) -> i64 {
        match self {
            Self::Minus => -val,
            Self::LogicalNot => (val == 0) as i64,
            Self::BinaryNot => !val,
        }
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
    is_pure: bool,
    f: fn(&EvalContext, &[Expr]) -> Result<i64, ExprError>,
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
            is_pure: false,
        },
        FuncTableEntry {
            name: "ite",
            number_of_args: 3,
            f: func_ite,
            is_pure: true,
        },
        FuncTableEntry {
            name: "signExt",
            number_of_args: 2,
            f: func_sign_ext,
            is_pure: true,
        },
    ],
};

fn func_random(ctx: &EvalContext, args: &[Expr]) -> Result<i64, ExprError> {
    let max = args[0].eval(ctx)?;
    Ok(ctx.random(1..max))
}

fn func_ite(ctx: &EvalContext, args: &[Expr]) -> Result<i64, ExprError> {
    let test = args[0].eval(ctx)?;
    if test == 0 {
        args[2].eval(ctx)
    } else {
        args[1].eval(ctx)
    }
}

fn func_sign_ext(_ctx: &EvalContext, _args: &[Expr]) -> Result<i64, ExprError> {
    todo!("signExt")
}

impl Expr {
    pub(crate) fn eval(&self, ctx: &EvalContext) -> Result<i64, ExprError> {
        match self {
            Self::Number(n) => Ok(*n),
            Self::Variable(name) => {
                match ctx
                    .get(name)
                    .expect("Variable not found. This should have been found at parse time")
                {
                    crate::OutputValue::Value(n) => Ok(n),
                    crate::OutputValue::Z => panic!("Unexpected value Z for variable '{name}'"),
                    crate::OutputValue::X => panic!("Unexpected value X for variable '{name}'"),
                }
            }
            Self::UnaryOp { op, expr } => Ok(op.eval(expr.eval(ctx)?)),
            Self::BinOp { op, left, right } => Ok(op.eval(left.eval(ctx)?, right.eval(ctx)?)),
            Self::Func { name, args } => {
                let entry = FUNC_TABLE
                    .get(name)
                    .expect("Function not found. This should have been found at parse time");
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

    pub(crate) fn eval_const(&self) -> Option<i64> {
        match self {
            Self::Number(n) => Some(*n),
            Self::UnaryOp { op, expr } => Some(op.eval(expr.eval_const()?)),
            Self::BinOp { op, left, right } => {
                Some(op.eval(left.eval_const()?, right.eval_const()?))
            }
            Self::Func { name, args } => {
                let entry = FUNC_TABLE.get(name)?;
                if !entry.is_pure {
                    return None;
                }
                let args = args
                    .iter()
                    .map(|expr| expr.eval_const().map(Expr::Number))
                    .collect::<Option<Vec<_>>>()?;
                Some((entry.f)(&EvalContext::new(), &args).ok()?)
            }
            _ => None,
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
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
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
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[rstest]
    #[case("-3", -3)]
    #[case("~3", !3)]
    #[case("!3", 0)]
    fn eval_works_for_unary_op(#[case] input: &str, #[case] value: i64) {
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }

    #[test]
    fn eval_random_works() {
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new("random(10)", &signals);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::with_seed(0);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 1);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 6);
        assert_eq!(expr.eval(&mut ctx).unwrap(), 3);
    }

    #[rstest]
    #[case("ite(0,2,3)", 3)]
    #[case("ite(1,2,3)", 2)]
    fn eval_ite_works(#[case] input: &str, #[case] value: i64) {
        let signals = vec!["a".to_string()];
        let mut parser = Parser::new(input, &signals);
        let expr = parser.parse_expr().unwrap();
        let mut ctx = EvalContext::new();
        assert_eq!(expr.eval(&mut ctx).unwrap(), value);
    }
}
