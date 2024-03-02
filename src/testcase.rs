use rand::{rngs::StdRng, Rng, SeedableRng};
use std::{fmt::Display, str::FromStr};

mod parse;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinOp {
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

impl FromStr for BinOp {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "=" => Ok(Self::Equal),
            "!=" => Ok(Self::NotEqual),
            ">" => Ok(Self::GreaterThan),
            "<" => Ok(Self::LessThan),
            ">=" => Ok(Self::GreaterThanOrEqual),
            "<=" => Ok(Self::LessThanOrEqual),
            "|" => Ok(Self::Or),
            "^" => Ok(Self::Xor),
            "&" => Ok(Self::And),
            "<<" => Ok(Self::ShiftLeft),
            ">>" => Ok(Self::ShiftRight),
            "+" => Ok(Self::Plus),
            "-" => Ok(Self::Minus),
            "*" => Ok(Self::Times),
            "/" => Ok(Self::Divide),
            "%" => Ok(Self::Reminder),
            _ => Err(anyhow::anyhow!("Unknown bin op {}", s)),
        }
    }
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

impl BinOp {
    fn precedence(&self) -> u8 {
        match self {
            Self::Equal => 7,
            Self::NotEqual => 7,
            Self::GreaterThan => 7,
            Self::LessThan => 7,
            Self::GreaterThanOrEqual => 7,
            Self::LessThanOrEqual => 7,
            Self::Or => 6,
            Self::Xor => 5,
            Self::And => 4,
            Self::ShiftLeft => 3,
            Self::ShiftRight => 3,
            Self::Plus => 2,
            Self::Minus => 2,
            Self::Times => 1,
            Self::Divide => 1,
            Self::Reminder => 1,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum UnaryOp {
    Minus,
    LogicalNot,
    BitNot,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Minus => "-",
            Self::LogicalNot => "!",
            Self::BitNot => "~",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
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
        params: Vec<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::Variable(s) => write!(f, "{s}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::UnaryOp { op, expr } => write!(f, "{op}{expr}"),
            Self::Func { name, params } => {
                let params = params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{name}({params})")
            }
        }
    }
}

impl Expr {
    fn eval(&self, ctx: &mut EvalContext) -> anyhow::Result<i64> {
        match self {
            Self::Number(n) => Ok(*n),
            Self::Variable(name) => ctx
                .get(name)
                .ok_or(anyhow::anyhow!("Variable {name} not found")),
            Self::UnaryOp { op, expr } => {
                let val = expr.eval(ctx)?;
                match op {
                    UnaryOp::BitNot => Ok(!val),
                    UnaryOp::LogicalNot => Ok(if val == 0 { 1 } else { 0 }),
                    UnaryOp::Minus => Ok(-val),
                }
            }
            Self::BinOp { op, left, right } => {
                let left = left.eval(ctx)?;
                let right = right.eval(ctx)?;
                match op {
                    BinOp::Equal => Ok(if left == right { 1 } else { 0 }),
                    BinOp::NotEqual => Ok(if left != right { 1 } else { 0 }),
                    BinOp::GreaterThan => Ok(if left > right { 1 } else { 0 }),
                    BinOp::LessThan => Ok(if left < right { 1 } else { 0 }),
                    BinOp::GreaterThanOrEqual => Ok(if left >= right { 1 } else { 0 }),
                    BinOp::LessThanOrEqual => Ok(if left <= right { 1 } else { 0 }),
                    BinOp::Or => Ok(left | right),
                    BinOp::Xor => Ok(left ^ right),
                    BinOp::And => Ok(left & right),
                    BinOp::ShiftLeft => Ok(left << right),
                    BinOp::ShiftRight => Ok(left >> right),
                    BinOp::Plus => Ok(left + right),
                    BinOp::Minus => Ok(left - right),
                    BinOp::Times => Ok(left * right),
                    BinOp::Divide => Ok(left / right),
                    BinOp::Reminder => Ok(left % right),
                }
            }
            Self::Func { name, params } => match name.as_str() {
                "random" => {
                    if params.len() == 1 {
                        let max = params[0].eval(ctx)?;
                        Ok(ctx.rng.gen_range(1..max))
                    } else {
                        anyhow::bail!("The function 'random' takes one parameter")
                    }
                }
                "ite" => {
                    if params.len() == 3 {
                        let test = params[0].eval(ctx)?;
                        if test == 0 {
                            Ok(params[2].eval(ctx)?)
                        } else {
                            Ok(params[1].eval(ctx)?)
                        }
                    } else {
                        anyhow::bail!("The function 'lte' takes three parameters")
                    }
                }
                "signExt" => anyhow::bail!("The function '{name}' is currently not implemented"),
                _ => anyhow::bail!("Unknown function '{name}'"),
            },
        }
    }
}

#[derive(Debug)]
struct EvalContext {
    values: Vec<(String, i64)>,
    frame_stack: Vec<usize>,
    rng: StdRng,
    seed: u64,
}

impl EvalContext {
    fn new() -> Self {
        let mut seed_bytes: [u8; 8] = Default::default();
        getrandom::getrandom(&mut seed_bytes).unwrap();
        let seed = u64::from_le_bytes(seed_bytes);

        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::seed_from_u64(seed),
            seed,
        }
    }

    fn with_seed(seed: u64) -> Self {
        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::seed_from_u64(seed),
            seed,
        }
    }

    fn push_frame(&mut self) {
        self.frame_stack.push(self.values.len())
    }

    fn pop_frame(&mut self) {
        let len = self.frame_stack.pop().unwrap_or(0);
        self.values.truncate(len);
    }

    fn set(&mut self, name: &str, value: i64) {
        let frame_start = *self.frame_stack.last().unwrap_or(&0);
        if let Some((_, entry_value)) = self.values[frame_start..]
            .iter_mut()
            .find(|entry| entry.0 == name)
        {
            *entry_value = value;
        } else {
            self.values.push((name.to_owned(), value));
        }
    }

    fn get(&self, name: &str) -> Option<i64> {
        self.values
            .iter()
            .rev()
            .find(|entry| entry.0 == name)
            .map(|entry| entry.1)
    }

    fn reset_random_seed(&mut self) {
        self.rng = StdRng::seed_from_u64(self.seed);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Stmt {
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
    fn run(&self, ctx: &mut EvalContext) {
        match self {
            Self::Let { name, expr } => {
                let value = expr.eval(ctx).unwrap();
                ctx.set(name, value);
            }
            Self::DataRow(entries) => {
                let data = entries
                    .iter()
                    .map(|entry| entry.run(ctx))
                    .collect::<Vec<_>>()
                    .join(" ");
                println!("{data}");
            }
            Self::Loop {
                variable,
                max,
                stmts,
            } => {
                ctx.push_frame();
                for i in 0..*max {
                    ctx.set(variable, i);
                    for stmt in stmts {
                        stmt.run(ctx);
                    }
                }
                ctx.pop_frame();
            }
            Self::ResetRandom => {
                ctx.reset_random_seed();
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DataEntry {
    Number(i64),
    Expr(Expr),
    Bits { number: u64, expr: Expr },
    X,
    Z,
}

impl DataEntry {
    fn run(&self, ctx: &mut EvalContext) -> String {
        match self {
            Self::Number(n) => format!("{n}"),
            Self::Expr(expr) => format!("{}", expr.eval(ctx).unwrap()),
            Self::Bits { number, expr } => {
                let value = expr.eval(ctx).unwrap();
                (0..*number)
                    .rev()
                    .map(|n| format!("{}", (value >> n) & 1))
                    .collect::<Vec<_>>()
                    .join(" ")
            }
            Self::X => String::from("X"),
            Self::Z => String::from("Z"),
        }
    }
}

pub struct TestCase {
    signals: Vec<String>,
    stmts: Vec<Stmt>,
}

impl FromStr for TestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse::parse(input)
    }
}

impl TestCase {
    pub fn run(&self) {
        let mut ctx = EvalContext::new();
        for stmt in &self.stmts {
            stmt.run(&mut ctx);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_context_works() {
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.set("a", 4);
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.push_frame();
        ctx.set("a", 5);
        ctx.set("b", 6);
        assert_eq!(ctx.get("a"), Some(5));
        assert_eq!(ctx.get("b"), Some(6));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.pop_frame();
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
    }

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
        assert_eq!(testcase.signals.len(), 11);
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
        testcase.run();
    }
}
