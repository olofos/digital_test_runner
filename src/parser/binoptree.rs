use crate::expr::{BinOp, Expr};

impl BinOp {
    pub fn precedence(&self) -> u8 {
        match self {
            Self::Equal => 8,
            Self::NotEqual => 8,
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

/// Used to parse strings of binary operators.
/// We construct a separate tree of only the binary operators on the same level, so that we don't recurse into expressions in brackets
#[derive(Debug, Clone)]
enum BinOpTree {
    Atom(Expr),
    BinOp {
        op: BinOp,
        left: Box<BinOpTree>,
        right: Box<BinOpTree>,
    },
    Dummy,
}

impl std::fmt::Display for BinOpTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(expr) => write!(f, "{expr}"),
            Self::BinOp { op, left, right } => write!(f, "({left} {op} {right})"),
            Self::Dummy => write!(f, "DUMMY"),
        }
    }
}

impl BinOpTree {
    fn add(&mut self, new_op: BinOp, new_expr: Expr) {
        if let Self::BinOp { op, left: _, right } = self {
            if new_op.precedence() < op.precedence() {
                right.add(new_op, new_expr);
                return;
            }
        };
        let left = std::mem::replace(self, Self::Dummy);
        *self = Self::BinOp {
            op: new_op,
            left: Box::new(left),
            right: Box::new(Self::Atom(new_expr)),
        }
    }

    fn into_expr(self) -> Expr {
        match self {
            Self::Atom(expr) => expr,
            Self::BinOp { op, left, right } => Expr::BinOp {
                op,
                left: Box::new(left.into_expr()),
                right: Box::new(right.into_expr()),
            },
            Self::Dummy => unreachable!(),
        }
    }
}
