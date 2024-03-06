pub mod dig;
mod eval_context;
mod expr;
mod testcase;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    pub name: String,
    pub bits: u8,
    pub dir: SignalDir,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum SignalDir {
    Input,
    Output,
}

pub use testcase::TestCase;
