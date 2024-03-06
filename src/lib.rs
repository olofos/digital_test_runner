mod expr;
mod testcase;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Signal {
    name: String,
    bits: u8,
    dir: SignalDir,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum SignalDir {
    Input,
    Output,
}
