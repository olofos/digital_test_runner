pub mod dig;
mod eval_context;
mod expr;
mod parse;
mod stmt;

use std::{fmt::Display, str::FromStr};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum InputValue {
    Value(i64),
    Z,
    // Expr(expr::Expr),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum OutputValue {
    Value(i64),
    Z,
    X,
    // Expr(expr::Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputSignal {
    pub name: String,
    pub bits: u8,
    pub default: InputValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputSignal {
    pub name: String,
    pub bits: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCase {
    stmts: Vec<stmt::OrderedStmt>,
    inputs: Vec<InputSignal>,
    outputs: Vec<OutputSignal>,
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let input_names = self.inputs.iter().map(|s| s.name.clone());
        let output_names = self.outputs.iter().map(|s| s.name.clone());

        let names = input_names
            .chain(output_names)
            .collect::<Vec<_>>()
            .join(" ");

        writeln!(f, "{names}")?;
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

pub struct TestCaseLoader<'a, I, O> {
    source: &'a str,
    inputs: I,
    outputs: O,
    expanded_signals: Vec<(&'a str, u64)>,
}

impl<'a> TestCaseLoader<'a, (), ()> {
    pub fn new(source: &str) -> TestCaseLoader<(), ()> {
        TestCaseLoader {
            source,
            inputs: (),
            outputs: (),
            expanded_signals: vec![],
        }
    }

    pub fn try_from_dig(
        dig: &'a crate::dig::DigFile,
        n: usize,
    ) -> anyhow::Result<TestCaseLoader<Vec<InputSignal>, Vec<OutputSignal>>> {
        if n >= dig.test_cases.len() {
            anyhow::bail!(
                "Trying to load test case #{n}, but file only contains {} test cases",
                dig.test_cases.len()
            );
        }
        let loader = TestCaseLoader::new(&dig.test_cases[n].test_data);
        Ok(loader.with_signals(dig.inputs.clone(), dig.outputs.clone()))
    }

    pub fn with_signals(
        self,
        inputs: Vec<InputSignal>,
        outputs: Vec<OutputSignal>,
    ) -> TestCaseLoader<'a, Vec<InputSignal>, Vec<OutputSignal>> {
        TestCaseLoader {
            source: self.source,
            inputs,
            outputs,
            expanded_signals: self.expanded_signals,
        }
    }
}

impl<'a, I, O> TestCaseLoader<'a, I, O> {
    pub fn expand(mut self, name: &'a str, bits: u64) -> Self {
        self.expanded_signals.push((name, bits));
        self
    }
}

impl<'a> TestCaseLoader<'a, Vec<InputSignal>, Vec<OutputSignal>> {
    fn get_inputs_and_outputs(
        &self,
        signal_names: &[String],
    ) -> anyhow::Result<(Vec<InputSignal>, Vec<usize>, Vec<OutputSignal>, Vec<usize>)> {
        let mut inputs: Vec<InputSignal> = vec![];
        let mut outputs: Vec<OutputSignal> = vec![];

        let mut input_indices: Vec<usize> = vec![];
        let mut output_indices: Vec<usize> = vec![];

        for (i, signal_name) in signal_names.iter().enumerate() {
            if let Some(input) = self
                .inputs
                .iter()
                .find(|signal| &signal.name == signal_name)
            {
                inputs.push(input.clone());
                input_indices.push(i);
            } else if let Some(output) = self
                .outputs
                .iter()
                .find(|signal| &signal.name == signal_name)
            {
                outputs.push(output.clone());
                output_indices.push(i);
            } else {
                anyhow::bail!("Unknown signal {signal_name}");
            }
        }

        Ok((inputs, input_indices, outputs, output_indices))
    }

    pub fn try_build(mut self) -> anyhow::Result<TestCase> {
        let parsed_test_case: ParsedTestCase = self.source.parse()?;

        let mut extended_bits: Vec<Option<u64>> = vec![None; parsed_test_case.signal_names.len()];
        for (extended_signal, bits) in &self.expanded_signals {
            let index = parsed_test_case
                .signal_names
                .iter()
                .position(|signal_name| signal_name == extended_signal)
                .ok_or_else(|| {
                    anyhow::anyhow!("Signal {extended_signal} not found in parsed test case")
                })?;
            extended_bits[index] = Some(*bits);
        }

        let (_, input_indices, _, output_indices) =
            self.get_inputs_and_outputs(&parsed_test_case.signal_names)?;

        let stmts = stmt::expand(parsed_test_case.stmts, &input_indices, &output_indices);
        let stmts = stmt::insert_bits(stmts, extended_bits);

        self.inputs = self
            .inputs
            .into_iter()
            .flat_map(|sig| {
                if let Some((name, bits)) = self
                    .expanded_signals
                    .iter()
                    .find(|(name, _)| *name == sig.name)
                {
                    (0..*bits)
                        .map(|i| {
                            let default = match sig.default {
                                InputValue::Z => InputValue::Z,
                                InputValue::Value(n) => InputValue::Value(n & (1 << i)),
                            };
                            InputSignal {
                                name: format!("{}:{i}", name),
                                bits: 1,
                                default,
                            }
                        })
                        .collect()
                } else {
                    vec![sig]
                }
            })
            .collect();

        self.outputs = self
            .outputs
            .into_iter()
            .flat_map(|sig| {
                if let Some((name, bits)) = self
                    .expanded_signals
                    .iter()
                    .find(|(name, _)| *name == sig.name)
                {
                    (0..*bits)
                        .map(|i| OutputSignal {
                            name: format!("{}:{i}", name),
                            bits: 1,
                        })
                        .collect()
                } else {
                    vec![sig]
                }
            })
            .collect();

        let signal_names: Vec<_> = parsed_test_case
            .signal_names
            .iter()
            .cloned()
            .flat_map(|sig_name| {
                if let Some((name, bits)) = self
                    .expanded_signals
                    .iter()
                    .find(|(name, _)| *name == sig_name)
                {
                    (0..*bits).map(|i| format!("{}:{i}", name)).collect()
                } else {
                    vec![sig_name]
                }
            })
            .collect();

        let (inputs, input_indices, outputs, output_indices) =
            self.get_inputs_and_outputs(&signal_names)?;

        let stmts = stmt::expand(stmts, &input_indices, &output_indices);

        let stmts = stmt::reorder(stmts, &input_indices, &output_indices);

        Ok(TestCase {
            stmts,
            inputs,
            outputs,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTestCase {
    pub(crate) signal_names: Vec<String>,
    pub(crate) stmts: Vec<stmt::Stmt>,
}

impl FromStr for ParsedTestCase {
    type Err = anyhow::Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::parse::parse(input)
    }
}

impl Display for ParsedTestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names = self.signal_names.join(" ");

        writeln!(f, "{names}")?;
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

impl TestCase {
    pub fn run(&self) -> Vec<stmt::ResultRow> {
        let mut ctx = eval_context::EvalContext::new();
        self.stmts
            .iter()
            .flat_map(|stmt| stmt.run(&mut ctx))
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let known_inputs = ["BUS-CLK", "S", "A", "B", "N", "ALU-~RESET", "ALU-AUX"]
            .into_iter()
            .map(|name| InputSignal {
                name: String::from(name),
                bits: 1,
                default: InputValue::Value(0),
            })
            .collect::<Vec<_>>();
        let known_outputs = ["OUT", "FLAG", "DLEN", "DSUM"]
            .into_iter()
            .map(|name| OutputSignal {
                name: String::from(name),
                bits: 1,
            })
            .collect::<Vec<_>>();
        let testcase = TestCaseLoader::new(input)
            .with_signals(known_inputs, known_outputs)
            .expand("S", 3)
            .try_build()
            .unwrap();
        let result = testcase.run();
        for row in result {
            println!("{row}");
        }
    }
}
