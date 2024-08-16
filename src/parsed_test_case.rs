use std::collections::HashSet;

use crate::{
    errors::{ParseError, SignalError, SignalErrorKind},
    expr::Expr,
    parser::{HeaderParser, ParseResult, Parser},
    stmt::Stmt,
    EntryIndex, Signal, SignalType, TestCase, VirtualExpr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VirtualSignal {
    pub(crate) name: String,
    pub(crate) expr: Expr,
}

/// Represents a test case as obtained directly from the test source code
///
/// To get a full runnable [TestCase], the input and output signals have to be specified using
/// the `with_signals` method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTestCase {
    pub(crate) stmts: Vec<Stmt>,
    /// List of signal names appearing in the test
    pub signals: Vec<String>,
    virtual_signals: Vec<(VirtualSignal, logos::Span)>,
    signal_spans: Vec<logos::Span>,
    expected_inputs: Vec<(String, logos::Span)>,
    read_outputs: Vec<(String, logos::Span)>,
}

impl ParsedTestCase {
    /// Construct a complete test case by supplying a description of the
    /// input and expected signals of the device under test
    pub fn with_signals(mut self, mut signals: Vec<Signal>) -> Result<TestCase, SignalError> {
        self.check_duplicate_signals(&signals)?;

        signals.extend(self.virtual_signals.drain(..).map(|(virt, _)| Signal {
            name: virt.name,
            bits: 64,
            typ: SignalType::Virtual {
                expr: VirtualExpr {
                    expr: Box::new(virt.expr),
                },
            },
        }));

        let (input_indices, expected_indices) = self.build_indices(&signals);
        self.check_missing_signals(&input_indices, &expected_indices)?;
        self.check_and_consume_expected_inputs(&signals)?;
        let read_outputs = self.build_read_outputs(&signals)?;

        Ok(TestCase {
            stmts: self.stmts,
            signals,
            input_indices,
            expected_indices,
            read_outputs,
        })
    }

    fn check_duplicate_signals(&self, signals: &[Signal]) -> Result<(), SignalError> {
        let mut names = HashSet::new();
        for sig in signals {
            if !names.insert(&sig.name) {
                return Err(SignalError(SignalErrorKind::DuplicateSignal {
                    signal: sig.name.clone(),
                }));
            }
        }
        for (virt, span) in &self.virtual_signals {
            if names.contains(&virt.name) {
                return Err(SignalError(SignalErrorKind::SignalIsVirtual {
                    name: virt.name.clone(),
                    at: span.clone(),
                    source_code: None,
                }));
            }
        }
        Ok(())
    }

    fn build_indices(&self, signals: &[Signal]) -> (Vec<EntryIndex>, Vec<EntryIndex>) {
        let mut input_indices: Vec<EntryIndex> = vec![];
        let mut expected_indices = vec![];

        for (signal_index, signal) in signals.iter().enumerate() {
            let index = self
                .signals
                .iter()
                .position(|signal_name| signal_name == &signal.name);

            let index_out = self
                .signals
                .iter()
                .position(|signal_name| signal_name == &(signal.name.clone() + "_out"));

            match signal.typ {
                SignalType::Input { .. } | SignalType::Bidirectional { .. } => {
                    input_indices.push(match &index {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
                SignalType::Output | SignalType::Virtual { .. } => {}
            }

            match signal.typ {
                SignalType::Input { .. } => {}
                SignalType::Bidirectional { .. } => {
                    expected_indices.push(match &index_out {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
                SignalType::Output | SignalType::Virtual { .. } => {
                    expected_indices.push(match &index {
                        Some(entry_index) => EntryIndex::Entry {
                            entry_index: *entry_index,
                            signal_index,
                        },
                        None => EntryIndex::Default { signal_index },
                    });
                }
            }
        }
        (input_indices, expected_indices)
    }

    fn check_missing_signals(
        &self,
        input_indices: &[EntryIndex],
        expected_indices: &[EntryIndex],
    ) -> Result<(), SignalError> {
        let missing_signals = self
            .signals
            .iter()
            .enumerate()
            .filter_map(|(entry_index, signal_name)| {
                if !input_indices
                    .iter()
                    .chain(expected_indices)
                    .any(|entry| entry.indexes(entry_index))
                {
                    Some(signal_name.to_owned())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if !missing_signals.is_empty() {
            let at = missing_signals
                .iter()
                .map(|name| {
                    let i = self
                        .signals
                        .iter()
                        .position(|sig_name| sig_name == name)
                        .unwrap();
                    self.signal_spans[i].clone()
                })
                .collect::<Vec<_>>();
            return Err(SignalError(SignalErrorKind::UnknownSignals {
                signals: missing_signals.join(", "),
                at,
                source_code: None,
            }));
        }
        Ok(())
    }

    fn check_and_consume_expected_inputs(&mut self, signals: &[Signal]) -> Result<(), SignalError> {
        for (name, at) in self.expected_inputs.drain(..) {
            if !signals.iter().any(|sig| sig.name == name && sig.is_input()) {
                if let Some(i) = self.signals.iter().position(|sig_name| sig_name == &name) {
                    let signal_span = self.signal_spans[i].clone();
                    return Err(SignalError(SignalErrorKind::NotAnInput {
                        name,
                        at,
                        signal_span,
                        source_code: None,
                    }));
                } else {
                    return Err(SignalError(SignalErrorKind::UnknownVariableOrSignal {
                        name,
                        at,
                        source_code: None,
                    }));
                }
            }
        }
        Ok(())
    }

    fn build_read_outputs(&mut self, signals: &[Signal]) -> Result<Vec<usize>, SignalError> {
        let mut read_outputs = vec![];
        for (name, at) in self.read_outputs.drain(..) {
            if let Some(i) = signals
                .iter()
                .position(|sig| sig.name == name && sig.is_output())
            {
                read_outputs.push(i);
            } else if let Some(i) = self.signals.iter().position(|sig_name| sig_name == &name) {
                let signal_span = self.signal_spans[i].clone();
                return Err(SignalError(SignalErrorKind::NotAnOutput {
                    name,
                    at,
                    signal_span,
                    source_code: None,
                }));
            } else {
                return Err(SignalError(SignalErrorKind::UnknownVariableOrSignal {
                    name,
                    at,
                    source_code: None,
                }));
            }
        }
        Ok(read_outputs)
    }

    pub(crate) fn parse(input: &str) -> Result<ParsedTestCase, ParseError> {
        let mut parser = HeaderParser::new(input);
        let (signals, signal_spans) = parser.parse()?;

        let mut parser = Parser::from(parser, &signals);
        let stmts = parser.parse_stmt_block(None)?;

        let ParseResult {
            expected_inputs,
            read_outputs,
            virtual_signals,
        } = parser.finish();

        let test_case = ParsedTestCase {
            stmts,
            signals,
            virtual_signals,
            signal_spans,
            expected_inputs,
            read_outputs,
        };
        Ok(test_case)
    }
}

impl std::str::FromStr for ParsedTestCase {
    type Err = ParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        ParsedTestCase::parse(input)
    }
}
