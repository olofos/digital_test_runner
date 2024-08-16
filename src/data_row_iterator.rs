use std::collections::HashMap;

use crate::{
    errors::{ExprError, IterationError, RuntimeError, RuntimeErrorKind},
    stmt::DataEntries,
    DataEntry, DataRow, EntryIndex, EvalContext, ExpectedEntry, ExpectedValue, InputEntry,
    InputValue, OutputEntry, OutputResultEntry, OutputValue, Signal, SignalType, StmtIterator,
    TestCase, TestDriver,
};

#[derive(Debug)]
/// An iterator over the test results for a dynamic test
pub struct DataRowIterator<'a, 'b, T> {
    ctx: EvalContext,
    test_data: DataRowIteratorTestData<'a>,
    driver: &'b mut T,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputEntryIndex<'a> {
    None,
    Output(usize),
    Virtual(&'a crate::expr::Expr),
}

#[derive(Debug)]
struct DataRowIteratorTestData<'a> {
    signals: &'a [Signal],
    iter: StmtIterator<'a>,
    /// List of inputs which links signals to test entries
    input_indices: &'a [EntryIndex],
    /// List of expected values which links signals to test entries
    expected_indices: &'a [EntryIndex],
    /// List with the same number of entries as `expected_indices`.
    /// Each non-trivial entry is an index into the output vec from the driver.
    output_indices: Vec<OutputEntryIndex<'a>>,
    prev: Option<Vec<DataEntry>>,
    /// The bool is check_update. This should probably sit inside DataEntries
    cache: Vec<(DataEntries, bool)>,
}

#[derive(Debug)]
struct EvaluatedRow<'a> {
    line: usize,
    inputs: Vec<InputEntry<'a>>,
    expected: Vec<ExpectedEntry<'a>>,
    update_output: bool,
}

impl<'a, 'b, T: TestDriver> Iterator for DataRowIterator<'a, 'b, T> {
    type Item = Result<DataRow<'a>, IterationError<T::Error>>;

    fn next(&mut self) -> Option<Self::Item> {
        let row = match self.test_data.get_row(&mut self.ctx) {
            Ok(val) => val?,
            Err(err) => {
                return Some(Err(IterationError::Runtime(
                    RuntimeErrorKind::ExprError(err).into(),
                )))
            }
        };

        match self.handle_io(&row.inputs, row.update_output) {
            Ok(outputs) => Some(Ok(row.into_data_row(outputs))),
            Err(err) => Some(Err(err)),
        }
    }
}

impl<'a, 'b, T: TestDriver> DataRowIterator<'a, 'b, T> {
    pub(crate) fn try_new(
        test_case: &'a TestCase,
        driver: &'b mut T,
    ) -> Result<Self, IterationError<T::Error>> {
        let mut test_data = DataRowIteratorTestData::new(test_case);

        let inputs = test_data.generate_default_input_entries();
        let outputs = driver.write_input_and_read_output(&inputs)?;
        test_data.build_output_indices(&outputs, &test_case.read_outputs)?;

        let ctx = EvalContext::new_with_outputs(&outputs);

        Ok(Self {
            ctx,
            test_data,
            driver,
        })
    }

    fn handle_io(
        &mut self,
        inputs: &[InputEntry<'a>],
        update_output: bool,
    ) -> Result<Vec<OutputValue>, IterationError<T::Error>> {
        if update_output {
            let outputs = self.driver.write_input_and_read_output(inputs)?;
            self.ctx.set_outputs(&outputs);
            self.test_data.extract_output_values(outputs, &mut self.ctx)
        } else {
            self.driver.write_input(inputs)?;
            Ok(vec![])
        }
    }

    /// The current value of all variables
    pub fn vars(&self) -> HashMap<String, i64> {
        self.ctx.vars()
    }
}

impl<'a> DataRowIteratorTestData<'a> {
    fn generate_default_input_entries(&self) -> Vec<InputEntry<'a>> {
        self.input_indices
            .iter()
            .map(|index| {
                let signal = &self.signals[index.signal_index()];
                let value = signal.default_value().unwrap();
                InputEntry {
                    signal,
                    value,
                    changed: false,
                }
            })
            .collect()
    }

    fn generate_input_entries(
        &self,
        stmt_entries: &[DataEntry],
        changed: &[bool],
    ) -> Vec<InputEntry<'a>> {
        self.input_indices
            .iter()
            .map(|index| match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        DataEntry::Number(n) => InputValue::Value(n & ((1 << signal.bits) - 1)),
                        DataEntry::Z => InputValue::Z,
                        _ => unreachable!(),
                    };
                    let changed = changed[*entry_index];
                    InputEntry {
                        signal,
                        value,
                        changed,
                    }
                }
                EntryIndex::Default { signal_index } => {
                    let signal = &self.signals[*signal_index];
                    InputEntry {
                        signal,
                        value: signal.default_value().unwrap(),
                        changed: false,
                    }
                }
            })
            .collect()
    }

    fn generate_expected_entries(&self, stmt_entries: &[DataEntry]) -> Vec<ExpectedEntry<'a>> {
        self.expected_indices
            .iter()
            .map(|index| match index {
                EntryIndex::Entry {
                    entry_index,
                    signal_index,
                } => {
                    let signal = &self.signals[*signal_index];
                    let value = match &stmt_entries[*entry_index] {
                        DataEntry::Number(n) => {
                            let mask = if signal.bits < 64 {
                                (1 << signal.bits) - 1
                            } else {
                                -1
                            };
                            ExpectedValue::Value(n & mask)
                        }
                        DataEntry::Z => ExpectedValue::Z,
                        DataEntry::X => ExpectedValue::X,
                        _ => unreachable!(),
                    };
                    ExpectedEntry { signal, value }
                }
                EntryIndex::Default { signal_index } => {
                    let signal = &self.signals[*signal_index];
                    ExpectedEntry {
                        signal,
                        value: ExpectedValue::X,
                    }
                }
            })
            .collect()
    }

    fn build_output_indices<E: std::error::Error>(
        &mut self,
        outputs: &[OutputEntry<'_>],
        read_outputs: &[usize],
    ) -> Result<(), IterationError<E>> {
        let mut output_indices = Vec::with_capacity(outputs.len());
        let mut found_outputs = vec![];

        for expected_index in self.expected_indices.iter() {
            let signal = &self.signals[expected_index.signal_index()];
            let entry = if let SignalType::Virtual { expr } = &signal.typ {
                OutputEntryIndex::Virtual(&expr.expr)
            } else if let Some(n) = outputs.iter().position(|output| output.signal == signal) {
                OutputEntryIndex::Output(n)
            } else {
                OutputEntryIndex::None
            };
            output_indices.push(entry);
            if matches!(entry, OutputEntryIndex::Output(_)) {
                found_outputs.push(expected_index.signal_index());
            }
        }

        let missing = read_outputs
            .iter()
            .filter_map(|read| {
                if !found_outputs.contains(read) {
                    Some(self.signals[*read].name.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        if missing.is_empty() {
            self.output_indices = output_indices;
            Ok(())
        } else {
            Err(IterationError::Runtime(
                RuntimeErrorKind::MissingOutputs(missing.join(", ")).into(),
            ))
        }
    }

    fn num_outputs(&self) -> usize {
        self.output_indices
            .iter()
            .filter(|i| matches!(i, OutputEntryIndex::Output(_)))
            .count()
    }

    fn extract_output_values<E: std::error::Error>(
        &self,
        outputs: Vec<OutputEntry<'_>>,
        ctx: &mut EvalContext,
    ) -> Result<Vec<OutputValue>, IterationError<E>> {
        let num_outputs = self.num_outputs();

        if outputs.len() != num_outputs {
            return Err(IterationError::Runtime(
                RuntimeErrorKind::WrongNumberOfOutputs(num_outputs, outputs.len()).into(),
            ));
        }

        ctx.swap_vars();
        let result = self
            .expected_indices
            .iter()
            .zip(&self.output_indices)
            .map(|(expected_index, output_index)| match *output_index {
                OutputEntryIndex::Output(output_entry_index) => {
                    let expected_signal = &self.signals[expected_index.signal_index()];
                    let output_signal = outputs[output_entry_index].signal;

                    if expected_signal == output_signal {
                        Ok(outputs[output_entry_index].value)
                    } else {
                        Err(IterationError::Runtime(
                            RuntimeErrorKind::WrongOutputOrder.into(),
                        ))
                    }
                }
                OutputEntryIndex::Virtual(expr) => expr
                    .eval(ctx)
                    .map(OutputValue::Value)
                    .map_err(|err| IterationError::Runtime(RuntimeError(err.into()))),
                OutputEntryIndex::None => Ok(OutputValue::X),
            })
            .collect();
        ctx.swap_vars();
        result
    }

    fn new(test_case: &'a TestCase) -> Self {
        DataRowIteratorTestData {
            iter: StmtIterator::new(&test_case.stmts),
            signals: &test_case.signals,
            input_indices: &test_case.input_indices,
            expected_indices: &test_case.expected_indices,
            output_indices: vec![],
            prev: None,
            cache: vec![],
        }
    }

    fn check_changed_entries(&self, stmt_entries: &[DataEntry]) -> Vec<bool> {
        if let Some(prev) = &self.prev {
            stmt_entries
                .iter()
                .zip(prev)
                .map(|(new, old)| new != old)
                .collect()
        } else {
            vec![true; stmt_entries.len()]
        }
    }

    fn entry_is_input(&self, entry_index: usize) -> bool {
        self.input_indices
            .iter()
            .any(|entry| entry.indexes(entry_index))
    }

    fn expand_x(&mut self) {
        loop {
            let (row_result, check_output) = self
                .cache
                .last()
                .expect("cache should be refilled before calling expand_x");
            let check_output = *check_output;

            let Some(x_index) =
                row_result
                    .entries
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(i, entry)| {
                        if entry == &DataEntry::X && self.entry_is_input(i) {
                            Some(i)
                        } else {
                            None
                        }
                    })
            else {
                break;
            };
            let (mut row_result, _) = self.cache.pop().unwrap();
            row_result.entries[x_index] = DataEntry::Number(1);
            self.cache.push((row_result.clone(), check_output));
            row_result.entries[x_index] = DataEntry::Number(0);
            self.cache.push((row_result, check_output));
        }
    }

    fn expand_c(&mut self) {
        let (mut row_result, check_output) = self
            .cache
            .pop()
            .expect("cache should be refilled before calling expand_c");

        let c_indices = row_result
            .entries
            .iter()
            .enumerate()
            .filter_map(|(i, entry)| {
                if entry == &DataEntry::C && self.entry_is_input(i) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if c_indices.is_empty() {
            self.cache.push((row_result, check_output));
        } else {
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), true));
            for entry_index in self.expected_indices {
                match entry_index {
                    EntryIndex::Entry {
                        entry_index,
                        signal_index: _,
                    } => row_result.entries[*entry_index] = DataEntry::X,
                    EntryIndex::Default { signal_index: _ } => continue,
                }
            }
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(1);
            }
            self.cache.push((row_result.clone(), false));
            for &i in &c_indices {
                row_result.entries[i] = DataEntry::Number(0);
            }
            self.cache.push((row_result.clone(), false));
        }
    }

    fn get_row(&mut self, ctx: &mut EvalContext) -> Result<Option<EvaluatedRow<'a>>, ExprError> {
        if self.cache.is_empty() {
            let Some(row_result) = self.iter.next_with_context(ctx)? else {
                return Ok(None);
            };
            self.cache.push((row_result, true));
        }

        self.expand_x();
        self.expand_c();

        let (row_result, update_output) = self.cache.pop().unwrap();

        let changed = self.check_changed_entries(&row_result.entries);

        let inputs = self.generate_input_entries(&row_result.entries, &changed);

        let expected = self.generate_expected_entries(&row_result.entries);

        let line = row_result.line;
        self.prev = Some(row_result.entries);

        Ok(Some(EvaluatedRow {
            line,
            inputs,
            expected,
            update_output,
        }))
    }
}

impl<'a> EvaluatedRow<'a> {
    fn into_data_row(self, outputs: Vec<OutputValue>) -> DataRow<'a> {
        let outputs = self
            .expected
            .into_iter()
            .zip(outputs)
            .map(|(expected_entry, output_value)| OutputResultEntry {
                signal: expected_entry.signal,
                output: output_value,
                expected: expected_entry.value,
            })
            .collect();

        DataRow {
            inputs: self.inputs,
            outputs,
            line: self.line,
        }
    }
}
