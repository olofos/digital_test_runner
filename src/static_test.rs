use crate::{
    errors::{IterationError, NoError, RuntimeError, StaticIteratorError},
    DataRow, DataRowIterator, ExpectedEntry, InputEntry, OutputEntry, TestCase, TestDriver,
};

#[derive(Debug)]
/// Trivial test driver that always returns an empty output.
///
/// This driver can be useful if the only goal is to get a list
/// of inputs and expected outputs for a test.
/// This only works for a "static" test, which does not
/// directly read the outputs from the DUT other then through
/// the test assertions.
pub struct Driver;
impl TestDriver for Driver {
    type Error = NoError;

    fn write_input_and_read_output(
        &mut self,
        _inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
        Ok(vec![])
    }
}

/// A single row of input values and expected values
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticDataRow<'a> {
    /// List of input values
    pub inputs: Vec<InputEntry<'a>>,
    /// List of output values together with the expected value
    pub expected: Vec<ExpectedEntry<'a>>,
    /// Line number of the test source code
    pub line: usize,
}

/// An iterator over the test results for a static test
#[derive(Debug)]
pub struct StaticDataRowIterator<'a> {
    it: DataRowIterator<'a, 'static, Driver>,
}

impl TestCase {
    /// Try to construct a static iterator
    pub fn try_iter_static(&self) -> Result<StaticDataRowIterator<'_>, StaticIteratorError> {
        if !self.read_outputs.is_empty() {
            let list = self
                .read_outputs
                .iter()
                .map(|i| self.signals[*i].name.clone())
                .collect::<Vec<_>>()
                .join(", ");
            return Err(StaticIteratorError(list));
        }
        let it = DataRowIterator::try_new(self, Box::leak(Box::new(Driver)))
            .expect("There shouldn't be any possible errors here");
        Ok(StaticDataRowIterator { it })
    }
}

impl<'a> From<DataRow<'a>> for StaticDataRow<'a> {
    fn from(row: DataRow<'a>) -> Self {
        let DataRow {
            inputs,
            outputs,
            line,
        } = row;
        let expected = outputs
            .into_iter()
            .map(|out| ExpectedEntry {
                signal: out.signal,
                value: out.expected,
            })
            .collect();
        Self {
            inputs,
            expected,
            line,
        }
    }
}

impl<'a> Iterator for StaticDataRowIterator<'a> {
    type Item = Result<StaticDataRow<'a>, RuntimeError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.it.next() {
            None => None,
            Some(Err(IterationError::Driver(_))) => unreachable!(),
            Some(Err(IterationError::Runtime(err))) => Some(Err(err)),
            Some(Ok(data_row)) => Some(Ok(data_row.into())),
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{InputValue, ParsedTestCase, Signal};

    use super::*;

    #[test]
    fn static_iterator_works() -> miette::Result<()> {
        let input = r"
    A B
    0 0
    0 1
    1 0
    1 1
    ";

        let known_inputs = vec![Signal::input("A", 1, 0)];
        let known_outputs = vec![Signal::output("B", 1)];
        let known_signals = Vec::from_iter(known_inputs.into_iter().chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;
        let mut it = testcase.try_iter_static()?;

        for (line, inp, outp, changed) in [
            (3, 0, 0, true),
            (4, 0, 1, false),
            (5, 1, 0, true),
            (6, 1, 1, false),
        ] {
            assert_eq!(
                it.next().unwrap()?,
                StaticDataRow {
                    inputs: vec![InputEntry {
                        signal: &known_signals[0],
                        value: InputValue::Value(inp),
                        changed
                    }],
                    expected: vec![ExpectedEntry {
                        signal: &known_signals[1],
                        value: crate::ExpectedValue::Value(outp)
                    }],
                    line
                }
            );
        }

        assert!(it.next().is_none());

        Ok(())
    }

    #[test]
    fn try_iter_static_gives_error_if_test_is_not_static() -> miette::Result<()> {
        let input = r"
    A B C D
    0 0 X X
    (B) (C) X X
    ";

        let known_inputs = vec![Signal::input("A", 1, 0)];
        let known_outputs = vec![
            Signal::output("B", 1),
            Signal::output("C", 1),
            Signal::output("D", 1),
        ];
        let known_signals = Vec::from_iter(known_inputs.into_iter().chain(known_outputs));
        let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;
        let Err(StaticIteratorError(list)) = testcase.try_iter_static() else {
            panic!("Expected an error")
        };
        assert_eq!(list, "B, C");

        Ok(())
    }
}
