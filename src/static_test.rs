use crate::{errors::NoError, InputEntry, OutputEntry, TestDriver};

#[derive(Debug)]
/// Trivial test driver that always returns an empty output.
///
/// This driver can be useful if the onlt goal is to get a list
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
