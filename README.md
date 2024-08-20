[![Latest version](https://img.shields.io/crates/v/digital_test_runner.svg)](https://crates.io/crates/digital_test_runner)
[![Documentation](https://docs.rs/digital_test_runner/badge.svg)](https://docs.rs/digital_test_runner)
[![Build Status](https://github.com/olofos/digital_test_runner/workflows/main/badge.svg)](https://github.com/olofos/digital_test_runner/actions?workflow=CI)
[![MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/olofos/digital_test_runner/blob/master/LICENSE-MIT)
[![Apache](https://img.shields.io/badge/license-Apache-blue.svg)](https://github.com/olofos/digital_test_runner/blob/master/LICENSE-APACHE)


# digital_test_runner

<!-- cargo-rdme start -->

Parse and run tests used in [hnemann's Digital](https://github.com/hneemann/Digital) logic designer and circuit simulator.
Tests give a simple description of the inputs and expected resulting outputs of a digital circuit.
This crate allows these tests to be reused to test other implementations of the same circuit, either in a different simulator
or in hardware.

### Usage

The simplest way of loading a test is to load a `.dig` file and then load a particular test by number or by name
```rust
use digital_test_runner::{dig,TestCase};

let dig_file = dig::File::open(path).unwrap();
let test_case = dig_file.load_test(n).unwrap();
```
To actually run the test we need a driver which is implementing the [TestDriver](https://docs.rs/digital_test_runner/latest/digital_test_runner/trait.TestDriver.html) trait.
This trait describes the communication between the test runner and the device under test.
Once we have a driver we can use the [TestCase::run_iter](https://docs.rs/digital_test_runner/latest/digital_test_runner/struct.TestCase.html#method.run_iter) function to obtain an iterator over the rows of the test.
Since both the driver and the test itself can fail during the execution of the test, each row is wrapped in  a `Result`.
Once we unwrap the row we can examine it to find for example if all output signals matched the expected values.
```rust
for row in test_case.run_iter(&mut driver)? {
    let row = row?;
    for entry in row.failing_outputs() {
        println!("{}: {} expected {} but found {}", row.line, entry.signal.name, entry.expected, entry.output);
    }
}
```

#### Implementing a driver

The [TestDriver](https://docs.rs/digital_test_runner/latest/digital_test_runner/trait.TestDriver.html) trait has a single required method, `write_input_and_read_output`,
which takes a list of values for the input signals which should be written to the device under test.
The driver should then wait for the output signals to settle, read them back and return a list of the read output values.

The list of output values should always be given in the same order for each invocation of `write_input_and_read_output`.
This allows us to detect some errors, such as missing output values read by the test program, already when the iterator is constructed.
To do this, the [TestCase::run_iter](https://docs.rs/digital_test_runner/latest/digital_test_runner/struct.TestCase.html#method.run_iter) constructor writes the default value of all inputs and reads the corresponding outputs before constructing the iterator.

Since `write_input_and_read_output` performs some form of IO it can potentially fail.
Hence, the trait comes with an associated error type `TestDriver::Error`, which should implement [std::error::Error](https://doc.rust-lang.org/stable/core/error/trait.Error.html).

The [TestDriver](https://docs.rs/digital_test_runner/latest/digital_test_runner/trait.TestDriver.html) trait has a second provided method `write_input` which is called when some input should be written to the device under test,
but the test does not care about the resulting output. By default this is implemented by calling `write_input_and_read_output` and discarding the output,
but a driver can implement its own version of `write_input` as an optimization if reading the output values is costly.

If the goal is to translate the test to a different language, a trivial driver is provided in [static_test::Driver](https://docs.rs/digital_test_runner/latest/digital_test_runner/static_test/struct.Driver.html).
This driver does not provide any output data, but the runner still gives a list of inputs and expected outputs.
This only works for simple "static" tests, that is, test which do not directly read the value of any output signals.

#### Manually loading a test

Instead of reading a test from a `dig` file it can be constructed directly from its source code.
However, the `dig` file does not only provide us with the source code for the test, but also with a description of the input and output signals.
By just parsing the source code we get a [ParsedTestCase](https://docs.rs/digital_test_runner/latest/digital_test_runner/parsed_test_case/struct.ParsedTestCase.html).
To turn this into a full [TestCase](https://docs.rs/digital_test_runner/latest/digital_test_runner/struct.TestCase.html) we need to provide a list of [Signal](https://docs.rs/digital_test_runner/latest/digital_test_runner/struct.Signal.html)s
to the [ParsedTestCase::with_signals](https://docs.rs/digital_test_runner/latest/digital_test_runner/parsed_test_case/struct.ParsedTestCase.html#method.with_signals) method.
For an example of this setup see the complete example below.

#### Inputs and outputs

This crate deals a lot with "inputs" and "outputs". These words are always used with respect to the device under test.
Hence, an input is a value that is written from the test runner to the DUT, and an output is read from the DUT by the test runner.

#### Values

This crate provides several value types:
- [InputValue](https://docs.rs/digital_test_runner/latest/digital_test_runner/value/enum.InputValue.html): A value written to the DUT
- [OutputValue](https://docs.rs/digital_test_runner/latest/digital_test_runner/value/enum.OutputValue.html): A value read from the DUT
- [ExpectedValue](https://docs.rs/digital_test_runner/latest/digital_test_runner/value/enum.ExpectedValue.html): An expected value provided by the test and compared to an output value

These values are defined as enums and all have two variants in common: a `Value(i64)` which represents an actual integer value, and a `Z` which represents a high impedance state.
Note that this is a simpler value model than what is available in for example Verilog, since either all or none of the bits making up the value are high impedance.

Additionally, the [OutputValue](https://docs.rs/digital_test_runner/latest/digital_test_runner/value/enum.OutputValue.html) and [ExpectedValue](https://docs.rs/digital_test_runner/latest/digital_test_runner/value/enum.ExpectedValue.html) both have `X` variants.
For an expected value, `X` represents that the test does not care about what the output value is.
Such an expected value *always* checks as equal to the output value.
For an output value `X` represents an unknown value, and can be returned by the driver if a value cannot be read
(though if the value can never be read it is probably better to just leave it out of the returned list of output values).
Such a value will *never* checks as equal to the expected value, unless the expected value is also `X`.

#### Complete example

Here is a complete example where a test is loaded from source, with the signals manually defined, as well as a simple driver.
In this simple example the driver is not communicating with a device under test, but simply implementing the logic itself.
Like this crate, this example uses [miette](https://crates.io/crates/miette) for error handling.

For a larger example, including a driver that does communicate with the device under test, see the `examples/` directory of the source code.
```rust
use digital_test_runner::{InputEntry, InputValue, OutputEntry, OutputValue, ParsedTestCase, Signal, TestDriver};

// Error type for driver
#[derive(Debug)]
struct Error(&'static str);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for Error {}

// Implement driver
struct Driver(Signal);

impl TestDriver for Driver {
    type Error = Error;

    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
        let input = inputs.get(0).ok_or(Error("No input"))?;
        let value = input.value.value().ok_or(Error("Unexpected Z"))?;
        let value = if value == 0 { 1 } else { 0 };
        Ok(vec![OutputEntry {
            signal: &self.0,
            value: value.into(),
        }])
    }
}

fn main() -> miette::Result<()> {
    let source = r#"
      A B
      0 1
      1 0
    "#;

    let parsed_test: ParsedTestCase = source.parse()?;

    let signals = vec![Signal::input("A", 1, 0), Signal::output("B", 1)];
    let testcase = parsed_test.with_signals(signals)?;

    let mut driver = Driver(Signal::output("B", 1));
    for row in testcase.run_iter(&mut driver)? {
        for output in row?.outputs {
            assert!(output.check());
        }
    }

    Ok(())
}
```

### Comparison with Digital

Here are some known differences in how test cases are interpreted by this crate compared to with what the original Digital program does:
- The `program`, `memory` and `init` statements are currently not supported.
- If the test directly references the value of an output signal in an expression and the device under test outputs a high impedance `Z` value for that signal this crate will give an error.
  Digital instead randomly assigns a high or low value to the signal when evaluating the expression.
- This crate is less strict when evaluating expressions for loop bounds.
  Digital requires the bound in `loop` and `repeat` statements to be a constant, while this crate accepts any expression.
  Note that the bound is evaluated once when entering the loop, not on each iteration.

<!-- cargo-rdme end -->
