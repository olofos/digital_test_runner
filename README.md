# digital_test_runner

Parse and run tests used in [hnemann's Digital](https://github.com/hneemann/Digital) logic designer and circuit simulator.
Tests give a simple description of the inputs and expected resulting outputs of a digital circuit.
This crate allows these tests to be reused to test other implementations of the same circuit, either in a different simulator
or in hardware.

## Usage

The simplest way of loading a test is to load a `.dig` file and then load a particular test by number or by name

    use digital_test_runner::{dig,TestCase};
    fn load_test(path: &std::path::Path, n: usize) -> TestCase {
        let dig_file = dig::File::open(path).unwrap();
        dig_file.load_test(n).unwrap()
    }

To actually run the test we need a driver which is implementing the `TestDriver` trait.

## Comparison with Digital

Here are some known differences in how test cases are interpreted by this crate compared to with what the original Digital program does:
- The `program`, `memory` and `init` statements are currently not supported.
- If the test directly references the value of an output signal in an expression and the device under test outputs a high impedence `Z` value for that signal this crate will give an error. Digital instead randomly assigns a high or low value to the signal when evaluating the expression.
- This crate is less strict when evaluating expressions for loop bounds. Digital requires the bound in `loop` and `repeat` statements to be a constant, while this crate accepts any expression. Note that the bound is evaluated once when entering the loop, not on each iteration.
