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

