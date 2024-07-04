# digital_test_runner

Parse and run tests used in [hnemann's Digital](https://github.com/hneemann/Digital) logic designer and circuit simulator.
Tests give a simple description of the inputs and expected resulting outputs of a digital circuit.
This crate allows these tests to be reused to test other implementations of the same circuit, either in a different simulator
or in hardware.

## Usage

The simplest way of loading a test is to first load a `.dig` file

    use digital_test_runner::dig;
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
    let dig_file: dig::File = std::fs::read_to_string(path).unwrap().parse().unwrap();
    let test_case = dig_file.load_test(0).unwrap();