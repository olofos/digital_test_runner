use digital_test_runner::{dig, TestCase};
use std::io::Write;

mod util;

fn main() -> anyhow::Result<()> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
    let dig_file = dig::parse(&std::fs::read_to_string(path)?)?;
    let test_case = TestCase::try_from_static_dig(&dig_file, 0)?;

    let counter_path = util::compile_verilog("counter_int_tb", &["Counter.v", "Counter_int_tb.v"])?;

    let mut child = std::process::Command::new(counter_path)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;

    let mut stdin = child.stdin.take().unwrap();
    let mut cursor = util::Cursor::new(child.stdout.take().unwrap());

    let mut error_count = 0;
    for row in &test_case {
        for input in row.inputs() {
            write!(stdin, "{:01$b}", input.value, input.signal.bits)?;
        }
        writeln!(stdin)?;

        for output in row.outputs() {
            let value = cursor.grab(output.signal.bits)?;
            if !output.value.check(value) {
                println!("Expected {} but got {}", output.value, value);
                error_count += 1;
            }
        }
    }
    if error_count == 0 {
        println!("All tests passed");
    } else {
        println!("Found {error_count} failing assertions");
    }

    Ok(())
}
