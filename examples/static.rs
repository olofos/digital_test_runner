use digital_test_runner::{dig, TestCase};
use std::io::prelude::*;

mod util;

#[derive(Debug, Clone)]
struct Cursor<'a> {
    slice: &'a str,
}

impl<'a> Cursor<'a> {
    pub fn new(slice: impl Into<&'a str>) -> Self {
        Self {
            slice: slice.into(),
        }
    }

    pub fn grab(&mut self, len: impl Into<usize>) -> anyhow::Result<&'a str> {
        let len = len.into();
        if self.slice.len() < len {
            Err(anyhow::anyhow!("Unexpected end of input"))
        } else {
            let result;
            (result, self.slice) = self.slice.split_at(len);
            Ok(result)
        }
    }
}

fn main() -> anyhow::Result<()> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
    let dig_file = dig::parse(&std::fs::read_to_string(path)?)?;
    let test_case = TestCase::try_from_static_dig(&dig_file, 0)?;

    let counter_path = util::compile_verilog("counter_int_tb", &["Counter.v", "Counter_int_tb.v"])?;

    let mut child = std::process::Command::new(counter_path)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;

    let mut lines = std::io::BufReader::new(child.stdout.take().unwrap()).lines();
    let mut stdin = child.stdin.take().unwrap();

    let mut error_count = 0;
    for row in &test_case {
        for input in row.inputs() {
            write!(stdin, "{:01$b}", input.value, input.signal.bits as usize)?;
        }
        writeln!(stdin)?;

        let line = lines.next().ok_or(anyhow::anyhow!("Unexpected EOF"))??;
        let mut cursor = Cursor::new(line.as_str());
        for output in row.outputs() {
            let value = i64::from_str_radix(cursor.grab(output.signal.bits)?, 2)?;
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
