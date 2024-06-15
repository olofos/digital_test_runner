use digital_test_runner::{dig, TestCase};
use std::io::{prelude::*, BufReader};

mod util;

#[derive(Debug)]
struct Cursor<T> {
    reader: BufReader<T>,
    line: String,
    index: usize,
}

impl<T: Read> Cursor<T> {
    pub fn new(reader: T) -> Self {
        Self {
            reader: std::io::BufReader::new(reader),
            line: String::new(),
            index: 0,
        }
    }

    pub fn grab(&mut self, len: impl Into<usize>) -> anyhow::Result<i64> {
        if self.index >= self.line.len() {
            self.line.clear();
            if self.reader.read_line(&mut self.line)? == 0 {
                anyhow::bail!("Unexpected end of file")
            };
            if self.line.ends_with('\n') {
                self.line.pop();
            }
            self.index = 0;
        }
        let len = len.into();
        if self.line.len() < self.index + len {
            Err(anyhow::anyhow!("Not enough data in line"))
        } else {
            let s = &self.line[self.index..(self.index + len)];
            self.index += len;
            Ok(i64::from_str_radix(s, 2)?)
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

    let mut stdin = child.stdin.take().unwrap();
    let mut cursor = Cursor::new(child.stdout.take().unwrap());

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
