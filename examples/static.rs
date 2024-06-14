use digital_test_runner::{dig, InputValue, SignalDirection, TestCase};
use std::io::prelude::*;

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
    let mut args = std::env::args();
    let prog_name = args.next().unwrap();
    let Some(path) = args.next() else {
        println!("Usage: {prog_name} file.dig [num]");
        return Ok(());
    };
    let test_num: Option<usize> = args.next().map(|s| s.parse().ok()).flatten();
    println!("Loading file {path}");
    let input = std::fs::read_to_string(path)?;
    let dig_file = dig::parse(&input)?;

    println!("Signals");
    println!("=======");
    for signal in &dig_file.signals {
        print!(
            "{} ({} {}",
            signal.name,
            signal.bits,
            if signal.bits == 1 { "bit" } else { "bits" }
        );
        match &signal.dir {
            SignalDirection::Input { default } | SignalDirection::Bidirectional { default } => {
                println!(
                    ", {})",
                    match default {
                        InputValue::Value(n) =>
                            if (0..10).contains(n) {
                                format!("{n}")
                            } else {
                                format!("0x{n:x}")
                            },
                        InputValue::Z => String::from("Z"),
                    },
                );
            }
            SignalDirection::Output => println!(")"),
        }
    }
    println!();

    println!("Found {} test cases:", dig_file.test_cases.len());

    for (i, test_case) in dig_file.test_cases.iter().enumerate() {
        println!("{}: {}", i + 1, test_case.name);
    }
    println!();

    let test_num = if let Some(test_num) = test_num {
        test_num
    } else {
        use std::io::prelude::*;
        print!("Which one do you want to run? ");
        std::io::stdout().flush()?;
        let mut answer = String::new();
        std::io::stdin().read_line(&mut answer)?;
        let n = answer.trim().parse();
        n.unwrap_or(1)
    }
    .clamp(1, dig_file.test_cases.len());

    let test_case = TestCase::try_from_static_dig(&dig_file, test_num - 1)?;

    println!();
    println!("Test case {test_num} after transformation:");
    println!("{test_case}");

    let mut child = std::process::Command::new("/tmp/counter")
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
