use digital_test_runner::{dig, InputEntry, OutputEntry, Signal, SignalDirection, TestDriver};
use std::{ffi::OsStr, io::Write};
use util::Cursor;

mod util;

struct Driver {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    cursor: Cursor<std::process::ChildStdout>,
    error_count: usize,
    output_signals: Vec<Signal>,
}

impl TestDriver for Driver {
    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry],
    ) -> Result<Vec<OutputEntry>, anyhow::Error> {
        for input in inputs {
            write!(self.stdin, "{:01$b}", input.value, input.signal.bits)?;
        }
        writeln!(self.stdin)?;

        self.output_signals
            .iter()
            .map(|signal| {
                self.cursor
                    .grab(signal.bits)
                    .map(|value| OutputEntry { signal, value })
            })
            .collect::<Result<Vec<_>, _>>()
    }
}

impl Driver {
    fn try_new(path: impl AsRef<OsStr>, signals: &[Signal]) -> anyhow::Result<Self> {
        let mut child = std::process::Command::new(path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()?;

        let stdin = child.stdin.take().unwrap();
        let cursor = util::Cursor::new(child.stdout.take().unwrap());

        let output_signals = signals
            .iter()
            .filter(|s| {
                matches!(
                    s.dir,
                    SignalDirection::Output | SignalDirection::Bidirectional { .. }
                )
            })
            .cloned()
            .collect();

        Ok(Self {
            child,
            stdin,
            cursor,
            error_count: 0,
            output_signals,
        })
    }
}

impl Drop for Driver {
    fn drop(&mut self) {
        writeln!(self.stdin, "quit").unwrap();
        let _ = self.child.wait().unwrap();
    }
}

fn main() -> anyhow::Result<()> {
    for test_name in ["Counter", "74779"] {
        println!("Testing circuit {test_name}");
        let path = format!(
            "{}/tests/data/{}.dig",
            env!("CARGO_MANIFEST_DIR"),
            test_name
        );
        let dig_file = dig::parse(&std::fs::read_to_string(path)?)?;

        for test_num in 0..dig_file.test_cases.len() {
            println!(
                "Running test #{test_num} \"{}\"",
                dig_file.test_cases[test_num].name
            );
            let test_case = dig_file.load_test(test_num)?;

            let prog_path = util::compile_verilog(
                &format!("{}_int_tb", test_name),
                &[
                    &format!("{}.v", test_name),
                    &format!("{}_int_tb.v", test_name),
                ],
            )?;
            let mut driver = Driver::try_new(prog_path, &test_case.signals)?;

            test_case.run(&mut driver)?;

            if driver.error_count == 0 {
                println!("Test passed");
            } else {
                println!("Found {} failing assertions", driver.error_count);
            }
        }
        println!();
    }

    Ok(())
}
