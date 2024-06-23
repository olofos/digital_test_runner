use digital_test_runner::{
    dig, DataEntry, InputValue, Signal, SignalDirection, TestCase, TestDriver,
};
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
        inputs: &[DataEntry<InputValue>],
    ) -> Result<Vec<DataEntry<'_, InputValue>>, anyhow::Error> {
        for input in inputs {
            write!(self.stdin, "{:01$b}", input.value, input.signal.bits)?;
        }
        writeln!(self.stdin)?;

        self.output_signals
            .iter()
            .map(|s| {
                self.cursor.grab(s.bits).map(|n| DataEntry {
                    signal: s,
                    value: InputValue::Value(n),
                    changed: true,
                })
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
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Counter.dig");
    let dig_file = dig::parse(&std::fs::read_to_string(path)?)?;

    for n in 0..dig_file.test_cases.len() {
        println!("Running test #{n} \"{}\"", dig_file.test_cases[n].name);
        let test_case = TestCase::try_from_dig(&dig_file, n)?;

        let counter_path =
            util::compile_verilog("counter_int_tb", &["Counter.v", "Counter_int_tb.v"])?;
        let mut driver = Driver::try_new(counter_path, &test_case.signals)?;

        test_case.run(&mut driver)?;

        if driver.error_count == 0 {
            println!("All tests passed");
        } else {
            println!("Found {} failing assertions", driver.error_count);
        }
    }

    Ok(())
}
