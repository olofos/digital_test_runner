use colored::{Color, Colorize};
use digital_test_runner::{dig, InputEntry, OutputEntry, Signal, SignalDirection, TestDriver};
use miette::Result;
use std::{ffi::OsStr, io::Write};
use util::Cursor;

mod util;

struct Driver {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    cursor: Cursor<std::process::ChildStdout>,
    output_signals: Vec<Signal>,
}

impl TestDriver for Driver {
    type Error = std::io::Error;

    fn write_input_and_read_output(
        &mut self,
        inputs: &[InputEntry],
    ) -> Result<Vec<OutputEntry>, Self::Error> {
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

fn main() -> miette::Result<()> {
    for test_name in ["Counter", "74779"] {
        println!("Testing circuit {test_name}");
        let path = format!(
            "{}/tests/data/{}.dig",
            env!("CARGO_MANIFEST_DIR"),
            test_name
        );
        let dig_file = dig::File::open(path)?;

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
            )
            .map_err(|err| miette::miette!("{err}"))?;
            let mut driver = Driver::try_new(prog_path, &test_case.signals)
                .map_err(|err| miette::miette!("{err}"))?;

            let mut it = test_case.run_iter(&mut driver);

            while let Some(row) = it.next() {
                let row = row.map_err(|err| miette::miette!("{err}"))?;
                print!("{:2}: ", row.line);
                for input in &row.inputs {
                    print!("{} ", input.value);
                }
                if !row.outputs.is_empty() {
                    print!(" =>  ");
                    for output in &row.outputs {
                        let color = match (output.is_checked(), output.check()) {
                            (true, true) => Color::Green,
                            (true, false) => Color::Red,
                            (false, _) => Color::BrightBlack,
                        };
                        print!(
                            "{} ",
                            format!("{}/{}", output.output, output.expected).color(color)
                        );
                    }
                    if row.failing_outputs().count() > 0 {
                        print!(
                            " [{}]",
                            it.vars()
                                .into_iter()
                                .map(|(k, v)| format!("{k}={v}"))
                                .collect::<Vec<_>>()
                                .join(",")
                        );
                    }
                }
                println!();
            }

            println!();
        }
    }

    Ok(())
}
