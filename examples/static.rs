use colored::{Color, Colorize};
use digital_test_runner::{dig, ExpectedValue};
use std::io::Write;

mod util;

fn main() -> anyhow::Result<()> {
    for test_name in ["Counter", "74779"] {
        println!("Testing circuit {test_name}");
        let path = format!(
            "{}/tests/data/{}.dig",
            env!("CARGO_MANIFEST_DIR"),
            test_name
        );
        let dig_file = dig::File::parse(&std::fs::read_to_string(path)?)?;
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

            let mut child = std::process::Command::new(prog_path)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()?;

            let mut stdin = child.stdin.take().unwrap();
            let mut cursor = util::Cursor::new(child.stdout.take().unwrap());

            let iter = match test_case.try_static_iter() {
                Ok(iter) => iter,
                Err(err) => {
                    println!("{err}");
                    println!();
                    continue;
                }
            };

            for row in iter {
                for input in &row.inputs {
                    print!("{} ", input.value);
                    write!(stdin, "{:01$b}", input.value, input.signal.bits)?;
                }
                writeln!(stdin)?;

                if !row.outputs.is_empty() {
                    print!(" =>  ");
                    for expected in &row.outputs {
                        let output = cursor.grab(expected.signal.bits)?;
                        let color = match (
                            expected.value != ExpectedValue::X,
                            expected.value.check(output),
                        ) {
                            (true, true) => Color::Green,
                            (true, false) => Color::Red,
                            (false, _) => Color::BrightBlack,
                        };
                        print!("{} ", format!("{}/{}", output, expected.value).color(color));
                    }
                }
                println!();
            }
            println!();
        }
    }

    Ok(())
}
