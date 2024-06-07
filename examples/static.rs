use digital_test_runner::{dig, InputValue, SignalType, TestCase};

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args();
    let prog_name = args.next().unwrap();
    let Some(path) = args.next() else {
        eprintln!("Usage: {prog_name} file.dig [num]");
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
        match &signal.typ {
            SignalType::Input { default } | SignalType::Bidirectional { default } => {
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
            SignalType::Output => println!(")"),
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

    println!();
    for row in &test_case {
        for input in row.inputs() {
            if input.changed {
                print!("{} ", input.value);
            } else {
                print!("- ");
            }
        }
        print!("| ");
        for output in row.outputs() {
            if !output.value.is_x() {
                print!("{} ", output.value);
            } else {
                print!("- ");
            }
        }
        println!();
    }

    Ok(())
}
