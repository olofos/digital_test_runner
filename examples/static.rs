use std::collections::HashMap;
use std::io::prelude::*;

use digital_test_runner::{dig, InputValue, SignalDirection, TestCase};

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

    let mut stdout = std::io::BufReader::new(child.stdout.take().unwrap());
    let mut stdin = child.stdin.take().unwrap();

    let mut error_count = 0;
    for row in &test_case {
        for input in row.changed_inputs() {
            writeln!(stdin, "{} {}", input.signal.name, input.value)?;
        }
        writeln!(stdin, "STEP")?;

        let mut values = HashMap::new();

        for line in (&mut stdout)
            .lines()
            .take_while(|l| !l.as_ref().unwrap().is_empty())
        {
            let mut pair: Vec<String> = line?.split_whitespace().map(String::from).collect();
            let value = pair[1].parse::<i64>()?;
            values.insert(pair.swap_remove(0), value);
        }

        for output in row.checked_outputs().filter(|entry| {
            values
                .get(&entry.signal.name)
                .map(|&v| !entry.value.check(v))
                .unwrap_or(false)
        }) {
            eprintln!(
                "Expected {} but got {}",
                output.value,
                values.get(&output.signal.name).unwrap()
            );
            error_count += 1;
        }
    }
    if error_count == 0 {
        eprintln!("All tests passed");
    } else {
        eprintln!("Found {error_count} failing assertions");
    }

    Ok(())
}
