use digital_test_runner::{dig, InputValue, TestCase};

fn main() -> anyhow::Result<()> {
    let path = std::env::args().nth(1).unwrap_or(String::from("ALU.dig"));
    println!("{path}");
    let input = std::fs::read_to_string(path).unwrap();
    let dig_file = dig::parse(&input).unwrap();

    println!("Inputs");
    println!("=======");
    for signal in &dig_file.inputs {
        println!(
            "{} {} {} ({})",
            signal.name,
            signal.bits,
            if signal.bits == 1 { "bit" } else { "bits" },
            match &signal.default {
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
    println!();

    println!("Outputs");
    println!("=======");
    for signal in &dig_file.outputs {
        println!(
            "{} {} {}",
            signal.name,
            signal.bits,
            if signal.bits == 1 { "bit" } else { "bits" }
        );
    }
    println!();

    println!("Found {} test cases:", dig_file.test_cases.len());

    for test_case in &dig_file.test_cases {
        println!("{}", test_case.name);
    }
    println!();

    let test_num = 2;

    let test_case = TestCase::try_from_dig(&dig_file, test_num)?;

    println!();
    println!("Test case {test_num} after transformation:");
    println!("{test_case}");

    // let result = test_case.run();
    // for row in result {
    //     println!("{row}");
    // }

    Ok(())
}
