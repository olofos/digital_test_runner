use digital_test_runner::dig;

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
            let it = match test_case.try_iter_static() {
                Ok(it) => it,
                Err(err) => {
                    println!("{err}");
                    continue;
                }
            };

            for row in it {
                let row = row?;
                for input in row.inputs {
                    print!("{} ", input.value);
                }
                print!("| ");
                if !row.expected.is_empty() {
                    for expected in row.expected {
                        print!("{} ", expected.value);
                    }
                }
                println!();
            }
        }
    }

    Ok(())
}
