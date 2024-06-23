use digital_test_runner::dig::{parse, DigFile};

#[test]
fn load_file() {
    let input =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/74779.dig"))
            .unwrap();
    let dig: DigFile = parse(&input).unwrap();
    let _ = dig.load_test(0).unwrap();
}
