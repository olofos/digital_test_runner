use digital_test_runner::dig;

#[test]
fn load_file() {
    let input =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/74779.dig"))
            .unwrap();
    let dig: dig::File = input.parse().unwrap();
    let _ = dig.load_test(0).unwrap();
}
