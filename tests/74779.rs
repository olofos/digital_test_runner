use digital_test_runner::{
    dig::{parse, DigFile},
    TestCase,
};

#[test]
fn test() {
    let input =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/74779.dig"))
            .unwrap();
    let dig: DigFile = parse(&input).unwrap();
    let _test_case = TestCase::try_from_static_dig(&dig, 0).unwrap();
}
