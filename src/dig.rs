use std::{collections::HashSet, ops::Range, str::FromStr};

use crate::{
    errors::{DigFileError, DigFileErrorKind},
    parser::HeaderParser,
    InputValue, Signal, SignalDirection,
};

/// Represent a test case in the dig file
#[derive(Debug, Clone)]
pub struct TestCaseDescription {
    /// The name of the test case
    pub name: String,
    /// The source code of the test
    pub source: String,
}

/// A parsed dig file
#[derive(Debug, Clone)]
pub struct File {
    /// The input and output signals of the circuit
    pub signals: Vec<Signal>,
    /// A list of test cases
    pub test_cases: Vec<TestCaseDescription>,
}

fn visual_elements<'a, 'b>(
    doc: &'a roxmltree::Document<'b>,
    names: &'static [&'static str],
) -> impl Iterator<Item = roxmltree::Node<'a, 'b>> {
    doc.descendants().filter(|visual_element_node| {
        if visual_element_node.tag_name().name() != "visualElement" {
            return false;
        }
        let Some(name_node) = visual_element_node
            .descendants()
            .find(|n| n.tag_name().name() == "elementName")
        else {
            return false;
        };
        name_node
            .text()
            .map(|name| names.contains(&name))
            .unwrap_or(false)
    })
}

fn attrib<'a, 'b>(node: roxmltree::Node<'a, 'b>, label: &str) -> Option<roxmltree::Node<'a, 'b>> {
    let attribs = node
        .descendants()
        .find(|n| n.tag_name().name() == "elementAttributes")?;

    for entry in attribs
        .descendants()
        .filter(|n| n.tag_name().name() == "entry")
    {
        let Some(s) = entry.first_element_child() else {
            continue;
        };
        if s.tag_name().name() == "string" && s.text() == Some(label) {
            return entry.last_element_child();
        }
    }
    None
}

fn extract_signal_data<'a>(node: roxmltree::Node<'a, '_>) -> Option<(&'a str, usize)> {
    let label = attrib(node, "Label")?.text()?;
    let bits = attrib(node, "Bits")
        .and_then(|node| node.text()?.parse().ok())
        .unwrap_or(1);

    Some((label, bits))
}

fn extract_input_data(node: roxmltree::Node<'_, '_>) -> InputValue {
    attrib(node, "InDefault")
        .and_then(|default_node| {
            if default_node.attribute("z") == Some("true") {
                Some(InputValue::Z)
            } else {
                default_node
                    .attribute("v")
                    .and_then(|v| v.parse().ok().map(InputValue::Value))
            }
        })
        .unwrap_or(InputValue::Value(0))
}

impl FromStr for File {
    type Err = DigFileError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        File::parse(s)
    }
}

fn text_pos_to_range(input: &str, pos: roxmltree::TextPos) -> Range<usize> {
    let pos: usize = input
        .lines()
        .take(pos.row as usize - 1)
        .map(|line| line.len() + 1)
        .sum::<usize>()
        + pos.col as usize
        - 1;

    pos..pos
}

impl File {
    /// Parse the input string as dig file
    pub fn parse(input: &str) -> Result<File, DigFileError> {
        let doc = roxmltree::Document::parse(input).map_err(|err| {
            let span = text_pos_to_range(input, err.pos());
            DigFileErrorKind::XMLError(err, span)
        })?;

        let output_signals = visual_elements(&doc, &["Out"])
            .filter_map(|node| extract_signal_data(node))
            .map(|(name, bits)| Signal {
                name: name.to_string(),
                bits,
                dir: SignalDirection::Output,
            });

        let inputs_signals = visual_elements(&doc, &["In", "Clock"])
            .filter_map(|node| {
                if let Some((name, bits)) = extract_signal_data(node) {
                    let default = extract_input_data(node);
                    Some((name, bits, default))
                } else {
                    None
                }
            })
            .map(|(name, bits, default)| Signal {
                name: name.to_string(),
                bits,
                dir: SignalDirection::Input { default },
            });

        let signals = Vec::from_iter(inputs_signals.chain(output_signals));

        let test_cases = visual_elements(&doc, &["Testcase"])
            .filter_map(|node| {
                let name: String = if let Some(label_node) = attrib(node, "Label") {
                    label_node.text()?.to_string()
                } else {
                    String::from("(unnamed)")
                };
                let test_data_node = attrib(node, "Testdata")?;
                if test_data_node.tag_name().name() != "testData" {
                    return None;
                }
                let data_string_node = test_data_node.first_element_child()?;
                if data_string_node.tag_name().name() != "dataString" {
                    return None;
                }
                let source = data_string_node.text()?.to_string();

                Some(TestCaseDescription { name, source })
            })
            .collect::<Vec<_>>();

        let mut test_signal_names: HashSet<String> = HashSet::new();
        let mut bidirectional: HashSet<String> = HashSet::new();
        for test_case in &test_cases {
            for name in HeaderParser::new(&test_case.source)
                .parse()
                .map_err(|_| DigFileErrorKind::EmptyTest)?
            {
                if let Some(stripped_name) = name.strip_suffix("_out") {
                    let stripped_name = stripped_name.to_string();
                    bidirectional.insert(stripped_name);
                } else {
                    test_signal_names.insert(name);
                }
            }
        }

        let signal_names: HashSet<String> = signals.iter().map(|s| s.name.clone()).collect();

        if !test_signal_names.is_subset(&signal_names) {
            let missing = test_signal_names
                .difference(&signal_names)
                .cloned()
                .collect::<Vec<_>>()
                .join(", ");
            return Err(DigFileErrorKind::MissingSignals(missing).into());
        }

        let mut signals = signals;
        for name in bidirectional {
            let sig = signals
                .iter_mut()
                .find(|sig| sig.name == name)
                .expect("We already checked that all test signals appear in the circuit");
            let dir = std::mem::replace(&mut sig.dir, SignalDirection::Output);
            let SignalDirection::Input { default } = dir else {
                unreachable!(
                    "By definition we know that there will be an input signal called {name}"
                );
            };
            sig.dir = SignalDirection::Bidirectional { default };
        }

        Ok(File {
            signals,
            test_cases,
        })
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use super::*;
    use rstest::rstest;

    #[test]
    fn test() {
        let input =
            std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/74779.dig"))
                .unwrap();
        let dig: File = input.parse().unwrap();
        dbg!(dig.signals);
    }

    #[rstest]
    #[case(1, 1, "a")]
    #[case(2, 1, "d")]
    #[case(3, 1, "g")]
    #[case(2, 3, "f")]
    fn test_text_pos_to_range(#[case] row: u32, #[case] col: u32, #[case] expected: &str) {
        let input = "abc\ndef\nghi";
        let pos = roxmltree::TextPos::new(row, col);
        let range = text_pos_to_range(input, pos);
        assert_eq!(&input[range.start..(range.end + 1)], expected);
    }

    #[test]
    fn test_error() {
        let input = r#"<?xml version="1.0" encoding="utf-8"?>
<circuit>
  <version>1</version>
  <attributes>
    <entry>
      <string>shapeType</string>
      <shapeType>DIL</shapeType>
    </entry>
</circuit>
"#;
        let Err(err) = File::parse(input) else {
            panic!("Expected an error")
        };
        println!("{err:?} {}", err.source().unwrap());
        assert!(matches!(
            err,
            DigFileError(DigFileErrorKind::XMLError(_, _))
        ))
    }
}
