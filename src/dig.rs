use std::collections::HashSet;

use crate::{parser::HeaderParser, InputValue, Signal, SignalType};

#[derive(Debug, Clone)]
pub struct TestCaseDescription {
    pub name: String,
    pub test_data: String,
}

#[derive(Debug, Clone)]
pub struct DigFile {
    pub signals: Vec<Signal>,
    pub test_cases: Vec<TestCaseDescription>,
}

fn visual_elements<'a, 'b>(
    doc: &'a roxmltree::Document<'b>,
    name: &'static str,
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
        name_node.text() == Some(name)
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

fn extract_signal_data<'a>(node: roxmltree::Node<'a, '_>) -> Option<(&'a str, u8)> {
    let label = attrib(node, "Label")?.text()?;
    let bits = attrib(node, "Bits")
        .and_then(|node| node.text()?.parse().ok())
        .unwrap_or(1);

    Some((label, bits))
}

fn extract_input_data(node: roxmltree::Node) -> InputValue {
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

pub fn parse(input: &str) -> anyhow::Result<DigFile> {
    let doc = roxmltree::Document::parse(input)?;

    let output_signals = visual_elements(&doc, "Out")
        .filter_map(|node| extract_signal_data(node))
        .map(|(name, bits)| Signal {
            name: name.to_string(),
            bits,
            typ: SignalType::Output,
        });

    let inputs_signals = visual_elements(&doc, "In")
        .chain(visual_elements(&doc, "Clock"))
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
            typ: SignalType::Input { default },
        });

    let signals = Vec::from_iter(inputs_signals.chain(output_signals));

    let test_cases = visual_elements(&doc, "Testcase")
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
            let test_data = data_string_node.text()?.to_string();

            Some(TestCaseDescription { name, test_data })
        })
        .collect::<Vec<_>>();

    let mut test_signal_names: HashSet<String> = HashSet::new();
    let mut bidirectional: HashSet<String> = HashSet::new();
    for test_case in &test_cases {
        for name in HeaderParser::new(&test_case.test_data).parse()? {
            if let Some(stripped_name) = name.strip_suffix("_out") {
                let stripped_name = stripped_name.to_string();
                bidirectional.insert(stripped_name.clone());
                test_signal_names.insert(stripped_name);
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
        anyhow::bail!("Signals {missing} found in tests but not found in circuit");
    }

    let mut signals = signals;
    for name in bidirectional {
        let sig = signals
            .iter_mut()
            .find(|sig| sig.name == name)
            .expect("We already checked that all test signals appear in the circuit");
        let dir = std::mem::replace(&mut sig.typ, SignalType::Output);
        sig.typ = dir.try_into_bidirectional()?;
    }

    Ok(DigFile {
        signals,
        test_cases,
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        let input =
            std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/74779.dig"))
                .unwrap();
        let dig: DigFile = parse(&input).unwrap();
        dbg!(dig.signals);
    }
}
