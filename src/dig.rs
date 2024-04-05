use crate::{InputSignal, InputValue, OutputSignal};

#[derive(Debug, Clone)]
pub struct TestCaseDescription {
    pub name: String,
    pub test_data: String,
}

#[derive(Debug, Clone)]
pub struct DigFile {
    pub inputs: Vec<InputSignal>,
    pub outputs: Vec<OutputSignal>,
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
    let label_node = attrib(node, "Label")?;
    let label = label_node.text()?;

    let bits = attrib(node, "Bits")
        .and_then(|node| node.text()?.parse().ok())
        .unwrap_or(1);

    Some((label, bits))
}

fn extract_input_data(node: roxmltree::Node) -> InputValue {
    let (default_v, default_z) = if let Some(default_node) = attrib(node, "InDefault") {
        (
            default_node.attribute("v").and_then(|v| v.parse().ok()),
            default_node.attribute("z") == Some("true"),
        )
    } else {
        (None, false)
    };

    if default_z {
        InputValue::Z
    } else if let Some(v) = default_v {
        InputValue::Value(v)
    } else {
        InputValue::Value(0)
    }
}

pub fn parse(input: &str) -> anyhow::Result<DigFile> {
    let doc = roxmltree::Document::parse(input)?;

    let outputs = visual_elements(&doc, "Out")
        .filter_map(|node| extract_signal_data(node))
        .map(|(name, bits)| OutputSignal {
            name: name.to_string(),
            bits,
        })
        .collect();

    let input_iter = visual_elements(&doc, "In").chain(visual_elements(&doc, "Clock"));

    let inputs = input_iter
        .filter_map(|node| {
            if let Some((name, bits)) = extract_signal_data(node) {
                let default = extract_input_data(node);
                Some((name, bits, default))
            } else {
                None
            }
        })
        .map(|(name, bits, default)| InputSignal {
            name: name.to_string(),
            bits,
            default,
        })
        .collect();

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

    Ok(DigFile {
        inputs,
        outputs,
        test_cases,
    })
}
