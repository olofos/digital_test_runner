use crate::{Signal, SignalDir};

#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    test_data: String,
}

fn visual_elements<'a, 'b>(
    doc: &'a roxmltree::Document<'b>,
    name: &str,
) -> Vec<roxmltree::Node<'a, 'b>> {
    doc.descendants()
        .filter(|visual_element_node| {
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
        .collect()
}

fn attrib<'a, 'b>(node: roxmltree::Node<'a, 'b>, label: &str) -> Option<roxmltree::Node<'a, 'b>> {
    let Some(attribs) = node
        .descendants()
        .find(|n| n.tag_name().name() == "elementAttributes")
    else {
        return None;
    };
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

fn extract_signal_data<'a, 'b>(node: roxmltree::Node<'a, 'b>) -> Option<(&'a str, u8)> {
    let Some(label_node) = attrib(node, "Label") else {
        return None;
    };
    let Some(label) = label_node.text() else {
        return None;
    };

    let bits = if let Some(bits_node) = attrib(node, "Bits") {
        let bits_text = bits_node.text().unwrap_or("1");
        u8::from_str_radix(bits_text, 10).unwrap_or(1)
    } else {
        1
    };

    Some((label, bits))
}

pub fn parse(input: &str) -> anyhow::Result<(Vec<Signal>, Vec<Signal>, Vec<TestCase>)> {
    let doc = roxmltree::Document::parse(&input)?;

    let outputs = visual_elements(&doc, "Out")
        .into_iter()
        .filter_map(|node| extract_signal_data(node))
        .map(|(name, bits)| Signal {
            name: name.to_string(),
            bits,
            dir: SignalDir::Output,
        })
        .collect::<Vec<Signal>>();

    let input_iter = visual_elements(&doc, "In")
        .into_iter()
        .chain(visual_elements(&doc, "Clock"));

    let inputs = input_iter
        .filter_map(|node| extract_signal_data(node))
        .map(|(name, bits)| Signal {
            name: name.to_string(),
            bits,
            dir: SignalDir::Input,
        })
        .collect::<Vec<Signal>>();

    let test_cases = visual_elements(&doc, "Testcase")
        .into_iter()
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

            Some(TestCase { name, test_data })
        })
        .collect::<Vec<_>>();

    Ok((inputs, outputs, test_cases))
}
