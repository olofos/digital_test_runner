use std::io::{BufRead, BufReader, Read};
use std::{path::PathBuf, process::Command};

use digital_test_runner::InputValue;

pub fn compile_verilog(name: &str, sources: &[&str]) -> anyhow::Result<PathBuf> {
    let iverilog_path = which::which("iverilog")?;
    let mut cmd = Command::new(iverilog_path);
    let output_path = std::env::temp_dir().join(name);

    cmd.arg("-g2012");

    for source in sources {
        cmd.arg(format!(
            "{}/tests/data/{}",
            env!("CARGO_MANIFEST_DIR"),
            source
        ));
    }

    cmd.arg("-o");
    cmd.arg(&output_path);

    let mut child = cmd.spawn()?;
    if child.wait()?.success() {
        Ok(output_path)
    } else {
        Err(anyhow::anyhow!("Error while executing iverilog"))
    }
}

#[derive(Debug)]
pub struct Cursor<T> {
    reader: BufReader<T>,
    line: String,
    index: usize,
}

impl<T: Read> Cursor<T> {
    pub fn new(reader: T) -> Self {
        Self {
            reader: std::io::BufReader::new(reader),
            line: String::new(),
            index: 0,
        }
    }

    pub fn grab(&mut self, len: impl Into<usize>) -> anyhow::Result<InputValue> {
        if self.index >= self.line.len() {
            loop {
                self.line.clear();
                if self.reader.read_line(&mut self.line)? == 0 {
                    anyhow::bail!("Unexpected end of file")
                };
                if self.line.starts_with("> ") {
                    if self.line.ends_with('\n') {
                        self.line.pop();
                    }
                    self.index = 2;
                    break;
                }
            }
        }
        let len = len.into();
        if self.line.len() < self.index + len {
            Err(anyhow::anyhow!("Not enough data in line"))
        } else {
            let s = &self.line[self.index..(self.index + len)];
            self.index += len;
            if s.contains('x') {
                eprintln!("Warning, unexpected x in data");
                Ok(InputValue::Value(0))
            } else if s.contains('z') {
                Ok(InputValue::Z)
            } else {
                Ok(InputValue::Value(i64::from_str_radix(s, 2)?))
            }
        }
    }
}
