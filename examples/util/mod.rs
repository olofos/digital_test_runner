use std::{path::PathBuf, process::Command};

pub fn compile_verilog(name: &str, sources: &[&str]) -> anyhow::Result<PathBuf> {
    let iverilog_path = which::which("iverilog")?;
    let mut cmd = Command::new(iverilog_path);
    let output_path = std::env::temp_dir().join(name);

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
