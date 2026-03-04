use std::env;
use std::fs;
use std::process::Command;

pub fn convert_tptp_file_to_smt2(input_path: &str, output_path: &str) -> Result<(), String> {
    let mut smt2 = convert_with_cvc5_parser(input_path)?;
    if !smt2.trim_start().starts_with("(set-logic") {
        smt2 = format!("(set-logic ALL)\n{}", smt2);
    }
    fs::write(output_path, smt2).map_err(|e| format!("Failed to write {}: {}", output_path, e))?;
    Ok(())
}

fn convert_with_cvc5_parser(input_path: &str) -> Result<String, String> {
    let cwd = env::current_dir().map_err(|e| format!("Failed to get current dir: {}", e))?;
    let cvc5_parser_bin = cwd.join("../bin/cvc5-1.0.5");

    if !cvc5_parser_bin.exists() {
        return Err(format!(
            "Missing converter binary: {}",
            cvc5_parser_bin.display()
        ));
    }

    let output = Command::new(&cvc5_parser_bin)
        .arg("-o")
        .arg("raw-benchmark")
        .arg("--parse-only")
        .arg("--output-lang=smt2")
        .arg(input_path)
        .output()
        .map_err(|e| format!("Failed to start {}: {}", cvc5_parser_bin.display(), e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "{} failed with status {}: {}",
            cvc5_parser_bin.display(),
            output
                .status
                .code()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "terminated by signal".to_string()),
            stderr.trim()
        ));
    }

    let smt2 = String::from_utf8_lossy(&output.stdout).to_string();
    if smt2.trim().is_empty() {
        return Err(format!(
            "{} produced empty SMT2 output",
            cvc5_parser_bin.display()
        ));
    }

    Ok(smt2)
}
