//! `--lean`: write the shortened proof as a Lean file and have Lean check it.
//!
//! The translation is done by `python/tolean.py`, which turns every step into
//! an explicit proof term. A file that Lean accepts without a message
//! therefore certifies the proof and its step count.

use std::path::Path;
use std::process::Command;

const LEAN_PROJECT: &str = "../lean";
const TRANSLATOR: &str = "../python/tolean.py";

/// Translate `proof_file` and check the result. Returns the Lean file on
/// success and what went wrong otherwise.
pub fn export_and_check(proof_file: &str) -> Result<String, String> {
    let stem = Path::new(proof_file).file_stem().unwrap().to_string_lossy();
    let lean_file = format!("{}/Proof/{}.lean", LEAN_PROJECT, stem);
    // a file left by an earlier run must not pass for this translation
    let _ = std::fs::remove_file(&lean_file);
    let translation = Command::new("python3")
        .args([TRANSLATOR, proof_file])
        .output()
        .map_err(|e| format!("Failed to start python3 for {}: {}", TRANSLATOR, e))?;
    // the first line names the file, the others describe the proof
    for line in String::from_utf8_lossy(&translation.stdout).lines().skip(1) {
        crate::klog_info!("[LEAN] {}", line.trim());
    }
    if !Path::new(&lean_file).exists() {
        let reason = String::from_utf8_lossy(&translation.stderr);
        let reason = reason.lines().last().unwrap_or("no message");
        return Err(format!("The proof could not be translated: {}", reason));
    }
    if !translation.status.success() {
        return Err(format!(
            "{} has steps that are not a single rewrite",
            lean_file
        ));
    }

    let check = Command::new("lean")
        .arg(format!("Proof/{}.lean", stem))
        .current_dir(LEAN_PROJECT)
        .output()
        .map_err(|e| format!("{} written, but `lean` did not start: {}", lean_file, e))?;
    let messages = [check.stdout, check.stderr].concat();
    if check.status.success() && messages.is_empty() {
        Ok(lean_file)
    } else {
        Err(format!(
            "Lean does not accept {}:\n{}",
            lean_file,
            String::from_utf8_lossy(&messages).trim_end()
        ))
    }
}
