use std::fs;
use std::path::Path;
use std::process::Command;

/// Run Twee on a given input file and save the raw Twee proof output.
pub fn run_twee_only(input: &str, output: &str) {
    let input_path = Path::new(input);
    if !input_path.exists() {
        crate::klog_error!(
            "[ERROR] Input file does not exist: {}",
            input_path.display()
        );
        return;
    }

    let output_path = Path::new(output);
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).expect("Failed to create output directory");
    }

    crate::klog_info!("[INFO] Phase 0: Running Twee.");
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());

    run_twee(input_path.to_str().unwrap(), output_path.to_str().unwrap());
}

/// Helper: actually runs the Twee binary and stores raw output.
pub fn run_twee(input_file: &str, output_file: &str) {
    let twee_bin = Path::new("../bin/twee");
    let output = Command::new(twee_bin)
        .arg("--quiet")
        .arg(input_file)
        .output()
        .expect("Failed to run Twee");

    let twee_output = String::from_utf8(output.stdout).expect("Twee output was not valid UTF-8");
    fs::write(output_file, twee_output).expect("Failed to write Twee output");

    crate::klog_debug!("[DEBUG] Twee proof written to {}", output_file);
}
