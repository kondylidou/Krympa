use std::fs;
use std::path::Path;
use std::process::Command;
use crate::proof_turnaround::eq_proof_procedure;

/// Run Vampire on a given input file and save its proof.
pub fn run_vampire_only(input: &str, output: &str) {
    let input_path = Path::new(input);
    if !input_path.exists() {
        eprintln!(
            "[ERROR] Input file does not exist: {}",
            input_path.display()
        );
        return;
    }

    let output_path = Path::new(output);
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).expect("Failed to create output directory");
    }

    println!("[INFO] Running Vampire...");
    run_vampire(input_path.to_str().unwrap(), output_path.to_str().unwrap());

    println!("[INFO] Vampire proof saved to {}", output_path.display());
}

/// Helper: actually runs the Vampire binary
pub fn run_vampire(input_file: &str, output_file: &str) {
    let vampire_bin = Path::new("../bin/vampire");

    let output = Command::new(vampire_bin)
        .arg(input_file)
        .output()
        .expect("Failed to run Vampire");

    // convert Vampire stdout to string
    let vampire_output =
        String::from_utf8(output.stdout).expect("Vampire output was not valid UTF-8");

    // turn the proof around + reformat
    let transformed_output = eq_proof_procedure(&vampire_output);

    // Write transformed proof
    fs::write(output_file, transformed_output)
        .expect("Failed to write transformed Vampire output");

    println!("Vampire proof written to {}", output_file);
}
