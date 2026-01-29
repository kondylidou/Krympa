use std::fs;
use std::path::Path;
use std::process::Command;

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

    fs::write(output_file, &output.stdout).expect("Failed to write Vampire output");
    println!("Vampire proof written to {}", output_file);
}
