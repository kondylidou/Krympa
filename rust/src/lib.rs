use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

pub mod prover_wrapper;
use crate::prover_wrapper::proof_length;

#[derive(Debug)]
pub struct BenchmarkResult {
    pub file: String,
    pub vampire_steps: Option<usize>,
    pub minimized_steps: Option<usize>,
}

/// Run the benchmarking.
/// `input_folder`: folder with input files
/// `frankenstein_bin`: path to prebuilt frankenstein binary
pub fn run(input_folder: &str, frankenstein_bin: &str) {
    let input_dir = Path::new(input_folder);
    if !input_dir.is_dir() {
        eprintln!(
            "Input folder '{}' does not exist or is not a directory.",
            input_dir.display()
        );
        return;
    }
    let output_dir = Path::new("../output");
    fs::create_dir_all(output_dir).expect("Failed to create output folder");

    let input_files: Vec<_> = fs::read_dir(input_dir)
        .expect("Failed to read input directory")
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            path.is_file().then_some(path)
        })
        .collect();

    let commands = ["run_vampire", "collect", "shorten", "minimize"];
    let mut all_results: Vec<BenchmarkResult> = Vec::new();

    println!("Starting benchmarking in folder: {}\n", input_dir.display());
    println!("Output folder: {}\n", output_dir.display());

    'file_loop: for input_file in input_files {
        let input_str = input_file.to_string_lossy().to_string();
        println!("=== Processing file: {} ===", input_str);

        let mut vampire_steps: Option<usize> = None;
        let mut minimized_steps: Option<usize> = None;

        for cmd in &commands {
            println!("Running '{} {}' ...", cmd, input_str);

            let mut child = match Command::new(frankenstein_bin)
                .args([cmd, input_str.as_str()])
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
            {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Failed to start '{} {}': {}", cmd, input_str, e);
                    continue;
                }
            };

            let timeout = Duration::from_secs(3600); // 1 hour

            let status = match child.wait_timeout(timeout) {
                Ok(Some(status)) => status,
                Ok(None) => {
                    eprintln!(
                        "[TIMEOUT] '{}' exceeded {:?} on {} — recording as failed",
                        cmd, timeout, input_str
                    );
                    let _ = child.kill();
                    all_results.push(BenchmarkResult {
                        file: input_str.clone(),
                        vampire_steps: None,
                        minimized_steps: None,
                    });
                    continue 'file_loop;
                }
                Err(e) => {
                    eprintln!("Failed waiting for '{}': {}", cmd, e);
                    continue;
                }
            };

            let output = child
                .wait_with_output()
                .expect("Failed to collect process output");

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if !status.success() {
                eprintln!("Command '{}' failed on {}\n{}", cmd, input_str, stderr);
            }

            // --- Vampire proof length ---
            if *cmd == "run_vampire" {
                let suffix = extract_suffix(&input_str);
                let vampire_file = output_dir.join(format!("vampire_proof_{}.out", suffix));

                if vampire_file.exists() {
                    let mut content = String::new();
                    if let Ok(mut file) = fs::File::open(&vampire_file) {
                        if file.read_to_string(&mut content).is_ok() {
                            vampire_steps = Some(proof_length("vampire", &content));
                        }
                    }
                }
            }

            // --- Minimized proof length ---
            if *cmd == "minimize" {
                for line in stdout.lines() {
                    if let Some(rest) = line.strip_prefix("[RESULT] Total steps:") {
                        if let Ok(n) = rest.trim().parse::<usize>() {
                            minimized_steps = Some(match vampire_steps {
                                Some(v) if n > v => v,
                                _ => n,
                            });
                            break; // we found the number, no need to keep scanning
                        }
                    }
                }
            }
        }

        println!("--- Summary for {} ---", input_str);
        println!(
            "Vampire proof steps: {}",
            vampire_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "N/A".to_string())
        );
        println!(
            "Minimized proof steps: {}",
            minimized_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "N/A".to_string())
        );
        println!("===========================\n");

        all_results.push(BenchmarkResult {
            file: input_str,
            vampire_steps,
            minimized_steps,
        });
    }

    // --- Global summary ---
    println!("\n========== GLOBAL SUMMARY ==========");

    let mut total_vampire = 0usize;
    let mut total_minimized = 0usize;
    let mut count_vampire = 0usize;
    let mut count_minimized = 0usize;

    for r in &all_results {
        println!(
            "{:<45}  Vampire: {:>6}  Minimized: {:>6}",
            r.file,
            r.vampire_steps
                .map(|v| {
                    total_vampire += v;
                    count_vampire += 1;
                    v.to_string()
                })
                .unwrap_or_else(|| "N/A".to_string()),
            r.minimized_steps
                .map(|m| {
                    total_minimized += m;
                    count_minimized += 1;
                    m.to_string()
                })
                .unwrap_or_else(|| "N/A".to_string()),
        );
    }

    println!("------------------------------------");

    if count_vampire > 0 {
        println!(
            "Average Vampire steps: {:.2}",
            total_vampire as f64 / count_vampire as f64
        );
    }

    if count_minimized > 0 {
        println!(
            "Average Minimized steps: {:.2}",
            total_minimized as f64 / count_minimized as f64
        );
    }

    println!("====================================");
    println!("All benchmarking runs completed.");
}

fn extract_suffix(path: &str) -> String {
    Path::new(path)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string()
}
