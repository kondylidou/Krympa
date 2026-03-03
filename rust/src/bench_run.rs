use crate::prover_wrapper::proof_length;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Debug)]
pub struct BenchmarkResult {
    pub file: String,
    pub initial_steps: Option<usize>,
    pub minimized_steps: Option<usize>,
}

/// Run the benchmarking.
/// `input_folder`: folder with input files
/// `krympa_bin`: path to prebuilt krympa binary
/// `timeout_secs`: per-command timeout (seconds)
pub fn run(input_folder: &str, krympa_bin: &str, timeout_secs: u64, input_prover: &str) {
    let input_dir = Path::new(input_folder);
    if !input_dir.is_dir() {
        crate::klog_error!(
            "Input folder '{}' does not exist or is not a directory.",
            input_dir.display()
        );
        return;
    }

    let run_cmd = match input_prover {
        "vampire" => "run_vampire",
        "twee" => "run_twee",
        _ => {
            crate::klog_error!(
                "Unknown input prover '{}'. Expected 'vampire' or 'twee'.",
                input_prover
            );
            return;
        }
    };

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

    let commands = [run_cmd, "collect", "minimize"];
    let mut all_results: Vec<BenchmarkResult> = Vec::new();

    crate::klog_info!("Starting benchmarking in folder: {}", input_dir.display());
    crate::klog_info!("Output folder: {}", output_dir.display());
    crate::klog_info!("Per-command timeout: {} seconds", timeout_secs);

    'file_loop: for input_file in input_files {
        let input_str = input_file.to_string_lossy().to_string();
        crate::klog_info!("=== Processing file: {} ===", input_str);

        let mut initial_steps: Option<usize> = None;
        let mut minimized_steps: Option<usize> = None;

        for cmd in &commands {
            crate::klog_debug!("Running '{} {}' ...", cmd, input_str);

            let mut command = Command::new(krympa_bin);
            if *cmd == "collect" || *cmd == "minimize" {
                command.args([*cmd, input_str.as_str(), input_prover]);
            } else {
                command.args([*cmd, input_str.as_str()]);
            }
            let mut child = match command
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
            {
                Ok(c) => c,
                Err(e) => {
                    crate::klog_error!("Failed to start '{} {}': {}", cmd, input_str, e);
                    continue;
                }
            };

            let timeout = Duration::from_secs(timeout_secs);

            let status = match child.wait_timeout(timeout) {
                Ok(Some(status)) => status,
                Ok(None) => {
                    crate::klog_warn!(
                        "[TIMEOUT] '{}' exceeded {:?} on {} — recording as failed",
                        cmd,
                        timeout,
                        input_str
                    );
                    let _ = child.kill();
                    all_results.push(BenchmarkResult {
                        file: input_str.clone(),
                        initial_steps: None,
                        minimized_steps: None,
                    });
                    continue 'file_loop;
                }
                Err(e) => {
                    crate::klog_error!("Failed waiting for '{}': {}", cmd, e);
                    continue;
                }
            };

            let output = child
                .wait_with_output()
                .expect("Failed to collect process output");

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if !status.success() {
                crate::klog_warn!("Command '{}' failed on {}\n{}", cmd, input_str, stderr);
            }

            // --- Initial proof length ---
            if *cmd == run_cmd {
                let suffix = extract_suffix(&input_str);
                let initial_file =
                    output_dir.join(format!("{}_proof_{}.out", input_prover, suffix));

                if initial_file.exists() {
                    let mut content = String::new();
                    if let Ok(mut file) = fs::File::open(&initial_file) {
                        if file.read_to_string(&mut content).is_ok() {
                            initial_steps = Some(proof_length(input_prover, &content));
                        }
                    }
                }
            }

            // --- Minimized proof length ---
            if *cmd == "minimize" {
                for line in stdout.lines() {
                    if let Some(rest) = line.strip_prefix("[RESULT] Total steps:") {
                        if let Ok(n) = rest.trim().parse::<usize>() {
                            minimized_steps = Some(match initial_steps {
                                Some(v) if n > v => v,
                                _ => n,
                            });
                            break; // we found the number, no need to keep scanning
                        }
                    }
                }
            }
        }

        crate::klog_info!("--- Summary for {} ---", input_str);
        crate::klog_info!(
            "Initial ({}) proof steps: {}",
            input_prover,
            initial_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "N/A".to_string())
        );
        crate::klog_info!(
            "Minimized proof steps: {}",
            minimized_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "N/A".to_string())
        );
        crate::klog_info!("===========================");

        all_results.push(BenchmarkResult {
            file: input_str,
            initial_steps,
            minimized_steps,
        });
    }

    // --- Global summary ---
    crate::klog_info!("========== GLOBAL SUMMARY ==========");

    let mut total_initial = 0usize;
    let mut total_minimized = 0usize;
    let mut count_initial = 0usize;
    let mut count_minimized = 0usize;

    for r in &all_results {
        crate::klog_info!(
            "{:<45}  Initial: {:>6}  Minimized: {:>6}",
            r.file,
            r.initial_steps
                .map(|i| {
                    total_initial += i;
                    count_initial += 1;
                    i.to_string()
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

    crate::klog_info!("------------------------------------");

    if count_initial > 0 {
        crate::klog_info!(
            "Average Initial steps: {:.2}",
            total_initial as f64 / count_initial as f64
        );
    }

    if count_minimized > 0 {
        crate::klog_info!(
            "Average Minimized steps: {:.2}",
            total_minimized as f64 / count_minimized as f64
        );
    }

    crate::klog_info!("====================================");
    crate::klog_info!("All benchmarking runs completed.");
}

fn extract_suffix(path: &str) -> String {
    Path::new(path)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string()
}
