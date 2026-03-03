use crate::proof_turnaround::eq_proof_procedure;
use rayon::prelude::*;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;
use wait_timeout::ChildExt;

pub const PROVER_TIMEOUT_SECS: u64 = 10;
pub const IPROVER_PROCESS_TIMEOUT_SECS: u64 = PROVER_TIMEOUT_SECS + 10;
pub const IPROVER_DEFAULT_SCHEDULE: &str = "tao_2026_03_01_schedule";

fn normalize_atp(value: &str) -> String {
    match value.trim().to_lowercase().as_str() {
        "vampire" => "vampire".to_string(),
        "iprover" => "iprover".to_string(),
        _ => {
            crate::klog_warn!(
                "[WARN] Unsupported KRYMPA_ATP='{}'. Falling back to 'vampire'.",
                value
            );
            "vampire".to_string()
        }
    }
}

pub fn atp() -> String {
    let raw = env::var("KRYMPA_ATP").unwrap_or_else(|_| "vampire".to_string());
    normalize_atp(&raw)
}

pub fn start_proof_output_file(suffix: &str, start_prover: &str) -> String {
    format!("../output/{}_proof_{}.out", start_prover, suffix)
}

/// Run the selected start prover (vampire/iprover) on a given input file and save its proof.
pub fn run_start_prover_only(input: &str, output: &str, start_prover: &str) {
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

    crate::klog_info!(
        "[INFO] Phase 0: Running {} and redirecting proof.",
        start_prover
    );
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());
    run_start_prover(
        input_path.to_str().unwrap(),
        output_path.to_str().unwrap(),
        start_prover,
    );
}

pub fn run_start_prover(input_file: &str, output_file: &str, start_prover: &str) {
    if !Path::new(input_file).exists() {
        crate::klog_error!(
            "[ERROR] Start prover input file does not exist: {}",
            input_file
        );
        return;
    }

    let output_text = match start_prover {
        "vampire" => run_vampire(input_file),
        "iprover" => run_iprover(input_file),
        _ => {
            crate::klog_warn!(
                "[WARN] Unknown start prover '{}', falling back to vampire.",
                start_prover
            );
            run_vampire(input_file)
        }
    };

    let Some(raw_output) = output_text else {
        crate::klog_debug!(
            "[DEBUG] {} returned no proof output for '{}'.",
            start_prover,
            input_file
        );
        return;
    };

    let transformed_output = eq_proof_procedure(&raw_output);
    fs::write(output_file, transformed_output).unwrap_or_else(|e| {
        panic!(
            "Failed to write transformed ATP output to {}: {}",
            output_file, e
        )
    });
    crate::klog_debug!("[DEBUG] {} proof written to {}", start_prover, output_file);
}

fn fmt_cmd(exe_path: &str, args: &[&str]) -> String {
    let mut parts = Vec::with_capacity(args.len() + 1);
    parts.push(exe_path.to_string());
    parts.extend(args.iter().map(|a| a.to_string()));
    parts.join(" ")
}

fn fmt_cmd_path(exe_path: &Path, args: &[&str]) -> String {
    let mut parts = Vec::with_capacity(args.len() + 1);
    parts.push(exe_path.display().to_string());
    parts.extend(args.iter().map(|a| a.to_string()));
    parts.join(" ")
}

fn preview_output(text: &str) -> String {
    const MAX_CHARS: usize = 1200;
    let trimmed = text.trim();
    if trimmed.chars().count() <= MAX_CHARS {
        trimmed.to_string()
    } else {
        let preview: String = trimmed.chars().take(MAX_CHARS).collect();
        format!("{} ... [truncated]", preview)
    }
}

fn run_external_prover(exe_path: &str, args: &[&str]) -> Option<String> {
    let cmd = fmt_cmd(exe_path, args);
    let mut child = match std::process::Command::new(exe_path)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            crate::klog_error!("[ERROR] Failed to start prover command '{}': {}", cmd, e);
            return None;
        }
    };

    let timeout = Duration::from_secs(PROVER_TIMEOUT_SECS);
    match child.wait_timeout(timeout).unwrap() {
        Some(status) => {
            let output = child.wait_with_output().unwrap();
            if status.success() {
                Some(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                let stderr = String::from_utf8_lossy(&output.stderr);
                let stdout = String::from_utf8_lossy(&output.stdout);
                crate::klog_debug!(
                    "[DEBUG] Prover command failed (status: {:?}): {}",
                    status.code(),
                    cmd
                );
                if !stderr.trim().is_empty() {
                    crate::klog_debug!("[DEBUG] Prover stderr: {}", preview_output(&stderr));
                } else if !stdout.trim().is_empty() {
                    crate::klog_debug!("[DEBUG] Prover stdout: {}", preview_output(&stdout));
                } else {
                    crate::klog_debug!("[DEBUG] Prover produced no stdout/stderr output.");
                }
                None
            }
        }
        None => {
            crate::klog_debug!(
                "[DEBUG] Prover command timed out after {} seconds: {}",
                timeout.as_secs(),
                cmd
            );
            let _ = child.kill();
            None
        }
    }
}

fn run_external_prover_in_dir(
    exe_path: &Path,
    args: &[&str],
    work_dir: &Path,
    timeout_secs: u64,
) -> Option<String> {
    let cmd = fmt_cmd_path(exe_path, args);
    let work_dir_display = work_dir.display().to_string();
    let mut child = match std::process::Command::new(exe_path)
        .current_dir(work_dir)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            crate::klog_error!(
                "[ERROR] Failed to start prover command '{}' in '{}': {}",
                cmd,
                work_dir_display,
                e
            );
            return None;
        }
    };

    let timeout = Duration::from_secs(timeout_secs);
    match child.wait_timeout(timeout).unwrap() {
        Some(status) => {
            let output = child.wait_with_output().unwrap();
            if status.success() {
                Some(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                let stderr = String::from_utf8_lossy(&output.stderr);
                let stdout = String::from_utf8_lossy(&output.stdout);
                crate::klog_debug!(
                    "[DEBUG] Prover command failed (status: {:?}) in '{}': {}",
                    status.code(),
                    work_dir_display,
                    cmd
                );
                if !stderr.trim().is_empty() {
                    crate::klog_debug!("[DEBUG] Prover stderr: {}", preview_output(&stderr));
                } else if !stdout.trim().is_empty() {
                    crate::klog_debug!("[DEBUG] Prover stdout: {}", preview_output(&stdout));
                } else {
                    crate::klog_debug!("[DEBUG] Prover produced no stdout/stderr output.");
                }
                None
            }
        }
        None => {
            crate::klog_debug!(
                "[DEBUG] Prover command timed out after {} seconds in '{}': {}",
                timeout.as_secs(),
                work_dir_display,
                cmd
            );
            let _ = child.kill();
            None
        }
    }
}

fn extract_status_marker(text: &str) -> String {
    text.lines()
        .filter(|l| l.contains("RESULT:") || l.contains("SZS status"))
        .last()
        .unwrap_or("")
        .to_lowercase()
}

fn vampire_path() -> String {
    env::current_dir()
        .unwrap()
        .join("../bin/vampire")
        .to_str()
        .unwrap()
        .to_string()
}

fn twee_path() -> String {
    env::current_dir()
        .unwrap()
        .join("../bin/twee")
        .to_str()
        .unwrap()
        .to_string()
}

pub fn run_vampire(file: &str) -> Option<String> {
    run_external_prover(&vampire_path(), &["--input_syntax", "tptp", file])
}

pub fn run_twee(file: &str) -> Option<String> {
    run_external_prover(&twee_path(), &["--quiet", file])
}

fn iprover_path() -> String {
    env::current_dir()
        .unwrap()
        .join("../bin/iprover-build/iproveropt-multi-core.sh")
        .to_str()
        .unwrap()
        .to_string()
}

pub fn run_iprover(file: &str) -> Option<String> {
    let timeout_s = PROVER_TIMEOUT_SECS.to_string();
    let schedule = env::var("KRYMPA_IPROVER_SCHEDULE")
        .unwrap_or_else(|_| IPROVER_DEFAULT_SCHEDULE.to_string());
    let script_path = PathBuf::from(iprover_path());
    let work_dir = script_path.parent().unwrap_or_else(|| Path::new("."));

    if !script_path.exists() {
        crate::klog_error!(
            "[ERROR] iProver launcher not found at '{}'.",
            script_path.display()
        );
        return None;
    }

    let input_abs = fs::canonicalize(file).unwrap_or_else(|_| {
        env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(file)
    });
    let input_abs_s = input_abs.to_string_lossy().to_string();
    let args = [
        "-s",
        schedule.as_str(),
        "-t",
        timeout_s.as_str(),
        input_abs_s.as_str(),
    ];
    run_external_prover_in_dir(&script_path, &args, work_dir, IPROVER_PROCESS_TIMEOUT_SECS)
}

/// Count Vampire proof steps, ignoring input/negated conjecture lines
/// Count Vampire proof steps based on core inference tags
pub fn proof_length_vampire(proof: &str) -> usize {
    let mut count = 0;

    // core inference indicators
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "subsumption",
        "simplification",
        "factoring",
        "rewriting",
        "distinctness",
        "light normalisation",
        "light_normalisation",
    ];

    for line in proof.lines() {
        let l = line.trim_start();

        // skip empty lines and comments
        if l.is_empty() || l.starts_with('%') {
            continue;
        }

        // remove leading line number (e.g., "23. ...")
        let l_no_num = if let Some(dot_pos) = l.find('.') {
            let (_, rest) = l.split_at(dot_pos + 1);
            rest.trim_start()
        } else {
            l
        };

        // only count lines whose inference tag contains one of the keywords
        if l_no_num.contains('[') && proof_keywords.iter().any(|kw| l_no_num.contains(kw)) {
            count += 1;
        }
    }

    count
}

pub fn proof_length_twee(proof: &str) -> usize {
    let mut in_proof = false;
    proof
        .lines()
        .map(str::trim_start)
        .filter(|line| {
            if line.starts_with("Proof:") {
                in_proof = true;
                return false;
            }
            in_proof && line.contains("= { by")
        })
        .count()
}

pub fn proof_length(prover: &str, proof: &str) -> usize {
    match prover {
        "vampire" | "iprover" => proof_length_vampire(proof),
        "twee" => proof_length_twee(proof),
        _ => proof.lines().count(),
    }
}

pub fn prove_lemmas(
    lemma_files: &[String],
    provers: &[&str],
    out_dir_path: &str,
) -> HashMap<u32, (String, String, String)> {
    let out_dir = Path::new(out_dir_path);
    if out_dir.exists() {
        fs::remove_dir_all(out_dir).unwrap();
    }
    fs::create_dir_all(out_dir).unwrap();

    let vampire_dir = out_dir.join("vampire_tmp");
    let iprover_dir = out_dir.join("iprover_tmp");
    let twee_dir = out_dir.join("twee_tmp");
    fs::create_dir_all(&vampire_dir).unwrap();
    fs::create_dir_all(&iprover_dir).unwrap();
    fs::create_dir_all(&twee_dir).unwrap();

    // group by lemma index
    let mut groups: HashMap<u32, Vec<String>> = HashMap::new();
    for f in lemma_files {
        let fname = Path::new(f).file_stem().unwrap().to_string_lossy();
        let num: u32 = fname
            .chars()
            .rev()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>()
            .chars()
            .rev()
            .collect::<String>()
            .parse()
            .unwrap_or(0);
        groups.entry(num).or_default().push(f.clone());
    }

    let mut sorted_nums: Vec<u32> = groups.keys().cloned().collect();
    sorted_nums.sort();

    // PARALLEL: each lemma index `n` runs on its own rayon worker thread
    sorted_nums
        .par_iter()
        .filter_map(|&n| {
            crate::klog_debug!("[DEBUG] Proving lemma {}", n);
            crate::klog_debug!(
                "[DEBUG] lemma {} running on thread {:?}",
                n,
                std::thread::current().id()
            );

            let files = &groups[&n];

            // collect all successful proofs for this group
            let mut all_proofs: Vec<(String, String, usize, String)> = Vec::new(); // (prover, proof, len, filename)

            for lemma_file in files {
                let file_stem = Path::new(lemma_file).file_stem().unwrap().to_string_lossy();
                let vampire_file = vampire_dir.join(format!("{}_vampire.proof", file_stem));
                let iprover_file = iprover_dir.join(format!("{}_iprover.proof", file_stem));
                let twee_file = twee_dir.join(format!("{}_twee.proof", file_stem));

                for (prover, proof, status_marker) in try_provers(
                    lemma_file,
                    provers,
                    &vampire_file,
                    &iprover_file,
                    &twee_file,
                ) {
                    let len = if status_marker.contains("countersatisfiable")
                        || status_marker.contains("counter-satisfiable")
                        || status_marker.contains("counter_satisfiable")
                        || (status_marker.contains("satisfiable")
                            && !status_marker.contains("unsatisfiable"))
                        || status_marker.contains("unknown")
                    {
                        1000 // sentinel for non-theorem / countersat / unknown
                             // TODO we can use them. But for now we just want shortest
                             // theorem proofs. Later we can see how we prove the
                             // conjecture from the satisfiable ones.
                    } else {
                        proof_length(&prover, &proof)
                    };

                    //let len = proof_length(&prover, &proof);
                    crate::klog_debug!("[DEBUG] {} proof length: {} lines", prover, len);
                    all_proofs.push((prover, proof, len, file_stem.to_string()));
                }
            }

            // pick the shortest proof across all modes and provers
            if let Some((best_prover, best_proof, best_len, best_file)) =
                all_proofs.into_iter().min_by(|a, b| {
                    // compare lengths first
                    if a.2 != b.2 {
                        a.2.cmp(&b.2)
                    } else {
                        // Tie-breaker: prefer "twee" over "vampire" over others
                        let order = |p: &String| {
                            if p == "twee" {
                                0
                            } else if p == "vampire" {
                                1
                            } else {
                                2
                            }
                        };
                        order(&a.0).cmp(&order(&b.0))
                    }
                })
            {
                let final_path = out_dir.join(format!("{}_{}.proof", best_file, best_prover));
                if let Err(e) = fs::write(&final_path, &best_proof) {
                    crate::klog_error!("[ERROR] Failed to save shortest proof: {}", e);
                } else {
                    crate::klog_debug!(
                        "[DEBUG] Saved shortest proof to '{}'",
                        final_path.display()
                    );
                }

                crate::klog_debug!(
                    "[DEBUG] Shortest proof for lemma {} found in '{}' by '{}' with {} lines",
                    n,
                    best_file,
                    best_prover,
                    best_len
                );

                Some((n, (best_file, best_prover, best_proof)))
            } else {
                crate::klog_warn!("[WARN] No successful proof for group {}", n);
                None
            }
        })
        .collect()
}

fn try_provers(
    lemma_file: &str,
    provers: &[&str],
    vampire_file: &Path,
    iprover_file: &Path,
    twee_file: &Path,
) -> Vec<(String, String, String)> {
    let mut successes = Vec::new();

    for &prover in provers {
        let output_file = match prover {
            "vampire" => vampire_file,
            "iprover" => iprover_file,
            "twee" => twee_file,
            _ => {
                crate::klog_error!("[ERROR] Unknown prover '{}'", prover);
                continue;
            }
        };

        crate::klog_debug!("[RUN] Trying prover '{}' on '{}'", prover, lemma_file);

        let raw_output = match prover {
            "vampire" => match run_vampire(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] Vampire failed for '{}'", lemma_file);
                    continue;
                }
            },
            "iprover" => match run_iprover(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] iProver failed for '{}'", lemma_file);
                    continue;
                }
            },
            "twee" => match run_twee(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] Twee failed for '{}'", lemma_file);
                    continue;
                }
            },
            _ => continue,
        };

        let status_marker = extract_status_marker(&raw_output);

        let proof_content = if prover == "vampire" || prover == "iprover" {
            eq_proof_procedure(&raw_output)
        } else {
            raw_output
        };

        if let Err(e) = fs::write(output_file, &proof_content) {
            crate::klog_error!(
                "[ERROR] Failed to save proof for prover '{}': {}",
                prover,
                e
            );
        }

        successes.push((prover.to_string(), proof_content, status_marker));
    }

    successes
}
