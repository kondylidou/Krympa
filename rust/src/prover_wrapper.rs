use crate::proof_turnaround::eq_proof_procedure;
use crate::tptp_to_smt2::convert_tptp_file_to_smt2;
use rayon::prelude::*;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;
use std::time::Duration;
use wait_timeout::ChildExt;

fn run_external_prover(exe_path: &str, args: &[&str]) -> Option<String> {
    let mut child = match std::process::Command::new(exe_path)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            crate::klog_error!("[ERROR] Failed to start process '{}': {}", exe_path, e);
            return None;
        }
    };

    let timeout = Duration::from_secs(5);
    match child.wait_timeout(timeout) {
        Ok(Some(status)) => {
            let output = match child.wait_with_output() {
                Ok(o) => o,
                Err(e) => {
                    crate::klog_error!(
                        "[ERROR] Failed to read prover output from '{}': {}",
                        exe_path,
                        e
                    );
                    return None;
                }
            };
            if status.success() {
                Some(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                crate::klog_debug!(
                    "[ERROR] Prover '{}' exited with error: {:?}",
                    exe_path,
                    status
                );
                let stderr = String::from_utf8_lossy(&output.stderr);
                crate::klog_debug!("[DEBUG] Stderr: {}", stderr);
                None
            }
        }
        Ok(None) => {
            crate::klog_debug!(
                "[TIMEOUT] Prover '{}' exceeded {} seconds",
                exe_path,
                timeout.as_secs()
            );
            let _ = child.kill();
            None
        }
        Err(e) => {
            crate::klog_error!(
                "[ERROR] Failed while waiting for prover '{}': {}",
                exe_path,
                e
            );
            let _ = child.kill();
            None
        }
    }
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

fn cvc5_path() -> String {
    let local = env::current_dir().unwrap().join("../bin/cvc5");
    if local.exists() {
        local.to_str().unwrap().to_string()
    } else {
        "cvc5".to_string()
    }
}

pub fn run_vampire(file: &str) -> Option<String> {
    run_external_prover(&vampire_path(), &["--input_syntax", "tptp", file])
}

pub fn run_twee(file: &str) -> Option<String> {
    run_external_prover(&twee_path(), &["--quiet", file])
}

pub fn run_cvc5(file: &str) -> Option<String> {
    let smt2_path = format!("{}.cvc5_tmp.smt2", file);
    if let Err(err) = convert_tptp_file_to_smt2(file, &smt2_path) {
        crate::klog_debug!("[DEBUG] cvc5 conversion failed for '{}': {}", file, err);
        return None;
    }
    let result = run_external_prover(
        &cvc5_path(),
        &[
            "--mbqi-enum",
            "--produce-proofs",
            "--dump-proofs",
            "--proof-format-mode=alethe",
            &smt2_path,
        ],
    );
    let _ = fs::remove_file(&smt2_path);
    result
}

pub fn run_vampire_only(input: &str, output: &str) {
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
        if let Err(e) = fs::create_dir_all(parent) {
            crate::klog_error!(
                "[ERROR] Failed to create output directory '{}': {}",
                parent.display(),
                e
            );
            return;
        }
    }

    crate::klog_info!("[INFO] Phase 0: Running Vampire and redirecting proof.");
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());

    run_vampire_to_file(input_path.to_str().unwrap(), output_path.to_str().unwrap());
}

pub fn run_vampire_to_file(input_file: &str, output_file: &str) {
    match run_vampire(input_file) {
        Some(vampire_output) => {
            let transformed_output = eq_proof_procedure(&vampire_output);
            if let Err(e) = fs::write(output_file, transformed_output) {
                crate::klog_error!(
                    "[ERROR] Failed to write transformed Vampire output '{}': {}",
                    output_file,
                    e
                );
            } else {
                crate::klog_debug!("[DEBUG] Vampire proof written to {}", output_file);
            }
        }
        None => {
            crate::klog_error!("[ERROR] Failed to run Vampire");
        }
    }
}

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
        if let Err(e) = fs::create_dir_all(parent) {
            crate::klog_error!(
                "[ERROR] Failed to create output directory '{}': {}",
                parent.display(),
                e
            );
            return;
        }
    }

    crate::klog_info!("[INFO] Phase 0: Running Twee.");
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());

    run_twee_to_file(input_path.to_str().unwrap(), output_path.to_str().unwrap());
}

pub fn run_twee_to_file(input_file: &str, output_file: &str) {
    match run_twee(input_file) {
        Some(twee_output) => {
            if let Err(e) = fs::write(output_file, twee_output) {
                crate::klog_error!(
                    "[ERROR] Failed to write Twee output '{}': {}",
                    output_file,
                    e
                );
            } else {
                crate::klog_debug!("[DEBUG] Twee proof written to {}", output_file);
            }
        }
        None => {
            crate::klog_error!("[ERROR] Failed to run Twee");
        }
    }
}

pub fn run_cvc5_only(input: &str, output: &str) {
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
        if let Err(e) = fs::create_dir_all(parent) {
            crate::klog_error!(
                "[ERROR] Failed to create output directory '{}': {}",
                parent.display(),
                e
            );
            return;
        }
    }

    crate::klog_info!("[INFO] Phase 0: Running cvc5.");
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());

    run_cvc5_to_file(input_path.to_str().unwrap(), output_path.to_str().unwrap());
}

pub fn run_cvc5_to_file(input_file: &str, output_file: &str) {
    match run_cvc5(input_file) {
        Some(cvc5_output) => {
            if let Err(e) = fs::write(output_file, cvc5_output) {
                crate::klog_error!(
                    "[ERROR] Failed to write cvc5 output '{}': {}",
                    output_file,
                    e
                );
            } else {
                crate::klog_debug!("[DEBUG] cvc5 output written to {}", output_file);
            }
        }
        None => {
            crate::klog_error!("[ERROR] Failed to run cvc5");
        }
    }
}

/// Count Vampire proof steps, ignoring input/negated conjecture lines
/// Count Vampire proof steps based on core inference tags
pub fn proof_length_vampire(proof: &str) -> usize {
    let mut count = 0;

    // core inference indicators
    let proof_keywords = ["demodulation", "superposition", "resolution"];

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

pub fn proof_length_cvc5(proof: &str) -> usize {
    let mut steps = 0usize;
    for line in proof.lines() {
        let l = line.trim_start();
        if l.starts_with("(step ") {
            steps += 1;
        }
    }
    if steps > 0 {
        steps
    } else {
        proof
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with(';') && !l.starts_with('%'))
            .count()
    }
}

pub fn proof_length(prover: &str, proof: &str) -> usize {
    match prover {
        "vampire" => proof_length_vampire(proof),
        "twee" => proof_length_twee(proof),
        "cvc5" => proof_length_cvc5(proof),
        _ => proof.lines().count(),
    }
}

fn classify_result_status(proof: &str) -> &'static str {
    for raw in proof.lines() {
        let l = raw.trim().to_ascii_lowercase();
        if l.is_empty() {
            continue;
        }
        if l.contains("szs status unsatisfiable") || l.contains("result: theorem") || l == "unsat" {
            return "theorem";
        }
        if l.contains("counter-satisfiable")
            || l.contains("counter_satisfiable")
            || l.contains("countersatisfiable")
            || (l.contains("satisfiable") && !l.contains("unsatisfiable"))
            || l == "sat"
        {
            return "sat";
        }
        if l.contains("unknown") || l == "unknown" {
            return "unknown";
        }
    }
    "unknown"
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
    let twee_dir = out_dir.join("twee_tmp");
    let cvc5_dir = out_dir.join("cvc5_tmp");
    fs::create_dir_all(&vampire_dir).unwrap();
    fs::create_dir_all(&twee_dir).unwrap();
    fs::create_dir_all(&cvc5_dir).unwrap();

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
                let twee_file = twee_dir.join(format!("{}_twee.proof", file_stem));
                let cvc5_file = cvc5_dir.join(format!("{}_cvc5.proof", file_stem));

                for (prover, proof) in
                    try_provers(lemma_file, provers, &vampire_file, &twee_file, &cvc5_file)
                {
                    let len = if matches!(classify_result_status(&proof), "sat" | "unknown") {
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
                        // Tie-breaker: prefer "twee" over "cvc5" over "vampire" over others.
                        let order = |p: &String| {
                            if p == "twee" {
                                0
                            } else if p == "cvc5" {
                                1
                            } else if p == "vampire" {
                                2
                            } else {
                                3
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
    twee_file: &Path,
    cvc5_file: &Path,
) -> Vec<(String, String)> {
    let mut successes = Vec::new();

    for &prover in provers {
        let output_file = match prover {
            "vampire" => vampire_file,
            "twee" => twee_file,
            "cvc5" => cvc5_file,
            _ => {
                crate::klog_error!("[ERROR] Unknown prover '{}'", prover);
                continue;
            }
        };

        crate::klog_debug!("[RUN] Trying prover '{}' on '{}'", prover, lemma_file);

        let proof_content = match prover {
            "vampire" => match run_vampire(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] Vampire failed for '{}'", lemma_file);
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
            "cvc5" => match run_cvc5(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] cvc5 failed for '{}'", lemma_file);
                    continue;
                }
            },
            _ => continue,
        };

        if let Err(e) = fs::write(output_file, &proof_content) {
            crate::klog_error!(
                "[ERROR] Failed to save proof for prover '{}': {}",
                prover,
                e
            );
        }

        successes.push((prover.to_string(), proof_content));
    }

    successes
}
