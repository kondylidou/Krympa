use crate::execution::{execution_mode, twee_executable, vampire_executable, ExecutionMode};
use crate::proof_turnaround::eq_proof_procedure;
use rayon::prelude::*;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;
use std::time::Duration;
use wait_timeout::ChildExt;

const PROVER_HINT: &str = "Put the provers in bin/, or give their executables with \
     --vampire/--twee or VAMPIRE/TWEE";

fn run_external_prover(exe_path: &str, args: &[&str]) -> Option<String> {
    let mut child = match std::process::Command::new(exe_path)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            crate::klog_error!(
                "[ERROR] Failed to start '{}': {}. {}",
                exe_path,
                e,
                PROVER_HINT
            );
            return None;
        }
    };

    let timeout = Duration::from_secs(7);
    match child.wait_timeout(timeout).unwrap() {
        Some(status) => {
            let output = child.wait_with_output().unwrap();
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
        None => {
            crate::klog_debug!(
                "[TIMEOUT] Prover '{}' exceeded {} seconds",
                exe_path,
                timeout.as_secs()
            );
            let _ = child.kill();
            None
        }
    }
}

/// The executable of a prover: the path given with `--vampire` / `--twee`,
/// else the environment variable, else the copy in `bin/`, else the plain
/// name, which the system then looks up on `PATH`.
fn prover_path(chosen: Option<String>, variable: &str, name: &str) -> String {
    if let Some(path) = chosen.or_else(|| env::var(variable).ok().filter(|v| !v.is_empty())) {
        // a bare name is looked up on the PATH; anything else is a file
        return if path.contains('/') {
            crate::execution::absolute(&path)
        } else {
            path
        };
    }
    let file = if cfg!(target_os = "macos") {
        format!("{}_mac", name)
    } else {
        name.to_string()
    };
    let bundled = env::current_dir().unwrap().join("bin").join(file);
    if bundled.exists() {
        bundled.to_string_lossy().to_string()
    } else {
        name.to_string()
    }
}

fn vampire_path() -> String {
    prover_path(vampire_executable(), "VAMPIRE", "vampire")
}

fn twee_path() -> String {
    prover_path(twee_executable(), "TWEE", "twee")
}

/// Extra command-line options for a prover, read from an environment variable
/// (`VAMPIRE_OPTIONS`, `TWEE_OPTIONS`) and split on whitespace.
/// Unset or empty means the prover runs exactly as before.
pub fn extra_options(variable: &str) -> Vec<String> {
    env::var(variable)
        .map(|value| value.split_whitespace().map(str::to_string).collect())
        .unwrap_or_default()
}

/// Vampire's raw output for a problem; gives up after the time limit of
/// `run_external_prover`.
pub fn run_vampire_limited(file: &str) -> Option<String> {
    let extra = extra_options("VAMPIRE_OPTIONS");
    let mut args = vec!["--input_syntax", "tptp"];
    args.extend(extra.iter().map(String::as_str));
    args.push(file);
    run_external_prover(&vampire_path(), &args)
}

pub fn run_twee(file: &str) -> Option<String> {
    let extra = extra_options("TWEE_OPTIONS");
    let mut args = vec!["--quiet"];
    args.extend(extra.iter().map(String::as_str));
    args.push(file);
    run_external_prover(&twee_path(), &args)
}

/// Count Vampire proof steps, ignoring input/negated conjecture lines
/// Count Vampire proof steps based on core inference tags
pub fn proof_length_vampire(proof: &str) -> usize {
    let mut count = 0;

    // core inference indicators — must match superpose.rs parse_vampire_proof
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
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
        "vampire" => proof_length_vampire(proof),
        "twee" => proof_length_twee(proof),
        _ => proof.lines().count(),
    }
}

/// Number of `op(` nodes in a term — a measure of structural complexity.
/// A bare variable scores 1 (minimum meaningful unit).
fn term_size(term: &str) -> usize {
    term.matches("op(").count() * 2 + 1
}

/// Average term size across all intermediate terms in a twee proof.
/// Counts every line inside a `Proof:` block that is not a `= { by … }` step line.
pub fn avg_term_size_twee(proof: &str) -> f64 {
    let mut in_proof = false;
    let mut sizes: Vec<usize> = Vec::new();

    for line in proof.lines() {
        let t = line.trim();
        if t.starts_with("Proof:") {
            in_proof = true;
            continue;
        }
        // New section starts, exits the proof block
        if t.starts_with("Lemma ") || t.starts_with("Goal ") || t.starts_with("RESULT") {
            in_proof = false;
            continue;
        }
        if !in_proof || t.is_empty() {
            continue;
        }
        // Skip step lines: "= { by … }"
        if t.starts_with("= {") {
            continue;
        }
        sizes.push(term_size(t));
    }

    if sizes.is_empty() {
        return 0.0;
    }
    sizes.iter().sum::<usize>() as f64 / sizes.len() as f64
}

/// Average term size across all inference-step formulas in a vampire proof.
/// Only considers superposition / demodulation / resolution steps.
/// For each such step the formula is split on `=` / `!=` and both sides are measured.
pub fn avg_term_size_vampire(proof: &str) -> f64 {
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
    ];
    let mut sizes: Vec<usize> = Vec::new();

    for line in proof.lines() {
        let l = line.trim_start();
        if l.is_empty() || l.starts_with('%') {
            continue;
        }
        // Strip leading line number "N. "
        let l_no_num = if let Some(dot_pos) = l.find('.') {
            l[dot_pos + 1..].trim_start()
        } else {
            l
        };
        if !l_no_num.contains('[') || !proof_keywords.iter().any(|kw| l_no_num.contains(kw)) {
            continue;
        }
        // Formula is everything before the last `[`
        let formula = match l_no_num.rfind('[') {
            Some(pos) => l_no_num[..pos].trim(),
            None => continue,
        };
        // Strip universal quantifier "! [X0,…] : body" if present
        let body = if formula.starts_with("! [") {
            match formula.find("] : ") {
                Some(pos) => formula[pos + 4..].trim(),
                None => formula,
            }
        } else {
            formula
        };
        // Split equation into its two sides; fall back to treating the whole body as one term
        if let Some(pos) = body.find(" != ") {
            sizes.push(term_size(body[..pos].trim()));
            sizes.push(term_size(body[pos + 4..].trim()));
        } else if let Some(pos) = body.find(" = ") {
            sizes.push(term_size(body[..pos].trim()));
            sizes.push(term_size(body[pos + 3..].trim()));
        } else {
            sizes.push(term_size(body));
        }
    }

    if sizes.is_empty() {
        return 0.0;
    }
    sizes.iter().sum::<usize>() as f64 / sizes.len() as f64
}

/// When `--term-size` is on, proof A is better than proof B if:
///   • A has strictly fewer steps, OR
///   • A has lower average term size and is at most TOLERANCE × longer.
/// Falls back to pure step-count comparison when term sizes are equal.
const TERM_SIZE_TOLERANCE: f64 = 1.5;

pub fn proof_quality_better(a_steps: usize, a_avg: f64, b_steps: usize, b_avg: f64) -> bool {
    if a_steps == b_steps {
        a_avg < b_avg
    } else if a_steps < b_steps {
        // A is shorter — A wins unless B has lower avg and is within tolerance
        !(b_avg < a_avg && b_steps as f64 <= a_steps as f64 * TERM_SIZE_TOLERANCE)
    } else {
        // B is shorter — A wins only if A has lower avg and is within tolerance
        a_avg < b_avg && a_steps as f64 <= b_steps as f64 * TERM_SIZE_TOLERANCE
    }
}

pub fn prove_lemmas(
    lemma_files: &[String],
    provers: &[&str],
    out_dir_path: &str,
) -> HashMap<u32, (String, String, String)> {
    reset_proof_dir(out_dir_path);
    prove_lemmas_into(lemma_files, provers, out_dir_path)
}

/// Empty the directory that `prove_lemmas_into` writes proofs to.
pub fn reset_proof_dir(out_dir_path: &str) {
    let out_dir = Path::new(out_dir_path);
    if out_dir.exists() {
        fs::remove_dir_all(out_dir).unwrap();
    }
    fs::create_dir_all(out_dir).unwrap();
}

/// Like `prove_lemmas`, but keeps the proofs that are already in `out_dir_path`,
/// so lemmas can be proved a few at a time.
pub fn prove_lemmas_into(
    lemma_files: &[String],
    provers: &[&str],
    out_dir_path: &str,
) -> HashMap<u32, (String, String, String)> {
    let out_dir = Path::new(out_dir_path);
    let vampire_dir = out_dir.join("vampire_tmp");
    let twee_dir = out_dir.join("twee_tmp");
    fs::create_dir_all(&vampire_dir).unwrap();
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

    let process_n = |&n: &u32| -> Option<(u32, (String, String, String))> {
        crate::klog_debug!("[DEBUG] Proving lemma {}", n);
        crate::klog_debug!(
            "[DEBUG] lemma {} running on thread {:?}",
            n,
            std::thread::current().id()
        );

        let files = &groups[&n];

        // Collect all successful proofs for this group. The runs of one lemma
        // (every variant with every prover) are independent, so they go in
        // parallel too; the order of the results stays variant by variant,
        // prover by prover, which the tie-break below relies on.
        let jobs: Vec<(&String, &str)> = files
            .iter()
            .flat_map(|file| provers.iter().map(move |prover| (file, *prover)))
            .collect();
        let run_job = |job: &(&String, &str)| -> Option<(String, String, usize, String)> {
            let (lemma_file, prover) = *job;
            let file_stem = Path::new(lemma_file).file_stem().unwrap().to_string_lossy();
            let vampire_file = vampire_dir.join(format!("{}_vampire.proof", file_stem));
            let twee_file = twee_dir.join(format!("{}_twee.proof", file_stem));

            let (prover, proof) = try_provers(lemma_file, &[prover], &vampire_file, &twee_file)
                .into_iter()
                .next()?;
            let szs_status = proof
                .lines()
                .find(|l| l.contains("RESULT:") || l.contains("SZS status"))
                .unwrap_or("")
                .to_lowercase(); // normalize to lowercase

            let len = if szs_status.contains("countersatisfiable")
                || szs_status.contains("counter-satisfiable")
                || szs_status.contains("counter_satisfiable")
                || (szs_status.contains("satisfiable") && !szs_status.contains("unsatisfiable"))
                || szs_status.contains("unknown")
            {
                1000 // sentinel for non-theorem / countersat / unknown
                     // TODO we can use them. But for now we just want shortest
                     // theorem proofs. Later we can see how we prove the
                     // conjecture from the satisfiable ones.
            } else {
                proof_length(&prover, &proof)
            };

            crate::klog_debug!("[DEBUG] {} proof length: {} lines", prover, len);
            Some((prover, proof, len, file_stem.to_string()))
        };
        // (prover, proof, len, filename)
        let all_proofs: Vec<(String, String, usize, String)> =
            if execution_mode() == ExecutionMode::Sequential {
                jobs.iter().filter_map(run_job).collect()
            } else {
                jobs.par_iter().filter_map(run_job).collect()
            };

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
                crate::klog_debug!("[DEBUG] Saved shortest proof to '{}'", final_path.display());
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
    };

    if execution_mode() == ExecutionMode::Sequential {
        sorted_nums.iter().filter_map(&process_n).collect()
    } else {
        sorted_nums.par_iter().filter_map(&process_n).collect()
    }
}

fn try_provers(
    lemma_file: &str,
    provers: &[&str],
    vampire_file: &Path,
    twee_file: &Path,
) -> Vec<(String, String)> {
    let mut successes = Vec::new();

    for &prover in provers {
        let output_file = match prover {
            "vampire" => vampire_file,
            "twee" => twee_file,
            _ => {
                crate::klog_error!("[ERROR] Unknown prover '{}'", prover);
                continue;
            }
        };

        crate::klog_debug!("[RUN] Trying prover '{}' on '{}'", prover, lemma_file);

        let proof_content = match prover {
            "vampire" => match run_vampire_limited(lemma_file) {
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

/// Run Vampire on a given input file and save its proof.
pub fn run_vampire_command(input: &str, output: &str) -> bool {
    let input_path = Path::new(input);
    if !input_path.exists() {
        crate::klog_error!(
            "[ERROR] Input file does not exist: {}",
            input_path.display()
        );
        return false;
    }

    let output_path = Path::new(output);
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).expect("Failed to create output directory");
    }

    crate::klog_info!("[INFO] Phase 0: Running Vampire and redirecting proof.");
    crate::klog_debug!("[DEBUG] Input: {}", input_path.display());
    crate::klog_debug!("[DEBUG] Output: {}", output_path.display());
    let proved = run_vampire_turned(input_path.to_str().unwrap(), output_path.to_str().unwrap());
    if !proved {
        crate::klog_error!(
            "[ERROR] Vampire did not find a proof for {}",
            input_path.display()
        );
    }
    proved
}

/// Helper: actually runs the Vampire binary.
///
/// The (transformed) output is always written to `output_file`, so the file
/// existing says nothing about success. Returns true only if Vampire reported
/// a proof; a timeout, a give-up or a rejected input returns false.
pub fn run_vampire_turned(input_file: &str, output_file: &str) -> bool {
    let vampire = vampire_path();
    let output = std::process::Command::new(&vampire)
        .args(extra_options("VAMPIRE_OPTIONS"))
        .arg(input_file)
        .output()
        .unwrap_or_else(|e| panic!("Failed to start '{}': {}. {}", vampire, e, PROVER_HINT));

    // convert Vampire stdout to string
    let vampire_output =
        String::from_utf8(output.stdout).expect("Vampire output was not valid UTF-8");

    let proved = vampire_output.contains("Refutation found")
        || vampire_output.contains("Termination reason: Refutation")
        || vampire_output.contains("SZS status Theorem")
        || vampire_output.contains("SZS status Unsatisfiable");

    // turn the proof around + reformat
    let transformed_output = eq_proof_procedure(&vampire_output);

    // Write transformed proof
    fs::write(output_file, transformed_output).expect("Failed to write transformed Vampire output");

    crate::klog_debug!("[DEBUG] Vampire proof written to {}", output_file);
    proved
}
