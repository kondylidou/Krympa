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
            eprintln!("[ERROR] Failed to start process '{}': {}", exe_path, e);
            return None;
        }
    };

    let timeout = Duration::from_secs(10);
    match child.wait_timeout(timeout).unwrap() {
        Some(status) => {
            let output = child.wait_with_output().unwrap();
            if status.success() {
                Some(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                eprintln!(
                    "[ERROR] Prover '{}' exited with error: {:?}",
                    exe_path, status
                );
                let stderr = String::from_utf8_lossy(&output.stderr);
                eprintln!("[ERROR] Stderr: {}", stderr);
                None
            }
        }
        None => {
            eprintln!(
                "[TIMEOUT] Prover '{}' exceeded {} seconds",
                exe_path,
                timeout.as_secs()
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

fn egg_path() -> String {
    env::current_dir()
        .unwrap()
        .join("target/debug/egg-sc-tptp")
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
fn run_egg(input: &str, output: &str) -> Option<String> {
    run_external_prover(&egg_path(), &[input, output])
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

fn proof_length_egg(proof: &str) -> usize {
    proof
        .lines()
        .filter(|l| {
            let line = l.trim_start();
            line.starts_with("fof(") && line.contains(", plain") && line.contains("inference(")
        })
        .count()
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
        "egg" => proof_length_egg(proof),
        "twee" => proof_length_twee(proof),
        _ => proof.lines().count(),
    }
}

pub fn prove_lemmas(
    lemma_files: &[String],
    provers: &[&str],
    out_dir_path: &str,
) -> HashMap<u32, (String, String, String)> {
    let mut results = HashMap::new();
    let out_dir = Path::new(out_dir_path);
    if out_dir.exists() {
        fs::remove_dir_all(out_dir).unwrap();
    }
    fs::create_dir_all(out_dir).unwrap();

    let egg_dir = out_dir.join("egg_tmp");
    let vampire_dir = out_dir.join("vampire_tmp");
    let twee_dir = out_dir.join("twee_tmp");
    fs::create_dir_all(&egg_dir).unwrap();
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

    for n in sorted_nums {
        println!("\n[INFO] Proving lemma {}", n);
        let files = &groups[&n];

        // collect all successful proofs for this group
        let mut all_proofs: Vec<(String, String, usize, String)> = Vec::new(); // (prover, proof, len, filename)

        for lemma_file in files {
            let file_stem = Path::new(lemma_file).file_stem().unwrap().to_string_lossy();
            let egg_file = egg_dir.join(format!("{}_egg.proof", file_stem));
            let vampire_file = vampire_dir.join(format!("{}_vampire.proof", file_stem));
            let twee_file = twee_dir.join(format!("{}_twee.proof", file_stem));

            for (prover, proof) in
                try_provers(lemma_file, provers, &egg_file, &vampire_file, &twee_file)
            {
                let szs_status = proof
                    .lines()
                    .find(|l| l.contains("RESULT:") || l.contains("SZS status"))
                    .unwrap_or("")
                    .to_lowercase(); // normalize to lowercase

                let len = if szs_status.contains("countersatisfiable")
                    || szs_status.contains("counter-satisfiable")
                    || szs_status.contains("counter_satisfiable")
                    || szs_status.contains("satisfiable") && !szs_status.contains("unsatisfiable")
                    || szs_status.contains("unknown")
                {
                    1000 // sentinel for non-theorem / countersat / unknown
                         // TODO we can use them. But for now we just want shortest
                         // theorem proofs. Later we can see how we prove the
                         // conjecture from the satisfiable ones.
                } else {
                    proof_length(&prover, &proof)
                };

                //let len = proof_length(&prover, &proof);
                println!("[INFO] {} proof length: {} lines", prover, len);
                all_proofs.push((prover, proof, len, file_stem.to_string()));
            }
        }

        // pick the shortest proof across all modes and provers
        if let Some((best_prover, best_proof, best_len, best_file)) =
            all_proofs.into_iter().min_by(|a, b| {
                // Compare lengths first
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
                eprintln!("[ERROR] Failed to save shortest proof: {}", e);
            } else {
                println!("[INFO] Saved shortest proof to '{}'", final_path.display());
            }

            println!(
                "[INFO] Shortest proof for lemma {} found in '{}' by '{}' with {} lines",
                n, best_file, best_prover, best_len
            );

            results.insert(n, (best_file, best_prover, best_proof));
        } else {
            println!("[WARN] No successful proof for group {}", n);
        }
    }

    results
}

fn try_provers(
    lemma_file: &str,
    provers: &[&str],
    egg_file: &Path,
    vampire_file: &Path,
    twee_file: &Path,
) -> Vec<(String, String)> {
    let mut successes = Vec::new();

    for &prover in provers {
        let output_file = match prover {
            "egg" => egg_file,
            "vampire" => vampire_file,
            "twee" => twee_file,
            _ => {
                eprintln!("[ERROR] Unknown prover '{}'", prover);
                continue;
            }
        };

        println!("[RUN] Trying prover '{}' on '{}'", prover, lemma_file);

        let proof_content = match prover {
            "egg" => {
                if run_egg(lemma_file, &output_file.to_string_lossy()).is_none() {
                    println!("[INFO] Egg failed for '{}'", lemma_file);
                    continue;
                }
                match fs::read_to_string(output_file) {
                    Ok(c) => c,
                    Err(_) => {
                        println!("[INFO] Egg failed to produce proof for '{}'", lemma_file);
                        continue;
                    }
                }
            }
            "vampire" => match run_vampire(lemma_file) {
                Some(c) => c,
                None => {
                    println!("[INFO] Vampire failed for '{}'", lemma_file);
                    continue;
                }
            },
            "twee" => match run_twee(lemma_file) {
                Some(c) => c,
                None => {
                    println!("[INFO] Twee failed for '{}'", lemma_file);
                    continue;
                }
            },
            _ => continue,
        };

        if let Err(e) = fs::write(output_file, &proof_content) {
            eprintln!(
                "[ERROR] Failed to save proof for prover '{}': {}",
                prover, e
            );
        }

        if prover != "egg" {
            let szs = proof_content
                .lines()
                .find(|l| l.contains("SZS status") || l.contains("RESULT:"))
                .unwrap_or("")
                .to_lowercase();

            if szs.contains("theorem") || szs.contains("unsatisfiable") {
                println!("[INFO] '{}' proved theorem for '{}'", prover, lemma_file);
            } else {
                println!(
                    "[INFO] '{}' returned non-theorem status for '{}': {}",
                    prover, lemma_file, szs
                );
            }
        }

        successes.push((prover.to_string(), proof_content));
    }

    successes
}
