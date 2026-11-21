use crate::provers::proof_length;
use crate::utils::extract_suffix;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Debug)]
pub struct BenchmarkResult {
    pub file: String,
    pub vampire_steps: Option<usize>,
    pub minimized_steps: Option<usize>,
}

/// Run the benchmarking.
/// `input_folder`: folder with input files
/// `krympa_bin`: path to prebuilt krympa binary
/// `timeout_secs`: per-command timeout (seconds)
pub fn run(input_folder: &str, krympa_bin: &str, timeout_secs: u64) {
    let input_dir = Path::new(input_folder);
    if !input_dir.is_dir() {
        crate::klog_error!(
            "Input folder '{}' does not exist or is not a directory.",
            input_dir.display()
        );
        return;
    }

    let output_dir = Path::new("output");
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

    crate::klog_info!("Starting benchmarking in folder: {}", input_dir.display());
    crate::klog_info!("Output folder: {}", output_dir.display());
    crate::klog_info!("Per-command timeout: {} seconds", timeout_secs);

    'file_loop: for input_file in input_files {
        let input_str = input_file.to_string_lossy().to_string();
        crate::klog_info!("=== Processing file: {} ===", input_str);

        let mut vampire_steps: Option<usize> = None;
        let mut minimized_steps: Option<usize> = None;

        for cmd in &commands {
            crate::klog_debug!("Running '{} {}' ...", cmd, input_str);

            let mut child = match Command::new(krympa_bin)
                .args([cmd, input_str.as_str()])
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
                        vampire_steps: None,
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

        crate::klog_info!("--- Summary for {} ---", input_str);
        crate::klog_info!(
            "Vampire proof steps: {}",
            vampire_steps
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
            vampire_steps,
            minimized_steps,
        });
    }

    // --- Global summary ---
    crate::klog_info!("========== GLOBAL SUMMARY ==========");

    let mut total_vampire = 0usize;
    let mut total_minimized = 0usize;
    let mut count_vampire = 0usize;
    let mut count_minimized = 0usize;

    for r in &all_results {
        crate::klog_info!(
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

    crate::klog_info!("------------------------------------");

    if count_vampire > 0 {
        crate::klog_info!(
            "Average Vampire steps: {:.2}",
            total_vampire as f64 / count_vampire as f64
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

// ---------------------------------------------------------------------------
// Benchmark problems: the theorems of a `Proofs*.lean` file as TPTP problems
// ---------------------------------------------------------------------------

/// Write one TPTP problem per theorem `EquationA_implies_EquationB` of a
/// benchmark file. The equations are read from `Equations/` next to it, and
/// the problems go to `input<N>/` next to it, N being the number in the file
/// name. Returns (problems written, theorems skipped for a missing equation).
pub fn generate_problems(proofs_file: &Path) -> Result<(usize, usize), String> {
    let benchmarks = proofs_file.parent().unwrap_or(Path::new("."));
    let stem = proofs_file
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let number = crate::regex_cache::cached_regex(r"(\d+)")
        .captures(&stem)
        .map_or("0".to_string(), |found| found[1].to_string());
    let out_dir = benchmarks.join(format!("input{}", number));
    let proofs = fs::read_to_string(proofs_file)
        .map_err(|e| format!("Cannot read {}: {}", proofs_file.display(), e))?;
    let equations = equation_index(&benchmarks.join("Equations"))?;
    let theorems: Vec<(String, String)> =
        crate::regex_cache::cached_regex(r"theorem\s+(Equation\d+)_implies_(Equation\d+)")
            .captures_iter(&proofs)
            .map(|found| (found[1].to_string(), found[2].to_string()))
            .collect();
    fs::create_dir_all(&out_dir)
        .map_err(|e| format!("Cannot create {}: {}", out_dir.display(), e))?;
    println!(
        "Generating TPTP from {} → {} ({} problems)",
        proofs_file
            .file_name()
            .unwrap_or_default()
            .to_string_lossy(),
        out_dir.display(),
        theorems.len()
    );

    let (mut written, mut skipped) = (0, 0);
    for (axiom, conjecture) in &theorems {
        let number = |name: &str| name.trim_start_matches("Equation").parse::<u32>().ok();
        let (Some(axiom_eq), Some(conjecture_eq)) = (
            number(axiom).and_then(|n| equations.get(&n)),
            number(conjecture).and_then(|n| equations.get(&n)),
        ) else {
            skipped += 1;
            continue;
        };
        let (axiom_tptp, axiom_vars) = lean_to_tptp(axiom_eq);
        let (conjecture_tptp, conjecture_vars) = lean_to_tptp(conjecture_eq);
        let mut variables: Vec<String> = [axiom_vars, conjecture_vars].concat();
        variables.sort();
        variables.dedup();
        let variables = variables.join(", ");
        let problem = format!(
            "fof(a1, axiom,\n    ! [{v}] :\n        {a}\n).\n\nfof(conjecture0, conjecture,\n    ! [{v}] :\n        {c}\n).\n",
            v = variables,
            a = axiom_tptp,
            c = conjecture_tptp
        );
        let file = out_dir.join(format!("{}_implies_{}.p", axiom, conjecture));
        fs::write(&file, problem).map_err(|e| format!("Cannot write {}: {}", file.display(), e))?;
        written += 1;
    }
    println!("Done. Written: {}, Skipped: {}", written, skipped);
    Ok((written, skipped))
}

/// Equation number -> its statement, from the `Eqns*.lean` files. A statement
/// may continue on the following lines, up to the next `equation`.
fn equation_index(dir: &Path) -> Result<std::collections::HashMap<u32, String>, String> {
    let start = crate::regex_cache::cached_regex(r"^equation\s+(\d+)\s*:=");
    let mut index = std::collections::HashMap::new();
    let entries = fs::read_dir(dir).map_err(|e| format!("Cannot read {}: {}", dir.display(), e))?;
    for entry in entries.flatten() {
        let name = entry.file_name().to_string_lossy().to_string();
        if !(name.starts_with("Eqns") && name.ends_with(".lean")) {
            continue;
        }
        let text = fs::read_to_string(entry.path()).map_err(|e| e.to_string())?;
        let mut current: Option<(u32, Vec<String>)> = None;
        for line in text.lines() {
            let line = line.trim();
            if let Some(found) = start.captures(line) {
                if let Some((number, parts)) = current.take() {
                    index.insert(number, parts.join(" ").trim().to_string());
                }
                let statement = line.split_once(":=").map_or("", |(_, s)| s).trim();
                current = Some((found[1].parse().unwrap(), vec![statement.to_string()]));
            } else if let Some((number, parts)) = current.as_mut() {
                if line.starts_with("equation") {
                    index.insert(*number, parts.join(" ").trim().to_string());
                    current = None;
                } else {
                    parts.push(line.to_string());
                }
            }
        }
        if let Some((number, parts)) = current {
            index.insert(number, parts.join(" ").trim().to_string());
        }
    }
    Ok(index)
}

/// `x = y ◇ (x ◇ z)` -> (`(X0 = op(X1,op(X0,X2)))`, [X0, X1, X2]).
pub fn lean_to_tptp(equation: &str) -> (String, Vec<String>) {
    let equation = equation.trim();
    let (lhs, rhs) = match equation.split_once('=') {
        Some((lhs, rhs)) => (lhs.trim(), rhs.trim()),
        None => ("", equation),
    };
    let (lhs, rhs) = (infix_to_prefix(lhs), infix_to_prefix(rhs));
    let mut names: Vec<String> = Vec::new();
    let mut rename = |side: &str| {
        crate::regex_cache::cached_regex(r"\b[a-zA-Z_]\w*\b")
            .replace_all(side, |found: &regex::Captures| {
                let name = &found[0];
                if name == "op" {
                    return name.to_string();
                }
                let index = names.iter().position(|n| n == name).unwrap_or_else(|| {
                    names.push(name.to_string());
                    names.len() - 1
                });
                format!("X{}", index)
            })
            .into_owned()
    };
    let (lhs, rhs) = (rename(&lhs), rename(&rhs));
    let variables = (0..names.len()).map(|i| format!("X{}", i)).collect();
    (format!("({} = {})", lhs, rhs), variables)
}

/// `x ◇ (y ◇ z)` -> `op(x,op(y,z))`, splitting at the first `◇` outside
/// parentheses.
fn infix_to_prefix(expression: &str) -> String {
    let mut expression = expression.trim();
    // drop parentheses around the whole expression
    while expression.starts_with('(') && expression.ends_with(')') {
        let mut depth = 0i32;
        let mut wrapped = true;
        for (i, c) in expression.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            if depth == 0 && i + c.len_utf8() < expression.len() {
                wrapped = false;
                break;
            }
        }
        if !wrapped {
            break;
        }
        expression = expression[1..expression.len() - 1].trim();
    }
    if !expression.contains('◇') {
        return expression.to_string();
    }
    let mut depth = 0i32;
    for (i, c) in expression.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '◇' if depth == 0 => {
                let left = infix_to_prefix(&expression[..i]);
                let right = infix_to_prefix(&expression[i + c.len_utf8()..]);
                return format!("op({},{})", left, right);
            }
            _ => {}
        }
    }
    expression.to_string()
}

// ---------------------------------------------------------------------------
// Summary of the benchmark logs
// ---------------------------------------------------------------------------

/// Print, per log of `log_dir` and over all of them, the average number of
/// steps of Vampire's and Krympa's proofs: for all problems, and for those
/// whose Vampire proof has at least 15 steps. A problem without a Krympa
/// result counts with Vampire's proof; one without a Vampire result is left out.
pub fn summarize(log_dir: &Path) -> Result<(), String> {
    let line_re = crate::regex_cache::cached_regex(r"Vampire:\s+(\d+)\s+Minimized:\s+(N/A|\d+)");
    let mut logs: Vec<String> = fs::read_dir(log_dir)
        .map_err(|e| format!("Cannot read {}: {}", log_dir.display(), e))?
        .flatten()
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .filter(|name| name.ends_with(".log"))
        .collect();
    logs.sort();

    let mut overall = Averages::default();
    for name in logs {
        let text = fs::read_to_string(log_dir.join(&name)).map_err(|e| e.to_string())?;
        let mut file = Averages::default();
        for line in text.lines() {
            let Some(found) = line_re.captures(line) else {
                continue;
            };
            let vampire: usize = found[1].parse().unwrap();
            let minimized = found[2].parse().unwrap_or(vampire);
            file.add(vampire, minimized);
            overall.add(vampire, minimized);
        }
        println!("\n=== {} ===", name);
        file.print();
    }
    println!("\n=== OVERALL SUMMARY (ALL FILES) ===");
    overall.print();
    Ok(())
}

/// Step counts (Vampire, Krympa), for all problems and for the long ones.
#[derive(Default)]
struct Averages {
    all: Vec<(usize, usize)>,
    long: Vec<(usize, usize)>,
}

impl Averages {
    fn add(&mut self, vampire: usize, minimized: usize) {
        self.all.push((vampire, minimized));
        if vampire >= 15 {
            self.long.push((vampire, minimized));
        }
    }

    fn print(&self) {
        for (title, pairs) in [("ALL:", &self.all), ("VAMPIRE >= 15:", &self.long)] {
            let average = |pick: fn(&(usize, usize)) -> usize| {
                if pairs.is_empty() {
                    0.0
                } else {
                    pairs.iter().map(pick).sum::<usize>() as f64 / pairs.len() as f64
                }
            };
            println!("{}", title);
            println!("  Count: {}", pairs.len());
            println!("  Avg Vampire:   {:.2}", average(|p| p.0));
            println!("  Avg Minimized: {:.2}", average(|p| p.1));
        }
    }
}
