use krympa::execution::{
    absolute, apply_flags, enter_krympa_home, parse_flags, parse_request, Request, WholeRun,
};
use krympa::utils::extract_suffix;
use krympa::{collect, compress, direct, lean, minimize, problem, provers};
use std::path::Path;
use std::{env, fs, process};

const USAGE: &str = "Usage: krympa [--direct] [--no-compress] [--lean] [--vampire-proof <file>] \
     [--term-size] [--refine] [--debug] [--sequential] [--vampire <exe>] [--twee <exe>] <problem.p>\n\
     One phase only: krympa [flags] <run_vampire|collect|shorten|minimize|direct|group> <problem.p>\n\
     On a proof file: krympa <lean|compress> <proof.out>";

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (flags, args) = parse_flags(&raw_args);
    apply_flags(flags);

    let request = parse_request(&args).unwrap_or_else(|problem| {
        krympa::klog_error!("{}\n{}", problem, USAGE);
        process::exit(2);
    });
    if let Err(problem) = enter_krympa_home() {
        krympa::klog_error!("[ERROR] {}", problem);
        process::exit(1);
    }
    let needs_provers = match &request {
        Request::Whole { .. } => true,
        Request::Phase { phase, .. } => phase != "group",
        Request::Tool { .. } => false,
    };
    if needs_provers {
        if let Err(problem) = provers::check_provers() {
            krympa::klog_error!("[ERROR] {}", problem);
            process::exit(1);
        }
    }
    let done = match request {
        Request::Whole { input, options } => match problem::fof_problem(&absolute(&input)) {
            Ok(input) => run_whole(&input, &options),
            Err(error) => reject(&input, &error),
        },
        Request::Phase { phase, input } => match problem::fof_problem(&absolute(&input)) {
            Ok(input) => run_phase(&phase, &input),
            Err(error) => reject(&input, &error),
        },
        Request::Tool { tool, proof } => match tool.as_str() {
            "lean" => check_in_lean(&absolute(&proof)),
            _ => {
                let proof = absolute(&proof);
                let path = Path::new(&proof);
                let stem = path.file_stem().unwrap_or_default().to_string_lossy();
                let target = path.with_file_name(format!("{}_compressed.out", stem));
                remove_avoidable_steps(&proof, &target.to_string_lossy(), true)
            }
        },
    };
    if !done {
        process::exit(1);
    }
}

/// Report a problem file that Krympa cannot work on.
fn reject(input_file: &str, error: &str) -> bool {
    krympa::klog_error!("[ERROR] {}: {}", input_file, error);
    false
}

/// Every phase in turn, stopping at the first that fails, then what the
/// options ask for on the proof.
fn run_whole(input_file: &str, options: &WholeRun) -> bool {
    let suffix = extract_suffix(input_file);
    let proof_file = format!("output/proof_{}.out", suffix);
    // A proof left by an earlier run must not pass for the result of this one.
    let _ = fs::remove_file(&proof_file);

    let started = match &options.vampire_proof {
        Some(saved) => provers::use_saved_vampire_proof(
            &absolute(saved),
            &format!("output/vampire_proof_{}.out", suffix),
        ),
        None => run_phase("run_vampire", input_file),
    };
    if !started {
        return false;
    }
    let search: &[&str] = if options.direct {
        &["direct"]
    } else {
        &["collect", "shorten", "minimize"]
    };
    if search.iter().any(|phase| !run_phase(phase, input_file)) {
        krympa::klog_error!(
            "No shortened proof. Vampire's proof is in output/vampire_proof_{}.out",
            suffix
        );
        return false;
    }
    // Removing steps is an improvement, not a requirement: if it is not
    // possible (e.g. a problem not over `op`), the proof stays as it is.
    if options.compress {
        remove_avoidable_steps(&proof_file, &proof_file, false);
    }
    !options.lean || check_in_lean(&proof_file)
}

/// Write `proof_file` without its avoidable steps to `target`. When it is not
/// possible, say why only if it was asked for (`report`).
fn remove_avoidable_steps(proof_file: &str, target: &str, report: bool) -> bool {
    let result = fs::read_to_string(proof_file)
        .map_err(|e| format!("Cannot read {}: {}", proof_file, e))
        .and_then(|text| compress::compress(&text))
        .and_then(|shorter| {
            fs::write(target, &shorter.text)
                .map_err(|e| format!("Cannot write {}: {}", target, e))?;
            Ok(shorter)
        });
    match result {
        Ok(shorter) if shorter.steps_after == shorter.steps_before => {
            krympa::klog_info!("[RESULT] No avoidable steps");
            if target != proof_file {
                krympa::klog_info!("[RESULT] Proof output: {}", target);
            }
            true
        }
        Ok(shorter) => {
            krympa::klog_info!(
                "[RESULT] Avoidable steps removed: {} -> {} steps",
                shorter.steps_before,
                shorter.steps_after
            );
            if target != proof_file {
                krympa::klog_info!("[RESULT] Proof output: {}", target);
            }
            true
        }
        Err(problem) if report => {
            krympa::klog_warn!("[WARN] Avoidable steps not removed: {}", problem);
            false
        }
        Err(problem) => {
            krympa::klog_debug!("[DEBUG] Avoidable steps not removed: {}", problem);
            false
        }
    }
}

/// Translate a proof to Lean and check it there.
fn check_in_lean(proof_file: &str) -> bool {
    match lean::export_and_check(proof_file) {
        Ok(lean_file) => {
            krympa::klog_info!("[LEAN] Accepted: {}", lean_file);
            true
        }
        Err(problem) => {
            krympa::klog_error!("[LEAN] {}", problem);
            false
        }
    }
}

/// One phase; the files it reads and writes are named after the problem file.
fn run_phase(phase: &str, input_file: &str) -> bool {
    let suffix = extract_suffix(input_file);
    let vampire_file = format!("output/vampire_proof_{}.out", suffix);
    let summary_file = format!("output/summary_{}.json", suffix);
    let report = |result: Result<String, String>| match result {
        Ok(message) => {
            krympa::klog_debug!("{}", message);
            true
        }
        Err(error) => {
            krympa::klog_error!("Error: {}", error);
            false
        }
    };
    match phase {
        "run_vampire" => provers::run_vampire_command(input_file, &vampire_file),
        "collect" => {
            collect::collect(input_file, &vampire_file, suffix);
            true
        }
        "shorten" => {
            collect::shorten_proofs(&summary_file);
            true
        }
        "group" => {
            collect::structural_groups(&summary_file);
            true
        }
        "minimize" => report(minimize::keep_shorter_than_vampire(
            input_file,
            &vampire_file,
            minimize::try_minimize(input_file, &vampire_file, &summary_file),
        )),
        "direct" => report(minimize::keep_shorter_than_vampire(
            input_file,
            &vampire_file,
            direct::try_direct(input_file, &vampire_file, &summary_file, &suffix),
        )),
        _ => unreachable!("parse_request only lets the known phases through"),
    }
}
