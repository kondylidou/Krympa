use krympa::execution::{apply_flags, parse_flags, parse_request, Request};
use krympa::utils::extract_suffix;
use krympa::{collect, direct, lean, minimize, provers};
use std::{env, fs, process};

const USAGE: &str = "Usage: krympa [--direct] [--lean] [--term-size] [--refine] [--debug] \
     [--sequential] [--vampire <exe>] [--twee <exe>] <problem.p>\n\
     One phase only: krympa [flags] <run_vampire|collect|shorten|minimize|direct|group> <problem.p>";

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (flags, args) = parse_flags(&raw_args);
    apply_flags(flags);

    let done = match parse_request(&args) {
        Ok(Request::Whole {
            input,
            direct,
            lean,
        }) => run_whole(&input, direct) && (!lean || check_in_lean(&input)),
        Ok(Request::Phase { phase, input }) => run_phase(&phase, &input),
        Err(problem) => {
            krympa::klog_error!("{}\n{}", problem, USAGE);
            process::exit(2);
        }
    };
    if !done {
        process::exit(1);
    }
}

/// Every phase in turn, stopping at the first that fails.
fn run_whole(input_file: &str, direct: bool) -> bool {
    let suffix = extract_suffix(input_file);
    // A proof left by an earlier run must not pass for the result of this one.
    let _ = fs::remove_file(format!("../output/proof_{}.out", suffix));

    let phases: &[&str] = if direct {
        &["run_vampire", "direct"]
    } else {
        &["run_vampire", "collect", "shorten", "minimize"]
    };
    let failed = phases.iter().find(|phase| !run_phase(phase, input_file));
    match failed {
        None => true,
        Some(&"run_vampire") => false,
        Some(_) => {
            krympa::klog_error!(
                "No shortened proof. Vampire's proof is in ../output/vampire_proof_{}.out",
                suffix
            );
            false
        }
    }
}

/// Translate the shortened proof to Lean and check it there.
fn check_in_lean(input_file: &str) -> bool {
    let proof_file = format!("../output/proof_{}.out", extract_suffix(input_file));
    match lean::export_and_check(&proof_file) {
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
    let vampire_file = format!("../output/vampire_proof_{}.out", suffix);
    let summary_file = format!("../output/summary_{}.json", suffix);
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
        "minimize" => report(minimize::try_minimize(
            input_file,
            &vampire_file,
            &summary_file,
        )),
        "direct" => report(direct::try_direct(
            input_file,
            &vampire_file,
            &summary_file,
            &suffix,
        )),
        _ => unreachable!("parse_request only lets the known phases through"),
    }
}
