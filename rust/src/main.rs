use krympa::utils::extract_suffix;
use krympa::{core, minimize, prover_wrapper};
use std::env;

fn selected_start_prover(arg: Option<&String>) -> String {
    match arg.map(|s| s.as_str()) {
        Some("vampire") => "vampire".to_string(),
        Some("iprover") => "iprover".to_string(),
        Some(other) => {
            krympa::klog_warn!(
                "[WARN] Unsupported prover '{}', falling back to KRYMPA_ATP/default.",
                other
            );
            prover_wrapper::atp()
        }
        None => prover_wrapper::atp(),
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        krympa::klog_error!(
            "Usage: cargo run -- [collect|shorten|group|minimize|run_atp] <input_file> [vampire|iprover]"
        );
        krympa::klog_error!("Usage for benchmarking: cargo run -- benchmarking");
        return;
    }
    match args[1].as_str() {
        "collect" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file> [vampire|iprover]");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let start_prover = selected_start_prover(args.get(3));
                let output_file = prover_wrapper::start_proof_output_file(&suffix, &start_prover);
                core::collect(input_file, &output_file, suffix);
            }
        }
        "shorten" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::shorten_proofs(&summary_file)
            }
        }
        "group" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::structural_groups(&summary_file)
            }
        }
        "minimize" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- minimize <input_file> [vampire|iprover]");
            } else {
                let input_file = &args[2];

                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let start_prover = selected_start_prover(args.get(3));

                // construct summary and output files with suffix
                let summary_file = format!("../output/summary_{}.json", suffix);
                let output_file = prover_wrapper::start_proof_output_file(&suffix, &start_prover);

                // call minimize with input file and suffixed summary
                match minimize::try_minimize(input_file, &output_file, &summary_file) {
                    Ok(msg) => krympa::klog_info!("{}", msg),
                    Err(err) => krympa::klog_error!("Error: {}", err),
                }
            }
        }
        "run_atp" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- run_atp <input_file> [vampire|iprover]");
            } else {
                let input_file = &args[2];
                let suffix = extract_suffix(input_file);
                let start_prover = selected_start_prover(args.get(3));
                let output_file = prover_wrapper::start_proof_output_file(&suffix, &start_prover);
                prover_wrapper::run_start_prover_only(input_file, &output_file, &start_prover);
            }
        }
        _ => krympa::klog_error!(
            "Unknown command '{}'. Use 'collect', 'shorten', 'group', 'minimize', or 'run_atp'",
            args[1]
        ),
    }
}
