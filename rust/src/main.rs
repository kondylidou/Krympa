use krympa::utils::extract_suffix;
use krympa::{core, minimize, prover_wrapper};
use std::env;
use std::path::Path;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        krympa::klog_error!(
            "Usage: cargo run -- [collect|shorten|group|minimize|run_vampire|run_twee|run_cvc5] <input_file> [vampire|twee|cvc5]"
        );
        krympa::klog_error!("Usage for benchmarking: cargo run -- benchmarking");
        return;
    }
    match args[1].as_str() {
        "collect" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file> [vampire|twee|cvc5]");
            } else {
                let input_file = &args[2];
                let input_prover = args.get(3).map(|s| s.as_str()).unwrap_or("vampire");
                if input_prover != "vampire" && input_prover != "twee" && input_prover != "cvc5" {
                    krympa::klog_error!(
                        "Unknown input prover '{}'. Expected 'vampire', 'twee', or 'cvc5'.",
                        input_prover
                    );
                    return;
                }
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/{}_proof_{}.out", input_prover, suffix);
                if !Path::new(&output_file).exists() {
                    krympa::klog_error!(
                        "[ERROR] Input proof file does not exist: '{}'. Run 'run_{} <input_file>' first.",
                        output_file,
                        input_prover
                    );
                    return;
                }
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
                krympa::klog_error!("Usage: cargo run -- minimize <input_file> [vampire|twee|cvc5]");
            } else {
                let input_file = &args[2];
                let input_prover = args.get(3).map(|s| s.as_str()).unwrap_or("vampire");
                if input_prover != "vampire" && input_prover != "twee" && input_prover != "cvc5" {
                    krympa::klog_error!(
                        "Unknown input prover '{}'. Expected 'vampire', 'twee', or 'cvc5'.",
                        input_prover
                    );
                    return;
                }

                // extract suffix from input file
                let suffix = extract_suffix(input_file);

                // construct summary and output files with suffix
                let summary_file = format!("../output/summary_{}.json", suffix);
                let output_file = format!("../output/{}_proof_{}.out", input_prover, suffix);
                if !Path::new(&output_file).exists() {
                    krympa::klog_error!(
                        "[ERROR] Input proof file does not exist: '{}'. Run 'run_{} <input_file>' first.",
                        output_file,
                        input_prover
                    );
                    return;
                }

                // call minimize with input file and suffixed summary
                match minimize::try_minimize(
                    input_file,
                    &output_file,
                    input_prover,
                    &summary_file,
                ) {
                    Ok(msg) => krympa::klog_info!("{}", msg),
                    Err(err) => krympa::klog_error!("Error: {}", err),
                }
            }
        }
        "run_vampire" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- run_vampire <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                prover_wrapper::run_vampire_only(input_file, &output_file);
            }
        }
        "run_twee" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- run_twee <input_file>");
            } else {
                let input_file = &args[2];
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/twee_proof_{}.out", suffix);

                prover_wrapper::run_twee_only(input_file, &output_file);
            }
        }
        "run_cvc5" => {
            if args.len() < 3 {
                krympa::klog_error!("Usage: cargo run -- run_cvc5 <input_file>");
            } else {
                let input_file = &args[2];
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/cvc5_proof_{}.out", suffix);

                prover_wrapper::run_cvc5_only(input_file, &output_file);
            }
        }
        _ => krympa::klog_error!(
            "Unknown command '{}'. Use 'run_vampire', 'run_twee', 'run_cvc5', 'collect', 'shorten', 'group', or 'minimize'",
            args[1]
        ),
    }
}
