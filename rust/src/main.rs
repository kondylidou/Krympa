mod alpha_match;
mod dag;
mod frankenstein;
mod minimize;
mod prover_wrapper;
mod run_vamp;
mod superpose;
mod utils;

use std::env;
use std::path::Path;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run -- [collect|shorten|group|minimize|run_vampire] <input_file>");
        eprintln!("Usage for benchmarking: cargo run -- benchmarking");
        return;
    }
    match args[1].as_str() {
        "collect" => {
            if args.len() < 3 {
                eprintln!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);
                frankenstein::collect(&input_file, &output_file, suffix);
            }
        }
        "shorten" => {
            if args.len() < 3 {
                eprintln!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                frankenstein::shorten_proofs(&summary_file)
            }
        }
        "group" => {
            if args.len() < 3 {
                eprintln!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                frankenstein::structural_groups(&summary_file)
            }
        }
        "minimize" => {
            if args.len() < 3 {
                eprintln!("Usage: cargo run -- minimize <input_file>");
            } else {
                let input_file = &args[2];

                // extract suffix from input file
                let suffix = extract_suffix(input_file);

                // construct summary and output files with suffix
                let summary_file = format!("../output/summary_{}.json", suffix);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                // call minimize with input file and suffixed summary
                match minimize::try_minimize(&input_file, &output_file, &summary_file) {
                    Ok(msg) => println!("{}", msg),
                    Err(err) => eprintln!("Error: {}", err),
                }
            }
        }
        "run_vampire" => {
            if args.len() < 3 {
                eprintln!("Usage: cargo run -- run_vampire <input_file>");
            } else {
                let input_file = &args[2];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                run_vamp::run_vampire_only(input_file, &output_file);
            }
        }
        _ => eprintln!(
            "Unknown command '{}'. Use 'collect', 'shorten', 'group', or 'minimize'",
            args[1]
        ),
    }
}

pub fn extract_suffix(path: &str) -> String {
    let stem = Path::new(path)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string();

    if let Some(stripped) = stem.strip_prefix("input_problem_") {
        stripped.to_string()
    } else {
        stem // fallback: whole stem
    }
}
