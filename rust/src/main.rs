use krympa::execution::{parse_execution_mode, set_execution_mode, set_term_size_aware};
use krympa::utils::extract_suffix;
use krympa::{core, direct, minimize, run_vamp};
use std::env;

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (mode, tsa, args) = parse_execution_mode(&raw_args);
    set_execution_mode(mode);
    set_term_size_aware(tsa);

    if args.is_empty() {
        krympa::klog_error!(
            "Usage: krympa [--sequential|--parallel] [--term-size] [collect|shorten|group|minimize|direct|run_vampire] <input_file>"
        );
        krympa::klog_error!("Usage for benchmarking: benchmarking_binary <input_folder> <timeout_secs> [krympa_binary]");
        return;
    }
    match args[0].as_str() {
        "collect" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa collect <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);
                core::collect(input_file, &output_file, suffix);
            }
        }
        "shorten" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa shorten <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::shorten_proofs(&summary_file)
            }
        }
        "group" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa group <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::structural_groups(&summary_file)
            }
        }
        "minimize" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa minimize <input_file>");
            } else {
                let input_file = &args[1];

                // extract suffix from input file
                let suffix = extract_suffix(input_file);

                // construct summary and output files with suffix
                let summary_file = format!("../output/summary_{}.json", suffix);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                // call minimize with input file and suffixed summary
                match minimize::try_minimize(input_file, &output_file, &summary_file) {
                    Ok(msg) => krympa::klog_info!("{}", msg),
                    Err(err) => krympa::klog_error!("Error: {}", err),
                }
            }
        }
        "direct" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa direct <input_file>");
            } else {
                let input_file = &args[1];
                let suffix = extract_suffix(input_file);
                let vampire_file = format!("../output/vampire_proof_{}.out", suffix);
                let summary_file = format!("../output/summary_{}.json", suffix);
                match direct::try_direct(input_file, &vampire_file, &summary_file, &suffix) {
                    Ok(msg) => krympa::klog_info!("{}", msg),
                    Err(err) => krympa::klog_error!("Error: {}", err),
                }
            }
        }
        "run_vampire" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: krympa run_vampire <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                run_vamp::run_vampire_only(input_file, &output_file);
            }
        }
        _ => krympa::klog_error!(
            "Unknown command '{}'. Use 'run_vampire', 'collect', 'shorten', 'group', 'minimize' or 'direct'",
            args[0]
        ),
    }
}
