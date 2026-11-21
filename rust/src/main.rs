use krympa::execution::{
    parse_execution_mode, parse_prover_executables, set_execution_mode, set_prover_executables,
    set_term_size_aware,
};
use krympa::utils::extract_suffix;
use krympa::{collect, direct, minimize, provers};
use std::env;

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (vampire, twee, raw_args) = parse_prover_executables(&raw_args);
    set_prover_executables(vampire, twee);
    let (mode, tsa, args) = parse_execution_mode(&raw_args);
    set_execution_mode(mode);
    set_term_size_aware(tsa);

    if args.is_empty() {
        krympa::klog_error!(
            "Usage: krympa [--sequential|--parallel] [--term-size] [--vampire <exe>] [--twee <exe>] [collect|shorten|group|minimize|direct|run_vampire] <input_file>"
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
                collect::collect(input_file, &output_file, suffix);
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
                collect::shorten_proofs(&summary_file)
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
                collect::structural_groups(&summary_file)
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

                provers::run_vampire_command(input_file, &output_file);
            }
        }
        _ => krympa::klog_error!(
            "Unknown command '{}'. Use 'run_vampire', 'collect', 'shorten', 'group', 'minimize' or 'direct'",
            args[0]
        ),
    }
}
