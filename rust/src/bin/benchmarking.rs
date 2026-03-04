use krympa::bench_run::run;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        krympa::klog_error!(
            "Usage: {} <input_folder> <timeout_secs> [krympa_binary] [vampire|twee|cvc5]",
            args[0]
        );
        std::process::exit(1);
    }

    let input_folder = &args[1];
    let timeout_secs: u64 = args[2].parse().expect("timeout_secs must be a number");

    let mut krympa_bin = "./krympa";
    let mut input_prover = "vampire";
    for arg in args.iter().skip(3) {
        if arg == "vampire" || arg == "twee" || arg == "cvc5" {
            input_prover = arg;
        } else {
            krympa_bin = arg;
        }
    }

    run(input_folder, krympa_bin, timeout_secs, input_prover);
}
