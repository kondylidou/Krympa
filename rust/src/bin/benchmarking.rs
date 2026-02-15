use krympa::bench_run::run;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "Usage: {} <input_folder> <timeout_secs> [krympa_binary]",
            args[0]
        );
        std::process::exit(1);
    }

    let input_folder = &args[1];
    let timeout_secs: u64 = args[2].parse().expect("timeout_secs must be a number");

    let krympa_bin = if args.len() >= 4 {
        &args[3]
    } else {
        "./krympa"
    };

    run(input_folder, krympa_bin, timeout_secs);
}
