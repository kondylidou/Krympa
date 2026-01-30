use core::run;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <input_folder> [krympa_binary]", args[0]);
        std::process::exit(1);
    }

    let input_folder = &args[1];
    let krympa_bin = if args.len() >= 3 {
        &args[2]
    } else {
        "./krympa"
    };

    run(input_folder, krympa_bin);
}
