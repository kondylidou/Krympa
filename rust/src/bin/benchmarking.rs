use frankenstein::run;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <input_folder> [frankenstein_binary]", args[0]);
        std::process::exit(1);
    }

    let input_folder = &args[1];
    let frankenstein_bin = if args.len() >= 3 {
        &args[2]
    } else {
        "./frankenstein"
    };

    run(input_folder, frankenstein_bin);
}
