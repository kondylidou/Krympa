use krympa::bench_run::{generate_problems, run, summarize};
use krympa::execution::{absolute, enter_krympa_home};
use std::env;
use std::path::Path;

const USAGE: &str = "Usage: benchmarking_binary <input_folder> <timeout_secs> [krympa_binary]\n\
     \x20      benchmarking_binary generate <Proofs*.lean>...\n\
     \x20      benchmarking_binary summarize <log_folder>";

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    // like krympa itself, work in the Krympa folder; paths are the user's
    let result = enter_krympa_home().and_then(|_| match args.first().map(String::as_str) {
        Some("generate") if args.len() > 1 => args[1..]
            .iter()
            .try_for_each(|file| generate_problems(Path::new(&absolute(file))).map(|_| ())),
        Some("summarize") if args.len() == 2 => summarize(Path::new(&absolute(&args[1]))),
        _ if args.len() >= 2 => match args[1].parse::<u64>() {
            Ok(timeout_secs) => {
                let krympa_bin = match args.get(2) {
                    Some(given) if given.contains('/') => absolute(given),
                    Some(given) => given.clone(),
                    None => "./krympa".to_string(),
                };
                run(&absolute(&args[0]), &krympa_bin, timeout_secs);
                Ok(())
            }
            Err(_) => Err("timeout_secs must be a number".to_string()),
        },
        _ => Err("Missing arguments".to_string()),
    });
    if let Err(problem) = result {
        krympa::klog_error!("{}\n{}", problem, USAGE);
        std::process::exit(1);
    }
}
