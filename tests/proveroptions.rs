use krympa::provers::extra_options;

#[test]
fn options_are_split_on_whitespace_and_default_to_none() {
    // a variable name no other test or user sets
    let var = "KRYMPA_TEST_ONLY_OPTIONS";
    std::env::remove_var(var);
    assert!(extra_options(var).is_empty());
    std::env::set_var(var, "  -sa discount   -awr 1:4 ");
    assert_eq!(extra_options(var), ["-sa", "discount", "-awr", "1:4"]);
    std::env::set_var(var, "");
    assert!(extra_options(var).is_empty());
    std::env::remove_var(var);
}

#[test]
fn flags_are_stripped_from_the_arguments() {
    use krympa::execution::{parse_flags, Flags};
    let args: Vec<String> = [
        "--vampire",
        "/opt/vampire",
        "--term-size",
        "--twee",
        "twee",
        "--direct",
        "--debug",
        "p.p",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let (flags, rest) = parse_flags(&args);
    assert_eq!(
        flags,
        Flags {
            term_size: true,
            debug: true,
            vampire: Some("/opt/vampire".into()),
            twee: Some("twee".into()),
            ..Flags::default()
        }
    );
    // what belongs to a whole run is left for `parse_request`
    assert_eq!(rest, ["--direct", "p.p"]);
}

#[test]
fn refinement_is_asked_for_separately() {
    use krympa::execution::parse_flags;
    let args = |list: &[&str]| list.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    assert!(!parse_flags(&args(&["--term-size", "p.p"])).0.refine);
    let (flags, _) = parse_flags(&args(&["--refine", "p.p"]));
    assert!(flags.refine && !flags.term_size);
}

fn request(args: &[&str]) -> Result<krympa::execution::Request, String> {
    let args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
    krympa::execution::parse_request(&args)
}

#[test]
fn a_problem_file_alone_asks_for_the_whole_run() {
    use krympa::execution::{Request, WholeRun};
    assert_eq!(
        request(&["p.p"]),
        Ok(Request::Whole {
            input: "p.p".into(),
            options: WholeRun::default()
        })
    );
    assert_eq!(
        request(&["--lean", "p.p", "--direct", "--no-compress"]),
        Ok(Request::Whole {
            input: "p.p".into(),
            options: WholeRun {
                direct: true,
                compress: false,
                lean: true,
                vampire_proof: None
            }
        })
    );
}

#[test]
fn a_whole_run_removes_avoidable_steps_unless_told_not_to() {
    use krympa::execution::{Request, WholeRun};
    let Ok(Request::Whole { options, .. }) = request(&["p.p"]) else {
        panic!("not a whole run");
    };
    assert!(options.compress);
    assert_eq!(options, WholeRun::default());
    let Ok(Request::Whole { options, .. }) = request(&["--no-compress", "p.p"]) else {
        panic!("not a whole run");
    };
    assert!(!options.compress);
}

#[test]
fn a_whole_run_can_start_from_a_saved_vampire_proof() {
    use krympa::execution::{Request, WholeRun};
    assert_eq!(
        request(&["--direct", "--vampire-proof", "saved.out", "p.p"]),
        Ok(Request::Whole {
            input: "p.p".into(),
            options: WholeRun {
                direct: true,
                vampire_proof: Some("saved.out".into()),
                ..WholeRun::default()
            }
        })
    );
    // the file is the next argument, even one that looks like a whole-run flag
    let Ok(Request::Whole { options, .. }) = request(&["--vampire-proof", "--lean", "p.p"]) else {
        panic!("not a whole run");
    };
    assert_eq!(options.vampire_proof.as_deref(), Some("--lean"));
    assert!(!options.lean);
    assert!(request(&["p.p", "--vampire-proof"]).is_err());
    assert!(request(&["--vampire-proof", "saved.out", "direct", "p.p"]).is_err());
}

#[test]
fn a_saved_vampire_proof_is_put_where_the_phases_read_it() {
    use krympa::provers::use_saved_vampire_proof;
    use std::fs;
    let dir = std::env::temp_dir().join(format!("krympa_saved_proof_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let saved = dir.join("vampire_proof_62.out");
    let text = "1. op(X0,X1) = X0 [input]\n";
    fs::write(&saved, text).unwrap();
    let output = dir.join("output").join("vampire_proof_p.out");
    let (saved, output) = (saved.to_str().unwrap(), output.to_str().unwrap());

    assert!(use_saved_vampire_proof(saved, output));
    assert_eq!(fs::read_to_string(output).unwrap(), text);
    // the proof already in place is kept, not emptied
    assert!(use_saved_vampire_proof(output, output));
    assert_eq!(fs::read_to_string(output).unwrap(), text);

    let (empty, missing) = (dir.join("empty.out"), dir.join("missing.out"));
    fs::write(&empty, "\n").unwrap();
    assert!(!use_saved_vampire_proof(empty.to_str().unwrap(), output));
    assert!(!use_saved_vampire_proof(missing.to_str().unwrap(), output));
    // a failed start leaves the proof that was there
    assert_eq!(fs::read_to_string(output).unwrap(), text);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_phase_name_asks_for_that_phase_only() {
    use krympa::execution::Request;
    assert_eq!(
        request(&["minimize", "p.p"]),
        Ok(Request::Phase {
            phase: "minimize".into(),
            input: "p.p".into()
        })
    );
}

#[test]
fn lean_and_compress_work_on_a_proof_file() {
    use krympa::execution::Request;
    assert_eq!(
        request(&["compress", "proof_p.out"]),
        Ok(Request::Tool {
            tool: "compress".into(),
            proof: "proof_p.out".into()
        })
    );
}

#[test]
fn malformed_requests_are_rejected() {
    assert!(request(&[]).is_err());
    assert!(request(&["collect"]).is_err());
    assert!(request(&["lean"]).is_err());
    assert!(request(&["prove", "p.p"]).is_err());
    assert!(request(&["--direct", "minimize", "p.p"]).is_err());
    assert!(request(&["--lean", "compress", "proof_p.out"]).is_err());
    assert!(request(&["--compress", "p.p"]).is_err());
    assert!(request(&["--directt", "p.p"]).is_err());
    assert!(request(&["p.p", "q.p"]).is_err());
}
