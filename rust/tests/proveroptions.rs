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
fn prover_executables_are_read_from_the_command_line() {
    use krympa::execution::parse_prover_executables;
    let args: Vec<String> = [
        "--vampire",
        "/opt/vampire",
        "--term-size",
        "--twee",
        "twee",
        "direct",
        "p.p",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let (vampire, twee, rest) = parse_prover_executables(&args);
    assert_eq!(vampire.as_deref(), Some("/opt/vampire"));
    assert_eq!(twee.as_deref(), Some("twee"));
    assert_eq!(rest, ["--term-size", "direct", "p.p"]);
}
