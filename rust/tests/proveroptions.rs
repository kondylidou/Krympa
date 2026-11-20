use krympa::prover_wrapper::extra_options;

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
