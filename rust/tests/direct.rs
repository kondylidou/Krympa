use krympa::direct::keep_needed;

const BLOCK: &str = "\
% === Superposition Steps ===
% lemma_0001: op(X0,X1) = X0 | deps: a_1: ! [X0] : op(X0,X0) = X0
% lemma_0002: op(X1,X0) = X0 | deps: a_1: ! [X0] : op(X0,X0) = X0
% lemma_0003: X0 = X1 | deps: lemma_0001: op(X0,X1) = X0, a_1: ! [X0] : op(X0,X0) = X0
";

#[test]
fn keeps_only_what_the_later_proof_needs() {
    let later = "Axiom 1 (lemma_0003): X = Y.\n";
    let kept = keep_needed(BLOCK, later);
    assert!(kept.contains("% lemma_0003:"));
    assert!(kept.contains("% lemma_0001:"), "dependency of a kept line");
    assert!(!kept.contains("% lemma_0002:"), "unused line must go");
    assert!(kept.contains("% === Superposition Steps ==="));
}

#[test]
fn keeps_nothing_when_nothing_is_used() {
    assert_eq!(keep_needed(BLOCK, "Axiom 1 (a1): op(X, X) = X.\n"), "");
}
