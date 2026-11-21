use krympa::compress::compress;
use krympa::lean::translate;
use krympa::rewrite::{parse_equation, parse_term, Fact, Library};

/// Equation 102 implies equation 617: the second line only restates the first.
const PROOF: &str = "\
% === Input Problem ===
fof(a1, axiom,
    ! [X0, X1] :
        (X0 = op(X0,op(op(X0,X1),X1)))
).

fof(conjecture0, conjecture,
    ! [X0, X1] :
        (X0 = op(X0,op(X0,op(op(X0,X1),X1))))
).


% === Superposition Steps ===
% lemma_0001: op(X0,op(X0,op(op(X0,X1),X1))) = X0 | deps: a_1: ! [X0,X1] : X0 = op(X0,op(op(X0,X1),X1))

% === Superposition Steps ===
% lemma_0001: ! [X0,X1] : X0 = op(X0,op(X0,op(op(X0,X1),X1))) | deps: lemma_0001, lemma_0001
";

#[test]
fn terms_over_op_are_parsed_and_others_rejected() {
    assert!(parse_term("op(X0, op(X1,X0))").is_ok());
    assert!(parse_term("op(X0,X1) X2").is_err());
    assert!(parse_term("mult(X0,X1)").is_err());
    assert!(parse_equation("! [X0] : (X0 = op(X0,X0))").is_ok());
}

#[test]
fn one_rewrite_is_found_and_two_are_not() {
    let (lhs, rhs) = parse_equation("op(X,X) = X").unwrap();
    let mut library = Library::default();
    let idempotence = library.add(Fact::new("idem", &lhs, &rhs));

    // op(op(a,a), b) = op(a, b): one rewrite inside the left argument
    let (s, t) = parse_equation("op(op(A,A),B) = op(A,B)").unwrap();
    let found = library.justify((&s, &t), &[idempotence], "a", true, None);
    let (proof, rewrites, _) = found.expect("one rewrite suffices");
    assert_eq!(rewrites, 1);
    assert!(proof.contains("congrArg"), "{}", proof);

    // op(op(op(a,a),a), b) = op(a, b) needs two rewrites
    let (s, t) = parse_equation("op(op(op(A,A),A),B) = op(A,B)").unwrap();
    assert!(library
        .justify((&s, &t), &[idempotence], "a", true, None)
        .is_none());
}

#[test]
fn every_step_of_a_proof_becomes_a_proof_term() {
    let translation = translate(PROOF, "proof.out").unwrap();
    assert!(translation.certified, "{:?}", translation.messages);
    assert_eq!(translation.steps, 2);
    assert!(!translation.lean.contains("sorry"));
    assert!(translation
        .lean
        .contains("theorem Equation_a1_implies_Equation_conjecture0"));
}

#[test]
fn a_restated_lemma_is_removed() {
    let shorter = compress(PROOF).unwrap();
    assert_eq!((shorter.steps_before, shorter.steps_after), (2, 1));
    assert!(shorter.text.contains("| deps: a1"), "{}", shorter.text);
    assert!(translate(&shorter.text, "shorter.out").unwrap().certified);
}

#[test]
fn a_step_that_is_not_one_rewrite_is_reported() {
    // the second line claims what no rewrite can give
    let broken = PROOF.replace(
        "% lemma_0001: ! [X0,X1] : X0 = op(X0,op(X0,op(op(X0,X1),X1))) | deps: lemma_0001, lemma_0001",
        "% lemma_0002: X0 = X1 | deps: lemma_0001",
    );
    let translation = translate(&broken, "broken.out").unwrap();
    assert!(!translation.certified);
    assert!(translation.lean.contains("sorry"));
    assert!(compress(&broken).is_err());
}

/// Equation 1842 implies equation 1477, reduced: `l3` follows from `l2` or,
/// in one rewrite, from `l4`, which itself comes from `l2`. Removing `l2`
/// must not leave `l4` behind without its derivation.
#[test]
fn a_removed_line_is_not_needed_by_its_replacement() {
    let proof = std::fs::read_to_string("tests/data/proof_1842_1477.out").unwrap();
    let before = translate(&proof, "proof.out").unwrap();
    assert!(before.certified);
    let shorter = compress(&proof).unwrap();
    assert!(shorter.steps_after <= shorter.steps_before);
    let after = translate(&shorter.text, "shorter.out").unwrap();
    assert!(after.certified, "{:?}\n{}", after.messages, shorter.text);
    // every premise a line lists is still in the file
    for line in shorter.text.lines().filter(|l| l.starts_with("% lemma_")) {
        let deps = line.split_once("| deps:").unwrap().1;
        for dep in deps
            .split(", ")
            .map(str::trim)
            .filter(|d| d.starts_with("lemma_"))
        {
            let name = dep.split(':').next().unwrap();
            assert!(
                shorter.text.contains(&format!("% {}:", name)),
                "{} is cited but not derived:\n{}",
                name,
                shorter.text
            );
        }
    }
}
