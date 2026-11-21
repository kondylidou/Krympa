use krympa::direct::cited_lemmas;

const TWEE_PROOF: &str = "\
The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0008): op(X, Y) = op(op(X, Y), op(Z, op(X, Z))).
Axiom 3 (lemma_0020): op(X, op(Y, X)) = X.

Goal 1 (conjecture_0021): op(x0, x1) = x0.
Proof:
  op(x0, x1)
= { by axiom 2 (lemma_0008) }
  op(op(x0, x1), op(x1, op(x0, x1)))
= { by axiom 3 (lemma_0020) }
  x0
";

#[test]
fn reads_the_lemmas_a_twee_proof_uses() {
    let used: Vec<u32> = cited_lemmas(TWEE_PROOF).into_iter().collect();
    assert_eq!(used, [8, 20]);
}

#[test]
fn a_proof_from_the_axioms_alone_uses_no_lemma() {
    let proof = "Axiom 1 (a1): X = op(X, X).\n\nGoal 1 (conjecture_0003): x0 = op(x0, x0).\n";
    assert!(cited_lemmas(proof).is_empty());
}
