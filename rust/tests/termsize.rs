use krympa::prover_wrapper::{avg_term_size_twee, avg_term_size_vampire};

// Twee proof with three intermediate terms:
//   op(X, Y)          → term_size = 1*2+1 = 3
//   op(X, op(Y, X))   → term_size = 2*2+1 = 5
//   X                 → term_size = 0*2+1 = 1
// avg = (3+5+1)/3 = 3.0
#[test]
fn test_avg_term_size_twee() {
    let proof = "\
Goal 1 (foo): op(X, Y) = X.
Proof:
  op(X, Y)
= { by axiom 1 }
  op(X, op(Y, X))
= { by axiom 2 }
  X

RESULT: Theorem (the conjecture is true).
";
    let avg = avg_term_size_twee(proof);
    assert!(
        (avg - 3.0).abs() < 1e-9,
        "expected avg_term_size=3.0, got {}",
        avg
    );
}

// Vampire proof with three inference steps:
//   superposition:              op(X0,X1) = op(op(X0,X1),op(X0,X1))
//     LHS op(X0,X1)             → 1*2+1 = 3
//     RHS op(op(X0,X1),op(…))   → 3*2+1 = 7
//   demodulation:               op(X0,X1) = X0
//     LHS op(X0,X1)             → 3
//     RHS X0                    → 1
//   trivial inequality removal: $false
//     body "$false"             → 0*2+1 = 1
// sizes = [3, 7, 3, 1, 1], avg = 15/5 = 3.0
#[test]
fn test_avg_term_size_vampire() {
    let proof = "\
% Refutation found.
2. op(X0,X1) = op(X0,X1) [input(assumption)]
50. op(X0,X1) = op(op(X0,X1),op(X0,X1)) [superposition 1,2]
51. op(X0,X1) = X0 [demodulation 50,16]
52. $false [trivial inequality removal 51]
";
    // line 2: [input(assumption)] — not a proof keyword → skipped
    let avg = avg_term_size_vampire(proof);
    assert!(
        (avg - 3.0).abs() < 1e-9,
        "expected avg_term_size=3.0, got {}",
        avg
    );
}
