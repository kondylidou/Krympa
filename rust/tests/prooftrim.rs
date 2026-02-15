use krympa::minimize::count_superposition_steps;
use krympa::minimize::trim_proof_parts;
use krympa::minimize::trim_superposition_block;
use krympa::prover_wrapper::proof_length_twee;
use krympa::prover_wrapper::proof_length_vampire;

/// Exact regression: later proof mentions only `lemma_0059` (and
/// `history_lemma_0058`), but the superposition block must keep the whole
/// dependency chain: lemma_0059 -> lemma_0055 -> (lemma_0053, lemma_0054)
#[test]
fn trim_keeps_dependency_chain() {
    let block = r#"
% lemma_0053: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))) | deps: lemma_0049: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(op(X17,X18),X18),op(X18,op(op(X17,X18),X18))))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0054: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213))) | deps: lemma_0050: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(op(X210,X211),X211),op(X211,op(op(X210,X211),X211))),X213))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18))) | deps: lemma_0053: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))), lemma_0054: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213)))
% lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))) | deps: lemma_0016: op(X10,op(X8,X10)) = op(op(X10,op(X8,X10)),op(op(X9,op(X8,X9)),op(X6,op(op(X7,X8),X6)))), lemma_0052: op(op(X14,X13),X13) = op(op(op(X14,X13),X13),op(X15,op(X13,X15)))
% lemma_0059: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144))) | deps: lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))), lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18)))
% history_lemma_0058: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144))) | deps: lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))), lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18)))
"#;

    let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.
Axiom 2 (lemma_0059): op(X, op(Y, X)) = op(op(X, op(Y, X)), op(Z, op(Y, Z))).
"#;

    let seg2 = r#"Goal 1 (conjecture0): ..."#;
    let seg3 = r#"
% lemma_0060: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))) | deps: lemma_0059: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(op(X17,X18),X18),op(X18,op(op(X17,X18),X18))))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0061: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213))) | deps: lemma_0050: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(op(X210,X211),X211),op(X211,op(op(X210,X211),X211))),X213))), lemma_0060: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
"#;

    let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

    // used
    assert!(trimmed.contains("% lemma_0059:"));
    assert!(trimmed.contains("% history_lemma_0058:"));

    // dependency chain that must be kept even if not mentioned later
    assert!(trimmed.contains("% lemma_0056:"));
    assert!(trimmed.contains("% lemma_0055:"));
    assert!(trimmed.contains("% lemma_0054:"));
    assert!(trimmed.contains("% lemma_0053:"));

    // sanity: should not introduce anything else
    assert!(!trimmed.contains("% lemma_0060:"));
    assert_eq!(count_superposition_steps(&trimmed), 6);
}

/// Exact regression: later proof mentions `lemma_0067` (as a dep of
/// axioms/proof), which implies we must keep `lemma_0066` even though the
/// final proof never mentions `lemma_0066` directly
#[test]
fn trim_keeps_internal_dep() {
    let block = r#"
% lemma_0066: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(X9,op(op(X7,X8),X9)),op(X6,op(op(X7,X8),X6)))) | deps: lemma_0039: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(op(X9,op(op(X7,X8),X9)),op(X10,op(op(X11,op(X7,X8)),X10))),op(X6,op(op(X7,X8),X6)))), lemma_0063: op(X199,op(X197,X199)) = op(op(X199,op(X197,X199)),op(X198,op(op(X196,X197),X198)))
% lemma_0067: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(X9,op(op(X7,X8),X9))) | deps: lemma_0066: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(X9,op(op(X7,X8),X9)),op(X6,op(op(X7,X8),X6)))), lemma_0059: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144)))
% lemma_0068: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(X1,op(op(X2,X0),X1)),X0)) | deps: lemma_0008: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,op(op(X3,X0),X4)))), lemma_0067: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(X9,op(op(X7,X8),X9)))
% lemma_0074: op(op(X3,X0),X4) = op(op(X3,X0),X4) | deps: lemma_0068: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(X1,op(op(X2,X0),X1)),X0)), lemma_0008: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,op(op(X3,X0),X4))))
% history_lemma_0058: op(X1052,op(op(X1050,op(op(X1051,X1050),X1050)),X1052)) = X1052 | deps: lemma_0074: op(X1052,op(op(op(X1050,op(op(X1051,X1050),X1050)),X1052),op(op(X1055,op(op(X1056,X1052),X1055)),X1052))) = X1052, lemma_0070: op(op(X1364,op(op(X1365,X1364),X1364)),X1366) = op(op(op(X1364,op(op(X1365,X1364),X1364)),X1366),op(op(X1367,op(op(X1368,X1366),X1367)),X1366))
"#;

    // 3 later segments; only segment 1 mentions history_lemma_0058 /
    // lemma_0059 (axioms). But the superposition liness above show that
    // history_lemma_0058 depends (eventually) on lemma_0068, which depends on
    // lemma_0067, which depends on lemma_0066.
    let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.
Axiom 2 (lemma_0059): op(X, op(Y, X)) = op(op(X, op(Y, X)), op(Z, op(Y, Z))).
"#;

    let seg2 = r#"Goal 1 (conjecture0): ..."#;
    let seg3 = r#"RESULT: Theorem."#;

    let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

    // because later proof uses history_lemma_0058 (axiom), we keep it
    assert!(trimmed.contains("% history_lemma_0058:"));

    // and we must keep the internal chain that leads to it
    assert!(trimmed.contains("% lemma_0068:"));
    assert!(trimmed.contains("% lemma_0067:"));
    assert!(trimmed.contains("% lemma_0066:"));
    assert_eq!(count_superposition_steps(&trimmed), 5);
}

/// Exact regression: Here the superposition block contains
/// lemma_0001..lemma_0008, but the proof only ever uses lemma_0003 (as axiom
/// 2). The trimmer must drop lemma_0004..lemma_0008
#[test]
fn trim_with_three_segments1() {
    let block = r#"% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))) | deps: lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))) | deps: lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))), lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16))))
% lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))) | deps: lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0008: op(X29,op(X27,X29)) = op(op(X29,op(X27,X29)),op(op(X27,op(op(X28,X27),X27)),op(X27,op(op(X27,op(op(X28,X27),X27)),X27)))) | deps: lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))), lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))

"#;

    // Segment 1
    let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0003): op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))).

"#;

    // Segment 2
    let seg2 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).
Axiom 3 (lemma_0002): op(X, op(op(Y, op(op(Z, op(W, X)), Y)), op(W, X))) = X.
Axiom 4 (lemma_0003): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(op(W, op(op(V, Z), W)), Z)).

Lemma 5: op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z))) = op(X, op(Y, X)).
Proof:
op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 1 (a1) }
op(op(X, op(op(Y, op(W, op(op(V, Y), W))), X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 2 (lemma_0001) R->L }
op(X, op(op(Y, op(W, op(op(V, Y), W))), X))
= { by axiom 1 (a1) R->L }
op(X, op(Y, X))

Goal 1 (history_lemma_0061): x0 = op(x0, x1).
Proof:
x0
= { by axiom 3 (lemma_0002) R->L }
op(x0, op(X, x1))
= { by axiom 4 (lemma_0003) R->L }
op(x0, op(op(X, x1), x1))
= { by lemma 5 }
op(x0, op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
op(x0, x1)
"#;

    // Segment 3
    let seg3 = r#"
% === Superposition Steps ===
% lemma_0009: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0010: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))
    "#;

    let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

    assert!(trimmed.contains("% === Superposition Steps ==="));
    assert!(trimmed.contains("% lemma_0001:"));
    assert!(trimmed.contains("% lemma_0002:"));
    assert!(trimmed.contains("% lemma_0003:"));

    // these must be gone (even though they appear after lemma_0003 in the
    // block)
    assert!(!trimmed.contains("% lemma_0004:"));
    assert!(!trimmed.contains("% lemma_0005:"));
    assert!(!trimmed.contains("% lemma_0006:"));
    assert!(!trimmed.contains("% lemma_0007:"));
    assert!(!trimmed.contains("% lemma_0008:"));
    assert_eq!(count_superposition_steps(&trimmed), 3);
}

/// Exact regression: Here the superposition block contains
/// lemma_0001..lemma_0005, but the proof only ever uses lemma_0003
#[test]
fn trim_with_two_segments1() {
    let block = r#"% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0)) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63 | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0))
% lemma_0005: op(X2,op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(op(X4,op(op(X5,X2),X4)),X2))) = X2 | deps: lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
"#;

    // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
    let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).
Axiom 3 (lemma_0002): op(X, op(op(Y, op(op(Z, op(W, X)), Y)), op(W, X))) = X.
Axiom 4 (lemma_0003): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(op(W, op(op(V, Z), W)), Z)).

Lemma 5: op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z))) = op(X, op(Y, X)).
Proof:
op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 1 (a1) }
op(op(X, op(op(Y, op(W, op(op(V, Y), W))), X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 2 (lemma_0001) R->L }
op(X, op(op(Y, op(W, op(op(V, Y), W))), X))
= { by axiom 1 (a1) R->L }
op(X, op(Y, X))

"#;

    // Segment 3: the final goal proof — still no lemma_0004..0008 usage
    let seg3 = r#"RESULT: Theorem (the conjecture is true)."#;

    let trimmed = trim_superposition_block(block, &[seg1, seg3]);

    assert!(trimmed.contains("% === Superposition Steps ==="));
    assert!(trimmed.contains("% lemma_0001:"));
    assert!(trimmed.contains("% lemma_0002:"));
    assert!(trimmed.contains("% lemma_0003:"));

    // these must be gone (even though they appear after lemma_0003 in the
    // block)
    assert!(!trimmed.contains("% lemma_0004:"));
    assert!(!trimmed.contains("% lemma_0005:"));
    assert!(!trimmed.contains("% lemma_0006:"));
    assert!(!trimmed.contains("% lemma_0007:"));
    assert!(!trimmed.contains("% lemma_0008:"));
    assert_eq!(count_superposition_steps(&trimmed), 3);
}

#[test]
fn trim_with_two_segments2() {
    let block = r#"
% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0)) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63 | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0))
% lemma_0005: op(X2,op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(op(X4,op(op(X5,X2),X4)),X2))) = X2 | deps: lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
"#;

    // Segment 1
    let seg2 = r#"
The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).
Axiom 3 (lemma_0002): op(X, op(op(Y, op(op(Z, op(W, X)), Y)), op(W, X))) = X.
Axiom 4 (lemma_0003): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(op(W, op(op(V, Z), W)), Z)).

Lemma 5: op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z))) = op(X, op(Y, X)).
Proof:
op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 1 (a1) }
op(op(X, op(op(Y, op(W, op(op(V, Y), W))), X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 2 (lemma_0001) R->L }
op(X, op(op(Y, op(W, op(op(V, Y), W))), X))
= { by axiom 1 (a1) R->L }
op(X, op(Y, X))

Lemma 6: op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(W, op(op(V, Y), W)))) = op(X, op(Y, X)).
Proof:
op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(W, op(op(V, Y), W))))
= { by axiom 2 (lemma_0001) }
op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(op(W, op(op(V, Y), W)), op(Z, op(Y, Z)))))
= { by lemma 5 }
op(X, op(Y, X))

Lemma 7: op(op(X, op(op(Y, Y), X)), op(Y, op(op(Y, Y), Y))) = op(X, op(op(Y, Y), X)).
Proof:
op(op(X, op(op(Y, Y), X)), op(Y, op(op(Y, Y), Y)))
= { by axiom 1 (a1) }
op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(Y, op(op(Y, Y), Y))), op(Y, op(op(Y, Y), Y))))))
= { by axiom 2 (lemma_0001) }
op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))), op(Y, op(op(Y, Y), Y))))))
= { by axiom 2 (lemma_0001) }
op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, Y), Y), op(Y, op(op(Y, Y), Y))))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(Y, Y)), op(Y, op(op(Y, Y), Y))))))
= { by lemma 6 }
op(X, op(op(Y, Y), X))

Lemma 8: op(op(op(X, X), X), op(X, op(op(X, X), X))) = op(op(X, X), X).
Proof:
op(op(op(X, X), X), op(X, op(op(X, X), X)))
= { by lemma 7 R->L }
op(op(op(X, X), X), op(op(X, op(op(X, X), X)), op(X, op(op(X, X), X))))
= { by lemma 7 R->L }
op(op(op(X, X), X), op(op(X, op(op(X, X), X)), op(op(X, op(op(X, X), X)), op(X, op(op(X, X), X)))))
= { by axiom 1 (a1) R->L }
op(op(X, X), X)

Lemma 9: op(X, op(op(op(Y, X), op(Y, X)), op(Y, X))) = X.
Proof:
op(X, op(op(op(Y, X), op(Y, X)), op(Y, X)))
= { by lemma 8 R->L }
op(X, op(op(op(op(Y, X), op(Y, X)), op(Y, X)), op(op(Y, X), op(op(op(Y, X), op(Y, X)), op(Y, X)))))
= { by axiom 1 (a1) R->L }
X

Lemma 10: op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z)))) = op(op(X, Y), Z).
Proof:
op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z))))
= { by axiom 2 (lemma_0001) }
op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(op(Z, op(op(X, Y), Z)), op(W, op(Y, W)))))
= { by axiom 1 (a1) R->L }
op(op(X, Y), Z)

Lemma 11: op(op(op(X, op(op(Y, Z), Z)), W), op(op(Z, op(op(Y, Z), Z)), op(W, op(op(X, op(op(Y, Z), Z)), W)))) = op(op(X, op(op(Y, Z), Z)), W).
Proof:
op(op(op(X, op(op(Y, Z), Z)), W), op(op(Z, op(op(Y, Z), Z)), op(W, op(op(X, op(op(Y, Z), Z)), W))))
= { by axiom 2 (lemma_0001) }
op(op(op(X, op(op(Y, Z), Z)), W), op(op(op(Z, op(op(Y, Z), Z)), op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z)))), op(W, op(op(X, op(op(Y, Z), Z)), W))))
= { by lemma 10 }
op(op(X, op(op(Y, Z), Z)), W)

Lemma 12: op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))))) = op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))).
Proof:
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 R->L }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 R->L }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 4 (lemma_0003) R->L }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) R->L }
op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))))))
= { by lemma 11 }
op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))))

Lemma 13: op(op(X, op(Y, X)), op(Y, op(Y, Y))) = op(X, op(Y, X)).
Proof:
op(op(X, op(Y, X)), op(Y, op(Y, Y)))
= { by axiom 3 (lemma_0002) R->L }
op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, Y), op(Y, op(Y, Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by lemma 12 }
op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by lemma 12 }
op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y))))))
= { by lemma 6 }
op(X, op(Y, X))

Lemma 14: op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X))) = op(X, X).
Proof:
op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))
= { by lemma 8 R->L }
op(op(X, X), op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))))
= { by axiom 2 (lemma_0001) }
op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 9 R->L }
op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(op(op(X, op(X, X)), op(X, op(X, X))), op(X, op(X, X)))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 13 }
op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(op(X, op(X, X)), op(X, op(X, X)))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 13 }
op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(X, op(X, X))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by axiom 3 (lemma_0002) }
op(X, X)

Lemma 15: op(op(X, X), op(X, X)) = op(X, X).
Proof:
op(op(X, X), op(X, X))
= { by lemma 14 R->L }
op(op(X, X), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X))))
= { by axiom 1 (a1) R->L }
op(X, X)

Lemma 16: op(X, op(X, X)) = X.
Proof:
op(X, op(X, X))
= { by lemma 15 R->L }
op(X, op(op(X, X), op(X, X)))
= { by lemma 15 R->L }
op(X, op(op(X, X), op(op(X, X), op(X, X))))
= { by axiom 1 (a1) R->L }
X

Lemma 17: op(X, X) = X.
Proof:
op(X, X)
= { by lemma 16 R->L }
op(X, op(X, op(X, X)))
= { by lemma 16 R->L }
op(op(X, op(X, X)), op(X, op(X, X)))
= { by lemma 13 }
op(X, op(X, X))
= { by lemma 16 }
X

Lemma 18: op(X, op(Y, X)) = X.
Proof:
op(X, op(Y, X))
= { by lemma 17 R->L }
op(X, op(op(Y, X), op(Y, X)))
= { by lemma 17 R->L }
op(X, op(op(Y, X), op(op(Y, X), op(Y, X))))
= { by axiom 1 (a1) R->L }
X

Lemma 19: op(op(X, Y), Y) = op(X, Y).
Proof:
op(op(X, Y), Y)
= { by axiom 3 (lemma_0002) R->L }
op(op(X, Y), op(Y, op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by lemma 16 R->L }
op(op(X, Y), op(op(Y, op(Y, Y)), op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by axiom 3 (lemma_0002) R->L }
op(op(X, Y), op(op(Y, op(op(Y, op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))), Y)), op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by axiom 3 (lemma_0002) }
op(X, Y)

Lemma 20: op(op(X, Y), op(Z, op(Y, Z))) = op(X, Y).
Proof:
op(op(X, Y), op(Z, op(Y, Z)))
= { by lemma 17 R->L }
op(op(op(X, Y), op(X, Y)), op(Z, op(Y, Z)))
= { by lemma 19 R->L }
op(op(op(op(X, Y), op(X, Y)), op(X, Y)), op(Z, op(Y, Z)))
= { by lemma 9 R->L }
op(op(op(op(X, Y), op(X, Y)), op(X, Y)), op(Z, op(op(Y, op(op(op(X, Y), op(X, Y)), op(X, Y))), Z)))
= { by axiom 1 (a1) R->L }
op(op(op(X, Y), op(X, Y)), op(X, Y))
= { by lemma 19 }
op(op(X, Y), op(X, Y))
= { by lemma 17 }
op(X, Y)

Lemma 21: op(X, op(op(Y, X), op(Z, op(Y, X)))) = X.
Proof:
op(X, op(op(Y, X), op(Z, op(Y, X))))
= { by lemma 19 R->L }
op(X, op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))))
= { by axiom 1 (a1) }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(Y, X))), X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(op(op(Y, X), op(op(X, X), op(Y, X))), X)))))
= { by axiom 4 (lemma_0003) R->L }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(Y, X))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 R->L }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(X, op(X, X))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 9 R->L }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(op(Y, X), op(X, op(X, X))), op(op(Y, X), op(X, op(X, X)))), op(op(Y, X), op(X, op(X, X)))))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(op(Y, X), op(X, op(X, X)))), op(op(Y, X), op(X, op(X, X)))))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(op(Y, X), op(X, op(X, X)))), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(Y, X)), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 19 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(Y, X), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 17 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(Y, X))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 1 (a1) R->L }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 1 (a1) }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), op(X, op(op(X, X), op(op(Y, X), op(X, X))))), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 16 R->L }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), op(op(X, op(X, X)), op(op(X, X), op(op(Y, X), op(X, X))))), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 10 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(Y, X), op(X, X)), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 17 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(Y, X), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 19 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 2 (lemma_0001) }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(X, op(X, X))))))
= { by lemma 16 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), X))))
= { by axiom 1 (a1) }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(X, op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))))
= { by lemma 20 }
op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(Y, X)))
= { by axiom 3 (lemma_0002) }
X

Lemma 22: op(X, op(Y, Z)) = X.
Proof:
op(X, op(Y, Z))
= { by lemma 18 R->L }
op(X, op(op(Y, Z), op(Z, op(Y, Z))))
= { by lemma 19 R->L }
op(X, op(op(Y, Z), op(Z, op(op(Y, Z), Z))))
= { by lemma 19 R->L }
op(X, op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))))
= { by lemma 6 R->L }
op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(op(W, X), op(Y, Z)), op(Z, op(op(W, X), op(Y, Z)))), op(Z, op(op(V, Z), Z)))))
= { by lemma 18 }
op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(op(V, Z), Z)))))
= { by lemma 19 }
op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 19 }
op(X, op(op(op(op(Y, Z), Z), op(Z, op(Y, Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 19 }
op(X, op(op(op(Y, Z), op(Z, op(Y, Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 18 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 18 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), Z)))
= { by lemma 21 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(Z, op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 1 (a1) }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(Z, op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(Z, Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(Z, Z), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 15 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, Z), op(Z, Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(Z, Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 14 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 11 R->L }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 14 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(Z, Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(Z, Z)), op(Z, op(op(Z, op(Z, Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(Z, Z)), op(Z, op(Z, Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 4 (lemma_0003) }
op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z), op(op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z)))), op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 3 (lemma_0002) }
op(X, op(op(Y, Z), op(op(W, X), op(Y, Z))))
= { by axiom 1 (a1) R->L }
X

Goal 1 (history_lemma_0061): x0 = op(x0, x1).
Proof:
x0
= { by lemma 22 R->L }
op(x0, op(X, x1))
= { by lemma 19 R->L }
op(x0, op(op(X, x1), x1))
= { by lemma 22 R->L }
op(op(x0, op(op(X, x1), x1)), op(Y, x1))
= { by lemma 11 R->L }
op(op(op(x0, op(op(X, x1), x1)), op(Y, x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(op(X, x1), x1)), op(Y, x1)))))
= { by lemma 22 }
op(op(x0, op(op(X, x1), x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(op(X, x1), x1)), op(Y, x1)))))
= { by lemma 19 }
op(op(x0, op(op(X, x1), x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 19 }
op(op(x0, op(op(X, x1), x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 19 }
op(op(x0, op(X, x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 22 }
op(op(x0, op(X, x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 22 }
op(x0, op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 18 }
op(x0, op(x1, op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 21 }
op(x0, x1)

RESULT: Theorem (the conjecture is true).
"#;

    // Segment 3
    let seg3 = r#"
RESULT: Theorem (the conjecture is true).
The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0061): X = op(X, Y).

Goal 1 (conjecture0): x0 = op(x0, op(x1, op(x2, op(x0, x2)))).
Proof:
x0
= { by axiom 1 (history_lemma_0061) }
op(x0, op(x1, op(x2, op(x0, x2))))

RESULT: Theorem (the conjecture is true).
    "#;

    let trimmed = trim_superposition_block(block, &[seg2, seg3]);

    assert!(trimmed.contains("% === Superposition Steps ==="));
    assert!(trimmed.contains("% lemma_0001:"));
    assert!(trimmed.contains("% lemma_0002:"));
    assert!(trimmed.contains("% lemma_0003:"));

    // these must be gone (even though they appear after lemma_0003 in the
    // block)
    assert!(!trimmed.contains("% lemma_0004:"));
    assert!(!trimmed.contains("% lemma_0005:"));
    assert!(!trimmed.contains("% lemma_0006:"));
    assert!(!trimmed.contains("% lemma_0007:"));
    assert!(!trimmed.contains("% lemma_0008:"));
    assert_eq!(count_superposition_steps(&trimmed), 3);
}

#[test]
fn trim_with_two_segments3() {
    let block = r#"
% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))) | deps: lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))) | deps: lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))), lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16))))
% lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))) | deps: lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0008: op(X29,op(X27,X29)) = op(op(X29,op(X27,X29)),op(op(X27,op(op(X28,X27),X27)),op(X27,op(op(X27,op(op(X28,X27),X27)),X27)))) | deps: lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))), lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))
"#;

    // Segment 2
    let seg2 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).

Lemma 3: op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))) = op(X, op(op(Y, op(op(Z, W), W)), X)).
Proof:
op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W)))
= { by axiom 2 (lemma_0001) }
op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(op(W, op(op(Z, W), W)), op(op(op(Z, W), W), op(W, op(op(Z, W), W)))))
= { by axiom 2 (lemma_0001) R->L }
op(X, op(op(Y, op(op(Z, W), W)), X))

Lemma 4: op(op(X, op(op(Y, X), X)), op(Z, op(op(W, op(op(V, op(op(Y, X), X)), W)), Z))) = op(X, op(op(Y, X), X)).
Proof:
op(op(X, op(op(Y, X), X)), op(Z, op(op(W, op(op(V, op(op(Y, X), X)), W)), Z)))
= { by lemma 3 R->L }
op(op(X, op(op(Y, X), X)), op(Z, op(op(op(W, op(op(V, op(op(Y, X), X)), W)), op(X, op(op(Y, X), X))), Z)))
= { by axiom 1 (a1) R->L }
op(X, op(op(Y, X), X))

Lemma 5: op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(W, U)), V))) = op(X, op(op(Y, op(op(Z, W), Y)), X)).
Proof:
op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(W, U)), V)))
= { by axiom 1 (a1) }
op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(op(W, op(Y, op(op(Z, W), Y))), U)), V)))
= { by axiom 2 (lemma_0001) }
op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(op(U, op(op(W, op(Y, op(op(Z, W), Y))), U)), op(X, op(op(Y, op(op(Z, W), Y)), X))), V)))
= { by axiom 1 (a1) R->L }
op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(op(U, op(W, U)), op(X, op(op(Y, op(op(Z, W), Y)), X))), V)))
= { by axiom 1 (a1) R->L }
op(X, op(op(Y, op(op(Z, W), Y)), X))

Lemma 6: op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z)))) = op(op(X, Y), Z).
Proof:
op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z))))
= { by axiom 2 (lemma_0001) }
op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(op(Z, op(op(X, Y), Z)), op(W, op(Y, W)))))
= { by axiom 1 (a1) R->L }
op(op(X, Y), Z)

Lemma 7: op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(X, op(op(Y, op(op(Z, W), W)), X)), V)))) = op(op(X, op(op(Y, op(op(Z, W), W)), X)), V).
Proof:
op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(X, op(op(Y, op(op(Z, W), W)), X)), V))))
= { by lemma 3 R->L }
op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V))))
= { by lemma 3 R->L }
op(op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V))))
= { by lemma 6 }
op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V)
= { by lemma 3 }
op(op(X, op(op(Y, op(op(Z, W), W)), X)), V)

Lemma 8: op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(W, op(op(Y, op(op(Z, Y), Y)), W))) = op(X, op(op(Y, op(op(Z, Y), Y)), X)).
Proof:
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(W, op(op(Y, op(op(Z, Y), Y)), W)))
= { by lemma 5 R->L }
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))
= { by axiom 2 (lemma_0001) }
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(X, op(op(Y, op(op(Z, Y), Y)), X)))))
= { by lemma 5 R->L }
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))))
= { by lemma 5 R->L }
op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))))
= { by lemma 7 }
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)))
= { by lemma 5 }
op(X, op(op(Y, op(op(Z, Y), Y)), X))

Lemma 9: op(op(X, op(op(Y, X), X)), op(X, op(op(Y, X), X))) = op(X, op(op(Y, X), X)).
Proof:
op(op(X, op(op(Y, X), X)), op(X, op(op(Y, X), X)))
= { by lemma 4 R->L }
op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(Z, op(op(X, op(op(Y, X), X)), Z))))))
= { by lemma 8 }
op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(W, op(op(X, op(op(Y, X), X)), W)))))
= { by lemma 8 }
op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(Z, op(op(X, op(op(Y, X), X)), Z))))
= { by lemma 3 R->L }
op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(X, op(op(Y, X), X)))))
= { by lemma 4 }
op(X, op(op(Y, X), X))

Lemma 10: op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))) = op(op(X, Y), Y).
Proof:
op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y)))
= { by lemma 9 R->L }
op(op(op(X, Y), Y), op(op(Y, op(op(X, Y), Y)), op(Y, op(op(X, Y), Y))))
= { by lemma 9 R->L }
op(op(op(X, Y), Y), op(op(Y, op(op(X, Y), Y)), op(op(Y, op(op(X, Y), Y)), op(Y, op(op(X, Y), Y)))))
= { by axiom 1 (a1) R->L }
op(op(X, Y), Y)

Lemma 11: op(op(op(X, Y), Y), op(op(X, Y), Y)) = op(op(X, Y), Y).
Proof:
op(op(op(X, Y), Y), op(op(X, Y), Y))
= { by lemma 10 R->L }
op(op(op(X, Y), Y), op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))))
= { by lemma 10 R->L }
op(op(op(X, Y), Y), op(op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))), op(Y, op(op(X, Y), Y))))
= { by lemma 6 }
op(op(X, Y), Y)

Lemma 12: op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(V, op(op(Y, op(op(Z, Y), Y)), V))) = op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W).
Proof:
op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(V, op(op(Y, op(op(Z, Y), Y)), V)))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(op(V, op(op(Y, op(op(Z, Y), Y)), V)), op(W, op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(Y, op(op(Z, Y), Y)), V))), W))))
= { by lemma 8 }
op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(op(V, op(op(Y, op(op(Z, Y), Y)), V)), op(W, op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W))))
= { by lemma 7 }
op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W)

Lemma 13: op(op(op(X, op(op(Y, X), X)), Z), op(op(X, op(op(Y, X), X)), W)) = op(op(X, op(op(Y, X), X)), Z).
Proof:
op(op(op(X, op(op(Y, X), X)), Z), op(op(X, op(op(Y, X), X)), W))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W))))))
= { by axiom 2 (lemma_0001) }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(op(op(Y, X), X), op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 11 }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 11 }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 12 R->L }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(X, op(op(Y, X), X)), W))))))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X))))))))))
= { by axiom 1 (a1) }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(Z, op(op(X, op(op(Y, X), X)), Z))))))))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by lemma 8 R->L }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by lemma 8 R->L }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by axiom 2 (lemma_0001) R->L }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))))))
= { by lemma 8 }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 8 }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))))
= { by lemma 12 }
op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W))))
= { by axiom 1 (a1) R->L }
op(op(X, op(op(Y, X), X)), Z)

Goal 1 (history_lemma_0058): op(x2, op(op(x0, op(op(x1, x0), x0)), x2)) = x2.
Proof:
op(x2, op(op(x0, op(op(x1, x0), x0)), x2))
= { by lemma 13 R->L }
op(x2, op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(x0, op(op(x1, x0), x0)), x2)))
= { by lemma 13 R->L }
op(x2, op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(x0, op(op(x1, x0), x0)), x2))))
= { by axiom 1 (a1) R->L }
x2

RESULT: Theorem (the conjecture is true).
"#;

    // Segment 3
    let seg3 = r#"
The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.

Goal 1 (conjecture0): x0 = op(x0, op(x1, op(x2, op(x0, x2)))).
Proof:
x0
= { by axiom 1 (a1) }
op(x0, op(X, op(op(Y, x0), X)))
= { by axiom 1 (a1) }
op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X)))
= { by axiom 1 (a1) }
op(op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X))), op(op(x1, op(x2, op(x0, x2))), op(op(op(X, op(op(Y, x0), X)), op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X)))), op(x1, op(x2, op(x0, x2))))))
= { by axiom 2 (history_lemma_0058) }
op(op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X))), op(x1, op(x2, op(x0, x2))))
= { by axiom 1 (a1) R->L }
op(op(x0, op(X, op(op(Y, x0), X))), op(x1, op(x2, op(x0, x2))))
= { by axiom 1 (a1) R->L }
op(x0, op(x1, op(x2, op(x0, x2))))

RESULT: Theorem (the conjecture is true).
    "#;

    let trimmed = trim_superposition_block(block, &[seg2, seg3]);

    assert!(trimmed.contains("% === Superposition Steps ==="));
    assert!(trimmed.contains("% lemma_0001:"));

    // these must be gone
    assert!(!trimmed.contains("% lemma_0002:"));
    assert!(!trimmed.contains("% lemma_0003:"));
    assert!(!trimmed.contains("% lemma_0004:"));
    assert!(!trimmed.contains("% lemma_0005:"));
    assert!(!trimmed.contains("% lemma_0006:"));
    assert!(!trimmed.contains("% lemma_0007:"));
    assert!(!trimmed.contains("% lemma_0008:"));
    assert_eq!(count_superposition_steps(&trimmed), 1);
}

#[test]
fn proof_uses_lemma() {
    let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

    // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
    let seg1 = r#"
% === Superposition Steps ===
% lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))) | deps: lemma_0001, lemma_0002
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004, lemma_0002
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7)))) | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1)) | deps: lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))), lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2)))))
% lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))) | deps: lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0002
% lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))) | deps: lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))), lemma_0002
% lemma_0017: op(X11,op(X12,op(X11,X12))) = X12 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1))
% lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))) | deps: lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))), lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1)
% lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) | deps: lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))), lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3))))
% lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17) | deps: lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17), lemma_0002
% lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17) | deps: lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17), lemma_0002
% lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17), lemma_0017: op(X11,op(X12,op(X11,X12))) = X12
% history_lemma_0151: op(X17,X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17), lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0)
"#;

    // Segment 3: the final goal proof — still no lemma_0004..0008 usage
    let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (lemma_0022): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).
Axiom 2 (lemma_0011): op(X, X) = op(op(Y, op(X, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
op(x0, x0)
= { by axiom 2 (lemma_0011) }
op(op(x0, op(x0, x0)), x0)
= { by axiom 1 (lemma_0022) }
op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
    // Use trim_proof_parts: block is the "start" vampire block, seg1 is the
    // "root" vampire block, seg3 is sub-proof.
    let (kept_start, kept_hist, kept_root, start_steps, hist_steps, root_steps) = trim_proof_parts(
        Some((block, "vampire", count_superposition_steps(block))),
        None,
        (
            "history_lemma_0151",
            seg1,
            "vampire",
            count_superposition_steps(seg1),
        ),
        Some(seg3),
    );

    // history is None -> empty string + 0 steps
    assert!(kept_hist.trim().is_empty());
    assert_eq!(hist_steps, 0);

    // start exists
    assert!(!kept_start.trim().is_empty());

    // start is vampire-trimmed, so it should NOT be empty
    assert!(!kept_start.trim().is_empty());
    assert!(kept_start.contains("% lemma_0001:"));
    assert!(kept_start.contains("% lemma_0002:"));
    assert!(kept_start.contains("% lemma_0003:"));
    assert!(kept_start.contains("% lemma_0004:"));
    assert!(kept_start.contains("% lemma_0005:"));
    assert!(kept_start.contains("% lemma_0006:"));

    // Root block must keep what the later proof actually uses:
    assert!(kept_root.contains("% lemma_0007:"));
    assert!(kept_root.contains("% lemma_0003:"));
    assert!(kept_root.contains("% lemma_0022:"));
    assert!(kept_root.contains("% lemma_0011:"));
    assert!(!kept_root.contains("% history_lemma_0151:"));

    // Step accounting
    assert_eq!(start_steps, 6);
    assert_eq!(root_steps, count_superposition_steps(&kept_root));
}

#[test]
fn proof_uses_lemma_remove_seg() {
    let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

    // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
    let seg1 = r#"
% === Superposition Steps ===
% lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))) | deps: lemma_0001, lemma_0002
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004, lemma_0002
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7)))) | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1)) | deps: lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))), lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2)))))
% lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))) | deps: lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0002
% lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))) | deps: lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))), lemma_0002
% lemma_0017: op(X11,op(X12,op(X11,X12))) = X12 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1))
% lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))) | deps: lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))), lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1)
% lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) | deps: lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))), lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3))))
% lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17) | deps: lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17), lemma_0002
% lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17) | deps: lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17), lemma_0002
% lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17), lemma_0017: op(X11,op(X12,op(X11,X12))) = X12
% history_lemma_0151: op(X17,X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17), lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0)
"#;

    // Segment 3: the final goal proof — still no lemma_0004..0008 usage
    let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (lemma_0001): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).
Axiom 2 (lemma_0002): op(X, X) = op(op(Y, op(X, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
op(x0, x0)
= { by axiom 2 (lemma_0002) }
op(op(x0, op(x0, x0)), x0)
= { by axiom 1 (lemma_0001) }
op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
    // Use trim_proof_parts: block is the "start" vampire block, seg1 is the
    // "root" vampire block, seg3 is sub-proof.
    let (kept_start, kept_hist, kept_root, start_steps, hist_steps, root_steps) = trim_proof_parts(
        Some((block, "vampire", count_superposition_steps(block))),
        None,
        (
            "history_lemma_0151",
            seg1,
            "vampire",
            count_superposition_steps(seg1),
        ),
        Some(seg3),
    );

    // history is None -> empty string + 0 steps
    assert!(kept_hist.trim().is_empty());
    assert_eq!(hist_steps, 0);

    // start exists -> should not be empty
    assert!(!kept_start.trim().is_empty());

    // start is vampire-trimmed
    assert!(!kept_start.trim().is_empty());
    assert!(kept_start.contains("% lemma_0001:"));
    assert!(kept_start.contains("% lemma_0002:"));
    assert!(!kept_start.contains("% lemma_0003:"));
    assert!(!kept_start.contains("% lemma_0004:"));
    assert!(!kept_start.contains("% lemma_0005:"));
    assert!(!kept_start.contains("% lemma_0006:"));

    // Root block must be empty
    assert!(kept_root.trim().is_empty());

    // Step accounting
    assert_eq!(start_steps, 2);
    assert_eq!(root_steps, 0);
}

#[test]
fn untouched() {
    let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

    // Segment 2: raw Vampire output
    let seg2 = r#"
1. ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0 [input]
2. ! [X0,X1,X2,X3] : op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) [input]
3. ! [X0,X1,X2,X3] : op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 [input]
4. ! [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X1,op(op(X2,X0),X1)),X4))) [input]
6. ! [X7,X8,X9,X10,X11] : op(X9,X10) = op(op(X9,X10),op(op(X11,op(op(X7,op(op(X8,X9),X7)),X11)),op(X10,op(X9,X10)))) [input]
7. ! [X0,X1,X2,X3,X4] : op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))) [input]
8. ! [X0,X1,X2,X3,X4] : op(X2,X4) = op(op(X2,X4),op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(X4,op(X2,X4)))) [input]
9. ! [X12,X13,X14,X15] : op(op(X13,op(op(X14,X13),X13)),X15) = op(op(op(X13,op(op(X14,X13),X13)),X15),op(op(X12,op(op(X13,op(op(X14,X13),X13)),X12)),op(X15,op(op(X13,op(op(X14,X13),X13)),X15)))) [input]
10. ! [X16,X17,X18,X19] : op(X19,op(op(X17,op(op(X18,X17),X17)),X19)) = op(op(X19,op(op(X17,op(op(X18,X17),X17)),X19)),op(X16,op(op(X17,op(op(X18,X17),X17)),X16))) [input]
14. ! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [input]
15. ~! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [negated conjecture 14]
17. ! [X0,X1,X2,X3,X4] : op(X2,X3) = op(op(X2,X3),op(op(X4,op(op(X0,op(op(X1,X2),X0)),X4)),op(X3,op(X2,X3)))) [rectify 6]
18. ! [X0,X1,X2,X3] : op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(op(X0,op(op(X1,op(op(X2,X1),X1)),X0)),op(X3,op(op(X1,op(op(X2,X1),X1)),X3)))) [rectify 9]
19. ! [X0,X1,X2,X3] : op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [rectify 10]
22. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 [ennf transformation 15]
23. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 => sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [choice axiom]
24. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [skolemisation 22,23]
25. op(X0,op(X1,op(op(X2,X0),X1))) = X0 [cnf transformation 1]
26. op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) [cnf transformation 2]
27. op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 [cnf transformation 3]
28. op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X1,op(op(X2,X0),X1)),X4))) [cnf transformation 4]
30. op(X2,X3) = op(op(X2,X3),op(op(X4,op(op(X0,op(op(X1,X2),X0)),X4)),op(X3,op(X2,X3)))) [cnf transformation 17]
31. op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))) [cnf transformation 7]
32. op(X2,X4) = op(op(X2,X4),op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(X4,op(X2,X4)))) [cnf transformation 8]
33. op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(op(X0,op(op(X1,op(op(X2,X1),X1)),X0)),op(X3,op(op(X1,op(op(X2,X1),X1)),X3)))) [cnf transformation 18]
34. op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [cnf transformation 19]
38. $true [cnf transformation 24]
39. op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [backward demodulation 33,34]
42. op(op(X2,X0),X1) = op(op(op(X2,X0),X1),op(op(X3,op(X0,X3)),op(X1,op(op(X2,X0),X1)))) [superposition 27,25]
62. op(X4,op(op(op(X7,op(X6,X7)),op(X4,op(op(X5,X6),X4))),op(op(X5,X6),X4))) = X4 [superposition 27,26]
66. op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) [superposition 27,26]
191. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(op(op(X23,op(X22,X23)),op(X20,op(op(X21,X22),X20))),op(X25,op(op(X26,op(X20,op(op(X21,X22),X20))),X25)))) [superposition 31,26]
224. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(op(op(X74,op(X73,X74)),op(X75,op(op(X76,X73),X75))),op(X72,op(X73,X72)))) [superposition 26,31]
663. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(op(op(X23,op(op(X24,X23),X23)),op(op(op(X24,X23),X23),op(X23,op(op(X24,X23),X23)))),op(X26,op(op(op(X24,X23),X23),X26)))) [superposition 32,39]
684. op(X134,op(op(X131,op(op(X132,X131),X131)),op(X133,X134))) = X134 [superposition 25,39]
748. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(op(X23,op(op(X24,X23),X23)),op(X26,op(op(op(X24,X23),X23),X26)))) [forward demodulation 663,26]
754. op(X3,op(op(op(X1,op(op(X2,X0),X1)),op(X0,op(X1,op(op(X2,X0),X1)))),op(X4,X3))) = X3 [superposition 684,25]
785. op(X0,X2) = op(op(X0,X2),op(X0,op(op(X1,X0),X0))) [superposition 684,26]
847. op(X3,op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,X3))) = X3 [forward demodulation 754,25]
1097. op(op(X8,X6),X6) = op(op(op(X8,X6),X6),op(X6,op(op(X7,X6),X6))) [superposition 684,785]
1100. op(op(X27,X26),X26) = op(op(op(X27,X26),X26),op(X26,op(X26,X26))) [superposition 42,785]
1101. op(X30,op(X28,X30)) = op(op(X30,op(X28,X30)),op(X28,op(X28,X28))) [superposition 31,785]
1102. op(X31,op(op(X31,op(X31,X31)),op(op(X32,X31),X31))) = X31 [superposition 62,785]
1486. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(op(X237,op(op(X238,X239),X237)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))),op(op(X240,op(X237,op(op(X238,X239),X237))),op(X237,op(op(X238,X239),X237)))),op(X237,op(op(X238,X239),X237)))) [superposition 28,1102]
2088. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(op(X21,op(X19,X21)),op(op(X19,op(X19,X19)),op(op(X18,X19),X19)))) [superposition 31,1100]
2136. op(X224,op(op(op(X225,op(op(op(X222,X223),X223),X225)),op(X223,op(X223,X223))),op(X226,X224))) = X224 [superposition 847,1100]
2199. op(X224,op(op(X225,op(op(op(X222,X223),X223),X225)),op(X226,X224))) = X224 [forward demodulation 2136,26]
3790. op(X14,X15) = op(op(X14,X15),op(X12,op(op(op(X13,X14),X14),X12))) [superposition 2199,26]
3911. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(X23,op(op(X24,X23),X23))) [backward demodulation 748,3790]
4003. op(X62,op(X61,X62)) = op(op(X62,op(X61,X62)),op(op(op(X60,X61),X61),op(X61,op(op(X60,X61),X61)))) [superposition 31,3911]
4163. op(X62,op(X61,X62)) = op(op(X62,op(X61,X62)),op(op(X60,X61),X61)) [forward demodulation 4003,1097]
4202. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(op(X21,op(X19,X21)),op(X19,op(X19,X19)))) [backward demodulation 2088,4163]
4239. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(X237,op(op(X238,X239),X237)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))),op(X237,op(op(X238,X239),X237)))) [backward demodulation 1486,4163]
4330. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(X21,op(X19,X21))) [forward demodulation 4202,1101]
4380. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237))),op(X237,op(op(X238,X239),X237)))) [forward demodulation 4239,4330]
4381. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))) [forward demodulation 4380,4330]
4382. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(X237,op(op(X238,X239),X237))) [forward demodulation 4381,4330]
4464. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(op(X23,op(X22,X23)),op(X25,op(op(X26,op(X20,op(op(X21,X22),X20))),X25)))) [backward demodulation 191,4382]
4478. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(op(X74,op(X73,X74)),op(X72,op(X73,X72)))) [backward demodulation 224,4382]
4906. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(X74,op(X73,X74))) [forward demodulation 4478,4330]
4914. op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22))) [backward demodulation 66,4906]
4948. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(X23,op(X22,X23))) [backward demodulation 4464,4914]
4950. op(X2,X3) = op(op(X2,X3),op(X4,op(op(X0,op(op(X1,X2),X0)),X4))) [backward demodulation 30,4948]
5701. op(X17,X19) = op(op(X17,X19),op(op(X18,op(X17,X18)),op(X15,op(op(X16,X17),X15)))) [superposition 4950,26]
5829. op(X17,X19) = op(op(X17,X19),op(X18,op(X17,X18))) [forward demodulation 5701,4382]
5856. op(X0,op(X3,op(X0,X3))) = X0 [superposition 5829,25]
6572. op(X12,op(X11,X12)) = X12 [superposition 5856,5829]
6656. op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),X3) [backward demodulation 26,6572]
8341. ! [X0,X1,X2] : X0 = op(X0,op(X1,X2)) [backward demodulation 38,6572]
8342. op(X1,X3) = X1 [forward demodulation 6656,6572]
8351. ! [X0,X1,X2] : X0 = op(X0,op(X1,op(X2,op(X0,X2)))) [subsumption resolution 8341,8342]
"#;

    // Segment 3: the final goal proof — still no lemma_0004..0008 usage
    let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0151): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
op(x0, x0)
= { by axiom 1 (history_lemma_0151) }
op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
    // Use trim_proof_parts: block is the "start" vampire block, seg1 is the
    // "root" vampire block, seg3 is sub-proof.
    let (kept_start, kept_hist, kept_root, _start_steps, hist_steps, root_steps) = trim_proof_parts(
        Some((block, "vampire", count_superposition_steps(block))),
        None,
        (
            "history_lemma_0151",
            seg2,
            "vampire",
            proof_length_vampire(seg2),
        ),
        Some(seg3),
    );

    // history is None -> empty string + 0 steps
    assert!(kept_hist.trim().is_empty());
    assert_eq!(hist_steps, 0);

    // start exists -> should not be empty
    assert!(!kept_start.trim().is_empty());

    // start is vampire-trimmed
    assert!(!kept_start.trim().is_empty());
    assert!(kept_start.contains("% lemma_0001:"));
    assert!(kept_start.contains("% lemma_0002:"));
    assert!(kept_start.contains("% lemma_0003:"));
    assert!(kept_start.contains("% lemma_0004:"));
    assert!(kept_start.contains("% lemma_0005:"));
    assert!(kept_start.contains("% lemma_0006:"));

    // Root block must be empty
    assert!(!kept_root.trim().is_empty());

    // Step accounting
    assert_eq!(root_steps, 44);
    assert_eq!(proof_length_twee(seg3), 1);
}

#[test]
fn stop_the_bleed_sub_freezes_all_trimming() {
    // This test checks the "SUB bleed => freeze everything" rule.
    //
    // Without the SUB check, `trim_superposition_block` would likely drop the
    // entire root block because the SUB does not reference any lemma_* by
    // name (only a_6:), so "needed" becomes empty.
    //
    // With the SUB check, we should freeze at Root, and keep the root block
    // untrimmed.

    let start = r#"
% === Superposition Steps ===
% lemma_0001: foo | deps: a_1: blah
"#;

    let root = r#"
% === Superposition Steps ===
% lemma_0002: bar | deps: a_1: blah
% lemma_0006: baz | deps: a_6: ! [X0,X1,X2] : op(X0,op(op(X0,X1),X2)) = op(X0,op(op(X0,X0),X0)), lemma_0002
"#;

    // SUB contains unresolved a_6: but doesn't cite lemma_0006 by name.
    let sub = r#"
% === Conjecture Proof ===
... uses a_6: ! [X0,X1,X2] : op(X0,op(op(X0,X1),X2)) = op(X0,op(op(X0,X0),X0)) ...
"#;

    let (kept_start, kept_history, kept_root, start_steps, hist_steps, root_steps) =
        trim_proof_parts(
            Some((start, "vampire", 1)),
            None,
            ("lemma_9999", root, "vampire", 2),
            Some(sub),
        );

    // History is absent.
    assert!(kept_history.is_empty());
    assert_eq!(hist_steps, 0);

    // Because SUB has a_6:, we should freeze trimming and keep the root block
    // intact.
    assert!(
        kept_root.contains("% lemma_0006:"),
        "expected root to be kept untrimmed due to a_6 in sub, but lemma_0006 was removed.\nkept_root:\n{}",
        kept_root
    );

    // In freeze mode, our code returns the input root_steps_in (not
    // recomputed).
    assert_eq!(root_steps, 2);

    // Start isn't necessarily trimmed/kept in any particular way for this
    // test, but it should still be present (freeze at Root implies
    // start/history/root are not trimmed).
    assert!(
        !kept_start.trim().is_empty(),
        "expected start to be kept (freeze), but it was empty"
    );
    assert_eq!(start_steps, 1);
}

#[test]
fn stop_the_bleed_but_not_kept() {
    // Root contains bleed `a_6:` but root is NOT needed (not referenced by
    // sub), so kept_root should be empty after trimming. Because root is not
    // kept, we must NOT freeze; therefore START trimming should still happen.
    //
    // We make START a vampire superposition block containing lemma_7777,
    // which is not referenced later, so it should trim to empty iff we did
    // not freeze.

    let start = r#"
% === Superposition Steps ===
% lemma_7777: s | deps: a_1: ok
"#;

    let history = r#"
% === Superposition Steps ===
% history_lemma_0003: h | deps: a_1: ok
"#;

    // Root has bleed `a_6:` but will not be referenced by sub, so should trim
    // away.
    let root = r#"
% === Superposition Steps ===
% lemma_0006: baz | deps: a_6: ! [X0] : p(X0), history_lemma_0003
"#;

    // SUB references history_lemma_0003, NOT lemma_0006, so root isn't
    // needed.
    let sub = r#"
% === Conjecture Proof ===
... = { by lemma 1 (history_lemma_0003) } ...
"#;

    let (kept_start, kept_history, kept_root, start_steps, hist_steps, root_steps) =
        trim_proof_parts(
            Some((start, "vampire", 999)), // steps_in doesn't matter; vampire steps are recomputed when trimmed
            Some(("history_lemma_0003", history, "vampire", 1)),
            ("lemma_9999", root, "vampire", 123),
            Some(sub),
        );

    // Root should be trimmed to empty because sub doesn't reference
    // lemma_0006
    assert!(
        kept_root.trim().is_empty(),
        "expected root to be trimmed to empty (not needed), but got:\n{}",
        kept_root
    );
    assert_eq!(
        root_steps, 0,
        "trimmed vampire root should count as 0 steps"
    );

    // History is needed by sub and should remain
    assert!(
        kept_history.contains("history_lemma_0003"),
        "expected history to be kept, but got:\n{}",
        kept_history
    );
    assert!(hist_steps > 0);

    // Critical: since root was not kept, we should NOT freeze; therefore
    // START should be trimmed normally and dropped (empty).
    assert!(
        kept_start.trim().is_empty(),
        "expected start to be trimmed away (not referenced) and not kept due to freeze, but got:\n{}",
        kept_start
    );
    assert_eq!(
        start_steps, 0,
        "trimmed vampire start should count as 0 steps"
    );
}
