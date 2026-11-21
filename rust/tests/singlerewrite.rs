use krympa::refine::is_single_rewrite_refutation;

// Vampire 5 output for: one axiom, goal reachable by one rewrite plus an
// instance of that axiom (formulas shortened).
const ONE_REWRITE: &str = "\
% SZS status Theorem for shortcut
1. ! [X0,X1] : op(X0,X1) = op(op(X0,X1),X0) [input(axiom)]
2. ! [X0,X1] : op(op(op(X0,X1),X0),op(X0,X1)) = op(X0,X1) [input(conjecture)]
3. ~! [X0,X1] : op(op(op(X0,X1),X0),op(X0,X1)) = op(X0,X1) [negated conjecture 2]
4. ? [X0,X1] : op(op(op(X0,X1),X0),op(X0,X1)) != op(X0,X1) [ennf transformation 3]
5. ? [X0,X1] : op(X0,X1) != op(op(X0,X1),X0) => sK0 != sK1 [skolem symbol introduction]
6. op(op(op(sK0,sK1),sK0),op(sK0,sK1)) != op(sK0,sK1) [skolemisation 4,5]
7. op(X0,X1) = op(op(X0,X1),X0) [cnf transformation 1]
8. op(op(op(sK0,sK1),sK0),op(sK0,sK1)) != op(sK0,sK1) [cnf transformation 6]
14. op(op(sK0,sK1),op(sK0,sK1)) != op(sK0,sK1) [superposition 8,7]
15. $false [forward subsumption resolution 14,7]
";

#[test]
fn one_rewrite_then_instance_is_accepted() {
    assert!(is_single_rewrite_refutation(ONE_REWRITE));
}

#[test]
fn old_vampire_tags_are_accepted() {
    let old = ONE_REWRITE
        .replace("[input(axiom)]", "[input]")
        .replace("[input(conjecture)]", "[input]")
        .replace("[skolem symbol introduction]", "[choice axiom]");
    assert!(is_single_rewrite_refutation(&old));
}

#[test]
fn two_rewrites_are_rejected() {
    let two = ONE_REWRITE.replace(
        "15. $false [forward subsumption resolution 14,7]",
        "15. op(sK0,sK1) != op(sK0,sK1) [forward demodulation 14,7]\n\
         16. $false [trivial inequality removal 15]",
    );
    assert!(!is_single_rewrite_refutation(&two));
}

#[test]
fn no_rewrite_is_rejected() {
    let none = ONE_REWRITE.replace("[superposition 8,7]", "[resolution 8,7]");
    assert!(!is_single_rewrite_refutation(&none));
}

#[test]
fn unknown_inference_rule_is_rejected() {
    let unknown = ONE_REWRITE.replace(
        "[forward subsumption resolution 14,7]",
        "[inner rewriting 14,7]",
    );
    assert!(!is_single_rewrite_refutation(&unknown));
}
