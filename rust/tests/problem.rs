use krympa::problem::cnf_to_fof;

#[test]
fn a_fof_problem_is_left_alone() {
    let problem =
        "fof(a1, axiom, ! [X] : op(X,X) = X).\nfof(goal, conjecture, ! [X] : X = op(X,X)).\n";
    assert_eq!(cnf_to_fof(problem), Ok(None));
}

#[test]
fn unit_clauses_become_quantified_equations() {
    let problem = "\
% a problem in the style of the TPTP library
cnf(left_identity, axiom,
    ( multiply(identity,X) = X ) ).
cnf(associativity, axiom, multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).
cnf(prove_this, negated_conjecture, multiply(a,identity) != a ).
";
    let expected = "\
fof(left_identity, axiom, ! [X] : multiply(identity,X) = X).
fof(associativity, axiom, ! [X, Y, Z] : multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z))).
fof(prove_this, conjecture, ! [X0] : multiply(X0,identity) = X0).
";
    assert_eq!(cnf_to_fof(problem), Ok(Some(expected.to_string())));
}

#[test]
fn only_constants_unknown_to_the_axioms_become_variables() {
    let problem = "\
cnf(a1, axiom, f(X,e) = X).
cnf(goal, negated_conjecture, f(f(a,b),e) != f(a,b)).
";
    let translated = cnf_to_fof(problem).unwrap().unwrap();
    assert!(translated.contains("fof(goal, conjecture, ! [X0, X1] : f(f(X0,X1),e) = f(X0,X1))."));
}

#[test]
fn what_is_not_an_equational_problem_is_rejected() {
    assert!(cnf_to_fof("cnf(c, axiom, p(X) | X = a).").is_err());
    assert!(cnf_to_fof("cnf(c, axiom, f(X) != X).").is_err());
    assert!(cnf_to_fof("cnf(c, negated_conjecture, f(X) != a).").is_err());
    assert!(cnf_to_fof("include('Axioms/GRP004-0.ax').\ncnf(c, axiom, a = b).").is_err());
    let two_goals = "cnf(a, axiom, f(X) = X).\ncnf(g1, negated_conjecture, a != b).\ncnf(g2, negated_conjecture, c != d).";
    assert!(cnf_to_fof(two_goals).is_err());
}
