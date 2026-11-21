use krympa::bench_run::{generate_problems, lean_to_tptp};
use std::fs;

#[test]
fn lean_equations_become_tptp() {
    assert_eq!(
        lean_to_tptp("x = y ◇ (x ◇ z)"),
        (
            "(X0 = op(X1,op(X0,X2)))".to_string(),
            vec!["X0".to_string(), "X1".to_string(), "X2".to_string()]
        )
    );
    assert_eq!(
        lean_to_tptp("(x ◇ x) ◇ y = ((y ◇ x))").0,
        "(op(op(X0,X0),X1) = op(X1,X0))"
    );
}

#[test]
fn a_benchmark_file_becomes_one_problem_per_theorem() {
    let dir = std::env::temp_dir().join(format!("krympa_bench_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("Equations")).unwrap();
    fs::write(
        dir.join("Equations/Eqns1_999.lean"),
        "-- equation 1 := x = x\nequation 3 := x = x ◇ x\nequation 8 := x = x ◇\n  (y ◇ x)\n",
    )
    .unwrap();
    fs::write(
        dir.join("Proofs7.lean"),
        "theorem Equation3_implies_Equation8 (G : Type*) := by\ntheorem Equation3_implies_Equation1 := by\n",
    )
    .unwrap();

    // equation 1 is commented out, so its theorem is skipped
    assert_eq!(generate_problems(&dir.join("Proofs7.lean")), Ok((1, 1)));
    let problem = fs::read_to_string(dir.join("input7/Equation3_implies_Equation8.p")).unwrap();
    assert_eq!(
        problem,
        "fof(a1, axiom,\n    ! [X0, X1] :\n        (X0 = op(X0,X0))\n).\n\n\
         fof(conjecture0, conjecture,\n    ! [X0, X1] :\n        (X0 = op(X0,op(X1,X0)))\n).\n"
    );
    fs::remove_dir_all(&dir).unwrap();
}
