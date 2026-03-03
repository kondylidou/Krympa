use krympa::superpose::extract_superposition_steps;
use krympa::superpose::parse_vampire_proof;
use krympa::superpose::prepend_superposition_steps;
use krympa::superpose::VampStep;
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

fn write_tmp(content: &str) -> String {
    let mut path: PathBuf = std::env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    path.push(format!("krympa_vamp_test_{}.txt", nanos));
    fs::write(&path, content).unwrap();
    path.to_string_lossy().to_string()
}

#[test]
fn test_parse_vampire_proof_collects_inputs_and_steps() {
    // Minimal Vampire-ish format:
    // - inputs stored
    // - relevant set contains superposition/resolution steps
    // - deps are vampire numbers
    let proof = r#"
1. p(a) [input]
2. q(a) [input]
3. r(a) [superposition 1,2]
4. s(a) [resolution 3,2]
"#;

    let file = write_tmp(proof);
    let (all_steps, inputs, relevant) = parse_vampire_proof(&file).unwrap();

    // Inputs collected
    assert_eq!(inputs.get(&1).unwrap(), "p(a)");
    assert_eq!(inputs.get(&2).unwrap(), "q(a)");

    // Steps exist
    assert_eq!(all_steps.get(&3).unwrap().formula, "r(a)");
    assert_eq!(all_steps.get(&4).unwrap().formula, "s(a)");

    // Deps are vampire numbers
    assert_eq!(all_steps.get(&3).unwrap().deps, vec![1, 2]);
    assert_eq!(all_steps.get(&4).unwrap().deps, vec![3, 2]);

    // Relevant contains 3 and 4
    assert!(relevant.contains(&3));
    assert!(relevant.contains(&4));
}

#[test]
fn test_prepend_resolves_input_deps_to_axiom_names() {
    // Build a tiny proof graph manually (all_steps)
    let mut all_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    all_steps.insert(
        1,
        VampStep {
            formula: "(op(X0,X1) = op(op(X1,op(X0,X2)),X0))".to_string(),
            deps: vec![],
            is_input: true,
        },
    );
    all_steps.insert(
        2,
        VampStep {
            formula: "op(X1,op(X0,op(op(X1,X2),X3))) = op(op(op(X1,X2),X0),X1)".to_string(),
            deps: vec![],
            is_input: true,
        },
    );
    all_steps.insert(
        3,
        VampStep {
            formula: "r(a)".to_string(),
            deps: vec![1, 2],
            is_input: false,
        },
    );
    all_steps.insert(
        4,
        VampStep {
            formula: "s(a)".to_string(),
            deps: vec![3, 2],
            is_input: false,
        },
    );

    // relevant steps map (subset of all_steps)
    let mut relevant_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    relevant_steps.insert(3, all_steps.get(&3).unwrap().clone());
    relevant_steps.insert(4, all_steps.get(&4).unwrap().clone());

    // input_formulas as produced by parse
    let mut input_formulas: BTreeMap<usize, String> = BTreeMap::new();
    input_formulas.insert(1, all_steps.get(&1).unwrap().formula.clone());
    input_formulas.insert(2, all_steps.get(&2).unwrap().formula.clone());

    // Axioms available in the problem (name, formula)
    let axioms: Vec<(String, String)> = vec![
        (
            "a1".to_string(),
            "(op(X0,X1) = op(op(X1,op(X0,X2)),X0))".to_string(),
        ),
        (
            "a2".to_string(),
            "op(X1,op(X0,op(op(X1,X2),X3))) = op(op(op(X1,X2),X0),X1)".to_string(),
        ),
    ];

    let (annotated, _renaming) =
        prepend_superposition_steps(&axioms, &relevant_steps, &input_formulas, &all_steps);

    // Step 3 deps should resolve to a1 and a2 somewhere on the r(a) line
    assert!(
        annotated
            .lines()
            .any(|l| l.contains(": r(a) | deps:") && l.contains("a1") && l.contains("a2")),
        "annotated proof did not contain resolved input deps. got:\n{annotated}"
    );

    // Step 4 should contain dependency on a lemma (for step 3) and also a2
    assert!(
        annotated
            .lines()
            .any(|l| l.contains(": s(a) | deps:") && l.contains("lemma_") && l.contains("a2")),
        "second step did not contain lemma dep + resolved input dep a2. got:\n{annotated}"
    );
}

#[test]
fn test_backtracks_nonrelevant_deps_to_inputs() {
    // This is the bug you described:
    // 15 depends on 8 depends on 5(input). 18 depends on 15 and 17(input).
    // We want deps to resolve to inputs 5 and 17 (not "a_15").
    let proof = r#"
5. A [input]
8. B [rectify 5]
15. C [cnf transformation 8]
17. D [input]
18. E [backward demodulation 15,17]
"#;

    let file = write_tmp(proof);
    let (all_steps, input_formulas, relevant_set) = parse_vampire_proof(&file).unwrap();

    // relevant should include 18 (demodulation) but not necessarily 8/15
    assert!(relevant_set.contains(&18));

    // Build relevant_steps map with just step 18
    let mut relevant_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    relevant_steps.insert(18, all_steps.get(&18).unwrap().clone());

    // no axioms matching: just check it prints a_5 or a_17, NOT a_15
    let axioms: Vec<(String, String)> = vec![];

    let (annotated, _renaming) =
        prepend_superposition_steps(&axioms, &relevant_steps, &input_formulas, &all_steps);

    // Must mention 5 and 17 in deps (as a_5 / a_17 or with formulas)
    assert!(
        annotated.contains("a_5") || annotated.contains("a_5:"),
        "expected deps to include input 5. got:\n{annotated}"
    );
    assert!(
        annotated.contains("a_17") || annotated.contains("a_17:"),
        "expected deps to include input 17. got:\n{annotated}"
    );

    // Must NOT treat 15 as an input dependency
    assert!(
        !annotated.contains("a_15") && !annotated.contains("a_15:"),
        "deps incorrectly included a_15 instead of backtracking to input 5. got:\n{annotated}"
    );
}

#[test]
fn test_real_vampire_uses_axiom_names_for_backtracked_inputs() {
    let proof = r#"
1. ! [X0,X1,X2] : op(X0,X1) = op(op(X1,op(X0,X2)),X0) [input]
2. ! [X0,X1,X2] : op(X0,X1) = op(op(X1,op(X2,X0)),X0) [input]
3. ~! [X0,X1,X2] : op(X0,X1) = op(op(X1,op(X2,X0)),X0) [negated conjecture 2]
5. ! [X4,X5,X6,X7] : op(X4,X7) = op(op(X7,op(op(op(X4,X6),X5),X4)),X4) [input]
7. ! [X0,X1,X2] : op(X1,X2) = op(op(X0,X1),X2) [input]
8. ! [X0,X1,X2,X3] : op(X0,X3) = op(op(X3,op(op(op(X0,X2),X1),X0)),X0) [rectify 5]
9. ? [X0,X1,X2] : op(X0,X1) != op(op(X1,op(X2,X0)),X0) [ennf transformation 3]
10. ? [X0,X1,X2] : op(X0,X1) != op(op(X1,op(X2,X0)),X0) => op(sK0,sK1) != op(op(sK1,op(sK2,sK0)),sK0) [choice axiom]
11. op(sK0,sK1) != op(op(sK1,op(sK2,sK0)),sK0) [skolemisation 9,10]
12. op(X0,X1) = op(op(X1,op(X0,X2)),X0) [cnf transformation 1]
13. $true [cnf transformation 11]
15. op(X0,X3) = op(op(X3,op(op(op(X0,X2),X1),X0)),X0) [cnf transformation 8]
17. op(X1,X2) = op(op(X0,X1),X2) [cnf transformation 7]
18. op(X0,X3) = op(op(X3,op(op(X2,X1),X0)),X0) [backward demodulation 15,17]
20. op(X0,X3) = op(op(X3,op(X1,X0)),X0) [forward demodulation 18,17]
"#;

    let file = write_tmp(proof);
    let (all_steps, input_formulas, _relevant_set) = parse_vampire_proof(&file).unwrap();

    // We want the same “superposition steps” you showed in your output:
    // vamp 18 and vamp 20 are relevant demodulation steps.
    let mut relevant_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    relevant_steps.insert(18, all_steps.get(&18).unwrap().clone());
    relevant_steps.insert(20, all_steps.get(&20).unwrap().clone());

    // Crucial part:
    // Provide axioms with NAMES you want, and FORMULAS that exactly match the Vampire INPUTS.
    // Then prepend_superposition_steps will resolve to those names.
    let axioms: Vec<(String, String)> = vec![
        (
            "lemma_0002".to_string(),
            input_formulas.get(&5).unwrap().clone(), // input step 5
        ),
        (
            "small_step_lemma_0139".to_string(),
            input_formulas.get(&7).unwrap().clone(), // input step 7
        ),
    ];

    let (annotated, _renaming) =
        prepend_superposition_steps(&axioms, &relevant_steps, &input_formulas, &all_steps);

    // Step 18 should backtrack 15 -> 8 -> 5 and 17 -> 7, then resolve to the NAMES above
    assert!(
        annotated.lines().any(|l| {
            l.contains("op(X0,X3) = op(op(X3,op(op(X2,X1),X0)),X0)")
                && l.contains("lemma_0002")
                && l.contains("small_step_lemma_0139")
        }),
        "expected step 18 deps to resolve to lemma_0002 and small_step_lemma_0139. got:\n{annotated}"
    );

    // Must NOT show intermediate non-input deps (15,17) as inputs
    assert!(
        !annotated.contains("a_15") && !annotated.contains("a_17"),
        "should not mention a_15 or a_17 if backtracking works. got:\n{annotated}"
    );

    // Also should not fall back to raw input ids if names resolved
    assert!(
        !annotated.contains("a_5") && !annotated.contains("a_7"),
        "should resolve to named axioms, not a_5/a_7. got:\n{annotated}"
    );

    // Step 20 depends on step 18 + (17 -> 7), so it should contain a lemma_... and small_step_lemma_0139
    assert!(
        annotated.lines().any(|l| {
            l.contains("op(X0,X3) = op(op(X3,op(X1,X0)),X0)")
                && l.contains("lemma_") // dependency on the renamed step 18
                && l.contains("small_step_lemma_0139")
                && !l.contains("a_17")
        }),
        "expected step 20 deps to include lemma_* and small_step_lemma_0139 (not a_17). got:\n{annotated}"
    );
}

#[test]
fn test_extract_superposition_steps_on_negated_conjecture_chain() {
    let proof = r#"
1. ! [X0,X1,X2,X3,X4] : op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))) [input]
2. ! [X0,X1,X2,X3,X4,X5,X6,X7] : op(op(X6,op(op(X7,X2),X6)),X2) = op(op(op(X6,op(op(X7,X2),X6)),X2),op(op(op(X3,op(op(X1,X2),X3)),op(X4,op(op(X5,op(X1,X2)),X4))),op(X0,op(op(X1,X2),X0)))) [input]
3. ! [X0,X1,X2,X3] : op(X2,op(X1,X2)) = op(op(X2,op(X1,X2)),op(X3,op(op(X0,X1),X3))) [input]
4. ! [X0,X1,X2,X3,X4,X5] : op(op(X4,op(op(X5,X2),X4)),X2) = op(op(op(X4,op(op(X5,X2),X4)),X2),op(op(X3,op(op(X1,X2),X3)),op(X0,op(op(X1,X2),X0)))) [input]
5. ~! [X0,X1,X2,X3,X4,X5] : op(op(X4,op(op(X5,X2),X4)),X2) = op(op(op(X4,op(op(X5,X2),X4)),X2),op(op(X3,op(op(X1,X2),X3)),op(X0,op(op(X1,X2),X0)))) [negated conjecture 4]
6. ? [X0,X1,X2,X3,X4,X5] : op(op(X4,op(op(X5,X2),X4)),X2) != op(op(op(X4,op(op(X5,X2),X4)),X2),op(op(X3,op(op(X1,X2),X3)),op(X0,op(op(X1,X2),X0)))) [ennf transformation 5]
7. ? [X0,X1,X2,X3,X4,X5] : op(op(X4,op(op(X5,X2),X4)),X2) != op(op(op(X4,op(op(X5,X2),X4)),X2),op(op(X3,op(op(X1,X2),X3)),op(X0,op(op(X1,X2),X0)))) => op(op(sK4,op(op(sK5,sK2),sK4)),sK2) != op(op(op(sK4,op(op(sK5,sK2),sK4)),sK2),op(op(sK3,op(op(sK1,sK2),sK3)),op(sK0,op(op(sK1,sK2),sK0)))) [choice axiom]
8. op(op(sK4,op(op(sK5,sK2),sK4)),sK2) != op(op(op(sK4,op(op(sK5,sK2),sK4)),sK2),op(op(sK3,op(op(sK1,sK2),sK3)),op(sK0,op(op(sK1,sK2),sK0)))) [skolemisation 6,7]
9. ( ! [X2,X3,X0,X1,X4] : (op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))))) [cnf transformation 1]
10. ( ! [X2,X3,X0,X1,X6,X7,X4,X5] : (op(op(X6,op(op(X7,X2),X6)),X2) = op(op(op(X6,op(op(X7,X2),X6)),X2),op(op(op(X3,op(op(X1,X2),X3)),op(X4,op(op(X5,op(X1,X2)),X4))),op(X0,op(op(X1,X2),X0)))))) [cnf transformation 2]
11. ( ! [X2,X3,X0,X1] : (op(X2,op(X1,X2)) = op(op(X2,op(X1,X2)),op(X3,op(op(X0,X1),X3))))) [cnf transformation 3]
12. op(op(sK4,op(op(sK5,sK2),sK4)),sK2) != op(op(op(sK4,op(op(sK5,sK2),sK4)),sK2),op(op(sK3,op(op(sK1,sK2),sK3)),op(sK0,op(op(sK1,sK2),sK0)))) [cnf transformation 8]
13. ! [X0,X1,X2,X3,X4] : (op(op(X0,op(X1,X0)),op(op(X2,op(X1,X2)),op(X3,op(op(X4,X1),X3)))) = op(X0,op(X1,X0))) [cnf transformation 9]
14. ! [X0,X1,X2,X3,X4,X5,X6,X7] : (op(op(op(X0,op(op(X1,X2),X0)),X2),op(op(op(X3,op(op(X4,X2),X3)),op(X5,op(op(X6,op(X4,X2)),X5))),op(X7,op(op(X4,X2),X7)))) = op(op(X0,op(op(X1,X2),X0)),X2)) [cnf transformation 10]
15. ! [X0,X1,X2,X3] : (op(op(X0,op(X1,X0)),op(X2,op(op(X3,X1),X2))) = op(X0,op(X1,X0))) [cnf transformation 11]
16. $true [cnf transformation 12]
17. ! [X0,X1,X2] : (op(op(X0,op(X1,X0)),op(X2,op(X1,X2))) = op(X0,op(X1,X0))) [demodulation 13,15]
18. ! [X0,X1,X2,X3,X4] : op(op(op(X0,op(op(X1,X2),X0)),X2),op(X3,op(op(X4,X2),X3))) = op(op(X0,op(op(X1,X2),X0)),X2) [demodulation 16,17]
19. ! [X0,X1,X2,X3,X4] : (op(op(op(X0,op(op(X1,X2),X0)),X2),op(X3,op(op(X4,X2),X3))) = op(op(X0,op(op(X1,X2),X0)),X2)) [demodulation 14,15,17]
20. ! [X0,X1,X2,X3,X4,X5] : op(op(op(X0,op(op(X1,X2),X0)),X2),op(op(X3,op(op(X4,X2),X3)),op(X5,op(op(X4,X2),X5)))) = op(op(X0,op(op(X1,X2),X0)),X2) [backward subsumption resolution 18,19]
"#;

    let file = write_tmp(proof);
    let (all_steps_parsed, _, _) = parse_vampire_proof(&file).unwrap();
    let target_formula = all_steps_parsed
        .get(&20)
        .expect("missing step 20 in parsed proof")
        .formula
        .clone();

    let (relevant_steps, input_formulas, _all_steps) =
        extract_superposition_steps(&file, &target_formula)
            .expect("expected to extract relevant superposition chain");

    // Only relevant inference chain should be kept.
    assert!(relevant_steps.contains_key(&20));
    assert!(relevant_steps.contains_key(&19));
    assert!(relevant_steps.contains_key(&18));
    assert!(relevant_steps.contains_key(&17));
    assert_eq!(relevant_steps.len(), 4);

    // Inputs are still tracked from the full proof.
    assert!(input_formulas.contains_key(&1));
    assert!(input_formulas.contains_key(&2));
    assert!(input_formulas.contains_key(&3));
    assert!(input_formulas.contains_key(&4));
}
