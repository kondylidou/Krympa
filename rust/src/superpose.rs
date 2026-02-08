use crate::alpha_match::formulas_match;
use crate::dag::load_dag;
use crate::utils::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

/// A single Vampire step (keyed by Vampire index).
#[derive(Debug, Clone)]
pub struct VampStep {
    pub formula: String,
    pub deps: Vec<usize>, // Vampire numbers
    pub is_input: bool,
}

/// Parse Vampire proof:
/// - returns all steps keyed by Vampire number
/// - returns input clauses (Vampire-number -> formula)
/// - returns relevant proof steps as a set of Vampire numbers (superposition/demodulation/...)
pub fn parse_vampire_proof(
    file_path: &str,
) -> Result<
    (
        BTreeMap<usize, VampStep>, // all steps (vamp -> step)
        BTreeMap<usize, String>,   // input_formulas (vamp -> formula)
        BTreeSet<usize>,           // relevant vamp indices
    ),
    String,
> {
    let content = fs::read_to_string(file_path).map_err(|e| e.to_string())?;

    let mut all_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    let mut input_formulas: BTreeMap<usize, String> = BTreeMap::new();
    let mut relevant: BTreeSet<usize> = BTreeSet::new();

    // keywords indicating relevant proof steps
    let proof_keywords = ["demodulation", "superposition", "resolution"];

    for line in content.lines() {
        let line_trimmed = line.trim();
        if line_trimmed.is_empty() {
            continue;
        }

        // split using the last '[ ... ]' which is the inference tag
        let (main_part, tag_part) = match line_trimmed.rfind('[') {
            Some(i) => (
                line_trimmed[..i].trim(),
                line_trimmed[i + 1..].trim_end_matches(']').trim(),
            ),
            None => continue,
        };

        // extract Vampire number if present (from main_part)
        let vamp_num: usize = match main_part
            .split('.')
            .next()
            .and_then(|s| s.trim().parse::<usize>().ok())
        {
            Some(n) => n,
            None => continue,
        };

        // formula = main_part with leading "N." stripped
        let mut formula = main_part.to_string();
        if let Some(pos) = formula.find('.') {
            if formula[..pos].trim().parse::<usize>().is_ok() {
                formula = formula[pos + 1..].trim().to_string();
            }
        }

        // deps: numbers in tag_part
        let deps: Vec<usize> = tag_part
            .split(|c| c == ',' || c == ' ')
            .filter_map(|s| s.trim().parse::<usize>().ok())
            .collect();

        let is_input = tag_part.contains("input");

        if is_input {
            input_formulas.insert(vamp_num, formula.clone());
        }

        if proof_keywords.iter().any(|k| tag_part.contains(k)) {
            relevant.insert(vamp_num);
        }

        all_steps.insert(
            vamp_num,
            VampStep {
                formula,
                deps,
                is_input,
            },
        );
    }

    Ok((all_steps, input_formulas, relevant))
}

/// Expand an arbitrary Vampire step number to the set of INPUT Vampire step numbers
/// by chasing deps through the FULL proof graph.
fn expand_to_inputs(
    start: usize,
    all_steps: &BTreeMap<usize, VampStep>,
    memo: &mut BTreeMap<usize, BTreeSet<usize>>,
    visiting: &mut BTreeSet<usize>,
) -> BTreeSet<usize> {
    if let Some(cached) = memo.get(&start) {
        return cached.clone();
    }
    if visiting.contains(&start) {
        return BTreeSet::new(); // cycle guard
    }
    visiting.insert(start);

    let mut out = BTreeSet::new();
    match all_steps.get(&start) {
        Some(step) if step.is_input => {
            out.insert(start);
        }
        Some(step) => {
            // not input: only recurse; if no deps => contributes no inputs
            for &d in &step.deps {
                out.extend(expand_to_inputs(d, all_steps, memo, visiting));
            }
        }
        None => {
            // unknown node => contributes no inputs
        }
    }

    visiting.remove(&start);
    memo.insert(start, out.clone());
    out
}

/// Collect all Vampire-step dependencies (transitively) within the FULL proof graph.
pub fn gather_all_vamp_dependencies(
    start: usize,
    all_steps: &BTreeMap<usize, VampStep>,
    collected: &mut BTreeSet<usize>,
) {
    if collected.contains(&start) {
        return;
    }
    collected.insert(start);

    if let Some(step) = all_steps.get(&start) {
        for &d in &step.deps {
            gather_all_vamp_dependencies(d, all_steps, collected);
        }
    }
}

/// Extract nth (history) lemma and matching Vampire steps.
///
/// Returns:
/// - dependency lemma names (from DAG)
/// - relevant Vampire steps (keyed by Vampire number)
/// - proved_history flag
/// - input_formulas (vamp->formula)
/// - full proof map (vamp->VampStep)
pub fn superposition_steps(
    dag: &str,
    vampire_file: &str,
    lemmas_dir: &str,
    lemma: &str,
) -> Option<(
    Vec<String>,
    BTreeMap<usize, VampStep>, // relevant steps as vampire-indexed map
    bool,
    BTreeMap<usize, String>,   // input_formulas
    BTreeMap<usize, VampStep>, // all_steps
)> {
    // load the DAG from a file. This DAG maps each lemma to its children.
    let dag = load_dag(&dag);

    let (all_steps, input_formulas, relevant_set) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            eprintln!(
                "  [WARN] Cannot parse vampire proof {}: {}",
                vampire_file, err
            );
            return None;
        }
    };

    let mut relevant_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    let mut proved_history = false;
    // TODO we might can do this a bit more elegantly but it works now:)
    let mut force_super = false;

    // build dependency lemma list from DAG
    let mut deps: Vec<String> = if lemma.starts_with("history_") {
        // for a history lemma, get its children in the DAG
        let children = match dag.get(lemma) {
            Some(c) => c,
            None => {
                eprintln!("   [WARN] No children for lemma {}", lemma);
                return None;
            }
        };

        // filter to only single children, if any exist
        let mut single_children: Vec<String> = children
            .iter()
            .filter(|c| c.starts_with("single_"))
            .cloned()
            .collect();

        if single_children.is_empty() {
            println!(
                "   [WARN] history lemma {} has no single lemma children; checking history children.",
                lemma
            );

            // gather history children of the lemma
            let history_children: Vec<String> = dag
                .get(lemma)
                .into_iter()
                .flat_map(|v| v.iter())
                .filter(|c| c.starts_with("history_"))
                .cloned()
                .collect();

            // filter out children that are parents in the DAG
            let non_parent_history_children: Vec<String> = history_children
                .into_iter()
                .filter(|child| !dag.keys().any(|k| k != lemma && dag[k].contains(child)))
                .collect();

            if non_parent_history_children.is_empty() {
                // no non-parent history children -> prove history itself
                println!(
                    "   [WARN] No non-parent history children found for {}; proving history directly.",
                    lemma
                );
                single_children.push(lemma.to_string());
                proved_history = true;
            } else {
                // use the non-parent history children as dependencies
                single_children = non_parent_history_children;
                force_super = true;
            }
        }

        single_children
    } else {
        // if not a history lemma, treat it as a single lemma
        // its own name is the dependency
        vec![lemma.to_string()]
    };

    // flag to check if any Vampire steps match the dependencies
    let mut matched_any = false;

    // match dependencies to Vampire relevant steps by formula
    for dep in &deps {
        // load the formula of the dependency lemma
        let dep_formula = match load_lemma(lemmas_dir, dep) {
            Ok(f) => f,
            Err(err) => {
                eprintln!("     [WARN] Cannot load {}: {}. Skipping.", dep, err);
                continue;
            }
        };

        // search only relevant vamp steps
        for &vnum in &relevant_set {
            let step = match all_steps.get(&vnum) {
                Some(s) => s,
                None => continue,
            };
            let wrapped = format!("({})", step.formula);

            // check if the dependency formula matches this step's formula
            if formulas_match(&dep_formula, &wrapped) {
                matched_any = true;

                // gather full transitive deps, then keep only relevant nodes among them
                let mut closure: BTreeSet<usize> = BTreeSet::new();
                gather_all_vamp_dependencies(vnum, &all_steps, &mut closure);

                for d in closure {
                    if relevant_set.contains(&d) {
                        if let Some(s) = all_steps.get(&d) {
                            relevant_steps.insert(d, s.clone());
                        }
                    }
                }

                break;
            }
        }
    }

    // return dependencies + matched Vampire steps if any were found
    if matched_any {
        if proved_history || force_super {
            // if we proved the history itself or forced superposition,
            // we have no other dependencies
            deps = Vec::new();
        }
        Some((
            deps,
            relevant_steps,
            proved_history,
            input_formulas,
            all_steps,
        ))
    } else {
        None
    }
}

/// Extract the exact derivation path (relevant-only) to prove a lemma formula.
/// Returns:
/// - relevant steps keyed by Vampire number
/// - input_formulas (vamp->formula)
/// - all_steps (vamp->VampStep)
pub fn extract_superposition_steps(
    vampire_file: &str,
    lemma_formula: &str,
) -> Option<(
    BTreeMap<usize, VampStep>,
    BTreeMap<usize, String>,
    BTreeMap<usize, VampStep>,
)> {
    let (all_steps, input_formulas, relevant_set) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            eprintln!(
                "  [WARN] Cannot parse Vampire proof {}: {}",
                vampire_file, err
            );
            return None;
        }
    };

    // find a relevant vamp step proving the lemma
    let proving_vnum = relevant_set.iter().copied().find(|vnum| {
        all_steps
            .get(vnum)
            .map(|step| formulas_match(lemma_formula, &format!("({})", step.formula)))
            .unwrap_or(false)
    })?;

    // gather full transitive deps and keep only relevant ones
    let mut closure: BTreeSet<usize> = BTreeSet::new();
    gather_all_vamp_dependencies(proving_vnum, &all_steps, &mut closure);

    let mut relevant_steps: BTreeMap<usize, VampStep> = BTreeMap::new();
    for v in closure {
        if relevant_set.contains(&v) {
            if let Some(step) = all_steps.get(&v) {
                relevant_steps.insert(v, step.clone());
            }
        }
    }

    Some((relevant_steps, input_formulas, all_steps))
}

/// Extend extra_dependencies using the renaming map from prepending superposition steps
pub fn extend_with_superposition_steps(
    extra_dependencies: &mut Vec<(String, String)>,
    relevant_steps: &BTreeMap<usize, VampStep>,
    renaming: &BTreeMap<usize, String>,
) {
    for (vnum, step) in relevant_steps {
        let Some(name) = renaming.get(vnum) else {
            eprintln!("[WARN] Missing renaming for vamp {}", vnum);
            continue;
        };

        if extra_dependencies.iter().any(|(n, _)| n == name) {
            continue;
        }

        extra_dependencies.push((name.clone(), step.formula.clone()));
    }
}

/// Find the lemma indices already present in dependencies
fn used_lemma_numbers(axioms: &Vec<(String, String)>) -> BTreeSet<usize> {
    let re = Regex::new(r"(?:history_|single_|abstract_)?lemma_(\d+)").unwrap();
    let mut used = BTreeSet::new();

    for (name, _) in axioms {
        for cap in re.captures_iter(name) {
            if let Ok(n) = cap[1].parse::<usize>() {
                used.insert(n);
            }
        }
    }

    used
}

/// Find the existing name of a lemma if available
fn find_existing_name_for_formula<'a>(
    axioms: &'a Vec<(String, String)>,
    step_formula: &str,
) -> Option<&'a str> {
    axioms
        .iter()
        .find(|(_, ax_f)| formulas_match(ax_f, step_formula) || formulas_match(step_formula, ax_f))
        .map(|(name, _)| name.as_str())
}

/// Prepend relevant Vampire steps and dependency formulas to a proof.
///
/// Key behavior change:
/// - deps that are not relevant steps are expanded (via FULL proof graph) to INPUT steps.
/// - those input steps are resolved to axiom names by formula matching when possible.
pub fn prepend_superposition_steps(
    axioms: &Vec<(String, String)>,             // (name, formula)
    relevant_steps: &BTreeMap<usize, VampStep>, // (vamp -> step) only relevant
    input_formulas: &BTreeMap<usize, String>,   // (vamp -> formula) for inputs
    all_steps: &BTreeMap<usize, VampStep>,      // full graph (vamp -> step)
) -> (String, BTreeMap<usize, String>) {
    // allocate lemma numbers from 1 upward, skipping already-used numbers
    let mut used = used_lemma_numbers(axioms);
    let mut next = 1usize;

    let mut fresh = || -> String {
        while used.contains(&next) {
            next += 1;
        }
        let n = next;
        used.insert(n);
        next += 1;
        format!("lemma_{:04}", n)
    };

    // build vamp -> global lemma name renaming for relevant steps
    let mut renaming: BTreeMap<usize, String> = BTreeMap::new();
    for (vnum, step) in relevant_steps {
        if let Some(existing) = find_existing_name_for_formula(axioms, &step.formula) {
            renaming.insert(*vnum, existing.to_string());
        } else {
            renaming.insert(*vnum, fresh());
        }
    }

    let mut annotated = String::new();
    annotated.push_str("% === Superposition Steps ===\n");

    let mut memo: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();

    for (vnum, step) in relevant_steps {
        let lemma_name = renaming.get(vnum).unwrap();

        let mut dep_strings: Vec<String> = Vec::new();

        for &d in &step.deps {
            if let Some(dep_lemma) = renaming.get(&d) {
                // dependency is another relevant step
                let dep_formula = relevant_steps
                    .get(&d)
                    .map(|s| s.formula.as_str())
                    .unwrap_or("UNKNOWN_FORMULA");
                dep_strings.push(format!("{}: {}", dep_lemma, dep_formula));
            } else {
                // dependency is non-relevant: expand to input leaves
                let mut visiting = BTreeSet::new();
                let inputs = expand_to_inputs(d, all_steps, &mut memo, &mut visiting);

                let mut resolved: Vec<String> = Vec::new();
                for iv in inputs {
                    // try resolve to axiom name
                    if let Some(inp_f) = input_formulas.get(&iv) {
                        if let Some((name, _)) =
                            axioms.iter().find(|(_, f)| formulas_match(f, inp_f))
                        {
                            resolved.push(name.clone());
                        } else {
                            resolved.push(format!("a_{}: {}", iv, inp_f));
                        }
                    } else if let Some(s) = all_steps.get(&iv) {
                        // fallback: show formula if we have it
                        resolved.push(format!("a_{}: {}", iv, s.formula));
                    } else {
                        resolved.push(format!("a_{}", iv));
                    }
                }

                resolved.sort();
                dep_strings.push(resolved.join(" + "));
            }
        }

        annotated.push_str(&format!(
            "% {}: {} | deps: {}\n",
            lemma_name,
            step.formula,
            dep_strings.join(", ")
        ));
    }

    annotated.push_str("\n");
    (annotated, renaming)
}

#[cfg(test)]
mod tests {
    use super::*;
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
                "history_lemma_0139".to_string(),
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
                    && l.contains("history_lemma_0139")
            }),
            "expected step 18 deps to resolve to lemma_0002 and history_lemma_0139. got:\n{annotated}"
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

        // Step 20 depends on step 18 + (17 -> 7), so it should contain a lemma_... and history_lemma_0139
        assert!(
            annotated.lines().any(|l| {
                l.contains("op(X0,X3) = op(op(X3,op(X1,X0)),X0)")
                    && l.contains("lemma_") // dependency on the renamed step 18
                    && l.contains("history_lemma_0139")
                    && !l.contains("a_17")
            }),
            "expected step 20 deps to include lemma_* and history_lemma_0139 (not a_17). got:\n{annotated}"
        );
    }
}
