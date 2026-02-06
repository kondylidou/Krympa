use crate::alpha_match::formulas_match;
use crate::dag::load_dag;
use crate::utils::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

/// Parse Vampire proof and extract superposition steps with dependencies
#[derive(Debug, Clone)]
pub struct SuperpositionStep {
    pub formula: String,
    /// (original Vampire number, sequential index)
    pub deps: Vec<(usize, usize)>,
}

/// Parse Vampire proof:
/// - returns relevant inference steps as seq-indexed map
/// - ALSO returns input clauses (Vampire-number -> formula) so we can resolve deps with seq_idx=0
pub fn parse_vampire_proof(
    file_path: &str,
) -> Result<(BTreeMap<usize, SuperpositionStep>, BTreeMap<usize, String>), String> {
    let content = fs::read_to_string(file_path).map_err(|e| e.to_string())?;
    let mut steps = BTreeMap::new();

    // map to look up seq_index from Vampire numbers (for relevant steps only)
    let mut vamp_to_seq: BTreeMap<usize, usize> = BTreeMap::new();

    // store input clause formulas: Vampire number -> formula
    let mut input_formulas: BTreeMap<usize, String> = BTreeMap::new();

    let mut seq_index: Option<usize> = None;

    // keywords indicating relevant proof steps
    let proof_keywords = ["demodulation", "superposition", "resolution", "inequality"];

    for line in content.lines() {
        let line_trimmed = line.trim();
        if line_trimmed.is_empty() {
            continue;
        }

        // extract Vampire number if present
        let vamp_num: Option<usize> = line_trimmed
            .split('.')
            .next()
            .and_then(|s| s.trim().parse::<usize>().ok());

        // formula (everything before first '['), with leading "N." stripped
        let mut formula = line_trimmed
            .split('[')
            .next()
            .unwrap_or("")
            .trim()
            .to_string();

        // remove leading Vampire number + dot
        if let Some(pos) = formula.find('.') {
            if formula[..pos].trim().parse::<usize>().is_ok() {
                formula = formula[pos + 1..].trim().to_string();
            }
        }

        // read bracket tag-part if present
        let tag_part = match line_trimmed.split('[').nth(1) {
            Some(t) => t.trim_end_matches(']').to_string(),
            None => continue,
        };

        // record input clauses (these are exactly the ones that later show up as deps with seq_idx=0)
        if tag_part.contains("input") {
            if let Some(vnum) = vamp_num {
                input_formulas.insert(vnum, formula);
            }
            continue;
        }

        // start indexing at first relevant step
        if seq_index.is_none() {
            if proof_keywords.iter().any(|k| tag_part.contains(k)) {
                seq_index = Some(1);
            } else {
                continue; // skip until first relevant step
            }
        }

        let current_idx = seq_index.unwrap();
        seq_index = Some(current_idx + 1);

        // extract dependencies (numbers inside brackets)
        let deps: Vec<(usize, usize)> = tag_part
            .split(|c| c == ',' || c == ' ')
            .filter_map(|s| s.trim().parse::<usize>().ok())
            .map(|vnum| {
                let seq = vamp_to_seq.get(&vnum).copied().unwrap_or(0);
                (vnum, seq)
            })
            .collect();

        // store the step
        steps.insert(current_idx, SuperpositionStep { formula, deps });

        // update lookup map for Vampire number (relevant steps only)
        if let Some(vnum) = vamp_num {
            vamp_to_seq.insert(vnum, current_idx);
        }
    }

    Ok((steps, input_formulas))
}

/// Find an axiom name whose formula matches `input_formula`
/// Fast structural check first, then alpha-match as fallback.
fn match_input_to_axiom_name(
    axioms: &Vec<(String, String)>,
    input_formula: &str,
) -> Option<String> {
    fn canon(s: &str) -> String {
        // strip whitespace + trailing punctuation that Vampire/TPTP sometimes leaves
        s.trim()
            .trim_end_matches('.')
            .trim()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect()
    }

    fn wrap(s: &str) -> String {
        let t = s.trim().trim_end_matches('.').trim();
        if t.starts_with('!') || t.starts_with('(') {
            t.to_string()
        } else {
            format!("({})", t)
        }
    }

    let in_c = canon(input_formula);

    // 1) exact match on canonical strings
    for (name, ax_f) in axioms {
        if canon(ax_f) == in_c {
            return Some(name.clone());
        }
    }

    // 2) try alpha match in a few safe variants (wrapped/unwrapped combinations)
    let in_w = wrap(input_formula);
    for (name, ax_f) in axioms {
        let ax_raw = ax_f.trim().trim_end_matches('.').trim().to_string();
        let ax_w = wrap(ax_f);

        if formulas_match(&ax_raw, input_formula)
            || formulas_match(&ax_w, input_formula)
            || formulas_match(&ax_raw, &in_w)
            || formulas_match(&ax_w, &in_w)
        {
            return Some(name.clone());
        }
    }

    None
}

/// Extract nth (history) lemma and matching Vampire steps.
///
/// This function takes a `dag`, a `vampire_file` (proof by Vampire),
/// the directory containing lemmas, and a lemma.
/// It returns:
/// - a vector of dependency lemma names (from DAG)
/// - a map of superposition steps from Vampire proof relevant to these dependencies.
///
/// If no relevant Vampire steps are found, it returns `None`.
/// This function is used to extract the initial superposition steps.
pub fn superposition_steps(
    dag: &str,
    vampire_file: &str,
    lemmas_dir: &str,
    lemma: &str,
) -> Option<(
    Vec<String>,
    BTreeMap<usize, SuperpositionStep>,
    Option<(String, usize)>, // one derived match
    bool,
    BTreeMap<usize, String>, // input_formulas
)> {
    // load the DAG from a file. This DAG maps each lemma to its children.
    let dag = load_dag(&dag);

    let (steps_map, input_formulas) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            eprintln!(
                "  [WARN] Cannot parse vampire proof {}: {}",
                vampire_file, err
            );
            return None; // if parsing fails, no steps can be returned
        }
    };

    // store all Vampire steps that are relevant to the dependencies of the lemma
    let mut relevant_steps: BTreeMap<usize, SuperpositionStep> = BTreeMap::new();
    let mut proved_history = false;
    // TODO we might can do this a bit more elegantly but it works now:)
    let mut force_super = false;
    // derived lemma (name, idx)
    let mut derived: Option<(String, usize)> = None;

    // build the list of dependency lemmas from the DAG
    let mut deps: Vec<String> = if lemma.starts_with("history_") {
        // for a history lemma, get its children in the DAG
        let children = match dag.get(lemma) {
            Some(c) => c,
            None => {
                eprintln!("   [WARN] No children for lemma {}", lemma);
                return None; // cannot proceed without children
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
        // return the single children as dependencies
        single_children
    } else {
        // if not a history lemma, treat it as a single lemma
        // its own name is the dependency
        vec![lemma.to_string()]
    };

    // flag to check if any Vampire steps match the dependencies
    let mut matched_any = false;

    // match dependencies to Vampire proof steps
    for dep in &deps {
        // load the formula of the dependency lemma
        let dep_formula = match load_lemma(lemmas_dir, dep) {
            Ok(f) => f,
            Err(err) => {
                eprintln!("     [WARN] Cannot load {}: {}. Skipping.", dep, err);
                continue; // skip missing lemmas
            }
        };

        // loop over all Vampire proof steps
        for (step_num, step) in &steps_map {
            let wrapped = format!("({})", step.formula);

            // check if the dependency formula matches this step's formula
            if formulas_match(&dep_formula, &wrapped) {
                matched_any = true;

                // store only one derived lemma (the first match)
                if derived.is_none() {
                    derived = Some((dep.clone(), *step_num));
                }

                // recursively gather all dependencies of this Vampire step
                let mut all_deps: BTreeSet<usize> = BTreeSet::new();
                gather_all_dependencies(*step_num, &steps_map, &mut all_deps);

                // collect the actual steps into the relevant steps map
                for idx in &all_deps {
                    if let Some(s) = steps_map.get(idx) {
                        relevant_steps.insert(*idx, s.clone());
                    }
                }

                // break the loop once a match is found for this dependency
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
        Some((deps, relevant_steps, derived, proved_history, input_formulas))
    } else {
        None // no matching Vampire steps found
    }
}

/// Parse a Vampire proof and extract the exact derivation path
/// to prove a lemma. Returns (relevant steps, seq_idx of derived lemma)
pub fn extract_superposition_steps(
    vampire_file: &str,
    lemma_formula: &str, // pass formula directly
) -> Option<(BTreeMap<usize, SuperpositionStep>, usize, BTreeMap<usize, String>)> {
    let (steps_map, input_formulas) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            eprintln!(
                "  [WARN] Cannot parse Vampire proof {}: {}",
                vampire_file, err
            );
            return None;
        }
    };

    // find the Vampire step proving the lemma
    let derived_seq_idx = steps_map.iter().find_map(|(step_num, step)| {
        let wrapped = format!("({})", step.formula);
        if formulas_match(lemma_formula, &wrapped) {
            Some(*step_num)
        } else {
            None
        }
    })?;

    // collect all transitive dependencies of that step
    let mut all_deps: BTreeSet<usize> = BTreeSet::new();
    gather_all_dependencies(derived_seq_idx, &steps_map, &mut all_deps);

    let mut relevant_steps: BTreeMap<usize, SuperpositionStep> = BTreeMap::new();
    for idx in &all_deps {
        if let Some(step) = steps_map.get(idx) {
            relevant_steps.insert(*idx, step.clone());
        }
    }

    Some((relevant_steps, derived_seq_idx, input_formulas))
}

/// Append all relevant superposition steps to a temporary file
pub fn append_superposition_steps_as_lemmas(
    tmp_file: &str,
    steps: &BTreeMap<usize, SuperpositionStep>,
    lemmas_dir: &str,
    proofs_dir: &str,
) -> Result<(), String> {
    for (seq_idx, _step) in steps {
        let mut all_deps = BTreeSet::new();
        gather_all_dependencies(*seq_idx, steps, &mut all_deps);

        for dep_idx in all_deps {
            let lemma_name = format!("lemma_{:04}", dep_idx);
            if let Some(actual) = select_actual_lemma(proofs_dir, &lemma_name) {
                let name = strip_prover_suffix(&actual);
                let formula = load_lemma(lemmas_dir, &name)?;
                append_as_axiom(tmp_file, &formula, &name);
            } else {
                let formula = load_lemma(lemmas_dir, &lemma_name)?;
                append_as_axiom(tmp_file, &formula, &lemma_name);
            }
        }
    }
    Ok(())
}

/// Recursively gather all sequential-indexed dependencies
pub fn gather_all_dependencies(
    lemma_step: usize,
    steps_map: &BTreeMap<usize, SuperpositionStep>,
    collected: &mut BTreeSet<usize>,
) {
    if collected.contains(&lemma_step) {
        return;
    }
    collected.insert(lemma_step);

    if let Some(step) = steps_map.get(&lemma_step) {
        for (_vamp_num, seq_idx) in &step.deps {
            if *seq_idx > 0 {
                gather_all_dependencies(*seq_idx, steps_map, collected);
            }
        }
    }
}

/// Extend extra_dependencies using the renaming map from prepending superposition steps
pub fn extend_with_superposition_steps(
    extra_dependencies: &mut Vec<(String, String)>, // (name, formula)
    superposition_steps: &BTreeMap<usize, SuperpositionStep>,
    renaming: &BTreeMap<usize, String>, // local seq_idx -> global lemma name
) {
    for (seq_idx, step) in superposition_steps {
        if let Some(name) = renaming.get(seq_idx) {
            extra_dependencies.push((name.clone(), step.formula.clone()));
        } else {
            eprintln!("[WARN] Missing renaming for seq_idx {}", seq_idx);
        }
    }
}

/// Find the lemma indices already present in dependencies
fn used_lemma_numbers(
    axioms: &Vec<(String, String)>,
    derived_lemma: &Option<(String, usize)>,
) -> BTreeSet<usize> {
    let re = Regex::new(r"(?:history_|single_|abstract_)?lemma_(\d+)").unwrap();
    let mut used = BTreeSet::new();

    for (name, _) in axioms {
        for cap in re.captures_iter(name) {
            if let Ok(n) = cap[1].parse::<usize>() {
                used.insert(n);
            }
        }
    }

    if let Some((name, _)) = derived_lemma {
        for cap in re.captures_iter(name) {
            if let Ok(n) = cap[1].parse::<usize>() {
                used.insert(n);
            }
        }
    }

    used
}

/// Prepend superposition steps and dependency formulas to a proof
/// Takes `input_formulas` so we can resolve seq_idx==0 deps by matching formulas to `axioms`.
pub fn prepend_superposition_steps(
    superposition_steps: &BTreeMap<usize, SuperpositionStep>,
    axioms: &Vec<(String, String)>,
    derived_lemma: Option<(String, usize)>,
    input_formulas: &BTreeMap<usize, String>, // vamp_num -> input formula
) -> (String, BTreeMap<usize, String>) {
    // allocate lemma numbers from 1 upward, skipping already-used numbers (20,21,...)
    let mut used = used_lemma_numbers(axioms, &derived_lemma);
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

    // derived_map: seq_idx -> derived lemma name (at most one)
    let mut derived_map: BTreeMap<usize, String> = BTreeMap::new();
    if let Some((name, idx)) = &derived_lemma {
        derived_map.insert(*idx, name.clone());
    }

    // build local -> global renaming
    let mut renaming: BTreeMap<usize, String> = BTreeMap::new();
    for seq_idx in superposition_steps.keys() {
        let name = if let Some(derived_name) = derived_map.get(seq_idx) {
            derived_name.to_string()
        } else {
            // assign next unique lemma number
            fresh()
        };
        renaming.insert(*seq_idx, name);
    }

    let mut annotated_proof = String::new();
    annotated_proof.push_str("% === Superposition Steps ===\n");

    for (seq_idx, step) in superposition_steps {
        let lemma_name = renaming.get(seq_idx).unwrap();

        // build dependencies list
        let dep_list: Vec<String> = step
            .deps
            .iter()
            .map(|(vnum, sidx)| {
                if *sidx == 0 {
                    // resolve input dep by formula -> axiom name if possible
                    if let Some(inp_f) = input_formulas.get(vnum) {
                        if let Some(ax_name) = match_input_to_axiom_name(axioms, inp_f) {
                            return ax_name;
                        }
                        // fallback: keep it distinct and show formula
                        return format!("a_{}: {}", vnum, inp_f);
                    }
                    // if we don't have the input formula, keep it distinct
                    format!("a_{}", vnum)
                } else {
                    // dependency is another superposition step
                    let dep_name = renaming
                        .get(sidx)
                        .cloned()
                        .unwrap_or_else(|| format!("lemma_{:04}", sidx));
                    let dep_formula = superposition_steps
                        .get(sidx)
                        .map(|s| s.formula.as_str())
                        .unwrap_or("UNKNOWN_FORMULA");
                    format!("{}: {}", dep_name, dep_formula)
                }
            })
            .collect();

        annotated_proof.push_str(&format!(
            "% {}: {} | deps: {}\n",
            lemma_name,
            step.formula,
            dep_list.join(", ")
        ));
    }

    annotated_proof.push_str("\n");
    (annotated_proof, renaming)
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
        // - first relevant inference starts seq_index=1
        // - deps map VampNum->seq when available, else 0
        let proof = r#"
1. p(a) [input]
2. q(a) [input]
3. r(a) [superposition 1,2]
4. s(a) [resolution 3,2]
"#;

        let file = write_tmp(proof);
        let (steps, inputs) = parse_vampire_proof(&file).unwrap();

        // Inputs collected
        assert_eq!(inputs.get(&1).unwrap(), "p(a)");
        assert_eq!(inputs.get(&2).unwrap(), "q(a)");

        // Two relevant steps, indexed from 1
        assert_eq!(steps.len(), 2);

        // Step 1 corresponds to Vamp "3."
        let step1 = steps.get(&1).unwrap();
        assert_eq!(step1.formula, "r(a)");
        // deps are vamp nums 1 and 2, neither have seq idx (they were inputs), so 0
        assert_eq!(step1.deps, vec![(1, 0), (2, 0)]);

        // Step 2 corresponds to Vamp "4."
        let step2 = steps.get(&2).unwrap();
        assert_eq!(step2.formula, "s(a)");
        // dep "3" is the previous relevant step => seq idx 1, dep "2" is input => 0
        assert_eq!(step2.deps, vec![(3, 1), (2, 0)]);
    }

    #[test]
    fn test_prepend_resolves_input_deps_to_axiom_names() {
        // Build a tiny superposition_steps map manually
        let mut steps: BTreeMap<usize, SuperpositionStep> = BTreeMap::new();
        steps.insert(
            1,
            SuperpositionStep {
                formula: "r(a)".to_string(),
                deps: vec![(1, 0), (2, 0)], // both are inputs
            },
        );
        steps.insert(
            2,
            SuperpositionStep {
                formula: "s(a)".to_string(),
                deps: vec![(3, 1), (2, 0)], // depends on step1 + input2
            },
        );

        // Axioms available in the problem (name, formula)
        let axioms: Vec<(String, String)> = vec![
            ("a1".to_string(), "p(a)".to_string()),
            ("a2".to_string(), "q(a)".to_string()),
        ];

        // Input formulas parsed from Vampire
        let mut input_formulas: BTreeMap<usize, String> = BTreeMap::new();
        input_formulas.insert(1, "p(a)".to_string());
        input_formulas.insert(2, "q(a)".to_string());

        let (annotated, _renaming) =
            prepend_superposition_steps(&steps, &axioms, None, &input_formulas);

        // Step 1 deps should resolve to a1, a2 (not a_1/a_2)
        assert!(
            annotated.contains("% lemma_0001: r(a) | deps: a1, a2")
                || annotated.contains("% lemma_0002: r(a) | deps: a1, a2")
                || annotated.contains("% lemma_0003: r(a) | deps: a1, a2"),
            "annotated proof did not contain resolved input deps. got:\n{annotated}"
        );

        // Step 2 should contain dependency on the first lemma plus a2 (resolved)
        // (lemma name for seq 1 depends on renaming allocation; just check 'a2' appears on the second step line)
        assert!(
            annotated
                .lines()
                .any(|l| l.contains(": s(a) | deps:") && l.contains("a2")),
            "second step did not contain resolved input dep a2. got:\n{annotated}"
        );
    }
}
