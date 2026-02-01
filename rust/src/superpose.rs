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

/// Parse Vampire proof and assign sequential indices starting from the first relevant inference step
pub fn parse_vampire_proof(file_path: &str) -> Result<BTreeMap<usize, SuperpositionStep>, String> {
    let content = fs::read_to_string(file_path).map_err(|e| e.to_string())?;
    let mut steps = BTreeMap::new();
    let mut seq_index: Option<usize> = None;
    // map to look up seq_index from Vampire numbers
    let mut vamp_to_seq: BTreeMap<usize, usize> = BTreeMap::new();

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

        // start indexing at first relevant step
        if seq_index.is_none() {
            if let Some(tag_part) = line_trimmed.split('[').nth(1) {
                if proof_keywords.iter().any(|k| tag_part.contains(k)) {
                    seq_index = Some(1);
                } else {
                    continue; // skip until first relevant step
                }
            } else {
                continue;
            }
        }

        let current_idx = seq_index.unwrap();
        seq_index = Some(current_idx + 1);

        // extract formula (everything before first '[')
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

        // extract dependencies (numbers inside brackets)
        let deps: Vec<(usize, usize)> = if let Some(tag_part) = line_trimmed.split('[').nth(1) {
            tag_part
                .trim_end_matches(']')
                .split(|c| c == ',' || c == ' ')
                .filter_map(|s| s.trim().parse::<usize>().ok())
                .map(|vnum| {
                    let seq = vamp_to_seq.get(&vnum).copied().unwrap_or(0);
                    (vnum, seq)
                })
                .collect()
        } else {
            Vec::new()
        };

        // store the step
        steps.insert(current_idx, SuperpositionStep { formula, deps });

        // update lookup map for Vampire number
        if let Some(vnum) = vamp_num {
            vamp_to_seq.insert(vnum, current_idx);
        }
    }

    Ok(steps)
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
    Option<String>,
    Option<usize>,
    bool,
)> {
    // load the DAG from a file. This DAG maps each lemma to its children.
    let dag = load_dag(&dag);

    // parse Vampire proof into a map of step number -> SuperpositionStep
    let steps_map = match parse_vampire_proof(vampire_file) {
        Ok(m) => m,
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
    let mut derived_name: Option<String> = None;
    let mut derived_seq_idx: Option<usize> = None;
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

                // first match is the derived step
                if derived_seq_idx.is_none() {
                    derived_seq_idx = Some(*step_num);
                    derived_name = Some(dep.clone());
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
        Some((
            deps,
            relevant_steps,
            derived_name,
            derived_seq_idx,
            proved_history,
        ))
    } else {
        None // no matching Vampire steps found
    }
}

/// Parse a Vampire proof and extract the exact derivation path
/// to prove a lemma. Returns (relevant steps, seq_idx of derived lemma)
pub fn extract_superposition_steps(
    vampire_file: &str,
    lemma_formula: &str, // pass formula directly
) -> Option<(BTreeMap<usize, SuperpositionStep>, usize)> {
    // parse Vampire proof
    let steps_map = match parse_vampire_proof(vampire_file) {
        Ok(m) => m,
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

    Some((relevant_steps, derived_seq_idx))
}

/// Append all relevant superposition steps to a temporary file
pub fn append_superposition_steps_as_lemmas(
    tmp_file: &str,
    steps: &BTreeMap<usize, SuperpositionStep>,
    lemmas_dir: &str,
) -> Result<(), String> {
    for (seq_idx, _step) in steps {
        let mut all_deps = BTreeSet::new();
        gather_all_dependencies(*seq_idx, steps, &mut all_deps);

        for dep_idx in all_deps {
            let lemma_name = format!("lemma_{:04}", dep_idx);
            let formula = load_lemma(lemmas_dir, &lemma_name)?;
            append_as_axiom(tmp_file, &formula, &lemma_name);
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

/// Extend extra_dependencies using the renaming map from prepend_superposition_steps
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

/// Find the highest lemma index already present in `extra_dependencies`
/// and any kind of lemma name (lemma_, history_lemma_, single_lemma_, abstract_lemma_)
fn last_lemma_index(deps: &[(String, String)]) -> usize {
    let re = Regex::new(r"(?:.*_)?lemma_(\d+)$").unwrap();
    deps.iter()
        .filter_map(|(name, _)| {
            re.captures(name)
                .and_then(|cap| cap.get(1))
                .and_then(|m| m.as_str().parse::<usize>().ok())
        })
        .max()
        .unwrap_or(0)
}

/// Prepend superposition steps and dependency formulas to a proof
/// `axioms` is a list of (name, formula) tuples, treated as existing dependencies/axioms
/// `derived_lemma_name` is optional: the name of the lemma we are proving
/// `derived_seq_idx` is optional: the seq_idx of the step corresponding to the derived lemma
pub fn prepend_superposition_steps(
    superposition_steps: &BTreeMap<usize, SuperpositionStep>,
    axioms: &[(String, String)], // existing deps, treated as axioms (name, formula)
    derived_lemma_name: Option<&str>, // e.g., "lemma_0031"
    derived_seq_idx: Option<usize>, // seq_idx of the derived lemma
) -> (String, BTreeMap<usize, String>) {
    // compute offset to continue lemma numbering
    let mut next_lemma_idx = last_lemma_index(axioms) + 1;

    // build local -> global renaming
    let mut renaming: BTreeMap<usize, String> = BTreeMap::new();
    for seq_idx in superposition_steps.keys() {
        let name = if *seq_idx == 0 {
            // seq_idx == 0 is always the axiom
            "a1".to_string()
        } else if Some(*seq_idx) == derived_seq_idx {
            // only the derived lemma gets the special name
            derived_lemma_name
                .unwrap_or(&format!("lemma_{:04}", next_lemma_idx))
                .to_string()
        } else {
            // assign next unique lemma number
            let n = next_lemma_idx;
            next_lemma_idx += 1;
            format!("lemma_{:04}", n)
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
            .map(|(_vnum, sidx)| {
                if *sidx == 0 {
                    // dependency is an axiom
                    if let Some((name, formula)) = axioms
                        .iter()
                        .find(|(_, f)| formulas_match(f, &step.formula))
                    {
                        if name == "a1" {
                            "a1".to_string()
                        } else {
                            format!("{}: {}", name, formula)
                        }
                    } else {
                        "a1".to_string()
                    }
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
