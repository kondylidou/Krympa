use crate::alpha_match::{formula_is_instance_of, formulas_match};
use crate::dag::load_dag;
use crate::proof_turnaround::eq_proof_procedure;
use crate::regex_cache::cached_regex;
use crate::utils::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

type AllSteps = BTreeMap<usize, VampStep>; // all steps (vamp -> step)
type InputFormulas = BTreeMap<usize, String>; // input_formulas (vamp -> formula)
type RelevantSteps = BTreeMap<usize, VampStep>; // only relevant (vamp -> step)

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
pub fn parse_vampire_proof(file_path: &str) -> Result<ParsedProof, String> {
    let content = fs::read_to_string(file_path).map_err(|e| e.to_string())?;
    parse_vampire_text(&content)
}

/// All steps, input formulas and relevant step numbers of a Vampire proof.
pub type ParsedProof = (AllSteps, InputFormulas, BTreeSet<usize>);

/// `parse_vampire_proof` on the text of a proof.
fn parse_vampire_text(content: &str) -> Result<ParsedProof, String> {
    let mut all_steps: AllSteps = BTreeMap::new();
    let mut input_formulas: InputFormulas = BTreeMap::new();
    let mut relevant: BTreeSet<usize> = BTreeSet::new();

    // keywords indicating relevant proof steps
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
    ];

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
            .split([',', ' '])
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
    all_steps: &AllSteps,
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
    all_steps: &AllSteps,
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
    RelevantSteps, // relevant steps as vampire-indexed map
    bool,
    InputFormulas, // input_formulas
    AllSteps,      // all_steps
)> {
    // load the DAG from a file. This DAG maps each lemma to its children.
    let dag = load_dag(dag);

    let (all_steps, input_formulas, relevant_set) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            crate::klog_warn!(
                "  [WARN] Cannot parse vampire proof {}: {}",
                vampire_file,
                err
            );
            return None;
        }
    };

    let mut relevant_steps: RelevantSteps = BTreeMap::new();
    let mut proved_history = false;
    // TODO we might can do this a bit more elegantly but it works now:)
    let mut force_super = false;

    // build dependency lemma list from DAG
    let mut deps: Vec<String> = if is_small_step_lemma(lemma) {
        // for a history lemma, get its children in the DAG
        let children = match dag.get(lemma) {
            Some(c) => c,
            None => {
                crate::klog_warn!("   [WARN] No children for lemma {}", lemma);
                return None;
            }
        };

        // filter to only single children, if any exist
        let mut single_children: Vec<String> = children
            .iter()
            .filter(|c| is_big_step_lemma(c))
            .cloned()
            .collect();

        if single_children.is_empty() {
            crate::klog_debug!(
                "   [WARN] history lemma {} has no single lemma children; checking history children.",
                lemma
            );

            // gather history children of the lemma
            let history_children: Vec<String> = dag
                .get(lemma)
                .into_iter()
                .flat_map(|v| v.iter())
                .filter(|c| is_small_step_lemma(c))
                .cloned()
                .collect();

            // filter out children that are parents in the DAG
            let non_parent_history_children: Vec<String> = history_children
                .into_iter()
                .filter(|child| !dag.keys().any(|k| k != lemma && dag[k].contains(child)))
                .collect();

            if non_parent_history_children.is_empty() {
                // no non-parent history children -> prove history itself
                crate::klog_debug!(
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
                crate::klog_warn!("     [WARN] Cannot load {}: {}. Skipping.", dep, err);
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
) -> Option<(RelevantSteps, InputFormulas, AllSteps)> {
    extract_superposition_steps_matching(vampire_file, lemma_formula, false)
}

pub(crate) fn extract_superposition_steps_matching(
    vampire_file: &str,
    lemma_formula: &str,
    allow_instance: bool,
) -> Option<(RelevantSteps, InputFormulas, AllSteps)> {
    let content = match fs::read_to_string(vampire_file) {
        Ok(content) => content,
        Err(err) => {
            crate::klog_warn!(
                "  [WARN] Cannot read Vampire proof {}: {}",
                vampire_file,
                err
            );
            return None;
        }
    };
    let find = |(all_steps, _, relevant_set): &ParsedProof| {
        relevant_set.iter().copied().find(|vnum| {
            all_steps
                .get(vnum)
                .map(|step| {
                    formulas_match(lemma_formula, &step.formula)
                        || formulas_match(lemma_formula, &format!("({})", step.formula))
                        || (allow_instance && formula_is_instance_of(&step.formula, lemma_formula))
                })
                .unwrap_or(false)
        })
    };
    let mut parsed = match parse_vampire_text(&content) {
        Ok(x) => x,
        Err(err) => {
            crate::klog_warn!(
                "  [WARN] Cannot parse Vampire proof {}: {}",
                vampire_file,
                err
            );
            return None;
        }
    };
    let mut proving_vnum = find(&parsed);
    // A lemma proof stored by `collect` is Vampire's refutation as printed. It
    // may never state the lemma itself; turned around, it ends with it.
    if proving_vnum.is_none() && content.contains("$false") {
        if let Ok(turned) = parse_vampire_text(&eq_proof_procedure(&content)) {
            proving_vnum = find(&turned);
            if proving_vnum.is_some() {
                parsed = turned;
            }
        }
    }
    let (all_steps, input_formulas, relevant_set) = parsed;

    if proving_vnum.is_none() {
        crate::klog_debug!(
            "[DEBUG] extract_superposition_steps: no step matched lemma formula: {}\n  relevant steps: {}",
            lemma_formula,
            relevant_set.iter()
                .filter_map(|v| all_steps.get(v).map(|s| format!("{}: {}", v, s.formula)))
                .collect::<Vec<_>>()
                .join("\n  ")
        );
    }

    let proving_vnum = proving_vnum?;

    // gather full transitive deps and keep only relevant ones
    let mut closure: BTreeSet<usize> = BTreeSet::new();
    gather_all_vamp_dependencies(proving_vnum, &all_steps, &mut closure);

    let mut relevant_steps: RelevantSteps = BTreeMap::new();
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
    relevant_steps: &RelevantSteps,
    renaming: &BTreeMap<usize, String>,
) {
    for (vnum, step) in relevant_steps {
        let Some(name) = renaming.get(vnum) else {
            crate::klog_warn!("[WARN] Missing renaming for vamp {}", vnum);
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
    let re = cached_regex(r"(?:small_step_|big_step_|abstracted_)?lemma_(\d+)");
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

/// The relevant steps, each after the steps it uses, otherwise by Vampire
/// number. The numbers alone are not such an order: a turned refutation keeps
/// Vampire's numbers, so a turned step can use a step with a higher number.
fn dependency_order(relevant_steps: &RelevantSteps, all_steps: &AllSteps) -> Vec<usize> {
    fn visit(
        step: usize,
        relevant_steps: &RelevantSteps,
        all_steps: &AllSteps,
        visited: &mut BTreeSet<usize>,
        order: &mut Vec<usize>,
    ) {
        if !visited.insert(step) {
            return;
        }
        // look through steps that are not relevant themselves, too
        let deps = all_steps
            .get(&step)
            .or_else(|| relevant_steps.get(&step))
            .map(|s| s.deps.clone())
            .unwrap_or_default();
        for dep in deps {
            visit(dep, relevant_steps, all_steps, visited, order);
        }
        if relevant_steps.contains_key(&step) {
            order.push(step);
        }
    }
    let (mut visited, mut order) = (BTreeSet::new(), Vec::new());
    for &step in relevant_steps.keys() {
        visit(step, relevant_steps, all_steps, &mut visited, &mut order);
    }
    order
}

/// The name of the premise that `step` merely restates, if it states the
/// same equation as one of its premises and that premise has a name: a step
/// of the block, or an input that is one of `axioms`.
fn restated_premise(
    step: &VampStep,
    renaming: &BTreeMap<usize, String>,
    axioms: &[(String, String)],
    input_formulas: &InputFormulas,
    all_steps: &AllSteps,
) -> Option<String> {
    let same = |formula: &str| formulas_match(formula, &step.formula);
    for dep in &step.deps {
        if let Some(name) = renaming.get(dep) {
            let formula = all_steps.get(dep).map(|s| s.formula.as_str()).unwrap_or("");
            if same(formula) {
                return Some(name.clone());
            }
            continue;
        }
        // a premise that is not a step of the block: an input, possibly
        // after a transformation such as cnf
        let mut visiting = BTreeSet::new();
        let mut memo = BTreeMap::new();
        let inputs = expand_to_inputs(*dep, all_steps, &mut memo, &mut visiting);
        let inputs: Vec<usize> = inputs.into_iter().collect();
        if let [input] = inputs.as_slice() {
            let formula = all_steps.get(dep).map(|s| s.formula.as_str()).unwrap_or("");
            if let (Some(input_formula), true) = (input_formulas.get(input), same(formula)) {
                if let Some((name, _)) = axioms
                    .iter()
                    .find(|(_, f)| formulas_match(f, input_formula))
                {
                    return Some(name.clone());
                }
            }
        }
    }
    None
}

/// Find the existing name of a lemma if available
fn find_existing_name_for_formula<'a>(
    axioms: &'a [(String, String)],
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
    axioms: &Vec<(String, String)>, // (name, formula)
    relevant_steps: &RelevantSteps, // (vamp -> step) only relevant
    input_formulas: &InputFormulas, // (vamp -> formula) for inputs
    all_steps: &AllSteps,           // full graph (vamp -> step)
) -> (String, BTreeMap<usize, String>) {
    prepend_superposition_steps_for_target(
        axioms,
        relevant_steps,
        input_formulas,
        all_steps,
        None,
        None,
    )
}

/// With `goal`, the (name, equation) the block proves: the step that states
/// the goal is named after it and always written. A step whose statement is
/// that of one of its own premises only restates it (the turned end of a
/// refutation starts like that); it is not written, and the steps that use it
/// cite the premise.
pub(crate) fn prepend_superposition_steps_for_target(
    axioms: &Vec<(String, String)>,
    relevant_steps: &RelevantSteps,
    input_formulas: &InputFormulas,
    all_steps: &AllSteps,
    target: Option<(&str, &str)>,
    goal: Option<(&str, &str)>,
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

    // build vamp -> global lemma name renaming for relevant steps.
    // also check steps already named in this run so equivalent formulas
    // (including reversed equality direction) collapse to the same name.
    let mut renaming: BTreeMap<usize, String> = BTreeMap::new();
    let mut seen_this_run: Vec<(String, String)> = Vec::new();
    // steps that restate a lemma derived earlier in the proof
    let mut restatements: BTreeSet<usize> = BTreeSet::new();
    // Steps are named and written in dependency order: of two steps with the
    // same equation, the one written is then the one with a derivation, and
    // the other, a mere restatement, gets its name.
    let order = dependency_order(relevant_steps, all_steps);
    let target_vnum = target.and_then(|(_, formula)| {
        relevant_steps
            .iter()
            .find(|(_, step)| formula_is_instance_of(&step.formula, formula))
            .map(|(vnum, _)| *vnum)
    });
    for vnum in &order {
        let step = &relevant_steps[vnum];
        if Some(*vnum) == target_vnum {
            renaming.insert(*vnum, target.unwrap().0.to_string());
        } else if let Some((name, _)) =
            goal.filter(|(_, formula)| formulas_match(formula, &step.formula))
        {
            renaming.insert(*vnum, name.to_string());
        } else if let Some(premise) =
            goal.and_then(|_| restated_premise(step, &renaming, axioms, input_formulas, all_steps))
        {
            restatements.insert(*vnum);
            renaming.insert(*vnum, premise);
        } else if let Some(existing) = find_existing_name_for_formula(axioms, &step.formula) {
            renaming.insert(*vnum, existing.to_string());
        } else if let Some(existing) = find_existing_name_for_formula(&seen_this_run, &step.formula)
        {
            renaming.insert(*vnum, existing.to_string());
        } else {
            let name = fresh();
            seen_this_run.push((name.clone(), step.formula.clone()));
            renaming.insert(*vnum, name);
        }
    }

    let mut annotated = String::new();
    annotated.push_str("% === Superposition Steps ===\n");

    let mut memo: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut output_names: BTreeSet<String> = BTreeSet::new();

    for vnum in &order {
        let step = &relevant_steps[vnum];
        let lemma_name = renaming.get(vnum).unwrap();

        // the lemma it restates is derived elsewhere in the proof
        if restatements.contains(vnum) {
            continue;
        }

        // skip if an equivalent step was already output under this name
        if !output_names.insert(lemma_name.clone()) {
            continue;
        }

        let mut dep_strings: Vec<String> = Vec::new();
        let mut seen_dep_names: BTreeSet<String> = BTreeSet::new();

        for &d in &step.deps {
            if let Some(dep_lemma) = renaming.get(&d) {
                // skip if this dep name was already listed (dedup of equivalent steps)
                if !seen_dep_names.insert(dep_lemma.clone()) {
                    continue;
                }
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

    annotated.push('\n');
    (annotated, renaming)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generalized_endpoint_gets_target_name_without_self_dependency() {
        let input = VampStep {
            formula: "op(X0,X0) = X0".to_string(),
            deps: vec![],
            is_input: true,
        };
        let intermediate = VampStep {
            formula: "op(X0,op(X1,X0)) = op(X0,X1)".to_string(),
            deps: vec![1],
            is_input: false,
        };
        let endpoint = VampStep {
            formula: "op(X0,X1) = X0".to_string(),
            deps: vec![10],
            is_input: false,
        };
        let relevant_steps = BTreeMap::from([(10, intermediate.clone()), (11, endpoint.clone())]);
        let input_formulas = BTreeMap::from([(1, input.formula.clone())]);
        let all_steps = BTreeMap::from([(1, input), (10, intermediate), (11, endpoint)]);
        let axioms = vec![("a1".to_string(), "op(X0,X0) = X0".to_string())];

        let (proof, renaming) = prepend_superposition_steps_for_target(
            &axioms,
            &relevant_steps,
            &input_formulas,
            &all_steps,
            Some(("goal", "op(X0,op(X1,X0)) = X0")),
            None,
        );

        assert_eq!(renaming.get(&11).map(String::as_str), Some("goal"));
        assert_ne!(renaming.get(&10).map(String::as_str), Some("goal"));
        assert!(!proof
            .lines()
            .any(|line| { line.starts_with("% goal:") && line.contains("| deps: goal:") }));
    }

    /// Equation 775 implies equation 2928: in the turned refutation, step 18
    /// restates step 43 and has the lower number. Step 43 must be written,
    /// with its derivation, and step 18 must not cite itself.
    #[test]
    fn a_restated_step_does_not_replace_its_derivation() {
        let step = |formula: &str, deps: Vec<usize>, is_input: bool| VampStep {
            formula: formula.to_string(),
            deps,
            is_input,
        };
        let all_steps = BTreeMap::from([
            (5, step("! [X0,X1] : op(X0,X1) = op(X1,X0)", vec![], true)),
            (
                6,
                step(
                    "! [X0,X1,X2] : X0 = op(op(X1,op(X2,op(X0,X1))),X2)",
                    vec![],
                    true,
                ),
            ),
            (11, step("$true", vec![], false)),
            (13, step("op(X0,X1) = op(X1,X0)", vec![5], false)),
            (
                14,
                step("op(op(X1,op(X2,op(X0,X1))),X2) = X0", vec![6], false),
            ),
            (
                18,
                step(
                    "! [X0,X1,X2] : X0 = op(X1,op(X2,op(X1,op(X0,X2))))",
                    vec![11, 43],
                    false,
                ),
            ),
            (
                43,
                step("op(X2,op(X1,op(X2,op(X0,X1)))) = X0", vec![13, 14], false),
            ),
            (
                210,
                step(
                    "! [X0,X1,X2] : X0 = op(X1,op(op(X1,op(X0,X2)),X2))",
                    vec![18, 13],
                    false,
                ),
            ),
        ]);
        let relevant_steps: RelevantSteps = [18, 43, 210]
            .iter()
            .map(|n| (*n, all_steps[n].clone()))
            .collect();
        let input_formulas = BTreeMap::from([
            (5, all_steps[&5].formula.clone()),
            (6, all_steps[&6].formula.clone()),
        ]);
        let axioms = vec![
            (
                "lemma_0003".to_string(),
                "op(X0,X1) = op(X1,X0)".to_string(),
            ),
            (
                "a1".to_string(),
                "X0 = op(op(X1,op(X2,op(X0,X1))),X2)".to_string(),
            ),
        ];

        let (proof, renaming) =
            prepend_superposition_steps(&axioms, &relevant_steps, &input_formulas, &all_steps);

        assert_eq!(renaming[&18], renaming[&43]);
        let name = &renaming[&43];
        let lines: Vec<&str> = proof
            .lines()
            .filter(|l| l.starts_with("% lemma_"))
            .collect();
        assert_eq!(lines.len(), 2, "{}", proof);
        // step 43 itself is written, not its restatement
        assert!(
            lines[0].starts_with(&format!(
                "% {}: op(X2,op(X1,op(X2,op(X0,X1)))) = X0 |",
                name
            )),
            "{}",
            proof
        );
        // no line cites itself
        for line in &lines {
            let (own, deps) = line[2..].split_once(": ").unwrap();
            let deps = deps.split_once("| deps:").unwrap().1;
            assert!(
                !deps
                    .split(", ")
                    .any(|dep| dep.trim().split(':').next() == Some(own)),
                "{}",
                proof
            );
        }
    }

    /// Equation 3108 implies equation 2496, reduced: the turned end of a
    /// refutation first restates the earlier lemma `lemma_0001`. That line is
    /// not written again, and the next step cites `lemma_0001` itself.
    #[test]
    fn a_restatement_of_an_earlier_lemma_is_not_written() {
        let step = |formula: &str, deps: Vec<usize>, is_input: bool| VampStep {
            formula: formula.to_string(),
            deps,
            is_input,
        };
        let all_steps = BTreeMap::from([
            (1, step("! [X0,X1] : op(op(X0,X1),X0) = X0", vec![], true)),
            (2, step("! [X0,X1] : X0 = op(X1,X0)", vec![], true)),
            (9, step("$true", vec![], false)),
            (12, step("op(op(X0,X2),X0) = X0", vec![1], false)),
            (
                20,
                step("! [X0,X1] : X0 = op(op(X0,X1),X0)", vec![9, 12], false),
            ),
            (21, step("! [X0,X1] : X0 = op(X1,X0)", vec![20, 12], false)),
        ]);
        let relevant_steps: RelevantSteps = [20, 21]
            .iter()
            .map(|n| (*n, all_steps[n].clone()))
            .collect();
        let input_formulas = BTreeMap::from([
            (1, all_steps[&1].formula.clone()),
            (2, all_steps[&2].formula.clone()),
        ]);
        let axioms = vec![
            (
                "lemma_0001".to_string(),
                "op(op(X0,X2),X0) = X0".to_string(),
            ),
            ("conjecture".to_string(), "X0 = op(X1,X0)".to_string()),
        ];

        let (proof, renaming) = prepend_superposition_steps_for_target(
            &axioms,
            &relevant_steps,
            &input_formulas,
            &all_steps,
            None,
            Some(("conjecture", "X0 = op(X1,X0)")),
        );

        assert_eq!(renaming[&20], "lemma_0001");
        let lines: Vec<&str> = proof
            .lines()
            .filter(|l| l.starts_with("% ") && !l.starts_with("% ==="))
            .collect();
        assert_eq!(lines.len(), 1, "{}", proof);
        assert!(lines[0].starts_with("% conjecture:"), "{}", proof);
        assert!(lines[0].contains("deps: lemma_0001"), "{}", proof);

        // without a goal nothing is left out, as before
        let (proof, _) = prepend_superposition_steps_for_target(
            &axioms,
            &relevant_steps,
            &input_formulas,
            &all_steps,
            None,
            None,
        );
        assert_eq!(
            proof
                .lines()
                .filter(|l| l.starts_with("% lemma_0001:"))
                .count(),
            1
        );
    }

    /// Equation 102 implies equation 617: the lemma being proved is already
    /// among the known names, but the step deriving it from the axiom is not
    /// a restatement and must be written.
    #[test]
    fn the_derivation_of_a_known_name_is_written() {
        let step = |formula: &str, deps: Vec<usize>, is_input: bool| VampStep {
            formula: formula.to_string(),
            deps,
            is_input,
        };
        let all_steps = BTreeMap::from([
            (
                1,
                step("! [X0,X1] : X0 = op(X0,op(op(X0,X1),X1))", vec![], true),
            ),
            (7, step("op(X0,op(op(X0,X1),X1)) = X0", vec![1], false)),
            (
                9,
                step("op(X0,op(X0,op(op(X0,X1),X1))) = X0", vec![7, 7], false),
            ),
        ]);
        let relevant_steps: RelevantSteps = BTreeMap::from([(9, all_steps[&9].clone())]);
        let input_formulas = BTreeMap::from([(1, all_steps[&1].formula.clone())]);
        let axioms = vec![
            ("a1".to_string(), "X0 = op(X0,op(op(X0,X1),X1))".to_string()),
            (
                "lemma_0001".to_string(),
                "X0 = op(X0,op(X0,op(op(X0,X1),X1)))".to_string(),
            ),
        ];
        let (proof, _) = prepend_superposition_steps_for_target(
            &axioms,
            &relevant_steps,
            &input_formulas,
            &all_steps,
            None,
            Some(("conjecture", "X0 = op(X0,op(X1,X1))")),
        );
        assert!(
            proof.contains("% lemma_0001: op(X0,op(X0,op(op(X0,X1),X1))) = X0 | deps: a1"),
            "{}",
            proof
        );
    }

    /// Equation 102 implies equation 617: the last step restates the premise
    /// `lemma_0001` and is at the same time the goal. It is written, under
    /// the goal's name.
    #[test]
    fn a_step_stating_the_goal_is_written_under_its_name() {
        let step = |formula: &str, deps: Vec<usize>, is_input: bool| VampStep {
            formula: formula.to_string(),
            deps,
            is_input,
        };
        let all_steps = BTreeMap::from([
            (
                1,
                step(
                    "! [X0,X1] : op(X0,op(X0,op(op(X0,X1),X1))) = X0",
                    vec![],
                    true,
                ),
            ),
            (10, step("$true", vec![], false)),
            (
                11,
                step("op(X0,op(X0,op(op(X0,X1),X1))) = X0", vec![1], false),
            ),
            (
                13,
                step(
                    "! [X0,X1] : X0 = op(X0,op(X0,op(op(X0,X1),X1)))",
                    vec![10, 11],
                    false,
                ),
            ),
        ]);
        let relevant_steps: RelevantSteps = BTreeMap::from([(13, all_steps[&13].clone())]);
        let input_formulas = BTreeMap::from([(1, all_steps[&1].formula.clone())]);
        let goal = "! [X0,X1] : X0 = op(X0,op(X0,op(op(X0,X1),X1)))";
        let axioms = vec![
            (
                "lemma_0001".to_string(),
                "op(X0,op(X0,op(op(X0,X1),X1))) = X0".to_string(),
            ),
            ("conjecture".to_string(), goal.to_string()),
        ];
        let (proof, renaming) = prepend_superposition_steps_for_target(
            &axioms,
            &relevant_steps,
            &input_formulas,
            &all_steps,
            None,
            Some(("conjecture", goal)),
        );
        assert_eq!(renaming[&13], "conjecture");
        assert!(
            proof
                .lines()
                .any(|l| l.starts_with("% conjecture: ") && l.contains("lemma_0001")),
            "{}",
            proof
        );
    }
}
