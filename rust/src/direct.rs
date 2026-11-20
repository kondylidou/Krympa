//! Minimization without the `collect` phase.
//!
//! The Vampire proof is a sequence of derived equations. Each of them is tried
//! as the single place to cut the proof: keep Vampire's own derivation of that
//! equation, and ask the provers to prove the conjecture again from it. The
//! cut with the fewest total steps wins.
//!
//! This needs one `prove_lemma` call per derived equation and nothing else, so
//! no lemma has to be proved in advance to find out where the segments are.

use crate::alpha_match::formulas_match;
use crate::execution::{execution_mode, ExecutionMode};
use crate::minimize::{count_superposition_steps, proof_uses_lemma, prove_lemma};
use crate::prover_wrapper::proof_length;
use crate::regex_cache::cached_regex;
use crate::superpose::{
    extend_with_superposition_steps, gather_all_vamp_dependencies, parse_vampire_proof,
    prepend_superposition_steps, VampStep,
};
use crate::utils::{extract_conjecture_from_file, extract_suffix};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

/// One evaluated cut: (total steps, kept derivation steps, Vampire step number, proof text).
type Cut = (usize, usize, usize, String);

/// Try every derived equation of the Vampire proof as the single cut point.
pub fn try_direct(input_file: &str, vampire_file: &str) -> Result<String, String> {
    let input_content = fs::read_to_string(input_file)
        .map_err(|e| format!("Failed to read input file {}: {}", input_file, e))?;
    let conjecture = extract_conjecture_from_file(input_file)?;
    let (all_steps, input_formulas, relevant) = parse_vampire_proof(vampire_file)?;

    // Steps that were derived from the conjecture itself must never be handed
    // to a prover as axioms, or the conjecture would prove itself.
    let tainted = derived_from_conjecture(&all_steps, &conjecture);
    let candidates: Vec<usize> = relevant
        .iter()
        .copied()
        .filter(|v| !tainted.contains(v))
        .filter(|v| is_plain_equation(&all_steps[v].formula))
        .collect();
    crate::klog_info!(
        "[INFO] Direct minimization: {} cut candidates from {} proof steps",
        candidates.len(),
        relevant.len()
    );

    let evaluate = |vnum: &usize| -> Result<Option<Cut>, String> {
        let mut closure = BTreeSet::new();
        gather_all_vamp_dependencies(*vnum, &all_steps, &mut closure);
        let derivation: BTreeMap<usize, VampStep> = closure
            .into_iter()
            .filter(|v| relevant.contains(v))
            .map(|v| (v, all_steps[&v].clone()))
            .collect();

        let mut axioms: Vec<(String, String)> = Vec::new();
        let (start, renaming) =
            prepend_superposition_steps(&axioms, &derivation, &input_formulas, &all_steps);
        extend_with_superposition_steps(&mut axioms, &derivation, &renaming);

        let Some((rest, rest_steps, _)) = prove_lemma(input_file, "", None, &mut axioms, None)?
        else {
            return Ok(None);
        };
        // If the new proof refers to a given equation by formula instead of by
        // name, its uses cannot be traced, so nothing may be trimmed.
        let kept = if has_unnamed_reference(&rest) {
            start.clone()
        } else {
            keep_needed(&start, &rest)
        };
        let kept_steps = count_superposition_steps(&kept);
        crate::klog_debug!(
            "[DEBUG] cut at step {}: {} kept + {} new = {}",
            vnum,
            kept_steps,
            rest_steps,
            kept_steps + rest_steps
        );
        Ok(Some((
            kept_steps + rest_steps,
            kept_steps,
            *vnum,
            format!("{}{}", kept, rest),
        )))
    };

    let results: Vec<Option<Cut>> = if execution_mode() == ExecutionMode::Sequential {
        candidates
            .iter()
            .map(&evaluate)
            .collect::<Result<_, String>>()?
    } else {
        candidates
            .par_iter()
            .map(&evaluate)
            .collect::<Result<_, String>>()?
    };

    // candidates are in proof order, so ties go to the earliest cut
    let best = results
        .into_iter()
        .flatten()
        .min_by_key(|(total, _, vnum, _)| (*total, *vnum))
        .ok_or("No cut produced a proof.")?;
    let (total, kept_steps, vnum, proof) = best;

    let suffix = extract_suffix(input_file);
    let output = format!("../output/proof_{}.out", suffix);
    fs::write(
        &output,
        format!("% === Input Problem ===\n{}\n\n{}", input_content, proof),
    )
    .map_err(|e| e.to_string())?;

    let initial = fs::read_to_string(vampire_file)
        .map(|text| proof_length("vampire", &text))
        .unwrap_or(0);
    crate::klog_info!(
        "[RESULT] Cut at Vampire step {}: {}",
        vnum,
        all_steps[&vnum].formula
    );
    crate::klog_info!(
        "[RESULT] Total steps: {} ({} kept from the Vampire proof, {} new)",
        total,
        kept_steps,
        total - kept_steps
    );
    crate::klog_info!("[RESULT] Initial proof steps: {}", initial);
    crate::klog_info!("[RESULT] Minimized proof output: {}", output);
    Ok("Direct minimization complete".into())
}

/// A universally quantified equation without Skolem constants.
fn is_plain_equation(formula: &str) -> bool {
    !formula.contains("sK")
        && !formula.contains('$')
        && !formula.contains("!=")
        && !formula.contains('~')
        && formula.contains('=')
}

/// Steps whose derivation uses the conjecture (through its negation).
fn derived_from_conjecture(
    all_steps: &BTreeMap<usize, VampStep>,
    conjecture: &str,
) -> BTreeSet<usize> {
    let mut tainted = BTreeSet::new();
    // step numbers increase along the proof, so one pass in order is enough
    for (vnum, step) in all_steps {
        let is_conjecture = step.is_input
            && (formulas_match(conjecture, &step.formula)
                || formulas_match(&step.formula, conjecture));
        if is_conjecture || step.deps.iter().any(|d| tainted.contains(d)) {
            tainted.insert(*vnum);
        }
    }
    tainted
}

/// A dependency printed as `a_N: formula` with N > 1 is an input equation whose
/// name could not be recovered (`a_1` is the problem's own axiom).
fn has_unnamed_reference(proof: &str) -> bool {
    cached_regex(r"\ba_(\d+)\s*:")
        .captures_iter(proof)
        .any(|caps| &caps[1] != "1")
}

/// Keep exactly the lines of a superposition block that `later` needs,
/// directly or through other kept lines.
pub fn keep_needed(block: &str, later: &str) -> String {
    let line_re =
        cached_regex(r"^\s*%\s*([A-Za-z_]*lemma_\d+)\s*:\s*(.*?)\s*(?:\|\s*deps:\s*(.*))?$");
    let name_re = cached_regex(r"\b[A-Za-z_]*lemma_\d+\b");

    let mut deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for line in block.lines() {
        if let Some(caps) = line_re.captures(line) {
            let listed = caps.get(3).map(|m| m.as_str()).unwrap_or("");
            let names = name_re
                .find_iter(listed)
                .map(|m| m.as_str().to_string())
                .collect();
            deps.insert(caps[1].to_string(), names);
        }
    }

    let mut needed: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<String> = deps
        .keys()
        .filter(|name| proof_uses_lemma(name, &[later]))
        .cloned()
        .collect();
    while let Some(name) = stack.pop() {
        if needed.insert(name.clone()) {
            stack.extend(deps.get(&name).cloned().unwrap_or_default());
        }
    }
    if needed.is_empty() {
        return String::new();
    }

    let mut out = String::new();
    for line in block.lines() {
        let keep = match line_re.captures(line) {
            Some(caps) => needed.contains(&caps[1]),
            None => true,
        };
        if keep {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}
