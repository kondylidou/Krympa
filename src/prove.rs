//! Proving one goal with Twee and Vampire and choosing between the two proofs.

use crate::execution::term_size_aware;
use crate::provers::*;
use crate::superpose::*;
use crate::utils::*;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

/// Proves a lemma using Twee and Vampire, selecting the shorter proof.
/// - `superposition_steps`: optional superposition steps to append
/// - `dependencies`: optional dependencies (lemma names)
/// - `axioms`: additional axioms to append
/// - `axioms`: existing dependencies, will be extended with new lemmas
/// - `conjecture`: optional lemma/conjecture to prove
pub fn prove_lemma(
    input_file: &str,
    lemmas_dir: &str,
    dependencies: Option<&[String]>,    // names
    axioms: &mut Vec<(String, String)>, // (name, formula)
    conjecture: Option<&str>,
) -> Result<Option<(String, usize, String)>, String> {
    prove_lemma_matching(
        input_file,
        lemmas_dir,
        dependencies,
        axioms,
        conjecture,
        false,
        None,
    )
}

pub(crate) fn prove_lemma_matching(
    input_file: &str,
    lemmas_dir: &str,
    dependencies: Option<&[String]>,
    axioms: &mut Vec<(String, String)>,
    conjecture: Option<&str>,
    allow_instance: bool,
    prover_axioms: Option<&[(String, String)]>,
) -> Result<Option<(String, usize, String)>, String> {
    let tmp_path = create_tmp_copy(input_file)?;
    let proofs_dir = "proofs".to_string();

    // 1. Append dependency lemmas
    if let Some(deps) = dependencies {
        for dep_name in deps {
            let dep_formula = load_lemma(lemmas_dir, dep_name)
                .map_err(|_| format!("Missing lemma {}", dep_name))?;
            append_as_axiom(&tmp_path, &dep_formula, dep_name);
        }
    }

    // 2. Append extra dependencies
    for (name, formula) in prover_axioms.unwrap_or(axioms) {
        append_as_axiom(&tmp_path, formula, name);
    }

    // 3. Handle conjecture
    let (c_name, c_formula) = if let Some(s) = conjecture {
        let s = s.to_string();
        promote_axiom_to_conjecture(&tmp_path, &s)?;
        let formula = load_lemma(lemmas_dir, &s).map_err(|_| format!("Cannot load lemma {}", s))?;
        (s, formula)
    } else {
        let formula = extract_conjecture_from_file(input_file)?;
        ("conjecture".to_string(), formula)
    };

    // build a lookup-only axiom list that also includes the conjecture formula so that
    // Vampire input steps corresponding to the conjecture are named rather than falling
    // back to an a_N annotation (which looks like an unresolved reference in the output)
    let lookup_storage: Option<Vec<(String, String)>> = if axioms.iter().all(|(n, _)| n != &c_name)
    {
        let mut tmp = axioms.clone();
        tmp.push((c_name.clone(), c_formula.clone()));
        Some(tmp)
    } else {
        None
    };
    let axioms_for_lookup: &Vec<(String, String)> = lookup_storage.as_ref().unwrap_or(axioms);

    // 6. Run provers
    let twee_proof = run_twee(&tmp_path);
    let vampire_proof_file = format!("{}.vampire_proof", tmp_path);
    // Without this check a Vampire run that fails (timeout, give-up, rejected
    // input) would be read below as a proof with zero steps.
    let vampire_proved = run_vampire_turned(&tmp_path, &vampire_proof_file);
    let vampire_proof_exists = vampire_proved && Path::new(&vampire_proof_file).exists();

    // 7. Select shorter proof (or better proof when --term-size-aware is on)
    let result: Option<(String, usize, String)> = match (twee_proof, vampire_proof_exists) {
        // Twee + Vampire available
        (Some(tp), true) => {
            let t_len = proof_length_twee(&tp);

            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps_matching(
                    &vampire_proof_file,
                    &c_formula,
                    allow_instance,
                )
            {
                let v_len = sp_steps.len();

                let chose_vampire = if term_size_aware() {
                    let vp_text = fs::read_to_string(&vampire_proof_file).unwrap_or_default();
                    let t_avg = avg_term_size_twee(&tp);
                    let v_avg = avg_term_size_vampire(&vp_text);
                    let better = proof_quality_better(v_len, v_avg, t_len, t_avg);
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps (avg_term={:.1}), vampire {} steps (avg_term={:.1}) → chose {}",
                        t_len, t_avg, v_len, v_avg,
                        if better { "vampire" } else { "twee" }
                    );
                    better
                } else if v_len < t_len {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps, vampire {} steps → chose vampire",
                        t_len,
                        v_len
                    );
                    true
                } else {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps, vampire {} steps → chose twee",
                        t_len,
                        v_len
                    );
                    false
                };

                if chose_vampire {
                    let target = allow_instance.then_some((c_name.as_str(), c_formula.as_str()));
                    let (vp, renaming) = prepend_superposition_steps_for_target(
                        axioms_for_lookup,
                        &sp_steps,
                        &input_formulas,
                        &all_steps,
                        target,
                    );
                    extend_with_superposition_steps(axioms, &sp_steps, &renaming);
                    let deduped_len = renaming.values().collect::<BTreeSet<_>>().len();
                    Some((vp, deduped_len, "vampire".to_string()))
                } else {
                    Some((tp, t_len, "twee".to_string()))
                }
            } else {
                crate::klog_debug!(
                    "[DEBUG] prove_lemma: twee {} steps, vampire: no superposition steps → chose twee",
                    t_len
                );
                Some((tp, t_len, "twee".to_string()))
            }
        }

        // Twee only
        (Some(tp), false) => {
            let t_len = proof_length_twee(&tp);
            crate::klog_debug!(
                "[DEBUG] prove_lemma: vampire: no proof, twee {} steps → chose twee",
                t_len
            );
            Some((tp, t_len, "twee".to_string()))
        }

        // Vampire only
        (None, true) => {
            let vp_text = fs::read_to_string(&vampire_proof_file)
                .map_err(|_| "Failed to read Vampire proof file")?;
            let v_len = proof_length_vampire(&vp_text);
            crate::klog_debug!(
                "[DEBUG] prove_lemma: twee: no proof, vampire {} steps → chose vampire",
                v_len
            );
            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps_matching(
                    &vampire_proof_file,
                    &c_formula,
                    allow_instance,
                )
            {
                let target = allow_instance.then_some((c_name.as_str(), c_formula.as_str()));
                let (vp, renaming) = prepend_superposition_steps_for_target(
                    axioms_for_lookup,
                    &sp_steps,
                    &input_formulas,
                    &all_steps,
                    target,
                );
                extend_with_superposition_steps(axioms, &sp_steps, &renaming);
                let deduped_len = renaming.values().collect::<BTreeSet<_>>().len();
                Some((vp, deduped_len, "vampire".to_string()))
            } else {
                Some((vp_text, v_len, "vampire".to_string()))
            }
        }

        // no proof
        (None, false) => {
            crate::klog_debug!("[DEBUG] prove_lemma: no proof found by either prover");
            None
        }
    };

    // 8. Fallback: load an existing proof from proofs_dir (only if <= current best)
    let result: Option<(String, usize, String)> = match result {
        Some((best_proof, best_steps, best_by)) => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                if fb_steps < best_steps {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: fallback {} steps < current {} steps → using fallback",
                        fb_steps, best_steps
                    );
                    Some((fb_proof, fb_steps, "fallback".to_string()))
                } else {
                    Some((best_proof, best_steps, best_by))
                }
            } else {
                Some((best_proof, best_steps, best_by))
            }
        }

        // no proof found in this run -> try fallback
        None => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                crate::klog_debug!(
                    "[DEBUG] prove_lemma: no proof from provers, fallback {} steps",
                    fb_steps
                );
                Some((fb_proof, fb_steps, "fallback".to_string()))
            } else {
                crate::klog_debug!("[DEBUG] prove_lemma: no proof found by any means");
                None
            }
        }
    };

    // 9. Cleanup temporary file
    let _ = fs::remove_file(&tmp_path);

    Ok(result)
}

fn is_single_or_abstract(name: &str) -> bool {
    is_big_step_lemma(name) || is_abstracted_lemma(name)
}

/// Fallback: load an existing proof from proofs_dir (any variant),
/// and if it's a Vampire proof try to prepend extracted superposition steps.
/// Returns (proof_text, step_count).
fn fallback_proof(
    proofs_dir: &str,
    lemma_name: &str,
    lemma_formula: &str,
) -> Result<(String, usize), String> {
    // restrict to single_lemma_* and abstract_lemma_* only
    // TODO but history_lemma_* is already what our tool does
    if !is_single_or_abstract(lemma_name) {
        return Err(format!(
            "[INFO] Fallback only applies to single and abstract lemmas, got {}",
            lemma_name
        ));
    }

    let actual_file = select_actual_lemma(proofs_dir, lemma_name)
        .ok_or_else(|| format!("No proof file found for {}", lemma_name))?;

    // try different variants
    let candidates = [
        format!("{}/{}.proof", proofs_dir, actual_file),
        format!("{}/{}_twee.proof", proofs_dir, actual_file),
        format!("{}/{}_vampire.proof", proofs_dir, actual_file),
    ];

    let path = candidates
        .iter()
        .find(|p| Path::new(p).exists())
        .ok_or_else(|| format!("No proof file found for {} in any variant", lemma_name))?;

    let mut proof_text =
        fs::read_to_string(path).map_err(|_| format!("Cannot read proof file {}", path))?;

    let prover = actual_file
        .rsplit('_')
        .next()
        .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
        .split('.')
        .next()
        .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
        .to_string();

    // handle Vampire-specific prepending
    let steps = if prover == "vampire" {
        //let extra_dependencies = Vec::new();
        if let Some((relevant_steps, input_formulas, all_steps)) =
            extract_superposition_steps(path, lemma_formula)
        {
            let (prepended, _renaming) = prepend_superposition_steps(
                &Vec::new(),     // no axioms in fallback mode
                &relevant_steps, // relevant steps (vamp -> VampStep)
                &input_formulas, // vamp -> input formula
                &all_steps,      // full proof graph (vamp -> VampStep)
            );
            // in case of a history problem we will have extra dependencies which we will need to prove
            //extend_with_superposition_steps(extra_dependencies, &superposition_steps, &renaming);

            let steps_init = proof_length(&prover, &proof_text);
            proof_text = prepended;
            //superposition_steps.len()
            steps_init
        } else {
            // extraction failed --> initial proof
            proof_length(&prover, &proof_text)
        }
    } else {
        proof_length(&prover, &proof_text)
    };

    Ok((proof_text, steps))
}
