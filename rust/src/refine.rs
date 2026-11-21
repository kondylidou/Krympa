//! The final refinement of the best proof (`--term-size`).

use crate::alpha_match::normalize_formula_alpha;
use crate::prove::prove_lemma_matching;
use crate::provers::{proof_length_twee, run_vampire_limited};
use crate::regex_cache::cached_regex;
use crate::trim::count_superposition_steps;
use crate::utils::*;
use std::fs;

/// Split one useful internal TWEE lemma out of the final proof and reprove only
/// the two remaining goals. This runs once, after the main search has finished.
pub(crate) fn refine_final_proof(
    input_file: &str,
    lemmas_dir: &str,
    proof: &str,
    original_steps: usize,
) -> Result<Option<(String, usize)>, String> {
    let marker = "The conjecture is true! Here is a proof.";
    let Some(twee_start) = proof.find(marker) else {
        return Ok(None);
    };
    let rest = &proof[twee_start..];
    let Some(twee_end) = rest.rfind("% === Superposition Steps ===") else {
        return Ok(None);
    };
    let twee = &rest[..twee_end];
    let cuts = extract_twee_lemmas(twee);
    if cuts.len() != 1 {
        return Ok(None);
    }
    let (cut_name, cut_formula) = &cuts[0];
    let Some((cut_text, _)) = twee.split_once("\nGoal ") else {
        return Ok(None);
    };

    let step_re = cached_regex(r"(?m)^%\s*([A-Za-z_]*lemma_\d+):\s*(.*?)\s*\|\s*deps:");
    let mut axioms = step_re
        .captures_iter(&proof[..twee_start])
        .map(|capture| (capture[1].to_string(), capture[2].to_string()))
        .collect::<Vec<_>>();
    let Some(mut cut_proof) = compress_twee_cut(input_file, cut_text, &axioms)? else {
        return Ok(None);
    };
    let header = cached_regex(r"(?m)^Lemma\s+(\d+):");
    cut_proof = header
        .replacen(&cut_proof, 1, format!("Lemma $1 ({}):", cut_name))
        .to_string();
    cut_proof.push_str("\n\nRESULT: Theorem (the lemma is true).\n\n");
    let cut_axiom = (cut_name.clone(), normalize_formula_alpha(cut_formula));
    axioms.push(cut_axiom.clone());

    let goal_re = cached_regex(r"Goal\s+\d+\s+\(([^)]+)\)");
    let Some(goal_name) = goal_re
        .captures(twee)
        .and_then(|capture| capture.get(1))
        .map(|name| name.as_str().to_string())
    else {
        return Ok(None);
    };
    let goal_axiom = (goal_name.clone(), load_lemma(lemmas_dir, &goal_name)?);
    axioms.push(goal_axiom.clone());
    let focused_axioms = [cut_axiom, goal_axiom];
    let Some((goal_proof, goal_steps, _)) = prove_lemma_matching(
        input_file,
        lemmas_dir,
        None,
        &mut axioms,
        Some(&goal_name),
        true,
        Some(&focused_axioms),
    )?
    else {
        return Ok(None);
    };
    let Some((conclusion, conclusion_steps, _)) =
        prove_lemma_matching(input_file, lemmas_dir, None, &mut axioms, None, true, None)?
    else {
        return Ok(None);
    };

    let prefix = &proof[..twee_start];
    let steps = count_superposition_steps(prefix)
        + proof_length_twee(&cut_proof)
        + goal_steps
        + conclusion_steps;
    if steps >= original_steps {
        return Ok(None);
    }
    crate::klog_debug!(
        "[DEBUG] Final local refinement: {} steps -> {} steps",
        original_steps,
        steps
    );
    Ok(Some((
        format!("{}{}{}{}", prefix, cut_proof, goal_proof, conclusion),
        steps,
    )))
}

fn compress_twee_cut(
    input_file: &str,
    proof: &str,
    axioms: &[(String, String)],
) -> Result<Option<String>, String> {
    let lines = proof.lines().collect::<Vec<_>>();
    let cite = cached_regex(r"by\s+(?:axiom|lemma)\s+\d+(?:\s+\(([^)]+)\))?");
    let source = |line: &str| {
        cite.captures(line)
            .and_then(|capture| capture.get(1).or_else(|| capture.get(0)))
            .map(|name| name.as_str().to_string())
    };
    let Some(index) = (1..lines.len().saturating_sub(3))
        .filter(|index| {
            source(lines[*index]).is_some() && source(lines[*index]) == source(lines[*index + 2])
        })
        .max_by_key(|index| {
            lines[index - 1].matches("op(").count() as isize
                - lines[index + 3].matches("op(").count() as isize
        })
    else {
        return Ok(None);
    };
    let equation = format!("{} = {}", lines[index - 1].trim(), lines[index + 3].trim());
    let Some(cited_axiom) =
        source(lines[index]).and_then(|source| axioms.iter().find(|(name, _)| name == &source))
    else {
        return Ok(None);
    };
    if !vampire_proves_in_one_step(input_file, cited_axiom, &equation)? {
        return Ok(None);
    }

    let mut output = lines[..index].join("\n");
    output.push_str(&format!(
        "\n= {{ by direct superposition of {} and {} }}\n{}\n",
        lines[index]
            .trim_start_matches("= { by ")
            .trim_end_matches(" }"),
        lines[index + 2]
            .trim_start_matches("= { by ")
            .trim_end_matches(" }"),
        lines[index + 3]
    ));
    output.push_str(&lines[index + 4..].join("\n"));
    Ok(Some(output))
}

fn vampire_proves_in_one_step(
    input_file: &str,
    axiom: &(String, String),
    formula: &str,
) -> Result<bool, String> {
    let candidate = create_tmp_copy(input_file)?;
    fs::write(&candidate, "").map_err(|error| error.to_string())?;
    append_as_axiom(&candidate, &axiom.1, &axiom.0);
    append_as_axiom(&candidate, formula, "local_shortcut");
    promote_axiom_to_conjecture(&candidate, "local_shortcut")?;
    let proof = run_vampire_limited(&candidate).unwrap_or_default();
    let _ = fs::remove_file(candidate);
    Ok(proof.contains("SZS status Theorem") && is_single_rewrite_refutation(&proof))
}

/// True if a Vampire refutation rewrites exactly once.
///
/// A merged step is counted as one proof step, so its justification must have
/// the shape of every other superposition step: one rewrite (superposition or
/// demodulation), after which the goal is closed by an instance of an equation
/// that is already available. Every inference in the refutation must therefore
/// be either preprocessing, that single rewrite, or such a closing step. Any
/// other inference rule makes the check fail, so an unknown rule can never be
/// mistaken for "no work".
pub fn is_single_rewrite_refutation(proof: &str) -> bool {
    const REWRITES: [&str; 3] = [
        "superposition",
        "forward demodulation",
        "backward demodulation",
    ];
    const NO_REWRITE: [&str; 17] = [
        "input",
        "negated conjecture",
        "ennf transformation",
        "nnf transformation",
        "rectify",
        "flattening",
        "skolemisation",
        "choice axiom",
        "skolem symbol introduction",
        "cnf transformation",
        "trivial inequality removal",
        "subsumption resolution",
        "forward subsumption resolution",
        "backward subsumption resolution",
        "resolution",
        "unit resulting resolution",
        "equality resolution",
    ];
    let step_re = cached_regex(r"^\d+\.\s.*\[([^\[\]]*)\]\s*$");
    let mut rewrites = 0;
    for line in proof.lines() {
        let Some(caps) = step_re.captures(line.trim()) else {
            continue;
        };
        // "superposition 8,7" -> "superposition"; "input(axiom)" -> "input"
        let tag = caps[1].trim();
        let rule = tag
            .trim_end_matches(|c: char| c.is_ascii_digit() || c == ',' || c == ' ')
            .split('(')
            .next()
            .unwrap_or("")
            .trim();
        if REWRITES.contains(&rule) {
            rewrites += 1;
        } else if !NO_REWRITE.contains(&rule) {
            return false;
        }
    }
    rewrites == 1
}
