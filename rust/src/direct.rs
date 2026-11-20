//! Minimization without the `collect` phase.
//!
//! The proof keeps Krympa's three segments:
//!
//!   1. axioms -> departure lemma: Vampire's own derivation, kept as it is;
//!   2. departure -> arrival lemma: proved again by the provers;
//!   3. arrival lemma -> conjecture: proved again by the provers.
//!
//! `minimize` learns which lemmas are worth trying from the per-lemma proofs
//! of `collect`. Here nothing is proved in advance:
//!
//!   * every equation of the Vampire proof is tried as departure lemma of a
//!     proof with two segments (departure, then straight to the conjecture);
//!   * the departures that did best there are combined with the last few
//!     equations of the Vampire proof as arrival lemma;
//!   * for the best of those combinations the last segment is proved once more
//!     with every equation of the first two segments available.

use crate::alpha_match::formulas_match;
use crate::execution::{execution_mode, term_size_aware, ExecutionMode};
use crate::minimize::{
    count_superposition_steps, proof_uses_lemma, prove_lemma, refine_final_proof,
};
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

/// How many of the last equations of the Vampire proof are tried as arrival lemma.
const MAX_ARRIVALS: usize = 5;
/// How many departure lemmas (the best ones with two segments) get an arrival lemma.
const MAX_DEPARTURES: usize = 15;
/// For how many combinations the last segment is proved again in full context.
const MAX_REFINED: usize = 10;
/// Name of the arrival lemma in the output; the number is out of the range
/// that the derived equations are numbered in.
const ARRIVAL: &str = "lemma_9001";
/// Lemma numbers of the last segment are shifted by this much, because that
/// segment is proved on its own and would otherwise reuse the numbers of the first.
const LAST_SEGMENT_OFFSET: usize = 5000;

type Steps = BTreeMap<usize, VampStep>;

/// One evaluated combination.
struct Candidate {
    total: usize,
    kept: usize,
    departure: usize,
    arrival: Option<usize>,
    proof: String,
}

/// The proof of the conjecture from one arrival lemma alone.
struct LastSegment {
    text: String,
    steps: usize,
}

/// The first two segments of a three-segment proof, before trimming.
struct FirstTwo {
    departure: usize,
    arrival: usize,
    start: String,
    middle: String,
    middle_steps: usize,
    middle_is_block: bool,
    /// every equation known after the second segment
    axioms: Vec<(String, String)>,
}

struct Problem<'a> {
    input_file: &'a str,
    all_steps: &'a Steps,
    input_formulas: &'a BTreeMap<usize, String>,
    relevant: &'a BTreeSet<usize>,
}

impl Problem<'_> {
    /// Vampire's derivation of one equation: the text block and its equations.
    fn derivation(&self, vnum: usize) -> (String, Vec<(String, String)>) {
        let mut closure = BTreeSet::new();
        gather_all_vamp_dependencies(vnum, self.all_steps, &mut closure);
        let steps: Steps = closure
            .into_iter()
            .filter(|v| self.relevant.contains(v))
            .map(|v| (v, self.all_steps[&v].clone()))
            .collect();
        let mut axioms: Vec<(String, String)> = Vec::new();
        let (text, renaming) =
            prepend_superposition_steps(&axioms, &steps, self.input_formulas, self.all_steps);
        extend_with_superposition_steps(&mut axioms, &steps, &renaming);
        (text, axioms)
    }

    /// Two segments: derivation of the departure lemma, then the conjecture.
    fn two_segments(&self, departure: usize) -> Result<Option<Candidate>, String> {
        let (start, mut axioms) = self.derivation(departure);
        let Some((rest, rest_steps, _)) =
            prove_lemma(self.input_file, "", None, &mut axioms, None)?
        else {
            return Ok(None);
        };
        let kept = keep_used(&start, &rest);
        let kept_steps = count_superposition_steps(&kept);
        Ok(Some(Candidate {
            total: kept_steps + rest_steps,
            kept: kept_steps,
            departure,
            arrival: None,
            proof: format!("{}{}", kept, rest),
        }))
    }

    /// Third segment for one arrival lemma: the conjecture from that lemma alone.
    fn last_segment(&self, arrival: usize) -> Result<Option<LastSegment>, String> {
        let mut axioms = vec![(
            ARRIVAL.to_string(),
            self.all_steps[&arrival].formula.clone(),
        )];
        let Some((text, steps, _)) = prove_lemma(self.input_file, "", None, &mut axioms, None)?
        else {
            return Ok(None);
        };
        if !proof_uses_lemma(ARRIVAL, &[&text]) || has_unnamed_reference(&text) {
            return Ok(None); // the arrival lemma does not help to reach the conjecture
        }
        Ok(Some(LastSegment {
            text: shift_lemma_numbers(&text, LAST_SEGMENT_OFFSET),
            steps,
        }))
    }

    /// First and second segment: derivation of the departure lemma, then the
    /// arrival lemma proved from it.
    fn first_two(&self, departure: usize, arrival: usize) -> Result<Option<FirstTwo>, String> {
        let (start, mut axioms) = self.derivation(departure);
        axioms.push((
            ARRIVAL.to_string(),
            self.all_steps[&arrival].formula.clone(),
        ));
        let Some((middle, middle_steps, by)) =
            prove_lemma(self.input_file, "", None, &mut axioms, Some(ARRIVAL))?
        else {
            return Ok(None);
        };
        Ok(Some(FirstTwo {
            departure,
            arrival,
            start,
            middle_is_block: by == "vampire" && middle.contains("Superposition Steps"),
            middle,
            middle_steps,
            axioms,
        }))
    }

    /// Put three segments together, dropping what the later ones do not use.
    fn assemble(&self, two: &FirstTwo, last: &str, last_steps: usize) -> Candidate {
        // the second segment is only needed for what the third takes from it
        let (middle, middle_steps) = if proof_uses_lemma(ARRIVAL, &[last]) {
            (two.middle.clone(), two.middle_steps)
        } else if two.middle_is_block {
            let kept = keep_used(&two.middle, last);
            let steps = count_superposition_steps(&kept);
            (kept, steps)
        } else {
            (String::new(), 0)
        };
        let later = format!("{}{}", middle, last);
        let kept = keep_used(&two.start, &later);
        let kept_steps = count_superposition_steps(&kept);
        Candidate {
            total: kept_steps + middle_steps + last_steps,
            kept: kept_steps,
            departure: two.departure,
            arrival: (!middle.is_empty()).then_some(two.arrival),
            proof: format!("{}{}", kept, later),
        }
    }

    /// Third segment proved with every equation of the first two available.
    fn refine(&self, two: &FirstTwo) -> Result<Option<Candidate>, String> {
        let mut axioms = two.axioms.clone();
        let Some((last, last_steps, _)) =
            prove_lemma(self.input_file, "", None, &mut axioms, None)?
        else {
            return Ok(None);
        };
        Ok(Some(self.assemble(two, &last, last_steps)))
    }
}

/// Run `task` on every item, in parallel unless `--sequential` was given.
fn run_all<T, R, F>(items: &[T], task: F) -> Result<Vec<R>, String>
where
    T: Sync,
    R: Send,
    F: Fn(&T) -> Result<R, String> + Sync + Send,
{
    if execution_mode() == ExecutionMode::Sequential {
        items.iter().map(&task).collect()
    } else {
        items.par_iter().map(&task).collect()
    }
}

/// Try every departure lemma, with and without an arrival lemma.
pub fn try_direct(input_file: &str, vampire_file: &str) -> Result<String, String> {
    let input_content = fs::read_to_string(input_file)
        .map_err(|e| format!("Failed to read input file {}: {}", input_file, e))?;
    let conjecture = extract_conjecture_from_file(input_file)?;
    let (all_steps, input_formulas, relevant) = parse_vampire_proof(vampire_file)?;
    let problem = Problem {
        input_file,
        all_steps: &all_steps,
        input_formulas: &input_formulas,
        relevant: &relevant,
    };

    // Steps that were derived from the conjecture itself must never be handed
    // to a prover as axioms, or the conjecture would prove itself.
    let tainted = derived_from_conjecture(&all_steps, &conjecture);
    let lemmas: Vec<usize> = relevant
        .iter()
        .copied()
        .filter(|v| !tainted.contains(v))
        .filter(|v| is_plain_equation(&all_steps[v].formula))
        .collect();
    let arrivals: Vec<usize> = lemmas.iter().rev().take(MAX_ARRIVALS).copied().collect();
    crate::klog_info!(
        "[INFO] Direct minimization: {} departure candidates, {} arrival candidates",
        lemmas.len(),
        arrivals.len()
    );

    // two segments
    let mut candidates: Vec<Candidate> = run_all(&lemmas, |d| problem.two_segments(*d))?
        .into_iter()
        .flatten()
        .collect();
    crate::klog_info!(
        "[INFO] Best with two segments: {}",
        candidates
            .iter()
            .map(|c| c.total)
            .min()
            .map_or("no proof".to_string(), |n| format!("{} steps", n))
    );

    // three segments, for the departures that did best with two
    let mut ranked: Vec<(usize, usize)> =
        candidates.iter().map(|c| (c.total, c.departure)).collect();
    ranked.sort();
    let departures: Vec<usize> = ranked
        .iter()
        .take(MAX_DEPARTURES)
        .map(|(_, d)| *d)
        .collect();

    let last_segments: BTreeMap<usize, LastSegment> = run_all(&arrivals, |a| {
        Ok(problem.last_segment(*a)?.map(|last| (*a, last)))
    })?
    .into_iter()
    .flatten()
    .collect();
    let pairs: Vec<(usize, usize)> = last_segments
        .keys()
        .flat_map(|a| {
            departures
                .iter()
                .filter(move |d| *d < a)
                .map(move |d| (*d, *a))
        })
        .collect();
    let mut first_twos: Vec<FirstTwo> = run_all(&pairs, |(d, a)| problem.first_two(*d, *a))?
        .into_iter()
        .flatten()
        .collect();
    for two in &first_twos {
        let last = &last_segments[&two.arrival];
        candidates.push(problem.assemble(two, &last.text, last.steps));
    }

    // the most promising combinations get a last segment in full context
    first_twos.sort_by_key(|two| {
        (
            count_superposition_steps(&keep_used(&two.start, &two.middle)) + two.middle_steps,
            two.departure,
            two.arrival,
        )
    });
    first_twos.truncate(MAX_REFINED);
    candidates.extend(
        run_all(&first_twos, |two| problem.refine(two))?
            .into_iter()
            .flatten(),
    );
    for c in &candidates {
        crate::klog_debug!(
            "[DEBUG] departure {} arrival {:?}: {} kept + {} new = {}",
            c.departure,
            c.arrival,
            c.kept,
            c.total - c.kept,
            c.total
        );
    }

    // fewest steps; ties go to fewer segments, then to the earliest lemmas
    let mut best = candidates
        .into_iter()
        .min_by_key(|c| (c.total, c.arrival.is_some(), c.departure, c.arrival))
        .ok_or("No combination produced a proof.")?;

    // With --term-size the final refinement of `minimize` applies here too.
    if let (true, Some(arrival)) = (term_size_aware(), best.arrival) {
        let statement = &all_steps[&arrival].formula;
        match refine_final_proof(input_file, "", &best.proof, best.total, Some(statement)) {
            Ok(Some((refined, steps))) => {
                // the refinement keeps the first segment as it is
                best.proof = refined;
                best.total = steps;
            }
            Ok(None) => {}
            Err(error) => crate::klog_warn!("[WARN] Final proof refinement skipped: {}", error),
        }
    }

    let suffix = extract_suffix(input_file);
    let output = format!("../output/proof_{}.out", suffix);
    fs::write(
        &output,
        format!(
            "% === Input Problem ===\n{}\n\n{}",
            input_content, best.proof
        ),
    )
    .map_err(|e| e.to_string())?;

    let initial = fs::read_to_string(vampire_file)
        .map(|text| proof_length("vampire", &text))
        .unwrap_or(0);
    crate::klog_info!(
        "[RESULT] Departure lemma: Vampire step {}: {}",
        best.departure,
        all_steps[&best.departure].formula
    );
    match best.arrival {
        Some(a) => crate::klog_info!(
            "[RESULT] Arrival lemma: Vampire step {}: {}",
            a,
            all_steps[&a].formula
        ),
        None => crate::klog_info!("[RESULT] Arrival lemma: none (two segments)"),
    }
    crate::klog_info!(
        "[RESULT] Total steps: {} ({} kept from the Vampire proof, {} new)",
        best.total,
        best.kept,
        best.total - best.kept
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
fn derived_from_conjecture(all_steps: &Steps, conjecture: &str) -> BTreeSet<usize> {
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

/// The part of a derivation that `later` uses. If `later` refers to an
/// equation by formula instead of by name, its uses cannot be traced and
/// nothing is dropped.
fn keep_used(block: &str, later: &str) -> String {
    if has_unnamed_reference(later) {
        block.to_string()
    } else {
        keep_needed(block, later)
    }
}

/// Add `offset` to every lemma number below `offset`, so that a segment that
/// was proved on its own does not reuse the numbers of another one.
pub fn shift_lemma_numbers(text: &str, offset: usize) -> String {
    cached_regex(r"\blemma_(\d+)\b")
        .replace_all(text, |caps: &regex::Captures| {
            match caps[1].parse::<usize>() {
                Ok(n) if n < offset => format!("lemma_{:04}", n + offset),
                _ => caps[0].to_string(),
            }
        })
        .to_string()
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
