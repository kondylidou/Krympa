//! Step removal: remove avoidable steps from a proof, without calling a prover.
//! A whole run does it at the end unless `--no-compress` is given.
//!
//! A superposition line is avoidable if every step that uses it can be derived
//! in one rewrite from the other equations instead; the search is the one the
//! Lean export checks steps with. Such lines, and then the lines nothing needs
//! any more, are dropped. Twee proofs are kept as they are. The result is a
//! proof file in the same format, so it can be checked in Lean like any other.

use crate::lean::{reachable, translate, Converter};
use crate::proof_file::{read_proof, Item, STEPS_HEADER, TWEE_MARKER};
use crate::regex_cache::cached_regex;
use crate::rewrite::FactId;
use std::collections::{BTreeSet, HashMap};

type Uses = HashMap<FactId, BTreeSet<FactId>>;

/// A proof without its avoidable steps.
pub struct Compressed {
    pub text: String,
    pub steps_before: usize,
    pub steps_after: usize,
}

/// Remove the avoidable steps of a proof. The result is translated once more,
/// so a proof whose steps no longer check is never returned.
pub fn compress(proof_text: &str) -> Result<Compressed, String> {
    let proof = read_proof(proof_text);
    let mut converter = Converter::new(&proof)?;
    converter.convert(&proof.items)?;
    let final_uses = std::mem::take(&mut converter.library.used);
    if !converter.failures.is_empty() || !converter.assumed.is_empty() {
        let problems = [converter.failures.clone(), converter.assumed.clone()].concat();
        return Err(format!(
            "the proof does not check as it is: {}",
            problems.join("; ")
        ));
    }

    // Lines between two Twee proofs may be reordered among themselves; number
    // those groups 0, 2, 4, ... and the Twee proofs 1, 3, ...
    let mut segment_of_item = Vec::with_capacity(proof.items.len());
    let mut segment = 0i64;
    for item in &proof.items {
        segment_of_item.push(match item {
            Item::Line { .. } => 2 * segment,
            Item::Axiom { block, .. } | Item::Chain { block, .. } => {
                segment = segment.max(*block as i64);
                2 * *block as i64 - 1
            }
        });
    }

    let facts: Vec<FactId> = converter
        .all_facts
        .iter()
        .copied()
        .filter(|fact| converter.item_of.contains_key(fact))
        .collect();
    let item = |fact: FactId| &proof.items[converter.item_of[&fact]];
    let mut proof_lines = Lines {
        facts: facts.clone(),
        axioms: converter.axiom_facts.clone(),
        segment: facts
            .iter()
            .map(|&fact| (fact, segment_of_item[converter.item_of[&fact]]))
            .collect(),
        is_line: facts.iter().map(|&f| (f, item(f).is_line())).collect(),
        citable: facts
            .iter()
            .map(|&f| (f, item(f).is_line() || !item(f).name().is_empty()))
            .collect(),
        removed: BTreeSet::new(),
    };
    let mut uses: Uses = facts
        .iter()
        .map(|&fact| (fact, converter.uses.get(&fact).cloned().unwrap_or_default()))
        .collect();

    let mut changed = true;
    while changed {
        changed = false;
        let mut live = reachable(&final_uses, &uses);
        let candidates: Vec<FactId> = facts
            .iter()
            .rev()
            .copied()
            .filter(|f| proof_lines.is_line[f] && live.contains(f))
            .filter(|f| !proof_lines.removed.contains(f))
            .collect();
        for line in candidates {
            if final_uses.contains(&line) {
                continue;
            }
            let dependents: Vec<FactId> = facts
                .iter()
                .copied()
                .filter(|d| live.contains(d) && !proof_lines.removed.contains(d))
                .filter(|d| uses[d].contains(&line))
                .collect();
            if dependents.iter().any(|d| !proof_lines.is_line[d]) {
                continue; // a Twee proof cites it: keep
            }
            // Derive the dependents again one after the other, each seeing the
            // new derivations of the ones before it; otherwise two of them
            // could end up depending on each other.
            let mut trial = uses.clone();
            let mut derived_all = true;
            for dependent in dependents {
                let fact = converter.library.facts[dependent].clone();
                let default = fact.default_var();
                let pool = proof_lines.available(dependent, line, &trial);
                let goal = (&fact.lhs, &fact.rhs);
                let library = &mut converter.library;
                library.used.clear();
                let found = library
                    .justify(goal, &pool, &default, false, None)
                    .or_else(|| library.justify(goal, &pool, &default, true, None));
                if found.is_none() {
                    derived_all = false;
                    break;
                }
                trial.insert(dependent, std::mem::take(&mut library.used));
            }
            if derived_all {
                uses = trial;
                proof_lines.removed.insert(line);
                changed = true;
                live = reachable(&final_uses, &uses);
            }
        }
    }
    converter.library.used.clear();

    let keep: BTreeSet<FactId> = reachable(&final_uses, &uses)
        .into_iter()
        .filter(|fact| !proof_lines.removed.contains(fact))
        .collect();
    for &fact in &keep {
        if ancestors(fact, &uses).contains(&fact) {
            return Err(format!(
                "internal error: {} depends on itself",
                item(fact).name()
            ));
        }
    }
    let kept_lines: Vec<FactId> = facts
        .iter()
        .copied()
        .filter(|f| proof_lines.is_line[f] && keep.contains(f))
        .collect();

    // write the file again, with the kept lines in place of the old ones
    let mut name_of: HashMap<FactId, String> = facts
        .iter()
        .map(|&fact| (fact, item(fact).name().to_string()))
        .collect();
    for (_, name, fact) in &converter.hypotheses {
        name_of.insert(*fact, name.clone());
    }
    let mut by_segment: HashMap<i64, BTreeSet<FactId>> = HashMap::new();
    for &fact in &kept_lines {
        by_segment
            .entry(proof_lines.segment[&fact])
            .or_default()
            .insert(fact);
    }
    let cited_in_order: Vec<FactId> = [facts.clone(), converter.axiom_facts.clone()].concat();

    let line_re = cached_regex(r"^%\s*([A-Za-z_]\w*)\s*:");
    let (mut out, mut blocks, mut emitted) = (Vec::new(), 0i64, BTreeSet::new());
    for line in proof_text.lines() {
        let stripped = line.trim();
        if stripped.starts_with(TWEE_MARKER) {
            blocks += 1;
        }
        if !line_re.is_match(stripped) && stripped != STEPS_HEADER {
            out.push(line.to_string());
            continue;
        }
        if !emitted.insert(2 * blocks) {
            continue;
        }
        let Some(group) = by_segment.get(&(2 * blocks)) else {
            continue;
        };
        out.push(STEPS_HEADER.to_string());
        for fact in dependencies_first(&facts, group, &uses) {
            let deps: Vec<&str> = cited_in_order
                .iter()
                .filter(|cited| uses[&fact].contains(cited))
                .map(|cited| name_of[cited].as_str())
                .collect();
            out.push(format!(
                "% {}: {} | deps: {}",
                name_of[&fact],
                item(fact).formula(),
                deps.join(", ")
            ));
        }
    }
    let text = cached_regex(r"\n{3,}")
        .replace_all(&out.join("\n"), "\n\n")
        .into_owned()
        + "\n";
    let check = translate(&text, "the shortened proof")?;
    if !check.certified {
        return Err(format!(
            "the shortened proof does not check: {}",
            check.messages.join("; ")
        ));
    }
    Ok(Compressed {
        text,
        steps_before: converter.steps,
        steps_after: check.steps,
    })
}

/// What step removal needs to know about the proved equations.
struct Lines {
    facts: Vec<FactId>,
    axioms: Vec<FactId>,
    segment: HashMap<FactId, i64>,
    is_line: HashMap<FactId, bool>,
    /// whether other steps may cite it: lines and named Twee goals
    citable: HashMap<FactId, bool>,
    removed: BTreeSet<FactId>,
}

impl Lines {
    /// The equations `dependent` may be derived from without `line`: the
    /// axioms, and the citable equations before it that need neither
    /// `dependent` (that would be circular) nor `line` (it is being removed).
    fn available(&self, dependent: FactId, line: FactId, uses: &Uses) -> Vec<FactId> {
        let mut pool = self.axioms.clone();
        for &fact in &self.facts {
            if fact == dependent
                || fact == line
                || self.removed.contains(&fact)
                || !self.citable[&fact]
            {
                continue;
            }
            let before = if self.is_line[&fact] {
                self.segment[&fact] <= self.segment[&dependent]
            } else {
                self.segment[&fact] < self.segment[&dependent]
            };
            if !before {
                continue;
            }
            let needs = ancestors(fact, uses);
            if !needs.contains(&dependent) && !needs.contains(&line) {
                pool.push(fact);
            }
        }
        pool
    }
}

/// Everything `fact` depends on, directly or not.
fn ancestors(fact: FactId, uses: &Uses) -> BTreeSet<FactId> {
    let mut found = BTreeSet::new();
    let mut stack = vec![fact];
    while let Some(current) = stack.pop() {
        for &cited in uses.get(&current).into_iter().flatten() {
            if found.insert(cited) {
                stack.push(cited);
            }
        }
    }
    found
}

/// The facts of `group`, each after the ones it depends on, otherwise in proof order.
fn dependencies_first(facts: &[FactId], group: &BTreeSet<FactId>, uses: &Uses) -> Vec<FactId> {
    fn visit(
        fact: FactId,
        facts: &[FactId],
        group: &BTreeSet<FactId>,
        uses: &Uses,
        done: &mut BTreeSet<FactId>,
        out: &mut Vec<FactId>,
    ) {
        if done.contains(&fact) || !group.contains(&fact) {
            return;
        }
        done.insert(fact);
        for &cited in facts.iter().filter(|f| uses[&fact].contains(f)) {
            visit(cited, facts, group, uses, done, out);
        }
        out.push(fact);
    }
    let (mut done, mut out) = (BTreeSet::new(), Vec::new());
    for &fact in facts {
        visit(fact, facts, group, uses, &mut done, &mut out);
    }
    out
}
