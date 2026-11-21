//! Lean export: write a proof as a Lean 4 file and have Lean check it.
//!
//! Every proof step becomes an explicit proof term, so Lean only checks the
//! proof and never has to search for it:
//!
//!   * a Twee rewrite step `s = t` becomes `congrArg (fun hole => C[hole]) (dep args)`,
//!     one rewrite of one subterm;
//!   * a superposition step becomes one rewrite that turns the goal into an
//!     instance of a second equation, `Eq.mpr (congrArg ...) (dep args)`, the
//!     term form of `rw [dep₁ ..]; exact dep₂ ..`.
//!
//! The instance and the rewritten occurrences are found by the search in
//! `rewrite.rs`. A step that is not a single rewrite of its premises is
//! reported and left as `sorry`, so a file that Lean accepts without a message
//! certifies the proof and its step count.

use crate::proof_file::{canon, read_proof, Item, ProofFile};
use crate::regex_cache::cached_regex;
use crate::rewrite::{
    parse_equation, parse_term, rename, show, term_vars, Fact, FactId, Library, Term,
};
use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::path::Path;
use std::process::Command;

const LEAN_PROJECT: &str = "../lean";

/// A proof file turned into Lean, step by step.
pub struct Converter {
    pub library: Library,
    conjecture: Option<(String, String)>,
    /// the `have` blocks of the Lean proof
    out: Vec<String>,
    /// name in the proof file, also in its canonical form -> fact
    by_name: HashMap<String, FactId>,
    /// the proved facts, in order
    pub all_facts: Vec<FactId>,
    pub axiom_facts: Vec<FactId>,
    /// (Lean name of the hypothesis, name of the axiom, its fact)
    pub hypotheses: Vec<(String, String, FactId)>,
    /// (Twee proof, number in it) -> fact
    block_axioms: HashMap<(usize, String), FactId>,
    block_lemmas: HashMap<(usize, String), FactId>,
    /// fact -> the facts its proof cites
    pub uses: HashMap<FactId, BTreeSet<FactId>>,
    /// fact -> index of the item of the proof file it was built from
    pub item_of: HashMap<FactId, usize>,
    /// fact -> its name in the proof file
    labels: HashMap<FactId, String>,
    counter: usize,
    pub steps: usize,
    rewrites: usize,
    failed_steps: usize,
    pub failures: Vec<String>,
    /// steps that state an existential; they are not checked
    existential: Vec<String>,
    notes: Vec<String>,
    /// names that are used but never proved
    pub assumed: Vec<String>,
}

impl Converter {
    pub fn new(proof: &ProofFile) -> Result<Converter, String> {
        let mut converter = Converter {
            library: Library::default(),
            conjecture: proof.conjecture.clone(),
            out: Vec::new(),
            by_name: HashMap::new(),
            all_facts: Vec::new(),
            axiom_facts: Vec::new(),
            hypotheses: Vec::new(),
            block_axioms: HashMap::new(),
            block_lemmas: HashMap::new(),
            uses: HashMap::new(),
            item_of: HashMap::new(),
            labels: HashMap::new(),
            counter: 0,
            steps: 0,
            rewrites: 0,
            failed_steps: 0,
            failures: Vec::new(),
            existential: Vec::new(),
            notes: Vec::new(),
            assumed: Vec::new(),
        };
        for (i, (name, formula)) in proof.axioms.iter().enumerate() {
            let hypothesis = if proof.axioms.len() == 1 {
                "op_law".to_string()
            } else {
                format!("{}_law", name)
            };
            let (lhs, rhs) = parse_equation(formula)?;
            let fact = converter.library.add(Fact::new(&hypothesis, &lhs, &rhs));
            converter.hypotheses.push((hypothesis, name.clone(), fact));
            converter.axiom_facts.push(fact);
            converter.by_name.insert(name.clone(), fact);
            converter.by_name.insert(format!("a_{}", i + 1), fact);
        }
        Ok(converter)
    }

    fn fact(&self, id: FactId) -> &Fact {
        &self.library.facts[id]
    }

    // ---- looking up premises ------------------------------------------------

    /// The proved fact that a premise refers to. With a formula, the fact must
    /// have it as an instance; the name is then only a first guess.
    fn lookup(&self, name: &str, formula: Option<&str>) -> Option<FactId> {
        let named = [self.by_name.get(name), self.by_name.get(&canon(name))];
        let mut candidates = named.into_iter().flatten().copied();
        let Some(formula) = formula else {
            return candidates.next();
        };
        let (lhs, rhs) = parse_equation(formula).ok()?;
        candidates
            .chain(self.axiom_facts.iter().copied())
            .chain(self.all_facts.iter().rev().copied())
            .find(|&fact| self.library.covers((&lhs, &rhs), fact))
    }

    /// A premise that the file never proves: state it with `sorry`.
    fn assume(&mut self, name: &str, formula: &str) -> Result<FactId, String> {
        self.counter += 1;
        let (lhs, rhs) = parse_equation(formula)?;
        let fact = Fact::new(&format!("assumed_{}", self.counter), &lhs, &rhs);
        let fact = self.library.add(fact);
        self.assumed.push(name.to_string());
        let comment = format!("{}: used but not proved in this file", name);
        self.emit_have(fact, "sorry", &comment);
        self.register(name, fact);
        Ok(fact)
    }

    fn register(&mut self, name: &str, fact: FactId) {
        self.by_name.insert(name.to_string(), fact);
        self.by_name.insert(canon(name), fact);
        self.all_facts.push(fact);
    }

    // ---- emitting -----------------------------------------------------------

    fn emit_have(&mut self, id: FactId, proof: &str, comment: &str) {
        let cited = std::mem::take(&mut self.library.used);
        self.uses.insert(id, cited);
        let label = comment.split(':').next().unwrap_or("").to_string();
        self.labels.insert(id, label);
        let fact = self.fact(id);
        let binder = if fact.vars.is_empty() {
            String::new()
        } else {
            format!(" ({} : G)", fact.vars.join(" "))
        };
        let have = format!(
            "  -- {}\n  have {}{} :\n      {} =\n      {} :=\n    {}\n",
            comment,
            fact.lean_name,
            binder,
            show(&fact.lhs),
            show(&fact.rhs),
            proof
        );
        self.out.push(have);
    }

    fn new_fact(&mut self, lhs: &Term, rhs: &Term) -> FactId {
        self.counter += 1;
        let fact = Fact::new(&format!("lemma_{}", self.counter), lhs, rhs);
        self.library.add(fact)
    }

    fn fail(&mut self, label: &str, why: &str) -> String {
        self.failures.push(format!("{}: {}", label, why));
        self.failed_steps += 1;
        "sorry".to_string()
    }

    fn names(&self, facts: &[FactId]) -> Vec<String> {
        facts
            .iter()
            .map(|&fact| self.fact(fact).lean_name.clone())
            .collect()
    }

    // ---- one superposition line ----------------------------------------------

    fn convert_line(
        &mut self,
        index: usize,
        name: &str,
        formula: &str,
        premises: &[(String, Option<String>)],
    ) -> Result<(), String> {
        if formula.contains('?') {
            // A turned refutation step can be an existential statement. It is
            // not an equation: later steps are checked without it.
            self.steps += 1;
            self.existential.push(name.to_string());
            return Ok(());
        }
        let (lhs, rhs) = parse_equation(formula)?;
        let fact = self.new_fact(&lhs, &rhs);
        self.item_of.insert(fact, index);
        let (mut deps, mut missing) = (Vec::new(), Vec::new());
        for (dep_name, dep_formula) in premises {
            if canon(dep_name) == canon(name) || dep_name.starts_with("conjecture") {
                continue; // the statement itself, not a premise
            }
            match self.lookup(dep_name, dep_formula.as_deref()) {
                None => missing.push(dep_name.clone()), // e.g. a lemma that is only proved later
                Some(dep) if !deps.contains(&dep) => deps.push(dep),
                Some(_) => {}
            }
        }
        self.steps += 1;
        let (lhs, rhs) = (self.fact(fact).lhs.clone(), self.fact(fact).rhs.clone());
        let goal = (&lhs, &rhs);
        let default = self.fact(fact).default_var();
        let mut found = self.library.justify(goal, &deps, &default, true, None);
        if found.is_none() {
            // The list of premises can be incomplete: allow any earlier
            // equation as well, still within a single rewrite.
            self.library.used.clear();
            let earlier = [self.axiom_facts.clone(), self.all_facts.clone()].concat();
            found = self
                .library
                .justify(goal, &earlier, &default, false, None)
                .or_else(|| {
                    self.library
                        .justify(goal, &deps, &default, true, Some(&earlier))
                })
                .or_else(|| self.library.justify(goal, &earlier, &default, true, None));
            if found.is_some() {
                let unlisted: Vec<FactId> = self
                    .library
                    .used
                    .iter()
                    .copied()
                    .filter(|used| !deps.contains(used))
                    .collect();
                let mut extra = self.names(&unlisted);
                extra.sort();
                self.notes.push(format!(
                    "{}: also needs {}, which its dependency list does not mention",
                    name,
                    extra.join(", ")
                ));
            }
        }
        let (proof, how) = match found {
            Some((proof, rewrites, how)) => {
                self.rewrites += rewrites;
                if !missing.is_empty() {
                    self.notes.push(format!(
                        "{}: lists {}, which is not proved before it (not needed)",
                        name,
                        missing.join(", ")
                    ));
                }
                (proof, how)
            }
            None => {
                let listed = [self.names(&deps), missing].concat();
                let listed = if listed.is_empty() {
                    "nothing".to_string()
                } else {
                    listed.join(", ")
                };
                let how = format!("NOT a single rewrite of {}", listed);
                (self.fail(name, &how), how)
            }
        };
        self.emit_have(fact, &proof, &format!("{}: {}", name, how));
        self.register(name, fact);
        Ok(())
    }

    // ---- one Twee lemma or goal ------------------------------------------------

    /// Facts cited by a `by ...` annotation, in the order they are cited.
    fn step_facts(&mut self, block: usize, label: &str, annotation: &str) -> Vec<FactId> {
        let reference = cached_regex(r"(?i)(axiom|lemma)\s+(\d+)(?:\s*\(([^)]+)\))?");
        let mut facts = Vec::new();
        for found in reference.captures_iter(annotation) {
            let (kind, number) = (&found[1], &found[2]);
            let key = (block, number.to_string());
            let fact = if kind.eq_ignore_ascii_case("lemma") {
                self.block_lemmas.get(&key).copied()
            } else {
                let cited = found.get(3).map(|cited| cited.as_str());
                self.block_axioms
                    .get(&key)
                    .copied()
                    .or_else(|| cited.and_then(|cited| self.lookup(cited, None)))
            };
            match fact {
                None => self.failures.push(format!(
                    "{}: unknown reference '{} {}'",
                    label, kind, number
                )),
                Some(fact) if !facts.contains(&fact) => facts.push(fact),
                Some(_) => {}
            }
        }
        facts
    }

    fn convert_chain(&mut self, index: usize, item: &Item) -> Result<(), String> {
        let Item::Chain {
            block,
            number,
            is_lemma,
            name,
            formula,
            terms,
            steps,
        } = item
        else {
            unreachable!("only called for chains");
        };
        let label = if name.is_empty() {
            format!("Lemma {} (block {})", number, block)
        } else {
            name.clone()
        };
        // what a failure inside the chain is reported under
        let short_label = if name.is_empty() {
            format!("Lemma {}", number)
        } else {
            name.clone()
        };
        let (lhs, rhs) = parse_equation(formula)?;
        let fact = self.new_fact(&lhs, &rhs);
        self.item_of.insert(fact, index);
        let mut order = Vec::new();
        term_vars(&lhs, &mut order);
        term_vars(&rhs, &mut order);
        let fresh = &self.fact(fact).vars;
        let mapping: HashMap<String, String> = order.iter().cloned().zip(fresh.clone()).collect();
        let default = self.fact(fact).default_var();
        // variables the prover introduced on the way are instantiated uniformly
        let terms: Vec<Term> = terms
            .iter()
            .map(|term| Ok(rename(&parse_term(term)?, &mapping, Some(&default))))
            .collect::<Result<_, String>>()?;

        let (mut lines, mut notes): (Vec<String>, Vec<String>) = (Vec::new(), Vec::new());
        for (i, annotation) in steps.iter().enumerate() {
            self.steps += 1;
            let facts = self.step_facts(*block, &short_label, annotation);
            let merged = annotation.contains("superposition");
            let (from, to) = match (terms.get(i), terms.get(i + 1)) {
                (Some(from), Some(to)) => (from, to),
                _ => return Err(format!("{}: a rewrite step has no term", label)),
            };
            let found = self
                .library
                .justify((from, to), &facts, &default, merged, None);
            let (proof, how) = match found {
                Some((proof, rewrites, how)) => {
                    self.rewrites += rewrites;
                    (proof, how)
                }
                None => {
                    let how = format!("step {} is NOT a single rewrite ({})", i + 1, annotation);
                    (self.fail(&label, &how), how)
                }
            };
            if !notes.contains(&how) {
                notes.push(how);
            }
            lines.push(format!("      _ = {} :=\n        {}", show(to), proof));
        }

        let (lhs, rhs) = (&self.fact(fact).lhs, &self.fact(fact).rhs);
        let ends = terms.first().zip(terms.last());
        let chain = || format!("calc {}\n{}", show(&terms[0]), lines.join("\n"));
        let proof = if lines.is_empty() {
            self.fail(&label, "no proof steps")
        } else if ends == Some((lhs, rhs)) {
            chain()
        } else if ends == Some((rhs, lhs)) {
            format!("Eq.symm ({})", chain())
        } else {
            self.fail(&label, "the rewrite chain does not connect the two sides")
        };
        let summary = if notes.is_empty() {
            "no steps".to_string()
        } else {
            notes.join("; ")
        };
        let comment = format!("{}: {} steps: {}", label, lines.len(), summary);
        self.emit_have(fact, &proof, &comment);

        if *is_lemma {
            self.block_lemmas.insert((*block, number.clone()), fact);
        }
        if name.is_empty() {
            self.all_facts.push(fact);
        } else {
            self.register(name, fact);
        }
        Ok(())
    }

    // ---- the whole file --------------------------------------------------------

    /// Convert every item; returns the last line of the Lean proof. Afterwards
    /// `library.used` holds the facts that this last line cites.
    pub fn convert(&mut self, items: &[Item]) -> Result<String, String> {
        for (index, item) in items.iter().enumerate() {
            match item {
                Item::Line {
                    name,
                    formula,
                    deps,
                } => self.convert_line(index, name, formula, deps)?,
                Item::Axiom {
                    block,
                    number,
                    name,
                    formula,
                } => {
                    let fact = match self.lookup(name, Some(formula)) {
                        Some(fact) => fact,
                        None => self.assume(name, formula)?,
                    };
                    self.block_axioms.insert((*block, number.clone()), fact);
                }
                Item::Chain { .. } => self.convert_chain(index, item)?,
            }
        }
        self.closing()
    }

    /// The conjecture must be an instance of something that was proved.
    fn closing(&mut self) -> Result<String, String> {
        self.library.used.clear();
        let Some((_, conjecture)) = self.conjecture.clone() else {
            return Ok(match self.all_facts.last() {
                Some(&last) => {
                    self.library.used.insert(last);
                    format!("  {}\n", self.fact(last).lean_name)
                }
                None => "  sorry\n".to_string(),
            });
        };
        let (lhs, rhs) = parse_equation(&conjecture)?;
        let goal = Fact::new("goal", &lhs, &rhs);
        let default = goal.default_var();
        let proved: Vec<FactId> = self.all_facts.iter().rev().copied().collect();
        for fact in [proved, self.axiom_facts.clone()].concat() {
            let proof = self
                .library
                .instance_of((&goal.lhs, &goal.rhs), fact, &default);
            if let Some(proof) = proof {
                return Ok(format!("  fun {} => {}\n", goal.vars.join(" "), proof));
            }
        }
        self.failures
            .push("the conjecture is not an instance of any proved lemma".to_string());
        Ok(format!("  fun {} => sorry\n", goal.vars.join(" ")))
    }

    /// Names of the proved steps that the final theorem does not depend on.
    fn unused(&self) -> Vec<String> {
        let needed = reachable(&self.library.used, &self.uses);
        self.all_facts
            .iter()
            .filter(|fact| !needed.contains(fact))
            .map(|fact| self.labels[fact].clone())
            .collect()
    }
}

/// The facts that `from` depend on, directly or not, including themselves.
pub fn reachable(
    from: &BTreeSet<FactId>,
    uses: &HashMap<FactId, BTreeSet<FactId>>,
) -> BTreeSet<FactId> {
    let mut needed = BTreeSet::new();
    let mut stack: Vec<FactId> = from.iter().copied().collect();
    while let Some(fact) = stack.pop() {
        if needed.insert(fact) {
            stack.extend(uses.get(&fact).into_iter().flatten());
        }
    }
    needed
}

/// A proof as a Lean file.
pub struct Translation {
    pub lean: String,
    /// the number of steps, as the Lean file counts them
    pub steps: usize,
    /// what to tell the user: the step count first, then notes and warnings
    pub messages: Vec<String>,
    /// false if the file contains `sorry`
    pub certified: bool,
}

/// Translate the text of a proof file; `source` is its name, for the header.
pub fn translate(proof_text: &str, source: &str) -> Result<Translation, String> {
    let proof = read_proof(proof_text);
    if proof.axioms.is_empty() {
        return Err("no axiom found in the input problem section".to_string());
    }
    let mut converter = Converter::new(&proof)?;
    let closing = converter.convert(&proof.items)?;
    let unused = converter.unused();

    let plain = converter.steps as i64
        - converter.rewrites as i64
        - converter.failed_steps as i64
        - converter.existential.len() as i64;
    let mut summary = format!(
        "{} proof steps: {} rewrite a subterm, {} only instantiate an earlier equation",
        converter.steps, converter.rewrites, plain
    );
    if !converter.existential.is_empty() {
        summary += &format!(
            ", {} existential (not needed by the Lean proof)",
            converter.existential.len()
        );
    }

    let abbreviation = |name: &str, formula: &str| -> Result<String, String> {
        let (lhs, rhs) = parse_equation(formula)?;
        let fact = Fact::new(name, &lhs, &rhs);
        Ok(format!(
            "abbrev Equation_{} (G : Type _) [Magma G] :=\n  ∀ {} : G, {}\n",
            name,
            fact.vars.join(" "),
            fact.statement()
        ))
    };
    let hypotheses: Vec<String> = converter
        .hypotheses
        .iter()
        .map(|(hypothesis, name, _)| format!("    ({} : Equation_{} G)", hypothesis, name))
        .collect();
    let (conjecture_name, goal_type) = match &proof.conjecture {
        Some((name, _)) => (name.clone(), format!("Equation_{} G", name)),
        None => {
            let last = converter
                .all_facts
                .last()
                .ok_or("the proof file proves nothing")?;
            (
                "no_conjecture".to_string(),
                converter.fact(*last).statement(),
            )
        }
    };

    let mut parts = vec![
        format!("-- Generated by Krympa from {}.\n-- {}.\n", source, summary),
        "set_option linter.unusedVariables false\n".to_string(),
        "class Magma (α : Type _) where\n  op : α → α → α\n".to_string(),
        "infix:65 \" ◇ \" => Magma.op\n".to_string(),
    ];
    for (name, formula) in &proof.axioms {
        parts.push(abbreviation(name, formula)?);
    }
    if let Some((name, formula)) = &proof.conjecture {
        parts.push(abbreviation(name, formula)?);
    }
    parts.push(format!(
        "theorem Equation_{}_implies_Equation_{} (G : Type _) [Magma G]\n{} :\n    {} :=\n{}\n{}",
        proof.axioms[0].0,
        conjecture_name,
        hypotheses.join("\n"),
        goal_type,
        converter.out.join("\n"),
        closing
    ));

    let mut messages = vec![summary];
    for name in unused {
        messages.push(format!(
            "note: {} is proved but nothing depends on it",
            name
        ));
    }
    for note in &converter.notes {
        messages.push(format!("note: {}", note));
    }
    for name in &converter.assumed {
        messages.push(format!(
            "WARNING: {} is used but never proved; stated with `sorry`",
            name
        ));
    }
    for failure in &converter.failures {
        messages.push(format!("WARNING: {}", failure));
    }
    let certified = converter.assumed.is_empty() && converter.failures.is_empty();
    if !certified {
        messages.push("The Lean file contains `sorry`; it does not certify the proof.".to_string());
    }
    Ok(Translation {
        lean: parts.join("\n"),
        steps: converter.steps,
        messages,
        certified,
    })
}

/// Write `proof_file` as `../lean/Proof/<name>.lean` and check it with Lean.
/// Returns the Lean file if Lean accepted it, and what went wrong otherwise.
pub fn export_and_check(proof_file: &str) -> Result<String, String> {
    let path = Path::new(proof_file);
    let text =
        fs::read_to_string(path).map_err(|e| format!("Cannot read {}: {}", proof_file, e))?;
    let source = path.file_name().unwrap_or_default().to_string_lossy();
    let stem = path.file_stem().unwrap_or_default().to_string_lossy();
    let translation = translate(&text, &source)
        .map_err(|problem| format!("The proof could not be translated: {}", problem))?;

    let lean_file = format!("{}/Proof/{}.lean", LEAN_PROJECT, stem);
    fs::create_dir_all(format!("{}/Proof", LEAN_PROJECT)).map_err(|e| e.to_string())?;
    fs::write(&lean_file, &translation.lean)
        .map_err(|e| format!("Cannot write {}: {}", lean_file, e))?;
    for message in &translation.messages {
        crate::klog_info!("[LEAN] {}", message);
    }
    if !translation.certified {
        return Err(format!(
            "{} has steps that are not a single rewrite",
            lean_file
        ));
    }

    let check = Command::new("lean")
        .arg(format!("Proof/{}.lean", stem))
        .current_dir(LEAN_PROJECT)
        .output()
        .map_err(|e| format!("{} written, but `lean` did not start: {}", lean_file, e))?;
    let output = [check.stdout, check.stderr].concat();
    if check.status.success() && output.is_empty() {
        Ok(lean_file)
    } else {
        Err(format!(
            "Lean does not accept {}:\n{}",
            lean_file,
            String::from_utf8_lossy(&output).trim_end()
        ))
    }
}
