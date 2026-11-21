//! Reading a proof file written by `minimize` (`output/proof_<name>.out`): the
//! input problem, followed by superposition lines and Twee proofs.

use crate::regex_cache::cached_regex;

pub const TWEE_MARKER: &str = "The conjecture is true! Here is a proof";
pub const STEPS_HEADER: &str = "% === Superposition Steps ===";

/// One entry of a proof file, in the order of the file.
#[derive(Debug, Clone)]
pub enum Item {
    /// `% name: equation | deps: ...`, one Vampire inference
    Line {
        name: String,
        formula: String,
        /// premises, each with its equation if the line spells it out
        deps: Vec<(String, Option<String>)>,
    },
    /// `Axiom n (name): equation`, an equation a Twee proof starts from
    Axiom {
        block: usize,
        number: String,
        name: String,
        formula: String,
    },
    /// `Goal n (name): equation` or `Lemma n: equation` with its rewrite chain
    Chain {
        block: usize,
        number: String,
        is_lemma: bool,
        name: String,
        formula: String,
        /// the terms of the chain; one more than there are steps
        terms: Vec<String>,
        /// the `by ...` annotation of each step
        steps: Vec<String>,
    },
}

impl Item {
    pub fn name(&self) -> &str {
        match self {
            Item::Line { name, .. } | Item::Axiom { name, .. } | Item::Chain { name, .. } => name,
        }
    }

    pub fn formula(&self) -> &str {
        match self {
            Item::Line { formula, .. }
            | Item::Axiom { formula, .. }
            | Item::Chain { formula, .. } => formula,
        }
    }

    pub fn is_line(&self) -> bool {
        matches!(self, Item::Line { .. })
    }
}

#[derive(Debug, Default)]
pub struct ProofFile {
    /// (name, formula) of the axioms of the input problem
    pub axioms: Vec<(String, String)>,
    pub conjecture: Option<(String, String)>,
    pub items: Vec<Item>,
}

/// `small_step_lemma_0021`, `big_step_lemma_0021`, `conjecture_0021` -> `lemma_0021`.
pub fn canon(name: &str) -> String {
    let name = name.trim();
    if name.starts_with("twee_") {
        return name.to_string();
    }
    match cached_regex(r"^(?:[A-Za-z]+_)*?(?:lemma|conjecture)_(\d+)$").captures(name) {
        Some(found) => format!("lemma_{}", &found[1]),
        None => name.to_string(),
    }
}

/// `name: formula, name, name: formula + name` -> [(name, formula if given)].
fn parse_deps(text: &str) -> Vec<(String, Option<String>)> {
    let name = cached_regex(r"\b(a_?\d+|(?:[A-Za-z]+_)*lemma_\d+|conjecture\w*)\b");
    let found: Vec<_> = name.find_iter(text).collect();
    let mut deps = Vec::new();
    for (i, dep) in found.iter().enumerate() {
        let end = found.get(i + 1).map_or(text.len(), |next| next.start());
        let rest = text[dep.end()..end].trim();
        let formula = rest
            .strip_prefix(':')
            .map(|formula| formula.trim().trim_end_matches([',', '+']).trim())
            .filter(|formula| !formula.is_empty())
            .map(str::to_string);
        deps.push((dep.as_str().to_string(), formula));
    }
    deps
}

pub fn read_proof(text: &str) -> ProofFile {
    let fof_re = cached_regex(r"(?s)^fof\(\s*(\w+)\s*,\s*(\w+)\s*,(.*)\)\s*\.$");
    let line_re = cached_regex(r"^%\s*([A-Za-z_]\w*)\s*:\s*(.*)$");
    let axiom_re = cached_regex(r"^Axiom\s+(\d+)\s+\(([^)]+)\)\s*:\s*(.*)$");
    let chain_re = cached_regex(r"^(Goal|Lemma)\s+(\d+)(?:\s*\(([^)]+)\))?\s*:\s*(.*)$");
    let step_re = cached_regex(r"^=\s*\{\s*by\s+(.*?)\s*\}\s*$");

    let mut proof = ProofFile::default();
    let mut fof: Option<String> = None;
    let mut block = 0;
    // the chain being read inside a Twee proof, and whether its statement is
    // still being read (it can span several lines before `Proof:`)
    let mut current: Option<Item> = None;
    let mut in_header = false;

    for raw in text.lines() {
        let line = raw.trim();

        if fof.is_some() || line.starts_with("fof(") {
            let formula = match fof.take() {
                Some(begun) => format!("{} {}", begun, line),
                None => line.to_string(),
            };
            if !formula.ends_with(").") {
                fof = Some(formula);
                continue;
            }
            if let Some(found) = fof_re.captures(&formula) {
                let entry = (found[1].to_string(), found[3].trim().to_string());
                if &found[2] == "axiom" {
                    proof.axioms.push(entry);
                } else if found[2].contains("conjecture") {
                    proof.conjecture = Some(entry);
                }
            }
            continue;
        }

        if line.starts_with(TWEE_MARKER) {
            proof.items.extend(current.take());
            block += 1;
            continue;
        }

        if line.starts_with('%') {
            if let Some(found) = line_re.captures(line) {
                proof.items.extend(current.take());
                let (body, deps) = found[2].split_once("| deps:").unwrap_or((&found[2], ""));
                proof.items.push(Item::Line {
                    name: found[1].to_string(),
                    formula: body.trim().to_string(),
                    deps: parse_deps(deps),
                });
            }
            continue;
        }

        if line.is_empty() {
            continue;
        }

        if let Some(found) = axiom_re.captures(line) {
            proof.items.extend(current.take());
            proof.items.push(Item::Axiom {
                block,
                number: found[1].to_string(),
                name: found[2].trim().to_string(),
                formula: found[3].to_string(),
            });
            continue;
        }

        if let Some(found) = chain_re.captures(line) {
            proof.items.extend(current.take());
            current = Some(Item::Chain {
                block,
                number: found[2].to_string(),
                is_lemma: &found[1] == "Lemma",
                name: found
                    .get(3)
                    .map_or("", |name| name.as_str())
                    .trim()
                    .to_string(),
                formula: found[4].to_string(),
                terms: Vec::new(),
                steps: Vec::new(),
            });
            in_header = true;
            continue;
        }

        if line.starts_with("RESULT") {
            proof.items.extend(current.take());
            continue;
        }

        let Some(Item::Chain {
            formula,
            terms,
            steps,
            ..
        }) = current.as_mut()
        else {
            continue;
        };
        if line == "Proof:" {
            in_header = false;
            terms.push(String::new());
        } else if in_header {
            formula.push(' ');
            formula.push_str(line);
        } else if let Some(found) = step_re.captures(line) {
            steps.push(found[1].to_string());
            terms.push(String::new());
        } else if let Some(term) = terms.last_mut() {
            term.push(' ');
            term.push_str(line);
        }
    }
    proof.items.extend(current.take());
    proof
}
