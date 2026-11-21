//! Dropping the parts of a segment that the later segments do not use.

use crate::regex_cache::cached_regex;
use std::collections::{BTreeMap, BTreeSet};

/// Returns true iff any proof segment uses the lemma.
/// Accepts any input variant like:
///   small_step_lemma_0060 / big_step_lemma_0060 / abstracted_lemma_0060 / lemma_0060
///   
/// By default we count:
///   - Axiom headers:  "Axiom k (lemma_0060):"
///   - deps mentions:  "deps: ... lemma_0060 ..." (with or without a trailing ':')
///
pub fn proof_uses_lemma(lemma_any_variant: &str, segments: &[&str]) -> bool {
    // extract trailing digits
    let num_re = cached_regex(r"(\d+)\s*$");
    let Some(cap) = num_re.captures(lemma_any_variant.trim()) else {
        return false;
    };
    let num = cap.get(1).unwrap().as_str();

    // allow all variants
    let variants = [
        format!("small_step_lemma_{}", num),
        format!("big_step_lemma_{}", num),
        format!("abstracted_lemma_{}", num),
        format!("lemma_{}", num),
    ];

    // build alternation safely
    let alts = variants
        .iter()
        .map(|n| regex::escape(n))
        .collect::<Vec<_>>()
        .join("|");

    // 1) Present as an axiom: "Axiom 1 (single_lemma_0025): ..."
    let axiom_re = cached_regex(&format!(
        r"(?m)^\s*Axiom\s+\d+\s*\(\s*(?:{})\s*\)\s*:",
        alts
    ));

    // 2) Mentioned in deps (deps-only; does NOT match "% lemma_xxxx:" headers)
    // Handles:
    //   "| deps: lemma_0002, lemma_0003"
    //   "| deps: lemma_0003: <formula>, ..."
    let deps_re = cached_regex(&format!(
        r"(?mi)\|\s*deps\s*:\s*[^|\n]*\b(?:{})\b(?:\s*:)?",
        alts
    ));

    // 3) Proof-step citations (should be handled by the above)
    // Matches:
    //   "= { by axiom 2 (lemma_0003) }"
    //   "= { by lemma 5 (history_lemma_0061) R->L }"
    let cite_re = cached_regex(&format!(
        r"(?mi)\bby\s+(?:axiom|lemma)\s+\d+\s*\(\s*(?:{})\s*\)",
        alts
    ));

    segments
        .iter()
        .any(|s| axiom_re.is_match(s) || deps_re.is_match(s) || cite_re.is_match(s))
}

/// Keep only those lemmas in `block` that are required to derive
/// the lemmas referenced in later segments
pub fn trim_superposition_block(block: &str, later_segments: &[&str]) -> String {
    let header_re = cached_regex(r"(?m)^\s*%\s*===\s*Superposition Steps\s*===\s*$");

    let lemma_line_re =
        cached_regex(r#"(?m)^\s*%\s*([A-Za-z_]*lemma_\d+)\s*:\s*(.*?)\s*(?:\|\s*deps:\s*(.*))?$"#);

    let dep_name_re = cached_regex(r"\b[A-Za-z_]*lemma_\d+\b");

    // parse block order + deps
    let mut order: Vec<String> = Vec::new();
    let mut deps_map: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for line in block.lines() {
        if let Some(cap) = lemma_line_re.captures(line) {
            let name = cap[1].to_string();
            order.push(name.clone());

            let deps_str = cap.get(3).map(|m| m.as_str()).unwrap_or("");
            let mut deps = BTreeSet::new();
            for m in dep_name_re.find_iter(deps_str) {
                deps.insert(m.as_str().to_string());
            }
            deps_map.insert(name, deps);
        }
    }

    if order.is_empty() {
        return block.to_string();
    }

    // roots: lemmas referenced later
    let in_block: BTreeSet<String> = order.iter().cloned().collect();
    let mut needed: BTreeSet<String> = BTreeSet::new();
    for name in &order {
        if proof_uses_lemma(name, later_segments) {
            needed.insert(name.clone());
        }
    }

    if needed.is_empty() {
        return String::new();
    }

    // optional: dependency closure *only to decide last needed point*
    let mut stack: Vec<String> = needed.iter().cloned().collect();
    while let Some(cur) = stack.pop() {
        if let Some(deps) = deps_map.get(&cur) {
            for d in deps {
                if in_block.contains(d) && !needed.contains(d) {
                    needed.insert(d.clone());
                    stack.push(d.clone());
                }
            }
        }
    }

    // IMPORTANT: prefix policy — keep everything up to the last needed lemma
    let mut last_idx: usize = 0;
    for (i, name) in order.iter().enumerate() {
        if needed.contains(name) {
            last_idx = last_idx.max(i);
        }
    }

    // rebuild: keep header + ALL lemma lines with index <= last_idx
    let mut out = String::new();
    let mut idx_map: BTreeMap<String, usize> = BTreeMap::new();
    for (i, n) in order.iter().enumerate() {
        idx_map.insert(n.clone(), i);
    }

    for line in block.lines() {
        if header_re.is_match(line) {
            out.push_str(line);
            out.push('\n');
            continue;
        }

        if let Some(cap) = lemma_line_re.captures(line) {
            let name = cap[1].to_string();
            if idx_map.get(&name).copied().unwrap_or(usize::MAX) <= last_idx {
                out.push_str(line);
                out.push('\n');
            }
        } else {
            // keep blank/comment lines
            if line.trim().is_empty() || line.trim_start().starts_with('%') {
                out.push_str(line);
                out.push('\n');
            }
        }
    }

    out
}

pub fn count_superposition_steps(block: &str) -> usize {
    let lemma_line_re = cached_regex(r"(?m)^\s*%\s*[A-Za-z_]*lemma_\d+\s*:");
    lemma_line_re.find_iter(block).count()
}

// STOP-THE-BLEED: helpers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FreezeBefore {
    None,
    Start,   // don't trim start
    History, // don't trim start + history
    Root,    // don't trim start + history + root
}

/// Match a_2, a_6:, a_26, etc. (no fragile \b word-boundary)
fn has_bleed(text: &str) -> Option<u32> {
    // Require a colon after the number to avoid matching inside other tokens.
    // Also require a word boundary before `a_` so we don't match `lemma_a_0002` etc.
    let re = cached_regex(r"\ba_(\d+)\s*:");
    for cap in re.captures_iter(text) {
        if let Ok(n) = cap[1].parse::<u32>() {
            if n != 1 {
                return Some(n);
            }
        }
    }
    None
}

/// Trims unecessary lemmas in proofs based on segments
/// TODO if start proof is not a superposition block but a Twee proof it doesn't trim it
pub fn trim_proof_parts(
    start: Option<(&str, &str, usize)>, // (start_text, start_proved_by, start_steps)
    history: Option<(&str, &str, &str, usize)>, // (history_name, history_text, history_proved_by, history_steps)
    root: (&str, &str, &str, usize), // (root_name, root_text, root_proved_by, root_steps)
    sub: Option<&str>,
) -> (
    String, // kept_start
    String, // kept_history
    String, // kept_root
    usize,  // start_steps
    usize,  // history_steps
    usize,  // root_steps
) {
    let (root_name, root_proof, root_by, root_steps_in) = root;

    // precompute sub segments (0 or 1 segment)
    let mut sub_segs: Vec<&str> = Vec::new();
    if let Some(s) = sub {
        if !s.trim().is_empty() {
            sub_segs.push(s);
        }
    }

    // If ANY vampire segment is raw (i.e., not our "% === Superposition Steps ===" block),
    // we disable trimming entirely and just return the segments as-is with provided step counts.
    let is_superposition_block = |txt: &str| -> bool {
        txt.lines()
            .any(|l| l.trim() == "% === Superposition Steps ===")
    };

    let any_raw_vampire = (start.is_some()
        && start.as_ref().unwrap().1 == "vampire"
        && !is_superposition_block(start.as_ref().unwrap().0))
        || (history.is_some()
            && history.as_ref().unwrap().2 == "vampire"
            && !is_superposition_block(history.as_ref().unwrap().1))
        || (root_by == "vampire" && !is_superposition_block(root_proof));

    if any_raw_vampire {
        let kept_start = start.map(|(t, _, _)| t.to_string()).unwrap_or_default();
        let kept_history = history
            .map(|(_, t, _, _)| t.to_string())
            .unwrap_or_default();
        let kept_root = root_proof.to_string();

        let start_steps = start.map(|(_, _, s)| s).unwrap_or(0);
        let history_steps = history.map(|(_, _, _, s)| s).unwrap_or(0);
        let root_steps = root_steps_in;

        return (
            kept_start,
            kept_history,
            kept_root,
            start_steps,
            history_steps,
            root_steps,
        );
    }

    // Run trimming once given a freeze level.
    let run = |freeze: FreezeBefore| -> (String, String, String, usize, usize, usize) {
        // helper: keep/trim a named segment
        let keep_named = |name: &str,
                          proof: &str,
                          by: &str,
                          steps_in: usize,
                          segs: &[&str]|
         -> (String, usize) {
            // TERMINAL RULE: if nothing comes after this segment, keep it.
            // (root becomes terminal when sub is absent)
            if segs.is_empty() {
                let kept = proof.to_string();
                let steps = if by == "vampire" {
                    count_superposition_steps(&kept)
                } else {
                    steps_in
                };
                return (kept, steps);
            }

            match by {
                "vampire" => {
                    let trimmed = trim_superposition_block(proof, segs);
                    let steps = count_superposition_steps(&trimmed);
                    (trimmed, steps)
                }
                "twee" => {
                    // if this segment isn't referenced later, drop it
                    if !proof_uses_lemma(name, segs) {
                        return (String::new(), 0);
                    }
                    (proof.to_string(), steps_in)
                }
                _ => (proof.to_string(), steps_in),
            }
        };

        // 1) root depends on sub (if any)
        let (kept_root, root_steps) = if freeze >= FreezeBefore::Root {
            (root_proof.to_string(), root_steps_in)
        } else {
            keep_named(root_name, root_proof, root_by, root_steps_in, &sub_segs)
        };

        // 2) history depends on root + sub
        let (kept_history, history_steps) = match history {
            None => (String::new(), 0),
            Some((h_name, h_proof, h_by, h_steps_in)) => {
                if freeze >= FreezeBefore::History {
                    let kept = h_proof.to_string();
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, h_steps_in)
                    }
                } else {
                    let mut segs: Vec<&str> = Vec::new();
                    if !kept_root.trim().is_empty() {
                        segs.push(&kept_root);
                    }
                    segs.extend(sub_segs.iter().copied());

                    let (kept, steps) = keep_named(h_name, h_proof, h_by, h_steps_in, &segs);
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, steps)
                    }
                }
            }
        };

        // 3) start depends on (history if non-empty) + root + sub
        let (kept_start, start_steps) = match start {
            None => (String::new(), 0),
            Some((start_proof, start_by, start_steps_in)) => {
                if freeze >= FreezeBefore::Start {
                    let kept = start_proof.to_string();
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, start_steps_in)
                    }
                } else {
                    let mut segs: Vec<&str> = Vec::new();
                    if !kept_history.trim().is_empty() {
                        segs.push(&kept_history);
                    }
                    if !kept_root.trim().is_empty() {
                        segs.push(&kept_root);
                    }
                    segs.extend(sub_segs.iter().copied());

                    let (kept, steps) = match start_by {
                        "vampire" => {
                            let trimmed = trim_superposition_block(start_proof, &segs);
                            let steps = count_superposition_steps(&trimmed);
                            (trimmed, steps)
                        }
                        _ => (start_proof.to_string(), start_steps_in),
                    };

                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, steps)
                    }
                }
            }
        };

        (
            kept_start,
            kept_history,
            kept_root,
            start_steps,
            history_steps,
            root_steps,
        )
    };

    // PASS 1: normal trimming
    let first = run(FreezeBefore::None);
    let (ref kept_start_1, ref kept_history_1, ref kept_root_1, _, _, _) = first;

    // Decide freeze based on KEPT segments only (+ SUB, because it's always kept)
    let mut freeze2 = FreezeBefore::None;

    // if SUB has unresolved a_k:, freeze everything
    if freeze2 == FreezeBefore::None {
        if let Some(sub_txt) = sub {
            if !sub_txt.trim().is_empty() {
                if let Some(n) = has_bleed(sub_txt) {
                    freeze2 = FreezeBefore::Root;
                    crate::klog_debug!(
                        "[DEBUG] stop-the-bleed: unresolved a_{} in SUB; freezing trimming of start/history/root",
                        n
                    );
                }
            }
        }
    }

    if freeze2 == FreezeBefore::None {
        if let Some(n) = has_bleed(kept_root_1) {
            freeze2 = FreezeBefore::Root;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT ROOT; freezing trimming of start/history/root",
                n
            );
        }
    }

    if freeze2 == FreezeBefore::None && !kept_history_1.trim().is_empty() {
        if let Some(n) = has_bleed(kept_history_1) {
            freeze2 = FreezeBefore::History;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT HISTORY; freezing trimming of start/history",
                n
            );
        }
    }

    if freeze2 == FreezeBefore::None && !kept_start_1.trim().is_empty() {
        if let Some(n) = has_bleed(kept_start_1) {
            freeze2 = FreezeBefore::Start;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT START; freezing trimming of start",
                n
            );
        }
    }

    // PASS 2: re-run only if needed
    if freeze2 == FreezeBefore::None {
        first
    } else {
        run(freeze2)
    }
}
