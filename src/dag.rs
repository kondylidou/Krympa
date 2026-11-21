use crate::alpha_match::*;
use crate::regex_cache::cached_regex;
use crate::utils::*;
use std::collections::VecDeque;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

type DependencyGraph = BTreeMap<String, BTreeSet<String>>;
type FormulaMap = BTreeMap<String, String>;

/// Parse DAG from file
pub fn load_dag(dag_file: &str) -> DependencyGraph {
    let content = fs::read_to_string(dag_file).expect("Failed to read DAG file");
    let re = cached_regex(r"^\s*(\S+)\s*->\s*\{([^}]*)\}");
    let mut dag = BTreeMap::new();
    for line in content.lines() {
        if let Some(cap) = re.captures(line) {
            let parent = cap[1].to_string();
            let children_str = cap[2].trim();
            let mut children = BTreeSet::new();
            if !children_str.is_empty() {
                for c in children_str.split(',') {
                    children.insert(c.trim().trim_matches('"').to_string());
                }
            }
            dag.insert(parent, children);
        }
    }
    dag
}

/// Write DAG to file
pub fn write_dag(dag_file: &str, dag: &DependencyGraph) -> Result<(), std::io::Error> {
    let mut output = String::new();
    for (parent, children) in dag.iter() {
        let children_str = children
            .iter()
            .map(|c| format!("\"{}\"", c))
            .collect::<Vec<_>>()
            .join(", ");

        output.push_str(&format!("{parent} -> {{{children_str}}}\n"));
    }
    fs::write(dag_file, output)
}

/// Build DAG from precomputed lemmas
pub fn build_dag(
    root_lemma: &str,
    precomputed: &PrecomputedLemmas,
) -> Result<(DependencyGraph, FormulaMap), String> {
    let PrecomputedLemmas {
        all_lemmas,
        all_twee,
        lemmas,
    } = precomputed;

    // build DAG
    let mut dag: DependencyGraph = BTreeMap::new();
    let mut duplicates: Vec<(String, String)> = Vec::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();

    queue.push_back(root_lemma.to_string());

    while let Some(lemma) = queue.pop_front() {
        // built-in axiom
        if lemma.starts_with('a') {
            continue;
        }
        // conjecture dependency
        if lemma.starts_with("conjecture_") {
            continue;
        }
        if seen.contains(&lemma) {
            continue;
        }
        seen.insert(lemma.clone());

        let lemma_info = all_lemmas
            .get(&lemma)
            .ok_or_else(|| format!("Lemma {} not found in precomputed lemmas", lemma))?;

        // check if the lemma itself is a duplicate of a TWEE lemma
        let mut redirected = false;
        for twee_dep in all_twee {
            let twee_name = &twee_dep.name;
            let twee_formula = &twee_dep.formula;
            if formulas_match(&lemma_info.formula, twee_formula)
                && formulas_match(twee_formula, &lemma_info.formula)
            {
                crate::klog_debug!("[DUPLICATE] lemma {} duplicates {}", lemma, twee_name);
                duplicates.push((lemma.clone(), twee_name.clone()));

                // redirect to smallest parent
                let smallest_parent = twee_dep
                    .parents
                    .iter()
                    .min_by_key(|p| {
                        p.chars()
                            .filter(|c| c.is_ascii_digit())
                            .collect::<String>()
                            .parse::<u32>()
                            .unwrap_or(u32::MAX)
                    })
                    .expect("Duplicate TWEE lemma has no parents");

                // add DAG edges
                // get the dependencies of the smallest parent
                if let Some(parent_info) = all_lemmas.get(smallest_parent) {
                    dag.entry(smallest_parent.clone()).or_default().extend(
                        parent_info
                            .dependencies
                            .iter()
                            .map(|(dep_name, _)| dep_name.clone()),
                    );
                }

                queue.push_back(smallest_parent.clone());
                redirected = true;
                break;
            }
        }

        // handle dependencies
        for (dep_name, dep_formula) in &lemma_info.dependencies {
            if dep_name.starts_with("twee_") {
                continue;
            } // skip twee dependencies

            let mut is_duplicate = false;
            for twee_dep in all_twee {
                let twee_name = &twee_dep.name;
                let twee_formula = &twee_dep.formula;
                if formulas_match(dep_formula, twee_formula)
                    && formulas_match(twee_formula, dep_formula)
                {
                    crate::klog_debug!("[DUPLICATE] dep {} duplicates {}", dep_name, twee_name);
                    duplicates.push((dep_name.clone(), twee_name.clone()));
                    is_duplicate = true;

                    // redirect DAG edges to the smallest parent
                    let smallest_parent = twee_dep
                        .parents
                        .iter()
                        .min_by_key(|p| {
                            p.chars()
                                .filter(|c| c.is_ascii_digit())
                                .collect::<String>()
                                .parse::<u32>()
                                .unwrap_or(u32::MAX)
                        })
                        .expect("TWEE dep has no parents");

                    // get the dependencies of the smallest parent
                    if let Some(parent_info) = all_lemmas.get(smallest_parent) {
                        dag.entry(smallest_parent.clone()).or_default().extend(
                            parent_info
                                .dependencies
                                .iter()
                                .map(|(dep_name, _)| dep_name.clone()),
                        );
                    }

                    // continue traversal from parent
                    if !seen.contains(smallest_parent) {
                        queue.push_back(smallest_parent.clone());
                    }
                    break;
                }
            }

            if !is_duplicate && !redirected {
                // normal DAG entry
                dag.entry(lemma.clone())
                    .or_default()
                    .insert(dep_name.clone());

                // also add all dependencies of this dep, if available
                if let Some(dep_info) = all_lemmas.get(dep_name) {
                    dag.entry(dep_name.clone())
                        .or_default()
                        .extend(dep_info.dependencies.iter().map(|(child, _)| child.clone()));
                }

                if !seen.contains(dep_name) {
                    queue.push_back(dep_name.clone());
                }
            }
        }
    }

    Ok((dag, lemmas.clone()))
}

#[derive(Debug)]
pub struct PrecomputedLemmas {
    pub all_lemmas: BTreeMap<String, LemmaInfo>,
    pub all_twee: Vec<TweeDependency>,
    pub lemmas: BTreeMap<String, String>,
}

#[derive(Clone, Debug)]
pub struct LemmaInfo {
    pub formula: String,
    pub dependencies: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
pub struct TweeDependency {
    pub name: String,
    pub formula: String,
    pub parents: Vec<String>,
}

// TODO optimization: precomputed lemmas takes the lemmas as they are in the proofs dir.
// we mix Vampire and Twee there. But here this is very Twee based so it would be good
// if we could take the shortest Twee proof as well and put it inside the precomputed lemmas.
// This would optimize. Ideally and a full fix would be to mix and match Vampire and Twee proofs
// depending on which is shorter for each lemma. But that is more complex to implement.
// In this way we would maybe find different proof paths that are shorter overall.
// (or just different, we cannot know if shorter yet)
// benchmark for this: benchmarks/input9/Equation3957_implies_Equation3971.p
// or prove these children by superposition as already tried
pub fn precompute_lemmas(
    proofs_dir: &str,
    lemmas_dir: &str,
    twee_proofs_dir: &str,
) -> Result<PrecomputedLemmas, String> {
    let mut all_lemmas: BTreeMap<String, LemmaInfo> = BTreeMap::new();
    let mut existing_lemmas: BTreeMap<String, String> = BTreeMap::new();
    let mut lemmas: BTreeMap<String, String> = BTreeMap::new();
    let mut all_twee: Vec<TweeDependency> = Vec::new();
    let mut next_index = 2;

    // precompute all lemmas
    for entry in fs::read_dir(proofs_dir).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let path = entry.path();
        if path.is_dir() {
            continue;
        }

        // canonical lemma name (remove _twee/_vampire)
        let lemma_name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .ok_or("Invalid proof file name")?
            .trim_end_matches("_twee")
            .trim_end_matches("_vampire")
            .to_string();

        // path to TWEE version
        let new_path = Path::new(twee_proofs_dir).join(format!("{}_twee.proof", lemma_name));
        let proof_content = match fs::read_to_string(&new_path) {
            Ok(c) => c,
            Err(_) => {
                // no twee proof for this lemma; register it with empty dependencies
                let formula = load_lemma(lemmas_dir, &lemma_name)?;
                all_lemmas.insert(
                    lemma_name,
                    LemmaInfo {
                        formula,
                        dependencies: Vec::new(),
                    },
                );
                continue;
            }
        };

        // extract dependencies
        let extracted = parse_used_lemmas(&proof_content, lemmas_dir, proofs_dir)?; // Vec<(name, formula)>
        let extracted_twee = extract_twee_lemmas(&proof_content); // Vec<(name, formula)>

        let mut dependencies: Vec<(String, String)> = Vec::new();
        for (dep_name, dep_formula) in extracted {
            dependencies.push((dep_name.clone(), dep_formula.clone()));
            lemmas.insert(dep_name, dep_formula);
        }

        // handle TWEE lemmas
        for (_twee_name, twee_formula) in extracted_twee {
            let key = normalize_formula_alpha(&twee_formula);
            let canonical_name = existing_lemmas
                .entry(key.clone())
                .or_insert_with(|| {
                    let name = format!("twee_lemma_{:02}", next_index);
                    next_index += 1;
                    name
                })
                .clone();

            // add parent if exists or create new
            if let Some(existing) = all_twee.iter_mut().find(|t| t.name == canonical_name) {
                if !existing.parents.contains(&lemma_name) {
                    existing.parents.push(lemma_name.clone());
                }
            } else {
                all_twee.push(TweeDependency {
                    name: canonical_name.clone(),
                    formula: twee_formula.clone(),
                    parents: vec![lemma_name.clone()],
                });
            }
            lemmas.insert(canonical_name.clone(), twee_formula.clone());
            dependencies.push((canonical_name, twee_formula));
        }

        let formula = load_lemma(lemmas_dir, &lemma_name)?;
        all_lemmas.insert(
            lemma_name.clone(),
            LemmaInfo {
                formula,
                dependencies,
            },
        );
    }

    Ok(PrecomputedLemmas {
        all_lemmas,
        all_twee,
        lemmas,
    })
}

/// Parse used lemmas from twee output and return their formulas
pub fn parse_used_lemmas(
    twee_output: &str,
    lemmas_dir: &str,
    proofs_dir: &str,
) -> Result<Vec<(String, String)>, String> {
    let axiom_re = cached_regex(r"Axiom\s+\d+\s+\(([^)]+)\)\s*:\s*(.+)");
    let goal_re = cached_regex(r"Goal\s+\d+\s+\(([^)]+)\)\s*:\s*(.+)");

    let mut used = Vec::new();

    for line in twee_output.lines() {
        // axioms
        if let Some(cap) = axiom_re.captures(line) {
            let name = cap[1].to_string();
            let formula = cap[2].trim().to_string();

            if name.starts_with('a') {
                used.push((name.clone(), formula.clone()));
                continue;
            }

            if name.starts_with("lemma_") {
                if let Some(actual) = select_actual_lemma(proofs_dir, &name) {
                    let clean = strip_prover_suffix(&actual);
                    let dep_formula = load_lemma(lemmas_dir, &clean)?;
                    used.push((clean, dep_formula));
                } else {
                    crate::klog_warn!("[WARN] No proof file found for {}", name);
                }
                continue;
            }

            if name.starts_with("conjecture_") {
                continue;
            }

            // any other symbol
            used.push((name.clone(), formula.clone()));
            continue;
        }

        // goals
        if let Some(cap) = goal_re.captures(line) {
            let name = cap[1].to_string();

            if name.starts_with("lemma_") {
                if let Some(actual) = select_actual_lemma(proofs_dir, &name) {
                    let clean = strip_prover_suffix(&actual);
                    let dep_formula = load_lemma(lemmas_dir, &clean)?;
                    used.push((clean, dep_formula));
                } else {
                    crate::klog_warn!("[WARN] No proof file found for {}", name);
                }
            }
        }
    }
    // deterministic order
    used.sort();
    Ok(used)
}
