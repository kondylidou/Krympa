use crate::dag::*;
use crate::extract_suffix;
use crate::prover_wrapper::*;
use crate::run_vamp::run_vampire;
use crate::superpose::*;
use crate::utils::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

/// Tries several candidate root lemmas and picks the best
pub fn try_minimize(
    input_file: &str,
    vampire_file: &str,
    summary_file: &str,
) -> Result<String, String> {
    let lemmas_dir = "../lemmas".to_string();
    let proofs_dir = "../proofs".to_string();
    let twee_proofs_dir = "../proofs/twee_tmp".to_string();
    let input_content = fs::read_to_string(&input_file)
        .map_err(|e| format!("Failed to read input file {}: {}", input_file, e))?;

    let suffix = extract_suffix(input_file);
    let dag_with_suffix = format!("../output/dag_{}.txt", suffix);
    let lemmas_with_suffix = format!("../output/lemmas_{}.p", suffix);
    let proof_with_suffix = format!("../output/proof_{}.out", suffix);

    let summary_data: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&summary_file).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;

    let max_key = summary_data
        .as_object()
        .ok_or("summary.json should contain an object")?
        .keys()
        .filter_map(|k| k.parse::<u32>().ok())
        .max()
        .ok_or("summary.json is empty")?;

    let mut global_best: Option<(
        usize,  // lemma_count
        usize,  // steps_total
        String, // root_lemma
        String, // best_history
        String, // annotated_proof
        String, // dag_text
        String, // lemmas_text
    )> = None;

    // precompute lemmas
    let precomputed = precompute_lemmas(&proofs_dir, &lemmas_dir, &twee_proofs_dir)?;

    let mut offset = 4;
    let mut accepted = 0;
    let max_candidates = 4;

    while accepted < max_candidates && offset < max_key {
        let key = (max_key - offset).to_string();
        offset += 1;

        // check if key exists in summary_data
        let entry = match summary_data.get(&key) {
            Some(e) => e,
            None => {
                // key not found in summary, skipping.
                continue;
            }
        };

        let root_lemma = entry[0].as_str().ok_or("Bad summary.json format")?;

        // skip lemmas containing Skolem constants
        let skolem_re = Regex::new(r"\bsK\d+\b").unwrap();
        let root_formula = load_lemma(&lemmas_dir, root_lemma)
            .map_err(|_| format!("Missing lemma {}", root_lemma))?;
        if skolem_re.is_match(&root_formula) {
            println!(
                "[DEBUG] Skipping root lemma {} due to Skolem constants in formula: {}",
                root_lemma, root_formula
            );
            // skipping lemma because it contains Skolem constants
            continue;
        }

        // valid root lemma
        accepted += 1;

        println!("\n[INFO] Root lemma {}", root_lemma);

        // build the minimal dag
        let (dag, lemmas) = build_dag(&root_lemma, &precomputed)?;
        let dag_file = "../output/tmp_dag.txt";
        write_dag(dag_file, &dag).map_err(|e| e.to_string())?;

        let lemmas_out_path = "../output/tmp_lemmas.p";
        let mut lemmas_txt = String::new();
        for (lemma_name, formula) in &lemmas {
            lemmas_txt.push_str(&format!(
                "fof({}, lemma,\n    {}\n).\n\n",
                lemma_name, formula
            ));
        }
        fs::write(&lemmas_out_path, lemmas_txt)
            .map_err(|e| format!("Failed to write {}: {}", lemmas_out_path, e))?;

        // collect all history candidates which appear before the root
        let root_index_str = root_lemma.rsplit('_').next().unwrap(); // "0016"
                                                                     // (steps_total, history_lemma, annotated_proof)
        let mut local_best: Option<(usize, Option<String>, String)> = None;
        let mut candidates: Vec<String> = dag
            .keys()
            .filter(|k| k.starts_with("history_"))
            .filter(|k| k.rsplit('_').next().unwrap() < root_index_str)
            .cloned()
            .collect();

        // collect all nodes: keys + all children
        let mut all_nodes: BTreeSet<String> = BTreeSet::new();
        for (parent, children) in &dag {
            all_nodes.insert(parent.clone());
            for child in children {
                all_nodes.insert(child.clone());
            }
        }
        let lemma_count = all_nodes.len();

        // fallback to single and abstract lemmas if empty

        // Two cases: the root can depend on single/abstract lemmas or the root itself is single/abstract
        if candidates.is_empty() {
            // extend the candidates with single and abstract lemmas
            // this can cause the root to be in the candidates too so we exclude it
            candidates.extend(
                dag.keys()
                    .filter(|k| {
                        (k.starts_with("single_lemma_") || k.starts_with("abstract_lemma_"))
                            && k != &root_lemma
                    })
                    .cloned(),
            );
            // if no single or abstract lemmas are present either, fallback to root-only proof
            // this is the second case: the root itself is single/abstract
            if candidates.is_empty() {
                let root_deps = dag.get(root_lemma).cloned().unwrap_or_default();
                let has_history_dependency = root_deps.iter().any(|d| d.starts_with("history_"));

                // TODO this is a bug in the DAG. so when the duplicate is in itself. When
                // we have cyclic dependencies. this is a patch. fix later!
                if candidates.is_empty() && has_history_dependency {
                    println!(
                        "   [BUG] Root {} depends on history {:?} — refusing root-only proof",
                        root_lemma, root_deps
                    );
                    continue; // skipping this now
                }
                println!(
                    "   [INFO] No history or single lemmas found — falling back to root-only proof"
                );

                // vector to collect new Vampire lemmas (names + formulas)
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                let actual_file = select_actual_lemma(&proofs_dir, root_lemma)
                    .ok_or_else(|| format!("No proof file found for root {}", root_lemma))?;
                // try different variants
                let ext = [
                    format!("{}/{}.proof", proofs_dir, actual_file),
                    format!("{}/{}_twee.proof", proofs_dir, actual_file),
                    format!("{}/{}_vampire.proof", proofs_dir, actual_file),
                ];

                let path = ext.iter().find(|p| Path::new(p).exists()).ok_or_else(|| {
                    format!("No proof file found for root {} in any variant", root_lemma)
                })?;

                let mut root_proof = fs::read_to_string(path)
                    .map_err(|_| format!("Cannot read proof file {}", path))?;

                let prover = actual_file
                    .rsplit('_')
                    .next()
                    .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
                    .split('.')
                    .next()
                    .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
                    .to_string();

                // handle Vampire-specific prepending
                let root_proof_steps = if prover == "vampire" {
                    if let Some((superposition_steps, idx)) =
                        extract_superposition_steps(path, root_lemma)
                    {
                        // prepend only the relevant Vampire steps and get the renaming
                        let (proof, renaming) = prepend_superposition_steps(
                            &superposition_steps,
                            &extra_dependencies,
                            Some(&root_lemma),
                            Some(idx),
                        );
                        extend_with_superposition_steps(
                            &mut extra_dependencies,
                            &superposition_steps,
                            &renaming,
                        );
                        root_proof = proof;
                        superposition_steps.len()
                    } else {
                        // fallback if extraction fails
                        proof_length(&prover, &root_proof)
                    }
                } else {
                    // Twee proof
                    proof_length(&prover, &root_proof)
                };

                let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    None,
                    None,
                    vec![(root_lemma, &root_formula)],
                    &mut extra_dependencies, // we don't need them cause we don't prove anything else
                    None,
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                let annotated_proof = format!(
                    "% === Input Problem ===\n{}\n\n{}{}",
                    input_content, root_proof, sub_proof
                );

                let steps_total = root_proof_steps + sub_proof_steps;

                // root-only fallback:
                local_best = Some((steps_total, None, annotated_proof));
            } else {
                // basically here we are trying to prove the root from its single or abstract dependecies.
                // this is the first case: the root depends on single/abstract lemmas
                println!(
                    "   [INFO] No history lemmas found — falling back to {} single lemmas",
                    candidates.len()
                );

                for candidate in &candidates {
                    println!(
                        "   [INFO] Trying single/abstract candidate {} of {}",
                        candidate,
                        candidates.len()
                    );

                    let mut annotated_proof = String::new();
                    let mut steps_total = 0;

                    // check whether candidate is single or abstract
                    let is_single = candidate.starts_with("single_lemma_");
                    let is_abstract = candidate.starts_with("abstract_lemma_");

                    // if we are falling back to single lemmas the superposition logic or indirect
                    // dependency proving logic will prove this directly. This means we will have
                    // to fall back in the 'no history used' logic below.
                    if is_single {
                        // 1. Get superposition steps
                        // get the lemma derived by superposition directly from Vampire proof
                        // in this case we are just proving the single lemma directly
                        let maybe_superposition =
                            superposition_steps(dag_file, vampire_file, &lemmas_dir, candidate);
                        // in dependencies we will get itself (the single lemma)
                        // in this case we can ignore proved_history
                        let (dependencies, superposition_steps, lemma, idx, _) =
                            match maybe_superposition {
                                Some((deps, steps, lemma, idx, ph)) => {
                                    (deps, steps, lemma, idx, ph)
                                }
                                None => (vec![], BTreeMap::new(), None, None, false),
                            };
                        let superposition_steps_count = superposition_steps.len();

                        // 2. Load dependency proofs
                        // load the proof of the single lemma
                        let dep_proofs = load_all_dependency_proofs(&proofs_dir, &dependencies)?;
                        // count the proof steps for the single lemma directly proven from the base axioms
                        let total_dep_steps: usize =
                            dep_proofs.iter().map(|(_, _, steps, _)| *steps).sum();
                        // combine all dependency proofs text (here this is probably useless since it's just one)
                        let combined_dep_proof_text = dep_proofs
                            .iter()
                            .map(|(_, _, _, text)| text.clone())
                            .collect::<Vec<_>>()
                            .join("\n\n"); // separate proofs by blank lines

                        // 3. Decide which source to use
                        let use_superposition = if total_dep_steps == 0 {
                            // no DAG dependencies -> must use superposition
                            true
                        } else {
                            // DAG dependencies exist -> use superposition only if it's shorter or equal
                            superposition_steps_count > 0
                                && superposition_steps_count <= total_dep_steps
                        };

                        // 4. Collect extra dependencies
                        let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                        // start lemmas
                        let (start_proof, start_proof_steps) =
                            if total_dep_steps <= superposition_steps_count && total_dep_steps != 0
                            {
                                // we don't need to add anything to extra_dependencies
                                // TODO maybe merge dependencies and extra_dependencies
                                (combined_dep_proof_text.clone(), total_dep_steps)
                            } else {
                                // here the extra_dependencies are empty, we are at the start
                                // we also don't care about renaming because it's the initial superposition steps
                                let (sp_proof_text, renaming) = prepend_superposition_steps(
                                    &superposition_steps,
                                    &Vec::new(),
                                    lemma.as_deref(),
                                    idx,
                                );
                                extend_with_superposition_steps(
                                    &mut extra_dependencies,
                                    &superposition_steps,
                                    &renaming,
                                );
                                (sp_proof_text, superposition_steps_count)
                            };

                        // 6. Compute root_proof
                        let Some((root_proof, root_proof_steps)) = prove_lemma(
                            &input_file,
                            &lemmas_dir,
                            if use_superposition {
                                Some(&superposition_steps)
                            } else {
                                None
                            },
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // if Vampire found the shortest proof then we have the new Vampire lemmas here
                            Some(&root_lemma),
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };

                        // 7. Compute sub_proof / conjecture proof
                        let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                            &input_file,
                            &lemmas_dir,
                            if use_superposition {
                                Some(&superposition_steps)
                            } else {
                                None
                            },
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // the extra dependencies transfer here as axioms
                            None,
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };

                        // 8. Check whether root lemma is actually used
                        let root_used = proof_uses_lemma(&sub_proof, &root_lemma);

                        // check whether root lemma was actually used in the proof
                        if !root_used {
                            println!(
                                "   [INFO] Root lemma {} not used in conjecture proof — skipping",
                                root_lemma
                            );
                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}",
                                input_content, start_proof, sub_proof
                            );

                            // 9. Compute total steps
                            steps_total = start_proof_steps + sub_proof_steps;
                        } else {
                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, start_proof, root_proof, sub_proof
                            );

                            // 9. Compute total steps
                            steps_total = start_proof_steps + root_proof_steps + sub_proof_steps;
                        }
                    }
                    // if we fall back to an abstract candidate we will have to prove
                    // it with Twee, we won't find it in the superposition steps.
                    else if is_abstract {
                        // 6. Compute (in this case find) root_proof
                        // construct the expected file path for the twee proof
                        let path = Path::new(&proofs_dir).join(format!("{}_twee.proof", candidate));

                        if path.exists() {
                            let abstract_proof = fs::read_to_string(&path).map_err(|_| {
                                format!("Cannot read proof file {}", path.display())
                            })?;

                            // extract prover
                            let prover = "twee".to_string();
                            let abstract_proof_steps = proof_length(&prover, &abstract_proof);

                            // load the formula of the abstracted lemma
                            let abstract_formula = match load_lemma(&lemmas_dir, candidate) {
                                Ok(f) => f,
                                Err(err) => {
                                    eprintln!(
                                        "     [WARN] Cannot load {}: {}. Skipping.",
                                        candidate, err
                                    );
                                    continue; // skip missing lemmas
                                }
                            };
                            // vector to collect new Vampire lemmas
                            let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                            // 6. Compute root_proof
                            let Some((root_proof, root_proof_steps)) = prove_lemma(
                                &input_file,
                                &lemmas_dir,
                                None,
                                None,
                                vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies,
                                Some(&root_lemma),
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };

                            // 7. Compute sub_proof / conjecture proof
                            let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                                &input_file,
                                &lemmas_dir,
                                None,
                                None,
                                vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies, // here they might become None as we won't find the abstracted lemma in a Vampire proof(?)
                                None,
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };
                            // 8. Check whether root lemma is actually used
                            let root_used = proof_uses_lemma(&sub_proof, &root_lemma);

                            // check whether root lemma was actually used in the proof
                            if !root_used {
                                println!(
                                    "   [INFO] Root lemma {} not used in conjecture proof — skipping",
                                    root_lemma
                                );
                                annotated_proof = format!(
                                    "% === Input Problem ===\n{}\n\n{}{}",
                                    input_content, abstract_proof, sub_proof
                                );

                                // 9. Compute total steps
                                steps_total = abstract_proof_steps + sub_proof_steps;
                            } else {
                                annotated_proof = format!(
                                    "% === Input Problem ===\n{}\n\n{}{}{}",
                                    input_content, abstract_proof, root_proof, sub_proof
                                );

                                // 9. Compute total steps
                                steps_total =
                                    abstract_proof_steps + root_proof_steps + sub_proof_steps;
                            }
                        } else {
                            println!(
                                "   [WARN] Abstract lemma {} proof file does not exist, skipping",
                                candidate
                            );
                            continue; // skip this candidate if proof is missing
                        }
                    }
                    // single/history fallback:
                    // update local best
                    local_best = match local_best {
                        None => Some((steps_total, Some(candidate.clone()), annotated_proof)),
                        Some((best_steps, _, _)) => {
                            if steps_total < best_steps {
                                Some((steps_total, Some(candidate.clone()), annotated_proof))
                            } else {
                                local_best
                            }
                        }
                    };
                }
            }
        }
        // from now on we have history candidates
        else {
            // loop over all history candidates
            for n_history_lemma in &candidates {
                if n_history_lemma == &root_lemma {
                    println!(
                        "[INFO] Skipping history {} because it is the root lemma",
                        n_history_lemma
                    );
                    continue;
                }
                println!(
                    "   [INFO] Trying history candidate {} of {}",
                    n_history_lemma,
                    candidates.len()
                );

                // 1. Get superposition steps
                // get the lemma derived by superposition directly from Vampire proof
                let maybe_superposition =
                    superposition_steps(dag_file, vampire_file, &lemmas_dir, n_history_lemma);

                let (dependencies, superposition_steps, lemma, idx, proved_history) =
                    match maybe_superposition {
                        Some((deps, steps, lemma, idx, ph)) => (deps, steps, lemma, idx, ph),
                        None => (vec![], BTreeMap::new(), None, None, false),
                    };
                let superposition_steps_count = superposition_steps.len();

                // If the history lemma is proved by superposition, the
                // dependencies vector will be empty. This means that we need to
                // compare the length of the history lemma proof with the
                // superposition steps The below code doesn't bother us cause
                // dependencies are empty and superposition will be chosen as
                // start proof.

                // check if it's already proven
                if dependencies.contains(n_history_lemma) {
                    println!(
                        "[INFO] Skipping {} because it's already proven via superposition/dependencies",
                        n_history_lemma
                    );
                    continue;
                }

                if proved_history && !dependencies.is_empty() {
                    return Err("[ERROR] {} is already proven via superposition, dependencies should have been empty!!".into());
                }

                // 2. Load dependency proofs
                // load all dependency proofs and sum their steps
                let dep_proofs = load_all_dependency_proofs(&proofs_dir, &dependencies)?;
                // count the steps for all the dependencies
                let total_dep_steps: usize = dep_proofs.iter().map(|(_, _, steps, _)| *steps).sum();
                // combine all dependency proofs text
                let combined_dep_proof_text = dep_proofs
                    .iter()
                    .map(|(_, _, _, text)| text.clone())
                    .collect::<Vec<_>>()
                    .join("\n\n"); // separate proofs by blank lines

                // 3. Decide which source to use
                let use_superposition = if total_dep_steps == 0 {
                    // no DAG dependencies -> must use superposition
                    true
                } else {
                    // DAG dependencies exist -> use superposition only if it's shorter or equal
                    superposition_steps_count > 0 && superposition_steps_count <= total_dep_steps
                };

                // 4. Build extra_dependencies before prepending
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                // start lemmas
                let (start_proof, start_proof_steps) =
                    if total_dep_steps <= superposition_steps_count && total_dep_steps != 0 {
                        (combined_dep_proof_text.clone(), total_dep_steps)
                    } else {
                        let (sp_proof_text, renaming) = prepend_superposition_steps(
                            &superposition_steps,
                            &Vec::new(),
                            lemma.as_deref(),
                            idx,
                        );
                        extend_with_superposition_steps(
                            &mut extra_dependencies,
                            &superposition_steps,
                            &renaming,
                        );
                        (sp_proof_text, superposition_steps_count)
                    };

                // 4. Load n_history formula
                let n_formula = load_lemma(&lemmas_dir, &n_history_lemma)
                    .map_err(|_| format!("Missing lemma {}", n_history_lemma))?;

                // 6. Compute n_history_proof
                let Some((n_history_proof, n_history_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    if use_superposition {
                        Some(&superposition_steps)
                    } else {
                        None
                    },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    vec![(&n_history_lemma, &n_formula)],
                    &mut extra_dependencies,
                    Some(&n_history_lemma),
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };
                // we need to compare the history proof we found with the existing start proof
                // in case this history lemma was already derived by superposition.
                let mut use_proved_history = false;
                if proved_history {
                    if n_history_proof_steps <= superposition_steps_count {
                        use_proved_history = false;
                    } else {
                        use_proved_history = true;
                    };
                }

                // 7. Compute root_proof
                let Some((root_proof, root_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    if use_superposition {
                        Some(&superposition_steps)
                    } else {
                        None
                    },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    Some(&root_lemma),
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                // 8. Compute sub_proof / conjecture proof
                let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    if use_superposition {
                        Some(&superposition_steps)
                    } else {
                        None
                    },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    None,
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                // 9. Check whether root lemma is actually used
                let root_used = proof_uses_lemma(&sub_proof, &root_lemma);
                let history_used;
                if !use_proved_history && root_used {
                    // 9.1. Check whether history lemma is used in the root proof
                    // or in the sub proof
                    history_used = proof_uses_lemma(&root_proof, &n_history_lemma)
                        || proof_uses_lemma(&sub_proof, &n_history_lemma);
                } else if !use_proved_history && !root_used {
                    // 9.2. Check whether history lemma is used in the sub proof
                    history_used = proof_uses_lemma(&sub_proof, &n_history_lemma);
                } else {
                    // avoid proving the history lemma twice
                    history_used = false;
                }
                // 10. Annotate all proofs
                let annotated_proof;
                let steps_total;
                if !root_used && !history_used {
                    println!(
                        "   [INFO] Root {} and history lemma {} not used in the proof — skipping",
                        root_lemma, n_history_lemma
                    );

                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}",
                        input_content, start_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_steps + sub_proof_steps;
                } else if !root_used && history_used {
                    println!(
                        "   [INFO] Root lemma {} not used in the proof — skipping",
                        root_lemma
                    );

                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}",
                        input_content, start_proof, n_history_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_steps + n_history_proof_steps + sub_proof_steps;
                } else if root_used && !history_used {
                    println!(
                        "   [INFO] History lemma {} not used in the proof — skipping",
                        n_history_lemma
                    );

                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}",
                        input_content, start_proof, root_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_steps + root_proof_steps + sub_proof_steps;
                } else {
                    // root and history were used
                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}{}",
                        input_content, start_proof, n_history_proof, root_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_steps
                        + n_history_proof_steps
                        + root_proof_steps
                        + sub_proof_steps;
                }

                println!("   [PROOOF-------------------------------------------------------] ");
                println!("   [PROOOF] {}", annotated_proof);
                // update local_best
                local_best = match local_best {
                    None => Some((steps_total, Some(n_history_lemma.clone()), annotated_proof)),
                    Some((best_steps, _, _)) => {
                        if steps_total < best_steps {
                            Some((steps_total, Some(n_history_lemma.clone()), annotated_proof))
                        } else {
                            local_best
                        }
                    }
                };

                println!(
                    "   [INFO] Candidate root {} with history {} requires {} total steps with {} initial superposition steps",
                    root_lemma, n_history_lemma, steps_total, start_proof_steps
                );
            }
        }
        // update global_best
        if let Some((steps_total, best_history, annotated_proof)) = local_best {
            let dag_text = fs::read_to_string("../output/tmp_dag.txt")
                .map_err(|e| format!("Failed to read tmp_dag.txt: {}", e))?;

            let lemmas_text = fs::read_to_string("../output/tmp_lemmas.p")
                .map_err(|e| format!("Failed to read tmp_lemmas.p: {}", e))?;

            global_best = match global_best {
                None => Some((
                    lemma_count,
                    steps_total,
                    root_lemma.to_string(),
                    best_history.unwrap_or_default(), // <- unwrap Option<String>,
                    annotated_proof,
                    dag_text,
                    lemmas_text,
                )),
                Some((b_lemmas, b_steps, _, _, _, _, _)) => {
                    if steps_total < b_steps || (lemma_count == b_lemmas && steps_total < b_steps) {
                        Some((
                            lemma_count,
                            steps_total,
                            root_lemma.to_string(),
                            best_history.unwrap_or_default(), // <- unwrap Option<String>,
                            annotated_proof,
                            dag_text,
                            lemmas_text,
                        ))
                    } else {
                        global_best
                    }
                }
            };
        }
    }
    if let Some((_, steps, root, n_history, annotated_proof, dag_text, lemmas_text)) = &global_best
    {
        println!("\n[RESULT] Best combination found:");
        println!("[RESULT] Root lemma: {}", root);
        println!("[RESULT] History lemma: {}", n_history);
        println!("[RESULT] Total steps: {}", steps);
        let vampire_steps = match fs::read_to_string(&vampire_file) {
            Ok(content) => proof_length("vampire", &content),
            Err(_) => 0,
        };
        println!("[RESULT] Initial proof steps: {}", vampire_steps);

        fs::write(dag_with_suffix.clone(), dag_text).map_err(|e| e.to_string())?;
        fs::write(lemmas_with_suffix.clone(), lemmas_text).map_err(|e| e.to_string())?;
        fs::write(proof_with_suffix.clone(), annotated_proof).map_err(|e| e.to_string())?;
    } else {
        return Err("No valid root/history candidate combination found.".into());
    }

    // cleanup temporary files
    let _ = fs::remove_file("../output/tmp_dag.txt");
    let _ = fs::remove_file("../output/tmp_lemmas.p");

    Ok("Minimization complete".into())
}

/// Proves a lemma using Twee and Vampire, selecting the shorter proof.
/// - `superposition_steps`: optional superposition steps to append
/// - `dependencies`: optional dependencies (lemma names)
/// - `axioms`: additional axioms to append
/// - `extra_dependencies`: existing dependencies, will be extended with new lemmas
/// - `conjecture`: optional lemma/conjecture to prove
pub fn prove_lemma(
    input_file: &str,
    lemmas_dir: &str,
    superposition_steps: Option<&BTreeMap<usize, SuperpositionStep>>,
    dependencies: Option<&[String]>,                // names
    axioms: Vec<(&str, &str)>,                      // (name, formula)
    extra_dependencies: &mut Vec<(String, String)>, // (name, formula)
    conjecture: Option<&str>,
) -> Result<Option<(String, usize)>, String> {
    let tmp_path = create_tmp_copy(input_file)?;

    // 1. Append superposition steps if provided
    if let Some(sp_steps) = superposition_steps {
        append_superposition_steps_as_lemmas(&tmp_path, sp_steps, lemmas_dir)?;
    }

    // 2. Append dependency lemmas
    if let Some(deps) = dependencies {
        for dep_name in deps {
            let dep_formula = load_lemma(lemmas_dir, dep_name)
                .map_err(|_| format!("Missing lemma {}", dep_name))?;
            append_as_axiom(&tmp_path, &dep_formula, dep_name);
        }
    }

    // 3. Append extra dependencies
    if !extra_dependencies.is_empty() {
        for (name, formula) in extra_dependencies.iter() {
            append_as_axiom(&tmp_path, formula, name);
        }
    }

    // 4. Append additional axioms
    if !axioms.is_empty() {
        for (name, formula) in axioms.iter() {
            append_as_axiom(&tmp_path, formula, name);
        }
    }

    // 5. Handle conjecture
    let (c_name, c_formula) = if let Some(s) = conjecture {
        let s = s.to_string();
        promote_axiom_to_conjecture(&tmp_path, &s)?;
        let formula = load_lemma(lemmas_dir, &s).map_err(|_| format!("Cannot load lemma {}", s))?;
        (s, formula)
    } else {
        let formula = extract_conjecture_from_file(input_file)?;
        ("conjecture".to_string(), formula)
    };

    // 6. Run provers
    let twee_proof = run_twee(&tmp_path);
    let vampire_proof_file = format!("{}.vampire_proof", tmp_path);
    run_vampire(&tmp_path, &vampire_proof_file);
    let vampire_proof_exists = Path::new(&vampire_proof_file).exists();

    // 7. Select shorter proof
    let result = match (twee_proof, vampire_proof_exists) {
        // Twee + Vampire available
        (Some(tp), true) => {
            let t_len = proof_length_twee(&tp);

            // read Vampire proof text
            let vp_text = fs::read_to_string(&vampire_proof_file)
                .map_err(|_| "Failed to read Vampire proof file")?;
            //let v_len = proof_length_vampire(&vp_text);

            // TODO should we compare the proof by contradiction or the direct derivation?
            // prepend superposition steps if they exist
            if let Some((sp_steps, idx)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let v_len = sp_steps.len();
                if v_len < t_len {
                    let (vp, renaming) = prepend_superposition_steps(
                        &sp_steps,
                        extra_dependencies,
                        Some(&c_name),
                        Some(idx),
                    );
                    extend_with_superposition_steps(extra_dependencies, &sp_steps, &renaming);
                    Some((vp, v_len))
                } else {
                    // we will do a fallback here to be revised TODO
                    // if we for some reason cannot extract superposition steps we will
                    // fall back to the Twee proof
                    Some((tp, t_len))
                }
            } else {
                Some((tp, t_len))
            }
        }

        // Twee only
        (Some(tp), false) => Some((tp.clone(), proof_length_twee(&tp))),

        // Vampire only
        (None, true) => {
            let vp_text = fs::read_to_string(&vampire_proof_file)
                .map_err(|_| "Failed to read Vampire proof file")?;
            let v_len = proof_length_vampire(&vp_text);

            if let Some((sp_steps, idx)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let (vp, renaming) = prepend_superposition_steps(
                    &sp_steps,
                    extra_dependencies,
                    Some(&c_name),
                    Some(idx),
                );
                extend_with_superposition_steps(extra_dependencies, &sp_steps, &renaming);
                Some((vp, v_len))
            } else {
                Some((vp_text, v_len))
            }
        }

        // no proof
        (None, false) => None,
    };

    // 8. Cleanup temporary file
    let _ = fs::remove_file(&tmp_path);

    Ok(result)
}

// AS NEEDS FIXING how lemmas are saved in the proof.. derived idx etc
// TODO this needs fixing!
/// Checks if a proof uses a lemma (Twee or Vampire)
pub fn proof_uses_lemma(proof: &str, lemma_name: &str) -> bool {
    proof.lines().any(|line| {
        let line = line.trim();

        // Twee match
        if line.contains(lemma_name)
            || line.contains(&format!("({},", lemma_name))
            || line.contains(&format!(" {} ", lemma_name))
        {
            return true;
        }

        // Vampire match (we assume its always a match cause of how Vampire works)
        if line.contains("[input]") {
            return true;
        }

        true
    })
}
