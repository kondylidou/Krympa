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

    let mut offset = 1;
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

                // if this arises this is a bug in the DAG. so when the
                // duplicate is in itself. When we have cyclic dependencies.
                // this is a patch
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
                    if let Some((superposition_steps, input_formulas, all_steps)) =
                        extract_superposition_steps(path, &root_formula)
                    {
                        // prepend only the relevant Vampire steps and get the renaming
                        let (proof, renaming) = prepend_superposition_steps(
                            &extra_dependencies,
                            &superposition_steps,
                            &input_formulas,
                            &all_steps,
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

                // we need to push what we already have proved to the extra dependencies for matching
                extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));
                println!("INPUT {:?}", extra_dependencies);

                let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    //None,
                    None,
                    &mut extra_dependencies,
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
                        let (dependencies, superposition_steps, _, input_formulas, all_steps) =
                            match maybe_superposition {
                                Some((deps, steps, ph, ipf, all)) => (deps, steps, ph, ipf, all),
                                None => (
                                    Vec::new(),
                                    BTreeMap::new(),
                                    false,
                                    BTreeMap::new(),
                                    BTreeMap::new(),
                                ),
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
                                // TODO maybe merge dependencies and extra_dependencies?
                                (combined_dep_proof_text.clone(), total_dep_steps)
                            } else {
                                // here the extra_dependencies are empty, we are at the start
                                // we also don't care about renaming because it's the initial superposition steps
                                let (sp_proof_text, renaming) = prepend_superposition_steps(
                                    &extra_dependencies,
                                    &superposition_steps,
                                    &input_formulas,
                                    &all_steps,
                                );
                                extend_with_superposition_steps(
                                    &mut extra_dependencies,
                                    &superposition_steps,
                                    &renaming,
                                );
                                (sp_proof_text, superposition_steps_count)
                            };

                        extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));
                        println!("INPUT {:?}", extra_dependencies);

                        // 6. Compute root_proof
                        let Some((root_proof, root_proof_steps)) = prove_lemma(
                            &input_file,
                            &lemmas_dir,
                            // if use_superposition {
                            //     Some((superposition_steps, input_formulas))
                            // } else {
                            //     None
                            // }, // new superposition steps are in extra dependencies so we don't need them here
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            //vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // if Vampire found the shortest proof then we have the new Vampire lemmas here
                            Some(&root_lemma),
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };
                        println!("INPUT {:?}", extra_dependencies);

                        // 7. Compute sub_proof / conjecture proof
                        let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                            &input_file,
                            &lemmas_dir,
                            // if use_superposition {
                            //     Some((superposition_steps, input_formulas))
                            // } else {
                            //     None
                            // },
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            //vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // the extra dependencies transfer here as axioms
                            None,
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };

                        let (start_proof_final, start_proof_final_steps) = if use_superposition {
                            let trimmed = trim_superposition_block(&start_proof, &[&root_proof, &sub_proof]);
                            let trimmed_steps = count_superposition_steps(&trimmed);
                            (trimmed, trimmed_steps)
                        } else {
                            (start_proof.clone(), start_proof_steps)
                        };

                        // 8. Check whether root lemma is actually used
                        let root_used = proof_uses_lemma(&root_lemma, &[&sub_proof]);

                        // check whether root lemma was actually used in the proof
                        if !root_used {
                            println!(
                                "   [INFO] Root lemma {} not used in conjecture proof — skipping",
                                root_lemma
                            );
                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}",
                                input_content, start_proof_final, sub_proof
                            );

                            // 9. Compute total steps
                            steps_total = start_proof_final_steps + sub_proof_steps;
                        } else {
                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, start_proof_final, root_proof, sub_proof
                            );

                            // 9. Compute total steps
                            steps_total = start_proof_final_steps + root_proof_steps + sub_proof_steps;
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
                            extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));
                            extra_dependencies
                                .push((candidate.to_string(), abstract_formula.clone()));
                            println!("INPUT {:?}", extra_dependencies);

                            // 6. Compute root_proof
                            let Some((root_proof, root_proof_steps)) = prove_lemma(
                                &input_file,
                                &lemmas_dir,
                                None,
                                //vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies,
                                Some(&root_lemma),
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };
                            println!("INPUT {:?}", extra_dependencies);

                            // 7. Compute sub_proof / conjecture proof
                            let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                                &input_file,
                                &lemmas_dir,
                                None,
                                //vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies, // here they might become None as we won't find the abstracted lemma in a Vampire proof(?)
                                None,
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };
                            // 8. Check whether root lemma is actually used
                            let root_used = proof_uses_lemma(&root_lemma, &[&sub_proof]);

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

                let (dependencies, superposition_steps, proved_history, input_formulas, all_steps) =
                    match maybe_superposition {
                        Some((deps, steps, ph, ipf, all)) => (deps, steps, ph, ipf, all),
                        None => (
                            Vec::new(),
                            BTreeMap::new(),
                            false,
                            BTreeMap::new(),
                            BTreeMap::new(),
                        ),
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

                // we need to compare the history proof we found with the existing start proof
                // in case this history lemma was already derived by superposition
                let use_proved_history = if use_superposition && proved_history {
                    // history lemma was already proved
                    false
                } else {
                    // either lemma was not proved or we are not using superposition
                    // and we are proving by dependencies
                    true
                };
                //let use_proved_history = !use_superposition || !proved_history;

                // 4. Build extra_dependencies before prepending
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                // start lemmas
                let (start_proof, start_proof_steps) =
                    if total_dep_steps <= superposition_steps_count && total_dep_steps != 0 {
                        // we don't need to add the dependencies to the extra dependencies
                        // we already have them saved
                        (combined_dep_proof_text.clone(), total_dep_steps)
                    } else {
                        // we build the start proof before adding the new superposition steps
                        // to the extra dependencies. This is because extra dependencies has
                        // to hold axioms for matching.
                        let (sp_proof_text, renaming) = prepend_superposition_steps(
                            &extra_dependencies,  // axioms for matching
                            &superposition_steps, // relevant vamp steps
                            &input_formulas,      // vamp input formulas
                            &all_steps,           // FULL proof graph
                        );
                        // here we add the new superposition steps
                        // to the extra dependencies to use them later
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

                // add the axioms (in this case it will become the conjecture)
                extra_dependencies.push((n_history_lemma.to_string(), n_formula.clone()));
                println!("INPUT {:?}", extra_dependencies);

                // 6. Compute n_history_proof
                let Some((n_history_proof, n_history_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    // if use_superposition {
                    //     Some((superposition_steps, input_formulas)) // TODO maybe this is dupl information and we don't need this
                    // } else {
                    //     None
                    // },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies) // if we don't use superposition the dependencies are here
                    },
                    //vec![(&n_history_lemma, &n_formula)],
                    &mut extra_dependencies, // this now includes the new superposition steps after renaming
                    Some(&n_history_lemma),
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));
                println!("INPUT {:?}", extra_dependencies);

                // 7. Compute root_proof
                let Some((root_proof, root_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    // if use_superposition {
                    //     Some((superposition_steps, input_formulas))
                    // } else {
                    //     None
                    // },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    //vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    Some(&root_lemma),
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };
                println!("INPUT {:?}", extra_dependencies);

                // 8. Compute sub_proof / conjecture proof
                let Some((sub_proof, sub_proof_steps)) = prove_lemma(
                    &input_file,
                    &lemmas_dir,
                    // if use_superposition {
                    //     Some((superposition_steps, input_formulas))
                    // } else {
                    //     None
                    // },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    //vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    None,
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                // 9. Check whether root lemma is actually used
                let root_used = proof_uses_lemma(&root_lemma, &[&sub_proof]);

                let history_used = if use_proved_history && root_used {
                    // history lemma may appear in root_proof or sub_proof
                    proof_uses_lemma(&n_history_lemma, &[&root_proof, &sub_proof])
                } else if use_proved_history && !root_used {
                    // only sub proof matters
                    proof_uses_lemma(&n_history_lemma, &[&sub_proof])
                } else {
                    false
                };

                let (start_proof_final, start_proof_final_steps) = if use_superposition {
                    let trimmed = trim_superposition_block(&start_proof, &[&n_history_proof, &root_proof, &sub_proof]);
                    let trimmed_steps = count_superposition_steps(&trimmed);
                    (trimmed, trimmed_steps)
                } else {
                    (start_proof.clone(), start_proof_steps)
                };

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
                        input_content, start_proof_final, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_final_steps + sub_proof_steps;
                } else if !root_used && history_used {
                    println!(
                        "   [INFO] Root lemma {} not used in the proof — skipping",
                        root_lemma
                    );

                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}",
                        input_content, start_proof_final, n_history_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_final_steps + n_history_proof_steps + sub_proof_steps;
                } else if root_used && !history_used {
                    println!(
                        "   [INFO] History lemma {} not used in the proof — skipping",
                        n_history_lemma
                    );

                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}",
                        input_content, start_proof_final, root_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_final_steps + root_proof_steps + sub_proof_steps;
                } else {
                    // root and history were used
                    annotated_proof = format!(
                        "% === Input Problem ===\n{}\n\n{}{}{}{}",
                        input_content, start_proof_final, n_history_proof, root_proof, sub_proof
                    );

                    // 11. Compute total steps
                    steps_total = start_proof_final_steps
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
                    root_lemma, n_history_lemma, steps_total, start_proof_final_steps
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
/// - `axioms`: existing dependencies, will be extended with new lemmas
/// - `conjecture`: optional lemma/conjecture to prove
pub fn prove_lemma(
    input_file: &str,
    lemmas_dir: &str,
    //    superposition_steps: Option<(BTreeMap<usize, SuperpositionStep>, BTreeMap<usize, String>)>,
    dependencies: Option<&[String]>,    // names
    axioms: &mut Vec<(String, String)>, // (name, formula)
    conjecture: Option<&str>,
) -> Result<Option<(String, usize)>, String> {
    let tmp_path = create_tmp_copy(input_file)?;
    let proofs_dir = "../proofs".to_string();

    // 1. Append dependency lemmas
    if let Some(deps) = dependencies {
        for dep_name in deps {
            let dep_formula = load_lemma(lemmas_dir, dep_name)
                .map_err(|_| format!("Missing lemma {}", dep_name))?;
            append_as_axiom(&tmp_path, &dep_formula, dep_name);
        }
    }

    // 2. Append extra dependencies
    if !axioms.is_empty() {
        for (name, formula) in axioms.iter() {
            append_as_axiom(&tmp_path, formula, name);
        }
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
            let _vp_text = fs::read_to_string(&vampire_proof_file)
                .map_err(|_| "Failed to read Vampire proof file")?;
            //let v_len = proof_length_vampire(&vp_text);

            // prepend superposition steps if they exist
            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let v_len = sp_steps.len();
                if v_len < t_len {
                    let (vp, renaming) =
                        prepend_superposition_steps(axioms, &sp_steps, &input_formulas, &all_steps);
                    extend_with_superposition_steps(axioms, &sp_steps, &renaming);
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

            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let (vp, renaming) =
                    prepend_superposition_steps(axioms, &sp_steps, &input_formulas, &all_steps);
                extend_with_superposition_steps(axioms, &sp_steps, &renaming);
                Some((vp, v_len))
            } else {
                Some((vp_text, v_len))
            }
        }

        // no proof
        (None, false) => None,
    };

    // 8. Fallback: load an existing proof from proofs_dir (only if <= current best)
    let result = match result {
        // we already found a proof in this run (Twee/Vampire)
        Some((best_proof, best_steps)) => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                if fb_steps < best_steps {
                    Some((fb_proof, fb_steps))
                } else {
                    Some((best_proof, best_steps))
                }
            } else {
                Some((best_proof, best_steps))
            }
        }

        // no proof found in this run -> try fallback
        None => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                Some((fb_proof, fb_steps))
            } else {
                None
            }
        }
    };

    // 9. Cleanup temporary file
    let _ = fs::remove_file(&tmp_path);

    Ok(result)
}

fn is_single_or_abstract(name: &str) -> bool {
    name.starts_with("single_lemma_") || name.starts_with("abstract_lemma_")
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

/// Returns true iff any proof segment uses the lemma
/// Accepts any input variant like:
///   history_lemma_0060 / single_lemma_0060 / abstract_lemma_0060 / lemma_0060
/// and searches for any of these variants in the proof
pub fn proof_uses_lemma(name_or_variant: &str, segments: &[&str]) -> bool {
    let num_re = Regex::new(r"(\d+)\s*$").unwrap();
    let Some(cap) = num_re.captures(name_or_variant.trim()) else {
        return false;
    };
    let num = cap.get(1).unwrap().as_str();

    // allow all variants
    let variants = [
        format!("history_lemma_{}", num),
        format!("single_lemma_{}", num),
        format!("abstract_lemma_{}", num),
        format!("lemma_{}", num),
    ];

    // helper: (history_lemma_0060|single_lemma_0060|abstract_lemma_0060|lemma_0060)
    let alts = variants
        .iter()
        .map(|n| regex::escape(n))
        .collect::<Vec<_>>()
        .join("|");

    // 1) As an axiom line: "Axiom 1 (lemma_0005): .
    let axiom_hdr = Regex::new(&format!(
        r"(?m)^\s*Axiom\s+\d+\s*\(\s*(?:{})\s*\)\s*:",
        alts
    ))
    .unwrap();

    // 2) As a superposition/recorded lemma header: "% lemma_0005: ..."
    // or
    // 3) In deps lists:
    //    - your format sometimes uses "deps: lemma_0002, lemma_0003"
    //    - sometimes "deps: lemma_0003: <formula>, ..."
    let recorded_or_deps = Regex::new(&format!(
        r"(?m)^\s*%\s*(?:{})\s*:|\b(?:{})\b\s*:",
        alts, alts
    ))
    .unwrap();

    segments
        .iter()
        .any(|s| axiom_hdr.is_match(s) || recorded_or_deps.is_match(s))
}

/// Keep only those lemmas in `block` that are required to derive
/// the lemmas referenced in later segments
// TODO might needs tuning, keeping out for now
// proof steps might be more due to skipping this
pub fn trim_superposition_block(block: &str, later_segments: &[&str]) -> String {
    let header_re = Regex::new(r"(?m)^\s*%\s*===\s*Superposition Steps\s*===\s*$").unwrap();

    let lemma_line_re =
        Regex::new(r#"(?m)^\s*%\s*([A-Za-z_]*lemma_\d+)\s*:\s*(.*?)\s*(?:\|\s*deps:\s*(.*))?$"#)
            .unwrap();

    let dep_name_re = Regex::new(r"\b[A-Za-z_]*lemma_\d+\b").unwrap();

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
    let lemma_line_re = Regex::new(r"(?m)^\s*%\s*[A-Za-z_]*lemma_\d+\s*:").unwrap();
    lemma_line_re.find_iter(block).count()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Exact regression:
    /// later proof mentions only `lemma_0059` (and `history_lemma_0058`),
    /// but the superposition block must keep the whole dependency chain:
    /// lemma_0059 -> lemma_0055 -> (lemma_0053, lemma_0054)
    #[test]
    fn trim_keeps_dependency_chain() {
        let block = r#"
% lemma_0053: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))) | deps: lemma_0049: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(op(X17,X18),X18),op(X18,op(op(X17,X18),X18))))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0054: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213))) | deps: lemma_0050: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(op(X210,X211),X211),op(X211,op(op(X210,X211),X211))),X213))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18))) | deps: lemma_0053: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))), lemma_0054: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213)))
% lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))) | deps: lemma_0016: op(X10,op(X8,X10)) = op(op(X10,op(X8,X10)),op(op(X9,op(X8,X9)),op(X6,op(op(X7,X8),X6)))), lemma_0052: op(op(X14,X13),X13) = op(op(op(X14,X13),X13),op(X15,op(X13,X15)))
% lemma_0059: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144))) | deps: lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))), lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18)))
% history_lemma_0058: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144))) | deps: lemma_0056: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(op(X144,op(X141,X144)),op(op(X142,op(X141,X142)),op(op(X140,X141),X141)))), lemma_0055: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(X20,op(X18,X20)),op(op(X17,X18),X18)))
"#;

        let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.
Axiom 2 (lemma_0059): op(X, op(Y, X)) = op(op(X, op(Y, X)), op(Z, op(Y, Z))).
"#;

        let seg2 = r#"Goal 1 (conjecture0): ..."#;
        let seg3 = r#"
% lemma_0060: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(X17,X18),X18))) | deps: lemma_0059: op(X19,op(X18,X19)) = op(op(X19,op(X18,X19)),op(op(op(X20,op(X18,X20)),op(X21,op(op(op(X17,X18),X18),X21))),op(op(op(X17,X18),X18),op(X18,op(op(X17,X18),X18))))), lemma_0051: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
% lemma_0061: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(X210,X211),X211),X213))) | deps: lemma_0050: op(X212,op(X211,X212)) = op(op(X212,op(X211,X212)),op(X213,op(op(op(op(X210,X211),X211),op(X211,op(op(X210,X211),X211))),X213))), lemma_0060: op(op(X12,X10),X10) = op(op(op(X12,X10),X10),op(X10,op(op(X11,X10),X10)))
"#;

        let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

        // used
        assert!(trimmed.contains("% lemma_0059:"));
        assert!(trimmed.contains("% history_lemma_0058:"));

        // dependency chain that must be kept even if not mentioned later
        assert!(trimmed.contains("% lemma_0056:"));
        assert!(trimmed.contains("% lemma_0055:"));
        assert!(trimmed.contains("% lemma_0054:"));
        assert!(trimmed.contains("% lemma_0053:"));

        // sanity: should not introduce anything else
        assert!(!trimmed.contains("% lemma_0060:"));
        assert_eq!(count_superposition_steps(&trimmed), 6);
    }

    /// Exact regression:
    /// later proof mentions `lemma_0067` (as a dep of axioms/proof),
    /// which implies we must keep `lemma_0066` even though the final proof never
    /// mentions `lemma_0066` directly
    #[test]
    fn trim_keeps_internal_dep() {
        let block = r#"
% lemma_0066: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(X9,op(op(X7,X8),X9)),op(X6,op(op(X7,X8),X6)))) | deps: lemma_0039: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(op(X9,op(op(X7,X8),X9)),op(X10,op(op(X11,op(X7,X8)),X10))),op(X6,op(op(X7,X8),X6)))), lemma_0063: op(X199,op(X197,X199)) = op(op(X199,op(X197,X199)),op(X198,op(op(X196,X197),X198)))
% lemma_0067: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(X9,op(op(X7,X8),X9))) | deps: lemma_0066: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(op(X9,op(op(X7,X8),X9)),op(X6,op(op(X7,X8),X6)))), lemma_0059: op(X143,op(X141,X143)) = op(op(X143,op(X141,X143)),op(X144,op(X141,X144)))
% lemma_0068: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(X1,op(op(X2,X0),X1)),X0)) | deps: lemma_0008: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,op(op(X3,X0),X4)))), lemma_0067: op(op(X12,op(op(X13,X8),X12)),X8) = op(op(op(X12,op(op(X13,X8),X12)),X8),op(X9,op(op(X7,X8),X9)))
% lemma_0074: op(op(X3,X0),X4) = op(op(X3,X0),X4) | deps: lemma_0068: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(X1,op(op(X2,X0),X1)),X0)), lemma_0008: op(op(X3,X0),X4) = op(op(op(X3,X0),X4),op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,op(op(X3,X0),X4))))
% history_lemma_0058: op(X1052,op(op(X1050,op(op(X1051,X1050),X1050)),X1052)) = X1052 | deps: lemma_0074: op(X1052,op(op(op(X1050,op(op(X1051,X1050),X1050)),X1052),op(op(X1055,op(op(X1056,X1052),X1055)),X1052))) = X1052, lemma_0070: op(op(X1364,op(op(X1365,X1364),X1364)),X1366) = op(op(op(X1364,op(op(X1365,X1364),X1364)),X1366),op(op(X1367,op(op(X1368,X1366),X1367)),X1366))
"#;

        // 3 later segments; only segment 1 mentions history_lemma_0058 / lemma_0059 (axioms).
        // But the superposition liness above show that history_lemma_0058 depends (eventually)
        // on lemma_0068, which depends on lemma_0067, which depends on lemma_0066.
        let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.
Axiom 2 (lemma_0059): op(X, op(Y, X)) = op(op(X, op(Y, X)), op(Z, op(Y, Z))).
"#;

        let seg2 = r#"Goal 1 (conjecture0): ..."#;
        let seg3 = r#"RESULT: Theorem."#;

        let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

        // because later proof uses history_lemma_0058 (axiom), we keep it
        assert!(trimmed.contains("% history_lemma_0058:"));

        // and we must keep the internal chain that leads to it
        assert!(trimmed.contains("% lemma_0068:"));
        assert!(trimmed.contains("% lemma_0067:"));
        assert!(trimmed.contains("% lemma_0066:"));
        assert_eq!(count_superposition_steps(&trimmed), 5);
    }

    /// Exact regression:
    /// Here the superposition block contains lemma_0001..lemma_0008, but the proof
    /// only ever uses lemma_0003 (as axiom 2).
    /// The trimmer must drop lemma_0004..lemma_0008
    #[test]
    fn trim_with_three_segments() {
        let block = r#"% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))) | deps: lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))) | deps: lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))), lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16))))
% lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))) | deps: lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0008: op(X29,op(X27,X29)) = op(op(X29,op(X27,X29)),op(op(X27,op(op(X28,X27),X27)),op(X27,op(op(X27,op(op(X28,X27),X27)),X27)))) | deps: lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))), lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))

"#;

        // Segment 1
        let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0003): op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))).

"#;

        // Segment 2
        let seg2 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).
Axiom 3 (lemma_0002): op(X, op(op(Y, op(op(Z, op(W, X)), Y)), op(W, X))) = X.
Axiom 4 (lemma_0003): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(op(W, op(op(V, Z), W)), Z)).

Lemma 5: op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z))) = op(X, op(Y, X)).
Proof:
  op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 1 (a1) }
  op(op(X, op(op(Y, op(W, op(op(V, Y), W))), X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 2 (lemma_0001) R->L }
  op(X, op(op(Y, op(W, op(op(V, Y), W))), X))
= { by axiom 1 (a1) R->L }
  op(X, op(Y, X))

Goal 1 (history_lemma_0061): x0 = op(x0, x1).
Proof:
  x0
= { by axiom 3 (lemma_0002) R->L }
  op(x0, op(X, x1))
= { by axiom 4 (lemma_0003) R->L }
  op(x0, op(op(X, x1), x1))
= { by lemma 5 }
  op(x0, op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
  op(x0, x1)
"#;

        // Segment 3
        let seg3 = r#"
% === Superposition Steps ===
% lemma_0009: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0010: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))
        "#;

        let trimmed = trim_superposition_block(block, &[seg1, seg2, seg3]);

        assert!(trimmed.contains("% === Superposition Steps ==="));
        assert!(trimmed.contains("% lemma_0001:"));
        assert!(trimmed.contains("% lemma_0002:"));
        assert!(trimmed.contains("% lemma_0003:"));

        // these must be gone (even though they appear after lemma_0003 in the block)
        assert!(!trimmed.contains("% lemma_0004:"));
        assert!(!trimmed.contains("% lemma_0005:"));
        assert!(!trimmed.contains("% lemma_0006:"));
        assert!(!trimmed.contains("% lemma_0007:"));
        assert!(!trimmed.contains("% lemma_0008:"));
        assert_eq!(count_superposition_steps(&trimmed), 3);
    }

    /// Exact regression:
    /// Here the superposition block contains lemma_0001..lemma_0005, but the proof
    /// only ever uses lemma_0003
    #[test]
    fn trim_two_segments() {
        let block = r#"% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0)) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63 | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0))
% lemma_0005: op(X2,op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(op(X4,op(op(X5,X2),X4)),X2))) = X2 | deps: lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
"#;

        // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
        let seg1 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).
Axiom 3 (lemma_0002): op(X, op(op(Y, op(op(Z, op(W, X)), Y)), op(W, X))) = X.
Axiom 4 (lemma_0003): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(op(W, op(op(V, Z), W)), Z)).

Lemma 5: op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z))) = op(X, op(Y, X)).
Proof:
  op(op(X, op(Y, X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 1 (a1) }
  op(op(X, op(op(Y, op(W, op(op(V, Y), W))), X)), op(Z, op(op(W, op(op(V, Y), W)), Z)))
= { by axiom 2 (lemma_0001) R->L }
  op(X, op(op(Y, op(W, op(op(V, Y), W))), X))
= { by axiom 1 (a1) R->L }
  op(X, op(Y, X))

"#;

        // Segment 3: the final goal proof — still no lemma_0004..0008 usage
        let seg3 = r#"RESULT: Theorem (the conjecture is true)."#;

        let trimmed = trim_superposition_block(block, &[seg1, seg3]);

        assert!(trimmed.contains("% === Superposition Steps ==="));
        assert!(trimmed.contains("% lemma_0001:"));
        assert!(trimmed.contains("% lemma_0002:"));
        assert!(trimmed.contains("% lemma_0003:"));

        // these must be gone (even though they appear after lemma_0003 in the block)
        assert!(!trimmed.contains("% lemma_0004:"));
        assert!(!trimmed.contains("% lemma_0005:"));
        assert!(!trimmed.contains("% lemma_0006:"));
        assert!(!trimmed.contains("% lemma_0007:"));
        assert!(!trimmed.contains("% lemma_0008:"));
        assert_eq!(count_superposition_steps(&trimmed), 3);
    }
}