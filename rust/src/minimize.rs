use crate::alpha_match::formulas_match;
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

    let mut offset = 0;
    let mut accepted = 0;
    let max_candidates = 5;

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
                let conjecture = extract_conjecture_from_file(input_file)?;
                if formulas_match(&root_formula, &conjecture)
                    || formulas_match(&conjecture, &root_formula)
                {
                    println!("   [INFO] Main theorem is root {} — skipping", root_lemma);
                    // don't re prove the main theorem
                    continue;
                }

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
                let (root_proof_steps, _root_proved_by) = if prover == "vampire" {
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
                        (superposition_steps.len(), "vampire".to_string())
                    } else {
                        // fallback if extraction fails
                        (proof_length(&prover, &root_proof), "fallback".to_string())
                    }
                } else {
                    // Twee proof
                    (proof_length(&prover, &root_proof), "twee".to_string())
                };

                // we need to push what we already have proved to the extra dependencies for matching
                extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));

                let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
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
                        let (start_proof, start_proof_steps, start_proved_by) = if total_dep_steps
                            < superposition_steps_count
                            && total_dep_steps != 0
                        {
                            // we don't need to add anything to extra_dependencies
                            // TODO maybe merge dependencies and extra_dependencies?
                            (
                                combined_dep_proof_text.clone(),
                                total_dep_steps,
                                "fallback".to_string(),
                            )
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
                            (
                                sp_proof_text,
                                superposition_steps_count,
                                "vampire".to_string(),
                            )
                        };

                        extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));

                        // 6. Compute root_proof
                        let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
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

                        // 7. Compute sub_proof / conjecture proof
                        let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
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

                        let conjecture = extract_conjecture_from_file(input_file)?;
                        if formulas_match(&root_formula, &conjecture)
                            || formulas_match(&conjecture, &root_formula)
                        {
                            println!("   [INFO] Main theorem is root {} — skipping", root_lemma);
                            let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                                trim_proof_parts(
                                    Some((&start_proof, &start_proved_by, start_proof_steps)),
                                    None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                    (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                    None,
                                );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}",
                                input_content, kept_start, kept_root
                            );

                            // 8. Compute total steps
                            steps_total = kept_start_steps + kept_root_steps;
                        } else {
                            let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                                trim_proof_parts(
                                    Some((&start_proof, &start_proved_by, start_proof_steps)),
                                    None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                    (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                    Some(&sub_proof),
                                );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, kept_start, kept_root, sub_proof
                            );

                            // 8. Compute total steps
                            steps_total = kept_start_steps + kept_root_steps + sub_proof_steps;
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

                            // 6. Compute root_proof
                            let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
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

                            // 7. Compute sub_proof / conjecture proof
                            let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
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

                            let conjecture = extract_conjecture_from_file(input_file)?;
                            if formulas_match(&root_formula, &conjecture)
                                || formulas_match(&conjecture, &root_formula)
                            {
                                println!(
                                    "   [INFO] Main theorem is root {} — skipping",
                                    root_lemma
                                );
                                // the goal was to prove something more abstract by dependencies, I doubt that in this case it will
                                // be helpful but let's TODO
                                continue;
                            }

                            let (
                                kept_abstract,
                                _,
                                kept_root,
                                kept_abstract_steps,
                                _,
                                kept_root_steps,
                            ) = trim_proof_parts(
                                Some((&abstract_proof, &prover, abstract_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                Some(&sub_proof),
                            );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, kept_abstract, kept_root, sub_proof
                            );

                            // 8. Compute total steps
                            steps_total = kept_abstract_steps + kept_root_steps + sub_proof_steps;
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
                let prove_history = if use_superposition && proved_history {
                    // history lemma was already proved
                    false
                } else {
                    // either lemma was not proved or we are not using superposition
                    // and we are proving by dependencies
                    true
                };

                // 4. Build extra_dependencies before prepending
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                // start lemmas
                let (start_proof, start_proof_steps, start_proved_by) =
                    if total_dep_steps < superposition_steps_count && total_dep_steps != 0 {
                        // we don't need to add the dependencies to the extra dependencies
                        // we already have them saved
                        (
                            combined_dep_proof_text.clone(),
                            total_dep_steps,
                            "fallback".to_string(),
                        )
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
                        (
                            sp_proof_text,
                            superposition_steps_count,
                            "vampire".to_string(),
                        )
                    };

                // 4. Load n_history formula
                let n_formula = load_lemma(&lemmas_dir, &n_history_lemma)
                    .map_err(|_| format!("Missing lemma {}", n_history_lemma))?;

                // add the axioms (in this case it will become the conjecture)
                extra_dependencies.push((n_history_lemma.to_string(), n_formula.clone()));

                // 6. Compute n_history_proof
                let Some((n_history_proof, n_history_proof_steps, n_history_proved_by)) =
                    prove_lemma(
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

                // 7. Compute root_proof
                let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
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

                // 8. Compute sub_proof / conjecture proof
                let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
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

                // 9. Annotate all proofs
                let annotated_proof;
                let steps_total;
                if !prove_history {
                    println!(
                        "   [INFO] History lemma {} already proved — skipping",
                        n_history_lemma
                    );

                    let conjecture = extract_conjecture_from_file(input_file)?;
                    if formulas_match(&root_formula, &conjecture)
                        || formulas_match(&conjecture, &root_formula)
                    {
                        // in this case here if root is the main theorem and we also have proved history
                        // we remain with start and root
                        println!("   [INFO] Main theorem is root {} — skipping", root_lemma);

                        let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                            trim_proof_parts(
                                Some((&start_proof, &start_proved_by, start_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                None,
                            );

                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}",
                            input_content, kept_start, kept_root
                        );

                        // 10. Compute total steps
                        steps_total = kept_start_steps + kept_root_steps;
                    } else {
                        let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                            trim_proof_parts(
                                Some((&start_proof, &start_proved_by, start_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                Some(&sub_proof),
                            );

                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}",
                            input_content, kept_start, kept_root, sub_proof
                        );

                        // 10. Compute total steps
                        steps_total = kept_start_steps + kept_root_steps + sub_proof_steps;
                    }
                } else {
                    let conjecture = extract_conjecture_from_file(input_file)?;
                    if formulas_match(&root_formula, &conjecture)
                        || formulas_match(&conjecture, &root_formula)
                    {
                        println!("   [INFO] Main theorem is root {} — skipping", root_lemma);

                        let (
                            kept_start,
                            kept_history,
                            kept_root,
                            kept_start_steps,
                            kept_history_steps,
                            kept_root_steps,
                        ) = trim_proof_parts(
                            Some((&start_proof, &start_proved_by, start_proof_steps)),
                            Some((
                                n_history_lemma,
                                &n_history_proof,
                                &n_history_proved_by,
                                n_history_proof_steps,
                            )),
                            (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                            None,
                        );

                        // root and history were used
                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}",
                            input_content, kept_start, kept_history, kept_root
                        );

                        // 11. Compute total steps
                        steps_total = kept_start_steps + kept_history_steps + kept_root_steps;
                    } else {
                        let (
                            kept_start,
                            kept_history,
                            kept_root,
                            kept_start_steps,
                            kept_history_steps,
                            kept_root_steps,
                        ) = trim_proof_parts(
                            Some((&start_proof, &start_proved_by, start_proof_steps)),
                            Some((
                                n_history_lemma,
                                &n_history_proof,
                                &n_history_proved_by,
                                n_history_proof_steps,
                            )),
                            (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                            Some(&sub_proof),
                        );

                        // root and history were used
                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}{}",
                            input_content, kept_start, kept_history, kept_root, sub_proof
                        );

                        // 11. Compute total steps
                        steps_total = kept_start_steps
                            + kept_history_steps
                            + kept_root_steps
                            + sub_proof_steps;
                    }
                }

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
/// - `axioms`: existing dependencies, will be extended with new lemmas
/// - `conjecture`: optional lemma/conjecture to prove
pub fn prove_lemma(
    input_file: &str,
    lemmas_dir: &str,
    //    superposition_steps: Option<(BTreeMap<usize, SuperpositionStep>, BTreeMap<usize, String>)>,
    dependencies: Option<&[String]>,    // names
    axioms: &mut Vec<(String, String)>, // (name, formula)
    conjecture: Option<&str>,
) -> Result<Option<(String, usize, String)>, String> {
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
    let result: Option<(String, usize, String)> = match (twee_proof, vampire_proof_exists) {
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
                    Some((vp, v_len, "vampire".to_string()))
                } else {
                    Some((tp, t_len, "twee".to_string()))
                }
            } else {
                Some((tp, t_len, "twee".to_string()))
            }
        }

        // Twee only
        (Some(tp), false) => {
            let t_len = proof_length_twee(&tp);
            Some((tp, t_len, "twee".to_string()))
        }

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
                Some((vp, v_len, "vampire".to_string()))
            } else {
                Some((vp_text, v_len, "vampire".to_string()))
            }
        }

        // no proof
        (None, false) => None,
    };

    // 8. Fallback: load an existing proof from proofs_dir (only if <= current best)
    let result: Option<(String, usize, String)> = match result {
        Some((best_proof, best_steps, best_by)) => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                if fb_steps < best_steps {
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
                Some((fb_proof, fb_steps, "fallback".to_string()))
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

/// Returns true iff any proof segment uses the lemma.
/// Accepts any input variant like:
///   history_lemma_0060 / single_lemma_0060 / abstract_lemma_0060 / lemma_0060
///
/// By default we count:
///   - Axiom headers:  "Axiom k (lemma_0060):"
///   - deps mentions:  "deps: ... lemma_0060 ..." (with or without a trailing ':')
///
pub fn proof_uses_lemma(lemma_any_variant: &str, segments: &[&str]) -> bool {
    // extract trailing digits
    let num_re = Regex::new(r"(\d+)\s*$").unwrap();
    let Some(cap) = num_re.captures(lemma_any_variant.trim()) else {
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

    // build alternation safely
    let alts = variants
        .iter()
        .map(|n| regex::escape(n))
        .collect::<Vec<_>>()
        .join("|");

    // 1) Present as an axiom: "Axiom 1 (single_lemma_0025): ..."
    let axiom_re = Regex::new(&format!(
        r"(?m)^\s*Axiom\s+\d+\s*\(\s*(?:{})\s*\)\s*:",
        alts
    ))
    .unwrap();

    // 2) Mentioned in deps (deps-only; does NOT match "% lemma_xxxx:" headers)
    // Handles:
    //   "| deps: lemma_0002, lemma_0003"
    //   "| deps: lemma_0003: <formula>, ..."
    let deps_re = Regex::new(&format!(
        r"(?mi)\|\s*deps\s*:\s*[^|\n]*\b(?:{})\b(?:\s*:)?",
        alts
    ))
    .unwrap();

    // 3) Proof-step citations (should be handled by the above)
    // Matches:
    //   "= { by axiom 2 (lemma_0003) }"
    //   "= { by lemma 5 (history_lemma_0061) R->L }"
    let cite_re = Regex::new(&format!(
        r"(?mi)\bby\s+(?:axiom|lemma)\s+\d+\s*\(\s*(?:{})\s*\)",
        alts
    ))
    .unwrap();

    segments
        .iter()
        .any(|s| axiom_re.is_match(s) || deps_re.is_match(s) || cite_re.is_match(s))
}

/// Keep only those lemmas in `block` that are required to derive
/// the lemmas referenced in later segments
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

    // helper: keep/trim a segment
    let keep_named =
        |name: &str, proof: &str, by: &str, steps_in: usize, segs: &[&str]| -> (String, usize) {
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
                    let kept = proof.to_string();
                    (kept, steps_in)
                }
                _ => {
                    let kept = proof.to_string();
                    (kept, steps_in)
                }
            }
        };

    // 1) root depends on sub (if any)
    let (kept_root, root_steps) =
        keep_named(root_name, root_proof, root_by, root_steps_in, &sub_segs);

    // 2) history depends on root + sub
    let (kept_history, history_steps) = match history {
        None => (String::new(), 0),
        Some((h_name, h_proof, h_by, h_steps_in)) => {
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
    };

    // 3) start depends on (history if non-empty) + root + sub
    let (kept_start, start_steps) = match start {
        None => (String::new(), 0),
        Some((start_proof, start_by, start_steps_in)) => {
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
    };

    (
        kept_start,
        kept_history,
        kept_root,
        start_steps,
        history_steps,
        root_steps,
    )
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
    fn trim_with_three_segments1() {
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
    fn trim_two_segments1() {
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

    #[test]
    fn trim_with_two_segments2() {
        let block = r#"
% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0)) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63 | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0003: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(op(X3,op(op(X4,X0),X3)),X0))
% lemma_0005: op(X2,op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(op(X4,op(op(X5,X2),X4)),X2))) = X2 | deps: lemma_0004: op(X63,op(op(X66,op(op(X61,op(op(X62,X63),X61)),X66)),op(op(X64,op(op(X65,X63),X64)),X63))) = X63, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
"#;

        // Segment 1
        let seg2 = r#"
The conjecture is true! Here is a proof.

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

Lemma 6: op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(W, op(op(V, Y), W)))) = op(X, op(Y, X)).
Proof:
  op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(W, op(op(V, Y), W))))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(Y, X)), op(op(Z, op(Y, Z)), op(op(W, op(op(V, Y), W)), op(Z, op(Y, Z)))))
= { by lemma 5 }
  op(X, op(Y, X))

Lemma 7: op(op(X, op(op(Y, Y), X)), op(Y, op(op(Y, Y), Y))) = op(X, op(op(Y, Y), X)).
Proof:
  op(op(X, op(op(Y, Y), X)), op(Y, op(op(Y, Y), Y)))
= { by axiom 1 (a1) }
  op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(Y, op(op(Y, Y), Y))), op(Y, op(op(Y, Y), Y))))))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))), op(Y, op(op(Y, Y), Y))))))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))), op(op(Y, op(op(Y, Y), Y)), op(op(op(Y, Y), Y), op(Y, op(op(Y, Y), Y))))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(Y, Y)), op(op(Y, op(op(Y, Y), Y)), op(Y, op(Y, Y)))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(X, op(op(Y, Y), X)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(op(Y, Y), Y)), op(op(Y, op(Y, Y)), op(Y, op(op(Y, Y), Y))))))
= { by lemma 6 }
  op(X, op(op(Y, Y), X))

Lemma 8: op(op(op(X, X), X), op(X, op(op(X, X), X))) = op(op(X, X), X).
Proof:
  op(op(op(X, X), X), op(X, op(op(X, X), X)))
= { by lemma 7 R->L }
  op(op(op(X, X), X), op(op(X, op(op(X, X), X)), op(X, op(op(X, X), X))))
= { by lemma 7 R->L }
  op(op(op(X, X), X), op(op(X, op(op(X, X), X)), op(op(X, op(op(X, X), X)), op(X, op(op(X, X), X)))))
= { by axiom 1 (a1) R->L }
  op(op(X, X), X)

Lemma 9: op(X, op(op(op(Y, X), op(Y, X)), op(Y, X))) = X.
Proof:
  op(X, op(op(op(Y, X), op(Y, X)), op(Y, X)))
= { by lemma 8 R->L }
  op(X, op(op(op(op(Y, X), op(Y, X)), op(Y, X)), op(op(Y, X), op(op(op(Y, X), op(Y, X)), op(Y, X)))))
= { by axiom 1 (a1) R->L }
  X

Lemma 10: op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z)))) = op(op(X, Y), Z).
Proof:
  op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z))))
= { by axiom 2 (lemma_0001) }
  op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(op(Z, op(op(X, Y), Z)), op(W, op(Y, W)))))
= { by axiom 1 (a1) R->L }
  op(op(X, Y), Z)

Lemma 11: op(op(op(X, op(op(Y, Z), Z)), W), op(op(Z, op(op(Y, Z), Z)), op(W, op(op(X, op(op(Y, Z), Z)), W)))) = op(op(X, op(op(Y, Z), Z)), W).
Proof:
  op(op(op(X, op(op(Y, Z), Z)), W), op(op(Z, op(op(Y, Z), Z)), op(W, op(op(X, op(op(Y, Z), Z)), W))))
= { by axiom 2 (lemma_0001) }
  op(op(op(X, op(op(Y, Z), Z)), W), op(op(op(Z, op(op(Y, Z), Z)), op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z)))), op(W, op(op(X, op(op(Y, Z), Z)), W))))
= { by lemma 10 }
  op(op(X, op(op(Y, Z), Z)), W)

Lemma 12: op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))))) = op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))).
Proof:
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 R->L }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 R->L }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 4 (lemma_0003) R->L }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(op(X, op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))))), op(X, op(op(Y, X), X)))))))
= { by lemma 5 }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), op(X, op(X, op(op(Y, X), X)))), op(X, op(op(Y, X), X)))))))
= { by axiom 1 (a1) R->L }
  op(op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), op(op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X)))))))
= { by lemma 11 }
  op(op(X, op(op(Y, X), X)), op(op(op(X, op(op(Y, X), X)), X), op(X, op(op(Y, X), X))))

Lemma 13: op(op(X, op(Y, X)), op(Y, op(Y, Y))) = op(X, op(Y, X)).
Proof:
  op(op(X, op(Y, X)), op(Y, op(Y, Y)))
= { by axiom 3 (lemma_0002) R->L }
  op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, Y), op(Y, op(Y, Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by lemma 12 }
  op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y))))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by lemma 12 }
  op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y)))), op(op(Y, Y), op(Y, op(Y, Y))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(X, op(Y, X)), op(op(Y, op(Y, Y)), op(op(Y, op(op(Z, Y), Y)), op(op(op(Y, op(op(Z, Y), Y)), Y), op(Y, op(op(Z, Y), Y))))))
= { by lemma 6 }
  op(X, op(Y, X))

Lemma 14: op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X))) = op(X, X).
Proof:
  op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))
= { by lemma 8 R->L }
  op(op(X, X), op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))))
= { by axiom 2 (lemma_0001) }
  op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 9 R->L }
  op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(op(op(X, op(X, X)), op(X, op(X, X))), op(X, op(X, X)))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 13 }
  op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(op(X, op(X, X)), op(X, op(X, X)))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by lemma 13 }
  op(op(X, X), op(op(op(op(op(X, X), op(X, X)), op(X, X)), op(op(op(X, X), op(X, op(X, X))), op(op(op(X, X), op(X, X)), op(X, X)))), op(X, op(X, X))))
= { by axiom 3 (lemma_0002) }
  op(X, X)

Lemma 15: op(op(X, X), op(X, X)) = op(X, X).
Proof:
  op(op(X, X), op(X, X))
= { by lemma 14 R->L }
  op(op(X, X), op(op(X, X), op(op(op(X, X), op(X, X)), op(X, X))))
= { by axiom 1 (a1) R->L }
  op(X, X)

Lemma 16: op(X, op(X, X)) = X.
Proof:
  op(X, op(X, X))
= { by lemma 15 R->L }
  op(X, op(op(X, X), op(X, X)))
= { by lemma 15 R->L }
  op(X, op(op(X, X), op(op(X, X), op(X, X))))
= { by axiom 1 (a1) R->L }
  X

Lemma 17: op(X, X) = X.
Proof:
  op(X, X)
= { by lemma 16 R->L }
  op(X, op(X, op(X, X)))
= { by lemma 16 R->L }
  op(op(X, op(X, X)), op(X, op(X, X)))
= { by lemma 13 }
  op(X, op(X, X))
= { by lemma 16 }
  X

Lemma 18: op(X, op(Y, X)) = X.
Proof:
  op(X, op(Y, X))
= { by lemma 17 R->L }
  op(X, op(op(Y, X), op(Y, X)))
= { by lemma 17 R->L }
  op(X, op(op(Y, X), op(op(Y, X), op(Y, X))))
= { by axiom 1 (a1) R->L }
  X

Lemma 19: op(op(X, Y), Y) = op(X, Y).
Proof:
  op(op(X, Y), Y)
= { by axiom 3 (lemma_0002) R->L }
  op(op(X, Y), op(Y, op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by lemma 16 R->L }
  op(op(X, Y), op(op(Y, op(Y, Y)), op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by axiom 3 (lemma_0002) R->L }
  op(op(X, Y), op(op(Y, op(op(Y, op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))), Y)), op(op(Z, op(op(W, op(X, Y)), Z)), op(X, Y))))
= { by axiom 3 (lemma_0002) }
  op(X, Y)

Lemma 20: op(op(X, Y), op(Z, op(Y, Z))) = op(X, Y).
Proof:
  op(op(X, Y), op(Z, op(Y, Z)))
= { by lemma 17 R->L }
  op(op(op(X, Y), op(X, Y)), op(Z, op(Y, Z)))
= { by lemma 19 R->L }
  op(op(op(op(X, Y), op(X, Y)), op(X, Y)), op(Z, op(Y, Z)))
= { by lemma 9 R->L }
  op(op(op(op(X, Y), op(X, Y)), op(X, Y)), op(Z, op(op(Y, op(op(op(X, Y), op(X, Y)), op(X, Y))), Z)))
= { by axiom 1 (a1) R->L }
  op(op(op(X, Y), op(X, Y)), op(X, Y))
= { by lemma 19 }
  op(op(X, Y), op(X, Y))
= { by lemma 17 }
  op(X, Y)

Lemma 21: op(X, op(op(Y, X), op(Z, op(Y, X)))) = X.
Proof:
  op(X, op(op(Y, X), op(Z, op(Y, X))))
= { by lemma 19 R->L }
  op(X, op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))))
= { by axiom 1 (a1) }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(Y, X))), X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(op(op(Y, X), op(op(X, X), op(Y, X))), X)))))
= { by axiom 4 (lemma_0003) R->L }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(Y, X))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 R->L }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(X, op(X, X))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 9 R->L }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(op(Y, X), op(X, op(X, X))), op(op(Y, X), op(X, op(X, X)))), op(op(Y, X), op(X, op(X, X)))))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(op(Y, X), op(X, op(X, X)))), op(op(Y, X), op(X, op(X, X)))))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(op(Y, X), op(X, op(X, X)))), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 20 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(op(Y, X), op(Y, X)), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 19 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(op(Y, X), op(Y, X)))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 17 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(op(X, X), op(op(Y, X), op(op(X, op(X, X)), op(Y, X))))), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 1 (a1) R->L }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 1 (a1) }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), op(X, op(op(X, X), op(op(Y, X), op(X, X))))), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 16 R->L }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(op(Y, X), op(X, X)), op(op(X, op(X, X)), op(op(X, X), op(op(Y, X), op(X, X))))), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 10 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(Y, X), op(X, X)), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 17 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(op(Y, X), X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by lemma 19 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))
= { by axiom 2 (lemma_0001) }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(X, op(X, X))))))
= { by lemma 16 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), X))))
= { by axiom 1 (a1) }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(op(Y, X), op(op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))), op(X, op(op(op(Z, op(Y, X)), op(Y, X)), op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X)))))))))
= { by lemma 20 }
  op(X, op(op(op(Y, X), op(op(Z, op(Y, X)), op(Y, X))), op(Y, X)))
= { by axiom 3 (lemma_0002) }
  X

Lemma 22: op(X, op(Y, Z)) = X.
Proof:
  op(X, op(Y, Z))
= { by lemma 18 R->L }
  op(X, op(op(Y, Z), op(Z, op(Y, Z))))
= { by lemma 19 R->L }
  op(X, op(op(Y, Z), op(Z, op(op(Y, Z), Z))))
= { by lemma 19 R->L }
  op(X, op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))))
= { by lemma 6 R->L }
  op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(op(W, X), op(Y, Z)), op(Z, op(op(W, X), op(Y, Z)))), op(Z, op(op(V, Z), Z)))))
= { by lemma 18 }
  op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(op(V, Z), Z)))))
= { by lemma 19 }
  op(X, op(op(op(op(Y, Z), Z), op(Z, op(op(Y, Z), Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 19 }
  op(X, op(op(op(op(Y, Z), Z), op(Z, op(Y, Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 19 }
  op(X, op(op(op(Y, Z), op(Z, op(Y, Z))), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 18 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(Z, op(V, Z)))))
= { by lemma 18 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), Z)))
= { by lemma 21 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(Z, op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 1 (a1) }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(Z, op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(Z, Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(Z, Z), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 15 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, Z), op(Z, Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(Z, Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 14 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z)), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 11 R->L }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 14 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(op(Z, Z), Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(op(Z, Z), op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), op(Z, Z))), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), op(Z, Z)), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(op(Z, Z), Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(op(Z, Z), op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(op(Z, Z), Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 17 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(op(Z, Z), Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(op(Z, Z), Z)), op(Z, op(op(Z, op(Z, Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 19 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(Z, Z)), op(Z, op(op(Z, op(Z, Z)), Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(op(Z, op(Z, Z)), op(Z, op(Z, Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by lemma 16 }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z), op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z))))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 4 (lemma_0003) }
  op(X, op(op(Y, Z), op(op(op(W, X), op(Y, Z)), op(op(op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z), op(op(op(op(W, X), op(Y, Z)), op(op(Y, Z), op(op(W, X), op(Y, Z)))), op(op(op(Z, op(Z, op(Z, Z))), op(op(Z, Z), op(Z, op(Z, op(Z, Z))))), Z))), op(op(Y, Z), op(op(W, X), op(Y, Z)))))))
= { by axiom 3 (lemma_0002) }
  op(X, op(op(Y, Z), op(op(W, X), op(Y, Z))))
= { by axiom 1 (a1) R->L }
  X

Goal 1 (history_lemma_0061): x0 = op(x0, x1).
Proof:
  x0
= { by lemma 22 R->L }
  op(x0, op(X, x1))
= { by lemma 19 R->L }
  op(x0, op(op(X, x1), x1))
= { by lemma 22 R->L }
  op(op(x0, op(op(X, x1), x1)), op(Y, x1))
= { by lemma 11 R->L }
  op(op(op(x0, op(op(X, x1), x1)), op(Y, x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(op(X, x1), x1)), op(Y, x1)))))
= { by lemma 22 }
  op(op(x0, op(op(X, x1), x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(op(X, x1), x1)), op(Y, x1)))))
= { by lemma 19 }
  op(op(x0, op(op(X, x1), x1)), op(op(x1, op(op(X, x1), x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 19 }
  op(op(x0, op(op(X, x1), x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 19 }
  op(op(x0, op(X, x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(op(x0, op(X, x1)), op(Y, x1)))))
= { by lemma 22 }
  op(op(x0, op(X, x1)), op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 22 }
  op(x0, op(op(x1, op(X, x1)), op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 18 }
  op(x0, op(x1, op(op(Y, x1), op(x0, op(Y, x1)))))
= { by lemma 21 }
  op(x0, x1)

RESULT: Theorem (the conjecture is true).
"#;

        // Segment 3
        let seg3 = r#"
RESULT: Theorem (the conjecture is true).
The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0061): X = op(X, Y).

Goal 1 (conjecture0): x0 = op(x0, op(x1, op(x2, op(x0, x2)))).
Proof:
  x0
= { by axiom 1 (history_lemma_0061) }
  op(x0, op(x1, op(x2, op(x0, x2))))

RESULT: Theorem (the conjecture is true).
        "#;

        let trimmed = trim_superposition_block(block, &[seg2, seg3]);

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

    #[test]
    fn trim_with_two_segments3() {
        let block = r#"
% === Superposition Steps ===
% lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 | deps: a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0, a_1: ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0
% lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0))) | deps: lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) | deps: lemma_0002: op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1, lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))) | deps: lemma_0005: op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))), lemma_0004: op(X15,X16) = op(op(X15,X16),op(op(X17,op(op(X13,op(op(X14,X15),X13)),X17)),op(X16,op(X15,X16))))
% lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))) | deps: lemma_0006: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62)),op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),op(op(op(X59,op(op(X60,X58),X59)),X58),op(X58,op(op(X59,op(op(X60,X58),X59)),X58)))))), lemma_0001: op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3)))
% lemma_0008: op(X29,op(X27,X29)) = op(op(X29,op(X27,X29)),op(op(X27,op(op(X28,X27),X27)),op(X27,op(op(X27,op(op(X28,X27),X27)),X27)))) | deps: lemma_0007: op(X61,op(X58,X61)) = op(op(X61,op(X58,X61)),op(X62,op(op(X58,op(op(X59,op(op(X60,X58),X59)),X58)),X62))), lemma_0003: op(X2,op(op(X3,op(op(X1,X0),X0)),X2)) = op(op(X2,op(op(X3,op(op(X1,X0),X0)),X2)),op(X0,op(op(X1,X0),X0)))
"#;

        // Segment 2
        let seg2 = r#"The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (lemma_0001): op(X, op(op(Y, Z), X)) = op(op(X, op(op(Y, Z), X)), op(W, op(Z, W))).

Lemma 3: op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))) = op(X, op(op(Y, op(op(Z, W), W)), X)).
Proof:
  op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W)))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(op(W, op(op(Z, W), W)), op(op(op(Z, W), W), op(W, op(op(Z, W), W)))))
= { by axiom 2 (lemma_0001) R->L }
  op(X, op(op(Y, op(op(Z, W), W)), X))

Lemma 4: op(op(X, op(op(Y, X), X)), op(Z, op(op(W, op(op(V, op(op(Y, X), X)), W)), Z))) = op(X, op(op(Y, X), X)).
Proof:
  op(op(X, op(op(Y, X), X)), op(Z, op(op(W, op(op(V, op(op(Y, X), X)), W)), Z)))
= { by lemma 3 R->L }
  op(op(X, op(op(Y, X), X)), op(Z, op(op(op(W, op(op(V, op(op(Y, X), X)), W)), op(X, op(op(Y, X), X))), Z)))
= { by axiom 1 (a1) R->L }
  op(X, op(op(Y, X), X))

Lemma 5: op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(W, U)), V))) = op(X, op(op(Y, op(op(Z, W), Y)), X)).
Proof:
  op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(W, U)), V)))
= { by axiom 1 (a1) }
  op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(U, op(op(W, op(Y, op(op(Z, W), Y))), U)), V)))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(op(U, op(op(W, op(Y, op(op(Z, W), Y))), U)), op(X, op(op(Y, op(op(Z, W), Y)), X))), V)))
= { by axiom 1 (a1) R->L }
  op(op(X, op(op(Y, op(op(Z, W), Y)), X)), op(V, op(op(op(U, op(W, U)), op(X, op(op(Y, op(op(Z, W), Y)), X))), V)))
= { by axiom 1 (a1) R->L }
  op(X, op(op(Y, op(op(Z, W), Y)), X))

Lemma 6: op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z)))) = op(op(X, Y), Z).
Proof:
  op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(Z, op(op(X, Y), Z))))
= { by axiom 2 (lemma_0001) }
  op(op(op(X, Y), Z), op(op(W, op(Y, W)), op(op(Z, op(op(X, Y), Z)), op(W, op(Y, W)))))
= { by axiom 1 (a1) R->L }
  op(op(X, Y), Z)

Lemma 7: op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(X, op(op(Y, op(op(Z, W), W)), X)), V)))) = op(op(X, op(op(Y, op(op(Z, W), W)), X)), V).
Proof:
  op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(X, op(op(Y, op(op(Z, W), W)), X)), V))))
= { by lemma 3 R->L }
  op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V))))
= { by lemma 3 R->L }
  op(op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V), op(op(U, op(op(W, op(op(Z, W), W)), U)), op(V, op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V))))
= { by lemma 6 }
  op(op(op(X, op(op(Y, op(op(Z, W), W)), X)), op(W, op(op(Z, W), W))), V)
= { by lemma 3 }
  op(op(X, op(op(Y, op(op(Z, W), W)), X)), V)

Lemma 8: op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(W, op(op(Y, op(op(Z, Y), Y)), W))) = op(X, op(op(Y, op(op(Z, Y), Y)), X)).
Proof:
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(W, op(op(Y, op(op(Z, Y), Y)), W)))
= { by lemma 5 R->L }
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))
= { by axiom 2 (lemma_0001) }
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(X, op(op(Y, op(op(Z, Y), Y)), X)))))
= { by lemma 5 R->L }
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))))
= { by lemma 5 R->L }
  op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))), op(op(W, op(op(Y, op(op(Z, Y), Y)), W)), op(op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)), op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V))))))
= { by lemma 7 }
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(op(op(Z, Y), Y), op(Y, op(op(Z, Y), Y))), V)))
= { by lemma 5 }
  op(X, op(op(Y, op(op(Z, Y), Y)), X))

Lemma 9: op(op(X, op(op(Y, X), X)), op(X, op(op(Y, X), X))) = op(X, op(op(Y, X), X)).
Proof:
  op(op(X, op(op(Y, X), X)), op(X, op(op(Y, X), X)))
= { by lemma 4 R->L }
  op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(Z, op(op(X, op(op(Y, X), X)), Z))))))
= { by lemma 8 }
  op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(W, op(op(X, op(op(Y, X), X)), W)))))
= { by lemma 8 }
  op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(Z, op(op(X, op(op(Y, X), X)), Z))))
= { by lemma 3 R->L }
  op(op(X, op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(X, op(op(Y, X), X)))))
= { by lemma 4 }
  op(X, op(op(Y, X), X))

Lemma 10: op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))) = op(op(X, Y), Y).
Proof:
  op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y)))
= { by lemma 9 R->L }
  op(op(op(X, Y), Y), op(op(Y, op(op(X, Y), Y)), op(Y, op(op(X, Y), Y))))
= { by lemma 9 R->L }
  op(op(op(X, Y), Y), op(op(Y, op(op(X, Y), Y)), op(op(Y, op(op(X, Y), Y)), op(Y, op(op(X, Y), Y)))))
= { by axiom 1 (a1) R->L }
  op(op(X, Y), Y)

Lemma 11: op(op(op(X, Y), Y), op(op(X, Y), Y)) = op(op(X, Y), Y).
Proof:
  op(op(op(X, Y), Y), op(op(X, Y), Y))
= { by lemma 10 R->L }
  op(op(op(X, Y), Y), op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))))
= { by lemma 10 R->L }
  op(op(op(X, Y), Y), op(op(op(op(X, Y), Y), op(Y, op(op(X, Y), Y))), op(Y, op(op(X, Y), Y))))
= { by lemma 6 }
  op(op(X, Y), Y)

Lemma 12: op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(V, op(op(Y, op(op(Z, Y), Y)), V))) = op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W).
Proof:
  op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(V, op(op(Y, op(op(Z, Y), Y)), V)))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(op(V, op(op(Y, op(op(Z, Y), Y)), V)), op(W, op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), op(V, op(op(Y, op(op(Z, Y), Y)), V))), W))))
= { by lemma 8 }
  op(op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W), op(op(V, op(op(Y, op(op(Z, Y), Y)), V)), op(W, op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W))))
= { by lemma 7 }
  op(op(X, op(op(Y, op(op(Z, Y), Y)), X)), W)

Lemma 13: op(op(op(X, op(op(Y, X), X)), Z), op(op(X, op(op(Y, X), X)), W)) = op(op(X, op(op(Y, X), X)), Z).
Proof:
  op(op(op(X, op(op(Y, X), X)), Z), op(op(X, op(op(Y, X), X)), W))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W))))))
= { by axiom 2 (lemma_0001) }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(op(op(Y, X), X), op(op(Y, X), X)))), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 11 }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(op(Y, X), X))), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 11 }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 12 R->L }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(X, op(op(Y, X), X)), W))))))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X))))))))))
= { by axiom 1 (a1) }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(op(Y, X), X), op(Z, op(op(X, op(op(Y, X), X)), Z))))))))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by lemma 8 R->L }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by lemma 8 R->L }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))), op(op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W))), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(Y, X), X)), op(W, op(op(X, op(op(Y, X), X)), W)))))))))
= { by axiom 2 (lemma_0001) R->L }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))))))
= { by lemma 8 }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(op(W, op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W))))))
= { by lemma 8 }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W)), op(W, op(op(X, op(op(Y, X), X)), W)))))
= { by lemma 12 }
  op(op(op(X, op(op(Y, X), X)), Z), op(op(op(X, op(op(Y, X), X)), W), op(op(Z, op(op(X, op(op(Y, X), X)), Z)), op(op(X, op(op(Y, X), X)), W))))
= { by axiom 1 (a1) R->L }
  op(op(X, op(op(Y, X), X)), Z)

Goal 1 (history_lemma_0058): op(x2, op(op(x0, op(op(x1, x0), x0)), x2)) = x2.
Proof:
  op(x2, op(op(x0, op(op(x1, x0), x0)), x2))
= { by lemma 13 R->L }
  op(x2, op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(x0, op(op(x1, x0), x0)), x2)))
= { by lemma 13 R->L }
  op(x2, op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(op(x0, op(op(x1, x0), x0)), x2), op(op(x0, op(op(x1, x0), x0)), x2))))
= { by axiom 1 (a1) R->L }
  x2

RESULT: Theorem (the conjecture is true).
"#;

        // Segment 3
        let seg3 = r#"
The conjecture is true! Here is a proof.

Axiom 1 (a1): X = op(X, op(Y, op(op(Z, X), Y))).
Axiom 2 (history_lemma_0058): op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X.

Goal 1 (conjecture0): x0 = op(x0, op(x1, op(x2, op(x0, x2)))).
Proof:
  x0
= { by axiom 1 (a1) }
  op(x0, op(X, op(op(Y, x0), X)))
= { by axiom 1 (a1) }
  op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X)))
= { by axiom 1 (a1) }
  op(op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X))), op(op(x1, op(x2, op(x0, x2))), op(op(op(X, op(op(Y, x0), X)), op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X)))), op(x1, op(x2, op(x0, x2))))))
= { by axiom 2 (history_lemma_0058) }
  op(op(op(x0, op(X, op(op(Y, x0), X))), op(X, op(op(Y, x0), X))), op(x1, op(x2, op(x0, x2))))
= { by axiom 1 (a1) R->L }
  op(op(x0, op(X, op(op(Y, x0), X))), op(x1, op(x2, op(x0, x2))))
= { by axiom 1 (a1) R->L }
  op(x0, op(x1, op(x2, op(x0, x2))))

RESULT: Theorem (the conjecture is true).
        "#;

        let trimmed = trim_superposition_block(block, &[seg2, seg3]);

        assert!(trimmed.contains("% === Superposition Steps ==="));
        assert!(trimmed.contains("% lemma_0001:"));

        // these must be gone
        assert!(!trimmed.contains("% lemma_0002:"));
        assert!(!trimmed.contains("% lemma_0003:"));
        assert!(!trimmed.contains("% lemma_0004:"));
        assert!(!trimmed.contains("% lemma_0005:"));
        assert!(!trimmed.contains("% lemma_0006:"));
        assert!(!trimmed.contains("% lemma_0007:"));
        assert!(!trimmed.contains("% lemma_0008:"));
        assert_eq!(count_superposition_steps(&trimmed), 1);
    }

    #[test]
    fn proof_uses_lemma() {
        let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

        // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
        let seg1 = r#"
% === Superposition Steps ===
% lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))) | deps: lemma_0001, lemma_0002
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004, lemma_0002
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7)))) | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1)) | deps: lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))), lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2)))))
% lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))) | deps: lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0002
% lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))) | deps: lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))), lemma_0002
% lemma_0017: op(X11,op(X12,op(X11,X12))) = X12 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1))
% lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))) | deps: lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))), lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1)
% lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) | deps: lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))), lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3))))
% lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17) | deps: lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17), lemma_0002
% lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17) | deps: lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17), lemma_0002
% lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17), lemma_0017: op(X11,op(X12,op(X11,X12))) = X12
% history_lemma_0151: op(X17,X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17), lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0)
"#;

        // Segment 3: the final goal proof — still no lemma_0004..0008 usage
        let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (lemma_0022): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).
Axiom 2 (lemma_0011): op(X, X) = op(op(Y, op(X, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
  op(x0, x0)
= { by axiom 2 (lemma_0011) }
  op(op(x0, op(x0, x0)), x0)
= { by axiom 1 (lemma_0022) }
  op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
        // Use trim_proof_parts: block is the "start" vampire block,
        // seg1 is the "root" vampire block, seg3 is sub-proof.
        let (kept_start, kept_hist, kept_root, start_steps, hist_steps, root_steps) =
            trim_proof_parts(
                Some((block, "vampire", count_superposition_steps(block))),
                None,
                (
                    "history_lemma_0151",
                    seg1,
                    "vampire",
                    count_superposition_steps(seg1),
                ),
                Some(seg3),
            );

        // history is None -> empty string + 0 steps
        assert!(kept_hist.trim().is_empty());
        assert_eq!(hist_steps, 0);

        // start exists
        assert!(!kept_start.trim().is_empty());

        // start is vampire-trimmed, so it should NOT be empty
        assert!(!kept_start.trim().is_empty());
        assert!(kept_start.contains("% lemma_0001:"));
        assert!(kept_start.contains("% lemma_0002:"));
        assert!(kept_start.contains("% lemma_0003:"));
        assert!(kept_start.contains("% lemma_0004:"));
        assert!(kept_start.contains("% lemma_0005:"));
        assert!(kept_start.contains("% lemma_0006:"));

        // Root block must keep what the later proof actually uses:
        assert!(kept_root.contains("% lemma_0007:"));
        assert!(kept_root.contains("% lemma_0003:"));
        assert!(kept_root.contains("% lemma_0022:"));
        assert!(kept_root.contains("% lemma_0011:"));
        assert!(!kept_root.contains("% history_lemma_0151:"));

        // Step accounting
        assert_eq!(start_steps, 6);
        assert_eq!(root_steps, count_superposition_steps(&kept_root));
    }

    #[test]
    fn proof_uses_lemma_remove_seg() {
        let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

        // Segment 1: the “main proof” (uses lemma_0003 as axiom 2)
        let seg1 = r#"
% === Superposition Steps ===
% lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))) | deps: lemma_0001, lemma_0002
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004, lemma_0002
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7)))) | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0002
% lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0) | deps: lemma_0008: op(op(X0,X1),op(X1,op(X1,X1))) = X1, lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1)) | deps: lemma_0010: op(X0,op(X1,X1)) = op(X1,op(op(X0,op(X1,X1)),op(op(X0,op(X1,X1)),op(X0,op(X1,X1))))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2))))), lemma_0007: op(X0,op(X2,X2)) = op(X3,op(X2,op(X3,op(X0,op(X2,X2)))))
% lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) | deps: lemma_0013: op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))) = op(op(X2,op(X3,X3)),op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0009: op(X6,X7) = op(X8,op(X8,op(X6,op(X7,X7))))
% lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))) | deps: lemma_0014: op(X2,X3) = op(X3,op(op(X2,op(X3,X3)),op(X2,op(X3,X3)))), lemma_0002
% lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))) | deps: lemma_0015: op(X2,X3) = op(X3,op(X2,op(op(X3,X3),op(X3,X3)))), lemma_0002
% lemma_0017: op(X11,op(X12,op(X11,X12))) = X12 | deps: lemma_0003: op(X1,op(X1,op(X0,X0))) = X0, lemma_0012: op(X0,op(X1,X1)) = op(X1,op(X0,X1))
% lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))) | deps: lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3)))), lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1)
% lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) | deps: lemma_0018: op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17) = op(X17,op(op(X17,op(X17,X17)),op(X17,op(X17,X17)))), lemma_0016: op(X2,X3) = op(X3,op(X2,op(X3,op(X3,X3))))
% lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17) | deps: lemma_0019: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(op(X17,op(X17,X17)),op(X17,op(X17,X17))))),X17), lemma_0002
% lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17) | deps: lemma_0020: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(op(X17,X17),op(X17,X17))))),X17), lemma_0002
% lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0021: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,op(X17,op(X17,op(X17,X17))))),X17), lemma_0017: op(X11,op(X12,op(X11,X12))) = X12
% history_lemma_0151: op(X17,X17) = op(op(X15,op(X16,X17)),X17) | deps: lemma_0022: op(op(X17,op(X17,X17)),X17) = op(op(X15,op(X16,X17)),X17), lemma_0011: op(X0,X0) = op(op(X1,op(X0,X0)),X0)
"#;

        // Segment 3: the final goal proof — still no lemma_0004..0008 usage
        let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (lemma_0001): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).
Axiom 2 (lemma_0002): op(X, X) = op(op(Y, op(X, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
  op(x0, x0)
= { by axiom 2 (lemma_0002) }
  op(op(x0, op(x0, x0)), x0)
= { by axiom 1 (lemma_0001) }
  op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
        // Use trim_proof_parts: block is the "start" vampire block,
        // seg1 is the "root" vampire block, seg3 is sub-proof.
        let (kept_start, kept_hist, kept_root, start_steps, hist_steps, root_steps) =
            trim_proof_parts(
                Some((block, "vampire", count_superposition_steps(block))),
                None,
                (
                    "history_lemma_0151",
                    seg1,
                    "vampire",
                    count_superposition_steps(seg1),
                ),
                Some(seg3),
            );

        // history is None -> empty string + 0 steps
        assert!(kept_hist.trim().is_empty());
        assert_eq!(hist_steps, 0);

        // start exists -> should not be empty
        assert!(!kept_start.trim().is_empty());

        // start is vampire-trimmed
        assert!(!kept_start.trim().is_empty());
        assert!(kept_start.contains("% lemma_0001:"));
        assert!(kept_start.contains("% lemma_0002:"));
        assert!(!kept_start.contains("% lemma_0003:"));
        assert!(!kept_start.contains("% lemma_0004:"));
        assert!(!kept_start.contains("% lemma_0005:"));
        assert!(!kept_start.contains("% lemma_0006:"));

        // Root block must be empty
        assert!(kept_root.trim().is_empty());

        // Step accounting
        assert_eq!(start_steps, 2);
        assert_eq!(root_steps, 0);
    }

    #[test]
    fn untouched() {
        let block = r#"% === Superposition Steps ===
% lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))) | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)) | deps: lemma_0001: op(op(X1,X2),op(X0,X2)) = op(X3,op(X2,op(X3,op(op(X1,X2),op(X0,X2))))), a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0
% lemma_0003: op(X1,op(X1,op(X0,X0))) = X0 | deps: a_1: ! [X0,X1,X2] : op(X1,op(op(X2,X0),op(X1,X0))) = X0, lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2)), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
% lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))) | deps: lemma_0004: op(X0,op(op(X0,op(X1,X1)),op(X0,op(X1,X1)))) = op(op(X2,op(X0,op(X1,X1))),X1), lemma_0002: op(op(X1,X2),op(X0,X2)) = op(X0,op(X2,X2))
% lemma_0006: op(X1,X1) = op(op(X2,op(X0,op(X1,X1))),X1) | deps: lemma_0005: op(op(X2,op(X0,op(X1,X1))),X1) = op(X0,op(X0,op(op(X1,X1),op(X1,X1)))), lemma_0003: op(X1,op(X1,op(X0,X0))) = X0
"#;

        // Segment 2: raw Vampire output
        let seg2 = r#"
1. ! [X0,X1,X2] : op(X0,op(X1,op(op(X2,X0),X1))) = X0 [input]
2. ! [X0,X1,X2,X3] : op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) [input]
3. ! [X0,X1,X2,X3] : op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 [input]
4. ! [X0,X1,X2,X3,X4] : op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X1,op(op(X2,X0),X1)),X4))) [input]
6. ! [X7,X8,X9,X10,X11] : op(X9,X10) = op(op(X9,X10),op(op(X11,op(op(X7,op(op(X8,X9),X7)),X11)),op(X10,op(X9,X10)))) [input]
7. ! [X0,X1,X2,X3,X4] : op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))) [input]
8. ! [X0,X1,X2,X3,X4] : op(X2,X4) = op(op(X2,X4),op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(X4,op(X2,X4)))) [input]
9. ! [X12,X13,X14,X15] : op(op(X13,op(op(X14,X13),X13)),X15) = op(op(op(X13,op(op(X14,X13),X13)),X15),op(op(X12,op(op(X13,op(op(X14,X13),X13)),X12)),op(X15,op(op(X13,op(op(X14,X13),X13)),X15)))) [input]
10. ! [X16,X17,X18,X19] : op(X19,op(op(X17,op(op(X18,X17),X17)),X19)) = op(op(X19,op(op(X17,op(op(X18,X17),X17)),X19)),op(X16,op(op(X17,op(op(X18,X17),X17)),X16))) [input]
14. ! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [input]
15. ~! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [negated conjecture 14]
17. ! [X0,X1,X2,X3,X4] : op(X2,X3) = op(op(X2,X3),op(op(X4,op(op(X0,op(op(X1,X2),X0)),X4)),op(X3,op(X2,X3)))) [rectify 6]
18. ! [X0,X1,X2,X3] : op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(op(X0,op(op(X1,op(op(X2,X1),X1)),X0)),op(X3,op(op(X1,op(op(X2,X1),X1)),X3)))) [rectify 9]
19. ! [X0,X1,X2,X3] : op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [rectify 10]
22. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 [ennf transformation 15]
23. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 => sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [choice axiom]
24. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [skolemisation 22,23]
25. op(X0,op(X1,op(op(X2,X0),X1))) = X0 [cnf transformation 1]
26. op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),op(X3,op(X0,X3))) [cnf transformation 2]
27. op(X1,op(op(X2,op(op(X3,op(X0,X1)),X2)),op(X0,X1))) = X1 [cnf transformation 3]
28. op(X3,op(X0,X3)) = op(op(X3,op(X0,X3)),op(X4,op(op(X1,op(op(X2,X0),X1)),X4))) [cnf transformation 4]
30. op(X2,X3) = op(op(X2,X3),op(op(X4,op(op(X0,op(op(X1,X2),X0)),X4)),op(X3,op(X2,X3)))) [cnf transformation 17]
31. op(X4,op(X2,X4)) = op(op(X4,op(X2,X4)),op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0)))) [cnf transformation 7]
32. op(X2,X4) = op(op(X2,X4),op(op(op(X3,op(X2,X3)),op(X0,op(op(X1,X2),X0))),op(X4,op(X2,X4)))) [cnf transformation 8]
33. op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(op(X0,op(op(X1,op(op(X2,X1),X1)),X0)),op(X3,op(op(X1,op(op(X2,X1),X1)),X3)))) [cnf transformation 18]
34. op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [cnf transformation 19]
38. $true [cnf transformation 24]
39. op(op(X1,op(op(X2,X1),X1)),X3) = op(op(op(X1,op(op(X2,X1),X1)),X3),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [backward demodulation 33,34]
42. op(op(X2,X0),X1) = op(op(op(X2,X0),X1),op(op(X3,op(X0,X3)),op(X1,op(op(X2,X0),X1)))) [superposition 27,25]
62. op(X4,op(op(op(X7,op(X6,X7)),op(X4,op(op(X5,X6),X4))),op(op(X5,X6),X4))) = X4 [superposition 27,26]
66. op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22)),op(X18,op(op(X19,X20),X18)))) [superposition 27,26]
191. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(op(op(X23,op(X22,X23)),op(X20,op(op(X21,X22),X20))),op(X25,op(op(X26,op(X20,op(op(X21,X22),X20))),X25)))) [superposition 31,26]
224. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(op(op(X74,op(X73,X74)),op(X75,op(op(X76,X73),X75))),op(X72,op(X73,X72)))) [superposition 26,31]
663. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(op(op(X23,op(op(X24,X23),X23)),op(op(op(X24,X23),X23),op(X23,op(op(X24,X23),X23)))),op(X26,op(op(op(X24,X23),X23),X26)))) [superposition 32,39]
684. op(X134,op(op(X131,op(op(X132,X131),X131)),op(X133,X134))) = X134 [superposition 25,39]
748. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(op(X23,op(op(X24,X23),X23)),op(X26,op(op(op(X24,X23),X23),X26)))) [forward demodulation 663,26]
754. op(X3,op(op(op(X1,op(op(X2,X0),X1)),op(X0,op(X1,op(op(X2,X0),X1)))),op(X4,X3))) = X3 [superposition 684,25]
785. op(X0,X2) = op(op(X0,X2),op(X0,op(op(X1,X0),X0))) [superposition 684,26]
847. op(X3,op(op(op(X1,op(op(X2,X0),X1)),X0),op(X4,X3))) = X3 [forward demodulation 754,25]
1097. op(op(X8,X6),X6) = op(op(op(X8,X6),X6),op(X6,op(op(X7,X6),X6))) [superposition 684,785]
1100. op(op(X27,X26),X26) = op(op(op(X27,X26),X26),op(X26,op(X26,X26))) [superposition 42,785]
1101. op(X30,op(X28,X30)) = op(op(X30,op(X28,X30)),op(X28,op(X28,X28))) [superposition 31,785]
1102. op(X31,op(op(X31,op(X31,X31)),op(op(X32,X31),X31))) = X31 [superposition 62,785]
1486. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(op(X237,op(op(X238,X239),X237)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))),op(op(X240,op(X237,op(op(X238,X239),X237))),op(X237,op(op(X238,X239),X237)))),op(X237,op(op(X238,X239),X237)))) [superposition 28,1102]
2088. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(op(X21,op(X19,X21)),op(op(X19,op(X19,X19)),op(op(X18,X19),X19)))) [superposition 31,1100]
2136. op(X224,op(op(op(X225,op(op(op(X222,X223),X223),X225)),op(X223,op(X223,X223))),op(X226,X224))) = X224 [superposition 847,1100]
2199. op(X224,op(op(X225,op(op(op(X222,X223),X223),X225)),op(X226,X224))) = X224 [forward demodulation 2136,26]
3790. op(X14,X15) = op(op(X14,X15),op(X12,op(op(op(X13,X14),X14),X12))) [superposition 2199,26]
3911. op(op(op(X24,X23),X23),X26) = op(op(op(op(X24,X23),X23),X26),op(X23,op(op(X24,X23),X23))) [backward demodulation 748,3790]
4003. op(X62,op(X61,X62)) = op(op(X62,op(X61,X62)),op(op(op(X60,X61),X61),op(X61,op(op(X60,X61),X61)))) [superposition 31,3911]
4163. op(X62,op(X61,X62)) = op(op(X62,op(X61,X62)),op(op(X60,X61),X61)) [forward demodulation 4003,1097]
4202. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(op(X21,op(X19,X21)),op(X19,op(X19,X19)))) [backward demodulation 2088,4163]
4239. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(X237,op(op(X238,X239),X237)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))),op(X237,op(op(X238,X239),X237)))) [backward demodulation 1486,4163]
4330. op(X20,op(X19,X20)) = op(op(X20,op(X19,X20)),op(X21,op(X19,X21))) [forward demodulation 4202,1101]
4380. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237))),op(X237,op(op(X238,X239),X237)))) [forward demodulation 4239,4330]
4381. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(op(X237,op(op(X238,X239),X237)),op(X237,op(op(X238,X239),X237)))) [forward demodulation 4380,4330]
4382. op(X241,op(X239,X241)) = op(op(X241,op(X239,X241)),op(X237,op(op(X238,X239),X237))) [forward demodulation 4381,4330]
4464. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(op(X23,op(X22,X23)),op(X25,op(op(X26,op(X20,op(op(X21,X22),X20))),X25)))) [backward demodulation 191,4382]
4478. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(op(X74,op(X73,X74)),op(X72,op(X73,X72)))) [backward demodulation 224,4382]
4906. op(X77,op(op(X78,op(X72,op(X73,X72))),X77)) = op(op(X77,op(op(X78,op(X72,op(X73,X72))),X77)),op(X74,op(X73,X74))) [forward demodulation 4478,4330]
4914. op(X21,op(X20,X21)) = op(op(X21,op(X20,X21)),op(X22,op(op(X23,op(X18,op(op(X19,X20),X18))),X22))) [backward demodulation 66,4906]
4948. op(X24,op(op(X20,op(op(X21,X22),X20)),X24)) = op(op(X24,op(op(X20,op(op(X21,X22),X20)),X24)),op(X23,op(X22,X23))) [backward demodulation 4464,4914]
4950. op(X2,X3) = op(op(X2,X3),op(X4,op(op(X0,op(op(X1,X2),X0)),X4))) [backward demodulation 30,4948]
5701. op(X17,X19) = op(op(X17,X19),op(op(X18,op(X17,X18)),op(X15,op(op(X16,X17),X15)))) [superposition 4950,26]
5829. op(X17,X19) = op(op(X17,X19),op(X18,op(X17,X18))) [forward demodulation 5701,4382]
5856. op(X0,op(X3,op(X0,X3))) = X0 [superposition 5829,25]
6572. op(X12,op(X11,X12)) = X12 [superposition 5856,5829]
6656. op(X1,op(op(X2,X0),X1)) = op(op(X1,op(op(X2,X0),X1)),X3) [backward demodulation 26,6572]
8341. ! [X0,X1,X2] : X0 = op(X0,op(X1,X2)) [backward demodulation 38,6572]
8342. op(X1,X3) = X1 [forward demodulation 6656,6572]
8351. ! [X0,X1,X2] : X0 = op(X0,op(X1,op(X2,op(X0,X2)))) [subsumption resolution 8341,8342]
"#;

        // Segment 3: the final goal proof — still no lemma_0004..0008 usage
        let seg3 = r#"The conjecture is true! Here is a proof.

Axiom 1 (history_lemma_0151): op(op(X, op(X, X)), X) = op(op(Y, op(Z, X)), X).

Goal 1 (conjecture0): op(x0, x0) = op(op(x1, op(x2, x0)), x0).
Proof:
  op(x0, x0)
= { by axiom 1 (history_lemma_0151) }
  op(op(x1, op(x2, x0)), x0)

RESULT: Theorem (the conjecture is true).
"#;
        // Use trim_proof_parts: block is the "start" vampire block,
        // seg1 is the "root" vampire block, seg3 is sub-proof.
        let (kept_start, kept_hist, kept_root, _start_steps, hist_steps, root_steps) =
            trim_proof_parts(
                Some((block, "vampire", count_superposition_steps(block))),
                None,
                (
                    "history_lemma_0151",
                    seg2,
                    "vampire",
                    proof_length_vampire(seg2),
                ),
                Some(seg3),
            );

        // history is None -> empty string + 0 steps
        assert!(kept_hist.trim().is_empty());
        assert_eq!(hist_steps, 0);

        // start exists -> should not be empty
        assert!(!kept_start.trim().is_empty());

        // start is vampire-trimmed
        assert!(!kept_start.trim().is_empty());
        assert!(kept_start.contains("% lemma_0001:"));
        assert!(kept_start.contains("% lemma_0002:"));
        assert!(kept_start.contains("% lemma_0003:"));
        assert!(kept_start.contains("% lemma_0004:"));
        assert!(kept_start.contains("% lemma_0005:"));
        assert!(kept_start.contains("% lemma_0006:"));

        // Root block must be empty
        assert!(!kept_root.trim().is_empty());

        // Step accounting
        assert_eq!(root_steps, 44);
        assert_eq!(proof_length_twee(seg3), 1);
    }
}
