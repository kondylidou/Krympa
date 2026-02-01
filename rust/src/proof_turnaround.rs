use std::collections::{BTreeMap, BTreeSet};
use regex::Regex;

#[derive(Debug, Clone)]
pub struct SuperpositionStep {
    pub formula: String,
    pub deps: Vec<(usize, usize)>,
    pub is_negated_conjecture: bool,
    pub rule: String,
}

fn is_proof_step(rule: &str) -> bool {
    matches!(
        rule,
        "demodulation"
            | "superposition"
            | "resolution"
            | "inequality"
            | "backward"
            | "forward"
            | "subsumption"
    )
}

pub fn parse_vampire_proof(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let mut map = BTreeMap::new();

    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('%') {
            continue;
        }

        let Some((idx_part, rest)) = line.split_once('.') else {
            continue;
        };
        let Ok(idx) = idx_part.trim().parse::<usize>() else {
            continue;
        };

        // Split into LHS and inference part
        let (before_inf, inf_part) = match rest.rsplit_once('[') {
            Some((b, i)) => (b.trim(), Some(i)),
            None => (rest.trim(), None),
        };

        // Extract formula AFTER colon
        let formula = match before_inf.split_once(':') {
            Some((_, f)) => f.trim().to_string(),
            None => before_inf.to_string(),
        };

        let mut is_negated_conjecture = false;
        let mut rule = "unknown".to_string(); // default value
        let mut deps = Vec::new();

        if let Some(inf) = inf_part {
            let inf = inf.trim_end_matches(']').trim();

            if inf.contains("negated conjecture") {
                is_negated_conjecture = true;
            }

            // Take the first token as rule, or keep "unknown"
            if let Some(first) = inf.split_whitespace().next() {
                rule = first.to_string();
            }

            deps = inf
                .split(|c: char| c == ',' || c.is_whitespace())
                .filter_map(|tok| tok.parse::<usize>().ok())
                .map(|d| (0, d))
                .collect();
        }

        map.insert(
            idx,
            SuperpositionStep {
                formula,
                deps,
                is_negated_conjecture,
                rule,
            },
        );
    }

    map
}

pub fn debug_print_parsed_proof(proof_text: &str) {
    let steps = parse_vampire_proof(proof_text);

    println!("\n===== PARSED VAMPIRE PROOF =====");
    for (idx, step) in &steps {
        println!(
            "{:>4}. formula = {:?}, deps = {:?}, is_neg = {:?}, has rule = {:?}",
            idx, step.formula, step.deps, step.is_negated_conjecture, step.rule
        );
    }
    println!("================================\n");
}

fn build_forward_deps(
    steps_map: &BTreeMap<usize, SuperpositionStep>,
) -> BTreeMap<usize, Vec<usize>> {
    let mut forward: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

    for (&idx, step) in steps_map {
        for &(_, dep) in &step.deps {
            forward.entry(dep).or_default().push(idx);
        }
    }

    println!("\n== FORWARD DEPENDENCIES ==");
    for (k, v) in &forward {
        println!("  {} -> {:?}", k, v);
    }

    forward
}

fn gather_forward_chain(
    start: usize,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
) {
    if !visited.insert(start) {
        return;
    }

    if let Some(nexts) = forward.get(&start) {
        for &n in nexts {
            gather_forward_chain(n, forward, visited);
        }
    }
}pub fn needs_proof_turnaround(
    steps_map: &BTreeMap<usize, SuperpositionStep>,
) -> bool {
    let forward = build_forward_deps(steps_map);

    // negated conjecture roots
    let negated_roots: Vec<usize> = steps_map
        .iter()
        .filter(|(_, s)| s.is_negated_conjecture)
        .map(|(&i, _)| i)
        .collect();

    if negated_roots.is_empty() {
        return false;
    }

    // REUSE the existing chain builder
    let (_prev, chain_vec) =
        build_neg_chain_and_prev_step(steps_map, &forward, &negated_roots);

    println!("\n== NEGATED CONJECTURE CHAIN ==");
    for &i in &chain_vec {
        let s = &steps_map[&i];
        println!("  {}: {} {:?}", i, s.formula, s.rule);
    }

    // find FIRST proof step
    for (pos, &i) in chain_vec.iter().enumerate() {
        let step = &steps_map[&i];

        if is_proof_step(&step.rule) {
            println!("\nFirst proof step in chain: {}", i);

            // check what immediately follows
            if pos + 1 >= chain_vec.len() {
                return false; // nothing follows → safe
            }

            let next = chain_vec[pos + 1];
            println!("Next step after proof step: {}", next);

            return steps_map[&next].formula != "$false";
        }
    }

    false
}

/// Build the negated conjecture chain and find the step immediately before the first proof step.
/// Returns a tuple: (Some(prev_idx) if there is a step before the first proof step, None otherwise, full chain vector)
fn build_neg_chain_and_prev_step(
    steps_map: &BTreeMap<usize, SuperpositionStep>,
    forward: &BTreeMap<usize, Vec<usize>>,
    negated_roots: &[usize],
) -> (Option<usize>, Vec<usize>) {
    // 1. Build forward chain from negated roots
    let mut chain = BTreeSet::new();
    for &r in negated_roots {
        gather_forward_chain(r, forward, &mut chain);
    }

    // 2. Sort chain into vector
    let mut chain_vec: Vec<usize> = chain.into_iter().collect();
    chain_vec.sort();

    println!("\n== NEGATED CONJECTURE CHAIN ==");
    for &i in &chain_vec {
        let s = &steps_map[&i];
        println!("  {}: {} {:?}", i, s.formula, s.rule);
    }

    // 3. Find first proof step and its previous step
    for (pos, &i) in chain_vec.iter().enumerate() {
        let step = &steps_map[&i];

        if is_proof_step(&step.rule) {
            println!("\nFirst proof step in chain: {}", i);

            if pos == 0 {
                // no step before first proof step
                return (None, chain_vec);
            }

            let prev = chain_vec[pos - 1];
            println!("Step immediately before first proof step: {}", prev);

            return (Some(prev), chain_vec);
        }
    }

    // No proof step found in chain
    (None, chain_vec)
}


/// Simple contrapositive transformation for disequality formulas
fn contrapositive_formula(formula: &str) -> String {
    formula.replace("!=", "=") // naive contrapositive for equational logic
}

/// Replace all Skolem constants sK\d+ -> X0, X1, X2...
fn skolem_to_variable(formula: &str) -> String {
    let re = Regex::new(r"sK\d+").unwrap();
    let mut counter = 0;
    let mut replaced = formula.to_string();

    for mat in re.find_iter(formula) {
        let var = format!("X{}", counter);
        replaced = replaced.replace(mat.as_str(), &var);
        counter += 1;
    }

    replaced
}

fn contrapositive_swap(
    idx: usize,
    steps_map: &mut BTreeMap<usize, SuperpositionStep>,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
    chain: &BTreeSet<usize>, // only swap steps in this chain
) {
    if !visited.insert(idx) || !chain.contains(&idx) {
        return;
    }

    let dependents = forward
        .get(&idx)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .filter(|d| chain.contains(d)) // only follow chain steps
        .collect::<Vec<_>>();

    // recurse first
    for &dep in &dependents {
        contrapositive_swap(dep, steps_map, forward, visited, order, chain);
    }

    // process current step
    if let Some(step) = steps_map.get_mut(&idx) {
        println!("\nProcessing step {}: {}", idx, step.formula);
        step.formula = contrapositive_formula(&step.formula);
        step.formula = skolem_to_variable(&step.formula);
        println!("  -> Result: {}", step.formula);
    }
    
    order.push(idx);
}


pub fn turn_proof_around(
    steps_map: &BTreeMap<usize, SuperpositionStep>,
) -> BTreeMap<usize, SuperpositionStep> {
    let forward = build_forward_deps(steps_map);

    // 1. Identify negated conjecture roots
    let negated_roots: Vec<usize> = steps_map
        .iter()
        .filter(|(_, s)| s.is_negated_conjecture)
        .map(|(&i, _)| i)
        .collect();

    if negated_roots.is_empty() {
        return steps_map.clone();
    }

    // 2. Build negated chain and start step
    let (start_idx_opt, chain_vec) = build_neg_chain_and_prev_step(&steps_map, &forward, &negated_roots);
    let chain_set: BTreeSet<usize> = chain_vec.iter().cloned().collect();

    if start_idx_opt.is_none() {
        return steps_map.clone();
    }
    let start_idx = start_idx_opt.unwrap();

    // 3. Compute local order along the chain
    let mut new_steps = steps_map.clone();
    let mut visited = BTreeSet::new();
    let mut local_order: Vec<usize> = Vec::new();

    contrapositive_swap(start_idx, &mut new_steps, &forward, &mut visited, &mut local_order, &chain_set);

    // 4. Reverse local_order to swap the chain
    let mut reversed_order = local_order.clone();
    reversed_order.reverse();

    // 5. Apply contrapositive and Skolem replacements, and swap indices
    let mut final_steps = steps_map.clone();

    for (i, &old_idx) in local_order.iter().enumerate() {
        let new_idx = reversed_order[i];
        let mut step = new_steps[&old_idx].clone();

        // Contrapositive disequalities
        step.formula = contrapositive_formula(&step.formula);
        step.formula = skolem_to_variable(&step.formula);

        // Replace $false by positive conjecture
        if step.formula == "$false" {
            step.formula = "$true".to_string();
        }

        // Mark as contraposed
        //step.rule = Some("contraposed".to_string());
        step.rule = steps_map[&new_idx].rule.clone();

        step.deps = steps_map[&new_idx].deps.clone();

        // Insert step at the new index in final map
        final_steps.insert(new_idx, step);
        
    }

    final_steps
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_turnaround() {
        let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation2892_implies_Equation2680
% SZS output start Proof for Equation2892_implies_Equation2680
1. ! [X0,X1,X2] : op(op(op(X0,op(X1,X2)),X2),X2) = X0 [input]
2. ! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [input]
3. ~! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [negated conjecture 2]
4. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 [ennf transformation 3]
5. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 => sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [choice axiom]
6. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [skolemisation 4,5]
7. op(op(op(X0,op(X1,X2)),X2),X2) = X0 [cnf transformation 1]
8. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [cnf transformation 6]
9. op(op(op(X3,X0),X2),X2) = X3 [superposition 7,7]
13. op(X0,op(X1,X2)) = op(X0,X2) [superposition 9,7]
14. op(X3,X4) = op(X3,X5) [superposition 9,9]
20. sK0 != op(op(op(sK0,sK1),sK0),sK1) [backward demodulation 8,13]
21. op(op(op(X0,X1),X2),X3) = X0 [superposition 14,9]
30. sK0 != op(op(op(sK0,sK1),X12),sK1) [superposition 20,14]
39. $false [subsumption resolution 30,21]
% SZS output end Proof for Equation2892_implies_Equation2680
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 4989
% Time elapsed: 0.0000 s
% ------------------------------
% ------------------------------
"#;
        debug_print_parsed_proof(proof_text);

        let steps_map = parse_vampire_proof(proof_text);
        println!("== NEGATED CONJECTURE STEPS ==");
        for (idx, step) in &steps_map {
            if step.is_negated_conjecture {
                println!("  {}: {}", idx, step.formula);
            }
        }

        assert!(needs_proof_turnaround(&steps_map));

        let steps = turn_proof_around(&steps_map);
        println!("== FINAL STEPS ==");
        for (idx, step) in &steps {
            println!("  {}: {} with {:?} and rule = {:?}", idx, step.formula, step.deps, step.rule);
        }

    }

    #[test]
    fn no_proof_turnaround() {
        let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation650_implies_Equation448
% SZS output start Proof for Equation650_implies_Equation448
2. ! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [input]
3. ~! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [negated conjecture 2]
30. ! [X0,X1,X2,X3] : op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [input]
51. ! [X0,X1,X2] : op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [input]
64. ! [X0,X1,X2] : op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [input]
71. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 [ennf transformation 3]
72. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 => sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [choice axiom]
73. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [skolemisation 71,72]
75. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [cnf transformation 73]
102. op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [cnf transformation 30]
123. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [cnf transformation 51]
136. op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [cnf transformation 64]
141. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),X2) [backward demodulation 123,136]
143. op(X3,op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) = X3 [backward demodulation 102,136]
144. op(X2,op(X0,op(op(X1,X0),X0))) = X2 [backward demodulation 136,141]
146. op(X3,op(X0,op(X1,op(op(X2,X1),X1)))) = X3 [forward demodulation 143,141]
147. op(X3,X0) = X3 [forward demodulation 146,144]
158. sK0 != op(sK0,sK1) [backward demodulation 75,147]
159. $false [subsumption resolution 158,147]
% SZS output end Proof for Equation650_implies_Equation448
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 4989
% Time elapsed: 0.002 s
% ------------------------------
% ------------------------------
"#;
        debug_print_parsed_proof(proof_text);

        let steps_map = parse_vampire_proof(proof_text);
        println!("== NEGATED CONJECTURE STEPS ==");
        for (idx, step) in &steps_map {
            if step.is_negated_conjecture {
                println!("  {}: {}", idx, step.formula);
            }
        }

        assert!(!needs_proof_turnaround(&steps_map));
    }

        #[test]
    fn proof_turnaround_dif() {
        let proof_text = r#"
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for Equation4417_implies_Equation4429
% SZS output start Proof for Equation4417_implies_Equation4429
1. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [input]
2. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [input]
3. ~! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [negated conjecture 2]
4. ! [X0,X1,X2] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [rectify 1]
5. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) [ennf transformation 3]
6. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) => op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [choice axiom]
7. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [skolemisation 5,6]
8. op(X0,op(X0,X1)) = op(op(X2,X0),X2) [cnf transformation 4]
9. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [cnf transformation 7]
11. op(op(X7,op(X4,X5)),X7) = op(op(X4,X5),op(X5,op(X5,X6))) [superposition 8,8]
12. op(op(X2,X0),X2) = op(op(X3,X0),X3) [superposition 8,8]
15. op(X1,op(X1,X2)) = op(X1,op(X1,X3)) [superposition 8,8]
16. op(sK0,op(sK0,sK1)) != op(sK3,op(sK3,X0)) [superposition 9,8]
18. op(sK0,op(sK0,sK1)) != op(op(X1,sK3),X1) [superposition 16,8]
43. op(X8,op(X8,X11)) = op(X8,op(op(X10,X8),X10)) [superposition 15,8]
249. op(X17,op(X17,X19)) = op(op(X20,op(op(X17,op(X17,X18)),X17)),X20) [superposition 11,8]
273. op(sK0,op(sK0,sK1)) != op(op(X23,op(op(sK3,op(sK3,X22)),sK3)),X23) [superposition 18,11]
340. op(op(X60,op(X57,X58)),X60) = op(op(X57,op(op(X59,X57),X59)),X57) [superposition 12,43]
11843. op(sK0,op(sK0,sK1)) != op(op(X16,op(op(sK3,X15),X17)),X16) [superposition 273,340]
12695. op(sK0,op(sK0,sK1)) != op(op(X2,op(X2,X3)),X2) [superposition 11843,43]
14320. op(sK0,op(sK0,sK1)) != op(X48,op(X48,X50)) [superposition 12695,249]
15184. $false [equality resolution 14320]
% SZS output end Proof for Equation4417_implies_Equation4429
% ------------------------------
% Version: Vampire 4.8 (commit )
% Termination reason: Refutation

% Memory used [KB]: 29935
% Time elapsed: 0.301 s
% ------------------------------
% ------------------------------
"#;
        debug_print_parsed_proof(proof_text);

        let steps_map = parse_vampire_proof(proof_text);
        println!("== NEGATED CONJECTURE STEPS ==");
        for (idx, step) in &steps_map {
            if step.is_negated_conjecture {
                println!("  {}: {}", idx, step.formula);
            }
        }

        assert!(needs_proof_turnaround(&steps_map));

        let steps = turn_proof_around(&steps_map);
        println!("== FINAL STEPS ==");
        for (idx, step) in &steps {
            println!("  {}: {} with {:?} and rule = {:?}", idx, step.formula, step.deps, step.rule);
        }

    }
}

