use std::collections::{BTreeMap, BTreeSet, HashMap};
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
            | "equality"
    )
}

/* ===================== PARSING ===================== */

pub fn parse_vampire_proof(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let mut steps_map = BTreeMap::new();

    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('%') {
            continue;
        }

        let Some((idx_part, rest)) = line.split_once('.') else { continue };
        let Ok(idx) = idx_part.trim().parse::<usize>() else { continue };

        let (before_inf, inf_part) = match rest.rsplit_once('[') {
            Some((b, i)) => (b.trim(), Some(i)),
            None => (rest.trim(), None),
        };

        let formula = match before_inf.split_once(':') {
            Some((_, f)) => f.trim().to_string(),
            None => before_inf.to_string(),
        };

        let mut is_negated_conjecture = false;
        let mut rule = "unknown".to_string();
        let mut deps = Vec::new();

        if let Some(inf) = inf_part {
            let inf = inf.trim_end_matches(']').trim();

            if inf.contains("negated conjecture") {
                is_negated_conjecture = true;
            }

            if let Some(first) = inf.split_whitespace().next() {
                rule = first.to_string();
            }

            deps = inf
                .split(|c: char| c == ',' || c.is_whitespace())
                .filter_map(|tok| tok.parse::<usize>().ok())
                .map(|d| (0, d))
                .collect();
        }

        steps_map.insert(
            idx,
            SuperpositionStep {
                formula,
                deps,
                is_negated_conjecture,
                rule,
            },
        );
    }

    steps_map
}

pub fn debug_print_parsed_proof(proof_text: &str) {
    let steps = parse_vampire_proof(proof_text);

    println!("\n[DEBUG] PARSED VAMPIRE PROOF");
    for (idx, step) in &steps {
        println!(
            "{:>4}. formula = {:?}, deps = {:?}, is_neg = {:?}, rule = {:?}",
            idx, step.formula, step.deps, step.is_negated_conjecture, step.rule
        );
    }
    println!("--------------------------------\n");
}

/* ===================== DEPENDENCIES ===================== */

fn build_forward_deps(
    steps: &BTreeMap<usize, SuperpositionStep>,
) -> BTreeMap<usize, Vec<usize>> {
    let mut forward: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

    for (&idx, step) in steps {
        for &(_, dep) in &step.deps {
            forward.entry(dep).or_default().push(idx);
        }
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
}

/* ===================== NEGATED CHAIN ===================== */

struct NegChain {
    start: Option<usize>,
    chain_vec: Vec<usize>,
    chain_set: BTreeSet<usize>,
    forward: BTreeMap<usize, Vec<usize>>,
}

fn compute_neg_chain(
    steps: &BTreeMap<usize, SuperpositionStep>,
) -> Option<NegChain> {
    let forward = build_forward_deps(steps);

    let neg_roots: Vec<usize> = steps
        .iter()
        .filter(|(_, s)| s.is_negated_conjecture)
        .map(|(&i, _)| i)
        .collect();

    if neg_roots.is_empty() {
        return None;
    }

    let mut chain = BTreeSet::new();
    for &r in &neg_roots {
        gather_forward_chain(r, &forward, &mut chain);
    }

    let chain_vec: Vec<usize> = chain.iter().cloned().collect();

    println!("\n[DEBUG] NEGATED CONJECTURE CHAIN");
    for &i in &chain_vec {
        println!("  {}: {} {:?}", i, steps[&i].formula, steps[&i].rule);
    }

    let mut start = None;
    for (pos, &i) in chain_vec.iter().enumerate() {
        if is_proof_step(&steps[&i].rule) {
            println!("\n[DEBUG] First proof step in chain: {}", i);
            start = pos.checked_sub(1).map(|p| chain_vec[p]);
            break;
        }
    }

    Some(NegChain {
        start,
        chain_set: chain,
        chain_vec,
        forward,
    })
}

/* ===================== NEEDS TURNAROUND ===================== */

pub fn needs_proof_turnaround(
    steps: &BTreeMap<usize, SuperpositionStep>,
) -> bool {
    let Some(chain) = compute_neg_chain(steps) else {
        return false;
    };

    let vec = &chain.chain_vec;

    for (pos, &i) in vec.iter().enumerate() {
        if is_proof_step(&steps[&i].rule) {
            if pos + 1 >= vec.len() {
                return false;
            }
            let next = vec[pos + 1];
            println!("[DEBUG] Next step: {}", next);
            return steps[&next].formula != "$false";
        }
    }

    false
}

/* ===================== FORMULA TRANSFORMS ===================== */

fn contrapositive_formula(formula: &str) -> String {
    formula.replace("!=", "=")
}

fn skolem_to_variable(formula: &str) -> String {
    let re = Regex::new(r"sK\d+").unwrap();
    let mut map = HashMap::new();
    let mut counter = 0;

    re.replace_all(formula, |caps: &regex::Captures| {
        map.entry(caps[0].to_string())
            .or_insert_with(|| {
                let v = format!("X{}", counter);
                counter += 1;
                v
            })
            .clone()
    })
    .to_string()
}

/* ===================== CONTRAPOSITIVE DFS ===================== */

fn contrapositive_swap(
    idx: usize,
    steps: &mut BTreeMap<usize, SuperpositionStep>,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
    chain: &BTreeSet<usize>,
) {
    if !visited.insert(idx) || !chain.contains(&idx) {
        return;
    }

    if let Some(nexts) = forward.get(&idx) {
        for &n in nexts.iter().filter(|n| chain.contains(n)) {
            contrapositive_swap(n, steps, forward, visited, order, chain);
        }
    }

    if let Some(step) = steps.get_mut(&idx) {
        println!("[DEBUG] Contrapositiving {}: {}", idx, step.formula);
        step.formula = skolem_to_variable(&contrapositive_formula(&step.formula));
        if step.formula == "$false" {
            step.formula = "$true".to_string();
        }
        println!("        -> {}", step.formula);
    }

    order.push(idx);
}

/* ===================== TURN PROOF AROUND ===================== */

pub fn turn_proof_around(
    steps: &BTreeMap<usize, SuperpositionStep>,
) -> BTreeMap<usize, SuperpositionStep> {
    let Some(chain) = compute_neg_chain(steps) else {
        return steps.clone();
    };

    let Some(start) = chain.start else {
        println!("[DEBUG] No turnaround needed");
        return steps.clone();
    };

    println!("[DEBUG] Turnaround starts at {}", start);

    let mut new_steps = steps.clone();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();

    contrapositive_swap(
        start,
        &mut new_steps,
        &chain.forward,
        &mut visited,
        &mut order,
        &chain.chain_set,
    );

    println!("\n[DEBUG] TURN ORDER {:?}", order);

    let mut result = steps.clone();
    for (old, new) in order.iter().zip(order.iter().rev()) {
        let mut step = new_steps[old].clone();
        step.rule = steps[new].rule.clone();
        step.deps = steps[new].deps.clone();
        result.insert(*new, step);
    }

    result
}

/* ===================== TOP-LEVEL PROCEDURE ===================== */

pub fn eq_proof_procedure(
    proof_text: &str,
) -> BTreeMap<usize, SuperpositionStep> {
    println!("\n[DEBUG] Parsing proof");
    let steps = parse_vampire_proof(proof_text);

    println!("\n[DEBUG] Checking if turnaround is needed");
    if needs_proof_turnaround(&steps) {
        println!("\n[DEBUG] Turnaround required");
        turn_proof_around(&steps)
    } else {
        println!("\n[DEBUG] No turnaround needed");
        steps
    }
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
        // Debug parse
        debug_print_parsed_proof(proof_text);

        // Parse once for analysis
        let steps_map = parse_vampire_proof(proof_text);

        // 1. Must detect that turnaround is needed
        assert!(
            needs_proof_turnaround(&steps_map),
            "Proof should require turnaround but was not detected"
        );

        // 2. Run full procedure (decides + transforms)
        let steps = eq_proof_procedure(proof_text);

        // 3. Final proof must NOT contain $false after turnaround
        assert!(
            steps.values().all(|s| s.formula != "$false"),
            "Turned proof must not contain $false"
        );

        // Debug output (kept as requested)
        println!("\n[DEBUG] FINAL STEPS");
        for (idx, step) in &steps {
            println!(
                "  {}: {} with {:?} and rule = {:?}",
                idx, step.formula, step.deps, step.rule
            );
        }

    }

//     #[test]
//     fn no_proof_turnaround() {
//         let proof_text = r#"
// % Running in auto input_syntax mode. Trying TPTP
// % Refutation found. Thanks to Tanya!
// % SZS status Theorem for Equation650_implies_Equation448
// % SZS output start Proof for Equation650_implies_Equation448
// 2. ! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [input]
// 3. ~! [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) = X0 [negated conjecture 2]
// 30. ! [X0,X1,X2,X3] : op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [input]
// 51. ! [X0,X1,X2] : op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [input]
// 64. ! [X0,X1,X2] : op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [input]
// 71. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 [ennf transformation 3]
// 72. ? [X0,X1,X2] : op(X0,op(X1,op(X2,op(X0,X2)))) != X0 => sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [choice axiom]
// 73. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [skolemisation 71,72]
// 75. sK0 != op(sK0,op(sK1,op(sK2,op(sK0,sK2)))) [cnf transformation 73]
// 102. op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) [cnf transformation 30]
// 123. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),op(X2,op(op(X0,op(op(X1,X0),X0)),X2))) [cnf transformation 51]
// 136. op(X2,op(op(X0,op(op(X1,X0),X0)),X2)) = X2 [cnf transformation 64]
// 141. op(X0,op(op(X1,X0),X0)) = op(op(X0,op(op(X1,X0),X0)),X2) [backward demodulation 123,136]
// 143. op(X3,op(X0,op(op(X1,op(op(X2,X1),X1)),X0))) = X3 [backward demodulation 102,136]
// 144. op(X2,op(X0,op(op(X1,X0),X0))) = X2 [backward demodulation 136,141]
// 146. op(X3,op(X0,op(X1,op(op(X2,X1),X1)))) = X3 [forward demodulation 143,141]
// 147. op(X3,X0) = X3 [forward demodulation 146,144]
// 158. sK0 != op(sK0,sK1) [backward demodulation 75,147]
// 159. $false [subsumption resolution 158,147]
// % SZS output end Proof for Equation650_implies_Equation448
// % ------------------------------
// % Version: Vampire 4.8 (commit )
// % Termination reason: Refutation

// % Memory used [KB]: 4989
// % Time elapsed: 0.002 s
// % ------------------------------
// % ------------------------------
// "#;
//         debug_print_parsed_proof(proof_text);
//         let steps_map = parse_vampire_proof(proof_text);
//         assert!(!needs_proof_turnaround(&steps_map));
//     }

//         #[test]
//     fn proof_turnaround_dif() {
//         let proof_text = r#"
// % Running in auto input_syntax mode. Trying TPTP
// % Refutation found. Thanks to Tanya!
// % SZS status Theorem for Equation4417_implies_Equation4429
// % SZS output start Proof for Equation4417_implies_Equation4429
// 1. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [input]
// 2. ! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [input]
// 3. ~! [X0,X1,X2,X3] : op(X0,op(X0,X1)) = op(op(X2,X3),X2) [negated conjecture 2]
// 4. ! [X0,X1,X2] : op(X0,op(X0,X1)) = op(op(X2,X0),X2) [rectify 1]
// 5. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) [ennf transformation 3]
// 6. ? [X0,X1,X2,X3] : op(X0,op(X0,X1)) != op(op(X2,X3),X2) => op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [choice axiom]
// 7. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [skolemisation 5,6]
// 8. op(X0,op(X0,X1)) = op(op(X2,X0),X2) [cnf transformation 4]
// 9. op(sK0,op(sK0,sK1)) != op(op(sK2,sK3),sK2) [cnf transformation 7]
// 11. op(op(X7,op(X4,X5)),X7) = op(op(X4,X5),op(X5,op(X5,X6))) [superposition 8,8]
// 12. op(op(X2,X0),X2) = op(op(X3,X0),X3) [superposition 8,8]
// 15. op(X1,op(X1,X2)) = op(X1,op(X1,X3)) [superposition 8,8]
// 16. op(sK0,op(sK0,sK1)) != op(sK3,op(sK3,X0)) [superposition 9,8]
// 18. op(sK0,op(sK0,sK1)) != op(op(X1,sK3),X1) [superposition 16,8]
// 43. op(X8,op(X8,X11)) = op(X8,op(op(X10,X8),X10)) [superposition 15,8]
// 249. op(X17,op(X17,X19)) = op(op(X20,op(op(X17,op(X17,X18)),X17)),X20) [superposition 11,8]
// 273. op(sK0,op(sK0,sK1)) != op(op(X23,op(op(sK3,op(sK3,X22)),sK3)),X23) [superposition 18,11]
// 340. op(op(X60,op(X57,X58)),X60) = op(op(X57,op(op(X59,X57),X59)),X57) [superposition 12,43]
// 11843. op(sK0,op(sK0,sK1)) != op(op(X16,op(op(sK3,X15),X17)),X16) [superposition 273,340]
// 12695. op(sK0,op(sK0,sK1)) != op(op(X2,op(X2,X3)),X2) [superposition 11843,43]
// 14320. op(sK0,op(sK0,sK1)) != op(X48,op(X48,X50)) [superposition 12695,249]
// 15184. $false [equality resolution 14320]
// % SZS output end Proof for Equation4417_implies_Equation4429
// % ------------------------------
// % Version: Vampire 4.8 (commit )
// % Termination reason: Refutation

// % Memory used [KB]: 29935
// % Time elapsed: 0.301 s
// % ------------------------------
// % ------------------------------
// "#;
//         debug_print_parsed_proof(proof_text);

//         let steps_map = parse_vampire_proof(proof_text);
//         println!("[DEBUG] NEGATED CONJECTURE STEPS");
//         for (idx, step) in &steps_map {
//             if step.is_negated_conjecture {
//                 println!("  {}: {}", idx, step.formula);
//             }
//         }

//         assert!(needs_proof_turnaround(&steps_map));

//         let steps = turn_proof_around(&steps_map);
//         println!("[DEBUG] FINAL STEPS");
//         for (idx, step) in &steps {
//             println!("  {}: {} with {:?} and rule = {:?}", idx, step.formula, step.deps, step.rule);
//         }

//     }
}

