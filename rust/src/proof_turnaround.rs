use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Term in equational logic
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Skolem(String),
    Fun(String, Vec<Term>),
}

/// AST for formulas with quantifiers
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Eq(Term, Term),
    Neq(Term, Term),
    Forall(Vec<String>, Box<Formula>),
    Exists(Vec<String>, Box<Formula>),
    Const(String), // $true or $false
}

impl Formula {
    /// Pretty-print formula to string
    pub fn to_string(&self) -> String {
        match self {
            Formula::Eq(a, b) => format!("{} = {}", term_to_string(a), term_to_string(b)),
            Formula::Neq(a, b) => format!("{} != {}", term_to_string(a), term_to_string(b)),
            Formula::Forall(vars, f) => format!("! [{}] : {}", vars.join(","), f.to_string()),
            Formula::Exists(vars, f) => format!("? [{}] : {}", vars.join(","), f.to_string()),
            Formula::Const(c) => c.clone(),
        }
    }
}

/// Pretty-print term
fn term_to_string(t: &Term) -> String {
    match t {
        Term::Var(s) => s.clone(),
        Term::Skolem(s) => s.clone(),
        Term::Fun(f, args) => {
            let inner: Vec<String> = args.iter().map(term_to_string).collect();
            format!("{}({})", f, inner.join(","))
        }
    }
}

/// Step in the proof
#[derive(Debug, Clone)]
pub struct SuperpositionStep {
    pub formula: Formula,
    pub deps: Vec<(usize, usize)>,
    pub is_negated_conjecture: bool,
    pub rule: String,
}

/// Check if a rule is a real proof step
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

/* ------------------ PARSING ------------------ */

/// Converts Vampire formula strings into Formula AST
/// Only handles equational logic with optional quantifiers
fn parse_formula(s: &str) -> Formula {
    let s = s.trim();

    // handle $false / $true
    if s == "$false" || s == "$true" {
        return Formula::Const(s.to_string());
    }

    // quantifiers
    if let Some(caps) = Regex::new(r"^!\s*\[([^\]]*)\]\s*:\s*(.*)$")
        .unwrap()
        .captures(s)
    {
        let vars: Vec<String> = caps[1]
            .split(',')
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty())
            .collect();
        let inner = parse_formula(&caps[2]);
        return Formula::Forall(vars, Box::new(inner));
    }

    if let Some(caps) = Regex::new(r"^\?\s*\[([^\]]*)\]\s*:\s*(.*)$")
        .unwrap()
        .captures(s)
    {
        let vars: Vec<String> = caps[1]
            .split(',')
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty())
            .collect();
        let inner = parse_formula(&caps[2]);
        return Formula::Exists(vars, Box::new(inner));
    }

    // Eq or Neq
    if let Some((lhs, rhs)) = s.split_once("!=") {
        Formula::Neq(parse_term(lhs), parse_term(rhs))
    } else if let Some((lhs, rhs)) = s.split_once('=') {
        Formula::Eq(parse_term(lhs), parse_term(rhs))
    } else {
        panic!("Cannot parse formula: {}", s);
    }
}

/// Parse term (naive)
fn parse_term(s: &str) -> Term {
    let s = s.trim();
    if let Some(caps) = Regex::new(r"^([a-zA-Z_][a-zA-Z0-9_]*)\((.*)\)$")
        .unwrap()
        .captures(s)
    {
        let f = caps[1].to_string();
        let args_str = &caps[2];
        let args: Vec<Term> = split_top_level(args_str, ',')
            .into_iter()
            .map(|t| parse_term(&t))
            .collect();
        Term::Fun(f, args)
    } else if s.starts_with("sK") {
        Term::Skolem(s.to_string())
    } else {
        Term::Var(s.to_string())
    }
}

/// Split top-level comma-separated terms
fn split_top_level(s: &str, sep: char) -> Vec<String> {
    let mut res = Vec::new();
    let mut depth = 0;
    let mut buf = String::new();
    for c in s.chars() {
        match c {
            '(' => {
                depth += 1;
                buf.push(c);
            }
            ')' => {
                depth -= 1;
                buf.push(c);
            }
            c if c == sep && depth == 0 => {
                res.push(buf.trim().to_string());
                buf.clear();
            }
            _ => buf.push(c),
        }
    }
    if !buf.trim().is_empty() {
        res.push(buf.trim().to_string());
    }
    res
}

/// Parse Vampire proof into steps
/// Parse Vampire proof into steps (robust version)
pub fn parse_vampire_proof(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let mut steps_map = BTreeMap::new();

    // Regex to capture: step number, optional dot, rest of line
    let line_re = Regex::new(r"^\s*(\d+)\s*[.]?\s*(.*)$").unwrap();

    for line in proof_text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('%') {
            continue;
        }

        let caps = match line_re.captures(line) {
            Some(c) => c,
            None => continue,
        };

        let idx: usize = caps[1].parse().unwrap();
        let rest = caps[2].trim();

        // Split off optional inference/dependency part in brackets
        let (before_inf, inf_part) = match rest.rsplit_once('[') {
            Some((b, i)) => (b.trim(), Some(i)),
            None => (rest.trim(), None),
        };

        // Extract formula (handle optional ':' after label)
        let formula_str = match before_inf.split_once(':') {
            Some((_, f)) => f.trim(),
            None => before_inf,
        };

        let formula = parse_formula(formula_str);

        let mut is_negated_conjecture = false;
        let mut rule = "unknown".to_string();
        let mut deps = Vec::new();

        if let Some(inf) = inf_part {
            let inf = inf.trim_end_matches(']').trim();

            if inf.contains("negated conjecture") {
                is_negated_conjecture = true;
            }

            // First word is the rule
            if let Some(first) = inf.split_whitespace().next() {
                rule = first.to_string();
            }

            // Dependencies: numbers in the inference
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


/* ------------------ DEPENDENCIES ------------------ */

fn build_forward_deps(steps: &BTreeMap<usize, SuperpositionStep>) -> BTreeMap<usize, Vec<usize>> {
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

/* ------------------ NEGATED CHAIN ------------------ */

struct NegChain {
    start: Option<usize>,
    chain_vec: Vec<usize>,
    chain_set: BTreeSet<usize>,
    forward: BTreeMap<usize, Vec<usize>>,
}

fn compute_neg_chain(steps: &BTreeMap<usize, SuperpositionStep>) -> Option<NegChain> {
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

    println!("\n[DEBUG] Negated conjecture chain");
    for &i in &chain_vec {
        println!("  {}: {:?} {:?}", i, steps[&i].formula, steps[&i].rule);
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

/* ------------------ CONTRAPOSITIVE TRANSFORM ------------------ */

/// Contrapose a formula recursively with polarity flipping
/// polarity: true = flip (negative context)
fn contrapose_formula(f: &Formula, polarity: bool) -> Formula {
    match f {
        Formula::Eq(a, b) => {
            if polarity {
                Formula::Neq(a.clone(), b.clone())
            } else {
                Formula::Eq(a.clone(), b.clone())
            }
        }
        Formula::Neq(a, b) => {
            if polarity {
                Formula::Eq(a.clone(), b.clone())
            } else {
                Formula::Neq(a.clone(), b.clone())
            }
        }
        Formula::Forall(vars, sub) => {
            if polarity {
                Formula::Exists(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            } else {
                Formula::Forall(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            }
        }
        Formula::Exists(vars, sub) => {
            if polarity {
                Formula::Forall(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            } else {
                Formula::Exists(vars.clone(), Box::new(contrapose_formula(sub, polarity)))
            }
        }
        Formula::Const(c) => match c.as_str() {
            "$true" => Formula::Const("$false".to_string()),
            "$false" => Formula::Const("$true".to_string()),
            _ => Formula::Const(c.clone()),
        },
    }
}

/// Replace Skolem constants with variables, respecting polarity
fn skolem_to_variable(f: &Formula, polarity: bool) -> Formula {
    let mut map = HashMap::new();
    let mut counter = 0;

    fn walk(
        f: &Formula,
        map: &mut HashMap<String, String>,
        counter: &mut usize,
        polarity: bool,
    ) -> Formula {
        match f {
            Formula::Eq(a, b) => Formula::Eq(
                walk_term(a, map, counter, polarity),
                walk_term(b, map, counter, polarity),
            ),
            Formula::Neq(a, b) => Formula::Neq(
                walk_term(a, map, counter, polarity),
                walk_term(b, map, counter, polarity),
            ),
            Formula::Forall(vars, sub) => {
                Formula::Forall(vars.clone(), Box::new(walk(sub, map, counter, polarity)))
            }
            Formula::Exists(vars, sub) => {
                Formula::Exists(vars.clone(), Box::new(walk(sub, map, counter, polarity)))
            }
            Formula::Const(c) => Formula::Const(c.clone()),
        }
    }

    fn walk_term(
        t: &Term,
        map: &mut HashMap<String, String>,
        counter: &mut usize,
        polarity: bool,
    ) -> Term {
        match t {
            Term::Skolem(s) => {
                let v = map.entry(s.clone()).or_insert_with(|| {
                    if polarity {
                        let name = format!("X{}", counter);
                        *counter += 1;
                        println!("[DEBUG] Skolem {} replaced with variable {}", s, name);
                        name
                    } else {
                        println!("[DEBUG] Skolem {} left unchanged", s);
                        s.clone()
                    }
                });
                Term::Var(v.clone())
            }
            Term::Var(v) => Term::Var(v.clone()),
            Term::Fun(f, args) => Term::Fun(
                f.clone(),
                args.iter()
                    .map(|x| walk_term(x, map, counter, polarity))
                    .collect(),
            ),
        }
    }

    walk(f, &mut map, &mut counter, polarity)
}

fn flatten_and_reorder_quantifiers(f: Formula) -> Formula {
    match f {
        Formula::Forall(mut vars, sub) => {
            let inner = flatten_and_reorder_quantifiers(*sub);
            match inner {
                Formula::Forall(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Forall(vars, inner_sub)
                }
                Formula::Exists(inner_vars, inner_sub) => {
                    // mixed quantifier: move Forall outside Exists
                    Formula::Exists(inner_vars, Box::new(Formula::Forall(vars, inner_sub)))
                }
                other => Formula::Forall(vars, Box::new(other)),
            }
        }
        Formula::Exists(mut vars, sub) => {
            let inner = flatten_and_reorder_quantifiers(*sub);
            match inner {
                Formula::Exists(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Exists(vars, inner_sub)
                }
                Formula::Forall(inner_vars, inner_sub) => {
                    // mixed quantifier: move Exists outside Forall
                    Formula::Forall(inner_vars, Box::new(Formula::Exists(vars, inner_sub)))
                }
                other => Formula::Exists(vars, Box::new(other)),
            }
        }
        Formula::Eq(a, b) => Formula::Eq(a, b),
        Formula::Neq(a, b) => Formula::Neq(a, b),
        Formula::Const(c) => Formula::Const(c),
    }
}

/* ------------------ CONTRAPOSITIVE SWAP ------------------ */

/// Collect all variables (Var + Skolem) in a term
fn collect_vars(t: &Term, vars: &mut BTreeSet<String>) {
    match t {
        Term::Var(v) => {
            vars.insert(v.clone());
        }
        Term::Skolem(s) => {
            vars.insert(s.clone());
        }
        Term::Fun(_, args) => {
            for a in args {
                collect_vars(a, vars);
            }
        }
    }
}

/// Collect all variables in a formula recursively
fn formula_vars(f: &Formula) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    match f {
        Formula::Eq(a, b) | Formula::Neq(a, b) => {
            collect_vars(a, &mut vars);
            collect_vars(b, &mut vars);
        }
        Formula::Forall(vs, sub) | Formula::Exists(vs, sub) => {
            for v in vs {
                vars.insert(v.clone());
            }
            vars.extend(formula_vars(sub));
        }
        Formula::Const(_) => {}
    }
    vars
}

/// Contrapositive swap: flip polarity, replace Skolem -> variable, flatten & reorder, and track new vars
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
        // track vars before
        let vars_before = formula_vars(&step.formula);

        // apply transformations
        let f = contrapose_formula(&step.formula, true); // Step 1: flip polarity
        let f = skolem_to_variable(&f, true); // Step 2: Skolem -> variable
        let f = flatten_and_reorder_quantifiers(f); // Step 3: flatten/reorder quantifiers
        step.formula = f.clone();

        // track vars after
        let vars_after = formula_vars(&step.formula);
        let new_vars: Vec<_> = vars_after.difference(&vars_before).cloned().collect();
        if !new_vars.is_empty() {
            println!(
                "[DEBUG] Step {}: New variables introduced during contrapositive: {:?}",
                idx, new_vars
            );
        }
    }

    order.push(idx);
}

/* ------------------ TURN PROOF AROUND ------------------ */

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

    println!("\n[DEBUG] Turn order {:?}", order);

    let mut result = steps.clone();
    for (old, new) in order.iter().zip(order.iter().rev()) {
        let mut step = new_steps[old].clone();
        step.rule = steps[new].rule.clone();
        step.deps = steps[new].deps.clone();
        result.insert(*new, step);
    }

    result
}

/* ------------------ TOP-LEVEL PROCEDURE ------------------ */

pub fn eq_proof_procedure(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let steps = parse_vampire_proof(proof_text);
    if needs_proof_turnaround(&steps) {
        println!("\n[DEBUG] Turnaround required");
        turn_proof_around(&steps)
    } else {
        println!("\n[DEBUG] No turnaround needed");
        steps
    }
}

/* ------------------ CHECK TURNAROUND ------------------ */

pub fn needs_proof_turnaround(steps: &BTreeMap<usize, SuperpositionStep>) -> bool {
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
            return steps[&next].formula.to_string() != "$false";
        }
    }

    false
}

/* ------------------ DEBUG ------------------ */

pub fn debug_print_parsed_proof(proof_text: &str) {
    let steps = parse_vampire_proof(proof_text);

    println!("\n[DEBUG] Parsed Vampire proof");
    for (idx, step) in &steps {
        println!(
            "{:>4}. formula = {:?}, deps = {:?}, is_neg = {:?}, rule = {:?}",
            idx,
            step.formula.to_string(),
            step.deps,
            step.is_negated_conjecture,
            step.rule
        );
    }
    println!("-------------------------------\n");
}

/// Format a proof (BTreeMap<usize, SuperpositionStep>) as Vampire-style text
pub fn _format_proof(steps: &BTreeMap<usize, SuperpositionStep>) -> String {
    let mut lines = Vec::new();

    for (&idx, step) in steps {
        let formula_str = step.formula.to_string();
        let deps_str = if step.deps.is_empty() {
            "".to_string()
        } else {
            step.deps
                .iter()
                .map(|(_, d)| d.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };

        let mut line = format!("{}. {}", idx, formula_str);
        if !deps_str.is_empty() || !step.rule.is_empty() {
            line.push_str(" [");
            if !deps_str.is_empty() {
                line.push_str(&deps_str);
            }
            if !step.rule.is_empty() {
                if !deps_str.is_empty() {
                    line.push_str(", ");
                }
                line.push_str(&step.rule);
            }
            if step.is_negated_conjecture {
                line.push_str(", negated conjecture");
            }
            line.push(']');
        }

        lines.push(line);
    }

    lines.join("\n")
}

/// Pretty-print the proof in the desired format
pub fn print_proof_steps(steps: &BTreeMap<usize, SuperpositionStep>) {
    for (idx, step) in steps {
        // Formula as string
        let formula_str = step.formula.to_string();

        // Dependencies as [(a,b), ...]
        let deps_str = if step.deps.is_empty() {
            "[]".to_string()
        } else {
            let deps_vec: Vec<String> = step
                .deps
                .iter()
                .map(|(a, b)| format!("({}, {})", a, b))
                .collect();
            format!("[{}]", deps_vec.join(", "))
        };

        // is_neg as true/false
        let is_neg_str = if step.is_negated_conjecture {
            "true"
        } else {
            "false"
        };

        println!(
            "{}. formula = \"{}\", deps = {}, is_neg = {}, rule = \"{}\"",
            idx, formula_str, deps_str, is_neg_str, step.rule
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //     #[test]
    //     fn proof_turnaround() {
    //         let proof_text = r#"
    // % Running in auto input_syntax mode. Trying TPTP
    // % Refutation found. Thanks to Tanya!
    // % SZS status Theorem for Equation2892_implies_Equation2680
    // % SZS output start Proof for Equation2892_implies_Equation2680
    // 1. ! [X0,X1,X2] : op(op(op(X0,op(X1,X2)),X2),X2) = X0 [input]
    // 2. ! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [input]
    // 3. ~! [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) = X0 [negated conjecture 2]
    // 4. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 [ennf transformation 3]
    // 5. ? [X0,X1,X2] : op(op(op(X0,X1),op(X2,X0)),X1) != X0 => sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [choice axiom]
    // 6. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [skolemisation 4,5]
    // 7. op(op(op(X0,op(X1,X2)),X2),X2) = X0 [cnf transformation 1]
    // 8. sK0 != op(op(op(sK0,sK1),op(sK2,sK0)),sK1) [cnf transformation 6]
    // 9. op(op(op(X3,X0),X2),X2) = X3 [superposition 7,7]
    // 13. op(X0,op(X1,X2)) = op(X0,X2) [superposition 9,7]
    // 14. op(X3,X4) = op(X3,X5) [superposition 9,9]
    // 20. sK0 != op(op(op(sK0,sK1),sK0),sK1) [backward demodulation 8,13]
    // 21. op(op(op(X0,X1),X2),X3) = X0 [superposition 14,9]
    // 30. sK0 != op(op(op(sK0,sK1),X12),sK1) [superposition 20,14]
    // 39. $false [subsumption resolution 30,21]
    // % SZS output end Proof for Equation2892_implies_Equation2680
    // % ------------------------------
    // % Version: Vampire 4.8 (commit )
    // % Termination reason: Refutation

    // % Memory used [KB]: 4989
    // % Time elapsed: 0.0000 s
    // % ------------------------------
    // % ------------------------------
    // "#;
    //         debug_print_parsed_proof(proof_text);

    //         let steps_map = parse_vampire_proof(proof_text);

    //         assert!(
    //             needs_proof_turnaround(&steps_map),
    //             "Proof should require turnaround but was not detected"
    //         );

    //         let steps = eq_proof_procedure(proof_text);

    //         let final_steps = eq_proof_procedure(&proof_text);
    //         print_proof_steps(&final_steps);

    //         // println!("\n[DEBUG] FINAL STEPS");
    //         // for (idx, step) in &steps {
    //         //     println!(
    //         //         "  {}: {:?} with {:?} and rule = {:?}",
    //         //         idx, step.formula, step.deps, step.rule
    //         //     );
    //         // }
    //     }

#[test]
fn test_mixed_quantifiers_contrapositive() {
    use crate::*;

    // Simulate a small Vampire-like proof that triggers mixed quantifiers and contrapositive swap
    let proof_text = r#"
1. ! [X,Y] : f(X) = f(Y) [input]
2. ? [sK0] : f(a) != sK0 [negated conjecture 1]
3  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 1,2]
4  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 2,3]
5. $false  [superposition 3,4]
"#;

    debug_print_parsed_proof(proof_text);

    let mut steps = parse_vampire_proof(proof_text);

    // Ensure turnaround is needed
    assert!(needs_proof_turnaround(&steps), "Turnaround should be detected");

    let turned = turn_proof_around(&steps);

    println!("\n[DEBUG] TURNED PROOF STEPS");
    for (idx, step) in &turned {
        println!("  {}: {}", idx, step.formula.to_string());
    }

    // Check that the contrapositive + Skolem-to-variable + quantifier flattening worked
    let step2_formula = &turned[&2].formula.to_string();
    println!("\n[DEBUG] Step 2 formula after turnaround: {}", step2_formula);

    // Expectation:
    // - Forall over sK0 (converted to X0)
    // - Exists Y inside
    assert!(step2_formula.contains("! [X0] : ? [Y]"), "Step 2 should have mixed quantifiers ![X0] : ?[Y]");
    assert!(step2_formula.contains("f(Y) = X0") || step2_formula.contains("f(Y) != X0"), "Step 2 should have variable Y inside");
}


    // #[test]
    // fn no_proof_turnaround() {
    //     let proof_text = r#"
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
    //     debug_print_parsed_proof(proof_text);
    //     let steps_map = parse_vampire_proof(proof_text);
    //     assert!(!needs_proof_turnaround(&steps_map));
    // }

    // #[test]
    // fn proof_turnaround_dif() {
    //     let proof_text = r#"
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
    //     debug_print_parsed_proof(proof_text);

    //     let steps_map = parse_vampire_proof(proof_text);

    //     assert!(
    //         needs_proof_turnaround(&steps_map),
    //         "Proof should require turnaround but was not detected"
    //     );

    //     let steps = eq_proof_procedure(proof_text);

    //     let final_steps = eq_proof_procedure(&proof_text);
    //     print_proof_steps(&final_steps);
    // }
}
