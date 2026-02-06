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
            Formula::Forall(vars, f) => {
                let inner = match **f {
                    Formula::Forall(_, _) | Formula::Exists(_, _) => format!("({})", f.to_string()),
                    _ => f.to_string(),
                };
                format!("! [{}] : {}", vars.join(","), inner)
            }
            Formula::Exists(vars, f) => {
                let inner = match **f {
                    Formula::Forall(_, _) | Formula::Exists(_, _) => format!("({})", f.to_string()),
                    _ => f.to_string(),
                };
                format!("? [{}] : {}", vars.join(","), inner)
            }
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
    pub rule: String, // full rule name
}

/// Check if a rule is a real proof step
fn is_proof_step(rule: &str) -> bool {
    rule.starts_with("superposition")
        || rule.starts_with("resolution")
        || rule.starts_with("factoring")
        || rule.starts_with("equality factoring")
        || rule.starts_with("equality resolution")
        || rule.starts_with("inequality resolution")
        || rule.starts_with("rewriting")
        || rule.starts_with("demodulation")
        || rule.starts_with("forward demodulation")
        || rule.starts_with("backward demodulation")
        || rule.starts_with("simplification")
        || rule.starts_with("subsumption")
        || rule.starts_with("distinctness")
        || rule.starts_with("trivial inequality removal")
        || rule == "equality"
        || rule == "inequality"
}

/* ------------------ PARSING ------------------ */

/// Converts Vampire formula strings into Formula AST
/// Only handles equational logic with optional quantifiers
pub fn parse_formula(s: &str) -> Formula {
    let mut bound = BTreeSet::<String>::new();
    parse_formula_with_bound(s.trim(), &mut bound)
}

/// Parse formulas with possibly chained leading quantifiers.
/// Handles:
///   ! [X] : F
///   ? [X] : F
///   ? [X] ! [Y] : F   (colon after first binder is optional)
fn parse_formula_with_bound(s: &str, bound: &mut BTreeSet<String>) -> Formula {
    let s = s.trim();

    if s == "$false" || s == "$true" {
        return Formula::Const(s.to_string());
    }

    // quantifier head with OPTIONAL ":" so "? [sK0] ! [Y] : ..." parses.
    let qre = Regex::new(r"^([!?])\s*\[([^\]]*)\]\s*(?::\s*)?(.*)$").unwrap();
    if let Some(caps) = qre.captures(s) {
        let q = &caps[1];
        let vars: Vec<String> = caps[2]
            .split(',')
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty())
            .collect();
        let rest = caps[3].trim();

        // push scope
        for v in &vars {
            bound.insert(v.clone());
        }

        let inner = parse_formula_with_bound(rest, bound);

        // pop scope
        for v in &vars {
            bound.remove(v);
        }

        return if q == "!" {
            Formula::Forall(vars, Box::new(inner))
        } else {
            Formula::Exists(vars, Box::new(inner))
        };
    }

    // base Eq/Neq
    if let Some((lhs, rhs)) = s.split_once("!=") {
        Formula::Neq(parse_term(lhs, bound), parse_term(rhs, bound))
    } else if let Some((lhs, rhs)) = s.split_once('=') {
        Formula::Eq(parse_term(lhs, bound), parse_term(rhs, bound))
    } else {
        panic!("Cannot parse formula: {}", s);
    }
}

/// Parse term (simple)
fn parse_term(s: &str, bound: &BTreeSet<String>) -> Term {
    let s = s.trim();

    if let Some(caps) = Regex::new(r"^([a-zA-Z_][a-zA-Z0-9_]*)\((.*)\)$")
        .unwrap()
        .captures(s)
    {
        let f = caps[1].to_string();
        let args_str = &caps[2];
        let args: Vec<Term> = split_top_level(args_str, ',')
            .into_iter()
            .map(|t| parse_term(&t, bound))
            .collect();
        return Term::Fun(f, args);
    }

    // if the name is bound by a quantifier, it is a variable even if it starts with sK.
    if bound.contains(s) {
        return Term::Var(s.to_string());
    }

    if s.starts_with("sK") {
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

/// Don't strip quantifier colons. Only strip genuine "label: formula" prefixes.
fn strip_optional_label(s: &str) -> &str {
    let s = s.trim();

    if s.starts_with('!') || s.starts_with('?') {
        return s;
    }

    if let Some((lhs, rhs)) = s.split_once(':') {
        let lhs = lhs.trim();
        let looks_like_label = !lhs.is_empty()
            && !lhs.contains(' ')
            && !lhs.contains('=')
            && !lhs.contains('!')
            && !lhs.contains('?')
            && !lhs.contains('(');

        if looks_like_label {
            return rhs.trim();
        }
    }

    s
}

/// Parse the bracket part, e.g.
///   "backward demodulation 8,13"
///   "subsumption resolution 30,21"
///   "negated conjecture 2"
/// Returns: (rule_full, deps, is_negated_conjecture)
fn parse_inf_bracket(inf: &str) -> (String, Vec<usize>, bool) {
    let inf = inf.trim().trim_end_matches(']').trim();

    let is_neg = inf.contains("negated conjecture");

    // deps: collect all integers anywhere
    let deps: Vec<usize> = inf
        .split(|c: char| c == ',' || c.is_whitespace())
        .filter_map(|tok| tok.parse::<usize>().ok())
        .collect();

    // rule_full: take all non-numeric words, excluding "negated conjecture"
    let mut words: Vec<String> = Vec::new();
    let toks: Vec<&str> = inf.split_whitespace().collect();

    let mut i = 0;
    while i < toks.len() {
        let tok = toks[i].trim_end_matches(',');

        // skip numeric tokens
        if tok.chars().all(|c| c.is_ascii_digit()) {
            i += 1;
            continue;
        }

        // skip "negated conjecture" tokens, but remember they were there
        if tok == "negated" && i + 1 < toks.len() && toks[i + 1] == "conjecture" {
            i += 2;
            continue;
        }

        // keep other words
        if tok.chars().any(|c| c.is_alphabetic()) {
            words.push(tok.to_string());
        }
        i += 1;
    }

    let rule_full = if !words.is_empty() {
        words.join(" ")
    } else if is_neg {
        "negated conjecture".to_string()
    } else {
        "unknown".to_string()
    };

    (rule_full, deps, is_neg)
}

/// Parse Vampire proof into steps (robust-ish)
pub fn parse_vampire_proof(proof_text: &str) -> BTreeMap<usize, SuperpositionStep> {
    let mut steps_map = BTreeMap::new();
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

        // split off optional inference/dependency part in brackets
        let (before_inf, inf_part) = match rest.rsplit_once('[') {
            Some((b, i)) => (b.trim(), Some(i)),
            None => (rest.trim(), None),
        };

        let formula_str = strip_optional_label(before_inf);
        let formula = parse_formula(formula_str);

        let mut is_negated_conjecture = false;
        let mut rule = "unknown".to_string();
        let mut deps = Vec::new();

        if let Some(inf) = inf_part {
            let inf = inf.trim_end_matches(']').trim();

            let (rule_full, deps_nums, is_neg) = parse_inf_bracket(inf);

            is_negated_conjecture = is_neg;
            rule = rule_full;

            deps = deps_nums.into_iter().map(|d| (0, d)).collect();
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

    let mut start = None;
    for (pos, &i) in chain_vec.iter().enumerate() {
        if is_proof_step(&steps[&i].rule) {
            start = pos.checked_sub(1).map(|p| chain_vec[p]);
            break;
        }
    }

    Some(NegChain {
        start,
        chain_set: chain,
        forward,
    })
}
/* ------------------ Trivial EQUALITY ELIMINATION ------------------ */

fn is_reflexive_eq(f: &Formula) -> bool {
    match f {
        Formula::Eq(a, b) => a == b,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => is_reflexive_eq(sub),
        _ => false,
    }
}

fn is_reflexive_neq(f: &Formula) -> bool {
    match f {
        Formula::Neq(a, b) => a == b,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => is_reflexive_neq(sub),
        _ => false,
    }
}

/// “Trivial” steps we don't want to count/print/use as explicit premises:
/// - reflexive equality: t = t  (possibly under quantifiers)
/// - (optionally) reflexive disequality: t != t  (usually only appears briefly)
/// - the turned-around equality-resolution node: $true [equality ...]
fn is_trivial_step(step: &SuperpositionStep) -> bool {
    if is_reflexive_eq(&step.formula) || is_reflexive_neq(&step.formula) {
        return true;
    }

    // turned equality-resolution node becomes $true and should be eliminated
    if step.rule == "equality" {
        if let Formula::Const(c) = &step.formula {
            if c == "$true" {
                return true;
            }
        }
    }

    false
}

/// Remove dependencies that point to trivial steps
/// This makes “use t=t as implicit premise” work naturally: the dep is dropped
fn drop_trivial_deps(steps: &mut BTreeMap<usize, SuperpositionStep>) {
    let trivial: BTreeSet<usize> = steps
        .iter()
        .filter_map(|(&i, s)| if is_trivial_step(s) { Some(i) } else { None })
        .collect();

    for (_, step) in steps.iter_mut() {
        step.deps.retain(|&(_, d)| !trivial.contains(&d));
    }
}

/// remove trivial steps from the map
/// IMPORTANT: indices become “gappy” (fine) unless we renumber (TODO)
fn remove_trivial_steps(steps: &mut BTreeMap<usize, SuperpositionStep>) {
    let trivial_ids: Vec<usize> = steps
        .iter()
        .filter_map(|(&i, s)| if is_trivial_step(s) { Some(i) } else { None })
        .collect();

    for i in trivial_ids {
        steps.remove(&i);
    }
}

/// A true step count
pub fn _count_nontrivial_steps(steps: &BTreeMap<usize, SuperpositionStep>) -> usize {
    steps.values().filter(|s| !is_trivial_step(s)).count()
}

/* ------------------ CORE LOGIC: CONTRAPOSITIVE (EQUATIONAL) ------------------ */

fn core_is_diseq(f: &Formula) -> bool {
    match f {
        Formula::Neq(_, _) => true,
        Formula::Eq(_, _) | Formula::Const(_) => false,
        Formula::Forall(_, sub) | Formula::Exists(_, sub) => core_is_diseq(sub),
    }
}

/// Negate in an equational setting:
/// - Eq <-> Neq under polarity
/// - ∀ <-> ∃ under polarity
/// - Constants unchanged (we handle $false -> $true separately for proof-turning)
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
        Formula::Const(c) => Formula::Const(c.clone()),
    }
}

/// Replace Skolem constants (Term::Skolem) with fresh variables (X0, X1, ...).
/// This is ONLY for actual Term::Skolem occurrences (not bound vars).
fn skolem_to_variable(f: &Formula) -> Formula {
    let mut map: HashMap<String, String> = HashMap::new();
    let mut counter: usize = 0;

    fn walk_term(t: &Term, map: &mut HashMap<String, String>, counter: &mut usize) -> Term {
        match t {
            Term::Skolem(s) => {
                let v = map.entry(s.clone()).or_insert_with(|| {
                    let name = format!("X{}", *counter);
                    *counter += 1;
                    name
                });
                Term::Var(v.clone())
            }
            Term::Var(v) => Term::Var(v.clone()),
            Term::Fun(f, args) => Term::Fun(
                f.clone(),
                args.iter().map(|a| walk_term(a, map, counter)).collect(),
            ),
        }
    }

    fn walk(f: &Formula, map: &mut HashMap<String, String>, counter: &mut usize) -> Formula {
        match f {
            Formula::Eq(a, b) => {
                Formula::Eq(walk_term(a, map, counter), walk_term(b, map, counter))
            }
            Formula::Neq(a, b) => {
                Formula::Neq(walk_term(a, map, counter), walk_term(b, map, counter))
            }
            Formula::Forall(vars, sub) => {
                Formula::Forall(vars.clone(), Box::new(walk(sub, map, counter)))
            }
            Formula::Exists(vars, sub) => {
                Formula::Exists(vars.clone(), Box::new(walk(sub, map, counter)))
            }
            Formula::Const(c) => Formula::Const(c.clone()),
        }
    }

    walk(f, &mut map, &mut counter)
}

/// Flatten consecutive same-kind quantifiers (∀∀..., ∃∃...).
fn flatten_quantifiers(f: Formula) -> Formula {
    match f {
        Formula::Forall(mut vars, sub) => {
            let inner = flatten_quantifiers(*sub);
            match inner {
                Formula::Forall(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Forall(vars, inner_sub)
                }
                other => Formula::Forall(vars, Box::new(other)),
            }
        }
        Formula::Exists(mut vars, sub) => {
            let inner = flatten_quantifiers(*sub);
            match inner {
                Formula::Exists(mut inner_vars, inner_sub) => {
                    vars.append(&mut inner_vars);
                    Formula::Exists(vars, inner_sub)
                }
                other => Formula::Exists(vars, Box::new(other)),
            }
        }
        other => other,
    }
}

/// Cosmetic but requested: rename bound variables that look like sK\d+ to X0,X1,...
/// This is scope-safe (handles shadowing).
fn rename_skolem_like_bound_vars(f: &Formula) -> Formula {
    let sk_like = Regex::new(r"^sK\d+$").unwrap();
    let mut counter: usize = 0;

    fn rename_term(t: &Term, env: &Vec<HashMap<String, String>>) -> Term {
        match t {
            Term::Var(v) => {
                for scope in env.iter().rev() {
                    if let Some(nv) = scope.get(v) {
                        return Term::Var(nv.clone());
                    }
                }
                Term::Var(v.clone())
            }
            Term::Skolem(s) => Term::Skolem(s.clone()),
            Term::Fun(f, args) => Term::Fun(
                f.clone(),
                args.iter().map(|a| rename_term(a, env)).collect(),
            ),
        }
    }

    fn walk(
        f: &Formula,
        sk_like: &Regex,
        counter: &mut usize,
        env: &mut Vec<HashMap<String, String>>,
    ) -> Formula {
        match f {
            Formula::Forall(vars, sub) => {
                let mut scope: HashMap<String, String> = HashMap::new();
                let mut new_vars: Vec<String> = Vec::with_capacity(vars.len());
                for v in vars {
                    if sk_like.is_match(v) {
                        let nv = format!("X{}", *counter);
                        *counter += 1;
                        scope.insert(v.clone(), nv.clone());
                        new_vars.push(nv);
                    } else {
                        new_vars.push(v.clone());
                    }
                }
                env.push(scope);
                let new_sub = walk(sub, sk_like, counter, env);
                env.pop();
                Formula::Forall(new_vars, Box::new(new_sub))
            }
            Formula::Exists(vars, sub) => {
                let mut scope: HashMap<String, String> = HashMap::new();
                let mut new_vars: Vec<String> = Vec::with_capacity(vars.len());
                for v in vars {
                    if sk_like.is_match(v) {
                        let nv = format!("X{}", *counter);
                        *counter += 1;
                        scope.insert(v.clone(), nv.clone());
                        new_vars.push(nv);
                    } else {
                        new_vars.push(v.clone());
                    }
                }
                env.push(scope);
                let new_sub = walk(sub, sk_like, counter, env);
                env.pop();
                Formula::Exists(new_vars, Box::new(new_sub))
            }
            Formula::Eq(a, b) => Formula::Eq(rename_term(a, env), rename_term(b, env)),
            Formula::Neq(a, b) => Formula::Neq(rename_term(a, env), rename_term(b, env)),
            Formula::Const(c) => Formula::Const(c.clone()),
        }
    }

    let mut env: Vec<HashMap<String, String>> = Vec::new();
    walk(f, &sk_like, &mut counter, &mut env)
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

/// Contrapositive swap:
/// - recurse along forward edges inside `chain`
/// - if the step is (core) disequality: negate it to equality, replace Skolems with fresh Xk vars
/// - universally quantify those newly introduced Xk vars
/// - keep a stable traversal order in `order`
fn contrapositive_swap(
    idx: usize,
    steps: &mut BTreeMap<usize, SuperpositionStep>,
    forward: &BTreeMap<usize, Vec<usize>>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
    chain: &BTreeSet<usize>,
) {
    if !chain.contains(&idx) || !visited.insert(idx) {
        return;
    }

    // Recurse first so `order` becomes a post-order (useful for later re-threading).
    if let Some(nexts) = forward.get(&idx) {
        for &n in nexts.iter().filter(|n| chain.contains(n)) {
            contrapositive_swap(n, steps, forward, visited, order, chain);
        }
    }

    if let Some(step) = steps.get_mut(&idx) {
        // 0) Special case: refutation node
        if let Formula::Const(c) = &step.formula {
            if c == "$false" {
                step.formula = Formula::Const("$true".to_string());
                order.push(idx);
                return;
            }
        }

        if core_is_diseq(&step.formula) {
            // 1) Save vars before (we only care about existing Xk vars to detect fresh ones later).
            let before = formula_vars(&step.formula);
            let before_x: BTreeSet<String> = before
                .into_iter()
                .filter(|v| v.starts_with('X')) // only track the "fresh" namespace
                .collect();

            // 2) Flip polarity: Neq -> Eq (and handles quantifiers if present)
            let mut f = contrapose_formula(&step.formula, true);

            // 3) Replace Skolem constants with fresh Xk variables
            f = skolem_to_variable(&f);

            // 4) Flatten quantifiers (purely structural/cosmetic)
            f = flatten_quantifiers(f);

            // 5) Cosmetic rename of bound vars that look like sK\d+
            f = rename_skolem_like_bound_vars(&f);

            // 6) Compute *new* X vars introduced by skolem_to_variable
            let after = formula_vars(&f);
            let after_x: BTreeSet<String> =
                after.into_iter().filter(|v| v.starts_with('X')).collect();

            let mut new_xs: Vec<String> = after_x.difference(&before_x).cloned().collect();
            new_xs.sort(); // deterministic printing and quantifier order

            // 7) Bind them universally (Skolems -> universally quantified vars)
            if !new_xs.is_empty() {
                f = Formula::Forall(new_xs.clone(), Box::new(f));
            }

            step.formula = f;
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
        return steps.clone();
    };

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

    //println!("\n[DEBUG] Turn order {:?}", order);

    let mut result = steps.clone();
    for (old, new) in order.iter().zip(order.iter().rev()) {
        let mut step = new_steps[old].clone();
        step.rule = steps[new].rule.clone();
        step.deps = steps[new].deps.clone();
        result.insert(*new, step);
    }

    // treat t=t and turned equality-resolution as trivial
    drop_trivial_deps(&mut result);

    // actually remove them from the proof object
    remove_trivial_steps(&mut result);

    result
}

/* ------------------ TOP-LEVEL PROCEDURE ------------------ */

pub fn eq_proof_procedure(proof_text: &str) -> String {
    let parsed = parse_vampire_proof(proof_text);

    // Always turn the proof
    let final_steps = turn_proof_around(&parsed);

    let formatted = format_proof(&final_steps);

    _debug_print_parsed_proof(&parsed);
    println!("\n[DEBUG] Contrapositive Vampire proof");
    println!("{}", formatted);
    println!("-------------------------------");

    formatted
}

/* ------------------ DEBUG ------------------ */

pub fn _debug_print_parsed_proof(steps: &BTreeMap<usize, SuperpositionStep>) {
    println!("\n[DEBUG] Parsed Vampire proof");
    for (idx, step) in steps {
        println!(
            "{:>4}. formula = {:?}, deps = {:?}, is_neg = {:?}, rule = {:?}",
            idx,
            step.formula.to_string(),
            step.deps,
            step.is_negated_conjecture,
            step.rule
        );
    }
    println!("-------------------------------");
}

/// Format a proof (BTreeMap<usize, SuperpositionStep>) as Vampire-style text
/// Format a proof (BTreeMap<usize, SuperpositionStep>) as Vampire-style text
/// Desired bracket style: [rule dep1,dep2] (Vampire-ish)
pub fn format_proof(steps: &BTreeMap<usize, SuperpositionStep>) -> String {
    let mut lines = Vec::new();

    for (&idx, step) in steps {
        let formula_str = step.formula.to_string();

        // deps like "1,2" (no spaces)
        let deps_str = step
            .deps
            .iter()
            .map(|(_, d)| d.to_string())
            .collect::<Vec<_>>()
            .join(",");

        // Decide what goes in [...]
        let mut parts: Vec<String> = Vec::new();

        // Put rule first (if known), then deps
        let rule = step.rule.trim();
        if !rule.is_empty() && rule != "unknown" {
            if deps_str.is_empty() {
                parts.push(rule.to_string());
            } else {
                parts.push(format!("{} {}", rule, deps_str));
            }
        } else if !deps_str.is_empty() {
            // no rule, but deps exist
            parts.push(deps_str.clone());
        }

        let mut line = format!("{}. {}", idx, formula_str);

        if !parts.is_empty() {
            line.push_str(" [");
            line.push_str(&parts.join(", "));
            line.push(']');
        }

        lines.push(line);
    }

    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eliminates_turned_equality_resolution_and_reflexive_eq() {
        let proof_text = r#"
    1. g(X) = f(X) [input]
    2. g(g(b)) != f(f(b)) [negated conjecture]
    3. g(f(b)) != f(f(b)) [superposition 1,2]
    4. f(f(b)) != f(f(b)) [superposition 1,3]
    5. $false [equality resolution 4]
    "#;

        let parsed = parse_vampire_proof(proof_text);

        // we expect the “useful” turned proof to have 3 nontrivial steps:
        // 1) axiom
        // 2) g(f(b)) = f(f(b))  (contraposed from step 3, using implicit f(f(b))=f(f(b)))
        // 3) g(g(b)) = f(f(b))  (contraposed from step 2)

        let steps = turn_proof_around(&parsed);
        assert_eq!(_count_nontrivial_steps(&steps), 4);

        // check that the key equalities appear somewhere in the result
        // (qe don't rely on exact indices because the turnaround rethreads indices)
        let strs: Vec<String> = steps.values().map(|s| s.formula.to_string()).collect();

        assert!(strs.iter().any(|s| s.contains("g(X) = f(X)")));
        assert!(strs.iter().any(|s| s.contains("g(f(b)) = f(f(b))")));
        assert!(strs.iter().any(|s| s.contains("g(g(b)) = f(f(b))")));

        // also ensure we didn't keep a visible reflexive equality as a step
        assert!(!strs.iter().any(|s| s.trim() == "f(f(b)) = f(f(b))"));
    }

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

        let steps_map = parse_vampire_proof(proof_text);
        _debug_print_parsed_proof(&steps_map);
        let final_proof = eq_proof_procedure(&proof_text);
        println!("\n[TEST] Final proof");
        println!("{}", final_proof);
    }

    #[test]
    fn test_mixed_quantifiers_contrapositive() {
        // Simulate a small Vampire-like proof that triggers mixed quantifiers and contrapositive swap
        let proof_text = r#"
    1. ! [X,Y] : f(X) = f(Y) [input]
    2. ? [sK0] : f(a) != sK0 [negated conjecture 1]
    3  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 1,2]
    4  ? [sK0] ! [Y] : f(Y) != sK0 [superposition 2,3]
    5. $false  [superposition 3,4]
    "#;

        let steps = parse_vampire_proof(proof_text);
        _debug_print_parsed_proof(&steps);
        let turned = turn_proof_around(&steps);
        println!("\n[TEST] Turned proof steps");
        for (idx, step) in &turned {
            println!("  {}: {}", idx, step.formula.to_string());
        }

        // Check that the contrapositive + Skolem-to-variable + quantifier flattening worked
        let step4_formula = &turned[&4].formula.to_string();
        println!(
            "\n[TEST] Step 4 formula after turnaround: {}",
            step4_formula
        );
        let step5_formula = &turned[&5].formula.to_string();
        println!(
            "\n[TEST] Step 5 formula after turnaround: {}",
            step5_formula
        );

        // Expectation:
        // - Forall over sK0 (converted to X0)
        // - Exists Y inside
        assert!(
            step4_formula.contains("! [X0] : (? [Y]"),
            "Step 4 should have mixed quantifiers ![X0] : ?[Y]"
        );
        assert!(
            step5_formula.contains("f(a) = X0") || step5_formula.contains("f(Y) != X0"),
            "Step 5 should have variable Y inside"
        );
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

        let parsed = parse_vampire_proof(proof_text);
        let turned = turn_proof_around(&parsed);

        // Collect steps in index order
        let mut steps: Vec<(&usize, &SuperpositionStep)> = turned.iter().collect();
        steps.sort_by_key(|(i, _)| *i);

        // Get last two steps
        let (idx2, step2) = steps[steps.len() - 2];
        let (idx1, step1) = steps[steps.len() - 1];

        // Assertions on indices (optional but nice)
        assert_eq!(*idx2, 158);
        assert_eq!(*idx1, 159);

        // Assertions on formulas (exact)
        assert_eq!(
            step2.formula.to_string(),
            "! [X0,X1] : X0 = op(X0,X1)",
            "Unexpected second-to-last formula"
        );

        assert_eq!(
            step1.formula.to_string(),
            "! [X0,X1,X2] : X0 = op(X0,op(X1,op(X2,op(X0,X2))))",
            "Unexpected last formula"
        );
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

        let steps_map = parse_vampire_proof(proof_text);
        _debug_print_parsed_proof(&steps_map);
        let final_proof = eq_proof_procedure(&proof_text);
        println!("\n[TEST] Final proof");
        println!("{}", final_proof);
    }
}
