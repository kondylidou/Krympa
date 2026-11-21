//! Terms over one binary operation `op`, and the search that justifies an
//! equation by a single rewrite. The Lean export checks every proof step with
//! it, and step removal uses it to find a shorter derivation.
//!
//! "One rewrite" means one instance of one equation, applied to one or more
//! occurrences of the same subterm, optionally followed by closing the goal
//! with an instance of a second equation. That is the shape of a superposition
//! inference (Vampire rewrites all occurrences at once).

use crate::regex_cache::cached_regex;
use std::collections::{BTreeSet, HashMap};

const VAR_NAMES: [&str; 25] = [
    "x", "y", "z", "w", "v", "u", "t", "s", "r", "q", "p", "o", "n", "m", "l", "k", "j", "i", "g",
    "f", "e", "d", "c", "b", "a",
];
const HOLE: &str = "hole";

fn fresh_name(i: usize) -> String {
    match VAR_NAMES.get(i) {
        Some(name) => name.to_string(),
        None => format!("x{}", i),
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(String),
    /// A variable of an equation that is being instantiated, as (tag, name).
    /// The variables of the goal are `Var`s and behave as constants.
    Pattern(char, String),
    Op(Box<Term>, Box<Term>),
    /// An equation, so that a rewrite context can span both sides.
    Eq(Box<Term>, Box<Term>),
}

/// A position in a term: 1 for the left argument, 2 for the right one.
type Path = Vec<u8>;
type Subst = HashMap<(char, String), Term>;

fn op(left: Term, right: Term) -> Term {
    Term::Op(Box::new(left), Box::new(right))
}

fn eq(left: Term, right: Term) -> Term {
    Term::Eq(Box::new(left), Box::new(right))
}

/// Parse `op(a, op(b, c))`; identifiers other than `op` are variables.
pub fn parse_term(text: &str) -> Result<Term, String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if "(),".contains(c) {
            tokens.push(c.to_string());
            i += 1;
        } else if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        } else {
            return Err(format!("cannot tokenize term: {:?}", text));
        }
    }
    let mut pos = 0;
    let term = parse_tokens(&tokens, &mut pos, text)?;
    if pos != tokens.len() {
        return Err(format!("trailing input in term: {:?}", text));
    }
    Ok(term)
}

fn parse_tokens(tokens: &[String], pos: &mut usize, text: &str) -> Result<Term, String> {
    let token = tokens
        .get(*pos)
        .ok_or_else(|| format!("unexpected end of term: {:?}", text))?;
    *pos += 1;
    if token == "op" && tokens.get(*pos).map(String::as_str) == Some("(") {
        *pos += 1;
        let left = parse_tokens(tokens, pos, text)?;
        expect(tokens, pos, ",", text)?;
        let right = parse_tokens(tokens, pos, text)?;
        expect(tokens, pos, ")", text)?;
        return Ok(op(left, right));
    }
    if "(),".contains(token.as_str()) {
        return Err(format!("unexpected {:?} in term: {:?}", token, text));
    }
    if tokens.get(*pos).map(String::as_str) == Some("(") {
        return Err(format!(
            "only problems over one binary operation `op` are supported, not `{}`",
            token
        ));
    }
    Ok(Term::Var(token.to_lowercase()))
}

fn expect(tokens: &[String], pos: &mut usize, token: &str, text: &str) -> Result<(), String> {
    if tokens.get(*pos).map(String::as_str) != Some(token) {
        return Err(format!("expected {:?} in term: {:?}", token, text));
    }
    *pos += 1;
    Ok(())
}

/// Parse `[! [..] :] lhs = rhs[.]` into its two sides.
pub fn parse_equation(text: &str) -> Result<(Term, Term), String> {
    let quantifier = cached_regex(r"(?s)^\s*!\s*\[[^\]]*\]\s*:\s*(.*)");
    let body = match quantifier.captures(text) {
        Some(found) => found.get(1).unwrap().as_str(),
        None => text,
    };
    let mut body = body.trim().trim_end_matches('.').trim();
    while body.len() >= 2
        && body.starts_with('(')
        && body.ends_with(')')
        && balanced(&body[1..body.len() - 1])
    {
        body = body[1..body.len() - 1].trim();
    }
    let mut depth = 0i32;
    for (i, c) in body.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '=' if depth == 0 => {
                return Ok((parse_term(&body[..i])?, parse_term(&body[i + 1..])?));
            }
            _ => {}
        }
    }
    Err(format!("not an equation: {:?}", body))
}

fn balanced(text: &str) -> bool {
    let mut depth = 0i32;
    for c in text.chars() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        if depth < 0 {
            return false;
        }
    }
    depth == 0
}

/// Add the variables of `term` to `seen`, in order of first appearance.
pub fn term_vars(term: &Term, seen: &mut Vec<String>) {
    match term {
        Term::Var(name) => {
            if !seen.contains(name) {
                seen.push(name.clone());
            }
        }
        Term::Op(left, right) => {
            term_vars(left, seen);
            term_vars(right, seen);
        }
        _ => {}
    }
}

/// Rename the variables of `term`; one that `mapping` does not know becomes
/// `default`, or stays as it is if there is no default.
pub fn rename(term: &Term, mapping: &HashMap<String, String>, default: Option<&str>) -> Term {
    match term {
        Term::Var(name) => Term::Var(match (mapping.get(name), default) {
            (Some(new), _) => new.clone(),
            (None, Some(default)) => default.to_string(),
            (None, None) => name.clone(),
        }),
        Term::Op(left, right) => op(
            rename(left, mapping, default),
            rename(right, mapping, default),
        ),
        other => other.clone(),
    }
}

/// The term in Lean syntax.
pub fn show(term: &Term) -> String {
    match term {
        Term::Var(name) | Term::Pattern(_, name) => name.clone(),
        Term::Eq(left, right) => format!("{} = {}", show(left), show(right)),
        Term::Op(left, right) => format!("({} ◇ {})", show(left), show(right)),
    }
}

/// All positions of a term, each before the positions below it.
fn positions(term: &Term, path: &Path, found: &mut Vec<Path>) {
    found.push(path.clone());
    if let Term::Op(left, right) | Term::Eq(left, right) = term {
        for (step, child) in [(1, left), (2, right)] {
            let mut below = path.clone();
            below.push(step);
            positions(child, &below, found);
        }
    }
}

fn subterm<'a>(term: &'a Term, path: &[u8]) -> &'a Term {
    match (path.split_first(), term) {
        (None, _) => term,
        (Some((1, rest)), Term::Op(left, _) | Term::Eq(left, _)) => subterm(left, rest),
        (Some((_, rest)), Term::Op(_, right) | Term::Eq(_, right)) => subterm(right, rest),
        _ => unreachable!("a path leads through operations only"),
    }
}

fn replace(term: &Term, path: &[u8], new: &Term) -> Term {
    let Some((step, rest)) = path.split_first() else {
        return new.clone();
    };
    let rebuilt = |left: &Term, right: &Term| {
        if *step == 1 {
            (replace(left, rest, new), right.clone())
        } else {
            (left.clone(), replace(right, rest, new))
        }
    };
    match term {
        Term::Op(left, right) => {
            let (left, right) = rebuilt(left, right);
            op(left, right)
        }
        Term::Eq(left, right) => {
            let (left, right) = rebuilt(left, right);
            eq(left, right)
        }
        _ => unreachable!("a path leads through operations only"),
    }
}

fn replace_all(term: &Term, paths: &[Path], new: &Term) -> Term {
    paths
        .iter()
        .fold(term.clone(), |term, path| replace(&term, path, new))
}

fn as_pattern(term: &Term, tag: char) -> Term {
    match term {
        Term::Var(name) => Term::Pattern(tag, name.clone()),
        Term::Op(left, right) => op(as_pattern(left, tag), as_pattern(right, tag)),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Unification
// ---------------------------------------------------------------------------

fn walk<'a>(mut term: &'a Term, subst: &'a Subst) -> &'a Term {
    while let Term::Pattern(tag, name) = term {
        match subst.get(&(*tag, name.clone())) {
            Some(bound) => term = bound,
            None => break,
        }
    }
    term
}

fn occurs(variable: &Term, term: &Term, subst: &Subst) -> bool {
    let term = walk(term, subst);
    if term == variable {
        return true;
    }
    match term {
        Term::Op(left, right) | Term::Eq(left, right) => {
            occurs(variable, left, subst) || occurs(variable, right, subst)
        }
        _ => false,
    }
}

fn unify(a: &Term, b: &Term, subst: &mut Subst) -> bool {
    let (a, b) = (walk(a, subst).clone(), walk(b, subst).clone());
    if a == b {
        return true;
    }
    if let Term::Pattern(tag, name) = &a {
        if occurs(&a, &b, subst) {
            return false;
        }
        subst.insert((*tag, name.clone()), b);
        return true;
    }
    if matches!(b, Term::Pattern(..)) {
        return unify(&b, &a, subst);
    }
    match (&a, &b) {
        (Term::Op(a1, a2), Term::Op(b1, b2)) | (Term::Eq(a1, a2), Term::Eq(b1, b2)) => {
            unify(a1, b1, subst) && unify(a2, b2, subst)
        }
        _ => false,
    }
}

/// The term with its pattern variables filled in; one that is still free
/// becomes `default`.
fn resolve(term: &Term, subst: &Subst, default: &str) -> Term {
    match walk(term, subst) {
        Term::Pattern(..) => Term::Var(default.to_string()),
        Term::Var(name) => Term::Var(name.clone()),
        Term::Op(left, right) | Term::Eq(left, right) => op(
            resolve(left, subst, default),
            resolve(right, subst, default),
        ),
    }
}

// ---------------------------------------------------------------------------
// Facts and the search for a single-rewrite justification
// ---------------------------------------------------------------------------

/// A universally quantified equation that is available under a Lean name.
#[derive(Clone, Debug)]
pub struct Fact {
    pub lean_name: String,
    pub vars: Vec<String>,
    pub lhs: Term,
    pub rhs: Term,
}

impl Fact {
    /// The equation with its variables renamed to `x`, `y`, `z`, ...
    pub fn new(lean_name: &str, lhs: &Term, rhs: &Term) -> Fact {
        let mut order = Vec::new();
        term_vars(lhs, &mut order);
        term_vars(rhs, &mut order);
        let mapping: HashMap<String, String> = order
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), fresh_name(i)))
            .collect();
        Fact {
            lean_name: lean_name.to_string(),
            vars: (0..order.len()).map(fresh_name).collect(),
            lhs: rename(lhs, &mapping, None),
            rhs: rename(rhs, &mapping, None),
        }
    }

    fn pattern(&self, tag: char) -> (Term, Term) {
        (as_pattern(&self.lhs, tag), as_pattern(&self.rhs, tag))
    }

    pub fn statement(&self) -> String {
        format!("{} = {}", show(&self.lhs), show(&self.rhs))
    }

    /// The name of the variable to use where a step leaves one free.
    pub fn default_var(&self) -> String {
        self.vars
            .first()
            .cloned()
            .unwrap_or_else(|| "x".to_string())
    }
}

/// A fact is referred to by its index in `Library::facts`.
pub type FactId = usize;

/// A justification: the Lean proof term, how many rewrites it makes (0 for a
/// plain instance, otherwise 1), and a description for the comment.
pub type Justification = (String, usize, String);

/// The facts proved so far, and which of them the proof term under
/// construction cites.
#[derive(Default)]
pub struct Library {
    pub facts: Vec<Fact>,
    pub used: BTreeSet<FactId>,
}

impl Library {
    pub fn add(&mut self, fact: Fact) -> FactId {
        self.facts.push(fact);
        self.facts.len() - 1
    }

    /// Lean term proving an instance of a fact (or its mirror image if `flipped`).
    fn apply(
        &mut self,
        id: FactId,
        tag: char,
        subst: &Subst,
        default: &str,
        flipped: bool,
    ) -> String {
        self.used.insert(id);
        let fact = &self.facts[id];
        let mut words = vec![fact.lean_name.clone()];
        for var in &fact.vars {
            let value = resolve(&Term::Pattern(tag, var.clone()), subst, default);
            words.push(show(&value));
        }
        let term = words.join(" ");
        if flipped {
            format!("({}).symm", term)
        } else if fact.vars.is_empty() {
            term
        } else {
            format!("({})", term)
        }
    }

    /// How `goal` is an instance of a fact, if it is: the substitution and
    /// whether the fact has to be read right to left.
    fn instance(&self, goal: (&Term, &Term), id: FactId) -> Option<(Subst, bool)> {
        let (left, right) = self.facts[id].pattern('A');
        for (first, second, flipped) in [(&left, &right, false), (&right, &left, true)] {
            let mut subst = Subst::new();
            if unify(first, goal.0, &mut subst) && unify(second, goal.1, &mut subst) {
                return Some((subst, flipped));
            }
        }
        None
    }

    /// `goal` is an instance of the fact. A lookup: the fact is not marked as used.
    pub fn covers(&self, goal: (&Term, &Term), id: FactId) -> bool {
        self.instance(goal, id).is_some()
    }

    /// `goal` is an instance of the fact (no rewrite at all).
    pub fn instance_of(
        &mut self,
        goal: (&Term, &Term),
        id: FactId,
        default: &str,
    ) -> Option<String> {
        let (subst, flipped) = self.instance(goal, id)?;
        Some(self.apply(id, 'A', &subst, default, flipped))
    }

    /// `goal` is `s = t` where t is s rewritten once by the fact.
    fn one_rewrite(
        &mut self,
        goal: (&Term, &Term),
        id: FactId,
        default: &str,
    ) -> Option<(String, usize)> {
        let (s, t) = goal;
        let (left, right) = self.facts[id].pattern('B');
        for paths in rewrite_sites(s, t) {
            for (from, to, flipped) in [(&left, &right, false), (&right, &left, true)] {
                let mut subst = Subst::new();
                if unify(from, subterm(s, &paths[0]), &mut subst)
                    && unify(to, subterm(t, &paths[0]), &mut subst)
                {
                    let equation = self.apply(id, 'B', &subst, default, flipped);
                    if paths.len() == 1 && paths[0].is_empty() {
                        return Some((equation, 1));
                    }
                    let proof = format!("(congrArg {} {})", context(s, &paths), equation);
                    return Some((proof, paths.len()));
                }
            }
        }
        None
    }

    /// One rewrite with `side` turns `goal` into an instance of `main`: a
    /// superposition step.
    fn rewrite_then_instance(
        &mut self,
        goal: (&Term, &Term),
        main: FactId,
        side: FactId,
        default: &str,
    ) -> Option<(String, usize)> {
        let equation = eq(goal.0.clone(), goal.1.clone());
        let (main_left, main_right) = self.facts[main].pattern('A');
        let (side_left, side_right) = self.facts[side].pattern('B');

        // the subterms of the goal with their occurrences, in order of first occurrence
        let mut all_positions = Vec::new();
        positions(&equation, &Vec::new(), &mut all_positions);
        let mut occurrences: Vec<(Term, Vec<Path>)> = Vec::new();
        let mut index_of: HashMap<Term, usize> = HashMap::new();
        for path in all_positions.into_iter().filter(|path| !path.is_empty()) {
            let target = subterm(&equation, &path).clone();
            let index = *index_of.entry(target.clone()).or_insert_with(|| {
                occurrences.push((target, Vec::new()));
                occurrences.len() - 1
            });
            occurrences[index].1.push(path);
        }

        for (from, to, side_flipped) in [
            (&side_left, &side_right, true),
            (&side_right, &side_left, false),
        ] {
            // the goal is an instance of `main` with occurrences of `from` replaced by `to`
            for (target, paths) in &occurrences {
                let mut base = Subst::new();
                if !unify(to, target, &mut base) {
                    continue;
                }
                for chosen in occurrence_sets(paths) {
                    let before = replace_all(&equation, &chosen, from);
                    for (first, second, main_flipped) in [
                        (&main_left, &main_right, false),
                        (&main_right, &main_left, true),
                    ] {
                        let mut subst = base.clone();
                        if unify(&eq(first.clone(), second.clone()), &before, &mut subst) {
                            let back = self.apply(side, 'B', &subst, default, side_flipped);
                            let closing = self.apply(main, 'A', &subst, default, main_flipped);
                            let proof = format!(
                                "(Eq.mpr (congrArg {} {}) {})",
                                context(&equation, &chosen),
                                back,
                                closing
                            );
                            return Some((proof, chosen.len()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Justify `goal` from `facts`: as an instance, by one rewrite, or (with
    /// `allow_pairs`) by one rewrite closed by a second equation. With `pool`,
    /// such a pair may combine a fact from `facts` with any fact from `pool`.
    pub fn justify(
        &mut self,
        goal: (&Term, &Term),
        facts: &[FactId],
        default: &str,
        allow_pairs: bool,
        pool: Option<&[FactId]>,
    ) -> Option<Justification> {
        for &id in facts {
            if let Some(proof) = self.instance_of(goal, id, default) {
                return Some((
                    proof,
                    0,
                    format!("instance of {}", self.facts[id].lean_name),
                ));
            }
        }
        for &id in facts {
            if let Some((proof, count)) = self.one_rewrite(goal, id, default) {
                let how = format!("one rewrite with {}{}", self.facts[id].lean_name, at(count));
                return Some((proof, 1, how));
            }
        }
        if !allow_pairs {
            return None;
        }
        let pairs: Vec<(FactId, FactId)> = match pool {
            None => pairs_of(facts, facts),
            Some(pool) => [pairs_of(facts, pool), pairs_of(pool, facts)].concat(),
        };
        for (main, side) in pairs {
            if let Some((proof, count)) = self.rewrite_then_instance(goal, main, side, default) {
                let how = format!(
                    "one rewrite with {}{}, closed by {}",
                    self.facts[side].lean_name,
                    at(count),
                    self.facts[main].lean_name
                );
                return Some((proof, 1, how));
            }
        }
        None
    }
}

fn pairs_of(mains: &[FactId], sides: &[FactId]) -> Vec<(FactId, FactId)> {
    mains
        .iter()
        .flat_map(|&main| sides.iter().map(move |&side| (main, side)))
        .collect()
}

fn at(count: usize) -> String {
    if count == 1 {
        String::new()
    } else {
        format!(" at {} occurrences", count)
    }
}

/// `(fun hole : G => ...)`: the term with a hole at the given positions.
fn context(term: &Term, paths: &[Path]) -> String {
    let hole = Term::Var(HOLE.to_string());
    format!(
        "(fun {} : G => {})",
        HOLE,
        show(&replace_all(term, paths, &hole))
    )
}

/// Outermost positions where s and t differ, with the two parts.
fn difference(s: &Term, t: &Term, path: &Path, found: &mut Vec<(Path, Term, Term)>) {
    if s == t {
        return;
    }
    if let (Term::Op(s1, s2), Term::Op(t1, t2)) = (s, t) {
        for (step, a, b) in [(1, s1, t1), (2, s2, t2)] {
            let mut below = path.clone();
            below.push(step);
            difference(a, b, &below, found);
        }
    } else {
        found.push((path.clone(), s.clone(), t.clone()));
    }
}

/// Candidate hole sets for rewriting s into t with one equation instance.
fn rewrite_sites(s: &Term, t: &Term) -> Vec<Vec<Path>> {
    let mut diff = Vec::new();
    difference(s, t, &Vec::new(), &mut diff);
    let mut sites = Vec::new();
    if diff.is_empty() {
        return sites;
    }
    // the same replacement everywhere: all those positions at once
    if diff
        .iter()
        .all(|(_, a, b)| (a, b) == (&diff[0].1, &diff[0].2))
    {
        sites.push(diff.iter().map(|(path, _, _)| path.clone()).collect());
    }
    // a single hole anywhere above all differences, deepest first
    let mut common = diff[0].0.clone();
    for (path, _, _) in &diff[1..] {
        let shared = common.iter().zip(path).take_while(|(a, b)| a == b).count();
        common.truncate(shared);
    }
    let start = if diff.len() > 1 {
        common.len() as isize
    } else {
        common.len() as isize - 1
    };
    for length in (0..=start).rev() {
        sites.push(vec![common[..length as usize].to_vec()]);
    }
    sites
}

/// Which occurrences of a subterm to rewrite: each alone, all, then the rest.
fn occurrence_sets(paths: &[Path]) -> Vec<Vec<Path>> {
    let mut sets: Vec<Vec<Path>> = paths.iter().map(|path| vec![path.clone()]).collect();
    if paths.len() > 1 {
        sets.push(paths.to_vec());
    }
    if paths.len() > 2 && paths.len() <= 8 {
        for mask in 1..(1usize << paths.len()) - 1 {
            let chosen: Vec<Path> = paths
                .iter()
                .enumerate()
                .filter(|(i, _)| mask >> i & 1 == 1)
                .map(|(_, path)| path.clone())
                .collect();
            if chosen.len() > 1 {
                sets.push(chosen);
            }
        }
    }
    sets
}
