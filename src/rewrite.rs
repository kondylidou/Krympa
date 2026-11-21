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

/// The term with its variables as pattern variables, except `keep`, which
/// stay constants (the witnesses of an existential fact).
fn as_pattern(term: &Term, tag: char, keep: &[String]) -> Term {
    match term {
        Term::Var(name) if !keep.contains(name) => Term::Pattern(tag, name.clone()),
        Term::Op(left, right) => op(as_pattern(left, tag, keep), as_pattern(right, tag, keep)),
        other => other.clone(),
    }
}

/// The variables `names` of `term` as pattern variables to be solved for:
/// the witnesses of an existential statement that is being proved.
pub fn open_witnesses(term: &Term, names: &[String]) -> Term {
    match term {
        Term::Var(name) if names.contains(name) => Term::Pattern('E', name.clone()),
        Term::Op(left, right) => op(open_witnesses(left, names), open_witnesses(right, names)),
        other => other.clone(),
    }
}

/// The term with the variables of `values` replaced.
pub fn substitute(term: &Term, values: &HashMap<String, Term>) -> Term {
    match term {
        Term::Var(name) => values.get(name).cloned().unwrap_or_else(|| term.clone()),
        Term::Op(left, right) => op(substitute(left, values), substitute(right, values)),
        other => other.clone(),
    }
}

/// Parse `! [..] : (? [Y, ..] : lhs = rhs)`: the existential variables (as
/// `parse_term` names them) and the two sides.
pub fn parse_existential(text: &str) -> Result<(Vec<String>, Term, Term), String> {
    let quantifier = cached_regex(r"(?s)^\s*!\s*\[[^\]]*\]\s*:\s*(.*)$");
    let mut body = match quantifier.captures(text) {
        Some(found) => found.get(1).unwrap().as_str(),
        None => text,
    }
    .trim();
    while body.len() >= 2
        && body.starts_with('(')
        && body.ends_with(')')
        && balanced(&body[1..body.len() - 1])
    {
        body = body[1..body.len() - 1].trim();
    }
    let found = cached_regex(r"(?s)^\?\s*\[([^\]]*)\]\s*:\s*(.*)$")
        .captures(body)
        .ok_or_else(|| format!("not an existential statement: {:?}", text))?;
    let names = found[1]
        .split(',')
        .map(|name| name.trim().to_lowercase())
        .filter(|name| !name.is_empty())
        .collect();
    let (lhs, rhs) = parse_equation(&found[2])?;
    Ok((names, lhs, rhs))
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
    /// the universally quantified variables
    pub vars: Vec<String>,
    /// for `∀ vars, ∃ witnesses, lhs = rhs`: the existential variables
    pub witnesses: Vec<String>,
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
            witnesses: Vec::new(),
            lhs: rename(lhs, &mapping, None),
            rhs: rename(rhs, &mapping, None),
        }
    }

    /// `∀ .., ∃ existential, lhs = rhs`: the universal variables renamed to
    /// `x`, `y`, ..., the existential ones to names unique to this fact.
    pub fn existential(lean_name: &str, lhs: &Term, rhs: &Term, existential: &[String]) -> Fact {
        let mut order = Vec::new();
        term_vars(lhs, &mut order);
        term_vars(rhs, &mut order);
        let universal: Vec<&String> = order.iter().filter(|v| !existential.contains(v)).collect();
        let witnesses: Vec<String> = (1..=existential.len())
            .map(|k| format!("{}_w{}", lean_name, k))
            .collect();
        let mut mapping: HashMap<String, String> = universal
            .iter()
            .enumerate()
            .map(|(i, name)| ((*name).clone(), fresh_name(i)))
            .collect();
        mapping.extend(existential.iter().cloned().zip(witnesses.iter().cloned()));
        Fact {
            lean_name: lean_name.to_string(),
            vars: (0..universal.len()).map(fresh_name).collect(),
            witnesses,
            lhs: rename(lhs, &mapping, None),
            rhs: rename(rhs, &mapping, None),
        }
    }

    fn pattern(&self, tag: char) -> (Term, Term) {
        (
            as_pattern(&self.lhs, tag, &self.witnesses),
            as_pattern(&self.rhs, tag, &self.witnesses),
        )
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
    /// existential facts the proof term uses, with the arguments of the one
    /// instance it uses; the term refers to that instance as `h_<name>`
    pub opened: Vec<(FactId, Vec<String>)>,
    /// set if an existential fact is used with two different instances
    pub conflict: bool,
    /// the substitution of the last justification
    last_subst: Subst,
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
        self.last_subst = subst.clone();
        let fact = &self.facts[id];
        let mut words = vec![fact.lean_name.clone()];
        for var in &fact.vars {
            let value = resolve(&Term::Pattern(tag, var.clone()), subst, default);
            words.push(show(&value));
        }
        if !fact.witnesses.is_empty() {
            let args = words[1..].to_vec();
            let name = format!("h_{}", fact.lean_name);
            match self.opened.iter().find(|(opened, _)| *opened == id) {
                Some((_, earlier)) if *earlier != args => self.conflict = true,
                Some(_) => {}
                None => self.opened.push((id, args)),
            }
            return if flipped {
                format!("({}).symm", name)
            } else {
                name
            };
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

    /// The value the last justification gives the witness `name` of the
    /// existential statement it proved.
    pub fn witness_value(&self, name: &str, default: &str) -> Term {
        resolve(
            &Term::Pattern('E', name.to_string()),
            &self.last_subst,
            default,
        )
    }

    /// What a candidate justification may have to undo.
    fn snapshot(&self) -> (BTreeSet<FactId>, Vec<(FactId, Vec<String>)>) {
        (self.used.clone(), self.opened.clone())
    }

    /// Keep a candidate if the existential facts it uses can be opened: each
    /// with one instance, whose arguments do not mention a witness (the
    /// witness only exists after opening). Otherwise undo it.
    fn keep(&mut self, snapshot: (BTreeSet<FactId>, Vec<(FactId, Vec<String>)>)) -> bool {
        let witnesses: Vec<&String> = self
            .opened
            .iter()
            .flat_map(|(id, _)| &self.facts[*id].witnesses)
            .collect();
        let mentions_witness = |arg: &String| {
            arg.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .any(|word| witnesses.iter().any(|w| w.as_str() == word))
        };
        let valid = !self.conflict
            && !self
                .opened
                .iter()
                .any(|(_, args)| args.iter().any(mentions_witness));
        if !valid {
            (self.used, self.opened) = snapshot;
            self.conflict = false;
        }
        valid
    }

    /// Forget what the last attempt used.
    pub fn reset(&mut self) {
        self.used.clear();
        self.opened.clear();
        self.conflict = false;
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

    /// Like `rewrite_then_instance`, but the rewritten positions are found by
    /// matching the goal against `main` directly, instead of trying sets of
    /// occurrences. Needed when the rewritten subterm occurs many times and
    /// only some of its occurrences are rewritten.
    fn rewrite_then_instance_anywhere(
        &mut self,
        goal: (&Term, &Term),
        main: FactId,
        side: FactId,
        default: &str,
    ) -> Option<(String, usize)> {
        let equation = eq(goal.0.clone(), goal.1.clone());
        let (main_left, main_right) = self.facts[main].pattern('A');
        let (side_left, side_right) = self.facts[side].pattern('B');
        for (from, to, side_flipped) in [
            (&side_left, &side_right, true),
            (&side_right, &side_left, false),
        ] {
            for (first, second, main_flipped) in [
                (&main_left, &main_right, false),
                (&main_right, &main_left, true),
            ] {
                let main_pattern = eq(first.clone(), second.clone());
                let mut subst = Subst::new();
                let mut paths = Vec::new();
                let rewrite = (from, to);
                if match_rewritten(
                    &main_pattern,
                    &equation,
                    rewrite,
                    &mut subst,
                    &[],
                    &mut paths,
                ) && !paths.is_empty()
                {
                    let back = self.apply(side, 'B', &subst, default, side_flipped);
                    let closing = self.apply(main, 'A', &subst, default, main_flipped);
                    let proof = format!(
                        "(Eq.mpr (congrArg {} {}) {})",
                        context(&equation, &paths),
                        back,
                        closing
                    );
                    return Some((proof, paths.len()));
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
            let before = self.snapshot();
            if let Some(proof) = self.instance_of(goal, id, default) {
                if self.keep(before) {
                    return Some((
                        proof,
                        0,
                        format!("instance of {}", self.facts[id].lean_name),
                    ));
                }
            }
        }
        for &id in facts {
            let before = self.snapshot();
            if let Some((proof, count)) = self.one_rewrite(goal, id, default) {
                if self.keep(before) {
                    let how = format!("one rewrite with {}{}", self.facts[id].lean_name, at(count));
                    return Some((proof, 1, how));
                }
            }
        }
        if !allow_pairs {
            return None;
        }
        let pairs: Vec<(FactId, FactId)> = match pool {
            None => pairs_of(facts, facts),
            Some(pool) => [pairs_of(facts, pool), pairs_of(pool, facts)].concat(),
        };
        for &(main, side) in &pairs {
            let before = self.snapshot();
            let found = self.rewrite_then_instance(goal, main, side, default);
            if let Some((proof, count)) = found.filter(|_| self.keep(before)) {
                let how = format!(
                    "one rewrite with {}{}, closed by {}",
                    self.facts[side].lean_name,
                    at(count),
                    self.facts[main].lean_name
                );
                return Some((proof, 1, how));
            }
        }
        for &(main, side) in &pairs {
            let before = self.snapshot();
            let found = self.rewrite_then_instance_anywhere(goal, main, side, default);
            if let Some((proof, count)) = found.filter(|_| self.keep(before)) {
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

/// Match `pattern` (an instance of `main`) against `term`, where `term` may
/// differ from it at some positions by one rewrite `from` -> `to`: there
/// `term` has an instance of `to` and the pattern an instance of `from`, the
/// same instance everywhere. The positions are collected in `paths`.
fn match_rewritten(
    pattern: &Term,
    term: &Term,
    rewrite: (&Term, &Term),
    subst: &mut Subst,
    path: &[u8],
    paths: &mut Vec<Path>,
) -> bool {
    let (from, to) = rewrite;
    // the same here
    let mut plain = subst.clone();
    if unify(pattern, term, &mut plain) {
        *subst = plain;
        return true;
    }
    // rewritten here (not the equation as a whole)
    if !path.is_empty() {
        let mut here = subst.clone();
        if unify(to, term, &mut here) && unify(pattern, from, &mut here) {
            *subst = here;
            paths.push(path.to_vec());
            return true;
        }
    }
    // the same operation, with rewrites below
    let pattern = walk(pattern, subst).clone();
    match (&pattern, term) {
        (Term::Op(p1, p2), Term::Op(t1, t2)) | (Term::Eq(p1, p2), Term::Eq(t1, t2)) => {
            let mut trial = subst.clone();
            let mut found = Vec::new();
            let left = [path, &[1]].concat();
            let right = [path, &[2]].concat();
            if match_rewritten(p1, t1, rewrite, &mut trial, &left, &mut found)
                && match_rewritten(p2, t2, rewrite, &mut trial, &right, &mut found)
            {
                *subst = trial;
                paths.extend(found);
                return true;
            }
            false
        }
        _ => false,
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
