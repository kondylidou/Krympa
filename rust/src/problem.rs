//! Reading the input problem.
//!
//! Krympa works on problems in `fof` form: equations as axioms, one equation
//! as conjecture. Equational problems of the TPTP library are written as unit
//! clauses in `cnf` form instead, with the goal negated:
//!
//! ```text
//! cnf(left_identity, axiom, multiply(identity,X) = X).
//! cnf(prove_this, negated_conjecture, multiply(a,identity) != a).
//! ```
//!
//! Such a problem is rewritten to `fof` form once, before anything else runs.
//! A constant of the negated goal that no axiom mentions stands for an
//! arbitrary element, so it becomes a universally quantified variable.

use crate::regex_cache::cached_regex;
use crate::utils::extract_suffix;
use std::collections::BTreeSet;
use std::fs;

/// The file the phases should read: the input itself if it is in `fof` form,
/// otherwise its translation, written to `../output/input_problem_<name>.p`.
pub fn fof_problem(input_file: &str) -> Result<String, String> {
    let text =
        fs::read_to_string(input_file).map_err(|e| format!("Cannot read {}: {}", input_file, e))?;
    match cnf_to_fof(&text)? {
        None => Ok(input_file.to_string()),
        Some(translated) => {
            // `extract_suffix` drops the prefix `input_problem_`, so the output
            // files are named after the problem either way.
            let file = format!("../output/input_problem_{}.p", extract_suffix(input_file));
            fs::create_dir_all("../output").map_err(|e| e.to_string())?;
            fs::write(&file, translated).map_err(|e| format!("Cannot write {}: {}", file, e))?;
            crate::klog_info!(
                "[INFO] Problem in cnf form, rewritten to fof form: {}",
                file
            );
            Ok(file)
        }
    }
}

/// Rewrite the `cnf` clauses of a problem as `fof` formulas. Returns `None`
/// if the problem has no `cnf` clause, and an error for a clause that is not
/// a single equation or a single negated equation.
pub fn cnf_to_fof(problem: &str) -> Result<Option<String>, String> {
    let statements = statements(problem)?;
    if !statements.iter().any(|s| s.language == "cnf") {
        return Ok(None);
    }
    let is_goal = |s: &Statement| s.role == "negated_conjecture" || s.role == "conjecture";
    let axiom_text: String = statements
        .iter()
        .filter(|s| !is_goal(s))
        .map(|s| format!("{} ", s.formula))
        .collect();
    if statements.iter().filter(|s| is_goal(s)).count() > 1 {
        return Err("The problem has more than one conjecture".into());
    }

    let mut lines = Vec::new();
    for statement in &statements {
        if statement.language != "cnf" {
            lines.push(format!("{}.", statement.text));
            continue;
        }
        let clause = strip_parentheses(&statement.formula);
        if clause.contains('|') {
            return Err(format!(
                "Clause '{}' is not a single equation",
                statement.name
            ));
        }
        let line = if statement.role == "negated_conjecture" {
            let (left, right) = clause.split_once("!=").ok_or_else(|| {
                format!(
                    "Negated conjecture '{}' is not a negated equation",
                    statement.name
                )
            })?;
            let equation = format!("{} = {}", left.trim(), right.trim());
            if !variables(&equation).is_empty() {
                return Err(format!(
                    "Negated conjecture '{}' has variables; only ground goals are supported",
                    statement.name
                ));
            }
            let equation = generalize(&equation, &axiom_text);
            fof(&statement.name, "conjecture", &equation)
        } else {
            if clause.contains("!=") || clause.contains('~') || !clause.contains('=') {
                return Err(format!("Clause '{}' is not an equation", statement.name));
            }
            fof(&statement.name, "axiom", clause)
        };
        lines.push(line);
    }
    Ok(Some(lines.join("\n") + "\n"))
}

/// One annotated formula: `language(name, role, formula).`
struct Statement {
    language: String,
    name: String,
    role: String,
    formula: String,
    /// the statement as written, without the final dot
    text: String,
}

/// Split a problem into its annotated formulas.
fn statements(problem: &str) -> Result<Vec<Statement>, String> {
    let without_comments: String = problem
        .lines()
        .map(|line| line.split('%').next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n");

    let mut result = Vec::new();
    let (mut depth, mut current) = (0usize, String::new());
    for c in without_comments.chars() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth = depth.saturating_sub(1),
            '.' if depth == 0 => {
                result.push(statement(current.trim())?);
                current.clear();
                continue;
            }
            _ => {}
        }
        current.push(c);
    }
    if !current.trim().is_empty() {
        return Err(format!("Unfinished formula: {}", current.trim()));
    }
    Ok(result)
}

fn statement(text: &str) -> Result<Statement, String> {
    let malformed = || format!("Cannot read formula: {}", text);
    let (language, rest) = text.split_once('(').ok_or_else(malformed)?;
    let language = language.trim();
    if language == "include" {
        return Err("`include` is not supported; put the axioms into the problem file".into());
    }
    let inner = rest.strip_suffix(')').ok_or_else(malformed)?;
    // name, role, formula (and possibly annotations): split at top-level commas
    let (mut depth, mut parts, mut start) = (0usize, Vec::new(), 0);
    for (i, c) in inner.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(inner[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(inner[start..].trim());
    if parts.len() < 3 {
        return Err(malformed());
    }
    Ok(Statement {
        language: language.to_string(),
        name: parts[0].to_string(),
        role: parts[1].to_string(),
        formula: parts[2].to_string(),
        text: text.to_string(),
    })
}

/// `( ( s = t ) )` -> `s = t`: drop parentheses that enclose the whole clause.
fn strip_parentheses(clause: &str) -> &str {
    let mut clause = clause.trim();
    while clause.starts_with('(') && closing_parenthesis(clause) == Some(clause.len() - 1) {
        clause = clause[1..clause.len() - 1].trim();
    }
    clause
}

/// Position of the parenthesis that closes the one at the start of `text`.
fn closing_parenthesis(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The variables of a formula, in order of first occurrence.
fn variables(formula: &str) -> Vec<String> {
    let mut seen = Vec::new();
    for found in cached_regex(r"\b[A-Z][A-Za-z0-9_]*\b").find_iter(formula) {
        if !seen.iter().any(|v| v == found.as_str()) {
            seen.push(found.as_str().to_string());
        }
    }
    seen
}

/// Replace the constants of `equation` that `axioms` do not mention by
/// variables `X0`, `X1`, ...
fn generalize(equation: &str, axioms: &str) -> String {
    let identifier = cached_regex(r"\b[a-z][A-Za-z0-9_]*\b");
    let known: BTreeSet<&str> = identifier.find_iter(axioms).map(|m| m.as_str()).collect();
    let mut fresh: Vec<String> = Vec::new();
    let (mut result, mut copied) = (String::new(), 0);
    for found in identifier.find_iter(equation) {
        let is_function = equation[found.end()..].trim_start().starts_with('(');
        if is_function || known.contains(found.as_str()) {
            continue;
        }
        let index = match fresh.iter().position(|c| c == found.as_str()) {
            Some(index) => index,
            None => {
                fresh.push(found.as_str().to_string());
                fresh.len() - 1
            }
        };
        result.push_str(&equation[copied..found.start()]);
        result.push_str(&format!("X{}", index));
        copied = found.end();
    }
    result.push_str(&equation[copied..]);
    result
}

/// `fof(name, role, ! [X, Y] : equation).`, without quantifier if there is no variable.
fn fof(name: &str, role: &str, equation: &str) -> String {
    let variables = variables(equation);
    if variables.is_empty() {
        format!("fof({}, {}, {}).", name, role, equation)
    } else {
        format!(
            "fof({}, {}, ! [{}] : {}).",
            name,
            role,
            variables.join(", "),
            equation
        )
    }
}
