use itertools::Itertools;
use regex::Regex;
use std::collections::BTreeMap;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

/// Normalize formula with alpha-renaming of quantified variables
/// Quantified variables are renamed in order: V0, V1, ...
/// Unquantified X-style variables are normalized separately.
pub fn normalize_formula_alpha(formula: &str) -> String {
    // regex to extract leading quantifier: ! [X,Y,...] : body
    let quant_re = Regex::new(r"!\s*\[([^\]]*)\]\s*:\s*(.*)").unwrap();

    let mut normalized_body = if let Some(cap) = quant_re.captures(formula) {
        // extract quantified variables
        let vars: Vec<&str> = cap[1].split(',').map(|v| v.trim()).collect();
        let mut body = cap[2].trim().to_string();

        // replace each quantified variable consistently
        for (i, var) in vars.iter().enumerate() {
            let canon_var = format!("V{}", i);
            let var_re = Regex::new(&format!(r"\b{}\b", regex::escape(var))).unwrap();
            body = var_re.replace_all(&body, canon_var.as_str()).to_string();
        }

        body
    } else {
        formula.to_string()
    };

    // normalize any remaining X-style variables (unquantified)
    let var_re = Regex::new(r"\bX\d+\b").unwrap();
    let mut var_map: BTreeMap<String, String> = BTreeMap::new();
    let mut counter = 0;

    normalized_body = var_re
        .replace_all(&normalized_body, |caps: &regex::Captures| {
            let v = &caps[0];
            if !var_map.contains_key(v) {
                var_map.insert(v.to_string(), format!("V{}", counter));
                counter += 1;
            }
            var_map[v].clone()
        })
        .to_string();

    // remove all whitespace for canonical comparison
    normalized_body
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect()
}

/// Parse a formula like "(op(V0,op(V1,V0))=X3)" into Term::Fun("=", [...]).
fn parse_formula(s: &str) -> Term {
    parse_term(s.trim())
}

fn parse_term(s: &str) -> Term {
    let s = s.trim();

    // Variable (no parentheses)
    if !s.starts_with('(') {
        return Term::Var(s.to_string());
    }

    // Function application: (name,arg1,arg2,...)
    let inside = &s[1..s.len() - 1];
    let mut parts = split_top_level(inside);

    let fun_name = parts.remove(0).to_string();
    let args = parts.into_iter().map(|p| parse_term(&p)).collect();
    Term::Fun(fun_name, args)
}

/// Split arguments at top-level commas: op(V0,op(X1,V0)) -> ["op", "V0", "op(X1,V0)"]
fn split_top_level(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut depth = 0;
    let mut start = 0;

    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                result.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }

    result.push(s[start..].trim().to_string());
    result
}

pub fn formulas_match(formula: &str, other_formula: &str) -> bool {
    formulas_match_with_permutations(formula, other_formula)
}

/// Pattern match formula onto other_formula with variable map
fn match_terms(formula: &Term, other_formula: &Term, map: &mut HashMap<String, Term>) -> bool {
    match formula {
        Term::Var(v) => {
            if let Some(existing) = map.get(v) {
                existing == other_formula
            } else {
                map.insert(v.clone(), other_formula.clone());
                true
            }
        }

        Term::Fun(f1, a1) => {
            if let Term::Fun(f2, a2) = other_formula {
                if f1 != f2 || a1.len() != a2.len() {
                    return false;
                }
                for (sub1, sub2) in a1.iter().zip(a2.iter()) {
                    if !match_terms(sub1, sub2, map) {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
    }
}

/// Checks whether two formulas match modulo variable renaming (alpha-equivalence),
/// including quantified variables at the top level.
pub fn formulas_match_with_permutations(formula: &str, other_formula: &str) -> bool {
    let quant_re = Regex::new(r"!\s*\[([^\]]*)\]\s*:\s*(.*)").unwrap();

    let (vars, body) = if let Some(cap) = quant_re.captures(formula) {
        let vars: Vec<String> = cap[1].split(',').map(|v| v.trim().to_string()).collect();
        (vars, cap[2].trim().to_string())
    } else {
        (Vec::new(), formula.to_string())
    };

    // normalize other_formula once
    let other_norm = normalize_formula_alpha(other_formula);
    let parsed_other = parse_formula(&other_norm);

    if vars.len() <= 3 {
        // try all permutations for small number of quantified variables
        for perm in vars.iter().permutations(vars.len()).unique() {
            let mut body_perm = body.clone();
            for (i, var) in perm.iter().enumerate() {
                let canon_var = format!("V{}", i);
                let var_re = Regex::new(&format!(r"\b{}\b", regex::escape(var))).unwrap();
                body_perm = var_re
                    .replace_all(&body_perm, canon_var.as_str())
                    .to_string();
            }

            let norm_body = normalize_formula_alpha(&body_perm);
            let parsed_formula = parse_formula(&norm_body);

            let mut map: HashMap<String, Term> = HashMap::new();
            if match_terms(&parsed_formula, &parsed_other, &mut map) {
                return true;
            }
        }
        false
    } else {
        // for larger formulas, just normalize in order without permutations
        let norm_body = normalize_formula_alpha(&body);
        let parsed_formula = parse_formula(&norm_body);

        let mut map: HashMap<String, Term> = HashMap::new();
        match_terms(&parsed_formula, &parsed_other, &mut map)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match() {
        let twee = "(op(V0,op(op(V1,V0),V2))=V3)";
        let vamp = "(op(X5,op(op(X6,X5),X7))=X8)";
        assert!(formulas_match(twee, vamp));
    }

    #[test]
    fn test_non_match() {
        let twee = "(op(V0,V1)=V2)";
        let vamp = "(op(X0,op(X1,X0))=X1)";
        assert!(!formulas_match(twee, vamp));
    }

    #[test]
    fn test_match_same() {
        let twee = "(op(X0,X1)=X2)";
        let vamp = "(op(X8,X3)=X4)";
        assert!(formulas_match(twee, vamp));
    }

    #[test]
    fn test_non_match_same() {
        let twee = "(op(X0,op(X1,X0))=X1)";
        let vamp = "(op(X0,X0)=X1)";
        assert!(!formulas_match(twee, vamp));
    }

    #[test]
    fn test_non_match_same_args() {
        let twee = "(op(X0,X1)=X1)";
        let vamp = "(op(X0,X0)=X1)";
        assert!(!formulas_match(twee, vamp));
    }

    #[test]
    fn test_var() {
        let twee = "(op(X0,X1)=X1)";
        let vamp = "(op(X0,X1)=op(X0,X1))";
        assert!(!formulas_match(twee, vamp));
    }

    #[test]
    fn test_non_match_twee_vamp() {
        let twee = "(op(V3,op(op(V1,op(op(V2,V1),V1)),V3))=op(op(V3,op(op(V1,op(op(V2,V1),V1)),V3)),op(V0,op(op(V1,op(op(V2,V1),V1)),V0))))";
        let vamp = "(op(V0,op(op(V1,op(op(V2,V3),V1)),V0))=op(op(V0,op(op(V1,op(op(V2,V3),V1)),V0)),op(V4,op(op(V5,op(V3,V5)),V4))))";
        assert!(!formulas_match(twee, vamp));
    }

    #[test]
    fn test_match_orig() {
        let twee = "! [X, Y] : (op(Y, X) = Y)";
        let vamp = "! [X0, X1] :
          (op(X1,X0) = X1)";
        assert!(formulas_match(twee, vamp));
    }

    #[test]
    fn test_match_orig_rev() {
        let twee = "! [X, Y] : (op(X, Y) = X)";
        let vamp = "! [X0, X1] :
          (op(X1,X0) = X1)";
        assert!(formulas_match(twee, vamp));
    }

    #[test]
    fn test_norm1() {
        let form = "! [X, Y] : (op(X, Y) = X)";
        let norm_form = "(op(V0,V1)=V0)";
        assert!(normalize_formula_alpha(form) == norm_form);
    }

    #[test]
    fn test_norm2() {
        let form = "(op(X1,X0) = X1)";
        let norm_form = "(op(V0,V1)=V0)";
        assert!(normalize_formula_alpha(form) == norm_form);
    }

    #[test]
    fn test_norm3() {
        let form = "! [X0, X1] :
          (op(X1,X0) = X1)";
        let norm_form = "(op(V1,V0)=V1)";
        assert!(normalize_formula_alpha(form) == norm_form);
    }

    #[test]
    fn test_twee_formulas() {
        let twee1 = "! [X, Y, Z] : (op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X)";
        let twee2 = "! [X, Y] : (op(X, Y) = X)";
        assert!(!formulas_match(twee1, twee2));
    }

    // TODO should they match?
    // only if X = Y?
    #[test]
    fn test_one() {
        let twee1 = "(op(X, op(op(Y, op(op(Z, X), Y)), X)) = X)";
        let twee2 = "(op(X, op(op(Y, op(op(Z, Y), Y)), X)) = X)";
        assert!(formulas_match(twee1, twee2));
    }

    #[test]
    fn test_vampire_formulas() {
        let formula1 = "! [X0, X1, X2, X3] : (op(X3,op(op(X1,op(op(X2,X1),X1)),X3)) = op(op(X3,op(op(X1,op(op(X2,X1),X1)),X3)),op(X0,op(op(X1,op(op(X2,X1),X1)),X0))))";
        let formula2 = "(op(X48,op(op(X45,op(op(X46,X45),X45)),X48)) = op(op(X48,op(op(X45,op(op(X46,X45),X45)),X48)),op(X44,op(op(X45,op(op(X46,X45),X45)),X44))))";
        println!("[DEBUG] formula 1 {}", normalize_formula_alpha(formula1));
        println!("[DEBUG] formula 2 {}", normalize_formula_alpha(formula2));
        let mut map: HashMap<String, Term> = HashMap::new();

        assert!(formulas_match(formula1, formula2));
    }
}
