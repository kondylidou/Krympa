import re
import sys
import os

# Recursive parser for op(...) terms into Lean infix ◇
def parse_term(s, i=0):
    n = len(s)
    while i < n and s[i].isspace():
        i += 1
    if i >= n:
        raise ValueError("Unexpected end while parsing term")

    if s.startswith("op(", i):
        i += 3
        left, i = parse_term(s, i)
        while i < n and s[i].isspace():
            i += 1
        if i >= n or s[i] != ',':
            raise ValueError(f"Expected ',' in op(...) at pos {i} in: {s}")
        i += 1
        right, i = parse_term(s, i)
        while i < n and s[i].isspace():
            i += 1
        if i >= n or s[i] != ')':
            raise ValueError(f"Expected ')' in op(...) at pos {i} in: {s}")
        i += 1
        return f"({left} ◇ {right})", i

    m = re.match(r'[A-Za-z]\w*', s[i:])
    if not m:
        raise ValueError(f"Expected variable at pos {i} in: {s}")
    ident = m.group(0)
    return ident, i + len(ident)

def parse_side(side_text):
    side_text = side_text.strip().rstrip('.')
    term, pos = parse_term(side_text, 0)
    while pos < len(side_text) and side_text[pos].isspace():
        pos += 1
    if pos != len(side_text):
        raise ValueError(f"Extra characters after parsed term: '{side_text[pos:]}'")
    return term

def parse_equation_tptp(eq):
    eq = eq.strip()
    if eq.startswith("(") and eq.endswith(")"):
        eq = eq[1:-1].strip()
    depth = 0
    pos_eq = None
    for i, c in enumerate(eq):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == '=' and depth == 0:
            pos_eq = i
            break
    if pos_eq is None:
        lhs = parse_side(eq)
        return lhs, None
    lhs_text = eq[:pos_eq].strip()
    rhs_text = eq[pos_eq + 1:].strip()
    lhs = parse_side(lhs_text)
    rhs = parse_side(rhs_text)
    return lhs, rhs

# Strip TPTP universal quantifiers ! [X,Y,...] :
def strip_forall(expr):
    m = re.match(r"!\s*\[.*?\]\s*:\s*(.*)", expr)
    if m:
        return m.group(1).strip()
    return expr.strip()

# Extract variables
def extract_variables(s):
    vars = sorted(set(re.findall(r"[A-Za-z]\w*", s)))
    if 'op' in vars:
        vars.remove('op')
    return vars

# Parse dependencies from proof lines
def parse_dependencies_from_proof(proof_lines):
    deps = set()
    for line in proof_lines:
        matches = re.findall(r'\((single_lemma_\d+|history_lemma_\d+|a1)\)', line)
        for m in matches:
            deps.add("op_law" if m == "a1" else m)

        matches2 = re.findall(r'by lemma (\d+)', line, flags=re.IGNORECASE)
        for m in matches2:
            deps.add(f"Lemma_{m}")
    return sorted(deps)

def normalize_variables(expr):
    """
    Renames variables in expr to x0, x1, x2, ... in sorted order.
    Variable matching is case-insensitive: X and x map to the same variable.
    Returns (new_expr, new_vars)
    """

    # Extract variables, normalize case
    raw_vars = re.findall(r"[A-Za-z]\w*", expr)

    # Remove 'op' and normalize to lowercase
    canon_vars = sorted({v.lower() for v in raw_vars if v.lower() != "op"})

    # Canonical renaming
    renaming = {v: f"x{i}" for i, v in enumerate(canon_vars)}

    def repl(match):
        v = match.group(0)
        return renaming.get(v.lower(), v)

    new_expr = re.sub(r"[A-Za-z]\w*", repl, expr)
    new_vars = [renaming[v] for v in canon_vars]

    return new_expr, new_vars

# Lean abbreviation
def lean_abbrev(name, expr):
    expr_core = strip_forall(expr)
    expr_norm, vars = normalize_variables(expr_core)
    varstr = " ".join(vars)
    lhs, rhs = parse_equation_tptp(expr_norm)
    if rhs is None:
        body = lhs
    else:
        body = f"{lhs} = {rhs}"
    return f"""abbrev Equation_{name} (G : Type _) [Magma G] :=
  ∀ {varstr} : G, {body}
"""

def lean_axiom(name, expr):
    expr_norm, vars = normalize_variables(expr)
    lhs, rhs = parse_equation_tptp(expr_norm)

    if rhs is None:
        body = lhs
    else:
        combined = f"{lhs} = {rhs}"
        if len(combined) > 80:
            # Put the '=' on its own line and rhs indented
            body = f"{lhs} =\n      {rhs}"
        else:
            body = combined

    return f"""axiom {name} (G : Type _) [Magma G] :
  ∀ {' '.join(vars)} : G, {body}
"""

def build_variable_renaming_from_expr(expr):
    """
    Build a variable renaming map from the lemma expression only.
    Case-insensitive: X and x are the same variable.
    """
    vars = sorted(
        set(v.lower() for v in extract_variables(expr))
        - {"op"}
    )
    return {v: f"x{i}" for i, v in enumerate(vars)}

def apply_renaming(expr, renaming):
    def repl(match):
        v = match.group(0)
        return renaming.get(v.lower(), v)
    return re.sub(r"[A-Za-z]\w*", repl, expr)

def format_calc_step(lhs, rhs, dep, indent="        ", max_len=80):
    expr_len = len(lhs) + len(rhs)

    if expr_len <= max_len:
        return (
            f"{lhs} = {rhs} := by\n"
            f"{indent}duper [{dep}]"
        )
    else:
        return (
            f"{lhs} =\n"
            f"{indent}{rhs} := by\n"
            f"{indent}duper [{dep}]"
        )
    
def format_lemma_body(lhs, rhs, indent="  ", max_len=80):
    """
    Format the body of a lemma:
      lhs = rhs
    If the total length exceeds max_len, break at the '='.
    """
    if rhs is None:
        # Just lhs
        return lhs
    full = f"{lhs} = {rhs}"
    if len(full) <= max_len:
        return full
    else:
        # break at '='
        return f"{lhs} =\n{indent}{rhs}"

def format_side(expr, indent="      ", max_len=80):
    """
    Format one side of an equation (LHS or RHS) for Lean.
    - Only break lines at the ◇ operator if the line exceeds max_len.
    - Each new line is indented.
    """
    expr = expr.strip()
    if len(expr) <= max_len:
        return expr

    parts = expr.split("◇")
    lines = []
    current = parts[0].strip()

    for part in parts[1:]:
        part = part.strip()
        # Add ◇ to the previous part
        candidate = f"{current} ◇ {part}"
        if len(candidate) > max_len:
            # Break line here
            lines.append(current)
            current = part
        else:
            current = candidate

    lines.append(current)
    # Join with newline + indent
    return ("\n" + indent).join(lines)

def build_calc_block(proof_lines, renaming):
    """
    Builds Lean calc block from TPTP proof lines.
    Each step may have:
      lhs
      = { by <dep> }
      rhs

    Converts to:
      lhs = rhs := by duper [dep]
    """
    lines = []

    for i in range(len(proof_lines)):
        line = proof_lines[i].strip()
        if not line or line.lower() == "proof:":
            continue

        
        # Look for a dependency line like "= { by ... }"
        m = re.match(r"=\s*\{\s*by\s+(\S+).*?\}", line)
        if m:
            # Determine dependency (only the first reference)
            refs = re.findall(r"(single_lemma_\d+|history_lemma_\d+|a1)", line)
            dep = None
            if refs:
                r = refs[0]
                if r == "a1":
                    dep = "op_law"
                elif r in name_mapping:
                    dep = name_mapping[r]
                else:
                    dep = r
            else:
                # Next, try "lemma N" pattern
                m2 = re.search(r"lemma\s+(\d+)", line, flags=re.IGNORECASE)
                if m2:
                    dep_num = m2.group(1)
                    # Original TPTP name may be "lemma_3", map via name_mapping
                    original_name = f"Lemma_{dep_num}"  # depends on how TPTP numbered lemmas
                    dep = name_mapping.get(original_name, f"lemma_{dep_num}")
                else:
                    # fallback: just take first word and translate if possible
                    dep = name_mapping.get(line.split()[0], line.split()[0])

            lhs_raw = apply_renaming(proof_lines[i - 1], renaming)
            rhs_raw = apply_renaming(proof_lines[i + 1], renaming)

            lhs, _ = parse_term(lhs_raw)
            rhs, _ = parse_term(rhs_raw)

            lines.append(format_calc_step(lhs, rhs, dep))
            # lines.append(f"{lhs} = {rhs} := by\n        duper [{dep}]")
            #lines.append(f"_ = {rhs_norm} := by\n        duper [{dep}]")

    return "\n      ".join(lines)
    

# Lean lemma with dependencies (works for lemmas and conjecture)
def lean_lemma(name, expr, deps_from_proof=[], proof_lines=None):
    expr_core = strip_forall(expr)
    renaming = build_variable_renaming_from_expr(expr_core)
    expr_norm = apply_renaming(expr_core, renaming)
    lhs, rhs = parse_equation_tptp(expr_norm)
    vars = [renaming[v] for v in sorted(renaming)]
    var_list = " ".join(vars)

    #body = lhs if rhs is None else f"{lhs} = {rhs}"
    body = format_lemma_body(lhs, rhs, indent="      ", max_len=80)

    if name.startswith("lemma_") and proof_lines:
        calc_block = build_calc_block(proof_lines, renaming)
        return f"""     
  have {name} ({var_list} : G) :
  {body} := by
    calc
      {calc_block}
  """

    if name.startswith("conjecture") and proof_lines:
        calc_block = build_calc_block(proof_lines, renaming)
        intros = " ".join(vars)
        return f"""
  show _ by
    intros {intros}
    calc
      {calc_block}
  """

    else:
        deps_str = f"[{', '.join(deps_from_proof)}]" if deps_from_proof else "[*]"
        return f"""
  have {name} ({var_list} : G) :
  {body} := by
    duper {deps_str}
  """

# Main program
if len(sys.argv) != 2:
    print("Usage: python tolean.py input_file")
    sys.exit(1)

input_file = sys.argv[1]
basename = os.path.splitext(os.path.basename(input_file))[0]
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
output_dir = os.path.join(project_root, "lean", "Proof")
os.makedirs(output_dir, exist_ok=True)
output_file = os.path.join(output_dir, f"{basename}.lean")

axiom = None
conjecture = None
lemmas = {}
inline_axioms = {}        # name -> expr
used_inline_axioms = set()
axiom_name_map = {}       # original -> axiomN
buffer = ""
proof_section = False
current_proof_lines = []
current_lemmaname = None
proofs_by_lemma = {}  # lemma_name -> list of proof lines

with open(input_file) as f:
    for line in f:
        stripped = line.strip()

        # Inline axioms like: Axiom 2 (a1): op(X, ...)
        m = re.match(r"Axiom\s+\d+\s+\(([^)]+)\):\s*(.*)", stripped)
        if m:
            ax_name = m.group(1)
            ax_expr = m.group(2).rstrip(".")
            inline_axioms[ax_name] = ax_expr
            continue

        # Start proof section
        if stripped.startswith("The conjecture is true! Here is a proof"):
            proof_section = True
            continue

        # Lemmas
        if stripped.startswith("% single_lemma_") or stripped.startswith("% history_lemma_"):
            parts = stripped.split("|")
            body = parts[0]
            deps_part = parts[1] if len(parts) > 1 else ""
            m = re.match(r"%\s*(\S+):\s*(.*)", body)
            if m:
                name, expr = m.group(1), m.group(2)
                deps = []
                if "deps:" in deps_part:
                    for d in deps_part.split("deps:")[1].split(","):
                        d = d.split("->")[0].strip()
                        deps.append("op_law" if d == "a1" else d)
                lemmas[name] = (expr, deps)
            continue

        # Parse proof goals if in proof section
        if proof_section:
            m = re.match(r'(?:Goal|Lemma)\s+(\d+)(?:\s*\(([^)]+)\))?\s*:\s*(.*)', stripped)
            if m:
                # If there is a current lemma being accumulated, finalize it
                if current_proof_lines and current_lemmaname:
                    proofs_by_lemma[current_lemmaname] = current_proof_lines.copy()
                    deps = parse_dependencies_from_proof(current_proof_lines)
                    expr, _ = lemmas[current_lemmaname]
                    lemmas[current_lemmaname] = (expr, deps)
                    current_proof_lines = []

                # Start new lemma
                number = m.group(1)
                current_lemmaname = m.group(2) if m.group(2) else f"Lemma_{number}"
                lemmaexpr = m.group(3).strip()
                current_proof_lines = []

                # Initialize lemma if not 'a1' (hypothesis)
                if "a1" not in current_lemmaname.lower():
                    lemmas[current_lemmaname] = (lemmaexpr, [])
                continue

            # Accumulate proof lines
            if current_lemmaname:
                if stripped and not stripped.startswith("Goal") and not stripped.startswith("Lemma") and not stripped.startswith("RESULT"):
                    current_proof_lines.append(stripped)
                    # detect usage of inline axioms or lemmas
                    matches = re.findall(r'\((single_lemma_\d+|history_lemma_\d+|a1)\)', stripped)
                    for ax in matches:
                        used_inline_axioms.add(ax)


            # Finalize current lemma if next Goal/Lemma or RESULT
            if re.match(r'(?:Goal|Lemma)\s+\d+', stripped) or stripped.startswith("RESULT"):
                if current_lemmaname and current_proof_lines:
                    proofs_by_lemma[current_lemmaname] = current_proof_lines.copy()
                    deps = parse_dependencies_from_proof(current_proof_lines)
                    expr, _ = lemmas[current_lemmaname]
                    lemmas[current_lemmaname] = (expr, deps)
                    current_proof_lines = []

        # Accumulate fof(...) blocks
        if "fof(" in stripped:
            buffer = stripped
            if buffer.endswith(")."):
                name = re.search(r"fof\(([^,]+)", buffer).group(1)
                formula_match = re.search(r"fof\([^,]+,[^,]+,(.*)\)\s*\.", buffer, re.DOTALL)
                if formula_match:
                    formula = formula_match.group(1).strip()
                    if "axiom" in buffer:
                        axiom = (name, formula)
                    elif "conjecture" in buffer:
                        conjecture = (name, formula)
                buffer = ""
            continue
        elif buffer:
            buffer += " " + stripped
            if buffer.endswith(")."):
                name = re.search(r"fof\(([^,]+)", buffer).group(1)
                formula_match = re.search(r"fof\([^,]+,[^,]+,(.*)\)\s*\.", buffer, re.DOTALL)
                if formula_match:
                    formula = formula_match.group(1).strip()
                    if "axiom" in buffer:
                        axiom = (name, formula)
                    elif "conjecture" in buffer:
                        conjecture = (name, formula)
                buffer = ""

if axiom is None or conjecture is None:
    print("ERROR: Missing axiom or conjecture in TPTP")
    sys.exit(1)

# Normalize axiom names and filter out those already proven
axiom_counter = 1
axiom_name_map = {}  # original inline name -> axiomN
for ax in sorted(used_inline_axioms):
    # Skip 'a1' if you treat it specially
    if ax == "a1":
        continue
    # If this axiom is already a lemma, skip it
    if ax in lemmas:
        continue
    axiom_name_map[ax] = f"axiom{axiom_counter}"
    axiom_counter += 1

# Normalize lemma names
normalized_lemmas = {}
name_mapping = {}
counter = 1

for old_name in lemmas.keys():
    if old_name.startswith("conjecture"):
        new_name = old_name
    else:
        new_name = f"lemma_{counter}"
        counter += 1
    name_mapping[old_name] = new_name
    normalized_lemmas[new_name] = lemmas[old_name]

lemmas = normalized_lemmas

# Normalize dependencies in lemmas
for lem_name, (expr, deps) in lemmas.items():
    new_deps = [name_mapping.get(d, d) for d in deps]
    lemmas[lem_name] = (expr, new_deps)

# Normalize proof lines dictionary keys
normalized_proofs = {}
for old_name, lines in proofs_by_lemma.items():
    if old_name in name_mapping:
        new_name = name_mapping[old_name]
        normalized_proofs[new_name] = lines
proofs_by_lemma = normalized_proofs

# Update lemma dependencies to point to axiom_n if needed
for lemmaname, (expr, deps) in lemmas.items():
    new_deps = []
    for d in deps:
        if d in axiom_name_map:
            new_deps.append(axiom_name_map[d])
        else:
            new_deps.append(d)
    lemmas[lemmaname] = (expr, new_deps)

# Output Lean file
axname, axexpr = axiom
conjname, conjexpr = conjecture

lean_ax = lean_abbrev(axname, axexpr)
lean_conj = lean_abbrev(conjname, conjexpr)

# Theorem header
theorem_header = (
    f"theorem Equation_{axname}_implies_Equation_{conjname}"
    f" (G : Type _) [Magma G]\n"
    f"    (op_law : Equation_{axname} G) : "
    f"Equation_{conjname} G :="
)

# Add only axioms that were not proven as lemmas
lean_axioms = ""
for old, new in axiom_name_map.items():
    lean_axioms += lean_axiom(new, inline_axioms[old])

# Add lemmas
lemma_text = ""
for lemmaname, (expr, deps) in lemmas.items():
    proof_lines = proofs_by_lemma.get(lemmaname)
    lemma_text += lean_lemma(lemmaname, expr, deps, proof_lines)

lean_output = f"""import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

{lean_ax}
{lean_axioms}
{lean_conj}
{theorem_header}{lemma_text}
"""

with open(output_file, "w") as f:
    f.write(lean_output)

print("✓ Generated Lean file:", output_file)
