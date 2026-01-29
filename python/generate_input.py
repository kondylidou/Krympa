import re
from pathlib import Path
import sys

# Paths
if len(sys.argv) < 2:
    print("Usage: python generate_tptp.py <proofs_file>")
    sys.exit(1)

PROOFS_FILE = Path(sys.argv[1])
if not PROOFS_FILE.exists():
    print(f"Proofs file {PROOFS_FILE} does not exist.")
    sys.exit(1)

# Extract file number (e.g., Proofs11 -> 11)
import re
m = re.search(r'(\d+)', PROOFS_FILE.stem)
file_number = m.group(1) if m else "0"

# Output folder based on file number
OUTPUT_DIR = Path(f"../benchmarks/input{file_number}")
OUTPUT_DIR.mkdir(exist_ok=True)

EQUATIONS_DIR = Path("../benchmarks/Equations")

# Regex patterns
THEOREM_RE = re.compile(r"theorem\s+(Equation\d+)_implies_(Equation\d+)")
EQUATION_START_RE = re.compile(r"equation\s+(\d+)\s*:=")

# Parse multi-line Lean equations
def build_equation_index():
    index = {}
    for file in EQUATIONS_DIR.glob("Eqns*.lean"):
        lines = file.read_text().splitlines()
        current_num = None
        buffer = []
        for line in lines:
            line_strip = line.strip()
            m = EQUATION_START_RE.match(line_strip)
            if m:
                if current_num is not None:
                    index[current_num] = " ".join(buffer).strip()
                current_num = int(m.group(1))
                buffer = [line_strip.split(":=",1)[1].strip()]
            elif current_num is not None:
                if line_strip.startswith("equation"):
                    index[current_num] = " ".join(buffer).strip()
                    current_num = None
                    buffer = []
                else:
                    buffer.append(line_strip)
        if current_num is not None:
            index[current_num] = " ".join(buffer).strip()
    return index

# Recursive infix ◇ -> prefix op
def infix_to_prefix(expr: str) -> str:
    """
    Convert Lean infix ◇ to prefix op(...) correctly, handling all nested parentheses.
    """
    expr = expr.strip()

    # Remove outer parentheses fully
    while expr.startswith('(') and expr.endswith(')'):
        # Ensure matching parentheses
        depth = 0
        for i, c in enumerate(expr):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            if depth == 0 and i < len(expr) - 1:
                break
        else:
            expr = expr[1:-1].strip()
            continue
        break

    # Base case: no ◇
    if '◇' not in expr:
        return expr

    # Split at top-level ◇
    depth = 0
    for i, c in enumerate(expr):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == '◇' and depth == 0:
            left = expr[:i].strip()
            right = expr[i+1:].strip()
            left_conv = infix_to_prefix(left)
            right_conv = infix_to_prefix(right)
            return f"op({left_conv},{right_conv})"

    # If no top-level ◇ found, recursively process inner expression
    return expr

# Map variables to TPTP
def lean_expr_to_tptp(expr: str):
    expr = expr.strip()

    # Split at '='
    if '=' not in expr:
        lhs, rhs = '', expr
    else:
        lhs, rhs = expr.split('=', 1)
        lhs = lhs.strip()
        rhs = rhs.strip()

    # Convert ◇ to nested op
    lhs = infix_to_prefix(lhs)
    rhs = infix_to_prefix(rhs)

    # Map variables
    var_map = {}
    counter = 0
    def repl(m):
        nonlocal counter
        v = m.group(0)
        if v == "op":
            return v
        if v not in var_map:
            var_map[v] = f"X{counter}"
            counter += 1
        return var_map[v]

    lhs = re.sub(r'\b[a-zA-Z_]\w*\b', repl, lhs)
    rhs = re.sub(r'\b[a-zA-Z_]\w*\b', repl, rhs)

    return f"({lhs} = {rhs})", list(var_map.values())

# Main
print("Indexing equations...")
EQUATION_INDEX = build_equation_index()
print(f"Indexed {len(EQUATION_INDEX)} equations")

proofs_text = PROOFS_FILE.read_text()
theorems = THEOREM_RE.findall(proofs_text)
print(f"Found {len(theorems)} theorems")

written = 0
skipped = 0

for ax_name, conj_name in theorems:
    ax_num = int(ax_name.replace("Equation", ""))
    conj_num = int(conj_name.replace("Equation", ""))

    if ax_num not in EQUATION_INDEX or conj_num not in EQUATION_INDEX:
        print(f"Skipping {ax_name}_implies_{conj_name}: missing equation")
        skipped += 1
        continue

    ax_expr = EQUATION_INDEX[ax_num]
    conj_expr = EQUATION_INDEX[conj_num]

    ax_tptp, ax_vars = lean_expr_to_tptp(ax_expr)
    conj_tptp, conj_vars = lean_expr_to_tptp(conj_expr)

    all_vars = sorted(set(ax_vars + conj_vars))
    vars_str = ", ".join(all_vars)

    tptp_text = f"""fof(a1, axiom,
    ! [{vars_str}] :
        {ax_tptp}
).

fof(conjecture0, conjecture,
    ! [{vars_str}] :
        {conj_tptp}
).
"""

    out_file = OUTPUT_DIR / f"{ax_name}_implies_{conj_name}.p"
    out_file.write_text(tptp_text)
    written += 1

print("\nDone.")
print(f"Written: {written}")
print(f"Skipped: {skipped}")
