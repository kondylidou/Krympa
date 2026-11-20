"""Convert a Krympa proof (`proof_*.out`) into a Lean 4 file.

Usage: python3 tolean.py <proof-file>
Writes lean/Proof/<basename>.lean next to this repository's `lean` project.

Every proof step is emitted as an explicit proof term, so Lean only checks the
proof and never has to search for it:

  * a Twee rewrite step `s = t` becomes `congrArg (fun hole => C[hole]) (dep args)`,
    one rewrite of one subterm;
  * a superposition step becomes one rewrite that turns the goal into an
    instance of a second equation, `Eq.mpr (congrArg ...) (dep args)`. This
    is the term form of `rw [dep₁ ..]; exact dep₂ ..`.

"One rewrite" means one instance of one equation, applied to one or more
occurrences of the same subterm (Vampire's superposition rewrites all
occurrences at once). The converter finds the instance and the occurrences
itself. A step that cannot be justified by one rewrite of its listed
dependencies is reported and left as `sorry`, so a file that Lean accepts
without warnings certifies the step count.
"""

import os
import re
import sys

VAR_NAMES = ["x", "y", "z", "w", "v", "u", "t", "s", "r", "q", "p", "o", "n", "m",
             "l", "k", "j", "i", "g", "f", "e", "d", "c", "b", "a"]
HOLE = "hole"
REAL_CONJ = "conjecture0"
TWEE_MARKER = "The conjecture is true! Here is a proof"


def fresh_name(i):
    return VAR_NAMES[i] if i < len(VAR_NAMES) else f"x{i}"


# --------------------------------------------------------------------------
# Terms.  A term is a variable name (str) or ("op", left, right).
# An equation is ("eq", left, right), so a context can span both sides.
# Pattern variables of a dependency are ("?", tag, name), so that the goal's
# own variables behave as constants during matching.
# --------------------------------------------------------------------------

TOKEN_RE = re.compile(r"\s*([A-Za-z_]\w*|[(),])")


def parse_term(text):
    """Parse `op(a, op(b, c))`; identifiers other than `op` are variables."""
    tokens = TOKEN_RE.findall(text)
    if "".join(tokens) != re.sub(r"\s+", "", text):
        raise ValueError(f"cannot tokenize term: {text!r}")
    pos = 0

    def term():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError(f"unexpected end of term: {text!r}")
        tok = tokens[pos]
        pos += 1
        if tok == "op" and pos < len(tokens) and tokens[pos] == "(":
            pos += 1
            left = term()
            expect(",")
            right = term()
            expect(")")
            return ("op", left, right)
        if tok in "(),":
            raise ValueError(f"unexpected {tok!r} in term: {text!r}")
        return tok.lower()

    def expect(tok):
        nonlocal pos
        if pos >= len(tokens) or tokens[pos] != tok:
            raise ValueError(f"expected {tok!r} in term: {text!r}")
        pos += 1

    result = term()
    if pos != len(tokens):
        raise ValueError(f"trailing input in term: {text!r}")
    return result


def strip_forall(text):
    m = re.match(r"\s*!\s*\[[^\]]*\]\s*:\s*(.*)", text, re.S)
    return (m.group(1) if m else text).strip()


def parse_equation(text):
    """Parse `[! [..] :] lhs = rhs[.]` into a pair of terms."""
    text = strip_forall(text).rstrip(".").strip()
    while text.startswith("(") and balanced(text[1:-1]) and text.endswith(")"):
        text = text[1:-1].strip()
    depth = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "=" and depth == 0:
            return parse_term(text[:i]), parse_term(text[i + 1:])
    raise ValueError(f"not an equation: {text!r}")


def balanced(text):
    depth = 0
    for ch in text:
        depth += ch == "("
        depth -= ch == ")"
        if depth < 0:
            return False
    return depth == 0


def term_vars(term, acc=None):
    """Variables in first-appearance order."""
    acc = [] if acc is None else acc
    if isinstance(term, str):
        if term not in acc:
            acc.append(term)
    elif term[0] == "op":
        term_vars(term[1], acc)
        term_vars(term[2], acc)
    return acc


def rename(term, mapping, default=None):
    if isinstance(term, str):
        return mapping.get(term, default if default is not None else term)
    return ("op", rename(term[1], mapping, default), rename(term[2], mapping, default))


def show(term):
    if isinstance(term, str):
        return term
    if term[0] == "eq":
        return f"{show(term[1])} = {show(term[2])}"
    return f"({show(term[1])} ◇ {show(term[2])})"


def positions(term, path=()):
    yield path
    if not isinstance(term, str) and term[0] in ("op", "eq"):
        yield from positions(term[1], path + (1,))
        yield from positions(term[2], path + (2,))


def subterm(term, path):
    for step in path:
        term = term[step]
    return term


def replace(term, path, new):
    if not path:
        return new
    parts = list(term)
    parts[path[0]] = replace(term[path[0]], path[1:], new)
    return tuple(parts)


def replace_all(term, paths, new):
    for path in paths:
        term = replace(term, path, new)
    return term


def as_pattern(term, tag):
    if isinstance(term, str):
        return ("?", tag, term)
    return ("op", as_pattern(term[1], tag), as_pattern(term[2], tag))


def is_pvar(term):
    return isinstance(term, tuple) and term[0] == "?"


def walk(term, subst):
    while is_pvar(term) and term in subst:
        term = subst[term]
    return term


def occurs(var, term, subst):
    term = walk(term, subst)
    if term == var:
        return True
    if isinstance(term, tuple):
        return occurs(var, term[1], subst) or occurs(var, term[2], subst)
    return False


def unify(a, b, subst):
    a, b = walk(a, subst), walk(b, subst)
    if a == b:
        return True
    if is_pvar(a):
        if occurs(a, b, subst):
            return False
        subst[a] = b
        return True
    if is_pvar(b):
        return unify(b, a, subst)
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == b[0]:
        return unify(a[1], b[1], subst) and unify(a[2], b[2], subst)
    return False


def resolve(term, subst, default):
    term = walk(term, subst)
    if is_pvar(term):
        return default
    if isinstance(term, str):
        return term
    return ("op", resolve(term[1], subst, default), resolve(term[2], subst, default))


# --------------------------------------------------------------------------
# Proved facts and the search for single-rewrite justifications
# --------------------------------------------------------------------------

USED = set()   # facts cited by the proof term currently being built


class Fact:
    """A universally quantified equation available under a Lean name."""

    def __init__(self, lean_name, lhs, rhs):
        order = term_vars(rhs, term_vars(lhs))
        mapping = {v: fresh_name(i) for i, v in enumerate(order)}
        self.lean_name = lean_name
        self.vars = [mapping[v] for v in order]
        self.lhs = rename(lhs, mapping)
        self.rhs = rename(rhs, mapping)

    def pattern(self, tag):
        return as_pattern(self.lhs, tag), as_pattern(self.rhs, tag)

    def apply(self, tag, subst, default, flipped):
        """Lean term proving the instance (or its mirror image if `flipped`)."""
        USED.add(self)
        args = [show(resolve(("?", tag, v), subst, default)) for v in self.vars]
        term = " ".join([self.lean_name] + args)
        if flipped:
            return f"({term}).symm"
        return f"({term})" if args else term

    def statement(self):
        return f"{show(self.lhs)} = {show(self.rhs)}"


def context(term, paths):
    return f"(fun {HOLE} : G => {show(replace_all(term, paths, HOLE))})"


def instance_of(goal, fact, default):
    """`goal` is an instance of `fact` (no rewrite at all)."""
    s, t = goal
    a1, a2 = fact.pattern("A")
    for (m1, m2), flipped in (((a1, a2), False), ((a2, a1), True)):
        subst = {}
        if unify(m1, s, subst) and unify(m2, t, subst):
            return fact.apply("A", subst, default, flipped)
    return None


def difference(s, t, path=()):
    """Outermost positions where s and t differ, as (path, s-part, t-part)."""
    if s == t:
        return []
    if isinstance(s, tuple) and isinstance(t, tuple) and s[0] == t[0]:
        return difference(s[1], t[1], path + (1,)) + difference(s[2], t[2], path + (2,))
    return [(path, s, t)]


def rewrite_sites(s, t):
    """Candidate hole sets for rewriting s into t with one equation instance."""
    diff = difference(s, t)
    if not diff:
        return
    if len({(a, b) for _, a, b in diff}) == 1:
        yield [path for path, _, _ in diff]
    # a single hole anywhere above all differences, deepest first
    common = diff[0][0]
    for path, _, _ in diff[1:]:
        k = 0
        while k < min(len(common), len(path)) and common[k] == path[k]:
            k += 1
        common = common[:k]
    start = len(common) if len(diff) > 1 else len(common) - 1
    for k in range(start, -1, -1):
        yield [common[:k]]


def one_rewrite(goal, fact, default):
    """`goal` is `s = t` where t is s rewritten once by `fact`."""
    s, t = goal
    b1, b2 = fact.pattern("B")
    for paths in rewrite_sites(s, t):
        for (l, r), flipped in (((b1, b2), False), ((b2, b1), True)):
            subst = {}
            if unify(l, subterm(s, paths[0]), subst) and unify(r, subterm(t, paths[0]), subst):
                eq_proof = fact.apply("B", subst, default, flipped)
                if paths == [()]:
                    return eq_proof, 1
                return f"(congrArg {context(s, paths)} {eq_proof})", len(paths)
    return None


def occurrence_sets(paths):
    """Which occurrences of a subterm to rewrite: each alone, all, then the rest."""
    yield from ([p] for p in paths)
    if len(paths) > 1:
        yield list(paths)
    if 2 < len(paths) <= 8:
        for mask in range(1, 2 ** len(paths) - 1):
            chosen = [p for i, p in enumerate(paths) if mask >> i & 1]
            if len(chosen) > 1:
                yield chosen


def rewrite_then_instance(goal, main, side, default):
    """One rewrite with `side` turns `goal` into an instance of `main`.

    This is a superposition step: `main` instantiated, with the occurrences of
    one subterm rewritten by `side`.
    """
    equation = ("eq", goal[0], goal[1])
    a1, a2 = main.pattern("A")
    b1, b2 = side.pattern("B")
    occurrences = {}
    for path in positions(equation):
        if path:
            occurrences.setdefault(subterm(equation, path), []).append(path)
    for (l, r), side_flipped in (((b1, b2), True), ((b2, b1), False)):
        # the goal is (main σ) with occurrences of l τ replaced by r τ
        for target, paths in occurrences.items():
            base = {}
            if not unify(r, target, base):
                continue
            for chosen in occurrence_sets(paths):
                before = replace_all(equation, chosen, l)
                for (m1, m2), main_flipped in (((a1, a2), False), ((a2, a1), True)):
                    subst = dict(base)
                    if unify(("eq", m1, m2), before, subst):
                        back = side.apply("B", subst, default, side_flipped)
                        proof = (f"(Eq.mpr (congrArg {context(equation, chosen)} {back}) "
                                 f"{main.apply('A', subst, default, main_flipped)})")
                        return proof, len(chosen)
    return None


def at(count):
    return "" if count == 1 else f" at {count} occurrences"


def justify(goal, facts, default, allow_pairs=True, pool=None):
    """Return (proof term, rewrites, description) or None.

    `rewrites` is 0 when the goal is a plain instance of a fact and 1 when one
    equation instance has to be rewritten with. With `pool`, a superposition
    may also combine a fact from `facts` with any fact from `pool`.
    """
    for fact in facts:
        proof = instance_of(goal, fact, default)
        if proof:
            return proof, 0, f"instance of {fact.lean_name}"
    for fact in facts:
        found = one_rewrite(goal, fact, default)
        if found:
            return found[0], 1, f"one rewrite with {fact.lean_name}{at(found[1])}"
    if allow_pairs:
        if pool is None:
            pairs = [(main, side) for main in facts for side in facts]
        else:
            pairs = ([(main, side) for main in facts for side in pool]
                     + [(main, side) for main in pool for side in facts])
        for main, side in pairs:
            found = rewrite_then_instance(goal, main, side, default)
            if found:
                return (found[0], 1, f"one rewrite with {side.lean_name}{at(found[1])}, "
                                     f"closed by {main.lean_name}")
    return None


# --------------------------------------------------------------------------
# Reading the Krympa proof file
# --------------------------------------------------------------------------

DEP_NAME_RE = re.compile(r"\b(a_?\d+|(?:[A-Za-z]+_)*lemma_\d+|conjecture\w*)\b")
VARIANT_RE = re.compile(r"^(?:[A-Za-z]+_)*?(?:lemma|conjecture)_(\d+)$")
STEP_RE = re.compile(r"^=\s*\{\s*by\s+(.*?)\s*\}\s*$")
REF_RE = re.compile(r"(axiom|lemma)\s+(\d+)(?:\s*\(([^)]+)\))?", re.I)


def canon(name):
    """small_step_lemma_0021, big_step_lemma_0021, conjecture_0021 -> lemma_0021."""
    name = name.strip()
    if name.startswith("twee_"):
        return name
    m = VARIANT_RE.match(name)
    return f"lemma_{m.group(1)}" if m else name


def parse_deps(text):
    """`name: formula, name, name: formula + name` -> [(name, formula or None)]."""
    found = list(DEP_NAME_RE.finditer(text))
    deps = []
    for i, m in enumerate(found):
        end = found[i + 1].start() if i + 1 < len(found) else len(text)
        rest = text[m.end():end].strip()
        formula = None
        if rest.startswith(":"):
            formula = rest[1:].strip().rstrip(",+").strip() or None
        deps.append((m.group(1), formula))
    return deps


def read_proof(path):
    """Return (input axioms, conjecture, items in proof order)."""
    axioms, conjecture, items = [], None, []
    fof = None
    block = 0
    current = None          # item being read inside a Twee block
    stage = None            # "header" or "chain"

    def close():
        nonlocal current, stage
        if current is not None:
            items.append(current)
        current, stage = None, None

    with open(path) as handle:
        for raw in handle:
            line = raw.strip()

            if fof is not None or line.startswith("fof("):
                fof = line if fof is None else fof + " " + line
                if fof.endswith(")."):
                    m = re.match(r"fof\(\s*(\w+)\s*,\s*(\w+)\s*,(.*)\)\s*\.$", fof, re.S)
                    if m and m.group(2) == "axiom":
                        axioms.append((m.group(1), m.group(3).strip()))
                    elif m and "conjecture" in m.group(2):
                        conjecture = (m.group(1), m.group(3).strip())
                    fof = None
                continue

            if line.startswith(TWEE_MARKER):
                close()
                block += 1
                continue

            if line.startswith("%"):
                m = re.match(r"%\s*([A-Za-z_]\w*)\s*:\s*(.*)$", line)
                if m:
                    close()
                    body, _, deps = m.group(2).partition("| deps:")
                    items.append({"kind": "line", "name": m.group(1),
                                  "formula": body.strip(), "deps": parse_deps(deps)})
                continue

            if not line:
                continue

            m = re.match(r"Axiom\s+(\d+)\s+\(([^)]+)\)\s*:\s*(.*)$", line)
            if m:
                close()
                items.append({"kind": "axiom", "block": block, "number": m.group(1),
                              "name": m.group(2).strip(), "formula": m.group(3)})
                continue

            m = re.match(r"(Goal|Lemma)\s+(\d+)(?:\s*\(([^)]+)\))?\s*:\s*(.*)$", line)
            if m:
                close()
                current = {"kind": "chain", "block": block, "number": m.group(2),
                           "role": m.group(1), "name": (m.group(3) or "").strip(),
                           "formula": m.group(4), "terms": [], "steps": []}
                stage = "header"
                continue

            if line.startswith("RESULT"):
                close()
                continue

            if current is None:
                continue
            if line == "Proof:":
                stage = "chain"
                current["terms"].append("")
            elif stage == "header":
                current["formula"] += " " + line
            elif STEP_RE.match(line):
                current["steps"].append(STEP_RE.match(line).group(1))
                current["terms"].append("")
            else:
                current["terms"][-1] += " " + line
    close()
    return axioms, conjecture, items


# --------------------------------------------------------------------------
# Building the Lean file
# --------------------------------------------------------------------------

class Converter:
    def __init__(self, axioms, conjecture, items):
        self.items = items
        self.conjecture = conjecture
        self.out = []
        self.by_name = {}        # exact name / canonical name -> Fact
        self.all_facts = []
        self.axiom_facts = []
        self.block_axioms = {}   # (block, number) -> Fact
        self.block_lemmas = {}   # (block, number) -> Fact
        self.uses = {}           # Fact -> facts its proof cites
        self.item_of = {}        # Fact -> the proof-file item it was built from
        self.labels = {}         # Fact -> name in the Krympa proof
        self.counter = 0
        self.steps = 0
        self.rewrites = 0
        self.failures = []
        self.failed_steps = 0
        self.notes = []
        self.assumed = []
        self.hypotheses = []
        for i, (name, formula) in enumerate(axioms):
            hyp = "op_law" if len(axioms) == 1 else f"{name}_law"
            fact = Fact(hyp, *parse_equation(formula))
            self.hypotheses.append((hyp, name, fact))
            self.axiom_facts.append(fact)
            self.by_name[name] = fact
            self.by_name[f"a_{i + 1}"] = fact

    # ---- looking up dependencies -------------------------------------------

    def covers(self, fact, formula):
        """`formula` is an instance of `fact` (a lookup, not a use of it)."""
        cited = set(USED)
        try:
            return instance_of(parse_equation(formula), fact, "x") is not None
        except ValueError:
            return False
        finally:
            USED.clear()
            USED.update(cited)

    def lookup(self, name, formula=None):
        """The proved fact a dependency refers to, or None."""
        candidates = [self.by_name.get(name), self.by_name.get(canon(name))]
        candidates = [c for c in candidates if c is not None]
        if formula is None:
            return candidates[0] if candidates else None
        for fact in candidates + self.axiom_facts + self.all_facts[::-1]:
            if self.covers(fact, formula):
                return fact
        return None

    def assume(self, name, formula):
        """A dependency that the file never proves: state it with `sorry`."""
        self.counter += 1
        fact = Fact(f"assumed_{self.counter}", *parse_equation(formula))
        self.assumed.append(name)
        self.emit_have(fact, "sorry", f"{name}: used but not proved in this file")
        self.register(name, fact)
        return fact

    def register(self, name, fact):
        self.by_name[name] = fact
        self.by_name[canon(name)] = fact
        self.all_facts.append(fact)

    # ---- emitting ----------------------------------------------------------

    def emit_have(self, fact, proof, comment):
        self.uses[fact] = set(USED)
        self.labels[fact] = comment.split(":")[0]
        USED.clear()
        binder = f" ({' '.join(fact.vars)} : G)" if fact.vars else ""
        self.out.append(
            f"  -- {comment}\n"
            f"  have {fact.lean_name}{binder} :\n"
            f"      {show(fact.lhs)} =\n"
            f"      {show(fact.rhs)} :=\n"
            f"    {proof}\n")

    def new_fact(self, lhs, rhs):
        self.counter += 1
        return Fact(f"lemma_{self.counter}", lhs, rhs)

    def fail(self, label, why):
        self.failures.append(f"{label}: {why}")
        self.failed_steps += 1
        return "sorry"

    # ---- one superposition line --------------------------------------------

    def convert_line(self, item):
        name = item["name"]
        fact = self.new_fact(*parse_equation(item["formula"]))
        self.item_of[fact] = item
        deps, missing = [], []
        for dep_name, formula in item["deps"]:
            if canon(dep_name) == canon(name) or dep_name.startswith("conjecture"):
                continue                      # the statement itself, not a premise
            dep = self.lookup(dep_name, formula)
            if dep is None:
                missing.append(dep_name)      # e.g. a lemma that is only proved later
            elif dep not in deps:
                deps.append(dep)
        self.steps += 1
        goal = (fact.lhs, fact.rhs)
        default = fact.vars[0] if fact.vars else "x"
        found = justify(goal, deps, default)
        if not found:
            # The dependency list can be incomplete: allow any earlier equation
            # as well, still within a single rewrite.
            USED.clear()
            earlier = self.axiom_facts + self.all_facts
            found = (justify(goal, earlier, default, allow_pairs=False)
                     or justify(goal, deps, default, pool=earlier)
                     or justify(goal, earlier, default))
            if found:
                extra = sorted(f.lean_name for f in USED if f not in deps)
                self.notes.append(f"{name}: also needs {', '.join(extra)}, which its "
                                  f"dependency list does not mention")
        if found:
            proof, rewrites, how = found
            self.rewrites += rewrites
            if missing:
                self.notes.append(f"{name}: lists {', '.join(missing)}, which is not "
                                  f"proved before it (not needed)")
        else:
            listed = ", ".join([d.lean_name for d in deps] + missing) or "nothing"
            how = f"NOT a single rewrite of {listed}"
            proof = self.fail(name, how)
        self.emit_have(fact, proof, f"{name}: {how}")
        self.register(name, fact)

    # ---- one Twee lemma or goal --------------------------------------------

    def step_facts(self, item, text):
        """Facts cited by a `by ...` annotation, in citation order."""
        facts = []
        for kind, number, cited in REF_RE.findall(text):
            key = (item["block"], number)
            if kind.lower() == "lemma":
                fact = self.block_lemmas.get(key)
            else:
                fact = self.block_axioms.get(key) or (self.lookup(cited) if cited else None)
            if fact is None:
                self.failures.append(f"{item['name'] or 'Lemma ' + item['number']}: "
                                     f"unknown reference '{kind} {number}'")
            elif fact not in facts:
                facts.append(fact)
        return facts

    def convert_chain(self, item):
        label = item["name"] or f"Lemma {item['number']} (block {item['block']})"
        lhs, rhs = parse_equation(item["formula"])
        fact = self.new_fact(lhs, rhs)
        self.item_of[fact] = item
        order = term_vars(rhs, term_vars(lhs))
        mapping = {v: fresh_name(i) for i, v in enumerate(order)}
        default = fact.vars[0] if fact.vars else "x"
        # variables the prover introduced on the way are instantiated uniformly
        terms = [rename(parse_term(t), mapping, default) for t in item["terms"]]

        lines, notes = [], []
        for i, annotation in enumerate(item["steps"]):
            self.steps += 1
            facts = self.step_facts(item, annotation)
            merged = "superposition" in annotation
            found = justify((terms[i], terms[i + 1]), facts, default, allow_pairs=merged)
            if found:
                proof, rewrites, how = found
                self.rewrites += rewrites
            else:
                how = f"step {i + 1} is NOT a single rewrite ({annotation})"
                proof = self.fail(label, how)
            notes.append(how)
            lines.append(f"      _ = {show(terms[i + 1])} :=\n        {proof}")

        if not lines:
            proof = self.fail(label, "no proof steps")
        elif (terms[0], terms[-1]) == (fact.lhs, fact.rhs):
            proof = "calc " + show(terms[0]) + "\n" + "\n".join(lines)
        elif (terms[0], terms[-1]) == (fact.rhs, fact.lhs):
            proof = "Eq.symm (calc " + show(terms[0]) + "\n" + "\n".join(lines) + ")"
        else:
            proof = self.fail(label, "the rewrite chain does not connect the two sides")
        summary = "; ".join(dict.fromkeys(notes)) if notes else "no steps"
        self.emit_have(fact, proof, f"{label}: {len(lines)} steps: {summary}")

        if item["role"] == "Lemma":
            self.block_lemmas[(item["block"], item["number"])] = fact
        if item["name"]:
            self.register(item["name"], fact)
        else:
            self.all_facts.append(fact)

    # ---- whole file --------------------------------------------------------

    def convert(self):
        for item in self.items:
            if item["kind"] == "line":
                self.convert_line(item)
            elif item["kind"] == "axiom":
                fact = self.lookup(item["name"], item["formula"])
                if fact is None:
                    fact = self.assume(item["name"], item["formula"])
                self.block_axioms[(item["block"], item["number"])] = fact
            else:
                self.convert_chain(item)
        return self.closing()

    def closing(self):
        """The conjecture must be an instance of something that was proved."""
        USED.clear()
        if self.conjecture is None:
            if self.all_facts:
                USED.add(self.all_facts[-1])
            return "  " + (self.all_facts[-1].lean_name if self.all_facts else "sorry") + "\n"
        goal = Fact("goal", *parse_equation(self.conjecture[1]))
        default = goal.vars[0] if goal.vars else "x"
        for fact in self.all_facts[::-1] + self.axiom_facts:
            proof = instance_of((goal.lhs, goal.rhs), fact, default)
            if proof:
                return f"  fun {' '.join(goal.vars)} => {proof}\n"
        self.failures.append("the conjecture is not an instance of any proved lemma")
        return f"  fun {' '.join(goal.vars)} => sorry\n"

    def unused(self):
        """Names of proved steps that the final theorem does not depend on."""
        needed, stack = set(), list(USED)
        while stack:
            fact = stack.pop()
            if fact not in needed:
                needed.add(fact)
                stack.extend(self.uses.get(fact, ()))
        return [self.labels[f] for f in self.all_facts if f not in needed]


def abbrev(name, formula):
    fact = Fact(name, *parse_equation(formula))
    return (f"abbrev Equation_{name} (G : Type _) [Magma G] :=\n"
            f"  ∀ {' '.join(fact.vars)} : G, {fact.statement()}\n")


def main():
    if len(sys.argv) != 2:
        print("Usage: python tolean.py input_file")
        sys.exit(1)
    input_file = sys.argv[1]
    basename = os.path.splitext(os.path.basename(input_file))[0]
    project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    output_dir = os.path.join(project_root, "lean", "Proof")
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, f"{basename}.lean")

    axioms, conjecture, items = read_proof(input_file)
    if not axioms:
        print("ERROR: no axiom found in the input problem section")
        sys.exit(1)

    conv = Converter(axioms, conjecture, items)
    closing = conv.convert()
    unused = conv.unused()
    summary = (f"{conv.steps} proof steps: {conv.rewrites} rewrite a subterm, "
               f"{conv.steps - conv.rewrites - conv.failed_steps} only instantiate "
               f"an earlier equation")

    conj_name = conjecture[0] if conjecture else "no_conjecture"
    hyps = "\n".join(f"    ({hyp} : Equation_{name} G)" for hyp, name, _ in conv.hypotheses)
    goal_type = f"Equation_{conj_name} G" if conjecture else conv.all_facts[-1].statement()
    parts = [
        f"-- Generated by python/tolean.py from {os.path.basename(input_file)}.\n"
        f"-- {summary}.\n",
        "set_option linter.unusedVariables false\n",
        "class Magma (α : Type _) where\n  op : α → α → α\n",
        'infix:65 " ◇ " => Magma.op\n',
        *[abbrev(name, formula) for name, formula in axioms],
        *([abbrev(*conjecture)] if conjecture else []),
        f"theorem Equation_{axioms[0][0]}_implies_Equation_{conj_name} (G : Type _) [Magma G]\n"
        f"{hyps} :\n    {goal_type} :=\n" + "\n".join(conv.out) + "\n" + closing,
    ]
    with open(output_file, "w") as handle:
        handle.write("\n".join(parts))

    print("✓ Generated Lean file:", output_file)
    print(f"  {summary}")
    for name in unused:
        print(f"  note: {name} is proved but nothing depends on it")
    for note in conv.notes:
        print(f"  note: {note}")
    for name in conv.assumed:
        print(f"  WARNING: {name} is used but never proved; stated with `sorry`")
    for failure in conv.failures:
        print(f"  WARNING: {failure}")
    if conv.assumed or conv.failures:
        print("  The Lean file contains `sorry`; it does not certify the proof.")
        sys.exit(2)


if __name__ == "__main__":
    main()
