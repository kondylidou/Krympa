"""Remove avoidable steps from a Krympa proof.

Usage: python3 compress.py <proof-file> [output-file]

A superposition line of the proof is avoidable if every step that uses it can
be derived in one rewrite from the other equations instead. Such lines, and
then the lines nothing needs any more, are dropped. No prover is called: the
one-rewrite search is the one `tolean.py` uses to check a step.

Only superposition lines are touched; Twee rewrite chains are kept as they are.
The result is written as a proof file in the same format, so `tolean.py` can
certify it.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tolean as T  # noqa: E402

LINE_RE = re.compile(r"^%\s*([A-Za-z_]\w*)\s*:")
HEADER = "% === Superposition Steps ==="


def segments(items):
    """Lines between two Twee blocks may be reordered; number those groups."""
    seg, out = 0, {}
    for i, item in enumerate(items):
        if item["kind"] == "line":
            out[i] = 2 * seg
        else:
            seg = max(seg, item["block"])
            out[i] = 2 * item["block"] - 1
    return out


def compress(path):
    axioms, conjecture, items = T.read_proof(path)
    conv = T.Converter(axioms, conjecture, items)
    conv.convert()
    final_uses = set(T.USED)
    if conv.failures or conv.assumed:
        raise SystemExit("the proof does not check as it is; not compressing:\n  "
                         + "\n  ".join(conv.failures + conv.assumed))

    seg_of_item = segments(items)
    index = {id(item): i for i, item in enumerate(items)}
    facts = [f for f in conv.all_facts if f in conv.item_of]
    seg = {f: seg_of_item[index[id(conv.item_of[f])]] for f in facts}
    is_line = {f: conv.item_of[f]["kind"] == "line" for f in facts}
    citable = {f: is_line[f] or bool(conv.item_of[f]["name"]) for f in facts}
    uses = {f: set(conv.uses.get(f, ())) for f in facts}
    removed = set()

    def ancestors(f, using, acc=None):
        acc = set() if acc is None else acc
        for g in using.get(f, ()):
            if g not in acc:
                acc.add(g)
                ancestors(g, using, acc)
        return acc

    def available(d, without, using):
        """Equations d may be derived from: nothing that itself needs d."""
        pool = list(conv.axiom_facts)
        for f in facts:
            if f is d or f in removed or f in without or not citable[f]:
                continue
            ok = seg[f] <= seg[d] if is_line[f] else seg[f] < seg[d]
            if ok and d not in ancestors(f, using):
                pool.append(f)
        return pool

    def needed():
        keep, stack = set(), list(final_uses)
        while stack:
            f = stack.pop()
            if f not in keep:
                keep.add(f)
                stack.extend(uses.get(f, ()))
        return keep

    changed = True
    while changed:
        changed = False
        live = needed()
        for s in [f for f in reversed(facts) if is_line[f] and f in live and f not in removed]:
            if s in final_uses:
                continue
            dependents = [d for d in facts if d in live and d not in removed and s in uses[d]]
            if any(not is_line[d] for d in dependents):
                continue                       # a Twee chain cites it: keep
            # Re-derive the dependents one after the other, each seeing the
            # new derivations of the ones before it; otherwise two of them
            # could end up depending on each other.
            trial = dict(uses)
            for d in dependents:
                default = d.vars[0] if d.vars else "x"
                pool = available(d, {s}, trial)
                T.USED.clear()
                found = (T.justify((d.lhs, d.rhs), pool, default, allow_pairs=False)
                         or T.justify((d.lhs, d.rhs), pool, default))
                if not found:
                    break
                trial[d] = set(T.USED)
            else:
                uses.update(trial)
                removed.add(s)
                changed = True
                live = needed()
    T.USED.clear()

    keep = {f for f in needed() if f not in removed}
    for f in keep:
        if f in ancestors(f, uses):
            raise SystemExit(f"internal error: {conv.item_of[f]['name']} depends on itself")
    kept_lines = [f for f in facts if is_line[f] and f in keep]
    return conv, items, facts, uses, seg, is_line, kept_lines


def write(path, out_path, conv, facts, uses, seg, kept_lines):
    name_of = {f: conv.item_of[f]["name"] for f in facts}
    for hyp, name, fact in conv.hypotheses:
        name_of[fact] = name

    def ordered(group):
        """Dependencies first, otherwise the original order."""
        done, out = set(), []

        def visit(f):
            if f in done or f not in group:
                return
            done.add(f)
            for g in [g for g in facts if g in uses[f]]:
                visit(g)
            out.append(f)

        for f in facts:
            visit(f)
        return out

    by_segment = {}
    for f in kept_lines:
        by_segment.setdefault(seg[f], []).append(f)

    out, blocks, emitted = [], 0, set()
    for raw in open(path):
        line = raw.rstrip("\n")
        if line.strip().startswith(T.TWEE_MARKER):
            blocks += 1
        is_step = bool(LINE_RE.match(line.strip())) or line.strip() == HEADER
        if not is_step:
            out.append(line)
            continue
        current = 2 * blocks
        if current in emitted:
            continue
        emitted.add(current)
        group = by_segment.get(current, [])
        if group:
            out.append(HEADER)
            for f in ordered(set(group)):
                deps = ", ".join(name_of[g] for g in facts + conv.axiom_facts if g in uses[f])
                out.append(f"% {name_of[f]}: {conv.item_of[f]['formula']} | deps: {deps}")
    text = re.sub(r"\n{3,}", "\n\n", "\n".join(out)) + "\n"
    with open(out_path, "w") as handle:
        handle.write(text)


def main():
    if len(sys.argv) not in (2, 3):
        print("Usage: python compress.py proof_file [output_file]")
        sys.exit(1)
    path = sys.argv[1]
    base, ext = os.path.splitext(path)
    out_path = sys.argv[2] if len(sys.argv) == 3 else f"{base}_compressed{ext}"
    conv, items, facts, uses, seg, is_line, kept_lines = compress(path)
    before = sum(1 for f in facts if is_line[f])
    write(path, out_path, conv, facts, uses, seg, kept_lines)
    saved = before - len(kept_lines)
    print(f"✓ {conv.steps} -> {conv.steps - saved} steps ({saved} superposition lines removed)")
    print(f"  written to {out_path}")


if __name__ == "__main__":
    main()
