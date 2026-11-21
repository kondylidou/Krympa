# Developers Guide

How to run the tool is in `README.md`, the method in the paper. This file is
for working on the code.

## Build and Checks

```bash
cd rust
./build.sh                      # optimized rust/krympa and rust/benchmarking_binary
cargo fmt
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test
```

- The build also compiles the OCaml extractor into `rust/ocaml_install/tptp_parser`,
  so `dune` must be installed.
- The two binaries and `tptp_parser` are tracked by git; a build shows up in
  `git status`.
- CI runs the three `cargo` checks and fails on any formatting difference or
  clippy warning. It uses the latest stable Rust, so its clippy can flag code
  that passes locally; `rustup update stable` avoids that.
- Remove build artifacts with `git clean -fdX rust/target ocaml/_build` (they are
  ignored files, so `-X` is needed).

## Where Things Are

| Path | Contents |
|---|---|
| `rust/src/main.rs`, `execution.rs`, `logging.rs` | Command line, the flags, `KRYMPA_LOG`. |
| `rust/src/provers.rs` | Every call of Twee and Vampire, where their executables come from, proof length, term size. |
| `rust/src/proof_turnaround.rs` | Turning Vampire's refutation into a forward proof. |
| `rust/src/collect.rs` | `collect`, `shorten`, `group`. |
| `rust/src/direct.rs` | `direct`: collecting only the lemmas that are needed. |
| `rust/src/minimize.rs` | `minimize`: the search over arrival and departure lemmas. |
| `rust/src/prove.rs` | Proving one goal with both provers and choosing between the two proofs. |
| `rust/src/trim.rs` | Dropping the parts of a segment that later segments do not use. |
| `rust/src/refine.rs` | The final refinement. |
| `rust/src/superpose.rs` | Reading a turned Vampire proof and writing the steps a goal needs as a block of lines. |
| `rust/src/dag.rs` | Dependencies between lemmas, read from the Twee proofs, and the graph built from them. |
| `rust/src/utils.rs`, `regex_cache.rs` | Lemma files, TPTP editing, temporary problem files; compiled regexes are kept for reuse. |
| `rust/src/alpha_match.rs` | Equality of formulas up to renaming and orientation. |
| `rust/src/bench_run.rs` | The benchmark driver behind `shell/run`. |
| `rust/tests/` | One test file per topic. |
| `ocaml/` | Lemma extractor: writes the lemma problems of a Vampire proof in the three variants. |
| `python/` | `generate_input.py` (benchmark file to TPTP problems), `summarize.py` (benchmark logs), `tolean.py`, `compress.py`. |
| `shell/` | `run_checked`, `run_one`, `run`. |
| `lean/` | Lean project for checking exported proofs. |
| `bin/` | Vampire and Twee, for Linux and macOS. Optional: see the prover options in `README.md`. |

Working directories, all next to `rust/` and ignored by git:

| Directory | Contents |
|---|---|
| `output/` | `vampire_proof_<name>.out`, `summary_<name>.json` (kept proof per lemma), `proof_<name>.out`, and the graph and lemmas of the chosen arrival lemma. |
| `lemmas/` | Lemma problems in `big-step/`, `small-step/`, `abstracted/`; temporary problems in `tmp/`. |
| `proofs/` | The kept proof of each lemma; every proof found, in `vampire_tmp/` and `twee_tmp/`. |
| `tmp/` | Proofs made by `shorten`, which are then copied to `proofs/`. |

## The Commands

Run from `rust/`; each reads what the previous one wrote. A step is one Twee
rewrite or one Vampire inference.

```bash
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p
./krympa run_vampire "$INPUT"
./krympa collect "$INPUT"
./krympa shorten "$INPUT"
./krympa minimize "$INPUT"      # or, instead of the last three: ./krympa direct "$INPUT"
```

| Command | What it does |
|---|---|
| `run_vampire` | Proves the problem with Vampire and turns the refutation into a forward proof. The equations it derives are the lemmas, numbered in order. |
| `collect` | Proves every lemma in three variants with Vampire and Twee (7 s per call) and keeps the shortest proof. Big-step: from the axioms. Small-step: from the axioms and all earlier lemmas. Abstracted: from the axioms, with one subterm of the lemma replaced by a variable. |
| `shorten` | Proves small-step lemmas again, using the abstracted statement of an earlier lemma where that variant was kept. |
| `minimize` | Tries each of the last 5 lemmas as arrival lemma and, for each, the lemmas its proof depends on as departure lemma. The proof then has three segments: axioms to departure lemma, departure to arrival lemma, arrival lemma to conjecture. The first is taken from the Vampire proof, the other two are proved again by both provers. The combination with the fewest steps is written out. |
| `direct` | Replaces `collect`, `shorten` and `minimize`; see below. |
| `group` | Optional analysis: groups the lemmas by the axioms their proofs use, in `output/structural_groups.txt`. |

For debugging use `KRYMPA_LOG=debug ./krympa --sequential <command> "$INPUT"`:
one prover call at a time and a readable trace.

Things to know:

- Dependencies between lemmas are read from the Twee proof of the kept variant:
  the lemmas it cites as axioms.
- Inside `minimize`, Twee is stopped after 7 s but Vampire runs until its own
  limit of 60 s (`run_vampire_turned` against `run_vampire_limited`).
- Vampire's default strategy (`lrs`) depends on elapsed time, so the same
  problem can give different proofs on a loaded machine. Setting
  `VAMPIRE_OPTIONS="-sa discount"` for all commands of a run avoids this.

## The Proof File

`output/proof_<name>.out` is the input problem followed by the segments, each in
one of two forms.

```
% === Superposition Steps ===
% lemma_0003: op(X0,X1) = X0 | deps: lemma_0001, a_1: ! [X0] : ...
```

One line per Vampire inference: name, equation, premises. `lemma_NNNN` is a
fresh name, `small_step_lemma_NNNN` (or `big_step_`, `abstracted_`) is lemma
NNNN of the original proof, `a_1` is the axiom, `conjecture` the goal.

```
The conjecture is true! Here is a proof.
Axiom 1 (lemma_0003): ...
Goal 1 (small_step_lemma_0058): ...
Proof:
  term
= { by axiom 1 (lemma_0003) R->L }
  term
```

A Twee proof, unchanged: each `= { by ... }` is one step.

## Direct

`collect` proves every lemma, but `minimize` only looks at the lemmas it can
reach from its arrival candidates. `direct` proves exactly those:

1. The lemma problems are written in all three variants, but not proved.
2. The arrival candidates are proved: going back from the end of the proof, the
   first 5 lemmas that have no Skolem constant and a proof.
3. For each proved lemma, the lemmas its kept Twee proof cites are proved next.
   This repeats until nothing new turns up.
4. `shorten` and `minimize` run unchanged on what was proved.

A lemma that is proved is treated as in `collect`, so the segmentation, the
candidates, `--term-size` and the final refinement are those of the pipeline.
On ten large problems it proved 38% of the lemmas and took 62% of the time.

One difference remains: `minimize` redirects a lemma that also occurs as an
internal lemma of some Twee proof. `direct` only knows the Twee proofs it made,
so it can end up with other departure candidates and a different proof (4 of
18 test proofs, three of them shorter).

## Term Size and Final Refinement

With `--term-size`, when Twee and Vampire both prove a goal, the proof with the
smaller average term size is chosen if it is at most 1.5 times as long as the
other; otherwise, and without the flag, the shorter one. A term's size is twice
its number of `op` symbols plus one.

The final refinement (`refine_final_proof`) then runs once on the best proof. It
needs a last Twee section with exactly one internal lemma, followed by a block
of superposition lines; otherwise it does nothing. A merged step is accepted
only if Vampire's proof of it has exactly one rewriting inference and otherwise
only rules from a fixed list (`is_single_rewrite_refutation`).

## Turning a Vampire Proof Around

Vampire proves by refutation: the end of its proof rewrites the negated goal
until it is contradictory. `proof_turnaround.rs` turns that end around so that
it reads as a derivation of the goal. Two rules, each with a test:

- Each turned line lists the equation it is derived with. In the refutation,
  step i+1 follows from step i and an equation E; read forwards, the statement
  of step i follows from that of step i+1 and E. So E belongs to the line of
  step i.
- A clause of the refutation can have variables of its own. Negated, it is an
  existential statement and is printed with `?`. Such a line counts as a step
  but is not a lemma: no lemma problem is written for it, and the Lean export
  skips it.

If either is violated, a proof can lose a lemma it needs or report too few
steps.

## Lean Export and Step Removal

`python/tolean.py` turns every step into an explicit proof term, so Lean checks
without searching and the file needs only core Lean.

- A step is accepted if it is one rewrite: one instance of one equation,
  applied to one or more occurrences of the same subterm, optionally followed
  by closing the goal with an instance of a second equation. That is the shape
  of a superposition inference.
- The converter finds the instance and the occurrences from the premises the
  step lists. If those do not suffice it tries the other equations proved so
  far and reports it.
- It prints how many steps rewrite a subterm and how many only instantiate an
  earlier equation, and notes steps that nothing depends on.
- A step that is not a single rewrite is left as `sorry` and the exit status is
  2. A file that Lean accepts without warnings therefore certifies the step
  count.

`python/compress.py` uses the same one-rewrite search, and no prover. It removes
a superposition line when every step that uses it can be derived in one rewrite
from the other equations instead, then removes the lines nothing needs any
more. Twee sections are left as they are. Example: in a 22-step proof of
650 ⇒ 448, one lemma is derived through three Vampire steps although it follows
in one rewrite from its neighbour and the axiom.
