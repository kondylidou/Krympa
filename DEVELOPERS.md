# Developers Guide

How to install and use Krympa is in `README.md`, the method in the paper. This
file is for working on the code and for running the benchmarks.

## Build and Checks

```bash
./build.sh                      # optimized krympa and benchmarking_binary
cargo fmt
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test
```

- The build also compiles the OCaml extractor into `ocaml_install/tptp_parser`,
  so `dune` must be installed.
- The two binaries and `tptp_parser` are tracked by git; a build shows up in
  `git status`. `Cargo.lock` is tracked too, so everyone builds with the same
  versions of the dependencies.
- CI runs the three `cargo` checks and fails on any formatting difference or
  clippy warning. It uses the latest stable Rust, so its clippy can flag code
  that passes locally; `rustup update stable` avoids that.
- Remove build artifacts with `git clean -fdX target ocaml/_build` (they are
  ignored files, so `-X` is needed).

## Where Things Are

| Path | Contents |
|---|---|
| `src/main.rs`, `execution.rs` | Command line: the whole run, the single phases, the flags; the Krympa folder. |
| `src/logging.rs` | Message levels: `klog_info!` is what a user sees, `klog_debug!` only with `--debug`. |
| `src/problem.rs` | Reading the input problem. A `cnf` problem (unit clauses, goal negated) is rewritten to `fof` form in `output/input_problem_<name>.p`; `include` is rejected. |
| `src/provers.rs` | Every call of Twee and Vampire, where their executables come from, proof length, term size. |
| `src/proof_turnaround.rs` | Turning Vampire's refutation into a forward proof. |
| `src/collect.rs` | `collect`, `shorten`, `group`. |
| `src/direct.rs` | `direct`: collecting only the lemmas that are needed. |
| `src/minimize.rs` | `minimize`: the search over arrival and departure lemmas. |
| `src/prove.rs` | Proving one goal with both provers and choosing between the two proofs. |
| `src/trim.rs` | Dropping the parts of a segment that later segments do not use. |
| `src/refine.rs` | The final refinement. |
| `src/proof_file.rs` | Reading a proof file written by `minimize`. |
| `src/rewrite.rs` | Terms over `op` and the search that justifies an equation by one rewrite. |
| `src/lean.rs` | `--lean` and `krympa lean`: the Lean export, then Lean. |
| `src/compress.rs` | Step removal: at the end of a whole run, and `krympa compress`. |
| `src/superpose.rs` | Reading a turned Vampire proof and writing the steps a goal needs as a block of lines. |
| `src/dag.rs` | Dependencies between lemmas, read from the Twee proofs, and the graph built from them. |
| `src/utils.rs`, `regex_cache.rs` | Lemma files, TPTP editing, temporary problem files; compiled regexes are kept for reuse. |
| `src/alpha_match.rs` | Equality of formulas up to renaming and orientation. |
| `src/bench_run.rs`, `src/bin/benchmarking.rs` | The benchmarks: problems from the benchmark files, the driver behind `benchmarks/run`, the summary of its logs. |
| `tests/` | One test file per topic. |
| `ocaml/` | Lemma extractor: writes the lemma problems of a Vampire proof in the three variants. |
| `benchmarks/` | The benchmark files, their equations, and the scripts `run` and `run_checked`. |
| `lean/` | Lean project for checking exported proofs. |
| `bin/` | Your own `vampire` and `twee` for your system, if you put them there; ignored by git. |

At start, Krympa changes into the Krympa folder: the nearest folder above its
executable that holds `ocaml_install/tptp_parser` (`krympa_home`). All paths in
the code are relative to it; paths the user gives are resolved against the
folder Krympa was started from (`absolute`). Working directories there, ignored
by git:

| Directory | Contents |
|---|---|
| `output/` | `vampire_proof_<name>.out`, `summary_<name>.json` (kept proof per lemma), `proof_<name>.out`, and the graph and lemmas of the chosen arrival lemma. |
| `lemmas/` | Lemma problems in `big-step/`, `small-step/`, `abstracted/`; temporary problems in `tmp/`. |
| `proofs/` | The kept proof of each lemma; every proof found, in `vampire_tmp/` and `twee_tmp/`. |
| `tmp/` | Proofs made by `shorten`, which are then copied to `proofs/`. |

## The Phases

`./krympa <problem.p>` runs `run_vampire`, `collect`, `shorten` and `minimize`
in turn; with `--direct` it runs `run_vampire` and `direct`. Each phase can
also be run on its own and reads what the previous one wrote. A step is one
Twee rewrite or one Vampire inference.

```bash
./benchmarking_binary generate benchmarks/Proofs11.lean   # writes benchmarks/input11/
INPUT=benchmarks/input11/Equation650_implies_Equation448.p
./krympa run_vampire "$INPUT"
./krympa collect "$INPUT"
./krympa shorten "$INPUT"
./krympa minimize "$INPUT"      # or, instead of the last three: ./krympa direct "$INPUT"
```

`--term-size` and `--refine` are read by `minimize` and `direct`; `--direct`,
`--no-compress` and `--lean` only go with a whole run, which removes avoidable
steps at the end unless told not to. A phase that fails exits
with a non-zero status. `./krympa lean <proof.out>` and
`./krympa compress <proof.out>` work on a proof file instead; see
[Lean Export and Step Removal](#lean-export-and-step-removal).

| Phase | What it does |
|---|---|
| `run_vampire` | Proves the problem with Vampire and turns the refutation into a forward proof. The equations it derives are the lemmas, numbered in order. |
| `collect` | Proves every lemma in three variants with Vampire and Twee (7 s per call) and keeps the shortest proof. Big-step: from the axioms. Small-step: from the axioms and all earlier lemmas. Abstracted: from the axioms, with one subterm of the lemma replaced by a variable. |
| `shorten` | Proves small-step lemmas again, using the abstracted statement of an earlier lemma where that variant was kept. |
| `minimize` | Tries each of the last 5 lemmas as arrival lemma and, for each, the lemmas its proof depends on as departure lemma. The proof then has three segments: axioms to departure lemma, departure to arrival lemma, arrival lemma to conjecture. The first is taken from the Vampire proof, the other two are proved again by both provers. The combination with the fewest steps is written out. |
| `direct` | Replaces `collect`, `shorten` and `minimize`; see below. |
| `group` | Optional analysis: groups the lemmas by the axioms their proofs use, in `output/structural_groups.txt`. |

For debugging use `./krympa --debug --sequential <phase> "$INPUT"`: one prover
call at a time and a readable trace. A message that only helps debugging should
be a `klog_debug!`; the default output is meant to stay at a few lines per run.

Things to know:

- Dependencies between lemmas are read from the Twee proof of the kept variant:
  the lemmas it cites as axioms.
- Inside `minimize`, Twee is stopped after 7 s but Vampire runs until its own
  limit of 60 s (`run_vampire_turned` against `run_vampire_limited`).
- Vampire's default strategy (`lrs`) depends on elapsed time, so the same
  problem can give different proofs on a loaded machine. Setting
  `VAMPIRE_OPTIONS="-sa discount"` for all commands of a run avoids this.

## Scripts and Benchmarks

The benchmarks are the files `benchmarks/Proofs*.lean`, with the equations in
`benchmarks/Equations/`. From `benchmarks/`:

| Command | Does |
|---|---|
| `../benchmarking_binary generate Proofs11.lean` | Writes the problems of one benchmark file to `input11/`, one `.p` file each. |
| `./run_checked [--direct] [--term-size] [--refine] <problem.p>` | Runs Krympa, checks the proof in Lean, removes avoidable steps and checks again. Exit status 0 only if Lean accepted both. |
| `./run [timeout] [binary]` | Generates the problems of every benchmark file and runs the four phases on each, with a limit of `timeout` seconds per phase (default 600) and the given Krympa binary (default `../krympa`). Logs go to `output_logs/`; at the end it prints their summary. |
| `../benchmarking_binary summarize output_logs` | The summary: per benchmark file and overall, the average number of steps of Vampire's and Krympa's proofs, for all problems and for those whose Vampire proof has at least 15 steps. |

`run` reads the line `[RESULT] Total steps:` from Krympa's output, so that line
must keep its wording. The older Linux binaries that use only some of the lemma
variants (`krympa_bs`, `krympa_sa`, `krympa_ba`, `krympa_bsa`; b = big-step,
s = small-step, a = abstracted) are in the git history, up to commit `308f3c2`.
They expect the earlier layout, with the code in `rust/`.

How the averages are counted: where Krympa found no proof, or a longer one than
Vampire's, the problem counts with Vampire's proof. A problem where a phase ran
out of time is left out.

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

The lines of a block are written by `prepend_superposition_steps` in
dependency order, not in Vampire's numbering: a turned refutation keeps
Vampire's numbers, so a turned step can use a step with a higher number. Steps
that state the same equation (up to renaming of variables and orientation)
share one name and are written once, the first in dependency order, which is
the one with a derivation. In a block from a Vampire proof made inside
`minimize`, the step stating the segment's goal is named after the goal, and a
step that only restates one of its own premises (the turned end of a
refutation often starts like that) is not written; the steps that use it cite
the premise. Existential statements are only equal if they are
the same up to renaming, existential variables to existential ones
(`formulas_match`). A lemma proof that `collect` stored as Vampire printed it
is turned around before its steps are copied.

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
candidates, `--term-size` and `--refine` are those of the pipeline.
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

With `--refine`, the final refinement (`refine_final_proof`) runs once on the
best proof, with or without `--term-size`. It needs a last Twee section with
exactly one internal lemma, followed by a block of superposition lines;
otherwise it does nothing. A merged step is accepted only if Vampire's proof of
it has exactly one rewriting inference and otherwise only rules from a fixed
list (`is_single_rewrite_refutation`).

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
  but is not a lemma: no lemma problem is written for it.

If either is violated, a proof can lose a lemma it needs or report too few
steps.

## Lean Export and Step Removal

`./krympa lean <proof.out>` writes `lean/Proof/<proof>.lean` and runs `lean` on
it in `lean/`; `--lean` does the same at the end of a run. The translation is
one to one: every step of the proof file becomes one `have` with an explicit
proof term, nothing is added or merged, so Lean checks without searching and
the file needs only core Lean. Terms over one binary operation `op` only.

- A step is accepted if it is one rewrite: one instance of one equation,
  applied to one or more occurrences of the same subterm, optionally followed
  by closing the goal with an instance of a second equation. That is the shape
  of a superposition inference.
- The converter finds the instance and the occurrences from the premises the
  step lists. If those do not suffice it tries the other equations proved so
  far and reports it. When the rewritten subterm occurs often and only some
  occurrences are rewritten, the positions are found by matching the goal
  against the second equation directly (`match_rewritten`).
- It prints how many steps rewrite a subterm and how many only instantiate an
  earlier equation, and notes steps that nothing depends on.
- A step that is not a single rewrite is left as `sorry`, and Lean is not run.
  A file that Lean accepts without a message therefore certifies the step
  count.
- An existential step `∀ u, ∃ w, s = t` (see above) is proved as
  `⟨term, proof⟩`: the witness term is found by unification, then the instance
  is checked as one rewrite. A step that uses an existential statement first
  picks its witness, `match e u with | ⟨w, h⟩ => ..`, and uses `h` as an
  equation, with one instance only. If an existential step cannot be
  translated it is left out, and a step that needs it fails.

`./krympa compress <proof.out>` writes `<proof>_compressed.out`; a whole run
replaces its proof this way unless `--no-compress` is given. The benchmark
driver runs the phases one by one, so its step counts are without it. It uses the same one-rewrite search, and no
prover. It removes a superposition line when every step that uses it can be
derived in one rewrite from the other equations instead, then removes the lines
nothing needs any more. Twee sections are left as they are. The result is
translated once more and kept only if every step still checks. Example: in a
22-step proof of 650 ⇒ 448, one lemma is derived through three Vampire steps
although it follows in one rewrite from its neighbour and the axiom.
