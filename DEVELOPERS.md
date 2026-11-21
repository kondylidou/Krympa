# Developers Guide

## Repo Layout

- `rust/` — main Krympa implementation and binaries
- `shell/` — helper scripts for running one problem or the full benchmark suite
- `python/` — input generation, log summary, step removal (`compress.py`) and Lean export (`tolean.py`)
- `lean/` — Lean project used to check exported proofs
- `benchmarks/` — Lean benchmark files and generated benchmark inputs
- `ocaml/` — lemma extractor / parser support

## Build

From `rust/`:

```bash
./build.sh
```

Produces `rust/krympa` and `rust/benchmarking_binary` as optimized (release)
builds. The build also compiles the OCaml lemma extractor, so `dune` must be
installed.

## Execution Modes

The `krympa` binary accepts `--sequential` or `--parallel` before the subcommand.
Default when neither flag is given is `--parallel`.

```bash
./krympa --parallel collect <input-file>
./krympa --sequential collect <input-file>
```

Use `--sequential` when debugging to get deterministic, interleaved-free log output.

The shell scripts `run_one` and `run` always run in parallel mode — they do not accept or forward execution mode flags.

## Term-Size Proof Selection

`--term-size` extends proof selection: a proof with lower average term size is
preferred when its step count is within 1.5× of the shorter proof's step count.
Strictly fewer steps still always wins.

```bash
./krympa --term-size minimize <input-file>
./krympa --sequential --term-size minimize <input-file>
./krympa --term-size direct <input-file>
```

With `--term-size`, `minimize` and `direct` also run the final refinement pass
on their best proof (described in `README.md`).

## Direct: the Pipeline Without Proving Every Lemma

`collect` proves every lemma of the Vampire proof in three variants with two
provers. `minimize` then only looks at the lemmas it can reach from its arrival
candidates. `direct` proves exactly those lemmas and nothing else:

```bash
./krympa run_vampire "$INPUT"
./krympa direct "$INPUT"
```

1. The lemma problems are written in all three variants, as in `collect`, but
   not proved.
2. The arrival candidates of `minimize` are proved: going back from the end of
   the proof, the first 5 lemmas that have no Skolem constant and a proof.
3. For each proved lemma, the Twee proof of its kept variant is read, and the
   lemmas it cites are proved next. This repeats until nothing new turns up.
4. `shorten` and `minimize` run unchanged on what was proved.

A lemma that is proved is treated as in `collect`: big-step, small-step and
abstracted, Vampire and Twee, shortest proof kept. "Cites" is the dependency
`minimize` builds its graph from. So the segmentation, the departure and arrival
candidates, `--term-size` and the final refinement are those of the pipeline;
the only number involved is the 5 arrival candidates it already had.

One difference remains. `minimize` redirects a lemma that also occurs as an
internal lemma of some Twee proof. `direct` only knows the Twee proofs it made,
so it can redirect differently and end up with other departure candidates.

Same Vampire proof for both, default prover options, macOS binaries, 2026-11-21.
Lean accepts all of these proofs.

| Problem | Lemmas | Proved by `direct` | Pipeline steps | `direct` steps | Pipeline time | `direct` time | Same proof |
|---|---|---|---|---|---|---|---|
| 650 ⇒ 448 | 81 | 42 | 26 | 26 | 187 s | 122 s | yes |
| 650 ⇒ 448, 62-step Vampire proof | 62 | 28 | 22 | 20 | 172 s | 150 s | no |
| 723 ⇒ 872 | 179 | 44 | 15 | 15 | 357 s | 149 s | yes |
| 947 ⇒ 3897 | 126 | 32 | 15 | 15 | 308 s | 177 s | yes |
| 2055 ⇒ 2656 | 79 | 41 | 15 | 15 | 150 s | 113 s | yes |
| 1560 ⇒ 960 | 53 | 31 | 15 | 15 | 99 s | 70 s | yes |
| 2789 ⇒ 895 | 66 | 16 | 15 | 9 | 104 s | 37 s | no |
| 2860 ⇒ 2660 | 49 | 31 | 17 | 17 | 71 s | 60 s | yes |
| 3569 ⇒ 3957 | 68 | 30 | 18 | 18 | 35 s | 45 s | yes |
| 3971 ⇒ 3347 | 84 | 27 | 19 | 19 | 26 s | 11 s | no |

On eight small problems (1 to 19 lemmas) the two give the same step count seven
times and `direct` is one step shorter once.

## Turning a Vampire Proof Around

Vampire proves by refutation: the end of its proof rewrites the negated goal
until it is contradictory. `proof_turnaround.rs` turns that end around so that
it reads as a derivation of the goal. Two things matter there.

- Each turned line must list the equation it is derived with. In the
  refutation, step i+1 follows from step i and an equation E; read forwards, the
  statement of step i follows from the statement of step i+1 and E. So E belongs
  to the line of step i, not of step i+1.
- A clause of the refutation can have variables of its own. Negated, it is an
  existential statement ("there is an X with ..."), and it is printed with `?`.
  Such a line is counted as a step but is not a lemma: no lemma problem is
  written for it and the Lean export skips it.

Before 2026-11-21 both were wrong: equations sat one line off, and existential
statements were printed as ordinary equations, with Skolem constants sometimes
renamed to a variable the clause already had. A proof could then lose a lemma
it needs, or contain a goal "derived" from nothing, and report too few steps.
Three of the ten proofs above were affected (723 ⇒ 872 was reported as 9 steps,
2860 ⇒ 2660 as 6, 3569 ⇒ 3957 as 17) and Lean rejected them.

## Removing Avoidable Steps

```bash
python3 ../python/compress.py ../output/proof_<name>.out
python3 ../python/tolean.py ../output/proof_<name>_compressed.out
```

The first segment is copied from the Vampire proof, and Vampire often reaches an
equation by a detour. `compress.py` removes a superposition line when every step
that uses it can be derived in one rewrite from the other equations instead, and
then removes the lines nothing needs any more. It calls no prover: it uses the
one-rewrite search of `tolean.py`. Twee rewrite chains are left as they are. It
works on the output of `minimize` and of `direct`.

Example: in the 22-step proof of 650 ⇒ 448, one lemma is derived through three
Vampire steps although it follows in one rewrite from its neighbour and the
axiom. Removing that detour, and one more line, gives 18 steps.

## Prover Options

`KRYMPA_VAMPIRE_OPTIONS` and `KRYMPA_TWEE_OPTIONS` add options to every call of
that prover, in every phase. Unset, the provers run as before.

```bash
KRYMPA_VAMPIRE_OPTIONS="-sa discount" ./krympa run_vampire "$INPUT"
KRYMPA_VAMPIRE_OPTIONS="-sa discount" ./krympa direct "$INPUT"
```

Set the same value for all phases of one run. Vampire's default strategy
(`lrs`) depends on elapsed time, so the same problem can give different proofs
on a loaded machine; `-sa discount` does not have this problem.

## Logging

Controlled by `KRYMPA_LOG`:

```bash
KRYMPA_LOG=debug ./krympa --sequential minimize <input-file>
```

- default / `info` — high-level progress only
- `debug` — full per-lemma trace

## Pipeline Steps

Run from `rust/` with a single input file:

```
run_vampire  →  collect  →  shorten  →  minimize
```

Optional analysis step: `group`.

Alternative that proves fewer lemmas: `run_vampire → direct`, see above.

### Manual run (parallel, default)

```bash
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p

./krympa run_vampire "$INPUT"
./krympa collect "$INPUT"
./krympa shorten "$INPUT"
./krympa minimize "$INPUT"
```

### Manual run (sequential, with debug logging)

```bash
INPUT=../benchmarks/input11/Equation650_implies_Equation448.p

KRYMPA_LOG=debug ./krympa --sequential run_vampire "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential collect "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential shorten "$INPUT"
KRYMPA_LOG=debug ./krympa --sequential minimize "$INPUT"
```

## Run One Problem End-to-End

From `shell/`:

```bash
./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

Always runs parallel. Generates inputs from the corresponding `.lean` file before running. For debug output, use the manual pipeline with `--sequential` and `KRYMPA_LOG=debug` instead.

## Run the Full Benchmark Suite

From `shell/`:

```bash
./run           # default 600s per problem
./run 200       # custom timeout
```

Always runs parallel. Generates inputs for all `Proofs*.lean` files before running each. The first argument is the per-problem timeout in seconds (default 600). Logs are written to `benchmarks/output_logs/`. For debug output on a single problem, use the manual pipeline with `--sequential` and `KRYMPA_LOG=debug` instead.

## Generate Benchmark Inputs

From `shell/`:

```bash
python3 ../python/generate_input.py ../benchmarks/Proofs11.lean
```

Produces `../benchmarks/input11/`.

## Pre-commit Check

From `rust/`:

```bash
cargo fmt
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test
```

CI runs these three checks and fails on any formatting difference or clippy
warning. It uses the latest stable Rust, so a newer clippy there can flag code
that passes locally; `rustup update stable` avoids the surprise.

## Clean Build Artifacts

From the repo root:

```bash
git clean -nd rust/target ocaml/_build   # preview
git clean -fd rust/target ocaml/_build   # actually remove
```
