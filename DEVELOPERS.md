# Developers Guide

## Repo Layout

- `rust/` — main Krympa implementation and binaries
- `shell/` — helper scripts for running one problem or the full benchmark suite
- `python/` — input-generation and output-conversion helpers
- `benchmarks/` — Lean benchmark files and generated benchmark inputs
- `ocaml/` — lemma extractor / parser support

## Build

From `rust/`:

```bash
./build.sh
```

Produces `rust/krympa` and `rust/benchmarking_binary`.

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
```

## Direct Minimization (without `collect`)

`collect` proves every lemma of the Vampire proof six times (three problem
variants, two provers) to learn which lemmas can be reached from which, and
`minimize` uses that to choose a departure and an arrival lemma. `direct` builds
the same three segments but needs only the Vampire proof:

```bash
./krympa run_vampire "$INPUT"
./krympa direct "$INPUT"
```

The three segments are the ones of `minimize`:

1. axioms → departure lemma: Vampire's own derivation, taken as it is;
2. departure lemma → arrival lemma: proved again by Twee and Vampire;
3. arrival lemma → conjecture: proved again by Twee and Vampire.

How they are found without proving any lemma first:

1. Every equation Vampire derived is tried as departure lemma of a proof with
   two segments: its derivation, then the conjecture proved from it. Equations
   derived from the negated conjecture are excluded, so the conjecture cannot
   be used to prove itself.
2. The 15 departures that did best are combined with each of the last 5
   equations of the Vampire proof as arrival lemma.
3. For the 10 best combinations the last segment is proved once more with every
   equation of the first two segments available.
4. In every candidate, lines of an earlier segment that the later ones do not
   use are dropped. The candidate with the fewest steps is written to
   `../output/proof_<name>.out` in the format of `minimize`.

`direct` has no problem variants (big-step, small-step, abstracted): those are
the questions `collect` asks about each lemma, and `direct` asks none.
`--term-size` works as in `minimize`: it steers each choice between a Twee and a
Vampire proof, and the final refinement pass runs on the best proof.

Steps, all results checked in Lean (default prover options, macOS binaries,
2026-11-20). "+ compress" is the result after `python/compress.py`, see below.

| Problem | Vampire | `minimize` | + compress | `direct` | + compress |
|---|---|---|---|---|---|
| 650 ⇒ 448 | 82 | 26 (29 in another run) | 19 | 22 | 18 |
| 650 ⇒ 448, from the 62-step Vampire proof | 62 | 22 | 18 | 22 | 18 |
| same, `--term-size` with final refinement | 62 | 19 | 16 | 19 | 16 |
| 470 ⇒ 3177 | 19 | 10 | 9 | 8 | 8 |
| 524 ⇒ 608 | 8 | 6 | 5 | 5 | 5 |
| 4514 ⇒ 4518 | 8 | 7 | 7 | 6 | 6 |
| 451 ⇒ 460 | 3 | 4 | 4 | 3 | 3 |
| 487 ⇒ 463 | 3 | 4 | 4 | 3 | 2 |
| 635 ⇒ 852 | 2 | 3 | 3 | 2 | 2 |
| 500 ⇒ 528 | 3 | 3 | 3 | 3 | 3 |
| 547 ⇒ 691 | 6 | 3 | 3 | 3 | 3 |

On 650 ⇒ 448 `direct` takes 50 to 60 s; `collect`, `shorten` and `minimize`
together take 145 to 180 s. From the 62-step proof `direct` picks the same
departure and arrival lemma as `minimize`.

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
cargo build
cargo test
```

CI enforces formatting — always run `cargo fmt` before committing.

## Clean Build Artifacts

From the repo root:

```bash
git clean -nd rust/target ocaml/_build   # preview
git clean -fd rust/target ocaml/_build   # actually remove
```
