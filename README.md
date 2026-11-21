# Krympa

Krympa shortens equational proofs. It takes a proof found by Vampire and
rebuilds it from shorter pieces proved by Vampire and Twee. The method is
described in the paper:
[Tao’s Equational Proof Challenge Accepted](https://kondylidou.github.io/assets/pdf/paper3.pdf)

## Requirements

* Linux or macOS.
* Vampire and Twee. Binaries for both systems are in `bin/`; to use your own, see
  [Provers](#provers).
* Python 3.
* Rust and OCaml (`dune`), to build the tool. Build details and internals are in
  `DEVELOPERS.md`.
* Lean 4, only if you want the proofs checked.

## Usage

Build once, then work from `shell/`:

```bash
cd rust && ./build.sh
cd ../shell
```

Generate the problems of a benchmark file. `Proofs11.lean` becomes
`benchmarks/input11/`, one `.p` file per problem:

```bash
python3 ../python/generate_input.py ../benchmarks/Proofs11.lean
```

Run one problem and check the result in Lean:

```bash
./run_checked ../benchmarks/input11/Equation650_implies_Equation448.p
```

Run one problem without Lean:

```bash
./run_one ../benchmarks/input11/Equation650_implies_Equation448.p
```

Run every problem of every `benchmarks/Proofs*.lean` (inputs are generated
automatically, logs go to `benchmarks/output_logs/`):

```bash
./run 600
python3 ../python/summarize.py ../benchmarks/output_logs
```

The shortened proof is written to `output/proof_<problem>.out`, the Vampire
proof it started from to `output/vampire_proof_<problem>.out`.

## Options

### Scripts

| Script | Arguments |
|---|---|
| `./run_checked [--direct] [--term-size] <problem.p>` | `--direct` and `--term-size` are explained below. Prints the step count and whether Lean accepted the proof, before and after removing avoidable steps. Exit status 0 only if Lean accepted both. |
| `./run_one <problem.p> [binary]` | `binary`: which Krympa binary to use (default `./krympa`). |
| `./run [timeout] [binary]` | `timeout`: seconds per problem (default 600). `binary` as above. |

Besides `krympa`, `rust/` holds older Linux binaries that use only some of the
lemma variants: `krympa_bs`, `krympa_sa`, `krympa_ba`, `krympa_bsa` (b =
big-step, s = small-step, a = abstracted). They lack `--term-size`, `direct`
and the environment variables.

### `--direct`

By default Krympa first proves every lemma of the Vampire proof. With
`--direct` it proves only the lemmas the search can actually use. The result is
of the same kind, usually the same proof, and it usually takes less time.

### `--term-size`

Prefers a proof with smaller terms over a slightly shorter one: when two proofs
of the same goal are available, the one with the smaller average term size is
taken if it is at most 1.5 times as long.

With this flag Krympa also runs a final refinement on its best proof,
contributed by Benjamin Przybocki. It splits out the internal lemma of the last
Twee subproof, merges two consecutive rewrites by the same lemma into one
superposition step, and accepts a derived equation that is more general than the
lemma asked for. The refined proof is kept only if it has fewer steps. On
`Equation650_implies_Equation448` it saves three steps
(`lean/Proof/ts_proof_16.lean`).

### Provers

| Variable | Effect |
|---|---|
| `VAMPIRE`, `TWEE` | The prover executables to use. |
| `VAMPIRE_OPTIONS`, `TWEE_OPTIONS` | Extra options for every call of that prover, e.g. `"-sa discount"`. |

```bash
VAMPIRE=/opt/vampire/vampire ./run_checked --direct <problem.p>
VAMPIRE_OPTIONS="-sa discount" ./run_checked --direct <problem.p>
```

Without `VAMPIRE` or `TWEE`, the copy in `bin/` is used; if there
is none, `vampire` and `twee` are looked up on your `PATH`. So `bin/` is not
needed when the provers are installed elsewhere.

### Logging

`KRYMPA_LOG=debug` gives a full trace instead of progress messages.

### Running the commands yourself

The scripts call `rust/krympa <flags> <command> <problem.p>`. Run from `rust/`,
flags before the command:

| Command | Does |
|---|---|
| `run_vampire` | Proves the problem with Vampire; its derived equations are the lemmas. |
| `collect` | Proves every lemma, in three variants, with both provers. |
| `shorten` | Proves some lemmas again from simpler statements. |
| `minimize` | Searches for the shortest proof and writes it. |
| `direct` | Does the work of `collect`, `shorten` and `minimize`, proving only the lemmas needed. |
| `group` | Optional analysis: groups the lemmas by the axioms their proofs use. |

| Flag | Effect |
|---|---|
| `--parallel` (default) / `--sequential` | Prover calls in parallel, or one at a time. |
| `--term-size` | As above; used by `minimize` and `direct`. |
| `--vampire <exe>`, `--twee <exe>` | The prover executables; same as `VAMPIRE` and `TWEE`, and take precedence over them. |

## Tools

| Tool | Use |
|---|---|
| `python3 ../python/tolean.py <proof.out>` | Writes the proof as `lean/Proof/<proof>.lean`. Check it with `cd ../lean && lean Proof/<proof>.lean`. |
| `python3 ../python/compress.py <proof.out>` | Removes steps that can be bypassed with a single rewrite; writes `<proof>_compressed.out`. |

`run_checked` runs both for you.

## Contributing

If you want to propose changes, fixes, or new features:

1. Open an issue describing your suggestion or bug.
2. Submit a pull request referencing the issue.
3. All contributions will be reviewed before merging.

Direct forks or redistribution of modified versions are not allowed.
