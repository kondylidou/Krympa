# Krympa

Krympa shortens equational proofs. It takes a proof found by Vampire and
rebuilds it from shorter pieces proved by Vampire and Twee. The method is
described in the paper:
[Tao’s Equational Proof Challenge Accepted](https://kondylidou.github.io/assets/pdf/paper3.pdf)

## Install

Krympa runs on Linux and macOS.

**1. Get the provers.** Krympa calls two provers, which you install yourself:

* [Vampire](https://github.com/vprover/vampire/releases): download an
  executable from the release page, or build it from source.
* [Twee](https://codeberg.org/nick8325/twee): download an executable, or
  install it with `cabal install twee`.

Krympa is tested with Vampire 4.8 and 5.0.1 and with Twee 2.4.2 and 2.6.2.

**2. Build Krympa.** This needs Rust (`cargo`) and OCaml with `dune`.

```bash
git clone https://github.com/kondylidou/Krympa.git
cd Krympa/rust
./build.sh
```

## Run

From `rust/`, tell Krympa where your provers are and give it a problem:

```bash
export VAMPIRE=/path/to/vampire
export TWEE=/path/to/twee

./krympa /path/to/problem.p
```

The problem is a TPTP file with equations as axioms and one equation as
conjecture, in `fof` form:

```
fof(a1, axiom, ! [X, Y, Z] : X = op(X,op(Y,op(op(Z,X),Y)))).
fof(goal, conjecture, ! [X, Y, Z] : X = op(X,op(Y,op(Z,op(X,Z))))).
```

Krympa reports its progress, then the number of steps of the shortened proof
(`Total steps`) and of Vampire's proof (`Initial proof steps`), and writes:

| File | Contents |
|---|---|
| `output/proof_<problem>.out` | The shortened proof. |
| `output/vampire_proof_<problem>.out` | The Vampire proof it started from. |

The exit status is 0 if a shortened proof was written.

Krympa has to be started from `rust/`. It keeps its working files in `output/`,
`lemmas/` and `proofs/` next to `rust/`; the last two are overwritten by every
run.

## Options

`./krympa [options] <problem.p>`

| Option | Effect |
|---|---|
| `--direct` | Prove only the lemmas the search can use, instead of every lemma of the Vampire proof. Usually finds the same proof in less time. |
| `--lean` | Write the shortened proof as a Lean file and have Lean check it; see below. |
| `--term-size` | Prefer proofs with smaller terms; see below. |
| `--refine` | Run a final refinement on the best proof; see below. |
| `--vampire <exe>`, `--twee <exe>` | The prover executables. Same as the variables `VAMPIRE` and `TWEE`, and take precedence over them. |
| `--sequential` | One prover call at a time instead of several in parallel. |
| `--debug` | Print a full trace instead of the progress messages. |

| Variable | Effect |
|---|---|
| `VAMPIRE`, `TWEE` | The prover executables. |
| `VAMPIRE_OPTIONS`, `TWEE_OPTIONS` | Extra options for every call of that prover, e.g. `VAMPIRE_OPTIONS="-sa discount"`. |
| `KRYMPA_LOG` | How much is printed: `error`, `warn`, `info` (default) or `debug` (same as `--debug`). |

If you name no executable, Krympa uses the copy in `bin/` and, if there is
none, looks for `vampire` and `twee` on your `PATH`.

### `--lean`

Writes the proof to `lean/Proof/proof_<problem>.lean`, runs Lean on it and
reports whether Lean accepted it; the exit status is 0 only if it did. Every
step is translated to an explicit proof term, so an accepted file certifies the
proof and its number of steps.

This needs Python 3 and Lean 4, and works for problems over one binary
operation named `op`, as in the example above.

For such problems, `python3 ../python/compress.py <proof.out>` removes the
steps of a proof that can be bypassed with a single rewrite and writes
`<proof>_compressed.out`.

### `--term-size`

Prefers a proof with smaller terms over a slightly shorter one: when two proofs
of the same goal are available, the one with the smaller average term size is
taken if it is at most 1.5 times as long. Term size counts the occurrences of
`op`, so this option too is meant for problems over one operation `op`.

### `--refine`

Runs a final refinement on the best proof, contributed by Benjamin Przybocki.
It splits out the internal lemma of the last Twee subproof, merges two
consecutive rewrites by the same lemma into one superposition step, and accepts
a derived equation that is more general than the lemma asked for. The refined
proof is kept only if it has fewer steps. On `Equation650_implies_Equation448`
it saves three steps (`lean/Proof/ts_proof_16.lean`).

## Benchmarks and Development

`DEVELOPERS.md` describes the benchmark problems and the scripts that run
them, how to run one phase of Krympa at a time, and the internals.

## Contributing

If you want to propose changes, fixes, or new features:

1. Open an issue describing your suggestion or bug.
2. Submit a pull request referencing the issue.
3. All contributions will be reviewed before merging.

Direct forks or redistribution of modified versions are not allowed.
