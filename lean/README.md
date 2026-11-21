# Lean proofs

Lean project used to check Krympa proofs. From this directory:

```bash
lake env lean Proof/<file>.lean
```

No output and exit status 0 means the proof is accepted.

## Files in `Proof/`

| File | Theorem | Notes |
|---|---|---|
| `proof.lean` | Equation650 ⇒ Equation448 | Krympa proof |
| `ts_proof.lean` | Equation650 ⇒ Equation448 | `--term-size` proof, 19 steps |
| `ts_proof_16.lean` | Equation650 ⇒ Equation448 | `--term-size --refine` proof, 16 steps |
| `secondproof.lean` | Equation947 ⇒ Equation3897 | Krympa proof |

These four use `nth_rw` and need Mathlib.

## Generated files

`./krympa lean <proof.out>` or a run with `--lean` writes
`Proof/<name>.lean` here and checks it. A generated file needs only core Lean:
every step is an explicit proof term, so Lean checks it in a few seconds
without searching. See the main `README.md`.
