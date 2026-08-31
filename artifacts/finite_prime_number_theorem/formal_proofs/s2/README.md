# Finite prime number theorem — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the direct Möbius-cutoff obstruction in Spotlight 2.

## Main results

- `PrimeS2.mobius_cutoff_primeBand_obstruction` proves the exact finite reflection and prime-band obstruction.
- `PrimeS2.mobius_cutoff_spotlight2` derives the displayed asymptotic conclusions from the classical analytic estimates used in the notebook.

## Source layout

- `PrimeS2/Definitions.lean` — cutoff weights and notebook quantities.
- `PrimeS2/Reflection.lean` — reflection and obstruction identities.
- `PrimeS2/FloorSum.lean` — balance and floor-sum equivalence.
- `PrimeS2/PrimeBand.lean` — prime-band evaluation.
- `PrimeS2/Analytic.lean` — analytic interface.
- `PrimeS2/Main.lean` — exported theorems.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/finite_prime_number_theorem/verification.ipynb`, Theorem 3.1.
