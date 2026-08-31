# Finite Kakeya — Spotlight 3 formal proof

This standalone Lean 4 project formalizes the uniform boundary-penalty theorem for the nondegenerate one-pole family in Spotlight 3.

## Main result

`FiniteKakeyaS3.finite_kakeya_s3` proves the explicit estimate

```text
|boundaryPenalty - 3p²/8| < 5p
```

for every odd prime and every nondegenerate member of the family.

## Source layout

- `FiniteKakeyaS3/Definitions.lean` — footprints, lines, unions, and penalty.
- `FiniteKakeyaS3/Geometry.lean` and `Character.lean` — geometric and character identities.
- `FiniteKakeyaS3/Selector.lean`, `MixedSums.lean`, and `Overlap.lean` — counting estimates.
- `FiniteKakeyaS3/Penalty.lean` — boundary cardinality bookkeeping.
- `FiniteKakeyaS3/Main.lean` — the exported theorem.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/finite_kakeya/verification.ipynb`, Theorem 4.1.
