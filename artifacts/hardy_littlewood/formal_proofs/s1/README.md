# Hardy–Littlewood — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the sharp non-tangential plateau in Spotlight 1.

## Main result

`HardyLittlewoodS1.spotlight_one_sharp_nontangential_plateau` proves

```text
C_α = 2  for  1/3 ≤ α ≤ 1.
```

The formal definition uses the one-dimensional non-tangential maximal operator on measurable nonnegative finite-mass functions.

## Source layout

- `HardyLittlewoodS1/Definitions.lean` — maximal operator and sharp constant.
- `HardyLittlewoodS1/IntervalCover.lean` — interval-cover multiplicity theorem.
- `HardyLittlewoodS1/UpperBound.lean` — the upper estimate.
- `HardyLittlewoodS1/LowerBound.lean` — equal-chain witnesses and lower estimate.
- `HardyLittlewoodS1/Main.lean` — the exported theorem.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/hardy_littlewood/verification.ipynb`, Theorem 2.5.
