# Finite Kakeya — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the three-dimensional one-pole Kakeya construction in Spotlight 1.

## Main result

`FiniteKakeyaInf.finite_kakeya_inf` proves that for every prime `p ≡ 3 (mod 4)` there is a Kakeya set in `𝔽_p³` of cardinality

```text
(2p³ + 7p² + 3) / 8.
```

## Source layout

- `FiniteKakeyaInf/Definitions.lean` — affine lines, Kakeya sets, body, and boundary.
- `FiniteKakeyaInf/Coverage.lean` — line coverage in every direction.
- `FiniteKakeyaInf/Counting.lean` — the exact cardinality calculation.
- `FiniteKakeyaInf/Main.lean` — the exported theorem.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/finite_kakeya/verification.ipynb`, Theorem 2.1.
