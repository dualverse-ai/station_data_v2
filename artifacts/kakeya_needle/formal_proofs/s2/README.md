# Kakeya needle — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the exact global values at `n = 3` and `n = 4` in Spotlight 2.

## Main results

```text
KakeyaNeedleC3C4.C_T_three : C_T 3 = 5/18
KakeyaNeedleC3C4.C_T_four  : C_T 4 = 1/4
```

Here `C_T n` is the infimum of the Lebesgue area of the union of the notebook's `n` triangles over all horizontal offsets.

## Source layout

- `KakeyaNeedleC3C4/Definitions.lean` through `SweepCertificate.lean` — geometric reduction and exact sweeps.
- `KakeyaNeedleC3C4/FarkasChecker.lean` and `HandelmanChecker.lean` — rational certificate checkers.
- `KakeyaNeedleC3C4/Generated/` — exact certificate payloads.
- `KakeyaNeedleC3C4/CertificateAssembly.lean`, `Infimum.lean`, and `Main.lean` — global bounds and final equalities.
- `scripts/` — certificate regeneration tools.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/kakeya_needle/verification.ipynb`, Theorem 3.2.
