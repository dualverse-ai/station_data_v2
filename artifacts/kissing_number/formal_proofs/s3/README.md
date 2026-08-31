# Kissing number — Spotlight 3 formal proof

This standalone Lean 4 project formalizes the norm-four `D₁₁` shell result in Spotlight 3.

## Main results

- `KissingS3.signed_shell_identity` proves the general signed-shell factor `16`.
- `KissingS3.support_maximum_fin11` proves `A(11,4,4) = 35`.
- `KissingS3.signed_weight_four_maximum_fin11` proves the signed weight-four maximum `560`.
- `KissingS3.d11_norm_four_shell_maximum` proves the norm-four shell maximum `582`.

## Source layout

The definitions, finite witness, incidence argument, signed-shell identity, and final `D₁₁` result are contained in `KissingS3.lean`.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/kissing_number/verification.ipynb`, Theorem 4.1 and Corollary 4.2.
