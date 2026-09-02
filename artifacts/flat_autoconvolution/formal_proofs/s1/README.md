# Flat autoconvolution — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the binary-step reduction for the
flat-autoconvolution supremum in Spotlight 1.

## Main results

```text
FlatAutoconvolutionS1.flat_autoconvolution_spotlight_one : C01 = C
FlatAutoconvolutionS1.flat_autoconvolution_spotlight_one_full :
  C01 = Cstep ∧ Cstep = C
```

Here `C`, `Cstep`, and `C01` are the suprema over admissible functions,
nonnegative equal-grid steps, and nonempty binary equal-grid steps.

## Source layout

- `FlatAutoconvolutionS1/Definitions.lean` — score and admissible classes.
- `FlatAutoconvolutionS1/StepDensity.lean` and `StepScoreDensity.lean` — analytic approximation.
- `FlatAutoconvolutionS1/BinaryRefinement.lean` through `BinaryStepDensity.lean` — binary refinement.
- `FlatAutoconvolutionS1/Main.lean` — exported theorems.

## Build

```bash
lake build
lake env lean Audit.lean
```

The project pins Lean `v4.26.0-rc2` and mathlib commit
`8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/flat_autoconvolution/verification.ipynb`, Theorem 2.1.
