# Kakeya needle — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the exact minima for `n = 3, 4`
and the reflection-fixed `n = 5` result in Spotlight 2.

## Main results

```text
KakeyaNeedleC3C4.C_T_three : C_T 3 = 5/18
KakeyaNeedleC3C4.C_T_four : C_T 4 = 1/4
KakeyaNeedleC3C4.theorem_3_5_reflection_fixed_minimum :
  IsLeast reflectionFixedAreas5 (7/30)
KakeyaNeedleC3C4.proposition_3_6_asymmetric_witness :
  unionArea 5 witnessAsym5 = 14/61 ∧ ¬ ReflectionFixed5 witnessAsym5
KakeyaNeedleC3C4.corollary_3_7_forced_symmetry_breaking :
  IsGlobalMinimizer5 x → ¬ ReflectionFixed5 x
```

Here `C_T n` is the infimum of the Lebesgue area of the union of the
notebook's `n` triangles over all horizontal offsets. The unrestricted value
`C_T 5` remains open and is not stated.

## Source layout

- `KakeyaNeedleC3C4/Definitions.lean` through `SweepCertificate.lean` — geometric reduction and exact sweeps.
- `KakeyaNeedleC3C4/FarkasChecker.lean` and `HandelmanChecker.lean` — rational certificate checkers.
- `KakeyaNeedleC3C4/Generated/` — exact certificate payloads.
- `KakeyaNeedleC3C4/CertificateAssembly.lean`, `Infimum.lean`, and `Main.lean` — global bounds and final equalities.
- `KakeyaNeedleC3C4/ReflectionFive.lean` — the reflection-fixed `n = 5` results.
- `scripts/` — certificate regeneration tools.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit
`8f62007a980111b87be592665493301acbb05ea4`.
The exact certificate checks use `native_decide`.
`KakeyaNeedleC3C4/Generated/certificate5.b64` has SHA-256
`56bb777481a7639a0ee2efd1c36f4d914e47b23dd6ce4f12e7388b8c5b4fd008`.

## Source correspondence

- Notebook: `artifacts/kakeya_needle/verification.ipynb`, Theorem 3.2 and
  Theorem 3.5–Corollary 3.7.
