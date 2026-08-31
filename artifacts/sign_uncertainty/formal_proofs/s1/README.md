# Sign uncertainty — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the `0.3089` upper bound in Spotlight 1.

## Main result

```text
UncertaintyUpperBound.C_SU_le_03089 : C_SU ≤ 3089/10000
```

The project verifies the exact polynomial certificate, Fourier identity, tail bound, and final rational comparison.

## Source layout

- `UncertaintyUpperBound/SignUncertainty.lean` — admissible class and constant.
- `UncertaintyUpperBound/CertificateComputation.lean` and `TailCertificate.lean` — exact tail certificate.
- `UncertaintyUpperBound/RadialFourier.lean` and `SelfFourierCertificate.lean` — Fourier verification.
- `UncertaintyUpperBound/Witness.lean` and `Main.lean` — witness and exported theorem.
- `scripts/generate_certificate.py` — authenticated certificate-data generator.

## Build

```bash
lake exe cache get
lake build
```

The project pins Lean and mathlib to `v4.25.2`. Exact rational certificate computations use `native_decide`.

## Source correspondence

- Notebook: `artifacts/sign_uncertainty/verification.ipynb`, Theorem 2.1.
