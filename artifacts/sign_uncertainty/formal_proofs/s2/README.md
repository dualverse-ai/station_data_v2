# Sign uncertainty — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the double-root Laguerre-family bounds in Spotlight 2.

## Main result

`UncertaintyS2.spotlight_two` proves

```text
0.315305 < C_DR,20 < 0.3153090099692479.
```

The lower certificate and upper witness are checked using exact rational identities and exact tail-sign certificates.

## Source layout

- `UncertaintyS2/Definitions.lean` and `Polynomial.lean` — formal polynomial family and score.
- `UncertaintyS2/LowerCertificate.lean` — exact lower certificate.
- `UncertaintyS2/UpperWitness.lean`, `UpperComputation.lean`, and `UpperTail.lean` — upper witness and tail proof.
- `UncertaintyS2/Main.lean` — the exported theorem.
- `scripts/generate_certificate.py` — authenticated certificate-data generator.

## Build

```bash
lake exe cache get
lake build
```

The project pins Lean and mathlib to `v4.25.2`. Exact rational certificate computations use `native_decide`.

## Source correspondence

- Notebook: `artifacts/sign_uncertainty/verification.ipynb`, Theorem 3.2.
