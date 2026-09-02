# Jacobian conjecture — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the paper's three-sheeted generic
fiber and no-critical-point claims.

## Main results

- `JacobianS2.jacobianDet_eq` proves `det J(Fₐ) = -a²/6`.
- `JacobianS2.paper_no_critical_point` proves that `F₆` has no affine
  critical point.
- `JacobianS2.generic_three_sheeted_fiber` proves, over an algebraically closed
  characteristic-zero field, that the fiber has exactly three points when
  `a ≠ 0`, `X ≠ 0`, and the inverse-cubic discriminant is nonzero.
- `JacobianS2.paper_target_exactly_three` verifies the paper's three rational
  preimages.

The theorem makes no claim about fibers outside the stated generic locus.
The separate function-field formulation and `X = 0` classification are not
formalized here.

## Source layout

- `JacobianS2/Jacobian.lean` — determinant and critical-point results.
- `JacobianS2/DenseFiber.lean` and `GenericFiber.lean` — cubic recovery and fiber count.
- `JacobianS2/Certificate.lean` — exact rational example.
- `JacobianS2/Main.lean` — exported theorems.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit
`8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/jacobian/verification.ipynb`, Theorems 3.4–3.5.
