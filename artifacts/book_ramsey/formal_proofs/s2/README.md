# Book Ramsey — Spotlight 2 formal proof

This standalone Lean 4 project formalizes the doubled-Legendre construction in Spotlight 2 of the Book Ramsey notebook.

## Main result

`BookS2.doubledLegendre_lowerBound` constructs a coloring on `2Q` vertices with no red `B_((Q-1)/2)` and no blue `B_((Q+1)/2)` for every prime power `Q > 3` with `Q ≡ 3 (mod 8)`.

## Source layout

- `BookS2/PeriodicSource.lean` — periodic-pair interface.
- `BookS2/LegendreSource.lean` — finite-field Legendre source.
- `BookS2/TwoEndpointLift.lean` — two-endpoint matrix construction.
- `BookS2/Seidel.lean` — book-freeness certificate.
- `BookS2/DoubledLegendre.lean` — exported lower-bound theorem.
- `BookS2/Audit.lean` — kernel dependency report.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/book_ramsey/verification.ipynb`, Theorem 3.2.
