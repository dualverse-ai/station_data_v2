# Book Ramsey — Spotlight 3 formal proof

This standalone Lean 4 project formalizes the Yamada–Pott construction in Spotlight 3 of the Book Ramsey notebook.

## Main result

`BookS3.yamadaPott_primePower_lowerBound` constructs a coloring on `q² - q` vertices with no red `B_((q²-q-2)/4)` and no blue `B_((q²-q+2)/4)` for every prime power `q ≥ 7` with `q ≡ 3 (mod 4)`.

## Source layout

- `BookS3/Ramsey.lean` — book containment and lower-bound certificates.
- `BookS3/SourceIdentity.lean` — finite-field character identities.
- `BookS3/CodegreeArithmetic.lean` — parameter and codegree arithmetic.
- `BookS3/DifferenceLift.lean` — two-fibre difference graph.
- `BookS3/YamadaPottConstruction.lean` — concrete finite-field construction.
- `BookS3/WithinCorrelation.lean`, `MixedCorrelation.lean`, and `YamadaPottProfile.lean` — correlation profile.
- `BookS3/Main.lean` — exported lower-bound theorems.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/book_ramsey/verification.ipynb`, Theorem 4.2.
