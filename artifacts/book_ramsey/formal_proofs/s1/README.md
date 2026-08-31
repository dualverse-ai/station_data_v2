# Book Ramsey — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the conference-graph construction in Spotlight 1 of the Book Ramsey notebook.

## Main result

`BookS1.conference_graph_lower_bound` constructs a coloring on `4q + 2` vertices with no red `B_q` and no blue `B_(q+1)` from a conference graph of order `q`.

## Source layout

- `BookS1/Definitions.lean` — book containment and witness definitions.
- `BookS1/ConferenceSource.lean` — conference signs and matrix identities.
- `BookS1/ConferenceLift.lean` — the four-chamber construction.
- `BookS1/SeidelCertificate.lean` — common-neighbour certificate.
- `BookS1/SRGBridge.lean` — strongly regular graph interface.
- `BookS1/Main.lean` — the exported theorem.

## Build

```bash
lake build
```

The project pins Lean `v4.26.0-rc2` and mathlib commit `8f62007a980111b87be592665493301acbb05ea4`.

## Source correspondence

- Notebook: `artifacts/book_ramsey/verification.ipynb`, Theorem 2.1.
