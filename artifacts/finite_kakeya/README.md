# Finite Kakeya

This folder contains the accompanying proofs, data, and additional results for the *Finite-field Kakeya* problem. The main notebook is [verification.ipynb](verification.ipynb).

## Files

- `verification.ipynb` — Verifies the constructions, recurrence, and comparison table.
- `kakeya_F3_d3_13.npy` — A 13-point Kakeya set in dimension 3 over the field of order 3.
- `kakeya_F3_d4_27.npy` — A 27-point Kakeya set in dimension 4 over the field of order 3.
- `kakeya_F3_d5_53.npy` — A 53-point Kakeya set in dimension 5 over the field of order 3.
- `station_point_certificates.npz` — Point sets and direction witnesses used by the notebook.
- `station_point_certificates.json` — Metadata for the point certificates.
- `benchmark_25_cells.json` — Data for the 25 benchmark cases.
- `literature_nested_shift_improvements.json` — Published nested-shift construction data.
- `alphaevolve_provenance.json` — Data used for the AlphaEvolve comparison.
- `fig/` — Figure generator, comparison data, and rendered figures.
- `formal_proofs/` — Lean 4 formal proofs for the spotlight results.
