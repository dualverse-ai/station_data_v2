# Witness-generation files

These files support the lower-bound witnesses checked by the main [verification notebook](../verification.ipynb).

## Files

- `generate_witness.py` — Generates candidate witness data.
- `run_witness_generation.py` — Coordinates the witness-generation workflow.
- `requirements.txt` — Numerical package requirements.
- `reference_run_summary.json` — Summary of the retained reference calculation.
- `file_manifest.json` — Inventory of the supporting files.
- `source/cpos_audit.py` — Audits positive-part constraints.
- `source/cpos_augmented_dual.py` — Builds the augmented dual problem.
- `source/even_dual_optimize.py` — Optimizes even dual witnesses.
- `source/phase_augmented_dual.py` — Builds the phase-augmented dual problem.
- `source/soc_budget_exact.py` — Computes exact budget data.
- `source/soc_dual.py` — Core second-order-cone dual routines.
- `source/soc_e1_certificate.py` — Builds the first-envelope certificate.
- `source/soc_freq_density3.py` — Builds the density-3 frequency envelope.
- `source/soc_freq_density4.py` — Builds the density-4 frequency envelope.
- `source/soc_freq_enrich2.py` — Builds the enriched frequency envelope.
- `source/soc_full_envelope.py` — Builds the full frequency envelope.
- `source/soc_menvelope_harden.py` — Refines the mean-parameter envelope.
- `source/soc_sos_dual.py` — Sum-of-squares dual routines.
- `source/soc_sos_dual_global.py` — Global sum-of-squares dual routines.
- `source/soc_sos_remainder_pilot.py` — Remainder-bound calculations.
- `source/verify_B0.py` — Checks the base certificate.
- `source/verify_cert_improved.py` — Checks the improved certificate.
- `source/soc_certificate_improved.json` — Retained improved certificate.
- `source/data/soc_budget_exact.json` — Exact budget data.
- `source/data/soc_freq_density3.json` — Density-3 envelope data.
- `source/data/soc_freq_density3_rows/*.json` — Density-3 rows at the retained mean anchors.
- `source/data/soc_freq_density4_rows/*.json` — Density-4 rows at the retained mean anchors.
- `source/data/soc_freq_enrich2.json` — Enriched frequency-envelope data.
- `source/data/soc_freq_enrich2_rows/*.json` — Enriched rows at the retained mean anchors.
- `source/data/soc_full_envelope.json` — Full-envelope data.
- `source/data/soc_full_envelope_rows/*.json` — Base and first-envelope rows at the retained mean anchors.
- `source/data/soc_sos_nconv_generators.npz` — Numerical generators used by the sum-of-squares routines.
