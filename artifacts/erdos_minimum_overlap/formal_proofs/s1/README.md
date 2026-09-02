# Erdős minimum overlap — Spotlight 1 formal proof

This standalone Lean 4 project formalizes the lower bound in Spotlight 1.

## Main result

```text
ErdosMinimum.paper_erdos_minimum_overlap_lower_bound :
  (380552 : ℝ) / 1000000 < paperErdosMinimum
```

The proof uses the paper's measure-theoretic `L∞` definition and checks
13,970 exact cells.

## Source layout

- `ErdosMinimum/PaperProblem.lean` — paper definition and its equivalent internal form.
- `ErdosMinimum/AnalyticBridge.lean` and `AnalyticCertificate.lean` — analytic reduction.
- `ErdosMinimum/AdaptiveCertificateRow*.lean` — exact certificate partitions.
- `ErdosMinimum/MainTheorem.lean` — exported theorem.

## Build

The generated Lean modules are compressed for Git. Extract them first:

```bash
unzip -q -o computed_sources.zip
bash certificate/replay_from_source.sh
```

A clean replay requires substantial time, 64 GiB RAM, about 500 GB free disk,
and Linux `vm.max_map_count >= 262144`.

Optional prebuilt cell artifacts are available from
[Zenodo](https://doi.org/10.5281/zenodo.22259273). Download the 28
`erdos-row*.tar.gz` files into one directory, then run:

```bash
bash certificate/use_zenodo_artifacts.sh /path/to/downloads
```

The script checks the archives and recompiles the aggregate proofs and final
theorem. It does not replay the individual cell proofs from source.

The project pins Lean `v4.26.0-rc2` and mathlib commit
`8f62007a980111b87be592665493301acbb05ea4`.
The cell proofs use kernel reduction (`decide`), not `native_decide`.

## Source correspondence

- Notebook: `artifacts/erdos_minimum_overlap/verification.ipynb`, Theorem 2.1.
