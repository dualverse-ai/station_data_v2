#!/usr/bin/env python3
"""Generate the floating-point witnesses underlying the sharp lower-bound search.

This is an optional provenance computation.  The rigorous theorem is verified
from fixed witnesses by the parent notebook, not by trusting this optimizer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from pathlib import Path


FAITHFUL_ANCHORS = (
    0.0, 0.0005, 0.001, 0.0015, 0.002, 0.0024,
    0.0026, 0.0028, 0.003, 0.004, 0.005, 0.006,
)

EXTENDED_ANCHORS = tuple(sorted(set(FAITHFUL_ANCHORS + (
    0.00175, 0.0019, 0.0021, 0.0022, 0.0023, 0.0025,
    0.0027, 0.0029, 0.0032, 0.0035, 0.0045,
))))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=("faithful", "extended", "smoke"), required=True)
    parser.add_argument("--term-limit", type=int)
    parser.add_argument("--refined-partitions", type=int)
    parser.add_argument("--domain-partitions", type=int)
    parser.add_argument("--output-dir", type=Path, default=Path("outputs"))
    return parser.parse_args()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    args = parse_args()
    source = Path("source")
    required = tuple(source / name for name in (
        "soc_sos_dual_global.py",
        "soc_sos_dual.py",
        "soc_sos_remainder_pilot.py",
        "soc_full_envelope.py",
    ))
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise SystemExit(f"run from a prepared work directory; missing {missing}")

    sys.path.insert(0, str(source))
    import soc_full_envelope as sfe  # noqa: PLC0415
    import soc_sos_dual as sos  # noqa: PLC0415
    import soc_sos_dual_global as sharp  # noqa: PLC0415

    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    anchor_cache = output_dir / "fresh_anchor_cache"
    anchor_cache.mkdir(parents=True, exist_ok=True)

    if args.profile == "faithful":
        anchors = FAITHFUL_ANCHORS
        term_limit = 220 if args.term_limit is None else args.term_limit
        schemes = ("uniform_top2", "uniform_top3", "uniform_top4")
        start_scales = (0.5, 1.0)
        maxiter = 180
        refined_partitions = 6_000_000 if args.refined_partitions is None else args.refined_partitions
        domain_partitions = 2_000_000 if args.domain_partitions is None else args.domain_partitions
    elif args.profile == "extended":
        anchors = EXTENDED_ANCHORS
        term_limit = 440 if args.term_limit is None else args.term_limit
        schemes = (
            "onehot_0", "onehot_1", "onehot_2", "onehot_3", "onehot_4", "onehot_5",
            "uniform_top2", "uniform_top3", "uniform_top4", "uniform_top5", "uniform_top6",
            "front_loaded_top4",
        )
        start_scales = (0.25, 0.5, 1.0, 1.5)
        maxiter = 500
        refined_partitions = 6_000_000 if args.refined_partitions is None else args.refined_partitions
        domain_partitions = 2_000_000 if args.domain_partitions is None else args.domain_partitions
    else:
        anchors = (0.0026,)
        term_limit = 8 if args.term_limit is None else args.term_limit
        schemes = ("uniform_top2",)
        start_scales = (0.5,)
        maxiter = 2
        refined_partitions = 500 if args.refined_partitions is None else args.refined_partitions
        domain_partitions = 2_000 if args.domain_partitions is None else args.domain_partitions

    if term_limit <= 0 or refined_partitions <= 0 or domain_partitions <= 0:
        raise SystemExit("term and partition counts must be positive")

    # Force fresh multiplier vectors rather than using any earlier optimized row.
    sharp._load_prior_pilot_anchor = lambda _m: None
    sharp.CACHE_DIR = anchor_cache
    sharp.OUT_JSON = output_dir / "sharp_witness.json"
    sharp.OUT_JSON_ROOT_COPY = output_dir / "sharp_witness_root_copy.json"
    sharp.ANCHORS = anchors
    sharp.GLOBAL_SCHEMES = schemes
    sharp.GLOBAL_START_SCALES = start_scales
    sharp.GLOBAL_MAXITER = maxiter
    sharp.REFINED_PARTITIONS = refined_partitions
    sharp.DOMAIN_PARTITIONS = domain_partitions
    sos.TERM_LIMIT = term_limit
    sfe.REFINED_PARTITIONS = refined_partitions
    sfe.DOMAIN_PARTITIONS = domain_partitions

    # The reduced profile exercises the same path while remaining quick.
    if args.profile == "smoke":
        sharp.EXACT_ROOT_GRID_N = 2_000
        sos.OPT_GRID_N = 129
        sos.CERT_PARTITIONS = 1_000

    config = {
        "profile": args.profile,
        "anchors": list(anchors),
        "term_limit": term_limit,
        "schemes": list(schemes),
        "start_scales": list(start_scales),
        "optimizer_maxiter": maxiter,
        "refined_partitions": refined_partitions,
        "domain_partitions": domain_partitions,
        "source_sha256": {str(path): sha256(path) for path in required},
        "role": "floating-point witness generation; rigorous directed verification is separate",
    }
    (output_dir / "run_config.json").write_text(
        json.dumps(config, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    print("WITNESS_GENERATION_BEGIN", flush=True)
    print(json.dumps(config, sort_keys=True), flush=True)
    started = time.time()
    result = sharp.run_global_analysis(max_total_seconds=float("inf"), out_json=sharp.OUT_JSON)

    missing_vectors: list[float] = []
    coefficient_counts: dict[str, int] = {}
    for anchor in result.get("anchor_results", []):
        best = anchor.get("raw_anchor_result", {}).get("best_scheme")
        m = float(anchor.get("anchor_m", -1.0))
        if best is None:
            missing_vectors.append(m)
            continue
        y = best.get("dual_y")
        pack = best.get("term_pack")
        if y is None or not pack:
            missing_vectors.append(m)
        else:
            coefficient_counts[f"{m:.7f}"] = len(y)

    completed_count = len(result.get("anchor_results", []))
    skipped = result.get("skipped_or_failed_anchors", result.get("skipped", []))
    summary = result.get("summary", {})
    complete = bool(
        completed_count == len(anchors)
        and not skipped
        and result.get("status") == "complete"
        and summary.get("completed_all_requested_anchors") is True
        and not missing_vectors
        and len(coefficient_counts) == len(anchors)
    )
    audit = {
        "elapsed_seconds": time.time() - started,
        "requested_anchor_count": len(anchors),
        "completed_anchor_count": completed_count,
        "skipped_or_failed_anchors": skipped,
        "anchors_missing_dual_vectors": sorted(set(missing_vectors)),
        "serialized_dual_coefficient_counts": coefficient_counts,
        "all_nonzero_best_schemes_serialized": bool(
            not missing_vectors and len(coefficient_counts) == len(anchors)
        ),
        "generation_complete": complete,
        "numerical_summary": summary,
        "proof_status": "requires the directed-arithmetic replay in the parent notebook",
    }
    (output_dir / "generation_audit.json").write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, sort_keys=True), flush=True)
    print("WITNESS_GENERATION_DONE", flush=True)
    return 0 if complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
