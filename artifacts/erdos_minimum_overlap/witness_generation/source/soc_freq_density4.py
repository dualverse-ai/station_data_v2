"""Fourth comb-density SOC frequency-enrichment run.

E8f is the final requested density point: base K=400 plus a 0.015625 fill on
[4, 16].  This module reuses the a predecessor computation E4f machinery and caches only new
E8f rows in a separate directory.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any

import numpy as np

import sys

sys.path.insert(0, "source")
import soc_e1_certificate as e1c  # noqa: E402
import soc_freq_density3 as d3  # noqa: E402
import soc_freq_enrich2 as fe2  # noqa: E402
import soc_full_envelope as sfe  # noqa: E402
import soc_dual as sd  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
BASE_CERT_PATH = ROOT / "soc_certificate_improved.json"
BASE_EXACT_BUDGET_PATH = DATA / "soc_budget_exact.json"
E4F_JSON = DATA / "soc_freq_density3.json"
OUT_JSON = DATA / "soc_freq_density4.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_freq_density4.json"
ROW_CACHE_DIR = DATA / "soc_freq_density4_rows"

BASE_CERTIFIED_GLOBAL = d3.BASE_CERTIFIED_GLOBAL
E1_CERTIFIED_VALUE = d3.E1_CERTIFIED_VALUE
E2F_CERTIFIED_VALUE = d3.E2F_CERTIFIED_VALUE
E4F_CERTIFIED_VALUE = 0.3805486481104096
KNOWN_FEASIBLE_GUARD = d3.KNOWN_FEASIBLE_GUARD
ACTIVE_BRACKETS = d3.ACTIVE_BRACKETS
E8F_ANCHORS_REQUESTED = [0.0, 0.001, 0.002, 0.0024, 0.0026, 0.0028, 0.003, 0.004475]
E8F_PRIORITY_SCHEDULE = [0.0, 0.003, 0.004475, 0.001, 0.002, 0.0024, 0.0026, 0.0028]
ROOT_GRID_N = d3.ROOT_GRID_N
ROOT_TOL = d3.ROOT_TOL
EXACT_DPS = d3.EXACT_DPS
REFINED_PARTITIONS = d3.REFINED_PARTITIONS
DOMAIN_PARTITIONS = d3.DOMAIN_PARTITIONS
MEAN_GUARD_EXPECTED = d3.MEAN_GUARD_EXPECTED


def _jsonify(value: Any) -> Any:
    return d3._jsonify(value)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_jsonify(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _comb_description() -> str:
    return "base K=400 plus 0.015625-grid fill on [4,16]"


def _build_frequency_sets(base_xi: np.ndarray) -> dict[str, np.ndarray]:
    freqs = d3._build_frequency_sets(base_xi)
    e8f_xi = np.union1d(np.asarray(base_xi, dtype=np.float64), d3._fill_grid(4.0, 16.0, 0.015625))
    return {**freqs, "e8f": e8f_xi}


def _inclusion_check(freqs: dict[str, np.ndarray]) -> dict[str, Any]:
    base = np.asarray(freqs["base"], dtype=np.float64)
    e1 = np.asarray(freqs["e1"], dtype=np.float64)
    e2f = np.asarray(freqs["e2f"], dtype=np.float64)
    e4f = np.asarray(freqs["e4f"], dtype=np.float64)
    e8f = np.asarray(freqs["e8f"], dtype=np.float64)
    missing_base = np.setdiff1d(base, e8f)
    missing_e1 = np.setdiff1d(e1, e8f)
    missing_e2f = np.setdiff1d(e2f, e8f)
    missing_e4f = np.setdiff1d(e4f, e8f)
    extra_vs_e4f = np.setdiff1d(e8f, e4f)
    return {
        "base_frequency_count": int(base.size),
        "e1_frequency_count": int(e1.size),
        "e2f_frequency_count": int(e2f.size),
        "e4f_frequency_count": int(e4f.size),
        "e8f_frequency_count": int(e8f.size),
        "e4f_expected_frequency_count": 736,
        "e8f_strict_superset_of_base": bool(e8f.size > base.size and missing_base.size == 0),
        "e8f_strict_superset_of_e1": bool(e8f.size > e1.size and missing_e1.size == 0),
        "e8f_strict_superset_of_e2f": bool(e8f.size > e2f.size and missing_e2f.size == 0),
        "e8f_strict_superset_of_e4f": bool(e8f.size > e4f.size and missing_e4f.size == 0),
        "missing_base_frequency_count": int(missing_base.size),
        "missing_e1_frequency_count": int(missing_e1.size),
        "missing_e2f_frequency_count": int(missing_e2f.size),
        "missing_e4f_frequency_count": int(missing_e4f.size),
        "extra_vs_e4f_count": int(extra_vs_e4f.size),
        "all_requested_inclusions_pass": bool(
            e4f.size == 736
            and e8f.size > e4f.size
            and missing_base.size == 0
            and missing_e1.size == 0
            and missing_e2f.size == 0
            and missing_e4f.size == 0
        ),
    }


def _cache_path(anchor_m: float) -> Path:
    safe = f"{float(anchor_m):.7f}".replace(".", "p")
    return ROW_CACHE_DIR / f"e8f_m_{safe}.json"


def _load_cached_e8f_row(anchor_m: float) -> dict[str, Any] | None:
    path = _cache_path(anchor_m)
    if not path.exists():
        return None
    payload = _load_json(path)
    row = payload.get("row")
    if row and row.get("exact_positive_part_budget", {}).get("exact_budget_pass") and row.get("real_generator_gate_pass"):
        payload = dict(payload)
        payload["cache_status"] = "loaded_from_cache"
        return payload
    return None


def _load_e4f_payloads() -> list[dict[str, Any]]:
    if not E4F_JSON.exists():
        return []
    e4f = _load_json(E4F_JSON)
    payloads: list[dict[str, Any]] = []
    for summary in e4f.get("completed_e4f_rows", []):
        path = Path(summary["cache_path"])
        if not path.exists() and not path.is_absolute():
            path = d3.ROW_CACHE_DIR / path.name
        if not path.exists():
            continue
        payload = _load_json(path)
        row = payload.get("row")
        if not row:
            continue
        if not row.get("exact_positive_part_budget", {}).get("exact_budget_pass"):
            continue
        if not row.get("real_generator_gate_pass"):
            continue
        payload = dict(payload)
        payload["cache_status"] = "loaded_from_soc_freq_density3_cache"
        payloads.append(payload)
    return payloads


def _row_for_exact_budget(comp: dict[str, Any], anchor_m: float) -> dict[str, Any]:
    return {
        "id": f"e8f_anchor_m_{anchor_m:.7f}",
        "m": float(anchor_m),
        "K": int(comp["selected_frequency_count"]),
        "positive_part_partitions": 200_000,
        "alpha_boundary_threshold": 1.0e-10,
        "coefficient_intervals": {
            "a0_raw": sfe._interval(float(comp["a0"])),
            "a1": sfe._interval(float(comp["a1"])),
            "a2": sfe._interval(float(comp["a2"])),
        },
        "atom_intervals": {
            "xi": [sfe._interval(float(v)) for v in np.asarray(comp["xi"], dtype=np.float64)],
            "alpha": [sfe._interval(float(v)) for v in np.asarray(comp["alpha"], dtype=np.float64)],
            "beta": [sfe._interval(float(v)) for v in np.asarray(comp["beta"], dtype=np.float64)],
        },
    }


def _hardened_row(comp: dict[str, Any], budget: dict[str, Any], anchor_m: float) -> dict[str, Any]:
    alpha = np.asarray(comp["alpha"], dtype=np.float64)
    beta = np.asarray(comp["beta"], dtype=np.float64)
    return {
        "id": f"e8f_anchor_m_{anchor_m:.7f}",
        "family": "e8f",
        "m": float(anchor_m),
        "K": int(comp["selected_frequency_count"]),
        "selected_frequency_count": int(comp["selected_frequency_count"]),
        "nominal_raw_L": float(comp["raw_L"]),
        "quadratic_c0_lower": float(budget["quadratic_c0_lower"]),
        "L_source_m_lower": float(budget["L_source_m_lower"]),
        "a1": float(comp["a1"]),
        "a2": float(comp["a2"]),
        "exact_positive_part_budget": budget,
        "real_generator_gate_pass": bool(np.all(alpha[np.abs(beta) > 0.0] > 0.0)),
        "min_alpha_where_beta_nonzero": (
            float(np.min(alpha[np.abs(beta) > 0.0])) if np.any(np.abs(beta) > 0.0) else None
        ),
        "beta_active_count_gt_1e_8": int(np.sum(np.abs(beta) > 1.0e-8)),
        "source": {
            "description": "E8f fixed-mean SOC witness.",
            "comb_rule": _comb_description(),
        },
    }


def _solve_and_harden_e8f_row(xi: np.ndarray, anchor_m: float) -> dict[str, Any]:
    cached = _load_cached_e8f_row(anchor_m)
    if cached is not None:
        print(f"row_cache_hit family=e8f m={anchor_m:.7f}", flush=True)
        return cached

    print(f"row_solve_start family=e8f m={anchor_m:.7f}", flush=True)
    started = time.time()
    sol = sd.solve_fixed_mean_soc(
        np.asarray(xi, dtype=np.float64),
        m=float(anchor_m),
        x_grid_points=1001,
        solver="CLARABEL",
        max_iter=500,
        tol=1.0e-8,
    )
    comp = sd.compress_zero_pairs(sol)
    print(
        f"row_nominal_done family=e8f m={anchor_m:.7f} raw={comp['raw_L']:.15f} "
        f"status={sol['solver_status']} active_freq={comp['selected_frequency_count']} "
        f"solve_seconds={sol['solve_elapsed_seconds']:.2f}",
        flush=True,
    )
    budget = e1c._exact_budget_for_row(_row_for_exact_budget(comp, anchor_m), grid_n=ROOT_GRID_N, dps=EXACT_DPS)
    row = _hardened_row(comp, budget, anchor_m)
    payload = {
        "schema": "public cached exact-hardened SOC E8f row v1",
        "family": "e8f",
        "anchor_m": float(anchor_m),
        "comb_description": _comb_description(),
        "solver_status": str(sol["solver_status"]),
        "nominal_raw_L": float(comp["raw_L"]),
        "nominal_solver_objective_L": float(sol["solver_objective_L"]),
        "selected_frequency_count": int(comp["selected_frequency_count"]),
        "zero_pruned_count": int(comp["zero_pruned_count"]),
        "solve_elapsed_seconds": float(sol["solve_elapsed_seconds"]),
        "total_elapsed_seconds": float(time.time() - started),
        "exact_shift": float(budget["certified_shift_upper"]),
        "raw_budget_hi": float(budget["raw_budget_hi"]),
        "shifted_budget_hi": float(budget["shifted_budget_checks"][-1]["budget_hi"]),
        "positive_part_margin": float(budget["positive_part_margin"]),
        "root_count": int(budget["root_count"]),
        "root_width_max": float(budget["root_width_max"]),
        "lost_float_bracket_count": int(budget["lost_float_bracket_count"]),
        "unsafe_same_sign_cell_count": int(budget["unsafe_same_sign_cell_count"]),
        "real_generator_gate_pass": bool(row["real_generator_gate_pass"]),
        "beta_active_count_gt_1e_8": int(row["beta_active_count_gt_1e_8"]),
        "row_value_at_source_m": float(row["L_source_m_lower"]),
        "row": row,
        "cache_status": "newly_solved",
    }
    _write_json(_cache_path(anchor_m), payload)
    print(
        f"row_hardened_done family=e8f m={anchor_m:.7f} "
        f"L_source={payload['row_value_at_source_m']:.15f} "
        f"shift={payload['exact_shift']:.12e} budget_margin={payload['positive_part_margin']:.3e} "
        f"elapsed={payload['total_elapsed_seconds']:.1f}",
        flush=True,
    )
    return payload


def _envelopes_by_bracket(
    base_rows: list[dict[str, Any]],
    inherited_rows: list[dict[str, Any]],
    prior_rows: list[dict[str, Any]],
    e4f_rows: list[dict[str, Any]],
    e8f_rows: list[dict[str, Any]],
    base_repro: dict[str, Any],
    mean_guard: float,
) -> dict[str, dict[str, Any]]:
    e2f_rows = [r for r in prior_rows if r.get("family") == "e2f"]
    e3f_rows = [r for r in prior_rows if r.get("family") == "e3f"]
    out: dict[str, dict[str, Any]] = {}
    for blo, bhi in ACTIVE_BRACKETS:
        key = f"{blo:.3f}_{bhi:.3f}"
        out[key] = {
            "e1_inherited": sfe._apply_baseline_floor(
                sfe._envelope(list(base_rows) + inherited_rows, mean_guard, "inherited_E1_dense_rows", active_bracket=(blo, bhi)),
                base_repro,
            ),
            "e2f_density": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + e2f_rows,
                    mean_guard,
                    "inherited_plus_E2f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "e4f_density": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + e2f_rows + e4f_rows,
                    mean_guard,
                    "inherited_plus_E2f_E4f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "e8f_density": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + e2f_rows + e4f_rows + e8f_rows,
                    mean_guard,
                    "inherited_plus_E2f_E4f_E8f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "union_all": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + prior_rows + e4f_rows + e8f_rows,
                    mean_guard,
                    "inherited_plus_E2f_E3f_E4f_E8f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
        }
    return out


def _payload_summary(payloads: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "family": str(p["family"]),
            "anchor_m": float(p["anchor_m"]),
            "nominal_raw_L": float(p["nominal_raw_L"]),
            "row_value_at_source_m": float(p["row_value_at_source_m"]),
            "selected_frequency_count": int(p["selected_frequency_count"]),
            "exact_shift": float(p["exact_shift"]),
            "positive_part_margin": float(p["positive_part_margin"]),
            "root_count": int(p["root_count"]),
            "cache_path": str(_cache_path(float(p["anchor_m"])) if p["family"] == "e8f" else p.get("cache_path", "")),
            "cache_status": str(p.get("cache_status", "unknown")),
        }
        for p in payloads
    ]


def _trend_summary(envelopes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    groups = [
        ("E1_0p125", "e1_inherited"),
        ("E2f_0p0625", "e2f_density"),
        ("E4f_0p03125", "e4f_density"),
        ("E8f_0p015625", "e8f_density"),
    ]
    points = {name: d3._best_outside_passing(envelopes, group) for name, group in groups}
    vals = {
        name: (entry["overall"]["certified_global"] if entry["overall"] is not None else None)
        for name, entry in points.items()
    }
    names = [name for name, _group in groups]
    increments: dict[str, float | None] = {}
    ratios: dict[str, float | None] = {}
    for left, right in zip(names[:-1], names[1:]):
        key = f"{left}_to_{right}"
        increments[key] = None if vals[left] is None or vals[right] is None else vals[right] - vals[left]
    inc_keys = list(increments)
    for prev, cur in zip(inc_keys[:-1], inc_keys[1:]):
        ratios[f"{cur}_over_{prev}"] = (
            None
            if increments[prev] in (None, 0.0) or increments[cur] is None
            else increments[cur] / increments[prev]
        )
    last_inc = increments[inc_keys[-1]]
    last_ratio = ratios[f"{inc_keys[-1]}_over_{inc_keys[-2]}"]
    if vals[names[-1]] is not None and last_inc is not None and last_ratio is not None and 0.0 <= last_ratio < 1.0:
        heuristic_ceiling = vals[names[-1]] + last_inc * last_ratio / (1.0 - last_ratio)
    else:
        heuristic_ceiling = None
    shrink_continues = bool(
        increments[inc_keys[0]] is not None
        and increments[inc_keys[1]] is not None
        and increments[inc_keys[2]] is not None
        and increments[inc_keys[0]] > increments[inc_keys[1]] > increments[inc_keys[2]] > 0.0
    )
    return {
        "points": points,
        "certified_values": vals,
        "increments": increments,
        "successive_ratios": ratios,
        "shrink_continues": shrink_continues,
        "heuristic_geometric_sum_ceiling_not_certified": heuristic_ceiling,
        "heuristic_note": "NOT CERTIFIED: assumes the last observed increment ratio persists for all finer comb-density points.",
    }


def _base_psd_gate(base_cert: dict[str, Any], exact_budget_summary: dict[str, Any]) -> dict[str, Any]:
    gates = smh._gate_summary(base_cert, smh.IMPROVED_ROW_ID, exact_budget_summary)
    return {
        "positive_part_exact_budget": gates["positive_part_exact_budget"],
        "gram_psd": gates["gram_psd"],
        "real_generator": gates["real_generator"],
    }


def _assemble_result(
    *,
    started: float,
    base_rows: list[dict[str, Any]],
    inherited_payloads: list[dict[str, Any]],
    prior_payloads: list[dict[str, Any]],
    e4f_payloads: list[dict[str, Any]],
    e8f_payloads: list[dict[str, Any]],
    skipped: list[dict[str, Any]],
    recovered: dict[str, Any],
    base_repro: dict[str, Any],
    base_psd_gate: dict[str, Any],
    inclusion_check: dict[str, Any],
    mean_guard: float,
    status: str,
) -> dict[str, Any]:
    inherited_rows = [p["row"] for p in inherited_payloads]
    prior_rows = [p["row"] for p in prior_payloads]
    e4f_rows = [p["row"] for p in e4f_payloads]
    e8f_rows = [p["row"] for p in e8f_payloads]
    envelopes = _envelopes_by_bracket(base_rows, inherited_rows, prior_rows, e4f_rows, e8f_rows, base_repro, mean_guard)
    best_union = d3._best_outside_passing(envelopes, "union_all")
    best_e8f = d3._best_outside_passing(envelopes, "e8f_density")
    trend = _trend_summary(envelopes)
    e8f_003 = envelopes["0.000_0.030"]["e8f_density"]
    e8f_004 = envelopes["0.000_0.040"]["e8f_density"]
    union_003 = envelopes["0.000_0.030"]["union_all"]
    union_004 = envelopes["0.000_0.040"]["union_all"]
    all_e8f_rows_valid = bool(
        all(p["row"]["exact_positive_part_budget"]["exact_budget_pass"] for p in e8f_payloads)
        and all(p["row"]["real_generator_gate_pass"] for p in e8f_payloads)
    )
    return {
        "schema": "public SOC frequency density point E8f v1",
        "status": status,
        "elapsed_seconds": float(time.time() - started),
        "base_reproduction": base_repro,
        "base_reproduction_expected": BASE_CERTIFIED_GLOBAL,
        "base_psd_and_budget_gates": base_psd_gate,
        "recovered_exact_budget_row": recovered,
        "inclusion_check": inclusion_check,
        "e8f_anchors_requested": E8F_ANCHORS_REQUESTED,
        "e8f_priority_schedule": E8F_PRIORITY_SCHEDULE,
        "completed_e8f_row_count": int(len(e8f_payloads)),
        "completed_e8f_rows": _payload_summary(e8f_payloads),
        "skipped_or_failed_rows": skipped,
        "inherited_payload_count": int(len(inherited_payloads)),
        "prior_enrichment_payload_count": int(len(prior_payloads)),
        "e4f_payload_count": int(len(e4f_payloads)),
        "bracket_envelopes": envelopes,
        "best_outside_passing_e8f_density": best_e8f,
        "best_outside_passing_union_all": best_union,
        "comb_density_trend": trend,
        "gate_summary": {
            "base_reproduction": bool(base_repro["pass"]),
            "base_positive_part_exact_budget": bool(base_psd_gate["positive_part_exact_budget"]["pass"]),
            "base_psd_gram": bool(base_psd_gate["gram_psd"]["pass"]),
            "base_real_generator": bool(base_psd_gate["real_generator"]["pass"]),
            "mean_guard_matches_request": bool(abs(float(mean_guard) - MEAN_GUARD_EXPECTED) <= 1.0e-15),
            "inclusion": bool(inclusion_check["all_requested_inclusions_pass"]),
            "e8f_exact_budget_all_completed": all_e8f_rows_valid,
            "e8f_all_requested_anchors_completed": bool(len(e8f_payloads) == len(E8F_ANCHORS_REQUESTED)),
            "e8f_density_0_03_outside_exclusion": bool(e8f_003["outside_exclusion_pass"]),
            "e8f_density_0_04_outside_exclusion": bool(e8f_004["outside_exclusion_pass"]),
            "union_0_03_outside_exclusion": bool(union_003["outside_exclusion_pass"]),
            "union_0_04_outside_exclusion": bool(union_004["outside_exclusion_pass"]),
            "union_smoke_under_known_feasible": bool(
                union_003["certified_global"] <= KNOWN_FEASIBLE_GUARD
                and union_004["certified_global"] <= KNOWN_FEASIBLE_GUARD
            ),
            "certified_claim_allowed": bool(
                base_repro["pass"]
                and base_psd_gate["positive_part_exact_budget"]["pass"]
                and base_psd_gate["gram_psd"]["pass"]
                and base_psd_gate["real_generator"]["pass"]
                and inclusion_check["all_requested_inclusions_pass"]
                and all_e8f_rows_valid
                and e8f_003["outside_exclusion_pass"]
                and e8f_004["outside_exclusion_pass"]
            ),
        },
        "settings": {
            "solver": "CLARABEL",
            "solver_tol": 1.0e-8,
            "solver_max_iter": 500,
            "x_grid_points": 1001,
            "exact_budget_root_grid_n": ROOT_GRID_N,
            "root_tol": ROOT_TOL,
            "exact_dps": EXACT_DPS,
            "domain_partitions": DOMAIN_PARTITIONS,
            "refined_partitions": REFINED_PARTITIONS,
            "mean_guard": float(mean_guard),
            "known_feasible_guard": KNOWN_FEASIBLE_GUARD,
            "compute_guard_note": "Skipped anchors are conservative because the envelope is a maximum over certified rows.",
        },
        "reference_values": {
            "baseline_base": BASE_CERTIFIED_GLOBAL,
            "E1_0p125_prior": E1_CERTIFIED_VALUE,
            "E2f_0p0625_prior": E2F_CERTIFIED_VALUE,
            "E4f_0p03125_prior": E4F_CERTIFIED_VALUE,
        },
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "e4f_json": str(E4F_JSON),
            "output_json": str(OUT_JSON),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
            "row_cache_dir": str(ROW_CACHE_DIR),
        },
    }


def _print_summary(result: dict[str, Any]) -> None:
    print("soc_freq_density4_summary_begin", flush=True)
    br = result["base_reproduction"]
    gates = result["gate_summary"]
    print(
        f"base_reproduction_integrity={br['value']:.15f} "
        f"expected={BASE_CERTIFIED_GLOBAL:.15f} argmin_m={br['argmin_m']:.7f} pass={br['pass']}",
        flush=True,
    )
    print(
        f"base_gates positive_part={gates['base_positive_part_exact_budget']} "
        f"gram_psd={gates['base_psd_gram']} real_generator={gates['base_real_generator']}",
        flush=True,
    )
    inc = result["inclusion_check"]
    print(
        f"e8f_inclusion base={inc['base_frequency_count']} e4f={inc['e4f_frequency_count']} "
        f"e8f={inc['e8f_frequency_count']} expected_e4f={inc['e4f_expected_frequency_count']} "
        f"strict_superset_e4f={inc['e8f_strict_superset_of_e4f']} extra_vs_e4f={inc['extra_vs_e4f_count']} "
        f"missing_e4f={inc['missing_e4f_frequency_count']}",
        flush=True,
    )
    for row in result["completed_e8f_rows"]:
        print(
            f"e8f_row m={row['anchor_m']:.7f} value={row['row_value_at_source_m']:.15f} "
            f"raw={row['nominal_raw_L']:.15f} active_freq={row['selected_frequency_count']} "
            f"shift={row['exact_shift']:.12e} budget_margin={row['positive_part_margin']:.3e} "
            f"cache={row['cache_status']}",
            flush=True,
        )
    if result["skipped_or_failed_rows"]:
        print(f"skipped_or_failed_rows={result['skipped_or_failed_rows']}", flush=True)
    for bracket_key, envs in result["bracket_envelopes"].items():
        for group in ("e1_inherited", "e2f_density", "e4f_density", "e8f_density", "union_all"):
            env = envs[group]
            print(
                f"envelope bracket={bracket_key} group={group} value={env['certified_global']:.15f} "
                f"argmin={env['global_argmin_m']:.7f} controlling={env['global_controlling_row']} "
                f"outside_pass={env['outside_exclusion_pass']} margin={env['outside_exclusion_margin']:.12e}",
                flush=True,
            )
    trend = result["comb_density_trend"]
    vals = trend["certified_values"]
    incs = trend["increments"]
    ratios = trend["successive_ratios"]
    print(
        "density_trend "
        f"E1={vals['E1_0p125']:.15f} E2f={vals['E2f_0p0625']:.15f} "
        f"E4f={vals['E4f_0p03125']:.15f} E8f={vals['E8f_0p015625']:.15f}",
        flush=True,
    )
    print(f"density_increments={incs}", flush=True)
    print(f"density_successive_ratios={ratios}", flush=True)
    print(
        f"shrink_continues={trend['shrink_continues']} "
        f"heuristic_geometric_sum_ceiling_NOT_CERTIFIED={trend['heuristic_geometric_sum_ceiling_not_certified']}",
        flush=True,
    )
    best = result["best_outside_passing_e8f_density"]["overall"]
    if best is not None:
        print(
            f"best_e8f_outside_passing value={best['certified_global']:.15f} "
            f"bracket={best['active_bracket']} argmin={best['global_argmin_m']:.7f} "
            f"controlling={best['global_controlling_row']} "
            f"delta_vs_E4f={best['certified_global'] - E4F_CERTIFIED_VALUE:.12e}",
            flush=True,
        )
    print(f"saved_json={OUT_JSON}", flush=True)
    print(f"saved_json_root_copy={OUT_JSON_ROOT_COPY}", flush=True)


def run_frequency_density4_analysis(*, max_total_seconds: float = 1680.0) -> dict[str, Any]:
    started = time.time()
    base_cert = _load_json(BASE_CERT_PATH)
    exact_budget_summary = _load_json(BASE_EXACT_BUDGET_PATH)
    mean_guard = float(base_cert["verification_settings"]["mean_guard"])
    base_rows, recovered = smh.build_verified_rows_with_baseline_recovery(base_cert, exact_budget_summary)
    base_repro = sfe._base_reproduction(base_rows, mean_guard)
    if not base_repro["pass"]:
        raise RuntimeError(f"base reproduction integrity control failed: {base_repro}")
    base_psd_gate = _base_psd_gate(base_cert, exact_budget_summary)

    freqs = _build_frequency_sets(e1c._base_frequencies(base_cert))
    inclusion_check = _inclusion_check(freqs)
    if not inclusion_check["all_requested_inclusions_pass"]:
        raise RuntimeError(f"E8f inclusion check failed: {inclusion_check}")

    print(
        f"base_reproduction_integrity={base_repro['value']:.15f} "
        f"expected={BASE_CERTIFIED_GLOBAL:.15f} argmin_m={base_repro['argmin_m']:.7f}",
        flush=True,
    )
    print(
        f"inclusion_check base={inclusion_check['base_frequency_count']} "
        f"e4f={inclusion_check['e4f_frequency_count']} e8f={inclusion_check['e8f_frequency_count']} "
        f"e8f_superset_e4f={inclusion_check['e8f_strict_superset_of_e4f']} "
        f"extra_vs_e4f={inclusion_check['extra_vs_e4f_count']}",
        flush=True,
    )

    inherited_payloads = fe2._load_inherited_payloads()
    prior_payloads = d3._load_prior_enrichment_payloads()
    e4f_payloads = _load_e4f_payloads()
    print(
        f"inherited_hardened_rows_loaded={len(inherited_payloads)} "
        f"prior_enrichment_rows_loaded={len(prior_payloads)} "
        f"e4f_rows_loaded={len(e4f_payloads)}",
        flush=True,
    )

    completed: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for idx, anchor_m in enumerate(E8F_PRIORITY_SCHEDULE):
        elapsed = time.time() - started
        cached = _load_cached_e8f_row(anchor_m)
        remaining_required = max(0, 3 - idx)
        reserve = 520.0 if remaining_required > 0 else 420.0
        if cached is None and elapsed > float(max_total_seconds) - reserve:
            skipped.append(
                {
                    "family": "e8f",
                    "anchor_m": float(anchor_m),
                    "reason": "compute_limit_guard",
                    "elapsed_seconds_before_row": float(elapsed),
                    "guard_reserve_seconds": float(reserve),
                }
            )
            print(f"row_skipped_compute_guard family=e8f m={anchor_m:.7f} elapsed={elapsed:.1f}", flush=True)
            continue
        try:
            payload = _solve_and_harden_e8f_row(freqs["e8f"], anchor_m)
        except Exception as exc:  # noqa: BLE001
            skipped.append({"family": "e8f", "anchor_m": float(anchor_m), "reason": "row_exception", "error": repr(exc)})
            print(f"row_failed family=e8f m={anchor_m:.7f} error={exc!r}", flush=True)
            continue
        completed.append(payload)
        partial = _assemble_result(
            started=started,
            base_rows=base_rows,
            inherited_payloads=inherited_payloads,
            prior_payloads=prior_payloads,
            e4f_payloads=e4f_payloads,
            e8f_payloads=completed,
            skipped=skipped,
            recovered=recovered,
            base_repro=base_repro,
            base_psd_gate=base_psd_gate,
            inclusion_check=inclusion_check,
            mean_guard=mean_guard,
            status="partial_running",
        )
        _write_json(OUT_JSON, partial)
        _write_json(OUT_JSON_ROOT_COPY, partial)

    status = "complete_within_time_guard" if not skipped else "compute_limited"
    result = _assemble_result(
        started=started,
        base_rows=base_rows,
        inherited_payloads=inherited_payloads,
        prior_payloads=prior_payloads,
        e4f_payloads=e4f_payloads,
        e8f_payloads=completed,
        skipped=skipped,
        recovered=recovered,
        base_repro=base_repro,
        base_psd_gate=base_psd_gate,
        inclusion_check=inclusion_check,
        mean_guard=mean_guard,
        status=status,
    )
    _write_json(OUT_JSON, result)
    _write_json(OUT_JSON_ROOT_COPY, result)
    _print_summary(result)
    return result


if __name__ == "__main__":
    run_frequency_density4_analysis()
