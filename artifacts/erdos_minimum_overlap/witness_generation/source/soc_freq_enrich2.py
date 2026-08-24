"""Frequency-enrichment continuation for the SOC mean envelope.

This extends the a predecessor computation dense E1 envelope with two stricter supersets:

* E2f: base K=400 plus 0.0625 fill on [4, 16].
* E3f: base K=400 plus 0.125 fill on [2, 20].

Rows are exact-budget hardened before inclusion in the envelope.
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
import soc_full_envelope as sfe  # noqa: E402
import soc_dual as sd  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
BASE_CERT_PATH = ROOT / "soc_certificate_improved.json"
BASE_EXACT_BUDGET_PATH = DATA / "soc_budget_exact.json"
INHERITED_JSON = DATA / "soc_full_envelope.json"
INHERITED_ROW_CACHE_DIR = DATA / "soc_full_envelope_rows"
OUT_JSON = DATA / "soc_freq_enrich2.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_freq_enrich2.json"
ROW_CACHE_DIR = DATA / "soc_freq_enrich2_rows"

BASE_CERTIFIED_GLOBAL = 0.38043481690472875
PREVIOUS_PLATEAU = 0.380496768638831
KNOWN_FEASIBLE_GUARD = 0.380895
ANCHORS = [0.003, 0.004475, 0.006]
PRIORITY_SCHEDULE = [
    ("e2f", 0.004475),
    ("e3f", 0.004475),
    ("e2f", 0.003),
    ("e3f", 0.003),
    ("e2f", 0.006),
    ("e3f", 0.006),
]
ACTIVE_BRACKETS = [(0.0, 0.03), (0.0, 0.04)]
ROOT_GRID_N = 1_000_000
EXACT_DPS = 80
ROOT_TOL = 5.0e-13
REFINED_PARTITIONS = 60_000
DOMAIN_PARTITIONS = 400_000
REFERENCE_M = 0.004475
INHERITED_CONTROL_ROW_ID = smh.IMPROVED_ROW_ID


def _jsonify(value: Any) -> Any:
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, (np.floating, np.integer)):
        return value.item()
    if isinstance(value, dict):
        return {str(k): _jsonify(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonify(v) for v in value]
    return value


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_jsonify(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fill_grid(lo: float, hi: float, step: float) -> np.ndarray:
    count = int(round((float(hi) - float(lo)) / float(step)))
    return np.asarray([float(lo) + float(step) * i for i in range(count + 1)], dtype=np.float64)


def _build_frequency_sets(base_xi: np.ndarray) -> dict[str, np.ndarray]:
    base_xi = np.asarray(base_xi, dtype=np.float64)
    e1_xi = e1c._build_e1_frequencies(base_xi)
    e2f_xi = np.union1d(base_xi, _fill_grid(4.0, 16.0, 0.0625))
    e3f_xi = np.union1d(base_xi, _fill_grid(2.0, 20.0, 0.125))
    return {"base": base_xi, "e1": e1_xi, "e2f": e2f_xi, "e3f": e3f_xi}


def _inclusion_check(freqs: dict[str, np.ndarray]) -> dict[str, Any]:
    base = freqs["base"]
    e1 = freqs["e1"]
    out: dict[str, Any] = {
        "base_frequency_count": int(base.size),
        "e1_frequency_count": int(e1.size),
    }
    for family in ("e2f", "e3f"):
        xi = freqs[family]
        missing_base = np.setdiff1d(base, xi)
        missing_e1 = np.setdiff1d(e1, xi)
        out[family] = {
            "frequency_count": int(xi.size),
            "strict_superset_of_base": bool(xi.size > base.size and missing_base.size == 0),
            "strict_superset_of_e1": bool(xi.size > e1.size and missing_e1.size == 0),
            "missing_base_frequency_count": int(missing_base.size),
            "missing_e1_frequency_count": int(missing_e1.size),
            "extra_vs_base_count": int(np.setdiff1d(xi, base).size),
            "extra_vs_e1_count": int(np.setdiff1d(xi, e1).size),
        }
    out["all_requested_inclusions_pass"] = bool(
        out["e2f"]["strict_superset_of_base"]
        and out["e2f"]["strict_superset_of_e1"]
        and out["e3f"]["strict_superset_of_base"]
        and out["e3f"]["strict_superset_of_e1"]
    )
    return out


def _cache_path(family: str, anchor_m: float) -> Path:
    safe = f"{float(anchor_m):.7f}".replace(".", "p")
    return ROW_CACHE_DIR / f"{family}_m_{safe}.json"


def _load_cached_new_row(family: str, anchor_m: float) -> dict[str, Any] | None:
    path = _cache_path(family, anchor_m)
    if not path.exists():
        return None
    payload = _load_json(path)
    row = payload.get("row")
    if row and row.get("exact_positive_part_budget", {}).get("exact_budget_pass") and row.get("real_generator_gate_pass"):
        payload = dict(payload)
        payload["cache_status"] = "loaded_from_cache"
        return payload
    return None


def _load_inherited_payloads() -> list[dict[str, Any]]:
    inherited = _load_json(INHERITED_JSON)
    payloads: list[dict[str, Any]] = []
    for summary in inherited.get("completed_rows", []):
        path = Path(summary["cache_path"])
        if not path.exists() and not path.is_absolute():
            path = INHERITED_ROW_CACHE_DIR / path.name
        payload = _load_json(path)
        row = payload.get("row")
        if not row:
            continue
        if not row.get("exact_positive_part_budget", {}).get("exact_budget_pass"):
            continue
        if not row.get("real_generator_gate_pass"):
            continue
        payload = dict(payload)
        payload["cache_status"] = "inherited_from_soc_full_envelope"
        payloads.append(payload)
    return payloads


def _row_for_exact_budget(comp: dict[str, Any], anchor_m: float, family: str) -> dict[str, Any]:
    return {
        "id": f"{family}_anchor_m_{anchor_m:.7f}",
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


def _comb_description(family: str) -> str:
    if family == "e2f":
        return "base K=400 plus 0.0625-grid fill on [4,16]"
    if family == "e3f":
        return "base K=400 plus 0.125-grid fill on [2,20]"
    return str(family)


def _hardened_row(comp: dict[str, Any], budget: dict[str, Any], anchor_m: float, family: str) -> dict[str, Any]:
    alpha = np.asarray(comp["alpha"], dtype=np.float64)
    beta = np.asarray(comp["beta"], dtype=np.float64)
    return {
        "id": f"{family}_anchor_m_{anchor_m:.7f}",
        "family": str(family),
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
            "description": f"{family} fixed-mean SOC witness.",
            "comb_rule": _comb_description(family),
        },
    }


def _solve_and_harden_row(xi: np.ndarray, anchor_m: float, family: str) -> dict[str, Any]:
    cached = _load_cached_new_row(family, anchor_m)
    if cached is not None:
        print(f"row_cache_hit family={family} m={anchor_m:.7f}", flush=True)
        return cached

    print(f"row_solve_start family={family} m={anchor_m:.7f}", flush=True)
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
        f"row_nominal_done family={family} m={anchor_m:.7f} raw={comp['raw_L']:.15f} "
        f"status={sol['solver_status']} active_freq={comp['selected_frequency_count']} "
        f"solve_seconds={sol['solve_elapsed_seconds']:.2f}",
        flush=True,
    )
    budget_row = _row_for_exact_budget(comp, anchor_m, family)
    budget = e1c._exact_budget_for_row(budget_row, grid_n=ROOT_GRID_N, dps=EXACT_DPS)
    row = _hardened_row(comp, budget, anchor_m, family)
    payload = {
        "schema": "public cached exact-hardened SOC frequency-enrichment row v1",
        "family": str(family),
        "anchor_m": float(anchor_m),
        "comb_description": _comb_description(family),
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
    _write_json(_cache_path(family, anchor_m), payload)
    print(
        f"row_hardened_done family={family} m={anchor_m:.7f} "
        f"L_source={payload['row_value_at_source_m']:.15f} "
        f"shift={payload['exact_shift']:.12e} budget_margin={payload['positive_part_margin']:.3e} "
        f"elapsed={payload['total_elapsed_seconds']:.1f}",
        flush=True,
    )
    return payload


def _row_value(row: dict[str, Any], m: float) -> float:
    mm = float(m)
    return float(row["quadratic_c0_lower"]) + float(row["a1"]) * mm + 0.5 * float(row["a2"]) * mm * mm


def _best_row_value(rows: list[dict[str, Any]], m: float, family: str | None = None) -> dict[str, Any]:
    candidates = rows
    if family is not None:
        candidates = [r for r in rows if r.get("family") == family or r["id"].startswith(f"{family}_")]
    if not candidates:
        return {"status": "no_rows", "value": None, "row_id": None}
    vals = np.asarray([_row_value(row, m) for row in candidates], dtype=np.float64)
    idx = int(np.argmax(vals))
    return {"status": "success", "value": float(vals[idx]), "row_id": candidates[idx]["id"]}


def _envelopes_by_bracket(
    base_rows: list[dict[str, Any]],
    inherited_rows: list[dict[str, Any]],
    new_rows: list[dict[str, Any]],
    base_repro: dict[str, Any],
    mean_guard: float,
) -> dict[str, dict[str, Any]]:
    e2f_rows = [r for r in new_rows if r.get("family") == "e2f"]
    e3f_rows = [r for r in new_rows if r.get("family") == "e3f"]
    out: dict[str, dict[str, Any]] = {}
    for blo, bhi in ACTIVE_BRACKETS:
        key = f"{blo:.3f}_{bhi:.3f}"
        out[key] = {
            "inherited": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows,
                    mean_guard,
                    "inherited_reference_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "with_e2f": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + e2f_rows,
                    mean_guard,
                    "inherited_plus_e2f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "with_e3f": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + e3f_rows,
                    mean_guard,
                    "inherited_plus_e3f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "union_all": sfe._apply_baseline_floor(
                sfe._envelope(
                    list(base_rows) + inherited_rows + new_rows,
                    mean_guard,
                    "inherited_plus_e2f_e3f_rows",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
        }
    return out


def _best_outside_passing(bracket_envelopes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    by_bracket: dict[str, Any] = {}
    best: dict[str, Any] | None = None
    for bracket_key, envs in bracket_envelopes.items():
        passing = []
        for family, env in envs.items():
            if env["outside_exclusion_pass"]:
                passing.append((float(env["certified_global"]), family, env))
        if passing:
            value, family, env = max(passing, key=lambda item: item[0])
            entry = {
                "active_bracket": bracket_key,
                "family": family,
                "certified_global": float(value),
                "delta_vs_plateau": float(value - PREVIOUS_PLATEAU),
                "delta_vs_base": float(value - BASE_CERTIFIED_GLOBAL),
                "plateau_change_lt_1e_6": bool(abs(value - PREVIOUS_PLATEAU) < 1.0e-6),
                "global_argmin_m": float(env["global_argmin_m"]),
                "global_controlling_row": env["global_controlling_row"],
                "outside_exclusion_margin": float(env["outside_exclusion_margin"]),
            }
        else:
            entry = {"active_bracket": bracket_key, "status": "no_outside_passing_envelope"}
        by_bracket[bracket_key] = entry
        if "certified_global" in entry and (best is None or entry["certified_global"] > best["certified_global"]):
            best = entry
    return {"by_bracket": by_bracket, "overall": best}


def _row_summary(payloads: list[dict[str, Any]]) -> list[dict[str, Any]]:
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
            "cache_path": str(_cache_path(str(p["family"]), float(p["anchor_m"]))),
            "cache_status": str(p.get("cache_status", "unknown")),
        }
        for p in payloads
    ]


def _comparison_summary(
    base_rows: list[dict[str, Any]],
    inherited_rows: list[dict[str, Any]],
    new_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    all_inherited = list(base_rows) + inherited_rows
    inherited_control = next(row for row in base_rows if row["id"] == INHERITED_CONTROL_ROW_ID)
    inherited_control_value = _row_value(inherited_control, REFERENCE_M)
    inherited_best = _best_row_value(all_inherited, REFERENCE_M)
    e1_best = _best_row_value(inherited_rows, REFERENCE_M, family="e1")
    out: dict[str, Any] = {
        "reference_m": REFERENCE_M,
        "inherited_control_row_id": INHERITED_CONTROL_ROW_ID,
        "inherited_control_value": float(inherited_control_value),
        "inherited_best_at_reference": inherited_best,
        "e1_best_at_reference": e1_best,
        "new_rows_at_reference": [],
        "per_comb_at_control_anchor": {},
    }
    for row in sorted(new_rows, key=lambda r: (r.get("family", ""), float(r["m"]))):
        value = _row_value(row, REFERENCE_M)
        item = {
            "family": row.get("family"),
            "row_id": row["id"],
            "source_m": float(row["m"]),
            "value_at_reference_m": float(value),
            "delta_vs_inherited_control": float(value - inherited_control_value),
            "delta_vs_inherited_best": (
                float(value - inherited_best["value"]) if inherited_best["value"] is not None else None
            ),
            "delta_vs_e1_best": float(value - e1_best["value"]) if e1_best["value"] is not None else None,
            "dominates_inherited_control": bool(value > inherited_control_value),
            "dominates_inherited_best": bool(inherited_best["value"] is not None and value > inherited_best["value"]),
            "beats_e1_best": bool(e1_best["value"] is not None and value > e1_best["value"]),
        }
        out["new_rows_at_reference"].append(item)
        if abs(float(row["m"]) - REFERENCE_M) <= 5.0e-13:
            out["per_comb_at_control_anchor"][str(row.get("family"))] = item
    out["enriched_comb_dominates_inherited_at_reference"] = bool(
        any(item["dominates_inherited_best"] for item in out["new_rows_at_reference"])
    )
    out["e2f_beats_e1_at_control_anchor"] = bool(
        out["per_comb_at_control_anchor"].get("e2f", {}).get("beats_e1_best", False)
    )
    out["e3f_beats_e1_at_control_anchor"] = bool(
        out["per_comb_at_control_anchor"].get("e3f", {}).get("beats_e1_best", False)
    )
    return out


def _assemble_result(
    *,
    started: float,
    base_rows: list[dict[str, Any]],
    inherited_payloads: list[dict[str, Any]],
    completed_payloads: list[dict[str, Any]],
    skipped: list[dict[str, Any]],
    recovered: dict[str, Any],
    base_repro: dict[str, Any],
    inclusion_check: dict[str, Any],
    mean_guard: float,
    status: str,
) -> dict[str, Any]:
    inherited_rows = [p["row"] for p in inherited_payloads]
    new_rows = [p["row"] for p in completed_payloads]
    bracket_envelopes = _envelopes_by_bracket(base_rows, inherited_rows, new_rows, base_repro, mean_guard)
    best = _best_outside_passing(bracket_envelopes)
    comparison = _comparison_summary(base_rows, inherited_rows, new_rows)
    union_003 = bracket_envelopes["0.000_0.030"]["union_all"]
    union_004 = bracket_envelopes["0.000_0.040"]["union_all"]
    return {
        "schema": "public SOC frequency enrichment beyond E1 v1",
        "status": status,
        "elapsed_seconds": float(time.time() - started),
        "base_reproduction": base_repro,
        "recovered_exact_budget_row": recovered,
        "inclusion_check": inclusion_check,
        "anchors_requested": ANCHORS,
        "priority_schedule": [{"family": f, "anchor_m": m} for f, m in PRIORITY_SCHEDULE],
        "completed_new_row_count": int(len(completed_payloads)),
        "inherited_payload_count": int(len(inherited_payloads)),
        "completed_rows": _row_summary(completed_payloads),
        "skipped_or_failed_rows": skipped,
        "bracket_envelopes": bracket_envelopes,
        "best_outside_passing": best,
        "reference_comparisons": comparison,
        "gate_summary": {
            "base_reproduction": bool(base_repro["pass"]),
            "inclusion": bool(inclusion_check["all_requested_inclusions_pass"]),
            "new_rows_exact_budget_all_completed": bool(
                all(p["row"]["exact_positive_part_budget"]["exact_budget_pass"] for p in completed_payloads)
            ),
            "new_rows_real_generator_all_completed": bool(
                all(p["row"]["real_generator_gate_pass"] for p in completed_payloads)
            ),
            "union_0_03_outside_exclusion": bool(union_003["outside_exclusion_pass"]),
            "union_0_04_outside_exclusion": bool(union_004["outside_exclusion_pass"]),
            "union_smoke_under_known_feasible": bool(
                union_003["certified_global"] <= KNOWN_FEASIBLE_GUARD
                and union_004["certified_global"] <= KNOWN_FEASIBLE_GUARD
            ),
            "certified_claim_allowed": bool(
                base_repro["pass"]
                and inclusion_check["all_requested_inclusions_pass"]
                and union_003["outside_exclusion_pass"]
                and union_004["outside_exclusion_pass"]
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
            "previous_plateau": PREVIOUS_PLATEAU,
            "base_certified_global": BASE_CERTIFIED_GLOBAL,
        },
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "inherited_envelope": str(INHERITED_JSON),
            "inherited_row_cache_dir": str(INHERITED_ROW_CACHE_DIR),
            "new_row_cache_dir": str(ROW_CACHE_DIR),
            "output_json": str(OUT_JSON),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
        },
    }


def run_frequency_enrichment_analysis(*, max_total_seconds: float = 1680.0) -> dict[str, Any]:
    started = time.time()
    base_cert = _load_json(BASE_CERT_PATH)
    exact_budget_summary = _load_json(BASE_EXACT_BUDGET_PATH)
    mean_guard = float(base_cert["verification_settings"]["mean_guard"])
    base_rows, recovered = smh.build_verified_rows_with_baseline_recovery(base_cert, exact_budget_summary)
    base_repro = sfe._base_reproduction(base_rows, mean_guard)
    if not base_repro["pass"]:
        raise RuntimeError(f"base reproduction integrity control failed: {base_repro}")
    print(
        f"base_reproduction_integrity={base_repro['value']:.15f} "
        f"expected={BASE_CERTIFIED_GLOBAL:.15f} argmin_m={base_repro['argmin_m']:.7f}",
        flush=True,
    )

    freqs = _build_frequency_sets(e1c._base_frequencies(base_cert))
    inclusion_check = _inclusion_check(freqs)
    if not inclusion_check["all_requested_inclusions_pass"]:
        raise RuntimeError(f"frequency inclusion check failed: {inclusion_check}")
    print(
        "inclusion_check "
        f"base={inclusion_check['base_frequency_count']} e1={inclusion_check['e1_frequency_count']} "
        f"e2f={inclusion_check['e2f']['frequency_count']} e3f={inclusion_check['e3f']['frequency_count']} "
        f"e2f_superset={inclusion_check['e2f']['strict_superset_of_e1']} "
        f"e3f_superset={inclusion_check['e3f']['strict_superset_of_e1']}",
        flush=True,
    )

    inherited_payloads = _load_inherited_payloads()
    print(f"inherited_hardened_rows_loaded={len(inherited_payloads)}", flush=True)

    completed: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for family, anchor_m in PRIORITY_SCHEDULE:
        elapsed = time.time() - started
        cached = _load_cached_new_row(family, anchor_m)
        if cached is None and elapsed > float(max_total_seconds) - 240.0:
            skipped.append(
                {
                    "family": family,
                    "anchor_m": float(anchor_m),
                    "reason": "compute_limit_guard",
                    "elapsed_seconds_before_row": float(elapsed),
                }
            )
            print(f"row_skipped_compute_guard family={family} m={anchor_m:.7f} elapsed={elapsed:.1f}", flush=True)
            continue
        try:
            payload = _solve_and_harden_row(freqs[family], anchor_m, family)
        except Exception as exc:  # noqa: BLE001
            skipped.append({"family": family, "anchor_m": float(anchor_m), "reason": "row_exception", "error": repr(exc)})
            print(f"row_failed family={family} m={anchor_m:.7f} error={exc!r}", flush=True)
            continue
        completed.append(payload)
        partial = _assemble_result(
            started=started,
            base_rows=base_rows,
            inherited_payloads=inherited_payloads,
            completed_payloads=completed,
            skipped=skipped,
            recovered=recovered,
            base_repro=base_repro,
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
        completed_payloads=completed,
        skipped=skipped,
        recovered=recovered,
        base_repro=base_repro,
        inclusion_check=inclusion_check,
        mean_guard=mean_guard,
        status=status,
    )
    _write_json(OUT_JSON, result)
    _write_json(OUT_JSON_ROOT_COPY, result)

    print("frequency_enrichment_summary_begin", flush=True)
    ref = result["reference_comparisons"]
    print(
        f"reference_m={ref['reference_m']:.7f} inherited_control={ref['inherited_control_value']:.15f} "
        f"inherited_best={ref['inherited_best_at_reference']['value']:.15f} "
        f"e1_best={ref['e1_best_at_reference']['value']:.15f}",
        flush=True,
    )
    for family in ("e2f", "e3f"):
        item = ref["per_comb_at_control_anchor"].get(family)
        if item:
            print(
                f"{family}_control_anchor value={item['value_at_reference_m']:.15f} "
                f"delta_vs_inherited={item['delta_vs_inherited_best']:.12e} "
                f"delta_vs_e1={item['delta_vs_e1_best']:.12e} "
                f"dominates_inherited={item['dominates_inherited_best']} beats_e1={item['beats_e1_best']}",
                flush=True,
            )
        else:
            print(f"{family}_control_anchor status=missing_or_skipped", flush=True)
    for bracket_key, envs in result["bracket_envelopes"].items():
        env = envs["union_all"]
        print(
            f"union_all bracket={bracket_key} value={env['certified_global']:.15f} "
            f"argmin={env['global_argmin_m']:.7f} controlling={env['global_controlling_row']} "
            f"outside_pass={env['outside_exclusion_pass']} "
            f"delta_vs_plateau={env['certified_global'] - PREVIOUS_PLATEAU:.12e}",
            flush=True,
        )
    best = result["best_outside_passing"]["overall"]
    if best:
        print(
            f"best_outside_passing value={best['certified_global']:.15f} "
            f"bracket={best['active_bracket']} family={best['family']} "
            f"delta_vs_plateau={best['delta_vs_plateau']:.12e} "
            f"plateau_lt_1e-6={best['plateau_change_lt_1e_6']}",
            flush=True,
        )
    print(f"saved_json={OUT_JSON}", flush=True)
    return result


if __name__ == "__main__":
    run_frequency_enrichment_analysis()
