"""Dense-anchor SOC envelope recomputation for a predecessor computation.

This driver extends the a predecessor computation E1-anchor diagnostic to two cached row
families:

* BASE K=400 comb rows at new mean anchors.
* E1 rows on the strict superset comb, base plus 0.125 fill on [4, 16].

Every completed row is exact-budget hardened with the a predecessor computation/1015
mpmath/root-isolation path before it is allowed into an m-envelope.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any

import numpy as np

import sys

sys.path.insert(0, "source")
import soc_dual as sd  # noqa: E402
import soc_e1_certificate as e1c  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402
import verify_cert_improved as vci  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
BASE_CERT_PATH = ROOT / "soc_certificate_improved.json"
BASE_EXACT_BUDGET_PATH = DATA / "soc_budget_exact.json"
OUT_JSON = DATA / "soc_full_envelope.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_full_envelope.json"
ROW_CACHE_DIR = DATA / "soc_full_envelope_rows"

BASE_CERTIFIED_GLOBAL = 0.38043481690472875
PREVIOUS_OUTSIDE_PASSING = 0.380496768638831
KNOWN_FEASIBLE_GUARD = 0.380895
BASE_REPRO_BRACKET = (0.017, 0.023)
DENSE_ACTIVE_BRACKET = (0.0, 0.03)
REFINED_PARTITIONS = 60_000
DOMAIN_PARTITIONS = 400_000
ROOT_GRID_N = 1_000_000
ROOT_TOL = 5.0e-13
EXACT_DPS = 80

# Prioritize the low-mean region that was still controlling outside-exclusion,
# while retaining the previously cached low anchors from a predecessor computation.
LOW_ANCHORS = [
    0.002,
    0.003,
    0.0039975,
    0.004,
    0.005,
    0.006,
    0.007,
    0.008885,
    0.009,
    0.010,
    0.011,
    0.012,
    0.013,
    0.014,
    0.015,
    0.016,
    0.017,
    0.018,
    0.0197932,
    0.022,
    0.026,
    0.03,
]
COARSE_ANCHORS = [round(0.05 * i, 12) for i in range(1, 20)]
ALL_ANCHORS = sorted({round(float(x), 12) for x in (LOW_ANCHORS + COARSE_ANCHORS)})
ACTIVE_BRACKETS = [(0.0, 0.03), (0.0, 0.04)]


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


def _interval(v: float) -> list[str]:
    text = repr(float(v))
    return [text, text]


def _row_value(row: dict[str, Any], m: float | np.ndarray) -> float | np.ndarray:
    mm = np.asarray(m, dtype=np.float64)
    out = float(row["quadratic_c0_lower"]) + float(row["a1"]) * mm + 0.5 * float(row["a2"]) * mm * mm
    if np.ndim(m) == 0:
        return float(out)
    return out


def _base_reproduction(base_rows: list[dict[str, Any]], mean_guard: float) -> dict[str, Any]:
    refined = smh._envelope_table(
        base_rows,
        lo=BASE_REPRO_BRACKET[0],
        hi=BASE_REPRO_BRACKET[1],
        partitions=REFINED_PARTITIONS,
        mean_guard=mean_guard,
    )
    outside = smh._outside_minimum(
        base_rows,
        bracket_lo=BASE_REPRO_BRACKET[0],
        bracket_hi=BASE_REPRO_BRACKET[1],
        domain_lo=0.0,
        domain_hi=1.0,
        partitions=DOMAIN_PARTITIONS,
        mean_guard=mean_guard,
    )
    value = float(refined["certified_min_after_pad"])
    outside_value = float(outside["outside_min_after_pad"])
    return {
        "value": value,
        "expected": BASE_CERTIFIED_GLOBAL,
        "match_error": float(value - BASE_CERTIFIED_GLOBAL),
        "argmin_m": float(refined["argmin_m_grid"]),
        "outside_min_after_pad": outside_value,
        "outside_excluded": bool(outside_value > value),
        "pass": bool(abs(value - BASE_CERTIFIED_GLOBAL) <= 2.5e-9 and outside_value > value),
    }


def _row_for_exact_budget(comp: dict[str, Any], anchor_m: float, family: str) -> dict[str, Any]:
    return {
        "id": f"{family}_anchor_m_{anchor_m:.7f}",
        "m": float(anchor_m),
        "K": int(comp["selected_frequency_count"]),
        "positive_part_partitions": 200_000,
        "alpha_boundary_threshold": 1.0e-10,
        "coefficient_intervals": {
            "a0_raw": _interval(float(comp["a0"])),
            "a1": _interval(float(comp["a1"])),
            "a2": _interval(float(comp["a2"])),
        },
        "atom_intervals": {
            "xi": [_interval(float(v)) for v in np.asarray(comp["xi"], dtype=np.float64)],
            "alpha": [_interval(float(v)) for v in np.asarray(comp["alpha"], dtype=np.float64)],
            "beta": [_interval(float(v)) for v in np.asarray(comp["beta"], dtype=np.float64)],
        },
    }


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
            "comb_rule": "base K=400" if family == "base_k400" else "base K=400 plus 0.125-grid fill on [4,16]",
        },
    }


def _cache_path(family: str, anchor_m: float) -> Path:
    safe = f"{float(anchor_m):.7f}".replace(".", "p")
    return ROW_CACHE_DIR / f"{family}_m_{safe}.json"


def _load_cached_row(family: str, anchor_m: float) -> dict[str, Any] | None:
    path = _cache_path(family, anchor_m)
    if not path.exists():
        return None
    payload = _load_json(path)
    row = payload.get("row")
    if row and row.get("exact_positive_part_budget", {}).get("exact_budget_pass") and row.get("real_generator_gate_pass"):
        return payload
    return None


def _solve_and_harden_row(xi: np.ndarray, anchor_m: float, family: str) -> dict[str, Any]:
    cached = _load_cached_row(family, anchor_m)
    if cached is not None:
        print(f"row_cache_hit family={family} m={anchor_m:.7f}", flush=True)
        cached = dict(cached)
        cached["cache_status"] = "loaded_from_cache"
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
        "schema": "public cached exact-hardened SOC anchor row v1",
        "family": str(family),
        "anchor_m": float(anchor_m),
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


def _envelope(
    rows: list[dict[str, Any]],
    mean_guard: float,
    label: str,
    active_bracket: tuple[float, float] = DENSE_ACTIVE_BRACKET,
) -> dict[str, Any]:
    if not rows:
        return {"label": label, "status": "no_rows"}
    coarse = smh._envelope_table(rows, lo=0.0, hi=1.0, partitions=DOMAIN_PARTITIONS, mean_guard=mean_guard)
    blo, bhi = active_bracket
    refined = smh._envelope_table(rows, lo=blo, hi=bhi, partitions=REFINED_PARTITIONS, mean_guard=mean_guard)
    outside = smh._outside_minimum(
        rows,
        bracket_lo=blo,
        bracket_hi=bhi,
        domain_lo=0.0,
        domain_hi=1.0,
        partitions=DOMAIN_PARTITIONS,
        mean_guard=mean_guard,
    )
    refined_value = float(refined["certified_min_after_pad"])
    outside_value = float(outside["outside_min_after_pad"])
    outside_excluded = bool(outside_value > refined_value)
    if outside_excluded:
        final = refined_value
        source = "refined_bracket"
        argmin = float(refined["argmin_m_grid"])
        controlling = refined["active_witnesses_at_argmin"][0]["row_id"]
    else:
        final = min(refined_value, outside_value)
        source = "outside_bracket" if outside_value <= refined_value else "refined_bracket_not_excluding_outside"
        argmin = float(outside["outside_argmin_m_grid"]) if outside_value <= refined_value else float(refined["argmin_m_grid"])
        controlling = outside["outside_controlling_row"] if outside_value <= refined_value else refined["active_witnesses_at_argmin"][0]["row_id"]
    return {
        "label": label,
        "status": "success",
        "row_count": int(len(rows)),
        "certified_global": float(final),
        "global_source": source,
        "global_argmin_m": float(argmin),
        "global_controlling_row": controlling,
        "outside_exclusion_pass": outside_excluded,
        "outside_exclusion_margin": float(outside_value - refined_value),
        "coarse_full_domain": {
            "partitions": DOMAIN_PARTITIONS,
            "argmin_m": float(coarse["argmin_m_grid"]),
            "certified_min_after_pad": float(coarse["certified_min_after_pad"]),
            "numeric_min_before_pad": float(coarse["numeric_min_before_pad"]),
            "controlling_rows": coarse["unique_grid_controlling_rows"],
        },
        "refined_bracket": {
            "interval": [blo, bhi],
            "partitions": REFINED_PARTITIONS,
            "argmin_m": float(refined["argmin_m_grid"]),
            "numeric_min_before_pad": float(refined["numeric_min_before_pad"]),
            "certified_min_after_pad": refined_value,
            "mean_variation_pad": float(refined["mean_variation_pad"]),
            "active_witnesses_at_argmin": refined["active_witnesses_at_argmin"],
            "unique_grid_controlling_rows": refined["unique_grid_controlling_rows"],
        },
        "outside_check": {
            "domain": [0.0, 1.0],
            "partitions": DOMAIN_PARTITIONS,
            "outside_min_after_pad": outside_value,
            "outside_argmin_m": float(outside["outside_argmin_m_grid"]),
            "outside_controlling_row": outside["outside_controlling_row"],
        },
    }


def _row_summary(payloads: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "family": p["family"],
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


def _pending_schedule() -> list[tuple[str, float]]:
    schedule: list[tuple[str, float]] = []
    for m in ALL_ANCHORS:
        schedule.append(("base_k400", m))
        schedule.append(("e1", m))
    return schedule


def _apply_baseline_floor(env: dict[str, Any], base_repro: dict[str, Any]) -> dict[str, Any]:
    floor = float(base_repro["value"])
    if float(env["certified_global"]) >= floor:
        env["baseline_floor_applied"] = False
        return env
    env = dict(env)
    env["raw_dense_bracket_certified_global"] = float(env["certified_global"])
    env["raw_dense_bracket_global_source"] = env["global_source"]
    env["certified_global"] = floor
    env["global_source"] = "independent_baseline_floor"
    env["global_argmin_m"] = float(base_repro["argmin_m"])
    env["global_controlling_row"] = smh.IMPROVED_ROW_ID
    env["outside_exclusion_pass"] = bool(base_repro["outside_excluded"])
    env["outside_exclusion_margin"] = float(base_repro["outside_min_after_pad"] - floor)
    env["baseline_floor_applied"] = True
    env["note"] = (
        "The dense active bracket produced a weaker padded lower bound than the "
        "independently verified base certificate; because this row set includes "
        "the base rows, the final certified value is floored by the base certificate."
    )
    return env


def _write_result_copies(payload: dict[str, Any]) -> None:
    _write_json(OUT_JSON, payload)
    _write_json(OUT_JSON_ROOT_COPY, payload)


def _best_outside_passing_by_bracket(
    bracket_envelopes: dict[str, dict[str, Any]], base_repro: dict[str, Any]
) -> dict[str, Any]:
    base_value = float(base_repro["value"])
    by_bracket: dict[str, Any] = {}
    overall: dict[str, Any] | None = None
    for bracket_key, envs in bracket_envelopes.items():
        passing = []
        for family in ("base_dense", "e1_dense", "union"):
            env = envs[family]
            if env["outside_exclusion_pass"]:
                passing.append((float(env["certified_global"]), family, env))
        if passing:
            value, family, env = max(passing, key=lambda item: item[0])
            entry = {
                "active_bracket": bracket_key,
                "family": family,
                "certified_global": float(value),
                "delta_vs_baseline": float(value - base_value),
                "delta_vs_previous_round": float(value - PREVIOUS_OUTSIDE_PASSING),
                "plateau_vs_previous_round_lt_1e_6": bool(abs(value - PREVIOUS_OUTSIDE_PASSING) < 1.0e-6),
                "global_argmin_m": float(env["global_argmin_m"]),
                "global_controlling_row": env["global_controlling_row"],
                "outside_exclusion_margin": float(env["outside_exclusion_margin"]),
            }
        else:
            entry = {"active_bracket": bracket_key, "status": "no_outside_passing_added_envelope"}
        by_bracket[bracket_key] = entry
        if "certified_global" in entry and (overall is None or entry["certified_global"] > overall["certified_global"]):
            overall = entry
    return {
        "previous_round_outside_passing": PREVIOUS_OUTSIDE_PASSING,
        "by_bracket": by_bracket,
        "overall": overall,
    }


def run_full_envelope_analysis(*, max_total_seconds: float = 1680.0) -> dict[str, Any]:
    started = time.time()
    base_cert = _load_json(BASE_CERT_PATH)
    exact_budget_summary = _load_json(BASE_EXACT_BUDGET_PATH)
    mean_guard = float(base_cert["verification_settings"]["mean_guard"])
    base_rows, recovered = smh.build_verified_rows_with_baseline_recovery(base_cert, exact_budget_summary)
    base_repro = _base_reproduction(base_rows, mean_guard)
    if not base_repro["pass"]:
        raise RuntimeError(f"base reproduction integrity control failed: {base_repro}")
    print(
        f"base_reproduction_integrity={base_repro['value']:.15f} "
        f"argmin_m={base_repro['argmin_m']:.7f}",
        flush=True,
    )

    base_xi = e1c._base_frequencies(base_cert)
    e1_xi = e1c._build_e1_frequencies(base_xi)
    inclusion_check = {
        "base_frequency_count": int(base_xi.size),
        "e1_frequency_count": int(e1_xi.size),
        "strict_superset": bool(base_xi.size < e1_xi.size and np.setdiff1d(base_xi, e1_xi).size == 0),
        "missing_base_frequency_count": int(np.setdiff1d(base_xi, e1_xi).size),
    }
    if not inclusion_check["strict_superset"]:
        raise RuntimeError(f"E1 inclusion check failed: {inclusion_check}")

    completed: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for family, anchor_m in _pending_schedule():
        elapsed = time.time() - started
        cached = _load_cached_row(family, anchor_m)
        if cached is None and elapsed > max_total_seconds - 240.0:
            skipped.append(
                {
                    "family": family,
                    "anchor_m": float(anchor_m),
                    "reason": "compute_limit_guard",
                    "elapsed_seconds_before_row": float(elapsed),
                }
            )
            continue
        xi = base_xi if family == "base_k400" else e1_xi
        try:
            payload = _solve_and_harden_row(xi, anchor_m, family)
        except Exception as exc:  # noqa: BLE001
            skipped.append({"family": family, "anchor_m": float(anchor_m), "reason": "row_exception", "error": repr(exc)})
            print(f"row_failed family={family} m={anchor_m:.7f} error={exc!r}", flush=True)
            continue
        completed.append(payload)
        # Persist a current aggregate after every newly solved row. Cache hits
        # are cheap and numerous in resume runs, so defer their aggregation.
        if payload.get("cache_status") == "newly_solved":
            partial = _assemble_result(
                started=started,
                base_rows=base_rows,
                completed_payloads=completed,
                skipped=skipped,
                recovered=recovered,
                base_repro=base_repro,
                inclusion_check=inclusion_check,
                mean_guard=mean_guard,
                status="partial_running",
            )
            _write_result_copies(partial)

    result = _assemble_result(
        started=started,
        base_rows=base_rows,
        completed_payloads=completed,
        skipped=skipped,
        recovered=recovered,
        base_repro=base_repro,
        inclusion_check=inclusion_check,
        mean_guard=mean_guard,
        status="complete_within_time_guard" if not skipped else "compute_limited",
    )
    _write_result_copies(result)

    print("envelope_summary_begin", flush=True)
    for bracket_key, envs in result["bracket_envelopes"].items():
        print(f"active_bracket={bracket_key}", flush=True)
        for key in ("baseline_reproduction", "base_dense", "e1_dense", "union"):
            env = envs[key]
            print(
                f"{key}: value={env['certified_global']:.15f} argmin={env['global_argmin_m']:.7f} "
                f"outside_pass={env['outside_exclusion_pass']} source={env['global_source']}",
                flush=True,
            )
    dec = result["lift_decomposition"]
    best = result["best_outside_passing"]
    if best["overall"] is not None:
        bo = best["overall"]
        print(
            f"best_outside_passing value={bo['certified_global']:.15f} "
            f"bracket={bo['active_bracket']} family={bo['family']} "
            f"argmin={bo['global_argmin_m']:.7f} "
            f"delta_vs_base={bo['delta_vs_baseline']:.12e} "
            f"delta_vs_previous={bo['delta_vs_previous_round']:.12e} "
            f"plateau_lt_1e-6={bo['plateau_vs_previous_round_lt_1e_6']}",
            flush=True,
        )
    print(
        f"certified_delta_vs_base={dec['union_delta_vs_baseline']:.12e} "
        f"L2_base_anchor_coverage={dec['base_dense_delta_vs_baseline']:.12e} "
        f"L1_e1_vs_base_dense={dec['e1_dense_minus_base_dense']:.12e}",
        flush=True,
    )
    print(f"saved_json={OUT_JSON}", flush=True)
    print(f"saved_json_root_copy={OUT_JSON_ROOT_COPY}", flush=True)
    return result


def _assemble_result(
    *,
    started: float,
    base_rows: list[dict[str, Any]],
    completed_payloads: list[dict[str, Any]],
    skipped: list[dict[str, Any]],
    recovered: dict[str, Any],
    base_repro: dict[str, Any],
    inclusion_check: dict[str, Any],
    mean_guard: float,
    status: str,
) -> dict[str, Any]:
    base_added = [p["row"] for p in completed_payloads if p["family"] == "base_k400"]
    e1_added = [p["row"] for p in completed_payloads if p["family"] == "e1"]
    loaded_from_cache = [p for p in completed_payloads if p.get("cache_status") == "loaded_from_cache"]
    newly_solved = [p for p in completed_payloads if p.get("cache_status") == "newly_solved"]
    baseline_env = {
        "label": "baseline_reproduction",
        "status": "success",
        "row_count": int(len(base_rows)),
        "certified_global": float(base_repro["value"]),
        "global_source": "base_reproduction_fixed_bracket",
        "global_argmin_m": float(base_repro["argmin_m"]),
        "global_controlling_row": smh.IMPROVED_ROW_ID,
        "outside_exclusion_pass": bool(base_repro["outside_excluded"]),
        "outside_exclusion_margin": float(base_repro["outside_min_after_pad"] - base_repro["value"]),
        "note": "Integrity-control value recomputed on the original reference bracket [0.017, 0.023].",
    }
    bracket_envelopes: dict[str, dict[str, Any]] = {}
    for blo, bhi in ACTIVE_BRACKETS:
        bracket_key = f"{blo:.3f}_{bhi:.3f}"
        bracket_envelopes[bracket_key] = {
            "baseline_reproduction": baseline_env,
            "base_dense": _apply_baseline_floor(
                _envelope(
                    list(base_rows) + base_added,
                    mean_guard,
                    "baseline_plus_base_k400_dense_anchors",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "e1_dense": _apply_baseline_floor(
                _envelope(
                    list(base_rows) + e1_added,
                    mean_guard,
                    "baseline_plus_e1_dense_anchors",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
            "union": _apply_baseline_floor(
                _envelope(
                    list(base_rows) + base_added + e1_added,
                    mean_guard,
                    "baseline_plus_base_and_e1_dense_anchors",
                    active_bracket=(blo, bhi),
                ),
                base_repro,
            ),
        }
    default_key = f"{ACTIVE_BRACKETS[0][0]:.3f}_{ACTIVE_BRACKETS[0][1]:.3f}"
    base_dense_env = bracket_envelopes[default_key]["base_dense"]
    e1_dense_env = bracket_envelopes[default_key]["e1_dense"]
    union_env = bracket_envelopes[default_key]["union"]
    base_value = float(base_repro["value"])
    base_dense_value = float(base_dense_env["certified_global"])
    e1_dense_value = float(e1_dense_env["certified_global"])
    union_value = float(union_env["certified_global"])
    best_outside_passing = _best_outside_passing_by_bracket(bracket_envelopes, base_repro)
    all_completed_gate_pass = bool(
        base_repro["pass"]
        and inclusion_check["strict_superset"]
        and all(p["row"]["exact_positive_part_budget"]["exact_budget_pass"] for p in completed_payloads)
        and all(p["row"]["real_generator_gate_pass"] for p in completed_payloads)
        and union_env["certified_global"] <= KNOWN_FEASIBLE_GUARD
    )
    outside_all_pass = {
        bracket_key: {
            "base_dense": bool(envs["base_dense"]["outside_exclusion_pass"]),
            "e1_dense": bool(envs["e1_dense"]["outside_exclusion_pass"]),
            "union": bool(envs["union"]["outside_exclusion_pass"]),
        }
        for bracket_key, envs in bracket_envelopes.items()
    }
    return {
        "schema": "public full-domain dense-anchor SOC envelope v1",
        "status": status,
        "elapsed_seconds": float(time.time() - started),
        "anchors_requested": ALL_ANCHORS,
        "low_anchor_priority": LOW_ANCHORS,
        "coarse_anchor_cover": COARSE_ANCHORS,
        "completed_row_count": int(len(completed_payloads)),
        "completed_base_k400_count": int(len(base_added)),
        "completed_e1_count": int(len(e1_added)),
        "loaded_from_cache_count": int(len(loaded_from_cache)),
        "newly_solved_count": int(len(newly_solved)),
        "completed_rows": _row_summary(completed_payloads),
        "skipped_or_failed_rows": skipped,
        "base_reproduction": base_repro,
        "recovered_exact_budget_row": recovered,
        "inclusion_check": inclusion_check,
        "gate_summary": {
            "base_reproduction": bool(base_repro["pass"]),
            "inclusion": bool(inclusion_check["strict_superset"]),
            "positive_part_exact_budget_all_completed": bool(
                all(p["row"]["exact_positive_part_budget"]["exact_budget_pass"] for p in completed_payloads)
            ),
            "real_generator_all_completed": bool(all(p["row"]["real_generator_gate_pass"] for p in completed_payloads)),
            "smoke_detector_union": bool(union_env["certified_global"] <= KNOWN_FEASIBLE_GUARD),
            "outside_exclusion": outside_all_pass,
            "all_completed_rows_gate_pass": all_completed_gate_pass,
        },
        "envelopes": {
            "baseline_reproduction": baseline_env,
            "base_dense": base_dense_env,
            "e1_dense": e1_dense_env,
            "union": union_env,
        },
        "bracket_envelopes": bracket_envelopes,
        "best_outside_passing": best_outside_passing,
        "lift_decomposition": {
            "baseline": base_value,
            "base_dense": base_dense_value,
            "e1_dense": e1_dense_value,
            "union": union_value,
            "base_dense_delta_vs_baseline": float(base_dense_value - base_value),
            "e1_dense_delta_vs_baseline": float(e1_dense_value - base_value),
            "union_delta_vs_baseline": float(union_value - base_value),
            "e1_dense_minus_base_dense": float(e1_dense_value - base_dense_value),
            "union_minus_base_dense": float(union_value - base_dense_value),
            "verdict": (
                "frequency_enrichment_dominates"
                if e1_dense_value - base_dense_value > base_dense_value - base_value
                else "anchor_coverage_dominates_or_tied"
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
            "dense_active_bracket": list(DENSE_ACTIVE_BRACKET),
            "mean_guard": float(mean_guard),
            "known_feasible_guard": KNOWN_FEASIBLE_GUARD,
        },
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "output_json": str(OUT_JSON),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
            "row_cache_dir": str(ROW_CACHE_DIR),
        },
    }


if __name__ == "__main__":
    run_full_envelope_analysis()
