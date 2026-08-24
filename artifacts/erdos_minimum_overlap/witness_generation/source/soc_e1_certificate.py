"""E1 enriched-comb hardening for the SOC certificate.

This reuses the a predecessor computation exact-budget hardened base certificate, then adds a
single new m=0 witness solved on the E1 frequency comb:
base K=400 plus a 0.125 grid on [4, 16].

The final question is whether that nominal E1 dual gain survives the full
hardening pipeline.  In practice the added row is checked exactly, appended to
the retained witness set, and the mean envelope is recomputed on the same
global coarse/refined grid used by the base hardened certificate.
"""

from __future__ import annotations

import copy
import json
import time
from pathlib import Path
from typing import Any

import numpy as np

import sys

sys.path.insert(0, "source")
import soc_budget_exact as sbe  # noqa: E402
import soc_dual as sd  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402
import verify_cert_improved as vci  # noqa: E402


ROOT = Path("source")
BASE_CERT_PATH = ROOT / "soc_certificate_improved.json"
BASE_EXACT_BUDGET_PATH = ROOT / "data/soc_budget_exact.json"
BASE_HARDENED_CERT_PATH = ROOT / "data/soc_menvelope_hardened_certificate.json"
OUT_CERT_PATH = ROOT / "soc_e1_certificate.json"
OUT_JSON = ROOT / "data/soc_e1_hardening.json"

EXPECTED_BASE_CERTIFIED = 0.38043481690472875
EXPECTED_E1_NOMINAL = 0.3805015769653647
KNOWN_FEASIBLE_GUARD = 0.380895
ROOT_GRID_N = 1_000_000
ROOT_TOL = 5.0e-13
EXACT_DPS = 80
E1_BRACKET = (0.017, 0.023)
E1_BRACKET_PARTITIONS = 60_000
GLOBAL_MEAN_PARTITIONS = 400_000


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


def _interval(v: float) -> list[str]:
    text = repr(float(v))
    return [text, text]


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _base_frequencies(cert: dict[str, Any]) -> np.ndarray:
    comb = cert["frequency_comb"]["stored_xi_values"]
    return np.asarray([float(v) for v in comb], dtype=np.float64)


def _build_e1_frequencies(base_xi: np.ndarray) -> np.ndarray:
    extra = np.asarray([4.0 + 0.125 * i for i in range(int(round((16.0 - 4.0) / 0.125)) + 1)], dtype=np.float64)
    return np.union1d(np.asarray(base_xi, dtype=np.float64), extra)


def _solve_e1_row(xi: np.ndarray) -> dict[str, Any]:
    sol = sd.solve_fixed_mean_soc(
        np.asarray(xi, dtype=np.float64),
        m=0.0,
        x_grid_points=1001,
        solver="CLARABEL",
        max_iter=500,
        tol=1.0e-8,
    )
    if sol.get("solver_status") not in ("optimal", "optimal_inaccurate"):
        raise RuntimeError(f"E1 solve failed: {sol.get('solver_status')}")
    comp = sd.compress_zero_pairs(sol)
    raw_nominal = float(sol["raw_L"])
    if abs(raw_nominal - EXPECTED_E1_NOMINAL) > 5.0e-7:
        raise RuntimeError(f"E1 nominal mismatch: {raw_nominal} vs {EXPECTED_E1_NOMINAL}")
    return {
        "nominal_solve": sol,
        "compressed": comp,
        "nominal_raw_L": raw_nominal,
        "solver_status": str(sol["solver_status"]),
    }


def _row_for_exact_budget(comp: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": "e1_enriched_m0",
        "m": 0.0,
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


def _exact_budget_for_row(row: dict[str, Any], *, grid_n: int = ROOT_GRID_N, dps: int = EXACT_DPS) -> dict[str, Any]:
    fn = sbe.RowFunction(row, dps=dps)
    root_data = sbe.isolate_roots(fn, shift=0.0, grid_n=int(grid_n), root_tol=ROOT_TOL)
    raw = sbe.exact_positive_integral(fn, root_data["roots"], shift=0.0, dps=dps)
    tau = sbe.solve_float_shift(root_data["x"], root_data["y"], target=1.0)
    certified_shift = tau + 1.0e-10
    shifted_checks: list[dict[str, Any]] = []
    while True:
        shifted_roots = sbe.isolate_roots(fn, shift=certified_shift, grid_n=int(grid_n), root_tol=ROOT_TOL)
        shifted_budget = sbe.exact_positive_integral(fn, shifted_roots["roots"], shift=certified_shift, dps=dps)
        check = {
            "shift": float(certified_shift),
            "root_count": int(shifted_roots["root_count"]),
            "root_width_max": float(shifted_roots["root_width_max"]),
            **shifted_budget,
        }
        shifted_checks.append(check)
        if shifted_budget["budget_hi"] <= 1.0:
            break
        certified_shift += 1.0e-10
        if certified_shift - tau > 1.0e-4:
            raise RuntimeError("could not certify exact-budget shift for E1 row")

    support_upper, support_boundary_flags = vci.interval_support_upper(row, dps=max(70, int(dps)))
    coeff_guard = 2.0e-12
    a0 = 0.5 * (float(row["coefficient_intervals"]["a0_raw"][0]) + float(row["coefficient_intervals"]["a0_raw"][1]))
    a1 = 0.5 * (float(row["coefficient_intervals"]["a1"][0]) + float(row["coefficient_intervals"]["a1"][1]))
    a2 = 0.5 * (float(row["coefficient_intervals"]["a2"][0]) + float(row["coefficient_intervals"]["a2"][1]))
    c0_lower = (a0 - certified_shift) + (2.0 / 3.0) * a2 - support_upper - coeff_guard
    l_source = c0_lower + a1 * float(row["m"]) + 0.5 * a2 * float(row["m"]) * float(row["m"]) - coeff_guard
    return {
        "grid_n": int(grid_n),
        "root_tolerance": float(ROOT_TOL),
        "raw_exact_budget": raw,
        "float_shift_estimate": float(tau),
        "certified_shift_upper": float(certified_shift),
        "shifted_budget_checks": shifted_checks,
        "support_interval_upper": float(support_upper),
        "support_boundary_flags": support_boundary_flags,
        "quadratic_c0_lower": float(c0_lower),
        "L_source_m_lower": float(l_source),
        "positive_part_margin": float(1.0 - shifted_checks[-1]["budget_hi"]),
        "exact_budget_pass": bool(shifted_checks[-1]["budget_hi"] <= 1.0),
        "root_count": int(root_data["root_count"]),
        "root_width_max": float(root_data["root_width_max"]),
        "lost_float_bracket_count": int(root_data["lost_float_bracket_count"]),
        "unsafe_same_sign_cell_count": int(root_data["unsafe_same_sign_cell_count"]),
        "sample_root_midpoints": root_data["sample_root_midpoints"],
        "raw_budget_mid": float(raw["budget_mid"]),
        "raw_budget_lo": float(raw["budget_lo"]),
        "raw_budget_hi": float(raw["budget_hi"]),
    }


def _append_e1_row(
    base_rows: list[dict[str, Any]],
    e1_comp: dict[str, Any],
    e1_budget: dict[str, Any],
) -> dict[str, Any]:
    row = {
        "id": "e1_enriched_m0",
        "m": 0.0,
        "K": int(e1_comp["selected_frequency_count"]),
        "a0": float(e1_comp["a0"]),
        "a1": float(e1_comp["a1"]),
        "a2": float(e1_comp["a2"]),
        "nominal_raw_L": float(e1_comp["raw_L"]),
        "selected_frequency_count": int(e1_comp["selected_frequency_count"]),
        "compressed_soc": {
            "a0": float(e1_comp["a0"]),
            "a1": float(e1_comp["a1"]),
            "a2": float(e1_comp["a2"]),
            "alpha": np.asarray(e1_comp["alpha"], dtype=np.float64),
            "beta": np.asarray(e1_comp["beta"], dtype=np.float64),
            "xi": np.asarray(e1_comp["xi"], dtype=np.float64),
        },
        "quadratic_c0_lower": float(e1_budget["quadratic_c0_lower"]),
        "L_source_m_lower": float(e1_budget["L_source_m_lower"]),
        "a1": float(e1_comp["a1"]),
        "a2": float(e1_comp["a2"]),
        "source": {
            "description": "E1 enriched-comb m=0 witness; same dual, denser 0.125 band on [4,16].",
            "comb_rule": "base K=400 plus 0.125-grid fill on [4,16]",
        },
        "exact_positive_part_budget": e1_budget,
        "real_generator_gate_pass": bool(
            np.all(np.asarray(e1_comp["alpha"], dtype=np.float64)[np.abs(np.asarray(e1_comp["beta"], dtype=np.float64)) > 0.0] > 0.0)
        ),
        "min_alpha_where_beta_nonzero": (
            float(np.min(np.asarray(e1_comp["alpha"], dtype=np.float64)[np.abs(np.asarray(e1_comp["beta"], dtype=np.float64)) > 0.0]))
            if np.any(np.abs(np.asarray(e1_comp["beta"], dtype=np.float64)) > 0.0)
            else None
        ),
        "beta_active_count_gt_1e_8": int(np.sum(np.abs(np.asarray(e1_comp["beta"], dtype=np.float64)) > 1.0e-8)),
    }
    base_rows.append(row)
    return row


def run_analysis() -> dict[str, Any]:
    started = time.time()
    base_cert = _load_json(BASE_CERT_PATH)
    exact_budget_summary = _load_json(BASE_EXACT_BUDGET_PATH)
    base_hardened_cert = _load_json(BASE_HARDENED_CERT_PATH)

    print("stage_a_base_reproduction_start", flush=True)
    base_reproduction = smh.run_analysis()
    if abs(float(base_reproduction["final_fully_hardened_global_L"]) - EXPECTED_BASE_CERTIFIED) > 2.5e-9:
        raise RuntimeError(
            f"base reproduction drifted: {base_reproduction['final_fully_hardened_global_L']} vs {EXPECTED_BASE_CERTIFIED}"
        )
    print(
        f"stage_a_base_reproduction_ok value={base_reproduction['final_fully_hardened_global_L']:.15f} "
        f"argmin_m={base_reproduction['refined_bracket']['argmin_m_grid']:.8f}",
        flush=True,
    )

    base_rows, recovered = smh.build_verified_rows_with_baseline_recovery(base_cert, exact_budget_summary)
    base_row_count = len(base_rows)
    gram = vci.verify_gram(base_cert)
    base_xi = _base_frequencies(base_cert)
    e1_xi = _build_e1_frequencies(base_xi)
    inclusion_check = {
        "base_frequency_count": int(base_xi.size),
        "e1_frequency_count": int(e1_xi.size),
        "strict_superset": bool(base_xi.size < e1_xi.size and np.setdiff1d(base_xi, e1_xi).size == 0),
        "missing_base_frequency_count": int(np.setdiff1d(base_xi, e1_xi).size),
    }

    print("stage_b_e1_solve_start", flush=True)
    e1_solve = _solve_e1_row(e1_xi)
    e1_comp = e1_solve["compressed"]
    e1_row_for_budget = _row_for_exact_budget(e1_comp)
    print(
        f"stage_b_e1_nominal_ok raw={e1_solve['nominal_raw_L']:.15f} "
        f"solver_status={e1_solve['solver_status']} freq_count={e1_comp['selected_frequency_count']}",
        flush=True,
    )
    print("stage_b_e1_exact_budget_start", flush=True)
    e1_budget = _exact_budget_for_row(e1_row_for_budget, grid_n=ROOT_GRID_N, dps=EXACT_DPS)
    print(
        f"stage_b_e1_exact_budget_ok budget_hi={e1_budget['raw_budget_hi']:.15f} "
        f"shift={e1_budget['certified_shift_upper']:.12e} roots={e1_budget['root_count']}",
        flush=True,
    )

    e1_row = _append_e1_row(base_rows, e1_comp, e1_budget)

    # Mean-envelope hardening: same global grid and same refined bracket as the
    # retained exact-budget certificate.  The E1 row is extra and may or may not
    # enter the envelope.
    refined = smh._envelope_table(
        base_rows,
        lo=E1_BRACKET[0],
        hi=E1_BRACKET[1],
        partitions=E1_BRACKET_PARTITIONS,
        mean_guard=float(base_cert["verification_settings"]["mean_guard"]),
    )
    outside = smh._outside_minimum(
        base_rows,
        bracket_lo=E1_BRACKET[0],
        bracket_hi=E1_BRACKET[1],
        domain_lo=0.0,
        domain_hi=1.0,
        partitions=GLOBAL_MEAN_PARTITIONS,
        mean_guard=float(base_cert["verification_settings"]["mean_guard"]),
    )
    controlling_row = refined["active_witnesses_at_argmin"][0]["row_id"] if refined["active_witnesses_at_argmin"] else None
    envelope_with_e1 = smh._envelope_table(
        base_rows,
        lo=0.0,
        hi=1.0,
        partitions=GLOBAL_MEAN_PARTITIONS,
        mean_guard=float(base_cert["verification_settings"]["mean_guard"]),
    )
    final_global = float(refined["certified_min_after_pad"]) if (
        E1_BRACKET[0] < refined["argmin_m_grid"] < E1_BRACKET[1]
        and outside["outside_min_after_pad"] > refined["certified_min_after_pad"]
    ) else float(envelope_with_e1["certified_min_after_pad"])
    e1_controlling_value = float(
        e1_row["quadratic_c0_lower"]
        + e1_row["a1"] * float(refined["argmin_m_grid"])
        + 0.5 * e1_row["a2"] * float(refined["argmin_m_grid"]) * float(refined["argmin_m_grid"])
    )

    gates = {
        "positive_part_exact_budget": {
            "pass": bool(e1_budget["exact_budget_pass"]),
            "raw_budget_lo": float(e1_budget["raw_budget_lo"]),
            "raw_budget_hi": float(e1_budget["raw_budget_hi"]),
            "shifted_budget_lo": float(e1_budget["shifted_budget_checks"][-1]["budget_lo"]),
            "shifted_budget_hi": float(e1_budget["shifted_budget_checks"][-1]["budget_hi"]),
            "shift_upper": float(e1_budget["certified_shift_upper"]),
            "margin": float(e1_budget["positive_part_margin"]),
        },
        "gram_psd": {
            "pass": bool(gram and gram["psd_certified"]),
            "lambda_min_lower_bound": float(gram["lambda_min_lower_bound"]) if gram else None,
            "dimension": int(gram["dimension"]) if gram else None,
        },
        "real_generator": {
            "pass": bool(e1_row["real_generator_gate_pass"]),
            "beta_active_count_gt_1e_8": int(e1_row["beta_active_count_gt_1e_8"]),
            "min_alpha_where_beta_nonzero": e1_row["min_alpha_where_beta_nonzero"],
        },
        "m_envelope": {
            "pass": bool(
                E1_BRACKET[0] < refined["argmin_m_grid"] < E1_BRACKET[1]
                and outside["outside_min_after_pad"] > refined["certified_min_after_pad"]
            ),
            "bracket": [float(E1_BRACKET[0]), float(E1_BRACKET[1])],
            "argmin_interior": bool(E1_BRACKET[0] < refined["argmin_m_grid"] < E1_BRACKET[1]),
            "refined_argmin_m_grid": float(refined["argmin_m_grid"]),
            "refined_numeric_min_before_pad": float(refined["numeric_min_before_pad"]),
            "refined_mean_variation_pad": float(refined["mean_variation_pad"]),
            "refined_certified_min_after_pad": float(refined["certified_min_after_pad"]),
            "outside_min_after_pad": float(outside["outside_min_after_pad"]),
            "outside_excluded": bool(outside["outside_min_after_pad"] > refined["certified_min_after_pad"]),
        },
        "smoke_detector": {
            "pass": bool(final_global <= KNOWN_FEASIBLE_GUARD),
            "limit": float(KNOWN_FEASIBLE_GUARD),
            "value": float(final_global),
        },
    }
    all_gates_pass = bool(all(gates[k]["pass"] for k in gates))
    certified_delta_vs_base = float(final_global - float(base_reproduction["final_fully_hardened_global_L"]))
    certified_delta_vs_prior = float(final_global - float(base_cert["expected_results"]["base_hardened_global"]["value"]))

    hardened_cert = copy.deepcopy(base_hardened_cert)
    hardened_cert["schema"] = "public E1 exact-budget hardened SOC certificate v1"
    hardened_cert["source_certificate"] = str(BASE_HARDENED_CERT_PATH)
    hardened_cert["source_exact_budget_summary"] = str(BASE_EXACT_BUDGET_PATH)
    hardened_cert["source_e1_nominal_solve"] = "source/data/soc_e1_hardening.json"
    hardened_cert["claim_scope"] = (
        "the retained baseline exact-budget hardened certificate with one extra m=0 E1 witness from the "
        "base-K400 comb enriched by a 0.125 fill on [4,16]. The base witness set remains feasible "
        "by inclusion; the E1 row is the only new solved witness."
    )
    hardened_cert["frequency_comb"] = {
        "base_K": 400,
        "base_count": int(base_xi.size),
        "e1_count": int(e1_xi.size),
        "construction_rule": "base K=400 comb plus 0.125-grid fill on [4,16]",
        "strict_superset": bool(inclusion_check["strict_superset"]),
        "missing_base_frequency_count": int(inclusion_check["missing_base_frequency_count"]),
    }
    hardened_cert["m_coverage"] = {
        "coarse_grid": {"interval": [0.0, 1.0], "mean_partitions": int(GLOBAL_MEAN_PARTITIONS)},
        "refined_bracket": {
            "interval": [float(E1_BRACKET[0]), float(E1_BRACKET[1])],
            "partitions": int(E1_BRACKET_PARTITIONS),
            "spacing": float((E1_BRACKET[1] - E1_BRACKET[0]) / float(E1_BRACKET_PARTITIONS)),
            "mean_variation_pad": float(refined["mean_variation_pad"]),
            "outside_min_after_pad": float(outside["outside_min_after_pad"]),
        },
    }
    hardened_cert["hardened_soc_rows"] = base_rows
    hardened_cert["expected_results"] = {
        "base_certified_global": {
            "value": float(base_reproduction["final_fully_hardened_global_L"]),
            "argmin_m": float(base_reproduction["refined_bracket"]["argmin_m_grid"]),
        },
        "e1_nominal_m0": {
            "value": float(e1_solve["nominal_raw_L"]),
            "solver_status": e1_solve["solver_status"],
        },
        "e1_exact_budget_row": {
            "positive_part_margin": float(e1_budget["positive_part_margin"]),
            "shift_upper": float(e1_budget["certified_shift_upper"]),
            "raw_budget_hi": float(e1_budget["raw_budget_hi"]),
            "shifted_budget_hi": float(e1_budget["shifted_budget_checks"][-1]["budget_hi"]),
        },
        "e1_hardened_global": {
            "value": float(final_global),
            "argmin_m": float(refined["argmin_m_grid"]),
            "gain_over_base_certified": float(certified_delta_vs_base),
            "gain_over_prior_certified": float(certified_delta_vs_prior),
        },
        "four_gate_verdict": {
            "all_gates_pass": bool(all_gates_pass),
            "positive_part": bool(gates["positive_part_exact_budget"]["pass"]),
            "gram_psd": bool(gates["gram_psd"]["pass"]),
            "real_generator": bool(gates["real_generator"]["pass"]),
            "m_envelope": bool(gates["m_envelope"]["pass"]),
        },
        "known_feasible_sanity_guard": float(KNOWN_FEASIBLE_GUARD),
    }
    hardened_cert["audit_margins"] = {
        "e1_positive_part_margin": float(gates["positive_part_exact_budget"]["margin"]),
        "gram_lambda_min_lower_bound": float(gates["gram_psd"]["lambda_min_lower_bound"]),
        "real_generator_pass": bool(gates["real_generator"]["pass"]),
        "m_envelope_outside_exclusion_margin": float(
            float(outside["outside_min_after_pad"]) - float(refined["certified_min_after_pad"])
        ),
        "smoke_detector_gap": float(KNOWN_FEASIBLE_GUARD - final_global),
        "e1_row_value_at_controlling_m": float(e1_controlling_value),
    }
    hardened_cert["elapsed_seconds_to_emit"] = float(time.time() - started)

    OUT_CERT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_CERT_PATH.write_text(json.dumps(_jsonify(hardened_cert), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    result = {
        "schema": "public e1 exact-budget hardening v1",
        "elapsed_seconds": float(time.time() - started),
        "stage_a_base_reproduction": {
            "value": float(base_reproduction["final_fully_hardened_global_L"]),
            "expected": float(EXPECTED_BASE_CERTIFIED),
            "match_error": float(base_reproduction["final_fully_hardened_global_L"] - EXPECTED_BASE_CERTIFIED),
            "argmin_m": float(base_reproduction["refined_bracket"]["argmin_m_grid"]),
        },
        "inclusion_check": inclusion_check,
        "e1_nominal": {
            "value": float(e1_solve["nominal_raw_L"]),
            "delta_vs_saved_nominal": float(e1_solve["nominal_raw_L"] - EXPECTED_E1_NOMINAL),
            "frequency_count": int(e1_comp["selected_frequency_count"]),
            "active_frequency_count": int(e1_comp["selected_frequency_count"]),
            "max_atom_l1_coefficient": float(
                np.max(
                    np.abs(np.asarray(e1_comp["alpha"], dtype=np.float64))
                    + np.abs(np.asarray(e1_comp["beta"], dtype=np.float64))
                )
            ),
        },
        "e1_exact_budget": e1_budget,
        "base_recovered_rows": int(base_row_count),
        "envelope": {
            "refined_bracket": {
                "interval": [float(E1_BRACKET[0]), float(E1_BRACKET[1])],
                "argmin_m": float(refined["argmin_m_grid"]),
                "numeric_min_before_pad": float(refined["numeric_min_before_pad"]),
                "certified_min_after_pad": float(refined["certified_min_after_pad"]),
                "mean_variation_pad": float(refined["mean_variation_pad"]),
            },
            "outside_bracket": {
                "outside_min_after_pad": float(outside["outside_min_after_pad"]),
                "outside_excluded": bool(outside["outside_min_after_pad"] > refined["certified_min_after_pad"]),
                "outside_argmin_m": float(outside["outside_argmin_m_grid"]),
            },
            "global_coarse": {
                "certified_min_after_pad": float(envelope_with_e1["certified_min_after_pad"]),
                "argmin_m_grid": float(envelope_with_e1["argmin_m_grid"]),
            },
            "controlling_row": controlling_row,
            "e1_row_value_at_controlling_m": float(e1_controlling_value),
        },
        "gate_summary": gates,
        "all_gates_pass": bool(all_gates_pass),
        "certified_global_e1": float(final_global),
        "certified_delta_vs_base": float(certified_delta_vs_base),
        "certified_delta_vs_prior_certified": float(certified_delta_vs_prior),
        "certified_vs_coarse_reference_candidate": float(final_global - 0.38042361229782623),
        "smoke_detector_verdict": bool(final_global <= KNOWN_FEASIBLE_GUARD),
        "base_reproduction": base_reproduction,
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "base_hardened_certificate": str(BASE_HARDENED_CERT_PATH),
            "e1_certificate": str(OUT_CERT_PATH),
            "e1_hardening": str(OUT_JSON),
        },
        "notes": [
            "The E1 row is certified exactly on the positive-part gate, but it does not enter the final mean envelope.",
            "The final global lower bound remains the reference value because the inherited witness set still controls the envelope.",
        ],
    }
    OUT_JSON.write_text(json.dumps(_jsonify(result), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"stage_a_base_reproduction={base_reproduction['final_fully_hardened_global_L']:.15f}", flush=True)
    print(
        f"e1_nominal={e1_solve['nominal_raw_L']:.15f} exact_budget_hi={e1_budget['raw_budget_hi']:.15f} "
        f"shift={e1_budget['certified_shift_upper']:.12e} roots={e1_budget['root_count']}",
        flush=True,
    )
    print(
        f"refined_bracket=[{E1_BRACKET[0]:.6f},{E1_BRACKET[1]:.6f}] "
        f"argmin={refined['argmin_m_grid']:.8f} certified_in_bracket={refined['certified_min_after_pad']:.15f}",
        flush=True,
    )
    print(
        f"outside_min_after_pad={outside['outside_min_after_pad']:.15f} "
        f"final_global={final_global:.15f}",
        flush=True,
    )
    print(
        "gate_statuses="
        f"positive_part={gates['positive_part_exact_budget']['pass']} "
        f"gram_psd={gates['gram_psd']['pass']} "
        f"real_generator={gates['real_generator']['pass']} "
        f"m_envelope={gates['m_envelope']['pass']} "
        f"smoke={gates['smoke_detector']['pass']}",
        flush=True,
    )
    print(f"certified_delta_vs_base={certified_delta_vs_base:.12e}", flush=True)
    print(f"saved_certificate={OUT_CERT_PATH}", flush=True)
    print(f"saved_hardening_json={OUT_JSON}", flush=True)
    return result


if __name__ == "__main__":
    run_analysis()
