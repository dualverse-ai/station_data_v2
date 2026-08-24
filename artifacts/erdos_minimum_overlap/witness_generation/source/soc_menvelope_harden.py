"""Refined m-envelope hardening for the a predecessor computation exact-budget SOC row.

This script reuses the a predecessor computation recovered positive-part downshift for the
the retained baseline improved K=400 row, then replaces the old coarse full-domain
mean-envelope gate by a refined bracket around the relocated argmin.
"""

from __future__ import annotations

import copy
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import sys

sys.path.insert(0, "source")
import soc_budget_exact as sbe  # noqa: E402
import verify_cert_improved as vci  # noqa: E402


CERT_PATH = Path("source/soc_certificate_improved.json")
EXACT_BUDGET_PATH = Path("source/data/soc_budget_exact.json")
RESCALED_PATH = Path("source/data/soc_budget_exact_rescaled_certificate.json")
OUT_PATH = Path("source/data/soc_menvelope_harden.json")
HARDENED_CERT_PATH = Path("source/data/soc_menvelope_hardened_certificate.json")

IMPROVED_ROW_ID = "perturbed_band_indicator_L10_basis2"
PRIOR_CERTIFIED_LB = 0.38032854254945764
BASELINE_COARSE_CANDIDATE = 0.38042361229782623
KNOWN_FEASIBLE_GUARD = 0.380895


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _row_value(row: dict[str, Any], m: np.ndarray) -> np.ndarray:
    return (
        float(row["quadratic_c0_lower"])
        + float(row["a1"]) * m
        + 0.5 * float(row["a2"]) * m * m
    )


def _row_slope_abs_sup(row: dict[str, Any], lo: float, hi: float) -> float:
    a1 = float(row["a1"])
    a2 = float(row["a2"])
    if lo <= 0.0 <= hi and a2 != 0.0:
        root = -a1 / a2
        if lo <= root <= hi:
            return max(abs(a1 + a2 * lo), abs(a1 + a2 * hi), 0.0)
    return max(abs(a1 + a2 * lo), abs(a1 + a2 * hi))


def _envelope_table(
    rows: list[dict[str, Any]],
    *,
    lo: float,
    hi: float,
    partitions: int,
    mean_guard: float,
) -> dict[str, Any]:
    m = np.linspace(float(lo), float(hi), int(partitions) + 1, dtype=np.float64)
    q = np.empty((len(rows), m.size), dtype=np.float64)
    for i, row in enumerate(rows):
        q[i] = _row_value(row, m)
    envelope = np.max(q, axis=0)
    argmax = np.argmax(q, axis=0)
    spacing = (float(hi) - float(lo)) / float(partitions)
    slope_sup = max(_row_slope_abs_sup(row, float(lo), float(hi)) for row in rows)
    mean_pad = 0.5 * slope_sup * spacing
    lower = envelope - mean_pad - float(mean_guard)
    idx = int(np.argmin(lower))
    active = np.flatnonzero(q[:, idx] >= envelope[idx] - 2.0e-7)
    unique_active = sorted({rows[int(i)]["id"] for i in np.unique(argmax)})
    return {
        "lo": float(lo),
        "hi": float(hi),
        "partitions": int(partitions),
        "spacing": float(spacing),
        "slope_sup_bound": float(slope_sup),
        "mean_variation_pad": float(mean_pad),
        "numeric_min_before_pad": float(envelope[idx]),
        "certified_min_after_pad": float(lower[idx]),
        "argmin_m_grid": float(m[idx]),
        "active_witnesses_at_argmin": [
            {
                "row_id": rows[int(i)]["id"],
                "m_source": float(rows[int(i)]["m"]),
                "value_at_argmin": float(q[int(i), idx]),
            }
            for i in active[:12]
        ],
        "unique_grid_controlling_rows": unique_active,
        "sample_table": [
            {
                "m": float(m[j]),
                "envelope": float(envelope[j]),
                "lower_after_pad": float(lower[j]),
                "controlling_row": rows[int(argmax[j])]["id"],
            }
            for j in np.linspace(0, m.size - 1, min(25, m.size), dtype=np.int64)
        ],
        "_m": m,
        "_q": q,
        "_envelope": envelope,
        "_lower": lower,
        "_argmax": argmax,
    }


def _outside_minimum(
    rows: list[dict[str, Any]],
    *,
    bracket_lo: float,
    bracket_hi: float,
    domain_lo: float,
    domain_hi: float,
    partitions: int,
    mean_guard: float,
) -> dict[str, Any]:
    table = _envelope_table(
        rows,
        lo=domain_lo,
        hi=domain_hi,
        partitions=partitions,
        mean_guard=mean_guard,
    )
    m = table["_m"]
    q = table["_q"]
    envelope = table["_envelope"]
    outside = (m < float(bracket_lo)) | (m > float(bracket_hi))
    if not np.any(outside):
        raise RuntimeError("outside bracket mask is empty")
    slope_sup = max(_row_slope_abs_sup(row, float(domain_lo), float(domain_hi)) for row in rows)
    spacing = (float(domain_hi) - float(domain_lo)) / float(partitions)
    pad = 0.5 * slope_sup * spacing
    lower = envelope[outside] - pad - float(mean_guard)
    m_out = m[outside]
    q_out = q[:, outside]
    idx = int(np.argmin(lower))
    active = int(np.argmax(q_out[:, idx]))
    return {
        "domain": [float(domain_lo), float(domain_hi)],
        "partitions": int(partitions),
        "spacing": float(spacing),
        "slope_sup_bound": float(slope_sup),
        "mean_variation_pad": float(pad),
        "outside_min_after_pad": float(lower[idx]),
        "outside_numeric_min_before_pad": float(envelope[outside][idx]),
        "outside_argmin_m_grid": float(m_out[idx]),
        "outside_controlling_row": rows[active]["id"],
    }


def _strip_arrays(obj: Any) -> Any:
    if isinstance(obj, dict):
        return {k: _strip_arrays(v) for k, v in obj.items() if not k.startswith("_")}
    if isinstance(obj, list):
        return [_strip_arrays(v) for v in obj]
    if isinstance(obj, np.ndarray):
        return obj.tolist()
    if isinstance(obj, (np.floating, np.integer)):
        return obj.item()
    return obj


def build_verified_rows_with_baseline_recovery(
    cert: dict[str, Any],
    exact_budget_summary: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = sbe.verified_rows_from_stored_expected(cert)
    rec = exact_budget_summary["recoverability"]
    recovered_delta_lower = float(rec["recoverable_delta_L_lower"])
    exact_shift_upper = float(rec["certified_needed_exact_downshift_upper"])
    for row in rows:
        if row["id"] == IMPROVED_ROW_ID:
            row["quadratic_c0_lower_unrecovered"] = float(row["quadratic_c0_lower"])
            row["quadratic_c0_lower"] = float(row["quadratic_c0_lower"] + recovered_delta_lower)
            row["L_source_m_lower"] = float(
                row["quadratic_c0_lower"] + row["a1"] * row["m"] + 0.5 * row["a2"] * row["m"] * row["m"]
            )
            row["exact_budget_recovered_delta_lower"] = recovered_delta_lower
            row["exact_budget_shift_upper"] = exact_shift_upper
            break
    else:
        raise KeyError(IMPROVED_ROW_ID)
    return rows, {
        "row_id": IMPROVED_ROW_ID,
        "stored_conservative_downshift": float(rec["stored_conservative_downshift"]),
        "certified_needed_exact_downshift_upper": exact_shift_upper,
        "recoverable_delta_lower": recovered_delta_lower,
        "reference_coarse_global_L": float(rec["new_certified_global_L_with_exact_budget_gate"]),
        "reference_coarse_argmin_m": float(rec["envelope"]["coarse_argmin_m"]),
        "reference_exact_budget_verdict": rec["verdict"],
    }


def _gate_summary(cert: dict[str, Any], controlling_row_id: str, exact_budget_summary: dict[str, Any]) -> dict[str, Any]:
    gram = vci.verify_gram(cert)
    row = next(row for row in cert["hardened_soc_rows"] if row["id"] == IMPROVED_ROW_ID)
    alpha = np.array([sbe._mid(p) for p in row["atom_intervals"]["alpha"]], dtype=np.float64)
    beta = np.array([sbe._mid(p) for p in row["atom_intervals"]["beta"]], dtype=np.float64)
    shifted = exact_budget_summary["exact_shift_to_budget_one"]["shifted_budget_checks"][-1]
    real_generator = bool(np.all(alpha[np.abs(beta) > 0.0] > 0.0))
    return {
        "positive_part_exact_budget": {
            "pass": bool(shifted["budget_hi"] <= 1.0),
            "row_id": IMPROVED_ROW_ID,
            "budget_hi": float(shifted["budget_hi"]),
            "budget_lo": float(shifted["budget_lo"]),
            "shift_upper": float(exact_budget_summary["recoverability"]["certified_needed_exact_downshift_upper"]),
            "margin": float(1.0 - shifted["budget_hi"]),
            "note": "The recovered row's exact positive-part shift is independent of the target m; it is applied to every refined m-grid point.",
        },
        "gram_psd": {
            "pass": bool(gram and gram["psd_certified"]),
            "lambda_min_lower_bound": float(gram["lambda_min_lower_bound"]) if gram else None,
            "dimension": int(gram["dimension"]) if gram else None,
            "method": gram["method"] if gram else None,
        },
        "real_generator": {
            "pass": real_generator,
            "nonzero_beta_count": int(np.count_nonzero(np.abs(beta) > 0.0)),
            "min_alpha_where_beta_nonzero": float(np.min(alpha[np.abs(beta) > 0.0]))
            if np.any(np.abs(beta) > 0.0)
            else None,
        },
        "m_envelope": {
            "pass": False,
            "controlling_row_at_grid_argmin": controlling_row_id,
        },
    }


def run_analysis(
    *,
    cert_path: Path = CERT_PATH,
    exact_budget_path: Path = EXACT_BUDGET_PATH,
    out_path: Path = OUT_PATH,
    hardened_cert_path: Path = HARDENED_CERT_PATH,
    bracket: tuple[float, float] = (0.017, 0.023),
    bracket_partitions: int = 60_000,
    domain: tuple[float, float] = (0.0, 1.0),
    domain_partitions: int = 400_000,
) -> dict[str, Any]:
    started = time.time()
    cert = _load_json(Path(cert_path))
    settings = cert["verification_settings"]
    exact_budget_summary = _load_json(Path(exact_budget_path))
    rows, recovery = build_verified_rows_with_baseline_recovery(cert, exact_budget_summary)

    # Reproduce the original verifier and the a predecessor computation coarse exact-budget value
    # before using the refined bracket. The stored verifier intentionally checks
    # the conservative the retained baseline certificate, not the recovered row.
    print("running_baseline_improved_verifier")
    baseline_verify = vci.verify_certificate(Path(cert_path))
    coarse = vci.envelope_from_verified_rows(rows, settings)

    blo, bhi = map(float, bracket)
    dlo, dhi = map(float, domain)
    refined = _envelope_table(
        rows,
        lo=blo,
        hi=bhi,
        partitions=int(bracket_partitions),
        mean_guard=float(settings["mean_guard"]),
    )
    outside = _outside_minimum(
        rows,
        bracket_lo=blo,
        bracket_hi=bhi,
        domain_lo=dlo,
        domain_hi=dhi,
        partitions=int(domain_partitions),
        mean_guard=float(settings["mean_guard"]),
    )
    controlling_row = refined["active_witnesses_at_argmin"][0]["row_id"]
    gates = _gate_summary(cert, controlling_row, exact_budget_summary)
    gates["m_envelope"] = {
        "pass": bool(
            blo < refined["argmin_m_grid"] < bhi
            and outside["outside_min_after_pad"] > refined["certified_min_after_pad"]
        ),
        "bracket": [blo, bhi],
        "argmin_interior": bool(blo < refined["argmin_m_grid"] < bhi),
        "refined_argmin_m_grid": refined["argmin_m_grid"],
        "refined_numeric_min_before_pad": refined["numeric_min_before_pad"],
        "refined_mean_variation_pad": refined["mean_variation_pad"],
        "refined_certified_min_after_pad": refined["certified_min_after_pad"],
        "outside_min_after_pad": outside["outside_min_after_pad"],
        "outside_excluded": bool(outside["outside_min_after_pad"] > refined["certified_min_after_pad"]),
        "domain": [dlo, dhi],
        "domain_partitions": int(domain_partitions),
    }
    all_gates_pass = bool(
        gates["positive_part_exact_budget"]["pass"]
        and gates["gram_psd"]["pass"]
        and gates["real_generator"]["pass"]
        and gates["m_envelope"]["pass"]
        and refined["certified_min_after_pad"] <= KNOWN_FEASIBLE_GUARD
    )
    final_lb = float(refined["certified_min_after_pad"]) if all_gates_pass else None

    hardened_cert = copy.deepcopy(cert)
    hardened_cert["schema"] = "public soc exact-budget refined m-envelope certificate v1"
    hardened_cert["source_certificate"] = str(cert_path)
    hardened_cert["source_exact_budget_summary"] = str(exact_budget_path)
    hardened_cert["claim_scope"] = (
        "K=400 the retained baseline improved row with a predecessor computation exact positive-part budget and "
        "a refined/padded m-envelope over the original [0,1] mean domain."
    )
    hardened_cert["m_coverage"] = {
        "coarse_grid": {"interval": [dlo, dhi], "mean_partitions": int(domain_partitions)},
        "refined_bracket": {
            "interval": [blo, bhi],
            "partitions": int(bracket_partitions),
            "spacing": refined["spacing"],
            "mean_variation_pad": refined["mean_variation_pad"],
            "outside_min_after_pad": outside["outside_min_after_pad"],
        },
    }
    hardened_cert["expected_results"] = {
        **hardened_cert.get("expected_results", {}),
        "reference_coarse_candidate": {
            "argmin_m": recovery["reference_coarse_argmin_m"],
            "value": recovery["reference_coarse_global_L"],
        },
        "refined_exact_budget_hardened_global": {
            "all_gates_pass": all_gates_pass,
            "argmin_m": refined["argmin_m_grid"],
            "value": final_lb,
            "margin_over_prior_certified": None if final_lb is None else final_lb - PRIOR_CERTIFIED_LB,
            "margin_over_reference_coarse_candidate": None if final_lb is None else final_lb - BASELINE_COARSE_CANDIDATE,
        },
    }
    hardened_cert_path.parent.mkdir(parents=True, exist_ok=True)
    hardened_cert_path.write_text(json.dumps(_strip_arrays(hardened_cert), indent=2, sort_keys=True), encoding="utf-8")

    result = {
        "schema": "public soc m-envelope hardening v1",
        "elapsed_seconds": time.time() - started,
        "source_paths": {
            "certificate": str(cert_path),
            "exact_budget_summary": str(exact_budget_path),
            "hardened_certificate": str(hardened_cert_path),
        },
        "reproduction": {
            "baseline_improved_global": baseline_verify["certified_global_L"],
            "baseline_improved_argmin_m": baseline_verify["refined"]["refined_argmin_m_grid"],
            "reference_coarse_global_loaded": recovery["reference_coarse_global_L"],
            "reference_coarse_argmin_m_loaded": recovery["reference_coarse_argmin_m"],
            "reference_coarse_global_recomputed": coarse["certified_min_over_0_1"],
            "reference_coarse_argmin_m_recomputed": coarse["argmin_m_grid"],
            "reference_reproduction_error": coarse["certified_min_over_0_1"] - recovery["reference_coarse_global_L"],
        },
        "recovered_exact_budget": recovery,
        "refined_bracket": _strip_arrays(refined),
        "outside_bracket": outside,
        "gate_summary": gates,
        "all_gates_pass": all_gates_pass,
        "final_fully_hardened_global_L": final_lb,
        "comparisons": {
            "prior_certified_LB": PRIOR_CERTIFIED_LB,
            "gain_over_prior_certified": None if final_lb is None else final_lb - PRIOR_CERTIFIED_LB,
            "reference_coarse_candidate": BASELINE_COARSE_CANDIDATE,
            "gain_over_reference_coarse_candidate": None if final_lb is None else final_lb - BASELINE_COARSE_CANDIDATE,
            "known_feasible_guard": KNOWN_FEASIBLE_GUARD,
            "below_known_feasible_guard": None if final_lb is None else bool(final_lb <= KNOWN_FEASIBLE_GUARD),
        },
        "notes": [
            "The exact positive-part shift is reused from a predecessor computation, which isolated roots at 80 dps and root tolerance below 5e-13.",
            "Only the a predecessor computation recovered perturbation row receives the exact-budget recovery; all other rows remain at their the retained baseline conservative interval-hardened values.",
            "The m-envelope is evaluated on the original the retained baseline mean domain [0,1].",
        ],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(_strip_arrays(result), indent=2, sort_keys=True), encoding="utf-8")

    print(f"reference_coarse_global={coarse['certified_min_over_0_1']:.15f} argmin_m={coarse['argmin_m_grid']:.8f}")
    print(
        f"refined_bracket=[{blo:.6f},{bhi:.6f}] partitions={int(bracket_partitions)} "
        f"spacing={refined['spacing']:.3e}"
    )
    print(
        f"refined_argmin_m={refined['argmin_m_grid']:.8f} "
        f"numeric_min={refined['numeric_min_before_pad']:.15f}"
    )
    print(
        f"mean_variation_pad={refined['mean_variation_pad']:.12e} "
        f"certified_in_bracket={refined['certified_min_after_pad']:.15f}"
    )
    print(
        f"outside_min_after_pad={outside['outside_min_after_pad']:.15f} "
        f"outside_argmin_m={outside['outside_argmin_m_grid']:.8f}"
    )
    print(
        "gate_statuses="
        f"positive_part={gates['positive_part_exact_budget']['pass']} "
        f"gram_psd={gates['gram_psd']['pass']} "
        f"real_generator={gates['real_generator']['pass']} "
        f"m_envelope={gates['m_envelope']['pass']}"
    )
    print(f"final_fully_hardened_global_L={final_lb if final_lb is not None else 'n.a.'}")
    if final_lb is not None:
        print(f"gain_over_prior_certified={final_lb - PRIOR_CERTIFIED_LB:.12e}")
        print(f"gain_over_reference_coarse_candidate={final_lb - BASELINE_COARSE_CANDIDATE:.12e}")
    print(f"saved_json={out_path}")
    print(f"saved_hardened_certificate={hardened_cert_path}")
    return result


if __name__ == "__main__":
    run_analysis()
