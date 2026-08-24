"""Phase-augmented per-mean positive-part dual.

This is the continuum dual requested for a predecessor computation.  For each fixed first
moment m it solves a finite LP for

    G0(x) = a0 + a1*x + a2*x^2 - sum_j lambda_j cos(xi_j*x - phi_j),

with lambda_j >= 0 and a grid positive-part budget.  The reported certificate
then applies the same curvature-envelope positive-part verifier used by the
C>=0 audit and downshifts a0 until int max(0,G0) <= 1-1e-10 on [-2,2].
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

from cpos_audit import (
    conservative_positive_upper_from_samples,
    selected_frequency_payload,
    shift_needed_for_positive_mass,
)
from cpos_augmented_dual import ROOT, load_b0even_best
from verify_B0 import sinc2


OUT_JSON = ROOT / "phase_augmented_dual.json"
REFINED_JSON = ROOT / "phase_augmented_dual_refined.json"
TARGET_EVEN_CPOS = 0.3804436121308823
REFERENCE_M025 = 0.3704006897
PHASES = (
    0.0,
    math.pi / 8.0,
    -math.pi / 8.0,
    math.pi / 4.0,
    -math.pi / 4.0,
    3.0 * math.pi / 8.0,
    -3.0 * math.pi / 8.0,
)
SCAN_M_VALUES = (
    0.0,
    0.0125,
    0.025,
    0.0375,
    0.05,
    0.0625,
    0.075,
    0.0875,
    0.10,
    0.125,
    0.15,
    0.20,
    0.25,
    0.30,
    0.40,
    0.50,
    0.70,
    1.00,
)


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


def build_atoms(xi: np.ndarray, phases: tuple[float, ...] = PHASES) -> dict[str, np.ndarray]:
    base_xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    phase = np.asarray(phases, dtype=np.float64).reshape(-1)
    atom_xi = np.repeat(base_xi, phase.size)
    atom_phase = np.tile(phase, base_xi.size)
    cos_phase = np.cos(atom_phase)
    if np.any(cos_phase <= 1.0e-14):
        raise ValueError("phase grid must stay inside (-pi/2, pi/2)")
    ceiling = sinc2(atom_xi) / cos_phase
    return {
        "base_xi": base_xi,
        "phase_grid": phase,
        "xi": atom_xi,
        "phase": atom_phase,
        "ceiling": ceiling,
        "cos_phase": cos_phase,
    }


def evaluate_g_chunked(
    x: np.ndarray,
    *,
    a0: float,
    a1: float,
    a2: float,
    xi: np.ndarray,
    phase: np.ndarray,
    lam: np.ndarray,
    chunk: int = 2048,
) -> np.ndarray:
    x = np.asarray(x, dtype=np.float64)
    xi = np.asarray(xi, dtype=np.float64)
    phase = np.asarray(phase, dtype=np.float64)
    lam = np.asarray(lam, dtype=np.float64)
    out = np.empty_like(x)
    for start in range(0, x.size, int(chunk)):
        stop = min(x.size, start + int(chunk))
        xs = x[start:stop]
        trig = np.cos(xs[:, None] * xi[None, :] - phase[None, :]) @ lam if xi.size else 0.0
        out[start:stop] = float(a0) + float(a1) * xs + float(a2) * xs * xs - trig
    return out


def curvature_bound(a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(2.0 * abs(float(a2)) + float(np.sum(np.abs(lam) * np.asarray(xi, dtype=np.float64) ** 2)))


def derivative_bound(a1: float, a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(abs(float(a1)) + 4.0 * abs(float(a2)) + float(np.sum(np.abs(lam) * np.asarray(xi, dtype=np.float64))))


def l_of_m(
    m: float,
    *,
    a0: float,
    a1: float,
    a2: float,
    ceiling: np.ndarray,
    lam: np.ndarray,
) -> float:
    mm = float(m)
    return float(
        float(a0)
        + float(a1) * mm
        + float(a2) * (2.0 / 3.0 + 0.5 * mm * mm)
        - float(np.asarray(ceiling, dtype=np.float64) @ np.asarray(lam, dtype=np.float64))
    )


def quadratic_min_on_interval(
    *,
    lo: float,
    hi: float,
    a0: float,
    a1: float,
    a2: float,
    ceiling: np.ndarray,
    lam: np.ndarray,
) -> dict[str, Any]:
    lo = float(lo)
    hi = float(hi)
    c0 = float(a0) + (2.0 / 3.0) * float(a2) - float(np.asarray(ceiling, dtype=np.float64) @ np.asarray(lam, dtype=np.float64))
    candidates = [lo, hi]
    if float(a2) > 0.0:
        vertex = -float(a1) / float(a2)
        if lo <= vertex <= hi:
            candidates.append(float(vertex))
    vals = [float(c0 + float(a1) * m + 0.5 * float(a2) * m * m) for m in candidates]
    idx = int(np.argmin(vals))
    return {
        "minimum": float(vals[idx]),
        "argmin_m": float(candidates[idx]),
        "candidate_count": int(len(candidates)),
        "endpoint_values": {
            "lo": float(c0 + float(a1) * lo + 0.5 * float(a2) * lo * lo),
            "hi": float(c0 + float(a1) * hi + 0.5 * float(a2) * hi * hi),
        },
    }


def row_quadratic_coefficients(row: dict[str, Any]) -> dict[str, Any]:
    cert = row["continuum_verification"]
    comp = row["compressed_lp"]
    a0 = float(cert["shifted_a0"])
    a1 = float(cert["a1"])
    a2 = float(cert["a2"])
    c0 = a0 + (2.0 / 3.0) * a2 - float(
        np.asarray(comp["ceiling"], dtype=np.float64) @ np.asarray(comp["lambda"], dtype=np.float64)
    )
    return {
        "source_m": float(row["m"]),
        "K": int(row.get("K", 0)),
        "c0": float(c0),
        "a1": float(a1),
        "a2": float(a2),
    }


def quadratic_value(coeff: dict[str, Any], m: float) -> float:
    mm = float(m)
    return float(float(coeff["c0"]) + float(coeff["a1"]) * mm + 0.5 * float(coeff["a2"]) * mm * mm)


def min_max_quadratics_on_interval(
    coeffs: list[dict[str, Any]],
    *,
    lo: float,
    hi: float,
) -> dict[str, Any]:
    lo = float(lo)
    hi = float(hi)
    candidates = [lo, hi]
    eps = 1.0e-12

    for coeff in coeffs:
        a2 = float(coeff["a2"])
        a1 = float(coeff["a1"])
        if abs(a2) > 1.0e-18:
            vertex = -a1 / a2
            if lo - eps <= vertex <= hi + eps:
                candidates.append(float(min(hi, max(lo, vertex))))

    for i, ci in enumerate(coeffs):
        for cj in coeffs[i + 1 :]:
            qa = 0.5 * (float(ci["a2"]) - float(cj["a2"]))
            qb = float(ci["a1"]) - float(cj["a1"])
            qc = float(ci["c0"]) - float(cj["c0"])
            if abs(qa) <= 1.0e-18:
                if abs(qb) > 1.0e-18:
                    root = -qc / qb
                    if lo - eps <= root <= hi + eps:
                        candidates.append(float(min(hi, max(lo, root))))
                continue
            disc = qb * qb - 4.0 * qa * qc
            if disc < -1.0e-14:
                continue
            disc = max(0.0, disc)
            sqrt_disc = math.sqrt(disc)
            for root in ((-qb - sqrt_disc) / (2.0 * qa), (-qb + sqrt_disc) / (2.0 * qa)):
                if lo - eps <= root <= hi + eps:
                    candidates.append(float(min(hi, max(lo, root))))

    unique = np.unique(np.asarray(candidates, dtype=np.float64))
    best: dict[str, Any] | None = None
    for m in unique:
        values = np.asarray([quadratic_value(coeff, float(m)) for coeff in coeffs], dtype=np.float64)
        upper = float(np.max(values))
        active = np.flatnonzero(values >= upper - 1.0e-10)
        item = {
            "minimum": upper,
            "argmin_m": float(m),
            "candidate_count": int(unique.size),
            "active_witness_count": int(active.size),
            "active_witnesses": [
                {
                    "source_m": float(coeffs[int(i)]["source_m"]),
                    "K": int(coeffs[int(i)]["K"]),
                    "value": float(values[int(i)]),
                }
                for i in active[:10]
            ],
        }
        if best is None or item["minimum"] < best["minimum"]:
            best = item
    if best is None:
        return {"minimum": float("nan"), "argmin_m": lo, "candidate_count": 0, "active_witnesses": []}
    return best


def solve_fixed_mean_phase_lp(
    atoms: dict[str, np.ndarray],
    *,
    m: float,
    x_grid_points: int,
    method: str = "highs-ipm",
) -> dict[str, Any]:
    atom_xi = np.asarray(atoms["xi"], dtype=np.float64)
    atom_phase = np.asarray(atoms["phase"], dtype=np.float64)
    ceiling = np.asarray(atoms["ceiling"], dtype=np.float64)
    k = int(atom_xi.size)
    m = float(m)
    x = np.linspace(-2.0, 2.0, int(x_grid_points), dtype=np.float64)
    n_x = int(x.size)
    weights = np.full(n_x, 4.0 / (n_x - 1), dtype=np.float64)
    weights[0] *= 0.5
    weights[-1] *= 0.5

    started_build = time.time()
    atom_grid = np.cos(x[:, None] * atom_xi[None, :] - atom_phase[None, :])
    prefix = sparse.csr_matrix(np.column_stack((np.ones(n_x), x, x * x, -atom_grid)))
    a_grid = sparse.hstack((prefix, -sparse.eye(n_x, format="csr")), format="csr")
    a_mass = sparse.hstack(
        (sparse.csr_matrix((1, 3 + k)), sparse.csr_matrix(weights[None, :])),
        format="csr",
    )
    a_ub = sparse.vstack((a_grid, a_mass), format="csr")
    b_ub = np.concatenate((np.zeros(n_x, dtype=np.float64), [1.0]))
    moment2 = 2.0 / 3.0 + 0.5 * m * m
    c = np.concatenate(([-1.0, -m, -moment2], ceiling, np.zeros(n_x, dtype=np.float64)))
    bounds = [(None, None), (None, None), (None, None)] + [(0.0, None)] * k + [(0.0, None)] * n_x
    build_elapsed = time.time() - started_build

    started_solve = time.time()
    result = linprog(
        c,
        A_ub=a_ub,
        b_ub=b_ub,
        bounds=bounds,
        method=method,
        options={
            "primal_feasibility_tolerance": 1.0e-8,
            "dual_feasibility_tolerance": 1.0e-8,
        },
    )
    solve_elapsed = time.time() - started_solve
    if not result.success:
        raise RuntimeError(f"phase LP failed at m={m}: {result.message}")

    y = np.asarray(result.x, dtype=np.float64)
    lam = np.maximum(y[3 : 3 + k], 0.0)
    a0 = float(y[0])
    a1 = float(y[1])
    a2 = float(y[2])
    grid_g = a0 + a1 * x + a2 * x * x - atom_grid @ lam
    raw_l = l_of_m(m, a0=a0, a1=a1, a2=a2, ceiling=ceiling, lam=lam)
    return {
        "m": m,
        "xi": atom_xi,
        "phase": atom_phase,
        "ceiling": ceiling,
        "lambda": lam,
        "a0": a0,
        "a1": a1,
        "a2": a2,
        "raw_L": raw_l,
        "solver_objective_L": float(-result.fun),
        "raw_objective_residual": float(raw_l + result.fun),
        "selected_atom_count": int(k),
        "x_grid_points": int(n_x),
        "grid_positive_integral_trapezoid": float(np.trapezoid(np.maximum(grid_g, 0.0), x)),
        "grid_integral_G_trapezoid": float(np.trapezoid(grid_g, x)),
        "grid_min_G": float(np.min(grid_g)),
        "grid_max_G": float(np.max(grid_g)),
        "grid_argmin_G": float(x[int(np.argmin(grid_g))]),
        "grid_argmax_G": float(x[int(np.argmax(grid_g))]),
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lambda_positive_count_gt_1e_8": int(np.sum(lam > 1.0e-8)),
        "build_elapsed_seconds": float(build_elapsed),
        "solve_elapsed_seconds": float(solve_elapsed),
        "solver_status": int(result.status),
        "solver_message": str(result.message),
    }


def compress_zero_lambdas(lp: dict[str, Any], *, tol: float = 0.0) -> dict[str, Any]:
    lam = np.asarray(lp["lambda"], dtype=np.float64)
    mask = lam > float(tol)
    out = dict(lp)
    for key in ("xi", "phase", "ceiling", "lambda"):
        out[key] = np.asarray(lp[key], dtype=np.float64)[mask]
    out["selected_atom_count"] = int(np.sum(mask))
    out["zero_pruned_count"] = int(np.sum(~mask))
    out["raw_L"] = l_of_m(
        float(out["m"]),
        a0=float(out["a0"]),
        a1=float(out["a1"]),
        a2=float(out["a2"]),
        ceiling=out["ceiling"],
        lam=out["lambda"],
    )
    return out


def phase_activity_summary(phase: np.ndarray, lam: np.ndarray) -> dict[str, Any]:
    phase = np.asarray(phase, dtype=np.float64)
    lam = np.asarray(lam, dtype=np.float64)
    active = lam > 1.0e-10
    rows = []
    for ph in PHASES:
        mask = np.isclose(phase, float(ph), atol=1.0e-14)
        rows.append(
            {
                "phase": float(ph),
                "active_count_gt_1e_10": int(np.sum(active & mask)),
                "lambda_sum": float(np.sum(lam[mask])),
                "active_lambda_sum": float(np.sum(lam[active & mask])),
                "max_lambda": float(np.max(lam[mask])) if np.any(mask) else 0.0,
            }
        )
    nonzero_active = active & (np.abs(phase) > 1.0e-14)
    zero_active = active & (np.abs(phase) <= 1.0e-14)
    return {
        "phase_rows": rows,
        "active_atom_count": int(np.sum(active)),
        "active_phi0_count": int(np.sum(zero_active)),
        "active_nonzero_phase_count": int(np.sum(nonzero_active)),
        "active_nonzero_phase_lambda_sum": float(np.sum(lam[nonzero_active])),
        "active_phi0_lambda_sum": float(np.sum(lam[zero_active])),
        "has_nonzero_phase_active": bool(np.any(nonzero_active)),
    }


def certify_fixed_mean_solution(
    lp: dict[str, Any],
    *,
    verify_points: int = 200_001,
    chunk: int = 2048,
) -> dict[str, Any]:
    xi = np.asarray(lp["xi"], dtype=np.float64)
    phase = np.asarray(lp["phase"], dtype=np.float64)
    ceiling = np.asarray(lp["ceiling"], dtype=np.float64)
    lam = np.asarray(lp["lambda"], dtype=np.float64)
    a0 = float(lp["a0"])
    a1 = float(lp["a1"])
    a2 = float(lp["a2"])
    m0 = float(lp["m"])
    curvature = curvature_bound(a2, xi, lam)
    slope = derivative_bound(a1, a2, xi, lam)
    roundoff_pad = 1.0e-12 * (1.0 + abs(a0) + 2.0 * abs(a1) + 4.0 * abs(a2) + float(np.sum(np.abs(lam))))
    target = 1.0 - 1.0e-10

    started = time.time()
    x = np.linspace(-2.0, 2.0, int(verify_points), dtype=np.float64)
    values = evaluate_g_chunked(x, a0=a0, a1=a1, a2=a2, xi=xi, phase=phase, lam=lam, chunk=chunk)
    spacing = float(4.0 / (int(verify_points) - 1))
    raw_upper = conservative_positive_upper_from_samples(
        values,
        spacing=spacing,
        second_derivative_sup=curvature,
        roundoff_pad=roundoff_pad,
    )
    req_shift, shifted_upper = shift_needed_for_positive_mass(
        values,
        spacing=spacing,
        second_derivative_sup=curvature,
        roundoff_pad=roundoff_pad,
        target=target,
    )
    shifted_a0 = a0 - req_shift
    shifted_values = values - req_shift
    verified_l = l_of_m(m0, a0=shifted_a0, a1=a1, a2=a2, ceiling=ceiling, lam=lam)

    active = np.flatnonzero(lam > 1.0e-10)
    top = active[np.argsort(lam[active])[-20:]][::-1] if active.size else np.empty(0, dtype=np.int64)
    phase_summary = phase_activity_summary(phase, lam)
    return {
        "m": m0,
        "verify_points": int(verify_points),
        "spacing": spacing,
        "raw_upper_int_positive_part": float(raw_upper),
        "raw_margin_to_one": float(1.0 - raw_upper),
        "required_downshift_for_strict_pass": float(req_shift),
        "strict_target": target,
        "shifted_upper_int_positive_part": float(shifted_upper),
        "shifted_margin_to_one": float(1.0 - shifted_upper),
        "pass_positive_part": bool(shifted_upper <= 1.0),
        "raw_L": float(lp["raw_L"]),
        "verified_L_at_m": float(verified_l),
        "downshift_loss": float(req_shift),
        "a0_raw": a0,
        "shifted_a0": float(shifted_a0),
        "a1": a1,
        "a2": a2,
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lambda_positive_count_gt_1e_8": int(np.sum(lam > 1.0e-8)),
        "phase_activity": phase_summary,
        "xi_max": float(np.max(xi)) if xi.size else None,
        "second_derivative_sup_bound": curvature,
        "first_derivative_sup_bound": slope,
        "roundoff_pad_per_endpoint": float(roundoff_pad),
        "dense_trapezoid_positive_shifted": float(np.trapezoid(np.maximum(shifted_values, 0.0), x)),
        "dense_min_G_shifted": float(np.min(shifted_values)),
        "dense_max_G_shifted": float(np.max(shifted_values)),
        "dense_argmin_G_shifted": float(x[int(np.argmin(shifted_values))]),
        "dense_argmax_G_shifted": float(x[int(np.argmax(shifted_values))]),
        "top_lambda_atoms": [
            {"xi": float(xi[int(i)]), "phase": float(phase[int(i)]), "lambda": float(lam[int(i)])}
            for i in top
        ],
        "elapsed_seconds": float(time.time() - started),
        "verification_method": (
            "Full-domain grid plus curvature envelope; then downshift a0 until "
            "the conservative upper integral of max(0,G0) is <= 1-1e-10."
        ),
    }


def interval_certificate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    valid = [row for row in rows if row.get("status") == "success"]
    if len(valid) < 2:
        return {"status": "insufficient_rows"}
    valid.sort(key=lambda row: float(row["m"]))
    coeffs = [row_quadratic_coefficients(row) for row in valid]
    by_m: dict[float, list[dict[str, Any]]] = {}
    for row, coeff in zip(valid, coeffs):
        by_m.setdefault(round(float(row["m"]), 12), []).append(coeff)
    unique_m = sorted(by_m)

    intervals: list[dict[str, Any]] = []
    for lo, hi in zip(unique_m, unique_m[1:]):
        local_coeffs = by_m.get(lo, []) + by_m.get(hi, [])
        all_env = min_max_quadratics_on_interval(coeffs, lo=lo, hi=hi)
        local_env = min_max_quadratics_on_interval(local_coeffs, lo=lo, hi=hi)
        intervals.append(
            {
                "lo": float(lo),
                "hi": float(hi),
                "certified_lower_bound": float(all_env["minimum"]),
                "argmin_m": float(all_env["argmin_m"]),
                "active_witnesses": all_env["active_witnesses"],
                "all_witness_candidate_count": int(all_env["candidate_count"]),
                "local_endpoint_lower_bound": float(local_env["minimum"]),
                "local_endpoint_argmin_m": float(local_env["argmin_m"]),
                "local_endpoint_active_witnesses": local_env["active_witnesses"],
            }
        )
    worst = min(intervals, key=lambda item: float(item["certified_lower_bound"]))
    worst_local = min(intervals, key=lambda item: float(item["local_endpoint_lower_bound"]))
    return {
        "status": "success",
        "method": (
            "Every shifted grid-point dual is m-independent feasible; on each "
            "mean interval, analytically minimize the maximum of all available "
            "feasible witness quadratics. The endpoint-only envelope is also "
            "recorded for the requested two-sided local covering."
        ),
        "intervals": intervals,
        "certified_min_over_0_1": float(worst["certified_lower_bound"]),
        "worst_interval": worst,
        "local_endpoint_certified_min_over_0_1": float(worst_local["local_endpoint_lower_bound"]),
        "local_endpoint_worst_interval": worst_local,
        "exceeds_reference_0_370": bool(float(worst["certified_lower_bound"]) > 0.370),
        "reaches_0_380": bool(float(worst["certified_lower_bound"]) >= 0.380 - 1.0e-12),
    }


def _run_one_row(
    *,
    atoms: dict[str, np.ndarray],
    k: int,
    m: float,
    x_grid_points: int,
    verify_points: int,
) -> dict[str, Any]:
    started = time.time()
    lp = solve_fixed_mean_phase_lp(atoms, m=float(m), x_grid_points=int(x_grid_points))
    compressed = compress_zero_lambdas(lp, tol=0.0)
    cert = certify_fixed_mean_solution(compressed, verify_points=int(verify_points))
    return {
        "K": int(k),
        "phase_count": int(np.asarray(atoms["phase_grid"]).size),
        "m": float(m),
        "x_grid_points": int(x_grid_points),
        "status": "success" if cert["pass_positive_part"] else "verification_failed",
        "lp": lp,
        "compressed_lp": compressed,
        "continuum_verification": cert,
        "elapsed_seconds": float(time.time() - started),
    }


def print_summary(package: dict[str, Any]) -> None:
    print("PHASE_AUGMENTED_DUAL_SCAN", flush=True)
    base = package.get("base_gate", {})
    print(
        f"BASE_GATE K={base.get('K')} raw={base.get('raw_L', float('nan')):.15f} "
        f"verified={base.get('verified_L', float('nan')):.15f} "
        f"diff_even={base.get('diff_from_target_even_cpos', float('nan')):+.3e} "
        f"phi0_active={base.get('active_phi0_count')} nonzero_phase_active={base.get('active_nonzero_phase_count')} "
        f"pass={base.get('pass')}",
        flush=True,
    )
    print("K | m | raw_L | verified_L | downshift | a1 | a2 | active | nonzero_phase_active", flush=True)
    for row in package.get("scan_rows", []):
        cert = row.get("continuum_verification", {})
        phase = cert.get("phase_activity", {})
        print(
            f"{row.get('K', 0):4d} | {float(row.get('m', float('nan'))):.4f} | "
            f"{cert.get('raw_L', float('nan')):.15f} | {cert.get('verified_L_at_m', float('nan')):.15f} | "
            f"{cert.get('required_downshift_for_strict_pass', float('nan')):.3e} | "
            f"{cert.get('a1', float('nan')):+.6e} | {cert.get('a2', float('nan')):+.6e} | "
            f"{cert.get('lambda_positive_count_gt_1e_10', 0):4d} | {phase.get('active_nonzero_phase_count', 0):4d}",
            flush=True,
        )
    if package.get("refinement_rows"):
        print("REFINEMENT_ROWS", flush=True)
        for row in package["refinement_rows"]:
            cert = row.get("continuum_verification", {})
            phase = cert.get("phase_activity", {})
            print(
                f"{row.get('K', 0):4d} | {float(row.get('m', float('nan'))):.5f} | "
                f"{cert.get('raw_L', float('nan')):.15f} | {cert.get('verified_L_at_m', float('nan')):.15f} | "
                f"active={cert.get('lambda_positive_count_gt_1e_10', 0)} nonzero_phase={phase.get('active_nonzero_phase_count', 0)}",
                flush=True,
            )
    print("SPOT_CHECKS", flush=True)
    for row in package.get("spot_check_rows", []):
        cert = row.get("continuum_verification", {})
        phase = cert.get("phase_activity", {})
        print(
            f"K={row.get('K')} m={float(row.get('m', float('nan'))):.3f} "
            f"raw={cert.get('raw_L', float('nan')):.15f} "
            f"verified={cert.get('verified_L_at_m', float('nan')):.15f} "
            f"active={cert.get('lambda_positive_count_gt_1e_10', 0)} "
            f"nonzero_phase_active={phase.get('active_nonzero_phase_count', 0)}",
            flush=True,
        )
    icert = package.get("interval_certificate", {})
    print(
        "INTERVAL_CERTIFIED_MIN "
        f"L={icert.get('certified_min_over_0_1', float('nan')):.15f} "
        f"local_endpoint_L={icert.get('local_endpoint_certified_min_over_0_1', float('nan')):.15f} "
        f"worst_interval={icert.get('worst_interval')} "
        f"exceeds_0_370={icert.get('exceeds_reference_0_370')} reaches_0_380={icert.get('reaches_0_380')}",
        flush=True,
    )
    print(f"VERDICT {package.get('verdict')}", flush=True)


def run_phase_augmented_experiment(
    *,
    out_path: Path = REFINED_JSON,
    scan_k: int = 400,
    spot_k: int = 800,
    scan_m_values: tuple[float, ...] = SCAN_M_VALUES,
    scan_x_grid_points: int = 1001,
    spot_x_grid_points: int = 1001,
    verify_points: int = 200_001,
    max_seconds: float = 1650.0,
    low_m_k_threshold: float = 0.1000000001,
) -> dict[str, Any]:
    started = time.time()
    best = load_b0even_best()
    scan_payload = selected_frequency_payload(best, int(scan_k))
    spot_payload = selected_frequency_payload(best, int(spot_k))
    atoms_by_k = {
        int(scan_k): build_atoms(np.asarray(scan_payload["xi"], dtype=np.float64)),
        int(spot_k): build_atoms(np.asarray(spot_payload["xi"], dtype=np.float64)),
    }

    scan_rows: list[dict[str, Any]] = []
    refinement_rows: list[dict[str, Any]] = []
    spot_rows: list[dict[str, Any]] = []
    package: dict[str, Any] = {
        "schema": "public phase-augmented per-mean C>=0 positive-part dual refined v2",
        "metadata": {
            "source package": "public",
            "created_by": "source/phase_augmented_dual.py",
            "claim_scope": "Continuum-verified fixed-mean lower bounds using phase-shifted cosine ceilings.",
            "scan_K": int(scan_k),
            "low_m_K": int(spot_k),
            "low_m_K_threshold": float(low_m_k_threshold),
            "phase_grid": list(PHASES),
            "scan_x_grid_points": int(scan_x_grid_points),
            "spot_x_grid_points": int(spot_x_grid_points),
            "verify_points": int(verify_points),
            "frequency_ordering": (
                "same as cpos_audit: all retained positive B0_even atoms first, "
                "then inactive certificate_B0even comb frequencies in increasing xi"
            ),
        },
        "references": {
            "target_even_cpos_saturation": TARGET_EVEN_CPOS,
            "reference_m025_verified": REFERENCE_M025,
            "even_value_rounded_request": 0.380444,
        },
        "scan_selection": {key: val for key, val in scan_payload.items() if key not in ("xi", "source_lambda", "indices")},
        "spot_selection": {key: val for key, val in spot_payload.items() if key not in ("xi", "source_lambda", "indices")},
        "scan_rows": scan_rows,
        "refinement_rows": refinement_rows,
        "spot_check_rows": spot_rows,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    for m in scan_m_values:
        elapsed = time.time() - started
        k_for_m = int(spot_k) if float(m) <= float(low_m_k_threshold) else int(scan_k)
        atoms_for_m = atoms_by_k[k_for_m]
        if elapsed > max_seconds - 180.0:
            scan_rows.append({"K": int(k_for_m), "m": float(m), "status": "skipped_time_guard", "elapsed_seconds": float(elapsed)})
            break
        print(f"PHASE_SOLVE_START K={k_for_m} m={float(m):.4f} elapsed={elapsed:.1f}s", flush=True)
        row = _run_one_row(
            atoms=atoms_for_m,
            k=int(k_for_m),
            m=float(m),
            x_grid_points=int(scan_x_grid_points),
            verify_points=int(verify_points),
        )
        scan_rows.append(row)
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        cert = row["continuum_verification"]
        phase = cert["phase_activity"]
        print(
            f"PHASE_SOLVE_DONE K={k_for_m} m={float(m):.4f} "
            f"raw={cert['raw_L']:.15f} verified={cert['verified_L_at_m']:.15f} "
            f"a1={cert['a1']:+.6e} a2={cert['a2']:+.6e} "
            f"active={cert['lambda_positive_count_gt_1e_10']} "
            f"nonzero_phase_active={phase['active_nonzero_phase_count']} elapsed={time.time()-started:.1f}s",
            flush=True,
        )

    successful_scan = [row for row in scan_rows if row.get("status") == "success"]
    if successful_scan:
        base_candidates = [row for row in successful_scan if abs(float(row["m"])) < 1.0e-12]
        if base_candidates:
            base_cert = base_candidates[0]["continuum_verification"]
            phase = base_cert["phase_activity"]
            package["base_gate"] = {
                "K": int(base_candidates[0].get("K", scan_k)),
                "raw_L": float(base_cert["raw_L"]),
                "verified_L": float(base_cert["verified_L_at_m"]),
                "diff_from_target_even_cpos": float(base_cert["verified_L_at_m"] - TARGET_EVEN_CPOS),
                "diff_from_0_380444": float(base_cert["verified_L_at_m"] - 0.380444),
                "a1": float(base_cert["a1"]),
                "a2": float(base_cert["a2"]),
                "active_phi0_count": int(phase["active_phi0_count"]),
                "active_nonzero_phase_count": int(phase["active_nonzero_phase_count"]),
                "active_nonzero_phase_lambda_sum": float(phase["active_nonzero_phase_lambda_sum"]),
                "active_phi0_lambda_sum": float(phase["active_phi0_lambda_sum"]),
                "pass": bool(
                    abs(float(base_cert["verified_L_at_m"]) - 0.380444) <= 1.0e-5
                    and abs(float(base_cert["a1"])) <= 1.0e-6
                    and float(phase["active_nonzero_phase_lambda_sum"])
                    <= 1.0e-4 * max(1.0, float(phase["active_phi0_lambda_sum"]))
                ),
            }

        grid_min_row = min(successful_scan, key=lambda row: float(row["continuum_verification"]["verified_L_at_m"]))
        package["grid_minimum"] = {
            "m": float(grid_min_row["m"]),
            "verified_L": float(grid_min_row["continuum_verification"]["verified_L_at_m"]),
            "raw_L": float(grid_min_row["continuum_verification"]["raw_L"]),
        }
        package["interval_certificate"] = interval_certificate(
            successful_scan + [row for row in refinement_rows if row.get("status") == "success"]
        )

    all_scan = [row for row in scan_rows + refinement_rows if row.get("status") == "success"]
    if all_scan:
        icert = package.get("interval_certificate", interval_certificate(all_scan))
        package["interval_certificate"] = icert
        m025 = min(all_scan, key=lambda row: abs(float(row["m"]) - 0.25))
        base = package.get("base_gate", {})
        package["m025_gate"] = {
            "nearest_m": float(m025["m"]),
            "verified_L": float(m025["continuum_verification"]["verified_L_at_m"]),
            "raw_L": float(m025["continuum_verification"]["raw_L"]),
            "gain_over_reference_m025": float(m025["continuum_verification"]["verified_L_at_m"] - REFERENCE_M025),
            "substantially_above_reference": bool(float(m025["continuum_verification"]["verified_L_at_m"]) > REFERENCE_M025 + 1.0e-3),
        }
        package["verdict"] = {
            "base_gate_pass": bool(base.get("pass", False)),
            "scan_grid_min_m": float(min(all_scan, key=lambda row: float(row["continuum_verification"]["verified_L_at_m"]))["m"]),
            "scan_grid_min_verified_L": float(min(all_scan, key=lambda row: float(row["continuum_verification"]["verified_L_at_m"]))["continuum_verification"]["verified_L_at_m"]),
            "interval_certified_min": float(icert.get("certified_min_over_0_1", float("nan"))),
            "local_endpoint_interval_certified_min": float(icert.get("local_endpoint_certified_min_over_0_1", float("nan"))),
            "gain_over_0_370": float(icert.get("certified_min_over_0_1", float("nan")) - 0.370),
            "gap_to_even_cpos": float(TARGET_EVEN_CPOS - icert.get("certified_min_over_0_1", float("nan"))),
            "local_endpoint_gap_to_even_cpos": float(
                TARGET_EVEN_CPOS - icert.get("local_endpoint_certified_min_over_0_1", float("nan"))
            ),
            "interpretation": (
                "phase_augmented_dual_certifies_general_improvement"
                if bool(icert.get("exceeds_reference_0_370", False))
                else "phase_augmented_dual_does_not_improve_reference"
            ),
        }
    else:
        package["verdict"] = {"interpretation": "no_successful_scan_rows"}
    package["elapsed_seconds"] = float(time.time() - started)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_summary(package)
    return package


if __name__ == "__main__":
    run_phase_augmented_experiment()
