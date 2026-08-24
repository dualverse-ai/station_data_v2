"""Exact SOC per-frequency dual for the minimum-overlap lower-bound study.

This upgrades the phase-grid approximation in ``phase_augmented_dual.py``.
For each fixed mean m it solves a finite grid relaxation of

    G0(x) = a0 + a1*x + a2*x^2
            - sum_k (alpha_k cos(xi_k*x) + beta_k sin(xi_k*x))

with ``int max(0, G0) <= 1`` and the exact support-function charge

    sinc(xi)^2 * (alpha_k + beta_k^2 / alpha_k), alpha_k >= 0.

The finite grid solution is then conservatively verified on a dense grid by
the same positive-part curvature-envelope downshift used in the C>=0 audits.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import cvxpy as cp
import numpy as np

from cpos_audit import (
    conservative_positive_upper_from_samples,
    selected_frequency_payload,
    shift_needed_for_positive_mass,
)
from cpos_augmented_dual import load_b0even_best
from phase_augmented_dual import (
    SCAN_M_VALUES,
    TARGET_EVEN_CPOS,
    interval_certificate,
)
from verify_B0 import sinc2


ROOT = Path("source")
OUT_JSON = ROOT / "soc_dual.json"
PHASE_GRID_REFERENCE = 0.380383112550269


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


def support_function(alpha: np.ndarray, beta: np.ndarray, xi: np.ndarray) -> float:
    """Evaluate sum sinc2(xi) * (alpha + beta^2 / alpha)."""
    alpha = np.asarray(alpha, dtype=np.float64)
    beta = np.asarray(beta, dtype=np.float64)
    xi = np.asarray(xi, dtype=np.float64)
    if np.any(alpha < -1.0e-10):
        return float("inf")
    active = alpha > 1.0e-14
    if np.any((~active) & (np.abs(beta) > 1.0e-10)):
        return float("inf")
    out = np.zeros_like(alpha)
    out[active] = alpha[active] + beta[active] * beta[active] / alpha[active]
    return float(sinc2(xi) @ out)


def verify_support_formula() -> dict[str, Any]:
    """Check the parabola support and its reduction to one phase atom."""
    rng = np.random.default_rng(448)
    rows = []
    max_closed_vs_stationary = 0.0
    max_phase_error = 0.0
    for phi in (0.0, math.pi / 8.0, -math.pi / 8.0, math.pi / 4.0, -math.pi / 4.0):
        for _ in range(3):
            xi = float(rng.uniform(0.25, 35.0))
            s2 = float(sinc2(np.asarray([xi]))[0])
            lam = float(rng.uniform(0.01, 3.0))
            alpha = lam * math.cos(phi)
            beta = lam * math.sin(phi)
            closed = s2 * (alpha + beta * beta / alpha)
            phase = lam * s2 / math.cos(phi)
            q_star = 2.0 * beta * s2 / alpha
            p_star = s2 - q_star * q_star / (4.0 * s2)
            stationary = alpha * p_star + beta * q_star
            closed_vs_stationary = abs(closed - stationary)
            phase_error = abs(closed - phase)
            max_closed_vs_stationary = max(max_closed_vs_stationary, closed_vs_stationary)
            max_phase_error = max(max_phase_error, phase_error)
            rows.append(
                {
                    "xi": xi,
                    "phase": phi,
                    "lambda": lam,
                    "alpha": alpha,
                    "beta": beta,
                    "closed_support": closed,
                    "stationary_support": stationary,
                    "phase_atom_support": phase,
                    "q_star": q_star,
                    "closed_vs_stationary_abs_error": closed_vs_stationary,
                    "phase_reduction_abs_error": phase_error,
                }
            )
    return {
        "status": "pass" if max_closed_vs_stationary <= 1.0e-12 and max_phase_error <= 1.0e-12 else "fail",
        "derivation": (
            "For alpha>=0, maximize alpha*(s^2-Q^2/(4s^2))+beta*Q. "
            "The stationary point Q=2 beta s^2/alpha gives "
            "s^2*(alpha+beta^2/alpha). Setting alpha=lambda cos(phi), "
            "beta=lambda sin(phi) gives lambda*s^2/cos(phi), exactly the "
            "single phase-atom ceiling."
        ),
        "max_closed_vs_stationary_abs_error": max_closed_vs_stationary,
        "max_phase_reduction_abs_error": max_phase_error,
        "rows": rows,
    }


def evaluate_g_chunked(
    x: np.ndarray,
    *,
    a0: float,
    a1: float,
    a2: float,
    xi: np.ndarray,
    alpha: np.ndarray,
    beta: np.ndarray,
    chunk: int = 2048,
) -> np.ndarray:
    x = np.asarray(x, dtype=np.float64)
    xi = np.asarray(xi, dtype=np.float64)
    alpha = np.asarray(alpha, dtype=np.float64)
    beta = np.asarray(beta, dtype=np.float64)
    out = np.empty_like(x)
    for start in range(0, x.size, int(chunk)):
        stop = min(x.size, start + int(chunk))
        xs = x[start:stop]
        if xi.size:
            trig = (
                np.cos(xs[:, None] * xi[None, :]) @ alpha
                + np.sin(xs[:, None] * xi[None, :]) @ beta
            )
        else:
            trig = 0.0
        out[start:stop] = float(a0) + float(a1) * xs + float(a2) * xs * xs - trig
    return out


def curvature_bound(a2: float, xi: np.ndarray, alpha: np.ndarray, beta: np.ndarray) -> float:
    xi = np.asarray(xi, dtype=np.float64)
    return float(2.0 * abs(float(a2)) + float(np.sum((np.abs(alpha) + np.abs(beta)) * xi * xi)))


def derivative_bound(a1: float, a2: float, xi: np.ndarray, alpha: np.ndarray, beta: np.ndarray) -> float:
    xi = np.asarray(xi, dtype=np.float64)
    return float(abs(float(a1)) + 4.0 * abs(float(a2)) + float(np.sum((np.abs(alpha) + np.abs(beta)) * xi)))


def l_of_m(
    m: float,
    *,
    a0: float,
    a1: float,
    a2: float,
    xi: np.ndarray,
    alpha: np.ndarray,
    beta: np.ndarray,
) -> float:
    mm = float(m)
    return float(
        float(a0)
        + float(a1) * mm
        + float(a2) * (2.0 / 3.0 + 0.5 * mm * mm)
        - support_function(alpha, beta, xi)
    )


def solve_fixed_mean_soc(
    xi: np.ndarray,
    *,
    m: float,
    x_grid_points: int,
    solver: str = "CLARABEL",
    max_iter: int = 500,
    tol: float = 1.0e-8,
) -> dict[str, Any]:
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    k = int(xi.size)
    m = float(m)
    x = np.linspace(-2.0, 2.0, int(x_grid_points), dtype=np.float64)
    weights = np.full(x.size, 4.0 / (x.size - 1), dtype=np.float64)
    weights[0] *= 0.5
    weights[-1] *= 0.5
    cos_grid = np.cos(x[:, None] * xi[None, :]) if k else np.empty((x.size, 0))
    sin_grid = np.sin(x[:, None] * xi[None, :]) if k else np.empty((x.size, 0))
    s2 = sinc2(xi)

    a0 = cp.Variable(name="a0")
    a1 = cp.Variable(name="a1")
    a2 = cp.Variable(name="a2")
    alpha = cp.Variable(k, nonneg=True, name="alpha")
    beta = cp.Variable(k, name="beta")
    gamma = cp.Variable(k, nonneg=True, name="gamma")
    slack = cp.Variable(x.size, nonneg=True, name="positive_part_slack")

    g_expr = a0 + a1 * x + a2 * (x * x) - cos_grid @ alpha - sin_grid @ beta
    constraints = [g_expr <= slack, weights @ slack <= 1.0]
    constraints.extend(
        cp.SOC(alpha[i] + gamma[i], cp.hstack([2.0 * beta[i], alpha[i] - gamma[i]]))
        for i in range(k)
    )
    support_terms = cp.multiply(s2, alpha + gamma)
    moment2 = 2.0 / 3.0 + 0.5 * m * m
    objective = cp.Maximize(a0 + a1 * m + a2 * moment2 - cp.sum(support_terms))
    problem = cp.Problem(objective, constraints)

    started = time.time()
    solve_kwargs: dict[str, Any] = {"solver": solver, "verbose": False}
    if solver.upper() == "CLARABEL":
        solve_kwargs.update({"max_iter": int(max_iter), "tol_gap_abs": float(tol), "tol_feas": float(tol)})
    elif solver.upper() == "SCS":
        solve_kwargs.update({"max_iters": int(max_iter), "eps": 2.0e-5})
    value = problem.solve(**solve_kwargs)
    elapsed = time.time() - started
    if problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
        raise RuntimeError(f"SOC solve failed at m={m}: {problem.status}")

    alpha_v = np.maximum(np.asarray(alpha.value, dtype=np.float64), 0.0)
    beta_v = np.asarray(beta.value, dtype=np.float64)
    gamma_v = np.maximum(np.asarray(gamma.value, dtype=np.float64), 0.0)
    tiny = alpha_v <= 1.0e-11
    beta_v[tiny & (np.abs(beta_v) <= 1.0e-8)] = 0.0
    a0_v = float(a0.value)
    a1_v = float(a1.value)
    a2_v = float(a2.value)
    raw_l = l_of_m(m, a0=a0_v, a1=a1_v, a2=a2_v, xi=xi, alpha=alpha_v, beta=beta_v)
    grid_g = a0_v + a1_v * x + a2_v * x * x - cos_grid @ alpha_v - sin_grid @ beta_v
    return {
        "m": m,
        "xi": xi,
        "alpha": alpha_v,
        "beta": beta_v,
        "gamma": gamma_v,
        "a0": a0_v,
        "a1": a1_v,
        "a2": a2_v,
        "raw_L": raw_l,
        "solver_objective_L": float(value),
        "raw_objective_residual": float(raw_l - float(value)),
        "selected_frequency_count": k,
        "x_grid_points": int(x.size),
        "grid_positive_integral_trapezoid": float(np.trapezoid(np.maximum(grid_g, 0.0), x)),
        "grid_min_G": float(np.min(grid_g)),
        "grid_max_G": float(np.max(grid_g)),
        "grid_argmin_G": float(x[int(np.argmin(grid_g))]),
        "grid_argmax_G": float(x[int(np.argmax(grid_g))]),
        "alpha_positive_count_gt_1e_10": int(np.sum(alpha_v > 1.0e-10)),
        "beta_active_count_gt_1e_8": int(np.sum(np.abs(beta_v) > 1.0e-8)),
        "beta_l1": float(np.sum(np.abs(beta_v))),
        "beta_linf": float(np.max(np.abs(beta_v))) if beta_v.size else 0.0,
        "alpha_l1": float(np.sum(alpha_v)),
        "support_charge": support_function(alpha_v, beta_v, xi),
        "linearized_support_charge": float(s2 @ (alpha_v + gamma_v)),
        "support_charge_residual": float(float(s2 @ (alpha_v + gamma_v)) - support_function(alpha_v, beta_v, xi)),
        "solver": solver,
        "solver_status": str(problem.status),
        "solve_elapsed_seconds": float(elapsed),
    }


def compress_zero_pairs(soc: dict[str, Any], *, tol_alpha: float = 1.0e-12, tol_beta: float = 1.0e-10) -> dict[str, Any]:
    alpha = np.asarray(soc["alpha"], dtype=np.float64)
    beta = np.asarray(soc["beta"], dtype=np.float64)
    mask = (alpha > float(tol_alpha)) | (np.abs(beta) > float(tol_beta))
    out = dict(soc)
    for key in ("xi", "alpha", "beta"):
        out[key] = np.asarray(soc[key], dtype=np.float64)[mask]
    out["selected_frequency_count"] = int(np.sum(mask))
    out["zero_pruned_count"] = int(np.sum(~mask))
    out["raw_L"] = l_of_m(
        float(out["m"]),
        a0=float(out["a0"]),
        a1=float(out["a1"]),
        a2=float(out["a2"]),
        xi=out["xi"],
        alpha=out["alpha"],
        beta=out["beta"],
    )
    out["support_charge"] = support_function(out["alpha"], out["beta"], out["xi"])
    return out


def certify_fixed_mean_solution(
    soc: dict[str, Any],
    *,
    verify_points: int = 200_001,
    chunk: int = 2048,
) -> dict[str, Any]:
    xi = np.asarray(soc["xi"], dtype=np.float64)
    alpha = np.asarray(soc["alpha"], dtype=np.float64)
    beta = np.asarray(soc["beta"], dtype=np.float64)
    a0 = float(soc["a0"])
    a1 = float(soc["a1"])
    a2 = float(soc["a2"])
    m0 = float(soc["m"])
    curvature = curvature_bound(a2, xi, alpha, beta)
    slope = derivative_bound(a1, a2, xi, alpha, beta)
    roundoff_pad = 1.0e-12 * (
        1.0 + abs(a0) + 2.0 * abs(a1) + 4.0 * abs(a2) + float(np.sum(np.abs(alpha) + np.abs(beta)))
    )
    target = 1.0 - 1.0e-10
    started = time.time()
    x = np.linspace(-2.0, 2.0, int(verify_points), dtype=np.float64)
    values = evaluate_g_chunked(x, a0=a0, a1=a1, a2=a2, xi=xi, alpha=alpha, beta=beta, chunk=chunk)
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
    verified_l = l_of_m(m0, a0=shifted_a0, a1=a1, a2=a2, xi=xi, alpha=alpha, beta=beta)
    shifted_values = values - req_shift
    active = np.flatnonzero((alpha > 1.0e-10) | (np.abs(beta) > 1.0e-8))
    if active.size:
        order = np.argsort(alpha[active] + np.abs(beta[active]))[-20:][::-1]
        top = active[order]
    else:
        top = np.empty(0, dtype=np.int64)
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
        "raw_L": float(soc["raw_L"]),
        "verified_L_at_m": float(verified_l),
        "downshift_loss": float(req_shift),
        "a0_raw": a0,
        "shifted_a0": float(shifted_a0),
        "a1": a1,
        "a2": a2,
        "alpha_positive_count_gt_1e_10": int(np.sum(alpha > 1.0e-10)),
        "beta_active_count_gt_1e_8": int(np.sum(np.abs(beta) > 1.0e-8)),
        "beta_l1": float(np.sum(np.abs(beta))),
        "beta_linf": float(np.max(np.abs(beta))) if beta.size else 0.0,
        "alpha_l1": float(np.sum(alpha)),
        "xi_max": float(np.max(xi)) if xi.size else None,
        "second_derivative_sup_bound": curvature,
        "first_derivative_sup_bound": slope,
        "roundoff_pad_per_endpoint": float(roundoff_pad),
        "dense_trapezoid_positive_shifted": float(np.trapezoid(np.maximum(shifted_values, 0.0), x)),
        "dense_min_G_shifted": float(np.min(shifted_values)),
        "dense_max_G_shifted": float(np.max(shifted_values)),
        "dense_argmin_G_shifted": float(x[int(np.argmin(shifted_values))]),
        "dense_argmax_G_shifted": float(x[int(np.argmax(shifted_values))]),
        "top_soc_atoms": [
            {
                "xi": float(xi[int(i)]),
                "alpha": float(alpha[int(i)]),
                "beta": float(beta[int(i)]),
                "beta_over_alpha": float(beta[int(i)] / alpha[int(i)]) if alpha[int(i)] > 1.0e-14 else None,
            }
            for i in top
        ],
        "elapsed_seconds": float(time.time() - started),
        "verification_method": (
            "Full-domain grid plus curvature envelope; then downshift a0 until "
            "the conservative upper integral of max(0,G0) is <= 1-1e-10."
        ),
    }


def row_quadratic_coefficients(row: dict[str, Any]) -> dict[str, Any]:
    cert = row["continuum_verification"]
    soc = row["compressed_soc"]
    a0 = float(cert["shifted_a0"])
    a1 = float(cert["a1"])
    a2 = float(cert["a2"])
    c0 = a0 + (2.0 / 3.0) * a2 - support_function(
        np.asarray(soc["alpha"], dtype=np.float64),
        np.asarray(soc["beta"], dtype=np.float64),
        np.asarray(soc["xi"], dtype=np.float64),
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
    return best or {"minimum": float("nan"), "argmin_m": lo, "candidate_count": 0, "active_witnesses": []}


def soc_interval_certificate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    valid = [row for row in rows if row.get("status") == "success"]
    if len(valid) < 2:
        return {"status": "insufficient_rows"}
    valid.sort(key=lambda row: float(row["m"]))
    coeffs = [row_quadratic_coefficients(row) for row in valid]
    by_m: dict[float, list[dict[str, Any]]] = {}
    for row, coeff in zip(valid, coeffs):
        by_m.setdefault(round(float(row["m"]), 12), []).append(coeff)
    unique_m = sorted(by_m)
    intervals = []
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
            "Every shifted SOC dual is m-independent feasible after positive-part "
            "verification; on each mean interval this analytically minimizes the "
            "maximum of all available feasible witness quadratics. Endpoint-only "
            "two-sided local covering is also recorded."
        ),
        "intervals": intervals,
        "certified_min_over_0_1": float(worst["certified_lower_bound"]),
        "worst_interval": worst,
        "local_endpoint_certified_min_over_0_1": float(worst_local["local_endpoint_lower_bound"]),
        "local_endpoint_worst_interval": worst_local,
        "exceeds_phase_grid_reference": bool(float(worst["certified_lower_bound"]) > PHASE_GRID_REFERENCE),
        "reaches_even_cpos": bool(float(worst["certified_lower_bound"]) >= TARGET_EVEN_CPOS - 1.0e-7),
    }


def _run_one_row(
    *,
    xi: np.ndarray,
    k: int,
    m: float,
    x_grid_points: int,
    verify_points: int,
    solver: str,
    max_iter: int,
) -> dict[str, Any]:
    started = time.time()
    soc = solve_fixed_mean_soc(
        xi,
        m=float(m),
        x_grid_points=int(x_grid_points),
        solver=solver,
        max_iter=max_iter,
    )
    compressed = compress_zero_pairs(soc)
    cert = certify_fixed_mean_solution(compressed, verify_points=int(verify_points))
    return {
        "K": int(k),
        "m": float(m),
        "x_grid_points": int(x_grid_points),
        "status": "success" if cert["pass_positive_part"] else "verification_failed",
        "soc": soc,
        "compressed_soc": compressed,
        "continuum_verification": cert,
        "elapsed_seconds": float(time.time() - started),
    }


def print_summary(package: dict[str, Any]) -> None:
    print("SOC_DUAL_SCAN", flush=True)
    sf = package.get("support_formula_check", {})
    print(
        f"SUPPORT_FORMULA status={sf.get('status')} "
        f"max_stationary_err={sf.get('max_closed_vs_stationary_abs_error', float('nan')):.3e} "
        f"max_phase_err={sf.get('max_phase_reduction_abs_error', float('nan')):.3e}",
        flush=True,
    )
    base = package.get("base_gate", {})
    print(
        f"BASE_GATE K={base.get('K')} raw={base.get('raw_L', float('nan')):.15f} "
        f"verified={base.get('verified_L', float('nan')):.15f} "
        f"diff_even={base.get('diff_from_target_even_cpos', float('nan')):+.3e} "
        f"beta_l1={base.get('beta_l1', float('nan')):.3e} beta_linf={base.get('beta_linf', float('nan')):.3e} "
        f"pass={base.get('pass')}",
        flush=True,
    )
    print("K | m | raw_L | verified_L | downshift | a1 | a2 | alpha_active | beta_active | beta_l1", flush=True)
    for row in package.get("scan_rows", []):
        cert = row.get("continuum_verification", {})
        print(
            f"{row.get('K', 0):4d} | {float(row.get('m', float('nan'))):.4f} | "
            f"{cert.get('raw_L', float('nan')):.15f} | {cert.get('verified_L_at_m', float('nan')):.15f} | "
            f"{cert.get('required_downshift_for_strict_pass', float('nan')):.3e} | "
            f"{cert.get('a1', float('nan')):+.6e} | {cert.get('a2', float('nan')):+.6e} | "
            f"{cert.get('alpha_positive_count_gt_1e_10', 0):4d} | "
            f"{cert.get('beta_active_count_gt_1e_8', 0):4d} | "
            f"{cert.get('beta_l1', float('nan')):.3e}",
            flush=True,
        )
    icert = package.get("interval_certificate", {})
    print(
        "INTERVAL_CERTIFIED_MIN "
        f"L={icert.get('certified_min_over_0_1', float('nan')):.15f} "
        f"local_endpoint_L={icert.get('local_endpoint_certified_min_over_0_1', float('nan')):.15f} "
        f"worst_interval={icert.get('worst_interval')} "
        f"exceeds_reference={icert.get('exceeds_phase_grid_reference')} "
        f"reaches_even={icert.get('reaches_even_cpos')}",
        flush=True,
    )
    print(f"VERDICT {package.get('verdict')}", flush=True)


def run_soc_dual_experiment(
    *,
    out_path: Path = OUT_JSON,
    scan_k: int = 400,
    low_m_k: int = 400,
    scan_m_values: tuple[float, ...] = SCAN_M_VALUES,
    x_grid_points: int = 1001,
    verify_points: int = 200_001,
    low_m_k_threshold: float = 0.1000000001,
    solver: str = "CLARABEL",
    max_iter: int = 500,
    max_seconds: float = 1_650.0,
) -> dict[str, Any]:
    started = time.time()
    best = load_b0even_best()
    scan_payload = selected_frequency_payload(best, int(scan_k))
    low_payload = selected_frequency_payload(best, int(low_m_k))
    xi_by_k = {
        int(scan_k): np.asarray(scan_payload["xi"], dtype=np.float64),
        int(low_m_k): np.asarray(low_payload["xi"], dtype=np.float64),
    }
    rows: list[dict[str, Any]] = []
    package: dict[str, Any] = {
        "schema": "public exact SOC per-mean C>=0 positive-part dual v1",
        "metadata": {
            "source package": "public",
            "created_by": "source/soc_dual.py",
            "claim_scope": "Continuum-verified fixed-mean lower bounds using exact per-frequency SOC support.",
            "scan_K": int(scan_k),
            "low_m_K": int(low_m_k),
            "low_m_K_threshold": float(low_m_k_threshold),
            "K800_fallback_note": (
                "A local timing probe for one K=800, m=0 row with the requested "
                "1001 optimization grid and 200001 verifier took about 173 s, "
                "so the official run uses the instruction's fallback policy: "
                "K=400 throughout to complete the full m-grid and interval certificate."
            ),
            "x_grid_points": int(x_grid_points),
            "verify_points": int(verify_points),
            "solver": solver,
            "max_iter": int(max_iter),
            "frequency_ordering": (
                "same as cpos_audit: all retained positive B0_even atoms first, "
                "then inactive certificate_B0even comb frequencies in increasing xi"
            ),
        },
        "references": {
            "target_even_cpos_saturation": TARGET_EVEN_CPOS,
            "reference_phase_grid_general_bound": PHASE_GRID_REFERENCE,
            "even_value_rounded_request": 0.380444,
        },
        "support_formula_check": verify_support_formula(),
        "scan_selection": {key: val for key, val in scan_payload.items() if key not in ("xi", "source_lambda", "indices")},
        "low_m_selection": {key: val for key, val in low_payload.items() if key not in ("xi", "source_lambda", "indices")},
        "scan_rows": rows,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    for m in scan_m_values:
        elapsed = time.time() - started
        if elapsed > max_seconds - 180.0:
            rows.append({"m": float(m), "status": "skipped_time_guard", "elapsed_seconds": float(elapsed)})
            break
        k_for_m = int(low_m_k) if float(m) <= float(low_m_k_threshold) else int(scan_k)
        xi = xi_by_k[k_for_m]
        print(f"SOC_SOLVE_START K={k_for_m} m={float(m):.4f} elapsed={elapsed:.1f}s", flush=True)
        row = _run_one_row(
            xi=xi,
            k=k_for_m,
            m=float(m),
            x_grid_points=int(x_grid_points),
            verify_points=int(verify_points),
            solver=solver,
            max_iter=max_iter,
        )
        rows.append(row)
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        cert = row["continuum_verification"]
        print(
            f"SOC_SOLVE_DONE K={k_for_m} m={float(m):.4f} "
            f"raw={cert['raw_L']:.15f} verified={cert['verified_L_at_m']:.15f} "
            f"a1={cert['a1']:+.6e} a2={cert['a2']:+.6e} "
            f"alpha_active={cert['alpha_positive_count_gt_1e_10']} "
            f"beta_active={cert['beta_active_count_gt_1e_8']} beta_l1={cert['beta_l1']:.3e} "
            f"elapsed={time.time()-started:.1f}s",
            flush=True,
        )

    successful = [row for row in rows if row.get("status") == "success"]
    if successful:
        base_candidates = [row for row in successful if abs(float(row["m"])) < 1.0e-12]
        if base_candidates:
            base_cert = base_candidates[0]["continuum_verification"]
            package["base_gate"] = {
                "K": int(base_candidates[0].get("K", low_m_k)),
                "raw_L": float(base_cert["raw_L"]),
                "verified_L": float(base_cert["verified_L_at_m"]),
                "diff_from_target_even_cpos": float(base_cert["verified_L_at_m"] - TARGET_EVEN_CPOS),
                "diff_from_0_380444": float(base_cert["verified_L_at_m"] - 0.380444),
                "a1": float(base_cert["a1"]),
                "a2": float(base_cert["a2"]),
                "beta_l1": float(base_cert["beta_l1"]),
                "beta_linf": float(base_cert["beta_linf"]),
                "pass": bool(
                    abs(float(base_cert["verified_L_at_m"]) - 0.380444) <= 1.0e-5
                    and abs(float(base_cert["a1"])) <= 1.0e-6
                    and float(base_cert["beta_l1"]) <= 1.0e-5
                ),
            }
        grid_min_row = min(successful, key=lambda row: float(row["continuum_verification"]["verified_L_at_m"]))
        package["grid_minimum"] = {
            "m": float(grid_min_row["m"]),
            "verified_L": float(grid_min_row["continuum_verification"]["verified_L_at_m"]),
            "raw_L": float(grid_min_row["continuum_verification"]["raw_L"]),
            "gap_to_even_cpos": float(TARGET_EVEN_CPOS - grid_min_row["continuum_verification"]["verified_L_at_m"]),
        }
        package["interval_certificate"] = soc_interval_certificate(successful)
        icert = package["interval_certificate"]
        package["verdict"] = {
            "base_gate_pass": bool(package.get("base_gate", {}).get("pass", False)),
            "grid_min_m": float(grid_min_row["m"]),
            "grid_min_verified_L": float(grid_min_row["continuum_verification"]["verified_L_at_m"]),
            "interval_certified_min": float(icert.get("certified_min_over_0_1", float("nan"))),
            "local_endpoint_interval_certified_min": float(icert.get("local_endpoint_certified_min_over_0_1", float("nan"))),
            "gain_over_reference_phase_grid": float(icert.get("certified_min_over_0_1", float("nan")) - PHASE_GRID_REFERENCE),
            "gap_to_even_cpos": float(TARGET_EVEN_CPOS - icert.get("certified_min_over_0_1", float("nan"))),
            "dip_fate": (
                "filled_to_even_within_1e-7"
                if float(icert.get("certified_min_over_0_1", float("nan"))) >= TARGET_EVEN_CPOS - 1.0e-7
                else "residual_minimum_below_even_persists"
            ),
        }
    else:
        package["verdict"] = {"interpretation": "no_successful_scan_rows"}
    package["elapsed_seconds"] = float(time.time() - started)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_summary(package)
    return package


if __name__ == "__main__":
    run_soc_dual_experiment()
