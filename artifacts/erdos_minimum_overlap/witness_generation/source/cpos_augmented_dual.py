"""Positive-part augmented even-class dual for the overlap problem.

This module tests the relaxed dual

    G(x) = a0 + a2*x^2 - sum_k lambda_k cos(xi_k*x),  lambda_k >= 0,

with the continuum feasibility condition int max(0, G) <= 1.  The objective is

    L = a0 + (2/3)*a2 - sum_k lambda_k*sinc(xi_k)^2.

The finite LP uses grid slacks for max(0, G).  The reported certificate then
verifies int max(0, G) <= 1 on the continuum by integrating a curvature upper
envelope on each interval of a much finer grid.
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

from even_dual_optimize import solve_grid_lp
from verify_B0 import int_cos_over_domain, sinc2


ROOT = Path("source")
OUT_JSON = ROOT / "cpos_augmented_dual.json"
CONVERGENCE_JSON = ROOT / "cpos_augmented_convergence.json"
TARGET_B0_EVEN = 0.370112650585918
BEST_EVEN_CONSTRUCTION = 0.381415941558174


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


def load_b0even_best() -> dict[str, Any]:
    return json.loads((ROOT / "certificate_B0even.json").read_text(encoding="utf-8"))["best"]


def active_frequency_support(best: dict[str, Any], *, limit: int | None = None) -> tuple[np.ndarray, np.ndarray]:
    xi = np.asarray(best["dual"]["frequencies"], dtype=np.float64)
    lam = np.asarray(best["dual"]["lambda"], dtype=np.float64)
    active = np.flatnonzero(lam > 1.0e-10)
    if limit is not None and active.size > int(limit):
        active = active[np.argsort(lam[active])[-int(limit) :]]
    active = active[np.argsort(xi[active])]
    return xi[active], lam[active]


def select_convergence_frequencies(best: dict[str, Any], k_requested: int) -> dict[str, Any]:
    """Select the K-frequency comb used for the convergence sweep.

    The retained B0_even comb has 2560 frequencies but only 200 positive
    multipliers.  For K below 200 we use the strongest retained atoms, matching
    a predecessor computation's 80-atom relaxed run.  For K >= 200 we include all retained active
    atoms and then append inactive certificate-comb frequencies in natural
    order, so the classical B0_even certificate remains available with zero
    multipliers on appended atoms.
    """
    xi = np.asarray(best["dual"]["frequencies"], dtype=np.float64)
    lam = np.asarray(best["dual"]["lambda"], dtype=np.float64)
    active = np.flatnonzero(lam > 1.0e-10)
    inactive = np.flatnonzero(lam <= 1.0e-10)
    k = min(int(k_requested), int(xi.size))
    if k <= active.size:
        selected = active[np.argsort(lam[active])[-k:]]
        mode = "strongest_retained_active_atoms"
    else:
        selected = np.concatenate((active, inactive[: k - active.size]))
        mode = "all_retained_active_atoms_plus_low_frequency_inactive_comb"
    selected = selected[np.argsort(xi[selected])]
    return {
        "requested_K": int(k_requested),
        "selected_K": int(selected.size),
        "selection_mode": mode,
        "active_atoms_in_certificate": int(active.size),
        "full_comb_frequency_count": int(xi.size),
        "xi": xi[selected],
        "source_lambda": lam[selected],
        "selected_source_positive_count_gt_1e_10": int(np.sum(lam[selected] > 1.0e-10)),
        "min_xi": float(np.min(xi[selected])) if selected.size else None,
        "max_xi": float(np.max(xi[selected])) if selected.size else None,
    }


def bound_constant(a0: float, a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(float(a0) + (2.0 / 3.0) * float(a2) - float(sinc2(xi) @ lam))


def solve_base_gate(best: dict[str, Any]) -> dict[str, Any]:
    xi, _ = active_frequency_support(best, limit=None)
    started = time.time()
    solved = solve_grid_lp(xi, x_grid_points=20_001, grid_margin=4.0e-6)
    elapsed = time.time() - started
    value = float(solved["lp_objective"])
    diff = value - TARGET_B0_EVEN
    return {
        "status": "pass" if abs(diff) <= 5.0e-7 else "fail",
        "target_B0_even": TARGET_B0_EVEN,
        "value": value,
        "difference_from_target": float(diff),
        "frequency_count": int(xi.size),
        "full_comb_frequency_count": int(np.asarray(best["dual"]["frequencies"]).size),
        "x_grid_points": 20_001,
        "grid_margin": 4.0e-6,
        "grid_min_G": float(solved["grid_min_G"]),
        "active_lambda_count": int(solved["lambda_positive_count_gt_1e_10"]),
        "elapsed_seconds": float(elapsed),
        "note": (
            "Solved on the positive-lambda support of certificate_B0even.json "
            "rather than the 2560-column zero-augmented comb; this reproduces "
            "the retained certified value within tolerance."
        ),
    }


def solve_base_gate_for_xi(xi: np.ndarray, *, x_grid_points: int = 20_001) -> dict[str, Any]:
    xi = np.asarray(xi, dtype=np.float64)
    started = time.time()
    solved = solve_grid_lp(xi, x_grid_points=int(x_grid_points), grid_margin=4.0e-6)
    elapsed = time.time() - started
    value = float(solved["lp_objective"])
    diff = value - TARGET_B0_EVEN
    return {
        "status": "pass" if abs(diff) <= 5.0e-7 else "fail",
        "target_B0_even": TARGET_B0_EVEN,
        "value": value,
        "difference_from_target": float(diff),
        "frequency_count": int(xi.size),
        "x_grid_points": int(x_grid_points),
        "grid_margin": 4.0e-6,
        "grid_min_G": float(solved["grid_min_G"]),
        "active_lambda_count": int(solved["lambda_positive_count_gt_1e_10"]),
        "elapsed_seconds": float(elapsed),
    }


def solve_relaxed_grid_lp(best: dict[str, Any], *, active_limit: int = 80) -> dict[str, Any]:
    xi, source_lam = active_frequency_support(best, limit=active_limit)
    return solve_relaxed_grid_lp_for_xi(
        xi,
        source_lam=source_lam,
        full_active_frequency_count=int(np.sum(np.asarray(best["dual"]["lambda"]) > 1.0e-10)),
        full_comb_frequency_count=int(np.asarray(best["dual"]["frequencies"]).size),
    )


def solve_relaxed_grid_lp_for_xi(
    xi: np.ndarray,
    *,
    source_lam: np.ndarray | None = None,
    full_active_frequency_count: int | None = None,
    full_comb_frequency_count: int | None = None,
    x_grid_points: int = 20_001,
    a2_lower_bound: float | None = None,
) -> dict[str, Any]:
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    if source_lam is None:
        source_lam = np.zeros_like(xi)
    source_lam = np.asarray(source_lam, dtype=np.float64).reshape(-1)
    n = 20_001
    n = int(x_grid_points)
    # The class is even, so int_{-2}^2 max(0,G) = 2*int_0^2 max(0,G).
    x = np.linspace(0.0, 2.0, n, dtype=np.float64)
    weights = np.full(n, 2.0 / (n - 1), dtype=np.float64)
    weights[0] *= 0.5
    weights[-1] *= 0.5
    k = int(xi.size)

    started_build = time.time()
    cos_grid = np.cos(x[:, None] * xi[None, :])
    c = np.concatenate(([-1.0, -2.0 / 3.0], sinc2(xi), np.zeros(n, dtype=np.float64)))

    # G(x_i) - s_i <= 0, s_i >= 0, and 2*trapezoid sum_i w_i s_i <= 1.
    prefix = sparse.csr_matrix(np.column_stack((np.ones(n), x * x, -cos_grid)))
    a_grid = sparse.hstack((prefix, -sparse.eye(n, format="csr")), format="csr")
    a_mass = sparse.hstack(
        (sparse.csr_matrix((1, 2 + k)), sparse.csr_matrix(weights[None, :])),
        format="csr",
    )
    a_ub = sparse.vstack((a_grid, a_mass), format="csr")
    b_ub = np.concatenate((np.zeros(n, dtype=np.float64), [0.5]))
    a2_bounds = (None if a2_lower_bound is None else float(a2_lower_bound), None)
    bounds = [(None, None), a2_bounds] + [(0.0, None)] * k + [(0.0, None)] * n
    build_elapsed = time.time() - started_build

    started_solve = time.time()
    result = linprog(
        c,
        A_ub=a_ub,
        b_ub=b_ub,
        bounds=bounds,
        method="highs-ipm",
        options={
            "primal_feasibility_tolerance": 1.0e-8,
            "dual_feasibility_tolerance": 1.0e-8,
        },
    )
    solve_elapsed = time.time() - started_solve
    if not result.success:
        raise RuntimeError(f"relaxed positive-part LP failed: {result.message}")

    y = np.asarray(result.x, dtype=np.float64)
    lam = np.maximum(y[2 : 2 + k], 0.0)
    a0 = float(y[0])
    a2 = float(y[1])
    grid_g = a0 + a2 * x * x - cos_grid @ lam
    grid_pos = np.maximum(grid_g, 0.0)
    grid_neg = np.maximum(-grid_g, 0.0)

    return {
        "a0": a0,
        "a2": a2,
        "a2_lower_bound": None if a2_lower_bound is None else float(a2_lower_bound),
        "xi": xi,
        "lambda": lam,
        "source_lambda": source_lam,
        "provisional_L": float(-result.fun),
        "x_grid_points": n,
        "grid_positive_integral_trapezoid": float(np.trapezoid(grid_pos, x)),
        "grid_negative_integral_trapezoid": float(np.trapezoid(grid_neg, x)),
        "grid_integral_G_trapezoid_half": float(np.trapezoid(grid_g, x)),
        "grid_integral_G_trapezoid": float(2.0 * np.trapezoid(grid_g, x)),
        "grid_min_G": float(np.min(grid_g)),
        "grid_max_G": float(np.max(grid_g)),
        "grid_min_x": float(x[int(np.argmin(grid_g))]),
        "grid_max_x": float(x[int(np.argmax(grid_g))]),
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lambda_positive_count_gt_1e_8": int(np.sum(lam > 1.0e-8)),
        "selected_frequency_count": int(k),
        "full_active_frequency_count": None if full_active_frequency_count is None else int(full_active_frequency_count),
        "full_comb_frequency_count": None if full_comb_frequency_count is None else int(full_comb_frequency_count),
        "solver_status": int(result.status),
        "solver_message": str(result.message),
        "build_elapsed_seconds": float(build_elapsed),
        "solve_elapsed_seconds": float(solve_elapsed),
    }


def second_derivative_bound(a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(2.0 * abs(float(a2)) + float(np.sum(np.asarray(lam) * np.asarray(xi) ** 2)))


def positive_line_integral_upper(g0: float, g1: float, h: float, envelope: float) -> float:
    a = min(g0 + envelope, g1 + envelope)
    b = max(g0 + envelope, g1 + envelope)
    if b <= 0.0:
        return 0.0
    if a >= 0.0:
        return 0.5 * h * (a + b)
    crossing = h * (-a) / (b - a)
    return 0.5 * b * (h - crossing)


def positive_part_upper_bound(values: np.ndarray, *, curvature: float, spacing: float) -> float:
    envelope = float(curvature) * float(spacing) * float(spacing) / 8.0
    total = 0.0
    vals = np.asarray(values, dtype=np.float64)
    h = float(spacing)
    for i in range(vals.size - 1):
        total += positive_line_integral_upper(float(vals[i]), float(vals[i + 1]), h, envelope)
    return float(total)


def evaluate_g_values_chunked(
    x: np.ndarray,
    *,
    a0: float,
    a2: float,
    xi: np.ndarray,
    lam: np.ndarray,
    chunk: int = 4096,
) -> np.ndarray:
    x = np.asarray(x, dtype=np.float64)
    xi = np.asarray(xi, dtype=np.float64)
    lam = np.asarray(lam, dtype=np.float64)
    out = np.empty_like(x)
    for start in range(0, x.size, int(chunk)):
        stop = min(x.size, start + int(chunk))
        xs = x[start:stop]
        trig = np.cos(xs[:, None] * xi[None, :]) @ lam if xi.size else 0.0
        out[start:stop] = float(a0) + float(a2) * xs * xs - trig
    return out


def sign_bands(x: np.ndarray, values: np.ndarray, *, negative: bool) -> list[dict[str, float]]:
    mask = values < 0.0 if negative else values > 0.0
    idx = np.flatnonzero(mask)
    if idx.size == 0:
        return []
    splits = np.where(np.diff(idx) > 1)[0] + 1
    groups = np.split(idx, splits)
    rows = []
    for group in groups:
        rows.append(
            {
                "count": int(group.size),
                "min_x": float(x[int(group[0])]),
                "max_x": float(x[int(group[-1])]),
                "center_x": float(0.5 * (x[int(group[0])] + x[int(group[-1])])),
            }
        )
    return rows


def certify_relaxed_solution(lp: dict[str, Any], *, verify_points: int = 200_001) -> dict[str, Any]:
    xi = np.asarray(lp["xi"], dtype=np.float64)
    lam = np.asarray(lp["lambda"], dtype=np.float64)
    a0 = float(lp["a0"])
    a2 = float(lp["a2"])
    x = np.linspace(-2.0, 2.0, int(verify_points), dtype=np.float64)
    g_raw = a0 + a2 * x * x - np.cos(x[:, None] * xi[None, :]) @ lam
    spacing = float(4.0 / (verify_points - 1))
    curvature = second_derivative_bound(a2, xi, lam)
    raw_upper = positive_part_upper_bound(g_raw, curvature=curvature, spacing=spacing)

    # Shift only a0 downward until the curvature-certified positive-part mass
    # is strictly below one.  This preserves lambda >= 0 and costs exactly the
    # same amount in L.
    target_upper = 1.0 - 1.0e-9
    lo = 0.0
    hi = max(1.0e-8, raw_upper - target_upper)
    while positive_part_upper_bound(g_raw - hi, curvature=curvature, spacing=spacing) > target_upper:
        hi *= 2.0
        if hi > 1.0e-2:
            raise RuntimeError("unexpectedly large constant shift needed for positive-part certificate")
    for _ in range(44):
        mid = 0.5 * (lo + hi)
        if positive_part_upper_bound(g_raw - mid, curvature=curvature, spacing=spacing) <= target_upper:
            hi = mid
        else:
            lo = mid
    shift = float(hi)
    g = g_raw - shift
    certified_upper = positive_part_upper_bound(g, curvature=curvature, spacing=spacing)
    exact_int_g = float(4.0 * (a0 - shift) + (16.0 / 3.0) * a2 - float(int_cos_over_domain(xi) @ lam))
    final_l = bound_constant(a0 - shift, a2, xi, lam)

    top = np.flatnonzero(lam > 1.0e-10)
    top = top[np.argsort(lam[top])[-20:]][::-1]
    return {
        "verify_points": int(verify_points),
        "spacing": spacing,
        "second_derivative_sup_bound": curvature,
        "curvature_interval_envelope": float(curvature * spacing * spacing / 8.0),
        "raw_positive_part_upper_bound": raw_upper,
        "constant_downshift": shift,
        "certified_positive_part_upper_bound": certified_upper,
        "positive_part_margin": float(1.0 - certified_upper),
        "pass_positive_part": bool(certified_upper <= 1.0),
        "final_certified_L": final_l,
        "gain_over_B0_even": float(final_l - TARGET_B0_EVEN),
        "below_best_even_construction": bool(final_l <= BEST_EVEN_CONSTRUCTION + 1.0e-12),
        "margin_to_best_even_construction": float(BEST_EVEN_CONSTRUCTION - final_l),
        "shifted_a0": float(a0 - shift),
        "a2": a2,
        "lambda_nonnegative_min": float(np.min(lam)) if lam.size else 0.0,
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lambda_positive_count_gt_1e_8": int(np.sum(lam > 1.0e-8)),
        "integral_G_exact": exact_int_g,
        "dense_positive_integral_trapezoid": float(np.trapezoid(np.maximum(g, 0.0), x)),
        "dense_negative_integral_trapezoid": float(np.trapezoid(np.maximum(-g, 0.0), x)),
        "dense_min_G": float(np.min(g)),
        "dense_max_G": float(np.max(g)),
        "dense_min_x": float(x[int(np.argmin(g))]),
        "dense_max_x": float(x[int(np.argmax(g))]),
        "negative_region_count": int(len(sign_bands(x, g, negative=True))),
        "positive_region_count": int(len(sign_bands(x, g, negative=False))),
        "negative_regions": sign_bands(x, g, negative=True)[:40],
        "top_lambda_atoms": [
            {"xi": float(xi[int(i)]), "lambda": float(lam[int(i)])}
            for i in top
        ],
        "verification_method": (
            "On each fine-grid interval, use |G''|<=K to bound G by the "
            "endpoint chord plus K*h^2/8, then integrate the positive part "
            "of that affine upper envelope exactly."
        ),
    }


def certify_relaxed_solution_chunked(
    lp: dict[str, Any],
    *,
    verify_points: int = 200_001,
    chunk: int = 4096,
) -> dict[str, Any]:
    xi = np.asarray(lp["xi"], dtype=np.float64)
    lam = np.asarray(lp["lambda"], dtype=np.float64)
    a0 = float(lp["a0"])
    a2 = float(lp["a2"])
    x = np.linspace(0.0, 2.0, int(verify_points), dtype=np.float64)
    g_raw = evaluate_g_values_chunked(x, a0=a0, a2=a2, xi=xi, lam=lam, chunk=chunk)
    spacing = float(2.0 / (verify_points - 1))
    curvature = second_derivative_bound(a2, xi, lam)
    raw_upper = 2.0 * positive_part_upper_bound(g_raw, curvature=curvature, spacing=spacing)

    target_upper = 1.0 - 1.0e-9
    lo = 0.0
    hi = max(1.0e-8, raw_upper - target_upper)
    while 2.0 * positive_part_upper_bound(g_raw - hi, curvature=curvature, spacing=spacing) > target_upper:
        hi *= 2.0
        if hi > 1.0e-2:
            raise RuntimeError("unexpectedly large constant shift needed for positive-part certificate")
    for _ in range(44):
        mid = 0.5 * (lo + hi)
        if 2.0 * positive_part_upper_bound(g_raw - mid, curvature=curvature, spacing=spacing) <= target_upper:
            hi = mid
        else:
            lo = mid
    shift = float(hi)
    g = g_raw - shift
    certified_upper = 2.0 * positive_part_upper_bound(g, curvature=curvature, spacing=spacing)
    exact_int_g = float(4.0 * (a0 - shift) + (16.0 / 3.0) * a2 - float(int_cos_over_domain(xi) @ lam))
    final_l = bound_constant(a0 - shift, a2, xi, lam)

    top = np.flatnonzero(lam > 1.0e-10)
    top = top[np.argsort(lam[top])[-20:]][::-1]
    return {
        "verify_points": int(verify_points),
        "verification_chunk": int(chunk),
        "spacing": spacing,
        "second_derivative_sup_bound": curvature,
        "curvature_interval_envelope": float(curvature * spacing * spacing / 8.0),
        "raw_positive_part_upper_bound": raw_upper,
        "constant_downshift": shift,
        "certified_positive_part_upper_bound": certified_upper,
        "positive_part_margin": float(1.0 - certified_upper),
        "pass_positive_part": bool(certified_upper <= 1.0),
        "final_certified_L": final_l,
        "gain_over_B0_even": float(final_l - TARGET_B0_EVEN),
        "below_best_even_construction": bool(final_l <= BEST_EVEN_CONSTRUCTION + 1.0e-12),
        "margin_to_best_even_construction": float(BEST_EVEN_CONSTRUCTION - final_l),
        "shifted_a0": float(a0 - shift),
        "a2": a2,
        "lambda_nonnegative_min": float(np.min(lam)) if lam.size else 0.0,
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lambda_positive_count_gt_1e_8": int(np.sum(lam > 1.0e-8)),
        "integral_G_exact": exact_int_g,
        "dense_positive_integral_trapezoid": float(2.0 * np.trapezoid(np.maximum(g, 0.0), x)),
        "dense_negative_integral_trapezoid": float(2.0 * np.trapezoid(np.maximum(-g, 0.0), x)),
        "dense_min_G": float(np.min(g)),
        "dense_max_G": float(np.max(g)),
        "dense_min_x": float(x[int(np.argmin(g))]),
        "dense_max_x": float(x[int(np.argmax(g))]),
        "negative_region_count": int(len(sign_bands(x, g, negative=True))),
        "positive_region_count": int(len(sign_bands(x, g, negative=False))),
        "top_lambda_atoms": [
            {"xi": float(xi[int(i)]), "lambda": float(lam[int(i)])}
            for i in top
        ],
        "verification_method": (
            "On each fine-grid interval, use |G''|<=K to bound G by the "
            "endpoint chord plus K*h^2/8, then integrate the positive part "
            "of that affine upper envelope exactly on [0,2] and double the "
            "result by even symmetry. G values were evaluated in chunks to "
            "avoid a dense verification matrix."
        ),
    }


def print_convergence_summary(package: dict[str, Any]) -> None:
    print("CPOS_AUGMENTED_CONVERGENCE")
    print(
        f"target_B0_even={TARGET_B0_EVEN:.15f} "
        f"best_even_construction={BEST_EVEN_CONSTRUCTION:.15f}"
    )
    print("K | base_gate | base_diff | relaxed_provisional | certified_L | margin | active_lambda")
    for row in package.get("rows", []):
        base = row.get("base_gate", {})
        lp = row.get("relaxed_grid_lp", {})
        cert = row.get("continuum_verification", {})
        print(
            f"{row['selected_K']:4d} | {base.get('value', float('nan')):.15f} | "
            f"{base.get('difference_from_target', float('nan')):+.3e} | "
            f"{lp.get('provisional_L', float('nan')):.15f} | "
            f"{cert.get('final_certified_L', float('nan')):.15f} | "
            f"{cert.get('positive_part_margin', float('nan')):.3e} | "
            f"{cert.get('lambda_positive_count_gt_1e_10', 0)}"
        )
        if base.get("status") != "pass":
            print(f"  BASE_GATE_WARNING K={row['selected_K']} status={base.get('status')} result marked suspect")
    skipped = package.get("skipped", [])
    for row in skipped:
        print(f"SKIPPED K={row['requested_K']} reason={row['reason']}")
    comp = package.get("apples_to_apples_K200")
    if comp:
        print(
            "APPLES_TO_APPLES_K200 "
            f"classical={comp['classical_value']:.15f} "
            f"augmented={comp['augmented_certified_L']:.15f} "
            f"lift={comp['certified_lift']:.15e}"
        )
    best = package.get("best_certified", {})
    if best:
        print(
            "BEST_CERTIFIED "
            f"K={best['K']} L={best['L']:.15f} "
            f"gain_vs_B0_even={best['gain_over_B0_even']:.15e}"
        )
    print(f"VERDICT {package.get('verdict', 'inconclusive')}")


def relaxed_grid_points_for_k(k_requested: int) -> int:
    if k_requested <= 80:
        return 20_001
    if k_requested <= 200:
        return 12_001
    if k_requested <= 400:
        return 12_001
    if k_requested <= 800:
        return 8_001
    return 6_001


def run_convergence_sweep(
    *,
    out_path: Path = CONVERGENCE_JSON,
    k_values: tuple[int, ...] = (80, 200, 400, 800, 1600, 2560),
    x_grid_points: int = 20_001,
    verify_points: int = 200_001,
    max_seconds: float = 1650.0,
) -> dict[str, Any]:
    started = time.time()
    best = load_b0even_best()
    rows: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    package: dict[str, Any] = {
        "schema": "public C>=0 positive-part augmented even dual convergence v1",
        "metadata": {
            "source package": "public",
            "created_by": "source/cpos_augmented_dual.py",
            "claim_scope": "Continuum-verified lower bound for the even/m=0 class only.",
            "selection_rule": (
                "K<200 uses the K strongest positive atoms from certificate_B0even.json; "
                "K>=200 uses all 200 positive atoms plus inactive certificate-comb frequencies "
                "in increasing xi order."
            ),
            "optimization_grid_policy": (
                "Base gate uses 20001 x-grid points at every K. Relaxed LP uses "
                "20001 for K<=80, 12001 for K<=400, 8001 for K<=800, and 6001 above."
            ),
            "reference_evaluations": [298, 363, 366, 415],
        },
        "target_B0_even": TARGET_B0_EVEN,
        "best_even_construction": BEST_EVEN_CONSTRUCTION,
        "requested_K_values": list(map(int, k_values)),
        "x_grid_points": int(x_grid_points),
        "verify_points": int(verify_points),
        "rows": rows,
        "skipped": skipped,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    for k in k_values:
        elapsed = time.time() - started
        if elapsed > max_seconds - 600.0 and k > 800:
            skipped.append({"requested_K": int(k), "reason": "time_guard_before_start", "elapsed_seconds": float(elapsed)})
            continue
        selected = select_convergence_frequencies(best, int(k))
        row: dict[str, Any] = {
            "requested_K": int(k),
            "selected_K": int(selected["selected_K"]),
            "selection": {key: val for key, val in selected.items() if key not in ("xi", "source_lambda")},
            "started_elapsed_seconds": float(elapsed),
        }
        xi = np.asarray(selected["xi"], dtype=np.float64)
        source_lam = np.asarray(selected["source_lambda"], dtype=np.float64)
        try:
            base = solve_base_gate_for_xi(xi, x_grid_points=x_grid_points)
            row["base_gate"] = base
            lp = solve_relaxed_grid_lp_for_xi(
                xi,
                source_lam=source_lam,
                full_active_frequency_count=int(selected["active_atoms_in_certificate"]),
                full_comb_frequency_count=int(selected["full_comb_frequency_count"]),
                x_grid_points=relaxed_grid_points_for_k(int(k)),
            )
            row["relaxed_grid_lp"] = lp
            cert = certify_relaxed_solution_chunked(lp, verify_points=verify_points)
            row["continuum_verification"] = cert
            row["status"] = "success" if cert["pass_positive_part"] else "verification_failed"
        except Exception as exc:
            row["status"] = "failed"
            row["error"] = f"{type(exc).__name__}: {exc}"
        row["elapsed_seconds_after_row"] = float(time.time() - started)
        rows.append(row)
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        if row.get("status") == "failed":
            break
        if time.time() - started > max_seconds and k >= 800:
            for remaining in k_values[k_values.index(k) + 1 :]:
                skipped.append({"requested_K": int(remaining), "reason": "time_guard_after_row", "elapsed_seconds": float(time.time() - started)})
            break

    valid_rows = [
        row for row in rows
        if row.get("status") == "success"
        and row.get("continuum_verification", {}).get("pass_positive_part")
    ]
    if valid_rows:
        best_row = max(valid_rows, key=lambda row: float(row["continuum_verification"]["final_certified_L"]))
        package["best_certified"] = {
            "K": int(best_row["selected_K"]),
            "L": float(best_row["continuum_verification"]["final_certified_L"]),
            "gain_over_B0_even": float(best_row["continuum_verification"]["gain_over_B0_even"]),
            "positive_part_margin": float(best_row["continuum_verification"]["positive_part_margin"]),
        }
    k200 = next((row for row in rows if int(row.get("selected_K", -1)) == 200 and row.get("status") == "success"), None)
    if k200 is not None:
        package["apples_to_apples_K200"] = {
            "classical_value": float(k200["base_gate"]["value"]),
            "augmented_provisional_L": float(k200["relaxed_grid_lp"]["provisional_L"]),
            "augmented_certified_L": float(k200["continuum_verification"]["final_certified_L"]),
            "certified_lift": float(k200["continuum_verification"]["final_certified_L"] - k200["base_gate"]["value"]),
            "base_diff_from_B0_even": float(k200["base_gate"]["difference_from_target"]),
        }
    completed_up_to = max((int(row["selected_K"]) for row in rows if row.get("status") == "success"), default=0)
    best_l = package.get("best_certified", {}).get("L", float("nan"))
    if math.isfinite(float(best_l)) and float(best_l) < 0.371:
        trend = "saturates_near_0.3704"
    elif math.isfinite(float(best_l)) and float(best_l) >= 0.375:
        trend = "climbs_substantially_toward_0.375_plus"
    else:
        trend = "inconclusive_intermediate"
    package["verdict"] = (
        f"{trend}; completed_verified_up_to_K={completed_up_to}; "
        "reported values are continuum certificates only where positive-part verification passed"
    )
    package["elapsed_seconds"] = float(time.time() - started)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_convergence_summary(package)
    return package


def run_experiment(out_path: Path = OUT_JSON) -> dict[str, Any]:
    started = time.time()
    best = load_b0even_best()
    base = solve_base_gate(best)
    package: dict[str, Any] = {
        "schema": "public C>=0 positive-part augmented even dual v1",
        "metadata": {
            "source package": "public",
            "created_by": "source/cpos_augmented_dual.py",
            "claim_scope": "Continuum-verified lower bound for the even/m=0 class only.",
            "reference_evaluations": [298, 363, 366, 409, 412],
        },
        "base_gate": base,
    }
    if base["status"] != "pass":
        package["status"] = "base_gate_failed"
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print_summary(package)
        return package

    lp = solve_relaxed_grid_lp(best, active_limit=80)
    cert = certify_relaxed_solution(lp, verify_points=200_001)
    package.update(
        {
            "status": "success" if cert["pass_positive_part"] and cert["below_best_even_construction"] else "failed",
            "relaxed_grid_lp": lp,
            "continuum_verification": cert,
            "comparisons": {
                "B0_even": TARGET_B0_EVEN,
                "best_even_construction": BEST_EVEN_CONSTRUCTION,
                "provisional_gain_over_B0_even": float(lp["provisional_L"] - TARGET_B0_EVEN),
                "certified_gain_over_B0_even": float(cert["gain_over_B0_even"]),
                "certified_L_is_strictly_above_B0_even": bool(cert["final_certified_L"] > TARGET_B0_EVEN + 1.0e-10),
                "certified_L_is_below_best_even_construction": bool(cert["below_best_even_construction"]),
            },
            "elapsed_seconds": float(time.time() - started),
        }
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_summary(package)
    return package


def print_summary(package: dict[str, Any]) -> None:
    base = package["base_gate"]
    print("CPOS_AUGMENTED_DUAL")
    print(
        f"BASE_GATE status={base['status']} value={base['value']:.15f} "
        f"target={base['target_B0_even']:.15f} diff={base['difference_from_target']:.3e} "
        f"K_active={base['frequency_count']} full_comb={base['full_comb_frequency_count']}"
    )
    if package.get("status") == "base_gate_failed":
        print("VERDICT base gate failed; relaxed value not trusted")
        return
    lp = package["relaxed_grid_lp"]
    cert = package["continuum_verification"]
    print(
        f"RELAXED provisional_L={lp['provisional_L']:.15f} "
        f"grid_pos_int={lp['grid_positive_integral_trapezoid']:.15f} "
        f"selected_freqs={lp['selected_frequency_count']} "
        f"lp_seconds={lp['solve_elapsed_seconds']:.2f}"
    )
    print(
        f"CONTINUUM int_Gplus_upper={cert['certified_positive_part_upper_bound']:.15f} "
        f"margin={cert['positive_part_margin']:.3e} "
        f"shift={cert['constant_downshift']:.3e} "
        f"curv={cert['second_derivative_sup_bound']:.6e}"
    )
    print(
        f"FINAL_CERTIFIED_L={cert['final_certified_L']:.15f} "
        f"gain_vs_B0_even={cert['gain_over_B0_even']:.15e} "
        f"margin_to_best_even={cert['margin_to_best_even_construction']:.15e}"
    )
    print(
        f"G_SHAPE min={cert['dense_min_G']:.12f} at {cert['dense_min_x']:.6f} "
        f"max={cert['dense_max_G']:.12f} at {cert['dense_max_x']:.6f} "
        f"int_pos_trap={cert['dense_positive_integral_trapezoid']:.15f} "
        f"int_neg_trap={cert['dense_negative_integral_trapezoid']:.15f} "
        f"neg_regions={cert['negative_region_count']} active_lambda={cert['lambda_positive_count_gt_1e_10']}"
    )
    print(
        "VERDICT "
        f"valid={cert['pass_positive_part'] and cert['below_best_even_construction']} "
        f"strictly_above_B0={package['comparisons']['certified_L_is_strictly_above_B0_even']} "
        "scope=even_m0_only"
    )


def load_best_even_candidate() -> np.ndarray:
    npz_path = ROOT / "data" / "symmetry_resolution_candidates.npz"
    if npz_path.exists():
        with np.load(npz_path) as data:
            if "reference_reference_frontier_best_even" in data:
                return np.asarray(data["reference_reference_frontier_best_even"], dtype=np.float64)
    slp_path = ROOT / "slp_push.json"
    if slp_path.exists():
        payload = json.loads(slp_path.read_text(encoding="utf-8"))
        if "even" in payload.get("candidate_weights", {}):
            return np.asarray(payload["candidate_weights"]["even"], dtype=np.float64)
    return np.full(4096, 0.5, dtype=np.float64)


def project_mean_half(weights: np.ndarray) -> np.ndarray:
    w = np.asarray(weights, dtype=np.float64).copy()
    w = np.clip(w, 0.0, 1.0)
    for _ in range(20):
        err = 0.5 - float(np.mean(w))
        if abs(err) <= 1.0e-13:
            break
        free = (w > 1.0e-12) & (w < 1.0 - 1.0e-12)
        if np.any(free):
            w[free] += err * w.size / int(np.sum(free))
        else:
            w += err
        w = np.clip(w, 0.0, 1.0)
    return w


if __name__ == "__main__":
    run_experiment()
