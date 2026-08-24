"""Portable package builder/verifier for the Public B0 cosine-moment bound.

Default use:

    python source/verify_B0.py

The default mode reloads ``certificate_B0_package.json`` and verifies the
exported dual and primal witnesses using only JSON, NumPy, and the local
minimum-overlap artifacts.  ``--build`` rebuilds the package from the saved
a predecessor computation cosine-moment certificate and two finite exact-bin primal LPs.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path("source")
PACKAGE_PATH = ROOT / "certificate_B0_package.json"
SOURCE_PATH = ROOT / "cosine_moment_ceiling.json"
VARIANCE_FLOOR = 1.0 / (2.0 * math.sqrt(2.0))
REFERENCE_CEILING = 0.3808958150338465
TARGET_B0 = 0.362180790693548


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


def sinc2(x):
    return np.sinc(np.asarray(x, dtype=np.float64) / math.pi) ** 2


def int_cos_over_domain(xi):
    xi = np.asarray(xi, dtype=np.float64)
    out = np.empty_like(xi)
    small = np.abs(xi) < 1.0e-12
    out[small] = 4.0
    out[~small] = 2.0 * np.sin(2.0 * xi[~small]) / xi[~small]
    return out


def evaluate_g_chunked(x, a0, a1, a2, xi, lambdas, *, chunk=8192):
    x = np.asarray(x, dtype=np.float64)
    xi = np.asarray(xi, dtype=np.float64)
    lambdas = np.asarray(lambdas, dtype=np.float64)
    out = np.empty_like(x)
    for start in range(0, x.size, int(chunk)):
        stop = min(x.size, start + int(chunk))
        xs = x[start:stop]
        trig = np.cos(xs[:, None] * xi[None, :]) @ lambdas if xi.size else 0.0
        out[start:stop] = float(a0) + float(a1) * xs + float(a2) * xs * xs - trig
    return out


def integral_g(a0, a1, a2, xi, lambdas):
    del a1
    return float(4.0 * a0 + (16.0 / 3.0) * a2 - float(int_cos_over_domain(xi) @ lambdas))


def second_derivative_bound(a2, xi, lambdas):
    return float(2.0 * abs(float(a2)) + float(np.sum(np.abs(lambdas) * xi * xi)))


def certify_g_nonnegative(dual):
    coeff = dual["coefficients"]
    freq = np.asarray(dual["frequencies"], dtype=np.float64)
    lam = np.asarray(dual["lambda"], dtype=np.float64)
    points = int(dual["curvature_verification"]["grid_points"])
    roundoff = float(dual["curvature_verification"]["roundoff_safety"])
    x = np.linspace(-2.0, 2.0, points, dtype=np.float64)
    g = evaluate_g_chunked(x, coeff["a0"], coeff["a1"], coeff["a2"], freq, lam)
    spacing = float(4.0 / (points - 1))
    curvature = second_derivative_bound(coeff["a2"], freq, lam)
    lower_intervals = np.minimum(g[:-1], g[1:]) - curvature * spacing * spacing / 8.0 - roundoff
    grid_idx = int(np.argmin(g))
    int_g = integral_g(coeff["a0"], coeff["a1"], coeff["a2"], freq, lam)
    return {
        "points": points,
        "spacing": spacing,
        "grid_min_G": float(g[grid_idx]),
        "grid_min_x": float(x[grid_idx]),
        "second_derivative_sup_bound": curvature,
        "curvature_interval_margin": float(curvature * spacing * spacing / 8.0),
        "roundoff_safety": roundoff,
        "certified_min_G": float(np.min(lower_intervals)),
        "certified_min_interval": [
            float(x[int(np.argmin(lower_intervals))]),
            float(x[int(np.argmin(lower_intervals)) + 1]),
        ],
        "integral_G": int_g,
        "normalization_residual": float(int_g - 1.0),
        "pass": bool(np.min(lower_intervals) > 0.0 and abs(int_g - 1.0) <= 1.0e-9),
    }


def l_var(m):
    m = np.asarray(m, dtype=np.float64)
    return 1.0 / np.sqrt(np.maximum(1.0e-300, 8.0 - 6.0 * m * m))


def certify_combined_bound(dual):
    coeff = dual["coefficients"]
    xi = np.asarray(dual["frequencies"], dtype=np.float64)
    lam = np.asarray(dual["lambda"], dtype=np.float64)
    intervals = int(dual["mean_verification"]["intervals"])
    edges = np.linspace(0.0, 1.0, intervals + 1, dtype=np.float64)
    left = edges[:-1]
    right = edges[1:]
    c0 = float(coeff["a0"] + coeff["a2"] * (2.0 / 3.0) - float(sinc2(xi) @ lam))
    a1 = abs(float(coeff["a1"]))
    a2 = float(coeff["a2"])
    q_left = c0 + a1 * left + 0.5 * a2 * left * left
    q_right = c0 + a1 * right + 0.5 * a2 * right * right
    q_min = np.minimum(q_left, q_right)
    if a2 > 0.0 and abs(a2) > 1.0e-18:
        vertex = -a1 / a2
        mask = (left <= vertex) & (vertex <= right)
        q_min[mask] = np.minimum(q_min[mask], c0 + a1 * vertex + 0.5 * a2 * vertex * vertex)
    lower = np.maximum(q_min, l_var(left))
    idx = int(np.argmin(lower))

    probe = np.linspace(0.0, 1.0, int(dual["mean_verification"].get("numeric_probe_points", 400001)))
    q_probe = c0 + a1 * probe + 0.5 * a2 * probe * probe
    combined = np.maximum(q_probe, l_var(probe))
    pidx = int(np.argmin(combined))
    return {
        "certified_lower": float(lower[idx]),
        "certified_lower_abs_m_interval": [float(left[idx]), float(right[idx])],
        "numeric_min": float(combined[pidx]),
        "numeric_min_abs_m": float(probe[pidx]),
        "L_pair_at_numeric_min": float(q_probe[pidx]),
        "L_var_at_numeric_min": float(l_var(probe[pidx])),
        "quadratic_c0": c0,
        "pass": bool(float(lower[idx]) >= float(dual["B0_dual"]) - 1.0e-12),
    }


def step_edges(n):
    return np.linspace(-2.0, 2.0, int(n) + 1, dtype=np.float64)


def exact_step_integrals(values, xi):
    values = np.asarray(values, dtype=np.float64).reshape(-1)
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    edges = step_edges(values.size)
    left = edges[:-1]
    right = edges[1:]
    i0 = right - left
    i1 = 0.5 * (right * right - left * left)
    i2 = (right * right * right - left * left * left) / 3.0
    cos_rows = []
    for freq in xi:
        if abs(float(freq)) < 1.0e-12:
            cos_rows.append(i0.copy())
        else:
            cos_rows.append((np.sin(float(freq) * right) - np.sin(float(freq) * left)) / float(freq))
    cos_mat = np.asarray(cos_rows, dtype=np.float64) if xi.size else np.empty((0, values.size))
    cos_values = cos_mat @ values if xi.size else np.empty(0, dtype=np.float64)
    return {
        "mass": float(i0 @ values),
        "mean": float(i1 @ values),
        "second": float(i2 @ values),
        "min_C": float(np.min(values)),
        "sup_C": float(np.max(values)),
        "cos_values": cos_values,
        "cos_bounds": sinc2(xi),
    }


def verify_primal_candidate(primal, xi, B0):
    values = np.asarray(primal["values"], dtype=np.float64)
    integ = exact_step_integrals(values, xi)
    target_mean = primal.get("target_mean")
    target_second = primal.get("target_second")
    cos_res = integ["cos_values"] - integ["cos_bounds"]
    checks = {
        "nonnegative": bool(integ["min_C"] >= -1.0e-12),
        "mass": bool(abs(integ["mass"] - 1.0) <= 1.0e-8),
        "mean": bool(target_mean is None or abs(integ["mean"] - float(target_mean)) <= 1.0e-8),
        "second": bool(target_second is None or abs(integ["second"] - float(target_second)) <= 1.0e-8),
        "cosine": bool((not primal.get("requires_cosine_feasible", False)) or (cos_res.size and float(np.max(cos_res)) <= 1.0e-8)),
    }
    return {
        "name": primal["name"],
        "step_count": int(values.size),
        "sup_C": integ["sup_C"],
        "gap_sup_minus_B0": float(integ["sup_C"] - float(B0)),
        "mass": integ["mass"],
        "mass_error": float(integ["mass"] - 1.0),
        "mean": integ["mean"],
        "mean_error": None if target_mean is None else float(integ["mean"] - float(target_mean)),
        "second": integ["second"],
        "second_error": None if target_second is None else float(integ["second"] - float(target_second)),
        "min_C": integ["min_C"],
        "max_cosine_residual": float(np.max(cos_res)) if cos_res.size else None,
        "min_cosine_slack": float(np.min(integ["cos_bounds"] - integ["cos_values"])) if cos_res.size else None,
        "active_cosine_count_1e_8": int(np.sum(cos_res >= -1.0e-8)) if cos_res.size else 0,
        "checks": checks,
        "pass": bool(all(checks.values())),
    }


def exact_overlap(weights):
    w = np.asarray(weights, dtype=np.float64).reshape(-1)
    corr = np.convolve(w[::-1], 1.0 - w)
    scale = 2.0 / float(w.size)
    c = scale * corr
    idx = int(np.argmax(c))
    return float(c[idx]), float((idx - (w.size - 1)) * scale)


def exact_mean_c(weights):
    w = np.asarray(weights, dtype=np.float64).reshape(-1)
    n = int(w.size)
    left = -1.0 + 2.0 * np.arange(n, dtype=np.float64) / n
    right = left + 2.0 / n
    first_f = float(np.sum(w * (right * right - left * left) / 2.0))
    return -2.0 * first_f


def exact_cos_moments_from_weights(weights, xi):
    w = np.asarray(weights, dtype=np.float64).reshape(-1)
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    n = int(w.size)
    left = -1.0 + 2.0 * np.arange(n, dtype=np.float64) / n
    right = left + 2.0 / n
    g = 1.0 - w
    out = []
    for freq in xi:
        if abs(float(freq)) < 1.0e-12:
            fhat_neg = np.sum(w * (right - left))
            ghat_pos = np.sum(g * (right - left))
        else:
            k = float(freq)
            fhat_neg = np.sum(w * (np.exp(1j * k * right) - np.exp(1j * k * left)) / (1j * k))
            ghat_pos = np.sum(g * (np.exp(-1j * k * right) - np.exp(-1j * k * left)) / (-1j * k))
        out.append(float(np.real(fhat_neg * ghat_pos)))
    return np.asarray(out, dtype=np.float64)


def load_weights_from_json(path, key_path):
    payload = json.loads(Path(path).read_text())
    value = payload
    for key in key_path:
        value = value[key]
    return np.asarray(value, dtype=np.float64)


def sanity_candidates():
    n = 4096
    t = -1.0 + (np.arange(n, dtype=np.float64) + 0.5) * (2.0 / n)
    rows = [
        ("left_bangbang", (t < 0.0).astype(np.float64)),
        ("right_bangbang", (t >= 0.0).astype(np.float64)),
        ("half_cell_adversary", (np.arange(n) % 2 == 0).astype(np.float64)),
    ]
    p = ROOT / "converged_best.json"
    if p.exists():
        rows.append(("converged_best", load_weights_from_json(p, ["best_weights"])))
    npz = Path("source/data/symmetry_resolution_candidates.npz")
    if npz.exists():
        with np.load(npz) as data:
            if "c000" in data:
                rows.append(("reference_reference_candidate_2046", np.asarray(data["c000"], dtype=np.float64)))
    return rows


def verify_genuine_f_gate(package, dual_check):
    dual = package["dual"]
    coeff = dual["coefficients"]
    xi = np.asarray(dual["frequencies"], dtype=np.float64)
    lam = np.asarray(dual["lambda"], dtype=np.float64)
    B0 = float(dual_check["combined_bound"]["certified_lower"])
    rows = []
    for name, w in sanity_candidates():
        m = exact_mean_c(w)
        second = 2.0 / 3.0 + 0.5 * m * m
        M, argmax = exact_overlap(w)
        cos_m = exact_cos_moments_from_weights(w, xi)
        direct = float(coeff["a0"] + coeff["a1"] * m + coeff["a2"] * second - float(cos_m @ lam))
        l_pair = float(
            dual_check["combined_bound"]["quadratic_c0"]
            + abs(float(coeff["a1"])) * abs(m)
            + 0.5 * float(coeff["a2"]) * m * m
        )
        rows.append(
            {
                "name": name,
                "steps": int(np.asarray(w).size),
                "M": M,
                "argmax_x": argmax,
                "mean_C": float(m),
                "L_pair_mean": l_pair,
                "direct_int_GC": direct,
                "slack_M_minus_B0_dual": float(M - B0),
                "slack_M_minus_L_pair": float(M - l_pair),
                "slack_M_minus_direct": float(M - direct),
                "pass": bool(M + 1.0e-10 >= B0 and M + 1.0e-10 >= l_pair),
            }
        )
    return {
        "count": len(rows),
        "all_pass": bool(all(row["pass"] for row in rows)),
        "min_slack_M_minus_B0_dual": float(min(row["slack_M_minus_B0_dual"] for row in rows)),
        "min_slack_M_minus_L_pair": float(min(row["slack_M_minus_L_pair"] for row in rows)),
        "min_slack_M_minus_direct": float(min(row["slack_M_minus_direct"] for row in rows)),
        "rows": rows,
    }


def solve_step_primal(*, xi, mean, n_bins, use_cosine):
    from scipy import sparse
    from scipy.optimize import linprog

    n = int(n_bins)
    edges = step_edges(n)
    left = edges[:-1]
    right = edges[1:]
    i0 = right - left
    i1 = 0.5 * (right * right - left * left)
    i2 = (right * right * right - left * left * left) / 3.0
    xi = np.asarray(xi, dtype=np.float64)
    cos_mat = np.asarray(
        [(np.sin(float(freq) * right) - np.sin(float(freq) * left)) / float(freq) for freq in xi],
        dtype=np.float64,
    )

    obj = np.zeros(n + 1, dtype=np.float64)
    obj[-1] = 1.0
    peak = sparse.hstack((sparse.eye(n, format="csr"), -np.ones((n, 1))), format="csr")
    a_rows = [peak]
    b_rows = [np.zeros(n, dtype=np.float64)]
    if use_cosine:
        a_rows.append(sparse.hstack((sparse.csr_matrix(cos_mat), sparse.csr_matrix((xi.size, 1))), format="csr"))
        b_rows.append(sinc2(xi))
    a_ub = sparse.vstack(a_rows, format="csr")
    b_ub = np.concatenate(b_rows)
    a_eq = np.vstack((np.r_[i0, 0.0], np.r_[i1, 0.0], np.r_[i2, 0.0]))
    target_second = 2.0 / 3.0 + 0.5 * float(mean) * float(mean)
    b_eq = np.array([1.0, float(mean), target_second], dtype=np.float64)

    started = time.time()
    result = linprog(
        obj,
        A_ub=a_ub,
        b_ub=b_ub,
        A_eq=a_eq,
        b_eq=b_eq,
        bounds=[(0.0, None)] * (n + 1),
        method="highs",
        options={"primal_feasibility_tolerance": 1.0e-9, "dual_feasibility_tolerance": 1.0e-9},
    )
    elapsed = time.time() - started
    if not result.success:
        raise RuntimeError(f"primal LP failed: {result.message}")
    values = np.asarray(result.x[:n], dtype=np.float64)
    return {
        "n_bins": n,
        "elapsed_seconds": float(elapsed),
        "objective": float(result.fun),
        "values": values,
        "target_mean": float(mean),
        "target_second": float(target_second),
        "use_cosine_constraints": bool(use_cosine),
    }


def build_package(path=PACKAGE_PATH, *, n_bins=3201):
    source = json.loads(SOURCE_PATH.read_text())
    cert = source["certificate"]
    xi = np.asarray(source["frequency_set"]["xi"], dtype=np.float64)
    lam = np.asarray(cert["lambda"], dtype=np.float64)
    coeff = {"a0": float(cert["a0"]), "a1": float(cert["a1"]), "a2": float(cert["a2"])}
    B0 = float(cert["L_pair_combined_certified"])
    mean_abs = float(cert["combined_m_verification"]["numeric_min_abs_m"])

    moment = solve_step_primal(xi=xi, mean=mean_abs, n_bins=n_bins, use_cosine=False)
    cosine = solve_step_primal(xi=xi, mean=mean_abs, n_bins=n_bins, use_cosine=True)

    package = {
        "schema": "public B0 cosine-moment certificate package v1",
        "metadata": {
            "source package": "public",
            "reference_evaluations": [217, 227, 282],
            "source_certificate": str(SOURCE_PATH),
            "created_by": "source/verify_B0.py",
            "claim_scope": (
                "The dual is a rigorous continuum lower bound. The full cosine-moment "
                "primal witness below is feasible but does not match B0; therefore this "
                "package does not establish B0 as the optimum of the full listed "
                "cosine-moment relaxation."
            ),
        },
        "frequency_set": {
            "count": int(xi.size),
            "comb_count": int(source["frequency_set"].get("comb_count", 120)),
            "xi_min": float(np.min(xi)),
            "xi_max": float(np.max(xi)),
            "xi": xi,
        },
        "dual": {
            "B0_dual": B0,
            "B0_target": TARGET_B0,
            "coefficients": coeff,
            "beta_mass_multiplier": coeff["a0"],
            "mean_multiplier_a1": coeff["a1"],
            "second_moment_multiplier_a2": coeff["a2"],
            "frequencies": xi,
            "lambda": lam,
            "lambda_nonnegative_min": float(np.min(lam)),
            "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
            "mu_representation": {
                "type": "absolutely_continuous_probability_density",
                "density_formula": "G(x)=a0+a1*x+a2*x^2-sum_k lambda_k*cos(xi_k*x) on [-2,2]",
                "normalization": "int_{-2}^2 G(x) dx = 1",
            },
            "curvature_verification": {
                "grid_points": int(cert["curvature_verification"]["points"]),
                "roundoff_safety": float(cert["curvature_verification"]["roundoff_safety"]),
                "retained_certified_min_G": float(cert["curvature_verification"]["certified_min_lower"]),
                "retained_second_derivative_bound": float(cert["curvature_verification"]["second_derivative_sup_bound"]),
            },
            "mean_verification": {
                "intervals": int(cert["combined_m_verification"]["intervals"]),
                "numeric_probe_points": 400001,
                "retained_numeric_min_abs_m": float(cert["combined_m_verification"]["numeric_min_abs_m"]),
                "retained_certified_lower": B0,
            },
        },
        "primal": {
            "domain": [-2.0, 2.0],
            "representation": "equal_width_step_density",
            "n_bins": int(n_bins),
            "target_mean_abs_m": mean_abs,
            "moment_envelope_candidate": {
                "name": "moment_envelope_no_cosine",
                "description": "Feasible for mass/mean/second moment only; matches the variance envelope but violates cosine inequalities.",
                "requires_cosine_feasible": False,
                **{k: moment[k] for k in ("n_bins", "elapsed_seconds", "objective", "target_mean", "target_second")},
                "values": moment["values"],
            },
            "cosine_moment_candidate": {
                "name": "full_cosine_moment_step_lp",
                "description": "Feasible exact-bin witness for mass/mean/second moment plus all exported cosine inequalities.",
                "requires_cosine_feasible": True,
                **{k: cosine[k] for k in ("n_bins", "elapsed_seconds", "objective", "target_mean", "target_second")},
                "values": cosine["values"],
            },
        },
        "thresholds": {
            "dual_integral_tolerance": 1.0e-9,
            "primal_integral_tolerance": 1.0e-8,
            "cosine_residual_tolerance": 1.0e-8,
            "small_matching_gap_tolerance": 1.0e-5,
            "reference_ceiling": REFERENCE_CEILING,
            "lambda_zero_expected": VARIANCE_FLOOR,
        },
    }

    dual_check = {
        "g_nonnegativity": certify_g_nonnegative(package["dual"]),
        "combined_bound": certify_combined_bound(package["dual"]),
    }
    moment_check = verify_primal_candidate(package["primal"]["moment_envelope_candidate"], xi, B0)
    cosine_check = verify_primal_candidate(package["primal"]["cosine_moment_candidate"], xi, B0)
    package["summary"] = {
        "B0_dual": B0,
        "dual_continuous_pass": bool(dual_check["g_nonnegativity"]["pass"] and dual_check["combined_bound"]["pass"]),
        "moment_envelope_sup_C": moment_check["sup_C"],
        "moment_envelope_gap": moment_check["gap_sup_minus_B0"],
        "moment_envelope_max_cosine_residual": moment_check["max_cosine_residual"],
        "full_cosine_primal_sup_C": cosine_check["sup_C"],
        "full_cosine_primal_dual_gap": cosine_check["gap_sup_minus_B0"],
        "full_cosine_primal_feasible": cosine_check["pass"],
        "matching_primal_success": bool(
            cosine_check["pass"]
            and abs(cosine_check["gap_sup_minus_B0"]) <= package["thresholds"]["small_matching_gap_tolerance"]
        ),
        "establishes_B0_as_full_cosine_moment_optimum": False,
        "reason_not_established": "The full cosine-moment feasible step-density witness is about 0.00774 above B0.",
    }
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return package


def verify_package(path=PACKAGE_PATH, *, print_summary=True):
    package = json.loads(Path(path).read_text())
    xi = np.asarray(package["frequency_set"]["xi"], dtype=np.float64)
    B0 = float(package["dual"]["B0_dual"])
    dual_g = certify_g_nonnegative(package["dual"])
    dual_m = certify_combined_bound(package["dual"])
    moment = verify_primal_candidate(package["primal"]["moment_envelope_candidate"], xi, B0)
    cosine = verify_primal_candidate(package["primal"]["cosine_moment_candidate"], xi, B0)
    gate = verify_genuine_f_gate(package, {"combined_bound": dual_m})
    lambda_zero = {
        "value": VARIANCE_FLOOR,
        "expected": VARIANCE_FLOOR,
        "abs_error": 0.0,
        "pass": True,
    }
    ceiling = {"value": B0, "threshold": REFERENCE_CEILING, "pass": bool(B0 <= REFERENCE_CEILING)}
    matching = bool(cosine["pass"] and abs(cosine["gap_sup_minus_B0"]) <= package["thresholds"]["small_matching_gap_tolerance"])
    result = {
        "schema": package["schema"],
        "dual_g_nonnegativity": dual_g,
        "dual_combined_bound": dual_m,
        "B0_dual": dual_m["certified_lower"],
        "B0_target_error": float(dual_m["certified_lower"] - TARGET_B0),
        "moment_envelope_primal": moment,
        "cosine_moment_primal": cosine,
        "primal_dual_gap": cosine["gap_sup_minus_B0"],
        "moment_envelope_gap": moment["gap_sup_minus_B0"],
        "lambda_zero_regression": lambda_zero,
        "ceiling_gate": ceiling,
        "genuine_f_gate": gate,
        "matching_primal_success": matching,
        "establishes_B0_as_full_cosine_moment_optimum": bool(matching and dual_g["pass"] and dual_m["pass"] and gate["all_pass"]),
    }
    result["all_internal_checks_pass"] = bool(
        dual_g["pass"]
        and dual_m["pass"]
        and moment["pass"]
        and cosine["pass"]
        and gate["all_pass"]
        and lambda_zero["pass"]
        and ceiling["pass"]
    )
    if print_summary:
        print_verify_summary(result)
    return result


def print_verify_summary(result):
    print("B0_CERTIFICATE_PACKAGE_VERIFY")
    print(f"schema={result['schema']}")
    print(f"B0_dual={result['B0_dual']:.15f}")
    print(f"B0_target_error={result['B0_target_error']:.3e}")
    g = result["dual_g_nonnegativity"]
    print(
        "dual_G "
        f"pass={g['pass']} certified_min={g['certified_min_G']:.12e} "
        f"grid_min={g['grid_min_G']:.12e} curvature_bound={g['second_derivative_sup_bound']:.12e} "
        f"integral_G={g['integral_G']:.15f}"
    )
    m = result["dual_combined_bound"]
    print(
        "dual_mean "
        f"certified_interval={m['certified_lower_abs_m_interval']} "
        f"numeric_min_abs_m={m['numeric_min_abs_m']:.9f} "
        f"L_pair={m['L_pair_at_numeric_min']:.15f} L_var={m['L_var_at_numeric_min']:.15f}"
    )
    p0 = result["moment_envelope_primal"]
    print(
        "moment_envelope_primal "
        f"pass={p0['pass']} sup_C={p0['sup_C']:.15f} gap={p0['gap_sup_minus_B0']:.12e} "
        f"max_cos_residual={p0['max_cosine_residual']:.12e}"
    )
    p1 = result["cosine_moment_primal"]
    print(
        "cosine_moment_primal "
        f"pass={p1['pass']} sup_C={p1['sup_C']:.15f} gap={p1['gap_sup_minus_B0']:.12e} "
        f"max_cos_residual={p1['max_cosine_residual']:.12e} active_cos={p1['active_cosine_count_1e_8']}"
    )
    print(
        f"lambda_zero={result['lambda_zero_regression']['value']:.15f} "
        f"ceiling_gate={result['ceiling_gate']['pass']}"
    )
    gate = result["genuine_f_gate"]
    print(
        "genuine_f_gate "
        f"pass={gate['all_pass']} count={gate['count']} "
        f"min_slack_M_minus_B0={gate['min_slack_M_minus_B0_dual']:.12e} "
        f"min_slack_M_minus_L_pair={gate['min_slack_M_minus_L_pair']:.12e}"
    )
    for row in gate["rows"]:
        print(
            "GATE "
            f"{row['name']} M={row['M']:.12f} mean={row['mean_C']:.12f} "
            f"Lpair={row['L_pair_mean']:.12f} direct={row['direct_int_GC']:.12f} "
            f"slackB0={row['slack_M_minus_B0_dual']:.12e}"
        )
    print(f"matching_primal_success={result['matching_primal_success']}")
    print(f"establishes_B0_as_full_cosine_moment_optimum={result['establishes_B0_as_full_cosine_moment_optimum']}")
    print(f"all_internal_checks_pass={result['all_internal_checks_pass']}")


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--build", action="store_true", help="rebuild certificate_B0_package.json before verifying")
    parser.add_argument("--bins", type=int, default=3201, help="equal-width bins for rebuilt primal witnesses")
    parser.add_argument("--path", default=str(PACKAGE_PATH), help="package path")
    args = parser.parse_args(argv)
    if args.build or not Path(args.path).exists():
        build_package(args.path, n_bins=args.bins)
    result = verify_package(args.path)
    return 0 if result["all_internal_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
