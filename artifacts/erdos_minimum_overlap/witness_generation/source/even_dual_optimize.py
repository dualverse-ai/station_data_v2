"""Even-class cosine+variance Fejer dual optimizer.

This module solves the fixed-mean m=0 dual

    G(x) = a0 + a2*x^2 - sum_k lambda_k cos(xi_k*x),  lambda_k >= 0,

with int G = 1 and G >= 0 on [-2, 2].  For even admissible f the overlap
density C is even, has int C = 1, int x^2 C = 2/3, and satisfies
int C cos(xi*x) <= sinc(xi)^2.  Therefore

    sup C >= a0 + (2/3)*a2 - sum_k lambda_k*sinc(xi_k)^2.

The final exported certificate is checked with the curvature verifier from
verify_B0.py, using the same 200001-point continuum check as the B0 package.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import linprog

from verify_B0 import (
    certify_g_nonnegative,
    exact_overlap,
    load_weights_from_json,
    sinc2,
)


ROOT = Path("source")
OUT_JSON = ROOT / "certificate_B0even.json"
BRACKET_JSON = ROOT / "even_upper_bracket.json"
REFERENCE_CEILING = 0.3808958150338465
REFERENCE_EVEN_REUSE = 0.36923478008058175


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


def int_cos_over_domain(xi: np.ndarray) -> np.ndarray:
    xi = np.asarray(xi, dtype=np.float64)
    out = np.empty_like(xi)
    small = np.abs(xi) < 1.0e-12
    out[small] = 4.0
    out[~small] = 2.0 * np.sin(2.0 * xi[~small]) / xi[~small]
    return out


def make_dense_comb(xi_max: float, spacing: float) -> np.ndarray:
    count = int(math.floor(float(xi_max) / float(spacing)))
    xi = float(spacing) * np.arange(1, count + 1, dtype=np.float64)
    return xi[xi <= float(xi_max) + 1.0e-12]


def bound_constant(a0: float, a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(float(a0) + (2.0 / 3.0) * float(a2) - float(sinc2(xi) @ lam))


def solve_grid_lp(
    xi: np.ndarray,
    *,
    x_grid_points: int,
    grid_margin: float,
) -> dict[str, Any]:
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    x = np.linspace(-2.0, 2.0, int(x_grid_points), dtype=np.float64)
    k = int(xi.size)
    t = sinc2(xi)
    icos = int_cos_over_domain(xi)

    # Minimize -L = -a0 - (2/3)a2 + sum lambda*sinc^2.
    c = np.concatenate(([-1.0, -2.0 / 3.0], t))
    a_eq = np.concatenate(([4.0, 16.0 / 3.0], -icos))[None, :]
    b_eq = np.array([1.0], dtype=np.float64)

    cos_grid = np.cos(x[:, None] * xi[None, :])
    a_ub = np.column_stack((-np.ones_like(x), -(x * x), cos_grid))
    b_ub = np.full(x.size, -float(grid_margin), dtype=np.float64)
    bounds = [(None, None), (None, None)] + [(0.0, None)] * k

    started = time.time()
    result = linprog(
        c,
        A_ub=a_ub,
        b_ub=b_ub,
        A_eq=a_eq,
        b_eq=b_eq,
        bounds=bounds,
        method="highs",
        options={
            "primal_feasibility_tolerance": 1.0e-9,
            "dual_feasibility_tolerance": 1.0e-9,
        },
    )
    elapsed = time.time() - started
    if not result.success:
        raise RuntimeError(f"even dual LP failed: {result.message}")

    y = np.asarray(result.x, dtype=np.float64)
    lam = np.maximum(y[2:], 0.0)
    a0 = float(y[0])
    a2 = float(y[1])
    grid_values = a0 + a2 * x * x - (cos_grid @ lam)
    return {
        "xi": xi,
        "a0": a0,
        "a1": 0.0,
        "a2": a2,
        "lambda": lam,
        "lambda_min_raw": float(np.min(y[2:])) if k else 0.0,
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "lp_objective": float(-result.fun),
        "lp_elapsed_seconds": float(elapsed),
        "x_grid_points": int(x_grid_points),
        "grid_margin": float(grid_margin),
        "grid_min_G": float(np.min(grid_values)),
        "grid_min_x": float(x[int(np.argmin(grid_values))]),
        "normalization_residual": float(4.0 * a0 + (16.0 / 3.0) * a2 - float(icos @ lam) - 1.0),
    }


def dual_dict(cert: dict[str, Any], *, verify_points: int, roundoff_safety: float) -> dict[str, Any]:
    return {
        "B0_dual": bound_constant(cert["a0"], cert["a2"], cert["xi"], cert["lambda"]),
        "coefficients": {"a0": float(cert["a0"]), "a1": 0.0, "a2": float(cert["a2"])},
        "frequencies": np.asarray(cert["xi"], dtype=np.float64),
        "lambda": np.asarray(cert["lambda"], dtype=np.float64),
        "curvature_verification": {
            "grid_points": int(verify_points),
            "roundoff_safety": float(roundoff_safety),
        },
        "mean_verification": {"fixed_mean": 0.0},
    }


def mix_with_uniform(
    cert: dict[str, Any],
    *,
    certified_min: float,
    desired_margin: float,
) -> dict[str, Any]:
    alpha = 0.0
    if float(certified_min) < float(desired_margin):
        alpha = (float(desired_margin) - float(certified_min)) / (0.25 - float(desired_margin))
        alpha = max(0.0, alpha) * (1.0 + 1.0e-10)
    out = dict(cert)
    if alpha > 0.0:
        out["a0"] = float((float(cert["a0"]) + 0.25 * alpha) / (1.0 + alpha))
        out["a2"] = float(float(cert["a2"]) / (1.0 + alpha))
        out["lambda"] = np.asarray(cert["lambda"], dtype=np.float64) / (1.0 + alpha)
    out["uniform_mixture_alpha"] = float(alpha)
    out["certified_L_even"] = bound_constant(out["a0"], out["a2"], out["xi"], out["lambda"])
    return out


def certify_even_dual(
    cert: dict[str, Any],
    *,
    verify_points: int = 200_001,
    roundoff_safety: float = 1.0e-12,
    desired_margin: float = 1.0e-6,
) -> dict[str, Any]:
    raw_dual = dual_dict(cert, verify_points=verify_points, roundoff_safety=roundoff_safety)
    raw_check = certify_g_nonnegative(raw_dual)
    mixed = mix_with_uniform(
        cert,
        certified_min=float(raw_check["certified_min_G"]),
        desired_margin=desired_margin,
    )
    mixed_dual = dual_dict(mixed, verify_points=verify_points, roundoff_safety=roundoff_safety)
    mixed_check = certify_g_nonnegative(mixed_dual)
    mixed["dual"] = mixed_dual
    mixed["raw_continuous_verification"] = raw_check
    mixed["continuous_verification"] = mixed_check
    mixed["certified_L_even"] = float(mixed_dual["B0_dual"])
    return mixed


def load_reference_or_sota() -> np.ndarray:
    path = Path("source/data/symmetry_resolution_candidates.npz")
    if path.exists():
        with np.load(path) as data:
            if "c000" in data:
                return np.asarray(data["c000"], dtype=np.float64)
    slp = ROOT / "slp_push.json"
    if slp.exists():
        payload = json.loads(slp.read_text())
        return np.asarray(payload["candidate_weights"]["best"], dtype=np.float64)
    return load_weights_from_json(ROOT / "converged_best.json", ["best_weights"])


def mass_correct(weights: np.ndarray) -> np.ndarray:
    w = np.asarray(weights, dtype=np.float64).copy()
    w += 0.5 - float(np.mean(w))
    return np.clip(w, 0.0, 1.0)


def evenize(weights: np.ndarray) -> np.ndarray:
    return mass_correct(0.5 * (np.asarray(weights, dtype=np.float64) + np.asarray(weights, dtype=np.float64)[::-1]))


def even_trapezoid(n: int = 4096, plateau_half_width: float = 0.25) -> np.ndarray:
    t = -1.0 + (np.arange(int(n), dtype=np.float64) + 0.5) * (2.0 / int(n))
    a = float(plateau_half_width)
    height = 1.0 / (1.0 + a)
    values = np.where(np.abs(t) <= a, height, height * (1.0 - np.abs(t)) / (1.0 - a))
    return mass_correct(values)


def standard_even_candidates() -> list[tuple[str, np.ndarray]]:
    n = 4096
    t = -1.0 + (np.arange(n, dtype=np.float64) + 0.5) * (2.0 / n)
    candidates: list[tuple[str, np.ndarray]] = [
        ("constant_half", np.full(n, 0.5, dtype=np.float64)),
        ("center_block_even", (np.abs(t) <= 0.5).astype(np.float64)),
        ("edge_blocks_even", (np.abs(t) >= 0.5).astype(np.float64)),
        ("simple_even_trapezoid", even_trapezoid(n=n, plateau_half_width=0.25)),
    ]
    conv_path = ROOT / "converged_best.json"
    if conv_path.exists():
        conv = load_weights_from_json(conv_path, ["best_weights"])
        candidates.append(("public_converged_best_evenized", evenize(conv)))
    slp_path = ROOT / "slp_push.json"
    if slp_path.exists():
        slp = np.asarray(json.loads(slp_path.read_text())["candidate_weights"]["best"], dtype=np.float64)
        candidates.append(("public_slp_push_evenized", evenize(slp)))
    reference = Path("source/data/symmetry_resolution_candidates.npz")
    if reference.exists():
        with np.load(reference) as data:
            if "c000" in data:
                candidates.append(("reference_reference_evenized", evenize(np.asarray(data["c000"], dtype=np.float64))))
    sr_npz = ROOT / "data" / "symmetry_resolution_candidates.npz"
    if sr_npz.exists():
        with np.load(sr_npz) as data:
            for key in data.files:
                if "even" in key.lower():
                    candidates.append((f"symmetry_resolution_{key}", np.asarray(data[key], dtype=np.float64)))
    return candidates


def adversary_gate(bound: float) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    seen = set()
    for name, w in standard_even_candidates():
        if name in seen:
            continue
        seen.add(name)
        score, argmax = exact_overlap(mass_correct(np.asarray(w, dtype=np.float64)))
        rows.append(
            {
                "name": name,
                "steps": int(np.asarray(w).size),
                "M": float(score),
                "argmax_x": float(argmax),
                "slack_M_minus_B0_even": float(score - float(bound)),
                "pass": bool(score + 1.0e-10 >= float(bound)),
            }
        )
    best_row = min(rows, key=lambda row: row["M"])
    return {
        "ceiling_threshold": REFERENCE_CEILING,
        "below_known_sota_threshold": bool(float(bound) <= REFERENCE_CEILING + 1.0e-12),
        "rows": rows,
        "all_standard_even_pass": bool(all(row["pass"] for row in rows)),
        "min_standard_even_slack": float(min(row["slack_M_minus_B0_even"] for row in rows)),
        "best_even_construction": best_row,
        "even_bracket": [float(bound), float(best_row["M"])],
        "even_bracket_width": float(best_row["M"] - float(bound)),
    }


def convergence_tail(rows: list[dict[str, Any]]) -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    for prev, cur in zip(rows[:-1], rows[1:]):
        out.append(
            {
                "from_xi_max": float(prev["xi_max"]),
                "to_xi_max": float(cur["xi_max"]),
                "certified_increment": float(cur["certified_L_even"] - prev["certified_L_even"]),
                "lp_increment": float(cur["lp_L_even"] - prev["lp_L_even"]),
            }
        )
    return out


def save_bracket_note(package: dict[str, Any], path: Path = BRACKET_JSON) -> None:
    gate = package["adversary_gate"]
    note = {
        "schema": "public even upper bracket note v1",
        "claim_scope": "Even-restricted feasible construction cross-checks only.",
        "B0_even": float(package["best"]["B0_even"]),
        "best_even_construction": gate["best_even_construction"],
        "even_bracket": gate["even_bracket"],
        "even_bracket_width": float(gate["even_bracket_width"]),
        "checked_even_constructions": gate["rows"],
    }
    path.write_text(json.dumps(_jsonify(note), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_even_dual_experiment(
    *,
    configs: list[dict[str, Any]] | None = None,
    verify_points: int = 200_001,
    roundoff_safety: float = 1.0e-12,
    desired_margin: float = 1.0e-6,
    out_path: Path = OUT_JSON,
) -> dict[str, Any]:
    if configs is None:
        configs = [
            {"xi_max": 320.0, "spacing": 0.25, "x_grid_points": 20_001, "grid_margin": 2.0e-6},
            {"xi_max": 480.0, "spacing": 0.25, "x_grid_points": 12_001, "grid_margin": 3.0e-6},
            {"xi_max": 640.0, "spacing": 0.25, "x_grid_points": 12_001, "grid_margin": 4.0e-6},
        ]

    started = time.time()
    rows = []
    best: dict[str, Any] | None = None
    for cfg in configs:
        xi = make_dense_comb(float(cfg["xi_max"]), float(cfg["spacing"]))
        solved = solve_grid_lp(
            xi,
            x_grid_points=int(cfg["x_grid_points"]),
            grid_margin=float(cfg["grid_margin"]),
        )
        checked = certify_even_dual(
            solved,
            verify_points=verify_points,
            roundoff_safety=roundoff_safety,
            desired_margin=desired_margin,
        )
        row = {
            "xi_max": float(cfg["xi_max"]),
            "spacing": float(cfg["spacing"]),
            "frequency_count": int(xi.size),
            "x_grid_points": int(cfg["x_grid_points"]),
            "grid_margin": float(cfg["grid_margin"]),
            "lp_L_even": float(solved["lp_objective"]),
            "certified_L_even": float(checked["certified_L_even"]),
            "a2": float(checked["a2"]),
            "lambda_min": float(np.min(checked["lambda"])) if xi.size else 0.0,
            "lambda_positive_count_gt_1e_10": int(np.sum(np.asarray(checked["lambda"]) > 1.0e-10)),
            "raw_certified_min_G": float(checked["raw_continuous_verification"]["certified_min_G"]),
            "certified_min_G": float(checked["continuous_verification"]["certified_min_G"]),
            "integral_G": float(checked["continuous_verification"]["integral_G"]),
            "uniform_mixture_alpha": float(checked["uniform_mixture_alpha"]),
            "lp_elapsed_seconds": float(solved["lp_elapsed_seconds"]),
        }
        rows.append(row)
        if best is None or row["certified_L_even"] > float(best["certified_L_even"]):
            best = checked
            best["config"] = dict(cfg)

    assert best is not None
    gate = adversary_gate(float(best["certified_L_even"]))
    package = {
        "schema": "public even fixed-mean cosine-variance Fejer dual v2",
        "metadata": {
            "source package": "public",
            "created_by": "source/even_dual_optimize.py",
            "claim_scope": "Verified continuum lower bound for the even-restricted problem only; not a full asymmetric M* bound.",
            "reference_evaluations": [293, 298, 360, 363],
        },
        "frequency_sweep": rows,
        "convergence_tail": convergence_tail(rows),
        "best": {
            "B0_even": float(best["certified_L_even"]),
            "margin_vs_reference_even_reuse": float(best["certified_L_even"] - REFERENCE_EVEN_REUSE),
            "exceeds_reference_even_reuse": bool(float(best["certified_L_even"]) > REFERENCE_EVEN_REUSE),
            "a0": float(best["a0"]),
            "a2": float(best["a2"]),
            "a2_sign": "positive" if float(best["a2"]) > 0.0 else ("negative" if float(best["a2"]) < 0.0 else "zero"),
            "lambda_min": float(np.min(best["lambda"])) if len(best["lambda"]) else 0.0,
            "lambda_nonnegative": bool(float(np.min(best["lambda"])) >= -1.0e-14) if len(best["lambda"]) else True,
            "lambda_positive_count_gt_1e_10": int(np.sum(np.asarray(best["lambda"]) > 1.0e-10)),
            "frequency_count": int(np.asarray(best["xi"]).size),
            "xi_max": float(np.max(best["xi"])) if len(best["xi"]) else 0.0,
            "spacing": float(best["config"]["spacing"]),
            "uniform_mixture_alpha": float(best["uniform_mixture_alpha"]),
            "dual": best["dual"],
            "continuous_verification": best["continuous_verification"],
            "raw_continuous_verification": best["raw_continuous_verification"],
        },
        "adversary_gate": gate,
        "elapsed_seconds": float(time.time() - started),
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    save_bracket_note(package)
    return package


def print_summary(package: dict[str, Any]) -> None:
    best = package["best"]
    print("B0_EVEN_CERTIFICATE")
    print(f"B0_even={best['B0_even']:.15f}")
    print(f"margin_vs_0.369234780={best['margin_vs_reference_even_reuse']:.15e}")
    print(f"a2={best['a2']:.17f} ({best['a2_sign']})")
    print(
        "lambda "
        f"min={best['lambda_min']:.3e} nonnegative={best['lambda_nonnegative']} "
        f"positive_count={best['lambda_positive_count_gt_1e_10']} "
        f"count={best['frequency_count']}"
    )
    check = best["continuous_verification"]
    print(
        "G_continuum "
        f"pass={check['pass']} certified_min={check['certified_min_G']:.12e} "
        f"grid_min={check['grid_min_G']:.12e} integral_G={check['integral_G']:.15f} "
        f"curvature_bound={check['second_derivative_sup_bound']:.12e}"
    )
    print("CONVERGENCE_TABLE")
    for row in package["frequency_sweep"]:
        print(
            f"xi_max={row['xi_max']:.1f} spacing={row['spacing']:.3f} "
            f"K={row['frequency_count']} lp={row['lp_L_even']:.15f} "
            f"cert={row['certified_L_even']:.15f} a2={row['a2']:.9f} "
            f"Gmin={row['certified_min_G']:.3e} alpha={row['uniform_mixture_alpha']:.3e} "
            f"seconds={row['lp_elapsed_seconds']:.2f}"
        )
    print("CONVERGENCE_TAIL")
    for row in package["convergence_tail"]:
        print(
            f"from={row['from_xi_max']:.1f} to={row['to_xi_max']:.1f} "
            f"cert_increment={row['certified_increment']:.15e} "
            f"lp_increment={row['lp_increment']:.15e}"
        )
    gate = package["adversary_gate"]
    print(
        "ADVERSARY_GATE "
        f"below_reference_threshold={gate['below_known_sota_threshold']} "
        f"all_even_pass={gate['all_standard_even_pass']} "
        f"min_even_slack={gate['min_standard_even_slack']:.12e}"
    )
    best_even = gate["best_even_construction"]
    print(
        "EVEN_UPPER_BRACKET "
        f"best_name={best_even['name']} M={best_even['M']:.15f} "
        f"bracket=[{gate['even_bracket'][0]:.15f}, {gate['even_bracket'][1]:.15f}] "
        f"width={gate['even_bracket_width']:.15e}"
    )
    for row in gate["rows"]:
        print(
            f"GATE {row['name']} steps={row['steps']} M={row['M']:.12f} "
            f"slack={row['slack_M_minus_B0_even']:.12e}"
        )


def main() -> int:
    package = run_even_dual_experiment()
    print_summary(package)
    return 0 if package["best"]["continuous_verification"]["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
