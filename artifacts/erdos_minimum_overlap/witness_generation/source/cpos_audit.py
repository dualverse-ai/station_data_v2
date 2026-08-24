"""Audit the C>=0-augmented even dual jump from a predecessor computation.

The optimization routines are reused from :mod:`cpos_augmented_dual`, but the
positive-part verifier below is intentionally separate from that module's
verifier.  It evaluates G on a prescribed full-domain grid and integrates a
curvature upper envelope for max(0, G) on each interval.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

from cpos_augmented_dual import (
    TARGET_B0_EVEN,
    BEST_EVEN_CONSTRUCTION,
    load_b0even_best,
    solve_base_gate_for_xi,
    solve_relaxed_grid_lp_for_xi,
)


ROOT = Path("source")
AUDIT_JSON = ROOT / "cpos_audit.json"
REFERENCE_PRIMAL_GRID_VALUE = 0.3804437497588655
REFERENCE_ACTIVE_BAND = (-0.86, 0.85)


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


def local_sinc2(xi: np.ndarray) -> np.ndarray:
    xi = np.asarray(xi, dtype=np.float64)
    return np.sinc(xi / math.pi) ** 2


def local_int_cos_domain(xi: np.ndarray) -> np.ndarray:
    xi = np.asarray(xi, dtype=np.float64)
    out = np.empty_like(xi)
    small = np.abs(xi) < 1.0e-12
    out[small] = 4.0
    out[~small] = 2.0 * np.sin(2.0 * xi[~small]) / xi[~small]
    return out


def objective_l(a0: float, a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(float(a0) + (2.0 / 3.0) * float(a2) - float(local_sinc2(xi) @ lam))


def exact_integral_g(a0: float, a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(4.0 * float(a0) + (16.0 / 3.0) * float(a2) - float(local_int_cos_domain(xi) @ lam))


def selected_indices(best: dict[str, Any], k_requested: int) -> np.ndarray:
    """Replicate a predecessor computation's frequency ordering, returning source indices."""
    xi = np.asarray(best["dual"]["frequencies"], dtype=np.float64)
    lam = np.asarray(best["dual"]["lambda"], dtype=np.float64)
    active = np.flatnonzero(lam > 1.0e-10)
    inactive = np.flatnonzero(lam <= 1.0e-10)
    k = min(int(k_requested), int(xi.size))
    if k <= active.size:
        chosen = active[np.argsort(lam[active])[-k:]]
    else:
        chosen = np.concatenate((active, inactive[: k - active.size]))
    return chosen[np.argsort(xi[chosen])]


def selected_frequency_payload(best: dict[str, Any], k_requested: int) -> dict[str, Any]:
    xi_all = np.asarray(best["dual"]["frequencies"], dtype=np.float64)
    lam_all = np.asarray(best["dual"]["lambda"], dtype=np.float64)
    idx = selected_indices(best, k_requested)
    return {
        "indices": idx,
        "xi": xi_all[idx],
        "source_lambda": lam_all[idx],
        "selected_K": int(idx.size),
        "xi_max": float(np.max(xi_all[idx])) if idx.size else None,
        "xi_min": float(np.min(xi_all[idx])) if idx.size else None,
        "source_positive_count": int(np.sum(lam_all[idx] > 1.0e-10)),
    }


def added_frequency_summary(best: dict[str, Any], previous: np.ndarray | None, current: np.ndarray) -> dict[str, Any]:
    xi_all = np.asarray(best["dual"]["frequencies"], dtype=np.float64)
    prev = set(map(int, previous.tolist())) if previous is not None else set()
    added_idx = np.asarray([int(i) for i in current.tolist() if int(i) not in prev], dtype=np.int64)
    added_xi = np.sort(xi_all[added_idx]) if added_idx.size else np.empty(0, dtype=np.float64)
    return {
        "count": int(added_xi.size),
        "min_xi": float(added_xi[0]) if added_xi.size else None,
        "max_xi": float(added_xi[-1]) if added_xi.size else None,
        "frequencies": added_xi,
        "first_12": added_xi[:12],
        "last_12": added_xi[-12:],
    }


def relaxed_grid_points(k: int) -> int:
    # Matches the a predecessor computation policy near the jump, keeping the fine sweep inside
    # one official attempt.
    if int(k) <= 440:
        return 12_001
    return 8_001


def load_prior_reference_lp(k: int) -> dict[str, Any] | None:
    prior = ROOT / "cpos_augmented_convergence.json"
    if not prior.exists():
        return None
    data = json.loads(prior.read_text(encoding="utf-8"))
    for row in data.get("rows", []):
        if int(row.get("selected_K", -1)) == int(k) and row.get("status") == "success":
            return row.get("relaxed_grid_lp")
    return None


def evaluate_g_on_grid(
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


def curvature_bound(a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(2.0 * abs(float(a2)) + float(np.sum(np.abs(lam) * np.asarray(xi, dtype=np.float64) ** 2)))


def derivative_bound(a2: float, xi: np.ndarray, lam: np.ndarray) -> float:
    return float(4.0 * abs(float(a2)) + float(np.sum(np.abs(lam) * np.asarray(xi, dtype=np.float64))))


def positive_integral_of_linear_upper(v0: np.ndarray, v1: np.ndarray, h: float) -> float:
    """Exact integral of max(0, linear interpolation of endpoints)."""
    v0 = np.asarray(v0, dtype=np.float64)
    v1 = np.asarray(v1, dtype=np.float64)
    out = np.zeros_like(v0)

    both_pos = (v0 >= 0.0) & (v1 >= 0.0)
    out[both_pos] = 0.5 * float(h) * (v0[both_pos] + v1[both_pos])

    cross_up = (v0 < 0.0) & (v1 > 0.0)
    if np.any(cross_up):
        out[cross_up] = 0.5 * float(h) * (v1[cross_up] * v1[cross_up]) / (v1[cross_up] - v0[cross_up])

    cross_down = (v0 > 0.0) & (v1 < 0.0)
    if np.any(cross_down):
        out[cross_down] = 0.5 * float(h) * (v0[cross_down] * v0[cross_down]) / (v0[cross_down] - v1[cross_down])

    one_zero = ((v0 == 0.0) & (v1 > 0.0)) | ((v1 == 0.0) & (v0 > 0.0))
    if np.any(one_zero):
        out[one_zero] = 0.25 * float(h) * (v0[one_zero] + v1[one_zero])

    return float(np.sum(out, dtype=np.float64))


def conservative_positive_upper_from_samples(
    values: np.ndarray,
    *,
    spacing: float,
    second_derivative_sup: float,
    roundoff_pad: float,
) -> float:
    envelope = float(second_derivative_sup) * float(spacing) * float(spacing) / 8.0 + float(roundoff_pad)
    return positive_integral_of_linear_upper(values[:-1] + envelope, values[1:] + envelope, float(spacing))


def shift_needed_for_positive_mass(
    values: np.ndarray,
    *,
    spacing: float,
    second_derivative_sup: float,
    roundoff_pad: float,
    target: float,
) -> tuple[float, float]:
    raw = conservative_positive_upper_from_samples(
        values,
        spacing=spacing,
        second_derivative_sup=second_derivative_sup,
        roundoff_pad=roundoff_pad,
    )
    if raw <= float(target):
        return 0.0, raw
    lo = 0.0
    hi = max(1.0e-12, (raw - float(target)) / 0.1)
    while True:
        trial = conservative_positive_upper_from_samples(
            values - hi,
            spacing=spacing,
            second_derivative_sup=second_derivative_sup,
            roundoff_pad=roundoff_pad,
        )
        if trial <= float(target):
            break
        hi *= 2.0
        if hi > 1.0:
            raise RuntimeError("positive-part audit needed an unexpectedly large downshift")
    for _ in range(54):
        mid = 0.5 * (lo + hi)
        trial = conservative_positive_upper_from_samples(
            values - mid,
            spacing=spacing,
            second_derivative_sup=second_derivative_sup,
            roundoff_pad=roundoff_pad,
        )
        if trial <= float(target):
            hi = mid
        else:
            lo = mid
    final_upper = conservative_positive_upper_from_samples(
        values - hi,
        spacing=spacing,
        second_derivative_sup=second_derivative_sup,
        roundoff_pad=roundoff_pad,
    )
    return float(hi), float(final_upper)


def sign_bands_from_samples(x: np.ndarray, y: np.ndarray, *, positive: bool) -> list[dict[str, float]]:
    mask = y > 0.0 if positive else y < 0.0
    idx = np.flatnonzero(mask)
    if idx.size == 0:
        return []
    groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
    return [
        {
            "min_x": float(x[int(g[0])]),
            "max_x": float(x[int(g[-1])]),
            "center_x": float(0.5 * (x[int(g[0])] + x[int(g[-1])])),
            "sample_count": int(g.size),
        }
        for g in groups
    ]


def trapz_on_mask(x: np.ndarray, y: np.ndarray, mask: np.ndarray) -> float:
    yy = np.where(mask, y, 0.0)
    return float(np.trapezoid(yy, x))


def independent_reverify(lp: dict[str, Any], *, grids: tuple[int, ...] = (200_001, 800_001)) -> dict[str, Any]:
    xi = np.asarray(lp["xi"], dtype=np.float64)
    lam = np.asarray(lp["lambda"], dtype=np.float64)
    a0 = float(lp["a0"])
    a2 = float(lp["a2"])
    curvature = curvature_bound(a2, xi, lam)
    slope = derivative_bound(a2, xi, lam)
    roundoff_pad = 1.0e-12 * (1.0 + abs(a0) + 4.0 * abs(a2) + float(np.sum(np.abs(lam))))
    target = 1.0 - 1.0e-10

    grid_rows: list[dict[str, Any]] = []
    values_by_grid: dict[int, tuple[np.ndarray, np.ndarray]] = {}
    max_required_shift = 0.0
    started = time.time()
    for points in grids:
        x = np.linspace(-2.0, 2.0, int(points), dtype=np.float64)
        values = evaluate_g_on_grid(x, a0=a0, a2=a2, xi=xi, lam=lam)
        spacing = float(4.0 / (int(points) - 1))
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
        max_required_shift = max(max_required_shift, req_shift)
        grid_rows.append(
            {
                "grid_points": int(points),
                "spacing": spacing,
                "raw_upper_int_positive_part": float(raw_upper),
                "raw_margin_to_one": float(1.0 - raw_upper),
                "raw_pass": bool(raw_upper <= 1.0),
                "required_downshift_for_strict_pass": float(req_shift),
                "strict_target": target,
                "shifted_upper_int_positive_part": float(shifted_upper),
                "shifted_margin_to_one": float(1.0 - shifted_upper),
                "valid_L_with_this_shift": objective_l(a0 - req_shift, a2, xi, lam),
                "grid_trapezoid_positive_raw": float(np.trapezoid(np.maximum(values, 0.0), x)),
                "grid_min_G_raw": float(np.min(values)),
                "grid_max_G_raw": float(np.max(values)),
                "grid_argmin_raw": float(x[int(np.argmin(values))]),
                "grid_argmax_raw": float(x[int(np.argmax(values))]),
            }
        )
        values_by_grid[int(points)] = (x, values)

    common_shift_rows = []
    for points, (x, values) in values_by_grid.items():
        spacing = float(4.0 / (int(points) - 1))
        common_upper = conservative_positive_upper_from_samples(
            values - max_required_shift,
            spacing=spacing,
            second_derivative_sup=curvature,
            roundoff_pad=roundoff_pad,
        )
        common_shift_rows.append(
            {
                "grid_points": int(points),
                "common_shift_upper_int_positive_part": float(common_upper),
                "common_shift_margin_to_one": float(1.0 - common_upper),
                "pass": bool(common_upper <= 1.0),
            }
        )

    fine_points = max(values_by_grid)
    x_fine, raw_fine = values_by_grid[fine_points]
    shifted_fine = raw_fine - max_required_shift
    positive = np.maximum(shifted_fine, 0.0)
    negative = np.maximum(-shifted_fine, 0.0)
    band_lo, band_hi = REFERENCE_ACTIVE_BAND
    outside_band = (x_fine < band_lo) | (x_fine > band_hi)
    inside_band = ~outside_band
    pos_int = float(np.trapezoid(positive, x_fine))
    neg_int = float(np.trapezoid(negative, x_fine))
    outside_pos = trapz_on_mask(x_fine, positive, outside_band)
    inside_pos = trapz_on_mask(x_fine, positive, inside_band)
    positive_bands = sign_bands_from_samples(x_fine, shifted_fine, positive=True)
    negative_bands = sign_bands_from_samples(x_fine, shifted_fine, positive=False)

    final_l = objective_l(a0 - max_required_shift, a2, xi, lam)
    return {
        "selected_K": int(np.asarray(lp["xi"]).size),
        "provisional_L": float(lp["provisional_L"]),
        "a0_raw": a0,
        "a2": a2,
        "lambda_positive_count_gt_1e_10": int(np.sum(lam > 1.0e-10)),
        "xi_max": float(np.max(xi)) if xi.size else None,
        "second_derivative_sup_bound": curvature,
        "first_derivative_sup_bound": slope,
        "roundoff_pad_per_endpoint": float(roundoff_pad),
        "verification_grids": grid_rows,
        "common_downshift": float(max_required_shift),
        "common_valid_L": final_l,
        "common_shift_checks": common_shift_rows,
        "all_common_checks_pass": bool(all(row["pass"] for row in common_shift_rows)),
        "valid_after_common_shift": bool(all(row["pass"] for row in common_shift_rows) and final_l <= BEST_EVEN_CONSTRUCTION + 1.0e-12),
        "gain_over_B0_even": float(final_l - TARGET_B0_EVEN),
        "gap_to_reference_primal_grid": float(REFERENCE_PRIMAL_GRID_VALUE - final_l),
        "exact_integral_G_after_shift": exact_integral_g(a0 - max_required_shift, a2, xi, lam),
        "mechanism_on_finest_grid": {
            "grid_points": int(fine_points),
            "trapezoid_int_G_positive": pos_int,
            "trapezoid_int_G_negative": neg_int,
            "trapezoid_int_G": float(np.trapezoid(shifted_fine, x_fine)),
            "sample_min_G": float(np.min(shifted_fine)),
            "sample_max_G": float(np.max(shifted_fine)),
            "sample_argmin_G": float(x_fine[int(np.argmin(shifted_fine))]),
            "sample_argmax_G": float(x_fine[int(np.argmax(shifted_fine))]),
            "positive_band_count": int(len(positive_bands)),
            "negative_band_count": int(len(negative_bands)),
            "positive_bands": positive_bands[:80],
            "negative_bands": negative_bands[:80],
            "reference_active_band": list(REFERENCE_ACTIVE_BAND),
            "positive_integral_inside_reference_band": inside_pos,
            "positive_integral_outside_reference_band": outside_pos,
            "positive_integral_fraction_inside_band": float(inside_pos / pos_int) if pos_int > 0.0 else None,
            "positive_support_sample_min": float(x_fine[np.flatnonzero(shifted_fine > 0.0)[0]]) if np.any(shifted_fine > 0.0) else None,
            "positive_support_sample_max": float(x_fine[np.flatnonzero(shifted_fine > 0.0)[-1]]) if np.any(shifted_fine > 0.0) else None,
        },
        "elapsed_seconds": float(time.time() - started),
        "verification_method": (
            "Independent full-domain verifier: evaluate G on the stated grid, "
            "bound every interval by the endpoint secant plus |G''| h^2/8 "
            "and a small roundoff pad, then integrate max(0, affine upper "
            "envelope) exactly. The common downshift is the maximum shift "
            "needed across all requested grids."
        ),
    }


def run_audit(
    *,
    out_path: Path = AUDIT_JSON,
    fine_k_values: tuple[int, ...] = (200, 240, 280, 320, 360, 400, 440),
    audit_k_values: tuple[int, ...] = (400, 800),
    base_grid_points: int = 20_001,
    max_seconds: float = 1_650.0,
) -> dict[str, Any]:
    started = time.time()
    best = load_b0even_best()
    all_k = list(fine_k_values)
    for k in audit_k_values:
        if k not in all_k:
            all_k.append(k)

    rows: list[dict[str, Any]] = []
    lp_by_k: dict[int, dict[str, Any]] = {}
    previous_idx: np.ndarray | None = None
    package: dict[str, Any] = {
        "schema": "public cpos augmented even jump audit v1",
        "metadata": {
            "source package": "public",
            "created_by": "source/cpos_audit.py",
            "claim_scope": "Continuum-verified lower bound for the even/m=0 class only.",
            "frequency_ordering": (
                "same as a predecessor computation: first the retained positive B0_even atoms, "
                "then inactive certificate-comb frequencies in increasing xi"
            ),
            "independent_verifier": "does not call cpos_augmented_dual positive-part verification helpers",
            "reference_evaluations": [408, 412, 415, 419],
        },
        "target_B0_even": TARGET_B0_EVEN,
        "reference_primal_grid_value": REFERENCE_PRIMAL_GRID_VALUE,
        "reference_active_band": list(REFERENCE_ACTIVE_BAND),
        "fine_k_values": list(map(int, fine_k_values)),
        "audit_k_values": list(map(int, audit_k_values)),
        "rows": rows,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)

    for k in all_k:
        selected = selected_frequency_payload(best, k)
        xi = np.asarray(selected["xi"], dtype=np.float64)
        source_lam = np.asarray(selected["source_lambda"], dtype=np.float64)
        row: dict[str, Any] = {
            "K": int(k),
            "selected_K": int(selected["selected_K"]),
            "xi_min": selected["xi_min"],
            "xi_max": selected["xi_max"],
            "source_positive_count": selected["source_positive_count"],
            "added_since_previous_fine_K": added_frequency_summary(
                best,
                previous_idx if k in fine_k_values else selected_indices(best, max([j for j in fine_k_values if j <= max(fine_k_values)])),
                selected["indices"],
            ),
            "optimization_x_grid_points": relaxed_grid_points(k),
            "started_elapsed_seconds": float(time.time() - started),
        }
        print(f"AUDIT_SOLVE_START K={k} xi_max={row['xi_max']:.6g} elapsed={time.time()-started:.1f}s", flush=True)
        base = solve_base_gate_for_xi(xi, x_grid_points=base_grid_points)
        lp = solve_relaxed_grid_lp_for_xi(
            xi,
            source_lam=source_lam,
            full_active_frequency_count=int(np.sum(np.asarray(best["dual"]["lambda"]) > 1.0e-10)),
            full_comb_frequency_count=int(np.asarray(best["dual"]["frequencies"]).size),
            x_grid_points=relaxed_grid_points(k),
        )
        row["base_gate"] = base
        row["relaxed_grid_lp"] = lp
        row["status"] = "solved"
        row["elapsed_seconds_after_solve"] = float(time.time() - started)
        rows.append(row)
        lp_by_k[int(k)] = lp
        if k in fine_k_values:
            previous_idx = selected["indices"]
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(
            f"AUDIT_SOLVE_DONE K={k} base={base['value']:.15f} "
            f"Lprov={lp['provisional_L']:.15f} active={lp['lambda_positive_count_gt_1e_10']} "
            f"elapsed={time.time()-started:.1f}s",
            flush=True,
        )
        if time.time() - started > max_seconds - 550.0 and int(k) >= max(fine_k_values):
            print(f"AUDIT_TIME_GUARD_AFTER_FINE_SWEEP elapsed={time.time()-started:.1f}s", flush=True)
            break

    verifications: dict[str, Any] = {}
    for k in audit_k_values:
        if int(k) not in lp_by_k:
            prior_lp = load_prior_reference_lp(int(k))
            if prior_lp is None:
                raise RuntimeError(
                    f"K={k} was not solved before verification and no prior same-order LP was available"
                )
            lp_by_k[int(k)] = prior_lp
            package.setdefault("fallbacks", []).append(
                {
                    "K": int(k),
                    "source": "source/cpos_augmented_convergence.json",
                    "reason": "time guard left insufficient room to re-solve before independent verification",
                }
            )
        print(f"AUDIT_VERIFY_START K={k} elapsed={time.time()-started:.1f}s", flush=True)
        verifications[str(int(k))] = independent_reverify(lp_by_k[int(k)], grids=(200_001, 800_001))
        package["independent_reverification"] = verifications
        package["elapsed_seconds"] = float(time.time() - started)
        out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(
            f"AUDIT_VERIFY_DONE K={k} Lvalid={verifications[str(int(k))]['common_valid_L']:.15f} "
            f"pass={verifications[str(int(k))]['valid_after_common_shift']} "
            f"elapsed={time.time()-started:.1f}s",
            flush=True,
        )

    fine_rows = [row for row in rows if int(row["K"]) in fine_k_values]
    jumps = []
    for prev, curr in zip(fine_rows, fine_rows[1:]):
        jumps.append(
            {
                "from_K": int(prev["K"]),
                "to_K": int(curr["K"]),
                "delta_provisional_L": float(curr["relaxed_grid_lp"]["provisional_L"] - prev["relaxed_grid_lp"]["provisional_L"]),
                "added_count": int(curr["added_since_previous_fine_K"]["count"]),
                "added_min_xi": curr["added_since_previous_fine_K"]["min_xi"],
                "added_max_xi": curr["added_since_previous_fine_K"]["max_xi"],
            }
        )
    biggest_jump = max(jumps, key=lambda row: abs(row["delta_provisional_L"])) if jumps else None
    valid400 = verifications.get("400", {}).get("valid_after_common_shift", False)
    valid800 = verifications.get("800", {}).get("valid_after_common_shift", False)
    package["jump_analysis"] = {
        "stepwise_deltas": jumps,
        "largest_abs_step": biggest_jump,
        "explanation": (
            "The lift appears when the first low-frequency inactive block after the 200 retained "
            "active atoms is admitted; subsequent 40-frequency blocks refine the same low-frequency "
            "positive-part shape rather than causing another isolated atom event."
            if biggest_jump and int(biggest_jump["to_K"]) <= 240
            else "The fine table should be inspected; the largest step is not the first added block."
        ),
    }
    package["verdict"] = {
        "K400_valid": bool(valid400),
        "K800_valid": bool(valid800),
        "jump_genuine_continuum_feature": bool(valid400 and valid800),
        "scope": "even/m=0 class only",
    }
    package["elapsed_seconds"] = float(time.time() - started)
    out_path.write_text(json.dumps(_jsonify(package), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_audit_summary(package)
    return package


def print_audit_summary(package: dict[str, Any]) -> None:
    print("CPOS_AUDIT_FINE_K")
    print("K | xi_max | added_count | added_span | base_gate | base_diff | provisional_L")
    for row in package.get("rows", []):
        if int(row["K"]) not in package["fine_k_values"]:
            continue
        add = row["added_since_previous_fine_K"]
        print(
            f"{row['K']:4d} | {row['xi_max']:.8g} | {add['count']:3d} | "
            f"[{add['min_xi']},{add['max_xi']}] | "
            f"{row['base_gate']['value']:.15f} | "
            f"{row['base_gate']['difference_from_target']:+.3e} | "
            f"{row['relaxed_grid_lp']['provisional_L']:.15f}",
            flush=True,
        )
    print("CPOS_AUDIT_INDEPENDENT_REVERIFY")
    for k, ver in sorted(package.get("independent_reverification", {}).items(), key=lambda kv: int(kv[0])):
        print(
            f"K={k} common_shift={ver['common_downshift']:.6e} "
            f"valid_L={ver['common_valid_L']:.15f} "
            f"pass={ver['valid_after_common_shift']} "
            f"gap_to_reference={ver['gap_to_reference_primal_grid']:.6e}",
            flush=True,
        )
        for grow in ver["verification_grids"]:
            print(
                f"  grid={grow['grid_points']} raw_upper={grow['raw_upper_int_positive_part']:.15f} "
                f"raw_margin={grow['raw_margin_to_one']:+.3e} "
                f"shift={grow['required_downshift_for_strict_pass']:.6e} "
                f"shifted_upper={grow['shifted_upper_int_positive_part']:.15f} "
                f"shifted_margin={grow['shifted_margin_to_one']:+.3e}",
                flush=True,
            )
    print(f"CPOS_AUDIT_VERDICT {package.get('verdict')}", flush=True)


def load_best_even_candidate() -> np.ndarray:
    path = ROOT / "data" / "symmetry_resolution_candidates.npz"
    with np.load(path, allow_pickle=False) as data:
        return np.asarray(data["reference_reference_frontier_best_even"], dtype=np.float64)


if __name__ == "__main__":
    run_audit()
