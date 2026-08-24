"""Standalone verifier for the improved Public SOC/localizer certificate.

The verifier intentionally depends only on Python, NumPy, mpmath, and the JSON
certificate it is asked to read.  It does not import CVXPY, scipy, or any
source package optimizer/reconstruction module.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np


DEFAULT_CERT = Path("source/soc_certificate_improved.json")
KNOWN_FEASIBLE_GUARD = 0.380895
REFERENCE_BASE_GLOBAL = 0.38030401970520017


class VerificationError(RuntimeError):
    pass


def _as_float_interval(pair: list[str] | tuple[str, str]) -> tuple[float, float]:
    lo = float(pair[0])
    hi = float(pair[1])
    if not (math.isfinite(lo) and math.isfinite(hi)) or lo > hi:
        raise VerificationError(f"bad interval {pair!r}")
    return lo, hi


def _scalar_mid(pair: list[str]) -> float:
    lo, hi = _as_float_interval(pair)
    return 0.5 * (lo + hi)


def _mid_array(pairs: list[list[str]]) -> np.ndarray:
    out = np.empty(len(pairs), dtype=np.float64)
    for i, pair in enumerate(pairs):
        out[i] = _scalar_mid(pair)
    return out


def _max_abs_array(pairs: list[list[str]]) -> np.ndarray:
    out = np.empty(len(pairs), dtype=np.float64)
    for i, pair in enumerate(pairs):
        lo, hi = _as_float_interval(pair)
        out[i] = max(abs(lo), abs(hi))
    return out


def _matrix_mid(pairs: list[list[list[str]]]) -> np.ndarray:
    return np.asarray([[_scalar_mid(pair) for pair in row] for row in pairs], dtype=np.float64)


def interval_support_upper(row: dict[str, Any], *, dps: int) -> tuple[float, list[tuple[int, float]]]:
    mp.iv.dps = int(dps)
    total = mp.iv.mpf([0.0, 0.0])
    boundary_flags: list[tuple[int, float]] = []
    threshold = float(row.get("alpha_boundary_threshold", 1.0e-10))
    for k, (xp, ap, bp) in enumerate(
        zip(row["atom_intervals"]["xi"], row["atom_intervals"]["alpha"], row["atom_intervals"]["beta"])
    ):
        xlo, xhi = _as_float_interval(xp)
        alo, ahi = _as_float_interval(ap)
        blo, bhi = _as_float_interval(bp)
        beta_nonzero = not (blo == 0.0 and bhi == 0.0)
        if beta_nonzero and alo <= 0.0:
            raise VerificationError(
                f"alpha interval not strictly positive where beta is nonzero: row={row['id']} k={k}"
            )
        if beta_nonzero and alo <= threshold:
            boundary_flags.append((k, alo))
        if ahi <= 0.0 and max(abs(blo), abs(bhi)) <= 1.0e-18:
            continue
        if alo <= 0.0:
            raise VerificationError(f"alpha interval crosses zero: row={row['id']} k={k} alpha={ap}")
        if xlo <= 0.0 <= xhi:
            raise VerificationError(f"xi interval contains zero: row={row['id']} k={k}")
        xiv = mp.iv.mpf([repr(xlo), repr(xhi)])
        av = mp.iv.mpf([repr(alo), repr(ahi)])
        bv = mp.iv.mpf([repr(blo), repr(bhi)])
        s = mp.iv.sin(xiv) / xiv
        total += (s * s) * (av + (bv * bv) / av)
    return float(total.b), boundary_flags


def evaluate_g_midpoints(row: dict[str, Any], x: np.ndarray, *, chunk: int) -> np.ndarray:
    coeff = row["coefficient_intervals"]
    a0 = _scalar_mid(coeff["a0_raw"])
    a1 = _scalar_mid(coeff["a1"])
    a2 = _scalar_mid(coeff["a2"])
    xi = _mid_array(row["atom_intervals"]["xi"])
    alpha = _mid_array(row["atom_intervals"]["alpha"])
    beta = _mid_array(row["atom_intervals"]["beta"])
    out = np.empty_like(x)
    for start in range(0, x.size, int(chunk)):
        stop = min(x.size, start + int(chunk))
        xs = x[start:stop]
        trig = np.cos(xs[:, None] * xi[None, :]) @ alpha
        trig += np.sin(xs[:, None] * xi[None, :]) @ beta
        out[start:stop] = a0 + a1 * xs + a2 * xs * xs - trig
    return out


def derivative_bound(row: dict[str, Any]) -> float:
    coeff = row["coefficient_intervals"]
    a1_abs = max(abs(v) for v in _as_float_interval(coeff["a1"]))
    a2_abs = max(abs(v) for v in _as_float_interval(coeff["a2"]))
    xi_abs = _max_abs_array(row["atom_intervals"]["xi"])
    alpha_abs = _max_abs_array(row["atom_intervals"]["alpha"])
    beta_abs = _max_abs_array(row["atom_intervals"]["beta"])
    return float(a1_abs + 4.0 * a2_abs + np.sum(xi_abs * (alpha_abs + beta_abs)))


def roundoff_pad(row: dict[str, Any]) -> float:
    coeff = row["coefficient_intervals"]
    a0_abs = max(abs(v) for v in _as_float_interval(coeff["a0_raw"]))
    a1_abs = max(abs(v) for v in _as_float_interval(coeff["a1"]))
    a2_abs = max(abs(v) for v in _as_float_interval(coeff["a2"]))
    alpha_abs = _max_abs_array(row["atom_intervals"]["alpha"])
    beta_abs = _max_abs_array(row["atom_intervals"]["beta"])
    scale = 1.0 + a0_abs + 2.0 * a1_abs + 4.0 * a2_abs + float(np.sum(alpha_abs + beta_abs))
    return float(5.0e-11 + 5.0e-12 * scale)


def positive_upper_midpoint(
    mid_values: np.ndarray,
    *,
    spacing: float,
    derivative_sup: float,
    eval_pad: float,
    shift: float,
) -> float:
    cell_sup = mid_values - float(shift) + 0.5 * float(derivative_sup) * float(spacing) + float(eval_pad)
    return float(spacing * np.sum(np.maximum(cell_sup, 0.0), dtype=np.float64))


def required_downshift(
    mid_values: np.ndarray,
    *,
    spacing: float,
    derivative_sup: float,
    eval_pad: float,
    target: float,
) -> tuple[float, float, float]:
    raw = positive_upper_midpoint(
        mid_values,
        spacing=spacing,
        derivative_sup=derivative_sup,
        eval_pad=eval_pad,
        shift=0.0,
    )
    if raw <= target:
        return 0.0, raw, raw
    lo = 0.0
    hi = max(1.0e-12, raw - target)
    while positive_upper_midpoint(
        mid_values,
        spacing=spacing,
        derivative_sup=derivative_sup,
        eval_pad=eval_pad,
        shift=hi,
    ) > target:
        hi *= 2.0
        if hi > 1.0:
            raise VerificationError("unexpectedly large positive-part downshift")
    for _ in range(70):
        mid = 0.5 * (lo + hi)
        if positive_upper_midpoint(
            mid_values,
            spacing=spacing,
            derivative_sup=derivative_sup,
            eval_pad=eval_pad,
            shift=mid,
        ) <= target:
            hi = mid
        else:
            lo = mid
    shifted = positive_upper_midpoint(
        mid_values,
        spacing=spacing,
        derivative_sup=derivative_sup,
        eval_pad=eval_pad,
        shift=hi,
    )
    return float(hi + 2.0e-12), float(raw), float(shifted)


def verify_row(row: dict[str, Any], settings: dict[str, Any]) -> dict[str, Any]:
    partitions = int(row.get("positive_part_partitions", settings["positive_part_partitions"]))
    spacing = 4.0 / float(partitions)
    x_mid = -2.0 + (np.arange(partitions, dtype=np.float64) + 0.5) * spacing
    values = evaluate_g_midpoints(row, x_mid, chunk=int(settings.get("chunk_size", 2048)))
    deriv = derivative_bound(row)
    pad = roundoff_pad(row)
    shift, raw_upper, shifted_upper = required_downshift(
        values,
        spacing=spacing,
        derivative_sup=deriv,
        eval_pad=pad,
        target=float(settings["positive_part_target"]),
    )
    if shifted_upper > 1.0:
        raise VerificationError(f"positive-part budget failed for row {row['id']}: {shifted_upper}")

    support_upper, boundary = interval_support_upper(row, dps=int(settings["mpmath_dps"]))
    coeff = row["coefficient_intervals"]
    a0 = _scalar_mid(coeff["a0_raw"])
    a1 = _scalar_mid(coeff["a1"])
    a2 = _scalar_mid(coeff["a2"])
    c0_lower = (a0 - shift) + (2.0 / 3.0) * a2 - support_upper - float(settings["coefficient_guard"])
    m0 = float(row["m"])
    l_source = c0_lower + a1 * m0 + 0.5 * a2 * m0 * m0 - float(settings["coefficient_guard"])

    got = {
        "id": row["id"],
        "m": m0,
        "K": int(row["K"]),
        "raw_upper_int_positive_part": raw_upper,
        "required_downshift_delta": shift,
        "shifted_upper_int_positive_part": shifted_upper,
        "positive_part_margin": 1.0 - shifted_upper,
        "support_interval_upper": support_upper,
        "quadratic_c0_lower": c0_lower,
        "L_source_m_lower": l_source,
        "a1": a1,
        "a2": a2,
        "boundary_alpha_flags": boundary,
    }

    expected = row.get("expected_hardened", {})
    tol = float(settings.get("comparison_tolerance", 2.5e-9))
    names = {
        "required_downshift_delta": shift,
        "raw_upper_int_positive_part": raw_upper,
        "support_interval_upper": support_upper,
        "L_source_m_lower": l_source,
    }
    for name, value in names.items():
        if name in expected and abs(float(value) - float(expected[name])) > tol:
            raise VerificationError(f"{name} mismatch for row {row['id']}: {value} vs {expected[name]}")

    adj = row.get("lower_bound_adjustment")
    if adj is not None:
        delta = float(adj["delta"])
        got["unadjusted_quadratic_c0_lower"] = got["quadratic_c0_lower"]
        got["unadjusted_L_source_m_lower"] = got["L_source_m_lower"]
        got["quadratic_c0_lower"] = float(got["quadratic_c0_lower"] + delta)
        got["L_source_m_lower"] = float(
            got["quadratic_c0_lower"] + got["a1"] * m0 + 0.5 * got["a2"] * m0 * m0
        )
        exp_adj = row.get("expected_adjusted_hardened", {})
        if exp_adj and abs(got["L_source_m_lower"] - float(exp_adj["L_source_m_lower"])) > tol:
            raise VerificationError(f"adjusted L mismatch for row {row['id']}")
    return got


def envelope_from_verified_rows(rows: list[dict[str, Any]], settings: dict[str, Any]) -> dict[str, Any]:
    mean_partitions = int(settings["mean_partitions"])
    m = np.linspace(0.0, 1.0, mean_partitions + 1, dtype=np.float64)
    q = np.empty((len(rows), m.size), dtype=np.float64)
    slope_sup = 0.0
    for i, row in enumerate(rows):
        c0 = float(row["quadratic_c0_lower"])
        a1 = float(row["a1"])
        a2 = float(row["a2"])
        q[i] = c0 + a1 * m + 0.5 * a2 * m * m
        slope_sup = max(slope_sup, float(np.max(np.abs(a1 + a2 * m))))
    envelope = np.max(q, axis=0)
    spacing = 1.0 / float(mean_partitions)
    lower_curve = envelope - 0.5 * slope_sup * spacing - float(settings["mean_guard"])
    idx = int(np.argmin(lower_curve))
    active = np.flatnonzero(q[:, idx] >= envelope[idx] - 2.0e-7)
    return {
        "mean_partitions": mean_partitions,
        "mean_spacing": spacing,
        "slope_sup_bound": slope_sup,
        "mean_variation_pad": 0.5 * slope_sup * spacing,
        "numeric_grid_min_before_mean_pad": float(envelope[idx]),
        "certified_min_over_0_1": float(lower_curve[idx]),
        "argmin_m_grid": float(m[idx]),
        "active_witnesses_at_argmin": [
            {"row_id": rows[int(i)]["id"], "m_source": float(rows[int(i)]["m"]), "value_at_argmin": float(q[int(i), idx])}
            for i in active[:12]
        ],
    }


def refined_envelope_from_verified_rows(rows: list[dict[str, Any]], settings: dict[str, Any], cert: dict[str, Any]) -> dict[str, Any]:
    refine = cert["m_coverage"]["refined_bracket"]
    lo, hi = map(float, refine["interval"])
    partitions = int(refine["partitions"])
    m = np.linspace(lo, hi, partitions + 1, dtype=np.float64)
    q = np.empty((len(rows), m.size), dtype=np.float64)
    slope_sup = 0.0
    for i, row in enumerate(rows):
        c0 = float(row["quadratic_c0_lower"])
        a1 = float(row["a1"])
        a2 = float(row["a2"])
        q[i] = c0 + a1 * m + 0.5 * a2 * m * m
        slope_sup = max(slope_sup, max(abs(a1 + a2 * lo), abs(a1 + a2 * hi)))
    envelope = np.max(q, axis=0)
    spacing = (hi - lo) / float(partitions)
    local_pad = 0.5 * slope_sup * spacing
    global_pad = float(refine["global_mean_variation_pad"])
    lower_global_pad = envelope - global_pad - float(settings["mean_guard"])
    lower_local_pad = envelope - local_pad - float(settings["mean_guard"])
    idx = int(np.argmin(lower_global_pad))

    # Reproduce a predecessor computation's outside-bracket exclusion on the stored coarse grid.
    coarse = envelope_from_verified_rows(rows, settings)
    mean_partitions = int(settings["mean_partitions"])
    m_all = np.linspace(0.0, 1.0, mean_partitions + 1, dtype=np.float64)
    q_all = np.empty((len(rows), m_all.size), dtype=np.float64)
    slope_all = 0.0
    for i, row in enumerate(rows):
        c0 = float(row["quadratic_c0_lower"])
        a1 = float(row["a1"])
        a2 = float(row["a2"])
        q_all[i] = c0 + a1 * m_all + 0.5 * a2 * m_all * m_all
        slope_all = max(slope_all, float(np.max(np.abs(a1 + a2 * m_all))))
    outside = (m_all < lo) | (m_all > hi)
    outside_lower = np.max(q_all[:, outside], axis=0) - 0.5 * slope_all / float(mean_partitions) - float(settings["mean_guard"])
    outside_idx = int(np.argmin(outside_lower))
    outside_min = float(outside_lower[outside_idx])
    if outside_min <= float(lower_global_pad[idx]):
        raise VerificationError("refined bracket does not exclude the outside coarse grid")
    if global_pad < local_pad:
        raise VerificationError("stored global mean pad does not cover refined local spacing")
    return {
        "coarse_full_domain": coarse,
        "refined_argmin_m_grid": float(m[idx]),
        "refined_numeric_min_before_pad": float(envelope[idx]),
        "refined_certified_min_with_retained_global_pad": float(lower_global_pad[idx]),
        "refined_certified_min_local_pad_only": float(lower_local_pad[idx]),
        "refine_mean_variation_pad": float(local_pad),
        "retained_mean_variation_pad": global_pad,
        "outside_refined_interval_min_using_coarse_pad": outside_min,
        "outside_excluded_vs_refined": True,
    }


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    return np.sinc(np.asarray(x) / math.pi)


def w_transform(omega: np.ndarray | float) -> np.ndarray | float:
    return 2.0 * sinc(omega)


def lambda_constant(local_lambda: np.ndarray, *, ell: int, w0: float) -> float:
    labels = list(range(-int(ell), int(ell) + 1))
    total = 0.0
    for r, j in enumerate(labels):
        for c, q in enumerate(labels):
            total += float(local_lambda[r, c]) * 0.25 * float(w_transform(float(j - q) * float(w0)))
    return float(total)


def lambda_a_matrix(local_lambda: np.ndarray, full_labels: np.ndarray, *, ell: int, w0: float) -> np.ndarray:
    labels = np.asarray(full_labels, dtype=np.int64).reshape(-1)
    neg_index = {int(label): i for i, label in enumerate(labels)}
    mu: dict[int, float] = {d: 0.0 for d in range(-2 * int(ell), 2 * int(ell) + 1)}
    small_labels = list(range(-int(ell), int(ell) + 1))
    for r, j in enumerate(small_labels):
        for c, q in enumerate(small_labels):
            if abs(j - q) <= 2 * int(ell):
                mu[j - q] += float(local_lambda[r, c])
    coeff = (float(w0) / (2.0 * math.pi)) ** 2
    sums = labels[:, None].astype(np.float64) + labels[None, :].astype(np.float64)
    kernel = np.zeros_like(sums, dtype=np.float64)
    for d, weight in mu.items():
        if weight != 0.0:
            kernel += float(weight) * w_transform((float(d) - sums) * float(w0))
    raw = coeff * kernel
    a_mat = np.empty_like(raw)
    for b_col, b_label in enumerate(labels.tolist()):
        a_mat[:, neg_index[-int(b_label)]] = raw[:, b_col]
    return 0.5 * (a_mat + a_mat.T)


def rebuild_gram(block: dict[str, Any]) -> np.ndarray:
    labels_pos = np.asarray(block["labels_pos"], dtype=np.int64)
    full_labels = np.asarray(block["full_labels"], dtype=np.int64)
    local = _matrix_mid(block["localizer_lambda_matrix_intervals"])
    alpha = _mid_array(block["alpha_intervals"])
    if alpha.size != labels_pos.size:
        raise VerificationError("Gram alpha length does not match positive label count")
    const = lambda_constant(local, ell=int(block["ell"]), w0=float(block["w0"]))
    if abs(const - float(block["lambda_constant"])) > float(block.get("comparison_tolerance", 2.5e-9)):
        raise VerificationError("localizer constant mismatch")
    a_mat = lambda_a_matrix(local, full_labels, ell=int(block["ell"]), w0=float(block["w0"]))
    labels = np.asarray(full_labels, dtype=np.int64)
    keep = labels != 0
    diag = np.zeros(labels.size, dtype=np.float64)
    by_label = {int(label): float(value) for label, value in zip(labels_pos, alpha)}
    for i, label in enumerate(labels.tolist()):
        if label != 0:
            diag[i] = 0.5 * by_label[abs(int(label))]
    gram = np.diag(diag[keep]) - a_mat[np.ix_(keep, keep)]
    return 0.5 * (gram + gram.T)


def shifted_cholesky_residual_bound(gram: np.ndarray, *, shift: float | None = None) -> dict[str, Any]:
    g = 0.5 * (np.asarray(gram, dtype=np.float64) + np.asarray(gram, dtype=np.float64).T)
    n = int(g.shape[0])
    eig = np.linalg.eigvalsh(g)
    eig_min = float(eig[0])
    eig_max = float(eig[-1])
    if shift is None:
        shift = min(2.0e-7, 0.5 * max(eig_min, 0.0))
    if shift <= 0.0:
        raise VerificationError(f"nonpositive Cholesky shift from eig_min={eig_min}")
    shifted = g - float(shift) * np.eye(n, dtype=np.float64)
    chol = np.linalg.cholesky(shifted)
    product = chol @ chol.T
    residual = shifted - product
    absdot = np.abs(chol) @ np.abs(chol.T)
    unit = 2.0**-53
    gamma_n = (n * unit) / (1.0 - n * unit)
    subtraction_pad = unit * (np.abs(shifted) + np.abs(product))
    entry_abs_bound = np.abs(residual) + 4.0 * (gamma_n * absdot + subtraction_pad) + 1.0e-30
    inf_upper = float(np.max(np.sum(entry_abs_bound, axis=1)))
    fro_upper = float(np.sqrt(np.sum(entry_abs_bound * entry_abs_bound, dtype=np.float64)))
    two_upper = min(inf_upper, fro_upper)
    lower = float(shift - two_upper)
    return {
        "method": "shifted Cholesky residual correction with Higham gamma_n binary64 roundoff envelope",
        "dimension": n,
        "float64_eig_min": eig_min,
        "float64_eig_max": eig_max,
        "shift_delta": float(shift),
        "raw_residual_inf_norm": float(np.linalg.norm(residual, ord=np.inf)),
        "raw_residual_fro_norm": float(np.linalg.norm(residual, ord="fro")),
        "gamma_n": float(gamma_n),
        "residual_norm_inf_upper": inf_upper,
        "residual_norm_fro_upper": fro_upper,
        "residual_norm2_upper": float(two_upper),
        "lambda_min_lower_bound": lower,
        "psd_certified": bool(lower >= 0.0),
    }


def verify_gram(cert: dict[str, Any]) -> dict[str, Any] | None:
    block = cert.get("localizer_gram_block")
    if not block:
        return None
    gram = rebuild_gram(block)
    got = shifted_cholesky_residual_bound(gram, shift=block.get("cholesky_shift_delta"))
    expected = block.get("expected_psd_certificate", {})
    tol = float(block.get("comparison_tolerance", 2.5e-9))
    if expected and abs(got["lambda_min_lower_bound"] - float(expected["lambda_min_lower_bound"])) > tol:
        raise VerificationError("Gram lambda_min lower-bound mismatch")
    if not got["psd_certified"]:
        raise VerificationError("Gram PSD verification failed")
    return got


def verify_certificate(cert_path: Path) -> dict[str, Any]:
    started = time.time()
    cert = json.loads(Path(cert_path).read_text(encoding="utf-8"))
    settings = cert["verification_settings"]
    mp.mp.dps = int(settings["mpmath_dps"])

    rows_in = cert["hardened_soc_rows"]
    verified_rows: list[dict[str, Any]] = []
    boundary_count = 0
    for row in rows_in:
        got = verify_row(row, settings)
        verified_rows.append(got)
        boundary_count += len(got["boundary_alpha_flags"])

    base_rows = [row for row_in, row in zip(rows_in, verified_rows) if not row_in.get("is_improved_perturbation")]
    base_env = envelope_from_verified_rows(base_rows, settings)
    if abs(base_env["certified_min_over_0_1"] - REFERENCE_BASE_GLOBAL) > float(settings["comparison_tolerance"]):
        raise VerificationError("base calibration mismatch from stored rows")

    if cert.get("localizer_gram_block"):
        refined = refined_envelope_from_verified_rows(verified_rows, settings, cert)
        final_value = float(refined["refined_certified_min_with_retained_global_pad"])
        expected = cert["expected_results"]["improved_hardened_global"]["value"]
        if abs(final_value - float(expected)) > float(settings["comparison_tolerance"]):
            raise VerificationError("improved global value mismatch")
    else:
        refined = None
        final_value = float(base_env["certified_min_over_0_1"])

    if final_value > KNOWN_FEASIBLE_GUARD:
        raise VerificationError(f"value exceeds feasible guard {KNOWN_FEASIBLE_GUARD}: {final_value}")

    gram_cert = verify_gram(cert)
    margin = final_value - REFERENCE_BASE_GLOBAL
    print("VERIFY_CERT_IMPROVED_PASS")
    print(f"certificate={cert_path}")
    print(f"base_calibration_global={base_env['certified_min_over_0_1']:.15f} argmin_m={base_env['argmin_m_grid']:.8f}")
    print(f"certified_global_L={final_value:.15f} margin_over_base={margin:.12e}")
    if refined is not None:
        print(
            f"refined_argmin_m={refined['refined_argmin_m_grid']:.8f} "
            f"coarse_full_L={refined['coarse_full_domain']['certified_min_over_0_1']:.15f} "
            f"refined_local_pad_L={refined['refined_certified_min_local_pad_only']:.15f}"
        )
        print(
            f"mean_pad={refined['retained_mean_variation_pad']:.12e} "
            f"outside_min={refined['outside_refined_interval_min_using_coarse_pad']:.15f}"
        )
    if gram_cert is not None:
        print(
            f"gram_lambda_min_lower={gram_cert['lambda_min_lower_bound']:.12e} "
            f"dimension={gram_cert['dimension']} gamma_n={gram_cert['gamma_n']:.12e}"
        )
    print(f"alpha_boundary_flags={boundary_count}")
    print(f"known_feasible_guard={KNOWN_FEASIBLE_GUARD:.15f}")
    print(f"elapsed_seconds={time.time() - started:.3f}")
    return {
        "status": "pass",
        "base_global": base_env["certified_min_over_0_1"],
        "certified_global_L": final_value,
        "margin_over_base": margin,
        "gram": gram_cert,
        "refined": refined,
        "elapsed_seconds": time.time() - started,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", default=str(DEFAULT_CERT))
    args = parser.parse_args(argv)
    try:
        verify_certificate(Path(args.certificate))
    except Exception as exc:  # noqa: BLE001
        print(f"VERIFY_CERT_IMPROVED_FAIL: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
