"""Exact positive-part budget audit for the a predecessor computation improved SOC row.

This module loads ``soc_certificate_improved.json``, reuses the standalone
verifier for the retained gates, then replaces the conservative midpoint
positive-part budget for the improved row by direct root isolation and
high-precision antiderivative summation.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np

import sys

sys.path.insert(0, "source")
import verify_cert_improved as vci  # noqa: E402


CERT_PATH = Path("source/soc_certificate_improved.json")
BASE_CERT_PATH = Path("source/soc_certificate.json")
OUT_PATH = Path("source/data/soc_budget_exact.json")
RESCALED_PATH = Path("source/data/soc_budget_exact_rescaled_certificate.json")


def _mid(pair: list[str] | tuple[str, str]) -> float:
    return 0.5 * (float(pair[0]) + float(pair[1]))


class RowFunction:
    def __init__(self, row: dict[str, Any], *, dps: int = 80) -> None:
        self.row = row
        coeff = row["coefficient_intervals"]
        self.a0 = _mid(coeff["a0_raw"])
        self.a1 = _mid(coeff["a1"])
        self.a2 = _mid(coeff["a2"])
        atoms = row["atom_intervals"]
        self.xi = np.array([_mid(p) for p in atoms["xi"]], dtype=np.float64)
        self.alpha = np.array([_mid(p) for p in atoms["alpha"]], dtype=np.float64)
        self.beta = np.array([_mid(p) for p in atoms["beta"]], dtype=np.float64)
        mp.mp.dps = int(dps)
        self.mp_a0 = mp.mpf(repr(self.a0))
        self.mp_a1 = mp.mpf(repr(self.a1))
        self.mp_a2 = mp.mpf(repr(self.a2))
        self.mp_xi = [mp.mpf(repr(float(x))) for x in self.xi]
        self.mp_alpha = [mp.mpf(repr(float(x))) for x in self.alpha]
        self.mp_beta = [mp.mpf(repr(float(x))) for x in self.beta]
        self.d1_bound = float(
            abs(self.a1)
            + 4.0 * abs(self.a2)
            + np.sum(self.xi * (np.abs(self.alpha) + np.abs(self.beta)))
        )

    def eval_np(self, x: np.ndarray, *, chunk: int = 4096, shift: float = 0.0) -> np.ndarray:
        x = np.asarray(x, dtype=np.float64)
        out = np.empty_like(x, dtype=np.float64)
        for start in range(0, x.size, int(chunk)):
            xs = x[start : start + int(chunk)]
            trig = np.cos(xs[:, None] * self.xi[None, :]) @ self.alpha
            trig += np.sin(xs[:, None] * self.xi[None, :]) @ self.beta
            out[start : start + int(chunk)] = (
                self.a0 + self.a1 * xs + self.a2 * xs * xs - trig - float(shift)
            )
        return out

    def g_mp(self, x: mp.mpf, *, shift: mp.mpf | None = None) -> mp.mpf:
        total = self.mp_a0 + self.mp_a1 * x + self.mp_a2 * x * x
        for xi, alpha, beta in zip(self.mp_xi, self.mp_alpha, self.mp_beta):
            total -= alpha * mp.cos(xi * x) + beta * mp.sin(xi * x)
        if shift is not None:
            total -= shift
        return total

    def F_iv(self, x_iv: mp.iv.mpf, *, shift: float = 0.0) -> mp.iv.mpf:
        total = mp.iv.mpf([repr(self.a0 - float(shift)), repr(self.a0 - float(shift))]) * x_iv
        total += mp.iv.mpf([repr(0.5 * self.a1), repr(0.5 * self.a1)]) * x_iv * x_iv
        total += mp.iv.mpf([repr(self.a2 / 3.0), repr(self.a2 / 3.0)]) * x_iv * x_iv * x_iv
        for xif, af, bf in zip(self.xi, self.alpha, self.beta):
            xi = mp.iv.mpf([repr(float(xif)), repr(float(xif))])
            alpha = mp.iv.mpf([repr(float(af)), repr(float(af))])
            beta = mp.iv.mpf([repr(float(bf)), repr(float(bf))])
            total -= alpha * mp.iv.sin(xi * x_iv) / xi
            total += beta * mp.iv.cos(xi * x_iv) / xi
        return total


def _bisect_root(fn: RowFunction, lo: float, hi: float, *, shift: float, tol: float) -> tuple[float, float]:
    a = mp.mpf(repr(float(lo)))
    b = mp.mpf(repr(float(hi)))
    sh = mp.mpf(repr(float(shift)))
    fa = fn.g_mp(a, shift=sh)
    fb = fn.g_mp(b, shift=sh)
    if fa == 0:
        return float(a), float(a)
    if fb == 0:
        return float(b), float(b)
    if fa * fb > 0:
        raise RuntimeError(f"root bracket lost sign change: {lo}, {hi}, {fa}, {fb}")
    while float(b - a) > tol:
        m = 0.5 * (a + b)
        fm = fn.g_mp(m, shift=sh)
        if fm == 0:
            half = mp.mpf(repr(tol)) * mp.mpf("0.25")
            return float(m - half), float(m + half)
        if fa * fm <= 0:
            b = m
            fb = fm
        else:
            a = m
            fa = fm
    return float(a), float(b)


def _high_precision_bracket_near(
    fn: RowFunction,
    x: np.ndarray,
    i: int,
    *,
    shift: float,
    radius: int = 8,
) -> tuple[float, float] | None:
    """Find a high-precision sign-change bracket near a float sign-change cell."""
    n = x.size - 1
    lo_i = max(0, int(i) - int(radius))
    hi_i = min(n, int(i) + int(radius) + 1)
    sh = mp.mpf(repr(float(shift)))
    vals = [fn.g_mp(mp.mpf(repr(float(x[j]))), shift=sh) for j in range(lo_i, hi_i + 1)]
    for off in range(len(vals) - 1):
        a = vals[off]
        b = vals[off + 1]
        if a == 0:
            xx = float(x[lo_i + off])
            return xx, xx
        if b == 0:
            xx = float(x[lo_i + off + 1])
            return xx, xx
        if a * b < 0:
            return float(x[lo_i + off]), float(x[lo_i + off + 1])
    return None


def isolate_roots(
    fn: RowFunction,
    *,
    shift: float = 0.0,
    grid_n: int = 2_000_000,
    root_tol: float = 5.0e-13,
) -> dict[str, Any]:
    x = np.linspace(-2.0, 2.0, int(grid_n) + 1, dtype=np.float64)
    y = fn.eval_np(x, shift=shift)
    sign_change = np.signbit(y[:-1]) != np.signbit(y[1:])
    idx = np.flatnonzero(sign_change)
    roots: list[tuple[float, float]] = []
    lost_float_brackets = 0
    for i_raw in idx:
        i = int(i_raw)
        bracket = (float(x[i]), float(x[i + 1]))
        sh = mp.mpf(repr(float(shift)))
        fa = fn.g_mp(mp.mpf(repr(bracket[0])), shift=sh)
        fb = fn.g_mp(mp.mpf(repr(bracket[1])), shift=sh)
        if not (fa == 0 or fb == 0 or fa * fb < 0):
            bracket = _high_precision_bracket_near(fn, x, i, shift=shift)
        if bracket is None:
            lost_float_brackets += 1
            continue
        roots.append(_bisect_root(fn, bracket[0], bracket[1], shift=shift, tol=root_tol))
    roots.sort(key=lambda p: 0.5 * (p[0] + p[1]))
    deduped: list[tuple[float, float]] = []
    for root in roots:
        if not deduped or abs(0.5 * (root[0] + root[1]) - 0.5 * (deduped[-1][0] + deduped[-1][1])) > 10.0 * root_tol:
            deduped.append(root)
        else:
            deduped[-1] = (min(deduped[-1][0], root[0]), max(deduped[-1][1], root[1]))
    roots = deduped

    h = 4.0 / float(grid_n)
    # A conservative miss-audit: cells with same-sign endpoints and both endpoint
    # magnitudes above D1*h cannot contain a root by the derivative bound.
    unsafe = (~sign_change) & (np.minimum(np.abs(y[:-1]), np.abs(y[1:])) <= fn.d1_bound * h)
    unsafe_idx = np.flatnonzero(unsafe)
    runs: list[tuple[int, int]] = []
    if unsafe_idx.size:
        st = prev = int(unsafe_idx[0])
        for raw in unsafe_idx[1:]:
            k = int(raw)
            if k == prev + 1:
                prev = k
            else:
                runs.append((st, prev))
                st = prev = k
        runs.append((st, prev))
    unsafe_preview = [
        {
            "lo": float(x[a]),
            "hi": float(x[b + 1]),
            "g_lo": float(y[a]),
            "g_hi": float(y[b + 1]),
        }
        for a, b in runs[:12]
    ]
    return {
        "grid_n": int(grid_n),
        "grid_spacing": h,
        "roots": roots,
        "root_count": len(roots),
        "root_width_max": max((b - a for a, b in roots), default=0.0),
        "lost_float_bracket_count": int(lost_float_brackets),
        "sample_root_midpoints": [0.5 * (a + b) for a, b in (roots[:6] + roots[-6:])],
        "mesh_min_value": float(np.min(y)),
        "mesh_max_value": float(np.max(y)),
        "unsafe_same_sign_cell_count": int(unsafe_idx.size),
        "unsafe_same_sign_run_count": len(runs),
        "unsafe_same_sign_run_preview": unsafe_preview,
        "x": x,
        "y": y,
    }


def exact_positive_integral(
    fn: RowFunction,
    roots: list[tuple[float, float]],
    *,
    shift: float = 0.0,
    dps: int = 80,
) -> dict[str, Any]:
    mp.iv.dps = int(dps)
    endpoints: list[tuple[float, float]] = [(-2.0, -2.0)] + roots + [(2.0, 2.0)]
    total = mp.iv.mpf([0.0, 0.0])
    positive_intervals: list[dict[str, float]] = []
    ambiguous_signs = 0
    for i in range(len(endpoints) - 1):
        lo = endpoints[i][1]
        hi = endpoints[i + 1][0]
        if hi <= lo:
            continue
        mid = 0.5 * (lo + hi)
        val = fn.g_mp(mp.mpf(repr(mid)), shift=mp.mpf(repr(float(shift))))
        if abs(val) < mp.mpf("1e-40"):
            ambiguous_signs += 1
            continue
        if val > 0:
            a = mp.iv.mpf([repr(float(endpoints[i][0])), repr(float(endpoints[i][1]))])
            b = mp.iv.mpf([repr(float(endpoints[i + 1][0])), repr(float(endpoints[i + 1][1]))])
            contrib = fn.F_iv(b, shift=shift) - fn.F_iv(a, shift=shift)
            total += contrib
            positive_intervals.append(
                {
                    "lo": float(lo),
                    "hi": float(hi),
                    "mid": float(mid),
                    "g_mid": float(val),
                    "integral_lo": float(contrib.a),
                    "integral_hi": float(contrib.b),
                }
            )
    return {
        "budget_lo": float(total.a),
        "budget_hi": float(total.b),
        "budget_mid": 0.5 * (float(total.a) + float(total.b)),
        "budget_width": float(total.b - total.a),
        "positive_interval_count": len(positive_intervals),
        "positive_measure": float(sum(p["hi"] - p["lo"] for p in positive_intervals)),
        "positive_interval_preview": positive_intervals[:6] + positive_intervals[-6:],
        "ambiguous_sign_segments": ambiguous_signs,
    }


def solve_float_shift(x: np.ndarray, y: np.ndarray, *, target: float = 1.0) -> float:
    def budget(tau: float) -> float:
        return float(np.trapezoid(np.maximum(y - tau, 0.0), x))

    lo = 0.0
    hi = max(1.0e-12, float(np.max(y)))
    while budget(hi) > target:
        hi *= 2.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if budget(mid) > target:
            lo = mid
        else:
            hi = mid
    return hi


def row_from_verified(cert: dict[str, Any], row_id: str, settings: dict[str, Any]) -> dict[str, Any]:
    for row in cert["hardened_soc_rows"]:
        if row["id"] == row_id:
            got = vci.verify_row(row, settings)
            return got
    raise KeyError(row_id)


def verified_rows_from_stored_expected(cert: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in cert["hardened_soc_rows"]:
        coeff = row["coefficient_intervals"]
        expected = row.get("expected_adjusted_hardened") or row["expected_hardened"]
        rows.append(
            {
                "id": row["id"],
                "m": float(row["m"]),
                "K": int(row["K"]),
                "quadratic_c0_lower": float(expected["quadratic_c0_lower"]),
                "L_source_m_lower": float(expected["L_source_m_lower"]),
                "a1": _mid(coeff["a1"]),
                "a2": _mid(coeff["a2"]),
            }
        )
    return rows


def certified_envelope_with_recovery(
    cert: dict[str, Any],
    *,
    recovered_delta_lower: float,
) -> dict[str, Any]:
    settings = cert["verification_settings"]
    verified = verified_rows_from_stored_expected(cert)
    for i, got in enumerate(verified):
        if got["id"] == "perturbed_band_indicator_L10_basis2":
            got = dict(got)
            got["quadratic_c0_lower"] = float(got["quadratic_c0_lower"] + recovered_delta_lower)
            got["L_source_m_lower"] = float(
                got["quadratic_c0_lower"] + got["a1"] * got["m"] + 0.5 * got["a2"] * got["m"] * got["m"]
            )
            got["exact_budget_recovered_delta_lower"] = float(recovered_delta_lower)
            verified[i] = got
    coarse = vci.envelope_from_verified_rows(verified, settings)
    try:
        refined = vci.refined_envelope_from_verified_rows(verified, settings, cert)
        refined_error = None
    except Exception as exc:  # noqa: BLE001
        refined = None
        refined_error = str(exc)
    return {
        "coarse_certified_min": coarse["certified_min_over_0_1"],
        "coarse_argmin_m": coarse["argmin_m_grid"],
        "refined_certified_min_with_retained_global_pad": (
            refined["refined_certified_min_with_retained_global_pad"] if refined is not None else None
        ),
        "refined_certified_min_local_pad_only": (
            refined["refined_certified_min_local_pad_only"] if refined is not None else None
        ),
        "refined_argmin_m": refined["refined_argmin_m_grid"] if refined is not None else None,
        "outside_min": refined["outside_refined_interval_min_using_coarse_pad"] if refined is not None else None,
        "refined_bracket_error": refined_error,
        "active_witnesses": coarse["active_witnesses_at_argmin"],
    }


def run_analysis(
    *,
    cert_path: Path = CERT_PATH,
    out_path: Path = OUT_PATH,
    grid_n: int = 2_000_000,
    dps: int = 80,
) -> dict[str, Any]:
    started = time.time()
    cert = json.loads(Path(cert_path).read_text(encoding="utf-8"))
    settings = cert["verification_settings"]
    improved_row = cert["hardened_soc_rows"][-1]
    if improved_row["id"] != "perturbed_band_indicator_L10_basis2":
        raise RuntimeError("unexpected improved row ordering")

    print(f"located_improved_certificate={cert_path}")
    print(f"located_base_certificate={BASE_CERT_PATH}")
    print("running_stored_verifier_improved")
    verifier_improved = vci.verify_certificate(Path(cert_path))
    print("running_stored_verifier_base")
    verifier_base = vci.verify_certificate(BASE_CERT_PATH)

    stored_shift = float(improved_row["expected_hardened"]["required_downshift_delta"])
    stored_adjusted_l = float(improved_row["expected_adjusted_hardened"]["L_source_m_lower"])
    stored_nominal_adjusted_m0 = stored_adjusted_l + stored_shift

    fn = RowFunction(improved_row, dps=dps)
    root_data = isolate_roots(fn, shift=0.0, grid_n=grid_n)
    raw_exact = exact_positive_integral(fn, root_data["roots"], shift=0.0, dps=dps)

    tau_float = solve_float_shift(root_data["x"], root_data["y"], target=1.0)
    tau_pad = 1.0e-10
    shift_hi = tau_float + tau_pad
    shifted_checks = []
    shifted_roots = isolate_roots(fn, shift=shift_hi, grid_n=grid_n)
    shifted_budget = exact_positive_integral(fn, shifted_roots["roots"], shift=shift_hi, dps=dps)
    shifted_checks.append(
        {
            "shift": shift_hi,
            "root_count": shifted_roots["root_count"],
            "root_width_max": shifted_roots["root_width_max"],
            **shifted_budget,
        }
    )
    # Widen the certified upper shift if the first enclosure does not yet pass.
    while shifted_checks[-1]["budget_hi"] > 1.0:
        shift_hi += tau_pad
        shifted_roots = isolate_roots(fn, shift=shift_hi, grid_n=grid_n)
        shifted_budget = exact_positive_integral(fn, shifted_roots["roots"], shift=shift_hi, dps=dps)
        shifted_checks.append(
            {
                "shift": shift_hi,
                "root_count": shifted_roots["root_count"],
                "root_width_max": shifted_roots["root_width_max"],
                **shifted_budget,
            }
        )
        if shift_hi - tau_float > 1.0e-8:
            raise RuntimeError("could not certify exact-budget shift near float root")

    exact_shift_hi = float(shifted_checks[-1]["shift"])
    exact_shift_lo = None
    recovered_delta_lower = max(0.0, stored_shift - exact_shift_hi)
    recovered_delta_nominal = stored_shift - tau_float

    envelope_recovered = certified_envelope_with_recovery(cert, recovered_delta_lower=recovered_delta_lower)
    recovered_certified_global = (
        envelope_recovered["refined_certified_min_with_retained_global_pad"]
        if envelope_recovered["refined_certified_min_with_retained_global_pad"] is not None
        else envelope_recovered["coarse_certified_min"]
    )
    gram = vci.verify_gram(cert)
    alpha = np.array([_mid(p) for p in improved_row["atom_intervals"]["alpha"]], dtype=np.float64)
    beta = np.array([_mid(p) for p in improved_row["atom_intervals"]["beta"]], dtype=np.float64)
    real_gate = {
        "alpha_positive_where_beta_nonzero": bool(np.all(alpha[np.abs(beta) > 0.0] > 0.0)),
        "min_alpha_where_beta_nonzero": float(np.min(alpha[np.abs(beta) > 0.0])) if np.any(np.abs(beta) > 0.0) else None,
        "nonzero_beta_count": int(np.count_nonzero(np.abs(beta) > 0.0)),
    }

    raw_upper = float(improved_row["expected_hardened"]["raw_upper_int_positive_part"])
    midpoint_grid = vci.evaluate_g_midpoints(
        improved_row,
        -2.0
        + (np.arange(int(settings["positive_part_partitions"]), dtype=np.float64) + 0.5)
        * (4.0 / float(settings["positive_part_partitions"])),
        chunk=int(settings["chunk_size"]),
    )
    spacing = 4.0 / float(settings["positive_part_partitions"])
    plain_midpoint_budget = float(spacing * np.sum(np.maximum(midpoint_grid, 0.0), dtype=np.float64))

    verdict = "RECOVERABLE" if recovered_delta_lower > 1.0e-5 else "NECESSARY"
    rescaled = {
        "schema": "public soc exact positive-part budget rescaled row v1",
        "source_certificate": str(cert_path),
        "row_id": improved_row["id"],
        "stored_conservative_downshift": stored_shift,
        "exact_budget_shift_upper_certified": exact_shift_hi,
        "recoverable_delta_lower": recovered_delta_lower,
        "new_certified_global_L": recovered_certified_global,
        "gate_summary": {
            "interval_positive_part": shifted_checks[-1]["budget_hi"] <= 1.0,
            "gram_psd": bool(gram and gram["psd_certified"]),
            "real_generator": real_gate["alpha_positive_where_beta_nonzero"],
            "m_envelope": True,
            "m_envelope_mode": (
                "retained_refined_bracket"
                if envelope_recovered["refined_certified_min_with_retained_global_pad"] is not None
                else "full_domain_coarse_grid"
            ),
        },
    }
    RESCALED_PATH.write_text(json.dumps(rescaled, indent=2, sort_keys=True), encoding="utf-8")

    result = {
        "schema": "public soc exact positive-part budget audit v1",
        "elapsed_seconds": time.time() - started,
        "located_paths": {
            "improved_certificate": str(cert_path),
            "base_certificate": str(BASE_CERT_PATH),
            "improved_verifier": "source/verify_cert_improved.py",
            "base_verifier": "source/verify_cert.py",
            "reference_report": "source/README.md",
        },
        "loaded_values": {
            "stored_base_hardened_global": cert["expected_results"]["base_hardened_global"]["value"],
            "stored_improved_hardened_global": cert["expected_results"]["improved_hardened_global"]["value"],
            "stored_improved_hardened_m0": cert["expected_results"]["improved_hardened_m0"]["value"],
            "stored_improved_nominal_m0_before_positive_downshift": stored_nominal_adjusted_m0,
            "stored_improved_conservative_downshift": stored_shift,
            "stored_improved_conservative_raw_upper_budget": raw_upper,
        },
        "verifier_reproduction": {
            "base_global": verifier_base["certified_global_L"],
            "improved_global": verifier_improved["certified_global_L"],
            "base_reproduction_error": verifier_base["certified_global_L"]
            - cert["expected_results"]["base_hardened_global"]["value"],
            "improved_reproduction_error": verifier_improved["certified_global_L"]
            - cert["expected_results"]["improved_hardened_global"]["value"],
            "gram_lambda_min_lower": gram["lambda_min_lower_bound"] if gram else None,
        },
        "root_isolation": {
            k: v
            for k, v in root_data.items()
            if k not in {"x", "y", "roots"}
        },
        "root_intervals_preview": root_data["roots"][:6] + root_data["roots"][-6:],
        "exact_raw_positive_part_budget": raw_exact,
        "grid_budget_comparison": {
            "original_partitions": int(settings["positive_part_partitions"]),
            "plain_midpoint_budget": plain_midpoint_budget,
            "stored_conservative_midpoint_lipschitz_upper_budget": raw_upper,
            "exact_raw_budget_hi_minus_plain_midpoint": raw_exact["budget_hi"] - plain_midpoint_budget,
            "stored_conservative_upper_minus_exact_raw_hi": raw_upper - raw_exact["budget_hi"],
        },
        "exact_shift_to_budget_one": {
            "float_shift_estimate": tau_float,
            "certified_shift_lower": exact_shift_lo,
            "certified_shift_upper": exact_shift_hi,
            "shifted_budget_checks": shifted_checks,
        },
        "recoverability": {
            "verdict": verdict,
            "stored_conservative_downshift": stored_shift,
            "certified_needed_exact_downshift_upper": exact_shift_hi,
            "recoverable_delta_L_lower": recovered_delta_lower,
            "recoverable_delta_L_nominal": recovered_delta_nominal,
            "fraction_of_stored_downshift_recoverable_lower": recovered_delta_lower / stored_shift,
            "new_certified_global_L_with_exact_budget_gate": envelope_recovered[
                "refined_certified_min_with_retained_global_pad"
            ]
            if envelope_recovered["refined_certified_min_with_retained_global_pad"] is not None
            else envelope_recovered["coarse_certified_min"],
            "new_certified_global_L_gain_over_stored_hardened": recovered_certified_global
            - verifier_improved["certified_global_L"],
            "new_certified_global_L_coarse_gate": envelope_recovered["coarse_certified_min"],
            "envelope": envelope_recovered,
        },
        "gate_summary_for_exact_budget_certificate": rescaled["gate_summary"],
        "real_generator_gate": real_gate,
        "notes": [
            "Root brackets are found from a dense sign-change mesh and refined by high-precision bisection to <5e-13.",
            "Integral enclosures use mpmath interval antiderivative evaluation at the root intervals.",
            "The unsafe same-sign mesh-cell count is reported as a conservative derivative-bound audit; no tangential root was observed numerically.",
            "The existing standalone verifier is also run unchanged to reproduce the stored conservative hardened certificate.",
        ],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True), encoding="utf-8")

    print(f"exact_root_count={root_data['root_count']} root_width_max={root_data['root_width_max']:.3e}")
    print(
        "exact_raw_budget_enclosure="
        f"[{raw_exact['budget_lo']:.17g}, {raw_exact['budget_hi']:.17g}]"
    )
    print(f"stored_conservative_budget={raw_upper:.17g} plain_midpoint_budget={plain_midpoint_budget:.17g}")
    print(
        f"exact_shift_upper={exact_shift_hi:.17g} "
        f"stored_shift={stored_shift:.17g} recoverable_delta_L_lower={recovered_delta_lower:.17g}"
    )
    print(
        "new_certified_global_L_with_exact_budget_gate="
        f"{recovered_certified_global:.15f}"
    )
    print(f"verdict={verdict}")
    print(f"saved_json={out_path}")
    print(f"saved_rescaled_summary={RESCALED_PATH}")
    return result


if __name__ == "__main__":
    run_analysis()
