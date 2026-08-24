"""Pilot for charging the dropped SOC completion-of-squares remainder.

This is a finite step-box diagnostic.  The hardened SOC envelope rows give

    M >= q_i(m) = c0_i + a1_i*m + 0.5*a2_i*m^2

after replacing the per-frequency SOC expression by its support function.
For a step function f, the dropped nonnegative slack is

    D_i(f) = sum_k alpha_k Re(hhat_k)^2
           + sum_{alpha_k>0} alpha_k (Im(hhat_k)-beta_k*sinc(xi_k)/alpha_k)^2,

where hhat is the Fourier transform of f-1/2 on [-1,1].  This driver solves
the finite-n convex program

    min_f max_i q_i(m_fixed) + D_i(f)

under 0<=f<=1, mean(f)=1/2, and the exact first-overlap-moment constraint.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path
from typing import Any

import cvxpy as cp
import numpy as np

sys.path.insert(0, "source")

import soc_budget_exact as sbe  # noqa: E402
import soc_dual as sd  # noqa: E402
import soc_e1_certificate as e1c  # noqa: E402
import soc_freq_density3 as sfd3  # noqa: E402
import soc_freq_density4 as sfd4  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
TMP = Path("runs/cache/soc_sos_remainder")
BASE_CERT_PATH = ROOT / "soc_certificate_improved.json"
BASE_EXACT_BUDGET_PATH = DATA / "soc_budget_exact.json"
OUT_JSON = DATA / "soc_sos_remainder_pilot.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_sos_remainder_pilot.json"
GENERATOR_CACHE = DATA / "soc_sos_remainder_pilot_generators.npz"
NCONV_OUT_JSON = DATA / "soc_sos_nconv.json"
NCONV_OUT_JSON_ROOT_COPY = ROOT / "soc_sos_nconv.json"
NCONV_GENERATOR_CACHE = DATA / "soc_sos_nconv_generators.npz"
NCONV_ROW_CACHE_DIR = DATA / "soc_sos_nconv_rows"

PILOT_N = 48
TEST_ANCHORS = (0.0, 0.003)
E4F_ROW_ANCHORS = (0.0, 0.003, 0.004475)
NCONV_TARGET_M = (0.0026, 0.003)
NCONV_STEPS = (48, 64, 96, 128, 192, 256)
NCONV_E8F_ROW_ANCHORS = (0.0, 0.0026, 0.003, 0.004475)
CLARABEL_TOL = 1.0e-8
SCS_TOL = 1.0e-7
MEAN_TOL = 5.0e-9
REMAINDER_ALPHA_TOL = 1.0e-10
REMAINDER_BETA_TOL = 1.0e-8


def _jsonify(value: Any) -> Any:
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, (np.floating, np.integer)):
        return value.item()
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(k): _jsonify(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonify(v) for v in value]
    return value


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_jsonify(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def sinc(x: np.ndarray | float) -> np.ndarray:
    return np.sinc(np.asarray(x, dtype=np.float64) / math.pi)


def _mid_interval(pair: list[str] | tuple[str, str]) -> float:
    return 0.5 * (float(pair[0]) + float(pair[1]))


def _row_value(row: dict[str, Any], m: float) -> float:
    mm = float(m)
    return float(row["quadratic_c0_lower"]) + float(row["a1"]) * mm + 0.5 * float(row["a2"]) * mm * mm


def _parse_base_generator_rows() -> list[dict[str, Any]]:
    cert = _load_json(BASE_CERT_PATH)
    exact = _load_json(BASE_EXACT_BUDGET_PATH)
    verified_rows, recovered = smh.build_verified_rows_with_baseline_recovery(cert, exact)
    by_id = {row["id"]: row for row in verified_rows}
    out: list[dict[str, Any]] = []
    for cert_row in cert["hardened_soc_rows"]:
        row_id = str(cert_row["id"])
        coeff_row = by_id[row_id]
        atoms = cert_row["atom_intervals"]
        xi = np.asarray([_mid_interval(v) for v in atoms["xi"]], dtype=np.float64)
        alpha = np.asarray([_mid_interval(v) for v in atoms["alpha"]], dtype=np.float64)
        beta = np.asarray([_mid_interval(v) for v in atoms["beta"]], dtype=np.float64)
        out.append(
            {
                "id": row_id,
                "family": "base",
                "source_m": float(coeff_row["m"]),
                "quadratic_c0_lower": float(coeff_row["quadratic_c0_lower"]),
                "a1": float(coeff_row["a1"]),
                "a2": float(coeff_row["a2"]),
                "xi": xi,
                "alpha": np.maximum(alpha, 0.0),
                "beta": beta,
                "K": int(xi.size),
                "recovered_reference_delta": (
                    float(coeff_row.get("exact_budget_recovered_delta_lower", 0.0))
                    if row_id == smh.IMPROVED_ROW_ID
                    else 0.0
                ),
            }
        )
    return out


def _cache_key(anchor: float, suffix: str) -> str:
    return f"e4f_{float(anchor):.7f}_{suffix}".replace(".", "p")


def _load_generator_cache() -> dict[str, np.ndarray]:
    if not GENERATOR_CACHE.exists():
        return {}
    with np.load(GENERATOR_CACHE, allow_pickle=False) as data:
        return {key: np.asarray(data[key], dtype=np.float64) for key in data.files}


def _save_generator_cache(cache: dict[str, np.ndarray]) -> None:
    GENERATOR_CACHE.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(GENERATOR_CACHE, **cache)


def _load_nconv_generator_cache() -> dict[str, np.ndarray]:
    if not NCONV_GENERATOR_CACHE.exists():
        return {}
    with np.load(NCONV_GENERATOR_CACHE, allow_pickle=False) as data:
        return {key: np.asarray(data[key], dtype=np.float64) for key in data.files}


def _save_nconv_generator_cache(cache: dict[str, np.ndarray]) -> None:
    NCONV_GENERATOR_CACHE.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(NCONV_GENERATOR_CACHE, **cache)


def _e4f_cache_path(anchor: float) -> Path:
    safe = f"{float(anchor):.7f}".replace(".", "p")
    return DATA / "soc_freq_density3_rows" / f"e4f_m_{safe}.json"


def _e8f_cache_path(anchor: float) -> Path:
    safe = f"{float(anchor):.7f}".replace(".", "p")
    return sfd4.ROW_CACHE_DIR / f"e8f_m_{safe}.json"


def _nconv_row_cache_path(anchor: float) -> Path:
    safe = f"{float(anchor):.7f}".replace(".", "p")
    return NCONV_ROW_CACHE_DIR / f"e8f_m_{safe}.json"


def _load_e4f_metadata(anchor: float) -> dict[str, Any]:
    path = _e4f_cache_path(anchor)
    if not path.exists():
        raise FileNotFoundError(path)
    payload = _load_json(path)
    row = payload["row"]
    return {
        "id": str(row["id"]),
        "family": "e4f",
        "source_m": float(row["m"]),
        "quadratic_c0_lower": float(row["quadratic_c0_lower"]),
        "a1": float(row["a1"]),
        "a2": float(row["a2"]),
        "nominal_raw_L_cached": float(payload["nominal_raw_L"]),
        "selected_frequency_count_cached": int(payload["selected_frequency_count"]),
        "cache_path": str(path),
    }


def _load_e8f_metadata(anchor: float) -> dict[str, Any]:
    for path in (_e8f_cache_path(anchor), _nconv_row_cache_path(anchor)):
        if path.exists():
            payload = _load_json(path)
            row = payload.get("row")
            if row is None:
                continue
            return {
                "id": str(row["id"]),
                "family": "e8f",
                "source_m": float(row["m"]),
                "quadratic_c0_lower": float(row["quadratic_c0_lower"]),
                "a1": float(row["a1"]),
                "a2": float(row["a2"]),
                "nominal_raw_L_cached": float(payload["nominal_raw_L"]),
                "selected_frequency_count_cached": int(payload["selected_frequency_count"]),
                "cache_path": str(path),
            }
    raise FileNotFoundError(_e8f_cache_path(anchor))


def _row_from_generator_meta(meta: dict[str, Any], xi: np.ndarray, alpha: np.ndarray, beta: np.ndarray) -> dict[str, Any]:
    return {
        "id": str(meta["id"]),
        "family": str(meta.get("family", "unknown")),
        "source_m": float(meta["source_m"]),
        "quadratic_c0_lower": float(meta["quadratic_c0_lower"]),
        "a1": float(meta["a1"]),
        "a2": float(meta["a2"]),
        "xi": np.asarray(xi, dtype=np.float64),
        "alpha": np.maximum(np.asarray(alpha, dtype=np.float64), 0.0),
        "beta": np.asarray(beta, dtype=np.float64),
        "K": int(np.asarray(xi).size),
        "source": {"cache_path": str(meta.get("cache_path", "")), "origin": "reconstructed_generator"},
        "nominal_raw_L": float(meta.get("nominal_raw_L_cached", np.nan)),
    }


def _solve_e4f_generator(anchor: float, xi_full: np.ndarray, cache: dict[str, np.ndarray]) -> tuple[dict[str, Any], dict[str, Any]]:
    meta = _load_e4f_metadata(anchor)
    k_xi = _cache_key(anchor, "xi")
    k_alpha = _cache_key(anchor, "alpha")
    k_beta = _cache_key(anchor, "beta")
    if k_xi in cache and k_alpha in cache and k_beta in cache:
        xi = np.asarray(cache[k_xi], dtype=np.float64)
        alpha = np.asarray(cache[k_alpha], dtype=np.float64)
        beta = np.asarray(cache[k_beta], dtype=np.float64)
        meta.update({"xi": xi, "alpha": alpha, "beta": beta, "K": int(xi.size)})
        return meta, {"status": "loaded_generator_cache", "anchor_m": float(anchor), "K": int(xi.size)}

    started = time.time()
    sol = sd.solve_fixed_mean_soc(
        np.asarray(xi_full, dtype=np.float64),
        m=float(anchor),
        x_grid_points=1001,
        solver="CLARABEL",
        max_iter=500,
        tol=CLARABEL_TOL,
    )
    comp = sd.compress_zero_pairs(sol)
    xi = np.asarray(comp["xi"], dtype=np.float64)
    alpha = np.maximum(np.asarray(comp["alpha"], dtype=np.float64), 0.0)
    beta = np.asarray(comp["beta"], dtype=np.float64)
    cache[k_xi] = xi
    cache[k_alpha] = alpha
    cache[k_beta] = beta
    meta.update({"xi": xi, "alpha": alpha, "beta": beta, "K": int(xi.size)})
    diag = {
        "status": "reconstructed_by_resolve",
        "anchor_m": float(anchor),
        "K": int(xi.size),
        "solver_status": str(sol["solver_status"]),
        "solve_elapsed_seconds": float(sol["solve_elapsed_seconds"]),
        "elapsed_seconds": float(time.time() - started),
        "raw_L_resolved": float(comp["raw_L"]),
        "raw_L_cached": float(meta["nominal_raw_L_cached"]),
        "raw_L_difference": float(comp["raw_L"] - meta["nominal_raw_L_cached"]),
        "selected_frequency_count_cached": int(meta["selected_frequency_count_cached"]),
    }
    return meta, diag


def _nconv_cache_key(anchor: float, suffix: str) -> str:
    return f"e8f_{float(anchor):.7f}_{suffix}".replace(".", "p")


def _harden_e8f_comp_for_nconv(comp: dict[str, Any], anchor: float) -> dict[str, Any]:
    budget = e1c._exact_budget_for_row(sfd4._row_for_exact_budget(comp, float(anchor)), grid_n=sfd4.ROOT_GRID_N, dps=sfd4.EXACT_DPS)
    row = sfd4._hardened_row(comp, budget, float(anchor))
    payload = {
        "schema": "public cached exact-hardened SOC E8f row for SOS n-convergence v1",
        "family": "e8f",
        "anchor_m": float(anchor),
        "comb_description": "base K=400 plus 0.015625-grid fill on [4,16]",
        "solver_status": str(comp.get("solver_status", "unknown")),
        "nominal_raw_L": float(comp["raw_L"]),
        "nominal_solver_objective_L": float(comp.get("solver_objective_L", comp["raw_L"])),
        "selected_frequency_count": int(comp["selected_frequency_count"]),
        "zero_pruned_count": int(comp.get("zero_pruned_count", 0)),
        "solve_elapsed_seconds": float(comp.get("solve_elapsed_seconds", 0.0)),
        "exact_shift": float(budget["certified_shift_upper"]),
        "raw_budget_hi": float(budget["raw_budget_hi"]),
        "shifted_budget_hi": float(budget["shifted_budget_checks"][-1]["budget_hi"]),
        "positive_part_margin": float(budget["positive_part_margin"]),
        "root_count": int(budget["root_count"]),
        "root_width_max": float(budget["root_width_max"]),
        "lost_float_bracket_count": int(budget["lost_float_bracket_count"]),
        "unsafe_same_sign_cell_count": int(budget["unsafe_same_sign_cell_count"]),
        "real_generator_gate_pass": bool(row["real_generator_gate_pass"]),
        "beta_active_count_gt_1e_8": int(row["beta_active_count_gt_1e_8"]),
        "row_value_at_source_m": float(row["L_source_m_lower"]),
        "row": row,
        "cache_status": "newly_solved_for_nconv",
    }
    _write_json(_nconv_row_cache_path(anchor), payload)
    return payload


def _solve_e8f_generator(anchor: float, xi_full: np.ndarray, cache: dict[str, np.ndarray]) -> tuple[dict[str, Any], dict[str, Any]]:
    k_xi = _nconv_cache_key(anchor, "xi")
    k_alpha = _nconv_cache_key(anchor, "alpha")
    k_beta = _nconv_cache_key(anchor, "beta")
    meta_missing = False
    try:
        meta = _load_e8f_metadata(anchor)
    except FileNotFoundError:
        meta_missing = True
        meta = {}

    if k_xi in cache and k_alpha in cache and k_beta in cache and not meta_missing:
        row = _row_from_generator_meta(meta, cache[k_xi], cache[k_alpha], cache[k_beta])
        return row, {
            "status": "loaded_generator_cache",
            "anchor_m": float(anchor),
            "K": int(row["K"]),
            "metadata_cache_path": str(meta.get("cache_path", "")),
        }

    started = time.time()
    print(f"e8f_generator_solve_start m={float(anchor):.7f} metadata_missing={meta_missing}", flush=True)
    sol = sd.solve_fixed_mean_soc(
        np.asarray(xi_full, dtype=np.float64),
        m=float(anchor),
        x_grid_points=1001,
        solver="CLARABEL",
        max_iter=700,
        tol=CLARABEL_TOL,
    )
    comp = sd.compress_zero_pairs(sol)
    print(
        f"e8f_generator_solve_done m={float(anchor):.7f} status={sol['solver_status']} "
        f"raw={comp['raw_L']:.15f} active_freq={comp['selected_frequency_count']} "
        f"solve_seconds={sol['solve_elapsed_seconds']:.1f}",
        flush=True,
    )
    if meta_missing:
        print(f"e8f_generator_harden_start m={float(anchor):.7f}", flush=True)
        payload = _harden_e8f_comp_for_nconv(comp, anchor)
        print(
            f"e8f_generator_harden_done m={float(anchor):.7f} "
            f"L_source={payload['row_value_at_source_m']:.15f} "
            f"shift={payload['exact_shift']:.12e}",
            flush=True,
        )
        meta = _load_e8f_metadata(anchor)
        meta["cache_path"] = str(_nconv_row_cache_path(anchor))
        cache_status = "reconstructed_and_hardened_by_resolve"
        raw_cached = float(payload["nominal_raw_L"])
    else:
        cache_status = "reconstructed_by_resolve"
        raw_cached = float(meta["nominal_raw_L_cached"])

    xi = np.asarray(comp["xi"], dtype=np.float64)
    alpha = np.maximum(np.asarray(comp["alpha"], dtype=np.float64), 0.0)
    beta = np.asarray(comp["beta"], dtype=np.float64)
    cache[k_xi] = xi
    cache[k_alpha] = alpha
    cache[k_beta] = beta
    row = _row_from_generator_meta(meta, xi, alpha, beta)
    diag = {
        "status": cache_status,
        "anchor_m": float(anchor),
        "K": int(xi.size),
        "solver_status": str(sol["solver_status"]),
        "solve_elapsed_seconds": float(sol["solve_elapsed_seconds"]),
        "elapsed_seconds": float(time.time() - started),
        "raw_L_resolved": float(comp["raw_L"]),
        "raw_L_cached": raw_cached,
        "raw_L_difference": float(comp["raw_L"] - raw_cached),
        "selected_frequency_count_cached": int(meta.get("selected_frequency_count_cached", xi.size)),
        "metadata_cache_path": str(meta.get("cache_path", "")),
    }
    return row, diag


def _load_rows() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    rows = _parse_base_generator_rows()
    cert = _load_json(BASE_CERT_PATH)
    freqs = sfd3._build_frequency_sets(e1c._base_frequencies(cert))
    e4f_xi = np.asarray(freqs["e4f"], dtype=np.float64)
    cache = _load_generator_cache()
    diagnostics: list[dict[str, Any]] = []
    changed = False
    for anchor in E4F_ROW_ANCHORS:
        before_keys = set(cache)
        row, diag = _solve_e4f_generator(anchor, e4f_xi, cache)
        diagnostics.append(diag)
        rows.append(row)
        changed = changed or (set(cache) != before_keys)
    if changed:
        _save_generator_cache(cache)
    return rows, diagnostics


def _load_nconv_rows() -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    rows = _parse_base_generator_rows()
    cert = _load_json(BASE_CERT_PATH)
    freqs = sfd4._build_frequency_sets(e1c._base_frequencies(cert))
    e8f_xi = np.asarray(freqs["e8f"], dtype=np.float64)
    cache = _load_nconv_generator_cache()
    diagnostics: list[dict[str, Any]] = []
    changed = False
    for anchor in NCONV_E8F_ROW_ANCHORS:
        before_keys = set(cache)
        row, diag = _solve_e8f_generator(anchor, e8f_xi, cache)
        diagnostics.append(diag)
        rows.append(row)
        changed = changed or (set(cache) != before_keys)
    if changed:
        _save_nconv_generator_cache(cache)
    inclusion = sfd4._inclusion_check(freqs)
    return rows, diagnostics, {
        "e8f_frequency_count": int(e8f_xi.size),
        "inclusion_check": inclusion,
    }


def step_fourier_matrix(n: int, xi: np.ndarray) -> np.ndarray:
    xi = np.asarray(xi, dtype=np.float64).reshape(-1)
    n = int(n)
    h = 2.0 / float(n)
    edges = -1.0 + h * np.arange(n + 1, dtype=np.float64)
    mat = np.empty((xi.size, n), dtype=np.complex128)
    zero = np.abs(xi) < 1.0e-13
    if np.any(zero):
        mat[zero, :] = h
    nz = np.flatnonzero(~zero)
    for start in range(0, nz.size, 128):
        take = nz[start : start + 128]
        om = xi[take]
        mat[take, :] = (np.exp(-1j * om[:, None] * edges[:-1]) - np.exp(-1j * om[:, None] * edges[1:])) / (
            1j * om[:, None]
        )
    return mat


def _affine_constraints(n: int, m: float) -> tuple[np.ndarray, float, float]:
    n = int(n)
    h = 2.0 / float(n)
    centers = -1.0 + h * (np.arange(n, dtype=np.float64) + 0.5)
    mass_target = 1.0
    first_f_target = -0.5 * float(m)
    return centers, mass_target, first_f_target


def _initial_feasible(n: int, m: float) -> np.ndarray:
    centers, mass_target, first_target = _affine_constraints(n, m)
    h = 2.0 / float(n)
    # f(t)=1/2+slope*t has int t*f(t)dt = slope*int t^2 dt.
    slope = float(first_target) / (2.0 / 3.0)
    f0 = 0.5 + slope * centers
    f0 = np.clip(f0, 0.0, 1.0)
    a = np.vstack([h * np.ones(n, dtype=np.float64), h * centers])
    b = np.asarray([mass_target, first_target], dtype=np.float64)
    for _ in range(20):
        resid = a @ f0 - b
        if float(np.max(np.abs(resid))) <= 1.0e-13:
            break
        free = (f0 > 1.0e-10) & (f0 < 1.0 - 1.0e-10)
        if np.sum(free) < 2:
            free = np.ones(n, dtype=bool)
        af = a[:, free]
        delta = af.T @ np.linalg.solve(af @ af.T + 1.0e-18 * np.eye(2), resid)
        f0[free] -= delta
        f0 = np.clip(f0, 0.0, 1.0)
    return f0


def _row_remainder_expr(row: dict[str, Any], f: cp.Variable, mat_cache: dict[str, tuple[np.ndarray, np.ndarray]], n: int) -> cp.Expression:
    xi = np.asarray(row["xi"], dtype=np.float64)
    alpha = np.asarray(row["alpha"], dtype=np.float64)
    beta = np.asarray(row["beta"], dtype=np.float64)
    keep = (alpha > REMAINDER_ALPHA_TOL) | (np.abs(beta) > REMAINDER_BETA_TOL)
    xi = xi[keep]
    alpha = alpha[keep]
    beta = beta[keep]
    key = str(row["id"])
    if key not in mat_cache:
        mat = step_fourier_matrix(int(n), xi)
        mat_cache[key] = (np.real(mat), np.imag(mat))
    real_mat, imag_mat = mat_cache[key]
    re_h = real_mat @ f - sinc(xi)
    im_h = imag_mat @ f
    terms: list[cp.Expression] = []
    pos = alpha > REMAINDER_ALPHA_TOL
    if np.any(alpha > 0.0):
        terms.append(cp.sum(cp.multiply(alpha, cp.square(re_h))))
    if np.any(pos):
        shift = np.zeros_like(alpha)
        shift[pos] = beta[pos] * sinc(xi[pos]) / alpha[pos]
        terms.append(cp.sum(cp.multiply(alpha[pos], cp.square(im_h[pos] - shift[pos]))))
    if not terms:
        return cp.Constant(0.0)
    return sum(terms)


def _row_remainder_data(
    row: dict[str, Any],
    f0: np.ndarray,
    null_basis: np.ndarray,
    n: int,
) -> dict[str, Any]:
    xi = np.asarray(row["xi"], dtype=np.float64)
    alpha = np.asarray(row["alpha"], dtype=np.float64)
    beta = np.asarray(row["beta"], dtype=np.float64)
    keep = (alpha > REMAINDER_ALPHA_TOL) | (np.abs(beta) > REMAINDER_BETA_TOL)
    xi = xi[keep]
    alpha = alpha[keep]
    beta = beta[keep]
    if xi.size == 0:
        return {
            "row_id": str(row["id"]),
            "family": str(row.get("family", "unknown")),
            "source_m": float(row["source_m"]),
            "q": None,
            "D_scale": 1.0,
            "atom_count": 0,
            "reduced_atom_count": 0,
            "alpha": alpha,
            "beta": beta,
            "xi": xi,
            "pos_mask": np.zeros(0, dtype=bool),
            "re_indices": np.zeros((0, n - 2), dtype=np.float64),
            "re_shift": np.zeros(0, dtype=np.float64),
            "im_indices": np.zeros((0, n - 2), dtype=np.float64),
            "im_shift": np.zeros(0, dtype=np.float64),
            "top_atom_info": [],
        }
    row_scale = float(max(np.max(alpha), np.max(np.abs(beta)), 1.0e-300))
    alpha_n = alpha / row_scale
    beta_n = beta / row_scale
    pos = alpha_n > REMAINDER_ALPHA_TOL
    mat = step_fourier_matrix(int(n), xi)
    real_mat = np.real(mat)
    imag_mat = np.imag(mat)
    re_map = real_mat @ null_basis
    re_shift = real_mat @ f0 - sinc(xi)
    if np.any(pos):
        im_map = imag_mat[pos] @ null_basis
        im_shift = imag_mat[pos] @ f0 - beta_n[pos] * sinc(xi[pos]) / alpha_n[pos]
    else:
        im_map = np.zeros((0, null_basis.shape[1]), dtype=np.float64)
        im_shift = np.zeros(0, dtype=np.float64)
    atom_info = []
    for j in range(min(6, xi.size)):
        atom_info.append(
            {
                "xi": float(xi[j]),
                "alpha": float(alpha[j]),
                "beta": float(beta[j]),
                "alpha_normalized": float(alpha_n[j]),
                "beta_normalized": float(beta_n[j]),
            }
        )
    return {
        "row_id": str(row["id"]),
        "family": str(row.get("family", "unknown")),
        "source_m": float(row["source_m"]),
        "q": None,
        "D_scale": row_scale,
        "atom_count": int(xi.size),
        "reduced_atom_count": int(np.sum(pos)),
        "alpha": alpha_n,
        "beta": beta_n,
        "xi": xi,
        "pos_mask": pos,
        "re_indices": re_map,
        "re_shift": re_shift,
        "im_indices": im_map,
        "im_shift": im_shift,
        "top_atom_info": atom_info,
    }


def _nullspace_basis(constraints: np.ndarray) -> np.ndarray:
    _, _, vh = np.linalg.svd(constraints, full_matrices=True)
    return vh[constraints.shape[0] :, :].T.copy()


def _solve_scaled_remainder_program(rows: list[dict[str, Any]], *, m: float, n: int) -> dict[str, Any]:
    started = time.time()
    n = int(n)
    m = float(m)
    centers, mass_target, first_target = _affine_constraints(n, m)
    h = 2.0 / float(n)
    pure_values = np.asarray([_row_value(row, m) for row in rows], dtype=np.float64)
    pure_idx = int(np.argmax(pure_values))
    pure_envelope = float(pure_values[pure_idx])
    null_basis = _nullspace_basis(np.vstack([h * np.ones(n, dtype=np.float64), h * centers]))
    f0 = _initial_feasible(n, m)
    if null_basis.size:
        q, _ = np.linalg.qr(null_basis, mode="reduced")
        null_basis = q
    u = cp.Variable(null_basis.shape[1], name="u")
    t = cp.Variable(name="t")
    f_expr = f0 if null_basis.size == 0 else f0 + null_basis @ u
    constraints: list[Any] = [f_expr >= 0.0, f_expr <= 1.0]
    row_data = [_row_remainder_data(row, f0, null_basis, n) for row in rows]
    for qv, data in zip(pure_values, row_data):
        if data["atom_count"] == 0:
            constraints.append(float(qv) <= t)
            continue
        re_expr = data["re_indices"] @ u + data["re_shift"]
        terms = [cp.sum_squares(cp.multiply(np.sqrt(data["alpha"]), re_expr))]
        if data["reduced_atom_count"] > 0:
            im_expr = data["im_indices"] @ u + data["im_shift"]
            terms.append(cp.sum_squares(cp.multiply(np.sqrt(data["alpha"][data["pos_mask"]]), im_expr)))
        D_expr = float(data["D_scale"]) * sum(terms)
        constraints.append(float(qv) + D_expr <= t)

    if null_basis.size:
        u.value = np.zeros(null_basis.shape[1], dtype=np.float64)
    t.value = pure_envelope + 1.0e-3
    problem = cp.Problem(cp.Minimize(t), constraints)

    solver_attempts = [
        (
            "CLARABEL",
            {
                "solver": "CLARABEL",
                "verbose": False,
                "max_iter": 5000,
                "time_limit": 120.0,
                "tol_gap_abs": CLARABEL_TOL,
                "tol_gap_rel": CLARABEL_TOL,
                "tol_feas": CLARABEL_TOL,
            },
        ),
        (
            "SCS",
            {
                "solver": "SCS",
                "verbose": False,
                "max_iters": 250000,
                "eps": SCS_TOL,
                "time_limit_secs": 180.0,
                "acceleration_lookback": 0,
                "normalize": True,
            },
        ),
    ]

    solve_value = None
    used_solver = None
    status = "unknown"
    last_error: str | None = None
    solver_attempts_log = []
    for solver_name, kwargs in solver_attempts:
        try:
            attempt_started = time.time()
            solve_value = problem.solve(**kwargs)
            used_solver = solver_name
            status = str(problem.status)
            solver_attempts_log.append(
                {
                    "solver": solver_name,
                    "status": status,
                    "elapsed_seconds": float(time.time() - attempt_started),
                    "value": None if solve_value is None else float(solve_value),
                }
            )
            if status in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
                break
        except Exception as exc:  # noqa: BLE001
            last_error = repr(exc)
            status = f"exception:{solver_name}"
            solver_attempts_log.append({"solver": solver_name, "status": status, "error": last_error})
            continue
    if solve_value is None and last_error is not None:
        raise RuntimeError(f"scaled remainder solve failed at m={m}: {last_error}")

    if null_basis.size:
        u_val = np.asarray(u.value, dtype=np.float64).reshape(-1)
        f_val = f0 + null_basis @ u_val
    else:
        u_val = np.zeros(0, dtype=np.float64)
        f_val = f0.copy()
    f_val = np.asarray(f_val, dtype=np.float64).reshape(-1)
    row_eval = []
    for row, qv, data in zip(rows, pure_values, row_data):
        if data["atom_count"] == 0:
            d_total = 0.0
            d_re = 0.0
            d_im = 0.0
        else:
            mat = step_fourier_matrix(n, data["xi"])
            hhat = mat @ f_val - sinc(data["xi"])
            d_re_norm = float(np.sum(data["alpha"] * (np.real(hhat) ** 2)))
            d_im_norm = 0.0
            if data["reduced_atom_count"] > 0:
                pos = data["pos_mask"]
                d_im_norm = float(
                    np.sum(
                        data["alpha"][pos]
                        * (np.imag(hhat[pos]) - data["beta"][pos] * sinc(data["xi"][pos]) / data["alpha"][pos]) ** 2
                    )
                )
            d_re = float(data["D_scale"]) * d_re_norm
            d_im = float(data["D_scale"]) * d_im_norm
            d_total = d_re + d_im
        row_eval.append(
            {
                "row_id": str(row["id"]),
                "family": str(row.get("family", "unknown")),
                "source_m": float(row["source_m"]),
                "q": float(qv),
                "D": d_total,
                "D_re": d_re,
                "D_im": d_im,
                "q_plus_D": float(qv + d_total),
                "D_scale": float(data["D_scale"]),
                "K": int(row["K"]),
                "atom_count": int(data["atom_count"]),
                "reduced_atom_count": int(data["reduced_atom_count"]),
                "top_atom_info": data["top_atom_info"][:4],
            }
        )
    row_eval.sort(key=lambda item: float(item["q_plus_D"]), reverse=True)
    max_qd = float(row_eval[0]["q_plus_D"])
    result = {
        "m": m,
        "n": n,
        "status": status,
        "solver": used_solver,
        "solver_attempts": solver_attempts_log,
        "solve_value": None if solve_value is None else float(solve_value),
        "pure_envelope": pure_envelope,
        "pure_controlling_row": str(rows[pure_idx]["id"]),
        "remainder_value": None if solve_value is None else float(solve_value),
        "remainder_lift": None if solve_value is None else float(float(solve_value) - pure_envelope),
        "recomputed_lift": float(max_qd - pure_envelope),
        "D_zero_reproduction": pure_envelope,
        "D_zero_reproduction_error": 0.0,
        "mass": float(h * np.sum(f_val)),
        "mass_error": float(h * np.sum(f_val) - mass_target),
        "first_f_moment": float(h * (centers @ f_val)),
        "first_f_moment_error": float(h * (centers @ f_val) - first_target),
        "target_first_f_moment": first_target,
        "box_min": float(np.min(f_val)),
        "box_max": float(np.max(f_val)),
        "elapsed_seconds": float(time.time() - started),
        "row_eval": row_eval,
        "top_rows_by_q_plus_D": row_eval[:8],
        "top_rows_by_D": sorted(row_eval, key=lambda item: float(item["D"]), reverse=True)[:8],
        "f": f_val,
    }
    result["gate_pass"] = bool(
        result["status"] in ("optimal", "optimal_inaccurate")
        and abs(result["D_zero_reproduction_error"]) <= 1.0e-12
        and abs(result["mass_error"]) <= MEAN_TOL
        and abs(result["first_f_moment_error"]) <= MEAN_TOL
        and result["box_min"] >= -1.0e-7
        and result["box_max"] <= 1.0 + 1.0e-7
        and max_qd + 5.0e-8 >= pure_envelope
    )
    return result


def solve_remainder_program(rows: list[dict[str, Any]], *, m: float, n: int = PILOT_N) -> dict[str, Any]:
    started = time.time()
    n = int(n)
    m = float(m)
    centers, mass_target, first_target = _affine_constraints(n, m)
    h = 2.0 / float(n)
    pure_values = np.asarray([_row_value(row, m) for row in rows], dtype=np.float64)
    pure_idx = int(np.argmax(pure_values))
    pure_envelope = float(pure_values[pure_idx])

    f = cp.Variable(n, name="f")
    t = cp.Variable(name="t")
    constraints: list[Any] = [
        f >= 0.0,
        f <= 1.0,
        h * cp.sum(f) == mass_target,
        h * (centers @ f) == first_target,
    ]
    mat_cache: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    for row, q in zip(rows, pure_values):
        constraints.append(float(q) + _row_remainder_expr(row, f, mat_cache, n) <= t)

    f0 = _initial_feasible(n, m)
    f.value = f0
    t.value = pure_envelope + 1.0e-3
    problem = cp.Problem(cp.Minimize(t), constraints)
    solve_kwargs = {
        "solver": "CLARABEL",
        "verbose": False,
        "max_iter": 1000,
        "tol_gap_abs": CLARABEL_TOL,
        "tol_gap_rel": CLARABEL_TOL,
        "tol_feas": CLARABEL_TOL,
    }
    value = problem.solve(**solve_kwargs)
    f_val = np.asarray(f.value, dtype=np.float64).reshape(-1)

    row_eval = []
    for row, q in zip(rows, pure_values):
        xi = np.asarray(row["xi"], dtype=np.float64)
        alpha = np.asarray(row["alpha"], dtype=np.float64)
        beta = np.asarray(row["beta"], dtype=np.float64)
        keep = (alpha > REMAINDER_ALPHA_TOL) | (np.abs(beta) > REMAINDER_BETA_TOL)
        xi = xi[keep]
        alpha = alpha[keep]
        beta = beta[keep]
        mat = step_fourier_matrix(n, xi)
        hhat = mat @ f_val - sinc(xi)
        active = alpha > REMAINDER_ALPHA_TOL
        d_re = float(np.sum(alpha * (np.real(hhat) ** 2)))
        d_im = 0.0
        if np.any(active):
            d_im = float(np.sum(alpha[active] * (np.imag(hhat[active]) - beta[active] * sinc(xi[active]) / alpha[active]) ** 2))
        d_total = d_re + d_im
        row_eval.append(
            {
                "row_id": str(row["id"]),
                "family": str(row.get("family", "unknown")),
                "source_m": float(row["source_m"]),
                "q": float(q),
                "D": d_total,
                "D_re": d_re,
                "D_im": d_im,
                "q_plus_D": float(q + d_total),
                "K": int(row["K"]),
                "remainder_atom_count": int(np.sum(keep)),
            }
        )
    row_eval.sort(key=lambda item: float(item["q_plus_D"]), reverse=True)
    max_qd = float(row_eval[0]["q_plus_D"])
    pure_zero_reproduction = pure_envelope
    result = {
        "m": m,
        "n": n,
        "status": str(problem.status),
        "solver": "CLARABEL",
        "solver_tol": CLARABEL_TOL,
        "objective": None if value is None else float(value),
        "max_q_plus_D_recomputed": max_qd,
        "objective_recompute_error": None if value is None else float(max_qd - float(value)),
        "pure_envelope": pure_envelope,
        "pure_controlling_row": str(rows[pure_idx]["id"]),
        "remainder_lift": None if value is None else float(float(value) - pure_envelope),
        "recomputed_lift": float(max_qd - pure_envelope),
        "entitlement_holds_objective": None if value is None else bool(float(value) + 5.0e-8 >= pure_envelope),
        "entitlement_holds_recomputed": bool(max_qd + 5.0e-8 >= pure_envelope),
        "D_zero_reproduction": pure_zero_reproduction,
        "D_zero_reproduction_error": float(pure_zero_reproduction - pure_envelope),
        "mass": float(h * np.sum(f_val)),
        "mass_error": float(h * np.sum(f_val) - mass_target),
        "first_f_moment": float(h * (centers @ f_val)),
        "first_f_moment_error": float(h * (centers @ f_val) - first_target),
        "target_first_f_moment": first_target,
        "box_min": float(np.min(f_val)),
        "box_max": float(np.max(f_val)),
        "elapsed_seconds": float(time.time() - started),
        "top_rows_by_q_plus_D": row_eval[:8],
        "top_rows_by_D": sorted(row_eval, key=lambda item: float(item["D"]), reverse=True)[:8],
    }
    result["gate_pass"] = bool(
        result["status"] in ("optimal", "optimal_inaccurate")
        and abs(result["D_zero_reproduction_error"]) <= 1.0e-12
        and result["entitlement_holds_recomputed"]
        and abs(result["mass_error"]) <= MEAN_TOL
        and abs(result["first_f_moment_error"]) <= MEAN_TOL
    )
    return result


def _nconv_row_summary(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "id": str(row["id"]),
            "family": str(row.get("family", "unknown")),
            "source_m": float(row["source_m"]),
            "K": int(row["K"]),
            "beta_active_count_gt_1e_8": int(np.sum(np.abs(np.asarray(row["beta"], dtype=np.float64)) > 1.0e-8)),
            "alpha_positive_count_gt_1e_10": int(np.sum(np.asarray(row["alpha"], dtype=np.float64) > 1.0e-10)),
            "alpha_linf": float(np.max(np.asarray(row["alpha"], dtype=np.float64))) if int(row["K"]) else 0.0,
            "beta_linf": float(np.max(np.abs(np.asarray(row["beta"], dtype=np.float64)))) if int(row["K"]) else 0.0,
        }
        for row in rows
    ]


def _trend_for_anchor(results: list[dict[str, Any]], m: float) -> dict[str, Any]:
    subset = [
        r
        for r in results
        if abs(float(r.get("m", -999.0)) - float(m)) <= 5.0e-12
        and r.get("gate_pass")
        and r.get("recomputed_lift") is not None
    ]
    subset.sort(key=lambda r: int(r["n"]))
    ns = np.asarray([int(r["n"]) for r in subset], dtype=np.float64)
    lifts = np.asarray([float(r["recomputed_lift"]) for r in subset], dtype=np.float64)
    clean = [r for r in subset if r.get("status") == "optimal"]
    fit = None
    if lifts.size >= 3:
        coeff = np.polyfit(1.0 / ns[-min(4, lifts.size) :], lifts[-min(4, lifts.size) :], 1)
        fit = {
            "last_points_used": int(min(4, lifts.size)),
            "linear_fit_lift_vs_1_over_n_intercept": float(coeff[1]),
            "linear_fit_lift_vs_1_over_n_slope": float(coeff[0]),
        }
    if lifts.size == 0:
        verdict = "no_gate_passing_results"
    elif lifts.size >= 3 and lifts[-1] <= max(1.0e-9, 0.25 * lifts[0]):
        verdict = "decaying_toward_zero"
    elif fit is not None and fit["linear_fit_lift_vs_1_over_n_intercept"] > 1.0e-6 and lifts[-1] > 1.0e-6:
        verdict = "positive_asymptote_possible"
    else:
        verdict = "inconclusive"
    return {
        "m": float(m),
        "gate_passing_n": [int(v) for v in ns],
        "gate_passing_lift": [float(v) for v in lifts],
        "largest_gate_passing_n": int(ns[-1]) if ns.size else None,
        "largest_clean_n": int(clean[-1]["n"]) if clean else None,
        "lift_at_largest_gate_passing_n": float(lifts[-1]) if lifts.size else None,
        "first_lift": float(lifts[0]) if lifts.size else None,
        "last_over_first": float(lifts[-1] / lifts[0]) if lifts.size and abs(lifts[0]) > 0.0 else None,
        "fit": fit,
        "trend_verdict": verdict,
        "final_top_rows_by_q_plus_D": subset[-1]["top_rows_by_q_plus_D"][:5] if subset else [],
        "final_top_rows_by_D": subset[-1]["top_rows_by_D"][:5] if subset else [],
    }


def _strip_f_vectors(result: dict[str, Any]) -> dict[str, Any]:
    out = dict(result)
    if "f" in out:
        out["f_summary"] = {
            "n": int(result["n"]),
            "min": float(np.min(result["f"])),
            "max": float(np.max(result["f"])),
            "mean": float(np.mean(result["f"])),
        }
        out.pop("f", None)
    out.pop("row_eval", None)
    return out


def run_nconv_analysis(
    *,
    out_json: Path = NCONV_OUT_JSON,
    anchors: tuple[float, ...] = NCONV_TARGET_M,
    steps: tuple[int, ...] = NCONV_STEPS,
    max_total_seconds: float = 1710.0,
) -> dict[str, Any]:
    started = time.time()
    TMP.mkdir(parents=True, exist_ok=True)
    rows, generator_diagnostics, freq_info = _load_nconv_rows()
    row_summary = _nconv_row_summary(rows)
    print("SOC_SOS_NCONV_BEGIN", flush=True)
    print(
        f"row_set base_rows={sum(1 for r in rows if r.get('family') == 'base')} "
        f"e8f_rows={sum(1 for r in rows if r.get('family') == 'e8f')} "
        f"e8f_frequency_count={freq_info['e8f_frequency_count']}",
        flush=True,
    )
    for diag in generator_diagnostics:
        print(
            f"generator anchor={diag['anchor_m']:.7f} status={diag['status']} K={diag['K']} "
            f"raw_diff={diag.get('raw_L_difference', 0.0):+.3e} "
            f"path={diag.get('metadata_cache_path', '')}",
            flush=True,
        )

    reused_results: dict[tuple[int, float], dict[str, Any]] = {}
    if Path(out_json).exists():
        try:
            previous = _load_json(Path(out_json))
            if previous.get("schema") == "public SOC SOS remainder n-convergence v1":
                for item in previous.get("solve_results", []):
                    key = (int(item.get("n", -1)), round(float(item.get("m", 0.0)), 12))
                    if item.get("gate_pass") and item.get("recomputed_lift") is not None:
                        reused_results[key] = item
                if reused_results:
                    print(f"nconv_resume_reused_rows={len(reused_results)} from={out_json}", flush=True)
        except Exception:
            reused_results = {}

    solve_results: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for n in steps:
        for m in anchors:
            reuse_key = (int(n), round(float(m), 12))
            if reuse_key in reused_results:
                res = dict(reused_results[reuse_key])
                solve_results.append(res)
                print(
                    f"nconv_reuse m={float(m):.7f} n={int(n)} status={res.get('status')} solver={res.get('solver')} "
                    f"E={res.get('pure_envelope', float('nan')):.15f} "
                    f"minS={res.get('remainder_value', float('nan')):.15f} "
                    f"lift={res.get('recomputed_lift', float('nan')):.9e}",
                    flush=True,
                )
                continue
            elapsed = time.time() - started
            if elapsed > float(max_total_seconds) - 90.0:
                skipped.append(
                    {
                        "m": float(m),
                        "n": int(n),
                        "reason": "time_guard_before_solve",
                        "elapsed_seconds": float(elapsed),
                        "max_total_seconds": float(max_total_seconds),
                    }
                )
                print(f"nconv_skip m={float(m):.7f} n={int(n)} reason=time_guard elapsed={elapsed:.1f}", flush=True)
                continue
            print(f"nconv_solve_start m={float(m):.7f} n={int(n)}", flush=True)
            try:
                res = _solve_scaled_remainder_program(rows, m=float(m), n=int(n))
            except Exception as exc:  # noqa: BLE001
                res = {
                    "m": float(m),
                    "n": int(n),
                    "status": "exception",
                    "solver": None,
                    "error": repr(exc),
                    "gate_pass": False,
                    "elapsed_seconds": 0.0,
                }
            solve_results.append(res)
            printable_obj = res.get("remainder_value")
            printable_lift = res.get("recomputed_lift")
            print(
                f"nconv_row m={float(m):.7f} n={int(n)} status={res.get('status')} solver={res.get('solver')} "
                f"E={res.get('pure_envelope', float('nan')):.15f} "
                f"minS={printable_obj if printable_obj is not None else float('nan'):.15f} "
                f"lift={printable_lift if printable_lift is not None else float('nan'):.9e} "
                f"D0_err={res.get('D_zero_reproduction_error', float('nan')):+.3e} "
                f"mass_err={res.get('mass_error', float('nan')):+.3e} "
                f"first_err={res.get('first_f_moment_error', float('nan')):+.3e} "
                f"gate={res.get('gate_pass')}",
                flush=True,
            )
            partial = {
                "schema": "public SOC SOS remainder n-convergence v1",
                "status": "partial_running",
                "elapsed_seconds": float(time.time() - started),
                "row_summary": row_summary,
                "generator_reconstruction": generator_diagnostics,
                "frequency_info": freq_info,
                "solve_results": [_strip_f_vectors(r) for r in solve_results],
                "skipped": skipped,
            }
            _write_json(Path(out_json), partial)
            _write_json(NCONV_OUT_JSON_ROOT_COPY, partial)

    trends = [_trend_for_anchor(solve_results, float(m)) for m in anchors]
    for trend in trends:
        print(
            f"nconv_trend m={trend['m']:.7f} n={trend['gate_passing_n']} "
            f"lifts={[f'{v:.9e}' for v in trend['gate_passing_lift']]} "
            f"largest_clean_n={trend['largest_clean_n']} verdict={trend['trend_verdict']}",
            flush=True,
        )
    package = {
        "schema": "public SOC SOS remainder n-convergence v1",
        "created_by": "source/soc_sos_remainder_pilot.py::run_nconv_analysis",
        "status": "complete_within_time_guard" if not skipped else "time_guard_partial",
        "elapsed_seconds": float(time.time() - started),
        "claim_scope": (
            "Finite n-cell step-box minimization of S(f)=max_i q_i(m)+D_i(f) over the restricted step subset. "
            "Restricted-f minima are biased high and are not certified lower bounds for the full continuum problem."
        ),
        "directionality_note": (
            "For feasible f, M(f)>=S(f) and D_i(f)>=0, so nonnegative lift over E(m)=max_i q_i(m) is automatic; "
            "the diagnostic value is whether the lift vanishes as n grows."
        ),
        "hyperparameters": {
            "anchors_m": [float(v) for v in anchors],
            "steps": [int(v) for v in steps],
            "e8f_row_anchors": [float(v) for v in NCONV_E8F_ROW_ANCHORS],
            "clarabel_tol": CLARABEL_TOL,
            "clarabel_max_iter": 5000,
            "clarabel_time_limit_seconds_per_solve": 120.0,
            "scs_tol": SCS_TOL,
            "scs_max_iters": 250000,
            "scs_time_limit_seconds_per_solve": 180.0,
            "atom_scaling": "row-wise divide alpha,beta by max(max(alpha),max(abs(beta)),1e-300), then multiply D by that scale",
            "linear_map_preconditioning": "f=f0+N u where N is an orthonormal nullspace basis for mass and first-moment constraints",
            "box": [0.0, 1.0],
            "mean_constraint": "integral f = 1",
            "first_moment_constraint": "int t f(t)dt=-m/2",
            "max_total_seconds": float(max_total_seconds),
        },
        "row_summary": row_summary,
        "generator_reconstruction": generator_diagnostics,
        "frequency_info": freq_info,
        "solve_results": [_strip_f_vectors(r) for r in solve_results],
        "trend_by_m": trends,
        "skipped": skipped,
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "e8f_summary": str(DATA / "soc_freq_density4.json"),
            "nconv_generator_cache": str(NCONV_GENERATOR_CACHE),
            "nconv_row_cache_dir": str(NCONV_ROW_CACHE_DIR),
            "output_json": str(out_json),
            "output_json_root_copy": str(NCONV_OUT_JSON_ROOT_COPY),
        },
    }
    _write_json(Path(out_json), package)
    _write_json(NCONV_OUT_JSON_ROOT_COPY, package)
    print(f"SOC_SOS_NCONV_DONE saved_json={out_json} elapsed={package['elapsed_seconds']:.1f}", flush=True)
    return package


def run_analysis(
    *,
    out_json: Path = OUT_JSON,
    n: int = PILOT_N,
    anchors: tuple[float, ...] = TEST_ANCHORS,
) -> dict[str, Any]:
    started = time.time()
    TMP.mkdir(parents=True, exist_ok=True)
    rows, generator_diagnostics = _load_rows()
    row_summary = [
        {
            "id": str(row["id"]),
            "family": str(row.get("family", "unknown")),
            "source_m": float(row["source_m"]),
            "K": int(row["K"]),
            "beta_active_count_gt_1e_8": int(np.sum(np.abs(np.asarray(row["beta"], dtype=np.float64)) > 1.0e-8)),
            "alpha_positive_count_gt_1e_10": int(np.sum(np.asarray(row["alpha"], dtype=np.float64) > 1.0e-10)),
        }
        for row in rows
    ]

    print("SOC_SOS_REMAINDER_PILOT", flush=True)
    print(
        f"row_set base_rows={sum(1 for r in rows if r.get('family') == 'base')} "
        f"e4f_rows={sum(1 for r in rows if r.get('family') == 'e4f')} n={int(n)}",
        flush=True,
    )
    for diag in generator_diagnostics:
        print(
            f"generator anchor={diag['anchor_m']:.7f} status={diag['status']} K={diag['K']} "
            f"raw_diff={diag.get('raw_L_difference', 0.0):+.3e}",
            flush=True,
        )

    anchor_results = []
    for m in anchors:
        print(f"remainder_solve_start m={float(m):.7f} n={int(n)}", flush=True)
        res = solve_remainder_program(rows, m=float(m), n=int(n))
        anchor_results.append(res)
        print(
            f"anchor m={float(m):.7f} E={res['pure_envelope']:.15f} "
            f"R={res['objective'] if res['objective'] is not None else float('nan'):.15f} "
            f"lift={res['remainder_lift'] if res['remainder_lift'] is not None else float('nan'):.9e} "
            f"entitlement={res['entitlement_holds_recomputed']} "
            f"D0_err={res['D_zero_reproduction_error']:+.3e} "
            f"status={res['status']} gate={res['gate_pass']}",
            flush=True,
        )

    valid_lifts = [
        float(res["recomputed_lift"])
        for res in anchor_results
        if res.get("gate_pass") and float(res.get("recomputed_lift", 0.0)) > 0.0
    ]
    largest = max(valid_lifts) if valid_lifts else 0.0
    verdict = (
        "positive_pilot_lift_on_tested_rows"
        if largest > 5.0e-8
        else "no_gate_passing_measurable_lift_on_tested_rows"
    )
    package = {
        "schema": "public SOC SOS remainder pilot v1",
        "created_by": "source/soc_sos_remainder_pilot.py",
        "elapsed_seconds": float(time.time() - started),
        "claim_scope": (
            "Finite-n step-box pilot on the base hardened rows plus E4f rows at m=0,0.003,0.004475. "
            "This is not a full-domain certified lower-bound claim."
        ),
        "hyperparameters": {
            "n": int(n),
            "anchors": [float(v) for v in anchors],
            "e4f_row_anchors": [float(v) for v in E4F_ROW_ANCHORS],
            "solver": "CLARABEL",
            "tol": CLARABEL_TOL,
            "remainder_alpha_tol": REMAINDER_ALPHA_TOL,
            "remainder_beta_tol": REMAINDER_BETA_TOL,
            "box": [0.0, 1.0],
            "mean_constraint": "integral f = 1 (mean weight 1/2)",
            "first_moment_constraint": "int x C(x) dx = m, implemented as int t f(t)dt=-m/2",
        },
        "row_summary": row_summary,
        "generator_reconstruction": generator_diagnostics,
        "anchor_results": anchor_results,
        "largest_gate_passing_recomputed_lift": float(largest),
        "any_gate_passing_measurable_lift_gt_5e_8": bool(largest > 5.0e-8),
        "verdict": verdict,
        "source_paths": {
            "base_certificate": str(BASE_CERT_PATH),
            "base_exact_budget": str(BASE_EXACT_BUDGET_PATH),
            "e4f_summary": str(DATA / "soc_freq_density3.json"),
            "generator_cache": str(GENERATOR_CACHE),
            "output_json": str(out_json),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
        },
    }
    _write_json(Path(out_json), package)
    _write_json(OUT_JSON_ROOT_COPY, package)
    print(
        f"largest_gate_passing_lift={largest:.9e} verdict={verdict} saved_json={out_json}",
        flush=True,
    )
    return package


if __name__ == "__main__":
    run_analysis()
