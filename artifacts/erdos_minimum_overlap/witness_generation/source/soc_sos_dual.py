"""Continuum dual pilot for the SOC completion-of-squares remainder.

The finite-n SOS remainder pilots minimized over a restricted step family, so
their values were biased high.  This module instead builds explicit dual
minorants for

    inf_{0<=f<=1, int f=1, int t f=-m/2} max_i q_i(m)+D_i(f)

at a few fixed means.  The optimizer is only a search heuristic; the reported
value is obtained by re-evaluating the final dual point with a conservative
continuous positive-part integral bound on [-1,1].
"""

from __future__ import annotations

import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, "source")

import soc_sos_remainder_pilot as pilot  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
OUT_JSON = DATA / "soc_sos_dual.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_sos_dual.json"
E8F_HEADLINE = 0.38054994359516015

ANCHORS = (0.0, 0.0026, 0.003)
ACTIVE_ROW_COUNT = 6
TERM_LIMIT = 220
OPT_GRID_N = 6001
CERT_PARTITIONS = 240_000
CLARABEL_TOL = 1.0e-8
FINITE_PRIMAL_N = 256
REMAINDER_ALPHA_TOL = pilot.REMAINDER_ALPHA_TOL
REMAINDER_BETA_TOL = pilot.REMAINDER_BETA_TOL


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


@dataclass
class TermPack:
    row_indices: np.ndarray
    xi: np.ndarray
    alpha: np.ndarray
    shift: np.ndarray
    kind: np.ndarray
    residual: np.ndarray
    contribution: np.ndarray
    selected_from_total: int


def _row_value(row: dict[str, Any], m: float) -> float:
    return pilot._row_value(row, float(m))


def _active_rows_from_primal(rows: list[dict[str, Any]], primal: dict[str, Any], m: float) -> list[int]:
    by_id = {str(row["id"]): i for i, row in enumerate(rows)}
    active: list[int] = []
    for item in primal.get("top_rows_by_q_plus_D", []):
        idx = by_id.get(str(item["row_id"]))
        if idx is not None and idx not in active:
            active.append(idx)
        if len(active) >= ACTIVE_ROW_COUNT:
            break
    if len(active) < ACTIVE_ROW_COUNT:
        q = np.asarray([_row_value(row, m) for row in rows], dtype=np.float64)
        for idx in np.argsort(q)[::-1]:
            ii = int(idx)
            if ii not in active:
                active.append(ii)
            if len(active) >= ACTIVE_ROW_COUNT:
                break
    return active


def _evaluate_row_terms(row: dict[str, Any], f: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    xi = np.asarray(row["xi"], dtype=np.float64)
    alpha = np.asarray(row["alpha"], dtype=np.float64)
    beta = np.asarray(row["beta"], dtype=np.float64)
    keep = (alpha > REMAINDER_ALPHA_TOL) | (np.abs(beta) > REMAINDER_BETA_TOL)
    xi = xi[keep]
    alpha = np.maximum(alpha[keep], 0.0)
    beta = beta[keep]
    mat = pilot.step_fourier_matrix(int(f.size), xi)
    hhat = mat @ f - sinc(xi)
    re_resid = np.real(hhat)
    re_shift = sinc(xi)
    re_kind = np.zeros(xi.size, dtype=np.int8)
    pos = alpha > REMAINDER_ALPHA_TOL
    im_xi = xi[pos]
    im_alpha = alpha[pos]
    im_shift = beta[pos] * sinc(im_xi) / im_alpha
    im_resid = np.imag(hhat[pos]) - im_shift
    im_kind = np.ones(im_xi.size, dtype=np.int8)
    return (
        np.concatenate([xi, im_xi]),
        np.concatenate([alpha, im_alpha]),
        np.concatenate([re_shift, im_shift]),
        np.concatenate([re_kind, im_kind]),
        np.concatenate([re_resid, im_resid]),
    )


def _build_term_pack(
    rows: list[dict[str, Any]],
    active_indices: list[int],
    lambdas: np.ndarray,
    f_ref: np.ndarray,
    *,
    term_limit: int,
) -> TermPack:
    row_ids: list[int] = []
    xis: list[np.ndarray] = []
    alphas: list[np.ndarray] = []
    shifts: list[np.ndarray] = []
    kinds: list[np.ndarray] = []
    residuals: list[np.ndarray] = []
    contribs: list[np.ndarray] = []
    for local_idx, row_idx in enumerate(active_indices):
        lam = float(lambdas[local_idx])
        if lam <= 0.0:
            continue
        xi, alpha, shift, kind, resid = _evaluate_row_terms(rows[row_idx], f_ref)
        c = lam * alpha
        good = c > 1.0e-18
        if not np.any(good):
            continue
        xi = xi[good]
        alpha = alpha[good]
        shift = shift[good]
        kind = kind[good]
        resid = resid[good]
        contrib = c[good] * resid * resid
        row_ids.extend([row_idx] * int(xi.size))
        xis.append(xi)
        alphas.append(alpha)
        shifts.append(shift)
        kinds.append(kind)
        residuals.append(resid)
        contribs.append(contrib)
    if not xis:
        return TermPack(
            row_indices=np.zeros(0, dtype=np.int32),
            xi=np.zeros(0),
            alpha=np.zeros(0),
            shift=np.zeros(0),
            kind=np.zeros(0, dtype=np.int8),
            residual=np.zeros(0),
            contribution=np.zeros(0),
            selected_from_total=0,
        )
    xi_all = np.concatenate(xis)
    alpha_all = np.concatenate(alphas)
    shift_all = np.concatenate(shifts)
    kind_all = np.concatenate(kinds)
    resid_all = np.concatenate(residuals)
    contrib_all = np.concatenate(contribs)
    total = int(xi_all.size)
    take = np.argsort(contrib_all)[::-1][: min(int(term_limit), total)]
    return TermPack(
        row_indices=np.asarray(row_ids, dtype=np.int32)[take],
        xi=xi_all[take],
        alpha=alpha_all[take],
        shift=shift_all[take],
        kind=kind_all[take],
        residual=resid_all[take],
        contribution=contrib_all[take],
        selected_from_total=total,
    )


def _kernel_matrix(t: np.ndarray, terms: TermPack) -> np.ndarray:
    if terms.xi.size == 0:
        return np.zeros((t.size, 0), dtype=np.float64)
    arg = t[:, None] * terms.xi[None, :]
    k = np.cos(arg)
    im = terms.kind.astype(bool)
    if np.any(im):
        k[:, im] = -np.sin(arg[:, im])
    return k


def _soft_min_and_prob(phi: np.ndarray, eps: float) -> tuple[np.ndarray, np.ndarray]:
    z = -phi / float(eps)
    out = -float(eps) * np.logaddexp(0.0, z)
    prob = 1.0 / (1.0 + np.exp(-np.clip(z, -60.0, 60.0)))
    return out, prob


def _approx_objective_factory(
    *,
    q_const: float,
    first_target: float,
    lambdas_by_global_row: np.ndarray,
    terms: TermPack,
    grid_n: int,
) -> tuple[Any, np.ndarray]:
    t = -1.0 + (np.arange(int(grid_n), dtype=np.float64) + 0.5) * (2.0 / float(grid_n))
    h = 2.0 / float(grid_n)
    k_mat = _kernel_matrix(t, terms)
    c = lambdas_by_global_row[terms.row_indices] * terms.alpha
    inv_c = 1.0 / c
    shift = terms.shift

    def fun_grad(x: np.ndarray) -> tuple[float, np.ndarray]:
        y = x[:-2]
        eta0 = float(x[-2])
        eta1 = float(x[-1])
        phi = eta0 + eta1 * t
        if y.size:
            phi = phi + 2.0 * (k_mat @ y)
        sm, prob = _soft_min_and_prob(phi, 1.0e-6)
        val = (
            float(q_const)
            - float(np.sum(y * y * inv_c))
            - 2.0 * float(y @ shift)
            - eta0
            - eta1 * float(first_target)
            + h * float(np.sum(sm))
        )
        grad_y = -2.0 * y * inv_c - 2.0 * shift
        if y.size:
            grad_y += 2.0 * h * (k_mat.T @ prob)
        grad_eta0 = -1.0 + h * float(np.sum(prob))
        grad_eta1 = -float(first_target) + h * float(t @ prob)
        grad = np.concatenate([grad_y, np.asarray([grad_eta0, grad_eta1])])
        return -val, -grad

    return fun_grad, t


def _field_values(t: np.ndarray, terms: TermPack, y: np.ndarray, eta0: float, eta1: float, *, chunk: int = 4096) -> np.ndarray:
    out = np.empty_like(t, dtype=np.float64)
    for start in range(0, t.size, int(chunk)):
        stop = min(t.size, start + int(chunk))
        ts = t[start:stop]
        phi = eta0 + eta1 * ts
        if y.size:
            phi = phi + 2.0 * (_kernel_matrix(ts, terms) @ y)
        out[start:stop] = phi
    return out


def _positive_upper_bound_for_minus_field(terms: TermPack, y: np.ndarray, eta0: float, eta1: float, *, partitions: int) -> dict[str, float]:
    h = 2.0 / float(partitions)
    t = -1.0 + (np.arange(int(partitions), dtype=np.float64) + 0.5) * h
    phi = _field_values(t, terms, y, eta0, eta1)
    psi_mid = -phi
    if y.size:
        cos_coeff = np.zeros_like(y)
        sin_coeff = np.zeros_like(y)
        real = terms.kind == 0
        imag = ~real
        cos_coeff[real] = -2.0 * y[real]
        sin_coeff[imag] = 2.0 * y[imag]
        deriv_sup = abs(float(eta1)) + float(np.sum(np.abs(terms.xi * cos_coeff) + np.abs(terms.xi * sin_coeff)))
        scale = 1.0 + abs(float(eta0)) + abs(float(eta1)) + float(np.sum(np.abs(cos_coeff) + np.abs(sin_coeff)))
    else:
        deriv_sup = abs(float(eta1))
        scale = 1.0 + abs(float(eta0)) + abs(float(eta1))
    pad = 5.0e-14 * scale
    cell_sup = psi_mid + 0.5 * deriv_sup * h + pad
    return {
        "method": "midpoint_lipschitz_positive_part_upper",
        "partitions": int(partitions),
        "spacing": float(h),
        "derivative_sup": float(deriv_sup),
        "eval_pad": float(pad),
        "positive_integral_upper": float(h * np.sum(np.maximum(cell_sup, 0.0), dtype=np.float64)),
        "mesh_positive_integral": float(h * np.sum(np.maximum(psi_mid, 0.0), dtype=np.float64)),
        "psi_mid_min": float(np.min(psi_mid)),
        "psi_mid_max": float(np.max(psi_mid)),
    }


def _dual_value_certificate(
    *,
    q_const: float,
    first_target: float,
    lambdas_by_global_row: np.ndarray,
    terms: TermPack,
    y: np.ndarray,
    eta0: float,
    eta1: float,
    partitions: int,
) -> dict[str, Any]:
    if y.size:
        c = lambdas_by_global_row[terms.row_indices] * terms.alpha
        penalty = float(np.sum((y * y) / c))
        shift_linear = float(2.0 * (y @ terms.shift))
    else:
        penalty = 0.0
        shift_linear = 0.0
    base_without_box = float(q_const - penalty - shift_linear - eta0 - eta1 * float(first_target))
    pos = _positive_upper_bound_for_minus_field(terms, y, float(eta0), float(eta1), partitions=int(partitions))
    value = float(base_without_box - pos["positive_integral_upper"])
    return {
        "certified_value_lower": value,
        "base_without_box_integral": base_without_box,
        "quadratic_conjugate_penalty": penalty,
        "shift_linear_term": shift_linear,
        "eta0": float(eta0),
        "eta1": float(eta1),
        "positive_part": pos,
    }


def _lambda_schemes(active_count: int) -> list[tuple[str, np.ndarray]]:
    schemes: list[tuple[str, np.ndarray]] = []
    for i in range(active_count):
        v = np.zeros(active_count, dtype=np.float64)
        v[i] = 1.0
        schemes.append((f"onehot_{i}", v))
    for k in range(2, active_count + 1):
        v = np.zeros(active_count, dtype=np.float64)
        v[:k] = 1.0 / float(k)
        schemes.append((f"uniform_top{k}", v))
    if active_count >= 4:
        v = np.zeros(active_count, dtype=np.float64)
        weights = np.asarray([0.40, 0.25, 0.20, 0.15], dtype=np.float64)
        v[:4] = weights / float(np.sum(weights))
        schemes.append(("front_loaded_top4", v))
    return schemes


def _optimize_scheme(
    *,
    rows: list[dict[str, Any]],
    active_indices: list[int],
    lambdas_local: np.ndarray,
    f_ref: np.ndarray,
    m: float,
    scheme_name: str,
    term_limit: int,
) -> dict[str, Any]:
    first_target = -0.5 * float(m)
    q_values = np.asarray([_row_value(row, m) for row in rows], dtype=np.float64)
    lambdas_by_row = np.zeros(len(rows), dtype=np.float64)
    for local_idx, row_idx in enumerate(active_indices):
        lambdas_by_row[row_idx] = float(lambdas_local[local_idx])
    q_const = float(lambdas_by_row @ q_values)
    terms = _build_term_pack(rows, active_indices, lambdas_local, f_ref, term_limit=int(term_limit))
    fun_grad, _ = _approx_objective_factory(
        q_const=q_const,
        first_target=first_target,
        lambdas_by_global_row=lambdas_by_row,
        terms=terms,
        grid_n=OPT_GRID_N,
    )
    c = lambdas_by_row[terms.row_indices] * terms.alpha if terms.xi.size else np.zeros(0)
    tangent = c * terms.residual
    starts: list[np.ndarray] = []
    for scale in (0.0, 0.25, 0.5, 1.0):
        starts.append(np.concatenate([scale * tangent, np.zeros(2, dtype=np.float64)]))
    attempts: list[dict[str, Any]] = []
    for start_idx, x0 in enumerate(starts):
        t0 = time.time()
        res = minimize(
            lambda x: fun_grad(x),
            x0,
            method="L-BFGS-B",
            jac=True,
            options={"maxiter": 500, "ftol": 1.0e-13, "gtol": 1.0e-9, "maxls": 40},
        )
        attempts.append(
            {
                "start_index": int(start_idx),
                "optimizer_success": bool(res.success),
                "optimizer_status": int(res.status),
                "optimizer_message": str(res.message),
                "optimizer_fun": float(res.fun),
                "optimizer_elapsed_seconds": float(time.time() - t0),
                "x": np.asarray(res.x, dtype=np.float64),
            }
        )
    best_attempt = min(attempts, key=lambda item: item["optimizer_fun"])
    y = np.asarray(best_attempt["x"][:-2], dtype=np.float64)
    eta0 = float(best_attempt["x"][-2])
    eta1 = float(best_attempt["x"][-1])
    cert = _dual_value_certificate(
        q_const=q_const,
        first_target=first_target,
        lambdas_by_global_row=lambdas_by_row,
        terms=terms,
        y=y,
        eta0=eta0,
        eta1=eta1,
        partitions=CERT_PARTITIONS,
    )
    best = {
        "scheme": scheme_name,
        "start_index": int(best_attempt["start_index"]),
        "optimizer_success": bool(best_attempt["optimizer_success"]),
        "optimizer_status": int(best_attempt["optimizer_status"]),
        "optimizer_message": str(best_attempt["optimizer_message"]),
        "optimizer_fun": float(best_attempt["optimizer_fun"]),
        "optimizer_elapsed_seconds": float(sum(a["optimizer_elapsed_seconds"] for a in attempts)),
        "start_attempts": [
            {
                "start_index": int(a["start_index"]),
                "optimizer_success": bool(a["optimizer_success"]),
                "optimizer_status": int(a["optimizer_status"]),
                "optimizer_fun": float(a["optimizer_fun"]),
                "optimizer_elapsed_seconds": float(a["optimizer_elapsed_seconds"]),
            }
            for a in attempts
        ],
        "q_const": q_const,
        "lambda_local": lambdas_local,
        "lambda_by_row": lambdas_by_row,
        "active_row_ids": [str(rows[i]["id"]) for i in active_indices],
        "term_count": int(terms.xi.size),
        "terms_selected_from_total": int(terms.selected_from_total),
        "selected_term_contribution_sum": float(np.sum(terms.contribution)),
        "selected_term_contribution_max": float(np.max(terms.contribution)) if terms.contribution.size else 0.0,
        "dual_y": y,
        "term_pack": {
            "row_indices": terms.row_indices,
            "xi": terms.xi,
            "alpha": terms.alpha,
            "shift": terms.shift,
            "kind": terms.kind,
            "residual": terms.residual,
            "contribution": terms.contribution,
            "selected_from_total": int(terms.selected_from_total),
        },
        "y_l2": float(np.linalg.norm(y)),
        "y_linf": float(np.max(np.abs(y))) if y.size else 0.0,
        "certification": cert,
    }
    keep = np.argsort(terms.contribution)[::-1][:10] if terms.contribution.size else np.zeros(0, dtype=np.int64)
    best["top_selected_terms"] = [
        {
            "row_id": str(rows[int(terms.row_indices[j])]["id"]),
            "xi": float(terms.xi[j]),
            "kind": "imag" if int(terms.kind[j]) else "real",
            "alpha": float(terms.alpha[j]),
            "shift": float(terms.shift[j]),
            "residual": float(terms.residual[j]),
            "finite_primal_contribution_weighted": float(terms.contribution[j]),
        }
        for j in keep
    ]
    return best


def _load_or_solve_primal(rows: list[dict[str, Any]], m: float, *, max_seconds_left: float) -> dict[str, Any]:
    nconv = pilot.NCONV_OUT_JSON
    if nconv.exists():
        try:
            data = _load_json(nconv)
            for item in data.get("solve_results", []):
                if int(item.get("n", -1)) == FINITE_PRIMAL_N and abs(float(item.get("m", -9.0)) - float(m)) <= 5.0e-12:
                    out = dict(item)
                    out["source"] = str(nconv)
                    out["contains_f_vector"] = False
                    return out
        except Exception:
            pass
    if max_seconds_left < 150.0:
        raise RuntimeError(f"not enough time left to solve n={FINITE_PRIMAL_N} primal for m={m}")
    res = pilot._solve_scaled_remainder_program(rows, m=float(m), n=FINITE_PRIMAL_N)
    res["source"] = "fresh_solve_in_soc_sos_dual"
    res["contains_f_vector"] = True
    return res


def _ensure_primal_with_f(rows: list[dict[str, Any]], m: float, cached_or_fresh: dict[str, Any]) -> dict[str, Any]:
    if cached_or_fresh.get("contains_f_vector") and "f" in cached_or_fresh:
        return cached_or_fresh
    # The previous JSON intentionally strips f.  Re-solve only when needed for
    # the tangent direction; cached values still provide the reported sandwich.
    res = pilot._solve_scaled_remainder_program(rows, m=float(m), n=FINITE_PRIMAL_N)
    res["source"] = "fresh_resolve_for_dual_tangent"
    res["contains_f_vector"] = True
    return res


def _strip_primal(primal: dict[str, Any]) -> dict[str, Any]:
    out = dict(primal)
    if "f" in out:
        f = np.asarray(out.pop("f"), dtype=np.float64)
        out["f_summary"] = {
            "n": int(f.size),
            "min": float(np.min(f)),
            "max": float(np.max(f)),
            "mean": float(np.mean(f)),
        }
    out.pop("row_eval", None)
    return _jsonify(out)


def solve_anchor(rows: list[dict[str, Any]], *, m: float, started: float, max_total_seconds: float) -> dict[str, Any]:
    q = np.asarray([_row_value(row, m) for row in rows], dtype=np.float64)
    pure_envelope = float(np.max(q))
    pure_controller = str(rows[int(np.argmax(q))]["id"])
    cached_primal = _load_or_solve_primal(rows, float(m), max_seconds_left=max_total_seconds - (time.time() - started))
    primal = _ensure_primal_with_f(rows, float(m), cached_primal)
    f_ref = np.asarray(primal["f"], dtype=np.float64)
    active_indices = _active_rows_from_primal(rows, primal, float(m))
    print(
        f"sos_dual_anchor m={float(m):.7f} E={pure_envelope:.15f} "
        f"controller={pure_controller} active={[str(rows[i]['id']) for i in active_indices]}",
        flush=True,
    )
    scheme_results: list[dict[str, Any]] = []
    for scheme_name, lambdas in _lambda_schemes(len(active_indices)):
        if time.time() - started > max_total_seconds - 120.0:
            print(f"sos_dual_scheme_skip m={float(m):.7f} scheme={scheme_name} reason=time_guard", flush=True)
            continue
        res = _optimize_scheme(
            rows=rows,
            active_indices=active_indices,
            lambdas_local=lambdas,
            f_ref=f_ref,
            m=float(m),
            scheme_name=scheme_name,
            term_limit=TERM_LIMIT,
        )
        scheme_results.append(res)
        print(
            f"sos_dual_scheme m={float(m):.7f} scheme={scheme_name} "
            f"cert={res['certification']['certified_value_lower']:.15f} "
            f"lift={res['certification']['certified_value_lower'] - pure_envelope:+.9e} "
            f"terms={res['term_count']} y_linf={res['y_linf']:.3e}",
            flush=True,
        )
    best_raw = max(
        (r["certification"]["certified_value_lower"] for r in scheme_results),
        default=-float("inf"),
    )
    # The zero-remainder conjugate point is always dual-feasible and exactly
    # reproduces E(m).  Use it whenever heuristic nonzero points do not certify
    # entitlement after conservative continuous verification.
    certified_value = max(pure_envelope, float(best_raw))
    best = max(scheme_results, key=lambda r: r["certification"]["certified_value_lower"], default=None)
    lift = certified_value - pure_envelope
    primal_upper = float(primal.get("recomputed_lift", 0.0)) + float(primal["pure_envelope"])
    return {
        "m": float(m),
        "pure_envelope_E": pure_envelope,
        "pure_controller_row": pure_controller,
        "certified_dual_value_Dstar": float(certified_value),
        "certified_lift": float(lift),
        "best_nonzero_dual_value_before_entitlement_floor": None if best is None else float(best["certification"]["certified_value_lower"]),
        "entitlement_holds": bool(certified_value + 1.0e-12 >= pure_envelope),
        "exceeds_e8f_headline": bool(certified_value > E8F_HEADLINE),
        "finite_n_primal_upper": primal_upper,
        "finite_n_primal_lift": float(primal.get("recomputed_lift", primal_upper - pure_envelope)),
        "primal_dual_sandwich_width": float(primal_upper - certified_value),
        "dual_le_primal_n256": bool(certified_value <= primal_upper + 5.0e-8),
        "active_rows": [
            {
                "index": int(i),
                "id": str(rows[i]["id"]),
                "family": str(rows[i].get("family", "unknown")),
                "source_m": float(rows[i]["source_m"]),
                "q_at_m": float(q[i]),
                "K": int(rows[i]["K"]),
            }
            for i in active_indices
        ],
        "finite_primal_n256": _strip_primal(primal),
        "scheme_count": int(len(scheme_results)),
        "best_scheme": None if best is None else _jsonify(best),
        "scheme_summaries": [
            {
                "scheme": str(r["scheme"]),
                "certified_value_lower": float(r["certification"]["certified_value_lower"]),
                "lift_vs_E": float(r["certification"]["certified_value_lower"] - pure_envelope),
                "term_count": int(r["term_count"]),
                "optimizer_success": bool(r["optimizer_success"]),
                "eta0": float(r["certification"]["eta0"]),
                "eta1": float(r["certification"]["eta1"]),
                "positive_integral_upper": float(r["certification"]["positive_part"]["positive_integral_upper"]),
            }
            for r in sorted(scheme_results, key=lambda x: x["certification"]["certified_value_lower"], reverse=True)[:12]
        ],
    }


def run_dual_analysis(
    *,
    out_json: Path = OUT_JSON,
    anchors: tuple[float, ...] = ANCHORS,
    max_total_seconds: float = 1680.0,
) -> dict[str, Any]:
    started = time.time()
    rows, generator_diagnostics, freq_info = pilot._load_nconv_rows()
    print("SOC_SOS_DUAL_BEGIN", flush=True)
    print(
        f"row_set total={len(rows)} base={sum(1 for r in rows if r.get('family') == 'base')} "
        f"e8f={sum(1 for r in rows if r.get('family') == 'e8f')} term_limit={TERM_LIMIT}",
        flush=True,
    )
    anchor_results: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for m in anchors:
        if time.time() - started > max_total_seconds - 240.0:
            skipped.append({"m": float(m), "reason": "time_guard_before_anchor"})
            continue
        try:
            res = solve_anchor(rows, m=float(m), started=started, max_total_seconds=max_total_seconds)
        except Exception as exc:  # noqa: BLE001
            res = {
                "m": float(m),
                "status": "exception",
                "error": repr(exc),
                "pure_envelope_E": float(max(_row_value(row, float(m)) for row in rows)),
                "certified_dual_value_Dstar": float(max(_row_value(row, float(m)) for row in rows)),
                "certified_lift": 0.0,
                "entitlement_holds": True,
            }
        anchor_results.append(res)
        print(
            f"sos_dual_anchor_result m={float(m):.7f} E={res['pure_envelope_E']:.15f} "
            f"Dstar={res['certified_dual_value_Dstar']:.15f} "
            f"lift={res['certified_lift']:.9e} "
            f"primal_upper={res.get('finite_n_primal_upper', float('nan')):.15f} "
            f"width={res.get('primal_dual_sandwich_width', float('nan')):.9e} "
            f"entitlement={res['entitlement_holds']}",
            flush=True,
        )
        partial = {
            "schema": "public SOC SOS continuum dual pilot v1",
            "status": "partial_running",
            "elapsed_seconds": float(time.time() - started),
            "anchor_results": anchor_results,
            "skipped": skipped,
        }
        _write_json(Path(out_json), partial)
        _write_json(OUT_JSON_ROOT_COPY, partial)
    valid = [r for r in anchor_results if r.get("entitlement_holds")]
    largest_lift = max((float(r.get("certified_lift", 0.0)) for r in valid), default=0.0)
    min_cert = min((float(r["certified_dual_value_Dstar"]) for r in valid), default=float("nan"))
    positive = largest_lift > 1.0e-10
    package = {
        "schema": "public SOC SOS continuum dual pilot v1",
        "created_by": "source/soc_sos_dual.py::run_dual_analysis",
        "status": "complete_within_time_guard" if not skipped else "time_guard_partial",
        "elapsed_seconds": float(time.time() - started),
        "claim_scope": (
            "Fixed-anchor continuum box dual pilot using base + E8f controller rows. "
            "Only the tested means are covered; this is not a full-domain outside-exclusion certificate."
        ),
        "directionality_note": (
            "Every nonzero reported candidate is re-evaluated as a dual-feasible lower bound. "
            "If conservative verification falls below E(m), the exact zero-remainder dual point is used, giving D*(m)=E(m)."
        ),
        "hyperparameters": {
            "anchors_m": [float(v) for v in anchors],
            "active_row_count": ACTIVE_ROW_COUNT,
            "active_row_rule": "top rows by finite-n q+D, backfilled by top q",
            "term_limit": TERM_LIMIT,
            "optimization_grid_midpoints": OPT_GRID_N,
            "cert_positive_part_partitions": CERT_PARTITIONS,
            "finite_primal_n": FINITE_PRIMAL_N,
            "clarabel_tol_for_finite_primal": CLARABEL_TOL,
            "box_dual_integral": "continuous midpoint Lipschitz upper bound for int positive(-field) on [-1,1]",
        },
        "reference_values": {
            "E8f_headline_reference": E8F_HEADLINE,
        },
        "frequency_info": freq_info,
        "generator_reconstruction": generator_diagnostics,
        "anchor_results": anchor_results,
        "summary": {
            "tested_anchor_count": int(len(anchor_results)),
            "skipped_anchor_count": int(len(skipped)),
            "largest_certified_lift": float(largest_lift),
            "any_certified_positive_lift_gt_1e_10": bool(positive),
            "min_certified_Dstar_over_tested_anchors": float(min_cert),
            "min_certified_Dstar_exceeds_E8f_headline": bool(min_cert > E8F_HEADLINE),
            "max_primal_dual_sandwich_width": float(
                max((float(r.get("primal_dual_sandwich_width", 0.0)) for r in valid), default=0.0)
            ),
            "all_entitlement_checks_pass": bool(all(r.get("entitlement_holds") for r in anchor_results)),
            "all_dual_le_finite_primal_n256": bool(all(r.get("dual_le_primal_n256", True) for r in anchor_results)),
        },
        "source_paths": {
            "nconv_primal_json": str(pilot.NCONV_OUT_JSON),
            "nconv_generator_cache": str(pilot.NCONV_GENERATOR_CACHE),
            "output_json": str(out_json),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
        },
    }
    _write_json(Path(out_json), package)
    _write_json(OUT_JSON_ROOT_COPY, package)
    print(
        f"SOC_SOS_DUAL_DONE min_Dstar={min_cert:.15f} largest_lift={largest_lift:.9e} "
        f"exceeds_E8f={min_cert > E8F_HEADLINE} saved_json={out_json}",
        flush=True,
    )
    return package


if __name__ == "__main__":
    run_dual_analysis()
