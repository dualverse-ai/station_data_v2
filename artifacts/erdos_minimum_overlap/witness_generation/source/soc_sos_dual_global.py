"""Global m-envelope test for the SOC SOS-remainder dual.

This extends ``soc_sos_dual.py`` from a fixed-anchor pilot to a row-envelope
certificate.  Each certified fixed-anchor dual point is converted into a
quadratic lower-bound row in the mean variable m, then combined with the full
E8f exact-budget row family and checked with the same outside-exclusion
machinery used by the E8f headline run.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, "source")

import soc_budget_exact as sbe  # noqa: E402
import soc_freq_density3 as d3  # noqa: E402
import soc_freq_density4 as sfd4  # noqa: E402
import soc_freq_enrich2 as fe2  # noqa: E402
import soc_full_envelope as sfe  # noqa: E402
import soc_menvelope_harden as smh  # noqa: E402
import soc_sos_dual as sos  # noqa: E402
import soc_sos_remainder_pilot as pilot  # noqa: E402


ROOT = Path("source")
DATA = ROOT / "data"
OUT_JSON = DATA / "soc_sos_dual_global.json"
OUT_JSON_ROOT_COPY = ROOT / "soc_sos_dual_global.json"
CACHE_DIR = DATA / "soc_sos_dual_global_anchors"

E8F_HEADLINE = 0.38054994359516015
ANCHORS = (
    0.0,
    0.0005,
    0.001,
    0.0015,
    0.002,
    0.0024,
    0.0026,
    0.0028,
    0.003,
    0.004,
    0.005,
    0.006,
)
ACTIVE_BRACKETS = ((0.0, 0.03), (0.0, 0.04))
DOMAIN_PARTITIONS = 400_000
REFINED_PARTITIONS = 60_000
EXACT_DPS = 80
EXACT_ROOT_GRID_N = 400_000
ROOT_TOL = 5.0e-13
GLOBAL_SCHEMES = ("uniform_top2", "uniform_top3", "uniform_top4")
GLOBAL_START_SCALES = (0.5, 1.0)
GLOBAL_MAXITER = 180


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


def _row_value(row: dict[str, Any], m: float | np.ndarray) -> float | np.ndarray:
    mm = np.asarray(m, dtype=np.float64)
    out = float(row["quadratic_c0_lower"]) + float(row["a1"]) * mm + 0.5 * float(row["a2"]) * mm * mm
    if np.ndim(m) == 0:
        return float(out)
    return out


class AffineTrigPositivePart:
    """High-precision representation of psi(t) = -dual_field(t) on [-1, 1]."""

    def __init__(self, *, eta0: float, eta1: float, y: np.ndarray, xi: np.ndarray, kind: np.ndarray, dps: int) -> None:
        self.eta0 = float(eta0)
        self.eta1 = float(eta1)
        self.y = np.asarray(y, dtype=np.float64)
        self.xi = np.asarray(xi, dtype=np.float64)
        self.kind = np.asarray(kind, dtype=np.int8)
        mp.mp.dps = int(dps)
        self.mp_eta0 = mp.mpf(repr(-self.eta0))
        self.mp_eta1 = mp.mpf(repr(-self.eta1))
        self.mp_y = [mp.mpf(repr(float(v))) for v in self.y]
        self.mp_xi = [mp.mpf(repr(float(v))) for v in self.xi]
        self.mp_kind = [int(v) for v in self.kind]
        self.d1_bound = float(abs(self.eta1) + 2.0 * np.sum(np.abs(self.y * self.xi)))

    def eval_np(self, x: np.ndarray) -> np.ndarray:
        x = np.asarray(x, dtype=np.float64)
        out = -self.eta0 - self.eta1 * x
        if self.y.size == 0:
            return out
        for start in range(0, self.y.size, 256):
            stop = min(self.y.size, start + 256)
            arg = x[:, None] * self.xi[None, start:stop]
            real = self.kind[start:stop] == 0
            block = np.zeros((x.size, stop - start), dtype=np.float64)
            if np.any(real):
                block[:, real] = -2.0 * self.y[start:stop][real] * np.cos(arg[:, real])
            if np.any(~real):
                block[:, ~real] = 2.0 * self.y[start:stop][~real] * np.sin(arg[:, ~real])
            out = out + np.sum(block, axis=1)
        return out

    def g_mp(self, x: mp.mpf) -> mp.mpf:
        total = self.mp_eta0 + self.mp_eta1 * x
        for y, xi, kind in zip(self.mp_y, self.mp_xi, self.mp_kind):
            if kind == 0:
                total -= 2 * y * mp.cos(xi * x)
            else:
                total += 2 * y * mp.sin(xi * x)
        return total

    def F_iv(self, x_iv: mp.iv.mpf) -> mp.iv.mpf:
        total = mp.iv.mpf([repr(-self.eta0), repr(-self.eta0)]) * x_iv
        total += mp.iv.mpf([repr(-0.5 * self.eta1), repr(-0.5 * self.eta1)]) * x_iv * x_iv
        for yf, xif, kind in zip(self.y, self.xi, self.kind):
            y = mp.iv.mpf([repr(float(yf)), repr(float(yf))])
            xi = mp.iv.mpf([repr(float(xif)), repr(float(xif))])
            if int(kind) == 0:
                total -= 2 * y * mp.iv.sin(xi * x_iv) / xi
            else:
                total -= 2 * y * mp.iv.cos(xi * x_iv) / xi
        return total


def _bisect_root(fn: AffineTrigPositivePart, lo: float, hi: float, *, tol: float) -> tuple[float, float]:
    a = mp.mpf(repr(float(lo)))
    b = mp.mpf(repr(float(hi)))
    fa = fn.g_mp(a)
    fb = fn.g_mp(b)
    if fa == 0:
        return float(a), float(a)
    if fb == 0:
        return float(b), float(b)
    if fa * fb > 0:
        raise RuntimeError(f"root bracket lost sign change: {lo}, {hi}, {fa}, {fb}")
    while float(b - a) > tol:
        mid = 0.5 * (a + b)
        fm = fn.g_mp(mid)
        if fm == 0:
            half = mp.mpf(repr(tol)) * mp.mpf("0.25")
            return float(mid - half), float(mid + half)
        if fa * fm <= 0:
            b = mid
            fb = fm
        else:
            a = mid
            fa = fm
    return float(a), float(b)


def _isolate_roots_unit(fn: AffineTrigPositivePart, *, grid_n: int) -> dict[str, Any]:
    x = np.linspace(-1.0, 1.0, int(grid_n) + 1, dtype=np.float64)
    y = fn.eval_np(x)
    sign_change = np.signbit(y[:-1]) != np.signbit(y[1:])
    roots = [_bisect_root(fn, float(x[i]), float(x[i + 1]), tol=ROOT_TOL) for i in np.flatnonzero(sign_change)]
    roots.sort(key=lambda p: 0.5 * (p[0] + p[1]))
    deduped: list[tuple[float, float]] = []
    for root in roots:
        if not deduped or abs(0.5 * (root[0] + root[1]) - 0.5 * (deduped[-1][0] + deduped[-1][1])) > 10.0 * ROOT_TOL:
            deduped.append(root)
        else:
            deduped[-1] = (min(deduped[-1][0], root[0]), max(deduped[-1][1], root[1]))
    h = 2.0 / float(grid_n)
    unsafe = (~sign_change) & (np.minimum(np.abs(y[:-1]), np.abs(y[1:])) <= fn.d1_bound * h)
    return {
        "domain": [-1.0, 1.0],
        "grid_n": int(grid_n),
        "grid_spacing": h,
        "roots": deduped,
        "root_count": int(len(deduped)),
        "root_width_max": max((b - a for a, b in deduped), default=0.0),
        "mesh_min_value": float(np.min(y)),
        "mesh_max_value": float(np.max(y)),
        "unsafe_same_sign_cell_count": int(np.sum(unsafe)),
    }


def _exact_positive_integral_unit(
    fn: AffineTrigPositivePart,
    roots: list[tuple[float, float]],
    *,
    dps: int,
) -> dict[str, Any]:
    mp.iv.dps = int(dps)
    endpoints: list[tuple[float, float]] = [(-1.0, -1.0)] + roots + [(1.0, 1.0)]
    total = mp.iv.mpf([0.0, 0.0])
    positive_intervals: list[dict[str, float]] = []
    ambiguous = 0
    for i in range(len(endpoints) - 1):
        lo = endpoints[i][1]
        hi = endpoints[i + 1][0]
        if hi <= lo:
            continue
        mid = 0.5 * (lo + hi)
        val = fn.g_mp(mp.mpf(repr(mid)))
        if abs(val) < mp.mpf("1e-40"):
            ambiguous += 1
            continue
        if val > 0:
            a = mp.iv.mpf([repr(float(endpoints[i][0])), repr(float(endpoints[i][1]))])
            b = mp.iv.mpf([repr(float(endpoints[i + 1][0])), repr(float(endpoints[i + 1][1]))])
            contrib = fn.F_iv(b) - fn.F_iv(a)
            total += contrib
            positive_intervals.append({"lo": float(lo), "hi": float(hi), "g_mid": float(val)})
    return {
        "budget_lo": float(total.a),
        "budget_hi": float(total.b),
        "budget_mid": 0.5 * (float(total.a) + float(total.b)),
        "budget_width": float(total.b - total.a),
        "positive_interval_count": int(len(positive_intervals)),
        "positive_measure": float(sum(p["hi"] - p["lo"] for p in positive_intervals)),
        "ambiguous_sign_segments": int(ambiguous),
        "positive_interval_preview": positive_intervals[:6] + positive_intervals[-6:],
    }


def _exact_recertify_scheme(scheme: dict[str, Any]) -> dict[str, Any] | None:
    term_pack = scheme.get("term_pack")
    y = scheme.get("dual_y")
    if not term_pack or y is None:
        return None
    cert = scheme["certification"]
    fn = AffineTrigPositivePart(
        eta0=float(cert["eta0"]),
        eta1=float(cert["eta1"]),
        y=np.asarray(y, dtype=np.float64),
        xi=np.asarray(term_pack["xi"], dtype=np.float64),
        kind=np.asarray(term_pack["kind"], dtype=np.int8),
        dps=EXACT_DPS,
    )
    root_data = _isolate_roots_unit(fn, grid_n=EXACT_ROOT_GRID_N)
    budget = _exact_positive_integral_unit(fn, root_data["roots"], dps=EXACT_DPS)
    value = float(cert["base_without_box_integral"] - budget["budget_hi"])
    return {
        "method": "80dps_root_isolated_positive_part_on_unit_interval",
        "dps": int(EXACT_DPS),
        "root_grid_n": int(EXACT_ROOT_GRID_N),
        "root_count": int(root_data["root_count"]),
        "root_width_max": float(root_data["root_width_max"]),
        "unsafe_same_sign_cell_count": int(root_data["unsafe_same_sign_cell_count"]),
        "positive_integral_hi": float(budget["budget_hi"]),
        "positive_integral_mid": float(budget["budget_mid"]),
        "positive_integral_width": float(budget["budget_width"]),
        "positive_interval_count": int(budget["positive_interval_count"]),
        "certified_value_lower": value,
        "passes_basic_root_audit": bool(root_data["root_width_max"] <= 1.1e-12 and budget["ambiguous_sign_segments"] == 0),
    }


def _load_full_e8f_rows() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    base_cert = _load_json(sfd4.BASE_CERT_PATH)
    exact_budget_summary = _load_json(sfd4.BASE_EXACT_BUDGET_PATH)
    mean_guard = float(base_cert["verification_settings"]["mean_guard"])
    base_rows, recovered = smh.build_verified_rows_with_baseline_recovery(base_cert, exact_budget_summary)
    inherited_payloads = fe2._load_inherited_payloads()
    prior_payloads = d3._load_prior_enrichment_payloads()
    e2f_rows = [p["row"] for p in prior_payloads if p.get("row", {}).get("family") == "e2f"]
    e4f_payloads = sfd4._load_e4f_payloads()
    e8f_payloads = []
    missing = []
    for m in sfd4.E8F_ANCHORS_REQUESTED:
        payload = sfd4._load_cached_e8f_row(float(m))
        if payload is None:
            missing.append(float(m))
        else:
            e8f_payloads.append(payload)
    if missing:
        raise FileNotFoundError(f"missing E8f row caches needed for headline envelope: {missing}")
    rows = (
        list(base_rows)
        + [p["row"] for p in inherited_payloads]
        + e2f_rows
        + [p["row"] for p in e4f_payloads]
        + [p["row"] for p in e8f_payloads]
    )
    return rows, {
        "mean_guard": mean_guard,
        "base_row_count": int(len(base_rows)),
        "inherited_payload_count": int(len(inherited_payloads)),
        "e2f_row_count": int(len(e2f_rows)),
        "e4f_row_count": int(len(e4f_payloads)),
        "e8f_row_count": int(len(e8f_payloads)),
        "recovered": recovered,
    }


def _cache_path(m: float) -> Path:
    safe = f"{float(m):.7f}".replace(".", "p")
    return CACHE_DIR / f"sos_global_anchor_m_{safe}.json"


def _load_prior_pilot_anchor(m: float) -> dict[str, Any] | None:
    path = sos.OUT_JSON_ROOT_COPY
    if not path.exists():
        return None
    try:
        data = _load_json(path)
    except Exception:
        return None
    for item in data.get("anchor_results", []):
        if abs(float(item.get("m", -9.0)) - float(m)) <= 5.0e-12 and item.get("best_scheme") is not None:
            out = dict(item)
            out["source"] = str(path)
            out["source_note"] = "loaded prior reference full fixed-anchor SOS pilot result"
            return out
    return None


def _scheme_to_quadratic_row(rows: list[dict[str, Any]], scheme: dict[str, Any], *, anchor_m: float, certified_value: float, method: str) -> dict[str, Any]:
    lam = np.asarray(scheme["lambda_by_row"], dtype=np.float64)
    eta1 = float(scheme["certification"]["eta1"])
    c0_mix = float(sum(float(row["quadratic_c0_lower"]) * float(lam[i]) for i, row in enumerate(rows)))
    a1_mix = float(sum(float(row["a1"]) * float(lam[i]) for i, row in enumerate(rows)))
    a2_mix = float(sum(float(row["a2"]) * float(lam[i]) for i, row in enumerate(rows)))
    q_anchor = float(sum(float(lam[i]) * _row_value(row, float(anchor_m)) for i, row in enumerate(rows)))
    c0 = c0_mix - q_anchor - 0.5 * eta1 * float(anchor_m) + float(certified_value)
    row = {
        "id": f"sos_dual_anchor_m_{float(anchor_m):.7f}_{scheme['scheme']}",
        "family": "sos_dual_global",
        "m": float(anchor_m),
        "source_m": float(anchor_m),
        "quadratic_c0_lower": float(c0),
        "L_source_m_lower": float(certified_value),
        "a1": float(a1_mix + 0.5 * eta1),
        "a2": float(a2_mix),
        "K": int(scheme.get("term_count", 0)),
        "source": {
            "description": "Certified SOC SOS-remainder box-dual row converted to a global quadratic in m.",
            "scheme": str(scheme["scheme"]),
            "certification_method": str(method),
            "active_row_ids": scheme.get("active_row_ids", []),
        },
    }
    row["source_value_check_error"] = float(_row_value(row, float(anchor_m)) - float(certified_value))
    return row


def _global_lambda_schemes(active_count: int) -> list[tuple[str, np.ndarray]]:
    return [(name, vec) for name, vec in sos._lambda_schemes(int(active_count)) if name in GLOBAL_SCHEMES]


def _optimize_scheme_lite(
    *,
    rows: list[dict[str, Any]],
    active_indices: list[int],
    lambdas_local: np.ndarray,
    f_ref: np.ndarray,
    m: float,
    scheme_name: str,
) -> dict[str, Any]:
    first_target = -0.5 * float(m)
    q_values = np.asarray([_row_value(row, float(m)) for row in rows], dtype=np.float64)
    lambdas_by_row = np.zeros(len(rows), dtype=np.float64)
    for local_idx, row_idx in enumerate(active_indices):
        lambdas_by_row[row_idx] = float(lambdas_local[local_idx])
    q_const = float(lambdas_by_row @ q_values)
    terms = sos._build_term_pack(rows, active_indices, lambdas_local, f_ref, term_limit=sos.TERM_LIMIT)
    fun_grad, _ = sos._approx_objective_factory(
        q_const=q_const,
        first_target=first_target,
        lambdas_by_global_row=lambdas_by_row,
        terms=terms,
        grid_n=sos.OPT_GRID_N,
    )
    c = lambdas_by_row[terms.row_indices] * terms.alpha if terms.xi.size else np.zeros(0)
    tangent = c * terms.residual
    attempts: list[dict[str, Any]] = []
    for start_idx, scale in enumerate(GLOBAL_START_SCALES):
        x0 = np.concatenate([float(scale) * tangent, np.zeros(2, dtype=np.float64)])
        t0 = time.time()
        res = minimize(
            lambda x: fun_grad(x),
            x0,
            method="L-BFGS-B",
            jac=True,
            options={"maxiter": int(GLOBAL_MAXITER), "ftol": 5.0e-13, "gtol": 3.0e-9, "maxls": 30},
        )
        attempts.append(
            {
                "start_index": int(start_idx),
                "scale": float(scale),
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
    cert = sos._dual_value_certificate(
        q_const=q_const,
        first_target=first_target,
        lambdas_by_global_row=lambdas_by_row,
        terms=terms,
        y=y,
        eta0=eta0,
        eta1=eta1,
        partitions=sos.CERT_PARTITIONS,
    )
    return {
        "scheme": scheme_name,
        "optimizer_success": bool(best_attempt["optimizer_success"]),
        "optimizer_status": int(best_attempt["optimizer_status"]),
        "optimizer_message": str(best_attempt["optimizer_message"]),
        "optimizer_fun": float(best_attempt["optimizer_fun"]),
        "optimizer_elapsed_seconds": float(sum(a["optimizer_elapsed_seconds"] for a in attempts)),
        "start_attempts": [
            {
                "start_index": int(a["start_index"]),
                "scale": float(a["scale"]),
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


def _fast_anchor_search(generator_rows: list[dict[str, Any]], m: float) -> dict[str, Any]:
    q = np.asarray([_row_value(row, float(m)) for row in generator_rows], dtype=np.float64)
    pure_envelope = float(np.max(q))
    active_indices = [int(i) for i in np.argsort(q)[::-1][: sos.ACTIVE_ROW_COUNT]]
    # This profile only selects/prioritizes nonnegative remainder terms.  The
    # final row is certified from the dual variables, so the reference profile
    # does not affect validity.
    f_ref = pilot._initial_feasible(sos.FINITE_PRIMAL_N, float(m))
    print(
        f"sos_global_fast_anchor m={float(m):.7f} generator_E={pure_envelope:.15f} "
        f"active={[str(generator_rows[i]['id']) for i in active_indices]}",
        flush=True,
    )
    scheme_results: list[dict[str, Any]] = []
    for scheme_name, lambdas in _global_lambda_schemes(len(active_indices)):
        res = _optimize_scheme_lite(
            rows=generator_rows,
            active_indices=active_indices,
            lambdas_local=lambdas,
            f_ref=f_ref,
            m=float(m),
            scheme_name=scheme_name,
        )
        scheme_results.append(res)
        print(
            f"sos_global_fast_scheme m={float(m):.7f} scheme={scheme_name} "
            f"cert={res['certification']['certified_value_lower']:.15f} "
            f"lift_vs_generator_E={res['certification']['certified_value_lower'] - pure_envelope:+.9e} "
            f"terms={res['term_count']}",
            flush=True,
        )
    best = max(scheme_results, key=lambda r: r["certification"]["certified_value_lower"], default=None)
    best_value = -float("inf") if best is None else float(best["certification"]["certified_value_lower"])
    return {
        "m": float(m),
        "pure_envelope_E": pure_envelope,
        "pure_controller_row": str(generator_rows[int(np.argmax(q))]["id"]),
        "certified_dual_value_Dstar": float(max(pure_envelope, best_value)),
        "certified_lift": float(max(pure_envelope, best_value) - pure_envelope),
        "best_nonzero_dual_value_before_entitlement_floor": None if best is None else float(best_value),
        "entitlement_holds": True,
        "dual_le_primal_n256": None,
        "finite_n_primal_upper": None,
        "primal_dual_sandwich_width": None,
        "active_rows": [
            {
                "index": int(i),
                "id": str(generator_rows[i]["id"]),
                "family": str(generator_rows[i].get("family", "unknown")),
                "source_m": float(generator_rows[i]["source_m"]),
                "q_at_m": float(q[i]),
                "K": int(generator_rows[i]["K"]),
            }
            for i in active_indices
        ],
        "finite_primal_n256": {
            "source": "not_solved_in_global_driver",
            "reason": "removed from dense global run; not needed for dual-feasible certification",
            "reference_profile": "pilot._initial_feasible used only for term selection",
        },
        "scheme_count": int(len(scheme_results)),
        "best_scheme": None if best is None else sos._jsonify(best),
        "scheme_summaries": [
            {
                "scheme": str(r["scheme"]),
                "certified_value_lower": float(r["certification"]["certified_value_lower"]),
                "lift_vs_generator_E": float(r["certification"]["certified_value_lower"] - pure_envelope),
                "term_count": int(r["term_count"]),
                "optimizer_success": bool(r["optimizer_success"]),
                "eta0": float(r["certification"]["eta0"]),
                "eta1": float(r["certification"]["eta1"]),
                "positive_integral_upper": float(r["certification"]["positive_part"]["positive_integral_upper"]),
            }
            for r in sorted(scheme_results, key=lambda x: x["certification"]["certified_value_lower"], reverse=True)[:12]
        ],
    }


def _solve_or_load_anchor(generator_rows: list[dict[str, Any]], pure_rows: list[dict[str, Any]], m: float, *, started: float, max_total_seconds: float) -> dict[str, Any]:
    path = _cache_path(float(m))
    if path.exists():
        cached = _load_json(path)
        if cached.get("schema") == "public SOC SOS global anchor cache v2":
            cached["cache_status"] = "loaded_from_cache"
            return cached
    raw = _load_prior_pilot_anchor(float(m))
    if raw is None:
        raw = _fast_anchor_search(generator_rows, float(m))
    best = raw.get("best_scheme")
    exact = None
    method = "zero_or_conservative_midpoint_lipschitz"
    nonzero_value = float(raw.get("best_nonzero_dual_value_before_entitlement_floor", -float("inf")))
    if best is not None:
        try:
            exact = _exact_recertify_scheme(best)
        except Exception as exc:  # noqa: BLE001
            exact = {"status": "exception", "error": repr(exc)}
        if isinstance(exact, dict) and "certified_value_lower" in exact:
            nonzero_value = max(nonzero_value, float(exact["certified_value_lower"]))
            method = "max_of_conservative_midpoint_and_80dps_root_isolated"
    pure_e = float(max(_row_value(row, float(m)) for row in pure_rows))
    dstar = max(pure_e, nonzero_value)
    sos_row = None
    if best is not None and math.isfinite(nonzero_value):
        sos_row = _scheme_to_quadratic_row(generator_rows, best, anchor_m=float(m), certified_value=nonzero_value, method=method)
    payload = {
        "schema": "public SOC SOS global anchor cache v2",
        "anchor_m": float(m),
        "cache_status": "newly_solved",
        "pure_e8f_envelope_E": pure_e,
        "generator_subset_E": float(raw["pure_envelope_E"]),
        "certified_dual_value_Dstar_at_anchor": float(dstar),
        "certified_lift_vs_full_E": float(dstar - pure_e),
        "entitlement_holds_vs_full_E": bool(dstar + 1.0e-12 >= pure_e),
        "best_nonzero_value": None if not math.isfinite(nonzero_value) else float(nonzero_value),
        "best_nonzero_lift_vs_full_E": None if not math.isfinite(nonzero_value) else float(nonzero_value - pure_e),
        "certification_method": method,
        "exact_recertification": exact,
        "sos_row": sos_row,
        "raw_anchor_result": raw,
    }
    _write_json(path, payload)
    return payload


def _envelope(rows: list[dict[str, Any]], mean_guard: float, label: str, bracket: tuple[float, float]) -> dict[str, Any]:
    env = sfe._envelope(rows, mean_guard, label, active_bracket=bracket)
    env["domain_partitions_requested"] = int(DOMAIN_PARTITIONS)
    env["refined_partitions_requested"] = int(REFINED_PARTITIONS)
    return env


def run_global_analysis(*, max_total_seconds: float = 1680.0, out_json: Path = OUT_JSON) -> dict[str, Any]:
    started = time.time()
    pure_rows, pure_info = _load_full_e8f_rows()
    mean_guard = float(pure_info["mean_guard"])
    generator_rows, generator_diagnostics, freq_info = pilot._load_nconv_rows()
    print("SOC_SOS_DUAL_GLOBAL_BEGIN", flush=True)
    print(
        f"pure_rows={len(pure_rows)} generator_rows={len(generator_rows)} "
        f"anchors={len(ANCHORS)} term_limit={sos.TERM_LIMIT}",
        flush=True,
    )

    anchor_payloads: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for m in ANCHORS:
        elapsed = time.time() - started
        if elapsed > max_total_seconds - 180.0:
            skipped.append({"m": float(m), "reason": "time_guard_before_anchor", "elapsed_seconds": float(elapsed)})
            continue
        try:
            payload = _solve_or_load_anchor(
                generator_rows,
                pure_rows,
                float(m),
                started=started,
                max_total_seconds=max_total_seconds,
            )
        except Exception as exc:  # noqa: BLE001
            skipped.append({"m": float(m), "reason": "exception", "error": repr(exc)})
            continue
        anchor_payloads.append(payload)
        print(
            f"sos_global_anchor m={float(m):.7f} E={payload['pure_e8f_envelope_E']:.15f} "
            f"Dstar={payload['certified_dual_value_Dstar_at_anchor']:.15f} "
            f"lift={payload['certified_lift_vs_full_E']:+.9e} "
            f"method={payload['certification_method']} cache={payload['cache_status']}",
            flush=True,
        )
        _write_json(
            Path(out_json),
            {
                "schema": "public SOC SOS dual global v1",
                "status": "partial_running",
                "elapsed_seconds": float(time.time() - started),
                "anchor_results": anchor_payloads,
                "skipped": skipped,
            },
        )

    sos_rows = [p["sos_row"] for p in anchor_payloads if p.get("sos_row") is not None]
    combined_rows = list(pure_rows) + sos_rows
    bracket_envelopes: dict[str, dict[str, Any]] = {}
    for bracket in ACTIVE_BRACKETS:
        key = f"{bracket[0]:.3f}_{bracket[1]:.3f}"
        pure_env = _envelope(pure_rows, mean_guard, "full_E8f_pure_envelope", bracket)
        sos_env = _envelope(combined_rows, mean_guard, "full_E8f_plus_sos_dual_rows", bracket)
        bracket_envelopes[key] = {"pure_e8f": pure_env, "sos_global": sos_env}
        print(
            f"sos_global_envelope bracket={key} value={sos_env['certified_global']:.15f} "
            f"argmin={sos_env['global_argmin_m']:.7f} controlling={sos_env['global_controlling_row']} "
            f"outside_pass={sos_env['outside_exclusion_pass']} margin={sos_env['outside_exclusion_margin']:.12e}",
            flush=True,
        )

    passing = [
        (float(envs["sos_global"]["certified_global"]), key, envs["sos_global"])
        for key, envs in bracket_envelopes.items()
        if envs["sos_global"]["outside_exclusion_pass"]
    ]
    if passing:
        global_value, best_key, best_env = max(passing, key=lambda item: item[0])
    else:
        global_value, best_key, best_env = float("nan"), None, None
    all_brackets_pass = bool(all(envs["sos_global"]["outside_exclusion_pass"] for envs in bracket_envelopes.values()))
    completed_all = bool(len(anchor_payloads) == len(ANCHORS) and not skipped)
    fully_certified = bool(completed_all and all_brackets_pass and math.isfinite(global_value))
    verdict = (
        "strict_global_sos_improvement"
        if fully_certified and global_value > E8F_HEADLINE
        else "no_strict_global_gain_or_incomplete"
    )
    package = {
        "schema": "public SOC SOS dual global v1",
        "created_by": "source/soc_sos_dual_global.py::run_global_analysis",
        "status": "complete" if completed_all else "partial_time_guard_or_anchor_failure",
        "elapsed_seconds": float(time.time() - started),
        "claim_scope": (
            "Full E8f exact-budget envelope plus certified SOS-remainder dual rows generated on the requested dense mean anchors. "
            "A global claim is allowed only when all requested anchors completed and both outside-exclusion brackets pass."
        ),
        "directionality_note": (
            "The certified global value is the minimum over m of the maximum of certified quadratic rows. "
            "Missing anchors can only make the tested SOS envelope weaker than a denser completed run, but an incomplete dense-grid request is reported separately."
        ),
        "hyperparameters": {
            "anchors_m": [float(v) for v in ANCHORS],
            "active_row_count": int(sos.ACTIVE_ROW_COUNT),
            "term_limit": int(sos.TERM_LIMIT),
            "optimization_grid_midpoints": int(sos.OPT_GRID_N),
            "fallback_cert_positive_part_partitions": int(sos.CERT_PARTITIONS),
            "exact_positive_part_dps": int(EXACT_DPS),
            "exact_root_grid_n": int(EXACT_ROOT_GRID_N),
            "outside_brackets": [[float(a), float(b)] for a, b in ACTIVE_BRACKETS],
            "outside_domain_partitions": int(DOMAIN_PARTITIONS),
            "outside_refined_partitions": int(REFINED_PARTITIONS),
        },
        "reference_values": {
            "E8f_headline_reference": float(E8F_HEADLINE),
        },
        "pure_row_info": pure_info,
        "generator_diagnostics": generator_diagnostics,
        "frequency_info": freq_info,
        "anchor_results": anchor_payloads,
        "skipped_or_failed_anchors": skipped,
        "sos_row_count": int(len(sos_rows)),
        "bracket_envelopes": bracket_envelopes,
        "summary": {
            "completed_anchor_count": int(len(anchor_payloads)),
            "requested_anchor_count": int(len(ANCHORS)),
            "completed_all_requested_anchors": completed_all,
            "all_anchor_entitlement_vs_full_E_pass": bool(all(p["entitlement_holds_vs_full_E"] for p in anchor_payloads)),
            "all_outside_exclusion_brackets_pass": all_brackets_pass,
            "best_outside_passing_bracket": best_key,
            "global_certified_value_V": None if not math.isfinite(global_value) else float(global_value),
            "binding_m": None if best_env is None else float(best_env["global_argmin_m"]),
            "binding_row": None if best_env is None else str(best_env["global_controlling_row"]),
            "strictly_exceeds_E8f_headline": bool(fully_certified and global_value > E8F_HEADLINE),
            "delta_vs_E8f_headline": None if not math.isfinite(global_value) else float(global_value - E8F_HEADLINE),
            "final_verdict": verdict,
            "fully_certified_global_claim_allowed": fully_certified,
        },
        "source_paths": {
            "output_json": str(out_json),
            "output_json_root_copy": str(OUT_JSON_ROOT_COPY),
            "anchor_cache_dir": str(CACHE_DIR),
            "sos_pilot": str(sos.OUT_JSON_ROOT_COPY),
            "e8f_envelope": str(sfd4.OUT_JSON_ROOT_COPY),
        },
    }
    _write_json(Path(out_json), package)
    _write_json(OUT_JSON_ROOT_COPY, package)
    print(
        f"SOC_SOS_DUAL_GLOBAL_DONE status={package['status']} V={package['summary']['global_certified_value_V']} "
        f"binding_m={package['summary']['binding_m']} binding_row={package['summary']['binding_row']} "
        f"outside_all={all_brackets_pass} verdict={verdict} saved_json={out_json}",
        flush=True,
    )
    return package


if __name__ == "__main__":
    run_global_analysis()
