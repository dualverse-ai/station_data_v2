"""Exact-rational full-space certificates for small Kakeya triangle unions.

The parameter gauge is x_n = 0, so the free coordinates are
``(x_1, ..., x_{n-1})``.  For n=3 and n=4 this module enumerates the complete
unbounded rational arrangement cut out by endpoint-crossing heights h=0,
h=1, and h_i=h_j.  On each full-dimensional cell the sweep schedule is fixed,
so the union area is an exact quadratic polynomial.
"""

from __future__ import annotations

import json
import math
import os
import time
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple


Rat = Fraction
Point = Tuple[Rat, ...]
Hyper = Tuple[Rat, ...]
Poly = Dict[Tuple[int, ...], Rat]


def frac_json(x: Rat) -> str:
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def parse_frac(s: str) -> Rat:
    if "/" in s:
        a, b = s.split("/")
        return Rat(int(a), int(b))
    return Rat(int(s), 1)


def normalize_offsets(offsets: Sequence[Rat]) -> List[Rat]:
    m = min(offsets)
    return [x - m for x in offsets]


def offsets_from_params(n: int, params: Sequence[Rat]) -> List[Rat]:
    if len(params) != n - 1:
        raise ValueError("wrong parameter dimension")
    return [Rat(v) for v in params] + [Rat(0)]


def endpoint_affines(n: int) -> List[Tuple[List[Rat], Rat, Rat, Tuple[int, str]]]:
    d = n - 1
    rows: List[Tuple[List[Rat], Rat, Rat, Tuple[int, str]]] = []
    for j in range(1, n + 1):
        coeff = [Rat(0) for _ in range(d)]
        if j < n:
            coeff[j - 1] = Rat(1)
        rows.append((coeff[:], Rat(0), Rat(j, n), (j, "L")))
        rows.append((coeff[:], Rat(1, n), Rat(j - 1, n), (j, "R")))
    return rows


def event_affines_frac(n: int) -> List[Tuple[List[Rat], Rat, Tuple[int, int]]]:
    lines = endpoint_affines(n)
    out: List[Tuple[List[Rat], Rat, Tuple[int, int]]] = []
    d = n - 1
    for i, (ai, bi, si, _) in enumerate(lines):
        for j, (aj, bj, sj, _) in enumerate(lines[i + 1 :], start=i + 1):
            if si == sj:
                continue
            den = si - sj
            out.append(([(aj[k] - ai[k]) / den for k in range(d)], (bj - bi) / den, (i, j)))
    return out


def canonical_hyper(row: Sequence[Rat]) -> Optional[Hyper]:
    if all(v == 0 for v in row[:-1]):
        return None
    lcm = 1
    for v in row:
        lcm = lcm * v.denominator // math.gcd(lcm, v.denominator)
    vals = [int(v * lcm) for v in row]
    g = 0
    for v in vals:
        g = math.gcd(g, abs(v))
    vals = [v // g for v in vals]
    first = next(v for v in vals if v != 0)
    if first < 0:
        vals = [-v for v in vals]
    return tuple(Rat(v) for v in vals)


def canonical_hyper_with_sign(row: Sequence[Rat]) -> Optional[Tuple[Hyper, int]]:
    h = canonical_hyper(row)
    if h is None:
        return None
    for raw, can in zip(row, h):
        if raw != 0:
            return h, (1 if raw / can > 0 else -1)
    return h, 1


def arrangement_hyperplanes(n: int) -> List[Hyper]:
    events = event_affines_frac(n)
    d = n - 1
    raw: List[List[Rat]] = []
    for a, c, _ in events:
        raw.append(a + [c])
        raw.append(a + [c - 1])
    for i, (ai, ci, _) in enumerate(events):
        for aj, cj, _ in events[i + 1 :]:
            raw.append([ai[k] - aj[k] for k in range(d)] + [ci - cj])
    seen = set()
    out: List[Hyper] = []
    for row in raw:
        h = canonical_hyper(row)
        if h is not None and h not in seen:
            seen.add(h)
            out.append(h)
    out.sort()
    return out


def hyper_value(h: Hyper, p: Point) -> Rat:
    return sum(h[i] * p[i] for i in range(len(p))) + h[-1]


def sign_vector(hypers: Sequence[Hyper], p: Point) -> Tuple[int, ...]:
    out = []
    for h in hypers:
        v = hyper_value(h, p)
        if v == 0:
            raise ValueError("sample on hyperplane")
        out.append(1 if v > 0 else -1)
    return tuple(out)


def enumerate_cells_1d(points_in: Sequence[Hyper]) -> Dict[Tuple[int, ...], Point]:
    points = sorted(-h[1] / h[0] for h in points_in)
    samples: List[Rat] = []
    if not points:
        samples = [Rat(0)]
    else:
        samples.append(points[0] - 1)
        for a, b in zip(points, points[1:]):
            samples.append((a + b) / 2)
        samples.append(points[-1] + 1)
    cells = {}
    for x in samples:
        cells[tuple(1 if x - p > 0 else -1 for p in points)] = (x,)
    return cells


def enumerate_cells_2d(lines_in: Sequence[Hyper]) -> Dict[Tuple[int, ...], Point]:
    lines: List[Tuple[Rat, Rat, Rat]] = [(h[0], h[1], h[2]) for h in lines_in]
    cells: Dict[Tuple[int, ...], Point] = {}
    if not lines:
        return {tuple(): (Rat(0), Rat(0))}
    for idx, line in enumerate(lines):
        a, b, c = line
        if b != 0:
            p0 = (Rat(0), -c / b)
        else:
            p0 = (-c / a, Rat(0))
        direction = (b, -a)
        ts = set()
        for j, other in enumerate(lines):
            if j == idx:
                continue
            aa, bb, cc = other
            alpha = aa * direction[0] + bb * direction[1]
            beta = aa * p0[0] + bb * p0[1] + cc
            if alpha != 0:
                ts.add(-beta / alpha)
        ordered = sorted(ts)
        samples: List[Rat] = []
        if not ordered:
            samples = [Rat(0)]
        else:
            samples.append(ordered[0] - 1)
            for u, v in zip(ordered, ordered[1:]):
                samples.append((u + v) / 2)
            samples.append(ordered[-1] + 1)
        for t in samples:
            base = (p0[0] + t * direction[0], p0[1] + t * direction[1])
            eps_limit: Optional[Rat] = None
            for j, other in enumerate(lines):
                if j == idx:
                    continue
                val = other[0] * base[0] + other[1] * base[1] + other[2]
                delta = other[0] * a + other[1] * b
                if delta != 0:
                    bound = abs(val / delta) / 2
                    if bound > 0 and (eps_limit is None or bound < eps_limit):
                        eps_limit = bound
            eps = eps_limit if eps_limit is not None else Rat(1, 2)
            if eps == 0:
                continue
            for side in (-1, 1):
                p = (base[0] + side * eps * a, base[1] + side * eps * b)
                try:
                    sv = tuple(1 if (ln[0] * p[0] + ln[1] * p[1] + ln[2]) > 0 else -1 for ln in lines)
                except ValueError:
                    continue
                cells.setdefault(sv, p)
    return cells


def plane_base_and_basis(plane: Hyper) -> Tuple[Point, Point, Point, Point]:
    a, b, c, d = plane
    if c != 0:
        p0 = (Rat(0), Rat(0), -d / c)
        u = (Rat(1), Rat(0), -a / c)
        v = (Rat(0), Rat(1), -b / c)
    elif b != 0:
        p0 = (Rat(0), -d / b, Rat(0))
        u = (Rat(1), -a / b, Rat(0))
        v = (Rat(0), -c / b, Rat(1))
    else:
        p0 = (-d / a, Rat(0), Rat(0))
        u = (-b / a, Rat(1), Rat(0))
        v = (-c / a, Rat(0), Rat(1))
    normal = (a, b, c)
    return p0, u, v, normal


def map_plane_point(p0: Point, u: Point, v: Point, q: Point) -> Point:
    return tuple(p0[i] + q[0] * u[i] + q[1] * v[i] for i in range(3))


def induced_lines_on_plane(hypers: Sequence[Hyper], plane_idx: int) -> Tuple[List[Hyper], List[int]]:
    p0, u, v, _ = plane_base_and_basis(hypers[plane_idx])
    lines: List[Hyper] = []
    owners: List[int] = []
    seen = set()
    for idx, h in enumerate(hypers):
        if idx == plane_idx:
            continue
        alpha = sum(h[i] * u[i] for i in range(3))
        beta = sum(h[i] * v[i] for i in range(3))
        gamma = hyper_value(h, p0)
        canon = canonical_hyper((alpha, beta, gamma))
        if canon is None:
            continue
        if canon not in seen:
            seen.add(canon)
            lines.append(canon)
            owners.append(idx)
    order = sorted(range(len(lines)), key=lambda i: lines[i])
    return [lines[i] for i in order], [owners[i] for i in order]


def enumerate_cells_3d(hypers: Sequence[Hyper], deadline: Optional[float] = None) -> Tuple[Dict[Tuple[int, ...], Point], bool]:
    cells: Dict[Tuple[int, ...], Point] = {}
    for plane_idx, plane in enumerate(hypers):
        if deadline is not None and time.time() > deadline:
            return cells, False
        induced, _owners = induced_lines_on_plane(hypers, plane_idx)
        face_cells = enumerate_cells_2d(induced)
        p0, u, v, normal = plane_base_and_basis(plane)
        for _face_sv, q in face_cells.items():
            base = map_plane_point(p0, u, v, q)
            eps_limit: Optional[Rat] = None
            for idx, h in enumerate(hypers):
                if idx == plane_idx:
                    continue
                val = hyper_value(h, base)
                delta = sum(h[i] * normal[i] for i in range(3))
                if delta != 0:
                    bound = abs(val / delta) / 2
                    if bound > 0 and (eps_limit is None or bound < eps_limit):
                        eps_limit = bound
            eps = eps_limit if eps_limit is not None else Rat(1, 2)
            if eps == 0:
                continue
            for side in (-1, 1):
                p = tuple(base[i] + side * eps * normal[i] for i in range(3))
                try:
                    sv = sign_vector(hypers, p)
                except ValueError:
                    continue
                cells.setdefault(sv, p)
    return cells, True


def affine_endpoint_value(n: int, endpoint_index: int, params: Point, y: Rat) -> Rat:
    coeff, const, slope, _ = endpoint_affines(n)[endpoint_index]
    return sum(coeff[i] * params[i] for i in range(len(params))) + const + slope * y


def interval_at_y(n: int, offsets: Sequence[Rat], j: int, y: Rat) -> Tuple[Rat, Rat]:
    x = offsets[j - 1]
    return x + Rat(j, n) * y, x + Rat(1, n) + Rat(j - 1, n) * y


def union_length_at_y_frac(n: int, offsets: Sequence[Rat], y: Rat) -> Rat:
    intervals = [interval_at_y(n, offsets, j, y) for j in range(1, n + 1)]
    intervals.sort()
    total = Rat(0)
    cur_l: Optional[Rat] = None
    cur_r: Optional[Rat] = None
    for lft, rgt in intervals:
        if cur_l is None:
            cur_l, cur_r = lft, rgt
        elif lft <= cur_r:
            if rgt > cur_r:
                cur_r = rgt
        else:
            total += cur_r - cur_l
            cur_l, cur_r = lft, rgt
    if cur_l is not None:
        total += cur_r - cur_l
    return total


def exact_area_offsets(n: int, offsets: Sequence[Rat]) -> Rat:
    lines: List[Tuple[Rat, Rat]] = []
    for j, x in enumerate(offsets, start=1):
        lines.append((Rat(j, n), x))
        lines.append((Rat(j - 1, n), x + Rat(1, n)))
    breaks = {Rat(0), Rat(1)}
    for i, (s1, b1) in enumerate(lines):
        for s2, b2 in lines[i + 1 :]:
            if s1 == s2:
                continue
            y = (b2 - b1) / (s1 - s2)
            if Rat(0) < y < Rat(1):
                breaks.add(y)
    bp = sorted(breaks)
    area = Rat(0)
    for a, b in zip(bp, bp[1:]):
        if a != b:
            area += (b - a) * (union_length_at_y_frac(n, offsets, a) + union_length_at_y_frac(n, offsets, b)) / 2
    return area


def poly_affine(coeff: Sequence[Rat], const: Rat) -> Poly:
    d = len(coeff)
    out: Poly = {}
    if const:
        out[(0,) * d] = const
    for i, a in enumerate(coeff):
        if a:
            exp = [0] * d
            exp[i] = 1
            out[tuple(exp)] = out.get(tuple(exp), Rat(0)) + a
    return {k: v for k, v in out.items() if v}


def poly_add(a: Poly, b: Poly, scale: Rat = Rat(1)) -> Poly:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Rat(0)) + scale * v
        if out[k] == 0:
            del out[k]
    return out


def poly_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ea, va in a.items():
        for eb, vb in b.items():
            exp = tuple(ea[i] + eb[i] for i in range(len(ea)))
            if sum(exp) > 2:
                raise ValueError("degree exceeded quadratic")
            out[exp] = out.get(exp, Rat(0)) + va * vb
    return {k: v for k, v in out.items() if v}


def poly_eval(poly: Poly, p: Point) -> Rat:
    total = Rat(0)
    for exp, coef in poly.items():
        term = coef
        for i, e in enumerate(exp):
            if e == 1:
                term *= p[i]
            elif e == 2:
                term *= p[i] * p[i]
        total += term
    return total


def union_expression_on_slab(n: int, sample: Point, y_mid: Rat) -> Tuple[List[Rat], Rat, Rat]:
    lines = endpoint_affines(n)
    intervals = []
    for j in range(1, n + 1):
        li = 2 * (j - 1)
        ri = li + 1
        lv = affine_endpoint_value(n, li, sample, y_mid)
        rv = affine_endpoint_value(n, ri, sample, y_mid)
        intervals.append((lv, rv, li, ri))
    intervals.sort(key=lambda row: (row[0], row[1], row[2], row[3]))
    clusters: List[Tuple[int, int]] = []
    cur_l: Optional[int] = None
    cur_r: Optional[int] = None
    cur_rv: Optional[Rat] = None
    for lv, rv, li, ri in intervals:
        if cur_l is None:
            cur_l, cur_r, cur_rv = li, ri, rv
        elif lv <= cur_rv:
            if rv > cur_rv:
                cur_r, cur_rv = ri, rv
        else:
            clusters.append((cur_l, cur_r))  # type: ignore[arg-type]
            cur_l, cur_r, cur_rv = li, ri, rv
    if cur_l is not None:
        clusters.append((cur_l, cur_r))  # type: ignore[arg-type]
    d = len(sample)
    a = [Rat(0) for _ in range(d)]
    b = Rat(0)
    cy = Rat(0)
    for li, ri in clusters:
        ar, br, sr, _ = lines[ri]
        al, bl, sl, _ = lines[li]
        for k in range(d):
            a[k] += ar[k] - al[k]
        b += br - bl
        cy += sr - sl
    return a, b, cy


def schedule_quadratic_exact(n: int, sample: Point) -> Poly:
    d = len(sample)
    events = event_affines_frac(n)
    vals = [(sum(a[i] * sample[i] for i in range(d)) + c, a, c) for a, c, _ in events]
    active = [(v, a, c) for v, a, c in vals if Rat(0) < v < Rat(1)]
    active.sort(key=lambda row: row[0])
    breaks = [(Rat(0), [Rat(0) for _ in range(d)], Rat(0))] + active + [(Rat(1), [Rat(0) for _ in range(d)], Rat(1))]
    poly: Poly = {}
    for left, right in zip(breaks, breaks[1:]):
        v0, a0, c0 = left
        v1, a1, c1 = right
        if v0 == v1:
            continue
        y_mid = (v0 + v1) / 2
        u_a, u_b, u_cy = union_expression_on_slab(n, sample, y_mid)
        h0 = poly_affine(a0, c0)
        h1 = poly_affine(a1, c1)
        dh = poly_add(h1, h0, scale=-1)
        term = poly_mul(poly_affine(u_a, u_b), dh)
        h1_sq = poly_mul(h1, h1)
        h0_sq = poly_mul(h0, h0)
        yterm = poly_add(h1_sq, h0_sq, scale=-1)
        yterm = {k: u_cy * v / 2 for k, v in yterm.items()}
        poly = poly_add(poly, term)
        poly = poly_add(poly, yterm)
    return poly


def poly_gradient_linear(poly: Poly, d: int) -> Tuple[List[List[Rat]], List[Rat]]:
    mat = [[Rat(0) for _ in range(d)] for _ in range(d)]
    vec = [Rat(0) for _ in range(d)]
    for exp, coef in poly.items():
        for i in range(d):
            if exp[i] == 0:
                continue
            new_exp = list(exp)
            new_exp[i] -= 1
            deriv_coef = coef * exp[i]
            if sum(new_exp) == 0:
                vec[i] += deriv_coef
            else:
                j = new_exp.index(1)
                mat[i][j] += deriv_coef
    return mat, vec


def solve_linear(mat: List[List[Rat]], rhs: List[Rat]) -> Optional[Point]:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(mat)]
    pivots = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if aug[i][c] != 0), None)
        if piv is None:
            continue
        aug[r], aug[piv] = aug[piv], aug[r]
        pv = aug[r][c]
        aug[r] = [v / pv for v in aug[r]]
        for i in range(n):
            if i != r and aug[i][c] != 0:
                f = aug[i][c]
                aug[i] = [aug[i][j] - f * aug[r][j] for j in range(n + 1)]
        pivots.append(c)
        r += 1
    if r < n:
        return None
    sol = [Rat(0) for _ in range(n)]
    for row, c in enumerate(pivots):
        sol[c] = aug[row][-1]
    return tuple(sol)


def feasible(hypers: Sequence[Hyper], signs: Tuple[int, ...], p: Point) -> bool:
    return all(s * hyper_value(h, p) >= 0 for h, s in zip(hypers, signs))


def q1_coeffs(poly: Poly) -> Tuple[Rat, Rat, Rat]:
    return poly.get((2,), Rat(0)), poly.get((1,), Rat(0)), poly.get((0,), Rat(0))


def minimize_cell_1d(poly: Poly, points: Sequence[Hyper], signs: Tuple[int, ...]) -> Tuple[Rat, Point]:
    lo: Optional[Rat] = None
    hi: Optional[Rat] = None
    for h, s in zip(points, signs):
        a, c = h
        p = -c / a
        if s * a > 0:
            lo = p if lo is None or p > lo else lo
        else:
            hi = p if hi is None or p < hi else hi
    candidates: List[Point] = []
    if lo is not None:
        candidates.append((lo,))
    if hi is not None:
        candidates.append((hi,))
    a, b, _ = q1_coeffs(poly)
    if a > 0:
        candidates.append((-b / (2 * a),))
    if (a == 0 and b == 0) or (lo is None and hi is None):
        candidates.append((Rat(0),))
    best: Optional[Tuple[Rat, Point]] = None
    for p in candidates:
        if feasible(points, signs, p):
            val = poly_eval(poly, p)
            if best is None or val < best[0]:
                best = (val, p)
    if best is None:
        raise RuntimeError("no 1D minimizer candidate")
    return best


def line_interval(lines: Sequence[Hyper], signs: Tuple[int, ...], boundary_idx: int) -> Tuple[Point, Point, Optional[Rat], Optional[Rat]]:
    a, b, c = lines[boundary_idx]
    if b != 0:
        p0 = (Rat(0), -c / b)
    else:
        p0 = (-c / a, Rat(0))
    direction = (b, -a)
    lo: Optional[Rat] = None
    hi: Optional[Rat] = None
    for idx, (line, s) in enumerate(zip(lines, signs)):
        if idx == boundary_idx:
            continue
        aa, bb, cc = line
        alpha = s * (aa * direction[0] + bb * direction[1])
        beta = s * (aa * p0[0] + bb * p0[1] + cc)
        if alpha == 0:
            if beta < 0:
                return p0, direction, Rat(1), Rat(0)
            continue
        bound = -beta / alpha
        if alpha > 0:
            lo = bound if lo is None or bound > lo else lo
        else:
            hi = bound if hi is None or bound < hi else hi
    return p0, direction, lo, hi


def restrict_poly_to_line(poly: Poly, p0: Point, direction: Point) -> Tuple[Rat, Rat, Rat]:
    vals = []
    for t in (Rat(0), Rat(1), Rat(2)):
        p = tuple(p0[i] + t * direction[i] for i in range(len(p0)))
        vals.append(poly_eval(poly, p))
    c = vals[0]
    a = (vals[2] - 2 * vals[1] + vals[0]) / 2
    b = vals[1] - vals[0] - a
    return a, b, c


def minimize_cell_2d(
    poly: Poly,
    lines: Sequence[Hyper],
    signs: Tuple[int, ...],
    boundary_indices: Optional[Sequence[int]] = None,
) -> Tuple[Rat, Point]:
    candidates: List[Point] = []
    mat, vec = poly_gradient_linear(poly, 2)
    stat = solve_linear(mat, [-vec[0], -vec[1]])
    if stat is not None:
        candidates.append(stat)
    if not lines and stat is None:
        candidates.append((Rat(0), Rat(0)))
    indices = list(boundary_indices) if boundary_indices is not None else list(range(len(lines)))
    for i in indices:
        p0, direction, lo, hi = line_interval(lines, signs, i)
        if lo is not None and hi is not None and lo > hi:
            continue
        a, b, _ = restrict_poly_to_line(poly, p0, direction)
        ts: List[Rat] = []
        if lo is not None:
            ts.append(lo)
        if hi is not None:
            ts.append(hi)
        if a > 0:
            t0 = -b / (2 * a)
            if (lo is None or t0 >= lo) and (hi is None or t0 <= hi):
                ts.append(t0)
        elif a == 0 and b == 0:
            if lo is not None:
                ts.append(lo)
            elif hi is not None:
                ts.append(hi)
            else:
                ts.append(Rat(0))
        for t in ts:
            candidates.append((p0[0] + t * direction[0], p0[1] + t * direction[1]))
    best: Optional[Tuple[Rat, Point]] = None
    for p in candidates:
        if feasible(lines, signs, p):
            val = poly_eval(poly, p)
            if best is None or val < best[0]:
                best = (val, p)
    if best is None:
        raise RuntimeError("no 2D minimizer candidate")
    return best


def restrict_poly_affine(poly: Poly, p0: Point, dirs: Sequence[Point]) -> Poly:
    k = len(dirs)
    out: Poly = {}
    d = len(p0)
    for exp, coef in poly.items():
        terms: Poly = {(0,) * k: coef}
        for i in range(d):
            power = exp[i]
            if power == 0:
                continue
            aff: Poly = {(0,) * k: p0[i]} if p0[i] else {}
            for j, direction in enumerate(dirs):
                if direction[i]:
                    e = [0] * k
                    e[j] = 1
                    aff[tuple(e)] = aff.get(tuple(e), Rat(0)) + direction[i]
            if power == 1:
                terms = poly_mul(terms, aff)
            elif power == 2:
                terms = poly_mul(poly_mul(terms, aff), aff)
        out = poly_add(out, terms)
    return out


def hyperplane_param(h: Hyper) -> Tuple[Point, List[Point]]:
    d = len(h) - 1
    coeff = h[:-1]
    const = h[-1]
    pivot = next(i for i, a in enumerate(coeff) if a != 0)
    p0 = [Rat(0) for _ in range(d)]
    p0[pivot] = -const / coeff[pivot]
    dirs: List[Point] = []
    for free in range(d):
        if free == pivot:
            continue
        v = [Rat(0) for _ in range(d)]
        v[free] = Rat(1)
        v[pivot] = -coeff[free] / coeff[pivot]
        dirs.append(tuple(v))
    return tuple(p0), dirs


def minimize_cell(
    poly: Poly,
    hypers: Sequence[Hyper],
    signs: Tuple[int, ...],
    dim: Optional[int] = None,
    boundary_indices: Optional[Sequence[int]] = None,
) -> Tuple[Rat, Point]:
    d = dim if dim is not None else (len(next(iter(poly.keys()))) if poly else len(hypers[0]) - 1)
    if d == 1:
        return minimize_cell_1d(poly, hypers, signs)
    if d == 2:
        return minimize_cell_2d(poly, hypers, signs, boundary_indices=boundary_indices)
    candidates: List[Point] = []
    mat, vec = poly_gradient_linear(poly, d)
    stat = solve_linear(mat, [-v for v in vec])
    if stat is not None:
        candidates.append(stat)
    indices = list(boundary_indices) if boundary_indices is not None else list(range(len(hypers)))
    for idx in indices:
        h = hypers[idx]
        p0, dirs = hyperplane_param(h)
        sub_poly = restrict_poly_affine(poly, p0, dirs)
        sub_hypers: List[Hyper] = []
        sub_signs: List[int] = []
        sub_boundary: List[int] = []
        infeasible_face = False
        for j, hh in enumerate(hypers):
            if j == idx:
                continue
            coeff = [sum(hh[i] * direction[i] for i in range(d)) for direction in dirs]
            const = hyper_value(hh, p0)
            canon_row = canonical_hyper_with_sign(coeff + [const])
            if canon_row is None:
                if signs[j] * const < 0:
                    infeasible_face = True
                    break
            else:
                canon, orient = canon_row
                sub_idx = len(sub_hypers)
                sub_hypers.append(canon)
                sub_signs.append(signs[j] * orient)
                if boundary_indices is not None and j in boundary_indices:
                    sub_boundary.append(sub_idx)
        if infeasible_face:
            continue
        if len(dirs) == 0:
            candidates.append(p0)
        else:
            try:
                sub_val, sub_p = minimize_cell(
                    sub_poly,
                    sub_hypers,
                    tuple(sub_signs),
                    dim=len(dirs),
                    boundary_indices=sub_boundary if boundary_indices is not None else None,
                )
            except RuntimeError:
                continue
            del sub_val
            candidates.append(tuple(p0[i] + sum(sub_p[j] * dirs[j][i] for j in range(len(dirs))) for i in range(d)))
    best: Optional[Tuple[Rat, Point]] = None
    for p in candidates:
        if feasible(hypers, signs, p):
            val = poly_eval(poly, p)
            if best is None or val < best[0]:
                best = (val, p)
    if best is None:
        raise RuntimeError("no exact minimizer candidate")
    return best


def map_affine_point(p0: Point, dirs: Sequence[Point], q: Point) -> Point:
    return tuple(p0[i] + sum(q[j] * dirs[j][i] for j in range(len(dirs))) for i in range(len(p0)))


def enumerate_cells_4d(hypers: Sequence[Hyper], deadline: Optional[float] = None) -> Tuple[Dict[Tuple[int, ...], Point], bool]:
    cells: Dict[Tuple[int, ...], Point] = {}
    for plane_idx, plane in enumerate(hypers):
        if deadline is not None and time.time() > deadline:
            return cells, False
        p0, dirs = hyperplane_param(plane)
        induced: List[Hyper] = []
        seen = set()
        for idx, h in enumerate(hypers):
            if idx == plane_idx:
                continue
            coeff = [sum(h[i] * direction[i] for i in range(4)) for direction in dirs]
            const = hyper_value(h, p0)
            canon = canonical_hyper(coeff + [const])
            if canon is None:
                continue
            if canon not in seen:
                seen.add(canon)
                induced.append(canon)
        induced.sort()
        face_cells, ok = enumerate_cells_3d(induced, deadline=deadline)
        if not ok:
            return cells, False
        normal = plane[:-1]
        for q in face_cells.values():
            base = map_affine_point(p0, dirs, q)
            eps_limit: Optional[Rat] = None
            for idx, h in enumerate(hypers):
                if idx == plane_idx:
                    continue
                val = hyper_value(h, base)
                delta = sum(h[i] * normal[i] for i in range(4))
                if delta != 0:
                    bound = abs(val / delta) / 2
                    if bound > 0 and (eps_limit is None or bound < eps_limit):
                        eps_limit = bound
            eps = eps_limit if eps_limit is not None else Rat(1, 2)
            if eps == 0:
                continue
            for side in (-1, 1):
                p = tuple(base[i] + side * eps * normal[i] for i in range(4))
                try:
                    sv = sign_vector(hypers, p)
                except ValueError:
                    continue
                cells.setdefault(sv, p)
    return cells, True


def sigma_params(n: int, p: Point) -> Point:
    if len(p) != n - 1:
        raise ValueError("wrong sigma parameter dimension")
    x1 = p[0]
    full = list(p) + [Rat(0)]
    return tuple(x1 - full[n - j] for j in range(1, n))


def sigma_orbit_report(n: int, hypers: Sequence[Hyper], cells: Dict[Tuple[int, ...], Point]) -> Dict[str, object]:
    mapped_missing = 0
    non_involutive = 0
    fixed = 0
    reps = set()
    sample_checks = []
    for signs, sample in cells.items():
        sp = sigma_params(n, sample)
        mapped = sign_vector(hypers, sp)
        if mapped not in cells:
            mapped_missing += 1
        if sign_vector(hypers, sigma_params(n, sp)) != signs:
            non_involutive += 1
        if mapped == signs:
            fixed += 1
        reps.add(min(signs, mapped))
        if len(sample_checks) < 3:
            a0 = exact_area_offsets(n, offsets_from_params(n, sample))
            a1 = exact_area_offsets(n, offsets_from_params(n, sp))
            sample_checks.append({"area": frac_json(a0), "sigma_area": frac_json(a1), "matches": a0 == a1})
    return {
        "enabled": True,
        "orbit_representative_count": len(reps),
        "fixed_cell_count": fixed,
        "mapped_missing_count": mapped_missing,
        "non_involutive_count": non_involutive,
        "sample_area_checks": sample_checks,
        "bijection_verified": mapped_missing == 0 and non_involutive == 0,
    }


def unconstrained_stationary_value(poly: Poly, d: int) -> Optional[Tuple[Rat, Point]]:
    mat, vec = poly_gradient_linear(poly, d)
    stat = solve_linear(mat, [-v for v in vec])
    if stat is None:
        return None
    return poly_eval(poly, stat), stat


def certify_fullspace_exact(
    n: int,
    deadline: Optional[float] = None,
    incumbent: Optional[Rat] = None,
    use_sigma_orbits: bool = False,
) -> Dict[str, object]:
    start = time.time()
    hypers = arrangement_hyperplanes(n)
    d = n - 1
    if d == 1:
        cells = enumerate_cells_1d(hypers)
        complete = True
    elif d == 2:
        cells = enumerate_cells_2d(hypers)
        complete = True
    elif d == 3:
        cells, complete = enumerate_cells_3d(hypers, deadline=deadline)
    elif d == 4:
        cells, complete = enumerate_cells_4d(hypers, deadline=deadline)
    else:
        raise ValueError("fullspace exact certifier currently supports dimensions <= 4")

    best_val: Optional[Rat] = None
    best_params: Optional[Point] = None
    sample_mismatches = []
    processed = 0
    pruned = 0
    degenerate_unconstrained = 0
    reps_skipped = 0
    cell_sign_set = set(cells)
    sigma_report: Dict[str, object] = {"enabled": False}
    if use_sigma_orbits:
        sigma_report = sigma_orbit_report(n, hypers, cells)
        if not sigma_report["bijection_verified"]:
            use_sigma_orbits = False
    visited_or_represented = 0
    for signs, sample in cells.items():
        if deadline is not None and time.time() > deadline:
            complete = False
            break
        if use_sigma_orbits:
            mapped = sign_vector(hypers, sigma_params(n, sample))
            if signs != min(signs, mapped):
                reps_skipped += 1
                continue
        visited_or_represented += 1
        poly = schedule_quadratic_exact(n, sample)
        sample_area = exact_area_offsets(n, offsets_from_params(n, sample))
        formula_area = poly_eval(poly, sample)
        if sample_area != formula_area:
            sample_mismatches.append(
                {"sample": [frac_json(x) for x in sample], "sweep": frac_json(sample_area), "formula": frac_json(formula_area)}
            )
            continue
        stat = unconstrained_stationary_value(poly, d)
        if incumbent is not None and stat is not None and stat[0] > incumbent:
            pruned += 1
            processed += 1
            continue
        if stat is None:
            degenerate_unconstrained += 1
        boundary_indices = None
        if d == 3 and complete:
            local = []
            for idx in range(len(hypers)):
                flipped = list(signs)
                flipped[idx] *= -1
                if tuple(flipped) in cell_sign_set:
                    local.append(idx)
            boundary_indices = local
        if d == 4 and complete:
            local = []
            for idx in range(len(hypers)):
                flipped = list(signs)
                flipped[idx] *= -1
                if tuple(flipped) in cell_sign_set:
                    local.append(idx)
            boundary_indices = local
        val, params = minimize_cell(poly, hypers, signs, dim=d, boundary_indices=boundary_indices)
        if best_val is None or val < best_val:
            best_val, best_params = val, params
        processed += 1
    if sample_mismatches:
        raise RuntimeError(f"quadratic/sweep mismatch in {len(sample_mismatches)} cells")
    if best_val is None or best_params is None:
        if incumbent is not None:
            best_val = incumbent
            best_params = tuple(Rat(0) for _ in range(d))
        else:
            raise RuntimeError("no cells processed")
    best_offsets = offsets_from_params(n, best_params)
    best_sweep = exact_area_offsets(n, best_offsets)
    plateau_checks: List[Dict[str, object]] = []
    if n == 4:
        for c in (Rat(1, 20), Rat(7, 80), Rat(1, 8)):
            off = [Rat(1, 4), Rat(1, 4) - c, c, Rat(0)]
            plateau_checks.append({"c": frac_json(c), "area": frac_json(exact_area_offsets(4, off))})
    return {
        "n": n,
        "dimension": d,
        "area": frac_json(best_val),
        "area_float": float(best_val),
        "params_xn_zero": [frac_json(x) for x in best_params],
        "offsets_normalized": [frac_json(x) for x in normalize_offsets(best_offsets)],
        "exact_sweep_at_min": frac_json(best_sweep),
        "min_formula_matches_sweep": best_sweep == best_val,
        "complete": complete,
        "completion_scope": "full_unbounded_parameter_arrangement" if complete else "partial_full_unbounded_parameter_arrangement",
        "cell_count": len(cells),
        "processed_cell_count": processed,
        "orbit_representatives_visited": visited_or_represented,
        "sigma_orbit_reduction": sigma_report,
        "cell_orbit_representatives_skipped": reps_skipped,
        "incumbent_pruned_cell_count": pruned,
        "fully_minimized_cell_count": processed - pruned,
        "degenerate_unconstrained_cell_count": degenerate_unconstrained,
        "incumbent": frac_json(incumbent) if incumbent is not None else None,
        "hyperplane_count": len(hypers),
        "quadratic_sweep_match_count": processed,
        "plateau_checks": plateau_checks,
        "wall_clock": time.time() - start,
    }