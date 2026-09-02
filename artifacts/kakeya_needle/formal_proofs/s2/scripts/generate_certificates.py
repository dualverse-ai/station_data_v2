#!/usr/bin/env python3
"""Generate exact finite certificate payloads for the Kakeya needle results.

This program is intentionally only a witness finder.  Every affine implication,
empty-polyhedron assertion, sweep schedule, and quadratic lower bound emitted by
it is replayed by the Lean checkers using exact rational arithmetic.

The generated polyhedron for a leaf has a fixed number of constraints, in this
order:

* the balanced decision-tree path, padded by the constant inequality ``1 >= 0``;
* ``1 + x_i >= 0`` and ``1 - x_i >= 0`` for every free coordinate;
* ``x_last >= 0`` and ``-x_last >= 0`` (the translation gauge).

The reference enumerator works in the gauge ``x_last = 0``.  Arrangement walls
and event heights are lifted to all ``n`` coordinates in translation-invariant
form, replacing ``z_i`` by ``x_i - x_last``.
"""

from __future__ import annotations

import argparse
import base64
import itertools
import json
import math
import random
import shutil
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import linprog

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import reference_enumerator as ref  # noqa: E402


Q = Fraction
Affine = Tuple[Q, ...]  # linear coefficients, followed by the constant
Sparse = List[Tuple[int, Q]]
Poly = Dict[Tuple[int, ...], Q]


@dataclass(frozen=True)
class TreeNode:
    wall: Optional[int] = None
    positive: Optional[int] = None
    negative: Optional[int] = None
    leaf: Optional[int] = None


@dataclass
class SlabData:
    order: Tuple[int, ...]
    overlap: Tuple[bool, ...]
    order_certificates: List[Sparse]
    overlap_certificates: List[Sparse]


@dataclass
class SweepData:
    breakpoints: List[Affine]
    breakpoint_certificates: List[Sparse]
    slabs: List[SlabData]


@dataclass
class LeafData:
    path: List[Tuple[int, int]]
    empty: Optional[Sparse]
    sweep: Optional[SweepData]
    handelman: Optional[List[Tuple[int, int, Q]]]
    squares: Optional[List[Tuple[Q, Affine]]] = None


def sigma5_offsets(params: Sequence[Q]) -> List[Q]:
    """Notebook Theorem 3.5 gauge: (a,b,a/2,a-b,0)."""
    if len(params) != 2:
        raise ValueError("the reflection-fixed n=5 family has two parameters")
    a, b = map(Q, params)
    return [a, b, a / 2, a - b, Q(0)]


def sigma5_endpoint_affines() -> List[Tuple[List[Q], Q, Q]]:
    rows: List[Tuple[List[Q], Q, Q]] = []
    for j in range(1, 6):
        values = []
        for k in range(2):
            unit = [Q(0), Q(0)]
            unit[k] = Q(1)
            values.append(sigma5_offsets(unit)[j - 1])
        rows.append((values[:], Q(0), Q(j, 5)))
        rows.append((values[:], Q(1, 5), Q(j - 1, 5)))
    return rows


def sigma5_event_affines() -> List[Tuple[List[Q], Q]]:
    lines = sigma5_endpoint_affines()
    out: List[Tuple[List[Q], Q]] = []
    for i, (ai, bi, si) in enumerate(lines):
        for aj, bj, sj in lines[i + 1:]:
            if si == sj:
                continue
            den = si - sj
            out.append(([(aj[k] - ai[k]) / den for k in range(2)],
                        (bj - bi) / den))
    return out


def sigma5_arrangement() -> List[Affine]:
    events = sigma5_event_affines()
    raw: List[Affine] = []
    for a, c in events:
        raw.extend([tuple(a + [c]), tuple(a + [c - 1])])
    for i, (ai, ci) in enumerate(events):
        for aj, cj in events[i + 1:]:
            raw.append((ai[0] - aj[0], ai[1] - aj[1], ci - cj))
    result = {ref.canonical_hyper(row) for row in raw}
    return sorted(row for row in result if row is not None)


def poly_affine(coefficients: Sequence[Q], constant: Q) -> Poly:
    d = len(coefficients)
    out: Poly = {}
    if constant:
        out[(0,) * d] = constant
    for i, coefficient in enumerate(coefficients):
        if coefficient:
            exponent = [0] * d
            exponent[i] = 1
            out[tuple(exponent)] = coefficient
    return out


def poly_add(a: Poly, b: Poly, scale: Q = Q(1)) -> Poly:
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, Q(0)) + scale * coefficient
        if out[exponent] == 0:
            del out[exponent]
    return out


def poly_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            exponent = tuple(ea[i] + eb[i] for i in range(len(ea)))
            out[exponent] = out.get(exponent, Q(0)) + ca * cb
    return {e: c for e, c in out.items() if c != 0}


def poly_eval(poly: Poly, point: Sequence[Q]) -> Q:
    total = Q(0)
    for exponent, coefficient in poly.items():
        term = coefficient
        for i, power in enumerate(exponent):
            term *= point[i] ** power
        total += term
    return total


def sigma5_schedule_quadratic(sample: Sequence[Q]) -> Poly:
    """Exact area quadratic on one cell in the notebook's (a,b)-plane."""
    lines = sigma5_endpoint_affines()
    events = sigma5_event_affines()
    vals = [(sum(a[i] * sample[i] for i in range(2)) + c, a, c)
            for a, c in events]
    active = sorted((row for row in vals if 0 < row[0] < 1), key=lambda r: r[0])
    breaks = [(Q(0), [Q(0), Q(0)], Q(0))] + active + [
        (Q(1), [Q(0), Q(0)], Q(1))]
    poly: Poly = {}
    for left, right in zip(breaks, breaks[1:]):
        v0, a0, c0 = left
        v1, a1, c1 = right
        if v0 == v1:
            continue
        ymid = (v0 + v1) / 2
        intervals = []
        for j in range(5):
            li, ri = 2 * j, 2 * j + 1
            def value(index: int) -> Q:
                aa, cc, slope = lines[index]
                return sum(aa[k] * sample[k] for k in range(2)) + cc + slope * ymid
            intervals.append((value(li), value(ri), li, ri))
        intervals.sort()
        clusters: List[Tuple[int, int]] = []
        cur_l = cur_r = None
        cur_rv = None
        for lv, rv, li, ri in intervals:
            if cur_l is None:
                cur_l, cur_r, cur_rv = li, ri, rv
            elif lv <= cur_rv:
                if rv > cur_rv:
                    cur_r, cur_rv = ri, rv
            else:
                clusters.append((cur_l, cur_r))
                cur_l, cur_r, cur_rv = li, ri, rv
        if cur_l is not None:
            clusters.append((cur_l, cur_r))
        ua = [Q(0), Q(0)]
        ub = uy = Q(0)
        for li, ri in clusters:
            ar, br, sr = lines[ri]
            al, bl, sl = lines[li]
            ua = [ua[k] + ar[k] - al[k] for k in range(2)]
            ub += br - bl
            uy += sr - sl
        h0, h1 = poly_affine(a0, c0), poly_affine(a1, c1)
        dh = poly_add(h1, h0, scale=-1)
        poly = poly_add(poly, poly_mul(poly_affine(ua, ub), dh))
        squares = poly_add(poly_mul(h1, h1), poly_mul(h0, h0), scale=-1)
        poly = poly_add(poly, {e: uy * v / 2 for e, v in squares.items()})
    return poly


def qstr(x: Q) -> str:
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"(({x.numerator} : ℚ) / {x.denominator})"


def affine_add(a: Affine, b: Affine) -> Affine:
    return tuple(x + y for x, y in zip(a, b))


def affine_scale(c: Q, a: Affine) -> Affine:
    return tuple(c * x for x in a)


def affine_sub(a: Affine, b: Affine) -> Affine:
    return affine_add(a, affine_scale(Q(-1), b))


def affine_eval(a: Affine, x: Sequence[Q]) -> Q:
    return sum(a[i] * x[i] for i in range(len(x))) + a[-1]


def lift_gauge_affine(a: Affine) -> Affine:
    """Lift a(z_0,...,z_{d-1}) using z_i=x_i-x_last."""
    linear = list(a[:-1])
    return tuple(linear + [-sum(linear), a[-1]])


def full_sample(sample: Sequence[Q]) -> Tuple[Q, ...]:
    return tuple(sample) + (Q(0),)


def coordinate_affine(n: int, i: int) -> Affine:
    row = [Q(0)] * n
    row[i] = Q(1)
    return tuple(row + [Q(0)])


def constant_affine(n: int, c: Q) -> Affine:
    return tuple([Q(0)] * n + [c])


def left_line(n: int, j: int) -> Tuple[Affine, Q]:
    return coordinate_affine(n, j), Q(j + 1, n)


def selected_endpoint(base: Affine, slope: Q, lo: Affine, hi: Affine) -> Affine:
    return affine_add(base, affine_scale(slope, lo if slope >= 0 else hi))


def monomials(d: int) -> List[Tuple[int, ...]]:
    zero = (0,) * d
    out = [zero]
    for i in range(d):
        e = [0] * d
        e[i] = 1
        out.append(tuple(e))
    for i in range(d):
        for j in range(i, d):
            e = [0] * d
            e[i] += 1
            e[j] += 1
            out.append(tuple(e))
    return out


def product_vector(g: Affine, h: Affine, d: int, mons: Sequence[Tuple[int, ...]]) -> List[Q]:
    result: Dict[Tuple[int, ...], Q] = {(0,) * d: g[-1] * h[-1]}
    for i in range(d):
        e = [0] * d
        e[i] = 1
        et = tuple(e)
        result[et] = result.get(et, Q(0)) + g[-1] * h[i] + g[i] * h[-1]
    for i in range(d):
        for j in range(d):
            e = [0] * d
            e[i] += 1
            e[j] += 1
            et = tuple(e)
            result[et] = result.get(et, Q(0)) + g[i] * h[j]
    return [result.get(m, Q(0)) for m in mons]


def exact_rref_solution(columns: Sequence[Sequence[Q]], rhs: Sequence[Q],
                        support: Sequence[int]) -> Optional[List[Q]]:
    """Solve A[:,support] x=rhs exactly, setting RREF free variables to zero."""
    rows = len(rhs)
    cols = len(support)
    aug = [[Q(columns[support[j]][i]) for j in range(cols)] + [Q(rhs[i])]
           for i in range(rows)]
    pivot_cols: List[int] = []
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if aug[i][c] != 0), None)
        if pivot is None:
            continue
        aug[r], aug[pivot] = aug[pivot], aug[r]
        p = aug[r][c]
        aug[r] = [v / p for v in aug[r]]
        for i in range(rows):
            if i != r and aug[i][c] != 0:
                f = aug[i][c]
                aug[i] = [aug[i][j] - f * aug[r][j] for j in range(cols + 1)]
        pivot_cols.append(c)
        r += 1
        if r == rows:
            break
    for i in range(r, rows):
        if all(aug[i][c] == 0 for c in range(cols)) and aug[i][-1] != 0:
            return None
    result = [Q(0)] * cols
    for row, c in enumerate(pivot_cols):
        result[c] = aug[row][-1]
    if any(v < 0 for v in result):
        return None
    # Never accept a numerically suggested support without exact replay here.
    for i in range(rows):
        if sum(columns[support[j]][i] * result[j] for j in range(cols)) != rhs[i]:
            return None
    return result


def conic_certificate(target: Affine, constraints: Sequence[Affine], tries: int = 12) -> Optional[Sparse]:
    """Find target=sum lambda_i constraints_i, lambda_i>=0, exactly."""
    if all(v == 0 for v in target):
        return []
    # Most sweep implications are literally a positive multiple of one path wall.
    for i, g in enumerate(constraints):
        nz = next((k for k, v in enumerate(g) if v != 0), None)
        if nz is None:
            continue
        ratio = target[nz] / g[nz]
        if ratio >= 0 and all(target[k] == ratio * g[k] for k in range(len(target))):
            return [] if ratio == 0 else [(i, ratio)]

    cols = [[g[-1]] + list(g[:-1]) for g in constraints]
    rhs = [target[-1]] + list(target[:-1])
    A = np.asarray([[float(c[i]) for c in cols] for i in range(len(rhs))])
    b = np.asarray([float(v) for v in rhs])
    for attempt in range(tries):
        rng = np.random.default_rng(0xC0DE + attempt)
        objective = rng.random(len(cols)) * (10.0 ** (-7 - attempt % 3))
        result = linprog(objective, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
        if not result.success:
            continue
        for threshold in (1e-8, 1e-10, 1e-12):
            support = [i for i, v in enumerate(result.x) if v > threshold]
            exact = exact_rref_solution(cols, rhs, support)
            if exact is not None:
                return [(i, v) for i, v in zip(support, exact) if v != 0]
    return None


def closed_infeasibility_certificate(constraints: Sequence[Affine]) -> Optional[Sparse]:
    n = len(constraints[0]) - 1
    target = tuple([Q(0)] * n + [Q(-1)])
    return conic_certificate(target, constraints, tries=20)


def float_feasible(constraints: Sequence[Affine]) -> bool:
    d = len(constraints[0]) - 1
    A_ub = np.asarray([[-float(v) for v in g[:-1]] for g in constraints])
    b_ub = np.asarray([float(g[-1]) for g in constraints])
    result = linprog(np.zeros(d), A_ub=A_ub, b_ub=b_ub,
                     bounds=[(None, None)] * d, method="highs")
    return bool(result.success)


def handelman_certificate(poly: Poly, target: Q, constraints: Sequence[Affine],
                          tries: int = 20) -> Optional[List[Tuple[int, int, Q]]]:
    d = len(constraints[0]) - 1
    mons = monomials(d)
    one = constant_affine(d, Q(1))
    generators = [one] + list(constraints)
    pairs = list(itertools.combinations_with_replacement(range(len(generators)), 2))
    cols = [product_vector(generators[i], generators[j], d, mons) for i, j in pairs]
    rhs = [poly.get(m, Q(0)) - (target if k == 0 else 0)
           for k, m in enumerate(mons)]
    A = np.asarray([[float(c[i]) for c in cols] for i in range(len(rhs))])
    b = np.asarray([float(v) for v in rhs])
    for attempt in range(tries):
        rng = np.random.default_rng(0x5EED + attempt)
        objective = rng.random(len(cols)) * (10.0 ** (-7 - attempt % 3))
        result = linprog(objective, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
        if not result.success:
            continue
        for threshold in (1e-8, 1e-10, 1e-12):
            support = [i for i, v in enumerate(result.x) if v > threshold]
            exact = exact_rref_solution(cols, rhs, support)
            if exact is not None:
                return [(pairs[i][0], pairs[i][1], v)
                        for i, v in zip(support, exact) if v != 0]
    return None


def global_sos_certificate(poly: Poly, target: Q, d: int) -> Optional[List[Tuple[Q, Affine]]]:
    """Exact weighted-affine-square decomposition of a globally PSD quadratic.

    Returns ``[(w,l), ...]`` with ``q-target=sum w*l^2`` and ``w>0``.
    Rational positive-semidefinite matrices admit this rational LDL-style
    decomposition; no square roots are introduced.
    """
    mons = monomials(d)
    coeff = {m: poly.get(m, Q(0)) - (target if m == (0,) * d else 0)
             for m in mons}
    size = d + 1  # variables followed by the affine constant coordinate
    matrix = [[Q(0) for _ in range(size)] for _ in range(size)]
    for i in range(d):
        e = [0] * d
        e[i] = 2
        matrix[i][i] = coeff[tuple(e)]
        e[i] = 1
        matrix[i][-1] = matrix[-1][i] = coeff[tuple(e)] / 2
    for i in range(d):
        for j in range(i + 1, d):
            e = [0] * d
            e[i] = e[j] = 1
            matrix[i][j] = matrix[j][i] = coeff[tuple(e)] / 2
    matrix[-1][-1] = coeff[(0,) * d]

    result: List[Tuple[Q, Affine]] = []
    while True:
        pivot = next((i for i in range(size) if matrix[i][i] > 0), None)
        if pivot is None:
            if any(matrix[i][j] != 0 for i in range(size) for j in range(size)):
                return None
            break
        p = matrix[pivot][pivot]
        row = [matrix[pivot][j] / p for j in range(size)]
        # row·[x,1] is the affine factor.
        result.append((p, tuple(row[:d] + [row[-1]])))
        for i in range(size):
            for j in range(size):
                matrix[i][j] -= p * row[i] * row[j]
        # A negative diagonal proves the original matrix was not PSD.
        if any(matrix[i][i] < 0 for i in range(size)):
            return None

    # Exact coefficient replay of the resulting squares.
    square_poly = [Q(0)] * len(mons)
    for weight, affine in result:
        column = product_vector(affine, affine, d, mons)
        square_poly = [a + weight * b for a, b in zip(square_poly, column)]
    expected = [coeff[m] for m in mons]
    if square_poly != expected:
        raise AssertionError("internal exact SOS replay failed")
    return result


def gauge_substitute_poly(poly: Poly, old_d: int) -> Poly:
    """Substitute z_i=x_i-x_last in a quadratic over old_d variables."""
    out: Poly = {}

    def add(exp: Sequence[int], c: Q) -> None:
        et = tuple(exp)
        out[et] = out.get(et, Q(0)) + c

    for exp, coefficient in poly.items():
        variables: List[int] = []
        for i, power in enumerate(exp):
            variables.extend([i] * power)
        if not variables:
            add([0] * (old_d + 1), coefficient)
        elif len(variables) == 1:
            e = [0] * (old_d + 1)
            e[variables[0]] = 1
            add(e, coefficient)
            e = [0] * (old_d + 1)
            e[old_d] = 1
            add(e, -coefficient)
        else:
            i, j = variables
            for u, cu in ((i, Q(1)), (old_d, Q(-1))):
                for v, cv in ((j, Q(1)), (old_d, Q(-1))):
                    e = [0] * (old_d + 1)
                    e[u] += 1
                    e[v] += 1
                    add(e, coefficient * cu * cv)
    return {e: c for e, c in out.items() if c != 0}


def cube_and_gauge_constraints(n: int) -> List[Affine]:
    out: List[Affine] = []
    for i in range(n - 1):
        plus = [Q(0)] * n
        plus[i] = 1
        out.append(tuple(plus + [Q(1)]))
        minus = [Q(0)] * n
        minus[i] = -1
        out.append(tuple(minus + [Q(1)]))
    gauge_plus = [Q(0)] * n
    gauge_plus[-1] = 1
    out.append(tuple(gauge_plus + [Q(0)]))
    gauge_minus = [Q(0)] * n
    gauge_minus[-1] = -1
    out.append(tuple(gauge_minus + [Q(0)]))
    return out


def padded_constraints(n: int, walls: Sequence[Affine], path: Sequence[Tuple[int, int]],
                       depth: int) -> List[Affine]:
    constraints = [affine_scale(Q(sign), walls[wall]) for wall, sign in path]
    constraints.extend([constant_affine(n, Q(1))] * (depth - len(path)))
    constraints.extend(cube_and_gauge_constraints(n))
    return constraints


def build_balanced_tree(sign_vectors: Sequence[Tuple[int, ...]]) -> Tuple[List[TreeNode], Dict[int, List[Tuple[int, int]]], int]:
    nodes: List[TreeNode] = []
    paths: Dict[int, List[Tuple[int, int]]] = {}

    def rec(ids: List[int], available: Tuple[int, ...], path: List[Tuple[int, int]]) -> int:
        node_id = len(nodes)
        nodes.append(TreeNode())
        if len(ids) == 1:
            paths[ids[0]] = list(path)
            nodes[node_id] = TreeNode(leaf=ids[0])
            return node_id
        choices = []
        for wall in available:
            positive = sum(sign_vectors[i][wall] > 0 for i in ids)
            if 0 < positive < len(ids):
                choices.append((abs(len(ids) - 2 * positive), wall))
        if not choices:
            raise RuntimeError(f"duplicate sign vectors in unresolved leaf of size {len(ids)}")
        _, wall = min(choices)
        remaining = tuple(i for i in available if i != wall)
        pos_ids = [i for i in ids if sign_vectors[i][wall] > 0]
        neg_ids = [i for i in ids if sign_vectors[i][wall] < 0]
        positive = rec(pos_ids, remaining, path + [(wall, 1)])
        negative = rec(neg_ids, remaining, path + [(wall, -1)])
        nodes[node_id] = TreeNode(wall=wall, positive=positive, negative=negative)
        return node_id

    root = rec(list(range(len(sign_vectors))), tuple(range(len(sign_vectors[0]))), [])
    if root != 0:
        raise AssertionError("preorder tree root is not zero")
    depth = max(map(len, paths.values()))
    return nodes, paths, depth


def sweep_targets(n: int, sample0: Sequence[Q], constraints: Sequence[Affine]) -> SweepData:
    sample = full_sample(sample0)
    events0 = ref.event_affines_frac(n)
    # Multiple endpoint pairs can define the same event height.  Duplicate
    # breakpoints add zero-width slabs and are therefore removed.
    event_forms = sorted({lift_gauge_affine(tuple(a + [c])) for a, c, _ in events0},
                         key=lambda a: affine_eval(a, sample))
    active = [a for a in event_forms if 0 < affine_eval(a, sample) < 1]
    breakpoints = [constant_affine(n, Q(0))] + active + [constant_affine(n, Q(1))]

    breakpoint_certificates: List[Sparse] = []
    slabs: List[SlabData] = []
    certificate_cache: Dict[Affine, Sparse] = {}

    def certify(target: Affine) -> Sparse:
        if target not in certificate_cache:
            cert = conic_certificate(target, constraints)
            if cert is None:
                raise RuntimeError(f"no exact Farkas implication for target {target}")
            certificate_cache[target] = cert
        return certificate_cache[target]

    for lo, hi in zip(breakpoints, breakpoints[1:]):
        breakpoint_certificates.append(certify(affine_sub(hi, lo)))
        y_mid = (affine_eval(lo, sample) + affine_eval(hi, sample)) / 2
        left_values = []
        for j in range(n):
            base, slope = left_line(n, j)
            left_values.append((affine_eval(base, sample) + slope * y_mid, j, base, slope))
        left_values.sort(key=lambda row: (row[0], row[1]))
        order = tuple(row[1] for row in left_values)
        overlap: List[bool] = []
        order_certs: List[Sparse] = []
        overlap_certs: List[Sparse] = []
        for left, right in zip(left_values, left_values[1:]):
            _, _, left_base, left_slope = left
            _, _, right_base, right_slope = right
            gap_base = affine_sub(right_base, left_base)
            gap_slope = right_slope - left_slope
            order_target = selected_endpoint(gap_base, gap_slope, lo, hi)
            order_certs.append(certify(order_target))

            width_base = constant_affine(n, Q(1, n))
            width_slope = Q(-1, n)
            overlap_base = affine_sub(width_base, gap_base)
            overlap_slope = width_slope - gap_slope
            overlap_value = affine_eval(overlap_base, sample) + overlap_slope * y_mid
            does_overlap = overlap_value >= 0
            if not does_overlap:
                overlap_base = affine_scale(Q(-1), overlap_base)
                overlap_slope = -overlap_slope
            overlap_target = selected_endpoint(overlap_base, overlap_slope, lo, hi)
            overlap.append(does_overlap)
            overlap_certs.append(certify(overlap_target))
        slabs.append(SlabData(order, tuple(overlap), order_certs, overlap_certs))
    return SweepData(breakpoints, breakpoint_certificates, slabs)


def generate_leaf(n: int, index: int, signs: Tuple[int, ...], sample: Sequence[Q],
                  path: Sequence[Tuple[int, int]], walls: Sequence[Affine], depth: int) -> LeafData:
    constraints = padded_constraints(n, walls, path, depth)
    if not float_feasible(constraints):
        empty = closed_infeasibility_certificate(constraints)
        if empty is not None:
            return LeafData(list(path), empty, None, None, None)
        # Floating feasibility can reject a lower-dimensional boundary leaf.

    sweep = sweep_targets(n, sample, constraints)
    gauge_poly = ref.schedule_quadratic_exact(n, sample)
    poly = gauge_substitute_poly(gauge_poly, n - 1)
    target = Q(5, 18) if n == 3 else Q(1, 4)
    lower = handelman_certificate(poly, target, constraints)
    squares: List[Tuple[Q, Affine]] = []
    if lower is None:
        sos = global_sos_certificate(poly, target, n)
        if sos is None:
            raise RuntimeError(f"leaf {index}: neither degree-two Handelman nor global SOS certificate")
        lower = []
        squares = sos
    return LeafData(list(path), None, sweep, lower, squares)


def symmetry_gauge_constraints5() -> List[Affine]:
    """Equalities defining the reflection-fixed locus and x_5=0.

    Each equality is represented by both signs, as required by the existing
    nonnegative-polyhedron checker.
    """
    equations = [
        (Q(1), Q(0), Q(-2), Q(0), Q(1), Q(0)),
        (Q(1), Q(-1), Q(0), Q(-1), Q(1), Q(0)),
        (Q(0), Q(0), Q(0), Q(0), Q(1), Q(0)),
    ]
    return [row for equation in equations for row in
            (equation, affine_scale(Q(-1), equation))]


def padded_constraints5(walls: Sequence[Affine], path: Sequence[Tuple[int, int]],
                        depth: int) -> List[Affine]:
    constraints = [affine_scale(Q(sign), walls[wall]) for wall, sign in path]
    constraints.extend([constant_affine(5, Q(1))] * (depth - len(path)))
    constraints.extend(symmetry_gauge_constraints5())
    return constraints


def subtract_weighted_squares(poly: Poly, target: Q,
                              squares: Sequence[Tuple[Q, Affine]], d: int) -> Poly:
    out = dict(poly)
    zero = (0,) * d
    out[zero] = out.get(zero, Q(0)) - target
    mons = monomials(d)
    for weight, affine in squares:
        column = product_vector(affine, affine, d, mons)
        for monomial, value in zip(mons, column):
            out[monomial] = out.get(monomial, Q(0)) - weight * value
    return {e: c for e, c in out.items() if c != 0}


def integrated_sweep_poly5(sweep: SweepData) -> Poly:
    """Mirror `SweepCertificate.integratedQuadratic5` exactly."""
    total: Poly = {}
    for index, slab in enumerate(sweep.slabs):
        intercept = constant_affine(5, Q(1))
        slope = Q(-1)
        for r, overlaps in enumerate(slab.overlap):
            if not overlaps:
                continue
            a, b = slab.order[r], slab.order[r + 1]
            overlap_intercept = list(constant_affine(5, Q(1, 5)))
            overlap_intercept[a] += 1
            overlap_intercept[b] -= 1
            overlap_slope = Q(-1 - b + a, 5)
            intercept = affine_sub(intercept, tuple(overlap_intercept))
            slope -= overlap_slope
        lo, hi = sweep.breakpoints[index], sweep.breakpoints[index + 1]
        delta = affine_sub(hi, lo)
        total = poly_add(total,
            poly_mul(poly_affine(intercept[:-1], intercept[-1]),
                     poly_affine(delta[:-1], delta[-1])))
        square_delta = poly_add(
            poly_mul(poly_affine(hi[:-1], hi[-1]),
                     poly_affine(hi[:-1], hi[-1])),
            poly_mul(poly_affine(lo[:-1], lo[-1]),
                     poly_affine(lo[:-1], lo[-1])), scale=-1)
        total = poly_add(total, {e: slope * c / 2 for e, c in square_delta.items()})
    return total


def generate_leaf5(index: int, sample: Sequence[Q],
                   path: Sequence[Tuple[int, int]], walls: Sequence[Affine],
                   depth: int) -> LeafData:
    constraints = padded_constraints5(walls, path, depth)
    offsets = sigma5_offsets(sample)
    sweep = sweep_targets(5, offsets[:-1], constraints)
    full_poly = integrated_sweep_poly5(sweep)
    target = Q(7, 30)
    lower = handelman_certificate(full_poly, target, constraints)
    squares5: List[Tuple[Q, Affine]] = []
    if lower is None:
        squares2 = global_sos_certificate(sigma5_schedule_quadratic(sample), target, 2)
        if squares2 is None:
            raise RuntimeError(f"n=5 leaf {index}: missing exact SOS certificate")
        squares5 = [(weight, (affine[0], affine[1], Q(0), Q(0), Q(0), affine[2]))
                    for weight, affine in squares2]
        remainder = subtract_weighted_squares(full_poly, target, squares5, 5)
        lower = handelman_certificate(remainder, Q(0), constraints, tries=40)
        if lower is None:
            raise RuntimeError(f"n=5 leaf {index}: missing equality remainder certificate")
    return LeafData(list(path), None, sweep, lower, squares5)


def emit_affine(a: Affine) -> str:
    return "{ constant := " + qstr(a[-1]) + ", linear := ![" + ", ".join(qstr(v) for v in a[:-1]) + "] }"


def emit_sparse(cert: Sparse) -> str:
    terms = ", ".join(f"({i}, {qstr(w)})" for i, w in cert)
    return "{ terms := [" + terms + "] }"


def emit_sweep(n: int, sweep: SweepData, indent: str = "") -> str:
    lines = ["{"]
    lines.append(f"{indent}  slabCount := {len(sweep.slabs)}")
    lines.append(f"{indent}  breakpoint := ![" + ", ".join(emit_affine(a) for a in sweep.breakpoints) + "]")
    lines.append(f"{indent}  breakpointOrderCertificate := ![" +
                 ", ".join(emit_sparse(c) for c in sweep.breakpoint_certificates) + "]")
    slab_text = []
    for slab in sweep.slabs:
        slab_text.append("{ order := ![" + ", ".join(map(str, slab.order)) + "]" +
                         ", overlap := ![" + ", ".join("true" if b else "false" for b in slab.overlap) + "]" +
                         ", orderCertificate := ![" + ", ".join(emit_sparse(c) for c in slab.order_certificates) + "]" +
                         ", overlapCertificate := ![" + ", ".join(emit_sparse(c) for c in slab.overlap_certificates) + "] }")
    lines.append(f"{indent}  slab := ![" + (",\n" + indent + "    ").join(slab_text) + "]")
    lines.append(indent + "}")
    return "\n".join(lines)


def emit_hand(cert: Sequence[Tuple[int, int, Q]]) -> str:
    terms = ", ".join("{ left := %d, right := %d, weight := %s }" % (i, j, qstr(w))
                      for i, j, w in cert)
    return "{ terms := [" + terms + "] }"


def emit_sos_hand(squares: Sequence[Tuple[Q, Affine]],
                  products: Sequence[Tuple[int, int, Q]]) -> str:
    square_text = ", ".join(
        "{ weight := " + qstr(weight) + ", affine := " + emit_affine(affine) + " }"
        for weight, affine in squares)
    return "{ squares := [" + square_text + "], products := " + emit_hand(products) + " }"


def emit_path(path: Sequence[Tuple[int, int]], depth: int) -> str:
    entries = [f"some ({wall}, {'true' if sign > 0 else 'false'})" for wall, sign in path]
    entries.extend(["none"] * (depth - len(path)))
    return "![" + ", ".join(entries) + "]"


def emit_leaf(n: int, index: int, leaf: LeafData, depth: int) -> str:
    del depth
    lines = [f"def leaf{n}_{index} : LeafCertificate.Leaf{n} ConstraintCount{n} :="]
    if leaf.empty is not None:
        lines.append(f"  .empty {emit_sparse(leaf.empty)}")
    else:
        assert leaf.sweep is not None and leaf.handelman is not None
        use_sos = bool(leaf.squares)
        lines.append("  .liveSOS" if use_sos else "  .live")
        lines.append("    " + emit_sweep(n, leaf.sweep, "    ").replace("\n", "\n    "))
        lines.append("    " + (emit_sos_hand(leaf.squares or [], leaf.handelman)
                              if use_sos else emit_hand(leaf.handelman)))
    return "\n".join(lines)


# Compact wire encoder matching `CertificateDecoder.lean`.  Python only finds
# witnesses; Lean decodes these bytes and replays every certificate exactly.
def put_var_nat(out: bytearray, value: int) -> None:
    if value < 0:
        raise ValueError("unsigned varint cannot encode a negative integer")
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)


def put_int(out: bytearray, value: int) -> None:
    put_var_nat(out, 2 * value if value >= 0 else -2 * value - 1)


def put_rat(out: bytearray, value: Q) -> None:
    put_int(out, value.numerator)
    put_var_nat(out, value.denominator - 1)


def put_affine(out: bytearray, affine: Affine, n: int) -> None:
    if len(affine) != n + 1:
        raise ValueError("affine dimension mismatch")
    put_rat(out, affine[-1])
    for coefficient in affine[:-1]:
        put_rat(out, coefficient)


def put_sparse(out: bytearray, certificate: Sparse) -> None:
    put_var_nat(out, len(certificate))
    for index, weight in certificate:
        put_var_nat(out, index)
        put_rat(out, weight)


def put_handelman(out: bytearray,
                  certificate: Sequence[Tuple[int, int, Q]]) -> None:
    put_var_nat(out, len(certificate))
    for left, right, weight in certificate:
        put_var_nat(out, left)
        put_var_nat(out, right)
        put_rat(out, weight)


def put_sweep(out: bytearray, sweep: SweepData, n: int) -> None:
    slab_count = len(sweep.slabs)
    if len(sweep.breakpoints) != slab_count + 1:
        raise ValueError("sweep breakpoint count mismatch")
    if len(sweep.breakpoint_certificates) != slab_count:
        raise ValueError("sweep breakpoint certificate count mismatch")
    put_var_nat(out, slab_count)
    for breakpoint in sweep.breakpoints:
        put_affine(out, breakpoint, n)
    for certificate in sweep.breakpoint_certificates:
        put_sparse(out, certificate)
    for slab in sweep.slabs:
        if len(slab.order) != n or len(slab.overlap) != n - 1:
            raise ValueError("sweep slab dimension mismatch")
        if (len(slab.order_certificates) != n - 1 or
                len(slab.overlap_certificates) != n - 1):
            raise ValueError("sweep slab certificate count mismatch")
        for index in slab.order:
            put_var_nat(out, index)
        for overlap in slab.overlap:
            out.append(1 if overlap else 0)
        for certificate in slab.order_certificates:
            put_sparse(out, certificate)
        for certificate in slab.overlap_certificates:
            put_sparse(out, certificate)


def encode_leaf(n: int, leaf: LeafData) -> bytes:
    out = bytearray()
    if leaf.empty is not None:
        out.append(0)
        put_sparse(out, leaf.empty)
        return bytes(out)
    assert leaf.sweep is not None and leaf.handelman is not None
    use_sos = bool(leaf.squares)
    out.append(2 if use_sos else 1)
    put_sweep(out, leaf.sweep, n)
    if use_sos:
        squares = leaf.squares or []
        put_var_nat(out, len(squares))
        for weight, affine in squares:
            put_rat(out, weight)
            put_affine(out, affine, n)
    put_handelman(out, leaf.handelman)
    return bytes(out)


def encode_tree_from(nodes: Sequence[TreeNode], leaf_encodings: Dict[int, bytes],
                     root_id: int) -> bytes:
    out = bytearray()

    def visit(node_id: int) -> None:
        node = nodes[node_id]
        if node.leaf is not None:
            out.append(0)
            out.extend(leaf_encodings[node.leaf])
            return
        assert node.wall is not None and node.positive is not None and node.negative is not None
        out.append(1)
        put_var_nat(out, node.wall)
        visit(node.positive)
        visit(node.negative)

    visit(root_id)
    return bytes(out)


def encode_tree(nodes: Sequence[TreeNode], leaf_encodings: Dict[int, bytes]) -> bytes:
    return encode_tree_from(nodes, leaf_encodings, 0)


def write_unpadded_base64(path: Path, data: bytes) -> None:
    encoded = base64.b64encode(data).decode("ascii").rstrip("=")
    line_width = 120
    text = "\n".join(encoded[i:i + line_width]
                     for i in range(0, len(encoded), line_width)) + "\n"
    path.write_text(text, encoding="ascii")


def emit_compact_subtrees4(out_dir: Path, nodes: Sequence[TreeNode],
                           leaf_encodings: Dict[int, bytes],
                           frontier_depth: int = 6,
                           chain_count: int = 4) -> int:
    """Emit 64 compact subtree checkers and a lightweight stitched root."""
    frontier = tree_frontier(nodes, frontier_depth)
    if len(frontier) != 2 ** frontier_depth:
        raise ValueError(f"depth-{frontier_depth} frontier is not full")
    frontier_index = {node_id: k for k, (node_id, _path) in enumerate(frontier)}
    total_binary_bytes = 0

    for k, (node_id, path) in enumerate(frontier):
        data = encode_tree_from(nodes, leaf_encodings, node_id)
        total_binary_bytes += len(data)
        asset_name = f"certificate4_sub{k:02d}.b64"
        write_unpadded_base64(out_dir / asset_name, data)
        dependency = ("CertificateBase4" if k < chain_count else
                      f"DecisionTree4Group{k - chain_count}")
        path_text = ", ".join(
            f"({wall}, {'true' if positive else 'false'})" for wall, positive in path)
        content = f"""import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.{dependency}

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath{k} : List (LeafCertificate.SignedIndex WallCount4) :=
  [{path_text}]

def encodedTree4Sub{k} : String := include_str "{asset_name}"

def encodedTree4SubCheck{k} : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath{k} encodedTree4Sub{k}

theorem encodedTree4Sub{k}_verified : encodedTree4SubCheck{k} = true := by
  native_decide

def tree4Sub{k} : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub{k}

theorem tree4Sub{k}_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath{k} tree4Sub{k} = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub{k}_verified

end KakeyaNeedleC3C4.Generated
"""
        (out_dir / f"DecisionTree4Group{k}.lean").write_text(content, encoding="utf-8")

    def top_term(node_id: int, indent: str) -> str:
        if node_id in frontier_index:
            return f"tree4Sub{frontier_index[node_id]}"
        node = nodes[node_id]
        assert node.wall is not None and node.positive is not None and node.negative is not None
        child_indent = indent + "  "
        return (f".branch {node.wall}\n{child_indent}(" +
                top_term(node.positive, child_indent) + f")\n{child_indent}(" +
                top_term(node.negative, child_indent) + ")")

    def top_proof(node_id: int, indent: str) -> str:
        """Kernel-small composition proof from the 64 checked subtrees.

        A single giant `simp` unfolds all imported decoded trees before it can
        rewrite the subtree facts and requires several GiB of memory.  This
        balanced proof follows only the six structural frontier levels and
        treats every imported subtree theorem as an opaque leaf fact.
        """
        if node_id in frontier_index:
            k = frontier_index[node_id]
            return (f"(by simpa [tree4SubPath{k}] using "
                    f"tree4Sub{k}_verified)")
        node = nodes[node_id]
        assert node.positive is not None and node.negative is not None
        child_indent = indent + "  "
        return ("(checkTreeAux4_branch_true (by native_decide)\n" +
                child_indent + top_proof(node.positive, child_indent) + "\n" +
                child_indent + top_proof(node.negative, child_indent) + ")")

    imports = "\n".join(
        f"import KakeyaNeedleC3C4.Generated.DecisionTree4Group{k}"
        for k in range(len(frontier) - chain_count, len(frontier)))
    content = f"""{imports}

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 1000000

/-- Compose two already-checked children without unfolding either payload. -/
theorem checkTreeAux4_branch_true {{H m maxDepth : ℕ}}
    {{polyForPath : List (LeafCertificate.SignedIndex H) →
      RationalPolyhedron 4 m}}
    {{target : ℚ}} {{current : List (LeafCertificate.SignedIndex H)}}
    {{wall : Fin H}} {{pos neg : LeafCertificate.Tree4 H m}}
    (hdepth : current.length < maxDepth)
    (hpos : LeafCertificate.checkTreeAux4 maxDepth polyForPath target
      (current ++ [(wall, true)]) pos = true)
    (hneg : LeafCertificate.checkTreeAux4 maxDepth polyForPath target
      (current ++ [(wall, false)]) neg = true) :
    LeafCertificate.checkTreeAux4 maxDepth polyForPath target current
      (.branch wall pos neg) = true := by
  simp only [LeafCertificate.checkTreeAux4, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨hdepth, hpos, hneg⟩

def tree4 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  {top_term(0, '  ')}

def treeCheck4 : Bool :=
  LeafCertificate.checkTree4 Depth4 polyForPath4 target4 tree4

theorem tree4_verified : treeCheck4 = true := by
  unfold treeCheck4 LeafCertificate.checkTree4 tree4
  exact {top_proof(0, '    ')}

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / "DecisionTree4.lean").write_text(content, encoding="utf-8")
    return total_binary_bytes


def emit_base5(out_dir: Path, walls: Sequence[Affine], depth: int,
               cell_count: int) -> None:
    wall_rows = ",\n  ".join(emit_affine(w) for w in walls)
    symmetry_rows = ",\n  ".join(emit_affine(a) for a in symmetry_gauge_constraints5())
    content = f"""import KakeyaNeedleC3C4.LeafCertificate5

namespace KakeyaNeedleC3C4.Generated

abbrev WallCount5 := {len(walls)}
abbrev Depth5 := {depth}
abbrev ConstraintCount5 := {depth + 6}
abbrev CellCount5 := {cell_count}

def walls5Array : Array (RationalAffine 5) := #[
  {wall_rows}
]

theorem walls5Array_size : walls5Array.size = WallCount5 := by native_decide

def walls5 (i : Fin WallCount5) : RationalAffine 5 :=
  walls5Array[i.1]'(by rw [walls5Array_size]; exact i.2)

def signedWall5 (positive : Bool) (w : Fin WallCount5) : RationalAffine 5 :=
  if positive then walls5 w else SweepCertificate.affineNeg (walls5 w)

def pathConstraint5 (path : List (LeafCertificate.SignedIndex WallCount5))
    (i : Fin Depth5) : RationalAffine 5 :=
  match path[i.1]? with
  | none => SweepCertificate.affineConst 5 1
  | some (w, positive) => signedWall5 positive w

def symmetryGaugeConstraints5 : Fin 6 → RationalAffine 5 := ![
  {symmetry_rows}
]

def polyForPath5 (path : List (LeafCertificate.SignedIndex WallCount5)) :
    RationalPolyhedron 5 ConstraintCount5 where
  constraint := Fin.append (pathConstraint5 path) symmetryGaugeConstraints5

def target5 : ℚ := ((7 : ℚ) / 30)

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / "CertificateBase5.lean").write_text(content, encoding="utf-8")


def emit_compact_tree5(out_dir: Path, nodes: Sequence[TreeNode],
                       leaf_encodings: Dict[int, bytes]) -> int:
    data = encode_tree(nodes, leaf_encodings)
    write_unpadded_base64(out_dir / "certificate5.b64", data)
    content = """import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.CertificateBase5

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def encodedTree5 : String := include_str "certificate5.b64"

def encodedTree5Check : Bool :=
  CertificateDecoder.checkEncodedTree5 Depth5 CellCount5 polyForPath5 target5
    encodedTree5

theorem encodedTree5_verified : encodedTree5Check = true := by
  native_decide

theorem encodedTree5_has_368_cells :
    ∃ tree, CertificateDecoder.decodeBase64 encodedTree5 >>=
        CertificateDecoder.decodeTree5 WallCount5 ConstraintCount5 = some tree ∧
      CertificateDecoder.treeLeafCount tree = CellCount5 := by
  exact CertificateDecoder.checkEncodedTree5_cellCount encodedTree5_verified

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / "DecisionTree5.lean").write_text(content, encoding="utf-8")
    return len(data)


def point_constraints5(offsets: Sequence[Q]) -> List[Affine]:
    rows: List[Affine] = [constant_affine(5, Q(1))]
    for i, value in enumerate(offsets):
        row = [Q(0)] * 5
        row[i] = Q(1)
        affine = tuple(row + [-value])
        rows.extend([affine, affine_scale(Q(-1), affine)])
    return rows


def emit_witness_certificates5(out_dir: Path) -> None:
    witnesses = {
        "Sym": [Q(4, 15), Q(1, 5), Q(2, 15), Q(1, 15), Q(0)],
        "Asym": [Q(79, 305), Q(47, 305), Q(10, 61), Q(12, 305), Q(0)],
    }
    blocks: List[str] = []
    for name, offsets in witnesses.items():
        constraints = point_constraints5(offsets)
        sweep = sweep_targets(5, offsets[:-1], constraints)
        rows = ",\n  ".join(emit_affine(a) for a in constraints)
        vector = ", ".join(qstr(v) for v in offsets)
        area = "((7 : ℝ) / 30)" if name == "Sym" else "((14 : ℝ) / 61)"
        area_q = "((7 : ℚ) / 30)" if name == "Sym" else "((14 : ℚ) / 61)"
        blocks.append(f"""
def witness{name}5Q : Fin 5 → ℚ := ![{vector}]

def witness{name}5 : Fin 5 → ℝ := fun i ↦ (witness{name}5Q i : ℝ)

def witness{name}Poly5 : RationalPolyhedron 5 11 where
  constraint := ![
  {rows}
  ]

def witness{name}Sweep5 : SweepCertificate.Certificate5 11 :=
  {emit_sweep(5, sweep)}

theorem witness{name}Sweep5_verified :
    SweepCertificate.check5 witness{name}Sweep5 witness{name}Poly5 = true := by
  native_decide

theorem witness{name}5_mem : witness{name}5 ∈ witness{name}Poly5.carrier := by
  intro i
  fin_cases i <;>
    norm_num [witness{name}5, witness{name}5Q, witness{name}Poly5, RationalAffine.eval,
      Fin.sum_univ_succ]

theorem witness{name}5_value :
    (SweepCertificate.integratedQuadratic5 witness{name}Sweep5).evalRat
      witness{name}5Q = {area_q} := by
  native_decide

theorem unionArea_witness{name}5 : unionArea 5 witness{name}5 = {area} := by
  rw [unionArea_eq_sliceArea]
  rw [SweepCertificate.sliceArea_eq_integratedQuadratic_five
    witness{name}Sweep5_verified witness{name}5_mem]
  rw [show witness{name}5 = (fun i ↦ (witness{name}5Q i : ℝ)) by rfl]
  rw [RationalQuadratic.eval_cast, witness{name}5_value]
  norm_num
""")
    content = """import KakeyaNeedleC3C4.SweepCertificate5

namespace KakeyaNeedleC3C4.Generated

noncomputable section

set_option maxHeartbeats 4000000

""" + "\n".join(blocks) + "\nend\nend KakeyaNeedleC3C4.Generated\n"
    (out_dir / "WitnessCertificates5.lean").write_text(content, encoding="utf-8")


def emit_base(out_dir: Path, n: int, walls: Sequence[Affine], depth: int, cell_count: int) -> None:
    d = n - 1
    constraint_count = depth + 2 * d + 2
    target = Q(5, 18) if n == 3 else Q(1, 4)
    wall_rows = ",\n  ".join(emit_affine(w) for w in walls)
    extra = cube_and_gauge_constraints(n)
    cube_rows = ",\n  ".join(emit_affine(a) for a in extra[:-2])
    gauge_rows = ",\n  ".join(emit_affine(a) for a in extra[-2:])
    content = f"""import KakeyaNeedleC3C4.LeafCertificate

namespace KakeyaNeedleC3C4.Generated

abbrev WallCount{n} := {len(walls)}
abbrev Depth{n} := {depth}
abbrev ConstraintCount{n} := {constraint_count}
abbrev CellCount{n} := {cell_count}

def walls{n}Array : Array (RationalAffine {n}) := #[
  {wall_rows}
]

theorem walls{n}Array_size : walls{n}Array.size = WallCount{n} := by
  native_decide

def walls{n} (i : Fin WallCount{n}) : RationalAffine {n} :=
  walls{n}Array[i.1]'(by
    rw [walls{n}Array_size]
    exact i.2)

def signedWall{n} (positive : Bool) (w : Fin WallCount{n}) : RationalAffine {n} :=
  if positive then walls{n} w else SweepCertificate.affineNeg (walls{n} w)

def pathConstraint{n} (path : List (LeafCertificate.SignedIndex WallCount{n}))
    (i : Fin Depth{n}) : RationalAffine {n} :=
  match path[i.1]? with
  | none => SweepCertificate.affineConst {n} 1
  | some (w, positive) => signedWall{n} positive w

def cubeConstraints{n} : Fin {2 * d} → RationalAffine {n} := ![
  {cube_rows}
]

def gaugeConstraints{n} : Fin 2 → RationalAffine {n} := ![
  {gauge_rows}
]

def polyForPath{n} (path : List (LeafCertificate.SignedIndex WallCount{n})) :
    RationalPolyhedron {n} ConstraintCount{n} where
  constraint := Fin.append (pathConstraint{n} path)
    (Fin.append cubeConstraints{n} gaugeConstraints{n})

def target{n} : ℚ := {qstr(target)}

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / f"CertificateBase{n}.lean").write_text(content, encoding="utf-8")


def emit_tree(out_dir: Path, n: int, nodes: Sequence[TreeNode], modules: Sequence[str]) -> None:
    def term(node_id: int, indent: str) -> str:
        node = nodes[node_id]
        if node.leaf is not None:
            return f".leaf leaf{n}_{node.leaf}"
        assert node.wall is not None and node.positive is not None and node.negative is not None
        child_indent = indent + "  "
        return (f".branch {node.wall}\n{child_indent}(" + term(node.positive, child_indent) +
                f")\n{child_indent}(" + term(node.negative, child_indent) + ")")

    imports = "\n".join(f"import KakeyaNeedleC3C4.Generated.{module}" for module in modules)
    tree_term = term(0, "  ")
    check = "checkTree3" if n == 3 else "checkTree4"
    content = f"""{imports}

namespace KakeyaNeedleC3C4.Generated

def tree{n} : LeafCertificate.Tree{n} WallCount{n} ConstraintCount{n} :=
  {tree_term}

def treeCheck{n} : Bool :=
  LeafCertificate.{check} Depth{n} polyForPath{n} target{n} tree{n}

theorem tree{n}_verified : treeCheck{n} = true := by
  native_decide

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / f"DecisionTree{n}.lean").write_text(content, encoding="utf-8")


def tree_frontier(nodes: Sequence[TreeNode], frontier_depth: int) \
        -> List[Tuple[int, List[Tuple[int, bool]]]]:
    """Return frontier node ids and their signed root paths, left to right."""
    frontier: List[Tuple[int, List[Tuple[int, bool]]]] = []

    def collect(node_id: int, depth: int, path: List[Tuple[int, bool]]) -> None:
        node = nodes[node_id]
        if depth == frontier_depth or node.leaf is not None:
            frontier.append((node_id, path))
            return
        assert node.wall is not None and node.positive is not None and node.negative is not None
        collect(node.positive, depth + 1, path + [(node.wall, True)])
        collect(node.negative, depth + 1, path + [(node.wall, False)])

    collect(0, 0, [])
    return frontier


def emit_chunk(out_dir: Path, n: int, chunk_index: int,
               leaves: Sequence[Tuple[int, LeafData]], depth: int) -> str:
    module = f"CertificateData{n}Chunk{chunk_index:03d}"
    definitions = "\n\n".join(emit_leaf(n, i, leaf, depth) for i, leaf in leaves)
    # Two dependency chains bound Lake's parallel elaboration to two large
    # generated modules at once.  Leaving all chunks independent can exhaust
    # memory when Lake starts dozens of Lean processes concurrently.
    dependency = (f"CertificateBase{n}" if chunk_index < 2 else
                  f"CertificateData{n}Chunk{chunk_index - 2:03d}")
    content = f"""import KakeyaNeedleC3C4.Generated.{dependency}

namespace KakeyaNeedleC3C4.Generated

{definitions}

end KakeyaNeedleC3C4.Generated
"""
    (out_dir / f"{module}.lean").write_text(content, encoding="utf-8")
    return module


def enumerate_problem(n: int):
    walls0 = ref.arrangement_hyperplanes(n)
    if n == 3:
        cells = ref.enumerate_cells_2d(walls0)
    elif n == 4:
        cells, complete = ref.enumerate_cells_3d(walls0)
        if not complete:
            raise RuntimeError("reference 3D arrangement enumeration was incomplete")
    else:
        raise ValueError("only n=3 and n=4 are supported")
    items = sorted(cells.items())
    signs = [s for s, _ in items]
    samples = [p for _, p in items]
    nodes, paths, depth = build_balanced_tree(signs)
    walls = [lift_gauge_affine(tuple(h)) for h in walls0]
    return walls, signs, samples, nodes, paths, depth


def generate_n(n: int, out_dir: Path, chunk_size: int, limit: Optional[int]) -> Dict[str, object]:
    start = time.time()
    walls, signs, samples, nodes, paths, depth = enumerate_problem(n)
    expected = 72 if n == 3 else 9350
    if len(signs) != expected:
        raise RuntimeError(f"n={n}: expected {expected} cells, found {len(signs)}")
    if limit is not None:
        signs = signs[:limit]
        samples = samples[:limit]
    print(f"n={n}: {len(walls)} walls, {expected} cells, balanced depth {depth}", flush=True)
    emit_base(out_dir, n, walls, depth, expected)

    modules: List[str] = []
    current: List[Tuple[int, LeafData]] = []
    compact_n4 = n == 4 and limit is None
    leaf_encodings: Dict[int, bytes] = {}
    empty_count = 0
    lower_count = 0
    sweep_farkas_terms = 0
    handelman_terms = 0
    sos_square_terms = 0
    for i, (sv, sample) in enumerate(zip(signs, samples)):
        leaf = generate_leaf(n, i, sv, sample, paths[i], walls, depth)
        if leaf.empty is not None:
            empty_count += 1
        else:
            lower_count += 1
            assert leaf.sweep is not None and leaf.handelman is not None
            sweep_farkas_terms += sum(len(c) for c in leaf.sweep.breakpoint_certificates)
            for slab in leaf.sweep.slabs:
                sweep_farkas_terms += sum(len(c) for c in slab.order_certificates)
                sweep_farkas_terms += sum(len(c) for c in slab.overlap_certificates)
            handelman_terms += len(leaf.handelman)
            sos_square_terms += len(leaf.squares or [])
        if compact_n4:
            leaf_encodings[i] = encode_leaf(n, leaf)
        else:
            current.append((i, leaf))
            if len(current) == chunk_size:
                modules.append(emit_chunk(out_dir, n, len(modules), current, depth))
                current = []
        if (i + 1) % (50 if n == 3 else 100) == 0:
            print(f"n={n}: leaves {i+1}/{len(signs)}, empty={empty_count}, "
                  f"elapsed={time.time()-start:.1f}s", flush=True)
    if current:
        modules.append(emit_chunk(out_dir, n, len(modules), current, depth))
    compact_bytes = 0
    if limit is None:
        if n == 4:
            compact_bytes = emit_compact_subtrees4(out_dir, nodes, leaf_encodings)
        else:
            emit_tree(out_dir, n, nodes, modules[-2:])
    manifest = {
        "n": n,
        "wall_count": len(walls),
        "cell_count": expected,
        "generated_leaf_count": len(signs),
        "tree_node_count": len(nodes),
        "balanced_depth": depth,
        "constraint_count": depth + 2 * (n - 1) + 2,
        "empty_leaf_count": empty_count,
        "lower_leaf_count": lower_count,
        "sweep_farkas_term_count": sweep_farkas_terms,
        "handelman_term_count": handelman_terms,
        "sos_square_term_count": sos_square_terms,
        "chunk_count": 64 if compact_n4 else len(modules),
        "payload_layout": ("compact_base64_depth6_four_chains" if compact_n4 else
                           "sequential_chunks"),
        "compact_binary_bytes": compact_bytes,
        "elapsed_seconds": time.time() - start,
    }
    (out_dir / f"manifest{n}.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2), flush=True)
    return manifest


def generate_n5(out_dir: Path, limit: Optional[int]) -> Dict[str, object]:
    start = time.time()
    walls2 = sigma5_arrangement()
    cells = ref.enumerate_cells_2d(walls2)
    items = sorted(cells.items())
    if len(walls2) != 37 or len(items) != 368:
        raise RuntimeError(
            f"n=5 certificate expected 37 walls/368 cells, got {len(walls2)}/{len(items)}")
    signs = [s for s, _ in items]
    samples = [p for _, p in items]
    nodes, paths, depth = build_balanced_tree(signs)
    if depth != 10:
        raise RuntimeError(f"n=5 expected balanced depth 10, got {depth}")
    walls5 = [(w[0], w[1], Q(0), Q(0), Q(0), w[2]) for w in walls2]
    emit_base5(out_dir, walls5, depth, len(items))

    leaf_encodings: Dict[int, bytes] = {}
    handelman_terms = sos_square_terms = sweep_farkas_terms = 0
    chosen = items if limit is None else items[:limit]
    for i, (_sv, sample) in enumerate(chosen):
        offsets = sigma5_offsets(sample)
        sigma_poly = sigma5_schedule_quadratic(sample)
        direct_poly = ref.schedule_quadratic_exact(5, tuple(offsets[:-1]))
        if poly_eval(sigma_poly, sample) != ref.exact_area_offsets(5, offsets):
            raise RuntimeError(f"n=5 cell {i}: notebook sweep/formula mismatch")
        if poly_eval(direct_poly, tuple(offsets[:-1])) != poly_eval(sigma_poly, sample):
            raise RuntimeError(f"n=5 cell {i}: full/symmetric quadratic mismatch")
        leaf = generate_leaf5(i, sample, paths[i], walls5, depth)
        assert leaf.sweep is not None and leaf.handelman is not None
        leaf_encodings[i] = encode_leaf(5, leaf)
        handelman_terms += len(leaf.handelman)
        sos_square_terms += len(leaf.squares or [])
        sweep_farkas_terms += sum(len(c) for c in leaf.sweep.breakpoint_certificates)
        for slab in leaf.sweep.slabs:
            sweep_farkas_terms += sum(map(len, slab.order_certificates))
            sweep_farkas_terms += sum(map(len, slab.overlap_certificates))
        if (i + 1) % 50 == 0:
            print(f"n=5: leaves {i+1}/{len(chosen)}, elapsed={time.time()-start:.1f}s",
                  flush=True)

    compact_bytes = 0
    if limit is None:
        compact_bytes = emit_compact_tree5(out_dir, nodes, leaf_encodings)
        emit_witness_certificates5(out_dir)
    manifest = {
        "n": 5,
        "scope": "reflection_fixed_full_unbounded_parameter_arrangement",
        "wall_count": len(walls2),
        "cell_count": len(items),
        "generated_leaf_count": len(chosen),
        "tree_node_count": len(nodes),
        "balanced_depth": depth,
        "constraint_count": depth + 6,
        "lower_leaf_count": len(chosen),
        "sweep_farkas_term_count": sweep_farkas_terms,
        "handelman_term_count": handelman_terms,
        "sos_square_term_count": sos_square_terms,
        "target": "7/30",
        "symmetric_witness": ["4/15", "1/5", "2/15", "1/15", "0"],
        "asymmetric_witness": ["79/305", "47/305", "10/61", "12/305", "0"],
        "asymmetric_witness_area": "14/61",
        "payload_layout": "compact_base64_single_tree",
        "compact_binary_bytes": compact_bytes,
        "elapsed_seconds": time.time() - start,
    }
    (out_dir / "manifest5.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2), flush=True)
    return manifest


def generate_tree_only(n: int, out_dir: Path, chunk_size: int) -> None:
    """Regenerate aggregate tree modules from already-emitted payload chunks."""
    if n == 4:
        raise RuntimeError(
            "n=4 tree modules carry frontier-local payloads; run full generation")
    walls, signs, _samples, nodes, _paths, depth = enumerate_problem(n)
    expected = 72 if n == 3 else 9350
    if len(signs) != expected:
        raise RuntimeError(f"n={n}: expected {expected} cells, found {len(signs)}")
    emit_base(out_dir, n, walls, depth, expected)
    chunk_count = (expected + chunk_size - 1) // chunk_size
    modules = [f"CertificateData{n}Chunk{i:03d}" for i in range(chunk_count)]
    emit_tree(out_dir, n, nodes, modules[-2:])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", choices=("3", "4", "5", "all"), default="all")
    parser.add_argument("--output", type=Path,
                        default=SCRIPT_DIR.parent / "KakeyaNeedleC3C4" / "Generated")
    parser.add_argument("--chunk-size", type=int, default=128)
    parser.add_argument("--limit", type=int, help="developer smoke test; does not emit aggregate module")
    parser.add_argument("--tree-only", action="store_true",
                        help="regenerate n=3 aggregate tree using existing payload chunks")
    parser.add_argument("--clean", action="store_true", help="remove the generated directory first")
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")
    if args.clean and args.output.exists():
        shutil.rmtree(args.output)
    args.output.mkdir(parents=True, exist_ok=True)
    selected = (3, 4, 5) if args.n == "all" else (int(args.n),)
    for n in selected:
        if n == 5:
            if args.tree_only:
                parser.error("--tree-only is not supported for n=5")
            generate_n5(args.output, args.limit)
            continue
        if args.tree_only:
            if args.limit is not None:
                parser.error("--tree-only and --limit cannot be combined")
            generate_tree_only(n, args.output, args.chunk_size)
        else:
            generate_n(n, args.output, args.chunk_size, args.limit)


if __name__ == "__main__":
    main()
