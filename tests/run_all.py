#!/usr/bin/env python3
"""Reviewer-style verification battery for the ORL note.

Run:  python3 run_all.py [--quick]
Writes ../results/verification_report.json and ../results/verification_report.md.
Every test is exact rational arithmetic unless its name ends in `_float`.
A test either passes (all assertions hold) or the report records the failure.
"""
import argparse
import hashlib
import itertools
import json
import math
import random
import sys
import time
import traceback
from fractions import Fraction as Q
from itertools import product
from math import ceil, comb, floor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from exactcg import (RAMPS, F, F_series, g_shift, dot, vertices, contains,
                     max_over, same_polytope, integer_points, canonical,
                     cg_row, cg_closure, closure_sequence, hull_rank,
                     grid_closure, ramp_linear, ramp_smoothstep,
                     reference_vertices_2d, support_closure_2d)

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"
SEED = 20261121
DELTAS = [Q(1), Q(1, 2), Q(1, 3), Q(1, 7), Q(1, 100)]
TESTS = []


def test(fn):
    TESTS.append(fn)
    return fn


def rand_rat(rng, lo, hi, dens=(1, 2, 3, 4, 5, 7, 10, 60)):
    d = rng.choice(dens)
    return Q(rng.randint(lo * d, hi * d), d)


def tricky_points(hi=10):
    """Integers, and points just left/right of integers and of k + delta."""
    pts = set()
    for k in range(hi + 1):
        for e in (Q(0), Q(1, 1000), Q(-1, 1000), Q(1, 10**9), Q(-1, 10**9)):
            if k + e >= 0:
                pts.add(Q(k) + e)
        for d in DELTAS:
            for e in (Q(0), Q(1, 10**9), Q(-1, 10**9)):
                if k + d + e >= 0:
                    pts.add(Q(k) + d + e)
    return sorted(pts)


# ---------------------------------------------------------------------------
# Lemma 1: construction
# ---------------------------------------------------------------------------


@test
def lemma1_closed_form_equals_series(args, rng):
    n = 0
    for name, S in RAMPS.items():
        for d in DELTAS:
            for s in tricky_points(12) + [rand_rat(rng, 0, 30) for _ in range(300)]:
                assert F(S, d, s) == F_series(S, d, s), (name, d, s)
                n += 1
    return {"evaluations": n}


@test
def lemma1_normalization_integers_sandwich(args, rng):
    n = 0
    for name, S in RAMPS.items():
        for d in DELTAS:
            assert F(S, d, 0) == 0
            for q in range(1, 41):
                assert F(S, d, q) == q - 1, (name, d, q)   # F(q) = q - 1
            for s in tricky_points(15) + [rand_rat(rng, 0, 40) for _ in range(400)]:
                lo = max(0, floor(s - d))
                v = F(S, d, s)
                assert lo <= v <= floor(s), (name, d, s, v)
                # Exact characterization is ramp-dependent; containment in
                # [q,q+delta) is universal, equality needs no early saturation.
                in_err = s >= 1 and S((s - floor(s)) / d) < 1
                assert (v < floor(s)) == in_err, (name, d, s, v)
                n += 1
    return {"points": n}


@test
def lemma1_plateau_ramps_error_set(args, rng):
    ramps = {"early_saturation": lambda t: ramp_linear(2 * t),
             "late_start": lambda t: ramp_linear(2 * t - 1)}
    checked = wrong_equality = 0
    for S in ramps.values():
        for d in DELTAS:
            pts = tricky_points(5) + [Q(k, 20) for k in range(121)]
            for s in pts:
                val = F(S, d, s)
                assert val == F_series(S, d, s)
                error = val < floor(s)
                assert error == (s >= 1 and S((s - floor(s)) / d) < 1)
                assert not error or (s - floor(s)) < d
                wrong_equality += error != (s >= 1 and (s - floor(s)) < d)
                assert max(0, floor(s - d)) <= val <= floor(s)
                checked += 1
            for s, t in product([Q(k, 8) for k in range(25)], repeat=2):
                assert F(S, d, s + t) >= F(S, d, s) + F(S, d, t)
        for values in ([Q(0)], [Q(0), Q(0)], [Q(0), Q(1), Q(2), Q(999, 1000), Q(1001, 1000)]):
            eps, width = recover_parameters(values)
            for d in (width, width / 7):
                assert all(F(S, d, (1 + eps) * z) == floor(z) for z in values)
    assert wrong_equality > 0, "the old universal exact-error-set claim must fail"
    return {"ramps": list(ramps), "points": checked,
            "old_error_set_equality_counterexamples": wrong_equality,
            "superadditivity_pairs": 2 * len(DELTAS) * 25 ** 2}


@test
def lemma1_monotone_superadditive(args, rng):
    trials = 4000 if args.quick else 25000
    n = 0
    pts = tricky_points(8)
    for name, S in RAMPS.items():
        for d in DELTAS:
            for _ in range(trials // len(DELTAS)):
                s = rng.choice(pts) if rng.random() < 0.3 else rand_rat(rng, 0, 12)
                t = rng.choice(pts) if rng.random() < 0.3 else rand_rat(rng, 0, 12)
                fs, ft, fst = F(S, d, s), F(S, d, t), F(S, d, s + t)
                assert fst >= fs + ft, ("superadditivity", name, d, s, t)
                lo, hi = min(s, t), max(s, t)
                assert F(S, d, lo) <= F(S, d, hi), ("monotone", name, d, s, t)
                n += 1
    return {"pairs": n}


@test
def lemma1_averaging_identity_linear_exact(args, rng):
    """F_{lin,delta}(s) = E[g_{delta T}(s)], T ~ U[0,1), computed exactly."""
    n = 0
    for d in DELTAS:
        for s in tricky_points(10) + [rand_rat(rng, 0, 20) for _ in range(300)]:
            # g_{delta t}(s) is piecewise constant in t with breakpoints where
            # s - delta t crosses an integer; integrate exactly.
            brk = {Q(0), Q(1)}
            for k in range(floor(s) - 2, floor(s) + 2):
                t = (s - k) / d
                if 0 < t < 1:
                    brk.add(t)
            brk = sorted(brk)
            e = sum((b - a) * g_shift(d * (a + b) / 2, s) for a, b in zip(brk, brk[1:]))
            assert e == F(ramp_linear, d, s), (d, s, e)
            n += 1
    return {"points": n}


@test
def lemma1_averaging_identity_smooth_float(args, rng):
    """For smooth ramps, E[g_{delta T}(s)] with T ~ CDF S, by quadrature."""
    import numpy as np
    worst = 0.0
    grid = np.linspace(0, 1, 200001)
    for name in ("smoothstep", "smootherstep"):
        S = RAMPS[name]
        Sv = np.array([float(S(Q(x).limit_denominator(10**7))) for x in grid[::100]])
        tt = grid[::100]
        for d in [1.0, 0.5, 0.1]:
            for s in np.linspace(0, 6, 61):
                g = np.maximum(0, np.floor(s - d * tt[:-1]))
                e = float(np.sum(g * np.diff(Sv)))      # Riemann–Stieltjes sum
                f = float(F(S, Q(d).limit_denominator(1000), Q(s).limit_denominator(10**6)))
                worst = max(worst, abs(e - f))
    assert worst < 5e-3, worst
    return {"max_abs_error": worst, "note": "Stieltjes sums on 2001 nodes"}


@test
def lemma1_cut_validity_integer_points(args, rng):
    cnt = inst = 0
    for _ in range(150 if args.quick else 600):
        m, n = rng.randint(1, 3), rng.randint(1, 4)
        rows = [(tuple(rng.randint(0, 6) for _ in range(n)), rng.randint(0, 12))
                for _ in range(m)]
        rows.append((tuple(1 for _ in range(n)), 8))   # boundedness
        pts = integer_points(rows, n)
        inst += 1
        for _ in range(20):
            u = [rand_rat(rng, 0, 3) for _ in rows]
            S = rng.choice(list(RAMPS.values()))
            d = rng.choice(DELTAS)
            col = [F(S, d, sum(ui * r[0][j] for ui, r in zip(u, rows))) for j in range(n)]
            rhs = F(S, d, sum(ui * r[1] for ui, r in zip(u, rows)))
            for x in pts:
                assert dot(col, x) <= rhs
            cnt += 1
    return {"instances": inst, "cuts": cnt}


# ---------------------------------------------------------------------------
# Domain restriction (Burai–Száz context): symmetric smooth floors fail
# ---------------------------------------------------------------------------


@test
def domain_symmetric_smooth_floor_not_superadditive_float(args, rng):
    """Normalized centred sigmoid-sum floors on R violate superadditivity."""
    import numpy as np
    def sig_floor(x, k=20.0, N=30):
        n = np.arange(-N, N + 1)
        exponent = np.clip(-k * (x[..., None] - n - 0.5), -700, 700)
        return np.sum(1 / (1 + np.exp(exponent)), axis=-1) - N - 0.5
    xs = np.linspace(-3, 3, 241)
    X, Y = np.meshgrid(xs, xs)
    f0 = sig_floor(np.array([0.0]))[0]
    Fn = lambda z: sig_floor(z) - f0
    viol = (Fn(X + Y) < Fn(X) + Fn(Y) - 1e-9).mean()
    assert viol > 0.1
    # Delayed construction restricted to R_+ has zero violations on same grid.
    xp = np.linspace(0, 6, 241)
    Xp, Yp = np.meshgrid(xp, xp)
    def dl(z, d=0.25):
        p = np.floor(z); r = np.clip((z - p) / d, 0, 1)
        return np.where(z < 1, 0.0, p - 1 + 3 * r**2 - 2 * r**3)
    viol_p = (dl(Xp + Yp) < dl(Xp) + dl(Yp) - 1e-12).mean()
    assert viol_p == 0
    return {"symmetric_violation_fraction_on_R": float(viol),
            "delayed_violation_fraction_on_R+": float(viol_p)}


@test
def domain_normalization_needed_example_float(args, rng):
    """s - 1 + sin(s)/4 is smooth, nonlinear, superadditive on R (F(0) != 0)."""
    import numpy as np
    s = np.linspace(-50, 50, 2001)
    S, T = np.meshgrid(s, s)
    f = lambda z: z - 1 + np.sin(z) / 4
    gap = f(S + T) - f(S) - f(T)          # = 1 + (sin(s+t)-sin s-sin t)/4 >= 1/4
    assert gap.min() >= 0.25 - 1e-12
    return {"min_superadditivity_gap": float(gap.min()), "analytic_lower_bound": 0.25}


# ---------------------------------------------------------------------------
# Theorem 1: finite certificate (forward) and exact recovery (reverse)
# ---------------------------------------------------------------------------


def certificate(A, b, u, t):
    """Proof construction: <= n+1 CG rows implying the shifted row g_t(uA)x <= g_t(ub)."""
    m, n = len(A), len(A[0])
    a = [sum(u[i] * A[i][j] for i in range(m)) for j in range(n)]
    B = sum(u[i] * b[i] for i in range(m))
    target = [max(0, floor(v - t)) for v in a]
    trhs = max(0, floor(B - t))
    N, r = floor(B), B - floor(B)
    if trhs == N:
        rows = [(Q(1), list(u))]
    else:
        assert N >= 1 and t > r
        eta = (t - r) / 2
        lam = (N - eta) / B
        coeff = [floor(lam * v) for v in a]
        rows = [(Q(1), [lam * v for v in u])]
        for j in range(n):
            if a[j] > B:
                d = max(0, target[j] - coeff[j])
                if d:
                    rows.append((Q(d), [v / a[j] for v in u]))
    coeff = [Q(0)] * n
    rhs = Q(0)
    for w, v in rows:
        assert w >= 0 and all(z >= 0 for z in v)
        for j in range(n):
            coeff[j] += w * floor(sum(v[i] * A[i][j] for i in range(m)))
        rhs += w * floor(sum(v[i] * b[i] for i in range(m)))
    return rows, coeff, rhs, target, trhs


@test
def thm1_certificate_random_and_boundary(args, rng):
    trials = 5000 if args.quick else 60000
    cases = {"direct": 0, "rescaled": 0, "with_fixings": 0}
    maxrows = 0
    bnd = [([[Q(0), Q(5)]], [Q(0)], [Q(1)], Q(0)),
           ([[Q(0), Q(5)]], [Q(0)], [Q(1)], Q(99, 100)),
           ([[Q(1), Q(5), Q(40)]], [Q(2)], [Q(1)], Q(1, 2)),
           ([[Q(1), Q(5)]], [Q(7, 3)], [Q(1)], Q(1, 3)),
           ([[Q(1), Q(5)]], [Q(7, 3)], [Q(1)], Q(1, 3) + Q(1, 10**12)),
           ([[Q(7, 3), Q(8, 3), Q(0)]], [Q(7, 3)], [Q(1)], Q(9, 10)),
           ([[Q(2), Q(3)]], [Q(3)], [Q(1)], Q(0)),          # integer B, t = 0
           ([[Q(2), Q(3)]], [Q(3)], [Q(1)], Q(999, 1000))]  # integer B, t -> 1
    items = list(bnd)
    for _ in range(trials):
        m, n = rng.randint(1, 3), rng.randint(1, 6)
        A = [[Q(rng.randrange(41), rng.randint(1, 9)) for _ in range(n)] for _ in range(m)]
        b = [Q(rng.randrange(31), rng.randint(1, 9)) for _ in range(m)]
        u = [Q(rng.randrange(21), rng.randint(1, 11)) for _ in range(m)]
        t = Q(rng.randrange(1000), 1000)
        items.append((A, b, u, t))
    for A, b, u, t in items:
        rows, coeff, rhs, target, trhs = certificate(A, b, u, t)
        assert len(rows) <= len(A[0]) + 1
        assert rhs == trhs
        assert all(c >= g for c, g in zip(coeff, target))
        maxrows = max(maxrows, len(rows))
        key = "direct" if len(rows) == 1 and rows[0][1] == list(u) else (
            "with_fixings" if len(rows) > 1 else "rescaled")
        cases[key] += 1
    return {"cases": len(items), "by_case": cases, "max_certificate_rows": maxrows,
            "bound_n_plus_1_holds": True}


def compress_conic_certificate(weighted_vectors):
    """Exact conic Caratheodory elimination, preserving the entire vector sum."""
    active = [(Q(w), tuple(Q(x) for x in v)) for w, v in weighted_vectors if w > 0 and any(v)]
    if not active:
        return []
    dimension = len(active[0][1])
    while len(active) > dimension:
        selected = active[:dimension + 1]
        mat = [[v[j] for _, v in selected] for j in range(dimension)]
        pivot_cols, rr = [], 0
        for col in range(dimension + 1):
            pivot = next((i for i in range(rr, dimension) if mat[i][col]), None)
            if pivot is None:
                continue
            mat[rr], mat[pivot] = mat[pivot], mat[rr]
            scale = mat[rr][col]
            mat[rr] = [x / scale for x in mat[rr]]
            for i in range(dimension):
                if i != rr:
                    scale = mat[i][col]
                    mat[i] = [x - scale * y for x, y in zip(mat[i], mat[rr])]
            pivot_cols.append(col)
            rr += 1
            if rr == dimension:
                break
        free = next(j for j in range(dimension + 1) if j not in pivot_cols)
        dependence = [Q(int(j == free)) for j in range(dimension + 1)]
        for i, j in enumerate(pivot_cols):
            dependence[j] = -mat[i][free]
        assert all(sum(d * v[j] for d, (_, v) in zip(dependence, selected)) == 0
                   for j in range(dimension))
        if not any(d > 0 for d in dependence):
            dependence = [-d for d in dependence]
        step = min(w / d for d, (w, _) in zip(dependence, selected) if d > 0)
        reduced = [(w - step * d, v) for d, (w, v) in zip(dependence, selected)]
        assert all(w >= 0 for w, _ in reduced)
        active = [(w, v) for w, v in reduced if w > 0] + active[dimension + 1:]
    return active


@test
def thm1_smooth_mixture_certificate_compression(args, rng):
    instances = 20 if args.quick else 120
    compressed = cuts = maximum = 0
    for _ in range(instances):
        n, m = rng.choice([2, 3]), rng.choice([1, 2])
        A = [[Q(rng.randrange(31), 4) for _ in range(n)] for _ in range(m)]
        b = [Q(rng.randrange(21), 4) for _ in range(m)]
        u = [Q(rng.randrange(1, 8), 3) for _ in range(m)]
        aggregate = [sum(u[i] * A[i][j] for i in range(m)) for j in range(n)]
        aggregate += [dot(u, b)]
        delta = rng.choice(DELTAS)
        # The shifted row is constant between these actual coefficient/RHS
        # discontinuities. CDF increments integrate each interval exactly.
        breakpoints = sorted({Q(0), delta} |
                             {z - floor(z) for z in aggregate if 0 < z - floor(z) < delta})
        for S in RAMPS.values():
            mixture = []
            target_average = [Q(0)] * (n + 1)
            for left, right in zip(breakpoints, breakpoints[1:]):
                mass = S(right / delta) - S(left / delta)
                t = (left + right) / 2
                cert, _, _, target, rhs = certificate(A, b, u, t)
                target_average = [x + mass * y for x, y in zip(target_average, [*target, rhs])]
                for weight, multiplier in cert:
                    a, beta = cg_row(list(zip(map(tuple, A), b)), multiplier)
                    mixture.append((mass * weight, (*a, beta)))
            smooth = [F(S, delta, z) for z in aggregate]
            assert target_average == smooth
            total = tuple(sum(w * v[j] for w, v in mixture) for j in range(n + 1))
            assert total[-1] == smooth[-1] and all(x >= y for x, y in zip(total[:-1], smooth[:-1]))
            short = compress_conic_certificate(mixture)
            assert len(short) <= n + 1
            assert tuple(sum(w * v[j] for w, v in short) for j in range(n + 1)) == total
            compressed += len(short) < sum(w > 0 and any(v) for w, v in mixture)
            cuts += 1
            maximum = max(maximum, len(short))
    assert compressed > 0, "compression must be exercised, not just return short inputs"
    return {"rational_smooth_cuts": cuts, "nontrivial_compressions": compressed,
            "maximum_compressed_rows": maximum, "bound_n_plus_1_holds": True}


def certificate_two_rows(A, b, u, t):
    """Sharpened proof construction: at most two CG rows imply the shifted row.

    The fixing rows of `certificate` are replaced by one row at u / min_J alpha_j,
    J = {j : alpha_j > B}. Its RHS is floor(B / min_J alpha_j) = 0 and its
    coefficient on every j in J is at least 1, so one multiple repairs all deficits.
    """
    m, n = len(A), len(A[0])
    a = [sum(u[i] * A[i][j] for i in range(m)) for j in range(n)]
    B = sum(u[i] * b[i] for i in range(m))
    target = [max(0, floor(v - t)) for v in a]
    trhs = max(0, floor(B - t))
    N, r = floor(B), B - floor(B)
    if trhs == N:
        rows = [(Q(1), list(u))]
    else:
        assert N >= 1 and t > r
        eta = (t - r) / 2
        lam = (N - eta) / B
        rows = [(Q(1), [lam * v for v in u])]
        J = [j for j in range(n) if a[j] > B]
        d = max([0] + [target[j] - floor(lam * a[j]) for j in J])
        if d:
            amin = min(a[j] for j in J)
            fix = [v / amin for v in u]
            assert floor(dot(fix, b)) == 0
            assert all(floor(sum(fix[i] * A[i][j] for i in range(m))) >= 1 for j in J)
            rows.append((Q(d), fix))
    return rows, target, trhs


def _combine(A, b, rows):
    m, n = len(A), len(A[0])
    coeff, rhs = [Q(0)] * n, Q(0)
    for w, v in rows:
        assert w >= 0 and all(z >= 0 for z in v)
        for j in range(n):
            coeff[j] += w * floor(sum(v[i] * A[i][j] for i in range(m)))
        rhs += w * floor(sum(v[i] * b[i] for i in range(m)))
    return coeff, rhs


def smooth_three_row_certificate(A, b, u, S, delta):
    """At most three CG rows imply the delayed-floor row at multiplier u.

    Shifts t <= {B} (or all t when floor(B) = 0) share the row at u. For t > {B}
    the RHS is floor(B) - 1 and the shifted coefficient vectors form a chain;
    the two-row certificate of its greatest member, attained just above {B},
    covers the whole group.
    """
    m, n = len(A), len(A[0])
    a = [sum(u[i] * A[i][j] for i in range(m)) for j in range(n)]
    B = dot(u, b)
    N, r = floor(B), B - floor(B)
    low = Q(1) if N == 0 or r >= delta else S(r / delta)   # Pr[delta T <= r]
    rows = [(low, list(u))] if low else []
    if low < 1:
        nxt = min([z - floor(z) for z in a if r < z - floor(z) < delta] + [delta])
        tstar = (r + nxt) / 2
        cert, _, _ = certificate_two_rows(A, b, u, tstar)
        rows += [((1 - low) * w, v) for w, v in cert]
    return rows, a, B


@test
def thm1_three_row_certificate(args, rng):
    """Theorem 3(i) sharpened: <= 2 CG rows per shifted row, <= 3 per smooth row;
    and the ramp-rescaling identity behind the prescribed-ramp qualifier."""
    trials = 5000 if args.quick else 60000
    shifted_by_rows = {1: 0, 2: 0}
    for _ in range(trials):
        m, n = rng.randint(1, 3), rng.randint(1, 6)
        A = [[Q(rng.randrange(41), rng.randint(1, 9)) for _ in range(n)] for _ in range(m)]
        b = [Q(rng.randrange(31), rng.randint(1, 9)) for _ in range(m)]
        u = [Q(rng.randrange(21), rng.randint(1, 11)) for _ in range(m)]
        t = Q(rng.randrange(1001), 1000)            # includes t = 1
        rows, target, trhs = certificate_two_rows(A, b, u, t)
        coeff, rhs = _combine(A, b, rows)
        assert len(rows) <= 2 and rhs == trhs
        assert all(c >= g for c, g in zip(coeff, target))
        shifted_by_rows[len(rows)] += 1
    smooth_by_rows = {1: 0, 2: 0, 3: 0}
    compressed_max = 0
    ninst = 300 if args.quick else 3000
    for _ in range(ninst):
        m, n = rng.randint(1, 3), rng.randint(1, 6)
        A = [[Q(rng.randrange(41), rng.randint(1, 9)) for _ in range(n)] for _ in range(m)]
        b = [Q(rng.randrange(31), rng.randint(1, 9)) for _ in range(m)]
        u = [Q(rng.randrange(21), rng.randint(1, 11)) for _ in range(m)]
        for S in RAMPS.values():
            for delta in DELTAS:
                rows, a, B = smooth_three_row_certificate(A, b, u, S, delta)
                coeff, rhs = _combine(A, b, rows)
                distinct = {tuple(v) for w, v in rows if w > 0}
                assert 1 <= len(distinct) <= 3
                assert rhs == F(S, delta, B), (A, b, u, delta)
                assert all(c >= F(S, delta, z) for c, z in zip(coeff, a))
                smooth_by_rows[len(distinct)] += 1
                # Conic Caratheodory: the same vector from at most min{3, n+1} rows.
                vecs = [(w, (*cg_row(list(zip(map(tuple, A), b)), v)[0],
                             cg_row(list(zip(map(tuple, A), b)), v)[1])) for w, v in rows]
                short = compress_conic_certificate(vecs)
                assert len(short) <= min(3, n + 1)
                total = tuple(sum(w * v[j] for w, v in vecs) for j in range(n + 1))
                assert tuple(sum(w * v[j] for w, v in short) for j in range(n + 1)) == total
                compressed_max = max(compressed_max, len(short))
    assert smooth_by_rows[3] > 0 and shifted_by_rows[2] > 0
    # Rescaling: with a free ramp shape, width D reproduces any width d <= D.
    resc = 0
    for name, S in RAMPS.items():
        for d in DELTAS:
            for D in DELTAS:
                if d > D:
                    continue
                St = (lambda S_, k: (lambda r: S_(k * r)))(S, D / d)
                for _ in range(40):
                    s = rand_rat(rng, 0, 12)
                    assert F(St, D, s) == F(S, d, s)
                    resc += 1
    return {"shifted_rows": trials, "shifted_by_rows": shifted_by_rows,
            "smooth_rows": sum(smooth_by_rows.values()),
            "smooth_by_distinct_rows": smooth_by_rows,
            "max_rows_after_compression": compressed_max,
            "rescaling_identity_checks": resc}


def _one_row_cg_family(a, b, qmax):
    """Undominated CG rows of one packing row a x <= b: for RHS q the row at
    v -> (q+1)/b from below, with coefficients ceil((q+1) a_j / b) - 1."""
    assert b > 0
    return [(tuple(max(0, ceil(Q(q + 1) * Q(aj) / Q(b)) - 1) for aj in a), q)
            for q in range(qmax + 1)]


def _implied_by(rows, c, beta):
    """Is c x <= beta implied on x >= 0 by a conic combination of `rows`?
    Exact LP: min sum w_i q_i s.t. sum w_i a_i >= c, w >= 0, by vertex enumeration."""
    from exactcg import inverse
    k, n = len(rows), len(c)
    cons = [([Q(r[0][j]) for r in rows], Q(c[j])) for j in range(n)]
    cons += [([Q(int(i == l)) for l in range(k)], Q(0)) for i in range(k)]
    best = None
    for sel in itertools.combinations(range(len(cons)), k):
        M = [cons[i][0] for i in sel]
        rhs = [cons[i][1] for i in sel]
        inv = inverse(M)
        if inv is None:
            continue
        w = [sum(inv[i][j] * rhs[j] for j in range(k)) for i in range(k)]
        if all(dot(coef, w) >= r for coef, r in cons):
            val = sum(wi * r[1] for wi, r in zip(w, rows))
            best = val if best is None else min(best, val)
    return best is not None and best <= beta


@test
def thm1_certificate_bounds_attained(args, rng):
    """Example after Theorem 3: three CG rows are necessary for a delayed-floor
    row and two for a shifted row (3x1 + 4x2 + 9x3 <= 6, u = 7/20)."""
    a, b, u, d = [Q(3), Q(4), Q(9)], Q(6), Q(7, 20), Q(2, 5)
    al, B = [u * x for x in a], u * b
    c = [F(ramp_smoothstep, d, x) for x in al]
    beta = F(ramp_smoothstep, d, B)
    assert [256 * x for x in c] == [11, 256, 593] and 256 * beta == 296
    rows = [((floor(v * 3), floor(v * 4), floor(v * 9)), floor(v * 6)) for v in (Q(1, 3), Q(1, 4), Q(1, 9))]
    tot = [sum(w * r[0][j] for w, r in zip((40, 216, 41), rows)) for j in range(3)]
    assert tot == [40, 256, 593] and sum(w * r[1] for w, r in zip((40, 216, 41), rows)) == 296
    qmax = 60 if args.quick else 200
    fam = _one_row_cg_family(a, b, qmax)
    assert not any(_implied_by([r], c, beta) for r in fam)
    assert not any(_implied_by(list(p), c, beta) for p in itertools.combinations(fam, 2))
    assert _implied_by(rows, c, beta)
    t = Q(1, 8)
    g = [max(0, floor(x - t)) for x in al]
    gb = max(0, floor(B - t))
    assert g == [0, 1, 3] and gb == 1
    assert not any(_implied_by([r], g, gb) for r in fam)
    assert any(_implied_by(list(p), g, gb) for p in itertools.combinations(fam, 2))
    # Deleting the oversized column x3 leaves 11x1 + 256x2 <= 296, which still needs two.
    fam2 = _one_row_cg_family(a[:2], b, qmax)
    assert not any(_implied_by([r], c[:2], beta) for r in fam2)
    assert any(_implied_by(list(p), c[:2], beta) for p in itertools.combinations(fam2, 2))
    # On P itself (original row available) two added cuts suffice.
    assert _implied_by([((3, 4, 9), 6), ((0, 0, 1), 0), ((0, 1, 2), 1)], c, beta)
    return {"smooth_row_times_256": [11, 256, 593, 296], "cg_rows_checked_up_to_rhs": qmax,
            "reduced_without_x3_needs_two": True, "on_P_two_added_cuts_suffice": True,
            "pairs_checked": len(fam) * (len(fam) - 1) // 2,
            "smooth_needs_three": True, "shifted_needs_two": True}


def recover_parameters(values):
    """epsilon, delta with F_{S,delta}((1+eps) z) = floor(z) for every z in values."""
    pos = [z for z in values if z > 0]
    eps = min((Q(floor(z) + 1) - z) / z for z in pos) / 2 if pos else Q(1, 2)
    sh = [(1 + eps) * z for z in values]
    ph = [z - floor(z) for z in sh if floor(z) >= 1]
    delta = min(min(ph) / 2, Q(1)) if ph else Q(1)
    return eps, delta


@test
def thm1_exact_recovery_all_ramps(args, rng):
    trials = 3000 if args.quick else 30000
    n_ok = 0
    for _ in range(trials):
        vals = [rand_rat(rng, 0, 15) for _ in range(rng.randint(1, 8))]
        if rng.random() < 0.5:
            vals += [Q(rng.randint(0, 9))]        # integer arguments are the hard case
        eps, delta = recover_parameters(vals)
        assert eps > 0 and 0 < delta <= 1
        for S in RAMPS.values():
            for z in vals:
                assert F(S, delta, (1 + eps) * z) == floor(z), (vals, z)
        # Also test the universal "all sufficiently small widths" quantifier.
        for z in vals:
            assert F(ramp_smoothstep, delta / 7, (1 + eps) * z) == floor(z)
        n_ok += 1
    return {"value_lists": n_ok, "ramps": list(RAMPS)}


def rand_packing(rng, n, m, cmax=5, bmax=9):
    while True:
        rows = [(tuple(rng.randint(0, cmax) for _ in range(n)), rng.randint(1, bmax))
                for _ in range(m)]
        if all(any(r[0][j] for r in rows) for j in range(n)):
            return rows


@test
def thm1_closure_equality_on_instances(args, rng):
    """For each instance: (i) all random smooth cuts are valid on C(P);
    (ii) smooth cuts reproduce every facet row of C(P); hence equality."""
    ninst = 25 if args.quick else 120
    smooth_cuts = facets = 0
    strict = 0
    for it in range(ninst):
        n = rng.choice([2, 2, 3])
        m = rng.choice([1, 2])
        rows = canonical(rand_packing(rng, n, m))[0]
        C1, der = cg_closure(rows, n)
        V1 = vertices(C1, n)
        if not same_polytope(rows, C1, n):
            strict += 1
        # (i) soundness against the exact closure, including fixed wide widths
        for _ in range(60):
            u = [rand_rat(rng, 0, 3) for _ in rows]
            S = rng.choice(list(RAMPS.values()))
            d = rng.choice(DELTAS)
            col = [F(S, d, sum(ui * r[0][j] for ui, r in zip(u, rows))) for j in range(n)]
            rhs = F(S, d, sum(ui * r[1] for ui, r in zip(u, rows)))
            assert all(dot(col, v) <= rhs for v in V1), (rows, u, d)
            smooth_cuts += 1
        # (ii) recovery of every row of C(P) by one smooth cut each
        recovered = []
        for (a, b), dv in zip(C1, der):
            u = dv["mult"]
            vals = [sum(ui * r[0][j] for ui, r in zip(u, rows)) for j in range(n)]
            vals.append(sum(ui * r[1] for ui, r in zip(u, rows)))
            eps, delta = recover_parameters(vals)
            for S in RAMPS.values():
                feat = [F(S, delta, (1 + eps) * z) for z in vals]
                assert feat == [floor(z) for z in vals]
            ca, cb = tuple(floor(z) for z in vals[:-1]), floor(vals[-1])
            # derived CG row dominates the canonical row (after scaling)
            sc = dv["scale"]
            assert all(sc * x >= y for x, y in zip(ca, a)) and sc * cb == b, (a, b, ca, cb, sc)
            recovered.append((ca, cb))
            facets += 1
        assert same_polytope(canonical(rows + recovered)[0], C1, n)
    return {"instances": ninst, "instances_with_C_strictly_inside_P": strict,
            "random_smooth_cuts_checked_against_C": smooth_cuts,
            "closure_rows_recovered_exactly": facets}


@test
def oracle_cross_check_grid_and_hull(args, rng):
    """Independent check of the closure oracle: grid multipliers + integer hull."""
    ninst = 15 if args.quick else 60
    agree = 0
    for _ in range(ninst):
        n = 2
        rows = canonical(rand_packing(rng, n, rng.choice([1, 2]), 4, 7))[0]
        C1, _ = cg_closure(rows, n)
        G = grid_closure(rows, n, 12 if len(rows) == 2 else 30)
        VC, VG = vertices(C1, n), vertices(G, n)
        # grid closure is a relaxation of C(P): C(P) subset grid
        assert all(contains(G, v) for v in VC)
        assert VC == VG, (rows, C1, G)
        # integer hull inside C(P), and C(P) inside P
        for x in integer_points(rows, n):
            assert contains(C1, x)
        assert all(contains(rows, v) for v in VC)
        agree += 1
    # rank-2 cross-check on the worked example
    C1, _ = cg_closure([((3, 4), 6)], 2)
    G2 = grid_closure(C1, 2, 8)
    assert vertices(G2, 2) == vertices(cg_closure(C1, 2)[0], 2)
    return {"instances_grid_equals_oracle": agree, "rank2_example_grid_D": 8}


@test
def oracle_separate_support_arithmetic_and_guards(args, rng):
    # Hand-selected cases include a face, a point, redundant rows, and a rank-2
    # polytope. Random sampling alone previously omitted most such boundaries.
    instances = [[((3, 4), 6)], [((1, 1), 0)],
                 [((1, 0), 0), ((0, 2), 3)],
                 [((2, 1), 3), ((1, 2), 3), ((4, 2), 6)],
                 [((0, 0), 2), ((1, 1), 3)]]
    instances += [rand_packing(rng, 2, rng.choice([1, 2]), 3, 6)
                  for _ in range(5 if args.quick else 15)]
    count = 0
    for rows in instances:
        ref_vertices = reference_vertices_2d(rows)
        assert ref_vertices == vertices(rows, 2)
        assert ref_vertices == vertices(canonical(rows)[0], 2)
        exact, derivs = cg_closure(rows, 2)
        assert vertices(exact, 2) == support_closure_2d(rows)
        assert vertices(exact, 2), "empty comparisons cannot certify equality"
        for (a, b), dv in zip(exact, derivs):
            ca, cb = cg_row(rows, dv["mult"])
            assert tuple(dv["scale"] * x for x in ca) == a
            assert dv["scale"] * cb == b
        count += 1
    rejected = 0
    for action in (lambda: canonical([((Q(3, 2), 1), 2)]),
                   lambda: canonical([((1, 1), Q(3, 2))]),
                   lambda: cg_closure([((1, 0), 2)], 2),
                   lambda: cg_closure([((1, 1), -1)], 2)):
        try:
            action()
        except AssertionError:
            rejected += 1
    assert rejected == 4
    # Shared rounding/canonical bugs would not cancel in this separate path.
    witness = [((3, 4), 6)]
    oracle, _ = cg_closure(witness, 2)
    weakened = [(a, b + 1) for a, b in oracle]
    assert reference_vertices_2d(weakened) != support_closure_2d(witness)
    return {"separate_support_oracle_matches": count,
            "invalid_inputs_rejected": rejected,
            "weakened_rhs_mutation_detected": True}


@test
def thm1_fixed_width_counterexample(args, rng):
    """P = [0, 3/2] (row x <= 3/2): at fixed delta = 1, every cut is redundant."""
    worst = None
    for name in ("linear", "smoothstep", "smootherstep"):
        S = RAMPS[name]
        for k in range(1, 6001):
            u = Q(k, 200)                       # u in (0, 30]
            a, b = F(S, Q(1), u), F(S, Q(1), u * Q(3, 2))
            if a > 0:
                lim = b / a
                assert lim >= Q(3, 2), (name, u, lim)
                worst = lim if worst is None else min(worst, lim)
            else:
                assert b >= 0
    # C(P) = [0,1] is reached by an ordinary CG cut (u = 1).
    assert (floor(Q(1)), floor(Q(3, 2))) == (1, 1)
    # smooth-ramp deviation bound used in the analytic argument
    dev = max(abs(ramp_smoothstep(Q(i, 10000)) - Q(i, 10000)) for i in range(10001))
    assert dev < Q(1, 5)
    return {"min_cut_bound_over_grid": str(worst), "C(P)": "[0,1]",
            "smoothstep_max_|S(r)-r|": float(dev), "needs_<_0.2": bool(dev < Q(1, 5))}


# ---------------------------------------------------------------------------
# Theorem 2: depth k = rank k (soundness and recovery)
# ---------------------------------------------------------------------------


def random_network(rng, rows, n, depth, width):
    """Returns list of layers; each neuron = (S, delta, u_on_inputs, lam_on_prev)."""
    layers = []
    for L in range(depth):
        prev = sum(len(l) for l in layers)
        layer = []
        for _ in range(width):
            u = [rand_rat(rng, 0, 2, (1, 2, 3, 4, 5)) for _ in rows]
            lam = [rand_rat(rng, 0, 2, (1, 2, 3)) for _ in range(prev)]
            if L > 0 and not any(lam):
                lam[rng.randrange(prev)] = Q(1)
            layer.append((rng.choice(list(RAMPS)), rng.choice(DELTAS), u, lam))
        layers.append(layer)
    return layers


def evaluate_network(layers, rows, n):
    """Rows (coefficients on x, rhs) of every neuron, with their depth."""
    cols = [[r[0][j] for r in rows] for j in range(n)] + [[r[1] for r in rows]]
    outs = [[] for _ in cols]           # per column (+ rhs), outputs so far
    cuts = []
    depths = []
    for layer in layers:
        new = []
        new_depths = []
        for S, d, u, lam in layer:
            assert len(u) == len(rows) and len(lam) == len(depths)
            depth = 1 + max((dp for weight, dp in zip(lam, depths) if weight > 0), default=0)
            vals = []
            for c, o in zip(cols, outs):
                z = sum(ui * ci for ui, ci in zip(u, c)) + sum(li * oi for li, oi in zip(lam, o))
                vals.append(F(RAMPS[S], d, z))
            new.append(vals)
            new_depths.append(depth)
            cuts.append((depth, vals))
        for vals in new:
            for k in range(len(cols)):
                outs[k].append(vals[k])
        depths.extend(new_depths)
    return cuts


@test
def thm2_soundness_random_networks(args, rng):
    ninst = 10 if args.quick else 40
    checked = 0
    beyond = 0   # depth-k cuts NOT valid for C^{k-1}: shows depth is used
    by_depth = {}
    rows_by_depth = {}
    networks = 0
    for _ in range(ninst):
        n = rng.choice([2, 3])
        rows = canonical(rand_packing(rng, n, rng.choice([1, 2]), 5, 9))[0]
        seq = closure_sequence(rows, n, 3)
        Vs = [vertices(r, n) for r, _ in seq]
        for _ in range(8):
            layers = random_network(rng, rows, n, rng.randint(1, 3), rng.randint(1, 3))
            networks += 1
            for depth, vals in evaluate_network(layers, rows, n):
                rows_by_depth[depth] = rows_by_depth.get(depth, 0) + 1
                k = min(depth, len(Vs) - 1)
                assert all(dot(vals[:-1], v) <= vals[-1] for v in Vs[k]), (rows, depth, vals)
                if depth - 1 < len(Vs) - 1 and any(dot(vals[:-1], v) > vals[-1]
                                                   for v in Vs[depth - 1]):
                    beyond += 1
                    by_depth[depth] = by_depth.get(depth, 0) + 1
                checked += 1
    return {"instances": ninst, "networks": networks, "neuron_cuts_checked": checked,
            "neuron_rows_by_depth": rows_by_depth,
            "cuts_using_their_full_depth": beyond,
            "full_depth_cuts_by_actual_depth": by_depth,
            "full_depth_cuts_of_depth_at_least_2": sum(v for k, v in by_depth.items() if k >= 2)}


def compile_closure_network(rows, n, seq):
    """Compile actual nonnegative DAG weights, using one width at every neuron.

    Canonical rows may be positive multiples of neuron outputs; their factors
    are absorbed into subsequent weights, not silently treated as activations.
    Return layers and each closure row's (input/neuron, index, scale) reference.
    """
    refs = [[("input", i, Q(1)) for i in range(len(rows))]]
    layers, thresholds = [], []
    count = 0
    for level in range(1, len(seq)):
        previous_rows, _ = seq[level - 1]
        rk, derivs = seq[level]
        layer, next_refs = [], []
        for (a, b), dv in zip(rk, derivs):
            u, lam = [Q(0)] * len(rows), [Q(0)] * count
            assert len(dv["mult"]) == len(refs[-1])
            for mult, (kind, index, scale) in zip(dv["mult"], refs[-1]):
                (u if kind == "input" else lam)[index] += mult * scale
            z = [sum(mu * (r[0][j] if j < n else r[1])
                     for mu, r in zip(dv["mult"], previous_rows)) for j in range(n + 1)]
            eps, threshold = recover_parameters(z)
            thresholds.append(threshold)
            layer.append(("smoothstep", threshold,
                          [(1 + eps) * w for w in u], [(1 + eps) * w for w in lam]))
            next_refs.append(("neuron", count + len(layer) - 1, dv["scale"]))
        count += len(layer)
        layers.append(layer)
        refs.append(next_refs)
    width = min(thresholds, default=Q(1))
    layers = [[(name, width, u, lam) for name, _, u, lam in layer] for layer in layers]
    return layers, refs, width


def network_values(layers, y):
    """Evaluate the compiled, fixed network on an arbitrary nonnegative input."""
    assert all(z >= 0 for z in y)
    out = []
    for layer in layers:
        new = []
        for name, delta, u, lam in layer:
            assert len(u) == len(y) and len(lam) == len(out)
            assert all(w >= 0 for w in (*u, *lam))
            z = dot(u, y) + dot(lam, out)
            new.append(F(RAMPS[name], delta, z))
        out.extend(new)
    return out


def referenced_values(layers, refs, y):
    out = network_values(layers, y)
    return [scale * (y if kind == "input" else out)[index]
            for kind, index, scale in refs]


def simulate_closure_network(rows, n, seq):
    layers, refs, width = compile_closure_network(rows, n, seq)
    cols = [[Q(r[0][j]) for r in rows] for j in range(n)] + [[Q(r[1]) for r in rows]]
    for name in RAMPS:
        chosen = [[(name, d, u, lam) for _, d, u, lam in layer] for layer in layers]
        assert all(d == width for layer in chosen for _, d, _, _ in layer)
        for k, (rk, _) in enumerate(seq):
            matrix = [referenced_values(chosen, refs[k], y) for y in cols]
            net_rows = [(tuple(matrix[j][i] for j in range(n)), matrix[n][i])
                        for i in range(len(rk))]
            assert net_rows == rk, (name, k, net_rows, rk)
            assert vertices(net_rows, n) and vertices(net_rows, n) == vertices(rk, n)
    return sum(len(layer) for layer in layers), len(layers), width


@test
def thm2_recovery_builds_Ck_exactly(args, rng):
    ninst = 10 if args.quick else 40
    total_neurons = 0
    depth_hist = {}
    insts = [[((3, 4), 6)], [((3, 4, 4), 6)], [((2, 1), 3), ((1, 2), 3)]]
    while len(insts) < ninst:
        insts.append(canonical(rand_packing(rng, rng.choice([2, 3]), rng.choice([1, 2]), 5, 9))[0])
    for rows in insts:
        n = len(rows[0][0])
        rows = canonical(rows)[0]
        seq = closure_sequence(rows, n, 4)
        nn, K, common_width = simulate_closure_network(rows, n, seq)
        assert 0 < common_width <= 1
        total_neurons += nn
        depth_hist[K] = depth_hist.get(K, 0) + 1
    return {"instances": len(insts), "neurons_simulated_exactly": total_neurons,
            "closure_levels_histogram": {str(k): v for k, v in sorted(depth_hist.items())},
            "one_common_width_per_network": True, "ramps_replayed": list(RAMPS)}


@test
def thm2_explicit_rank2_example(args, rng):
    d = Q(1, 10)
    S = ramp_smoothstep
    f1 = tuple(F(S, d, Q(3, 10) * z) for z in (3, 4, 6))
    f2 = tuple(F(S, d, Q(4, 5) * z) for z in (3, 4, 6))
    f3 = tuple(F(S, d, Q(11, 20) * (a + b)) for a, b in zip(f1, f2))
    assert f1 == (0, 1, 1) and f2 == (2, 3, 4) and f3 == (1, 2, 2)
    C1, _ = cg_closure([((3, 4), 6)], 2)
    C2, _ = cg_closure(C1, 2)
    assert C1 == [((0, 1), 1), ((2, 3), 4)] and C2 == [((1, 2), 2)]
    assert contains(C1, (Q(1, 2), Q(1))) and not contains(C2, (Q(1, 2), Q(1)))
    # no depth-1 smooth cut on a fine grid removes (1/2, 1)
    worst = None
    for k in range(1, 801):
        u = Q(k, 80)
        for dd in DELTAS:
            for S2 in RAMPS.values():
                a, b, r = F(S2, dd, 3 * u), F(S2, dd, 4 * u), F(S2, dd, 6 * u)
                slack = r - (a / 2 + b)
                worst = slack if worst is None else min(worst, slack)
                assert slack >= 0
    return {"features": [list(map(str, f)) for f in (f1, f2, f3)],
            "depth2_cut": "x + 2y <= 2", "min_depth1_slack_at_(1/2,1)": str(worst)}


# ---------------------------------------------------------------------------
# Section 5: closure-value identity and objective rank
# ---------------------------------------------------------------------------


def lp_dual_certificate(rows, n, c):
    """min lam.b s.t. lam^T A >= c, lam >= 0 by enumeration of dual bases (exact)."""
    from itertools import combinations as comb_
    from exactcg import inverse
    m = len(rows)
    best = None
    # Dual constraints: sum_i lam_i a_ij >= c_j (n of them), lam >= 0 (m of them).
    cons = [([rows[i][0][j] for i in range(m)], c[j]) for j in range(n)]
    cons += [([int(i == k) for i in range(m)], 0) for k in range(m)]
    for inds in comb_(range(len(cons)), m):
        Mt = [cons[i][0] for i in inds]
        inv = inverse(Mt)
        if inv is None:
            continue
        rhs = [Q(cons[i][1]) for i in inds]
        lam = [sum(inv[r][k] * rhs[k] for k in range(m)) for r in range(m)]
        if all(dot(a, lam) >= bb for a, bb in cons):
            val = sum(l * r[1] for l, r in zip(lam, rows))
            if best is None or val < best[0]:
                best = (val, lam)
    return best


@test
def cor3_closure_value_identity(args, rng):
    ninst = 15 if args.quick else 60
    checks = 0
    pairs_by_k = {}
    for _ in range(ninst):
        n = rng.choice([2, 3])
        rows = canonical(rand_packing(rng, n, rng.choice([1, 2]), 5, 9))[0]
        c = [rng.randint(1, 6) for _ in range(n)]
        seq = closure_sequence(rows, n, 3)
        layers, refs, _ = compile_closure_network(rows, n, seq)
        for k, (rk, _) in enumerate(seq):
            primal = max_over(rk, n, c)
            dual = lp_dual_certificate(rk, n, c)
            assert dual is not None
            val, lam = dual
            # Evaluate an actual fixed smooth DAG and LP-dual output layer.
            active = layers[:k]
            G_cols = [dot(lam, referenced_values(active, refs[k], [r[0][j] for r in rows]))
                      for j in range(n)]
            G_rhs = dot(lam, referenced_values(active, refs[k], [r[1] for r in rows]))
            assert all(g >= cj for g, cj in zip(G_cols, c))      # column feasibility
            assert G_rhs == val == primal, (rows, c, k, G_rhs, val, primal)
            checks += 1
            pairs_by_k[k] = pairs_by_k.get(k, 0) + 1
    # k runs over 0, 1, ... until C^k = C^{k-1} (that repeated level included) or k = 3.
    return {"instances": ninst, "(instance,k)_pairs_exact_equality": checks,
            "pairs_by_k": pairs_by_k,
            "actual_compiled_network_evaluated": True}


@test
def example_3x4y_table(args, rng):
    hull, obj, exact_values = {}, {}, {}
    for b in range(0, 13):
        rows = [((3, 4), b)] if b > 0 else [((3, 4), 0)]
        z = max(x + y for x, y in integer_points([((3, 4), b)], 2))
        assert z == b // 3
        exact_values[b] = z
        if b == 0:
            hull[b] = obj[b] = 0
            continue
        seq = closure_sequence(canonical(rows)[0], 2, 5)
        hk = next(k for k, (r, _) in enumerate(seq)
                  if all(all(int(t) == t for t in v) for v in vertices(r, 2)))
        ok = next(k for k, (r, _) in enumerate(seq) if max_over(r, 2, (1, 1)) == z)
        hull[b], obj[b] = hk, ok
    assert [hull[b] for b in range(13)] == [0, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0]
    assert [obj[b] for b in range(13)] == [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]
    # G(t) = floor(t/3): column feasible, exact value function on B
    G = lambda t: Q(floor(Q(t, 3)))
    assert G(3) >= 1 and G(4) >= 1 and all(G(b) == b // 3 for b in range(13))
    # depth 0 impossible: z not concave on the integer grid
    assert exact_values[2] < Q(exact_values[1] + exact_values[3], 2)
    # One fixed smooth neuron must fit both the columns and every RHS in B.
    inputs = [Q(b, 3) for b in range(13)] + [Q(3, 3), Q(4, 3)]
    eps, width = recover_parameters(inputs)
    for S in RAMPS.values():
        smooth_G = lambda t: F(S, width, (1 + eps) * Q(t, 3))
        assert smooth_G(3) >= 1 and smooth_G(4) >= 1
        assert all(smooth_G(b) == exact_values[b] for b in range(13))
    return {"hull_rank": hull, "objective_rank": obj,
            "min_value_function_depth": 1, "max_hull_rank": max(hull.values()),
            "fixed_smooth_neuron_exact_on_all_13_rhs": True}


@test
def cor4_fixed_branch_min_pool_on_finite_rhs(args, rng):
    domain = range(13)
    pair_checks = branches = 0
    ranks = {}
    for c in ((1, 1), (1, 2)):
        z = {b: max(dot(c, x) for x in integer_points([((3, 4), b)], 2)) for b in domain}
        fixed = []
        for anchor in domain:
            rows = [((3, 4), anchor)]
            seq = closure_sequence(rows, 2, 4)
            depth = next(k for k, (r, _) in enumerate(seq) if max_over(r, 2, c) == z[anchor])
            layers, refs, _ = compile_closure_network(rows, 2, seq[:depth + 1])
            val, lam = lp_dual_certificate(seq[depth][0], 2, c)
            assert val == z[anchor]
            for col, cost in zip((3, 4), c):
                assert dot(lam, referenced_values(layers, refs[-1], [Q(col)])) >= cost
            fixed.append((layers, refs[-1], lam, depth))
            branches += 1
        for b in domain:
            bounds = [dot(lam, referenced_values(layers, ref, [Q(b)]))
                      for layers, ref, lam, _ in fixed]
            assert all(bound >= z[b] for bound in bounds)
            assert min(bounds) == z[b]
            pair_checks += len(bounds)
        ranks[str(c)] = max(depth for _, _, _, depth in fixed)
    assert ranks["(1, 2)"] == 2, "the rank-2 case must be covered"
    return {"fixed_branches": branches, "cross_anchor_rhs_evaluations": pair_checks,
            "max_objective_rank_by_cost": ranks, "min_pool_exact_at_every_rhs": True}


@test
def objective_rank_vs_hull_rank_random(args, rng):
    ninst = 12 if args.quick else 40
    strict = total = 0
    for _ in range(ninst):
        n = 2
        A = [(rng.randint(1, 6), rng.randint(1, 6))]
        c = (rng.randint(1, 4), rng.randint(1, 4))
        mh = mo = 0
        for b in range(1, 15):
            rows = canonical([(A[0], b)])[0]
            seq = closure_sequence(rows, n, 5)
            z = max(dot(c, x) for x in integer_points(rows, n))
            hk = next((k for k, (r, _) in enumerate(seq)
                       if all(all(int(t) == t for t in v) for v in vertices(r, n))), None)
            ok = next((k for k, (r, _) in enumerate(seq) if max_over(r, n, c) == z), None)
            assert hk is not None and ok is not None and ok <= hk
            mh, mo = max(mh, hk), max(mo, ok)
        total += 1
        strict += mo < mh
    return {"families": total, "families_with_max_obj_rank_<_max_hull_rank": strict}


# ---------------------------------------------------------------------------
# Scope: complementation and invalid signed inputs
# ---------------------------------------------------------------------------


@test
def complementation_scope(args, rng):
    # (a) a covering row with box: 2x1 + 3x2 >= 4, 0 <= x <= (3,2). Substitute
    # y = u - x: 2y1 + 3y2 <= 2*3 + 3*2 - 4 = 8, y <= (3,2).
    pack = canonical([((2, 3), 8), ((1, 0), 3), ((0, 1), 2)])[0]
    C1p, _ = cg_closure(pack, 2)
    # Direct closure of the covering system (signed rows incl. bounds), by an
    # independent grid oracle, equals the pulled-back packing closure.
    from exactcg import general_grid_closure, general_vertices
    cover = [((-2, -3), -4), ((1, 0), 3), ((0, 1), 2), ((-1, 0), 0), ((0, -1), 0)]
    Cc = general_grid_closure(cover, 4)
    Vc = general_vertices(Cc, 2)
    Vp = sorted((3 - y1, 2 - y2) for y1, y2 in vertices(C1p, 2))
    assert Vc == Vp, (Vc, Vp)
    Pp2, _ = cg_closure(C1p, 2)
    Cc2 = general_grid_closure(Cc, 3) if len(Cc) <= 9 else None
    rank2 = None
    if Cc2 is not None:
        rank2 = general_vertices(Cc2, 2) == sorted((3 - y1, 2 - y2) for y1, y2 in vertices(Pp2, 2))
        assert rank2
    # Rank-2 covering example: 3x1 + 4x2 >= 8, 0 <= x <= (2,2) is the
    # complement of 3y1 + 4y2 <= 6, y <= (2,2) (box rows LP-redundant) under
    # x = (2,2) - y.
    def facets2d(rows_):
        V = general_vertices(rows_, 2)
        return [r for r in rows_ if sum(dot(r[0], v) == r[1] for v in V) >= 2]
    cov = [((-3, -4), -8), ((1, 0), 2), ((0, 1), 2), ((-1, 0), 0), ((0, -1), 0)]
    pk = canonical([((3, 4), 6), ((1, 0), 2), ((0, 1), 2)])[0]
    pseq = closure_sequence(pk, 2, 4)
    cur = cov
    rank2_levels = []
    for k in (1, 2):
        cur = facets2d(general_grid_closure(cur, 6 if k == 1 else 4))
        mapped = sorted((2 - y1, 2 - y2) for y1, y2 in vertices(pseq[k][0], 2))
        rank2_levels.append(general_vertices(cur, 2) == mapped)
        assert rank2_levels[-1], (k, general_vertices(cur, 2), mapped)
    assert not same_polytope(pseq[1][0], pseq[2][0], 2)   # genuinely rank 2
    rank2 = all(rank2_levels)
    # Integer hull mapping check: x integer feasible <-> y integer feasible
    xs = {(x1, x2) for x1 in range(4) for x2 in range(3) if 2 * x1 + 3 * x2 >= 4}
    ys = {(3 - y1, 2 - y2) for y1, y2 in integer_points(pack, 2)}
    assert xs == ys
    # Closure commutes with the integral affine map: test each C(P') row pulled
    # back is a valid CG cut of the original covering system (shown via its
    # multiplier on the transformed rows, which is the same multiplier on the
    # original rows because the map is integral and unimodular).
    # (b) conflicting signs: x1 - x2 <= 0 and -x1 + x2 <= 0 need opposite s.
    A = [(1, -1), (-1, 1)]
    feasible_signs = [s for s in product((1, -1), repeat=2)
                      if all(r[0] * s[0] >= 0 and r[1] * s[1] >= 0 for r in A)]
    assert feasible_signs == []
    # (c) Deliberately extend the nonnegative-domain formula by zero to negative
    # arguments. Applied to 2x1-2x2<=0 it produces x1<=0, invalid at (1,1).
    # Coefficients +/-1 would NOT witness this for smooth F because F(1)=0.
    signed_source, witness = (Q(2), Q(-2)), (Q(1), Q(1))
    assert dot(signed_source, witness) <= 0
    for S in RAMPS.values():
        cut = tuple(F(S, Q(1, 2), z) for z in (*signed_source, Q(0)))
        assert cut == (1, 0, 0) and dot(cut[:-1], witness) > cut[-1]
    return {"covering_closure_equals_pulled_back_packing_closure": True,
            "rank2_also_checked": rank2, "closure_vertices": [list(map(str, v)) for v in Vc],
            "covering_to_packing_integer_points_match": len(xs),
            "transformed_closure_rows": len(C1p),
            "conflicting_sign_choices_available": 0,
            "signed_input_counterexample": "zero-extension of F: 2x1 - 2x2 <= 0 -> x1 <= 0 cuts (1,1)"}


def lifted_packing_rows(rows, U):
    """Packing relaxation in coordinate order (x, x'), for a nonempty box IP."""
    n = len(U)
    assert all(u >= 0 and Q(u).denominator == 1 for u in U)
    out = []
    for a, b in rows:
        assert len(a) == n
        pos = tuple(max(c, 0) for c in a)
        neg = tuple(max(-c, 0) for c in a)
        rhs = b + dot(neg, U)
        assert rhs >= 0
        out.append((pos + neg, rhs))
    for j, u in enumerate(U):
        e = [0] * (2 * n)
        e[j] = e[n + j] = 1
        out.append((tuple(e), u))
    return canonical(out)[0]


def pullback_lifted_rows(rows, U):
    """Substitute x' = U - x; callers also supply the original box bounds."""
    n = len(U)
    return [(tuple(a[j] - a[n + j] for j in range(n)),
             b - dot(a[n:], U)) for a, b in rows]


@test
def lifting_remark_mixed_sign_rank1(args, rng):
    """Exact lifted closure vs a finite signed multiplier grid (shared helpers).

    The grid is a cross-check, not a complete signed-closure oracle in general.
    """
    from exactcg import general_grid_closure, general_vertices
    cases = [([((1, -1), 0), ((-1, 1), 0)], (1, 1)),       # x1 = x2: conflicting signs
             ([((2, -2), 1), ((-2, 2), 1)], (2, 2))]       # |x1 - x2| <= 1/2: C(P) < P
    target = 4 if args.quick else 8
    while len(cases) < target:
        U = (rng.randint(1, 2), rng.randint(1, 2))
        rows = [((rng.randint(1, 3), -rng.randint(1, 3)), rng.randint(0, 3)),
                ((-rng.randint(1, 3), rng.randint(1, 3)), rng.randint(0, 3))]
        box = [((1, 0), U[0]), ((0, 1), U[1]), ((-1, 0), 0), ((0, -1), 0)]
        V = general_vertices(rows + box, 2)
        # keep only instances with a fractional LP vertex, so the closure acts
        if V and any(int(t) != t for v in V for t in v):
            cases.append((rows, U))
    strict = 0
    for rows, U in cases:
        box = [((1, 0), U[0]), ((0, 1), U[1]), ((-1, 0), 0), ((0, -1), 0)]
        P_v = general_vertices(rows + box, 2)
        CP = general_vertices(general_grid_closure(rows + box, 4), 2)
        CL, _ = cg_closure(lifted_packing_rows(rows, U), 4)
        CT = general_vertices(pullback_lifted_rows(CL, U) + box, 2)
        assert CT == CP, (rows, U, CP, CT)
        strict += CP != P_v
    assert strict >= len(cases) - 1   # all but the integral x1 = x2 case
    return {"instances": len(cases), "instances_with_C(P)_strictly_inside_P": strict,
            "includes_conflicting_sign_example": "x1 = x2 on [0,1]^2",
            "note": "rank 1 only; C(P) by grid multipliers (denominators <= 4)"}


@test
def lifting_remark_rank2_and_empty_slice(args, rng):
    """Two strict lifted rounds, an empty slice, and real-to-integer penalties."""
    from exactcg import general_grid_closure, general_vertices
    # A conflicting-sign triangle of CG rank 2. Its integer hull is the base
    # segment. In C(P), the two sloping cuts give the smaller triangle below.
    # The new apex survives every integral support cut: for h=(a,b), b<=0 is
    # covered by the integral base; for b>=1, the old apex support a/2+b,
    # rounded down, is at least (a+b)/2. Round 2 rounds max y=1/2 to zero.
    signed = [((-2, 1), 0), ((2, 1), 2)]
    U = (1, 1)
    box = [((1, 0), 1), ((0, 1), 1), ((-1, 0), 0), ((0, -1), 0)]
    expected = [sorted([(Q(0), Q(0)), (Q(1), Q(0)), (Q(1, 2), Q(1))]),
                sorted([(Q(0), Q(0)), (Q(1), Q(0)), (Q(1, 2), Q(1, 2))]),
                [(Q(0), Q(0)), (Q(1), Q(0))]]
    # A separate signed-grid path generates the two explicit sloping cuts
    # and then y<=0. The hand-derived expected sets establish this example's
    # complete closures; the grid is not advertised as complete in general.
    direct1 = general_grid_closure(signed + box, 2)
    assert general_vertices(direct1, 2) == expected[1]
    direct2 = general_grid_closure([((-1, 1), 0), ((1, 1), 1), ((0, -1), 0)], 2)
    assert general_vertices(direct2, 2) == expected[2]
    rows = lifted_packing_rows(signed, U)
    seq = [(rows, None)]
    slices = []
    for k in range(3):
        if k:
            nxt, derivs = cg_closure(seq[-1][0], 4)
            seq.append((nxt, derivs))
        sliced = general_vertices(pullback_lifted_rows(seq[k][0], U) + box, 2)
        assert sliced == expected[k], (k, sliced, expected[k])
        slices.append(sliced)
    assert slices[0] != slices[1] and slices[1] != slices[2]
    assert contains(seq[1][0], (Q(1, 2), Q(1, 2), Q(1, 2), Q(1, 2)))
    assert not contains(seq[2][0], (Q(1, 2), Q(1, 2), Q(1, 2), Q(1, 2)))
    # Replay actual nonnegative networks on the four lifted columns and RHS,
    # for all three ramps with a single common width in each network.
    neurons, depth, width = simulate_closure_network(rows, 4, seq)
    assert depth == 2

    # P={1/2}, U=1 is nonempty but lattice-free and lower-dimensional.
    # C(P) is empty (x<=0 and x>=1). The packing closures still contain 0,
    # while their slices are empty at both ranks 1 and 2. Rank 2 exercises
    # precisely the branch where the preceding slice is already empty.
    empty_rows = lifted_packing_rows([((2,), 1), ((-2,), -1)], (1,))
    box1 = [((1,), 1), ((-1,), 0)]
    assert general_vertices(pullback_lifted_rows(empty_rows, (1,)) + box1, 1) == [(Q(1, 2),)]
    empty_levels = []
    for k in (1, 2):
        empty_rows, _ = cg_closure(empty_rows, 2)
        assert contains(empty_rows, (0, 0))
        assert general_vertices(pullback_lifted_rows(empty_rows, (1,)) + box1, 1) == []
        empty_levels.append(k)

    # P={0} from 2x1-x2<=0, x2<=0, U=(1,1). For c=(1,0), delta=0,
    # a valid optimal linking penalty is mu=(0,1/2), not an integer vector.
    # The origin and (1/2,0,0,0) force mu_2>=1/2 when mu_1=0.
    penalty_rows = lifted_packing_rows([((2, -1), 0), ((0, 1), 0)], U)
    assert general_vertices(pullback_lifted_rows(penalty_rows, U) + box, 2) == [(Q(0), Q(0))]
    c, delta, mu = (1, 0), Q(0), (Q(0), Q(1, 2))
    lam = tuple(math.ceil(v) for v in mu)
    assert lam == (0, 1) and mu != lam
    for penalty in (mu, lam):
        normal = tuple(cj + v for cj, v in zip(c, penalty)) + penalty
        rhs = delta + dot(penalty, U)
        assert max_over(penalty_rows, 4, normal) == rhs
    rounded_normal = tuple(cj + v for cj, v in zip(c, lam)) + lam
    assert pullback_lifted_rows([(rounded_normal, floor(delta + dot(lam, U)))], U) == [(c, floor(delta))]
    witness = (Q(1, 2), Q(0), Q(0), Q(0))
    assert contains(penalty_rows, witness)
    assert dot(c, witness[:2]) > delta   # dropping the penalty is invalid
    return {"strict_lifted_rounds": 2, "slice_vertex_counts": list(map(len, slices)),
            "lifted_closure_rows": [len(r) for r, _ in seq],
            "replayed_neurons": neurons, "network_depth": depth,
            "common_width": str(width), "ramps": len(RAMPS),
            "empty_slice_ranks": empty_levels, "packing_closures_remain_nonempty": True,
            "fractional_linking_penalty": list(map(str, mu)),
            "rounded_linking_penalty": list(lam)}


# ---------------------------------------------------------------------------
# Proposition 4: accuracy vs Lipschitz constant
# ---------------------------------------------------------------------------


@test
def prop4_frontier_exact(args, rng):
    out = {}
    for G in (1, 2, 3, 4, 10, 25):
        d = Q(1, G)
        Fr = lambda s: F(ramp_linear, d, s)
        # Lipschitz constant G and minorant of floor
        for s in tricky_points(6):
            assert Fr(s) <= floor(s)
        for _ in range(500):
            s, t = rand_rat(rng, 0, 8), rand_rat(rng, 0, 8)
            assert abs(Fr(s) - Fr(t)) <= G * abs(s - t)
        # integrated error on [0, L] = (L-1)/(2G) exactly (piecewise linear)
        for L in (2, 3, 7):
            err = Q(L - 1, 2 * G)
            # direct exact integration of floor - F: the integrand is affine on
            # each piece between breakpoints, so the midpoint rule is exact.
            brk = sorted({Q(k) for k in range(L + 1)} | {Q(k) + d for k in range(1, L)})
            direct = sum((b - a) * (floor((a + b) / 2) - Fr((a + b) / 2))
                         for a, b in zip(brk, brk[1:]))
            assert direct == err, (G, L, direct, err)
        # uniform error on K_eps = max(1 - G eps, 0), attained just right of k+eps
        for eps in (Q(1, 10), Q(1, 3), Q(1, 2)):
            sup = max(floor(k + eps) - Fr(k + eps) for k in range(1, 6))
            assert sup == max(1 - G * eps, 0)
        # Generate admissible PL minorants independently of the extremal ramp.
        # On each half-unit segment choose a nonnegative slope <= G, with the
        # right endpoint below the floor's LEFT limit. These endpoint/slope
        # conditions certify continuity, monotonicity, minorant and Lipschitz
        # properties everywhere on [0,6], not merely at sampled points.
        for _ in range(200):
            values = [Q(0)]
            for j in range(1, 13):
                x = Q(j, 2)
                left_limit = (x.numerator - 1) // x.denominator
                ceiling = min(values[-1] + Q(G, 2), left_limit)
                assert ceiling >= values[-1]
                values.append(values[-1] + Q(rng.randrange(11), 10) * (ceiling - values[-1]))
            for j in range(1, 13):
                assert 0 <= 2 * (values[j] - values[j - 1]) <= G
                x = Q(j, 2)
                assert values[j] <= (x.numerator - 1) // x.denominator
            def Fz(s):
                if s == 6:
                    return values[-1]
                j = floor(2 * s)
                return values[j] + (2 * s - j) * (values[j + 1] - values[j])
            for k in range(1, 5):
                for t in (Q(0), Q(1, 7), Q(1, 3), Q(2, 3)):
                    assert k - Fz(k + t) >= max(1 - G * t, 0)
            for L in (2, 3, 5):
                integral = sum((floor(Q(2 * j + 1, 4)) - Fz(Q(2 * j + 1, 4))) / 2
                               for j in range(2 * L))
                assert integral >= Q(L - 1, 2 * G)
        # A width mutation doubles the slope and breaks the claimed G bound.
        t = Q(1, 2 * G)
        wrong = F(ramp_linear, Q(1, 2 * G), 1 + t)
        assert 1 - wrong < max(1 - G * t, 0)
        out[G] = {"L1_error_per_unit": str(Q(1, 2 * G)),
                  "independent_admissible_PL_minorants": 200,
                  "too_steep_mutation_detected": True}
    return out


# ---------------------------------------------------------------------------
# Appendix: dense MIK generator collapse bound
# ---------------------------------------------------------------------------


def qn_rn_exact(n):
    tot = (n + 1) ** 3
    surv_pair = sum(1 for b in range(n, 2 * n + 1)
                    for a1 in range(n + 1) for a2 in range(n + 1) if a1 + a2 <= b)
    surv_rep = sum(1 for b in range(n, 2 * n + 1) for a in range(n + 1) if 2 * a <= b)
    return Q(surv_pair, tot), Q(surv_rep, (n + 1) ** 2)


@test
def mik_generator_bound(args, rng):
    import numpy as np
    for n in range(1, 41):
        q, r = qn_rn_exact(n)
        assert q == 1 - Q(n * (n + 2), 6 * (n + 1) ** 2), n
        assert r == Q(sum(b // 2 + 1 for b in range(n, 2 * n + 1)), (n + 1) ** 2), n
    def bound(m, n):
        q = 1 - Q(n * (n + 2), 6 * (n + 1) ** 2)
        r = Q(sum(b // 2 + 1 for b in range(n, 2 * n + 1)), (n + 1) ** 2)
        return comb(n, 2) * q ** m + n * r ** m
    b_med = bound(100, 200)
    assert abs(b_med - Q("0.0002404051")) < Q(1, 10**9)
    # Monte Carlo at the medium size: every sampled instance collapses
    gen = np.random.default_rng(SEED)
    reps = 20 if args.quick else 200
    collapsed = 0
    for _ in range(reps):
        A = gen.integers(0, 201, size=(100, 200)); b = gen.integers(200, 401, size=100)
        pair_ok = ((A[:, :, None] + A[:, None, :]) <= b[:, None, None]).all(axis=0)
        np.fill_diagonal(pair_ok, ((2 * A) <= b[:, None]).all(axis=0))
        collapsed += not pair_ok.any()
    assert collapsed == reps
    # small size: bound vacuous and collapse genuinely fails
    small_ok = 0
    for _ in range(200):
        A = gen.integers(0, 21, size=(10, 20)); b = gen.integers(20, 41, size=10)
        pair_ok = ((A[:, :, None] + A[:, None, :]) <= b[:, None, None]).all(axis=0)
        small_ok += pair_ok.any()
    return {"formula_checked_n_1_to_40": True, "bound_100x200": float(b_med),
            "bound_10x20": float(bound(10, 20)), "bound_1000x2000": float(bound(1000, 2000)),
            "monte_carlo_100x200_collapsed": f"{collapsed}/{reps}",
            "monte_carlo_10x20_with_multi_item_solution": f"{small_ok}/200"}


# ---------------------------------------------------------------------------
# Mutation tests: deliberately wrong constructions MUST be detected
# ---------------------------------------------------------------------------


@test
def mutation_tests_detect_errors(args, rng):
    caught = {}
    # M1: smooth round-to-nearest (a common soft-rounding surrogate): invalid cuts
    def F_adv(S, d, s):
        p = floor(s)
        return Q(p) + S((s - p - Q(1, 2)) / d + Q(1, 2))
    bad = 0
    for _ in range(300):
        n = rng.randint(1, 3)
        rows = [(tuple(rng.randint(0, 6) for _ in range(n)), rng.randint(1, 12))]
        rows.append((tuple(1 for _ in range(n)), 8))
        pts = integer_points(rows, n)
        u = [rand_rat(rng, 0, 3) for _ in rows]
        d = Q(1, 5)
        col = [F_adv(ramp_linear, d, sum(ui * r[0][j] for ui, r in zip(u, rows))) for j in range(n)]
        rhs = F_adv(ramp_linear, d, sum(ui * r[1] for ui, r in zip(u, rows)))
        bad += any(dot(col, x) > rhs for x in pts)
    caught["M1_round_to_nearest_invalid_cuts_found"] = bad
    assert bad > 0
    # M2: certificate without variable-fixing rows fails coefficient domination
    fails = 0
    for _ in range(3000):
        m, n = 1, rng.randint(2, 5)
        A = [[Q(rng.randrange(41), rng.randint(1, 9)) for _ in range(n)]]
        b = [Q(rng.randrange(31), rng.randint(1, 9))]
        u = [Q(1)]
        t = Q(rng.randrange(1000), 1000)
        a = [A[0][j] for j in range(n)]; B = b[0]
        target = [max(0, floor(v - t)) for v in a]
        N, r = floor(B), B - floor(B)
        if max(0, floor(B - t)) == N or N < 1:
            continue
        lam = (N - (t - r) / 2) / B
        fails += any(floor(lam * v) < g for v, g in zip(a, target))
    caught["M2_no_fixing_rows_domination_failures"] = fails
    assert fails > 0
    # M3: recovery without the (1+eps) rescaling breaks at integer arguments
    mism = sum(F(ramp_linear, Q(1, 10), Q(k)) != k for k in range(1, 20))
    caught["M3_eps0_integer_mismatches"] = mism
    assert mism > 0
    # M4: closure oracle restricted to basis rows disagrees with the grid oracle
    dis = 0
    for _ in range(40):
        rows = canonical(rand_packing(rng, 2, rng.choice([1, 2]), 4, 7))[0]
        Cb, _ = cg_closure(rows, 2, basis_only=True)
        G = grid_closure(rows, 2, 12 if len(rows) == 2 else 30)
        dis += vertices(Cb, 2) != vertices(G, 2)
    caught["M4_basis_only_oracle_disagreements"] = dis
    assert dis > 0
    # M5: a negative network weight produces cuts invalid on integer points
    inval = 0
    for _ in range(400):
        n = 2
        rows = [((rng.randint(1, 5), rng.randint(1, 5)), rng.randint(3, 9)),
                ((rng.randint(0, 5), rng.randint(0, 5)), rng.randint(3, 9))]
        pts = integer_points(rows, n)
        u = [rand_rat(rng, 0, 2), -rand_rat(rng, 0, 2)]
        z = [sum(ui * r[0][j] for ui, r in zip(u, rows)) for j in range(n)]
        zb = sum(ui * r[1] for ui, r in zip(u, rows))
        col = [g_shift(0, v) for v in z]; rhs = g_shift(0, zb)
        inval += any(dot(col, x) > rhs for x in pts)
    caught["M5_negative_weight_invalid_cuts_found"] = inval
    assert inval > 0
    # M6: an oracle that enumerates the parallelepipeds but keeps only points
    # whose packing multiplier has one nonzero entry, so it never aggregates two
    # packing rows. Unlike M4 it keeps nontrivial cuts (asserted below). Random
    # disagreements may also come from single-row cuts that this restricted
    # enumeration happens to miss, so a fixed witness checks that aggregation
    # itself is essential: for y <= 1, 2x + y <= 2 the point (1/2, 1) satisfies
    # every single-row CG cut, but (1/2)(y <= 1) + (1/2)(2x + y <= 2) gives
    # x + y <= 1. Uses its own stream so the draws of M1-M5 are unchanged.
    r6 = random.Random("20261121-mutation-M6-single-row")
    dis = nontriv = full_agree = 0
    for _ in range(60):
        rows = canonical(rand_packing(r6, 2, 2, 4, 7))[0]
        C, _ = cg_closure(rows, 2)
        Cs, _ = cg_closure(rows, 2, single_row=True)
        G = grid_closure(rows, 2, 12 if len(rows) == 2 else 30)
        vs, vg = vertices(Cs, 2), vertices(G, 2)
        full_agree += vertices(C, 2) == vg
        nontriv += vs != vertices(rows, 2)
        dis += vs != vg
    wrows = [((0, 1), 1), ((2, 1), 2)]
    wpt = (Q(1, 2), Q(1))
    single = list(wrows) + [cg_row(wrows, [Q(p, d) if k == i else Q(0) for k in range(2)])
                            for i in range(2) for d in range(1, 61) for p in range(1, d)]
    witness_ok = (contains(single, wpt)
                  and contains(cg_closure(wrows, 2, single_row=True)[0], wpt)
                  and not contains(cg_closure(wrows, 2)[0], wpt)
                  and not contains(grid_closure(wrows, 2, 12), wpt))
    caught["M6_single_row_instances"] = 60
    caught["M6_full_oracle_agrees"] = full_agree
    caught["M6_mutant_nontrivial"] = nontriv
    caught["M6_mutant_disagreements"] = dis
    caught["M6_aggregation_witness_detected"] = witness_ok
    assert full_agree == 60 and nontriv > 0 and dis > 0 and witness_ok
    return caught


# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Revision checks (Gemini review, Nov 2026)
# ---------------------------------------------------------------------------


@test
def thm1_certificate_at_t_equals_one(args, rng):
    """Theorem 3(i) extended to t = 1: same certificate, eta in (0, 1/2]."""
    trials = 2000 if args.quick else 20000
    items = [([[Q(2), Q(3)]], [Q(3)], [Q(1)]), ([[Q(1), Q(5), Q(40)]], [Q(2)], [Q(1)]),
             ([[Q(7, 3), Q(8, 3), Q(0)]], [Q(7, 3)], [Q(1)])]
    for _ in range(trials):
        m, n = rng.randint(1, 3), rng.randint(1, 6)
        A = [[Q(rng.randrange(41), rng.randint(1, 9)) for _ in range(n)] for _ in range(m)]
        b = [Q(rng.randrange(31), rng.randint(1, 9)) for _ in range(m)]
        u = [Q(rng.randrange(21), rng.randint(1, 11)) for _ in range(m)]
        items.append((A, b, u))
    nontrivial = 0
    for A, b, u in items:
        rows, coeff, rhs, target, trhs = certificate(A, b, u, Q(1))
        assert len(rows) <= len(A[0]) + 1
        assert rhs == trhs and all(c >= g for c, g in zip(coeff, target))
        nontrivial += len(rows) > 1 or rows[0][1] != list(u)
    return {"cases": len(items), "rescaled_or_fixed": nontrivial}


def _plateau_data():
    """(ramp, c = max zero point, r0 = first point where S = 1, ell = longest
    interior flat piece), including long plateaus and steep transitions."""
    def long_flat(t):
        return (ramp_linear(100 * t) + ramp_linear(100 * t - 99)) / 2

    def shifted_flat(t):
        return long_flat(2 * t - Q(1, 2))

    return {"linear": (RAMPS["linear"], Q(0), Q(1), Q(0)),
            "smoothstep": (RAMPS["smoothstep"], Q(0), Q(1), Q(0)),
            "smootherstep": (RAMPS["smootherstep"], Q(0), Q(1), Q(0)),
            "early_saturation": (lambda t: ramp_linear(2 * t), Q(0), Q(1, 2), Q(0)),
            "late_start": (lambda t: ramp_linear(2 * t - 1), Q(1, 2), Q(1), Q(0)),
            "long_interior_flat": (long_flat, Q(0), Q(1), Q(49, 50)),
            "shifted_interior_flat": (shifted_flat, Q(1, 4), Q(3, 4), Q(49, 100)),
            "steep_late_start": (lambda t: ramp_linear(500 * t - Q(499, 2)),
                                 Q(499, 1000), Q(501, 1000), Q(0))}


@test
def fixed_width_no_universal_width(args, rng):
    """Proposition S?: for every ramp and width there is P = [0, 2 - eta] whose
    fixed-width closure strictly contains C(P) = [0, 1].  Checks the pointwise
    inequality F(Bu) > F(u) on a fine grid and reports the smallest ratio."""
    step = 200 if args.quick else 800
    out = {}
    for name, (S, c, r0, ell) in _plateau_data().items():
        for d in DELTAS:
            eta = min((r0 - c) * d, 1 - ell, 1 - c * d) / 2
            B = 2 - eta
            assert floor(B) == 1                      # C(P) = [0, 1]
            lo = 1 + c * d
            us = [lo + Q(k, step) for k in range(1, 12 * step)] + \
                 [lo + Q(1, 10 ** e) for e in (3, 6, 9)]
            worst = None
            for u in us:
                fu = F(S, d, u)
                if fu > 0:
                    fbu = F(S, d, B * u)
                    assert fbu > fu, (name, d, u)
                    ratio = fbu / fu
                    worst = ratio if worst is None else min(worst, ratio)
            assert worst > 1
            out[f"{name}/delta={d}"] = f"eta={eta}, min ratio {float(worst):.4f}"
    # A bound using only the final saturation point misses interior plateaus:
    # eta=2/5 satisfies the review's proposed r0-only bound, but gives equality.
    S = _plateau_data()["long_interior_flat"][0]
    u, B = Q(11, 10), Q(8, 5)
    assert F(S, Q(1), u) == F(S, Q(1), B * u) == Q(1, 2)
    return {"cases": len(out), "min_ratio_overall": min(float(v.split()[-1]) for v in out.values()),
            "interior_plateau_counterexample_to_saturation_only_bound": True,
            "examples": dict(list(out.items())[:5])}


def _dramp(name, tau):
    """Exact derivative S'(tau) for the C^1 and C^2 ramps."""
    if tau <= 0 or tau >= 1:
        return Q(0)
    if name == "smoothstep":
        return 6 * tau - 6 * tau * tau
    return 30 * tau ** 4 - 60 * tau ** 3 + 30 * tau ** 2


@test
def recovery_points_have_zero_gradient(args, rng):
    """At the exact-recovery parameters of Theorem 3(ii) every evaluated argument
    lies where F' = 0 (C^1 ramps), and F' != 0 forces F < floor."""
    trials = 2000 if args.quick else 20000
    evals = 0
    for _ in range(trials):
        vals = [rand_rat(rng, 0, 15) for _ in range(rng.randint(1, 8))]
        if rng.random() < 0.5:
            vals += [Q(rng.randint(0, 9))]
        eps, half = recover_parameters(vals)          # half = delta_0 / 2 (or 1)
        delta0 = min(2 * half, Q(1))
        for name in ("smoothstep", "smootherstep"):
            for d in (delta0, delta0 / 2):
                for z in vals:
                    s = (1 + eps) * z
                    slope = Q(0) if s < 1 else _dramp(name, (s - floor(s)) / d) / d
                    width_slope = Q(0) if s < 1 else -(s - floor(s)) * slope / d
                    assert slope == 0, (vals, z, d)
                    assert width_slope == 0 and F(RAMPS[name], d, s) == floor(z)
                    evals += 1
    # Conversely, a nonzero slope occurs only where F is strictly below the floor.
    for name in ("smoothstep", "smootherstep"):
        for d in DELTAS:
            for s in [Q(k, 97) for k in range(97, 97 * 8)]:
                if _dramp(name, (s - floor(s)) / d) != 0:
                    assert F(RAMPS[name], d, s) < floor(s)
    # Endpoint recovery for a merely continuous ramp can have a corner.
    h, s, d = Q(1, 1000), Q(3, 2), Q(1, 2)
    assert F(ramp_linear, d, s) == 1
    assert (F(ramp_linear, d, s) - F(ramp_linear, d, s - h)) / h == 2
    assert (F(ramp_linear, d, s + h) - F(ramp_linear, d, s)) / h == 0
    # Nonzero activation derivatives do not imply a weaker cut at the same u.
    a, b = Q(9, 5), Q(21, 10)
    fa, fb = F(ramp_smoothstep, d, a), F(ramp_smoothstep, d, b)
    assert fa == 1 and fb == Q(138, 125)
    assert _dramp("smoothstep", (b - floor(b)) / d) / d == Q(48, 25)
    assert fb / fa < b / a < Q(floor(b), floor(a))
    return {"evaluations_with_zero_slope": evals,
            "width_derivatives_zero": True,
            "nondifferentiable_endpoint_checked": True,
            "same_multiplier_cut_order_counterexample": True}


@test
def thm2_recovery_higher_rank_instances(args, rng):
    """Theorem 5(ii) on random packing instances that need at least two strict
    CG rounds (C^2 != C^1), replayed with one common width and three ramps."""
    plan = [(2, 9, 20)] * (4 if args.quick else 16) + [(3, 6, 12)] * (1 if args.quick else 4)
    want = len(plan)
    found, tries, neurons = [], 0, 0
    hist = {}
    while len(found) < want and tries < 20000:
        tries += 1
        n, cmax, bmax = plan[len(found)]
        rows = canonical(rand_packing(rng, n, rng.choice([1, 2]), cmax, bmax))[0]
        seq = closure_sequence(rows, n, 4)
        strict = sum(not same_polytope(seq[k][0], seq[k + 1][0], n) for k in range(len(seq) - 1))
        if strict >= 2:
            found.append((rows, n, seq))
            hist[strict] = hist.get(strict, 0) + 1
    assert len(found) == want, (len(found), tries)
    for rows, n, seq in found:
        nn, K, width = simulate_closure_network(rows, n, seq)
        assert 0 < width <= 1
        neurons += nn
    return {"instances_with_rank_at_least_2": len(found), "sampled": tries,
            "strict_rounds_histogram": {str(k): v for k, v in sorted(hist.items())},
            "neurons_simulated_exactly": neurons}


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: this verification suite requires Python assertions.")
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--only")
    args = ap.parse_args()
    RESULTS.mkdir(parents=True, exist_ok=True)
    report = {"seed": SEED, "quick": args.quick, "python": sys.version.split()[0],
              "tests": {},
              "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in (Path(__file__), Path(__file__).resolve().parent.parent / "src" / "exactcg.py")}}
    fails = 0
    for fn in TESTS:
        if args.only and args.only not in fn.__name__:
            continue
        rng = random.Random(f"{SEED}-{fn.__name__}")
        t0 = time.time()
        try:
            res = fn(args, rng)
            status = "PASS"
        except Exception as e:  # noqa: BLE001
            res = {"error": repr(e)[:2000], "trace": traceback.format_exc()[-3000:]}
            status = "FAIL"
            fails += 1
        dt = time.time() - t0
        report["tests"][fn.__name__] = {"status": status, "seconds": round(dt, 2), **res}
        print(f"{status:4}  {dt:7.1f}s  {fn.__name__}", flush=True)
    report["summary"] = {"total": len(report["tests"]), "failed": fails}
    if not report["tests"]:
        ap.error("--only did not match any test")
    suffix = "_quick" if args.quick else ""
    if args.only:
        suffix += "_selected"
    (RESULTS / f"verification_report{suffix}.json").write_text(
        json.dumps(report, indent=2, default=str) + "\n")
    lines = ["# Verification report" + (" (quick)" if args.quick else ""), "",
             f"Seed {SEED}. {len(report['tests'])} tests, {fails} failed.", "",
             "| Test | Status | Seconds | Key numbers |", "|---|---|---:|---|"]
    for k, v in report["tests"].items():
        keys = {a: b for a, b in v.items() if a not in ("status", "seconds", "trace")}
        lines.append(f"| `{k}` | {v['status']} | {v['seconds']} | "
                     f"{json.dumps(keys, default=str)[:500]} |")
    (RESULTS / f"verification_report{suffix}.md").write_text("\n".join(lines) + "\n")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
