"""Exact rational toolkit for the ORL note verification suite.

Everything here uses fractions.Fraction; no floating-point tolerance is involved
unless a function name says `float`.

Conventions
-----------
* A packing system is a list of rows (a, b): a tuple of nonnegative integers and
  an integer b >= 0, meaning a.x <= b, together with x >= 0 (implicit).
* Ramps S: [0,1] -> [0,1] are nondecreasing with S(0)=0, S(1)=1; outside [0,1]
  they are clamped (S=0 below 0, S=1 above 1).
* F_{S,delta}(s) = sum_{q>=1} S((s-q)/delta), for s >= 0 and 0 < delta <= 1.
"""
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations, product
from math import floor, gcd

# --------------------------------------------------------------------------
# Ramps (rational polynomials, so exact arithmetic is possible)
# --------------------------------------------------------------------------


def _clamp(r):
    return Q(0) if r <= 0 else (Q(1) if r >= 1 else r)


def ramp_linear(r):
    return _clamp(r)


def ramp_smoothstep(r):          # C^1
    r = _clamp(r)
    return 3 * r * r - 2 * r ** 3


def ramp_smootherstep(r):        # C^2
    r = _clamp(r)
    return 6 * r ** 5 - 15 * r ** 4 + 10 * r ** 3


RAMPS = {"linear": ramp_linear, "smoothstep": ramp_smoothstep,
         "smootherstep": ramp_smootherstep}


def F_series(S, delta, s):
    """Literal definition: sum over q >= 1 (terms vanish for q >= s)."""
    s = Q(s)
    # Terms with q >= s vanish because S(r) = 0 for r <= 0.
    return sum((S((s - q) / delta) for q in range(1, floor(s) + 2)), Q(0))


def F(S, delta, s):
    """Closed form of the delayed smooth floor (equals F_series)."""
    s = Q(s)
    if s < 1:
        return Q(0)
    p = floor(s)
    return Q(p - 1) + S((s - p) / delta)


def g_shift(t, s):
    """Shifted floor g_t(s) = max{0, floor(s - t)}."""
    return Q(max(0, floor(Q(s) - t)))


# --------------------------------------------------------------------------
# Small linear algebra
# --------------------------------------------------------------------------


def dot(a, b):
    return sum(Q(x) * y for x, y in zip(a, b))


def inverse(mat):
    n = len(mat)
    t = [[Q(x) for x in row] + [Q(int(i == j)) for j in range(n)]
         for i, row in enumerate(mat)]
    for j in range(n):
        piv = next((i for i in range(j, n) if t[i][j]), None)
        if piv is None:
            return None
        t[j], t[piv] = t[piv], t[j]
        v = t[j][j]
        t[j] = [x / v for x in t[j]]
        for i in range(n):
            if i != j and t[i][j]:
                v = t[i][j]
                t[i] = [x - v * y for x, y in zip(t[i], t[j])]
    return [row[n:] for row in t]


def full_system(rows, n):
    """Rows plus nonnegativity written as -x_i <= 0."""
    return list(rows) + [(tuple(-int(i == j) for j in range(n)), 0)
                         for i in range(n)]


def vertices(rows, n):
    """Exact vertex set of {x >= 0 : rows} (bounded, nonempty assumed)."""
    full = full_system(rows, n)
    out = set()
    for inds in combinations(range(len(full)), n):
        basis = [full[i][0] for i in inds]
        inv = inverse(basis)
        if inv is None:
            continue
        rhs = [full[i][1] for i in inds]
        v = tuple(dot(r, rhs) for r in inv)
        if all(dot(a, v) <= b for a, b in full):
            out.add(v)
    return sorted(out)


def contains(rows, x):
    return all(c >= 0 for c in x) and all(dot(a, x) <= b for a, b in rows)


def max_over(rows, n, c):
    return max(dot(c, v) for v in vertices(rows, n))


def same_polytope(r1, r2, n):
    return vertices(r1, n) == vertices(r2, n)


def integer_points(rows, n):
    bounds = []
    for j in range(n):
        cands = [b // a[j] for a, b in rows if a[j] > 0]
        assert cands, "unbounded variable"
        bounds.append(min(cands))
    return [x for x in product(*(range(u + 1) for u in bounds))
            if all(dot(a, x) <= b for a, b in rows)]


# --------------------------------------------------------------------------
# Canonical packing rows with derivation tracking
# --------------------------------------------------------------------------


def canonical(rows, derivs=None):
    """Divide by gcd, keep best RHS per direction, drop dominated rows.

    derivs (optional) is a parallel list; each derivation d is a dict
    {"scale": Fraction, "mult": tuple} meaning row = (cg row of mult) * scale.
    Returns (rows, derivs) with the kept rows' derivations rescaled.
    """
    if derivs is None:
        derivs = [None] * len(rows)
    assert len(rows) == len(derivs), "one derivation is required per row"
    best = {}
    for (a, b), d in zip(rows, derivs):
        assert all(Q(x).denominator == 1 for x in (*a, b)), "nonintegral packing row"
        a = tuple(int(x) for x in a)
        b = int(b)
        assert all(x >= 0 for x in a) and b >= 0
        if not any(a):
            continue
        g = reduce(gcd, (*a, b))
        a2, b2 = tuple(x // g for x in a), b // g
        d2 = None if d is None else dict(d, scale=d["scale"] / g)
        if a2 not in best or b2 < best[a2][0]:
            best[a2] = (b2, d2)
    items = sorted((a, b, d) for a, (b, d) in best.items())
    keep = []
    for a, b, d in items:
        dominated = False
        for c, e, _ in items:
            if (a, b) == (c, e):
                continue
            if e == 0:
                dom = all(x == 0 or y > 0 for x, y in zip(a, c))
            elif b == 0:
                dom = False
            else:
                dom = all(b * y >= e * x for x, y in zip(a, c))
            if dom and (b != e or a < c or any(b * y > e * x for x, y in zip(a, c))):
                dominated = True
                break
        if not dominated:
            keep.append((a, b, d))
    return [(a, b) for a, b, _ in keep], [d for _, _, d in keep]


def cg_row(rows, u):
    """CG row floor(u A) x <= floor(u b) for nonnegative multipliers u."""
    n = len(rows[0][0])
    assert len(u) == len(rows) and all(ui >= 0 for ui in u), "invalid CG multiplier"
    a = tuple(floor(sum(Q(ui) * r[0][j] for ui, r in zip(u, rows))) for j in range(n))
    b = floor(sum(Q(ui) * r[1] for ui, r in zip(u, rows)))
    return a, b


def cg_closure(rows, n, basis_only=False, single_row=False):
    """Complete CG closure of a bounded packing system with integral data.

    Uses fundamental parallelepipeds of feasible vertex bases. For packing data
    the support h may be replaced by h_+; the multiplier on the packing rows of
    the basis gives a valid CG derivation (nonnegativity rows only lower the
    coefficients, and have zero RHS), which is returned for every kept row.
    Completeness: an optimal LP dual for any integral support normal has a
    feasible vertex basis. Split its nonnegative basis multipliers into integer
    and fractional parts. The latter produces an integral normal in the
    half-open fundamental parallelepiped enumerated below. Its rounded cut plus
    integer multiples of the original integral basis rows implies the original
    support cut. Replacing negative support coefficients by zero is legitimate
    for packing sets; discarding nonnegativity-row multipliers only strengthens
    the generated packing cut. This is an algorithmic justification, not a
    conclusion drawn from a finite multiplier-grid cross-check.

    basis_only and single_row are deliberate mutations used only by the
    mutation tests: the first skips the enumeration, the second keeps only
    parallelepiped points whose packing multiplier has at most one nonzero
    entry (no aggregation of packing rows).

    Returns (rows, derivations) where derivation["mult"] is indexed by `rows`.
    """
    assert n > 0 and rows and all(len(a) == n for a, _ in rows)
    assert all(Q(z).denominator == 1 and z >= 0 for a, b in rows for z in (*a, b))
    assert all(any(a[j] > 0 for a, _ in rows) for j in range(n)), "unbounded packing system"
    full = full_system(rows, n)
    m = len(rows)
    gen, der = [], []
    for i, (a, b) in enumerate(rows):
        gen.append((a, b))
        der.append({"scale": Q(1), "mult": tuple(Q(int(k == i)) for k in range(m))})
    for inds in combinations(range(len(full)), n):
        basis = [full[i][0] for i in inds]
        inv = inverse(basis)
        if inv is None:
            continue
        rhs = [full[i][1] for i in inds]
        v = tuple(dot(r, rhs) for r in inv)
        if not all(dot(a, v) <= b for a, b in full):
            continue
        ranges = [range(sum(min(0, a[j]) for a in basis),
                        sum(max(0, a[j]) for a in basis) + 1) for j in range(n)]
        for h in ([] if basis_only else product(*ranges)):
            # lam solves lam^T basis = h, i.e. lam = h^T basis^{-1}.
            lam = [sum(Q(h[k]) * inv[k][i] for k in range(n)) for i in range(n)]
            if not all(0 <= t < 1 for t in lam):
                continue
            mult = [Q(0)] * m
            for coef, idx in zip(lam, inds):
                if idx < m:
                    mult[idx] += coef
            if single_row and sum(1 for t in mult if t) > 1:
                continue
            gen.append(cg_row(rows, mult))
            der.append({"scale": Q(1), "mult": tuple(mult)})
    out_rows, out_der = canonical(gen, der)
    return out_rows, out_der


def closure_sequence(rows, n, kmax):
    """[C^0, C^1, ..., ] rows with derivations, stopping at integrality or kmax."""
    seq = [(canonical(rows)[0], None)]
    for _ in range(kmax):
        prev = seq[-1][0]
        nxt, der = cg_closure(prev, n)
        seq.append((nxt, der))
        if same_polytope(prev, nxt, n):
            break
    return seq


def hull_rank(rows, n, kmax=6):
    seq = closure_sequence(rows, n, kmax)
    pts = integer_points(rows, n)
    for k, (r, _) in enumerate(seq):
        if all(all(int(z) == z for z in v) for v in vertices(r, n)):
            return k, seq
    return None, seq


def grid_closure(rows, n, D):
    """Finite multiplier-grid cross-check, not a complete closure in general.

    The enumeration differs from cg_closure, but shares cg_row, canonical and
    the vertex routines. Use support_closure_2d for a separate arithmetic path.
    """
    fracs = sorted({Q(p, q) for q in range(1, D + 1) for p in range(q)})
    gen = list(rows)
    for u in product(fracs, repeat=len(rows)):
        if any(u):
            a, b = cg_row(rows, u)
            if any(a):
                gen.append((a, b))
    return canonical(gen)[0]


def reference_vertices_2d(rows):
    """Exact 2-D packing vertices by Cramer's rule, without inverse/full_system.

    Keeps all inequalities and does not call canonical or production vertices.
    Requires a nonempty bounded packing system, including zero-RHS faces.
    """
    assert rows and all(len(a) == 2 and min(*a, b) >= 0 for a, b in rows)
    assert all(any(a[j] > 0 for a, _ in rows) for j in (0, 1)), "unbounded system"
    inequalities = [(Q(a[0]), Q(a[1]), Q(b)) for a, b in rows]
    inequalities += [(Q(-1), Q(0), Q(0)), (Q(0), Q(-1), Q(0))]
    result = set()
    for i, (a, b, c) in enumerate(inequalities):
        for d, e, f in inequalities[i + 1:]:
            det = a * e - b * d
            if not det:
                continue
            x, y = (c * e - b * f) / det, (a * f - c * d) / det
            if all(g * x + h * y <= rhs for g, h, rhs in inequalities):
                result.add((x, y))
    assert result, "empty vertex set violates the nonempty bounded premise"
    return sorted(result)


def support_closure_2d(rows):
    """Separate complete 2-D support-normal enumeration for integral packing.

    A feasible basis has two rows. Every nonnegative normal of its fractional
    parallelepiped has coordinate at most the sum of the two largest original
    row coefficients in that coordinate (nonnegativity rows cannot increase
    it). Enumerating this entire box therefore includes a sufficient support
    cut family. Support values use reference_vertices_2d, with no CG multiplier,
    inverse, canonical-row or production-vertex helper. Redundancy is removed
    only after generating all support inequalities, using their actual vertices.
    """
    assert all(Q(z).denominator == 1 for a, b in rows for z in (*a, b))
    original = reference_vertices_2d(rows)
    caps = [sum(sorted((a[j] for a, _ in rows), reverse=True)[:2]) for j in (0, 1)]
    cuts = list(rows)
    for h1 in range(caps[0] + 1):
        for h2 in range(caps[1] + 1):
            if h1 or h2:
                value = max(h1 * x + h2 * y for x, y in original)
                cuts.append(((h1, h2), value.numerator // value.denominator))
    return reference_vertices_2d(cuts)


def general_vertices(rows, n):
    """Vertices of {x : rows} for arbitrary signed integral rows (bounded)."""
    out = set()
    for inds in combinations(range(len(rows)), n):
        basis = [rows[i][0] for i in inds]
        inv = inverse(basis)
        if inv is None:
            continue
        rhs = [rows[i][1] for i in inds]
        v = tuple(dot(r, rhs) for r in inv)
        if all(dot(a, v) <= b for a, b in rows):
            out.add(v)
    return sorted(out)


def general_dedupe(rows):
    best = {}
    for a, b in rows:
        assert all(Q(x).denominator == 1 for x in (*a, b)), "nonintegral signed row"
        a = tuple(int(x) for x in a); b = int(b)
        if not any(a):
            assert b >= 0, "infeasible row"
            continue
        g = reduce(gcd, (*[abs(x) for x in a], abs(b))) or 1
        a2, b2 = tuple(x // g for x in a), b // g if b % g == 0 else b // g
        # floor division keeps validity only if exact; use exact when divisible
        if b % g:
            a2, b2 = a, b
        best[a2] = min(b2, best.get(a2, b2))
    return sorted(best.items())


def general_grid_closure(rows, D):
    """CG closure (grid multipliers in [0,1) with denominators <= D) of a
    general integral system that already includes its bound rows."""
    fracs = sorted({Q(p, q) for q in range(1, D + 1) for p in range(q)})
    gen = list(rows)
    for u in product(fracs, repeat=len(rows)):
        if any(u):
            gen.append(cg_row(rows, u))
    return general_dedupe(gen)
