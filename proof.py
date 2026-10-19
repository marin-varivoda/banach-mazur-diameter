"""The proof of d(K, L) <= 11/5: exact geometry (paper, Sections 2-4) and checker (Section 5).

    python3 proof.py                       the covering theorem (3.2) and the counts of the net (3.1)
    python3 proof.py search_result.jsonl.gz [workers]   the certificate

Coordinates (x, y/sqrt3).  H is the regular hexagon with vertices (+-1, 0), (+-2, -1), (+-1, -2)
and centre I = (0, -1).  Side 0 is BC with B = (-1, 0), C = (1, 0); side k is side 0 rotated by
60k degrees about I.  A point over side 0 is given by its slopes (a, b) = (y/(1+x), y/(1-x)).

Standard library only, exact rational arithmetic.  The certificate is untrusted.  It is
a gzipped file of JSON lines:

    {"target": [11, 5], "den": den, "hubs": [configuration names]}
    one line per root cell (in the order of configurations()): its witnesses against the hubs
    [i, j, tree] for some pairs of root cells i <= j

A witness for a pair of cells (C, D) is a list [m00, m01, m10, m11, t0, t1, s0, s1, lam] of
integers, each meaning w / den.  It claims

    M O(D) + t  in  P(C)   and   O(C)  in  lam M P(D) + s,

which gives d(K, L) <= lam for all bodies K of C and L of D (Proposition 5.1).  A hub is the
fixed polygon Q = P(D) = O(D) of a root cell D.  A tree for (C, D) is a witness with lam <= target,
or [side, k, "a", "b", tree_in, tree_out]: split C (side 0) or D (side 1) on the slope point
(a, b) over side k of H, and give trees for both resulting pairs.  Every pair of root cells
must be covered by a hub (e(i, h) e(j, h) <= target) or by a tree (Lemma 5.2).
"""

import gzip
import json
import sys
from fractions import Fraction as Fr
from functools import cache, lru_cache
from itertools import product
from multiprocessing import Pool

HEX = [(Fr(x), Fr(y)) for x, y in [(1, 0), (-1, 0), (-2, -1), (-1, -2), (1, -2), (2, -1)]]
NET = {"Y": (Fr(1, 7), Fr(1, 7)), "S": (Fr(1, 3), Fr(1, 7)), "T": (Fr(1, 7), Fr(1, 3)),
       "U": (Fr(1, 2), Fr(1, 3)), "V": (Fr(1, 3), Fr(1, 2)), "X": (Fr(3, 5), Fr(3, 5))}
PATCH = {"0": "", "Y": "Y", "S": "YS", "T": "YT", "ST": "YST", "U": "YSTU", "V": "YSTV", "UV": "YSTUV", "X": "YSTUVX"}
MIRROR = {"S": "T", "T": "S", "U": "V", "V": "U"}  # a reflection of H swaps the slopes a and b


def q(z, k=0):
    """The point with slopes z = (a, b) over side k."""
    a, b = z
    x, y = (b - a) / (a + b), 2 * a * b / (a + b) + 1  # relative to I
    for _ in range(k):
        x, y = (x - 3 * y) / 2, (x + y) / 2  # rotation by 60 degrees
    return x, y - 1


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull(points):
    """Convex hull, counter-clockwise (Andrew's monotone chain)."""
    def half(pts):
        h = []
        for p in pts:
            while len(h) >= 2 and cross(h[-2], h[-1], p) <= 0:
                h.pop()
            h.append(p)
        return h[:-1]
    pts = sorted(set(points))
    return half(pts) + half(pts[::-1])


def inside(poly, p):
    """Is p in the convex polygon poly (vertices in either orientation)?"""
    s = [cross(poly[i - 1], poly[i], p) for i in range(len(poly))]
    return min(s) >= 0 or max(s) <= 0


def top(points, i):
    """The largest a-slope (i = 0) or b-slope (i = 1) of a set of slope points; 0 if it is empty."""
    return max((z[i] for z in points), default=Fr(0))


def m(t):
    """Lemma 2.3: next to a point with b-slope t over side k+1, the a-slopes over side k are at most m(t)
    (and next to a point with a-slope t over side k-1, the b-slopes over side k are at most m(t))."""
    return (1 - t) / (1 + 3 * t)


# ---------------------------------------------------------------- configurations and cells

def admissible(c):
    pts = [[NET[g] for g in PATCH[p]] for p in c]
    return all(top(pts[k], 0) <= m(top(pts[(k + 1) % 6], 1)) for k in range(6))


@cache
def configurations():
    """Representatives of the admissible configurations modulo the symmetries of H."""
    def images(c):
        for r in range(6):
            d = c[r:] + c[:r]
            yield d
            yield tuple(MIRROR.get(p, p) for p in d[:1] + d[:0:-1])
    return sorted({min(images(c)) for c in product(PATCH, repeat=6) if admissible(c)})


def root(c):
    """The root cell of a configuration c: inside are the net points of its patches, outside the others."""
    return (tuple(tuple(NET[g] for g in PATCH[p]) for p in c),
            tuple(tuple(z for g, z in NET.items() if g not in PATCH[p]) for p in c))


def split(cell, k, z):
    """The two children of a cell: the slope point z over side k is inside, resp. outside, the body."""
    ins, outs = cell
    add = lambda sets: sets[:k] + (sets[k] + (z,),) + sets[k + 1:]  # noqa: E731
    return (add(ins), outs), (ins, add(outs))


def corners(cell, k):
    """The corners of the staircase S_k (Definition 4.1), and some points below them."""
    ins, outs = cell
    am, bm = m(top(ins[(k + 1) % 6], 1)), m(top(ins[k - 1], 0))
    A = {am} | {a for a, b in outs[k] if a < am}
    B = {bm} | {b for a, b in outs[k] if b < bm}
    return [(a, b) for a in A for b in B if all(a <= ae or b <= be for ae, be in outs[k])]


@lru_cache(maxsize=4096)
def polygons(cell):
    """The inner polygon P and the outer polygon O of a cell (Definition 4.1)."""
    P = HEX + [q(z, k) for k in range(6) for z in cell[0][k]]
    O = HEX + [q(c, k) for k in range(6) for c in corners(cell, k)]
    return hull(P), hull(O)


# ---------------------------------------------------------------- the 1/4-net

def covering_check():
    """Theorem 3.2: F(q) is in conv(H, net points dominated by q) for every q over side 0, F = I + 4/5 (. - I).

    On each of 25 rectangles of slopes the dominated net points are fixed, and the points with these
    slopes form the quadrilateral with corners q(a, b), a in {a0, a1}, b in {b0, b1}; a corner with a
    zero slope is B or C, which F maps into H.
    """
    F = lambda p: (4 * p[0] / 5, (4 * p[1] - 1) / 5)  # noqa: E731
    cuts = [Fr(0), Fr(1, 7), Fr(1, 3), Fr(1, 2), Fr(3, 5), Fr(1)]
    for (a0, a1), (b0, b1) in product(zip(cuts, cuts[1:]), repeat=2):
        target = hull(HEX + [q(z) for z in NET.values() if z[0] <= a0 and z[1] <= b0])
        assert all(inside(target, F(q((a, b)))) for a in (a0, a1) for b in (b0, b1) if a * b > 0)



def require(ok, msg):
    if not ok:
        sys.exit(f"NOT VALID: {msg}")


def witness_ok(C, D, w, den):
    """C = (P(C), O(C)) and D = (P(D), O(D)) are polygons."""
    m00, m01, m10, m11, t0, t1, s0, s1, lam = (Fr(v, den) for v in w)
    f = lambda p, c, u, v: (c * (m00 * p[0] + m01 * p[1]) + u, c * (m10 * p[0] + m11 * p[1]) + v)  # noqa: E731
    big = [f(p, lam, s0, s1) for p in D[0]]  # lam M P(D) + s, a convex polygon as M is invertible
    return (lam > 0 and m00 * m11 != m01 * m10 and all(inside(C[0], f(p, 1, t0, t1)) for p in D[1])
            and all(inside(big, p) for p in C[1]))


def tree_ok(C, D, t, target, den):
    """Does the tree t prove d(K, L) <= target for all bodies K of the cell C and L of the cell D?"""
    if isinstance(t[-1], int):
        return Fr(t[-1], den) <= target and witness_ok(polygons(C), polygons(D), t, den)
    side, k, a, b, t_in, t_out = t
    z = (Fr(a), Fr(b))
    if side not in (0, 1) or k not in range(6) or not (0 < z[0] < 1 and 0 < z[1] < 1):
        return False
    pairs = [(c, D) for c in split(C, k, z)] if side == 0 else [(C, d) for d in split(D, k, z)]
    return all(tree_ok(*pair, sub, target, den) for pair, sub in zip(pairs, (t_in, t_out)))


def hubs_ok(job):
    cell, hubs, ws, den = job
    return all(witness_ok(polygons(cell), (Q, Q), w, den) for Q, w in zip(hubs, ws))


def pair_ok(job):
    return tree_ok(*job)


def uncovered(rows, target, den):
    """The pairs i <= j of root cells with e(i, h) e(j, h) > target for every hub h (rows[i][h][-1] = den e(i, h))."""
    out = []
    for i in range(len(rows)):
        rest = range(i, len(rows))
        for h in range(len(rows[i])):
            rest = [j for j in rest if rows[i][h][-1] * rows[j][h][-1] * target.denominator > target.numerator * den**2]
        out += [(i, j) for j in rest]
    return out


def main(path, workers=12):
    roots = [root(c) for c in configurations()]
    n = len(roots)
    with gzip.open(path, "rt") as f:
        head = json.loads(next(f))
        rows = [json.loads(next(f)) for _ in range(n)]
        trees = {(i, j): t for i, j, t in map(json.loads, f)}
    target, den = Fr(*head["target"]), head["den"]
    hubs = [polygons(root(tuple(s.split("-"))))[0] for s in head["hubs"]]
    print(f"target {target}: {n} root cells, {len(hubs)} hubs, {len(trees)} trees")

    with Pool(workers) as pool:
        require(all(len(ws) == len(hubs) for ws in rows), "missing hub witnesses")
        require(all(pool.imap(hubs_ok, [(c, hubs, ws, den) for c, ws in zip(roots, rows)], 16)), "bad hub witness")
        print(f"1. all {n * len(hubs)} hub witnesses are valid")
        jobs = [(roots[i], roots[j], t, target, den) for (i, j), t in trees.items()]
        require(all(pool.imap(pair_ok, jobs)), "bad tree")
        print(f"2. all {len(trees)} trees are valid")

    rest = uncovered(rows, target, den)
    require(all(p in trees for p in rest), "a pair of root cells is not covered")
    print(f"3. all {n * (n + 1) // 2} pairs of root cells are covered: {len(rest)} by trees, the others by hubs")
    print(f"VALID: d(K, L) <= {target} for all planar convex bodies K, L")


if __name__ == "__main__":
    if len(sys.argv) == 1:
        covering_check()
        print("covering theorem: verified on all 25 rectangles")
        n = sum(map(admissible, product(PATCH, repeat=6)))
        print(f"{n} admissible configurations, {len(configurations())} up to symmetry")
    else:
        main(sys.argv[1], *map(int, sys.argv[2:]))
