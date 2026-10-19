"""Produce the certificate for d(K, L) <= 11/5 (format: proof.py).  Nothing here needs to be correct.

    python3 search.py [workers]        # writes search_result.jsonl.gz

Witnesses.  For polygons P(C), O(C), P(D), O(D) and a linear map M let mu be the largest number
with mu M O(D) + t in P(C), and sigma the largest with sigma O(C) + s in M P(D).  Both are linear
programs in three variables.  Then (mu M, t, 1/(mu sigma), -s/sigma) is a witness of value
1/(mu sigma), which does not change when M is scaled.  We minimise it over the maps
M = W_C^-1 R(theta) [[e^a, b], [0, e^-a]] F W_D, where W puts a polygon in isotropic position and
F = diag(1, +-1): Nelder-Mead from the best 32 of 4096 random (theta, a, b, F).  The witness is
then shrunk/enlarged by a relative 1e-8, rounded to rationals and verified exactly.

Proof trees.  If the witness of a pair is above 11/5, we split one of the two cells at an outer
corner that is active in the witness (on the boundary of the other polygon) and farthest from the
inner polygon, at the slope point halfway between the inner staircase and the corner; recurse.
"""

import gzip
import json
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

import numpy as np
from numba import njit

import proof

TARGET, DEN = Fr(11, 5), 10**10
HUBS = [
    '0-0-0-0-0-0', '0-X-0-X-0-X', 'ST-ST-ST-ST-ST-ST', '0-UV-0-UV-0-UV', '0-0-X-0-0-X', 'Y-Y-X-Y-Y-X',
    '0-0-ST-0-0-ST', '0-T-X-0-X-S', '0-Y-ST-Y-T-UV', '0-V-T-X-S-U', '0-0-U-0-T-U', '0-0-ST-U-S-U',
    'Y-ST-S-ST-Y-U', '0-0-Y-X-Y-X', '0-T-X-S-0-X', '0-Y-V-T-Y-X', '0-0-Y-0-0-X', '0-V-ST-U-0-X',
    'S-T-X-S-T-X', '0-T-U-S-Y-UV', '0-0-Y-X-0-U', '0-U-Y-U-Y-X', '0-T-X-Y-V-U', '0-0-T-U-Y-X',
    '0-0-UV-0-0-UV', '0-0-T-0-U-S', '0-V-U-0-V-U', 'Y-T-U-Y-UV-S', '0-X-Y-V-T-X', '0-0-S-U-0-ST',
    '0-Y-0-Y-0-Y', '0-Y-T-X-S-Y', '0-T-UV-0-T-X', 'Y-T-V-U-Y-X', '0-S-0-X-Y-U', '0-S-T-Y-V-U',
    '0-T-ST-0-T-X', '0-0-ST-0-0-UV', '0-T-ST-T-X-S', '0-0-0-0-T-X', '0-0-0-X-0-X', 'Y-V-U-Y-V-U',
    '0-Y-V-Y-V-U', '0-ST-S-S-Y-U', 'Y-ST-Y-X-Y-X', 'Y-Y-UV-S-T-X', 'S-S-S-T-T-T', 'Y-T-ST-Y-ST-S',
    '0-S-Y-U-Y-UV', '0-V-T-T-Y-X', 'Y-Y-UV-Y-Y-UV', '0-0-0-0-V-U', '0-0-V-0-V-U', 'Y-Y-U-Y-Y-U',
    '0-T-U-0-ST-U', 'Y-T-X-Y-X-S', '0-Y-V-0-Y-V', 'Y-T-X-S-S-U', 'Y-S-Y-UV-Y-T', 'Y-ST-Y-ST-Y-ST',
]  # the hexagon, the triangle-like member, symmetric members and a spread-out sample; any choice is valid
_rng = np.random.default_rng(0)
SAMPLE = np.column_stack([_rng.uniform(0, 2 * np.pi, 4096), _rng.uniform(-0.6, 0.6, (4096, 2)), _rng.choice([-1.0, 1.0], 4096)])


# ---------------------------------------------------------------- the witness search (floating point)

@njit(cache=True)
def largest(X, Y):
    """(mu, t) with mu largest such that mu X + t lies in the convex polygon Y (either orientation, 0 inside Y).

    The linear program  max mu  s.t.  mu g_i + n_i.t <= h_i  over the edges n_i.x <= h_i of Y, with
    g_i = max n_i.X, by the simplex method from the feasible point mu = 0, t = 0 (all h_i > 0).
    """
    m = len(Y)
    turn = (Y[1, 0] - Y[0, 0]) * (Y[2, 1] - Y[1, 1]) - (Y[1, 1] - Y[0, 1]) * (Y[2, 0] - Y[1, 0])
    T = np.zeros((m + 1, m + 6))  # columns: mu, t+ (2), t- (2), slacks (m), right-hand side
    for i in range(m):
        n0, n1 = np.sign(turn) * (Y[(i + 1) % m, 1] - Y[i, 1]), np.sign(turn) * (Y[i, 0] - Y[(i + 1) % m, 0])
        T[i, :5] = np.max(X[:, 0] * n0 + X[:, 1] * n1), n0, n1, -n0, -n1
        T[i, 5 + i], T[i, -1] = 1.0, n0 * Y[i, 0] + n1 * Y[i, 1]
    T[m, 0] = -1.0
    basis = np.arange(5, 5 + m)
    for _ in range(100):
        j = np.argmin(T[m, :-1])
        if T[m, j] > -1e-12:
            break
        i, best = -1, np.inf
        for r in range(m):
            if T[r, j] > 1e-9 and T[r, -1] / T[r, j] < best:
                i, best = r, T[r, -1] / T[r, j]
        if i < 0:
            break
        T[i] /= T[i, j]
        for r in range(m + 1):
            if r != i:
                T[r] -= T[r, j] * T[i]
        basis[i] = j
    x = np.zeros(6)
    x[basis[basis < 5]] = T[:m, -1][basis < 5]
    return x[0], np.array([x[1] - x[3], x[2] - x[4]])


@njit(cache=True)
def the_map(x, WCi, WD):
    c, s, e = np.cos(x[0]), np.sin(x[0]), np.exp(x[1])
    R = np.array([[c, -s], [s, c]])
    return WCi @ R @ np.array([[e, x[2]], [0.0, 1 / e]]) @ np.array([[1.0, 0.0], [0.0, x[3]]]) @ WD


@njit(cache=True)
def value(x, WCi, WD, PC, OC, PD, OD):
    M = the_map(x, WCi, WD)
    mu, sigma = largest(OD @ M.T, PC)[0], largest(OC, PD @ M.T)[0]
    return 1 / (mu * sigma) if mu > 0 and sigma > 0 else np.inf


@njit(cache=True)
def nelder_mead(x, args, iters=300):
    """Local minimum of value(., *args) in (theta, a, b) from x (the sign x[3] stays fixed)."""
    S, f = np.empty((4, 4)), np.empty(4)
    for i in range(4):
        S[i] = x
        S[i, i - 1] += 0.03 * (i > 0)
        f[i] = value(S[i], *args)
    for _ in range(iters):
        o = np.argsort(f)
        S, f = S[o], f[o]
        if np.abs(S[1:, :3] - S[0, :3]).max() < 1e-10:
            break
        c = (S[0] + S[1] + S[2]) / 3
        r = 2 * c - S[3]
        fr = value(r, *args)
        if fr < f[0]:
            e = 3 * c - 2 * S[3]
            fe = value(e, *args)
            S[3], f[3] = (e, fe) if fe < fr else (r, fr)
        elif fr < f[2]:
            S[3], f[3] = r, fr
        else:
            k = (c + S[3]) / 2
            fk = value(k, *args)
            if fk < f[3]:
                S[3], f[3] = k, fk
            else:
                for i in range(1, 4):
                    S[i] = (S[0] + S[i]) / 2
                    f[i] = value(S[i], *args)
    return S[np.argmin(f)], f.min()


@njit(cache=True)
def best_map(args):
    vals = np.array([value(x, *args) for x in SAMPLE])
    best, fbest = SAMPLE[0], np.inf
    for k in np.argsort(vals)[:32]:
        x, fx = nelder_mead(SAMPLE[k].copy(), args)
        if fx < fbest:
            best, fbest = x, fx
    return the_map(best, args[0], args[1])


def floats(P):
    """Float coordinates relative to the centre I = (0, -1) of H, which is inside every polygon."""
    return np.array([[float(x), float(y) + 1] for x, y in P])


def isotropic(P):
    w, V = np.linalg.eigh(np.cov(P.T))
    return V @ np.diag(w ** -0.5) @ V.T


def witness(C, D):
    """A rational witness for polygon pairs C = (P(C), O(C)), D = (P(D), O(D)), with float data.

    Returns (w, lam, inner, outer): inner(y) = mu M y + t and outer = lam mu M P(D) + s (a polygon).
    """
    PC, OC, PD, OD = map(floats, C + D)
    M = best_map((np.linalg.inv(isotropic(PC)), isotropic(PD), PC, OC, PD, OD))
    mu, t = largest(OD @ M.T, PC)
    sigma, s = largest(OC, PD @ M.T)
    M, lam, s, I = mu * M, 1 / (mu * sigma), -s / sigma, np.array([0.0, -1.0])
    for eps in (1e-8, 1e-6):  # shrink the inner and enlarge the outer copy about the image of I
        A, lam1 = (1 - eps) * M, lam * (1 + eps) / (1 - eps)  # back to the coordinates of proof.py:
        w = [round(DEN * v) for v in (*A.ravel(), *(t + I - A @ I), *(s + I - lam1 * A @ I))]
        w.append(int(np.ceil(DEN * lam1)))
        if proof.witness_ok(C, D, w, DEN):
            outer = lam * PD @ M.T + s
            return w, lam, lambda y: y @ M.T + t, outer if np.linalg.det(M) > 0 else outer[::-1]
    return None, np.inf, None, None


# ---------------------------------------------------------------- proof trees

def depth(points, poly):
    """Distance of each point from the boundary of the convex counter-clockwise polygon (negative outside)."""
    e = np.roll(poly, -1, 0) - poly
    n = np.column_stack([-e[:, 1], e[:, 0]]) / np.linalg.norm(e, axis=1)[:, None]
    return ((points[:, None, :] - poly[None]) * n[None]).sum(2).min(1)


def candidates(cell, test):
    """(gap, k, corner, active) for the outer corners of a cell: gap is the distance of the corner from the
    inner polygon, and test(points) says whether it is active in the witness."""
    P = floats(proof.polygons(cell)[0])
    out = []
    for k in range(6):
        for c in proof.corners(cell, k):
            p = floats([proof.q(c, k)])
            out.append((-depth(p, P)[0], k, c, test(p)[0]))
    return out


def split_point(cell, k, c):
    """The slope point halfway between the inner staircase of side k and the corner c, on the ray to c."""
    tau = max([Fr(0)] + [min(Fr(1), z[0] / c[0], z[1] / c[1]) for z in cell[0][k]])
    t = (1 + tau) / 2
    z = (Fr(t * c[0]).limit_denominator(1000), Fr(t * c[1]).limit_denominator(1000))
    return z if 0 < z[0] < c[0] and 0 < z[1] < c[1] else (t * c[0], t * c[1])  # rounding keeps z below c


def prove(C, D, level=0):
    """A proof tree for the pair of cells (C, D) (format: proof.py)."""
    PC, PD = proof.polygons(C), proof.polygons(D)
    w, lam, inner, outer = witness(PC, PD)
    if w is not None and Fr(w[-1], DEN) <= TARGET:
        return w
    assert level < 60, "proof tree too deep"
    cands = []
    if w is not None:  # corners of O(C) on the boundary of the outer copy, of O(D) mapped onto the boundary of P(C)
        cands += [(g, 0, k, c, a) for g, k, c, a in candidates(C, lambda p: depth(p, outer) < 1e-7)]
        cands += [(g, 1, k, c, a) for g, k, c, a in candidates(D, lambda p: depth(inner(p), floats(PC[0])) < 1e-7)]
    else:
        cands += [(g, side, k, c, False) for side, X in enumerate((C, D)) for g, k, c, _ in candidates(X, lambda p: [0])]
    g, side, k, c, _ = max(cands, key=lambda x: (x[4] and x[0] > 1e-6, x[0]))  # active first, then farthest
    assert g > 1e-6, "no corner to split"
    z = split_point((C, D)[side], k, c)
    kids = proof.split((C, D)[side], k, z)
    subs = [prove(kid, D, level + 1) if side == 0 else prove(C, kid, level + 1) for kid in kids]
    return [side, k, str(z[0]), str(z[1]), *subs]


# ---------------------------------------------------------------- the certificate

ROOTS = [proof.root(c) for c in proof.configurations()]
HUB_POLYS = [proof.polygons(proof.root(tuple(s.split("-"))))[0] for s in HUBS]


def hub_row(i):
    ws = [witness(proof.polygons(ROOTS[i]), (Q, Q))[0] for Q in HUB_POLYS]
    assert None not in ws, f"no hub witness for root cell {i}"
    return ws


def tree(pair):
    i, j = pair
    return [i, j, prove(ROOTS[i], ROOTS[j])]


def main(workers=12):
    with gzip.open("search_result.jsonl.gz", "wt") as f, Pool(workers) as pool:
        f.write(json.dumps({"target": [TARGET.numerator, TARGET.denominator], "den": DEN, "hubs": HUBS}) + "\n")
        rows = []
        for i, ws in enumerate(pool.imap(hub_row, range(len(ROOTS)), 8)):
            rows.append(ws)
            f.write(json.dumps(ws) + "\n")
            print(f"hub witnesses: {i + 1}/{len(ROOTS)}", end="\r", flush=True)
        pairs = proof.uncovered(rows, TARGET, DEN)
        print(f"\n{len(pairs)} pairs of root cells are not covered by hubs")
        for n, line in enumerate(pool.imap_unordered(tree, pairs)):
            f.write(json.dumps(line, separators=(",", ":")) + "\n")
            print(f"trees: {n + 1}/{len(pairs)}", end="\r", flush=True)
    print("\ndone: search_result.jsonl.gz")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
