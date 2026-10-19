# The planar Banach–Mazur diameter is at most 11/5

**Theorem.** For all planar convex bodies *K*, *L* (compact, convex, with non-empty interior),

    d_BM(K, L) = inf{ λ ≥ 1 : T(L) ⊆ K ⊆ λ T(L) + b,  T invertible affine,  b ∈ R² }  ≤  11/5.

The previous best bound was (19 − √73)/4 ≈ 2.614 (Brodiuk, Palko and Prymak, 2018). Lassak's conjecture
is 1 + √5/2 ≈ 2.118, the distance from a triangle to a regular pentagon.

The proof is in [`paper/paper.pdf`](paper/paper.pdf). It is computer assisted, and this repository contains
everything needed to check it, in two independent ways. One is an exact checker in Python, below. The other is a
complete formalization in Lean 4 + Mathlib, in [`lean/`](lean). The Lean version includes a proof of
Besicovitch's lemma and has no `sorry`.

## Files

| file | role |
|---|---|
| `proof.py` | the proof: exact geometry (hexagon frame, net, cells) and the checker of the certificate, in exact rational arithmetic |
| `search.py` | finds the certificate (floating point; numpy, numba) |
| `search_result.jsonl.gz` | the certificate found by `search.py` (its format is described at the top of `proof.py`) |
| `paper/` | the paper |
| `lean/` | the Lean 4 + Mathlib proof (`BM.banachMazur_diam_le`); see [`lean/README.md`](lean/README.md) |

The trusted part of the proof is `proof.py` (about 230 lines). It uses only the Python standard library
(3.9 or later). `search.py` only *finds* witnesses, so its correctness does not matter.

## Checking the proof

The certificate is `search_result.jsonl.gz` (22 MB, the output of `search.py`). Run

```bash
python3 proof.py                        # the 1/4-net theorem and the counts of the net (15 s)
python3 proof.py search_result.jsonl.gz 20   # the proof, on 20 cores (under a minute)
```

The checker recomputes the 6,729 root cells, verifies every witness, follows every proof tree (recomputing the
split cells), and checks that every pair of root cells is covered by a hub or by a proof tree. It prints

```
target 11/5: 6729 root cells, 60 hubs, 1339 trees
1. all 403740 hub witnesses are valid
2. all 1339 trees are valid
3. all 22643085 pairs of root cells are covered: 1339 by trees, the others by hubs
VALID: d(K, L) <= 11/5 for all planar convex bodies K, L
```

The certificate format is described at the top of `proof.py`.

## Checking the proof in Lean

```bash
cd lean && lake exe cache get && lake build      # about 2 minutes on 8 cores, after the Mathlib cache
```

## Producing the certificate

```bash
python3 -m venv .venv && .venv/bin/pip install numpy numba
.venv/bin/python search.py 20          # writes search_result.jsonl.gz, using 20 cores (about an hour)
```

The floating-point search may behave slightly differently on another machine, so the certificate need not
be identical to the one in this repository, but it is checked in the same way.

## Building the paper

```bash
cd paper && tectonic paper.tex
```
