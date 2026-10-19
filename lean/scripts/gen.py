"""Generate Lean data files from search_result.jsonl.gz.  usage: gen.py search_result.jsonl.gz outdir rows_per_chunk tree_chunks [limit_rows]"""
import gzip, json, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
import proof as net
from fractions import Fraction as Fr
NAME = {"0":0,"Y":1,"S":2,"T":3,"ST":4,"U":5,"V":6,"UV":7,"X":8}
path, out, per, ntc = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
limit = int(sys.argv[5]) if len(sys.argv) > 5 else None
os.makedirs(out, exist_ok=True)
confs = net.configurations()
n = len(confs)
f = gzip.open(path, 'rt')
head = json.loads(next(f)); rows = [json.loads(next(f)) for _ in range(n)]
trees = [json.loads(l) for l in f]
assert head["den"] == 10**10 and head["target"] == [11, 5]
def lit(s):  # Lean string literal, data has no special chars
    return '"' + s + '"'
def wrap(s, w=4000):
    return "\\\n".join(s[i:i+w] for i in range(0, len(s), w))  # Lean: backslash-newline continues string? check
reps = " ".join("".join(str(NAME[p]) for p in c) for c in confs)
hubs = " ".join("".join(str(NAME[p]) for p in s.split("-")) for s in head["hubs"])
with open(f"{out}/Reps.lean", "w") as g:
    g.write("namespace BMD\n\n")
    g.write(f"def repsStr : String := {lit(reps)}\n\n")
    g.write(f"def hubsStr : String := {lit(hubs)}\n\nend BMD\n")
nr = n if limit is None else limit
chunks = [list(range(s, min(s + per, nr))) for s in range(0, nr, per)]
for c, idx in enumerate(chunks):
    s = "\n".join(" ".join([str(i)] + [str(v) for w in rows[i] for v in w]) for i in idx)
    with open(f"{out}/Hub{c:03d}.lean", "w") as g:
        g.write(f"namespace BMD\n\ndef hub{c:03d} : String := {lit(s)}\n\nend BMD\n")
def enc(t, acc):
    if isinstance(t[-1], int):
        acc.append("L " + " ".join(map(str, t)))
    else:
        side, k, a, b, ti, to = t
        a, b = Fr(a), Fr(b)
        acc.append(f"N {side} {k} {a.numerator} {a.denominator} {b.numerator} {b.denominator}")
        enc(ti, acc); enc(to, acc)
def leaves(t):
    return 1 if isinstance(t[-1], int) else leaves(t[4]) + leaves(t[5])
trees.sort(key=lambda t: (t[0], t[1]))
tot = sum(leaves(t[2]) for t in trees)
tc, cur, acc = [], 0, []
for t in trees:
    acc.append(t); cur += leaves(t[2])
    if cur >= tot / ntc and len(tc) < ntc - 1:
        tc.append(acc); acc, cur = [], 0
tc.append(acc)
for c, ts in enumerate(tc):
    parts = []
    for i, j, t in ts:
        a = [f"T {i} {j}"]; enc(t, a); parts.append(" ".join(a))
    with open(f"{out}/Tree{c:03d}.lean", "w") as g:
        g.write(f"namespace BMD\n\ndef tree{c:03d} : String := {lit(chr(10).join(parts))}\n\nend BMD\n")
print(n, len(chunks), len(tc), [sum(leaves(t[2]) for t in ts) for ts in tc][:5])
