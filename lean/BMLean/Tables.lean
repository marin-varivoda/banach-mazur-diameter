/-
The fixed tables (root configurations, hubs) and the chunk checks run by `native_decide`.
-/
import BMLean.Parse
import BMLean.Data.Reps

namespace BMC

def reps : Array Config := ((parseCfgs BMD.repsStr).map cfgOfList).toArray

def hubCfgs : List Config := (parseCfgs BMD.hubsStr).map cfgOfList

def hubGens (c : Config) : List Pt := gensP (root c)

def hubPolys : List Polys := hubCfgs.map fun c => fixedPolys (hubGens c)

def rootCell (i : Nat) : Cell := root reps[i]!

def rowOk (hp : List Polys) (r : Row) : Bool :=
  let C := polys (rootCell r.idx)
  decide (r.idx < reps.size) && decide (r.wits.length = hp.length) && C.ok &&
    (hp.zip r.wits).all fun (D, w) => D.ok && witnessOk C D w

def hubChunkOk (rows : List Row) : Bool := rows.all (rowOk hubPolys)

def treeRecOk (t : TreeRec) : Bool :=
  decide (t.i < reps.size) && decide (t.j < reps.size) && treeOk (rootCell t.i) (rootCell t.j) t.tree

def treeChunkOk (ts : List TreeRec) : Bool := ts.all treeRecOk

def hubCov (tab : Array Row) (i j : Nat) : Bool :=
  (tab[i]!.wits.zip tab[j]!.wits).any fun (w1, w2) =>
    decide (5 * (w1.lam * w2.lam) ≤ 11 * ((den : Int) * den))

/-- every pair i ≤ j of root cells is covered by a hub or by a tree -/
def coverOk (rows : List Row) (trees : List TreeRec) : Bool :=
  let tab := rows.toArray
  let n := reps.size
  let pairs := trees.map fun t => (t.i, t.j)
  decide (tab.size = n) && (rows.zipIdx.all fun (r, p) => decide (r.idx = p)) &&
  (List.range n).all fun i => (List.range' i (n - i)).all fun j => hubCov tab i j || pairs.contains (i, j)

/-! ### root configurations: every admissible configuration is a symmetric image of a representative -/

def allConfigs : List Config :=
  (List.range 531441).map fun n => fun k => Fin.ofNat 9 (n / 9 ^ (5 - k.val) % 9)

def repIndex : Std.HashMap Nat Nat :=
  (reps.toList.zipIdx.map fun (c, i) => (code c, i)).foldl (fun m (a, b) => m.insert a b) {}

def isRepImage (c : Config) : Bool :=
  (List.finRange 6).any fun j => [false, true].any fun f =>
    let d := transform j f c
    match repIndex.get? (code d) with
    | some i => decide (i < reps.size) && (List.finRange 6).all fun k => decide (reps[i]! k = d k)
    | none => false

def rootsOk : Bool := allConfigs.all fun c => !admissible c || isRepImage c

end BMC
