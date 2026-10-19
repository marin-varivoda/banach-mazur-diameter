/-
The computational part: cells, their polygons and the witness / proof-tree checker,
in core Lean `Rat` arithmetic.  No Mathlib.  Soundness is proved in `BMLean.Sound`.
-/
import Std.Data.HashMap

namespace BMC

abbrev Pt := Rat × Rat

@[inline] def cross (o a b : Pt) : Rat :=
  (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-- rotation by 60° about I = (0,-1), in coordinates (x, y/√3) -/
def rot (p : Pt) : Pt := ((p.1 - 3 * (p.2 + 1)) / 2, (p.1 + p.2 + 1) / 2 - 1)

/-- the point with slopes z = (a, b) over side 0 -/
def qz (z : Pt) : Pt := ((z.2 - z.1) / (z.1 + z.2), 2 * z.1 * z.2 / (z.1 + z.2))

def rotN : Nat → Pt → Pt
  | 0, p => p
  | n + 1, p => rotN n (rot p)

def qk (k : Nat) (z : Pt) : Pt := rotN k (qz z)

def hex : List Pt := [(1, 0), (-1, 0), (-2, -1), (-1, -2), (1, -2), (2, -1)]

def mfun (t : Rat) : Rat := (1 - t) / (1 + 3 * t)

def topA (l : List Pt) : Rat := l.foldl (fun m z => max m z.1) 0
def topB (l : List Pt) : Rat := l.foldl (fun m z => max m z.2) 0

structure Cell where
  ins : Fin 6 → List Pt
  outs : Fin 6 → List Pt

def corners (c : Cell) (k : Fin 6) : List Pt :=
  let am := mfun (topB (c.ins (k + 1)))
  let bm := mfun (topA (c.ins (k - 1)))
  let E := c.outs k
  let A := am :: (E.map (·.1)).filter (fun a => decide (a < am))
  let B := bm :: (E.map (·.2)).filter (fun b => decide (b < bm))
  A.flatMap fun a =>
    (B.filter fun b => E.all fun e => decide (a ≤ e.1) || decide (b ≤ e.2)).map fun b => (a, b)

def gensP (c : Cell) : List Pt :=
  hex ++ (List.finRange 6).flatMap fun k => (c.ins k).map (qk k.val)

def gensO (c : Cell) : List Pt :=
  hex ++ (List.finRange 6).flatMap fun k => (corners c k).map (qk k.val)

def cellValid (c : Cell) : Bool :=
  (List.finRange 6).all fun k =>
    (c.ins k ++ c.outs k).all fun z => decide (0 < z.1) && decide (0 < z.2)

/-! ### untrusted convex hull (Andrew's monotone chain) -/

def push : List Pt → Pt → List Pt
  | b :: tl@(a :: _), p => if cross a b p ≤ 0 then push tl p else p :: b :: tl
  | h, p => p :: h

def half (pts : List Pt) : List Pt := ((pts.foldl push []).drop 1).reverse

def hull (pts : List Pt) : List Pt :=
  let s := pts.mergeSort (fun a b => decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2)))
  half s ++ half s.reverse

/-! ### trusted point-in-triangle and point-in-fan tests -/

def inTri (a b c p : Pt) : Bool :=
  let d := cross a b c
  let x := cross p b c
  let y := cross a p c
  let z := cross a b p
  (decide (0 < d) && decide (0 ≤ x) && decide (0 ≤ y) && decide (0 ≤ z)) ||
  (decide (d < 0) && decide (x ≤ 0) && decide (y ≤ 0) && decide (z ≤ 0))

def inPoly : List Pt → Pt → Bool
  | a :: rest, p => (rest.zip rest.tail).any fun bc => inTri a bc.1 bc.2 p
  | [], _ => false

/-! ### polygons of a cell -/

/-- `gP`, `gO`: generators of the inner and outer polygon; `hP`, `hO`: their (untrusted) hulls.
`ok` checks `hP ⊆ gP` and `gO ⊆ conv hO`, so `conv hP ⊆ conv gP` and `conv gO ⊆ conv hO`. -/
structure Polys where
  gP : List Pt
  hP : List Pt
  gO : List Pt
  hO : List Pt

def Polys.ok (P : Polys) : Bool :=
  (P.hP.all fun x => P.gP.contains x) && (P.gO.all fun x => inPoly P.hO x)

def polys (c : Cell) : Polys :=
  let g := gensP c
  let o := gensO c
  ⟨g, hull g, o, hull o⟩

/-- a fixed polygon (hub): P = O -/
def fixedPolys (g : List Pt) : Polys := let h := hull g; ⟨g, h, g, h⟩

/-! ### witnesses -/

structure Wit where
  m00 : Int
  m01 : Int
  m10 : Int
  m11 : Int
  t0 : Int
  t1 : Int
  s0 : Int
  s1 : Int
  lam : Int
deriving Repr, Inhabited

def den : Nat := 10000000000

@[inline] def rq (n : Int) : Rat := mkRat n den

/-- p ↦ c • M p + (u, v) -/
@[inline] def amap (a b c d : Rat) (l u v : Rat) (p : Pt) : Pt :=
  (l * (a * p.1 + b * p.2) + u, l * (c * p.1 + d * p.2) + v)

def witnessOk (C D : Polys) (w : Wit) : Bool :=
  let a := rq w.m00
  let b := rq w.m01
  let c := rq w.m10
  let d := rq w.m11
  let t0 := rq w.t0
  let t1 := rq w.t1
  let s0 := rq w.s0
  let s1 := rq w.s1
  let l := rq w.lam
  decide (0 < l) && decide (a * d - b * c ≠ 0) &&
    D.hO.all (fun p => inPoly C.hP (amap a b c d 1 t0 t1 p)) &&
    (let big := D.hP.map (amap a b c d l s0 s1)
     C.hO.all fun p => inPoly big p)

/-! ### proof trees -/

inductive Tree where
  | leaf (w : Wit)
  | node (side : Bool) (k : Fin 6) (z : Pt) (tin tout : Tree)
deriving Inhabited

def addIn (c : Cell) (k : Fin 6) (z : Pt) : Cell :=
  { c with ins := fun j => if j = k then z :: c.ins j else c.ins j }

def addOut (c : Cell) (k : Fin 6) (z : Pt) : Cell :=
  { c with outs := fun j => if j = k then z :: c.outs j else c.outs j }

/-- target 11/5: lam / den ≤ 11/5 -/
def lamOk (l : Int) : Bool := decide (5 * l ≤ 11 * (den : Int))

def treeOk : Cell → Cell → Tree → Bool
  | C, D, .leaf w =>
      let PC := polys C
      let PD := polys D
      lamOk w.lam && PC.ok && PD.ok && witnessOk PC PD w
  | C, D, .node side k z tin tout =>
      decide (0 < z.1) && decide (z.1 < 1) && decide (0 < z.2) && decide (z.2 < 1) &&
      (if side then treeOk C (addIn D k z) tin && treeOk C (addOut D k z) tout
       else treeOk (addIn C k z) D tin && treeOk (addOut C k z) D tout)

/-! ### the net, configurations, root cells -/

def net : Fin 6 → Pt
  | 0 => (1/7, 1/7) | 1 => (1/3, 1/7) | 2 => (1/7, 1/3)
  | 3 => (1/2, 1/3) | 4 => (1/3, 1/2) | 5 => (3/5, 3/5)

/-- patches 0, Y, S, T, ST, U, V, UV, X (net indices Y S T U V X = 0..5) -/
def patch : Fin 9 → List (Fin 6)
  | 0 => [] | 1 => [0] | 2 => [0, 1] | 3 => [0, 2] | 4 => [0, 1, 2]
  | 5 => [0, 1, 2, 3] | 6 => [0, 1, 2, 4] | 7 => [0, 1, 2, 3, 4] | 8 => [0, 1, 2, 3, 4, 5]

abbrev Config := Fin 6 → Fin 9

def root (cfg : Config) : Cell where
  ins k := (patch (cfg k)).map net
  outs k := ((List.finRange 6).filter fun i => !(patch (cfg k)).contains i).map net

def admissible (c : Config) : Bool :=
  (List.finRange 6).all fun k => (patch (c k)).all fun i => (patch (c (k + 1))).all fun j =>
    decide ((net i).1 + (net j).2 + 3 * (net i).1 * (net j).2 ≤ 1)

def swapP : Fin 9 → Fin 9
  | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | p => p

/-- the configuration of `rot^[j] (σ^f K)` when K has configuration c -/
def transform (j : Fin 6) (f : Bool) (c : Config) : Config :=
  if f then fun k => swapP (c (j - k)) else fun k => c (k - j)

def cfgOfList (l : List Nat) : Config := fun k => Fin.ofNat 9 (l.getD k.val 0)

def code (c : Config) : Nat := (List.finRange 6).foldl (fun n k => 9 * n + (c k).val) 0

end BMC
