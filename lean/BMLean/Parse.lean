/-
Untrusted parsers for the certificate data (string literals in `BMLean/Data`).
Nothing about them is proved: the checks are stated about whatever they return.
-/
import BMLean.Check

namespace BMC

def isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9

partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if isWs b[i] then skipWs b (i + 1) else i) else i

partial def readNatAux (b : ByteArray) (i : Nat) (acc : Nat) : Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if 48 ≤ c && c ≤ 57 then readNatAux b (i + 1) (10 * acc + (c - 48).toNat) else (acc, i)
  else (acc, i)

def readInt (b : ByteArray) (i : Nat) : Int × Nat :=
  let i := skipWs b i
  if h : i < b.size then
    if b[i] == 45 then
      let (n, j) := readNatAux b (i + 1) 0
      (-(n : Int), j)
    else
      let (n, j) := readNatAux b i 0
      ((n : Int), j)
  else (0, i)

def readChar (b : ByteArray) (i : Nat) : UInt8 × Nat :=
  let i := skipWs b i
  if h : i < b.size then (b[i], i + 1) else (0, i)

def readWit (b : ByteArray) (i : Nat) : Wit × Nat :=
  let (a, i) := readInt b i
  let (bb, i) := readInt b i
  let (c, i) := readInt b i
  let (d, i) := readInt b i
  let (t0, i) := readInt b i
  let (t1, i) := readInt b i
  let (s0, i) := readInt b i
  let (s1, i) := readInt b i
  let (l, i) := readInt b i
  (⟨a, bb, c, d, t0, t1, s0, s1, l⟩, i)

partial def readWits (b : ByteArray) (i : Nat) (k : Nat) (acc : Array Wit) : Array Wit × Nat :=
  if k = 0 then (acc, i) else
    let (w, i) := readWit b i
    readWits b i (k - 1) (acc.push w)

structure Row where
  idx : Nat
  wits : List Wit
deriving Inhabited

partial def readRows (b : ByteArray) (i : Nat) (acc : Array Row) : Array Row :=
  let i := skipWs b i
  if i < b.size then
    let (n, i) := readInt b i
    let (ws, i) := readWits b i 60 #[]
    readRows b i (acc.push ⟨n.toNat, ws.toList⟩)
  else acc

def parseRows (s : String) : List Row := (readRows s.toUTF8 0 #[]).toList

partial def readTree (b : ByteArray) (i : Nat) : Tree × Nat :=
  let (c, i) := readChar b i
  if c == 76 then -- 'L'
    let (w, i) := readWit b i
    (.leaf w, i)
  else
    let (side, i) := readInt b i
    let (k, i) := readInt b i
    let (an, i) := readInt b i
    let (ad, i) := readInt b i
    let (bn, i) := readInt b i
    let (bd, i) := readInt b i
    let (t1, i) := readTree b i
    let (t2, i) := readTree b i
    (.node (side == 1) (Fin.ofNat 6 k.toNat) (mkRat an ad.toNat, mkRat bn bd.toNat) t1 t2, i)

structure TreeRec where
  i : Nat
  j : Nat
  tree : Tree
deriving Inhabited

partial def readTrees (b : ByteArray) (i : Nat) (acc : Array TreeRec) : Array TreeRec :=
  let i := skipWs b i
  if i < b.size then
    let (_, i) := readChar b i -- 'T'
    let (a, i) := readInt b i
    let (c, i) := readInt b i
    let (t, i) := readTree b i
    readTrees b i (acc.push ⟨a.toNat, c.toNat, t⟩)
  else acc

def parseTrees (s : String) : List TreeRec := (readTrees s.toUTF8 0 #[]).toList

partial def readDigits (b : ByteArray) (i : Nat) (l : Array Nat) : Array Nat × Nat :=
  if h : i < b.size then
    if isWs b[i] then (l, i) else readDigits b (i + 1) (l.push (b[i] - 48).toNat)
  else (l, i)

partial def readCfgs (b : ByteArray) (i : Nat) (acc : Array (List Nat)) : Array (List Nat) :=
  let i := skipWs b i
  if i < b.size then
    let (l, i) := readDigits b i #[]
    readCfgs b i (acc.push l.toList)
  else acc

def parseCfgs (s : String) : List (List Nat) := (readCfgs s.toUTF8 0 #[]).toList

end BMC
