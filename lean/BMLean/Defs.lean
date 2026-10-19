/-
Real-valued counterparts of the checker's objects, normalised bodies, cells, and the basic frame
facts (rotation, reflection, casts).
-/
import BMLean.Sandwich
import BMLean.Check

namespace BM

open Set

/-- a rational point as a point of the plane -/
def toR (p : BMC.Pt) : P2 := ((p.1 : ℝ), (p.2 : ℝ))

/-- the convex hull of a list of rational points -/
def hullR (l : List BMC.Pt) : Set P2 := convexHull ℝ (toR '' {p | p ∈ l})

/-- rotation by 60° about I = (0, -1) -/
noncomputable def rotR (p : P2) : P2 := ((p.1 - 3 * (p.2 + 1)) / 2, (p.1 + p.2 + 1) / 2 - 1)

/-- the reflection in the axis x = 0 (it fixes side 0 and swaps the slopes) -/
def sigR (p : P2) : P2 := (-p.1, p.2)

/-- the point with slopes z = (a, b) over side 0 -/
noncomputable def qzR (z : P2) : P2 := ((z.2 - z.1) / (z.1 + z.2), 2 * z.1 * z.2 / (z.1 + z.2))

/-- the point with slopes z over side k -/
noncomputable def qR (k : ℕ) (z : P2) : P2 := rotR^[k] (qzR z)

/-- B = (-1, 0) and C = (1, 0), the ends of side 0 -/
def ptB : P2 := (-1, 0)
def ptC : P2 := (1, 0)

lemma toR_rot (p : BMC.Pt) : toR (BMC.rot p) = rotR (toR p) := by
  simp only [toR, BMC.rot, rotR]; push_cast; ring_nf

lemma toR_rotN (k : ℕ) (p : BMC.Pt) : toR (BMC.rotN k p) = rotR^[k] (toR p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp only [BMC.rotN, ih, toR_rot, Function.iterate_succ_apply]

lemma toR_qz (z : BMC.Pt) : toR (BMC.qz z) = qzR (toR z) := by
  simp only [toR, BMC.qz, qzR]; push_cast; ring_nf

lemma toR_qk (k : ℕ) (z : BMC.Pt) : toR (BMC.qk k z) = qR k (toR z) := by
  simp only [BMC.qk, qR, toR_rotN, toR_qz]

lemma rotR_iter_six : rotR^[6] = id := by
  funext p; simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, rotR, id]
  ext <;> ring

lemma rotR_iter_mod (n : ℕ) : rotR^[n % 6] = rotR^[n] := by
  conv_rhs => rw [← Nat.mod_add_div n 6]
  rw [Function.iterate_add, Function.iterate_mul, rotR_iter_six, Function.iterate_id]; rfl

noncomputable def rotE : P2 ≃ᵃ[ℝ] P2 := affE (1/2) (-3/2) (1/2) (1/2) (-3/2) (-1/2) (by norm_num)

lemma rotE_coe : ⇑rotE = rotR := by
  funext p; simp only [rotE, affE_apply, rotR]; ext <;> ring

noncomputable def sigE : P2 ≃ᵃ[ℝ] P2 := affE (-1) 0 0 1 0 0 (by norm_num)

lemma sigE_coe : ⇑sigE = sigR := by
  funext p; simp only [sigE, affE_apply, sigR]; ext <;> ring

/-- rotR^[k] as an affine equivalence -/
noncomputable def rotIter : ℕ → P2 ≃ᵃ[ℝ] P2
  | 0 => AffineEquiv.refl ℝ P2
  | k + 1 => rotE.trans (rotIter k)

lemma rotIter_coe (k : ℕ) : ⇑(rotIter k) = rotR^[k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext p
    simp only [rotIter, AffineEquiv.coe_trans, Function.comp_apply, ih, rotE_coe,
      Function.iterate_succ_apply]

lemma rotR_hex {v : P2} (hv : v ∈ hexVerts) : rotR v ∈ hexVerts := by
  simp only [hexVerts, mem_insert_iff, mem_singleton_iff] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rotR, Prod.mk.injEq] <;> norm_num

lemma rotR_iter_hex (k : ℕ) {v : P2} (hv : v ∈ hexVerts) : rotR^[k] v ∈ hexVerts := by
  induction k generalizing v with
  | zero => exact hv
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (rotR_hex hv)

lemma sigR_hex {v : P2} (hv : v ∈ hexVerts) : sigR v ∈ hexVerts := by
  simp only [hexVerts, mem_insert_iff, mem_singleton_iff] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sigR, Prod.mk.injEq] <;> norm_num

/-- K is normalised: a convex body with the six vertices of H₀ on its boundary -/
def Normalized (K : Set P2) : Prop := IsConvexBody K ∧ ∀ v ∈ hexVerts, v ∈ frontier K

/-- K belongs to the cell c -/
def Belongs (K : Set P2) (c : BMC.Cell) : Prop :=
  ∀ k : Fin 6, (∀ z ∈ c.ins k, qR k (toR z) ∈ K) ∧ (∀ z ∈ c.outs k, qR k (toR z) ∉ K)

end BM
