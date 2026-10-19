/-
The statement: convex bodies, the hexagon H₀ and the Besicovitch hypothesis.

Coordinates are the paper's coordinates (x, y/√3): in them the regular hexagon of the paper is
H₀ = conv{(±1, 0), (±2, -1), (±1, -2)}, an affine-regular hexagon of ℝ².
-/
import Mathlib

namespace BM

open Set

/-- the plane -/
abbrev P2 := ℝ × ℝ

/-- a convex body: compact, convex, with non-empty interior -/
def IsConvexBody (K : Set P2) : Prop := IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- the six vertices of the hexagon H₀ -/
def hexVerts : Set P2 := {(1, 0), (-1, 0), (-2, -1), (-1, -2), (1, -2), (2, -1)}

/-- the affine-regular hexagon H₀ -/
def H0 : Set P2 := convexHull ℝ hexVerts

/-- **Besicovitch's lemma** (assumed, not proved): every planar convex body has an inscribed
affine-regular hexagon, i.e. an affine image of H₀ contained in K whose six vertices lie on the
boundary of K. -/
def Besicovitch : Prop :=
  ∀ K : Set P2, IsConvexBody K → ∃ A : P2 ≃ᵃ[ℝ] P2, A '' H0 ⊆ K ∧ ∀ v ∈ hexVerts, A v ∈ frontier K

/-- `Sandwich K L λ`: some affine image T(L) satisfies T(L) ⊆ K ⊆ λ T(L) + b, i.e. d_BM(K, L) ≤ λ. -/
def Sandwich (K L : Set P2) (lam : ℝ) : Prop :=
  ∃ (T : P2 ≃ᵃ[ℝ] P2) (b : P2), T '' L ⊆ K ∧ K ⊆ (fun x ↦ lam • x + b) '' (T '' L)

end BM
