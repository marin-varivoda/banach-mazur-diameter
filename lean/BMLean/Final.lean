/-
The unconditional theorem: Besicovitch's lemma (`BMLean/Besicovitch.lean`) discharges the hypothesis
of `BM.diam_le` (`BMLean/Main.lean`).
-/
import BMLean.Main
import BMLean.Besicovitch

namespace BM

/-- **The planar Banach–Mazur diameter is at most 11/5**: for all planar convex bodies `K`, `L` there
is an affine image `T(L)` with `T(L) ⊆ K ⊆ (11/5)·T(L) + b`, i.e. `d_BM(K, L) ≤ 11/5`. -/
theorem banachMazur_diam_le (K L : Set P2) (hK : IsConvexBody K) (hL : IsConvexBody L) :
    ∃ (T : P2 ≃ᵃ[ℝ] P2) (b : P2), T '' L ⊆ K ∧ K ⊆ (fun x ↦ (11 / 5 : ℝ) • x + b) '' (T '' L) :=
  diam_le besicovitch K L hK hL

end BM
