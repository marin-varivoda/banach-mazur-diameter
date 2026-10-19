/-
Algebra of sandwiches T(L) ⊆ K ⊆ λ T(L) + b: affine invariance, symmetry, the multiplicative
triangle inequality, monotonicity in λ; explicit affine maps of the plane.
-/
import BMLean.Statement

namespace BM

open Set

/-- x ↦ λ x + b -/
def hom (lam : ℝ) (b : P2) : P2 → P2 := fun x ↦ lam • x + b

lemma affine_hom (E : P2 ≃ᵃ[ℝ] P2) (lam : ℝ) (b x : P2) :
    E (lam • x + b) = lam • E x + (E b - lam • E 0) := by
  have h1 : ∀ v : P2, E v = E.linear v + E 0 := by
    intro v
    have := E.toAffineMap.linear_apply_vsub v 0
    simp only [vsub_eq_sub, sub_zero] at this
    change E v = E.toAffineMap.linear v + E 0
    rw [this]; simp
  rw [h1 (lam • x + b), h1 x, h1 b, map_add, map_smul]
  simp only [smul_add]
  abel

lemma image_hom (E : P2 ≃ᵃ[ℝ] P2) (lam : ℝ) (b : P2) (S : Set P2) :
    E '' ((fun x ↦ lam • x + b) '' S) = (fun x ↦ lam • x + (E b - lam • E 0)) '' (E '' S) := by
  ext y; simp only [mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨E x, ⟨x, hx, rfl⟩, (affine_hom E lam b x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨lam • x + b, ⟨x, hx, rfl⟩, affine_hom E lam b x⟩

lemma image_hom_hom (a c : ℝ) (b d : P2) (S : Set P2) :
    (fun x ↦ a • x + b) '' ((fun x ↦ c • x + d) '' S) = (fun x ↦ (a * c) • x + (a • d + b)) '' S := by
  rw [image_image]; congr 1; funext x; simp only [smul_add, smul_smul]; abel

/-- affine invariance -/
lemma Sandwich.image {K L : Set P2} {lam : ℝ} (h : Sandwich K L lam) (E F : P2 ≃ᵃ[ℝ] P2) :
    Sandwich (E '' K) (F '' L) lam := by
  obtain ⟨T, b, h1, h2⟩ := h
  refine ⟨(F.symm.trans T).trans E, E b - lam • E 0, ?_, ?_⟩
  · have : ((F.symm.trans T).trans E) '' (F '' L) = E '' (T '' L) := by
      simp only [← image_comp]; congr 1; funext x; simp
    rw [this]; exact image_mono h1
  · have : ((F.symm.trans T).trans E) '' (F '' L) = E '' (T '' L) := by
      simp only [← image_comp]; congr 1; funext x; simp
    rw [this, ← image_hom]; exact image_mono h2

/-- the affine equivalence x ↦ λ x + b, λ ≠ 0 -/
noncomputable def homE (lam : ℝ) (h : lam ≠ 0) (b : P2) : P2 ≃ᵃ[ℝ] P2 :=
  ((LinearEquiv.smulOfNeZero ℝ P2 lam h).toAffineEquiv).trans (AffineEquiv.constVAdd ℝ P2 b)

@[simp] lemma homE_apply (lam : ℝ) (h : lam ≠ 0) (b x : P2) : homE lam h b x = lam • x + b := by
  simp [homE, add_comm]

lemma Sandwich.symm {K L : Set P2} {lam : ℝ} (hl : lam ≠ 0) (h : Sandwich K L lam) :
    Sandwich L K lam := by
  obtain ⟨T, b, h1, h2⟩ := h
  -- S := (hom ∘ T)⁻¹ maps K into L, and T⁻¹ K ⊇ L
  set G : P2 ≃ᵃ[ℝ] P2 := T.trans (homE lam hl b)
  have hG : ∀ x, G x = lam • T x + b := fun x ↦ by simp [G]
  refine ⟨G.symm, T.symm b - lam • T.symm 0 + ?_, ?_, ?_⟩
  · exact 0
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨_, ⟨l, hl', rfl⟩, hxl⟩ := h2 hx
    have : G.symm x = l := by
      rw [AffineEquiv.symm_apply_eq, hG]; exact hxl.symm
    rw [this]; exact hl'
  · intro l hl'
    have hTl : T l ∈ K := h1 ⟨l, hl', rfl⟩
    refine ⟨G.symm (T l), ⟨T l, hTl, rfl⟩, ?_⟩
    -- λ G⁻¹(T l) + (T⁻¹ b - λ T⁻¹ 0) = l
    have key := affine_hom T.symm lam b (G.symm (T l))
    have hGT : lam • T (G.symm (T l)) + b = T l := by rw [← hG]; simp
    have : T.symm (lam • T (G.symm (T l)) + b) = l := by rw [hGT]; simp
    -- T.symm (λ • T y + b) = λ • y + (T.symm b - λ • T.symm 0)
    have key2 := affine_hom T.symm lam b (T (G.symm (T l)))
    simp only [AffineEquiv.symm_apply_apply] at key2
    show lam • G.symm (T l) + (T.symm b - lam • T.symm 0 + 0) = l
    rw [add_zero, ← key2, this]

/-- multiplicative triangle inequality -/
lemma Sandwich.trans {K M L : Set P2} {e e' : ℝ} (h1 : Sandwich K M e) (h2 : Sandwich M L e') :
    Sandwich K L (e * e') := by
  obtain ⟨T1, b1, h11, h12⟩ := h1
  obtain ⟨T2, b2, h21, h22⟩ := h2
  refine ⟨T2.trans T1, e • (T1 b2 - e' • T1 0) + b1, ?_, ?_⟩
  · have : (T2.trans T1) '' L = T1 '' (T2 '' L) := by rw [← image_comp]; rfl
    rw [this]; exact (image_mono h21).trans h11
  · have : (T2.trans T1) '' L = T1 '' (T2 '' L) := by rw [← image_comp]; rfl
    rw [this, ← image_hom_hom, ← image_hom]
    exact h12.trans (image_mono (image_mono h22))

/-- monotonicity in λ -/
lemma Sandwich.mono {K L : Set P2} {lam mu : ℝ} (h : Sandwich K L lam) (hl : 0 < lam)
    (hlm : lam ≤ mu) (hL : Convex ℝ L) (hne : L.Nonempty) : Sandwich K L mu := by
  obtain ⟨T, b, h1, h2⟩ := h
  obtain ⟨c0, hc0⟩ := hne
  set c := T c0
  have hTL : Convex ℝ (T '' L) := hL.affine_image T.toAffineMap
  have hc : c ∈ T '' L := ⟨c0, hc0, rfl⟩
  have hmu : 0 < mu := hl.trans_le hlm
  refine ⟨T, b - (mu - lam) • c, h1, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h2 hx
  refine ⟨c + (lam / mu) • (y - c), ?_, ?_⟩
  · have : c + (lam / mu) • (y - c) = (1 - lam / mu) • c + (lam / mu) • y := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    apply hTL hc hy
    · rw [sub_nonneg, div_le_one hmu]; exact hlm
    · positivity
    · ring
  · simp only [smul_add, smul_sub, smul_smul]
    rw [mul_div_cancel₀ _ hmu.ne']
    simp only [sub_smul]; abel

/-- explicit affine maps of the plane: p ↦ (a p₁ + b p₂ + e, c p₁ + d p₂ + f) -/
noncomputable def affE (a b c d e f : ℝ) (h : a * d - b * c ≠ 0) : P2 ≃ᵃ[ℝ] P2 :=
  (LinearEquiv.toAffineEquiv
    { toFun := fun p ↦ (a * p.1 + b * p.2, c * p.1 + d * p.2)
      invFun := fun p ↦ ((d * p.1 - b * p.2) / (a * d - b * c), (a * p.2 - c * p.1) / (a * d - b * c))
      map_add' := fun p q ↦ by ext <;> simp <;> ring
      map_smul' := fun r p ↦ by ext <;> simp <;> ring
      left_inv := fun p ↦ by
        ext
        · show (d * (a * p.1 + b * p.2) - b * (c * p.1 + d * p.2)) / (a * d - b * c) = p.1
          rw [div_eq_iff h]; ring
        · show (a * (c * p.1 + d * p.2) - c * (a * p.1 + b * p.2)) / (a * d - b * c) = p.2
          rw [div_eq_iff h]; ring
      right_inv := fun p ↦ by
        ext
        · show a * ((d * p.1 - b * p.2) / (a * d - b * c)) + b * ((a * p.2 - c * p.1) / (a * d - b * c)) = p.1
          rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff h]; ring
        · show c * ((d * p.1 - b * p.2) / (a * d - b * c)) + d * ((a * p.2 - c * p.1) / (a * d - b * c)) = p.2
          rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff h]; ring }).trans
    (AffineEquiv.constVAdd ℝ P2 (e, f))

@[simp] lemma affE_apply (a b c d e f : ℝ) (h : a * d - b * c ≠ 0) (p : P2) :
    affE a b c d e f h p = (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f) := by
  simp [affE, add_comm]

end BM
