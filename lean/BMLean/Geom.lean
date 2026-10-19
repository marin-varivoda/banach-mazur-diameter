/-
The geometry of the hexagon frame (paper, Sections 2 and 4): supporting lines at the vertices,
the hexagram lemma, slopes, the vertex condition, dominance, and the cell lemma P(C) ⊆ K ⊆ O(C).
-/
import BMLean.Defs

namespace BM

open Set

lemma IsConvexBody.image {K : Set P2} (hK : IsConvexBody K) (E : P2 ≃ᵃ[ℝ] P2) :
    IsConvexBody (E '' K) := by
  obtain ⟨hc, hcv, hi⟩ := hK
  set H := E.toHomeomorphOfFiniteDimensional
  have hH : ⇑H = ⇑E := rfl
  refine ⟨hc.image E.toHomeomorphOfFiniteDimensional.continuous, hcv.affine_image E.toAffineMap, ?_⟩
  have : interior (H '' K) = H '' interior K := (H.image_interior K).symm
  rw [hH] at this
  rw [this]; exact hi.image _

lemma Normalized.image {K : Set P2} (hK : Normalized K) (E : P2 ≃ᵃ[ℝ] P2)
    (hE : ∀ v ∈ hexVerts, E.symm v ∈ hexVerts) : Normalized (E '' K) := by
  refine ⟨hK.1.image E, fun v hv ↦ ?_⟩
  set H := E.toHomeomorphOfFiniteDimensional
  have hH : ⇑H = ⇑E := rfl
  have : frontier (H '' K) = H '' frontier K := (H.image_frontier K).symm
  rw [hH] at this
  rw [this]
  exact ⟨E.symm v, hK.2 _ (hE v hv), by simp⟩

lemma Normalized.hex_mem {K : Set P2} (hK : Normalized K) {v : P2} (hv : v ∈ hexVerts) : v ∈ K := by
  have := frontier_subset_closure (hK.2 v hv)
  rwa [hK.1.1.isClosed.closure_eq] at this

lemma Normalized.H0_subset {K : Set P2} (hK : Normalized K) : H0 ⊆ K :=
  convexHull_min (fun _ hv ↦ hK.hex_mem hv) hK.1.2.1

/-- normalisation, from the Besicovitch hypothesis -/
lemma normalize (hB : Besicovitch) {K : Set P2} (hK : IsConvexBody K) :
    ∃ A : P2 ≃ᵃ[ℝ] P2, Normalized (A '' K) := by
  obtain ⟨A, -, hA⟩ := hB K hK
  refine ⟨A.symm, hK.image A.symm, fun v hv ↦ ?_⟩
  set H := A.symm.toHomeomorphOfFiniteDimensional
  have hH : ⇑H = ⇑A.symm := rfl
  have : frontier (H '' K) = H '' frontier K := (H.image_frontier K).symm
  rw [hH] at this
  rw [this]
  exact ⟨A v, hA v hv, by simp⟩

/-- a supporting line at a boundary point -/
lemma exists_support {K : Set P2} (hK : IsConvexBody K) {V : P2} (hV : V ∈ frontier K) :
    ∃ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) ∧ ∀ p ∈ K, u * (p.1 - V.1) + v * (p.2 - V.2) ≤ 0 := by
  obtain ⟨-, hconv, hint⟩ := hK
  have hVi : V ∉ interior K := hV.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior hVi
  have hcl : K ⊆ closure (interior K) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint]; exact subset_closure
  have hle : ∀ p ∈ K, f p ≤ f V := by
    intro p hp
    have : p ∈ closure {q | f q ≤ f V} := closure_mono (fun q hq ↦ (hf q hq).le) (hcl hp)
    rwa [(isClosed_le f.continuous continuous_const).closure_eq] at this
  have dec : ∀ q : P2, f q = q.1 * f (1, 0) + q.2 * f (0, 1) := by
    intro q
    have : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨f (1, 0), f (0, 1), ?_, ?_⟩
  · by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := hint
    have := hf a ha
    rw [dec a, dec V, h.1, h.2] at this
    simp at this
  · intro p hp
    have := hle p hp
    rw [dec p, dec V] at this
    linarith

/-! ### helpers -/

lemma mem_hull3 {a b c p : P2} {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : 0 < x + y + z) (h1 : x * a.1 + y * b.1 + z * c.1 = (x + y + z) * p.1)
    (h2 : x * a.2 + y * b.2 + z * c.2 = (x + y + z) * p.2) : p ∈ convexHull ℝ {a, b, c} := by
  have := Finset.centerMass_mem_convexHull (R := ℝ) (s := ({a, b, c} : Set P2)) Finset.univ
    (w := ![x, y, z]) (z := ![a, b, c]) (by intro i _; fin_cases i <;> simpa)
    (by simpa [Fin.sum_univ_three] using hs) (by intro i _; fin_cases i <;> simp)
  convert this using 1
  have hs' : x + y + z ≠ 0 := hs.ne'
  ext
  · simp only [Finset.centerMass, Fin.sum_univ_three, Prod.smul_fst, Prod.fst_add, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Prod.smul_mk]
    field_simp; linarith
  · simp only [Finset.centerMass, Fin.sum_univ_three, Prod.smul_snd, Prod.snd_add, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Prod.smul_mk]
    field_simp; linarith

/-- signed area -/
def crossG (o a b : P2) : ℝ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

lemma mem_tri_cross {a b c p : P2} (hD : 0 < crossG a b c) (hx : 0 ≤ crossG p b c)
    (hy : 0 ≤ crossG a p c) (hz : 0 ≤ crossG a b p) : p ∈ convexHull ℝ {a, b, c} := by
  have hsum : crossG p b c + crossG a p c + crossG a b p = crossG a b c := by
    simp only [crossG]; ring
  refine mem_hull3 hx hy hz (by rw [hsum]; exact hD) ?_ ?_ <;> rw [hsum] <;> simp only [crossG] <;> ring

lemma Normalized.rot {K : Set P2} (hK : Normalized K) (k : ℕ) : Normalized (rotR^[k] ⁻¹' K) := by
  have : rotR^[k] ⁻¹' K = (rotIter k).symm '' K := by
    rw [AffineEquiv.image_symm, rotIter_coe]
  rw [this]
  refine hK.image _ (fun v hv ↦ ?_)
  have : (rotIter k).symm.symm v = rotIter k v := rfl
  rw [this, rotIter_coe]; exact rotR_iter_hex k hv

lemma hB_mem : ptB ∈ hexVerts := by simp [hexVerts, ptB]
lemma hC_mem : ptC ∈ hexVerts := by simp [hexVerts, ptC]

/-- supporting line at B, with the constraints from C and B₁ = (-2,-1) -/
lemma supportB {K : Set P2} (hK : Normalized K) :
    ∃ u v : ℝ, u ≤ 0 ∧ 0 < v ∧ -u ≤ v ∧ ∀ p ∈ K, u * (p.1 + 1) + v * p.2 ≤ 0 := by
  obtain ⟨u, v, hne, h⟩ := exists_support hK.1 (hK.2 _ hB_mem)
  have hC := h _ (hK.hex_mem hC_mem)
  have hB1 := h (-2, -1) (hK.hex_mem (by simp [hexVerts]))
  simp only [ptB, ptC] at hC hB1 h
  norm_num at hC hB1
  have hv : 0 < v := by
    rcases lt_or_eq_of_le (show 0 ≤ v by linarith) with h' | h'
    · exact h'
    · exfalso; rcases hne with h1 | h1
      · exact h1 (by linarith)
      · exact h1 h'.symm
  refine ⟨u, v, by linarith, hv, by linarith, fun p hp ↦ ?_⟩
  have := h p hp; simp at this; linarith

/-- supporting line at C, with the constraints from B and C₅ = (2,-1) -/
lemma supportC {K : Set P2} (hK : Normalized K) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 < v ∧ u ≤ v ∧ ∀ p ∈ K, u * (p.1 - 1) + v * p.2 ≤ 0 := by
  obtain ⟨u, v, hne, h⟩ := exists_support hK.1 (hK.2 _ hC_mem)
  have hB := h _ (hK.hex_mem hB_mem)
  have hC5 := h (2, -1) (hK.hex_mem (by simp [hexVerts]))
  simp only [ptB, ptC] at hB hC5 h
  norm_num at hB hC5
  have hv : 0 < v := by
    rcases lt_or_eq_of_le (show 0 ≤ v by linarith) with h' | h'
    · exact h'
    · exfalso; rcases hne with h1 | h1
      · exact h1 (by linarith)
      · exact h1 h'.symm
  refine ⟨u, v, by linarith, hv, by linarith, fun p hp ↦ ?_⟩
  have := h p hp; simp at this; linarith

lemma side0 {K : Set P2} (hK : Normalized K) {p : P2} (hp : p ∈ K) (hy : 0 < p.2) :
    -1 < p.1 ∧ p.1 < 1 := by
  obtain ⟨u, v, hu, hv, huv, h⟩ := supportB hK
  obtain ⟨u', v', hu', hv', huv', h'⟩ := supportC hK
  have h1 := h p hp
  have h2 := h' p hp
  constructor
  · by_contra hc; push Not at hc
    have : 0 ≤ u * (p.1 + 1) := mul_nonneg_of_nonpos_of_nonpos hu (by linarith)
    have : 0 < v * p.2 := mul_pos hv hy
    linarith
  · by_contra hc; push Not at hc
    have : 0 ≤ u' * (p.1 - 1) := mul_nonneg hu' (by linarith)
    have : 0 < v' * p.2 := mul_pos hv' hy
    linarith

lemma qzR_slopes {w : P2} (hw : 0 < w.1 ∧ 0 < w.2) :
    (qzR w).1 + 1 = 2 * w.2 / (w.1 + w.2) ∧ (qzR w).1 - 1 = -(2 * w.1 / (w.1 + w.2)) ∧
    (qzR w).2 = 2 * w.1 * w.2 / (w.1 + w.2) := by
  have : w.1 + w.2 ≠ 0 := by linarith
  refine ⟨?_, ?_, rfl⟩ <;> simp only [qzR] <;> field_simp <;> ring

lemma pos_of_mul {c t : ℝ} (hc : 0 < c) (h : c * t ≤ 0) : t ≤ 0 := by
  by_contra h'; push Not at h'; linarith [mul_pos hc h']

/-- at B: u + a v ≤ 0 for a point of K over side 0 with slope a -/
lemma atB {u v : ℝ} {w : P2} (hw : 0 < w.1 ∧ 0 < w.2)
    (h : u * ((qzR w).1 + 1) + v * (qzR w).2 ≤ 0) : u + w.1 * v ≤ 0 := by
  obtain ⟨e1, -, e3⟩ := qzR_slopes hw
  rw [e1, e3] at h
  have hs : 0 < w.1 + w.2 := by linarith
  apply pos_of_mul (c := 2 * w.2 / (w.1 + w.2)) (div_pos (by linarith) hs)
  have : 2 * w.2 / (w.1 + w.2) * (u + w.1 * v) = u * (2 * w.2 / (w.1 + w.2)) + v * (2 * w.1 * w.2 / (w.1 + w.2)) := by
    field_simp; try ring
  linarith

lemma atC {u v : ℝ} {w : P2} (hw : 0 < w.1 ∧ 0 < w.2)
    (h : u * ((qzR w).1 - 1) + v * (qzR w).2 ≤ 0) : -u + w.2 * v ≤ 0 := by
  obtain ⟨-, e2, e3⟩ := qzR_slopes hw
  rw [e2, e3] at h
  have hs : 0 < w.1 + w.2 := by linarith
  apply pos_of_mul (c := 2 * w.1 / (w.1 + w.2)) (div_pos (by linarith) hs)
  have : 2 * w.1 / (w.1 + w.2) * (-u + w.2 * v) = u * -(2 * w.1 / (w.1 + w.2)) + v * (2 * w.1 * w.2 / (w.1 + w.2)) := by
    field_simp; try ring
  linarith

/-- at B, for a point over side 1 (= rotR of a point over side 0) with b-slope b' -/
lemma atB1 {u v : ℝ} {z : P2} (hz : 0 < z.1 ∧ 0 < z.2)
    (h : u * ((rotR (qzR z)).1 + 1) + v * (rotR (qzR z)).2 ≤ 0) :
    -u * (1 + 3 * z.2) + v * (z.2 - 1) ≤ 0 := by
  have hs : 0 < z.1 + z.2 := by linarith
  have e : u * ((rotR (qzR z)).1 + 1) + v * (rotR (qzR z)).2 =
      z.1 / (z.1 + z.2) * (-u * (1 + 3 * z.2) + v * (z.2 - 1)) := by
    simp only [rotR, qzR]; field_simp; ring
  rw [e] at h
  exact pos_of_mul (div_pos (by linarith) hs) h

/-- at C, for a point over side 5 (= rotR^[5] of a point over side 0) with a-slope a' -/
lemma atC5 {u v : ℝ} {z : P2} (hz : 0 < z.1 ∧ 0 < z.2)
    (h : u * ((rotR^[5] (qzR z)).1 - 1) + v * (rotR^[5] (qzR z)).2 ≤ 0) :
    u * (1 + 3 * z.1) + v * (z.1 - 1) ≤ 0 := by
  have hs : 0 < z.1 + z.2 := by linarith
  have e : u * ((rotR^[5] (qzR z)).1 - 1) + v * (rotR^[5] (qzR z)).2 =
      z.2 / (z.1 + z.2) * (u * (1 + 3 * z.1) + v * (z.1 - 1)) := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, rotR, qzR]
    field_simp; ring
  rw [e] at h
  exact pos_of_mul (div_pos (by linarith) hs) h

lemma qzR_inv {p : P2} (h1 : -1 < p.1) (h2 : p.1 < 1) (hy : 0 < p.2) :
    qzR (p.2 / (1 + p.1), p.2 / (1 - p.1)) = p := by
  have a1 : 1 + p.1 ≠ 0 := by linarith
  have a2 : 1 - p.1 ≠ 0 := by linarith
  have a3 : p.2 ≠ 0 := hy.ne'
  ext <;> simp only [qzR] <;> field_simp <;> ring

lemma mem_H0_of_forms {x : P2} (h : ∀ j < 6, (rotR^[j] x).2 ≤ 0) : x ∈ H0 := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, rotR] at h0 h1 h2 h3 h4 h5
  have sub : ∀ a ∈ hexVerts, ∀ b ∈ hexVerts, ∀ c ∈ hexVerts, convexHull ℝ {a, b, c} ⊆ H0 := by
    intro a ha b hb c hc
    apply convexHull_mono
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have v0 : ((1 : ℝ), (0 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  have v1 : ((-1 : ℝ), (0 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  have v2 : ((-2 : ℝ), (-1 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  have v3 : ((-1 : ℝ), (-2 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  have v4 : ((1 : ℝ), (-2 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  have v5 : ((2 : ℝ), (-1 : ℝ)) ∈ hexVerts := by simp [hexVerts]
  rcases le_total (x.1 - 3 * x.2 - 1) 0 with d1 | d1
  · apply sub _ v0 _ v1 _ v2
    apply mem_tri_cross <;> simp only [crossG] <;> norm_num <;> linarith
  rcases le_total (x.1 - x.2 - 1) 0 with d2 | d2
  · apply sub _ v0 _ v2 _ v3
    apply mem_tri_cross <;> simp only [crossG] <;> norm_num <;> linarith
  rcases le_total (x.1 - 1) 0 with d3 | d3
  · apply sub _ v0 _ v3 _ v4
    apply mem_tri_cross <;> simp only [crossG] <;> norm_num <;> linarith
  · apply sub _ v0 _ v4 _ v5
    apply mem_tri_cross <;> simp only [crossG] <;> norm_num <;> linarith

/-- Lemma 2.2 (hexagram), in slope form: a point of K outside H₀ lies over some side k, with
positive slopes. -/
lemma hexagram {K : Set P2} (hK : Normalized K) {x : P2} (hx : x ∈ K) (hxH : x ∉ H0) :
    ∃ k < 6, ∃ w : P2, 0 < w.1 ∧ 0 < w.2 ∧ qR k w = x := by
  by_contra hne
  push Not at hne
  apply hxH
  apply mem_H0_of_forms
  intro j hj
  by_contra hy
  push Not at hy
  set p := rotR^[j] x with hp
  set kk := (6 - j) % 6
  have hkk : kk < 6 := Nat.mod_lt _ (by norm_num)
  have hpx : rotR^[kk] p = x := by
    simp only [kk, p]
    rw [rotR_iter_mod, ← Function.iterate_add_apply, show 6 - j + j = 6 by omega, rotR_iter_six]
    rfl
  have hK' := hK.rot kk
  have hpK : p ∈ rotR^[kk] ⁻¹' K := by rw [mem_preimage, hpx]; exact hx
  obtain ⟨h1, h2⟩ := side0 hK' hpK hy
  have hq : qzR (p.2 / (1 + p.1), p.2 / (1 - p.1)) = p := qzR_inv h1 h2 hy
  refine hne kk hkk (p.2 / (1 + p.1), p.2 / (1 - p.1)) (div_pos hy (by linarith))
    (div_pos hy (by linarith)) ?_
  simp only [qR]; rw [hq, hpx]

/-- Lemma 2.3 (vertex condition) -/
lemma vertex {K : Set P2} (hK : Normalized K) (k : ℕ) {w z : P2} (hw : 0 < w.1 ∧ 0 < w.2)
    (hz : 0 < z.1 ∧ 0 < z.2) (h1 : qR k w ∈ K) (h2 : qR (k + 1) z ∈ K) :
    w.1 + z.2 + 3 * w.1 * z.2 ≤ 1 := by
  have hK' := hK.rot k
  obtain ⟨u, v, hu, hv, huv, hs⟩ := supportB hK'
  have e1 : qzR w ∈ rotR^[k] ⁻¹' K := h1
  have e2 : rotR (qzR z) ∈ rotR^[k] ⁻¹' K := by
    rw [mem_preimage, ← Function.iterate_succ_apply]; exact h2
  have hB := atB hw (hs _ e1)
  have hB1 := atB1 hz (hs _ e2)
  have h3 : (u + w.1 * v) * (1 + 3 * z.2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hB (by linarith)
  have : v * (w.1 + z.2 + 3 * w.1 * z.2 - 1) ≤ 0 := by
    have : v * (w.1 + z.2 + 3 * w.1 * z.2 - 1) =
      (u + w.1 * v) * (1 + 3 * z.2) + (-u * (1 + 3 * z.2) + v * (z.2 - 1)) := by ring
    linarith
  linarith [pos_of_mul hv this]

/-- the slopes of the points of K are at most 1 -/
lemma slope_le_one {K : Set P2} (hK : Normalized K) (k : ℕ) {w : P2} (hw : 0 < w.1 ∧ 0 < w.2)
    (h : qR k w ∈ K) : w.1 ≤ 1 ∧ w.2 ≤ 1 := by
  have hK' := hK.rot k
  have e1 : qzR w ∈ rotR^[k] ⁻¹' K := h
  obtain ⟨u, v, hu, hv, huv, hs⟩ := supportB hK'
  obtain ⟨u', v', hu', hv', huv', hs'⟩ := supportC hK'
  have hB := atB hw (hs _ e1)
  have hC := atC hw (hs' _ e1)
  constructor
  · have : v * (w.1 - 1) ≤ 0 := by linarith
    linarith [pos_of_mul hv this]
  · have : v' * (w.2 - 1) ≤ 0 := by linarith
    linarith [pos_of_mul hv' this]

/-- (2.1) dominance -/
lemma dominance (k : ℕ) {e w : P2} (he : 0 < e.1 ∧ 0 < e.2) (h1 : e.1 ≤ w.1) (h2 : e.2 ≤ w.2) :
    qR k e ∈ convexHull ℝ {rotR^[k] ptB, rotR^[k] ptC, qR k w} := by
  have hw : 0 < w.1 ∧ 0 < w.2 := ⟨he.1.trans_le h1, he.2.trans_le h2⟩
  have h0 : qzR e ∈ convexHull ℝ {ptB, ptC, qzR w} := by
    obtain ⟨a, b⟩ := e
    obtain ⟨a', b'⟩ := w
    simp only at he hw h1 h2
    obtain ⟨ha, hb⟩ := he
    obtain ⟨ha', hb'⟩ := hw
    have s1 : a + b ≠ 0 := by linarith
    have s2 : a' + b' ≠ 0 := by linarith
    apply mem_hull3 (x := (b' - b) * a * a') (y := (a' - a) * b * b') (z := a * b * (a' + b'))
    · have : 0 ≤ b' - b := by linarith
      positivity
    · have : 0 ≤ a' - a := by linarith
      positivity
    · have : 0 < a' + b' := by linarith
      positivity
    · have : (b' - b) * a * a' + (a' - a) * b * b' + a * b * (a' + b') = a' * b' * (a + b) := by ring
      rw [this]
      have : 0 < a + b := by linarith
      positivity
    · simp only [ptB, ptC, qzR]; field_simp; ring
    · simp only [ptB, ptC, qzR]; field_simp; ring
  have := mem_image_of_mem (rotIter k).toAffineMap h0
  rw [AffineMap.image_convexHull] at this
  simp only [image_insert_eq, image_singleton, AffineEquiv.coe_toAffineMap, rotIter_coe] at this
  exact this

/-- Z_k(K) is a down-set -/
lemma downset {K : Set P2} (hK : Normalized K) (k : ℕ) {e w : P2} (he : 0 < e.1 ∧ 0 < e.2)
    (h1 : e.1 ≤ w.1) (h2 : e.2 ≤ w.2) (hw : qR k w ∈ K) : qR k e ∈ K := by
  refine convexHull_min ?_ hK.1.2.1 (dominance k he h1 h2)
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact hK.hex_mem (rotR_iter_hex k hB_mem)
  · exact hK.hex_mem (rotR_iter_hex k hC_mem)
  · exact hw

/-! ### cells -/

lemma toR_hex_mem {p : BMC.Pt} (hp : p ∈ BMC.hex) : toR p ∈ hexVerts := by
  simp only [BMC.hex, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [toR, hexVerts]

lemma hexVerts_toR {v : P2} (hv : v ∈ hexVerts) : ∃ p ∈ BMC.hex, toR p = v := by
  simp only [hexVerts, mem_insert_iff, mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(1, 0), by simp [BMC.hex], by norm_num [toR]⟩
  · exact ⟨(-1, 0), by simp [BMC.hex], by norm_num [toR]⟩
  · exact ⟨(-2, -1), by simp [BMC.hex], by norm_num [toR]⟩
  · exact ⟨(-1, -2), by simp [BMC.hex], by norm_num [toR]⟩
  · exact ⟨(1, -2), by simp [BMC.hex], by norm_num [toR]⟩
  · exact ⟨(2, -1), by simp [BMC.hex], by norm_num [toR]⟩

lemma hexVerts_sub_gensO (c : BMC.Cell) : hexVerts ⊆ toR '' {p | p ∈ BMC.gensO c} := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := hexVerts_toR hv
  exact ⟨p, List.mem_append_left _ hp, rfl⟩

lemma foldl_max_cases (f : BMC.Pt → ℚ) (l : List BMC.Pt) (m0 : ℚ) :
    l.foldl (fun m z => max m (f z)) m0 = m0 ∨
      ∃ z ∈ l, f z = l.foldl (fun m z => max m (f z)) m0 := by
  induction l generalizing m0 with
  | nil => left; rfl
  | cons z l ih =>
    simp only [List.foldl_cons]
    rcases ih (max m0 (f z)) with h | ⟨z', hz', h⟩
    · rw [h]
      rcases max_choice m0 (f z) with h' | h'
      · left; exact h'
      · right; exact ⟨z, by simp, h'.symm⟩
    · right; exact ⟨z', by simp [hz'], h⟩

lemma foldl_max_ge (f : BMC.Pt → ℚ) (l : List BMC.Pt) (m0 : ℚ) :
    m0 ≤ l.foldl (fun m z => max m (f z)) m0 := by
  induction l generalizing m0 with
  | nil => exact le_rfl
  | cons z l ih => exact (le_max_left _ _).trans (ih _)

lemma mfun_cast (r : ℚ) : ((BMC.mfun r : ℚ) : ℝ) = (1 - (r : ℝ)) / (1 + 3 * (r : ℝ)) := by
  simp [BMC.mfun]

/-- t ≤ m(top f l), from the vertex inequalities against the points of l -/
lemma le_mfun_top (f : BMC.Pt → ℚ) (l : List BMC.Pt) {t : ℝ} (ht1 : t ≤ 1)
    (h : ∀ z ∈ l, t + (f z : ℝ) + 3 * t * (f z : ℝ) ≤ 1) :
    t ≤ ((BMC.mfun (l.foldl (fun m z => max m (f z)) 0) : ℚ) : ℝ) := by
  set r := l.foldl (fun m z => max m (f z)) 0
  have hr : (0 : ℝ) ≤ r := by exact_mod_cast foldl_max_ge f l 0
  rw [mfun_cast, le_div_iff₀ (by linarith)]
  rcases foldl_max_cases f l 0 with h0 | ⟨z, hz, hzr⟩
  · have : (r : ℝ) = 0 := by exact_mod_cast h0
    rw [this]; linarith
  · have := h z hz
    rw [hzr] at this
    linarith

lemma exists_min_ge (A : List ℚ) (t : ℝ) (h : ∃ α ∈ A, t ≤ (α : ℝ)) :
    ∃ a ∈ A, t ≤ (a : ℝ) ∧ ∀ α ∈ A, t ≤ (α : ℝ) → a ≤ α := by
  induction A with
  | nil => simp at h
  | cons x A ih =>
    by_cases hA : ∃ α ∈ A, t ≤ (α : ℝ)
    · obtain ⟨a, ha, hta, hmin⟩ := ih hA
      by_cases hx : t ≤ (x : ℝ) ∧ x < a
      · refine ⟨x, by simp, hx.1, ?_⟩
        intro α hα htα
        simp only [List.mem_cons] at hα
        rcases hα with rfl | hα
        · exact le_rfl
        · exact hx.2.le.trans (hmin α hα htα)
      · refine ⟨a, by simp [ha], hta, ?_⟩
        intro α hα htα
        simp only [List.mem_cons] at hα
        rcases hα with rfl | hα
        · push Not at hx; exact hx htα
        · exact hmin α hα htα
    · obtain ⟨α, hα, htα⟩ := h
      simp only [List.mem_cons] at hα
      rcases hα with rfl | hα
      · refine ⟨α, by simp, htα, ?_⟩
        intro β hβ htβ
        simp only [List.mem_cons] at hβ
        rcases hβ with rfl | hβ
        · exact le_rfl
        · exact absurd ⟨β, hβ, htβ⟩ hA
      · exact absurd ⟨α, hα, htα⟩ hA

lemma corner_exists (c : BMC.Cell) (k : Fin 6) (w : P2)
    (ha : w.1 ≤ ((BMC.mfun (BMC.topB (c.ins (k + 1))) : ℚ) : ℝ))
    (hb : w.2 ≤ ((BMC.mfun (BMC.topA (c.ins (k - 1))) : ℚ) : ℝ))
    (hE : ∀ e ∈ c.outs k, w.1 < (e.1 : ℝ) ∨ w.2 < (e.2 : ℝ)) :
    ∃ cc ∈ BMC.corners c k, w.1 ≤ (cc.1 : ℝ) ∧ w.2 ≤ (cc.2 : ℝ) := by
  obtain ⟨a, haA, hwa, hamin⟩ := exists_min_ge
    (BMC.mfun (BMC.topB (c.ins (k + 1))) :: ((c.outs k).map (·.1)).filter
      (fun a => decide (a < BMC.mfun (BMC.topB (c.ins (k + 1)))))) w.1 ⟨_, List.mem_cons_self, ha⟩
  obtain ⟨b, hbB, hwb, hbmin⟩ := exists_min_ge
    (BMC.mfun (BMC.topA (c.ins (k - 1))) :: ((c.outs k).map (·.2)).filter
      (fun b => decide (b < BMC.mfun (BMC.topA (c.ins (k - 1)))))) w.2 ⟨_, List.mem_cons_self, hb⟩
  refine ⟨(a, b), ?_, hwa, hwb⟩
  simp only [BMC.corners, List.mem_flatMap, List.mem_map, List.mem_filter, List.all_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨a, haA, b, ⟨hbB, fun e he ↦ ?_⟩, rfl⟩
  rcases hE e he with h | h
  · left
    by_cases hlt : e.1 < BMC.mfun (BMC.topB (c.ins (k + 1)))
    · exact hamin e.1 (List.mem_cons_of_mem _ (List.mem_filter.2
        ⟨List.mem_map_of_mem he, by simpa using hlt⟩)) h.le
    · push Not at hlt
      exact (hamin _ List.mem_cons_self ha).trans hlt
  · right
    by_cases hlt : e.2 < BMC.mfun (BMC.topA (c.ins (k - 1)))
    · exact hbmin e.2 (List.mem_cons_of_mem _ (List.mem_filter.2
        ⟨List.mem_map_of_mem he, by simpa using hlt⟩)) h.le
    · push Not at hlt
      exact (hbmin _ List.mem_cons_self hb).trans hlt

lemma cellValid_pos {c : BMC.Cell} (hc : BMC.cellValid c = true) (k : Fin 6) {z : BMC.Pt}
    (hz : z ∈ c.ins k ∨ z ∈ c.outs k) : 0 < (toR z).1 ∧ 0 < (toR z).2 := by
  simp only [BMC.cellValid, List.all_eq_true, List.mem_finRange, true_implies, List.mem_append,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨h1, h2⟩ := hc k z hz
  exact ⟨by simpa [toR] using h1, by simpa [toR] using h2⟩

lemma qR_mod (n : ℕ) (z : P2) : qR (n % 6) z = qR n z := by
  simp only [qR, rotR_iter_mod]

/-- the outer inclusion, for a point outside H₀ -/
lemma outer_point {K : Set P2} {c : BMC.Cell} (hK : Normalized K) (hc : BMC.cellValid c = true)
    (hb : Belongs K c) {k : ℕ} (hk : k < 6) {w : P2} (hw : 0 < w.1 ∧ 0 < w.2) (hx : qR k w ∈ K) :
    qR k w ∈ hullR (BMC.gensO c) := by
  set kf : Fin 6 := ⟨k, hk⟩
  have hE : ∀ e ∈ c.outs kf, w.1 < (e.1 : ℝ) ∨ w.2 < (e.2 : ℝ) := by
    intro e he
    by_contra hcon
    push Not at hcon
    exact (hb kf).2 e he (downset hK k (cellValid_pos hc kf (Or.inr he)) hcon.1 hcon.2 hx)
  have h1 : ((kf + 1 : Fin 6) : ℕ) = (k + 1) % 6 := by simp [Fin.val_add, kf]
  have h5 : ((kf - 1 : Fin 6) : ℕ) = (k + 5) % 6 := by
    rw [Fin.val_sub]; simp only [kf]; congr 1; omega
  have ha : w.1 ≤ ((BMC.mfun (BMC.topB (c.ins (kf + 1))) : ℚ) : ℝ) := by
    apply le_mfun_top (fun z => z.2) _ (slope_le_one hK k hw hx).1
    intro z hz
    have hzK := (hb (kf + 1)).1 z hz
    rw [h1, qR_mod] at hzK
    exact vertex hK k hw (cellValid_pos hc _ (Or.inl hz)) hx hzK
  have hb' : w.2 ≤ ((BMC.mfun (BMC.topA (c.ins (kf - 1))) : ℚ) : ℝ) := by
    apply le_mfun_top (fun z => z.1) _ (slope_le_one hK k hw hx).2
    intro z hz
    have hzK := (hb (kf - 1)).1 z hz
    rw [h5, qR_mod] at hzK
    have hxK : qR (k + 5 + 1) w ∈ K := by
      rw [← qR_mod, show (k + 5 + 1) % 6 = k by omega]; exact hx
    have := vertex hK (k + 5) (cellValid_pos hc _ (Or.inl hz)) hw hzK hxK
    simp only [toR] at this ⊢
    linarith
  obtain ⟨cc, hcc, hc1, hc2⟩ := corner_exists c kf w ha hb' hE
  have hdom := dominance k (w := toR cc) hw hc1 hc2
  refine convexHull_mono ?_ hdom
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact hexVerts_sub_gensO c (rotR_iter_hex k hB_mem)
  · exact hexVerts_sub_gensO c (rotR_iter_hex k hC_mem)
  · refine ⟨BMC.qk k cc, ?_, toR_qk k cc⟩
    simp only [mem_setOf_eq, BMC.gensO, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨kf, List.mem_finRange kf, cc, hcc, rfl⟩

/-- Lemma 4.2 (cell lemma) -/
theorem cell_lemma {K : Set P2} {c : BMC.Cell} (hK : Normalized K) (hc : BMC.cellValid c = true)
    (hb : Belongs K c) : hullR (BMC.gensP c) ⊆ K ∧ K ⊆ hullR (BMC.gensO c) := by
  constructor
  · apply convexHull_min _ hK.1.2.1
    rintro _ ⟨p, hp, rfl⟩
    simp only [mem_setOf_eq, BMC.gensP, List.mem_append, List.mem_flatMap, List.mem_map] at hp
    rcases hp with hp | ⟨k, -, z, hz, rfl⟩
    · exact hK.hex_mem (toR_hex_mem hp)
    · rw [toR_qk]; exact (hb k).1 z hz
  · intro x hx
    by_cases hxH : x ∈ H0
    · exact convexHull_mono (hexVerts_sub_gensO c) hxH
    · obtain ⟨k, hk, w, hw1, hw2, rfl⟩ := hexagram hK hx hxH
      exact outer_point hK hc hb hk ⟨hw1, hw2⟩ hx

end BM
