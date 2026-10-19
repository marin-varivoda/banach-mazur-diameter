/-
Soundness of the checker's polygon tests: point in triangle, point in fan, and witnesses
(Proposition 5.1 of the paper).
-/
import BMLean.Defs

namespace BM

open Set

def crossR (o a b : P2) : ℝ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

lemma toR_cross (o a b : BMC.Pt) : ((BMC.cross o a b : ℚ) : ℝ) = crossR (toR o) (toR a) (toR b) := by
  simp only [BMC.cross, crossR, toR]; push_cast; ring

lemma tri_mem (a b c p : P2) (hd : crossR a b c ≠ 0) (hx : 0 ≤ crossR p b c / crossR a b c)
    (hy : 0 ≤ crossR a p c / crossR a b c) (hz : 0 ≤ crossR a b p / crossR a b c) :
    p ∈ convexHull ℝ {a, b, c} := by
  set d := crossR a b c
  let w : Fin 3 → ℝ := ![crossR p b c / d, crossR a p c / d, crossR a b p / d]
  let z : Fin 3 → P2 := ![a, b, c]
  have hsum : ∑ i, w i = 1 := by
    simp only [w, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← add_div, ← add_div, div_eq_one_iff_eq hd]
    simp only [d, crossR]; ring
  have hmem := Finset.centerMass_mem_convexHull (R := ℝ) (s := ({a, b, c} : Set P2))
    (Finset.univ : Finset (Fin 3)) (w := w) (z := z)
    (fun i _ ↦ by fin_cases i <;> simpa [w] using by assumption)
    (by rw [hsum]; norm_num)
    (fun i _ ↦ by fin_cases i <;> simp [z])
  have hcm : (Finset.univ : Finset (Fin 3)).centerMass w z = p := by
    rw [Finset.centerMass, hsum, inv_one, one_smul]
    simp only [w, z, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      simp only [d, crossR]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      simp only [d, crossR]; ring
  rw [hcm] at hmem; exact hmem

lemma inTri_sound {a b c p : BMC.Pt} (h : BMC.inTri a b c p = true) :
    toR p ∈ convexHull ℝ {toR a, toR b, toR c} := by
  simp only [BMC.inTri, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have e := toR_cross
  rcases h with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  · have h0' : (0 : ℝ) < crossR (toR a) (toR b) (toR c) := by rw [← e]; exact_mod_cast h0
    have h1' : (0 : ℝ) ≤ crossR (toR p) (toR b) (toR c) := by rw [← e]; exact_mod_cast h1
    have h2' : (0 : ℝ) ≤ crossR (toR a) (toR p) (toR c) := by rw [← e]; exact_mod_cast h2
    have h3' : (0 : ℝ) ≤ crossR (toR a) (toR b) (toR p) := by rw [← e]; exact_mod_cast h3
    exact tri_mem _ _ _ _ h0'.ne' (div_nonneg h1' h0'.le) (div_nonneg h2' h0'.le)
      (div_nonneg h3' h0'.le)
  · have h0' : crossR (toR a) (toR b) (toR c) < 0 := by rw [← e]; exact_mod_cast h0
    have h1' : crossR (toR p) (toR b) (toR c) ≤ 0 := by rw [← e]; exact_mod_cast h1
    have h2' : crossR (toR a) (toR p) (toR c) ≤ 0 := by rw [← e]; exact_mod_cast h2
    have h3' : crossR (toR a) (toR b) (toR p) ≤ 0 := by rw [← e]; exact_mod_cast h3
    exact tri_mem _ _ _ _ h0'.ne (div_nonneg_of_nonpos h1' h0'.le)
      (div_nonneg_of_nonpos h2' h0'.le) (div_nonneg_of_nonpos h3' h0'.le)

lemma hullR_mono {l1 l2 : List BMC.Pt} (h : ∀ x ∈ l1, x ∈ l2) : hullR l1 ⊆ hullR l2 :=
  convexHull_mono (image_mono fun x hx ↦ h x hx)

lemma mem_hullR {l : List BMC.Pt} {x : BMC.Pt} (h : x ∈ l) : toR x ∈ hullR l :=
  subset_convexHull ℝ _ ⟨x, h, rfl⟩

lemma convex_hullR (l : List BMC.Pt) : Convex ℝ (hullR l) := convex_convexHull ℝ _

lemma inPoly_sound {h : List BMC.Pt} {p : BMC.Pt} (hp : BMC.inPoly h p = true) :
    toR p ∈ hullR h := by
  match h, hp with
  | a :: rest, hp =>
    simp only [BMC.inPoly, List.any_eq_true] at hp
    obtain ⟨⟨b, c⟩, hbc, ht⟩ := hp
    have hb : b ∈ rest := List.of_mem_zip hbc |>.1
    have hc : c ∈ rest := List.mem_of_mem_tail (List.of_mem_zip hbc).2
    refine convexHull_mono ?_ (inTri_sound ht)
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨a, List.mem_cons_self .., rfl⟩
    · exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    · exact ⟨c, List.mem_cons_of_mem _ hc, rfl⟩

lemma hullR_subset_of_inPoly {l h : List BMC.Pt} (H : ∀ x ∈ l, BMC.inPoly h x = true) :
    hullR l ⊆ hullR h :=
  convexHull_min (by rintro _ ⟨x, hx, rfl⟩; exact inPoly_sound (H x hx)) (convex_hullR h)

lemma Polys.ok_sound {P : BMC.Polys} (h : P.ok = true) :
    hullR P.hP ⊆ hullR P.gP ∧ hullR P.gO ⊆ hullR P.hO := by
  simp only [BMC.Polys.ok, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨hullR_mono h.1, hullR_subset_of_inPoly h.2⟩

lemma image_hullR (E : P2 ≃ᵃ[ℝ] P2) (f : BMC.Pt → BMC.Pt) (hf : ∀ p, toR (f p) = E (toR p))
    (l : List BMC.Pt) : E '' hullR l = hullR (l.map f) := by
  rw [hullR, hullR, ← AffineEquiv.coe_toAffineMap, AffineMap.image_convexHull]
  congr 1
  ext y
  simp only [mem_image, mem_ofPred_eq, List.mem_map, AffineEquiv.coe_toAffineMap]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨f p, ⟨p, hp, rfl⟩, hf p⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨toR p, ⟨p, hp, rfl⟩, (hf p).symm⟩

/-- Proposition 5.1 -/
theorem witness_sound {C D : BMC.Polys} {w : BMC.Wit} (hC : C.ok = true) (hD : D.ok = true)
    (hw : BMC.witnessOk C D w = true) {K L : Set P2} (h1 : hullR C.gP ⊆ K) (h2 : K ⊆ hullR C.gO)
    (h3 : hullR D.gP ⊆ L) (h4 : L ⊆ hullR D.gO) :
    0 < BMC.rq w.lam ∧ Sandwich K L ((BMC.rq w.lam : ℚ) : ℝ) := by
  obtain ⟨hCP, hCO⟩ := Polys.ok_sound hC
  obtain ⟨hDP, hDO⟩ := Polys.ok_sound hD
  simp only [BMC.witnessOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  obtain ⟨⟨⟨hl, hdet⟩, hin⟩, hout⟩ := hw
  refine ⟨hl, ?_⟩
  set a := BMC.rq w.m00
  set b := BMC.rq w.m01
  set c := BMC.rq w.m10
  set d := BMC.rq w.m11
  set t0 := BMC.rq w.t0
  set t1 := BMC.rq w.t1
  set s0 := BMC.rq w.s0
  set s1 := BMC.rq w.s1
  set l := BMC.rq w.lam
  have hdetR : (a : ℝ) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  set T := affE a b c d t0 t1 hdetR
  set bb : P2 := ((s0 : ℝ), (s1 : ℝ)) - (l : ℝ) • ((t0 : ℝ), (t1 : ℝ))
  set F : P2 ≃ᵃ[ℝ] P2 := T.trans (homE l hlR.ne' bb)
  have hT : ∀ p, toR (BMC.amap a b c d 1 t0 t1 p) = T (toR p) := by
    intro p; simp only [toR, BMC.amap, T, affE_apply]; push_cast; ext <;> simp
  have hF : ∀ p, toR (BMC.amap a b c d l s0 s1 p) = F (toR p) := by
    intro p
    simp only [toR, BMC.amap, F, T, bb, AffineEquiv.coe_trans, Function.comp_apply, homE_apply,
      affE_apply]
    push_cast; ext <;> simp <;> ring
  refine ⟨T, bb, ?_, ?_⟩
  · calc T '' L ⊆ T '' hullR D.hO := image_mono (h4.trans hDO)
      _ = hullR (D.hO.map (BMC.amap a b c d 1 t0 t1)) := image_hullR T _ hT _
      _ ⊆ hullR C.hP := hullR_subset_of_inPoly (by
          intro x hx
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
          exact hin p hp)
      _ ⊆ K := hCP.trans h1
  · have hFe : (fun x ↦ (l : ℝ) • x + bb) '' (T '' L) = F '' L := by
      rw [← image_comp]; congr 1; funext x; simp [F]
    rw [hFe]
    calc K ⊆ hullR C.hO := h2.trans hCO
      _ ⊆ hullR (D.hP.map (BMC.amap a b c d l s0 s1)) := hullR_subset_of_inPoly hout
      _ = F '' hullR D.hP := (image_hullR F _ hF _).symm
      _ ⊆ F '' L := image_mono (hDP.trans h3)

end BM
