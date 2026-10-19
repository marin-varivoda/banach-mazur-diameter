/-
The proof of the main theorem: proof trees (Lemma 5.2), hubs, coverage, and the assembly.
-/
import BMLean.Hull
import BMLean.Roots
import BMLean.AllRun

namespace BM

open Set

lemma IsConvexBody.nonempty {K : Set P2} (hK : IsConvexBody K) : K.Nonempty :=
  hK.2.2.mono interior_subset

lemma rq_cast (x : Int) : ((BMC.rq x : ℚ) : ℝ) = (x : ℝ) / 10000000000 := by
  simp only [BMC.rq, BMC.den, Rat.mkRat_eq_div]; push_cast; ring

/-! ### proof trees -/

lemma cellValid_iff {c : BMC.Cell} :
    BMC.cellValid c = true ↔ ∀ k, ∀ z ∈ c.ins k ++ c.outs k, 0 < z.1 ∧ 0 < z.2 := by
  simp only [BMC.cellValid, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq]

lemma cellValid_addIn {c : BMC.Cell} (hc : BMC.cellValid c = true) {k : Fin 6} {z : BMC.Pt}
    (hz : 0 < z.1 ∧ 0 < z.2) : BMC.cellValid (BMC.addIn c k z) = true := by
  rw [cellValid_iff] at hc ⊢
  intro j y hy
  simp only [BMC.addIn] at hy
  split_ifs at hy with hjk
  · simp only [List.cons_append, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hz
    · exact hc j y hy
  · exact hc j y hy

lemma cellValid_addOut {c : BMC.Cell} (hc : BMC.cellValid c = true) {k : Fin 6} {z : BMC.Pt}
    (hz : 0 < z.1 ∧ 0 < z.2) : BMC.cellValid (BMC.addOut c k z) = true := by
  rw [cellValid_iff] at hc ⊢
  intro j y hy
  simp only [BMC.addOut] at hy
  split_ifs at hy with hjk
  · simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hc j y (List.mem_append_left _ hy)
    · exact hz
    · exact hc j y (List.mem_append_right _ hy)
  · exact hc j y hy

/-- splitting: every body of a cell belongs to one of its two halves -/
lemma belongs_split {K : Set P2} {c : BMC.Cell} (hb : Belongs K c) (k : Fin 6) (z : BMC.Pt) :
    Belongs K (BMC.addIn c k z) ∨ Belongs K (BMC.addOut c k z) := by
  by_cases hz : qR k (toR z) ∈ K
  · left
    intro j
    refine ⟨?_, (hb j).2⟩
    intro y hy
    simp only [BMC.addIn] at hy
    split_ifs at hy with hjk
    · subst hjk
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hz
      · exact (hb j).1 y hy
    · exact (hb j).1 y hy
  · right
    intro j
    refine ⟨(hb j).1, ?_⟩
    intro y hy
    simp only [BMC.addOut] at hy
    split_ifs at hy with hjk
    · subst hjk
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hz
      · exact (hb j).2 y hy
    · exact (hb j).2 y hy

lemma lamOk_sound {l : Int} (h : BMC.lamOk l = true) : ((BMC.rq l : ℚ) : ℝ) ≤ 11 / 5 := by
  simp only [BMC.lamOk, BMC.den] at h
  rw [rq_cast, div_le_iff₀ (by norm_num)]
  have : (5 : ℝ) * l ≤ 11 * 10000000000 := by exact_mod_cast of_decide_eq_true h
  linarith

/-- Lemma 5.2 -/
theorem tree_sound : ∀ (t : BMC.Tree) (C D : BMC.Cell), BMC.treeOk C D t = true →
    BMC.cellValid C = true → BMC.cellValid D = true → ∀ K L : Set P2, Normalized K →
    Normalized L → Belongs K C → Belongs L D → Sandwich K L (11 / 5)
  | .leaf w, C, D, ht, hC, hD, K, L, hK, hL, hKC, hLD => by
    simp only [BMC.treeOk, Bool.and_eq_true] at ht
    obtain ⟨⟨⟨hl, hPC⟩, hPD⟩, hw⟩ := ht
    obtain ⟨h1, h2⟩ := cell_lemma hK hC hKC
    obtain ⟨h3, h4⟩ := cell_lemma hL hD hLD
    obtain ⟨hpos, hs⟩ := witness_sound hPC hPD hw h1 h2 h3 h4
    exact hs.mono (by exact_mod_cast hpos) (lamOk_sound hl) hL.1.2.1 hL.1.nonempty
  | .node side k z tin tout, C, D, ht, hC, hD, K, L, hK, hL, hKC, hLD => by
    simp only [BMC.treeOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨⟨hz1, -⟩, hz2⟩, -⟩, ht⟩ := ht
    have hz : 0 < z.1 ∧ 0 < z.2 := ⟨hz1, hz2⟩
    cases side with
    | true =>
      simp only [ite_true, Bool.and_eq_true] at ht
      rcases belongs_split hLD k z with h | h
      · exact tree_sound tin _ _ ht.1 hC (cellValid_addIn hD hz) K L hK hL hKC h
      · exact tree_sound tout _ _ ht.2 hC (cellValid_addOut hD hz) K L hK hL hKC h
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at ht
      rcases belongs_split hKC k z with h | h
      · exact tree_sound tin _ _ ht.1 (cellValid_addIn hC hz) hD K L hK hL h hLD
      · exact tree_sound tout _ _ ht.2 (cellValid_addOut hC hz) hD K L hK hL h hLD

/-! ### the certificate data -/

def allRows : List BMC.Row := BMC.allRowsL.flatten
def allTrees : List BMC.TreeRec := BMC.allTreesL.flatten

lemma row_ok {r : BMC.Row} (hr : r ∈ allRows) : BMC.rowOk BMC.hubPolys r = true := by
  obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
  have h := List.all_eq_true.1 BMC.all_hub_ok l hl
  exact List.all_eq_true.1 h r hrl

lemma tree_ok {t : BMC.TreeRec} (ht : t ∈ allTrees) : BMC.treeRecOk t = true := by
  obtain ⟨l, hl, htl⟩ := List.mem_flatten.1 ht
  have h := List.all_eq_true.1 BMC.all_tree_ok l hl
  exact List.all_eq_true.1 h t htl

/-- the hub polygons -/
def hubQ (n : ℕ) (hn : n < BMC.hubPolys.length) : Set P2 := hullR (BMC.hubPolys[n]).gP

lemma hubPolys_get (n : ℕ) (hn : n < BMC.hubPolys.length) :
    ∃ c, BMC.hubPolys[n] = BMC.fixedPolys (BMC.hubGens c) := by
  simp only [BMC.hubPolys, List.getElem_map]; exact ⟨_, rfl⟩

lemma hubQ_convex (n : ℕ) (hn) : Convex ℝ (hubQ n hn) := convex_hullR _

lemma hubQ_nonempty (n : ℕ) (hn) : (hubQ n hn).Nonempty := by
  obtain ⟨c, hc⟩ := hubPolys_get n hn
  refine ⟨toR (1, 0), ?_⟩
  rw [hubQ, hc]
  exact mem_hullR (by simp [BMC.fixedPolys, BMC.hubGens, BMC.gensP, BMC.hex])

/-- the hub witness of a root cell -/
lemma hub_sound {r : BMC.Row} (hr : r ∈ allRows) {K : Set P2} (hK : Normalized K)
    (hb : Belongs K (BMC.rootCell r.idx)) (n : ℕ) (hn : n < BMC.hubPolys.length)
    (hnw : n < r.wits.length) :
    0 < BMC.rq (r.wits[n]).lam ∧ Sandwich K (hubQ n hn) ((BMC.rq (r.wits[n]).lam : ℚ) : ℝ) := by
  have h := row_ok hr
  simp only [BMC.rowOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, hC⟩, hall⟩ := h
  have hmem : (BMC.hubPolys[n], r.wits[n]) ∈ BMC.hubPolys.zip r.wits := by
    have : n < (BMC.hubPolys.zip r.wits).length := by simp [hn, hnw]
    have := List.getElem_mem this
    simpa using this
  have := hall _ hmem
  simp only [Bool.and_eq_true] at this
  obtain ⟨hD, hw⟩ := this
  obtain ⟨h1, h2⟩ := cell_lemma hK (root_valid r.idx) hb
  obtain ⟨c, hc⟩ := hubPolys_get n hn
  have hQ : hubQ n hn = hullR (BMC.hubPolys[n]).gO := by
    rw [hubQ, hc]; rfl
  exact witness_sound hC hD hw h1 h2 subset_rfl hQ.le

lemma cover : BMC.coverOk allRows allTrees = true := BMC.cover_ok

/-- the bound for two root cells i ≤ j -/
lemma root_pair_le {i j : ℕ} (hij : i ≤ j) (hj : j < BMC.reps.size) {K L : Set P2}
    (hK : Normalized K) (hL : Normalized L) (hKi : Belongs K (BMC.rootCell i))
    (hLj : Belongs L (BMC.rootCell j)) : Sandwich K L (11 / 5) := by
  have h := cover
  simp only [BMC.coverOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨hsize, hidx⟩, hpairs⟩ := h
  have hi : i < BMC.reps.size := lt_of_le_of_lt hij hj
  have hjm : j ∈ List.range' i (BMC.reps.size - i) := by
    rw [List.mem_range'_1]; omega
  rcases (hpairs i hi j hjm).symm with htree | hhub
  · -- a proof tree
    simp only [List.elem_eq_mem, decide_eq_true_eq, List.mem_map] at htree
    obtain ⟨t, ht, htij⟩ := htree
    have := tree_ok ht
    simp only [BMC.treeRecOk, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Prod.mk.injEq] at htij
    obtain ⟨rfl, rfl⟩ := htij
    exact tree_sound t.tree _ _ this.2 (root_valid _) (root_valid _) K L hK hL hKi hLj
  · -- a hub
    have hsz : allRows.length = BMC.reps.size := by simpa using hsize
    have hrow : ∀ m (hm : m < BMC.reps.size), allRows[m] ∈ allRows ∧ (allRows[m]).idx = m := by
      intro m hm
      refine ⟨List.getElem_mem _, ?_⟩
      have hm' : m < (allRows.zipIdx).length := by simp [hsz, hm]
      have := hidx _ (List.getElem_mem hm')
      simpa using this
    have hti : allRows.toArray[i]! = allRows[i] := by
      rw [getElem!_pos allRows.toArray i (by simp [hsz, hi])]; simp
    have htj : allRows.toArray[j]! = allRows[j] := by
      rw [getElem!_pos allRows.toArray j (by simp [hsz, hj])]; simp
    simp only [BMC.hubCov, hti, htj, List.any_eq_true, decide_eq_true_eq] at hhub
    obtain ⟨⟨w1, w2⟩, hmem, hle⟩ := hhub
    obtain ⟨n, hn, hn12⟩ := List.getElem_of_mem hmem
    simp only [List.getElem_zip, Prod.mk.injEq] at hn12
    obtain ⟨h1, h2⟩ := hn12
    have hn1 : n < (allRows[i]).wits.length := by simp at hn; omega
    have hn2 : n < (allRows[j]).wits.length := by simp at hn; omega
    obtain ⟨hri, hidi⟩ := hrow i hi
    obtain ⟨hrj, hidj⟩ := hrow j hj
    have hlen : (allRows[i]).wits.length = BMC.hubPolys.length := by
      have := row_ok hri
      simp only [BMC.rowOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.2
    have hnh : n < BMC.hubPolys.length := hlen ▸ hn1
    obtain ⟨e1, s1⟩ := hub_sound hri hK (by rw [hidi]; exact hKi) n hnh hn1
    obtain ⟨e2, s2⟩ := hub_sound hrj hL (by rw [hidj]; exact hLj) n hnh hn2
    rw [h1] at e1 s1
    rw [h2] at e2 s2
    have e2' : ((BMC.rq w2.lam : ℚ) : ℝ) ≠ 0 := by exact_mod_cast e2.ne'
    have hprod := s1.trans (s2.symm e2')
    refine hprod.mono (by have : (0 : ℝ) < BMC.rq w1.lam := by exact_mod_cast e1
                          have : (0 : ℝ) < BMC.rq w2.lam := by exact_mod_cast e2
                          positivity) ?_ hL.1.2.1 hL.1.nonempty
    rw [rq_cast, rq_cast]
    have : (5 : ℝ) * (w1.lam * w2.lam) ≤ 11 * (10000000000 * 10000000000) := by
      simp only [BMC.den] at hle; exact_mod_cast hle
    rw [div_mul_div_comm, div_le_iff₀ (by norm_num)]
    linarith

lemma root_pair {i j : ℕ} (hi : i < BMC.reps.size) (hj : j < BMC.reps.size) {K L : Set P2}
    (hK : Normalized K) (hL : Normalized L) (hKi : Belongs K (BMC.rootCell i))
    (hLj : Belongs L (BMC.rootCell j)) : Sandwich K L (11 / 5) := by
  rcases le_total i j with hij | hji
  · exact root_pair_le hij hj hK hL hKi hLj
  · exact (root_pair_le hji hi hL hK hLj hKi).symm (by norm_num)

/-- **Main theorem.** Assuming Besicovitch's lemma, for all planar convex bodies K and L there are
an affine equivalence T and a vector b with T(L) ⊆ K ⊆ (11/5) T(L) + b, i.e. d_BM(K, L) ≤ 11/5. -/
theorem diam_le (hB : Besicovitch) (K L : Set P2) (hK : IsConvexBody K) (hL : IsConvexBody L) :
    ∃ (T : P2 ≃ᵃ[ℝ] P2) (b : P2), T '' L ⊆ K ∧ K ⊆ (fun x ↦ (11 / 5 : ℝ) • x + b) '' (T '' L) := by
  obtain ⟨A, hA⟩ := normalize hB hK
  obtain ⟨A', hA'⟩ := normalize hB hL
  obtain ⟨i, hi, g, hg, hgi⟩ := root_lemma hA
  obtain ⟨j, hj, g', hg', hgj⟩ := root_lemma hA'
  have h := (root_pair hi hj hg hg' hgi hgj).image (A.trans g).symm (A'.trans g').symm
  have e1 : (A.trans g).symm '' (g '' (A '' K)) = K := by
    rw [← image_comp, ← image_comp]
    convert image_id K using 2; exact (A.trans g).symm_apply_apply _
  have e2 : (A'.trans g').symm '' (g' '' (A' '' L)) = L := by
    rw [← image_comp, ← image_comp]
    convert image_id L using 2; exact (A'.trans g').symm_apply_apply _
  rw [e1, e2] at h
  exact h

end BM
