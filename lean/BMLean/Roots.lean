/-
Lemma 4.3 (roots): every normalised body is, after a symmetry of H₀, in one of the root cells of
the representatives. Uses `BMC.roots_ok` (native_decide).
-/
import BMLean.Geom
import BMLean.Run.Roots

namespace BM

open Set

/-! ### finite facts about the net -/

lemma net_pos : ∀ i : Fin 6, 0 < (BMC.net i).1 ∧ 0 < (BMC.net i).2 := by
  intro i; fin_cases i <;> simp [BMC.net]

lemma toR_net_pos (i : Fin 6) : 0 < (toR (BMC.net i)).1 ∧ 0 < (toR (BMC.net i)).2 := by
  simp only [toR]
  exact ⟨by exact_mod_cast (net_pos i).1, by exact_mod_cast (net_pos i).2⟩

lemma root_valid_cfg (cfg : BMC.Config) : BMC.cellValid (BMC.root cfg) = true := by
  simp only [BMC.cellValid, BMC.root, List.all_eq_true, List.mem_append, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq]
  rintro k - z (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) <;> exact net_pos i

lemma root_valid (i : ℕ) : BMC.cellValid (BMC.rootCell i) = true := root_valid_cfg _

/-- the reflection of the net: S ↔ T, U ↔ V -/
def swapI : Fin 6 → Fin 6
  | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | i => i

lemma net_swap : ∀ i : Fin 6, (BMC.net (swapI i)).2 = (BMC.net i).1 ∧
    (BMC.net (swapI i)).1 = (BMC.net i).2 := by
  intro i; fin_cases i <;> simp [BMC.net, swapI]

lemma net_swap_R (i : Fin 6) :
    ((toR (BMC.net (swapI i))).2, (toR (BMC.net (swapI i))).1) = toR (BMC.net i) := by
  simp only [toR, (net_swap i).1, (net_swap i).2]

lemma patch_swap : ∀ (p : Fin 9) (i : Fin 6),
    i ∈ BMC.patch (BMC.swapP p) ↔ swapI i ∈ BMC.patch p := by decide

/-! ### transport of slope points under the symmetries -/

lemma qR_mod_r (n : ℕ) (z : P2) : qR (n % 6) z = qR n z := by
  unfold qR; rw [rotR_iter_mod]

lemma rot_qR (j n : ℕ) (z : P2) : rotR^[j] (qR n z) = qR (n + j) z := by
  unfold qR; rw [← Function.iterate_add_apply, add_comm]

lemma sigR_rotR (x : P2) : sigR (rotR x) = rotR^[5] (sigR x) := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, rotR, sigR]
  ext <;> ring

lemma sigR_iter (n : ℕ) (x : P2) : sigR (rotR^[n] x) = rotR^[5 * n] (sigR x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, sigR_rotR, ← Function.iterate_add_apply,
      show 5 * (n + 1) = 5 * n + 5 by ring]

lemma sigR_qzR (z : P2) : sigR (qzR z) = qzR (z.2, z.1) := by
  simp only [sigR, qzR]
  refine Prod.ext ?_ ?_ <;> simp only [] <;> ring

lemma sigR_qR (n : ℕ) (z : P2) : sigR (qR n z) = qR (5 * n) (z.2, z.1) := by
  unfold qR; rw [sigR_iter, sigR_qzR]

lemma sigR_sigR (x : P2) : sigR (sigR x) = x := by simp [sigR]

lemma rot_inv (j : ℕ) (v : P2) : rotR^[j] (rotR^[5 * j] v) = v := by
  rw [← Function.iterate_add_apply, show j + 5 * j = 6 * j by ring, Function.iterate_mul,
    rotR_iter_six, Function.iterate_id, id]

/-! ### the configuration of a normalised body -/

def bit (K : Set P2) (k : ℕ) (i : Fin 6) : Prop := qR k (toR (BMC.net i)) ∈ K

def leNet (i j : Fin 6) : Bool :=
  decide ((BMC.net i).1 ≤ (BMC.net j).1) && decide ((BMC.net i).2 ≤ (BMC.net j).2)

def downB (b : Fin 6 → Bool) : Bool :=
  (List.finRange 6).all fun i => (List.finRange 6).all fun j => !(leNet i j && b j) || b i

lemma patch_exists : ∀ b : Fin 6 → Bool, downB b = true →
    ∃ p : Fin 9, ∀ i, (BMC.patch p).contains i = b i := by native_decide

lemma side_patch {K : Set P2} (hK : Normalized K) (k : ℕ) :
    ∃ p : Fin 9, ∀ i, (i ∈ BMC.patch p ↔ bit K k i) := by
  classical
  have hdown : downB (fun i => decide (bit K k i)) = true := by
    simp only [downB, List.all_eq_true]
    intro i _ j _
    by_cases hb : bit K k i
    · simp [hb]
    · by_cases hj : bit K k j
      · have hle : leNet i j = false := by
          by_contra hle
          simp only [leNet, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hle
          apply hb
          exact downset hK k (toR_net_pos i) (by simp only [toR]; exact_mod_cast hle.1)
            (by simp only [toR]; exact_mod_cast hle.2) hj
        simp [hle, hb]
      · simp [hb, hj]
  obtain ⟨p, hp⟩ := patch_exists (fun i => decide (bit K k i)) hdown
  refine ⟨p, fun i => ?_⟩
  rw [← List.contains_iff_mem, hp i, decide_eq_true_iff]

lemma exists_cfg {K : Set P2} (hK : Normalized K) :
    ∃ c : BMC.Config, ∀ (k : Fin 6) i, (i ∈ BMC.patch (c k) ↔ bit K k i) := by
  choose p hp using fun k : Fin 6 => side_patch hK k
  exact ⟨p, hp⟩

lemma cfg_admissible {K : Set P2} (hK : Normalized K) {c : BMC.Config}
    (hc : ∀ (k : Fin 6) i, (i ∈ BMC.patch (c k) ↔ bit K k i)) : BMC.admissible c = true := by
  simp only [BMC.admissible, List.all_eq_true, decide_eq_true_eq]
  intro k _ i hi j hj
  have h1 := (hc k i).1 hi
  have h2 := (hc (k + 1) j).1 hj
  have h2' : qR (k.val + 1) (toR (BMC.net j)) ∈ K := by
    unfold bit at h2
    rw [Fin.val_add, show ((1 : Fin 6) : ℕ) = 1 from rfl, qR_mod_r] at h2
    exact h2
  have := vertex hK k (toR_net_pos i) (toR_net_pos j) h1 h2'
  simp only [toR] at this
  exact_mod_cast this

lemma mem_allConfigs (c : BMC.Config) : c ∈ BMC.allConfigs := by
  simp only [BMC.allConfigs, List.mem_map, List.mem_range]
  have h0 := (c 0).isLt
  have h1 := (c 1).isLt
  have h2 := (c 2).isLt
  have h3 := (c 3).isLt
  have h4 := (c 4).isLt
  have h5 := (c 5).isLt
  refine ⟨(c 0).val * 59049 + (c 1).val * 6561 + (c 2).val * 729 + (c 3).val * 81 +
    (c 4).val * 9 + (c 5).val, by omega, ?_⟩
  funext k
  apply Fin.ext
  simp only [Fin.val_ofNat]
  fin_cases k <;> simp <;> omega

lemma roots_image (c : BMC.Config) (hc : BMC.admissible c = true) :
    ∃ (j : Fin 6) (f : Bool) (i : ℕ), i < BMC.reps.size ∧
      ∀ k, BMC.reps[i]! k = BMC.transform j f c k := by
  have h := BMC.roots_ok
  simp only [BMC.rootsOk, List.all_eq_true] at h
  have h' := h c (mem_allConfigs c)
  rw [hc] at h'
  simp only [Bool.not_true, Bool.false_or] at h'
  simp only [BMC.isRepImage, List.any_eq_true] at h'
  obtain ⟨j, -, f, -, hf⟩ := h'
  split at hf
  · rename_i i _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
    exact ⟨j, f, i, hf.1, fun k => hf.2 k (List.mem_finRange k)⟩
  · simp at hf

lemma belongs_root {L : Set P2} {d : BMC.Config}
    (h : ∀ (k : Fin 6) i, (qR k (toR (BMC.net i)) ∈ L ↔ i ∈ BMC.patch (d k))) :
    Belongs L (BMC.root d) := by
  intro k
  constructor
  · intro z hz
    simp only [BMC.root, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    exact (h k i).2 hi
  · intro z hz hm
    simp only [BMC.root, List.mem_map, List.mem_filter] at hz
    obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hz
    have := (h k i).1 hm
    simp [this] at hi

theorem root_lemma {K : Set P2} (hK : Normalized K) :
    ∃ i < BMC.reps.size, ∃ g : P2 ≃ᵃ[ℝ] P2, Normalized (g '' K) ∧ Belongs (g '' K) (BMC.rootCell i) := by
  obtain ⟨c, hc⟩ := exists_cfg hK
  obtain ⟨j, f, i, hi, hk⟩ := roots_image c (cfg_admissible hK hc)
  have hd : BMC.reps[i]! = BMC.transform j f c := funext hk
  refine ⟨i, hi, ?_⟩
  show ∃ g : P2 ≃ᵃ[ℝ] P2, Normalized (g '' K) ∧ Belongs (g '' K) (BMC.root BMC.reps[i]!)
  rw [hd]
  cases f with
  | false =>
    refine ⟨rotIter j, ?_, ?_⟩
    · refine hK.image _ fun v hv => ?_
      have : (rotIter j).symm v = rotR^[5 * j] v := by
        rw [AffineEquiv.symm_apply_eq, rotIter_coe, rot_inv]
      rw [this]; exact rotR_iter_hex _ hv
    · refine belongs_root fun k i => ?_
      have hidx : ((k - j : Fin 6).val + j.val) % 6 = k.val := by
        rw [← Fin.val_add, sub_add_cancel]
      have e : qR k (toR (BMC.net i)) = rotIter j (qR (k - j : Fin 6) (toR (BMC.net i))) := by
        rw [rotIter_coe, rot_qR, ← qR_mod_r ((k - j : Fin 6).val + j.val), hidx]
      rw [e, (rotIter j).injective.mem_set_image]
      simp only [BMC.transform]
      exact (hc (k - j) i).symm
  | true =>
    have hg : ∀ x, (sigE.trans (rotIter j)) x = rotR^[j] (sigR x) := by
      intro x; simp [rotIter_coe, sigE_coe]
    refine ⟨sigE.trans (rotIter j), ?_, ?_⟩
    · refine hK.image _ fun v hv => ?_
      have : (sigE.trans (rotIter j)).symm v = sigR (rotR^[5 * j] v) := by
        rw [AffineEquiv.symm_apply_eq, hg, sigR_sigR, rot_inv]
      rw [this]; exact sigR_hex (rotR_iter_hex _ hv)
    · refine belongs_root fun k i => ?_
      have h0 : ((j - k : Fin 6).val + k.val) % 6 = j.val := by
        rw [← Fin.val_add, sub_add_cancel]
      have hidx : (5 * (j - k : Fin 6).val + j.val) % 6 = k.val := by
        have := (j - k).isLt; have := k.isLt; have := j.isLt
        omega
      have e : qR k (toR (BMC.net i)) =
          (sigE.trans (rotIter j)) (qR (j - k : Fin 6) (toR (BMC.net (swapI i)))) := by
        rw [hg, sigR_qR, net_swap_R, rot_qR, ← qR_mod_r (5 * (j - k : Fin 6).val + j.val), hidx]
      rw [e, (sigE.trans (rotIter j)).injective.mem_set_image]
      simp only [BMC.transform, ite_true, patch_swap]
      exact (hc (j - k) (swapI i)).symm

end BM
