/-
Besicovitch, part 1: one-dimensional lemmas on a concave, continuous, nonnegative function
`w` on `[m, M]` (the chord-width function of a convex body in a fixed direction).
`HexLev w m M r t1 t2`: levels of Besicovitch's hexagon (top/bottom chords of length `r` at
`t1 < t2`, middle chord of length `2r` at `(t1+t2)/2`).
-/
import Mathlib

namespace BM.Besi

open Set Filter Topology

/-- three-point concavity, multiplied out -/
lemma concave3 {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {x y z : ℝ} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
    (z - y) * f x + (y - x) * f z ≤ (z - x) * f y := by
  have hzx : 0 < z - x := by linarith
  have ha : (0:ℝ) ≤ (z - y) / (z - x) := div_nonneg (by linarith) hzx.le
  have hb : (0:ℝ) ≤ (y - x) / (z - x) := div_nonneg (by linarith) hzx.le
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
  have h := hf.2 hx hz ha hb hab
  have hy : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp; ring
  simp only [smul_eq_mul, hy] at h
  have := mul_le_mul_of_nonneg_left h hzx.le
  calc (z - y) * f x + (y - x) * f z
      = (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) := by
        field_simp
    _ ≤ (z - x) * f y := this

/-- slope comparison for concave functions -/
lemma concave_slope {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {x1 y1 x2 y2 : ℝ}
    (hx1 : x1 ∈ s) (_hy1 : y1 ∈ s) (hx2 : x2 ∈ s) (hy2 : y2 ∈ s) (h1 : x1 < y1) (h2 : x2 < y2)
    (hx : x1 ≤ x2) (hy : y1 ≤ y2) :
    (f y2 - f x2) * (y1 - x1) ≤ (f y1 - f x1) * (y2 - x2) := by
  -- A: slope(x1,y2) ≤ slope(x1,y1)
  have A : (f y2 - f x1) * (y1 - x1) ≤ (f y1 - f x1) * (y2 - x1) := by
    rcases hy.lt_or_eq with hy | hy
    · have := concave3 hf hx1 hy2 h1 hy
      nlinarith
    · subst hy; nlinarith
  -- B: slope(x2,y2) ≤ slope(x1,y2)
  have B : (f y2 - f x2) * (y2 - x1) ≤ (f y2 - f x1) * (y2 - x2) := by
    rcases hx.lt_or_eq with hx | hx
    · have := concave3 hf hx1 hy2 hx h2
      nlinarith
    · subst hx; nlinarith
  have p1 : 0 < y1 - x1 := by linarith
  have p2 : 0 < y2 - x2 := by linarith
  have p3 : 0 < y2 - x1 := by linarith
  have := mul_le_mul_of_nonneg_left B p1.le
  have := mul_le_mul_of_nonneg_left A p2.le
  have key : (y2 - x1) * ((f y2 - f x2) * (y1 - x1)) ≤ (y2 - x1) * ((f y1 - f x1) * (y2 - x2)) := by
    nlinarith
  exact le_of_mul_le_mul_left key p3


lemma concave_lower {a b : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc a b) f) {t t' : ℝ}
    (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) :
    f t - (|f b - f t| / (b - t) + |f a - f t| / (t - a)) * |t' - t| ≤ f t' := by
  have hb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hA : 0 ≤ |f b - f t| / (b - t) := div_nonneg (abs_nonneg _) (by linarith [ht.2])
  have hB : 0 ≤ |f a - f t| / (t - a) := div_nonneg (abs_nonneg _) (by linarith [ht.1])
  rcases lt_trichotomy t' t with h | h | h
  · -- t' < t
    have hta : 0 < t - a := by linarith [ht'.1]
    have key : f t - |f a - f t| / (t - a) * (t - t') ≤ f t' := by
      rcases ht'.1.lt_or_eq with h' | h'
      · have c3 := concave3 hf ha ht h' h
        have e : |f a - f t| / (t - a) * (t - t') * (t - a) = |f a - f t| * (t - t') := by
          field_simp
        have := neg_abs_le (f a - f t)
        have : (f t - |f a - f t| / (t - a) * (t - t')) * (t - a) ≤ f t' * (t - a) := by
          nlinarith
        exact le_of_mul_le_mul_right this hta
      · subst h'
        have e : |f a - f t| / (t - a) * (t - a) = |f a - f t| := by field_simp
        rw [e]; linarith [neg_abs_le (f a - f t), le_abs_self (f a - f t)]
    have : |t' - t| = t - t' := by rw [abs_of_neg (by linarith)]; ring
    rw [this]
    nlinarith [mul_nonneg hA (by linarith : (0:ℝ) ≤ t - t')]
  · subst h; simp
  · -- t < t'
    have htb : 0 < b - t := by linarith [ht'.2]
    have key : f t - |f b - f t| / (b - t) * (t' - t) ≤ f t' := by
      rcases ht'.2.lt_or_eq with h' | h'
      · have c3 := concave3 hf ht hb h h'
        have e : |f b - f t| / (b - t) * (t' - t) * (b - t) = |f b - f t| * (t' - t) := by
          field_simp
        have := neg_abs_le (f b - f t)
        have : (f t - |f b - f t| / (b - t) * (t' - t)) * (b - t) ≤ f t' * (b - t) := by
          nlinarith
        exact le_of_mul_le_mul_right this htb
      · subst h'
        have e : |f t' - f t| / (t' - t) * (t' - t) = |f t' - f t| := by field_simp
        rw [e]; linarith [neg_abs_le (f t' - f t), le_abs_self (f t' - f t)]
    have : |t' - t| = t' - t := abs_of_pos (by linarith)
    rw [this]
    nlinarith [mul_nonneg hB (by linarith : (0:ℝ) ≤ t' - t)]

lemma concave_lsc {a b : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc a b) f) {t : ℝ}
    (ht : t ∈ Icc a b) : ∀ y < f t, ∀ᶠ t' in 𝓝[Icc a b] t, y < f t' := by
  intro y hy
  set C := |f b - f t| / (b - t) + |f a - f t| / (t - a) with hC
  have hC0 : 0 ≤ C := add_nonneg (div_nonneg (abs_nonneg _) (by linarith [ht.2]))
    (div_nonneg (abs_nonneg _) (by linarith [ht.1]))
  rw [eventually_nhdsWithin_iff]
  have hε : 0 < (f t - y) / (C + 1) := div_pos (by linarith) (by linarith)
  filter_upwards [Metric.ball_mem_nhds t hε] with t' ht' hmem
  have hl := concave_lower hf ht hmem
  rw [← hC] at hl
  have hd : |t' - t| < (f t - y) / (C + 1) := by
    simpa [Metric.mem_ball, Real.dist_eq] using ht'
  have : C * |t' - t| ≤ C * ((f t - y) / (C + 1)) := mul_le_mul_of_nonneg_left hd.le hC0
  have h2 : C * ((f t - y) / (C + 1)) < f t - y := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith


/-- the levels of Besicovitch's hexagon -/
def HexLev (w : ℝ → ℝ) (m M r t1 t2 : ℝ) : Prop :=
  m ≤ t1 ∧ t1 < t2 ∧ t2 ≤ M ∧ 0 < r ∧ r ≤ w t1 ∧ r ≤ w t2 ∧ (t1 = m ∨ w t1 = r) ∧
    (t2 = M ∨ w t2 = r) ∧ w ((t1 + t2) / 2) = 2 * r

variable {w : ℝ → ℝ} {m M : ℝ}

lemma hexLev_step1 (hw : ConcaveOn ℝ (Icc m M) w) {r t1 t2 r' s1 s2 : ℝ}
    (h : HexLev w m M r t1 t2) (h' : HexLev w m M r' s1 s2) (hr : r ≤ r') :
    t1 ≤ s1 ∧ s2 ≤ t2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h'
  have hmid : (t1 + t2) / 2 ∈ Icc m M := ⟨by linarith, by linarith⟩
  constructor
  · by_contra hc
    push Not at hc
    have e : w t1 = r := by
      rcases a7 with e | e
      · exact absurd e (by linarith)
      · exact e
    have c3 := concave3 hw ⟨b1, by linarith⟩ hmid hc (by linarith)
    rw [e, a9] at c3
    have : ((t1 + t2) / 2 - t1) * r ≤ ((t1 + t2) / 2 - t1) * w s1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_pos (by linarith : (0:ℝ) < t1 - s1) a4]
  · by_contra hc
    push Not at hc
    have e : w t2 = r := by
      rcases a8 with e | e
      · exact absurd e (by linarith)
      · exact e
    have c3 := concave3 hw hmid ⟨by linarith, b3⟩ (by linarith) hc
    rw [e, a9] at c3
    have : (t2 - (t1 + t2) / 2) * r ≤ (t2 - (t1 + t2) / 2) * w s2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_pos (by linarith : (0:ℝ) < s2 - t2) a4]

lemma hexLev_step2 (hw : ConcaveOn ℝ (Icc m M) w) {r t1 t2 r' s1 s2 : ℝ}
    (h : HexLev w m M r t1 t2) (h' : HexLev w m M r' s1 s2) (hr : r ≤ r') : r' ≤ r := by
  obtain ⟨l1, l2⟩ := hexLev_step1 hw h h' hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h'
  have hmid : (t1 + t2) / 2 ∈ Icc m M := ⟨by linarith, by linarith⟩
  have hmid' : (s1 + s2) / 2 ∈ Icc m M := ⟨by linarith, by linarith⟩
  set mid := (t1 + t2) / 2
  set mid' := (s1 + s2) / 2
  rcases le_or_gt (s1 - t1) (t2 - s2) with hc | hc
  · rcases (show mid' ≤ mid by simp only [mid, mid']; linarith).lt_or_eq with hm | hm
    · have hs2 : s2 < t2 := by simp only [mid, mid'] at hm; linarith
      have e : w s2 = r' := by
        rcases b8 with e | e
        · exact absurd e (by linarith)
        · exact e
      have sl := concave_slope hw hmid' hmid ⟨by linarith, b3⟩ ⟨by linarith, a3⟩ hm hs2
        (by simp only [mid']; linarith) (by simp only [mid]; linarith)
      rw [e, a9, b9] at sl
      have : (r - r') * (mid - mid') ≤ (w t2 - r') * (mid - mid') :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      by_contra hcon
      push Not at hcon
      have hd : mid - mid' ≤ (t2 - s2) / 2 := by simp only [mid, mid']; linarith
      nlinarith [mul_pos (by linarith : (0:ℝ) < r' - r) (by linarith : (0:ℝ) < t2 - s2),
        mul_le_mul_of_nonneg_left hd (by linarith : (0:ℝ) ≤ r' - r)]
    · rw [hm] at b9; linarith
  · have hs1 : t1 < s1 := by linarith
    have e : w s1 = r' := by
      rcases b7 with e | e
      · exact absurd e (by linarith)
      · exact e
    have hm : mid < mid' := by simp only [mid, mid']; linarith
    have sl := concave_slope hw ⟨a1, by linarith⟩ ⟨by linarith, by linarith⟩ hmid hmid' hs1 hm
      (by simp only [mid]; linarith) (by simp only [mid']; linarith)
    rw [e, a9, b9] at sl
    have : (r' - w t1) * (mid' - mid) ≤ (r' - r) * (mid' - mid) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    by_contra hcon
    push Not at hcon
    have hd : mid' - mid ≤ (s1 - t1) / 2 := by simp only [mid, mid']; linarith
    nlinarith [mul_pos (by linarith : (0:ℝ) < r' - r) (by linarith : (0:ℝ) < s1 - t1),
      mul_le_mul_of_nonneg_left hd (by linarith : (0:ℝ) ≤ r' - r)]

lemma hexLev_unique (hw : ConcaveOn ℝ (Icc m M) w) {r t1 t2 r' s1 s2 : ℝ}
    (h : HexLev w m M r t1 t2) (h' : HexLev w m M r' s1 s2) : r = r' ∧ t1 = s1 ∧ t2 = s2 := by
  have hrr : r = r' := by
    rcases le_total r r' with hr | hr
    · exact le_antisymm hr (hexLev_step2 hw h h' hr)
    · exact le_antisymm (hexLev_step2 hw h' h hr) hr
  obtain ⟨u1, u2⟩ := hexLev_step1 hw h h' hrr.le
  obtain ⟨v1, v2⟩ := hexLev_step1 hw h' h hrr.ge
  exact ⟨hrr, le_antisymm u1 v1, le_antisymm v2 u2⟩


/-- beyond the top level the width is controlled -/
lemma hexLev_above (hw : ConcaveOn ℝ (Icc m M) w) {r t1 t2 : ℝ}
    (h : HexLev w m M r t1 t2) {t : ℝ} (ht : t ∈ Icc m M) (htt : t2 < t) :
    (t2 - t1) / 2 * w t ≤ r * (2 * t2 - (t1 + t2) / 2 - t) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  have e : w t2 = r := by
    rcases a8 with e | e
    · exact absurd e (by linarith [ht.2])
    · exact e
  have c3 := concave3 hw ⟨by linarith, by linarith⟩ ht (by linarith : (t1 + t2) / 2 < t2) htt
  rw [e, a9] at c3
  nlinarith

lemma hexLev_below (hw : ConcaveOn ℝ (Icc m M) w) {r t1 t2 : ℝ}
    (h : HexLev w m M r t1 t2) {t : ℝ} (ht : t ∈ Icc m M) (htt : t < t1) :
    (t2 - t1) / 2 * w t ≤ r * (t - 2 * t1 + (t1 + t2) / 2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  have e : w t1 = r := by
    rcases a7 with e | e
    · exact absurd e (by linarith [ht.1])
    · exact e
  have c3 := concave3 hw ht ⟨by linarith, by linarith⟩ htt (by linarith : t1 < (t1 + t2) / 2)
  rw [e, a9] at c3
  nlinarith

lemma hexLev_bound (hw : ConcaveOn ℝ (Icc m M) w) (hw0 : ∀ t ∈ Icc m M, 0 ≤ w t)
    {r t1 t2 : ℝ} (h : HexLev w m M r t1 t2) :
    (∀ t ∈ Icc m M, w t ≤ 4 * r) ∧ M - m ≤ 2 * (t2 - t1) := by
  have hab := fun {t} => hexLev_above hw h (t := t)
  have hbe := fun {t} => hexLev_below hw h (t := t)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  have hmid : (t1 + t2) / 2 ∈ Icc m M := ⟨by linarith, by linarith⟩
  have h1m : t1 ∈ Icc m M := ⟨a1, by linarith⟩
  have h2m : t2 ∈ Icc m M := ⟨by linarith, a3⟩
  constructor
  · intro t ht
    rcases lt_or_ge t2 t with h1 | h1
    · have := hab ht h1
      nlinarith [hw0 t ht]
    rcases lt_or_ge t t1 with h2 | h2
    · have := hbe ht h2
      nlinarith [hw0 t ht]
    rcases lt_trichotomy t ((t1 + t2) / 2) with h3 | h3 | h3
    · have c3 := concave3 hw ht h2m h3 (by linarith)
      rw [a9] at c3
      nlinarith [hw0 t2 h2m]
    · rw [h3, a9]; linarith
    · have c3 := concave3 hw h1m ht (by linarith) h3
      rw [a9] at c3
      nlinarith [hw0 t1 h1m]
  · have hM : M ≤ 2 * t2 - (t1 + t2) / 2 := by
      rcases lt_or_ge t2 M with h1 | h1
      · have := hab ⟨by linarith, le_rfl⟩ h1
        by_contra hc
        push Not at hc
        nlinarith [hw0 M ⟨by linarith, le_rfl⟩]
      · linarith
    have hm : 2 * t1 - (t1 + t2) / 2 ≤ m := by
      rcases lt_or_ge m t1 with h1 | h1
      · have := hbe ⟨le_rfl, by linarith⟩ h1
        by_contra hc
        push Not at hc
        nlinarith [hw0 m ⟨le_rfl, by linarith⟩]
      · linarith
    linarith


lemma sup_level (hwc : ContinuousOn w (Icc m M)) {s0 r : ℝ} (hs0 : s0 ∈ Icc m M)
    (hr : r ≤ w s0) : ∃ t2 ∈ Icc s0 M, r ≤ w t2 ∧ (t2 = M ∨ w t2 ≤ r) := by
  set T := Icc s0 M ∩ w ⁻¹' Ici r with hT
  have hTc : IsClosed T :=
    (hwc.mono (Icc_subset_Icc_left hs0.1)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hTk : IsCompact T := isCompact_Icc.of_isClosed_subset hTc inter_subset_left
  have hTn : T.Nonempty := ⟨s0, ⟨le_rfl, hs0.2⟩, hr⟩
  have hmem := hTk.sSup_mem hTn
  refine ⟨sSup T, hmem.1, hmem.2, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hne, hlt⟩ := hc
  have hlt2 : sSup T < M := lt_of_le_of_ne hmem.1.2 hne
  have hcont := hwc (sSup T) ⟨hs0.1.trans hmem.1.1, hmem.1.2⟩
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (w (sSup T) - r) (by linarith)
  set t := min (sSup T + δ / 2) M
  have ht1 : sSup T < t := lt_min (by linarith) hlt2
  have htM : t ≤ M := min_le_right _ _
  have hd : dist t (sSup T) < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    have : t ≤ sSup T + δ / 2 := min_le_left _ _
    linarith
  have h1 := hδ' ⟨by linarith [hs0.1, hmem.1.1], htM⟩ hd
  rw [Real.dist_eq] at h1
  have hwt : r ≤ w t := by linarith [neg_abs_le (w t - w (sSup T))]
  have h2 : t ∈ T := ⟨⟨by linarith [hmem.1.1], htM⟩, hwt⟩
  have := le_csSup hTk.bddAbove h2
  linarith

lemma inf_level (hwc : ContinuousOn w (Icc m M)) {s0 r : ℝ} (hs0 : s0 ∈ Icc m M)
    (hr : r ≤ w s0) : ∃ t1 ∈ Icc m s0, r ≤ w t1 ∧ (t1 = m ∨ w t1 ≤ r) := by
  set T := Icc m s0 ∩ w ⁻¹' Ici r with hT
  have hTc : IsClosed T :=
    (hwc.mono (Icc_subset_Icc_right hs0.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hTk : IsCompact T := isCompact_Icc.of_isClosed_subset hTc inter_subset_left
  have hTn : T.Nonempty := ⟨s0, ⟨hs0.1, le_rfl⟩, hr⟩
  have hmem := hTk.sInf_mem hTn
  refine ⟨sInf T, hmem.1, hmem.2, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hne, hlt⟩ := hc
  have hlt2 : m < sInf T := lt_of_le_of_ne hmem.1.1 (Ne.symm hne)
  have hcont := hwc (sInf T) ⟨hmem.1.1, hmem.1.2.trans hs0.2⟩
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (w (sInf T) - r) (by linarith)
  set t := max (sInf T - δ / 2) m
  have ht1 : t < sInf T := max_lt (by linarith) hlt2
  have htm : m ≤ t := le_max_right _ _
  have hd : dist t (sInf T) < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : sInf T - δ / 2 ≤ t := le_max_left _ _
    linarith
  have h1 := hδ' ⟨htm, by linarith [hs0.2, hmem.1.2]⟩ hd
  rw [Real.dist_eq] at h1
  have hwt : r ≤ w t := by linarith [neg_abs_le (w t - w (sInf T))]
  have h2 : t ∈ T := ⟨⟨htm, by linarith [hmem.1.2]⟩, hwt⟩
  have := csInf_le hTk.bddBelow h2
  linarith

lemma top_level_unique (hw : ConcaveOn ℝ (Icc m M) w) {s0 r t t' : ℝ} (hs0 : s0 ∈ Icc m M)
    (hrD : r < w s0) (ht : t ∈ Icc s0 M) (ht' : t' ∈ Icc s0 M) (h1 : r ≤ w t)
    (h1' : r ≤ w t') (h2 : t = M ∨ w t ≤ r) (h2' : t' = M ∨ w t' ≤ r) : t = t' := by
  have aux : ∀ t t', t ∈ Icc s0 M → t' ∈ Icc s0 M → r ≤ w t' → (t = M ∨ w t ≤ r) →
      t < t' → False := by
    intro t t' ht ht' h1' h2 hlt
    have hwt : w t ≤ r := by
      rcases h2 with e | e
      · exact absurd e (by linarith [ht'.2])
      · exact e
    rcases ht.1.lt_or_eq with hs | hs
    · have c3 := concave3 hw hs0 ⟨by linarith [hs0.1, ht'.1], ht'.2⟩ hs hlt
      nlinarith [mul_pos (by linarith : (0:ℝ) < t' - t) (by linarith : (0:ℝ) < w s0 - r)]
    · rw [← hs] at hwt; linarith
  rcases lt_trichotomy t t' with h | h | h
  · exact (aux t t' ht ht' h1' h2 h).elim
  · exact h
  · exact (aux t' t ht' ht h1 h2' h).elim

lemma bot_level_unique (hw : ConcaveOn ℝ (Icc m M) w) {s0 r t t' : ℝ} (hs0 : s0 ∈ Icc m M)
    (hrD : r < w s0) (ht : t ∈ Icc m s0) (ht' : t' ∈ Icc m s0) (h1 : r ≤ w t)
    (h1' : r ≤ w t') (h2 : t = m ∨ w t ≤ r) (h2' : t' = m ∨ w t' ≤ r) : t = t' := by
  have aux : ∀ t t', t ∈ Icc m s0 → t' ∈ Icc m s0 → r ≤ w t' → (t = m ∨ w t ≤ r) →
      t' < t → False := by
    intro t t' ht ht' h1' h2 hlt
    have hwt : w t ≤ r := by
      rcases h2 with e | e
      · exact absurd e (by linarith [ht'.1])
      · exact e
    rcases ht.2.lt_or_eq with hs | hs
    · have c3 := concave3 hw ⟨ht'.1, by linarith [hs0.2, ht'.2]⟩ hs0 hlt hs
      nlinarith [mul_pos (by linarith : (0:ℝ) < t - t') (by linarith : (0:ℝ) < w s0 - r)]
    · rw [hs] at hwt; linarith
  rcases lt_trichotomy t t' with h | h | h
  · exact (aux t' t ht' ht h1 h2' h).elim
  · exact h
  · exact (aux t t' ht ht' h1' h2 h).elim

lemma pos_of_interior (hw : ConcaveOn ℝ (Icc m M) w) (hw0 : ∀ t ∈ Icc m M, 0 ≤ w t)
    {s0 : ℝ} (hs0 : s0 ∈ Icc m M) (hD : 0 < w s0) {t : ℝ} (ht : t ∈ Ioo m M) : 0 < w t := by
  rcases lt_trichotomy t s0 with h | h | h
  · have c3 := concave3 hw ⟨le_rfl, by linarith [ht.1, ht.2]⟩ hs0 ht.1 h
    have := hw0 m ⟨le_rfl, by linarith [ht.1, ht.2]⟩
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (by linarith [ht.1] : (0:ℝ) < t - m) hD,
      mul_nonneg (by linarith : (0:ℝ) ≤ s0 - t) this,
      mul_nonneg (by linarith [ht.1] : (0:ℝ) ≤ s0 - m) (by linarith : (0:ℝ) ≤ -w t)]
  · rw [h]; exact hD
  · have c3 := concave3 hw hs0 ⟨by linarith [ht.1, ht.2], le_rfl⟩ h ht.2
    have := hw0 M ⟨by linarith [ht.1, ht.2], le_rfl⟩
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (by linarith [ht.2] : (0:ℝ) < M - t) hD,
      mul_nonneg (by linarith : (0:ℝ) ≤ t - s0) this,
      mul_nonneg (by linarith [ht.2] : (0:ℝ) ≤ M - s0) (by linarith : (0:ℝ) ≤ -w t)]

lemma closed_le {α : Type*} [TopologicalSpace α] {Q : Set α} (hQ : IsClosed Q) {f g : α → ℝ}
    (hf : ContinuousOn f Q) (hg : ContinuousOn g Q) : IsClosed (Q ∩ {q | f q ≤ g q}) := by
  have := (hg.sub hf).preimage_isClosed_of_isClosed hQ (isClosed_Ici (a := (0:ℝ)))
  convert this using 1
  ext q; simp [sub_nonneg]


lemma hexLev_exists (hw : ConcaveOn ℝ (Icc m M) w) (hwc : ContinuousOn w (Icc m M))
    (hw0 : ∀ t ∈ Icc m M, 0 ≤ w t) (hmM : m < M) (hpos : ∃ t ∈ Icc m M, 0 < w t) :
    ∃ r t1 t2, HexLev w m M r t1 t2 := by
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hmM.le) hwc
  set D := w s0 with hDdef
  have hD : 0 < D := by
    obtain ⟨t, ht, hp⟩ := hpos
    exact hp.trans_le (hmax ht)
  have hle : ∀ t ∈ Icc m M, w t ≤ D := fun t ht => hmax ht
  -- the compact parameter box
  set Q : Set (ℝ × ℝ × ℝ) := Icc 0 (D / 2) ×ˢ (Icc m s0 ×ˢ Icc s0 M) with hQ
  have hQk : IsCompact Q := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hQc : IsClosed Q := hQk.isClosed
  have hQ1 : ∀ q ∈ Q, q.2.1 ∈ Icc m M := fun q hq => ⟨hq.2.1.1, hq.2.1.2.trans hs0.2⟩
  have hQ2 : ∀ q ∈ Q, q.2.2 ∈ Icc m M := fun q hq => ⟨hs0.1.trans hq.2.2.1, hq.2.2.2⟩
  have hQ3 : ∀ q ∈ Q, (q.2.1 + q.2.2) / 2 ∈ Icc m M := fun q hq =>
    ⟨by linarith [(hQ1 q hq).1, (hQ2 q hq).1], by linarith [(hQ1 q hq).2, (hQ2 q hq).2]⟩
  have g1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => w q.2.1) Q :=
    hwc.comp (continuous_fst.comp continuous_snd).continuousOn hQ1
  have g2 : ContinuousOn (fun q : ℝ × ℝ × ℝ => w q.2.2) Q :=
    hwc.comp (continuous_snd.comp continuous_snd).continuousOn hQ2
  have g3 : ContinuousOn (fun q : ℝ × ℝ × ℝ => w ((q.2.1 + q.2.2) / 2)) Q :=
    hwc.comp (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ => (q.2.1 + q.2.2) / 2).continuousOn
      hQ3
  have g0 : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.1) Q := continuous_fst.continuousOn
  have g0' : ContinuousOn (fun q : ℝ × ℝ × ℝ => 2 * q.1) Q := by fun_prop
  set C : Set (ℝ × ℝ × ℝ) := (Q ∩ {q | q.1 ≤ w q.2.1}) ∩ (Q ∩ {q | q.1 ≤ w q.2.2}) ∩
    ((Q ∩ {q | q.2.1 = m}) ∪ (Q ∩ {q | w q.2.1 ≤ q.1})) ∩
    ((Q ∩ {q | q.2.2 = M}) ∪ (Q ∩ {q | w q.2.2 ≤ q.1})) with hC
  have hCc : IsClosed C := by
    refine ((closed_le hQc g0 g1).inter (closed_le hQc g0 g2)).inter ?_ |>.inter ?_
    · exact (hQc.inter (isClosed_eq (continuous_fst.comp continuous_snd) continuous_const)).union
        (closed_le hQc g1 g0)
    · exact (hQc.inter (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)).union
        (closed_le hQc g2 g0)
  set SA := C ∩ (Q ∩ {q | 2 * q.1 ≤ w ((q.2.1 + q.2.2) / 2)}) with hSA
  set SB := C ∩ (Q ∩ {q | w ((q.2.1 + q.2.2) / 2) ≤ 2 * q.1}) with hSB
  have hCQ : C ⊆ Q := fun q hq => hq.1.1.1.1
  have hSAk : IsCompact SA :=
    hQk.of_isClosed_subset (hCc.inter (closed_le hQc g0' g3)) (inter_subset_left.trans hCQ)
  have hSBk : IsCompact SB :=
    hQk.of_isClosed_subset (hCc.inter (closed_le hQc g3 g0')) (inter_subset_left.trans hCQ)
  set A := Prod.fst '' SA
  set B := Prod.fst '' SB
  have hA : IsClosed A := (hSAk.image continuous_fst).isClosed
  have hB : IsClosed B := (hSBk.image continuous_fst).isClosed
  -- levels exist for every r
  have hlev : ∀ r ∈ Icc 0 (D / 2), ∃ t1 t2, (r, t1, t2) ∈ C := by
    intro r hr
    have hrD : r ≤ w s0 := by linarith [hr.2]
    obtain ⟨t1, ht1, a1, a2⟩ := inf_level hwc hs0 hrD
    obtain ⟨t2, ht2, b1, b2⟩ := sup_level hwc hs0 hrD
    have hq : (r, t1, t2) ∈ Q := ⟨hr, ht1, ht2⟩
    refine ⟨t1, t2, ⟨⟨⟨hq, a1⟩, ⟨hq, b1⟩⟩, ?_⟩, ?_⟩
    · rcases a2 with e | e
      · exact Or.inl ⟨hq, e⟩
      · exact Or.inr ⟨hq, e⟩
    · rcases b2 with e | e
      · exact Or.inl ⟨hq, e⟩
      · exact Or.inr ⟨hq, e⟩
  have hcover : Icc 0 (D / 2) ⊆ A ∪ B := by
    intro r hr
    obtain ⟨t1, t2, hc⟩ := hlev r hr
    rcases le_total (2 * r) (w ((t1 + t2) / 2)) with h | h
    · exact Or.inl ⟨(r, t1, t2), ⟨hc, hCQ hc, h⟩, rfl⟩
    · exact Or.inr ⟨(r, t1, t2), ⟨hc, hCQ hc, h⟩, rfl⟩
  have h0 : (0 : ℝ) ∈ Icc 0 (D / 2) := ⟨le_rfl, by linarith⟩
  have hD2 : D / 2 ∈ Icc 0 (D / 2) := ⟨by linarith, le_rfl⟩
  have hAne : (Icc 0 (D / 2) ∩ A).Nonempty := by
    obtain ⟨t1, t2, hc⟩ := hlev 0 h0
    refine ⟨0, h0, (0, t1, t2), ⟨hc, hCQ hc, ?_⟩, rfl⟩
    simpa using hw0 _ (hQ3 _ (hCQ hc))
  have hBne : (Icc 0 (D / 2) ∩ B).Nonempty := by
    obtain ⟨t1, t2, hc⟩ := hlev (D / 2) hD2
    refine ⟨D / 2, hD2, (D / 2, t1, t2), ⟨hc, hCQ hc, ?_⟩, rfl⟩
    have := hle _ (hQ3 _ (hCQ hc))
    simp only [mem_ofPred_eq]; linarith
  obtain ⟨r, hr, ⟨⟨r1, t1, t2⟩, ⟨hcA, -, hA'⟩, e1⟩, ⟨⟨r2, t1', t2'⟩, ⟨hcB, -, hB'⟩, e2⟩⟩ :=
    isPreconnected_closed_iff.1 isPreconnected_Icc A B hA hB hcover hAne hBne
  simp only at e1 e2
  subst e1 e2
  obtain ⟨⟨⟨⟨hq, a1⟩, ⟨-, b1⟩⟩, c1⟩, d1⟩ := hcA
  obtain ⟨⟨⟨⟨hq', a1'⟩, ⟨-, b1'⟩⟩, c1'⟩, d1'⟩ := hcB
  simp only [mem_inter_iff, mem_ofPred_eq, mem_union] at a1 b1 c1 d1 a1' b1' c1' d1' hA' hB'
  have c1 : t1 = m ∨ w t1 ≤ r2 := by rcases c1 with e | e; exacts [Or.inl e.2, Or.inr e.2]
  have d1 : t2 = M ∨ w t2 ≤ r2 := by rcases d1 with e | e; exacts [Or.inl e.2, Or.inr e.2]
  have c1' : t1' = m ∨ w t1' ≤ r2 := by rcases c1' with e | e; exacts [Or.inl e.2, Or.inr e.2]
  have d1' : t2' = M ∨ w t2' ≤ r2 := by rcases d1' with e | e; exacts [Or.inl e.2, Or.inr e.2]
  obtain ⟨hr0, ht1, ht2⟩ := hq
  obtain ⟨-, ht1', ht2'⟩ := hq'
  simp only at hr0 ht1 ht2 ht1' ht2'
  have hrD : r2 < w s0 := by linarith [hr0.2]
  have u1 := bot_level_unique hw hs0 hrD ht1 ht1' a1 a1' c1 c1'
  have u2 := top_level_unique hw hs0 hrD ht2 ht2' b1 b1' d1 d1'
  subst u1 u2
  have hmid : w ((t1 + t2) / 2) = 2 * r2 := le_antisymm hB' hA'
  -- t1 < t2
  have hlt : t1 < t2 := by
    rcases (ht1.2.trans ht2.1).lt_or_eq with h | h
    · exact h
    · exfalso
      have e1 : t1 = s0 := le_antisymm ht1.2 (h ▸ ht2.1)
      have e2 : t2 = s0 := le_antisymm (h ▸ ht1.2) ht2.1
      have hm : t1 = m := by
        rcases c1 with e | e
        · exact e
        · rw [e1] at e; linarith
      have hM : t2 = M := by
        rcases d1 with e | e
        · exact e
        · rw [e2] at e; linarith
      linarith
  have hpos' : 0 < w ((t1 + t2) / 2) :=
    pos_of_interior hw hw0 hs0 hD ⟨by linarith [ht1.1], by linarith [ht2.2]⟩
  refine ⟨r2, t1, t2, ht1.1, hlt, ht2.2, by linarith, a1, b1, ?_, ?_, hmid⟩
  · rcases c1 with e | e
    · exact Or.inl e
    · exact Or.inr (le_antisymm e a1)
  · rcases d1 with e | e
    · exact Or.inl e
    · exact Or.inr (le_antisymm e b1)

end BM.Besi
