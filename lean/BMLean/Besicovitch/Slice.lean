/-
Besicovitch, part 2: horizontal slices of a planar convex body.
For a level `t ∈ [ylo, yhi]` the slice `{x | (x, t) ∈ K}` is `[lft t, rgt t]`; its width `wid`
is concave and continuous on `[ylo, yhi]`, and the boundary points of `K` at an interior level
are exactly the two chord endpoints.
-/
import BMLean.Statement

namespace BM.Besi

open Set Filter Topology

variable (K : Set P2)

/-- lowest level of `K` -/
noncomputable def ylo : ℝ := sInf (Prod.snd '' K)
/-- highest level of `K` -/
noncomputable def yhi : ℝ := sSup (Prod.snd '' K)
/-- left end of the horizontal chord at level `t` -/
noncomputable def lft (t : ℝ) : ℝ := sInf {x | (x, t) ∈ K}
/-- right end of the horizontal chord at level `t` -/
noncomputable def rgt (t : ℝ) : ℝ := sSup {x | (x, t) ∈ K}
/-- length of the horizontal chord at level `t` -/
noncomputable def wid (t : ℝ) : ℝ := rgt K t - lft K t

variable {K}

lemma slice_eq (t : ℝ) : {x | (x, t) ∈ K} = Prod.fst '' (K ∩ {p | p.2 = t}) := by
  ext x
  constructor
  · intro h; exact ⟨(x, t), ⟨h, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hpt⟩, rfl⟩
    show (p.1, t) ∈ K
    rw [← hpt]; exact hp

lemma slice_compact (hK : IsConvexBody K) (t : ℝ) : IsCompact {x | (x, t) ∈ K} := by
  rw [slice_eq]
  exact (hK.1.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst

lemma slice_convex (hK : IsConvexBody K) (t : ℝ) : Convex ℝ {x | (x, t) ∈ K} := by
  intro x hx y hy a b ha hb hab
  have := hK.2.1 hx hy ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
  show (a * x + b * y, t) ∈ K
  rwa [← add_mul, hab, one_mul] at this

lemma snd_compact (hK : IsConvexBody K) : IsCompact (Prod.snd '' K) :=
  hK.1.image continuous_snd

lemma K_nonempty (hK : IsConvexBody K) : K.Nonempty := by
  obtain ⟨z, hz⟩ := hK.2.2
  exact ⟨z, interior_subset hz⟩

lemma ylo_mem (hK : IsConvexBody K) : ylo K ∈ Prod.snd '' K :=
  (snd_compact hK).sInf_mem ((K_nonempty hK).image _)

lemma yhi_mem (hK : IsConvexBody K) : yhi K ∈ Prod.snd '' K :=
  (snd_compact hK).sSup_mem ((K_nonempty hK).image _)

lemma ylo_le (hK : IsConvexBody K) {p : P2} (hp : p ∈ K) : ylo K ≤ p.2 :=
  csInf_le (snd_compact hK).bddBelow ⟨p, hp, rfl⟩

lemma le_yhi (hK : IsConvexBody K) {p : P2} (hp : p ∈ K) : p.2 ≤ yhi K :=
  le_csSup (snd_compact hK).bddAbove ⟨p, hp, rfl⟩

lemma snd_convex (hK : IsConvexBody K) : Convex ℝ (Prod.snd '' K) := by
  have := hK.2.1.linear_image (LinearMap.snd ℝ ℝ ℝ)
  simpa using this

lemma slice_nonempty (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    {x | (x, t) ∈ K}.Nonempty := by
  have h := (convex_iff_ordConnected.1 (snd_convex hK)).out (ylo_mem hK) (yhi_mem hK) ht
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p.1, hp⟩

lemma lft_le (hK : IsConvexBody K) {x t : ℝ} (h : (x, t) ∈ K) : lft K t ≤ x :=
  csInf_le (slice_compact hK t).bddBelow h

lemma le_rgt (hK : IsConvexBody K) {x t : ℝ} (h : (x, t) ∈ K) : x ≤ rgt K t :=
  le_csSup (slice_compact hK t).bddAbove h

lemma habs {ε : ℝ} (hε : 0 < ε) : |ε / 2| < ε := by
  rw [abs_of_pos (half_pos hε)]; linarith

lemma interior_box (_hK : IsConvexBody K) {p : P2} (hp : p ∈ interior K) :
    ∃ ε > 0, ∀ v : P2, |v.1| < ε → |v.2| < ε → p + v ∈ K := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
  obtain ⟨ε, hε, hb⟩ := hp
  refine ⟨ε, hε, fun v h1 h2 ↦ hb ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [Prod.fst_add, Prod.snd_add, Real.dist_eq, add_sub_cancel_left]
  exact max_lt h1 h2

lemma ylo_lt_yhi (hK : IsConvexBody K) : ylo K < yhi K := by
  obtain ⟨z, hz⟩ := hK.2.2
  obtain ⟨ε, hε, hb⟩ := interior_box hK hz
  have h1 := hb (0, ε / 2) (by simp [hε]) (by simpa using habs hε)
  have h2 := hb (0, -(ε / 2)) (by simp [hε]) (by simpa using habs hε)
  have := ylo_le hK h2
  have := le_yhi hK h1
  simp at *
  linarith

lemma mem_iff (hK : IsConvexBody K) {x t : ℝ} :
    (x, t) ∈ K ↔ t ∈ Icc (ylo K) (yhi K) ∧ x ∈ Icc (lft K t) (rgt K t) := by
  constructor
  · intro h
    exact ⟨⟨ylo_le hK h, le_yhi hK h⟩, lft_le hK h, le_rgt hK h⟩
  · rintro ⟨ht, hx⟩
    have hne := slice_nonempty hK ht
    have h1 : lft K t ∈ {x | (x, t) ∈ K} := (slice_compact hK t).sInf_mem hne
    have h2 : rgt K t ∈ {x | (x, t) ∈ K} := (slice_compact hK t).sSup_mem hne
    exact (convex_iff_ordConnected.1 (slice_convex hK t)).out h1 h2 hx

lemma lft_mem (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    (lft K t, t) ∈ K :=
  (slice_compact hK t).sInf_mem (slice_nonempty hK ht)

lemma rgt_mem (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    (rgt K t, t) ∈ K :=
  (slice_compact hK t).sSup_mem (slice_nonempty hK ht)

lemma wid_nonneg (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    0 ≤ wid K t := by
  have := le_rgt hK (lft_mem hK ht)
  unfold wid; linarith

lemma wid_concave (hK : IsConvexBody K) : ConcaveOn ℝ (Icc (ylo K) (yhi K)) (wid K) := by
  refine ⟨convex_Icc _ _, fun t ht t' ht' a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  have hr := hK.2.1 (rgt_mem hK ht) (rgt_mem hK ht') ha hb hab
  have hl := hK.2.1 (lft_mem hK ht) (lft_mem hK ht') ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hr hl
  have h1 := le_rgt hK hr
  have h2 := lft_le hK hl
  unfold wid
  nlinarith

private lemma slice_interp {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y) (hyz : y ≤ z) (hxz : x < z) :
    (z - y) * f x + (y - x) * f z ≤ (z - x) * f y := by
  have hd : 0 < z - x := by linarith
  have ha : 0 ≤ (z - y) / (z - x) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (y - x) / (z - x) := div_nonneg (by linarith) hd.le
  have hne : z - x ≠ 0 := hd.ne'
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hne]; ring
  have h := hf.2 hx hz ha hb hab
  simp only [smul_eq_mul] at h
  have hy : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp; ring
  rw [hy] at h
  have e : (z - y) * f x + (y - x) * f z =
      (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) := by
    field_simp
  rw [e]; exact mul_le_mul_of_nonneg_left h hd.le

private lemma slice_concave_bound {a b : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc a b) f) {t t' : ℝ}
    (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) :
    f t - (|f b - f t| / (b - t) + |f a - f t| / (t - a)) * |t' - t| ≤ f t' := by
  have hC1 : 0 ≤ |f b - f t| / (b - t) := div_nonneg (abs_nonneg _) (by linarith [ht.2])
  have hC2 : 0 ≤ |f a - f t| / (t - a) := div_nonneg (abs_nonneg _) (by linarith [ht.1])
  rcases lt_trichotomy t' t with h | h | h
  · have hta : a < t := lt_of_le_of_lt ht'.1 h
    have := slice_interp hf ⟨le_rfl, by linarith [ht.2]⟩ ht ht'.1 h.le hta
    rw [abs_of_neg (show t' - t < 0 by linarith)]
    have key : f t - |f a - f t| / (t - a) * (t - t') ≤ f t' := by
      have hd : 0 < t - a := by linarith
      have e : |f a - f t| / (t - a) * (t - t') = |f a - f t| * (t - t') / (t - a) := by ring
      rw [e, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hd]
      have := neg_abs_le (f a - f t)
      nlinarith
    nlinarith
  · subst h; simp
  · have htb : t < b := lt_of_lt_of_le h ht'.2
    have := slice_interp hf ht ⟨by linarith [ht.1], le_rfl⟩ h.le ht'.2 htb
    rw [abs_of_pos (show 0 < t' - t by linarith)]
    have key : f t - |f b - f t| / (b - t) * (t' - t) ≤ f t' := by
      have hd : 0 < b - t := by linarith
      have e : |f b - f t| / (b - t) * (t' - t) = |f b - f t| * (t' - t) / (b - t) := by ring
      rw [e, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hd]
      have := neg_abs_le (f b - f t)
      nlinarith
    nlinarith

lemma slice_concave_lsc {a b : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc a b) f) {t : ℝ}
    (ht : t ∈ Icc a b) : ∀ y < f t, ∀ᶠ t' in 𝓝[Icc a b] t, y < f t' := by
  intro y hy
  set C := |f b - f t| / (b - t) + |f a - f t| / (t - a) with hCdef
  have hC : 0 ≤ C := add_nonneg (div_nonneg (abs_nonneg _) (by linarith [ht.2]))
    (div_nonneg (abs_nonneg _) (by linarith [ht.1]))
  have hε : 0 < (f t - y) / (C + 1) := div_pos (by linarith) (by linarith)
  have h1 : ∀ᶠ t' in 𝓝 t, |t' - t| < (f t - y) / (C + 1) := by
    have := Metric.ball_mem_nhds t hε
    filter_upwards [this] with t' ht'
    rwa [Metric.mem_ball, Real.dist_eq] at ht'
  filter_upwards [eventually_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h1] with t' ht' h2
  have hb := slice_concave_bound hf ht ht'
  rw [← hCdef] at hb
  have : C * |t' - t| < f t - y := by
    calc C * |t' - t| ≤ C * ((f t - y) / (C + 1)) := mul_le_mul_of_nonneg_left h2.le hC
      _ < f t - y := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

lemma wid_usc (hK : IsConvexBody K) {t : ℝ} (_ht : t ∈ Icc (ylo K) (yhi K)) :
    ∀ y, wid K t < y → ∀ᶠ t' in 𝓝[Icc (ylo K) (yhi K)] t, wid K t' < y := by
  intro y hy
  set P : Set (P2 × P2) := (K ×ˢ K) ∩ ({pq | pq.1.2 = pq.2.2} ∩ {pq | y ≤ pq.2.1 - pq.1.1})
  have hP : IsCompact P := (hK.1.prod hK.1).inter_right
    ((isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop)))
  have hcl : IsClosed ((fun pq : P2 × P2 ↦ pq.1.2) '' P) := (hP.image (by fun_prop)).isClosed
  have hnot : t ∉ (fun pq : P2 × P2 ↦ pq.1.2) '' P := by
    rintro ⟨pq, ⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    simp only [mem_ofPred_eq] at h3 h4 h5
    have e1 : ((pq.1.1, t) : P2) ∈ K := by rw [← h5]; exact h1
    have e2 : ((pq.2.1, t) : P2) ∈ K := by rw [← h5, h3]; exact h2
    have := lft_le hK e1
    have := le_rgt hK e2
    unfold wid at hy
    linarith
  have hev : ∀ᶠ t' in 𝓝 t, t' ∉ (fun pq : P2 × P2 ↦ pq.1.2) '' P :=
    hcl.isOpen_compl.mem_nhds hnot
  filter_upwards [eventually_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with t' ht' h2
  by_contra hc
  push Not at hc
  apply h2
  refine ⟨((lft K t', t'), (rgt K t', t')), ⟨⟨lft_mem hK ht', rgt_mem hK ht'⟩, rfl, ?_⟩, rfl⟩
  exact hc

lemma wid_cont (hK : IsConvexBody K) : ContinuousOn (wid K) (Icc (ylo K) (yhi K)) := by
  intro t ht
  rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact ⟨slice_concave_lsc (wid_concave hK) ht, wid_usc hK ht⟩

lemma not_mem_interior_of (hK : IsConvexBody K) {p : P2} (hp : p ∈ K)
    (h : ∀ ε > 0, ∃ v : P2, |v.1| < ε ∧ |v.2| < ε ∧ p + v ∉ K) : p ∈ frontier K := by
  refine ⟨subset_closure hp, fun hi ↦ ?_⟩
  obtain ⟨ε, hε, hb⟩ := interior_box hK hi
  obtain ⟨v, h1, h2, h3⟩ := h ε hε
  exact h3 (hb v h1 h2)

lemma frontier_of_top (hK : IsConvexBody K) {p : P2} (hp : p ∈ K) (h : p.2 = yhi K) :
    p ∈ frontier K := by
  refine not_mem_interior_of hK hp fun ε hε ↦ ?_
  have h1 : |((0 : ℝ), ε / 2).1| < ε := by simp [hε]
  have h2 : |((0 : ℝ), ε / 2).2| < ε := by simpa using habs hε
  refine ⟨(0, ε / 2), h1, h2, fun hq ↦ ?_⟩
  have := le_yhi hK hq
  simp at this; linarith

lemma frontier_of_bot (hK : IsConvexBody K) {p : P2} (hp : p ∈ K) (h : p.2 = ylo K) :
    p ∈ frontier K := by
  refine not_mem_interior_of hK hp fun ε hε ↦ ?_
  have h1 : |((0 : ℝ), -(ε / 2)).1| < ε := by simp [hε]
  have h2 : |((0 : ℝ), -(ε / 2)).2| < ε := by simpa using habs hε
  refine ⟨(0, -(ε / 2)), h1, h2, fun hq ↦ ?_⟩
  have := ylo_le hK hq
  simp at this; linarith

lemma frontier_lft (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    (lft K t, t) ∈ frontier K := by
  refine not_mem_interior_of hK (lft_mem hK ht) fun ε hε ↦ ?_
  have h1 : |(-(ε / 2), (0 : ℝ)).1| < ε := by simpa using habs hε
  have h2 : |(-(ε / 2), (0 : ℝ)).2| < ε := by simp [hε]
  refine ⟨(-(ε / 2), 0), h1, h2, fun hq ↦ ?_⟩
  have := lft_le hK (x := lft K t + -(ε / 2)) (t := t) (by simpa using hq)
  linarith

lemma frontier_rgt (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Icc (ylo K) (yhi K)) :
    (rgt K t, t) ∈ frontier K := by
  refine not_mem_interior_of hK (rgt_mem hK ht) fun ε hε ↦ ?_
  have h1 : |(ε / 2, (0 : ℝ)).1| < ε := by simpa using habs hε
  have h2 : |(ε / 2, (0 : ℝ)).2| < ε := by simp [hε]
  refine ⟨(ε / 2, 0), h1, h2, fun hq ↦ ?_⟩
  have := le_rgt hK (x := rgt K t + ε / 2) (t := t) (by simpa using hq)
  linarith

lemma seg_interior (hK : IsConvexBody K) {z y : P2} (hz : z ∈ interior K) (hy : y ∈ K) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : (1 - s) • z + s • y ∈ interior K :=
  hK.2.1.openSegment_interior_closure_subset_interior hz (subset_closure hy)
    ⟨1 - s, s, by linarith, hs0, by ring, rfl⟩

/-- an interior point at every interior level -/
lemma exists_interior_level (hK : IsConvexBody K) {t : ℝ} (ht : t ∈ Ioo (ylo K) (yhi K)) :
    ∃ q ∈ interior K, q.2 = t := by
  obtain ⟨z, hz⟩ := hK.2.2
  rcases lt_trichotomy z.2 t with h | h | h
  · obtain ⟨p, hp, hp2⟩ := yhi_mem hK
    have hlt : z.2 < yhi K := h.trans ht.2
    set s := (t - z.2) / (yhi K - z.2)
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith [ht.2])
    refine ⟨_, seg_interior hK hz hp hs0 hs1, ?_⟩
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hp2, s]
    field_simp; ring
  · exact ⟨z, hz, h⟩
  · obtain ⟨p, hp, hp2⟩ := ylo_mem hK
    have hlt : ylo K < z.2 := ht.1.trans h
    set s := (z.2 - t) / (z.2 - ylo K)
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith [ht.1])
    refine ⟨_, seg_interior hK hz hp hs0 hs1, ?_⟩
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hp2, s]
    field_simp; ring

lemma interior_of_between (hK : IsConvexBody K) {x t : ℝ} (ht : t ∈ Ioo (ylo K) (yhi K))
    (h1 : lft K t < x) (h2 : x < rgt K t) : (x, t) ∈ interior K := by
  obtain ⟨q, hq, hq2⟩ := exists_interior_level hK ht
  have hqK : (q.1, t) ∈ K := by rw [← hq2]; exact interior_subset hq
  have htI : t ∈ Icc (ylo K) (yhi K) := Ioo_subset_Icc_self ht
  rcases lt_trichotomy x q.1 with h | h | h
  · have hl := lft_le hK hqK
    set s := (q.1 - x) / (q.1 - lft K t)
    have hne : q.1 - lft K t ≠ 0 := (show (0:ℝ) < q.1 - lft K t by linarith).ne'
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have := seg_interior hK hq (lft_mem hK htI) hs0 hs1
    convert this using 1
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, s]
      field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hq2]; ring
  · rw [h, ← hq2]; exact hq
  · have hl := le_rgt hK hqK
    set s := (x - q.1) / (rgt K t - q.1)
    have hne : rgt K t - q.1 ≠ 0 := (show (0:ℝ) < rgt K t - q.1 by linarith).ne'
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have := seg_interior hK hq (rgt_mem hK htI) hs0 hs1
    convert this using 1
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, s]
      field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hq2]; ring

/-- two boundary points on an interior level are the chord endpoints -/
lemma chord (hK : IsConvexBody K) {x x' t : ℝ} (hx : (x, t) ∈ frontier K)
    (hx' : (x', t) ∈ frontier K) (hlt : x < x') (ht : t ∈ Ioo (ylo K) (yhi K)) :
    x = lft K t ∧ x' = rgt K t := by
  have hxK := hK.1.isClosed.frontier_subset hx
  have hxK' := hK.1.isClosed.frontier_subset hx'
  have h1 := lft_le hK hxK
  have h2 := le_rgt hK hxK'
  constructor
  · by_contra hne
    exact hx.2 (interior_of_between hK ht (lt_of_le_of_ne h1 (Ne.symm hne)) (by linarith))
  · by_contra hne
    exact hx'.2 (interior_of_between hK ht (by linarith) (lt_of_le_of_ne h2 hne))

end BM.Besi
