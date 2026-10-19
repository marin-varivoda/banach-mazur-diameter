/-
Besicovitch, part 3: horizontal configurations (Besicovitch's hexagon up to the defect `δ`).
`HConf K r0 h0 r c b δ`: the six points `c ± b`, `c + b - (r,0)`, `c - b + (r,0)`,
`c + (δ ± r, 0)` lie on `∂K`, with `r0 ≤ r`, `h0 ≤ b.2`. For `δ = 0` it is an inscribed
affine-regular hexagon `c ± a, c ± b, c ± (b - a)` with `a = (r, 0)`.
-/
import BMLean.Besicovitch.OneDim
import BMLean.Besicovitch.Slice

namespace BM.Besi

open Set Filter Topology

/-- Besicovitch's hexagon with horizontal sides, up to the defect `δ` of the middle chord -/
def HConf (K : Set P2) (r0 h0 r : ℝ) (c b : P2) (δ : ℝ) : Prop :=
  c + b ∈ frontier K ∧ c + b - (r, 0) ∈ frontier K ∧ c - b ∈ frontier K ∧
    c - b + (r, 0) ∈ frontier K ∧ c + (δ + r, 0) ∈ frontier K ∧ c + (δ - r, 0) ∈ frontier K ∧
    r0 ≤ r ∧ h0 ≤ b.2

variable {K : Set P2}

lemma fr_pt {p : P2} {x t : ℝ} (hp : p ∈ frontier K) (h1 : p.1 = x) (h2 : p.2 = t) :
    (x, t) ∈ frontier K := by
  subst h1 h2; exact hp

lemma mem_pt {p : P2} {x t : ℝ} (hp : p ∈ K) (h1 : p.1 = x) (h2 : p.2 = t) :
    (x, t) ∈ K := by
  subst h1 h2; exact hp

lemma pt_fr {p : P2} {x t : ℝ} (hp : (x, t) ∈ frontier K) (h1 : p.1 = x) (h2 : p.2 = t) :
    p ∈ frontier K := by
  subst h1 h2; exact hp

lemma fr_sub (hK : IsConvexBody K) : frontier K ⊆ K := hK.1.isClosed.frontier_subset

/-- convex combination of two boundary points at the same level which coincide or lie on the
top or bottom level -/
lemma comb_frontier (hK : IsConvexBody K) {p q : P2} (hp : p ∈ frontier K)
    (hq : q ∈ frontier K) (h2 : p.2 = q.2) (h : p.1 = q.1 ∨ p.2 = yhi K ∨ p.2 = ylo K)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) • p + s • q ∈ frontier K := by
  rcases h with h | h | h
  · have : q = p := Prod.ext h.symm h2.symm
    subst this
    rw [← add_smul]; simpa using hp
  · have hm : (1 - s) • p + s • q ∈ K :=
      hK.2.1 (fr_sub hK hp) (fr_sub hK hq) (by linarith) hs0 (by ring)
    refine frontier_of_top hK hm ?_
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [← h2, h]; ring
  · have hm : (1 - s) • p + s • q ∈ K :=
      hK.2.1 (fr_sub hK hp) (fr_sub hK hq) (by linarith) hs0 (by ring)
    refine frontier_of_bot hK hm ?_
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [← h2, h]; ring

/-- a configuration gives the levels of Besicovitch's hexagon, and the chord data -/
lemma hconf_hexLev (hK : IsConvexBody K) {r0 h0 r δ : ℝ} {c b : P2} (hr0 : 0 < r0)
    (hh0 : 0 < h0) (h : HConf K r0 h0 r c b δ) :
    HexLev (wid K) (ylo K) (yhi K) r (c.2 - b.2) (c.2 + b.2) ∧
      (c.2 + b.2 < yhi K → c.1 + b.1 = rgt K (c.2 + b.2)) ∧
      (ylo K < c.2 - b.2 → c.1 - b.1 = lft K (c.2 - b.2)) ∧
      c.1 + δ + r = rgt K c.2 := by
  obtain ⟨hP2, hP3, hP5, hP6, hM1, hM2, hr, hb⟩ := h
  have hr' : 0 < r := by linarith
  have hb' : 0 < b.2 := by linarith
  have f2 : (c.1 + b.1, c.2 + b.2) ∈ frontier K := fr_pt hP2 (by simp) (by simp)
  have f3 : (c.1 + b.1 - r, c.2 + b.2) ∈ frontier K := fr_pt hP3 (by simp) (by simp)
  have f5 : (c.1 - b.1, c.2 - b.2) ∈ frontier K := fr_pt hP5 (by simp) (by simp)
  have f6 : (c.1 - b.1 + r, c.2 - b.2) ∈ frontier K := fr_pt hP6 (by simp) (by simp)
  have f1 : (c.1 + δ + r, c.2) ∈ frontier K := fr_pt hM1 (by simp; ring) (by simp)
  have f4 : (c.1 + δ - r, c.2) ∈ frontier K := fr_pt hM2 (by simp; ring) (by simp)
  obtain ⟨⟨a2, a2'⟩, ⟨x2, x2'⟩⟩ := (mem_iff hK).1 (fr_sub hK f2)
  obtain ⟨_, ⟨x3, _⟩⟩ := (mem_iff hK).1 (fr_sub hK f3)
  obtain ⟨⟨a5, a5'⟩, ⟨x5, _⟩⟩ := (mem_iff hK).1 (fr_sub hK f5)
  obtain ⟨_, ⟨_, x6'⟩⟩ := (mem_iff hK).1 (fr_sub hK f6)
  have hmid : c.2 ∈ Ioo (ylo K) (yhi K) := ⟨by linarith, by linarith⟩
  obtain ⟨e4, e1⟩ := chord hK f4 f1 (by linarith) hmid
  have htop : c.2 + b.2 < yhi K → c.1 + b.1 - r = lft K (c.2 + b.2) ∧
      c.1 + b.1 = rgt K (c.2 + b.2) := fun h ↦ chord hK f3 f2 (by linarith) ⟨by linarith, h⟩
  have hbot : ylo K < c.2 - b.2 → c.1 - b.1 = lft K (c.2 - b.2) ∧
      c.1 - b.1 + r = rgt K (c.2 - b.2) := fun h ↦ chord hK f5 f6 (by linarith) ⟨h, by linarith⟩
  have emid : (c.2 - b.2 + (c.2 + b.2)) / 2 = c.2 := by ring
  refine ⟨⟨a5, by linarith, a2', hr', ?_, ?_, ?_, ?_, ?_⟩, fun h ↦ (htop h).2,
    fun h ↦ (hbot h).1, e1⟩
  · unfold wid; linarith
  · unfold wid; linarith
  · rcases eq_or_lt_of_le a5 with h | h
    · exact Or.inl h.symm
    · right; obtain ⟨u, v⟩ := hbot h; unfold wid; linarith
  · rcases eq_or_lt_of_le a2' with h | h
    · exact Or.inl h
    · right; obtain ⟨u, v⟩ := htop h; unfold wid; linarith
  · rw [emid]; unfold wid; linarith

/-- existence of a configuration, with uniform bounds from four points `o ± ρ e_i` of `K` -/
lemma hconf_exists (hK : IsConvexBody K) {o : P2} {ρ : ℝ} (hρ : 0 < ρ)
    (h1 : o + (ρ, 0) ∈ K) (h2 : o - (ρ, 0) ∈ K) (h3 : o + (0, ρ) ∈ K) (h4 : o - (0, ρ) ∈ K) :
    ∃ r c b δ, HConf K (ρ / 2) (ρ / 2) r c b δ := by
  have hm := ylo_lt_yhi hK
  have k1 : (o.1 + ρ, o.2) ∈ K := mem_pt h1 (by simp) (by simp)
  have k2 : (o.1 - ρ, o.2) ∈ K := mem_pt h2 (by simp) (by simp)
  have k3 : (o.1, o.2 + ρ) ∈ K := mem_pt h3 (by simp) (by simp)
  have k4 : (o.1, o.2 - ρ) ∈ K := mem_pt h4 (by simp) (by simp)
  obtain ⟨ho, ⟨_, q1⟩⟩ := (mem_iff hK).1 k1
  obtain ⟨_, ⟨q2, _⟩⟩ := (mem_iff hK).1 k2
  obtain ⟨⟨_, q3⟩, _⟩ := (mem_iff hK).1 k3
  obtain ⟨⟨q4, _⟩, _⟩ := (mem_iff hK).1 k4
  have hwo : 2 * ρ ≤ wid K o.2 := by unfold wid; linarith
  obtain ⟨r, t1, t2, hL⟩ := hexLev_exists (wid_concave hK) (wid_cont hK)
    (fun t ht ↦ wid_nonneg hK ht) hm ⟨o.2, ho, by linarith⟩
  obtain ⟨B1, B2⟩ := hexLev_bound (wid_concave hK) (fun t ht ↦ wid_nonneg hK ht) hL
  have hB1 := B1 o.2 ho
  obtain ⟨l1, l12, l2, hr, w1, w2, e1, e2, wm⟩ := hL
  have ht1 : t1 ∈ Icc (ylo K) (yhi K) := ⟨l1, by linarith⟩
  have ht2 : t2 ∈ Icc (ylo K) (yhi K) := ⟨by linarith, l2⟩
  set mid := (t1 + t2) / 2 with hmid
  have htm : mid ∈ Icc (ylo K) (yhi K) := ⟨by linarith, by linarith⟩
  refine ⟨r, ((rgt K t2 + lft K t1) / 2, mid), ((rgt K t2 - lft K t1) / 2, (t2 - t1) / 2),
    (lft K mid + rgt K mid) / 2 - (rgt K t2 + lft K t1) / 2, ?_, ?_, ?_, ?_, ?_, ?_,
    by linarith, by simp only; linarith⟩
  · exact pt_fr (frontier_rgt hK ht2) (by simp; ring) (by simp; ring)
  · rcases e2 with e | e
    · have hk : (rgt K t2 - r, t2) ∈ K :=
        (mem_iff hK).2 ⟨ht2, by unfold wid at w2; linarith, by linarith⟩
      exact pt_fr (frontier_of_top hK hk e) (by simp; ring) (by simp; ring)
    · have : rgt K t2 - r = lft K t2 := by unfold wid at e; linarith
      exact pt_fr (frontier_lft hK ht2) (by simp; linarith) (by simp; ring)
  · exact pt_fr (frontier_lft hK ht1) (by simp; ring) (by simp; ring)
  · rcases e1 with e | e
    · have hk : (lft K t1 + r, t1) ∈ K :=
        (mem_iff hK).2 ⟨ht1, by linarith, by unfold wid at w1; linarith⟩
      exact pt_fr (frontier_of_bot hK hk e) (by simp; ring) (by simp; ring)
    · have : lft K t1 + r = rgt K t1 := by unfold wid at e; linarith
      exact pt_fr (frontier_rgt hK ht1) (by simp; linarith) (by simp; ring)
  · have : (lft K mid + rgt K mid) / 2 + r = rgt K mid := by unfold wid at wm; linarith
    exact pt_fr (frontier_rgt hK htm) (by simp; linarith) (by simp)
  · have : (lft K mid + rgt K mid) / 2 - r = lft K mid := by unfold wid at wm; linarith
    exact pt_fr (frontier_lft hK htm) (by simp; linarith) (by simp)

/-- the configurations with fixed body form a convex set -/
lemma hconf_convex (hK : IsConvexBody K) {r0 h0 r r' δ δ' : ℝ} {c c' b b' : P2} (hr0 : 0 < r0)
    (hh0 : 0 < h0) (h : HConf K r0 h0 r c b δ) (h' : HConf K r0 h0 r' c' b' δ') {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HConf K r0 h0 ((1 - s) * r + s * r') ((1 - s) • c + s • c') ((1 - s) • b + s • b')
      ((1 - s) * δ + s * δ') := by
  obtain ⟨L, top, bot, md⟩ := hconf_hexLev hK hr0 hh0 h
  obtain ⟨L', top', bot', md'⟩ := hconf_hexLev hK hr0 hh0 h'
  obtain ⟨er, et1, et2⟩ := hexLev_unique (wid_concave hK) L L'
  subst er
  have ec2 : c'.2 = c.2 := by linarith
  have eb2 : b'.2 = b.2 := by linarith
  have emd : c'.1 + δ' = c.1 + δ := by rw [ec2] at md'; linarith
  obtain ⟨hP2, hP3, hP5, hP6, hM1, hM2, hr, hb⟩ := h
  obtain ⟨hP2', hP3', hP5', hP6', hM1', hM2', -, -⟩ := h'
  obtain ⟨l1, _, l2, -⟩ := L
  have T : c.1 + b.1 = c'.1 + b'.1 ∨ c.2 + b.2 = yhi K ∨ c.2 + b.2 = ylo K := by
    rcases eq_or_lt_of_le l2 with e | e
    · exact Or.inr (Or.inl e)
    · left; rw [top e, et2, top' (by rw [← et2]; exact e)]
  have Bt : c.1 - b.1 = c'.1 - b'.1 ∨ c.2 - b.2 = yhi K ∨ c.2 - b.2 = ylo K := by
    rcases eq_or_lt_of_le l1 with e | e
    · exact Or.inr (Or.inr e.symm)
    · left; rw [bot e, et1, bot' (by rw [← et1]; exact e)]
  have rr : (1 - s) * r + s * r = r := by ring
  rw [rr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hr, ?_⟩
  · have e : (1 - s) • c + s • c' + ((1 - s) • b + s • b') = (1 - s) • (c + b) + s • (c' + b') := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hP2 hP2' (by simp; linarith) ?_ hs0 hs1
    simpa using T
  · have e : (1 - s) • c + s • c' + ((1 - s) • b + s • b') - (r, 0) =
        (1 - s) • (c + b - (r, 0)) + s • (c' + b' - (r, 0)) := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hP3 hP3' (by simp; linarith) ?_ hs0 hs1
    simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add, sub_zero]
    rcases T with T | T | T
    · left; rw [T]
    · right; left; exact T
    · right; right; exact T
  · have e : (1 - s) • c + s • c' - ((1 - s) • b + s • b') = (1 - s) • (c - b) + s • (c' - b') := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hP5 hP5' (by simp; linarith) ?_ hs0 hs1
    simpa using Bt
  · have e : (1 - s) • c + s • c' - ((1 - s) • b + s • b') + (r, 0) =
        (1 - s) • (c - b + (r, 0)) + s • (c' - b' + (r, 0)) := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hP6 hP6' (by simp; linarith) ?_ hs0 hs1
    simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add, add_zero]
    rcases Bt with T | T | T
    · left; rw [T]
    · right; left; exact T
    · right; right; exact T
  · have e : (1 - s) • c + s • c' + ((1 - s) * δ + s * δ' + r, (0 : ℝ)) =
        (1 - s) • (c + (δ + r, 0)) + s • (c' + (δ' + r, 0)) := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hM1 hM1' (by simp; linarith) (Or.inl ?_) hs0 hs1
    simp; linarith
  · have e : (1 - s) • c + s • c' + ((1 - s) * δ + s * δ' - r, (0 : ℝ)) =
        (1 - s) • (c + (δ - r, 0)) + s • (c' + (δ' - r, 0)) := by
      ext <;> simp <;> ring
    rw [e]
    refine comb_frontier hK hM2 hM2' (by simp; linarith) (Or.inl ?_) hs0 hs1
    simp; linarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [eb2]; nlinarith

end BM.Besi
