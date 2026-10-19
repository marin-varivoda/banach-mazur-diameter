/-
**Besicovitch's lemma**: every planar convex body has an inscribed affine-regular hexagon.
`theorem BM.besicovitch : BM.Besicovitch`. Plan and progress log: `Besicovitch/PROGRESS.md`.

Files: `Besicovitch/OneDim.lean` (1-D concavity lemmas), `Besicovitch/Slice.lean` (horizontal
chords), `Besicovitch/Config.lean` (horizontal configurations: existence, levels, convexity);
this file: rotations, the connectedness argument in the direction θ, and the affine map.

Rotation convention: `rot θ` rotates by `θ`; the configurations for direction `θ` are the
horizontal configurations of `rot θ ⁻¹' K`, mapped to `K` by `rot θ`.
-/
import BMLean.Besicovitch.Config
namespace BM.Besi
open Set Real

/-- rotation by `θ` as a function -/
noncomputable def rotF (θ : ℝ) (p : P2) : P2 :=
  (p.1 * cos θ - p.2 * sin θ, p.1 * sin θ + p.2 * cos θ)

/-- rotation by `θ` -/
noncomputable def rotLE (θ : ℝ) : P2 ≃ₗ[ℝ] P2 where
  toFun := rotF θ
  invFun := rotF (-θ)
  map_add' p q := by ext <;> simp [rotF] <;> ring
  map_smul' a p := by ext <;> simp [rotF] <;> ring
  left_inv p := by
    ext
    · simp only [rotF, cos_neg, sin_neg]; linear_combination (p.1) * sin_sq_add_cos_sq θ
    · simp only [rotF, cos_neg, sin_neg]; linear_combination (p.2) * sin_sq_add_cos_sq θ
  right_inv p := by
    ext
    · simp only [rotF, cos_neg, sin_neg]; linear_combination (p.1) * sin_sq_add_cos_sq θ
    · simp only [rotF, cos_neg, sin_neg]; linear_combination (p.2) * sin_sq_add_cos_sq θ

/-- rotation by `θ`, as a continuous linear equivalence -/
noncomputable def rot (θ : ℝ) : P2 ≃L[ℝ] P2 := (rotLE θ).toContinuousLinearEquiv

@[simp] lemma rot_apply (θ : ℝ) (p : P2) : rot θ p = rotF θ p := rfl

lemma continuous_rotF : Continuous fun x : ℝ × P2 ↦ rotF x.1 x.2 := by
  unfold rotF; fun_prop

lemma rotF_add_pi (θ : ℝ) (p : P2) : rotF (θ + π) p = rotF θ (-p) := by
  ext <;> simp [rotF, cos_add_pi, sin_add_pi]

lemma abs_lin_le (x y a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |x * a + y * b| ≤ |x| + |y| := by
  calc |x * a + y * b| ≤ |x * a| + |y * b| := abs_add_le _ _
    _ = |x| * |a| + |y| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ |x| * 1 + |y| * 1 := by gcongr
    _ = |x| + |y| := by ring

lemma norm_rotF_le (θ : ℝ) (p : P2) : ‖rotF θ p‖ ≤ |p.1| + |p.2| := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have := abs_lin_le p.1 p.2 (cos θ) (-sin θ) (abs_cos_le_one θ) (by rw [abs_neg]; exact abs_sin_le_one θ)
    simpa [rotF, sub_eq_add_neg] using this
  · simpa [rotF] using abs_lin_le p.1 p.2 (sin θ) (cos θ) (abs_sin_le_one θ) (abs_cos_le_one θ)

lemma norm_le_rotF (θ : ℝ) (p : P2) : ‖p‖ ≤ 2 * ‖rotF θ p‖ := by
  have h : rotF (-θ) (rotF θ p) = p := (rotLE θ).left_inv p
  calc ‖p‖ = ‖rotF (-θ) (rotF θ p)‖ := by rw [h]
    _ ≤ |(rotF θ p).1| + |(rotF θ p).2| := norm_rotF_le _ _
    _ ≤ ‖rotF θ p‖ + ‖rotF θ p‖ := by
        gcongr
        · exact norm_fst_le (rotF θ p)
        · exact norm_snd_le (rotF θ p)
    _ = 2 * ‖rotF θ p‖ := by ring

lemma mem_frontier_rot {K : Set P2} (θ : ℝ) (p : P2) :
    p ∈ frontier (rot θ ⁻¹' K) ↔ rotF θ p ∈ frontier K := by
  have h := (rot θ).toHomeomorph.preimage_frontier K
  exact (Set.ext_iff.1 h p).symm

lemma rot_body {K : Set P2} (hK : IsConvexBody K) (θ : ℝ) : IsConvexBody (rot θ ⁻¹' K) := by
  refine ⟨(rot θ).toHomeomorph.isCompact_preimage.2 hK.1, hK.2.1.linear_preimage
    (rot θ).toLinearEquiv.toLinearMap, ?_⟩
  have h := (rot θ).toHomeomorph.preimage_interior K
  obtain ⟨x, hx⟩ := hK.2.2
  refine ⟨(rot θ).symm x, ?_⟩
  have : (rot θ).symm x ∈ (rot θ).toHomeomorph ⁻¹' interior K := by simpa using hx
  rw [h] at this
  exact this

/-! ### From six boundary points to the affine map -/

lemma inv_aux (d X Y Z W p : ℝ) (hd : d ≠ 0) (h : X * Z + Y * W = d * p) :
    d⁻¹ * X * Z + d⁻¹ * Y * W = p := by
  rw [mul_assoc, mul_assoc, ← mul_add, h, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- the linear map `(x, y) ↦ x u + y v`, an equivalence when `det(u, v) ≠ 0` -/
noncomputable def linUV (u v : P2) (hd : u.1 * v.2 - u.2 * v.1 ≠ 0) : P2 ≃ₗ[ℝ] P2 where
  toFun p := (p.1 * u.1 + p.2 * v.1, p.1 * u.2 + p.2 * v.2)
  invFun p := ((u.1 * v.2 - u.2 * v.1)⁻¹ * (p.1 * v.2 - p.2 * v.1),
    (u.1 * v.2 - u.2 * v.1)⁻¹ * (u.1 * p.2 - u.2 * p.1))
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp <;> ring
  left_inv p := by
    ext <;> dsimp only <;> rw [eq_comm, eq_inv_mul_iff_mul_eq₀ hd] <;> ring
  right_inv p := by
    ext <;> dsimp only <;> exact inv_aux _ _ _ _ _ _ hd (by ring)

lemma hex_of_points {K : Set P2} (hK : IsConvexBody K) (c a b : P2)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0)
    (h1 : c + a ∈ frontier K) (h2 : c + b ∈ frontier K) (h3 : c + (b - a) ∈ frontier K)
    (h4 : c - a ∈ frontier K) (h5 : c - b ∈ frontier K) (h6 : c - (b - a) ∈ frontier K) :
    ∃ A : P2 ≃ᵃ[ℝ] P2, A '' H0 ⊆ K ∧ ∀ v ∈ hexVerts, A v ∈ frontier K := by
  set u : P2 := (1 / 2 : ℝ) • a
  set v : P2 := b - (1 / 2 : ℝ) • a
  have hd : u.1 * v.2 - u.2 * v.1 ≠ 0 := by
    simp only [u, v, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    intro h; apply hdet; linarith
  let A : P2 ≃ᵃ[ℝ] P2 := (AffineEquiv.constVAdd ℝ P2 (-((0 : ℝ), (-1 : ℝ)))).trans
    ((linUV u v hd).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ P2 c))
  have hA : ∀ p : P2, A p = c + linUV u v hd (-((0 : ℝ), (-1 : ℝ)) + p) := fun p ↦ by
    simp [A, vadd_eq_add]
  have hfr : frontier K ⊆ K := hK.1.isClosed.frontier_subset
  have hv : ∀ w ∈ hexVerts, A w ∈ frontier K := by
    intro w hw
    simp only [hexVerts, mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · convert h2 using 1; rw [hA]; ext <;> simp [linUV, u, v]
    · convert h3 using 1; rw [hA]; ext <;> simp [linUV, u, v] <;> ring
    · convert h4 using 1; rw [hA]; ext <;> simp [linUV, u, v] <;> ring
    · convert h5 using 1; rw [hA]; ext <;> simp [linUV, u, v] <;> ring
    · convert h6 using 1; rw [hA]; ext <;> simp [linUV, u, v] <;> ring
    · convert h1 using 1; rw [hA]; ext <;> simp [linUV, u, v]
  refine ⟨A, ?_, hv⟩
  have : (A : P2 → P2) '' H0 = convexHull ℝ ((A : P2 → P2) '' hexVerts) :=
    A.toAffineMap.image_convexHull hexVerts
  rw [this]
  refine convexHull_min ?_ hK.2.1
  rintro _ ⟨w, hw, rfl⟩
  exact hfr (hv w hw)


/-! ### Configurations in direction `θ` -/

variable {K : Set P2}

/-- configurations in direction `θ`: horizontal configurations of `rot θ ⁻¹' K` -/
def Conf (K : Set P2) (ρ θ : ℝ) (q : ℝ × P2 × P2 × ℝ) : Prop :=
  HConf (rot θ ⁻¹' K) (ρ / 2) (ρ / 2) q.1 q.2.1 q.2.2.1 q.2.2.2

lemma conf_iff {ρ θ : ℝ} {q : ℝ × P2 × P2 × ℝ} : Conf K ρ θ q ↔
    rotF θ (q.2.1 + q.2.2.1) ∈ frontier K ∧ rotF θ (q.2.1 + q.2.2.1 - (q.1, 0)) ∈ frontier K ∧
    rotF θ (q.2.1 - q.2.2.1) ∈ frontier K ∧ rotF θ (q.2.1 - q.2.2.1 + (q.1, 0)) ∈ frontier K ∧
    rotF θ (q.2.1 + (q.2.2.2 + q.1, 0)) ∈ frontier K ∧
    rotF θ (q.2.1 + (q.2.2.2 - q.1, 0)) ∈ frontier K ∧ ρ / 2 ≤ q.1 ∧ ρ / 2 ≤ q.2.2.1.2 := by
  simp only [Conf, HConf, mem_frontier_rot]

lemma isClosed_conf (ρ : ℝ) : IsClosed {x : ℝ × (ℝ × P2 × P2 × ℝ) | Conf K ρ x.1 x.2} := by
  simp only [conf_iff, ofPred_and]
  refine IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_frontier.preimage (by unfold rotF; fun_prop)) <|
    IsClosed.inter (isClosed_le continuous_const (by fun_prop))
      (isClosed_le continuous_const (by fun_prop))

/-- antisymmetry: turning the direction by `π` negates the defect -/
lemma conf_add_pi {ρ θ r δ : ℝ} {c b : P2} (h : Conf K ρ θ (r, c, b, δ)) :
    Conf K ρ (θ + π) (r, -c, b, -δ) := by
  rw [conf_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [rotF_add_pi] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, h8⟩
  · convert h3 using 2; ext <;> simp <;> ring
  · convert h4 using 2; ext <;> simp <;> ring
  · convert h1 using 2; ext <;> simp <;> ring
  · convert h2 using 2; ext <;> simp <;> ring
  · convert h6 using 2; ext <;> simp <;> ring
  · convert h5 using 2; ext <;> simp <;> ring

lemma comp_bound {θ R : ℝ} {p : P2} (hR : K ⊆ Metric.closedBall 0 R) (hKc : IsClosed K)
    (h : rotF θ p ∈ frontier K) : -(2 * R) ≤ p.1 ∧ p.1 ≤ 2 * R ∧ -(2 * R) ≤ p.2 ∧ p.2 ≤ 2 * R := by
  have h1 : ‖rotF θ p‖ ≤ R := by
    simpa using hR (hKc.frontier_subset h)
  have h2 := (norm_le_rotF θ p).trans (by linarith : 2 * ‖rotF θ p‖ ≤ 2 * R)
  have h3 := (norm_fst_le p).trans h2
  have h4 := (norm_snd_le p).trans h2
  rw [Real.norm_eq_abs, abs_le] at h3 h4
  exact ⟨h3.1, h3.2, h4.1, h4.2⟩

lemma conf_bound {ρ θ R : ℝ} {q : ℝ × P2 × P2 × ℝ} (hR : K ⊆ Metric.closedBall 0 R)
    (hKc : IsClosed K) (hθ : θ ∈ Icc 0 π) (h : Conf K ρ θ q) : ‖(θ, q)‖ ≤ 8 * R + 4 := by
  obtain ⟨r, c, b, δ⟩ := q
  rw [conf_iff] at h
  obtain ⟨h1, h2, h3, -, h5, h6, -, -⟩ := h
  have e1 := comp_bound hR hKc h1
  have e2 := comp_bound hR hKc h2
  have e3 := comp_bound hR hKc h3
  have e5 := comp_bound hR hKc h5
  have e6 := comp_bound hR hKc h6
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3 e5 e6
  have hpi := Real.pi_le_four
  simp only [norm_prod_le_iff, Real.norm_eq_abs, abs_le]
  obtain ⟨hθ0, hθ1⟩ := hθ
  repeat' constructor
  all_goals linarith

/-! ### The connectedness argument in the direction -/

theorem besicovitch_body (hK : IsConvexBody K) :
    ∃ A : P2 ≃ᵃ[ℝ] P2, A '' H0 ⊆ K ∧ ∀ v ∈ hexVerts, A v ∈ frontier K := by
  have hKc : IsClosed K := hK.1.isClosed
  obtain ⟨R, hR⟩ := hK.1.isBounded.subset_closedBall 0
  -- a small box around an interior point gives the uniform bounds
  obtain ⟨o, ho⟩ := hK.2.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ho)
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hbox : ∀ θ (v : P2), |v.1| + |v.2| ≤ ρ → (rot θ).symm o + v ∈ rot θ ⁻¹' K := by
    intro θ v hv
    show rot θ ((rot θ).symm o + v) ∈ K
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_le_of_lt ((norm_rotF_le θ v).trans hv) (by linarith)
  have hex : ∀ θ, ∃ q, Conf K ρ θ q := by
    intro θ
    have hb : ∀ v : P2, |v.1| + |v.2| ≤ ρ → (rot θ).symm o + v ∈ rot θ ⁻¹' K := hbox θ
    obtain ⟨r, c, b, δ, h⟩ := hconf_exists (rot_body hK θ) hρ
      (hb _ (by simp [abs_of_pos hρ])) (by rw [sub_eq_add_neg]; exact hb _ (by simp [abs_of_pos hρ]))
      (hb _ (by simp [abs_of_pos hρ])) (by rw [sub_eq_add_neg]; exact hb _ (by simp [abs_of_pos hρ]))
    exact ⟨(r, c, b, δ), h⟩
  -- the compact set of configurations over `[0, π]`
  set S : Set (ℝ × (ℝ × P2 × P2 × ℝ)) := {x | x.1 ∈ Icc 0 π ∧ Conf K ρ x.1 x.2} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_Icc.preimage continuous_fst).inter (isClosed_conf ρ)
    · refine isBounded_iff_forall_norm_le.2 ⟨8 * R + 4, ?_⟩
      rintro ⟨θ, q⟩ ⟨hθ, hq⟩
      exact conf_bound hR hKc hθ hq
  set A := Prod.fst '' (S ∩ {x | 0 ≤ x.2.2.2.2}) with hA
  set B := Prod.fst '' (S ∩ {x | x.2.2.2.2 ≤ 0}) with hB
  have hAc : IsClosed A :=
    ((hSc.inter_right (isClosed_le continuous_const (by fun_prop))).image continuous_fst).isClosed
  have hBc : IsClosed B :=
    ((hSc.inter_right (isClosed_le (by fun_prop) continuous_const)).image continuous_fst).isClosed
  have hcov : Icc 0 π ⊆ A ∪ B := by
    intro θ hθ
    obtain ⟨q, hq⟩ := hex θ
    rcases le_total 0 q.2.2.2 with h | h
    · exact Or.inl ⟨(θ, q), ⟨⟨hθ, hq⟩, h⟩, rfl⟩
    · exact Or.inr ⟨(θ, q), ⟨⟨hθ, hq⟩, h⟩, rfl⟩
  have h0 : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, pi_pos.le⟩
  have hpi : π ∈ Icc 0 π := ⟨pi_pos.le, le_rfl⟩
  have hne : (Icc 0 π ∩ A).Nonempty ∧ (Icc 0 π ∩ B).Nonempty := by
    obtain ⟨⟨r, c, b, δ⟩, hq⟩ := hex 0
    have hq' : Conf K ρ π (r, -c, b, -δ) := by simpa using conf_add_pi hq
    rcases le_total 0 δ with h | h
    · exact ⟨⟨0, h0, ⟨(0, (r, c, b, δ)), ⟨⟨h0, hq⟩, h⟩, rfl⟩⟩,
        ⟨π, hpi, ⟨(π, (r, -c, b, -δ)), ⟨⟨hpi, hq'⟩, by simpa using h⟩, rfl⟩⟩⟩
    · exact ⟨⟨π, hpi, ⟨(π, (r, -c, b, -δ)), ⟨⟨hpi, hq'⟩, by simpa using h⟩, rfl⟩⟩,
        ⟨0, h0, ⟨(0, (r, c, b, δ)), ⟨⟨h0, hq⟩, h⟩, rfl⟩⟩⟩
  obtain ⟨θ, -, hθA, hθB⟩ :=
    isPreconnected_closed_iff.1 isPreconnected_Icc A B hAc hBc hcov hne.1 hne.2
  obtain ⟨⟨θ1, r1, c1, b1, δ1⟩, ⟨⟨-, hq1⟩, hδ1⟩, rfl⟩ := hθA
  obtain ⟨⟨θ2, r2, c2, b2, δ2⟩, ⟨⟨-, hq2⟩, hδ2⟩, hθ2⟩ := hθB
  simp only [mem_ofPred_eq] at hθ2 hδ1 hδ2 hq1 hq2
  subst hθ2
  -- a configuration with zero defect
  have hzero : ∃ r c b, HConf (rot θ2 ⁻¹' K) (ρ / 2) (ρ / 2) r c b 0 := by
    by_cases hd : δ1 - δ2 = 0
    · have : δ1 = 0 := by linarith
      exact ⟨r1, c1, b1, this ▸ hq1⟩
    · have hpos : 0 < δ1 - δ2 := lt_of_le_of_ne (by linarith) (Ne.symm hd)
      set s := δ1 / (δ1 - δ2)
      have hs0 : 0 ≤ s := div_nonneg hδ1 hpos.le
      have hs1 : s ≤ 1 := (div_le_one hpos).2 (by linarith)
      have h := hconf_convex (rot_body hK θ2) (half_pos hρ) (half_pos hρ) hq1 hq2 hs0 hs1
      have e : (1 - s) * δ1 + s * δ2 = 0 := by
        simp only [s]; field_simp; ring
      rw [e] at h
      exact ⟨_, _, _, h⟩
  obtain ⟨r, c, b, h⟩ := hzero
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := h
  rw [mem_frontier_rot] at g1 g2 g3 g4 g5 g6
  have hdet : (rot θ2 (r, 0)).1 * (rot θ2 b).2 - (rot θ2 (r, 0)).2 * (rot θ2 b).1 = r * b.2 := by
    simp only [rot_apply, rotF]
    linear_combination (r * b.2) * sin_sq_add_cos_sq θ2
  refine hex_of_points hK (rot θ2 c) (rot θ2 (r, 0)) (rot θ2 b) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hdet]; exact ne_of_gt (mul_pos (by linarith) (by linarith))
  · rw [← map_add]; show rotF θ2 _ ∈ _; convert g5 using 2; ext <;> simp
  · rw [← map_add]; exact g1
  · rw [← map_sub, ← map_add]; show rotF θ2 _ ∈ _; convert g2 using 2; abel
  · rw [← map_sub]; show rotF θ2 _ ∈ _; convert g6 using 2; ext <;> simp [sub_eq_add_neg]
  · rw [← map_sub]; exact g3
  · rw [← map_sub, ← map_sub]; show rotF θ2 _ ∈ _; convert g4 using 2; abel

end BM.Besi

/-- **Besicovitch's lemma**: every planar convex body has an inscribed affine-regular hexagon. -/
theorem BM.besicovitch : BM.Besicovitch := fun _ hK ↦ BM.Besi.besicovitch_body hK
