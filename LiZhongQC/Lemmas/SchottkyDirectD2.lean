import LiZhongQC.Ch11.S36_Hamilton

/-!
# Dirichlet fundamental domain of a torsion-free Fuchsian group (R82, thm32_2 direct route, D2)

`s82dx_exists_fundamentalDomain`: every torsion-free Fuchsian group has a measurable fundamental
domain with null boundary (`IsFundamentalDomainH`): the closed Dirichlet domain around any point.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- Only finitely many elements of a Fuchsian group move a point into a given ball. -/
theorem s82dx_finite_ball {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (z₀ z : UpperHalfPlane) (R : ℝ) : {γ ∈ Γ | dist (γ • z₀) z ≤ R}.Finite := by
  have hC : IsCompact (Metric.closedBall z R ∪ {z₀}) :=
    (isCompact_closedBall z R).union isCompact_singleton
  refine (hΓ _ hC).subset ?_
  rintro γ ⟨hγ, hd⟩
  refine ⟨hγ, γ • z₀, ⟨⟨z₀, Or.inr rfl, rfl⟩, Or.inl ?_⟩⟩
  exact hd

/-- A Fuchsian group is countable. -/
theorem s82dx_countable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (z₀ : UpperHalfPlane) : (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Countable := by
  have : (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) ⊆
      ⋃ n : ℕ, {γ | γ ∈ Γ ∧ dist (γ • z₀) z₀ ≤ n} := by
    intro γ hγ
    obtain ⟨n, hn⟩ := exists_nat_ge (dist (γ • z₀) z₀)
    exact mem_iUnion.mpr ⟨n, hγ, hn⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun n => ?_)
  exact (s82dx_finite_ball hΓ z₀ z₀ n).countable

/-- Equal hyperbolic distance from two points is a quadratic condition on the Euclidean coordinates. -/
theorem s82dx_bisector_eq {a b z : UpperHalfPlane} (h : dist z a = dist z b) :
    ‖(z : ℂ) - a‖ ^ 2 * b.im = ‖(z : ℂ) - b‖ ^ 2 * a.im := by
  have h1 := UpperHalfPlane.cosh_dist z a
  have h2 := UpperHalfPlane.cosh_dist z b
  rw [h, h2] at h1
  have hz := z.im_pos
  have ha := a.im_pos
  have hb := b.im_pos
  rw [Complex.dist_eq, Complex.dist_eq] at h1
  have h3 : ‖(z : ℂ) - b‖ ^ 2 / (2 * z.im * b.im) = ‖(z : ℂ) - a‖ ^ 2 / (2 * z.im * a.im) := by
    linarith
  rw [div_eq_div_iff (by positivity) (by positivity)] at h3
  have : z.im * (‖(z : ℂ) - b‖ ^ 2 * a.im - ‖(z : ℂ) - a‖ ^ 2 * b.im) * 2 = 0 := by nlinarith
  have h4 : ‖(z : ℂ) - b‖ ^ 2 * a.im - ‖(z : ℂ) - a‖ ^ 2 * b.im = 0 := by
    rcases mul_eq_zero.mp this with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 hz.ne'
      · exact h6
    · norm_num at h5
  linarith

theorem s82dx_line_null (w : ℂ) (hw : w ≠ 0) (r : ℝ) : volume {z : ℂ | (z * w).re = r} = 0 := by
  by_cases hne : ∃ z₁ : ℂ, (z₁ * w).re = r
  · obtain ⟨z₁, hz₁⟩ := hne
    let L : ℂ →ₗ[ℝ] ℝ :=
      { toFun := fun z => (z * w).re
        map_add' := by intro x y; simp [add_mul]
        map_smul' := by intro c x; simp [mul_assoc] }
    let s : AffineSubspace ℝ ℂ := AffineSubspace.mk' z₁ (LinearMap.ker L)
    have hsub : {z : ℂ | (z * w).re = r} ⊆ (s : Set ℂ) := by
      intro z hz
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker]
      show ((z -ᵥ z₁) * w).re = 0
      rw [vsub_eq_sub, sub_mul, Complex.sub_re]
      have hz' : (z * w).re = r := hz
      linarith
    have hs : s ≠ ⊤ := by
      intro htop
      have hmem : z₁ + (starRingEnd ℂ) w ∈ s := by rw [htop]; trivial
      rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at hmem
      have h1 : ((z₁ + (starRingEnd ℂ) w) -ᵥ z₁) * w = (starRingEnd ℂ) w * w := by
        rw [vsub_eq_sub]; ring
      have h2 : (((z₁ + (starRingEnd ℂ) w) -ᵥ z₁) * w).re = 0 := hmem
      rw [h1, Complex.conj_mul'] at h2
      simp only [Complex.ofReal_pow, ← Complex.ofReal_pow] at h2
      have : ‖w‖ ^ 2 = 0 := by exact_mod_cast h2
      exact hw (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this))
    exact measure_mono_null hsub (MeasureTheory.Measure.addHaar_affineSubspace volume s hs)
  · push_neg at hne
    have : {z : ℂ | (z * w).re = r} = ∅ := by
      ext z; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]; exact hne z
    rw [this, measure_empty]

theorem s82dx_circle_null (c s : ℝ) :
    volume {z : ℂ | (z.re - c) ^ 2 + z.im ^ 2 = s} = 0 := by
  by_cases hs : 0 ≤ s
  · refine measure_mono_null ?_ (MeasureTheory.Measure.addHaar_sphere volume ((c : ℂ)) (Real.sqrt s))
    intro z hz
    rw [mem_sphere_iff_norm]
    have h1 : ‖z - (c : ℂ)‖ ^ 2 = s := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hz' : (z.re - c) ^ 2 + z.im ^ 2 = s := hz
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
      nlinarith
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  · have : {z : ℂ | (z.re - c) ^ 2 + z.im ^ 2 = s} = ∅ := by
      ext z
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      nlinarith [sq_nonneg (z.re - c), sq_nonneg z.im]
    rw [this, measure_empty]

/-- The bisector of two distinct points of `ℍ`, in coordinates, is a Euclidean null set. -/
theorem s82dx_poly_bisector_null {a b : UpperHalfPlane} (hab : a ≠ b) :
    volume {z : ℂ | ‖z - a‖ ^ 2 * b.im = ‖z - b‖ ^ 2 * a.im} = 0 := by
  have hsq : ∀ z : ℂ, ∀ p : UpperHalfPlane, ‖z - p‖ ^ 2 = (z.re - p.re) ^ 2 + (z.im - p.im) ^ 2 := by
    intro z p
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  by_cases him : a.im = b.im
  · -- a line
    have hre : a.re ≠ b.re := by
      intro h
      apply hab
      apply UpperHalfPlane.ext
      exact Complex.ext h him
    set w : ℂ := (starRingEnd ℂ) ((b : ℂ) - a) with hw
    have hw0 : w ≠ 0 := by
      rw [hw]
      intro h
      have := (map_eq_zero _).mp h
      apply hre
      have h' := congrArg Complex.re this
      simp at h'
      linarith
    refine measure_mono_null ?_ (s82dx_line_null w hw0 ((b.re ^ 2 + b.im ^ 2 - a.re ^ 2 - a.im ^ 2) / 2))
    intro z hz
    have hz' : ‖z - a‖ ^ 2 * b.im = ‖z - b‖ ^ 2 * a.im := hz
    rw [hsq, hsq] at hz'
    have hbpos := b.im_pos
    have h1 : (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 = (z.re - b.re) ^ 2 + (z.im - b.im) ^ 2 := by
      have hz2 : ((z.re - a.re) ^ 2 + (z.im - a.im) ^ 2) * b.im =
          ((z.re - b.re) ^ 2 + (z.im - b.im) ^ 2) * b.im := by
        rw [hz', him]
      exact mul_right_cancel₀ hbpos.ne' hz2
    show (z * w).re = _
    rw [hw]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith
  · -- a circle centred on the real axis
    set α : ℝ := b.im - a.im with hα
    have hα0 : α ≠ 0 := by
      intro h; apply him; linarith
    set c : ℝ := (a.re * b.im - b.re * a.im) / α with hc
    set K : ℝ := a.re ^ 2 * b.im - b.re ^ 2 * a.im + a.im * b.im * (a.im - b.im) with hK
    refine measure_mono_null ?_ (s82dx_circle_null c (c ^ 2 - K / α))
    intro z hz
    have hz' : ‖z - a‖ ^ 2 * b.im = ‖z - b‖ ^ 2 * a.im := hz
    rw [hsq, hsq] at hz'
    show (z.re - c) ^ 2 + z.im ^ 2 = c ^ 2 - K / α
    have key : α * ((z.re - c) ^ 2 + z.im ^ 2) = α * c ^ 2 - K := by
      have : α * c = a.re * b.im - b.re * a.im := by
        rw [hc]; field_simp
      calc α * ((z.re - c) ^ 2 + z.im ^ 2)
          = α * (z.re ^ 2 + z.im ^ 2) - 2 * z.re * (α * c) + α * c ^ 2 := by ring
        _ = α * (z.re ^ 2 + z.im ^ 2) - 2 * z.re * (a.re * b.im - b.re * a.im) + α * c ^ 2 := by
          rw [this]
        _ = α * c ^ 2 - K := by
          simp only [hα, hK]
          linear_combination hz'
    field_simp
    nlinarith [key]

theorem s82dx_dist_le_iff (z a b : UpperHalfPlane) :
    dist z a ≤ dist z b ↔ ‖(z : ℂ) - a‖ ^ 2 * b.im ≤ ‖(z : ℂ) - b‖ ^ 2 * a.im := by
  have hz := z.im_pos
  have ha := a.im_pos
  have hb := b.im_pos
  rw [← abs_of_nonneg (dist_nonneg : 0 ≤ dist z a), ← abs_of_nonneg (dist_nonneg : 0 ≤ dist z b),
    ← Real.cosh_le_cosh, UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist, Complex.dist_eq,
    Complex.dist_eq]
  rw [add_le_add_iff_left, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℝ) < 2 * z.im := by positivity
  constructor
  · intro h
    have h' : (‖(z : ℂ) - a‖ ^ 2 * b.im) * (2 * z.im) ≤ (‖(z : ℂ) - b‖ ^ 2 * a.im) * (2 * z.im) := by
      linarith [h]
    exact le_of_mul_le_mul_right h' h2
  · intro h
    have h' := mul_le_mul_of_nonneg_right h h2.le
    linarith [h']

/-- The Dirichlet domain of a torsion-free Fuchsian group, as a subset of `ℂ`. -/
theorem s82dx_dirichlet {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) :
    ∃ F : Set ℂ, F ⊆ upperHalf ∧ MeasurableSet F ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F → (τ₂ : ℂ) ∈ interior F →
        (∃ γ ∈ Γ, γ • τ₁ = τ₂) → τ₁ = τ₂) ∧
      volume (F \ interior F) = 0 := by
  classical
  let z₀ : UpperHalfPlane := ⟨Complex.I, by simp⟩
  let D : Set UpperHalfPlane := {w | ∀ γ ∈ Γ, dist w z₀ ≤ dist w (γ • z₀)}
  let F : Set ℂ := UpperHalfPlane.coe '' D
  have hmove : ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → γ • z₀ ≠ z₀ := by
    intro γ hγ h1 h2 h
    rcases hfree γ hγ z₀ h with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hneg1 : ∀ τ : UpperHalfPlane, (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have hcount := s82dx_countable hΓ z₀
  -- the null set of bisectors
  let N : Set ℂ := ⋃ γ ∈ {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧ γ • z₀ ≠ z₀},
    {z : ℂ | ‖z - z₀‖ ^ 2 * (γ • z₀).im = ‖z - ((γ • z₀ : UpperHalfPlane) : ℂ)‖ ^ 2 * z₀.im}
  have hN : volume N = 0 := by
    refine (measure_biUnion_null_iff (hcount.mono (s₁ := {γ | γ ∈ Γ ∧ γ • z₀ ≠ z₀}) fun γ hγ => hγ.1)).2 ?_
    intro γ hγ
    exact s82dx_poly_bisector_null (a := z₀) (b := γ • z₀) (Ne.symm hγ.2)
  -- membership in `N`
  have hNmem : ∀ (w : UpperHalfPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ ∈ Γ →
      γ • z₀ ≠ z₀ → dist w z₀ = dist w (γ • z₀) → (w : ℂ) ∈ N := by
    intro w γ hγ hne h
    refine mem_iUnion₂.mpr ⟨γ, ⟨hγ, hne⟩, ?_⟩
    exact s82dx_bisector_eq h
  -- strictness off the null set
  have hstrict : ∀ w ∈ D, (w : ℂ) ∉ N → ∀ γ ∈ Γ, γ • z₀ ≠ z₀ →
      dist w z₀ < dist w (γ • z₀) := by
    intro w hw hwN γ hγ hne
    refine lt_of_le_of_ne (hw γ hγ) fun h => hwN (hNmem w γ hγ hne h)
  -- local finiteness
  have hint : ∀ w : UpperHalfPlane, (∀ γ ∈ Γ, γ • z₀ ≠ z₀ → dist w z₀ < dist w (γ • z₀)) →
      D ∈ 𝓝 w := by
    intro w hs
    set S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
      {γ | γ ∈ Γ ∧ dist (γ • z₀) w ≤ dist w z₀ + 1} with hS
    have hSfin : S.Finite := s82dx_finite_ball hΓ z₀ w (dist w z₀ + 1)
    have h1 : ∀ᶠ w' in 𝓝 w, ∀ γ ∈ S, γ • z₀ ≠ z₀ → dist w' z₀ < dist w' (γ • z₀) := by
      rw [Filter.eventually_all_finite hSfin]
      intro γ hγ
      by_cases hz : γ • z₀ = z₀
      · exact Filter.Eventually.of_forall fun _ h => absurd hz h
      · have hopen : IsOpen {w' : UpperHalfPlane | dist w' z₀ < dist w' (γ • z₀)} :=
          isOpen_lt (by fun_prop) (by fun_prop)
        have hmem : {w' : UpperHalfPlane | dist w' z₀ < dist w' (γ • z₀)} ∈ 𝓝 w :=
          hopen.mem_nhds (hs γ hγ.1 hz)
        filter_upwards [hmem] with w' hw' _ using hw'
    have h2 : ∀ᶠ w' in 𝓝 w, dist w' w < 1 / 2 := Metric.ball_mem_nhds w (by norm_num)
    filter_upwards [h1, h2] with w' hw1 hw2
    intro δ hδ
    by_cases hδS : δ ∈ S
    · by_cases hz : δ • z₀ = z₀
      · rw [hz]
      · exact (hw1 δ hδS hz).le
    · have hbig : dist w z₀ + 1 < dist (δ • z₀) w := by
        by_contra hc
        exact hδS ⟨hδ, not_lt.mp hc⟩
      have t1 := dist_triangle w' w z₀
      have t2 := dist_triangle w (w') (δ • z₀)
      rw [dist_comm w' w] at t1
      rw [dist_comm (δ • z₀) w] at hbig
      rw [dist_comm w w'] at t2
      have hsym := dist_comm w w'
      linarith
  -- interior membership
  have hinterior : ∀ w ∈ D, (w : ℂ) ∉ N → (w : ℂ) ∈ interior F := by
    intro w hw hwN
    rw [mem_interior_iff_mem_nhds]
    show UpperHalfPlane.coe '' D ∈ 𝓝 (w : ℂ)
    exact UpperHalfPlane.isOpenEmbedding_coe.image_mem_nhds.2
      (hint w fun γ hγ hne => hstrict w hw hwN γ hγ hne)
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.im_pos
  · -- measurability
    have hFeq : F = upperHalf ∩ ⋂ γ ∈ (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
        {z : ℂ | ‖z - z₀‖ ^ 2 * (γ • z₀).im ≤ ‖z - ((γ • z₀ : UpperHalfPlane) : ℂ)‖ ^ 2 * z₀.im} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.im_pos, ?_⟩
        simp only [mem_iInter]
        intro γ hγ
        exact (s82dx_dist_le_iff w z₀ (γ • z₀)).1 (hw γ hγ)
      · rintro ⟨hz, hz'⟩
        simp only [mem_iInter] at hz'
        refine ⟨⟨z, hz⟩, ?_, rfl⟩
        intro γ hγ
        exact (s82dx_dist_le_iff ⟨z, hz⟩ z₀ (γ • z₀)).2 (hz' γ hγ)
    rw [hFeq]
    refine isOpen_upperHalf.measurableSet.inter (MeasurableSet.biInter hcount fun γ _ => ?_)
    exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · -- every orbit meets `F`
    intro τ
    set R := dist τ z₀ with hR
    have hfin : {γ ∈ Γ | dist (γ • τ) z₀ ≤ R}.Finite := s82dx_finite_ball hΓ τ z₀ R
    obtain ⟨γ₀, hγ₀, hmin⟩ := Set.exists_min_image {γ ∈ Γ | dist (γ • τ) z₀ ≤ R}
      (fun γ => dist (γ • τ) z₀) hfin ⟨1, Γ.one_mem, by simp [hR]⟩
    refine ⟨γ₀, hγ₀.1, γ₀ • τ, ?_, rfl⟩
    intro δ hδ
    have h1 : dist (γ₀ • τ) (δ • z₀) = dist ((δ⁻¹ * γ₀) • τ) z₀ := by
      rw [← dist_smul δ⁻¹, ← mul_smul, inv_smul_smul]
    rw [h1]
    by_cases hmem : δ⁻¹ * γ₀ ∈ {γ ∈ Γ | dist (γ • τ) z₀ ≤ R}
    · exact hmin _ hmem
    · have : R < dist ((δ⁻¹ * γ₀) • τ) z₀ := by
        by_contra hc
        exact hmem ⟨Γ.mul_mem (Γ.inv_mem hδ) hγ₀.1, not_lt.mp hc⟩
      linarith [hγ₀.2]
  · -- injectivity on the interior
    rintro τ₁ τ₂ h1 h2 ⟨γ, hγ, hτ⟩
    by_cases hγ1 : γ = 1 ∨ γ = -1
    · rcases hγ1 with rfl | rfl
      · simpa using hτ
      · rw [hneg1] at hτ
        exact hτ
    · push_neg at hγ1
      by_contra hne
      let W : Set UpperHalfPlane := {τ | (τ : ℂ) ∈ interior F ∧ ((γ • τ : UpperHalfPlane) : ℂ) ∈ interior F}
      have hWo : IsOpen W :=
        (isOpen_interior.preimage UpperHalfPlane.continuous_coe).inter
          (isOpen_interior.preimage (UpperHalfPlane.continuous_coe.comp (continuous_const_smul γ)))
      have hWne : τ₁ ∈ W := ⟨h1, by rw [hτ]; exact h2⟩
      have hopen : IsOpen (UpperHalfPlane.coe '' W) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hWo
      have hpos : 0 < volume (UpperHalfPlane.coe '' W) :=
        hopen.measure_pos volume ⟨_, ⟨τ₁, hWne, rfl⟩⟩
      have hnot : ¬ (UpperHalfPlane.coe '' W ⊆ N) := by
        intro hsub
        have := measure_mono_null hsub hN
        rw [this] at hpos
        exact lt_irrefl _ hpos
      obtain ⟨_, ⟨w, hw, rfl⟩, hwN⟩ := not_subset.mp hnot
      have hwD : w ∈ D := by
        obtain ⟨v, hv, hvw⟩ := interior_subset hw.1
        have : v = w := UpperHalfPlane.ext hvw
        rwa [← this]
      have hgwD : γ • w ∈ D := by
        obtain ⟨v, hv, hvw⟩ := interior_subset hw.2
        have : v = γ • w := UpperHalfPlane.ext hvw
        rwa [← this]
      have hγinv : γ⁻¹ ∈ Γ := Γ.inv_mem hγ
      have hne1 : γ⁻¹ ≠ 1 := by simpa using hγ1.1
      have hne2 : γ⁻¹ ≠ -1 := by
        intro h
        apply hγ1.2
        have := congrArg (fun x => x⁻¹) h
        simpa using this
      have hmv := hmove γ⁻¹ hγinv hne1 hne2
      have h3 : dist w (γ⁻¹ • z₀) = dist (γ • w) z₀ := by
        rw [← dist_smul γ, smul_inv_smul]
      have e1 : dist w z₀ ≤ dist (γ • w) z₀ := by
        have := hwD γ⁻¹ hγinv
        linarith
      have e2 : dist (γ • w) z₀ ≤ dist w z₀ := by
        have := hgwD γ hγ
        rwa [dist_smul] at this
      exact hwN (hNmem w γ⁻¹ hγinv hmv (by linarith))
  · -- the boundary is null
    refine measure_mono_null ?_ hN
    intro z hz
    obtain ⟨⟨w, hw, rfl⟩, hnint⟩ := hz
    by_contra hwN
    exact hnint (hinterior w hw hwN)

/-- **[D2] A measurable fundamental domain with null boundary** for any torsion-free Fuchsian group
(Dirichlet domain). -/
theorem s82dx_exists_fundamentalDomain {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) : ∃ F : Set ℂ, IsFundamentalDomainH Γ F := by
  obtain ⟨F, h1, h2, h3, h4, h5⟩ := s82dx_dirichlet hΓ hfree
  exact ⟨F, h1, h2, h3, h4, h5⟩

end LiZhongQC
