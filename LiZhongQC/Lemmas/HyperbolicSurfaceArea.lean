import LiZhongQC.Lemmas.HyperbolicAreaFundamentalDomain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- A fixed extension of the covering projection; its values off the upper
half-plane will not affect any measure restricted to a fundamental domain. -/
def s22gm_projectionExtension {S : Type*} (p : UpperHalfPlane → S) : ℂ → S :=
  fun z => p (UpperHalfPlane.ofComplex z)

/-- Hyperbolic density on a specified complex set, as an extended measure. -/
def s22gm_areaOn (F : Set ℂ) : Measure ℂ :=
  (volume.restrict F).withDensity (fun z => ENNReal.ofReal (1 / z.im ^ 2))

/-- Pushforward area, on the Borel sigma algebra of the surface. Fundamental
domain independence is proved below; no area value or finiteness is built in. -/
def s22gm_surfaceArea {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (p : UpperHalfPlane → S) (F : Set ℂ) : Measure S :=
  Measure.map (s22gm_projectionExtension p) (s22gm_areaOn F)

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

theorem s22gm_projectionExtension_coe (p : UpperHalfPlane → S) (τ : UpperHalfPlane) :
    s22gm_projectionExtension p (τ : ℂ) = p τ := by
  change p (UpperHalfPlane.ofComplex (τ : ℂ)) = p τ
  rw [UpperHalfPlane.ofComplex_apply]

theorem s22gm_projectionExtension_continuousOn {p : UpperHalfPlane → S} (hp : Continuous p) :
    ContinuousOn (s22gm_projectionExtension p) upperHalf := by
  intro z hz
  exact (hp.continuousAt.comp
    (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt).continuousWithinAt

theorem s22gm_projectionExtension_measurable {p : UpperHalfPlane → S} (hp : Continuous p) :
    Measurable (s22gm_projectionExtension p) := by
  classical
  have hH := s22gm_projectionExtension_continuousOn hp
  have hC : ContinuousOn (s22gm_projectionExtension p) upperHalfᶜ := by
    have heq : EqOn (s22gm_projectionExtension p)
        (fun _ : ℂ => p (UpperHalfPlane.ofComplex (0 : ℂ))) upperHalfᶜ := by
      intro z hz
      change p (UpperHalfPlane.ofComplex z) = p (UpperHalfPlane.ofComplex (0 : ℂ))
      apply congrArg p
      exact UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (le_of_not_gt hz) (by simp)
    exact continuousOn_const.congr heq
  simpa only [Set.piecewise_same] using
    hH.measurable_piecewise hC isOpen_upperHalf.measurableSet

/-- Arbitrary changes to the density off the upper half-plane disappear after
restriction to a measurable subset of the upper half-plane. -/
theorem s22gm_density_extension_congr {F : Set ℂ} (hFm : MeasurableSet F)
    (hFH : F ⊆ upperHalf) {r : ℂ → ℝ≥0∞}
    (hr : ∀ z ∈ upperHalf, r z = ENNReal.ofReal (1 / z.im ^ 2)) :
    (volume.restrict F).withDensity r = s22gm_areaOn F := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hFm] with z hz
  exact hr z (hFH hz)

/-- Arbitrary extensions of p agreeing on the upper half-plane give the same
pushforward; no off-domain measurability is needed for this a.e. congruence. -/
theorem s22gm_projection_extension_congr {F : Set ℂ} (hFm : MeasurableSet F)
    (hFH : F ⊆ upperHalf) {q₁ q₂ : ℂ → S}
    (hq : ∀ z ∈ upperHalf, q₁ z = q₂ z) :
    Measure.map q₁ (s22gm_areaOn F) = Measure.map q₂ (s22gm_areaOn F) := by
  apply Measure.map_congr
  apply (withDensity_absolutelyContinuous (volume.restrict F)
    (fun z => ENNReal.ofReal (1 / z.im ^ 2))).ae_eq
  filter_upwards [ae_restrict_mem hFm] with z hz
  exact hq z (hFH hz)

theorem s22gm_projectionExtension_invariant [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    s22gm_projectionExtension p (h36p_m γ z) = s22gm_projectionExtension p z := by
  have he := h36p_m_coe γ ⟨z, hz⟩
  simp only at he
  rw [he, s22gm_projectionExtension_coe]
  change p (γ • (⟨z, hz⟩ : UpperHalfPlane)) = p (UpperHalfPlane.ofComplex z)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact ((hp.2.2.2 ⟨z, hz⟩ (γ • (⟨z, hz⟩ : UpperHalfPlane))).2 ⟨γ, hγ, rfl⟩).symm

/-- A test function pulled back from the surface preserves density covariance. -/
theorem s22gm_test_density_covariant [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (f : S → ℝ≥0∞)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (f (s22gm_projectionExtension p (h36p_m γ z)) *
        ENNReal.ofReal (1 / (h36p_m γ z).im ^ 2)) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2) := by
  rw [s22gm_projectionExtension_invariant hp hγ hz, mul_assoc,
    s22ga_hyperbolic_density_covariant γ hz]

theorem s22gm_lintegral_surfaceArea {p : UpperHalfPlane → S} (hp : Continuous p)
    (F : Set ℂ) {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in F, f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2) := by
  have hq := s22gm_projectionExtension_measurable hp
  change (∫⁻ y, f y ∂Measure.map (s22gm_projectionExtension p)
    ((volume.restrict F).withDensity (fun z => ENNReal.ofReal (1 / z.im ^ 2)))) = _
  have hr : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)) := by fun_prop
  rw [lintegral_map hf hq]
  simpa only [Function.comp_apply, Pi.mul_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul (volume.restrict F) hr (hf.comp hq))

/-- Equality against every nonnegative measurable test function gives equality
of the pushed Borel measures, not merely equality of their total masses. -/
theorem s22gm_surfaceArea_eq [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F G : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (hG : IsFundamentalDomainH Γ G) :
    s22gm_surfaceArea p F = s22gm_surfaceArea p G := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [s22gm_lintegral_surfaceArea hp.1.continuous F hf,
    s22gm_lintegral_surfaceArea hp.1.continuous G hf]
  apply s22ga_lintegral_eq_of_covariant (utm_x2_isFuchsian hp) hF hG
  · exact (hf.comp (s22gm_projectionExtension_measurable hp.1.continuous)).mul (by fun_prop)
  · intro γ hγ z hz
    exact s22gm_test_density_covariant hp f hγ hz

theorem s22gm_surfaceArea_univ {p : UpperHalfPlane → S} (hp : Continuous p) (F : Set ℂ) :
    s22gm_surfaceArea p F Set.univ = ∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2) := by
  simpa only [lintegral_one, one_mul] using
    (s22gm_lintegral_surfaceArea hp F (f := fun _ => 1) measurable_const)

/-- Partial tiling for a single injective sheet. A full fundamental domain is
used only to obtain the a.e. uniqueness up to the actual SL kernel. -/
theorem s22gm_partial_tiling [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hUH : U ⊆ upperHalf)
    (hinj : InjOn (s22gm_projectionExtension p) U) (w : ℂ → ℝ≥0∞) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      (∑' γ : Γ, (h36p_m γ.1 ⁻¹' U).indicator w z) =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) *
          (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z := by
  classical
  filter_upwards [h36p_ae_unique hΓ hF,
    ae_restrict_mem isOpen_upperHalf.measurableSet] with z hu hz
  by_cases hex : s22gm_projectionExtension p z ∈ s22gm_projectionExtension p '' U
  · rw [indicator_of_mem
      (show z ∈ s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U) from hex)]
    obtain ⟨v, hv, hvz⟩ := hex
    have hpzv : p (⟨z, hz⟩ : UpperHalfPlane) = p (⟨v, hUH hv⟩ : UpperHalfPlane) := by
      simpa only [s22gm_projectionExtension, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        UpperHalfPlane.ofComplex_apply_of_im_pos (hUH hv)] using hvz.symm
    obtain ⟨γ₀, hγ₀, hγ₀v⟩ := (hp.2.2.2 ⟨z, hz⟩ ⟨v, hUH hv⟩).1 hpzv
    have hγ₀z : h36p_m γ₀ z = v := by
      have he := h36p_m_coe γ₀ ⟨z, hz⟩
      rw [hγ₀v] at he
      exact he
    have hγ₀U : h36p_m γ₀ z ∈ U := hγ₀z.symm ▸ hv
    obtain ⟨δ, hδ, hδF⟩ := hF.2.2.1 ⟨v, hUH hv⟩
    have hδvF : h36p_m δ v ∈ F := by
      have he := h36p_m_coe δ ⟨v, hUH hv⟩
      simp only at he
      rw [he]
      exact hδF
    have hδγ₀F : h36p_m (δ * γ₀) z ∈ F := by
      rw [h36p_b_m_mul δ γ₀ hz, hγ₀z]
      exact hδvF
    have hrw : ∀ γ : Γ, (h36p_m γ.1 ⁻¹' U).indicator w z =
        {γ : Γ | h36p_m γ.1 z ∈ U}.indicator (fun _ => w z) γ := by
      intro γ
      by_cases h : h36p_m γ.1 z ∈ U
      · rw [indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' U from h),
          indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 z ∈ U} from h)]
      · rw [indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' U from h),
          indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 z ∈ U} from h)]
    rw [tsum_congr hrw]
    apply h36p_a_count (P := fun γ => h36p_m γ z ∈ U) hγ₀
    intro γ hγ
    constructor
    · intro hγU
      have heq : h36p_m γ z = h36p_m γ₀ z := hinj hγU hγ₀U
        ((s22gm_projectionExtension_invariant hp hγ hz).trans
          (s22gm_projectionExtension_invariant hp hγ₀ hz).symm)
      have hδγF : h36p_m (δ * γ) z ∈ F := by
        rw [h36p_b_m_mul δ γ hz, heq, hγ₀z]
        exact hδvF
      rcases hu (δ * γ) (Γ.mul_mem hδ hγ) (δ * γ₀) (Γ.mul_mem hδ hγ₀)
        hδγF hδγ₀F with h | h
      · exact Or.inl (mul_left_cancel h)
      · exact Or.inr (mul_left_cancel
          (show δ * γ = δ * -γ₀ by simpa only [mul_neg] using h))
    · rintro (rfl | rfl)
      · exact hγ₀U
      · rw [h36p_a_m_neg]
        exact hγ₀U
  · rw [indicator_of_notMem
      (show z ∉ s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U) from hex),
      mul_zero]
    calc
      _ = ∑' γ : Γ, (0 : ℝ≥0∞) := by
        apply tsum_congr
        intro γ
        apply indicator_of_notMem
        intro h
        exact hex ⟨h36p_m γ.1 z, h, s22gm_projectionExtension_invariant hp γ.2 hz⟩
      _ = 0 := by simp

/-- Unfolding over a partial injective sheet, still with the positive finite SL
kernel factor explicitly present until the last cancellation. -/
theorem s22gm_lintegral_partial_sheet [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hU : MeasurableSet U)
    (hUH : U ⊆ upperHalf) (hinj : InjOn (s22gm_projectionExtension p) U)
    {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (hcov : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      w (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = w z) :
    (∫⁻ z in F,
      (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z) =
      ∫⁻ z in U, w z := by
  classical
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  let m : ℝ≥0∞ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have hmfin : m ≠ ⊤ := ENNReal.natCast_ne_top _
  have hterm (γ : Γ) :
      (∫⁻ z in F, U.indicator w (h36p_m γ.1 z) *
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)) =
      ∫⁻ z in F, (h36p_m γ.1 ⁻¹' U).indicator w z := by
    refine setLIntegral_congr_fun hF.2.1 fun z hz => ?_
    by_cases h : h36p_m γ.1 z ∈ U
    · rw [indicator_of_mem h,
        indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' U from h)]
      exact hcov γ.1 γ.2 z (hF.1 hz)
    · rw [indicator_of_notMem h,
        indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' U from h), zero_mul]
  have hsum :
      (∑' γ : Γ, ∫⁻ z in F, U.indicator w (h36p_m γ.1 z) *
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)) =
      m * ∫⁻ z in F,
        (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z := by
    calc
      _ = ∑' γ : Γ, ∫⁻ z in F, (h36p_m γ.1 ⁻¹' U).indicator w z :=
        tsum_congr hterm
      _ = ∫⁻ z in F, ∑' γ : Γ, (h36p_m γ.1 ⁻¹' U).indicator w z :=
        (lintegral_tsum fun γ : Γ =>
          (hw.indicator (h36p_m_measurable γ.1 hU)).aemeasurable).symm
      _ = ∫⁻ z in F, m *
          (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z :=
        lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hF.1
          (s22gm_partial_tiling hp hΓ hF hUH hinj w))
      _ = _ := lintegral_const_mul' _ _ hmfin
  have hbalance := hsum.symm.trans (h36p_unfold hΓ hF (hw.indicator hU))
  rw [setLIntegral_indicator hU, inter_eq_left.2 hUH] at hbalance
  change m * (∫⁻ z in F,
    (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z) =
    m * (∫⁻ z in U, w z) at hbalance
  have hcancel := congrArg (fun x : ℝ≥0∞ => m⁻¹ * x) hbalance
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmfin, one_mul] using hcancel

/-- Local integration on any measurable injective sheet with measurable image. -/
theorem s22gm_lintegral_local [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hU : MeasurableSet U)
    (hUH : U ⊆ upperHalf) (hinj : InjOn (s22gm_projectionExtension p) U)
    (himage : MeasurableSet (s22gm_projectionExtension p '' U))
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' U, f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2) := by
  classical
  let w : ℂ → ℝ≥0∞ := fun z =>
    f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2)
  have hw : Measurable w :=
    (hf.comp (s22gm_projectionExtension_measurable hp.1.continuous)).mul (by fun_prop)
  rw [← lintegral_indicator himage,
    s22gm_lintegral_surfaceArea hp.1.continuous F (hf.indicator himage)]
  calc
    _ = ∫⁻ z in F,
        (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' U)).indicator w z := by
      refine setLIntegral_congr_fun hF.2.1 fun z _ => ?_
      by_cases hz : s22gm_projectionExtension p z ∈ s22gm_projectionExtension p '' U
      · rw [indicator_of_mem hz,
          indicator_of_mem (show z ∈ s22gm_projectionExtension p ⁻¹'
            (s22gm_projectionExtension p '' U) from hz)]
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (show z ∉ s22gm_projectionExtension p ⁻¹'
            (s22gm_projectionExtension p '' U) from hz), zero_mul]
    _ = ∫⁻ z in U, w z :=
      s22gm_lintegral_partial_sheet hp (utm_x2_isFuchsian hp) hF hU hUH hinj hw
        (fun γ hγ z hz => s22gm_test_density_covariant hp f hγ hz)

theorem s22gm_projectionExtension_image_isOpen [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ upperHalf) :
    IsOpen (s22gm_projectionExtension p '' U) := by
  have heq : s22gm_projectionExtension p '' U = p '' (UpperHalfPlane.coe ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hUH hz⟩, hz, ?_⟩
      change p (⟨z, hUH hz⟩ : UpperHalfPlane) = p (UpperHalfPlane.ofComplex z)
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUH hz)]
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(τ : ℂ), hτ, s22gm_projectionExtension_coe p τ⟩
  rw [heq]
  exact hp.1.isOpenMap _ (hU.preimage UpperHalfPlane.continuous_coe)

/-- The covering-sheet formula in complex upper-half-plane coordinates. The
image is Borel because the projection is an open covering map. -/
theorem s22gm_lintegral_open_sheet [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F U : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hU : IsOpen U)
    (hUH : U ⊆ upperHalf) (hinj : InjOn (s22gm_projectionExtension p) U)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in s22gm_projectionExtension p '' U, f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in U, f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2) :=
  s22gm_lintegral_local hp hF hU.measurableSet hUH hinj
    (s22gm_projectionExtension_image_isOpen hp hU hUH).measurableSet hf

/-- The same local formula stated directly for an open injective covering
sheet V in the upper half-plane, with the literal surface projection p. -/
theorem s22gm_lintegral_covering_sheet [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {V : Set UpperHalfPlane} (hV : IsOpen V) (hinj : InjOn p V)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y in p '' V, f y ∂s22gm_surfaceArea p F) =
      ∫⁻ z in UpperHalfPlane.coe '' V,
        f (s22gm_projectionExtension p z) * ENNReal.ofReal (1 / z.im ^ 2) := by
  have hU : IsOpen (UpperHalfPlane.coe '' V) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hV
  have hUH : UpperHalfPlane.coe '' V ⊆ upperHalf := by
    rintro z ⟨τ, _, rfl⟩
    exact τ.coe_im_pos
  have hi : InjOn (s22gm_projectionExtension p) (UpperHalfPlane.coe '' V) := by
    rintro z ⟨τ, hτ, rfl⟩ w ⟨σ, hσ, rfl⟩ heq
    exact congrArg UpperHalfPlane.coe (hinj hτ hσ
      (by simpa only [s22gm_projectionExtension_coe] using heq))
  have himage : s22gm_projectionExtension p '' (UpperHalfPlane.coe '' V) = p '' V := by
    simp only [Set.image_image, s22gm_projectionExtension_coe]
  simpa only [himage] using s22gm_lintegral_open_sheet hp hF hU hUH hi hf

/-- On an injective covering sheet, the surface measure restricts exactly to
the pushforward of hyperbolic density on that sheet. -/
theorem s22gm_surfaceArea_restrict_sheet [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {V : Set UpperHalfPlane} (hV : IsOpen V) (hinj : InjOn p V) :
    (s22gm_surfaceArea p F).restrict (p '' V) =
      s22gm_surfaceArea p (UpperHalfPlane.coe '' V) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [s22gm_lintegral_covering_sheet hp hF hV hinj hf,
    s22gm_lintegral_surfaceArea hp.1.continuous (UpperHalfPlane.coe '' V) hf]

end LiZhongQC


