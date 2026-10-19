import LiZhongQC.Lemmas.StrebelGammaBounds

/-! Setwise QC and square-root integral bounds for E6.
Source-only producer. No new global definitions or instances.
Existing str_* geometry and s36g_* pointwise estimates are imported, not redeclared. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A QC self-homeomorphism of H maps open subsets of H to plane-open sets. -/
theorem s36e_qc_image_open {g : ℂ → ℂ} {K : ℝ}
    (hgK : IsKQC g upperHalf K) (hgimg : g '' upperHalf = upperHalf)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ upperHalf) :
    IsOpen (g '' U) := by
  have hinj : InjOn g upperHalf := hgK.2.2.1.2.1
  have hc : ContinuousOn (Function.invFunOn g upperHalf) upperHalf := by
    simpa only [hgimg] using hgK.2.2.1.2.2.2
  have heq : g '' U = upperHalf ∩ (Function.invFunOn g upperHalf) ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hgimg ▸ mem_image_of_mem g (hUH hw), ?_⟩
      change Function.invFunOn g upperHalf (g w) ∈ U
      rw [hinj.leftInvOn_invFunOn (hUH hw)]
      exact hw
    · intro hz
      obtain ⟨w, hw, hwz⟩ : z ∈ g '' upperHalf := by rw [hgimg]; exact hz.1
      have he : Function.invFunOn g upperHalf z = w := by
        rw [← hwz]
        exact hinj.leftInvOn_invFunOn hw
      have h2 : Function.invFunOn g upperHalf z ∈ U := hz.2
      rw [he] at h2
      exact ⟨w, h2, hwz⟩
  rw [heq]
  exact hc.isOpen_inter_preimage isOpen_upperHalf hU

/-- Interior membership pulls back through the actual QC homeomorphism. -/
theorem s36e_qc_preimage_interior {g : ℂ → ℂ} {K : ℝ}
    (hgK : IsKQC g upperHalf K) {F : Set ℂ} (hFH : F ⊆ upperHalf)
    {z : ℂ} (hz : z ∈ upperHalf) (hgz : g z ∈ interior (g '' F)) :
    z ∈ interior F := by
  have hinj : InjOn g upperHalf := hgK.2.2.1.2.1
  have hU : IsOpen (upperHalf ∩ g ⁻¹' interior (g '' F)) :=
    hgK.2.2.1.1.isOpen_inter_preimage isOpen_upperHalf isOpen_interior
  have hUF : upperHalf ∩ g ⁻¹' interior (g '' F) ⊆ F := by
    intro w hw
    exact (hinj.mem_image_iff hFH hw.1).1 (interior_subset hw.2)
  exact mem_interior_iff_mem_nhds.2
    (Filter.mem_of_superset (hU.mem_nhds ⟨hz, hgz⟩) hUF)

/-- A commuting QC self-homeomorphism carries the full fundamental-domain data
to its image; boundary nullity uses the QC N-property. -/
theorem s36e_image_domain {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    (hcomm : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, g (h36p_m γ z) = h36p_m γ (g z)) :
    IsFundamentalDomainH Γ (g '' F) := by
  have hinj : InjOn g upperHalf := hgK.2.2.1.2.1
  have hEH : g '' F ⊆ upperHalf := hgimg ▸ image_mono hF.1
  have hEm : MeasurableSet (g '' F) :=
    hF.2.1.image_of_continuousOn_injOn (hgK.2.2.1.1.mono hF.1) (hinj.mono hF.1)
  refine ⟨hEH, hEm, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨z, hz, hgz⟩ : (τ : ℂ) ∈ g '' upperHalf := by
      rw [hgimg]
      exact τ.im_pos
    obtain ⟨γ, hγ, hγF⟩ := hF.2.2.1 ⟨z, hz⟩
    refine ⟨γ, hγ, h36p_m γ z, ?_, ?_⟩
    · rwa [h36p_m_coe γ ⟨z, hz⟩]
    · rw [hcomm γ hγ z hz, hgz, h36p_m_coe γ τ]
  · intro τ₁ τ₂ hτ₁ hτ₂ hrel
    obtain ⟨x, hx, hxeq⟩ := interior_subset hτ₁
    obtain ⟨y, hy, hyeq⟩ := interior_subset hτ₂
    have hxH := hF.1 hx
    have hyH := hF.1 hy
    have hxint : x ∈ interior F :=
      s36e_qc_preimage_interior hgK hF.1 hxH (by rwa [hxeq])
    have hyint : y ∈ interior F :=
      s36e_qc_preimage_interior hgK hF.1 hyH (by rwa [hyeq])
    obtain ⟨γ, hγ, hγτ⟩ := hrel
    have hxy : h36p_m γ x = y := by
      apply hinj (h36p_m_mem γ hxH) hyH
      rw [hcomm γ hγ x hxH, hxeq, hyeq, h36p_m_coe γ τ₁, hγτ]
    have hxyH : (⟨x, hxH⟩ : UpperHalfPlane) = ⟨y, hyH⟩ := by
      apply hF.2.2.2.1 _ _ hxint hyint
      refine ⟨γ, hγ, ?_⟩
      apply UpperHalfPlane.ext
      rw [← h36p_m_coe γ ⟨x, hxH⟩]
      exact hxy
    apply UpperHalfPlane.ext
    calc (τ₁ : ℂ) = g x := hxeq.symm
      _ = g y := congrArg g (congrArg UpperHalfPlane.coe hxyH)
      _ = (τ₂ : ℂ) := hyeq
  · have hbad : (g '' F) \ interior (g '' F) ⊆ g '' (F \ interior F) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz.1
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hxint
      apply hz.2
      have hopen := s36e_qc_image_open hgK hgimg isOpen_interior
        (interior_subset.trans hF.1)
      exact mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset (hopen.mem_nhds ⟨x, hxint, rfl⟩)
          (image_mono interior_subset))
    exact measure_mono_null hbad
      (ac_n_volume_image_null_of_isKQC hgK (diff_subset.trans hF.1) hF.2.2.2.2)

/-- QC area change on an arbitrary measurable subset, without automorphy. -/
theorem s36e_area_image {E : Set ℂ} (hEm : MeasurableSet E) (hEH : E ⊆ upperHalf)
    {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf) (α : ℂ → ℂ) :
    (∫⁻ z in E, ENNReal.ofReal (‖α (g z)‖ * jacobian g z)) = phiArea α (g '' E) := by
  have hinj : InjOn g upperHalf := hgK.2.2.1.2.1
  have hgm : MeasurableSet (g '' E) :=
    hEm.image_of_continuousOn_injOn (hgK.2.2.1.1.mono hEH) (hinj.mono hEH)
  have hgEH : g '' E ⊆ upperHalf := hgimg ▸ image_mono hEH
  have hcv := fx_lintegral_image_eq hgK ((g '' E).indicator (fun w => ENNReal.ofReal ‖α w‖))
  rw [hgimg, setLIntegral_indicator hgm, inter_eq_left.2 hgEH] at hcv
  rw [phiArea, hcv]
  have hind : ∀ z ∈ upperHalf, ENNReal.ofReal (jacobian g z) *
      (g '' E).indicator (fun w => ENNReal.ofReal ‖α w‖) (g z) =
      E.indicator (fun z => ENNReal.ofReal (‖α (g z)‖ * jacobian g z)) z := by
    intro z hz
    by_cases hzE : z ∈ E
    · rw [indicator_of_mem (mem_image_of_mem g hzE), indicator_of_mem hzE,
        ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
    · have hn : g z ∉ g '' E := fun h => hzE ((hinj.mem_image_iff hEH hz).1 h)
      rw [indicator_of_notMem hn, indicator_of_notMem hzE, mul_zero]
  rw [setLIntegral_congr_fun isOpen_upperHalf.measurableSet hind,
    setLIntegral_indicator hEm, inter_eq_left.2 hEH]

/-- Setwise Holder estimate. The target L1 norm is taken on g(F); neither
function is assumed automorphic under any group. -/
theorem s36e_holder_on {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    {α β : ℂ → ℂ} (hα : DifferentiableOn ℂ α upperHalf)
    (hβ : DifferentiableOn ℂ β upperHalf) :
    (∫⁻ z in F, ENNReal.ofReal ((‖dz g z‖ + ‖dzbar g z‖) *
      Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖)) ≤
      ENNReal.ofReal (Real.sqrt K) * phiArea α (g '' F) ^ (1 / 2 : ℝ) *
        phiArea β F ^ (1 / 2 : ℝ) := by
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hK0 : 0 ≤ K := zero_le_one.trans hgK.2.1
  have hmono : volume.restrict F ≤ volume.restrict upperHalf := Measure.restrict_mono hFH le_rfl
  set D : ℂ → ℝ := fun z => ‖dz g z‖ + ‖dzbar g z‖ with hDdef
  have hDm : Measurable D := s36g_D_meas g
  have hgc : ContinuousOn g upperHalf := hgK.2.2.1.1
  have hmaps : MapsTo g upperHalf upperHalf := fun z hz => hgimg ▸ mem_image_of_mem g hz
  have hαg : AEMeasurable (fun z => Real.sqrt ‖α (g z)‖) (volume.restrict F) := by
    have hc : ContinuousOn (fun z => Real.sqrt ‖α (g z)‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn (hα.continuousOn.comp hgc hmaps)
    exact (hc.aemeasurable hΔ).mono_measure hmono
  have hβm : AEMeasurable (fun z => Real.sqrt ‖β z‖) (volume.restrict F) := by
    have hc : ContinuousOn (fun z => Real.sqrt ‖β z‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn hβ.continuousOn
    exact (hc.aemeasurable hΔ).mono_measure hmono
  set f1 : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖) with hf1
  set f2 : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt ‖β z‖) with hf2
  have hf1m : AEMeasurable f1 (volume.restrict F) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hDm.aemeasurable.mul hαg)
  have hf2m : AEMeasurable f2 (volume.restrict F) := ENNReal.measurable_ofReal.comp_aemeasurable hβm
  have hsplit : ∀ z, ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖) = (f1 * f2) z := by
    intro z
    simp only [hf1, hf2, Pi.mul_apply]
    rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _))]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict F) Real.HolderConjugate.two_two hf1m hf2m
  have e2 : ∫⁻ z in F, f2 z ^ (2 : ℝ) = phiArea β F := by
    unfold phiArea
    refine lintegral_congr fun z => ?_
    simp only [hf2]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (norm_nonneg _)]
  have hsq : ∀ᵐ z ∂(volume.restrict F), D z ^ 2 ≤ K * jacobian g z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH (thm9_4_dilatation_ae hgK)] with z hz
    have h0 : 0 ≤ D z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    simp only [hDdef]
    unfold jacobian
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have e1 : ∫⁻ z in F, f1 z ^ (2 : ℝ) ≤ ENNReal.ofReal K * phiArea α (g '' F) := by
    rw [← s36e_area_image hFm hFH hgK hgimg α, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hsq] with z hz
    simp only [hf1]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.sqrt_nonneg _)) (by norm_num), Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right hz (norm_nonneg (α (g z)))
    nlinarith [norm_nonneg (α (g z))]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc ∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖)
      = ∫⁻ z in F, (f1 * f2) z := lintegral_congr hsplit
    _ ≤ (∫⁻ z in F, f1 z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ z in F, f2 z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hH
    _ ≤ (ENNReal.ofReal K * phiArea α (g '' F)) ^ (1 / (2 : ℝ)) * phiArea β F ^ (1 / (2 : ℝ)) := by
        rw [e2]
        exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow e1 hhalf) (by positivity)
    _ = ENNReal.ofReal (Real.sqrt K) * phiArea α (g '' F) ^ (1 / 2 : ℝ) * phiArea β F ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ENNReal.ofReal_rpow_of_nonneg hK0 hhalf,
          ← Real.sqrt_eq_rpow]

/-- Triangle bound for a difference on an arbitrary measurable subset of H. -/
theorem s36e_phiArea_sub_le {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    {φ χ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hχ : DifferentiableOn ℂ χ upperHalf) :
    phiArea (φ - χ) F ≤ phiArea φ F + phiArea χ F := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal ‖φ z‖) (volume.restrict F) :=
    (hφ.continuousOn.mono hFH).aestronglyMeasurable hFm |>.aemeasurable.norm.ennreal_ofReal
  change (∫⁻ z in F, ENNReal.ofReal ‖φ z - χ z‖) ≤
    (∫⁻ z in F, ENNReal.ofReal ‖φ z‖) + ∫⁻ z in F, ENNReal.ofReal ‖χ z‖
  rw [← lintegral_add_left' hm]
  apply lintegral_mono
  intro z
  show ENNReal.ofReal ‖φ z - χ z‖ ≤ ENNReal.ofReal ‖φ z‖ + ENNReal.ofReal ‖χ z‖
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)

/-- Setwise bound for the nonlinear stretch integrand, including arbitrary tails. -/
theorem s36e_stretch_bound_on {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    {χ : ℂ → ℂ} (hχ : DifferentiableOn ℂ χ upperHalf) :
    (∫⁻ z in F, ENNReal.ofReal ‖χ z‖ *
      ENNReal.ofReal (lambdaStretchPlane χ χ g z)) ≤
      ENNReal.ofReal (Real.sqrt K) * phiArea χ (g '' F) ^ (1 / 2 : ℝ) *
        phiArea χ F ^ (1 / 2 : ℝ) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (s36e_holder_on hFm hFH hgK hgimg hχ hχ)
  rw [← ENNReal.ofReal_mul (norm_nonneg _), s36g_T_eq]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left
    (s36g_N_bound (dz g z) (dzbar g z) (χ z)) (Real.sqrt_nonneg ‖χ (g z)‖)
  nlinarith [Real.sqrt_nonneg ‖χ (g z)‖, Real.sqrt_nonneg ‖χ z‖]

/-- L1 continuity on an arbitrary set controlled simultaneously on F and g(F).
The uniform M bounds replace an invalid ambient-automorphy assumption on approximants. -/
theorem s36e_stretch_cont_on {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    {φ χ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hχ : DifferentiableOn ℂ χ upperHalf) {M : ℝ≥0∞}
    (hφF : phiArea φ F ≤ M) (hχF : phiArea χ F ≤ M)
    (hφg : phiArea φ (g '' F) ≤ M) (hχg : phiArea χ (g '' F) ≤ M) :
    (∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal (lambdaStretchPlane χ χ g z)) ≤
      (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
      3 * ENNReal.ofReal (Real.sqrt K) * (2 * M) ^ (1 / 2 : ℝ) *
        (phiArea (φ - χ) F + phiArea (φ - χ) (g '' F)) ^ (1 / 2 : ℝ) := by
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hmono : volume.restrict F ≤ volume.restrict upperHalf := Measure.restrict_mono hFH le_rfl
  set δ := φ - χ with hδdef
  set D : ℂ → ℝ := fun z => ‖dz g z‖ + ‖dzbar g z‖ with hDdef
  have hDm : Measurable D := s36g_D_meas g
  have hgc : ContinuousOn g upperHalf := hgK.2.2.1.1
  have hmaps : MapsTo g upperHalf upperHalf := fun z hz => hgimg ▸ mem_image_of_mem g hz
  -- a.e.-measurability of the three error terms
  have haem : ∀ α β : ℂ → ℂ, DifferentiableOn ℂ α upperHalf → DifferentiableOn ℂ β upperHalf →
      AEMeasurable (fun z => ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖))
        (volume.restrict F) := by
    intro α β hα hβ
    have h1 : ContinuousOn (fun z => Real.sqrt ‖α (g z)‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn (hα.continuousOn.comp hgc hmaps)
    have h2 : ContinuousOn (fun z => Real.sqrt ‖β z‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn hβ.continuousOn
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((hDm.aemeasurable.mul
      ((h1.aemeasurable hΔ).mono_measure hmono)).mul ((h2.aemeasurable hΔ).mono_measure hmono))
  have hpt : ∀ z, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal (lambdaStretchPlane χ χ g z) ≤
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) +
        (ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) := by
    intro z
    have hD0 : 0 ≤ D z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hφl : 0 ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z := by
      rw [s36g_T_eq]
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_add hφl (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := s36g_T_le φ χ g z
    simp only [hδdef, Pi.sub_apply]
    simp only [hDdef] at *
    linarith
  have hφd := hφ
  have hδd := hφ.sub hχ
  have hI1 := s36e_holder_on hFm hFH hgK hgimg hφ hδd
  have hI2 := s36e_holder_on hFm hFH hgK hgimg hδd hφd
  have hI3 := s36e_holder_on hFm hFH hgK hgimg hδd hδd
  set S : ℝ≥0∞ := 2 * M with hS
  set c := ENNReal.ofReal (Real.sqrt K) with hc
  set e : ℝ≥0∞ := phiArea δ F + phiArea δ (g '' F) with he
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hgm : MeasurableSet (g '' F) :=
    hFm.image_of_continuousOn_injOn (hgK.2.2.1.1.mono hFH) (hgK.2.2.1.2.1.mono hFH)
  have hgFH : g '' F ⊆ upperHalf := hgimg ▸ image_mono hFH
  have hMS : M ≤ S := by
    rw [hS, two_mul]
    exact le_self_add
  have hδgS : phiArea δ (g '' F) ≤ S := by
    calc phiArea δ (g '' F) ≤ phiArea φ (g '' F) + phiArea χ (g '' F) :=
        s36e_phiArea_sub_le hgm hgFH hφ hχ
      _ ≤ M + M := add_le_add hφg hχg
      _ = S := (two_mul M).symm
  have ha : phiArea φ (g '' F) ^ (1 / 2 : ℝ) ≤ S ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (hφg.trans hMS) hhalf
  have hb : phiArea φ F ^ (1 / 2 : ℝ) ≤ S ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (hφF.trans hMS) hhalf
  have hd : phiArea δ (g '' F) ^ (1 / 2 : ℝ) ≤ S ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hδgS hhalf
  have heF : phiArea δ F ^ (1 / 2 : ℝ) ≤ e ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow le_self_add hhalf
  have heg : phiArea δ (g '' F) ^ (1 / 2 : ℝ) ≤ e ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow le_add_self hhalf
  calc ∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal (lambdaStretchPlane χ χ g z)
      ≤ ∫⁻ z in F, (ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) +
        (ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖))) := lintegral_mono hpt
    _ = (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        ((∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖)) +
          (∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖)) +
          ∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) := by
        have hsum : AEMeasurable (fun z => ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
            ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
            ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) (volume.restrict F) :=
          ((haem _ _ hφd hδd).add (haem _ _ hδd hφd)).add (haem _ _ hδd hδd)
        rw [lintegral_add_right' _ hsum, lintegral_add_right' _ (haem _ _ hδd hδd),
          lintegral_add_right' _ (haem _ _ hδd hφd)]
    _ ≤ (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        (c * phiArea φ (g '' F) ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ) +
          c * phiArea δ (g '' F) ^ (1 / 2 : ℝ) * phiArea φ F ^ (1 / 2 : ℝ) +
          c * phiArea δ (g '' F) ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ)) :=
        add_le_add le_rfl (add_le_add (add_le_add hI1 hI2) hI3)
    _ ≤ (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        (c * S ^ (1 / 2 : ℝ) * e ^ (1 / 2 : ℝ) +
          c * e ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) +
          c * S ^ (1 / 2 : ℝ) * e ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        3 * c * S ^ (1 / 2 : ℝ) * e ^ (1 / 2 : ℝ) := by ring

end LiZhongQC
