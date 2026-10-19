import LiZhongQC.Lemmas.UniformizedTeichmuller

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- The projection-fibre fundamental-domain clause in S22 is exactly the orbit
clause in S36, for the same uniformizing group and projection. -/
theorem s22ga_fundamentalDomainH_iff_projection
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hFH : F ⊆ upperHalf) :
    IsFundamentalDomainH Γ F ↔
      MeasurableSet F ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F →
        (τ₂ : ℂ) ∈ interior F → p τ₁ = p τ₂ → τ₁ = τ₂) ∧
      volume (F \ interior F) = 0 := by
  constructor
  · intro hF
    refine ⟨hF.2.1, hF.2.2.1, ?_, hF.2.2.2.2⟩
    intro τ₁ τ₂ h₁ h₂ heq
    exact hF.2.2.2.1 τ₁ τ₂ h₁ h₂ ((hp.2.2.2 τ₁ τ₂).1 heq)
  · rintro ⟨hFm, hcov, hinj, hnull⟩
    refine ⟨hFH, hFm, hcov, ?_, hnull⟩
    intro τ₁ τ₂ h₁ h₂ horbit
    exact hinj τ₁ τ₂ h₁ h₂ ((hp.2.2.2 τ₁ τ₂).2 horbit)

/-- The hyperbolic area density transforms by the inverse Euclidean Jacobian.
Both denominators are nonzero on the upper half-plane. -/
theorem s22ga_hyperbolic_density_covariant
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    ENNReal.ofReal (1 / (h36p_m γ z).im ^ 2) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      ENNReal.ofReal (1 / z.im ^ 2) := by
  have hy : z.im ≠ 0 := ne_of_gt (show 0 < z.im from hz)
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 :=
    k24_d_den_ne_zero (b33_d_det γ) hy
  have hn : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  have him : (h36p_m γ z).im =
      z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
    change (((γ 0 0 : ℂ) * z + γ 0 1) /
      ((γ 1 0 : ℂ) * z + γ 1 1)).im = _
    rw [utm_im_mobius (b33_d_det γ), Complex.normSq_eq_norm_sq]
  rw [← ENNReal.ofReal_mul
    (by positivity : 0 ≤ 1 / (h36p_m γ z).im ^ 2), him]
  congr 1
  field_simp [hy, hn] <;> ring

/-- Weighted a.e. tiling counts the actual SL subgroup, including its ineffective
kernel. The multiplicity is |Γ ∩ ⟨-1⟩|, rather than an assumed value of one. -/
theorem s22ga_ae_weighted_tiling
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {G : Set ℂ} (hG : IsFundamentalDomainH Γ G)
    (w : ℂ → ℝ≥0∞) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      (∑' γ : Γ, (h36p_m γ.1 ⁻¹' G).indicator w z) =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * w z := by
  classical
  filter_upwards [h36p_ae_unique hΓ hG,
    ae_restrict_mem isOpen_upperHalf.measurableSet] with z hu hz
  have hrw : ∀ γ : Γ, (h36p_m γ.1 ⁻¹' G).indicator w z =
      {γ : Γ | h36p_m γ.1 z ∈ G}.indicator (fun _ => w z) γ := by
    intro γ
    by_cases h : h36p_m γ.1 z ∈ G
    · rw [indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' G from h),
        indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 z ∈ G} from h)]
    · rw [indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' G from h),
        indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 z ∈ G} from h)]
  rw [tsum_congr hrw]
  obtain ⟨γ₀, hγ₀, hγ₀G⟩ := hG.2.2.1 ⟨z, hz⟩
  have hγ₀G' : h36p_m γ₀ z ∈ G := by
    have e := h36p_m_coe γ₀ ⟨z, hz⟩
    simp only at e
    rw [e]
    exact hγ₀G
  refine h36p_a_count (P := fun γ => h36p_m γ z ∈ G) hγ₀
    (fun γ hγ => ⟨fun h => hu γ hγ γ₀ hγ₀ h hγ₀G', ?_⟩) (w z)
  rintro (rfl | rfl)
  · exact hγ₀G'
  · rw [h36p_a_m_neg]
    exact hγ₀G'

/-- Any measurable nonnegative density with the Möbius Jacobian covariance
has the same extended integral over two measurable fundamental domains.
No finiteness hypothesis on either integral is needed. -/
theorem s22ga_lintegral_eq_of_covariant
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {F G : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (hG : IsFundamentalDomainH Γ G)
    {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (hcov : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      w (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = w z) :
    (∫⁻ z in F, w z) = ∫⁻ z in G, w z := by
  classical
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  let m : ℝ≥0∞ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have hmfin : m ≠ ⊤ := ENNReal.natCast_ne_top _
  have hterm (γ : Γ) :
      (∫⁻ z in F, G.indicator w (h36p_m γ.1 z) *
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)) =
      ∫⁻ z in F, (h36p_m γ.1 ⁻¹' G).indicator w z := by
    refine setLIntegral_congr_fun hF.2.1 fun z hz => ?_
    by_cases h : h36p_m γ.1 z ∈ G
    · rw [indicator_of_mem h,
        indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' G from h)]
      exact hcov γ.1 γ.2 z (hF.1 hz)
    · rw [indicator_of_notMem h,
        indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' G from h), zero_mul]
  have hsum :
      (∑' γ : Γ, ∫⁻ z in F, G.indicator w (h36p_m γ.1 z) *
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)) =
      m * ∫⁻ z in F, w z := by
    calc
      _ = ∑' γ : Γ, ∫⁻ z in F, (h36p_m γ.1 ⁻¹' G).indicator w z :=
        tsum_congr hterm
      _ = ∫⁻ z in F, ∑' γ : Γ, (h36p_m γ.1 ⁻¹' G).indicator w z :=
        (lintegral_tsum fun γ : Γ =>
          (hw.indicator (h36p_m_measurable γ.1 hG.2.1)).aemeasurable).symm
      _ = ∫⁻ z in F, m * w z := by
        exact lintegral_congr_ae
          (ae_restrict_of_ae_restrict_of_subset hF.1 (s22ga_ae_weighted_tiling hΓ hG w))
      _ = m * ∫⁻ z in F, w z :=
        lintegral_const_mul' _ _ hmfin
  have hrestrict : (∫⁻ z in upperHalf, G.indicator w z) = ∫⁻ z in G, w z := by
    rw [setLIntegral_indicator hG.2.1, inter_eq_left.2 hG.1]
  have hbalance := hsum.symm.trans (h36p_unfold hΓ hF (hw.indicator hG.2.1))
  rw [hrestrict] at hbalance
  change m * (∫⁻ z in F, w z) = m * (∫⁻ z in G, w z) at hbalance
  -- Cancel a positive finite kernel factor in ENNReal, even when an area is infinite.
  have hcancel := congrArg (fun x : ℝ≥0∞ => m⁻¹ * x) hbalance
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmfin, one_mul] using hcancel

/-- Hyperbolic areas of two S36 measurable fundamental domains agree, with the
SL₂ ineffective kernel handled by the weighted unfolding theorem. -/
theorem s22ga_hyperbolic_area_eq
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {F G : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (hG : IsFundamentalDomainH Γ G) :
    (∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2)) =
      ∫⁻ z in G, ENNReal.ofReal (1 / z.im ^ 2) := by
  apply s22ga_lintegral_eq_of_covariant hΓ hF hG
  · fun_prop
  · intro γ _ z hz
    exact s22ga_hyperbolic_density_covariant γ hz

/-- Fundamental-domain independence in the literal projection-fibre model of
gauss_bonnet_area. This asserts no value or finiteness for the common area. -/
theorem s22ga_hyperbolic_area_eq_of_uniformization
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F G : Set ℂ} (hFH : F ⊆ upperHalf) (hGH : G ⊆ upperHalf)
    (hFundF : MeasurableSet F ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F →
        (τ₂ : ℂ) ∈ interior F → p τ₁ = p τ₂ → τ₁ = τ₂) ∧
      volume (F \ interior F) = 0)
    (hFundG : MeasurableSet G ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ G) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior G →
        (τ₂ : ℂ) ∈ interior G → p τ₁ = p τ₂ → τ₁ = τ₂) ∧
      volume (G \ interior G) = 0) :
    (∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2)) =
      ∫⁻ z in G, ENNReal.ofReal (1 / z.im ^ 2) := by
  exact s22ga_hyperbolic_area_eq (utm_x2_isFuchsian hp)
    ((s22ga_fundamentalDomainH_iff_projection hp hFH).2 hFundF)
    ((s22ga_fundamentalDomainH_iff_projection hp hGH).2 hFundG)

end LiZhongQC

