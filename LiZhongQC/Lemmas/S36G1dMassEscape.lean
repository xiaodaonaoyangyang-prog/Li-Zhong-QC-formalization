import LiZhongQC.Lemmas.S36G1dExhaustion
import LiZhongQC.Lemmas.StrebelGammaTransport

/-!
E4 independent source producer: subgroup saturation, no-return a.e., theta tail
unfolding, and dominated convergence. It does not require the E2 domain construction:
its frozen premises supply the actual domain data.
Revision 003: compile repairs only. No new global definitions or instances.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Ineffective-kernel cardinalities are monotone under subgroup inclusion. -/
theorem s36e_kernel_card_mono (hΛ : Λ ≤ Γ) :
    Nat.card ↥(Λ ⊓ Subgroup.zpowers (-1)) ≤
      Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) := by
  letI : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
  letI : Finite ↥(Γ ⊓ Subgroup.zpowers (-1)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : Γ ⊓ Subgroup.zpowers (-1) ≤ Subgroup.zpowers (-1)))
  have hle : Λ ⊓ Subgroup.zpowers (-1) ≤ Γ ⊓ Subgroup.zpowers (-1) :=
    inf_le_inf hΛ le_rfl
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

/-- A subgroup saturation of a measurable set is measurable. -/
theorem s36e_saturation_measurable (hΛ : IsFuchsian Λ)
    {F : Set ℂ} (hF : MeasurableSet F) :
    MeasurableSet {w : ℂ | ∃ γ ∈ Λ, h36p_m γ w ∈ F} := by
  have : Countable Λ := (h36p_countable hΛ).to_subtype
  have heq : {w : ℂ | ∃ γ ∈ Λ, h36p_m γ w ∈ F} =
      ⋃ γ : Λ, h36p_m γ.val ⁻¹' F := by
    ext w
    constructor
    · rintro ⟨γ, hγ, hw⟩
      exact mem_iUnion.2 ⟨⟨γ, hγ⟩, hw⟩
    · intro hw
      obtain ⟨γ, hγ⟩ := mem_iUnion.1 hw
      exact ⟨γ.val, γ.property, hγ⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun γ : Λ => h36p_m_measurable γ.val hF)

/-- Off F, almost every point of a subgroup domain D containing F has no subgroup
translate in F. The conclusion includes all group elements at once. -/
theorem s36e_no_return (hΛ : IsFuchsian Λ)
    {F D : Set ℂ} (hD : IsFundamentalDomainH Λ D) (hFD : F ⊆ D) :
    ∀ᵐ z ∂(volume.restrict D), z ∉ F →
      ∀ γ ∈ Λ, h36p_m γ z ∉ F := by
  have hu := ae_restrict_of_ae_restrict_of_subset hD.1 (h36p_ae_unique hΛ hD)
  filter_upwards [hu, ae_restrict_mem hD.2.1] with z hz hzD
  intro hzF γ hγ hγF
  have h1 : h36p_m 1 z ∈ D := by simpa only [h36p_a_m_one] using hzD
  rcases hz γ hγ 1 Λ.one_mem (hFD hγF) h1 with h | h
  · rw [h, h36p_a_m_one] at hγF
    exact hzF hγF
  · rw [h, h36p_a_m_neg, h36p_a_m_one] at hγF
    exact hzF hγF

/-- Absolute theta unfolding bounds the mass on D minus F by the seed mass outside
the subgroup saturation of F. No finite generation or freeness is used. -/
theorem s36e_theta_tail_bound (hΛ : IsFuchsian Λ)
    {F D : Set ℂ} (hD : IsFundamentalDomainH Λ D)
    (hF : MeasurableSet F) (hFD : F ⊆ D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) :
    phiArea (h36p_theta Λ f) (D \ F) ≤
      (Nat.card ↥(Λ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) *
        ∫⁻ w in upperHalf,
          ({w : ℂ | ∃ γ ∈ Λ, h36p_m γ w ∈ F}ᶜ).indicator
            (upperHalf.indicator (fun w => ENNReal.ofReal ‖f w‖)) w := by
  classical
  have : Countable Λ := (h36p_countable hΛ).to_subtype
  let R : Set ℂ := {w | ∃ γ ∈ Λ, h36p_m γ w ∈ F}
  let G : ℂ → ℝ≥0∞ := Rᶜ.indicator
    (upperHalf.indicator (fun w => ENNReal.ofReal ‖f w‖))
  let T : Λ → ℂ → ℂ := fun γ z =>
    f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4
  let J : Λ → ℂ → ℝ≥0∞ := fun γ z =>
    ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4)
  have hR : MeasurableSet R := s36e_saturation_measurable hΛ hF
  have hG : Measurable G := (str_meas hf).indicator hR.compl
  have hW : ∀ γ : Λ, AEMeasurable
      (fun z => G (h36p_m γ.val z) * J γ z) (volume.restrict D) := by
    intro γ
    have hm : ContinuousOn (h36p_m γ.val) D := fun z hz =>
      (h36p_m_hasDerivAt γ.val (hD.1 hz)).continuousAt.continuousWithinAt
    have hJ : Measurable (J γ) := by
      change Measurable (fun z : ℂ =>
        ENNReal.ofReal (‖(γ.val 1 0 : ℂ) * z + γ.val 1 1‖⁻¹ ^ 4))
      fun_prop
    exact (hG.comp_aemeasurable
      (hm.aestronglyMeasurable hD.2.1).aemeasurable).mul hJ.aemeasurable
  have heq : (fun z => ∑' γ : Λ, ‖T γ z‖ₑ) =ᵐ[volume.restrict (D \ F)]
      (fun z => ∑' γ : Λ, G (h36p_m γ.val z) * J γ z) := by
    have hu := ae_restrict_of_ae_restrict_of_subset
      (show D \ F ⊆ D from fun _ h => h.1) (s36e_no_return hΛ hD hFD)
    filter_upwards [hu, ae_restrict_mem (hD.2.1.diff hF)] with z hz hzE
    apply tsum_congr
    intro γ
    have hzH := hD.1 hzE.1
    have hnot : h36p_m γ.val z ∉ R := by
      rintro ⟨δ, hδ, hδF⟩
      have hprod : h36p_m (δ * γ.val) z ∈ F := by
        rwa [h36p_a_m_mul δ γ.val hzH]
      exact hz hzE.2 (δ * γ.val) (Λ.mul_mem hδ γ.property) hprod
    change ‖f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4‖ₑ =
      Rᶜ.indicator (upperHalf.indicator (fun w => ENNReal.ofReal ‖f w‖))
        (h36p_m γ.val z) * J γ z
    rw [indicator_of_mem hnot, indicator_of_mem (h36p_m_mem γ.val hzH),
      ← ofReal_norm, h36p_b_norm_term, ENNReal.ofReal_mul (norm_nonneg _)]
  calc phiArea (h36p_theta Λ f) (D \ F)
      = ∫⁻ z in D \ F, ‖h36p_theta Λ f z‖ₑ := by
        simp only [phiArea, ofReal_norm]
    _ ≤ ∫⁻ z in D \ F, ∑' γ : Λ, ‖T γ z‖ₑ :=
      lintegral_mono (fun z => enorm_tsum_le_tsum_enorm)
    _ = ∫⁻ z in D \ F, ∑' γ : Λ, G (h36p_m γ.val z) * J γ z :=
      lintegral_congr_ae heq
    _ ≤ ∫⁻ z in D, ∑' γ : Λ, G (h36p_m γ.val z) * J γ z :=
      lintegral_mono_set (show D \ F ⊆ D from fun _ h => h.1)
    _ = ∑' γ : Λ, ∫⁻ z in D, G (h36p_m γ.val z) * J γ z :=
      lintegral_tsum hW
    _ = (Nat.card ↥(Λ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) *
        ∫⁻ z in upperHalf, G z :=
      h36p_unfold hΛ hD hG

/-- E4: no mass escapes through the extra coset tiles.
The domains need not be nested: monotonicity is imposed on H, not on D.
The proof bounds the tail by the L1 mass of f outside the H_i-saturation of F. -/
theorem s36e_theta_mass_escape (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hsub : ∀ i, H i ≤ Γ) (hmono : Monotone H)
    (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    (D : ℕ → Set ℂ) (hD : ∀ i, IsFundamentalDomainH (H i) (D i))
    (hFD : ∀ i, F ⊆ D i)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤) :
    Tendsto (fun i => phiArea (h36p_theta (H i) f) (D i \ F))
      atTop (𝓝 0) := by
  classical
  let G : ℂ → ℝ≥0∞ := upperHalf.indicator (fun z => ENNReal.ofReal ‖f z‖)
  let R : ℕ → Set ℂ := fun i => {w | ∃ γ ∈ H i, h36p_m γ w ∈ F}
  let Q : ℕ → ℂ → ℝ≥0∞ := fun i => (R i)ᶜ.indicator G
  have hHi : ∀ i, IsFuchsian (H i) := fun i C hC =>
    (hΓ C hC).subset (fun γ hγ => ⟨hsub i hγ.1, hγ.2⟩)
  have hR : ∀ i, MeasurableSet (R i) := fun i =>
    s36e_saturation_measurable (hHi i) hF.2.1
  have hG : Measurable G := str_meas hf
  have hQm : ∀ i, AEMeasurable (Q i) (volume.restrict upperHalf) :=
    fun i => (hG.indicator (hR i).compl).aemeasurable
  have hbound : ∀ i, Q i ≤ᵐ[volume.restrict upperHalf] G :=
    fun i => Filter.Eventually.of_forall (fun z => indicator_le_self _ _ _)
  have hGfin : (∫⁻ z in upperHalf, G z) ≠ ⊤ := by
    have heq : (∫⁻ z in upperHalf, G z) = phiArea f upperHalf := by
      apply setLIntegral_congr_fun isOpen_upperHalf.measurableSet
      intro z hz
      exact indicator_of_mem hz _
    rw [heq]
    exact hfA.ne
  have hlim : ∀ᵐ z ∂(volume.restrict upperHalf),
      Tendsto (fun i => Q i z) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
    obtain ⟨γ, hγ, hγF⟩ := hF.2.2.1 ⟨z, hz⟩
    have hγF' : h36p_m γ z ∈ F := by
      rw [h36p_m_coe γ ⟨z, hz⟩]
      exact hγF
    apply tendsto_const_nhds.congr'
    filter_upwards [s36e_mem_eventually H hmono hcover hγ] with i hi
    have hzR : z ∈ R i := ⟨γ, hi, hγF'⟩
    have hzero : Q i z = 0 :=
      indicator_of_notMem (show z ∉ (R i)ᶜ from fun hn => hn hzR) _
    exact hzero.symm
  have htail : Tendsto (fun i => ∫⁻ z in upperHalf, Q i z) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' G hQm hbound hGfin hlim
  let mΓ : ℝ≥0∞ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))
  have hmfin : mΓ ≠ ⊤ := ENNReal.natCast_ne_top _
  have hscaled : Tendsto (fun i => mΓ * ∫⁻ z in upperHalf, Q i z)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := mΓ) htail (Or.inr hmfin)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
  · intro i
    exact zero_le
  · intro i
    have hfirst := s36e_theta_tail_bound (hHi i) (hD i) hF.2.1 (hFD i) hf
    have hcard : (Nat.card ↥(H i ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≤ mΓ := by
      exact Nat.cast_le.2 (s36e_kernel_card_mono (hsub i))
    exact hfirst.trans (mul_le_mul_of_nonneg_right hcard (zero_le))

end LiZhongQC
