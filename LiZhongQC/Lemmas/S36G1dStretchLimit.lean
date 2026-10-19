import LiZhongQC.Lemmas.S36G1dSetBounds
import LiZhongQC.Lemmas.S36G1dAreaLimit

/-! E6 source-only producer. No compiler run; no new global definitions.
The only predecessor inputs are the E1/E3/E4/E5 producers and shared Bounds.
No G1c/G2/G3 stub or open book theorem is called. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Absolute unfolding bounds every subgroup theta series on an ambient domain. -/
theorem s36e_theta_area_le (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΛ : Λ ≤ Γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) :
    phiArea (h36p_theta Λ f) F ≤
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf := by
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  have hm : ∀ γ : Γ, AEMeasurable
      (fun z => ‖f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4‖ₑ)
      (volume.restrict F) := fun γ =>
    ((h36p_b_term_diff hf γ.val).continuousOn.mono hF.1).aestronglyMeasurable hF.2.1 |>.enorm
  calc phiArea (h36p_theta Λ f) F =
      ∫⁻ z in F, ‖h36p_theta Λ f z‖ₑ := by simp only [phiArea, ofReal_norm]
    _ ≤ ∫⁻ z in F, ∑' γ : Γ,
        ‖f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4‖ₑ :=
      lintegral_mono (fun z => s36e_theta_enorm_le hΛ f z)
    _ = ∑' γ : Γ, ∫⁻ z in F,
        ‖f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4‖ₑ :=
      lintegral_tsum hm
    _ = _ := h36p_b_sum_lintegral hΓ hF hf

/-- A finite constant times the square root of an ENNReal error tends to zero. -/
theorem s36e_sqrt_error_tendsto {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {e : ℕ → ℝ≥0∞} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun i => C * e i ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp he
  have hm := ENNReal.Tendsto.const_mul (a := C) hr (Or.inr hC)
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_zero] using hm

/-- E6: pass the nonlinear stretch integral.
Use E3 on F and g(F), the existing square-root pointwise estimate, and QC area
change. On D_i \ F use E4 and a uniform Cauchy-Schwarz tail estimate.
One cannot apply the existing same-group L1 continuity theorem directly:
theta_(H_i) f is generally not Gamma-automorphic. -/
theorem s36e_stretch_tendsto (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hsub : ∀ i, H i ≤ Γ) (hmono : Monotone H)
    (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    (D : ℕ → Set ℂ) (hD : ∀ i, IsFundamentalDomainH (H i) (D i))
    (hFD : ∀ i, F ⊆ D i)
    (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    (hθ : ∀ z ∈ upperHalf, φ z = h36p_theta Γ f z) :
    Tendsto (fun i => ∫⁻ z in D i, ENNReal.ofReal ‖h36p_theta (H i) f z‖ *
      ENNReal.ofReal (lambdaStretchPlane (h36p_theta (H i) f)
        (h36p_theta (H i) f) (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z))
      atTop (𝓝 (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ *
        ENNReal.ofReal (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z))) := by
  -- The frozen hφ is retained; membership also follows from hθ and the seed hypotheses.
  have _ := hφ
  let ψ : ℕ → ℂ → ℂ := fun i => h36p_theta (H i) f
  let θ : ℂ → ℂ := h36p_theta Γ f
  let g : ℂ → ℂ := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1
  obtain ⟨K, hgK, hgimg, hcomm⟩ := str_g_facts μ ν hrel
  have hFg : IsFundamentalDomainH Γ (g '' F) := s36e_image_domain hF hgK hgimg hcomm
  have hHi : ∀ i, IsFuchsian (H i) := fun i C hC =>
    (hΓ C hC).subset (fun γ hγ => ⟨hsub i hγ.1, hγ.2⟩)
  have hψmem : ∀ i, ψ i ∈ integrableAutomorphicQD (H i) (D i) :=
    fun i => (h36p_poincare (hHi i) (hD i) hf hfA).1
  have hψd : ∀ i, DifferentiableOn ℂ (ψ i) upperHalf := fun i => (hψmem i).1
  have hθd : DifferentiableOn ℂ θ upperHalf := h36p_b_theta_diff hΓ hf hfA
  let M : ℝ≥0∞ := (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfA.ne
  have hψF : ∀ i, phiArea (ψ i) F ≤ M :=
    fun i => s36e_theta_area_le hΓ hF (hsub i) hf
  have hψg : ∀ i, phiArea (ψ i) (g '' F) ≤ M :=
    fun i => s36e_theta_area_le hΓ hFg (hsub i) hf
  have hθF : phiArea θ F ≤ M := s36e_theta_area_le hΓ hF le_rfl hf
  have hθg : phiArea θ (g '' F) ≤ M := s36e_theta_area_le hΓ hFg le_rfl hf
  have hneg : ∀ (i : ℕ) (E : Set ℂ),
      phiArea (θ - ψ i) E = phiArea (ψ i - θ) E := by
    intro i E
    apply lintegral_congr
    intro z
    exact congrArg ENNReal.ofReal (norm_sub_rev (θ z) (ψ i z))
  let e : ℕ → ℝ≥0∞ := fun i =>
    phiArea (θ - ψ i) F + phiArea (θ - ψ i) (g '' F)
  have he : Tendsto e atTop (𝓝 0) := by
    have h1 := s36e_theta_L1_fixed hΓ hF H hsub hmono hcover hf hfA
    have h2 := s36e_theta_L1_fixed hΓ hFg H hsub hmono hcover hf hfA
    simpa only [e, hneg, add_zero] using h1.add h2
  let C : ℝ≥0∞ := 3 * ENNReal.ofReal (Real.sqrt K) * (2 * M) ^ (1 / 2 : ℝ)
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) hM))
  have herror : Tendsto (fun i => C * e i ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    s36e_sqrt_error_tendsto hC he
  have hfixed : Tendsto (fun i => ∫⁻ z in F, ENNReal.ofReal ‖ψ i z‖ *
      ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z)) atTop
      (𝓝 (∫⁻ z in F, ENNReal.ofReal ‖θ z‖ *
        ENNReal.ofReal (lambdaStretchPlane θ θ g z))) := by
    apply s36e_tendsto_of_add_error herror
    · intro i
      exact s36e_stretch_cont_on hF.2.1 hF.1 hgK hgimg hθd (hψd i)
        hθF (hψF i) hθg (hψg i)
    · intro i
      have h := s36e_stretch_cont_on hF.2.1 hF.1 hgK hgimg (hψd i) hθd
        (hψF i) hθF (hψg i) hθg
      rw [← hneg i F, ← hneg i (g '' F)] at h
      exact h
  have hψD : ∀ i, phiArea (ψ i) (D i) ≤ M := by
    intro i
    have hbase := s36e_theta_area_le (hHi i) (hD i)
      (show H i ≤ H i from le_rfl) hf
    have hm : (Nat.card ↥(H i ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≤
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
      exact_mod_cast s36e_kernel_card_mono (hsub i)
    exact hbase.trans (mul_le_mul_of_nonneg_right hm zero_le)
  have hψgD : ∀ i, phiArea (ψ i) (g '' D i) ≤ M := by
    intro i
    have hc := str_area (hHi i) (hD i) (hψmem i) hgK hgimg
      (fun γ hγ z hz => hcomm γ (hsub i hγ) z hz)
    have heq := s36e_area_image (hD i).2.1 (hD i).1 hgK hgimg (ψ i)
    have hsame : phiArea (ψ i) (g '' D i) = phiArea (ψ i) (D i) := heq.symm.trans hc
    rw [hsame]
    exact hψD i
  let Ctail : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt K) * M ^ (1 / 2 : ℝ)
  have hCtail : Ctail ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hM)
  have hescape := s36e_theta_mass_escape hΓ hF H hsub hmono hcover D hD hFD hf hfA
  have htailbound := s36e_sqrt_error_tendsto hCtail hescape
  have htail : Tendsto (fun i => ∫⁻ z in D i \ F, ENNReal.ofReal ‖ψ i z‖ *
      ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htailbound
    · intro i
      exact zero_le
    · intro i
      have hI := s36e_stretch_bound_on ((hD i).2.1.diff hF.2.1)
        (diff_subset.trans (hD i).1) hgK hgimg (hψd i)
      have hle : phiArea (ψ i) (g '' (D i \ F)) ≤ M :=
        (lintegral_mono_set (image_mono diff_subset)).trans (hψgD i)
      apply hI.trans
      change ENNReal.ofReal (Real.sqrt K) *
          phiArea (ψ i) (g '' (D i \ F)) ^ (1 / 2 : ℝ) *
          phiArea (ψ i) (D i \ F) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt K) * M ^ (1 / 2 : ℝ) *
          phiArea (ψ i) (D i \ F) ^ (1 / 2 : ℝ)
      gcongr
  have hsplit : ∀ i,
      (∫⁻ z in F, ENNReal.ofReal ‖ψ i z‖ * ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z)) +
      (∫⁻ z in D i \ F, ENNReal.ofReal ‖ψ i z‖ *
        ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z)) =
      ∫⁻ z in D i, ENNReal.ofReal ‖ψ i z‖ *
        ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z) := by
    intro i
    have h := lintegral_inter_add_sdiff (μ := volume)
      (fun z => ENNReal.ofReal ‖ψ i z‖ *
        ENNReal.ofReal (lambdaStretchPlane (ψ i) (ψ i) g z)) (D i) hF.2.1
    rw [inter_eq_right.2 (hFD i)] at h
    exact h
  have hIθ : (∫⁻ z in F, ENNReal.ofReal ‖θ z‖ *
      ENNReal.ofReal (lambdaStretchPlane θ θ g z)) =
      ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ *
        ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
    apply setLIntegral_congr_fun hF.2.1
    intro z hz
    have hzH := hF.1 hz
    have hgzH : g z ∈ upperHalf := hgimg ▸ mem_image_of_mem g hzH
    have hzq : φ z = θ z := hθ z hzH
    have hgzq : φ (g z) = θ (g z) := hθ (g z) hgzH
    simp only [lambdaStretchPlane, ← hzq, ← hgzq]
  simpa only [add_zero, hsplit, hIθ] using hfixed.add htail

end LiZhongQC
