import LiZhongQC.Lemmas.StrebelGammaBounds
import LiZhongQC.Lemmas.StrebelGammaTransport
import LiZhongQC.Lemmas.StrebelGammaG3Helpers

/-! The end of the Strebel proof, with explicit producer inputs.
These helpers do not discharge G1d or alter any book statement.
The final assembly must supply the actual proved inequality. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **G2.** The Γ main inequality (simplified, GL (4.21)). -/
theorem str_gamma_main_inequality_of_eq35_5 (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F)
    (hEq : ∀ {ψ : ℂ → ℂ}, ψ ∈ integrableAutomorphicQD Γ F →
      phiArea ψ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖ψ z‖ * ENNReal.ofReal
        (lambdaStretchPlane ψ ψ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z)) :
    phiArea φ F ≤ ENNReal.ofReal ((1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1)) *
      ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ *
        (‖1 - μ.1.1 z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2))) := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  set c := beltramiNormH ν.1.1 with hc
  have hc1 : c < 1 := c36_c_normH_lt_one ν.1
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  obtain ⟨hK, hfs⟩ := str_fMu_facts ν
  obtain ⟨hK₀, hf₀s⟩ := str_fMu_facts μ
  set K := (1 + c) / (1 - c) with hKdef
  set f := fMuSym ν.1.1 with hf
  set f₀ := fMuSym μ.1.1 with hf₀
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ.1
  have hdil : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f₀ z = μ.1.1 z :=
    (fMuSym_upperHalf hk0 hk1 hμ).2.2.2.2
  set a := Function.invFunOn f upperHalf with hadef
  have haK : IsKQC a upperHalf K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hfi : InjOn f upperHalf := hK.2.2.1.2.1
  have hgK := thm7_1_comp hK₀ haK hf₀s.subset
  have hgimg : (a ∘ f₀) '' upperHalf = upperHalf := by
    rw [image_comp, hf₀s]
    conv_lhs => rw [← hfs]
    exact hfi.leftInvOn_invFunOn.image_image
  have hcomm : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, (a ∘ f₀) (h36p_m γ z) = h36p_m γ ((a ∘ f₀) z) :=
    fun γ hγ z hz => str_comm μ ν hrel hγ z hz
  have hgmaps : MapsTo (a ∘ f₀) upperHalf upperHalf := fun z hz => hgimg ▸ mem_image_of_mem _ hz
  set g := a ∘ f₀ with hgdef
  have hφc : ContinuousOn φ upperHalf := hφ.1.continuousOn
  have hφg : ContinuousOn (fun z => φ (g z)) upperHalf := hφc.comp hgK.2.2.1.1 hgmaps
  have hJm : Measurable (jacobian g) :=
    ((measurable_dz g).norm.pow_const 2).sub ((measurable_dzbar g).norm.pow_const 2)
  have hJposF : ∀ᵐ z ∂(volume.restrict F), 0 < jacobian g z :=
    ae_restrict_of_ae_restrict_of_subset hFH (thm9_6_cor2_jacobian_pos hgK)
  have hneg := str_neg hφ
  have h5 := hEq hneg
  have hareaψ : phiArea (fun z => -φ z) F = phiArea φ F := by simp [phiArea]
  rw [hareaψ] at h5
  set X : ℂ → ℝ := fun z => ‖φ (g z)‖ * jacobian g z with hX
  set Ev : ℂ → ℝ := fun z => ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 / jacobian g z with hEv
  have hXm : AEMeasurable (fun z => ENNReal.ofReal (X z)) (volume.restrict F) :=
    (((hφg.mono hFH).norm.aestronglyMeasurable hFm).aemeasurable.mul
      hJm.aemeasurable).ennreal_ofReal
  -- step 1: AM–GM pointwise
  have hstep1 : ∀ᵐ z ∂(volume.restrict F),
      2 * (ENNReal.ofReal ‖-φ z‖ * ENNReal.ofReal
        (lambdaStretchPlane (fun z => -φ z) (fun z => -φ z) g z)) ≤
        ENNReal.ofReal (X z) + ENNReal.ofReal (‖φ z‖ * Ev z) := by
    filter_upwards [hJposF] with z hJ
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    have hlam : lambdaStretchPlane (fun z => -φ z) (fun z => -φ z) g z =
        Real.sqrt ‖φ (g z)‖ * ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ / Real.sqrt ‖φ z‖ := by
      simp only [lambdaStretchPlane, norm_neg]
      congr 3
      ring
    rw [hlam, norm_neg]
    have h := m35_amgm (norm_nonneg (φ z)) (norm_nonneg (φ (g z))) hJ
      (D := ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖)
    have hX0 : 0 ≤ X z := mul_nonneg (norm_nonneg _) hJ.le
    have hE0 : 0 ≤ ‖φ z‖ * Ev z := mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) hJ.le)
    rw [← ENNReal.ofReal_add hX0 hE0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    show 2 * (‖φ z‖ * (Real.sqrt ‖φ (g z)‖ * ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ /
      Real.sqrt ‖φ z‖)) ≤ ‖φ (g z)‖ * jacobian g z +
        ‖φ z‖ * (‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 / jacobian g z)
    linarith
  -- step 2: change of variables in the first half
  have hstep3 : ∫⁻ z in F, ENNReal.ofReal (X z) = phiArea φ F :=
    str_area hΓ hF' hφ hgK hgimg hcomm
  -- step 3: the second half is bounded by `K` times the target integrand
  have hKc : (K - 1) / (K + 1) = c := by
    rw [hKdef]
    have : (1 - c) ≠ 0 := by linarith
    field_simp
    ring
  have hda := str_ae_comp hK₀ hf₀s
    ((thm9_3_differentiable_ae haK).and (thm9_6_cor2_jacobian_pos haK))
  have hκ₁ := str_ae_comp hK₀ hf₀s (isKQC_maxDilatation_le haK).2
  have hKc1 : K ≤ K := le_rfl
  have hstep4 : ∀ᵐ z ∂(volume.restrict F), ENNReal.ofReal (‖φ z‖ * Ev z) ≤
      ENNReal.ofReal K * ENNReal.ofReal (‖φ z‖ *
        (‖1 - μ.1.1 z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2))) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH (thm9_3_differentiable_ae hK₀),
      ae_restrict_of_ae_restrict_of_subset hFH (thm9_6_cor2_jacobian_pos hK₀),
      ae_restrict_of_ae_restrict_of_subset hFH hda, ae_restrict_of_ae_restrict_of_subset hFH hκ₁,
      ae_restrict_of_ae_restrict_of_subset hFH hdil]
      with z hdz hJz hdaz hk1z hdilz
    obtain ⟨hdaz, hJaz⟩ := hdaz
    rw [hKc] at hk1z
    rw [← ENNReal.ofReal_mul (by linarith [show (1 : ℝ) ≤ K from hK.2.1])]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hp : φ z = 0
    · simp [hp]
    obtain ⟨hκ, hd0⟩ := m35_norm_cd_lt_one hJz
    obtain ⟨hκ₁', ha0⟩ := m35_norm_cd_lt_one hJaz
    obtain ⟨hdzg, hdbzg⟩ := m35_chain_mainIneq hdz hdaz hd0 ha0
    have hτ : ‖conj (dz f₀ z) / dz f₀ z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hd0)]
    have hv : ‖φ z / (‖φ z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hp).ne']
    have hG : dz a (f₀ z) * dz f₀ z ≠ 0 := mul_ne_zero ha0 hd0
    have key := m35_E_eq_AB hκ hκ₁' hτ hv hG
    have hEz : Ev z = ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 /
        (‖dz g z‖ ^ 2 - ‖dzbar g z‖ ^ 2) := rfl
    have hconjv : conj (φ z / (‖φ z‖ : ℂ)) = conj (φ z) / (‖φ z‖ : ℂ) := by
      rw [map_div₀, Complex.conj_ofReal]
    have hB := m35_mainIneq_second_le (κ := complexDilatation f₀ z)
      (κ₁ := complexDilatation a (f₀ z)) (τ := conj (dz f₀ z) / dz f₀ z) (p := φ z) hc1 hk1z
      (m35_norm_conj_div_le_one (dz f₀ z))
    have hEeq : Ev z = (‖1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ)‖ ^ 2 /
          (1 - ‖complexDilatation f₀ z‖ ^ 2)) *
        (‖1 - complexDilatation a (f₀ z) * (conj (dz f₀ z) / dz f₀ z) * (φ z / (‖φ z‖ : ℂ)) *
          (1 - conj (complexDilatation f₀ z) * conj (φ z) / (‖φ z‖ : ℂ)) /
          (1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ))‖ ^ 2 /
          (1 - ‖complexDilatation a (f₀ z)‖ ^ 2)) := by
      rw [hEz, hdzg, hdbzg, key]
      rw [hconjv]
      simp only [mul_div_assoc]
    have hA : 0 ≤ ‖φ z‖ * (‖1 - complexDilatation f₀ z * φ z / ‖φ z‖‖ ^ 2 /
        (1 - ‖complexDilatation f₀ z‖ ^ 2)) :=
      mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _)
        (by nlinarith [norm_nonneg (complexDilatation f₀ z)]))
    have hB' : (‖1 - complexDilatation a (f₀ z) * (conj (dz f₀ z) / dz f₀ z) * (φ z / (‖φ z‖ : ℂ)) *
          (1 - conj (complexDilatation f₀ z) * conj (φ z) / (‖φ z‖ : ℂ)) /
          (1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ))‖ ^ 2 /
          (1 - ‖complexDilatation a (f₀ z)‖ ^ 2)) ≤ K := hB
    rw [← hdilz, hEeq]
    calc ‖φ z‖ * ((‖1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ)‖ ^ 2 /
          (1 - ‖complexDilatation f₀ z‖ ^ 2)) *
        (‖1 - complexDilatation a (f₀ z) * (conj (dz f₀ z) / dz f₀ z) * (φ z / (‖φ z‖ : ℂ)) *
          (1 - conj (complexDilatation f₀ z) * conj (φ z) / (‖φ z‖ : ℂ)) /
          (1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ))‖ ^ 2 /
          (1 - ‖complexDilatation a (f₀ z)‖ ^ 2)))
        = (‖φ z‖ * (‖1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ)‖ ^ 2 /
          (1 - ‖complexDilatation f₀ z‖ ^ 2))) * (‖1 - complexDilatation a (f₀ z) *
          (conj (dz f₀ z) / dz f₀ z) * (φ z / (‖φ z‖ : ℂ)) *
          (1 - conj (complexDilatation f₀ z) * conj (φ z) / (‖φ z‖ : ℂ)) /
          (1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ))‖ ^ 2 /
          (1 - ‖complexDilatation a (f₀ z)‖ ^ 2)) := by ring
      _ ≤ (‖φ z‖ * (‖1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ)‖ ^ 2 /
          (1 - ‖complexDilatation f₀ z‖ ^ 2))) * K := mul_le_mul_of_nonneg_left hB' hA
      _ = K * (‖φ z‖ * (‖1 - complexDilatation f₀ z * φ z / (‖φ z‖ : ℂ)‖ ^ 2 /
          (1 - ‖complexDilatation f₀ z‖ ^ 2))) := by ring
  -- step 4: conclude
  have hPtop : phiArea φ F ≠ ⊤ := hφ.2.1.ne
  have hmain : 2 * phiArea φ F ≤ phiArea φ F + ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ * Ev z) := by
    calc 2 * phiArea φ F
        ≤ 2 * ∫⁻ z in F, ENNReal.ofReal ‖-φ z‖ *
            ENNReal.ofReal (lambdaStretchPlane (fun z => -φ z) (fun z => -φ z) g z) := by gcongr
      _ = ∫⁻ z in F, 2 * (ENNReal.ofReal ‖-φ z‖ *
            ENNReal.ofReal (lambdaStretchPlane (fun z => -φ z) (fun z => -φ z) g z)) :=
          (lintegral_const_mul' _ _ (by simp)).symm
      _ ≤ ∫⁻ z in F, (ENNReal.ofReal (X z) + ENNReal.ofReal (‖φ z‖ * Ev z)) :=
          lintegral_mono_ae hstep1
      _ = phiArea φ F + ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ * Ev z) := by
          rw [lintegral_add_left' hXm, hstep3]
  rw [two_mul] at hmain
  have hle := (ENNReal.add_le_add_iff_left hPtop).1 hmain
  calc phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ * Ev z) := hle
    _ ≤ ∫⁻ z in F, ENNReal.ofReal K * ENNReal.ofReal (‖φ z‖ *
        (‖1 - μ.1.1 z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2))) := lintegral_mono_ae hstep4
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **G3 (下属1).** -/
theorem strebel_hamilton_sufficient_of_main_inequality (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (h : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1)
    (hMain : ∀ (ν : BeltramiGamma Γ), teichSetoidGamma Γ ν μ →
      ∀ {φ : ℂ → ℂ}, φ ∈ integrableAutomorphicQD Γ F →
      phiArea φ F ≤ ENNReal.ofReal ((1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1)) *
        ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ *
          (‖1 - μ.1.1 z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2)))) :
    IsExtremalModBoundary Γ μ := by
  intro ν hrel
  have hk0 := beltramiNormH_nonneg μ.1.1
  have hν0 := beltramiNormH_nonneg ν.1.1
  have hk1 := beltramiNormH_lt_one μ.1
  have hν1 := beltramiNormH_lt_one ν.1
  by_cases hA : ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1
  · obtain ⟨φ, hφ, hlim⟩ := h36p_seq_of_hamilton hF μ h hA
    have hκm := s36g_meas μ.1 F
    have hae := h36p_ae_le_normH_F μ hF.1
    have hX := s36g_lim_main hF.1 hF.2.1 hκm hk0 hk1 hae hφ hlim
    refine s36g_final hk0 hk1 hν0 hν1 hX fun n => ?_
    have hMI := hMain ν hrel (hφ n).1
    rw [(hφ n).2] at hMI
    refine s36g_toReal_step (div_nonneg (by linarith) (by linarith)) ?_ hMI
    rw [s36g_expand hF.1 hF.2.1 hκm hk1 hae (hφ n).1 (hφ n).2]
    exact ENNReal.ofReal_ne_top
  · have h0 := s36g_hamiltonNorm_eq_zero (κ := μ.1.1) hA
    linarith

end LiZhongQC
