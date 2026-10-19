import LiZhongQC.Lemmas.StrebelGammaG1cTiles
import LiZhongQC.Lemmas.StrebelGammaMapFacts
import LiZhongQC.Lemmas.StrebelSurfaceLambda
import LiZhongQC.Lemmas.StrebelGammaTransport

/-!
# G1c lambda covariance and finite-index reduction

Source-only candidate. The two shared predecessor modules are to be registered by Root.
No book theorem is invoked; G1b remains an explicit argument only in the final reduction helper.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Write the frozen automorphy identity in the derivative form needed by str_lambda_conj. -/
theorem s36c_mobius_pullback {F : Set ℂ} {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    φ z = φ (h36p_m γ z) * deriv (h36p_m γ) z ^ 2 := by
  have ha := hφ.2.2 γ hγ z hz
  have hden := k24_d_den_ne_zero (b33_d_det γ)
    (ne_of_gt (show 0 < z.im from hz))
  calc φ z = φ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := ha.symm
    _ = φ (h36p_m γ z) * deriv (h36p_m γ) z ^ 2 := by
      rw [(h36p_m_hasDerivAt γ hz).deriv]
      field_simp [hden]

/-- The lambda density is invariant under Gamma, for the exact frozen invFunOn map.
Reuse the predecessor's str_comm/str_g_facts and str_lambda_conj after their narrow host is approved;
do not reproach the book theorem or duplicate those existing source proofs. -/
theorem s36c_lambda_density_covariant (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) {F : Set ℂ}
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict upperHalf),
      (ENNReal.ofReal ‖φ (h36p_m γ z)‖ * ENNReal.ofReal
        (lambdaStretchPlane φ φ
          (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) (h36p_m γ z))) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
        (lambdaStretchPlane φ φ
          (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  let g : ℂ → ℂ := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1
  obtain ⟨K, hgK, hgimage, hcomm⟩ := str_g_facts μ ν hrel
  have hgH : MapsTo g upperHalf upperHalf := by
    intro z hz
    rw [← hgimage]
    exact mem_image_of_mem _ hz
  intro γ hγ
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
  have hgz : g z ∈ upperHalf := hgH hz
  have hinv : ∀ w ∈ upperHalf,
      ∀ᶠ u in 𝓝 w, h36p_m γ⁻¹ (h36p_m γ u) = u := by
    intro w hw
    filter_upwards [isOpen_upperHalf.mem_nhds hw] with u hu
    exact h36p_a_inv_m γ hu
  have hinv' : ∀ᶠ u in 𝓝 (h36p_m γ z), h36p_m γ (h36p_m γ⁻¹ u) = u := by
    filter_upwards [isOpen_upperHalf.mem_nhds (h36p_m_mem γ hz)] with u hu
    simpa only [inv_inv] using h36p_a_inv_m γ⁻¹ hu
  have hevent : (g ∘ h36p_m γ) =ᶠ[𝓝 z] (h36p_m γ ∘ g) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with u hu
    exact hcomm γ hγ u hu
  have hderiv : ∀ w ∈ upperHalf, deriv (h36p_m γ) w ≠ 0 := by
    intro w hw
    rw [(h36p_m_hasDerivAt γ hw).deriv]
    exact div_ne_zero one_ne_zero (pow_ne_zero _
      (k24_d_den_ne_zero (b33_d_det γ) (ne_of_gt (show 0 < w.im from hw))))
  have htarget : φ (g z) = φ (g (h36p_m γ z)) * deriv (h36p_m γ) (g z) ^ 2 := by
    rw [show g (h36p_m γ z) = h36p_m γ (g z) from hcomm γ hγ z hz]
    exact s36c_mobius_pullback hφ hγ hgz
  have hlam : lambdaStretchPlane φ φ g z = lambdaStretchPlane φ φ g (h36p_m γ z) :=
    str_lambda_conj (Ls := g) (Lc := g)
      (B := h36p_m γ) (A := h36p_m γ) (B' := h36p_m γ⁻¹) (A' := h36p_m γ⁻¹)
      (Qs := φ) (Qt := φ) (Φ := φ) (Φ' := φ)
      (h36p_m_hasDerivAt γ hz).differentiableAt
      (h36p_m_hasDerivAt γ⁻¹ (h36p_m_mem γ hz)).differentiableAt rfl
      (hinv z hz) hinv'
      (h36p_m_hasDerivAt γ hgz).differentiableAt
      (h36p_m_hasDerivAt γ⁻¹ (h36p_m_mem γ hgz)).differentiableAt
      (hinv (g z) hgz)
      (hgK.2.2.1.1.continuousAt (isOpen_upperHalf.mem_nhds hz))
      hevent (hcomm γ hγ z hz).symm (hderiv z hz) (hderiv (g z) hgz)
      (s36c_mobius_pullback hφ hγ hz) htarget
  have harea := str_inv' hφ.1 hφ.2.2 hγ hz
  rw [indicator_of_mem (h36p_m_mem γ hz), indicator_of_mem hz] at harea
  change (ENNReal.ofReal ‖φ (h36p_m γ z)‖ * ENNReal.ofReal
    (lambdaStretchPlane φ φ g (h36p_m γ z))) *
      ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
    ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)
  rw [← hlam]
  calc (ENNReal.ofReal ‖φ (h36p_m γ z)‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4)
      = (ENNReal.ofReal ‖φ (h36p_m γ z)‖ *
          ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4)) *
          ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by ac_rfl
    _ = _ := by rw [harea]

/-- The finite-index reduction data are produced from the original inputs, not assumed.
Both integrals have the same positive finite degree, and the underlying BeltramiH elements agree exactly. -/
theorem s36c_reduction_data (hΓ : IsFuchsian Γ) (hfg : Γ.FG)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    ∃ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (E : Set ℂ) (d : ℕ) (μΔ νΔ : BeltramiGamma Δ),
      Δ ≤ Γ ∧ Γ ⊓ Subgroup.zpowers (-1) ≤ Δ ∧
      d = Δ.relIndex Γ ∧ d ≠ 0 ∧ IsFuchsian Δ ∧ ActsFreely Δ ∧ Δ.FG ∧
      IsFundamentalDomainH Δ E ∧ μΔ.1 = μ.1 ∧ νΔ.1 = ν.1 ∧
      teichSetoidGamma Δ νΔ μΔ ∧ φ ∈ integrableAutomorphicQD Δ E ∧
      phiArea φ E = (d : ℝ≥0∞) * phiArea φ F ∧
      (∫⁻ z in E, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
        (lambdaStretchPlane φ φ
          (Function.invFunOn (fMuSym νΔ.1.1) upperHalf ∘ fMuSym μΔ.1.1) z)) =
      (d : ℝ≥0∞) *
        (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
          (lambdaStretchPlane φ φ
            (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z)) := by
  obtain ⟨Δ, hle, hidx, hfgΔ, hΔ, hfree, hker⟩ := s36c_selberg_effective hΓ hfg
  obtain ⟨d, T, hdeg, hd, hT, hcos⟩ := s36c_right_representatives hle hidx
  let E : Set ℂ := ⋃ i : Fin d, h36p_m (T i) '' F
  have hE : IsFundamentalDomainH Δ E :=
    (s36c_fundamental_tiling hΓ hle hker T hT hcos hF).1
  obtain ⟨μΔ, hμ⟩ := s36c_beltrami_restrict hle μ
  obtain ⟨νΔ, hν⟩ := s36c_beltrami_restrict hle ν
  have hrelΔ := s36c_teich_restrict μ ν μΔ νΔ hμ hν hrel
  have harea := s36c_area_scaling hΓ hle hker T hT hcos hF hφ
  have hφΔ : φ ∈ integrableAutomorphicQD Δ E :=
    s36c_automorphic_restrict hle hφ harea.2
  refine ⟨Δ, E, d, μΔ, νΔ, hle, hker, hdeg, hd, hΔ, hfree, hfgΔ,
    hE, hμ, hν, hrelΔ, hφΔ, harea.1, ?_⟩
  rw [s36c_comparison_map_restrict μ ν μΔ νΔ hμ hν]
  exact s36c_density_scaling hΓ hle hker T hT hcos hF
    (fun z => ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ
        (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z))
    (s36c_lambda_density_covariant μ ν hrel hφ)

/-- Assembly target with the exact G1b conclusion as a temporary explicit predecessor argument.
The final frozen str_g1c will supply the proved str_g1b here; no such input is added to the book theorem. -/
theorem s36c_reduce_of_g1b
    (g1b : ∀ {Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)},
      IsFuchsian Λ → ActsFreely Λ → Λ.FG →
      ∀ {E : Set ℂ}, IsFundamentalDomainH Λ E →
      ∀ (μΛ νΛ : BeltramiGamma Λ), teichSetoidGamma Λ νΛ μΛ →
      ∀ {ψ : ℂ → ℂ}, ψ ∈ integrableAutomorphicQD Λ E →
      phiArea ψ E ≤ ∫⁻ z in E, ENNReal.ofReal ‖ψ z‖ * ENNReal.ofReal
        (lambdaStretchPlane ψ ψ
          (Function.invFunOn (fMuSym νΛ.1.1) upperHalf ∘ fMuSym μΛ.1.1) z))
    (hΓ : IsFuchsian Γ) (hfg : Γ.FG)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ
        (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  obtain ⟨Δ, E, d, μΔ, νΔ, hle, hker, hdeg, hd, hΔ, hfree, hfgΔ,
    hE, hμ, hν, hrelΔ, hφΔ, harea, hlam⟩ :=
    s36c_reduction_data hΓ hfg hF μ ν hrel hφ
  have h := g1b hΔ hfree hfgΔ hE μΔ νΔ hrelΔ hφΔ
  rw [harea, hlam] at h
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hd)
    (ENNReal.natCast_ne_top d)).mp h

end LiZhongQC
