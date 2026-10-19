import LiZhongQC.Lemmas.StrebelG1Final
import LiZhongQC.Lemmas.S36G1dExhaustion
import LiZhongQC.Lemmas.S36G1dDomains
import LiZhongQC.Lemmas.S36G1dAreaLimit
import LiZhongQC.Lemmas.S36G1dStretchLimit
import LiZhongQC.Lemmas.StrebelGammaG1cSupport
import LiZhongQC.Lemmas.StrebelGammaG1cFinal

/-! S36 G1d final host: `str_g1c` (finite-index reduction applied to the proved `str_g1b`) and the
frozen G1d theorem `str_gamma_eq35_5` (exhaustion by finitely generated subgroups and Poincaré series).
Statements byte-identical to StrebelGammaIface (95317f71). No stubs. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **G1c.** The same for finitely generated `Γ` (elliptic elements allowed). -/
theorem str_g1c (hΓ : IsFuchsian Γ) (hfg : Γ.FG)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  exact s36c_reduce_of_g1b
    (fun {Λ} hΛ hfreeΛ hfgΛ {E} hE μΛ νΛ hrelΛ {ψ} hψ => str_g1b hΛ hfreeΛ hfgΛ hE μΛ νΛ hrelΛ hψ)
    hΓ hfg hF μ ν hrel hφ

/-- **G1d.** The Γ-version of (35.5) for an arbitrary Fuchsian group (exhaustion by finitely generated
subgroups and Poincaré series). -/
theorem str_gamma_eq35_5 (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  obtain ⟨f, hf, hfA, hθ⟩ := h36p_theta_surj hΓ hF φ hφ
  obtain ⟨H, hmono, hsub, hfg, hcover, hker⟩ := s36e_fg_exhaustion hΓ
  have hdom : ∀ i : ℕ, ∃ D : Set ℂ, IsFundamentalDomainH (H i) D ∧ F ⊆ D :=
    fun i => s36e_domain_over hΓ hF (hsub i) (hker i)
  choose D hD hFD using hdom
  have hleft := s36e_area_tendsto hΓ hF H hsub hmono hcover D hD hFD hf hfA hθ
  have hright := s36e_stretch_tendsto hΓ hF H hsub hmono hcover D hD hFD
    μ ν hrel hf hfA hφ hθ
  apply le_of_tendsto_of_tendsto' hleft hright
  intro i
  have hHi := s36c_fuchsian_subgroup hΓ (hsub i)
  obtain ⟨μi, hμi⟩ := s36c_beltrami_restrict (hsub i) μ
  obtain ⟨νi, hνi⟩ := s36c_beltrami_restrict (hsub i) ν
  have hrel_i := s36c_teich_restrict μ ν μi νi hμi hνi hrel
  have hmem := (h36p_poincare hHi (hD i) hf hfA).1
  have hi := str_g1c hHi (hfg i) (hD i) μi νi hrel_i hmem
  simpa only [hμi, hνi] using hi

end LiZhongQC
