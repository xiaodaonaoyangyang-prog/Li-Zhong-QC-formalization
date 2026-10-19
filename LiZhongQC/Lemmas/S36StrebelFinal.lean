import LiZhongQC.Lemmas.S36G1dFinal
import LiZhongQC.Lemmas.StrebelGammaEndgame

/-! S36 final host: the Γ main inequality (G2) from `str_gamma_eq35_5` and the Endgame bridge, Strebel's
sufficiency (G3), and the book helper `s36f_strebel_hamilton_sufficient` (docstring and statement byte-identical
to S36_Hamilton.lean `strebel_hamilton_sufficient`, md5 6534e9f2, apart from the name); the book block relocates
here at install with body `exact s36f_strebel_hamilton_sufficient hΓ hF μ h`. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **G2.** The Γ main inequality (simplified, GL (4.21)): for `ν ∼ μ` and `φ ∈ A(Γ,F)`,
`∬_F |φ| ≤ K[ν] ∬_F |φ| |1 − μφ/|φ||²/(1 − |μ|²)`, `K[ν] = (1+‖ν‖∞)/(1−‖ν‖∞)`. -/
theorem str_gamma_main_inequality (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ENNReal.ofReal ((1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1)) *
      ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ *
        (‖1 - μ.1.1 z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖μ.1.1 z‖ ^ 2))) := by
  exact str_gamma_main_inequality_of_eq35_5 hΓ hF μ ν hrel hφ
    (fun {ψ} hψ => str_gamma_eq35_5 hΓ hF μ ν hrel hψ)

/-- **G3 (下属1).** -/
theorem strebel_hamilton_sufficient' (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (h : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1) : IsExtremalModBoundary Γ μ := by
  exact strebel_hamilton_sufficient_of_main_inequality hΓ hF μ h
    (fun ν hrel {φ} hφ => str_gamma_main_inequality hΓ hF μ ν hrel hφ)

/-- §36.2 (K. Strebel): the Hamilton condition is also sufficient for extremality. -/
theorem s36f_strebel_hamilton_sufficient (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (h : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1) : IsExtremalModBoundary Γ μ := by
  exact strebel_hamilton_sufficient' hΓ hF μ h

section RelocatedS36


/-- §36.2 (K. Strebel): the Hamilton condition is also sufficient for extremality. -/
theorem strebel_hamilton_sufficient (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (h : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1) : IsExtremalModBoundary Γ μ := by
  exact s36f_strebel_hamilton_sufficient hΓ hF μ h

end RelocatedS36

end LiZhongQC
