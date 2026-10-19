import LiZhongQC.Lemmas.F1FinalAssembly
import LiZhongQC.Lemmas.F1EndNormalForm
import LiZhongQC.Lemmas.F1BExteriors

/-! F1 endpoint: `ft1fas_decomposition_with_ordinary` (frozen D1F1Contract), from the conditional
assembly and the accepted producers `ft1gb_periodic_exteriors` and `ft1fas_end_normal_form`. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Coherent F1 decomposition and its full spherical ordinary funnel arcs.
Proposed shared export of the F1 assembly lane, with original alternatives intact. -/
theorem ft1fas_decomposition_with_ordinary (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) :
    (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    ∃ (n m : ℕ) (C : Set UpperHalfPlane) (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (B h : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : Fin m → ℝ),
      IsCompact C ∧
      (∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ j, h j ∈ Γ ∧ 1 < lam j ∧ 0 < θ j ∧ θ j < π ∧
        ∀ τ : UpperHalfPlane, (((B j)⁻¹ • (h j • (B j • τ)) : UpperHalfPlane) : ℂ) = (lam j : ℂ) * (τ : ℂ)) ∧
      (∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
        i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k) ∧
      (∀ j j' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ j →
        arg (((B j')⁻¹ • (γ • (B j • τ)) : UpperHalfPlane) : ℂ) < θ j' →
        j = j' ∧ ∃ k : ℤ, γ = h j ^ k ∨ γ = -h j ^ k) ∧
      (∀ i j γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
        θ j ≤ arg (((B j)⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ)) ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨ (∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) ∨
        ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j) ∧
      (∀ j (t : ℝ), 0 < t →
      mobiusSL (slRealToComplex (B j)) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ) ∧
      (∀ x : ExtPlane, x ∈ ordinarySet Γ →
      ∃ γ ∈ Γ, ∃ j : Fin m, ∃ t : ℝ, 0 < t ∧
        x = mobiusSL (slRealToComplex (γ * B j)) ((t : ℂ) : ExtPlane)) :=
  ft1fas_assembly_of_exteriors hΓ (ft1gb_periodic_exteriors hΓ hfree hfg)
    (ft1fas_end_normal_form hΓ hfree)

end LiZhongQC
