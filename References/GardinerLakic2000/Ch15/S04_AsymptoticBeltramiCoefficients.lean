import References.GardinerLakic2000.Ch15.S03_WeightedBeltramiCoefficients

/-!
# Gardiner–Lakic 2000, Ch. 15 §15.4 Asymptotic Beltrami coefficients

Source `teichmuller.txt`, lines 11767–11914 (Chapter 15, §15.4).

* Theorem 2 (l. 11770) — `thm15_2`
* Proposition 2 (l. 11905; used in §17.1) — `prop15_2`
* Corollary 2 (l. 11907) — `cor15_2_2`

Not items: the proof of Theorem 2 (l. 11772–11903); the exercises (l. 11909–11913). Modelling: as §15.1; a class of
`AT` is batch D's `AsymTeichSpace` (a `Quot` of `M(R)` by `asymRel`); "`h*(η) = h(η)`" is `IsAsymExtremal`;
`k₀(τ)` is batch B's `extremalK`; `T₀` is batch D's `IsInT0`; a vanishing representative has `b*(η) = 0`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 2** (§15.4, l. 11770). Every class in `AT` is represented by a Beltrami coefficient `η` with
`h*(η) = h(η)`. -/
theorem thm15_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (a : AsymTeichSpace R p) :
    ∃ η : beltramiBall R, Quot.mk (asymRel p) η = a ∧ IsAsymExtremal p η := by
  sorry

/-- **Proposition 2** (§15.4, l. 11905). For every `τ ∈ T` and `ε > 0` there is a representative `η` of `τ` with
`‖η‖∞ < k₀(τ) + ε` and `h([τ]) = h*(η)`. -/
theorem prop15_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (τ : TeichSpace R p) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : beltramiBall R, Quot.mk (teichRel p) η = τ ∧ (beltramiNormRS η.1).toReal < extremalK p τ + ε ∧
      IsAsymExtremal p η := by
  sorry

/-- **Corollary 2** (§15.4, l. 11907). For every `τ ∈ T₀` and `ε > 0` there is a vanishing representative `η` of `τ`
with `‖η‖∞ < k₀(τ) + ε`. -/
theorem cor15_2_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (τ : TeichSpace R p) (hτ : IsInT0 p τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : beltramiBall R, Quot.mk (teichRel p) η = τ ∧ (beltramiNormRS η.1).toReal < extremalK p τ + ε ∧
      boundaryDilatationStar η.1 = 0 := by
  sorry

end GardinerLakic2000
