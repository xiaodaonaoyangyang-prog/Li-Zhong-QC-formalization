import References.GardinerLakic2000.Ch15.S02_AsymptoticBeltramiDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 15 §15.3 Weighted Beltrami coefficients

Source `teichmuller.txt`, lines 11477–11766 (Chapter 15, §15.3).

* Definition (`K(μ) = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)`, l. 11480) — `kOf`
* Lemma 2 ((15.7), l. 11481) — `lemma15_2`

Not items: Steps I–VII and (15.8)–(15.15) (proof of Lemma 2). Modelling: `f⁻¹_{F,ν}` (the quasiconformal map with
Beltrami coefficient `νχ_{R∖F}`, l. 11480) is a quasiconformal `g : R → Y` onto a surface of batch A's `RSBundle`
with `HasBeltramiCoeff g (νχ_{R∖F})`; the class `τ = [f_{F,ν}] ∈ T(Y)` is the class of the coefficient `σ` of
`g⁻¹ : Y → R` for a uniformization `p_Y` of `Y`, and "`τ` is represented by `η̂`" is `teichRel p_Y η̂ σ` (stated for
all membership proofs, so no proof term occurs). `H(ν)` is the boundary dilatation `H` of the class of `ν` (batch B's
`boundaryDilatationH`), `K(ν) = kOf ν`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization IsQCRS)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§15.3, l. 11480). `K(μ) = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)`. -/
def kOf (μ : R → ℂ → ℂ) : ℝ := (1 + (beltramiNormRS μ).toReal) / (1 - (beltramiNormRS μ).toReal)

/-- **Lemma 2** (§15.3, l. 11481). Let `ν ∈ M(R)` and `0 < α < 1`. For every `ε > 0` there is a compact `E₀` such that
for every compact `E ⊇ E₀` there is a compact `F ⊇ E` for which the class `τ = [f_{F,ν}] ∈ T(f⁻¹_{F,ν}(R))` is
represented by `η̂ = η χ_{f⁻¹(R∖F)} + α η χ_{f⁻¹(F∖E)}` with (15.7):
`(K(ν)H(ν) − 1) K(η) + K(αη)(K(ν) − H(ν)) < H(ν)(K(ν)² − 1) + ε`.
[CORRECTION] (AUDIT5_GL1518 G15-9) The coefficient `σ` of `f_{F,ν} = g⁻¹` is assumed in `M(Y)` (`hσ`); before, the class
clause was vacuous for a `σ` with junk values off the local domains. -/
theorem lemma15_2 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (ν : beltramiBall R) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ E₀ : Set R, IsCompact E₀ ∧ ∀ E : Set R, IsCompact E → E₀ ⊆ E → ∃ F : Set R, IsCompact F ∧ E ⊆ F ∧
      ∀ (Y : RSBundle.{u}) (g : R ≃ₜ Y.carrier), IsQCRS g → HasBeltramiCoeff g (restrictBeltrami ν.1 Fᶜ) →
        ∀ (ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (pY : UpperHalfPlane → Y.carrier), IsFuchsian ΓY →
          IsUniformization ΓY pY → ∀ σ : Y.carrier → ℂ → ℂ, HasBeltramiCoeff (g.symm : Y.carrier → R) σ →
            ∀ hσ : σ ∈ beltramiBall Y.carrier,
            ∃ η : Y.carrier → ℂ → ℂ, η ∈ beltramiBall Y.carrier ∧
              (∀ h₁ : (fun x z => restrictBeltrami η (g '' Fᶜ) x z + α * restrictBeltrami η (g '' (F \ E)) x z) ∈
                  beltramiBall Y.carrier, teichRel pY ⟨_, h₁⟩ ⟨σ, hσ⟩) ∧
              (kOf ν.1 * (boundaryDilatationH p (Quot.mk (teichRel p) ν)).toReal - 1) * kOf η +
                  kOf (fun x z => α * η x z) * (kOf ν.1 - (boundaryDilatationH p (Quot.mk (teichRel p) ν)).toReal) <
                (boundaryDilatationH p (Quot.mk (teichRel p) ν)).toReal * (kOf ν.1 ^ 2 - 1) + ε := by
  sorry

end GardinerLakic2000
