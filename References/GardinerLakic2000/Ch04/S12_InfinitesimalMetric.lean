import References.GardinerLakic2000.Ch04.S11_StrebelPoints

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.12 Teichmüller's infinitesimal metric

Source `teichmuller.txt`, lines 4582–4656.

* Theorem 13 (`d([0], [tμ]) = t sup |Re ∬ μφ| + O(t²)`, l. 4585; cited l. 11115) — `thm4_13`
* Definition (`F([μ], ν)`, (4.28), l. 4628–4633) — `infTeichNormAt`
* Theorem 14 (`d([μ], [μ + tν]) = t F([μ], ν) + O(t²)`, l. 4625) — `thm4_14`

Not items (DESIGN §3): (4.29) and the derivative `S` of `α` (l. 4634–4655), steps of the proof.

**Conventions.** Theorem 13 is stated in the Part A setting; "the constant in `O(t²)` depends only on `k₁`" is the
quantifier order `∀ k₁ ∃ C δ ∀ R μ t`. Theorem 14 involves `A(f^μ(R))` and the map `f^μ`, so it is stated in the
Fuchsian model (B0.1, `para5_2_teichGamma_equiv`): `f^μ = w_μ = LiZhongQC.fMuSym μ`, `f^μ(R) = ℍ/G^μ` with
`G^μ = w_μ G w_μ⁻¹` (given with its defining relation, as in `LiZhongQC.eq33_12_translation`) and a fundamental domain
`F^μ` of `G^μ`; `θ = p̄/p`, `p = ∂_z w_μ`, and the integrand is transported by `z = w_μ⁻¹(w)`. The segment
`t ↦ μ + tν` is given as a family `σ_t ∈ M(G)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization quadDiffNorm BeltramiGamma teichSetoidGamma teichDistanceGamma
  integrableAutomorphicQD phiArea IsFundamentalDomainH fMuSym mobiusFn upperHalf dz)

/-- **Theorem 13** (§4.12, l. 4585). Let `μ ∈ M(R)` with `0 < ‖μ‖∞ ≤ k₁`. Then for `t > 0` tending to `0`,
`d([0], [tμ]) = t sup |Re ∬_R μφ| + O(t²)`, the supremum over `φ ∈ A(R)` with `‖φ‖ = 1`; the constant in `O(t²)`
depends only on `k₁`. -/
theorem thm4_13 {k₁ : ℝ} (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) : ∃ C δ : ℝ, 0 < δ ∧
    ∀ (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
      (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → R), IsFuchsian Γ →
      IsUniformization Γ p → (∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) →
      ∀ (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) (μ : R → ℂ → ℂ), μ ∈ beltramiSpace R → 0 < beltramiNormRS μ →
      beltramiNormRS μ ≤ ENNReal.ofReal k₁ → ∀ (t : ℝ), 0 < t → t < δ → ∀ ν : beltramiBall R,
      ν.1 = (fun x z => t * μ x z) →
      |teichDist p (Quot.mk (teichRel p) ⟨0, h0⟩) (Quot.mk (teichRel p) ν) - t * bigJ μ| ≤ C * t ^ 2 := by
  sorry

/-- **Definition** ((4.28), §4.12, l. 4628–4633). `F([μ], ν) = sup |Re ∬_{f^μ(R)} φ(w) [ν/(1 − |μ|²) · 1/θ] du dv|`,
the supremum over `φ ∈ A(f^μ(R))` with `‖φ‖ = 1`, `θ = p̄/p`, `p = ∂_z f^μ`, the bracket evaluated at
`z = (f^μ)⁻¹(w)` (Fuchsian model, see the module docstring). -/
def infTeichNormAt (Gμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (Fμ : Set ℂ) (μ ν : ℂ → ℂ) : ℝ :=
  ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableAutomorphicQD Gμ Fμ ∧ phiArea φ Fμ = 1),
    |(∫ w in Fμ, φ w * (ν (Function.invFunOn (fMuSym μ) univ w) /
        (1 - ‖μ (Function.invFunOn (fMuSym μ) univ w)‖ ^ 2) *
        (dz (fMuSym μ) (Function.invFunOn (fMuSym μ) univ w) /
          conj (dz (fMuSym μ) (Function.invFunOn (fMuSym μ) univ w))))).re|

/-- **Theorem 14** (§4.12, l. 4625). Let `μ` and `μ + tν` (`t > 0`) in `M(R)` represent points of `T(R)`. Then
`d([μ], [μ + tν]) = t F([μ], ν) + O(t²)`. Modelling: see the module docstring. -/
theorem thm4_14 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) (μ : BeltramiGamma Γ) (ν : ℂ → ℂ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (σ : ℝ → BeltramiGamma Γ) (hσ : ∀ t, 0 < t → t < δ₀ → (σ t).1.1 = fun z => μ.1.1 z + t * ν z)
    {Gμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hGμ : (∀ γ ∈ Γ, ∃ γ' ∈ Gμ, ∀ z ∈ upperHalf,
      fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z)) ∧
      ∀ γ' ∈ Gμ, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
        fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z))
    {Fμ : Set ℂ} (hFμ : IsFundamentalDomainH Gμ Fμ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      |teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) (σ t)) -
        t * infTeichNormAt Gμ Fμ μ.1.1 ν| ≤ C * t ^ 2 := by
  sorry

end GardinerLakic2000
