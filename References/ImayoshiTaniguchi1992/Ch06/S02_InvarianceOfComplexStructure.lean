import References.ImayoshiTaniguchi1992.Ch06.S01_BersEmbedding
import LiZhongQC.Ch11.S36_Hamilton
import References.GardinerLakic2000.Ch06.S05_InfinitesimalTheory

/-!
# Imayoshi–Taniguchi, Chapter 6 §6.2: Invariance of the complex structure of Teichmüller space

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 6 §6.2 (`full.md` IT1:5420–5830,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions (Ch. 6, IT1:5200): `Γ` is the Fuchsian model of a closed Riemann surface of genus `g ≥ 2`
(`LiZhongQC.IsFuchsian`, `IsCocompact`) in `H = ℍ`, `H*` the lower half-plane. `T(Γ)` is `LiZhongQC.TeichGamma Γ` and Bers' embedding
is `LiZhongQC.bersMapGamma`. `w_μ` is the normalized quasiconformal self-map of `ℂ̂` with dilatation `μ` on `H` and `0` on `H*`
(`LiZhongQC.normalizedSolution μ`, `μ ∈ B(H, Γ)₁` extended by `0`); `Φ(μ) = S(w_μ)|_{H*}` is `LiZhongQC.bersFunction μ` (zero off
`H*`). The hyperbolic `L^∞`-norm on `H*` is `LiZhongQC.bersNormL` (`sup (Im z)² |φ(z)|`, which is `‖φ‖_∞` of IT1:5440, so that
`V = {φ ∈ A₂(H*, Γ) | ‖φ‖_∞ < 1/2}` is `aheV Γ`). **Chart-wise reading (IT-D5):** no complex structure is put on `T(Γ)`; "`Ψ`
holomorphic with `B Ψ = id`" is the statement `B Ψ = id` together with continuity of `Ψ` and openness of its image (the structure on
`T(Γ)` is defined through `B`, so holomorphy of `Ψ` is then trivial). The Teichmüller distance is the project's `teichDistanceGamma`
(half of IT's `d`, IT-D3), which does not matter for continuity and openness.

* Theorem 6.8 (local right inverse `Ψ` of Bers' embedding on `V`, IT1:5444) — `aheV`, `thm6_8`
* Theorem 6.9 (Ahlfors–Weill: `B([w_{μ_φ}]) = φ` for `‖φ‖_∞ < 1/2`, IT1:5446) — exists: `LiZhongQC.lemma33_3`
* Corollary to Theorem 6.9, first assertion (a real-analytic `w_μ` representing `B⁻¹(φ)`, IT1:5582) — `cor6_9_a`
* Corollary to Theorem 6.9, second assertion (every point of `T(R)` has a real-analytic representative, IT1:5584) — `cor6_9_b`
* Theorem 6.10 (`Φ̇₀[ν] = -(6/π) ∬ ν/(ζ - z)⁴`, IT1:5610) — exists: `GardinerLakic2000.thm6_5`
* Theorem 6.11 (the derivative `Φ̇_μ[ν]` at a general `μ`, IT1:5642) — `phiDot`, `thm6_11`
* Theorem 6.12 (`[f₁]_*` and Bers' embedding are biholomorphic, invariance of the complex structure, IT1:5716) — exists:
  `Lehto1987.thm5_5_5`, `Lehto1987.thm5_5_4`
* Lemma 6.13 (an injective holomorphic map of a domain of `ℂⁿ` into `ℂⁿ` has non-vanishing Jacobian, IT1:5754) — omitted:
  general several complex variables, not Teichmüller theory
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (TeichGamma BeltramiGamma bersMapGamma bersFunction bersNormL teichDistanceGamma normalizedSolution automorphicQD
  upperHalf lowerHalf IsFuchsian IsCocompact dz)
open Lehto1987 (LinfG)

/-- **The neighbourhood `V` of the origin in `A₂(H*, Γ)`** (IT1:5440): the `Γ`-automorphic holomorphic quadratic differentials
`φ` on `H*` (extended by `0`) with `‖φ‖_∞ = sup (Im z)² |φ(z)| < 1/2`. -/
def aheV (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {φ | φ ∈ automorphicQD Γ ∧ bersNormL φ < ENNReal.ofReal (1 / 2)}

/-- **Theorem 6.8** (Ch. 6 §6.2.1). Let `V = {φ ∈ A₂(H*, Γ) | ‖φ‖_∞ < 1/2}` and `Ψ(φ) = [w_{μ_φ}]`, where
`μ_φ(z) = -2 (Im z)² φ(\bar z)` the Bers Beltrami differential of `φ` (as in `LiZhongQC.lemma33_3`). Then `Ψ : V → T(Γ)` is
continuous, `U = Ψ(V)` is an open neighbourhood of the base point in `T(Γ)` and `Ψ : V → U` is a right inverse of Bers' embedding,
`B Ψ = id` (a holomorphic section for the structure defined by `B`). -/
theorem thm6_8 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hc : IsCocompact Γ) :
    ∃ Ψ : (ℂ → ℂ) → TeichGamma Γ,
      (∀ φ ∈ aheV Γ, ∃ μ : BeltramiGamma Γ, (∀ z ∈ upperHalf, μ.1.1 z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
        Ψ φ = Quotient.mk _ μ) ∧
      (∀ φ ∈ aheV Γ, bersMapGamma Γ (Ψ φ) = φ) ∧
      (∀ φ ∈ aheV Γ, ∀ ε > 0, ∃ δ > 0, ∀ φ' ∈ aheV Γ, bersNormL (φ' - φ) < ENNReal.ofReal δ →
        teichDistanceGamma (Ψ φ') (Ψ φ) < ε) ∧
      (∀ p ∈ Ψ '' aheV Γ, ∃ ε > 0, ∀ q, teichDistanceGamma q p < ε → q ∈ Ψ '' aheV Γ) := by
  sorry

/-- **Corollary to Theorem 6.9, first assertion** (Ch. 6 §6.2.2). For every `φ ∈ V` there is `μ ∈ B(H, Γ)₁` such that `w_μ` is
real-analytic on `H` and `B⁻¹(φ) = [w_μ]`, i.e. `B([w_μ]) = φ`. -/
theorem cor6_9_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hc : IsCocompact Γ) {φ : ℂ → ℂ}
    (hφ : φ ∈ aheV Γ) :
    ∃ μ : BeltramiGamma Γ, AnalyticOnNhd ℝ (normalizedSolution μ.1.1) upperHalf ∧
      bersMapGamma Γ (Quotient.mk _ μ) = φ := by
  sorry

/-- **Corollary to Theorem 6.9, second assertion** (Ch. 6 §6.2.2). Every point `[S, f]` of the Teichmüller space `T(R)` of
`R = H/Γ` is represented by a real-analytic quasiconformal map `g : R → S`. In the model `T(Γ)`: every class contains a
`μ ∈ B(H, Γ)₁` with `w_μ` real-analytic on `H` (the lift of `g` to the universal covers). -/
theorem cor6_9_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hc : IsCocompact Γ)
    (p : TeichGamma Γ) :
    ∃ μ : BeltramiGamma Γ, (Quotient.mk _ μ : TeichGamma Γ) = p ∧ AnalyticOnNhd ℝ (normalizedSolution μ.1.1) upperHalf := by
  sorry

/-- **The formal derivative `Φ̇_μ[ν]`** (Theorem 6.11, formula (6.10)): on `H*`,
`z ↦ [ -(6/π) ∬_H ν(ζ) ((w_μ)_ζ(ζ))² / (w_μ(ζ) - w_μ(z))⁴ dξ dη ] w_μ'(z)²`, and `0` off `H*`. The partial derivative `(w_μ)_ζ`
is `LiZhongQC.dz` of the normalized solution (it exists almost everywhere; junk `0` elsewhere). -/
def phiDot (μ ν : ℂ → ℂ) : ℂ → ℂ :=
  lowerHalf.indicator fun z =>
    (-(6 / π : ℂ) * ∫ ζ in upperHalf, ν ζ * (dz (normalizedSolution μ) ζ) ^ 2 /
        (normalizedSolution μ ζ - normalizedSolution μ z) ^ 4) * (deriv (normalizedSolution μ) z) ^ 2

/-- **Theorem 6.11** (Ch. 6 §6.2.2). For every `μ ∈ B(H, Γ)₁` and `ν ∈ B(H, Γ)`, the derivative `Φ̇_μ[ν]` exists and is given by
(6.10): if `μ_t ∈ B(H, Γ)₁` for `t` near `0` with `μ_t = μ + tν + tε(t)`, `‖ε(t)‖_∞ → 0` as `t → 0`, then
`(Φ(μ_t) - Φ(μ))/t → Φ̇_μ[ν]` in the hyperbolic `L^∞`-norm `bersNormL`. -/
theorem thm6_11 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hc : IsCocompact Γ)
    (μ : BeltramiGamma Γ) {ν : ℂ → ℂ} (hν : ν ∈ LinfG Γ) (μt : ℂ → ℂ → ℂ)
    (hμt : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ m : BeltramiGamma Γ, m.1.1 = μt t)
    (hε : Tendsto (fun t : ℂ => eLpNorm (fun z => (μt t z - μ.1.1 z - t * ν z) / t) ⊤ volume) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun t : ℂ => bersNormL (t⁻¹ • (bersFunction (μt t) - bersFunction μ.1.1) - phiDot μ.1.1 ν)) (𝓝[≠] 0) (𝓝 0) := by
  sorry

end ImayoshiTaniguchi1992
