import References.GardinerLakic2000.Ch06.S03_BersEmbedding

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.4 The manifold structure

Source `teichmuller.txt`, lines 5755–5826.

* Definition (`A(G)` and `B(G)` on `ℍ`, l. 5757–5768) — exists: `LiZhongQC.integrableAutomorphicQD`
  `GardinerLakic2000.boundedCuspForms` (on ℍ the curvature −4 density gives the book's (2y)²)
* Definition (holomorphic maps between open sets of cusp-form spaces, l. 5823) — `IsHolBMap`, `cuspFormsL`
* Theorem 2 (the Ahlfors–Weill chart at the origin, l. 5774) — `thm6_2`
* Definition (complex Banach manifold structure on `T(G)`, l. 5787) — `IsBanachAtlasT`
* Theorem 3 (`T(G)` is a complex Banach manifold, l. 5787) — `thm6_3`
* Theorem 4 (the transition maps are holomorphic, l. 5817) — `thm6_4`

Not items (DESIGN §3): `B(G^μ)`, `B_*(G^μ)` ((6.15), (6.16)), the isometries between them and the isometric
isomorphism `T(G₁) → T(G)` (l. 5791–5811), used in the proofs only; the identification `M(R) = M(G)`,
`T(R) = T(G)` (l. 5770; `para5_2_teichGamma_equiv`).

**Conventions (B0.3).** Openness and continuity on `T(G)` are explicit, for `LiZhongQC.teichDistanceGamma` (the
book's quotient topology; the metric topology is the same [reading]); the charts take values in `B(G)` on `𝕃`, where
the Bers map lives (§6.4 writes `B(G)` on `ℍ`; `z ↦ z̄` is an isometry between the two). A map between subsets of
`B(G)` is holomorphic when it is holomorphic along every complex line through every point, evaluated at every
`z ∈ 𝕃`, and locally bounded in the cusp norm (weak reading, A0.6: this is Fréchet holomorphy for locally bounded
maps). Theorem 4 is stated for the transition map `χ` of the project (`LiZhongQC.b33_t_chi`), which sends the chart at
`[μ₀]` to the chart at the origin; the book's `Φ̄ ∘ β ∘ Φ̄₁⁻¹` is its inverse, again a map `b33_t_chi λ₀` for the
coefficient `λ₀` of `(w^{μ₀})⁻¹`, so the statement for all `μ₀` covers it [reading]. The formula of Theorem 4
(`S(w^ν̂)(w) w^μ′(z)² + S(w^μ)(z)`, with `ν̂` read `μ̂` [OCR?]) is recorded here only.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (BeltramiH TeichGamma lowerHalf bersMapGamma bersFunction teichDistanceGamma IsFuchsian)

/-- **Definition** (holomorphic maps of cusp forms, §6.4, l. 5813–5825). `T` is holomorphic on the (open) set `A` of
functions on `𝕃`, with directions in the space `D` containing `A`: for all `φ ∈ A`, every direction `ψ ∈ D` and every
`z ∈ 𝕃`, `t ↦ T(φ + tψ)(z)` is holomorphic near `t = 0`, and `T` is locally bounded in the cusp norm. -/
def IsHolBMap (D A : Set (ℂ → ℂ)) (T : (ℂ → ℂ) → ℂ → ℂ) : Prop :=
  (∀ φ ∈ A, ∀ ψ ∈ D, ∀ z ∈ lowerHalf, ∃ r > 0,
      DifferentiableOn ℂ (fun t : ℂ => T (φ + t • ψ) z) (ball 0 r)) ∧
    ∀ φ ∈ A, ∃ r > 0, ∃ C : ℝ, ∀ φ' ∈ A, cuspNorm lowerHalf (φ' - φ) < ENNReal.ofReal r →
      cuspNorm lowerHalf (T φ') ≤ ENNReal.ofReal C

/-- The space `B(G)` of cusp forms on `𝕃` of the chart values (extended by `0` off `𝕃`), the directions for
`IsHolBMap`. -/
def cuspFormsL (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {φ | φ ∈ boundedCuspForms Γ lowerHalf ∧ ∀ z ∉ lowerHalf, φ z = 0}

/-- **Theorem 2** (§6.4, l. 5774). Let `U = {[μ] ∈ T(G) : d(0, [μ]) < ½ log 2}`. Then `Φ̄|U` is a homeomorphism onto
an open set contained in the ball of radius 2 and containing the ball of radius `2/3` of `B(G)`. -/
theorem thm6_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    let U := {p : TeichGamma Γ | teichDistanceGamma (LiZhongQC.TeichGamma.origin Γ) p < 1 / 2 * Real.log 2}
    (∀ p ∈ U, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U, teichDistanceGamma p q < δ →
        cuspNorm lowerHalf (bersMapGamma Γ q - bersMapGamma Γ p) < ENNReal.ofReal ε) ∧
      (∀ p ∈ U, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U,
        cuspNorm lowerHalf (bersMapGamma Γ q - bersMapGamma Γ p) < ENNReal.ofReal δ → teichDistanceGamma p q < ε) ∧
      (∀ p ∈ U, ∃ δ > 0, ∀ φ ∈ boundedCuspForms Γ lowerHalf, (∀ z ∉ lowerHalf, φ z = 0) →
        cuspNorm lowerHalf (φ - bersMapGamma Γ p) < ENNReal.ofReal δ → ∃ q ∈ U, bersMapGamma Γ q = φ) ∧
      (∀ p ∈ U, cuspNorm lowerHalf (bersMapGamma Γ p) < 2) ∧
      ∀ φ ∈ boundedCuspForms Γ lowerHalf, (∀ z ∉ lowerHalf, φ z = 0) → cuspNorm lowerHalf φ < 2 / 3 →
        ∃ q ∈ U, bersMapGamma Γ q = φ := by
  sorry

/-- **Definition** (complex Banach manifold, §6.4, l. 5787). `T(G)` has an atlas modelled on `B(G)`: every point
lies in the domain `U` of a chart `ψ`, a homeomorphism (for the Teichmüller metric and the cusp norm) of the open set
`U` onto an open subset of `B(G)`, and the transition maps between charts are holomorphic (`IsHolBMap`). Modelling:
a predicate on a family of charts (no instance). -/
def IsBanachAtlasT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) {ι : Type}
    (U : ι → Set (TeichGamma Γ)) (ψ : ι → TeichGamma Γ → ℂ → ℂ) : Prop :=
  (∀ p, ∃ i, p ∈ U i) ∧
    (∀ i, ∀ p ∈ U i, ∃ δ > 0, ∀ q, teichDistanceGamma p q < δ → q ∈ U i) ∧
    (∀ i, ∀ p ∈ U i, ψ i p ∈ boundedCuspForms Γ lowerHalf) ∧
    (∀ i, InjOn (ψ i) (U i)) ∧
    (∀ i, ∀ p ∈ U i, ∃ δ > 0, ∀ φ ∈ boundedCuspForms Γ lowerHalf, (∀ z ∉ lowerHalf, φ z = 0) →
      cuspNorm lowerHalf (φ - ψ i p) < ENNReal.ofReal δ → φ ∈ ψ i '' U i) ∧
    (∀ i, ∀ p ∈ U i, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U i, teichDistanceGamma p q < δ →
      cuspNorm lowerHalf (ψ i q - ψ i p) < ENNReal.ofReal ε) ∧
    (∀ i, ∀ p ∈ U i, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U i,
      cuspNorm lowerHalf (ψ i q - ψ i p) < ENNReal.ofReal δ → teichDistanceGamma p q < ε) ∧
    ∀ i j, ∃ T : (ℂ → ℂ) → ℂ → ℂ, IsHolBMap (cuspFormsL Γ) (ψ i '' (U i ∩ U j)) T ∧
      ∀ p ∈ U i ∩ U j, T (ψ i p) = ψ j p

/-- **Theorem 3** (§6.4, l. 5787). The Teichmüller space `T(G)` is a complex Banach manifold (modelled on `B(G)`). -/
theorem thm6_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    ∃ (ι : Type) (U : ι → Set (TeichGamma Γ)) (ψ : ι → TeichGamma Γ → ℂ → ℂ), IsBanachAtlasT Γ U ψ := by
  sorry

/-- **Theorem 4** (§6.4, l. 5817). The transition maps between the Ahlfors–Weill charts are holomorphic near the
origin: for `μ₀ ∈ M(ℍ)`, the map `χ : φ_μ ↦ φ_λ`, `w^λ = w^μ ∘ (w^{μ₀})⁻¹` (`LiZhongQC.b33_t_chi`), is holomorphic on
a neighbourhood of `φ_{μ₀}` in the Bers image (see the module docstring for the direction). -/
theorem thm6_4 (μ₀ : BeltramiH) : ∃ δ > 0,
    IsHolBMap (cuspFormsL ⊥) {φ | φ ∈ range (fun μ : BeltramiH => bersFunction μ.1) ∧
        cuspNorm lowerHalf (φ - bersFunction μ₀.1) < ENNReal.ofReal δ} (LiZhongQC.b33_t_chi μ₀) := by
  sorry

end GardinerLakic2000
