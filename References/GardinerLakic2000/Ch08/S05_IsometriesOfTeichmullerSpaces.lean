import References.GardinerLakic2000.Ch08.S04_AdjointnessTheorem

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.5 Isometries of Teichmüller spaces

Source `teichmuller.txt`, lines 6762–6784 (Chapter 8, §8.5).

* Definition (a surface of finite genus: an open subset of a compact Riemann surface, l. 6763, 6786) —
  `EmbedsInClosedRS`
* Theorem 9 (the classification theorem, l. 6763) — `thm8_9`
* Theorem 10 (the isomorphism theorem, l. 6769) — `thm8_10`

Not items: the remark on local isometries (l. 6767). Modelling: `T(R)`, `T(S)` in the Fuchsian model of their
uniformizations (C0.1); "biholomorphic" is `IsHolAutT` (C0.2); "`R` has finite genus" is read as "`R` is (conformally)
an open subset of a compact Riemann surface" (the hypothesis of Theorem 11, l. 6786) [reading]. The book proves
Theorem 10 only up to `α = 1`, which Corollary 11.3 (`cor11_5_3_b`) and Theorem 8.6 complete (l. 6781–6783, 8783).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS TeichGamma IsFuchsian ActsFreely IsUniformization)

/-- **Definition** (finite genus, §8.5–§8.6, l. 6763, 6786). `R` is conformally an open subset of a compact Riemann
surface: there is a holomorphic open embedding of `R` into a closed Riemann surface. -/
def EmbedsInClosedRS (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Prop :=
  ∃ (X : LiZhongQC.ClosedRS.{u}) (ι : R → X.carrier), Topology.IsOpenEmbedding ι ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι

/-- **Theorem 9** (the classification theorem, §8.5, l. 6763). If `F : T(R) → T(S)` is biholomorphic, `R` has finite
genus and is not of exceptional type, then there is a quasiconformal map from `R` onto `S`. -/
theorem thm8_9 {R S : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hR : EmbedsInClosedRS R) (hex : ¬ IsExceptionalGL R)
    {ΓR ΓS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓR : IsFuchsian ΓR) (hΓS : IsFuchsian ΓS)
    (hfR : ActsFreely ΓR) (hfS : ActsFreely ΓS) {pR : UpperHalfPlane → R} {pS : UpperHalfPlane → S}
    (hpR : IsUniformization ΓR pR) (hpS : IsUniformization ΓS pS) {F : TeichGamma ΓR → TeichGamma ΓS}
    (hF : IsHolAutT ΓR ΓS F) : ∃ f : R ≃ₜ S, IsQCRS f := by
  sorry

/-- **Theorem 10** (the isomorphism theorem, §8.5, l. 6769). Under the hypotheses of Theorem 9 the biholomorphic map
`F` is geometric: `F = ρ_h` for a quasiconformal map `h` conjugating the covering groups. -/
theorem thm8_10 {R S : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (hR : EmbedsInClosedRS R) (hex : ¬ IsExceptionalGL R)
    {ΓR ΓS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓR : IsFuchsian ΓR) (hΓS : IsFuchsian ΓS)
    (hfR : ActsFreely ΓR) (hfS : ActsFreely ΓS) {pR : UpperHalfPlane → R} {pS : UpperHalfPlane → S}
    (hpR : IsUniformization ΓR pR) (hpS : IsUniformization ΓS pS) {F : TeichGamma ΓR → TeichGamma ΓS}
    (hF : IsHolAutT ΓR ΓS F) : ∃ h : ℂ → ℂ, IsQCConj ΓR ΓS h ∧ IsRhoGamma ΓR ΓS h F := by
  sorry

end GardinerLakic2000
