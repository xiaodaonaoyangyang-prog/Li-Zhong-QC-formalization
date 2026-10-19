import References.GardinerLakic2000.Ch14.S05_BersLOperators

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.7 Manifold structure

Source `teichmuller.txt`, lines 10553–10736.

* Definition (`b*(ν, G)`, l. 10577; `B(Ω*, G)`, `B₀(Ω*, G)`, l. 10582–10587) — exists:
  `GardinerLakic2000.bStarOmega` `GardinerLakic2000.boundedCuspFormsC` `GardinerLakic2000.boundedCuspForms0`
* Lemma 6 ([EGL98b], l. 10594) — `lemma14_6`
* Definition (the Bers embedding, steps 1–5, l. 10627–10641) — exists: `LiZhongQC.bersMapGamma`
* Definition (`T₀(ℍ, Γ)`; the relation of `AT(ℍ, Γ)`, l. 10642, 10658) — `IsInT0Gamma`, `IsAsymEquivGamma`
* Theorem 5 ([EGL98b], l. 10642) — `thm14_5_a`, `thm14_5_b`
* Definition (complex Banach manifold structure on T₀ modelled on B₀, l. 10650) — `IsBanachAtlasT0`
* Theorem 6 ([EGL98b], l. 10650) — `thm14_6_a` (T₀), `thm14_6_b` (AT)
* Corollary 2 (T₀ is path connected, l. 10731) — `cor14_6_2`
* Corollary 3 (every point of T₀ has a vanishing representative, l. 10734) — `cor14_6_3`

Not items (DESIGN §3): (14.27) (l. 10685) and the construction of `ã`, `r` (l. 10660–10672), steps of the proof.

**Modelling (calibration D0.8, D0.9).** The Fuchsian model is the project's `LiZhongQC.TeichGamma` with the Bers map
`LiZhongQC.bersMapGamma` (on `ℍ* = 𝕃`) and the Teichmüller metric `LiZhongQC.teichDistanceGamma`. `B₀(ℍ*, Γ)` is
`boundedCuspForms0` of B's `cuspFormsL`. `[μ] ∈ T₀` iff the infimum of `b*(μ′, Γ)` over the representatives `μ′` is `0`
(the book's "for every `ε` a representative with dilatation `< 1 + ε` off a compact set", l. 10644). Two points `[μ]`,
`[ν]` are equal in `AT` iff the class of `a = f_ν ∘ f_μ⁻¹` is asymptotically conformal on `f_μ(ℍ)`, for the conjugate
group `f_μ Γ f_μ⁻¹` (l. 10658), with `f_μ = LiZhongQC.fMuSym μ`. The manifold structure of `T₀` is a predicate on an
atlas, as B's `IsBanachAtlasT`, restricted to `T₀` with values in `B₀`. For `AT` (D0.9) the two assertions of the proof
are stated: the Bers map is well defined modulo `B₀` on `AT`-classes, and it is locally injective modulo `B₀`; the
holomorphy of the induced transition maps of `B/B₀` is not stated separately [reading]. The image of `T₀` is contained
in the closed ball of radius `6` ("the ball of radius 6", Nehari). Paths in `T₀` are continuous for the Teichmüller
metric. Theorem 5 prints `T₀(ℍ*, Γ)` for `T₀(ℍ, Γ)` [misprint; GL1:3322 prints the same].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane IsQuasiFuchsian IsFuchsian TeichGamma BeltramiGamma teichSetoidGamma bersMapGamma
  teichDistanceGamma fMuSym schwarzian normalizedSolution complexDilatation upperHalf lowerHalf)

/-- **Definition** (`T₀(ℍ, Γ)`, §14.7, l. 10642–10644). `P` is asymptotically conformal: the infimum of `b*(μ, Γ)` over
the representatives `μ` of `P` is `0`. -/
def IsInT0Gamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (P : TeichGamma Γ) : Prop :=
  ⨅ (μ : BeltramiGamma Γ) (_ : Quotient.mk (teichSetoidGamma Γ) μ = P), bStarOmega (orbitMapsR Γ) upperHalf μ.1.1 = 0

/-- **Definition** (§14.7, l. 10658). `P = [μ]` and `Q = [ν]` represent the same point of `AT(ℍ, Γ)`: the Beltrami
coefficients of `a = f_ν ∘ f_μ⁻¹` (over the representatives) have infimal `b*` equal to `0` for the group
`f_μ Γ f_μ⁻¹` on `ℍ`. -/
def IsAsymEquivGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (P Q : TeichGamma Γ) : Prop :=
  ⨅ (μ : BeltramiGamma Γ) (ν : BeltramiGamma Γ)
    (_ : Quotient.mk (teichSetoidGamma Γ) μ = P ∧ Quotient.mk (teichSetoidGamma Γ) ν = Q),
    bStarOmega {g' | ∃ g ∈ orbitMapsR Γ, g' = fMuSym μ.1.1 ∘ g ∘ Function.invFun (fMuSym μ.1.1)} upperHalf
      (complexDilatation (fMuSym ν.1.1 ∘ Function.invFun (fMuSym μ.1.1))) = 0

/-- **Lemma 6** (§14.7, l. 10594; [EGL98b]). If the Beltrami coefficient `ν` of `f` (conformal on `Ω*`) satisfies
`b*(ν) = 0`, then `{f, z} ∈ B₀(Ω*, G)`. -/
theorem lemma14_6 {C : Set ExtPlane} {Ω Ωs : Set ℂ} {G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hc : IsQCConfiguration C Ω Ωs) (hG : IsQuasiFuchsian G C) {ν : ℂ → ℂ} (hν : ν ∈ beltramiSpaceOmega G Ω)
    (hν1 : eLpNorm ν ⊤ (volume.restrict Ω) < 1) (hν0 : bStarOmega (orbitMapsC G) Ω ν = 0) :
    schwarzian (normalizedSolution (Ω.indicator ν)) ∈
      boundedCuspForms0 (orbitMapsC G) Ωs (boundedCuspFormsC G Ωs) := by
  sorry

/-- **Theorem 5** (§14.7, l. 10642; [EGL98b]), first part. If `h` represents an element of `T₀(ℍ, Γ)`, then its Bers
image lies in `B₀(ℍ*, Γ)`. -/
theorem thm14_5_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {P : TeichGamma Γ}
    (hP : IsInT0Gamma Γ P) : bersMapGamma Γ P ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ) := by
  sorry

/-- **Theorem 5** (§14.7, l. 10642; [EGL98b]), second part. The Bers image of `T₀` contains the ball of radius `2` of
`B₀(ℍ*, Γ)` and is contained in the ball of radius `6`. -/
theorem thm14_5_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    (∀ φ ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ), cuspNorm lowerHalf φ < 2 →
      ∃ P : TeichGamma Γ, IsInT0Gamma Γ P ∧ bersMapGamma Γ P = φ) ∧
    ∀ P : TeichGamma Γ, IsInT0Gamma Γ P → cuspNorm lowerHalf (bersMapGamma Γ P) ≤ 6 := by
  sorry

/-- **Definition** (§14.7, l. 10650; D0.9). An atlas of `T₀(ℍ, Γ)` modelled on `B₀(ℍ*, Γ)`: `B`'s `IsBanachAtlasT`
with the chart domains relatively open subsets of `T₀` covering `T₀`, values and directions in `B₀`. -/
def IsBanachAtlasT0 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) {ι : Type}
    (U : ι → Set (TeichGamma Γ)) (ψ : ι → TeichGamma Γ → ℂ → ℂ) : Prop :=
  (∀ p, IsInT0Gamma Γ p → ∃ i, p ∈ U i) ∧ (∀ i, ∀ p ∈ U i, IsInT0Gamma Γ p) ∧
    (∀ i, ∀ p ∈ U i, ∃ δ > 0, ∀ q, IsInT0Gamma Γ q → teichDistanceGamma p q < δ → q ∈ U i) ∧
    (∀ i, ∀ p ∈ U i, ψ i p ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ)) ∧
    (∀ i, InjOn (ψ i) (U i)) ∧
    (∀ i, ∀ p ∈ U i, ∃ δ > 0, ∀ φ ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ),
      cuspNorm lowerHalf (φ - ψ i p) < ENNReal.ofReal δ → φ ∈ ψ i '' U i) ∧
    (∀ i, ∀ p ∈ U i, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U i, teichDistanceGamma p q < δ →
      cuspNorm lowerHalf (ψ i q - ψ i p) < ENNReal.ofReal ε) ∧
    (∀ i, ∀ p ∈ U i, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ U i,
      cuspNorm lowerHalf (ψ i q - ψ i p) < ENNReal.ofReal δ → teichDistanceGamma p q < ε) ∧
    ∀ i j, ∃ T : (ℂ → ℂ) → ℂ → ℂ,
      IsHolBMap (boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ)) (ψ i '' (U i ∩ U j)) T ∧
        ∀ p ∈ U i ∩ U j, T (ψ i p) = ψ j p

/-- **Theorem 6** (§14.7, l. 10650; [EGL98b]), for `T₀`. The Ahlfors–Weill charts make `T₀` a complex manifold
modelled on `B₀`. -/
theorem thm14_6_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    ∃ (ι : Type) (U : ι → Set (TeichGamma Γ)) (ψ : ι → TeichGamma Γ → ℂ → ℂ), IsBanachAtlasT0 Γ U ψ := by
  sorry

/-- **Theorem 6** (§14.7, l. 10650–10729; [EGL98b]), for `AT` (D0.9). The Bers map is well defined on `AT` modulo
`B₀`, and it is locally injective modulo `B₀`: near every point, a difference in `B₀` of small norm forces the same
point of `AT`. -/
theorem thm14_6_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    (∀ P Q : TeichGamma Γ, IsAsymEquivGamma Γ P Q →
      bersMapGamma Γ P - bersMapGamma Γ Q ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ)) ∧
    ∀ P : TeichGamma Γ, ∃ δ > 0, ∀ Q : TeichGamma Γ,
      bersMapGamma Γ Q - bersMapGamma Γ P ∈ boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ) →
      cuspNorm lowerHalf (bersMapGamma Γ Q - bersMapGamma Γ P) < ENNReal.ofReal δ → IsAsymEquivGamma Γ P Q := by
  sorry

/-- **Corollary 2** (§14.7, l. 10731). `T₀` is path connected (for the Teichmüller metric). -/
theorem cor14_6_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {P Q : TeichGamma Γ}
    (hP : IsInT0Gamma Γ P) (hQ : IsInT0Gamma Γ Q) :
    ∃ c : ℝ → TeichGamma Γ, c 0 = P ∧ c 1 = Q ∧ (∀ t ∈ Icc (0 : ℝ) 1, IsInT0Gamma Γ (c t)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < δ →
        teichDistanceGamma (c t) (c s) < ε := by
  sorry

/-- **Corollary 3** (§14.7, l. 10734). Every `τ ∈ T₀` has a vanishing representative. -/
theorem cor14_6_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {P : TeichGamma Γ}
    (hP : IsInT0Gamma Γ P) :
    ∃ μ : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) μ = P ∧
      bStarOmega (orbitMapsR Γ) upperHalf μ.1.1 = 0 := by
  sorry

end GardinerLakic2000
