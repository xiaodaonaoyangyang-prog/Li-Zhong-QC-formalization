import References.GardinerLakic2000.Ch11.S06_Examples

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.7 Differentials with two directions

Source `teichmuller.txt`, lines 8719–8785 (Chapter 11, §11.7).

* Theorem 5 (l. 8720; announced in the introduction, l. 8339) — `thm11_5`
* Corollary 2 (l. 8732) — `cor11_5_2`
* Corollary 3 (l. 8773; with Theorem 8.5 completes the proof that automorphisms of `T(R)` are geometric, l. 8783) —
  `cor11_5_3_a`, `cor11_5_3_b`

Not items: the strips, covering maps and rectangles of the proof of Theorem 5 (l. 8722–8730); the computation of the
parabolic matrix (l. 8735–8771, proof); the remark on the groups `Γ(D_φ)` (l. 8785). Modelling: Theorem 5 is on the
surface level (C0.1): "two Jenkins–Strebel directions with only finitely many annuli" is two unimodular `c₁ ≠ c₂`
with finite ring-domain decompositions `IsJSDecomp (c_i φ) A_i`, "finite analytic type" is batch B's
`IsFiniteAnalyticType` for some `(g, n)` and "infinite analytic type" is its negation. Corollaries 2, 3 are in the
Fuchsian model (C0.1): `R = ℍ/Γ` via `p`, `D_φ` is batch B's `teichmullerDisc` of the lift `liftQD p φ`, `Γ(D_φ)` is
`discStabilizer`, `ρ_f` is a `Φ` with `IsRhoGamma Γ Γ f Φ`; "acts as a parabolic Möbius transformation fixing `s = 1`"
is the action `ActsOnDiscBy` with the matrix `(1 + i a₂, −i a₂; i a₂, 1 − i a₂)` of the proof (`a₂ = 0` is the
identity). "`φ` has one annulus" is a decomposition `IsJSDecomp φ A` indexed by `Unit`. In the second part of
Corollary 3 the hypothesis `A(R) ≠ 0` (a unit `φ ∈ A(R)`) is added as a guard.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm IsFuchsian ActsFreely IsUniformization TeichGamma BeltramiGamma teichSetoidGamma
  upperHalf)

/-- **Theorem 5** (§11.7, l. 8720). If `φ ∈ A(R)`, `‖φ‖ = 1`, has two Jenkins–Strebel directions with only finitely
many annuli for each direction, then `R` has finite analytic type. -/
theorem thm11_5 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hφ1 : quadDiffNorm φ = 1) {c₁ c₂ : ℂ}
    (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : c₁ ≠ c₂) {n₁ n₂ : ℕ} {A₁ : Fin n₁ → Set R} {A₂ : Fin n₂ → Set R}
    (hA₁ : IsJSDecomp (fun x z => c₁ * φ x z) A₁) (hA₂ : IsJSDecomp (fun x z => c₂ * φ x z) A₂) :
    ∃ g n : ℕ, IsFiniteAnalyticType R g n := by
  sorry

/-- **Corollary 2** (§11.7, l. 8732). Let `R` have infinite analytic type and `φ ∈ A(R)` be a Jenkins–Strebel
differential with one annulus. If `f` is a quasiconformal self-map of `R` with `ρ_f(D_φ) = D_φ`, then `ρ_f` acts on
`D_φ` as a parabolic Möbius transformation fixing `s = 1`. -/
theorem cor11_5_2 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hinf : ¬ ∃ g n : ℕ, IsFiniteAnalyticType R g n)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {φ : R → ℂ → ℂ} (hφ1 : quadDiffNorm φ = 1)
    {A : Unit → Set R} (hA : IsJSDecomp φ A) {f : ℂ → ℂ} (hf : f ∈ discStabilizer Γ (liftQD p φ)) :
    ∃ a₂ : ℝ, ∀ Φ : TeichGamma Γ → TeichGamma Γ, IsRhoGamma Γ Γ f Φ →
      ActsOnDiscBy Γ (liftQD p φ) Φ (1 + a₂ * I) (-(a₂ * I)) := by
  sorry

/-- **Corollary 3** (§11.7, l. 8773), first part. With `R`, `φ` as in Corollary 2 and `ρ_f ∈ Γ(D_φ)`: if `0 < t₀ < 1`
and `ρ_f([t₀|φ|/φ]) = [s₀|φ|/φ]`, then `|s₀| > |t₀|` unless `s₀ = t₀`. -/
theorem cor11_5_3_a {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hinf : ¬ ∃ g n : ℕ, IsFiniteAnalyticType R g n)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {φ : R → ℂ → ℂ} (hφ1 : quadDiffNorm φ = 1)
    {A : Unit → Set R} (hA : IsJSDecomp φ A) {f : ℂ → ℂ} (hf : f ∈ discStabilizer Γ (liftQD p φ))
    {Φ : TeichGamma Γ → TeichGamma Γ} (hΦ : IsRhoGamma Γ Γ f Φ) {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₀ < 1) {s₀ : ℂ}
    (hs₀ : ‖s₀‖ < 1) (μ ν : BeltramiGamma Γ)
    (hμ : ∀ z ∈ upperHalf, μ.1.1 z = t₀ * (conj (liftQD p φ z) / ‖liftQD p φ z‖))
    (hν : ∀ z ∈ upperHalf, ν.1.1 z = s₀ * (conj (liftQD p φ z) / ‖liftQD p φ z‖))
    (hΦμ : Φ (Quotient.mk (teichSetoidGamma Γ) μ) = Quotient.mk (teichSetoidGamma Γ) ν) :
    t₀ < ‖s₀‖ ∨ s₀ = t₀ := by
  sorry

/-- **Corollary 3** (§11.7, l. 8773), second part. If `R` has infinite analytic type, there are Teichmüller discs that
are not `α`-rotationally transitive for any `α ≠ 1`. -/
theorem cor11_5_3_b {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hinf : ¬ ∃ g n : ℕ, IsFiniteAnalyticType R g n)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) :
    ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1 ∧
      ∀ α : ℂ, ‖α‖ = 1 → IsRotTransitive Γ (liftQD p φ) α → α = 1 := by
  sorry

end GardinerLakic2000
