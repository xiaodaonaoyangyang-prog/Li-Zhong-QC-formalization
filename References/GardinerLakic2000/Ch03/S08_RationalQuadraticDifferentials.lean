import References.GardinerLakic2000.Ch03.S07_RationalApproximation

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.8 Rational quadratic differentials

Source `teichmuller.txt`, lines 2969–3036 (Chapter 3, §3.8).

* Definition (`Rat(S, Γ)`, the rational quadratic differentials of `A(R)`, l. 2970–2979) — `ratSpaceGamma`
* Theorem 10 (l. 2981) — `thm3_10`

Not items: (3.37)–(3.39), steps of the proof. Modelling: the section is in the ℍ model already (`R = ℍ/Γ`, `Γ` a
Fuchsian group, `Λ` its limit set, `ω` a fundamental domain; here `F`, measurable). `S ⊆ ℝ` is `Γ`-invariant and
contains `Λ ∩ ℝ` (and `∞` when it is a limit point: the book's `S` lies in the real axis). Condition 4 ("the orbit
space of poles is finite") reads: every pole in `S ∖ Λ` is in the `Γ`-orbit of one of finitely many real points.
`A(R)` is `LiZhongQC.integrableAutomorphicQD Γ F`, whose elements are identified with their restrictions to `ℍ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane phiArea fuchsianLimitSet integrableAutomorphicQD IsFuchsian ActsFreely
  IsFundamentalDomainH upperHalf h36p_m)

/-- **Definition** (§3.8, l. 2970–2979). `Rat(S, Γ)`: meromorphic `φ` (1) with at most simple poles at the points of
`S ∖ Λ`, (2) `Γ`-invariant, `φ(γz) γ′(z)² = φ(z)`, (3) integrable over the fundamental domain `F` and holomorphic on
`ℂ ∖ S`, (4) with finitely many `Γ`-orbits of poles. -/
def ratSpaceGamma (S : Set ℝ) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) : Set (ℂ → ℂ) :=
  {φ | (∀ s ∈ S, (((s : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] (s : ℂ), φ z = g z / (z - s)) ∧
    (∀ γ ∈ Γ, ∀ z : ℂ, (∀ s ∈ S, z ≠ s) → (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 →
      φ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) ∧
    phiArea φ F < ⊤ ∧ DifferentiableOn ℂ φ {z : ℂ | ∀ s ∈ S, z ≠ s} ∧
    ∃ T : Finset ℝ, ∀ s ∈ S, (((s : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ →
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] (s : ℂ), φ z = g z) ∨
        ∃ γ ∈ Γ, ∃ t ∈ T, h36p_m γ t = s}

/-- **Theorem 10** (§3.8, l. 2981). If `S` is dense in `ℝ` (and `Γ`-invariant, containing the limit set), then
`Rat(S, Γ)` is dense in `A(R)`. -/
theorem thm3_10 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {S : Set ℝ} (hS : Dense S)
    (hinv : ∀ γ ∈ Γ, ∀ s ∈ S, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → (γ 0 0 * s + γ 0 1) / (γ 1 0 * s + γ 1 1) ∈ S)
    (hΛ : ∀ x : ℝ, (((x : ℂ)) : ExtPlane) ∈ fuchsianLimitSet Γ → x ∈ S) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ψ ∈ ratSpaceGamma S Γ F, phiArea (φ - ψ) F < ε := by
  sorry

end GardinerLakic2000
