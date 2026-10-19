import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch05.S04_QuadraticDifferentials

/-!
# Hubbard 2006, Chapter 6 §6.12: Simultaneous uniformization and quasi-Fuchsian groups (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3576–3760.

**Conventions.** `X = ℍ/Γ` for a torsion-free Fuchsian group `Γ ⊂ SL(2, ℝ)`; `ℳ(X) = LiZhongQC.BeltramiGamma Γ` are the
`Γ`-invariant Beltrami coefficients on `ℍ`. A Beltrami form `μ₂ ∈ ℳ(X*)` on `X* = ℍ*/Γ` is recorded by its reflection to
`ℍ` (`μ₂(z) ↦ conj μ₂(z̄)`), again an element of `BeltramiGamma Γ`; the pair `(μ₁, μ₂)` is the coefficient on
`ℍ ∪ ℍ*` extended by `0` on `ℝ̄` (a null set) — `pairCoeff`. The normalized quasiconformal homeomorphism
`f^{(μ̃₁, μ̃₂)} : ℙ¹ → ℙ¹` fixing `0`, `1`, `∞` is `LiZhongQC.normalizedSolution (pairCoeff μ₁ μ₂)` (Notation 4.7.5).
The quasi-Fuchsian representation is `γ ↦ f ∘ γ ∘ f⁻¹`, recorded by the relation `IsQFConj` (a matrix
`g ∈ SL(2, ℂ)` with
`f ∘ γ = g ∘ f` on `ℙ¹`); the Möbius map `g` is unique, so this is the representation of Definition 6.12.2.

* Notation 6.12.1 (`Rep(Γ)`, `R̄ep(Γ)`) — omitted: notation
* Def. 6.12.2 and Notation 6.12.3 (the quasi-Fuchsian representation `QF(μ₁, μ₂) = μ₁ ⫫ μ₂`) — `pairCoeff`, `qfSol`,
  `IsQFConj`
* Prop. 6.12.2 (the conjugate `f ∘ γ ∘ f⁻¹` of an element of `Γ` is a Möbius transformation) — `prop6_12_2`
* Prop. 6.12.4 (1) (the representation depends only on the points `τ₁ ∈ 𝒯_X`, `τ₂ ∈ 𝒯_{X*}`, i.e. on the classes of
  `μ₁`,
  `μ₂`) — `prop6_12_4_a`
* Prop. 6.12.4 (2) (`QF` is an analytic isomorphism onto an open subset of a submanifold of representations),
  Thm 6.12.5 (quasi-Fuchsian reciprocity, `⟨DΨ_X(ν), μ⟩ = ⟨DΨ_Y(μ), ν⟩`) — deferred: need the Banach-analytic structure
  of `𝒯_X × 𝒯_{X*}` and the derivative of the Bers embedding
-/

open Set MeasureTheory
open scoped ComplexConjugate

namespace Hubbard2006

open LiZhongQC

/-- **The pair of Beltrami coefficients on `ℍ ∪ ℍ*`** (equation (6.12.1)): `μ₁` on `ℍ`, the reflection
`z ↦ conj μ₂(z̄)` of the coefficient `μ₂` (given on `ℍ`) on `ℍ*`, and `0` on `ℝ`. -/
noncomputable def pairCoeff (μ₁ μ₂ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then μ₁ z else if z.im < 0 then conj (μ₂ (conj z)) else 0

/-- **The normalized solution** `f^{(μ̃₁, μ̃₂)}` of the Beltrami equation with the coefficient `pairCoeff μ₁ μ₂`, fixing
`0`, `1`, `∞`. -/
noncomputable def qfSol {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ₁ μ₂ : BeltramiGamma Γ) : ℂ → ℂ :=
  normalizedSolution (pairCoeff μ₁.1.1 μ₂.1.1)

/-- **`g` is the quasi-Fuchsian image of `γ`** (equation (6.12.2)): `f ∘ γ = g ∘ f` on `ℙ¹`, for
`f = f^{(μ̃₁, μ̃₂)}`. -/
def IsQFConj {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ₁ μ₂ : BeltramiGamma Γ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Prop :=
  ∀ p : ExtPlane, OnePoint.map (qfSol μ₁ μ₂) (mobiusSL (slRealToComplex γ) p) =
    mobiusSL g (OnePoint.map (qfSol μ₁ μ₂) p)

/-- **Definition 6.12.2** (quasi-Fuchsian representation, H2:3598). For every `γ ∈ Γ` the conjugate
`f^{(μ̃₁, μ̃₂)} ∘ γ ∘ (f^{(μ̃₁, μ̃₂)})⁻¹` is a Möbius transformation: there is `g ∈ SL(2, ℂ)` with `f ∘ γ = g ∘ f`. -/
theorem prop6_12_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (μ₁ μ₂ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, IsQFConj μ₁ μ₂ γ g := by
  sorry

/-- **Proposition 6.12.4 (1)** (Simultaneous uniformization, H2:3618). If `μ₁`, `μ₁'` define the same point of `𝒯_X` and
`μ₂`, `μ₂'` the same point of `𝒯_{X*}` (equivalent for `LiZhongQC.teichSetoidGamma`), the quasi-Fuchsian
representations coincide: if `g`, `g'` are the images of `γ ∈ Γ` for `(μ₁, μ₂)`, `(μ₁', μ₂')`, then `g` and `g'`
define the same Möbius transformation, so `QF : 𝒯_X × 𝒯_{X*} → Hom(Γ, PSL₂ℂ)` is well defined. -/
theorem prop6_12_4_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {μ₁ μ₁' μ₂ μ₂' : BeltramiGamma Γ} (h₁ : (teichSetoidGamma Γ).r μ₁ μ₁') (h₂ : (teichSetoidGamma Γ).r μ₂ μ₂')
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {g g' : Matrix.SpecialLinearGroup (Fin 2) ℂ}
    (hg : IsQFConj μ₁ μ₂ γ g) (hg' : IsQFConj μ₁' μ₂' γ g') : mobiusSL g = mobiusSL g' := by
  sorry

end Hubbard2006
