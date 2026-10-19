import References.FarkasKra1992.Ch04.S06_ExceptionalSurfaces
import LiZhongQC.Ch08.S28_Moduli

/-!
# Farkas–Kra, Chapter IV §7: Two problems on moduli

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §7 (`full.md` FK2:1227–1290).

Conventions: as in `Ch04/S06_ExceptionalSurfaces`. An annulus is one of the surfaces `Δ_r = annulusOpens r`,
`0 < r < 1`; the multiplier `λ > 1` of the generator `z ↦ λz` of its covering group on `U` is related to `r` by
`r = exp(-2π²/log λ)` (IV(6.8.1)). A torus is a surface `X` with `LiZhongQC.IsTorusWithPeriod τ p`.

* IV.7.1 (lifts to the universal coverings) — `para4_7_1`
* Theorem IV.7.2 — `annulusOfMultiplier`, `thm4_7_2`
* IV.7.3 (conformally equivalent tori: the modular criterion) — exists: `LiZhongQC.torus_conformal_iff`
* Theorem IV.7.3 — `thm4_7_3`
-/

open scoped Manifold ContDiff MatrixGroups Topology References Real
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsBiholomorphic RSConformallyEquivalent)

/-- **The annulus with multiplier `λ`** (Ch. IV §7.2, helper). `U/⟨z ↦ λz⟩` for `λ > 1`, modelled as the plane annulus
`Δ_r` with `r = exp(-2π²/log λ)` (the covering `U → Δ_r`, `z ↦ exp(2πi log z/log λ)`, IV(6.8.1)). -/
def annulusOfMultiplier (l : ℝ) : TopologicalSpace.Opens ℂ := annulusOpens (Real.exp (-2 * π ^ 2 / Real.log l))

/-- **Unlabelled** (Ch. IV §7.1, FK2:1231–1249). Let `M_j` be a Riemann surface with `π_j : M̃_j → M_j` a holomorphic
universal covering map (`j = 1, 2`). If `f : M₁ → M₂` is continuous, there is a continuous `f̃ : M̃₁ → M̃₂` with
`π₂ ∘ f̃ = f ∘ π₁`; if `f` is holomorphic (resp. conformal) the lift `f̃` can be chosen holomorphic (resp. conformal). -/
theorem para4_7_1 {M₁ M₂ M₁t M₂t : Type} [TopologicalSpace M₁] [ChartedSpace ℂ M₁] [TopologicalSpace M₂]
    [ChartedSpace ℂ M₂] [TopologicalSpace M₁t] [ChartedSpace ℂ M₁t] [TopologicalSpace M₂t] [ChartedSpace ℂ M₂t]
    {π₁ : M₁t → M₁} {π₂ : M₂t → M₂} (h₁ : Forster1981.IsUniversalCovering π₁) (h₂ : Forster1981.IsUniversalCovering π₂)
    (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (hπ₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₂) (f : M₁ → M₂) (hf : Continuous f) :
    (∃ ft : M₁t → M₂t, Continuous ft ∧ π₂ ∘ ft = f ∘ π₁) ∧
      (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∃ ft : M₁t → M₂t, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ft ∧ π₂ ∘ ft = f ∘ π₁) ∧
      (IsBiholomorphic f → ∃ ft : M₁t → M₂t, IsBiholomorphic ft ∧ π₂ ∘ ft = f ∘ π₁) := by
  sorry

/-- **Theorem IV.7.2** (Ch. IV §7.2). The set of conformal equivalence classes of annuli is in one-to-one canonical
correspondence with the open real interval `(1, ∞)`: the annuli `U/⟨z ↦ λ₁z⟩` and `U/⟨z ↦ λ₂z⟩` are conformally
equivalent if and only if `λ₁ = λ₂`, and every annulus `Δ_r` (`0 < r < 1`) is one of them (`r = exp(-2π²/log λ)`). -/
theorem thm4_7_2 :
    (∀ l₁ l₂ : ℝ, 1 < l₁ → 1 < l₂ →
      (RSConformallyEquivalent ↥(annulusOfMultiplier l₁) ↥(annulusOfMultiplier l₂) ↔ l₁ = l₂)) ∧
      ∀ r : ℝ, 0 < r → r < 1 → ∃ l : ℝ, 1 < l ∧ annulusOpens r = annulusOfMultiplier l := by
  sorry

/-- **Theorem IV.7.3** (Ch. IV §7.3). The set of equivalence classes of tori is in one-to-one canonical correspondence
with the points in `ℂ`.
Modelling: the criterion for conformal equivalence of two tori `ℂ/⟨1, τ_j⟩` is the modular one
(`LiZhongQC.torus_conformal_iff`: `τ₁ = (γ + δτ₂)/(α + βτ₂)` with `αδ − βγ = ±1`, the `PSL(2, ℤ)` orbit relation on `U`);
the correspondence with `ℂ` ("`U/Γ ≅ ℂ`, with some work") is stated without the `j`-invariant, which Mathlib lacks: there is
a function `J` holomorphic on the upper half plane, onto `ℂ`, whose fibres are exactly the `SL(2, ℤ)`-orbits. Together with
the criterion, `J` is the bijection (classes of tori) `↔ ℂ`. -/
theorem thm4_7_3 :
    ∃ J : ℂ → ℂ, DifferentiableOn ℂ J {τ : ℂ | 0 < τ.im} ∧ (∀ w : ℂ, ∃ τ : UpperHalfPlane, J τ = w) ∧
      ∀ τ τ' : UpperHalfPlane, J τ = J τ' ↔ LiZhongQC.modularGroupOrbitRel.r τ τ' := by
  sorry

end FarkasKra1992
