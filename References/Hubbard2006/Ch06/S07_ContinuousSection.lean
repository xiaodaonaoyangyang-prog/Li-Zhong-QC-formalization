import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch05.S01_DouadyEarleExtension

/-!
# Hubbard 2006, Chapter 6 §6.7–6.8: Contractibility, rigidity of hyperbolic surfaces (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 2977–3330.

**Conventions.** Teichmüller space is read in the Fuchsian model of the project: for a Fuchsian group `Γ ⊂ SL(2, ℝ)`,
`LiZhongQC.BeltramiGamma Γ` is the space `ℳ(X)` of `Γ`-invariant Beltrami coefficients on `ℍ` (norm `‖·‖_∞ < 1`),
`LiZhongQC.TeichGamma Γ` is `𝒯_X = ℳ(X)/∼` (Hubbard's `Φ_S` is the quotient map), with the distance
`LiZhongQC.teichDistanceGamma = ½ · (Hubbard's d)` (D18). Continuity in `ℳ(X)` is for the `L^∞` norm and in
`𝒯_X` for `teichDistanceGamma`. The ideal boundary `I(X)` is not modelled: Proposition 6.8.1 is stated for a
non-elementary group, where it holds without reference to the ideal boundary (the book's own proof treats the
non-elementary case first).

* Thm 6.7.1 (`Φ_S` has a continuous section `F : 𝒯_S → ℳ`, `Φ_S ∘ F = id`) — `thm6_7_1`
* Cor. 6.7.2 (Teichmüller space is contractible) — deferred: `LiZhongQC.TeichGamma` carries no bundled topology
  (only the pseudo-distance `teichDistanceGamma`); for finite type see the installed `LiZhongQC` ball models
* Prop. 6.8.1 (an analytic self-map of a hyperbolic surface homotopic to the identity is the identity) — `prop6_8_1`
* Cor. 6.8.2 (`QC⁰(S)` is contractible), Prop. 6.8.3–6.8.7 and Defs 6.8.x (the universal curve `Ξ_S` and its universal
  property) — deferred: need Banach-analytic manifolds and the ideal boundary `I(S)`
-/

open Set MeasureTheory
open scoped Manifold ContDiff

namespace Hubbard2006

open LiZhongQC

/-- **Theorem 6.7.1 (`Φ_S` has a continuous section)** (H2:2985). For a torsion-free Fuchsian group `Γ` there is a map
`F : 𝒯_X → ℳ(X)`, continuous (for `teichDistanceGamma` on `𝒯_X` and the `L^∞` norm on `ℳ(X)`), with `Φ_X ∘ F = id`,
i.e. `[F(τ)] = τ`. -/
theorem thm6_7_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    ∃ F : TeichGamma Γ → BeltramiGamma Γ, (∀ τ, Quotient.mk (teichSetoidGamma Γ) (F τ) = τ) ∧
      ∀ τ : TeichGamma Γ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ : TeichGamma Γ, teichDistanceGamma τ σ < δ →
        eLpNorm (fun z => (F τ).1.1 z - (F σ).1.1 z) ⊤ (volume.restrict upperHalf) < ENNReal.ofReal ε := by
  sorry

/-- **Proposition 6.8.1 (Automorphisms homotopic to the identity are the identity)** (H2:3015). Let `X = ℍ/Γ` be a
hyperbolic Riemann surface with non-elementary uniformizing group `Γ` (limit set of at least three points), and
`α : X → X` analytic
and homotopic to the identity. Then `α` is the identity. -/
theorem prop6_8_1 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hne : References.IsNonElementary Γ)
    (α : C(X, X)) (hα : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) α) (hh : ContinuousMap.Homotopic α (ContinuousMap.id X)) :
    ⇑α = id := by
  sorry

end Hubbard2006
