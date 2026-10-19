import References.Hubbard2006.Ch03.S06_TrouserDecomposition
import References.ImayoshiTaniguchi1992.Ch03.S02_FenchelNielsen

/-!
# Hubbard 2006, Chapter 3 §3.7: Limit sets and ideal boundaries

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2580–2617.

**Conventions.** A hyperbolic surface is `X = ℍ/Γ` for a torsion-free Fuchsian group `Γ ⊆ SL(2, ℝ)`. The limit set is
`limitSetAt Γ I` (independent of the base point, Prop. 3.4.1), and the ideal boundary of the book, `I(X) = (S¹ ∖
Λ_Γ)/Γ`, is the quotient of `∂ℍ ∖ Λ_Γ` by the action of `Γ` on `ℂ̄` (`idealBoundary`), with the quotient topology. That
`X̄ = (𝔻̄ ∖ Λ_Γ)/Γ` is a manifold with boundary `I(X)` is **deferred** (no manifolds with boundary on quotients in the
project): only the content about the components of `I(X)` is stated.

* Proposition and Definition 3.7.1 (ideal boundary of a Riemann surface) — `idealBoundary`, `prop3_7_1`
* Proposition and Definition 3.7.1 (`X̄ = (𝔻̄ ∖ Λ_Γ)/Γ` is a manifold with boundary `I(X)`) — deferred: manifolds with
  boundary on quotients are not available in the project (the content on the components of `I(X)` is `prop3_7_1`)
* Examples 3.7.2 — omitted: example
* Definition (maximal geodesic multicurve = system of decomposing curves, used in Prop. 3.7.3) — exists:
  `ImayoshiTaniguchi1992.IsDecomposingSystem`
* Proposition 3.7.3 (the complementary components are all trousers iff the ideal boundary is empty) — `prop3_7_3`
-/

open Set
open scoped Manifold ContDiff Topology
open LiZhongQC References

namespace Hubbard2006

/-- **The ideal boundary `I(X) = (S¹ ∖ Λ_Γ)/Γ`** of `X = ℍ/Γ` (Prop. and Def. 3.7.1, H1:2594): the quotient of the ideal
boundary `∂ℍ` minus the limit set `Λ_Γ = limitSetAt Γ I` by the action of `Γ`, with the quotient topology. It is empty
iff `Λ_Γ = ∂ℍ`. -/
abbrev idealBoundary (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quot (fun a b : ↥(idealBoundaryH \ limitSetAt Γ UpperHalfPlane.I) => ∃ γ ∈ Γ, bdryAct γ a = b)

/-- **Proposition 3.7.1** (ideal boundary, Ch. 3 §3.7, H1:2594). Let `X = ℍ/Γ` be a hyperbolic Riemann surface, `Γ` a
torsion-free Fuchsian group. The ideal boundary `I(X)` is a one-dimensional manifold whose components are homeomorphic
to `S¹` or to `ℝ`: every connected component of `I(X)` is homeomorphic to the circle or to the line. (Empty when `Λ_Γ =
∂ℍ`.) The statement that `X̄` is a manifold with boundary `I(X)` is deferred. -/
theorem prop3_7_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (x : idealBoundary Γ) :
    Nonempty (↥(connectedComponent x) ≃ₜ Circle) ∨ Nonempty (↥(connectedComponent x) ≃ₜ ℝ) := by
  sorry

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Proposition 3.7.3** (Ch. 3 §3.7, H1:2612). Let `Y` be a maximal geodesic multicurve on a hyperbolic Riemann
surface `X` whose union `Z` satisfies the conditions of Theorem 3.6.2 (`IsTrouserDecomposition`). Then the closures of
the components of `X ∖ Z̄` are all trousers iff the ideal boundary of `X` is empty. Modelling: maximal among *geodesic*
multicurves (`ImayoshiTaniguchi1992.IsDecomposingSystem`); "trouser" is the lifted pair of the component
(`liftStabModel`, `IsTrouserCore`). -/
theorem prop3_7_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {Y : Set (Set X)}
    (hY : IsTrouserDecomposition Γ p Y) (hmax : ImayoshiTaniguchi1992.IsDecomposingSystem Γ p Y) :
    (∀ x ∈ (closure (⋃₀ Y))ᶜ, ∀ z : UpperHalfPlane, p z ∈ connectedComponentIn (closure (⋃₀ Y))ᶜ x →
      ∃ S' : HypSurfBdry, liftStabModel Γ p (connectedComponentIn (closure (⋃₀ Y))ᶜ x) z S' ∧ IsTrouserCore S') ↔
      IsEmpty (idealBoundary Γ) := by
  sorry

end Hubbard2006
