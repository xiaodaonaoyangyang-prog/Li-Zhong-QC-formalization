import References.Common.RiemannSurface
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations

/-!
# Hubbard 2006, Chapter 1 §1.3: Radó's theorem

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 471–557.

**Conventions.** Riemann surfaces as in `S01_TwoStatements`: Hausdorff and connected, **without** second countability
(`References.IsRiemannSurface` of Forster 1981 has no countability condition), so Radó's theorem is a genuine
statement here. The Farkas–Kra lane points its Radó corollary (IV.3.18 Cor 3) at `thm1_3_3`.

* Example 1.3.1 — omitted: example (a non-second-countable surface; motivation only, never cited)
* Proposition 1.3.2 (1) (the universal covering second countable ⇒ `X` second countable) — `prop1_3_2_a`
* Proposition 1.3.2 (2) (a connected Riemann surface with a nonconstant holomorphic function `X → ℂ` is second
  countable) — `prop1_3_2_b`
* Theorem 1.3.3 (Radó) — `thm1_3_3`
* Example 1.3.4 — omitted: example (a two-dimensional complex manifold that is not second countable)
-/

open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Proposition 1.3.2 (1)** (Ch. 1 §1.3, H1:508). If the universal covering space of a Riemann surface `X` is second
countable, then so is `X`. Modelling: "universal covering" is `Forster1981.IsUniversalCovering p` (a covering map from a
connected space with the universal property), `p : Y → X` for some topological space `Y`. -/
theorem prop1_3_2_a {X Y : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] {p : Y → X} (hp : Forster1981.IsUniversalCovering p)
    [SecondCountableTopology Y] : SecondCountableTopology X := by
  sorry

/-- **Proposition 1.3.2 (2)** (Ch. 1 §1.3, H1:508). A connected Riemann surface `X` carrying a nonconstant holomorphic
function `f : X → ℂ` is second countable. -/
theorem prop1_3_2_b {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (f : X → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c : ℂ, f = fun _ => c) :
    SecondCountableTopology X := by
  sorry

/-- **Theorem 1.3.3** (Radó, Ch. 1 §1.3, H1:524). Every connected Riemann surface is second countable. -/
theorem thm1_3_3 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : SecondCountableTopology X := by
  sorry

end Hubbard2006
