import References.Common.RiemannSurface
import References.Common.RiemannSurfaceHarmonic

/-!
# Hubbard 2006, Chapter 1 §1.2: Subharmonic and harmonic functions

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 390–476.

**Conventions.** Riemann surfaces as in `S01_TwoStatements`. The harmonic, subharmonic and superharmonic functions and
the
Perron families of Definitions 1.2.1–1.2.2 are the shared notions of `References/Common/RiemannSurfaceHarmonic.lean`
(`References.IsHarmonicRS`, `IsSubharmonicRS`, `IsSuperharmonicRS`, `IsPerronFamily`); Hubbard's *bounded* Perron family
(Def. 1.2.2) is `IsPerronFamily 𝓕` together with a bound `M` on all members, and a Perron family in his sense is one
here (his closure under `sup` and under harmonic replacement imply Farkas–Kra's conditions (2.6.2)–(2.6.3)), so
`prop1_2_3` below is stated for the weaker, larger class. A **smooth subsurface** `K` of a Riemann surface `Y`
(Prop. 1.2.4) and a **compact `C^∞` piece** (§1.4) are modelled by a local defining function: `K` is closed and every
frontier point has an open neighbourhood `U` and a function `ρ`, smooth in every chart of the maximal analytic atlas
and without critical points on `U`, with `K ∩ U = {ρ ≤ 0} ∩ U` (so the boundary is a smooth curve and `K` lies on one
side of it).

* Definition 1.2.1 (harmonic, subharmonic, superharmonic) — exists: `References.IsHarmonicRS`,
  `References.IsSubharmonicRS`, `References.IsSuperharmonicRS`
* Definition 1.2.2 (bounded Perron family) — exists: `References.IsPerronFamily` (with a bound on the members, in
  Prop. 1.2.3)
* Definition (smooth subsurface, Prop. 1.2.4; compact `C^∞` piece, §1.4) — `IsSmoothSubsurface`,
  `IsCompactSmoothPiece`
* Proposition 1.2.3 (Perron) — `prop1_2_3`
* Proposition 1.2.4 (existence of harmonic functions) — `prop1_2_4`
* Example 1.2.5 — omitted: example (a counterexample showing that smoothness of the boundary is needed; not cited)
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Smooth subsurface** of a Riemann surface `Y` (Prop. 1.2.4, "subsurface with smooth boundary"): `K ⊆ Y` is closed
and
every frontier point `x` has an open neighbourhood `U` and a function `ρ : Y → ℝ` that is `C^∞` in every chart `e` of
the maximal analytic atlas (`ρ ∘ e⁻¹` on `e.target`), has non-vanishing real derivative on `U` in every chart, and
satisfies `K ∩ U = {ρ ≤ 0} ∩ U`. A set with empty frontier (a union of components) is admitted; Prop. 1.2.4 asks for a
non-empty frontier separately. -/
def IsSmoothSubsurface {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] (K : Set Y) : Prop :=
  IsClosed K ∧ ∀ x ∈ frontier K, ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧ ∃ ρ : Y → ℝ,
    (∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas Y, ContDiffOn ℝ ∞ (fun w => ρ (e.symm w)) e.target) ∧
    (∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas Y, ∀ y ∈ U ∩ e.source,
      fderiv ℝ (fun w => ρ (e.symm w)) (e y) ≠ 0) ∧
    K ∩ U = {y | ρ y ≤ 0} ∩ U

/-- **Compact `C^∞` piece** of a Riemann surface `X` (§1.4): a compact smooth subsurface ("a 2-dimensional compact
subsurface of `X` with `C^∞` boundary"). A compact surface `X` is a piece of itself, with empty boundary. -/
def IsCompactSmoothPiece {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (K : Set X) : Prop :=
  IsCompact K ∧ IsSmoothSubsurface K

/-- **Proposition 1.2.3** (Perron's theorem, Ch. 1 §1.2, H1:420). A non-empty Perron family `𝓕` on a Riemann surface
`X`,
bounded by `M`, has a harmonic supremum `F = sup 𝓕`. Modelling: `IsPerronFamily` is Farkas–Kra's family, weaker than
Hubbard's, so this is the same theorem for a larger class; the supremum is a real `sSup` of a non-empty set bounded
by `M`, so there is no junk value. -/
theorem prop1_2_3 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (𝓕 : Set (X → ℝ)) (h𝓕 : References.IsPerronFamily 𝓕) (M : ℝ)
    (hM : ∀ f ∈ 𝓕, ∀ x, |f x| ≤ M) :
    References.IsHarmonicRS univ (fun x => sSup {y : ℝ | ∃ f ∈ 𝓕, f x = y}) := by
  sorry

/-- **Proposition 1.2.4** (existence of harmonic functions, Ch. 1 §1.2, H1:434). Let `m ≤ M`, let `K` be a subsurface
of a Riemann surface `Y` with non-empty smooth boundary, and `f : ∂K → [m, M]` continuous. Then there is a continuous
`f̃ : K → [m, M]` that is harmonic on the interior of `K` and equals `f` on `∂K`. Modelling: the boundary datum is a
function `f : Y → ℝ` continuous on `frontier K` (its values elsewhere are irrelevant). -/
theorem prop1_2_4 {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {K : Set Y} (hK : IsSmoothSubsurface K) (hne : (frontier K).Nonempty)
    {m M : ℝ} (hmM : m ≤ M) (f : Y → ℝ) (hf : ContinuousOn f (frontier K))
    (hfr : ∀ x ∈ frontier K, f x ∈ Icc m M) :
    ∃ g : Y → ℝ, ContinuousOn g K ∧ (∀ x ∈ K, g x ∈ Icc m M) ∧ References.IsHarmonicRS (interior K) g ∧
      ∀ x ∈ frontier K, g x = f x := by
  sorry

end Hubbard2006
