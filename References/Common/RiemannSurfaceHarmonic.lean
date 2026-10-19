import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Shared layer: harmonic, subharmonic and Perron families on Riemann surfaces

Harmonic, subharmonic and superharmonic functions on a Riemann surface, Perron families, and Green's functions
(DESIGN §2, shared layer; registry `refs_lean\FOUNDATIONS.md`). The names were agreed between the Hubbard 2006 lane
and the Farkas–Kra 1992 lane on 2026-10-09: Hubbard Def. 1.2.1–1.2.2 and Farkas–Kra IV.2.1, IV.2.6, IV.3.6 both
point here. Everything is a genuine definition; no `sorry`.

**Convention.** `X` carries `[TopologicalSpace X] [ChartedSpace ℂ X]`; the intended surfaces are those of
`References/Common/RiemannSurface.lean` (`[T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]`), which is not
needed to state the definitions. The charts used are the members of the maximal analytic atlas
`(contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X`. Functions are real valued; a function on `X` is only looked at on the
open set `U` it is declared on.

**Mean-value definition.** `u : X → ℝ` is harmonic (resp. sub-, superharmonic) on the open set `U` if it is
continuous on `U` and its circle average over every circle `∂B(c, r)` equals (resp. is `≥`, `≤`) its value at the
centre, for every chart `e` of the atlas and every closed disc `B̄(c, r)` contained in the chart image such that
the disc, pulled back to `X`, lies in `U`. Modelling choice (Hubbard 1.2.1 says only "every circle in `U`"): the
whole closed disc is required to lie in the chart image and in `U`. With only the circle in `U` the value at the
centre can be undefined or the condition false for genuinely harmonic functions (for example `log |ζ − 1/2|` on
`ℂ ∖ {1/2}`, circle `|ζ| = 1`). Circle averages are Mathlib's `Real.circleAverage`; `u ∘ e⁻¹` is continuous on the
compact disc, so no integrability junk arises. For `U = X` the pull-back condition is vacuous.

**Near misses (not the same notion).** `Forster1981.IsHarmonicOn` (`d′d″f = 0` for smooth `f`; equal to the notion
here on smooth functions, but not stated by the mean-value property); `References.IsSubharmonicOn` of
`Common/Subharmonic` (functions `ℂ → EReal`, upper semicontinuous, by harmonic majorants, on planar open sets; this
file asks continuity, as Hubbard 1.2.1 and Farkas–Kra IV.2.1 do); `GarnettMarshall2005.greenFunction`
(a function of two points of a finitely connected Jordan domain of `ℂ̄`, defined by the Dirichlet problem, not the
global minimal function of Farkas–Kra IV.3.6 on an arbitrary Riemann surface).

* Shared notion (harmonic function on an open subset of a Riemann surface, by the mean-value property in charts;
  Hubbard 1.2.1, Farkas–Kra IV.1) — `IsHarmonicRS`
* Shared notion (subharmonic function; Hubbard 1.2.1, Farkas–Kra IV.2.1) — `IsSubharmonicRS`
* Shared notion (superharmonic function; Hubbard 1.2.1, Farkas–Kra IV.2.1) — `IsSuperharmonicRS`
* Shared notion (Perron family; Hubbard 1.2.2 bounded by `M` is `IsPerronFamily 𝓕` together with a bound `M`,
  Farkas–Kra IV.2.6 (2.6.1)–(2.6.3)) — `IsPerronFamily`
* Shared notion (the conditions (3.6.1)–(3.6.3) of Farkas–Kra IV.3.6, without minimality) — `IsGreenCandidate`
* Shared notion (Green's function with singularity `P` on a Riemann surface, Farkas–Kra IV.3.6 with minimality
  (3.6.4)) — `IsGreenFunction`
-/

open Set Metric
open scoped Manifold ContDiff

namespace References

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Harmonic function on an open subset of a Riemann surface** (Hubbard 1.2.1; Farkas–Kra IV.1): `U` is open,
`u` is continuous on `U`, and for every chart `e` of the maximal analytic atlas and every closed disc `B̄(c, r)`,
`r > 0`, contained in `e.target` with `e⁻¹(B̄(c, r)) ⊆ U`, the circle average of `u ∘ e⁻¹` over `∂B(c, r)` equals
`u (e⁻¹ c)`. Modelling: the closed disc (not just the circle) must lie in the chart image and in `U`; see the module
docstring. The values of `u` outside `U` do not matter. -/
def IsHarmonicRS (U : Set X) (u : X → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X, ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ e.target →
      e.symm '' closedBall c r ⊆ U → Real.circleAverage (fun w => u (e.symm w)) c r = u (e.symm c)

/-- **Subharmonic function on an open subset of a Riemann surface** (Hubbard 1.2.1; Farkas–Kra IV.2.1, whose
definition by the maximum principle is a lemma about this one): as `IsHarmonicRS`, with "the circle average is
`≥ u (e⁻¹ c)`". -/
def IsSubharmonicRS (U : Set X) (u : X → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X, ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ e.target →
      e.symm '' closedBall c r ⊆ U → u (e.symm c) ≤ Real.circleAverage (fun w => u (e.symm w)) c r

/-- **Superharmonic function on an open subset of a Riemann surface** (Hubbard 1.2.1; Farkas–Kra IV.2.1): as
`IsHarmonicRS`, with "the circle average is `≤ u (e⁻¹ c)`". -/
def IsSuperharmonicRS (U : Set X) (u : X → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X, ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ e.target →
      e.symm '' closedBall c r ⊆ U → Real.circleAverage (fun w => u (e.symm w)) c r ≤ u (e.symm c)

/-- **Perron family** on a Riemann surface (Farkas–Kra IV.2.6; Hubbard 1.2.2 without the bound): `𝓕` is a
non-empty set of functions subharmonic on all of `X` (2.6.1), such that for every function `u ∈ 𝓕` and every
coordinate disc (the preimage `e⁻¹(B(c, r))` of an open disc whose closure lies in the chart image of a chart `e`
of the maximal atlas) there is `v ∈ 𝓕` with `v ≥ u` that is harmonic on that disc (2.6.2), and any two members
have a common upper bound in `𝓕` (2.6.3). Modelling: Farkas–Kra's conformal discs are the coordinate discs with
`c = 0` and radius `> 1`; all coordinate discs are used here (the same condition after a change of chart).
Hubbard's *bounded* Perron family (Def. 1.2.2) is `IsPerronFamily 𝓕 ∧ ∃ M, ∀ f ∈ 𝓕, ∀ x, |f x| ≤ M`; his
conditions 2 and 3 (closure under `sup` and under harmonic replacement) imply (2.6.2) and (2.6.3) with
`v = max u₁ u₂` and `v = u^{(D)}`, so a family that is Perron in Hubbard's sense is Perron in this sense. -/
def IsPerronFamily (𝓕 : Set (X → ℝ)) : Prop :=
  𝓕.Nonempty ∧ (∀ u ∈ 𝓕, IsSubharmonicRS univ u) ∧
    (∀ u ∈ 𝓕, ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X, ∀ (c : ℂ) (r : ℝ), 0 < r →
      closedBall c r ⊆ e.target → ∃ v ∈ 𝓕, u ≤ v ∧ IsHarmonicRS (e.symm '' ball c r) v) ∧
    (∀ u₁ ∈ 𝓕, ∀ u₂ ∈ 𝓕, ∃ v ∈ 𝓕, u₁ ≤ v ∧ u₂ ≤ v)

/-- **The conditions of a Green's function without minimality** (Farkas–Kra IV.3.6, (3.6.1)–(3.6.3)): `g` is
harmonic on `X ∖ {P}` (3.6.1), `g > 0` on `X ∖ {P}` (3.6.2), and for every chart `e` of the maximal atlas with
`P ∈ e.source` and `e P = 0` there are an open neighbourhood `V ⊆ e.source` of `P` and a function `h` harmonic on
`V` with `h = g + log ‖e‖` on `V ∖ {P}` (3.6.3: "`g + log |z|` is harmonic in a neighbourhood of `P`", the value at
`P` being supplied by `h`). Modelling: the value `g P` is irrelevant (never looked at); `Real.log` is applied to
`‖e x‖ ≠ 0` on `V ∖ {P}` only if `e` is injective there, which holds on `e.source`, so there is no `log 0` junk.
Condition (3.6.3) is independent of the chart vanishing at `P` (Farkas–Kra's remark), so quantifying over all of
them is the book's condition. Intended for Hausdorff `X` (so that `{P}ᶜ` is open). -/
def IsGreenCandidate (P : X) (g : X → ℝ) : Prop :=
  IsHarmonicRS {P}ᶜ g ∧ (∀ x, x ≠ P → 0 < g x) ∧
    ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X, P ∈ e.source → e P = 0 →
      ∃ V : Set X, V ⊆ e.source ∧ P ∈ V ∧ ∃ h : X → ℝ, IsHarmonicRS V h ∧
        ∀ x ∈ V, x ≠ P → h x = g x + Real.log ‖e x‖

/-- **Green's function with singularity at `P`** (Farkas–Kra IV.3.6): `g` satisfies (3.6.1)–(3.6.3)
(`IsGreenCandidate P g`) and is minimal: every other function `ĝ` satisfying them has `ĝ ≥ g` on `X ∖ {P}`
(3.6.4). Modelling: the book's "`ĝ ≥ g`" is read on `X ∖ {P}`, where both are defined; the values at `P` are never
looked at. Hubbard's Green function of a compact `C^∞` piece (Prop. 1.5.1) is a different notion
(`Hubbard2006.IsGreenFunctionOn`: vanishing on the boundary, no minimality). -/
def IsGreenFunction (P : X) (g : X → ℝ) : Prop :=
  IsGreenCandidate P g ∧ ∀ g' : X → ℝ, IsGreenCandidate P g' → ∀ x, x ≠ P → g x ≤ g' x

end References
