/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.AnalyticContinuationGlobalization
import Jacobians.MappingDegree.FibresFiniteAssembly


/-! # Reducing `ConnectivityGlobalizationHypothesis` to a within-chart witness hypothesis

`FibresFiniteAssembly.lean` reduced `fibres_finite_statement X Y` to a single
hypothesis: `ConnectivityGlobalizationHypothesis X Y`. That hypothesis is
*filter-shaped* ("not eventually equal to a constant"), and its proof requires
walking analytic continuation along a path in `X`.

This file provides a **strictly smaller, different-shaped** hypothesis that
suffices: for every non-constant `C^ω` map `f : X → Y` and every fibre point
`x` of every `y₀`, there exists a *concrete witness* — an open preconnected
set `U ⊆ ℂ` containing the chart image `(chartAt ℂ x) x` on which the chart
pullback is `AnalyticOnNhd ℂ`, together with a point `z₁ ∈ U` whose value
under the chart pullback differs from the chart image of `f x`.

The shape is genuinely smaller because it is *existential* (provide a
`(U, z₁)` pair) rather than a *universal* filter statement; `U` need not be
the entire chart domain; and the "not eventually `c`" conclusion is *derived*
from the witness via the classical identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, packaged as
`not_eventually_const_of_not_constOn`).

This is a *partial* reduction: the within-chart witness still encodes
"non-constancy is observed *in this fibre point's chart*", which in general
requires path-walking from a globally non-constant pair into the chart of
`x`.  But it isolates the path-walking to a clean existence-of-witness
statement in `ℂ`, with no mention of eventually-equal filters or the identity
theorem. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## The within-chart witness hypothesis -/

/-- **Within-chart witness hypothesis.** For every non-constant `C^ω` map
`f : X → Y` and every fibre point `x` of every `y₀ : Y`, there exists an open
preconnected set `U ⊆ ℂ` containing the chart image of `x`, on which the
chart pullback of `f` is `AnalyticOnNhd`, plus a witness `z₁ ∈ U` whose chart
pullback value differs from `(chartAt ℂ (f x)) (f x)`.

This hypothesis is strictly weaker (and strictly different in shape) than
`ConnectivityGlobalizationHypothesis`: that one quantifies a filter
("not eventually equal"); this one provides an explicit `(U, z₁)` pair from
which the filter statement is derived via the classical identity theorem. -/
def WithinChartWitnessHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ∃ U : Set ℂ,
        IsPreconnected U ∧
        ((chartAt ℂ x) x) ∈ U ∧
        AnalyticOnNhd ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) U ∧
        ∃ z₁ ∈ U,
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z₁
            ≠ (chartAt ℂ (f x)) (f x)

/-! ## Discharge of the connectivity hypothesis from the within-chart witness -/

/-- **Reduction.** The within-chart witness hypothesis implies the
connectivity-globalization hypothesis. The proof is a direct application of
`not_eventually_const_of_not_constOn` (the classical identity-theorem
contrapositive in this file's companion). -/
theorem connectivityGlobalization_of_withinChartWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : WithinChartWitnessHypothesis X Y) :
    ConnectivityGlobalizationHypothesis X Y := by
  intro f hf hnc y₀ x hx
  obtain ⟨U, hU_pc, hxU, hFA, z₁, hz₁U, hz₁_ne⟩ := H f hf hnc y₀ x hx
  exact not_eventually_const_of_not_constOn hFA hU_pc hxU hz₁U hz₁_ne

/-! ## End-to-end: `fibres_finite_statement` from the within-chart witness -/

/-- **End-to-end:** the within-chart witness hypothesis suffices for
the full `fibres_finite_statement`. -/
theorem fibres_finite_statement_holds_of_withinChartWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : WithinChartWitnessHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_connectivity
    (connectivityGlobalization_of_withinChartWitness H)

end Degree
end ContMDiff
end Jacobians.Discharge
