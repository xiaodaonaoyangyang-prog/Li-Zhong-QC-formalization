/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.ChartPullbackDataConstruction


/-! # Full assembly: `fibres_finite_statement` modulo a single connectivity hypothesis

This file composes the reduction chain for `Degree.fibres_finite_statement`:

* `Degree.lean`: `fibres_finite_of_all_fibers_isDiscrete` reduces the
  statement to per-fibre `IsDiscrete`.
* `AnalyticFiberDiscrete.lean`: `fibres_finite_of_chart_pullback`
  reduces it further to a per-fibre-point `ChartPullbackData`.
* `ContMDiffOmegaAnalytic.lean`: the bridge
  `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x → AnalyticAt ℂ` on chart pullbacks.
* `AnalyticContinuationGlobalization.lean`: the within-chart globalisation
  of "not eventually constant" via the identity theorem.
* `ChartPullbackDataConstruction.lean`:
  `chartPullbackData_of_contMDiff_global` builds `ChartPullbackData` from
  `ContMDiff … ω f` plus a per-fibre-point local non-degeneracy hypothesis.

The single remaining input is the **connectivity-globalization** step,
packaged as `ConnectivityGlobalizationHypothesis`: from "`f` is not (globally)
constant" on a connected `X`, derive "for every fibre point `x`, the chart
pullback of `f` is not eventually equal to its value at `(chartAt ℂ x) x`" —
the analytic-continuation argument across charts. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Connectivity-globalization hypothesis

The single input taken as a hypothesis-parameter here: for every
non-constant `C^ω` map between (connected) complex manifolds, the chart
pullback near every fibre point is not eventually equal to its target
chart-value. Equivalently, "`f` non-constant globally" implies "the chart
pullback of `f` is not eventually constant at any fibre point". -/
def ConnectivityGlobalizationHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
            = (chartAt ℂ (f x)) (f x)

/-! ## Assembly

The proof composes `chartPullbackData_of_contMDiff_global` (the connectivity
hypothesis into a `ChartPullbackData` at every fibre point) with
`fibres_finite_of_chart_pullback`. -/

/-- **Full assembly: `fibres_finite_statement` from the connectivity-
globalization hypothesis.** Given `ConnectivityGlobalizationHypothesis X Y`,
the classical statement `fibres_finite_statement X Y` holds. -/
theorem fibres_finite_of_connectivity_hypothesis
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ConnectivityGlobalizationHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite := by
  -- Build the per-fibre-point chart-pullback assignment from `H`.
  refine fibres_finite_of_chart_pullback ?_
  intro f hf hnc y x hx
  -- `hx : x ∈ f ⁻¹' {y}`, i.e. `f x = y`.
  have hx_eq : f x = y := hx
  -- Apply the globalised constructor; its non-degeneracy parameter is
  -- exactly the conclusion of `H` (after specialising `y₀ := y`).
  have hne : ∀ x' : X, f x' = y →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x') x'),
          ((chartAt ℂ (f x')) ∘ f ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f x')) (f x') := fun x' hx' => H f hf hnc y x' hx'
  exact chartPullbackData_of_contMDiff_global hf hne x hx

/-! ## Discharge restated against `fibres_finite_statement`

We export the assembly as a direct conditional discharge of
`fibres_finite_statement`: under the connectivity hypothesis, the statement
holds. -/

/-- **Conditional discharge.** `fibres_finite_statement X Y` holds whenever the
connectivity-globalization hypothesis holds. Equivalent to
`fibres_finite_of_connectivity_hypothesis` but stated as a one-line
implication for ergonomic downstream use. -/
theorem fibres_finite_statement_holds_of_connectivity
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ConnectivityGlobalizationHypothesis X Y →
      ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
        ¬ Jacobians.Discharge.IsConstantMap f →
          ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_of_connectivity_hypothesis

end Degree
end ContMDiff
end Jacobians.Discharge
