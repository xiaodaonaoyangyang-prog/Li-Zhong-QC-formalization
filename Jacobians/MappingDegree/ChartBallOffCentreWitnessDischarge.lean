/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.PerChartNonConstancyReduction


/-! # Discharging the chart-ball off-centre witness from "not eventually constant"

`PerChartNonConstancyReduction.lean` reduced
`PerChartNonConstancyHypothesis X Y` to `ChartBallOffCentreWitnessHypothesis X Y`.
That hypothesis asks, for every non-constant `C^ω` map `f`, every fibre point
`x` of `y₀ = f x`, and every radius `r > 0`, to exhibit a single point
`z₁ ∈ Metric.ball ((chartAt ℂ x) x) r` at which the chart pullback differs
from its value at the chart image of `x`.

This file provides the **identity-theorem witness extractor**: given
that the chart pullback `F : ℂ → ℂ` is analytic at `z₀ = (chartAt ℂ x) x`
(true under `ContMDiff … ω`) and that `F` is **not** eventually equal
to `F z₀` near `z₀`, every metric ball around `z₀` contains an off-centre
point at which `F` differs from `F z₀`.

The mechanism is the mathlib dichotomy
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`: either `F - F z₀` is
eventually zero near `z₀` (excluded by hypothesis) or `F - F z₀ ≠ 0` on a
punctured neighborhood, hence on every small enough metric ball minus `z₀`.

The remaining obstruction is the bridge from `¬ IsConstantMap f` to "chart
pullback at every fibre point is not eventually `chartAt _ y₀ y₀`" — the
manifold-level analytic-continuation step, taken as a hypothesis-parameter. -/

@[expose] public section

open Set Filter Topology Metric
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## ℂ-analytic core: off-centre witness from "not eventually constant" -/

/-- **Off-centre witness in any small ball.** If `F : ℂ → ℂ` is analytic at
`z₀` and is *not* eventually equal to `F z₀` near `z₀`, then every metric
ball around `z₀` of positive radius contains a point at which `F` differs
from `F z₀`.

Mechanism: the mathlib dichotomy
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` applied to
`G z := F z - F z₀` rules out the "eventually zero" branch by hypothesis,
leaving `G ≠ 0` (i.e., `F z ≠ F z₀`) on a punctured neighborhood. Any open
ball is itself a neighborhood of `z₀`, so it intersects that punctured
neighborhood non-trivially. -/
lemma AnalyticAt.exists_off_centre_value_ne
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) :
    ∀ r : ℝ, 0 < r → ∃ z ∈ Metric.ball z₀ r, F z ≠ F z₀ := by
  -- Reduce to the zero version on `G := F - (fun _ => F z₀)`.
  set G : ℂ → ℂ := fun z => F z - F z₀ with hG_def
  have hG : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hGne : ¬ ∀ᶠ z in 𝓝 z₀, G z = 0 := by
    intro hG_zero
    apply hne
    filter_upwards [hG_zero] with z hz
    have hsub : F z - F z₀ = 0 := hz
    exact sub_eq_zero.mp hsub
  -- Mathlib dichotomy: either eventually 0, or `≠ 0` on a punctured nbhd.
  have h_dich := hG.eventually_eq_zero_or_eventually_ne_zero
  rcases h_dich with h_ev0 | h_punc
  · exact (hGne h_ev0).elim
  · -- `h_punc : ∀ᶠ z in 𝓝[≠] z₀, G z ≠ 0`. Extract an open punctured nbhd.
    intro r hr_pos
    -- Take radius `r` and intersect with the punctured-nbhd condition.
    rw [eventually_nhdsWithin_iff] at h_punc
    -- `h_punc : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → G z ≠ 0`.
    rcases Metric.eventually_nhds_iff.mp h_punc with ⟨ρ, hρ_pos, hρ_imp⟩
    -- Pick a real `t > 0` strictly less than both `r` and `ρ`, and let
    -- `z := z₀ + t`. Then `z ∈ ball z₀ r`, `z ≠ z₀`, and `dist z z₀ < ρ`.
    set t : ℝ := min (r / 2) (ρ / 2) with ht_def
    have ht_pos : 0 < t := by
      apply lt_min
      · linarith
      · linarith
    have ht_lt_r : t < r := by
      have : t ≤ r / 2 := min_le_left _ _
      linarith
    have ht_lt_ρ : t < ρ := by
      have : t ≤ ρ / 2 := min_le_right _ _
      linarith
    refine ⟨z₀ + (t : ℂ), ?_, ?_⟩
    · -- `z₀ + t ∈ Metric.ball z₀ r`.
      simp only [Metric.mem_ball, dist_self_add_left]
      have : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real]
        exact abs_of_pos ht_pos
      rw [this]
      exact ht_lt_r
    · -- `F (z₀ + t) ≠ F z₀`. Apply `hρ_imp` at `z₀ + t`.
      have h_dist : dist (z₀ + (t : ℂ)) z₀ < ρ := by
        simp only [dist_self_add_left]
        have : ‖(t : ℂ)‖ = t := by
          rw [Complex.norm_real]
          exact abs_of_pos ht_pos
        rw [this]
        exact ht_lt_ρ
      have h_ne_z0 : z₀ + (t : ℂ) ≠ z₀ := by
        intro heq
        have htC : (t : ℂ) = 0 := by
          have h := heq
          -- z₀ + t = z₀ → t = 0
          linear_combination h
        have ht0 : t = 0 := by exact_mod_cast htC
        exact (ne_of_gt ht_pos) ht0
      have h_G_ne : G (z₀ + (t : ℂ)) ≠ 0 := hρ_imp h_dist h_ne_z0
      intro h_F_eq
      apply h_G_ne
      show F (z₀ + (t : ℂ)) - F z₀ = 0
      rw [h_F_eq, sub_self]

/-! ## Chart-pullback hypothesis-parameter -/

/-- **Chart-pullback non-eventual-constancy hypothesis.** For every
non-constant `C^ω` map `f : X → Y`, every fibre point `x` of every `y₀`,
the chart pullback `F = (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` is **not
eventually equal** to `(chartAt ℂ (f x)) (f x)` at the chart image
`(chartAt ℂ x) x`.

This is the manifold-side hypothesis-parameter that bridges
`¬ IsConstantMap f` to per-chart non-constancy of the pullback. The
within-one-chart version of this bridge is supplied by
`chart_pullback_not_eventually_const_of_witness` in
`AnalyticContinuationGlobalization.lean`; the manifold-globalization step
across chart overlaps is deferred elsewhere and is not the subject of this file. -/
def ChartPullbackNotEventuallyConstHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)

/-! ## Manifold-side discharge -/

/-- **Discharge of `ChartBallOffCentreWitnessHypothesis`.** From the
chart-pullback non-eventual-constancy hypothesis-parameter and the
ℂ-analyticity of chart pullbacks, every chart ball around the chart
image of a fibre point contains an off-centre value witness.

Proof: the chart pullback is analytic at `z₀ = (chartAt ℂ x) x` by the bridge
(`contMDiff_omega_analyticAt_chart_pullback`). Combined with the hypothesis
"`F` is not eventually `F z₀`" (rewritten via the chart-left-inverse identity
`F z₀ = (chartAt ℂ (f x)) (f x)`), the ℂ-side extractor
`AnalyticAt.exists_off_centre_value_ne` produces a witness in any ball. -/
theorem chartBallOffCentreWitness_of_chart_pullback_not_eventually_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartPullbackNotEventuallyConstHypothesis X Y) :
    ChartBallOffCentreWitnessHypothesis X Y := by
  intro f hf hnc y₀ x hx r hr_pos
  -- Set up the chart pullback and its centre.
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  -- Analyticity at `z₀` from the chart-pullback bridge.
  have hFA_at : AnalyticAt ℂ F z₀ :=
    contMDiff_omega_analyticAt_chart_pullback hf x
  -- `F z₀ = (chartAt ℂ (f x)) (f x)` via the chart left-inverse.
  have hz₀_F : F z₀ = (chartAt ℂ (f x)) (f x) := by
    have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv hx_src
    show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (chartAt ℂ (f x)) (f x)
    simp [Function.comp, h_inv]
  -- The hypothesis says `F` is not eventually equal to `chart(f x)(f x)` at `z₀`.
  -- Rewrite this to "not eventually equal to `F z₀`".
  have h_not_ev : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀ := by
    have h := H f hf hnc y₀ x hx
    -- `h : ¬ ∀ᶠ z in 𝓝 z₀, F z = (chartAt ℂ (f x)) (f x)`.
    intro hev
    apply h
    filter_upwards [hev] with z hz
    show F z = (chartAt ℂ (f x)) (f x)
    rw [hz]; exact hz₀_F
  -- Apply the ℂ-side extractor.
  obtain ⟨z, hz_mem, hz_ne⟩ :=
    AnalyticAt.exists_off_centre_value_ne hFA_at h_not_ev r hr_pos
  refine ⟨z, hz_mem, ?_⟩
  -- Translate `F z ≠ F z₀` to `F z ≠ (chartAt ℂ (f x)) (f x)`.
  rw [hz₀_F] at hz_ne
  exact hz_ne

/-! ## End-to-end composition -/

/-- **End-to-end conditional discharge of `fibres_finite_statement` from
chart-pullback non-eventual-constancy.** -/
theorem fibres_finite_statement_holds_of_chart_pullback_not_eventually_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartPullbackNotEventuallyConstHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_chartBallOffCentreWitness
    (chartBallOffCentreWitness_of_chart_pullback_not_eventually_const H)

end Degree
end ContMDiff
end Jacobians.Discharge
