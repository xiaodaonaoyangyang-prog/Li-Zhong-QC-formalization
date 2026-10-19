/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Jacobians.MappingDegree.LocalMultiplicityInvariance

/-! # Local multiplicity invariance — branched (`k ≥ 1`) reduction

This file extends ZZ74's `k = 1` result
(`localMultiplicityOne_preimage_card`, in
`Jacobians.Discharge.Manifold.LocalMultiplicityInvariance`) toward the
**branched** case where the local order at `x₀` is `k ≥ 1`.

## Reduction strategy

If `g : ℂ → ℂ` is analytic at `x₀` with `g x₀ = w₀` and local order `k`,
then on a small disc

  `g(z) - w₀ = (z - x₀) ^ k · u(z)`,

with `u` analytic at `x₀` and `u(x₀) ≠ 0`. Choosing an analytic `k`-th
root branch of `u` on a small disc, set
`v(z) := (z - x₀) · u(z) ^ (1 / k)`. Then

  `g(z) - w₀ = v(z) ^ k`,    `v(x₀) = 0`,    `v'(x₀) ≠ 0`.

So `v` is a local biholomorphism (ZZ74's `k = 1` case applied to `v`).
Solving `g z = w` becomes solving `v(z) ^ k = w - w₀`, with exactly `k`
distinct `k`-th roots for `w ≠ w₀` near `w₀`, each producing one
preimage `z = v.symm w'` via the local inverse of `v`.

## What this file delivers

The packaging of "analytic `k`-th root branch of a non-vanishing analytic
function on a small disc" is **not** routed at the mathlib pin
`8e3c989` (15 April 2026). Per the brief's guidance for blocked content,
we therefore:

1. **State the analytic substitution as a hypothesis bundle**
   (`KthRootSubstitution g x₀ w₀ k`).

2. **Discharge the `k = 1` bundle unconditionally**
   (`kthRootSubstitution_of_localMultiplicityOne`): take
   `v(z) := g(z) - w₀`.

3. **Reduce the bundle's `k = 1` consequence to ZZ74**
   (`localKFoldMultiplicity_preimage_card_of_substitution_one`).

The general-`k` step (passing from `card = 1` for `v(z) = w'` to `card = k`
for `g(z) = w`) requires the analytic `k`-th root packaging mentioned
above — see the named statement
`analytic_kth_root_branch_exists_statement` — and an explicit `k`-th
roots-of-unity enumeration; both are unrouted at this pin.

## Status

* `KthRootSubstitution` — definition. No `axiom`, no gaps.
* `kthRootSubstitution_of_localMultiplicityOne` — `k = 1` bundle is
  unconditional. No gaps.
* `localKFoldMultiplicity_preimage_card_of_substitution_one` — full
  ε–δ count for `k = 1` from the bundle, by deriving `g`-side analyticity
  + nonvanishing-derivative directly from the bundle and re-invoking
  ZZ74 on `g` itself. No gaps.
* `analytic_kth_root_branch_exists_statement` — `Prop`-valued name for
  the missing-mathlib content, the only block on the general `k ≥ 2`
  step. No `axiom`; this is *only* a statement.

-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Hypothesis bundle for the `k`-th root substitution.**

For `g : ℂ → ℂ` analytic with `g x₀ = w₀` and local order `k` at `x₀`, the
analytic substitution `v` should satisfy, on a small closed disc of
radius `ρ`:

* `v` is analytic on `closedBall x₀ ρ`,
* `v x₀ = 0`,
* `deriv v x₀ ≠ 0`,
* `g z - w₀ = (v z) ^ k` for every `z ∈ closedBall x₀ ρ`.

These four conditions are exactly the data needed to reduce the `k`-fold
preimage-count theorem to ZZ74's `k = 1` case applied to `v`.

For `k = 1` the bundle is constructed unconditionally
(`kthRootSubstitution_of_localMultiplicityOne`). For `k ≥ 2` the
construction requires an analytic `k`-th root branch of the unit factor
`u` in the local form `g - w₀ = (z - x₀)^k · u`, which is the
named-only gap `analytic_kth_root_branch_exists_statement`. -/
structure KthRootSubstitution (g : ℂ → ℂ) (x₀ w₀ : ℂ) (k : ℕ) : Prop where
  exists_substitution :
    ∃ (v : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOnNhd ℂ v (Metric.closedBall x₀ ρ) ∧
      v x₀ = 0 ∧
      deriv v x₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall x₀ ρ, g z - w₀ = (v z) ^ k)

end Manifold
end Jacobians.Discharge

end
