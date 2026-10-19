/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.LocalKFoldMultiplicityUnconditional
import Jacobians.LocalMultiplicity.AnalyticLocalFactorization



/-! # Planar k-fold local multiplicity

Composition of `localKFoldMultiplicity_preimage_card_of_localFactorization`
(which still required a local analytic factorization
`g z - w₀ = (z - x₀)^k * u z` with `u x₀ ≠ 0` as a hypothesis) with
`analytic_local_factorization` (which discharges that factorization
hypothesis directly from `AnalyticAt ℂ g x₀` plus
`analyticOrderAt (g - w₀) x₀ = k`).

The result is a hypothesis-free statement: from `AnalyticAt ℂ g x₀`,
`g x₀ = w₀`, and `analyticOrderAt (g - w₀) x₀ = k` with `k ≥ 1`, there
exist radii `ε, δ > 0` such that for every `w ∈ ball w₀ δ \ {w₀}` the
equation `g z = w` has exactly `k` solutions in `ball x₀ ε`.

No bundle hypotheses: only `AnalyticAt`, the value condition, and the
`analyticOrderAt = k` order condition.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

end Manifold
end Jacobians.Discharge

end
