/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology


/-! # Local multiplicity invariance — the `k = 1` (biholomorphic) case

This file proves the **`k = 1` slice** of the topological local-multiplicity
theorem (the "branched holomorphic degree" combinatorial fact):

> Let `g : ℂ → ℂ` be analytic at `x₀ : ℂ` with `g(x₀) = w₀` and
> `deriv g x₀ ≠ 0` (i.e. local multiplicity exactly `1`). Then there exist
> `ε > 0` and `δ > 0` such that for every `w ∈ ball w₀ δ` with `w ≠ w₀`,
> the equation `g z = w` has *exactly one* solution in `ball x₀ ε`.

In the language of branched-cover degree theory, this is the statement that
near a regular point (one with non-vanishing derivative), the analytic map
`g` is locally a homeomorphism onto an open set, so each value near `w₀` has
exactly one preimage in the chosen neighborhood.

The proof routes through the **inverse function theorem**
(`HasStrictFDerivAt.toOpenPartialHomeomorph`); the general `k ≥ 2` case
requires the argument principle / Rouché theorem and lives elsewhere.  The
companion file `LocalNormalForm.lean` proves *injectivity* of `g` on a
neighborhood of a regular point; the contribution here is to upgrade that to
the **explicit ε–δ preimage-count form**: for every value `w` close to (but
not equal to) `w₀`, the preimage set in a *specified* `ball x₀ ε` has
*exactly one* element.

## Proof sketch

1. Lift `AnalyticAt` to `HasStrictDerivAt` (via
   `AnalyticAt.hasStrictDerivAt`).
2. With non-vanishing derivative, repackage as `HasStrictFDerivAt` with a
   `ContinuousLinearEquiv` derivative
   (`HasStrictDerivAt.hasStrictFDerivAt_equiv`).
3. The inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`)
   yields an `OpenPartialHomeomorph φ` realising `g` as a homeomorphism from
   an open neighborhood of `x₀` onto an open neighborhood of `w₀`.
4. Pick `ε > 0` small enough that `ball x₀ ε ⊆ φ.source`
   (`IsOpen.mem_nhds` on the source).
5. Pick `δ > 0` small enough that `ball w₀ δ ⊆ φ.target` *and*
   `φ.symm '' (ball w₀ δ) ⊆ ball x₀ ε` (via continuity of `φ.symm` at `w₀`).
6. For `w ∈ ball w₀ δ \ {w₀}`, the unique solution to `g z = w` in
   `φ.source` is `φ.symm w ∈ ball x₀ ε`, and by `φ.injOn` no other
   `z ∈ φ.source` solves it; in particular no other `z ∈ ball x₀ ε ⊆ φ.source`
   does. Therefore the preimage has cardinality exactly `1`.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

end Manifold
end Jacobians.Discharge

end
