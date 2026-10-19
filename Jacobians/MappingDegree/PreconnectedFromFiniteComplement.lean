/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Connected.PathConnected
/-! # Path-connected ⇒ preconnected reduction for the finite-puncture case

For a connected complex 1-manifold `Y`, the complement of any finite set
is preconnected. This is the standard "go around the puncture" fact: the
path-connectedness of `Cᶜ` for finite `C` on a connected 2-manifold.
Mathlib's `Set.Countable.isPathConnected_compl_of_one_lt_rank` gives this
for normed ℝ-spaces of real rank ≥ 2 but does not lift through a chart
structure, so this file states the reduction: given the manifold-lift
`h_path` (path-connectedness of the finite complement), preconnectedness
follows. -/

@[expose] public section

namespace Jacobians.Discharge
namespace Manifold

universe u

/-- Given the path-connectedness of `Cᶜ`, preconnectedness follows.

Used by `RegularSubsetPreconnected.lean`'s `h_topo` parameter via the
convenience wrapper `isPreconnected_compl_of_isPathConnected_compl` below. -/
theorem isPreconnected_compl_finite_of_isPathConnected
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {C : Set Y} (_hC : C.Finite)
    (h_path : (Cᶜ : Set Y).Nonempty → IsPathConnected (Cᶜ : Set Y)) :
    IsPreconnected (Cᶜ : Set Y) := by
  by_cases h : (Cᶜ : Set Y) = ∅
  · rw [h]; exact isPreconnected_empty
  · have hne : (Cᶜ : Set Y).Nonempty := Set.nonempty_iff_ne_empty.mpr h
    exact (h_path hne).isConnected.isPreconnected

/-- **Convenience composition.** If the complement of every finite set is
path-connected (when nonempty), then the complement of every finite set is
preconnected — the shape consumed by `RegularSubsetPreconnected.lean`. -/
theorem isPreconnected_compl_of_isPathConnected_compl
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y)) :
    ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) := by
  intro C hC
  exact isPreconnected_compl_finite_of_isPathConnected hC (h_path C hC)

end Manifold
end Jacobians.Discharge
