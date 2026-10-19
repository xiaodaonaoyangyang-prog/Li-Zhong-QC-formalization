/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Connected.Basic

/-! # Preconnectedness of the regular subset on a general compact connected
complex 1-manifold

This file provides the general-`Y` analogue of
`RegularValueSetConnected.lean`. It packages two purely topological
reductions:

1.  **Subtype-from-ambient**: an ambient `IsPreconnected (S : Set Y)`
    upgrades to `IsPreconnected (Set.univ : Set ↥S)`. This is a clean
    one-liner via `Subtype.preconnectedSpace`.

2.  **Regular-subset reduction**: parameterised on the standard
    topological fact

    *   for any finite `C : Set Y`, the complement `Cᶜ ⊆ Y` is
        preconnected,

    we deliver, for any finite critical-value set `C`, the
    subtype-preconnectedness conclusion in the literal shape
    `fibre_card_eq_of_locallyConstant_subtype_reg` consumes:
    `IsPreconnected (Set.univ : Set (Cᶜ : Set Y))`.

The mathematical content of (2) — that a connected complex 1-manifold
(equivalently, real 2-manifold) minus finitely many points is
preconnected — is the standard "go around the puncture" path argument.
Following the pattern of `RegularValueSetConnected.lean` (the sphere
case), we name this fact as a clean topological hypothesis here and let
downstream consumers supply it. -/

@[expose] public section

noncomputable section

open Set Topology

namespace Jacobians.Discharge
namespace Manifold

universe u

/-! ## Subtype-from-ambient bridge -/

/-- **Subtype-preconnectedness from ambient preconnectedness.** If
`S : Set Y` is preconnected as an ambient set, then the universe of the
subtype `↥S` is preconnected. This is the literal shape consumed by
`fibre_card_eq_of_locallyConstant_subtype_reg`. -/
lemma isPreconnected_univ_subtype_of_isPreconnected_set_general
    {Y : Type u} [TopologicalSpace Y]
    {S : Set Y} (h : IsPreconnected S) :
    IsPreconnected (Set.univ : Set S) := by
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace h
  exact isPreconnected_univ

/-! ## Regular-subset reduction -/

/-- **Subtype preconnectedness of `Cᶜ`, given ambient preconnectedness
of `Cᶜ`.** Bare wrapper around the subtype-from-ambient bridge,
specialised to the complement form `Cᶜ` that is the literal output of
`Y \ f(criticalSet f)`. -/
theorem regularSubset_isPreconnected_subtype_of_compl
    {Y : Type u} [TopologicalSpace Y]
    (C : Set Y)
    (h_amb : IsPreconnected (Cᶜ : Set Y)) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set Y))) :=
  isPreconnected_univ_subtype_of_isPreconnected_set_general h_amb

/-- **Headline structural theorem (parameterised on the topological
hypothesis).** Given that the complement of any finite set in `Y` is
preconnected (the standard "connected complex 1-manifold minus finitely
many points stays connected" fact), the regular subset
`(f(criticalSet f))ᶜ` is preconnected as a subtype, in the exact form
`FibreCardOnRegularSubset` consumes.

The hypothesis `h_topo` is the clean topological boundary: for compact
connected complex 1-manifolds (equivalently real 2-manifolds), this is
known classically; we name it here so the downstream consumer can
compose against it without bringing the chart-by-chart construction
into this file. -/
theorem regularSubset_isPreconnected_of_finite_complement_hypothesis
    {Y : Type u} [TopologicalSpace Y]
    (h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y))
    (C : Set Y) (hC_fin : C.Finite) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set Y))) :=
  regularSubset_isPreconnected_subtype_of_compl C (h_topo C hC_fin)

end Manifold
end Jacobians.Discharge
