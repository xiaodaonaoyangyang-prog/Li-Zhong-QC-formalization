/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.FibreCardWellDefinedAtRegular
import Jacobians.MappingDegree.PreconnectedFromFiniteComplement
import Jacobians.MappingDegree.RegularSubsetPreconnected

/-! # Hurwitz constant-card, staged on `h_path`

Compose `fibre_card_well_defined_at_regular_holds_of_locallyConstant_preconnected`
with `isPreconnected_compl_of_isPathConnected_compl` so that the *only*
topological residual exposed at the headline is

```
∀ C : Set Y, C.Finite → (Cᶜ).Nonempty → IsPathConnected (Cᶜ : Set Y).
```

The wrapper exposes the analytic content as a single `h_pkg` parameter —
the **per-`f` regular-subset packaging**: for every non-constant analytic
`f`, a finite set `C ⊆ Y` such that every `RegularValueWitnessReg f` has
its `value` in `Cᶜ`, and the fibre-cardinality `(f ⁻¹' {y}).ncard` is
locally constant on `Cᶜ`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

namespace Degree

universe u v

/-- **Hurwitz constant fibre-cardinality, staged on path-connected
complements.** Given:

* `h_path` — the complement of any finite set in `Y` is path-connected
  (when nonempty); `isPreconnected_compl_of_isPathConnected_compl` turns
  it into the `IsPreconnected` hypothesis consumed downstream.
* `h_pkg` — per-`f` packaging: existence of a finite `C ⊆ Y` with
  - regular witnesses' values in `Cᶜ`,
  - locally-constant fibre-ncard on `Cᶜ`.

Conclude the unfolded form of
`fibre_card_well_defined_at_regular_statement`. -/
theorem fibre_card_well_defined_at_regular_holds_of_pathConnected_compl
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y))
    (h_pkg : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (C : Set Y), C.Finite ∧
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y)) ∧
        IsLocallyConstant
          (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  -- Build the preconnectedness supplier from h_path.
  have h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) :=
    Jacobians.Discharge.Manifold.isPreconnected_compl_of_isPathConnected_compl h_path
  -- Supply the bundled (R, h_supp, h_lc, h_conn).
  apply fibre_card_well_defined_at_regular_holds_of_locallyConstant_preconnected
  intro f hf hnc
  obtain ⟨C, hC_fin, h_supp, h_lc⟩ := h_pkg f hf hnc
  refine ⟨(Cᶜ : Set Y), h_supp, h_lc, ?_⟩
  -- IsPreconnected (univ : Set Cᶜ) from h_topo via subtype lift.
  exact Jacobians.Discharge.Manifold.regularSubset_isPreconnected_of_finite_complement_hypothesis
    h_topo C hC_fin

end Degree

end ContMDiff

end Jacobians.Discharge
