/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionF_IntArith

/-!
# Section G: Set-Theoretic Topology
## HOL Light: Section G (Lines 12022–12657)

Homeomorphisms, closures, images, and their interactions.

Most HOL Light results in this section are standard Mathlib facts:
- `IMAGE_INTERS` ↔ `Set.image_iInter₂` (injective case)
- `homeo_closure` ↔ `Homeomorph.image_closure`
- `INJ_IMAGE` / `image_power_inj` ↔ `Function.Injective.image_eq`
- `homeomorphism_inv` ↔ `Homeomorph.symm`
- `inv_comp_left/right` ↔ `Homeomorph.symm_apply_apply` /
  `Homeomorph.apply_symm_apply`
- `image_inv_image` ↔ `Set.preimage_image_eq` + injectivity
- `image_powerset` ↔ `Homeomorph.image_bijective` (Section F)

We formalize only the custom lemmas that depend on definitions from
earlier sections (`cellAdj`, `numClosure`, `IMAGE2`, `Segment`).
-/

open Set Topology

noncomputable section

/-! ## Adjacency under homeomorphisms -/

/-- A homeomorphism preserves cell-adjacency, provided the image of
    every cell is again a cell.
    HOL Light: `homeo_adj` (line 12183). -/
theorem homeomorph_cellAdj (f : E2 ≃ₜ E2)
    (hcell : ∀ C, isCell C → isCell (f '' C))
    {X Y : Set E2} (hadj : cellAdj X Y) :
    cellAdj (f '' X) (f '' Y) := by
  obtain ⟨hX, hY, hne, z, hz⟩ := hadj
  refine ⟨hcell X hX, hcell Y hY, ?_, ?_⟩
  · exact fun h => hne (f.injective.image_injective h)
  · rw [← f.image_closure X, ← f.image_closure Y] at *
    exact ⟨f z, Set.mem_inter
      (Set.mem_image_of_mem f hz.1)
      (Set.mem_image_of_mem f hz.2)⟩

/-! ## numClosure under homeomorphisms -/

/-- A homeomorphism preserves `numClosure`, provided the target point is
    the image of the source lattice point.
    HOL Light: `homeo_num_closure` (line 12563). -/
theorem homeo_numClosure (f : E2 ≃ₜ E2)
    (G : Finset (Set E2)) (m m' : ℤ × ℤ)
    (hm : f (pointI m) = pointI m') :
    numClosure G m =
      numClosure (G.image (f '' ·)) m' := by
  classical
  simp only [numClosure, incidentEdges]
  have hinj : Function.Injective (f '' · : Set E2 → Set E2) :=
    f.injective.image_injective
  conv_rhs => rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ hinj]
  congr 1; ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hcl⟩
    refine ⟨he, ?_⟩
    rw [← f.image_closure, ← hm]
    exact Set.mem_image_of_mem f hcl
  · rintro ⟨he, hcl⟩
    refine ⟨he, ?_⟩
    rw [← f.image_closure, ← hm] at hcl
    exact f.injective.mem_set_image.mp hcl

end
