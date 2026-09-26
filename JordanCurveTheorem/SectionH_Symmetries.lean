/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionG_SetTopology

/-!
# Section H: Symmetries
## HOL Light: Section H (Lines 12658–14930)

The three reflection symmetries of the cell decomposition: coordinate swap
(`reflA`), horizontal reflection (`reflB`), and vertical reflection (`reflC`).
These allow reducing case analysis by factors of 2–4 throughout the proof.

### Key HOL Light definitions
- `reflA`: (x, y) ↦ (y, x) — swaps horizontal and vertical edges
- `reflB`: (x, y) ↦ (-x - 1, y) — horizontal reflection
- `reflC`: (x, y) ↦ (x, -y - 1) — vertical reflection
-/

open Set

noncomputable section

/-! ## reflA: Coordinate swap -/

/-- Coordinate swap reflection: (x, y) ↦ (y, x).
    HOL Light: `reflA`. Maps h_edges to v_edges and vice versa. -/
def reflA : E2 → E2 := fun p => point (p 1, p 0)

/-- `reflA` is an involution: applying it twice is the identity. -/
theorem reflA_involutive : Function.Involutive reflA := by
  intro z
  simp only [reflA, point, Fin.isValue, WithLp.equiv_symm_apply, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  ext i; fin_cases i <;> simp

/-- `reflA` is continuous. -/
theorem reflA_continuous : Continuous reflA := by
  unfold reflA
  change Continuous (fun p : E2 => point (p 1, p 0))
  unfold point
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i; fin_cases i
  · exact PiLp.continuous_apply 2 _ 1
  · exact PiLp.continuous_apply 2 _ 0

/-- `reflA` maps lattice points to lattice points. -/
theorem reflA_pointI (m : ℤ × ℤ) :
    reflA (pointI m) = pointI (m.2, m.1) := by
  simp [reflA, pointI, point]

/-- `reflA` is a homeomorphism of ℝ². -/
def reflA_homeomorph : E2 ≃ₜ E2 where
  toEquiv := reflA_involutive.toPerm
  continuous_toFun := reflA_continuous
  continuous_invFun := reflA_continuous

/-- `reflA` maps horizontal edges to vertical edges. -/
theorem reflA_hEdge (m : ℤ × ℤ) :
    reflA '' (hEdge m) = vEdge (m.2, m.1) := by
  ext z; simp only [mem_image, hEdge, vEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h3, h1, h2⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflA z, ?_, reflA_involutive z⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h2, h3, h1⟩

/-- `reflA` maps vertical edges to horizontal edges. -/
theorem reflA_vEdge (m : ℤ × ℤ) :
    reflA '' (vEdge m) = hEdge (m.2, m.1) := by
  ext z; simp only [mem_image, vEdge, hEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h2, h3, h1⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflA z, ?_, reflA_involutive z⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h3, h1, h2⟩

/-- `reflA` maps squares to squares. -/
theorem reflA_squ (m : ℤ × ℤ) :
    reflA '' (squ m) = squ (m.2, m.1) := by
  ext z; simp only [mem_image, squ, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h3, h4, h1, h2⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨reflA z, ?_, reflA_involutive z⟩
    simp only [reflA, point_coord_zero, point_coord_one]; exact ⟨h3, h4, h1, h2⟩

/-- `reflA` maps cells to cells. -/
theorem reflA_cell {C : Set E2} (hC : isCell C) :
    isCell (reflA '' C) := by
  obtain ⟨ct, rfl⟩ := hC
  cases ct with
  | point m => exact ⟨.point (m.2, m.1),
      show reflA '' {pointI m} = {pointI (m.2, m.1)} by
        rw [image_singleton, reflA_pointI]⟩
  | hEdge m => exact ⟨.vEdge (m.2, m.1), reflA_hEdge m⟩
  | vEdge m => exact ⟨.hEdge (m.2, m.1), reflA_vEdge m⟩
  | squ m => exact ⟨.squ (m.2, m.1), reflA_squ m⟩

/-- `reflA` preserves adjacency. -/
theorem reflA_cellAdj {X Y : Set E2} (h : cellAdj X Y) :
    cellAdj (reflA '' X) (reflA '' Y) :=
  homeomorph_cellAdj reflA_homeomorph (fun _C hC => reflA_cell hC) h

/-- Common connectivity argument for reflection-based rectagon preservation. -/
private theorem image_rectagon_connected (f : E2 → E2)
    (h_cellAdj : ∀ {X Y : Set E2}, cellAdj X Y → cellAdj (f '' X) (f '' Y))
    (G : Rectagon) :
    let edges' := G.edges.image (f '' ·)
    ∀ S ⊆ (↑edges' : Set _), S.Nonempty →
        (∀ C ∈ S, ∀ C' ∈ (↑edges' : Set _), cellAdj C C' → C' ∈ S) →
        S = ↑edges' := by
  intro edges' S hS hSne hSclosed
  let T : Set (Set E2) := {e ∈ (↑G.edges : Set _) | f '' e ∈ S}
  have hTG : T ⊆ ↑G.edges := fun e he => he.1
  have hTne : T.Nonempty := by
    obtain ⟨C, hC⟩ := hSne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hS hC))
    exact ⟨e, Finset.mem_coe.mpr he, hC⟩
  have hTclosed : ∀ C ∈ T, ∀ C' ∈ (↑G.edges : Set _), cellAdj C C' → C' ∈ T := by
    intro C ⟨hCG, hCS⟩ C' hC'G hadj
    exact ⟨hC'G, hSclosed _ hCS _
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨C', Finset.mem_coe.mp hC'G, rfl⟩))
      (h_cellAdj hadj)⟩
  have hTeq := G.connected T hTG hTne hTclosed
  ext C'; exact ⟨fun h => hS h, fun hC' => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hC')
    exact (hTeq ▸ Finset.mem_coe.mpr he : e ∈ T).2⟩

/-- `reflA` preserves the rectagon property.
    HOL Light: `reflA_segment`. -/
theorem reflA_rectagon (G : Rectagon) :
    ∃ G' : Rectagon, (↑G'.edges : Set _) = (fun e => reflA '' e) '' ↑G.edges := by
  let edges' := G.edges.image (fun e => reflA '' e)
  have hne : edges'.Nonempty := G.nonempty.image _
  have hall : ∀ e ∈ edges', isEdge e := by
    intro e he; obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    rcases G.all_edges e' he' with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr ⟨(m.2, m.1), reflA_hEdge m⟩
    · exact Or.inl ⟨(m.2, m.1), reflA_vEdge m⟩
  have heven : ∀ m : ℤ × ℤ, numClosure edges' m ∈ ({0, 2} : Set ℕ) := by
    intro m
    exact (homeo_numClosure reflA_homeomorph G.edges (m.2, m.1) m
      (reflA_pointI (m.2, m.1))) ▸ G.even_degree (m.2, m.1)
  have hconn := image_rectagon_connected reflA (fun hadj => reflA_cellAdj hadj) G
  exact ⟨⟨edges', hne, hall, heven, hconn⟩, Finset.coe_image⟩

/-! ## reflB: Horizontal reflection -/

/-- Horizontal reflection: (x, y) ↦ (-x - 1, y).
    HOL Light: `reflB`. -/
def reflB : E2 → E2 := fun p => point (-(p 0) - 1, p 1)

/-- `reflB` is an involution: applying it twice is the identity. -/
theorem reflB_involutive : Function.Involutive reflB := by
  intro z
  simp only [reflB, point, Fin.isValue, WithLp.equiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_sub, sub_neg_eq_add,
    add_sub_cancel_left]
  ext i; fin_cases i <;> simp

/-- `reflB` is continuous. -/
theorem reflB_continuous : Continuous reflB := by
  unfold reflB
  change Continuous (fun p : E2 => point (-(p 0) - 1, p 1))
  unfold point
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i; fin_cases i
  · exact (PiLp.continuous_apply 2 _ 0).neg.sub continuous_const
  · exact PiLp.continuous_apply 2 _ 1

/-- `reflB` maps lattice points to lattice points. -/
theorem reflB_pointI (m : ℤ × ℤ) :
    reflB (pointI m) = pointI (-m.1 - 1, m.2) := by
  simp [reflB, pointI, point]

/-- `reflB` as a homeomorphism of `E2`, using its involutive and continuous properties. -/
def reflB_homeomorph : E2 ≃ₜ E2 where
  toEquiv := reflB_involutive.toPerm
  continuous_toFun := reflB_continuous
  continuous_invFun := reflB_continuous

/-- `reflB` maps the horizontal edge `hEdge m` to `hEdge (-m.1 - 2, m.2)`. -/
theorem reflB_hEdge (m : ℤ × ℤ) :
    reflB '' (hEdge m) = hEdge (-m.1 - 2, m.2) := by
  ext z; simp only [mem_image, hEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, ?_, h3⟩ <;> push_cast <;> linarith
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflB z, ?_, reflB_involutive z⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, ?_, h3⟩ <;> push_cast at * <;> linarith

/-- `reflB` maps the vertical edge `vEdge m` to `vEdge (-m.1 - 1, m.2)`. -/
theorem reflB_vEdge (m : ℤ × ℤ) :
    reflB '' (vEdge m) = vEdge (-m.1 - 1, m.2) := by
  ext z; simp only [mem_image, vEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, h2, h3⟩; push_cast; linarith
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflB z, ?_, reflB_involutive z⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, h2, h3⟩; push_cast at *; linarith

/-- `reflB` maps the open square `squ m` to `squ (-m.1 - 2, m.2)`. -/
theorem reflB_squ (m : ℤ × ℤ) :
    reflB '' (squ m) = squ (-m.1 - 2, m.2) := by
  ext z; simp only [mem_image, squ, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, ?_, h3, h4⟩ <;> push_cast <;> linarith
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨reflB z, ?_, reflB_involutive z⟩
    simp only [reflB, point_coord_zero, point_coord_one]
    refine ⟨?_, ?_, h3, h4⟩ <;> push_cast at * <;> linarith

/-- `reflB` maps any cell to a cell: it preserves the cell type structure. -/
theorem reflB_cell {C : Set E2} (hC : isCell C) :
    isCell (reflB '' C) := by
  obtain ⟨ct, rfl⟩ := hC
  cases ct with
  | point m => exact ⟨.point (-m.1 - 1, m.2),
      show reflB '' {pointI m} = {pointI (-m.1 - 1, m.2)} by
        rw [image_singleton, reflB_pointI]⟩
  | hEdge m => exact ⟨.hEdge (-m.1 - 2, m.2), reflB_hEdge m⟩
  | vEdge m => exact ⟨.vEdge (-m.1 - 1, m.2), reflB_vEdge m⟩
  | squ m => exact ⟨.squ (-m.1 - 2, m.2), reflB_squ m⟩

/-- `reflB` preserves the rectagon property.
    HOL Light: `reflB_segment`. -/
theorem reflB_rectagon (G : Rectagon) :
    ∃ G' : Rectagon, (↑G'.edges : Set _) = (fun e => reflB '' e) '' ↑G.edges := by
  let edges' := G.edges.image (fun e => reflB '' e)
  have hne : edges'.Nonempty := G.nonempty.image _
  have hall : ∀ e ∈ edges', isEdge e := by
    intro e he; obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    rcases G.all_edges e' he' with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inl ⟨(-m.1 - 2, m.2), reflB_hEdge m⟩
    · exact Or.inr ⟨(-m.1 - 1, m.2), reflB_vEdge m⟩
  have heven : ∀ m : ℤ × ℤ, numClosure edges' m ∈ ({0, 2} : Set ℕ) := by
    intro m
    have hm : reflB_homeomorph (pointI (-m.1 - 1, m.2)) = pointI m := by
      change reflB (pointI (-m.1 - 1, m.2)) = pointI m
      have h := reflB_involutive (pointI m); rw [reflB_pointI] at h; exact h
    exact (homeo_numClosure reflB_homeomorph G.edges (-m.1 - 1, m.2) m hm) ▸
      G.even_degree (-m.1 - 1, m.2)
  have hconn := image_rectagon_connected reflB
    (fun hadj => homeomorph_cellAdj reflB_homeomorph (fun D hD => reflB_cell hD) hadj) G
  exact ⟨⟨edges', hne, hall, heven, hconn⟩, Finset.coe_image⟩

/-! ## reflC: Vertical reflection -/

/-- Vertical reflection: (x, y) ↦ (x, -y - 1).
    HOL Light: `reflC`. -/
def reflC : E2 → E2 := fun p => point (p 0, -(p 1) - 1)

/-- `reflC` is an involution: applying it twice is the identity. -/
theorem reflC_involutive : Function.Involutive reflC := by
  intro z
  simp only [reflC, point, Fin.isValue, WithLp.equiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_sub, sub_neg_eq_add,
    add_sub_cancel_left]
  ext i; fin_cases i <;> simp

/-- `reflC` is continuous. -/
theorem reflC_continuous : Continuous reflC := by
  unfold reflC
  change Continuous (fun p : E2 => point (p 0, -(p 1) - 1))
  unfold point
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i; fin_cases i
  · exact PiLp.continuous_apply 2 _ 0
  · exact (PiLp.continuous_apply 2 _ 1).neg.sub continuous_const

/-- `reflC` maps lattice points to lattice points. -/
theorem reflC_pointI (m : ℤ × ℤ) :
    reflC (pointI m) = pointI (m.1, -m.2 - 1) := by
  simp [reflC, pointI, point]

/-- `reflC` as a homeomorphism of `E2`, using its involutive and continuous properties. -/
def reflC_homeomorph : E2 ≃ₜ E2 where
  toEquiv := reflC_involutive.toPerm
  continuous_toFun := reflC_continuous
  continuous_invFun := reflC_continuous

/-- `reflC` maps the horizontal edge `hEdge m` to `hEdge (m.1, -m.2 - 1)`. -/
theorem reflC_hEdge (m : ℤ × ℤ) :
    reflC '' (hEdge m) = hEdge (m.1, -m.2 - 1) := by
  ext z; simp only [mem_image, hEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, h2, ?_⟩; push_cast; linarith
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflC z, ?_, reflC_involutive z⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, h2, ?_⟩; push_cast at *; linarith

/-- `reflC` maps the vertical edge `vEdge m` to `vEdge (m.1, -m.2 - 2)`. -/
theorem reflC_vEdge (m : ℤ × ℤ) :
    reflC '' (vEdge m) = vEdge (m.1, -m.2 - 2) := by
  ext z; simp only [mem_image, vEdge, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> linarith
  · intro ⟨h1, h2, h3⟩
    refine ⟨reflC z, ?_, reflC_involutive z⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, ?_, ?_⟩ <;> push_cast at * <;> linarith

/-- `reflC` maps the open square `squ m` to `squ (m.1, -m.2 - 2)`. -/
theorem reflC_squ (m : ℤ × ℤ) :
    reflC '' (squ m) = squ (m.1, -m.2 - 2) := by
  ext z; simp only [mem_image, squ, mem_setOf_eq]; constructor
  · rintro ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, h2, ?_, ?_⟩ <;> push_cast <;> linarith
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨reflC z, ?_, reflC_involutive z⟩
    simp only [reflC, point_coord_zero, point_coord_one]
    refine ⟨h1, h2, ?_, ?_⟩ <;> push_cast at * <;> linarith

/-- `reflC` maps any cell to a cell: it preserves the cell type structure. -/
theorem reflC_cell {C : Set E2} (hC : isCell C) :
    isCell (reflC '' C) := by
  obtain ⟨ct, rfl⟩ := hC
  cases ct with
  | point m => exact ⟨.point (m.1, -m.2 - 1),
      show reflC '' {pointI m} = {pointI (m.1, -m.2 - 1)} by
        rw [image_singleton, reflC_pointI]⟩
  | hEdge m => exact ⟨.hEdge (m.1, -m.2 - 1), reflC_hEdge m⟩
  | vEdge m => exact ⟨.vEdge (m.1, -m.2 - 2), reflC_vEdge m⟩
  | squ m => exact ⟨.squ (m.1, -m.2 - 2), reflC_squ m⟩

/-- `reflC` preserves the rectagon property.
    HOL Light: `reflC_segment`. -/
theorem reflC_rectagon (G : Rectagon) :
    ∃ G' : Rectagon, (↑G'.edges : Set _) = (fun e => reflC '' e) '' ↑G.edges := by
  let edges' := G.edges.image (fun e => reflC '' e)
  have hne : edges'.Nonempty := G.nonempty.image _
  have hall : ∀ e ∈ edges', isEdge e := by
    intro e he; obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    rcases G.all_edges e' he' with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inl ⟨(m.1, -m.2 - 1), reflC_hEdge m⟩
    · exact Or.inr ⟨(m.1, -m.2 - 2), reflC_vEdge m⟩
  have heven : ∀ m : ℤ × ℤ, numClosure edges' m ∈ ({0, 2} : Set ℕ) := by
    intro m
    have hm : reflC_homeomorph (pointI (m.1, -m.2 - 1)) = pointI m := by
      change reflC (pointI (m.1, -m.2 - 1)) = pointI m
      have h := reflC_involutive (pointI m); rw [reflC_pointI] at h; exact h
    exact (homeo_numClosure reflC_homeomorph G.edges (m.1, -m.2 - 1) m hm) ▸
      G.even_degree (m.1, -m.2 - 1)
  have hconn := image_rectagon_connected reflC
    (fun hadj => homeomorph_cellAdj reflC_homeomorph (fun D hD => reflC_cell hD) hadj) G
  exact ⟨⟨edges', hne, hall, heven, hconn⟩, Finset.coe_image⟩

/-! ## Composition of reflections -/

/-- `reflA ∘ reflB ∘ reflA = reflC` (up to appropriate index shifts).
    This is used to transfer results between the three reflections. -/
theorem reflA_reflB_reflA_eq_reflC :
    ∀ z : E2, reflA (reflB (reflA z)) = reflC z := by
  intro z
  simp [reflA, reflB, reflC, point]

/-- The group generated by reflA, reflB, reflC acts on cells. -/
theorem refl_group_action (σ : E2 → E2)
    (hσ : σ = reflA ∨ σ = reflB ∨ σ = reflC ∨ σ = reflA ∘ reflB ∨
          σ = reflB ∘ reflA ∨ σ = reflA ∘ reflC ∨ σ = reflC ∘ reflA) :
    ∀ C : Set E2, isCell C → isCell (σ '' C) := by
  intro C hC
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reflA_cell hC
  · exact reflB_cell hC
  · exact reflC_cell hC
  · rw [image_comp]; exact reflA_cell (reflB_cell hC)
  · rw [image_comp]; exact reflB_cell (reflA_cell hC)
  · rw [image_comp]; exact reflA_cell (reflC_cell hC)
  · rw [image_comp]; exact reflC_cell (reflA_cell hC)

end
