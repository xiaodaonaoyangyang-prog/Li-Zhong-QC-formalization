/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification24: pinned classification sources; see BUNDLE_MAP.json. -/
import LiZhongExternal.Classification.SchottkyClassification23
import LiZhongExternal.Classification.SchottkyClassification21
import LiZhongExternal.Classification.SchottkyClassification22

/- BEGIN ClassificationOfSurfaces.FiniteCyclicP2DegenerateRealization | ff01c5f9a7b706ffaa4eb5755e96af54eabfe0aec8fd78603c185791687ac6cc -/
noncomputable section

section schottkyclassification24_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal realization of one-sided-degenerate Gallier--Xu P2

This file lifts the local monogon--polygon disk theorem to finite cyclic presentations.  The
positive base case has an empty left cut word and a nonempty right cut word.  Reversal and child
swap transport that case to every ordinary-valid one-sided-degenerate cut.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

theorem leftLength_eq_zero
    {P : FiniteCyclicPresentation} {cut : P2Cut P}
    (hleft : cut.left = []) :
    cut.left.length = 0 := by
  simp [hleft]

/-- The rotated source side index, specialized to an empty-left cut. -/
noncomputable def rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (_hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    Fin cut.right.length :=
  ⟨(i.val + positiveCutRotation P cut horientation) %
      cut.right.length,
    Nat.mod_lt _ hr⟩

@[simp]
theorem rightDegenerateCutSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr i).val =
      (i.val + positiveCutRotation P cut horientation) %
        cut.right.length :=
  rfl

theorem sourceBoundaryLength_eq_rightLength
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hleft : cut.left = []) :
    (P.boundary cut.face.face).length =
      cut.right.length := by
  rw [sourceBoundaryLength_eq_cutLength P cut,
    hleft]
  simp

theorem rightDegenerateCutSideIndex_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  intro i j hij
  have hmod :
      i.val + positiveCutRotation P cut horientation ≡
        j.val + positiveCutRotation P cut horientation
          [MOD cut.right.length] :=
    congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD cut.right.length] :=
    Nat.ModEq.add_right_cancel'
      (positiveCutRotation P cut horientation) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← sourceBoundaryLength_eq_rightLength P cut hleft,
    Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

theorem rightDegenerateCutSideIndex_surjective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Surjective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  exact ((Fintype.bijective_iff_injective_and_card
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr)).2
      ⟨rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr,
        by
          simp only [Fintype.card_fin]
          exact sourceBoundaryLength_eq_rightLength
            P cut hleft⟩).2

theorem right_get_rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    cut.right[
        (rightDegenerateCutSideIndex
          P cut horientation hleft hr i).val] =
      (P.boundary cut.face.face)[i.val] := by
  -- Use the rotation lookup directly, with the empty append simplified.
  have hiCut :
      i.val < (cut.left ++ cut.right).length := by
    rw [hleft, List.nil_append,
      ← sourceBoundaryLength_eq_rightLength P cut hleft]
    exact i.isLt
  have hpoint :=
    congrArg (fun word => word[i.val]?)
      (rotate_cutBoundary_eq_sourceBoundary
        P cut horientation)
  rw [List.getElem?_rotate hiCut] at hpoint
  rw [hleft, List.nil_append] at hpoint
  rw [List.getElem?_eq_getElem
      (Nat.mod_lt _ hr),
    List.getElem?_eq_getElem i.isLt] at hpoint
  exact Option.some.inj (by
    simpa [rightDegenerateCutSideIndex] using hpoint)

/-- Phantom transport from the literal monogon to a selected child whose old-side count is
propositionally zero. -/
noncomputable def zeroLeftCellHomeomorph
    {l : ℕ} (hl : l = 0) :
    PolygonCell 1 ≃ₜ PolygonCell (l + 1) :=
  PolygonCell.rotateHomeomorph (by omega) 0

theorem zeroLeftCellHomeomorph_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    zeroLeftCellHomeomorph hl
        (PolygonCell.side (0 : Fin 1) t) =
      PolygonCell.side (Fin.last l) t := by
  rw [zeroLeftCellHomeomorph]
  have hpos : 0 < l + 1 := by omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (by omega) hpos 0 (0 : Fin 1) t]
  congr 2
  apply Fin.ext
  simp [hl]

/-- The `zeroLeftChildPairHomeomorph` declaration. -/
noncomputable def zeroLeftChildPairHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ChildPair 0 r ≃ₜ
      DiskSquare.ChildPair l r :=
  Homeomorph.sumCongr
    (zeroLeftCellHomeomorph hl)
    (Homeomorph.refl (PolygonCell (r + 1)))

theorem zeroLeftChildPair_generator_map
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator l r
      (zeroLeftChildPairHomeomorph hl x)
      (zeroLeftChildPairHomeomorph hl y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator l r
          (.inl
            (zeroLeftCellHomeomorph hl
              (PolygonCell.side (0 : Fin 1) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftCellHomeomorph_symm_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    (zeroLeftCellHomeomorph hl).symm
        (PolygonCell.side (Fin.last l) t) =
      PolygonCell.side (0 : Fin 1) t := by
  apply (zeroLeftCellHomeomorph hl).injective
  rw [Homeomorph.apply_symm_apply,
    zeroLeftCellHomeomorph_side]

theorem zeroLeftChildPair_generator_comap
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair l r}
    (hxy : DiskSquare.ParamChildSeamGenerator l r x y) :
    DiskSquare.ParamChildSeamGenerator 0 r
      ((zeroLeftChildPairHomeomorph hl).symm x)
      ((zeroLeftChildPairHomeomorph hl).symm y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 r
          (.inl
            ((zeroLeftCellHomeomorph hl).symm
              (PolygonCell.side (Fin.last l) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_symm_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftChildPair_eqvGen_iff
    {l r : ℕ} (hl : l = 0)
    (x y : DiskSquare.ChildPair 0 r) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 r) x y ↔
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator l r)
        (zeroLeftChildPairHomeomorph hl x)
        (zeroLeftChildPairHomeomorph hl y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (zeroLeftChildPair_generator_map hl h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e :
        DiskSquare.ChildPair 0 r ≃ₜ
          DiskSquare.ChildPair l r :=
      zeroLeftChildPairHomeomorph hl
    have hcomap :
        ∀ {u v : DiskSquare.ChildPair l r},
          Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator l r) u v →
            Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 r)
              (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          exact Relation.EqvGen.rel _ _
            (zeroLeftChildPair_generator_comap hl h)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using
      hcomap hxy

/-- The `zeroLeftChildGluingHomeomorph` declaration. -/
noncomputable def zeroLeftChildGluingHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ParamChildGluing 0 r ≃ₜ
      DiskSquare.ParamChildGluing l r :=
  Homeomorph.Quotient.congr
    (zeroLeftChildPairHomeomorph hl)
    (zeroLeftChildPair_eqvGen_iff hl)

@[simp]
theorem zeroLeftChildGluingHomeomorph_mk_inr
    {l r : ℕ} (hl : l = 0)
    (z : PolygonCell (r + 1)) :
    zeroLeftChildGluingHomeomorph hl
        (@Quotient.mk''
          (DiskSquare.ChildPair 0 r)
          (DiskSquare.paramChildSeamSetoid 0 r)
          (.inr z)) =
      @Quotient.mk''
        (DiskSquare.ChildPair l r)
        (DiskSquare.paramChildSeamSetoid l r)
        (.inr z) :=
  rfl

/-- The selected source cell, cyclically aligned and then cut by the local degenerate disk
homeomorphism. -/
noncomputable def rightDegenerateSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
    (sourceBoundaryLength_eq_rightLength P cut hleft)
    (positiveCutRotation P cut horientation)).trans
    ((P2DegenerateDisk.sourceChildGluingHomeomorph
      cut.right.length hr).trans
      (zeroLeftChildGluingHomeomorph
        (leftLength_eq_zero hleft)))

theorem rightDegenerateSelectedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedCellHomeomorph
        P cut horientation hleft hr
        (PolygonCell.side i t) =
      @Quotient.mk''
        (DiskSquare.ChildPair
          cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid
          cut.left.length cut.right.length)
        (.inr
          (PolygonCell.side
            ((rightDegenerateCutSideIndex
              P cut horientation hleft hr i).addNat 1) t)) := by
  have hrotate :=
    PolygonCell.rotateHomeomorph_side_of_eq
      (sourceBoundaryLength_eq_rightLength P cut hleft)
      hr
      (positiveCutRotation P cut horientation) i t
  rw [rightDegenerateSelectedCellHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    hrotate,
    P2DegenerateDisk.sourceChildGluingHomeomorph_side,
    zeroLeftChildGluingHomeomorph_mk_inr]
  congr 3

/-- Cut the selected source face and include its local child quotient in the complete split
realization. -/
noncomputable def rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary cut.face.face).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  positiveChildGluingMap P cut horientation validP ∘
    rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr

theorem continuous_rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_positiveChildGluingMap
      P cut horientation validP).comp
    (rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr).continuous

theorem rightDegenerateSelectedFaceMap_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegenerateSelectedFaceMap,
    Function.comp_apply,
    rightDegenerateSelectedCellHomeomorph_side,
    positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]

/-- Facewise forward map for an empty-left positive cut. -/
noncomputable def rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP
  · exact retainedFaceMap P cut hface validP

theorem continuous_rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (rightDegenerateFaceMap
      P cut horientation hleft hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [rightDegenerateFaceMap] using
      continuous_rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
  · simpa [rightDegenerateFaceMap, hface] using
      continuous_retainedFaceMap P cut hface validP

/-- The `rightDegeneratePreMap` declaration. -/
noncomputable def rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  fun x => rightDegenerateFaceMap
    P cut horientation hleft hr validP x.1 x.2

theorem continuous_rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegeneratePreMap
      P cut horientation hleft hr validP) := by
  apply continuous_sigma
  exact continuous_rightDegenerateFaceMap
    P cut horientation hleft hr validP

@[simp]
theorem rightDegeneratePreMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, z⟩ =
      rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP z := by
  simp [rightDegeneratePreMap, rightDegenerateFaceMap]

@[simp]
theorem rightDegeneratePreMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP ⟨f, z⟩ =
      retainedFaceMap P cut hface validP z := by
  simp [rightDegeneratePreMap,
    rightDegenerateFaceMap, hface]

theorem rightDegeneratePreMap_selected_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegeneratePreMap_selected,
    rightDegenerateSelectedFaceMap_side]

theorem rightDegeneratePreMap_retained_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨f, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut f,
          PolygonCell.side
            (retainedSideIndex P cut hface i) t⟩ := by
  rw [rightDegeneratePreMap_retained
      P cut horientation hleft hr validP hface,
    retainedFaceMap, retainedCellHomeomorph_side]

/-- Route every old source occurrence to the target occurrence carrying it after the split. -/
noncomputable def rightDegenerateMapOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (split P cut).BoundaryOccurrence := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    exact
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩
  · exact
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩

@[simp]
theorem rightDegenerateMapOccurrence_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr
        ⟨cut.face.face, i⟩ =
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩ := by
  simp [rightDegenerateMapOccurrence]

@[simp]
theorem rightDegenerateMapOccurrence_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr ⟨f, i⟩ =
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩ := by
  simp [rightDegenerateMapOccurrence, hface]

theorem rightDegeneratePreMap_occurrenceSide
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ((P.occurrenceSide o).point t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        (((split P cut).occurrenceSide
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr o)).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_selected_side
      P cut horientation hleft hr validP i t using 1 <;> rfl
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_retained_side
      P cut horientation hleft hr validP hface i t using 1 <;> rfl

theorem rightDegenerateMapOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).dart =
      P1.castSuccDart o.dart := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq (split_boundary_right P cut)]
    change
      (rightBoundary P cut).get
          ⟨(rightDegenerateCutSideIndex
              P cut horientation hleft hr i).val + 1,
            by
              rw [rightBoundary_of_orientation_false
                P cut horientation]
              simp only [rightDegenerateCutSideIndex_val, retainWord, List.length_cons,
                List.length_map, Order.lt_add_one_iff, Order.add_one_le_iff]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt⟩ =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.get_of_eq
      (rightBoundary_of_orientation_false
        P cut horientation)]
    change
      (.neg (freshEdge P) :: retainWord cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val + 1]'(by
              simp only [rightDegenerateCutSideIndex_val, retainWord, List.length_cons,
                List.length_map, Order.lt_add_one_iff, Order.add_one_le_iff]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt) =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_cons_succ]
    change
      (List.map P1.castSuccDart cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val] =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_map]
    exact congrArg P1.castSuccDart
      (right_get_rightDegenerateCutSideIndex
        P cut horientation hleft hr i)
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq
      (split_boundary_old_of_ne P cut hface)]
    change
      (List.map P1.castSuccDart
        (P.boundary f))[i.val] =
          P1.castSuccDart
            ((P.boundary f)[i.val])
    rw [List.getElem_map]

@[simp]
theorem rightDegenerateMapOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).edge =
      o.edge.castSucc := by
  rw [BoundaryOccurrence.edge,
    rightDegenerateMapOccurrence_dart]
  exact P1.edgeOfDart_castSuccDart o.dart

theorem rightDegenerateMapOccurrence_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateMapOccurrence
        P cut horientation hleft hr) := by
  classical
  rintro ⟨f, i⟩ ⟨g, j⟩ hmap
  by_cases hf : f = cut.face.face
  · subst f
    by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_selected] at hmap
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hindex :
          rightDegenerateCutSideIndex
              P cut horientation hleft hr i =
            rightDegenerateCutSideIndex
              P cut horientation hleft hr j := by
        apply Fin.ext
        simpa [positiveRightChildSideIndex] using hval
      have hij :=
        rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr hindex
      subst j
      rfl
    · rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      exact (oldFace_ne_rightFace P cut g
        (congrArg Sigma.fst hmap).symm).elim
  · by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_selected] at hmap
      exact (oldFace_ne_rightFace P cut f
        (congrArg Sigma.fst hmap)).elim
    · rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      have hface : f = g :=
        oldFace_injective P cut
          (congrArg Sigma.fst hmap)
      subst g
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hij : i = j := by
        apply Fin.ext
        simpa [retainedSideIndex] using hval
      subst j
      rfl

/-- The `rightDegenerateMapPairing` declaration. -/
noncomputable def rightDegenerateMapPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (split P cut).BoundaryPairing where
  source :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.source
  target :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.target
  source_ne_target := by
    intro h
    exact pairing.source_ne_target
      (rightDegenerateMapOccurrence_injective
        P cut horientation hleft hr h)
  source_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.source_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  target_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.target_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction with
    | same =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        exact congrArg P1.castSuccDart hcompatible
    | opposite =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart.flip
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        change
          P1.castSuccDart pairing.target.dart =
            (P1.castSuccDart pairing.source.dart).flip
        rw [← P2.castSuccDart_flip]
        exact congrArg P1.castSuccDart hcompatible

theorem rightDegeneratePreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.source.point t) =
      rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.target.point
          (pairing.identification.parameter t)) := by
  rw [BoundaryPairing.identification_source,
    BoundaryPairing.identification_target,
    rightDegeneratePreMap_occurrenceSide,
    rightDegeneratePreMap_occurrenceSide]
  simpa [rightDegenerateMapPairing,
      PolygonGluing.Identification.parameter] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (rightDegenerateMapPairing
        P cut horientation hleft hr pairing) t

theorem rightDegeneratePreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP x =
      rightDegeneratePreMap
        P cut horientation hleft hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact rightDegeneratePreMap_pairing_eq
            P cut horientation hleft hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-! ### Inverse map -/

/-- Collapse the local child quotient back to the selected source face. -/
noncomputable def rightDegenerateChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ParamChildGluing cut.left.length cut.right.length →
      P.PolygonalRealization validP :=
  fun q =>
    P.polygonalMk validP
      ⟨cut.face.face,
        (rightDegenerateSelectedCellHomeomorph
          P cut horientation hleft hr).symm q⟩

theorem continuous_rightDegenerateChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP) :=
  (P.continuous_polygonalMk validP).comp
    (continuous_sigmaMk.comp
      (rightDegenerateSelectedCellHomeomorph
        P cut horientation hleft hr).symm.continuous)

@[simp]
theorem rightDegenerateChildGluingInvMap_selectedCell
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (rightDegenerateSelectedCellHomeomorph
          P cut horientation hleft hr z) =
      P.polygonalMk validP ⟨cut.face.face, z⟩ := by
  simp [rightDegenerateChildGluingInvMap]

/-- Inverse map on the selected target child. -/
noncomputable def rightDegenerateSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length →
      P.PolygonalRealization validP :=
  rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP ∘
    positiveSelectedChildToGluing P cut horientation

theorem continuous_rightDegenerateSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateSelectedChildInvFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP).comp
    (continuous_positiveSelectedChildToGluing
      P cut horientation)

/-- Inverse map on the right target child. -/
noncomputable def rightDegenerateRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary (rightFace P cut)).length →
      P.PolygonalRealization validP :=
  rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP ∘
    positiveRightChildToGluing P cut horientation

theorem continuous_rightDegenerateRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateRightChildInvFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP).comp
    (continuous_positiveRightChildToGluing
      P cut horientation)

/-- Inverse map at an old target-face position. -/
noncomputable def rightDegenerateOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell
        ((split P cut).boundary (oldFace P cut f)).length →
      P.PolygonalRealization validP := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact rightDegenerateSelectedChildInvFaceMap
      P cut horientation hleft hr validP
  · exact retainedInvFaceMap P cut hface validP

theorem continuous_rightDegenerateOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (rightDegenerateOldInvFaceMap
      P cut horientation hleft hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [rightDegenerateOldInvFaceMap] using
      continuous_rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP
  · simpa [rightDegenerateOldInvFaceMap, hface] using
      continuous_retainedInvFaceMap P cut hface validP

/-- Inverse face map indexed before applying the target `faceEquiv`. -/
noncomputable def rightDegenerateIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    PolygonCell
        ((split P cut).boundary (faceEquiv P cut j)).length →
      P.PolygonalRealization validP :=
  Fin.lastCases
    (rightDegenerateRightChildInvFaceMap
      P cut horientation hleft hr validP)
    (fun f =>
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f)
    j

@[simp]
theorem rightDegenerateIndexedInvFaceMap_last
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateIndexedInvFaceMap
        P cut horientation hleft hr validP (Fin.last P.faces.length) =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP :=
  Fin.lastCases_last

@[simp]
theorem rightDegenerateIndexedInvFaceMap_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    rightDegenerateIndexedInvFaceMap
        P cut horientation hleft hr validP f.castSucc =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f :=
  Fin.lastCases_castSucc f

theorem continuous_rightDegenerateIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    Continuous (rightDegenerateIndexedInvFaceMap
      P cut horientation hleft hr validP j) := by
  induction j using Fin.lastCases with
  | last =>
      rw [rightDegenerateIndexedInvFaceMap_last]
      exact continuous_rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP
  | cast f =>
      rw [rightDegenerateIndexedInvFaceMap_castSucc]
      exact continuous_rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f

/-- Inverse face map on the actual target face type. -/
noncomputable def rightDegenerateInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    PolygonCell ((split P cut).boundary q).length →
      P.PolygonalRealization validP := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  exact hq ▸ rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j

theorem continuous_rightDegenerateInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    Continuous (rightDegenerateInvFaceMap
      P cut horientation hleft hr validP q) := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  change Continuous (hq ▸ rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j)
  cases hq
  exact continuous_rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j

@[simp]
theorem rightDegenerateInvFaceMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    rightDegenerateInvFaceMap P cut horientation hleft hr validP
        (oldFace P cut f) =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f := by
  unfold rightDegenerateInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (oldFace P cut f) = f.castSucc :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact rightDegenerateIndexedInvFaceMap_castSucc
    P cut horientation hleft hr validP f

@[simp]
theorem rightDegenerateInvFaceMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateInvFaceMap P cut horientation hleft hr validP
        (rightFace P cut) =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP := by
  unfold rightDegenerateInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (rightFace P cut) =
        Fin.last P.faces.length :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact rightDegenerateIndexedInvFaceMap_last
    P cut horientation hleft hr validP

/-- Continuous inverse map on the complete split polygonal pre-realization. -/
noncomputable def rightDegenerateInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalPreRealization →
      P.PolygonalRealization validP :=
  fun x => rightDegenerateInvFaceMap
    P cut horientation hleft hr validP x.1 x.2

theorem continuous_rightDegenerateInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateInvPreMap
      P cut horientation hleft hr validP) := by
  apply continuous_sigma
  exact continuous_rightDegenerateInvFaceMap
    P cut horientation hleft hr validP

@[simp]
theorem rightDegenerateInvPreMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (z : PolygonCell
      ((split P cut).boundary (oldFace P cut f)).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut f, z⟩ =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f z := by
  simp [rightDegenerateInvPreMap]

@[simp]
theorem rightDegenerateInvPreMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell
      ((split P cut).boundary (rightFace P cut)).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut, z⟩ =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP z := by
  simp [rightDegenerateInvPreMap]

@[simp]
theorem rightDegenerateOldInvFaceMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP cut.face.face =
      rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP := by
  simp [rightDegenerateOldInvFaceMap]

@[simp]
theorem rightDegenerateOldInvFaceMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f =
      retainedInvFaceMap P cut hface validP := by
  simp [rightDegenerateOldInvFaceMap, hface]

@[simp]
theorem rightDegenerateSelectedChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP
        (positiveSelectedChildCellHomeomorph
          P cut horientation z) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  simp [rightDegenerateSelectedChildInvFaceMap, Function.comp_apply]

@[simp]
theorem rightDegenerateRightChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP
        (positiveRightChildCellHomeomorph
          P cut horientation z) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  simp [rightDegenerateRightChildInvFaceMap, Function.comp_apply]

theorem rightDegenerateInvPreMap_retained_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut f,
          retainedCellHomeomorph P cut hface z⟩ =
      P.polygonalMk validP ⟨f, z⟩ := by
  rw [rightDegenerateInvPreMap_oldFace,
    rightDegenerateOldInvFaceMap_retained
      P cut horientation hleft hr validP hface,
    retainedInvFaceMap_apply]

theorem rightDegenerateInvPreMap_selectedChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph
            P cut horientation z⟩ =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  rw [rightDegenerateInvPreMap_oldFace,
    rightDegenerateOldInvFaceMap_selected,
    rightDegenerateSelectedChildInvFaceMap_apply]

theorem rightDegenerateInvPreMap_rightChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph
            P cut horientation z⟩ =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  rw [rightDegenerateInvPreMap_rightFace,
    rightDegenerateRightChildInvFaceMap_apply]

/-- The inverse pre-map identifies the fresh target seam. -/
theorem rightDegenerateInvPreMap_fresh_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph P cut horientation
            (PolygonCell.side (Fin.last cut.left.length) t)⟩ =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph P cut horientation
            (PolygonCell.side (0 : Fin (cut.right.length + 1))
              (unitInterval.symm t))⟩ := by
  rw [rightDegenerateInvPreMap_selectedChild_apply,
    rightDegenerateInvPreMap_rightChild_apply]
  apply congrArg
    (rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP)
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (DiskSquare.ParamChildSeamGenerator.glue t)

/-- On every old boundary side, the inverse pre-map exactly undoes occurrence transport. -/
theorem rightDegenerateInvPreMap_mapOccurrence_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr o)).point t) =
      P.polygonalMk validP ((P.occurrenceSide o).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected]
    change
      rightDegenerateInvPreMap P cut horientation hleft hr validP
          ⟨rightFace P cut,
            PolygonCell.side
              (positiveRightChildSideIndex P cut horientation
                ((rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).addNat 1)) t⟩ =
        P.polygonalMk validP
          ⟨cut.face.face, PolygonCell.side i t⟩
    rw [← positiveRightChildCellHomeomorph_side
        P cut horientation
        ((rightDegenerateCutSideIndex
          P cut horientation hleft hr i).addNat 1) t,
      rightDegenerateInvPreMap_rightChild_apply,
      ← rightDegenerateSelectedCellHomeomorph_side
        P cut horientation hleft hr i t,
      rightDegenerateChildGluingInvMap_selectedCell]
  · rw [rightDegenerateMapOccurrence_retained
        P cut horientation hleft hr hface i]
    change
      rightDegenerateInvPreMap P cut horientation hleft hr validP
          ⟨oldFace P cut f,
            PolygonCell.side (retainedSideIndex P cut hface i) t⟩ =
        P.polygonalMk validP ⟨f, PolygonCell.side i t⟩
    rw [← retainedCellHomeomorph_side P cut hface i t,
      rightDegenerateInvPreMap_retained_apply]

/-- Every target occurrence on an old edge is the transported copy of a source occurrence.
The selected monogon and index zero of the right child are exactly the fresh seam. -/
theorem exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (q : (split P cut).BoundaryOccurrence) (e : P.Edge)
    (hedge : q.edge = e.castSucc) :
    ∃ o : P.BoundaryOccurrence,
      rightDegenerateMapOccurrence
        P cut horientation hleft hr o = q := by
  classical
  rcases q with ⟨qf, j⟩
  rcases face_cases P cut qf with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      have hjval : j.val = cut.left.length := by
        have hlen :=
          positive_split_boundary_selected_length
            P cut horientation
        have hjlt := j.isLt
        have hzero := leftLength_eq_zero hleft
        omega
      have hqfresh :
          (show (split P cut).BoundaryOccurrence from
            ⟨oldFace P cut cut.face.face, j⟩) =
            positiveSelectedFreshOccurrence
              P cut horientation := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact hjval
      have hqedge := congrArg BoundaryOccurrence.edge hqfresh
      rw [positiveSelectedFreshOccurrence_edge] at hqedge
      have hbad : e.castSucc = freshEdge P :=
        hedge.symm.trans hqedge
      exact (P1.firstSubedge_ne_freshEdge e hbad).elim
    · let i : Fin (P.boundary f).length :=
        ⟨j.val, by
          rw [← split_boundary_old_length_of_ne P cut hface]
          exact j.isLt⟩
      refine ⟨⟨f, i⟩, ?_⟩
      rw [rightDegenerateMapOccurrence_retained
        P cut horientation hleft hr hface i]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        rfl
  · by_cases hj : j.val = 0
    · have hqfresh :
          (show (split P cut).BoundaryOccurrence from
            ⟨rightFace P cut, j⟩) =
            positiveRightFreshOccurrence P cut horientation := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact hj
      have hqedge := congrArg BoundaryOccurrence.edge hqfresh
      rw [positiveRightFreshOccurrence_edge] at hqedge
      have hbad : e.castSucc = freshEdge P :=
        hedge.symm.trans hqedge
      exact (P1.firstSubedge_ne_freshEdge e hbad).elim
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
      let rightIndex : Fin cut.right.length :=
        ⟨j.val - 1, by
          have hlen :=
            positive_split_boundary_right_length
              P cut horientation
          have hjlt := j.isLt
          omega⟩
      obtain ⟨i, hi⟩ :=
        rightDegenerateCutSideIndex_surjective
          P cut horientation hleft hr rightIndex
      refine ⟨⟨cut.face.face, i⟩, ?_⟩
      rw [rightDegenerateMapOccurrence_selected]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        simp only [positiveRightChildSideIndex,
          Fin.val_addNat]
        rw [hi]
        simp only [rightIndex]
        omega

/-- A target pairing based at an old edge is exactly the transported source pairing. -/
theorem exists_rightDegenerateMapPairing_eq_of_source_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (e : P.Edge)
    (hsourceEdge : q.source.edge = e.castSucc) :
    ∃ r : P.BoundaryPairing,
      rightDegenerateMapPairing
        P cut horientation hleft hr r = q := by
  have htargetEdge : q.target.edge = e.castSucc :=
    (targetPairing_edge_eq_source_edge q).trans hsourceEdge
  obtain ⟨source, hsource⟩ :=
    exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
      P cut horientation hleft hr q.source e hsourceEdge
  obtain ⟨target, htarget⟩ :=
    exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
      P cut horientation hleft hr q.target e htargetEdge
  have hsourceOldEdge : source.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge hsource
    rw [rightDegenerateMapOccurrence_edge, hsourceEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have htargetOldEdge : target.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge htarget
    rw [rightDegenerateMapOccurrence_edge, htargetEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have heInternal : ¬P.IsBoundaryEdge e := by
    intro heBoundary
    apply q.source_not_boundary
    unfold IsBoundaryEdge at heBoundary ⊢
    rw [hsourceEdge]
    exact
      (edgeMultiplicity_split_castSucc P cut e).symm.trans
        heBoundary
  have hsourceInternal : ¬P.IsBoundaryEdge source.edge := by
    rw [hsourceOldEdge]
    exact heInternal
  obtain ⟨r, hrsource⟩ :=
    validP.exists_pairing_source source hsourceInternal
  obtain ⟨_partner, _hpartner, hunique⟩ :=
    validP.exists_unique_partner source hsourceInternal
  have hsourceneTarget : source ≠ target := by
    intro heq
    apply q.source_ne_target
    calc
      q.source =
          rightDegenerateMapOccurrence
            P cut horientation hleft hr source :=
        hsource.symm
      _ = rightDegenerateMapOccurrence
            P cut horientation hleft hr target :=
        congrArg
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr) heq
      _ = q.target := htarget
  have hrcondition :
      source ≠ r.target ∧ r.target.edge = source.edge := by
    constructor
    · intro heq
      exact r.source_ne_target (hrsource.trans heq)
    · calc
        r.target.edge = r.source.edge :=
          targetPairing_edge_eq_source_edge r
        _ = source.edge :=
          congrArg BoundaryOccurrence.edge hrsource
  have htcondition :
      source ≠ target ∧ target.edge = source.edge :=
    ⟨hsourceneTarget,
      htargetOldEdge.trans hsourceOldEdge.symm⟩
  have hrtarget : r.target = target :=
    (hunique r.target hrcondition).trans
      (hunique target htcondition).symm
  have hmapSource :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).source = q.source := by
    change
      rightDegenerateMapOccurrence
          P cut horientation hleft hr r.source = q.source
    rw [hrsource, hsource]
  have hmapTarget :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).target = q.target := by
    change
      rightDegenerateMapOccurrence
          P cut horientation hleft hr r.target = q.target
    rw [hrtarget, htarget]
  have hmapDirection :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).direction = q.direction :=
    targetPairing_direction_eq_of_source_target_eq
      (rightDegenerateMapPairing
        P cut horientation hleft hr r) q
      hmapSource hmapTarget
  exact ⟨r,
    targetPairing_eq_of_source_target_direction_eq
      (rightDegenerateMapPairing
        P cut horientation hleft hr r) q
      hmapSource hmapTarget hmapDirection⟩

/-- Occurrence-side form of the exact fresh-seam equality. -/
theorem rightDegenerateInvPreMap_fresh_occurrence_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (positiveSelectedFreshOccurrence
            P cut horientation)).point t) =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (positiveRightFreshOccurrence
            P cut horientation)).point
              (unitInterval.symm t)) := by
  rw [← positiveChildPairPreMap_fresh_inl
      P cut horientation t,
    ← positiveChildPairPreMap_fresh_inr
      P cut horientation (unitInterval.symm t)]
  exact rightDegenerateInvPreMap_fresh_seam
    P cut horientation hleft hr validP t

/-- The inverse pre-map identifies every target gluing generator. -/
theorem rightDegenerateInvPreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (q.identification.source.point t) =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        (q.identification.target.point
          (q.identification.parameter t)) := by
  let edge : Fin (P.edgeCount + 1) := q.source.edge
  have hsourceEdge : q.source.edge = edge := rfl
  refine Fin.lastCases
    (motive := fun edge : Fin (P.edgeCount + 1) =>
      q.source.edge = edge →
        rightDegenerateInvPreMap
            P cut horientation hleft hr validP
            (q.identification.source.point t) =
          rightDegenerateInvPreMap
            P cut horientation hleft hr validP
            (q.identification.target.point
              (q.identification.parameter t)))
    ?_ (fun e hedge ↦ ?_) edge hsourceEdge
  · intro hedge
    have hfresh : q.source.edge = freshEdge P := by
      simpa only [freshEdge, P1.freshEdge] using hedge
    have htargetFresh : q.target.edge = freshEdge P :=
      (targetPairing_edge_eq_source_edge q).trans hfresh
    rcases positiveFreshOccurrence_cases
        P cut horientation validP q.source hfresh with
      hsourceSelected | hsourceRight
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · exact (q.source_ne_target
          (hsourceSelected.trans htargetSelected.symm)).elim
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceSelected, htargetRight,
                positiveRightFreshOccurrence_dart,
                positiveSelectedFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceSelected, htargetRight, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          rightDegenerateInvPreMap_fresh_occurrence_seam
            P cut horientation hleft hr validP t
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceRight, htargetSelected,
                positiveSelectedFreshOccurrence_dart,
                positiveRightFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceRight, htargetSelected, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          (rightDegenerateInvPreMap_fresh_occurrence_seam
            P cut horientation hleft hr validP
            (unitInterval.symm t)).symm
      · exact (q.source_ne_target
          (hsourceRight.trans htargetRight.symm)).elim
  · obtain ⟨r, hrPairing⟩ :=
      exists_rightDegenerateMapPairing_eq_of_source_edge_castSucc
        P cut horientation hleft hr validP q e hedge
    rw [← hrPairing, BoundaryPairing.identification_source,
      BoundaryPairing.identification_target]
    change
      rightDegenerateInvPreMap
          P cut horientation hleft hr validP
          (((split P cut).occurrenceSide
            (rightDegenerateMapOccurrence
              P cut horientation hleft hr r.source)).point t) =
        rightDegenerateInvPreMap
          P cut horientation hleft hr validP
          (((split P cut).occurrenceSide
            (rightDegenerateMapOccurrence
              P cut horientation hleft hr r.target)).point
            ((rightDegenerateMapPairing
              P cut horientation hleft hr r).identification.parameter t))
    rw [rightDegenerateInvPreMap_mapOccurrence_side,
      rightDegenerateInvPreMap_mapOccurrence_side]
    simpa [rightDegenerateMapPairing,
        PolygonGluing.Identification.parameter] using
      P.polygonalMk_pairing_eq validP r t

/-- The inverse pre-map is constant on the complete target gluing relation. -/
theorem rightDegenerateInvPreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : (split P cut).PolygonalPreRealization}
    (hxy :
      (split P cut).PolygonalGluingRel
        (split_isSurfaceValid P cut validP) x y) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP x =
      rightDegenerateInvPreMap
        P cut horientation hleft hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((split P cut).polygonalIdentifications
        (split_isSurfaceValid P cut validP))) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact rightDegenerateInvPreMap_pairing_eq
            P cut horientation hleft hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Descended equivalence -/

/-- Forward map after descent through the source polygonal quotient. -/
noncomputable def rightDegenerateRealizationMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  Quotient.lift
    (rightDegeneratePreMap
      P cut horientation hleft hr validP)
    (fun _ _ hxy =>
      rightDegeneratePreMap_respects
        P cut horientation hleft hr validP hxy)

/-- Inverse map after descent through the target polygonal quotient. -/
noncomputable def rightDegenerateRealizationInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) →
      P.PolygonalRealization validP :=
  Quotient.lift
    (rightDegenerateInvPreMap
      P cut horientation hleft hr validP)
    (fun _ _ hxy =>
      rightDegenerateInvPreMap_respects
        P cut horientation hleft hr validP hxy)

@[simp]
theorem rightDegenerateRealizationMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (P.polygonalMk validP x) =
      rightDegeneratePreMap
        P cut horientation hleft hr validP x :=
  rfl

@[simp]
theorem rightDegenerateRealizationInvMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        ((split P cut).polygonalMk
          (split_isSurfaceValid P cut validP) y) =
      rightDegenerateInvPreMap
        P cut horientation hleft hr validP y :=
  rfl

/-- On the locally glued child pair, the descended inverse is the explicit collapse map. -/
theorem rightDegenerateRealizationInvMap_childGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        (positiveChildGluingMap
          P cut horientation validP q) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP q := by
  induction q using Quotient.inductionOn'
  case _ x =>
    cases x with
    | inl z =>
        rw [positiveChildGluingMap_mk]
        change
          rightDegenerateInvPreMap
              P cut horientation hleft hr validP
              ⟨oldFace P cut cut.face.face,
                positiveSelectedChildCellHomeomorph
                  P cut horientation z⟩ =
            rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inl z))
        exact rightDegenerateInvPreMap_selectedChild_apply
          P cut horientation hleft hr validP z
    | inr z =>
        rw [positiveChildGluingMap_mk]
        change
          rightDegenerateInvPreMap
              P cut horientation hleft hr validP
              ⟨rightFace P cut,
                positiveRightChildCellHomeomorph
                  P cut horientation z⟩ =
            rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inr z))
        exact rightDegenerateInvPreMap_rightChild_apply
          P cut horientation hleft hr validP z

/-- The descended forward map sends the child-collapse class back to the same local quotient. -/
theorem rightDegenerateRealizationMap_childGluingInv
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (rightDegenerateChildGluingInvMap
          P cut horientation hleft hr validP q) =
      positiveChildGluingMap P cut horientation validP q := by
  rw [rightDegenerateChildGluingInvMap,
    rightDegenerateRealizationMap_polygonalMk,
    rightDegeneratePreMap_selected]
  simp [rightDegenerateSelectedFaceMap, Function.comp_apply]

/-- The descended inverse is a left inverse on every source pre-realization point. -/
theorem rightDegenerateRealization_left_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        (rightDegeneratePreMap
          P cut horientation hleft hr validP x) =
      P.polygonalMk validP x := by
  rcases x with ⟨f, z⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegeneratePreMap_selected]
    change
      rightDegenerateRealizationInvMap
          P cut horientation hleft hr validP
          (positiveChildGluingMap P cut horientation validP
            (rightDegenerateSelectedCellHomeomorph
              P cut horientation hleft hr z)) =
        P.polygonalMk validP ⟨cut.face.face, z⟩
    rw [rightDegenerateRealizationInvMap_childGluing,
      rightDegenerateChildGluingInvMap_selectedCell]
  · rw [rightDegeneratePreMap_retained
        P cut horientation hleft hr validP hface,
      retainedFaceMap,
      rightDegenerateRealizationInvMap_polygonalMk,
      rightDegenerateInvPreMap_retained_apply]

/-- The descended forward map is a right inverse on every target pre-realization point. -/
theorem rightDegenerateRealization_right_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (rightDegenerateInvPreMap
          P cut horientation hleft hr validP y) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP) y := by
  rcases y with ⟨q, z⟩
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      rw [rightDegenerateInvPreMap_oldFace,
        rightDegenerateOldInvFaceMap_selected]
      change
        rightDegenerateRealizationMap
            P cut horientation hleft hr validP
            (rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (positiveSelectedChildToGluing
                P cut horientation z)) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut cut.face.face, z⟩
      rw [rightDegenerateRealizationMap_childGluingInv,
        positiveChildGluingMap_selectedChildToGluing]
    · rw [rightDegenerateInvPreMap_oldFace,
        rightDegenerateOldInvFaceMap_retained
          P cut horientation hleft hr validP hface]
      change
        rightDegenerateRealizationMap
            P cut horientation hleft hr validP
            (P.polygonalMk validP
              ⟨f, (retainedCellHomeomorph
                P cut hface).symm z⟩) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut f, z⟩
      rw [rightDegenerateRealizationMap_polygonalMk,
        rightDegeneratePreMap_retained
          P cut horientation hleft hr validP hface,
        retainedFaceMap]
      simp
  · rw [rightDegenerateInvPreMap_rightFace]
    change
      rightDegenerateRealizationMap
          P cut horientation hleft hr validP
          (rightDegenerateChildGluingInvMap
            P cut horientation hleft hr validP
            (positiveRightChildToGluing
              P cut horientation z)) =
        (split P cut).polygonalMk
          (split_isSurfaceValid P cut validP)
          ⟨rightFace P cut, z⟩
    rw [rightDegenerateRealizationMap_childGluingInv,
      positiveChildGluingMap_rightChildToGluing]

/-- Complete realization-equivalence data for an empty-left positive P2 split. -/
noncomputable def rightDegenerateRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    RealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) where
  toPre :=
    rightDegeneratePreMap
      P cut horientation hleft hr validP
  invPre :=
    rightDegenerateInvPreMap
      P cut horientation hleft hr validP
  continuous_toPre :=
    continuous_rightDegeneratePreMap
      P cut horientation hleft hr validP
  continuous_invPre :=
    continuous_rightDegenerateInvPreMap
      P cut horientation hleft hr validP
  to_respects := fun _ _ hxy =>
    rightDegeneratePreMap_respects
      P cut horientation hleft hr validP hxy
  inv_respects := fun _ _ hxy =>
    rightDegenerateInvPreMap_respects
      P cut horientation hleft hr validP hxy
  left_inverse_mk :=
    rightDegenerateRealization_left_inverse_mk
      P cut horientation hleft hr validP
  right_inverse_mk :=
    rightDegenerateRealization_right_inverse_mk
      P cut horientation hleft hr validP

/-- Explicit homeomorphism for an empty-left positive P2 split. -/
noncomputable def rightDegenerateRealizationHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  (rightDegenerateRealizationEquivData
    P cut horientation hleft hr validP).homeomorph

/-- Propositional realization invariance for an empty-left positive P2 split. -/
theorem rightDegeneratePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) :=
  (rightDegenerateRealizationEquivData
    P cut horientation hleft hr validP).polygonallyEquivalent

/-! ### Transport to every one-sided-degenerate cut -/

/-- A positive cut with an empty right word reduces to the base theorem by swapping its two
displayed pieces. -/
theorem leftDegeneratePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hright : cut.right = [])
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hswapOrientation :
      cut.swap.face.orientation = false := by
    simpa [P2Cut.swap] using horientation
  have hswapLeft : cut.swap.left = [] := by
    simpa [P2Cut.swap] using hright
  have hswapRight : 0 < cut.swap.right.length := by
    simpa [P2Cut.swap] using hl
  let validSwap :=
    split_isSurfaceValid P cut.swap validP
  exact
    (rightDegeneratePolygonallyEquivalent
      P cut.swap hswapOrientation hswapLeft hswapRight validP).trans
      ((swapSignedPresentationIso P cut).polygonallyEquivalent
        validSwap (split_isSurfaceValid P cut validP))

/-- Every positive one-sided-degenerate cut preserves polygonal realization. -/
theorem positiveOneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
  · exact rightDegeneratePolygonallyEquivalent
      P cut horientation hleft hr validP
  · exact leftDegeneratePolygonallyEquivalent
      P cut horientation hl hright validP

/-- A negative one-sided cut reduces to the positive theorem after reversing the cut. -/
theorem negativeOneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = true)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hflipOrientation :
      cut.flip.face.orientation = false := by
    simp [P2Cut.flip, OrientedFace.flip, horientation]
  have hflipOneSided :
      (cut.flip.left = [] ∧ 0 < cut.flip.right.length) ∨
        (0 < cut.flip.left.length ∧ cut.flip.right = []) := by
    rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
    · right
      constructor
      · simpa [P2Cut.flip, inverseWord] using hr
      · simp [P2Cut.flip, inverseWord, hleft]
    · left
      constructor
      · simp [P2Cut.flip, inverseWord, hright]
      · simpa [P2Cut.flip, inverseWord] using hl
  let validFlip :=
    split_isSurfaceValid P cut.flip validP
  exact
    (positiveOneSidedPolygonallyEquivalent
      P cut.flip hflipOrientation hflipOneSided validP).trans
      ((flipSignedPresentationIso P cut).polygonallyEquivalent
        validFlip (split_isSurfaceValid P cut validP))

/-- Every one-sided-degenerate P2 split preserves the faithful polygonal realization,
independently of traversal orientation and of which displayed cut word is empty. -/
theorem oneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  cases horientation : cut.face.orientation
  · exact positiveOneSidedPolygonallyEquivalent
      P cut horientation honeSided validP
  · exact negativeOneSidedPolygonallyEquivalent
      P cut horientation honeSided validP

end P2

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_01
/- END ClassificationOfSurfaces.FiniteCyclicP2DegenerateRealization -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicDyck | c99ff082558f72b969e7104b4b742edfa71d14ec5cc8178900632abab297a366 -/
section schottkyclassification24_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The Gallier--Xu Dyck rewrite

This file implements the common-subdivision identity underlying Gallier--Xu's handle extraction
and boundary-loop grouping:

`a U V a⁻¹ X  ~  b V U b⁻¹ X`.

We retain the edge name `a` for `b`. Both one-face words split to signed-isomorphic two-face
presentations. The isomorphism exchanges the retained copy of `a` with the fresh cutting edge and
reverses the former. The side words `U`, `V`, and `X` must not use `a`; this is exactly the
side-condition available when the displayed two darts are the two occurrences of an inner edge.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Dyck

/-- A finite-cyclic presentation with one explicitly indexed face. -/
@[reducible]
def oneFace {n : ℕ} (word : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation where
  edgeCount := n
  faces := [word]

theorem oneFace_boundary_zero {n : ℕ} (word : List (SignedDart (Fin n))) :
    (oneFace word).boundary 0 = word :=
  rfl

/-- The source spelling of the Dyck rewrite. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace (([.pos a] ++ U) ++ (V ++ [.neg a] ++ X))

/-- A cyclic spelling of the target word `a V U a⁻¹ X`, chosen so its common P2 subdivision is
definitionally transparent. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace ((U ++ [.neg a]) ++ (X ++ [.pos a] ++ V))

/-- The P2 cut of the source word. -/
def sourceCut {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    P2Cut (source a U V X) where
  face := .pos 0
  left := [.pos a] ++ U
  right := V ++ [.neg a] ++ X
  boundary_rotated := by
    change
      (([SignedDart.pos a] ++ U) ++
          (V ++ [SignedDart.neg a] ++ X)).IsRotated
        (([SignedDart.pos a] ++ U) ++
          (V ++ [SignedDart.neg a] ++ X))
    exact List.IsRotated.refl _

/-- The P2 cut of the cyclic target spelling. -/
def targetCut {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    P2Cut (target a U V X) where
  face := .pos 0
  left := U ++ [.neg a]
  right := X ++ [.pos a] ++ V
  boundary_rotated := by
    change
      ((U ++ [SignedDart.neg a]) ++
          (X ++ [SignedDart.pos a] ++ V)).IsRotated
        ((U ++ [SignedDart.neg a]) ++
          (X ++ [SignedDart.pos a] ++ V))
    exact List.IsRotated.refl _

theorem sourceCut_isNondegenerate {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (sourceCut a U V X).IsNondegenerate := by
  constructor <;> simp [sourceCut]

theorem targetCut_isNondegenerate {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (targetCut a U V X).IsNondegenerate := by
  constructor <;> simp [targetCut]

/-- Exchange the old edge `a` with the fresh P2 edge, reversing the old edge. -/
def commonEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin (n + 1)) (Fin (n + 1)) where
  edgeEquiv := Equiv.swap a.castSucc (Fin.last n)
  reverse := fun e ↦ e = a.castSucc

@[simp]
theorem commonEdgeRelabeling_pos_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos a.castSucc) =
      .neg (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg a.castSucc) =
      .pos (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_pos_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos (Fin.last n)) =
      .pos a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
    (Fin.castSucc_ne_last a).symm]

@[simp]
theorem commonEdgeRelabeling_neg_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg (Fin.last n)) =
      .neg a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
    (Fin.castSucc_ne_last a).symm]

theorem commonEdgeRelabeling_castSucc_of_ne {n : ℕ} (a e : Fin n)
    (h : e ≠ a) (orientation : Bool) :
    (commonEdgeRelabeling a).mapDart
        (if orientation then .neg e.castSucc else .pos e.castSucc) =
      if orientation then .neg e.castSucc else .pos e.castSucc := by
  have hcast : e.castSucc ≠ a.castSucc :=
    fun heq ↦ h (Fin.castSucc_injective _ heq)
  have hfresh : e.castSucc ≠ Fin.last n :=
    Fin.castSucc_ne_last e
  cases orientation <;>
    simp [commonEdgeRelabeling, EdgeRelabeling.mapDart, hcast,
      Equiv.swap_apply_of_ne_of_ne hcast hfresh]

theorem commonEdgeRelabeling_retainWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
      P2.retainWord word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hda : edgeOfDart d ≠ a := by
        intro h
        apply ha
        simp [h]
      have htail : a ∉ word.map edgeOfDart := by
        intro h
        exact ha (by simp [h])
      change
        (commonEdgeRelabeling a).mapDart (P1.castSuccDart d) ::
            (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
          P1.castSuccDart d :: P2.retainWord word
      rw [ih htail]
      congr 1
      cases d with
      | pos e =>
          exact commonEdgeRelabeling_castSucc_of_ne a e hda false
      | neg e =>
          exact commonEdgeRelabeling_castSucc_of_ne a e hda true

/-- Match the explicit face indices of the two canonical splits. -/
def commonFaceEquiv {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).Face ≃
      (P2.split (source a U V X) (sourceCut a U V X)).Face :=
  (P2.faceEquiv (target a U V X) (targetCut a U V X)).symm.trans
    (P2.faceEquiv (source a U V X) (sourceCut a U V X))

@[simp]
theorem commonFaceEquiv_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    commonFaceEquiv a U V X
        (P2.oldFace (target a U V X) (targetCut a U V X) 0) =
      P2.oldFace (source a U V X) (sourceCut a U V X) 0 :=
  rfl

theorem commonFaceEquiv_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    commonFaceEquiv a U V X
        (P2.rightFace (target a U V X) (targetCut a U V X)) =
      P2.rightFace (source a U V X) (sourceCut a U V X) :=
  rfl

theorem split_target_boundary_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.oldFace (target a U V X) (targetCut a U V X) 0) =
      P2.selectedBoundary (target a U V X) (targetCut a U V X) := by
  change
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.oldFace (target a U V X) (targetCut a U V X)
          (targetCut a U V X).face.face) =
      P2.selectedBoundary (target a U V X) (targetCut a U V X)
  exact P2.split_boundary_selected (target a U V X) (targetCut a U V X)

theorem split_source_boundary_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.oldFace (source a U V X) (sourceCut a U V X) 0) =
      P2.selectedBoundary (source a U V X) (sourceCut a U V X) := by
  change
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.oldFace (source a U V X) (sourceCut a U V X)
          (sourceCut a U V X).face.face) =
      P2.selectedBoundary (source a U V X) (sourceCut a U V X)
  exact P2.split_boundary_selected (source a U V X) (sourceCut a U V X)

theorem split_target_boundary_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.rightFace (target a U V X) (targetCut a U V X)) =
      P2.rightBoundary (target a U V X) (targetCut a U V X) :=
  P2.split_boundary_right (target a U V X) (targetCut a U V X)

theorem split_source_boundary_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.rightFace (source a U V X) (sourceCut a U V X)) =
      P2.rightBoundary (source a U V X) (sourceCut a U V X) :=
  P2.split_boundary_right (source a U V X) (sourceCut a U V X)

/-- The selected target child maps to a cyclic rotation of the selected source child. -/
theorem map_selectedBoundary_isRotated {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart) :
    ((P2.selectedBoundary (target a U V X) (targetCut a U V X)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.selectedBoundary (source a U V X) (sourceCut a U V X)) := by
  simp only [targetCut, sourceCut,
    OrientedFace.pos, P2.selectedBoundary, P2.storedWord_false,
    P2.selectedOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_append, List.map_singleton]
  rw [show P2.retainWord [SignedDart.neg a] =
      [SignedDart.neg a.castSucc] from rfl,
    show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_retainWord a U haU,
    commonEdgeRelabeling_neg_old,
    commonEdgeRelabeling_pos_fresh]
  exact List.isRotated_append

/-- The right target child maps to a cyclic rotation of the right source child. -/
theorem map_rightBoundary_isRotated {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    ((P2.rightBoundary (target a U V X) (targetCut a U V X)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.rightBoundary (source a U V X) (sourceCut a U V X)) := by
  simp only [targetCut, sourceCut,
    OrientedFace.pos, P2.rightBoundary, P2.storedWord_false,
    P2.rightOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_cons, List.map_append]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    show P2.retainWord [SignedDart.neg a] =
      [SignedDart.neg a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_neg_fresh,
    commonEdgeRelabeling_retainWord a X haX,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_retainWord a V haV]
  simpa only [List.cons_append, List.singleton_append, List.nil_append,
    List.append_assoc] using
    (List.isRotated_append
      (l := SignedDart.neg a.castSucc :: P2.retainWord X)
      (l' := SignedDart.neg (Fin.last n) :: P2.retainWord V))

/-- The two canonical P2 splits in the Dyck rewrite differ only by signed edge relabeling. -/
def splitSignedPresentationIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (P2.split (target a U V X) (targetCut a U V X))
      (P2.split (source a U V X) (sourceCut a U V X)) where
  edgeRelabeling := commonEdgeRelabeling a
  faceEquiv := commonFaceEquiv a U V X
  boundary_rotated := by
    intro q
    rcases P2.face_cases (target a U V X) (targetCut a U V X) q with
      ⟨f, rfl⟩ | rfl
    · have hf : f = 0 := by
        apply Fin.ext
        have hf' := f.isLt
        change f.val < 1 at hf'
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hf')
      subst f
      rw [commonFaceEquiv_selected,
        split_target_boundary_selected,
        split_source_boundary_selected]
      exact map_selectedBoundary_isRotated a U V X haU
    · rw [commonFaceEquiv_right,
        split_target_boundary_right,
        split_source_boundary_right]
      exact map_rightBoundary_isRotated a U V X haV haX

/-- The Gallier--Xu Dyck rewrite has a common directed subdivision. -/
theorem hasCommonSubdivision {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    HasCommonSubdivision (source a U V X) (target a U V X) := by
  let R := P2.split (source a U V X) (sourceCut a U V X)
  refine ⟨R, ?_, ?_⟩
  · exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (sourceCut_isNondegenerate a U V X))
  · exact Subdivides.p2
      ⟨targetCut a U V X,
        Or.inl (targetCut_isNondegenerate a U V X),
        ⟨splitSignedPresentationIso a U V X haU haV haX⟩⟩

/-- The Dyck rewrite preserves faithful polygonal realizations whenever the two displayed
one-face presentations are ordinary-valid. -/
theorem polygonallyEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (source a U V X).IsSurfaceValid)
    (validTarget : (target a U V X).IsSurfaceValid) :
    (source a U V X).PolygonallyEquivalent (target a U V X)
      validSource validTarget :=
  (hasCommonSubdivision a U V X haU haV haX).toPolygonallyEquivalent
    validSource validTarget

end Dyck

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_02
/- END ClassificationOfSurfaces.FiniteCyclicDyck -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicCrosscap | fb31b3c47bc8ccedfe2a37839833598478496c89eccd7b8659c7c63ec19b0148 -/
section schottkyclassification24_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The Gallier--Xu cross-cap rewrite

This file implements the common P2 refinement behind the pseudo-rewrite

`a X a Y  ~  b b Y⁻¹ X`.

The first source child is compared in its stored orientation and the second source child is read
backwards, exactly as in Gallier--Xu's derivation. The broader
`UnorientedPresentationIso` makes that face-orientation choice explicit; it is not hidden in the
ordinary signed edge relabeling.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Crosscap

/-- The source spelling with two equally oriented occurrences of `a`. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.pos a] ++ X) ++ ([.pos a] ++ Y))

/-- A cyclic spelling of the target cross-cap word `a a Y⁻¹ X`. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ((X ++ [.pos a]) ++ ([.pos a] ++ inverseWord Y))

/-- Split the source between the two occurrences of `a`. -/
def sourceCut {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    P2Cut (source a X Y) where
  face := .pos 0
  left := [.pos a] ++ X
  right := [.pos a] ++ Y
  boundary_rotated := by
    change
      (([SignedDart.pos a] ++ X) ++
          ([SignedDart.pos a] ++ Y)).IsRotated
        (([SignedDart.pos a] ++ X) ++
          ([SignedDart.pos a] ++ Y))
    exact List.IsRotated.refl _

/-- Split the target along the edge used to merge the first source child with the reverse of the
second. -/
def targetCut {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    P2Cut (target a X Y) where
  face := .pos 0
  left := X ++ [.pos a]
  right := [.pos a] ++ inverseWord Y
  boundary_rotated := by
    change
      ((X ++ [SignedDart.pos a]) ++
          ([SignedDart.pos a] ++ inverseWord Y)).IsRotated
        ((X ++ [SignedDart.pos a]) ++
          ([SignedDart.pos a] ++ inverseWord Y))
    exact List.IsRotated.refl _

theorem sourceCut_isNondegenerate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (sourceCut a X Y).IsNondegenerate := by
  constructor <;> simp [sourceCut]

theorem targetCut_isNondegenerate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (targetCut a X Y).IsNondegenerate := by
  constructor <;> simp [targetCut]

/-- Exchange the target cross-cap edge with its fresh cutting edge. -/
def commonEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin (n + 1)) (Fin (n + 1)) where
  edgeEquiv := Equiv.swap a.castSucc (Fin.last n)
  reverse := fun _ ↦ false

theorem commonEdgeRelabeling_pos_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos a.castSucc) =
      .pos (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg a.castSucc) =
      .neg (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_pos_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos (Fin.last n)) =
      .pos a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg (Fin.last n)) =
      .neg a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

theorem commonEdgeRelabeling_retainWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
      P2.retainWord word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hda : edgeOfDart d ≠ a := by
        intro h
        apply ha
        simp [h]
      have htail : a ∉ word.map edgeOfDart := by
        intro h
        exact ha (by simp [h])
      change
        (commonEdgeRelabeling a).mapDart (P1.castSuccDart d) ::
            (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
          P1.castSuccDart d :: P2.retainWord word
      rw [ih htail]
      congr 1
      cases d with
      | pos e =>
          have hcast : e.castSucc ≠ a.castSucc :=
            fun heq ↦ hda (Fin.castSucc_injective _ heq)
          simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
            Equiv.swap_apply_of_ne_of_ne hcast (Fin.castSucc_ne_last e)]
      | neg e =>
          have hcast : e.castSucc ≠ a.castSucc :=
            fun heq ↦ hda (Fin.castSucc_injective _ heq)
          simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
            Equiv.swap_apply_of_ne_of_ne hcast (Fin.castSucc_ne_last e)]

/-- Match the explicit face indices of the two canonical splits. -/
def commonFaceEquiv {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).Face ≃
      (P2.split (source a X Y) (sourceCut a X Y)).Face :=
  (P2.faceEquiv (target a X Y) (targetCut a X Y)).symm.trans
    (P2.faceEquiv (source a X Y) (sourceCut a X Y))

@[simp]
theorem commonFaceEquiv_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    commonFaceEquiv a X Y
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) =
      P2.oldFace (source a X Y) (sourceCut a X Y) 0 :=
  rfl

@[simp]
theorem commonFaceEquiv_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    commonFaceEquiv a X Y
        (P2.rightFace (target a X Y) (targetCut a X Y)) =
      P2.rightFace (source a X Y) (sourceCut a X Y) :=
  rfl

/-- Reverse exactly the right child of the target split. -/
def reverseCommonFace {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (q : (P2.split (target a X Y) (targetCut a X Y)).Face) : Bool :=
  decide (q = P2.rightFace (target a X Y) (targetCut a X Y))

@[simp]
theorem reverseCommonFace_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    reverseCommonFace a X Y
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) = false := by
  simp [reverseCommonFace, P2.oldFace, P2.rightFace, P2.faceEquiv,
    target, Dyck.oneFace] <;> first | decide | rfl | simp [finCongr]

theorem reverseCommonFace_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    reverseCommonFace a X Y
        (P2.rightFace (target a X Y) (targetCut a X Y)) = true := by
  simp [reverseCommonFace]

theorem split_target_boundary_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) =
      P2.selectedBoundary (target a X Y) (targetCut a X Y) := by
  change
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.oldFace (target a X Y) (targetCut a X Y)
          (targetCut a X Y).face.face) =
      P2.selectedBoundary (target a X Y) (targetCut a X Y)
  exact P2.split_boundary_selected (target a X Y) (targetCut a X Y)

theorem split_source_boundary_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.oldFace (source a X Y) (sourceCut a X Y) 0) =
      P2.selectedBoundary (source a X Y) (sourceCut a X Y) := by
  change
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.oldFace (source a X Y) (sourceCut a X Y)
          (sourceCut a X Y).face.face) =
      P2.selectedBoundary (source a X Y) (sourceCut a X Y)
  exact P2.split_boundary_selected (source a X Y) (sourceCut a X Y)

theorem split_target_boundary_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.rightFace (target a X Y) (targetCut a X Y)) =
      P2.rightBoundary (target a X Y) (targetCut a X Y) :=
  P2.split_boundary_right (target a X Y) (targetCut a X Y)

theorem split_source_boundary_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.rightFace (source a X Y) (sourceCut a X Y)) =
      P2.rightBoundary (source a X Y) (sourceCut a X Y) :=
  P2.split_boundary_right (source a X Y) (sourceCut a X Y)

/-- The selected target child maps to a rotation of the selected source child. -/
theorem map_selectedBoundary_isRotated {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) :
    ((P2.selectedBoundary (target a X Y) (targetCut a X Y)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.selectedBoundary (source a X Y) (sourceCut a X Y)) := by
  simp only [targetCut, sourceCut, OrientedFace.pos,
    P2.selectedBoundary, P2.storedWord_false,
    P2.selectedOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_append, List.map_singleton]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_retainWord a X haX,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_pos_fresh]
  exact List.isRotated_append

/-- The right target child maps to a rotation of the reversed right source child. -/
theorem map_rightBoundary_isRotated_inverse {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haY : a ∉ Y.map edgeOfDart) :
    ((P2.rightBoundary (target a X Y) (targetCut a X Y)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (inverseWord
          (P2.rightBoundary (source a X Y) (sourceCut a X Y))) := by
  simp only [targetCut, sourceCut, OrientedFace.pos,
    P2.rightBoundary, P2.storedWord_false,
    P2.rightOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_cons, List.map_append]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_neg_fresh,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_retainWord a (inverseWord Y) (by
      simpa [map_edgeOfDart_inverseWord] using haY)]
  rw [show
    inverseWord
        (SignedDart.neg (Fin.last n) ::
          ([SignedDart.pos a.castSucc] ++ P2.retainWord Y)) =
      inverseWord (P2.retainWord Y) ++
        [SignedDart.neg a.castSucc, SignedDart.pos (Fin.last n)] by
    simp [inverseWord, SignedDart.flip]]
  rw [P2.retainWord_inverseWord]
  simpa only [List.cons_append, List.singleton_append, List.nil_append,
    List.append_assoc] using
    (List.isRotated_append
      (l := [SignedDart.neg a.castSucc, SignedDart.pos (Fin.last n)])
      (l' := inverseWord (P2.retainWord Y)))

/-- The two P2 refinements differ by edge relabeling and reversal of their right child face. -/
def splitUnorientedPresentationIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    UnorientedPresentationIso
      (P2.split (target a X Y) (targetCut a X Y))
      (P2.split (source a X Y) (sourceCut a X Y)) where
  edgeRelabeling := commonEdgeRelabeling a
  faceEquiv := commonFaceEquiv a X Y
  reverseFace := reverseCommonFace a X Y
  boundary_rotated := by
    intro q
    rcases P2.face_cases (target a X Y) (targetCut a X Y) q with
        ⟨f, rfl⟩ | rfl
    · have hf : f = 0 := by
        apply Fin.ext
        have hf' := f.isLt
        change f.val < 1 at hf'
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hf')
      subst f
      rw [commonFaceEquiv_selected, reverseCommonFace_selected,
        split_target_boundary_selected]
      change
        ((P2.selectedBoundary (target a X Y) (targetCut a X Y)).map
          (commonEdgeRelabeling a).mapDart).IsRotated
            ((P2.split (source a X Y) (sourceCut a X Y)).orientedBoundary
              (.pos (P2.oldFace (source a X Y) (sourceCut a X Y) 0)))
      rw [orientedBoundary_pos, split_source_boundary_selected]
      exact map_selectedBoundary_isRotated a X Y haX
    · rw [commonFaceEquiv_right, reverseCommonFace_right,
        split_target_boundary_right]
      change
        ((P2.rightBoundary (target a X Y) (targetCut a X Y)).map
          (commonEdgeRelabeling a).mapDart).IsRotated
            ((P2.split (source a X Y) (sourceCut a X Y)).orientedBoundary
              (.neg (P2.rightFace (source a X Y) (sourceCut a X Y))))
      rw [orientedBoundary_neg, split_source_boundary_right]
      exact map_rightBoundary_isRotated_inverse a X Y haY

/-- The Gallier--Xu cross-cap rewrite preserves faithful polygonal realizations. -/
theorem polygonallyEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (source a X Y).IsSurfaceValid)
    (validTarget : (target a X Y).IsSurfaceValid) :
    (source a X Y).PolygonallyEquivalent (target a X Y)
      validSource validTarget := by
  let validSourceSplit :=
    P2.split_isSurfaceValid (source a X Y) (sourceCut a X Y) validSource
  let validTargetSplit :=
    P2.split_isSurfaceValid (target a X Y) (targetCut a X Y) validTarget
  have hSource :
      (source a X Y).PolygonallyEquivalent
        (P2.split (source a X Y) (sourceCut a X Y))
        validSource validSourceSplit :=
    P2.nondegeneratePolygonallyEquivalent
      (source a X Y) (sourceCut a X Y)
      (by simp [sourceCut]) (by simp [sourceCut]) validSource
  have hTarget :
      (target a X Y).PolygonallyEquivalent
        (P2.split (target a X Y) (targetCut a X Y))
        validTarget validTargetSplit :=
    P2.nondegeneratePolygonallyEquivalent
      (target a X Y) (targetCut a X Y)
      (by simp [targetCut]) (by simp [targetCut]) validTarget
  have hCommon :
      (P2.split (target a X Y) (targetCut a X Y)).PolygonallyEquivalent
        (P2.split (source a X Y) (sourceCut a X Y))
        validTargetSplit validSourceSplit :=
    (splitUnorientedPresentationIso a X Y haX haY).polygonallyEquivalent
      validTargetSplit validSourceSplit
  exact hSource.trans (hCommon.symm.trans hTarget.symm)

end Crosscap

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_03
/- END ClassificationOfSurfaces.FiniteCyclicCrosscap -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicNormalization | 3e250b2916b1be280ab3cf319454f2a179f14d7099a7ad8beedbf220928a00ac -/
section schottkyclassification24_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Stable closure for Gallier--Xu normalization chains

Directed P1/P2 chains and common subdivisions preserve ordinary validity internally. The
cross-cap rewrite additionally reads one refined face backwards, and the current
orientation-sensitive validity predicate is not invariant under arbitrary face reversal.

`ValidPresentation` therefore bundles the ordinary-validity witness at every node of a
normalization chain. `NormalizationStep` has exactly two proof-producing seams:

* a common directed P1/P2/signed-isomorphism subdivision;
* an unoriented presentation isomorphism in either direction.

The equivalence closure composes these seams, and its realization theorem needs no extra
intermediate validity arguments. This is the stable target for the remaining derived
normalization chains.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- An ordinary-valid finite cyclic presentation, used as a node in a normalization chain. -/
structure ValidPresentation where
  /-- The `presentation` declaration. -/
  presentation : FiniteCyclicPresentation
  valid : presentation.IsSurfaceValid

namespace ValidPresentation

instance : Coe ValidPresentation FiniteCyclicPresentation :=
  ⟨ValidPresentation.presentation⟩

@[ext]
theorem ext {P Q : ValidPresentation}
    (h : P.presentation = Q.presentation) :
    P = Q := by
  cases P with
  | mk presentation valid =>
      cases Q with
      | mk presentation' valid' =>
          dsimp at h
          subst presentation'
          rfl

/-- Package an ordinary-valid presentation. -/
def mk' (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    ValidPresentation :=
  ⟨P, validP⟩

end ValidPresentation

/-- One validity-safe normalization comparison. Common subdivisions cover the P1/P2/signed
closure; the second constructor covers an independent choice of face traversal in either
direction. -/
inductive NormalizationStep : ValidPresentation → ValidPresentation → Prop
  | commonSubdivision {P Q : ValidPresentation}
      (h : HasCommonSubdivision P.presentation Q.presentation) :
      NormalizationStep P Q
  | unoriented {P Q : ValidPresentation}
      (h : Nonempty (UnorientedPresentationIso P.presentation Q.presentation) ∨
        Nonempty (UnorientedPresentationIso Q.presentation P.presentation)) :
      NormalizationStep P Q
  | oneSidedP2 {P : ValidPresentation}
      (cut : P2Cut P.presentation)
      (honeSided :
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = [])) :
      NormalizationStep P
        ⟨P2.split P.presentation cut,
          P2.split_isSurfaceValid P.presentation cut P.valid⟩

namespace NormalizationStep

theorem ofUnorientedIso {P Q : ValidPresentation}
    (e : UnorientedPresentationIso P.presentation Q.presentation) :
    NormalizationStep P Q :=
  .unoriented (Or.inl ⟨e⟩)

theorem ofUnorientedIsoSymm {P Q : ValidPresentation}
    (e : UnorientedPresentationIso Q.presentation P.presentation) :
    NormalizationStep P Q :=
  .unoriented (Or.inr ⟨e⟩)

/-- A one-sided-degenerate P2 split is a normalization step. -/
theorem ofOneSidedP2 {P : ValidPresentation}
    (cut : P2Cut P.presentation)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = [])) :
    NormalizationStep P
      ⟨P2.split P.presentation cut,
        P2.split_isSurfaceValid P.presentation cut P.valid⟩ :=
  .oneSidedP2 cut honeSided

/-- Every normalization step preserves the faithful polygonal realization of its bundled valid
endpoints. -/
theorem polygonallyEquivalent {P Q : ValidPresentation}
    (h : NormalizationStep P Q) :
    P.presentation.PolygonallyEquivalent Q.presentation P.valid Q.valid := by
  cases h with
  | commonSubdivision hcommon =>
      exact hcommon.toPolygonallyEquivalent P.valid Q.valid
  | unoriented horiented =>
      rcases horiented with hforward | hbackward
      · rcases hforward with ⟨e⟩
        exact e.polygonallyEquivalent P.valid Q.valid
      · rcases hbackward with ⟨e⟩
        exact (e.polygonallyEquivalent Q.valid P.valid).symm
  | oneSidedP2 cut honeSided =>
      exact P2.oneSidedPolygonallyEquivalent
        P.presentation cut honeSided P.valid

end NormalizationStep

/-- Equivalence closure of validity-safe normalization comparisons. -/
def NormalizationEquivalent (P Q : ValidPresentation) : Prop :=
  Relation.EqvGen NormalizationStep P Q

namespace NormalizationEquivalent

theorem refl (P : ValidPresentation) : NormalizationEquivalent P P :=
  Relation.EqvGen.refl P

theorem ofStep {P Q : ValidPresentation} (h : NormalizationStep P Q) :
    NormalizationEquivalent P Q :=
  Relation.EqvGen.rel P Q h

theorem ofCommonSubdivision {P Q : ValidPresentation}
    (h : HasCommonSubdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.commonSubdivision h)

/-- A directed subdivision is a normalization equivalence, using its target as the common
subdivision. -/
theorem ofSubdivides {P Q : ValidPresentation}
    (h : Subdivides P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofCommonSubdivision ⟨Q.presentation, h, Subdivides.refl Q.presentation⟩

/-- A signed presentation isomorphism is a normalization equivalence. -/
theorem ofSignedIso {P Q : ValidPresentation}
    (e : SignedPresentationIso P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.signedIso e)

/-- A P1 subdivision is a normalization equivalence. -/
theorem ofP1 {P Q : ValidPresentation}
    (h : P1Subdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.p1 h)

/-- A P2 subdivision is a normalization equivalence. -/
theorem ofP2 {P Q : ValidPresentation}
    (h : P2Subdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.p2 h)

theorem ofUnorientedIso {P Q : ValidPresentation}
    (e : UnorientedPresentationIso P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.ofUnorientedIso e)

theorem ofUnorientedIsoSymm {P Q : ValidPresentation}
    (e : UnorientedPresentationIso Q.presentation P.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.ofUnorientedIsoSymm e)

/-- A one-sided-degenerate P2 split is a normalization equivalence. -/
theorem ofOneSidedP2 {P : ValidPresentation}
    (cut : P2Cut P.presentation)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = [])) :
    NormalizationEquivalent P
      ⟨P2.split P.presentation cut,
        P2.split_isSurfaceValid P.presentation cut P.valid⟩ :=
  ofStep (.ofOneSidedP2 cut honeSided)

theorem symm {P Q : ValidPresentation} (h : NormalizationEquivalent P Q) :
    NormalizationEquivalent Q P :=
  Relation.EqvGen.symm P Q h

theorem trans {P Q R : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q)
    (hQR : NormalizationEquivalent Q R) :
    NormalizationEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR

/-- A normalization chain yields a homeomorphism of the faithful polygonal realizations of its
endpoints. -/
theorem polygonallyEquivalent {P Q : ValidPresentation}
    (h : NormalizationEquivalent P Q) :
    P.presentation.PolygonallyEquivalent Q.presentation P.valid Q.valid := by
  induction h with
  | rel _ _ hstep =>
      exact hstep.polygonallyEquivalent
  | refl _ =>
      exact PolygonallyEquivalent.refl _ _
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ihPQ ihQR =>
      exact ihPQ.trans ihQR

end NormalizationEquivalent

namespace Dyck

/-- The generic Dyck rewrite as a node in the stable normalization closure. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SurfaceCellComplex.SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (source a U V X).IsSurfaceValid)
    (validTarget : (target a U V X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a U V X, validSource⟩
      ⟨target a U V X, validTarget⟩ :=
  NormalizationEquivalent.ofCommonSubdivision
    (hasCommonSubdivision a U V X haU haV haX)

end Dyck

namespace Crosscap

/-- The generic cross-cap rewrite as a three-step normalization chain: split the source, reverse
the right refined face, and merge to the target. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SurfaceCellComplex.SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (source a X Y).IsSurfaceValid)
    (validTarget : (target a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a X Y, validSource⟩
      ⟨target a X Y, validTarget⟩ := by
  let sourceSplit :=
    P2.split (source a X Y) (sourceCut a X Y)
  let targetSplit :=
    P2.split (target a X Y) (targetCut a X Y)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source a X Y) (sourceCut a X Y) validSource
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (target a X Y) (targetCut a X Y) validTarget
  let P : ValidPresentation := ⟨source a X Y, validSource⟩
  let S : ValidPresentation := ⟨sourceSplit, validSourceSplit⟩
  let T : ValidPresentation := ⟨targetSplit, validTargetSplit⟩
  let Q : ValidPresentation := ⟨target a X Y, validTarget⟩
  have hPS : NormalizationEquivalent P S := by
    apply NormalizationEquivalent.ofCommonSubdivision
    refine ⟨sourceSplit, ?_, Subdivides.refl sourceSplit⟩
    exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (sourceCut_isNondegenerate a X Y))
  have hST : NormalizationEquivalent S T := by
    exact NormalizationEquivalent.ofUnorientedIsoSymm
      (splitUnorientedPresentationIso a X Y haX haY)
  have hTQ : NormalizationEquivalent T Q := by
    apply NormalizationEquivalent.ofCommonSubdivision
    refine ⟨targetSplit, Subdivides.refl targetSplit, ?_⟩
    exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (targetCut_isNondegenerate a X Y))
  exact hPS.trans (hST.trans hTQ)

end Crosscap

namespace P1

/-- Contract a canonical P1 expansion inside the normalization closure. -/
theorem contractionNormalizationEquivalent
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨expand P a, expand_isSurfaceValid P a validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofP1
    (P := ⟨P, validP⟩)
    (Q := ⟨expand P a, expand_isSurfaceValid P a validP⟩)
    (P1Subdivision.canonical P a)).symm

end P1

namespace P2

/-- Merge the two children of a nondegenerate canonical P2 split inside the normalization
closure. -/
theorem mergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut : cut.IsNondegenerate)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofP2
    (P := ⟨P, validP⟩)
    (Q := ⟨split P cut, split_isSurfaceValid P cut validP⟩)
    (P2Subdivision.canonical P cut hcut)).symm

/-- Merge the two children of a one-sided-degenerate P2 split. This is the inverse form needed
by cancellation chains, where one child is a monogon. -/
theorem oneSidedMergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofOneSidedP2
    (P := ⟨P, validP⟩) cut honeSided).symm

/-- Merge any ordinary-valid canonical P2 split whose cut is either nondegenerate or
one-sided-degenerate. -/
theorem ordinaryMergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ := by
  rcases hcut with hnondegenerate | honeSided
  · exact mergeNormalizationEquivalent P cut hnondegenerate validP
  · exact oneSidedMergeNormalizationEquivalent P cut honeSided validP

end P2

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_04
/- END ClassificationOfSurfaces.FiniteCyclicNormalization -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicDerivedRewrites | 7d9fa36c82c7b5e31e0422f750e03261e2c27f3f869beab64d388fc892464c49 -/
section schottkyclassification24_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Derived Gallier--Xu word rewrites

This file builds the repeated word transformations used after the primitive P1/P2 phase of the
normalization proof.  It starts with proof-producing infrastructure for one-face cyclic words:

* cyclic rotation is a signed presentation isomorphism;
* validity transports across any permutation of the underlying unoriented edge occurrences;
* the Dyck rewrite is available with either orientation of its distinguished edge.

These lemmas keep intermediate validity witnesses out of the public derived-chain APIs.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Dyck

@[simp]
theorem inverseWord_singleton {α : Type*} (d : SignedDart α) :
    inverseWord [d] = [d.flip] :=
  rfl

/-- The unique face of an explicitly indexed one-face presentation. -/
theorem oneFace_face_eq_zero {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    f = 0 := by
  change (show Fin 1 from f) = (0 : Fin 1)
  exact Fin.eq_zero _

@[simp]
theorem oneFace_boundary {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    (oneFace word).boundary f = word := by
  rw [oneFace_face_eq_zero word f]
  rfl

/-- The edge multiplicity of a one-face presentation is the count in its displayed word. -/
@[simp]
theorem oneFace_edgeMultiplicity {n : ℕ}
    (word : List (SignedDart (Fin n))) (e : Fin n) :
    (oneFace word).edgeMultiplicity e =
      (word.map edgeOfDart).count e := by
  classical
  simp [edgeMultiplicity, faceEdgeMultiplicity, oneFace]

/-- A permutation of the unoriented edge occurrences preserves one-face surface validity.
Orientation signs and cyclic positions are intentionally irrelevant here. -/
theorem oneFace_isSurfaceValid_of_edgePerm {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hperm :
      (sourceWord.map edgeOfDart).Perm
        (targetWord.map edgeOfDart))
    (validSource : (oneFace sourceWord).IsSurfaceValid) :
    (oneFace targetWord).IsSurfaceValid := by
  classical
  have hsourceNonempty : sourceWord ≠ [] := by
    simpa using validSource.2.1 (0 : (oneFace sourceWord).Face)
  have htargetNonempty : targetWord ≠ [] := by
    intro htarget
    have hlength := hperm.length_eq
    simp only [List.length_map, htarget, List.length_nil] at hlength
    exact hsourceNonempty (List.length_eq_zero_iff.mp hlength)
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa using htargetNonempty
  · intro f g _h
    rw [oneFace_face_eq_zero targetWord f,
      oneFace_face_eq_zero targetWord g]
  · intro e
    rw [oneFace_edgeMultiplicity]
    rw [← hperm.count_eq e]
    simpa only [oneFace_edgeMultiplicity] using validSource.2.2.2 e

/-- A cyclic rotation of one displayed face word is a signed presentation isomorphism. -/
def oneFaceSignedIsoOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord) :
    SignedPresentationIso (oneFace sourceWord) (oneFace targetWord) where
  edgeRelabeling := EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl,
      oneFace_boundary, oneFace_boundary]
    exact hrotated

/-- A cyclic rotation of ordinary-valid one-face words is a normalization equivalence. -/
theorem normalizationEquivalentOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord)
    (validSource : (oneFace sourceWord).IsSurfaceValid)
    (validTarget : (oneFace targetWord).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨oneFace sourceWord, validSource⟩
      ⟨oneFace targetWord, validTarget⟩ :=
  NormalizationEquivalent.ofSignedIso
    (oneFaceSignedIsoOfIsRotated hrotated)

/-- The Dyck rewrite preserves the unoriented edge-occurrence multiset, hence ordinary validity. -/
theorem target_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (source a U V X).IsSurfaceValid) :
    (target a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- Reverse exactly one named edge orientation. -/
def reverseEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin n) (Fin n) where
  edgeEquiv := Equiv.refl _
  reverse := fun e ↦ decide (e = a)

@[simp]
theorem reverseEdgeRelabeling_pos {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.pos a) = .neg a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem reverseEdgeRelabeling_neg {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.neg a) = .pos a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

theorem reverseEdgeRelabeling_of_ne {n : ℕ} (a e : Fin n)
    (h : e ≠ a) (orientation : Bool) :
    (reverseEdgeRelabeling a).mapDart
        (if orientation then .neg e else .pos e) =
      if orientation then .neg e else .pos e := by
  cases orientation <;>
    simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart, h]

theorem reverseEdgeRelabeling_word {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    word.map (reverseEdgeRelabeling a).mapDart = word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hda : edgeOfDart d ≠ a := by
        intro h
        apply ha
        simp [h]
      have htail : a ∉ word.map edgeOfDart := by
        intro h
        exact ha (by simp [h])
      rw [List.map_cons, ih htail]
      congr 1
      cases d with
      | pos e =>
          exact reverseEdgeRelabeling_of_ne a e hda false
      | neg e =>
          exact reverseEdgeRelabeling_of_ne a e hda true

/-- The negatively oriented spelling of the Dyck source. -/
@[reducible]
def negativeSource {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace (([.neg a] ++ U) ++ (V ++ [.pos a] ++ X))

/-- The corresponding negatively oriented target spelling. -/
@[reducible]
def negativeTarget {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace ((U ++ [.pos a]) ++ (X ++ [.neg a] ++ V))

/-- Reversing `a` identifies the negative source spelling with the positive source spelling. -/
def negativeSourceSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeSource a U V X) (source a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_neg, reverseEdgeRelabeling_pos]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a V haV,
      reverseEdgeRelabeling_word a X haX]

/-- Reversing `a` identifies the negative target spelling with the positive target spelling. -/
def negativeTargetSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeTarget a U V X) (target a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_pos, reverseEdgeRelabeling_neg]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a X haX,
      reverseEdgeRelabeling_word a V haV]

/-- The negatively spelled Dyck rewrite also preserves ordinary validity. -/
theorem negativeTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (negativeSource a U V X).IsSurfaceValid) :
    (negativeTarget a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- The generic Dyck rewrite with the distinguished edge displayed negative first. -/
theorem negativeNormalizationEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (negativeSource a U V X).IsSurfaceValid)
    (validTarget : (negativeTarget a U V X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeSource a U V X, validSource⟩
      ⟨negativeTarget a U V X, validTarget⟩ := by
  let sourceIso := negativeSourceSignedIso a U V X haU haV haX
  let targetIso := negativeTargetSignedIso a U V X haU haV haX
  let validPositiveSource : (source a U V X).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validPositiveTarget : (target a U V X).IsSurfaceValid :=
    targetIso.isSurfaceValid validTarget
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent a U V X haU haV haX
          validPositiveSource validPositiveTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso).symm)

end Dyck

namespace Crosscap

/-- The cross-cap rewrite preserves the unoriented edge-occurrence multiset, hence validity. -/
theorem target_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (source a X Y).IsSurfaceValid) :
    (target a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- The cross-cap source with the distinguished edge displayed negative. -/
@[reducible]
def negativeSource {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.neg a] ++ X) ++ ([.neg a] ++ Y))

/-- The corresponding negatively oriented target. -/
@[reducible]
def negativeTarget {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ((X ++ [.neg a]) ++ ([.neg a] ++ inverseWord Y))

/-- The negatively oriented cross-cap rewrite preserves ordinary validity. -/
theorem negativeTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (negativeSource a X Y).IsSurfaceValid) :
    (negativeTarget a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- The `negativeSourceSignedIso` declaration. -/
def negativeSourceSignedIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    SignedPresentationIso
      (negativeSource a X Y) (source a X Y) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      Dyck.reverseEdgeRelabeling_neg]
    rw [Dyck.reverseEdgeRelabeling_word a X haX,
      Dyck.reverseEdgeRelabeling_word a Y haY]

/-- The `negativeTargetSignedIso` declaration. -/
def negativeTargetSignedIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    SignedPresentationIso
      (negativeTarget a X Y) (target a X Y) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      Dyck.reverseEdgeRelabeling_neg]
    rw [Dyck.reverseEdgeRelabeling_word a X haX,
      Dyck.reverseEdgeRelabeling_word a (inverseWord Y) (by
        simpa [map_edgeOfDart_inverseWord] using haY)]

/-- The cross-cap rewrite with both distinguished occurrences displayed negative. -/
theorem negativeNormalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (negativeSource a X Y).IsSurfaceValid)
    (validTarget : (negativeTarget a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeSource a X Y, validSource⟩
      ⟨negativeTarget a X Y, validTarget⟩ := by
  let sourceIso := negativeSourceSignedIso a X Y haX haY
  let targetIso := negativeTargetSignedIso a X Y haX haY
  let validPositiveSource : (source a X Y).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validPositiveTarget : (target a X Y).IsSurfaceValid :=
    targetIso.isSurfaceValid validTarget
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent a X Y haX haY
          validPositiveSource validPositiveTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso).symm)

/-- The adjacent-crosscap source `a a X Y`. -/
@[reducible]
def adjacentSource {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.pos a, .pos a] ++ X ++ Y)

/-- The alternate cross-cap target `a Y a X⁻¹`. -/
@[reducible]
def adjacentTarget {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  source a Y (inverseWord X)

/-- The alternate adjacent-crosscap rewrite preserves ordinary validity. -/
theorem adjacentTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (adjacentSource a X Y).IsSurfaceValid) :
    (adjacentTarget a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_cons, List.map_nil, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- `a a X Y` is a rotation of the ordinary cross-cap target obtained from
`a Y a X⁻¹`. -/
theorem adjacentSource_isRotated_target {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (adjacentSource a X Y).boundary 0 |>.IsRotated
      ((target a Y (inverseWord X)).boundary 0) := by
  simp only [adjacentSource, target, Dyck.oneFace_boundary_zero,
    inverseWord_inverseWord]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a, SignedDart.pos a] ++ X)
      (l' := Y)) using 1
  all_goals simp only [List.nil_append, List.cons_append,
    List.append_assoc]

/-- Gallier--Xu's alternate rule `a a X Y ~ a Y a X⁻¹`. -/
theorem adjacentNormalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (adjacentSource a X Y).IsSurfaceValid)
    (validTarget : (adjacentTarget a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨adjacentSource a X Y, validSource⟩
      ⟨adjacentTarget a X Y, validTarget⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (adjacentSource_isRotated_target a X Y)
  let validGenericTarget :
      (target a Y (inverseWord X)).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  have hRotate :
      NormalizationEquivalent
        ⟨adjacentSource a X Y, validSource⟩
        ⟨target a Y (inverseWord X), validGenericTarget⟩ :=
    NormalizationEquivalent.ofSignedIso rotation
  have haInverseX : a ∉ (inverseWord X).map edgeOfDart := by
    simpa [map_edgeOfDart_inverseWord] using haX
  have hCrosscap :
      NormalizationEquivalent
        ⟨source a Y (inverseWord X), validTarget⟩
        ⟨target a Y (inverseWord X), validGenericTarget⟩ :=
    normalizationEquivalent a Y (inverseWord X)
      haY haInverseX validTarget validGenericTarget
  exact hRotate.trans hCrosscap.symm

end Crosscap

namespace Handle

/-- The source spelling for Gallier--Xu handle extraction. -/
@[reducible]
def source {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- The result of the first Dyck rewrite. -/
@[reducible]
def afterFirst {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- A cyclic spelling of `afterFirst` exposing the two occurrences of `b`. -/
@[reducible]
def secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- The result of the second Dyck rewrite. -/
@[reducible]
def afterSecond {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- A cyclic spelling of `afterSecond` exposing `a⁻¹` before `a`. -/
@[reducible]
def thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- The target spelling contains the handle `a b a⁻¹ b⁻¹`, followed cyclically by
`Y X V U`. -/
@[reducible]
def target {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- Handle extraction preserves the unoriented edge-occurrence multiset, hence ordinary
validity. -/
theorem target_isSurfaceValid {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n)))
    (validSource : (source a b U V X Y).IsSurfaceValid) :
    (target a b U V X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_cons, List.map_nil, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- The chosen target spelling is cyclically the handle
`a b a⁻¹ b⁻¹`, followed by `Y X V U`. -/
theorem target_boundary_isRotated_handle {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (target a b U V X Y).boundary 0 |>.IsRotated
      ([.pos a, .pos b, .neg a, .neg b] ++ Y ++ X ++ V ++ U) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X ++ V ++ U)
      (l' := [SignedDart.pos a, SignedDart.pos b,
        SignedDart.neg a, SignedDart.neg b] ++ Y)) using 1 <;>
    simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- Rotate the first Dyck target to expose the second distinguished edge. -/
theorem afterFirst_isRotated_secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterFirst a b U V X Y).boundary 0 |>.IsRotated
      ((secondSource a b U V X Y).boundary 0) := by
  simp only [afterFirst, secondSource, Dyck.target, Dyck.source,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := U ++ [SignedDart.neg a] ++ X ++
        [SignedDart.neg b] ++ Y ++ [SignedDart.pos a])
      (l' := [SignedDart.pos b] ++ V)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Rotate the second Dyck target to expose `a` in the opposite orientation. -/
theorem afterSecond_isRotated_thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterSecond a b U V X Y).boundary 0 |>.IsRotated
      ((thirdSource a b U V X Y).boundary 0) := by
  simp only [afterSecond, thirdSource, Dyck.target, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := V ++ U ++ [SignedDart.neg b] ++ Y ++
        [SignedDart.pos a] ++ [SignedDart.pos b])
      (l' := [SignedDart.neg a] ++ X)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu's three-Dyck chain extracts the interleaved opposite pairs as a handle. -/
theorem normalizationEquivalent {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b)
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (hbU : b ∉ U.map edgeOfDart)
    (hbV : b ∉ V.map edgeOfDart)
    (hbX : b ∉ X.map edgeOfDart)
    (hbY : b ∉ Y.map edgeOfDart)
    (validSource : (source a b U V X Y).IsSurfaceValid)
    (validTarget : (target a b U V X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a b U V X Y, validSource⟩
      ⟨target a b U V X Y, validTarget⟩ := by
  have haBV :
      a ∉ ([SignedDart.pos b] ++ V).map edgeOfDart := by
    simp [edgeOfDart, hab, haV]
  have haXbY :
      a ∉ (X ++ [SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, haX, hab, haY]
  let validAfterFirst : (afterFirst a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) validSource
  have hFirst :
      NormalizationEquivalent
        ⟨source a b U V X Y, validSource⟩
        ⟨afterFirst a b U V X Y, validAfterFirst⟩ :=
    Dyck.normalizationEquivalent a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) haU haBV haXbY
      validSource validAfterFirst
  let firstRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterFirst_isRotated_secondSource a b U V X Y)
  let validSecondSource : (secondSource a b U V X Y).IsSurfaceValid :=
    firstRotation.isSurfaceValid validAfterFirst
  have hRotateFirst :
      NormalizationEquivalent
        ⟨afterFirst a b U V X Y, validAfterFirst⟩
        ⟨secondSource a b U V X Y, validSecondSource⟩ :=
    NormalizationEquivalent.ofSignedIso firstRotation
  have hbVU : b ∉ (V ++ U).map edgeOfDart := by
    simp [hbV, hbU]
  have hbNegAX :
      b ∉ ([SignedDart.neg a] ++ X).map edgeOfDart := by
    simp [edgeOfDart, hab.symm, hbX]
  have hbYPosA :
      b ∉ (Y ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [edgeOfDart, hbY, hab.symm]
  let validAfterSecond : (afterSecond a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) validSecondSource
  have hSecond :
      NormalizationEquivalent
        ⟨secondSource a b U V X Y, validSecondSource⟩
        ⟨afterSecond a b U V X Y, validAfterSecond⟩ :=
    Dyck.normalizationEquivalent b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) hbVU hbNegAX hbYPosA
      validSecondSource validAfterSecond
  let secondRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterSecond_isRotated_thirdSource a b U V X Y)
  let validThirdSource : (thirdSource a b U V X Y).IsSurfaceValid :=
    secondRotation.isSurfaceValid validAfterSecond
  have hRotateSecond :
      NormalizationEquivalent
        ⟨afterSecond a b U V X Y, validAfterSecond⟩
        ⟨thirdSource a b U V X Y, validThirdSource⟩ :=
    NormalizationEquivalent.ofSignedIso secondRotation
  have haXVU : a ∉ (X ++ V ++ U).map edgeOfDart := by
    simp [haX, haV, haU]
  have haNegBY :
      a ∉ ([SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, haY]
  have haPosB :
      a ∉ ([SignedDart.pos b] : List (SignedDart (Fin n))).map edgeOfDart := by
    simp [edgeOfDart, hab]
  have hThird :
      NormalizationEquivalent
        ⟨thirdSource a b U V X Y, validThirdSource⟩
        ⟨target a b U V X Y, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a
      (X ++ V ++ U) ([SignedDart.neg b] ++ Y) [SignedDart.pos b]
      haXVU haNegBY haPosB validThirdSource validTarget
  exact hFirst.trans
    (hRotateFirst.trans
      (hSecond.trans (hRotateSecond.trans hThird)))

end Handle

namespace HandleToCrosscaps

-- A compact interface for one validity-preserving normalization rewrite.  Keeping validity
-- transport inside the certificate prevents long chains from exposing every dependent witness.
private structure RewriteCertificate (P Q : FiniteCyclicPresentation) : Prop where
  target_isSurfaceValid : P.IsSurfaceValid → Q.IsSurfaceValid
  normalizationEquivalent :
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      NormalizationEquivalent ⟨P, validP⟩ ⟨Q, validQ⟩

-- Composition chooses the intermediate validity witness once, behind the compact interface.
private theorem RewriteCertificate.trans {P Q R : FiniteCyclicPresentation}
    (hPQ : RewriteCertificate P Q) (hQR : RewriteCertificate Q R) :
    RewriteCertificate P R where
  target_isSurfaceValid validP := hQR.target_isSurfaceValid (hPQ.target_isSurfaceValid validP)
  normalizationEquivalent validP validR := by
    let validQ := hPQ.target_isSurfaceValid validP
    exact (hPQ.normalizationEquivalent validP validQ).trans
      (hQR.normalizationEquivalent validQ validR)

-- Package the generic negative cross-cap rule without specializing its presentation expressions.
private theorem negativeCrosscap_rewriteCertificate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (Crosscap.negativeSource a X Y) (Crosscap.negativeTarget a X Y) := by
  constructor
  · exact Crosscap.negativeTarget_isSurfaceValid a X Y
  · exact Crosscap.negativeNormalizationEquivalent a X Y haX haY

-- Package the generic positive cross-cap rule at the same compact interface.
private theorem crosscap_rewriteCertificate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (Crosscap.source a X Y) (Crosscap.target a X Y) := by
  constructor
  · exact Crosscap.target_isSurfaceValid a X Y
  · exact Crosscap.normalizationEquivalent a X Y haX haY

/-- A crosscap followed by a handle, with arbitrary intervening words `X` and `Y`. -/
@[reducible]
def source {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.adjacentSource a
    (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)

/-- The first alternate cross-cap rewrite. -/
@[reducible]
def afterFirst {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.adjacentTarget a
    (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)

/-- Rotate the first target to expose the two negative occurrences of `b`. -/
@[reducible]
def secondSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeSource b
    ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
    (inverseWord X ++ [.pos a])

/-- The result of rewriting the two negative occurrences of `b`. -/
@[reducible]
def afterSecond {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeTarget b
    ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
    (inverseWord X ++ [.pos a])

/-- Expose the two negative occurrences of `c`. -/
@[reducible]
def thirdSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeSource c
    (Y ++ [.pos a])
    ([.neg b, .neg b, .neg a] ++ X)

/-- The result of rewriting the two negative occurrences of `c`. -/
@[reducible]
def afterThird {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeTarget c
    (Y ++ [.pos a])
    ([.neg b, .neg b, .neg a] ++ X)

/-- Expose the remaining two occurrences of `a`. -/
@[reducible]
def fourthSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.source a
    ([.pos b, .pos b] ++ Y)
    ([.neg c, .neg c] ++ inverseWord X)

/-- The final spelling is cyclically `a a X c c b b Y`: three crosscaps. -/
@[reducible]
def target {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.target a
    ([.pos b, .pos b] ++ Y)
    ([.neg c, .neg c] ++ inverseWord X)

theorem afterFirst_isRotated_secondSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterFirst a b c X Y).boundary 0 |>.IsRotated
      ((secondSource a b c X Y).boundary 0) := by
  simp only [afterFirst, secondSource, Crosscap.adjacentTarget,
    Crosscap.source, Crosscap.negativeSource,
    Dyck.oneFace_boundary_zero, inverseWord_append]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a])
      (l' := [SignedDart.neg b, SignedDart.neg c] ++ Y ++
        [SignedDart.pos a, SignedDart.neg c, SignedDart.neg b] ++
        inverseWord X)) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

theorem afterSecond_isRotated_thirdSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterSecond a b c X Y).boundary 0 |>.IsRotated
      ((thirdSource a b c X Y).boundary 0) := by
  simpa only [afterSecond, thirdSource, Crosscap.negativeTarget,
    Crosscap.negativeSource, Dyck.oneFace_boundary_zero,
    inverseWord_append, inverseWord_inverseWord,
    Dyck.inverseWord_singleton, SignedDart.flip,
    List.cons_append, List.nil_append, List.append_assoc] using
      (List.IsRotated.refl ((thirdSource a b c X Y).boundary 0))

theorem afterThird_isRotated_fourthSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterThird a b c X Y).boundary 0 |>.IsRotated
      ((fourthSource a b c X Y).boundary 0) := by
  simp only [afterThird, fourthSource, Crosscap.negativeTarget,
    Crosscap.source, Dyck.oneFace_boundary_zero, inverseWord_append]
  convert
    (List.isRotated_append
      (l := Y ++ [SignedDart.pos a, SignedDart.neg c,
        SignedDart.neg c] ++ inverseWord X)
      (l' := [SignedDart.pos a, SignedDart.pos b,
        SignedDart.pos b])) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

/-- Check the exact final cyclic order of the three crosscaps. -/
theorem target_boundary_isRotated_crosscaps {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (target a b c X Y).boundary 0 |>.IsRotated
      ([.pos a, .pos a] ++ X ++
        [.pos c, .pos c, .pos b, .pos b] ++ Y) := by
  simp only [target, Crosscap.target, Dyck.oneFace_boundary_zero,
    inverseWord_append, inverseWord_inverseWord]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos b, SignedDart.pos b] ++ Y)
      (l' := [SignedDart.pos a, SignedDart.pos a] ++ X ++
        [SignedDart.pos c, SignedDart.pos c])) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

-- The first alternate cross-cap rewrite, with its validity transport hidden in a certificate.
private theorem first_rewriteCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b) (hac : a ≠ c)
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (source a b c X Y) (afterFirst a b c X Y) := by
  have haFirstX :
      a ∉ (X ++ [SignedDart.pos b, SignedDart.pos c]).map edgeOfDart := by
    simp [edgeOfDart, haX, hab, hac]
  have haFirstY :
      a ∉ ([SignedDart.neg b, SignedDart.neg c] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, hac, haY]
  constructor
  · exact Crosscap.adjacentTarget_isSurfaceValid a
      (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)
  · intro validP validQ
    exact Crosscap.adjacentNormalizationEquivalent a
      (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)
      haFirstX haFirstY validP validQ

-- Rotation after the first rewrite is independent of the chosen validity witnesses.
private theorem first_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterFirst a b c X Y) (secondSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterFirst_isRotated_secondSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

-- Rotation after rewriting `b` exposes the two negative occurrences of `c`.
private theorem second_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterSecond a b c X Y) (thirdSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterSecond_isRotated_thirdSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

-- The final rotation exposes the two remaining occurrences of `a`.
private theorem third_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterThird a b c X Y) (fourthSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterThird_isRotated_fourthSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

/-- Gallier--Xu Step 5: a crosscap and a handle are equivalent to three crosscaps. -/
theorem normalizationEquivalent {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart)
    (hbX : b ∉ X.map edgeOfDart) (hbY : b ∉ Y.map edgeOfDart)
    (hcX : c ∉ X.map edgeOfDart) (hcY : c ∉ Y.map edgeOfDart)
    (validSource : (source a b c X Y).IsSurfaceValid)
    (validTarget : (target a b c X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a b c X Y, validSource⟩
      ⟨target a b c X Y, validTarget⟩ := by
  have hbSecondX :
      b ∉ ([SignedDart.neg c] ++ Y ++
        [SignedDart.pos a] ++ [SignedDart.neg c]).map edgeOfDart := by
    simp [edgeOfDart, hbc, hbY, hab.symm]
  have hbSecondY :
      b ∉ (inverseWord X ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [map_edgeOfDart_inverseWord, hbX, edgeOfDart, hab.symm]
  have hcThirdX :
      c ∉ (Y ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [hcY, edgeOfDart, hac.symm]
  have hcThirdY :
      c ∉ ([SignedDart.neg b, SignedDart.neg b,
        SignedDart.neg a] ++ X).map edgeOfDart := by
    simp [edgeOfDart, hbc.symm, hac.symm, hcX]
  have haFourthX :
      a ∉ ([SignedDart.pos b, SignedDart.pos b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, haY]
  have haFourthY :
      a ∉ ([SignedDart.neg c, SignedDart.neg c] ++
        inverseWord X).map edgeOfDart := by
    simp [edgeOfDart, hac, map_edgeOfDart_inverseWord, haX]
  let chain₁ :=
    (first_rewriteCertificate a b c X Y hab hac haX haY).trans
      (first_rotationCertificate a b c X Y)
  let chain₂ := chain₁.trans
    (negativeCrosscap_rewriteCertificate b
      ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
      (inverseWord X ++ [.pos a]) hbSecondX hbSecondY)
  let chain₃ := chain₂.trans (second_rotationCertificate a b c X Y)
  let chain₄ := chain₃.trans
    (negativeCrosscap_rewriteCertificate c
      (Y ++ [.pos a]) ([.neg b, .neg b, .neg a] ++ X)
      hcThirdX hcThirdY)
  let chain₅ := chain₄.trans (third_rotationCertificate a b c X Y)
  let chain := chain₅.trans
    (crosscap_rewriteCertificate a
      ([.pos b, .pos b] ++ Y) ([.neg c, .neg c] ++ inverseWord X)
      haFourthX haFourthY)
  exact chain.normalizationEquivalent validSource validTarget

end HandleToCrosscaps

namespace LoopGrouping

/-- A cyclic word with the loop block `a H a⁻¹`, a separating word `X`, and a block `V` to
move next to the loop. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.pos a] ++ H) ++ ([.neg a] ++ X ++ V))

/-- Rotate the source to expose the negative occurrence of `a` first. -/
@[reducible]
def rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a X V H

/-- The target is cyclically `a H a⁻¹ V X`, so `V` has crossed the separating word `X`. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a X V H

theorem source_isRotated_rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (source a H X V).boundary 0 |>.IsRotated
      ((rotatedSource a H X V).boundary 0) := by
  simp only [source, rotatedSource, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a] ++ H)
      (l' := [SignedDart.neg a] ++ X ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- The target spelling displays the moved block immediately after the loop. -/
theorem target_boundary_isRotated_grouped {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (target a H X V).boundary 0 |>.IsRotated
      ([.pos a] ++ H ++ [.neg a] ++ V ++ X) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X)
      (l' := [SignedDart.pos a] ++ H ++
        [SignedDart.neg a] ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu loop grouping is one negative Dyck rewrite after a cyclic rotation. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n)))
    (haH : a ∉ H.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (validSource : (source a H X V).IsSurfaceValid)
    (validTarget : (target a H X V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a H X V, validSource⟩
      ⟨target a H X V, validTarget⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (source_isRotated_rotatedSource a H X V)
  let validRotatedSource : (rotatedSource a H X V).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  have hRotate :
      NormalizationEquivalent
        ⟨source a H X V, validSource⟩
        ⟨rotatedSource a H X V, validRotatedSource⟩ :=
    NormalizationEquivalent.ofSignedIso rotation
  have hDyck :
      NormalizationEquivalent
        ⟨rotatedSource a H X V, validRotatedSource⟩
        ⟨target a H X V, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a X V H
      haX haV haH validRotatedSource validTarget
  exact hRotate.trans hDyck

end LoopGrouping

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_05
/- END ClassificationOfSurfaces.FiniteCyclicDerivedRewrites -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicCancellation | 4219b8a6816ae5cff2429c74ff30710dd00fbe9337f5153214bf42c8e4fee9d8 -/
section schottkyclassification24_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Cancellation chains for finite cyclic presentations

This file implements Gallier--Xu Step 1.  The exact base spelling has a fresh-last edge followed
immediately by its inverse.  Splitting between that pair and the remaining word produces exactly
the P1 expansion of the one-sided split of the word with the pair removed.  Thus one P2 split,
one P1 contraction, and one one-sided P2 merge cancel the pair.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Cancellation

/-- The word after deleting the displayed inverse pair. -/
@[reducible]
def target {n : ℕ} (X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace X

/-- The base cancellation spelling, with the cancellable edge named last. -/
@[reducible]
def source {n : ℕ} (X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace
    ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
      P2.retainWord X)

/-- Retaining after contraction recovers a word which does not use the fresh-last edge. -/
theorem retainWord_contractWord_of_fresh_not_mem {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (hfresh : P1.freshEdge n ∉ word.map edgeOfDart) :
    P2.retainWord (P1.contractWord word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      have htail : P1.freshEdge n ∉ word.map edgeOfDart := by
        intro h
        exact hfresh (by simp [h])
      have hd : edgeOfDart d ≠ P1.freshEdge n := by
        intro h
        exact hfresh (by simp [h])
      cases d with
      | pos e =>
          induction e using Fin.lastCases with
          | last =>
              exact (hd rfl).elim
          | cast e =>
              rw [show P1.contractWord
                    (SignedDart.pos e.castSucc :: word) =
                  SignedDart.pos e :: P1.contractWord word by
                simp [P1.contractWord]]
              change
                P2.retainWord
                    (SignedDart.pos e :: P1.contractWord word) =
                  SignedDart.pos e.castSucc :: word
              have ih' := ih htail
              change
                (P1.contractWord word).map P1.castSuccDart = word at ih'
              rw [P2.retainWord, List.map_cons,
                P1.castSuccDart_pos, ih']
      | neg e =>
          induction e using Fin.lastCases with
          | last =>
              exact (hd rfl).elim
          | cast e =>
              rw [show P1.contractWord
                    (SignedDart.neg e.castSucc :: word) =
                  SignedDart.neg e :: P1.contractWord word by
                simp [P1.contractWord]]
              change
                P2.retainWord
                    (SignedDart.neg e :: P1.contractWord word) =
                  SignedDart.neg e.castSucc :: word
              have ih' := ih htail
              change
                (P1.contractWord word).map P1.castSuccDart = word at ih'
              rw [P2.retainWord, List.map_cons,
                P1.castSuccDart_neg, ih']

/-- Move a chosen edge name to the fresh-last position. -/
def moveToLast {n : ℕ} (a : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.swap a (Fin.last n)

/-- Rename a tail so that the displayed cancellable edge becomes last. -/
def renamedTail {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin (n + 1))) :=
  X.map (SignedDart.mapEquiv (moveToLast a))

/-- Delete the now-unused last edge name from a renamed tail. -/
def lowerTail {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  P1.contractWord (renamedTail a X)

theorem freshEdge_not_mem_renamedTail {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    P1.freshEdge n ∉ (renamedTail a X).map edgeOfDart := by
  intro hfresh
  rcases List.mem_map.mp hfresh with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  rw [edgeOfDart_mapEquiv] at hedge
  have holdEdge : edgeOfDart old = a := by
    apply (moveToLast a).injective
    rw [hedge]
    simp [moveToLast, P1.freshEdge]
  exact ha (List.mem_map.mpr ⟨old, hold, holdEdge⟩)

/-- Lowering and re-embedding a tail which avoids the cancellable edge recovers its exact
renamed spelling. -/
theorem retainWord_lowerTail {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    P2.retainWord (lowerTail a X) = renamedTail a X :=
  retainWord_contractWord_of_fresh_not_mem
    (renamedTail a X) (freshEdge_not_mem_renamedTail a X ha)

/-- A one-face word with a displayed positive inverse pair. -/
@[reducible]
def namedSource {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.pos a, .neg a] ++ X)

/-- Rename a displayed cancellable edge to last and contract the unused name from its tail. -/
def namedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (namedSource a X) (source (lowerTail a X)) where
  edgeRelabeling := EdgeRelabeling.ofEquiv (moveToLast a)
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    rw [retainWord_lowerTail a X ha]
    change
      ([SignedDart.mapEquiv (moveToLast a) (.pos a),
          SignedDart.mapEquiv (moveToLast a) (.neg a)] ++
        renamedTail a X).IsRotated
        ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
          renamedTail a X)
    have hmove : moveToLast a a = P1.freshEdge n := by
      simp [moveToLast, P1.freshEdge]
    rw [show SignedDart.mapEquiv (moveToLast a) (.pos a) =
          .pos (P1.freshEdge n) by simp [hmove],
      show SignedDart.mapEquiv (moveToLast a) (.neg a) =
          .neg (P1.freshEdge n) by simp [hmove]]

/-- Split the inverse pair from the remaining word. -/
def sourceCut {n : ℕ} (X : List (SignedDart (Fin n))) :
    P2Cut (source X) where
  face := ⟨0, false⟩
  left := [.pos (P1.freshEdge n)]
  right := [.neg (P1.freshEdge n)] ++ P2.retainWord X
  boundary_rotated := by
    exact List.IsRotated.refl _

/-- Split the target at position zero, producing a monogon and the target word. -/
def targetCut {n : ℕ} (X : List (SignedDart (Fin n))) :
    P2Cut (target X) :=
  P2Cut.canonical ⟨0, false⟩ 0

@[simp]
theorem sourceCut_left {n : ℕ} (X : List (SignedDart (Fin n))) :
    (sourceCut X).left = [.pos (P1.freshEdge n)] :=
  rfl

@[simp]
theorem sourceCut_right {n : ℕ} (X : List (SignedDart (Fin n))) :
    (sourceCut X).right =
      [.neg (P1.freshEdge n)] ++ P2.retainWord X :=
  rfl

theorem sourceCut_isNondegenerate {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    (sourceCut X).IsNondegenerate := by
  constructor <;> simp

@[simp]
theorem targetCut_left {n : ℕ} (X : List (SignedDart (Fin n))) :
    (targetCut X).left = [] :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ} (X : List (SignedDart (Fin n))) :
    (targetCut X).right = X :=
  rfl

/-- Expanding at the fresh-last edge only retains every twice-embedded old dart. -/
theorem expandWord_retainWord_fresh {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    P1.expandWord (P1.freshEdge n) (P2.retainWord X) =
      P2.retainWord (P2.retainWord X) := by
  change
    P1.expandWord (Fin.last n) (X.map P1.castSuccDart) =
      (X.map P1.castSuccDart).map P1.castSuccDart
  induction X with
  | nil => rfl
  | cons d X ih =>
      simp only [List.map_cons, P1.expandWord_cons]
      cases d with
      | pos e =>
          simp only [P1.castSuccDart_pos]
          rw [P1.expandDart_pos_of_ne (Fin.castSucc_ne_last e)]
          simp only [ih, List.singleton_append]
      | neg e =>
          simp only [P1.castSuccDart_neg]
          rw [P1.expandDart_neg_of_ne (Fin.castSucc_ne_last e)]
          simp only [ih, List.singleton_append]

/-- The source split is exactly the P1 expansion of the target's one-sided split. -/
theorem split_source_eq_expand_split_target {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    P2.split (source X) (sourceCut X) =
      P1.expand (P2.split (target X) (targetCut X))
        (P2.freshEdge (target X)) := by
  simp only [P2.split, source, Dyck.oneFace, P1.freshEdge, P2.retainWord,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, List.ofFn_succ, P2.faceWord, P2.rightBoundary, P2.storedWord,
    sourceCut, Bool.false_eq_true, ↓reduceIte, P2.rightOrientedBoundary,
    P2.freshEdge, List.map_cons, P1.castSuccDart_neg, List.map_map,
    P2.selectedBoundary, P2.selectedOrientedBoundary, P1.castSuccDart_pos,
    List.map_nil, Dyck.oneFace_boundary, Fin.isValue, Fin.cast_eq_self,
    Fin.succ_zero_eq_one, List.ofFn_zero, P1.expand, target, targetCut,
    P2Cut.canonical, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero,
    List.drop_zero, P1.expandWord, mk.injEq, heq_eq_eq,
    List.cons.injEq, and_true, true_and]
  constructor
  · change
      [SignedDart.pos (Fin.last n).castSucc,
        SignedDart.pos (Fin.last (n + 1))] =
        P1.expandWord (Fin.last n) [.pos (Fin.last n)]
    simp [P1.firstSubedge, P1.freshEdge]
  · change
      SignedDart.neg (Fin.last (n + 1)) ::
          SignedDart.neg (Fin.last n).castSucc ::
            X.map (P1.castSuccDart ∘ P1.castSuccDart) =
        P1.expandWord (Fin.last n)
          (SignedDart.neg (Fin.last n) ::
            X.map P1.castSuccDart)
    rw [P1.expandWord_cons, P1.expandDart_neg_self,
      show
        P1.expandWord (Fin.last n) (X.map P1.castSuccDart) =
          (X.map P1.castSuccDart).map P1.castSuccDart by
            simpa [P1.freshEdge, P2.retainWord] using
              expandWord_retainWord_fresh X]
    simp [P1.firstSubedge, P1.freshEdge, Function.comp_def]

/-- Deleting an inverse pair preserves the unoriented edge-occurrence multiplicities of all
remaining edges. -/
theorem target_isSurfaceValid {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (hX : X ≠ [])
    (validSource : (source X).IsSurfaceValid) :
    (target X).IsSurfaceValid := by
  classical
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    have hsourceNonempty :
        ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
          P2.retainWord X) ≠ [] := by
      simp
    simpa [target, Dyck.oneFace_boundary] using hX
  · intro f g _h
    exact Dyck.oneFace_face_eq_zero X f |>.trans
      (Dyck.oneFace_face_eq_zero X g).symm
  · intro e
    have hmultiplicity := validSource.2.2.2 e.castSucc
    rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity ⊢
    simp only [List.map_append, List.map_cons,
      List.map_nil, edgeOfDart, List.count_append,
      List.count_cons, List.count_nil] at hmultiplicity
    rw [P2.count_retainWord_castSucc] at hmultiplicity
    have hne : e.castSucc ≠ P1.freshEdge n :=
      P1.firstSubedge_ne_freshEdge e
    simp only [beq_iff_eq, hne.symm, ↓reduceIte, add_zero, zero_add] at hmultiplicity
    exact hmultiplicity

/-- Gallier--Xu Step 1 for the base spelling: split the inverse pair, contract the resulting
two-edge paths, then merge the monogon produced by the one-sided target split. -/
theorem normalizationEquivalent {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (hX : X ≠ [])
    (validSource : (source X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source X, validSource⟩
      ⟨target X, target_isSurfaceValid X hX validSource⟩ := by
  let validTarget : (target X).IsSurfaceValid :=
    target_isSurfaceValid X hX validSource
  let sourceSplit := P2.split (source X) (sourceCut X)
  let targetSplit := P2.split (target X) (targetCut X)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source X) (sourceCut X) validSource
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (target X) (targetCut X) validTarget
  have hsource :
      NormalizationEquivalent
        ⟨source X, validSource⟩
        ⟨sourceSplit, validSourceSplit⟩ :=
    NormalizationEquivalent.ofP2
      (P2Subdivision.canonical
        (source X) (sourceCut X) (sourceCut_isNondegenerate X))
  have hmiddle :
      NormalizationEquivalent
        ⟨sourceSplit, validSourceSplit⟩
        ⟨targetSplit, validTargetSplit⟩ := by
    have hcontract :=
      P1.contractionNormalizationEquivalent
        targetSplit (P2.freshEdge (target X)) validTargetSplit
    have hnode :
        (⟨sourceSplit, validSourceSplit⟩ : ValidPresentation) =
          ⟨P1.expand targetSplit (P2.freshEdge (target X)),
            P1.expand_isSurfaceValid targetSplit
              (P2.freshEdge (target X)) validTargetSplit⟩ := by
      apply ValidPresentation.ext
      exact split_source_eq_expand_split_target X
    rw [hnode]
    exact hcontract
  have htarget :
      NormalizationEquivalent
        ⟨targetSplit, validTargetSplit⟩
        ⟨target X, validTarget⟩ := by
    apply P2.oneSidedMergeNormalizationEquivalent
    exact Or.inl
      ⟨targetCut_left X,
        List.length_pos_iff_ne_nil.mpr hX⟩
  exact hsource.trans (hmiddle.trans htarget)

/-- The zero-tail cancellation branch lands at the ordinary two-monogon sphere. -/
theorem sphereNormalizationEquivalent
    (validSource : (source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source ([] : List (SignedDart (Fin 0))), validSource⟩
      ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ := by
  let X : List (SignedDart (Fin 0)) := []
  let sourceSplit := P2.split (source X) (sourceCut X)
  let targetSplit := P2.split (target X) (targetCut X)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source X) (sourceCut X) validSource
  have htargetSplit : targetSplit = twoMonogonSphere := by
    rfl
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    htargetSplit.symm ▸ twoMonogonSphere_isSurfaceValid
  have hsource :
      NormalizationEquivalent
        ⟨source X, validSource⟩
        ⟨sourceSplit, validSourceSplit⟩ :=
    NormalizationEquivalent.ofP2
      (P2Subdivision.canonical
        (source X) (sourceCut X) (sourceCut_isNondegenerate X))
  have hmiddle :
      NormalizationEquivalent
        ⟨sourceSplit, validSourceSplit⟩
        ⟨targetSplit, validTargetSplit⟩ := by
    have hcontract :=
      P1.contractionNormalizationEquivalent
        targetSplit (P2.freshEdge (target X)) validTargetSplit
    have hnode :
        (⟨sourceSplit, validSourceSplit⟩ : ValidPresentation) =
          ⟨P1.expand targetSplit (P2.freshEdge (target X)),
            P1.expand_isSurfaceValid targetSplit
              (P2.freshEdge (target X)) validTargetSplit⟩ := by
      apply ValidPresentation.ext
      exact split_source_eq_expand_split_target X
    rw [hnode]
    exact hcontract
  have htargetNode :
      (⟨targetSplit, validTargetSplit⟩ : ValidPresentation) =
        ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ := by
    apply ValidPresentation.ext
    exact htargetSplit
  rw [← htargetNode]
  exact hsource.trans hmiddle

/-! ### Cancellation in a multi-face context -/

namespace Context

/-- Delete the displayed pair in the first face and retain all other faces. -/
@[reducible]
def target {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n
  faces := X :: W

/-- The base contextual cancellation spelling, with the cancellable edge named last. -/
@[reducible]
def source {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
      P2.retainWord X) :: W.map P2.retainWord

/-- Split the displayed inverse pair from the rest of the first source face. -/
def sourceCut {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (source X W) where
  face := ⟨⟨0, by simp [source]⟩, false⟩
  left := [.pos (P1.freshEdge n)]
  right := [.neg (P1.freshEdge n)] ++ P2.retainWord X
  boundary_rotated := List.IsRotated.refl _

/-- Split the first target face at position zero. -/
def targetCut {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (target X W) :=
  P2Cut.canonical ⟨⟨0, by simp [target]⟩, false⟩ 0

@[simp]
theorem sourceCut_left {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (sourceCut X W).left = [.pos (P1.freshEdge n)] :=
  rfl

@[simp]
theorem sourceCut_right {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (sourceCut X W).right =
      [.neg (P1.freshEdge n)] ++ P2.retainWord X :=
  rfl

theorem sourceCut_isNondegenerate {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (sourceCut X W).IsNondegenerate := by
  constructor <;> simp

@[simp]
theorem targetCut_left {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut X W).left = [] :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut X W).right = X :=
  rfl

/-- Source and target retain the same face positions before the auxiliary P2 splits. -/
def baseFaceEquiv {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source X W).Face ≃ (target X W).Face :=
  finCongr (by simp [source, target])

/-- The face positions in the source split and the expanded target split have the same explicit
indexing: old positions first and the right child last. -/
def middleFaceEquiv {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (P2.split (source X W) (sourceCut X W)).Face ≃
      (P1.expand (P2.split (target X W) (targetCut X W))
        (P2.freshEdge (target X W))).Face :=
  (P2.faceEquiv (source X W) (sourceCut X W)).symm |>.trans
    ((finCongr (by simp [source, target])).trans
      ((P2.faceEquiv (target X W) (targetCut X W)).trans
        (P1.faceEquiv
          (P2.split (target X W) (targetCut X W))
          (P2.freshEdge (target X W)))))

@[simp]
theorem middleFaceEquiv_apply_val {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (P2.split (source X W) (sourceCut X W)).Face) :
    (middleFaceEquiv X W f).val = f.val := by
  simp only [middleFaceEquiv, Equiv.trans_apply, P2.faceEquiv,
    P1.faceEquiv, finCongr_apply, Fin.val_cast]
  rfl

@[simp]
theorem middleFaceEquiv_oldFace {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (source X W).Face) :
    middleFaceEquiv X W
        (P2.oldFace (source X W) (sourceCut X W) f) =
      P1.faceEquiv
        (P2.split (target X W) (targetCut X W))
        (P2.freshEdge (target X W))
        (P2.oldFace (target X W) (targetCut X W)
          (baseFaceEquiv X W f)) := by
  apply Fin.ext
  rw [middleFaceEquiv_apply_val]
  change f.val = (baseFaceEquiv X W f).val
  rfl

@[simp]
theorem middleFaceEquiv_rightFace {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    middleFaceEquiv X W
        (P2.rightFace (source X W) (sourceCut X W)) =
      P1.faceEquiv
        (P2.split (target X W) (targetCut X W))
        (P2.freshEdge (target X W))
        (P2.rightFace (target X W) (targetCut X W)) := by
  apply Fin.ext
  rw [middleFaceEquiv_apply_val]
  change (source X W).faces.length = (target X W).faces.length
  simp [source, target]

/-- Splitting the contextual source is signed-isomorphic to P1 expansion of the one-sided target
split. Untouched faces are retained through both fresh-edge embeddings. -/
def splitSourceSignedIsoExpandSplitTarget {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    SignedPresentationIso
      (P2.split (source X W) (sourceCut X W))
      (P1.expand (P2.split (target X W) (targetCut X W))
        (P2.freshEdge (target X W))) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 2)) (Fin (n + 2))
    exact EdgeRelabeling.refl _
  faceEquiv := middleFaceEquiv X W
  boundary_rotated := by
    intro f
    change
      (((P2.split (source X W) (sourceCut X W)).boundary f).map
        (EdgeRelabeling.refl (Fin (n + 2))).mapDart).IsRotated
        ((P1.expand (P2.split (target X W) (targetCut X W))
          (P2.freshEdge (target X W))).boundary
            (middleFaceEquiv X W f))
    erw [EdgeRelabeling.map_mapDart_refl]
    let i :=
      (P2.faceEquiv (source X W) (sourceCut X W)).symm f
    have hf :
        P2.faceEquiv (source X W) (sourceCut X W) i = f :=
      (P2.faceEquiv (source X W) (sourceCut X W)).apply_symm_apply f
    rw [← hf]
    induction i using Fin.lastCases with
    | last =>
        change
          (P2.split (source X W) (sourceCut X W)).boundary
              (P2.rightFace (source X W) (sourceCut X W)) |>.IsRotated
            ((P1.expand
                (P2.split (target X W) (targetCut X W))
                (P2.freshEdge (target X W))).boundary
                (middleFaceEquiv X W
                  (P2.rightFace (source X W) (sourceCut X W))))
        erw [middleFaceEquiv_rightFace, P1.expand_boundary,
          P2.split_boundary_right, P2.split_boundary_right]
        simp only [sourceCut, targetCut, P2Cut.canonical, source, target,
          P2.rightBoundary, P2.rightOrientedBoundary, P2.storedWord,
          P2.freshEdge]
        change
          (SignedDart.neg (Fin.last (n + 1)) ::
              P2.retainWord
                (SignedDart.neg (Fin.last n) :: P2.retainWord X)).IsRotated
            (P1.expandWord (Fin.last n)
              (SignedDart.neg (Fin.last n) :: P2.retainWord X))
        rw [show
          P1.expandWord (Fin.last n)
              (SignedDart.neg (Fin.last n) :: P2.retainWord X) =
            SignedDart.neg (Fin.last (n + 1)) ::
              P2.retainWord
                (SignedDart.neg (Fin.last n) :: P2.retainWord X) by
          rw [P1.expandWord_cons, P1.expandDart_neg_self,
            show
              P1.expandWord (Fin.last n) (P2.retainWord X) =
                P2.retainWord (P2.retainWord X) by
              simpa only [P1.freshEdge] using
                Cancellation.expandWord_retainWord_fresh X]
          rfl]
    | cast j =>
        induction j using Fin.cases with
        | zero =>
            change
              (P2.split (source X W) (sourceCut X W)).boundary
                  (P2.oldFace (source X W) (sourceCut X W) 0) |>.IsRotated
                ((P1.expand
                    (P2.split (target X W) (targetCut X W))
                    (P2.freshEdge (target X W))).boundary
                    (middleFaceEquiv X W
                    (P2.oldFace (source X W) (sourceCut X W) 0)))
            erw [middleFaceEquiv_oldFace, P1.expand_boundary]
            have hsourceZero :
                (0 : (source X W).Face) =
                  (sourceCut X W).face.face := by
              apply Fin.ext
              rfl
            have htargetZero :
                baseFaceEquiv X W (sourceCut X W).face.face =
                  (targetCut X W).face.face := by
              apply Fin.ext
              rfl
            rw [hsourceZero, P2.split_boundary_selected,
              htargetZero, P2.split_boundary_selected]
            simp only [source, List.cons_append, List.nil_append, sourceCut,
              List.length_cons, Fin.zero_eta, P2.selectedBoundary, P2.storedWord,
              Bool.false_eq_true, ↓reduceIte, P2.selectedOrientedBoundary,
              P2.freshEdge, target, P2.split_edgeCount, targetCut_left,
              P2.retainWord_nil, Dyck.inverseWord_singleton]
            simp only [P1.freshEdge, P2.retainWord, List.map_cons,
              P1.castSuccDart_pos, List.map_nil, List.cons_append,
              List.nil_append, P1.expandWord, targetCut, P2Cut.canonical,
              List.length_cons, Fin.zero_eta, Fin.coe_ofNat_eq_mod,
              orientedBoundary_length, Nat.zero_mod, List.take_zero,
              List.drop_zero, Bool.false_eq_true, ↓reduceIte,
              List.flatMap_cons, P1.expandDart, P1.firstSubedge,
              List.flatMap_nil, List.append_nil]
            exact List.IsRotated.refl _
        | succ k =>
            change
              (P2.split (source X W) (sourceCut X W)).boundary
                  (P2.oldFace (source X W) (sourceCut X W) k.succ) |>.IsRotated
                ((P1.expand
                    (P2.split (target X W) (targetCut X W))
                    (P2.freshEdge (target X W))).boundary
                    (middleFaceEquiv X W
                    (P2.oldFace (source X W) (sourceCut X W) k.succ)))
            erw [middleFaceEquiv_oldFace, P1.expand_boundary,
              P2.split_boundary_old_of_ne, P2.split_boundary_old_of_ne]
            · let kW : Fin W.length :=
                ⟨k.val, by simpa using k.isLt⟩
              have hsourceBoundary :
                  (source X W).boundary k.succ =
                    P2.retainWord (W.get kW) := by
                simp [source, FiniteCyclicPresentation.boundary, kW]
              have htargetBoundary :
                  (target X W).boundary
                      (baseFaceEquiv X W k.succ) =
                    W.get kW := by
                simp [target, baseFaceEquiv,
                  FiniteCyclicPresentation.boundary, kW]
              rw [hsourceBoundary, htargetBoundary]
              change
                (P2.retainWord (P2.retainWord (W.get kW))).IsRotated
                  (P1.expandWord (P1.freshEdge n)
                    (P2.retainWord (W.get kW)))
              rw [Cancellation.expandWord_retainWord_fresh]
            · intro h
              have hval := congrArg Fin.val h
              change k.val + 1 = 0 at hval
              omega
            · intro h
              have hval := congrArg Fin.val h
              change k.val + 1 = 0 at hval
              omega

/-- Gallier--Xu Step 1 inside a multi-face context: split the displayed pair, contract the
resulting two-edge paths, and merge the monogon, leaving all other faces untouched. -/
theorem normalizationEquivalent {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hX : X ≠ [])
    (validSource : (source X W).IsSurfaceValid)
    (validTarget : (target X W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source X W, validSource⟩
      ⟨target X W, validTarget⟩ := by
  let sourceSplit := P2.split (source X W) (sourceCut X W)
  let targetSplit := P2.split (target X W) (targetCut X W)
  let expandedTargetSplit :=
    P1.expand targetSplit (P2.freshEdge (target X W))
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source X W) (sourceCut X W) validSource
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (target X W) (targetCut X W) validTarget
  let middleIso :
      SignedPresentationIso sourceSplit expandedTargetSplit :=
    splitSourceSignedIsoExpandSplitTarget X W
  let validExpandedFromIso : expandedTargetSplit.IsSurfaceValid :=
    middleIso.isSurfaceValid validSourceSplit
  let validCanonicalExpanded : expandedTargetSplit.IsSurfaceValid :=
    P1.expand_isSurfaceValid targetSplit
      (P2.freshEdge (target X W)) validTargetSplit
  have hsource :
      NormalizationEquivalent
        ⟨source X W, validSource⟩
        ⟨sourceSplit, validSourceSplit⟩ :=
    NormalizationEquivalent.ofP2
      (P2Subdivision.canonical
        (source X W) (sourceCut X W)
        (sourceCut_isNondegenerate X W))
  have hiso :
      NormalizationEquivalent
        ⟨sourceSplit, validSourceSplit⟩
        ⟨expandedTargetSplit, validExpandedFromIso⟩ :=
    NormalizationEquivalent.ofSignedIso middleIso
  have hexpandedNode :
      (⟨expandedTargetSplit, validExpandedFromIso⟩ : ValidPresentation) =
        ⟨expandedTargetSplit, validCanonicalExpanded⟩ := by
    apply ValidPresentation.ext
    rfl
  rw [hexpandedNode] at hiso
  have hcontract :
      NormalizationEquivalent
        ⟨expandedTargetSplit, validCanonicalExpanded⟩
        ⟨targetSplit, validTargetSplit⟩ :=
    P1.contractionNormalizationEquivalent targetSplit
      (P2.freshEdge (target X W)) validTargetSplit
  have htarget :
      NormalizationEquivalent
        ⟨targetSplit, validTargetSplit⟩
        ⟨target X W, validTarget⟩ := by
    apply P2.oneSidedMergeNormalizationEquivalent
    exact Or.inl
      ⟨targetCut_left X W,
        List.length_pos_iff_ne_nil.mpr hX⟩
  exact hsource.trans (hiso.trans (hcontract.trans htarget))

/-- Public realization-invariance form of contextual inverse-pair cancellation. -/
theorem polygonallyEquivalent {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hX : X ≠ [])
    (validSource : (source X W).IsSurfaceValid)
    (validTarget : (target X W).IsSurfaceValid) :
    (source X W).PolygonallyEquivalent
      (target X W) validSource validTarget :=
  (normalizationEquivalent
    X W hX validSource validTarget).polygonallyEquivalent

/-- Transport contextual cancellation across arbitrary edge names, face orders, orientations,
and cyclic starting points supplied by signed presentation isomorphisms. -/
theorem normalizationEquivalentOfSignedIsos
    {P Q : FiniteCyclicPresentation} {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hX : X ≠ [])
    (sourceIso : SignedPresentationIso P (source X W))
    (targetIso : SignedPresentationIso (target X W) Q)
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨Q, validQ⟩ := by
  let validContextSource : (source X W).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validContextTarget : (target X W).IsSurfaceValid :=
    targetIso.symm.isSurfaceValid validQ
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent
          X W hX validContextSource validContextTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso))

end Context

/-- Transport base cancellation across arbitrary signed presentation isomorphisms. This is the
stable constructor used after rotating a face and renaming its cancellable edge to the last
index. -/
theorem normalizationEquivalentOfSignedIsos
    {P Q : FiniteCyclicPresentation} {n : ℕ}
    (X : List (SignedDart (Fin n))) (hX : X ≠ [])
    (sourceIso : SignedPresentationIso P (source X))
    (targetIso : SignedPresentationIso (target X) Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent ⟨P, validP⟩ ⟨Q, validQ⟩ := by
  let validSource : (source X).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validTarget : (target X).IsSurfaceValid :=
    target_isSurfaceValid X hX validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent X hX validSource).trans
        (NormalizationEquivalent.ofSignedIso targetIso))

/-- Cancellation preserves faithful polygonal realization, in the transported public form. -/
theorem polygonallyEquivalentOfSignedIsos
    {P Q : FiniteCyclicPresentation} {n : ℕ}
    (X : List (SignedDart (Fin n))) (hX : X ≠ [])
    (sourceIso : SignedPresentationIso P (source X))
    (targetIso : SignedPresentationIso (target X) Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  (normalizationEquivalentOfSignedIsos
    X hX sourceIso targetIso validP validQ).polygonallyEquivalent

/-- Cancel a positively displayed adjacent inverse pair with an arbitrary edge name. -/
theorem namedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (namedSource a X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨namedSource a X, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid validSource)⟩ := by
  let sourceIso := namedSourceSignedIso a X ha
  let validBase : (source (lowerTail a X)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      (normalizationEquivalent (lowerTail a X) hlower validBase)

/-- A one-face word with a negatively displayed inverse pair. -/
@[reducible]
def negativeNamedSource {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.neg a, .pos a] ++ X)

/-- Reverse only the displayed edge to turn negative cancellation into positive cancellation. -/
def negativeNamedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeNamedSource a X) (namedSource a X) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_cons, List.map_nil,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos]
    rw [Dyck.reverseEdgeRelabeling_word a X ha]

/-- Cancel a negatively displayed adjacent inverse pair. -/
theorem negativeNamedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (negativeNamedSource a X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeNamedSource a X, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((negativeNamedSourceSignedIso a X ha).isSurfaceValid
              validSource))⟩ := by
  let signIso := negativeNamedSourceSignedIso a X ha
  let validPositive : (namedSource a X).IsSurfaceValid :=
    signIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso signIso).trans
      (namedNormalizationEquivalent a X ha hlower validPositive)

/-- Cancel a positive adjacent inverse pair exposed by a cyclic rotation. -/
theorem normalizationEquivalentOfIsRotated {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (hrotated : word.IsRotated ([.pos a, .neg a] ++ X))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (Dyck.oneFace word).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((Dyck.oneFaceSignedIsoOfIsRotated hrotated).isSurfaceValid
              validSource))⟩ := by
  let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
  let validNamed : (namedSource a X).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso rotation).trans
      (namedNormalizationEquivalent a X ha hlower validNamed)

/-- Cancel a negative adjacent inverse pair exposed by a cyclic rotation. -/
theorem negativeNormalizationEquivalentOfIsRotated {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (hrotated : word.IsRotated ([.neg a, .pos a] ++ X))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (Dyck.oneFace word).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((negativeNamedSourceSignedIso a X ha).isSurfaceValid
              ((Dyck.oneFaceSignedIsoOfIsRotated hrotated).isSurfaceValid
                validSource)))⟩ := by
  let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
  let validNamed : (negativeNamedSource a X).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso rotation).trans
      (negativeNamedNormalizationEquivalent
        a X ha hlower validNamed)

end Cancellation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification24_block_06
/- END ClassificationOfSurfaces.FiniteCyclicCancellation -/
