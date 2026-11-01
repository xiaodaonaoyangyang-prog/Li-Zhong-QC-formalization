/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification25: pinned classification sources; see BUNDLE_MAP.json. -/
import LiZhongExternal.Classification.SchottkyClassification24
import LiZhongExternal.Classification.SchottkyClassification20

/- BEGIN ClassificationOfSurfaces.FiniteCyclicFaceMerge | 12e43ecb90dd109e376d18dfbf03d37ff4b8412fa34917add26494d107cd2ac7 -/
noncomputable section

section schottkyclassification25_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Exact two-face merging for finite cyclic presentations

Two displayed faces separated by a last-index edge are the canonical P2 split of the
concatenation of their old boundary words, up to rotating the first child.  This supplies the
local merge used to reduce a connected presentation to one face.  It covers both ordinary
nondegenerate cuts and the one-sided monogon case.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace FaceMerge

/-- The one-face presentation obtained after merging the displayed pair. -/
@[reducible]
def target {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (U ++ V)

/-- Two displayed faces sharing only the last-index separator in the shown positions. -/
@[reducible]
def source {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    [[.pos (P1.freshEdge n)] ++ P2.retainWord U,
      [.neg (P1.freshEdge n)] ++ P2.retainWord V]

/-- The canonical cut of the concatenated target word between `U` and `V`. -/
def targetCut {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    P2Cut (target U V) where
  face := ⟨0, false⟩
  left := U
  right := V
  boundary_rotated := List.IsRotated.refl _

@[simp]
theorem targetCut_left {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).left = U :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).right = V :=
  rfl

/-- The displayed two-face source differs from the canonical target split only by rotating its
first child boundary. -/
def sourceSignedIsoSplitTarget {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    SignedPresentationIso
      (source U V) (P2.split (target U V) (targetCut U V)) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 1)) (Fin (n + 1))
    exact EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    change
      (((source U V).boundary f).map
        (EdgeRelabeling.refl (Fin (n + 1))).mapDart).IsRotated
        ((P2.split (target U V) (targetCut U V)).boundary f)
    rw [EdgeRelabeling.map_mapDart_refl]
    fin_cases f
    · change
        ([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).IsRotated
          (P2.retainWord U ++
            [SignedDart.pos (P1.freshEdge n)])
      exact List.isRotated_append
    · change
        ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).IsRotated
          ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V)
      exact List.IsRotated.refl _

/-- Merging preserves ordinary validity whenever the resulting face is nonempty. -/
theorem target_isSurfaceValid {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (target U V).IsSurfaceValid := by
  classical
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa [target, Dyck.oneFace_boundary] using hUV
  · intro f g _h
    exact (Dyck.oneFace_face_eq_zero (U ++ V) f).trans
      (Dyck.oneFace_face_eq_zero (U ++ V) g).symm
  · intro e
    have hmultiplicity := validSource.2.2.2 e.castSucc
    change
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 1 ∨
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 2
        at hmultiplicity
    rw [Fin.sum_univ_two] at hmultiplicity
    change
      ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 1) ∨
        ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 2)
        at hmultiplicity
    have hne : P1.freshEdge n ≠ e.castSucc :=
      (P1.firstSubedge_ne_freshEdge e).symm
    simp only [List.map_append, List.map_cons, List.map_nil,
      edgeOfDart, List.count_append, List.count_cons,
      List.count_nil] at hmultiplicity
    simp only [beq_iff_eq, hne, ↓reduceIte, add_zero, zero_add] at hmultiplicity
    rw [P2.count_retainWord_castSucc,
      P2.count_retainWord_castSucc] at hmultiplicity
    rw [Dyck.oneFace_edgeMultiplicity]
    change
      ((U ++ V).map edgeOfDart).count e = 1 ∨
        ((U ++ V).map edgeOfDart).count e = 2
    simpa [List.map_append, List.count_append] using hmultiplicity

/-- The canonical cut is ordinary whenever the concatenated target is nonempty: it is either
nondegenerate or exactly one-sided-degenerate. -/
theorem targetCut_isOrdinary {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ []) :
    (targetCut U V).IsNondegenerate ∨
      ((targetCut U V).left = [] ∧
          0 < (targetCut U V).right.length) ∨
        (0 < (targetCut U V).left.length ∧
          (targetCut U V).right = []) := by
  by_cases hU : U = []
  · right
    left
    subst U
    exact ⟨rfl, List.length_pos_iff_ne_nil.mpr (by simpa using hUV)⟩
  · by_cases hV : V = []
    · right
      right
      exact ⟨List.length_pos_iff_ne_nil.mpr hU, hV⟩
    · left
      exact ⟨hU, hV⟩

/-- Merge the displayed two faces into their concatenated one-face presentation. -/
theorem normalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V, validSource⟩
      ⟨target U V,
        target_isSurfaceValid U V hUV validSource⟩ := by
  let splitTarget := P2.split (target U V) (targetCut U V)
  let sourceIso := sourceSignedIsoSplitTarget U V
  let validSplit : splitTarget.IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validTarget : (target U V).IsSurfaceValid :=
    target_isSurfaceValid U V hUV validSource
  have hsplit :
      NormalizationEquivalent
        ⟨source U V, validSource⟩
        ⟨splitTarget, validSplit⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  have hmerge :
      NormalizationEquivalent
        ⟨splitTarget, validSplit⟩
        ⟨target U V, validTarget⟩ := by
    have hcanonical :=
      P2.ordinaryMergeNormalizationEquivalent
        (target U V) (targetCut U V)
        (targetCut_isOrdinary U V hUV) validTarget
    exact hcanonical
  exact hsplit.trans hmerge

/-- Public realization-invariance form of exact two-face merging. -/
theorem polygonallyEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (source U V).PolygonallyEquivalent
      (target U V) validSource
      (target_isSurfaceValid U V hUV validSource) :=
  (normalizationEquivalent U V hUV validSource).polygonallyEquivalent

/-! ### Merging through an arbitrary signed-isomorphic split -/

/-- Any presentation signed-isomorphic to an ordinary canonical P2 split can be merged.
This is the stable interface used when the two child faces occur among additional untouched
faces: all face ordering and edge naming is confined to `sourceIso`. -/
theorem normalizationEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨Q, validQ⟩ := by
  let validSplitFromIso : (P2.split Q cut).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validCanonicalSplit : (P2.split Q cut).IsSurfaceValid :=
    P2.split_isSurfaceValid Q cut validQ
  have hsplitNode :
      (⟨P2.split Q cut, validSplitFromIso⟩ : ValidPresentation) =
        ⟨P2.split Q cut, validCanonicalSplit⟩ := by
    apply ValidPresentation.ext
    rfl
  have hsource :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨P2.split Q cut, validSplitFromIso⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  rw [hsplitNode] at hsource
  exact hsource.trans
    (P2.ordinaryMergeNormalizationEquivalent Q cut hcut validQ)

/-- Public realization-invariance form of merging through a signed-isomorphic split. -/
theorem polygonallyEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  (normalizationEquivalentOfSignedIso
    cut hcut sourceIso validP validQ).polygonallyEquivalent

/-! ### A merge among untouched faces -/

namespace ContextMerge

/-- Merge `U` and `V` into the first face while retaining the remaining face words `W`. -/
@[reducible]
def target {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n
  faces := (U ++ V) :: W

/-! ### Marked merging

Deleting the separating edge immediately can make the merged word cyclically equal to an
untouched face.  The marked merge instead retains that edge as an adjacent inverse pair.  Its
two occurrences distinguish the merged face from every untouched face, so ordinary validity is
preserved.  A later contextual cancellation removes the marker after the face-merging recursion
has finished.
-/

/-- Merge the first and last displayed children while retaining their separator as an adjacent
inverse pair in the merged face. -/
@[reducible]
def markedTarget {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    (P2.retainWord U ++
      [.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
      P2.retainWord V) ::
      W.map P2.retainWord

/-- Cut the marked merged face immediately after the positive marker occurrence. -/
def markedTargetCut {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (markedTarget U V W) where
  face := ⟨⟨0, by simp [markedTarget]⟩, false⟩
  left := P2.retainWord U ++ [.pos (P1.freshEdge n)]
  right := [.neg (P1.freshEdge n)] ++ P2.retainWord V
  boundary_rotated := by
    change
      (P2.retainWord U ++
          [SignedDart.pos (P1.freshEdge n),
            SignedDart.neg (P1.freshEdge n)] ++
          P2.retainWord V).IsRotated
        ((P2.retainWord U ++
            [SignedDart.pos (P1.freshEdge n)]) ++
          ([SignedDart.neg (P1.freshEdge n)] ++ P2.retainWord V))
    simpa only [List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
      (List.IsRotated.refl
        (P2.retainWord U ++
          [SignedDart.pos (P1.freshEdge n),
            SignedDart.neg (P1.freshEdge n)] ++
          P2.retainWord V))

theorem markedTargetCut_isNondegenerate {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (markedTargetCut U V W).IsNondegenerate := by
  constructor <;> simp [markedTargetCut]

/-- The canonical cut of the first face of a contextual merge. -/
def targetCut {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (target U V W) where
  face := ⟨⟨0, by simp [target]⟩, false⟩
  left := U
  right := V
  boundary_rotated := List.IsRotated.refl _

@[simp]
theorem targetCut_left {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut U V W).left = U :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut U V W).right = V :=
  rfl

/-- The canonical source for merging in context is the exact P2 split of the target. -/
@[reducible]
def source {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation :=
  P2.split (target U V W) (targetCut U V W)

/-- Match the face positions of the expanded contextual source with the split marked target. -/
def markedMiddleFaceEquiv {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (P1.expand (source U V W) (P1.freshEdge n)).Face ≃
      (P2.split (markedTarget U V W) (markedTargetCut U V W)).Face :=
  finCongr (by
    erw [P1.expand_faces_length]
    change
      (P2.split (target U V W)
          (targetCut U V W)).faces.length =
        (P2.split (markedTarget U V W)
          (markedTargetCut U V W)).faces.length
    rw [P2.split_faces_length, P2.split_faces_length]
    simp [target, markedTarget])

@[simp]
theorem markedMiddleFaceEquiv_apply_val {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (P1.expand (source U V W) (P1.freshEdge n)).Face) :
    (markedMiddleFaceEquiv U V W f).val = f.val :=
  rfl

@[simp]
theorem markedMiddleFaceEquiv_oldFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (target U V W).Face) :
    markedMiddleFaceEquiv U V W
        (P1.faceEquiv (source U V W) (P1.freshEdge n)
          (P2.oldFace (target U V W) (targetCut U V W) f)) =
      P2.oldFace (markedTarget U V W) (markedTargetCut U V W)
        ⟨f.val, by
          change f.val < (W.map P2.retainWord).length + 1
          simpa [target] using f.isLt⟩ := by
  apply Fin.ext
  change f.val = f.val
  rfl

@[simp]
theorem markedMiddleFaceEquiv_rightFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    markedMiddleFaceEquiv U V W
        (P1.faceEquiv (source U V W) (P1.freshEdge n)
          (P2.rightFace (target U V W) (targetCut U V W))) =
      P2.rightFace (markedTarget U V W) (markedTargetCut U V W) := by
  apply Fin.ext
  change (target U V W).faces.length =
    (markedTarget U V W).faces.length
  simp [target, markedTarget]

/-- The child occupying the selected old-face position. -/
def selectedFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).Face :=
  P2.oldFace (target U V W) (targetCut U V W)
    (targetCut U V W).face.face

/-- The child appended by the P2 split. -/
def rightFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).Face :=
  P2.rightFace (target U V W) (targetCut U V W)

/-- The target face occupied by the `i`th untouched word. -/
def untouchedTargetFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (target U V W).Face :=
  ⟨i.val + 1, by
    change i.val + 1 < ((U ++ V) :: W).length
    simp only [List.length_cons]
    omega⟩

/-- The source face occupied by the `i`th untouched word. -/
def untouchedSourceFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (source U V W).Face :=
  P2.oldFace (target U V W) (targetCut U V W)
    (untouchedTargetFace U V W i)

@[simp]
theorem source_boundary_selected {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).boundary (selectedFace U V W) =
      P2.retainWord U ++ [.pos (P1.freshEdge n)] := by
  simp [source, selectedFace, targetCut, P2.selectedBoundary,
    P2.selectedOrientedBoundary, P2.freshEdge, target]
  rfl

@[simp]
theorem source_boundary_right {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).boundary (rightFace U V W) =
      [.neg (P1.freshEdge n)] ++ P2.retainWord V := by
  simp [source, rightFace, targetCut, P2.rightBoundary,
    P2.rightOrientedBoundary, P2.freshEdge, target]
  rfl

@[simp]
theorem target_boundary_untouched {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (target U V W).boundary (untouchedTargetFace U V W i) =
      W.get i := by
  simp [target, untouchedTargetFace,
    FiniteCyclicPresentation.boundary]

@[simp]
theorem source_boundary_untouched {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (source U V W).boundary (untouchedSourceFace U V W i) =
      P2.retainWord (W.get i) := by
  change
    (P2.split (target U V W) (targetCut U V W)).boundary
        (P2.oldFace (target U V W) (targetCut U V W)
          (untouchedTargetFace U V W i)) =
      P2.retainWord (W.get i)
  rw [P2.split_boundary_old_of_ne]
  · rw [target_boundary_untouched]
  · intro h
    have hval := congrArg Fin.val h
    change i.val + 1 = 0 at hval
    omega

/-- P1 expansion of the retained separator in the contextual source is signed-isomorphic to the
P2 split of the marked target. -/
def expandSourceSignedIsoSplitMarkedTarget {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    SignedPresentationIso
      (P1.expand (source U V W) (P1.freshEdge n))
      (P2.split (markedTarget U V W) (markedTargetCut U V W)) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 2)) (Fin (n + 2))
    exact EdgeRelabeling.refl _
  faceEquiv := markedMiddleFaceEquiv U V W
  boundary_rotated := by
    intro f
    let p :=
      (P1.faceEquiv (source U V W) (P1.freshEdge n)).symm f
    have hf :
        P1.faceEquiv (source U V W) (P1.freshEdge n) p = f :=
      (P1.faceEquiv (source U V W)
        (P1.freshEdge n)).apply_symm_apply f
    rw [← hf]
    erw [P1.expand_boundary]
    have hmap :
        (P1.expandWord (P1.freshEdge n)
            ((source U V W).boundary p)).map
              (EdgeRelabeling.refl (Fin (n + 2))).mapDart =
          P1.expandWord (P1.freshEdge n)
            ((source U V W).boundary p) :=
      EdgeRelabeling.map_mapDart_refl _
    refine Eq.mpr
      (congrArg
        (fun word ↦ word.IsRotated
          ((P2.split (markedTarget U V W)
            (markedTargetCut U V W)).boundary
              (markedMiddleFaceEquiv U V W
                (P1.faceEquiv (source U V W)
                  (P1.freshEdge n) p))))
        hmap) ?_
    rcases P2.face_cases (target U V W) (targetCut U V W) p with
      ⟨q, hq⟩ | hq
    · rw [hq]
      rw [markedMiddleFaceEquiv_oldFace]
      induction q using Fin.cases with
      | zero =>
          have hsourceBoundary :
              (source U V W).boundary
                  (P2.oldFace (target U V W) (targetCut U V W) 0) =
                P2.selectedBoundary (target U V W)
                  (targetCut U V W) := by
            rw [P2.split_boundary_old]
            simp [targetCut] <;> rfl
          have htargetBoundary :
              (P2.split (markedTarget U V W)
                  (markedTargetCut U V W)).boundary
                    (P2.oldFace (markedTarget U V W)
                      (markedTargetCut U V W)
                      ⟨(0 : (target U V W).Face).val, by
                        change 0 <
                          (W.map P2.retainWord).length + 1
                        simp⟩) =
                P2.selectedBoundary (markedTarget U V W)
                  (markedTargetCut U V W) := by
            rw [P2.split_boundary_old]
            simp [markedTargetCut] <;> rfl
          rw [hsourceBoundary, htargetBoundary]
          simp only [targetCut, markedTargetCut,
            P2.selectedBoundary, P2.selectedOrientedBoundary,
            P2.storedWord, Bool.false_eq_true, if_false,
            P2.freshEdge]
          rw [P1.expandWord_append,
            Cancellation.expandWord_retainWord_fresh,
            P1.expandWord_singleton, P1.expandDart_pos_self]
          simp only [P2.retainWord, List.map_map, P1.firstSubedge, P1.freshEdge, List.map_append,
            List.map_cons, P1.castSuccDart_pos, List.map_nil, List.append_assoc, List.cons_append,
            List.nil_append]
          exact List.IsRotated.refl _
      | succ i =>
          let iW : Fin W.length :=
            ⟨i.val, by simp [target]⟩
          have hsource :
              (source U V W).boundary
                  (P2.oldFace (target U V W) (targetCut U V W)
                    i.succ) =
                P2.retainWord (W.get iW) := by
            rw [P2.split_boundary_old_of_ne]
            · simp [target, FiniteCyclicPresentation.boundary, iW] <;> rfl
            · intro h
              have hval := congrArg Fin.val h
              change i.val + 1 = 0 at hval
              omega
          rw [hsource]
          rw [show
            P1.expandWord (P1.freshEdge n)
                (P2.retainWord (W.get iW)) =
              P2.retainWord (P2.retainWord (W.get iW)) by
            exact Cancellation.expandWord_retainWord_fresh _]
          rw [P2.split_boundary_old_of_ne]
          · simp only [P2.retainWord, Fin.eta, List.get_eq_getElem, List.map_map,
              markedTarget, FiniteCyclicPresentation.boundary, List.length_cons,
              Fin.val_succ, List.append_assoc, List.cons_append, List.nil_append,
              List.getElem_cons_succ, List.getElem_map, iW]
            exact List.IsRotated.refl _
          · intro h
            have hval := congrArg Fin.val h
            change i.val + 1 = 0 at hval
            omega
    · rw [hq]
      rw [markedMiddleFaceEquiv_rightFace,
        P2.split_boundary_right, P2.split_boundary_right]
      simp only [targetCut, markedTargetCut, P2.rightBoundary,
        P2.rightOrientedBoundary, P2.storedWord, if_false,
        Bool.false_eq_true, P2.freshEdge]
      rw [P1.expandWord_cons, P1.expandDart_neg_self,
        Cancellation.expandWord_retainWord_fresh]
      simp only [P1.freshEdge, P1.firstSubedge, P2.retainWord, List.map_map, List.cons_append,
        List.nil_append, List.map_cons, P1.castSuccDart_neg]
      exact List.IsRotated.refl _

@[simp]
theorem markedTarget_boundary_zero {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (markedTarget U V W).boundary 0 =
      P2.retainWord U ++
        [.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
        P2.retainWord V :=
  rfl

@[simp]
theorem markedTarget_boundary_succ {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (markedTarget U V W).boundary
        ⟨i.val + 1, by
          change i.val + 1 < (W.map P2.retainWord).length + 1
          simp⟩ =
      P2.retainWord (W.get i) := by
  simp [markedTarget, FiniteCyclicPresentation.boundary]

@[simp]
theorem markedTarget_boundary_succMap {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin (W.map P2.retainWord).length) :
    (markedTarget U V W).boundary i.succ =
      P2.retainWord
        (W.get ⟨i.val, by simpa using i.isLt⟩) := by
  let iW : Fin W.length := ⟨i.val, by simpa using i.isLt⟩
  have hface :
      i.succ =
        (⟨iW.val + 1, by
          change iW.val + 1 < (W.map P2.retainWord).length + 1
          simp⟩ : (markedTarget U V W).Face) := by
    apply Fin.ext
    rfl
  rw [hface, markedTarget_boundary_succ]

/-- The adjacent inverse marker makes the merged face distinct from every untouched face, so a
marked merge preserves the project's strict ordinary validity predicate. -/
theorem markedTarget_isSurfaceValid {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    (markedTarget U V W).IsSurfaceValid := by
  classical
  let marker := P1.freshEdge n
  let validExpanded :
      (P1.expand (source U V W) marker).IsSurfaceValid :=
    P1.expand_isSurfaceValid (source U V W) marker validSource
  let middleIso :=
    expandSourceSignedIsoSplitMarkedTarget U V W
  let validSplit :
      (P2.split (markedTarget U V W)
        (markedTargetCut U V W)).IsSurfaceValid :=
    middleIso.isSurfaceValid validExpanded
  refine ⟨⟨0, by simp [markedTarget]⟩, ?_, ?_, ?_⟩
  · intro f
    induction f using Fin.cases with
    | zero =>
        rw [markedTarget_boundary_zero]
        simp
    | succ i =>
        let iW : Fin W.length :=
          ⟨i.val, by simpa using i.isLt⟩
        have hsourceNonempty :=
          validSource.2.1
            (untouchedSourceFace U V W iW)
        rw [source_boundary_untouched] at hsourceNonempty
        rw [markedTarget_boundary_succMap]
        intro hnil
        apply hsourceNonempty
        exact (P2.retainWord_eq_nil_iff _).mpr
          (by simpa [iW] using hnil)
  · intro f g hfg
    induction f using Fin.cases with
    | zero =>
        induction g using Fin.cases with
        | zero => rfl
        | succ j =>
            let jW : Fin W.length :=
              ⟨j.val, by simpa using j.isLt⟩
            have hmarker :
                SignedDart.pos marker ∈
                  (markedTarget U V W).boundary 0 := by
              simp [marker]
            have htarget := hfg.mem_iff.mp hmarker
            rw [markedTarget_boundary_succMap] at htarget
            have hmarkerEq :
                P2.freshEdge (target U V W) = marker := by
              apply Fin.ext
              rfl
            have hnot :
                SignedDart.pos marker ∉
                  P2.retainWord (W.get jW) := by
              rw [← hmarkerEq]
              exact
                P2.pos_freshEdge_not_mem_retainWord
                  (target U V W) (W.get jW)
            exact (hnot (by simpa [jW] using htarget)).elim
    | succ i =>
        induction g using Fin.cases with
        | zero =>
            let iW : Fin W.length :=
              ⟨i.val, by simpa using i.isLt⟩
            have hmarker :
                SignedDart.pos marker ∈
                  (markedTarget U V W).boundary 0 := by
              simp [marker]
            have hsource := hfg.symm.mem_iff.mp hmarker
            rw [markedTarget_boundary_succMap] at hsource
            have hmarkerEq :
                P2.freshEdge (target U V W) = marker := by
              apply Fin.ext
              rfl
            have hnot :
                SignedDart.pos marker ∉
                  P2.retainWord (W.get iW) := by
              rw [← hmarkerEq]
              exact
                P2.pos_freshEdge_not_mem_retainWord
                  (target U V W) (W.get iW)
            exact (hnot (by simpa [iW] using hsource)).elim
        | succ j =>
            let iW : Fin W.length :=
              ⟨i.val, by simpa using i.isLt⟩
            let jW : Fin W.length :=
              ⟨j.val, by simpa using j.isLt⟩
            have hboundaries :
                (P2.retainWord (W.get iW)).IsRotated
                  (P2.retainWord (W.get jW)) := by
              rw [markedTarget_boundary_succMap,
                markedTarget_boundary_succMap] at hfg
              simpa [iW, jW] using hfg
            have hsourceBoundaries :
                ((source U V W).boundary
                    (untouchedSourceFace U V W iW)).IsRotated
                  ((source U V W).boundary
                    (untouchedSourceFace U V W jW)) := by
              rw [source_boundary_untouched,
                source_boundary_untouched]
              exact hboundaries
            have hsourceFaces :=
              validSource.2.2.1
                (untouchedSourceFace U V W iW)
                (untouchedSourceFace U V W jW)
                hsourceBoundaries
            apply Fin.ext
            have hval := congrArg Fin.val hsourceFaces
            have holdVal (k : Fin W.length) :
                (untouchedSourceFace U V W k).val =
                  k.val + 1 :=
              rfl
            rw [holdVal iW, holdVal jW] at hval
            have hij : iW.val = jW.val :=
              Nat.add_right_cancel hval
            simpa [iW, jW] using hij
  · intro e
    rw [P2.edgeMultiplicity_split_castSucc
      (markedTarget U V W) (markedTargetCut U V W) e]
    exact validSplit.2.2.2 e.castSucc

/-- The validity-safe marked merge preserves face-incidence connectivity. -/
theorem markedTarget_isConnected {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (connectedSource : (source U V W).IsConnected) :
    (markedTarget U V W).IsConnected := by
  have connectedExpanded :
      (P1.expand (source U V W) (P1.freshEdge n)).IsConnected :=
    P1.expand_isConnected
      (source U V W) (P1.freshEdge n) connectedSource
  have connectedSplit :
      (P2.split (markedTarget U V W)
        (markedTargetCut U V W)).IsConnected :=
    (expandSourceSignedIsoSplitMarkedTarget U V W).isConnected
      connectedExpanded
  exact P2.isConnected_of_split
    (markedTarget U V W) (markedTargetCut U V W) connectedSplit

/-- The validity-safe marked merge is a common P1/P2 subdivision: expand the old separator in
the source and cut the marked parent along the fresh second subedge. -/
theorem markedNormalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V W, validSource⟩
      ⟨markedTarget U V W,
        markedTarget_isSurfaceValid U V W validSource⟩ := by
  let expandedSource :=
    P1.expand (source U V W) (P1.freshEdge n)
  let splitMarked :=
    P2.split (markedTarget U V W) (markedTargetCut U V W)
  have hsourceExpanded :
      Subdivides (source U V W) expandedSource :=
    Subdivides.p1
      (P1Subdivision.canonical
        (source U V W) (P1.freshEdge n))
  have hexpandedSplit :
      Subdivides expandedSource splitMarked :=
    Subdivides.signedIso
      (expandSourceSignedIsoSplitMarkedTarget U V W)
  have htargetSplit :
      Subdivides (markedTarget U V W) splitMarked :=
    Subdivides.p2
      (P2Subdivision.canonical
        (markedTarget U V W) (markedTargetCut U V W)
        (markedTargetCut_isNondegenerate U V W))
  exact NormalizationEquivalent.ofCommonSubdivision
    ⟨splitMarked, hsourceExpanded.trans hexpandedSplit,
      htargetSplit⟩

/-- Faithful realization invariance of the validity-safe marked merge. -/
theorem markedPolygonallyEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    (source U V W).PolygonallyEquivalent
      (markedTarget U V W) validSource
      (markedTarget_isSurfaceValid U V W validSource) :=
  (markedNormalizationEquivalent U V W validSource).polygonallyEquivalent

/-- The contextual cut is ordinary exactly under the same nonempty condition as the two-face
special case. -/
theorem targetCut_isOrdinary {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ []) :
    (targetCut U V W).IsNondegenerate ∨
      ((targetCut U V W).left = [] ∧
          0 < (targetCut U V W).right.length) ∨
        (0 < (targetCut U V W).left.length ∧
          (targetCut U V W).right = []) := by
  by_cases hU : U = []
  · right
    left
    subst U
    exact ⟨rfl, List.length_pos_iff_ne_nil.mpr (by simpa using hUV)⟩
  · by_cases hV : V = []
    · right
      right
      exact ⟨List.length_pos_iff_ne_nil.mpr hU, hV⟩
    · left
      exact ⟨hU, hV⟩

/-- A validity-safe contextual merge. The target-validity hypothesis is explicit because merging
can make two cyclic face words coincide, while `IsSurfaceValid` deliberately excludes duplicate
faces. -/
theorem normalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ [])
    (validTarget : (target U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V W,
        P2.split_isSurfaceValid
          (target U V W) (targetCut U V W) validTarget⟩
      ⟨target U V W, validTarget⟩ :=
  P2.ordinaryMergeNormalizationEquivalent
    (target U V W) (targetCut U V W)
    (targetCut_isOrdinary U V W hUV) validTarget

/-- Transport a contextual merge across the face ordering and edge naming of an arbitrary
source presentation. -/
theorem normalizationEquivalentOfSignedIso
    {P : FiniteCyclicPresentation} {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ [])
    (sourceIso : SignedPresentationIso P (source U V W))
    (validP : P.IsSurfaceValid)
    (validTarget : (target U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨target U V W, validTarget⟩ :=
  FaceMerge.normalizationEquivalentOfSignedIso
    (targetCut U V W) (targetCut_isOrdinary U V W hUV)
    sourceIso validP validTarget

end ContextMerge

/-! ### Arbitrary separator names -/

/-- Two displayed faces with an arbitrarily named, oppositely oriented separator. -/
@[reducible]
def namedSource {n : ℕ} (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces := [[.pos a] ++ U, [.neg a] ++ V]

/-- Rename the separator to last and delete that name from both remaining face words. -/
def namedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart) :
    SignedPresentationIso
      (namedSource a U V)
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv (Cancellation.moveToLast a)
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    fin_cases f
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.pos a)] ++
          Cancellation.renamedTail a U).IsRotated
          ([.pos (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a U))
      rw [Cancellation.retainWord_lowerTail a U haU]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.pos a) =
            .pos (P1.freshEdge n) by simp [hmove]]
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.neg a)] ++
          Cancellation.renamedTail a V).IsRotated
          ([.neg (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a V))
      rw [Cancellation.retainWord_lowerTail a V haV]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.neg a) =
            .neg (P1.freshEdge n) by simp [hmove]]

/-- Merge two displayed faces with an arbitrary separator name. -/
theorem namedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (hUV :
      Cancellation.lowerTail a U ++
        Cancellation.lowerTail a V ≠ [])
    (validSource : (namedSource a U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨namedSource a U V, validSource⟩
      ⟨target
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V),
        target_isSurfaceValid
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V) hUV
          ((namedSourceSignedIso a U V haU haV).isSurfaceValid
            validSource)⟩ := by
  let sourceIso := namedSourceSignedIso a U V haU haV
  let validBase :
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      (normalizationEquivalent
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V) hUV validBase)

end FaceMerge

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification25_block_01
/- END ClassificationOfSurfaces.FiniteCyclicFaceMerge -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicNormalizationResult | f8f00f58d65e7a043dfaa7044eb625191262a4f926311cbdb43c6fa1680437a3 -/
section schottkyclassification25_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Canonical output of finite-cyclic normalization

This file fixes the output type of the Gallier--Xu recursion before that recursion is assembled.
A result lands only at the existing `NormalForm.canonicalPresentation`; it cannot introduce a
second project-owned spelling of the Eval representatives.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- The validity-bundled canonical presentation selected by an admissible normal form. -/
noncomputable def canonicalValidPresentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    ValidPresentation :=
  ⟨N.canonicalPresentation, N.canonicalPresentation_isSurfaceValid hN⟩

@[simp]
theorem canonicalValidPresentation_presentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    (canonicalValidPresentation N hN).presentation =
      N.canonicalPresentation :=
  rfl

/-- Certified output of the finite-cyclic Gallier--Xu normalization.

The dependent admissibility field supplies ordinary validity for the canonical endpoint, and the
equivalence field records the entire validity-safe move chain. -/
structure NormalizationResult (P : ValidPresentation) where
  /-- The `normalForm` declaration. -/
  normalForm : NormalForm
  admissible : normalForm.IsEvalAdmissible
  equivalent :
    NormalizationEquivalent P
      (canonicalValidPresentation normalForm admissible)

namespace NormalizationResult

/-- A canonical presentation is already normalized. -/
noncomputable def canonical
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    NormalizationResult (canonicalValidPresentation N hN) where
  normalForm := N
  admissible := hN
  equivalent := NormalizationEquivalent.refl _

/-- Transport a normalization result backward through a normalization equivalence. -/
noncomputable def ofEquivalent
    {P Q : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q)
    (result : NormalizationResult Q) :
    NormalizationResult P where
  normalForm := result.normalForm
  admissible := result.admissible
  equivalent := hPQ.trans result.equivalent

/-- Transport a normalization result across a signed presentation isomorphism. -/
noncomputable def ofSignedIso
    {P Q : ValidPresentation}
    (e : SignedPresentationIso P.presentation Q.presentation)
    (result : NormalizationResult Q) :
    NormalizationResult P :=
  result.ofEquivalent (NormalizationEquivalent.ofSignedIso e)

/-- A normalization result gives the faithful polygonal realization equivalence to its exact
canonical finite-cyclic endpoint. -/
theorem polygonallyEquivalent
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonallyEquivalent
      result.normalForm.canonicalPresentation
      P.valid
      (result.normalForm.canonicalPresentation_isSurfaceValid
        result.admissible) :=
  result.equivalent.polygonallyEquivalent

/-- Homeomorphism from a normalized input's faithful polygonal realization to the exact canonical
finite-cyclic realization. -/
noncomputable def realizationHomeomorph
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonalRealization P.valid ≃ₜ
      result.normalForm.canonicalPresentation.PolygonalRealization
        (result.normalForm.canonicalPresentation_isSurfaceValid
          result.admissible) :=
  Classical.choice result.polygonallyEquivalent

end NormalizationResult

namespace Cancellation

/-- The terminal inverse-pair cancellation with no remaining darts yields the agreed canonical
sphere presentation. -/
noncomputable def sphereNormalizationResult
    (validSource :
      (source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid) :
    NormalizationResult
      ⟨source ([] : List (SignedDart (Fin 0))), validSource⟩ := by
  let hcanonical :=
    sphereNormalizationEquivalent validSource
  let canonicalSphere :=
    canonicalValidPresentation NormalForm.sphere trivial
  have hnode :
      (⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ :
        ValidPresentation) = canonicalSphere := by
    apply ValidPresentation.ext
    rfl
  rw [hnode] at hcanonical
  exact
    { normalForm := .sphere
      admissible := trivial
      equivalent := hcanonical }

end Cancellation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification25_block_02
/- END ClassificationOfSurfaces.FiniteCyclicNormalizationResult -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicReduction | 17a36c353c755ac97f77e1ebc49c705cd702770d7fea1c1a70e05b7de3310bef -/
section schottkyclassification25_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Combinatorial selections for finite-cyclic reduction

This file supplies the finite graph and cyclic-list selections used by the recursive
Gallier--Xu normalization.  In particular, connected presentations with more than one face expose
a genuinely adjacent pair, and either occurrence of their common edge can be placed at the head
of a suitably oriented cyclic boundary.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Reduction

/-- Build an unoriented presentation isomorphism from equations stated using oriented source
faces and stored target faces. Reversing both sides converts this convenient input convention to
the target-oriented convention of `UnorientedPresentationIso`. -/
def unorientedIsoOfOrientedBoundaries
    {P Q : FiniteCyclicPresentation}
    (edgeRelabeling : EdgeRelabeling P.Edge Q.Edge)
    (faceEquiv : P.Face ≃ Q.Face)
    (reverseFace : P.Face → Bool)
    (boundary_rotated :
      ∀ f,
        ((P.orientedBoundary ⟨f, reverseFace f⟩).map
          edgeRelabeling.mapDart).IsRotated
            (Q.boundary (faceEquiv f))) :
    UnorientedPresentationIso P Q where
  edgeRelabeling := edgeRelabeling
  faceEquiv := faceEquiv
  reverseFace := reverseFace
  boundary_rotated := by
    intro f
    cases hreverse : reverseFace f with
    | false =>
        simpa [FiniteCyclicPresentation.orientedBoundary, hreverse] using
          boundary_rotated f
    | true =>
        have hinverse :=
          inverseWord_isRotated (boundary_rotated f)
        simpa only [FiniteCyclicPresentation.orientedBoundary,
          hreverse, if_true, inverseWord_inverseWord,
          EdgeRelabeling.inverseWord_map_mapDart] using hinverse

/-! ### Deleting a selected edge name -/

/-- The edge count after deleting one selected edge. -/
def edgeCountAfterDelete
    (P : FiniteCyclicPresentation) : ℕ :=
  P.edgeCount - 1

theorem edgeCountAfterDelete_add_one
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeCountAfterDelete P + 1 = P.edgeCount := by
  have hpositive : 0 < P.edgeCount := Nat.zero_lt_of_lt e.isLt
  exact Nat.sub_add_cancel hpositive

/-- Rename an arbitrary selected edge to the last position of the one-larger edge type. -/
def edgeToLast
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    P.Edge ≃ Fin (edgeCountAfterDelete P + 1) := by
  let castCount :
      P.Edge ≃ Fin (edgeCountAfterDelete P + 1) :=
    finCongr (edgeCountAfterDelete_add_one P e).symm
  exact castCount.trans (Cancellation.moveToLast (castCount e))

theorem edgeToLast_selected
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeToLast P e e =
      P1.freshEdge (edgeCountAfterDelete P) := by
  simp [edgeToLast, Cancellation.moveToLast, P1.freshEdge]

/-- Rename a word after moving the selected edge to the fresh-last index. -/
def renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P + 1))) :=
  word.map (SignedDart.mapEquiv (edgeToLast P e))

/-- Contract the now-unused last edge name from a renamed word. -/
def lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  P1.contractWord (renamedTail P e word)

theorem freshEdge_not_mem_renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P1.freshEdge (edgeCountAfterDelete P) ∉
      (renamedTail P e word).map edgeOfDart := by
  intro hfresh
  rcases List.mem_map.mp hfresh with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  rw [edgeOfDart_mapEquiv] at hedge
  have holdEdge : edgeOfDart old = e := by
    apply (edgeToLast P e).injective
    rw [hedge, edgeToLast_selected]
  exact he (List.mem_map.mpr ⟨old, hold, holdEdge⟩)

/-- Lowering and re-embedding a renamed word which avoids the selected edge recovers that exact
renamed word. -/
theorem retainWord_lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P2.retainWord (lowerTail P e word) =
      renamedTail P e word :=
  Cancellation.retainWord_contractWord_of_fresh_not_mem
    (renamedTail P e word)
    (freshEdge_not_mem_renamedTail P e word he)

/-! ### Moving a selected face pair to the endpoints -/

/-- The last face index, using an existing face to certify nonemptiness. -/
def lastFace
    (P : FiniteCyclicPresentation) (f : P.Face) :
    P.Face :=
  ⟨P.faces.length - 1, by
    have hf := f.isLt
    omega⟩

/-- Move `f` to index zero and a distinct `g` to the final index. -/
def faceToEndpoints
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.Face ≃ P.Face :=
  let moveFirst :=
    Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  moveFirst.trans (Equiv.swap (moveFirst g) (lastFace P f))

theorem faceToEndpoints_selected
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    faceToEndpoints P f g f =
      ⟨0, Nat.zero_lt_of_lt f.isLt⟩ := by
  let zero : P.Face := ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  let moveFirst := Equiv.swap f zero
  have hgf : moveFirst g ≠ moveFirst f := by
    intro h
    exact hfg (moveFirst.injective h.symm)
  have hgzero : moveFirst g ≠ zero := by
    simpa [moveFirst] using hgf
  have hvalues : f.val ≠ g.val := by
    exact fun h ↦ hfg (Fin.ext h)
  have hmany : 1 < P.faces.length := by
    omega
  have hlastZero : lastFace P f ≠ zero := by
    intro h
    have hval := congrArg Fin.val h
    change P.faces.length - 1 = 0 at hval
    omega
  change
    (Equiv.swap (moveFirst g) (lastFace P f)) (moveFirst f) =
      zero
  rw [show moveFirst f = zero by simp [moveFirst]]
  exact Equiv.swap_apply_of_ne_of_ne hgzero.symm hlastZero.symm

@[simp]
theorem faceToEndpoints_right
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    faceToEndpoints P f g g = lastFace P f := by
  change
    (Equiv.swap
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g)
      (lastFace P f))
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g) =
        lastFace P f
  exact Equiv.swap_apply_left _ _

/-- Number of untouched faces after selecting two distinct endpoints. -/
def faceCountBetween
    (P : FiniteCyclicPresentation) : ℕ :=
  P.faces.length - 2

/-- The `i`th interior position between zero and the final face index. -/
def middleFacePosition
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  ⟨i.val + 1, by
    have hvalues : f.val ≠ g.val :=
      fun h ↦ hfg (Fin.ext h)
    have hmany : 1 < P.faces.length := by
      omega
    have hi := i.isLt
    change i.val < P.faces.length - 2 at hi
    change i.val + 1 < P.faces.length
    omega⟩

/-- The original face occupying an interior position after moving the selected pair to the
endpoints. -/
def middleOriginalFace
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  (faceToEndpoints P f g).symm
    (middleFacePosition P f g hfg i)

/-- Enumerate the original faces not selected as endpoints, in their transported order. -/
def middleOriginalFaces
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    List P.Face :=
  List.ofFn (middleOriginalFace P f g hfg)

theorem middleOriginalFace_ne_selected
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    middleOriginalFace P f g hfg i ≠ f := by
  intro h
  have hpositions := congrArg (faceToEndpoints P f g) h
  have hmiddle :
      faceToEndpoints P f g
          (middleOriginalFace P f g hfg i) =
        middleFacePosition P f g hfg i := by
    simp [middleOriginalFace]
  rw [hmiddle, faceToEndpoints_selected P f g hfg] at hpositions
  have hval := congrArg Fin.val hpositions
  change i.val + 1 = 0 at hval
  omega

theorem middleOriginalFace_ne_right
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    middleOriginalFace P f g hfg i ≠ g := by
  intro h
  have hpositions := congrArg (faceToEndpoints P f g) h
  have hmiddle :
      faceToEndpoints P f g
          (middleOriginalFace P f g hfg i) =
        middleFacePosition P f g hfg i := by
    simp [middleOriginalFace]
  rw [hmiddle, faceToEndpoints_right] at hpositions
  have hval := congrArg Fin.val hpositions
  change i.val + 1 = P.faces.length - 1 at hval
  have hi := i.isLt
  change i.val < P.faces.length - 2 at hi
  omega

@[simp]
theorem middleOriginalFaces_length
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    (middleOriginalFaces P f g hfg).length =
      faceCountBetween P := by
  simp [middleOriginalFaces]

/-- Every face is the selected face, the right face, or a uniquely positioned untouched face. -/
theorem face_eq_selected_or_right_or_middle
    (P : FiniteCyclicPresentation) (f g q : P.Face)
    (hfg : f ≠ g) :
    q = f ∨ q = g ∨
      ∃ i : Fin (faceCountBetween P),
        q = middleOriginalFace P f g hfg i := by
  let position := faceToEndpoints P f g q
  by_cases hzero : position.val = 0
  · left
    apply (faceToEndpoints P f g).injective
    apply Fin.ext
    rw [faceToEndpoints_selected P f g hfg]
    exact hzero
  · by_cases hlast :
      position.val = P.faces.length - 1
    · right
      left
      apply (faceToEndpoints P f g).injective
      apply Fin.ext
      rw [faceToEndpoints_right]
      exact hlast
    · right
      right
      have hvalues : f.val ≠ g.val :=
        fun h ↦ hfg (Fin.ext h)
      have hmany : 1 < P.faces.length := by
        omega
      have hpositionPositive : 0 < position.val := by
        omega
      have hpositionBelow : position.val < P.faces.length - 1 := by
        have hlt := position.isLt
        omega
      let i : Fin (faceCountBetween P) :=
        ⟨position.val - 1, by
          change position.val - 1 < P.faces.length - 2
          omega⟩
      refine ⟨i, ?_⟩
      apply (faceToEndpoints P f g).injective
      change
        faceToEndpoints P f g q =
          faceToEndpoints P f g
            ((faceToEndpoints P f g).symm
              (middleFacePosition P f g hfg i))
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      change position.val = i.val + 1
      simp only [i]
      omega

/-- A nontrivial reflexive-transitive path contains a genuinely non-reflexive step. -/
theorem exists_ne_step_of_reflTransGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) (hne : a ≠ b) :
    ∃ x y, r x y ∧ x ≠ y := by
  induction h with
  | refl =>
      exact (hne rfl).elim
  | @tail b c hab hbc ih =>
      by_cases hbcne : b ≠ c
      · exact ⟨b, c, hbc, hbcne⟩
      · have hbcEq : b = c := not_ne_iff.mp hbcne
        subst c
        exact ih hne

/-- Face adjacency is symmetric. -/
theorem faceAdjacent_comm
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.FaceAdjacent f g ↔ P.FaceAdjacent g f := by
  constructor
  · rintro ⟨e, hef, heg⟩
    exact ⟨e, heg, hef⟩
  · rintro ⟨e, heg, hef⟩
    exact ⟨e, hef, heg⟩

/-- The contributions of two distinct faces are bounded by the total edge multiplicity. -/
theorem add_faceEdgeMultiplicity_le_edgeMultiplicity
    (P : FiniteCyclicPresentation)
    (f g : P.Face) (e : P.Edge) (hfg : f ≠ g) :
    P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
      P.edgeMultiplicity e := by
  classical
  unfold edgeMultiplicity
  have hsubset :
      ({f, g} : Finset P.Face) ⊆ Finset.univ := by
    intro x hx
    simp
  have hsum :=
    Finset.sum_le_sum_of_subset
      (f := fun q ↦ P.faceEdgeMultiplicity q e) hsubset
  simpa [hfg] using hsum

/-- Three distinct face contributions are bounded by total edge multiplicity. -/
theorem add_three_faceEdgeMultiplicity_le_edgeMultiplicity
    (P : FiniteCyclicPresentation)
    (f g q : P.Face) (e : P.Edge)
    (hfg : f ≠ g) (hfq : f ≠ q) (hgq : g ≠ q) :
    P.faceEdgeMultiplicity f e +
        P.faceEdgeMultiplicity g e +
        P.faceEdgeMultiplicity q e ≤
      P.edgeMultiplicity e := by
  classical
  unfold edgeMultiplicity
  have hsubset :
      ({f, g, q} : Finset P.Face) ⊆ Finset.univ := by
    intro x hx
    simp
  have hsum :=
    Finset.sum_le_sum_of_subset
      (f := fun r ↦ P.faceEdgeMultiplicity r e) hsubset
  simpa [hfg, hfq, hgq, Nat.add_assoc] using hsum

/-- Once two distinct faces contain an edge of surface multiplicity at most two, no third face
contains that edge. -/
theorem edge_not_mem_boundary_of_other
    (P : FiniteCyclicPresentation)
    (valid : P.IsSurfaceValid)
    (f g q : P.Face) (e : P.Edge)
    (hfg : f ≠ g) (hfq : f ≠ q) (hgq : g ≠ q)
    (hef : e ∈ (P.boundary f).map edgeOfDart)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ (P.boundary q).map edgeOfDart := by
  classical
  intro heq
  have hfpos : 0 < P.faceEdgeMultiplicity f e :=
    List.count_pos_iff.mpr hef
  have hgpos : 0 < P.faceEdgeMultiplicity g e :=
    List.count_pos_iff.mpr heg
  have hqpos : 0 < P.faceEdgeMultiplicity q e :=
    List.count_pos_iff.mpr heq
  have hthree :=
    add_three_faceEdgeMultiplicity_le_edgeMultiplicity
      P f g q e hfg hfq hgq
  rcases valid.2.2.2 e with htotal | htotal <;> omega

/-- A connected presentation with at least two faces contains two distinct adjacent faces. -/
theorem exists_distinct_faceAdjacent
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ f g : P.Face, f ≠ g ∧ P.FaceAdjacent f g := by
  let f : P.Face := ⟨0, by omega⟩
  let g : P.Face := ⟨1, hmany⟩
  have hfg : f ≠ g := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 at hval
    omega
  rcases exists_ne_step_of_reflTransGen
      (connected.2 f g) hfg with
    ⟨x, y, hxy, hxyne⟩
  exact ⟨x, y, hxyne, hxy⟩

/-- Any member of a linear list can be moved to its head by a cyclic rotation. -/
theorem exists_tail_isRotated_cons_of_mem
    {α : Type*} {a : α} {word : List α}
    (ha : a ∈ word) :
    ∃ tail, word.IsRotated (a :: tail) := by
  rw [List.mem_iff_append] at ha
  rcases ha with ⟨left, right, rfl⟩
  refine ⟨right ++ left, ?_⟩
  simpa only [List.cons_append, List.append_assoc] using
    (List.isRotated_append
      (l := left) (l' := a :: right))

/-- Recover a signed occurrence from membership in the projected unoriented edge word. -/
theorem exists_dart_of_mem_map_edgeOfDart
    {α : Type*} {e : α} {word : List (SignedDart α)}
    (he : e ∈ word.map edgeOfDart) :
    ∃ d ∈ word, edgeOfDart d = e := by
  rcases List.mem_map.mp he with ⟨d, hd, hde⟩
  exact ⟨d, hd, hde⟩

/-- A common edge displayed positively at the head of an oriented cyclic face boundary. -/
structure PositiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  /-- The `orientedFace` declaration. -/
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  /-- The `tail` declaration. -/
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.pos e :: tail)

/-- A common edge displayed negatively at the head of an oriented cyclic face boundary. -/
structure NegativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  /-- The `orientedFace` declaration. -/
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  /-- The `tail` declaration. -/
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.neg e :: tail)

/-- Choose the traversal orientation which displays a selected edge occurrence positively. -/
theorem exists_positiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (PositiveOccurrence P f e) := by
  rcases exists_dart_of_mem_map_edgeOfDart he with
    ⟨d, hd, hde⟩
  cases d with
  | pos a =>
      change a = e at hde
      subst e
      rcases exists_tail_isRotated_cons_of_mem hd with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, false⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩
  | neg a =>
      change a = e at hde
      subst e
      have hpositive :
          SignedDart.pos a ∈ inverseWord (P.boundary f) := by
        rw [inverseWord]
        exact List.mem_map.mpr
          ⟨.neg a, by simpa using hd, rfl⟩
      rcases exists_tail_isRotated_cons_of_mem hpositive with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, true⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩

/-- Reverse a positive displayed occurrence to obtain a negative displayed occurrence. -/
def PositiveOccurrence.flip
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    NegativeOccurrence P f e where
  orientedFace := occurrence.orientedFace.flip
  face_eq := occurrence.face_eq
  tail := inverseWord occurrence.tail
  boundary_rotated := by
    rw [P.orientedBoundary_flip]
    have hhead :
        (inverseWord (.pos e :: occurrence.tail)).IsRotated
          (.neg e :: inverseWord occurrence.tail) := by
      simpa [inverseWord, SignedDart.flip] using
        (List.isRotated_concat (.neg e) (inverseWord occurrence.tail))
    exact
      (inverseWord_isRotated occurrence.boundary_rotated).trans hhead

/-- The underlying stored face contains the positively displayed edge. -/
theorem PositiveOccurrence.edge_mem_boundary
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    e ∈ (P.boundary f).map edgeOfDart := by
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have horientedMem :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart :=
    hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have horientedPositive :
      0 <
        ((P.orientedBoundary occurrence.orientedFace).map
          edgeOfDart).count e :=
    List.count_pos_iff.mpr horientedMem
  have hfacePositive :
      0 < P.faceEdgeMultiplicity occurrence.orientedFace.face e := by
    rw [← P.orientedBoundary_edgeMultiplicity
      occurrence.orientedFace e]
    exact horientedPositive
  rw [occurrence.face_eq] at hfacePositive
  exact List.count_pos_iff.mp hfacePositive

/-- The underlying stored face contains the negatively displayed edge. -/
theorem NegativeOccurrence.edge_mem_boundary
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P f e) :
    e ∈ (P.boundary f).map edgeOfDart := by
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have horientedMem :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart :=
    hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have horientedPositive :
      0 <
        ((P.orientedBoundary occurrence.orientedFace).map
          edgeOfDart).count e :=
    List.count_pos_iff.mpr horientedMem
  have hfacePositive :
      0 < P.faceEdgeMultiplicity occurrence.orientedFace.face e := by
    rw [← P.orientedBoundary_edgeMultiplicity
      occurrence.orientedFace e]
    exact horientedPositive
  rw [occurrence.face_eq] at hfacePositive
  exact List.count_pos_iff.mp hfacePositive

/-- In two distinct incident faces, the displayed occurrence consumes the entire multiplicity
contributed by its face, so the same edge does not occur again in its tail. -/
theorem PositiveOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  classical
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have hpositive :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart := by
    exact hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have hfpos : 0 < P.faceEdgeMultiplicity f e := by
    have horiented :=
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
    rw [← occurrence.face_eq, ← horiented]
    exact List.count_pos_iff.mpr hpositive
  have hgpos : 0 < P.faceEdgeMultiplicity g e := by
    exact List.count_pos_iff.mpr heg
  have htwo :
      P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
        P.edgeMultiplicity e :=
    add_faceEdgeMultiplicity_le_edgeMultiplicity P f g e hfg
  have htotal := valid.2.2.2 e
  have hfaceOne : P.faceEdgeMultiplicity f e = 1 := by
    rcases htotal with htotal | htotal <;> omega
  have horientedCount :
      ((P.orientedBoundary occurrence.orientedFace).map edgeOfDart).count e =
        P.faceEdgeMultiplicity f e := by
    simpa only [occurrence.face_eq] using
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
  have hrotatedCount := hmapRotated.perm.count_eq e
  have htailCount :
      (occurrence.tail.map edgeOfDart).count e = 0 := by
    rw [horientedCount, hfaceOne] at hrotatedCount
    simpa [edgeOfDart] using hrotatedCount.symm
  exact List.count_eq_zero.mp htailCount

/-- The corresponding no-second-occurrence statement for a negatively displayed face. -/
theorem NegativeOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  let positive : PositiveOccurrence P f e :=
    { orientedFace := occurrence.orientedFace.flip
      face_eq := occurrence.face_eq
      tail := inverseWord occurrence.tail
      boundary_rotated := by
        rw [P.orientedBoundary_flip]
        have hhead :
            (inverseWord (.neg e :: occurrence.tail)).IsRotated
              (.pos e :: inverseWord occurrence.tail) := by
          simpa [inverseWord, SignedDart.flip] using
            (List.isRotated_concat (.pos e) (inverseWord occurrence.tail))
        exact
          (inverseWord_isRotated occurrence.boundary_rotated).trans hhead }
  have hpositive :=
    positive.edge_not_mem_tail valid hfg heg
  simpa [positive, map_edgeOfDart_inverseWord] using hpositive

/-- The lowered left word used by the canonical contextual merge. -/
def mergeLeftWord
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  lowerTail P e occurrence.tail

/-- The lowered right word used by the canonical contextual merge. -/
def mergeRightWord
    {P : FiniteCyclicPresentation} {g : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P g e) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  lowerTail P e occurrence.tail

/-- Lower and enumerate all faces not selected for a merge. -/
def mergeMiddleWords
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g) :
    List (List (SignedDart (Fin (edgeCountAfterDelete P)))) :=
  (middleOriginalFaces P f g hfg).map
    (fun q ↦ lowerTail P e (P.boundary q))

theorem mergeMiddleWords_length
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g) :
    (mergeMiddleWords P e f g hfg).length =
      faceCountBetween P := by
  simp [mergeMiddleWords]

theorem mergeMiddleWords_get
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g)
    (i : Fin (faceCountBetween P)) :
    (mergeMiddleWords P e f g hfg).get
        ⟨i.val, by
          rw [mergeMiddleWords_length]
          exact i.isLt⟩ =
      lowerTail P e
        (P.boundary (middleOriginalFace P f g hfg i)) := by
  simp [mergeMiddleWords, middleOriginalFaces,
    middleOriginalFace]

theorem faceCountBetween_add_two
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    faceCountBetween P + 2 = P.faces.length := by
  have hvalues : f.val ≠ g.val :=
    fun h ↦ hfg (Fin.ext h)
  have hmany : 1 < P.faces.length := by
    omega
  simp only [faceCountBetween]
  omega

/-- The canonical contextual P2 source associated to two oppositely displayed adjacent faces. -/
@[reducible]
def mergeSource
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.source
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

/-- The presentation after merging the selected adjacent faces and deleting their separator. -/
@[reducible]
def mergeTarget
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.target
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

@[simp]
theorem mergeSource_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (mergeSource left right hfg).faces.length =
      P.faces.length := by
  rw [show
    (mergeSource left right hfg).faces.length =
      (mergeMiddleWords P e f g hfg).length + 2 by
    rw [P2.split_faces_length]
    simp [FaceMerge.ContextMerge.target]]
  rw [mergeMiddleWords_length, faceCountBetween_add_two P f g hfg]

theorem mergeTarget_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (mergeTarget left right hfg).faces.length =
      P.faces.length - 1 := by
  change
    (mergeMiddleWords P e f g hfg).length + 1 =
      P.faces.length - 1
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

/-- Reindex the input faces to the selected/interior/right ordering of its contextual merge
source. -/
def mergeFaceEquiv
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    P.Face ≃ (mergeSource left right hfg).Face :=
  (faceToEndpoints P f g).trans
    (finCongr (mergeSource_faces_length left right hfg).symm)

@[simp]
theorem mergeFaceEquiv_selected
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    mergeFaceEquiv left right hfg f =
      FaceMerge.ContextMerge.selectedFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg) := by
  apply Fin.ext
  change (faceToEndpoints P f g f).val = 0
  exact congrArg Fin.val (faceToEndpoints_selected P f g hfg)

@[simp]
theorem mergeFaceEquiv_right
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    mergeFaceEquiv left right hfg g =
      FaceMerge.ContextMerge.rightFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg) := by
  apply Fin.ext
  rw [show
    (mergeFaceEquiv left right hfg g).val =
      (lastFace P f).val by
    change (faceToEndpoints P f g g).val = (lastFace P f).val
    exact congrArg Fin.val (faceToEndpoints_right P f g)]
  change P.faces.length - 1 =
    (mergeMiddleWords P e f g hfg).length + 1
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

@[simp]
theorem mergeFaceEquiv_middle
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (i : Fin (faceCountBetween P)) :
    mergeFaceEquiv left right hfg
        (middleOriginalFace P f g hfg i) =
      FaceMerge.ContextMerge.untouchedSourceFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg)
        ⟨i.val, by
          rw [mergeMiddleWords_length]
          exact i.isLt⟩ := by
  apply Fin.ext
  simp only [P2.split_edgeCount, mergeFaceEquiv, middleOriginalFace,
    middleFacePosition, Equiv.trans_apply, Equiv.apply_symm_apply,
    FaceMerge.ContextMerge.untouchedSourceFace,
    FaceMerge.ContextMerge.untouchedTargetFace, List.length_cons]
  first
    | (erw [Equiv.trans_apply, Equiv.apply_symm_apply]; rfl)
    | (erw [Equiv.apply_symm_apply]; rfl)
    | exact congrArg Fin.val ((faceToEndpoints P f g).apply_symm_apply ⟨i.val + 1, by omega⟩)

/-- Reverse precisely the two selected source faces according to the traversals used to expose
their separator; untouched faces retain their stored orientation. -/
def mergeReverseFace
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (q : P.Face) :
    Bool :=
  if q = f then left.orientedFace.orientation
  else if q = g then right.orientedFace.orientation
  else false

/-- The arbitrary adjacent pair is the canonical contextual merge source after renaming the
separator, reordering faces, and choosing the two displayed traversal orientations. -/
def mergeUnorientedIso
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (valid : P.IsSurfaceValid) :
    UnorientedPresentationIso P (mergeSource left right hfg) := by
  apply unorientedIsoOfOrientedBoundaries
    (EdgeRelabeling.ofEquiv (edgeToLast P e))
    (mergeFaceEquiv left right hfg)
    (mergeReverseFace left right)
  intro q
  by_cases hqf : q = f
  · subst q
    rw [mergeFaceEquiv_selected,
      FaceMerge.ContextMerge.source_boundary_selected]
    have hreverse :
        mergeReverseFace left right f =
          left.orientedFace.orientation := by
      simp [mergeReverseFace]
    rw [hreverse]
    have horientedFace :
        (⟨f, left.orientedFace.orientation⟩ : P.OrientedFace) =
          left.orientedFace := by
      cases hleft : left.orientedFace with
      | mk face orientation =>
          have hface : face = f := by
            simpa [hleft] using left.face_eq
          subst face
          rfl
    rw [horientedFace]
    change
      ((P.orientedBoundary left.orientedFace).map
        (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
          (P2.retainWord (lowerTail P e left.tail) ++
            [.pos (P1.freshEdge (edgeCountAfterDelete P))])
    rw [retainWord_lowerTail P e left.tail
      (left.edge_not_mem_tail valid hfg
        right.edge_mem_boundary)]
    have hmapped :=
      left.boundary_rotated.map
        (SignedDart.mapEquiv (edgeToLast P e))
    apply hmapped.trans
    change
      (SignedDart.pos (edgeToLast P e e) ::
          renamedTail P e left.tail).IsRotated
        (renamedTail P e left.tail ++
          [SignedDart.pos (P1.freshEdge
            (edgeCountAfterDelete P))])
    rw [edgeToLast_selected]
    exact List.IsRotated.cons_append_singleton
  · by_cases hqg : q = g
    · subst q
      rw [mergeFaceEquiv_right,
        FaceMerge.ContextMerge.source_boundary_right]
      have hreverse :
          mergeReverseFace left right g =
            right.orientedFace.orientation := by
        simp [mergeReverseFace, hfg.symm]
      rw [hreverse]
      have horientedFace :
          (⟨g, right.orientedFace.orientation⟩ : P.OrientedFace) =
            right.orientedFace := by
        cases hright : right.orientedFace with
        | mk face orientation =>
            have hface : face = g := by
              simpa [hright] using right.face_eq
            subst face
            rfl
      rw [horientedFace]
      change
        ((P.orientedBoundary right.orientedFace).map
          (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
            ([.neg (P1.freshEdge (edgeCountAfterDelete P))] ++
              P2.retainWord (lowerTail P e right.tail))
      rw [retainWord_lowerTail P e right.tail
        (right.edge_not_mem_tail valid hfg.symm
          left.edge_mem_boundary)]
      have hmapped :=
        right.boundary_rotated.map
          (SignedDart.mapEquiv (edgeToLast P e))
      simpa [SignedDart.mapEquiv, edgeToLast_selected,
        renamedTail] using hmapped
    · rcases face_eq_selected_or_right_or_middle
        P f g q hfg with hselected | hright | ⟨i, hmiddle⟩
      · exact (hqf hselected).elim
      · exact (hqg hright).elim
      · subst q
        rw [mergeFaceEquiv_middle,
          FaceMerge.ContextMerge.source_boundary_untouched,
          mergeMiddleWords_get]
        have hmiddleF :
            middleOriginalFace P f g hfg i ≠ f := by
          intro h
          apply hqf
          exact h
        have hmiddleG :
            middleOriginalFace P f g hfg i ≠ g := by
          intro h
          apply hqg
          exact h
        rw [show
          mergeReverseFace left right
              (middleOriginalFace P f g hfg i) = false by
            simp [mergeReverseFace, hmiddleF, hmiddleG]]
        change
          ((P.boundary (middleOriginalFace P f g hfg i)).map
            (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
              (P2.retainWord
                (lowerTail P e
                  (P.boundary
                    (middleOriginalFace P f g hfg i))))
        rw [retainWord_lowerTail P e
          (P.boundary (middleOriginalFace P f g hfg i))
          (edge_not_mem_boundary_of_other P valid f g
            (middleOriginalFace P f g hfg i) e hfg
            (Ne.symm hmiddleF) (Ne.symm hmiddleG)
            left.edge_mem_boundary right.edge_mem_boundary)]
        exact List.IsRotated.refl _

private theorem mergeSource_untouched_eq_of_boundary_rotated
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e) (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) (validP : P.IsSurfaceValid)
    (i j : Fin (mergeMiddleWords P e f g hfg).length)
    (h : ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
          (mergeRightWord right) (mergeMiddleWords P e f g hfg) i)).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
          (mergeRightWord right) (mergeMiddleWords P e f g hfg) j))) :
    FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
        (mergeRightWord right) (mergeMiddleWords P e f g hfg) i =
      FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
        (mergeRightWord right) (mergeMiddleWords P e f g hfg) j := by
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  let iso := mergeUnorientedIso left right hfg validP
  let i' : Fin (faceCountBetween P) :=
    ⟨i.val, by simpa [W, mergeMiddleWords_length] using i.isLt⟩
  let j' : Fin (faceCountBetween P) :=
    ⟨j.val, by simpa [W, mergeMiddleWords_length] using j.isLt⟩
  let fi := middleOriginalFace P f g hfg i'
  let fj := middleOriginalFace P f g hfg j'
  have hfi : fi ≠ f := middleOriginalFace_ne_selected P f g hfg i'
  have hfig : fi ≠ g := middleOriginalFace_ne_right P f g hfg i'
  have hfj : fj ≠ f := middleOriginalFace_ne_selected P f g hfg j'
  have hfjg : fj ≠ g := middleOriginalFace_ne_right P f g hfg j'
  have hiFace : iso.faceEquiv fi =
      FaceMerge.ContextMerge.untouchedSourceFace U V W i := by
    apply Fin.ext
    change (mergeFaceEquiv left right hfg (middleOriginalFace P f g hfg i')).val = i.val + 1
    rw [mergeFaceEquiv_middle]
    rfl
  have hjFace : iso.faceEquiv fj =
      FaceMerge.ContextMerge.untouchedSourceFace U V W j := by
    apply Fin.ext
    change (mergeFaceEquiv left right hfg (middleOriginalFace P f g hfg j')).val = j.val + 1
    rw [mergeFaceEquiv_middle]
    rfl
  have hiReverse : mergeReverseFace left right fi = false := by
    simp [mergeReverseFace, hfi, hfig]
  have hjReverse : mergeReverseFace left right fj = false := by
    simp [mergeReverseFace, hfj, hfjg]
  have hiFace' : mergeFaceEquiv left right hfg fi =
      FaceMerge.ContextMerge.untouchedSourceFace U V W i := hiFace
  have hjFace' : mergeFaceEquiv left right hfg fj =
      FaceMerge.ContextMerge.untouchedSourceFace U V W j := hjFace
  have hi := iso.boundary_rotated fi
  have hj := iso.boundary_rotated fj
  change ((P.boundary fi).map iso.edgeRelabeling.mapDart).IsRotated
    ((mergeSource left right hfg).orientedBoundary
      ⟨mergeFaceEquiv left right hfg fi, mergeReverseFace left right fi⟩) at hi
  change ((P.boundary fj).map iso.edgeRelabeling.mapDart).IsRotated
    ((mergeSource left right hfg).orientedBoundary
      ⟨mergeFaceEquiv left right hfg fj, mergeReverseFace left right fj⟩) at hj
  have hi' : ((P.boundary fi).map iso.edgeRelabeling.mapDart).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace U V W i)) := by
    rw [hiFace', hiReverse] at hi
    simpa [FiniteCyclicPresentation.orientedBoundary] using hi
  have hj' : ((P.boundary fj).map iso.edgeRelabeling.mapDart).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace U V W j)) := by
    rw [hjFace', hjReverse] at hj
    simpa [FiniteCyclicPresentation.orientedBoundary] using hj
  have hmapped := hi'.trans (h.trans hj'.symm)
  have horiginal := hmapped.map iso.edgeRelabeling.symm.mapDart
  rw [EdgeRelabeling.map_mapDart_symm, EdgeRelabeling.map_mapDart_symm] at horiginal
  have hfij := validP.2.2.1 fi fj horiginal
  exact hiFace.symm.trans ((congrArg iso.faceEquiv hfij).trans hjFace)

/-- The specialized unoriented comparison used by an adjacent-face merge preserves ordinary
validity.  Reversing either selected face cannot create a duplicate: both selected faces contain
the fresh separator, untouched faces do not, and the two selected occurrences have opposite
signs. -/
theorem mergeSource_isSurfaceValid
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    (mergeSource left right hfg).IsSurfaceValid := by
  classical
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  let base := FaceMerge.ContextMerge.target U V W
  let cut := FaceMerge.ContextMerge.targetCut U V W
  let iso := mergeUnorientedIso left right hfg validP
  have hfaces (q : (mergeSource left right hfg).Face) :
      q = FaceMerge.ContextMerge.selectedFace U V W ∨
        (∃ i : Fin W.length,
          q = FaceMerge.ContextMerge.untouchedSourceFace U V W i) ∨
        q = FaceMerge.ContextMerge.rightFace U V W := by
    rcases P2.face_cases base cut q with ⟨p, hp⟩ | hp
    · induction p using Fin.cases with
      | zero =>
          left
          rw [hp]
          apply Fin.ext
          rfl
      | succ i =>
          right
          left
          refine ⟨i, ?_⟩
          rw [hp]
          apply Fin.ext
          rfl
    · exact Or.inr (Or.inr hp)
  have hselectedRight
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W))) :
      False := by
    have hmem :
        P2.selectedFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W) := by
      change
        P2.selectedFreshDart base cut ∈
          (P2.split base cut).boundary
            (P2.oldFace base cut cut.face.face)
      rw [P2.split_boundary_selected]
      exact P2.selectedFreshDart_mem_selectedBoundary base cut
    have htarget := h.mem_iff.mp hmem
    change
      P2.selectedFreshDart base cut ∈
        (P2.split base cut).boundary (P2.rightFace base cut)
        at htarget
    rw [P2.split_boundary_right] at htarget
    exact P2.selectedFreshDart_not_mem_rightBoundary
      base cut htarget
  have hselectedUntouched
      (i : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i))) :
      False := by
    have hmem :
        P2.selectedFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W) := by
      change
        P2.selectedFreshDart base cut ∈
          (P2.split base cut).boundary
            (P2.oldFace base cut cut.face.face)
      rw [P2.split_boundary_selected]
      exact P2.selectedFreshDart_mem_selectedBoundary base cut
    have htarget := h.mem_iff.mp hmem
    rw [FaceMerge.ContextMerge.source_boundary_untouched] at htarget
    exact P2.selectedFreshDart_not_mem_retainWord
      base cut (W.get i) htarget
  have hrightUntouched
      (i : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i))) :
      False := by
    have hmem :
        P2.rightFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W) := by
      change
        P2.rightFreshDart base cut ∈
          (P2.split base cut).boundary (P2.rightFace base cut)
      rw [P2.split_boundary_right]
      exact P2.rightFreshDart_mem_rightBoundary base cut
    have htarget := h.mem_iff.mp hmem
    rw [FaceMerge.ContextMerge.source_boundary_untouched] at htarget
    exact P2.rightFreshDart_not_mem_retainWord
      base cut (W.get i) htarget
  have huntouched
      (i j : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W j))) :
      FaceMerge.ContextMerge.untouchedSourceFace U V W i =
        FaceMerge.ContextMerge.untouchedSourceFace U V W j :=
    mergeSource_untouched_eq_of_boundary_rotated left right hfg validP i j h
  refine ⟨iso.faceEquiv.nonempty_congr.mp validP.1, ?_, ?_, ?_⟩
  · intro q hq
    let p := iso.faceEquiv.symm q
    have hlength := iso.boundary_length_eq p
    rw [iso.faceEquiv.apply_symm_apply] at hlength
    have hp : (P.boundary p).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact validP.2.1 p (List.length_eq_zero_iff.mp hp)
  · intro q r hqr
    rcases hfaces q with hq | ⟨i, hq⟩ | hq <;>
      rcases hfaces r with hr | ⟨j, hr⟩ | hr
    · exact hq.trans hr.symm
    · subst q
      subst r
      exact (hselectedUntouched j hqr).elim
    · subst q
      subst r
      exact (hselectedRight hqr).elim
    · subst q
      subst r
      exact (hselectedUntouched i hqr.symm).elim
    · subst q
      subst r
      exact huntouched i j hqr
    · subst q
      subst r
      exact (hrightUntouched i hqr.symm).elim
    · subst q
      subst r
      exact (hselectedRight hqr.symm).elim
    · subst q
      subst r
      exact (hrightUntouched j hqr).elim
    · exact hq.trans hr.symm
  · intro b
    let a := iso.edgeEquiv.symm b
    have hmultiplicity := validP.2.2.2 a
    rw [iso.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [iso.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- The validity-safe result of merging an arbitrary adjacent pair while retaining its separator
as a cancellable adjacent inverse marker. -/
@[reducible]
def markedMergeTarget
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.markedTarget
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

/-- An arbitrary marked merge preserves strict ordinary validity. -/
theorem markedMergeTarget_isSurfaceValid
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    (markedMergeTarget left right hfg).IsSurfaceValid :=
  FaceMerge.ContextMerge.markedTarget_isSurfaceValid
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)
    (mergeSource_isSurfaceValid left right hfg validP)

/-- An arbitrary marked merge preserves face-incidence connectivity. -/
theorem markedMergeTarget_isConnected
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (connectedP : P.IsConnected) :
    (markedMergeTarget left right hfg).IsConnected :=
  FaceMerge.ContextMerge.markedTarget_isConnected
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)
    ((mergeUnorientedIso left right hfg validP).isConnected connectedP)

/-- Merge any oppositely displayed adjacent pair without a target-validity side condition.  The
retained inverse marker is canceled only after the face recursion, preventing intermediate cyclic
duplicate faces. -/
theorem markedMergeNormalizationEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨markedMergeTarget left right hfg,
        markedMergeTarget_isSurfaceValid left right hfg validP⟩ := by
  let validSource :=
    mergeSource_isSurfaceValid left right hfg validP
  have hsource :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨mergeSource left right hfg, validSource⟩ :=
    NormalizationEquivalent.ofUnorientedIso
      (mergeUnorientedIso left right hfg validP)
  exact hsource.trans
    (FaceMerge.ContextMerge.markedNormalizationEquivalent
      (mergeLeftWord left) (mergeRightWord right)
      (mergeMiddleWords P e f g hfg) validSource)

/-- A marked merge removes exactly one face. -/
theorem markedMergeTarget_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (markedMergeTarget left right hfg).faces.length =
      P.faces.length - 1 := by
  simp only [markedMergeTarget,
    FaceMerge.ContextMerge.markedTarget,
    List.length_cons, List.length_map]
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

/-- Faithful polygonal-realization invariance of the arbitrary marked merge. -/
theorem markedMergePolygonallyEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent
      (markedMergeTarget left right hfg) validP
      (markedMergeTarget_isSurfaceValid left right hfg validP) :=
  (markedMergeNormalizationEquivalent
    left right hfg validP).polygonallyEquivalent

/-- Merge an arbitrary oppositely displayed adjacent pair. Target validity remains explicit:
under the project's strict stored-word uniqueness clause, a merge can make its new word coincide
cyclically with an untouched face. -/
theorem mergeNormalizationEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (validTarget : (mergeTarget left right hfg).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨mergeTarget left right hfg, validTarget⟩ := by
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  have hUV : U ++ V ≠ [] := by
    let first :
        (FaceMerge.ContextMerge.target U V W).Face :=
      ⟨0, by simp [FaceMerge.ContextMerge.target]⟩
    intro hempty
    apply validTarget.2.1 first
    change U ++ V = []
    exact hempty
  let validSource :
      (FaceMerge.ContextMerge.source U V W).IsSurfaceValid :=
    P2.split_isSurfaceValid
      (FaceMerge.ContextMerge.target U V W)
      (FaceMerge.ContextMerge.targetCut U V W)
      validTarget
  have hiso :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨FaceMerge.ContextMerge.source U V W, validSource⟩ := by
    apply NormalizationEquivalent.ofUnorientedIso
    exact mergeUnorientedIso left right hfg validP
  exact hiso.trans
    (FaceMerge.ContextMerge.normalizationEquivalent
      U V W hUV validTarget)

/-- Faithful polygonal-realization invariance of the arbitrary adjacent-face merge. -/
theorem mergePolygonallyEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (validTarget : (mergeTarget left right hfg).IsSurfaceValid) :
    P.PolygonallyEquivalent
      (mergeTarget left right hfg) validP validTarget :=
  (mergeNormalizationEquivalent
    left right hfg validP validTarget).polygonallyEquivalent

/-- Choose the traversal orientation which displays a selected edge occurrence negatively. -/
theorem exists_negativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (NegativeOccurrence P f e) := by
  rcases exists_positiveOccurrence P f e he with ⟨occurrence⟩
  exact ⟨occurrence.flip⟩

/-- A distinct adjacent pair can always be oriented with positive and negative occurrences of
the same separator displayed at the heads of its two cyclic boundaries. -/
theorem exists_oppositelyDisplayedAdjacentFaces
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ (f g : P.Face) (e : P.Edge),
      f ≠ g ∧
        Nonempty (PositiveOccurrence P f e) ∧
        Nonempty (NegativeOccurrence P g e) := by
  rcases exists_distinct_faceAdjacent P connected hmany with
    ⟨f, g, hfg, e, hef, heg⟩
  exact
    ⟨f, g, e, hfg,
      exists_positiveOccurrence P f e hef,
      exists_negativeOccurrence P g e heg⟩

/-- The validity-safe output of merging a connected presentation down to one face. -/
structure OneFaceReduction (P : ValidPresentation) where
  /-- The `target` declaration. -/
  target : ValidPresentation
  connected : target.presentation.IsConnected
  faces_length : target.presentation.faces.length = 1
  equivalent : NormalizationEquivalent P target

/-- Repeated marked merges reduce every connected ordinary-valid presentation to one face.

Each merge retains its separator as an adjacent inverse marker.  Consequently every recursive
target remains strictly valid even when deleting the separator immediately would duplicate an
untouched cyclic face word. -/
noncomputable def reduceToOneFace
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    OneFaceReduction P := by
  classical
  by_cases hone : P.presentation.faces.length = 1
  · exact
      { target := P
        connected := connectedP
        faces_length := hone
        equivalent := NormalizationEquivalent.refl P }
  · have hpositive : 0 < P.presentation.faces.length := by
      rcases P.valid.1 with ⟨f⟩
      have hf := f.isLt
      omega
    have hmany : 1 < P.presentation.faces.length := by
      omega
    have hwitness :=
      exists_oppositelyDisplayedAdjacentFaces
        P.presentation connectedP hmany
    let f := Classical.choose hwitness
    have hwitnessF := Classical.choose_spec hwitness
    let g := Classical.choose hwitnessF
    have hwitnessG := Classical.choose_spec hwitnessF
    let e := Classical.choose hwitnessG
    have hdisplayed := Classical.choose_spec hwitnessG
    have hfg : f ≠ g := hdisplayed.1
    let left := Classical.choice hdisplayed.2.1
    let right := Classical.choice hdisplayed.2.2
    let validTarget :=
      markedMergeTarget_isSurfaceValid left right hfg P.valid
    let target : ValidPresentation :=
      ⟨markedMergeTarget left right hfg, validTarget⟩
    have connectedTarget : target.presentation.IsConnected :=
      markedMergeTarget_isConnected
        left right hfg P.valid connectedP
    have firstEquivalent : NormalizationEquivalent P target :=
      markedMergeNormalizationEquivalent left right hfg P.valid
    have result : OneFaceReduction target :=
      reduceToOneFace target connectedTarget
    exact
      { target := result.target
        connected := result.connected
        faces_length := result.faces_length
        equivalent := firstEquivalent.trans result.equivalent }
termination_by P.presentation.faces.length
decreasing_by
  rw [markedMergeTarget_faces_length]
  omega

end Reduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification25_block_03
/- END ClassificationOfSurfaces.FiniteCyclicReduction -/
