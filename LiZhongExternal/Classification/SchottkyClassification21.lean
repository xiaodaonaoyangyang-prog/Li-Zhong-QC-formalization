/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification21: pinned classification sources; see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification20
import Mathlib.Topology.Homeomorph.Lemmas
import LiZhongExternal.Classification.SchottkyClassification19
import LiZhongExternal.Classification.SchottkyClassification09
import LiZhongExternal.Classification.SchottkyClassification03
import LiZhongExternal.Classification.SchottkyClassification01

/- BEGIN ClassificationOfSurfaces.FiniteCyclicP2 | 13404f2384d1c2a582d5149a4943da747102f57667c1b4607432cde08630ea07 -/
section schottkyclassification21_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Gallier--Xu P2 face subdivision

This file formalizes the second primitive subdivision from Gallier--Xu, Definition 6.3. A cyclic
boundary is cut, in a chosen traversal orientation, into two pieces `left` and `right`. The
presentation-level construction permits empty pieces so that it also expresses Gallier--Xu's
exceptional empty-word-sphere conversion. The public `P2Subdivision` relation requires both
pieces to be nonempty for an ordinary face subdivision. The selected face is replaced by two
faces whose boundaries in that same orientation
are

* `left d`, and
* `d⁻¹ right`,

where `d` is a fresh edge.

The orientation stored on the two target faces is the orientation chosen by the cut. In
particular, a negatively oriented cut deliberately stores the inverses of the displayed words;
it does not claim to preserve the old positive stored orientation. This convention makes
reversing a cut exchange the two children exactly.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- A cyclic, oriented place at which to apply Gallier--Xu P2.

The decomposition is cyclic rather than tied to the stored head of the list. Empty `left` or
`right` pieces are allowed. -/
structure P2Cut (P : FiniteCyclicPresentation) where
  /-- The `face` declaration. -/
  face : P.OrientedFace
  /-- The `left` declaration. -/
  left : List P.Dart
  /-- The `right` declaration. -/
  right : List P.Dart
  boundary_rotated : (P.orientedBoundary face).IsRotated (left ++ right)

namespace P2Cut

/-- A genuine face cut has an old boundary side on each side of the new cutting edge.

The raw `P2Cut` structure also represents the exceptional empty-word-sphere conversion, for which
both pieces are necessarily empty. -/
def IsNondegenerate {P : FiniteCyclicPresentation} (cut : P2Cut P) : Prop :=
  cut.left ≠ [] ∧ cut.right ≠ []

theorem isNondegenerate_iff_lengths_pos {P : FiniteCyclicPresentation}
    (cut : P2Cut P) :
    cut.IsNondegenerate ↔ 0 < cut.left.length ∧ 0 < cut.right.length := by
  simp only [IsNondegenerate, List.length_pos_iff_ne_nil]

/-- Cut a chosen oriented representative at a linear position. -/
def canonical {P : FiniteCyclicPresentation} (face : P.OrientedFace)
    (position : Fin ((P.orientedBoundary face).length + 1)) : P2Cut P where
  face := face
  left := (P.orientedBoundary face).take position
  right := (P.orientedBoundary face).drop position
  boundary_rotated := by
    simpa only [List.take_append_drop] using
      List.IsRotated.refl (P.orientedBoundary face)

@[simp]
theorem canonical_face {P : FiniteCyclicPresentation} (face : P.OrientedFace)
    (position : Fin ((P.orientedBoundary face).length + 1)) :
    (canonical face position).face = face :=
  rfl

@[simp]
theorem canonical_zero_left {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face 0).left = [] :=
  rfl

@[simp]
theorem canonical_zero_right {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face 0).right = P.orientedBoundary face :=
  rfl

@[simp]
theorem canonical_last_left {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face (Fin.last (P.orientedBoundary face).length)).left =
      P.orientedBoundary face := by
  simp [canonical]

@[simp]
theorem canonical_last_right {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face (Fin.last (P.orientedBoundary face).length)).right = [] := by
  simp [canonical]

/-- Move the cyclic cut point to the other end of the two pieces. -/
def swap {P : FiniteCyclicPresentation} (cut : P2Cut P) : P2Cut P where
  face := cut.face
  left := cut.right
  right := cut.left
  boundary_rotated :=
    cut.boundary_rotated.trans List.isRotated_append

/-- Reverse the traversal orientation of a cut. -/
def flip {P : FiniteCyclicPresentation} (cut : P2Cut P) : P2Cut P where
  face := cut.face.flip
  left := inverseWord cut.right
  right := inverseWord cut.left
  boundary_rotated := by
    rw [P.orientedBoundary_flip]
    simpa only [inverseWord_append] using
      inverseWord_isRotated cut.boundary_rotated

@[simp]
theorem swap_face {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.face = cut.face :=
  rfl

@[simp]
theorem flip_face {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.face = cut.face.flip :=
  rfl

@[simp]
theorem swap_swap {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.swap = cut := by
  cases cut
  rfl

@[simp]
theorem flip_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.flip = cut := by
  cases cut
  simp [flip]

theorem swap_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.flip = cut.flip.swap := by
  cases cut
  rfl

@[simp]
theorem isNondegenerate_swap {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.IsNondegenerate ↔ cut.IsNondegenerate := by
  rw [isNondegenerate_iff_lengths_pos, isNondegenerate_iff_lengths_pos]
  change
    (0 < cut.right.length ∧ 0 < cut.left.length) ↔
      0 < cut.left.length ∧ 0 < cut.right.length
  exact and_comm

@[simp]
theorem isNondegenerate_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.IsNondegenerate ↔ cut.IsNondegenerate := by
  rw [isNondegenerate_iff_lengths_pos, isNondegenerate_iff_lengths_pos]
  change
    (0 < (inverseWord cut.right).length ∧
      0 < (inverseWord cut.left).length) ↔
        0 < cut.left.length ∧ 0 < cut.right.length
  simp only [inverseWord_length]
  exact and_comm

end P2Cut

namespace P2

/-- The fresh cutting edge. -/
def freshEdge (P : FiniteCyclicPresentation) : Fin (P.edgeCount + 1) :=
  P1.freshEdge P.edgeCount

/-- Retain an old boundary word in the enlarged edge type. -/
def retainWord {n : ℕ} (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  word.map P1.castSuccDart

/-- Store a displayed oriented boundary in the presentation's positive orientation. -/
def storedWord {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) : List (SignedDart α) :=
  if orientation then inverseWord word else word

@[simp]
theorem retainWord_nil {n : ℕ} :
    retainWord ([] : List (SignedDart (Fin n))) = [] :=
  rfl

@[simp]
theorem retainWord_append {n : ℕ}
    (left right : List (SignedDart (Fin n))) :
    retainWord (left ++ right) = retainWord left ++ retainWord right := by
  simp [retainWord]

@[simp]
theorem castSuccDart_flip {n : ℕ} (d : SignedDart (Fin n)) :
    P1.castSuccDart d.flip = (P1.castSuccDart d).flip := by
  cases d <;> rfl

@[simp]
theorem retainWord_inverseWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    retainWord (inverseWord word) = inverseWord (retainWord word) := by
  simp [retainWord, inverseWord, List.map_map, Function.comp_def]

@[simp]
theorem storedWord_false {α : Type*} (word : List (SignedDart α)) :
    storedWord false word = word :=
  rfl

@[simp]
theorem storedWord_true {α : Type*} (word : List (SignedDart α)) :
    storedWord true word = inverseWord word :=
  rfl

/-- Reading a stored word in its selected orientation returns the displayed word. -/
@[simp]
theorem oriented_storedWord {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) :
    (if orientation then inverseWord (storedWord orientation word)
      else storedWord orientation word) = word := by
  cases orientation <;> simp [storedWord]

@[simp]
theorem contractDart_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    P1.contractDart (P1.castSuccDart d) = some d := by
  cases d <;> simp [P1.contractDart, P1.castSuccDart]

@[simp]
theorem contractWord_retainWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    P1.contractWord (retainWord word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [retainWord, List.map_cons]
      rw [P1.contractWord]
      simp only [List.filterMap_cons, contractDart_castSuccDart]
      exact congrArg (List.cons d) ih

/-- The first displayed child boundary. -/
def selectedOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  retainWord cut.left ++ [.pos (freshEdge P)]

/-- The second displayed child boundary. -/
def rightOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  .neg (freshEdge P) :: retainWord cut.right

/-- The first child boundary in its stored orientation. -/
def selectedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  storedWord cut.face.orientation (selectedOrientedBoundary P cut)

/-- The second child boundary in its stored orientation. -/
def rightBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  storedWord cut.face.orientation (rightOrientedBoundary P cut)

/-- The word stored at a target face index. -/
def faceWord (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) → List (SignedDart (Fin (P.edgeCount + 1))) :=
  Fin.lastCases (rightBoundary P cut) fun f ↦
    if f = cut.face.face then
      selectedBoundary P cut
    else
      retainWord (P.boundary f)

/-- Canonical presentation-level P2 face split. -/
def split (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := List.ofFn (faceWord P cut)

@[simp]
theorem split_edgeCount (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).edgeCount = P.edgeCount + 1 :=
  rfl

@[simp]
theorem split_faces_length (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faces.length = P.faces.length + 1 := by
  simp [split]

/-- Identify the explicit target indexing type with the presentation's face type. -/
def faceEquiv (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) ≃ (split P cut).Face :=
  finCongr (split_faces_length P cut).symm

/-- The target face occupying an old source-face position. -/
def oldFace (P : FiniteCyclicPresentation) (cut : P2Cut P) (f : P.Face) :
    (split P cut).Face :=
  faceEquiv P cut f.castSucc

/-- The fresh second child face. -/
def rightFace (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).Face :=
  faceEquiv P cut (Fin.last P.faces.length)

@[simp]
theorem faceEquiv_apply_val (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : Fin (P.faces.length + 1)) :
    (faceEquiv P cut f).val = f.val :=
  rfl

theorem face_cases (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    (∃ f : P.Face, q = oldFace P cut f) ∨ q = rightFace P cut := by
  let i := (faceEquiv P cut).symm q
  have hi : faceEquiv P cut i = q :=
    (faceEquiv P cut).apply_symm_apply q
  refine Fin.lastCases
    (motive := fun j ↦ faceEquiv P cut j = q →
      (∃ f : P.Face, q = oldFace P cut f) ∨ q = rightFace P cut)
    ?_ (fun f h ↦ Or.inl ⟨f, h.symm⟩) i hi
  intro h
  exact Or.inr h.symm

@[simp]
theorem split_boundary_index (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : Fin (P.faces.length + 1)) :
    (split P cut).boundary (faceEquiv P cut q) = faceWord P cut q := by
  unfold boundary split
  rw [List.get_ofFn]
  apply congrArg (faceWord P cut)
  apply Fin.ext
  rfl

@[simp]
theorem split_boundary_old (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : P.Face) :
    (split P cut).boundary (oldFace P cut f) =
      if f = cut.face.face then
        selectedBoundary P cut
      else
        retainWord (P.boundary f) := by
  simp [oldFace, faceWord]
  rfl

theorem split_boundary_selected (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).boundary (oldFace P cut cut.face.face) =
      selectedBoundary P cut := by
  simp
  rfl

theorem split_boundary_old_of_ne (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (h : f ≠ cut.face.face) :
    (split P cut).boundary (oldFace P cut f) =
      retainWord (P.boundary f) := by
  simp [h]
  rfl

@[simp]
theorem split_boundary_right (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).boundary (rightFace P cut) = rightBoundary P cut := by
  simp [rightFace, faceWord]
  rfl

/-- The selected child has exactly the displayed oriented boundary `left d`. -/
theorem split_orientedBoundary_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).orientedBoundary
        ⟨oldFace P cut cut.face.face, cut.face.orientation⟩ =
      selectedOrientedBoundary P cut := by
  rw [orientedBoundary]
  simp only [split_boundary_selected]
  exact oriented_storedWord cut.face.orientation _

/-- The right child has exactly the displayed oriented boundary `d⁻¹ right`. -/
theorem split_orientedBoundary_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).orientedBoundary
        ⟨rightFace P cut, cut.face.orientation⟩ =
      rightOrientedBoundary P cut := by
  rw [orientedBoundary]
  simp only [split_boundary_right]
  exact oriented_storedWord cut.face.orientation _

/-- Retaining a word preserves whether it is empty. -/
@[simp]
theorem retainWord_eq_nil_iff {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    retainWord word = [] ↔ word = [] := by
  exact List.map_eq_nil_iff

/-- Retaining a word preserves the multiplicity of every old edge. -/
theorem count_retainWord_castSucc {n : ℕ} (e : Fin n)
    (word : List (SignedDart (Fin n))) :
    ((retainWord word).map edgeOfDart).count e.castSucc =
      (word.map edgeOfDart).count e := by
  have hcount :=
    List.count_map_of_injective (word.map edgeOfDart)
      Fin.castSucc (Fin.castSucc_injective n) e
  simpa [retainWord, List.map_map, Function.comp_def] using hcount

/-- Reversing the stored traversal does not change unoriented edge multiplicities. -/
theorem count_storedWord (orientation : Bool) {α : Type*} [DecidableEq α]
    (word : List (SignedDart α)) (e : α) :
    ((storedWord orientation word).map edgeOfDart).count e =
      (word.map edgeOfDart).count e := by
  cases orientation
  · rfl
  · rw [storedWord_true, map_edgeOfDart_inverseWord]
    exact (List.reverse_perm _).count_eq e

/-- The fresh edge does not occur in a retained old word. -/
theorem freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    freshEdge P ∉ (retainWord word).map edgeOfDart := by
  intro h
  rcases List.mem_map.mp h with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  have hlast : (edgeOfDart old).castSucc ≠ freshEdge P := by
    exact P1.firstSubedge_ne_freshEdge (edgeOfDart old)
  exact hlast (P1.edgeOfDart_castSuccDart old ▸ hedge)

@[simp]
theorem pos_freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.pos (freshEdge P) ∉ retainWord word := by
  intro h
  exact freshEdge_not_mem_retainWord P word
    (List.mem_map.mpr ⟨.pos (freshEdge P), h, rfl⟩)

@[simp]
theorem neg_freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.neg (freshEdge P) ∉ retainWord word := by
  intro h
  exact freshEdge_not_mem_retainWord P word
    (List.mem_map.mpr ⟨.neg (freshEdge P), h, rfl⟩)

@[simp]
theorem pos_freshEdge_not_mem_inverse_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.pos (freshEdge P) ∉ inverseWord (retainWord word) := by
  intro h
  have hedge :
      freshEdge P ∈ (inverseWord (retainWord word)).map edgeOfDart :=
    List.mem_map.mpr ⟨.pos (freshEdge P), h, rfl⟩
  rw [map_edgeOfDart_inverseWord] at hedge
  exact freshEdge_not_mem_retainWord P word (List.mem_reverse.mp hedge)

@[simp]
theorem neg_freshEdge_not_mem_inverse_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.neg (freshEdge P) ∉ inverseWord (retainWord word) := by
  intro h
  have hedge :
      freshEdge P ∈ (inverseWord (retainWord word)).map edgeOfDart :=
    List.mem_map.mpr ⟨.neg (freshEdge P), h, rfl⟩
  rw [map_edgeOfDart_inverseWord] at hedge
  exact freshEdge_not_mem_retainWord P word (List.mem_reverse.mp hedge)

/-- The signed fresh dart occurring in the selected child. -/
def selectedFreshDart (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedDart (Fin (P.edgeCount + 1)) :=
  if cut.face.orientation then .neg (freshEdge P) else .pos (freshEdge P)

/-- The opposite signed fresh dart occurring in the right child. -/
def rightFreshDart (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedDart (Fin (P.edgeCount + 1)) :=
  (selectedFreshDart P cut).flip

@[simp]
theorem edgeOfDart_selectedFreshDart
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    edgeOfDart (selectedFreshDart P cut) = freshEdge P := by
  cases h : cut.face.orientation <;>
    simp [selectedFreshDart, h, edgeOfDart]

@[simp]
theorem edgeOfDart_rightFreshDart
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    edgeOfDart (rightFreshDart P cut) = freshEdge P := by
  rw [rightFreshDart, edgeOfDart_flip, edgeOfDart_selectedFreshDart]

theorem selectedBoundary_of_orientation_false
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = false) :
    selectedBoundary P cut =
      retainWord cut.left ++ [.pos (freshEdge P)] := by
  simp [selectedBoundary, selectedOrientedBoundary, storedWord, h]

theorem selectedBoundary_of_orientation_true
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = true) :
    selectedBoundary P cut =
      .neg (freshEdge P) :: inverseWord (retainWord cut.left) := by
  simp [selectedBoundary, selectedOrientedBoundary, storedWord, h,
    inverseWord, SignedDart.flip]

theorem rightBoundary_of_orientation_false
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = false) :
    rightBoundary P cut =
      .neg (freshEdge P) :: retainWord cut.right := by
  simp [rightBoundary, rightOrientedBoundary, storedWord, h]

theorem rightBoundary_of_orientation_true
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = true) :
    rightBoundary P cut =
      inverseWord (retainWord cut.right) ++ [.pos (freshEdge P)] := by
  simp [rightBoundary, rightOrientedBoundary, storedWord, h,
    inverseWord, SignedDart.flip]

/-- Reversing the cut exchanges its selected child with the original right child. -/
@[simp]
theorem selectedBoundary_flip
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedBoundary P cut.flip = rightBoundary P cut := by
  cases h : cut.face.orientation
  · have hflip : cut.flip.face.orientation = true := by
      simp [P2Cut.flip, OrientedFace.flip, h]
    rw [selectedBoundary_of_orientation_true P cut.flip hflip]
    rw [rightBoundary_of_orientation_false P cut h]
    simp [P2Cut.flip]
  · have hflip : cut.flip.face.orientation = false := by
      simp [P2Cut.flip, OrientedFace.flip, h]
    rw [selectedBoundary_of_orientation_false P cut.flip hflip]
    rw [rightBoundary_of_orientation_true P cut h]
    simp [P2Cut.flip]

/-- Reversing the cut exchanges its right child with the original selected child. -/
@[simp]
theorem rightBoundary_flip
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightBoundary P cut.flip = selectedBoundary P cut := by
  simpa only [P2Cut.flip_flip] using
    (selectedBoundary_flip P cut.flip).symm

theorem selectedFreshDart_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedFreshDart P cut ∈ selectedBoundary P cut := by
  cases h : cut.face.orientation
  · rw [selectedBoundary_of_orientation_false P cut h]
    simp [selectedFreshDart, h]
  · rw [selectedBoundary_of_orientation_true P cut h]
    simp [selectedFreshDart, h]

theorem selectedFreshDart_not_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedFreshDart P cut ∉ rightBoundary P cut := by
  cases h : cut.face.orientation
  · rw [rightBoundary_of_orientation_false P cut h]
    simp [selectedFreshDart, h]
  · rw [rightBoundary_of_orientation_true P cut h]
    simp [selectedFreshDart, h]

theorem rightFreshDart_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightFreshDart P cut ∈ rightBoundary P cut := by
  cases h : cut.face.orientation
  · rw [rightBoundary_of_orientation_false P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]
  · rw [rightBoundary_of_orientation_true P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

theorem rightFreshDart_not_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightFreshDart P cut ∉ selectedBoundary P cut := by
  cases h : cut.face.orientation
  · rw [selectedBoundary_of_orientation_false P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]
  · rw [selectedBoundary_of_orientation_true P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

theorem selectedFreshDart_not_mem_retainWord
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (word : List P.Dart) :
    selectedFreshDart P cut ∉ retainWord word := by
  cases h : cut.face.orientation <;>
    simp [selectedFreshDart, h]

theorem rightFreshDart_not_mem_retainWord
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (word : List P.Dart) :
    rightFreshDart P cut ∉ retainWord word := by
  cases h : cut.face.orientation <;>
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

/-- The selected child receives the old-edge occurrences in the left cut piece. -/
theorem faceEdgeMultiplicity_split_selected_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut cut.face.face) e.castSucc =
      (cut.left.map edgeOfDart).count e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_selected]
  calc
    ((selectedBoundary P cut).map edgeOfDart).count e.castSucc =
        ((selectedOrientedBoundary P cut).map edgeOfDart).count e.castSucc :=
      count_storedWord cut.face.orientation _ _
    _ = (cut.left.map edgeOfDart).count e := by
      have hne : e.castSucc ≠ freshEdge P :=
        P1.firstSubedge_ne_freshEdge e
      have hne' : freshEdge P ≠ e.castSucc :=
        Ne.symm hne
      simp [selectedOrientedBoundary, edgeOfDart,
        count_retainWord_castSucc, hne']

/-- The right child receives the old-edge occurrences in the right cut piece. -/
theorem faceEdgeMultiplicity_split_right_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (rightFace P cut) e.castSucc =
      (cut.right.map edgeOfDart).count e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_right]
  calc
    ((rightBoundary P cut).map edgeOfDart).count e.castSucc =
        ((rightOrientedBoundary P cut).map edgeOfDart).count e.castSucc :=
      count_storedWord cut.face.orientation _ _
    _ = (cut.right.map edgeOfDart).count e := by
      have hne : e.castSucc ≠ freshEdge P :=
        P1.firstSubedge_ne_freshEdge e
      have hne' : freshEdge P ≠ e.castSucc :=
        Ne.symm hne
      simp [rightOrientedBoundary, edgeOfDart,
        count_retainWord_castSucc, hne']

/-- Every unselected face retains its old-edge multiplicities. -/
theorem faceEdgeMultiplicity_split_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f : P.Face}
    (h : f ≠ cut.face.face) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc =
      P.faceEdgeMultiplicity f e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_old_of_ne P cut h]
  exact count_retainWord_castSucc e (P.boundary f)

/-- The selected child contains the fresh edge exactly once. -/
@[simp]
theorem faceEdgeMultiplicity_split_selected_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut cut.face.face)
      (freshEdge P) = 1 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_selected]
  calc
    ((selectedBoundary P cut).map edgeOfDart).count (freshEdge P) =
        ((selectedOrientedBoundary P cut).map edgeOfDart).count (freshEdge P) :=
      count_storedWord cut.face.orientation _ _
    _ = 1 := by
      have hzero :
          ((retainWord cut.left).map edgeOfDart).count (freshEdge P) = 0 :=
        List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P cut.left)
      simp [selectedOrientedBoundary, edgeOfDart, hzero]

/-- The right child contains the fresh edge exactly once. -/
@[simp]
theorem faceEdgeMultiplicity_split_right_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faceEdgeMultiplicity (rightFace P cut) (freshEdge P) = 1 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_right]
  calc
    ((rightBoundary P cut).map edgeOfDart).count (freshEdge P) =
        ((rightOrientedBoundary P cut).map edgeOfDart).count (freshEdge P) :=
      count_storedWord cut.face.orientation _ _
    _ = 1 := by
      have hzero :
          ((retainWord cut.right).map edgeOfDart).count (freshEdge P) = 0 :=
        List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P cut.right)
      simp [rightOrientedBoundary, edgeOfDart, hzero]

/-- An unselected face contains no occurrence of the fresh edge. -/
theorem faceEdgeMultiplicity_split_old_freshEdge_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f : P.Face}
    (h : f ≠ cut.face.face) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut f) (freshEdge P) = 0 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_old_of_ne P cut h]
  exact List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P (P.boundary f))

/-- The selected source face's multiplicity is the sum of the two cut-piece counts. -/
theorem faceEdgeMultiplicity_cut_eq_add
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    P.faceEdgeMultiplicity cut.face.face e =
      (cut.left.map edgeOfDart).count e +
        (cut.right.map edgeOfDart).count e := by
  have hrotation :=
    (cut.boundary_rotated.map edgeOfDart).perm.count_eq e
  calc
    P.faceEdgeMultiplicity cut.face.face e =
        ((P.orientedBoundary cut.face).map edgeOfDart).count e :=
      (P.orientedBoundary_edgeMultiplicity cut.face e).symm
    _ = (((cut.left ++ cut.right).map edgeOfDart).count e) :=
      hrotation
    _ = (cut.left.map edgeOfDart).count e +
        (cut.right.map edgeOfDart).count e := by
      simp

private theorem sum_replace_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℕ) (selected : ι) (left right : ℕ)
    (hselected : values selected = left + right) :
    (∑ x, if x = selected then left else values x) + right =
      ∑ x, values x := by
  have hsum :
      (∑ x, if x = selected then left else values x) =
        left + ∑ x ∈ Finset.univ.erase selected, values x := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun x ↦ if x = selected then left else values x)
      (Finset.mem_univ selected)]
    simp only [if_pos]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ selected :=
      Finset.ne_of_mem_erase hx
    simp [hne]
  rw [hsum]
  calc
    (left + ∑ x ∈ Finset.univ.erase selected, values x) + right =
        (left + right) + ∑ x ∈ Finset.univ.erase selected, values x := by
      omega
    _ = values selected + ∑ x ∈ Finset.univ.erase selected, values x := by
      rw [hselected]
    _ = ∑ x, values x :=
      Finset.add_sum_erase Finset.univ values (Finset.mem_univ selected)

/-- P2 preserves the total multiplicity of every retained old edge. -/
theorem edgeMultiplicity_split_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    P.edgeMultiplicity e =
      (split P cut).edgeMultiplicity e.castSucc := by
  unfold edgeMultiplicity
  have hreindex :
      (∑ q : (split P cut).Face,
          (split P cut).faceEdgeMultiplicity q e.castSucc) =
        ∑ q : Fin (P.faces.length + 1),
          (split P cut).faceEdgeMultiplicity (faceEquiv P cut q) e.castSucc :=
    (Fintype.sum_equiv (faceEquiv P cut)
      (fun q ↦ (split P cut).faceEdgeMultiplicity
        (faceEquiv P cut q) e.castSucc)
      (fun q ↦ (split P cut).faceEdgeMultiplicity q e.castSucc)
      (fun _ ↦ rfl)).symm
  rw [hreindex, Fin.sum_univ_castSucc]
  symm
  change
    (∑ f : P.Face,
      (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc) +
        (split P cut).faceEdgeMultiplicity (rightFace P cut) e.castSucc =
      ∑ f : P.Face, P.faceEdgeMultiplicity f e
  rw [faceEdgeMultiplicity_split_right_castSucc]
  have hold :
      (∑ f : P.Face,
          (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc) =
        ∑ f : P.Face,
          if f = cut.face.face then
            (cut.left.map edgeOfDart).count e
          else
            P.faceEdgeMultiplicity f e := by
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hface : f = cut.face.face
    · subst f
      simp [faceEdgeMultiplicity_split_selected_castSucc]
    · simp [hface, faceEdgeMultiplicity_split_old_of_ne P cut hface]
  rw [hold]
  exact sum_replace_add
    (fun f ↦ P.faceEdgeMultiplicity f e) cut.face.face
    ((cut.left.map edgeOfDart).count e)
    ((cut.right.map edgeOfDart).count e)
    (faceEdgeMultiplicity_cut_eq_add P cut e)

/-- The fresh cutting edge occurs exactly once in each child and nowhere else. -/
@[simp]
theorem edgeMultiplicity_split_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).edgeMultiplicity (freshEdge P) = 2 := by
  unfold edgeMultiplicity
  have hreindex :
      (∑ q : (split P cut).Face,
          (split P cut).faceEdgeMultiplicity q (freshEdge P)) =
        ∑ q : Fin (P.faces.length + 1),
          (split P cut).faceEdgeMultiplicity
            (faceEquiv P cut q) (freshEdge P) :=
    (Fintype.sum_equiv (faceEquiv P cut)
      (fun q ↦ (split P cut).faceEdgeMultiplicity
        (faceEquiv P cut q) (freshEdge P))
      (fun q ↦ (split P cut).faceEdgeMultiplicity q (freshEdge P))
      (fun _ ↦ rfl)).symm
  rw [hreindex, Fin.sum_univ_castSucc]
  change
    (∑ f : P.Face,
      (split P cut).faceEdgeMultiplicity (oldFace P cut f) (freshEdge P)) +
        (split P cut).faceEdgeMultiplicity (rightFace P cut) (freshEdge P) = 2
  rw [faceEdgeMultiplicity_split_right_freshEdge]
  have hold :
      (∑ f : P.Face,
          (split P cut).faceEdgeMultiplicity
            (oldFace P cut f) (freshEdge P)) =
        ∑ f : P.Face, if f = cut.face.face then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hface : f = cut.face.face
    · subst f
      simp
    · simp [hface, faceEdgeMultiplicity_split_old_freshEdge_of_ne P cut hface]
  rw [hold]
  simp

/-- Retaining old edge names preserves and reflects cyclic rotation. -/
@[simp]
theorem retainWord_isRotated_iff {n : ℕ}
    (left right : List (SignedDart (Fin n))) :
    (retainWord left).IsRotated (retainWord right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [contractWord_retainWord] using
      P1.contractWord_isRotated h
  · intro h
    simpa only [retainWord] using h.map P1.castSuccDart

/-- P2 preserves ordinary finite-presentation incidence validity. -/
theorem split_isSurfaceValid
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsSurfaceValid) :
    (split P cut).IsSurfaceValid := by
  refine ⟨⟨rightFace P cut⟩, ?_, ?_, ?_⟩
  · intro q
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · by_cases hface : f = cut.face.face
      · subst f
        rw [split_boundary_selected]
        exact List.ne_nil_of_mem
          (selectedFreshDart_mem_selectedBoundary P cut)
      · rw [split_boundary_old_of_ne P cut hface]
        intro hnil
        exact h.2.1 f ((retainWord_eq_nil_iff (P.boundary f)).mp hnil)
    · rw [split_boundary_right]
      exact List.ne_nil_of_mem (rightFreshDart_mem_rightBoundary P cut)
  · intro q r hqr
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · by_cases hf : f = cut.face.face
        · subst f
          by_cases hg : g = cut.face.face
          · subst g
            rfl
          · have hselected :
                selectedFreshDart P cut ∈
                  (split P cut).boundary
                    (oldFace P cut cut.face.face) := by
              rw [split_boundary_selected]
              exact selectedFreshDart_mem_selectedBoundary P cut
            have htarget := hqr.mem_iff.mp hselected
            rw [split_boundary_old_of_ne P cut hg] at htarget
            exact (selectedFreshDart_not_mem_retainWord
              P cut (P.boundary g) htarget).elim
        · by_cases hg : g = cut.face.face
          · subst g
            have hselected :
                selectedFreshDart P cut ∈
                  (split P cut).boundary
                    (oldFace P cut cut.face.face) := by
              rw [split_boundary_selected]
              exact selectedFreshDart_mem_selectedBoundary P cut
            have htarget := hqr.symm.mem_iff.mp hselected
            rw [split_boundary_old_of_ne P cut hf] at htarget
            exact (selectedFreshDart_not_mem_retainWord
              P cut (P.boundary f) htarget).elim
          · have hretained :
                (retainWord (P.boundary f)).IsRotated
                  (retainWord (P.boundary g)) := by
              rw [← split_boundary_old_of_ne P cut hf,
                ← split_boundary_old_of_ne P cut hg]
              exact hqr
            have hsource :=
              (retainWord_isRotated_iff (P.boundary f) (P.boundary g)).mp
                hretained
            have hfg := h.2.2.1 f g hsource
            subst g
            rfl
      · by_cases hf : f = cut.face.face
        · subst f
          have hselected :
              selectedFreshDart P cut ∈
                (split P cut).boundary
                  (oldFace P cut cut.face.face) := by
            rw [split_boundary_selected]
            exact selectedFreshDart_mem_selectedBoundary P cut
          have htarget := hqr.mem_iff.mp hselected
          rw [split_boundary_right] at htarget
          exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
        · have hright :
              rightFreshDart P cut ∈
                (split P cut).boundary (rightFace P cut) := by
            rw [split_boundary_right]
            exact rightFreshDart_mem_rightBoundary P cut
          have htarget := hqr.symm.mem_iff.mp hright
          rw [split_boundary_old_of_ne P cut hf] at htarget
          exact (rightFreshDart_not_mem_retainWord
            P cut (P.boundary f) htarget).elim
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · by_cases hg : g = cut.face.face
        · subst g
          have hselected :
              selectedFreshDart P cut ∈
                (split P cut).boundary
                  (oldFace P cut cut.face.face) := by
            rw [split_boundary_selected]
            exact selectedFreshDart_mem_selectedBoundary P cut
          have htarget := hqr.symm.mem_iff.mp hselected
          rw [split_boundary_right] at htarget
          exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
        · have hright :
              rightFreshDart P cut ∈
                (split P cut).boundary (rightFace P cut) := by
            rw [split_boundary_right]
            exact rightFreshDart_mem_rightBoundary P cut
          have htarget := hqr.mem_iff.mp hright
          rw [split_boundary_old_of_ne P cut hg] at htarget
          exact (rightFreshDart_not_mem_retainWord
            P cut (P.boundary g) htarget).elim
      · rfl
  · intro e
    change Fin (P.edgeCount + 1) at e
    refine Fin.lastCases ?_ (fun old ↦ ?_) e
    · exact Or.inr (by
        simpa only [freshEdge, P1.freshEdge] using
          edgeMultiplicity_split_freshEdge P cut)
    · have hmultiplicity := h.2.2.2 old
      rw [edgeMultiplicity_split_castSucc P cut old] at hmultiplicity
      exact hmultiplicity

/-- Edge membership is independent of the chosen traversal orientation of a face. -/
theorem edge_mem_orientedBoundary_iff
    (P : FiniteCyclicPresentation) (face : P.OrientedFace) (e : P.Edge) :
    e ∈ (P.orientedBoundary face).map edgeOfDart ↔
      e ∈ (P.boundary face.face).map edgeOfDart := by
  cases face with
  | mk face orientation =>
      cases orientation
      · rfl
      · rw [orientedBoundary, if_pos rfl, map_edgeOfDart_inverseWord]
        exact List.mem_reverse

/-- An edge of the selected face occurs in one of the two cut pieces. -/
theorem edge_mem_cut_pieces_iff
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    e ∈ cut.left.map edgeOfDart ∨ e ∈ cut.right.map edgeOfDart ↔
      e ∈ (P.boundary cut.face.face).map edgeOfDart := by
  calc
    e ∈ cut.left.map edgeOfDart ∨ e ∈ cut.right.map edgeOfDart ↔
        e ∈ (cut.left ++ cut.right).map edgeOfDart := by
      simp
    _ ↔ e ∈ (P.orientedBoundary cut.face).map edgeOfDart :=
      (cut.boundary_rotated.map edgeOfDart).mem_iff.symm
    _ ↔ e ∈ (P.boundary cut.face.face).map edgeOfDart :=
      edge_mem_orientedBoundary_iff P cut.face e

/-- Membership of an old edge is retained after enlarging the edge type. -/
theorem castSucc_edge_mem_retainWord
    {n : ℕ} {e : Fin n} {word : List (SignedDart (Fin n))}
    (h : e ∈ word.map edgeOfDart) :
    e.castSucc ∈ (retainWord word).map edgeOfDart := by
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  exact List.mem_map.mpr
    ⟨P1.castSuccDart d, List.mem_map.mpr ⟨d, hd, rfl⟩,
      P1.edgeOfDart_castSuccDart d⟩

/-- Storing a word in the opposite traversal preserves unoriented edge membership. -/
theorem edge_mem_storedWord_iff
    {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) (e : α) :
    e ∈ (storedWord orientation word).map edgeOfDart ↔
      e ∈ word.map edgeOfDart := by
  cases orientation
  · rfl
  · rw [storedWord_true, map_edgeOfDart_inverseWord]
    exact List.mem_reverse

theorem castSucc_edge_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {e : P.Edge}
    (h : e ∈ cut.left.map edgeOfDart) :
    e.castSucc ∈ (selectedBoundary P cut).map edgeOfDart := by
  apply (edge_mem_storedWord_iff cut.face.orientation _ _).mpr
  simp only [selectedOrientedBoundary, List.map_append, List.map_singleton,
    List.mem_append, List.mem_singleton]
  exact Or.inl (castSucc_edge_mem_retainWord h)

theorem castSucc_edge_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {e : P.Edge}
    (h : e ∈ cut.right.map edgeOfDart) :
    e.castSucc ∈ (rightBoundary P cut).map edgeOfDart := by
  apply (edge_mem_storedWord_iff cut.face.orientation _ _).mpr
  simp only [rightOrientedBoundary, List.map_cons, List.mem_cons]
  exact Or.inr (castSucc_edge_mem_retainWord h)

/-- The two child faces are adjacent through the fresh cutting edge. -/
theorem split_children_faceAdjacent
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).FaceAdjacent
      (oldFace P cut cut.face.face) (rightFace P cut) := by
  refine ⟨freshEdge P, ?_, ?_⟩
  · rw [split_boundary_selected]
    exact List.mem_map.mpr
      ⟨selectedFreshDart P cut,
        selectedFreshDart_mem_selectedBoundary P cut,
        edgeOfDart_selectedFreshDart P cut⟩
  · rw [split_boundary_right]
    exact List.mem_map.mpr
      ⟨rightFreshDart P cut,
        rightFreshDart_mem_rightBoundary P cut,
        edgeOfDart_rightFreshDart P cut⟩

private theorem faceAdjacent_symm
    {P : FiniteCyclicPresentation} {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    P.FaceAdjacent g f := by
  rcases h with ⟨e, hf, hg⟩
  exact ⟨e, hg, hf⟩

private theorem faceChain_symm
    {P : FiniteCyclicPresentation} {f g : P.Face}
    (h : Relation.ReflTransGen P.FaceAdjacent f g) :
    Relation.ReflTransGen P.FaceAdjacent g f := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl f => exact Relation.ReflTransGen.refl
  | single h => exact Relation.ReflTransGen.single (faceAdjacent_symm h)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂.trans ih₁

/-- A source-face edge occurs in a child reachable from the retained face position. -/
theorem exists_child_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : P.Face) (e : P.Edge)
    (h : e ∈ (P.boundary f).map edgeOfDart) :
    ∃ q : (split P cut).Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        (oldFace P cut f) q ∧
      e.castSucc ∈ ((split P cut).boundary q).map edgeOfDart := by
  by_cases hface : f = cut.face.face
  · subst f
    rcases (edge_mem_cut_pieces_iff P cut e).mpr h with hleft | hright
    · refine ⟨oldFace P cut cut.face.face,
        Relation.ReflTransGen.refl, ?_⟩
      rw [split_boundary_selected]
      exact castSucc_edge_mem_selectedBoundary P cut hleft
    · refine ⟨rightFace P cut,
        Relation.ReflTransGen.single (split_children_faceAdjacent P cut), ?_⟩
      rw [split_boundary_right]
      exact castSucc_edge_mem_rightBoundary P cut hright
  · refine ⟨oldFace P cut f, Relation.ReflTransGen.refl, ?_⟩
    rw [split_boundary_old_of_ne P cut hface]
    exact castSucc_edge_mem_retainWord h

/-- A source adjacency lifts to a target path between the retained face positions. -/
theorem map_faceAdjacent_chain
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    Relation.ReflTransGen (split P cut).FaceAdjacent
      (oldFace P cut f) (oldFace P cut g) := by
  rcases h with ⟨e, hf, hg⟩
  rcases exists_child_edge P cut f e hf with ⟨q, hfq, hq⟩
  rcases exists_child_edge P cut g e hg with ⟨r, hgr, hr⟩
  exact hfq.trans
    ((Relation.ReflTransGen.single ⟨e.castSucc, hq, hr⟩).trans
      (faceChain_symm hgr))

/-- A source face-adjacency path lifts to a target path. -/
theorem map_faceChain
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f g : P.Face}
    (h : Relation.ReflTransGen P.FaceAdjacent f g) :
    Relation.ReflTransGen (split P cut).FaceAdjacent
      (oldFace P cut f) (oldFace P cut g) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl f => exact Relation.ReflTransGen.refl
  | single h => exact map_faceAdjacent_chain P cut h
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem target_to_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    ∃ f : P.Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        q (oldFace P cut f) := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · exact ⟨f, Relation.ReflTransGen.refl⟩
  · exact ⟨cut.face.face,
      Relation.ReflTransGen.single
        (faceAdjacent_symm (split_children_faceAdjacent P cut))⟩

private theorem oldFace_to_target
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    ∃ f : P.Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        (oldFace P cut f) q := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · exact ⟨f, Relation.ReflTransGen.refl⟩
  · exact ⟨cut.face.face,
      Relation.ReflTransGen.single (split_children_faceAdjacent P cut)⟩

/-- P2 preserves connectivity of the face-edge incidence graph. -/
theorem split_isConnected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsConnected) :
    (split P cut).IsConnected := by
  refine ⟨⟨rightFace P cut⟩, ?_⟩
  intro q r
  rcases target_to_oldFace P cut q with ⟨f, hq⟩
  rcases oldFace_to_target P cut r with ⟨g, hr⟩
  exact hq.trans ((map_faceChain P cut (h.2 f g)).trans hr)

/-- Collapse both child faces of a P2 split back to their source face. -/
def collapseFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) : P.Face :=
  if h : q.val < P.faces.length then
    ⟨q.val, h⟩
  else
    cut.face.face

@[simp]
theorem collapseFace_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (f : P.Face) :
    collapseFace P cut (oldFace P cut f) = f := by
  apply Fin.ext
  simp [collapseFace, oldFace]

@[simp]
theorem collapseFace_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    collapseFace P cut (rightFace P cut) = cut.face.face := by
  apply Fin.ext
  simp [collapseFace, rightFace]

/-- A retained old edge in a child face comes from the corresponding collapsed source face. -/
private theorem oldEdge_mem_collapseFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) (e : P.Edge)
    (h : e.castSucc ∈ ((split P cut).boundary q).map edgeOfDart) :
    e ∈ (P.boundary (collapseFace P cut q)).map edgeOfDart := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · rw [collapseFace_oldFace]
    by_cases hface : f = cut.face.face
    · subst f
      apply List.count_pos_iff.mp
      have hpositive :
          0 < (split P cut).faceEdgeMultiplicity
            (oldFace P cut cut.face.face) e.castSucc :=
        List.count_pos_iff.mpr h
      rw [faceEdgeMultiplicity_split_selected_castSucc] at hpositive
      change 0 < P.faceEdgeMultiplicity cut.face.face e
      rw [faceEdgeMultiplicity_cut_eq_add]
      omega
    · apply List.count_pos_iff.mp
      have hpositive :
          0 < (split P cut).faceEdgeMultiplicity
            (oldFace P cut f) e.castSucc :=
        List.count_pos_iff.mpr h
      rw [faceEdgeMultiplicity_split_old_of_ne P cut hface] at hpositive
      exact hpositive
  · rw [collapseFace_rightFace]
    apply List.count_pos_iff.mp
    have hpositive :
        0 < (split P cut).faceEdgeMultiplicity
          (rightFace P cut) e.castSucc :=
      List.count_pos_iff.mpr h
    rw [faceEdgeMultiplicity_split_right_castSucc] at hpositive
    change 0 < P.faceEdgeMultiplicity cut.face.face e
    rw [faceEdgeMultiplicity_cut_eq_add]
    omega

/-- Any child containing the fresh cutting edge collapses to the selected source face. -/
private theorem collapseFace_eq_of_freshEdge_mem
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face)
    (h : freshEdge P ∈ ((split P cut).boundary q).map edgeOfDart) :
    collapseFace P cut q = cut.face.face := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · rw [collapseFace_oldFace]
    by_contra hface
    have hpositive :
        0 < (split P cut).faceEdgeMultiplicity
          (oldFace P cut f) (freshEdge P) :=
      List.count_pos_iff.mpr h
    rw [faceEdgeMultiplicity_split_old_freshEdge_of_ne P cut hface] at hpositive
    omega
  · exact collapseFace_rightFace P cut

/-- Collapsing the child faces sends target adjacency to a source adjacency path. -/
theorem collapse_faceAdjacent_chain
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {q r : (split P cut).Face}
    (h : (split P cut).FaceAdjacent q r) :
    Relation.ReflTransGen P.FaceAdjacent
      (collapseFace P cut q) (collapseFace P cut r) := by
  rcases h with ⟨b, hqb, hrb⟩
  change Fin (P.edgeCount + 1) at b
  revert hqb hrb
  refine Fin.lastCases ?_ (fun e hqb hrb ↦ ?_) b
  · intro hqb hrb
    rw [collapseFace_eq_of_freshEdge_mem P cut q hqb,
      collapseFace_eq_of_freshEdge_mem P cut r hrb]
  · exact Relation.ReflTransGen.single
      ⟨e, oldEdge_mem_collapseFace P cut q e hqb,
        oldEdge_mem_collapseFace P cut r e hrb⟩

/-- Collapsing the child faces sends target adjacency paths to source adjacency paths. -/
theorem collapse_faceChain
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {q r : (split P cut).Face}
    (h : Relation.ReflTransGen (split P cut).FaceAdjacent q r) :
    Relation.ReflTransGen P.FaceAdjacent
      (collapseFace P cut q) (collapseFace P cut r) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hadj => exact collapse_faceAdjacent_chain P cut hadj
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A P2 split is connected only if its source presentation is connected. -/
theorem isConnected_of_split
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : (split P cut).IsConnected) :
    P.IsConnected := by
  refine ⟨?_, ?_⟩
  · exact (Nonempty.map (collapseFace P cut) h.1)
  · intro f g
    have hchain := h.2 (oldFace P cut f) (oldFace P cut g)
    have hmapped := collapse_faceChain P cut hchain
    simpa only [collapseFace_oldFace] using hmapped

/-- Every P2 split of an exceptional empty-word presentation is ordinarily valid. -/
theorem split_isSurfaceValid_of_isEmptyWordSphere
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsEmptyWordSphere) :
    (split P cut).IsSurfaceValid := by
  have hallFaces (f : P.Face) : f = cut.face.face := by
    apply Fin.ext
    have hlength := h.faces_length_eq_one
    have hf := f.isLt
    have hcut := cut.face.face.isLt
    omega
  refine ⟨⟨rightFace P cut⟩, ?_, ?_, ?_⟩
  · intro q
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rw [hallFaces f, split_boundary_selected]
      exact List.ne_nil_of_mem
        (selectedFreshDart_mem_selectedBoundary P cut)
    · rw [split_boundary_right]
      exact List.ne_nil_of_mem (rightFreshDart_mem_rightBoundary P cut)
  · intro q r hqr
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · rw [hallFaces f, hallFaces g]
      · rw [hallFaces f] at hqr
        have hselected :
            selectedFreshDart P cut ∈
              (split P cut).boundary
                (oldFace P cut cut.face.face) := by
          rw [split_boundary_selected]
          exact selectedFreshDart_mem_selectedBoundary P cut
        have htarget := hqr.mem_iff.mp hselected
        rw [split_boundary_right] at htarget
        exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · rw [hallFaces g] at hqr
        have hselected :
            selectedFreshDart P cut ∈
              (split P cut).boundary
                (oldFace P cut cut.face.face) := by
          rw [split_boundary_selected]
          exact selectedFreshDart_mem_selectedBoundary P cut
        have htarget := hqr.symm.mem_iff.mp hselected
        rw [split_boundary_right] at htarget
        exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
      · rfl
  · intro e
    change Fin (P.edgeCount + 1) at e
    have hedgeCount := h.edgeCount_eq_zero
    have he : e = freshEdge P := by
      apply Fin.ext
      have heLt := e.isLt
      simp only [freshEdge, P1.freshEdge, Fin.last]
      omega
    subst e
    exact Or.inr (edgeMultiplicity_split_freshEdge P cut)

/-- P2 preserves Gallier validity, including the exceptional empty-word branch. -/
theorem split_isGallierValid
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsGallierValid) :
    (split P cut).IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl
      ⟨split_isSurfaceValid P cut hregular.1,
        split_isConnected P cut hregular.2⟩
  · exact Or.inl
      ⟨split_isSurfaceValid_of_isEmptyWordSphere P cut hempty,
        split_isConnected P cut hempty.isConnected⟩

/-- The zero-position P2 cut of Gallier--Xu's exceptional sphere presentation. -/
def emptyWordSphereCut : P2Cut emptyWordSphere :=
  P2Cut.canonical (.pos 0) 0

/-- The last-position spelling of the same empty boundary cut. -/
def emptyWordSphereLastCut : P2Cut emptyWordSphere :=
  P2Cut.canonical (.pos 0) (Fin.last 0)

@[simp]
theorem emptyWordSphereLastCut_eq :
    emptyWordSphereLastCut = emptyWordSphereCut :=
  rfl

/-- P2 turns the exceptional empty-word sphere presentation into the two-monogon presentation. -/
@[simp]
theorem split_emptyWordSphere :
    split emptyWordSphere emptyWordSphereCut = twoMonogonSphere :=
  rfl

/-- The endpoint-at-the-right spelling gives the same exact regression. -/
@[simp]
theorem split_emptyWordSphere_last :
    split emptyWordSphere emptyWordSphereLastCut = twoMonogonSphere :=
  rfl

end P2

/-- A Gallier--Xu P2 face subdivision, up to signed presentation isomorphism of the target.

An ordinary P2 move cuts between two distinct places of a nonempty cyclic boundary, so both old
boundary pieces are nonempty. The sole degenerate case admitted here is Gallier--Xu's exceptional
empty-word sphere, whose conversion to the ordinary-valid two-monogon presentation is also
represented by the raw `P2.split` construction. This is a syntactic move relation and
deliberately does not bundle source validity. -/
def P2Subdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ cut : P2Cut P,
    (cut.IsNondegenerate ∨ P.IsEmptyWordSphere) ∧
      Nonempty (SignedPresentationIso (P2.split P cut) Q)

namespace P2Subdivision

/-- A canonical nondegenerate split is a P2 subdivision. -/
theorem canonical (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut : cut.IsNondegenerate) :
    P2Subdivision P (P2.split P cut) :=
  ⟨cut, Or.inl hcut, ⟨SignedPresentationIso.refl _⟩⟩

/-- The raw split of an exceptional empty-word sphere is an allowed exceptional P2 step. -/
theorem canonicalEmptyWordSphere (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hP : P.IsEmptyWordSphere) :
    P2Subdivision P (P2.split P cut) :=
  ⟨cut, Or.inr hP, ⟨SignedPresentationIso.refl _⟩⟩

/-- P2 subdivisions preserve ordinary incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isSurfaceValid (P2.split_isSurfaceValid P cut h)

/-- P2 subdivisions preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isConnected (P2.split_isConnected P cut h)

/-- P2 subdivisions preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isGallierValid (P2.split_isGallierValid P cut h)

/-- The exceptional sphere presentation subdivides to the two-monogon sphere presentation. -/
theorem emptyWordSphere_twoMonogonSphere :
    P2Subdivision emptyWordSphere twoMonogonSphere := by
  simpa only [P2.split_emptyWordSphere] using
    canonicalEmptyWordSphere emptyWordSphere P2.emptyWordSphereCut
      emptyWordSphere_isEmptyWordSphere

end P2Subdivision

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification21_block_01
/- END ClassificationOfSurfaces.FiniteCyclicP2 -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicSignedRealization | 42d5409f222c370164cff54bf78fcc1e0673eb6a864cc503cf536bbab69dcb20 -/
section schottkyclassification21_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal realization under signed presentation isomorphism

A signed presentation isomorphism may rename and independently reverse edge names, relabel faces,
and cyclically rotate each stored face word. This file realizes those operations geometrically.
The selected cyclic rotation acts on the circular polygon carrier by an exact complex rotation,
so every labelled source side is sent to the target side carrying its relabelled dart.

The resulting homeomorphism of polygonal pre-realizations transports both the elementary gluing
generators and their equivalence closures. It therefore descends to a homeomorphism of the faithful
polygonal quotients.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace PolygonCell

/-- The `rotationUnit` declaration. -/
noncomputable def rotationUnit (n k : ℕ) : Circle :=
  Circle.exp (2 * Real.pi * k / n)

/-- The `rotateHomeomorph` declaration. -/
noncomputable def rotateHomeomorph {n m : ℕ} (h : n = m) (k : ℕ) :
    PolygonCell n ≃ₜ PolygonCell m := by
  subst m
  exact
    { toFun := fun z => ⟨(rotationUnit n k : ℂ) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      invFun := fun z => ⟨((rotationUnit n k)⁻¹ : Circle) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      left_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      right_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      continuous_toFun := by
        apply continuous_induced_rng.2
        fun_prop
      continuous_invFun := by
        apply continuous_induced_rng.2
        fun_prop }

@[simp]
theorem rotateHomeomorph_apply_val {n m : ℕ} (h : n = m) (k : ℕ)
    (z : PolygonCell n) :
    (rotateHomeomorph h k z).val = (rotationUnit n k : ℂ) * z.val :=
  by
    subst m
    rfl

/-- The `rotateIndex` declaration. -/
def rotateIndex {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩

@[simp]
theorem rotateIndex_val {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) :
    (rotateIndex hn k i).val = (i.val + k) % n :=
  rfl

theorem rotateHomeomorph_side {n : ℕ} (hn : 0 < n) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph (Eq.refl n) k (side i t) =
      side (rotateIndex hn k i) t := by
  apply PolygonCell.ext
  change ((Circle.exp (2 * Real.pi * k / n) : Circle) : ℂ) *
      ((Circle.exp (sideAngle i t) : Circle) : ℂ) =
    ((Circle.exp (sideAngle (rotateIndex hn k i) t) : Circle) : ℂ)
  rw [← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨Int.ofNat ((i.val + k) / n), ?_⟩
  simp only [sideAngle, rotateIndex_val]
  have hdecomp : (i.val + k) % n + n * ((i.val + k) / n) = i.val + k :=
    Nat.mod_add_div (i.val + k) n
  have hdecompR := congrArg (fun q : ℕ => (q : ℝ)) hdecomp
  push_cast at hdecompR
  have hquot :
      ((Int.ofNat ((i.val + k) / n) : ℤ) : ℝ) =
        (((i.val + k) / n : ℕ) : ℝ) := by
    rfl
  rw [hquot]
  field_simp [hn.ne']
  nlinarith [hdecompR]

/-- Rotation sends a side to the correspondingly shifted side after changing only the phantom
side-count index. -/
theorem rotateHomeomorph_side_of_eq {n m : ℕ} (h : n = m) (hm : 0 < m) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph h k (side i t) =
      side
        (⟨(i.val + k) % m, Nat.mod_lt _ hm⟩ : Fin m) t := by
  subst m
  exact rotateHomeomorph_side hm k i t

end PolygonCell

namespace FiniteCyclicPresentation.SignedPresentationIso

open SurfaceCellComplex

variable {P Q : FiniteCyclicPresentation}

/-- The target-boundary rotation selected for a signed presentation isomorphism. -/
noncomputable def faceRotation (e : SignedPresentationIso P Q) (f : P.Face) : ℕ :=
  Classical.choose (e.boundary_rotated f).symm

theorem rotate_target_boundary (e : SignedPresentationIso P Q) (f : P.Face) :
    (Q.boundary (e.faceEquiv f)).rotate (e.faceRotation f) =
      (P.boundary f).map e.edgeRelabeling.mapDart :=
  Classical.choose_spec (e.boundary_rotated f).symm

/-- The target side occupied by a source side after the selected face rotation. -/
noncomputable def sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    Fin (Q.boundary (e.faceEquiv f)).length := by
  have hpos : 0 < (Q.boundary (e.faceEquiv f)).length :=
    List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  exact ⟨(i.val + e.faceRotation f) %
    (Q.boundary (e.faceEquiv f)).length, Nat.mod_lt _ hpos⟩

@[simp]
theorem sideIndex_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (e.sideIndex validQ f i).val =
      (i.val + e.faceRotation f) %
        (Q.boundary (e.faceEquiv f)).length :=
  rfl

/-- The rotated target side carries exactly the relabeled source dart. -/
theorem boundary_get_sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  let target := Q.boundary (e.faceEquiv f)
  let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
  have hrot : target.rotate (e.faceRotation f) = mapped :=
    e.rotate_target_boundary f
  have hlen : target.length = mapped.length := by
    rw [← hrot, List.length_rotate]
  have hiTarget : i.val < target.length := by
    rw [hlen]
    simpa only [mapped, List.length_map] using i.isLt
  have hpoint :
      (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
    congrArg (fun word => word[i.val]?) hrot
  rw [List.getElem?_rotate hiTarget] at hpoint
  have hmapped :
      mapped[i.val]? =
        some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
    simp [mapped, i.isLt]
  rw [hmapped] at hpoint
  have htarget :
      target.get
          ⟨(i.val + e.faceRotation f) % target.length,
            Nat.mod_lt _ (List.length_pos_of_ne_nil
              (validQ.2.1 (e.faceEquiv f)))⟩ =
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
    rw [← Option.some_inj, ← hpoint]
    simp
  exact htarget

/-- The disk homeomorphism on a face selected by the cyclic boundary rotation. -/
noncomputable def faceHomeomorph (e : SignedPresentationIso P Q) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell (Q.boundary (e.faceEquiv f)).length :=
  PolygonCell.rotateHomeomorph (e.boundary_length_eq f) (e.faceRotation f)

/-- A signed presentation isomorphism gives a facewise homeomorphism of polygonal
pre-realizations. -/
noncomputable def preHomeomorph (e : SignedPresentationIso P Q) :
    P.PolygonalPreRealization ≃ₜ Q.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap e.faceEquiv.bijective
      (fun f => (e.faceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map e.faceEquiv fun f => e.faceHomeomorph f)

@[simp]
theorem preHomeomorph_apply_fst (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).1 = e.faceEquiv x.1 :=
  rfl

@[simp]
theorem preHomeomorph_apply_snd (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).2 = e.faceHomeomorph x.1 x.2 :=
  rfl

/-- On a labelled side, the pre-realization homeomorphism is exactly the selected cyclic shift. -/
theorem preHomeomorph_side (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    e.preHomeomorph ⟨f, PolygonCell.side i t⟩ =
      ⟨e.faceEquiv f, PolygonCell.side (e.sideIndex validQ f i) t⟩ := by
  apply Sigma.ext
  · rfl
  · simp only [preHomeomorph_apply_snd, faceHomeomorph]
    apply heq_of_eq
    exact PolygonCell.rotateHomeomorph_side_of_eq
        (e.boundary_length_eq f)
        (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
        (e.faceRotation f) i t

/-- Transport a boundary occurrence through the selected cyclic shift. -/
noncomputable def mapOccurrence (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence → Q.BoundaryOccurrence
  | ⟨f, i⟩ => ⟨e.faceEquiv f, e.sideIndex validQ f i⟩

@[simp]
theorem mapOccurrence_fst (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).1 = e.faceEquiv o.1 := by
  cases o
  rfl

@[simp]
theorem mapOccurrence_snd_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).2.val =
      (o.2.val + e.faceRotation o.1) %
        (Q.boundary (e.faceEquiv o.1)).length := by
  cases o
  rfl

/-- The transported occurrence carries the signed relabeling of the source dart. -/
theorem mapOccurrence_dart (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).dart =
      e.edgeRelabeling.mapDart o.dart := by
  rcases o with ⟨f, i⟩
  exact e.boundary_get_sideIndex validQ f i

/-- Cyclic shifting is injective on the finite side-index type. -/
private theorem sideIndex_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face) :
    Function.Injective (e.sideIndex validQ f) := by
  intro i j hij
  have hlen := e.boundary_length_eq f
  have hmod :
      i.val + e.faceRotation f ≡ j.val + e.faceRotation f
        [MOD (Q.boundary (e.faceEquiv f)).length] := by
    exact congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD (Q.boundary (e.faceEquiv f)).length] :=
    Nat.ModEq.add_right_cancel' (e.faceRotation f) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← hlen, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

/-- Transport of boundary occurrences is injective. -/
theorem mapOccurrence_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    Function.Injective (e.mapOccurrence validQ) := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hface : f = g := by
    apply e.faceEquiv.injective
    exact congrArg Sigma.fst h
  subst g
  have hindex : i = j := by
    apply e.sideIndex_injective validQ f
    exact eq_of_heq ((Sigma.ext_iff.mp h).2)
  subst j
  rfl

@[simp]
theorem mapOccurrence_edge (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).edge = e.edgeEquiv o.edge := by
  rw [BoundaryOccurrence.edge, e.mapOccurrence_dart,
    EdgeRelabeling.edgeOfDart_mapDart]
  rfl

/-- A compatible source pairing transports to a compatible target pairing. -/
noncomputable def mapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    Q.BoundaryPairing where
  source := e.mapOccurrence validQ pairing.source
  target := e.mapOccurrence validQ pairing.target
  source_ne_target :=
    (e.mapOccurrence_injective validQ).ne pairing.source_ne_target
  source_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.source.edge).not.mp
      pairing.source_not_boundary
  target_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.target.edge).not.mp
      pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible]
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible,
        EdgeRelabeling.mapDart_flip]

@[simp]
theorem mapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).direction = pairing.direction :=
  rfl

@[simp]
theorem mapPairing_source (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).source =
      e.mapOccurrence validQ pairing.source :=
  rfl

@[simp]
theorem mapPairing_target (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).target =
      e.mapOccurrence validQ pairing.target :=
  rfl

/-- The pre-realization homeomorphism maps an occurrence-side point to its transported side. -/
theorem preHomeomorph_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph ((P.occurrenceSide o).point t) =
      (Q.occurrenceSide (e.mapOccurrence validQ o)).point t := by
  rcases o with ⟨f, i⟩
  exact e.preHomeomorph_side validQ f i t

/-- Ignoring cyclic shifts, corresponding boundary-occurrence types have the same cardinality. -/
noncomputable def rawOccurrenceEquiv (e : SignedPresentationIso P Q) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.sigmaCongr e.faceEquiv fun f =>
    (Fin.castOrderIso (e.boundary_length_eq f)).toEquiv

/-- The cyclic occurrence transport bundled as an equivalence. -/
noncomputable def occurrenceEquiv (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.ofBijective (e.mapOccurrence validQ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨e.mapOccurrence_injective validQ,
        Fintype.card_congr e.rawOccurrenceEquiv⟩)

@[simp]
theorem occurrenceEquiv_apply (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    e.occurrenceEquiv validQ o = e.mapOccurrence validQ o :=
  rfl

@[simp]
theorem mapOccurrence_occurrenceEquiv_symm
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.mapOccurrence validQ ((e.occurrenceEquiv validQ).symm o) = o :=
  (e.occurrenceEquiv validQ).apply_symm_apply o

theorem preHomeomorph_symm_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph.symm ((Q.occurrenceSide o).point t) =
      (P.occurrenceSide ((e.occurrenceEquiv validQ).symm o)).point t := by
  apply e.preHomeomorph.injective
  rw [e.preHomeomorph.apply_symm_apply]
  rw [e.preHomeomorph_occurrenceSide_point validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

theorem occurrenceEquiv_symm_dart
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeRelabeling.mapDart ((e.occurrenceEquiv validQ).symm o).dart =
      o.dart := by
  rw [← e.mapOccurrence_dart validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

theorem occurrenceEquiv_symm_edge
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeEquiv ((e.occurrenceEquiv validQ).symm o).edge = o.edge := by
  rw [← e.mapOccurrence_edge validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/-- Pull a compatible target pairing back through the occurrence equivalence. -/
noncomputable def comapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    P.BoundaryPairing where
  source := (e.occurrenceEquiv validQ).symm pairing.source
  target := (e.occurrenceEquiv validQ).symm pairing.target
  source_ne_target :=
    (e.occurrenceEquiv validQ).symm.injective.ne pairing.source_ne_target
  source_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.source).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.source_not_boundary
  target_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.target).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      simpa only [EdgeRelabeling.dartEquiv_apply,
        e.occurrenceEquiv_symm_dart validQ] using hcompatible
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      rw [EdgeRelabeling.dartEquiv_apply, EdgeRelabeling.dartEquiv_apply,
        EdgeRelabeling.mapDart_flip, e.occurrenceEquiv_symm_dart,
        e.occurrenceEquiv_symm_dart]
      exact hcompatible

@[simp]
theorem comapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).direction = pairing.direction :=
  rfl

theorem preHomeomorph_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.source.point t) =
      ((e.mapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.source t

theorem preHomeomorph_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.target.point t) =
      ((e.mapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.target t

theorem preHomeomorph_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.mapPairing validQ pairing).identification.target.point
        ((e.mapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_pairing_target_point]
  rfl

/-- The facewise homeomorphism sends every source gluing generator into the target generated
relation. -/
theorem preHomeomorph_generator_related
    (e : SignedPresentationIso P Q) (_validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    Q.PolygonalGluingRel validQ
      (e.preHomeomorph (pairing.identification.source.point t))
      (e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_pairing_source_point,
    e.preHomeomorph_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.mapPairing validQ pairing).identification
    (pairing_identification_mem validQ (e.mapPairing validQ pairing)) t

/-- The facewise homeomorphism preserves the complete generated gluing relation. -/
theorem preHomeomorph_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem preHomeomorph_symm_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.source.point t) =
      ((e.comapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.source t

theorem preHomeomorph_symm_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.target.point t) =
      ((e.comapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.target t

theorem preHomeomorph_symm_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.comapPairing validQ pairing).identification.target.point
        ((e.comapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_symm_pairing_target_point]
  rfl

/-- The inverse facewise homeomorphism sends every target generator into the source relation. -/
theorem preHomeomorph_symm_generator_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm (pairing.identification.source.point t))
      (e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_symm_pairing_source_point,
    e.preHomeomorph_symm_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.comapPairing validQ pairing).identification
    (pairing_identification_mem validP (e.comapPairing validQ pairing)) t

/-- The inverse facewise homeomorphism preserves the complete generated relation. -/
theorem preHomeomorph_symm_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : Q.PolygonalPreRealization}
    (hxy : Q.PolygonalGluingRel validQ x y) :
    P.PolygonalGluingRel validP (e.preHomeomorph.symm x)
      (e.preHomeomorph.symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (Q.polygonalIdentifications validQ)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_symm_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The selected pre-realization homeomorphism identifies the two generated gluing relations. -/
theorem preHomeomorph_related_iff
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  constructor
  · exact e.preHomeomorph_related validP validQ
  · intro hxy
    simpa only [e.preHomeomorph.symm_apply_apply] using
      e.preHomeomorph_symm_related validP validQ hxy

/-- Signed edge relabeling, face relabeling, and cyclic boundary rotation preserve the faithful
polygonal realization. -/
noncomputable def realizationHomeomorph
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ :=
  PolygonGluing.realizationCongr e.preHomeomorph
    (e.preHomeomorph_related_iff validP validQ)

/-- Propositional realization-invariance form used by elementary-move closures. -/
theorem polygonallyEquivalent
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  ⟨e.realizationHomeomorph validP validQ⟩

end FiniteCyclicPresentation.SignedPresentationIso

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification21_block_02
/- END ClassificationOfSurfaces.FiniteCyclicSignedRealization -/

/- BEGIN ClassificationOfSurfaces.GeometricTriangulationRealization | efa2810979decfb39a7fd11a6189f13ad62009e46d73583b1b895707458a1529 -/
section schottkyclassification21_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Faithful polygonal realization of a geometric triangulation

The local map in this file identifies each three-sided polygon cell with the corresponding
barycentric face.  Its side formula uses the cyclic face order exactly, so adjacent face maps
agree under the signed occurrence pairing.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

private theorem orientedEdge_eq_or_eq_flip_of_edge_eq
    {d e : OrientedEdge T.Edge} (h : d.edge = e.edge) :
    d = e ∨ d = e.flip := by
  cases d <;> cases e <;> simp_all [OrientedEdge.edge, OrientedEdge.flip]

/-- A three-sided polygon cell is canonically identified with one closed barycentric face. -/
noncomputable def faceCellHomeomorph (f : T.Triangle) :
    PolygonCell 3 ≃ₜ T.toIntrinsic.ClosedFace f :=
  TriangleCell.cellHomeomorph.trans
    (T.toIntrinsic.facePlaneHomeomorph f).symm

@[simp]
theorem faceVertexEmbedding_eq_cyclic (f : T.Triangle) (i : Fin 3) :
    T.toIntrinsic.faceVertexEmbedding f i =
      T.toIntrinsic.faceVertex f (ZMod.finEquiv 3 i) := by
  rw [← T.toIntrinsic.faceVertexEmbedding_cyclic]
  simp

/-- On cyclic side `i`, the face-cell map is the affine barycentric path from face vertex `i`
to face vertex `i+1`. -/
theorem faceCellHomeomorph_side (f : T.Triangle) (i : Fin 3)
    (r : unitInterval) :
    ((T.faceCellHomeomorph f) (PolygonCell.side i r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single (T.toIntrinsic.faceVertexEmbedding f i) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ)
        (Pi.single (T.toIntrinsic.faceVertexEmbedding f (finRotate 3 i)) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ) r := by
  rw [faceCellHomeomorph, Homeomorph.trans_apply,
    TriangleCell.cellHomeomorph_side,
    T.toIntrinsic.facePlaneHomeomorph_symm_val]
  change T.toIntrinsic.facePlaneInverseAffine f
      (AffineMap.lineMap (Moise.standardTriangleVertex i)
        (Moise.standardTriangleVertex (finRotate 3 i)) (r : ℝ)) = _
  rw [AffineMap.apply_lineMap,
    T.toIntrinsic.facePlaneInverseAffine_standardVertex f i,
    T.toIntrinsic.facePlaneInverseAffine_standardVertex f (finRotate 3 i)]

/-- Recover the geometric triangle represented by an enumerated cyclic face. -/
noncomputable def cyclicFace (f : T.toFiniteCyclicPresentation.Face) : T.Triangle :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm f

@[simp]
theorem cyclicFace_finiteCyclicFaceEquiv (f : T.Triangle) :
    T.cyclicFace
      (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f) = f :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f

@[simp]
theorem finiteCyclicFaceEquiv_cyclicFace
    (f : T.toFiniteCyclicPresentation.Face) :
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace f) = f :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.apply_symm_apply f

/-- Every polygon appearing in the cyclic presentation of a triangulation has three marked
sides. -/
theorem cyclicBoundaryLength (f : T.toFiniteCyclicPresentation.Face) :
    (T.toFiniteCyclicPresentation.boundary f).length = 3 := by
  rw [← T.finiteCyclicFaceEquiv_cyclicFace f]
  exact (T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_boundary_faceEquiv_length
    (T.cyclicFace f)).trans
      (T.triangleBoundary_length (T.cyclicFace f))

/-- The enumerated polygon for `f`, including its stored side-count type, is homeomorphic to the
corresponding closed geometric face. -/
noncomputable def polygonFaceHomeomorph
    (f : T.toFiniteCyclicPresentation.Face) :
    PolygonCell (T.toFiniteCyclicPresentation.boundary f).length ≃ₜ
      T.toIntrinsic.ClosedFace (T.cyclicFace f) :=
  (PolygonCell.castHomeomorph (T.cyclicBoundaryLength f)).trans
    (T.faceCellHomeomorph (T.cyclicFace f))

/-- The facewise map on the disjoint union of cyclic polygon cells. -/
noncomputable def polygonalPreMap :
    T.toFiniteCyclicPresentation.PolygonalPreRealization → T.realization :=
  fun x => (T.polygonFaceHomeomorph x.1 x.2).1

theorem continuous_polygonalPreMap : Continuous T.polygonalPreMap := by
  apply continuous_sigma
  intro f
  exact continuous_subtype_val.comp (T.polygonFaceHomeomorph f).continuous

/-- The original oriented geometric edge stored at an enumerated boundary occurrence. -/
noncomputable def cyclicOrientedEdge
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    OrientedEdge T.Edge :=
  T.orientedFaceEdge (T.cyclicFace o.1)
    (ZMod.finEquiv 3 (Fin.cast (T.cyclicBoundaryLength o.1) o.2))

/-- The boundary occurrence belonging to a specified `Fin 3` side of an enumerated face. -/
noncomputable def cyclicOccurrence
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    T.toFiniteCyclicPresentation.BoundaryOccurrence :=
  ⟨f, Fin.cast (T.cyclicBoundaryLength f).symm i⟩

@[simp]
theorem cyclicOccurrence_face
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    (T.cyclicOccurrence f i).1 = f :=
  rfl

@[simp]
theorem cyclicOccurrence_index_cast
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    Fin.cast (T.cyclicBoundaryLength f) (T.cyclicOccurrence f i).2 = i := by
  apply Fin.ext
  rfl

@[simp]
theorem cyclicOrientedEdge_cyclicOccurrence
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    T.cyclicOrientedEdge (T.cyclicOccurrence f i) =
      T.orientedFaceEdge (T.cyclicFace f) (ZMod.finEquiv 3 i) := by
  simp [cyclicOrientedEdge, cyclicOccurrence]
  rfl

@[simp]
theorem finiteCyclicDartEquiv_cyclicOrientedEdge
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
        (T.cyclicOrientedEdge o) = o.dart := by
  obtain ⟨p, rfl⟩ :=
    T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv.surjective o
  change T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
      (T.cyclicOrientedEdge
        (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p)) =
    (T.toFiniteCyclicPresentation.boundary
      (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p).1).get
        (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p).2
  rw [T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv_dart]
  congr 1
  rcases p with ⟨f, i⟩
  change T.cyclicOrientedEdge
      (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv ⟨f, i⟩) =
    (T.triangleBoundary f).get i
  refine Eq.trans ?_ (T.triangleBoundary_get f i).symm
  simp only [cyclicOrientedEdge, cyclicFace,
    FiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv]
  congr
  exact T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f

@[simp]
theorem finiteCyclicDartEquiv_flip (d : OrientedEdge T.Edge) :
    T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d.flip =
      (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d).flip := by
  cases d <;> rfl

@[simp]
theorem orientedEdgeSource_flip (d : OrientedEdge T.Edge) :
    T.orientedEdgeSource d.flip = T.orientedEdgeTarget d := by
  cases d <;> rfl

@[simp]
theorem orientedEdgeTarget_flip (d : OrientedEdge T.Edge) :
    T.orientedEdgeTarget d.flip = T.orientedEdgeSource d := by
  cases d <;> rfl

/-- The enumerated side parameter is carried to the corresponding affine edge parameter. -/
theorem polygonFaceHomeomorph_side
    (f : T.toFiniteCyclicPresentation.Face)
    (i : Fin (T.toFiniteCyclicPresentation.boundary f).length)
    (r : unitInterval) :
    ((T.polygonFaceHomeomorph f) (PolygonCell.side i r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single
          (T.toIntrinsic.faceVertexEmbedding (T.cyclicFace f)
            (Fin.cast (T.cyclicBoundaryLength f) i)) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ)
        (Pi.single
          (T.toIntrinsic.faceVertexEmbedding (T.cyclicFace f)
            (finRotate 3 (Fin.cast (T.cyclicBoundaryLength f) i))) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ) r := by
  rw [polygonFaceHomeomorph, Homeomorph.trans_apply,
    PolygonCell.castHomeomorph_side, T.faceCellHomeomorph_side]

/-- The affine endpoints of an enumerated side are the source and target of its original
oriented geometric edge. -/
theorem polygonFaceHomeomorph_side_oriented
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence)
    (r : unitInterval) :
    ((T.polygonFaceHomeomorph o.1) (PolygonCell.side o.2 r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single (T.orientedEdgeSource (T.cyclicOrientedEdge o)) (1 : ℝ) :
          T.Vertex → ℝ)
        (Pi.single (T.orientedEdgeTarget (T.cyclicOrientedEdge o)) (1 : ℝ) :
          T.Vertex → ℝ) r := by
  rw [T.polygonFaceHomeomorph_side]
  rw [cyclicOrientedEdge, T.orientedFaceEdge_source, T.orientedFaceEdge_target,
    T.faceVertexEmbedding_eq_cyclic]
  congr 3
  rw [T.faceVertexEmbedding_eq_cyclic]
  apply congrArg (T.toIntrinsic.faceVertex (T.cyclicFace o.1))
  have hrotate (i : Fin 3) :
      ZMod.finEquiv 3 (finRotate 3 i) = ZMod.finEquiv 3 i + 1 := by
    fin_cases i <;> rfl
  exact hrotate _

/-- Every point of a geometric edge has the affine parameterization determined by either
orientation of that edge. -/
theorem exists_orientedEdgeParameter
    (d : OrientedEdge T.Edge) (x : T.realization)
    (hx : x ∈ T.toIntrinsic.faceCarrier d.edge.1) :
    ∃ r : unitInterval,
      x.1 = AffineMap.lineMap (k := ℝ)
        (Pi.single (T.orientedEdgeSource d) (1 : ℝ) : T.Vertex → ℝ)
        (Pi.single (T.orientedEdgeTarget d) (1 : ℝ) : T.Vertex → ℝ) r := by
  let a := T.orientedEdgeSource d
  let b := T.orientedEdgeTarget d
  have hab : d.edge.1 = {a, b} := by
    cases d with
    | pos e => exact T.edge_eq_pair e
    | neg e =>
        simpa [a, b, orientedEdgeSource, orientedEdgeTarget,
          OrientedEdge.edge, Finset.pair_comm] using T.edge_eq_pair e
  have hne : a ≠ b := by
    cases d with
    | pos e => exact T.edgeSource_ne_edgeTarget e
    | neg e => exact (T.edgeSource_ne_edgeTarget e).symm
  let r : unitInterval :=
    ⟨x.1 b, mem_Icc_of_mem_stdSimplex x.2.1 b⟩
  have hsum : x.1 a + x.1 b = 1 := by
    calc
      x.1 a + x.1 b = ∑ v ∈ d.edge.1, x.1 v := by
        rw [hab]
        simp [hne]
      _ = ∑ v, x.1 v := Finset.sum_subset (Finset.subset_univ d.edge.1)
        (fun v _ hv => hx v hv)
      _ = 1 := x.2.1.2
  refine ⟨r, ?_⟩
  funext v
  rw [AffineMap.lineMap_apply_module]
  by_cases hva : v = a
  · subst v
    simp [a, b, r, hne]
    linarith
  · by_cases hvb : v = b
    · subst v
      simp [a, b, r, hne]
    · have hv : v ∉ d.edge.1 := by
        rw [hab]
        simp [hva, hvb]
      rw [hx v hv]
      simp [a, b, r, hva, hvb]

/-- Compatible signed occurrence pairings have identical images under the facewise geometric
map. -/
theorem polygonalPreMap_pairing_eq
    (pairing : T.toFiniteCyclicPresentation.BoundaryPairing)
    (r : unitInterval) :
    T.polygonalPreMap (pairing.identification.source.point r) =
      T.polygonalPreMap
        (pairing.identification.target.point
          (pairing.identification.parameter r)) := by
  apply Subtype.ext
  change
    ((T.polygonFaceHomeomorph pairing.source.1)
      (PolygonCell.side pairing.source.2 r)).1.1 =
    ((T.polygonFaceHomeomorph pairing.target.1)
      (PolygonCell.side pairing.target.2
        (pairing.direction.homeomorph r))).1.1
  rw [T.polygonFaceHomeomorph_side_oriented,
    T.polygonFaceHomeomorph_side_oriented]
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      have hedge :
          T.cyclicOrientedEdge pairing.target =
            T.cyclicOrientedEdge pairing.source := by
        apply T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv.injective
        rw [T.finiteCyclicDartEquiv_cyclicOrientedEdge,
          T.finiteCyclicDartEquiv_cyclicOrientedEdge, hcompatible]
      simp only [PolygonGluing.ParameterDirection.homeomorph_same_apply]
      rw [hedge]
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      have hedge :
          T.cyclicOrientedEdge pairing.target =
            (T.cyclicOrientedEdge pairing.source).flip := by
        apply T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv.injective
        rw [T.finiteCyclicDartEquiv_cyclicOrientedEdge,
          T.finiteCyclicDartEquiv_flip,
          T.finiteCyclicDartEquiv_cyclicOrientedEdge, hcompatible]
      simp only [PolygonGluing.ParameterDirection.homeomorph_opposite_apply]
      rw [hedge, T.orientedEdgeSource_flip, T.orientedEdgeTarget_flip,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_one_sub]

/-- The facewise map is constant on the equivalence relation generated by all compatible
pairings. -/
theorem polygonalPreMap_respects
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {x y : T.toFiniteCyclicPresentation.PolygonalPreRealization}
    (hxy : T.toFiniteCyclicPresentation.PolygonalGluingRel valid x y) :
    T.polygonalPreMap x = T.polygonalPreMap y := by
  induction hxy with
  | rel x y h =>
      cases h with
      | glue identification hidentification r =>
          rcases hidentification with ⟨pairing, rfl⟩
          exact T.polygonalPreMap_pairing_eq pairing r
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Descend the calibrated face maps through the cyclic polygonal quotient. -/
noncomputable def polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid → T.realization :=
  Quotient.lift T.polygonalPreMap fun _ _ h => T.polygonalPreMap_respects valid h

@[simp]
theorem polygonalRealizationMap_mk
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.toFiniteCyclicPresentation.PolygonalPreRealization) :
    T.polygonalRealizationMap valid
        (T.toFiniteCyclicPresentation.polygonalMk valid x) =
      T.polygonalPreMap x :=
  rfl

theorem continuous_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Continuous (T.polygonalRealizationMap valid) :=
  T.continuous_polygonalPreMap.quotient_lift fun _ _ h =>
    T.polygonalPreMap_respects valid h

theorem surjective_polygonalPreMap :
    Function.Surjective T.polygonalPreMap := by
  intro x
  have hxall : x ∈ ⋃ f : T.Triangle, T.toIntrinsic.faceCarrier f.1 := by
    rw [← T.toIntrinsic.realization_eq_iUnion_faceCarrier]
    trivial
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxall
  let pf := T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f
  have hface : T.cyclicFace pf = f :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f
  let xf : T.toIntrinsic.ClosedFace (T.cyclicFace pf) :=
    ⟨x, hface ▸ hxf⟩
  let z := (T.polygonFaceHomeomorph pf).symm xf
  refine ⟨⟨pf, z⟩, ?_⟩
  change ((T.polygonFaceHomeomorph pf) z).1 = x
  rw [Homeomorph.apply_symm_apply]

theorem surjective_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Function.Surjective (T.polygonalRealizationMap valid) := by
  intro x
  obtain ⟨z, rfl⟩ := T.surjective_polygonalPreMap x
  exact ⟨T.toFiniteCyclicPresentation.polygonalMk valid z, rfl⟩

/-- Two distinct occurrences carrying the same oriented geometric edge identify equal side
parameters in the polygonal quotient. -/
theorem polygonalMk_side_eq_of_orientedEdge_eq
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {o p : T.toFiniteCyclicPresentation.BoundaryOccurrence}
    (hop : o ≠ p) (hedge : T.cyclicOrientedEdge p = T.cyclicOrientedEdge o)
    (r : unitInterval) :
    T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
      T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide p).point r) := by
  have hdart : p.dart = o.dart := by
    rw [← T.finiteCyclicDartEquiv_cyclicOrientedEdge,
      ← T.finiteCyclicDartEquiv_cyclicOrientedEdge, hedge]
  have hedgeName : p.edge = o.edge := congrArg FiniteCyclicPresentation.edgeOfDart hdart
  have hsource :=
    T.toFiniteCyclicPresentation.not_isBoundaryEdge_of_ne_of_edge_eq hop hedgeName
  have htarget : ¬T.toFiniteCyclicPresentation.IsBoundaryEdge p.edge := by
    rw [hedgeName]
    exact hsource
  let pairing : T.toFiniteCyclicPresentation.BoundaryPairing :=
    { source := o
      target := p
      source_ne_target := hop
      source_not_boundary := hsource
      target_not_boundary := htarget
      direction := .same
      compatible := hdart }
  have h :=
    T.toFiniteCyclicPresentation.polygonalMk_pairing_eq valid pairing r
  change T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
    T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide p).point r) at h
  exact h

/-- Two distinct occurrences carrying oppositely oriented copies of one geometric edge identify
opposite side parameters in the polygonal quotient. -/
theorem polygonalMk_side_eq_of_orientedEdge_eq_flip
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {o p : T.toFiniteCyclicPresentation.BoundaryOccurrence}
    (hop : o ≠ p)
    (hedge : T.cyclicOrientedEdge p = (T.cyclicOrientedEdge o).flip)
    (r : unitInterval) :
    T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
      T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide p).point
          (unitInterval.symm r)) := by
  have hdart : p.dart = o.dart.flip := by
    calc
      p.dart =
          T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
            (T.cyclicOrientedEdge p) :=
        (T.finiteCyclicDartEquiv_cyclicOrientedEdge p).symm
      _ = T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
          (T.cyclicOrientedEdge o).flip := congrArg _ hedge
      _ = (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
          (T.cyclicOrientedEdge o)).flip :=
        T.finiteCyclicDartEquiv_flip _
      _ = o.dart.flip :=
        congrArg SurfaceCellComplex.SignedDart.flip
          (T.finiteCyclicDartEquiv_cyclicOrientedEdge o)
  have hedgeName : p.edge = o.edge := by
    change FiniteCyclicPresentation.edgeOfDart p.dart =
      FiniteCyclicPresentation.edgeOfDart o.dart
    rw [hdart]
    cases o.dart <;> rfl
  have hsource :=
    T.toFiniteCyclicPresentation.not_isBoundaryEdge_of_ne_of_edge_eq hop hedgeName
  have htarget : ¬T.toFiniteCyclicPresentation.IsBoundaryEdge p.edge := by
    rw [hedgeName]
    exact hsource
  let pairing : T.toFiniteCyclicPresentation.BoundaryPairing :=
    { source := o
      target := p
      source_ne_target := hop
      source_not_boundary := hsource
      target_not_boundary := htarget
      direction := .opposite
      compatible := hdart }
  have h :=
    T.toFiniteCyclicPresentation.polygonalMk_pairing_eq valid pairing r
  change T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
    T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide p).point
        (unitInterval.symm r)) at h
  exact h

/-- Invert one calibrated face map and include that polygon in the quotient. -/
noncomputable def faceQuotientMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face) :
    T.toIntrinsic.ClosedFace (T.cyclicFace f) →
      T.toFiniteCyclicPresentation.PolygonalRealization valid :=
  fun x => T.toFiniteCyclicPresentation.polygonalMk valid
    ⟨f, (T.polygonFaceHomeomorph f).symm x⟩

/-- Transport a closed face along equality of its face name. -/
noncomputable def closedFaceCastHomeomorph
    {f g : T.Triangle} (h : f = g) :
    T.toIntrinsic.ClosedFace f ≃ₜ T.toIntrinsic.ClosedFace g := by
  subst g
  exact Homeomorph.refl _

@[simp]
theorem closedFaceCastHomeomorph_val
    {f g : T.Triangle} (h : f = g)
    (x : T.toIntrinsic.ClosedFace f) :
    (T.closedFaceCastHomeomorph h x).1 = x.1 := by
  subst g
  rfl

theorem continuous_faceQuotientMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face) :
    Continuous (T.faceQuotientMap valid f) :=
  T.toFiniteCyclicPresentation.continuous_polygonalMk valid |>.comp
    (continuous_sigmaMk.comp (T.polygonFaceHomeomorph f).symm.continuous)

/-- Changing only the proof-level name of a packed face does not change its inverse quotient
value. -/
theorem faceQuotientMap_congr
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {f g : T.toFiniteCyclicPresentation.Face} (hfg : f = g)
    (x : T.toIntrinsic.ClosedFace (T.cyclicFace f))
    (y : T.toIntrinsic.ClosedFace (T.cyclicFace g))
    (hxy : x.1 = y.1) :
    T.faceQuotientMap valid f x = T.faceQuotientMap valid g y := by
  subst g
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

@[simp]
theorem faceQuotientMap_faceHomeomorph
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face)
    (z : PolygonCell (T.toFiniteCyclicPresentation.boundary f).length) :
    T.faceQuotientMap valid f (T.polygonFaceHomeomorph f z) =
      T.toFiniteCyclicPresentation.polygonalMk valid ⟨f, z⟩ := by
  simp [faceQuotientMap]

/-- The two inverse face maps agree in the quotient along a common geometric edge. -/
theorem faceQuotientMap_eq_of_inter_card_two
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {f g : T.toFiniteCyclicPresentation.Face} (hfg : f ≠ g)
    (hcard : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card = 2)
    (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace f).1)
    (hxg : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace g).1) :
    T.faceQuotientMap valid f ⟨x, hxf⟩ =
      T.faceQuotientMap valid g ⟨x, hxg⟩ := by
  let e : T.Edge :=
    ⟨(T.cyclicFace f).1 ∩ (T.cyclicFace g).1, by
      change (T.cyclicFace f).1 ∩ (T.cyclicFace g).1 ∈
        T.faces.biUnion fun t => t.powersetCard 2
      apply Finset.mem_biUnion.mpr
      exact ⟨(T.cyclicFace f).1, (T.cyclicFace f).2,
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hcard⟩⟩⟩
  have hef : e.1 ⊆ (T.cyclicFace f).1 := Finset.inter_subset_left
  have heg : e.1 ⊆ (T.cyclicFace g).1 := Finset.inter_subset_right
  obtain ⟨i, hi⟩ :=
    T.toIntrinsic.exists_faceEdge_eq_of_subset (T.cyclicFace f) e hef
  obtain ⟨j, hj⟩ :=
    T.toIntrinsic.exists_faceEdge_eq_of_subset (T.cyclicFace g) e heg
  let oi : Fin 3 := (ZMod.finEquiv 3).symm i
  let oj : Fin 3 := (ZMod.finEquiv 3).symm j
  have hoedge :
      (T.cyclicOrientedEdge (T.cyclicOccurrence f oi)).edge = e := by
    rw [cyclicOrientedEdge_cyclicOccurrence, T.orientedFaceEdge_edge]
    exact (congrArg (T.toIntrinsic.faceEdge (T.cyclicFace f))
      ((ZMod.finEquiv 3).apply_symm_apply i)).trans hi
  have hpedge :
      (T.cyclicOrientedEdge (T.cyclicOccurrence g oj)).edge = e := by
    rw [cyclicOrientedEdge_cyclicOccurrence, T.orientedFaceEdge_edge]
    exact (congrArg (T.toIntrinsic.faceEdge (T.cyclicFace g))
      ((ZMod.finEquiv 3).apply_symm_apply j)).trans hj
  have hxedge : x ∈ T.toIntrinsic.faceCarrier e.1 := by
    rw [← T.toIntrinsic.faceCarrier_inter]
    exact ⟨hxf, hxg⟩
  obtain ⟨r, hxr⟩ :=
    T.exists_orientedEdgeParameter
      (T.cyclicOrientedEdge (T.cyclicOccurrence f oi)) x
      (hoedge ▸ hxedge)
  have hop : T.cyclicOccurrence f oi ≠ T.cyclicOccurrence g oj := by
    intro hop
    apply hfg
    exact congrArg Sigma.fst hop
  rcases orientedEdge_eq_or_eq_flip_of_edge_eq T
      (hpedge.trans hoedge.symm) with horiented | horiented
  · have hfo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence f oi).1
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) =
          ⟨x, by simpa using hxf⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented]
      exact hxr.symm
    have hfo :
        T.polygonFaceHomeomorph f
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) = ⟨x, hxf⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hfo'
    have hgo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence g oj).1
            (PolygonCell.side (T.cyclicOccurrence g oj).2 r) =
          ⟨x, by simpa using hxg⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented, horiented]
      exact hxr.symm
    have hgo :
        T.polygonFaceHomeomorph g
            (PolygonCell.side (T.cyclicOccurrence g oj).2 r) = ⟨x, hxg⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hgo'
    rw [← hfo, ← hgo]
    refine (T.faceQuotientMap_faceHomeomorph valid f _).trans ?_
    refine Eq.trans ?_ (T.faceQuotientMap_faceHomeomorph valid g _).symm
    exact T.polygonalMk_side_eq_of_orientedEdge_eq valid hop horiented r
  · have hfo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence f oi).1
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) =
          ⟨x, by simpa using hxf⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented]
      exact hxr.symm
    have hfo :
        T.polygonFaceHomeomorph f
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) = ⟨x, hxf⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hfo'
    have hgo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence g oj).1
            (PolygonCell.side (T.cyclicOccurrence g oj).2
              (unitInterval.symm r)) =
          ⟨x, by simpa using hxg⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented, horiented,
        T.orientedEdgeSource_flip, T.orientedEdgeTarget_flip,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_one_sub]
      exact hxr.symm
    have hgo :
        T.polygonFaceHomeomorph g
            (PolygonCell.side (T.cyclicOccurrence g oj).2
              (unitInterval.symm r)) = ⟨x, hxg⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hgo'
    rw [← hfo, ← hgo]
    refine (T.faceQuotientMap_faceHomeomorph valid f _).trans ?_
    refine Eq.trans ?_ (T.faceQuotientMap_faceHomeomorph valid g _).symm
    exact T.polygonalMk_side_eq_of_orientedEdge_eq_flip valid hop horiented r

private theorem card_inter_eq_two_of_faceAdjacentAtVertex_of_ne
    {v : T.Vertex} {f g : T.Triangle}
    (hfg : f ≠ g)
    (hadj : TriangleFamily.FaceAdjacentAtVertex T.faces v f g) :
    (f.1 ∩ g.1).card = 2 := by
  rcases hadj with ⟨e, hecard, _hve, hef, heg⟩
  have heinter : e ⊆ f.1 ∩ g.1 := by
    intro w hw
    exact Finset.mem_inter.mpr ⟨hef hw, heg hw⟩
  have hlower : 2 ≤ (f.1 ∩ g.1).card := by
    rw [← hecard]
    exact Finset.card_le_card heinter
  have hupper : (f.1 ∩ g.1).card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ (f.1 ∩ g.1).card := by omega
    have hinterf : f.1 ∩ g.1 = f.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [T.triangle_card f]
        exact hthree)
    have hinterg : f.1 ∩ g.1 = g.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [T.triangle_card g]
        exact hthree)
    exact hfg (Subtype.ext (hinterf.symm.trans hinterg))
  omega

private theorem card_inter_le_two_of_ne
    {f g : T.Triangle} (hfg : f ≠ g) :
    (f.1 ∩ g.1).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ (f.1 ∩ g.1).card := by omega
  have hinterf : f.1 ∩ g.1 = f.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [T.triangle_card f]
      exact hthree)
  have hinterg : f.1 ∩ g.1 = g.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
      rw [T.triangle_card g]
      exact hthree)
  exact hfg (Subtype.ext (hinterf.symm.trans hinterg))

/-- At a fixed vertex, inverse face maps agree across one star-adjacency step. -/
theorem faceQuotientMap_eq_vertexPoint_of_faceAdjacentAtVertex
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (v : T.toIntrinsic.UsedVertex) {f g : T.Triangle}
    (hvf : v.1 ∈ f.1) (hvg : v.1 ∈ g.1)
    (hadj : TriangleFamily.FaceAdjacentAtVertex T.faces v.1 f g) :
    T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvf⟩ =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvg⟩ := by
  by_cases hfg : f = g
  · subst g
    rfl
  · have hpacked :
        T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f ≠
          T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g :=
      T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.injective.ne hfg
    have hcyclic :
        T.cyclicFace (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f) ≠
          T.cyclicFace
            (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g) := by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.cyclicFace_finiteCyclicFaceEquiv]
      exact hfg
    apply T.faceQuotientMap_eq_of_inter_card_two valid hpacked
      (T.card_inter_eq_two_of_faceAdjacentAtVertex_of_ne hcyclic (by
        simpa only [T.cyclicFace_finiteCyclicFaceEquiv] using hadj))

/-- Strong fixed-star connectivity makes the quotient value of a vertex independent of the
incident face used to compute it. -/
theorem faceQuotientMap_eq_vertexPoint
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (v : T.toIntrinsic.UsedVertex) (f g : T.Triangle)
    (hvf : v.1 ∈ f.1) (hvg : v.1 ∈ g.1) :
    T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvf⟩ =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvg⟩ := by
  have hpath := hstar v.1 f g hvf hvg
  induction hpath with
  | refl => rfl
  | tail hpath hstep ih =>
      have hvleft :
          v.1 ∈ _ :=
        TriangleFamily.mem_of_reflTransGen_faceAdjacentAtVertex hvf hpath
      have hvright :
          v.1 ∈ _ :=
        TriangleFamily.mem_right_of_faceAdjacentAtVertex hstep
      exact (ih hvleft).trans
        (T.faceQuotientMap_eq_vertexPoint_of_faceAdjacentAtVertex
          valid v hvleft hvright hstep)

/-- Under strong fixed-star connectivity, inverse face maps agree on every face overlap. -/
theorem faceQuotientMap_eq_of_mem
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (f g : T.toFiniteCyclicPresentation.Face) (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace f).1)
    (hxg : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace g).1) :
    T.faceQuotientMap valid f ⟨x, hxf⟩ =
      T.faceQuotientMap valid g ⟨x, hxg⟩ := by
  by_cases hfg : f = g
  · subst g
    rfl
  have hcyclic : T.cyclicFace f ≠ T.cyclicFace g := by
    intro h
    apply hfg
    calc
      f = T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.cyclicFace f) := (T.finiteCyclicFaceEquiv_cyclicFace f).symm
      _ = T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.cyclicFace g) := congrArg _ h
      _ = g := T.finiteCyclicFaceEquiv_cyclicFace g
  by_cases htwo : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card = 2
  · exact T.faceQuotientMap_eq_of_inter_card_two valid hfg htwo x hxf hxg
  have hle : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card ≤ 1 := by
    have :=
      T.card_inter_le_two_of_ne hcyclic
    omega
  have hxinter :
      x ∈ T.toIntrinsic.faceCarrier
        ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1) := by
    rw [← T.toIntrinsic.faceCarrier_inter]
    exact ⟨hxf, hxg⟩
  obtain ⟨v, hxv⟩ :=
    T.toIntrinsic.exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
      (T.cyclicFace f) Finset.inter_subset_left hle hxinter
  have hvf : v.1 ∈ (T.cyclicFace f).1 := by
    apply (T.toIntrinsic.vertexPoint_mem_faceCarrier_iff v _).mp
    rw [← hxv]
    exact hxf
  have hvg : v.1 ∈ (T.cyclicFace g).1 := by
    apply (T.toIntrinsic.vertexPoint_mem_faceCarrier_iff v _).mp
    rw [← hxv]
    exact hxg
  have hvertex := T.faceQuotientMap_eq_vertexPoint valid hstar v
    (T.cyclicFace f) (T.cyclicFace g) hvf hvg
  subst x
  let pf :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace f)
  let pg :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace g)
  let xf' : T.toIntrinsic.ClosedFace (T.cyclicFace pf) :=
    ⟨T.toIntrinsic.vertexPoint v, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
      exact hvf⟩
  let xg' : T.toIntrinsic.ClosedFace (T.cyclicFace pg) :=
    ⟨T.toIntrinsic.vertexPoint v, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
      exact hvg⟩
  have hmiddle :
      T.faceQuotientMap valid pf xf' =
        T.faceQuotientMap valid pg xg' := by
    exact hvertex
  calc
    T.faceQuotientMap valid f
        ⟨T.toIntrinsic.vertexPoint v, hxf⟩ =
        T.faceQuotientMap valid pf xf' := by
      apply T.faceQuotientMap_congr valid
        (T.finiteCyclicFaceEquiv_cyclicFace f).symm
      rfl
    _ = T.faceQuotientMap valid pg xg' := hmiddle
    _ = T.faceQuotientMap valid g
        ⟨T.toIntrinsic.vertexPoint v, hxg⟩ := by
      apply T.faceQuotientMap_congr valid
        (T.finiteCyclicFaceEquiv_cyclicFace g)
      rfl

/-- Choose one containing face and use its inverse face map. Overlap compatibility makes this
choice immaterial. -/
noncomputable def realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.realization) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid :=
  let f := T.toIntrinsic.containingFace x
  T.faceQuotientMap valid
    (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
    ⟨x, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv]
      exact T.toIntrinsic.mem_faceCarrier_containingFace x⟩

theorem realizationInverse_eqOn_face
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (f : T.Triangle) (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier f.1) :
    T.realizationInverse valid x =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨x, by
          rw [T.cyclicFace_finiteCyclicFaceEquiv]
          exact hxf⟩ := by
  unfold realizationInverse
  apply T.faceQuotientMap_eq_of_mem valid hstar

theorem continuous_realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    Continuous (T.realizationInverse valid) := by
  let carriers : T.Triangle → Set T.realization :=
    fun f => T.toIntrinsic.faceCarrier f.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ f : T.Triangle, IsClosed (carriers f) :=
    fun f => T.toIntrinsic.faceCarrier_closed f.1
  have hlocal : ∀ f : T.Triangle,
      ContinuousOn (T.realizationInverse valid) (carriers f) := by
    intro f
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : T.toIntrinsic.ClosedFace f =>
      T.realizationInverse valid x.1)
    let pf := T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f
    have hface : T.cyclicFace pf = f :=
      T.cyclicFace_finiteCyclicFaceEquiv f
    have hc : Continuous (fun x : T.toIntrinsic.ClosedFace f =>
        T.faceQuotientMap valid pf
          (T.closedFaceCastHomeomorph hface.symm x)) :=
      (T.continuous_faceQuotientMap valid pf).comp
        (T.closedFaceCastHomeomorph hface.symm).continuous
    apply hc.congr
    intro x
    symm
    refine (T.realizationInverse_eqOn_face valid hstar f x.1 x.2).trans ?_
    apply T.faceQuotientMap_congr valid rfl
    exact (T.closedFaceCastHomeomorph_val hface.symm x).symm
  exact hfinite.continuous
    T.toIntrinsic.realization_eq_iUnion_faceCarrier.symm hclosed hlocal

theorem polygonalRealizationMap_realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.realization) :
    T.polygonalRealizationMap valid (T.realizationInverse valid x) = x := by
  unfold realizationInverse faceQuotientMap
  change
    ((T.polygonFaceHomeomorph
      (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
        (T.toIntrinsic.containingFace x)))
      ((T.polygonFaceHomeomorph
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.toIntrinsic.containingFace x))).symm ⟨x, _⟩)).1 = x
  rw [Homeomorph.apply_symm_apply]

theorem realizationInverse_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (q : T.toFiniteCyclicPresentation.PolygonalRealization valid) :
    T.realizationInverse valid (T.polygonalRealizationMap valid q) = q := by
  induction q using Quotient.inductionOn with
  | _ z =>
      rcases z with ⟨f, z⟩
      have hz :=
        (T.polygonFaceHomeomorph f z).2
      change T.realizationInverse valid (T.polygonFaceHomeomorph f z).1 = _
      rw [T.realizationInverse_eqOn_face valid hstar (T.cyclicFace f)
        (T.polygonFaceHomeomorph f z).1 hz]
      calc
        T.faceQuotientMap valid
            (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
              (T.cyclicFace f))
            ⟨(T.polygonFaceHomeomorph f z).1, _⟩ =
            T.faceQuotientMap valid f (T.polygonFaceHomeomorph f z) := by
          apply T.faceQuotientMap_congr valid
            (T.finiteCyclicFaceEquiv_cyclicFace f)
          rfl
        _ = T.toFiniteCyclicPresentation.polygonalMk valid ⟨f, z⟩ :=
          T.faceQuotientMap_faceHomeomorph valid f z

/-- The faithful homeomorphism from the cyclic polygonal quotient to the barycentric geometric
realization. -/
noncomputable def polygonalRealizationHomeomorph
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ T.realization where
  toFun := T.polygonalRealizationMap valid
  invFun := T.realizationInverse valid
  left_inv := T.realizationInverse_polygonalRealizationMap valid hstar
  right_inv := T.polygonalRealizationMap_realizationInverse valid
  continuous_toFun := T.continuous_polygonalRealizationMap valid
  continuous_invFun := T.continuous_realizationInverse valid hstar

/-- Existence form used by the classification pipeline. -/
theorem polygonalRealization_homeomorphic
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    Nonempty
      (T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ
        T.realization) :=
  ⟨T.polygonalRealizationHomeomorph valid hstar⟩

/-- For a genuine surface triangulation, fixed-star connectivity follows from the manifold
charts, so the faithful polygonal realization needs no extra combinatorial hypothesis. -/
theorem polygonalRealization_homeomorphic_of_surface
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Nonempty
      (T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ
        T.realization) :=
  T.polygonalRealization_homeomorphic valid
    T.faces_isStrongVertexStarConnected

end GeometricTriangulation

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The Radó triangulation of a compact Eval surface has connected fixed-vertex stars. -/
theorem compact_eval_surface_geometricTriangulation_isStrongVertexStarConnected :
    TriangleFamily.IsStrongVertexStarConnected
      (compactEvalSurfaceGeometricTriangulation S).faces :=
  (compactEvalSurfaceGeometricTriangulation S).faces_isStrongVertexStarConnected

/-- The Eval-surface triangulation simultaneously carries cyclic validity, dual connectivity,
and the fixed-star connectivity used by the faithful geometric quotient. -/
theorem compact_eval_surface_polygonalRealization_certificates :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsSurfaceValid ∧
      TriangleFamily.IsDualConnected
        (compactEvalSurfaceGeometricTriangulation S).faces ∧
      TriangleFamily.IsStrongVertexStarConnected
        (compactEvalSurfaceGeometricTriangulation S).faces :=
  ⟨compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S,
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S).dual_connected,
    compact_eval_surface_geometricTriangulation_isStrongVertexStarConnected S⟩

/-- The polygonal quotient enumerated from the Radó triangulation is homeomorphic to its honest
barycentric geometric realization. -/
theorem compact_eval_surface_polygonalRealization_homeomorphic :
    Nonempty
      ((compactEvalSurfaceFiniteCyclicPresentation S).PolygonalRealization
          (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S) ≃ₜ
        (compactEvalSurfaceGeometricTriangulation S).realization) :=
  GeometricTriangulation.polygonalRealization_homeomorphic_of_surface
      (compactEvalSurfaceGeometricTriangulation S)
      (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S)

/-- Surface-level form of the geometric bridge: the valid polygonal quotient obtained from the
named Radó triangulation is homeomorphic to the original compact Eval surface. -/
theorem compact_eval_surface_polygonalRealization_homeomorphic_surface :
    Nonempty
      ((compactEvalSurfaceFiniteCyclicPresentation S).PolygonalRealization
          (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S) ≃ₜ S) := by
  exact Nonempty.map
    (fun h ↦ h.trans (compactEvalSurfaceGeometricTriangulation S).homeo)
    (compact_eval_surface_polygonalRealization_homeomorphic S)

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification21_block_03
/- END ClassificationOfSurfaces.GeometricTriangulationRealization -/

/- BEGIN ClassificationOfSurfaces.P2DegenerateDisk | e708766a8a50023cf9dc49d36dae0ec4ff2bee4126faf16d8aa67f168f8424b8 -/
section schottkyclassification21_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The one-sided-degenerate P2 disk model

The ordinary P2 model glues two polygons along a marked side, with at least one old side on
each child.  Cancellation in the Gallier--Xu normalization also uses the limiting case in which
one child is a monogon.  This file supplies a concrete model for that case.

The local target is a polynomial teardrop.  The map

`z ↦ (1 - z) ^ 2`

is injective on the closed unit disk: translating by `1` puts the disk in a closed half-plane,
on which squaring has no nontrivial antipodal pair.  Its image is star-shaped at the cusp.  A
scaled copy receives the monogon, while the other child fills the collar between that copy and
the full teardrop.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace P2DegenerateDisk

/-- Every polygon cell has the closed-unit-disk norm bound. -/
theorem norm_le_one {n : ℕ} (z : PolygonCell n) :
    ‖z.val‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using z.property

/-- The polynomial disk used as the target of the degenerate two-child gluing. -/
def teardropMap {n : ℕ} (z : PolygonCell n) : ℂ :=
  (1 - z.val) ^ 2

theorem continuous_teardropMap {n : ℕ} :
    Continuous (teardropMap : PolygonCell n → ℂ) := by
  unfold teardropMap
  fun_prop

/-- A point of the closed unit disk with real part `1` is the cusp point `1`. -/
theorem eq_one_of_re_eq_one {n : ℕ} (z : PolygonCell n)
    (hre : z.val.re = 1) :
    z.val = 1 := by
  have hnorm : Complex.normSq z.val ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  apply Complex.ext
  · simpa using hre
  · simp only [Complex.one_im]
    rw [Complex.normSq_apply] at hnorm
    nlinarith

/-- Squaring after translation by `1` is injective on the closed unit disk. -/
theorem teardropMap_injective {n m : ℕ}
    {z : PolygonCell n} {w : PolygonCell m}
    (h : teardropMap z = teardropMap w) :
    z.val = w.val := by
  let u : ℂ := 1 - z.val
  let v : ℂ := 1 - w.val
  have hprod : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
      _ = 0 := by
        dsimp [u, v, teardropMap] at h ⊢
        rw [h]
        ring
  rcases mul_eq_zero.mp hprod with huv | huv
  · dsimp [u, v] at huv
    linear_combination -huv
  · have hsum : z.val + w.val = 2 := by
      dsimp [u, v] at huv
      calc
        z.val + w.val =
            2 - ((1 - z.val) + (1 - w.val)) := by ring
        _ = 2 := by rw [huv, sub_zero]
    have hzre : z.val.re ≤ 1 :=
      (Complex.re_le_norm z.val).trans (norm_le_one z)
    have hwre : w.val.re ≤ 1 :=
      (Complex.re_le_norm w.val).trans (norm_le_one w)
    have hsumre := congrArg Complex.re hsum
    change z.val.re + w.val.re = 2 at hsumre
    have hzre_eq : z.val.re = 1 := by linarith
    have hwre_eq : w.val.re = 1 := by linarith
    rw [eq_one_of_re_eq_one z hzre_eq,
      eq_one_of_re_eq_one w hwre_eq]

/-- The teardrop image, equipped with the subspace topology inherited from the plane. -/
abbrev Teardrop :=
  Set.range (teardropMap : PolygonCell 1 → ℂ)

/-- The polynomial map as a map into its exact range. -/
def toTeardrop (z : PolygonCell 1) : Teardrop :=
  ⟨teardropMap z, ⟨z, rfl⟩⟩

theorem continuous_toTeardrop :
    Continuous toTeardrop := by
  exact continuous_induced_rng.2 continuous_teardropMap

theorem toTeardrop_bijective :
    Function.Bijective toTeardrop := by
  constructor
  · intro z w h
    apply PolygonCell.ext
    exact teardropMap_injective (congrArg Subtype.val h)
  · rintro ⟨x, z, rfl⟩
    exact ⟨z, rfl⟩

/-- The closed disk is homeomorphic to its polynomial teardrop image. -/
noncomputable def teardropHomeomorph :
    PolygonCell 1 ≃ₜ Teardrop :=
  IsHomeomorph.homeomorph toTeardrop
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_toTeardrop, toTeardrop_bijective⟩)

@[simp]
theorem teardropHomeomorph_apply_val (z : PolygonCell 1) :
    (teardropHomeomorph z).val = teardropMap z :=
  by
    simp [teardropHomeomorph, toTeardrop]

/-- Contracting the translated disk toward its cusp stays in the translated disk. -/
theorem one_sub_smul_mem_closedBall
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(1 : ℂ) - s * (1 - z.val)‖ ≤ 1 := by
  have hconvex :
      (1 : ℂ) - s * (1 - z.val) =
        (1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val := by
    ring
  rw [hconvex]
  calc
    ‖(1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val‖ ≤
        ‖(1 - (s : ℂ)) * (1 : ℂ)‖ +
          ‖(s : ℂ) * z.val‖ :=
      norm_add_le _ _
    _ = (1 - s) + s * ‖z.val‖ := by
      rw [norm_mul, norm_mul, norm_one, mul_one]
      have hsub :
          (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hs1)]
    _ ≤ 1 := by
      have hz := norm_le_one z
      nlinarith

/-- Every radial contraction of a teardrop point is again a teardrop point. -/
theorem smul_teardropMap_mem_range
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s : ℂ) * teardropMap z ∈
      Set.range (teardropMap : PolygonCell 1 → ℂ) := by
  let r : ℝ := Real.sqrt s
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := by
    simpa [r] using hs1
  let w : PolygonCell 1 :=
    ⟨(1 : ℂ) - r * (1 - z.val), by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        one_sub_smul_mem_closedBall z hr0 hr1⟩
  refine ⟨w, ?_⟩
  unfold teardropMap
  dsimp [w, r]
  have hsqrt : (Real.sqrt s) ^ 2 = s :=
    Real.sq_sqrt hs0
  have hsqrtC : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast hsqrt
  rw [show (1 : ℂ) -
      ((1 : ℂ) - (Real.sqrt s : ℂ) * (1 - z.val)) =
        (Real.sqrt s : ℂ) * (1 - z.val) by ring]
  rw [mul_pow, hsqrtC]

/-! ## The monogon and collar maps -/

/-- The monogon occupies the inner radial half of the teardrop. -/
noncomputable def monogonMap (z : PolygonCell 1) : ℂ :=
  (((2 : ℝ)⁻¹ : ℝ) : ℂ) * teardropMap z

theorem continuous_monogonMap :
    Continuous monogonMap := by
  unfold monogonMap
  exact continuous_const.mul continuous_teardropMap

/-- Half of a teardrop point is still in the full teardrop. -/
theorem monogonMap_mem_teardrop (z : PolygonCell 1) :
    monogonMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  unfold monogonMap
  exact smul_teardropMap_mem_range
    (s := (2 : ℝ)⁻¹) z (by norm_num) (by norm_num)

/-- The nonnegative height of the upper circular boundary above a fixed real coordinate. -/
noncomputable def chordHeight (z : PolygonCell 2) : ℝ :=
  Real.sqrt (1 - z.val.re ^ 2)

theorem re_sq_le_one (z : PolygonCell 2) :
    z.val.re ^ 2 ≤ 1 := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  nlinarith [sq_nonneg z.val.im]

theorem chordHeight_nonneg (z : PolygonCell 2) :
    0 ≤ chordHeight z :=
  Real.sqrt_nonneg _

theorem chordHeight_sq (z : PolygonCell 2) :
    chordHeight z ^ 2 = 1 - z.val.re ^ 2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr (re_sq_le_one z))

theorem neg_chordHeight_le_im (z : PolygonCell 2) :
    -chordHeight z ≤ z.val.im := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im + chordHeight z)]

theorem im_le_chordHeight (z : PolygonCell 2) :
    z.val.im ≤ chordHeight z := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im - chordHeight z)]

/-- The lower unit-circle point on the vertical chord through a digon point, squared so that the
two chord endpoints sweep the teardrop boundary once. -/
noncomputable def collarCircleValue (z : PolygonCell 2) : ℂ :=
  ((z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I) ^ 2

theorem collarCircleValue_norm (z : PolygonCell 2) :
    ‖collarCircleValue z‖ = 1 := by
  let a : ℂ :=
    (z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I
  have haSq : Complex.normSq a = 1 := by
    rw [Complex.normSq_apply]
    simp only [a, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, sub_zero, Complex.sub_im,
      Complex.mul_im, Complex.I_im, mul_one, add_zero,
      zero_sub]
    nlinarith [chordHeight_sq z]
  have haNorm : ‖a‖ = 1 := by
    have hnorm0 := norm_nonneg a
    rw [Complex.normSq_eq_norm_sq] at haSq
    nlinarith
  change ‖a ^ 2‖ = 1
  rw [norm_pow, haNorm]
  norm_num

/-- The collar's boundary-direction point, bundled as a point of the unit disk. -/
noncomputable def collarCirclePoint (z : PolygonCell 2) :
    PolygonCell 1 :=
  ⟨collarCircleValue z, by
    simp [Metric.mem_closedBall, dist_zero_right,
      collarCircleValue_norm z]⟩

theorem continuous_chordHeight :
    Continuous chordHeight := by
  unfold chordHeight
  fun_prop

theorem continuous_collarCircleValue :
    Continuous collarCircleValue := by
  unfold collarCircleValue
  apply Continuous.pow
  apply Continuous.sub
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp PolygonCell.continuous_val)
  · exact
      (Complex.continuous_ofReal.comp continuous_chordHeight).mul
        continuous_const

theorem continuous_collarCirclePoint :
    Continuous collarCirclePoint :=
  continuous_induced_rng.2 continuous_collarCircleValue

/-- The teardrop boundary value of the collar direction has an exact quadratic factor. -/
theorem teardropMap_collarCirclePoint
    (z : PolygonCell 2) :
    teardropMap (collarCirclePoint z) =
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 *
        collarCircleValue z := by
  let x : ℝ := z.val.re
  let s : ℝ := chordHeight z
  let a : ℂ := (x : ℂ) - (s : ℂ) * Complex.I
  have hcircleR : x ^ 2 + s ^ 2 = 1 := by
    dsimp [x, s]
    nlinarith [chordHeight_sq z]
  have hcircleC : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    exact_mod_cast hcircleR
  have hone : (1 : ℂ) - a ^ 2 =
      2 * Complex.I * (s : ℂ) * a := by
    apply Complex.ext
    · simp [a, pow_two]
      nlinarith [hcircleR]
    · simp [a, pow_two]
      ring
  have hI : (2 * Complex.I : ℂ) ^ 2 = -4 := by
    calc
      (2 * Complex.I : ℂ) ^ 2 =
          4 * (Complex.I * Complex.I) := by ring
      _ = -4 := by rw [Complex.I_mul_I]; ring
  change (1 - a ^ 2) ^ 2 =
    (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2
  rw [hone]
  calc
    (2 * Complex.I * (s : ℂ) * a) ^ 2 =
        (2 * Complex.I) ^ 2 * (s : ℂ) ^ 2 * a ^ 2 := by ring
    _ = (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2 := by rw [hI]

/-- The digon fills the radial collar between the half-size and full teardrop boundaries. -/
noncomputable def collarMap (z : PolygonCell 2) : ℂ :=
  let s := chordHeight z
  collarCircleValue z *
    ((s * z.val.im - 3 * s ^ 2 : ℝ) : ℂ)

theorem continuous_collarMap :
    Continuous collarMap := by
  unfold collarMap
  apply continuous_collarCircleValue.mul
  apply Complex.continuous_ofReal.comp
  exact
    (continuous_chordHeight.mul
      (Complex.continuous_im.comp PolygonCell.continuous_val)).sub
        (continuous_const.mul (continuous_chordHeight.pow 2))

/-- Away from the two chord tips, the collar map is a radial teardrop value with scale in
`[1/2, 1]`. -/
theorem collarMap_eq_smul_teardropMap
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    collarMap z =
      (((3 * chordHeight z ^ 2 -
          chordHeight z * z.val.im) /
            (4 * chordHeight z ^ 2) : ℝ) : ℂ) *
        teardropMap (collarCirclePoint z) := by
  let s : ℝ := chordHeight z
  let y : ℝ := z.val.im
  have hscalar :
      s * y - 3 * s ^ 2 =
        ((3 * s ^ 2 - s * y) / (4 * s ^ 2)) *
          (-4) * s ^ 2 := by
    have hs' : s ≠ 0 := by simpa [s] using hs
    field_simp [hs']
    ring
  have hscalarC :
      ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
        (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
          (-4 : ℂ) * (s : ℂ) ^ 2 := by
    exact_mod_cast hscalar
  rw [teardropMap_collarCirclePoint]
  unfold collarMap
  change
    collarCircleValue z *
        ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
      (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
        ((-4 : ℂ) * (s : ℂ) ^ 2 * collarCircleValue z)
  rw [hscalarC]
  ring

theorem collarScale_nonneg
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    0 ≤ (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := im_le_chordHeight z
  apply div_nonneg
  · nlinarith
  · positivity

theorem collarScale_le_one
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) ≤ 1 := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := neg_chordHeight_le_im z
  rw [div_le_one (by positivity)]
  nlinarith

theorem collarMap_mem_teardrop (z : PolygonCell 2) :
    collarMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  by_cases hs : chordHeight z = 0
  · refine ⟨⟨1, by simp [Metric.mem_closedBall]⟩, ?_⟩
    simp [collarMap, hs, teardropMap]
  · rw [collarMap_eq_smul_teardropMap z hs]
    exact smul_teardropMap_mem_range
      (collarCirclePoint z)
      (collarScale_nonneg z hs)
      (collarScale_le_one z hs)

/-! ## Exact compatibility on the fresh seam -/

/-- On the upper circular boundary of the digon, the collar meets the half-size teardrop
occupied by the monogon. -/
theorem collarMap_eq_monogonMap_collarCirclePoint_of_im_eq
    (z : PolygonCell 2) (hy : z.val.im = chordHeight z) :
    collarMap z = monogonMap (collarCirclePoint z) := by
  unfold collarMap monogonMap
  rw [teardropMap_collarCirclePoint]
  rw [hy]
  norm_num
  ring

/-- Side zero of the digon is the upper semicircle with its usual angle parameter. -/
theorem side_zero_digon_val (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ) := by
  change
    (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 2) t) : ℂ) =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ)
  congr 2
  unfold PolygonCell.sideAngle
  norm_num
  ring

/-- The imaginary coordinate on side zero of the digon. -/
theorem side_zero_digon_im (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val.im =
      Real.sin (Real.pi * (t : ℝ)) := by
  rw [side_zero_digon_val]
  exact Complex.exp_ofReal_mul_I_im _

/-- The chord height agrees with the imaginary coordinate on the upper digon side. -/
theorem chordHeight_side_zero_digon (t : unitInterval) :
    chordHeight (PolygonCell.side (0 : Fin 2) t) =
      Real.sin (Real.pi * (t : ℝ)) := by
  let z : PolygonCell 2 := PolygonCell.side (0 : Fin 2) t
  let θ : ℝ := Real.pi * (t : ℝ)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le t.property.1
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos, t.property.2]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hre : z.val.re = Real.cos θ := by
    dsimp [z, θ]
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have him : z.val.im = Real.sin θ := by
    simpa [z, θ] using side_zero_digon_im t
  have hs := chordHeight_sq z
  have htrig := Real.sin_sq_add_cos_sq θ
  rw [hre] at hs
  have hheight0 := chordHeight_nonneg z
  change chordHeight z = Real.sin θ
  nlinarith

/-- Squaring the lower endpoint of an upper digon chord gives the corresponding monogon
boundary point. -/
theorem collarCirclePoint_side_zero_digon_symm (t : unitInterval) :
    collarCirclePoint
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) =
      PolygonCell.side (0 : Fin 1) t := by
  apply PolygonCell.ext
  let u : unitInterval := unitInterval.symm t
  let θ : ℝ := Real.pi * (u : ℝ)
  have hheight :
      chordHeight (PolygonCell.side (0 : Fin 2) u) =
        Real.sin θ := by
    simpa [θ] using chordHeight_side_zero_digon u
  have hre :
      (PolygonCell.side (0 : Fin 2) u : PolygonCell 2).val.re =
        Real.cos θ := by
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have ha :
      ((Real.cos θ : ℂ) -
          (Real.sin θ : ℂ) * Complex.I) =
        (Circle.exp (-θ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul,
        mul_one, add_zero, zero_sub, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  change collarCircleValue
      (PolygonCell.side (0 : Fin 2) u) =
    (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val
  unfold collarCircleValue
  rw [hheight, hre, ha]
  change ((Circle.exp (-θ) : ℂ) ^ 2) =
    (Circle.exp (PolygonCell.sideAngle (0 : Fin 1) t) : ℂ)
  rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  dsimp [θ, u]
  simp only [PolygonCell.sideAngle, Fin.val_zero, Nat.cast_one,
    div_one, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul]
  ring

/-- The analytic child map respects the exact reversed fresh-side parameter used by P2. -/
theorem monogonMap_fresh_seam (t : unitInterval) :
    monogonMap (PolygonCell.side (0 : Fin 1) t) =
      collarMap
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) := by
  symm
  rw [collarMap_eq_monogonMap_collarCirclePoint_of_im_eq,
    collarCirclePoint_side_zero_digon_symm]
  rw [side_zero_digon_im]
  exact (chordHeight_side_zero_digon (unitInterval.symm t)).symm

/-! ## Descending the base child pair to the teardrop -/

/-- The base one-sided-degenerate child pair: a monogon and a digon. -/
abbrev BaseChildPair :=
  DiskSquare.ChildPair 0 1

/-- Map both children into their complementary regions of the teardrop. -/
noncomputable def baseChildPairMap : BaseChildPair → Teardrop
  | .inl z => ⟨monogonMap z, monogonMap_mem_teardrop z⟩
  | .inr z => ⟨collarMap z, collarMap_mem_teardrop z⟩

theorem continuous_baseChildPairMap :
    Continuous baseChildPairMap := by
  apply continuous_induced_rng.2
  convert continuous_monogonMap.sumElim continuous_collarMap using 1
  funext x
  cases x <;> rfl

@[simp]
theorem baseChildPairMap_inl (z : PolygonCell 1) :
    (baseChildPairMap (.inl z)).val = monogonMap z :=
  rfl

@[simp]
theorem baseChildPairMap_inr (z : PolygonCell 2) :
    (baseChildPairMap (.inr z)).val = collarMap z :=
  rfl

/-- The child-pair map is constant on the generating fresh seam. -/
theorem baseChildPairMap_eq_of_generator
    {x y : BaseChildPair}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 1 x y) :
    baseChildPairMap x = baseChildPairMap y := by
  cases hxy with
  | glue t =>
      apply Subtype.ext
      exact monogonMap_fresh_seam t

/-- The child-pair map is constant on the equivalence relation generated by the fresh seam. -/
theorem baseChildPairMap_respects
    {x y : BaseChildPair}
    (hxy :
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1) x y) :
    baseChildPairMap x = baseChildPairMap y := by
  induction hxy with
  | rel _ _ h => exact baseChildPairMap_eq_of_generator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The continuous analytic map induced on the one-sided-degenerate child quotient. -/
noncomputable def baseChildGluingMap :
    C(DiskSquare.ParamChildGluing 0 1, Teardrop) where
  toFun :=
    Quotient.lift baseChildPairMap fun _ _ hxy ↦
      baseChildPairMap_respects hxy
  continuous_toFun :=
    continuous_baseChildPairMap.quotient_lift fun _ _ hxy ↦
      baseChildPairMap_respects hxy

@[simp]
theorem baseChildGluingMap_mk (x : BaseChildPair) :
    baseChildGluingMap
        (@Quotient.mk'' BaseChildPair
          (DiskSquare.paramChildSeamSetoid 0 1) x) =
      baseChildPairMap x :=
  rfl

/-! ## The collar has no hidden interior identifications -/

/-- The nonnegative radial magnitude used by the collar map. -/
noncomputable def collarRadius (z : PolygonCell 2) : ℝ :=
  3 * chordHeight z ^ 2 - chordHeight z * z.val.im

theorem two_mul_chordHeight_sq_le_collarRadius
    (z : PolygonCell 2) :
    2 * chordHeight z ^ 2 ≤ collarRadius z := by
  have hs0 := chordHeight_nonneg z
  have hy := im_le_chordHeight z
  unfold collarRadius
  nlinarith

theorem collarRadius_nonneg (z : PolygonCell 2) :
    0 ≤ collarRadius z :=
  (mul_nonneg (by norm_num) (sq_nonneg _)).trans
    (two_mul_chordHeight_sq_le_collarRadius z)

theorem collarRadius_pos (z : PolygonCell 2)
    (hs : chordHeight z ≠ 0) :
    0 < collarRadius z := by
  have hsSq : 0 < chordHeight z ^ 2 :=
    sq_pos_of_ne_zero hs
  exact (mul_pos (by norm_num) hsSq).trans_le
    (two_mul_chordHeight_sq_le_collarRadius z)

theorem collarMap_eq_neg_radius_mul (z : PolygonCell 2) :
    collarMap z =
      (-(collarRadius z) : ℂ) * collarCircleValue z := by
  unfold collarMap collarRadius
  push_cast
  ring

theorem norm_collarMap (z : PolygonCell 2) :
    ‖collarMap z‖ = collarRadius z := by
  rw [collarMap_eq_neg_radius_mul, norm_mul,
    collarCircleValue_norm]
  rw [mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (collarRadius_nonneg z)]

/-- Equal non-tip collar values have the same boundary direction. -/
theorem collarCircleValue_eq_of_collarMap_eq
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarMap z = collarMap w) :
    collarCircleValue z = collarCircleValue w := by
  have hradius :
      collarRadius z = collarRadius w := by
    rw [← norm_collarMap z, ← norm_collarMap w, hzw]
  have hradius_ne : collarRadius z ≠ 0 :=
    (collarRadius_pos z hz).ne'
  have hradius_ne_w : collarRadius w ≠ 0 := by
    rwa [← hradius]
  rw [collarMap_eq_neg_radius_mul,
    collarMap_eq_neg_radius_mul, hradius] at hzw
  exact mul_left_cancel₀
    (show (-(collarRadius w) : ℂ) ≠ 0 by
      exact_mod_cast neg_ne_zero.mpr hradius_ne_w)
    hzw

/-- The lower unit-circle representatives used by the squaring map. -/
noncomputable def lowerChordValue (z : PolygonCell 2) : ℂ :=
  (z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I

theorem collarCircleValue_eq_lowerChordValue_sq
    (z : PolygonCell 2) :
    collarCircleValue z = lowerChordValue z ^ 2 :=
  rfl

theorem lowerChordValue_im (z : PolygonCell 2) :
    (lowerChordValue z).im = -chordHeight z := by
  simp [lowerChordValue]

theorem lowerChordValue_re (z : PolygonCell 2) :
    (lowerChordValue z).re = z.val.re := by
  simp [lowerChordValue]

/-- Squaring is injective on the open lower semicircle used by non-tip collar chords. -/
theorem lowerChordValue_eq_of_collarCircleValue_eq
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarCircleValue z = collarCircleValue w) :
    lowerChordValue z = lowerChordValue w := by
  rw [collarCircleValue_eq_lowerChordValue_sq,
    collarCircleValue_eq_lowerChordValue_sq] at hzw
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hzw with heq | hneg
  · exact heq
  · exfalso
    have him := congrArg Complex.im hneg
    rw [lowerChordValue_im, Complex.neg_im,
      lowerChordValue_im] at him
    have hzpos : 0 < chordHeight z :=
      (chordHeight_nonneg z).lt_of_ne' hz
    have hw0 := chordHeight_nonneg w
    linarith

/-- The collar is injective away from its two pinched tips. -/
theorem collarMap_injective_of_chordHeight_ne_zero
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarMap z = collarMap w) :
    z = w := by
  have hcircle :=
    collarCircleValue_eq_of_collarMap_eq z w hz hzw
  have hlower :=
    lowerChordValue_eq_of_collarCircleValue_eq z w hz hcircle
  have hre : z.val.re = w.val.re := by
    simpa only [lowerChordValue_re] using
      congrArg Complex.re hlower
  have hs : chordHeight z = chordHeight w := by
    have him := congrArg Complex.im hlower
    rw [lowerChordValue_im, lowerChordValue_im] at him
    linarith
  have hradius :
      collarRadius z = collarRadius w := by
    rw [← norm_collarMap z, ← norm_collarMap w, hzw]
  have him : z.val.im = w.val.im := by
    have hzpos : 0 < chordHeight z :=
      (chordHeight_nonneg z).lt_of_ne' hz
    unfold collarRadius at hradius
    rw [hs] at hradius
    nlinarith
  apply PolygonCell.ext
  exact Complex.ext hre him

theorem chordHeight_eq_zero_of_collarRadius_eq_zero
    (z : PolygonCell 2) (hradius : collarRadius z = 0) :
    chordHeight z = 0 := by
  have hle := two_mul_chordHeight_sq_le_collarRadius z
  rw [hradius] at hle
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (chordHeight z)]

/-- The only zero-height digon points are the two endpoints of its upper side. -/
theorem eq_side_zero_or_side_one_of_chordHeight_eq_zero
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    z = PolygonCell.side (0 : Fin 2) 0 ∨
      z = PolygonCell.side (0 : Fin 2) 1 := by
  have hsSq := chordHeight_sq z
  rw [hs] at hsSq
  have hreSq : z.val.re ^ 2 = 1 := by
    nlinarith
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have him : z.val.im = 0 := by
    nlinarith [sq_nonneg z.val.im]
  rcases sq_eq_one_iff.mp hreSq with hre | hre
  · left
    apply PolygonCell.ext
    rw [side_zero_digon_val]
    apply Complex.ext
    · simpa using hre
    · simpa using him
  · right
    apply PolygonCell.ext
    rw [side_zero_digon_val]
    apply Complex.ext
    · simpa [Circle.coe_exp] using hre
    · simpa [Circle.coe_exp] using him

/-- Either collar tip is identified with the monogon basepoint by the generated seam relation. -/
theorem inr_tip_eqv_inl_monogon_basepoint
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inr z : BaseChildPair)
        (.inl (PolygonCell.side (0 : Fin 1) 0)) := by
  rcases eq_side_zero_or_side_one_of_chordHeight_eq_zero z hs with hz | hz
  · subst z
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (1 : unitInterval))
    exact Relation.EqvGen.symm _ _ (by
      simpa [PolygonCell.side_zero_eq_side_one_monogon] using hgen)
  · subst z
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (0 : unitInterval))
    exact Relation.EqvGen.symm _ _ (by simpa using hgen)

/-- Equality inside the collar is exactly equality modulo the two endpoint seam identifications. -/
theorem baseChildPair_eqvGen_inr_inr_of_map_eq
    (z w : PolygonCell 2) (hzw : collarMap z = collarMap w) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inr z : BaseChildPair) (.inr w) := by
  by_cases hz : chordHeight z = 0
  · have hzmap : collarMap z = 0 := by
      simp [collarMap, hz]
    have hwmap : collarMap w = 0 := hzmap ▸ hzw.symm
    have hradius : collarRadius w = 0 := by
      rw [← norm_collarMap w, hwmap, norm_zero]
    have hw := chordHeight_eq_zero_of_collarRadius_eq_zero w hradius
    exact Relation.EqvGen.trans _ _ _
      (inr_tip_eqv_inl_monogon_basepoint z hz)
      (Relation.EqvGen.symm _ _
        (inr_tip_eqv_inl_monogon_basepoint w hw))
  · have heq :=
      collarMap_injective_of_chordHeight_ne_zero z w hz hzw
    subst w
    exact Relation.EqvGen.refl _

/-- Every point on the upper circular boundary of the digon has a side-zero parameter. -/
theorem exists_side_zero_digon_eq_of_im_eq_chordHeight
    (z : PolygonCell 2) (hy : z.val.im = chordHeight z) :
    ∃ t : unitInterval, PolygonCell.side (0 : Fin 2) t = z := by
  have hcircleSq :
      z.val.re ^ 2 + z.val.im ^ 2 = 1 := by
    rw [hy, chordHeight_sq]
    ring
  have hnorm : ‖z.val‖ = 1 := by
    have hnormSq : ‖z.val‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      simpa [pow_two] using hcircleSq
    nlinarith [norm_nonneg z.val]
  let q : Circle :=
    ⟨z.val, mem_sphere_zero_iff_norm.mpr hnorm⟩
  have harg0 : 0 ≤ q.val.arg := by
    rw [Complex.arg_nonneg_iff]
    exact hy.trans_ge (chordHeight_nonneg z)
  have hargPi : q.val.arg ≤ Real.pi :=
    Complex.arg_le_pi _
  let t : unitInterval :=
    ⟨q.val.arg / Real.pi,
      div_nonneg harg0 Real.pi_pos.le,
      (div_le_one Real.pi_pos).2 hargPi⟩
  refine ⟨t, ?_⟩
  apply PolygonCell.ext
  rw [side_zero_digon_val]
  have hangle :
      Real.pi * (t : ℝ) = q.val.arg := by
    dsimp [t]
    field_simp [Real.pi_ne_zero]
  rw [hangle]
  exact congrArg Subtype.val (Circle.exp_arg q)

/-- A disk point cannot lie radially beyond a non-cusp boundary point of the teardrop. -/
theorem teardrop_radial_scale_le_one
    (z q : PolygonCell 1) (hqnorm : ‖q.val‖ = 1)
    (hqcusp : q.val ≠ 1) {μ : ℝ} (hμ : 1 ≤ μ)
    (hscale :
      teardropMap z = (μ : ℂ) * teardropMap q) :
    μ ≤ 1 := by
  let u : ℂ := 1 - z.val
  let v : ℂ := 1 - q.val
  let r : ℝ := Real.sqrt μ
  have hμ0 : 0 ≤ μ := le_trans (by norm_num) hμ
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = μ := by
    exact Real.sq_sqrt hμ0
  have hr1 : 1 ≤ r := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hμ
  have hsq :
      u ^ 2 = ((r : ℂ) * v) ^ 2 := by
    dsimp [u, v, r, teardropMap] at hscale ⊢
    rw [mul_pow]
    have hrSqC : (Real.sqrt μ : ℂ) ^ 2 = (μ : ℂ) := by
      exact_mod_cast hrSq
    rw [hrSqC]
    exact hscale
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hplus | hminus
  · have hzval :
        z.val = 1 - (r : ℂ) * (1 - q.val) := by
      dsimp [u, v] at hplus
      linear_combination -hplus
    have hqre : q.val.re < 1 := by
      have hle :
          q.val.re ≤ 1 :=
        (Complex.re_le_norm q.val).trans_eq hqnorm
      exact lt_of_le_of_ne hle fun heq ↦
        hqcusp (eq_one_of_re_eq_one q heq)
    have hqSq : q.val.re ^ 2 + q.val.im ^ 2 = 1 := by
      have h := congrArg (fun x : ℝ ↦ x ^ 2) hqnorm
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply] at h
      simpa [pow_two] using h
    have hformula :
        Complex.normSq
            (1 - (r : ℂ) * (1 - q.val)) =
          1 + 2 * r * (r - 1) * (1 - q.val.re) := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re,
        Complex.re_ofReal_mul, Complex.sub_im,
        Complex.one_im, Complex.im_ofReal_mul, zero_sub]
      linear_combination r ^ 2 * hqSq
    have hnormz : Complex.normSq z.val ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_le_one z, norm_nonneg z.val]
    rw [hzval, hformula] at hnormz
    have hrle : r ≤ 1 := by
      by_contra hr
      have hrlt : 1 < r := lt_of_not_ge hr
      have hprod :
          0 < 2 * r * (r - 1) * (1 - q.val.re) := by
        positivity
      linarith
    nlinarith [hrSq]
  · have hzval :
        z.val = 1 + (r : ℂ) * (1 - q.val) := by
      dsimp [u, v] at hminus
      linear_combination -hminus
    have hqre : q.val.re < 1 := by
      have hle :
          q.val.re ≤ 1 :=
        (Complex.re_le_norm q.val).trans_eq hqnorm
      exact lt_of_le_of_ne hle fun heq ↦
        hqcusp (eq_one_of_re_eq_one q heq)
    have hqSq : q.val.re ^ 2 + q.val.im ^ 2 = 1 := by
      have h := congrArg (fun x : ℝ ↦ x ^ 2) hqnorm
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply] at h
      simpa [pow_two] using h
    have hformula :
        Complex.normSq
            (1 + (r : ℂ) * (1 - q.val)) =
          1 + 2 * r * (r + 1) * (1 - q.val.re) := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re,
        Complex.re_ofReal_mul, Complex.sub_re,
        Complex.add_im, Complex.one_im,
        Complex.im_ofReal_mul, Complex.sub_im, zero_sub]
      linear_combination r ^ 2 * hqSq
    have hnormz : Complex.normSq z.val ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_le_one z, norm_nonneg z.val]
    rw [hzval, hformula] at hnormz
    have hprod :
        0 < 2 * r * (r + 1) * (1 - q.val.re) := by
      have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
      positivity
    linarith

theorem collarScale_half_le
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (2 : ℝ)⁻¹ ≤
      (3 * chordHeight z ^ 2 -
          chordHeight z * z.val.im) /
        (4 * chordHeight z ^ 2) := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := im_le_chordHeight z
  rw [le_div_iff₀ (by positivity)]
  norm_num
  nlinarith

theorem norm_collarCirclePoint (z : PolygonCell 2) :
    ‖(collarCirclePoint z).val‖ = 1 :=
  collarCircleValue_norm z

theorem collarCirclePoint_ne_cusp
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (collarCirclePoint z).val ≠ 1 := by
  intro hcusp
  have htd := teardropMap_collarCirclePoint z
  have hleftzero :
      teardropMap (collarCirclePoint z) = 0 := by
    unfold teardropMap
    rw [hcusp]
    ring
  have hzero' :
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 *
          collarCircleValue z = 0 :=
    htd.symm.trans hleftzero
  have hzero :
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 = 0 := by
    rw [show collarCircleValue z = 1 from hcusp,
      mul_one] at hzero'
    exact hzero'
  rcases mul_eq_zero.mp hzero with hfour | hsSq
  · norm_num at hfour
  · exact hs (by
      exact_mod_cast (sq_eq_zero_iff.mp hsSq))

/-- The half-size teardrop map reaches the cusp only at the monogon basepoint. -/
theorem eq_monogon_basepoint_of_monogonMap_eq_zero
    (z : PolygonCell 1) (hz : monogonMap z = 0) :
    z = PolygonCell.side (0 : Fin 1) 0 := by
  have htd : teardropMap z = 0 := by
    unfold monogonMap at hz
    have hhalf :
        ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hz).resolve_left hhalf
  apply PolygonCell.ext
  apply teardropMap_injective
  rw [htd]
  change 0 =
    (1 -
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 1) 0) : ℂ)) ^ 2
  simp [PolygonCell.sideAngle]

/-- A monogon point and a collar point have the same image exactly along the declared seam. -/
theorem baseChildPair_eqvGen_inl_inr_of_map_eq
    (z : PolygonCell 1) (w : PolygonCell 2)
    (hzw : monogonMap z = collarMap w) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inl z : BaseChildPair) (.inr w) := by
  by_cases hs : chordHeight w = 0
  · have hwmap : collarMap w = 0 := by
      simp [collarMap, hs]
    have hzmap : monogonMap z = 0 := hzw.trans hwmap
    have hz := eq_monogon_basepoint_of_monogonMap_eq_zero z hzmap
    subst z
    exact Relation.EqvGen.symm _ _
      (inr_tip_eqv_inl_monogon_basepoint w hs)
  · let scale : ℝ :=
      (3 * chordHeight w ^ 2 -
          chordHeight w * w.val.im) /
        (4 * chordHeight w ^ 2)
    have hcollar :
        collarMap w =
          (scale : ℂ) * teardropMap (collarCirclePoint w) := by
      simpa [scale] using collarMap_eq_smul_teardropMap w hs
    have hscale :
        teardropMap z =
          ((2 * scale : ℝ) : ℂ) *
            teardropMap (collarCirclePoint w) := by
      unfold monogonMap at hzw
      rw [hcollar] at hzw
      calc
        teardropMap z =
            (2 : ℂ) *
              (((((2 : ℝ)⁻¹ : ℝ) : ℂ)) *
                teardropMap z) := by
                  norm_num
                  ring
        _ = (2 : ℂ) *
              ((scale : ℂ) *
                teardropMap (collarCirclePoint w)) := by
              rw [hzw]
        _ = ((2 * scale : ℝ) : ℂ) *
              teardropMap (collarCirclePoint w) := by
              push_cast
              ring
    have hμone :
        2 * scale ≤ 1 :=
      teardrop_radial_scale_le_one z (collarCirclePoint w)
        (norm_collarCirclePoint w)
        (collarCirclePoint_ne_cusp w hs)
        (by
          dsimp [scale]
          nlinarith [collarScale_half_le w hs])
        hscale
    have hscaleHalf : scale = (2 : ℝ)⁻¹ := by
      have hhalf := collarScale_half_le w hs
      dsimp [scale] at hhalf ⊢
      nlinarith
    have hy : w.val.im = chordHeight w := by
      have hden : 4 * chordHeight w ^ 2 ≠ 0 := by
        positivity
      dsimp [scale] at hscaleHalf
      rw [div_eq_iff hden] at hscaleHalf
      norm_num at hscaleHalf
      have hspos : 0 < chordHeight w :=
        (chordHeight_nonneg w).lt_of_ne' hs
      nlinarith
    have htd :
        teardropMap z =
          teardropMap (collarCirclePoint w) := by
      have hμeq : 2 * scale = 1 := by
        rw [hscaleHalf]
        norm_num
      simpa [hμeq] using hscale
    have hzcircle : z = collarCirclePoint w := by
      apply PolygonCell.ext
      exact teardropMap_injective htd
    obtain ⟨u, hu⟩ :=
      exists_side_zero_digon_eq_of_im_eq_chordHeight w hy
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (unitInterval.symm u))
    rw [← hu] at hzcircle ⊢
    have hc :=
      collarCirclePoint_side_zero_digon_symm
        (unitInterval.symm u)
    simp only [unitInterval.symm_symm] at hc hgen
    rw [hzcircle, hc]
    exact hgen

theorem monogonMap_injective :
    Function.Injective monogonMap := by
  intro z w hzw
  unfold monogonMap at hzw
  have hhalf :
      ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 0 := by norm_num
  have htd :
      teardropMap z = teardropMap w :=
    mul_left_cancel₀ hhalf hzw
  apply PolygonCell.ext
  exact teardropMap_injective htd

/-- Equality under the analytic child-pair map is exactly the generated seam relation. -/
theorem baseChildPairMap_eqvGen_of_eq
    {x y : BaseChildPair}
    (hxy : baseChildPairMap x = baseChildPairMap y) :
    Relation.EqvGen
      (DiskSquare.ParamChildSeamGenerator 0 1) x y := by
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          have hzw : monogonMap z = monogonMap w :=
            congrArg Subtype.val hxy
          have heq := monogonMap_injective hzw
          subst w
          exact Relation.EqvGen.refl _
      | inr w =>
          exact baseChildPair_eqvGen_inl_inr_of_map_eq z w
            (congrArg Subtype.val hxy)
  | inr z =>
      cases y with
      | inl w =>
          exact Relation.EqvGen.symm _ _
            (baseChildPair_eqvGen_inl_inr_of_map_eq w z
              (congrArg Subtype.val hxy).symm)
      | inr w =>
          exact baseChildPair_eqvGen_inr_inr_of_map_eq z w
            (congrArg Subtype.val hxy)

theorem baseChildGluingMap_injective :
    Function.Injective baseChildGluingMap := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
          apply Quotient.sound
          apply baseChildPairMap_eqvGen_of_eq
          simpa only [baseChildGluingMap_mk] using hqr

/-! ## Surjectivity onto the teardrop -/

theorem collarCirclePoint_eq_cusp_of_chordHeight_eq_zero
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    (collarCirclePoint z).val = 1 := by
  change collarCircleValue z = 1
  unfold collarCircleValue
  rw [hs]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  have hsSq := chordHeight_sq z
  rw [hs] at hsSq
  exact_mod_cast (by nlinarith [hsSq] :
    z.val.re ^ 2 = (1 : ℝ))

/-- Every radial scale between one half and one is realized by a unique vertical chord in the
digon collar, for any non-cusp teardrop boundary direction. -/
theorem exists_collarMap_eq_smul_teardropMap
    (q : PolygonCell 1) (hqnorm : ‖q.val‖ = 1)
    (hqcusp : q.val ≠ 1) {a : ℝ}
    (haHalf : (2 : ℝ)⁻¹ ≤ a) (haOne : a ≤ 1) :
    ∃ w : PolygonCell 2,
      collarMap w = (a : ℂ) * teardropMap q := by
  have hqSphere :
      q.val ∈ Metric.sphere (0 : ℂ) 1 := by
    exact mem_sphere_zero_iff_norm.mpr hqnorm
  obtain ⟨i, t, hit⟩ :=
    PolygonCell.exists_side_eq_of_mem_sphere
      (n := 1) (by omega) q hqSphere
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  let upper : PolygonCell 2 :=
    PolygonCell.side (0 : Fin 2) (unitInterval.symm t)
  have hcircle :
      collarCirclePoint upper = q := by
    rw [collarCirclePoint_side_zero_digon_symm]
    exact hit
  have hheight : chordHeight upper ≠ 0 := by
    intro hs
    apply hqcusp
    rw [← hcircle]
    exact collarCirclePoint_eq_cusp_of_chordHeight_eq_zero
      upper hs
  let s : ℝ := chordHeight upper
  let y : ℝ := s * (3 - 4 * a)
  have hs0 : 0 ≤ s := chordHeight_nonneg upper
  have hspos : 0 < s := hs0.lt_of_ne' (by
    simpa [s] using hheight)
  have hfactorLower : -1 ≤ 3 - 4 * a := by
    nlinarith
  have hfactorUpper : 3 - 4 * a ≤ 1 := by
    nlinarith
  have hyBounds : -s ≤ y ∧ y ≤ s := by
    dsimp [y]
    constructor <;> nlinarith
  have hySq : y ^ 2 ≤ s ^ 2 := by
    exact sq_le_sq' hyBounds.1 hyBounds.2
  let w : PolygonCell 2 :=
    ⟨Complex.mk upper.val.re y, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hupperSq := chordHeight_sq upper
      have hnormSq :
          Complex.normSq (Complex.mk upper.val.re y) ≤ 1 := by
        rw [Complex.normSq_apply]
        change
          upper.val.re * upper.val.re + y * y ≤ 1
        nlinarith
      rw [Complex.normSq_eq_norm_sq] at hnormSq
      nlinarith [norm_nonneg (Complex.mk upper.val.re y)]⟩
  have hwHeight : chordHeight w = s := by
    have hwSq := chordHeight_sq w
    have hupperSq := chordHeight_sq upper
    have hwre : w.val.re = upper.val.re := by rfl
    rw [hwre] at hwSq
    have hw0 := chordHeight_nonneg w
    nlinarith
  have hwCircle : collarCirclePoint w = q := by
    rw [← hcircle]
    apply PolygonCell.ext
    unfold collarCirclePoint collarCircleValue
    dsimp only [w]
    rw [hwHeight]
  refine ⟨w, ?_⟩
  have hwHeightNe : chordHeight w ≠ 0 := by
    rw [hwHeight]
    exact hspos.ne'
  rw [collarMap_eq_smul_teardropMap w hwHeightNe,
    hwCircle]
  congr 2
  rw [hwHeight]
  change
    (3 * s ^ 2 - s * y) / (4 * s ^ 2) = a
  dsimp [y]
  field_simp [hspos.ne']
  ring

/-- Every non-cusp teardrop point lies on a unique radial segment from a non-cusp boundary
direction, at a scale in `(0, 1]`. -/
theorem exists_teardrop_boundary_scale
    (z : PolygonCell 1) (hz : z.val ≠ 1) :
    ∃ q : PolygonCell 1, ∃ a : ℝ,
      ‖q.val‖ = 1 ∧ q.val ≠ 1 ∧
        0 < a ∧ a ≤ 1 ∧
          teardropMap z = (a : ℂ) * teardropMap q := by
  let u : ℂ := 1 - z.val
  have hu : u ≠ 0 := by
    intro hu0
    apply hz
    dsimp [u] at hu0
    linear_combination -hu0
  have huSqPos : 0 < Complex.normSq u :=
    Complex.normSq_pos.mpr hu
  have hzNormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  have huSqLe : Complex.normSq u ≤ 2 * u.re := by
    rw [Complex.normSq_apply] at hzNormSq
    rw [Complex.normSq_apply]
    dsimp [u]
    simp only [zero_sub]
    nlinarith
  have hurePos : 0 < u.re := by
    nlinarith
  let r : ℝ := 2 * u.re / Complex.normSq u
  have hrPos : 0 < r := by
    dsimp [r]
    positivity
  have hrOne : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ huSqPos]
    simpa using huSqLe
  let qval : ℂ := 1 - (r : ℂ) * u
  have hqNormSq : Complex.normSq qval = 1 := by
    rw [Complex.normSq_apply]
    simp only [qval, Complex.sub_re, Complex.one_re,
      Complex.re_ofReal_mul, Complex.sub_im, Complex.one_im,
      Complex.im_ofReal_mul, zero_sub]
    have huApply := Complex.normSq_apply u
    dsimp [r]
    field_simp [huSqPos.ne']
    nlinarith
  have hqNorm : ‖qval‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hqNormSq
    nlinarith [norm_nonneg qval]
  let q : PolygonCell 1 :=
    ⟨qval, by
      simp [Metric.mem_closedBall, dist_zero_right,
        hqNorm]⟩
  have hqne : q.val ≠ 1 := by
    intro hq
    have hmul : (r : ℂ) * u = 0 := by
      dsimp [q, qval] at hq
      linear_combination -hq
    rcases mul_eq_zero.mp hmul with hr | hu0
    · have hrCast : (r : ℂ) ≠ 0 := by
        exact_mod_cast hrPos.ne'
      exact hrCast hr
    · exact hu hu0
  let a : ℝ := (r ^ 2)⁻¹
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have haOne : a ≤ 1 := by
    dsimp [a]
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg r]
  have hscale :
      teardropMap z = (a : ℂ) * teardropMap q := by
    unfold teardropMap
    change u ^ 2 =
      (a : ℂ) * (1 - q.val) ^ 2
    have hqdiff : (1 : ℂ) - q.val = (r : ℂ) * u := by
      dsimp [q, qval]
      ring
    rw [hqdiff, mul_pow]
    dsimp [a]
    have hrne : r ≠ 0 := hrPos.ne'
    push_cast
    field_simp [hrne]
  exact ⟨q, a, by simpa [q] using hqNorm,
    hqne, haPos, haOne, hscale⟩

theorem baseChildGluingMap_surjective :
    Function.Surjective baseChildGluingMap := by
  rintro ⟨x, z, rfl⟩
  by_cases hz : z.val = 1
  · let p : PolygonCell 1 :=
      PolygonCell.side (0 : Fin 1) 0
    refine ⟨@Quotient.mk'' BaseChildPair
      (DiskSquare.paramChildSeamSetoid 0 1) (.inl p), ?_⟩
    apply Subtype.ext
    change monogonMap p = teardropMap z
    have hp : p.val = 1 := by
      dsimp [p]
      change
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 1) 0) : ℂ) = 1
      simp [PolygonCell.sideAngle]
    unfold monogonMap teardropMap
    rw [hz, hp]
    ring
  · obtain ⟨q, a, hqnorm, hqne, haPos, haOne, hscale⟩ :=
      exists_teardrop_boundary_scale z hz
    by_cases haHalf : a ≤ (2 : ℝ)⁻¹
    · have hb0 : 0 ≤ 2 * a := by positivity
      have hb1 : 2 * a ≤ 1 := by
        norm_num at haHalf ⊢
        linarith
      obtain ⟨v, hv⟩ :=
        smul_teardropMap_mem_range q hb0 hb1
      refine ⟨@Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1) (.inl v), ?_⟩
      apply Subtype.ext
      change monogonMap v = teardropMap z
      unfold monogonMap
      rw [hv, hscale]
      push_cast
      norm_num
      ring
    · have haHalf' : (2 : ℝ)⁻¹ ≤ a :=
        le_of_not_ge haHalf
      obtain ⟨w, hw⟩ :=
        exists_collarMap_eq_smul_teardropMap
          q hqnorm hqne haHalf' haOne
      refine ⟨@Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1) (.inr w), ?_⟩
      apply Subtype.ext
      change collarMap w = teardropMap z
      rw [hw, hscale]

/-- A monogon glued along its entire side to one side of a digon is a closed disk. -/
noncomputable def baseChildGluingHomeomorph :
    DiskSquare.ParamChildGluing 0 1 ≃ₜ Teardrop := by
  let e : DiskSquare.ParamChildGluing 0 1 ≃ Teardrop :=
    Equiv.ofBijective baseChildGluingMap
      ⟨baseChildGluingMap_injective,
        baseChildGluingMap_surjective⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) baseChildGluingMap.continuous

@[simp]
theorem baseChildGluingHomeomorph_apply
    (q : DiskSquare.ParamChildGluing 0 1) :
    baseChildGluingHomeomorph q = baseChildGluingMap q :=
  rfl

/-- The complete base equivalence from the unsplit monogon to the one-sided-degenerate child
quotient. -/
noncomputable def baseSourceChildGluingHomeomorph :
    PolygonCell 1 ≃ₜ DiskSquare.ParamChildGluing 0 1 :=
  teardropHomeomorph.trans baseChildGluingHomeomorph.symm

/-! ## Exact compatibility with the surviving digon side -/

theorem side_one_digon_val (t : unitInterval) :
    (PolygonCell.side (1 : Fin 2) t : PolygonCell 2).val =
      (Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ) := by
  change
    (Circle.exp
        (PolygonCell.sideAngle (1 : Fin 2) t) : ℂ) =
      (Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ)
  congr 2
  unfold PolygonCell.sideAngle
  norm_num
  ring

theorem side_one_digon_im (t : unitInterval) :
    (PolygonCell.side (1 : Fin 2) t : PolygonCell 2).val.im =
      -Real.sin (Real.pi * (t : ℝ)) := by
  rw [side_one_digon_val]
  simp only [Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]
  have hangle :
      Real.pi * (1 + (t : ℝ)) =
        Real.pi * (t : ℝ) + Real.pi := by ring
  rw [hangle, Real.sin_add_pi]

theorem chordHeight_side_one_digon (t : unitInterval) :
    chordHeight (PolygonCell.side (1 : Fin 2) t) =
      Real.sin (Real.pi * (t : ℝ)) := by
  let z : PolygonCell 2 := PolygonCell.side (1 : Fin 2) t
  let θ : ℝ := Real.pi * (t : ℝ)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le t.property.1
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos, t.property.2]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have him : z.val.im = -Real.sin θ := by
    simpa [z, θ] using side_one_digon_im t
  have hnormSq : Complex.normSq z.val = 1 := by
    have hmem :=
      PolygonCell.side_mem_sphere (1 : Fin 2) t
    rw [Metric.mem_sphere, Complex.dist_eq,
      sub_zero] at hmem
    rw [Complex.normSq_eq_norm_sq, hmem]
    norm_num
  rw [Complex.normSq_apply] at hnormSq
  have hsSq := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  change chordHeight z = Real.sin θ
  rw [him] at hnormSq
  nlinarith

theorem collarCirclePoint_side_one_digon (t : unitInterval) :
    collarCirclePoint (PolygonCell.side (1 : Fin 2) t) =
      PolygonCell.side (0 : Fin 1) t := by
  apply PolygonCell.ext
  let z : PolygonCell 2 := PolygonCell.side (1 : Fin 2) t
  have hheight :
      chordHeight z = Real.sin (Real.pi * (t : ℝ)) := by
    simpa [z] using chordHeight_side_one_digon t
  have him :
      z.val.im = -Real.sin (Real.pi * (t : ℝ)) := by
    simpa [z] using side_one_digon_im t
  have hlower :
      ((z.val.re : ℂ) -
          (chordHeight z : ℂ) * Complex.I) = z.val := by
    apply Complex.ext
    · simp
    · simp only [Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, add_zero]
      rw [hheight, him]
      ring
  change collarCircleValue z =
    (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val
  unfold collarCircleValue
  rw [hlower]
  rw [side_one_digon_val]
  change
    ((Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ) ^ 2) =
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 1) t) : ℂ)
  rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun q : Circle ↦ (q : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  simp only [PolygonCell.sideAngle, Fin.val_zero,
    Nat.cast_one, div_one, Int.cast_one, one_mul]
  ring

theorem collarMap_eq_teardropMap_collarCirclePoint_of_im_eq_neg
    (z : PolygonCell 2)
    (hy : z.val.im = -chordHeight z) :
    collarMap z = teardropMap (collarCirclePoint z) := by
  unfold collarMap
  rw [hy, teardropMap_collarCirclePoint]
  push_cast
  ring

theorem collarMap_old_side (t : unitInterval) :
    collarMap (PolygonCell.side (1 : Fin 2) t) =
      teardropMap (PolygonCell.side (0 : Fin 1) t) := by
  rw [collarMap_eq_teardropMap_collarCirclePoint_of_im_eq_neg,
    collarCirclePoint_side_one_digon]
  rw [side_one_digon_im, chordHeight_side_one_digon]

/-- In the base one-sided-degenerate P2 equivalence, the source side is exactly the surviving
digon side. -/
theorem baseSourceChildGluingHomeomorph_side
    (t : unitInterval) :
    baseSourceChildGluingHomeomorph
        (PolygonCell.side (0 : Fin 1) t) =
      @Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1)
        (.inr (PolygonCell.side (1 : Fin 2) t)) := by
  apply baseChildGluingHomeomorph.injective
  rw [baseSourceChildGluingHomeomorph,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    baseChildGluingHomeomorph_apply,
    baseChildGluingMap_mk]
  apply Subtype.ext
  rw [teardropHomeomorph_apply_val,
    baseChildPairMap_inr]
  exact (collarMap_old_side t).symm

/-! ## Transport to an arbitrary positive surviving side count -/

/-- Boundary weights which make side zero fill one digon semicircle and divide the other
semicircle equally among the `r` old sides. -/
def rightDegenerateWeights (r : ℕ) : List ℕ :=
  r :: List.replicate r 1

@[simp]
theorem rightDegenerateWeights_length (r : ℕ) :
    (rightDegenerateWeights r).length = r + 1 := by
  simp [rightDegenerateWeights]

@[simp]
theorem rightDegenerateWeights_sum (r : ℕ) :
    (rightDegenerateWeights r).sum = 2 * r := by
  simp [rightDegenerateWeights]
  omega

theorem rightDegenerateWeights_positive
    {r : ℕ} (hr : 0 < r) :
    WeightedCircle.Positive (rightDegenerateWeights r) := by
  intro w hw
  simp only [rightDegenerateWeights, List.mem_cons,
    List.mem_replicate] at hw
  rcases hw with rfl | ⟨_, rfl⟩
  · exact hr
  · norm_num

theorem rightDegenerateWeights_ne_nil (r : ℕ) :
    rightDegenerateWeights r ≠ [] := by
  simp [rightDegenerateWeights]

theorem rightDegenerateWeights_get_zero (r : ℕ) :
    (rightDegenerateWeights r).get
        ⟨0, by simp⟩ = r := by
  simp [rightDegenerateWeights]

theorem rightDegenerateWeights_take_succ
    (r : ℕ) (i : Fin r) :
    (rightDegenerateWeights r).take (i.val + 1) =
      r :: List.replicate i.val 1 := by
  simp [rightDegenerateWeights, List.take_succ_cons]

theorem rightDegenerateWeights_get_succ
    (r : ℕ) (i : Fin r) :
    (rightDegenerateWeights r).get
        ⟨i.val + 1, by
          simp only [rightDegenerateWeights_length]
          omega⟩ = 1 := by
  simp [rightDegenerateWeights]

/-- The common parameter occupied by old side `i` inside the surviving digon semicircle. -/
noncomputable def oldSideParameter
    {r : ℕ} (hr : 0 < r) (i : Fin r)
    (t : unitInterval) : unitInterval :=
  ⟨((i.val : ℝ) + (t : ℝ)) / r,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1)
      (Nat.cast_nonneg _),
    by
      rw [div_le_one (by positivity)]
      have hi : (i.val : ℝ) + 1 ≤ r := by
        exact_mod_cast i.isLt
      linarith [t.property.2]⟩

/-- Reparameterize the `(r+1)`-gon boundary as a digon boundary, assigning the entire first
semicircle to the fresh side. -/
noncomputable def rightBoundaryHomeomorph
    (r : ℕ) (hr : 0 < r) : Circle ≃ₜ Circle :=
  WeightedCircle.circleHomeomorph
    (rightDegenerateWeights r)
    (rightDegenerateWeights_positive hr)
    (rightDegenerateWeights_ne_nil r)

/-- Radially extend the weighted boundary map from the surviving child to a digon. -/
noncomputable def rightCellHomeomorph
    (r : ℕ) (hr : 0 < r) :
    PolygonCell (r + 1) ≃ₜ PolygonCell 2 :=
  PolygonCell.radialHomeomorph
    (rightBoundaryHomeomorph r hr)

/-- Forget the side subdivision on the unsplit source disk. -/
noncomputable def sourceCellHomeomorph
    (r : ℕ) : PolygonCell r ≃ₜ PolygonCell 1 :=
  PolygonCell.radialHomeomorph (Homeomorph.refl Circle)

theorem rightBoundaryHomeomorph_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    rightBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      Circle.exp
        (PolygonCell.sideAngle (0 : Fin 2) t) := by
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (rightDegenerateWeights r)
      (rightDegenerateWeights_positive hr)
      (rightDegenerateWeights_ne_nil r)
      ⟨0, by simp⟩ t
  rw [show PolygonCell.sideAngle (0 : Fin (r + 1)) t =
      2 * Real.pi / (rightDegenerateWeights r).length *
        ((0 : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [rightDegenerateWeights_length,
      Fin.val_zero, Nat.cast_zero, zero_add]
    ring]
  unfold rightBoundaryHomeomorph
  have h' := h
  simp only [Nat.cast_zero, zero_add] at h'
  simp only [zero_add]
  rw [h']
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  simp only [rightDegenerateWeights_sum,
    List.take_zero, List.sum_nil,
    rightDegenerateWeights_get_zero,
    Nat.cast_zero, zero_add, Int.cast_zero,
    zero_mul, add_zero]
  unfold PolygonCell.sideAngle
  simp only [Fin.val_zero, Nat.cast_zero, zero_add]
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrReal]

theorem rightBoundaryHomeomorph_old
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    rightBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (i.addNat 1) t)) =
      Circle.exp
        (PolygonCell.sideAngle (1 : Fin 2)
          (oldSideParameter hr i t)) := by
  let j : Fin (rightDegenerateWeights r).length :=
    ⟨i.val + 1, by
      simp only [rightDegenerateWeights_length]
      omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (rightDegenerateWeights r)
      (rightDegenerateWeights_positive hr)
      (rightDegenerateWeights_ne_nil r) j t
  rw [show PolygonCell.sideAngle (i.addNat 1) t =
      2 * Real.pi / (rightDegenerateWeights r).length *
        ((j : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [rightDegenerateWeights_length, j,
      Fin.val_addNat]
    ring]
  unfold rightBoundaryHomeomorph
  rw [h]
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  have hget :
      (rightDegenerateWeights r).get j = 1 := by
    dsimp [j]
    exact rightDegenerateWeights_get_succ r i
  rw [hget]
  rw [rightDegenerateWeights_take_succ]
  simp only [rightDegenerateWeights_sum,
    List.sum_cons, List.sum_replicate,
    nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat,
    Int.cast_zero, zero_mul, add_zero]
  unfold PolygonCell.sideAngle oldSideParameter
  simp only [Fin.val_one, Nat.cast_one]
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrReal]
  ring

theorem rightCellHomeomorph_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    rightCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1)) t) =
      PolygonCell.side (0 : Fin 2) t := by
  unfold rightCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (rightBoundaryHomeomorph r hr)
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (PolygonCell.sideAngle (0 : Fin (r + 1)) t))) =
      PolygonCell.ofCircle 2
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 2) t))
  rw [PolygonCell.radialHomeomorph_ofCircle,
    rightBoundaryHomeomorph_fresh]

theorem rightCellHomeomorph_old
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    rightCellHomeomorph r hr
        (PolygonCell.side (i.addNat 1) t) =
      PolygonCell.side (1 : Fin 2)
        (oldSideParameter hr i t) := by
  unfold rightCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (rightBoundaryHomeomorph r hr)
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (PolygonCell.sideAngle (i.addNat 1) t))) =
      PolygonCell.ofCircle 2
        (Circle.exp
          (PolygonCell.sideAngle (1 : Fin 2)
            (oldSideParameter hr i t)))
  rw [PolygonCell.radialHomeomorph_ofCircle,
    rightBoundaryHomeomorph_old]

theorem sourceCellHomeomorph_side
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    sourceCellHomeomorph r
        (PolygonCell.side i t) =
      PolygonCell.side (0 : Fin 1)
        (oldSideParameter hr i t) := by
  unfold sourceCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (Homeomorph.refl Circle)
        (PolygonCell.ofCircle r
          (Circle.exp (PolygonCell.sideAngle i t))) =
      PolygonCell.ofCircle 1
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 1)
            (oldSideParameter hr i t)))
  rw [PolygonCell.radialHomeomorph_ofCircle]
  apply congrArg (PolygonCell.ofCircle 1)
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  unfold PolygonCell.sideAngle oldSideParameter
  simp only [Fin.val_zero, Nat.cast_zero,
    Nat.cast_one, zero_add, div_one,
    Int.cast_zero, zero_mul, add_zero]
  ring

/-- Simultaneously straighten a one-sided-degenerate child pair to the base monogon--digon
pair. -/
noncomputable def childPairBaseHomeomorph
    (r : ℕ) (hr : 0 < r) :
    DiskSquare.ChildPair 0 r ≃ₜ BaseChildPair :=
  Homeomorph.sumCongr
    (Homeomorph.refl (PolygonCell 1))
    (rightCellHomeomorph r hr)

@[simp]
theorem childPairBaseHomeomorph_inl
    (r : ℕ) (hr : 0 < r) (z : PolygonCell 1) :
    childPairBaseHomeomorph r hr (.inl z) = .inl z :=
  rfl

@[simp]
theorem childPairBaseHomeomorph_inr
    (r : ℕ) (hr : 0 < r)
    (z : PolygonCell (r + 1)) :
    childPairBaseHomeomorph r hr (.inr z) =
      .inr (rightCellHomeomorph r hr z) :=
  rfl

theorem rightCellHomeomorph_symm_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (rightCellHomeomorph r hr).symm
        (PolygonCell.side (0 : Fin 2) t) =
      PolygonCell.side (0 : Fin (r + 1)) t := by
  apply (rightCellHomeomorph r hr).injective
  rw [Homeomorph.apply_symm_apply,
    rightCellHomeomorph_fresh]

theorem childPairBase_generator_map
    (r : ℕ) (hr : 0 < r)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator 0 1
      (childPairBaseHomeomorph r hr x)
      (childPairBaseHomeomorph r hr y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 1
          (.inl (PolygonCell.side (0 : Fin 1) t))
          (.inr
            (rightCellHomeomorph r hr
              (PolygonCell.side (0 : Fin (r + 1))
                (unitInterval.symm t))))
      rw [rightCellHomeomorph_fresh]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem childPairBase_generator_comap
    (r : ℕ) (hr : 0 < r)
    {x y : BaseChildPair}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 1 x y) :
    DiskSquare.ParamChildSeamGenerator 0 r
      ((childPairBaseHomeomorph r hr).symm x)
      ((childPairBaseHomeomorph r hr).symm y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 r
          (.inl (PolygonCell.side (0 : Fin 1) t))
          (.inr
            ((rightCellHomeomorph r hr).symm
              (PolygonCell.side (0 : Fin 2)
                (unitInterval.symm t))))
      rw [rightCellHomeomorph_symm_fresh]
      exact DiskSquare.ParamChildSeamGenerator.glue t

/-- The weighted child straightening identifies exactly the two generated seam relations. -/
theorem childPairBase_eqvGen_iff
    (r : ℕ) (hr : 0 < r)
    (x y : DiskSquare.ChildPair 0 r) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 r) x y ↔
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (childPairBaseHomeomorph r hr x)
        (childPairBaseHomeomorph r hr y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (childPairBase_generator_map r hr h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e := childPairBaseHomeomorph r hr
    have hcomap :
        ∀ {u v : BaseChildPair},
          Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 1)
              u v →
            Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 r)
              (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          exact Relation.EqvGen.rel _ _
            (childPairBase_generator_comap r hr h)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using
      hcomap hxy

/-- The arbitrary one-sided-degenerate child quotient is identified with the base
monogon--digon quotient. -/
noncomputable def childGluingBaseHomeomorph
    (r : ℕ) (hr : 0 < r) :
    DiskSquare.ParamChildGluing 0 r ≃ₜ
      DiskSquare.ParamChildGluing 0 1 :=
  Homeomorph.Quotient.congr
    (childPairBaseHomeomorph r hr)
    (childPairBase_eqvGen_iff r hr)

@[simp]
theorem childGluingBaseHomeomorph_mk
    (r : ℕ) (hr : 0 < r)
    (x : DiskSquare.ChildPair 0 r) :
    childGluingBaseHomeomorph r hr
        (@Quotient.mk'' (DiskSquare.ChildPair 0 r)
          (DiskSquare.paramChildSeamSetoid 0 r) x) =
      @Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1)
        (childPairBaseHomeomorph r hr x) :=
  rfl

/-- The local source-to-children equivalence for any ordinary-valid right one-sided-degenerate
P2 cut. -/
noncomputable def sourceChildGluingHomeomorph
    (r : ℕ) (hr : 0 < r) :
    PolygonCell r ≃ₜ DiskSquare.ParamChildGluing 0 r :=
  (sourceCellHomeomorph r).trans
    (baseSourceChildGluingHomeomorph.trans
      (childGluingBaseHomeomorph r hr).symm)

/-- Every old source side is carried to the corresponding surviving-child side with its exact
original parameter. -/
theorem sourceChildGluingHomeomorph_side
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    sourceChildGluingHomeomorph r hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair 0 r)
        (DiskSquare.paramChildSeamSetoid 0 r)
        (.inr (PolygonCell.side (i.addNat 1) t)) := by
  apply (childGluingBaseHomeomorph r hr).injective
  rw [sourceChildGluingHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply,
    childGluingBaseHomeomorph_mk,
    childPairBaseHomeomorph_inr,
    sourceCellHomeomorph_side,
    rightCellHomeomorph_old]
  exact baseSourceChildGluingHomeomorph_side
    (oldSideParameter hr i t)

end P2DegenerateDisk

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification21_block_04
/- END ClassificationOfSurfaces.P2DegenerateDisk -/

/- BEGIN ClassificationOfSurfaces.SphereHemisphere | 7c64beef767600bc96b08fa7bef7fb7f47cc96557009fe234bb8954bae179c56 -/
section schottkyclassification21_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Hemisphere maps for the two-monogon sphere

This file maps the two disk faces of `SurfaceCellComplex.sphere` to the upper and lower unit
hemispheres. The lower face uses complex conjugation, so the existing opposite-direction monogon
pairing has identical images.

The two possible directed sphere identifications are classified explicitly. The resulting
continuous facewise map on the polygonal pre-realization respects every raw gluing generator.
`SphereQuotientHomeomorph` descends this map and proves that it is a homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- The squared radius of a point in an indexed polygon cell is at most one. -/
theorem normSq_le_one {n : ℕ} (z : PolygonCell n) : Complex.normSq z.val ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq, sq_le_one_iff_abs_le_one, abs_norm]
  simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property

/-- The nonnegative height above the equatorial plane associated to a disk point. -/
noncomputable def hemisphereHeight {n : ℕ} (z : PolygonCell n) : ℝ :=
  Real.sqrt (1 - Complex.normSq z.val)

theorem hemisphereHeight_nonneg {n : ℕ} (z : PolygonCell n) :
    0 ≤ hemisphereHeight z :=
  Real.sqrt_nonneg _

@[simp]
theorem hemisphereHeight_sq {n : ℕ} (z : PolygonCell n) :
    hemisphereHeight z ^ 2 = 1 - Complex.normSq z.val := by
  exact Real.sq_sqrt (sub_nonneg.mpr (normSq_le_one z))

@[fun_prop]
theorem continuous_hemisphereHeight {n : ℕ} :
    Continuous (hemisphereHeight : PolygonCell n → ℝ) := by
  unfold hemisphereHeight
  exact Real.continuous_sqrt.comp
    (continuous_const.sub (Complex.continuous_normSq.comp PolygonCell.continuous_val))

/-- A disk point placed on the upper unit hemisphere. -/
noncomputable def upperHemisphereVector (z : PolygonCell 1) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[z.val.re, z.val.im, hemisphereHeight z]

/-- A conjugated disk point placed on the lower unit hemisphere. -/
noncomputable def lowerHemisphereVector (z : PolygonCell 1) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[(conj z.val).re, (conj z.val).im, -hemisphereHeight z]

theorem upperHemisphereVector_norm (z : PolygonCell 1) :
    ‖upperHemisphereVector z‖ = 1 := by
  have hsquare : ‖upperHemisphereVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [upperHemisphereVector, Fin.sum_univ_succ, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (upperHemisphereVector z)]

theorem lowerHemisphereVector_norm (z : PolygonCell 1) :
    ‖lowerHemisphereVector z‖ = 1 := by
  have hsquare : ‖lowerHemisphereVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [lowerHemisphereVector, Fin.sum_univ_succ, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (lowerHemisphereVector z)]

@[fun_prop]
theorem continuous_upperHemisphereVector : Continuous upperHemisphereVector := by
  unfold upperHemisphereVector
  fun_prop

@[fun_prop]
theorem continuous_lowerHemisphereVector : Continuous lowerHemisphereVector := by
  unfold lowerHemisphereVector
  fun_prop

/-- The continuous map from a monogon disk to the upper unit hemisphere. -/
noncomputable def upperHemisphere : C(PolygonCell 1, SphereRepresentative) where
  toFun z := ⟨upperHemisphereVector z, by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using upperHemisphereVector_norm z⟩
  continuous_toFun := continuous_upperHemisphereVector.subtype_mk fun z ↦ by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using upperHemisphereVector_norm z

/-- The continuous map from a monogon disk to the lower unit hemisphere. -/
noncomputable def lowerHemisphere : C(PolygonCell 1, SphereRepresentative) where
  toFun z := ⟨lowerHemisphereVector z, by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using lowerHemisphereVector_norm z⟩
  continuous_toFun := continuous_lowerHemisphereVector.subtype_mk fun z ↦ by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using lowerHemisphereVector_norm z

@[simp]
theorem hemisphereHeight_side_monogon (t : unitInterval) :
    hemisphereHeight (side (0 : Fin 1) t) = 0 := by
  unfold hemisphereHeight
  have hnorm : ‖((side (0 : Fin 1) t : PolygonCell 1).val : ℂ)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (side_mem_sphere (0 : Fin 1) t)
  rw [Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- The positive-to-negative monogon pairing has the same upper and lower hemisphere image. -/
theorem upperHemisphere_side_eq_lowerHemisphere_side_symm (t : unitInterval) :
    upperHemisphere (side (0 : Fin 1) t) =
      lowerHemisphere (side (0 : Fin 1) (unitInterval.symm t)) := by
  apply Subtype.ext
  change upperHemisphereVector (side (0 : Fin 1) t) =
    lowerHemisphereVector (side (0 : Fin 1) (unitInterval.symm t))
  unfold upperHemisphereVector lowerHemisphereVector
  rw [conj_side_symm_monogon]
  ext i
  fin_cases i <;> simp

/-- The swapped monogon pairing has the same lower and upper hemisphere image. -/
theorem lowerHemisphere_side_eq_upperHemisphere_side_symm (t : unitInterval) :
    lowerHemisphere (side (0 : Fin 1) t) =
      upperHemisphere (side (0 : Fin 1) (unitInterval.symm t)) := by
  simpa only [unitInterval.symm_symm] using
    (upperHemisphere_side_eq_lowerHemisphere_side_symm (unitInterval.symm t)).symm

end PolygonCell

namespace SurfaceCellComplex

/-- Every boundary occurrence of the sphere is one of its two monogon occurrences. -/
theorem sphereBoundaryOccurrence_eq (occurrence : sphere.BoundaryOccurrence) :
    occurrence = spherePositiveOccurrence ∨ occurrence = sphereNegativeOccurrence := by
  rcases occurrence with ⟨face, index⟩
  cases face
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    exact Or.inl rfl
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    exact Or.inr rfl

/-- The two directed forms of the unique sphere side pairing exhaust its identifications. -/
theorem mem_sphere_polygonalIdentifications_iff
    (identification :
      PolygonGluing.Identification sphere.Face sphere.faceBoundaryLength) :
    identification ∈ sphere.polygonalIdentifications sphere_occurrencePairingValid ↔
      identification = sphereBoundaryPairing.identification ∨
        identification = swapIdentification sphereBoundaryPairing.identification := by
  change identification ∈ Set.range BoundaryPairing.identification ↔ _
  constructor
  · rintro
      ⟨⟨source, target, hne, _hsource, _htarget, direction, hcompatible⟩, rfl⟩
    rcases sphereBoundaryOccurrence_eq source with rfl | rfl
    · rcases sphereBoundaryOccurrence_eq target with rfl | rfl
      · exact (hne rfl).elim
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inl rfl
    · rcases sphereBoundaryOccurrence_eq target with rfl | rfl
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inr rfl
      · exact (hne rfl).elim
  · rintro (rfl | rfl)
    · exact sphereBoundaryPairing_mem
    · exact swapIdentification_mem_polygonalIdentifications
        sphere_occurrencePairingValid sphereBoundaryPairing_mem

/-- The continuous facewise map from the two monogon disks to the corresponding hemispheres. -/
noncomputable def spherePreMap : C(sphere.PolygonalPreRealization, SphereRepresentative) where
  toFun
    | ⟨false, z⟩ => PolygonCell.upperHemisphere z
    | ⟨true, z⟩ => PolygonCell.lowerHemisphere z
  continuous_toFun := by
    apply continuous_sigma
    intro face
    cases face
    · exact PolygonCell.upperHemisphere.continuous
    · exact PolygonCell.lowerHemisphere.continuous

@[simp]
theorem spherePreMap_false (z : PolygonCell 1) :
    spherePreMap ⟨false, z⟩ = PolygonCell.upperHemisphere z :=
  rfl

@[simp]
theorem spherePreMap_true (z : PolygonCell 1) :
    spherePreMap ⟨true, z⟩ = PolygonCell.lowerHemisphere z :=
  rfl

/-- The facewise map respects the canonical directed sphere boundary pairing. -/
theorem spherePreMap_sphereBoundaryPairing (t : unitInterval) :
    spherePreMap (sphereBoundaryPairing.identification.source.point t) =
      spherePreMap
        (sphereBoundaryPairing.identification.target.point
          (sphereBoundaryPairing.identification.parameter t)) := by
  change PolygonCell.upperHemisphere (PolygonCell.side (0 : Fin 1) t) =
    PolygonCell.lowerHemisphere
      (PolygonCell.side (0 : Fin 1) (unitInterval.symm t))
  exact PolygonCell.upperHemisphere_side_eq_lowerHemisphere_side_symm t

/-- The facewise map respects the swapped directed sphere boundary pairing. -/
theorem spherePreMap_swapSphereBoundaryPairing (t : unitInterval) :
    spherePreMap
        ((swapIdentification sphereBoundaryPairing.identification).source.point t) =
      spherePreMap
        ((swapIdentification sphereBoundaryPairing.identification).target.point
          ((swapIdentification sphereBoundaryPairing.identification).parameter t)) := by
  change PolygonCell.lowerHemisphere (PolygonCell.side (0 : Fin 1) t) =
    PolygonCell.upperHemisphere
      (PolygonCell.side (0 : Fin 1) (unitInterval.symm t))
  exact PolygonCell.lowerHemisphere_side_eq_upperHemisphere_side_symm t

/-- The facewise sphere map identifies the endpoints of every raw polygon gluing generator. -/
theorem spherePreMap_eq_of_generator
    {x y : sphere.PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        (sphere.polygonalIdentifications sphere_occurrencePairingValid) x y) :
    spherePreMap x = spherePreMap y := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_sphere_polygonalIdentifications_iff] at hidentification
      rcases hidentification with rfl | rfl
      · exact spherePreMap_sphereBoundaryPairing t
      · exact spherePreMap_swapSphereBoundaryPairing t

end SurfaceCellComplex

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification21_block_05
/- END ClassificationOfSurfaces.SphereHemisphere -/

/- BEGIN ClassificationOfSurfaces.CanonicalGeneratorMaps | 8f7a3fc569e6aec5d02e5484361ef9255621fa4066986dbfe7291cb17e18d284 -/
section schottkyclassification21_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Generator maps for the canonical Eval representatives

This file upgrades the explicit carrier-coordinate comparisons to maps between the full raw
generator relations.  Together with the reverse maps from the trusted Eval constructors, these
maps identify the generated equivalence relations and descend the one-face carrier homeomorphisms
to the canonical quotient spaces.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces.NormalForm

open Complex
open SurfaceCellComplex

/-- Every orientable polygon generator maps into the trusted equivalence closure. -/
theorem orientableGenerator_to_eqvGen
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid)) x y) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n) x)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n) y) := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_orientable_polygonalIdentifications_iff hvalid] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨i, rfl | rfl⟩ | ⟨j, rfl | rfl⟩
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
              (unitInterval.symm t)))
        exact orientableCarrier_handle_a_eqvGen (n := n) i t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 2) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_handle_a_eqvGen (n := n) i (unitInterval.symm t))
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
              (unitInterval.symm t)))
        exact orientableCarrier_handle_b_eqvGen (n := n) i t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 3) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 1)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_handle_b_eqvGen (n := n) i (unitInterval.symm t))
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
              (unitInterval.symm t)))
        exact orientableCarrier_boundary_c_eqvGen (p := p) j t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_boundary_c_eqvGen (p := p) j (unitInterval.symm t))

/-- Every nonorientable polygon generator maps into the trusted equivalence closure. -/
theorem nonOrientableGenerator_to_eqvGen
    {p n : ℕ} (hp : 1 ≤ p)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp)) x y) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n) x)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n) y) := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_nonOrientable_polygonalIdentifications_iff hp] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨j, rfl | rfl⟩
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 0) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 1) t))
        exact nonOrientableCarrier_crosscap_a_eqvGen (n := n) i t
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 1) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 0) t))
        exact Relation.EqvGen.symm _ _
          (nonOrientableCarrier_crosscap_a_eqvGen (n := n) i t)
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 0) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 2)
              (unitInterval.symm t)))
        exact nonOrientableCarrier_boundary_c_eqvGen (p := p) j t
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 2) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (nonOrientableCarrier_boundary_c_eqvGen
            (p := p) j (unitInterval.symm t))

/-- Every trusted orientable generator maps back into the polygonal equivalence closure. -/
theorem orientableRel_to_polygonEqvGen
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    {x y : ClosedUnitDisc} (hxy : OrientableRel p n x y) :
    Relation.EqvGen
      (PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid)))
      ((oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)).symm x)
      ((oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)).symm y) := by
  cases hxy with
  | a t i =>
      rw [← orientableCarrier_handle_a_pos i t,
        ← orientableCarrier_handle_a_neg i t]
      erw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (orientableHandleAIdentification (n := n) i)
          (orientableHandleAIdentification_mem (n := n) hvalid i) t)
  | b t i =>
      rw [← orientableCarrier_handle_b_pos i t,
        ← orientableCarrier_handle_b_neg i t]
      erw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (orientableHandleBIdentification (n := n) i)
          (orientableHandleBIdentification_mem (n := n) hvalid i) t)
  | c t i =>
      have hsource :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (orientableBoundaryWord p n)
              (orientableOccurrencePoint p n
                (orientableBoundaryPosition p n (Fin.rev i) 2)
                (unitInterval.symm t)) := by
        simpa using
          orientableBoundary_trustedSource_eq_carrier_c_neg
            (p := p) (Fin.rev i) t
      have htarget :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (orientableBoundaryWord p n)
              (orientableOccurrencePoint p n
                (orientableBoundaryPosition p n (Fin.rev i) 0) t) := by
        simpa using
          orientableBoundary_trustedTarget_eq_carrier_c_pos
            (p := p) (Fin.rev i) t
      rw [hsource, htarget]
      erw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      change Relation.EqvGen
        (PolygonGluing.Generator
          ((orientableCellComplex p n).polygonalIdentifications
            (orientableCellComplex_occurrencePairingValid hvalid)))
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n (Fin.rev i) 2)
          (unitInterval.symm t))
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n (Fin.rev i) 0) t)
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (PolygonGluing.Generator.glue
            (orientableBoundaryIdentification (p := p) (Fin.rev i))
            (orientableBoundaryIdentification_mem
              (p := p) hvalid (Fin.rev i)) t))

/-- Every trusted nonorientable generator maps back into the polygonal equivalence closure. -/
theorem nonOrientableRel_to_polygonEqvGen
    {p n : ℕ} (hp : 1 ≤ p)
    {x y : ClosedUnitDisc} (hxy : NonOrientableRel p n x y) :
    Relation.EqvGen
      (PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp)))
      ((oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)).symm x)
      ((oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)).symm y) := by
  cases hxy with
  | a t i =>
      rw [← nonOrientableCarrier_crosscap_a_first i t,
        ← nonOrientableCarrier_crosscap_a_second i t]
      erw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (nonOrientableCrosscapIdentification (n := n) i)
          (nonOrientableCrosscapIdentification_mem (n := n) hp i) t)
  | c t i =>
      have hsource :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (nonOrientableBoundaryWord p n)
              (nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n (Fin.rev i) 2)
                (unitInterval.symm t)) := by
        simpa using
          nonOrientableBoundary_trustedSource_eq_carrier_c_neg
            (p := p) (Fin.rev i) t
      have htarget :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + 3 - (t : ℝ)) / (2 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (nonOrientableBoundaryWord p n)
              (nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n (Fin.rev i) 0) t) := by
        simpa using
          nonOrientableBoundary_trustedTarget_eq_carrier_c_pos
            (p := p) (Fin.rev i) t
      rw [hsource, htarget]
      erw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      change Relation.EqvGen
        (PolygonGluing.Generator
          ((nonOrientableCellComplex p n).polygonalIdentifications
            (nonOrientableCellComplex_occurrencePairingValid hp)))
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n (Fin.rev i) 2)
          (unitInterval.symm t))
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n (Fin.rev i) 0) t)
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (PolygonGluing.Generator.glue
            (nonOrientableBoundaryIdentification (p := p) (Fin.rev i))
            (nonOrientableBoundaryIdentification_mem
              (p := p) hp (Fin.rev i)) t))

/-- The canonical orientable polygonal realization is the trusted Eval quotient. -/
noncomputable def orientablePolygonalRealizationHomeomorph
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    (orientableCellComplex p n).PolygonalRealization
        (orientableCellComplex_occurrencePairingValid hvalid) ≃ₜ
      Quot (OrientableRel p n) :=
  eqvGenQuotientCongrRawOfGeneratorMaps
    (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n))
    (fun _ _ hxy ↦ orientableGenerator_to_eqvGen hvalid hxy)
    (fun _ _ hxy ↦ orientableRel_to_polygonEqvGen hvalid hxy)

/-- The canonical nonorientable polygonal realization is the trusted Eval quotient. -/
noncomputable def nonOrientablePolygonalRealizationHomeomorph
    {p n : ℕ} (hp : 1 ≤ p) :
    (nonOrientableCellComplex p n).PolygonalRealization
        (nonOrientableCellComplex_occurrencePairingValid hp) ≃ₜ
      Quot (NonOrientableRel p n) :=
  eqvGenQuotientCongrRawOfGeneratorMaps
    (oneFacePolygonalPreRealizationHomeomorph
      (nonOrientableBoundaryWord p n))
    (fun _ _ hxy ↦ nonOrientableGenerator_to_eqvGen hp hxy)
    (fun _ _ hxy ↦ nonOrientableRel_to_polygonEqvGen hp hxy)

end LeanEval.Topology.ClassificationOfSurfaces.NormalForm
end schottkyclassification21_block_06
/- END ClassificationOfSurfaces.CanonicalGeneratorMaps -/
