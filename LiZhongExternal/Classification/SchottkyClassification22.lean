/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification22: pinned classification sources; see BUNDLE_MAP.json. -/
import LiZhongExternal.Classification.SchottkyClassification20
import LiZhongExternal.Classification.SchottkyClassification21
import Mathlib.Data.Fin.Rev
import LiZhongExternal.Classification.SchottkyClassification03

/- BEGIN ClassificationOfSurfaces.FiniteCyclicMoves | f08eeada65ef056c77ad07493bba3f16be6e752efc81e476c78d28404f4693fb -/
noncomputable section

section schottkyclassification22_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite cyclic move closures

This file combines signed presentation isomorphisms and the two primitive Gallier--Xu
subdivisions into stable closure APIs.

`Subdivides` is the directed reflexive-transitive closure. It preserves ordinary validity,
connectivity, and Gallier validity. `HasCommonSubdivision P Q` supplies a validity-safe common
target for topological comparison: starting with two ordinary-valid presentations, both forward
chains remain ordinary-valid. This is stronger operational data than an unrestricted symmetric
move chain, which may pass through the exceptional empty-word sphere where
`PolygonalRealization` is deliberately unavailable.

`MoveEquivalent` is also provided as the purely syntactic equivalence closure. A common
subdivision implies move equivalence, but no converse or confluence theorem is asserted here.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- One directed presentation step: a signed isomorphism, P1 subdivision, or P2 subdivision. -/
def SubdivisionStep (P Q : FiniteCyclicPresentation) : Prop :=
  Nonempty (SignedPresentationIso P Q) ∨
    P1Subdivision P Q ∨ P2Subdivision P Q

namespace SubdivisionStep

theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    SubdivisionStep P Q :=
  Or.inl ⟨e⟩

theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inl h)

theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inr h)

/-- Every directed step preserves ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isSurfaceValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isSurfaceValid validP
    · exact hP2.isSurfaceValid validP

/-- Every directed step preserves face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isConnected connectedP
  · rcases hrest with hP1 | hP2
    · exact hP1.isConnected connectedP
    · exact hP2.isConnected connectedP

/-- Every directed step preserves the packed Gallier--Xu validity predicate. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isGallierValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isGallierValid validP
    · exact hP2.isGallierValid validP

end SubdivisionStep

/-- Directed finite subdivision by signed isomorphisms, P1, and P2. -/
def Subdivides (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.ReflTransGen SubdivisionStep P Q

namespace Subdivides

theorem refl (P : FiniteCyclicPresentation) : Subdivides P P :=
  Relation.ReflTransGen.refl

theorem single {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : Subdivides P Q :=
  Relation.ReflTransGen.single h

theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : Subdivides P Q :=
  single (SubdivisionStep.signedIso e)

theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p1 h)

theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p2 h)

theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (hQR : Subdivides Q R) :
    Subdivides P R :=
  Relation.ReflTransGen.trans hPQ hQR

/-- Directed subdivision chains preserve ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isSurfaceValid ih

/-- Directed subdivision chains preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  induction hPQ with
  | refl =>
      exact connectedP
  | tail _ hstep ih =>
      exact hstep.isConnected ih

/-- Directed subdivision chains preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isGallierValid ih

end Subdivides

/-- Two presentations have a common directed subdivision. -/
def HasCommonSubdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ R : FiniteCyclicPresentation, Subdivides P R ∧ Subdivides Q R

namespace HasCommonSubdivision

theorem refl (P : FiniteCyclicPresentation) : HasCommonSubdivision P P :=
  ⟨P, Subdivides.refl P, Subdivides.refl P⟩

theorem symm {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) :
    HasCommonSubdivision Q P := by
  rcases h with ⟨R, hPR, hQR⟩
  exact ⟨R, hQR, hPR⟩

end HasCommonSubdivision

/-- Purely syntactic equivalence generated by signed isomorphisms, P1, and P2. -/
def MoveEquivalent (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.EqvGen SubdivisionStep P Q

namespace MoveEquivalent

theorem refl (P : FiniteCyclicPresentation) : MoveEquivalent P P :=
  Relation.EqvGen.refl P

theorem ofStep {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : MoveEquivalent P Q :=
  Relation.EqvGen.rel P Q h

theorem symm {P Q : FiniteCyclicPresentation}
    (h : MoveEquivalent P Q) : MoveEquivalent Q P :=
  Relation.EqvGen.symm P Q h

theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : MoveEquivalent P Q) (hQR : MoveEquivalent Q R) :
    MoveEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR

end MoveEquivalent

/-- Every directed subdivision chain is a syntactic move equivalence. -/
theorem Subdivides.moveEquivalent {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) :
    MoveEquivalent P Q := by
  induction hPQ with
  | refl =>
      exact MoveEquivalent.refl P
  | @tail Q R _ hstep ih =>
      exact ih.trans (MoveEquivalent.ofStep hstep)

/-- A common directed subdivision is in particular a syntactic move equivalence. -/
theorem HasCommonSubdivision.moveEquivalent
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q) :
    MoveEquivalent P Q := by
  rcases h with ⟨R, hPR, hQR⟩
  exact hPR.moveEquivalent.trans hQR.moveEquivalent.symm

namespace PolygonallyEquivalent

theorem refl (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent P validP validP :=
  ⟨Homeomorph.refl _⟩

theorem symm {P Q : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    (h : P.PolygonallyEquivalent Q validP validQ) :
    Q.PolygonallyEquivalent P validQ validP := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem trans {P Q R : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    {validR : R.IsSurfaceValid}
    (hPQ : P.PolygonallyEquivalent Q validP validQ)
    (hQR : Q.PolygonallyEquivalent R validQ validR) :
    P.PolygonallyEquivalent R validP validR := by
  rcases hPQ with ⟨ePQ⟩
  rcases hQR with ⟨eQR⟩
  exact ⟨ePQ.trans eQR⟩

end PolygonallyEquivalent

/-- The stable proof obligation for primitive realization invariance.

The P1 and P2 realization files discharge the corresponding disjuncts; signed isomorphisms are
already implemented by `SignedPresentationIso.polygonallyEquivalent`. -/
def SubdivisionStep.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, SubdivisionStep P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P1 subdivisions. -/
def P1Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P1Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P2 subdivisions. -/
def P2Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P2Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- Signed-isomorphism invariance plus the two primitive geometric obligations supplies invariance
for every directed elementary step. -/
theorem SubdivisionStep.preservesPolygonalRealization
    (hP1 : P1Subdivision.PreservesPolygonalRealization)
    (hP2 : P2Subdivision.PreservesPolygonalRealization) :
    SubdivisionStep.PreservesPolygonalRealization := by
  intro P Q hstep validP validQ
  rcases hstep with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.polygonallyEquivalent validP validQ
  · rcases hrest with hP1Step | hP2Step
    · exact hP1 hP1Step validP validQ
    · exact hP2 hP2Step validP validQ

/-- If every primitive directed step preserves the faithful polygonal quotient, so does every
directed subdivision chain. -/
theorem Subdivides.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  induction hPQ with
  | refl =>
      exact PolygonallyEquivalent.refl P validP
  | @tail R Q hPR hstep ih =>
      let validR : R.IsSurfaceValid :=
        Subdivides.isSurfaceValid hPR validP
      exact (ih validR).trans (hprimitive hstep validR validQ)

/-- Primitive realization invariance promotes a common-subdivision certificate to a
homeomorphism of faithful polygonal quotients. -/
theorem HasCommonSubdivision.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  rcases h with ⟨R, hPR, hQR⟩
  let validR : R.IsSurfaceValid :=
    Subdivides.isSurfaceValid hPR validP
  exact
    (hPR.polygonallyEquivalent hprimitive validP validR).trans
      (hQR.polygonallyEquivalent hprimitive validQ validR).symm

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification22_block_01
/- END ClassificationOfSurfaces.FiniteCyclicMoves -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicUnorientedRealization | c6927bfbeb0b8f9d3c52155351cb9586371191a2e1ac9dfe22d8feb16115e33c -/
section schottkyclassification22_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal realization under independently reoriented faces

Gallier--Xu treat a face and the same face read in the opposite direction interchangeably. This
file records that convention explicitly. An `UnorientedPresentationIso` may rename and reorient
edges, relabel faces, cyclically rotate their boundaries, and independently reverse the traversal
orientation of every face.

Unlike `SignedPresentationIso`, this broader comparison does not claim to preserve the current
orientation-sensitive `IsSurfaceValid` predicate. When both endpoints are ordinarily valid, it
does preserve their faithful polygonal realizations. This is the exact extra comparison needed by
the cross-cap pseudo-rewrite, whose common P2 refinement reads one of its two faces backwards.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- Reflection of a polygon cell across the real axis. -/
noncomputable def reflectionHomeomorph (n : ℕ) : PolygonCell n ≃ₜ PolygonCell n where
  toFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  invFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  left_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  right_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  continuous_toFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)
  continuous_invFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)

@[simp]
theorem reflectionHomeomorph_apply (n : ℕ) (z : PolygonCell n) :
    (reflectionHomeomorph n z).val = conj z.val :=
  rfl

/-- Reflection reverses both the cyclic side index and its interval parameter. -/
theorem reflectionHomeomorph_side {n : ℕ} (i : Fin n) (t : unitInterval) :
    reflectionHomeomorph n (side i t) =
      side i.rev (unitInterval.symm t) := by
  apply PolygonCell.ext
  change conj (Circle.exp (sideAngle i t) : ℂ) =
    (Circle.exp (sideAngle i.rev (unitInterval.symm t)) : Circle)
  rw [← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  simp only [sideAngle, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    unitInterval.coe_symm_eq]
  rw [show i.rev.val = n - (i.val + 1) from rfl]
  rw [Nat.cast_sub (Nat.succ_le_iff.mpr i.isLt)]
  push_cast
  field_simp [Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)]
  ring

end PolygonCell

namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- Presentation isomorphism up to independent choices of traversal orientation on target
faces. -/
structure UnorientedPresentationIso (P Q : FiniteCyclicPresentation) where
  /-- The `edgeRelabeling` declaration. -/
  edgeRelabeling : EdgeRelabeling P.Edge Q.Edge
  /-- The `faceEquiv` declaration. -/
  faceEquiv : P.Face ≃ Q.Face
  /-- The `reverseFace` declaration. -/
  reverseFace : P.Face → Bool
  boundary_rotated :
    ∀ f, ((P.boundary f).map edgeRelabeling.mapDart).IsRotated
      (Q.orientedBoundary ⟨faceEquiv f, reverseFace f⟩)

namespace UnorientedPresentationIso

variable {P Q : FiniteCyclicPresentation}

/-- The `edgeEquiv` declaration. -/
abbrev edgeEquiv (e : UnorientedPresentationIso P Q) : P.Edge ≃ Q.Edge :=
  e.edgeRelabeling.edgeEquiv

/-- Ordinary signed presentation isomorphisms are the orientation-preserving special case. -/
def ofSignedPresentationIso (e : SignedPresentationIso P Q) :
    UnorientedPresentationIso P Q where
  edgeRelabeling := e.edgeRelabeling
  faceEquiv := e.faceEquiv
  reverseFace := fun _ ↦ false
  boundary_rotated := by
    intro f
    exact e.boundary_rotated f

/-- Corresponding stored boundaries have the same length. -/
theorem boundary_length_eq (e : UnorientedPresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  rw [← Q.orientedBoundary_length
    (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)]
  simpa only [List.length_map] using
    (e.boundary_rotated f).perm.length_eq

/-- Independent face reversal does not alter edge multiplicity in a corresponding face. -/
theorem faceEdgeMultiplicity_eq (e : UnorientedPresentationIso P Q)
    (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have horiented :=
    Q.orientedBoundary_edgeMultiplicity
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)
      (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count
          (e.edgeEquiv a) =
        Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
    rw [← horiented]
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count
          (e.edgeEquiv a) := by
      symm
      exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- Total edge multiplicities are invariant under an unoriented presentation isomorphism. -/
theorem edgeMultiplicity_eq (e : UnorientedPresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

theorem isBoundaryEdge_iff (e : UnorientedPresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Face adjacency is preserved when target faces may be read in either orientation. -/
theorem map_faceAdjacent (e : UnorientedPresentationIso P Q)
    {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply List.count_pos_iff.mp
    change 0 < Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a)
    rw [← e.faceEdgeMultiplicity_eq f a]
    exact List.count_pos_iff.mpr hfa
  · apply List.count_pos_iff.mp
    change 0 < Q.faceEdgeMultiplicity (e.faceEquiv g) (e.edgeEquiv a)
    rw [← e.faceEdgeMultiplicity_eq g a]
    exact List.count_pos_iff.mpr hga

/-- Face-incidence connectivity is preserved by an unoriented presentation isomorphism. -/
theorem isConnected (e : UnorientedPresentationIso P Q)
    (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped :=
    hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q))
      (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Looking up the reversed signed word reverses the finite index and flips the dart. -/
theorem inverseWord_get_rev {α : Type*}
    (word : List (SignedDart α)) (i : Fin word.length) :
    (inverseWord word).get
        ⟨i.val, by simpa only [inverseWord_length] using i.isLt⟩ =
      (word.get i.rev).flip := by
  simp [inverseWord]
  congr 2
  omega

/-- The target-boundary rotation selected for an unoriented presentation isomorphism. -/
noncomputable def faceRotation (e : UnorientedPresentationIso P Q) (f : P.Face) : ℕ :=
  Classical.choose (e.boundary_rotated f).symm

theorem rotate_target_orientedBoundary
    (e : UnorientedPresentationIso P Q) (f : P.Face) :
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).rotate
        (e.faceRotation f) =
      (P.boundary f).map e.edgeRelabeling.mapDart :=
  Classical.choose_spec (e.boundary_rotated f).symm

/-- The side index in the chosen orientation of the target face. -/
noncomputable def orientedSideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    Fin (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length := by
  have hpos : 0 <
      (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length := by
    rw [Q.orientedBoundary_length]
    exact List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  exact ⟨(i.val + e.faceRotation f) %
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length,
      Nat.mod_lt _ hpos⟩

/-- Convert an oriented target-side index to the stored boundary indexing. -/
noncomputable def sideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    Fin (Q.boundary (e.faceEquiv f)).length :=
  let j := (e.orientedSideIndex validQ f i).cast
    (Q.orientedBoundary_length
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))
  if e.reverseFace f then j.rev else j

/-- Reflection reverses the side parameter exactly when the target face is read backwards. -/
def sideParameter (e : UnorientedPresentationIso P Q)
    (f : P.Face) (t : unitInterval) : unitInterval :=
  if e.reverseFace f then unitInterval.symm t else t

@[simp]
theorem sideParameter_false (e : UnorientedPresentationIso P Q)
    (f : P.Face) (h : e.reverseFace f = false) (t : unitInterval) :
    e.sideParameter f t = t := by
  simp [sideParameter, h]

@[simp]
theorem sideParameter_true (e : UnorientedPresentationIso P Q)
    (f : P.Face) (h : e.reverseFace f = true) (t : unitInterval) :
    e.sideParameter f t = unitInterval.symm t := by
  simp [sideParameter, h]

@[simp]
theorem sideParameter_sideParameter
    (e : UnorientedPresentationIso P Q) (f : P.Face) (t : unitInterval) :
    e.sideParameter f (e.sideParameter f t) = t := by
  cases h : e.reverseFace f <;>
    simp [sideParameter, h, unitInterval.symm_symm]

/-- The rotated oriented target side carries the relabeled source dart. -/
theorem orientedBoundary_get_orientedSideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).get
        (e.orientedSideIndex validQ f i) =
      e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  let target :=
    Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩
  let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
  have hrot : target.rotate (e.faceRotation f) = mapped :=
    e.rotate_target_orientedBoundary f
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
  rw [← Option.some_inj, ← hpoint]
  simp [orientedSideIndex, target]

/-- The stored target occurrence carries the relabeled dart, flipped exactly when its face was
read backwards. -/
theorem boundary_get_sideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      if e.reverseFace f then
        (e.edgeRelabeling.mapDart ((P.boundary f).get i)).flip
      else
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  have horiented := e.orientedBoundary_get_orientedSideIndex validQ f i
  cases hreverse : e.reverseFace f
  · have hob : Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩ =
        Q.boundary (e.faceEquiv f) := by
      simp [orientedBoundary, hreverse]
    have hs : e.sideIndex validQ f i =
        (e.orientedSideIndex validQ f i).cast (congrArg List.length hob) := by
      simp [sideIndex, hreverse]
    rw [if_neg Bool.false_ne_true, hs]
    exact (List.get_of_eq hob _).symm.trans horiented
  · let target := inverseWord (Q.boundary (e.faceEquiv f))
    let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
    have hrot : target.rotate (e.faceRotation f) = mapped := by
      simpa only [target, mapped, hreverse, orientedBoundary, if_true] using
        e.rotate_target_orientedBoundary f
    have hlen : target.length = mapped.length := by
      rw [← hrot, List.length_rotate]
    have hiTarget : i.val < target.length := by
      rw [hlen]
      simpa only [mapped, List.length_map] using i.isLt
    let jTarget : Fin target.length :=
      ⟨(i.val + e.faceRotation f) % target.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt hiTarget)⟩
    have hpoint :
        (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
      congrArg (fun word => word[i.val]?) hrot
    rw [List.getElem?_rotate hiTarget] at hpoint
    have horiented' :
        target.get jTarget =
          e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
      have htargetSome :
          target[jTarget.val]? = some (target.get jTarget) := by
        simp [jTarget.isLt]
      have hmappedSome :
          mapped[i.val]? =
            some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
        simp [mapped, i.isLt]
      rw [hmappedSome] at hpoint
      exact Option.some.inj (htargetSome.symm.trans hpoint)
    let j : Fin (Q.boundary (e.faceEquiv f)).length :=
      jTarget.cast (by simp only [target, inverseWord_length])
    have hinverse :=
      inverseWord_get_rev (Q.boundary (e.faceEquiv f)) j
    have hindex :
        (⟨j.val, by simpa only [inverseWord_length] using j.isLt⟩ :
            Fin (inverseWord (Q.boundary (e.faceEquiv f))).length) =
          jTarget := by
      apply Fin.ext
      rfl
    rw [hindex] at hinverse
    have hflipped :=
      congrArg SignedDart.flip (hinverse.symm.trans horiented')
    have hside : e.sideIndex validQ f i = j.rev := by
      apply Fin.ext
      simp [sideIndex, orientedSideIndex, hreverse, j, jTarget, target]
    rw [hside]
    simpa using hflipped

/-- The facewise disk homeomorphism: rotate to the selected cyclic spelling, then reflect if the
target face is read backwards. -/
noncomputable def faceHomeomorph
    (e : UnorientedPresentationIso P Q) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell (Q.boundary (e.faceEquiv f)).length :=
  let rotation :=
    PolygonCell.rotateHomeomorph (e.boundary_length_eq f) (e.faceRotation f)
  if e.reverseFace f then
    rotation.trans
      (PolygonCell.reflectionHomeomorph
        (Q.boundary (e.faceEquiv f)).length)
  else
    rotation

/-- The facewise homeomorphism sends a source side to the corresponding stored target side, with
the interval parameter reversed exactly for a reversed face. -/
theorem faceHomeomorph_side
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) (t : unitInterval) :
    e.faceHomeomorph f (PolygonCell.side i t) =
      PolygonCell.side (e.sideIndex validQ f i) (e.sideParameter f t) := by
  cases hreverse : e.reverseFace f
  · simp only [faceHomeomorph, hreverse, Bool.false_eq_true, ↓reduceIte,
      sideIndex, sideParameter]
    have hindex :
        (e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
          (⟨(i.val + e.faceRotation f) %
              (Q.boundary (e.faceEquiv f)).length,
            Nat.mod_lt _
              (List.length_pos_of_ne_nil
                (validQ.2.1 (e.faceEquiv f)))⟩ :
            Fin (Q.boundary (e.faceEquiv f)).length) := by
      apply Fin.ext
      simp [orientedSideIndex, hreverse, orientedBoundary] <;> rfl
    rw [hindex]
    exact PolygonCell.rotateHomeomorph_side_of_eq
      (e.boundary_length_eq f)
      (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
      (e.faceRotation f) i t
  · simp only [faceHomeomorph, hreverse, ↓reduceIte, Homeomorph.trans_apply,
      sideIndex, sideParameter]
    have hindex :
        (e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
          (⟨(i.val + e.faceRotation f) %
              (Q.boundary (e.faceEquiv f)).length,
            Nat.mod_lt _
              (List.length_pos_of_ne_nil
                (validQ.2.1 (e.faceEquiv f)))⟩ :
            Fin (Q.boundary (e.faceEquiv f)).length) := by
      apply Fin.ext
      simp [orientedSideIndex, hreverse, orientedBoundary] <;> rfl
    rw [hindex]
    rw [PolygonCell.rotateHomeomorph_side_of_eq
      (e.boundary_length_eq f)
      (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
      (e.faceRotation f) i t]
    exact PolygonCell.reflectionHomeomorph_side _ _

/-- A facewise homeomorphism of polygonal pre-realizations. -/
noncomputable def preHomeomorph (e : UnorientedPresentationIso P Q) :
    P.PolygonalPreRealization ≃ₜ Q.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap e.faceEquiv.bijective
      (fun f => (e.faceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map e.faceEquiv fun f => e.faceHomeomorph f)

@[simp]
theorem preHomeomorph_apply_fst (e : UnorientedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).1 = e.faceEquiv x.1 :=
  rfl

@[simp]
theorem preHomeomorph_apply_snd (e : UnorientedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).2 = e.faceHomeomorph x.1 x.2 :=
  rfl

/-- Transport a boundary occurrence through the selected cyclic rotation and possible
reflection. -/
noncomputable def mapOccurrence
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence → Q.BoundaryOccurrence
  | ⟨f, i⟩ => ⟨e.faceEquiv f, e.sideIndex validQ f i⟩

@[simp]
theorem mapOccurrence_fst
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).1 = e.faceEquiv o.1 := by
  cases o
  rfl

@[simp]
theorem mapOccurrence_dart
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).dart =
      if e.reverseFace o.1 then
        (e.edgeRelabeling.mapDart o.dart).flip
      else
        e.edgeRelabeling.mapDart o.dart := by
  rcases o with ⟨f, i⟩
  exact e.boundary_get_sideIndex validQ f i

/-- On a labelled side, the pre-realization map performs its selected cyclic shift and possible
reflection. -/
theorem preHomeomorph_occurrenceSide_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph ((P.occurrenceSide o).point t) =
      (Q.occurrenceSide (e.mapOccurrence validQ o)).point
        (e.sideParameter o.1 t) := by
  rcases o with ⟨f, i⟩
  apply Sigma.ext
  · rfl
  · simp only [preHomeomorph_apply_snd, PolygonGluing.Side.point]
    apply heq_of_eq
    exact e.faceHomeomorph_side validQ f i t

/-- Cyclic shift followed by an optional finite-index reversal is injective. -/
private theorem sideIndex_injective
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) :
    Function.Injective (e.sideIndex validQ f) := by
  have horiented :
      Function.Injective (e.orientedSideIndex validQ f) := by
    intro i j hij
    let target :=
      Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩
    have hlen : (P.boundary f).length = target.length := by
      simpa only [target, Q.orientedBoundary_length] using e.boundary_length_eq f
    have hmod :
        i.val + e.faceRotation f ≡ j.val + e.faceRotation f
          [MOD target.length] := by
      exact congrArg Fin.val hij
    have hcancel :
        i.val ≡ j.val [MOD target.length] :=
      Nat.ModEq.add_right_cancel' (e.faceRotation f) hmod
    apply Fin.ext
    unfold Nat.ModEq at hcancel
    rw [← hlen, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] at hcancel
    exact hcancel
  intro i j hij
  apply horiented
  have hcast :
      (e.orientedSideIndex validQ f i).cast
          (Q.orientedBoundary_length
            (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
        (e.orientedSideIndex validQ f j).cast
          (Q.orientedBoundary_length
            (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) := by
    by_cases hreverse : e.reverseFace f = true
    · have hrev :
        ((e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))).rev =
          ((e.orientedSideIndex validQ f j).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))).rev := by
        simpa only [sideIndex, if_pos hreverse] using hij
      exact Fin.rev_injective hrev
    · simpa only [sideIndex, if_neg hreverse] using hij
  exact Fin.cast_injective
    (Q.orientedBoundary_length
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) hcast

/-- Transport of all boundary occurrences is injective. -/
theorem mapOccurrence_injective
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
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
theorem mapOccurrence_edge
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).edge = e.edgeEquiv o.edge := by
  change edgeOfDart (e.mapOccurrence validQ o).dart =
    e.edgeEquiv (edgeOfDart o.dart)
  rw [e.mapOccurrence_dart]
  cases e.reverseFace o.1 <;>
    simp [EdgeRelabeling.edgeOfDart_mapDart, edgeOfDart_flip]

/-- Ignoring the selected cyclic shifts and reflections, the occurrence types have equal
cardinality. -/
noncomputable def rawOccurrenceEquiv (e : UnorientedPresentationIso P Q) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.sigmaCongr e.faceEquiv fun f =>
    (Fin.castOrderIso (e.boundary_length_eq f)).toEquiv

/-- Boundary-occurrence transport bundled as an equivalence. -/
noncomputable def occurrenceEquiv
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.ofBijective (e.mapOccurrence validQ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨e.mapOccurrence_injective validQ,
        Fintype.card_congr e.rawOccurrenceEquiv⟩)

@[simp]
theorem occurrenceEquiv_apply
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    e.occurrenceEquiv validQ o = e.mapOccurrence validQ o :=
  rfl

@[simp]
theorem mapOccurrence_occurrenceEquiv_symm
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.mapOccurrence validQ ((e.occurrenceEquiv validQ).symm o) = o :=
  (e.occurrenceEquiv validQ).apply_symm_apply o

/-- Toggle a gluing direction when exactly one incident face is reflected. -/
def transportDirection (sourceReverse targetReverse : Bool) :
    PolygonGluing.ParameterDirection → PolygonGluing.ParameterDirection
  | .same =>
      if sourceReverse = targetReverse then .same else .opposite
  | .opposite =>
      if sourceReverse = targetReverse then .opposite else .same

/-- The transported gluing parameter commutes with the two optional side reflections. -/
theorem transportDirection_parameter
    (sourceReverse targetReverse : Bool)
    (direction : PolygonGluing.ParameterDirection) (t : unitInterval) :
    (transportDirection sourceReverse targetReverse direction).homeomorph
        (if sourceReverse then unitInterval.symm t else t) =
      if targetReverse then
        unitInterval.symm (direction.homeomorph t)
      else
        direction.homeomorph t := by
  cases sourceReverse <;> cases targetReverse <;> cases direction <;>
    simp [transportDirection, PolygonGluing.ParameterDirection.homeomorph_opposite_apply,
      unitInterval.symm_symm]

/-- Transport a compatible source pairing, toggling its parameter direction precisely when one
of the two incident faces is reflected. -/
noncomputable def mapPairing
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) : Q.BoundaryPairing where
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
  direction := transportDirection
    (e.reverseFace pairing.source.1)
    (e.reverseFace pairing.target.1)
    pairing.direction
  compatible := by
    rw [e.mapOccurrence_dart, e.mapOccurrence_dart]
    cases hs : e.reverseFace pairing.source.1 <;>
      cases ht : e.reverseFace pairing.target.1 <;>
        cases hd : pairing.direction
    all_goals
      have hcompatible := pairing.compatible
      simp only [hd] at hcompatible
      simp only [↓reduceIte, transportDirection,
        Bool.false_eq_true, Bool.true_eq_false,
        SignedDart.flip_flip]
      first
      | simpa only [EdgeRelabeling.mapDart_flip,
          SignedDart.flip_flip] using
          congrArg e.edgeRelabeling.mapDart hcompatible
      | simpa only [EdgeRelabeling.mapDart_flip,
          SignedDart.flip_flip] using
          congrArg SignedDart.flip
            (congrArg e.edgeRelabeling.mapDart hcompatible)

@[simp]
theorem mapPairing_source
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).source =
      e.mapOccurrence validQ pairing.source :=
  rfl

@[simp]
theorem mapPairing_target
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).target =
      e.mapOccurrence validQ pairing.target :=
  rfl

@[simp]
theorem mapPairing_direction
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).direction =
      transportDirection
        (e.reverseFace pairing.source.1)
        (e.reverseFace pairing.target.1)
        pairing.direction :=
  rfl

/-- The pre-realization map sends a pairing source point to its transported source side. -/
theorem preHomeomorph_pairing_source_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.source.point t) =
      (e.mapPairing validQ pairing).identification.source.point
        (e.sideParameter pairing.source.1 t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.source t

/-- The pre-realization map sends a pairing target point to its transported target side. -/
theorem preHomeomorph_pairing_target_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.target.point t) =
      (e.mapPairing validQ pairing).identification.target.point
        (e.sideParameter pairing.target.1 t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.target t

/-- Transported side parameters intertwine the source and target pairing maps. -/
theorem mapPairing_parameter_sideParameter
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    (e.mapPairing validQ pairing).identification.parameter
        (e.sideParameter pairing.source.1 t) =
      e.sideParameter pairing.target.1
        (pairing.identification.parameter t) := by
  exact transportDirection_parameter
    (e.reverseFace pairing.source.1)
    (e.reverseFace pairing.target.1)
    pairing.direction t

/-- The facewise homeomorphism sends every source generator into the target generated
relation. -/
theorem preHomeomorph_generator_related
    (e : UnorientedPresentationIso P Q) (_validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    Q.PolygonalGluingRel validQ
      (e.preHomeomorph (pairing.identification.source.point t))
      (e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_pairing_source_point,
    e.preHomeomorph_pairing_target_point,
    ← e.mapPairing_parameter_sideParameter]
  exact PolygonGluing.related_of_mem
    (e.mapPairing validQ pairing).identification
    (pairing_identification_mem validQ (e.mapPairing validQ pairing))
    (e.sideParameter pairing.source.1 t)

/-- The facewise homeomorphism preserves the generated gluing relation. -/
theorem preHomeomorph_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
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

/-- The inverse pre-realization homeomorphism uses the same involutive side-parameter
reflection. -/
theorem preHomeomorph_symm_occurrenceSide_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph.symm ((Q.occurrenceSide o).point t) =
      (P.occurrenceSide ((e.occurrenceEquiv validQ).symm o)).point
        (e.sideParameter ((e.occurrenceEquiv validQ).symm o).1 t) := by
  apply e.preHomeomorph.injective
  rw [e.preHomeomorph.apply_symm_apply]
  rw [e.preHomeomorph_occurrenceSide_point validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]
  rw [e.sideParameter_sideParameter]

/-- The relabeled dart of a pulled-back occurrence is the target dart, flipped exactly when its
source face was reflected. -/
theorem occurrenceEquiv_symm_mapDart
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeRelabeling.mapDart ((e.occurrenceEquiv validQ).symm o).dart =
      if e.reverseFace ((e.occurrenceEquiv validQ).symm o).1 then
        o.dart.flip
      else
        o.dart := by
  let p := (e.occurrenceEquiv validQ).symm o
  have hdart := e.mapOccurrence_dart validQ p
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ] at hdart
  cases hreverse : e.reverseFace p.1
  · simpa [p, hreverse] using hdart.symm
  · have hflipped := congrArg SignedDart.flip hdart.symm
    simpa [p, hreverse] using hflipped

/-- The relabeled edge of a pulled-back occurrence is its target edge. -/
theorem occurrenceEquiv_symm_edge
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeEquiv ((e.occurrenceEquiv validQ).symm o).edge = o.edge := by
  rw [← e.mapOccurrence_edge validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/-- Pull a compatible target pairing back through the occurrence equivalence. -/
noncomputable def comapPairing
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) : P.BoundaryPairing where
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
  direction := transportDirection
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
    pairing.direction
  compatible := by
    let source := (e.occurrenceEquiv validQ).symm pairing.source
    let target := (e.occurrenceEquiv validQ).symm pairing.target
    have hsource := e.occurrenceEquiv_symm_mapDart validQ pairing.source
    have htarget := e.occurrenceEquiv_symm_mapDart validQ pairing.target
    change
      e.edgeRelabeling.mapDart source.dart =
        if e.reverseFace source.1 then pairing.source.dart.flip
        else pairing.source.dart at hsource
    change
      e.edgeRelabeling.mapDart target.dart =
        if e.reverseFace target.1 then pairing.target.dart.flip
        else pairing.target.dart at htarget
    change
      match transportDirection
          (e.reverseFace source.1) (e.reverseFace target.1)
          pairing.direction with
        | .same => target.dart = source.dart
        | .opposite => target.dart = source.dart.flip
    cases hs : e.reverseFace source.1 <;>
      cases ht : e.reverseFace target.1 <;>
        cases hd : pairing.direction
    all_goals
      apply e.edgeRelabeling.dartEquiv.injective
      simp only [EdgeRelabeling.dartEquiv_apply,
        EdgeRelabeling.mapDart_flip]
      have hcompatible := pairing.compatible
      simp only [hd] at hcompatible
      simp only [hs, ht, Bool.false_eq_true,
        ↓reduceIte] at hsource htarget
      first
      | simpa only [hsource, htarget,
          Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, SignedDart.flip_flip] using hcompatible
      | simpa only [hsource, htarget,
          Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, SignedDart.flip_flip] using
          congrArg SignedDart.flip hcompatible

@[simp]
theorem comapPairing_source
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).source =
      (e.occurrenceEquiv validQ).symm pairing.source :=
  rfl

@[simp]
theorem comapPairing_target
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).target =
      (e.occurrenceEquiv validQ).symm pairing.target :=
  rfl

@[simp]
theorem comapPairing_direction
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).direction =
      transportDirection
        (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
        (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
        pairing.direction :=
  rfl

/-- The inverse pre-realization map sends a target pairing source to its pulled-back side. -/
theorem preHomeomorph_symm_pairing_source_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.source.point t) =
      (e.comapPairing validQ pairing).identification.source.point
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.source).1 t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.source t

/-- The inverse pre-realization map sends a target pairing target to its pulled-back side. -/
theorem preHomeomorph_symm_pairing_target_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.target.point t) =
      (e.comapPairing validQ pairing).identification.target.point
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.target).1 t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.target t

/-- Pulled-back gluing parameters commute with the two side reflections. -/
theorem comapPairing_parameter_sideParameter
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    (e.comapPairing validQ pairing).identification.parameter
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.source).1 t) =
      e.sideParameter
        ((e.occurrenceEquiv validQ).symm pairing.target).1
        (pairing.identification.parameter t) := by
  exact transportDirection_parameter
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
    pairing.direction t

/-- The inverse facewise homeomorphism sends every target generator into the source generated
relation. -/
theorem preHomeomorph_symm_generator_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm (pairing.identification.source.point t))
      (e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_symm_pairing_source_point,
    e.preHomeomorph_symm_pairing_target_point,
    ← e.comapPairing_parameter_sideParameter]
  exact PolygonGluing.related_of_mem
    (e.comapPairing validQ pairing).identification
    (pairing_identification_mem validP (e.comapPairing validQ pairing))
    (e.sideParameter
      ((e.occurrenceEquiv validQ).symm pairing.source).1 t)

/-- The inverse facewise homeomorphism preserves the generated gluing relation. -/
theorem preHomeomorph_symm_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : Q.PolygonalPreRealization}
    (hxy : Q.PolygonalGluingRel validQ x y) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm x) (e.preHomeomorph.symm y) := by
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

/-- The facewise homeomorphism identifies the two generated gluing relations. -/
theorem preHomeomorph_related_iff
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  constructor
  · exact e.preHomeomorph_related validP validQ
  · intro hxy
    simpa only [e.preHomeomorph.symm_apply_apply] using
      e.preHomeomorph_symm_related validP validQ hxy

/-- Independent edge and face reorientation preserves the faithful polygonal realization whenever
both endpoint presentations satisfy ordinary incidence validity. -/
noncomputable def realizationHomeomorph
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ :=
  PolygonGluing.realizationCongr e.preHomeomorph
    (e.preHomeomorph_related_iff validP validQ)

/-- Propositional realization-invariance form for face-reversing presentation comparisons. -/
theorem polygonallyEquivalent
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  ⟨e.realizationHomeomorph validP validQ⟩

end UnorientedPresentationIso

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification22_block_02
/- END ClassificationOfSurfaces.FiniteCyclicUnorientedRealization -/

/- BEGIN ClassificationOfSurfaces.SphereQuotientHomeomorph | a29e974f0b74a500b2ebb57432bf25224eb93986e76619865243316bcbd3c8f5 -/
section schottkyclassification22_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The two-monogon quotient is the standard sphere

The facewise hemisphere map from `SphereHemisphere` respects the equivalence relation generated
by the sphere's side pairing, so it descends to the polygonal realization.  This file proves that
the descended map is bijective and hence, by compactness of the source and the Hausdorff property
of the target, a homeomorphism with `SphereRepresentative`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- The upper hemisphere parameterization remembers its disk point. -/
theorem upperHemisphere_injective : Function.Injective upperHemisphere := by
  intro z w hzw
  apply PolygonCell.ext
  apply Complex.ext
  · simpa [upperHemisphere, upperHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
  · simpa [upperHemisphere, upperHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw

/-- The lower hemisphere parameterization remembers its disk point. -/
theorem lowerHemisphere_injective : Function.Injective lowerHemisphere := by
  intro z w hzw
  apply PolygonCell.ext
  have hconj : conj z.val = conj w.val := by
    apply Complex.ext
    · simpa [lowerHemisphere, lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
    · simpa [lowerHemisphere, lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw
  simpa using congrArg conj hconj

/-- Zero hemisphere height means that the disk point lies on its boundary circle. -/
theorem mem_sphere_of_hemisphereHeight_eq_zero {n : ℕ} (z : PolygonCell n)
    (hz : hemisphereHeight z = 0) :
    z.val ∈ Metric.sphere 0 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hsquare := hemisphereHeight_sq z
  norm_num [hz, Complex.normSq_eq_norm_sq] at hsquare
  nlinarith [norm_nonneg z.val]

/-- The horizontal coordinates of a point on the standard sphere, regarded as a disk point. -/
noncomputable def sphereDiskPoint (x : SphereRepresentative) : PolygonCell 1 :=
  ⟨Complex.mk (x.val 0) (x.val 1), by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := mem_sphere_zero_iff_norm.mp x.property
    have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
    rw [EuclideanSpace.real_norm_sq_eq] at hsquare
    have hsum : x.val 0 ^ 2 + x.val 1 ^ 2 + x.val 2 ^ 2 = 1 := by
      simp [Fin.sum_univ_succ] at hsquare
      nlinarith
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num)]
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith [sq_nonneg (x.val 2)]⟩

@[simp]
theorem sphereDiskPoint_re (x : SphereRepresentative) :
    (sphereDiskPoint x).val.re = x.val 0 :=
  rfl

@[simp]
theorem sphereDiskPoint_im (x : SphereRepresentative) :
    (sphereDiskPoint x).val.im = x.val 1 :=
  rfl

/-- The height recovered from the horizontal coordinates is the absolute vertical coordinate. -/
@[simp]
theorem hemisphereHeight_sphereDiskPoint (x : SphereRepresentative) :
    hemisphereHeight (sphereDiskPoint x) = |x.val 2| := by
  unfold hemisphereHeight
  have hnorm := mem_sphere_zero_iff_norm.mp x.property
  have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
  rw [EuclideanSpace.real_norm_sq_eq] at hsquare
  have hsum : x.val 0 ^ 2 + x.val 1 ^ 2 + x.val 2 ^ 2 = 1 := by
    simp [Fin.sum_univ_succ] at hsquare
    nlinarith
  rw [show 1 - Complex.normSq (sphereDiskPoint x).val = x.val 2 ^ 2 by
    rw [Complex.normSq_apply]
    simp only [sphereDiskPoint_re, sphereDiskPoint_im]
    nlinarith]
  exact Real.sqrt_sq_eq_abs _

/-- Complex conjugation does not change the height assigned to a disk point. -/
@[simp]
theorem hemisphereHeight_conjHomeomorph {n : ℕ} (z : PolygonCell n) :
    hemisphereHeight (conjHomeomorph n z) = hemisphereHeight z := by
  simp [hemisphereHeight, Complex.normSq_conj]

/-- A sphere point with nonnegative vertical coordinate is hit by the upper hemisphere. -/
theorem upperHemisphere_sphereDiskPoint (x : SphereRepresentative) (hx : 0 ≤ x.val 2) :
    upperHemisphere (sphereDiskPoint x) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [upperHemisphere, upperHemisphereVector, abs_of_nonneg hx]

/-- A sphere point with nonpositive vertical coordinate is hit by the conjugated lower face. -/
theorem lowerHemisphere_conj_sphereDiskPoint (x : SphereRepresentative) (hx : x.val 2 ≤ 0) :
    lowerHemisphere (conjHomeomorph 1 (sphereDiskPoint x)) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [lowerHemisphere, lowerHemisphereVector, abs_of_nonpos hx]

end PolygonCell

namespace SurfaceCellComplex

/-- The sphere pre-map is constant on the equivalence relation generated by the side pairing. -/
theorem spherePreMap_eq_of_gluingRel
    {x y : sphere.PolygonalPreRealization}
    (hxy : sphere.PolygonalGluingRel sphere_occurrencePairingValid x y) :
    spherePreMap x = spherePreMap y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (sphere.polygonalIdentifications sphere_occurrencePairingValid)) x y at hxy
  induction hxy with
  | rel _ _ h => exact spherePreMap_eq_of_generator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- The continuous sphere map descended from the two monogon faces to their polygonal quotient. -/
noncomputable def sphereQuotientMap :
    C(sphere.PolygonalRealization sphere_occurrencePairingValid, SphereRepresentative) where
  toFun := Quotient.lift spherePreMap fun _ _ hxy ↦ spherePreMap_eq_of_gluingRel hxy
  continuous_toFun :=
    spherePreMap.continuous.quotient_lift fun _ _ hxy ↦ spherePreMap_eq_of_gluingRel hxy

@[simp]
theorem sphereQuotientMap_polygonalMk (x : sphere.PolygonalPreRealization) :
    sphereQuotientMap (sphere.polygonalMk sphere_occurrencePairingValid x) = spherePreMap x :=
  rfl

/-- Equality between an upper- and a lower-hemisphere image is exactly an equatorial gluing. -/
theorem sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere
    (z w : PolygonCell 1)
    (hzw : PolygonCell.upperHemisphere z = PolygonCell.lowerHemisphere w) :
    sphere.PolygonalGluingRel sphere_occurrencePairingValid
      ⟨false, z⟩ ⟨true, w⟩ := by
  have hheight :
      PolygonCell.hemisphereHeight z = -PolygonCell.hemisphereHeight w := by
    simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
      PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 2) hzw
  have hzheight : PolygonCell.hemisphereHeight z = 0 := by
    nlinarith [PolygonCell.hemisphereHeight_nonneg z,
      PolygonCell.hemisphereHeight_nonneg w]
  obtain ⟨i, t, hit⟩ :=
    PolygonCell.exists_side_eq_of_mem_sphere (n := 1) (by decide) z
      (PolygonCell.mem_sphere_of_hemisphereHeight_eq_zero z hzheight)
  have hi : i = 0 := Fin.eq_zero i
  subst i
  have hcomplex :
      (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val = conj w.val := by
    rw [hit]
    apply Complex.ext
    · simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
        PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
    · simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
        PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw
  have hw :
      w = PolygonCell.side (0 : Fin 1) (unitInterval.symm t) := by
    apply PolygonCell.ext
    have hconj := congrArg conj hcomplex
    rw [Complex.conj_conj] at hconj
    have hside :
        conj ((PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val) =
          (PolygonCell.side (0 : Fin 1) (unitInterval.symm t) : PolygonCell 1).val := by
      simpa only [unitInterval.symm_symm] using
        PolygonCell.conj_side_symm_monogon (unitInterval.symm t)
    exact hconj.symm.trans hside
  rw [← hit, hw]
  exact PolygonGluing.related_of_mem sphereBoundaryPairing.identification
    sphereBoundaryPairing_mem t

/-- Equal images under the facewise map are related by the generated sphere gluing relation. -/
theorem sphereGluingRel_of_spherePreMap_eq
    {x y : sphere.PolygonalPreRealization}
    (hxy : spherePreMap x = spherePreMap y) :
    sphere.PolygonalGluingRel sphere_occurrencePairingValid x y := by
  rcases x with ⟨face, z⟩
  rcases y with ⟨face', w⟩
  cases face <;> cases face'
  · have hzw : z = w := PolygonCell.upperHemisphere_injective hxy
    subst w
    exact Relation.EqvGen.refl _
  · exact sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere z w hxy
  · exact Relation.EqvGen.symm _ _
      (sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere w z hxy.symm)
  · have hzw : z = w := PolygonCell.lowerHemisphere_injective hxy
    subst w
    exact Relation.EqvGen.refl _

/-- The generated sphere gluing relation is precisely the kernel relation of the pre-map. -/
theorem spherePreMap_eq_iff_gluingRel
    {x y : sphere.PolygonalPreRealization} :
    spherePreMap x = spherePreMap y ↔
      sphere.PolygonalGluingRel sphere_occurrencePairingValid x y :=
  ⟨sphereGluingRel_of_spherePreMap_eq, spherePreMap_eq_of_gluingRel⟩

/-- The descended sphere map is injective. -/
theorem sphereQuotientMap_injective : Function.Injective sphereQuotientMap := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          apply Quotient.sound
          apply sphereGluingRel_of_spherePreMap_eq
          change spherePreMap x = spherePreMap y at hqr
          exact hqr

/-- Every point of the standard sphere is hit by the descended two-monogon map. -/
theorem sphereQuotientMap_surjective : Function.Surjective sphereQuotientMap := by
  intro x
  by_cases hx : 0 ≤ x.val 2
  · refine ⟨sphere.polygonalMk sphere_occurrencePairingValid
        ⟨false, PolygonCell.sphereDiskPoint x⟩, ?_⟩
    change PolygonCell.upperHemisphere (PolygonCell.sphereDiskPoint x) = x
    exact PolygonCell.upperHemisphere_sphereDiskPoint x hx
  · have hx' : x.val 2 ≤ 0 := le_of_not_ge hx
    refine ⟨sphere.polygonalMk sphere_occurrencePairingValid
        ⟨true, PolygonCell.conjHomeomorph 1 (PolygonCell.sphereDiskPoint x)⟩, ?_⟩
    change
      PolygonCell.lowerHemisphere
        (PolygonCell.conjHomeomorph 1 (PolygonCell.sphereDiskPoint x)) = x
    exact PolygonCell.lowerHemisphere_conj_sphereDiskPoint x hx'

/-- The descended sphere map is bijective. -/
theorem sphereQuotientMap_bijective : Function.Bijective sphereQuotientMap :=
  ⟨sphereQuotientMap_injective, sphereQuotientMap_surjective⟩

/-- The underlying equivalence of the two-monogon quotient with the standard sphere. -/
noncomputable def spherePolygonalRealizationEquiv :
    sphere.PolygonalRealization sphere_occurrencePairingValid ≃ SphereRepresentative :=
  Equiv.ofBijective sphereQuotientMap sphereQuotientMap_bijective

@[simp]
theorem spherePolygonalRealizationEquiv_apply
    (q : sphere.PolygonalRealization sphere_occurrencePairingValid) :
    spherePolygonalRealizationEquiv q = sphereQuotientMap q :=
  rfl

/-- The polygonal realization of the two-monogon presentation is the standard two-sphere. -/
noncomputable def spherePolygonalRealizationHomeomorph :
    sphere.PolygonalRealization sphere_occurrencePairingValid ≃ₜ SphereRepresentative :=
  Continuous.homeoOfEquivCompactToT2
    (f := spherePolygonalRealizationEquiv) sphereQuotientMap.continuous

@[simp]
theorem spherePolygonalRealizationHomeomorph_apply
    (q : sphere.PolygonalRealization sphere_occurrencePairingValid) :
    spherePolygonalRealizationHomeomorph q = sphereQuotientMap q :=
  rfl

@[simp]
theorem spherePolygonalRealizationHomeomorph_polygonalMk
    (x : sphere.PolygonalPreRealization) :
    spherePolygonalRealizationHomeomorph
        (sphere.polygonalMk sphere_occurrencePairingValid x) =
      spherePreMap x :=
  rfl

end SurfaceCellComplex

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification22_block_03
/- END ClassificationOfSurfaces.SphereQuotientHomeomorph -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicCanonicalRealization | fe881e86366e497584c28504386d95624b7c7d7697c88768cc0f87821acc7f6e -/
section schottkyclassification22_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Realization of canonical finite-cyclic presentations

`FiniteCyclicPresentation.ofOneFaceWord` enumerates the edge names of an existing typed
one-face word.  This file proves that the enumeration does not change the faithful polygonal
quotient.  The result is the only adapter between the finite-cyclic normalization target and the
already-certified canonical polygonal quotients; in particular, it does not restate either
Lean-Eval relation.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open SurfaceCellComplex

namespace FiniteCyclicPresentation

variable {Edge : Type} [Fintype Edge]

theorem ofOneFaceWord_boundary_length
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    ((ofOneFaceWord word).boundary f).length = word.length := by
  rw [ofOneFaceWord_boundary]
  simp

/-- The unique enumerated face is equivalent to the unique typed one-face face. -/
noncomputable def ofOneFaceWordFaceEquiv (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).Face ≃ PUnit where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ 0
  left_inv := fun f ↦ (ofOneFaceWord_face_eq_zero word f).symm
  right_inv := by
    intro f
    cases f
    rfl

/-- The face disk of the enumerated word, with its phantom side count cast back to the original
word length. -/
noncomputable def ofOneFaceWordFaceHomeomorph
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    PolygonCell ((ofOneFaceWord word).boundary f).length ≃ₜ
      PolygonCell word.length :=
  PolygonCell.rotateHomeomorph (ofOneFaceWord_boundary_length word f) 0

/-- Enumerating the edge names and the unique face leaves the polygonal pre-realization
homeomorphic to the original typed one-face pre-realization. -/
noncomputable def ofOneFaceWordPreHomeomorph
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).PolygonalPreRealization ≃ₜ
      (oneFacePresentation Edge word).PolygonalPreRealization :=
  letI : ∀ f : PUnit,
      TopologicalSpace
        (PolygonCell ((oneFacePresentation Edge word).faceBoundaryLength f)) :=
    fun _ => inferInstance
  (IsHomeomorph.sigmaMap (ofOneFaceWordFaceEquiv word).bijective
      (fun f => (ofOneFaceWordFaceHomeomorph word f).isHomeomorph)).homeomorph
    (Sigma.map (ofOneFaceWordFaceEquiv word)
      fun f => ofOneFaceWordFaceHomeomorph word f)

@[simp]
theorem ofOneFaceWordPreHomeomorph_apply_fst
    (word : List (SignedDart Edge))
    (x : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWordPreHomeomorph word x).1 = PUnit.unit :=
  rfl

@[simp]
theorem ofOneFaceWordPreHomeomorph_apply_snd
    (word : List (SignedDart Edge))
    (x : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWordPreHomeomorph word x).2 =
      ofOneFaceWordFaceHomeomorph word x.1 x.2 :=
  rfl

/-- A boundary position of the enumerated word, read as the same position of the original typed
word. -/
noncomputable def ofOneFaceWordMapOccurrence
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).BoundaryOccurrence →
      (oneFacePresentation Edge word).BoundaryOccurrence
  | ⟨f, i⟩ =>
      ⟨PUnit.unit, Fin.cast (ofOneFaceWord_boundary_length word f) i⟩

@[simp]
theorem ofOneFaceWordMapOccurrence_fst
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    (ofOneFaceWordMapOccurrence word o).1 = PUnit.unit :=
  rfl

@[simp]
theorem ofOneFaceWordMapOccurrence_snd_val
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    (ofOneFaceWordMapOccurrence word o).2.val = o.2.val :=
  rfl

/-- The pre-realization homeomorphism is parameter-exact on every labelled side. -/
theorem ofOneFaceWordPreHomeomorph_occurrenceSide_point
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (((ofOneFaceWord word).occurrenceSide o).point t) =
      ((oneFacePresentation Edge word).occurrenceSide
        (ofOneFaceWordMapOccurrence word o)).point t := by
  rcases o with ⟨f, i⟩
  change
    ofOneFaceWordPreHomeomorph word
        ⟨f, PolygonCell.side i t⟩ =
      ⟨PUnit.unit,
        PolygonCell.side
          (Fin.cast (ofOneFaceWord_boundary_length word f) i) t⟩
  apply Sigma.ext
  · rfl
  · simp only [ofOneFaceWordPreHomeomorph_apply_snd,
      ofOneFaceWordFaceHomeomorph]
    apply heq_of_eq
    rw [PolygonCell.rotateHomeomorph_side_of_eq
      (ofOneFaceWord_boundary_length word f)
      (by
        rw [← ofOneFaceWord_boundary_length word f]
        exact Nat.zero_lt_of_lt i.isLt)
      0 i t]
    congr 2
    apply Fin.ext
    simp only [Nat.add_zero, Fin.cast]
    exact Nat.mod_eq_of_lt (by
      simpa only [ofOneFaceWord_boundary_length] using i.isLt)

/-- Relabeling the original dart at a mapped position recovers the enumerated dart exactly. -/
theorem ofOneFaceWordMapOccurrence_dart
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    SignedDart.mapEquiv (Fintype.equivFin Edge)
        ((oneFacePresentation Edge word).occurrenceDart
          (ofOneFaceWordMapOccurrence word o)) =
      o.dart := by
  rcases o with ⟨f, i⟩
  have hf : f = 0 := ofOneFaceWord_face_eq_zero word f
  subst f
  simp only [BoundaryOccurrence.dart_mk, List.get_eq_getElem,
    ofOneFaceWord_boundary, List.getElem_map,
    EmbeddingLike.apply_eq_iff_eq]
  exact congrArg (SignedDart.mapEquiv (Fintype.equivFin Edge)) rfl

/-- The inverse occurrence transport, from the typed one-face word to its enumeration. -/
noncomputable def ofOneFaceWordComapOccurrence
    (word : List (SignedDart Edge)) :
    (oneFacePresentation Edge word).BoundaryOccurrence →
      (ofOneFaceWord word).BoundaryOccurrence
  | ⟨f, i⟩ =>
      ⟨0, Fin.cast
        (ofOneFaceWord_boundary_length word 0).symm
        (by
          cases f
          exact i)⟩

/-- Boundary positions are unchanged by enumeration. -/
noncomputable def ofOneFaceWordOccurrenceEquiv
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).BoundaryOccurrence ≃
      (oneFacePresentation Edge word).BoundaryOccurrence where
  toFun := ofOneFaceWordMapOccurrence word
  invFun := ofOneFaceWordComapOccurrence word
  left_inv := by
    rintro ⟨f, i⟩
    have hf : f = 0 := ofOneFaceWord_face_eq_zero word f
    subst f
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  right_inv := by
    rintro ⟨f, i⟩
    cases f
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl

@[simp]
theorem ofOneFaceWordOccurrenceEquiv_apply
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    ofOneFaceWordOccurrenceEquiv word o =
      ofOneFaceWordMapOccurrence word o :=
  rfl

@[simp]
theorem ofOneFaceWordMapOccurrence_comap
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence) :
    ofOneFaceWordMapOccurrence word
        ((ofOneFaceWordOccurrenceEquiv word).symm o) = o :=
  (ofOneFaceWordOccurrenceEquiv word).apply_symm_apply o

theorem ofOneFaceWordComapOccurrence_dart
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence) :
    SignedDart.mapEquiv (Fintype.equivFin Edge)
        ((oneFacePresentation Edge word).occurrenceDart o) =
      (FiniteCyclicPresentation.BoundaryOccurrence.dart
        ((ofOneFaceWordOccurrenceEquiv word).symm o)) := by
  rw [← ofOneFaceWordMapOccurrence_dart word
    ((ofOneFaceWordOccurrenceEquiv word).symm o)]
  rw [ofOneFaceWordMapOccurrence_comap]

/-- Two distinct occurrences of one finite-cyclic edge force that edge to be internal. -/
theorem IsSurfaceValid.not_isBoundaryEdge_of_distinct_occurrences
    {P : FiniteCyclicPresentation} (_valid : P.IsSurfaceValid)
    (source target : P.BoundaryOccurrence) (hne : source ≠ target)
    (hedge : target.edge = source.edge) :
    ¬P.IsBoundaryEdge source.edge := by
  intro hboundary
  have hcard : (P.edgeOccurrences source.edge).card = 1 := by
    rw [P.card_edgeOccurrences]
    exact hboundary
  obtain ⟨only, hset⟩ := Finset.card_eq_one.mp hcard
  have hsource : source ∈ P.edgeOccurrences source.edge := by
    exact (P.mem_edgeOccurrences source.edge source).mpr rfl
  have htarget : target ∈ P.edgeOccurrences source.edge := by
    exact (P.mem_edgeOccurrences source.edge target).mpr hedge
  have hs : source = only := by simpa only [hset, Finset.mem_singleton] using hsource
  have ht : target = only := by simpa only [hset, Finset.mem_singleton] using htarget
  exact hne (hs.trans ht.symm)

/-- Transport a finite-cyclic pairing back to the original typed one-face word. -/
noncomputable def ofOneFaceWordMapPairing
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (oneFacePresentation Edge word).BoundaryPairing := by
  let K := oneFacePresentation Edge word
  let source := ofOneFaceWordMapOccurrence word pairing.source
  let target := ofOneFaceWordMapOccurrence word pairing.target
  have hne : source ≠ target :=
    (ofOneFaceWordOccurrenceEquiv word).injective.ne pairing.source_ne_target
  have hcompatible :
      match pairing.direction with
      | .same => K.occurrenceDart target = K.occurrenceDart source
      | .opposite =>
          K.occurrenceDart target = K.inv (K.occurrenceDart source) := by
    cases hdirection : pairing.direction with
    | same =>
        have hp : pairing.target.dart = pairing.source.dart := by
          simpa only [hdirection] using pairing.compatible
        apply (SignedDart.mapEquiv (Fintype.equivFin Edge)).injective
        rw [ofOneFaceWordMapOccurrence_dart,
          ofOneFaceWordMapOccurrence_dart]
        exact hp
    | opposite =>
        have hp : pairing.target.dart = pairing.source.dart.flip := by
          simpa only [hdirection] using pairing.compatible
        apply (SignedDart.mapEquiv (Fintype.equivFin Edge)).injective
        change
          SignedDart.mapEquiv (Fintype.equivFin Edge)
              (K.occurrenceDart target) =
            SignedDart.mapEquiv (Fintype.equivFin Edge)
              (K.occurrenceDart source).flip
        exact (ofOneFaceWordMapOccurrence_dart word pairing.target).trans
          (hp.trans ((congrArg SignedDart.flip
            (ofOneFaceWordMapOccurrence_dart word pairing.source)).symm.trans
            (SignedDart.mapEquiv_flip _ _).symm))
  have horbit :
      K.Occurs (K.occurrenceDart source) target := by
    cases hdirection : pairing.direction with
    | same =>
        left
        simpa only [hdirection] using hcompatible
    | opposite =>
        right
        simpa only [hdirection] using hcompatible
  have hsourceBoundary :
      ¬K.IsBoundaryDart (K.occurrenceDart source) :=
    SurfaceCellComplex.not_isBoundaryDart_of_occurs_at_ne
      hne (Or.inl rfl) horbit
  have htargetBoundary :
      ¬K.IsBoundaryDart (K.occurrenceDart target) := by
    cases hdirection : pairing.direction with
    | same =>
        have hsame : K.occurrenceDart target = K.occurrenceDart source := by
          simpa only [hdirection] using hcompatible
        rw [hsame]
        exact hsourceBoundary
    | opposite =>
        have hopp :
            K.occurrenceDart target = K.inv (K.occurrenceDart source) := by
          simpa only [hdirection] using hcompatible
        rw [hopp]
        exact ((K.isBoundaryDart_inv_iff
          (K.occurrenceDart source)).not).mpr hsourceBoundary
  exact
    { source := source
      target := target
      source_ne_target := hne
      source_not_boundary := hsourceBoundary
      target_not_boundary := htargetBoundary
      direction := pairing.direction
      compatible := hcompatible }

/-- Pull a typed one-face pairing forward to the enumerated finite-cyclic word. -/
noncomputable def ofOneFaceWordComapPairing
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWord word).BoundaryPairing := by
  let source := (ofOneFaceWordOccurrenceEquiv word).symm pairing.source
  let target := (ofOneFaceWordOccurrenceEquiv word).symm pairing.target
  have hne : source ≠ target :=
    (ofOneFaceWordOccurrenceEquiv word).symm.injective.ne
      pairing.source_ne_target
  have hcompatible :
      match pairing.direction with
      | .same => target.dart = source.dart
      | .opposite => target.dart = source.dart.flip := by
    cases hdirection : pairing.direction with
    | same =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).occurrenceDart pairing.source := by
          simpa only [hdirection] using pairing.compatible
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) :=
            congrArg (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart :=
            ofOneFaceWordComapOccurrence_dart word pairing.source
    | opposite =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).inv
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) := by
          simpa only [hdirection] using pairing.compatible
        change
          (oneFacePresentation Edge word).occurrenceDart pairing.target =
            ((oneFacePresentation Edge word).occurrenceDart
              pairing.source).flip at hp
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source).flip := by
            exact congrArg
              (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart.flip := by
            exact (SignedDart.mapEquiv_flip _ _).trans
              (congrArg SignedDart.flip
                (ofOneFaceWordComapOccurrence_dart word pairing.source))
  have hedge : target.edge = source.edge := by
    cases hdirection : pairing.direction with
    | same =>
        have hsame : target.dart = source.dart := by
          simpa only [hdirection] using hcompatible
        exact congrArg edgeOfDart hsame
    | opposite =>
        have hopp : target.dart = source.dart.flip := by
          simpa only [hdirection] using hcompatible
        simpa only [BoundaryOccurrence.edge, edgeOfDart_flip] using
          congrArg edgeOfDart hopp
  have hsourceBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge source.edge :=
    valid.not_isBoundaryEdge_of_distinct_occurrences source target hne hedge
  have htargetBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge target.edge := by
    rw [hedge]
    exact hsourceBoundary
  exact
    { source := source
      target := target
      source_ne_target := hne
      source_not_boundary := hsourceBoundary
      target_not_boundary := htargetBoundary
      direction := pairing.direction
      compatible := hcompatible }

@[simp]
theorem ofOneFaceWordMapPairing_source
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).source =
      ofOneFaceWordMapOccurrence word pairing.source :=
  rfl

@[simp]
theorem ofOneFaceWordMapPairing_target
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).target =
      ofOneFaceWordMapOccurrence word pairing.target :=
  rfl

@[simp]
theorem ofOneFaceWordMapPairing_direction
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).direction = pairing.direction :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_source
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).source =
      (ofOneFaceWordOccurrenceEquiv word).symm pairing.source :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_target
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).target =
      (ofOneFaceWordOccurrenceEquiv word).symm pairing.target :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_direction
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).direction =
      pairing.direction :=
  rfl

theorem ofOneFaceWordPreHomeomorph_pairing_source_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.source.point t) =
      (ofOneFaceWordMapPairing word pairing).identification.source.point t := by
  exact ofOneFaceWordPreHomeomorph_occurrenceSide_point
    word pairing.source t

theorem ofOneFaceWordPreHomeomorph_pairing_target_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point t) =
      (ofOneFaceWordMapPairing word pairing).identification.target.point t := by
  exact ofOneFaceWordPreHomeomorph_occurrenceSide_point
    word pairing.target t

theorem ofOneFaceWordPreHomeomorph_pairing_parameter_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (ofOneFaceWordMapPairing word pairing).identification.target.point
        ((ofOneFaceWordMapPairing word pairing).identification.parameter t) := by
  rw [ofOneFaceWordPreHomeomorph_pairing_target_point]
  rfl

theorem ofOneFaceWordPreHomeomorph_generator_related
    (word : List (SignedDart Edge))
    (_validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (pairing : (ofOneFaceWord word).BoundaryPairing)
    (t : unitInterval) :
    (oneFacePresentation Edge word).PolygonalGluingRel validTyped
      (ofOneFaceWordPreHomeomorph word
        (pairing.identification.source.point t))
      (ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [ofOneFaceWordPreHomeomorph_pairing_source_point,
    ofOneFaceWordPreHomeomorph_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (ofOneFaceWordMapPairing word pairing).identification
    (SurfaceCellComplex.pairing_identification_mem validTyped
      (ofOneFaceWordMapPairing word pairing)) t

/-- The enumeration pre-homeomorphism maps the complete finite-cyclic gluing relation into the
typed one-face gluing relation. -/
theorem ofOneFaceWordPreHomeomorph_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    {x y : (ofOneFaceWord word).PolygonalPreRealization}
    (hxy :
      (ofOneFaceWord word).PolygonalGluingRel validFinite x y) :
    (oneFacePresentation Edge word).PolygonalGluingRel validTyped
      (ofOneFaceWordPreHomeomorph word x)
      (ofOneFaceWordPreHomeomorph word y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((ofOneFaceWord word).polygonalIdentifications validFinite)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact ofOneFaceWordPreHomeomorph_generator_related
            word validFinite validTyped pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (((oneFacePresentation Edge word).occurrenceSide o).point t) =
      ((ofOneFaceWord word).occurrenceSide
        ((ofOneFaceWordOccurrenceEquiv word).symm o)).point t := by
  apply (ofOneFaceWordPreHomeomorph word).injective
  rw [(ofOneFaceWordPreHomeomorph word).apply_symm_apply]
  rw [ofOneFaceWordPreHomeomorph_occurrenceSide_point]
  rw [ofOneFaceWordMapOccurrence_comap]

theorem ofOneFaceWordPreHomeomorph_symm_pairing_source_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.source.point t) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.source.point t := by
  exact ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    word pairing.source t

theorem ofOneFaceWordPreHomeomorph_symm_pairing_target_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point t) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.target.point t := by
  exact ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    word pairing.target t

theorem ofOneFaceWordPreHomeomorph_symm_pairing_parameter_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.target.point
        ((ofOneFaceWordComapPairing word validFinite pairing).identification.parameter t) := by
  rw [ofOneFaceWordPreHomeomorph_symm_pairing_target_point]
  rfl

theorem ofOneFaceWordPreHomeomorph_symm_generator_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (_validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite
      ((ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.source.point t))
      ((ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [ofOneFaceWordPreHomeomorph_symm_pairing_source_point,
    ofOneFaceWordPreHomeomorph_symm_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (ofOneFaceWordComapPairing word validFinite pairing).identification
    (pairing_identification_mem validFinite
      (ofOneFaceWordComapPairing word validFinite pairing)) t

/-- The inverse enumeration pre-homeomorphism maps the complete typed gluing relation back into
the finite-cyclic gluing relation. -/
theorem ofOneFaceWordPreHomeomorph_symm_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    {x y : (oneFacePresentation Edge word).PolygonalPreRealization}
    (hxy :
      (oneFacePresentation Edge word).PolygonalGluingRel validTyped x y) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite
      ((ofOneFaceWordPreHomeomorph word).symm x)
      ((ofOneFaceWordPreHomeomorph word).symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((oneFacePresentation Edge word).polygonalIdentifications validTyped)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact ofOneFaceWordPreHomeomorph_symm_generator_related
            word validFinite validTyped pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem ofOneFaceWordPreHomeomorph_related_iff
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (x y : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite x y ↔
      (oneFacePresentation Edge word).PolygonalGluingRel validTyped
        (ofOneFaceWordPreHomeomorph word x)
        (ofOneFaceWordPreHomeomorph word y) := by
  constructor
  · exact ofOneFaceWordPreHomeomorph_related
      word validFinite validTyped
  · intro hxy
    simpa only [(ofOneFaceWordPreHomeomorph word).symm_apply_apply] using
      ofOneFaceWordPreHomeomorph_symm_related
        word validFinite validTyped hxy

/-- Enumerating the edge names of a typed one-face word preserves its faithful polygonal
realization. -/
noncomputable def ofOneFaceWordRealizationHomeomorph
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid) :
    (ofOneFaceWord word).PolygonalRealization validFinite ≃ₜ
      (oneFacePresentation Edge word).PolygonalRealization validTyped :=
  PolygonGluing.realizationCongr (ofOneFaceWordPreHomeomorph word)
    (ofOneFaceWordPreHomeomorph_related_iff
      word validFinite validTyped)

end FiniteCyclicPresentation

namespace NormalForm

/-- The admissible canonical orientable finite-cyclic presentation realizes the exact vendored
Lean-Eval quotient. -/
noncomputable def canonicalOrientableRealizationHomeomorph
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    (canonicalPresentation (.orientable p n)).PolygonalRealization
        (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid) ≃ₜ
      Quot (OrientableRel p n) :=
  (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
      (orientableBoundaryWord p n)
      (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
      (orientableCellComplex_occurrencePairingValid hvalid)).trans
    (orientablePolygonalRealizationHomeomorph hvalid)

/-- The admissible canonical nonorientable finite-cyclic presentation realizes the exact vendored
Lean-Eval quotient. -/
noncomputable def canonicalNonOrientableRealizationHomeomorph
    {p n : ℕ} (hp : 1 ≤ p) :
    (canonicalPresentation (.nonOrientable p n)).PolygonalRealization
        (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp) ≃ₜ
      Quot (NonOrientableRel p n) :=
  (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
      (nonOrientableBoundaryWord p n)
      (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
      (nonOrientableCellComplex_occurrencePairingValid hp)).trans
    (nonOrientablePolygonalRealizationHomeomorph hp)

end NormalForm

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification22_block_04
/- END ClassificationOfSurfaces.FiniteCyclicCanonicalRealization -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicP1Realization | 4b5b0a4c87bad7673611ff6251920bbff00ebb2844ba4081c5d98290b154db0c -/
section schottkyclassification22_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal realization of Gallier--Xu P1

The boundary of every source face is assigned weight two at occurrences of the subdivided edge
and weight one everywhere else.  `WeightedCircle` turns those weights into the exact boundary
homeomorphism required by P1, and radial extension gives the corresponding disk homeomorphism.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P1

/-- The number of target sides replacing one source dart. -/
def dartWeight {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) : ℕ :=
  if edgeOfDart d = a then 2 else 1

/-- The P1 subdivision weights around one face boundary. -/
def faceWeights (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    List ℕ :=
  (P.boundary f).map (dartWeight a)

@[simp]
theorem faceWeights_length (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (faceWeights P a f).length = (P.boundary f).length := by
  simp [faceWeights]

theorem faceWeights_positive (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    WeightedCircle.Positive (faceWeights P a f) := by
  intro w hw
  rcases List.mem_map.1 hw with ⟨d, _hd, rfl⟩
  simp only [dartWeight]
  split <;> norm_num

theorem faceWeights_ne_nil
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (validP : P.IsSurfaceValid) :
    faceWeights P a f ≠ [] := by
  simpa [faceWeights] using validP.2.1 f

@[simp]
theorem length_expandDart_eq_dartWeight {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    (expandDart a d).length = dartWeight a d := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, dartWeight, edgeOfDart]
      · simp [expandDart, dartWeight, edgeOfDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, dartWeight, edgeOfDart]
      · simp [expandDart, dartWeight, edgeOfDart, h]

theorem expandWord_length_eq_sum_map_dartWeight {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    (expandWord a word).length = (word.map (dartWeight a)).sum := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      simp [expandWord, length_expandDart_eq_dartWeight]

theorem expandWord_length_eq_sum_faceWeights
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    (expandWord a (P.boundary f)).length = (faceWeights P a f).sum := by
  exact expandWord_length_eq_sum_map_dartWeight a (P.boundary f)

theorem faceWeights_sum
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    (faceWeights P a f).sum =
      ((expand P a).boundary (faceEquiv P a f)).length := by
  calc
    (faceWeights P a f).sum =
        (expandWord a (P.boundary f)).length :=
      (expandWord_length_eq_sum_faceWeights P a f).symm
    _ = ((expand P a).boundary (faceEquiv P a f)).length := by
      exact congrArg List.length (expand_boundary P a f).symm

/-- The first target side replacing source side `i`. -/
def expandedStartIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum, by
    rw [← faceWeights_sum P a f]
    exact WeightedCircle.sum_take_lt_sum
      (faceWeights_positive P a f) (Fin.cast (faceWeights_length P a f).symm i)⟩

@[simp]
theorem expandedStartIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (expandedStartIndex P a f i).val =
      ((faceWeights P a f).take i).sum :=
  rfl

/-- Transport a source occurrence to the first target occurrence in its expanded block. -/
def firstExpandedOccurrence
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a o.1, expandedStartIndex P a o.1 o.2⟩

theorem expandWord_getElem?_expandedStart {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) (i : Fin word.length) :
    (expandWord a word)[((word.map (dartWeight a)).take i).sum]? =
      (expandDart a (word.get i))[0]? := by
  induction word with
  | nil => exact Fin.elim0 i
  | cons d word ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · cases d with
        | pos e =>
            by_cases he : e = a
            · subst e
              simp [expandWord, expandDart, dartWeight, edgeOfDart]
            · simp [expandWord, expandDart, dartWeight, edgeOfDart, he]
        | neg e =>
            by_cases he : e = a
            · subst e
              simp [expandWord, expandDart, dartWeight, edgeOfDart]
            · simp [expandWord, expandDart, dartWeight, edgeOfDart, he]
      · simp only [List.map_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons, expandWord_cons, List.get_eq_getElem,
          List.getElem_cons_succ]
        rw [List.getElem?_append_right]
        · rw [length_expandDart_eq_dartWeight]
          simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using ih j
        · rw [length_expandDart_eq_dartWeight]
          omega

theorem expandDart_length_pos {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    0 < (expandDart a d).length := by
  rw [length_expandDart_eq_dartWeight]
  unfold dartWeight
  split <;> omega

@[simp]
theorem dartWeight_eq_two_iff {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d = 2 ↔ edgeOfDart d = a := by
  simp [dartWeight]

@[simp]
theorem dartWeight_eq_one_iff {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d = 1 ↔ edgeOfDart d ≠ a := by
  simp [dartWeight]

/-- More generally, lookup inside an expanded block agrees with lookup in the substituted
dart-word. -/
theorem expandWord_getElem?_expandedOffset {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) (i : Fin word.length)
    (k : ℕ) (hk : k < (expandDart a (word.get i)).length) :
    (expandWord a word)[
        ((word.map (dartWeight a)).take i).sum + k]? =
      (expandDart a (word.get i))[k]? := by
  induction word with
  | nil => exact Fin.elim0 i
  | cons d word ih =>
      induction i using Fin.cases with
      | zero =>
        simp only [List.map_cons, Fin.val_zero, List.take_zero, List.sum_nil,
          zero_add, expandWord_cons, List.get_eq_getElem, List.getElem_cons_zero]
        apply List.getElem?_append_left
        exact hk
      | succ j =>
        simp only [List.map_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons, expandWord_cons, List.get_eq_getElem,
          List.getElem_cons_succ]
        rw [List.getElem?_append_right]
        · rw [length_expandDart_eq_dartWeight]
          simpa only [Nat.add_assoc, Nat.add_sub_cancel_left,
            List.get_eq_getElem] using ih j hk
        · rw [length_expandDart_eq_dartWeight]
          omega

theorem firstExpandedOccurrence_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) :
    (firstExpandedOccurrence P a o).dart =
      (expandDart a o.dart).get
        ⟨0, expandDart_length_pos a o.dart⟩ := by
  rcases o with ⟨f, i⟩
  have hlookup :=
    expandWord_getElem?_expandedStart a (P.boundary f) i
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    exact WeightedCircle.sum_take_lt_sum
      (faceWeights_positive P a f)
      (Fin.cast (faceWeights_length P a f).symm i)
  rw [List.getElem?_eq_getElem hstart,
    List.getElem?_eq_getElem (expandDart_length_pos a
      ((P.boundary f).get i))] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [firstExpandedOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

theorem sum_take_add_get_le_sum {weights : List ℕ}
    (i : Fin weights.length) :
    (weights.take i).sum + weights.get i ≤ weights.sum := by
  have hsplit :=
    congrArg List.sum (List.take_append_drop (i.val + 1) weights)
  rw [List.sum_append, List.take_succ_eq_append_getElem i.isLt,
    List.sum_append] at hsplit
  simp only [List.sum_singleton] at hsplit
  have hget : weights[i.val] = weights.get i := rfl
  rw [hget] at hsplit
  omega

theorem sum_take_add_one_lt_sum_of_get_eq_two {weights : List ℕ}
    (i : Fin weights.length) (hget : weights.get i = 2) :
    (weights.take i).sum + 1 < weights.sum := by
  have hle := sum_take_add_get_le_sum i
  rw [hget] at hle
  omega

/-- A position in the concatenation of blocks whose lengths are `weights`. -/
abbrev BlockPosition (weights : List ℕ) :=
  Σ i : Fin weights.length, Fin (weights.get i)

/-- Linear position of a block-local index. -/
def blockPosition {weights : List ℕ} (p : BlockPosition weights) : ℕ :=
  (weights.take p.1).sum + p.2

/-- Distinct block-local positions have distinct linear positions. -/
@[simp] theorem blockPosition_injective (weights : List ℕ) :
    Function.Injective (@blockPosition weights) := by
  induction weights with
  | nil =>
      rintro ⟨i, _⟩
      exact Fin.elim0 i
  | cons w weights ih =>
      rintro ⟨i, k⟩ ⟨j, l⟩ heq
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero =>
              have hkl : k = l := by
                apply Fin.ext
                simpa [blockPosition] using heq
              subst l
              rfl
          | succ j =>
              exfalso
              have hk : k.val < w := k.isLt
              simp only [blockPosition, Fin.val_zero, List.take_zero,
                List.sum_nil, zero_add, Fin.val_succ,
                List.take_succ_cons, List.sum_cons] at heq
              omega
      | succ i =>
          induction j using Fin.cases with
          | zero =>
              exfalso
              have hl : l.val < w := l.isLt
              simp only [blockPosition, Fin.val_zero, List.take_zero,
                List.sum_nil, zero_add, Fin.val_succ,
                List.take_succ_cons, List.sum_cons] at heq
              omega
          | succ j =>
              have htail :
                  blockPosition (weights := weights) ⟨i, k⟩ =
                    blockPosition (weights := weights) ⟨j, l⟩ := by
                simp only [blockPosition, Fin.val_succ,
                  List.take_succ_cons, List.sum_cons] at heq ⊢
                omega
              have hp := ih htail
              cases hp
              rfl

theorem faceWeights_get
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (faceWeights P a f).get
        (Fin.cast (faceWeights_length P a f).symm i) =
      dartWeight a ((P.boundary f).get i) := by
  simp [faceWeights] <;> rfl

/-- A target-side index inside the expanded block of source side `i`. -/
def expandedOffsetIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i))) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum + k, by
    rw [← faceWeights_sum P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hle := sum_take_add_get_le_sum i'
    have hget :
        (faceWeights P a f).get i' =
          dartWeight a ((P.boundary f).get i) := by
      exact faceWeights_get P a f i
    change
      ((faceWeights P a f).take i).sum +
          (faceWeights P a f).get i' ≤
        (faceWeights P a f).sum at hle
    rw [hget] at hle
    omega⟩

@[simp]
theorem expandedOffsetIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i))) :
    (expandedOffsetIndex P a f i k).val =
      ((faceWeights P a f).take i).sum + k :=
  rfl

/-- A source occurrence together with one of the one or two target sides replacing it. -/
abbrev ExpandedSourcePosition
    (P : FiniteCyclicPresentation) (a : P.Edge) :=
  Σ o : P.BoundaryOccurrence, Fin (dartWeight a o.dart)

/-- Transport a block-local source position to its target boundary occurrence. -/
def expandedOccurrenceAt
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a p.1.1,
    expandedOffsetIndex P a p.1.1 p.1.2 p.2⟩

/-- The block-local occurrence transport is injective: expanded blocks never overlap. -/
theorem expandedOccurrenceAt_injective
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    Function.Injective (expandedOccurrenceAt P a) := by
  rintro ⟨⟨f, i⟩, k⟩ ⟨⟨g, j⟩, l⟩ h
  have hface : f = g := by
    apply (faceEquiv P a).injective
    exact congrArg Sigma.fst h
  subst g
  have hlinear :
      ((faceWeights P a f).take i).sum + k =
        ((faceWeights P a f).take j).sum + l := by
    exact congrArg (fun o => o.2.val) h
  let i' : Fin (faceWeights P a f).length :=
    Fin.cast (faceWeights_length P a f).symm i
  let j' : Fin (faceWeights P a f).length :=
    Fin.cast (faceWeights_length P a f).symm j
  let k' : Fin ((faceWeights P a f).get i') :=
    Fin.cast (faceWeights_get P a f i).symm k
  let l' : Fin ((faceWeights P a f).get j') :=
    Fin.cast (faceWeights_get P a f j).symm l
  have hblock :
      blockPosition (weights := faceWeights P a f) ⟨i', k'⟩ =
        blockPosition (weights := faceWeights P a f) ⟨j', l'⟩ := by
    exact hlinear
  have hpair :=
    blockPosition_injective (faceWeights P a f) hblock
  have hij' : i' = j' := congrArg Sigma.fst hpair
  have hij : i = j := by
    apply Fin.ext
    have hvals := congrArg Fin.val hij'
    change i.val = j.val at hvals
    exact hvals
  subst j
  have hkl : k = l := by
    apply Fin.ext
    simpa using hlinear
  subst l
  rfl

theorem expandedOccurrenceAt_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).dart =
      (expandDart a p.1.dart).get
        (Fin.cast (length_expandDart_eq_dartWeight a p.1.dart).symm p.2) := by
  rcases p with ⟨⟨f, i⟩, k⟩
  let k' : Fin (expandDart a ((P.boundary f).get i)).length :=
    Fin.cast (length_expandDart_eq_dartWeight a _).symm k
  have hlookup :=
    expandWord_getElem?_expandedOffset a (P.boundary f) i k'
      k'.isLt
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum + k <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    change
      ((faceWeights P a f).take i).sum + k <
        (faceWeights P a f).sum
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hle := sum_take_add_get_le_sum i'
    change
      ((faceWeights P a f).take i).sum +
          (faceWeights P a f).get i' ≤
        (faceWeights P a f).sum at hle
    have hget :
        (faceWeights P a f).get i' =
          dartWeight a ((P.boundary f).get i) := by
      exact faceWeights_get P a f i
    rw [hget] at hle
    have hk :
        k.val < dartWeight a ((P.boundary f).get i) :=
      k.isLt
    omega
  have hstart' :
      (((P.boundary f).map (dartWeight a)).take i).sum + k' <
        (expandWord a (P.boundary f)).length := by
    exact hstart
  rw [List.getElem?_eq_getElem hstart',
    List.getElem?_eq_getElem k'.isLt] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [expandedOccurrenceAt, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

theorem isBoundaryEdge_expand_castSucc_iff
    (P : FiniteCyclicPresentation) (a e : P.Edge) :
    (expand P a).IsBoundaryEdge e.castSucc ↔
      P.IsBoundaryEdge e := by
  unfold IsBoundaryEdge
  rw [← edgeMultiplicity_expand_castSucc P a e]

theorem isBoundaryEdge_expand_freshEdge_iff
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).IsBoundaryEdge (freshEdge P.edgeCount) ↔
      P.IsBoundaryEdge a := by
  unfold IsBoundaryEdge
  rw [← edgeMultiplicity_expand_freshEdge P a]

/-- The target edge at a block-local offset. -/
def expandedSubedge {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : Fin (n + 1) :=
  edgeOfDart
    ((expandDart a d).get
      (Fin.cast (length_expandDart_eq_dartWeight a d).symm k))

/-- Each target subedge has the same boundary/internal status as its source edge. -/
theorem isBoundaryEdge_expandedSubedge_iff
    (P : FiniteCyclicPresentation) (a : P.Edge) (d : P.Dart)
    (k : Fin (dartWeight a d)) :
    (expand P a).IsBoundaryEdge (expandedSubedge a d k) ↔
      P.IsBoundaryEdge (edgeOfDart d) := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge, isBoundaryEdge_expand_castSucc_iff,
            isBoundaryEdge_expand_freshEdge_iff, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0, isBoundaryEdge_expand_castSucc_iff]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge, isBoundaryEdge_expand_castSucc_iff,
            isBoundaryEdge_expand_freshEdge_iff, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0, isBoundaryEdge_expand_castSucc_iff]

/-- Every target subedge has the same boundary/internal status as its source edge. -/
theorem expandedOccurrenceAt_not_boundary
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a)
    (h : ¬P.IsBoundaryEdge p.1.edge) :
    ¬(expand P a).IsBoundaryEdge (expandedOccurrenceAt P a p).edge := by
  rw [BoundaryOccurrence.edge, expandedOccurrenceAt_dart]
  exact (isBoundaryEdge_expandedSubedge_iff P a p.1.dart p.2).not.mpr h

/-- The first local target-side offset always exists. -/
def zeroOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    Fin (dartWeight a d) :=
  ⟨0, by
    unfold dartWeight
    split <;> omega⟩

/-- A selected source side has a second local target-side offset. -/
def oneOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (hselected : edgeOfDart d = a) :
    Fin (dartWeight a d) :=
  ⟨1, by
    rw [(dartWeight_eq_two_iff a d).2 hselected]
    omega⟩

@[simp]
theorem dartWeight_flip {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    dartWeight a d.flip = dartWeight a d := by
  cases d <;> simp [dartWeight, edgeOfDart, SignedDart.flip] <;> rfl

/-- The signed target dart at a block-local offset. -/
def expandedSubdart {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : SignedDart (Fin (n + 1)) :=
  (expandDart a d).get
    (Fin.cast (length_expandDart_eq_dartWeight a d).symm k)

/-- Reverse a block-local offset after reversing the source dart. -/
def reverseOffset {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) : Fin (dartWeight a d.flip) :=
  Fin.cast (dartWeight_flip a d).symm k.rev

/-- Reversing a source dart reverses the expanded block and flips its signed darts. -/
theorem expandedSubdart_flip_reverseOffset {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d)) :
    expandedSubdart a d.flip (reverseOffset a d k) =
      (expandedSubdart a d k).flip := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
            edgeOfDart, SignedDart.flip, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
          edgeOfDart, he, hk0, SignedDart.flip]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
            edgeOfDart, SignedDart.flip, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubdart, reverseOffset, expandDart, dartWeight,
          edgeOfDart, he, hk0, SignedDart.flip]

theorem BoundaryPairing.target_edge_eq_source_edge
    {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.target.edge = pairing.source.edge := by
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible]
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible, edgeOfDart_flip]

theorem expandedOccurrenceAt_dart_eq_expandedSubdart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).dart =
      expandedSubdart a p.1.dart p.2 := by
  exact expandedOccurrenceAt_dart P a p

/-- Transport a block-local offset across an equal-dart pairing. -/
def samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    Fin (dartWeight a pairing.target.dart) :=
  Fin.cast (congrArg (dartWeight a) hcompatible.symm) k

/-- Transport a block-local offset across a flipped-dart pairing. -/
def oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    Fin (dartWeight a pairing.target.dart) :=
  Fin.cast (congrArg (dartWeight a) hcompatible.symm)
    (reverseOffset a pairing.source.dart k)

theorem expandedSubdart_cast_eq {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁)
    (k : Fin (dartWeight a d₁)) :
    expandedSubdart a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm) k) =
      expandedSubdart a d₁ k := by
  subst d₂
  rfl

theorem expandedSubdart_cast_flip {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁.flip)
    (k : Fin (dartWeight a d₁)) :
    expandedSubdart a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm)
          (reverseOffset a d₁ k)) =
      (expandedSubdart a d₁ k).flip := by
  subst d₂
  exact expandedSubdart_flip_reverseOffset a d₁ k

theorem expandedSubdart_samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    expandedSubdart a pairing.target.dart
        (samePairedOffset a pairing hcompatible k) =
      expandedSubdart a pairing.source.dart k := by
  exact expandedSubdart_cast_eq a hcompatible k

theorem expandedSubdart_oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    expandedSubdart a pairing.target.dart
        (oppositePairedOffset a pairing hcompatible k) =
      (expandedSubdart a pairing.source.dart k).flip := by
  exact expandedSubdart_cast_flip a hcompatible k

/-- Each same-direction old pairing expands to corresponding target-subedge pairings. -/
noncomputable def expandedPairingSame
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (expand P a).BoundaryPairing where
  source := expandedOccurrenceAt P a ⟨pairing.source, k⟩
  target :=
    expandedOccurrenceAt P a
      ⟨pairing.target, samePairedOffset a pairing hcompatible k⟩
  source_ne_target := by
    intro heq
    have hp :=
      expandedOccurrenceAt_injective P a heq
    exact pairing.source_ne_target (congrArg Sigma.fst hp)
  source_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.source, k⟩ pairing.source_not_boundary
  target_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.target, samePairedOffset a pairing hcompatible k⟩
      pairing.target_not_boundary
  direction := .same
  compatible := by
    rw [expandedOccurrenceAt_dart_eq_expandedSubdart,
      expandedOccurrenceAt_dart_eq_expandedSubdart]
    exact expandedSubdart_samePairedOffset a pairing hcompatible k

/-- Each opposite-direction old pairing expands to reversed target-subedge pairings. -/
noncomputable def expandedPairingOpposite
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (expand P a).BoundaryPairing where
  source := expandedOccurrenceAt P a ⟨pairing.source, k⟩
  target :=
    expandedOccurrenceAt P a
      ⟨pairing.target, oppositePairedOffset a pairing hcompatible k⟩
  source_ne_target := by
    intro heq
    have hp :=
      expandedOccurrenceAt_injective P a heq
    exact pairing.source_ne_target (congrArg Sigma.fst hp)
  source_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.source, k⟩ pairing.source_not_boundary
  target_not_boundary :=
    expandedOccurrenceAt_not_boundary P a
      ⟨pairing.target, oppositePairedOffset a pairing hcompatible k⟩
      pairing.target_not_boundary
  direction := .opposite
  compatible := by
    rw [expandedOccurrenceAt_dart_eq_expandedSubdart,
      expandedOccurrenceAt_dart_eq_expandedSubdart]
    exact expandedSubdart_oppositePairedOffset a pairing hcompatible k

/-- The second target side replacing a selected source occurrence. -/
def secondExpandedIndex
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a) :
    Fin ((expand P a).boundary (faceEquiv P a f)).length :=
  ⟨((faceWeights P a f).take i).sum + 1, by
    rw [← faceWeights_sum P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hget : (faceWeights P a f).get i' = 2 :=
      (faceWeights_get P a f i).trans ((dartWeight_eq_two_iff a _).2 hselected)
    exact sum_take_add_one_lt_sum_of_get_eq_two i' hget⟩

@[simp]
theorem secondExpandedIndex_val
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a) :
    (secondExpandedIndex P a f i hselected).val =
      ((faceWeights P a f).take i).sum + 1 :=
  rfl

/-- Transport a selected source occurrence to the second occurrence in its expanded block. -/
def secondExpandedOccurrence
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) (hselected : o.edge = a) :
    (expand P a).BoundaryOccurrence :=
  ⟨faceEquiv P a o.1,
    secondExpandedIndex P a o.1 o.2 hselected⟩

theorem secondExpandedOccurrence_dart
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (o : P.BoundaryOccurrence) (hselected : o.edge = a) :
    (secondExpandedOccurrence P a o hselected).dart =
      (expandDart a o.dart).get
        ⟨1, by
          rw [length_expandDart_eq_dartWeight]
          rw [(dartWeight_eq_two_iff a o.dart).2 hselected]
          norm_num⟩ := by
  rcases o with ⟨f, i⟩
  have hk :
      1 < (expandDart a ((P.boundary f).get i)).length := by
    rw [length_expandDart_eq_dartWeight]
    have hw : dartWeight a ((P.boundary f).get i) = 2 :=
      (dartWeight_eq_two_iff a _).2 hselected
    omega
  have hlookup :=
    expandWord_getElem?_expandedOffset a (P.boundary f) i 1 hk
  have hstart :
      (((P.boundary f).map (dartWeight a)).take i).sum + 1 <
        (expandWord a (P.boundary f)).length := by
    rw [expandWord_length_eq_sum_faceWeights P a f]
    let i' : Fin (faceWeights P a f).length :=
      Fin.cast (faceWeights_length P a f).symm i
    have hget : (faceWeights P a f).get i' = 2 :=
      (faceWeights_get P a f i).trans ((dartWeight_eq_two_iff a _).2 hselected)
    exact sum_take_add_one_lt_sum_of_get_eq_two i' hget
  rw [List.getElem?_eq_getElem hstart,
    List.getElem?_eq_getElem hk] at hlookup
  have hvalue := Option.some.inj hlookup
  simp only [secondExpandedOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (expand_boundary P a f)]
  exact hvalue

/-- The exact weighted homeomorphism between the source and P1-expanded face boundaries. -/
noncomputable def faceCircleHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Circle ≃ₜ Circle :=
  WeightedCircle.circleHomeomorph
    (faceWeights P a f) (faceWeights_positive P a f)
    (faceWeights_ne_nil P a f validP)

/-- Radially extend the weighted boundary map to the whole face disk. -/
noncomputable def faceHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell ((expand P a).boundary (faceEquiv P a f)).length :=
  PolygonCell.radialHomeomorph (faceCircleHomeomorph P a validP f)

/-- P1 acts facewise on the polygonal pre-realization. -/
noncomputable def preHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization ≃ₜ (expand P a).PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap (faceEquiv P a).bijective
      (fun f => (faceHomeomorph P a validP f).isHomeomorph)).homeomorph
    (Sigma.map (faceEquiv P a) fun f => faceHomeomorph P a validP f)

@[simp]
theorem preHomeomorph_apply_fst
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (x : P.PolygonalPreRealization) :
    (preHomeomorph P a validP x).1 = faceEquiv P a x.1 :=
  rfl

@[simp]
theorem faceHomeomorph_ofCircle
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face) (z : Circle) :
    faceHomeomorph P a validP f
        (PolygonCell.ofCircle (P.boundary f).length z) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (faceCircleHomeomorph P a validP f z) := by
  exact PolygonCell.radialHomeomorph_ofCircle _ _

/-- Exact boundary-coordinate formula for the facewise P1 map. -/
theorem faceHomeomorph_side
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (2 * Real.pi /
              ((expand P a).boundary (faceEquiv P a f)).length *
            (((faceWeights P a f).take i).sum +
              (faceWeights P a f).get
                  (Fin.cast (faceWeights_length P a f).symm i) *
                (t : ℝ)))) := by
  rw [show PolygonCell.side i t =
      PolygonCell.ofCircle (P.boundary f).length
        (Circle.exp
          (2 * Real.pi / (P.boundary f).length *
            ((i : ℝ) + (t : ℝ)))) by
    apply PolygonCell.ext
    change (Circle.exp (PolygonCell.sideAngle i t) : ℂ) =
      (Circle.exp
        (2 * Real.pi / (P.boundary f).length *
          ((i : ℝ) + (t : ℝ))) : Circle)
    congr 2
    unfold PolygonCell.sideAngle
    ring]
  rw [faceHomeomorph_ofCircle]
  apply congrArg (PolygonCell.ofCircle
    ((expand P a).boundary (faceEquiv P a f)).length)
  simpa only [faceCircleHomeomorph, faceWeights_length,
      faceWeights_sum, Fin.val_cast] using
    WeightedCircle.circleHomeomorph_exp_index_add'
      (faceWeights P a f) (faceWeights_positive P a f)
      (faceWeights_ne_nil P a f validP)
      (Fin.cast (faceWeights_length P a f).symm i) t

theorem faceHomeomorph_side_of_not_selected
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hnot : edgeOfDart ((P.boundary f).get i) ≠ a)
    (t : unitInterval) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (expandedStartIndex P a f i) t := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle (expandedStartIndex P a f i) t) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_one_iff a _).2 hnot]
  unfold PolygonCell.sideAngle
  rw [expandedStartIndex_val]
  push_cast
  ring

/-- Rescale the first half of a source side to a complete target side. -/
def firstHalfParameter (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    unitInterval :=
  ⟨2 * (t : ℝ), mul_nonneg (by norm_num) t.property.1, by linarith⟩

/-- Rescale the second half of a source side to a complete target side. -/
def secondHalfParameter (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ)) :
    unitInterval :=
  ⟨2 * (t : ℝ) - 1, by linarith, by linarith [t.property.2]⟩

@[simp]
theorem firstHalfParameter_val (t : unitInterval)
    (h : (t : ℝ) ≤ 1 / 2) :
    (firstHalfParameter t h : ℝ) = 2 * (t : ℝ) :=
  rfl

@[simp]
theorem secondHalfParameter_val (t : unitInterval)
    (h : 1 / 2 ≤ (t : ℝ)) :
    (secondHalfParameter t h : ℝ) = 2 * (t : ℝ) - 1 :=
  rfl

theorem faceHomeomorph_side_firstHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (expandedStartIndex P a f i)
        (firstHalfParameter t ht) := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle (expandedStartIndex P a f i)
          (firstHalfParameter t ht)) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_two_iff a _).2 hselected]
  unfold PolygonCell.sideAngle
  rw [expandedStartIndex_val, firstHalfParameter_val]
  push_cast
  ring

theorem faceHomeomorph_side_secondHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (hselected : edgeOfDart ((P.boundary f).get i) = a)
    (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    faceHomeomorph P a validP f (PolygonCell.side i t) =
      PolygonCell.side (secondExpandedIndex P a f i hselected)
        (secondHalfParameter t ht) := by
  rw [faceHomeomorph_side]
  apply PolygonCell.ext
  change
    (Circle.exp
      (2 * Real.pi /
          ((expand P a).boundary (faceEquiv P a f)).length *
        (((faceWeights P a f).take i).sum +
          (faceWeights P a f).get
              (Fin.cast (faceWeights_length P a f).symm i) *
            (t : ℝ))) : ℂ) =
      (Circle.exp
        (PolygonCell.sideAngle
          (secondExpandedIndex P a f i hselected)
          (secondHalfParameter t ht)) : ℂ)
  rw [faceWeights_get,
    (dartWeight_eq_two_iff a _).2 hselected]
  unfold PolygonCell.sideAngle
  rw [secondExpandedIndex_val, secondHalfParameter_val]
  push_cast
  ring

theorem preHomeomorph_occurrenceSide_of_not_selected
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hnot : o.edge ≠ a) (t : unitInterval) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨o, zeroOffset a o.dart⟩)).point t := by
  rcases o with ⟨f, i⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (zeroOffset a ((P.boundary f).get i))) t⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_of_not_selected P a validP f i hnot]
    congr 2

theorem preHomeomorph_occurrenceSide_firstHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hselected : o.edge = a) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨o, zeroOffset a o.dart⟩)).point
        (firstHalfParameter t ht) := by
  rcases o with ⟨f, i⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (zeroOffset a ((P.boundary f).get i)))
          (firstHalfParameter t ht)⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_firstHalf P a validP f i hselected t ht]
    congr 2

theorem preHomeomorph_occurrenceSide_secondHalf
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (o : P.BoundaryOccurrence)
    (hselected : o.edge = a) (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    preHomeomorph P a validP ((P.occurrenceSide o).point t) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨o, oneOffset a o.dart hselected⟩)).point
        (secondHalfParameter t ht) := by
  rcases o with ⟨f, i⟩
  have hselected' :
      edgeOfDart ((P.boundary f).get i) = a :=
    hselected
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f (PolygonCell.side i t)⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side
          (expandedOffsetIndex P a f i
            (oneOffset a ((P.boundary f).get i) hselected'))
          (secondHalfParameter t ht)⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    rw [faceHomeomorph_side_secondHalf P a validP f i hselected t ht]
    congr 2

@[simp]
theorem samePairedOffset_val
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (samePairedOffset a pairing hcompatible k).val = k.val :=
  rfl

@[simp]
theorem oppositePairedOffset_val
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) :
    (oppositePairedOffset a pairing hcompatible k).val =
      dartWeight a pairing.source.dart - (k.val + 1) := by
  rfl

theorem symm_firstHalfParameter
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval.symm (firstHalfParameter t ht) =
      secondHalfParameter (unitInterval.symm t) (by
        change 1 / 2 ≤ 1 - (t : ℝ)
        linarith) := by
  apply Subtype.ext
  simp [firstHalfParameter, secondHalfParameter, unitInterval.symm]
  ring

theorem symm_secondHalfParameter
    (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    unitInterval.symm (secondHalfParameter t ht) =
      firstHalfParameter (unitInterval.symm t) (by
        change 1 - (t : ℝ) ≤ 1 / 2
        linarith) := by
  apply Subtype.ext
  simp [firstHalfParameter, secondHalfParameter, unitInterval.symm]
  ring

theorem expandedPairingSame_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validQ : (expand P a).IsSurfaceValid)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    (expand P a).PolygonalGluingRel validQ
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u)
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨pairing.target,
            samePairedOffset a pairing hcompatible k⟩)).point u) := by
  exact PolygonGluing.related_of_mem
    (expandedPairingSame P a pairing hcompatible k).identification
    (pairing_identification_mem validQ
      (expandedPairingSame P a pairing hcompatible k)) u

theorem expandedPairingOpposite_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validQ : (expand P a).IsSurfaceValid)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    (expand P a).PolygonalGluingRel validQ
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u)
      (((expand P a).occurrenceSide
        (expandedOccurrenceAt P a
          ⟨pairing.target,
            oppositePairedOffset a pairing hcompatible k⟩)).point
        (unitInterval.symm u)) := by
  exact PolygonGluing.related_of_mem
    (expandedPairingOpposite P a pairing hcompatible k).identification
    (pairing_identification_mem validQ
      (expandedPairingOpposite P a pairing hcompatible k)) u

/-- The facewise P1 map sends every source gluing generator into the target generated
relation. -/
theorem preHomeomorph_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
      (preHomeomorph P a validP
        (pairing.identification.source.point t))
      (preHomeomorph P a validP
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  let validQ := expand_isSurfaceValid P a validP
  change
    (expand P a).PolygonalGluingRel validQ
      (preHomeomorph P a validP
        ((P.occurrenceSide pairing.source).point t))
      (preHomeomorph P a validP
        ((P.occurrenceSide pairing.target).point
          (pairing.identification.parameter t)))
  have hedge : pairing.target.edge = pairing.source.edge :=
    BoundaryPairing.target_edge_eq_source_edge pairing
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      have hparameter :
          pairing.identification.parameter t = t := by
        simp [BoundaryPairing.identification, PolygonGluing.Identification.parameter,
          hdirection]
      rw [hparameter]
      by_cases hselected : pairing.source.edge = a
      · have htargetSelected : pairing.target.edge = a :=
          hedge.trans hselected
        by_cases ht : (t : ℝ) ≤ 1 / 2
        · rw [preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.source hselected t ht,
            preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.target htargetSelected t ht]
          have hoffset :
              samePairedOffset a pairing hcompatible
                  (zeroOffset a pairing.source.dart) =
                zeroOffset a pairing.target.dart := by
            apply Fin.ext
            rfl
          rw [← hoffset]
          exact expandedPairingSame_related P a validQ pairing hcompatible
            (zeroOffset a pairing.source.dart) (firstHalfParameter t ht)
        · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
          rw [preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.source hselected t ht',
            preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.target htargetSelected t ht']
          have hoffset :
              samePairedOffset a pairing hcompatible
                  (oneOffset a pairing.source.dart hselected) =
                oneOffset a pairing.target.dart htargetSelected := by
            apply Fin.ext
            rfl
          rw [← hoffset]
          exact expandedPairingSame_related P a validQ pairing hcompatible
            (oneOffset a pairing.source.dart hselected)
            (secondHalfParameter t ht')
      · have htargetNot : pairing.target.edge ≠ a := by
          rw [hedge]
          exact hselected
        rw [preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.source hselected t,
            preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.target htargetNot t]
        have hoffset :
            samePairedOffset a pairing hcompatible
                (zeroOffset a pairing.source.dart) =
              zeroOffset a pairing.target.dart := by
          apply Fin.ext
          rfl
        rw [← hoffset]
        exact expandedPairingSame_related P a validQ pairing hcompatible
          (zeroOffset a pairing.source.dart) t
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      have hparameter :
          pairing.identification.parameter t = unitInterval.symm t := by
        simp [BoundaryPairing.identification, PolygonGluing.Identification.parameter,
          hdirection, PolygonGluing.ParameterDirection.homeomorph_opposite_apply]
      rw [hparameter]
      by_cases hselected : pairing.source.edge = a
      · have htargetSelected : pairing.target.edge = a :=
          hedge.trans hselected
        by_cases ht : (t : ℝ) ≤ 1 / 2
        · have hsymmHalf :
              1 / 2 ≤ (unitInterval.symm t : ℝ) := by
            change 1 / 2 ≤ 1 - (t : ℝ)
            linarith
          rw [preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.source hselected t ht,
            preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.target htargetSelected
                (unitInterval.symm t) hsymmHalf]
          have hoffset :
              oppositePairedOffset a pairing hcompatible
                  (zeroOffset a pairing.source.dart) =
                oneOffset a pairing.target.dart htargetSelected := by
            apply Fin.ext
            have hw :
                dartWeight a pairing.source.dart = 2 :=
              (dartWeight_eq_two_iff a _).2 hselected
            simp [oppositePairedOffset_val, hw, zeroOffset, oneOffset]
          rw [← hoffset, ← symm_firstHalfParameter t ht]
          exact expandedPairingOpposite_related P a validQ pairing hcompatible
            (zeroOffset a pairing.source.dart) (firstHalfParameter t ht)
        · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
          have hsymmHalf :
              (unitInterval.symm t : ℝ) ≤ 1 / 2 := by
            change 1 - (t : ℝ) ≤ 1 / 2
            linarith
          rw [preHomeomorph_occurrenceSide_secondHalf
              P a validP pairing.source hselected t ht',
            preHomeomorph_occurrenceSide_firstHalf
              P a validP pairing.target htargetSelected
                (unitInterval.symm t) hsymmHalf]
          have hoffset :
              oppositePairedOffset a pairing hcompatible
                  (oneOffset a pairing.source.dart hselected) =
                zeroOffset a pairing.target.dart := by
            apply Fin.ext
            have hw :
                dartWeight a pairing.source.dart = 2 :=
              (dartWeight_eq_two_iff a _).2 hselected
            simp [oppositePairedOffset_val, hw, zeroOffset, oneOffset]
          rw [← hoffset, ← symm_secondHalfParameter t ht']
          exact expandedPairingOpposite_related P a validQ pairing hcompatible
            (oneOffset a pairing.source.dart hselected)
            (secondHalfParameter t ht')
      · have htargetNot : pairing.target.edge ≠ a := by
          rw [hedge]
          exact hselected
        rw [preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.source hselected t,
            preHomeomorph_occurrenceSide_of_not_selected
              P a validP pairing.target htargetNot (unitInterval.symm t)]
        have hoffset :
            oppositePairedOffset a pairing hcompatible
                (zeroOffset a pairing.source.dart) =
              zeroOffset a pairing.target.dart := by
          apply Fin.ext
          have hw :
              dartWeight a pairing.source.dart = 1 :=
            (dartWeight_eq_one_iff a _).2 hselected
          simp [oppositePairedOffset_val, hw, zeroOffset]
        rw [← hoffset]
        exact expandedPairingOpposite_related P a validQ pairing hcompatible
          (zeroOffset a pairing.source.dart) t

theorem card_expandedSourcePosition
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    Fintype.card (ExpandedSourcePosition P a) =
      Fintype.card (expand P a).BoundaryOccurrence := by
  simp only [ExpandedSourcePosition, BoundaryOccurrence,
    Fintype.card_sigma, Fintype.card_fin]
  rw [Fintype.sum_sigma]
  calc
    (∑ f : P.Face,
        ∑ i : Fin (P.boundary f).length,
          dartWeight a ((P.boundary f).get i)) =
        ∑ f : P.Face, (faceWeights P a f).sum := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [← List.sum_ofFn]
      congr 1
      ext i
      simp [faceWeights]
    _ = ∑ q : (expand P a).Face,
          ((expand P a).boundary q).length := by
      apply Fintype.sum_equiv (faceEquiv P a)
      intro f
      exact faceWeights_sum P a f

/-- Expanded source blocks enumerate all target boundary occurrences. -/
noncomputable def expandedOccurrenceEquiv
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    ExpandedSourcePosition P a ≃ (expand P a).BoundaryOccurrence :=
  Equiv.ofBijective (expandedOccurrenceAt P a)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨expandedOccurrenceAt_injective P a,
        card_expandedSourcePosition P a⟩)

@[simp]
theorem expandedOccurrenceEquiv_apply
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    expandedOccurrenceEquiv P a p = expandedOccurrenceAt P a p :=
  rfl

/-- Contract either target subedge back to its source edge. -/
def contractExpandedEdge {n : ℕ} (a : Fin n) : Fin (n + 1) → Fin n :=
  Fin.lastCases a id

@[simp]
theorem contractExpandedEdge_castSucc {n : ℕ} (a e : Fin n) :
    contractExpandedEdge a e.castSucc = e := by
  simp [contractExpandedEdge]

@[simp]
theorem contractExpandedEdge_freshEdge {n : ℕ} (a : Fin n) :
    contractExpandedEdge a (freshEdge n) = a := by
  simp [contractExpandedEdge, freshEdge]

theorem contractExpandedEdge_expandedSubedge {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d)) :
    contractExpandedEdge a (expandedSubedge a d k) = edgeOfDart d := by
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0]
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        obtain ⟨kv, hkv⟩ := k
        have hk' : kv < 2 := hk
        clear hk
        interval_cases kv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge, Fin.cast, Fin.rev] <;> rfl
      · have hk0 : k.val = 0 := by
          have hk : k.val < 1 := by
            simpa [dartWeight, edgeOfDart, he] using k.isLt
          omega
        simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
          he, hk0]

theorem sourceEdge_eq_of_expandedSubedge_eq {n : ℕ} (a : Fin n)
    {d e : SignedDart (Fin n)}
    {k : Fin (dartWeight a d)} {l : Fin (dartWeight a e)}
    (h : expandedSubedge a d k = expandedSubedge a e l) :
    edgeOfDart d = edgeOfDart e := by
  have := congrArg (contractExpandedEdge a) h
  simpa only [contractExpandedEdge_expandedSubedge] using this

theorem expandedSubedge_injective_offset {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    Function.Injective (expandedSubedge a d) := by
  intro k l h
  cases d with
  | pos e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        have hl : l.val < 2 := by
          simpa [dartWeight, edgeOfDart] using l.isLt
        apply Fin.ext
        obtain ⟨kv, hkv⟩ := k
        obtain ⟨lv, hlv⟩ := l
        have hk' : kv < 2 := hk
        have hl' : lv < 2 := hl
        clear hk hl
        interval_cases kv <;> interval_cases lv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge_ne_freshEdge, Fin.cast, Fin.rev,
            (firstSubedge_ne_freshEdge a).symm] at h ⊢ <;>
          first
            | rfl
            | exact absurd h (firstSubedge_ne_freshEdge a)
            | exact absurd h (firstSubedge_ne_freshEdge a).symm
      · apply Fin.ext
        have hk : k.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using k.isLt
        have hl : l.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using l.isLt
        omega
  | neg e =>
      by_cases he : e = a
      · subst e
        have hk : k.val < 2 := by
          simpa [dartWeight, edgeOfDart] using k.isLt
        have hl : l.val < 2 := by
          simpa [dartWeight, edgeOfDart] using l.isLt
        apply Fin.ext
        obtain ⟨kv, hkv⟩ := k
        obtain ⟨lv, hlv⟩ := l
        have hk' : kv < 2 := hk
        have hl' : lv < 2 := hl
        clear hk hl
        interval_cases kv <;> interval_cases lv <;>
          simp [expandedSubedge, expandDart, dartWeight, edgeOfDart,
            firstSubedge_ne_freshEdge, Fin.cast, Fin.rev,
            (firstSubedge_ne_freshEdge a).symm] at h ⊢ <;>
          first
            | rfl
            | exact absurd h (firstSubedge_ne_freshEdge a)
            | exact absurd h (firstSubedge_ne_freshEdge a).symm
      · apply Fin.ext
        have hk : k.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using k.isLt
        have hl : l.val < 1 := by
          simpa [dartWeight, edgeOfDart, he] using l.isLt
        omega

theorem expandedOccurrenceAt_edge
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p : ExpandedSourcePosition P a) :
    (expandedOccurrenceAt P a p).edge =
      expandedSubedge a p.1.dart p.2 := by
  rw [BoundaryOccurrence.edge, expandedOccurrenceAt_dart]
  rfl

theorem expandedSourcePosition_eq_of_fst_eq_of_subedge_eq
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (p q : ExpandedSourcePosition P a)
    (hfst : p.1 = q.1)
    (hedge :
      expandedSubedge a p.1.dart p.2 =
        expandedSubedge a q.1.dart q.2) :
    p = q := by
  rcases p with ⟨o, k⟩
  rcases q with ⟨o', l⟩
  cases hfst
  have hkl : k = l :=
    expandedSubedge_injective_offset a o.dart hedge
  subst l
  rfl

theorem expandedSourcePosition_mk_transport
    (P : FiniteCyclicPresentation) (a : P.Edge)
    {o o' : P.BoundaryOccurrence} (h : o = o')
    (k : Fin (dartWeight a o'.dart)) :
    (⟨o, h.symm ▸ k⟩ : ExpandedSourcePosition P a) = ⟨o', k⟩ := by
  cases h
  rfl

theorem BoundaryPairing.direction_eq_of_source_target_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source) (htarget : p.target = q.target) :
    p.direction = q.direction := by
  have hsourceDart := congrArg BoundaryOccurrence.dart hsource
  have htargetDart := congrArg BoundaryOccurrence.dart htarget
  cases hp : p.direction <;> cases hq : q.direction
  · rfl
  · have hpcompat : p.target.dart = p.source.dart := by
      simpa only [hp] using p.compatible
    have hqcompat : q.target.dart = q.source.dart.flip := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart = p.source.dart.flip := by
      calc
        p.source.dart = p.target.dart := hpcompat.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart.flip := hqcompat
        _ = p.source.dart.flip := congrArg SignedDart.flip hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · have hpcompat : p.target.dart = p.source.dart.flip := by
      simpa only [hp] using p.compatible
    have hqcompat : q.target.dart = q.source.dart := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart.flip = p.source.dart := by
      calc
        p.source.dart.flip = p.target.dart := hpcompat.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart := hqcompat
        _ = p.source.dart := hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · rfl

theorem BoundaryPairing.eq_of_source_target_direction_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source) (htarget : p.target = q.target)
    (hdirection : p.direction = q.direction) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Every target pairing is one of the subedge pairings expanded from a unique old pairing. -/
theorem exists_eq_expandedPairing
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid)
    (q : (expand P a).BoundaryPairing) :
    (∃ (r : P.BoundaryPairing)
        (_hdirection : r.direction = .same)
        (hcompatible : r.target.dart = r.source.dart)
        (k : Fin (dartWeight a r.source.dart)),
        q = expandedPairingSame P a r hcompatible k) ∨
      (∃ (r : P.BoundaryPairing)
        (_hdirection : r.direction = .opposite)
        (hcompatible : r.target.dart = r.source.dart.flip)
        (k : Fin (dartWeight a r.source.dart)),
        q = expandedPairingOpposite P a r hcompatible k) := by
  let e := expandedOccurrenceEquiv P a
  let ps : ExpandedSourcePosition P a := e.symm q.source
  let pt : ExpandedSourcePosition P a := e.symm q.target
  have hps : expandedOccurrenceAt P a ps = q.source :=
    e.apply_symm_apply q.source
  have hpt : expandedOccurrenceAt P a pt = q.target :=
    e.apply_symm_apply q.target
  have hqedge : q.target.edge = q.source.edge :=
    BoundaryPairing.target_edge_eq_source_edge q
  have hsubedge :
      expandedSubedge a ps.1.dart ps.2 =
        expandedSubedge a pt.1.dart pt.2 := by
    have hqedge' := hqedge
    rw [← hpt, ← hps, expandedOccurrenceAt_edge,
      expandedOccurrenceAt_edge] at hqedge'
    exact hqedge'.symm
  have holdEdge : ps.1.edge = pt.1.edge :=
    sourceEdge_eq_of_expandedSubedge_eq a hsubedge
  have holdNe : ps.1 ≠ pt.1 := by
    intro heq
    have hpEq :=
      expandedSourcePosition_eq_of_fst_eq_of_subedge_eq
        P a ps pt heq hsubedge
    apply q.source_ne_target
    calc
      q.source = expandedOccurrenceAt P a ps := hps.symm
      _ = expandedOccurrenceAt P a pt :=
        congrArg (expandedOccurrenceAt P a) hpEq
      _ = q.target := hpt
  have hsourceInternal : ¬P.IsBoundaryEdge ps.1.edge := by
    intro hb
    apply q.source_not_boundary
    rw [← hps, expandedOccurrenceAt_edge]
    exact
      (isBoundaryEdge_expandedSubedge_iff
        P a ps.1.dart ps.2).2 hb
  obtain ⟨r, hrsource⟩ :=
    validP.exists_pairing_source ps.1 hsourceInternal
  obtain ⟨partner, _hpartner, hunique⟩ :=
    validP.exists_unique_partner ps.1 hsourceInternal
  have hrcondition :
      ps.1 ≠ r.target ∧ r.target.edge = ps.1.edge := by
    constructor
    · intro heq
      apply r.source_ne_target
      rw [hrsource, heq]
    · rw [← hrsource]
      exact BoundaryPairing.target_edge_eq_source_edge r
  have htcondition :
      ps.1 ≠ pt.1 ∧ pt.1.edge = ps.1.edge :=
    ⟨holdNe, holdEdge.symm⟩
  have hrtarget : r.target = pt.1 :=
    (hunique r.target hrcondition).trans
      (hunique pt.1 htcondition).symm
  let k : Fin (dartWeight a r.source.dart) :=
    hrsource.symm ▸ ps.2
  have hposition :
      (⟨r.source, k⟩ : ExpandedSourcePosition P a) = ps := by
    change
      (⟨r.source, hrsource.symm ▸ ps.2⟩ :
        ExpandedSourcePosition P a) = ps
    exact (expandedSourcePosition_mk_transport P a hrsource ps.2).trans
      (Sigma.eta ps)
  let validQ := expand_isSurfaceValid P a validP
  cases hdirection : r.direction with
  | same =>
      have hcompatible : r.target.dart = r.source.dart := by
        simpa only [hdirection] using r.compatible
      let er := expandedPairingSame P a r hcompatible k
      have hersource : er.source = q.source := by
        change
          expandedOccurrenceAt P a ⟨r.source, k⟩ = q.source
        rw [hposition, hps]
      obtain ⟨qpartner, _hqpartner, hqunique⟩ :=
        validQ.exists_unique_partner q.source q.source_not_boundary
      have hercondition :
          q.source ≠ er.target ∧ er.target.edge = q.source.edge := by
        constructor
        · intro heq
          apply er.source_ne_target
          exact hersource.trans heq
        · calc
            er.target.edge = er.source.edge :=
              BoundaryPairing.target_edge_eq_source_edge er
            _ = q.source.edge :=
              congrArg BoundaryOccurrence.edge hersource
      have hqcondition :
          q.source ≠ q.target ∧ q.target.edge = q.source.edge :=
        ⟨q.source_ne_target, hqedge⟩
      have hertarget : er.target = q.target :=
        (hqunique er.target hercondition).trans
          (hqunique q.target hqcondition).symm
      have hdirectionEq : q.direction = er.direction :=
        BoundaryPairing.direction_eq_of_source_target_eq q er
          hersource.symm hertarget.symm
      exact Or.inl
        ⟨r, hdirection, hcompatible, k,
          BoundaryPairing.eq_of_source_target_direction_eq q er
            hersource.symm hertarget.symm hdirectionEq⟩
  | opposite =>
      have hcompatible : r.target.dart = r.source.dart.flip := by
        simpa only [hdirection] using r.compatible
      let er := expandedPairingOpposite P a r hcompatible k
      have hersource : er.source = q.source := by
        change
          expandedOccurrenceAt P a ⟨r.source, k⟩ = q.source
        rw [hposition, hps]
      obtain ⟨qpartner, _hqpartner, hqunique⟩ :=
        validQ.exists_unique_partner q.source q.source_not_boundary
      have hercondition :
          q.source ≠ er.target ∧ er.target.edge = q.source.edge := by
        constructor
        · intro heq
          apply er.source_ne_target
          exact hersource.trans heq
        · calc
            er.target.edge = er.source.edge :=
              BoundaryPairing.target_edge_eq_source_edge er
            _ = q.source.edge :=
              congrArg BoundaryOccurrence.edge hersource
      have hqcondition :
          q.source ≠ q.target ∧ q.target.edge = q.source.edge :=
        ⟨q.source_ne_target, hqedge⟩
      have hertarget : er.target = q.target :=
        (hqunique er.target hercondition).trans
          (hqunique q.target hqcondition).symm
      have hdirectionEq : q.direction = er.direction :=
        BoundaryPairing.direction_eq_of_source_target_eq q er
          hersource.symm hertarget.symm
      exact Or.inr
        ⟨r, hdirection, hcompatible, k,
          BoundaryPairing.eq_of_source_target_direction_eq q er
            hersource.symm hertarget.symm hdirectionEq⟩

theorem dartWeight_pos {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    0 < dartWeight a d := by
  unfold dartWeight
  split <;> omega

/-- Convert a target subedge-local parameter back to the original source-side parameter. -/
noncomputable def unexpandParameter {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (k : Fin (dartWeight a d)) (u : unitInterval) : unitInterval :=
  ⟨((k : ℝ) + (u : ℝ)) / dartWeight a d,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) u.property.1)
      (Nat.cast_nonneg _), by
    rw [div_le_one (by exact_mod_cast dartWeight_pos a d)]
    have hk : (k.val : ℝ) + 1 ≤ dartWeight a d := by
      exact_mod_cast k.isLt
    linarith [u.property.2]⟩

@[simp]
theorem unexpandParameter_val {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d))
    (u : unitInterval) :
    (unexpandParameter a d k u : ℝ) =
      ((k : ℝ) + (u : ℝ)) / dartWeight a d :=
  rfl

theorem faceHomeomorph_side_unexpand
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length)
    (k : Fin (dartWeight a ((P.boundary f).get i)))
    (u : unitInterval) :
    faceHomeomorph P a validP f
        (PolygonCell.side i
          (unexpandParameter a ((P.boundary f).get i) k u)) =
      PolygonCell.side (expandedOffsetIndex P a f i k) u := by
  rw [faceHomeomorph_side]
  change
    PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (2 * Real.pi /
              ((expand P a).boundary (faceEquiv P a f)).length *
            (((faceWeights P a f).take i).sum +
              (faceWeights P a f).get
                  (Fin.cast (faceWeights_length P a f).symm i) *
                (unexpandParameter a ((P.boundary f).get i) k u : ℝ)))) =
      PolygonCell.ofCircle
        ((expand P a).boundary (faceEquiv P a f)).length
        (Circle.exp
          (PolygonCell.sideAngle (expandedOffsetIndex P a f i k) u))
  apply congrArg
    (PolygonCell.ofCircle
      ((expand P a).boundary (faceEquiv P a f)).length)
  apply congrArg Circle.exp
  rw [faceWeights_get]
  unfold PolygonCell.sideAngle
  rw [expandedOffsetIndex_val, unexpandParameter_val]
  have hw : (dartWeight a ((P.boundary f).get i) : ℝ) ≠ 0 := by
    exact_mod_cast (dartWeight_pos a ((P.boundary f).get i)).ne'
  push_cast
  field_simp [hw]
  ring

theorem preHomeomorph_occurrenceSide_unexpand
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (p : ExpandedSourcePosition P a)
    (u : unitInterval) :
    preHomeomorph P a validP
        ((P.occurrenceSide p.1).point
          (unexpandParameter a p.1.dart p.2 u)) =
      ((expand P a).occurrenceSide
        (expandedOccurrenceAt P a p)).point u := by
  rcases p with ⟨⟨f, i⟩, k⟩
  change
    (⟨faceEquiv P a f,
        faceHomeomorph P a validP f
          (PolygonCell.side i
            (unexpandParameter a ((P.boundary f).get i) k u))⟩ :
      (expand P a).PolygonalPreRealization) =
      ⟨faceEquiv P a f,
        PolygonCell.side (expandedOffsetIndex P a f i k) u⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact faceHomeomorph_side_unexpand P a validP f i k u

theorem preHomeomorph_symm_expandedOccurrenceAt
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (p : ExpandedSourcePosition P a)
    (u : unitInterval) :
    (preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a p)).point u) =
      (P.occurrenceSide p.1).point
        (unexpandParameter a p.1.dart p.2 u) := by
  apply (preHomeomorph P a validP).injective
  rw [(preHomeomorph P a validP).apply_symm_apply]
  exact (preHomeomorph_occurrenceSide_unexpand P a validP p u).symm

theorem unexpandParameter_cast_eq {n : ℕ} (a : Fin n)
    {d₁ d₂ : SignedDart (Fin n)} (h : d₂ = d₁)
    (k : Fin (dartWeight a d₁)) (u : unitInterval) :
    unexpandParameter a d₂
        (Fin.cast (congrArg (dartWeight a) h.symm) k) u =
      unexpandParameter a d₁ k u := by
  subst d₂
  rfl

theorem unexpandParameter_flip_reverse {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) (k : Fin (dartWeight a d))
    (u : unitInterval) :
    unexpandParameter a d.flip (reverseOffset a d k)
        (unitInterval.symm u) =
      unitInterval.symm (unexpandParameter a d k u) := by
  apply Subtype.ext
  simp only [unexpandParameter_val,
    reverseOffset, Fin.val_cast, Fin.val_rev, dartWeight_flip,
    unitInterval.coe_symm_eq]
  have hk : k.val + 1 ≤ dartWeight a d :=
    k.isLt
  have hw : (dartWeight a d : ℝ) ≠ 0 := by
    exact_mod_cast (dartWeight_pos a d).ne'
  rw [Nat.cast_sub hk]
  push_cast
  field_simp [hw]
  ring

theorem unexpandParameter_samePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart)) (u : unitInterval) :
    unexpandParameter a pairing.target.dart
        (samePairedOffset a pairing hcompatible k) u =
      unexpandParameter a pairing.source.dart k u :=
  unexpandParameter_cast_eq a hcompatible k u

theorem unexpandParameter_oppositePairedOffset
    {P : FiniteCyclicPresentation} (a : P.Edge)
    (pairing : P.BoundaryPairing)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart)) (u : unitInterval) :
    unexpandParameter a pairing.target.dart
        (oppositePairedOffset a pairing hcompatible k)
        (unitInterval.symm u) =
      unitInterval.symm
        (unexpandParameter a pairing.source.dart k u) := by
  exact (unexpandParameter_cast_eq a hcompatible
      (reverseOffset a pairing.source.dart k)
      (unitInterval.symm u)).trans
    (unexpandParameter_flip_reverse a pairing.source.dart k u)

theorem preHomeomorph_symm_expandedPairingSame_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (hdirection : pairing.direction = .same)
    (hcompatible : pairing.target.dart = pairing.source.dart)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        ((expandedPairingSame P a pairing hcompatible k).identification.source.point u))
      ((preHomeomorph P a validP).symm
        ((expandedPairingSame P a pairing hcompatible k).identification.target.point
          ((expandedPairingSame P a pairing hcompatible k).identification.parameter u))) := by
  change
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u))
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a
            ⟨pairing.target,
              samePairedOffset a pairing hcompatible k⟩)).point u))
  rw [preHomeomorph_symm_expandedOccurrenceAt,
    preHomeomorph_symm_expandedOccurrenceAt,
    unexpandParameter_samePairedOffset]
  change
    P.PolygonalGluingRel validP
      ((P.occurrenceSide pairing.source).point
        (unexpandParameter a pairing.source.dart k u))
      ((P.occurrenceSide pairing.target).point
        (unexpandParameter a pairing.source.dart k u))
  simpa [BoundaryPairing.identification,
      PolygonGluing.Identification.parameter, hdirection,
      PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
    PolygonGluing.related_of_mem pairing.identification
      (pairing_identification_mem validP pairing)
      (unexpandParameter a pairing.source.dart k u)

theorem preHomeomorph_symm_expandedPairingOpposite_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (hdirection : pairing.direction = .opposite)
    (hcompatible : pairing.target.dart = pairing.source.dart.flip)
    (k : Fin (dartWeight a pairing.source.dart))
    (u : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        ((expandedPairingOpposite P a pairing hcompatible k).identification.source.point u))
      ((preHomeomorph P a validP).symm
        ((expandedPairingOpposite P a pairing hcompatible k).identification.target.point
          ((expandedPairingOpposite P a pairing hcompatible k).identification.parameter u))) := by
  change
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a ⟨pairing.source, k⟩)).point u))
      ((preHomeomorph P a validP).symm
        (((expand P a).occurrenceSide
          (expandedOccurrenceAt P a
            ⟨pairing.target,
              oppositePairedOffset a pairing hcompatible k⟩)).point
          (unitInterval.symm u)))
  rw [preHomeomorph_symm_expandedOccurrenceAt,
    preHomeomorph_symm_expandedOccurrenceAt,
    unexpandParameter_oppositePairedOffset]
  change
    P.PolygonalGluingRel validP
      ((P.occurrenceSide pairing.source).point
        (unexpandParameter a pairing.source.dart k u))
      ((P.occurrenceSide pairing.target).point
        (unitInterval.symm
          (unexpandParameter a pairing.source.dart k u)))
  simpa [BoundaryPairing.identification,
      PolygonGluing.Identification.parameter, hdirection,
      PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
    PolygonGluing.related_of_mem pairing.identification
      (pairing_identification_mem validP pairing)
      (unexpandParameter a pairing.source.dart k u)

/-! ### Descent to the faithful polygonal quotient -/

/-- The inverse facewise map sends every target gluing generator into the source generated
relation. -/
theorem preHomeomorph_symm_generator_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (pairing : (expand P a).BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm
        (pairing.identification.source.point t))
      ((preHomeomorph P a validP).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rcases exists_eq_expandedPairing P a validP pairing with
      ⟨r, hdirection, hcompatible, k, rfl⟩ |
      ⟨r, hdirection, hcompatible, k, rfl⟩
  · exact preHomeomorph_symm_expandedPairingSame_generator_related
      P a validP r hdirection hcompatible k t
  · exact preHomeomorph_symm_expandedPairingOpposite_generator_related
      P a validP r hdirection hcompatible k t

/-- The facewise P1 homeomorphism preserves the complete source gluing relation. -/
theorem preHomeomorph_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
      (preHomeomorph P a validP x) (preHomeomorph P a validP y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact preHomeomorph_generator_related P a validP pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The inverse facewise P1 homeomorphism preserves the complete target gluing relation. -/
theorem preHomeomorph_symm_related
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid)
    {x y : (expand P a).PolygonalPreRealization}
    (hxy :
      (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP) x y) :
    P.PolygonalGluingRel validP
      ((preHomeomorph P a validP).symm x)
      ((preHomeomorph P a validP).symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((expand P a).polygonalIdentifications
        (expand_isSurfaceValid P a validP))) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact preHomeomorph_symm_generator_related P a validP pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The selected P1 pre-realization homeomorphism identifies the two generated gluing relations
exactly. -/
theorem preHomeomorph_related_iff
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      (expand P a).PolygonalGluingRel (expand_isSurfaceValid P a validP)
        (preHomeomorph P a validP x) (preHomeomorph P a validP y) := by
  constructor
  · exact preHomeomorph_related P a validP
  · intro hxy
    simpa only [Homeomorph.symm_apply_apply] using
      preHomeomorph_symm_related P a validP hxy

/-- Canonical P1 expansion preserves the faithful polygonal realization. -/
noncomputable def realizationHomeomorph
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ
      (expand P a).PolygonalRealization (expand_isSurfaceValid P a validP) :=
  PolygonGluing.realizationCongr (preHomeomorph P a validP)
    (preHomeomorph_related_iff P a validP)

/-- Propositional realization-invariance form for the canonical P1 expansion. -/
theorem polygonallyEquivalent
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (expand P a) validP
      (expand_isSurfaceValid P a validP) :=
  ⟨realizationHomeomorph P a validP⟩

end P1

/-- Every P1 subdivision, including signed relabeling of the canonical target, preserves the
faithful polygonal realization. -/
theorem P1Subdivision.preservesPolygonalRealization :
    P1Subdivision.PreservesPolygonalRealization := by
  intro P Q hPQ validP validQ
  rcases hPQ with ⟨a, ⟨e⟩⟩
  let validExpand := P1.expand_isSurfaceValid P a validP
  exact (P1.polygonallyEquivalent P a validP).trans
    (e.polygonallyEquivalent validExpand validQ)

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification22_block_05
/- END ClassificationOfSurfaces.FiniteCyclicP1Realization -/
