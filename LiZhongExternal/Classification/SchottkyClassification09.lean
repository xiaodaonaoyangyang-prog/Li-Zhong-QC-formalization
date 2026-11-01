/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification09: pinned classification sources (upstream e3c7230f); see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification07
import LiZhongExternal.Classification.SchottkyClassification08
import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LiZhongExternal.Classification.SchottkyClassification06
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Instances.AddCircle.Real

/- BEGIN ClassificationOfSurfaces.Moise.AdaptiveTileComplex | cc7497ba1325e1f8e0099b54866f0c09db52388d6945bbddd92be8db81424c24 -/
noncomputable section

section schottkyclassification09_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite conforming meshes on adaptive open-complex tiles

An adaptive tile is a closed face of an iterated midpoint subdivision, transported to the
original intrinsic realization.  Its faithful subdivision chart followed by
`facePlaneHomeomorph` identifies it with the standard plane triangle.  We mark every vertex of
every touching adaptive tile on its boundary, refine the standard boundary graph at those
marks, and cone that graph to an interior point.  This file packages the resulting honest finite
plane complex for one tile.  The next layer proves that the transported tile complexes agree on
overlaps and takes their locally finite union.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- A transported adaptive tile, as a closed subspace of the original realization. -/
abbrev AdaptiveClosedFace (t : K.AdaptiveFace U) :=
  {p : K.realization // p ∈ K.adaptiveFaceCarrier U t}

theorem levelFaceHomeoSymm_mem_carrier {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    (K.safeSubdivision n).homeo.symm p ∈
      (K.safeSubdivision n).refined.faceCarrier t.1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  simpa only [(K.safeSubdivision n).homeo.symm_apply_apply] using hx

/-- Remove the faithful subdivision transport from one adaptive tile. -/
noncomputable def adaptiveFaceSourceHomeomorph (t : K.AdaptiveFace U) :
    K.AdaptiveClosedFace U t ≃ₜ
      (K.safeSubdivision t.1).refined.ClosedFace t.2.1 where
  toFun p := ⟨(K.safeSubdivision t.1).homeo.symm p.1,
    K.levelFaceHomeoSymm_mem_carrier t.2.1 p.2⟩
  invFun x := ⟨(K.safeSubdivision t.1).homeo x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (K.safeSubdivision t.1).homeo.apply_symm_apply p.1
  right_inv x := by
    apply Subtype.ext
    exact (K.safeSubdivision t.1).homeo.symm_apply_apply x.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (K.safeSubdivision t.1).homeo.symm.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (K.safeSubdivision t.1).homeo.continuous.comp continuous_subtype_val

/-- The canonical standard-plane chart of an adaptive tile. -/
noncomputable def adaptiveFacePlaneHomeomorph (t : K.AdaptiveFace U) :
    K.AdaptiveClosedFace U t ≃ₜ standardTrianglePlaneComplex.support :=
  (K.adaptiveFaceSourceHomeomorph U t).trans
    ((K.safeSubdivision t.1).refined.facePlaneHomeomorph t.2.1)

/-- A point on an adaptive edge pulls back to the corresponding edge of the refined face. -/
theorem homeo_symm_mem_levelFaceEdgeCarrier {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) {p : K.realization} (hp : p ∈ K.levelFaceEdgeCarrier t i) :
    (K.safeSubdivision n).homeo.symm p ∈
      (K.safeSubdivision n).refined.faceCarrier
        ((K.safeSubdivision n).refined.faceEdge t i).1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  simpa only [(K.safeSubdivision n).homeo.symm_apply_apply] using hx

/-- The finite type of resolved boundary points of one adaptive tile. -/
abbrev AdaptiveBoundaryVertex (hU : IsOpen U) (t : K.AdaptiveFace U) :=
  {p : K.realization // p ∈ K.boundaryVertices U hU t}

/-- A resolved boundary point in the standard plane chart of its adaptive tile. -/
noncomputable def adaptiveBoundaryPlanePoint (hU : IsOpen U)
    (t : K.AdaptiveFace U) (p : K.AdaptiveBoundaryVertex U hU t) : Plane :=
  K.adaptiveFacePlaneHomeomorph U t
    ⟨p.1, ((K.mem_boundaryVertices_iff U hU t p.1).mp p.2).1⟩

/-- Every resolved boundary mark lies in the standard triangle's one-skeleton. -/
theorem adaptiveBoundaryPlanePoint_mem_standardOneSkeleton (hU : IsOpen U)
    (t : K.AdaptiveFace U) (p : K.AdaptiveBoundaryVertex U hU t) :
    K.adaptiveBoundaryPlanePoint U hU t p ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  have hpCarrier : p.1 ∈ K.adaptiveFaceCarrier U t :=
    ((K.mem_boundaryVertices_iff U hU t p.1).mp p.2).1
  have hpNot : p.1 ∉ K.adaptiveFaceRelInterior U t :=
    K.boundaryVertices_not_mem_relInterior U hU t p.2
  obtain ⟨i, hpEdge⟩ :=
    K.exists_levelFaceEdge_of_mem_not_relInterior t.2.1 hpCarrier hpNot
  rw [standardTriangle_oneSkeleton_support]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [← (K.safeSubdivision t.1).refined.facePlaneHomeomorph_image_edge t.2.1 i]
  let x : (K.safeSubdivision t.1).refined.ClosedFace t.2.1 :=
    ⟨(K.safeSubdivision t.1).homeo.symm p.1,
      K.levelFaceHomeoSymm_mem_carrier t.2.1 hpCarrier⟩
  refine ⟨x, K.homeo_symm_mem_levelFaceEdgeCarrier t.2.1 i hpEdge, ?_⟩
  rfl

/-- The standard boundary graph refined at every touching-tile vertex. -/
noncomputable def adaptiveBoundarySubdivision (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.adaptiveBoundaryPlanePoint U hU t)

theorem adaptiveBoundarySubdivision_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveBoundarySubdivision U hU t).support =
      frontier standardTrianglePlaneComplex.support := by
  rw [adaptiveBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.adaptiveBoundaryPlanePoint U hU t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    standardTriangle_oneSkeleton_support, standardTriangleCircle_carrier,
    standardTrianglePlaneComplex_support]

/-- Remove any arrangement vertices not used by the refined boundary graph. -/
noncomputable def adaptiveBoundaryGraph (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  (K.adaptiveBoundarySubdivision U hU t).used

theorem adaptiveBoundaryGraph_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveBoundaryGraph U hU t).support =
      frontier standardTrianglePlaneComplex.support := by
  rw [adaptiveBoundaryGraph, PlaneComplex.used_support,
    K.adaptiveBoundarySubdivision_support U hU t]

theorem adaptiveBoundaryGraph_isGraph (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    ∀ s ∈ (K.adaptiveBoundaryGraph U hU t).simplexes, s.card ≤ 2 := by
  intro s hs
  let L := K.adaptiveBoundarySubdivision U hU t
  have hsub : L.Subdivides standardTrianglePlaneComplex.oneSkeleton :=
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
      (K.adaptiveBoundaryPlanePoint U hU t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph
  have hsL : s.map L.usedEmbedding ∈ L.simplexes := L.mem_usedSimplexes.mp hs
  obtain ⟨u, hu, hsu⟩ := hsub.2 _ hsL
  have hcard := PlaneComplex.card_le_two_of_cellCarrier_subset_face hsL hu
    (standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph u hu) hsu
  calc
    s.card = (s.map L.usedEmbedding).card := (Finset.card_map L.usedEmbedding).symm
    _ ≤ 2 := hcard

/-- Exact support on the polygonal frontier rules out isolated used vertices: every boundary
vertex belongs to a two-vertex face. -/
theorem adaptiveBoundaryGraph_vertex_mem_edge (hU : IsOpen U)
    (t : K.AdaptiveFace U) (v : (K.adaptiveBoundaryGraph U hU t).Vertex) :
    ∃ e ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
      v ∈ e ∧ e.card = 2 := by
  classical
  let G := K.adaptiveBoundaryGraph U hU t
  have hvFace : ({v} : Finset G.Vertex) ∈ G.simplexes :=
    (K.adaptiveBoundarySubdivision U hU t).used_vertex_face v
  have hvCarrier : G.position v ∈ G.cellCarrier ({v} : Finset G.Vertex) := by
    rw [PlaneComplex.cellCarrier]
    exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, rfl⟩
  by_contra hno
  push Not at hno
  let other : Set Plane := ⋃ s : {s : Finset G.Vertex // s ∈ G.simplexes ∧ s ≠ {v}},
    G.cellCarrier s.1
  have hpNot : G.position v ∉ other := by
    intro hp
    obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hp
    have hinter : G.position v ∈ G.cellCarrier (({v} : Finset G.Vertex) ∩ s.1) := by
      change G.position v ∈ convexHull ℝ
        (G.position '' ((({v} : Finset G.Vertex) ∩ s.1 : Finset G.Vertex) : Set G.Vertex))
      rw [← G.face_inter ({v} : Finset G.Vertex) hvFace s.1 s.2.1]
      exact ⟨hvCarrier, hps⟩
    have hvs : v ∈ s.1 := by
      by_contra hvs
      have hempty : ({v} : Finset G.Vertex) ∩ s.1 = ∅ := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false]
        rintro ⟨rfl, hw⟩
        exact hvs hw
      rw [hempty, PlaneComplex.cellCarrier] at hinter
      simp at hinter
    have hsle := K.adaptiveBoundaryGraph_isGraph U hU t s.1 s.2.1
    have hstwo : s.1.card = 2 := by
      have hsone : 1 ≤ s.1.card := Finset.one_le_card.mpr ⟨v, hvs⟩
      have hsneone : s.1.card ≠ 1 := by
        intro hsone'
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsone'
        have hva : v = a := Finset.mem_singleton.mp (ha ▸ hvs)
        have hsingle : s.1 = {v} := by simpa only [hva] using ha
        exact s.2.2 hsingle
      omega
    exact hno s.1 s.2.1 hvs hstwo
  have hotherClosed : IsClosed other := by
    apply isClosed_iUnion_of_finite
    intro s
    exact (G.isCompact_cellCarrier s.1).isClosed
  have hpOpen : G.position v ∈ otherᶜ := Set.mem_compl hpNot
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hotherClosed.isOpen_compl
    (G.position v) hpOpen
  have hpSupport : G.position v ∈ G.support := G.cellCarrier_subset_support hvFace hvCarrier
  have hpFrontier : G.position v ∈ frontier standardTrianglePlaneComplex.support := by
    rw [← K.adaptiveBoundaryGraph_support U hU t]
    exact hpSupport
  have hpCircle : G.position v ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardTrianglePlaneComplex_support] using hpFrontier
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpCircle
  change ZMod 3 at i
  let a := standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1))
  let b := standardTriangleVertex ((ZMod.finEquiv 3).symm i)
  have hab : b ≠ a := by
    apply standardTriangleVertex_injective.ne
    exact (ZMod.finEquiv 3).symm.injective.ne
      ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  let q := if h : G.position v ≠ a then a else b
  have hpq : G.position v ≠ q := by
    dsimp only [q]
    split_ifs with h
    · exact h
    · intro hp
      apply hab
      exact hp.symm.trans (not_ne_iff.mp h)
  have hqSide : q ∈ standardTriangleCircle.edgeSegment i := by
    dsimp only [q, a, b]
    split_ifs
    · exact right_mem_segment ℝ _ _
    · exact left_mem_segment ℝ _ _
  have hpqSide : segment ℝ (G.position v) q ⊆
      standardTriangleCircle.edgeSegment i :=
    (convex_segment _ _).segment_subset hpi hqSide
  obtain ⟨z, hzOpen, hzBall⟩ := exists_mem_openSegment_inter_ball hpq hε
  have hzSide : z ∈ standardTriangleCircle.edgeSegment i :=
    hpqSide (openSegment_subset_segment ℝ _ _ hzOpen)
  have hzFrontier : z ∈ frontier standardTrianglePlaneComplex.support := by
    have hzCircle : z ∈ standardTriangleCircle.carrier :=
      Set.mem_iUnion.mpr ⟨i, hzSide⟩
    rw [standardTriangleCircle_carrier] at hzCircle
    simpa only [standardTrianglePlaneComplex_support] using hzCircle
  have hzSupport : z ∈ G.support := by
    rw [K.adaptiveBoundaryGraph_support U hU t]
    exact hzFrontier
  rw [PlaneComplex.support] at hzSupport
  simp only [Set.mem_iUnion] at hzSupport
  obtain ⟨s, hs, hzs⟩ := hzSupport
  by_cases hsv : s = {v}
  · subst s
    have hzv : z = G.position v := by
      simpa [PlaneComplex.cellCarrier] using hzs
    exact hpq (left_mem_openSegment_iff.mp (hzv ▸ hzOpen))
  · have hzOther : z ∈ other := Set.mem_iUnion.mpr ⟨⟨s, hs, hsv⟩, hzs⟩
    exact (hball hzBall) hzOther

/-- Every simplex of the boundary graph is contained in an edge. -/
theorem adaptiveBoundaryGraph_isPureOne (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    ∀ s ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
      ∃ e ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
        s ⊆ e ∧ e.card = 2 := by
  intro s hs
  have hspos : 0 < s.card := Finset.card_pos.mpr
    ((K.adaptiveBoundaryGraph U hU t).nonempty_of_mem s hs)
  have hsle := K.adaptiveBoundaryGraph_isGraph U hU t s hs
  have hscases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hscases with hscard | hscard
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
    obtain ⟨e, he, hve, hecard⟩ :=
      K.adaptiveBoundaryGraph_vertex_mem_edge U hU t v
    exact ⟨e, he, Finset.singleton_subset_iff.mpr hve, hecard⟩
  · exact ⟨s, hs, subset_rfl, hscard⟩

/-- A fixed interior point of the standard triangle, used as every tile's cone vertex. -/
noncomputable def standardAdaptiveConePoint : Plane :=
  Classical.choose standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty

theorem standardAdaptiveConePoint_mem_interior :
    standardAdaptiveConePoint ∈ interior standardTrianglePlaneComplex.support :=
  Classical.choose_spec standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty

theorem standardAdaptiveConePoint_not_mem_boundaryGraph_range (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    standardAdaptiveConePoint ∉ Set.range (K.adaptiveBoundaryGraph U hU t).position := by
  rintro ⟨v, hv⟩
  have hvSupport : (K.adaptiveBoundaryGraph U hU t).position v ∈
      (K.adaptiveBoundaryGraph U hU t).support := by
    exact (K.adaptiveBoundaryGraph U hU t).cellCarrier_subset_support
      ((K.adaptiveBoundarySubdivision U hU t).used_vertex_face v)
      (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, rfl⟩)
  rw [K.adaptiveBoundaryGraph_support U hU t, hv] at hvSupport
  exact (disjoint_interior_frontier (s := standardTrianglePlaneComplex.support)).le_bot
    ⟨standardAdaptiveConePoint_mem_interior, hvSupport⟩

/-- The finite cone triangulation of one adaptive tile in standard plane coordinates. -/
noncomputable def adaptiveTilePlaneComplex (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  (K.adaptiveBoundaryGraph U hU t).cone
    standardTrianglePlaneComplex.support
    standardTrianglePlaneComplex_isTriangle.convex
    standardAdaptiveConePoint
    standardAdaptiveConePoint_mem_interior
    (K.standardAdaptiveConePoint_not_mem_boundaryGraph_range U hU t)
    (K.adaptiveBoundaryGraph_isGraph U hU t)
    (K.adaptiveBoundaryGraph_support U hU t)

theorem adaptiveTilePlaneComplex_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support =
      standardTrianglePlaneComplex.support := by
  apply (K.adaptiveBoundaryGraph U hU t).cone_support_eq
    standardTrianglePlaneComplex.support
    standardTrianglePlaneComplex_isTriangle.convex
    standardTrianglePlaneComplex_isTriangle.isCompact
    standardAdaptiveConePoint
    standardAdaptiveConePoint_mem_interior
    (K.standardAdaptiveConePoint_not_mem_boundaryGraph_range U hU t)
    (K.adaptiveBoundaryGraph_isGraph U hU t)
    (K.adaptiveBoundaryGraph_support U hU t)
    standardTrianglePlaneComplex_isTriangle.frontier_nonempty

/-- Coning a pure boundary graph produces a pure two-dimensional tile complex. -/
theorem adaptiveTilePlaneComplex_isPure2 (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).IsPure2 := by
  let G := K.adaptiveBoundaryGraph U hU t
  change ∀ s ∈ G.coneSimplexes,
    ∃ u ∈ G.coneSimplexes, s ⊆ u ∧ u.card = 3
  intro s hs
  obtain ⟨hsne, b, hb, hsb⟩ := G.mem_coneSimplexes_iff.mp hs
  obtain ⟨e, he, hbe, hecard⟩ :=
    K.adaptiveBoundaryGraph_isPureOne U hU t b hb
  let τ : Finset (Option G.Vertex) := insert none (G.liftFace e)
  refine ⟨τ, ?_, ?_, ?_⟩
  · apply G.mem_coneSimplexes_iff.mpr
    exact ⟨⟨none, Finset.mem_insert_self none (G.liftFace e)⟩,
      e, he, subset_rfl⟩
  · intro z hz
    have hzParent := hsb hz
    cases z with
    | none => exact Finset.mem_insert_self none (G.liftFace e)
    | some z =>
        apply Finset.mem_insert_of_mem
        change some z ∈ e.map Function.Embedding.some
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        apply hbe
        have : some z ∈ G.liftFace b := by
          simpa only [Option.some.injEq, Finset.mem_insert, Option.some_ne_none,
            false_or] using hzParent
        simpa [PlaneComplex.liftFace] using this
  · have hnone : none ∉ G.liftFace e := by simp [PlaneComplex.liftFace]
    dsimp only [τ]
    calc
      (insert none (G.liftFace e)).card = (G.liftFace e).card + 1 :=
        Finset.card_insert_of_notMem hnone
      _ = e.card + 1 := by simp [PlaneComplex.liftFace]
      _ = 3 := by omega

/-- Identify a tile cone's support with the corresponding adaptive closed face. -/
noncomputable def adaptiveTileSupportHomeomorph (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support ≃ₜ K.AdaptiveClosedFace U t :=
  (Homeomorph.setCongr (K.adaptiveTilePlaneComplex_support U hU t)).trans
    (K.adaptiveFacePlaneHomeomorph U t).symm

/-- Embed a tile cone support into the open subspace. -/
noncomputable def adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support → U :=
  fun p ↦ ⟨(K.adaptiveTileSupportHomeomorph U hU t p).1,
    K.adaptiveFaceCarrier_subset U t
      (K.adaptiveTileSupportHomeomorph U hU t p).2⟩

theorem isEmbedding_adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    _root_.Topology.IsEmbedding (K.adaptiveTileSupportEmbed U hU t) := by
  let e : K.AdaptiveClosedFace U t → U := fun p ↦
    ⟨p.1, K.adaptiveFaceCarrier_subset U t p.2⟩
  have he : _root_.Topology.IsEmbedding e :=
    _root_.Topology.IsEmbedding.subtypeVal.codRestrict U
      (fun p ↦ K.adaptiveFaceCarrier_subset U t p.2)
  unfold adaptiveTileSupportEmbed
  change _root_.Topology.IsEmbedding
    (e ∘ (K.adaptiveTileSupportHomeomorph U hU t))
  exact he.comp (K.adaptiveTileSupportHomeomorph U hU t).isEmbedding

theorem range_adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    Set.range (K.adaptiveTileSupportEmbed U hU t) =
      K.adaptiveFaceCarrierInOpen U t := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, rfl⟩
    exact (K.adaptiveTileSupportHomeomorph U hU t q).2
  · intro p hp
    let q : K.AdaptiveClosedFace U t := ⟨p.1, hp⟩
    let z := (K.adaptiveTileSupportHomeomorph U hU t).symm q
    refine ⟨z, ?_⟩
    change (⟨((K.adaptiveTileSupportHomeomorph U hU t) z).1,
      K.adaptiveFaceCarrier_subset U t
        ((K.adaptiveTileSupportHomeomorph U hU t) z).2⟩ : U) = p
    apply Subtype.ext
    have hzq :
        ((K.adaptiveTileSupportHomeomorph U hU t) z).1 = q.1 := by
      exact congrArg
        (fun x : K.AdaptiveClosedFace U t ↦ x.1)
        ((K.adaptiveTileSupportHomeomorph U hU t).apply_symm_apply q)
    exact hzq

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification09_block_01
/- END ClassificationOfSurfaces.Moise.AdaptiveTileComplex -/

/- BEGIN ClassificationOfSurfaces.Moise.Brouwer | edb39f07609cefde882196306cbe572631c0a9eba45d8548e7ceaaefa7dd62b8 -/
section schottkyclassification09_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Brouwer's fixed-point theorem for the plane disk

This file derives Brouwer's fixed-point theorem for the closed unit disk in `Plane` from
`no_retraction_planeClosedUnitBall`.

If a continuous self-map `f` of the disk had no fixed point, the ray starting at `f x` and
passing through `x` would meet the unit sphere in a continuously varying point.  The positive
root of the resulting quadratic equation gives this intersection explicitly.  On the unit
sphere that root is `1`, so the construction would be a retraction of the disk onto its boundary,
contradicting `no_retraction_planeClosedUnitBall`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped InnerProductSpace

/-- The scale at which the ray from `p` through `x` meets the unit sphere.  Its intended use is
when `p` lies in the unit ball and `p ≠ x`. -/
noncomputable def fixedPointRayScale (p x : Plane) : ℝ :=
  let d := x - p
  let a := ⟪d, d⟫_ℝ
  let b := ⟪p, d⟫_ℝ
  (-b + Real.sqrt (b ^ 2 + a * (1 - ⟪p, p⟫_ℝ))) / a

private lemma fixedPointRayScale_mul_inner (p x : Plane) (hpx : p ≠ x) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x =
      -⟪p, x - p⟫_ℝ + Real.sqrt
        (⟪p, x - p⟫_ℝ ^ 2 + ⟪x - p, x - p⟫_ℝ * (1 - ⟪p, p⟫_ℝ)) := by
  rw [fixedPointRayScale]
  have hdenom : ⟪x - p, x - p⟫_ℝ ≠ 0 :=
    inner_self_ne_zero.mpr (sub_ne_zero.mpr hpx.symm)
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hdenom]

private lemma quadratic_root (a b c : ℝ) (ha : 0 < a) (hc : c ≤ 1) :
    a * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) ^ 2 +
        2 * b * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) + c = 1 := by
  let D := b ^ 2 + a * (1 - c)
  let t := (-b + Real.sqrt D) / a
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have ht : a * t = -b + Real.sqrt D := by
    dsimp [t]
    field_simp [ha.ne']
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  change a * t ^ 2 + 2 * b * t + c = 1
  have htb : a * t + b = Real.sqrt D := by
    linarith
  calc
    a * t ^ 2 + 2 * b * t + c = ((a * t + b) ^ 2 - b ^ 2) / a + c := by
      field_simp [ha.ne']
      ring
    _ = (D - b ^ 2) / a + c := by rw [htb, hsqrt]
    _ = 1 := by
      dsimp [D]
      field_simp [ha.ne']
      ring

private lemma fixedPointRayScale_quadratic (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x ^ 2 +
        2 * ⟪p, x - p⟫_ℝ * fixedPointRayScale p x + ⟪p, p⟫_ℝ = 1 := by
  have ha : 0 < ⟪x - p, x - p⟫_ℝ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpx.symm)
  have hc : ⟪p, p⟫_ℝ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg p]
  simpa [fixedPointRayScale] using quadratic_root
    ⟪x - p, x - p⟫_ℝ ⟪p, x - p⟫_ℝ ⟪p, p⟫_ℝ ha hc

private lemma fixedPointRayEndpoint_mem_sphere (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    p + fixedPointRayScale p x • (x - p) ∈ Metric.sphere (0 : Plane) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hquad := fixedPointRayScale_quadratic p x hpx hp
  have hsq : ‖p + fixedPointRayScale p x • (x - p)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm p (x - p)]
    nlinarith [hquad]
  nlinarith [norm_nonneg (p + fixedPointRayScale p x • (x - p))]

private lemma fixedPointRayScale_eq_one_of_mem_sphere (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) (hx : ‖x‖ = 1) :
    fixedPointRayScale p x = 1 := by
  let a := ⟪x - p, x - p⟫_ℝ
  let b := ⟪p, x - p⟫_ℝ
  let c := ⟪p, p⟫_ℝ
  let t := fixedPointRayScale p x
  have hroot : a * t ^ 2 + 2 * b * t + c = 1 := by
    simpa [a, b, c, t] using fixedPointRayScale_quadratic p x hpx hp
  have hxinner : ⟪x, x⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hx]
    norm_num
  have hrootOne : a + 2 * b + c = 1 := by
    rw [show x = p + (x - p) by abel] at hxinner
    simp only [inner_add_left, inner_add_right] at hxinner
    rw [real_inner_comm p (x - p)] at hxinner
    dsimp only [a, b, c]
    nlinarith [hxinner]
  let s : EuclideanGeometry.Sphere Plane := ⟨0, 1⟩
  have hxmem : x ∈ s := by
    change dist x (0 : Plane) = 1
    simpa [dist_zero_right] using hx
  have hple : dist p s.center ≤ s.radius := by
    simpa [s, dist_zero_right] using hp
  have hgeom : 0 < ⟪x - p, x⟫_ℝ := by
    simpa [s] using
      (EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius hxmem hple).resolve_right hpx.symm
  have hab : 0 < a + b := by
    have hinner : ⟪x - p, x⟫_ℝ = a + b := by
      calc
        ⟪x - p, x⟫_ℝ = ⟪x - p, (x - p) + p⟫_ℝ := by
          congr 1
          abel
        _ = a + b := by
          rw [inner_add_right, real_inner_comm p (x - p)]
    rwa [hinner] at hgeom
  have ht : a * t = -b + Real.sqrt (b ^ 2 + a * (1 - c)) := by
    simpa [a, b, c, t] using fixedPointRayScale_mul_inner p x hpx
  have hfactor : 0 < a * (t + 1) + 2 * b := by
    nlinarith [Real.sqrt_nonneg (b ^ 2 + a * (1 - c))]
  have hprod : (t - 1) * (a * (t + 1) + 2 * b) = 0 := by
    nlinarith [hroot, hrootOne]
  have htOne : t = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact False.elim (hfactor.ne' h)
  exact htOne

private lemma continuous_fixedPointRayScale
    (f : Metric.closedBall (0 : Plane) 1 → Metric.closedBall (0 : Plane) 1)
    (hf : Continuous f) (hne : ∀ x, f x ≠ x) :
    Continuous fun x ↦ fixedPointRayScale (f x).1 x.1 := by
  have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
  have hxv : Continuous fun x : Metric.closedBall (0 : Plane) 1 ↦ x.1 :=
    continuous_subtype_val
  have hd : Continuous fun x ↦ x.1 - (f x).1 := hxv.sub hfv
  have ha : Continuous fun x ↦ ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ := hd.inner hd
  have hb : Continuous fun x ↦ ⟪(f x).1, x.1 - (f x).1⟫_ℝ := hfv.inner hd
  have hc : Continuous fun x ↦ ⟪(f x).1, (f x).1⟫_ℝ := hfv.inner hfv
  have hdisc : Continuous fun x ↦
      ⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ * (1 - ⟪(f x).1, (f x).1⟫_ℝ) :=
    hb.pow 2 |>.add (ha.mul (continuous_const.sub hc))
  have hdenom : ∀ x, ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ ≠ 0 := by
    intro x
    apply inner_self_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro h
    apply hne x
    exact Subtype.ext h.symm
  change Continuous fun x ↦
    (-⟪(f x).1, x.1 - (f x).1⟫_ℝ +
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ))) /
      ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ
  have hsqrt : Continuous fun x ↦
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ)) := by
    exact Real.continuous_sqrt.comp hdisc
  exact (hb.neg.add hsqrt).div ha hdenom

/-- Brouwer's fixed-point theorem for the closed unit disk in the Euclidean plane. -/
theorem brouwer_fixed_point_planeClosedUnitBall
    (f : Metric.closedBall (0 : Plane) 1 → Metric.closedBall (0 : Plane) 1)
    (hf : Continuous f) :
    ∃ x, f x = x := by
  by_contra hfixed
  have hne : ∀ x, f x ≠ x := by
    intro x hx
    exact hfixed ⟨x, hx⟩
  let r : Metric.closedBall (0 : Plane) 1 → Metric.sphere (0 : Plane) 1 := fun x ↦
    ⟨(f x).1 + fixedPointRayScale (f x).1 x.1 • (x.1 - (f x).1), by
      apply fixedPointRayEndpoint_mem_sphere
      · intro heq
        apply hne x
        exact Subtype.ext heq
      · have hp := (f x).2
        rw [Metric.mem_closedBall, dist_zero_right] at hp
        exact hp⟩
  apply no_retraction_planeClosedUnitBall
  refine ⟨r, ?_, ?_⟩
  · apply Continuous.subtype_mk
    have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
    have hxv : Continuous fun x : Metric.closedBall (0 : Plane) 1 ↦ x.1 :=
      continuous_subtype_val
    exact hfv.add ((continuous_fixedPointRayScale f hf hne).smul (hxv.sub hfv))
  · intro z
    apply Subtype.ext
    let x : Metric.closedBall (0 : Plane) 1 :=
      ⟨z.1, Metric.mem_closedBall.mpr z.2.le⟩
    have hpx : (f x).1 ≠ z.1 := by
      intro heq
      apply hne x
      exact Subtype.ext heq
    have hp : ‖(f x).1‖ ≤ 1 := by
      have hp := (f x).2
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      exact hp
    have hz : ‖z.1‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp z.2
    have hscale := fixedPointRayScale_eq_one_of_mem_sphere (f x).1 z.1 hpx hp hz
    change (f x).1 + fixedPointRayScale (f x).1 z.1 • (z.1 - (f x).1) = z.1
    rw [hscale, one_smul]
    abel

instance :
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane where
  brouwer_fixed_point := brouwer_fixed_point_planeClosedUnitBall

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification09_block_02
/- END ClassificationOfSurfaces.Moise.Brouwer -/

/- BEGIN ClassificationOfSurfaces.Moise.GraphPolygonalization | 17e2a67a05a1755519cb48569c56e1930a06670c3f988e7f2a78507c31df2a0e -/
section schottkyclassification09_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Simultaneous polygonalization of finite embedded plane graphs

This file formalizes the separation part of Moise Chapter 6, Theorem 2.  The first construction
chooses the disjoint circular regions around graph vertices from Moise's Figure 6.1.  Later
constructions trim each embedded edge at the last exits from those regions and polygonalize the
remaining pairwise-disjoint compact arcs.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

theorem exists_pos_uniform_fintype' {I : Type*} [Finite I] [Nonempty I]
    (P : I → ℝ → Prop)
    (hP : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P i δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
  classical
  letI := Fintype.ofFinite I
  let values : Finset ℝ := Finset.univ.image fun i => Classical.choose (hP i)
  have hvalues : values.Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨Classical.choose (hP i),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let ε := values.min' hvalues
  have hε : 0 < ε := by
    have hmem : ε ∈ values := Finset.min'_mem values hvalues
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]
    exact (Classical.choose_spec (hP i)).1
  refine ⟨ε, hε, ?_⟩
  intro i δ hδ hδε
  apply (Classical.choose_spec (hP i)).2 δ hδ
  exact hδε.trans_le (Finset.min'_le values
    (Classical.choose (hP i)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- The last parameter at which an arc lies in a closed disk. -/
structure LastExitData (γ : ℝ → Plane) (center : Plane) (radius : ℝ) where
  /-- The `parameter` declaration. -/
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  parameter_pos : 0 < parameter
  parameter_lt_one : parameter < 1
  on_sphere : dist (γ parameter) center = radius
  after_exit : ∀ t ∈ Set.Icc (0 : ℝ) 1, parameter < t →
    γ t ∉ Metric.closedBall center radius

theorem exists_lastExitData {γ : ℝ → Plane} {center : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hstart : γ 0 = center) (hfinish : γ 1 ∉ Metric.closedBall center radius) :
    Nonempty (LastExitData γ center radius) := by
  let I := Set.Icc (0 : ℝ) 1
  let γI : I → Plane := I.restrict γ
  have hγI : Continuous γI := hcont.restrict
  let E : Set I := γI ⁻¹' Metric.closedBall center radius
  have hEclosed : IsClosed E := Metric.isClosed_closedBall.preimage hγI
  have hEcompact : IsCompact E := hEclosed.isCompact
  have hEne : E.Nonempty := by
    let z : I := ⟨0, show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num⟩
    refine ⟨z, ?_⟩
    change γ 0 ∈ Metric.closedBall center radius
    rw [hstart, Metric.mem_closedBall, dist_self]
    exact hradius.le
  obtain ⟨t, htE, htGreatest⟩ := hEcompact.exists_isGreatest hEne
  have htmem : t.1 ∈ Set.Icc (0 : ℝ) 1 := t.2
  have htlt : t.1 < 1 := by
    apply lt_of_le_of_ne htmem.2
    intro ht1
    apply hfinish
    change γ t.1 ∈ Metric.closedBall center radius at htE
    rwa [ht1] at htE
  have htpos : 0 < t.1 := by
    have hcont0 := (Metric.continuousWithinAt_iff.mp (hcont 0 (by norm_num)))
      radius hradius
    obtain ⟨δ, hδ, hclose⟩ := hcont0
    let d : ℝ := min (δ / 2) (1 / 2)
    have hd : 0 < d := lt_min (half_pos hδ) (by norm_num)
    have hdδ : d < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
    let dI : I := ⟨d, ⟨hd.le, hd1⟩⟩
    have hdclose : dist (γ d) center < radius := by
      rw [← hstart]
      apply hclose dI.2
      change dist d 0 < δ
      rw [Real.dist_eq, sub_zero, abs_of_pos hd]
      exact hdδ
    have hdE : dI ∈ E := by
      exact Metric.mem_closedBall.mpr (le_of_lt hdclose)
    have hdt : dI ≤ t := htGreatest hdE
    exact hd.trans_le hdt
  have hafter : ∀ u ∈ Set.Icc (0 : ℝ) 1, t.1 < u →
      γ u ∉ Metric.closedBall center radius := by
    intro u hu htu huBall
    let uI : I := ⟨u, hu⟩
    have huE : uI ∈ E := huBall
    exact (not_le_of_gt htu) (htGreatest huE)
  have htsphere : dist (γ t.1) center = radius := by
    have htle : dist (γ t.1) center ≤ radius := by
      exact Metric.mem_closedBall.mp htE
    apply le_antisymm htle
    by_contra hnot
    have htinner : dist (γ t.1) center < radius := lt_of_not_ge hnot
    let ε := radius - dist (γ t.1) center
    have hε : 0 < ε := sub_pos.mpr htinner
    have hct := Metric.continuousWithinAt_iff.mp (hcont t.1 htmem) ε hε
    obtain ⟨δ, hδ, hclose⟩ := hct
    let d : ℝ := min (δ / 2) ((1 - t.1) / 2)
    have hd : 0 < d := lt_min (half_pos hδ) (half_pos (sub_pos.mpr htlt))
    have hdδ : d < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hdend : d ≤ 1 - t.1 :=
      (min_le_right _ _).trans (half_le_self (sub_nonneg.mpr htmem.2))
    let u := t.1 + d
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [u]
        linarith [htmem.1]
      · dsimp [u]
        linarith
    have htu : t.1 < u := by dsimp [u]; linarith
    have hdistut : dist u t.1 < δ := by
      rw [Real.dist_eq]
      have : u - t.1 = d := by simp [u]
      rw [this, abs_of_pos hd]
      exact hdδ
    have hγclose : dist (γ u) (γ t.1) < ε := hclose hu hdistut
    have huinner : dist (γ u) center < radius := by
      calc
        dist (γ u) center ≤ dist (γ u) (γ t.1) + dist (γ t.1) center :=
          dist_triangle _ _ _
        _ < ε + dist (γ t.1) center := by linarith
        _ = radius := by simp [ε]
    exact hafter u hu htu (Metric.mem_closedBall.mpr huinner.le)
  exact ⟨{
    parameter := t.1
    parameter_mem := htmem
    parameter_pos := htpos
    parameter_lt_one := htlt
    on_sphere := htsphere
    after_exit := hafter }⟩

/-- A last exit which may occur at the initial endpoint when the arc starts on the sphere. -/
structure WeakLastExitData (γ : ℝ → Plane) (center : Plane) (radius : ℝ) where
  /-- The `parameter` declaration. -/
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  parameter_lt_one : parameter < 1
  on_sphere : dist (γ parameter) center = radius
  after_exit : ∀ t ∈ Set.Icc (0 : ℝ) 1, parameter < t →
    γ t ∉ Metric.closedBall center radius

theorem exists_weakLastExitData {γ : ℝ → Plane} {center : Plane} {radius : ℝ}
    (_ : 0 < radius) (hcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hstart : dist (γ 0) center = radius)
    (hfinish : γ 1 ∉ Metric.closedBall center radius) :
    Nonempty (WeakLastExitData γ center radius) := by
  let I := Set.Icc (0 : ℝ) 1
  let γI : I → Plane := I.restrict γ
  have hγI : Continuous γI := hcont.restrict
  let E : Set I := γI ⁻¹' Metric.closedBall center radius
  have hEclosed : IsClosed E := Metric.isClosed_closedBall.preimage hγI
  have hEcompact : IsCompact E := hEclosed.isCompact
  have hEne : E.Nonempty := by
    let z : I := ⟨0, by constructor <;> norm_num⟩
    refine ⟨z, ?_⟩
    change γ 0 ∈ Metric.closedBall center radius
    rw [Metric.mem_closedBall, hstart]
  obtain ⟨t, htE, htGreatest⟩ := hEcompact.exists_isGreatest hEne
  have htmem : t.1 ∈ Set.Icc (0 : ℝ) 1 := t.2
  have htlt : t.1 < 1 := by
    apply lt_of_le_of_ne htmem.2
    intro ht1
    apply hfinish
    change γ t.1 ∈ Metric.closedBall center radius at htE
    rwa [ht1] at htE
  have hafter : ∀ u ∈ Set.Icc (0 : ℝ) 1, t.1 < u →
      γ u ∉ Metric.closedBall center radius := by
    intro u hu htu huBall
    let uI : I := ⟨u, hu⟩
    exact (not_le_of_gt htu) (htGreatest (show uI ∈ E from huBall))
  have htsphere : dist (γ t.1) center = radius := by
    have htle : dist (γ t.1) center ≤ radius := Metric.mem_closedBall.mp htE
    apply le_antisymm htle
    by_contra hnot
    have htinner : dist (γ t.1) center < radius := lt_of_not_ge hnot
    let ε := radius - dist (γ t.1) center
    have hε : 0 < ε := sub_pos.mpr htinner
    obtain ⟨δ, hδ, hclose⟩ :=
      Metric.continuousWithinAt_iff.mp (hcont t.1 htmem) ε hε
    let d : ℝ := min (δ / 2) ((1 - t.1) / 2)
    have hd : 0 < d := lt_min (half_pos hδ) (half_pos (sub_pos.mpr htlt))
    have hdδ : d < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hdend : d ≤ 1 - t.1 :=
      (min_le_right _ _).trans (half_le_self (sub_nonneg.mpr htmem.2))
    let u := t.1 + d
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [u]
        linarith [htmem.1]
      · dsimp [u]
        linarith
    have htu : t.1 < u := by dsimp [u]; linarith
    have hdistut : dist u t.1 < δ := by
      rw [Real.dist_eq]
      have : u - t.1 = d := by simp [u]
      rw [this, abs_of_pos hd]
      exact hdδ
    have hγclose : dist (γ u) (γ t.1) < ε := hclose hu hdistut
    have huinner : dist (γ u) center < radius := by
      calc
        dist (γ u) center ≤ dist (γ u) (γ t.1) + dist (γ t.1) center :=
          dist_triangle _ _ _
        _ < ε + dist (γ t.1) center := by linarith
        _ = radius := by simp [ε]
    exact hafter u hu htu (Metric.mem_closedBall.mpr huinner.le)
  exact ⟨{
    parameter := t.1
    parameter_mem := htmem
    parameter_lt_one := htlt
    on_sphere := htsphere
    after_exit := hafter }⟩

/-- Ordered exits of an arc from two disjoint endpoint disks. -/
structure TwoSidedExitData (γ : ℝ → Plane) (first second : Plane) (radius : ℝ) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_one : right < 1
  left_on_sphere : dist (γ left) first = radius
  right_on_sphere : dist (γ right) second = radius
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    γ t ∉ Metric.closedBall first radius
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    γ t ∉ Metric.closedBall second radius

theorem exists_twoSidedExitData {γ : ℝ → Plane} {first second : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hstart : γ 0 = first) (hfinish : γ 1 = second)
    (hdisjoint : Disjoint (Metric.closedBall first radius)
      (Metric.closedBall second radius)) :
    Nonempty (TwoSidedExitData γ first second radius) := by
  have hsecondBall : second ∈ Metric.closedBall second radius := by
    rw [Metric.mem_closedBall, dist_self]
    exact hradius.le
  have hfinishOutside : γ 1 ∉ Metric.closedBall first radius := by
    rw [hfinish]
    intro hfirstBall
    exact Set.disjoint_left.mp hdisjoint hfirstBall hsecondBall
  obtain ⟨L⟩ := exists_lastExitData hradius hcont hstart hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let ρ : ℝ → Plane := fun s => γ (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by
      dsimp [q]
      ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 := mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hqcont : Continuous q := by fun_prop
  have hρcont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) :=
    hcont.comp hqcont.continuousOn hqMaps
  have hρzero : ρ 0 = second := by simp [ρ, q, hfinish]
  have hleftFirstBall : γ a ∈ Metric.closedBall first radius := by
    rw [Metric.mem_closedBall]
    exact L.on_sphere.le
  have hleftOutsideSecond : ρ 1 ∉ Metric.closedBall second radius := by
    have hρone : ρ 1 = γ a := by simp [ρ, q, a]
    rw [hρone]
    exact fun hsecond => Set.disjoint_left.mp hdisjoint hleftFirstBall hsecond
  obtain ⟨R⟩ := exists_lastExitData hradius hρcont hρzero hleftOutsideSecond
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_lt_one]
  have hb1 : b < 1 := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_pos]
  refine ⟨{
    left := a
    right := b
    left_pos := L.parameter_pos
    left_lt_right := hab
    right_lt_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := R.on_sphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hρs : ρ s = γ t := by
    dsimp [ρ, q, s]
    congr 2
    rw [mul_div_cancel₀ (1 - t) (sub_ne_zero.mpr ha1.ne')]
    ring
  rw [← hρs]
  exact R.after_exit s hs hRs

/-- Ordered exits for an arc whose endpoints already lie on the two boundary circles. -/
structure BoundaryExitData (γ : ℝ → Plane) (first second : Plane) (radius : ℝ) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_nonneg : 0 ≤ left
  left_lt_right : left < right
  right_le_one : right ≤ 1
  left_on_sphere : dist (γ left) first = radius
  right_on_sphere : dist (γ right) second = radius
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    γ t ∉ Metric.closedBall first radius
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    γ t ∉ Metric.closedBall second radius

theorem exists_boundaryExitData {γ : ℝ → Plane} {first second : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hstart : dist (γ 0) first = radius) (hfinish : dist (γ 1) second = radius)
    (hdisjoint : Disjoint (Metric.closedBall first radius)
      (Metric.closedBall second radius)) :
    Nonempty (BoundaryExitData γ first second radius) := by
  have hfinishOutside : γ 1 ∉ Metric.closedBall first radius := by
    intro hfirst
    exact Set.disjoint_left.mp hdisjoint hfirst
      (Metric.mem_closedBall.mpr hfinish.le)
  obtain ⟨L⟩ := exists_weakLastExitData hradius hcont hstart hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let ρ : ℝ → Plane := fun s => γ (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by dsimp [q]; ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 := mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hρcont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) := by
    exact hcont.comp (by fun_prop) hqMaps
  have hρstart : dist (ρ 0) second = radius := by simp [ρ, q, hfinish]
  have hρfinishOutside : ρ 1 ∉ Metric.closedBall second radius := by
    have hρone : ρ 1 = γ a := by simp [ρ, q, a]
    rw [hρone]
    intro hsecond
    exact Set.disjoint_left.mp hdisjoint
      (Metric.mem_closedBall.mpr L.on_sphere.le) hsecond
  obtain ⟨R⟩ := exists_weakLastExitData hradius hρcont hρstart hρfinishOutside
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_lt_one]
  have hb1 : b ≤ 1 := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_mem.1]
  refine ⟨{
    left := a
    right := b
    left_nonneg := L.parameter_mem.1
    left_lt_right := hab
    right_le_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := R.on_sphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hρs : ρ s = γ t := by
    dsimp [ρ, q, s]
    congr 2
    rw [mul_div_cancel₀ (1 - t) (sub_ne_zero.mpr ha1.ne')]
    ring
  rw [← hρs]
  exact R.after_exit s hs hRs

/-- Radial segments to two distinct points on the same circle meet only at their center. -/
theorem radial_segments_inter {center p q : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hp : dist p center = radius)
    (hq : dist q center = radius) (hpq : p ≠ q) :
    segment ℝ center p ∩ segment ℝ center q = {center} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxq⟩
    rw [segment_eq_image_lineMap] at hx hxq
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨u, hu, heq⟩ := hxq
    have htu : t = u := by
      have hdistT : dist (AffineMap.lineMap center p t) center = t * radius := by
        rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1,
          dist_comm center p, hp]
      have hdistU : dist (AffineMap.lineMap center q u) center = u * radius := by
        rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hu.1,
          dist_comm center q, hq]
      rw [heq] at hdistU
      nlinarith
    by_cases ht0 : t = 0
    · simp [ht0]
    · exfalso
      apply hpq
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', htu] at heq
      have hsmul : t • (q - center) = t • (p - center) := by
        simpa [htu] using add_right_cancel heq
      have hpqc : p - center = q - center := by
        exact (smul_right_injective Plane ht0 hsmul).symm
      calc
        p = (p - center) + center := by abel
        _ = (q - center) + center := congrArg (fun z => z + center) hpqc
        _ = q := by abel
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- The only point of a radial segment on its outer circle is its endpoint. -/
theorem eq_endpoint_of_mem_radial_segment {center p x : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hp : dist p center = radius)
    (hx : x ∈ segment ℝ center p) (hxsphere : dist x center = radius) : x = p := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hdist : dist (AffineMap.lineMap center p t) center = t * radius := by
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1,
      dist_comm center p, hp]
  have ht1 : t = 1 := by nlinarith
  simp [ht1]

theorem disjoint_radial_segments_away_center {center p q : Plane} {radius : ℝ}
    (hradius : 0 < radius) (hp : dist p center = radius)
    (hq : dist q center = radius) (hpq : p ≠ q) :
    Disjoint (segment ℝ center p \ {center}) (segment ℝ center q \ {center}) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxp, hxc⟩ ⟨hxq, -⟩
  have hx : x ∈ ({center} : Set Plane) := by
    rw [← radial_segments_inter hradius hp hq hpq]
    exact ⟨hxp, hxq⟩
  exact hxc hx

/-- Concatenating two simple paths whose ranges meet only at their common endpoint is simple. -/
theorem Path.trans_injective_of_range_inter {X : Type*} [TopologicalSpace X]
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hinter : Set.range γ ∩ Set.range δ = {y}) :
    Function.Injective (γ.trans δ) := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2 <;>
    simp only [dif_pos, hs, ht] at hst
  · have heq := hγ hst
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    dsimp at hval
    linarith
  · let a : unitInterval := ⟨2 * s,
      (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩
    let b : unitInterval := ⟨2 * t - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
      ⟨⟨a, rfl⟩, ⟨b, hst.symm⟩⟩
    have hjoin : γ a = y := by
      have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
      simpa using this
    have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
    have hb : b = (0 : unitInterval) := hδ (hst.symm.trans (hjoin.trans δ.source.symm))
    apply Subtype.ext
    have ha' := congrArg Subtype.val ha
    have hb' := congrArg Subtype.val hb
    dsimp [a, b] at ha' hb'
    linarith
  · let a : unitInterval := ⟨2 * t,
      (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    let b : unitInterval := ⟨2 * s - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩
    have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
      ⟨⟨a, rfl⟩, ⟨b, hst⟩⟩
    have hjoin : γ a = y := by
      have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
      simpa using this
    have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
    have hb : b = (0 : unitInterval) := hδ (hst.trans (hjoin.trans δ.source.symm))
    apply Subtype.ext
    have ha' := congrArg Subtype.val ha
    have hb' := congrArg Subtype.val hb
    dsimp [a, b] at ha' hb'
    linarith
  · have heq := hδ hst
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    dsimp at hval
    linarith

namespace PlaneComplex

variable (K : PlaneComplex)

private theorem image_cellCarrier_inter {h : Plane → Plane}
    (hinj : Set.InjOn h K.support) {s t : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (ht : t ∈ K.simplexes) :
    h '' K.cellCarrier s ∩ h '' K.cellCarrier t =
      h '' K.cellCarrier (s ∩ t) := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨x, hxs, rfl⟩, z, hzt, hzx⟩
    have hzx' : z = x := hinj (K.cellCarrier_subset_support ht hzt)
      (K.cellCarrier_subset_support hs hxs) hzx
    subst z
    refine ⟨x, ?_, rfl⟩
    have hinter : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa only [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [← hinter]
    exact ⟨hxs, hzt⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, convexHull_mono (Set.image_mono Finset.inter_subset_left) hx, rfl⟩,
      x, convexHull_mono (Set.image_mono Finset.inter_subset_right) hx, rfl⟩

private theorem exists_disjoint_image_face_thickenings {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (hinj : Set.InjOn h K.support)
    {s t : Finset K.Vertex} (hs : s ∈ K.simplexes) (ht : t ∈ K.simplexes)
    (hst : Disjoint s t) :
    ∃ δ : ℝ, 0 < δ ∧
      Disjoint (Metric.thickening δ (h '' K.cellCarrier s))
        (Metric.thickening δ (h '' K.cellCarrier t)) := by
  have hcompactS : IsCompact (h '' K.cellCarrier s) :=
    (K.isCompact_cellCarrier s).image_of_continuousOn
      (hcont.mono (K.cellCarrier_subset_support hs))
  have hcompactT : IsCompact (h '' K.cellCarrier t) :=
    (K.isCompact_cellCarrier t).image_of_continuousOn
      (hcont.mono (K.cellCarrier_subset_support ht))
  have hdisjoint : Disjoint (h '' K.cellCarrier s) (h '' K.cellCarrier t) := by
    rw [Set.disjoint_iff_inter_eq_empty, K.image_cellCarrier_inter hinj hs ht]
    have hinter : s ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hst
    rw [hinter, PlaneComplex.cellCarrier]
    simp
  exact hdisjoint.exists_thickenings hcompactS hcompactT.isClosed

/-- Moise's pairwise-disjoint circular vertex regions, also disjoint from every nonincident
embedded edge. -/
structure VertexDiskControl (h : Plane → Plane) where
  /-- The `radius` declaration. -/
  radius : ℝ
  radius_pos : 0 < radius
  vertices_disjoint : ∀ v w : K.Vertex, v ≠ w →
    Disjoint (Metric.closedBall (h (K.position v)) radius)
      (Metric.closedBall (h (K.position w)) radius)
  avoids_nonincident_edge : ∀ v : K.Vertex, ∀ e : K.EdgeFace, v ∉ e.1 →
    Disjoint (Metric.closedBall (h (K.position v)) radius)
      (Metric.cthickening radius (h '' K.cellCarrier e.1))

/-- The `edgeCurve` declaration. -/
noncomputable def edgeCurve (h : Plane → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) (t : ℝ) : Plane :=
  h (AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) t)

theorem edge_lineMap_mem_support (i : Fin (Fintype.card K.EdgeFace)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) t ∈
      K.support := by
  apply K.cellCarrier_subset_support (K.edgeAt_mem_simplexes i)
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact lineMap_mem_segment ℝ _ _ ht

theorem edgeCurve_continuousOn {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (i : Fin (Fintype.card K.EdgeFace)) :
    ContinuousOn (K.edgeCurve h i) (Set.Icc (0 : ℝ) 1) := by
  apply hcont.comp (AffineMap.lineMap_continuous.continuousOn)
  intro t ht
  exact K.edge_lineMap_mem_support i ht

@[simp] theorem edgeCurve_zero (h : Plane → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeCurve h i 0 = h (K.position (K.edgeFirst i)) := by
  simp [edgeCurve]

@[simp] theorem edgeCurve_one (h : Plane → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeCurve h i 1 = h (K.position (K.edgeSecond i)) := by
  simp [edgeCurve]

/-- The two ordered circle crossings which delimit the central part of an embedded edge. -/
structure EdgeTrimData (h : Plane → Plane) (D : K.VertexDiskControl h)
    (i : Fin (Fintype.card K.EdgeFace)) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_one : right < 1
  left_on_sphere : dist (K.edgeCurve h i left) (h (K.position (K.edgeFirst i))) = D.radius
  right_on_sphere : dist (K.edgeCurve h i right) (h (K.position (K.edgeSecond i))) = D.radius
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    K.edgeCurve h i t ∉ Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    K.edgeCurve h i t ∉ Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius

/-- The vertex-disk choice in Moise 6.2, Figure 6.1. -/
theorem exists_vertexDiskControl
    (hvertex : ∀ v : K.Vertex, ({v} : Finset K.Vertex) ∈ K.simplexes)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) : Nonempty (K.VertexDiskControl h) := by
  classical
  let I := Option ((K.Vertex × K.Vertex) ⊕ (K.Vertex × K.EdgeFace))
  let P : I → ℝ → Prop
    | none, _ => True
    | some (Sum.inl (v, w)), δ => v = w ∨
        Disjoint (Metric.cthickening δ (h '' K.cellCarrier {v}))
          (Metric.cthickening δ (h '' K.cellCarrier {w}))
    | some (Sum.inr (v, e)), δ => v ∈ e.1 ∨
        Disjoint (Metric.cthickening δ (h '' K.cellCarrier {v}))
          (Metric.cthickening δ (h '' K.cellCarrier e.1))
  have hlocal : ∀ i : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
    intro c
    rcases c with _ | c
    · exact ⟨1, by norm_num, fun _ _ _ => trivial⟩
    · rcases c with ⟨v, w⟩ | ⟨v, e⟩
      · by_cases hvw : v = w
        · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hvw⟩
        · obtain ⟨ε, hε, hdis⟩ := K.exists_disjoint_image_face_thickenings
            hcont hinj (hvertex v) (hvertex w) (by simpa [Finset.disjoint_singleton])
          refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
          exact hdis.mono (Metric.cthickening_subset_thickening' hε hδε _)
            (Metric.cthickening_subset_thickening' hε hδε _)
      · by_cases hve : v ∈ e.1
        · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hve⟩
        · have he : e.1 ∈ K.simplexes := (Finset.mem_filter.mp e.2).1
          have hdisFaces : Disjoint ({v} : Finset K.Vertex) e.1 := by
            exact Finset.disjoint_singleton_left.mpr hve
          obtain ⟨ε, hε, hdis⟩ := K.exists_disjoint_image_face_thickenings
            hcont hinj (hvertex v) he hdisFaces
          refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
          exact hdis.mono (Metric.cthickening_subset_thickening' hε hδε _)
            (Metric.cthickening_subset_thickening' hε hδε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨{
    radius := r
    radius_pos := hr
    vertices_disjoint := ?_
    avoids_nonincident_edge := ?_ }⟩
  · intro v w hvw
    have hP := huniform (some (Sum.inl (v, w))) r hr (half_lt_self hε)
    rcases hP with hEq | hdis
    · exact (hvw hEq).elim
    · have hvCenter : h (K.position v) ∈ h '' K.cellCarrier {v} := by
        refine ⟨K.position v, ?_, rfl⟩
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      have hwCenter : h (K.position w) ∈ h '' K.cellCarrier {w} := by
        refine ⟨K.position w, ?_, rfl⟩
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩
      exact hdis.mono
        (Metric.closedBall_subset_cthickening hvCenter r)
        (Metric.closedBall_subset_cthickening hwCenter r)
  · intro v e hve
    have hP := huniform (some (Sum.inr (v, e))) r hr (half_lt_self hε)
    rcases hP with hv | hdis
    · exact (hve hv).elim
    · have hvCenter : h (K.position v) ∈ h '' K.cellCarrier {v} := by
        refine ⟨K.position v, ?_, rfl⟩
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      exact hdis.mono_left
        (Metric.closedBall_subset_cthickening hvCenter r)

namespace VertexDiskControl

/-- All separation properties survive shrinking the common vertex radius. -/
def shrink {h : Plane → Plane} (D : K.VertexDiskControl h) (r : ℝ)
    (hr : 0 < r) (hrD : r ≤ D.radius) : K.VertexDiskControl h where
  radius := r
  radius_pos := hr
  vertices_disjoint v w hvw :=
    (D.vertices_disjoint v w hvw).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.closedBall_subset_closedBall hrD)
  avoids_nonincident_edge v e hve :=
    (D.avoids_nonincident_edge v e hve).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.cthickening_mono hrD _)

end VertexDiskControl

theorem exists_vertexDiskControl_lt
    (hvertex : ∀ v : K.Vertex, ({v} : Finset K.Vertex) ∈ K.simplexes)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) {η : ℝ} (hη : 0 < η) :
    ∃ D : K.VertexDiskControl h, D.radius < η := by
  obtain ⟨D⟩ := K.exists_vertexDiskControl hvertex hcont hinj
  let r := min (D.radius / 2) (η / 2)
  have hr : 0 < r := lt_min (half_pos D.radius_pos) (half_pos hη)
  have hrD : r ≤ D.radius :=
    (min_le_left _ _).trans (half_le_self D.radius_pos.le)
  refine ⟨VertexDiskControl.shrink K D r hr hrD, ?_⟩
  exact (min_le_right _ _).trans_lt (half_lt_self hη)

theorem exists_edgeTrimData
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (i : Fin (Fintype.card K.EdgeFace)) :
    Nonempty (K.EdgeTrimData h D i) := by
  have hends : K.edgeFirst i ≠ K.edgeSecond i := K.edgeFirst_ne_edgeSecond i
  have hsecondBall : h (K.position (K.edgeSecond i)) ∈
      Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius := by
    rw [Metric.mem_closedBall, dist_self]
    exact D.radius_pos.le
  have hfinishOutside : K.edgeCurve h i 1 ∉
      Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius := by
    rw [K.edgeCurve_one]
    intro hfirstBall
    exact Set.disjoint_left.mp
      (D.vertices_disjoint (K.edgeFirst i) (K.edgeSecond i) hends)
      hfirstBall hsecondBall
  obtain ⟨L⟩ := exists_lastExitData D.radius_pos (K.edgeCurve_continuousOn hcont i)
    (K.edgeCurve_zero h i) hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let ρ : ℝ → Plane := fun s => K.edgeCurve h i (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by
      dsimp [q]
      ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2)
        (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 :=
        mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hqcont : Continuous q := by
    fun_prop
  have hρcont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) := by
    exact (K.edgeCurve_continuousOn hcont i).comp hqcont.continuousOn hqMaps
  have hρzero : ρ 0 = h (K.position (K.edgeSecond i)) := by
    simp [ρ, q]
  have hleftFirstBall : K.edgeCurve h i a ∈
      Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius := by
    rw [Metric.mem_closedBall]
    exact L.on_sphere.le
  have hleftOutsideSecond : ρ 1 ∉
      Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius := by
    have hρone : ρ 1 = K.edgeCurve h i a := by simp [ρ, q, a]
    rw [hρone]
    intro hsecond
    exact Set.disjoint_left.mp
      (D.vertices_disjoint (K.edgeFirst i) (K.edgeSecond i) hends)
      hleftFirstBall hsecond
  obtain ⟨R⟩ := exists_lastExitData D.radius_pos hρcont hρzero hleftOutsideSecond
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    have ha1 : a < 1 := L.parameter_lt_one
    have hR1 : R.parameter < 1 := R.parameter_lt_one
    nlinarith
  have hb1 : b < 1 := by
    dsimp [b, q]
    have ha1 : a < 1 := L.parameter_lt_one
    have hR0 : 0 < R.parameter := R.parameter_pos
    nlinarith
  have hbSphere : dist (K.edgeCurve h i b)
      (h (K.position (K.edgeSecond i))) = D.radius := by
    exact R.on_sphere
  refine ⟨{
    left := a
    right := b
    left_pos := L.parameter_pos
    left_lt_right := hab
    right_lt_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := hbSphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hρs : ρ s = K.edgeCurve h i t := by
    dsimp [ρ, q, s]
    congr 2
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.ne'
    rw [mul_div_cancel₀ (1 - t) hden]
    ring
  rw [← hρs]
  exact R.after_exit s hs hRs

theorem openSegments_disjoint_of_ne
    {i j : Fin (Fintype.card K.EdgeFace)} (hij : i ≠ j) :
    Disjoint
      (openSegment ℝ (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)))
      (openSegment ℝ (K.position (K.edgeFirst j)) (K.position (K.edgeSecond j))) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxiSeg : x ∈ K.cellCarrier (K.edgeAt i).1 := by
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
      ext y
      simp [eq_comm]
    rw [himage, convexHull_pair]
    exact openSegment_subset_segment ℝ _ _ hxi
  have hxjSeg : x ∈ K.cellCarrier (K.edgeAt j).1 := by
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({K.edgeFirst j, K.edgeSecond j} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst j), K.position (K.edgeSecond j)} := by
      ext y
      simp [eq_comm]
    rw [himage, convexHull_pair]
    exact openSegment_subset_segment ℝ _ _ hxj
  have hxInter : x ∈ K.cellCarrier ((K.edgeAt i).1 ∩ (K.edgeAt j).1) := by
    have hface := K.face_inter (K.edgeAt i).1 (K.edgeAt_mem_simplexes i)
      (K.edgeAt j).1 (K.edgeAt_mem_simplexes j)
    have hxPair : x ∈ K.cellCarrier (K.edgeAt i).1 ∩
        K.cellCarrier (K.edgeAt j).1 := ⟨hxiSeg, hxjSeg⟩
    change x ∈ convexHull ℝ (K.position '' ((K.edgeAt i).1 : Set K.Vertex)) ∩
      convexHull ℝ (K.position '' ((K.edgeAt j).1 : Set K.Vertex)) at hxPair
    rw [hface] at hxPair
    exact hxPair
  have hinterCard : ((K.edgeAt i).1 ∩ (K.edgeAt j).1).card ≤ 1 := by
    by_contra hnot
    have hcard : ((K.edgeAt i).1 ∩ (K.edgeAt j).1).card = 2 := by
      have hle := Finset.card_le_card (Finset.inter_subset_left :
        (K.edgeAt i).1 ∩ (K.edgeAt j).1 ⊆ (K.edgeAt i).1)
      rw [K.edgeAt_card i] at hle
      omega
    have hiEq : (K.edgeAt i).1 ∩ (K.edgeAt j).1 = (K.edgeAt i).1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.edgeAt_card i, hcard])
    have hjEq : (K.edgeAt i).1 ∩ (K.edgeAt j).1 = (K.edgeAt j).1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [K.edgeAt_card j, hcard])
    apply hij
    apply K.edgeEquiv.symm.injective
    apply Subtype.ext
    exact hiEq.symm.trans hjEq
  have hinterNonempty : ((K.edgeAt i).1 ∩ (K.edgeAt j).1).Nonempty := by
    by_contra hempty
    have hinterEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hinterEmpty, PlaneComplex.cellCarrier] at hxInter
    simp at hxInter
  have hinterOne : ((K.edgeAt i).1 ∩ (K.edgeAt j).1).card = 1 := by
    exact le_antisymm hinterCard (Finset.one_le_card.mpr hinterNonempty)
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hinterOne
  have hxv : x = K.position v := by
    rw [hv, PlaneComplex.cellCarrier] at hxInter
    simpa using hxInter
  rw [openSegment_eq_image_lineMap] at hxi
  obtain ⟨t, ht, htx⟩ := hxi
  have hvi : v ∈ (K.edgeAt i).1 := by
    have : v ∈ (K.edgeAt i).1 ∩ (K.edgeAt j).1 := by rw [hv]; simp
    exact Finset.mem_of_mem_inter_left this
  rw [K.edgeAt_eq] at hvi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvi
  rcases hvi with hvi | hvi
  · have heq : AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
        (K.position (K.edgeSecond i)) t =
        AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
          (K.position (K.edgeSecond i)) (0 : ℝ) := by
      have htx' : AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
          (K.position (K.edgeSecond i)) t = x := htx
      rw [hxv, hvi] at htx'
      calc
        _ = K.position (K.edgeFirst i) := htx'
        _ = _ := by simp
    have ht0 := AffineMap.lineMap_injective ℝ
      (K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)) heq
    linarith [ht.1]
  · have heq : AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
        (K.position (K.edgeSecond i)) t =
        AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
          (K.position (K.edgeSecond i)) (1 : ℝ) := by
      have htx' : AffineMap.lineMap (k := ℝ) (K.position (K.edgeFirst i))
          (K.position (K.edgeSecond i)) t = x := htx
      rw [hxv, hvi] at htx'
      calc
        _ = K.position (K.edgeSecond i) := htx'
        _ = _ := by simp
    have ht1 := AffineMap.lineMap_injective ℝ
      (K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)) heq
    linarith [ht.2]

namespace EdgeTrimData

variable {K : PlaneComplex} {h : Plane → Plane}
  {D : K.VertexDiskControl h} {i : Fin (Fintype.card K.EdgeFace)}

/-- The `centralCarrier` declaration. -/
def centralCarrier (T : K.EdgeTrimData h D i) : Set Plane :=
  K.edgeCurve h i '' Set.Icc T.left T.right

theorem isCompact_centralCarrier (T : K.EdgeTrimData h D i)
    (hcont : ContinuousOn h K.support) : IsCompact T.centralCarrier := by
  apply (isCompact_Icc.image_of_continuousOn)
  exact (K.edgeCurve_continuousOn hcont i).mono fun t ht =>
    ⟨T.left_pos.le.trans ht.1, ht.2.trans T.right_lt_one.le⟩

theorem centralCarrier_subset_image_openSegment (T : K.EdgeTrimData h D i) :
    T.centralCarrier ⊆ h ''
      openSegment ℝ (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) := by
  rintro y ⟨t, ht, rfl⟩
  refine ⟨AffineMap.lineMap (K.position (K.edgeFirst i))
    (K.position (K.edgeSecond i)) t, ?_, rfl⟩
  exact lineMap_mem_openSegment ℝ _ _ ⟨T.left_pos.trans_le ht.1,
    ht.2.trans_lt T.right_lt_one⟩

theorem disjoint_centralCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {T' : K.EdgeTrimData h D j} (T : K.EdgeTrimData h D i)
    (hinj : Set.InjOn h K.support) (hij : i ≠ j) :
    Disjoint T.centralCarrier T'.centralCarrier := by
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨x, hxOpen, hxy⟩ := T.centralCarrier_subset_image_openSegment hy
  obtain ⟨x', hx'Open, hx'y⟩ := T'.centralCarrier_subset_image_openSegment hy'
  have hxSupport : x ∈ K.support := by
    apply K.cellCarrier_subset_support (K.edgeAt_mem_simplexes i)
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
      ext z
      simp [eq_comm]
    rw [himage, convexHull_pair]
    exact openSegment_subset_segment ℝ _ _ hxOpen
  have hx'Support : x' ∈ K.support := by
    apply K.cellCarrier_subset_support (K.edgeAt_mem_simplexes j)
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({K.edgeFirst j, K.edgeSecond j} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst j), K.position (K.edgeSecond j)} := by
      ext z
      simp [eq_comm]
    rw [himage, convexHull_pair]
    exact openSegment_subset_segment ℝ _ _ hx'Open
  have hxx' : x = x' := hinj hxSupport hx'Support (hxy.trans hx'y.symm)
  exact Set.disjoint_left.mp (K.openSegments_disjoint_of_ne hij) hxOpen (hxx' ▸ hx'Open)

end EdgeTrimData

/-- The `edgeTrim` declaration. -/
noncomputable def edgeTrim {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (i : Fin (Fintype.card K.EdgeFace)) :
    K.EdgeTrimData h D i :=
  Classical.choice (K.exists_edgeTrimData hcont D i)

/-- Pairwise-disjoint closed tubes around all trimmed central arcs. -/
structure CentralTubeControl {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) where
  /-- The `radius` declaration. -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_vertex : radius < D.radius
  pairwise_disjoint : ∀ i j : Fin (Fintype.card K.EdgeFace), i ≠ j →
    Disjoint
      (Metric.cthickening radius (K.edgeTrim hcont D i).centralCarrier)
      (Metric.cthickening radius (K.edgeTrim hcont D j).centralCarrier)

theorem exists_centralTubeControl {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (hinj : Set.InjOn h K.support)
    (D : K.VertexDiskControl h) : Nonempty (K.CentralTubeControl hcont D) := by
  classical
  let I := Option (Fin (Fintype.card K.EdgeFace) × Fin (Fintype.card K.EdgeFace))
  let P : I → ℝ → Prop
    | none, _ => True
    | some (i, j), δ => i = j ∨
        Disjoint (Metric.cthickening δ (K.edgeTrim hcont D i).centralCarrier)
          (Metric.cthickening δ (K.edgeTrim hcont D j).centralCarrier)
  have hlocal : ∀ c : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P c δ := by
    intro c
    rcases c with _ | ⟨i, j⟩
    · exact ⟨1, by norm_num, fun _ _ _ => trivial⟩
    · by_cases hij : i = j
      · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hij⟩
      · have hdis : Disjoint (K.edgeTrim hcont D i).centralCarrier
          (K.edgeTrim hcont D j).centralCarrier :=
          EdgeTrimData.disjoint_centralCarrier (T' := K.edgeTrim hcont D j)
            (K.edgeTrim hcont D i) hinj hij
        have hcompactI := (K.edgeTrim hcont D i).isCompact_centralCarrier hcont
        have hcompactJ := (K.edgeTrim hcont D j).isCompact_centralCarrier hcont
        obtain ⟨ε, hε, hthick⟩ := hdis.exists_thickenings hcompactI hcompactJ.isClosed
        refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
        exact hthick.mono (Metric.cthickening_subset_thickening' hε hδε _)
          (Metric.cthickening_subset_thickening' hε hδε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := min (ε / 2) (D.radius / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos D.radius_pos)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrD : r < D.radius := (min_le_right _ _).trans_lt (half_lt_self D.radius_pos)
  refine ⟨{
    radius := r
    radius_pos := hr
    radius_lt_vertex := hrD
    pairwise_disjoint := ?_ }⟩
  intro i j hij
  have hP := huniform (some (i, j)) r hr hrε
  rcases hP with heq | hdis
  · exact (hij heq).elim
  · exact hdis

namespace EdgeTrimData

theorem isPreconnected_centralCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (i : Fin (Fintype.card K.EdgeFace)) :
    IsPreconnected (K.edgeTrim hcont D i).centralCarrier := by
  apply IsPreconnected.image (convex_Icc _ _).isPreconnected
  exact (K.edgeCurve_continuousOn hcont i).mono fun t ht =>
    ⟨(K.edgeTrim hcont D i).left_pos.le.trans ht.1,
      ht.2.trans (K.edgeTrim hcont D i).right_lt_one.le⟩

theorem left_mem_centralCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeCurve h i (K.edgeTrim hcont D i).left ∈
      (K.edgeTrim hcont D i).centralCarrier :=
  ⟨_, ⟨le_rfl, (K.edgeTrim hcont D i).left_lt_right.le⟩, rfl⟩

theorem right_mem_centralCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeCurve h i (K.edgeTrim hcont D i).right ∈
      (K.edgeTrim hcont D i).centralCarrier :=
  ⟨_, ⟨(K.edgeTrim hcont D i).left_lt_right.le, le_rfl⟩, rfl⟩

end EdgeTrimData

/-- A polygonal replacement for one trimmed central arc, kept inside its assigned tube. -/
structure CentralPolygonalArc {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace)) where
  /-- The `data` declaration. -/
  data : BrokenLineData
    (Metric.thickening C.radius (K.edgeTrim hcont D i).centralCarrier ∩
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1))
  start_eq : data.start = K.edgeCurve h i (K.edgeTrim hcont D i).left
  finish_eq : data.finish = K.edgeCurve h i (K.edgeTrim hcont D i).right

theorem exists_centralPolygonalArc {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    Nonempty (K.CentralPolygonalArc hcont D C i) := by
  let A := (K.edgeTrim hcont D i).centralCarrier
  have hjoined : JoinedByBrokenLine
      (Metric.thickening C.radius A ∩ convexHull ℝ A)
      (K.edgeCurve h i (K.edgeTrim hcont D i).left)
      (K.edgeCurve h i (K.edgeTrim hcont D i).right) := by
    exact brokenLine_in_thickening_inter_convexHull_of_preconnected
      (EdgeTrimData.isPreconnected_centralCarrier K hcont D i)
      (EdgeTrimData.left_mem_centralCarrier K hcont D i)
      (EdgeTrimData.right_mem_centralCarrier K hcont D i) C.radius_pos
  obtain ⟨B, hstart, hfinish⟩ := BrokenLineData.exists_data_of_joined hjoined
  have hcentral : A ⊆ h '' K.cellCarrier (K.edgeAt i).1 := by
    rintro y ⟨t, ht, rfl⟩
    refine ⟨AffineMap.lineMap (K.position (K.edgeFirst i))
        (K.position (K.edgeSecond i)) t, ?_, rfl⟩
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
      ext z
      simp [eq_comm]
    rw [himage, convexHull_pair]
    exact lineMap_mem_segment ℝ _ _
      ⟨(K.edgeTrim hcont D i).left_pos.le.trans ht.1,
        ht.2.trans (K.edgeTrim hcont D i).right_lt_one.le⟩
  refine ⟨{
    data := {
      n := B.n
      vertex := B.vertex
      segment_subset := fun j ↦ (B.segment_subset j).trans fun x hx ↦
        ⟨hx.1, convexHull_mono hcentral hx.2⟩ }
    start_eq := hstart
    finish_eq := hfinish }⟩

/-- The `centralPolygonalArc` declaration. -/
noncomputable def centralPolygonalArc {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    K.CentralPolygonalArc hcont D C i :=
  Classical.choice (K.exists_centralPolygonalArc hcont D C i)

namespace CentralPolygonalArc

variable {K : PlaneComplex} {h : Plane → Plane} {hcont : ContinuousOn h K.support}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
  {i : Fin (Fintype.card K.EdgeFace)}

theorem resolvedCarrier_subset_tube (A : K.CentralPolygonalArc hcont D C i) :
    A.data.resolvedCarrier ⊆
      Metric.thickening C.radius (K.edgeTrim hcont D i).centralCarrier := by
  apply (A.data.resolvedCarrier_subset ?_).trans Set.inter_subset_left
  rw [A.start_eq]
  refine ⟨Metric.self_subset_thickening C.radius_pos _
      (EdgeTrimData.left_mem_centralCarrier K hcont D i), ?_⟩
  apply subset_convexHull ℝ _
  let t := (K.edgeTrim hcont D i).left
  refine ⟨AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) t, ?_, rfl⟩
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext z
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact lineMap_mem_segment ℝ _ _
    ⟨(K.edgeTrim hcont D i).left_pos.le,
      (K.edgeTrim hcont D i).left_lt_right.le.trans
        (K.edgeTrim hcont D i).right_lt_one.le⟩

/-- The loop-resolved middle remains in the convex hull of the original target edge. -/
theorem resolvedCarrier_subset_edgeConvexHull
    (A : K.CentralPolygonalArc hcont D C i) :
    A.data.resolvedCarrier ⊆
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) := by
  apply (A.data.resolvedCarrier_subset ?_).trans Set.inter_subset_right
  rw [A.start_eq]
  refine ⟨Metric.self_subset_thickening C.radius_pos _
      (EdgeTrimData.left_mem_centralCarrier K hcont D i), ?_⟩
  apply subset_convexHull ℝ _
  let t := (K.edgeTrim hcont D i).left
  refine ⟨AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) t, ?_, rfl⟩
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext z
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact lineMap_mem_segment ℝ _ _
    ⟨(K.edgeTrim hcont D i).left_pos.le,
      (K.edgeTrim hcont D i).left_lt_right.le.trans
        (K.edgeTrim hcont D i).right_lt_one.le⟩

theorem disjoint_resolvedCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.data.resolvedCarrier A'.data.resolvedCarrier :=
  (C.pairwise_disjoint i j hij).mono
    (A.resolvedCarrier_subset_tube.trans (Metric.thickening_subset_cthickening _ _))
    (A'.resolvedCarrier_subset_tube.trans (Metric.thickening_subset_cthickening _ _))

/-- A simple parameterization of the polygonal replacement, normalized to the unit interval. -/
structure Parameterization (A : K.CentralPolygonalArc hcont D C i) where
  /-- The `source` declaration. -/
  source : PlaneComplex
  /-- The `map` declaration. -/
  map : Plane → Plane
  /-- The `curve` declaration. -/
  curve : ℝ → Plane
  source_support : source.support =
    segment ℝ (planePoint 0 0) (planePoint A.data.resolvedWalk.length 0)
  map_isPL : IsPLOn source map
  map_affineOn : ∀ s ∈ source.simplexes, IsAffineOn map (source.cellCarrier s)
  source_card_le_two : ∀ s ∈ source.simplexes, s.card ≤ 2
  source_vertex_mem : ∀ v, source.position v ∈ source.support
  curve_eq : ∀ t, curve t = map (planePoint (A.data.resolvedWalk.length * t) 0)
  continuousOn : ContinuousOn curve (Set.Icc (0 : ℝ) 1)
  injectiveOn : Set.InjOn curve (Set.Icc (0 : ℝ) 1)
  image_eq : curve '' Set.Icc (0 : ℝ) 1 = A.data.resolvedCarrier
  start_eq : curve 0 = A.data.start
  finish_eq : curve 1 = A.data.finish

theorem start_ne_finish (A : K.CentralPolygonalArc hcont D C i) :
    A.data.start ≠ A.data.finish := by
  have hleft : K.edgeCurve h i (K.edgeTrim hcont D i).left ∈
      Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius := by
    rw [Metric.mem_closedBall]
    exact (K.edgeTrim hcont D i).left_on_sphere.le
  have hright : K.edgeCurve h i (K.edgeTrim hcont D i).right ∈
      Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius := by
    rw [Metric.mem_closedBall]
    exact (K.edgeTrim hcont D i).right_on_sphere.le
  rw [A.start_eq, A.finish_eq]
  intro heq
  exact Set.disjoint_left.mp
    (D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i)) hleft (heq ▸ hright)

theorem resolvedWalk_length_pos (A : K.CentralPolygonalArc hcont D C i) :
    0 < A.data.resolvedWalk.length := by
  by_contra hnot
  have hzero : A.data.resolvedWalk.length = 0 := Nat.eq_zero_of_not_pos hnot
  apply A.start_ne_finish
  rw [← A.data.resolvedVertex_start, ← A.data.resolvedVertex_finish]
  congr 2
  exact Fin.ext (by simp [hzero])

/-- The polygonal arc model from Chapter 6.1 gives a continuous injective unit-interval
parameterization. -/
theorem exists_parameterization (A : K.CentralPolygonalArc hcont D C i) :
    Nonempty A.Parameterization := by
  obtain ⟨S, F, hSsupport, hpl, hSgraph, hinj, himage, hstart, hfinish⟩ :=
    A.data.exists_PL_segment_model
  have hplS := hpl
  obtain ⟨L, hLsub, hLaffine⟩ := hpl
  let n : ℝ := A.data.resolvedWalk.length
  let axis : ℝ → Plane := fun t => planePoint (n * t) 0
  let curve : ℝ → Plane := fun t => F (axis t)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have haxisLine : axis = AffineMap.lineMap (planePoint 0 0) (planePoint n 0) := by
    funext t
    ext k
    fin_cases k <;> simp [axis, planePoint, AffineMap.lineMap_apply_module, mul_comm]
  have haxisImage : axis '' Set.Icc (0 : ℝ) 1 =
      segment ℝ (planePoint 0 0) (planePoint n 0) := by
    rw [haxisLine, segment_eq_image_lineMap]
  have haxisMaps : Set.MapsTo axis (Set.Icc (0 : ℝ) 1) S.support := by
    rw [hSsupport]
    simpa [n] using Set.mapsTo_iff_image_subset.mpr haxisImage.le
  have haxisCont : Continuous axis := by
    rw [haxisLine]
    exact AffineMap.lineMap_continuous
  have hcurveCont : ContinuousOn curve (Set.Icc (0 : ℝ) 1) := by
    exact hplS.continuousOn.comp haxisCont.continuousOn haxisMaps
  have haxisInj : Set.InjOn axis (Set.Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    have hcoord := congrArg (fun p : Plane => p 0) hxy
    change n * x = n * y at hcoord
    exact (mul_left_cancel₀ hn.ne' hcoord)
  have hcurveInj : Set.InjOn curve (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply haxisInj hx hy
    exact hinj (haxisMaps hx) (haxisMaps hy) hxy
  have hcurveImage : curve '' Set.Icc (0 : ℝ) 1 = A.data.resolvedCarrier := by
    rw [show curve '' Set.Icc (0 : ℝ) 1 = F '' (axis '' Set.Icc (0 : ℝ) 1) by
      exact (Set.image_image F axis (Set.Icc (0 : ℝ) 1)).symm]
    rw [haxisImage, ← hSsupport, himage]
  refine ⟨{
    source := PlaneComplex.active L
    map := F
    curve := curve
    source_support := by rw [L.active_support, hLsub.1, hSsupport]
    map_isPL := by
      refine ⟨PlaneComplex.active L, PlaneComplex.Subdivides.refl _, ?_⟩
      intro s hs
      exact Eq.mpr (congrArg (IsAffineOn F) (L.active_cellCarrier s))
        (hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs))
    map_affineOn := by
      intro s hs
      exact Eq.mpr (congrArg (IsAffineOn F) (L.active_cellCarrier s))
        (hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs))
    source_card_le_two := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := (PlaneComplex.active_subdivides_left hLsub).2 s hs
      exact card_le_two_of_cellCarrier_subset_face hs ht (hSgraph t ht) hst
    source_vertex_mem := by
      intro v
      change L.position v.1 ∈ (PlaneComplex.active L).support
      rw [L.active_support]
      exact v.2
    curve_eq := by intro t; rfl
    continuousOn := hcurveCont
    injectiveOn := hcurveInj
    image_eq := hcurveImage
    start_eq := ?_
    finish_eq := ?_ }⟩
  · simpa [curve, axis, n] using hstart
  · simpa [curve, axis, n] using hfinish

/-- The `parameterization` declaration. -/
noncomputable def parameterization (A : K.CentralPolygonalArc hcont D C i) :
    A.Parameterization :=
  Classical.choice A.exists_parameterization

/-- The portion of the polygonal replacement between its ordered exits from the endpoint disks. -/
noncomputable def exitData (A : K.CentralPolygonalArc hcont D C i) :
    BoundaryExitData A.parameterization.curve
      (h (K.position (K.edgeFirst i))) (h (K.position (K.edgeSecond i))) D.radius := by
  apply Classical.choice
  apply exists_boundaryExitData D.radius_pos A.parameterization.continuousOn
  · rw [A.parameterization.start_eq, A.start_eq]
    exact (K.edgeTrim hcont D i).left_on_sphere
  · rw [A.parameterization.finish_eq, A.finish_eq]
    exact (K.edgeTrim hcont D i).right_on_sphere
  · exact D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i)

/-- The `trimmedCarrier` declaration. -/
def trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  A.parameterization.curve '' Set.Icc A.exitData.left A.exitData.right

theorem trimmedCarrier_subset_resolvedCarrier
    (A : K.CentralPolygonalArc hcont D C i) :
    A.trimmedCarrier ⊆ A.data.resolvedCarrier := by
  rw [← A.parameterization.image_eq]
  exact Set.image_mono fun t ht =>
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩

theorem trimmedCarrier_avoids_first
    (A : K.CentralPolygonalArc hcont D C i) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxleft : x ≠ A.parameterization.curve A.exitData.left) :
    x ∉ Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius := by
  obtain ⟨t, ht, rfl⟩ := hx
  apply A.exitData.after_left t
  · exact ⟨A.exitData.left_nonneg.trans ht.1,
      ht.2.trans A.exitData.right_le_one⟩
  · apply lt_of_le_of_ne ht.1
    intro heq
    apply hxleft
    rw [heq]

theorem trimmedCarrier_avoids_second
    (A : K.CentralPolygonalArc hcont D C i) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxright : x ≠ A.parameterization.curve A.exitData.right) :
    x ∉ Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius := by
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hleft : t = A.exitData.left
  · subst t
    apply Set.disjoint_left.mp
      (D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i))
    · rw [Metric.mem_closedBall]
      exact A.exitData.left_on_sphere.le
  · apply A.exitData.before_right t
    · exact ⟨A.exitData.left_nonneg.trans ht.1,
        ht.2.trans A.exitData.right_le_one⟩
    · exact lt_of_le_of_ne ht.1 (Ne.symm hleft)
    · apply lt_of_le_of_ne ht.2
      intro heq
      apply hxright
      rw [heq]

theorem trimmedCarrier_avoids_nonincident
    (A : K.CentralPolygonalArc hcont D C i) (v : K.Vertex)
    (hv : v ∉ (K.edgeAt i).1) :
    Disjoint (Metric.closedBall (h (K.position v)) D.radius) A.trimmedCarrier := by
  apply (D.avoids_nonincident_edge v (K.edgeAt i) hv).mono_right
  apply A.trimmedCarrier_subset_resolvedCarrier.trans
  apply A.resolvedCarrier_subset_tube.trans
  apply (Metric.thickening_subset_cthickening_of_le C.radius_lt_vertex.le
    (K.edgeTrim hcont D i).centralCarrier).trans
  apply Metric.cthickening_subset_of_subset
  apply (K.edgeTrim hcont D i).centralCarrier_subset_image_openSegment.trans
  apply Set.image_mono
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact openSegment_subset_segment ℝ _ _

/-- The `leftEndpoint` declaration. -/
noncomputable def leftEndpoint (A : K.CentralPolygonalArc hcont D C i) : Plane :=
  A.parameterization.curve A.exitData.left

/-- The `rightEndpoint` declaration. -/
noncomputable def rightEndpoint (A : K.CentralPolygonalArc hcont D C i) : Plane :=
  A.parameterization.curve A.exitData.right

/-- The `leftSpoke` declaration. -/
noncomputable def leftSpoke (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  segment ℝ (h (K.position (K.edgeFirst i))) A.leftEndpoint

/-- The `rightSpoke` declaration. -/
noncomputable def rightSpoke (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  segment ℝ A.rightEndpoint (h (K.position (K.edgeSecond i)))

/-- The complete polygonal replacement of an edge: a radial spoke, the trimmed middle arc, and
a second radial spoke. -/
noncomputable def completeCarrier (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  A.leftSpoke ∪ A.trimmedCarrier ∪ A.rightSpoke

/-- Every complete finite replacement edge stays in the convex hull of its original target
edge.  In particular, simultaneous finite graph approximation preserves any convex target such
as the model half-plane. -/
theorem completeCarrier_subset_edgeConvexHull
    (A : K.CentralPolygonalArc hcont D C i) :
    A.completeCarrier ⊆ convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) := by
  have hconvex : Convex ℝ (convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1)) :=
    convex_convexHull ℝ _
  have hfirstSource : K.position (K.edgeFirst i) ∈
      K.cellCarrier (K.edgeAt i).1 := by
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    exact subset_convexHull ℝ _ ⟨K.edgeFirst i, by simp, rfl⟩
  have hsecondSource : K.position (K.edgeSecond i) ∈
      K.cellCarrier (K.edgeAt i).1 := by
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
    exact subset_convexHull ℝ _ ⟨K.edgeSecond i, by simp, rfl⟩
  have hfirst : h (K.position (K.edgeFirst i)) ∈
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) :=
    subset_convexHull ℝ _ ⟨_, hfirstSource, rfl⟩
  have hsecond : h (K.position (K.edgeSecond i)) ∈
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) :=
    subset_convexHull ℝ _ ⟨_, hsecondSource, rfl⟩
  have hleft : A.leftEndpoint ∈
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) :=
    A.resolvedCarrier_subset_edgeConvexHull
      (A.trimmedCarrier_subset_resolvedCarrier
        ⟨A.exitData.left, ⟨le_rfl, A.exitData.left_lt_right.le⟩, rfl⟩)
  have hright : A.rightEndpoint ∈
      convexHull ℝ (h '' K.cellCarrier (K.edgeAt i).1) :=
    A.resolvedCarrier_subset_edgeConvexHull
      (A.trimmedCarrier_subset_resolvedCarrier
        ⟨A.exitData.right, ⟨A.exitData.left_lt_right.le, le_rfl⟩, rfl⟩)
  rintro x ((hx | hx) | hx)
  · exact hconvex.segment_subset hfirst hleft hx
  · exact A.resolvedCarrier_subset_edgeConvexHull
      (A.trimmedCarrier_subset_resolvedCarrier hx)
  · exact hconvex.segment_subset hright hsecond hx

/-- The `leftOpenSpoke` declaration. -/
noncomputable def leftOpenSpoke (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  A.leftSpoke \ {h (K.position (K.edgeFirst i))}

/-- The `rightOpenSpoke` declaration. -/
noncomputable def rightOpenSpoke (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  A.rightSpoke \ {h (K.position (K.edgeSecond i))}

/-- The relative interior of a replacement edge. -/
noncomputable def interiorCarrier (A : K.CentralPolygonalArc hcont D C i) : Set Plane :=
  A.leftOpenSpoke ∪ A.trimmedCarrier ∪ A.rightOpenSpoke

theorem leftEndpoint_mem_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    A.leftEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.left, ⟨le_rfl, A.exitData.left_lt_right.le⟩, rfl⟩

theorem rightEndpoint_mem_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    A.rightEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.right, ⟨A.exitData.left_lt_right.le, le_rfl⟩, rfl⟩

theorem leftEndpoint_on_sphere (A : K.CentralPolygonalArc hcont D C i) :
    dist A.leftEndpoint (h (K.position (K.edgeFirst i))) = D.radius :=
  A.exitData.left_on_sphere

theorem rightEndpoint_on_sphere (A : K.CentralPolygonalArc hcont D C i) :
    dist A.rightEndpoint (h (K.position (K.edgeSecond i))) = D.radius :=
  A.exitData.right_on_sphere

/-- The trimmed middle arc as a path. -/
noncomputable def middlePath (A : K.CentralPolygonalArc hcont D C i) :
    Path A.leftEndpoint A.rightEndpoint where
  toFun t := A.parameterization.curve
    (Path.segment A.exitData.left A.exitData.right t)
  continuous_toFun := by
    apply A.parameterization.continuousOn.comp_continuous
    · exact (Path.segment A.exitData.left A.exitData.right).continuous
    · intro t
      have ht : Path.segment A.exitData.left A.exitData.right t ∈
          segment ℝ A.exitData.left A.exitData.right := by
        rw [← Path.range_segment]
        exact ⟨t, rfl⟩
      rw [segment_eq_Icc A.exitData.left_lt_right.le] at ht
      exact ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩
  source' := by simp [leftEndpoint]
  target' := by simp [rightEndpoint]

theorem range_middlePath (A : K.CentralPolygonalArc hcont D C i) :
    Set.range A.middlePath = A.trimmedCarrier := by
  rw [trimmedCarrier]
  have hsegment : segment ℝ A.exitData.left A.exitData.right =
      Set.Icc A.exitData.left A.exitData.right :=
    segment_eq_Icc A.exitData.left_lt_right.le
  rw [← hsegment, ← Path.range_segment]
  ext x
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Path.segment A.exitData.left A.exitData.right t,
      ⟨t, rfl⟩, by rfl⟩
  · rintro ⟨r, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, by rfl⟩

/-- The full replacement path for an edge. -/
noncomputable def completePath (A : K.CentralPolygonalArc hcont D C i) :
    Path (h (K.position (K.edgeFirst i))) (h (K.position (K.edgeSecond i))) :=
  (Path.segment (h (K.position (K.edgeFirst i))) A.leftEndpoint).trans
    (A.middlePath.trans
      (Path.segment A.rightEndpoint (h (K.position (K.edgeSecond i)))))

theorem range_completePath (A : K.CentralPolygonalArc hcont D C i) :
    Set.range A.completePath = A.completeCarrier := by
  rw [completePath, Path.trans_range, Path.trans_range, Path.range_segment,
    Path.range_segment, A.range_middlePath]
  simp [completeCarrier, leftSpoke, rightSpoke, Set.union_assoc]

theorem middlePath_injective (A : K.CentralPolygonalArc hcont D C i) :
    Function.Injective A.middlePath := by
  intro s t hst
  have hs : Path.segment A.exitData.left A.exitData.right s ∈
        Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨s, rfl⟩
  have ht : Path.segment A.exitData.left A.exitData.right t ∈
        Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨t, rfl⟩
  have hparam := A.parameterization.injectiveOn
    ⟨A.exitData.left_nonneg.trans hs.1, hs.2.trans A.exitData.right_le_one⟩
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩ hst
  exact Path.segment_injective_of_ne A.exitData.left_lt_right.ne hparam

theorem disjoint_trimmedCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.trimmedCarrier A'.trimmedCarrier :=
  (CentralPolygonalArc.disjoint_resolvedCarrier (A' := A') A hij).mono
    A.trimmedCarrier_subset_resolvedCarrier
    A'.trimmedCarrier_subset_resolvedCarrier

theorem leftEndpoint_ne_leftEndpoint {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    A.leftEndpoint ≠ A'.leftEndpoint := by
  intro heq
  have hmem : A.leftEndpoint ∈ A'.trimmedCarrier := by
    rw [heq]
    exact A'.leftEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp
    (CentralPolygonalArc.disjoint_trimmedCarrier (A' := A') A hij)
    A.leftEndpoint_mem_trimmedCarrier hmem

theorem leftEndpoint_ne_rightEndpoint {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    A.leftEndpoint ≠ A'.rightEndpoint := by
  intro heq
  have hmem : A.leftEndpoint ∈ A'.trimmedCarrier := by
    rw [heq]
    exact A'.rightEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp
    (CentralPolygonalArc.disjoint_trimmedCarrier (A' := A') A hij)
    A.leftEndpoint_mem_trimmedCarrier hmem

theorem rightEndpoint_ne_leftEndpoint {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    A.rightEndpoint ≠ A'.leftEndpoint := by
  intro heq
  have hmem : A.rightEndpoint ∈ A'.trimmedCarrier := by
    rw [heq]
    exact A'.leftEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp
    (CentralPolygonalArc.disjoint_trimmedCarrier (A' := A') A hij)
    A.rightEndpoint_mem_trimmedCarrier hmem

theorem rightEndpoint_ne_rightEndpoint {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    A.rightEndpoint ≠ A'.rightEndpoint := by
  intro heq
  have hmem : A.rightEndpoint ∈ A'.trimmedCarrier := by
    rw [heq]
    exact A'.rightEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp
    (CentralPolygonalArc.disjoint_trimmedCarrier (A' := A') A hij)
    A.rightEndpoint_mem_trimmedCarrier hmem

theorem leftSpoke_subset_disk (A : K.CentralPolygonalArc hcont D C i) :
    A.leftSpoke ⊆ Metric.closedBall (h (K.position (K.edgeFirst i))) D.radius := by
  apply (convex_closedBall _ _).segment_subset
  · exact Metric.mem_closedBall_self D.radius_pos.le
  · rw [Metric.mem_closedBall]
    simpa [dist_comm] using A.leftEndpoint_on_sphere.le

theorem rightSpoke_subset_disk (A : K.CentralPolygonalArc hcont D C i) :
    A.rightSpoke ⊆ Metric.closedBall (h (K.position (K.edgeSecond i))) D.radius := by
  apply (convex_closedBall _ _).segment_subset
  · rw [Metric.mem_closedBall]
    exact A.rightEndpoint_on_sphere.le
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem leftSpoke_inter_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    A.leftSpoke ∩ A.trimmedCarrier = {A.leftEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_first hxTrim hx (A.leftSpoke_subset_disk hxSpoke)
  · rintro x rfl
    exact ⟨right_mem_segment ℝ _ _, A.leftEndpoint_mem_trimmedCarrier⟩

theorem rightSpoke_inter_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    A.rightSpoke ∩ A.trimmedCarrier = {A.rightEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_second hxTrim hx (A.rightSpoke_subset_disk hxSpoke)
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, A.rightEndpoint_mem_trimmedCarrier⟩

theorem leftSpoke_disjoint_rightSpoke (A : K.CentralPolygonalArc hcont D C i) :
    Disjoint A.leftSpoke A.rightSpoke :=
  (D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i)).mono
    A.leftSpoke_subset_disk A.rightSpoke_subset_disk

/-- Every complete replacement edge is a simple path. -/
theorem completePath_injective (A : K.CentralPolygonalArc hcont D C i) :
    Function.Injective A.completePath := by
  let first := Path.segment (h (K.position (K.edgeFirst i))) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.position (K.edgeSecond i)))
  have hfirstNe : h (K.position (K.edgeFirst i)) ≠ A.leftEndpoint := by
    intro heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq, dist_self] at hs
    linarith [D.radius_pos]
  have hlastNe : A.rightEndpoint ≠ h (K.position (K.edgeSecond i)) := by
    intro heq
    have hs := A.rightEndpoint_on_sphere
    rw [heq, dist_self] at hs
    linarith [D.radius_pos]
  have hfirstInj : Function.Injective first := Path.segment_injective_of_ne hfirstNe
  have hlastInj : Function.Injective last := Path.segment_injective_of_ne hlastNe
  have hmiddleLastInter : Set.range A.middlePath ∩ Set.range last = {A.rightEndpoint} := by
    rw [A.range_middlePath, Path.range_segment]
    rw [Set.inter_comm]
    exact A.rightSpoke_inter_trimmedCarrier
  have htailInj : Function.Injective (A.middlePath.trans last) :=
    Path.trans_injective_of_range_inter A.middlePath last A.middlePath_injective
      hlastInj hmiddleLastInter
  have hfirstMiddleInter : Set.range first ∩ Set.range A.middlePath = {A.leftEndpoint} := by
    rw [Path.range_segment, A.range_middlePath]
    exact A.leftSpoke_inter_trimmedCarrier
  have hfirstLast : Disjoint (Set.range first) (Set.range last) := by
    rw [Path.range_segment, Path.range_segment]
    exact A.leftSpoke_disjoint_rightSpoke
  have hfirstTailInter : Set.range first ∩ Set.range (A.middlePath.trans last) =
      {A.leftEndpoint} := by
    rw [Path.trans_range, Set.inter_union_distrib_left, hfirstMiddleInter,
      Set.disjoint_iff_inter_eq_empty.mp hfirstLast, Set.union_empty]
  exact Path.trans_injective_of_range_inter first (A.middlePath.trans last)
    hfirstInj htailInj hfirstTailInter

theorem firstCenter_not_mem_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    h (K.position (K.edgeFirst i)) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_first hx
  · intro heq
    have heq' : h (K.position (K.edgeFirst i)) = A.leftEndpoint := by
      simpa [leftEndpoint] using heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq', dist_self] at hs
    linarith [D.radius_pos]
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem secondCenter_not_mem_trimmedCarrier (A : K.CentralPolygonalArc hcont D C i) :
    h (K.position (K.edgeSecond i)) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_second hx
  · intro heq
    have heq' : h (K.position (K.edgeSecond i)) = A.rightEndpoint := by
      simpa [rightEndpoint] using heq
    have hs := A.rightEndpoint_on_sphere
    rw [← heq', dist_self] at hs
    linarith [D.radius_pos]
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem firstCenter_not_mem_rightSpoke (A : K.CentralPolygonalArc hcont D C i) :
    h (K.position (K.edgeFirst i)) ∉ A.rightSpoke := by
  intro hx
  exact Set.disjoint_left.mp (D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i))
    (Metric.mem_closedBall_self D.radius_pos.le) (A.rightSpoke_subset_disk hx)

theorem secondCenter_not_mem_leftSpoke (A : K.CentralPolygonalArc hcont D C i) :
    h (K.position (K.edgeSecond i)) ∉ A.leftSpoke := by
  intro hx
  exact Set.disjoint_left.mp (D.vertices_disjoint _ _ (K.edgeFirst_ne_edgeSecond i))
    (A.leftSpoke_subset_disk hx) (Metric.mem_closedBall_self D.radius_pos.le)

theorem completeCarrier_sdiff_endpoints (A : K.CentralPolygonalArc hcont D C i) :
    A.completeCarrier \
        {h (K.position (K.edgeFirst i)), h (K.position (K.edgeSecond i))} =
      A.interiorCarrier := by
  ext x
  simp only [completeCarrier, interiorCarrier, leftOpenSpoke, rightOpenSpoke,
    Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  constructor
  · rintro ⟨(hL | hT) | hR, hne⟩
    · exact Or.inl (Or.inl ⟨hL, fun hx => hne (Or.inl hx)⟩)
    · exact Or.inl (Or.inr hT)
    · exact Or.inr ⟨hR, fun hx => hne (Or.inr hx)⟩
  · rintro ((⟨hL, hx0⟩ | hT) | ⟨hR, hx1⟩)
    · refine ⟨Or.inl (Or.inl hL), ?_⟩
      rintro (hx | hx)
      · exact hx0 hx
      · exact A.secondCenter_not_mem_leftSpoke (hx ▸ hL)
    · refine ⟨Or.inl (Or.inr hT), ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_trimmedCarrier (hx ▸ hT)
      · exact A.secondCenter_not_mem_trimmedCarrier (hx ▸ hT)
    · refine ⟨Or.inr hR, ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_rightSpoke (hx ▸ hR)
      · exact hx1 hx

theorem disjoint_leftSpoke_trimmedCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.leftSpoke A'.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxBall := A.leftSpoke_subset_disk hxSpoke
  by_cases hv : K.edgeFirst i ∈ (K.edgeAt j).1
  · rw [K.edgeAt_eq] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hxEq : x = A'.leftEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_first hxTrim hne
        simpa [hv] using hxBall
      have hxSphere : dist x (h (K.position (K.edgeFirst i))) = D.radius := by
        rw [hxEq, hv]
        exact A'.leftEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.leftEndpoint_on_sphere
          hxSpoke hxSphere
      exact CentralPolygonalArc.leftEndpoint_ne_leftEndpoint (A' := A') A hij
        (hxOwn.symm.trans hxEq)
    · have hxEq : x = A'.rightEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_second hxTrim hne
        simpa [hv] using hxBall
      have hxSphere : dist x (h (K.position (K.edgeFirst i))) = D.radius := by
        rw [hxEq, hv]
        exact A'.rightEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.leftEndpoint_on_sphere
          hxSpoke hxSphere
      exact CentralPolygonalArc.leftEndpoint_ne_rightEndpoint (A' := A') A hij
        (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp (A'.trimmedCarrier_avoids_nonincident (K.edgeFirst i) hv)
      hxBall hxTrim

theorem disjoint_rightSpoke_trimmedCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.rightSpoke A'.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxBall := A.rightSpoke_subset_disk hxSpoke
  have hxSpoke' : x ∈ segment ℝ (h (K.position (K.edgeSecond i))) A.rightEndpoint := by
    rwa [segment_symm]
  by_cases hv : K.edgeSecond i ∈ (K.edgeAt j).1
  · rw [K.edgeAt_eq] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hxEq : x = A'.leftEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_first hxTrim hne
        simpa [hv] using hxBall
      have hxSphere : dist x (h (K.position (K.edgeSecond i))) = D.radius := by
        rw [hxEq, hv]
        exact A'.leftEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.rightEndpoint_on_sphere
          hxSpoke' hxSphere
      exact CentralPolygonalArc.rightEndpoint_ne_leftEndpoint (A' := A') A hij
        (hxOwn.symm.trans hxEq)
    · have hxEq : x = A'.rightEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_second hxTrim hne
        simpa [hv] using hxBall
      have hxSphere : dist x (h (K.position (K.edgeSecond i))) = D.radius := by
        rw [hxEq, hv]
        exact A'.rightEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.rightEndpoint_on_sphere
          hxSpoke' hxSphere
      exact CentralPolygonalArc.rightEndpoint_ne_rightEndpoint (A' := A') A hij
        (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp (A'.trimmedCarrier_avoids_nonincident (K.edgeSecond i) hv)
      hxBall hxTrim

theorem disjoint_leftOpenSpoke_leftOpenSpoke {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.leftOpenSpoke A'.leftOpenSpoke := by
  by_cases hv : K.edgeFirst i = K.edgeFirst j
  · simpa [leftOpenSpoke, leftSpoke, hv] using
      disjoint_radial_segments_away_center D.radius_pos A.leftEndpoint_on_sphere
        (by simpa [hv] using A'.leftEndpoint_on_sphere)
        (CentralPolygonalArc.leftEndpoint_ne_leftEndpoint (A' := A') A hij)
  · exact (D.vertices_disjoint _ _ hv).mono
      (Set.sdiff_subset.trans A.leftSpoke_subset_disk)
      (Set.sdiff_subset.trans A'.leftSpoke_subset_disk)

theorem disjoint_leftOpenSpoke_rightOpenSpoke {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.leftOpenSpoke A'.rightOpenSpoke := by
  by_cases hv : K.edgeFirst i = K.edgeSecond j
  · simpa [leftOpenSpoke, leftSpoke, rightOpenSpoke, rightSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.leftEndpoint_on_sphere
        (by simpa [hv] using A'.rightEndpoint_on_sphere)
        (CentralPolygonalArc.leftEndpoint_ne_rightEndpoint (A' := A') A hij)
  · exact (D.vertices_disjoint _ _ hv).mono
      (Set.sdiff_subset.trans A.leftSpoke_subset_disk)
      (Set.sdiff_subset.trans A'.rightSpoke_subset_disk)

theorem disjoint_rightOpenSpoke_leftOpenSpoke {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.rightOpenSpoke A'.leftOpenSpoke := by
  by_cases hv : K.edgeSecond i = K.edgeFirst j
  · simpa [rightOpenSpoke, rightSpoke, leftOpenSpoke, leftSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.rightEndpoint_on_sphere
        (by simpa [hv] using A'.leftEndpoint_on_sphere)
        (CentralPolygonalArc.rightEndpoint_ne_leftEndpoint (A' := A') A hij)
  · exact (D.vertices_disjoint _ _ hv).mono
      (Set.sdiff_subset.trans A.rightSpoke_subset_disk)
      (Set.sdiff_subset.trans A'.leftSpoke_subset_disk)

theorem disjoint_rightOpenSpoke_rightOpenSpoke {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.rightOpenSpoke A'.rightOpenSpoke := by
  by_cases hv : K.edgeSecond i = K.edgeSecond j
  · simpa [rightOpenSpoke, rightSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.rightEndpoint_on_sphere
        (by simpa [hv] using A'.rightEndpoint_on_sphere)
        (CentralPolygonalArc.rightEndpoint_ne_rightEndpoint (A' := A') A hij)
  · exact (D.vertices_disjoint _ _ hv).mono
      (Set.sdiff_subset.trans A.rightSpoke_subset_disk)
      (Set.sdiff_subset.trans A'.rightSpoke_subset_disk)

/-- Distinct replacement edges have disjoint relative interiors. -/
theorem disjoint_interiorCarrier {j : Fin (Fintype.card K.EdgeFace)}
    {A' : K.CentralPolygonalArc hcont D C j}
    (A : K.CentralPolygonalArc hcont D C i) (hij : i ≠ j) :
    Disjoint A.interiorCarrier A'.interiorCarrier := by
  have hLT' : Disjoint A.leftOpenSpoke A'.trimmedCarrier :=
    (CentralPolygonalArc.disjoint_leftSpoke_trimmedCarrier (A' := A') A hij).mono_left
      Set.sdiff_subset
  have hRT' : Disjoint A.rightOpenSpoke A'.trimmedCarrier :=
    (CentralPolygonalArc.disjoint_rightSpoke_trimmedCarrier (A' := A') A hij).mono_left
      Set.sdiff_subset
  have hTL' : Disjoint A.trimmedCarrier A'.leftOpenSpoke :=
    ((CentralPolygonalArc.disjoint_leftSpoke_trimmedCarrier (A' := A) A' hij.symm).mono_left
      Set.sdiff_subset).symm
  have hTR' : Disjoint A.trimmedCarrier A'.rightOpenSpoke :=
    ((CentralPolygonalArc.disjoint_rightSpoke_trimmedCarrier (A' := A) A' hij.symm).mono_left
      Set.sdiff_subset).symm
  rw [Set.disjoint_left]
  intro x hx hx'
  change x ∈ (A.leftOpenSpoke ∪ A.trimmedCarrier) ∪ A.rightOpenSpoke at hx
  change x ∈ (A'.leftOpenSpoke ∪ A'.trimmedCarrier) ∪ A'.rightOpenSpoke at hx'
  rcases hx with (hL | hT) | hR <;> rcases hx' with (hL' | hT') | hR'
  · exact Set.disjoint_left.mp
      (CentralPolygonalArc.disjoint_leftOpenSpoke_leftOpenSpoke (A' := A') A hij) hL hL'
  · exact Set.disjoint_left.mp hLT' hL hT'
  · exact Set.disjoint_left.mp
      (CentralPolygonalArc.disjoint_leftOpenSpoke_rightOpenSpoke (A' := A') A hij) hL hR'
  · exact Set.disjoint_left.mp hTL' hT hL'
  · exact Set.disjoint_left.mp
      (CentralPolygonalArc.disjoint_trimmedCarrier (A' := A') A hij) hT hT'
  · exact Set.disjoint_left.mp hTR' hT hR'
  · exact Set.disjoint_left.mp
      (CentralPolygonalArc.disjoint_rightOpenSpoke_leftOpenSpoke (A' := A') A hij) hR hL'
  · exact Set.disjoint_left.mp hRT' hR hT'
  · exact Set.disjoint_left.mp
      (CentralPolygonalArc.disjoint_rightOpenSpoke_rightOpenSpoke (A' := A') A hij) hR hR'

theorem completeCarrier_avoids_nonincident
    (A : K.CentralPolygonalArc hcont D C i) (v : K.Vertex)
    (hv : v ∉ (K.edgeAt i).1) :
    Disjoint (Metric.closedBall (h (K.position v)) D.radius) A.completeCarrier := by
  have hvFirst : v ≠ K.edgeFirst i := by
    intro heq
    apply hv
    simp [K.edgeAt_eq, heq]
  have hvSecond : v ≠ K.edgeSecond i := by
    intro heq
    apply hv
    simp [K.edgeAt_eq, heq]
  rw [Set.disjoint_left]
  intro x hxBall hxCarrier
  rcases hxCarrier with (hxLeft | hxTrim) | hxRight
  · exact Set.disjoint_left.mp (D.vertices_disjoint v (K.edgeFirst i) hvFirst)
      hxBall (A.leftSpoke_subset_disk hxLeft)
  · exact Set.disjoint_left.mp (A.trimmedCarrier_avoids_nonincident v hv) hxBall hxTrim
  · exact Set.disjoint_left.mp (D.vertices_disjoint v (K.edgeSecond i) hvSecond)
      hxBall (A.rightSpoke_subset_disk hxRight)

end CentralPolygonalArc

/-- The selected replacement arc for an enumerated edge. -/
noncomputable def replacementArc {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace)) : K.CentralPolygonalArc hcont D C i :=
  K.centralPolygonalArc hcont D C i

/-- The `rawMiddleBreakpoint` declaration. -/
noncomputable def rawMiddleBreakpoint
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (v : A.parameterization.source.Vertex) : ℝ :=
  (((A.parameterization.source.position v) 0 /
      A.data.resolvedWalk.length - A.exitData.left) /
      (A.exitData.right - A.exitData.left) + 2) / 4

/-- The `middleSourceScalarMap` declaration. -/
noncomputable def middleSourceScalarMap
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) : Plane →ᵃ[ℝ] ℝ :=
  (A.data.resolvedWalk.length : ℝ) •
    (AffineMap.const ℝ Plane A.exitData.left +
      (A.exitData.right - A.exitData.left) •
        ((4 : ℝ) • K.edgeParameter i - AffineMap.const ℝ Plane 2))

/-- The `middleSourceMap` declaration. -/
noncomputable def middleSourceMap
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) : Plane →ᵃ[ℝ] Plane :=
  BrokenLineData.realAxisAffine.comp (middleSourceScalarMap K A)

@[simp] theorem middleSourceMap_apply
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (x : Plane) :
    middleSourceMap K A x = planePoint
      (A.data.resolvedWalk.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * K.edgeParameter i x - 2))) 0 := by
  rfl

/-- The `middleBreakpoint` declaration. -/
noncomputable def middleBreakpoint
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (v : A.parameterization.source.Vertex) : ℝ :=
  max (1 / 2 : ℝ) (min (3 / 4 : ℝ) (rawMiddleBreakpoint K A v))

theorem middleBreakpoint_mem
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (v : A.parameterization.source.Vertex) :
    middleBreakpoint K A v ∈ Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem middleBreakpoint_eq_raw_of_mem
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.data.resolvedWalk.length)
    (hv1 : A.parameterization.source.position v 0 / A.data.resolvedWalk.length ≤
      A.exitData.right) :
    middleBreakpoint K A v = rawMiddleBreakpoint K A v := by
  have hden : 0 < A.exitData.right - A.exitData.left :=
    sub_pos.mpr A.exitData.left_lt_right
  have hfrac0 : 0 ≤
      (A.parameterization.source.position v 0 / A.data.resolvedWalk.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) :=
    div_nonneg (sub_nonneg.mpr hv0) hden.le
  have hfrac1 :
      (A.parameterization.source.position v 0 / A.data.resolvedWalk.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith
  have hraw0 : (1 / 2 : ℝ) ≤ rawMiddleBreakpoint K A v := by
    dsimp [rawMiddleBreakpoint]
    linarith
  have hraw1 : rawMiddleBreakpoint K A v ≤ (3 / 4 : ℝ) := by
    dsimp [rawMiddleBreakpoint]
    linarith
  rw [middleBreakpoint, min_eq_right hraw1, max_eq_right hraw0]

theorem middleSourceScalar_breakpoint
    {h : Plane → Plane} {hcont : ContinuousOn h K.support}
    {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont D}
    {i : Fin (Fintype.card K.EdgeFace)}
    (A : K.CentralPolygonalArc hcont D C i) (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.data.resolvedWalk.length)
    (hv1 : A.parameterization.source.position v 0 / A.data.resolvedWalk.length ≤
      A.exitData.right) :
    A.data.resolvedWalk.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * middleBreakpoint K A v - 2)) =
      A.parameterization.source.position v 0 := by
  rw [middleBreakpoint_eq_raw_of_mem K A v hv0 hv1]
  have hn : (A.data.resolvedWalk.length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.resolvedWalk_length_pos)
  have hden : A.exitData.right - A.exitData.left ≠ 0 :=
    sub_ne_zero.mpr A.exitData.left_lt_right.ne'
  dsimp [rawMiddleBreakpoint]
  field_simp [hn, hden]
  ring

/-- The finite set of all source breakpoints: the two spoke joins and every vertex of every
middle PL model. -/
abbrev GraphBreakpoint {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D) :=
  Σ i : Fin (Fintype.card K.EdgeFace),
    Option (Option (K.replacementArc hcont D C i).parameterization.source.Vertex)

/-- The `graphBreakpointParameter` declaration. -/
noncomputable def graphBreakpointParameter {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (b : K.GraphBreakpoint hcont D C) : ℝ :=
  match b.2 with
  | none => 1 / 2
  | some none => 3 / 4
  | some (some v) => middleBreakpoint K (K.replacementArc hcont D C b.1) v

theorem graphBreakpointParameter_mem {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (b : K.GraphBreakpoint hcont D C) :
    K.graphBreakpointParameter hcont D C b ∈ Set.Icc (0 : ℝ) 1 := by
  rcases b with ⟨i, _ | _ | v⟩
  · norm_num [graphBreakpointParameter]
  · norm_num [graphBreakpointParameter]
  · have hb := middleBreakpoint_mem K (K.replacementArc hcont D C i) v
    change middleBreakpoint K (K.replacementArc hcont D C i) v ∈ Set.Icc (0 : ℝ) 1
    constructor <;> linarith [hb.1, hb.2]

/-- The `graphBreakpointPoint` declaration. -/
noncomputable def graphBreakpointPoint {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (b : K.GraphBreakpoint hcont D C) : Plane :=
  AffineMap.lineMap (K.position (K.edgeFirst b.1)) (K.position (K.edgeSecond b.1))
    (K.graphBreakpointParameter hcont D C b)

theorem graphBreakpointPoint_mem_support {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (b : K.GraphBreakpoint hcont D C) :
    K.graphBreakpointPoint hcont D C b ∈ K.support :=
  K.edge_lineMap_mem_support b.1 (K.graphBreakpointParameter_mem hcont D C b)

/-- The common source subdivision carrying all edgewise PL breakpoints. -/
noncomputable def graphReplacementSubdivision {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) : PlaneComplex :=
  K.markedEdgeSubdivision (K.graphBreakpointPoint hcont D C)

theorem graphReplacementSubdivision_subdivides {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) :
    (K.graphReplacementSubdivision hcont D C).Subdivides K :=
  K.markedEdgeSubdivision_subdivides (K.graphBreakpointPoint hcont D C) hgraph

theorem exists_graphReplacementSubdivision_vertex {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (b : K.GraphBreakpoint hcont D C) :
    ∃ w : (K.graphReplacementSubdivision hcont D C).Vertex,
      ({w} : Finset (K.graphReplacementSubdivision hcont D C).Vertex) ∈
        (K.graphReplacementSubdivision hcont D C).simplexes ∧
      (K.graphReplacementSubdivision hcont D C).position w =
        K.graphBreakpointPoint hcont D C b :=
  K.exists_markedEdgeSubdivision_vertex (K.graphBreakpointPoint hcont D C) b
    (K.graphBreakpointPoint_mem_support hcont D C b)

theorem graphReplacementFace_parameter_side {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace))
    (b : Option (Option (K.replacementArc hcont D C i).parameterization.source.Vertex))
    {u : Finset (K.graphReplacementSubdivision hcont D C).Vertex}
    (hu : u ∈ (K.graphReplacementSubdivision hcont D C).simplexes) :
    (∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
        K.edgeParameter i x ≤ K.graphBreakpointParameter hcont D C ⟨i, b⟩) ∨
      (∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
        K.graphBreakpointParameter hcont D C ⟨i, b⟩ ≤ K.edgeParameter i x) := by
  have huArrangement := ((K.markedEdgeArrangement (K.graphBreakpointPoint hcont D C))
    |>.mem_subordinateTo_simplexes_iff K).mp hu |>.1
  have hside := K.markedFaceCarrier_parameter_side
    (K.graphBreakpointPoint hcont D C) (⟨i, b⟩ : K.GraphBreakpoint hcont D C)
    i (K.graphBreakpointParameter hcont D C ⟨i, b⟩) rfl huArrangement
  exact hside

theorem graphReplacementFace_piece {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace))
    {u : Finset (K.graphReplacementSubdivision hcont D C).Vertex}
    (hu : u ∈ (K.graphReplacementSubdivision hcont D C).simplexes) :
    (∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
        K.edgeParameter i x ≤ (1 / 2 : ℝ)) ∨
      ((∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
          (1 / 2 : ℝ) ≤ K.edgeParameter i x) ∧
        (∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
          K.edgeParameter i x ≤ (3 / 4 : ℝ))) ∨
      (∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
        (3 / 4 : ℝ) ≤ K.edgeParameter i x) := by
  have hhalf := K.graphReplacementFace_parameter_side hcont D C i none hu
  have hthree := K.graphReplacementFace_parameter_side hcont D C i (some none) hu
  change (∀ x ∈ _, K.edgeParameter i x ≤ (1 / 2 : ℝ)) ∨
      (∀ x ∈ _, (1 / 2 : ℝ) ≤ K.edgeParameter i x) at hhalf
  change (∀ x ∈ _, K.edgeParameter i x ≤ (3 / 4 : ℝ)) ∨
      (∀ x ∈ _, (3 / 4 : ℝ) ≤ K.edgeParameter i x) at hthree
  rcases hhalf with hleHalf | hgeHalf
  · exact Or.inl hleHalf
  · rcases hthree with hleThree | hgeThree
    · exact Or.inr (Or.inl ⟨hgeHalf, hleThree⟩)
    · exact Or.inr (Or.inr hgeThree)

/-- The replacement map on the affine line carrying one source edge. -/
noncomputable def edgeReplacementMap {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D)
    (i : Fin (Fintype.card K.EdgeFace)) (x : Plane) : Plane :=
  (K.replacementArc hcont D C i).completePath.extend (K.edgeParameter i x)

theorem edgeReplacementMap_continuous {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    Continuous (K.edgeReplacementMap hcont D C i) := by
  exact (K.replacementArc hcont D C i).completePath.continuous_extend.comp
    (K.edgeParameter i).continuous_of_finiteDimensional

@[simp] theorem edgeReplacementMap_first {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeReplacementMap hcont D C i (K.position (K.edgeFirst i)) =
      h (K.position (K.edgeFirst i)) := by
  simp [edgeReplacementMap, K.edgeParameter_apply_first]

@[simp] theorem edgeReplacementMap_second {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeReplacementMap hcont D C i (K.position (K.edgeSecond i)) =
      h (K.position (K.edgeSecond i)) := by
  simp [edgeReplacementMap, K.edgeParameter_apply_second]

theorem edgeReplacementMap_image_cellCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeReplacementMap hcont D C i '' K.cellCarrier (K.edgeAt i).1 =
      (K.replacementArc hcont D C i).completeCarrier := by
  rw [← (K.replacementArc hcont D C i).range_completePath]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    let t : unitInterval := ⟨K.edgeParameter i x, K.edgeParameter_mem_Icc i hx⟩
    refine ⟨t, ?_⟩
    change (K.replacementArc hcont D C i).completePath t =
      (K.replacementArc hcont D C i).completePath.extend (K.edgeParameter i x)
    exact (Path.extend_apply _ (K.edgeParameter_mem_Icc i hx)).symm
  · rintro y ⟨t, rfl⟩
    let x := AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) (t : ℝ)
    have hx : x ∈ K.cellCarrier (K.edgeAt i).1 := by
      rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
      have himage : K.position ''
          (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
          {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
        ext z
        simp [eq_comm]
      rw [himage, convexHull_pair]
      exact lineMap_mem_segment ℝ _ _ t.2
    refine ⟨x, hx, ?_⟩
    change (K.replacementArc hcont D C i).completePath.extend (K.edgeParameter i x) =
      (K.replacementArc hcont D C i).completePath t
    have hparam : K.edgeParameter i x = (t : ℝ) := by
      exact K.edgeParameter_lineMap i t
    rw [hparam]
    exact Path.extend_apply _ t.2

/-- The `IsGraphVertexPoint` declaration. -/
def IsGraphVertexPoint (x : Plane) : Prop :=
  ∃ v : K.Vertex, ({v} : Finset K.Vertex) ∈ K.simplexes ∧ x = K.position v

/-- The `edgeIndexAt` declaration. -/
noncomputable def edgeIndexAt (x : Plane)
    (hx : ∃ i : Fin (Fintype.card K.EdgeFace), x ∈ K.cellCarrier (K.edgeAt i).1) :
    Fin (Fintype.card K.EdgeFace) :=
  Classical.choose hx

theorem edgeIndexAt_spec (x : Plane)
    (hx : ∃ i : Fin (Fintype.card K.EdgeFace), x ∈ K.cellCarrier (K.edgeAt i).1) :
    x ∈ K.cellCarrier (K.edgeAt (K.edgeIndexAt x hx)).1 :=
  Classical.choose_spec hx

/-- The simultaneous replacement map.  Active graph vertices are handled first; every other
point of the graph lies in the open part of a unique edge. -/
noncomputable def graphReplacementMap {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (x : Plane) : Plane :=
  by
    classical
    exact if K.IsGraphVertexPoint x then h x
      else if hx : ∃ i : Fin (Fintype.card K.EdgeFace),
          x ∈ K.cellCarrier (K.edgeAt i).1 then
        K.edgeReplacementMap hcont D C (K.edgeIndexAt x hx) x
      else h x

theorem graphReplacementMap_vertex {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) {v : K.Vertex}
    (hv : ({v} : Finset K.Vertex) ∈ K.simplexes) :
    K.graphReplacementMap hcont D C (K.position v) = h (K.position v) := by
  classical
  rw [graphReplacementMap, if_pos ⟨v, hv, rfl⟩]

private theorem mem_openSegment_of_mem_edge_not_vertex
    {x : Plane} (i : Fin (Fintype.card K.EdgeFace))
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) (hnv : ¬K.IsGraphVertexPoint x) :
    x ∈ openSegment ℝ (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) := by
  apply mem_openSegment_of_ne_left_right
  · intro hxFirst
    apply hnv
    refine ⟨K.edgeFirst i, ?_, hxFirst.symm⟩
    exact K.down_closed (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) {K.edgeFirst i}
      (by simp [K.edgeAt_eq]) (Finset.singleton_nonempty _)
  · intro hxSecond
    apply hnv
    refine ⟨K.edgeSecond i, ?_, hxSecond.symm⟩
    exact K.down_closed (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) {K.edgeSecond i}
      (by simp [K.edgeAt_eq]) (Finset.singleton_nonempty _)
  · rw [← convexHull_pair]
    rw [K.edgeAt_eq, PlaneComplex.cellCarrier] at hx
    have himage : K.position ''
        (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
        {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
      ext z
      simp [eq_comm]
    rwa [himage] at hx

theorem edgeIndexAt_eq_of_not_vertex {x : Plane}
    (hnv : ¬K.IsGraphVertexPoint x)
    (hx : ∃ i : Fin (Fintype.card K.EdgeFace), x ∈ K.cellCarrier (K.edgeAt i).1)
    (i : Fin (Fintype.card K.EdgeFace)) (hxi : x ∈ K.cellCarrier (K.edgeAt i).1) :
    K.edgeIndexAt x hx = i := by
  by_contra hne
  exact Set.disjoint_left.mp (K.openSegments_disjoint_of_ne hne)
    (K.mem_openSegment_of_mem_edge_not_vertex _ (K.edgeIndexAt_spec x hx) hnv)
    (K.mem_openSegment_of_mem_edge_not_vertex i hxi hnv)

theorem graphReplacementMap_eq_edge {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) {x : Plane}
    (hnv : ¬K.IsGraphVertexPoint x) (i : Fin (Fintype.card K.EdgeFace))
    (hxi : x ∈ K.cellCarrier (K.edgeAt i).1) :
    K.graphReplacementMap hcont D C x = K.edgeReplacementMap hcont D C i x := by
  classical
  let hx : ∃ j : Fin (Fintype.card K.EdgeFace), x ∈ K.cellCarrier (K.edgeAt j).1 := ⟨i, hxi⟩
  rw [graphReplacementMap, if_neg hnv, dif_pos hx,
    K.edgeIndexAt_eq_of_not_vertex hnv hx i hxi]

theorem graphReplacementMap_eq_edge_on_cellCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace)) :
    Set.EqOn (K.graphReplacementMap hcont D C)
      (K.edgeReplacementMap hcont D C i) (K.cellCarrier (K.edgeAt i).1) := by
  intro x hx
  by_cases hnv : ¬K.IsGraphVertexPoint x
  · exact K.graphReplacementMap_eq_edge hcont D C hnv i hx
  · push Not at hnv
    obtain ⟨v, hvface, rfl⟩ := hnv
    have hvCarrier : K.position v ∈ K.cellCarrier ({v} : Finset K.Vertex) := by
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
    have hvEdge : v ∈ (K.edgeAt i).1 := by
      by_contra hvnot
      have hinter : ({v} : Finset K.Vertex) ∩ (K.edgeAt i).1 = ∅ := by
        ext w
        simp [hvnot]
      have hp : K.position v ∈ K.cellCarrier
          (({v} : Finset K.Vertex) ∩ (K.edgeAt i).1) := by
        have hface := K.face_inter ({v} : Finset K.Vertex) hvface
          (K.edgeAt i).1 (K.edgeAt_mem_simplexes i)
        have : K.position v ∈ K.cellCarrier ({v} : Finset K.Vertex) ∩
            K.cellCarrier (K.edgeAt i).1 := ⟨hvCarrier, hx⟩
        change K.position v ∈ convexHull ℝ (K.position '' ({v} : Finset K.Vertex)) ∩
          convexHull ℝ (K.position '' ((K.edgeAt i).1 : Set K.Vertex)) at this
        rw [hface] at this
        exact this
      rw [hinter, PlaneComplex.cellCarrier] at hp
      simp at hp
    rw [K.edgeAt_eq] at hvEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvEdge
    rcases hvEdge with rfl | rfl
    · rw [K.graphReplacementMap_vertex hcont D C hvface,
        K.edgeReplacementMap_first]
    · rw [K.graphReplacementMap_vertex hcont D C hvface,
        K.edgeReplacementMap_second]

theorem vertexPoint_or_exists_edge_of_mem_support
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) {x : Plane} (hx : x ∈ K.support) :
    K.IsGraphVertexPoint x ∨
      ∃ i : Fin (Fintype.card K.EdgeFace), x ∈ K.cellCarrier (K.edgeAt i).1 := by
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hscard := hgraph s hs
  have hscases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hscases with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    left
    refine ⟨v, hs, ?_⟩
    simpa [PlaneComplex.cellCarrier] using hxs
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    right
    refine ⟨i, ?_⟩
    rw [hi]
    exact hxs

/-- The finite simultaneous graph replacement remains in the convex hull of the original
target graph. -/
theorem graphReplacementMap_mem_targetConvexHull
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D)
    {x : Plane} (hx : x ∈ K.support) :
    K.graphReplacementMap hcont D C x ∈ convexHull ℝ (h '' K.support) := by
  rcases K.vertexPoint_or_exists_edge_of_mem_support hgraph hx with hxv | ⟨i, hxi⟩
  · obtain ⟨v, hv, rfl⟩ := hxv
    rw [K.graphReplacementMap_vertex hcont D C hv]
    exact subset_convexHull ℝ _ ⟨K.position v,
      K.cellCarrier_subset_support hv
        (subset_convexHull ℝ _ ⟨v, by simp, rfl⟩), rfl⟩
  · have himage : K.edgeReplacementMap hcont D C i x ∈
        (K.replacementArc hcont D C i).completeCarrier := by
      rw [← K.edgeReplacementMap_image_cellCarrier hcont D C i]
      exact ⟨x, hxi, rfl⟩
    rw [K.graphReplacementMap_eq_edge_on_cellCarrier hcont D C i hxi]
    apply convexHull_mono
      (Set.image_mono (K.cellCarrier_subset_support (K.edgeAt_mem_simplexes i)))
    exact (K.replacementArc hcont D C i).completeCarrier_subset_edgeConvexHull himage

theorem edgeReplacementMap_eq_path {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {x : Plane} (hx : x ∈ K.cellCarrier (K.edgeAt i).1) :
    K.edgeReplacementMap hcont D C i x =
      (K.replacementArc hcont D C i).completePath
        ⟨K.edgeParameter i x, K.edgeParameter_mem_Icc i hx⟩ := by
  exact Path.extend_apply _ (K.edgeParameter_mem_Icc i hx)

theorem edgeReplacementMap_eq_left {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {x : Plane} (hx : x ∈ K.cellCarrier (K.edgeAt i).1)
    (ht : K.edgeParameter i x ≤ (1 / 2 : ℝ)) :
    K.edgeReplacementMap hcont D C i x =
      AffineMap.lineMap (h (K.position (K.edgeFirst i)))
        (K.replacementArc hcont D C i).leftEndpoint (2 * K.edgeParameter i x) := by
  let A := K.replacementArc hcont D C i
  let first := Path.segment (h (K.position (K.edgeFirst i))) A.leftEndpoint
  let tail := A.middlePath.trans
    (Path.segment A.rightEndpoint (h (K.position (K.edgeSecond i))))
  rw [edgeReplacementMap, show A.completePath = first.trans tail by rfl,
    Path.extend_trans_of_le_half first tail ht]
  have hp := K.edgeParameter_mem_Icc i hx
  have h2t : 2 * K.edgeParameter i x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hp.1, hp.2]
  rw [Path.extend_apply first h2t]
  rfl

theorem edgeReplacementMap_eq_middle {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {x : Plane} (hx : x ∈ K.cellCarrier (K.edgeAt i).1)
    (ht0 : (1 / 2 : ℝ) ≤ K.edgeParameter i x)
    (ht1 : K.edgeParameter i x ≤ (3 / 4 : ℝ)) :
    K.edgeReplacementMap hcont D C i x =
      (K.replacementArc hcont D C i).parameterization.map
        (planePoint
          ((K.replacementArc hcont D C i).data.resolvedWalk.length *
            ((K.replacementArc hcont D C i).exitData.left +
              ((K.replacementArc hcont D C i).exitData.right -
                (K.replacementArc hcont D C i).exitData.left) *
                (4 * K.edgeParameter i x - 2))) 0) := by
  let A := K.replacementArc hcont D C i
  let first := Path.segment (h (K.position (K.edgeFirst i))) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.position (K.edgeSecond i)))
  have hp := K.edgeParameter_mem_Icc i hx
  have htail : (1 / 2 : ℝ) ≤ K.edgeParameter i x := ht0
  rw [edgeReplacementMap, show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) htail]
  have hinner : 2 * K.edgeParameter i x - 1 ≤ (1 / 2 : ℝ) := by linarith
  rw [Path.extend_trans_of_le_half A.middlePath last hinner]
  have hu : 2 * (2 * K.edgeParameter i x - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  rw [Path.extend_apply A.middlePath hu]
  change A.parameterization.curve
      (Path.segment A.exitData.left A.exitData.right
        ⟨2 * (2 * K.edgeParameter i x - 1), hu⟩) = _
  rw [A.parameterization.curve_eq]
  congr 2
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  ring

theorem edgeReplacementMap_eq_right {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {x : Plane} (hx : x ∈ K.cellCarrier (K.edgeAt i).1)
    (ht : (3 / 4 : ℝ) ≤ K.edgeParameter i x) :
    K.edgeReplacementMap hcont D C i x =
      AffineMap.lineMap (K.replacementArc hcont D C i).rightEndpoint
        (h (K.position (K.edgeSecond i))) (4 * K.edgeParameter i x - 3) := by
  let A := K.replacementArc hcont D C i
  let first := Path.segment (h (K.position (K.edgeFirst i))) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.position (K.edgeSecond i)))
  have hp := K.edgeParameter_mem_Icc i hx
  have houter : (1 / 2 : ℝ) ≤ K.edgeParameter i x := by linarith
  rw [edgeReplacementMap, show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) houter]
  have hinner : (1 / 2 : ℝ) ≤ 2 * K.edgeParameter i x - 1 := by linarith
  rw [Path.extend_trans_of_half_le A.middlePath last hinner]
  have hu : 2 * (2 * K.edgeParameter i x - 1) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2]
  rw [Path.extend_apply last hu]
  change AffineMap.lineMap A.rightEndpoint (h (K.position (K.edgeSecond i)))
      (2 * (2 * K.edgeParameter i x - 1) - 1) = _
  congr 1
  ring

theorem graphReplacementMap_affineOn_left {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {E : Set Plane} (hE : E ⊆ K.cellCarrier (K.edgeAt i).1)
    (hle : ∀ x ∈ E, K.edgeParameter i x ≤ (1 / 2 : ℝ)) :
    IsAffineOn (K.graphReplacementMap hcont D C) E := by
  let scalar : Plane →ᵃ[ℝ] ℝ := (2 : ℝ) • K.edgeParameter i
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap (h (K.position (K.edgeFirst i)))
      (K.replacementArc hcont D C i).leftEndpoint).comp scalar
  refine ⟨g, ?_⟩
  intro x hx
  rw [K.graphReplacementMap_eq_edge_on_cellCarrier hcont D C i (hE hx),
    K.edgeReplacementMap_eq_left hcont D C i (hE hx) (hle x hx)]
  rfl

theorem graphReplacementMap_affineOn_right {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {E : Set Plane} (hE : E ⊆ K.cellCarrier (K.edgeAt i).1)
    (hge : ∀ x ∈ E, (3 / 4 : ℝ) ≤ K.edgeParameter i x) :
    IsAffineOn (K.graphReplacementMap hcont D C) E := by
  let scalar : Plane →ᵃ[ℝ] ℝ :=
    (4 : ℝ) • K.edgeParameter i - AffineMap.const ℝ Plane 3
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap (K.replacementArc hcont D C i).rightEndpoint
      (h (K.position (K.edgeSecond i)))).comp scalar
  refine ⟨g, ?_⟩
  intro x hx
  rw [K.graphReplacementMap_eq_edge_on_cellCarrier hcont D C i (hE hx),
    K.edgeReplacementMap_eq_right hcont D C i (hE hx) (hge x hx)]
  rfl

theorem graphReplacementMap_affineOn_middle {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {u : Finset (K.graphReplacementSubdivision hcont D C).Vertex}
    (hu : u ∈ (K.graphReplacementSubdivision hcont D C).simplexes)
    (hui : (K.graphReplacementSubdivision hcont D C).cellCarrier u ⊆
      K.cellCarrier (K.edgeAt i).1)
    (hmid0 : ∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
      (1 / 2 : ℝ) ≤ K.edgeParameter i x)
    (hmid1 : ∀ x ∈ (K.graphReplacementSubdivision hcont D C).cellCarrier u,
      K.edgeParameter i x ≤ (3 / 4 : ℝ)) :
    IsAffineOn (K.graphReplacementMap hcont D C)
      ((K.graphReplacementSubdivision hcont D C).cellCarrier u) := by
  let R := K.graphReplacementSubdivision hcont D C
  let A := K.replacementArc hcont D C i
  let n : ℝ := A.data.resolvedWalk.length
  let z : Plane → ℝ := fun x => n *
    (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.edgeParameter i x - 2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have hdelta : 0 ≤ A.exitData.right - A.exitData.left :=
    sub_nonneg.mpr A.exitData.left_lt_right.le
  have hmono {x y : Plane} (hxy : K.edgeParameter i x ≤ K.edgeParameter i y) :
      z x ≤ z y := by
    dsimp [z]
    apply mul_le_mul_of_nonneg_left _ hn.le
    have hr : 4 * K.edgeParameter i x - 2 ≤ 4 * K.edgeParameter i y - 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hr hdelta
    linarith
  have hzBounds {x : Plane} (hx : x ∈ R.cellCarrier u) : z x ∈ Set.Icc 0 n := by
    have ht0 := hmid0 x hx
    have ht1 := hmid1 x hx
    have hr0 : 0 ≤ 4 * K.edgeParameter i x - 2 := by linarith
    have hr1 : 4 * K.edgeParameter i x - 2 ≤ 1 := by linarith
    constructor
    · apply mul_nonneg hn.le
      exact add_nonneg A.exitData.left_nonneg (mul_nonneg hdelta hr0)
    · calc
        n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.edgeParameter i x - 2)) ≤ n * 1 := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          calc
            A.exitData.left + (A.exitData.right - A.exitData.left) *
                (4 * K.edgeParameter i x - 2) ≤ A.exitData.right := by
              have := mul_le_mul_of_nonneg_left hr1 hdelta
              linarith
            _ ≤ 1 := A.exitData.right_le_one
        _ = n := mul_one n
  have hucard : u.card ≤ 2 :=
    card_le_two_of_cellCarrier_subset_face hu (K.edgeAt_mem_simplexes i)
      (by rw [K.edgeAt_card]) hui
  have hupos : 0 < u.card := Finset.card_pos.mpr
    ((K.graphReplacementSubdivision hcont D C).nonempty_of_mem u hu)
  have hcard : u.card = 1 ∨ u.card = 2 := by omega
  rcases hcard with hcard | hcard
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.graphReplacementMap hcont D C (R.position p))
    refine ⟨g, ?_⟩
    intro x hx
    have hx' : x = R.position p := by
      simpa [R, PlaneComplex.cellCarrier] using hx
    subst x
    rfl
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
    have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
      subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
    have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
      subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
    let a := min (z (R.position p)) (z (R.position q))
    let b := max (z (R.position p)) (z (R.position q))
    have hab : a ≤ b := min_le_max
    have ha : 0 ≤ a := by
      exact le_min (hzBounds hp).1 (hzBounds hq).1
    have hb : b ≤ n := by
      exact max_le (hzBounds hp).2 (hzBounds hq).2
    have havoid : ∀ v : A.parameterization.source.Vertex,
        A.parameterization.source.position v 0 ≤ a ∨
          b ≤ A.parameterization.source.position v 0 := by
      intro v
      let c := A.parameterization.source.position v 0
      by_cases hv0 : c / n < A.exitData.left
      · left
        have hcn : c < n * A.exitData.left := by
          rw [div_lt_iff₀ hn] at hv0
          simpa [mul_comm] using hv0
        have hpLower : n * A.exitData.left ≤ z (R.position p) := by
          dsimp [z]
          have hr := hmid0 (R.position p) hp
          have : 0 ≤ (A.exitData.right - A.exitData.left) *
              (4 * K.edgeParameter i (R.position p) - 2) :=
            mul_nonneg hdelta (by linarith)
          nlinarith
        have hqLower : n * A.exitData.left ≤ z (R.position q) := by
          dsimp [z]
          have hr := hmid0 (R.position q) hq
          have : 0 ≤ (A.exitData.right - A.exitData.left) *
              (4 * K.edgeParameter i (R.position q) - 2) :=
            mul_nonneg hdelta (by linarith)
          nlinarith
        exact hcn.le.trans (le_min hpLower hqLower)
      · have hv0' : A.exitData.left ≤ c / n := le_of_not_gt hv0
        by_cases hv1 : c / n ≤ A.exitData.right
        · have hbreak := K.graphReplacementFace_parameter_side hcont D C i
              (some (some v)) hu
          have hvalue := middleSourceScalar_breakpoint K A v hv0' hv1
          rcases hbreak with hle | hge
          · right
            have hpUpper : z (R.position p) ≤ c := by
              calc
                z (R.position p) ≤ z (K.graphBreakpointPoint hcont D C
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [graphBreakpointPoint, K.edgeParameter_lineMap]
                      exact hle _ hp)
                _ = c := by
                  dsimp [z, graphBreakpointPoint, graphBreakpointParameter, c]
                  rw [K.edgeParameter_lineMap]
                  exact hvalue
            have hqUpper : z (R.position q) ≤ c := by
              calc
                z (R.position q) ≤ z (K.graphBreakpointPoint hcont D C
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [graphBreakpointPoint, K.edgeParameter_lineMap]
                      exact hle _ hq)
                _ = c := by
                  dsimp [z, graphBreakpointPoint, graphBreakpointParameter, c]
                  rw [K.edgeParameter_lineMap]
                  exact hvalue
            exact max_le hpUpper hqUpper
          · left
            have hpLower : c ≤ z (R.position p) := by
              calc
                c = z (K.graphBreakpointPoint hcont D C
                    ⟨i, some (some v)⟩) := by
                  dsimp [z, graphBreakpointPoint, graphBreakpointParameter, c]
                  rw [K.edgeParameter_lineMap]
                  exact hvalue.symm
                _ ≤ z (R.position p) := hmono (by
                  rw [graphBreakpointPoint, K.edgeParameter_lineMap]
                  exact hge _ hp)
            have hqLower : c ≤ z (R.position q) := by
              calc
                c = z (K.graphBreakpointPoint hcont D C
                    ⟨i, some (some v)⟩) := by
                  dsimp [z, graphBreakpointPoint, graphBreakpointParameter, c]
                  rw [K.edgeParameter_lineMap]
                  exact hvalue.symm
                _ ≤ z (R.position q) := hmono (by
                  rw [graphBreakpointPoint, K.edgeParameter_lineMap]
                  exact hge _ hq)
            exact le_min hpLower hqLower
        · right
          have hcn : n * A.exitData.right < c := by
            have : A.exitData.right < c / n := lt_of_not_ge hv1
            rw [lt_div_iff₀ hn] at this
            simpa [mul_comm] using this
          have hpUpper : z (R.position p) ≤ n * A.exitData.right := by
            dsimp [z]
            have hr := hmid1 (R.position p) hp
            have hmul := mul_le_mul_of_nonneg_left
              (show 4 * K.edgeParameter i (R.position p) - 2 ≤ 1 by linarith) hdelta
            nlinarith
          have hqUpper : z (R.position q) ≤ n * A.exitData.right := by
            dsimp [z]
            have hr := hmid1 (R.position q) hq
            have hmul := mul_le_mul_of_nonneg_left
              (show 4 * K.edgeParameter i (R.position q) - 2 ≤ 1 by linarith) hdelta
            nlinarith
          exact (max_le hpUpper hqUpper).trans hcn.le
    obtain ⟨s, hs, hssegment⟩ := exists_face_containing_axis_segment_of_no_vertex
      A.parameterization.source hn.le hab ha hb A.parameterization.source_support
        A.parameterization.source_card_le_two havoid
    have hsourceImage : middleSourceMap K A '' R.cellCarrier ({p, q} : Finset R.Vertex) =
        segment ℝ (planePoint a 0) (planePoint b 0) := by
      rw [PlaneComplex.cellCarrier]
      have himage : R.position '' (({p, q} : Finset R.Vertex) : Set R.Vertex) =
          {R.position p, R.position q} := by
        ext x
        simp [eq_comm]
      rw [himage, convexHull_pair, image_segment]
      simp only [middleSourceMap_apply]
      change segment ℝ (planePoint (z (R.position p)) 0)
          (planePoint (z (R.position q)) 0) = _
      rcases le_total (z (R.position p)) (z (R.position q)) with hpqz | hqpz
      · simp [a, b, min_eq_left hpqz, max_eq_right hpqz]
      · rw [segment_symm]
        simp [a, b, min_eq_right hqpz, max_eq_left hqpz]
    obtain ⟨g, hg⟩ := A.parameterization.map_affineOn s hs
    refine ⟨g.comp (middleSourceMap K A), ?_⟩
    intro x hx
    have hxSource : middleSourceMap K A x ∈ A.parameterization.source.cellCarrier s := by
      apply hssegment
      rw [← hsourceImage]
      exact ⟨x, hx, rfl⟩
    rw [K.graphReplacementMap_eq_edge_on_cellCarrier hcont D C i (hui hx),
      K.edgeReplacementMap_eq_middle hcont D C i (hui hx) (hmid0 x hx) (hmid1 x hx)]
    exact hg hxSource

/-- The simultaneous edge replacement is affine on every face of its named common source
subdivision. -/
theorem graphReplacementMap_affineOn_subdivision {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) :
    ∀ u ∈ (K.graphReplacementSubdivision hcont D C).simplexes,
      IsAffineOn (K.graphReplacementMap hcont D C)
        ((K.graphReplacementSubdivision hcont D C).cellCarrier u) := by
  let R := K.graphReplacementSubdivision hcont D C
  intro u hu
  have hsub : R.Subdivides K :=
    K.graphReplacementSubdivision_subdivides hgraph hcont D C
  obtain ⟨t, ht, hut⟩ := hsub.2 u hu
  have htpos : 0 < t.card := Finset.card_pos.mpr (K.nonempty_of_mem t ht)
  have htcard := hgraph t ht
  have htCases : t.card = 1 ∨ t.card = 2 := by omega
  rcases htCases with htone | httwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp htone
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.graphReplacementMap hcont D C (K.position v))
    refine ⟨g, ?_⟩
    intro x hx
    have hx' : x = K.position v := by
      have := hut hx
      simpa [PlaneComplex.cellCarrier] using this
    subst x
    rfl
  · have htEdge : t ∈ K.edges := Finset.mem_filter.mpr ⟨ht, httwo⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt ⟨t, htEdge⟩
    have hti : t = (K.edgeAt i).1 := congrArg Subtype.val hi.symm
    subst t
    rcases K.graphReplacementFace_piece hcont D C i hu with hleft | hmiddle | hright
    · exact K.graphReplacementMap_affineOn_left hcont D C i hut hleft
    · exact K.graphReplacementMap_affineOn_middle hcont D C i hu hut hmiddle.1 hmiddle.2
    · exact K.graphReplacementMap_affineOn_right hcont D C i hut hright

/-- The simultaneous edge replacement is PL on the original graph.  All breakpoints of all
polygonal middle arcs occur as vertices of one common finite subdivision. -/
theorem graphReplacementMap_isPL {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) :
    IsPLOn K (K.graphReplacementMap hcont D C) := by
  exact ⟨K.graphReplacementSubdivision hcont D C,
    K.graphReplacementSubdivision_subdivides hgraph hcont D C,
    K.graphReplacementMap_affineOn_subdivision hgraph hcont D C⟩

theorem edgeReplacementMap_mem_interiorCarrier {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (i : Fin (Fintype.card K.EdgeFace))
    {x : Plane} (hx : x ∈ K.cellCarrier (K.edgeAt i).1)
    (hnv : ¬K.IsGraphVertexPoint x) :
    K.edgeReplacementMap hcont D C i x ∈
      (K.replacementArc hcont D C i).interiorCarrier := by
  let A := K.replacementArc hcont D C i
  have hcarrier : K.edgeReplacementMap hcont D C i x ∈ A.completeCarrier := by
    rw [← K.edgeReplacementMap_image_cellCarrier hcont D C i]
    exact ⟨x, hx, rfl⟩
  rw [← A.completeCarrier_sdiff_endpoints]
  refine ⟨hcarrier, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro heq
    have hpath := K.edgeReplacementMap_eq_path hcont D C i hx
    have hzero : A.completePath
        ⟨K.edgeParameter i x, K.edgeParameter_mem_Icc i hx⟩ = A.completePath 0 := by
      rw [← hpath, heq]
      exact A.completePath.source.symm
    have hparam : K.edgeParameter i x = 0 := congrArg Subtype.val
      (A.completePath_injective hzero)
    apply hnv
    refine ⟨K.edgeFirst i, ?_, ?_⟩
    · exact K.down_closed (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) {K.edgeFirst i}
        (by simp [K.edgeAt_eq]) (Finset.singleton_nonempty _)
    · calc
        x = AffineMap.lineMap (K.position (K.edgeFirst i))
            (K.position (K.edgeSecond i)) (K.edgeParameter i x) :=
          (K.lineMap_edgeParameter_eq i hx).symm
        _ = K.position (K.edgeFirst i) := by simp [hparam]
  · intro heq
    have hpath := K.edgeReplacementMap_eq_path hcont D C i hx
    have hone : A.completePath
        ⟨K.edgeParameter i x, K.edgeParameter_mem_Icc i hx⟩ = A.completePath 1 := by
      rw [← hpath, heq]
      exact A.completePath.target.symm
    have hparam : K.edgeParameter i x = 1 := congrArg Subtype.val
      (A.completePath_injective hone)
    apply hnv
    refine ⟨K.edgeSecond i, ?_, ?_⟩
    · exact K.down_closed (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) {K.edgeSecond i}
        (by simp [K.edgeAt_eq]) (Finset.singleton_nonempty _)
    · calc
        x = AffineMap.lineMap (K.position (K.edgeFirst i))
            (K.position (K.edgeSecond i)) (K.edgeParameter i x) :=
          (K.lineMap_edgeParameter_eq i hx).symm
        _ = K.position (K.edgeSecond i) := by simp [hparam]

theorem vertex_image_ne_edgeReplacementMap {h : Plane → Plane}
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) (v : K.Vertex)
    (i : Fin (Fintype.card K.EdgeFace)) {x : Plane}
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) (hnv : ¬K.IsGraphVertexPoint x) :
    h (K.position v) ≠ K.edgeReplacementMap hcont D C i x := by
  let A := K.replacementArc hcont D C i
  have hxInterior := K.edgeReplacementMap_mem_interiorCarrier hcont D C i hx hnv
  have hxCarrier : K.edgeReplacementMap hcont D C i x ∈ A.completeCarrier := by
    rw [← K.edgeReplacementMap_image_cellCarrier hcont D C i]
    exact ⟨x, hx, rfl⟩
  by_cases hv : v ∈ (K.edgeAt i).1
  · rw [K.edgeAt_eq] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rw [← A.completeCarrier_sdiff_endpoints] at hxInterior
    rcases hxInterior with ⟨-, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    rcases hv with rfl | rfl
    · exact fun heq => hne.1 heq.symm
    · exact fun heq => hne.2 heq.symm
  · intro heq
    exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hv)
      (Metric.mem_closedBall_self D.radius_pos.le) (heq ▸ hxCarrier)

theorem graphReplacementMap_injectiveOn {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (hinj : Set.InjOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D) :
    Set.InjOn (K.graphReplacementMap hcont D C) K.support := by
  intro x hx y hy hxy
  by_cases hvx : K.IsGraphVertexPoint x
  · obtain ⟨v, hv, rfl⟩ := hvx
    by_cases hvy : K.IsGraphVertexPoint y
    · obtain ⟨w, hw, rfl⟩ := hvy
      apply hinj
      · exact K.cellCarrier_subset_support hv (by simp [PlaneComplex.cellCarrier])
      · exact K.cellCarrier_subset_support hw (by simp [PlaneComplex.cellCarrier])
      rw [K.graphReplacementMap_vertex hcont D C hv,
        K.graphReplacementMap_vertex hcont D C hw] at hxy
      exact hxy
    · rcases K.vertexPoint_or_exists_edge_of_mem_support hgraph hy with hyv | ⟨j, hyj⟩
      · exact (hvy hyv).elim
      · exfalso
        apply K.vertex_image_ne_edgeReplacementMap hcont D C v j hyj hvy
        rw [← K.graphReplacementMap_vertex hcont D C hv,
          ← K.graphReplacementMap_eq_edge hcont D C hvy j hyj]
        exact hxy
  · rcases K.vertexPoint_or_exists_edge_of_mem_support hgraph hx with hxv | ⟨i, hxi⟩
    · exact (hvx hxv).elim
    · by_cases hvy : K.IsGraphVertexPoint y
      · obtain ⟨w, hw, rfl⟩ := hvy
        exfalso
        apply K.vertex_image_ne_edgeReplacementMap hcont D C w i hxi hvx
        rw [← K.graphReplacementMap_vertex hcont D C hw,
          ← K.graphReplacementMap_eq_edge hcont D C hvx i hxi]
        exact hxy.symm
      · rcases K.vertexPoint_or_exists_edge_of_mem_support hgraph hy with hyv | ⟨j, hyj⟩
        · exact (hvy hyv).elim
        · rw [K.graphReplacementMap_eq_edge hcont D C hvx i hxi,
            K.graphReplacementMap_eq_edge hcont D C hvy j hyj] at hxy
          by_cases hij : i = j
          · subst j
            have hpathX := K.edgeReplacementMap_eq_path hcont D C i hxi
            have hpathY := K.edgeReplacementMap_eq_path hcont D C i hyj
            have hparam : K.edgeParameter i x = K.edgeParameter i y :=
              congrArg Subtype.val
                ((K.replacementArc hcont D C i).completePath_injective
                  (hpathX.symm.trans (hxy.trans hpathY)))
            calc
              x = AffineMap.lineMap (K.position (K.edgeFirst i))
                  (K.position (K.edgeSecond i)) (K.edgeParameter i x) :=
                (K.lineMap_edgeParameter_eq i hxi).symm
              _ = AffineMap.lineMap (K.position (K.edgeFirst i))
                  (K.position (K.edgeSecond i)) (K.edgeParameter i y) := by rw [hparam]
              _ = y := K.lineMap_edgeParameter_eq i hyj
          · have hxInt := K.edgeReplacementMap_mem_interiorCarrier hcont D C i hxi hvx
            have hyInt := K.edgeReplacementMap_mem_interiorCarrier hcont D C j hyj hvy
            exact (Set.disjoint_left.mp
              (CentralPolygonalArc.disjoint_interiorCarrier
                (A' := K.replacementArc hcont D C j)
                (K.replacementArc hcont D C i) hij) hxInt (hxy ▸ hyInt)).elim

/-- Moise's simultaneous polygonal replacement gives a PL embedding of the finite source
graph, before imposing a quantitative approximation bound. -/
theorem graphReplacementMap_isPLEmbeddingOn {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (hinj : Set.InjOn h K.support)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont D) :
    IsPLEmbeddingOn K (K.graphReplacementMap hcont D C) :=
  ⟨K.graphReplacementMap_isPL hgraph hcont D C,
    K.graphReplacementMap_injectiveOn hgraph hcont hinj D C⟩

/-- If the image of every source face has diameter below `η`, and both geometric controls are
smaller than `η`, then simultaneous polygonal replacement moves every graph point by less than
`2 * η`. -/
theorem graphReplacementMap_dist_lt_two_mul {h : Plane → Plane}
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hcont : ContinuousOn h K.support) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont D) {η : ℝ}
    (hsmall : ∀ u ∈ K.simplexes, ∀ x ∈ K.cellCarrier u,
      ∀ y ∈ K.cellCarrier u, dist (h x) (h y) < η)
    (hD : D.radius < η) :
    ∀ x ∈ K.support,
      dist (K.graphReplacementMap hcont D C x) (h x) < 2 * η := by
  intro x hx
  rcases K.vertexPoint_or_exists_edge_of_mem_support hgraph hx with hxv | ⟨i, hxi⟩
  · obtain ⟨v, hv, rfl⟩ := hxv
    rw [K.graphReplacementMap_vertex hcont D C hv, dist_self]
    linarith [D.radius_pos, hD]
  · let A := K.replacementArc hcont D C i
    have hyCarrier : K.edgeReplacementMap hcont D C i x ∈ A.completeCarrier := by
      rw [← K.edgeReplacementMap_image_cellCarrier hcont D C i]
      exact ⟨x, hxi, rfl⟩
    have hxMap : K.graphReplacementMap hcont D C x =
        K.edgeReplacementMap hcont D C i x :=
      K.graphReplacementMap_eq_edge_on_cellCarrier hcont D C i hxi
    rw [hxMap]
    have hfirst : K.position (K.edgeFirst i) ∈ K.cellCarrier (K.edgeAt i).1 := by
      exact subset_convexHull ℝ _ ⟨K.edgeFirst i, by simp [K.edgeAt_eq], rfl⟩
    have hsecond : K.position (K.edgeSecond i) ∈ K.cellCarrier (K.edgeAt i).1 := by
      exact subset_convexHull ℝ _ ⟨K.edgeSecond i, by simp [K.edgeAt_eq], rfl⟩
    rcases hyCarrier with (hyLeft | hyMiddle) | hyRight
    · have hyBall := A.leftSpoke_subset_disk hyLeft
      calc
        dist (K.edgeReplacementMap hcont D C i x) (h x) ≤
            dist (K.edgeReplacementMap hcont D C i x)
                (h (K.position (K.edgeFirst i))) +
              dist (h (K.position (K.edgeFirst i))) (h x) := dist_triangle _ _ _
        _ < η + η := add_lt_add
          ((Metric.mem_closedBall.mp hyBall).trans_lt hD)
          (by simpa [dist_comm] using
            hsmall (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) x hxi _ hfirst)
        _ = 2 * η := by ring
    · have hyTube := A.resolvedCarrier_subset_tube
          (A.trimmedCarrier_subset_resolvedCarrier hyMiddle)
      obtain ⟨y, hyCentral, hdist⟩ := Metric.mem_thickening_iff.mp hyTube
      obtain ⟨t, ht, rfl⟩ := hyCentral
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨(K.edgeTrim hcont D i).left_pos.le.trans ht.1,
          ht.2.trans (K.edgeTrim hcont D i).right_lt_one.le⟩
      have htCarrier : AffineMap.lineMap (K.position (K.edgeFirst i))
          (K.position (K.edgeSecond i)) t ∈ K.cellCarrier (K.edgeAt i).1 := by
        rw [K.edgeAt_eq, PlaneComplex.cellCarrier]
        have himage : K.position ''
            (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
            {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
          ext y
          simp [eq_comm]
        rw [himage, convexHull_pair]
        exact lineMap_mem_segment ℝ _ _ htIcc
      calc
        dist (K.edgeReplacementMap hcont D C i x) (h x) ≤
            dist (K.edgeReplacementMap hcont D C i x)
                (K.edgeCurve h i t) + dist (K.edgeCurve h i t) (h x) :=
          dist_triangle _ _ _
        _ < η + η := add_lt_add (hdist.trans (C.radius_lt_vertex.trans hD))
          (by simpa [edgeCurve, dist_comm] using
            hsmall (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) x hxi _ htCarrier)
        _ = 2 * η := by ring
    · have hyBall := A.rightSpoke_subset_disk hyRight
      calc
        dist (K.edgeReplacementMap hcont D C i x) (h x) ≤
            dist (K.edgeReplacementMap hcont D C i x)
                (h (K.position (K.edgeSecond i))) +
              dist (h (K.position (K.edgeSecond i))) (h x) := dist_triangle _ _ _
        _ < η + η := add_lt_add
          ((Metric.mem_closedBall.mp hyBall).trans_lt hD)
          (by simpa [dist_comm] using
            hsmall (K.edgeAt i).1 (K.edgeAt_mem_simplexes i) x hxi _ hsecond)
        _ = 2 * η := by ring

/-- Moise Chapter 6, Theorem 2 for finite plane complexes: after first sampling the source
graph finely, simultaneous polygonal replacement gives an arbitrarily close PL embedding and
preserves every original vertex value. -/
theorem exists_graph_PL_approximation_facewise (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      (∀ v : K.Vertex, f (K.position v) = h (K.position v)) ∧
      (∀ x ∈ K.support, dist (f x) (h x) < ε) ∧
      (∀ x ∈ K.support, f x ∈ convexHull ℝ (h '' K.support)) ∧
      ∀ A : Set Plane,
        (∀ x ∈ A, ∃ s ∈ K.simplexes,
          x ∈ K.cellCarrier s ∧ K.cellCarrier s ⊆ A) →
        IsPLOnSet A f := by
  let η := ε / 3
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨cuts, hsmall0⟩ :=
    K.exists_sampledEdgeSubdivision_image_diameter_lt hgraph hcont hη
  let L0 := K.sampledEdgeSubdivision cuts
  let L := PlaneComplex.used L0
  have hsub0 : L0.Subdivides K := K.sampledEdgeSubdivision_subdivides cuts hgraph
  have hsub : L.Subdivides K := PlaneComplex.used_subdivides_left hsub0
  have hgraphL : ∀ s ∈ L.simplexes, s.card ≤ 2 := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hsub.2 s hs
    exact card_le_two_of_cellCarrier_subset_face hs ht (hgraph t ht) hst
  have hcontL : ContinuousOn h L.support := by
    rw [hsub.1]
    exact hcont
  have hinjL : Set.InjOn h L.support := by
    rw [hsub.1]
    exact hinj
  have hsmallL : ∀ u ∈ L.simplexes, ∀ x ∈ L.cellCarrier u,
      ∀ y ∈ L.cellCarrier u, dist (h x) (h y) < η := by
    intro u hu x hx y hy
    have hx' := hx
    have hy' := hy
    change x ∈ (PlaneComplex.used L0).cellCarrier u at hx'
    change y ∈ (PlaneComplex.used L0).cellCarrier u at hy'
    erw [L0.used_cellCarrier] at hx' hy'
    exact hsmall0 (u.map L0.usedEmbedding) (L0.mem_usedSimplexes.mp hu) x hx' y hy'
  obtain ⟨D, hD⟩ := L.exists_vertexDiskControl_lt
    (fun v => L0.used_vertex_face v) hcontL hinjL hη
  obtain ⟨C⟩ := L.exists_centralTubeControl hcontL hinjL D
  let f := L.graphReplacementMap hcontL D C
  refine ⟨f, IsPLOn.of_subdivision hsub
      (L.graphReplacementMap_isPL hgraphL hcontL D C), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsub.1]
    exact L.graphReplacementMap_injectiveOn hgraphL hcontL hinjL D C
  · intro v
    by_cases hv : K.position v ∈ K.support
    · obtain ⟨w0, hwpos, hwface⟩ :=
        K.exists_sampledEdgeSubdivision_vertex_position_eq cuts v hv
      let w : L.Vertex := ⟨w0, ⟨{w0}, hwface, by simp⟩⟩
      have hw : ({w} : Finset L.Vertex) ∈ L.simplexes := L0.used_vertex_face w
      calc
        f (K.position v) = f (L.position w) := by rw [show L.position w = K.position v from hwpos]
        _ = h (L.position w) := L.graphReplacementMap_vertex hcontL D C hw
        _ = h (K.position v) := by rw [show L.position w = K.position v from hwpos]
    · have hvL : K.position v ∉ L.support := by rwa [hsub.1]
      have hnv : ¬L.IsGraphVertexPoint (K.position v) := by
        rintro ⟨w, hw, heq⟩
        apply hvL
        rw [heq]
        exact L.cellCarrier_subset_support hw
          (subset_convexHull ℝ _ ⟨w, by simp, rfl⟩)
      have hne : ¬∃ i : Fin (Fintype.card L.EdgeFace),
          K.position v ∈ L.cellCarrier (L.edgeAt i).1 := by
        rintro ⟨i, hi⟩
        exact hvL (L.cellCarrier_subset_support (L.edgeAt_mem_simplexes i) hi)
      simp [f, PlaneComplex.graphReplacementMap, hnv, hne]
  · intro x hx
    have hbound := L.graphReplacementMap_dist_lt_two_mul hgraphL hcontL D C hsmallL hD x
      (by rwa [hsub.1])
    dsimp [f]
    dsimp [η] at hbound
    linarith
  · intro x hx
    have hxL : x ∈ L.support := by rwa [hsub.1]
    have hconvex := L.graphReplacementMap_mem_targetConvexHull
      hgraphL hcontL D C hxL
    rw [hsub.1] at hconvex
    exact hconvex
  · intro A hA
    have hAL : ∀ x ∈ A, ∃ s ∈ L.simplexes,
        x ∈ L.cellCarrier s ∧ L.cellCarrier s ⊆ A := by
      intro x hx
      obtain ⟨s, hs, hxs, hsA⟩ := hA x hx
      obtain ⟨u, hu, hxu, huS⟩ :=
        K.exists_sampledEdgeSubdivision_face_at cuts hgraph hs hxs
      obtain ⟨w, hw, -, hwCarrier⟩ := L0.exists_used_face_eq u hu
      refine ⟨w, hw, ?_, ?_⟩
      · rw [hwCarrier]
        exact hxu
      · rw [hwCarrier]
        exact huS.trans hsA
    let R := L.graphReplacementSubdivision hcontL D C
    let S := R.restrictToSet A
    have hSsupport : S.support = A := by
      change ((L.markedEdgeSubdivision (L.graphBreakpointPoint hcontL D C))
        |>.restrictToSet A).support = A
      exact L.markedEdgeSubdivision_restrictToSet_support_eq
        (L.graphBreakpointPoint hcontL D C) hgraphL A hAL
    refine ⟨S, hSsupport, S, PlaneComplex.Subdivides.refl S, ?_⟩
    intro u hu
    have huR : u ∈ R.simplexes := (R.mem_restrictToSet_simplexes_iff A).mp hu |>.1
    exact L.graphReplacementMap_affineOn_subdivision hgraphL hcontL D C u huR

/-- Moise Chapter 6, Theorem 2 in its conventional interface. -/
theorem exists_graph_PL_approximation (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      (∀ v : K.Vertex, f (K.position v) = h (K.position v)) ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε := by
  obtain ⟨f, hpl, hinj, hvertex, hclose, -, -⟩ :=
    K.exists_graph_PL_approximation_facewise hgraph hcont hinj hε
  exact ⟨f, hpl, hinj, hvertex, hclose⟩

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification09_block_03
/- END ClassificationOfSurfaces.Moise.GraphPolygonalization -/

/- BEGIN ClassificationOfSurfaces.Moise.PLMoves | a689e4d3a6916ede440fe2272631a27a072c18b4c32729de7651f0210029714d -/
section schottkyclassification09_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# PL certificates for the elementary Schoenflies moves

The topological homeomorphisms used by the Chapter 3 ear shelling were constructed earlier by
barycentric repositioning.  This file records the missing PL certificates used in Chapter 5.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Extending a self-homeomorphism of a closed patch by the identity preserves that patch
setwise. -/
theorem extendHomeomorphByIdentity_image {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x) :
    extendHomeomorphByIdentity hP e hfrontier '' P = P := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [extendHomeomorphByIdentity_apply_mem hP e hfrontier hx]
    exact (e ⟨x, hx⟩).property
  · intro y hy
    let x : P := e.symm ⟨y, hy⟩
    refine ⟨x, x.property, ?_⟩
    rw [extendHomeomorphByIdentity_apply_mem hP e hfrontier x.property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- An affine equivalence is finite PL on the support of any explicit pure complex. -/
def affineEquivHomeomorphFinitePL (e : Plane ≃ᵃ[ℝ] Plane)
    (K : PlaneComplex) (hpure : K.IsPure2) :
    FinitePLHomeomorphOn (affineEquivHomeomorph e) K.support where
  complex := K
  support_eq := rfl
  pure := hpure
  affineOn := by
    intro s hs
    exact ⟨e.toAffineMap, fun _ _ => rfl⟩

namespace TriangleMesh

variable (M : TriangleMesh)

/-- All nonempty faces of the incidence-one edges of a triangle mesh. -/
noncomputable def boundaryFaces : Finset (Finset M.Vertex) := by
  classical
  exact M.allBoundaryEdges.biUnion fun e => e.powerset.filter (·.Nonempty)

theorem mem_boundaryFaces_iff {s : Finset M.Vertex} :
    s ∈ M.boundaryFaces ↔ s.Nonempty ∧ ∃ e ∈ M.allBoundaryEdges, s ⊆ e := by
  classical
  simp [boundaryFaces, and_assoc, and_comm]

/-- The incidence-one edges and their faces form a finite one-dimensional plane complex. -/
noncomputable def boundaryComplex : PlaneComplex where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  simplexes := M.boundaryFaces
  nonempty_of_mem := fun s hs => (M.mem_boundaryFaces_iff.mp hs).1
  card_le_three := by
    intro s hs
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    have hecard : e.card = 2 :=
      M.card_of_mem_edges (M.mem_allBoundaryEdges_iff.mp he).1
    exact (Finset.card_le_card hse).trans (by omega)
  down_closed := by
    intro s hs t hts ht
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    exact M.mem_boundaryFaces_iff.mpr ⟨ht, e, he, hts.trans hse⟩
  affineIndependent := by
    intro s hs
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    obtain ⟨u, hu, heu⟩ :=
      Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp he).1
    exact (M.affineIndependent_triangle u hu).comp_embedding
      ⟨fun v : s => (⟨v.1, (Finset.mem_powersetCard.mp heu).1 (hse v.2)⟩ : u), by
        intro v w hvw
        apply Subtype.ext
        exact congrArg (fun q : u => q.1) hvw⟩
  face_inter := by
    intro s hs t ht
    obtain ⟨hsne, es, hes, hses⟩ := M.mem_boundaryFaces_iff.mp hs
    obtain ⟨htne, et, het, htet⟩ := M.mem_boundaryFaces_iff.mp ht
    have hsM : s ∈ M.toPlaneComplex.simplexes := by
      apply M.mem_faces_iff.mpr
      obtain ⟨u, hu, heu⟩ :=
        Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp hes).1
      exact ⟨hsne, u, hu, hses.trans (Finset.mem_powersetCard.mp heu).1⟩
    have htM : t ∈ M.toPlaneComplex.simplexes := by
      apply M.mem_faces_iff.mpr
      obtain ⟨u, hu, heu⟩ :=
        Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp het).1
      exact ⟨htne, u, hu, htet.trans (Finset.mem_powersetCard.mp heu).1⟩
    exact M.toPlaneComplex.face_inter s hsM t htM

theorem boundaryComplex_support :
    M.boundaryComplex.support = M.boundaryCarrier := by
  classical
  rw [PlaneComplex.support, boundaryCarrier]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    exact ⟨e, he, convexHull_mono (Set.image_mono hse) hxs⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨e, he, hxe⟩ := hx
    have hene : e.Nonempty := Finset.card_pos.mp (by
      rw [M.card_of_mem_edges (M.mem_allBoundaryEdges_iff.mp he).1]
      omega)
    exact ⟨e, M.mem_boundaryFaces_iff.mpr ⟨hene, e, he, subset_rfl⟩, hxe⟩

/-- Every boundary-complex face is a face of the full mesh complex. -/
theorem boundaryComplex_simplex_mem_toPlaneComplex {s : Finset M.Vertex}
    (hs : s ∈ M.boundaryComplex.simplexes) :
    s ∈ M.toPlaneComplex.simplexes := by
  obtain ⟨hsne, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
  obtain ⟨u, hu, heu⟩ :=
    Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp he).1
  exact M.mem_faces_iff.mpr
    ⟨hsne, u, hu, hse.trans (Finset.mem_powersetCard.mp heu).1⟩

/-- On its closed patch, an ambient barycentric repositioning agrees with the facewise-affine
`PlaneComplex.repositionMap`. -/
theorem ambientRepositionHomeomorph_eq_repositionMap_on_support
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Set.EqOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      (M.toPlaneComplex.repositionMap position' hinj
        (fun s hs =>
          (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.affineIndependent
            s hs)
        (fun s hs t ht =>
          (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.face_inter
            s hs t ht))
      M.toPlaneComplex.support := by
  classical
  let K := M.toPlaneComplex
  let N := M.reposition position' hinj haffTriangle hinterTriangle
  have hKpure : K.IsPure2 := by
    simpa only [K] using M.toPlaneComplex_isPure2
  let haff : ∀ s : Finset M.Vertex, s ∈ K.simplexes →
      AffineIndependent ℝ fun v : s => position' v := by
    intro s hs
    exact N.toPlaneComplex.affineIndependent s hs
  let hface : ∀ s : Finset M.Vertex, s ∈ K.simplexes →
      ∀ t : Finset M.Vertex, t ∈ K.simplexes →
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)) :=
    fun s hs t ht => N.toPlaneComplex.face_inter s hs t ht
  intro x hx
  have hxK : x ∈ K.support := by simpa only [K] using hx
  rw [PlaneComplex.support] at hxK
  simp only [Set.mem_iUnion] at hxK
  obtain ⟨s, hs, hxs⟩ := hxK
  obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hxs
  obtain ⟨u, hu, hsu, hucard⟩ := hKpure s hs
  have hucell : u ∈ K.cells := Finset.mem_filter.mpr ⟨hu, hucard⟩
  have hzu : ∀ v ∉ u, z v = 0 := fun v hv => hzsupp v (fun hvs => hv (hsu hvs))
  let xa : GeometricRealization K.Vertex K.simplexes :=
    ⟨z, ⟨hz0, hz1⟩, s, hs, hzsupp⟩
  let xc : GeometricRealization K.Vertex K.cells :=
    ⟨z, ⟨hz0, hz1⟩, u, hucell, hzu⟩
  have hrmap : K.repositionMap position' hinj haff hface x =
      (K.reposition position' hinj haff hface).baryEval z := by
    rw [← hzeval]
    exact K.repositionMap_apply_realization position' hinj haff hface xa
  have hambient :
      M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
          hsupport hfrontier x = N.toPlaneComplex.baryEval z := by
    rw [ambientRepositionHomeomorph,
      extendHomeomorphByIdentity_apply_mem _ _ _ (by simpa only [K] using hx)]
    have hxc :
        (K.realizationHomeomorph hKpure).symm
          ⟨x, by simpa only [K] using hx⟩ = xc := by
      apply (K.realizationHomeomorph hKpure).injective
      apply Subtype.ext
      simpa [xc] using hzeval.symm
    rw [TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply, hxc]
  rw [hrmap, hambient]
  rfl

/-- An ambient barycentric repositioning is affine on every face of its source mesh. -/
theorem ambientRepositionHomeomorph_affineOn
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x)
    {s : Finset M.Vertex} (hs : s ∈ M.toPlaneComplex.simplexes) :
    IsAffineOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      (M.toPlaneComplex.cellCarrier s) := by
  let haff : ∀ u : Finset M.Vertex, u ∈ M.toPlaneComplex.simplexes →
      AffineIndependent ℝ fun v : u => position' v :=
    fun u hu =>
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.affineIndependent
        u hu
  let hface : ∀ u : Finset M.Vertex, u ∈ M.toPlaneComplex.simplexes →
      ∀ v : Finset M.Vertex, v ∈ M.toPlaneComplex.simplexes →
      convexHull ℝ (position' '' (u : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (v : Set M.Vertex)) =
        convexHull ℝ (position' '' ((u ∩ v : Finset M.Vertex) : Set M.Vertex)) :=
    fun u hu v hv =>
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.face_inter
        u hu v hv
  obtain ⟨g, hg⟩ := M.toPlaneComplex.repositionMap_affineOn_face
    position' hinj haff hface hs
  refine ⟨g, fun x hx => ?_⟩
  exact (M.ambientRepositionHomeomorph_eq_repositionMap_on_support position' hinj
    haffTriangle hinterTriangle hsupport hfrontier
      (M.toPlaneComplex.cellCarrier_subset_support hs hx)).trans (hg hx)

/-- An ambient barycentric repositioning, together with its original mesh, is a finite PL
homeomorphism on the closed patch. -/
noncomputable def ambientRepositionHomeomorphFinitePL
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    FinitePLHomeomorphOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      M.toPlaneComplex.support where
  complex := M.toPlaneComplex
  support_eq := rfl
  pure := M.toPlaneComplex_isPure2
  affineOn := by
    intro s hs
    exact M.ambientRepositionHomeomorph_affineOn position' hinj haffTriangle
      hinterTriangle hsupport hfrontier hs

end TriangleMesh

/-- The elementary diamond fan move is a finite PL homeomorphism on the diamond. -/
noncomputable def diamondFanAmbientHomeomorphFinitePL (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    FinitePLHomeomorphOn (diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1)
      diamondPatch := by
  refine {
    complex := (diamondFanMesh a ha0 ha1).toPlaneComplex
    support_eq := diamondFanMesh_support a ha0 ha1
    pure := (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  exact (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph_affineOn
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1) hs

theorem diamondFanAmbientHomeomorph_image (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1 '' diamondPatch = diamondPatch := by
  rw [← diamondFanMesh_support a ha0 ha1]
  exact extendHomeomorphByIdentity_image
    (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)

/-! ## The outer kite coordinate change -/

/-- The affine formula for `thinKiteMap` on the left half-plane. -/
noncomputable def thinKiteLeftAffine (δ : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.toAffineMap.comp
    (AffineMap.pi ![cartesianX,
      thinKiteScale δ • cartesianY + (2 : ℝ)⁻¹ • cartesianX +
        AffineMap.const ℝ Plane (2 : ℝ)⁻¹])

/-- The affine formula for `thinKiteMap` on the right half-plane. -/
noncomputable def thinKiteRightAffine (δ : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.toAffineMap.comp
    (AffineMap.pi ![cartesianX,
      thinKiteScale δ • cartesianY - (2 : ℝ)⁻¹ • cartesianX +
        AffineMap.const ℝ Plane (2 : ℝ)⁻¹])

theorem thinKiteMap_eq_leftAffine (δ : ℝ) {p : Plane} (hp : p 0 ≤ 0) :
    thinKiteMap δ p = thinKiteLeftAffine δ p := by
  apply plane_ext
  · simp [thinKiteMap, thinKiteLeftAffine]
  · simp only [thinKiteMap, planePoint_apply_one]
    rw [show |p 0| = -p 0 from abs_of_nonpos hp]
    simp [thinKiteLeftAffine]
    ring

theorem thinKiteMap_eq_rightAffine (δ : ℝ) {p : Plane} (hp : 0 ≤ p 0) :
    thinKiteMap δ p = thinKiteRightAffine δ p := by
  apply plane_ext
  · simp [thinKiteMap, thinKiteRightAffine]
  · simp only [thinKiteMap, planePoint_apply_one]
    rw [show |p 0| = p 0 from abs_of_nonneg hp]
    simp [thinKiteRightAffine]
    ring

theorem nonpos_zero_of_mem_axisKite_left {lo hi : ℝ} {p : Plane}
    (hp : p ∈ convexHull ℝ
      (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _))) :
    p 0 ≤ 0 := by
  have hp' : p ∈ {q : Plane | cartesianX q ∈ Set.Iic (0 : ℝ)} := by
    apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨v, hv, rfl⟩
    fin_cases v <;> simp [axisKitePosition] at hv ⊢
  exact hp'

theorem nonneg_zero_of_mem_axisKite_right {lo hi : ℝ} {p : Plane}
    (hp : p ∈ convexHull ℝ
      (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _))) :
    0 ≤ p 0 := by
  have hp' : p ∈ {q : Plane | cartesianX q ∈ Set.Ici (0 : ℝ)} := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨v, hv, rfl⟩
    fin_cases v <;> simp [axisKitePosition] at hv ⊢
  exact hp'

/-- The explicit global change from the fixed diamond to a thin kite is finite PL on the
diamond's two-triangle mesh. -/
noncomputable def thinKiteGlobalHomeomorphFinitePL (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (thinKiteGlobalHomeomorph δ hδ) diamondPatch := by
  refine {
    complex := (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).toPlaneComplex
    support_eq := (axisKiteMesh_support (-2) 2 (by norm_num) (by norm_num)).trans
      axisKitePatch_negTwo_two
    pure := (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  obtain ⟨-, t, ht, hst⟩ :=
    (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).mem_faces_iff.mp hs
  change Finset (Fin 4) at t
  change t ∈ axisKiteTriangles at ht
  have ht' : t = {0, 2, 3} ∨ t = {1, 2, 3} := by
    simpa [axisKiteTriangles] using ht
  rcases ht' with ht' | ht'
  · subst t
    refine ⟨thinKiteLeftAffine δ, fun p hp => ?_⟩
    change thinKiteMap δ p = thinKiteLeftAffine δ p
    apply thinKiteMap_eq_leftAffine
    apply nonpos_zero_of_mem_axisKite_left
    exact convexHull_mono (Set.image_mono hst) hp
  · subst t
    refine ⟨thinKiteRightAffine δ, fun p hp => ?_⟩
    change thinKiteMap δ p = thinKiteRightAffine δ p
    apply thinKiteMap_eq_rightAffine
    apply nonneg_zero_of_mem_axisKite_right
    exact convexHull_mono (Set.image_mono hst) hp

theorem thinKiteGlobalHomeomorph_image (δ : ℝ) (hδ : 0 < δ) :
    thinKiteGlobalHomeomorph δ hδ '' diamondPatch = thinKitePatch δ := by
  rfl

/-- The normalized thin-kite shelling move is finite PL on its kite patch. -/
noncomputable def thinKiteAmbientHomeomorphFinitePL (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (thinKiteAmbientHomeomorph δ hδ) (thinKitePatch δ) := by
  let outer := thinKiteGlobalHomeomorph δ hδ
  let move := diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  let Fouter := thinKiteGlobalHomeomorphFinitePL δ hδ
  let Fmove := diamondFanAmbientHomeomorphFinitePL
    (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  have houter : outer '' diamondPatch = thinKitePatch δ :=
    thinKiteGlobalHomeomorph_image δ hδ
  have hpull : outer.symm '' thinKitePatch δ = diamondPatch := by
    rw [← houter]
    ext p
    simp
  have hmove : move '' diamondPatch = diamondPatch :=
    diamondFanAmbientHomeomorph_image
      (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  let Fpull := Fouter.symm |>.congrSet houter
  let Fmove' := Fmove.congrSet hpull.symm
  let Ffirst := Fpull.trans Fmove'
  have hfirst : (outer.symm.trans move) '' thinKitePatch δ = diamondPatch := by
    change (fun p => move (outer.symm p)) '' thinKitePatch δ = diamondPatch
    rw [← Set.image_image, hpull, hmove]
  let Fouter' := Fouter.congrSet hfirst.symm
  let Ftotal := Ffirst.trans Fouter'
  apply Ftotal.congrHomeomorph
  apply Homeomorph.ext
  intro p
  rfl

theorem thinKiteAmbientHomeomorph_image (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ '' thinKitePatch δ = thinKitePatch δ := by
  let outer := thinKiteGlobalHomeomorph δ hδ
  let move := diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  have houter : outer '' diamondPatch = thinKitePatch δ :=
    thinKiteGlobalHomeomorph_image δ hδ
  have hpull : outer.symm '' thinKitePatch δ = diamondPatch := by
    rw [← houter]
    ext p
    simp
  have hmove : move '' diamondPatch = diamondPatch :=
    diamondFanAmbientHomeomorph_image
      (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  change (fun p => outer (move (outer.symm p))) '' thinKitePatch δ =
    thinKitePatch δ
  rw [← Set.image_image outer (fun p => move (outer.symm p)),
    ← Set.image_image move outer.symm, hpull, hmove, houter]

/-- Affine transport preserves the finite-PL certificate for the local thin-kite move. -/
noncomputable def transportedThinKiteHomeomorphFinitePL
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ)
      (transportedThinKitePatch e δ) := by
  let affine := affineEquivHomeomorph e
  let thin := thinKiteAmbientHomeomorph δ hδ
  let Fthin := thinKiteAmbientHomeomorphFinitePL δ hδ
  let Faff := (affineEquivHomeomorphFinitePL e Fthin.complex Fthin.pure).congrSet
    Fthin.support_eq
  have hpull : affine.symm '' (affine '' thinKitePatch δ) = thinKitePatch δ := by
    ext p
    simp [affine]
  have hthin : thin '' thinKitePatch δ = thinKitePatch δ :=
    thinKiteAmbientHomeomorph_image δ hδ
  let Fpull := Faff.symm
  let Fthin' := Fthin.congrSet hpull.symm
  let Ffirst := Fpull.trans Fthin'
  have hfirst : (affine.symm.trans thin) '' (affine '' thinKitePatch δ) =
      thinKitePatch δ := by
    change (fun p => thin (affine.symm p)) '' (affine '' thinKitePatch δ) =
      thinKitePatch δ
    rw [← Set.image_image, hpull, hthin]
  let Faff' := Faff.congrSet hfirst.symm
  let Ftotal := Ffirst.trans Faff'
  have hhome : (affine.symm.trans thin).trans affine =
      transportedThinKiteHomeomorph e δ hδ := by
    apply Homeomorph.ext
    intro p
    rfl
  exact (Ftotal.congrHomeomorph hhome).congrSet rfl

theorem transportedThinKiteHomeomorph_image
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ) :
    transportedThinKiteHomeomorph e δ hδ '' transportedThinKitePatch e δ =
      transportedThinKitePatch e δ := by
  let affine := affineEquivHomeomorph e
  let thin := thinKiteAmbientHomeomorph δ hδ
  have hpull : affine.symm '' (affine '' thinKitePatch δ) = thinKitePatch δ := by
    ext p
    simp [affine]
  change (fun p => affine (thin (affine.symm p))) '' (affine '' thinKitePatch δ) =
    affine '' thinKitePatch δ
  rw [← Set.image_image affine (fun p => thin (affine.symm p)),
    ← Set.image_image thin affine.symm, hpull,
    thinKiteAmbientHomeomorph_image δ hδ]

/-- A transported local move is finite PL on any finite pure source polyhedron. -/
noncomputable def transportedThinKiteHomeomorphFinitePLOn
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ)
    (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ) K.support :=
  (transportedThinKiteHomeomorphFinitePL e δ hδ).extendByIdentity
    (transportedThinKiteHomeomorph_eqOn_compl e δ hδ) K hKpure

/-- The inverse transported local move is likewise finite PL on any finite pure polyhedron. -/
noncomputable def transportedThinKiteHomeomorphSymmFinitePLOn
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ)
    (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ).symm K.support := by
  let g := transportedThinKiteHomeomorph e δ hδ
  let P := transportedThinKitePatch e δ
  let F := transportedThinKiteHomeomorphFinitePL e δ hδ
  have himage : g '' P = P := transportedThinKiteHomeomorph_image e δ hδ
  let Finv := F.symm |>.congrSet himage
  have hfixInv : Set.EqOn g.symm id Pᶜ := by
    intro p hp
    apply g.symm_apply_eq.mpr
    exact (transportedThinKiteHomeomorph_eqOn_compl e δ hδ hp).symm
  exact Finv.extendByIdentity hfixInv K hKpure

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification09_block_04
/- END ClassificationOfSurfaces.Moise.PLMoves -/

/- BEGIN ClassificationOfSurfaces.TriangleCell | 6b57cfcafbeb97eb6fe219e4aea99a2fac958035d80ea6820d66e45e8841558e -/
section schottkyclassification09_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# A side-parameter-compatible polygon cell model for a triangle

This file identifies the three-sided `PolygonCell` with the standard closed triangle.  The
boundary calibration is exact: circular side `i` at parameter `t` is sent to the affine point at
parameter `t` on standard triangle edge `i`.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Moise

namespace TriangleCell

local instance : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩

/-- The closed standard triangle, viewed as a topological subspace. -/
abbrev StandardTriangle :=
  Moise.standardTrianglePlaneComplex.support

/-- The frontier of the standard triangle. -/
abbrev StandardTriangleBoundary :=
  frontier Moise.standardTrianglePlaneComplex.support

/-- Traverse the three affine sides of the standard triangle during the interval `[0, 3]`. -/
noncomputable def boundaryParam (x : ℝ) : Moise.Plane :=
  if x ≤ 1 then
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 0) (Moise.standardTriangleVertex 1) x
  else if x ≤ 2 then
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 1) (Moise.standardTriangleVertex 2) (x - 1)
  else
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 2) (Moise.standardTriangleVertex 0) (x - 2)

theorem continuous_boundaryParam : Continuous boundaryParam := by
  unfold boundaryParam
  apply Continuous.if_le
    (by fun_prop)
    (by
      apply Continuous.if_le (by fun_prop) (by fun_prop)
        continuous_id continuous_const
      intro x hx
      change x = 2 at hx
      subst x
      norm_num [AffineMap.lineMap_apply_module])
    continuous_id continuous_const
  intro x hx
  change x = 1 at hx
  subst x
  norm_num [AffineMap.lineMap_apply_module]

@[simp]
theorem boundaryParam_zero :
    boundaryParam 0 = Moise.standardTriangleVertex 0 := by
  simp [boundaryParam]

@[simp]
theorem boundaryParam_one :
    boundaryParam 1 = Moise.standardTriangleVertex 1 := by
  simp [boundaryParam]

@[simp]
theorem boundaryParam_two :
    boundaryParam 2 = Moise.standardTriangleVertex 2 := by
  norm_num [boundaryParam]

@[simp]
theorem boundaryParam_three :
    boundaryParam 3 = Moise.standardTriangleVertex 0 := by
  norm_num [boundaryParam]

theorem boundaryParam_mem_frontier {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    boundaryParam x ∈ StandardTriangleBoundary := by
  change boundaryParam x ∈
    frontier Moise.standardTrianglePlaneComplex.support
  rw [Moise.standardTrianglePlaneComplex_support,
    ← Moise.standardTriangleCircle_carrier]
  by_cases hx1 : x ≤ 1
  · apply Set.mem_iUnion.mpr
    refine ⟨(0 : ZMod 3), ?_⟩
    change _ ∈ segment ℝ _ _
    rw [segment_eq_image_lineMap]
    refine ⟨x, ⟨hx.1, hx1⟩, ?_⟩
    change
      AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex 0)
          (Moise.standardTriangleVertex 1) x =
        boundaryParam x
    rw [boundaryParam, if_pos hx1]
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hx2 : x ≤ 2
    · apply Set.mem_iUnion.mpr
      refine ⟨(1 : ZMod 3), ?_⟩
      change _ ∈ segment ℝ _ _
      rw [segment_eq_image_lineMap]
      refine ⟨x - 1, ⟨by linarith, by linarith⟩, ?_⟩
      change
        AffineMap.lineMap (k := ℝ)
            (Moise.standardTriangleVertex 1)
            (Moise.standardTriangleVertex 2) (x - 1) =
          boundaryParam x
      rw [boundaryParam, if_neg hx1, if_pos hx2]
    · have hx2' : 2 < x := lt_of_not_ge hx2
      apply Set.mem_iUnion.mpr
      refine ⟨(2 : ZMod 3), ?_⟩
      change _ ∈ segment ℝ _ _
      rw [segment_eq_image_lineMap]
      refine ⟨x - 2, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
      change
        AffineMap.lineMap (k := ℝ)
            (Moise.standardTriangleVertex 2)
            (Moise.standardTriangleVertex 0) (x - 2) =
          boundaryParam x
      rw [boundaryParam, if_neg hx1, if_neg hx2]

/-- The affine boundary traversal, with its frontier-membership proof. -/
noncomputable def boundaryParamIcc (x : Set.Icc (0 : ℝ) (0 + 3)) :
    StandardTriangleBoundary :=
  ⟨boundaryParam x, boundaryParam_mem_frontier (by simpa only [zero_add] using x.2)⟩

theorem continuous_boundaryParamIcc : Continuous boundaryParamIcc := by
  apply Continuous.subtype_mk
  exact continuous_boundaryParam.comp continuous_subtype_val

theorem boundaryParamIcc_zero_eq_three :
    boundaryParamIcc ⟨0, by norm_num⟩ =
      boundaryParamIcc ⟨3, by norm_num⟩ := by
  apply Subtype.ext
  exact boundaryParam_zero.trans boundaryParam_three.symm

private theorem boundaryParam_eq_iff
    (x y : Set.Icc (0 : ℝ) (0 + 3))
    (h : boundaryParam x = boundaryParam y) :
    x = y ∨
      (x = ⟨0, by norm_num⟩ ∧ y = ⟨3, by norm_num⟩) ∨
      (x = ⟨3, by norm_num⟩ ∧ y = ⟨0, by norm_num⟩) := by
  have hx0 : 0 ≤ (x : ℝ) := x.2.1
  have hx3 : (x : ℝ) ≤ 3 := by simpa only [zero_add] using x.2.2
  have hy0 : 0 ≤ (y : ℝ) := y.2.1
  have hy3 : (y : ℝ) ≤ 3 := by simpa only [zero_add] using y.2.2
  have h0 := congrArg (fun p : Moise.Plane => p 0) h
  have h1 := congrArg (fun p : Moise.Plane => p 1) h
  by_cases hx1 : (x : ℝ) ≤ 1
  · by_cases hy1 : (y : ℝ) ≤ 1
    · left
      apply Subtype.ext
      simp only [Fin.isValue, boundaryParam, hx1, ↓reduceIte, Moise.standardTriangleVertex,
        Matrix.cons_val_zero, Matrix.cons_val_one, AffineMap.lineMap_apply_module,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_zero, mul_one, zero_add,
        hy1] at h0
      exact h0
    · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
      by_cases hy2 : (y : ℝ) ≤ 2
      · simp [boundaryParam, hx1, hy1, hy2, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        exfalso
        linarith
      · right
        left
        have hy2' : 2 < (y : ℝ) := lt_of_not_ge hy2
        simp [boundaryParam, hx1, hy1, hy2, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        constructor <;> apply Subtype.ext <;> simp_all ; linarith
  · have hx1' : 1 < (x : ℝ) := lt_of_not_ge hx1
    by_cases hx2 : (x : ℝ) ≤ 2
    · by_cases hy1 : (y : ℝ) ≤ 1
      · simp [boundaryParam, hx1, hx2, hy1, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        exfalso
        linarith
      · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
        by_cases hy2 : (y : ℝ) ≤ 2
        · left
          apply Subtype.ext
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          linarith
        · have hy2' : 2 < (y : ℝ) := lt_of_not_ge hy2
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          exfalso
          linarith
    · have hx2' : 2 < (x : ℝ) := lt_of_not_ge hx2
      by_cases hy1 : (y : ℝ) ≤ 1
      · right
        right
        simp [boundaryParam, hx1, hx2, hy1, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        constructor <;> apply Subtype.ext <;> simp_all ; linarith
      · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
        by_cases hy2 : (y : ℝ) ≤ 2
        · simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          exfalso
          linarith
        · left
          apply Subtype.ext
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          linarith

/-- The quotient of `[0,3]` with its endpoints identified maps around the standard frontier. -/
noncomputable def boundaryQuotMap :
    Quot (AddCircle.EndpointIdent (3 : ℝ) 0) → StandardTriangleBoundary :=
  Quot.lift boundaryParamIcc (by
    rintro _ _ ⟨_⟩
    simpa only [zero_add] using boundaryParamIcc_zero_eq_three)

theorem continuous_boundaryQuotMap : Continuous boundaryQuotMap := by
  exact continuous_quot_lift _ continuous_boundaryParamIcc

theorem injective_boundaryQuotMap : Function.Injective boundaryQuotMap := by
  intro q r
  induction q using Quot.inductionOn with
  | _ x =>
      induction r using Quot.inductionOn with
      | _ y =>
          intro h
          change boundaryParamIcc x = boundaryParamIcc y at h
          have hval : boundaryParam x = boundaryParam y :=
            congrArg Subtype.val h
          rcases boundaryParam_eq_iff x y hval with hxy | hends | hends
          · subst y
            rfl
          · rcases hends with ⟨rfl, rfl⟩
            have hend :
                AddCircle.EndpointIdent (3 : ℝ) 0
                  ⟨0, by norm_num⟩ ⟨0 + 3, by norm_num⟩ :=
              AddCircle.EndpointIdent.mk
            simpa only [zero_add] using Quot.sound hend
          · rcases hends with ⟨rfl, rfl⟩
            have hend :
                AddCircle.EndpointIdent (3 : ℝ) 0
                  ⟨0, by norm_num⟩ ⟨0 + 3, by norm_num⟩ :=
              AddCircle.EndpointIdent.mk
            simpa only [zero_add] using (Quot.sound hend).symm

theorem surjective_boundaryQuotMap : Function.Surjective boundaryQuotMap := by
  intro p
  have hpCarrier : p.1 ∈ Moise.standardTriangleCircle.carrier := by
    rw [Moise.standardTriangleCircle_carrier,
      ← Moise.standardTrianglePlaneComplex_support]
    exact p.2
  change p.1 ∈
    ⋃ i : ZMod 3, Moise.standardTriangleCircle.edgeSegment i at hpCarrier
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  fin_cases i
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 0) (Moise.standardTriangleVertex 1) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨t, ht.1, by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam t = p.1
    rw [boundaryParam, if_pos ht.2]
    exact htp
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 1) (Moise.standardTriangleVertex 2) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨1 + t, by linarith [ht.1], by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam (1 + t) = p.1
    by_cases ht0 : t = 0
    · subst t
      simpa [Moise.standardTriangleVertex] using htp
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [boundaryParam, if_neg (by linarith), if_pos (by linarith [ht.2])]
      convert htp using 1; ring
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 2) (Moise.standardTriangleVertex 0) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨2 + t, by linarith [ht.1], by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam (2 + t) = p.1
    by_cases ht0 : t = 0
    · subst t
      simpa [Moise.standardTriangleVertex] using htp
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [boundaryParam, if_neg (by linarith), if_neg (by linarith)]
      convert htp using 1; ring

/-- The additive circle of circumference three is the standard triangular frontier. -/
noncomputable def addCircleBoundaryHomeomorph :
    AddCircle (3 : ℝ) ≃ₜ StandardTriangleBoundary :=
  let e : AddCircle (3 : ℝ) ≃ StandardTriangleBoundary :=
    (AddCircle.equivIccQuot 3 0).trans
      (Equiv.ofBijective boundaryQuotMap
        ⟨injective_boundaryQuotMap, surjective_boundaryQuotMap⟩)
  Continuous.homeoOfEquivCompactToT2 (f := e) (by
    exact continuous_boundaryQuotMap.comp
      (AddCircle.homeoIccQuot 3 0).continuous)

/-- The complex unit circle is the standard triangular frontier. -/
noncomputable def circleBoundaryHomeomorph :
    Circle ≃ₜ StandardTriangleBoundary :=
  (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm.trans
    addCircleBoundaryHomeomorph

private theorem addCircleBoundaryHomeomorph_coe_Icc
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    addCircleBoundaryHomeomorph (x : AddCircle (3 : ℝ)) =
      boundaryParamIcc
        ⟨x, by simpa only [zero_add] using hx⟩ := by
  by_cases hx3 : x = 3
  · subst x
    rw [show (↑(3 : ℝ) : AddCircle (3 : ℝ)) = 0 by
      exact AddCircle.coe_period (3 : ℝ)]
    have hzero : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by norm_num
    have hzero' : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 3) := by
      simpa only [zero_add] using hzero
    change
      boundaryQuotMap
          (AddCircle.equivIccQuot 3 0 (0 : AddCircle (3 : ℝ))) =
        boundaryParamIcc ⟨3, by norm_num⟩
    have he :=
      (AddCircle.equivIco (3 : ℝ) 0).apply_symm_apply ⟨0, hzero'⟩
    change AddCircle.equivIco (3 : ℝ) 0 (0 : AddCircle (3 : ℝ)) =
      ⟨0, hzero'⟩ at he
    rw [show AddCircle.equivIccQuot 3 0 (0 : AddCircle (3 : ℝ)) =
        Quot.mk _ ⟨0, by norm_num⟩ by
      change Quot.mk _ (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco 3 0 (0 : AddCircle (3 : ℝ)))) = _
      rw [he]]
    exact boundaryParamIcc_zero_eq_three
  · have hxIco : x ∈ Set.Ico (0 : ℝ) 3 :=
      ⟨hx.1, hx.2.lt_of_ne hx3⟩
    have hxIco' : x ∈ Set.Ico (0 : ℝ) (0 + 3) := by
      simpa only [zero_add] using hxIco
    change
      boundaryQuotMap
          (AddCircle.equivIccQuot 3 0 (x : AddCircle (3 : ℝ))) =
        boundaryParamIcc ⟨x, by simpa only [zero_add] using hx⟩
    have he :=
      (AddCircle.equivIco (3 : ℝ) 0).apply_symm_apply ⟨x, hxIco'⟩
    change AddCircle.equivIco (3 : ℝ) 0 (x : AddCircle (3 : ℝ)) =
      ⟨x, hxIco'⟩ at he
    rw [show AddCircle.equivIccQuot 3 0 (x : AddCircle (3 : ℝ)) =
        Quot.mk _ ⟨x, by simpa only [zero_add] using hx⟩ by
      change Quot.mk _ (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco 3 0 (x : AddCircle (3 : ℝ)))) = _
      rw [he]]
    rfl

theorem circleBoundaryHomeomorph_side
    (i : Fin 3) (t : unitInterval) :
    circleBoundaryHomeomorph
        (Circle.exp (PolygonCell.sideAngle i t)) =
      ⟨AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex i)
          (Moise.standardTriangleVertex (finRotate 3 i)) t,
        by
          change
            AffineMap.lineMap (k := ℝ)
                (Moise.standardTriangleVertex i)
                (Moise.standardTriangleVertex (finRotate 3 i)) t ∈
              frontier Moise.standardTrianglePlaneComplex.support
          rw [Moise.standardTrianglePlaneComplex_support,
            ← Moise.standardTriangleCircle_carrier]
          apply Set.mem_iUnion.mpr
          refine ⟨(i : ZMod 3), ?_⟩
          change _ ∈ segment ℝ _ _
          rw [segment_eq_image_lineMap]
          refine ⟨t, t.2, ?_⟩
          congr 2; fin_cases i <;> rfl⟩ := by
  let x : ℝ := i + t
  have hx : x ∈ Set.Icc (0 : ℝ) 3 := by
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
    have hi2 : (i : ℕ) ≤ 2 := Nat.le_of_lt_succ i.isLt
    have hi2' : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hi2
    constructor
    · dsimp [x]
      exact add_nonneg hi0 t.2.1
    · dsimp [x]
      linarith [t.2.2]
  have hcircle :
      AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)
          (x : AddCircle (3 : ℝ)) =
        Circle.exp (PolygonCell.sideAngle i t) := by
    rw [AddCircle.homeomorphCircle_apply]
    change Circle.exp (2 * Real.pi / 3 * x) =
      Circle.exp (PolygonCell.sideAngle i t)
    congr 1
    dsimp [x]
    unfold PolygonCell.sideAngle
    push_cast
    ring
  change
    addCircleBoundaryHomeomorph
        ((AddCircle.homeomorphCircle
          (by norm_num : (3 : ℝ) ≠ 0)).symm
            (Circle.exp (PolygonCell.sideAngle i t))) = _
  rw [← hcircle, Homeomorph.symm_apply_apply,
    addCircleBoundaryHomeomorph_coe_Icc hx]
  apply Subtype.ext
  change boundaryParam x =
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex i)
      (Moise.standardTriangleVertex (finRotate 3 i)) t
  have hicases : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp
  rcases hicases with rfl | rfl | rfl
  · have hxval : x = (t : ℝ) := by simp [x]
    have hrot : finRotate 3 (0 : Fin 3) = 1 := rfl
    rw [hxval, hrot, boundaryParam, if_pos t.2.2]
  · have hxval : x = 1 + (t : ℝ) := by norm_num [x]
    have hrot : finRotate 3 (1 : Fin 3) = 2 := rfl
    rw [hxval, hrot]
    by_cases ht0 : (t : ℝ) = 0
    · have ht : t = 0 := Subtype.ext ht0
      subst t
      norm_num [boundaryParam, AffineMap.lineMap_apply_module]
    · have htpos : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      rw [boundaryParam, if_neg (by linarith),
        if_pos (by linarith [t.2.2])]
      congr 2
      ring
  · have hxval : x = 2 + (t : ℝ) := by norm_num [x]
    have hrot : finRotate 3 (2 : Fin 3) = 0 := rfl
    rw [hxval, hrot]
    by_cases ht0 : (t : ℝ) = 0
    · have ht : t = 0 := Subtype.ext ht0
      subst t
      norm_num [boundaryParam, AffineMap.lineMap_apply_module]
    · have htpos : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      rw [boundaryParam, if_neg (by linarith),
        if_neg (by linarith)]
      congr 2
      ring

/-- An ambient straightening of the standard triangle to the Euclidean closed unit disk. -/
theorem exists_triangleAmbientHomeomorph :
    ∃ h : Moise.Plane ≃ₜ ℂ,
      h '' Moise.standardTrianglePlaneComplex.support = Metric.closedBall 0 1 ∧
      h '' frontier Moise.standardTrianglePlaneComplex.support = Metric.sphere 0 1 := by
  obtain ⟨g, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      Moise.standardTrianglePlaneComplex_isTriangle.convex
      Moise.standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty
      Moise.standardTrianglePlaneComplex.isCompact_support.isBounded
  let h : Moise.Plane ≃ₜ ℂ :=
    g.trans Moise.PolygonalCircle.planeComplexEquiv.toHomeomorph
  have hball :
      Moise.PolygonalCircle.planeComplexEquiv ''
          Metric.closedBall (0 : Moise.Plane) 1 =
        Metric.closedBall (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Metric.mem_closedBall,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hx
    · intro hz
      refine ⟨Moise.PolygonalCircle.planeComplexEquiv.symm z, ?_, by simp⟩
      simpa [Metric.mem_closedBall,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hz
  have hsphere :
      Moise.PolygonalCircle.planeComplexEquiv ''
          Metric.sphere (0 : Moise.Plane) 1 =
        Metric.sphere (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Metric.mem_sphere,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hx
    · intro hz
      refine ⟨Moise.PolygonalCircle.planeComplexEquiv.symm z, ?_, by simp⟩
      simpa [Metric.mem_sphere,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hz
  refine ⟨h, ?_, ?_⟩
  · rw [show h '' Moise.standardTrianglePlaneComplex.support =
        Moise.PolygonalCircle.planeComplexEquiv ''
          (g '' Moise.standardTrianglePlaneComplex.support) by
      rw [Set.image_image]
      rfl]
    have hsupport :
        g '' Moise.standardTrianglePlaneComplex.support =
          Metric.closedBall (0 : Moise.Plane) 1 := by
      simpa only [
        Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.closure_eq]
        using hclosure
    rw [hsupport, hball]
  · rw [show h '' frontier Moise.standardTrianglePlaneComplex.support =
        Moise.PolygonalCircle.planeComplexEquiv ''
          (g '' frontier Moise.standardTrianglePlaneComplex.support) by
      rw [Set.image_image]
      rfl]
    rw [hfrontier, hsphere]

/-- The `triangleAmbientHomeomorph` declaration. -/
noncomputable def triangleAmbientHomeomorph : Moise.Plane ≃ₜ ℂ :=
  Classical.choose exists_triangleAmbientHomeomorph

theorem triangleAmbientHomeomorph_image_triangle :
    triangleAmbientHomeomorph '' Moise.standardTrianglePlaneComplex.support =
      Metric.closedBall 0 1 :=
  (Classical.choose_spec exists_triangleAmbientHomeomorph).1

theorem triangleAmbientHomeomorph_image_boundary :
    triangleAmbientHomeomorph ''
        frontier Moise.standardTrianglePlaneComplex.support =
      Metric.sphere 0 1 :=
  (Classical.choose_spec exists_triangleAmbientHomeomorph).2

/-- Restrict the ambient straightening to the closed triangle. -/
noncomputable def triangleDiskHomeomorph :
    StandardTriangle ≃ₜ PolygonCell 3 where
  toFun z :=
    ⟨triangleAmbientHomeomorph z.1, by
      rw [← triangleAmbientHomeomorph_image_triangle]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨triangleAmbientHomeomorph.symm z.val, by
      have hz :
          triangleAmbientHomeomorph
              (triangleAmbientHomeomorph.symm z.val) ∈
            triangleAmbientHomeomorph ''
              Moise.standardTrianglePlaneComplex.support := by
        rw [triangleAmbientHomeomorph_image_triangle]
        simpa using z.property
      rcases hz with ⟨w, hw, heq⟩
      exact triangleAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact triangleAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact triangleAmbientHomeomorph.apply_symm_apply z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.symm.continuous.comp PolygonCell.continuous_val

/-- The ambient straightening restricted to the standard triangular frontier. -/
noncomputable def boundaryCircleHomeomorph :
    StandardTriangleBoundary ≃ₜ Circle where
  toFun z :=
    ⟨triangleAmbientHomeomorph z.1, by
      change triangleAmbientHomeomorph z.1 ∈ Metric.sphere 0 1
      rw [← triangleAmbientHomeomorph_image_boundary]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨triangleAmbientHomeomorph.symm z, by
      have hz :
          triangleAmbientHomeomorph
              (triangleAmbientHomeomorph.symm z) ∈
            triangleAmbientHomeomorph ''
              frontier Moise.standardTrianglePlaneComplex.support := by
        rw [triangleAmbientHomeomorph_image_boundary]
        rw [triangleAmbientHomeomorph.apply_symm_apply]
        rw [Metric.mem_sphere, dist_zero_right]
        exact Circle.norm_coe z
      rcases hz with ⟨w, hw, heq⟩
      exact triangleAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact triangleAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply Circle.ext
    exact triangleAmbientHomeomorph.apply_symm_apply z
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.symm.continuous.comp continuous_subtype_val

/-- Include the standard frontier in the closed standard triangle. -/
def boundaryInclusion : C(StandardTriangleBoundary, StandardTriangle) where
  toFun z :=
    ⟨z.1, Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset z.2⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

@[simp]
theorem triangleDiskHomeomorph_boundary (z : StandardTriangleBoundary) :
    triangleDiskHomeomorph (boundaryInclusion z) =
      PolygonCell.ofCircle 3 (boundaryCircleHomeomorph z) := by
  apply PolygonCell.ext
  rfl

/-- The calibrated homeomorphism from the three-sided cell to the standard triangle. -/
noncomputable def cellHomeomorph : PolygonCell 3 ≃ₜ StandardTriangle :=
  (PolygonCell.radialHomeomorph
      (circleBoundaryHomeomorph.trans boundaryCircleHomeomorph)).trans
    triangleDiskHomeomorph.symm

@[simp]
theorem cellHomeomorph_ofCircle (z : Circle) :
    cellHomeomorph (PolygonCell.ofCircle 3 z) =
      boundaryInclusion (circleBoundaryHomeomorph z) := by
  apply triangleDiskHomeomorph.injective
  rw [cellHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, PolygonCell.radialHomeomorph_ofCircle,
    triangleDiskHomeomorph_boundary]
  rfl

theorem cellHomeomorph_side (i : Fin 3) (t : unitInterval) :
    cellHomeomorph (PolygonCell.side i t) =
      ⟨AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex i)
          (Moise.standardTriangleVertex (finRotate 3 i)) t,
        by
          have hfrontier :
              AffineMap.lineMap (k := ℝ)
                  (Moise.standardTriangleVertex i)
                  (Moise.standardTriangleVertex (finRotate 3 i)) t ∈
                frontier Moise.standardTrianglePlaneComplex.support := by
            have heq := congrArg Subtype.val
              (circleBoundaryHomeomorph_side i t)
            change
              (circleBoundaryHomeomorph
                  (Circle.exp (PolygonCell.sideAngle i t))).1 =
                AffineMap.lineMap (k := ℝ)
                  (Moise.standardTriangleVertex i)
                  (Moise.standardTriangleVertex (finRotate 3 i)) t at heq
            rw [← heq]
            exact (circleBoundaryHomeomorph
              (Circle.exp (PolygonCell.sideAngle i t))).2
          exact
            Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
              hfrontier⟩ := by
  rw [show PolygonCell.side i t =
      PolygonCell.ofCircle 3
        (Circle.exp (PolygonCell.sideAngle i t)) by rfl,
    cellHomeomorph_ofCircle]
  apply Subtype.ext
  change
    (circleBoundaryHomeomorph
        (Circle.exp (PolygonCell.sideAngle i t))).1 =
      AffineMap.lineMap (k := ℝ)
        (Moise.standardTriangleVertex i)
        (Moise.standardTriangleVertex (finRotate 3 i)) t
  exact congrArg Subtype.val (circleBoundaryHomeomorph_side i t)

end TriangleCell

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification09_block_05
/- END ClassificationOfSurfaces.TriangleCell -/
