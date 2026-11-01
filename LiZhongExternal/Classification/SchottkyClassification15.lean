/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification15: pinned classification sources; see BUNDLE_MAP.json. -/
import LiZhongExternal.Classification.SchottkyClassification14
import LiZhongExternal.Classification.SchottkyClassification08
import LiZhongExternal.Classification.SchottkyClassification12
import LiZhongExternal.Classification.SchottkyClassification04

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicFaceExtension | bc205db54aa746b45263c22376be250d39d65f12b38edd05650b6835080cf558 -/
noncomputable section

section schottkyclassification15_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Relative polygonal boundary maps for intrinsic faces

The simultaneous intrinsic graph replacement is defined once on the global one-skeleton.  This
file restricts that one map to each closed face, in standard triangle coordinates.  Consequently
two neighboring face extensions will have literally the same boundary values on their shared
edge.  The construction below is topological; the finite conforming subdivision which certifies
that it is PL is kept as a separate obligation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The closed standard triangle used as the source model for every intrinsic face. -/
abbrev standardFaceRegion : Set Plane := standardTrianglePlaneComplex.support

/-- Its polygonal frontier, as a subtype. -/
abbrev StandardFaceBoundary :=
  {p : Plane // p ∈ frontier standardFaceRegion}

theorem standardFaceBoundary_mem_region (p : StandardFaceBoundary) :
    p.1 ∈ standardFaceRegion :=
  standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset p.2

/-- A point on a standard cyclic side lifts to the corresponding intrinsic edge. -/
theorem facePlaneHomeomorph_symm_mem_edge (t : K.Face) (i : ZMod 3)
    {p : Plane} (hp : p ∈ standardTriangleCircle.edgeSegment i) :
    ((K.facePlaneHomeomorph t).symm
      ⟨p, standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
        (by
          have hp' : p ∈ standardTriangleCircle.carrier :=
            Set.mem_iUnion.mpr ⟨i, hp⟩
          rw [standardTriangleCircle_carrier] at hp'
          simpa only [standardTrianglePlaneComplex_support] using hp')⟩).1 ∈
      K.faceCarrier (K.faceEdge t i).1 := by
  rw [← K.facePlaneHomeomorph_image_edge t i] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hpFrontier : p ∈ frontier standardTrianglePlaneComplex.support := by
    have hp' : p ∈ standardTriangleCircle.carrier :=
      Set.mem_iUnion.mpr ⟨i, by simpa only [hxp] using
        (show (K.facePlaneHomeomorph t x).1 ∈
          standardTriangleCircle.edgeSegment i from
          (Set.ext_iff.mp (K.facePlaneHomeomorph_image_edge t i)
            (K.facePlaneHomeomorph t x).1).mp ⟨x, hx, rfl⟩)⟩
    rw [standardTriangleCircle_carrier] at hp'
    simpa only [standardTrianglePlaneComplex_support] using hp'
  have heq : (K.facePlaneHomeomorph t).symm
      ⟨p, standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
        hpFrontier⟩ = x := by
    apply (K.facePlaneHomeomorph t).injective
    simp only [Homeomorph.apply_symm_apply]
    exact Subtype.ext hxp.symm
  rw [heq]
  exact hx

/-- The inverse standard-face chart sends the standard frontier into the global intrinsic
one-skeleton. -/
theorem facePlaneHomeomorph_symm_mem_oneSkeleton (t : K.Face)
    (p : StandardFaceBoundary) :
    ((K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩).1 ∈ K.oneSkeleton := by
  have hpCarrier : p.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using p.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  exact ⟨K.faceEdge t i, K.facePlaneHomeomorph_symm_mem_edge t i hi⟩

/-- The canonical lift of the standard triangular frontier to the global intrinsic
one-skeleton. -/
noncomputable def faceBoundaryLift (t : K.Face) :
    StandardFaceBoundary → K.oneSkeleton :=
  fun p => ⟨((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).1,
      K.facePlaneHomeomorph_symm_mem_oneSkeleton t p⟩

theorem continuous_faceBoundaryLift (t : K.Face) :
    Continuous (K.faceBoundaryLift t) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    ((K.facePlaneHomeomorph t).symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

theorem injective_faceBoundaryLift (t : K.Face) :
    Function.Injective (K.faceBoundaryLift t) := by
  intro p q hpq
  have hval : ((K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩).1 =
      ((K.facePlaneHomeomorph t).symm
        ⟨q.1, standardFaceBoundary_mem_region q⟩).1 :=
    congrArg (fun z : K.oneSkeleton => (z.1 : K.realization)) hpq
  have hclosed : (K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩ =
      (K.facePlaneHomeomorph t).symm
        ⟨q.1, standardFaceBoundary_mem_region q⟩ := by
    exact Subtype.ext hval
  have hsource := (K.facePlaneHomeomorph t).symm.injective hclosed
  exact Subtype.ext
    (congrArg (fun z : standardTrianglePlaneComplex.support => (z.1 : Plane)) hsource)

/-- The global graph replacement, expressed on the standard frontier of one intrinsic face.
Outside that frontier the value is deliberately irrelevant. -/
noncomputable def faceBoundaryMap (t : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ frontier standardFaceRegion then
    K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t ⟨p, hp⟩).1
  else 0

@[simp] theorem faceBoundaryMap_apply (t : K.Face) (p : StandardFaceBoundary) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1 =
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t p).1 := by
  simp [faceBoundaryMap, p.2]

/-- The canonical face boundary map is continuous on the standard frontier. -/
theorem continuousOn_faceBoundaryMap (t : K.Face) :
    ContinuousOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      (frontier standardFaceRegion) := by
  rw [continuousOn_iff_continuous_restrict]
  have hg : Continuous (fun x : K.oneSkeleton =>
      K.graphReplacementMap hcont hinj D C x.1) :=
    continuousOn_iff_continuous_restrict.mp
      (K.continuousOn_graphReplacementMap_oneSkeleton hcont hinj D C)
  convert hg.comp (K.continuous_faceBoundaryLift t) using 1
  funext p
  exact K.faceBoundaryMap_apply t p

/-- The canonical face boundary map is injective on the standard frontier. -/
theorem faceBoundaryMap_injectiveOn (t : K.Face) :
    Set.InjOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      (frontier standardFaceRegion) := by
  intro p hp q hq hpq
  let p' : StandardFaceBoundary := ⟨p, hp⟩
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have hpq' :
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t p').1 =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q').1 := by
    rw [← K.faceBoundaryMap_apply t p', ← K.faceBoundaryMap_apply t q']
    exact hpq
  have hgraph : K.faceBoundaryLift t p' = K.faceBoundaryLift t q' := by
    apply Subtype.ext
    apply K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
      (K.faceBoundaryLift t p').2 (K.faceBoundaryLift t q').2
    exact hpq'
  exact congrArg Subtype.val (K.injective_faceBoundaryLift t hgraph)

private theorem faceEdgeCarrier_subset_faceCarrier (t : K.Face) (i : ZMod 3) :
    K.faceCarrier (K.faceEdge t i).1 ⊆ K.faceCarrier t.1 := by
  intro x hx v hvt
  apply hx v
  intro hve
  rw [K.faceEdge_val] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl
  · exact hvt (K.faceVertex_mem t i)
  · exact hvt (K.faceVertex_mem t (i + 1))

/-- The canonical boundary parameterization has exactly the polygon assembled from the three
global replacement edges as its image. -/
theorem faceBoundaryMap_image_frontier (t : K.Face) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ''
        frontier standardFaceRegion =
      K.faceReplacementCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have hpCarrier : p ∈ standardTriangleCircle.carrier := by
      rw [standardTriangleCircle_carrier]
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← K.graphReplacementMap_image_faceCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      (e := K.faceEdge t i)]
    refine ⟨(K.faceBoundaryLift t ⟨p, hp⟩).1, ?_, ?_⟩
    · exact K.facePlaneHomeomorph_symm_mem_edge t i hi
    · exact (K.faceBoundaryMap_apply t ⟨p, hp⟩).symm
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [← K.graphReplacementMap_image_faceCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      (e := K.faceEdge t i)] at hi
    obtain ⟨x, hx, hxy⟩ := hi
    let x' : K.ClosedFace t := ⟨x, K.faceEdgeCarrier_subset_faceCarrier t i hx⟩
    let p : Plane := (K.facePlaneHomeomorph t x').1
    have hpSide : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← K.facePlaneHomeomorph_image_edge t i]
      exact ⟨x', hx, rfl⟩
    have hpFrontier : p ∈ frontier standardFaceRegion := by
      have hp' : p ∈ standardTriangleCircle.carrier :=
        Set.mem_iUnion.mpr ⟨i, hpSide⟩
      rw [standardTriangleCircle_carrier] at hp'
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp'
    refine ⟨p, hpFrontier, ?_⟩
    rw [K.faceBoundaryMap_apply t ⟨p, hpFrontier⟩]
    have hlift : (K.faceBoundaryLift t ⟨p, hpFrontier⟩).1 = x := by
      change ((K.facePlaneHomeomorph t).symm
        ⟨p, standardFaceBoundary_mem_region ⟨p, hpFrontier⟩⟩).1 = x
      have heq : (K.facePlaneHomeomorph t).symm
          ⟨p, standardFaceBoundary_mem_region ⟨p, hpFrontier⟩⟩ = x' := by
        apply (K.facePlaneHomeomorph t).injective
        simp only [Homeomorph.apply_symm_apply]
        rfl
      exact congrArg Subtype.val heq
    rw [hlift, hxy]

/-- The same exact image statement, expressed using the extracted polygonal circle. -/
theorem faceBoundaryMap_image_polygon (t : K.Face) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ''
        frontier standardFaceRegion =
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  rw [K.faceBoundaryMap_image_frontier t, K.facePolygonalCircle_carrier t]

/-! ## A finite source subdivision carrying all boundary breakpoints -/

theorem faceStandardEdge_card (i : ZMod 3) : (faceStandardEdge i).card = 2 := by
  rw [faceStandardEdge]
  apply Finset.card_pair
  exact (ZMod.finEquiv 3).symm.injective.ne
    ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)

/-- A cyclic side of the standard triangle, regarded as an edge of its one-skeleton. -/
noncomputable def standardFaceEdgeFace (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.EdgeFace :=
  ⟨faceStandardEdge i, Finset.mem_filter.mpr ⟨
    standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨faceStandardEdge_mem_simplexes i, (faceStandardEdge_card i).le⟩,
    faceStandardEdge_card i⟩⟩

/-- The finite graph enumeration index of a cyclic standard side. -/
noncomputable def standardFaceEdgeIndex (i : ZMod 3) :
    Fin (Fintype.card standardTrianglePlaneComplex.oneSkeleton.EdgeFace) :=
  Classical.choose
    (standardTrianglePlaneComplex.oneSkeleton.exists_edgeAt (standardFaceEdgeFace i))

theorem standardFaceEdgeAt_eq (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.edgeAt (standardFaceEdgeIndex i) =
      standardFaceEdgeFace i :=
  Classical.choose_spec
    (standardTrianglePlaneComplex.oneSkeleton.exists_edgeAt (standardFaceEdgeFace i))

/-- All breakpoints needed on all three sides of one intrinsic face. -/
abbrev FaceBreakpoint (t : K.Face) :=
  Σ i : ZMod 3,
    EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i))

/-- A replacement-edge breakpoint placed on the corresponding oriented standard side. -/
noncomputable def faceBreakpointPoint (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) : Plane :=
  K.faceEdgeSourcePoint t b.1
    (edgeBreakpointParameter
      (K.replacementArc hcont hinj D C (K.faceEdge t b.1)) b.2)

theorem faceBreakpointPoint_mem_standardEdge (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t b ∈
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge b.1) := by
  apply K.faceEdgeSourcePoint_mem_standardEdge
  exact edgeBreakpointParameter_mem
    (K.replacementArc hcont hinj D C (K.faceEdge t b.1)) b.2

theorem faceBreakpointPoint_mem_standardOneSkeleton
    (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t b ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  apply standardTrianglePlaneComplex.oneSkeleton.cellCarrier_subset_support
    (standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨faceStandardEdge_mem_simplexes b.1, (faceStandardEdge_card b.1).le⟩)
  simpa only [PlaneComplex.oneSkeleton_cellCarrier] using
    K.faceBreakpointPoint_mem_standardEdge t b

/-- The common finite standard-boundary subdivision carrying the spoke joins and every vertex
of every middle polygonal model. -/
noncomputable def faceBoundarySubdivision (t : K.Face) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

theorem faceBoundarySubdivision_subdivides (t : K.Face) :
    (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Subdivides
      standardTrianglePlaneComplex.oneSkeleton :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
    (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph

theorem faceBoundarySubdivision_support (t : K.Face) :
    (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).support =
      frontier standardFaceRegion := by
  rw [faceBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    standardTriangle_oneSkeleton_support, standardTriangleCircle_carrier]
  simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

/-- A standard `Fin 3` corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def standardBoundaryVertex (j : Fin 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact j

/-- Every two-vertex simplex of the standard boundary graph is one of its three cyclic sides. -/
theorem exists_faceStandardEdge_of_standardBoundaryEdge
    {s : Finset standardTrianglePlaneComplex.oneSkeleton.Vertex}
    (hcard : s.card = 2) :
    ∃ i : ZMod 3, s = (standardFaceEdgeFace i).1 := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hcard
  have hsurj (x : standardTrianglePlaneComplex.oneSkeleton.Vertex) :
      ∃ j : Fin 3, x = standardBoundaryVertex j := by
    change ∃ j : Fin 3, x = j
    exact ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hsurj v
  obtain ⟨b, hb⟩ := hsurj w
  subst v
  subst w
  fin_cases a <;> fin_cases b
  · exact (hvw rfl).elim
  · refine ⟨0, ?_⟩
    change ({0, 1} : Finset (Fin 3)) = faceStandardEdge 0
    decide
  · refine ⟨2, ?_⟩
    change ({0, 2} : Finset (Fin 3)) = faceStandardEdge 2
    decide
  · refine ⟨0, ?_⟩
    change ({1, 0} : Finset (Fin 3)) = faceStandardEdge 0
    decide
  · exact (hvw rfl).elim
  · refine ⟨1, ?_⟩
    change ({1, 2} : Finset (Fin 3)) = faceStandardEdge 1
    decide
  · refine ⟨2, ?_⟩
    change ({2, 0} : Finset (Fin 3)) = faceStandardEdge 2
    decide
  · refine ⟨1, ?_⟩
    change ({2, 1} : Finset (Fin 3)) = faceStandardEdge 1
    decide
  · exact (hvw rfl).elim

theorem standardFaceEdgeFace_cellCarrier (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.cellCarrier (standardFaceEdgeFace i).1 =
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rfl

/-- The first oriented standard corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def faceEdgeFirstBoundaryVertex (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeFirstIndex t i

/-- The second oriented standard corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def faceEdgeSecondBoundaryVertex (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeSecondIndex t i

@[simp] theorem faceEdgeFirstBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position (K.faceEdgeFirstBoundaryVertex t i) =
      standardTriangleVertex (K.faceEdgeFirstIndex t i) := rfl

@[simp] theorem faceEdgeSecondBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position (K.faceEdgeSecondBoundaryVertex t i) =
      standardTriangleVertex (K.faceEdgeSecondIndex t i) := rfl

theorem standardFaceEdgeFace_val_eq_boundaryEndpoints (t : K.Face) (i : ZMod 3) :
    (standardFaceEdgeFace i).1 =
      {K.faceEdgeFirstBoundaryVertex t i, K.faceEdgeSecondBoundaryVertex t i} := by
  change faceStandardEdge i =
    {K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i}
  exact K.faceStandardEdge_eq_endpointIndices t i

/-- The arbitrary graph enumeration of a standard side either follows or reverses the global
intrinsic edge orientation. -/
theorem standardFaceEdge_endpoint_order (t : K.Face) (i : ZMod 3) :
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex t i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex t i) ∨
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex t i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex t i) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let j := standardFaceEdgeIndex i
  have hfirst : S.edgeFirst j ∈ (S.edgeAt j).1 := by
    rw [S.edgeAt_eq]
    simp
  have hsecond : S.edgeSecond j ∈ (S.edgeAt j).1 := by
    rw [S.edgeAt_eq]
    simp
  have hedge : (S.edgeAt j).1 = (standardFaceEdgeFace i).1 :=
    congrArg Subtype.val (standardFaceEdgeAt_eq i)
  rw [hedge, K.standardFaceEdgeFace_val_eq_boundaryEndpoints t i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (S.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (S.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim

/-- The intrinsic edge parameter, pulled back as an ambient affine coordinate on the standard
face plane. -/
noncomputable def faceEdgeParameterAffine (t : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] ℝ :=
  (K.edgeCoordinateAffine (K.faceEdge t i)).comp (K.facePlaneInverseAffine t)

@[simp] theorem faceEdgeParameterAffine_apply (t : K.Face) (i : ZMod 3) (p : Plane) :
    K.faceEdgeParameterAffine t i p =
      K.facePlaneInverseAffine t p (K.edgeSecond (K.faceEdge t i)) := rfl

theorem faceEdgeParameterAffine_sourcePoint
    (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.faceEdgeParameterAffine t i (K.faceEdgeSourcePoint t i r) = r := by
  exact K.facePlaneInverseAffine_faceEdgeSourcePoint_apply_second t i r

theorem standardFaceEdgeParameter_sourcePoint_of_forward (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint t i r) = r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position t i,
    ← K.faceEdgeSecondBoundaryVertex_position t i,
    ← horient.1, ← horient.2,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_sourcePoint_of_reverse (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint t i r) = 1 - r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position t i,
    ← K.faceEdgeSecondBoundaryVertex_position t i,
    ← horient.2, ← horient.1, ← AffineMap.lineMap_apply_one_sub,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
    (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p =
      K.faceEdgeParameterAffine t i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc t i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_forward t i horient,
    K.faceEdgeParameterAffine_sourcePoint]

theorem standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
    (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p =
      1 - K.faceEdgeParameterAffine t i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc t i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_reverse t i horient,
    K.faceEdgeParameterAffine_sourcePoint]

/-- Every face of the marked boundary subdivision lies on one side of every marked parameter,
in the standard graph enumeration coordinate. -/
theorem faceBoundarySubdivision_parameter_side_standard
    (t : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i)))
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            ⟨i, b⟩)) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            ⟨i, b⟩) ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let point := K.faceBreakpointPoint
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let j := standardFaceEdgeIndex i
  have hbCarrier : point ⟨i, b⟩ ∈ S.cellCarrier (S.edgeAt j).1 := by
    rw [show (S.edgeAt j).1 = faceStandardEdge i from
      congrArg Subtype.val (standardFaceEdgeAt_eq i)]
    rw [standardTrianglePlaneComplex.oneSkeleton_cellCarrier]
    exact K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩
  have hpoint : point ⟨i, b⟩ =
      AffineMap.lineMap (S.position (S.edgeFirst j)) (S.position (S.edgeSecond j))
        (S.edgeParameter j (point ⟨i, b⟩)) :=
    (S.lineMap_edgeParameter_eq j hbCarrier).symm
  have huArrangement :=
    ((S.markedEdgeArrangement point).mem_subordinateTo_simplexes_iff S).mp hu |>.1
  have hside := S.markedFaceCarrier_parameter_side point
    (⟨i, b⟩ : FaceBreakpoint
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    j (S.edgeParameter j (point ⟨i, b⟩)) hpoint huArrangement
  exact hside

/-- On a subdivision face contained in one standard side, the same side test is exactly the
intrinsic edge parameter test, independent of orientation. -/
theorem faceBoundarySubdivision_parameter_side
    (t : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i)))
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ edgeBreakpointParameter
        (K.replacementArc hcont hinj D C (K.faceEdge t i)) b) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      edgeBreakpointParameter (K.replacementArc hcont hinj D C (K.faceEdge t i)) b ≤
        K.faceEdgeParameterAffine t i p) := by
  have hside := K.faceBoundarySubdivision_parameter_side_standard t i b hu
  have hmark : K.faceBreakpointPoint
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ⟨i, b⟩ =
      K.faceEdgeSourcePoint t i
        (edgeBreakpointParameter (K.replacementArc hcont hinj D C (K.faceEdge t i)) b) := rfl
  rcases K.standardFaceEdge_endpoint_order t i with hforward | hreverse
  · have hmarkEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
      t i hforward (K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        t i hforward (hui hp)
      have hpSide := hle p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        t i hforward (hui hp)
      have hpSide := hge p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
  · have hmarkEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
      t i hreverse (K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        t i hreverse (hui hp)
      have := hle p hp
      rw [hpEq, hmark, hmarkEq] at this
      linarith
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        t i hreverse (hui hp)
      have := hge p hp
      rw [hpEq, hmark, hmarkEq] at this
      linarith

/-- The two spoke joins split every subdivision face on a selected standard side into the
left, middle, or right parameter range. -/
theorem faceBoundarySubdivision_piece
    (t : K.Face) (i : ZMod 3)
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) ∨
    ((∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p) ∧
      (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ))) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) := by
  have hhalf := K.faceBoundarySubdivision_parameter_side t i none hu hui
  have hthree := K.faceBoundarySubdivision_parameter_side t i (some none) hu hui
  change (∀ p ∈ _, K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) ∨
      (∀ p ∈ _, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p) at hhalf
  change (∀ p ∈ _, K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ)) ∨
      (∀ p ∈ _, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) at hthree
  rcases hhalf with hleHalf | hgeHalf
  · exact Or.inl hleHalf
  · rcases hthree with hleThree | hgeThree
    · exact Or.inr (Or.inl ⟨hgeHalf, hleThree⟩)
    · exact Or.inr (Or.inr hgeThree)

/-- Pull an intrinsic affine certificate back through the affine inverse face chart. -/
theorem faceBoundaryMap_affineOn_of_lift
    (t : K.Face) {E : Set Plane} {X : Set K.realization}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hlift : ∀ (p : Plane) (hp : p ∈ E),
      (K.faceBoundaryLift t ⟨p, hfrontier hp⟩).1 ∈ X)
    (haffine : K.IsAffineOnSet
      (K.graphReplacementMap hcont hinj D C) X) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  obtain ⟨a, ha⟩ := haffine
  refine ⟨a.comp (K.facePlaneInverseAffine t), ?_⟩
  intro p hp
  let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
  have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p := by
    exact K.facePlaneHomeomorph_symm_val t
      ⟨p, standardFaceBoundary_mem_region q⟩
  rw [show K.faceBoundaryMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 by
      exact K.faceBoundaryMap_apply t q]
  change K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 =
    a (K.facePlaneInverseAffine t p)
  rw [ha (K.faceBoundaryLift t q).1 (hlift p hp), hcoords]

/-- On a left spoke piece of a standard side, the canonical face boundary map is affine. -/
theorem faceBoundaryMap_affineOn_left
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hle : ∀ p ∈ E, K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let X : Set K.realization :=
    {x | x ∈ K.faceCarrier e.1 ∧ x.1 (K.edgeSecond e) ≤ (1 / 2 : ℝ)}
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
    have hpEdge : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← standard_cellCarrier_faceStandardEdge i]
      exact hside hp
    have hmem := K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p :=
      K.facePlaneHomeomorph_symm_val t ⟨p, standardFaceBoundary_mem_region q⟩
    refine ⟨hmem, ?_⟩
    change (K.faceBoundaryLift t q).1.1 (K.edgeSecond e) ≤ (1 / 2 : ℝ)
    rw [hcoords]
    exact hle p hp
  · apply K.graphReplacementMap_affineOn_left
    · exact fun _ hx => hx.1
    · exact fun _ hx => hx.2

/-- On a right spoke piece of a standard side, the canonical face boundary map is affine. -/
theorem faceBoundaryMap_affineOn_right
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hge : ∀ p ∈ E, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let X : Set K.realization :=
    {x | x ∈ K.faceCarrier e.1 ∧ (3 / 4 : ℝ) ≤ x.1 (K.edgeSecond e)}
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
    have hpEdge : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← standard_cellCarrier_faceStandardEdge i]
      exact hside hp
    have hmem := K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p :=
      K.facePlaneHomeomorph_symm_val t ⟨p, standardFaceBoundary_mem_region q⟩
    refine ⟨hmem, ?_⟩
    change (3 / 4 : ℝ) ≤ (K.faceBoundaryLift t q).1.1 (K.edgeSecond e)
    rw [hcoords]
    exact hge p hp
  · apply K.graphReplacementMap_affineOn_right
    · exact fun _ hx => hx.1
    · exact fun _ hx => hx.2

/-- On a middle piece, affinity follows once its pulled-back source image lies in one face of
the finite polygonal segment model. -/
theorem faceBoundaryMap_affineOn_middle
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hmid0 : ∀ p ∈ E, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p)
    (hmid1 : ∀ p ∈ E, K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ))
    (hsource : ∃ s ∈
        (K.replacementArc hcont hinj D C (K.faceEdge t i)).parameterization.source.simplexes,
      Set.MapsTo (fun p : Plane =>
        edgeMiddleSourceMap (K.replacementArc hcont hinj D C (K.faceEdge t i))
          (K.facePlaneInverseAffine t p)) E
        ((K.replacementArc hcont hinj D C (K.faceEdge t i))
          |>.parameterization.source.cellCarrier s)) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let A := K.replacementArc hcont hinj D C e
  let lift : {p : Plane // p ∈ E} → K.realization := fun p =>
    (K.faceBoundaryLift t ⟨p.1, hfrontier p.2⟩).1
  let X : Set K.realization := Set.range lift
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    exact ⟨⟨p, hp⟩, rfl⟩
  · apply K.graphReplacementMap_affineOn_middle
    · rintro x ⟨p, rfl⟩
      have hpEdge : p.1 ∈ standardTriangleCircle.edgeSegment i := by
        rw [← standard_cellCarrier_faceStandardEdge i]
        exact hside p.2
      exact K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    · rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change (1 / 2 : ℝ) ≤ (lift p).1 (K.edgeSecond e)
      rw [hcoords]
      exact hmid0 p.1 p.2
    · rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change (lift p).1 (K.edgeSecond e) ≤ (3 / 4 : ℝ)
      rw [hcoords]
      exact hmid1 p.1 p.2
    · obtain ⟨s, hs, hmaps⟩ := hsource
      refine ⟨s, hs, ?_⟩
      rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change edgeMiddleSourceMap A (lift p).1 ∈ A.parameterization.source.cellCarrier s
      rw [hcoords]
      exact hmaps p.2

/-- The marked middle-model vertices ensure that the pulled-back image of a two-vertex
subdivision face is contained in one face of the finite segment model. -/
theorem faceBoundarySubdivision_middleSource
    (t : K.Face) (i : ZMod 3)
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hcard : u.card = 2)
    (hmid0 : ∀ p ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        |>.cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p)
    (hmid1 : ∀ p ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ)) :
    ∃ s ∈
        (K.replacementArc hcont hinj D C (K.faceEdge t i)).parameterization.source.simplexes,
      Set.MapsTo (fun p : Plane =>
        edgeMiddleSourceMap (K.replacementArc hcont hinj D C (K.faceEdge t i))
          (K.facePlaneInverseAffine t p))
        ((K.faceBoundarySubdivision
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier u)
        ((K.replacementArc hcont hinj D C (K.faceEdge t i))
          |>.parameterization.source.cellCarrier s) := by
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let A := K.replacementArc hcont hinj D C (K.faceEdge t i)
  let n : ℝ := A.data.resolvedWalk.length
  let z : Plane → ℝ := fun p => n *
    (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine t i p - 2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have hdelta : 0 ≤ A.exitData.right - A.exitData.left :=
    sub_nonneg.mpr A.exitData.left_lt_right.le
  have hmono {p q : Plane}
      (hpq : K.faceEdgeParameterAffine t i p ≤ K.faceEdgeParameterAffine t i q) :
      z p ≤ z q := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i p - 2)) ≤
      n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i q - 2))
    apply mul_le_mul_of_nonneg_left _ hn.le
    have hr : 4 * K.faceEdgeParameterAffine t i p - 2 ≤
        4 * K.faceEdgeParameterAffine t i q - 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr hdelta
    linarith
  have hzBounds {p : Plane} (hp : p ∈ R.cellCarrier u) : z p ∈ Set.Icc 0 n := by
    have ht0 := hmid0 p hp
    have ht1 := hmid1 p hp
    have hr0 : 0 ≤ 4 * K.faceEdgeParameterAffine t i p - 2 := by linarith
    have hr1 : 4 * K.faceEdgeParameterAffine t i p - 2 ≤ 1 := by linarith
    constructor
    · exact mul_nonneg hn.le
        (add_nonneg A.exitData.left_nonneg (mul_nonneg hdelta hr0))
    · calc
        z p ≤ n * 1 := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          have hmul := mul_le_mul_of_nonneg_left hr1 hdelta
          linarith [A.exitData.right_le_one]
        _ = n := mul_one n
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
  have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
  have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
  have zLower {r : Plane} (hr : r ∈ R.cellCarrier ({p, q} : Finset R.Vertex)) :
      n * A.exitData.left ≤ z r := by
    change n * A.exitData.left ≤ n *
      (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i r - 2))
    have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i r - 2) :=
      mul_nonneg hdelta (by linarith [hmid0 r hr])
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
  have zUpper {r : Plane} (hr : r ∈ R.cellCarrier ({p, q} : Finset R.Vertex)) :
      z r ≤ n * A.exitData.right := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine t i r - 2)) ≤ n * A.exitData.right
    have hmul := mul_le_mul_of_nonneg_left
      (show 4 * K.faceEdgeParameterAffine t i r - 2 ≤ 1 by linarith [hmid1 r hr]) hdelta
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
  let a := min (z (R.position p)) (z (R.position q))
  let b := max (z (R.position p)) (z (R.position q))
  have hab : a ≤ b := min_le_max
  have ha : 0 ≤ a := le_min (hzBounds hp).1 (hzBounds hq).1
  have hb : b ≤ n := max_le (hzBounds hp).2 (hzBounds hq).2
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
      exact hcn.le.trans (le_min (zLower hp) (zLower hq))
    · have hv0' : A.exitData.left ≤ c / n := le_of_not_gt hv0
      by_cases hv1 : c / n ≤ A.exitData.right
      · have hbreak := K.faceBoundarySubdivision_parameter_side t i
          (some (some v)) hu hui
        have hvalue := edgeMiddleSourceScalar_breakpoint A v hv0' hv1
        have hparamBreak : K.faceEdgeParameterAffine t i
            (K.faceBreakpointPoint
              (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                ⟨i, some (some v)⟩) =
              edgeBreakpointParameter A (some (some v)) := by
          change K.faceEdgeParameterAffine t i
            (K.faceEdgeSourcePoint t i (edgeBreakpointParameter A (some (some v)))) = _
          rw [K.faceEdgeParameterAffine_sourcePoint]
        have hbreakValue : z (K.faceBreakpointPoint
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              ⟨i, some (some v)⟩) = c := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine t i
              (K.faceBreakpointPoint
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                  ⟨i, some (some v)⟩) - 2)) = c
          rw [hparamBreak]
          simpa only [n, c, edgeBreakpointParameter] using hvalue
        rcases hbreak with hle | hge
        · right
          apply max_le
          · calc
              z (R.position p) ≤ z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [hparamBreak]
                      exact hle _ hp)
              _ = c := hbreakValue
          · calc
              z (R.position q) ≤ z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [hparamBreak]
                      exact hle _ hq)
              _ = c := hbreakValue
        · left
          apply le_min
          · calc
              c = z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position p) := hmono (by
                rw [hparamBreak]
                exact hge _ hp)
          · calc
              c = z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position q) := hmono (by
                rw [hparamBreak]
                exact hge _ hq)
      · right
        have hcn : n * A.exitData.right < c := by
          have hc : A.exitData.right < c / n := lt_of_not_ge hv1
          rw [lt_div_iff₀ hn] at hc
          simpa [mul_comm] using hc
        exact (max_le (zUpper hp) (zUpper hq)).trans hcn.le
  obtain ⟨s, hs, hssegment⟩ := PlaneComplex.exists_face_containing_axis_segment_of_no_vertex
    A.parameterization.source hn.le hab ha hb A.parameterization.source_support
      A.parameterization.source_card_le_two havoid
  let sourceAffine : Plane →ᵃ[ℝ] Plane :=
    (edgeMiddleSourceMap A).comp (K.facePlaneInverseAffine t)
  have hsourceApply (x : Plane) : sourceAffine x = planePoint (z x) 0 := by
    simp only [sourceAffine, AffineMap.comp_apply, edgeMiddleSourceMap_apply]
    rfl
  have hsourceImage : sourceAffine '' R.cellCarrier ({p, q} : Finset R.Vertex) =
      segment ℝ (planePoint a 0) (planePoint b 0) := by
    rw [PlaneComplex.cellCarrier]
    have himage : R.position '' (({p, q} : Finset R.Vertex) : Set R.Vertex) =
        {R.position p, R.position q} := by
      ext x
      simp [eq_comm]
    rw [himage, convexHull_pair, image_segment]
    rw [hsourceApply, hsourceApply]
    rcases le_total (z (R.position p)) (z (R.position q)) with hpzq | hqzp
    · simp [a, b, min_eq_left hpzq, max_eq_right hpzq]
    · rw [segment_symm]
      simp [a, b, min_eq_right hqzp, max_eq_left hqzp]
  refine ⟨s, hs, ?_⟩
  intro x hx
  apply hssegment
  rw [← hsourceImage]
  exact ⟨x, hx, rfl⟩

/-- The canonical face boundary map is affine on every face of its common finite marked
subdivision. -/
theorem faceBoundaryMap_affineOn_subdivision (t : K.Face) :
    ∀ u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes,
      IsAffineOn
        (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        ((K.faceBoundarySubdivision
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier u) := by
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let S := standardTrianglePlaneComplex.oneSkeleton
  intro u hu
  have hsub : R.Subdivides S := K.faceBoundarySubdivision_subdivides t
  obtain ⟨s, hs, hus⟩ := hsub.2 u hu
  have hscard : s.card ≤ 2 := standardTrianglePlaneComplex.oneSkeleton_isGraph s hs
  have hucard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face hu hs hscard hus
  have hupos : 0 < u.card := Finset.card_pos.mpr (R.nonempty_of_mem u hu)
  have huCases : u.card = 1 ∨ u.card = 2 := by omega
  rcases huCases with huone | hutwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huone
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        (R.position v))
    refine ⟨g, ?_⟩
    intro p hp
    have hp' := hus hp
    have hpEq : p = R.position v := by
      simpa [PlaneComplex.cellCarrier] using hp
    subst p
    rfl
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hutwo
    have hspos : 0 < s.card := Finset.card_pos.mpr (S.nonempty_of_mem s hs)
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
      have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
      have hpEq : R.position p = S.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hp
      have hqEq : R.position q = S.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hq
      exact (hpq (R.position_injective (hpEq.trans hqEq.symm))).elim
    · obtain ⟨i, hsi⟩ := exists_faceStandardEdge_of_standardBoundaryEdge hstwo
      have hui : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
        intro x hx
        have hx' := hus hx
        rw [hsi, standardFaceEdgeFace_cellCarrier] at hx'
        exact hx'
      have hfrontier : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          frontier standardFaceRegion := by
        intro x hx
        have hxSupport := R.cellCarrier_subset_support hu hx
        rw [K.faceBoundarySubdivision_support t] at hxSupport
        exact hxSupport
      rcases K.faceBoundarySubdivision_piece t i hu hui with hleft | hmiddle | hright
      · exact K.faceBoundaryMap_affineOn_left t i hfrontier hui hleft
      · apply K.faceBoundaryMap_affineOn_middle t i hfrontier hui hmiddle.1 hmiddle.2
        exact K.faceBoundarySubdivision_middleSource t i hu hui
          (by simp [hpq]) hmiddle.1 hmiddle.2
      · exact K.faceBoundaryMap_affineOn_right t i hfrontier hui hright

/-- The canonical standard-triangle boundary map is genuinely PL on the polygonal frontier. -/
theorem faceBoundaryMap_isPLOnSet (t : K.Face) :
    IsPLOnSet (frontier standardFaceRegion)
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  refine ⟨S, ?_, R, K.faceBoundarySubdivision_subdivides t,
    K.faceBoundaryMap_affineOn_subdivision t⟩
  calc
    S.support = standardTriangleCircle.carrier := standardTriangle_oneSkeleton_support
    _ = frontier standardFaceRegion := by
      rw [standardTriangleCircle_carrier]
      simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_01
/- END ClassificationOfSurfaces.Moise.IntrinsicFaceExtension -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteFaceModel | a7b60d63627d75ce30e2032f69de55fd921e94ec40a94b4a0ff5e21eb1f762a9 -/
section schottkyclassification15_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Standard plane models for locally finite faces

A maximal face of a `LocallyFiniteTriangleComplex` is already parametrized by a standard
simplex on its three literal global vertices. This file reindexes those coordinates by the
chosen cyclic `Fin 3` ordering and identifies the result with the standard closed plane
triangle. The cyclic sides are carried exactly to the corresponding standard polygon sides.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- The closed standard triangle used as the source model for every locally finite face. -/
abbrev standardFaceRegion : Set Plane := standardTrianglePlaneComplex.support

/-- The frontier of the standard source triangle, as a subtype. -/
abbrev StandardFaceBoundary :=
  {p : Plane // p ∈ frontier standardFaceRegion}

theorem standardFaceBoundary_mem_region (p : StandardFaceBoundary) :
    p.1 ∈ standardFaceRegion :=
  standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset p.2

/-- One closed maximal face in its native simplex coordinates. -/
abbrev ClosedFace (f : K.Face) := stdSimplex ℝ {v // v ∈ K.faceVertices f}

/-- Reindex native face coordinates by the chosen cyclic `Fin 3` ordering. -/
noncomputable def faceReindexToStandard (f : K.Face) (x : K.ClosedFace f) :
    stdSimplex ℝ (Fin 3) := by
  refine ⟨fun i ↦ x (K.faceVertexEquiv f i), ?_, ?_⟩
  · exact fun i ↦ x.2.1 _
  · exact (K.faceVertexEquiv f).sum_comp (fun v ↦ x v) |>.trans x.2.2

/-- Undo the cyclic coordinate reindexing. -/
noncomputable def faceReindexFromStandard (f : K.Face) (z : stdSimplex ℝ (Fin 3)) :
    K.ClosedFace f := by
  refine ⟨fun v ↦ z ((K.faceVertexEquiv f).symm v), ?_, ?_⟩
  · exact fun v ↦ z.2.1 _
  · exact (K.faceVertexEquiv f).symm.sum_comp (fun i ↦ z i) |>.trans z.2.2

@[simp] theorem faceReindexFromStandard_toStandard (f : K.Face)
    (x : K.ClosedFace f) :
    K.faceReindexFromStandard f (K.faceReindexToStandard f x) = x := by
  apply Subtype.ext
  funext v
  change x (K.faceVertexEquiv f ((K.faceVertexEquiv f).symm v)) = x v
  rw [(K.faceVertexEquiv f).apply_symm_apply]

@[simp] theorem faceReindexToStandard_fromStandard (f : K.Face)
    (z : stdSimplex ℝ (Fin 3)) :
    K.faceReindexToStandard f (K.faceReindexFromStandard f z) = z := by
  apply Subtype.ext
  funext i
  change z ((K.faceVertexEquiv f).symm (K.faceVertexEquiv f i)) = z i
  rw [(K.faceVertexEquiv f).symm_apply_apply]

theorem continuous_faceReindexToStandard (f : K.Face) :
    Continuous (K.faceReindexToStandard f) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i ↦
    (continuous_apply (K.faceVertexEquiv f i)).comp continuous_subtype_val

theorem continuous_faceReindexFromStandard (f : K.Face) :
    Continuous (K.faceReindexFromStandard f) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun v ↦
    (continuous_apply ((K.faceVertexEquiv f).symm v)).comp continuous_subtype_val

/-- Native face coordinates are canonically homeomorphic to `stdSimplex ℝ (Fin 3)`. -/
noncomputable def faceReindexHomeomorph (f : K.Face) :
    K.ClosedFace f ≃ₜ stdSimplex ℝ (Fin 3) where
  toFun := K.faceReindexToStandard f
  invFun := K.faceReindexFromStandard f
  left_inv := K.faceReindexFromStandard_toStandard f
  right_inv := K.faceReindexToStandard_fromStandard f
  continuous_toFun := K.continuous_faceReindexToStandard f
  continuous_invFun := K.continuous_faceReindexFromStandard f

/-- Insert a standard simplex point into the one-face intrinsic realization used by the
standard plane triangle complex. -/
noncomputable def standardSimplexToRealization (z : stdSimplex ℝ (Fin 3)) :
    standardTrianglePlaneComplex.toIntrinsic.realization :=
  ⟨z.1, z.2, ⟨Finset.univ, standardTriangle_univ_mem_cells, by simp⟩⟩

/-- Forget the vacuous one-face support witness in the standard intrinsic realization. -/
noncomputable def standardRealizationToSimplex
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    stdSimplex ℝ (Fin 3) :=
  ⟨z.1, z.2.1⟩

@[simp] theorem standardRealizationToSimplex_toRealization (z : stdSimplex ℝ (Fin 3)) :
    standardRealizationToSimplex (standardSimplexToRealization z) = z := rfl

@[simp] theorem standardSimplexToRealization_toSimplex
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    standardSimplexToRealization (standardRealizationToSimplex z) = z := by
  apply Subtype.ext
  rfl

/-- The standard simplex and the canonical intrinsic realization of the standard triangle are
the same topological simplex. -/
noncomputable def standardSimplexRealizationHomeomorph :
    stdSimplex ℝ (Fin 3) ≃ₜ standardTrianglePlaneComplex.toIntrinsic.realization where
  toFun := standardSimplexToRealization
  invFun := standardRealizationToSimplex
  left_inv := standardRealizationToSimplex_toRealization
  right_inv := standardSimplexToRealization_toSimplex
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- A cyclic face edge is contained in the face which names it. -/
theorem faceEdge_subset_faceVertices (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 ⊆ K.faceVertices f := by
  rw [K.faceEdge_val f i]
  exact Finset.insert_subset_iff.mpr
    ⟨K.faceVertex_mem f i, Finset.singleton_subset_iff.mpr
      (K.faceVertex_mem f (i + 1))⟩

theorem edgeFirst_faceEdge_mem_face (f : K.Face) (i : ZMod 3) :
    K.edgeFirst (K.faceEdge f i) ∈ K.faceVertices f :=
  K.faceEdge_subset_faceVertices f i (K.edgeFirst_mem (K.faceEdge f i))

theorem edgeSecond_faceEdge_mem_face (f : K.Face) (i : ZMod 3) :
    K.edgeSecond (K.faceEdge f i) ∈ K.faceVertices f :=
  K.faceEdge_subset_faceVertices f i (K.edgeSecond_mem (K.faceEdge f i))

/-- The standard plane realization of one locally finite closed face. -/
noncomputable def facePlaneHomeomorph (f : K.Face) :
    K.ClosedFace f ≃ₜ standardTrianglePlaneComplex.support :=
  (K.faceReindexHomeomorph f).trans
    (standardSimplexRealizationHomeomorph.trans
      (standardTrianglePlaneComplex.realizationHomeomorph
        standardTrianglePlaneComplex_pure))

/-- The chosen ordering of a locally finite face, viewed in the global vertex type. -/
noncomputable def faceVertexEmbedding (f : K.Face) : Fin 3 ↪ K.Vertex where
  toFun j := (K.faceVertexEquiv f j).1
  inj' := fun _ _ h ↦ (K.faceVertexEquiv f).injective (Subtype.ext h)

/-- The standard corner corresponding to the globally chosen first endpoint of a face edge. -/
noncomputable def faceEdgeFirstIndex (f : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv f).symm
    ⟨K.edgeFirst (K.faceEdge f i), K.edgeFirst_faceEdge_mem_face f i⟩

/-- The standard corner corresponding to the globally chosen second endpoint of a face edge. -/
noncomputable def faceEdgeSecondIndex (f : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv f).symm
    ⟨K.edgeSecond (K.faceEdge f i), K.edgeSecond_faceEdge_mem_face f i⟩

@[simp] theorem faceVertexEmbedding_faceEdgeFirstIndex (f : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding f (K.faceEdgeFirstIndex f i) =
      K.edgeFirst (K.faceEdge f i) := by
  change ((K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _)).1 = _
  rw [(K.faceVertexEquiv f).apply_symm_apply]

@[simp] theorem faceVertexEmbedding_faceEdgeSecondIndex (f : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding f (K.faceEdgeSecondIndex f i) =
      K.edgeSecond (K.faceEdge f i) := by
  change ((K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _)).1 = _
  rw [(K.faceVertexEquiv f).apply_symm_apply]

/-- The two standard indices of cyclic side `i`, ordered by the global abstract edge. -/
theorem faceStandardEdge_eq_endpointIndices (f : K.Face) (i : ZMod 3) :
    IntrinsicTwoComplex.faceStandardEdge i =
      {K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} := by
  rcases K.faceEdge_endpoint_order f i with hforward | hreverse
  · have hfirst : K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm i := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hforward.1
    have hsecond : K.faceEdgeSecondIndex f i =
        (ZMod.finEquiv 3).symm (i + 1) := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hforward.2
    simp [IntrinsicTwoComplex.faceStandardEdge, hfirst, hsecond]
  · have hfirst : K.faceEdgeFirstIndex f i =
        (ZMod.finEquiv 3).symm (i + 1) := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hreverse.1
    have hsecond : K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm i := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hreverse.2
    simp [IntrinsicTwoComplex.faceStandardEdge, hfirst, hsecond,
      Finset.pair_comm]
    exact Finset.pair_comm _ _

/-- The standard source point on a face side, oriented by the global edge ordering. -/
noncomputable def faceEdgeSourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) : Plane :=
  AffineMap.lineMap
    (standardTriangleVertex (K.faceEdgeFirstIndex f i))
    (standardTriangleVertex (K.faceEdgeSecondIndex f i)) r

/-- The affine barycentric coordinate along the globally oriented standard side. -/
noncomputable def faceEdgeParameterAffine (f : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (K.faceEdgeSecondIndex f i)).toAffineMap.comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

@[simp] theorem faceEdgeParameterAffine_sourcePoint
    (f : K.Face) (i : ZMod 3) (r : ℝ) :
    K.faceEdgeParameterAffine f i (K.faceEdgeSourcePoint f i r) = r := by
  have hfirst := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace
    (v := K.faceEdgeFirstIndex f i) (by
      change K.faceEdgeFirstIndex f i ∈ (Finset.univ : Finset (Fin 3)); simp)
  have hsecond := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace
    (v := K.faceEdgeSecondIndex f i) (by
      change K.faceEdgeSecondIndex f i ∈ (Finset.univ : Finset (Fin 3)); simp)
  have hne : K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
    intro h
    apply K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
    rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
      ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]
  rw [standardTrianglePlaneComplex_position] at hfirst hsecond
  rw [faceEdgeParameterAffine, faceEdgeSourcePoint, AffineMap.comp_apply,
    AffineMap.apply_lineMap, hfirst, hsecond]
  simp [AffineMap.lineMap_apply_module, hne]

theorem faceEdgeSourcePoint_mem_standardEdge (f : K.Face) (i : ZMod 3)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r ∈
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices f i, PlaneComplex.cellCarrier]
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex f i),
        standardTriangleVertex (K.faceEdgeSecondIndex f i)} by
    ext p; simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact ⟨r, hr, rfl⟩

theorem faceEdgeSourcePoint_image_Icc (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i '' Set.Icc (0 : ℝ) 1 =
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices f i, PlaneComplex.cellCarrier]
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex f i),
        standardTriangleVertex (K.faceEdgeSecondIndex f i)} by
    ext p; simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  rfl

/-- Native face-simplex points supported on cyclic edge `i`. -/
def faceSide (f : K.Face) (i : ZMod 3) : Set (K.ClosedFace f) :=
  {x | ∀ v, v.1 ∉ (K.faceEdge f i).1 → x v = 0}

private theorem eq_edgeFirst_or_edgeSecond (e : K.Edge) {v : K.Vertex}
    (hv : v ∈ e.1) : v = K.edgeFirst e ∨ v = K.edgeSecond e := by
  rw [K.edge_eq_pair e] at hv
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hv

/-- The two endpoint coordinates of a face point supported on an edge add to one. -/
theorem supportedOnEdge_endpoint_sum (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    x ⟨K.edgeFirst e, hef (K.edgeFirst_mem e)⟩ +
        x ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩ = 1 := by
  let a : {v // v ∈ K.faceVertices f} :=
    ⟨K.edgeFirst e, hef (K.edgeFirst_mem e)⟩
  let b : {v // v ∈ K.faceVertices f} :=
    ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩
  let E : Finset {v // v ∈ K.faceVertices f} :=
    Finset.univ.filter fun v ↦ v.1 ∈ e.1
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  have hE : E = {a, b} := by
    ext v
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [K.edge_eq_pair e]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  change x a + x b = 1
  calc
    x a + x b = ∑ v ∈ E, x v := by rw [hE]; simp [hab]
    _ = ∑ v, x v := by
      apply Finset.sum_subset (Finset.subset_univ E)
      intro v _ hvE
      apply hx v
      intro hve
      apply hvE
      change v.1 ∈ e.1 at hve
      simp [E, hve]
    _ = 1 := x.2.2

theorem faceSide_endpoint_sum (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    x ⟨K.edgeFirst (K.faceEdge f i), K.edgeFirst_faceEdge_mem_face f i⟩ +
        x ⟨K.edgeSecond (K.faceEdge f i), K.edgeSecond_faceEdge_mem_face f i⟩ = 1 :=
  K.supportedOnEdge_endpoint_sum f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- Restrict a face-simplex point supported on an arbitrary incident edge. -/
noncomputable def supportedOnEdgeToSimplex (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (_hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    stdSimplex ℝ {v // v ∈ e.1} :=
  K.edgeSimplexPath e
    ⟨x ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩,
      mem_Icc_of_mem_stdSimplex x.2
        ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩⟩

/-- Restrict a face-simplex point supported on side `i` to the corresponding edge simplex. -/
noncomputable def faceSideToEdgeSimplex (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    stdSimplex ℝ {v // v ∈ (K.faceEdge f i).1} :=
  K.supportedOnEdgeToSimplex f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- A face point supported on an incident edge maps into that edge carrier. -/
theorem faceMap_mem_edgeCarrier_of_supportedOnEdge (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    K.faceMap f x ∈ K.edgeCarrier e := by
  let z := K.supportedOnEdgeToSimplex f e hef x hx
  refine ⟨z, ?_⟩
  rw [K.edgeMap_eq_faceMap e f hef z]
  apply K.faceMap_eq_iff.mpr
  rw [extendFaceCoordinates_map_subset]
  funext v
  by_cases hv : v ∈ e.1
  · rw [extendFaceCoordinates_of_mem e.1 z hv,
      extendFaceCoordinates_of_mem (K.faceVertices f) x (hef hv)]
    rcases K.eq_edgeFirst_or_edgeSecond e hv with hv | hv
    · subst v
      rw [show (⟨K.edgeFirst e, hv⟩ : {w // w ∈ e.1}) =
        ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ by apply Subtype.ext; rfl]
      dsimp [z, supportedOnEdgeToSimplex]
      rw [K.edgeSimplexPath_apply_first]
      linarith [K.supportedOnEdge_endpoint_sum f e hef x hx]
    · subst v
      rw [show (⟨K.edgeSecond e, hv⟩ : {w // w ∈ e.1}) =
        ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ by apply Subtype.ext; rfl]
      dsimp [z, supportedOnEdgeToSimplex]
      rw [K.edgeSimplexPath_apply_second]
  · rw [extendFaceCoordinates_of_notMem e.1 z hv]
    by_cases hvf : v ∈ K.faceVertices f
    · rw [extendFaceCoordinates_of_mem (K.faceVertices f) x hvf]
      exact (hx ⟨v, hvf⟩ hv).symm
    · rw [extendFaceCoordinates_of_notMem (K.faceVertices f) x hvf]

/-- A point of a native face side maps into the corresponding ambient edge carrier. -/
theorem faceMap_mem_edgeCarrier_of_mem_faceSide (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    K.faceMap f x ∈ K.edgeCarrier (K.faceEdge f i) :=
  K.faceMap_mem_edgeCarrier_of_supportedOnEdge f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- Include edge-local simplex coordinates in any incident maximal face. -/
noncomputable def edgeSimplexInFace (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) : K.ClosedFace f :=
  stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) z

theorem faceMap_edgeSimplexInFace (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) :
    K.faceMap f (K.edgeSimplexInFace f e hef z) = K.edgeMap e z :=
  (K.edgeMap_eq_faceMap e f hef z).symm

theorem edgeSimplexInFace_supported (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1})
    (v : {v // v ∈ K.faceVertices f}) (hv : v.1 ∉ e.1) :
    K.edgeSimplexInFace f e hef z v = 0 := by
  simp only [edgeSimplexInFace, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  have hempty : Finset.univ.filter
      (fun w : {w // w ∈ e.1} ↦
        (⟨w.1, hef w.2⟩ : {q // q ∈ K.faceVertices f}) = v) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro hw
    apply hv
    rw [← congrArg Subtype.val hw]
    exact w.2
  rw [hempty]
  simp

/-- Reindexing the canonical edge simplex inside a face gives the same oriented affine
parameter on the corresponding two standard vertices. -/
theorem faceReindexToStandard_edgeSimplexPath (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.faceReindexToStandard f
      (K.edgeSimplexInFace f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i)
        (K.edgeSimplexPath (K.faceEdge f i) r))).1 =
      AffineMap.lineMap
        (Pi.single (K.faceEdgeFirstIndex f i) (1 : ℝ) : Fin 3 → ℝ)
        (Pi.single (K.faceEdgeSecondIndex f i) (1 : ℝ) : Fin 3 → ℝ) r.1 := by
  classical
  funext j
  let e := K.faceEdge f i
  let hef := K.faceEdge_subset_faceVertices f i
  let x := K.edgeSimplexPath e r
  have hcoords := congrFun (extendFaceCoordinates_map_subset hef x)
    (K.faceVertexEmbedding f j)
  have hvf : K.faceVertexEmbedding f j ∈ K.faceVertices f :=
    (K.faceVertexEquiv f j).2
  rw [extendFaceCoordinates_of_mem (K.faceVertices f) _ hvf] at hcoords
  change (K.edgeSimplexInFace f e hef x) (K.faceVertexEquiv f j) = _
  change (K.edgeSimplexInFace f e hef x) (K.faceVertexEquiv f j) =
    extendFaceCoordinates e.1 x (K.faceVertexEmbedding f j) at hcoords
  by_cases hve : K.faceVertexEmbedding f j ∈ e.1
  · rcases K.eq_edgeFirst_or_edgeSecond e hve with hfirst | hsecond
    · have hj : j = K.faceEdgeFirstIndex f i := by
        apply (K.faceVertexEmbedding f).injective
        rw [K.faceVertexEmbedding_faceEdgeFirstIndex f i]
        exact hfirst
      subst j
      rw [hcoords, extendFaceCoordinates_of_mem e.1 x hve,
        show (⟨K.faceVertexEmbedding f (K.faceEdgeFirstIndex f i), hve⟩ :
          {v // v ∈ e.1}) =
            ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ by
              apply Subtype.ext
              exact K.faceVertexEmbedding_faceEdgeFirstIndex f i,
        K.edgeSimplexPath_apply_first]
      have hne : K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
        intro h
        apply K.edgeFirst_ne_edgeSecond e
        rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
          ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]
      simp [AffineMap.lineMap_apply_module, hne]
    · have hj : j = K.faceEdgeSecondIndex f i := by
        apply (K.faceVertexEmbedding f).injective
        rw [K.faceVertexEmbedding_faceEdgeSecondIndex f i]
        exact hsecond
      subst j
      rw [hcoords, extendFaceCoordinates_of_mem e.1 x hve,
        show (⟨K.faceVertexEmbedding f (K.faceEdgeSecondIndex f i), hve⟩ :
          {v // v ∈ e.1}) =
            ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ by
              apply Subtype.ext
              exact K.faceVertexEmbedding_faceEdgeSecondIndex f i,
        K.edgeSimplexPath_apply_second]
      have hne : K.faceEdgeSecondIndex f i ≠ K.faceEdgeFirstIndex f i := by
        intro h
        apply K.edgeFirst_ne_edgeSecond e
        rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
          ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, ← h]
      simp [AffineMap.lineMap_apply_module, hne]
  · have hjFirst : j ≠ K.faceEdgeFirstIndex f i := by
      intro h
      subst j
      exact hve (by
        rw [K.faceVertexEmbedding_faceEdgeFirstIndex f i]
        exact K.edgeFirst_mem e)
    have hjSecond : j ≠ K.faceEdgeSecondIndex f i := by
      intro h
      subst j
      exact hve (by
        rw [K.faceVertexEmbedding_faceEdgeSecondIndex f i]
        exact K.edgeSecond_mem e)
    rw [hcoords, extendFaceCoordinates_of_notMem e.1 x hve]
    simp [AffineMap.lineMap_apply_module, hjFirst, hjSecond]

/-- The standard plane chart sends the canonical edge-simplex path to the globally oriented
affine parameter on the corresponding standard side. -/
theorem facePlaneHomeomorph_edgeSimplexPath (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.facePlaneHomeomorph f
      (K.edgeSimplexInFace f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i)
        (K.edgeSimplexPath (K.faceEdge f i) r))).1 =
      K.faceEdgeSourcePoint f i r.1 := by
  rw [facePlaneHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    PlaneComplex.realizationHomeomorph_apply]
  change standardTrianglePlaneComplex.baryEval
      (K.faceReindexToStandard f
        (K.edgeSimplexInFace f (K.faceEdge f i)
          (K.faceEdge_subset_faceVertices f i)
          (K.edgeSimplexPath (K.faceEdge f i) r))).1 = _
  rw [K.faceReindexToStandard_edgeSimplexPath f i]
  rw [PlaneComplex.baryEval, faceEdgeSourcePoint,
    AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp_rw [add_smul]
  rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ j : Fin 3,
          ((1 - r.1) * if j = K.faceEdgeFirstIndex f i then 1 else 0) •
            standardTrianglePlaneComplex.position j =
        (1 - r.1) • standardTriangleVertex (K.faceEdgeFirstIndex f i) := by
    simp []
  have hsecond :
      ∑ j : Fin 3,
          (r.1 * if j = K.faceEdgeSecondIndex f i then 1 else 0) •
            standardTrianglePlaneComplex.position j =
        r.1 • standardTriangleVertex (K.faceEdgeSecondIndex f i) := by
    simp []
  rw [hfirst, hsecond, AffineMap.lineMap_apply_module]

theorem edgeCarrier_subset_faceCarrier_of_subset (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    K.edgeCarrier e ⊆ K.faceCarrier f := by
  rintro y ⟨z, rfl⟩
  exact ⟨K.edgeSimplexInFace f e hef z,
    K.faceMap_edgeSimplexInFace f e hef z⟩

theorem faceReindexToStandard_mem_faceCarrier (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) :
    standardSimplexToRealization (K.faceReindexToStandard f x) ∈
        standardTrianglePlaneComplex.toIntrinsic.faceCarrier
          (IntrinsicTwoComplex.faceStandardEdge i) ↔
      x ∈ K.faceSide f i := by
  constructor
  · intro hx v hv
    let j : Fin 3 := (K.faceVertexEquiv f).symm v
    have hj : j ∉ IntrinsicTwoComplex.faceStandardEdge i := by
      intro hj
      apply hv
      rw [K.faceEdge_val f i]
      simp only [IntrinsicTwoComplex.faceStandardEdge, Finset.mem_insert,
        Finset.mem_singleton] at hj ⊢
      rcases hj with hj | hj
      · left
        have heq : K.faceVertexEquiv f j = v :=
          (K.faceVertexEquiv f).apply_symm_apply v
        calc
          v.1 = (K.faceVertexEquiv f j).1 := congrArg Subtype.val heq.symm
          _ = K.faceVertex f i := by rw [hj]; rfl
      · right
        have heq : K.faceVertexEquiv f j = v :=
          (K.faceVertexEquiv f).apply_symm_apply v
        calc
          v.1 = (K.faceVertexEquiv f j).1 := congrArg Subtype.val heq.symm
          _ = K.faceVertex f (i + 1) := by rw [hj]; rfl
    have hz := hx j hj
    change x (K.faceVertexEquiv f j) = 0 at hz
    simpa [j] using hz
  · intro hx j hj
    change x (K.faceVertexEquiv f j) = 0
    apply hx
    intro hmem
    apply hj
    rw [K.faceEdge_val f i] at hmem
    simp only [IntrinsicTwoComplex.faceStandardEdge, Finset.mem_insert,
      Finset.mem_singleton] at hmem ⊢
    rcases hmem with hmem | hmem
    · left
      apply (K.faceVertexEquiv f).injective
      exact Subtype.ext hmem
    · right
      apply (K.faceVertexEquiv f).injective
      exact Subtype.ext hmem

/-- The standard plane chart sends cyclic source side `i` exactly onto cyclic side `i` of the
standard triangle. -/
theorem facePlaneHomeomorph_image_edge (f : K.Face) (i : ZMod 3) :
    (fun x : K.ClosedFace f ↦ (K.facePlaneHomeomorph f x).1) '' K.faceSide f i =
      standardTriangleCircle.edgeSegment i := by
  let s := IntrinsicTwoComplex.faceStandardEdge i
  have hs : s ∈ standardTrianglePlaneComplex.simplexes :=
    IntrinsicTwoComplex.faceStandardEdge_mem_simplexes i
  have hgeom := standardTrianglePlaneComplex.realizationHomeomorph_image_faceCarrier
    standardTrianglePlaneComplex_pure hs
  rw [IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i] at hgeom
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    let z := standardSimplexToRealization (K.faceReindexToStandard f x)
    have hz : z ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s := by
      exact (K.faceReindexToStandard_mem_faceCarrier f i x).mpr hx
    rw [← hgeom]
    exact ⟨z, hz, rfl⟩
  · intro p hp
    rw [← hgeom] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let x : K.ClosedFace f :=
      (K.faceReindexHomeomorph f).symm (standardRealizationToSimplex z)
    have hx : x ∈ K.faceSide f i := by
      apply (K.faceReindexToStandard_mem_faceCarrier f i x).mp
      have heq : standardSimplexToRealization (K.faceReindexToStandard f x) = z := by
        apply Subtype.ext
        change (K.faceReindexHomeomorph f x).1 = z.1
        rw [(K.faceReindexHomeomorph f).apply_symm_apply]
        rfl
      rwa [heq]
    refine ⟨x, hx, ?_⟩
    change (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure
        (standardSimplexToRealization (K.faceReindexHomeomorph f x))).1 = p
    simpa [x] using hzp

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_02
/- END ClassificationOfSurfaces.Moise.LocallyFiniteFaceModel -/

/- BEGIN ClassificationOfSurfaces.Moise.AdaptiveFanAffine | 84e386f15bdf2fb72519f5c98ae3374adf9112e9f595ce7e5d4b7d3012bf2543 -/
section schottkyclassification15_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Affine standard-coordinate formulas for adaptive fan faces

The adaptive fan realization is assembled through faithful midpoint subdivisions.  Although its
definition is geometric, on each named fan triangle its value in the original intrinsic
barycentric coordinates is one affine function of the standard planar face coordinates.  The
relative Radó weld uses this formula after composing with the inverse-affine pieces of retained
polygonal filling certificates.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (L : LocallyFiniteTriangleComplex S)

/-- Reindex standard coordinates onto the literal three-vertex type of one locally finite
face. -/
noncomputable def faceCoordExtensionAffineLF (f : L.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  AffineMap.pi fun v =>
    (LinearMap.proj ((L.faceVertexEquiv f).symm v)).toAffineMap

@[simp] theorem faceCoordExtensionAffineLF_apply
    (f : L.Face) (z : Fin 3 → ℝ)
    (v : {v // v ∈ L.faceVertices f}) :
    L.faceCoordExtensionAffineLF f z v =
      z ((L.faceVertexEquiv f).symm v) := by
  simp [faceCoordExtensionAffineLF]

/-- The affine inverse-coordinate formula for the standard plane chart of a locally finite
face. -/
noncomputable def facePlaneInverseAffineLF (f : L.Face) :
    Plane →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  (L.faceCoordExtensionAffineLF f).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

theorem facePlaneHomeomorph_symm_val_LF (f : L.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((L.facePlaneHomeomorph f).symm p).1 =
      L.facePlaneInverseAffineLF f p.1 := by
  let z := (standardTrianglePlaneComplex.realizationHomeomorph
    standardTrianglePlaneComplex_pure).symm p
  have hz : z.1 = standardTrianglePlaneComplex.faceCoords
      standardTriangleMeshFace p.1 := by
    apply standardTrianglePlaneComplex.realizationHomeomorph_symm_val_eq_faceCoords
      standardTrianglePlaneComplex_pure standardTriangleMeshFace p
    change p.1 ∈ standardTrianglePlaneComplex.cellCarrier
      (Finset.univ : Finset (Fin 3))
    rw [standardTriangle_cellCarrier_univ]
    exact p.2
  change
    (L.faceReindexFromStandard f
      (standardRealizationToSimplex z)).1 =
        L.facePlaneInverseAffineLF f p.1
  funext v
  simp only [faceReindexFromStandard, standardRealizationToSimplex,
    facePlaneInverseAffineLF, AffineMap.comp_apply,
    L.faceCoordExtensionAffineLF_apply]
  exact congrFun hz ((L.faceVertexEquiv f).symm v)

end LocallyFiniteTriangleComplex

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {U : Set K.realization}
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Relabeling a global adaptive fan simplex preserves the source-weighted affine sum. -/
theorem adaptiveFanRelabel_source_sum_apply
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (v : (K.safeSubdivision f.1.1).refined.Vertex) :
    (∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        (K.adaptiveFanRelabelSimplex U hU f x) p *
          (K.adaptiveFanVertexSource U hU f p).1 v) =
      ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        x ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
          (K.adaptiveFanVertexSource U hU f p).1 v := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  let q : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} :=
    (K.adaptiveFanFaceVertexEquiv U hU f).symm p
  have hweight :=
    K.adaptiveFanRelabel_extended_apply U hU f x q.1
  change
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
        (K.adaptiveFanRelabelSimplex U hU f x) p.1 =
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x q.1
    at hweight
  rw [extendFaceCoordinates_of_mem _ _ p.2,
    extendFaceCoordinates_of_mem _ _ q.2] at hweight
  exact hweight

theorem adaptiveGlobalFanFaceMap_standardAffine_point
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (aQ : ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ))
    (haQ : ∀ z : (K.safeSubdivision f.1.1).refined.realization,
      z ∈ (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 →
        ((K.safeSubdivision f.1.1).homeo z).1 = aQ z.1)
    (b : ({v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ) →ₗ[ℝ]
      (K.safeSubdivision f.1.1).refined.Vertex → ℝ)
    (hb : ∀ (z : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ)
      (v : (K.safeSubdivision f.1.1).refined.Vertex),
      b z v = ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        z ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
          (K.adaptiveFanVertexSource U hU f p).1 v) :
    ∀ x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
      ((K.safeSubdivision f.1.1).homeo
          (K.adaptiveFanSourcePoint U hU f
            (K.adaptiveFanRelabelSimplex U hU f x))).1 =
        aQ (b ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f
          ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1)) := by
  classical
  let R := K.adaptiveLocallyFiniteTriangleComplex U hU
  let Q := K.safeSubdivision f.1.1
  intro x
  let y := K.adaptiveFanRelabelSimplex U hU f x
  have hyCarrier : K.adaptiveFanSourcePoint U hU f y ∈
      Q.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f y
  have hxPlane : x.1 = R.facePlaneInverseAffineLF f
      (R.facePlaneHomeomorph f x).1 := by
    have h := R.facePlaneHomeomorph_symm_val_LF f (R.facePlaneHomeomorph f x)
    exact (congrArg Subtype.val ((R.facePlaneHomeomorph f).symm_apply_apply x)).symm.trans h
  change (Q.homeo (K.adaptiveFanSourcePoint U hU f y)).1 =
    aQ (b (R.facePlaneInverseAffineLF f (R.facePlaneHomeomorph f x).1))
  rw [haQ _ hyCarrier]
  apply congrArg aQ
  rw [← hxPlane]
  funext v
  change (∑ p, y p * (K.adaptiveFanVertexSource U hU f p).1 v) = b x.1 v
  rw [hb]
  exact K.adaptiveFanRelabel_source_sum_apply hU f x v

/-- The affine subdivision map on the refined face supporting a global fan. -/
noncomputable def adaptiveGlobalFanAffinePiece
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  Classical.choose ((K.safeSubdivision f.1.1).affineOnFace
    f.1.2.1.1 f.1.2.1.2)

/-- The linear map that relabels global fan coordinates into refined coordinates. -/
noncomputable def adaptiveGlobalFanLinearPiece
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ({v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ) →ₗ[ℝ]
      ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) :=
  ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
    (LinearMap.proj
      ((K.adaptiveFanFaceVertexEquiv U hU f).symm p)).smulRight
        (K.adaptiveFanVertexSource U hU f p).1

/-- The affine map describing one global adaptive fan face in standard coordinates. -/
noncomputable def adaptiveGlobalFanMapStandardAffine
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
  ((K.adaptiveGlobalFanAffinePiece hU f).comp
      (K.adaptiveGlobalFanLinearPiece hU f).toAffineMap).comp
    ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f)

/-- The standard simplex indexing a global adaptive fan face. -/
abbrev adaptiveGlobalFanSimplex (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :=
  stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}

/-- The intrinsic-coordinate value of a global adaptive fan face map. -/
noncomputable def adaptiveGlobalFanFaceMapValue
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    K.adaptiveGlobalFanSimplex hU f → (K.Vertex → ℝ) :=
  fun x ↦ (K.adaptiveGlobalFanFaceMap U hU f x).1.1

theorem adaptiveGlobalFanMapStandardAffine_apply
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    K.adaptiveGlobalFanFaceMapValue hU f x =
      K.adaptiveGlobalFanMapStandardAffine hU f
        ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1 := by
  classical
  have haQ := Classical.choose_spec ((K.safeSubdivision f.1.1).affineOnFace
    f.1.2.1.1 f.1.2.1.2)
  have hb : ∀ (z : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ)
      (v : (K.safeSubdivision f.1.1).refined.Vertex),
      K.adaptiveGlobalFanLinearPiece hU f z v =
        ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
          z ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
            (K.adaptiveFanVertexSource U hU f p).1 v := by
    intro z v
    simp only [adaptiveGlobalFanLinearPiece, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hpoint := K.adaptiveGlobalFanFaceMap_standardAffine_point hU f
    (K.adaptiveGlobalFanAffinePiece hU f) haQ
      (K.adaptiveGlobalFanLinearPiece hU f) hb x
  change ((K.safeSubdivision f.1.1).homeo
      (K.adaptiveFanSourcePoint U hU f
        (K.adaptiveFanRelabelSimplex U hU f x))).1 = _
  change _ =
    (((K.adaptiveGlobalFanAffinePiece hU f).comp
      (K.adaptiveGlobalFanLinearPiece hU f).toAffineMap).comp
        ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f))
      ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1
  exact hpoint

/- One adaptive global fan face is affine, in original intrinsic barycentric coordinates, as a
function of its standard planar face coordinates. -/
theorem adaptiveGlobalFanFaceMap_standardAffine
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ∃ a : Plane →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : K.adaptiveGlobalFanSimplex hU f,
        K.adaptiveGlobalFanFaceMapValue hU f x =
          a ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1 := by
  refine ⟨K.adaptiveGlobalFanMapStandardAffine hU f, ?_⟩
  intro x
  exact K.adaptiveGlobalFanMapStandardAffine_apply hU f x

/-- On one local fan triangle, the transported old barycentric coordinates are the
barycentric weighted sum of the coordinates of its three geometric vertices.  This is the
supporting-face formula used by the bordered chart straightening. -/
theorem adaptiveFanFaceMap_val_eq_vertex_sum
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.adaptiveFanFaceMap U hU f x).1.1 =
      fun v ↦ ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        x p * p.1.1 v := by
  classical
  let Q := K.safeSubdivision f.1.1
  obtain ⟨a, ha⟩ := Q.affineOnFace f.1.2.1.1 f.1.2.1.2
  let point :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} →
        (Q.refined.Vertex → ℝ) :=
    fun p ↦ (K.adaptiveFanVertexSource U hU f p).1
  let weight : {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ :=
    fun p ↦ x p
  have hweight : ∑ p, weight p = 1 := x.2.2
  let zfun : Q.refined.Vertex → ℝ :=
    (Finset.univ : Finset
      {p // p ∈ K.adaptiveFanFaceVertices U hU f}
    ).affineCombination ℝ point weight
  have hzfun :
      zfun = (K.adaptiveFanSourcePoint U hU f x).1 := by
    rw [show zfun =
        ∑ p, weight p • point p by
      exact Finset.affineCombination_eq_linear_combination
        Finset.univ point weight hweight]
    funext v
    simp only [weight, point, adaptiveFanSourcePoint,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsourceCarrier :
      K.adaptiveFanSourcePoint U hU f x ∈
        Q.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f x
  have hvertex (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
      a (point p) = p.1.1 := by
    have hpCarrier :=
      K.adaptiveFanVertexSource_mem_carrier U hU f p
    have hpAffine := ha (K.adaptiveFanVertexSource U hU f p) hpCarrier
    rw [← hpAffine]
    exact congrArg Subtype.val
      (Q.homeo.apply_symm_apply p.1)
  change
    (Q.homeo (K.adaptiveFanSourcePoint U hU f x)).1 =
      fun v ↦ ∑ p, x p * p.1.1 v
  rw [ha _ hsourceCarrier]
  change a (K.adaptiveFanSourcePoint U hU f x).1 = _
  rw [← hzfun,
    (Finset.univ : Finset
      {p // p ∈ K.adaptiveFanFaceVertices U hU f}
    ).map_affineCombination point weight hweight a,
    Finset.affineCombination_eq_linear_combination
      Finset.univ (a ∘ point) weight hweight]
  funext v
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, weight]
  apply Finset.sum_congr rfl
  intro p _
  rw [hvertex p]

/-- The same vertex-sum formula after relabeling a fan triangle by the global vertex type of
the locally finite adaptive complex. -/
theorem adaptiveGlobalFanFaceMap_val_eq_vertex_sum
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    (K.adaptiveGlobalFanFaceMap U hU f x).1.1 =
      fun k ↦ ∑ v :
          {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
        x v * v.1.1.1 k := by
  classical
  let E := K.adaptiveFanFaceVertexEquiv U hU f
  let y := K.adaptiveFanRelabelSimplex U hU f x
  rw [show K.adaptiveGlobalFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU f y by rfl,
    K.adaptiveFanFaceMap_val_eq_vertex_sum hU f y]
  funext k
  rw [← E.sum_comp
    (fun p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦
      y p * p.1.1 k)]
  apply Finset.sum_congr rfl
  intro v _
  have hweight :
      y (E v) = x v := by
    let gv : K.AdaptiveFanVertex U hU := v.1
    have h :=
      K.adaptiveFanRelabel_extended_apply U hU f x gv
    have hp : gv.1 ∈ K.adaptiveFanFaceVertices U hU f :=
      (E v).2
    rw [extendFaceCoordinates_of_mem
        (K.adaptiveFanFaceVertices U hU f)
          (K.adaptiveFanRelabelSimplex U hU f x) hp,
      extendFaceCoordinates_of_mem
        (K.adaptiveGlobalFanFaceVertices U hU f) x v.2] at h
    have hEv :
        E v = (⟨gv.1, hp⟩ :
          {p // p ∈ K.adaptiveFanFaceVertices U hU f}) := by
      apply Subtype.ext
      rfl
    rw [hEv]
    simpa only [y] using h
  rw [hweight]
  rfl

/-- The vertices of an adaptive fan face whose geometric source points lie in an old
barycentric carrier. -/
noncomputable def adaptiveGlobalFanFaceVerticesInCarrier
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex) : Finset (K.AdaptiveFanVertex U hU) := by
  classical
  exact
    (K.adaptiveGlobalFanFaceVertices U hU f).filter
      (fun w : K.AdaptiveFanVertex U hU ↦
        w.1 ∈ K.faceCarrier b)

/-- Pulling an old barycentric face carrier back to one adaptive fan triangle gives the
simplex face spanned by precisely those adaptive vertices which lie in the old carrier. -/
theorem adaptiveGlobalFanFaceMap_mem_faceCarrier_iff_supported
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    (K.adaptiveGlobalFanFaceMap U hU f x).1 ∈ K.faceCarrier b ↔
      ∀ v :
          {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
        v.1 ∉ K.adaptiveGlobalFanFaceVerticesInCarrier hU f b →
          x v = 0 := by
  classical
  rw [K.mem_faceCarrier_iff]
  rw [K.adaptiveGlobalFanFaceMap_val_eq_vertex_sum hU f x]
  constructor
  · intro hsupport v hv
    have hvNot : v.1.1 ∉ K.faceCarrier b := by
      simpa only [adaptiveGlobalFanFaceVerticesInCarrier,
        Finset.mem_filter, v.2, true_and] using hv
    rw [K.mem_faceCarrier_iff] at hvNot
    push Not at hvNot
    obtain ⟨k, hkb, hvk⟩ := hvNot
    have hvkPos : 0 < v.1.1.1 k :=
      lt_of_le_of_ne (v.1.1.2.1.1 k)
        (Ne.symm hvk)
    by_contra hxv
    have hxvPos : 0 < x v :=
      lt_of_le_of_ne (x.2.1 v) (Ne.symm hxv)
    have hsumPos :
        0 < ∑ w :
            {w // w ∈ K.adaptiveGlobalFanFaceVertices U hU f},
          x w * w.1.1.1 k := by
      apply Finset.sum_pos'
      · intro w _
        exact mul_nonneg (x.2.1 w) (w.1.1.2.1.1 k)
      · exact ⟨v, Finset.mem_univ v, mul_pos hxvPos hvkPos⟩
    have hzero := hsupport k hkb
    exact (ne_of_gt hsumPos) hzero
  · intro hx k hkb
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv :
        v.1 ∈ K.adaptiveGlobalFanFaceVerticesInCarrier hU f b
    · have hvCarrier : v.1.1 ∈ K.faceCarrier b :=
        (by
          simpa only [adaptiveGlobalFanFaceVerticesInCarrier,
            Finset.mem_filter, v.2, true_and] using hv)
      have hvzero :=
        (K.mem_faceCarrier_iff b v.1.1).mp hvCarrier k hkb
      rw [hvzero, mul_zero]
    · rw [hx v hv, zero_mul]

/-- Iterating the strict-interior preservation of midpoint subdivision reaches a level-zero
parent without requiring dependent arithmetic casts in downstream arguments. -/
private theorem exists_levelZeroAncestor_relInterior
    (n : ℕ) (s : K.LevelFace n) :
    ∃ a₀ : K.LevelFace 0,
      K.levelFaceRelInterior s ⊆ K.levelFaceRelInterior a₀ := by
  induction n with
  | zero =>
      exact ⟨s, Set.Subset.rfl⟩
  | succ n ih =>
      let p : K.LevelFace n := K.levelParentFace n s
      obtain ⟨a₀, ha₀⟩ := ih p
      exact ⟨a₀,
        (K.levelFaceRelInterior_subset_parent n s).trans ha₀⟩

/-- The cone center of an adaptive fan face lies in the relative interior of its unique
level-zero parent.  Hence it misses every proper old face of cardinality at most two in any
old triangle to which the refined face is subordinate. -/
theorem adaptiveFaceCenter_not_mem_faceCarrier_of_subordinate
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (t : K.Face)
    (hsub : ∀ x : (K.safeSubdivision f.1.1).refined.realization,
      x ∈ (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 →
        (K.safeSubdivision f.1.1).homeo x ∈ K.faceCarrier t.1)
    (b : Finset K.Vertex) (hbt : b ⊆ t.1) (hbcard : b.card ≤ 2) :
    K.adaptiveFaceCenter U f.1 ∉ K.faceCarrier b := by
  classical
  let s : K.LevelFace f.1.1 := f.1.2.1
  obtain ⟨a₀, ha₀⟩ :=
    exists_levelZeroAncestor_relInterior (K := K) f.1.1 s
  let t₀ : K.LevelFace 0 := by
    change K.Face
    exact t
  have hcenterAnc :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceRelInterior a₀ := by
    apply ha₀
    exact K.adaptiveFaceCenter_mem_relInterior U f.1
  have hcenterParent :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceCarrier t₀ := by
    have hc := K.adaptiveFaceCenter_mem_carrier U f.1
    obtain ⟨z, hz, hzeq⟩ := hc
    have hzParent := hsub z hz
    rw [hzeq] at hzParent
    change K.adaptiveFaceCenter U f.1 ∈
      (Subdivision.refl K).homeo '' K.faceCarrier t.1
    exact ⟨K.adaptiveFaceCenter U f.1, hzParent, rfl⟩
  have hat : a₀ = t₀ := by
    by_contra hne
    exact Set.disjoint_left.mp
      (K.disjoint_levelFaceRelInterior_levelFaceCarrier hne)
        hcenterAnc hcenterParent
  have hcenterRel :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceRelInterior t₀ := by
    rw [← hat]
    exact hcenterAnc
  have hcenterPos :
      ∀ v ∈ t.1, 0 < (K.adaptiveFaceCenter U f.1).1 v := by
    change K.adaptiveFaceCenter U f.1 ∈
      (K.safeSubdivision 0).homeo ''
        {x : (K.safeSubdivision 0).refined.realization |
          x ∈ (K.safeSubdivision 0).refined.faceCarrier t₀.1 ∧
            ∀ v ∈ t₀.1, 0 < x.1 v} at hcenterRel
    obtain ⟨z, ⟨-, hzpos⟩, hzeq⟩ := hcenterRel
    have hval :
        z.1 = (K.adaptiveFaceCenter U f.1).1 := by
      have := congrArg Subtype.val hzeq
      exact this
    intro v hvt
    rw [← congrFun hval v]
    exact hzpos v hvt
  have hproper : b ⊂ t.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hbt, ?_⟩
    intro h
    have := congrArg Finset.card h
    rw [K.faces_card t.1 t.2] at this
    omega
  obtain ⟨v, hvt, hvb⟩ := Finset.exists_of_ssubset hproper
  intro hcenterB
  have hzero :=
    (K.mem_faceCarrier_iff b (K.adaptiveFaceCenter U f.1)).mp
      hcenterB v hvb
  have hpos := hcenterPos v hvt
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos)

/-- If one declared fan vertex misses an old carrier, that pullback carrier has at most two
vertices and hence is an exposed proper face of the adaptive triangle. -/
theorem adaptiveGlobalFanFaceMap_exists_exposedFace
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex)
    (v₀ : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (hv₀ : v₀.1.1 ∉ K.faceCarrier b) :
    ∃ d : Finset (K.AdaptiveFanVertex U hU),
      d ⊆ K.adaptiveGlobalFanFaceVertices U hU f ∧
        d.card ≤ 2 ∧
        ∀ x : stdSimplex ℝ
            {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
          ((K.adaptiveGlobalFanFaceMap U hU f x).1 ∈ K.faceCarrier b ↔
            ∀ v :
                {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
              v.1 ∉ d → x v = 0) := by
  classical
  let d := K.adaptiveGlobalFanFaceVerticesInCarrier hU f b
  refine ⟨d, Finset.filter_subset _ _, ?_, ?_⟩
  · have hv₀d : v₀.1 ∉ d := by
      simp only [d, adaptiveGlobalFanFaceVerticesInCarrier,
        Finset.mem_filter, v₀.2, true_and]
      exact hv₀
    have hproper :
        d ⊂ K.adaptiveGlobalFanFaceVertices U hU f := by
      refine Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      apply hv₀d
      rw [heq]
      exact v₀.2
    have hcard :=
      Finset.card_lt_card hproper
    have hthree :
        (K.adaptiveGlobalFanFaceVertices U hU f).card = 3 :=
      (K.adaptiveLocallyFiniteTriangleComplex U hU).faceVertices_card f
    omega
  · intro x
    exact
      K.adaptiveGlobalFanFaceMap_mem_faceCarrier_iff_supported hU f b x

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_03
/- END ClassificationOfSurfaces.Moise.AdaptiveFanAffine -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicFaceFilling | 7dcc426d7bb7f45986ab84dc3f3dd10eb4fcf95917909eeaff9ed141f07f7ffe -/
section schottkyclassification15_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# PL fillings of intrinsic polygonal face boundaries

The simultaneous intrinsic graph replacement gives every maximal face a canonical map from the
standard triangular frontier onto a simple polygonal circle.  `IntrinsicFaceExtension` proves
that this map is genuinely PL on one named finite subdivision.  Polygonal Schoenflies now fills
it by a finite PL homeomorphism, without changing any shared-edge boundary values.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- A certified finite PL filling of the canonical polygonal boundary of one intrinsic face. -/
structure FacePLFilling (t : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map
    (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion =
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion)

/-- Polygonal Schoenflies fills the canonical face boundary by a finite PL homeomorphism. -/
theorem exists_facePLFilling (t : K.Face) :
    Nonempty (K.FacePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle J
      (K.faceBoundaryMap_isPLOnSet t)
      (K.faceBoundaryMap_injectiveOn t)
      (K.faceBoundaryMap_image_polygon t)
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert
  }⟩

/-- A fixed choice of the certified PL filling for downstream finite gluing. -/
noncomputable def facePLFilling (t : K.Face) :
    K.FacePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
  Classical.choice (K.exists_facePLFilling t)

/-- Fillings of neighboring faces agree wherever their standard boundary lifts name the same
intrinsic one-skeleton point.  The equality is pointwise because both restrictions are the same
global graph replacement map. -/
theorem facePLFilling_eq_of_boundaryLift_eq
    {t u : K.Face} {p q : StandardFaceBoundary}
    (hpq : (K.faceBoundaryLift t p).1 = (K.faceBoundaryLift u q).1) :
    (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).map p.1 =
      (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).map q.1 := by
  rw [(K.facePLFilling t).eqOn_boundary p.2,
    (K.facePLFilling u).eqOn_boundary q.2,
    K.faceBoundaryMap_apply t p, K.faceBoundaryMap_apply u q, hpq]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_04
/- END ClassificationOfSurfaces.Moise.IntrinsicFaceFilling -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteFaceExtension | b0a0cadb886245fcaada1fc1e8f7bc92e0e2c125bb2dcc25942803d47920891a -/
section schottkyclassification15_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Coherent polygonal boundary maps for locally finite faces

The globally defined locally finite graph replacement is restricted to each standard triangular
frontier.  Since a shared abstract edge is represented by the same source-support points, the
resulting boundary maps agree literally on overlaps.  This is the compatibility needed before
applying polygonal Schoenflies face by face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-- The inverse standard-face chart takes cyclic side `i` into the corresponding native side. -/
theorem facePlaneHomeomorph_symm_mem_faceSide (f : K.Face) (i : ZMod 3)
    (p : StandardFaceBoundary)
    (hp : p.1 ∈ standardTriangleCircle.edgeSegment i) :
    (K.facePlaneHomeomorph f).symm
        ⟨p.1, standardFaceBoundary_mem_region p⟩ ∈ K.faceSide f i := by
  rw [← K.facePlaneHomeomorph_image_edge f i] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have heq : (K.facePlaneHomeomorph f).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩ = x := by
    apply (K.facePlaneHomeomorph f).injective
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
    exact Subtype.ext hxp.symm
  rwa [heq]

/-- The source-support point named by a standard face-boundary point. -/
noncomputable def faceBoundarySupportPoint (f : K.Face)
    (p : StandardFaceBoundary) : K.support :=
  faceToSupport (K := K) f
    ((K.facePlaneHomeomorph f).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩)

theorem faceBoundarySupportPoint_mem_edge (f : K.Face) (i : ZMod 3)
    (p : StandardFaceBoundary)
    (hp : p.1 ∈ standardTriangleCircle.edgeSegment i) :
    K.faceBoundarySupportPoint f p ∈ edgeInSupport (K := K) (K.faceEdge f i) := by
  rw [edgeInSupport_eq_preimage (K := K)]
  exact K.faceMap_mem_edgeCarrier_of_mem_faceSide f i _
    (K.facePlaneHomeomorph_symm_mem_faceSide f i p hp)

theorem faceBoundarySupportPoint_mem_oneSkeleton (f : K.Face)
    (p : StandardFaceBoundary) :
    K.faceBoundarySupportPoint f p ∈ oneSkeletonInSupport (K := K) := by
  have hpCarrier : p.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using p.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  exact Set.mem_iUnion.mpr
    ⟨K.faceEdge f i, K.faceBoundarySupportPoint_mem_edge f i p hi⟩

/-- The canonical lift of a standard triangular frontier to the source one-skeleton. -/
noncomputable def faceBoundaryLift (f : K.Face) :
    StandardFaceBoundary → oneSkeletonInSupport (K := K) :=
  fun p ↦ ⟨K.faceBoundarySupportPoint f p,
    K.faceBoundarySupportPoint_mem_oneSkeleton f p⟩

theorem continuous_faceBoundarySupportPoint (f : K.Face) :
    Continuous (K.faceBoundarySupportPoint f) := by
  apply Continuous.subtype_mk
  exact (K.faceMap_continuous f).comp
    ((K.facePlaneHomeomorph f).symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

theorem continuous_faceBoundaryLift (f : K.Face) :
    Continuous (K.faceBoundaryLift f) := by
  apply Continuous.subtype_mk
  exact K.continuous_faceBoundarySupportPoint f

theorem injective_faceBoundaryLift (f : K.Face) :
    Function.Injective (K.faceBoundaryLift f) := by
  intro p q hpq
  have hmap : K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨p.1, standardFaceBoundary_mem_region p⟩) =
      K.faceMap f
        ((K.facePlaneHomeomorph f).symm
          ⟨q.1, standardFaceBoundary_mem_region q⟩) :=
    congrArg (fun z : oneSkeletonInSupport (K := K) ↦ (z.1 : K.support).1) hpq
  have hface := K.faceMap_injective f hmap
  have hstandard := (K.facePlaneHomeomorph f).symm.injective hface
  apply Subtype.ext
  exact congrArg (fun z : standardFaceRegion ↦ z.1) hstandard

/-- The global graph replacement expressed on one standard face frontier. -/
noncomputable def faceBoundaryMap (f : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ frontier standardFaceRegion then
    G.graphReplacementMap (K.faceBoundaryLift f ⟨p, hp⟩)
  else 0

@[simp] theorem faceBoundaryMap_apply (f : K.Face) (p : StandardFaceBoundary) :
    K.faceBoundaryMap (G := G) f p.1 =
      G.graphReplacementMap (K.faceBoundaryLift f p) := by
  simp [faceBoundaryMap, p.2]

theorem continuousOn_faceBoundaryMap (f : K.Face) :
    ContinuousOn (K.faceBoundaryMap (G := G) f)
      (frontier standardFaceRegion) := by
  rw [continuousOn_iff_continuous_restrict]
  convert G.continuous_graphReplacementMap.comp (K.continuous_faceBoundaryLift f) using 1
  funext p
  exact K.faceBoundaryMap_apply f p

theorem faceBoundaryMap_injectiveOn (f : K.Face) :
    Set.InjOn (K.faceBoundaryMap (G := G) f)
      (frontier standardFaceRegion) := by
  intro p hp q hq hpq
  let p' : StandardFaceBoundary := ⟨p, hp⟩
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have hgraph : G.graphReplacementMap (K.faceBoundaryLift f p') =
      G.graphReplacementMap (K.faceBoundaryLift f q') := by
    rw [← K.faceBoundaryMap_apply f p', ← K.faceBoundaryMap_apply f q']
    exact hpq
  exact congrArg Subtype.val
    (K.injective_faceBoundaryLift f (G.graphReplacementMap_injective hgraph))

/-- The globally oriented affine parameter on a standard side lies on the face frontier. -/
theorem faceEdgeSourcePoint_mem_frontier (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r.1 ∈ frontier standardFaceRegion := by
  have hpEdge : K.faceEdgeSourcePoint f i r.1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i]
    exact K.faceEdgeSourcePoint_mem_standardEdge f i r.2
  have hpCarrier : K.faceEdgeSourcePoint f i r.1 ∈
      standardTriangleCircle.carrier :=
    Set.mem_iUnion.mpr ⟨i, hpEdge⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- On a standard face side, the canonical boundary lift is literally the global canonical
source path of the corresponding abstract edge. -/
theorem faceBoundarySupportPoint_sourcePoint (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceBoundarySupportPoint f
        ⟨K.faceEdgeSourcePoint f i r.1,
          K.faceEdgeSourcePoint_mem_frontier f i r⟩ =
      edgePathInSupport (K := K) (K.faceEdge f i) r := by
  apply Subtype.ext
  change K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨K.faceEdgeSourcePoint f i r.1,
          standardFaceBoundary_mem_region
            ⟨K.faceEdgeSourcePoint f i r.1,
              K.faceEdgeSourcePoint_mem_frontier f i r⟩⟩) =
    K.edgePath (K.faceEdge f i) r
  have hinv :
      (K.facePlaneHomeomorph f).symm
          ⟨K.faceEdgeSourcePoint f i r.1,
            standardFaceBoundary_mem_region
              ⟨K.faceEdgeSourcePoint f i r.1,
                K.faceEdgeSourcePoint_mem_frontier f i r⟩⟩ =
        K.edgeSimplexInFace f (K.faceEdge f i)
          (K.faceEdge_subset_faceVertices f i)
          (K.edgeSimplexPath (K.faceEdge f i) r) := by
    apply (K.facePlaneHomeomorph f).injective
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
    apply Subtype.ext
    exact K.facePlaneHomeomorph_edgeSimplexPath f i r |>.symm
  rw [hinv, K.faceMap_edgeSimplexInFace]
  rfl

/-- On every oriented source side, the face boundary map is the complete polygonal replacement
path with the identical unit-interval parameter. -/
theorem faceBoundaryMap_sourcePoint (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r.1) =
      (G.replacementArc (K.faceEdge f i)).completePath r := by
  let p : StandardFaceBoundary :=
    ⟨K.faceEdgeSourcePoint f i r.1,
      K.faceEdgeSourcePoint_mem_frontier f i r⟩
  have hpEdge : p.1 ∈ standardTriangleCircle.edgeSegment i := by
    rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i]
    exact K.faceEdgeSourcePoint_mem_standardEdge f i r.2
  change K.faceBoundaryMap (G := G) f p.1 = _
  rw [K.faceBoundaryMap_apply (G := G) f p]
  rw [G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f p)
    (K.faceBoundarySupportPoint_mem_edge f i p hpEdge)]
  have hlift : (K.faceBoundaryLift f p).1 =
      edgePathInSupport (K := K) (K.faceEdge f i) r := by
    exact K.faceBoundarySupportPoint_sourcePoint f i r
  convert replacementEdgeMap_edgePath G (K.faceEdge f i) r using 1
  congr 1
  apply Subtype.ext
  exact hlift

/-- The canonical face boundary map has exactly the assembled three-edge carrier as image. -/
theorem faceBoundaryMap_image_frontier (f : K.Face) :
    K.faceBoundaryMap (G := G) f '' frontier standardFaceRegion =
      K.faceReplacementCarrier (G := G) f := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have hpCarrier : p ∈ standardTriangleCircle.carrier := by
      rw [standardTriangleCircle_carrier]
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    let q : StandardFaceBoundary := ⟨p, hp⟩
    rw [K.faceBoundaryMap_apply f q,
      G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f q)
        (K.faceBoundarySupportPoint_mem_edge f i q hi),
      ← G.range_replacementEdgeMap (K.faceEdge f i)]
    exact Set.mem_range_self _
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [← G.range_replacementEdgeMap (K.faceEdge f i)] at hi
    obtain ⟨q, rfl⟩ := hi
    have hqEdge : q.1.1 ∈ K.edgeCarrier (K.faceEdge f i) := by
      have hq : q.1 ∈ Subtype.val ⁻¹' K.edgeCarrier (K.faceEdge f i) := by
        rw [← edgeInSupport_eq_preimage (K := K) (K.faceEdge f i)]
        exact q.2
      exact hq
    obtain ⟨z, hz⟩ := hqEdge
    let x : K.ClosedFace f := K.edgeSimplexInFace f (K.faceEdge f i)
      (K.faceEdge_subset_faceVertices f i) z
    let p : Plane := (K.facePlaneHomeomorph f x).1
    have hxSide : x ∈ K.faceSide f i := by
      intro v hv
      exact K.edgeSimplexInFace_supported f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i) z v hv
    have hpSide : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← K.facePlaneHomeomorph_image_edge f i]
      exact ⟨x, hxSide, rfl⟩
    have hpFrontier : p ∈ frontier standardFaceRegion := by
      have hpCarrier : p ∈ standardTriangleCircle.carrier :=
        Set.mem_iUnion.mpr ⟨i, hpSide⟩
      rw [standardTriangleCircle_carrier] at hpCarrier
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier
    refine ⟨p, hpFrontier, ?_⟩
    let p' : StandardFaceBoundary := ⟨p, hpFrontier⟩
    have hlift : (K.faceBoundaryLift f p').1 = q.1 := by
      apply Subtype.ext
      change K.faceMap f
          ((K.facePlaneHomeomorph f).symm
            ⟨p, standardFaceBoundary_mem_region p'⟩) = q.1.1
      have hinv : (K.facePlaneHomeomorph f).symm
          ⟨p, standardFaceBoundary_mem_region p'⟩ = x := by
        apply (K.facePlaneHomeomorph f).injective
        rw [(K.facePlaneHomeomorph f).apply_symm_apply]
      rw [hinv, K.faceMap_edgeSimplexInFace, hz]
    rw [K.faceBoundaryMap_apply f p',
      G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f p')
        (K.faceBoundarySupportPoint_mem_edge f i p' hpSide)]
    congr 1
    apply Subtype.ext
    exact hlift

theorem faceBoundaryMap_image_polygon (f : K.Face) :
    K.faceBoundaryMap (G := G) f '' frontier standardFaceRegion =
      (K.facePolygonalCircle (G := G) f).carrier := by
  rw [K.faceBoundaryMap_image_frontier f, K.facePolygonalCircle_carrier f]

/-! ## A finite source subdivision carrying all boundary breakpoints -/

/-- All source breakpoints required on the three replacement sides of one face. -/
abbrev FaceBreakpoint (f : K.Face) :=
  Σ i : ZMod 3, EdgeBreakpoint (G.replacementArc (K.faceEdge f i))

/-- Place one replacement-edge breakpoint on its globally oriented standard side. -/
noncomputable def faceBreakpointPoint (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) : Plane :=
  K.faceEdgeSourcePoint f b.1
    (edgeBreakpointParameter (G.replacementArc (K.faceEdge f b.1)) b.2)

theorem faceBreakpointPoint_mem_standardEdge (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) :
    K.faceBreakpointPoint (G := G) f b ∈
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge b.1) := by
  apply K.faceEdgeSourcePoint_mem_standardEdge
  exact edgeBreakpointParameter_mem
    (G.replacementArc (K.faceEdge f b.1)) b.2

theorem faceBreakpointPoint_mem_standardOneSkeleton (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) :
    K.faceBreakpointPoint (G := G) f b ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  apply standardTrianglePlaneComplex.oneSkeleton.cellCarrier_subset_support
    (standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨IntrinsicTwoComplex.faceStandardEdge_mem_simplexes b.1,
        (IntrinsicTwoComplex.faceStandardEdge_card b.1).le⟩)
  simpa only [PlaneComplex.oneSkeleton_cellCarrier] using
    K.faceBreakpointPoint_mem_standardEdge (G := G) f b

/-- The common finite subdivision of the standard triangular boundary carrying every spoke
join and every vertex of the three finite middle polygonal models. -/
noncomputable def faceBoundarySubdivision (f : K.Face) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.faceBreakpointPoint (G := G) f)

theorem faceBoundarySubdivision_subdivides (f : K.Face) :
    (K.faceBoundarySubdivision (G := G) f).Subdivides
      standardTrianglePlaneComplex.oneSkeleton :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
    (K.faceBreakpointPoint (G := G) f)
    standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph

theorem faceBoundarySubdivision_support (f : K.Face) :
    (K.faceBoundarySubdivision (G := G) f).support =
      frontier standardFaceRegion := by
  rw [faceBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.faceBreakpointPoint (G := G) f)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    IntrinsicTwoComplex.standardTriangle_oneSkeleton_support,
    standardTriangleCircle_carrier]
  simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

/-- The first globally oriented standard corner, typed as a vertex of the standard boundary
graph. -/
noncomputable def faceEdgeFirstBoundaryVertex (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeFirstIndex f i

/-- The second globally oriented standard corner, typed as a vertex of the standard boundary
graph. -/
noncomputable def faceEdgeSecondBoundaryVertex (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeSecondIndex f i

@[simp] theorem faceEdgeFirstBoundaryVertex_position (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position
        (K.faceEdgeFirstBoundaryVertex f i) =
      standardTriangleVertex (K.faceEdgeFirstIndex f i) := rfl

@[simp] theorem faceEdgeSecondBoundaryVertex_position (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position
        (K.faceEdgeSecondBoundaryVertex f i) =
      standardTriangleVertex (K.faceEdgeSecondIndex f i) := rfl

theorem standardFaceEdgeFace_val_eq_boundaryEndpoints (f : K.Face) (i : ZMod 3) :
    (IntrinsicTwoComplex.standardFaceEdgeFace i).1 =
      {K.faceEdgeFirstBoundaryVertex f i,
        K.faceEdgeSecondBoundaryVertex f i} := by
  change IntrinsicTwoComplex.faceStandardEdge i =
    {K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i}
  exact K.faceStandardEdge_eq_endpointIndices f i

/-- The arbitrary finite graph enumeration of a standard side either follows or reverses the
global edge orientation. -/
theorem standardFaceEdge_endpoint_order (f : K.Face) (i : ZMod 3) :
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex f i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex f i) ∨
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex f i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex f i) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let j := IntrinsicTwoComplex.standardFaceEdgeIndex i
  have hfirst : T.edgeFirst j ∈ (T.edgeAt j).1 := by
    rw [T.edgeAt_eq]
    simp
  have hsecond : T.edgeSecond j ∈ (T.edgeAt j).1 := by
    rw [T.edgeAt_eq]
    simp
  have hedge : (T.edgeAt j).1 =
      (IntrinsicTwoComplex.standardFaceEdgeFace i).1 :=
    congrArg Subtype.val (IntrinsicTwoComplex.standardFaceEdgeAt_eq i)
  rw [hedge, K.standardFaceEdgeFace_val_eq_boundaryEndpoints f i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (T.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (T.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim

theorem standardFaceEdgeParameter_sourcePoint_of_forward (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint f i r) = r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position f i,
    ← K.faceEdgeSecondBoundaryVertex_position f i,
    ← horient.1, ← horient.2,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_sourcePoint_of_reverse (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint f i r) = 1 - r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position f i,
    ← K.faceEdgeSecondBoundaryVertex_position f i,
    ← horient.2, ← horient.1, ← AffineMap.lineMap_apply_one_sub,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
    (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i) p =
      K.faceEdgeParameterAffine f i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_forward f i horient,
    K.faceEdgeParameterAffine_sourcePoint]

theorem standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
    (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i) p =
      1 - K.faceEdgeParameterAffine f i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_reverse f i horient,
    K.faceEdgeParameterAffine_sourcePoint]

/-- Every face of the marked boundary subdivision lies on one side of every marked parameter,
measured in the finite graph enumeration coordinate. -/
theorem faceBoundarySubdivision_parameter_side_standard
    (f : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (G.replacementArc (K.faceEdge f i)))
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) p ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (G := G) f ⟨i, b⟩)) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (G := G) f ⟨i, b⟩) ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) p) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let point := K.faceBreakpointPoint (G := G) f
  let j := IntrinsicTwoComplex.standardFaceEdgeIndex i
  have hbCarrier : point ⟨i, b⟩ ∈ T.cellCarrier (T.edgeAt j).1 := by
    rw [show (T.edgeAt j).1 = IntrinsicTwoComplex.faceStandardEdge i from
      congrArg Subtype.val (IntrinsicTwoComplex.standardFaceEdgeAt_eq i)]
    rw [standardTrianglePlaneComplex.oneSkeleton_cellCarrier]
    exact K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩
  have hpoint : point ⟨i, b⟩ =
      AffineMap.lineMap (T.position (T.edgeFirst j)) (T.position (T.edgeSecond j))
        (T.edgeParameter j (point ⟨i, b⟩)) :=
    (T.lineMap_edgeParameter_eq j hbCarrier).symm
  have huArrangement :=
    ((T.markedEdgeArrangement point).mem_subordinateTo_simplexes_iff T).mp hu |>.1
  have hside := T.markedFaceCarrier_parameter_side point
    (⟨i, b⟩ : FaceBreakpoint (K := K) (G := G) f)
    j (T.edgeParameter j (point ⟨i, b⟩)) hpoint huArrangement
  exact hside

/-- On a subdivision face contained in one standard side, the marked-side test is the globally
oriented edge-parameter test, independently of the graph enumeration orientation. -/
theorem faceBoundarySubdivision_parameter_side
    (f : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (G.replacementArc (K.faceEdge f i)))
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i)) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤
        edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b ≤
        K.faceEdgeParameterAffine f i p) := by
  have hside := K.faceBoundarySubdivision_parameter_side_standard
    (G := G) f i b hu
  have hmark : K.faceBreakpointPoint (G := G) f ⟨i, b⟩ =
      K.faceEdgeSourcePoint f i
        (edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b) := rfl
  rcases K.standardFaceEdge_endpoint_order f i with hforward | hreverse
  · have hmarkEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
      f i hforward (K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        f i hforward (hui hp)
      have hpSide := hle p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        f i hforward (hui hp)
      have hpSide := hge p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
  · have hmarkEq :=
      K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (hui hp)
      have h := hle p hp
      rw [hpEq, hmark, hmarkEq] at h
      linarith
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (hui hp)
      have h := hge p hp
      rw [hpEq, hmark, hmarkEq] at h
      linarith

/-- The two spoke joins split each subdivision face on a selected standard side into the left,
middle, or right parameter range. -/
theorem faceBoundarySubdivision_piece
    (f : K.Face) (i : ZMod 3)
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i)) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) ∨
    ((∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p) ∧
      (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
        K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ))) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) := by
  have hhalf := K.faceBoundarySubdivision_parameter_side
    (G := G) f i none hu hui
  have hthree := K.faceBoundarySubdivision_parameter_side
    (G := G) f i (some none) hu hui
  change (∀ p ∈ _, K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) ∨
      (∀ p ∈ _, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p) at hhalf
  change (∀ p ∈ _, K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ)) ∨
      (∀ p ∈ _, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) at hthree
  rcases hhalf with hleHalf | hgeHalf
  · exact Or.inl hleHalf
  · rcases hthree with hleThree | hgeThree
    · exact Or.inr (Or.inl ⟨hgeHalf, hleThree⟩)
    · exact Or.inr (Or.inr hgeThree)

/-! ## Affine formulas on subdivision pieces -/

/-- The affine map from a standard face side into the source axis of the finite middle
polygonal model. -/
noncomputable def faceMiddleSourceAffine (f : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] Plane :=
  let A := G.replacementArc (K.faceEdge f i)
  (AffineMap.lineMap
    (planePoint (A.parameterization.length *
      (A.exitData.left + (A.exitData.right - A.exitData.left) * (-2))) 0)
    (planePoint (A.parameterization.length *
      (A.exitData.left + (A.exitData.right - A.exitData.left) * 2)) 0)).comp
    (K.faceEdgeParameterAffine f i)

@[simp] theorem faceMiddleSourceAffine_apply (f : K.Face) (i : ZMod 3)
    (p : Plane) :
    K.faceMiddleSourceAffine (G := G) f i p =
      planePoint ((G.replacementArc (K.faceEdge f i)).parameterization.length *
        ((G.replacementArc (K.faceEdge f i)).exitData.left +
          ((G.replacementArc (K.faceEdge f i)).exitData.right -
            (G.replacementArc (K.faceEdge f i)).exitData.left) *
          (4 * K.faceEdgeParameterAffine f i p - 2))) 0 := by
  let A := G.replacementArc (K.faceEdge f i)
  change (AffineMap.lineMap
      (planePoint (A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) * (-2))) 0)
      (planePoint (A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) * 2)) 0))
        (K.faceEdgeParameterAffine f i p) = _
  ext j
  fin_cases j <;>
    simp [AffineMap.lineMap_apply_module, planePoint]; ring

/-- The boundary map is affine on every subset of a standard side contained in the first
spoke range. -/
theorem faceBoundaryMap_affineOn_left
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hle : ∀ p ∈ E, K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  let scalar : Plane →ᵃ[ℝ] ℝ := (2 : ℝ) • K.faceEdgeParameterAffine f i
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap (G.vertexImage (K.edgeFirst (K.faceEdge f i)))
      A.leftEndpoint).comp scalar
  refine ⟨g, ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let q : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hq : r ≤ (1 / 2 : ℝ) := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hle (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath q from K.faceBoundaryMap_sourcePoint (G := G) f i q,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_left A q hq]
  simp [g, scalar, q, AffineMap.comp_apply]

/-- The boundary map is affine on every subset of a standard side contained in the final
spoke range. -/
theorem faceBoundaryMap_affineOn_right
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hge : ∀ p ∈ E, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  let scalar : Plane →ᵃ[ℝ] ℝ :=
    (4 : ℝ) • K.faceEdgeParameterAffine f i - AffineMap.const ℝ Plane 3
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap A.rightEndpoint
      (G.vertexImage (K.edgeSecond (K.faceEdge f i)))).comp scalar
  refine ⟨g, ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let q : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hq : (3 / 4 : ℝ) ≤ r := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hge (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath q from K.faceBoundaryMap_sourcePoint (G := G) f i q,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_right A q hq]
  simp [g, scalar, q, AffineMap.comp_apply]

/-- A middle side piece is affine once its affine source image lies in one simplex of the
finite polygonal segment model. -/
theorem faceBoundaryMap_affineOn_middle
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hmid0 : ∀ p ∈ E, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p)
    (hmid1 : ∀ p ∈ E, K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ))
    (hsource : ∃ s ∈
        (G.replacementArc (K.faceEdge f i)).parameterization.source.simplexes,
      Set.MapsTo (K.faceMiddleSourceAffine (G := G) f i) E
        ((G.replacementArc (K.faceEdge f i)).parameterization.source.cellCarrier s)) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  obtain ⟨s, hs, hmaps⟩ := hsource
  obtain ⟨q, hq⟩ := A.parameterization.map_affineOn s hs
  refine ⟨q.comp (K.faceMiddleSourceAffine (G := G) f i), ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let t : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have ht0 : (1 / 2 : ℝ) ≤ r := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hmid0 (K.faceEdgeSourcePoint f i r) hp
  have ht1 : r ≤ (3 / 4 : ℝ) := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hmid1 (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath t from K.faceBoundaryMap_sourcePoint (G := G) f i t,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_middle A t ht0 ht1]
  simpa only [AffineMap.comp_apply, K.faceMiddleSourceAffine_apply,
    K.faceEdgeParameterAffine_sourcePoint] using hq (hmaps hp)

/-- The marked middle-model vertices ensure that a two-vertex subdivision face maps into one
simplex of the finite segment model. -/
theorem faceBoundarySubdivision_middleSource
    (f : K.Face) (i : ZMod 3)
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i))
    (hcard : u.card = 2)
    (hmid0 : ∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p)
    (hmid1 : ∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ)) :
    ∃ s ∈ (G.replacementArc (K.faceEdge f i)).parameterization.source.simplexes,
      Set.MapsTo (K.faceMiddleSourceAffine (G := G) f i)
        ((K.faceBoundarySubdivision (G := G) f).cellCarrier u)
        ((G.replacementArc (K.faceEdge f i)).parameterization.source.cellCarrier s) := by
  let R := K.faceBoundarySubdivision (G := G) f
  let A := G.replacementArc (K.faceEdge f i)
  let n : ℝ := A.parameterization.length
  let z : Plane → ℝ := fun p ↦ n *
    (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine f i p - 2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have hdelta : 0 ≤ A.exitData.right - A.exitData.left :=
    sub_nonneg.mpr A.exitData.left_lt_right.le
  have hmono {p q : Plane}
      (hpq : K.faceEdgeParameterAffine f i p ≤
        K.faceEdgeParameterAffine f i q) : z p ≤ z q := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine f i p - 2)) ≤
      n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine f i q - 2))
    apply mul_le_mul_of_nonneg_left _ hn.le
    have hr : 4 * K.faceEdgeParameterAffine f i p - 2 ≤
        4 * K.faceEdgeParameterAffine f i q - 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr hdelta
    linarith
  have hzBounds {p : Plane} (hp : p ∈ R.cellCarrier u) :
      z p ∈ Set.Icc 0 n := by
    have ht0 := hmid0 p hp
    have ht1 := hmid1 p hp
    have hr0 : 0 ≤ 4 * K.faceEdgeParameterAffine f i p - 2 := by linarith
    have hr1 : 4 * K.faceEdgeParameterAffine f i p - 2 ≤ 1 := by linarith
    constructor
    · exact mul_nonneg hn.le
        (add_nonneg A.exitData.left_nonneg (mul_nonneg hdelta hr0))
    · calc
        z p ≤ n * 1 := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          have hmul := mul_le_mul_of_nonneg_left hr1 hdelta
          linarith [A.exitData.right_le_one]
        _ = n := mul_one n
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
  have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
  have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
  let a := min (z (R.position p)) (z (R.position q))
  let b := max (z (R.position p)) (z (R.position q))
  have hab : a ≤ b := min_le_max
  have ha : 0 ≤ a := le_min (hzBounds hp).1 (hzBounds hq).1
  have hb : b ≤ n := max_le (hzBounds hp).2 (hzBounds hq).2
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
        change n * A.exitData.left ≤ n *
          (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2))
        have hr := hmid0 (R.position p) hp
        have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2) :=
          mul_nonneg hdelta (by linarith)
        apply mul_le_mul_of_nonneg_left _ hn.le
        linarith
      have hqLower : n * A.exitData.left ≤ z (R.position q) := by
        change n * A.exitData.left ≤ n *
          (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2))
        have hr := hmid0 (R.position q) hq
        have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2) :=
          mul_nonneg hdelta (by linarith)
        apply mul_le_mul_of_nonneg_left _ hn.le
        linarith
      exact hcn.le.trans (le_min hpLower hqLower)
    · have hv0' : A.exitData.left ≤ c / n := le_of_not_gt hv0
      by_cases hv1 : c / n ≤ A.exitData.right
      · have hbreak := K.faceBoundarySubdivision_parameter_side
          (G := G) f i (some (some v)) hu hui
        have hvalue := edgeMiddleSourceScalar_breakpoint A v hv0' hv1
        have hparamBreak : K.faceEdgeParameterAffine f i
            (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) =
              edgeBreakpointParameter A (some (some v)) := by
          change K.faceEdgeParameterAffine f i
            (K.faceEdgeSourcePoint f i
              (edgeBreakpointParameter A (some (some v)))) = _
          rw [K.faceEdgeParameterAffine_sourcePoint]
        have hbreakValue : z
            (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) = c := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i
              (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) - 2)) = c
          rw [hparamBreak]
          simpa only [n, c, edgeBreakpointParameter] using hvalue
        rcases hbreak with hle | hge
        · right
          apply max_le
          · calc
              z (R.position p) ≤ z
                  (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) :=
                hmono (by rw [hparamBreak]; exact hle _ hp)
              _ = c := hbreakValue
          · calc
              z (R.position q) ≤ z
                  (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) :=
                hmono (by rw [hparamBreak]; exact hle _ hq)
              _ = c := hbreakValue
        · left
          apply le_min
          · calc
              c = z (K.faceBreakpointPoint (G := G) f
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position p) :=
                hmono (by rw [hparamBreak]; exact hge _ hp)
          · calc
              c = z (K.faceBreakpointPoint (G := G) f
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position q) :=
                hmono (by rw [hparamBreak]; exact hge _ hq)
      · right
        have hcn : n * A.exitData.right < c := by
          have hc : A.exitData.right < c / n := lt_of_not_ge hv1
          rw [lt_div_iff₀ hn] at hc
          simpa [mul_comm] using hc
        have hpUpper : z (R.position p) ≤ n * A.exitData.right := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2)) ≤
              n * A.exitData.right
          have hr := hmid1 (R.position p) hp
          have hmul := mul_le_mul_of_nonneg_left
            (show 4 * K.faceEdgeParameterAffine f i (R.position p) - 2 ≤ 1 by
              linarith) hdelta
          apply mul_le_mul_of_nonneg_left _ hn.le
          linarith
        have hqUpper : z (R.position q) ≤ n * A.exitData.right := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2)) ≤
              n * A.exitData.right
          have hr := hmid1 (R.position q) hq
          have hmul := mul_le_mul_of_nonneg_left
            (show 4 * K.faceEdgeParameterAffine f i (R.position q) - 2 ≤ 1 by
              linarith) hdelta
          apply mul_le_mul_of_nonneg_left _ hn.le
          linarith
        exact (max_le hpUpper hqUpper).trans hcn.le
  obtain ⟨s, hs, hssegment⟩ :=
    PlaneComplex.exists_face_containing_axis_segment_of_no_vertex
      A.parameterization.source hn.le hab ha hb A.parameterization.source_support
        A.parameterization.source_card_le_two havoid
  let sourceAffine : Plane →ᵃ[ℝ] Plane :=
    K.faceMiddleSourceAffine (G := G) f i
  have hsourceApply (x : Plane) : sourceAffine x = planePoint (z x) 0 := by
    simpa only [sourceAffine, z] using
      K.faceMiddleSourceAffine_apply (G := G) f i x
  have hsourceImage :
      sourceAffine '' R.cellCarrier ({p, q} : Finset R.Vertex) =
        segment ℝ (planePoint a 0) (planePoint b 0) := by
    rw [PlaneComplex.cellCarrier]
    have himage : R.position '' (({p, q} : Finset R.Vertex) : Set R.Vertex) =
        {R.position p, R.position q} := by
      ext x
      simp [eq_comm]
    rw [himage, convexHull_pair, image_segment]
    rw [hsourceApply, hsourceApply]
    rcases le_total (z (R.position p)) (z (R.position q)) with hpzq | hqzp
    · simp [a, b, min_eq_left hpzq, max_eq_right hpzq]
    · rw [segment_symm]
      simp [a, b, min_eq_right hqzp, max_eq_left hqzp]
  refine ⟨s, hs, ?_⟩
  intro x hx
  apply hssegment
  rw [← hsourceImage]
  exact ⟨x, hx, rfl⟩

/-- The canonical face boundary map is affine on every simplex of its finite marked
subdivision. -/
theorem faceBoundaryMap_affineOn_subdivision (f : K.Face) :
    ∀ u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes,
      IsAffineOn (K.faceBoundaryMap (G := G) f)
        ((K.faceBoundarySubdivision (G := G) f).cellCarrier u) := by
  let R := K.faceBoundarySubdivision (G := G) f
  let T := standardTrianglePlaneComplex.oneSkeleton
  intro u hu
  have hsub : R.Subdivides T := K.faceBoundarySubdivision_subdivides (G := G) f
  obtain ⟨s, hs, hus⟩ := hsub.2 u hu
  have hscard : s.card ≤ 2 :=
    standardTrianglePlaneComplex.oneSkeleton_isGraph s hs
  have hucard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face hu hs hscard hus
  have hupos : 0 < u.card := Finset.card_pos.mpr (R.nonempty_of_mem u hu)
  have huCases : u.card = 1 ∨ u.card = 2 := by omega
  rcases huCases with huone | hutwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huone
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.faceBoundaryMap (G := G) f (R.position v))
    refine ⟨g, ?_⟩
    intro p hp
    have hpEq : p = R.position v := by
      simpa [PlaneComplex.cellCarrier] using hp
    subst p
    rfl
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hutwo
    have hspos : 0 < s.card := Finset.card_pos.mpr (T.nonempty_of_mem s hs)
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
      have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
      have hpEq : R.position p = T.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hp
      have hqEq : R.position q = T.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hq
      exact (hpq (R.position_injective (hpEq.trans hqEq.symm))).elim
    · obtain ⟨i, hsi⟩ :=
        IntrinsicTwoComplex.exists_faceStandardEdge_of_standardBoundaryEdge hstwo
      have hui : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          standardTrianglePlaneComplex.cellCarrier
            (IntrinsicTwoComplex.faceStandardEdge i) := by
        intro x hx
        have hx' := hus hx
        rw [hsi, IntrinsicTwoComplex.standardFaceEdgeFace_cellCarrier] at hx'
        exact hx'
      rcases K.faceBoundarySubdivision_piece (G := G) f i hu hui with
          hleft | hmiddle | hright
      · exact K.faceBoundaryMap_affineOn_left (G := G) f i hui hleft
      · apply K.faceBoundaryMap_affineOn_middle (G := G) f i
          hui hmiddle.1 hmiddle.2
        exact K.faceBoundarySubdivision_middleSource (G := G) f i hu hui
          (by simp [hpq]) hmiddle.1 hmiddle.2
      · exact K.faceBoundaryMap_affineOn_right (G := G) f i hui hright

/-- The coherent standard-triangle boundary map is genuinely PL on the polygonal frontier. -/
theorem faceBoundaryMap_isPLOnSet (f : K.Face) :
    IsPLOnSet (frontier standardFaceRegion)
      (K.faceBoundaryMap (G := G) f) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let R := K.faceBoundarySubdivision (G := G) f
  refine ⟨T, ?_, R, K.faceBoundarySubdivision_subdivides (G := G) f,
    K.faceBoundaryMap_affineOn_subdivision (G := G) f⟩
  calc
    T.support = standardTriangleCircle.carrier :=
      IntrinsicTwoComplex.standardTriangle_oneSkeleton_support
    _ = frontier standardFaceRegion := by
      rw [standardTriangleCircle_carrier]
      simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_05
/- END ClassificationOfSurfaces.Moise.LocallyFiniteFaceExtension -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension | 1779256720825946af3550d838b88053d6d036a1226141847186112378fc7509 -/
section schottkyclassification15_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Cellwise assembly of intrinsic PL face fillings

The fillings supplied by `IntrinsicFaceFilling` use one standard triangle for every maximal
intrinsic face.  This file transports them back to the canonical barycentric realization and
glues the finite family.  Coherence is proved from the common global one-skeleton replacement;
it is not stored as an extra compatibility assumption.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

namespace FacePLFilling

/-- A standard-triangle filling transported to its intrinsic closed face. -/
noncomputable def intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.ClosedFace t → Plane :=
  fun x ↦ F.map (K.facePlaneHomeomorph t x).1

theorem continuous_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Continuous F.intrinsicMap := by
  have hF : Continuous (fun p : standardFaceRegion ↦ F.map p.1) :=
    continuousOn_iff_continuous_restrict.mp F.continuousOn
  exact hF.comp (K.facePlaneHomeomorph t).continuous

theorem injective_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Function.Injective F.intrinsicMap := by
  intro x y hxy
  apply (K.facePlaneHomeomorph t).injective
  apply Subtype.ext
  apply F.injectiveOn (K.facePlaneHomeomorph t x).2 (K.facePlaneHomeomorph t y).2
  exact hxy

theorem range_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Set.range F.intrinsicMap =
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
  rw [← F.image_eq]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(K.facePlaneHomeomorph t x).1, (K.facePlaneHomeomorph t x).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    let q : standardFaceRegion := ⟨p, hp⟩
    exact ⟨(K.facePlaneHomeomorph t).symm q, by
      change F.map (K.facePlaneHomeomorph t ((K.facePlaneHomeomorph t).symm q)).1 = F.map p
      rw [(K.facePlaneHomeomorph t).apply_symm_apply]⟩

/-- The relative interior of a filled intrinsic face maps to the bounded complementary region. -/
theorem mapsTo_interiorRegion {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Set.MapsTo F.map (interior standardFaceRegion)
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion := by
  intro p hp
  have hpRegion : p ∈ standardFaceRegion := interior_subset hp
  have hclosed : F.map p ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
    rw [← F.image_eq]
    exact ⟨p, hpRegion, rfl⟩
  rw [(K.facePolygonalCircle t).closedRegion_eq_union] at hclosed
  rcases hclosed with hbounded | hcarrier
  · exact hbounded
  · rw [← K.faceBoundaryMap_image_polygon t] at hcarrier
    obtain ⟨q, hq, hqmap⟩ := hcarrier
    have hmapEq : F.map p = F.map q := by
      rw [F.eqOn_boundary hq]
      exact hqmap.symm
    have hpq : p = q := F.injectiveOn hpRegion
      (standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hq) hmapEq
    subst q
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hp hq)

end FacePLFilling

private theorem exists_edge_between_small_carriers
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    ∃ e : K.Edge, t.1 ∩ s ⊆ e.1 ∧ e.1 ⊆ t.1 ∧ x ∈ K.faceCarrier e.1 := by
  classical
  have hxInter : x ∈ K.faceCarrier (t.1 ∩ s) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hxt, hxs⟩
  have hInterNonempty : (t.1 ∩ s).Nonempty := by
    by_contra h
    have hempty : t.1 ∩ s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, K.faceCarrier_empty] at hxInter
    exact hxInter
  have hInterCard : (t.1 ∩ s).card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hsCard
  have hTwoLe : 2 ≤ t.1.card := by
    rw [K.faces_card t.1 t.2]
    norm_num
  obtain ⟨e, hInterE, hEt, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq Finset.inter_subset_left hInterCard hTwoLe
  have heEdges : e ∈ K.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨hEt, hEcard⟩⟩
  let E : K.Edge := ⟨e, heEdges⟩
  refine ⟨E, hInterE, hEt, ?_⟩
  intro v hvE
  apply hxInter v
  intro hvInter
  exact hvE (hInterE hvInter)

/-- A point of a face which is also carried by a set of at most two vertices lies on one of
that face's three intrinsic edges. -/
theorem exists_faceEdge_of_mem_small_carrier
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    ∃ i : ZMod 3, x ∈ K.faceCarrier (K.faceEdge t i).1 := by
  obtain ⟨e, -, het, hxe⟩ := K.exists_edge_between_small_carriers t hsCard hxt hxs
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset t e het
  exact ⟨i, by simpa only [hi] using hxe⟩

private theorem faceChart_mem_frontier_of_mem_small_carrier
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  obtain ⟨i, hxi⟩ := K.exists_faceEdge_of_mem_small_carrier t hsCard hxt hxs
  have hpSide : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← K.facePlaneHomeomorph_image_edge t i]
    exact ⟨⟨x, hxt⟩, hxi, rfl⟩
  have hpCarrier : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.carrier :=
    Set.mem_iUnion.mpr ⟨i, hpSide⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- The standard coordinate of a point shared by two distinct faces lies on the standard
triangle frontier. -/
theorem faceChart_mem_frontier_of_mem_distinct_faces
    {t u : K.Face} (htu : t ≠ u) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  classical
  have hInterCard : (t.1 ∩ u.1).card ≤ 2 := by
    by_contra h
    have hge : 3 ≤ (t.1 ∩ u.1).card := by omega
    have hle : (t.1 ∩ u.1).card ≤ 3 := by
      simpa [K.faces_card t.1 t.2] using
        Finset.card_le_card (Finset.inter_subset_left : t.1 ∩ u.1 ⊆ t.1)
    have hcard : (t.1 ∩ u.1).card = 3 := by omega
    have hinterT : t.1 ∩ u.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.faces_card t.1 t.2, hcard])
    have htuSub : t.1 ⊆ u.1 := by
      rw [← hinterT]
      exact Finset.inter_subset_right
    have htuEq : t.1 = u.1 :=
      Finset.eq_of_subset_of_card_le htuSub (by
        rw [K.faces_card t.1 t.2, K.faces_card u.1 u.2])
    exact htu (Subtype.ext htuEq)
  have hxInter : x ∈ K.faceCarrier (t.1 ∩ u.1) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hxt, hxu⟩
  exact K.faceChart_mem_frontier_of_mem_small_carrier t hInterCard hxt hxInter

/-- A point shared by distinct maximal intrinsic faces belongs to the global one-skeleton. -/
theorem mem_oneSkeleton_of_mem_distinct_faces
    {t u : K.Face} (htu : t ≠ u) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    x ∈ K.oneSkeleton := by
  have hp := K.faceChart_mem_frontier_of_mem_distinct_faces htu hxt hxu
  have hpCarrier : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  have hxi := K.facePlaneHomeomorph_symm_mem_edge t i hi
  have heq : ((K.facePlaneHomeomorph t).symm
      ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
        standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩).1 = x := by
    rw [show (⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
        standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩ :
      standardFaceRegion) = K.facePlaneHomeomorph t ⟨x, hxt⟩ by rfl,
      (K.facePlaneHomeomorph t).symm_apply_apply]
  exact ⟨K.faceEdge t i, by simpa only [heq] using hxi⟩

/-- Lifting the standard coordinate of an intrinsic boundary point recovers that point. -/
theorem faceBoundaryLift_facePlaneHomeomorph
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion) :
    (K.faceBoundaryLift t
      ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩).1 = x := by
  change ((K.facePlaneHomeomorph t).symm
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, _⟩).1 = x
  have hsubtype :
      (⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
          standardFaceBoundary_mem_region
            ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩⟩ :
        standardFaceRegion) = K.facePlaneHomeomorph t ⟨x, hxt⟩ := by
    rfl
  rw [hsubtype, (K.facePlaneHomeomorph t).symm_apply_apply]

theorem faceBoundaryLift_mem_faceCarrier (t : K.Face) (p : StandardFaceBoundary) :
    (K.faceBoundaryLift t p).1 ∈ K.faceCarrier t.1 := by
  change ((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).1 ∈ K.faceCarrier t.1
  exact ((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).2

/-- The transported fillings of two faces agree at every point of their overlap. -/
theorem facePLFilling_intrinsicMap_eq
    (t u : K.Face) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).intrinsicMap
        ⟨x, hxt⟩ =
      (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).intrinsicMap
        ⟨x, hxu⟩ := by
  by_cases htu : t = u
  · subst u
    rfl
  let p : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces htu hxt hxu⟩
  let q : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces (Ne.symm htu) hxu hxt⟩
  apply K.facePLFilling_eq_of_boundaryLift_eq (t := t) (u := u) (p := p) (q := q)
  rw [K.faceBoundaryLift_facePlaneHomeomorph t hxt p.2,
    K.faceBoundaryLift_facePlaneHomeomorph u hxu q.2]

/-- A chosen maximal face containing a point of the canonical realization. -/
noncomputable def containingFace (x : K.realization) : K.Face :=
  ⟨Classical.choose x.2.2, (Classical.choose_spec x.2.2).1⟩

theorem mem_faceCarrier_containingFace (x : K.realization) :
    x ∈ K.faceCarrier (K.containingFace x).1 :=
  (Classical.choose_spec x.2.2).2

/-- The finite family of intrinsic face fillings, glued into one map. -/
noncomputable def cellwisePLFillingMap (x : K.realization) : Plane :=
  (K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) (K.containingFace x)).intrinsicMap
    ⟨x, K.mem_faceCarrier_containingFace x⟩

/-- The glued map restricts to the chosen certified filling on every maximal face. -/
theorem cellwisePLFillingMap_eqOn_face (t : K.Face) (x : K.realization)
    (hxt : x ∈ K.faceCarrier t.1) :
    K.cellwisePLFillingMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      (K.facePLFilling
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).intrinsicMap ⟨x, hxt⟩ := by
  exact K.facePLFilling_intrinsicMap_eq (K.containingFace x) t
    (K.mem_faceCarrier_containingFace x) hxt

/-- The finite cellwise filling is continuous on the whole intrinsic realization. -/
theorem continuous_cellwisePLFillingMap :
    Continuous (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  let carriers : K.Face → Set K.realization := fun t ↦ K.faceCarrier t.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ t : K.Face, IsClosed (carriers t) := fun t ↦ K.faceCarrier_closed t.1
  have hlocal : ∀ t : K.Face,
      ContinuousOn (K.cellwisePLFillingMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)) (carriers t) := by
    intro t
    rw [continuousOn_iff_continuous_restrict]
    have hF := (K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).continuous_intrinsicMap
    convert hF using 1
    funext x
    exact K.cellwisePLFillingMap_eqOn_face t x.1 x.2
  exact hfinite.continuous K.realization_eq_iUnion_faceCarrier.symm hclosed hlocal

/-- On the global intrinsic one-skeleton, the cellwise filling is exactly the previously
constructed simultaneous graph replacement. -/
theorem cellwisePLFillingMap_eq_graphReplacement
    {x : K.realization} (hx : x ∈ K.oneSkeleton) :
    K.cellwisePLFillingMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      K.graphReplacementMap hcont hinj D C x := by
  obtain ⟨e, hxe⟩ := hx
  let t := K.containingFace x
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion :=
    K.faceChart_mem_frontier_of_mem_small_carrier t
      (by rw [K.card_of_mem_edges e.2]) hxt hxe
  rw [K.cellwisePLFillingMap_eqOn_face t x hxt]
  change (K.facePLFilling t).map (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 = _
  rw [(K.facePLFilling t).eqOn_boundary hp, K.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

/-- The original embedding written in the standard coordinates of one intrinsic face.  Values
outside the standard closed triangle are irrelevant. -/
noncomputable def faceOriginalMap (t : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ standardFaceRegion then
    h ((K.facePlaneHomeomorph t).symm ⟨p, hp⟩).1
  else 0

@[simp] theorem faceOriginalMap_apply (t : K.Face) (p : standardFaceRegion) :
    K.faceOriginalMap (h := h) t p.1 =
      h ((K.facePlaneHomeomorph t).symm p).1 := by
  simp [faceOriginalMap, p.2]

theorem continuousOn_faceOriginalMap (hcont : Continuous h) (t : K.Face) :
    ContinuousOn (K.faceOriginalMap (h := h) t) standardFaceRegion := by
  rw [continuousOn_iff_continuous_restrict]
  convert hcont.comp
    (continuous_subtype_val.comp (K.facePlaneHomeomorph t).symm.continuous) using 1
  funext p
  exact K.faceOriginalMap_apply t p

theorem faceOriginalMap_mem_face_image (t : K.Face) (p : standardFaceRegion) :
    K.faceOriginalMap (h := h) t p.1 ∈ h '' K.faceCarrier t.1 := by
  refine ⟨((K.facePlaneHomeomorph t).symm p).1,
    ((K.facePlaneHomeomorph t).symm p).2, ?_⟩
  exact (K.faceOriginalMap_apply t p).symm

/-- A one-skeleton point lying in a face has a standard coordinate on that face's frontier. -/
theorem faceChart_mem_frontier_of_mem_oneSkeleton
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hx : x ∈ K.oneSkeleton) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  obtain ⟨e, hxe⟩ := hx
  exact K.faceChart_mem_frontier_of_mem_small_carrier t
    (by rw [K.card_of_mem_edges e.2]) hxt hxe

/-- Conversely, the inverse face chart takes the standard frontier into the global
one-skeleton. -/
theorem mem_oneSkeleton_of_faceChart_mem_frontier
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion) :
    x ∈ K.oneSkeleton := by
  let p : StandardFaceBoundary := ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩
  have hlift := (K.faceBoundaryLift t p).2
  rw [K.faceBoundaryLift_facePlaneHomeomorph t hxt hp] at hlift
  exact hlift

/-- The graph-side condition needed for injective cellwise assembly: the simultaneous global
one-skeleton replacement avoids the bounded interior selected for every face. -/
def FaceFillingsGraphAvoidInteriors : Prop :=
  ∀ t : K.Face,
    Disjoint
      (K.graphReplacementMap hcont hinj D C '' K.oneSkeleton)
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion

/-- The finite vertex-side condition used to establish graph-side compatibility. -/
def FaceFillingsVerticesAvoidClosedRegions : Prop :=
  ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
    h (K.vertexPoint v) ∉
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion

/-- A finite embedded intrinsic two-complex has one positive separation radius for every
maximal face and every used vertex not belonging to that face. -/
theorem exists_uniform_vertex_face_separation
    (hcont : Continuous h) (hinj : Function.Injective h) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
        Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
          (Metric.cthickening r (h '' K.faceCarrier t.1)) := by
  classical
  let I := Option (K.Face × K.UsedVertex)
  let P : I → ℝ → Prop
    | none, _ => True
    | some (t, v), r =>
        v.1 ∈ t.1 ∨
          Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
            (Metric.cthickening r (h '' K.faceCarrier t.1))
  have hlocal : ∀ i : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → P i r := by
    intro i
    rcases i with _ | ⟨t, v⟩
    · exact ⟨1, by norm_num, fun _ _ _ ↦ trivial⟩
    · by_cases hvt : v.1 ∈ t.1
      · exact ⟨1, by norm_num, fun _ _ _ ↦ Or.inl hvt⟩
      · have hdisjoint : Disjoint ({h (K.vertexPoint v)} : Set Plane)
            (h '' K.faceCarrier t.1) := by
          rw [Set.disjoint_singleton_left]
          rintro ⟨x, hxt, hvx⟩
          have hxv : x = K.vertexPoint v := hinj hvx
          rw [hxv] at hxt
          exact hvt ((K.vertexPoint_mem_faceCarrier_iff v t.1).mp hxt)
        have hcompact : IsCompact (h '' K.faceCarrier t.1) :=
          (K.faceCarrier_closed t.1).isCompact.image hcont
        obtain ⟨ε, hε, hthick⟩ := hdisjoint.exists_thickenings
          isCompact_singleton hcompact.isClosed
        refine ⟨ε, hε, fun r hr hrε ↦ Or.inr ?_⟩
        exact hthick.mono
          ((Metric.closedBall_subset_cthickening (Set.mem_singleton _) r).trans
            (Metric.cthickening_subset_thickening' hε hrε _))
          (Metric.cthickening_subset_thickening' hε hrε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨r, hr, ?_⟩
  intro t v hvt
  have hP := huniform (some (t, v)) r hr (half_lt_self hε)
  rcases hP with hmem | hdis
  · exact (hvt hmem).elim
  · exact hdis

/-- Quantitative closeness and vertex-to-face separation put every nonincident vertex on the
unbounded side of every replacement polygon. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_close
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
      Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
        (Metric.cthickening r (h '' K.faceCarrier t.1)))
    (hclose : ∀ x ∈ K.oneSkeleton,
      dist (K.graphReplacementMap hcont hinj D C x) (h x) < r) :
    K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  intro t v hvt
  let b := K.faceBoundaryMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let hface := K.faceOriginalMap (h := h) t
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap t
  have hhface : ContinuousOn hface standardFaceRegion :=
    K.continuousOn_faceOriginalMap hcont t
  have hbclose : ∀ p ∈ frontier standardFaceRegion, dist (b p) (hface p) < r := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    have hq := hclose (K.faceBoundaryLift t q).1 (K.faceBoundaryLift t q).2
    rw [← K.faceBoundaryMap_apply t q] at hq
    have horiginal : hface p = h (K.faceBoundaryLift t q).1 := by
      change K.faceOriginalMap (h := h) t p = _
      rw [K.faceOriginalMap_apply t
        ⟨p, standardFaceBoundary_mem_region q⟩]
      rfl
    change dist (K.faceBoundaryMap t p) (K.faceOriginalMap (h := h) t p) < r
    have horiginal' : K.faceOriginalMap (h := h) t p =
        h (K.faceBoundaryLift t q).1 := horiginal
    rw [horiginal']
    exact hq
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed hr hbcont hhface hbclose
  have hvAvoid : h (K.vertexPoint v) ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : h (K.vertexPoint v) ∈
        Metric.closedBall (h (K.vertexPoint v)) r :=
      Metric.mem_closedBall_self hr.le
    have hFthick : F p ∈ Metric.cthickening r (h '' K.faceCarrier t.1) := by
      apply Metric.mem_cthickening_of_dist_le (F p) (hface p) r
        (h '' K.faceCarrier t.1)
      · exact K.faceOriginalMap_mem_face_image t ⟨p, hp⟩
      · exact hFclose p hp
    exact Set.disjoint_left.mp (hsep t v hvt) hvBall (hFp ▸ hFthick)
  have hvExterior : h (K.vertexPoint v) ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).exteriorRegion := by
    apply (K.facePolygonalCircle t).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn t) (K.faceBoundaryMap_image_polygon t)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle t).disjoint_closedRegion_exteriorRegion hvClosed hvExterior

/-- Every filled face boundary is part of the single global replacement graph. -/
theorem facePolygonalCircle_carrier_subset_graphReplacement (t : K.Face) :
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier ⊆
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon t] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  let q : StandardFaceBoundary := ⟨p, hp⟩
  exact ⟨(K.faceBoundaryLift t q).1, (K.faceBoundaryLift t q).2,
    (K.faceBoundaryMap_apply t q).symm⟩

/-- A replacement-graph point can lie on the polygon of a face only when its intrinsic source
lies in that face.  This is the exact-carrier consequence of boundary coherence and injectivity
of the simultaneous graph replacement. -/
theorem mem_faceCarrier_of_graphReplacement_mem_facePolygonalCircle
    (t : K.Face) {x : K.realization} (hx : x ∈ K.oneSkeleton)
    (himage : K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier) :
    x ∈ K.faceCarrier t.1 := by
  rw [← K.faceBoundaryMap_image_polygon t] at himage
  obtain ⟨p, hp, hpEq⟩ := himage
  let q : StandardFaceBoundary := ⟨p, hp⟩
  have hgraphEq : K.graphReplacementMap hcont hinj D C x =
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 := by
    rw [← K.faceBoundaryMap_apply t q]
    exact hpEq.symm
  have hxEq := K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
    hx (K.faceBoundaryLift t q).2 hgraphEq
  rw [hxEq]
  exact K.faceBoundaryLift_mem_faceCarrier t q

/-- A point of a face which lies on the one-skeleton maps to that face's polygonal boundary. -/
theorem graphReplacement_mem_facePolygonalCircle
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hx : x ∈ K.oneSkeleton) :
    K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton t hxt hx
  rw [← K.faceBoundaryMap_image_polygon t]
  refine ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp, ?_⟩
  rw [K.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

/-- Vertex avoidance places every vertex not incident to a face in the unbounded component of
that face's replacement polygon. -/
theorem graphReplacement_vertex_mem_exterior
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (t : K.Face) (v : K.UsedVertex) (hvt : v.1 ∉ t.1) :
    K.graphReplacementMap hcont hinj D C (K.vertexPoint v) ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).exteriorRegion := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  rw [K.graphReplacementMap_vertex hcont hinj D C]
  have hnotClosed := hvertices t v hvt
  have hnotInterior : h (K.vertexPoint v) ∉ J.interiorRegion := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inl hv
  have hnotCarrier : h (K.vertexPoint v) ∉ J.carrier := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inr hv
  have hoff : h (K.vertexPoint v) ∈ J.carrierᶜ := hnotCarrier
  rw [← J.interior_union_exterior] at hoff
  exact hoff.resolve_left hnotInterior

/-- Moise's finite vertex condition propagates along every intrinsic edge.  Thus the whole
simultaneous replacement graph avoids the bounded polygonal region selected for each face. -/
theorem faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  intro t
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  have hinteriorCarrier : Disjoint J.interiorRegion J.carrier := by
    rw [← J.interior_closedRegion, ← J.frontier_closedRegion]
    exact disjoint_interior_frontier
  rw [Set.disjoint_left]
  rintro _ ⟨x, hxOne, rfl⟩ hxInterior
  obtain ⟨e, hxe⟩ := hxOne
  by_cases het : e.1 ⊆ t.1
  · have hxt : x ∈ K.faceCarrier t.1 := by
      intro v hvt
      exact hxe v (fun hve ↦ hvt (het hve))
    exact Set.disjoint_left.mp hinteriorCarrier hxInterior
      (K.graphReplacement_mem_facePolygonalCircle t hxt ⟨e, hxe⟩)
  let I := Set.Icc (0 : ℝ) 1
  let z0 : I := ⟨0, by simp [I]⟩
  let z1 : I := ⟨1, by simp [I]⟩
  let gpath : I → Plane := fun s ↦
    K.graphReplacementMap hcont hinj D C (K.edgePath e s)
  have hpathCarrier (s : I) : K.edgePath e s ∈ K.faceCarrier e.1 := by
    rw [← K.range_edgePath e]
    exact ⟨s, rfl⟩
  have hpathOne (s : I) : K.edgePath e s ∈ K.oneSkeleton :=
    ⟨e, hpathCarrier s⟩
  have hgpath : Continuous gpath := by
    have hgraph := K.continuousOn_graphReplacementMap_faceCarrier hcont hinj D C e
    simpa only [gpath, Function.comp_def] using
      hgraph.comp_continuous (K.continuous_edgePath e) hpathCarrier
  have hoffCarrier {A : Set I}
      (houtside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1) :
      Set.MapsTo gpath A J.carrierᶜ := by
    intro s hs hcarrier
    exact houtside s hs
      (K.mem_faceCarrier_of_graphReplacement_mem_facePolygonalCircle t
        (hpathOne s) hcarrier)
  let r : I := K.edgeParameter e x hxe
  have hxPath : K.edgePath e r = x := K.edgePath_edgeParameter e x hxe
  have hsharedImpossible (hxt : x ∈ K.faceCarrier t.1) : False := by
    exact Set.disjoint_left.mp hinteriorCarrier hxInterior
      (K.graphReplacement_mem_facePolygonalCircle t hxt ⟨e, hxe⟩)
  by_cases hfirst : K.edgeFirst e ∈ t.1
  · have hsecond : K.edgeSecond e ∉ t.1 := by
      intro hsecond
      apply het
      rw [K.edge_eq_pair e]
      exact Finset.insert_subset_iff.mpr
        ⟨hfirst, Finset.singleton_subset_iff.mpr hsecond⟩
    by_cases hr0 : r.1 = 0
    · apply hsharedImpossible
      have hxFirst : x = K.edgeFirstPoint e := by
        calc
          x = K.edgePath e r := hxPath.symm
          _ = K.edgePath e z0 := by congr 1; exact Subtype.ext hr0
          _ = K.edgeFirstPoint e := K.edgePath_zero e
      rw [hxFirst, ← K.vertexPoint_edgeFirstUsed e]
      exact (K.vertexPoint_mem_faceCarrier_iff (K.edgeFirstUsed e) t.1).mpr hfirst
    · let A : Set I := Set.Ioc z0 z1
      have hApreconnected : IsPreconnected A := isPreconnected_Ioc
      have hAoutside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1 := by
        intro s hs hsFace
        have hzero := hsFace (K.edgeSecond e) hsecond
        rw [K.edgePath_apply_second] at hzero
        have hspos : 0 < s.1 := by
          exact_mod_cast hs.1
        exact (ne_of_gt hspos) hzero
      have hz1Exterior : gpath z1 ∈ J.exteriorRegion := by
        have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
          (K.edgeSecondUsed e) hsecond
        simpa only [gpath, z1, K.edgePath_one, K.vertexPoint_edgeSecondUsed] using hvertex
      have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected hApreconnected hgpath.continuousOn
          (hoffCarrier hAoutside) ⟨z1, by simp [A, z0, z1], hz1Exterior⟩
      have hrA : r ∈ A := by
        constructor
        · change (0 : ℝ) < r.1
          exact lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        · change r.1 ≤ (1 : ℝ)
          exact r.2.2
      have hrExterior := hAExterior hrA
      change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
        J.exteriorRegion at hrExterior
      rw [hxPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior
  · by_cases hsecond : K.edgeSecond e ∈ t.1
    · by_cases hr1 : r.1 = 1
      · apply hsharedImpossible
        have hxSecond : x = K.edgeSecondPoint e := by
          calc
            x = K.edgePath e r := hxPath.symm
            _ = K.edgePath e z1 := by congr 1; exact Subtype.ext hr1
            _ = K.edgeSecondPoint e := K.edgePath_one e
        rw [hxSecond, ← K.vertexPoint_edgeSecondUsed e]
        exact (K.vertexPoint_mem_faceCarrier_iff (K.edgeSecondUsed e) t.1).mpr hsecond
      · let A : Set I := Set.Ico z0 z1
        have hApreconnected : IsPreconnected A := isPreconnected_Ico
        have hAoutside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1 := by
          intro s hs hsFace
          have hzero := hsFace (K.edgeFirst e) hfirst
          rw [K.edgePath_apply_first] at hzero
          have hslt : s.1 < 1 := by
            exact_mod_cast hs.2
          linarith
        have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
          have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
            (K.edgeFirstUsed e) hfirst
          simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hvertex
        have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
          J.mapsTo_exteriorRegion_of_isPreconnected hApreconnected hgpath.continuousOn
            (hoffCarrier hAoutside) ⟨z0, by simp [A, z0, z1], hz0Exterior⟩
        have hrA : r ∈ A := by
          constructor
          · change (0 : ℝ) ≤ r.1
            exact r.2.1
          · change r.1 < (1 : ℝ)
            exact lt_of_le_of_ne r.2.2 hr1
        have hrExterior := hAExterior hrA
        change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
          J.exteriorRegion at hrExterior
        rw [hxPath] at hrExterior
        exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior
    · have hAllOutside : ∀ s : I, K.edgePath e s ∉ K.faceCarrier t.1 := by
        intro s hsFace
        have hzeroFirst := hsFace (K.edgeFirst e) hfirst
        have hzeroSecond := hsFace (K.edgeSecond e) hsecond
        rw [K.edgePath_apply_first] at hzeroFirst
        rw [K.edgePath_apply_second] at hzeroSecond
        linarith
      have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
        have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
          (K.edgeFirstUsed e) hfirst
        simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hvertex
      have hAllExterior : Set.MapsTo gpath Set.univ J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_univ hgpath.continuousOn
          (hoffCarrier fun s _ ↦ hAllOutside s) ⟨z0, Set.mem_univ _, hz0Exterior⟩
      have hrExterior := hAllExterior (Set.mem_univ r)
      change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
        J.exteriorRegion at hrExterior
      rw [hxPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior

/-- Quantitative control of the cellwise filling.  If the original map oscillates by less than
`η` on every face and its replacement graph is `ρ`-close, the whole filled face is contained in
the closed ball of radius `η + ρ` about the original value. -/
theorem cellwisePLFillingMap_dist_le
    {η ρ : ℝ}
    (hsmall : ∀ t : K.Face, ∀ x ∈ K.faceCarrier t.1,
      ∀ y ∈ K.faceCarrier t.1, dist (h x) (h y) < η)
    (hclose : ∀ x ∈ K.oneSkeleton,
      dist (K.graphReplacementMap hcont hinj D C x) (h x) < ρ)
    (x : K.realization) :
    dist (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x) (h x) ≤ η + ρ := by
  let t := K.containingFace x
  let F := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hcarrierBall : J.carrier ⊆ Metric.closedBall (h x) (η + ρ) := by
    intro y hy
    rw [← K.faceBoundaryMap_image_polygon t] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    let q : StandardFaceBoundary := ⟨p, hp⟩
    let z : K.realization := (K.faceBoundaryLift t q).1
    have hzOne : z ∈ K.oneSkeleton := (K.faceBoundaryLift t q).2
    have hzFace : z ∈ K.faceCarrier t.1 := K.faceBoundaryLift_mem_faceCarrier t q
    have hzClose := hclose z hzOne
    have hxzSmall := hsmall t x hxt z hzFace
    rw [K.faceBoundaryMap_apply t q]
    rw [Metric.mem_closedBall]
    calc
      dist (K.graphReplacementMap hcont hinj D C z) (h x) ≤
          dist (K.graphReplacementMap hcont hinj D C z) (h z) +
            dist (h z) (h x) := dist_triangle _ _ _
      _ ≤ ρ + η := (add_lt_add hzClose
        (by simpa [dist_comm] using hxzSmall)).le
      _ = η + ρ := add_comm _ _
  have hmapClosed : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x ∈ J.closedRegion := by
    rw [K.cellwisePLFillingMap_eqOn_face t x hxt]
    rw [← F.range_intrinsicMap]
    exact ⟨⟨x, hxt⟩, rfl⟩
  exact Metric.mem_closedBall.mp
    (J.closedRegion_subset_closedBall_of_carrier_subset hcarrierBall hmapClosed)

/-- Under graph-side compatibility, bounded interiors selected for distinct intrinsic faces are
disjoint. -/
theorem disjoint_facePolygonalCircle_interiors
    (hside : K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (t u : K.Face) (htu : t ≠ u) :
    Disjoint
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).interiorRegion := by
  classical
  have hnotSubset : ¬u.1 ⊆ t.1 := by
    intro hsub
    have heq : u.1 = t.1 := Finset.eq_of_subset_of_card_le hsub (by
      rw [K.faces_card u.1 u.2, K.faces_card t.1 t.2])
    exact htu (Subtype.ext heq.symm)
  obtain ⟨w, hwu, hwnt⟩ := Finset.not_subset.mp hnotSubset
  let v : K.UsedVertex := ⟨w, u.1, u.2, hwu⟩
  let x : K.realization := K.vertexPoint v
  have hxu : x ∈ K.faceCarrier u.1 := (K.vertexPoint_mem_faceCarrier_iff v u.1).mpr hwu
  have hxOne : x ∈ K.oneSkeleton := by
    obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem u hwu
    let e : K.Edge := K.faceEdge u i
    apply K.faceCarrier_edge_subset_oneSkeleton e
    apply (K.vertexPoint_mem_faceCarrier_iff v e.1).mpr
    change w ∈ (K.faceEdge u i).1
    rw [K.faceEdge_val, ← hi]
    simp
  have hpU : K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).carrier := by
    have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton u hxu hxOne
    rw [← K.faceBoundaryMap_image_polygon u]
    refine ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1, hp, ?_⟩
    rw [K.faceBoundaryMap_apply u
      ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1, hp⟩,
      K.faceBoundaryLift_facePlaneHomeomorph u hxu hp]
  have hpNotT : K.graphReplacementMap hcont hinj D C x ∉
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
    intro hpT
    rw [← K.faceBoundaryMap_image_polygon t] at hpT
    obtain ⟨q, hq, hqEq⟩ := hpT
    let q' : StandardFaceBoundary := ⟨q, hq⟩
    have hgraphEq : K.graphReplacementMap hcont hinj D C x =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q').1 := by
      rw [← K.faceBoundaryMap_apply t q']
      exact hqEq.symm
    have hxLift := K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
      hxOne (K.faceBoundaryLift t q').2 hgraphEq
    have hxt : x ∈ K.faceCarrier t.1 := by
      rw [hxLift]
      exact K.faceBoundaryLift_mem_faceCarrier t q'
    exact hwnt ((K.vertexPoint_mem_faceCarrier_iff v t.1).mp hxt)
  apply (K.facePolygonalCircle t).disjoint_interiorRegion_of_boundary_avoidance
    (K.facePolygonalCircle u)
  · exact (hside u).mono_left (K.facePolygonalCircle_carrier_subset_graphReplacement t)
  · exact (hside t).mono_left (K.facePolygonalCircle_carrier_subset_graphReplacement u)
  · exact ⟨K.graphReplacementMap hcont hinj D C x, hpU, hpNotT⟩

/-- Once the global replacement graph avoids every selected face interior, the coherent
cellwise filling is injective. -/
theorem injective_cellwisePLFillingMap
    (hside : K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    Function.Injective (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  intro x y hxy
  let t := K.containingFace x
  let u := K.containingFace y
  let Ft := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let Fu := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) u
  let Jt := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let Ju := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) u
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hyu : y ∈ K.faceCarrier u.1 := K.mem_faceCarrier_containingFace y
  have hmapX : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      Ft.intrinsicMap ⟨x, hxt⟩ :=
    K.cellwisePLFillingMap_eqOn_face t x hxt
  have hmapY : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) y =
      Fu.intrinsicMap ⟨y, hyu⟩ :=
    K.cellwisePLFillingMap_eqOn_face u y hyu
  have hlocalEq : Ft.intrinsicMap ⟨x, hxt⟩ = Fu.intrinsicMap ⟨y, hyu⟩ :=
    hmapX.symm.trans (hxy.trans hmapY)
  by_cases htu : t = u
  · have hyt : y ∈ K.faceCarrier t.1 := by
      rw [htu]
      exact hyu
    have hyCompat : Ft.intrinsicMap ⟨y, hyt⟩ =
        Fu.intrinsicMap ⟨y, hyu⟩ :=
      K.facePLFilling_intrinsicMap_eq t u hyt hyu
    have hlocalEq' : Ft.intrinsicMap ⟨x, hxt⟩ = Ft.intrinsicMap ⟨y, hyt⟩ := by
      exact hlocalEq.trans hyCompat.symm
    exact congrArg Subtype.val (Ft.injective_intrinsicMap hlocalEq')
  let p : Plane := (K.facePlaneHomeomorph t ⟨x, hxt⟩).1
  let q : Plane := (K.facePlaneHomeomorph u ⟨y, hyu⟩).1
  have hpqMap : Ft.map p = Fu.map q := hlocalEq
  by_cases hpInt : p ∈ interior standardFaceRegion
  · have hpx : Ft.map p ∈ Jt.interiorRegion := Ft.mapsTo_interiorRegion hpInt
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion := Fu.mapsTo_interiorRegion hqInt
      exact False.elim (Set.disjoint_left.mp
        (K.disjoint_facePolygonalCircle_interiors hside t u htu) hpx
        (by rw [show Ft.map p = Fu.map q from hlocalEq]
            exact hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      have hqyGraph : Fu.map q ∈
          K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
        refine ⟨y, hyOne, ?_⟩
        calc
          K.graphReplacementMap hcont hinj D C y =
              K.cellwisePLFillingMap
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) y :=
            (K.cellwisePLFillingMap_eq_graphReplacement hyOne).symm
          _ = Fu.intrinsicMap ⟨y, hyu⟩ := hmapY
          _ = Fu.map q := rfl
      exact False.elim (Set.disjoint_left.mp (hside t) hqyGraph
        (by rw [← hpqMap]; simpa only [Jt] using hpx))
  · have hpFrontier : p ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).2, hpInt⟩
    have hxOne := K.mem_oneSkeleton_of_faceChart_mem_frontier t hxt hpFrontier
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion := Fu.mapsTo_interiorRegion hqInt
      have hpxGraph : Ft.map p ∈
          K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
        refine ⟨x, hxOne, ?_⟩
        calc
          K.graphReplacementMap hcont hinj D C x =
              K.cellwisePLFillingMap
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) x :=
            (K.cellwisePLFillingMap_eq_graphReplacement hxOne).symm
          _ = Ft.intrinsicMap ⟨x, hxt⟩ := hmapX
          _ = Ft.map p := rfl
      exact False.elim (Set.disjoint_left.mp (hside u) hpxGraph
        (by rw [hpqMap]; simpa only [Ju] using hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      apply K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C hxOne hyOne
      rw [← K.cellwisePLFillingMap_eq_graphReplacement hxOne,
        ← K.cellwisePLFillingMap_eq_graphReplacement hyOne]
      exact hxy

/-- Vertex-side compatibility is sufficient to make the coherent cellwise filling a genuine
topological embedding of the compact intrinsic realization into the plane. -/
theorem cellwisePLFillingMap_isEmbedding
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    _root_.Topology.IsEmbedding (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  apply Topology.IsClosedEmbedding.toIsEmbedding
  apply Continuous.isClosedEmbedding
  · exact K.continuous_cellwisePLFillingMap
  · exact K.injective_cellwisePLFillingMap
      (K.faceFillingsGraphAvoidInteriors_of_verticesAvoid hvertices)

/-- The image of the coherent cellwise filling is exactly the finite union of its polygonal
closed face regions. -/
theorem range_cellwisePLFillingMap :
    Set.range (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) =
      ⋃ t : K.Face,
        (K.facePolygonalCircle
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let t := K.containingFace x
    let F := K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    rw [K.cellwisePLFillingMap_eqOn_face t x hxt, ← F.range_intrinsicMap]
    exact ⟨⟨x, hxt⟩, rfl⟩
  · intro y hy
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hy
    let F := K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    rw [← F.range_intrinsicMap] at hyt
    obtain ⟨x, rfl⟩ := hyt
    refine ⟨x.1, ?_⟩
    exact (K.cellwisePLFillingMap_eqOn_face t x.1 x.2).trans rfl

/-- The exact image of the coherent cellwise filling carries one conforming pure finite plane
complex.  The complex is built from a common arrangement of all face-polygon edge lines, rather
than by taking a nonconforming union of the independently certified face meshes. -/
theorem exists_cellwisePLFilling_targetComplex :
    ∃ L : PlaneComplex,
      L.support = Set.range (K.cellwisePLFillingMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)) ∧
      L.IsPure2 := by
  let J : K.Face → PolygonalCircle := fun t ↦ K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  obtain ⟨L, hLsupport, hLpure⟩ := PolygonalFamily.closedRegion_is_polyhedron J
  refine ⟨L, ?_, hLpure⟩
  rw [hLsupport, K.range_cellwisePLFillingMap]
  rfl

/-- A compatible cellwise filling gives a finite plane triangulation of the intrinsic source,
with the plane support coordinate equal to the filling map.  This is the concrete output needed
when a Radó chart replaces an abstract old patch by a polygonal patch in chart coordinates. -/
theorem exists_cellwisePLFilling_retriangulation
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    ∃ (L : PlaneComplex) (_ : L.IsPure2)
      (e : L.support ≃ₜ K.realization),
      ∀ p : L.support,
        K.cellwisePLFillingMap
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) (e p) = p.1 := by
  let f := K.cellwisePLFillingMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  obtain ⟨L, hLsupport, hLpure⟩ := K.exists_cellwisePLFilling_targetComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  have hfEmbedding : _root_.Topology.IsEmbedding f :=
    K.cellwisePLFillingMap_isEmbedding hvertices
  let ef : K.realization ≃ₜ Set.range f := hfEmbedding.toHomeomorph
  let e : L.support ≃ₜ K.realization :=
    (Homeomorph.setCongr hLsupport).trans ef.symm
  refine ⟨L, hLpure, e, ?_⟩
  intro p
  have hpRange : p.1 ∈ Set.range f := by
    rw [← hLsupport]
    exact p.2
  change f (ef.symm ⟨p.1, hpRange⟩) = p.1
  exact congrArg Subtype.val (ef.apply_symm_apply ⟨p.1, hpRange⟩)

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_06
/- END ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteFaceFilling | e37e82c1d9da700e8c997cc8e48a9efd892464c328a2f91f2c97616216448ecc -/
section schottkyclassification15_block_07
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# PL fillings of locally finite polygonal face boundaries

The globally coherent graph replacement gives every maximal face a PL map from the standard
triangular frontier onto a simple polygonal circle. Polygonal Schoenflies fills that map by a
finite PL homeomorphism without changing its shared-edge boundary values.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-- A certified finite PL filling of the canonical polygonal boundary of one locally finite
face. -/
structure FacePLFilling (f : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map (K.faceBoundaryMap (G := G) f)
    (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion =
    (K.facePolygonalCircle (G := G) f).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (K.facePolygonalCircle (G := G) f).closedRegion)

/-- Polygonal Schoenflies fills the canonical face boundary by a finite PL homeomorphism. -/
theorem exists_facePLFilling (f : K.Face) :
    Nonempty (K.FacePLFilling (G := G) f) := by
  let J := K.facePolygonalCircle (G := G) f
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle J
      (K.faceBoundaryMap_isPLOnSet (G := G) f)
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert
  }⟩

/-- A fixed certified PL filling for downstream locally finite gluing. -/
noncomputable def facePLFilling (f : K.Face) :
    K.FacePLFilling (G := G) f :=
  Classical.choice (K.exists_facePLFilling (G := G) f)

/-- Fillings of neighboring faces agree whenever their boundary lifts name the same global
one-skeleton point. -/
theorem facePLFilling_eq_of_boundaryLift_eq
    {f g : K.Face} {p q : StandardFaceBoundary}
    (hpq : K.faceBoundaryLift f p = K.faceBoundaryLift g q) :
    (K.facePLFilling (G := G) f).map p.1 =
      (K.facePLFilling (G := G) g).map q.1 := by
  rw [(K.facePLFilling (G := G) f).eqOn_boundary p.2,
    (K.facePLFilling (G := G) g).eqOn_boundary q.2,
    K.faceBoundaryMap_apply (G := G) f p,
    K.faceBoundaryMap_apply (G := G) g q, hpq]

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_07
/- END ClassificationOfSurfaces.Moise.LocallyFiniteFaceFilling -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteCellwiseExtension | 3459266df04c60bc35555021690f070c61447c80d2c6c7566165f0a260c6f1c1 -/
section schottkyclassification15_block_08
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Cellwise assembly for locally finite PL face fillings

This file transports every polygonal Schoenflies filling back to its native abstract face.  A
single compatibility package records the three geometric facts needed for global assembly:
filled interiors are pairwise disjoint, the replacement graph misses every filled interior, and
the family of filled closed regions is locally finite.  Under these conditions the transported
maps form a genuine locally finite triangle complex in the plane.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

namespace FacePLFilling

/-- A standard-triangle filling transported back to the native simplex of its source face. -/
noncomputable def faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    K.ClosedFace f → Plane :=
  fun x ↦ F.map (K.facePlaneHomeomorph f x).1

theorem continuous_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Continuous F.faceMap := by
  have hF : Continuous (fun p : standardFaceRegion ↦ F.map p.1) :=
    continuousOn_iff_continuous_restrict.mp F.continuousOn
  exact hF.comp (K.facePlaneHomeomorph f).continuous

theorem injective_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Function.Injective F.faceMap := by
  intro x y hxy
  apply (K.facePlaneHomeomorph f).injective
  apply Subtype.ext
  exact F.injectiveOn (K.facePlaneHomeomorph f x).2
    (K.facePlaneHomeomorph f y).2 hxy

theorem range_faceMap {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Set.range F.faceMap = (K.facePolygonalCircle (G := G) f).closedRegion := by
  rw [← F.image_eq]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(K.facePlaneHomeomorph f x).1,
      (K.facePlaneHomeomorph f x).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    let q : standardFaceRegion := ⟨p, hp⟩
    refine ⟨(K.facePlaneHomeomorph f).symm q, ?_⟩
    change F.map (K.facePlaneHomeomorph f
      ((K.facePlaneHomeomorph f).symm q)).1 = F.map p
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]

/-- The relative interior of a filled source face maps into the bounded complementary region
of its polygonal boundary. -/
theorem mapsTo_interiorRegion {f : K.Face} (F : K.FacePLFilling (G := G) f) :
    Set.MapsTo F.map (interior standardFaceRegion)
      (K.facePolygonalCircle (G := G) f).interiorRegion := by
  intro p hp
  have hpRegion : p ∈ standardFaceRegion := interior_subset hp
  have hclosed : F.map p ∈
      (K.facePolygonalCircle (G := G) f).closedRegion := by
    rw [← F.image_eq]
    exact ⟨p, hpRegion, rfl⟩
  rw [(K.facePolygonalCircle (G := G) f).closedRegion_eq_union] at hclosed
  rcases hclosed with hbounded | hcarrier
  · exact hbounded
  · rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hcarrier
    obtain ⟨q, hq, hqmap⟩ := hcarrier
    have hmapEq : F.map p = F.map q := by
      rw [F.eqOn_boundary hq]
      exact hqmap.symm
    have hpq : p = q := F.injectiveOn hpRegion
      (standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hq) hmapEq
    subst q
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hp hq)

end FacePLFilling

/-! ## Boundary recognition from global barycentric coordinates -/

theorem exists_faceVertex_eq_of_mem (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) : ∃ i : ZMod 3, K.faceVertex f i = v := by
  let w : {w // w ∈ K.faceVertices f} := ⟨v, hv⟩
  let j : Fin 3 := (K.faceVertexEquiv f).symm w
  let i : ZMod 3 := ZMod.finEquiv 3 j
  refine ⟨i, ?_⟩
  change ((K.faceVertexEquiv f)
    ((ZMod.finEquiv 3).symm (ZMod.finEquiv 3 j))).1 = v
  rw [(ZMod.finEquiv 3).symm_apply_apply,
    (K.faceVertexEquiv f).apply_symm_apply]

/-- Every abstract edge contained in a maximal face is one of its three cyclic edges. -/
theorem exists_faceEdge_eq_of_subset (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    ∃ i : ZMod 3, K.faceEdge f i = e := by
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f (hef (K.edgeFirst_mem e))
  obtain ⟨j, hj⟩ := K.exists_faceVertex_eq_of_mem f (hef (K.edgeSecond_mem e))
  have hij : i ≠ j := by
    intro h
    apply K.edgeFirst_ne_edgeSecond e
    rw [← hi, ← hj, h]
  rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
    h | h | h
  · exact (hij h.symm).elim
  · subst j
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair, hi, hj]
  · subst j
    refine ⟨i + 2, ?_⟩
    apply Subtype.ext
    rw [K.faceEdge_val, K.edge_eq_pair]
    have hcycle : i + 2 + 1 = i :=
      (by decide : ∀ k : ZMod 3, k + 2 + 1 = k) i
    rw [hcycle]
    rw [hi, hj]
    ext v
    simp [or_comm]

/-- If equal global barycentric coordinates are represented on distinct vertex triples, the
standard coordinate on the first triangle lies on its frontier. -/
theorem faceChart_mem_frontier_of_extended_eq
    {f g : K.Face} (hfg : K.faceVertices f ≠ K.faceVertices g)
    {x : K.ClosedFace f} {y : K.ClosedFace g}
    (hxy : extendFaceCoordinates (K.faceVertices f) x =
      extendFaceCoordinates (K.faceVertices g) y) :
    (K.facePlaneHomeomorph f x).1 ∈ frontier standardFaceRegion := by
  classical
  let inter := K.faceVertices f ∩ K.faceVertices g
  have hinterCard : inter.card ≤ 2 := by
    have hle : inter.card ≤ 3 := by
      calc
        inter.card ≤ (K.faceVertices f).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 3 := K.faceVertices_card f
    by_contra hnot
    have hthree : inter.card = 3 := by omega
    have hleft : inter = K.faceVertices f :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.faceVertices_card f, hthree])
    have hright : inter = K.faceVertices g :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [K.faceVertices_card g, hthree])
    exact hfg (hleft.symm.trans hright)
  have hinterNonempty : inter.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hxzero : ∀ v : {v // v ∈ K.faceVertices f}, x v = 0 := by
      intro v
      have hvNotG : v.1 ∉ K.faceVertices g := by
        intro hvg
        have : v.1 ∈ inter := Finset.mem_inter.mpr ⟨v.2, hvg⟩
        rw [hempty] at this
        exact Finset.notMem_empty _ this
      have hc := congrFun hxy v.1
      rw [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
        extendFaceCoordinates_of_notMem (K.faceVertices g) y hvNotG] at hc
      exact hc
    have hzero : (∑ v, x v) = 0 := by simp [hxzero]
    have hone : (∑ v, x v) = 1 := stdSimplex.sum_eq_one x
    rw [hzero] at hone
    norm_num at hone
  have htwo : 2 ≤ (K.faceVertices f).card := by
    rw [K.faceVertices_card f]
    omega
  obtain ⟨e, hinterE, hEf, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq Finset.inter_subset_left
      hinterCard htwo
  let E : K.Edge := ⟨e, hEcard, f, hEf⟩
  have hxSupported : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ E.1 → x v = 0 := by
    intro v hvE
    have hvNotG : v.1 ∉ K.faceVertices g := by
      intro hvg
      exact hvE (hinterE (Finset.mem_inter.mpr ⟨v.2, hvg⟩))
    have hc := congrFun hxy v.1
    rw [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
      extendFaceCoordinates_of_notMem (K.faceVertices g) y hvNotG] at hc
    exact hc
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset f E hEf
  have hxSide : x ∈ K.faceSide f i := by
    change ∀ v, v.1 ∉ (K.faceEdge f i).1 → x v = 0
    simpa only [hi] using hxSupported
  have hpSide : (K.facePlaneHomeomorph f x).1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← K.facePlaneHomeomorph_image_edge f i]
    exact ⟨x, hxSide, rfl⟩
  have hpCarrier : (K.facePlaneHomeomorph f x).1 ∈
      standardTriangleCircle.carrier := Set.mem_iUnion.mpr ⟨i, hpSide⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- Lifting the standard coordinate of a boundary point recovers its original ambient support
point. -/
theorem faceBoundaryLift_facePlaneHomeomorph (f : K.Face) (x : K.ClosedFace f)
    (hp : (K.facePlaneHomeomorph f x).1 ∈ frontier standardFaceRegion) :
    (K.faceBoundaryLift f
      ⟨(K.facePlaneHomeomorph f x).1, hp⟩).1 =
      faceToSupport (K := K) f x := by
  apply Subtype.ext
  change K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨(K.facePlaneHomeomorph f x).1,
          standardFaceBoundary_mem_region
            ⟨(K.facePlaneHomeomorph f x).1, hp⟩⟩) = K.faceMap f x
  congr 1
  apply (K.facePlaneHomeomorph f).injective
  rw [(K.facePlaneHomeomorph f).apply_symm_apply]

/-! ## Global cellwise compatibility -/

/-- The geometric conditions under which the independently chosen polygonal face fillings
assemble to a locally finite plane complex.  The first field rules out duplicate maximal-face
labels; the remaining fields say that different filled cells meet only along the replacement
graph and remain locally finite. -/
structure CellwiseCompatibility (G : K.PlaneGraphRealization) : Prop where
  faceVertices_injective : Function.Injective K.faceVertices
  graphAvoidsInteriors : ∀ f : K.Face,
    Disjoint (Set.range G.graphReplacementMap)
      (K.facePolygonalCircle (G := G) f).interiorRegion
  interiorsDisjoint : ∀ f g : K.Face, f ≠ g →
    Disjoint (K.facePolygonalCircle (G := G) f).interiorRegion
      (K.facePolygonalCircle (G := G) g).interiorRegion
  closedRegions_mem_region : ∀ f : K.Face,
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region
  locallyFiniteClosedRegions : LocallyFinite fun f : K.Face ↦
    {q : G.region | q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion}

namespace CellwiseCompatibility

theorem distinct_faceVertices (H : K.CellwiseCompatibility G)
    {f g : K.Face} (hfg : f ≠ g) :
    K.faceVertices f ≠ K.faceVertices g := by
  exact fun h ↦ hfg (CellwiseCompatibility.faceVertices_injective H h)

/-- The transported chosen fillings have exactly the same overlap relation as the original
abstract triangles. -/
theorem faceMap_eq_iff (H : K.CellwiseCompatibility G)
    {f g : K.Face} {x : K.ClosedFace f} {y : K.ClosedFace g} :
    (K.facePLFilling (G := G) f).faceMap x =
        (K.facePLFilling (G := G) g).faceMap y ↔
      extendFaceCoordinates (K.faceVertices f) x =
        extendFaceCoordinates (K.faceVertices g) y := by
  let F := K.facePLFilling (G := G) f
  let L := K.facePLFilling (G := G) g
  let p := K.facePlaneHomeomorph f x
  let q := K.facePlaneHomeomorph g y
  change F.map p.1 = L.map q.1 ↔ _
  constructor
  · intro hmap
    by_cases hfg : f = g
    · subst g
      have hxy : x = y := F.injective_faceMap hmap
      subst y
      rfl
    have hverts := distinct_faceVertices H hfg
    have hpNotInterior : p.1 ∉ interior standardFaceRegion := by
      intro hpInterior
      have hpFilled : F.map p.1 ∈
          (K.facePolygonalCircle (G := G) f).interiorRegion :=
        F.mapsTo_interiorRegion hpInterior
      by_cases hqInterior : q.1 ∈ interior standardFaceRegion
      · have hqFilled : L.map q.1 ∈
            (K.facePolygonalCircle (G := G) g).interiorRegion :=
          L.mapsTo_interiorRegion hqInterior
        exact Set.disjoint_left.mp (H.interiorsDisjoint f g hfg) hpFilled
          (hmap ▸ hqFilled)
      · have hqFrontier : q.1 ∈ frontier standardFaceRegion := by
          rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
          exact ⟨q.2, hqInterior⟩
        have hqGraph : L.map q.1 ∈ Set.range G.graphReplacementMap := by
          refine ⟨K.faceBoundaryLift g ⟨q.1, hqFrontier⟩, ?_⟩
          rw [L.eqOn_boundary hqFrontier,
            K.faceBoundaryMap_apply (G := G) g ⟨q.1, hqFrontier⟩]
        exact Set.disjoint_left.mp (H.graphAvoidsInteriors f) hqGraph
          (hmap ▸ hpFilled)
    have hqNotInterior : q.1 ∉ interior standardFaceRegion := by
      intro hqInterior
      have hqFilled : L.map q.1 ∈
          (K.facePolygonalCircle (G := G) g).interiorRegion :=
        L.mapsTo_interiorRegion hqInterior
      have hpFrontier : p.1 ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨p.2, hpNotInterior⟩
      have hpGraph : F.map p.1 ∈ Set.range G.graphReplacementMap := by
        refine ⟨K.faceBoundaryLift f ⟨p.1, hpFrontier⟩, ?_⟩
        rw [F.eqOn_boundary hpFrontier,
          K.faceBoundaryMap_apply (G := G) f ⟨p.1, hpFrontier⟩]
      exact Set.disjoint_left.mp (H.graphAvoidsInteriors g) hpGraph
        (hmap ▸ hqFilled)
    have hpFrontier : p.1 ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨p.2, hpNotInterior⟩
    have hqFrontier : q.1 ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨q.2, hqNotInterior⟩
    have hgraph :
        G.graphReplacementMap (K.faceBoundaryLift f ⟨p.1, hpFrontier⟩) =
          G.graphReplacementMap (K.faceBoundaryLift g ⟨q.1, hqFrontier⟩) := by
      rw [← K.faceBoundaryMap_apply (G := G) f ⟨p.1, hpFrontier⟩,
        ← K.faceBoundaryMap_apply (G := G) g ⟨q.1, hqFrontier⟩,
        ← F.eqOn_boundary hpFrontier, ← L.eqOn_boundary hqFrontier]
      exact hmap
    have hlift := G.graphReplacementMap_injective hgraph
    have hsupp : faceToSupport (K := K) f x = faceToSupport (K := K) g y := by
      calc
        faceToSupport (K := K) f x =
            (K.faceBoundaryLift f ⟨p.1, hpFrontier⟩).1 :=
          (K.faceBoundaryLift_facePlaneHomeomorph f x hpFrontier).symm
        _ = (K.faceBoundaryLift g ⟨q.1, hqFrontier⟩).1 :=
          congrArg Subtype.val hlift
        _ = faceToSupport (K := K) g y :=
          K.faceBoundaryLift_facePlaneHomeomorph g y hqFrontier
    exact K.faceMap_eq_iff.mp (congrArg Subtype.val hsupp)
  · intro hcoords
    by_cases hfg : f = g
    · subst g
      have hxy : x = y := K.faceMap_injective f (K.faceMap_eq_iff.mpr hcoords)
      subst y
      rfl
    have hpFrontier := K.faceChart_mem_frontier_of_extended_eq
      (distinct_faceVertices H hfg) hcoords
    have hqFrontier := K.faceChart_mem_frontier_of_extended_eq
      (distinct_faceVertices H (Ne.symm hfg)) hcoords.symm
    exact K.facePLFilling_eq_of_boundaryLift_eq
      (f := f) (g := g) (p := ⟨p.1, hpFrontier⟩) (q := ⟨q.1, hqFrontier⟩) (by
        apply Subtype.ext
        rw [K.faceBoundaryLift_facePlaneHomeomorph f x hpFrontier,
          K.faceBoundaryLift_facePlaneHomeomorph g y hqFrontier]
        exact Subtype.ext (K.faceMap_eq_iff.mpr hcoords))

end CellwiseCompatibility

/-! ## The assembled replacement complex -/

/-- Replace every face of a locally finite complex by its coherent polygonal Schoenflies
filling.  The abstract vertices and faces are unchanged. -/
noncomputable abbrev polygonalReplacementComplex (H : K.CellwiseCompatibility G) :
    LocallyFiniteTriangleComplex G.region where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := K.faceVertices
  faceVertices_card := K.faceVertices_card
  vertex_used := K.vertex_used
  faceMap f x := ⟨(K.facePLFilling (G := G) f).faceMap x,
    H.closedRegions_mem_region f <|
      (K.facePLFilling (G := G) f).range_faceMap ▸ Set.mem_range_self x⟩
  faceMap_continuous f := by
    apply Continuous.subtype_mk
    exact (K.facePLFilling (G := G) f).continuous_faceMap
  faceMap_eq_iff := by
    intro f g x y
    constructor
    · intro h
      exact (CellwiseCompatibility.faceMap_eq_iff H).mp
        (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (CellwiseCompatibility.faceMap_eq_iff H).mpr h
  locallyFinite := by
    convert H.locallyFiniteClosedRegions using 1
    funext f
    ext q
    constructor
    · rintro ⟨x, hx⟩
      change q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion
      rw [← (K.facePLFilling (G := G) f).range_faceMap]
      exact ⟨x, congrArg Subtype.val hx⟩
    · intro hq
      rw [← (K.facePLFilling (G := G) f).range_faceMap] at hq
      obtain ⟨x, hx⟩ := hq
      exact ⟨x, Subtype.ext hx⟩

@[simp] theorem polygonalReplacementComplex_faceVertices
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    (K.polygonalReplacementComplex H).faceVertices f = K.faceVertices f := rfl

@[simp] theorem polygonalReplacementComplex_faceMap
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    ((K.polygonalReplacementComplex H).faceMap f x).1 =
      (K.facePLFilling (G := G) f).faceMap x := rfl

theorem polygonalReplacementComplex_faceCarrier
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    (K.polygonalReplacementComplex H).faceCarrier f =
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion} := by
  ext q
  constructor
  · rintro ⟨x, hx⟩
    change q.1 ∈ (K.facePolygonalCircle (G := G) f).closedRegion
    rw [← (K.facePLFilling (G := G) f).range_faceMap]
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro hq
    rw [← (K.facePLFilling (G := G) f).range_faceMap] at hq
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩

/-! ## The canonical homeomorphism onto the replacement -/

/-- A chosen maximal face containing a point of the support. -/
noncomputable def supportFace (p : K.support) : K.Face :=
  Classical.choose (Set.mem_iUnion.mp p.2)

theorem mem_faceCarrier_supportFace (p : K.support) :
    p.1 ∈ K.faceCarrier (K.supportFace p) :=
  Classical.choose_spec (Set.mem_iUnion.mp p.2)

/-- Chosen barycentric coordinates for a support point in its chosen maximal face. -/
noncomputable def supportFacePoint (p : K.support) : K.ClosedFace (K.supportFace p) :=
  Classical.choose (K.mem_faceCarrier_supportFace p)

theorem faceMap_supportFacePoint (p : K.support) :
    K.faceMap (K.supportFace p) (K.supportFacePoint p) = p.1 :=
  Classical.choose_spec (K.mem_faceCarrier_supportFace p)

theorem faceInSupport_eq_preimage (f : K.Face) :
    faceInSupport (K := K) f =
      Subtype.val ⁻¹' K.faceCarrier f := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact Set.mem_range_self x
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hx

theorem locallyFinite_faceInSupport :
    LocallyFinite (faceInSupport (K := K)) := by
  have h := K.locallyFinite.preimage_continuous
    (g := fun p : K.support ↦ p.1) continuous_subtype_val
  convert h using 1
  funext f
  exact K.faceInSupport_eq_preimage f

/-- The image of one source face, regarded as a subset of the permitted open plane region. -/
def PlaneGraphRealization.faceImageInRegion (G : K.PlaneGraphRealization)
    (f : K.Face) : Set G.region :=
  {q | q.1 ∈ G.map '' faceInSupport (K := K) f}

/-- Source faces remain locally finite after passing through a realization which is closed
relative to its perturbation region. -/
theorem PlaneGraphRealization.locallyFinite_faceImagesInRegion
    (G : K.PlaneGraphRealization) :
    LocallyFinite G.faceImageInRegion := by
  let mapInRegion : K.support → G.region := fun p ↦ ⟨G.map p, G.map_mem_region p⟩
  have hEmbedding : _root_.Topology.IsEmbedding mapInRegion :=
    G.isEmbedding.codRestrict G.region G.map_mem_region
  have hlocal : LocallyFinite fun f : K.Face ↦
      mapInRegion '' faceInSupport (K := K) f :=
    PlaneGraphRealization.locallyFinite_image_isEmbedding_of_isClosed_range
      K.locallyFinite_faceInSupport hEmbedding G.mapClosedInRegion
  have heq : (fun f : K.Face ↦ mapInRegion '' faceInSupport (K := K) f) =
      G.faceImageInRegion := by
    funext f
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      exact ⟨p, hp, congrArg Subtype.val hpq⟩
    · rintro ⟨p, hp, hpq⟩
      refine ⟨p, hp, ?_⟩
      apply Subtype.ext
      exact hpq
  rwa [← heq]

theorem iUnion_faceInSupport :
    (⋃ f : K.Face, faceInSupport (K := K) f) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  apply Set.mem_iUnion.mpr
  refine ⟨K.supportFace p, K.supportFacePoint p, ?_⟩
  apply Subtype.ext
  exact K.faceMap_supportFacePoint p

theorem isEmbedding_faceToSupport [T2Space S] (f : K.Face) :
    _root_.Topology.IsEmbedding (faceToSupport (K := K) f) :=
  (K.isEmbedding_faceMap f).codRestrict K.support
    (fun x ↦ Set.mem_iUnion.mpr ⟨f, Set.mem_range_self x⟩)

/-- A closed abstract face is homeomorphic to its carrier inside the whole support. -/
noncomputable def faceToSupportHomeomorph [T2Space S] (f : K.Face) :
    K.ClosedFace f ≃ₜ faceInSupport (K := K) f :=
  (K.isEmbedding_faceToSupport f).toHomeomorph

@[simp] theorem faceToSupportHomeomorph_apply [T2Space S]
    (f : K.Face) (x : K.ClosedFace f) :
    (K.faceToSupportHomeomorph f x).1 = faceToSupport (K := K) f x := rfl

variable [T2Space S]

/-- The coherent cellwise filling as a map into the support of the assembled plane complex. -/
noncomputable def polygonalReplacementMap (H : K.CellwiseCompatibility G) :
    K.support → (K.polygonalReplacementComplex H).support :=
  fun p ↦ ⟨⟨(K.facePLFilling (G := G) (K.supportFace p)).faceMap
      (K.supportFacePoint p), H.closedRegions_mem_region (K.supportFace p) <|
        (K.facePLFilling (G := G) (K.supportFace p)).range_faceMap ▸
          Set.mem_range_self (K.supportFacePoint p)⟩,
    Set.mem_iUnion.mpr ⟨K.supportFace p,
      Set.mem_range_self (K.supportFacePoint p)⟩⟩

omit [T2Space S] in
/-- On every named source face, the global replacement map is the chosen face filling. -/
theorem polygonalReplacementMap_faceToSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    K.polygonalReplacementMap H (faceToSupport (K := K) f x) =
      faceToSupport (K := K.polygonalReplacementComplex H) f x := by
  apply Subtype.ext
  apply Subtype.ext
  change (K.facePLFilling (G := G)
      (K.supportFace (faceToSupport (K := K) f x))).faceMap
        (K.supportFacePoint (faceToSupport (K := K) f x)) =
    (K.facePLFilling (G := G) f).faceMap x
  apply (CellwiseCompatibility.faceMap_eq_iff H).mpr
  apply K.faceMap_eq_iff.mp
  rw [K.faceMap_supportFacePoint]
  rfl

/-- The source face formula, expressed on a carrier subtype. -/
noncomputable def polygonalReplacementMapOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    faceInSupport (K := K) f → (K.polygonalReplacementComplex H).support :=
  fun p ↦ faceToSupport (K := K.polygonalReplacementComplex H) f
    ((K.faceToSupportHomeomorph f).symm p)

theorem continuous_polygonalReplacementMapOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    Continuous (K.polygonalReplacementMapOnFace H f) := by
  exact (continuous_faceToSupport
    (K := K.polygonalReplacementComplex H) f).comp
      (K.faceToSupportHomeomorph f).symm.continuous

theorem polygonalReplacementMap_eqOn_faceInSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    ∀ p : faceInSupport (K := K) f,
      K.polygonalReplacementMap H p.1 =
        K.polygonalReplacementMapOnFace H f p := by
  rintro ⟨p, x, rfl⟩
  rw [K.polygonalReplacementMap_faceToSupport H f x]
  congr 1
  exact (K.faceToSupportHomeomorph f).symm_apply_apply x |>.symm

theorem continuous_polygonalReplacementMap (H : K.CellwiseCompatibility G) :
    Continuous (K.polygonalReplacementMap H) := by
  apply K.locallyFinite_faceInSupport.continuous K.iUnion_faceInSupport
  · intro f
    exact (isCompact_faceInSupport (K := K) f).isClosed
  · intro f
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous_polygonalReplacementMapOnFace H f using 1
    funext p
    exact K.polygonalReplacementMap_eqOn_faceInSupport H f p

/-- Read the old face map in coordinates chosen from a point of the replacement support. -/
noncomputable def polygonalReplacementInverse (H : K.CellwiseCompatibility G) :
    (K.polygonalReplacementComplex H).support → K.support :=
  fun p ↦ faceToSupport (K := K)
    ((K.polygonalReplacementComplex H).supportFace p)
    ((K.polygonalReplacementComplex H).supportFacePoint p)

omit [T2Space S] in
/-- On every replacement face, the inverse is the original face parametrization. -/
theorem polygonalReplacementInverse_faceToSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) (x : K.ClosedFace f) :
    K.polygonalReplacementInverse H
        (faceToSupport (K := K.polygonalReplacementComplex H) f x) =
      faceToSupport (K := K) f x := by
  let L := K.polygonalReplacementComplex H
  let p : L.support := faceToSupport (K := L) f x
  let g := L.supportFace p
  let y := L.supportFacePoint p
  apply Subtype.ext
  change K.faceMap g y = K.faceMap f x
  apply K.faceMap_eq_iff.mpr
  apply L.faceMap_eq_iff.mp
  calc
    L.faceMap g y = p.1 := L.faceMap_supportFacePoint p
    _ = L.faceMap f x := rfl

/-- The inverse face formula on one replacement carrier. -/
noncomputable def polygonalReplacementInverseOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    faceInSupport (K := K.polygonalReplacementComplex H) f → K.support :=
  fun p ↦ faceToSupport (K := K) f
    (((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm p)

omit [T2Space S] in
theorem continuous_polygonalReplacementInverseOnFace
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    Continuous (K.polygonalReplacementInverseOnFace H f) := by
  exact (continuous_faceToSupport (K := K) f).comp
    ((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm.continuous

omit [T2Space S] in
theorem polygonalReplacementInverse_eqOn_faceInSupport
    (H : K.CellwiseCompatibility G) (f : K.Face) :
    ∀ p : faceInSupport (K := K.polygonalReplacementComplex H) f,
      K.polygonalReplacementInverse H p.1 =
        K.polygonalReplacementInverseOnFace H f p := by
  rintro ⟨p, x, rfl⟩
  rw [K.polygonalReplacementInverse_faceToSupport H f x]
  congr 1
  exact ((K.polygonalReplacementComplex H).faceToSupportHomeomorph f).symm_apply_apply x |>.symm

omit [T2Space S] in
theorem continuous_polygonalReplacementInverse (H : K.CellwiseCompatibility G) :
    Continuous (K.polygonalReplacementInverse H) := by
  let L := K.polygonalReplacementComplex H
  apply L.locallyFinite_faceInSupport.continuous L.iUnion_faceInSupport
  · intro f
    exact (isCompact_faceInSupport (K := L) f).isClosed
  · intro f
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous_polygonalReplacementInverseOnFace H f using 1
    funext p
    exact K.polygonalReplacementInverse_eqOn_faceInSupport H f p

omit [T2Space S] in
theorem polygonalReplacementInverse_apply_map
    (H : K.CellwiseCompatibility G) (p : K.support) :
    K.polygonalReplacementInverse H (K.polygonalReplacementMap H p) = p := by
  let f := K.supportFace p
  let x := K.supportFacePoint p
  have hpresentation : faceToSupport (K := K) f x = p := by
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  rw [← hpresentation, K.polygonalReplacementMap_faceToSupport H f x,
    K.polygonalReplacementInverse_faceToSupport H f x]

omit [T2Space S] in
theorem polygonalReplacementMap_apply_inverse
    (H : K.CellwiseCompatibility G)
    (p : (K.polygonalReplacementComplex H).support) :
    K.polygonalReplacementMap H (K.polygonalReplacementInverse H p) = p := by
  let L := K.polygonalReplacementComplex H
  let f := L.supportFace p
  let x := L.supportFacePoint p
  have hpresentation : faceToSupport (K := L) f x = p := by
    apply Subtype.ext
    exact L.faceMap_supportFacePoint p
  rw [← hpresentation, K.polygonalReplacementInverse_faceToSupport H f x,
    K.polygonalReplacementMap_faceToSupport H f x]

/-- The source support and its coherent polygonal replacement are canonically homeomorphic. -/
noncomputable def polygonalReplacementHomeomorph (H : K.CellwiseCompatibility G) :
    K.support ≃ₜ (K.polygonalReplacementComplex H).support where
  toFun := K.polygonalReplacementMap H
  invFun := K.polygonalReplacementInverse H
  left_inv := K.polygonalReplacementInverse_apply_map H
  right_inv := K.polygonalReplacementMap_apply_inverse H
  continuous_toFun := K.continuous_polygonalReplacementMap H
  continuous_invFun := K.continuous_polygonalReplacementInverse H

/-- The canonical replacement homeomorphism preserves every named closed face exactly.  This
is stronger than preservation of the total support and is the bridge used when a finite family
of replacement faces is pulled back to a finite source subcomplex. -/
theorem polygonalReplacementHomeomorph_mem_faceCarrier_iff
    (H : K.CellwiseCompatibility G) (f : K.Face) (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1 ∈
        (K.polygonalReplacementComplex H).faceCarrier f ↔
      p.1 ∈ K.faceCarrier f := by
  constructor
  · rintro ⟨x, hx⟩
    have htarget :
        faceToSupport (K := K.polygonalReplacementComplex H) f x =
          K.polygonalReplacementHomeomorph H p :=
      Subtype.ext hx
    have hsource :
        (K.polygonalReplacementHomeomorph H).symm
            (faceToSupport (K := K.polygonalReplacementComplex H) f x) = p := by
      rw [htarget, (K.polygonalReplacementHomeomorph H).symm_apply_apply]
    change K.polygonalReplacementInverse H
        (faceToSupport (K := K.polygonalReplacementComplex H) f x) = p at hsource
    rw [K.polygonalReplacementInverse_faceToSupport H f x] at hsource
    exact ⟨x, congrArg Subtype.val hsource⟩
  · rintro ⟨x, hx⟩
    have hsource : faceToSupport (K := K) f x = p := Subtype.ext hx
    have hmap := K.polygonalReplacementMap_faceToSupport H f x
    change K.polygonalReplacementHomeomorph H
        (faceToSupport (K := K) f x) =
          faceToSupport (K := K.polygonalReplacementComplex H) f x at hmap
    rw [hsource] at hmap
    exact ⟨x, (congrArg Subtype.val hmap).symm⟩

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification15_block_08
/- END ClassificationOfSurfaces.Moise.LocallyFiniteCellwiseExtension -/
