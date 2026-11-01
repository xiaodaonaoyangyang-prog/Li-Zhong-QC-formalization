/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification16: pinned classification sources; see BUNDLE_MAP.json. -/
import LiZhongExternal.Classification.SchottkyClassification15
import LiZhongExternal.Classification.SchottkyClassification14

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFinitePLApproximation | 7ed5b85f85b5cfb34e1d5f0aee6cc4691f17f2fbe72685d2d9be035e6020d825 -/
noncomputable section

section schottkyclassification16_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Quantitative locally finite PL approximation

This file records the facewise metric control used in Moise Chapter 6, Theorem 3.  It is
deliberately pointwise: on a noncompact open complex no uniform positive tolerance exists, but a
strongly positive tolerance has a positive lower bound on every compact face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-! ## The original face map and the achievable side-control hypotheses -/

/-- A global vertex lies in a maximal face carrier exactly when it labels that face. -/
theorem vertexPoint_mem_faceCarrier_iff (f : K.Face) (v : K.Vertex) :
    K.vertexPoint v ∈ K.faceCarrier f ↔ v ∈ K.faceVertices f := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra hv
    have hcoords := K.faceMap_eq_iff.mp hx.symm
    have hc := congrFun hcoords v
    rw [K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v), Pi.single_eq_same,
      extendFaceCoordinates_of_notMem (K.faceVertices f) x hv] at hc
    norm_num at hc
  · intro hv
    exact K.vertexPoint_in_faceCarrier f hv

theorem vertexSupportPoint_mem_faceInSupport_iff (f : K.Face) (v : K.Vertex) :
    (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) ∈
        faceInSupport (K := K) f ↔ v ∈ K.faceVertices f := by
  rw [K.faceInSupport_eq_preimage]
  exact K.vertexPoint_mem_faceCarrier_iff f v

/-- The original plane embedding, written in the standard coordinates of one face.  Values
outside the standard closed triangle are irrelevant. -/
noncomputable def faceOriginalMap (G : K.PlaneGraphRealization) (f : K.Face)
    (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ standardFaceRegion then
    G.map (faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨p, hp⟩))
  else 0

@[simp] theorem faceOriginalMap_apply (f : K.Face) (p : standardFaceRegion) :
    faceOriginalMap G f p.1 =
      G.map (faceToSupport (K := K) f
        ((K.facePlaneHomeomorph f).symm p)) := by
  simp [faceOriginalMap, p.2]

theorem continuousOn_faceOriginalMap (f : K.Face) :
    ContinuousOn (faceOriginalMap G f) standardFaceRegion := by
  rw [continuousOn_iff_continuous_restrict]
  convert G.isEmbedding.continuous.comp
    ((continuous_faceToSupport (K := K) f).comp
      (K.facePlaneHomeomorph f).symm.continuous) using 1
  funext p
  exact faceOriginalMap_apply (G := G) f p

theorem faceOriginalMap_mem_face_image (f : K.Face) (p : standardFaceRegion) :
    faceOriginalMap G f p.1 ∈ G.map '' faceInSupport (K := K) f := by
  refine ⟨faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm p), Set.mem_range_self _, ?_⟩
  exact (faceOriginalMap_apply (G := G) f p).symm

/-- The replacement graph is close to the original embedding on each face boundary, with a
radius allowed to depend on the face.  This is the quantitative hypothesis actually used in
Moise's side-preservation argument. -/
def FaceBoundariesClose (G : K.PlaneGraphRealization) (r : K.Face → ℝ) : Prop :=
  ∀ (f : K.Face) (q : StandardFaceBoundary),
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
      (faceOriginalMap G f q.1) < r f

/-- A face-indexed radius separates every nonincident vertex from the original embedded face.
The closed-ball/closed-thickening formulation is exactly what the bounded Tietze extension
argument consumes. -/
def FaceVertexThickeningsSeparated (G : K.PlaneGraphRealization)
    (r : K.Face → ℝ) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    Disjoint (Metric.closedBall (G.vertexImage v) (r f))
      (Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f))

/-- The relatively locally finite set of all vertex images not belonging to one face, made
ambiently closed by adjoining the complement of the perturbation region. -/
def outsideVertexImages (G : K.PlaneGraphRealization) (f : K.Face) : Set Plane :=
  (⋃ v : {v : K.Vertex // v ∉ K.faceVertices f}, G.vertexImageCarrier v.1) ∪
    G.regionᶜ

private theorem isClosed_union_compl_of_isClosed_preimage'
    {X : Type*} [TopologicalSpace X] {V A : Set X} (hV : IsOpen V)
    (hA : IsClosed ((↑) ⁻¹' A : Set V)) : IsClosed (A ∪ Vᶜ) := by
  apply isOpen_compl_iff.mp
  have hopen := hV.isOpenEmbedding_subtypeVal.isOpenMap _ hA.isOpen_compl
  convert hopen using 1
  ext x
  constructor
  · intro hx
    have hxV : x ∈ V := by
      by_contra hxV
      exact hx (Or.inr hxV)
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_preimage] using
      fun hxA ↦ hx (Or.inl hxA)
  · rintro ⟨y, hy, rfl⟩ h
    rcases h with hA | hV
    · exact hy hA
    · exact hV y.2

theorem isClosed_outsideVertexImages (f : K.Face) :
    IsClosed (outsideVertexImages G f) := by
  apply isClosed_union_compl_of_isClosed_preimage' G.regionOpen
  have hlocal : LocallyFinite
      (fun v : {v : K.Vertex // v ∉ K.faceVertices f} ↦
        G.vertexImageCarrierInRange v.1) :=
    G.locallyFinite_vertexImages.comp_injective
      (g := fun v : {v : K.Vertex // v ∉ K.faceVertices f} ↦ v.1)
      Subtype.val_injective
  have hclosed : IsClosed
      (⋃ v : {v : K.Vertex // v ∉ K.faceVertices f},
        G.vertexImageCarrierInRange v.1) := by
    apply hlocal.isClosed_iUnion
    intro v
    have hvclosed :=
      ((isClosed_singleton : IsClosed ({G.vertexImage v.1} : Set Plane)).preimage
        (continuous_subtype_val : Continuous (Subtype.val : G.region → Plane)))
    convert hvclosed using 1
    ext q
    simp [PlaneGraphRealization.vertexImageCarrierInRange,
      PlaneGraphRealization.vertexImageCarrier]
  convert hclosed using 1
  ext p
  simp only [PlaneGraphRealization.vertexImageCarrierInRange, Set.mem_preimage,
    Set.mem_iUnion, Set.mem_setOf_eq]

theorem faceImage_disjoint_outsideVertexImages (f : K.Face) :
    Disjoint (G.map '' faceInSupport (K := K) f) (outsideVertexImages G f) := by
  rw [Set.disjoint_left]
  rintro q ⟨p, hpFace, rfl⟩ hqOutside
  rcases hqOutside with hqVertex | hqRegion
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hqVertex
    have heq : G.map p = G.vertexImage v.1 := by
      simpa [PlaneGraphRealization.vertexImageCarrier] using hv
    let vp : K.support :=
      ⟨K.vertexPoint v.1, K.vertexPoint_mem_support v.1⟩
    have hpv : p = vp := G.isEmbedding.injective heq
    have hvFace : vp ∈ faceInSupport (K := K) f := hpv ▸ hpFace
    exact v.2 ((K.vertexSupportPoint_mem_faceInSupport_iff f v.1).mp hvFace)
  · exact hqRegion (G.map_mem_region p)

/-- Every face admits one positive radius separating its compact image from all nonincident
vertices at once.  Local finiteness replaces the finite minimum used in the compact theorem. -/
theorem exists_faceVertexSeparationRadius (f : K.Face) :
    ∃ r : ℝ, 0 < r ∧
      ∀ v : K.Vertex, v ∉ K.faceVertices f →
        Disjoint (Metric.closedBall (G.vertexImage v) r)
          (Metric.cthickening r (G.map '' faceInSupport (K := K) f)) := by
  have hcompact : IsCompact (G.map '' faceInSupport (K := K) f) :=
    (isCompact_faceInSupport (K := K) f).image G.isEmbedding.continuous
  obtain ⟨r, hr, hdis⟩ :=
    (faceImage_disjoint_outsideVertexImages (G := G) f).exists_cthickenings hcompact
      (isClosed_outsideVertexImages (G := G) f)
  refine ⟨r, hr, fun v hv ↦ ?_⟩
  apply hdis.symm.mono
  · apply Metric.closedBall_subset_cthickening
    apply Set.mem_union_left
    apply Set.mem_iUnion.mpr
    exact ⟨⟨v, hv⟩, by simp [PlaneGraphRealization.vertexImageCarrier]⟩
  · exact Set.Subset.rfl

/-- A canonical positive side-separation radius for every face. -/
noncomputable def faceVertexSeparationRadius (G : K.PlaneGraphRealization)
    (f : K.Face) : ℝ :=
  Classical.choose (exists_faceVertexSeparationRadius (G := G) f)

theorem faceVertexSeparationRadius_pos (f : K.Face) :
    0 < faceVertexSeparationRadius G f :=
  (Classical.choose_spec (exists_faceVertexSeparationRadius (G := G) f)).1

theorem faceVertexSeparationRadius_separates :
    FaceVertexThickeningsSeparated G (faceVertexSeparationRadius G) := by
  intro f
  exact (Classical.choose_spec (exists_faceVertexSeparationRadius (G := G) f)).2

/-! ## The edgewise target for Moise's fine graph subdivision -/

/-- The finite family of coarse faces meeting an edge.  It contains, in particular, every face
having that edge as one of its sides. -/
def edgeMeetingFaces (K : LocallyFiniteTriangleComplex S) (e : K.Edge) : Set K.Face :=
  {f | (K.faceCarrier f ∩ K.edgeCarrier e).Nonempty}

theorem finite_edgeMeetingFaces (e : K.Edge) :
    (K.edgeMeetingFaces e).Finite := by
  exact K.locallyFinite.finite_nonempty_inter_compact
    (K.isCompact_edgeCarrier e)

theorem edgeFace_mem_edgeMeetingFaces (e : K.Edge) :
    K.edgeFace e ∈ K.edgeMeetingFaces e := by
  let v := K.edgeFirst e
  have hvEdge : K.vertexPoint v ∈ K.edgeCarrier e :=
    (K.vertexPoint_mem_edgeCarrier_iff v e).mpr (K.edgeFirst_mem e)
  have hvFace : K.vertexPoint v ∈ K.faceCarrier (K.edgeFace e) :=
    K.edgeCarrier_subset_faceCarrier e hvEdge
  exact ⟨K.vertexPoint v, hvFace, hvEdge⟩

/-- The minimum side-separation radius among the finitely many coarse faces meeting an edge.
This is the exact mesh target in Moise Chapter 6, Theorem 2: subdividing the edge until its
polygonal replacement is closer than this number preserves the side of every incident face. -/
noncomputable def edgeFaceSeparationRadius (G : K.PlaneGraphRealization)
    (e : K.Edge) : ℝ :=
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  (F.image (faceVertexSeparationRadius G)).min' (hF.image _)

theorem edgeFaceSeparationRadius_pos (e : K.Edge) :
    0 < edgeFaceSeparationRadius G e := by
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  have hmem := Finset.min'_mem (F.image (faceVertexSeparationRadius G)) (hF.image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  change 0 < (F.image (faceVertexSeparationRadius G)).min' _
  rw [← hf]
  exact faceVertexSeparationRadius_pos (G := G) f

theorem edgeFaceSeparationRadius_le_of_mem {e : K.Edge} {f : K.Face}
    (hf : f ∈ K.edgeMeetingFaces e) :
    edgeFaceSeparationRadius G e ≤ faceVertexSeparationRadius G f := by
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨f, (Set.Finite.mem_toFinset _).mpr hf, rfl⟩

theorem faceEdge_mem_edgeMeetingFaces (f : K.Face) (i : ZMod 3) :
    f ∈ K.edgeMeetingFaces (K.faceEdge f i) := by
  let v := K.edgeFirst (K.faceEdge f i)
  have hvEdge : K.vertexPoint v ∈ K.edgeCarrier (K.faceEdge f i) :=
    (K.vertexPoint_mem_edgeCarrier_iff v (K.faceEdge f i)).mpr
      (K.edgeFirst_mem (K.faceEdge f i))
  have hvFace : K.vertexPoint v ∈ K.faceCarrier f :=
    K.edgeCarrier_subset_faceCarrier_of_subset
      f (K.faceEdge f i) (K.faceEdge_subset_faceVertices f i) hvEdge
  exact ⟨K.vertexPoint v, hvFace, hvEdge⟩

/-- Edgewise diameter control below the incident-face minimum implies the facewise boundary
closeness consumed by the side-preservation theorem. -/
theorem faceBoundariesClose_of_edgeFaceSeparation_control
    (hsmall : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeFaceSeparationRadius G e) :
    FaceBoundariesClose G (faceVertexSeparationRadius G) := by
  intro f q
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  let e := K.faceEdge f i
  have hqe : (K.faceBoundaryLift f q).1 ∈ edgeInSupport (K := K) e :=
    K.faceBoundarySupportPoint_mem_edge f i q hi
  calc
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
        (faceOriginalMap G f q.1) =
        dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) := by
            congr 1
            change faceOriginalMap G f
                (⟨q.1, standardFaceBoundary_mem_region q⟩ : standardFaceRegion).1 = _
            rw [faceOriginalMap_apply]
            rfl
    _ < 2 * Metric.diam (G.edgeImage e) := by
      rw [G.graphReplacementMap_eq e _ hqe]
      exact G.replacementEdgeMap_dist_lt_two_mul_edgeImage_diam e
        ⟨(K.faceBoundaryLift f q).1, hqe⟩
    _ < edgeFaceSeparationRadius G e := hsmall e
    _ ≤ faceVertexSeparationRadius G f :=
      edgeFaceSeparationRadius_le_of_mem (G := G)
        (K.faceEdge_mem_edgeMeetingFaces f i)

/-- The exact facewise estimate needed to control a Schoenflies filling.  Every point of a
replacement boundary is compared first with its original boundary point and then with an
arbitrary point of the same source face. -/
def FaceBoundariesControlled (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (p : K.support),
    p ∈ faceInSupport (K := K) f → ∀ q : StandardFaceBoundary,
      dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤ phi p

/-- Separate the graph approximation allowance from the oscillation of the original map on one
face.  This is the form discharged by an adaptive mesh. -/
def FaceOscillationControlled (G : K.PlaneGraphRealization)
    (rho phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (p : K.support),
    p ∈ faceInSupport (K := K) f → ∀ q : StandardFaceBoundary,
      rho (K.faceBoundaryLift f q).1 +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤ phi p

/-- Edgewise graph control plus within-face oscillation gives the exact boundary estimate used
by every Schoenflies filling. -/
theorem faceBoundariesControlled_of_graph_and_oscillation
    {rho phi : K.support → ℝ} (hgraph : G.EdgeImagesControlled rho)
    (hface : FaceOscillationControlled G rho phi) :
    FaceBoundariesControlled G phi := by
  intro f p hp q
  calc
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤
        rho (K.faceBoundaryLift f q).1 +
          dist (G.map (K.faceBoundaryLift f q).1) (G.map p) :=
      add_le_add
        (G.isPhiApproximation_graphReplacementMap hgraph
          (K.faceBoundaryLift f q)).le le_rfl
    _ ≤ phi p := hface f p hp q

/-- Under facewise control, the entire polygonal disk selected by Schoenflies lies in the
prescribed ball about every point of its source face. -/
theorem facePolygonalCircle_closedRegion_subset_closedBall
    {phi : K.support → ℝ} (hcontrol : FaceBoundariesControlled G phi)
    (f : K.Face) (p : K.support) (hp : p ∈ faceInSupport (K := K) f) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆
      Metric.closedBall (G.map p) (phi p) := by
  apply (K.facePolygonalCircle (G := G) f).closedRegion_subset_closedBall_of_carrier_subset
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  rw [Metric.mem_closedBall, K.faceBoundaryMap_apply (G := G) f q']
  exact (dist_triangle _ (G.map (K.faceBoundaryLift f q').1) _).trans
    (hcontrol f p hp q')

/-- Pointwise control of the global cellwise replacement. -/
theorem polygonalReplacementMap_dist_le
    (H : K.CellwiseCompatibility G) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi) (p : K.support) :
    dist (K.polygonalReplacementMap H p).1.1 (G.map p) ≤ phi p := by
  let f := K.supportFace p
  let x := K.supportFacePoint p
  have hpFace : p ∈ faceInSupport (K := K) f := by
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  have hmapFace : (K.polygonalReplacementMap H p).1.1 ∈
      (K.facePolygonalCircle (G := G) f).closedRegion := by
    rw [show p = faceToSupport (K := K) f x by
      apply Subtype.ext
      exact (K.faceMap_supportFacePoint p).symm,
      K.polygonalReplacementMap_faceToSupport H f x]
    rw [← (K.facePLFilling (G := G) f).range_faceMap]
    exact Set.mem_range_self x
  exact Metric.mem_closedBall.mp
    (facePolygonalCircle_closedRegion_subset_closedBall hcontrol f p hpFace hmapFace)

/-- A pointwise tolerance separates nonincident vertices from every source face. -/
def SeparatesVerticesFromFaces (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    ∀ p ∈ faceInSupport (K := K) f,
      phi p < dist (G.vertexImage v) (G.map p)

/-- Any pointwise smaller tolerance inherits vertex-to-face separation. -/
theorem SeparatesVerticesFromFaces.mono {phi psi : K.support → ℝ}
    (hsep : SeparatesVerticesFromFaces G phi) (hle : ∀ p, psi p ≤ phi p) :
    SeparatesVerticesFromFaces G psi :=
  fun f v hvf p hp ↦ (hle p).trans_lt (hsep f v hvf p hp)

/-- Local finiteness leaves only finitely many faces through any one support point. -/
theorem finite_setOf_mem_faceInSupport (p : K.support) :
    {f : K.Face | p ∈ faceInSupport (K := K) f}.Finite :=
  K.locallyFinite_faceInSupport.point_finite p

theorem mem_faceInSupport_supportFace (p : K.support) :
    p ∈ faceInSupport (K := K) (K.supportFace p) := by
  rw [K.faceInSupport_eq_preimage]
  exact K.mem_faceCarrier_supportFace p

/-- The finite set of maximal faces through one support point. -/
noncomputable def facesContaining (p : K.support) : Finset K.Face :=
  (finite_setOf_mem_faceInSupport (K := K) p).toFinset

theorem mem_facesContaining {p : K.support} {f : K.Face} :
    f ∈ facesContaining (K := K) p ↔ p ∈ faceInSupport (K := K) f :=
  Set.Finite.mem_toFinset _

theorem facesContaining_nonempty (p : K.support) :
    (facesContaining (K := K) p).Nonempty :=
  ⟨K.supportFace p, mem_facesContaining.mpr (mem_faceInSupport_supportFace p)⟩

/-- The pointwise vertex-to-face separation control: the smallest per-face separation radius
among the finitely many faces through the point.  This is the locally finite analogue of the
finite `exists_uniform_vertex_face_separation`: positive at every point, strongly positive on
compact sets, and smaller than the distance from any face through the point to any vertex not
incident to that face. -/
noncomputable def vertexSeparationControl (G : K.PlaneGraphRealization)
    (p : K.support) : ℝ :=
  ((facesContaining (K := K) p).image (faceVertexSeparationRadius G)).min'
    ((facesContaining_nonempty p).image _)

theorem vertexSeparationControl_le {p : K.support} {f : K.Face}
    (hf : p ∈ faceInSupport (K := K) f) :
    vertexSeparationControl G p ≤ faceVertexSeparationRadius G f :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (mem_facesContaining.mpr hf))

theorem vertexSeparationControl_pos (p : K.support) :
    0 < vertexSeparationControl G p := by
  have hmem := Finset.min'_mem
    ((facesContaining (K := K) p).image (faceVertexSeparationRadius G))
    ((facesContaining_nonempty p).image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [vertexSeparationControl, ← hf]
  exact faceVertexSeparationRadius_pos (G := G) f

/-- The canonical control separates every nonincident vertex from every face: each face image
is a positive thickening away from the vertex, and the control is below that radius. -/
theorem separatesVerticesFromFaces_vertexSeparationControl :
    SeparatesVerticesFromFaces G (vertexSeparationControl G) := by
  intro f v hvf p hp
  have hgap : faceVertexSeparationRadius G f < dist (G.vertexImage v) (G.map p) := by
    by_contra hle
    push Not at hle
    have hball : G.map p ∈
        Metric.closedBall (G.vertexImage v) (faceVertexSeparationRadius G f) := by
      rw [Metric.mem_closedBall, dist_comm]
      exact hle
    have hthick : G.map p ∈
        Metric.cthickening (faceVertexSeparationRadius G f)
          (G.map '' faceInSupport (K := K) f) :=
      Metric.self_subset_cthickening _ ⟨p, hp, rfl⟩
    exact Set.disjoint_left.mp
      (faceVertexSeparationRadius_separates (G := G) f v hvf) hball hthick
  exact (vertexSeparationControl_le hp).trans_lt hgap

/-- On every compact set the canonical separation control has a positive lower bound: only
finitely many faces meet the compact set, and each contributes a positive radius. -/
theorem stronglyPositiveOn_vertexSeparationControl :
    StronglyPositiveOn Set.univ (vertexSeparationControl G) := by
  intro C hC _
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  have hfin : {f : K.Face | (faceInSupport (K := K) f ∩ C).Nonempty}.Finite :=
    K.locallyFinite_faceInSupport.finite_nonempty_inter_compact hC
  obtain ⟨p₀, hp₀⟩ := hCne
  have hFne : hfin.toFinset.Nonempty :=
    ⟨K.supportFace p₀, (Set.Finite.mem_toFinset _).mpr
      ⟨p₀, mem_faceInSupport_supportFace p₀, hp₀⟩⟩
  refine ⟨(hfin.toFinset.image (faceVertexSeparationRadius G)).min' (hFne.image _),
    ?_, ?_⟩
  · have hmem := Finset.min'_mem
      (hfin.toFinset.image (faceVertexSeparationRadius G)) (hFne.image _)
    obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
    rw [← hf]
    exact faceVertexSeparationRadius_pos (G := G) f
  · intro p hp
    apply Finset.le_min'
    intro r hr
    obtain ⟨f, hfp, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.min'_le
    apply Finset.mem_image_of_mem
    exact (Set.Finite.mem_toFinset _).mpr
      ⟨p, mem_facesContaining.mp hfp, hp⟩

/-- The vertex-side compatibility condition used in Moise's side-preservation argument. -/
def FaceFillingsVerticesAvoidClosedRegions (G : K.PlaneGraphRealization) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    G.vertexImage v ∉ (K.facePolygonalCircle (G := G) f).closedRegion

/-- Facewise metric control and vertex-to-face separation keep every nonincident vertex outside
the selected polygonal closed disk. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_control
    {phi : K.support → ℝ} (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf hvClosed
  obtain ⟨z, hz⟩ := K.faceCarrier_nonempty f
  obtain ⟨x, rfl⟩ := hz
  let p : K.support := faceToSupport (K := K) f x
  have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self x
  have hball := facePolygonalCircle_closedRegion_subset_closedBall
    hcontrol f p hp hvClosed
  have hle : dist (G.vertexImage v) (G.map p) ≤ phi p :=
    Metric.mem_closedBall.mp hball
  exact (not_lt_of_ge hle) (hsep f v hvf p hp)

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification16_block_01
/- END ClassificationOfSurfaces.Moise.LocallyFinitePLApproximation -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteSidePreservation | 5bf1661e51a1bcb96857928ebe27669444b61c458efe4dec5a916256ef28d072 -/
section schottkyclassification16_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Side preservation for locally finite face fillings

The metric estimates of `LocallyFinitePLApproximation` put nonincident vertices outside each
replacement polygon.  This file propagates that information along every replacement edge.  The
argument is the same connected-side argument used in Moise Chapter 6: an edge can cross a
polygonal boundary only where the corresponding abstract edge meets the face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-- The canonical boundary lift belongs to the face whose boundary it parametrizes. -/
theorem faceBoundaryLift_mem_faceInSupport (f : K.Face) (q : StandardFaceBoundary) :
    (K.faceBoundaryLift f q).1 ∈ faceInSupport (K := K) f := by
  exact Set.mem_range_self
    ((K.facePlaneHomeomorph f).symm
      ⟨q.1, standardFaceBoundary_mem_region q⟩)

/-- A replacement graph pointwise finer than the canonical vertex-separation control is
facewise close at the canonical per-face separation radii.  This is the bridge from a
tolerance-parametrized one-skeleton replacement to the side-preservation entry
`FaceBoundariesClose G (faceVertexSeparationRadius G)`. -/
theorem faceBoundariesClose_of_lt_vertexSeparationControl
    (harc : ∀ p : oneSkeletonInSupport (K := K),
      dist (G.graphReplacementMap p) (G.map p.1) < vertexSeparationControl G p.1) :
    FaceBoundariesClose G (faceVertexSeparationRadius G) := by
  intro f q
  have heq : faceOriginalMap G f q.1 = G.map (K.faceBoundaryLift f q).1 := by
    change faceOriginalMap G f
        (⟨q.1, standardFaceBoundary_mem_region q⟩ : standardFaceRegion).1 = _
    rw [faceOriginalMap_apply]
    rfl
  rw [heq]
  exact (harc (K.faceBoundaryLift f q)).trans_le
    (vertexSeparationControl_le (faceBoundaryLift_mem_faceInSupport f q))

/-- Every selected face boundary is part of the single global replacement graph. -/
theorem facePolygonalCircle_carrier_subset_graphReplacement (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).carrier ⊆
      Set.range G.graphReplacementMap := by
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  exact ⟨K.faceBoundaryLift f q',
    (K.faceBoundaryMap_apply (G := G) f q').symm⟩

/-- If a replacement-graph point lies on one face polygon, its source lies in that face. -/
theorem mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
    (f : K.Face) (p : oneSkeletonInSupport (K := K))
    (hp : G.graphReplacementMap p ∈
      (K.facePolygonalCircle (G := G) f).carrier) :
    p.1 ∈ faceInSupport (K := K) f := by
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hp
  obtain ⟨q, hq, hqmap⟩ := hp
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have heq : G.graphReplacementMap p =
      G.graphReplacementMap (K.faceBoundaryLift f q') := by
    rw [← K.faceBoundaryMap_apply (G := G) f q']
    exact hqmap.symm
  have hpq := G.graphReplacementMap_injective heq
  rw [hpq]
  exact K.faceBoundaryLift_mem_faceInSupport f q'

/-- Include the interval parametrization of an edge in the source one-skeleton. -/
noncomputable def edgePathInOneSkeleton (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    oneSkeletonInSupport (K := K) :=
  ⟨edgePathInSupport (K := K) e r,
    Set.mem_iUnion.mpr ⟨e, by
      rw [← range_edgePathInSupport (K := K) e]
      exact Set.mem_range_self r⟩⟩

theorem continuous_edgePathInOneSkeleton (e : K.Edge) :
    Continuous (edgePathInOneSkeleton (K := K) e) := by
  apply Continuous.subtype_mk
  exact continuous_edgePathInSupport (K := K) e

@[simp] theorem edgePathInOneSkeleton_val (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (edgePathInOneSkeleton (K := K) e r).1 = edgePathInSupport (K := K) e r := rfl

/-- An edge contained in a face has all its support points in that face. -/
theorem edgeInSupport_subset_faceInSupport (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    edgeInSupport (K := K) e ⊆ faceInSupport (K := K) f := by
  rintro p ⟨q, rfl⟩
  obtain ⟨x, hx⟩ := q.2
  let y := stdSimplex.map
    (fun v : {v // v ∈ e.1} ↦
      (⟨v.1, hef v.2⟩ : {w // w ∈ K.faceVertices f})) x
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change K.faceMap f y = q.1
  exact (K.edgeMap_eq_faceMap e f hef x).symm.trans hx

/-- If the second endpoint of an edge is absent from a face, an edge-path point in that face
must have parameter zero. -/
theorem edgePathInSupport_parameter_eq_zero_of_mem_face
    (f : K.Face) (e : K.Edge) (r : Set.Icc (0 : ℝ) 1)
    (hsecond : K.edgeSecond e ∉ K.faceVertices f)
    (hr : edgePathInSupport (K := K) e r ∈ faceInSupport (K := K) f) :
    r.1 = 0 := by
  obtain ⟨y, hy⟩ := hr
  have hcoords := K.faceMap_eq_iff.mp (congrArg Subtype.val hy).symm
  have hc := congrFun hcoords (K.edgeSecond e)
  rw [K.extendFaceCoordinates_map_edgeVertexToFace e,
    extendFaceCoordinates_of_mem e.1 _ (K.edgeSecond_mem e),
    extendFaceCoordinates_of_notMem (K.faceVertices f) y hsecond,
    K.edgeSimplexPath_apply_second] at hc
  exact hc

/-- If the first endpoint of an edge is absent from a face, an edge-path point in that face must
have parameter one. -/
theorem edgePathInSupport_parameter_eq_one_of_mem_face
    (f : K.Face) (e : K.Edge) (r : Set.Icc (0 : ℝ) 1)
    (hfirst : K.edgeFirst e ∉ K.faceVertices f)
    (hr : edgePathInSupport (K := K) e r ∈ faceInSupport (K := K) f) :
    r.1 = 1 := by
  obtain ⟨y, hy⟩ := hr
  have hcoords := K.faceMap_eq_iff.mp (congrArg Subtype.val hy).symm
  have hc := congrFun hcoords (K.edgeFirst e)
  rw [K.extendFaceCoordinates_map_edgeVertexToFace e,
    extendFaceCoordinates_of_mem e.1 _ (K.edgeFirst_mem e),
    extendFaceCoordinates_of_notMem (K.faceVertices f) y hfirst,
    K.edgeSimplexPath_apply_first] at hc
  linarith

/-- The replacement of an abstract edge contained in a face lies on that face's polygon. -/
theorem graphReplacement_mem_facePolygonalCircle_of_edge_subset
    (f : K.Face) (e : K.Edge) (p : oneSkeletonInSupport (K := K))
    (hp : p.1 ∈ edgeInSupport (K := K) e)
    (hef : e.1 ⊆ K.faceVertices f) :
    G.graphReplacementMap p ∈
      (K.facePolygonalCircle (G := G) f).carrier := by
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset f e hef
  rw [K.facePolygonalCircle_carrier (G := G) f]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hp' : p.1 ∈ edgeInSupport (K := K) (K.faceEdge f i) := by
    simpa only [hi] using hp
  rw [G.graphReplacementMap_eq (K.faceEdge f i) p hp',
    ← G.range_replacementEdgeMap (K.faceEdge f i)]
  exact Set.mem_range_self
    (⟨p.1, hp'⟩ : edgeInSupport (K := K) (K.faceEdge f i))

/-- The simultaneous graph replacement fixes every abstract vertex. -/
theorem graphReplacementMap_vertex (v : K.Vertex) :
    ∃ p : oneSkeletonInSupport (K := K), p.1.1 = K.vertexPoint v ∧
      G.graphReplacementMap p = G.vertexImage v := by
  obtain ⟨f, hvf⟩ := K.vertex_used v
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f hvf
  let e := K.faceEdge f i
  have hve : v ∈ e.1 := by
    rw [K.faceEdge_val, ← hi]
    simp
  let s : K.support := ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩
  have hse : s ∈ edgeInSupport (K := K) e := by
    rw [edgeInSupport_eq_preimage (K := K)]
    exact (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve
  let p : oneSkeletonInSupport (K := K) :=
    ⟨s, Set.mem_iUnion.mpr ⟨e, hse⟩⟩
  refine ⟨p, rfl, ?_⟩
  rw [G.graphReplacementMap_eq e p hse]
  exact G.replacementEdgeMap_vertex e v hve

/-- A vertex of a face maps to that face's replacement polygon. -/
theorem graphReplacement_vertex_mem_facePolygonalCircle
    (f : K.Face) (v : K.Vertex) (hvf : v ∈ K.faceVertices f) :
    G.vertexImage v ∈ (K.facePolygonalCircle (G := G) f).carrier := by
  obtain ⟨p, hpv, hpmap⟩ := graphReplacementMap_vertex (G := G) v
  rw [← hpmap]
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f hvf
  let e := K.faceEdge f i
  have hpe : p.1 ∈ edgeInSupport (K := K) e := by
    rw [edgeInSupport_eq_preimage (K := K)]
    change p.1.1 ∈ K.edgeCarrier e
    rw [hpv]
    apply (K.vertexPoint_mem_edgeCarrier_iff v e).mpr
    rw [K.faceEdge_val, ← hi]
    simp
  exact graphReplacement_mem_facePolygonalCircle_of_edge_subset (G := G) f e p hpe
    (K.faceEdge_subset_faceVertices f i)

theorem graphReplacementMap_edgePathInOneSkeleton_zero (e : K.Edge) :
    G.graphReplacementMap
        (edgePathInOneSkeleton (K := K) e ⟨0, by simp⟩) =
      G.vertexImage (K.edgeFirst e) := by
  obtain ⟨p, hp, hmap⟩ := graphReplacementMap_vertex (G := G) (K.edgeFirst e)
  rw [← hmap]
  apply congrArg G.graphReplacementMap
  apply Subtype.ext
  apply Subtype.ext
  exact (K.edgePath_zero e).trans hp.symm

theorem graphReplacementMap_edgePathInOneSkeleton_one (e : K.Edge) :
    G.graphReplacementMap
        (edgePathInOneSkeleton (K := K) e ⟨1, by simp⟩) =
      G.vertexImage (K.edgeSecond e) := by
  obtain ⟨p, hp, hmap⟩ := graphReplacementMap_vertex (G := G) (K.edgeSecond e)
  rw [← hmap]
  apply congrArg G.graphReplacementMap
  apply Subtype.ext
  apply Subtype.ext
  exact (K.edgePath_one e).trans hp.symm

/-- Graph-side compatibility required for coherent cellwise assembly. -/
def FaceFillingsGraphAvoidInteriors (G : K.PlaneGraphRealization) : Prop :=
  ∀ f : K.Face,
    Disjoint (Set.range G.graphReplacementMap)
      (K.facePolygonalCircle (G := G) f).interiorRegion

/-- Facewise closeness and vertex-to-face separation put every nonincident vertex on the
unbounded side of the replacement polygon.  This is the locally finite form of Moise's actual
Chapter 6 argument: bounded Tietze extension fills the close boundary while avoiding the outside
vertex, and no-retraction detects the unbounded side. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_close
    {r : K.Face → ℝ} (hr : ∀ f, 0 < r f)
    (hsep : FaceVertexThickeningsSeparated G r)
    (hclose : FaceBoundariesClose G r) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf
  let b := K.faceBoundaryMap (G := G) f
  let hface := faceOriginalMap G f
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap (G := G) f
  have hhface : ContinuousOn hface standardFaceRegion :=
    continuousOn_faceOriginalMap (G := G) f
  have hbclose : ∀ p ∈ frontier standardFaceRegion,
      dist (b p) (hface p) < r f := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    change dist (K.faceBoundaryMap (G := G) f p)
      (faceOriginalMap G f p) < r f
    rw [K.faceBoundaryMap_apply (G := G) f q]
    exact hclose f q
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed (hr f)
      hbcont hhface hbclose
  have hvAvoid : G.vertexImage v ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : G.vertexImage v ∈
        Metric.closedBall (G.vertexImage v) (r f) :=
      Metric.mem_closedBall_self (hr f).le
    have hFthick : F p ∈
        Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f) := by
      apply Metric.mem_cthickening_of_dist_le (F p) (hface p) (r f)
        (G.map '' faceInSupport (K := K) f)
      · exact faceOriginalMap_mem_face_image (G := G) f ⟨p, hp⟩
      · exact hFclose p hp
    exact Set.disjoint_left.mp (hsep f v hvf) hvBall (hFp ▸ hFthick)
  have hvExterior : G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
    apply (K.facePolygonalCircle (G := G) f).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle (G := G) f).disjoint_closedRegion_exteriorRegion
      hvClosed hvExterior

/-- Parametrization-independent form of `faceFillingsVerticesAvoidClosedRegions_of_close`: the
comparison map on the standard region may be ANY continuous map whose values stay within half
the separation radius of the original face image, and which is within half that radius of the
replacement boundary on the frontier.  This absorbs the parameter misalignment between the
replacement arcs' `Path.trans` splits and the original edge trims: an aligned comparison built
from `CentralPolygonalArc.curve_close` can discharge the closeness at the approximation-control
scale, which the crude same-parameter comparison with `faceOriginalMap` cannot. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_comparison
    {r : K.Face → ℝ} (hr : ∀ f, 0 < r f)
    (hsep : FaceVertexThickeningsSeparated G r)
    (comp : K.Face → Plane → Plane)
    (hcompCont : ∀ f, ContinuousOn (comp f) standardFaceRegion)
    (hcompMem : ∀ (f : K.Face), ∀ p ∈ standardFaceRegion,
      comp f p ∈ Metric.cthickening (r f / 2) (G.map '' faceInSupport (K := K) f))
    (hclose : ∀ (f : K.Face) (q : StandardFaceBoundary),
      dist (G.graphReplacementMap (K.faceBoundaryLift f q)) (comp f q.1) < r f / 2) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf
  let b := K.faceBoundaryMap (G := G) f
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap (G := G) f
  have hbclose : ∀ p ∈ frontier standardFaceRegion,
      dist (b p) (comp f p) < r f / 2 := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    change dist (K.faceBoundaryMap (G := G) f p) (comp f p) < r f / 2
    rw [K.faceBoundaryMap_apply (G := G) f q]
    exact hclose f q
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed (half_pos (hr f))
      hbcont (hcompCont f) hbclose
  have hvAvoid : G.vertexImage v ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : G.vertexImage v ∈
        Metric.closedBall (G.vertexImage v) (r f) :=
      Metric.mem_closedBall_self (hr f).le
    have hFhalf : F p ∈ Metric.cthickening (r f / 2)
        (Metric.cthickening (r f / 2) (G.map '' faceInSupport (K := K) f)) :=
      Metric.mem_cthickening_of_dist_le (F p) (comp f p) (r f / 2) _
        (hcompMem f p hp) (hFclose p hp)
    have hFthick : F p ∈
        Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f) := by
      have hmem := Metric.cthickening_cthickening_subset
        (half_pos (hr f)).le (half_pos (hr f)).le
        (G.map '' faceInSupport (K := K) f) hFhalf
      rwa [add_halves] at hmem
    exact Set.disjoint_left.mp (hsep f v hvf) hvBall (hFp ▸ hFthick)
  have hvExterior : G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
    apply (K.facePolygonalCircle (G := G) f).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle (G := G) f).disjoint_closedRegion_exteriorRegion
      hvClosed hvExterior

/-- A nonincident vertex outside the polygonal closed disk lies in its unbounded component. -/
theorem graphReplacement_vertex_mem_exterior
    (hvertices : FaceFillingsVerticesAvoidClosedRegions G)
    (f : K.Face) (v : K.Vertex) (hvf : v ∉ K.faceVertices f) :
    G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
  let J := K.facePolygonalCircle (G := G) f
  have hnotClosed := hvertices f v hvf
  have hnotInterior : G.vertexImage v ∉ J.interiorRegion := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inl hv
  have hnotCarrier : G.vertexImage v ∉ J.carrier := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inr hv
  have hoff : G.vertexImage v ∈ J.carrierᶜ := hnotCarrier
  rw [← J.interior_union_exterior] at hoff
  exact hoff.resolve_left hnotInterior

/-- Moise's vertex-side condition propagates along every edge: the complete simultaneous
replacement graph avoids the bounded interior selected for each face. -/
theorem faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (hvertices : FaceFillingsVerticesAvoidClosedRegions G) :
    FaceFillingsGraphAvoidInteriors G := by
  intro f
  let J := K.facePolygonalCircle (G := G) f
  have hinteriorCarrier : Disjoint J.interiorRegion J.carrier := by
    rw [← J.interior_closedRegion, ← J.frontier_closedRegion]
    exact disjoint_interior_frontier
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ hpInterior
  obtain ⟨e, hpe⟩ := Set.mem_iUnion.mp p.2
  by_cases hef : e.1 ⊆ K.faceVertices f
  · have hpCarrier := graphReplacement_mem_facePolygonalCircle_of_edge_subset
      (G := G) f e p hpe hef
    exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
  let I := Set.Icc (0 : ℝ) 1
  let z0 : I := ⟨0, by simp [I]⟩
  let z1 : I := ⟨1, by simp [I]⟩
  let gpath : I → Plane := fun r ↦
    G.graphReplacementMap (edgePathInOneSkeleton (K := K) e r)
  have hgpath : Continuous gpath := by
    exact G.continuous_graphReplacementMap.comp
      (continuous_edgePathInOneSkeleton (K := K) e)
  have hoffCarrier {A : Set I}
      (houtside : ∀ r ∈ A,
        edgePathInSupport (K := K) e r ∉ faceInSupport (K := K) f) :
      Set.MapsTo gpath A J.carrierᶜ := by
    intro r hr hcarrier
    exact houtside r hr
      (mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
        (G := G) f (edgePathInOneSkeleton (K := K) e r) hcarrier)
  let r : I := (G.edgePathInSupportHomeomorph e).symm ⟨p.1, hpe⟩
  have hrPath : edgePathInSupport (K := K) e r = p.1 := by
    exact congrArg Subtype.val
      ((G.edgePathInSupportHomeomorph e).apply_symm_apply ⟨p.1, hpe⟩)
  have hpPath : edgePathInOneSkeleton (K := K) e r = p := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val hrPath
  have hmapPath : gpath r = G.graphReplacementMap p := congrArg G.graphReplacementMap hpPath
  by_cases hfirst : K.edgeFirst e ∈ K.faceVertices f
  · have hsecond : K.edgeSecond e ∉ K.faceVertices f := by
      intro hsecond
      apply hef
      rw [K.edge_eq_pair e]
      exact Finset.insert_subset_iff.mpr
        ⟨hfirst, Finset.singleton_subset_iff.mpr hsecond⟩
    by_cases hr0 : r.1 = 0
    · have hrz : r = z0 := Subtype.ext hr0
      have hpCarrier : G.graphReplacementMap p ∈ J.carrier := by
        rw [← hmapPath, hrz]
        simpa only [gpath, z0, J,
          graphReplacementMap_edgePathInOneSkeleton_zero] using
            graphReplacement_vertex_mem_facePolygonalCircle
              (G := G) f (K.edgeFirst e) hfirst
      exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
    · let A : Set I := Set.Ioc z0 z1
      have hAoutside : ∀ s ∈ A,
          edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
        intro s hs hsFace
        have hs0 := edgePathInSupport_parameter_eq_zero_of_mem_face
          f e s hsecond hsFace
        exact (ne_of_gt (show (0 : ℝ) < s.1 by exact_mod_cast hs.1)) hs0
      have hz1Exterior : gpath z1 ∈ J.exteriorRegion := by
        simpa only [gpath, z1, J,
          graphReplacementMap_edgePathInOneSkeleton_one] using
          graphReplacement_vertex_mem_exterior (G := G) hvertices f
            (K.edgeSecond e) hsecond
      have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ioc
          hgpath.continuousOn (hoffCarrier hAoutside)
          ⟨z1, by simp [A, z0, z1], hz1Exterior⟩
      have hrA : r ∈ A := by
        constructor
        · change (0 : ℝ) < r.1
          exact lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        · exact r.2.2
      have hrExterior := hAExterior hrA
      rw [hmapPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior
  · by_cases hsecond : K.edgeSecond e ∈ K.faceVertices f
    · by_cases hr1 : r.1 = 1
      · have hrz : r = z1 := Subtype.ext hr1
        have hpCarrier : G.graphReplacementMap p ∈ J.carrier := by
          rw [← hmapPath, hrz]
          simpa only [gpath, z1, J,
            graphReplacementMap_edgePathInOneSkeleton_one] using
              graphReplacement_vertex_mem_facePolygonalCircle
                (G := G) f (K.edgeSecond e) hsecond
        exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
      · let A : Set I := Set.Ico z0 z1
        have hAoutside : ∀ s ∈ A,
            edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
          intro s hs hsFace
          have hs1 := edgePathInSupport_parameter_eq_one_of_mem_face
            f e s hfirst hsFace
          exact (ne_of_lt (show s.1 < (1 : ℝ) by exact_mod_cast hs.2)) hs1
        have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
          simpa only [gpath, z0, J,
            graphReplacementMap_edgePathInOneSkeleton_zero] using
            graphReplacement_vertex_mem_exterior (G := G) hvertices f
              (K.edgeFirst e) hfirst
        have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
          J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ico
            hgpath.continuousOn (hoffCarrier hAoutside)
            ⟨z0, by simp [A, z0, z1], hz0Exterior⟩
        have hrA : r ∈ A := by
          constructor
          · exact r.2.1
          · change r.1 < (1 : ℝ)
            exact lt_of_le_of_ne r.2.2 hr1
        have hrExterior := hAExterior hrA
        rw [hmapPath] at hrExterior
        exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior
    · have hAllOutside : ∀ s : I,
          edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
        intro s hsFace
        have hs0 := edgePathInSupport_parameter_eq_zero_of_mem_face
          f e s hsecond hsFace
        have hs1 := edgePathInSupport_parameter_eq_one_of_mem_face
          f e s hfirst hsFace
        linarith
      have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
        simpa only [gpath, z0, J,
          graphReplacementMap_edgePathInOneSkeleton_zero] using
          graphReplacement_vertex_mem_exterior (G := G) hvertices f
            (K.edgeFirst e) hfirst
      have hAllExterior : Set.MapsTo gpath Set.univ J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_univ
          hgpath.continuousOn (hoffCarrier fun s _ ↦ hAllOutside s)
          ⟨z0, Set.mem_univ _, hz0Exterior⟩
      have hrExterior := hAllExterior (Set.mem_univ r)
      rw [hmapPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior

/-- Once the replacement graph stays out of every selected bounded component, distinct filled
face interiors are disjoint.  A vertex of the second face not belonging to the first supplies the
strict side witness required by polygonal Jordan separation. -/
theorem disjoint_facePolygonalCircle_interiors
    (hfaces : Function.Injective K.faceVertices)
    (hside : FaceFillingsGraphAvoidInteriors G)
    (f g : K.Face) (hfg : f ≠ g) :
    Disjoint
      (K.facePolygonalCircle (G := G) f).interiorRegion
      (K.facePolygonalCircle (G := G) g).interiorRegion := by
  classical
  have hnotSubset : ¬K.faceVertices g ⊆ K.faceVertices f := by
    intro hsub
    have heq : K.faceVertices g = K.faceVertices f :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [K.faceVertices_card g, K.faceVertices_card f])
    exact hfg (hfaces heq.symm)
  obtain ⟨w, hwg, hwnf⟩ := Finset.not_subset.mp hnotSubset
  have hwCarrierG : G.vertexImage w ∈
      (K.facePolygonalCircle (G := G) g).carrier :=
    graphReplacement_vertex_mem_facePolygonalCircle (G := G) g w hwg
  have hwNotCarrierF : G.vertexImage w ∉
      (K.facePolygonalCircle (G := G) f).carrier := by
    intro hwCarrierF
    obtain ⟨p, hpw, hpmap⟩ := graphReplacementMap_vertex (G := G) w
    have hpFace : p.1 ∈ faceInSupport (K := K) f :=
      mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
        (G := G) f p (by simpa only [hpmap] using hwCarrierF)
    rw [K.faceInSupport_eq_preimage] at hpFace
    change p.1.1 ∈ K.faceCarrier f at hpFace
    have hwFace : K.vertexPoint w ∈ K.faceCarrier f := by
      rw [hpw] at hpFace
      exact hpFace
    exact hwnf ((K.vertexPoint_mem_faceCarrier_iff f w).mp hwFace)
  apply (K.facePolygonalCircle (G := G) f).disjoint_interiorRegion_of_boundary_avoidance
    (K.facePolygonalCircle (G := G) g)
  · exact (hside g).mono_left
      (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) f)
  · exact (hside f).mono_left
      (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) g)
  · exact ⟨G.vertexImage w, hwCarrierG, hwNotCarrierF⟩

/-- The quantitative Chapter 6 hypotheses, together with local finiteness of the selected closed
polygonal disks, produce the complete compatibility package needed for cellwise assembly. -/
theorem cellwiseCompatibility_of_control
    (hfaces : Function.Injective K.faceVertices)
    {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_control
    (G := G) hcontrol hsep
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

/-- Moise's original side-control interface: facewise graph closeness below the canonical
vertex-to-face separation radius gives the compatibility package for all Schoenflies fillings.
Unlike `cellwiseCompatibility_of_control`, this formulation does not force one pointwise
tolerance to serve every face incident to a source point. -/
theorem cellwiseCompatibility_of_facewise_close
    (hfaces : Function.Injective K.faceVertices)
    (hclose : FaceBoundariesClose G (faceVertexSeparationRadius G))
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_close
    (G := G) (faceVertexSeparationRadius_pos (G := G))
      (faceVertexSeparationRadius_separates (G := G)) hclose
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

/-- The compatibility package from a parametrization-independent comparison map at the
canonical separation radii.  This is the entry matched to the locally finite replacement arcs:
their `curve_close` tracking is stated against the trimmed original curve, not against the
`Path.trans` parameter, so only a reparametrized comparison can be discharged at the
approximation-control scale. -/
theorem cellwiseCompatibility_of_comparison
    (hfaces : Function.Injective K.faceVertices)
    (comp : K.Face → Plane → Plane)
    (hcompCont : ∀ f, ContinuousOn (comp f) standardFaceRegion)
    (hcompMem : ∀ (f : K.Face), ∀ p ∈ standardFaceRegion,
      comp f p ∈ Metric.cthickening (faceVertexSeparationRadius G f / 2)
        (G.map '' faceInSupport (K := K) f))
    (hclose : ∀ (f : K.Face) (q : StandardFaceBoundary),
      dist (G.graphReplacementMap (K.faceBoundaryLift f q)) (comp f q.1) <
        faceVertexSeparationRadius G f / 2)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_comparison
    (G := G) (faceVertexSeparationRadius_pos (G := G))
      (faceVertexSeparationRadius_separates (G := G)) comp hcompCont hcompMem hclose
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification16_block_02
/- END ClassificationOfSurfaces.Moise.LocallyFiniteSidePreservation -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation | 22be3ca46711c3cd750b81e3c5c3be4cacfd4974886c39692cdd162557b0e350 -/
section schottkyclassification16_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Controlled locally finite PL replacement

This file packages the completed cellwise part of Moise Chapter 6, Theorem 3.  The graph-level
construction supplies quantitative face control and separation.  Polygonal Schoenflies then
fills every face, and local finiteness glues the fillings into a homeomorphism of supports.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] [T2Space S]
variable {K : LocallyFiniteTriangleComplex S}

/-- The closed metric controls used for a replacement are contained in the permitted open
region. -/
def PlaneGraphRealization.ControlsStayInRegion (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ p, Metric.closedBall (G.map p) (phi p) ⊆ G.region

/-- A global bound and a frontier-relative bound sufficient to control a locally finite
family of polygonal face fillings. -/
def PlaneGraphRealization.UniformFrontierControl (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  (∀ p, phi p ≤ 1) ∧
    ∀ (_ : G.regionᶜ.Nonempty) (p : K.support),
      phi p ≤ Metric.infDist (G.map p) G.regionᶜ / 4

omit [T2Space S] in
/-- Frontier control keeps each selected polygonal disk inside the permitted open region. -/
theorem closedRegions_mem_region_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region := by
  by_cases hcomp : G.regionᶜ.Nonempty
  · obtain ⟨z, hz⟩ := K.faceCarrier_nonempty f
    obtain ⟨x, rfl⟩ := hz
    let p : K.support := faceToSupport (K := K) f x
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self x
    have hball := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp
    intro q hq
    have hdist : dist (G.map p) q ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hball hq
    have hinfPos : 0 < Metric.infDist (G.map p) G.regionᶜ := by
      exact (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
        (by simpa only [Set.mem_compl_iff, not_not] using G.map_mem_region p)
    have hlt : dist (G.map p) q < Metric.infDist (G.map p) G.regionᶜ := by
      calc
        dist (G.map p) q ≤ phi p := hdist
        _ ≤ Metric.infDist (G.map p) G.regionᶜ / 4 := hfrontier.2 hcomp p
        _ < Metric.infDist (G.map p) G.regionᶜ := by linarith
    have hnot := Metric.notMem_of_dist_lt_infDist hlt
    simpa only [Set.mem_compl_iff, not_not] using hnot
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    rw [hregion]
    exact Set.subset_univ _

omit [T2Space S] in
/-- The filled polygonal disks of a uniformly frontier-controlled replacement are locally
finite in the open perturbation region.  The proof confines any disk meeting a small ball to
an original face meeting a fixed compact ball, then uses relative closed-embedding transport. -/
theorem locallyFinite_closedRegions_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) :
    LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion} := by
  intro x
  by_cases hcomp : G.regionᶜ.Nonempty
  · let d := Metric.infDist x.1 G.regionᶜ
    have hd : 0 < d := by
      apply (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
      show x.1 ∉ G.regionᶜ
      simpa only [Set.mem_compl_iff, not_not] using x.2
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 (d / 8)}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (div_pos hd (by norm_num))), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 (d / 2)
    have hCV : C ⊆ G.region := by
      intro q hq
      by_contra hqRegion
      have hinf := Metric.infDist_le_dist_of_mem (x := x.1)
        (show q ∈ G.regionᶜ from hqRegion)
      have hdist : dist x.1 q ≤ d / 2 := by
        simpa only [C, Metric.mem_closedBall, dist_comm] using hq
      dsimp only [d] at hd hinf hdist
      linarith
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < d / 8 := Metric.mem_ball.mp hzU
    have hinf : Metric.infDist (G.map p) G.regionᶜ ≤
        d + dist (G.map p) x.1 :=
      Metric.infDist_le_infDist_add_dist
    have hmain : dist (G.map p) x.1 <
        (d + dist (G.map p) x.1) / 4 + d / 8 := calc
      dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
        dist_triangle _ _ _
      _ < phi p + d / 8 := add_lt_add_of_le_of_lt hcenterZ hzX
      _ ≤ (d + dist (G.map p) x.1) / 4 + d / 8 := by
        gcongr
        exact (hfrontier.2 hcomp p).trans
          (div_le_div_of_nonneg_right hinf (by norm_num))
    have hpCenter : dist (G.map p) x.1 ≤ d / 2 := by linarith
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 1}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (by norm_num)), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 2
    have hCV : C ⊆ G.region := by rw [hregion]; exact Set.subset_univ _
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < 1 := Metric.mem_ball.mp hzU
    have hpCenter : dist (G.map p) x.1 ≤ 2 := by
      apply le_of_lt
      calc
        dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
          dist_triangle _ _ _
        _ < phi p + 1 := add_lt_add_of_le_of_lt hcenterZ hzX
        _ ≤ 2 := by linarith [hfrontier.1 p]
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter

omit [T2Space S] in
/-- Convex target regions are preserved by the simultaneous polygonal replacement of the
one-skeleton.  The construction chooses each central broken line in the convex hull of its
original embedded edge. -/
theorem range_graphReplacementMap_subset_of_convex
    (G : K.PlaneGraphRealization) {C : Set Plane} (hC : Convex ℝ C)
    (hmap : Set.range G.map ⊆ C) :
    Set.range G.graphReplacementMap ⊆ C := by
  rw [G.range_graphReplacementMap]
  intro y hy
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
  apply convexHull_min _ hC <|
    (G.replacementArc e).completeCarrier_subset_edgeConvexHull hye
  rintro z ⟨p, -, rfl⟩
  exact hmap (Set.mem_range_self p)

omit [T2Space S] in
/-- A source realization in the model half-plane has a replacement graph in that half-plane. -/
theorem range_graphReplacementMap_subset_halfPlane
    (G : K.PlaneGraphRealization) (hmap : Set.range G.map ⊆ HalfPlaneSet) :
    Set.range G.graphReplacementMap ⊆ HalfPlaneSet :=
  range_graphReplacementMap_subset_of_convex G convex_halfPlaneSet hmap

omit [T2Space S] in
/-- A zero-normal point of a complete replacement arc is supported by zero-normal points of the
old embedded edge.  This is the exact supporting-face statement behind boundary preservation;
mere half-plane containment would only give one implication. -/
theorem PlaneGraphRealization.CentralPolygonalArc.mem_convexHull_edgeImage_coordZero
    (G : K.PlaneGraphRealization) {e : K.Edge}
    (A : G.CentralPolygonalArc e)
    (hmap : G.edgeImage e ⊆ HalfPlaneSet)
    {x : Plane} (hx : x ∈ A.completeCarrier) (hxZero : x 0 = 0) :
    x ∈ convexHull ℝ (G.edgeImage e ∩ {p | p 0 = 0}) := by
  have hnonneg : ∀ p ∈ G.edgeImage e, 0 ≤ cartesianX p := by
    intro p hp
    exact hmap hp
  change x ∈ convexHull ℝ (G.edgeImage e ∩ {p | cartesianX p = 0})
  rw [← convexHull_inter_affine_zero_of_nonneg_set
    (G.edgeImage e) cartesianX hnonneg]
  exact ⟨A.completeCarrier_subset_edgeConvexHull hx, hxZero⟩

omit [T2Space S] in
/-- On the source one-skeleton, the assembled cellwise replacement is exactly the previously
constructed global graph replacement. -/
theorem polygonalReplacementMap_eq_graphReplacementMap
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (p : oneSkeletonInSupport (K := K)) :
    (K.polygonalReplacementMap H p.1).1.1 = G.graphReplacementMap p := by
  let e : K.Edge := containingEdge (K := K) p
  let f : K.Face := K.edgeFace e
  have hpe : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  have hef : e.1 ⊆ K.faceVertices f := K.edge_subset_faceVertices e
  have hpf : p.1 ∈ faceInSupport (K := K) f :=
    edgeInSupport_subset_faceInSupport (K := K) f e hef hpe
  obtain ⟨x, hx⟩ := hpf
  have hpPolygon :
      G.graphReplacementMap p ∈
        (K.facePolygonalCircle (G := G) f).carrier :=
    graphReplacement_mem_facePolygonalCircle_of_edge_subset
      (G := G) f e p hpe hef
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hpPolygon
  obtain ⟨z, hzFrontier, hzMap⟩ := hpPolygon
  let zBoundary : StandardFaceBoundary := ⟨z, hzFrontier⟩
  have hgraph :
      G.graphReplacementMap p =
        G.graphReplacementMap (K.faceBoundaryLift f zBoundary) := by
    rw [← K.faceBoundaryMap_apply (G := G) f zBoundary]
    exact hzMap.symm
  have hpLift : p = K.faceBoundaryLift f zBoundary :=
    G.graphReplacementMap_injective hgraph
  let zFace : K.ClosedFace f :=
    (K.facePlaneHomeomorph f).symm
      ⟨z, standardFaceBoundary_mem_region zBoundary⟩
  have hsource : x = zFace := by
    apply K.faceMap_injective f
    have hzSupport :
        faceToSupport (K := K) f zFace =
          (K.faceBoundaryLift f zBoundary).1 := rfl
    exact congrArg Subtype.val
      (hx.trans ((congrArg Subtype.val hpLift).trans hzSupport.symm))
  have hglobal :=
    K.polygonalReplacementMap_faceToSupport H f x
  rw [hx] at hglobal
  have hplane := congrArg (fun q => q.1.1) hglobal
  have hplane' :
      (K.polygonalReplacementMap H p.1).1.1 =
        (K.facePLFilling (G := G) f).faceMap x := by
    exact hplane
  rw [hplane', hsource]
  change
    (K.facePLFilling (G := G) f).map
        (K.facePlaneHomeomorph f zFace).1 =
      G.graphReplacementMap p
  have hzFace : (K.facePlaneHomeomorph f zFace).1 = z := by
    change
      (K.facePlaneHomeomorph f
        ((K.facePlaneHomeomorph f).symm
          ⟨z, standardFaceBoundary_mem_region zBoundary⟩)).1 = z
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
  rw [hzFace]
  rw [(K.facePLFilling (G := G) f).eqOn_boundary hzFrontier]
  exact hzMap

/-- The source zero-normal locus already lies in the source one-skeleton. -/
def PlaneGraphRealization.SourceCoordZeroCarriedByOneSkeleton
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ p : K.support, G.map p 0 = 0 →
    p ∈ oneSkeletonInSupport (K := K)

/-- On every source triangle, the supporting-line locus is an exposed face with at most two
vertices.  This is the intrinsic condition which excludes a boundary chord: the zero locus in
a triangle is either empty, a vertex, or an entire edge. -/
def PlaneGraphRealization.FacewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ f : K.Face, ∃ b : Finset K.Vertex,
    b ⊆ K.faceVertices f ∧ b.card ≤ 2 ∧
      ∀ x : K.ClosedFace f,
        G.map (faceToSupport (K := K) f x) 0 = 0 ↔
          ∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b → x v = 0

omit [T2Space S] in
/-- A facewise exposed zero locus is necessarily carried by the source one-skeleton. -/
theorem sourceCoordZeroCarriedByOneSkeleton_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (hface : G.FacewiseCoordZeroExposed) :
    G.SourceCoordZeroCarriedByOneSkeleton := by
  classical
  intro p hpZero
  let f : K.Face := K.supportFace p
  let x : K.ClosedFace f := K.supportFacePoint p
  obtain ⟨b, hbf, hbcard, hb⟩ := hface f
  have hfacePoint :
      faceToSupport (K := K) f x = p := by
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  have hxSupported : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ b → x v = 0 := by
    apply (hb x).mp
    rw [hfacePoint]
    exact hpZero
  have htwo : 2 ≤ (K.faceVertices f).card := by
    rw [K.faceVertices_card f]
    omega
  obtain ⟨e, hbe, hef, hecard⟩ :=
    Finset.exists_subsuperset_card_eq hbf hbcard htwo
  let E : K.Edge := ⟨e, hecard, f, hef⟩
  have hxE : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ E.1 → x v = 0 := by
    intro v hv
    exact hxSupported v fun hvb ↦ hv (hbe hvb)
  have hpEdge : p.1 ∈ K.edgeCarrier E := by
    rw [← congrArg Subtype.val hfacePoint]
    exact K.faceMap_mem_edgeCarrier_of_supportedOnEdge f E hef x hxE
  apply Set.mem_iUnion.mpr
  refine ⟨E, ?_⟩
  rw [edgeInSupport_eq_preimage (K := K)]
  exact hpEdge

/-- The graph replacement preserves the zero-normal locus pointwise on its source graph. -/
def PlaneGraphRealization.GraphReplacementPreservesCoordZero
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ p : oneSkeletonInSupport (K := K),
    G.graphReplacementMap p 0 = 0 ↔ G.map p.1 0 = 0

/-- The exact edgewise alternatives needed at a supporting boundary line.  On each old edge,
the zero-normal locus is either the whole image, one incident vertex, or empty.  In particular,
this rules out an interior edge whose two endpoints lie on the model boundary while its interior
does not: an arbitrary convex-hull polygonalization could otherwise create a spurious boundary
segment. -/
def PlaneGraphRealization.EdgeCoordZeroTrichotomy
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ e : K.Edge,
    (∀ x ∈ G.edgeImage e, x 0 = 0) ∨
      (∃ v : K.Vertex, v ∈ e.1 ∧
        G.edgeImage e ∩ {x | x 0 = 0} = {G.vertexImage v}) ∨
      G.edgeImage e ∩ {x | x 0 = 0} = ∅

omit [T2Space S] in
/-- Including an edge simplex in an incident face does not change its endpoint
coordinates. -/
private theorem edgeSimplexInFace_apply
    (f : K.Face) (e : K.Edge) (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) (w : {v // v ∈ e.1}) :
    K.edgeSimplexInFace f e hef z ⟨w.1, hef w.2⟩ = z w := by
  have hcoords := congrFun (extendFaceCoordinates_map_subset hef z) w.1
  rw [extendFaceCoordinates_of_mem (K.faceVertices f)
      (stdSimplex.map (fun v : {v // v ∈ e.1} ↦
        ⟨v.1, hef v.2⟩) z) (hef w.2),
    extendFaceCoordinates_of_mem e.1 z w.2] at hcoords
  exact hcoords

omit [T2Space S] in
/-- Support on a selected set of face vertices can be checked before including an edge
simplex into its incident face. -/
private theorem edgeSimplexInFace_supportedOn_iff
    (f : K.Face) (e : K.Edge) (hef : e.1 ⊆ K.faceVertices f)
    (b : Finset K.Vertex) (z : stdSimplex ℝ {v // v ∈ e.1}) :
    (∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b →
        K.edgeSimplexInFace f e hef z v = 0) ↔
      ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 := by
  constructor
  · intro h w hwb
    have hw := h ⟨w.1, hef w.2⟩ hwb
    simpa only [edgeSimplexInFace_apply] using hw
  · intro h v hvb
    by_cases hve : v.1 ∈ e.1
    · let w : {w // w ∈ e.1} := ⟨v.1, hve⟩
      have hw := h w hvb
      have happly := edgeSimplexInFace_apply (K := K) f e hef z w
      change K.edgeSimplexInFace f e hef z v = 0
      rw [show v = ⟨w.1, hef w.2⟩ by apply Subtype.ext; rfl,
        happly]
      exact hw
    · exact K.edgeSimplexInFace_supported f e hef z v hve

omit [T2Space S] in
/-- A facewise exposed zero locus gives the edgewise full/singleton/empty alternatives. -/
theorem edgeCoordZeroTrichotomy_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (hface : G.FacewiseCoordZeroExposed) :
    G.EdgeCoordZeroTrichotomy := by
  classical
  intro e
  let f : K.Face := K.edgeFace e
  have hef : e.1 ⊆ K.faceVertices f := K.edge_subset_faceVertices e
  obtain ⟨b, -, -, hb⟩ := hface f
  let a : K.Vertex := K.edgeFirst e
  let d : K.Vertex := K.edgeSecond e
  have hae : a ∈ e.1 := K.edgeFirst_mem e
  have hde : d ∈ e.1 := K.edgeSecond_mem e
  have had : a ≠ d := K.edgeFirst_ne_edgeSecond e
  have hendpoints (w : {v // v ∈ e.1}) : w.1 = a ∨ w.1 = d := by
    have hw : w.1 ∈
        ({K.edgeFirst e, K.edgeSecond e} : Finset K.Vertex) := by
      rw [← K.edge_eq_pair e]
      exact w.2
    simpa only [a, d, Finset.mem_insert, Finset.mem_singleton] using hw
  have hzero (p : K.support) (z : stdSimplex ℝ {v // v ∈ e.1})
      (hz : K.edgeMap e z = p.1) :
      G.map p 0 = 0 ↔
        ∀ w : {w // w ∈ e.1}, w.1 ∉ b →
          z w = 0 := by
    let x : K.ClosedFace f := K.edgeSimplexInFace f e hef z
    have hpx : faceToSupport (K := K) f x = p := by
      apply Subtype.ext
      exact (K.faceMap_edgeSimplexInFace f e hef z).trans hz
    calc
      G.map p 0 = 0 ↔
          G.map (faceToSupport (K := K) f x) 0 = 0 := by rw [hpx]
      _ ↔ ∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b → x v = 0 :=
        hb x
      _ ↔ ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
        edgeSimplexInFace_supportedOn_iff (K := K) f e hef b z
  by_cases hab : a ∈ b
  · by_cases hdb : d ∈ b
    · left
      rintro y ⟨p, hp, rfl⟩
      obtain ⟨z, hz⟩ := hp
      apply (hzero p z hz).mpr
      intro w hwb
      rcases hendpoints w with hwa | hwd
      · exact absurd (hwa ▸ hab) hwb
      · exact absurd (hwd ▸ hdb) hwb
    · right
      left
      refine ⟨a, hae, ?_⟩
      ext y
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hpZero⟩
        let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
        have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
        have hzSupport :
            ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
          (hzero p z hz).mp hpZero
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        have hzd : z wd = 0 := hzSupport wd hdb
        have hza : z wa = 1 := by
          calc
            z wa = z wa + z wd := by rw [hzd, add_zero]
            _ = ∑ w, z w := by
              rw [show (Finset.univ : Finset {v // v ∈ e.1}) = {wa, wd} by
                ext w
                simp only [Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_iff]
                rcases hendpoints w with hw | hw
                · exact Or.inl (Subtype.ext hw)
                · exact Or.inr (Subtype.ext hw)]
              simp [show wa ≠ wd by
                intro h; exact had (congrArg Subtype.val h)]
            _ = 1 := z.2.2
        have hzVertex : z = stdSimplex.vertex wa := by
          apply stdSimplex.ext
          funext w
          rcases hendpoints w with hw | hw
          · rw [show w = wa by apply Subtype.ext; exact hw]
            simp [hza]
          · rw [show w = wd by apply Subtype.ext; exact hw, hzd]
            simp [show wd ≠ wa by
              intro h; exact had (congrArg Subtype.val h).symm]
        have hpSource :
            p = ⟨K.vertexPoint a, K.vertexPoint_mem_support a⟩ := by
          apply Subtype.ext
          rw [← hz, hzVertex,
            K.edgeMap_vertex_eq_vertexPoint]
        rw [hpSource]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hvImage : G.vertexImage a ∈ G.edgeImage e :=
          (G.vertexImage_mem_edgeImage_iff a e).mpr hae
        refine ⟨hvImage, ?_⟩
        let p : K.support :=
          ⟨K.vertexPoint a, K.vertexPoint_mem_support a⟩
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        change G.map p 0 = 0
        have hzedge :
            K.edgeMap e (stdSimplex.vertex wa) = p.1 := by
          exact K.edgeMap_vertex_eq_vertexPoint e wa
        apply (hzero p (stdSimplex.vertex wa) hzedge).mpr
        intro w hwb
        have hwa : w ≠ wa := by
          intro hw
          apply hwb
          rw [hw]
          exact hab
        simp [stdSimplex.vertex, hwa]
  · by_cases hdb : d ∈ b
    · right
      left
      refine ⟨d, hde, ?_⟩
      ext y
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hpZero⟩
        let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
        have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
        have hzSupport :
            ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
          (hzero p z hz).mp hpZero
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        have hza : z wa = 0 := hzSupport wa hab
        have hzd : z wd = 1 := by
          calc
            z wd = z wa + z wd := by rw [hza, zero_add]
            _ = ∑ w, z w := by
              rw [show (Finset.univ : Finset {v // v ∈ e.1}) = {wa, wd} by
                ext w
                simp only [Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_iff]
                rcases hendpoints w with hw | hw
                · exact Or.inl (Subtype.ext hw)
                · exact Or.inr (Subtype.ext hw)]
              simp [show wa ≠ wd by
                intro h; exact had (congrArg Subtype.val h)]
            _ = 1 := z.2.2
        have hzVertex : z = stdSimplex.vertex wd := by
          apply stdSimplex.ext
          funext w
          rcases hendpoints w with hw | hw
          · rw [show w = wa by apply Subtype.ext; exact hw, hza]
            simp [show wa ≠ wd by
              intro h; exact had (congrArg Subtype.val h)]
          · rw [show w = wd by apply Subtype.ext; exact hw]
            simp [hzd]
        have hpSource :
            p = ⟨K.vertexPoint d, K.vertexPoint_mem_support d⟩ := by
          apply Subtype.ext
          rw [← hz, hzVertex,
            K.edgeMap_vertex_eq_vertexPoint]
        rw [hpSource]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hvImage : G.vertexImage d ∈ G.edgeImage e :=
          (G.vertexImage_mem_edgeImage_iff d e).mpr hde
        refine ⟨hvImage, ?_⟩
        let p : K.support :=
          ⟨K.vertexPoint d, K.vertexPoint_mem_support d⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        change G.map p 0 = 0
        have hzedge :
            K.edgeMap e (stdSimplex.vertex wd) = p.1 := by
          exact K.edgeMap_vertex_eq_vertexPoint e wd
        apply (hzero p (stdSimplex.vertex wd) hzedge).mpr
        intro w hwb
        have hwd : w ≠ wd := by
          intro hw
          apply hwb
          rw [hw]
          exact hdb
        simp [stdSimplex.vertex, hwd]
    · right
      right
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨p, hp, rfl⟩, hpZero⟩
      let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
      have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
      have hzSupport :
          ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
        (hzero p z hz).mp hpZero
      have hzeroAll : ∀ w, z w = 0 := by
        intro w
        rcases hendpoints w with hw | hw
        · exact hzSupport w (hw ▸ hab)
        · exact hzSupport w (hw ▸ hdb)
      have : (∑ w, z w) = 0 := by simp [hzeroAll]
      have hone : (∑ w, z w) = 1 := z.2.2
      exact one_ne_zero (hone.symm.trans this)

omit [T2Space S] in
/-- The edgewise zero-locus trichotomy makes the simultaneous graph replacement preserve the
supporting boundary line exactly.  The forward direction uses the supporting-face theorem for
the replacement convex hull; the reverse direction uses vertex fixing in the singleton case. -/
theorem graphReplacementPreservesCoordZero_of_edgeCoordZeroTrichotomy
    (G : K.PlaneGraphRealization)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hedges : G.EdgeCoordZeroTrichotomy) :
    G.GraphReplacementPreservesCoordZero := by
  intro p
  let e : K.Edge := containingEdge (K := K) p
  have hpe : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  have hpCarrier : p.1.1 ∈ K.edgeCarrier e := by
    change p.1 ∈ Subtype.val ⁻¹' K.edgeCarrier e
    rw [← edgeInSupport_eq_preimage (K := K) e]
    exact hpe
  have hpImage : G.map p.1 ∈ G.edgeImage e :=
    ⟨p.1, hpCarrier, rfl⟩
  have hedgeHalf : G.edgeImage e ⊆ HalfPlaneSet := by
    rintro x ⟨q, -, rfl⟩
    exact hhalf (Set.mem_range_self q)
  rw [G.graphReplacementMap_eq e p hpe]
  rcases hedges e with hfull | hsingle | hempty
  · constructor
    · intro _
      exact hfull (G.map p.1) hpImage
    · intro _
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e) :=
        (G.replacementArc e).completeCarrier_subset_edgeConvexHull hyCarrier
      have hyZero :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            {x | cartesianX x = 0} := by
        apply convexHull_min (𝕜 := ℝ)
        · intro x hx
          exact hfull x hx
        · exact (convex_singleton (0 : ℝ)).affine_preimage cartesianX
        · exact hyHull
      exact hyZero
  · obtain ⟨v, hve, hzeroSet⟩ := hsingle
    let pv : edgeInSupport (K := K) e :=
      ⟨⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩,
        by
          rw [edgeInSupport_eq_preimage (K := K)]
          exact (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve⟩
    have hvZero : G.vertexImage v 0 = 0 := by
      have hvImage : G.vertexImage v ∈ G.edgeImage e :=
        (G.vertexImage_mem_edgeImage_iff v e).mpr hve
      have hvMem :
          G.vertexImage v ∈ G.edgeImage e ∩ {x | x 0 = 0} := by
        rw [hzeroSet]
        exact Set.mem_singleton _
      exact hvMem.2
    constructor
    · intro hyZero
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e ∩ {x | x 0 = 0}) :=
        (G.replacementArc e).mem_convexHull_edgeImage_coordZero G
          hedgeHalf hyCarrier hyZero
      have hyVertex :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ = G.vertexImage v := by
        rw [hzeroSet, convexHull_singleton] at hyHull
        exact hyHull
      have hpv : (⟨p.1, hpe⟩ : edgeInSupport (K := K) e) = pv := by
        apply G.replacementEdgeMap_injective e
        rw [hyVertex, G.replacementEdgeMap_vertex e v hve]
      have hpSupport :
          p.1 = (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) :=
        congrArg (fun q : edgeInSupport (K := K) e ↦ q.1) hpv
      rw [hpSupport]
      exact hvZero
    · intro hpZero
      have hpZeroMem :
          G.map p.1 ∈ G.edgeImage e ∩ {x | x 0 = 0} :=
        ⟨hpImage, hpZero⟩
      have hpImageEq : G.map p.1 = G.vertexImage v := by
        rw [hzeroSet] at hpZeroMem
        exact hpZeroMem
      have hpSupport :
          p.1 = (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) :=
        G.isEmbedding.injective hpImageEq
      have hpv : (⟨p.1, hpe⟩ : edgeInSupport (K := K) e) = pv := by
        apply Subtype.ext
        exact hpSupport
      rw [hpv, G.replacementEdgeMap_vertex e v hve]
      exact hvZero
  · constructor
    · intro hyZero
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e ∩ {x | x 0 = 0}) :=
        (G.replacementArc e).mem_convexHull_edgeImage_coordZero G
          hedgeHalf hyCarrier hyZero
      rw [hempty, convexHull_empty] at hyHull
      exact hyHull.elim
    · intro hpZero
      have hpZeroMem :
          G.map p.1 ∈ G.edgeImage e ∩ {x | x 0 = 0} :=
        ⟨hpImage, hpZero⟩
      rw [hempty] at hpZeroMem
      exact hpZeroMem.elim

omit [T2Space S] in
/-- The facewise exposed-face invariant is the single source-side hypothesis needed for exact
zero-coordinate preservation by the simultaneous graph replacement. -/
theorem graphReplacementPreservesCoordZero_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hface : G.FacewiseCoordZeroExposed) :
    G.GraphReplacementPreservesCoordZero :=
  graphReplacementPreservesCoordZero_of_edgeCoordZeroTrichotomy G hhalf
    (edgeCoordZeroTrichotomy_of_facewiseCoordZeroExposed G hface)

/-- Once exact zero-coordinate preservation is known on the replacement graph, the polygonal
Schoenflies fillings preserve it on every filled face.  No filled-face interior can reach the
supporting line, so the two-dimensional statement reduces completely to the one-skeleton. -/
theorem polygonalReplacementHomeomorph_coordZero_iff
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hsource : G.SourceCoordZeroCarriedByOneSkeleton)
    (hgraph : G.GraphReplacementPreservesCoordZero)
    (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 0 = 0 ↔
      G.map p 0 = 0 := by
  constructor
  · intro hpZero
    let f : K.Face := K.supportFace p
    let J : PolygonalCircle := K.facePolygonalCircle (G := G) f
    have hcarrierHalf : J.carrier ⊆ HalfPlaneSet := by
      exact (K.facePolygonalCircle_carrier_subset_graphReplacement
        (G := G) f).trans
          (range_graphReplacementMap_subset_halfPlane G hhalf)
    have hpClosed :
        (K.polygonalReplacementHomeomorph H p).1.1 ∈ J.closedRegion := by
      change
        (K.facePLFilling (G := G) (K.supportFace p)).faceMap
            (K.supportFacePoint p) ∈ J.closedRegion
      rw [show J =
        K.facePolygonalCircle (G := G) (K.supportFace p) by rfl,
        ← (K.facePLFilling (G := G) (K.supportFace p)).range_faceMap]
      exact Set.mem_range_self _
    have hpCarrier :
        (K.polygonalReplacementHomeomorph H p).1.1 ∈ J.carrier :=
      J.mem_carrier_of_mem_closedRegion_coordZero hcarrierHalf hpClosed hpZero
    obtain ⟨q, hq⟩ :=
      K.facePolygonalCircle_carrier_subset_graphReplacement
        (G := G) f hpCarrier
    have hqMap :
        (K.polygonalReplacementHomeomorph H q.1).1.1 =
          G.graphReplacementMap q :=
      polygonalReplacementMap_eq_graphReplacementMap G H q
    have hpqTarget :
        K.polygonalReplacementHomeomorph H p =
          K.polygonalReplacementHomeomorph H q.1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hq.symm.trans hqMap.symm
    have hpq : p = q.1 :=
      (K.polygonalReplacementHomeomorph H).injective hpqTarget
    rw [hpq]
    exact hgraph q |>.mp (by rw [← hqMap, ← hpq]; exact hpZero)
  · intro hpZero
    let q : oneSkeletonInSupport (K := K) :=
      ⟨p, hsource p hpZero⟩
    have hqZero : G.graphReplacementMap q 0 = 0 :=
      (hgraph q).mpr hpZero
    rw [show p = q.1 by rfl]
    have hqMap :=
      polygonalReplacementMap_eq_graphReplacementMap G H q
    change
      (K.polygonalReplacementHomeomorph H q.1).1.1 =
        G.graphReplacementMap q at hqMap
    rw [hqMap]
    exact hqZero

/-- Exact preservation on filled faces, stated directly from the facewise exposed-face
invariant. -/
theorem polygonalReplacementHomeomorph_coordZero_iff_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hface : G.FacewiseCoordZeroExposed) (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 0 = 0 ↔
      G.map p 0 = 0 :=
  polygonalReplacementHomeomorph_coordZero_iff G H hhalf
    (sourceCoordZeroCarriedByOneSkeleton_of_facewiseCoordZeroExposed G hface)
    (graphReplacementPreservesCoordZero_of_facewiseCoordZeroExposed G hhalf hface) p

omit [T2Space S] in
/-- A controlled compatible cellwise replacement lands in the permitted perturbation region. -/
theorem polygonalReplacementMap_mem_region (G : K.PlaneGraphRealization)
    (H : K.CellwiseCompatibility G) {phi : K.support → ℝ}
    (_ : FaceBoundariesControlled G phi)
    (_ : G.ControlsStayInRegion phi) (p : K.support) :
    (K.polygonalReplacementMap H p).1.1 ∈ G.region :=
  (K.polygonalReplacementMap H p).1.2

/-- The full locally finite Chapter 6 output from its quantitative graph hypotheses. -/
theorem exists_controlled_polygonalReplacement (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    ∃ H : K.CellwiseCompatibility G,
      (∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p) := by
  let H := cellwiseCompatibility_of_control (G := G) hfaces hcontrol hsep hregion hloc
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The complete locally finite Chapter 6 output in Moise's facewise side-control form.
Uniform frontier control supplies target containment and local finiteness automatically. -/
theorem exists_controlled_polygonalReplacement_of_facewise_close
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hclose : FaceBoundariesClose G (faceVertexSeparationRadius G)) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  let H := cellwiseCompatibility_of_facewise_close (G := G) hfaces hclose
    (closedRegions_mem_region_of_uniformFrontierControl G hcontrol hfrontier)
    (locallyFinite_closedRegions_of_uniformFrontierControl G hcontrol hfrontier)
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The Chapter 6 cellwise approximation from the exact edge-mesh condition supplied by an
internal edge subdivision.  No independent side hypothesis remains: the incident-face minimum
turns edgewise diameter control into the required facewise closeness. -/
theorem exists_controlled_polygonalReplacement_of_edgeMesh
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hmesh : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeFaceSeparationRadius G e) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  exact exists_controlled_polygonalReplacement_of_facewise_close G hfaces hcontrol hfrontier
    (faceBoundariesClose_of_edgeFaceSeparation_control (G := G) hmesh)

omit [T2Space S] in
/-- If the replacement graph lies in the closed right half-plane, every selected polygonal face
disk lies there too. -/
theorem facePolygonalCircle_closedRegion_subset_halfPlane
    (G : K.PlaneGraphRealization)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ HalfPlaneSet := by
  apply (K.facePolygonalCircle (G := G) f).closedRegion_subset_halfPlane
  exact (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) f).trans hgraph

omit [T2Space S] in
/-- Consequently the entire assembled locally finite replacement complex stays in the closed
right half-plane. -/
theorem polygonalReplacementComplex_support_subset_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet) :
    Subtype.val '' (K.polygonalReplacementComplex H).support ⊆ HalfPlaneSet := by
  rintro p ⟨q, hq, rfl⟩
  have hpSupport : q ∈ (K.polygonalReplacementComplex H).support := hq
  obtain ⟨f, hpf⟩ := Set.mem_iUnion.mp hpSupport
  rw [K.polygonalReplacementComplex_faceCarrier H f] at hpf
  exact facePolygonalCircle_closedRegion_subset_halfPlane G hgraph f hpf

/-- Pointwise half-plane preservation for the assembled replacement homeomorphism. -/
theorem polygonalReplacementHomeomorph_mem_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 ∈ HalfPlaneSet :=
  polygonalReplacementComplex_support_subset_halfPlane G H hgraph
    ⟨(K.polygonalReplacementHomeomorph H p).1,
      (K.polygonalReplacementHomeomorph H p).2, rfl⟩

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification16_block_03
/- END ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation -/

/- BEGIN ClassificationOfSurfaces.Moise.FacewiseComparison | 9b56d43763ffcda1c8d41a8f6f2300d898368ded3e2a4740dcf25ec9d34757fd -/
section schottkyclassification16_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The per-face comparison map for locally finite side preservation

This file discharges the side-preservation entry of the locally finite Chapter 6 replacement
through the parametrization-independent interface `cellwiseCompatibility_of_comparison`.

The canonical replacement arcs only track the *trimmed* original edge curve
(`CentralPolygonalArc.curve_close`), with the `Path.trans` parameter misaligned against the
original face parametrization, so no same-parameter estimate can beat the mesh scale.  The
comparison map built here is the original face chart composed with a clamped radial
reparametrization of the standard triangle (`sidePiece`, glued over three closed sectors in
`facewiseComparison`): on each side the boundary parameter is redistributed so that the middle
replacement range covers exactly the matched trim window, and the spoke ranges cover the two
trimmed-off end pieces.  All values lie in the original face image, so the cthickening
membership required by `cellwiseCompatibility_of_comparison` is automatic.

The key quantitative input is `exists_comparisonScale`: the original face chart and its
inverse are both uniformly continuous on the compact standard triangle, so once the vertex
isolation disk and central tube of an edge are small in the *image*, the endpoints of each
trimmed-off piece have close images, hence (inverse modulus) close standard parameters, hence
(forward modulus) the whole reparametrized piece stays within a quarter separation radius of
the vertex image.  In particular the last-exit trim cannot make the trimmed-off original
curve wander once the controls undercut the comparison scale — the wandering is bounded by
the two-sided modulus, not by any mesh estimate.

Everything is arranged for a realization with shrunken approximation controls
(`withApproximationControls`), which changes neither the embedded map nor the face separation
radii; the resulting entry point is `exists_controlled_polygonalReplacement_of_comparison`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

/-! ## Barycentric coordinates on the standard triangle -/

/-- The standard triangle vertices as an affine basis of the plane. -/
noncomputable def stdTriBasis : AffineBasis (Fin 3) ℝ Plane :=
  planeAffineBasisOfTriple standardTriangleVertex standardTriangleVertex_affineIndependent

@[simp] theorem stdTriBasis_apply (j : Fin 3) :
    stdTriBasis j = standardTriangleVertex j := rfl

theorem range_stdTriBasis :
    Set.range ⇑stdTriBasis = Set.range standardTriangleVertex := rfl

/-- The barycentric coordinate of a plane point with respect to a standard triangle vertex. -/
noncomputable def triCoord (j : Fin 3) (x : Plane) : ℝ := stdTriBasis.coord j x

theorem continuous_triCoord (j : Fin 3) : Continuous (triCoord j) :=
  (stdTriBasis.coord j).continuous_of_finiteDimensional

@[simp] theorem triCoord_vertex_self (j : Fin 3) :
    triCoord j (standardTriangleVertex j) = 1 := by
  simpa [triCoord] using stdTriBasis.coord_apply_eq j

theorem triCoord_vertex_ne {j k : Fin 3} (hjk : j ≠ k) :
    triCoord j (standardTriangleVertex k) = 0 := by
  simpa [triCoord] using stdTriBasis.coord_apply_ne hjk

theorem sum_triCoord (x : Plane) : ∑ j, triCoord j x = 1 :=
  stdTriBasis.sum_coord_apply_eq_one x

theorem triCoord_lineMap (j : Fin 3) (a b : Plane) (t : ℝ) :
    triCoord j (AffineMap.lineMap a b t) =
      AffineMap.lineMap (triCoord j a) (triCoord j b) t := by
  simp only [triCoord]
  exact (stdTriBasis.coord j).apply_lineMap a b t

theorem standardFaceRegion_eq_convexHull :
    standardFaceRegion = convexHull ℝ (Set.range standardTriangleVertex) :=
  standardTrianglePlaneComplex_support

theorem convex_standardFaceRegion : Convex ℝ standardFaceRegion := by
  rw [standardFaceRegion_eq_convexHull]
  exact convex_convexHull ℝ _

theorem mem_standardFaceRegion_iff {x : Plane} :
    x ∈ standardFaceRegion ↔ ∀ j, 0 ≤ triCoord j x := by
  rw [standardFaceRegion_eq_convexHull, ← range_stdTriBasis,
    stdTriBasis.convexHull_eq_nonneg_coord]
  rfl

theorem interior_standardFaceRegion :
    interior standardFaceRegion = {x | ∀ j, 0 < triCoord j x} := by
  rw [standardFaceRegion_eq_convexHull, ← range_stdTriBasis]
  exact interior_convexHull_affineBasis stdTriBasis

theorem mem_frontier_standardFaceRegion_iff {x : Plane} :
    x ∈ frontier standardFaceRegion ↔
      x ∈ standardFaceRegion ∧ ∃ j, triCoord j x = 0 := by
  rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq,
    Set.mem_sdiff, interior_standardFaceRegion]
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    by_contra hall
    push Not at hall
    apply hnot
    intro j
    exact lt_of_le_of_ne (mem_standardFaceRegion_iff.mp hx j) (Ne.symm (hall j))
  · rintro ⟨hx, j, hj⟩
    refine ⟨hx, ?_⟩
    intro hint
    exact (hint j).ne' hj

theorem mem_frontier_of_triCoord_eq_zero {x : Plane}
    (hx : x ∈ standardFaceRegion) {j : Fin 3} (hj : triCoord j x = 0) :
    x ∈ frontier standardFaceRegion :=
  mem_frontier_standardFaceRegion_iff.mpr ⟨hx, j, hj⟩

/-- The barycenter of the standard triangle. -/
noncomputable def triCenter : Plane :=
  Finset.univ.centroid ℝ standardTriangleVertex

@[simp] theorem triCoord_triCenter (j : Fin 3) :
    triCoord j triCenter = 1 / 3 := by
  have h := stdTriBasis.coord_apply_centroid
    (s := (Finset.univ : Finset (Fin 3))) (i := j) (Finset.mem_univ j)
  have hcentroid : Finset.univ.centroid ℝ ⇑stdTriBasis = triCenter := rfl
  rw [hcentroid] at h
  simpa [triCoord] using h

theorem triCenter_mem_standardFaceRegion : triCenter ∈ standardFaceRegion := by
  rw [mem_standardFaceRegion_iff]
  intro j
  rw [triCoord_triCenter]
  norm_num

/-! ## The clamped unit parameter -/

/-- Clamp a real parameter into `[0, 1]`. -/
noncomputable def unitClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem continuous_unitClamp : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem unitClamp_nonneg (t : ℝ) : 0 ≤ unitClamp t := le_max_left _ _

theorem unitClamp_le_one (t : ℝ) : unitClamp t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem unitClamp_mem (t : ℝ) : unitClamp t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨unitClamp_nonneg t, unitClamp_le_one t⟩

theorem unitClamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    unitClamp t = t := by
  rw [unitClamp, min_eq_right ht.2, max_eq_right ht.1]

@[simp] theorem unitClamp_zero : unitClamp 0 = 0 :=
  unitClamp_of_mem ⟨le_rfl, zero_le_one⟩

@[simp] theorem unitClamp_one : unitClamp 1 = 1 :=
  unitClamp_of_mem ⟨zero_le_one, le_rfl⟩

/-- A clamped line-map combination of two points of a convex set stays in the set. -/
theorem lineMap_unitClamp_mem {s : Set Plane} (hs : Convex ℝ s) {a b : Plane}
    (ha : a ∈ s) (hb : b ∈ s) (t : ℝ) :
    AffineMap.lineMap a b (unitClamp t) ∈ s := by
  have hseg : AffineMap.lineMap a b (unitClamp t) ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨unitClamp t, unitClamp_mem t, rfl⟩
  exact hs.segment_subset ha hb hseg

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-! ## Coordinates along one oriented standard side -/

theorem faceEdgeFirstIndex_ne_secondIndex (f : K.Face) (i : ZMod 3) :
    K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
  intro h
  apply K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
  rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
    ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]

theorem triCoord_secondIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (K.faceEdgeSecondIndex f i) (K.faceEdgeSourcePoint f i r) = r := by
  rw [faceEdgeSourcePoint, triCoord_lineMap,
    triCoord_vertex_ne (Ne.symm (K.faceEdgeFirstIndex_ne_secondIndex f i)),
    triCoord_vertex_self]
  simp [AffineMap.lineMap_apply_module]

theorem triCoord_firstIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (K.faceEdgeFirstIndex f i) (K.faceEdgeSourcePoint f i r) = 1 - r := by
  rw [faceEdgeSourcePoint, triCoord_lineMap, triCoord_vertex_self,
    triCoord_vertex_ne (K.faceEdgeFirstIndex_ne_secondIndex f i)]
  simp [AffineMap.lineMap_apply_module]

theorem triCoord_other_sourcePoint (f : K.Face) (i : ZMod 3) {j : Fin 3}
    (hj₁ : j ≠ K.faceEdgeFirstIndex f i) (hj₂ : j ≠ K.faceEdgeSecondIndex f i)
    (r : ℝ) :
    triCoord j (K.faceEdgeSourcePoint f i r) = 0 := by
  rw [faceEdgeSourcePoint, triCoord_lineMap, triCoord_vertex_ne hj₁,
    triCoord_vertex_ne hj₂]
  simp

@[simp] theorem faceEdgeSourcePoint_zero (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i 0 =
      standardTriangleVertex (K.faceEdgeFirstIndex f i) :=
  AffineMap.lineMap_apply_zero _ _

@[simp] theorem faceEdgeSourcePoint_one (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i 1 =
      standardTriangleVertex (K.faceEdgeSecondIndex f i) :=
  AffineMap.lineMap_apply_one _ _

theorem faceEdgeSourcePoint_mem_region (f : K.Face) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r ∈ standardFaceRegion := by
  rw [mem_standardFaceRegion_iff]
  intro j
  by_cases hj₁ : j = K.faceEdgeFirstIndex f i
  · rw [hj₁, triCoord_firstIndex_sourcePoint]
    linarith [hr.2]
  by_cases hj₂ : j = K.faceEdgeSecondIndex f i
  · rw [hj₂, triCoord_secondIndex_sourcePoint]
    exact hr.1
  · rw [triCoord_other_sourcePoint f i hj₁ hj₂]

theorem continuous_faceEdgeSourcePoint (f : K.Face) (i : ZMod 3) :
    Continuous (K.faceEdgeSourcePoint f i) :=
  (AffineMap.lineMap _ _).continuous_of_finiteDimensional.comp
    (by exact continuous_id) |>.congr fun r => rfl

/-! ## The original face chart along a source side -/

/-- The original face chart carries the oriented standard side to the charted edge curve with
the identical parameter. -/
theorem faceOriginalMap_sourcePoint (f : K.Face) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    faceOriginalMap G f (K.faceEdgeSourcePoint f i r) =
      G.chartEdgeCurve (K.faceEdge f i) r := by
  let r' : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hmem : K.faceEdgeSourcePoint f i r ∈ standardFaceRegion :=
    K.faceEdgeSourcePoint_mem_region f i hr
  have happly := faceOriginalMap_apply (G := G) f
    ⟨K.faceEdgeSourcePoint f i r, hmem⟩
  have hsupport := K.faceBoundarySupportPoint_sourcePoint f i r'
  have hsupport' : faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨K.faceEdgeSourcePoint f i r, hmem⟩) =
      edgePathInSupport (K := K) (K.faceEdge f i) r' := by
    exact hsupport
  rw [happly, hsupport', G.chartEdgeCurve_eq_of_mem _ hr]
  rfl

/-- The original face chart is injective on the closed standard triangle. -/
theorem faceOriginalMap_injOn (f : K.Face) :
    Set.InjOn (faceOriginalMap G f) standardFaceRegion := by
  intro x hx y hy hxy
  rw [faceOriginalMap_apply (G := G) f ⟨x, hx⟩,
    faceOriginalMap_apply (G := G) f ⟨y, hy⟩] at hxy
  have hsupp : faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨x, hx⟩) =
      faceToSupport (K := K) f ((K.facePlaneHomeomorph f).symm ⟨y, hy⟩) :=
    G.isEmbedding.injective hxy
  have hface : K.faceMap f ((K.facePlaneHomeomorph f).symm ⟨x, hx⟩) =
      K.faceMap f ((K.facePlaneHomeomorph f).symm ⟨y, hy⟩) :=
    congrArg Subtype.val hsupp
  have := (K.facePlaneHomeomorph f).symm.injective (K.faceMap_injective f hface)
  exact congrArg Subtype.val this

/-! ## The comparison scale of a face

The face separation radius bounds the target tolerance; the two-sided uniform continuity of
the original face chart converts image smallness into segment-image smallness.  The resulting
scale is what the shrunken approximation controls must undercut. -/

/-- Two-sided modulus: once two standard points have images within twice this scale, the whole
straight segment between them has image within a quarter separation radius of either end. -/
theorem exists_comparisonScale (G : K.PlaneGraphRealization) (f : K.Face) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ faceVertexSeparationRadius G f / 8 ∧
      ∀ x ∈ standardFaceRegion, ∀ y ∈ standardFaceRegion,
        dist (faceOriginalMap G f x) (faceOriginalMap G f y) ≤ 2 * eta →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (faceOriginalMap G f (AffineMap.lineMap x y t))
            (faceOriginalMap G f x) ≤ faceVertexSeparationRadius G f / 4 := by
  classical
  set r := faceVertexSeparationRadius G f with hr
  have hrpos : 0 < r := faceVertexSeparationRadius_pos (G := G) f
  set h := faceOriginalMap G f with hh
  have hcont : ContinuousOn h standardFaceRegion :=
    continuousOn_faceOriginalMap (G := G) f
  have hcompact : IsCompact standardFaceRegion :=
    standardTrianglePlaneComplex.isCompact_support
  -- forward modulus
  obtain ⟨d₁, hd₁, hd₁close⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hcompact.uniformContinuousOn_of_continuous hcont)) (r / 4) (by positivity)
  -- inverse modulus by compactness of the far diagonal
  set KK : Set (Plane × Plane) :=
    (standardFaceRegion ×ˢ standardFaceRegion) ∩ {p | d₁ ≤ dist p.1 p.2} with hKK
  have hKKcompact : IsCompact KK :=
    (hcompact.prod hcompact).inter_right
      (isClosed_le continuous_const (continuous_dist))
  have hinverse : ∃ mu : ℝ, 0 < mu ∧
      ∀ x ∈ standardFaceRegion, ∀ y ∈ standardFaceRegion,
        dist (h x) (h y) < mu → dist x y < d₁ := by
    rcases KK.eq_empty_or_nonempty with hempty | hne
    · refine ⟨1, one_pos, ?_⟩
      intro x hx y hy _
      by_contra hfar
      push Not at hfar
      exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty (x, y))
        (fun hnot => hnot ⟨⟨hx, hy⟩, hfar⟩)
    · have hFcont : ContinuousOn (fun p : Plane × Plane => dist (h p.1) (h p.2)) KK := by
        have h1 : ContinuousOn (fun p : Plane × Plane => h p.1) KK :=
          hcont.comp continuousOn_fst fun p hp => hp.1.1
        have h2 : ContinuousOn (fun p : Plane × Plane => h p.2) KK :=
          hcont.comp continuousOn_snd fun p hp => hp.1.2
        exact continuous_dist.comp_continuousOn (h1.prodMk h2)
      obtain ⟨p₀, hp₀KK, hp₀min⟩ := hKKcompact.exists_isMinOn hne hFcont
      have hp₀pos : 0 < dist (h p₀.1) (h p₀.2) := by
        rw [dist_pos]
        intro heq
        have hne12 : p₀.1 ≠ p₀.2 := by
          intro h12
          have hfar : d₁ ≤ dist p₀.1 p₀.2 := hp₀KK.2
          rw [h12, dist_self] at hfar
          exact absurd hfar (not_le.mpr hd₁)
        exact hne12 (faceOriginalMap_injOn (G := G) f hp₀KK.1.1 hp₀KK.1.2 heq)
      refine ⟨dist (h p₀.1) (h p₀.2), hp₀pos, ?_⟩
      intro x hx y hy hclose
      by_contra hfar
      push Not at hfar
      have hxyKK : (x, y) ∈ KK := ⟨⟨hx, hy⟩, hfar⟩
      exact absurd (hp₀min hxyKK) (not_le.mpr hclose)
  obtain ⟨mu, hmu, hmuinv⟩ := hinverse
  refine ⟨min (r / 8) (mu / 4), lt_min (by positivity) (by positivity),
    min_le_left _ _, ?_⟩
  intro x hx y hy hclose t ht
  have hclose' : dist (h x) (h y) < mu := by
    have h2 : 2 * min (r / 8) (mu / 4) ≤ mu / 2 := by
      have := min_le_right (r / 8) (mu / 4)
      linarith
    calc dist (h x) (h y) ≤ 2 * min (r / 8) (mu / 4) := hclose
      _ ≤ mu / 2 := h2
      _ < mu := by linarith
  have hxy : dist x y < d₁ := hmuinv x hx y hy hclose'
  set z := AffineMap.lineMap x y t with hz
  have hzmem : z ∈ standardFaceRegion := by
    have hseg : z ∈ segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    exact convex_standardFaceRegion.segment_subset hx hy hseg
  have hzx : dist z x < d₁ := by
    have hdist : dist z x = |t| * dist x y := by
      rw [hz, dist_lineMap_left, Real.norm_eq_abs]
    rw [hdist]
    calc |t| * dist x y ≤ 1 * dist x y := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          rw [abs_of_nonneg ht.1]
          exact ht.2
      _ = dist x y := one_mul _
      _ < d₁ := hxy
  exact (hd₁close z hzmem x hx hzx).le

/-- A canonical positive comparison scale for every face. -/
noncomputable def comparisonScale (G : K.PlaneGraphRealization) (f : K.Face) : ℝ :=
  Classical.choose (exists_comparisonScale G f)

theorem comparisonScale_pos (G : K.PlaneGraphRealization) (f : K.Face) :
    0 < comparisonScale G f :=
  (Classical.choose_spec (exists_comparisonScale G f)).1

theorem comparisonScale_le (G : K.PlaneGraphRealization) (f : K.Face) :
    comparisonScale G f ≤ faceVertexSeparationRadius G f / 8 :=
  (Classical.choose_spec (exists_comparisonScale G f)).2.1

theorem comparisonScale_segment (G : K.PlaneGraphRealization) (f : K.Face)
    {x y : Plane} (hx : x ∈ standardFaceRegion) (hy : y ∈ standardFaceRegion)
    (hclose : dist (faceOriginalMap G f x) (faceOriginalMap G f y) ≤
      2 * comparisonScale G f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (faceOriginalMap G f (AffineMap.lineMap x y t))
      (faceOriginalMap G f x) ≤ faceVertexSeparationRadius G f / 4 :=
  (Classical.choose_spec (exists_comparisonScale G f)).2.2 x hx y hy hclose t ht

/-! ## The standard index opposite a cyclic side -/

/-- The standard corner index not lying on cyclic side `i`. -/
noncomputable def standardOppIndex (i : ZMod 3) : Fin 3 :=
  (ZMod.finEquiv 3).symm (i + 2)

theorem finEquiv_symm_injective :
    Function.Injective ((ZMod.finEquiv 3).symm : ZMod 3 → Fin 3) :=
  (ZMod.finEquiv 3).symm.injective

theorem faceEdge_index_cases (f : K.Face) (i : ZMod 3) :
    (K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm i ∧
        K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm (i + 1)) ∨
      (K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm (i + 1) ∧
        K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm i) := by
  have hpair : ({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} :
      Finset (Fin 3)) =
      {(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :=
    (K.faceStandardEdge_eq_endpointIndices f i).symm
  have hfs : K.faceEdgeFirstIndex f i ∈
      ({(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :
        Finset (Fin 3)) := by
    rw [← hpair]
    exact Finset.mem_insert_self _ _
  have hss : K.faceEdgeSecondIndex f i ∈
      ({(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :
        Finset (Fin 3)) := by
    rw [← hpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hne := K.faceEdgeFirstIndex_ne_secondIndex f i
  rcases Finset.mem_insert.mp hfs with h₁ | h₁
  · rcases Finset.mem_insert.mp hss with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hne
    · exact Or.inl ⟨h₁, Finset.mem_singleton.mp h₂⟩
  · rcases Finset.mem_insert.mp hss with h₂ | h₂
    · exact Or.inr ⟨Finset.mem_singleton.mp h₁, h₂⟩
    · exact absurd ((Finset.mem_singleton.mp h₁).trans
        (Finset.mem_singleton.mp h₂).symm) hne

theorem standardOppIndex_ne_symm (i : ZMod 3) :
    standardOppIndex i ≠ (ZMod.finEquiv 3).symm i := by
  intro h
  exact (by decide : ∀ z : ZMod 3, z + 2 ≠ z) i (finEquiv_symm_injective h)

theorem standardOppIndex_ne_symm_succ (i : ZMod 3) :
    standardOppIndex i ≠ (ZMod.finEquiv 3).symm (i + 1) := by
  intro h
  exact (by decide : ∀ z : ZMod 3, z + 2 ≠ z + 1) i (finEquiv_symm_injective h)

theorem standardOppIndex_ne_firstIndex (f : K.Face) (i : ZMod 3) :
    standardOppIndex i ≠ K.faceEdgeFirstIndex f i := by
  rcases K.faceEdge_index_cases f i with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · rw [h₁]; exact standardOppIndex_ne_symm i
  · rw [h₁]; exact standardOppIndex_ne_symm_succ i

theorem standardOppIndex_ne_secondIndex (f : K.Face) (i : ZMod 3) :
    standardOppIndex i ≠ K.faceEdgeSecondIndex f i := by
  rcases K.faceEdge_index_cases f i with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · rw [h₂]; exact standardOppIndex_ne_symm_succ i
  · rw [h₂]; exact standardOppIndex_ne_symm i

theorem triCoord_oppIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (standardOppIndex i) (K.faceEdgeSourcePoint f i r) = 0 :=
  K.triCoord_other_sourcePoint f i (K.standardOppIndex_ne_firstIndex f i)
    (K.standardOppIndex_ne_secondIndex f i) r

/-- The three coordinates named by one side enumerate the whole coordinate sum. -/
theorem triCoord_side_sum (f : K.Face) (i : ZMod 3) (x : Plane) :
    triCoord (K.faceEdgeFirstIndex f i) x + triCoord (K.faceEdgeSecondIndex f i) x +
      triCoord (standardOppIndex i) x = 1 := by
  classical
  set a := K.faceEdgeFirstIndex f i
  set b := K.faceEdgeSecondIndex f i
  set c := standardOppIndex i
  have hab : a ≠ b := K.faceEdgeFirstIndex_ne_secondIndex f i
  have hca : c ≠ a := K.standardOppIndex_ne_firstIndex f i
  have hcb : c ≠ b := K.standardOppIndex_ne_secondIndex f i
  have hbc : b ∉ ({c} : Finset (Fin 3)) := by
    rw [Finset.mem_singleton]
    exact fun h => hcb h.symm
  have habc : a ∉ ({b, c} : Finset (Fin 3)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hab, fun h => hca h.symm⟩
  have hcard : ({a, b, c} : Finset (Fin 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem habc, Finset.card_insert_of_notMem hbc,
      Finset.card_singleton]
  have huniv : ({a, b, c} : Finset (Fin 3)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard]; rfl)
  have hsum := sum_triCoord x
  rw [← huniv, Finset.sum_insert habc, Finset.sum_insert hbc,
    Finset.sum_singleton] at hsum
  linarith

/-! ## The matched trim parameters of one side -/

/-- The original edge parameter matched to the polygonal arc's left exit. -/
noncomputable def sideTrimLeft (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : ℝ :=
  AffineMap.lineMap (G.edgeTrim (K.faceEdge f i)).left
    (G.edgeTrim (K.faceEdge f i)).right
    (G.replacementArc (K.faceEdge f i)).exitData.left

/-- The original edge parameter matched to the polygonal arc's right exit. -/
noncomputable def sideTrimRight (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : ℝ :=
  AffineMap.lineMap (G.edgeTrim (K.faceEdge f i)).left
    (G.edgeTrim (K.faceEdge f i)).right
    (G.replacementArc (K.faceEdge f i)).exitData.right

theorem sideTrim_left_le_right (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimLeft G f i ≤ sideTrimRight G f i := by
  have hT := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hX := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  simp only [sideTrimLeft, sideTrimRight, AffineMap.lineMap_apply_ring]
  nlinarith

theorem sideTrimLeft_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimLeft G f i ∈ Set.Icc (0 : ℝ) 1 := by
  have hTl := (G.edgeTrim (K.faceEdge f i)).left_pos
  have hTlr := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hTr := (G.edgeTrim (K.faceEdge f i)).right_lt_one
  have hXl := (G.replacementArc (K.faceEdge f i)).exitData.left_nonneg
  have hXlr := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  have hXr := (G.replacementArc (K.faceEdge f i)).exitData.right_le_one
  simp only [sideTrimLeft, AffineMap.lineMap_apply_ring]
  constructor <;> nlinarith

theorem sideTrimRight_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimRight G f i ∈ Set.Icc (0 : ℝ) 1 := by
  have hTl := (G.edgeTrim (K.faceEdge f i)).left_pos
  have hTlr := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hTr := (G.edgeTrim (K.faceEdge f i)).right_lt_one
  have hXl := (G.replacementArc (K.faceEdge f i)).exitData.left_nonneg
  have hXlr := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  have hXr := (G.replacementArc (K.faceEdge f i)).exitData.right_le_one
  simp only [sideTrimRight, AffineMap.lineMap_apply_ring]
  constructor <;> nlinarith

/-! ## The matched boundary parameter profile of one side -/

/-- The piecewise-affine reparametrization of one side matched to the complete replacement
path: the left spoke range covers the trimmed-off initial edge piece, the middle range covers
the matched trim window, and the right spoke range covers the trimmed-off final piece. -/
noncomputable def sideParamProfile (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then 2 * u * sideTrimLeft G f i
  else if u ≤ 3 / 4 then
    AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * u - 2)
  else AffineMap.lineMap (sideTrimRight G f i) 1 (4 * u - 3)

theorem continuous_sideParamProfile (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : Continuous (sideParamProfile G f i) := by
  apply Continuous.if_le
  · fun_prop
  · apply Continuous.if_le
    · simp only [AffineMap.lineMap_apply_ring]
      fun_prop
    · simp only [AffineMap.lineMap_apply_ring]
      fun_prop
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hu]
      norm_num [AffineMap.lineMap_apply_ring]
  · fun_prop
  · fun_prop
  · intro u hu
    rw [hu]
    norm_num [AffineMap.lineMap_apply_ring]

@[simp] theorem sideParamProfile_zero (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideParamProfile G f i 0 = 0 := by
  norm_num [sideParamProfile]

@[simp] theorem sideParamProfile_one (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideParamProfile G f i 1 = 1 := by
  norm_num [sideParamProfile, AffineMap.lineMap_apply_ring]

theorem sideParamProfile_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    sideParamProfile G f i u ∈ Set.Icc (0 : ℝ) 1 := by
  have hl := sideTrimLeft_mem G f i
  have hr := sideTrimRight_mem G f i
  have hlr := sideTrim_left_le_right G f i
  rw [sideParamProfile]
  split_ifs with h₁ h₂
  · constructor <;> nlinarith [hu.1, hu.2, hl.1, hl.2]
  · rw [AffineMap.lineMap_apply_ring]
    push Not at h₁
    constructor <;> nlinarith [hu.1, hu.2, hl.1, hl.2, hr.1, hr.2]
  · rw [AffineMap.lineMap_apply_ring]
    push Not at h₁ h₂
    constructor <;> nlinarith [hu.1, hu.2, hr.1, hr.2]

/-! ## The comparison piece adapted to one side -/

/-- The barycentric depth of a point relative to one side: `1` on the side, `0` at the
barycenter. -/
noncomputable def sideDepth (i : ZMod 3) (x : Plane) : ℝ :=
  1 - 3 * triCoord (standardOppIndex i) x

theorem continuous_sideDepth (i : ZMod 3) : Continuous (sideDepth i) :=
  continuous_const.sub
    (continuous_const.mul (continuous_triCoord (standardOppIndex i)))

/-- The raw radial side parameter of a point: on the side itself it is the oriented affine
side parameter; near the barycenter the clamped denominator keeps it continuous. -/
noncomputable def sideRawParam (f : K.Face) (i : ZMod 3) (x : Plane) : ℝ :=
  (triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3) /
      max (sideDepth i x) (1 / 3) + 1 / 3

theorem continuous_sideRawParam (f : K.Face) (i : ZMod 3) :
    Continuous (sideRawParam f i) := by
  apply Continuous.add _ continuous_const
  apply Continuous.div
  · exact (continuous_triCoord _).sub continuous_const
  · exact (continuous_sideDepth i).max continuous_const
  · intro x
    have : (0 : ℝ) < max (sideDepth i x) (1 / 3) :=
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact ne_of_gt this

/-- The comparison piece adapted to side `i`: the original face chart evaluated on the clamped
radial interpolation from the barycenter to the reparametrized side point. -/
noncomputable def sidePiece (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) : Plane :=
  faceOriginalMap G f (AffineMap.lineMap triCenter
    (K.faceEdgeSourcePoint f i
      (sideParamProfile G f i (unitClamp (sideRawParam f i x))))
    (unitClamp (3 * sideDepth i x - 1)))

/-- The domain point fed to the original chart by a side piece. -/
theorem sidePiece_arg_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) :
    AffineMap.lineMap triCenter
      (K.faceEdgeSourcePoint f i
        (sideParamProfile G f i (unitClamp (sideRawParam f i x))))
      (unitClamp (3 * sideDepth i x - 1)) ∈ standardFaceRegion := by
  apply lineMap_unitClamp_mem convex_standardFaceRegion
    triCenter_mem_standardFaceRegion
  exact K.faceEdgeSourcePoint_mem_region f i
    (sideParamProfile_mem G f i (unitClamp_mem _))

theorem sidePiece_mem_faceImage (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) :
    sidePiece G f i x ∈ G.map '' faceInSupport (K := K) f := by
  rw [sidePiece]
  exact faceOriginalMap_mem_face_image (G := G) f
    ⟨_, K.sidePiece_arg_mem G f i x⟩

theorem continuous_sidePiece (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : Continuous (sidePiece G f i) := by
  apply (continuousOn_faceOriginalMap (G := G) f).comp_continuous
  · have hpt : Continuous fun x : Plane =>
        K.faceEdgeSourcePoint f i
          (sideParamProfile G f i (unitClamp (sideRawParam f i x))) :=
      (K.continuous_faceEdgeSourcePoint f i).comp
        ((continuous_sideParamProfile G f i).comp
          (continuous_unitClamp.comp (K.continuous_sideRawParam f i)))
    have hcoef : Continuous fun x : Plane =>
        unitClamp (3 * sideDepth i x - 1) :=
      continuous_unitClamp.comp
        (((continuous_const.mul (continuous_sideDepth i)).sub continuous_const))
    simp only [AffineMap.lineMap_apply_module]
    exact ((continuous_const.sub hcoef).smul continuous_const).add (hcoef.smul hpt)
  · intro x
    exact K.sidePiece_arg_mem G f i x

/-! ## Evaluation of a side piece -/

theorem unitClamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : unitClamp t = 0 := by
  rw [unitClamp, min_eq_right (ht.trans zero_le_one), max_eq_left ht]

theorem unitClamp_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitClamp t = 1 := by
  rw [unitClamp, min_eq_left ht]
  exact max_eq_right zero_le_one

/-- On the side itself the raw parameter is the oriented affine side parameter. -/
theorem sideRawParam_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    sideRawParam f i (K.faceEdgeSourcePoint f i r) = r := by
  rw [sideRawParam, sideDepth, K.triCoord_oppIndex_sourcePoint f i r,
    K.triCoord_secondIndex_sourcePoint f i r]
  norm_num

theorem sideDepth_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    sideDepth i (K.faceEdgeSourcePoint f i r) = 1 := by
  rw [sideDepth, K.triCoord_oppIndex_sourcePoint f i r]
  norm_num

/-- A side piece evaluated on its own side is the reparametrized original boundary chart. -/
theorem sidePiece_sourcePoint (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    sidePiece G f i (K.faceEdgeSourcePoint f i r) =
      faceOriginalMap G f
        (K.faceEdgeSourcePoint f i (sideParamProfile G f i r)) := by
  rw [sidePiece, K.sideRawParam_sourcePoint f i r, K.sideDepth_sourcePoint f i r,
    unitClamp_of_mem hr, unitClamp_of_one_le (by norm_num),
    AffineMap.lineMap_apply_one]

/-- The first-corner evaluation: whenever the first endpoint coordinate agrees with the
opposite coordinate, the side piece interpolates toward the second corner. -/
theorem sidePiece_of_firstCoord_eq (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {x : Plane}
    (hcc : triCoord (K.faceEdgeFirstIndex f i) x =
      triCoord (standardOppIndex i) x) :
    sidePiece G f i x =
      faceOriginalMap G f (AffineMap.lineMap triCenter
        (standardTriangleVertex (K.faceEdgeSecondIndex f i))
        (unitClamp (3 * sideDepth i x - 1))) := by
  by_cases hd : 1 / 3 ≤ sideDepth i x
  · have hsum := K.triCoord_side_sum f i x
    have hraw : sideRawParam f i x = 1 := by
      rw [sideRawParam, max_eq_left hd]
      have hden : sideDepth i x ≠ 0 := by
        intro h0
        rw [h0] at hd
        norm_num at hd
      have hnum : triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3 =
          2 / 3 * sideDepth i x := by
        rw [sideDepth]
        linarith
      rw [hnum, mul_div_assoc, div_self hden]
      norm_num
    rw [sidePiece, hraw, unitClamp_one, sideParamProfile_one,
      faceEdgeSourcePoint_one]
  · push Not at hd
    have hcoef : unitClamp (3 * sideDepth i x - 1) = 0 :=
      unitClamp_of_nonpos (by linarith)
    rw [sidePiece, hcoef, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_zero]

/-- The second-corner evaluation: whenever the second endpoint coordinate agrees with the
opposite coordinate, the side piece interpolates toward the first corner. -/
theorem sidePiece_of_secondCoord_eq (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {x : Plane}
    (hcc : triCoord (K.faceEdgeSecondIndex f i) x =
      triCoord (standardOppIndex i) x) :
    sidePiece G f i x =
      faceOriginalMap G f (AffineMap.lineMap triCenter
        (standardTriangleVertex (K.faceEdgeFirstIndex f i))
        (unitClamp (3 * sideDepth i x - 1))) := by
  by_cases hd : 1 / 3 ≤ sideDepth i x
  · have hraw : sideRawParam f i x = 0 := by
      rw [sideRawParam, max_eq_left hd]
      have hden : sideDepth i x ≠ 0 := by
        intro h0
        rw [h0] at hd
        norm_num at hd
      have hnum : triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3 =
          -(1 / 3) * sideDepth i x := by
        rw [sideDepth, hcc]
        ring
      rw [hnum, mul_div_assoc, div_self hden]
      norm_num
    rw [sidePiece, hraw, unitClamp_zero, sideParamProfile_zero,
      faceEdgeSourcePoint_zero]
  · push Not at hd
    have hcoef : unitClamp (3 * sideDepth i x - 1) = 0 :=
      unitClamp_of_nonpos (by linarith)
    rw [sidePiece, hcoef, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_zero]

/-! ## Agreement of adjacent side pieces -/

theorem standardOppIndex_succ (i : ZMod 3) :
    standardOppIndex (i + 1) = (ZMod.finEquiv 3).symm i := by
  rw [standardOppIndex]
  congr 1
  have h30 : (3 : ZMod 3) = 0 := by decide
  calc i + 1 + 2 = i + 3 := by ring
    _ = i := by rw [h30, add_zero]

theorem standardOppIndex_succ_succ (i : ZMod 3) :
    standardOppIndex (i + 2) = (ZMod.finEquiv 3).symm (i + 1) := by
  rw [standardOppIndex]
  congr 1
  have h30 : (3 : ZMod 3) = 0 := by decide
  calc i + 2 + 2 = i + 1 + 3 := by ring
    _ = i + 1 := by rw [h30, add_zero]

/-- Two side pieces agree wherever their opposite coordinates agree.  This is the closed
interface condition of the sector decomposition; no minimality is required. -/
theorem sidePiece_interface (G : K.PlaneGraphRealization) (f : K.Face)
    {i i' : ZMod 3} (hne : i ≠ i') {x : Plane}
    (heq : triCoord (standardOppIndex i) x =
      triCoord (standardOppIndex i') x) :
    sidePiece G f i x = sidePiece G f i' x := by
  have hdepth : sideDepth i x = sideDepth i' x := by
    rw [sideDepth, sideDepth, heq]
  have hcase : i' = i + 1 ∨ i' = i + 2 := by
    have h3 : ∀ a b : ZMod 3, a ≠ b → b = a + 1 ∨ b = a + 2 := by decide
    exact h3 i i' hne
  have h30 : (3 : ZMod 3) = 0 := by decide
  rcases hcase with rfl | rfl
  · -- shared corner: `symm (i + 1)`
    have hopp' : standardOppIndex (i + 1) = (ZMod.finEquiv 3).symm i :=
      standardOppIndex_succ i
    have e1 : i + 1 + 1 = i + 2 := by ring
    have hleft : sidePiece G f i x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
          (unitClamp (3 * sideDepth i x - 1))) := by
      rcases K.faceEdge_index_cases f i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have hcc : triCoord (K.faceEdgeFirstIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₁, ← hopp', ← heq]
        rw [K.sidePiece_of_firstCoord_eq G f i hcc, h₂]
      · have hcc : triCoord (K.faceEdgeSecondIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₂, ← hopp', ← heq]
        rw [K.sidePiece_of_secondCoord_eq G f i hcc, h₁]
    have hright : sidePiece G f (i + 1) x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
          (unitClamp (3 * sideDepth (i + 1) x - 1))) := by
      rcases K.faceEdge_index_cases f (i + 1) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the second endpoint of side `i + 1` is the opposite corner of side `i`
        have hcc : triCoord (K.faceEdgeSecondIndex f (i + 1)) x =
            triCoord (standardOppIndex (i + 1)) x := by
          rw [h₂, e1]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_secondCoord_eq G f (i + 1) hcc, h₁]
      · have hcc : triCoord (K.faceEdgeFirstIndex f (i + 1)) x =
            triCoord (standardOppIndex (i + 1)) x := by
          rw [h₁, e1]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_firstCoord_eq G f (i + 1) hcc, h₂]
    rw [hleft, hright, hdepth]
  · -- shared corner: `symm i`
    have hopp' : standardOppIndex (i + 2) = (ZMod.finEquiv 3).symm (i + 1) :=
      standardOppIndex_succ_succ i
    have e2 : i + 2 + 1 = i := by
      calc i + 2 + 1 = i + 3 := by ring
        _ = i := by rw [h30, add_zero]
    have hleft : sidePiece G f i x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
          (unitClamp (3 * sideDepth i x - 1))) := by
      rcases K.faceEdge_index_cases f i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the second endpoint `symm (i + 1)` is the opposite corner of side `i + 2`
        have hcc : triCoord (K.faceEdgeSecondIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₂, ← hopp', ← heq]
        rw [K.sidePiece_of_secondCoord_eq G f i hcc, h₁]
      · have hcc : triCoord (K.faceEdgeFirstIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₁, ← hopp', ← heq]
        rw [K.sidePiece_of_firstCoord_eq G f i hcc, h₂]
    have hright : sidePiece G f (i + 2) x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
          (unitClamp (3 * sideDepth (i + 2) x - 1))) := by
      rcases K.faceEdge_index_cases f (i + 2) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the first endpoint of side `i + 2` is the opposite corner of side `i`
        have hcc : triCoord (K.faceEdgeFirstIndex f (i + 2)) x =
            triCoord (standardOppIndex (i + 2)) x := by
          rw [h₁]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_firstCoord_eq G f (i + 2) hcc, h₂, e2]
      · have hcc : triCoord (K.faceEdgeSecondIndex f (i + 2)) x =
            triCoord (standardOppIndex (i + 2)) x := by
          rw [h₂]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_secondCoord_eq G f (i + 2) hcc, h₁, e2]
    rw [hleft, hright, hdepth]

/-! ## The assembled facewise comparison map -/

/-- The comparison map of one face: the three side pieces glued over the closed sectors on
which the corresponding opposite coordinate is minimal. -/
noncomputable def facewiseComparison (G : K.PlaneGraphRealization) (f : K.Face)
    (x : Plane) : Plane :=
  if triCoord (standardOppIndex 0) x ≤
      min (triCoord (standardOppIndex 1) x) (triCoord (standardOppIndex 2) x) then
    sidePiece G f 0 x
  else if triCoord (standardOppIndex 1) x ≤ triCoord (standardOppIndex 2) x then
    sidePiece G f 1 x
  else sidePiece G f 2 x

theorem facewiseComparison_mem_faceImage (G : K.PlaneGraphRealization)
    (f : K.Face) (x : Plane) :
    facewiseComparison G f x ∈ G.map '' faceInSupport (K := K) f := by
  rw [facewiseComparison]
  split_ifs <;> exact K.sidePiece_mem_faceImage G f _ x

theorem continuousOn_facewiseComparison (G : K.PlaneGraphRealization)
    (f : K.Face) :
    ContinuousOn (facewiseComparison G f) standardFaceRegion := by
  apply ContinuousOn.if
  · rintro a ⟨-, haF⟩
    have haeq : triCoord (standardOppIndex 0) a =
        min (triCoord (standardOppIndex 1) a) (triCoord (standardOppIndex 2) a) :=
      frontier_le_subset_eq (continuous_triCoord _)
        ((continuous_triCoord _).min (continuous_triCoord _)) haF
    by_cases h12 : triCoord (standardOppIndex 1) a ≤ triCoord (standardOppIndex 2) a
    · have h01 : triCoord (standardOppIndex 0) a =
          triCoord (standardOppIndex 1) a := by
        rw [haeq, min_eq_left h12]
      rw [K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 1) h01, if_pos h12]
    · have h02 : triCoord (standardOppIndex 0) a =
          triCoord (standardOppIndex 2) a := by
        rw [haeq, min_eq_right (le_of_not_ge h12)]
      rw [K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 2) h02, if_neg h12]
  · exact (K.continuous_sidePiece G f 0).continuousOn
  · apply ContinuousOn.if
    · rintro a ⟨-, haF⟩
      have haeq : triCoord (standardOppIndex 1) a =
          triCoord (standardOppIndex 2) a :=
        frontier_le_subset_eq (continuous_triCoord _) (continuous_triCoord _) haF
      exact K.sidePiece_interface G f (by decide : (1 : ZMod 3) ≠ 2) haeq
    · exact (K.continuous_sidePiece G f 1).continuousOn
    · exact (K.continuous_sidePiece G f 2).continuousOn

/-- On the closed sector of side `i` — in fact anywhere the opposite coordinate of side `i`
vanishes — the comparison map is the side-`i` piece. -/
theorem facewiseComparison_eq_sidePiece (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3) {x : Plane} (hx : x ∈ standardFaceRegion)
    (hzero : triCoord (standardOppIndex i) x = 0) :
    facewiseComparison G f x = sidePiece G f i x := by
  have hnn : ∀ j : Fin 3, 0 ≤ triCoord j x := mem_standardFaceRegion_iff.mp hx
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    have h3 : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
    exact h3 i
  rw [facewiseComparison]
  rcases hi with rfl | rfl | rfl
  · rw [if_pos]
    rw [hzero]
    exact le_min (hnn _) (hnn _)
  · split_ifs with h₀ h₁
    · apply K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 1)
      have h₀' : triCoord (standardOppIndex 0) x ≤ 0 := by
        rw [← hzero]
        exact h₀.trans (min_le_left _ _)
      rw [le_antisymm h₀' (hnn _), hzero]
    · rfl
    · exact absurd (hzero ▸ hnn (standardOppIndex 2)) h₁
  · split_ifs with h₀ h₁
    · apply K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 2)
      have h₀' : triCoord (standardOppIndex 0) x ≤ 0 := by
        rw [← hzero]
        exact h₀.trans (min_le_right _ _)
      rw [le_antisymm h₀' (hnn _), hzero]
    · apply K.sidePiece_interface G f (by decide : (1 : ZMod 3) ≠ 2)
      have h₁' : triCoord (standardOppIndex 1) x ≤ 0 := hzero ▸ h₁
      rw [le_antisymm h₁' (hnn _), hzero]
    · rfl

/-! ## The boundary estimate -/

private theorem dist_completePath_comparison_lt_of_middle (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3)
    (htube : G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (hr2 : ¬r ≤ 1 / 2) (hr34 : r ≤ 3 / 4) :
    dist ((G.replacementArc (K.faceEdge f i)).completePath ⟨r, hr⟩)
        (faceOriginalMap G f
          (K.faceEdgeSourcePoint f i (sideParamProfile G f i r))) <
      faceVertexSeparationRadius G f / 2 := by
  set e := K.faceEdge f i with he
  set A := G.replacementArc e with hA
  have hXl : A.exitData.left ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg,
      A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩
  have hXr : A.exitData.right ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg.trans A.exitData.left_lt_right.le,
      A.exitData.right_le_one⟩
  have hw : (0 : ℝ) ≤ 2 * (2 * r - 1) ∧ 2 * (2 * r - 1) ≤ 1 := by
    constructor <;> nlinarith [not_le.mp hr2]
  have hcp : A.completePath ⟨r, hr⟩ =
      A.parameterizationData.curve
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))) := by
    rw [CentralPolygonalArc.completePath, Path.trans_apply]
    rw [dif_neg (show ¬ ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2 from hr2)]
    rw [Path.trans_apply]
    rw [dif_pos (by
      change (2 * ((⟨r, hr⟩ : unitInterval) : ℝ) - 1) ≤ 1 / 2
      linarith)]
    change A.parameterizationData.curve
        (Path.segment A.exitData.left A.exitData.right _) = _
    rw [Path.segment_apply]
  have hprofile : sideParamProfile G f i r =
      AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * r - 2) := by
    rw [sideParamProfile, if_neg hr2, if_pos hr34]
  have hT : AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * r - 2) =
      (G.edgeTrim e).left + ((G.edgeTrim e).right - (G.edgeTrim e).left) *
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))) := by
    simp only [sideTrimLeft, sideTrimRight, AffineMap.lineMap_apply_ring]
    rw [← he]
    ring
  have htmem : AffineMap.lineMap A.exitData.left A.exitData.right
      (2 * (2 * r - 1)) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [AffineMap.lineMap_apply_ring]
    have hlr := A.exitData.left_lt_right
    constructor <;> nlinarith [hXl.1, hXl.2, hXr.1, hXr.2, hw.1, hw.2]
  have hpmem : sideParamProfile G f i r ∈ Set.Icc (0 : ℝ) 1 :=
    sideParamProfile_mem G f i hr
  rw [hcp, K.faceOriginalMap_sourcePoint f i hpmem, hprofile, hT]
  have hclose := A.curve_close _ htmem
  calc
    dist (A.parameterizationData.curve
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))))
        (G.chartEdgeCurve e ((G.edgeTrim e).left +
          ((G.edgeTrim e).right - (G.edgeTrim e).left) *
            AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1)))) <
      G.centralTubeRadius e := hclose
    _ ≤ faceVertexSeparationRadius G f / 2 := by
      have := htube.trans (comparisonScale_le G f)
      linarith [faceVertexSeparationRadius_pos (G := G) f]

/-- The complete replacement path of one side stays within half the face separation radius of
the reparametrized original boundary chart, once the vertex isolation disks and the central
tube are below the comparison scale. -/
theorem dist_completePath_comparison_lt (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3)
    (hiso₁ : G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
      comparisonScale G f)
    (hiso₂ : G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
      comparisonScale G f)
    (htube : G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    dist ((G.replacementArc (K.faceEdge f i)).completePath ⟨r, hr⟩)
        (faceOriginalMap G f
          (K.faceEdgeSourcePoint f i (sideParamProfile G f i r))) <
      faceVertexSeparationRadius G f / 2 := by
  classical
  set e := K.faceEdge f i with he
  set A := G.replacementArc e with hA
  set eta := comparisonScale G f with heta
  set rsep := faceVertexSeparationRadius G f with hrsep
  have hrsep_pos : 0 < rsep := faceVertexSeparationRadius_pos (G := G) f
  have heta8 : eta ≤ rsep / 8 := comparisonScale_le G f
  have hXl : A.exitData.left ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg,
      A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩
  have hXr : A.exitData.right ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg.trans A.exitData.left_lt_right.le,
      A.exitData.right_le_one⟩
  -- the two matched endpoint estimates
  have hPLQ : dist A.leftEndpoint (G.chartEdgeCurve e (sideTrimLeft G f i)) <
      G.centralTubeRadius e := by
    have hclose := A.curve_close A.exitData.left hXl
    have harg : (G.edgeTrim e).left +
        ((G.edgeTrim e).right - (G.edgeTrim e).left) * A.exitData.left =
        sideTrimLeft G f i := by
      rw [sideTrimLeft, AffineMap.lineMap_apply_ring, ← he]
      ring
    rw [harg] at hclose
    exact hclose
  have hPRQ : dist A.rightEndpoint (G.chartEdgeCurve e (sideTrimRight G f i)) <
      G.centralTubeRadius e := by
    have hclose := A.curve_close A.exitData.right hXr
    have harg : (G.edgeTrim e).left +
        ((G.edgeTrim e).right - (G.edgeTrim e).left) * A.exitData.right =
        sideTrimRight G f i := by
      rw [sideTrimRight, AffineMap.lineMap_apply_ring, ← he]
      ring
    rw [harg] at hclose
    exact hclose
  -- chart values at the distinguished side parameters
  have hsrc0 : faceOriginalMap G f (K.faceEdgeSourcePoint f i 0) =
      G.vertexImage (K.edgeFirst e) := by
    rw [K.faceOriginalMap_sourcePoint f i (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    exact G.chartEdgeCurve_zero e
  have hsrc1 : faceOriginalMap G f (K.faceEdgeSourcePoint f i 1) =
      G.vertexImage (K.edgeSecond e) := by
    rw [K.faceOriginalMap_sourcePoint f i (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    exact G.chartEdgeCurve_one e
  have hsrcL : faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) =
      G.chartEdgeCurve e (sideTrimLeft G f i) :=
    K.faceOriginalMap_sourcePoint f i (sideTrimLeft_mem G f i)
  have hsrcR : faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimRight G f i)) =
      G.chartEdgeCurve e (sideTrimRight G f i) :=
    K.faceOriginalMap_sourcePoint f i (sideTrimRight_mem G f i)
  -- the modulus premises at the two corners
  have hmodL : dist (faceOriginalMap G f (K.faceEdgeSourcePoint f i 0))
      (faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimLeft G f i))) ≤
      2 * eta := by
    rw [hsrc0, hsrcL]
    calc dist (G.vertexImage (K.edgeFirst e))
          (G.chartEdgeCurve e (sideTrimLeft G f i)) ≤
        dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint +
          dist A.leftEndpoint (G.chartEdgeCurve e (sideTrimLeft G f i)) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeFirst e) + G.centralTubeRadius e := by
          apply add_le_add _ hPLQ.le
          rw [dist_comm]
          exact (A.leftEndpoint_on_sphere).le
      _ ≤ 2 * eta := by rw [two_mul]; exact add_le_add hiso₁ htube
  have hmodR : dist (faceOriginalMap G f (K.faceEdgeSourcePoint f i 1))
      (faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimRight G f i))) ≤
      2 * eta := by
    rw [hsrc1, hsrcR]
    calc dist (G.vertexImage (K.edgeSecond e))
          (G.chartEdgeCurve e (sideTrimRight G f i)) ≤
        dist (G.vertexImage (K.edgeSecond e)) A.rightEndpoint +
          dist A.rightEndpoint (G.chartEdgeCurve e (sideTrimRight G f i)) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeSecond e) + G.centralTubeRadius e := by
          apply add_le_add _ hPRQ.le
          rw [dist_comm]
          exact (A.rightEndpoint_on_sphere).le
      _ ≤ 2 * eta := by rw [two_mul]; exact add_le_add hiso₂ htube
  by_cases hr2 : r ≤ 1 / 2
  · -- left spoke
    have hcp : A.completePath ⟨r, hr⟩ =
        AffineMap.lineMap (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
          (2 * r) := by
      rw [CentralPolygonalArc.completePath, Path.trans_apply]
      rw [dif_pos (show ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2 from hr2)]
      rw [Path.segment_apply]
    have hprofile : sideParamProfile G f i r = 2 * r * sideTrimLeft G f i := by
      rw [sideParamProfile, if_pos hr2]
    have hsrcpt : K.faceEdgeSourcePoint f i (2 * r * sideTrimLeft G f i) =
        AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
          (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r) := by
      have harg : 2 * r * sideTrimLeft G f i =
          AffineMap.lineMap (0 : ℝ) (sideTrimLeft G f i) (2 * r) := by
        rw [AffineMap.lineMap_apply_ring]
        ring
      rw [harg, faceEdgeSourcePoint]
      exact (AffineMap.lineMap _ _).apply_lineMap _ _ _
    rw [hcp, hprofile, hsrcpt]
    have h2r : (2 : ℝ) * r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hr.1], by linarith⟩
    calc dist (AffineMap.lineMap (G.vertexImage (K.edgeFirst e))
            A.leftEndpoint (2 * r))
          (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
            (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r))) ≤
        dist (AffineMap.lineMap (G.vertexImage (K.edgeFirst e))
            A.leftEndpoint (2 * r)) (G.vertexImage (K.edgeFirst e)) +
          dist (G.vertexImage (K.edgeFirst e))
            (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
              (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r))) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeFirst e) + rsep / 4 := by
          apply add_le_add
          · rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg h2r.1]
            calc 2 * r * dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint ≤
                1 * dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint :=
                  mul_le_mul_of_nonneg_right h2r.2 dist_nonneg
              _ = G.vertexIsolationRadius (K.edgeFirst e) := by
                  rw [one_mul, dist_comm]
                  exact A.leftEndpoint_on_sphere
          · rw [← hsrc0, dist_comm]
            exact comparisonScale_segment G f
              (K.faceEdgeSourcePoint_mem_region f i (by norm_num))
              (K.faceEdgeSourcePoint_mem_region f i (sideTrimLeft_mem G f i))
              hmodL h2r
      _ < rsep / 2 := by
          have : G.vertexIsolationRadius (K.edgeFirst e) ≤ rsep / 8 :=
            hiso₁.trans heta8
          linarith
  · by_cases hr34 : r ≤ 3 / 4
    · -- middle range
      exact dist_completePath_comparison_lt_of_middle G f i htube hr hr2 hr34
    · -- right spoke
      push Not at hr2 hr34
      have hw : (0 : ℝ) ≤ 2 * (2 * r - 1) - 1 ∧ 2 * (2 * r - 1) - 1 ≤ 1 := by
        constructor <;> nlinarith [hr.2]
      have hcp : A.completePath ⟨r, hr⟩ =
          AffineMap.lineMap A.rightEndpoint (G.vertexImage (K.edgeSecond e))
            (2 * (2 * r - 1) - 1) := by
        rw [CentralPolygonalArc.completePath, Path.trans_apply]
        rw [dif_neg (by linarith : ¬ ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2)]
        rw [Path.trans_apply]
        rw [dif_neg (by
          change ¬ (2 * ((⟨r, hr⟩ : unitInterval) : ℝ) - 1) ≤ 1 / 2
          linarith)]
        rw [Path.segment_apply]
      have hprofile : sideParamProfile G f i r =
          AffineMap.lineMap (sideTrimRight G f i) 1 (4 * r - 3) := by
        rw [sideParamProfile, if_neg (not_le.mpr hr2), if_neg (not_le.mpr hr34)]
      have hw' : 4 * r - 3 = 2 * (2 * r - 1) - 1 := by ring
      have hsrcpt : K.faceEdgeSourcePoint f i
          (AffineMap.lineMap (sideTrimRight G f i) 1 (4 * r - 3)) =
          AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
            (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
            (1 - (2 * (2 * r - 1) - 1)) := by
        rw [faceEdgeSourcePoint]
        rw [show AffineMap.lineMap (sideTrimRight G f i) (1:ℝ) (4 * r - 3) =
            AffineMap.lineMap (1:ℝ) (sideTrimRight G f i)
              (1 - (2 * (2 * r - 1) - 1)) by
          simp only [AffineMap.lineMap_apply_ring]
          ring]
        exact (AffineMap.lineMap _ _).apply_lineMap _ _ _
      rw [hcp, hprofile, hsrcpt]
      have h1w : (1 : ℝ) - (2 * (2 * r - 1) - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hw.2], by linarith [hw.1]⟩
      calc dist (AffineMap.lineMap A.rightEndpoint
              (G.vertexImage (K.edgeSecond e)) (2 * (2 * r - 1) - 1))
            (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
              (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
              (1 - (2 * (2 * r - 1) - 1)))) ≤
          dist (AffineMap.lineMap A.rightEndpoint
              (G.vertexImage (K.edgeSecond e)) (2 * (2 * r - 1) - 1))
            (G.vertexImage (K.edgeSecond e)) +
            dist (G.vertexImage (K.edgeSecond e))
              (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
                (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
                (1 - (2 * (2 * r - 1) - 1)))) := dist_triangle _ _ _
        _ ≤ G.vertexIsolationRadius (K.edgeSecond e) + rsep / 4 := by
            apply add_le_add
            · rw [dist_lineMap_right, Real.norm_eq_abs,
                abs_of_nonneg (by linarith [hw.2] : (0:ℝ) ≤ 1 - (2 * (2 * r - 1) - 1))]
              calc (1 - (2 * (2 * r - 1) - 1)) *
                  dist A.rightEndpoint (G.vertexImage (K.edgeSecond e)) ≤
                  1 * dist A.rightEndpoint (G.vertexImage (K.edgeSecond e)) :=
                    mul_le_mul_of_nonneg_right (by linarith [hw.1]) dist_nonneg
                _ = G.vertexIsolationRadius (K.edgeSecond e) := by
                    rw [one_mul]
                    exact A.rightEndpoint_on_sphere
            · rw [← hsrc1, dist_comm]
              exact comparisonScale_segment G f
                (K.faceEdgeSourcePoint_mem_region f i (by norm_num))
                (K.faceEdgeSourcePoint_mem_region f i (sideTrimRight_mem G f i))
                hmodR h1w
        _ < rsep / 2 := by
            have : G.vertexIsolationRadius (K.edgeSecond e) ≤ rsep / 8 :=
              hiso₂.trans heta8
            linarith

/-- The graph replacement on one face boundary stays within half the face separation radius of
the facewise comparison map. -/
theorem facewiseComparison_close (G : K.PlaneGraphRealization) (f : K.Face)
    (hiso : ∀ i : ZMod 3,
      G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          comparisonScale G f ∧
        G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          comparisonScale G f)
    (htube : ∀ i : ZMod 3,
      G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    (q : StandardFaceBoundary) :
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
        (facewiseComparison G f q.1) < faceVertexSeparationRadius G f / 2 := by
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i,
    ← K.faceEdgeSourcePoint_image_Icc f i] at hi
  obtain ⟨r, hrIcc, hrq⟩ := hi
  have hLHS : G.graphReplacementMap (K.faceBoundaryLift f q) =
      (G.replacementArc (K.faceEdge f i)).completePath ⟨r, hrIcc⟩ := by
    rw [← K.faceBoundaryMap_apply (G := G) f q, ← hrq]
    exact K.faceBoundaryMap_sourcePoint (G := G) f i ⟨r, hrIcc⟩
  have hRHS : facewiseComparison G f q.1 =
      faceOriginalMap G f
        (K.faceEdgeSourcePoint f i (sideParamProfile G f i r)) := by
    rw [← hrq]
    rw [K.facewiseComparison_eq_sidePiece G f i
      (K.faceEdgeSourcePoint_mem_region f i hrIcc)
      (K.triCoord_oppIndex_sourcePoint f i r)]
    exact K.sidePiece_sourcePoint G f i hrIcc
  rw [hLHS, hRHS]
  exact K.dist_completePath_comparison_lt G f i (hiso i).1 (hiso i).2 (htube i) hrIcc

/-- The complete cellwise compatibility package from comparison-scale-small approximation
data.  This is the honest side-preservation discharge for the locally finite Chapter 6
replacement: no same-parameter mesh estimate enters. -/
theorem cellwiseCompatibility_of_comparisonScale (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices)
    (hiso : ∀ (f : K.Face) (i : ZMod 3),
      G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          comparisonScale G f ∧
        G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          comparisonScale G f)
    (htube : ∀ (f : K.Face) (i : ZMod 3),
      G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  apply cellwiseCompatibility_of_comparison hfaces
    (fun f => facewiseComparison G f)
    (fun f => K.continuousOn_facewiseComparison G f)
    (fun f p _ => Metric.self_subset_cthickening _
      (K.facewiseComparison_mem_faceImage G f p))
    (fun f q => K.facewiseComparison_close G f (hiso f) (htube f) q)
    hregion hloc

/-! ## Choosing the approximation controls below every incident comparison scale -/

/-- The support point of a global vertex. -/
noncomputable def vertexSupportPoint (K : LocallyFiniteTriangleComplex S) (v : K.Vertex) :
    K.support :=
  ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩

/-- The minimum comparison scale among the finitely many faces through a vertex. -/
noncomputable def comparisonVertexControl (G : K.PlaneGraphRealization)
    (v : K.Vertex) : ℝ :=
  ((facesContaining (K := K) (K.vertexSupportPoint v)).image
    (comparisonScale G)).min' ((facesContaining_nonempty _).image _)

theorem comparisonVertexControl_pos (G : K.PlaneGraphRealization)
    (v : K.Vertex) : 0 < comparisonVertexControl G v := by
  have hmem := Finset.min'_mem
    ((facesContaining (K := K) (K.vertexSupportPoint v)).image (comparisonScale G))
    ((facesContaining_nonempty _).image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [comparisonVertexControl, ← hf]
  exact comparisonScale_pos G f

theorem comparisonVertexControl_le (G : K.PlaneGraphRealization)
    {v : K.Vertex} {f : K.Face} (hv : v ∈ K.faceVertices f) :
    comparisonVertexControl G v ≤ comparisonScale G f := by
  apply Finset.min'_le
  apply Finset.mem_image_of_mem
  exact mem_facesContaining.mpr
    ((K.vertexSupportPoint_mem_faceInSupport_iff f v).mpr hv)

/-- The minimum comparison scale among the finitely many faces meeting an edge. -/
noncomputable def comparisonEdgeControl (G : K.PlaneGraphRealization)
    (e : K.Edge) : ℝ :=
  ((finite_edgeMeetingFaces (K := K) e).toFinset.image
    (comparisonScale G)).min'
    (Finset.Nonempty.image
      ⟨K.edgeFace e, (Set.Finite.mem_toFinset _).mpr
        (K.edgeFace_mem_edgeMeetingFaces e)⟩ _)

theorem comparisonEdgeControl_pos (G : K.PlaneGraphRealization) (e : K.Edge) :
    0 < comparisonEdgeControl G e := by
  have hmem := Finset.min'_mem
    ((finite_edgeMeetingFaces (K := K) e).toFinset.image (comparisonScale G))
    (Finset.Nonempty.image
      ⟨K.edgeFace e, (Set.Finite.mem_toFinset _).mpr
        (K.edgeFace_mem_edgeMeetingFaces e)⟩ _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [comparisonEdgeControl, ← hf]
  exact comparisonScale_pos G f

theorem comparisonEdgeControl_le (G : K.PlaneGraphRealization)
    {e : K.Edge} {f : K.Face} (hf : f ∈ K.edgeMeetingFaces e) :
    comparisonEdgeControl G e ≤ comparisonScale G f := by
  apply Finset.min'_le
  exact Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hf)

/-! ## Invariance of the comparison data under control shrinking -/

theorem faceVertexSeparationRadius_withApproximationControls
    (G : K.PlaneGraphRealization)
    (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
    (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e) (f : K.Face) :
    faceVertexSeparationRadius (G.withApproximationControls vc hvc ec hec) f =
      faceVertexSeparationRadius G f := rfl

theorem comparisonScale_withApproximationControls (G : K.PlaneGraphRealization)
    (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
    (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e) (f : K.Face) :
    comparisonScale (G.withApproximationControls vc hvc ec hec) f =
      comparisonScale G f := rfl

/-- **The side-preservation discharge with shrunken controls.**  For every locally finite
realization there are strictly positive replacement controls below which the complete
cellwise compatibility package holds; the shrunken realization keeps the same map, region and
separation radii. -/
theorem exists_controls_cellwiseCompatibility (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) :
    ∃ (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
      (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e),
      ∀ (_ : ∀ f : K.Face,
          (K.facePolygonalCircle
            (G := G.withApproximationControls vc hvc ec hec) f).closedRegion ⊆
            (G.withApproximationControls vc hvc ec hec).region)
        (_ : LocallyFinite fun f : K.Face ↦
          {q : (G.withApproximationControls vc hvc ec hec).region | q.1 ∈
            (K.facePolygonalCircle
              (G := G.withApproximationControls vc hvc ec hec) f).closedRegion}),
        Nonempty (K.CellwiseCompatibility
          (G.withApproximationControls vc hvc ec hec)) := by
  refine ⟨comparisonVertexControl G, comparisonVertexControl_pos G,
    comparisonEdgeControl G, comparisonEdgeControl_pos G, ?_⟩
  intro hregion hloc
  set G' := G.withApproximationControls (comparisonVertexControl G)
    (comparisonVertexControl_pos G) (comparisonEdgeControl G)
    (comparisonEdgeControl_pos G) with hG'
  refine ⟨K.cellwiseCompatibility_of_comparisonScale G' hfaces ?_ ?_ hregion hloc⟩
  · intro f i
    have hscale : comparisonScale G' f = comparisonScale G f :=
      comparisonScale_withApproximationControls G _ _ _ _ f
    constructor
    · calc G'.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          G'.vertexApproximationControl (K.edgeFirst (K.faceEdge f i)) :=
            G'.vertexIsolationRadius_le_control _
        _ = comparisonVertexControl G (K.edgeFirst (K.faceEdge f i)) := rfl
        _ ≤ comparisonScale G f :=
            comparisonVertexControl_le G (K.edgeFirst_faceEdge_mem_face f i)
        _ = comparisonScale G' f := hscale.symm
    · calc G'.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          G'.vertexApproximationControl (K.edgeSecond (K.faceEdge f i)) :=
            G'.vertexIsolationRadius_le_control _
        _ = comparisonVertexControl G (K.edgeSecond (K.faceEdge f i)) := rfl
        _ ≤ comparisonScale G f :=
            comparisonVertexControl_le G (K.edgeSecond_faceEdge_mem_face f i)
        _ = comparisonScale G' f := hscale.symm
  · intro f i
    have hscale : comparisonScale G' f = comparisonScale G f :=
      comparisonScale_withApproximationControls G _ _ _ _ f
    calc G'.centralTubeRadius (K.faceEdge f i) ≤
        G'.edgeApproximationControl (K.faceEdge f i) :=
          G'.centralTubeRadius_le_control _
      _ = comparisonEdgeControl G (K.faceEdge f i) := rfl
      _ ≤ comparisonScale G f :=
          comparisonEdgeControl_le G (K.faceEdge_mem_edgeMeetingFaces f i)
      _ = comparisonScale G' f := hscale.symm

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification16_block_04
/- END ClassificationOfSurfaces.Moise.FacewiseComparison -/

/- BEGIN ClassificationOfSurfaces.Moise.AdaptiveControlledApproximation | 3bc662a28601e368248cacbc7995af41b4fef36a5e5fcdf372d679d9d218e780 -/
section schottkyclassification16_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Adaptive meshes for strongly-positive metric controls

Moise Chapter 6 first subdivides the source until every simplex is small compared with the
prescribed strongly-positive tolerance.  This file supplies that step for the locally finite
adaptive triangulation.  Strong positivity gives a uniform lower bound on a compact
neighborhood of each point; continuity then shrinks that neighborhood until its image has small
diameter.  Subordination to the resulting open cover converts the existing setwise polygonal
graph replacement into a pointwise controlled approximation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open Filter

/-- A neighborhood on which `phi` has a fixed positive lower bound and the image of `f` has
diameter at most one quarter of that bound. -/
structure ControlledNeighborhood {X : Type*} [TopologicalSpace X]
    (f : X → Plane) (phi : X → ℝ) (x : X) where
  /-- The `set` declaration. -/
  set : Set X
  isOpen : IsOpen set
  mem_set : x ∈ set
  /-- The `scale` declaration. -/
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  scale_le : ∀ y ∈ set, scale ≤ phi y
  dist_le_quarter : ∀ y ∈ set, ∀ z ∈ set,
    dist (f y) (f z) ≤ scale / 4

/-- Strong positivity and local compactness produce controlled neighborhoods for every point. -/
theorem exists_controlledNeighborhood {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {f : X → Plane} (hf : Continuous f)
    {phi : X → ℝ} (hphi : StronglyPositiveOn Set.univ phi) (x : X) :
    Nonempty (ControlledNeighborhood f phi x) := by
  obtain ⟨C, hCcompact, hCnhds⟩ := exists_compact_mem_nhds x
  obtain ⟨eps, heps, heps_le⟩ := hphi C hCcompact (Set.subset_univ C)
  let delta := min eps 1
  have hdelta : 0 < delta := lt_min heps zero_lt_one
  let W : Set X := interior C ∩ f ⁻¹' Metric.ball (f x) (delta / 8)
  have hxInterior : x ∈ interior C := mem_interior_iff_mem_nhds.mpr hCnhds
  have hxBall : f x ∈ Metric.ball (f x) (delta / 8) :=
    Metric.mem_ball_self (by positivity)
  refine ⟨{
    set := W
    isOpen := isOpen_interior.inter (Metric.isOpen_ball.preimage hf)
    mem_set := ⟨hxInterior, hxBall⟩
    scale := delta
    scale_pos := hdelta
    scale_le_one := min_le_right _ _
    scale_le := ?_
    dist_le_quarter := ?_ }⟩
  · intro y hy
    exact (min_le_left eps 1).trans (heps_le y (interior_subset hy.1))
  · intro y hy z hz
    have hyx : dist (f y) (f x) < delta / 8 := Metric.mem_ball.mp hy.2
    have hxz : dist (f x) (f z) < delta / 8 := by
      simpa only [dist_comm] using Metric.mem_ball.mp hz.2
    apply le_of_lt
    calc
      dist (f y) (f z) ≤ dist (f y) (f x) + dist (f x) (f z) :=
        dist_triangle _ _ _
      _ < delta / 8 + delta / 8 := add_lt_add hyx hxz
      _ = delta / 4 := by ring

/-- A chosen controlled neighborhood at every point. -/
noncomputable def controlledNeighborhood {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {f : X → Plane} (hf : Continuous f)
    {phi : X → ℝ} (hphi : StronglyPositiveOn Set.univ phi) (x : X) :
    ControlledNeighborhood f phi x :=
  Classical.choice (exists_controlledNeighborhood hf hphi x)

/-- The part of a mesh tolerance reserved for staying inside an open target region.  When the
region is all of the plane, the constant bound `1` is used instead. -/
noncomputable def regionMeshControl {X : Type*} (V : Set Plane)
    (f : X → Plane) (x : X) : ℝ := by
  classical
  exact if hcomp : Vᶜ.Nonempty then min 1 (frontierDistance V (f x) / 4) else 1

theorem regionMeshControl_le_one {X : Type*} (V : Set Plane)
    (f : X → Plane) (x : X) : regionMeshControl V f x ≤ 1 := by
  by_cases hcomp : Vᶜ.Nonempty
  · simp [regionMeshControl, hcomp]
  · simp [regionMeshControl, hcomp]

theorem regionMeshControl_le_frontier {X : Type*} {V : Set Plane}
    (hcomp : Vᶜ.Nonempty) (f : X → Plane) (x : X) :
    regionMeshControl V f x ≤ frontierDistance V (f x) / 4 := by
  simp [regionMeshControl, hcomp]

/-- The target-region mesh control is strongly positive along any continuous map landing in
that region. -/
theorem stronglyPositiveOn_regionMeshControl {X : Type*} [TopologicalSpace X]
    {V : Set Plane} (hV : IsOpen V) {f : X → Plane} (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) :
    StronglyPositiveOn Set.univ (regionMeshControl V f) := by
  intro C hC _hCU
  by_cases hcomp : Vᶜ.Nonempty
  · have hImageCompact : IsCompact (f '' C) := hC.image hf
    have hImageSubset : f '' C ⊆ V := by
      rintro _ ⟨x, -, rfl⟩
      exact hmem x
    obtain ⟨eps, heps, hepsLe⟩ :=
      stronglyPositiveOn_frontierDistance hV hcomp (f '' C)
        hImageCompact hImageSubset
    let delta := min 1 (eps / 4)
    have hdelta : 0 < delta := lt_min zero_lt_one (div_pos heps (by norm_num))
    refine ⟨delta, hdelta, ?_⟩
    intro x hx
    rw [regionMeshControl]
    simp only [hcomp, ↓reduceDIte]
    dsimp only [delta]
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_right (hepsLe (f x) ⟨x, hx, rfl⟩) (by norm_num)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _hx
    simp [regionMeshControl, hcomp]

/-- Combine a requested approximation tolerance with the target-region mesh control. -/
noncomputable def regionSafeControl {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) : ℝ :=
  min (phi x) (regionMeshControl V f x)

theorem regionSafeControl_le_left {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ phi x := min_le_left _ _

theorem regionSafeControl_le_one {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ 1 :=
  (min_le_right _ _).trans (regionMeshControl_le_one V f x)

theorem regionSafeControl_le_frontier {X : Type*} {V : Set Plane}
    (hcomp : Vᶜ.Nonempty) (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ frontierDistance V (f x) / 4 :=
  (min_le_right _ _).trans (regionMeshControl_le_frontier hcomp f x)

/-- A minimum of two strongly-positive controls is strongly positive. -/
theorem StronglyPositiveOn.min_control {X : Type*} [TopologicalSpace X]
    {U : Set X} {phi psi : X → ℝ}
    (hphi : StronglyPositiveOn U phi) (hpsi : StronglyPositiveOn U psi) :
    StronglyPositiveOn U (fun x ↦ min (phi x) (psi x)) := by
  intro C hC hCU
  obtain ⟨eps, heps, hepsLe⟩ := hphi C hC hCU
  obtain ⟨delta, hdelta, hdeltaLe⟩ := hpsi C hC hCU
  refine ⟨min eps delta, lt_min heps hdelta, ?_⟩
  intro x hx
  exact min_le_min (hepsLe x hx) (hdeltaLe x hx)

theorem stronglyPositiveOn_regionSafeControl {X : Type*} [TopologicalSpace X]
    {V : Set Plane} (hV : IsOpen V) {f : X → Plane} (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) {phi : X → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) :
    StronglyPositiveOn Set.univ (regionSafeControl V f phi) :=
  StronglyPositiveOn.min_control hphi
    (stronglyPositiveOn_regionMeshControl hV hf hmem)

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- The ambient open cover obtained from controlled neighborhoods in the open subspace `U`. -/
noncomputable def controlledAdaptiveOpenCover (hU : IsOpen U)
    (f : U → Plane) (hf : Continuous f) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : K.AdaptiveOpenCover U := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let N : ∀ x : U, ControlledNeighborhood f phi x :=
    fun x ↦ controlledNeighborhood hf hphi x
  exact {
    Index := U
    set := fun x ↦ Subtype.val '' (N x).set
    isOpen := fun x ↦ hU.isOpenEmbedding_subtypeVal.isOpenMap _ (N x).isOpen
    subset := by
      rintro x _ ⟨y, -, rfl⟩
      exact y.2
    covers := by
      intro p hp
      let x : U := ⟨p, hp⟩
      exact ⟨x, ⟨x, (N x).mem_set, rfl⟩⟩ }

namespace ControlledAdaptiveOpenCover

variable (hU : IsOpen U) (f : U → Plane) (hf : Continuous f)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable def N (x : U) : ControlledNeighborhood f phi x := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact controlledNeighborhood hf hphi x

/-- Every selected cover set retains its quantitative scale and image-diameter bounds. -/
theorem cover_set_control (x : U) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      (∀ y : U, y.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        eps ≤ phi y) ∧
      ∀ y z : U,
        y.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        z.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        dist (f y) (f z) ≤ eps / 4 := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let M := N K U hU f hf phi hphi x
  refine ⟨M.scale, M.scale_pos, M.scale_le_one, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzx : z = y := Subtype.ext hzy
    exact M.scale_le y (hzx ▸ hz)
  · intro y z hy hz
    obtain ⟨y', hy', hy'eq⟩ := hy
    obtain ⟨z', hz', hz'eq⟩ := hz
    have hyy' : y' = y := Subtype.ext hy'eq
    have hzz' : z' = z := Subtype.ext hz'eq
    exact M.dist_le_quarter y (hyy' ▸ hy') z (hzz' ▸ hz')

end ControlledAdaptiveOpenCover

/-- The adaptive locally finite triangle complex subordinate to the quantitative cover. -/
noncomputable abbrev controlledAdaptiveComplex (hU : IsOpen U)
    (f : U → Plane) (hf : Continuous f) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : LocallyFiniteTriangleComplex U :=
  AdaptiveOpenCover.locallyFiniteTriangleComplex K U
    (K.controlledAdaptiveOpenCover U hU f hf phi hphi) hU

/-- The controlled adaptive complex with its tolerance automatically reduced near the frontier
of an open target region. -/
noncomputable abbrev regionControlledAdaptiveComplex (hU : IsOpen U)
    (V : Set Plane) (hV : IsOpen V) (f : U → Plane) (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : LocallyFiniteTriangleComplex U :=
  K.controlledAdaptiveComplex U hU f hf (regionSafeControl V f phi)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hphi)

namespace ControlledAdaptiveComplex

variable (hU : IsOpen U) (f : U → Plane) (hf : Continuous f)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable abbrev L : LocallyFiniteTriangleComplex U :=
  K.controlledAdaptiveComplex U hU f hf phi hphi

/-- Each adaptive face inherits one quantitative scale from the cover member containing it. -/
theorem exists_face_scale (t : (L K U hU f hf phi hphi).Face) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      (∀ p ∈ (L K U hU f hf phi hphi).faceCarrier t, eps ≤ phi p) ∧
      ∀ p q : U,
        p ∈ (L K U hU f hf phi hphi).faceCarrier t →
        q ∈ (L K U hU f hf phi hphi).faceCarrier t →
        dist (f p) (f q) ≤ eps / 4 := by
  let C := K.controlledAdaptiveOpenCover U hU f hf phi hphi
  obtain ⟨i, hti⟩ := AdaptiveOpenCover.exists_cover_set_of_complex_face K U C hU t
  obtain ⟨eps, heps, hepsOne, hepsPhi, hepsDist⟩ :=
    ControlledAdaptiveOpenCover.cover_set_control K U hU f hf phi hphi i
  refine ⟨eps, heps, hepsOne, ?_, ?_⟩
  · intro p hp
    exact hepsPhi p (hti ⟨p, hp, rfl⟩)
  · intro p q hp hq
    exact hepsDist p q (hti ⟨p, hp, rfl⟩) (hti ⟨q, hq, rfl⟩)

/-- Subordination makes every edge image small enough for the canonical simultaneous
polygonal replacement to satisfy the original strongly-positive pointwise control. -/
theorem edgeImagesControlled
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    G.EdgeImagesControlled (fun p ↦ phi p.1) := by
  intro e p hp
  let t := (L K U hU f hf phi hphi).edgeFace e
  obtain ⟨eps, heps, -, hepsPhi, hepsDist⟩ :=
    exists_face_scale K U hU f hf phi hphi t
  have hdiam : Metric.diam (G.edgeImage e) ≤ eps / 4 := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro y hy z hz
    obtain ⟨py, hpy, rfl⟩ := hy
    obtain ⟨pz, hpz, rfl⟩ := hz
    have hpyFace : py.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
      apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
      exact hpy
    have hpzFace : pz.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
      apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
      exact hpz
    rw [hmap py, hmap pz]
    exact hepsDist py.1 pz.1 hpyFace hpzFace
  have hpFace : p.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
    apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
    have hp' : p ∈ Subtype.val ⁻¹'
        (L K U hU f hf phi hphi).edgeCarrier e := by
      rw [← LocallyFiniteTriangleComplex.PlaneGraphRealization.edgeInSupport_eq_preimage
        (K := L K U hU f hf phi hphi) e]
      exact hp
    exact hp'
  calc
    2 * Metric.diam (G.edgeImage e) ≤ 2 * (eps / 4) := by gcongr
    _ < eps := by linarith
    _ ≤ phi p.1 := hepsPhi p.1 hpFace

/-- The canonical replacement graph on the controlled adaptive mesh is a pointwise
`phi`-approximation of the original realization. -/
theorem isPhiApproximation_graphReplacementMap
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    ∀ p : LocallyFiniteTriangleComplex.PlaneGraphRealization.oneSkeletonInSupport
        (K := L K U hU f hf phi hphi),
      dist (G.graphReplacementMap p) (f p.1.1) < phi p.1.1 := by
  intro p
  rw [← hmap p.1]
  exact G.isPhiApproximation_graphReplacementMap
    (edgeImagesControlled K U hU f hf phi hphi G hmap) p

/-- Every edge belonging to a controlled adaptive face has image diameter bounded by that
face's selected scale. -/
theorem edgeImage_diam_le_face_scale
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (t : (L K U hU f hf phi hphi).Face)
    (e : (L K U hU f hf phi hphi).Edge)
    (het : e.1 ⊆ (L K U hU f hf phi hphi).faceVertices t)
    {eps : ℝ}
    (heps : 0 < eps)
    (hepsDist : ∀ p q : U,
      p ∈ (L K U hU f hf phi hphi).faceCarrier t →
      q ∈ (L K U hU f hf phi hphi).faceCarrier t →
      dist (f p) (f q) ≤ eps / 4) :
    Metric.diam (G.edgeImage e) ≤ eps / 4 := by
  apply Metric.diam_le_of_forall_dist_le
  · positivity
  · intro y hy z hz
    obtain ⟨py, hpy, rfl⟩ := hy
    obtain ⟨pz, hpz, rfl⟩ := hz
    have hpyCarrier : py.1 ∈ (L K U hU f hf phi hphi).edgeCarrier e := hpy
    have hpzCarrier : pz.1 ∈ (L K U hU f hf phi hphi).edgeCarrier e := hpz
    have hedgeFace : (L K U hU f hf phi hphi).edgeCarrier e ⊆
        (L K U hU f hf phi hphi).faceCarrier t := by
      rintro _ ⟨x, rfl⟩
      refine ⟨stdSimplex.map (fun v : {v // v ∈ e.1} ↦
        (⟨v.1, het v.2⟩ : {w // w ∈ (L K U hU f hf phi hphi).faceVertices t})) x, ?_⟩
      exact ((L K U hU f hf phi hphi).edgeMap_eq_faceMap e t het x).symm
    have hpyFace : py.1 ∈ (L K U hU f hf phi hphi).faceCarrier t :=
      hedgeFace hpyCarrier
    have hpzFace : pz.1 ∈ (L K U hU f hf phi hphi).faceCarrier t :=
      hedgeFace hpzCarrier
    rw [hmap py, hmap pz]
    exact hepsDist py.1 pz.1 hpyFace hpzFace

/-- The boundary error on one adaptive face is bounded by a positive scale which is at most
both the prescribed pointwise tolerance and one. -/
theorem exists_faceBoundary_control
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (t : (L K U hU f hf phi hphi).Face)
    (p : (L K U hU f hf phi hphi).support)
    (hp : p ∈ LocallyFiniteTriangleComplex.PlaneGraphRealization.faceInSupport t)
    (q : LocallyFiniteTriangleComplex.StandardFaceBoundary) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      dist
          (G.graphReplacementMap
            ((L K U hU f hf phi hphi).faceBoundaryLift t q))
          (G.map ((L K U hU f hf phi hphi).faceBoundaryLift t q).1) +
        dist (G.map ((L K U hU f hf phi hphi).faceBoundaryLift t q).1)
          (G.map p) ≤ eps ∧
      eps ≤ phi p.1 := by
  obtain ⟨eps, heps, hepsOne, hepsPhi, hepsDist⟩ :=
    exists_face_scale K U hU f hf phi hphi t
  let b := (L K U hU f hf phi hphi).faceBoundaryLift t q
  have hpCarrier : p.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
    obtain ⟨x, rfl⟩ := hp
    exact Set.mem_range_self x
  have hqCarrier : b.1.1 ∈
      (L K U hU f hf phi hphi).faceCarrier t := by
    change (L K U hU f hf phi hphi).faceMap t _ ∈
      Set.range ((L K U hU f hf phi hphi).faceMap t)
    exact Set.mem_range_self _
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  let e := (L K U hU f hf phi hphi).faceEdge t i
  have hqe : b.1 ∈
      LocallyFiniteTriangleComplex.PlaneGraphRealization.edgeInSupport e :=
    (L K U hU f hf phi hphi).faceBoundarySupportPoint_mem_edge t i q hi
  have hdiam : Metric.diam (G.edgeImage e) ≤ eps / 4 :=
    edgeImage_diam_le_face_scale K U hU f hf phi hphi G hmap t e
      ((L K U hU f hf phi hphi).faceEdge_subset_faceVertices t i) heps hepsDist
  have hgraph : dist
      (G.graphReplacementMap b) (G.map b.1) < eps / 2 := by
    rw [G.graphReplacementMap_eq e _ hqe]
    exact (G.replacementEdgeMap_dist_lt_two_mul_edgeImage_diam e
      ⟨b.1, hqe⟩).trans_le (by
        linarith)
  have hosc : dist
      (G.map b.1) (G.map p) ≤ eps / 4 := by
    rw [hmap, hmap]
    exact hepsDist _ _ hqCarrier hpCarrier
  have hlt :
      dist (G.graphReplacementMap b) (G.map b.1) +
          dist (G.map b.1) (G.map p) < eps := by
    calc
      dist
          (G.graphReplacementMap b) (G.map b.1) +
          dist (G.map b.1) (G.map p) < eps / 2 + eps / 4 :=
        add_lt_add_of_lt_of_le hgraph hosc
      _ < eps := by linarith
  exact ⟨eps, heps, hepsOne, hlt.le, hepsPhi p.1 hpCarrier⟩

/-- The adaptive mesh discharges the exact face-boundary estimate consumed by the cellwise
Schoenflies extension. -/
theorem faceBoundariesControlled
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    LocallyFiniteTriangleComplex.FaceBoundariesControlled G (fun p ↦ phi p.1) := by
  intro t p hp q
  obtain ⟨eps, -, -, hcontrol, hepsPhi⟩ :=
    exists_faceBoundary_control K U hU f hf phi hphi G hmap t p hp q
  exact hcontrol.trans hepsPhi

/-- If the original controlled realization lies in the model half-plane, so does its entire
simultaneous polygonal replacement graph. -/
theorem range_graphReplacementMap_subset_halfPlane
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (hfHalf : Set.range f ⊆ HalfPlaneSet) :
    Set.range G.graphReplacementMap ⊆ HalfPlaneSet := by
  rw [G.range_graphReplacementMap]
  intro y hy
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
  apply convexHull_min _ convex_halfPlaneSet
  · exact (G.replacementArc e).completeCarrier_subset_edgeConvexHull hye
  · rintro z ⟨p, -, rfl⟩
    rw [hmap p]
    exact hfHalf (Set.mem_range_self p.1)

end ControlledAdaptiveComplex

namespace RegionControlledAdaptiveComplex

variable (hU : IsOpen U) (V : Set Plane) (hV : IsOpen V)
  (f : U → Plane) (hf : Continuous f) (hmem : ∀ x, f x ∈ V)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable abbrev R : LocallyFiniteTriangleComplex U :=
  K.regionControlledAdaptiveComplex U hU V hV f hf hmem phi hphi

/-- The adaptive face-boundary estimate for the frontier-reduced tolerance. -/
theorem faceBoundariesControlled
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    LocallyFiniteTriangleComplex.FaceBoundariesControlled G
      (fun p ↦ regionSafeControl V f phi p.1) :=
  ControlledAdaptiveComplex.faceBoundariesControlled K U hU f hf
    (regionSafeControl V f phi)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hphi) G hmap

/-- The tolerance consumed by the filling is uniformly bounded and frontier-relative. -/
theorem uniformFrontierControl
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    G.UniformFrontierControl
      (fun p ↦ regionSafeControl V f phi p.1) := by
  constructor
  · intro p
    exact regionSafeControl_le_one V f phi p.1
  · intro hcomp p
    have hcompV : Vᶜ.Nonempty := by rwa [← hregion]
    calc
      regionSafeControl V f phi p.1 ≤ frontierDistance V (f p.1) / 4 :=
        regionSafeControl_le_frontier hcompV f phi p.1
      _ = Metric.infDist (G.map p) G.regionᶜ / 4 := by
        rw [hmap p, hregion]
        rfl

/-- The frontier-reduced adaptive fillings lie in the open target region. -/
theorem closedRegions_mem_region
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    ∀ t : (R K U hU V hV f hf hmem phi hphi).Face,
      ((R K U hU V hV f hf hmem phi hphi).facePolygonalCircle
        (G := G) t).closedRegion ⊆ G.region := by
  exact LocallyFiniteTriangleComplex.closedRegions_mem_region_of_uniformFrontierControl
    G (faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap)
      (uniformFrontierControl K U hU V hV f hf hmem phi hphi G hmap hregion)

/-- The frontier-reduced adaptive fillings form a locally finite family in the open target. -/
theorem locallyFinite_closedRegions
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    LocallyFinite fun t : (R K U hU V hV f hf hmem phi hphi).Face ↦
      {q : G.region | q.1 ∈
        ((R K U hU V hV f hf hmem phi hphi).facePolygonalCircle
          (G := G) t).closedRegion} := by
  exact LocallyFiniteTriangleComplex.locallyFinite_closedRegions_of_uniformFrontierControl
    G (faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap)
      (uniformFrontierControl K U hU V hV f hf hmem phi hphi G hmap hregion)

/-- The region-controlled adaptive complex carries distinct vertex triples on distinct faces:
the `hfaces` entry condition of `exists_polygonalReplacement` holds unconditionally. -/
theorem faceVertices_injective :
    Function.Injective (R K U hU V hV f hf hmem phi hphi).faceVertices :=
  AdaptiveOpenCover.faceVertices_injective K U
    (K.controlledAdaptiveOpenCover U hU f hf (regionSafeControl V f phi)
      (stronglyPositiveOn_regionSafeControl hV hf hmem hphi)) hU

/-- Complete locally finite cellwise replacement once the remaining side-separation condition
is supplied.  Region containment and local finiteness are now consequences, not hypotheses. -/
theorem exists_polygonalReplacement
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V)
    (hfaces : Function.Injective
      (R K U hU V hV f hf hmem phi hphi).faceVertices)
    (hsep : LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces G
      (fun p ↦ regionSafeControl V f phi p.1)) :
    ∃ H : (R K U hU V hV f hf hmem phi hphi).CellwiseCompatibility G,
      ∀ p : (R K U hU V hV f hf hmem phi hphi).support,
        dist
          ((R K U hU V hV f hf hmem phi hphi).polygonalReplacementHomeomorph H p).1.1
          (G.map p) ≤ phi p.1 := by
  have hcontrol := faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap
  obtain ⟨H, hH⟩ :=
    LocallyFiniteTriangleComplex.exists_controlled_polygonalReplacement G hfaces
      hcontrol hsep
      (closedRegions_mem_region K U hU V hV f hf hmem phi hphi G hmap hregion)
      (locallyFinite_closedRegions K U hU V hV f hf hmem phi hphi G hmap hregion)
  refine ⟨H, fun p ↦ (hH p).trans ?_⟩
  exact regionSafeControl_le_left V f phi p.1

/-- **Complete locally finite cellwise replacement with no residual side hypothesis.**  The
separation entry of `exists_polygonalReplacement` is discharged by the facewise comparison
map after shrinking the arc approximation controls; the shrunken realization keeps the map,
the region, and the frontier-reduced tolerance, so all adaptive control theorems reapply. -/
theorem exists_polygonalReplacement_of_comparison
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    ∃ (vc : (R K U hU V hV f hf hmem phi hphi).Vertex → ℝ)
      (hvc : ∀ v, 0 < vc v)
      (ec : (R K U hU V hV f hf hmem phi hphi).Edge → ℝ)
      (hec : ∀ e, 0 < ec e)
      (H : (R K U hU V hV f hf hmem phi hphi).CellwiseCompatibility
        (G.withApproximationControls vc hvc ec hec)),
      ∀ p : (R K U hU V hV f hf hmem phi hphi).support,
        dist
          ((R K U hU V hV f hf hmem phi hphi).polygonalReplacementHomeomorph H p).1.1
          (G.map p) ≤ phi p.1 := by
  obtain ⟨vc, hvc, ec, hec, hpack⟩ :=
    LocallyFiniteTriangleComplex.exists_controls_cellwiseCompatibility G
      (faceVertices_injective K U hU V hV f hf hmem phi hphi)
  set G' := G.withApproximationControls vc hvc ec hec with hG'
  have hmap' : ∀ p, G'.map p = f p.1 := hmap
  have hregion' : G'.region = V := hregion
  obtain ⟨H⟩ := hpack
    (closedRegions_mem_region K U hU V hV f hf hmem phi hphi G' hmap' hregion')
    (locallyFinite_closedRegions K U hU V hV f hf hmem phi hphi G' hmap' hregion')
  refine ⟨vc, hvc, ec, hec, H, ?_⟩
  intro p
  have hcontrol :=
    faceBoundariesControlled K U hU V hV f hf hmem phi hphi G' hmap'
  have hdist :=
    LocallyFiniteTriangleComplex.polygonalReplacementMap_dist_le H hcontrol p
  have hmapeq : G'.map p = G.map p := rfl
  rw [hmapeq] at hdist
  exact hdist.trans (regionSafeControl_le_left V f phi p.1)

end RegionControlledAdaptiveComplex

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification16_block_05
/- END ClassificationOfSurfaces.Moise.AdaptiveControlledApproximation -/
