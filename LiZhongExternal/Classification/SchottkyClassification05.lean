/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification05: pinned classification sources (upstream e3c7230f); see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification04
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Interval.Set.Infinite
import LiZhongExternal.Classification.SchottkyClassification01
import LiZhongExternal.Classification.SchottkyClassification02
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/- BEGIN ClassificationOfSurfaces.Moise.FreeTriangle | 2a0eb938f16ed1c152ab95120b7b6069317b0124c77bea64cb9c168e1910e132 -/
noncomputable section

section schottkyclassification05_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Free triangles in finite planar meshes

This file formalizes Moise Chapter 3, Theorem 3 in the form needed by the polygonal
Schoenflies induction.  A finite planar triangle mesh with infinite frontier has an edge incident
to exactly one triangle, hence a free triangle that can be removed by a supported ambient move.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace TriangleMesh

variable (M : TriangleMesh)

/-- The geometric carrier of a maximal triangle. -/
def triangleCarrier (t : Finset M.Vertex) : Set Plane :=
  convexHull ℝ (M.position '' (t : Set M.Vertex))

/-- The two-element faces occurring in maximal triangles. -/
def edges : Finset (Finset M.Vertex) :=
  M.triangles.biUnion fun t => t.powersetCard 2

/-- Maximal triangles incident to an edge. -/
def incidentTriangles (e : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  M.triangles.filter fun t => e ⊆ t

/-- A boundary edge is incident to exactly one maximal triangle. -/
def IsBoundaryEdge (e : Finset M.Vertex) : Prop :=
  e ∈ M.edges ∧ (M.incidentTriangles e).card = 1

/-- A weakly free triangle contains an incidence-one edge.  This is the boundary-edge precursor
used to find Moise's geometrically free triangles; by itself it does not exclude an additional
isolated boundary vertex. -/
def IsFreeTriangle (t : Finset M.Vertex) : Prop :=
  t ∈ M.triangles ∧ ∃ e, M.IsBoundaryEdge e ∧ e ⊆ t

/-- The three abstract edges of a maximal triangle. -/
def triangleEdges (t : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  t.powersetCard 2

/-- The boundary edges belonging to a maximal triangle. -/
noncomputable def boundaryEdges (t : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  by
    classical
    exact (M.triangleEdges t).filter M.IsBoundaryEdge

/-- All incidence-one edges of a finite triangle mesh. -/
noncomputable def allBoundaryEdges : Finset (Finset M.Vertex) := by
  classical
  exact M.edges.filter M.IsBoundaryEdge

theorem mem_allBoundaryEdges_iff {e : Finset M.Vertex} :
    e ∈ M.allBoundaryEdges ↔ M.IsBoundaryEdge e := by
  classical
  simp [allBoundaryEdges, IsBoundaryEdge]

/-- The finite union of the geometric carriers of all incidence-one mesh edges. -/
noncomputable def boundaryCarrier : Set Plane :=
  ⋃ e ∈ M.allBoundaryEdges, convexHull ℝ (M.position '' (e : Set M.Vertex))

theorem isCompact_boundaryCarrier : IsCompact M.boundaryCarrier := by
  classical
  exact M.allBoundaryEdges.finite_toSet.isCompact_biUnion fun e _ =>
    (e.finite_toSet.image M.position).isCompact_convexHull ℝ

theorem card_of_mem_edges {e : Finset M.Vertex} (he : e ∈ M.edges) : e.card = 2 := by
  obtain ⟨t, _, het⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_powersetCard.mp het).2

theorem mem_incidentTriangles_iff {e t : Finset M.Vertex} :
    t ∈ M.incidentTriangles e ↔ t ∈ M.triangles ∧ e ⊆ t := by
  simp [incidentTriangles]

theorem frontier_biUnion_subset (F : Finset (Finset M.Vertex)) :
    frontier (⋃ t ∈ F, M.triangleCarrier t) ⊆
      ⋃ t ∈ F, frontier (M.triangleCarrier t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert t F ht ih =>
      simpa [ht] using (frontier_union_subset (M.triangleCarrier t)
        (⋃ u ∈ F, M.triangleCarrier u)).trans
          (Set.union_subset_union Set.inter_subset_left (Set.inter_subset_right.trans ih))

/-- Index the vertices of a maximal triangle by `Fin 3`. -/
noncomputable def triangleIndexEquiv {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    Fin 3 ≃ t :=
  Fintype.equivOfCardEq (by simpa using (M.card_triangle t ht).symm)

/-- The vertices of a maximal planar triangle form an affine basis of the plane. -/
noncomputable def triangleAffineBasis {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    AffineBasis (Fin 3) ℝ Plane := by
  let e := M.triangleIndexEquiv ht
  let p : Fin 3 → Plane := fun i => M.position (e i)
  have hp : AffineIndependent ℝ p :=
    (M.affineIndependent_triangle t ht).comp_embedding e.toEmbedding
  refine ⟨p, hp, ?_⟩
  apply hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Plane]

theorem range_triangleAffineBasis {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    Set.range (M.triangleAffineBasis ht) = M.position '' (t : Set M.Vertex) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨M.triangleIndexEquiv ht i, (M.triangleIndexEquiv ht i).property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    let w : t := ⟨v, hv⟩
    refine ⟨(M.triangleIndexEquiv ht).symm w, ?_⟩
    change M.position (M.triangleIndexEquiv ht ((M.triangleIndexEquiv ht).symm w)) =
      M.position v
    rw [Equiv.apply_symm_apply]

/-- The edge opposite an indexed vertex of a maximal triangle. -/
noncomputable def triangleEdgeOpposite {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (i : Fin 3) : Finset M.Vertex :=
  t.erase (M.triangleIndexEquiv ht i)

theorem triangleEdgeOpposite_card {t : Finset M.Vertex} (ht : t ∈ M.triangles) (i : Fin 3) :
    (M.triangleEdgeOpposite ht i).card = 2 := by
  rw [triangleEdgeOpposite, Finset.card_erase_of_mem (M.triangleIndexEquiv ht i).property,
    M.card_triangle t ht]

theorem triangleEdgeOpposite_subset {t : Finset M.Vertex} (ht : t ∈ M.triangles) (i : Fin 3) :
    M.triangleEdgeOpposite ht i ⊆ t :=
  Finset.erase_subset _ _

theorem image_compl_eq_triangleEdgeOpposite {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (i : Fin 3) :
    M.triangleAffineBasis ht '' ({i}ᶜ : Set (Fin 3)) =
      M.position '' (M.triangleEdgeOpposite ht i : Set M.Vertex) := by
  ext p
  constructor
  · rintro ⟨j, hji, rfl⟩
    refine ⟨M.triangleIndexEquiv ht j, ?_, rfl⟩
    exact Finset.mem_erase.mpr ⟨by simpa using hji, (M.triangleIndexEquiv ht j).property⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' := Finset.mem_erase.mp hv
    let w : t := ⟨v, hv'.2⟩
    refine ⟨(M.triangleIndexEquiv ht).symm w, ?_, ?_⟩
    · intro heq
      apply hv'.1
      have h := congrArg (fun j => ((M.triangleIndexEquiv ht j : t) : M.Vertex)) heq
      simpa [w] using h
    · change M.position (M.triangleIndexEquiv ht ((M.triangleIndexEquiv ht).symm w)) =
        M.position v
      rw [Equiv.apply_symm_apply]

/-- A nonvertex point on the frontier of a maximal triangle lies in one of its edges. -/
theorem exists_edge_of_mem_frontier_triangle {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    {p : Plane} (hp : p ∈ frontier (M.triangleCarrier t)) :
    ∃ e : Finset M.Vertex, e.card = 2 ∧ e ⊆ t ∧
      p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  let b := M.triangleAffineBasis ht
  have hrange := M.range_triangleAffineBasis ht
  have hclosed : IsClosed (M.triangleCarrier t) :=
    (t.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hpCarrier : p ∈ M.triangleCarrier t := hclosed.frontier_subset hp
  have hpNotInterior : p ∉ interior (M.triangleCarrier t) :=
    (mem_frontier_iff_notMem_interior hpCarrier).mp hp
  have hpHull : p ∈ convexHull ℝ (Set.range b) := by
    simpa only [b, hrange, triangleCarrier] using hpCarrier
  have hnonneg : ∀ i, 0 ≤ b.coord i p := by
    rw [b.convexHull_eq_nonneg_coord] at hpHull
    exact hpHull
  have hnotpos : ¬∀ i, 0 < b.coord i p := by
    intro hpos
    apply hpNotInterior
    rw [triangleCarrier, ← hrange, b.interior_convexHull]
    exact hpos
  push Not at hnotpos
  obtain ⟨i, hi⟩ := hnotpos
  have hzero : b.coord i p = 0 := le_antisymm hi (hnonneg i)
  let s : Finset (Fin 3) := Finset.univ.erase i
  have hsum : ∑ j ∈ s, b.coord j p = 1 := by
    have htotal := b.sum_coord_apply_eq_one p
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hzero, add_zero] at htotal
    exact htotal
  have hcenter : s.centerMass (fun j => b.coord j p) b = p := by
    rw [s.centerMass_eq_of_sum_1 _ hsum]
    calc
      (∑ j ∈ s, b.coord j p • b j) = ∑ j, b.coord j p • b j := by
        dsimp [s]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hzero, zero_smul, add_zero]
      _ = p := b.linear_combination_coord_eq_self p
  have hpEdge : p ∈ convexHull ℝ (b '' ({i}ᶜ : Set (Fin 3))) := by
    rw [← hcenter]
    apply s.centerMass_mem_convexHull
    · intro j _
      exact hnonneg j
    · rw [hsum]
      norm_num
    · intro j hj
      exact ⟨j, by simpa [s] using (Finset.mem_erase.mp hj).1, rfl⟩
  refine ⟨M.triangleEdgeOpposite ht i, M.triangleEdgeOpposite_card ht i,
    M.triangleEdgeOpposite_subset ht i, ?_⟩
  rwa [M.image_compl_eq_triangleEdgeOpposite ht i] at hpEdge

theorem oppositeCoord_eq_zero_of_mem_oppositeEdge (T : M.Triangle) (k : Fin 3)
    {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane)) :
    M.oppositeCoord T k p = 0 := by
  have h := hp
  rw [← M.parent_inter_oppositeCoord_zero T k] at h
  exact h.2

/-- At a nonvertex point of an edge, the two barycentric coordinates along the edge are positive. -/
theorem oppositeCoord_pos_of_mem_oppositeEdge_of_not_vertex (T : M.Triangle) (k j : Fin 3)
    (hjk : j ≠ k) {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane))
    (hpv : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i)) :
    0 < M.oppositeCoord T j p := by
  have hpParent : p ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) := by
    rw [← M.parent_inter_oppositeCoord_zero T k] at hp
    exact hp.1
  have hnonneg := M.oppositeCoord_nonneg_of_mem_parent T j hpParent
  apply lt_of_le_of_ne hnonneg
  intro hzero'
  have hzeroj : M.oppositeCoord T j p = 0 := hzero'.symm
  have hzerok := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hp
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hsum : b.coord 0 p + b.coord 1 p + b.coord 2 p = 1 := by
    simpa only [Fin.sum_univ_three] using b.sum_coord_apply_eq_one p
  change b.coord j p = 0 at hzeroj
  change b.coord k p = 0 at hzerok
  have eq_vertex_of_two_zero (r : Fin 3)
      (hz : ∀ l : Fin 3, l ≠ r → M.oppositeCoord T l p = 0) :
      p = M.position (M.orderedVertex T r) := by
    have hcoordr : M.oppositeCoord T r p = 1 := by
      fin_cases r
      · have h1 := hz 1 (by decide)
        have h2 := hz 2 (by decide)
        change b.coord 1 p = 0 at h1
        change b.coord 2 p = 0 at h2
        change b.coord 0 p = 1
        linarith
      · have h0 := hz 0 (by decide)
        have h2 := hz 2 (by decide)
        change b.coord 0 p = 0 at h0
        change b.coord 2 p = 0 at h2
        change b.coord 1 p = 1
        linarith
      · have h0 := hz 0 (by decide)
        have h1 := hz 1 (by decide)
        change b.coord 0 p = 0 at h0
        change b.coord 1 p = 0 at h1
        change b.coord 2 p = 1
        linarith
    apply b.ext_elem
    intro l
    change M.oppositeCoord T l p =
      M.oppositeCoord T l (M.position (M.orderedVertex T r))
    rw [M.oppositeCoord_vertex]
    by_cases hl : l = r
    · subst l
      simpa using hcoordr
    · simpa [hl] using hz l hl
  have hpv' : ∃ r : Fin 3, p = M.position (M.orderedVertex T r) := by
    fin_cases k <;> fin_cases j
    · exact (hjk rfl).elim
    · refine ⟨2, eq_vertex_of_two_zero 2 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, Fin.reduceEq,
          not_false_eq_true, Fin.mk_one, Fin.reduceFinMk, not_true_eq_false] at hl ⊢ <;>
        assumption
    · refine ⟨1, eq_vertex_of_two_zero 1 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
          Fin.mk_one, not_true_eq_false, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨2, eq_vertex_of_two_zero 2 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, Fin.reduceEq,
          not_false_eq_true, Fin.mk_one, Fin.reduceFinMk, not_true_eq_false] at hl ⊢ <;>
        assumption
    · exact (hjk rfl).elim
    · refine ⟨0, eq_vertex_of_two_zero 0 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, not_true_eq_false, Fin.mk_one,
          one_ne_zero, not_false_eq_true, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨1, eq_vertex_of_two_zero 1 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
          Fin.mk_one, not_true_eq_false, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨0, eq_vertex_of_two_zero 0 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, not_true_eq_false, Fin.mk_one,
          one_ne_zero, not_false_eq_true, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · exact (hjk rfl).elim
  obtain ⟨r, hr⟩ := hpv'
  exact hpv r hr

theorem oppositeCoord_smul_eq_of_same_edge (T U : M.Triangle) (kT kU : Fin 3)
    (hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU) :
    (M.oppositeCoord T kT (M.position (M.orderedVertex U kU))) •
        M.oppositeCoord U kU = M.oppositeCoord T kT := by
  let bU := affineBasisOfTriangle (M.position ∘ M.orderedVertex U)
    (M.orderedVertex_affineIndependent U)
  apply AffineMap.ext_on bU.tot
  rintro x ⟨i, rfl⟩
  change M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) *
      M.oppositeCoord U kU (M.position (M.orderedVertex U i)) =
    M.oppositeCoord T kT (M.position (M.orderedVertex U i))
  by_cases hi : i = kU
  · subst i
    simp
  · have hmemU : M.position (M.orderedVertex U i) ∈ M.oppositeEdgePoints U kU := by
      unfold oppositeEdgePoints
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩
    have hmemT : M.position (M.orderedVertex U i) ∈ M.oppositeEdgePoints T kT := by
      rw [hedge]
      exact hmemU
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT
      (subset_convexHull ℝ _ hmemT)
    simp [M.oppositeCoord_vertex U kU i, Ne.symm hi, hz]

theorem oppositeCoord_ne_zero_of_same_edge (T U : M.Triangle) (kT kU : Fin 3)
    (hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU) :
    M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) ≠ 0 := by
  intro hc
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU hedge
  rw [hc, zero_smul] at hrel
  have h := congrArg (fun f : Plane →ᵃ[ℝ] ℝ =>
    f (M.position (M.orderedVertex T kT))) hrel
  simp at h

theorem interior_triangleCarrier (T : M.Triangle) :
    interior (M.triangleCarrier T.1) =
      {p | ∀ i : Fin 3, 0 < M.oppositeCoord T i p} := by
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hrange : Set.range b = M.position '' (T.1 : Set M.Vertex) := by
    change Set.range (M.position ∘ M.orderedVertex T) = _
    rw [Set.range_comp, M.range_orderedVertex T]
  rw [triangleCarrier, ← hrange, b.interior_convexHull]
  rfl

theorem interior_triangleCarrier_nonempty (T : M.Triangle) :
    (interior (M.triangleCarrier T.1)).Nonempty := by
  let b := M.triangleAffineBasis T.2
  have hspan : affineSpan ℝ (Set.range b) = ⊤ := b.tot
  have hnonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  simpa only [triangleCarrier, b, M.range_triangleAffineBasis T.2] using hnonempty

/-- A nondegenerate closed triangle is the closure of its Euclidean interior. -/
theorem closure_interior_triangleCarrier (T : M.Triangle) :
    closure (interior (M.triangleCarrier T.1)) = M.triangleCarrier T.1 := by
  unfold triangleCarrier
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (M.interior_triangleCarrier_nonempty T)]
  exact (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ |>.closure_eq

/-- The interior of a maximal triangle misses the carrier of every proper face of that
triangle.  The formulation with an arbitrary set of at most two vertices is convenient when
restricting a mesh along an existing edge. -/
theorem disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
    (T : M.Triangle) {s : Finset M.Vertex} (hs : s ⊆ T.1) (hcard : s.card ≤ 2) :
    Disjoint (interior (M.triangleCarrier T.1))
      (convexHull ℝ (M.position '' (s : Set M.Vertex))) := by
  have hproper : s ⊂ T.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
    intro h
    have := congrArg Finset.card h
    rw [M.card_triangle T.1 T.2] at this
    omega
  obtain ⟨v, hvT, hvNotS⟩ := Finset.exists_of_ssubset hproper
  obtain ⟨k, hkv⟩ : ∃ k : Fin 3, M.orderedVertex T k = v := by
    have hvRange : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact hvT
    simpa only [Set.mem_range] using hvRange
  have hsOpposite : M.position '' (s : Set M.Vertex) ⊆
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
    rintro p ⟨w, hw, rfl⟩
    obtain ⟨i, hiw⟩ : ∃ i : Fin 3, M.orderedVertex T i = w := by
      have hwRange : w ∈ Set.range (M.orderedVertex T) := by
        rw [M.range_orderedVertex T]
        exact hs hw
      simpa only [Set.mem_range] using hwRange
    change M.position w ∈ M.oppositeEdgePoints T k
    unfold oppositeEdgePoints
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩, ?_⟩
    · intro hik
      apply hvNotS
      rw [← hkv, ← hik, hiw]
      exact hw
    · simp only [Function.comp_apply, hiw]
  rw [Set.disjoint_left]
  intro p hpInterior hpFace
  have hpOpposite : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) :=
    convexHull_mono hsOpposite hpFace
  have hzero := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpOpposite
  have hpos : 0 < M.oppositeCoord T k p := by
    rw [M.interior_triangleCarrier T] at hpInterior
    exact hpInterior k
  linarith

/-- The interior of every maximal triangle misses every edge carrier of the mesh, whether or
not that edge belongs to the triangle. -/
theorem disjoint_interior_triangleCarrier_edgeCarrier (T : M.Triangle)
    {e : Finset M.Vertex} (he : e ∈ M.edges) :
    Disjoint (interior (M.triangleCarrier T.1))
      (convexHull ℝ (M.position '' (e : Set M.Vertex))) := by
  obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
  have heData := Finset.mem_powersetCard.mp heu
  let U : M.Triangle := ⟨u, hu⟩
  by_cases hTU : T.1 = U.1
  · apply M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
      T _ heData.2.le
    rw [hTU]
    exact heData.1
  have hInterCard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := by
      have hle : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ T.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [M.card_triangle T.1 T.2] at hle
      omega
    have hinterT : T.1 ∩ U.1 = T.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcard, M.card_triangle T.1 T.2])
    have hsubset : T.1 ⊆ U.1 := by
      rw [← hinterT]
      exact Finset.inter_subset_right
    have hEq : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsubset (by
      rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
    exact hTU hEq
  rw [Set.disjoint_left]
  intro p hpT hpEdge
  have hpU : p ∈ M.triangleCarrier U.1 :=
    convexHull_mono (Set.image_mono heData.1) hpEdge
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((T.1 ∩ U.1 : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hpT, hpU⟩
  exact Set.disjoint_left.mp
    (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two T
      Finset.inter_subset_left hInterCard) hpT hpInter

/-- The interior of one maximal triangle misses the full carrier of every distinct maximal
triangle. -/
theorem disjoint_interior_triangleCarrier_triangleCarrier {T U : M.Triangle}
    (hne : T.1 ≠ U.1) :
    Disjoint (interior (M.triangleCarrier T.1)) (M.triangleCarrier U.1) := by
  have hInterCard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := by
      have hle : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ T.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [M.card_triangle T.1 T.2] at hle
      omega
    have hsubset : T.1 ⊆ U.1 := by
      have hinterT : T.1 ∩ U.1 = T.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          rw [hcard, M.card_triangle T.1 T.2])
      rw [← hinterT]
      exact Finset.inter_subset_right
    have heq : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsubset (by
      rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
    exact hne heq
  rw [Set.disjoint_left]
  intro p hpT hpU
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((T.1 ∩ U.1 : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hpT, hpU⟩
  exact Set.disjoint_left.mp
    (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two T
      Finset.inter_subset_left hInterCard) hpT hpInter

/-- Maximal triangles in a face-to-face mesh have disjoint interiors. -/
theorem eq_of_interior_triangleCarrier_inter_nonempty (T U : M.Triangle)
    (hinterior : (interior (M.triangleCarrier T.1) ∩
      interior (M.triangleCarrier U.1)).Nonempty) : T.1 = U.1 := by
  let f : Finset M.Vertex := T.1 ∩ U.1
  have hfne : f.Nonempty := by
    by_contra hf
    have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    obtain ⟨p, hpT, hpU⟩ := hinterior
    have hpInter : p ∈ convexHull ℝ (M.position '' (f : Set M.Vertex)) := by
      rw [show f = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
      exact ⟨interior_subset hpT, interior_subset hpU⟩
    rw [hfempty] at hpInter
    simp at hpInter
  have hfSimplex : f ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨hfne, T.1, T.2, Finset.inter_subset_left⟩
  have hOpenSubset :
      interior (M.triangleCarrier T.1) ∩ interior (M.triangleCarrier U.1) ⊆
        convexHull ℝ (M.position '' (f : Set M.Vertex)) := by
    intro p hp
    rw [show f = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hp.1, interior_subset hp.2⟩
  have hfInterior :
      (interior (convexHull ℝ (M.position '' (f : Set M.Vertex)))).Nonempty := by
    obtain ⟨p, hp⟩ := hinterior
    exact ⟨p, interior_maximal hOpenSubset (isOpen_interior.inter isOpen_interior) hp⟩
  have hspan : affineSpan ℝ (M.position '' (f : Set M.Vertex)) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hfInterior
  let e : {v // v ∈ f} ↪ {v // v ∈ T.1} :=
    ⟨fun v => ⟨v, Finset.inter_subset_left v.2⟩,
      fun a b hab => by
        apply Subtype.ext
        exact congrArg (fun x : {v // v ∈ T.1} => (x : M.Vertex)) hab⟩
  have hAI : AffineIndependent ℝ (fun v : f => M.position v) :=
    (M.affineIndependent_triangle T.1 T.2).comp_embedding e
  have hrange : Set.range (fun v : f => M.position v) =
      M.position '' (f : Set M.Vertex) := by
    ext p
    simp
  have hfcard : f.card = 3 := by
    have hspan' : affineSpan ℝ (Set.range (fun v : f => M.position v)) = ⊤ := by
      rw [hrange]
      exact hspan
    have := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hspan'
    rw [Fintype.card_coe] at this
    have hfinrank : Module.finrank ℝ Plane = 2 := by simp [Plane]
    omega
  have hfT : f = T.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
    rw [hfcard, M.card_triangle T.1 T.2])
  have hfU : f = U.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
    rw [hfcard, M.card_triangle U.1 U.2])
  exact hfT.symm.trans hfU

theorem disjoint_interior_triangleCarrier {T U : M.Triangle} (hne : T.1 ≠ U.1) :
    Disjoint (interior (M.triangleCarrier T.1))
      (interior (M.triangleCarrier U.1)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact Set.not_nonempty_iff_eq_empty.mp fun h =>
    hne (M.eq_of_interior_triangleCarrier_inter_nonempty T U h)

/-- Deleting a maximal triangle leaves precisely the closure of the part of the old support
outside that triangle.  This is the face-to-face form of the elementary observation used in
Moise's free-triangle removal: points on a surviving triangle are limits of points in its
interior, and the interior of a different maximal triangle misses the deleted carrier. -/
theorem eraseTriangle_support_eq_closure_diff_triangleCarrier (T : M.Triangle) :
    (M.eraseTriangle T.1).toPlaneComplex.support =
      closure (M.toPlaneComplex.support \ M.triangleCarrier T.1) := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [TriangleMesh.toPlaneComplex_support] at hp
    simp only [TriangleMesh.eraseTriangle_triangles, Set.mem_iUnion] at hp
    obtain ⟨u, hu, hpU⟩ := hp
    have huData := Finset.mem_erase.mp hu
    let U : M.Triangle := ⟨u, huData.2⟩
    change p ∈ M.triangleCarrier U.1 at hpU
    rw [← M.closure_interior_triangleCarrier U] at hpU
    apply closure_mono (s := interior (M.triangleCarrier U.1)) ?_ hpU
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [M.toPlaneComplex_support]
      exact Set.mem_iUnion_of_mem U.1 (Set.mem_iUnion_of_mem U.2 (interior_subset hq))
    · intro hqT
      have hinterCard : (U.1 ∩ T.1 : Finset M.Vertex).card ≤ 2 := by
        have hle := Finset.card_le_card
          (Finset.inter_subset_left : U.1 ∩ T.1 ⊆ U.1)
        rw [M.card_triangle U.1 U.2] at hle
        by_contra hcard
        have hcardEq : (U.1 ∩ T.1 : Finset M.Vertex).card = 3 := by omega
        have hinterU : U.1 ∩ T.1 = U.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
            rw [hcardEq, M.card_triangle U.1 U.2])
        have hsub : U.1 ⊆ T.1 := hinterU ▸ Finset.inter_subset_right
        have hUT : U.1 = T.1 := Finset.eq_of_subset_of_card_le hsub (by
          rw [M.card_triangle U.1 U.2, M.card_triangle T.1 T.2])
        exact huData.1 hUT
      have hqInter : q ∈ convexHull ℝ
          (M.position '' ((U.1 ∩ T.1 : Finset M.Vertex) : Set M.Vertex)) := by
        rw [← M.triangle_inter U.1 U.2 T.1 T.2]
        exact ⟨interior_subset hq, hqT⟩
      exact Set.disjoint_left.mp
        (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two U
          Finset.inter_subset_left hinterCard) hq hqInter
  · apply closure_minimal
    · intro p hp
      rw [M.toPlaneComplex_support] at hp
      rw [TriangleMesh.toPlaneComplex_support]
      simp only [Set.mem_sdiff, Set.mem_iUnion,
        TriangleMesh.eraseTriangle_triangles] at hp ⊢
      obtain ⟨u, hu, hpU⟩ := hp.1
      by_cases huT : u = T.1
      · exact False.elim (hp.2 (huT ▸ hpU))
      · exact ⟨u, Finset.mem_erase.mpr ⟨huT, hu⟩, hpU⟩
    · exact (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed

/-- The remaining support cannot contain an interior point of the deleted triangle. -/
theorem disjoint_eraseTriangle_support_interior_triangleCarrier (T : M.Triangle) :
    Disjoint (M.eraseTriangle T.1).toPlaneComplex.support
      (interior (M.triangleCarrier T.1)) := by
  rw [M.eraseTriangle_support_eq_closure_diff_triangleCarrier T, Set.disjoint_left]
  intro p hpClosure hpInterior
  have hpClosureCompl : p ∈ closure (M.triangleCarrier T.1)ᶜ :=
    closure_mono (by
      intro q hq
      exact hq.2) hpClosure
  rw [closure_compl] at hpClosureCompl
  exact hpClosureCompl hpInterior

/-- The frontier after deleting a maximal triangle consists of the old frontier away from the
triangle together with the exact attachment of the surviving support to that triangle. -/
theorem frontier_eraseTriangle_support (T : M.Triangle) :
    frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        ((M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1) := by
  let A := M.toPlaneComplex.support
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  let K := M.triangleCarrier T.1
  have hAclosed : IsClosed A := M.toPlaneComplex.isCompact_support.isClosed
  have hBclosed : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  have hKclosed : IsClosed K :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hBA : B ⊆ A := M.eraseTriangle_support_subset T.1
  have hAunion : A = B ∪ K := M.support_eq_eraseTriangle_union_triangleCarrier T.2
  have hBdisjoint : Disjoint B (interior K) :=
    M.disjoint_eraseTriangle_support_interior_triangleCarrier T
  ext p
  constructor
  · intro hp
    have hpData : p ∈ B ∧ p ∉ interior B := by
      rw [hBclosed.frontier_eq] at hp
      exact hp
    by_cases hpK : p ∈ K
    · exact Or.inr ⟨hpData.1, hpK⟩
    · left
      refine ⟨?_, hpK⟩
      rw [hAclosed.frontier_eq]
      refine ⟨hBA hpData.1, ?_⟩
      intro hpIntA
      apply hpData.2
      apply interior_maximal (t := interior A ∩ Kᶜ)
      · intro q hq
        have hqA : q ∈ A := interior_subset hq.1
        rw [hAunion] at hqA
        exact hqA.resolve_right hq.2
      · exact isOpen_interior.inter hKclosed.isOpen_compl
      · exact ⟨hpIntA, hpK⟩
  · rintro (hpOld | hpAttach)
    · rw [hBclosed.frontier_eq]
      refine ⟨?_, ?_⟩
      · have hpA : p ∈ A := by
          rw [hAclosed.frontier_eq] at hpOld
          exact hpOld.1.1
        rw [hAunion] at hpA
        exact hpA.resolve_right hpOld.2
      · intro hpIntB
        have hpIntA : p ∈ interior A := interior_mono hBA hpIntB
        have hpNotIntA : p ∉ interior A := by
          rw [hAclosed.frontier_eq] at hpOld
          exact hpOld.1.2
        exact hpNotIntA hpIntA
    · rw [hBclosed.frontier_eq]
      refine ⟨hpAttach.1, ?_⟩
      intro hpIntB
      have hpClosureIntK : p ∈ closure (interior K) := by
        rw [M.closure_interior_triangleCarrier T]
        exact hpAttach.2
      have hpClosureMeet : p ∈ closure (interior B ∩ interior K) :=
        isOpen_interior.inter_closure ⟨hpIntB, hpClosureIntK⟩
      obtain ⟨q, hqB, hqK⟩ := Set.Nonempty.of_closure ⟨p, hpClosureMeet⟩
      exact Set.disjoint_left.mp hBdisjoint (interior_subset hqB) hqK

theorem triangleCarrier_eq_nonnegCoords (T : M.Triangle) :
    M.triangleCarrier T.1 = {p | ∀ i : Fin 3, 0 ≤ M.oppositeCoord T i p} := by
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hrange : Set.range b = M.position '' (T.1 : Set M.Vertex) := by
    change Set.range (M.position ∘ M.orderedVertex T) = _
    rw [Set.range_comp, M.range_orderedVertex T]
  rw [triangleCarrier, ← hrange, b.convexHull_eq_nonneg_coord]
  rfl

/-- A neighborhood of a relative interior point of an edge, retaining positivity of all
barycentric coordinates tangent to that edge. -/
def nonOppositeCoordNeighborhood (T : M.Triangle) (k : Fin 3) : Set Plane :=
  {p | ∀ j : Fin 3, j ≠ k → 0 < M.oppositeCoord T j p}

theorem isOpen_nonOppositeCoordNeighborhood (T : M.Triangle) (k : Fin 3) :
    IsOpen (M.nonOppositeCoordNeighborhood T k) := by
  have heq : M.nonOppositeCoordNeighborhood T k =
      ⋂ j : Fin 3, ⋂ (_ : j ≠ k), M.oppositeCoord T j ⁻¹' Set.Ioi 0 := by
    ext p
    simp [nonOppositeCoordNeighborhood]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_Ioi.preimage (M.oppositeCoord T j).continuous_of_finiteDimensional

theorem mem_nonOppositeCoordNeighborhood_of_mem_edge (T : M.Triangle) (k : Fin 3)
    {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane))
    (hpv : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i)) :
    p ∈ M.nonOppositeCoordNeighborhood T k := by
  intro j hj
  exact M.oppositeCoord_pos_of_mem_oppositeEdge_of_not_vertex T k j hj hp hpv

theorem triangle_inter_eq_edge {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2) (heT : e ⊆ T.1) (heU : e ⊆ U.1) :
    T.1 ∩ U.1 = e := by
  have heInter : e ⊆ (T.1 ∩ U.1 : Finset M.Vertex) := fun v hv =>
    Finset.mem_inter.mpr ⟨heT hv, heU hv⟩
  have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hge : 3 ≤ (T.1 ∩ U.1 : Finset M.Vertex).card := by omega
    have hleT : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 3 := by
      have h := Finset.card_le_card
        (Finset.inter_subset_left : (T.1 ∩ U.1 : Finset M.Vertex) ⊆ T.1)
      rwa [M.card_triangle T.1 T.2] at h
    have hcard3 : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := le_antisymm hleT hge
    have hEqT : (T.1 ∩ U.1 : Finset M.Vertex) = T.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcard3, M.card_triangle T.1 T.2])
    have hEqU : (T.1 ∩ U.1 : Finset M.Vertex) = U.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcard3, M.card_triangle U.1 U.2])
    exact hTU (hEqT.symm.trans hEqU)
  symm
  exact Finset.eq_of_subset_of_card_le heInter (by simpa [hecard] using hcard)

theorem oppositeCoord_negative_across_shared_edge {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2) (heT : e ⊆ T.1) (heU : e ⊆ U.1)
    (kT kU : Fin 3)
    (hedgeT : M.oppositeEdgePoints T kT = e.image M.position)
    (hedgeU : M.oppositeEdgePoints U kU = e.image M.position)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpvT : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i))
    (hpvU : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex U i)) :
    M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) < 0 := by
  let c := M.oppositeCoord T kT (M.position (M.orderedVertex U kU))
  have hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU :=
    hedgeT.trans hedgeU.symm
  have hcne : c ≠ 0 := M.oppositeCoord_ne_zero_of_same_edge T U kT kU hedge
  apply lt_of_le_of_ne (not_lt.mp ?_) hcne
  intro hcpos
  have hEdgeSetT : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeT, Finset.coe_image]
  have hEdgeSetU : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeU, Finset.coe_image]
  have hpEdgeU : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
    rw [hEdgeSetU]
    exact hpEdge
  have hpEdgeT : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
    rw [hEdgeSetT]
    exact hpEdge
  have hpOT : p ∈ M.nonOppositeCoordNeighborhood T kT :=
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge T kT hpEdgeT hpvT
  have hpOU : p ∈ M.nonOppositeCoordNeighborhood U kU :=
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge U kU hpEdgeU hpvU
  let q := M.position (M.orderedVertex U kU)
  have hpclosure : p ∈ closure (openSegment ℝ p q) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ p q)
  obtain ⟨z, hzOT, hzseg⟩ := (mem_closure_iff.mp hpclosure)
    (M.nonOppositeCoordNeighborhood T kT)
    (M.isOpen_nonOppositeCoordNeighborhood T kT) hpOT
  have hzU : z ∈ interior (M.triangleCarrier U.1) := by
    rw [M.interior_triangleCarrier U]
    rw [openSegment_eq_image_lineMap] at hzseg
    obtain ⟨θ, hθ, rfl⟩ := hzseg
    intro i
    rw [AffineMap.apply_lineMap]
    by_cases hi : i = kU
    · subst i
      rw [M.oppositeCoord_eq_zero_of_mem_oppositeEdge U kU hpEdgeU,
        M.oppositeCoord_vertex]
      simp [AffineMap.lineMap_apply_module, hθ.1]
    · have hpi := hpOU i hi
      rw [M.oppositeCoord_vertex]
      simp [hi, AffineMap.lineMap_apply_module]
      nlinarith [hpi, hθ.2]
  have hzT : z ∈ interior (M.triangleCarrier T.1) := by
    rw [M.interior_triangleCarrier T]
    intro i
    by_cases hi : i = kT
    · subst i
      rw [openSegment_eq_image_lineMap] at hzseg
      obtain ⟨θ, hθ, rfl⟩ := hzseg
      rw [AffineMap.apply_lineMap,
        M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT hpEdgeT]
      change 0 < AffineMap.lineMap 0 c θ
      simp [AffineMap.lineMap_apply_module]
      nlinarith [hcpos, hθ.1]
    · exact hzOT i hi
  have hinter := M.triangle_inter T.1 T.2 U.1 U.2
  rw [M.triangle_inter_eq_edge hTU hecard heT heU] at hinter
  have hzEdge : z ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [← hinter]
    exact ⟨interior_subset hzT, interior_subset hzU⟩
  have hzZero : M.oppositeCoord T kT z = 0 := by
    apply M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT
    rw [hEdgeSetT]
    exact hzEdge
  have hzPos : 0 < M.oppositeCoord T kT z := by
    rw [M.interior_triangleCarrier T] at hzT
    exact hzT kT
  linarith

/-- A genuine geometric edge contains infinitely many points. -/
theorem edgeCarrier_infinite {e : Finset M.Vertex} (hecard : e.card = 2) :
    (convexHull ℝ (M.position '' (e : Set M.Vertex))).Infinite := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  have hpne : M.position v ≠ M.position w := M.position_injective.ne hvw
  rw [show M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨v, by simp, rfl⟩
      · exact ⟨w, by simp, rfl⟩]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
    (AffineMap.lineMap_injective ℝ hpne).injOn

/-- Choose a relative-interior edge point which is not any vertex of the finite mesh. -/
theorem exists_nonvertex_mem_edgeCarrier {e : Finset M.Vertex} (hecard : e.card = 2) :
    ∃ p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)),
      ∀ v : M.Vertex, p ≠ M.position v := by
  let vertexPositions : Finset Plane := Finset.univ.image M.position
  obtain ⟨p, hp, hpnot⟩ := (M.edgeCarrier_infinite hecard).exists_notMem_finset
    vertexPositions
  refine ⟨p, hp, fun v hpv => ?_⟩
  apply hpnot
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hpv.symm⟩

/-- Two mesh edges containing the same nonvertex point are the same edge. -/
theorem edge_eq_of_nonvertex_mem_edgeCarriers {e f : Finset M.Vertex}
    (he : e ∈ M.edges) (hf : f ∈ M.edges) {p : Plane}
    (hpe : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpf : p ∈ convexHull ℝ (M.position '' (f : Set M.Vertex)))
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) : e = f := by
  have hecard := M.card_of_mem_edges he
  have hfcard := M.card_of_mem_edges hf
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    have hetData := Finset.mem_powersetCard.mp het
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hecard]; omega), t, ht, hetData.1⟩
  have hfFace : f ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
    have hftData := Finset.mem_powersetCard.mp hft
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hfcard]; omega), t, ht, hftData.1⟩
  have hface := M.toPlaneComplex.face_inter e heFace f hfFace
  change convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (f : Set M.Vertex)) =
        convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex))
    at hface
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface]
    exact ⟨hpe, hpf⟩
  have hinterCard : (e ∩ f).card = 2 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left : e ∩ f ⊆ e)
    rw [hecard] at hle
    by_contra hne
    have hsmall : (e ∩ f).card ≤ 1 := by omega
    obtain hempty | hnonempty := (e ∩ f).eq_empty_or_nonempty
    · rw [hempty] at hpInter
      simp at hpInter
    · obtain ⟨v, hv⟩ := hnonempty
      have hsingleton : e ∩ f = {v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hv, fun w hw => ?_⟩
        by_contra hwv
        have hvw : v ≠ w := Ne.symm hwv
        have hpairs : ({v, w} : Finset M.Vertex) ⊆ e ∩ f := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card hpairs
        simp [hvw] at this
        omega
      rw [hsingleton] at hpInter
      have hp : p = M.position v := by simpa using hpInter
      exact hpv v hp
  have heqE : e ∩ f = e :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hinterCard, hecard])
  have heqF : e ∩ f = f :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hinterCard, hfcard])
  exact heqE.symm.trans heqF

/-- Edge carriers in a face-to-face mesh meet in exactly the carrier of their common
vertices. -/
theorem edgeCarrier_inter_edgeCarrier {e f : Finset M.Vertex}
    (he : e ∈ M.edges) (hf : f ∈ M.edges) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
        convexHull ℝ (M.position '' (f : Set M.Vertex)) =
      convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    have hetData := Finset.mem_powersetCard.mp het
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hetData.2]; omega), t, ht, hetData.1⟩
  have hfFace : f ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
    have hftData := Finset.mem_powersetCard.mp hft
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hftData.2]; omega), t, ht, hftData.1⟩
  exact M.toPlaneComplex.face_inter e heFace f hfFace

/-- A used mesh vertex lying on an edge carrier is one of that edge's abstract endpoints. -/
theorem vertex_mem_edge_of_position_mem_edgeCarrier {v : M.Vertex} {e t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hvt : v ∈ t) (he : e ∈ M.edges)
    (hv : M.position v ∈ convexHull ℝ (M.position '' (e : Set M.Vertex))) : v ∈ e := by
  have hvFace : {v} ∈ M.toPlaneComplex.simplexes := by
    change ({v} : Finset M.Vertex) ∈ M.faces
    exact M.mem_faces_iff.mpr ⟨by simp, t, ht, by simpa using hvt⟩
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
    have heuData := Finset.mem_powersetCard.mp heu
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [heuData.2]; omega), u, hu, heuData.1⟩
  have hface := M.toPlaneComplex.face_inter {v} hvFace e heFace
  change convexHull ℝ (M.position '' (({v} : Finset M.Vertex) : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (e : Set M.Vertex)) =
        convexHull ℝ
          (M.position '' ((({v} : Finset M.Vertex) ∩ e : Finset M.Vertex) : Set M.Vertex))
    at hface
  by_contra hve
  have hinter : ({v} : Finset M.Vertex) ∩ e = ∅ := by
    simp [hve]
  have hp : M.position v ∈
      convexHull ℝ (M.position '' ((({v} : Finset M.Vertex) ∩ e : Finset M.Vertex) :
        Set M.Vertex)) := by
    rw [← hface]
    exact ⟨by simp, hv⟩
  rw [hinter] at hp
  simp at hp

/-- In a face-to-face planar mesh, once one incident triangle is fixed there is at most one
other triangle incident to the same edge. -/
theorem incidentTriangle_eq_of_ne {e t u v : Finset M.Vertex} (hecard : e.card = 2)
    (ht : t ∈ M.incidentTriangles e) (hu : u ∈ M.incidentTriangles e)
    (hv : v ∈ M.incidentTriangles e) (hut : u ≠ t) (hvt : v ≠ t) : u = v := by
  by_contra huv
  have htData := M.mem_incidentTriangles_iff.mp ht
  have huData := M.mem_incidentTriangles_iff.mp hu
  have hvData := M.mem_incidentTriangles_iff.mp hv
  let T : M.Triangle := ⟨t, htData.1⟩
  let U : M.Triangle := ⟨u, huData.1⟩
  let V : M.Triangle := ⟨v, hvData.1⟩
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T htData.2 hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U huData.2 hecard
  obtain ⟨kV, hedgeV⟩ := M.exists_oppositeEdgePoints_eq V hvData.2 hecard
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hecard
  have hcTU : M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge hut.symm hecard htData.2 huData.2
      kT kU hedgeT hedgeU hpEdge (fun i => hpv (M.orderedVertex T i))
        (fun i => hpv (M.orderedVertex U i))
  have hcTV : M.oppositeCoord T kT (M.position (M.orderedVertex V kV)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge hvt.symm hecard htData.2 hvData.2
      kT kV hedgeT hedgeV hpEdge (fun i => hpv (M.orderedVertex T i))
        (fun i => hpv (M.orderedVertex V i))
  have hcUV : M.oppositeCoord U kU (M.position (M.orderedVertex V kV)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge huv hecard huData.2 hvData.2
      kU kV hedgeU hedgeV hpEdge (fun i => hpv (M.orderedVertex U i))
        (fun i => hpv (M.orderedVertex V i))
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU
    (hedgeT.trans hedgeU.symm)
  have hrelV := congrArg (fun f : Plane →ᵃ[ℝ] ℝ =>
    f (M.position (M.orderedVertex V kV))) hrel
  change M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) *
      M.oppositeCoord U kU (M.position (M.orderedVertex V kV)) =
    M.oppositeCoord T kT (M.position (M.orderedVertex V kV)) at hrelV
  nlinarith

/-- Every geometric edge of a face-to-face planar mesh is incident to at most two triangles. -/
theorem card_incidentTriangles_le_two {e : Finset M.Vertex} (hecard : e.card = 2) :
    (M.incidentTriangles e).card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < (M.incidentTriangles e).card := by omega
  obtain ⟨t, u, v, ht, hu, hv, htu, htv, huv⟩ := Finset.two_lt_card_iff.mp hthree
  have huv' := M.incidentTriangle_eq_of_ne hecard ht hu hv htu.symm htv.symm
  exact huv huv'

/-- If a nonvertex point of an edge of `t` also belongs to `u`, then `u` contains the whole
edge.  This is the face-to-face property upgraded from geometry to incidence. -/
theorem edge_subset_of_nonvertex_mem_triangleCarrier {e t u : Finset M.Vertex} {p : Plane}
    (hecard : e.card = 2) (het : e ⊆ t) (ht : t ∈ M.triangles)
    (hu : u ∈ M.triangles)
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpU : p ∈ M.triangleCarrier u) (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    e ⊆ u := by
  have hpT : p ∈ M.triangleCarrier t :=
    convexHull_mono (Set.image_mono het) hpEdge
  have hinter := M.triangle_inter t ht u hu
  have hpInter : p ∈ convexHull ℝ (M.position '' ((t ∩ u : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hinter]
    exact ⟨hpT, hpU⟩
  let f : Finset M.Vertex := t ∩ u
  have hfne : f.Nonempty := by
    by_contra hf
    have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    rw [show (t ∩ u : Finset M.Vertex) = f by rfl, hfempty] at hpInter
    simp at hpInter
  have heSimplex : e ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by omega), t, ht, het⟩
  have hfSimplex : f ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨hfne, t, ht, by exact Finset.inter_subset_left⟩
  have hface := M.toPlaneComplex.face_inter e heSimplex f hfSimplex
  change convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (f : Set M.Vertex)) =
    convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) at hface
  have hpCommon : p ∈
      convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface]
    exact ⟨hpEdge, by simpa only [f] using hpInter⟩
  by_contra hsub
  have hcardCommon : (e ∩ f).card ≤ 1 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left : e ∩ f ⊆ e)
    rw [hecard] at hle
    by_contra hnot
    have hcardeq : (e ∩ f).card = 2 := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [hcardeq, hecard])
    apply hsub
    intro v hv
    have hvinter : v ∈ e ∩ f := by rw [heq]; exact hv
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hvinter).2).2
  obtain hempty | hnonempty := (e ∩ f).eq_empty_or_nonempty
  · rw [hempty] at hpCommon
    simp at hpCommon
  · obtain ⟨v, hv⟩ := hnonempty
    have hsingleton : e ∩ f = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv, fun w hw => ?_⟩
      have hcardPair : ({v, w} : Finset M.Vertex).card ≤ 1 :=
        (Finset.card_le_card (show ({v, w} : Finset M.Vertex) ⊆ e ∩ f by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)).trans hcardCommon
      by_contra hwv
      have hvw : v ≠ w := Ne.symm hwv
      have hcardTwo : ({v, w} : Finset M.Vertex).card = 2 := by simp [hvw]
      omega
    rw [hsingleton] at hpCommon
    have hpEq : p = M.position v := by
      simpa using hpCommon
    exact hpv v hpEq

/-- Every nonvertex point of an incidence-one edge lies on the support frontier. -/
theorem mem_frontier_of_mem_boundaryEdge {e : Finset M.Vertex} (he : M.IsBoundaryEdge e)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    p ∈ frontier M.toPlaneComplex.support := by
  classical
  obtain ⟨t, ht, hetPower⟩ := Finset.mem_biUnion.mp he.1
  have hetData := Finset.mem_powersetCard.mp hetPower
  have het : e ⊆ t := hetData.1
  have hecard : e.card = 2 := hetData.2
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  let A := M.triangleCarrier t
  let B := ⋃ u ∈ M.triangles.erase t, M.triangleCarrier u
  have hBcompact : IsCompact B := by
    exact (M.triangles.erase t).finite_toSet.isCompact_biUnion fun u _ =>
      (u.finite_toSet.image M.position).isCompact_convexHull ℝ
  have hpNotB : p ∉ B := by
    intro hpB
    simp only [B, Set.mem_iUnion] at hpB
    obtain ⟨u, huErase, hpU⟩ := hpB
    have huData := Finset.mem_erase.mp huErase
    have heu : e ⊆ u := M.edge_subset_of_nonvertex_mem_triangleCarrier hecard het ht
      huData.2 hpEdge hpU hpv
    have huinc : u ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨huData.2, heu⟩
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp he.2
    have htw : t = w := by
      rw [hw] at htinc
      simpa using htinc
    have huw : u = w := by
      rw [hw] at huinc
      simpa using huinc
    exact huData.1 (huw.trans htw.symm)
  have hsupport : M.toPlaneComplex.support = A ∪ B := by
    rw [M.toPlaneComplex_support]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, A, B]
    constructor
    · rintro ⟨u, hu, hxu⟩
      by_cases hut : u = t
      · left
        rwa [hut] at hxu
      · right
        exact ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩, hxu⟩
    · rintro (hxt | ⟨u, hu, hxu⟩)
      · exact ⟨t, ht, hxt⟩
      · exact ⟨u, (Finset.mem_erase.mp hu).2, hxu⟩
  let T : M.Triangle := ⟨t, ht⟩
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T het hecard
  have hpOpposite : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
    rw [hedge, Finset.coe_image]
    exact hpEdge
  have hpA : p ∈ A := convexHull_mono (Set.image_mono het) hpEdge
  have hpNotInteriorA : p ∉ interior A := by
    rw [M.interior_triangleCarrier T]
    intro hpos
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpOpposite
    linarith [hpos k]
  have hpFrontierA : p ∈ frontier A :=
    (mem_frontier_iff_notMem_interior hpA).mpr hpNotInteriorA
  have hpSupport : p ∈ M.toPlaneComplex.support := by
    rw [hsupport]
    exact Or.inl hpA
  have hpNotInteriorSupport : p ∉ interior M.toPlaneComplex.support := by
    intro hpInterior
    let O := interior M.toPlaneComplex.support ∩ Bᶜ
    have hOopen : IsOpen O := isOpen_interior.inter hBcompact.isClosed.isOpen_compl
    have hpO : p ∈ O := ⟨hpInterior, hpNotB⟩
    have hOsub : O ⊆ A := by
      intro x hx
      have hxsupport : x ∈ M.toPlaneComplex.support := interior_subset hx.1
      rw [hsupport] at hxsupport
      rcases hxsupport with hxA | hxB
      · exact hxA
      · exact False.elim (hx.2 hxB)
    have hpInteriorA : p ∈ interior A := interior_maximal hOsub hOopen hpO
    exact Set.disjoint_left.mp disjoint_interior_frontier hpInteriorA hpFrontierA
  rw [M.toPlaneComplex.isCompact_support.isClosed.frontier_eq]
  exact ⟨hpSupport, hpNotInteriorSupport⟩

/-- The whole carrier of an incidence-one edge lies in the support frontier, including endpoints. -/
theorem boundaryEdgeCarrier_subset_frontier {e : Finset M.Vertex} (he : M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      frontier M.toPlaneComplex.support := by
  classical
  have hecard := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  let a := M.position v
  let b := M.position w
  have hab : a ≠ b := M.position_injective.ne hvw
  have himage : M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) = {a, b} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [a, b]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨v, by simp, rfl⟩
      · exact ⟨w, by simp, rfl⟩
  rw [himage, convexHull_pair]
  let line : ℝ → Plane := AffineMap.lineMap a b
  let bad : Set ℝ := line ⁻¹' Set.range M.position
  have hbadFinite : bad.Finite := by
    apply Set.Finite.preimage (AffineMap.lineMap_injective ℝ hab).injOn
    exact Set.finite_range M.position
  have hdense : Dense badᶜ := hbadFinite.countable.dense_compl ℝ
  let good : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ badᶜ
  have hIooGood : Set.Ioo (0 : ℝ) 1 ⊆ closure good := by
    exact hdense.open_subset_closure_inter isOpen_Ioo
  have hgoodImage : line '' good ⊆ frontier M.toPlaneComplex.support := by
    rintro p ⟨c, hc, rfl⟩
    apply M.mem_frontier_of_mem_boundaryEdge he
    · rw [himage, convexHull_pair]
      exact lineMap_mem_segment ℝ a b ⟨hc.1.1.le, hc.1.2.le⟩
    · intro x hx
      apply hc.2
      exact ⟨x, hx.symm⟩
  intro p hp
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  have hcClosureIoo : c ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hc
  have hcClosureGood : c ∈ closure good := by
    have : c ∈ closure (closure good) := closure_mono hIooGood hcClosureIoo
    simpa using this
  have hlineContinuous : Continuous line := by
    exact AffineMap.lineMap_continuous
  have hmemClosureImage : line c ∈ closure (line '' good) :=
    image_closure_subset_closure_image hlineContinuous ⟨c, hcClosureGood, rfl⟩
  exact (closure_minimal hgoodImage isClosed_frontier) hmemClosureImage

theorem boundaryCarrier_subset_frontier :
    M.boundaryCarrier ⊆ frontier M.toPlaneComplex.support := by
  intro p hp
  simp only [boundaryCarrier, Set.mem_iUnion] at hp
  obtain ⟨e, he, hpe⟩ := hp
  exact M.boundaryEdgeCarrier_subset_frontier
    (M.mem_allBoundaryEdges_iff.mp he) hpe

theorem card_triangleEdges {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    (M.triangleEdges t).card = 3 := by
  simp [triangleEdges, M.card_triangle t ht]

theorem boundaryEdges_subset_triangleEdges (t : Finset M.Vertex) :
    M.boundaryEdges t ⊆ M.triangleEdges t := by
  classical
  intro e he
  exact (Finset.mem_filter.mp (show e ∈ (M.triangleEdges t).filter M.IsBoundaryEdge by
    simpa [boundaryEdges] using he)).1

theorem mem_boundaryEdges_iff {e t : Finset M.Vertex} :
    e ∈ M.boundaryEdges t ↔ e ⊆ t ∧ e.card = 2 ∧ M.IsBoundaryEdge e := by
  classical
  simp [boundaryEdges, triangleEdges, Finset.mem_powersetCard]
  tauto

theorem boundaryEdges_nonempty_of_isFreeTriangle {t : Finset M.Vertex}
    (ht : M.IsFreeTriangle t) : (M.boundaryEdges t).Nonempty := by
  obtain ⟨htM, e, he, het⟩ := ht
  exact ⟨e, M.mem_boundaryEdges_iff.mpr
    ⟨het, M.card_of_mem_edges he.1, he⟩⟩

/-- A non-boundary edge of a maximal triangle has exactly two incident triangles. -/
theorem card_incidentTriangles_eq_two_of_not_boundary {e t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hecard : e.card = 2) (het : e ⊆ t)
    (he : ¬M.IsBoundaryEdge e) : (M.incidentTriangles e).card = 2 := by
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  have hpos : 0 < (M.incidentTriangles e).card := Finset.card_pos.mpr ⟨t, htinc⟩
  have hle := M.card_incidentTriangles_le_two hecard
  have hne : (M.incidentTriangles e).card ≠ 1 := by
    intro hcard
    apply he
    refine ⟨?_, hcard⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨t, ht, Finset.mem_powersetCard.mpr ⟨het, hecard⟩⟩
  omega

/-- Two maximal triangles are edge-neighbors if they contain a common two-vertex face. -/
def AreEdgeNeighbors (t u : Finset M.Vertex) : Prop :=
  ∃ e : Finset M.Vertex, e.card = 2 ∧ e ⊆ t ∧ e ⊆ u

/-- A triangle with an edge-neighbor cannot have all three edges on the boundary. -/
theorem card_boundaryEdges_le_two_of_neighbor {t u : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hu : u ∈ M.triangles) (htu : t ≠ u)
    (hneigh : M.AreEdgeNeighbors t u) : (M.boundaryEdges t).card ≤ 2 := by
  by_contra hcard
  have hthree : (M.boundaryEdges t).card = 3 := by
    have hle := Finset.card_le_card (M.boundaryEdges_subset_triangleEdges t)
    rw [M.card_triangleEdges ht] at hle
    omega
  have hall : M.boundaryEdges t = M.triangleEdges t :=
    Finset.eq_of_subset_of_card_le (M.boundaryEdges_subset_triangleEdges t) (by
      rw [hthree, M.card_triangleEdges ht])
  obtain ⟨e, hecard, het, heu⟩ := hneigh
  have heBoundary : M.IsBoundaryEdge e := by
    have heTri : e ∈ M.triangleEdges t :=
      Finset.mem_powersetCard.mpr ⟨het, hecard⟩
    rw [← hall] at heTri
    exact (M.mem_boundaryEdges_iff.mp heTri).2.2
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  have huinc : u ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨hu, heu⟩
  have htwo : 2 ≤ (M.incidentTriangles e).card := by
    exact Finset.one_lt_card.mpr ⟨t, htinc, u, huinc, htu⟩
  rw [heBoundary.2] at htwo
  omega

/-- Two distinct face-to-face triangles fill a neighborhood of every nonvertex point of their
common edge. -/
theorem mem_interior_union_triangleCarrier_of_shared_edge {T U : M.Triangle}
    (hTU : T.1 ≠ U.1) {e : Finset M.Vertex} (hecard : e.card = 2)
    (heT : e ⊆ T.1) (heU : e ⊆ U.1) {p : Plane}
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpvT : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i))
    (hpvU : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex U i)) :
    p ∈ interior (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) := by
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T heT hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U heU hecard
  have hEdgeSetT : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeT, Finset.coe_image]
  have hEdgeSetU : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeU, Finset.coe_image]
  have hpEdgeT : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
    rw [hEdgeSetT]
    exact hpEdge
  have hpEdgeU : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
    rw [hEdgeSetU]
    exact hpEdge
  let c := M.oppositeCoord T kT (M.position (M.orderedVertex U kU))
  have hc : c < 0 := M.oppositeCoord_negative_across_shared_edge hTU hecard heT heU
    kT kU hedgeT hedgeU hpEdge hpvT hpvU
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU
    (hedgeT.trans hedgeU.symm)
  let O := M.nonOppositeCoordNeighborhood T kT ∩
    M.nonOppositeCoordNeighborhood U kU
  have hOpen : IsOpen O :=
    (M.isOpen_nonOppositeCoordNeighborhood T kT).inter
      (M.isOpen_nonOppositeCoordNeighborhood U kU)
  have hpO : p ∈ O := ⟨
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge T kT hpEdgeT hpvT,
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge U kU hpEdgeU hpvU⟩
  have hOsub : O ⊆ M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 := by
    intro x hx
    by_cases hfx : 0 ≤ M.oppositeCoord T kT x
    · left
      rw [M.triangleCarrier_eq_nonnegCoords T]
      intro i
      by_cases hi : i = kT
      · simpa [hi] using hfx
      · exact (hx.1 i hi).le
    · right
      rw [M.triangleCarrier_eq_nonnegCoords U]
      intro i
      by_cases hi : i = kU
      · subst i
        have hrelx := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) hrel
        change c * M.oppositeCoord U kU x = M.oppositeCoord T kT x at hrelx
        have hfx' : M.oppositeCoord T kT x < 0 := lt_of_not_ge hfx
        nlinarith
      · exact (hx.2 i hi).le
  exact interior_maximal hOsub hOpen hpO

theorem orderedVertex_ne_of_not_mem_edgeVertices (T : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex}
    (hedge : M.oppositeEdgePoints T k = e.image M.position)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpNotVertices : p ∉ M.position '' (e : Set M.Vertex)) :
    ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i) := by
  intro i hpi
  by_cases hi : i = k
  · subst i
    have hpEdge' : p ∈ convexHull ℝ
        ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
      rw [hedge, Finset.coe_image]
      exact hpEdge
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpEdge'
    rw [hpi, M.oppositeCoord_vertex] at hz
    simp at hz
  · apply hpNotVertices
    have hmemOpposite : M.position (M.orderedVertex T i) ∈
        M.oppositeEdgePoints T k := by
      unfold oppositeEdgePoints
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩
    rw [hedge] at hmemOpposite
    obtain ⟨v, hve, hv⟩ := Finset.mem_image.mp hmemOpposite
    exact ⟨v, hve, hv.trans hpi.symm⟩

/-- The shared-edge neighborhood theorem only needs the point to avoid the two endpoints of
the common edge; unrelated retained mesh vertices are irrelevant. -/
theorem mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
    {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2)
    (heT : e ⊆ T.1) (heU : e ⊆ U.1) {p : Plane}
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpNotVertices : p ∉ M.position '' (e : Set M.Vertex)) :
    p ∈ interior (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) := by
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T heT hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U heU hecard
  exact M.mem_interior_union_triangleCarrier_of_shared_edge hTU hecard heT heU hpEdge
    (M.orderedVertex_ne_of_not_mem_edgeVertices T kT hedgeT hpEdge hpNotVertices)
    (M.orderedVertex_ne_of_not_mem_edgeVertices U kU hedgeU hpEdge hpNotVertices)

/-- Every non-endpoint point of a non-boundary mesh edge is interior to the mesh support. -/
theorem edgeCarrier_diff_vertices_subset_interior_support
    {e t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (hecard : e.card = 2) (heT : e ⊆ t) (heNotBoundary : ¬M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) \
        (M.position '' (e : Set M.Vertex)) ⊆ interior M.toPlaneComplex.support := by
  intro p hp
  have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
    ht hecard heT heNotBoundary
  have htIncident : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, heT⟩
  have hother : ∃ u ∈ M.incidentTriangles e, u ≠ t := by
    by_contra h
    push Not at h
    have hsingleton : M.incidentTriangles e = {t} := by
      ext u
      constructor
      · exact fun hu => Finset.mem_singleton.mpr (h u hu)
      · intro hu
        rw [Finset.mem_singleton.mp hu]
        exact htIncident
    rw [hsingleton] at hcard
    simp at hcard
  obtain ⟨u, huIncident, hut⟩ := hother
  have huData := M.mem_incidentTriangles_iff.mp huIncident
  let T : M.Triangle := ⟨t, ht⟩
  let U : M.Triangle := ⟨u, huData.1⟩
  have hpInteriorUnion :=
    M.mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
      (T := T) (U := U) hut.symm hecard heT huData.2 hp.1 hp.2
  have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
      M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.union_subset
      (Set.subset_iUnion_of_subset T.1
        (Set.subset_iUnion_of_subset T.2 (by rfl)))
      (Set.subset_iUnion_of_subset U.1
        (Set.subset_iUnion_of_subset U.2 (by rfl)))
  exact interior_mono hUnionSubset hpInteriorUnion

/-- Every nonvertex point of the support frontier lies on an incidence-one mesh edge. -/
theorem exists_boundaryEdge_through_frontier_point {p : Plane}
    (hpFrontier : p ∈ frontier M.toPlaneComplex.support)
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    ∃ t ∈ M.triangles, ∃ e : Finset M.Vertex,
      M.IsBoundaryEdge e ∧ e ⊆ t ∧
        p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  classical
  have hpFrontierUnion : p ∈ frontier (⋃ t ∈ M.triangles, M.triangleCarrier t) := by
    rw [M.toPlaneComplex_support] at hpFrontier
    simpa only [triangleCarrier] using hpFrontier
  have hpTriangleFrontier := M.frontier_biUnion_subset M.triangles hpFrontierUnion
  simp only [Set.mem_iUnion] at hpTriangleFrontier
  obtain ⟨t, ht, hpT⟩ := hpTriangleFrontier
  obtain ⟨e, hecard, heT, hpEdge⟩ := M.exists_edge_of_mem_frontier_triangle ht hpT
  have heEdges : e ∈ M.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨t, ht, Finset.mem_powersetCard.mpr ⟨heT, hecard⟩⟩
  have htIncident : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, heT⟩
  have hIncidentCard : (M.incidentTriangles e).card = 1 := by
    by_contra hne
    have hother : ∃ u ∈ M.incidentTriangles e, u ≠ t := by
      by_contra h
      push Not at h
      have hsingleton : M.incidentTriangles e = {t} := by
        ext u
        constructor
        · intro hu
          exact Finset.mem_singleton.mpr (h u hu)
        · intro hu
          rw [Finset.mem_singleton.mp hu]
          exact htIncident
      apply hne
      rw [hsingleton]
      simp
    obtain ⟨u, huIncident, hut⟩ := hother
    have huData := M.mem_incidentTriangles_iff.mp huIncident
    let T : M.Triangle := ⟨t, ht⟩
    let U : M.Triangle := ⟨u, huData.1⟩
    have hpInteriorUnion : p ∈ interior
        (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) :=
      M.mem_interior_union_triangleCarrier_of_shared_edge
        (T := T) (U := U) hut.symm hecard heT huData.2 hpEdge
          (fun i => hpv (M.orderedVertex T i))
          (fun i => hpv (M.orderedVertex U i))
    have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
        M.toPlaneComplex.support := by
      change M.triangleCarrier t ∪ M.triangleCarrier u ⊆ M.toPlaneComplex.support
      rw [M.toPlaneComplex_support]
      exact Set.union_subset
        (Set.subset_iUnion_of_subset t
          (Set.subset_iUnion_of_subset ht (by rfl)))
        (Set.subset_iUnion_of_subset u
          (Set.subset_iUnion_of_subset huData.1 (by rfl)))
    have hpInteriorSupport : p ∈ interior M.toPlaneComplex.support :=
      interior_mono hUnionSubset hpInteriorUnion
    exact (Set.disjoint_left.1 disjoint_interior_frontier hpInteriorSupport hpFrontier)
  exact ⟨t, ht, e, ⟨heEdges, hIncidentCard⟩, heT, hpEdge⟩

theorem mem_frontier_iff_exists_boundaryEdge_of_nonvertex {p : Plane}
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    p ∈ frontier M.toPlaneComplex.support ↔
      ∃ e : Finset M.Vertex, M.IsBoundaryEdge e ∧
        p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  constructor
  · intro hp
    obtain ⟨-, -, e, he, -, hpe⟩ :=
      M.exists_boundaryEdge_through_frontier_point hp hpv
    exact ⟨e, he, hpe⟩
  · rintro ⟨e, he, hpe⟩
    exact M.mem_frontier_of_mem_boundaryEdge he hpe hpv

/-- Away from mesh vertices, a triangle's frontier trace is exactly the union of its
incidence-one edges.  Extra isolated frontier vertices are precisely the obstruction addressed
by Moise's cutting induction. -/
theorem frontier_inter_triangleCarrier_diff_vertices {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) :
    (frontier M.toPlaneComplex.support ∩ M.triangleCarrier t) \ Set.range M.position =
      (⋃ e ∈ M.boundaryEdges t,
        convexHull ℝ (M.position '' (e : Set M.Vertex))) \ Set.range M.position := by
  ext p
  constructor
  · rintro ⟨⟨hpFrontier, hpT⟩, hpNotVertex⟩
    have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
      intro v hp
      exact hpNotVertex ⟨v, hp.symm⟩
    obtain ⟨e, he, hpEdge⟩ :=
      (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hpv).mp hpFrontier
    obtain ⟨u, hu, heuPower⟩ := Finset.mem_biUnion.mp he.1
    have heuData := Finset.mem_powersetCard.mp heuPower
    have het : e ⊆ t := M.edge_subset_of_nonvertex_mem_triangleCarrier heuData.2
      heuData.1 hu ht hpEdge hpT hpv
    have heBoundary : e ∈ M.boundaryEdges t :=
      M.mem_boundaryEdges_iff.mpr ⟨het, heuData.2, he⟩
    exact ⟨Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem heBoundary hpEdge), hpNotVertex⟩
  · rintro ⟨hpUnion, hpNotVertex⟩
    simp only [Set.mem_iUnion] at hpUnion
    obtain ⟨e, heBoundary, hpEdge⟩ := hpUnion
    have heData := M.mem_boundaryEdges_iff.mp heBoundary
    have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
      intro v hp
      exact hpNotVertex ⟨v, hp.symm⟩
    refine ⟨⟨M.mem_frontier_of_mem_boundaryEdge heData.2.2 hpEdge hpv, ?_⟩,
      hpNotVertex⟩
    exact convexHull_mono (Set.image_mono heData.1) hpEdge

/-- No mesh vertex contributes an isolated point to this triangle's frontier trace. -/
def HasNoIsolatedFrontierVertex (t : Finset M.Vertex) : Prop :=
  ∀ v : M.Vertex, M.position v ∈ frontier M.toPlaneComplex.support →
    M.position v ∈ M.triangleCarrier t →
      ∃ e ∈ M.boundaryEdges t,
        M.position v ∈ convexHull ℝ (M.position '' (e : Set M.Vertex))

/-- An isolated point in a triangle's frontier trace must be one of the triangle's own
vertices.  This remains valid when the mesh vertex type contains unused retained vertices. -/
theorem vertex_mem_triangle_of_frontier_not_mem_boundaryEdges (T : M.Triangle)
    (v : M.Vertex) (hvFrontier : M.position v ∈ frontier M.toPlaneComplex.support)
    (hvTriangle : M.position v ∈ M.triangleCarrier T.1)
    (hvBoundary : ∀ e ∈ M.boundaryEdges T.1,
      M.position v ∉ convexHull ℝ (M.position '' (e : Set M.Vertex))) :
    v ∈ T.1 := by
  have htriangleSubset : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 (by rfl))
  have hvNotInterior : M.position v ∉ interior (M.triangleCarrier T.1) := by
    intro hvInterior
    have hvSupportInterior := interior_mono htriangleSubset hvInterior
    exact Set.disjoint_left.mp disjoint_interior_frontier hvSupportInterior hvFrontier
  have htriangleClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hvTriangleFrontier : M.position v ∈ frontier (M.triangleCarrier T.1) := by
    rw [htriangleClosed.frontier_eq]
    exact ⟨hvTriangle, hvNotInterior⟩
  obtain ⟨e, hecard, heT, hvEdge⟩ :=
    M.exists_edge_of_mem_frontier_triangle T.2 hvTriangleFrontier
  have hvEdgeVertices : M.position v ∈ M.position '' (e : Set M.Vertex) := by
    by_contra hvNotVertices
    by_cases heBoundary : M.IsBoundaryEdge e
    · have heMem : e ∈ M.boundaryEdges T.1 :=
        M.mem_boundaryEdges_iff.mpr ⟨heT, hecard, heBoundary⟩
      exact hvBoundary e heMem hvEdge
    · have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
          T.2 hecard heT heBoundary
      have hTIncident : T.1 ∈ M.incidentTriangles e :=
        M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
      have hother : ∃ u ∈ M.incidentTriangles e, u ≠ T.1 := by
        by_contra h
        push Not at h
        have hsingleton : M.incidentTriangles e = {T.1} := by
          ext u
          constructor
          · exact fun hu => Finset.mem_singleton.mpr (h u hu)
          · intro hu
            rw [Finset.mem_singleton.mp hu]
            exact hTIncident
        rw [hsingleton] at hcard
        simp at hcard
      obtain ⟨u, huIncident, huT⟩ := hother
      have huData := M.mem_incidentTriangles_iff.mp huIncident
      let U : M.Triangle := ⟨u, huData.1⟩
      have hvInteriorUnion :=
        M.mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
          (T := T) (U := U) huT.symm hecard heT huData.2 hvEdge hvNotVertices
      have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
          M.toPlaneComplex.support := by
        rw [M.toPlaneComplex_support]
        exact Set.union_subset
          (Set.subset_iUnion_of_subset T.1
            (Set.subset_iUnion_of_subset T.2 (by rfl)))
          (Set.subset_iUnion_of_subset U.1
            (Set.subset_iUnion_of_subset U.2 (by rfl)))
      have hvSupportInterior := interior_mono hUnionSubset hvInteriorUnion
      exact Set.disjoint_left.mp disjoint_interior_frontier hvSupportInterior hvFrontier
  obtain ⟨w, hwe, hwv⟩ := hvEdgeVertices
  have hw : w = v := M.position_injective (hwv.trans rfl)
  rw [← hw]
  exact heT hwe

/-- If two edges of a maximal triangle are boundary edges, every frontier vertex on that
triangle lies on one of them. -/
theorem hasNoIsolatedFrontierVertex_of_boundaryEdges_card_two (T : M.Triangle)
    (hcard : (M.boundaryEdges T.1).card = 2) :
    M.HasNoIsolatedFrontierVertex T.1 := by
  intro v hvFrontier hvTriangle
  by_contra hexists
  push Not at hexists
  have hvT := M.vertex_mem_triangle_of_frontier_not_mem_boundaryEdges
    T v hvFrontier hvTriangle hexists
  obtain ⟨e, f, hef, hboundary⟩ := Finset.card_eq_two.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have hfMem : f ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  have hfData := M.mem_boundaryEdges_iff.mp hfMem
  have hvNotE : v ∉ e := by
    intro hve
    exact hexists e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
  have hvNotF : v ∉ f := by
    intro hvf
    exact hexists f hfMem (subset_convexHull ℝ _ ⟨v, hvf, rfl⟩)
  have heraseCard : (T.1.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvT, M.card_triangle T.1 T.2]
  have heErase : e = T.1.erase v :=
    Finset.eq_of_subset_of_card_le
      (fun w hw => Finset.mem_erase.mpr
        ⟨fun hwv => hvNotE (hwv ▸ hw), heData.1 hw⟩)
      (by rw [heData.2.1, heraseCard])
  have hfErase : f = T.1.erase v :=
    Finset.eq_of_subset_of_card_le
      (fun w hw => Finset.mem_erase.mpr
        ⟨fun hwv => hvNotF (hwv ▸ hw), hfData.1 hw⟩)
      (by rw [hfData.2.1, heraseCard])
  exact hef (heErase.trans hfErase.symm)

theorem frontier_inter_triangleCarrier_eq_boundaryEdges {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hvertices : M.HasNoIsolatedFrontierVertex t) :
    frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
      ⋃ e ∈ M.boundaryEdges t,
        convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpVertex : p ∈ Set.range M.position
    · obtain ⟨v, rfl⟩ := hpVertex
      obtain ⟨e, he, hpe⟩ := hvertices v hp.1 hp.2
      exact Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem he hpe)
    · have hpDiff : p ∈
          (frontier M.toPlaneComplex.support ∩ M.triangleCarrier t) \
            Set.range M.position := ⟨hp, hpVertex⟩
      rw [M.frontier_inter_triangleCarrier_diff_vertices ht] at hpDiff
      exact hpDiff.1
  · intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    have heData := M.mem_boundaryEdges_iff.mp he
    exact ⟨M.boundaryEdgeCarrier_subset_frontier heData.2.2 hpe,
      convexHull_mono (Set.image_mono heData.1) hpe⟩

/-- An infinite frontier of a finite face-to-face planar mesh contains a boundary edge.  This is
the weak free-triangle existence theorem used at the start of Moise's finite induction. -/
theorem exists_free_triangle (hfrontier : (frontier M.toPlaneComplex.support).Infinite) :
    ∃ t, M.IsFreeTriangle t := by
  classical
  let vertexPositions : Finset Plane := Finset.univ.image M.position
  obtain ⟨p, hpFrontier, hpNotVertex⟩ :=
    hfrontier.exists_notMem_finset vertexPositions
  have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
    intro v hpv
    apply hpNotVertex
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hpv.symm⟩
  obtain ⟨t, ht, e, he, het, -⟩ :=
    M.exists_boundaryEdge_through_frontier_point hpFrontier hpv
  exact ⟨t, ht, e, he, het⟩

/-- The frontier of every nonempty finite planar triangle mesh is infinite. -/
theorem frontier_infinite_of_triangles_nonempty (hne : M.triangles.Nonempty) :
    (frontier M.toPlaneComplex.support).Infinite := by
  classical
  obtain ⟨t, ht⟩ := hne
  let T : M.Triangle := ⟨t, ht⟩
  have hcarrierInterior : (interior (M.triangleCarrier t)).Nonempty := by
    let b := M.triangleAffineBasis ht
    have hrange := M.range_triangleAffineBasis ht
    have hspan : affineSpan ℝ (Set.range b) = ⊤ := b.tot
    have hnonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
    simpa only [triangleCarrier, b, hrange] using hnonempty
  have hcarrierSubset : M.triangleCarrier t ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t
      (Set.subset_iUnion_of_subset ht (by rfl))
  have hinterior : (interior M.toPlaneComplex.support).Nonempty :=
    hcarrierInterior.mono (interior_mono hcarrierSubset)
  have hsupportClosed : IsClosed M.toPlaneComplex.support :=
    M.toPlaneComplex.isCompact_support.isClosed
  have hsupportNe : M.toPlaneComplex.support ≠ Set.univ :=
    M.toPlaneComplex.isCompact_support.ne_univ
  obtain ⟨q, hq⟩ : (M.toPlaneComplex.supportᶜ).Nonempty :=
    Set.nonempty_compl.mpr hsupportNe
  have hqInterior : q ∈ interior M.toPlaneComplex.supportᶜ := by
    rw [hsupportClosed.isOpen_compl.interior_eq]
    exact hq
  intro hfinite
  have hconnected : IsConnected ((frontier M.toPlaneComplex.support)ᶜ) :=
    hfinite.countable.isConnected_compl_of_one_lt_rank (by
      apply Module.one_lt_rank_of_one_lt_finrank
      simp [Plane])
  have hdecomp : (frontier M.toPlaneComplex.support)ᶜ =
      interior M.toPlaneComplex.support ∪ interior M.toPlaneComplex.supportᶜ :=
    compl_frontier_eq_union_interior
  have hdisjoint : Disjoint (interior M.toPlaneComplex.support)
      (interior M.toPlaneComplex.supportᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  obtain ⟨p, hpInterior⟩ := hinterior
  have hpComplFrontier : p ∈ (frontier M.toPlaneComplex.support)ᶜ := by
    rw [hdecomp]
    exact Or.inl hpInterior
  have hallInterior : (frontier M.toPlaneComplex.support)ᶜ ⊆
      interior M.toPlaneComplex.support :=
    hconnected.isPreconnected.subset_left_of_subset_union isOpen_interior isOpen_interior
      hdisjoint (by rw [hdecomp]) ⟨p, hpComplFrontier, hpInterior⟩
  have hqComplFrontier : q ∈ (frontier M.toPlaneComplex.support)ᶜ := by
    rw [hdecomp]
    exact Or.inr hqInterior
  exact Set.disjoint_left.mp hdisjoint (hallInterior hqComplFrontier) hqInterior

theorem exists_free_triangle_of_triangles_nonempty (hne : M.triangles.Nonempty) :
    ∃ t, M.IsFreeTriangle t :=
  M.exists_free_triangle (M.frontier_infinite_of_triangles_nonempty hne)

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification05_block_01
/- END ClassificationOfSurfaces.Moise.FreeTriangle -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision | e9744546f8b8951d8e637408a81c70c8b62b441a072294d883a21cf82b7a6ccf -/
section schottkyclassification05_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Fine subdivisions of intrinsic two-complexes

The midpoint subdivision is quantitatively faithful: on every iteration, the image diameter of
each new face is at most half that of its parent.  This supplies the finite fine-subdivision and
open-subcomplex extraction used in the compact form of Moise Chapter 8, Theorem 2.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- The barycentric realization point at a specified vertex of a specified maximal face. -/
noncomputable def facePoint (t : K.Face) (v : t.1) : K.realization :=
  K.vertexPoint ⟨v.1, t.1, t.2, v.2⟩

@[simp] theorem facePoint_val (t : K.Face) (v : t.1) :
    (K.facePoint t v).1 = Pi.single v.1 1 := rfl

theorem facePoint_mem_faceCarrier (t : K.Face) (v : t.1) :
    K.facePoint t v ∈ K.faceCarrier t.1 :=
  (K.vertexPoint_mem_faceCarrier_iff ⟨v.1, t.1, t.2, v.2⟩ t.1).mpr v.2

theorem sum_face_coords (t : K.Face) (x : K.realization)
    (hx : x ∈ K.faceCarrier t.1) :
    ∑ v : t.1, x.1 v.1 = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    ∑ v ∈ t.1, x.1 v = ∑ v, x.1 v :=
      Finset.sum_subset (Finset.subset_univ t.1) (fun v _ hv => hx v hv)
    _ = 1 := x.2.1.2

theorem face_affineCombination_eq (t : K.Face) (x : K.realization)
    (hx : x ∈ K.faceCarrier t.1) :
    (Finset.univ.affineCombination ℝ
      (fun v : t.1 => (K.facePoint t v).1) (fun v => x.1 v.1)) = x.1 := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (K.sum_face_coords t x hx)]
  funext w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, K.facePoint_val]
  by_cases hw : w ∈ t.1
  · let v : t.1 := ⟨w, hw⟩
    rw [Finset.sum_eq_single v]
    · simp [v]
    · intro u _ huv
      have huw : u.1 ≠ w := fun h => huv (Subtype.ext h)
      simp [huw]
    · simp
  · have hxw : x.1 w = 0 := hx w hw
    rw [hxw]
    apply Finset.sum_eq_zero
    intro v _
    have hvw : v.1 ≠ w := fun h => hw (h ▸ v.2)
    simp [hvw]

/-- An affine image of a face lies in the convex hull of the images of its three vertices. -/
theorem affine_mem_convexHull_facePoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    (x : K.realization) (hx : x ∈ K.faceCarrier t.1) :
    a x.1 ∈ convexHull ℝ
      (Set.range fun v : t.1 => a (K.facePoint t v).1) := by
  let w : t.1 → ℝ := fun v => x.1 v.1
  have hw0 : ∀ v ∈ (Finset.univ : Finset t.1), 0 ≤ w v :=
    fun v _ => x.2.1.1 v.1
  have hw1 : ∑ v ∈ (Finset.univ : Finset t.1), w v = 1 := by
    simpa only [Finset.sum_const_zero, w] using K.sum_face_coords t x hx
  have hmem := affineCombination_mem_convexHull hw0 hw1
    (v := fun v : t.1 => a (K.facePoint t v).1)
  have heq : a x.1 = (Finset.univ.affineCombination ℝ
      (fun v : t.1 => a (K.facePoint t v).1) w) := by
    calc
      a x.1 = a (Finset.univ.affineCombination ℝ
          (fun v : t.1 => (K.facePoint t v).1) w) := by
        rw [K.face_affineCombination_eq t x hx]
      _ = Finset.univ.affineCombination ℝ
          (a ∘ fun v : t.1 => (K.facePoint t v).1) w :=
        Finset.map_affineCombination _ _ _ hw1 a
      _ = Finset.univ.affineCombination ℝ
          (fun v : t.1 => a (K.facePoint t v).1) w := rfl
  rwa [← heq] at hmem

/-- Distances in an affine image of one face are bounded by a distance between vertex images. -/
theorem exists_facePoints_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    (x y : K.realization) (hx : x ∈ K.faceCarrier t.1)
    (hy : y ∈ K.faceCarrier t.1) :
    ∃ v w : t.1,
      dist (a x.1) (a y.1) ≤
        dist (a (K.facePoint t v).1) (a (K.facePoint t w).1) := by
  obtain ⟨p, ⟨v, rfl⟩, q, ⟨w, rfl⟩, hpq⟩ :=
    convexHull_exists_dist_ge2
      (K.affine_mem_convexHull_facePoints t a x hx)
      (K.affine_mem_convexHull_facePoints t a y hy)
  exact ⟨v, w, hpq⟩

/-- Affine maps preserve midpoints. -/
theorem affine_map_midpoint
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E →ᵃ[ℝ] F) (x y : E) :
    a (midpoint ℝ x y) = midpoint ℝ (a x) (a y) := by
  let s : Finset Bool := {false, true}
  let p : Bool → E := fun b => if b then y else x
  let w : Bool → ℝ := fun _ => (2 : ℝ)⁻¹
  have hw : ∑ i ∈ s, w i = 1 := by simp [s, w]
  have hs : s.affineCombination ℝ p w = midpoint ℝ x y := by
    simp only [s, p, w, Finset.affineCombination_eq_linear_combination, hw,
      Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true, not_false_eq_true,
      Finset.sum_singleton, if_false, if_true, midpoint, AffineMap.lineMap_apply_module]
    congr 1
    norm_num
  have ht : s.affineCombination ℝ (a ∘ p) w = midpoint ℝ (a x) (a y) := by
    simp only [s, p, w, Finset.affineCombination_eq_linear_combination, hw,
      Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true, not_false_eq_true,
      Finset.sum_singleton, Function.comp_apply, if_false, if_true, midpoint,
      AffineMap.lineMap_apply_module]
    congr 1
    norm_num
  rw [← hs, Finset.map_affineCombination s p w hw a, ht]

theorem midpointPosition_faceEdge (t : K.Face) (i : ZMod 3) :
    K.midpointPosition (Sum.inr (K.faceEdge t i)) =
      midpoint ℝ (Pi.single (K.faceVertex t i) 1 : K.Vertex → ℝ)
        (Pi.single (K.faceVertex t (i + 1)) 1 : K.Vertex → ℝ) := by
  funext v
  by_cases hvi : v = K.faceVertex t i
  · subst v
    simp [midpoint, AffineMap.lineMap_apply_module, K.faceVertex_ne_next t i]
    norm_num
  · by_cases hvj : v = K.faceVertex t (i + 1)
    · subst v
      simp [midpoint, AffineMap.lineMap_apply_module, hvi]
    · have hvEdge : v ∉ (K.faceEdge t i).1 := by
        simp [hvi, hvj]
      simp [midpointPosition, midpoint, AffineMap.lineMap_apply_module, hvi, hvj]

theorem midpointEval_facePoint
    (s : K.midpointComplex.Face) (w : s.1) :
    (K.midpointEval (K.midpointComplex.facePoint s w)).1 =
      K.midpointPosition w.1 := by
  rw [K.midpointEval_val]; erw [K.midpointEvalAffine_apply]
  simp only [K.midpointComplex.facePoint_val]
  let q : K.MidpointVertex := w.1
  change (∑ u : K.MidpointVertex,
    (Pi.single q 1 : K.MidpointVertex → ℝ) u • K.midpointPosition u) =
      K.midpointPosition q
  rw [Finset.sum_eq_single q]
  · simp []
  · intro u _ huw
    simp [huw]
  · simp

theorem midpointEvalAffine_facePoint
    (s : K.midpointComplex.Face) (w : s.1) :
    K.midpointEvalAffine (K.midpointComplex.facePoint s w).1 =
      K.midpointPosition w.1 := by
  simpa only [← K.midpointEval_val] using K.midpointEval_facePoint s w

/-- A mesh bound measured after transporting each refined face into the original realization. -/
def Subdivision.MeshLE {K : IntrinsicTwoComplex} (R : K.Subdivision) (d : ℝ) : Prop :=
  ∀ t ∈ R.refined.faces, ∀ x ∈ R.refined.faceCarrier t,
    ∀ y ∈ R.refined.faceCarrier t, dist (R.homeo x) (R.homeo y) ≤ d

theorem Subdivision.meshLE_nonneg {K : IntrinsicTwoComplex} {R : K.Subdivision} {d : ℝ}
    (hR : R.MeshLE d) (t : R.refined.Face) : 0 ≤ d := by
  have htpos : 0 < t.1.card := by rw [R.refined.faces_card t.1 t.2]; decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  let p := R.refined.facePoint t ⟨v, hv⟩
  simpa only [dist_self] using hR t.1 t.2 p
    (R.refined.facePoint_mem_faceCarrier t _) p
    (R.refined.facePoint_mem_faceCarrier t _)

theorem dist_midpointPosition_corner_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (i : ZMod 3) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    {d : ℝ} (hd : 0 ≤ d)
    (hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (K.faceVertex t j) 1))
        (a (Pi.single (K.faceVertex t k) 1)) ≤ d)
    {w z : K.MidpointVertex} (hw : w ∈ K.midpointCornerFace t i)
    (hz : z ∈ K.midpointCornerFace t i) :
    dist (a (K.midpointPosition w)) (a (K.midpointPosition z)) ≤ d / 2 := by
  let P : ZMod 3 → E := fun j => a (Pi.single (K.faceVertex t j) 1)
  have hedge (j : ZMod 3) :
      a (K.midpointPosition (Sum.inr (K.faceEdge t j))) =
        midpoint ℝ (P j) (P (j + 1)) := by
    rw [K.midpointPosition_faceEdge t j, affine_map_midpoint]
  have hold (j : ZMod 3) :
      a (K.midpointPosition (Sum.inl (K.faceVertex t j))) = P j := rfl
  have hw' : w = Sum.inl (K.faceVertex t i) ∨
      w = Sum.inr (K.faceEdge t i) ∨
      w = Sum.inr (K.faceEdge t (i + 2)) := by
    simpa [midpointCornerFace] using hw
  have hz' : z = Sum.inl (K.faceVertex t i) ∨
      z = Sum.inr (K.faceEdge t i) ∨
      z = Sum.inr (K.faceEdge t (i + 2)) := by
    simpa [midpointCornerFace] using hz
  rcases hw' with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  · rw [hold, dist_self]
    positivity
  · rw [hold, hedge, dist_left_midpoint]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P i) (P (i + 1)) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex i (i + 1)) (by norm_num)
      _ = d / 2 := by ring
  · rw [hold, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, dist_right_midpoint]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P (i + 2)) (P i) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex (i + 2) i) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, hold, dist_midpoint_left]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P i) (P (i + 1)) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex i (i + 1)) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, dist_self]
    positivity
  · rw [hedge, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, midpoint_comm (R := ℝ) (P (i + 2)) (P i)]
    calc
      dist (midpoint ℝ (P i) (P (i + 1)))
          (midpoint ℝ (P i) (P (i + 2))) ≤
          (dist (P i) (P i) + dist (P (i + 1)) (P (i + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, hold]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, dist_midpoint_right]
    norm_num
    calc
      (1 / 2 : ℝ) * dist (P (i + 2)) (P i) ≤ (1 / 2) * d :=
        mul_le_mul_of_nonneg_left (hvertex (i + 2) i) (by norm_num)
      _ = d / 2 := by ring
  · rw [hedge, hedge]
    have hcycle : i + 2 + 1 = i := zmod3_add_two_add_one i
    rw [hcycle, midpoint_comm (R := ℝ) (P (i + 2)) (P i), dist_comm]
    calc
      dist (midpoint ℝ (P i) (P (i + 1)))
          (midpoint ℝ (P i) (P (i + 2))) ≤
          (dist (P i) (P i) + dist (P (i + 1)) (P (i + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, dist_self]
    positivity

theorem dist_midpointPosition_central_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K.Face) (a : (K.Vertex → ℝ) →ᵃ[ℝ] E)
    {d : ℝ} (hd : 0 ≤ d)
    (hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (K.faceVertex t j) 1))
        (a (Pi.single (K.faceVertex t k) 1)) ≤ d)
    {w z : K.MidpointVertex} (hw : w ∈ K.midpointCentralFace t)
    (hz : z ∈ K.midpointCentralFace t) :
    dist (a (K.midpointPosition w)) (a (K.midpointPosition z)) ≤ d / 2 := by
  let P : ZMod 3 → E := fun j => a (Pi.single (K.faceVertex t j) 1)
  have hedge (j : ZMod 3) :
      a (K.midpointPosition (Sum.inr (K.faceEdge t j))) =
        midpoint ℝ (P j) (P (j + 1)) := by
    rw [K.midpointPosition_faceEdge t j, affine_map_midpoint]
  rw [midpointCentralFace] at hw hz
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
  rcases (by decide : ∀ j k : ZMod 3, k = j ∨ k = j + 1 ∨ k = j + 2) j k with
    rfl | rfl | rfl
  · rw [hedge, dist_self]
    positivity
  · rw [hedge, hedge, midpoint_comm (R := ℝ) (P j) (P (j + 1))]
    calc
      dist (midpoint ℝ (P (j + 1)) (P j))
          (midpoint ℝ (P (j + 1)) (P (j + 1 + 1))) ≤
          (dist (P (j + 1)) (P (j + 1)) +
            dist (P j) (P (j + 1 + 1))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _
  · rw [hedge, hedge]
    have hcycle : j + 2 + 1 = j := zmod3_add_two_add_one j
    rw [hcycle, midpoint_comm (R := ℝ) (P (j + 2)) (P j)]
    calc
      dist (midpoint ℝ (P j) (P (j + 1)))
          (midpoint ℝ (P j) (P (j + 2))) ≤
          (dist (P j) (P j) + dist (P (j + 1)) (P (j + 2))) / 2 :=
        dist_midpoint_midpoint_le _ _ _ _
      _ ≤ d / 2 := by simp only [dist_self, zero_add]; gcongr; exact hvertex _ _



/-- One midpoint subdivision halves every existing mesh bound. -/
theorem Subdivision.meshLE_trans_midpoint
    {K : IntrinsicTwoComplex} (R : K.Subdivision) {d : ℝ}
    (hR : R.MeshLE d) :
    (R.trans R.refined.midpointSubdivision).MeshLE (d / 2) := by
  intro s hs x hx y hy
  change dist (R.homeo (R.refined.midpointHomeomorph x))
    (R.homeo (R.refined.midpointHomeomorph y)) ≤ d / 2
  erw [R.refined.midpointHomeomorph_apply, R.refined.midpointHomeomorph_apply]
  obtain ⟨t, hst⟩ := R.refined.exists_parentFace_of_mem_midpointFaces hs
  obtain ⟨a, ha⟩ := R.affineOnFace t.1 t.2
  have hxParent : R.refined.midpointEval x ∈ R.refined.faceCarrier t.1 :=
    R.refined.midpointEval_mem_parentFace t hst x hx
  have hyParent : R.refined.midpointEval y ∈ R.refined.faceCarrier t.1 :=
    R.refined.midpointEval_mem_parentFace t hst y hy
  have hvertex : ∀ j k : ZMod 3,
      dist (a (Pi.single (R.refined.faceVertex t j) 1))
        (a (Pi.single (R.refined.faceVertex t k) 1)) ≤ d := by
    intro j k
    let v : t.1 := ⟨R.refined.faceVertex t j, R.refined.faceVertex_mem t j⟩
    let w : t.1 := ⟨R.refined.faceVertex t k, R.refined.faceVertex_mem t k⟩
    have h := hR t.1 t.2 (R.refined.facePoint t v)
      (R.refined.facePoint_mem_faceCarrier t v) (R.refined.facePoint t w)
      (R.refined.facePoint_mem_faceCarrier t w)
    change dist ((R.homeo (R.refined.facePoint t v)).1)
      ((R.homeo (R.refined.facePoint t w)).1) ≤ d at h
    rw [ha _ (R.refined.facePoint_mem_faceCarrier t v),
      ha _ (R.refined.facePoint_mem_faceCarrier t w)] at h
    simpa only [R.refined.facePoint_val, v, w] using h
  let b : (R.refined.midpointComplex.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
    a.comp R.refined.midpointEvalAffine
  let S : R.refined.midpointComplex.Face := ⟨s, hs⟩
  obtain ⟨v, w, hvw⟩ :=
    R.refined.midpointComplex.exists_facePoints_dist_ge S b x y hx hy
  have hxy : dist (R.homeo (R.refined.midpointEval x))
      (R.homeo (R.refined.midpointEval y)) = dist (b x.1) (b y.1) := by
    change dist ((R.homeo (R.refined.midpointEval x)).1)
      ((R.homeo (R.refined.midpointEval y)).1) = _
    rw [ha _ hxParent, ha _ hyParent]
    rfl
  rw [hxy]
  refine hvw.trans ?_
  have hbv : b (R.refined.midpointComplex.facePoint S v).1 =
      a (R.refined.midpointPosition v.1) := by
    change a (R.refined.midpointEvalAffine
      (R.refined.midpointComplex.facePoint S v).1) = _
    rw [R.refined.midpointEvalAffine_facePoint S v]
  have hbw : b (R.refined.midpointComplex.facePoint S w).1 =
      a (R.refined.midpointPosition w.1) := by
    change a (R.refined.midpointEvalAffine
      (R.refined.midpointComplex.facePoint S w).1) = _
    rw [R.refined.midpointEvalAffine_facePoint S w]
  rw [hbv, hbw]
  have hd : 0 ≤ d := R.meshLE_nonneg hR t
  rw [midpointFacesOver] at hst
  replace hst := Finset.mem_union.mp hst
  rcases hst with hcorner | hcentral
  · obtain ⟨i, -, hsi⟩ := Finset.mem_image.mp hcorner
    have hv : v.1 ∈ R.refined.midpointCornerFace t i := by rw [hsi]; exact v.2
    have hw : w.1 ∈ R.refined.midpointCornerFace t i := by rw [hsi]; exact w.2
    exact R.refined.dist_midpointPosition_corner_le t i a hd hvertex hv hw
  · have hscentral : s = R.refined.midpointCentralFace t :=
      Finset.mem_singleton.mp hcentral
    have hv : v.1 ∈ R.refined.midpointCentralFace t := by rw [← hscentral]; exact v.2
    have hw : w.1 ∈ R.refined.midpointCentralFace t := by rw [← hscentral]; exact w.2
    exact R.refined.dist_midpointPosition_central_le t a hd hvertex hv hw

/-- The identity subdivision has mesh at most one in barycentric sup distance. -/
theorem Subdivision.refl_meshLE (K : IntrinsicTwoComplex) :
    (Subdivision.refl K).MeshLE 1 := by
  intro t ht x hx y hy
  change dist x.1 y.1 ≤ 1
  rw [dist_pi_le_iff zero_le_one]
  intro v
  rw [Real.dist_eq, abs_le]
  have hxv := mem_Icc_of_mem_stdSimplex x.2.1 v
  have hyv := mem_Icc_of_mem_stdSimplex y.2.1 v
  rcases hxv with ⟨hx0, hx1⟩
  rcases hyv with ⟨hy0, hy1⟩
  constructor <;> linarith

/-- The `n`-fold intrinsic midpoint subdivision. -/
noncomputable def iteratedMidpointSubdivision (K : IntrinsicTwoComplex) :
    (n : ℕ) → K.Subdivision
  | 0 => Subdivision.refl K
  | n + 1 =>
      let R := K.iteratedMidpointSubdivision n
      R.trans R.refined.midpointSubdivision

@[simp] theorem iteratedMidpointSubdivision_zero (K : IntrinsicTwoComplex) :
    K.iteratedMidpointSubdivision 0 = Subdivision.refl K := rfl

theorem iteratedMidpointSubdivision_succ (K : IntrinsicTwoComplex) (n : ℕ) :
    K.iteratedMidpointSubdivision (n + 1) =
      (K.iteratedMidpointSubdivision n).trans
        (K.iteratedMidpointSubdivision n).refined.midpointSubdivision := rfl

/-- Every iterated midpoint refinement preserves the surface edge-valence bound. -/
theorem hasSurfaceEdgeValence_iteratedMidpointSubdivision
    (K : IntrinsicTwoComplex) (hK : K.HasSurfaceEdgeValence) :
    ∀ n, (K.iteratedMidpointSubdivision n).refined.HasSurfaceEdgeValence := by
  intro n
  induction n with
  | zero =>
      simpa [iteratedMidpointSubdivision] using hK
  | succ n ih =>
      exact
        (K.iteratedMidpointSubdivision n).refined.hasSurfaceEdgeValence_midpointComplex ih

/-- Quantitative mesh estimate for iterated midpoint subdivision. -/
theorem iteratedMidpointSubdivision_meshLE (K : IntrinsicTwoComplex) (n : ℕ) :
    (K.iteratedMidpointSubdivision n).MeshLE ((1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => simpa using Subdivision.refl_meshLE K
  | succ n ih =>
      rw [K.iteratedMidpointSubdivision_succ n]
      have h := (K.iteratedMidpointSubdivision n).meshLE_trans_midpoint ih
      convert h using 1
      rw [pow_succ]
      ring

/-- Every intrinsic finite two-complex has a faithful subdivision of arbitrarily small mesh. -/
theorem exists_subdivision_mesh_lt (K : IntrinsicTwoComplex) {eps : ℝ} (heps : 0 < eps) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∀ x ∈ R.refined.faceCarrier t, ∀ y ∈ R.refined.faceCarrier t,
        dist (R.homeo x) (R.homeo y) < eps := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.iteratedMidpointSubdivision n
  refine ⟨R, ?_⟩
  intro t ht x hx y hy
  exact (K.iteratedMidpointSubdivision_meshLE n t ht x hx y hy).trans_lt hn

/-- Heine--Cantor and faithful midpoint subdivision make the image of every refined face have
arbitrarily small diameter under a continuous map. -/
theorem exists_subdivision_image_dist_lt (K : IntrinsicTwoComplex)
    {h : K.realization → Plane} (hcont : Continuous h)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∀ x ∈ R.refined.faceCarrier t, ∀ y ∈ R.refined.faceCarrier t,
        dist (h (R.homeo x)) (h (R.homeo y)) < eps := by
  have huniform : UniformContinuousOn h (Set.univ : Set K.realization) :=
    isCompact_univ.uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) eps heps
  obtain ⟨R, hR⟩ := K.exists_subdivision_mesh_lt hdelta
  refine ⟨R, ?_⟩
  intro t ht x hx y hy
  exact hcontrol (R.homeo x) (Set.mem_univ _) (R.homeo y) (Set.mem_univ _)
    (hR t ht x hx y hy)

/-- A sufficiently fine intrinsic subdivision is subordinate to any open cover. -/
theorem exists_subdivision_subordinate_openCover (K : IntrinsicTwoComplex)
    {I : Type*} (U : I → Set K.realization) (hU : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set K.realization) ⊆ ⋃ i, U i) :
    ∃ R : K.Subdivision, ∀ t ∈ R.refined.faces,
      ∃ i, ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U i := by
  obtain ⟨delta, hdelta, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set K.realization))
      isCompact_univ hU hcover
  obtain ⟨R, hR⟩ := K.exists_subdivision_mesh_lt hdelta
  refine ⟨R, ?_⟩
  intro t ht
  have htpos : 0 < t.card := by rw [R.refined.faces_card t ht]; decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  let T : R.refined.Face := ⟨t, ht⟩
  let p := R.refined.facePoint T ⟨v, hv⟩
  obtain ⟨i, hi⟩ := hLebesgue (R.homeo p) (Set.mem_univ _)
  refine ⟨i, fun x hx => hi ?_⟩
  rw [Metric.mem_ball]
  rw [dist_comm]
  exact hR t ht p (R.refined.facePoint_mem_faceCarrier T _) x hx

/-! ## Finite subcomplexes between compact and open sets -/

/-- A finite subcomplex of a faithful subdivision of `K`, selected so that its carrier contains
the prescribed compact set `C` and remains inside the prescribed open set `U`.

This is the finite-complex form of the compact part of Moise Ch. 8, Thm. 2.  The full theorem in
Moise treats arbitrary open subsets by a locally finite exhaustion; the Radó step only needs a
finite collar around the compact part already constructed. -/
structure OpenSubcomplex (K : IntrinsicTwoComplex) (C U : Set K.realization) where
  /-- A faithful finite refinement of the original complex. -/
  subdivision : K.Subdivision
  /-- The maximal refined faces retained in the subcomplex. -/
  keptFaces : Finset (Finset subdivision.refined.Vertex)
  /-- Every retained face is a face of the refined complex. -/
  keptFaces_subset : keptFaces ⊆ subdivision.refined.faces
  /-- The selected subcomplex contains `C` after transport to the original realization. -/
  covers : C ⊆ Set.range (subdivision.homeo ∘
    subdivision.refined.restrictFacesInclusion (fun t => t ∈ keptFaces))
  /-- Its transported carrier is contained in `U`. -/
  contained : Set.range (subdivision.homeo ∘
    subdivision.refined.restrictFacesInclusion (fun t => t ∈ keptFaces)) ⊆ U

namespace OpenSubcomplex

variable {K : IntrinsicTwoComplex} {C U : Set K.realization}

/-- The selected finite intrinsic complex. -/
abbrev complex (L : K.OpenSubcomplex C U) : IntrinsicTwoComplex :=
  L.subdivision.refined.restrictFaces (fun t => t ∈ L.keptFaces)

/-- Its canonical map into the original realization. -/
def inclusion (L : K.OpenSubcomplex C U) : L.complex.realization → K.realization :=
  L.subdivision.homeo ∘
    L.subdivision.refined.restrictFacesInclusion (fun t => t ∈ L.keptFaces)

/-- The canonical inclusion of an open subcomplex is an embedding. -/
theorem isEmbedding_inclusion (L : K.OpenSubcomplex C U) :
    _root_.Topology.IsEmbedding L.inclusion :=
  L.subdivision.homeo.isEmbedding.comp
    (L.subdivision.refined.isEmbedding_restrictFacesInclusion
      (fun t => t ∈ L.keptFaces))

/-- The carrier of the selected subcomplex in the original realization. -/
def support (L : K.OpenSubcomplex C U) : Set K.realization :=
  Set.range L.inclusion

theorem covers_support (L : K.OpenSubcomplex C U) : C ⊆ L.support :=
  L.covers

theorem support_subset (L : K.OpenSubcomplex C U) : L.support ⊆ U :=
  L.contained

end OpenSubcomplex

/-- A compact subset of an open subset of a finite intrinsic complex is covered by a finite
subcomplex of a faithful subdivision which is still contained in that open set. -/
theorem exists_openSubcomplex (K : IntrinsicTwoComplex) {C U : Set K.realization}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    Nonempty (K.OpenSubcomplex C U) := by
  classical
  let W : Bool → Set K.realization := fun b => if b then Cᶜ else U
  have hWopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b <;> simp [W, hU, hC.isClosed]
  have hWcover : (Set.univ : Set K.realization) ⊆ ⋃ b, W b := by
    intro x _
    by_cases hx : x ∈ C
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [W] using hCU hx⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [W] using hx⟩
  obtain ⟨R, hR⟩ := K.exists_subdivision_subordinate_openCover W hWopen hWcover
  let keep : Finset (Finset R.refined.Vertex) :=
    R.refined.faces.filter fun t =>
      ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U
  refine ⟨⟨R, keep, ?_, ?_, ?_⟩⟩
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro z hz
    let x : R.refined.realization := R.homeo.symm z
    rcases x.2.2 with ⟨t, ht, hxt⟩
    obtain ⟨b, hb⟩ := hR t ht
    have htU : ∀ y ∈ R.refined.faceCarrier t, R.homeo y ∈ U := by
      cases b with
      | false => simpa [W] using hb
      | true =>
          exfalso
          have hxcomp : z ∈ Cᶜ := by
            have := hb x hxt
            simpa [W, x] using this
          exact hxcomp hz
    have htkeep : t ∈ keep := Finset.mem_filter.mpr ⟨ht, htU⟩
    let y : (R.refined.restrictFaces (fun s => s ∈ keep)).realization :=
      ⟨x.1, x.2.1, ⟨t, (Finset.mem_filter (p := fun s => s ∈ keep)).mpr ⟨ht, htkeep⟩, hxt⟩⟩
    refine ⟨y, ?_⟩
    change R.homeo (R.refined.restrictFacesInclusion (fun s => s ∈ keep) y) = z
    rw [← R.homeo.apply_symm_apply z]
    congr 1
  · rintro z ⟨y, rfl⟩
    rcases y.2.2 with ⟨t, ht, hyt⟩
    have htkeep : t ∈ keep := ((Finset.mem_filter (p := fun t => t ∈ keep)).mp ht).2
    have htU := (Finset.mem_filter.mp htkeep).2
    exact htU (R.refined.restrictFacesInclusion (fun s => s ∈ keep) y) hyt

/-! ## Compact stages exhausting a proper open subset -/

/-- Finite faithful subcomplex stages exhausting an open subset of a finite intrinsic complex.
Each stage contains a canonical compact distance core and lies in the interior of the next
distance core.  The stages are not yet a single conforming locally finite complex: reconciling
their boundary subdivisions is the remaining combinatorial part of Moise Ch. 8, Thm. 2. -/
structure OpenExhaustion (K : IntrinsicTwoComplex) (U : Set K.realization) where
  /-- The `stage` declaration. -/
  stage : ∀ n : ℕ,
    K.OpenSubcomplex (frontierCore U n) (interior (frontierCore U (n + 1)))

namespace OpenExhaustion

variable {K : IntrinsicTwoComplex} {U : Set K.realization}

/-- The carrier of one finite stage, viewed in the original realization. -/
def stageSupport (E : K.OpenExhaustion U) (n : ℕ) : Set K.realization :=
  (E.stage n).support

theorem stageSupport_subset (E : K.OpenExhaustion U) (hUc : Uᶜ.Nonempty) (n : ℕ) :
    E.stageSupport n ⊆ U := by
  exact (E.stage n).support_subset.trans interior_subset |>.trans
    (frontierCore_subset hUc (n + 1))

/-- The finite stage carriers cover exactly the prescribed open set. -/
theorem iUnion_stageSupport (E : K.OpenExhaustion U) (hU : IsOpen U)
    (hUc : Uᶜ.Nonempty) :
    (⋃ n : ℕ, E.stageSupport n) = U := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact E.stageSupport_subset hUc n hn
  · intro x hx
    have hxC : x ∈ ⋃ n : ℕ, frontierCore U n := by
      rw [iUnion_frontierCore hU hUc]
      exact hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxC
    exact Set.mem_iUnion.mpr ⟨n, (E.stage n).covers hn⟩

end OpenExhaustion

/-- Every proper open subset of a finite intrinsic complex has a compactly nested exhaustion by
finite subcomplexes of faithful subdivisions. -/
theorem exists_openExhaustion (K : IntrinsicTwoComplex) {U : Set K.realization}
    (_ : IsOpen U) (_ : Uᶜ.Nonempty) : Nonempty (K.OpenExhaustion U) := by
  refine ⟨⟨fun n => Classical.choice (K.exists_openSubcomplex
    (isCompact_frontierCore U n) isOpen_interior
    (frontierCore_subset_interior_succ U n))⟩⟩

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification05_block_02
/- END ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.PolygonalArc | 7d31e62f3b97787e630dc73a5bdcce3314aa4520f60587471493c120730fc9fd -/
section schottkyclassification05_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal arcs from broken lines

This is the finite-arrangement layer needed between Moise Chapter 6, Theorems 1 and 2.  The
connectivity theorem produces an arbitrary finite chain of segments.  Subdividing a large
triangle by the supporting lines of those segments, and by two coordinate lines through every
chain vertex, turns all crossings and all chain vertices into vertices of one finite triangle
mesh.  A simple graph path in the resulting one-skeleton is then a loop-free polygonal arc.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Concrete data carried by a broken-line witness. -/
structure BrokenLineData (U : Set Plane) where
  /-- The `n` declaration. -/
  n : ℕ
  /-- The `vertex` declaration. -/
  vertex : Fin (n + 1) → Plane
  segment_subset : ∀ i : Fin n,
    segment ℝ (vertex i.castSucc) (vertex i.succ) ⊆ U

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- The `start` declaration. -/
def start : Plane := B.vertex 0

/-- The `finish` declaration. -/
def finish : Plane := B.vertex (Fin.last B.n)

/-- An auxiliary broken line listing an arbitrary finite family of segments.  The prescribed
segments occur at the even indices; the odd indices are disposable connectors.  This is the
common-arrangement input used when several independently constructed polygonal arcs must be
viewed in one finite plane complex. -/
noncomputable def segmentFamilyChain {I : Type*} [Fintype I]
    (left right : I → Plane) : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card I
  let e := Fintype.equivFin I
  let vertex : Fin (2 * m + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then left (e.symm i) else right (e.symm i)
    else 0
  exact {
    n := 2 * m
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

/-- The even index carrying the segment labelled by `i`. -/
noncomputable def segmentFamilyIndex {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    Fin (segmentFamilyChain left right).n :=
  ⟨2 * (Fintype.equivFin I i).val, by
    change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I
    omega⟩

theorem segmentFamilyChain_vertex_even {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).vertex
        ⟨2 * (Fintype.equivFin I i).val, by
          change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I + 1
          omega⟩ = left i := by
  classical
  simp only [segmentFamilyChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * (Fintype.equivFin I i).val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * (Fintype.equivFin I i).val / 2 =
      (Fintype.equivFin I i).val := by omega
  have hi : (⟨2 * (Fintype.equivFin I i).val / 2, by omega⟩ :
      Fin (Fintype.card I)) = Fintype.equivFin I i := Fin.ext hdiv
  rw [hi, (Fintype.equivFin I).symm_apply_apply]

theorem segmentFamilyChain_vertex_odd {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).vertex
        ⟨2 * (Fintype.equivFin I i).val + 1, by
          change 2 * (Fintype.equivFin I i).val + 1 < 2 * Fintype.card I + 1
          omega⟩ = right i := by
  classical
  simp only [segmentFamilyChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * (Fintype.equivFin I i).val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * (Fintype.equivFin I i).val + 1) / 2 =
      (Fintype.equivFin I i).val := by omega
  have hi : (⟨(2 * (Fintype.equivFin I i).val + 1) / 2, by omega⟩ :
      Fin (Fintype.card I)) = Fintype.equivFin I i := Fin.ext hdiv
  rw [hi, (Fintype.equivFin I).symm_apply_apply]

@[simp] theorem segmentFamilyIndex_castSucc {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyIndex left right i).castSucc =
      ⟨2 * (Fintype.equivFin I i).val, by
        change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I + 1
        omega⟩ := rfl

@[simp] theorem segmentFamilyIndex_succ {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyIndex left right i).succ =
      ⟨2 * (Fintype.equivFin I i).val + 1, by
        change 2 * (Fintype.equivFin I i).val + 1 < 2 * Fintype.card I + 1
        omega⟩ := rfl

/-- The segment at the distinguished even index is exactly the requested family member. -/
theorem segmentFamilyChain_segment {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    segment ℝ
        ((segmentFamilyChain left right).vertex
          (segmentFamilyIndex left right i).castSucc)
        ((segmentFamilyChain left right).vertex
          (segmentFamilyIndex left right i).succ) =
      segment ℝ (left i) (right i) := by
  rw [segmentFamilyIndex_castSucc, segmentFamilyIndex_succ,
    segmentFamilyChain_vertex_even, segmentFamilyChain_vertex_odd]

theorem exists_data_of_joined {a b : Plane} (h : JoinedByBrokenLine U a b) :
    ∃ B : BrokenLineData U, B.start = a ∧ B.finish = b := by
  obtain ⟨n, v, hv0, hvlast, hvseg⟩ := h
  exact ⟨⟨n, v, hvseg⟩, hv0, hvlast⟩

/-- The affine functional whose zero set contains the line through `a` and `b`. -/
noncomputable def segmentLine (a b : Plane) : Plane →ᵃ[ℝ] ℝ :=
  (b 1 - a 1) • cartesianX - (b 0 - a 0) • cartesianY -
    AffineMap.const ℝ Plane ((b 1 - a 1) * a 0 - (b 0 - a 0) * a 1)

@[simp] theorem segmentLine_apply_left (a b : Plane) : segmentLine a b a = 0 := by
  simp [segmentLine]

@[simp] theorem segmentLine_apply_right (a b : Plane) : segmentLine a b b = 0 := by
  simp [segmentLine]
  ring

theorem segmentLine_eq_zero_of_mem_segment (a b : Plane) {x : Plane}
    (hx : x ∈ segment ℝ a b) : segmentLine a b x = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨t, -, rfl⟩ := hx
  simp [segmentLine]
  ring

/-- A point on the supporting line of a nondegenerate segment belongs to the segment exactly when
its coordinates lie between the endpoint coordinates.  Both coordinate hypotheses make the
statement symmetric and avoid selecting a preferred nonconstant coordinate in its interface. -/
theorem mem_segment_of_segmentLine_eq_zero {a b x : Plane} (hab : a ≠ b)
    (hline : segmentLine a b x = 0)
    (hx0 : x 0 ∈ Set.uIcc (a 0) (b 0))
    (hx1 : x 1 ∈ Set.uIcc (a 1) (b 1)) : x ∈ segment ℝ a b := by
  have hcoord : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra h
    push Not at h
    apply hab
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  rw [segment_eq_image']
  rcases hcoord with h0 | h1
  · let t : ℝ := (x 0 - a 0) / (b 0 - a 0)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_uIcc] at hx0
      rcases hx0 with hx0 | hx0
      · have hab0 : a 0 < b 0 := lt_of_le_of_ne (hx0.1.trans hx0.2) h0
        have hden : 0 < b 0 - a 0 := by linarith
        constructor
        · exact div_nonneg (by linarith) hden.le
        · exact (div_le_one hden).mpr (by linarith)
      · have hden : b 0 - a 0 < 0 := by
          have hba0 : b 0 < a 0 := lt_of_le_of_ne (hx0.1.trans hx0.2) h0.symm
          linarith
        constructor
        · exact div_nonneg_of_nonpos (by linarith) hden.le
        · exact (div_le_one_of_neg hden).mpr (by linarith)
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · dsimp [t]
      field_simp [sub_ne_zero.mpr h0.symm]
      ring
    · dsimp [t]
      simp [segmentLine] at hline
      field_simp [sub_ne_zero.mpr h0.symm]
      nlinarith
  · let t : ℝ := (x 1 - a 1) / (b 1 - a 1)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_uIcc] at hx1
      rcases hx1 with hx1 | hx1
      · have hab1 : a 1 < b 1 := lt_of_le_of_ne (hx1.1.trans hx1.2) h1
        have hden : 0 < b 1 - a 1 := by linarith
        constructor
        · exact div_nonneg (by linarith) hden.le
        · exact (div_le_one hden).mpr (by linarith)
      · have hden : b 1 - a 1 < 0 := by
          have hba1 : b 1 < a 1 := lt_of_le_of_ne (hx1.1.trans hx1.2) h1.symm
          linarith
        constructor
        · exact div_nonneg_of_nonpos (by linarith) hden.le
        · exact (div_le_one_of_neg hden).mpr (by linarith)
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · dsimp [t]
      simp [segmentLine] at hline
      field_simp [sub_ne_zero.mpr h1.symm]
      nlinarith
    · dsimp [t]
      field_simp [sub_ne_zero.mpr h1.symm]
      ring

/-- The `verticalLine` declaration. -/
noncomputable def verticalLine (p : Plane) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - AffineMap.const ℝ Plane (p 0)

/-- The `horizontalLine` declaration. -/
noncomputable def horizontalLine (p : Plane) : Plane →ᵃ[ℝ] ℝ :=
  cartesianY - AffineMap.const ℝ Plane (p 1)

@[simp] theorem verticalLine_apply_self (p : Plane) : verticalLine p p = 0 := by
  simp [verticalLine]

@[simp] theorem horizontalLine_apply_self (p : Plane) : horizontalLine p p = 0 := by
  simp [horizontalLine]

/-- Supporting lines of the chain segments. -/
noncomputable def segmentLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (Fin B.n)).toList.map fun i =>
    segmentLine (B.vertex i.castSucc) (B.vertex i.succ)

/-- Coordinate lines force every chain vertex to become an arrangement vertex, including at a
collinear turn or a degenerate segment. -/
noncomputable def vertexLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (Fin (B.n + 1))).toList.flatMap fun i =>
    [verticalLine (B.vertex i), horizontalLine (B.vertex i)]

/-- The `arrangementLines` declaration. -/
noncomputable def arrangementLines : List (Plane →ᵃ[ℝ] ℝ) :=
  B.segmentLines ++ B.vertexLines

/-- A positive radius containing every chain vertex. -/
noncomputable def enclosingRadius : ℝ :=
  1 + ∑ i, ‖B.vertex i‖

theorem enclosingRadius_pos : 0 < B.enclosingRadius := by
  unfold enclosingRadius
  have hsum : 0 ≤ ∑ i, ‖B.vertex i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

theorem vertex_mem_enclosingBall (i : Fin (B.n + 1)) :
    B.vertex i ∈ Metric.closedBall (0 : Plane) B.enclosingRadius := by
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold enclosingRadius
  have hi : ‖B.vertex i‖ ≤ ∑ j, ‖B.vertex j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

theorem segment_subset_enclosingBall (i : Fin B.n) :
    segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) ⊆
      Metric.closedBall (0 : Plane) B.enclosingRadius :=
  (convex_closedBall (0 : Plane) B.enclosingRadius).segment_subset
    (B.vertex_mem_enclosingBall i.castSucc) (B.vertex_mem_enclosingBall i.succ)

/-- The `enclosingMesh` declaration. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (PolygonalCircle.enclosingTriangleVertices B.enclosingRadius)
    (PolygonalCircle.enclosingTriangleVertices_affineIndependent B.enclosingRadius_pos)

/-- The finite line arrangement resolving every segment crossing and chain vertex. -/
noncomputable def arrangementMesh : TriangleMesh :=
  B.enclosingMesh.refineByLines B.arrangementLines

theorem arrangementMesh_support :
    B.arrangementMesh.toPlaneComplex.support =
      convexHull ℝ (Set.range
        (PolygonalCircle.enclosingTriangleVertices B.enclosingRadius)) := by
  rw [arrangementMesh, TriangleMesh.refineByLines_support, enclosingMesh,
    TriangleMesh.single_support]

theorem segment_subset_arrangementMesh_support (i : Fin B.n) :
    segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) ⊆
      B.arrangementMesh.toPlaneComplex.support := by
  rw [B.arrangementMesh_support]
  exact (B.segment_subset_enclosingBall i).trans
    (PolygonalCircle.closedBall_subset_enclosingTriangle B.enclosingRadius_pos)

theorem segmentLine_mem_arrangementLines (i : Fin B.n) :
    segmentLine (B.vertex i.castSucc) (B.vertex i.succ) ∈ B.arrangementLines := by
  simp [arrangementLines, segmentLines]

theorem verticalLine_mem_arrangementLines (i : Fin (B.n + 1)) :
    verticalLine (B.vertex i) ∈ B.arrangementLines := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨i, by simp, by simp⟩

theorem horizontalLine_mem_arrangementLines (i : Fin (B.n + 1)) :
    horizontalLine (B.vertex i) ∈ B.arrangementLines := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨i, by simp, by simp⟩

theorem arrangementMesh_monochromatic_segmentLine (i : Fin B.n) :
    B.arrangementMesh.IsMonochromatic
      (segmentLine (B.vertex i.castSucc) (B.vertex i.succ)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.segmentLine_mem_arrangementLines i)

theorem arrangementMesh_monochromatic_verticalLine (i : Fin (B.n + 1)) :
    B.arrangementMesh.IsMonochromatic (verticalLine (B.vertex i)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.verticalLine_mem_arrangementLines i)

theorem arrangementMesh_monochromatic_horizontalLine (i : Fin (B.n + 1)) :
    B.arrangementMesh.IsMonochromatic (horizontalLine (B.vertex i)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.horizontalLine_mem_arrangementLines i)

end BrokenLineData

namespace TriangleMesh

variable (M : TriangleMesh)

/-- In a triangulation monochromatic for an affine functional, every point of its zero set lies
in a face all of whose vertices are zero. -/
theorem exists_zero_face_of_mem_support {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {x : Plane} (hx : x ∈ M.toPlaneComplex.support)
    (hfx : f x = 0) :
    ∃ s ∈ M.toPlaneComplex.simplexes,
      x ∈ M.toPlaneComplex.cellCarrier s ∧ ∀ v ∈ s, f (M.position v) = 0 := by
  rw [M.toPlaneComplex_support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨w, hwsupp, hw0, hw1, hweval⟩ :=
    M.toPlaneComplex.exists_weights_of_mem_cellCarrier hxt
  change M.Vertex → ℝ at w
  change ∀ v : M.Vertex, 0 ≤ w v at hw0
  change (∑ v : M.Vertex, w v) = 1 at hw1
  change (∑ v : M.Vertex, w v • M.position v) = x at hweval
  have hsum : ∑ v ∈ t, w v = 1 := by
    exact (Finset.sum_subset (Finset.subset_univ t)
      (fun v _ hv => hwsupp v hv)).trans hw1
  have hfeval : ∑ v ∈ t, w v * f (M.position v) = 0 := by
    have hcomb : t.affineCombination ℝ M.position w = x := by
      rw [t.affineCombination_eq_linear_combination M.position w hsum]
      exact (Finset.sum_subset (Finset.subset_univ t)
        (fun v _ hv => by rw [hwsupp v hv, zero_smul])).trans hweval
    have hmap := t.map_affineCombination M.position w hsum f
    rw [hcomb, hfx] at hmap
    simpa [Finset.affineCombination_eq_linear_combination, hsum] using hmap.symm
  let s : Finset M.Vertex := t.filter fun v => f (M.position v) = 0
  have hzero : ∀ v ∈ t, v ∉ s → w v = 0 := by
    intro v hvt hvs
    have hfv : f (M.position v) ≠ 0 := by simpa [s, hvt] using hvs
    rcases hmono t ht with hpos | hneg
    · have hterm : w v * f (M.position v) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (s := t) (f := fun u =>
          w u * f (M.position u)) (fun u hu => mul_nonneg (hw0 u) (hpos u hu))).mp hfeval v hvt
      exact (mul_eq_zero.mp hterm).resolve_right hfv
    · have hterm : w v * (-f (M.position v)) = 0 := by
        have hsumNeg : ∑ u ∈ t, w u * (-f (M.position u)) = 0 := by
          calc
            ∑ u ∈ t, w u * (-f (M.position u)) =
                -(∑ u ∈ t, w u * f (M.position u)) := by
              simp only [mul_neg, Finset.sum_neg_distrib]
            _ = 0 := by rw [hfeval]; simp
        apply (Finset.sum_eq_zero_iff_of_nonneg (s := t) (f := fun u =>
          w u * (-f (M.position u))) (fun u hu =>
            mul_nonneg (hw0 u) (neg_nonneg.mpr (hneg u hu)))).mp hsumNeg v hvt
      exact (mul_eq_zero.mp hterm).resolve_right (neg_ne_zero.mpr hfv)
  have hsne : s.Nonempty := by
    by_contra hs
    have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hwAll : ∀ v, w v = 0 := by
      intro v
      by_cases hvt : v ∈ t
      · exact hzero v hvt (by simp [hsEmpty])
      · exact hwsupp v hvt
    have : (∑ v, w v) = 0 := by simp [hwAll]
    exact one_ne_zero (hw1.symm.trans this)
  have hst : s ⊆ t := Finset.filter_subset _ _
  have hsface : s ∈ M.toPlaneComplex.simplexes :=
    M.toPlaneComplex.down_closed t
      (M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
        t, ht, subset_rfl⟩) s hst hsne
  refine ⟨s, hsface, ?_, ?_⟩
  · rw [← hweval]
    apply M.toPlaneComplex.baryEval_mem_cellCarrier
    · intro v hvs
      by_cases hvt : v ∈ t
      · exact hzero v hvt hvs
      · exact hwsupp v hvt
    · exact hw0
    · exact hw1
  · intro v hv
    exact (Finset.mem_filter.mp hv).2

/-- Two monochromatic coordinate lines through a supported point force that point to occur as an
actual mesh vertex. -/
theorem exists_vertex_position_eq_of_monochromatic_coordinates (p : Plane)
    (hp : p ∈ M.toPlaneComplex.support)
    (hx : M.IsMonochromatic (BrokenLineData.verticalLine p))
    (hy : M.IsMonochromatic (BrokenLineData.horizontalLine p)) :
    ∃ v : M.Vertex, M.toPlaneComplex.position v = p ∧
      ({v} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes := by
  obtain ⟨s, hs, hps, hs0⟩ := M.exists_zero_face_of_mem_support hx hp
    (BrokenLineData.verticalLine_apply_self p)
  obtain ⟨t, ht, hpt, ht0⟩ := M.exists_zero_face_of_mem_support hy hp
    (BrokenLineData.horizontalLine_apply_self p)
  have hpInter : p ∈ M.toPlaneComplex.cellCarrier (s ∩ t) := by
    have hface := M.toPlaneComplex.face_inter s hs t ht
    have hmem : p ∈ M.toPlaneComplex.cellCarrier s ∩
        M.toPlaneComplex.cellCarrier t := ⟨hps, hpt⟩
    change p ∈ convexHull ℝ
        (M.toPlaneComplex.position '' (s : Set M.toPlaneComplex.Vertex)) ∩
      convexHull ℝ (M.toPlaneComplex.position '' (t : Set M.toPlaneComplex.Vertex)) at hmem
    rw [hface] at hmem
    exact hmem
  have hne : (s ∩ t).Nonempty := by
    by_contra h
    have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, PlaneComplex.cellCarrier] at hpInter
    simp at hpInter
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, plane_ext ?_ ?_, ?_⟩
  · have hv0 := hs0 v (Finset.mem_of_mem_inter_left hv)
    change M.toPlaneComplex.position v 0 - p 0 = 0 at hv0
    exact sub_eq_zero.mp hv0
  · have hv1 := ht0 v (Finset.mem_of_mem_inter_right hv)
    change M.toPlaneComplex.position v 1 - p 1 = 0 at hv1
    exact sub_eq_zero.mp hv1
  · exact M.toPlaneComplex.down_closed s hs {v}
      (by
        intro w hw
        simp only [Finset.mem_singleton] at hw
        subst w
        exact Finset.mem_of_mem_inter_left hv)
      (Finset.singleton_nonempty _)

theorem nonneg_on_face_of_monochromatic_of_pos {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {s : Finset M.Vertex}
    (hs : s ∈ M.toPlaneComplex.simplexes) {x : Plane}
    (hxs : x ∈ M.toPlaneComplex.cellCarrier s) (hfx : 0 < f x) :
    ∀ v ∈ s, 0 ≤ f (M.position v) := by
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  rcases hmono t ht with hnonneg | hnonpos
  · exact fun v hv => hnonneg v (hst hv)
  · exfalso
    have hxnonpos : f x ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage f) hxs
      rintro y ⟨v, hv, rfl⟩
      exact hnonpos v (hst hv)
    linarith

theorem nonpos_on_face_of_monochromatic_of_neg {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {s : Finset M.Vertex}
    (hs : s ∈ M.toPlaneComplex.simplexes) {x : Plane}
    (hxs : x ∈ M.toPlaneComplex.cellCarrier s) (hfx : f x < 0) :
    ∀ v ∈ s, f (M.position v) ≤ 0 := by
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  rcases hmono t ht with hnonneg | hnonpos
  · exfalso
    have hxnonneg : 0 ≤ f x := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage f) hxs
      rintro y ⟨v, hv, rfl⟩
      exact hnonneg v (hst hv)
    linarith
  · exact fun v hv => hnonpos v (hst hv)

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- An affine-independent face whose vertices lie on one segment has at most two vertices. -/
theorem card_le_two_of_vertices_mem_segment {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) {a b : Plane}
    (hseg : ∀ v ∈ s, K.position v ∈ segment ℝ a b) : s.card ≤ 2 := by
  classical
  let A : Finset Plane := s.image K.position
  have hAI : AffineIndependent ℝ ((↑) : A → Plane) := by
    apply affineIndependent_finset_coe (K.affineIndependent s hs)
    intro x hx
    obtain ⟨v, hvs, hvx⟩ := Finset.mem_image.mp hx
    exact ⟨⟨v, hvs⟩, hvx⟩
  have hspan : (A : Set Plane) ⊆
      affineSpan ℝ (({a, b} : Finset Plane) : Set Plane) := by
    intro x hx
    obtain ⟨v, hvs, hvx⟩ := Finset.mem_image.mp hx
    rw [← hvx]
    apply convexHull_subset_affineSpan
      (({a, b} : Finset Plane) : Set Plane)
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      hseg v hvs
  have hcard := hAI.card_le_card_of_subset_affineSpan (t := {a, b}) hspan
  calc
    s.card = A.card := by
      symm
      exact Finset.card_image_iff.mpr K.position_injective.injOn
    _ ≤ ({a, b} : Finset Plane).card := hcard
    _ ≤ 2 := Finset.card_le_two

/-- A point in a nonempty face of cardinality at most two lies on a segment joining two of that
face's vertices (the two vertices may coincide for a zero-face). -/
theorem exists_vertex_pair_segment_of_mem_cellCarrier {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (hcard : s.card ≤ 2) {x : Plane}
    (hx : x ∈ K.cellCarrier s) :
    ∃ v w : K.Vertex, v ∈ s ∧ w ∈ s ∧
      x ∈ segment ℝ (K.position v) (K.position w) := by
  have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    refine ⟨v, v, by simp, by simp, ?_⟩
    simpa [PlaneComplex.cellCarrier, segment_same] using hx
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp htwo
    refine ⟨v, w, by simp, by simp, ?_⟩
    rw [PlaneComplex.cellCarrier] at hx
    have himage : K.position ''
        (({v, w} : Finset K.Vertex) : Set K.Vertex) =
        {K.position v, K.position w} := by
      ext y
      simp [eq_comm]
    rwa [himage, convexHull_pair] at hx

/-- The graph formed by the one-dimensional faces of a plane complex. -/
def vertexGraph : SimpleGraph K.Vertex where
  Adj v w := v ≠ w ∧ ({v, w} : Finset K.Vertex) ∈ K.simplexes
  symm := ⟨by
    rintro v w ⟨hvw, hedge⟩
    exact ⟨hvw.symm, by simpa [Finset.pair_comm] using hedge⟩⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

theorem vertexGraph_adj_iff {v w : K.Vertex} :
    K.vertexGraph.Adj v w ↔
      v ≠ w ∧ ({v, w} : Finset K.Vertex) ∈ K.simplexes := Iff.rfl

/-- Every vertex visited by a one-skeleton walk is geometrically supported, provided the final
vertex is an actual zero-face.  All earlier vertices occur in an edge of the walk. -/
theorem position_mem_support_of_mem_walk {u v w : K.Vertex}
    (p : K.vertexGraph.Walk u v)
    (hv : ({v} : Finset K.Vertex) ∈ K.simplexes)
    (hw : w ∈ p.support) : K.position w ∈ K.support := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mp hw with hwv | ⟨e, he, hwe⟩
  · rw [hwv]
    exact K.cellCarrier_subset_support hv
      (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩)
  · induction e using Sym2.inductionOn with
    | hf a b =>
        rcases Sym2.mem_iff.mp hwe with hwa | hwb
        · rw [hwa]
          have hab := p.adj_of_mem_edges he
          exact K.cellCarrier_subset_support hab.2
            (subset_convexHull ℝ _ ⟨a, by simp, rfl⟩)
        · rw [hwb]
          have hab := p.adj_of_mem_edges he
          exact K.cellCarrier_subset_support hab.2
            (subset_convexHull ℝ _ ⟨b, by simp, rfl⟩)

/-- The induced subcomplex on the vertices satisfying `p`.  Vertices outside `p` remain in the
ambient finite type but occur in no face; `PlaneComplex.active` can remove them when desired. -/
noncomputable def inducedBy (p : K.Vertex → Prop) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => ∀ v ∈ s, p v
    nonempty_of_mem := by
      intro s hs
      exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsp⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      exact ⟨K.down_closed s hsK t hts ht, fun v hv => hsp v (hts hv)⟩
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem inducedBy_position (p : K.Vertex → Prop) :
    (K.inducedBy p).position = K.position := rfl

@[simp] theorem inducedBy_cellCarrier (p : K.Vertex → Prop) (s : Finset K.Vertex) :
    (K.inducedBy p).cellCarrier s = K.cellCarrier s := rfl

theorem mem_inducedBy_simplexes_iff (p : K.Vertex → Prop) {s : Finset K.Vertex} :
    s ∈ (K.inducedBy p).simplexes ↔ s ∈ K.simplexes ∧ ∀ v ∈ s, p v := by
  classical
  change s ∈ K.simplexes.filter (fun t => ∀ v ∈ t, p v) ↔ _
  exact Finset.mem_filter

theorem inducedBy_support_subset {C : Set Plane} (hC : Convex ℝ C)
    (p : K.Vertex → Prop) (hp : ∀ v, p v → K.position v ∈ C) :
    (K.inducedBy p).support ⊆ C := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  apply convexHull_min _ hC hxs
  rintro y ⟨v, hv, rfl⟩
  exact hp v (((K.mem_inducedBy_simplexes_iff p).mp hs).2 v hv)

theorem inducedBy_support_eq {C : Set Plane} (hC : Convex ℝ C)
    (p : K.Vertex → Prop) (hp : ∀ v, p v → K.position v ∈ C)
    (hcover : ∀ x ∈ C, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ ∀ v ∈ s, p v) :
    (K.inducedBy p).support = C := by
  apply Set.Subset.antisymm (K.inducedBy_support_subset hC p hp)
  intro x hx
  obtain ⟨s, hs, hxs, hsp⟩ := hcover x hx
  rw [PlaneComplex.support]
  exact Set.mem_iUnion₂.mpr
    ⟨s, (K.mem_inducedBy_simplexes_iff p).mpr ⟨hs, hsp⟩, hxs⟩

/-- The subcomplex consisting of exactly those faces whose whole geometric carrier lies in `C`.
Unlike `inducedBy`, this is appropriate when `C` is a nonconvex polygonal set. -/
noncomputable def restrictedTo (C : Set Plane) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => K.cellCarrier s ⊆ C
    nonempty_of_mem := by
      intro s hs
      exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsC⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨K.down_closed s hsK t hts ht, ?_⟩
      exact (convexHull_mono (Set.image_mono hts)).trans hsC
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem restrictedTo_position (C : Set Plane) :
    (K.restrictedTo C).position = K.position := rfl

@[simp] theorem restrictedTo_cellCarrier (C : Set Plane) (s : Finset K.Vertex) :
    (K.restrictedTo C).cellCarrier s = K.cellCarrier s := rfl

theorem mem_restrictedTo_simplexes_iff (C : Set Plane) {s : Finset K.Vertex} :
    s ∈ (K.restrictedTo C).simplexes ↔ s ∈ K.simplexes ∧ K.cellCarrier s ⊆ C := by
  classical
  change s ∈ K.simplexes.filter (fun t => K.cellCarrier t ⊆ C) ↔ _
  exact Finset.mem_filter

theorem restrictedTo_support_subset (C : Set Plane) :
    (K.restrictedTo C).support ⊆ C := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact ((K.mem_restrictedTo_simplexes_iff C).mp hs).2 hxs

theorem restrictedTo_support_eq (C : Set Plane)
    (hcover : ∀ x ∈ C, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ K.cellCarrier s ⊆ C) :
    (K.restrictedTo C).support = C := by
  apply Set.Subset.antisymm (K.restrictedTo_support_subset C)
  intro x hx
  obtain ⟨s, hs, hxs, hsC⟩ := hcover x hx
  rw [PlaneComplex.support]
  exact Set.mem_iUnion₂.mpr
    ⟨s, (K.mem_restrictedTo_simplexes_iff C).mpr ⟨hs, hsC⟩, hxs⟩

/-- All vertices of one simplex lie in one reachability class of the vertex graph. -/
theorem vertexGraph_reachable_of_mem_simplex {s : Finset K.Vertex} (hs : s ∈ K.simplexes)
    {v w : K.Vertex} (hv : v ∈ s) (hw : w ∈ s) : K.vertexGraph.Reachable v w := by
  by_cases hvw : v = w
  · simp [hvw]
  · apply SimpleGraph.Adj.reachable
    rw [K.vertexGraph_adj_iff]
    refine ⟨hvw, K.down_closed s hs {v, w} ?_ (by simp)⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hw

/-- If the support of a finite plane complex is connected, then any two vertices which actually
occur as zero-faces are joined by a path in its one-skeleton. -/
theorem vertexGraph_reachable_of_isPreconnected
    (hconn : IsPreconnected K.support) {u v : K.Vertex}
    (hu : ({u} : Finset K.Vertex) ∈ K.simplexes)
    (hv : ({v} : Finset K.Vertex) ∈ K.simplexes) :
    K.vertexGraph.Reachable u v := by
  classical
  by_contra huv
  let R : K.Vertex → Prop := fun w => K.vertexGraph.Reachable u w
  let leftFaces := K.simplexes.filter fun s => ∃ w ∈ s, R w
  let rightFaces := K.simplexes.filter fun s => ∃ w ∈ s, ¬R w
  let A : Set Plane := ⋃ s ∈ leftFaces, K.cellCarrier s
  let B : Set Plane := ⋃ s ∈ rightFaces, K.cellCarrier s
  have hface_uniform (s : Finset K.Vertex) (hs : s ∈ K.simplexes) :
      (∀ w ∈ s, R w) ∨ (∀ w ∈ s, ¬R w) := by
    obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
    by_cases hRw : R w
    · left
      intro z hz
      exact hRw.trans (K.vertexGraph_reachable_of_mem_simplex hs hw hz)
    · right
      intro z hz hRz
      exact hRw (hRz.trans (K.vertexGraph_reachable_of_mem_simplex hs hz hw))
  have hclosedA : IsClosed A := by
    apply isClosed_biUnion_finset
    intro s hs
    exact K.isCompact_cellCarrier s |>.isClosed
  have hclosedB : IsClosed B := by
    apply isClosed_biUnion_finset
    intro s hs
    exact K.isCompact_cellCarrier s |>.isClosed
  have hcover : K.support ⊆ A ∪ B := by
    intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rcases hface_uniform s hs with hleft | hright
    · left
      obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
      exact Set.mem_iUnion₂.mpr
        ⟨s, Finset.mem_filter.mpr ⟨hs, w, hw, hleft w hw⟩, hxs⟩
    · right
      obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
      exact Set.mem_iUnion₂.mpr
        ⟨s, Finset.mem_filter.mpr ⟨hs, w, hw, hright w hw⟩, hxs⟩
  have hdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨s, hsleft, hxs⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨t, htright, hxt⟩ := Set.mem_iUnion₂.mp hxB
    obtain ⟨hs, w, hws, hRw⟩ := Finset.mem_filter.mp hsleft
    obtain ⟨ht, z, hzt, hRz⟩ := Finset.mem_filter.mp htright
    have hxinter : x ∈ K.cellCarrier (s ∩ t) := by
      have hinter : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
        simpa only [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
      rw [← hinter]
      exact ⟨hxs, hxt⟩
    have hst : (s ∩ t).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, PlaneComplex.cellCarrier] at hxinter
      simp at hxinter
    obtain ⟨q, hq⟩ := hst
    have hRq : R q := hRw.trans
      (K.vertexGraph_reachable_of_mem_simplex hs hws (Finset.mem_of_mem_inter_left hq))
    have hnRq : ¬R q := fun h => hRz
      (h.trans (K.vertexGraph_reachable_of_mem_simplex ht
        (Finset.mem_of_mem_inter_right hq) hzt))
    exact hnRq hRq
  have hleftNonempty : (K.support ∩ A).Nonempty := by
    refine ⟨K.position u, ?_, ?_⟩
    · exact K.cellCarrier_subset_support hu
        (subset_convexHull ℝ _ ⟨u, by simp, rfl⟩)
    · exact Set.mem_iUnion₂.mpr ⟨{u}, Finset.mem_filter.mpr
        ⟨hu, u, by simp, SimpleGraph.Reachable.refl u⟩,
          subset_convexHull ℝ _ ⟨u, by simp, rfl⟩⟩
  have hrightNonempty : (K.support ∩ B).Nonempty := by
    refine ⟨K.position v, ?_, ?_⟩
    · exact K.cellCarrier_subset_support hv
        (subset_convexHull ℝ _ ⟨v, by simp, rfl⟩)
    · exact Set.mem_iUnion₂.mpr ⟨{v}, Finset.mem_filter.mpr
        ⟨hv, v, by simp, huv⟩,
          subset_convexHull ℝ _ ⟨v, by simp, rfl⟩⟩
  have hinter := (isPreconnected_closed_iff.mp hconn) A B hclosedA hclosedB hcover
    hleftNonempty hrightNonempty
  obtain ⟨x, -, hxA, hxB⟩ := hinter
  exact Set.disjoint_left.mp hdisjoint hxA hxB

end PlaneComplex

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- Every original chain vertex is a vertex of the line-arrangement mesh. -/
theorem exists_arrangementVertex_position_eq (i : Fin (B.n + 1)) :
    ∃ v : B.arrangementMesh.Vertex,
      B.arrangementMesh.toPlaneComplex.position v = B.vertex i ∧
        ({v} : Finset B.arrangementMesh.Vertex) ∈
          B.arrangementMesh.toPlaneComplex.simplexes := by
  let M := B.arrangementMesh
  have hxSupport : B.vertex i ∈ M.toPlaneComplex.support := by
    rw [B.arrangementMesh_support]
    exact PolygonalCircle.closedBall_subset_enclosingTriangle B.enclosingRadius_pos
      (B.vertex_mem_enclosingBall i)
  exact M.exists_vertex_position_eq_of_monochromatic_coordinates (B.vertex i) hxSupport
    (B.arrangementMesh_monochromatic_verticalLine i)
    (B.arrangementMesh_monochromatic_horizontalLine i)

/-- Every point of an original nondegenerate chain segment lies in an arrangement face whose
vertices all lie on that segment. -/
theorem exists_face_on_segment (i : Fin B.n) {x : Plane}
    (hx : x ∈ segment ℝ (B.vertex i.castSucc) (B.vertex i.succ)) :
    ∃ s ∈ B.arrangementMesh.toPlaneComplex.simplexes,
      x ∈ B.arrangementMesh.toPlaneComplex.cellCarrier s ∧
        ∀ v ∈ s, B.arrangementMesh.toPlaneComplex.position v ∈
          segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  let a := B.vertex i.castSucc
  let b := B.vertex i.succ
  let M := B.arrangementMesh
  change x ∈ segment ℝ a b at hx
  by_cases hab : a = b
  · have hxa : x = a := by
      rw [hab, segment_same, Set.mem_singleton_iff] at hx
      exact hx.trans hab.symm
    obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.castSucc
    refine ⟨{v}, hvface, ?_, ?_⟩
    · rw [hxa]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
    · intro w hw
      have hwv : w = v := Finset.mem_singleton.mp hw
      subst w
      change M.toPlaneComplex.position v ∈ segment ℝ a b
      rw [hvpos]
      exact left_mem_segment ℝ a b
  · by_cases hxa : x = a
    · obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.castSucc
      refine ⟨{v}, hvface, ?_, ?_⟩
      · rw [hxa]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
      · intro w hw
        have hwv : w = v := Finset.mem_singleton.mp hw
        subst w
        change M.toPlaneComplex.position v ∈ segment ℝ a b
        rw [hvpos]
        exact left_mem_segment ℝ a b
    · by_cases hxb : x = b
      · obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.succ
        refine ⟨{v}, hvface, ?_, ?_⟩
        · rw [hxb]
          exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
        · intro w hw
          have hwv : w = v := Finset.mem_singleton.mp hw
          subst w
          change M.toPlaneComplex.position v ∈ segment ℝ a b
          rw [hvpos]
          exact right_mem_segment ℝ a b
      · have hxSupport : x ∈ M.toPlaneComplex.support :=
          B.segment_subset_arrangementMesh_support i hx
        obtain ⟨s, hs, hxs, hsline⟩ := M.exists_zero_face_of_mem_support
          (B.arrangementMesh_monochromatic_segmentLine i) hxSupport
          (segmentLine_eq_zero_of_mem_segment a b hx)
        have ht : ∃ t ∈ Set.Ioo (0 : ℝ) 1, AffineMap.lineMap a b t = x := by
          rw [segment_eq_image_lineMap] at hx
          obtain ⟨t, ht, htx⟩ := hx
          refine ⟨t, ⟨?_, ?_⟩, htx⟩
          · apply lt_of_le_of_ne ht.1
            intro hzero
            apply hxa
            rw [← htx, ← hzero]
            simp
          · apply lt_of_le_of_ne ht.2
            intro hone
            apply hxb
            rw [← htx, hone]
            simp
        obtain ⟨t, ht, htx⟩ := ht
        have hxcoord0 : x 0 = (1 - t) * a 0 + t * b 0 := by
          rw [← htx]
          simp [AffineMap.lineMap_apply_module]
        have hxcoord1 : x 1 = (1 - t) * a 1 + t * b 1 := by
          rw [← htx]
          simp [AffineMap.lineMap_apply_module]
        refine ⟨s, hs, hxs, ?_⟩
        intro v hv
        have hvline := hsline v hv
        change segmentLine a b (M.toPlaneComplex.position v) = 0 at hvline
        apply mem_segment_of_segmentLine_eq_zero hab hvline
        · by_cases h0 : a 0 = b 0
          · rw [h0, Set.uIcc_self]
            have h1 : a 1 ≠ b 1 := by
              intro h1
              apply hab
              ext k
              fin_cases k
              · exact h0
              · exact h1
            have hprod : (b 1 - a 1) * (M.toPlaneComplex.position v 0 - a 0) = 0 := by
              simp only [segmentLine, Fin.isValue, AffineMap.coe_sub, AffineMap.coe_smul,
                AffineMap.coe_const, Pi.sub_apply, Pi.smul_apply, cartesianX_apply, smul_eq_mul,
                cartesianY_apply, Function.const_apply] at hvline
              rw [h0] at hvline
              ring_nf at hvline ⊢
              rw [h0]
              exact hvline
            calc
              M.toPlaneComplex.position v 0 = a 0 := sub_eq_zero.mp
                ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h1.symm))
              _ = b 0 := h0
          · rcases lt_or_gt_of_ne h0 with hlt | hgt
            · rw [Set.uIcc_of_le hlt.le, Set.mem_Icc]
              have hxlo : 0 < verticalLine a x := by
                change 0 < x 0 - a 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hxhi : verticalLine b x < 0 := by
                change x 0 - b 0 < 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_verticalLine i.castSucc) hs hxs hxlo v hv
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_verticalLine i.succ) hs hxs hxhi v hv
              change 0 ≤ M.toPlaneComplex.position v 0 - a 0 at hlo
              change M.toPlaneComplex.position v 0 - b 0 ≤ 0 at hhi
              constructor <;> linarith
            · rw [Set.uIcc_of_ge hgt.le, Set.mem_Icc]
              have hxhi : verticalLine a x < 0 := by
                change x 0 - a 0 < 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hxlo : 0 < verticalLine b x := by
                change 0 < x 0 - b 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_verticalLine i.castSucc) hs hxs hxhi v hv
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_verticalLine i.succ) hs hxs hxlo v hv
              change M.toPlaneComplex.position v 0 - a 0 ≤ 0 at hhi
              change 0 ≤ M.toPlaneComplex.position v 0 - b 0 at hlo
              constructor <;> linarith
        · by_cases h1 : a 1 = b 1
          · rw [h1, Set.uIcc_self]
            have h0 : a 0 ≠ b 0 := by
              intro h0
              apply hab
              ext k
              fin_cases k
              · exact h0
              · exact h1
            have hprod : (b 0 - a 0) * (M.toPlaneComplex.position v 1 - a 1) = 0 := by
              simp only [segmentLine, Fin.isValue, AffineMap.coe_sub, AffineMap.coe_smul,
                AffineMap.coe_const, Pi.sub_apply, Pi.smul_apply, cartesianX_apply, smul_eq_mul,
                cartesianY_apply, Function.const_apply] at hvline
              rw [h1] at hvline
              ring_nf at hvline ⊢
              rw [h1]
              linarith
            calc
              M.toPlaneComplex.position v 1 = a 1 := sub_eq_zero.mp
                ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h0.symm))
              _ = b 1 := h1
          · rcases lt_or_gt_of_ne h1 with hlt | hgt
            · rw [Set.uIcc_of_le hlt.le, Set.mem_Icc]
              have hxlo : 0 < horizontalLine a x := by
                change 0 < x 1 - a 1
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hxhi : horizontalLine b x < 0 := by
                change x 1 - b 1 < 0
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_horizontalLine i.castSucc) hs hxs hxlo v hv
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_horizontalLine i.succ) hs hxs hxhi v hv
              change 0 ≤ M.toPlaneComplex.position v 1 - a 1 at hlo
              change M.toPlaneComplex.position v 1 - b 1 ≤ 0 at hhi
              constructor <;> linarith
            · rw [Set.uIcc_of_ge hgt.le, Set.mem_Icc]
              have hxhi : horizontalLine a x < 0 := by
                change x 1 - a 1 < 0
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hxlo : 0 < horizontalLine b x := by
                change 0 < x 1 - b 1
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_horizontalLine i.castSucc) hs hxs hxhi v hv
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_horizontalLine i.succ) hs hxs hxlo v hv
              change M.toPlaneComplex.position v 1 - a 1 ≤ 0 at hhi
              change 0 ≤ M.toPlaneComplex.position v 1 - b 1 at hlo
              constructor <;> linarith

/-- The common arrangement of a finite segment family resolves each requested member into faces
contained in that member.  Keeping this theorem abstract in the family index prevents clients
with dependent finite index types from unfolding their entire enumeration during kernel
checking. -/
theorem exists_face_on_segmentFamily {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) {x : Plane}
    (hx : x ∈ segment ℝ (left i) (right i)) :
    ∃ s ∈ (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.simplexes,
      x ∈ (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.cellCarrier s ∧
      (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        segment ℝ (left i) (right i) := by
  let B := segmentFamilyChain left right
  let q := segmentFamilyIndex left right i
  have hsegment : segment ℝ (B.vertex q.castSucc) (B.vertex q.succ) =
      segment ℝ (left i) (right i) := segmentFamilyChain_segment left right i
  obtain ⟨s, hs, hxs, hsSegment⟩ := B.exists_face_on_segment q (hsegment.symm ▸ hx)
  refine ⟨s, hs, hxs, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hvSegment := hsSegment v hv
  rw [hsegment] at hvSegment
  exact hvSegment

/-- The geometric carrier of all listed segments of a finite broken line.  Auxiliary line
arrangements may contain many additional faces, so this is the carrier relevant to the
polygonal object itself. -/
def segmentCarrier : Set Plane :=
  ⋃ i : Fin B.n, segment ℝ (B.vertex i.castSucc) (B.vertex i.succ)

/-- The line arrangement restricted to the actual segments of a finite broken line.  This is a
canonical finite plane complex even when the listed segments cross or overlap: the ambient line
arrangement has already inserted every required intersection vertex. -/
noncomputable def carrierComplex : PlaneComplex :=
  B.arrangementMesh.toPlaneComplex.restrictToSet B.segmentCarrier

/-- The canonical complex of a broken line has exactly the union of its listed segments as
support. -/
theorem carrierComplex_support : B.carrierComplex.support = B.segmentCarrier := by
  apply Set.Subset.antisymm
  · exact B.arrangementMesh.toPlaneComplex.restrictToSet_support_subset B.segmentCarrier
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, hsSegment⟩ := B.exists_face_on_segment i hxi
    rw [PlaneComplex.support]
    refine Set.mem_iUnion₂.mpr ⟨s, ?_, hxs⟩
    apply (B.arrangementMesh.toPlaneComplex.mem_restrictToSet_simplexes_iff
      B.segmentCarrier).mpr
    refine ⟨hs, ?_⟩
    have hfaceSegment :
        B.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
          segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hfaceSegment.trans (Set.subset_iUnion (fun j : Fin B.n =>
      segment ℝ (B.vertex j.castSucc) (B.vertex j.succ)) i)

/-- A canonical arrangement vertex representing an original chain vertex. -/
noncomputable def arrangementVertex (i : Fin (B.n + 1)) :
    B.arrangementMesh.toPlaneComplex.Vertex :=
  Classical.choose (B.exists_arrangementVertex_position_eq i)

theorem arrangementVertex_position (i : Fin (B.n + 1)) :
    B.arrangementMesh.toPlaneComplex.position (B.arrangementVertex i) = B.vertex i :=
  (Classical.choose_spec (B.exists_arrangementVertex_position_eq i)).1

theorem arrangementVertex_face (i : Fin (B.n + 1)) :
    ({B.arrangementVertex i} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
      B.arrangementMesh.toPlaneComplex.simplexes :=
  (Classical.choose_spec (B.exists_arrangementVertex_position_eq i)).2

/-- The left endpoint of a listed family segment is a canonical vertex of the common
arrangement. -/
theorem segmentFamily_arrangementVertex_position_left {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
      ((segmentFamilyChain left right).arrangementVertex
        (segmentFamilyIndex left right i).castSucc) = left i := by
  rw [(segmentFamilyChain left right).arrangementVertex_position]
  exact segmentFamilyChain_vertex_even left right i

/-- The right endpoint of a listed family segment is a canonical vertex of the common
arrangement. -/
theorem segmentFamily_arrangementVertex_position_right {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
      ((segmentFamilyChain left right).arrangementVertex
        (segmentFamilyIndex left right i).succ) = right i := by
  rw [(segmentFamilyChain left right).arrangementVertex_position]
  exact segmentFamilyChain_vertex_odd left right i

/-- The part of the arrangement mesh lying wholly on one original chain segment. -/
noncomputable def segmentComplex (i : Fin B.n) : PlaneComplex :=
  B.arrangementMesh.toPlaneComplex.restrictedTo
    (segment ℝ (B.vertex i.castSucc) (B.vertex i.succ))

theorem segmentComplex_support (i : Fin B.n) :
    (B.segmentComplex i).support =
      segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsseg⟩ := B.exists_face_on_segment i hx
  refine ⟨s, hs, hxs, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  exact hsseg v hv

theorem arrangementVertex_mem_segmentComplex_left (i : Fin B.n) :
    ({B.arrangementVertex i.castSucc} : Finset (B.segmentComplex i).Vertex) ∈
      (B.segmentComplex i).simplexes := by
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face i.castSucc, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hv' : v = B.arrangementVertex i.castSucc := Finset.mem_singleton.mp hv
  subst v
  rw [B.arrangementVertex_position]
  exact left_mem_segment ℝ _ _

theorem arrangementVertex_mem_segmentComplex_right (i : Fin B.n) :
    ({B.arrangementVertex i.succ} : Finset (B.segmentComplex i).Vertex) ∈
      (B.segmentComplex i).simplexes := by
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face i.succ, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hv' : v = B.arrangementVertex i.succ := Finset.mem_singleton.mp hv
  subst v
  rw [B.arrangementVertex_position]
  exact right_mem_segment ℝ _ _

/-- The line arrangement turns every original chain segment into a path in a finite
one-skeleton. -/
theorem reachable_on_segment (i : Fin B.n) :
    (B.segmentComplex i).vertexGraph.Reachable
      (B.arrangementVertex i.castSucc) (B.arrangementVertex i.succ) := by
  apply (B.segmentComplex i).vertexGraph_reachable_of_isPreconnected
  · rw [B.segmentComplex_support]
    exact (convex_segment (B.vertex i.castSucc) (B.vertex i.succ)).isPreconnected
  · exact B.arrangementVertex_mem_segmentComplex_left i
  · exact B.arrangementVertex_mem_segmentComplex_right i

theorem exists_path_on_segment (i : Fin B.n) :
    Nonempty ((B.segmentComplex i).vertexGraph.Path
      (B.arrangementVertex i.castSucc) (B.arrangementVertex i.succ)) := by
  obtain ⟨p, hp⟩ := (B.reachable_on_segment i).exists_isPath
  exact ⟨⟨p, hp⟩⟩

/-- Arrangement edges whose geometric segments lie in the prescribed open set. -/
def inSetGraph : SimpleGraph B.arrangementMesh.toPlaneComplex.Vertex where
  Adj v w := v ≠ w ∧
    ({v, w} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
      B.arrangementMesh.toPlaneComplex.simplexes ∧
    B.arrangementMesh.toPlaneComplex.cellCarrier {v, w} ⊆ U
  symm := ⟨by
    rintro v w ⟨hvw, hedge, hU⟩
    exact ⟨hvw.symm, by simpa [Finset.pair_comm] using hedge,
      by rw [Finset.pair_comm]; exact hU⟩⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

theorem inSetGraph_adj_iff {v w : B.arrangementMesh.toPlaneComplex.Vertex} :
    B.inSetGraph.Adj v w ↔ v ≠ w ∧
      ({v, w} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
        B.arrangementMesh.toPlaneComplex.simplexes ∧
      B.arrangementMesh.toPlaneComplex.cellCarrier {v, w} ⊆ U := Iff.rfl

theorem inSetGraph_le_arrangementVertexGraph :
    B.inSetGraph ≤ B.arrangementMesh.toPlaneComplex.vertexGraph := by
  intro v w hvw
  rw [B.inSetGraph_adj_iff] at hvw
  rw [B.arrangementMesh.toPlaneComplex.vertexGraph_adj_iff]
  exact ⟨hvw.1, hvw.2.1⟩

theorem segmentVertexGraph_le_inSetGraph (i : Fin B.n) :
    (B.segmentComplex i).vertexGraph ≤
      B.inSetGraph := by
  intro v w hvw
  rw [(B.segmentComplex i).vertexGraph_adj_iff] at hvw
  erw [B.inSetGraph_adj_iff]
  obtain ⟨hedge, hsegment⟩ :=
    (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mp hvw.2
  exact ⟨hvw.1, hedge, hsegment.trans (B.segment_subset i)⟩

/-- Concatenating the segment paths gives a walk through the entire broken line; Mathlib's
loop-erasure then produces a path with the same endpoints. -/
theorem exists_arrangement_path :
    Nonempty (B.inSetGraph.Path
      (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n))) := by
  let G := B.inSetGraph
  have hwalk : ∀ k : ℕ, ∀ hk : k ≤ B.n,
      Nonempty (G.Walk (B.arrangementVertex 0)
        (B.arrangementVertex ⟨k, Nat.lt_succ_of_le hk⟩)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨SimpleGraph.Walk.nil⟩
    | succ k ih =>
        intro hk
        have hklt : k < B.n := Nat.lt_of_succ_le hk
        obtain ⟨p⟩ := ih (Nat.le_of_lt hklt)
        let i : Fin B.n := ⟨k, hklt⟩
        obtain ⟨q⟩ := B.exists_path_on_segment i
        have q' : G.Walk (B.arrangementVertex i.castSucc)
            (B.arrangementVertex i.succ) :=
          (q : (B.segmentComplex i).vertexGraph.Walk _ _).mapLe
            (B.segmentVertexGraph_le_inSetGraph i)
        have hpEnd : B.arrangementVertex ⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hklt)⟩ =
            B.arrangementVertex i.castSucc := by rfl
        have hqEnd : B.arrangementVertex i.succ =
            B.arrangementVertex ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by rfl
        rw [hpEnd] at p
        rw [← hqEnd]
        exact ⟨p.append q'⟩
  obtain ⟨p⟩ := hwalk B.n le_rfl
  have hpEnd : B.arrangementVertex ⟨B.n, Nat.lt_succ_self B.n⟩ =
      B.arrangementVertex (Fin.last B.n) := by rfl
  rw [hpEnd] at p
  exact ⟨p.toPath⟩

/-- A canonical loop-free resolution of the broken line. -/
noncomputable def resolvedPath : B.inSetGraph.Path
    (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n)) :=
  Classical.choice B.exists_arrangement_path

/-- The `resolvedWalk` declaration. -/
noncomputable def resolvedWalk : B.inSetGraph.Walk
    (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n)) :=
  B.resolvedPath

/-- Ordered geometric vertices of the resolved polygonal arc. -/
noncomputable def resolvedVertex
    (i : Fin (B.resolvedWalk.length + 1)) : Plane :=
  B.arrangementMesh.toPlaneComplex.position
    (B.resolvedWalk.getVert i)

theorem resolvedVertex_injective : Function.Injective B.resolvedVertex := by
  intro i j hij
  apply Fin.ext
  apply B.resolvedPath.property.getVert_injOn
  · change i.val ≤ B.resolvedWalk.length
    omega
  · change j.val ≤ B.resolvedWalk.length
    omega
  apply B.arrangementMesh.toPlaneComplex.position_injective
  exact hij

theorem resolvedVertex_start : B.resolvedVertex 0 = B.start := by
  change B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert 0) = B.start
  rw [SimpleGraph.Walk.getVert_zero]
  exact B.arrangementVertex_position 0

theorem resolvedVertex_finish :
    B.resolvedVertex (Fin.last B.resolvedWalk.length) =
      B.finish := by
  change B.arrangementMesh.toPlaneComplex.position
    (B.resolvedWalk.getVert B.resolvedWalk.length) = B.finish
  rw [SimpleGraph.Walk.getVert_length]
  exact B.arrangementVertex_position (Fin.last B.n)

theorem resolvedSegment_subset (i : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ⊆ U := by
  let p : B.inSetGraph.Walk _ _ := B.resolvedWalk
  have hadj := p.adj_getVert_succ i.isLt
  rw [B.inSetGraph_adj_iff] at hadj
  have hcarrier := hadj.2.2
  change segment ℝ
      (B.arrangementMesh.toPlaneComplex.position (p.getVert i.val))
      (B.arrangementMesh.toPlaneComplex.position (p.getVert (i.val + 1))) ⊆ U
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({p.getVert i.val, p.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position (p.getVert i.val),
        B.arrangementMesh.toPlaneComplex.position (p.getVert (i.val + 1))} := by
    ext x
    simp [eq_comm]
  rw [PlaneComplex.cellCarrier, himage, convexHull_pair] at hcarrier
  exact hcarrier

theorem resolvedSegment_eq_cellCarrier (i : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) =
      B.arrangementMesh.toPlaneComplex.cellCarrier
        {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} := by
  change segment ℝ
      (B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert i.val))
      (B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert (i.val + 1))) = _
  rw [PlaneComplex.cellCarrier]
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert i.val),
        B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert (i.val + 1))} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

theorem resolvedEdge_mem_simplexes (i : Fin B.resolvedWalk.length) :
    ({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
        B.arrangementMesh.toPlaneComplex.simplexes := by
  have hadj := B.resolvedWalk.adj_getVert_succ i.isLt
  rw [B.inSetGraph_adj_iff] at hadj
  exact hadj.2.1

/-- Exact face-to-face intersection for the ordered segments of the resolved arc. -/
theorem resolvedSegment_inter (i j : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ∩
      segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) =
    B.arrangementMesh.toPlaneComplex.cellCarrier
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}) := by
  rw [B.resolvedSegment_eq_cellCarrier i, B.resolvedSegment_eq_cellCarrier j]
  simpa only [PlaneComplex.cellCarrier] using
    B.arrangementMesh.toPlaneComplex.face_inter _ (B.resolvedEdge_mem_simplexes i)
      _ (B.resolvedEdge_mem_simplexes j)

/-- The geometric carrier of the selected graph path. -/
def resolvedCarrier : Set Plane :=
  if _ : B.resolvedWalk.length = 0 then {B.resolvedVertex 0}
  else ⋃ i : Fin B.resolvedWalk.length,
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ)

theorem resolvedCarrier_subset (hstart : B.start ∈ U) : B.resolvedCarrier ⊆ U := by
  intro x hx
  unfold resolvedCarrier at hx
  split_ifs at hx with hzero
  · have hx0 : x = B.resolvedVertex 0 := hx
    rw [hx0, B.resolvedVertex_start]
    exact hstart
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact B.resolvedSegment_subset i hxi

private def IsResolvedFace (s : Finset B.arrangementMesh.toPlaneComplex.Vertex) : Prop :=
  s.Nonempty ∧
    ((B.resolvedWalk.length = 0 ∧ s ⊆ {B.resolvedWalk.getVert 0}) ∨
      ∃ i : Fin B.resolvedWalk.length,
        s ⊆ {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)})

/-- The parent-arrangement subcomplex consisting of the chosen path edges and their vertices. -/
noncomputable def resolvedComplex : PlaneComplex := by
  classical
  let K := B.arrangementMesh.toPlaneComplex
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter B.IsResolvedFace
    nonempty_of_mem := by
      intro s hs
      exact (Finset.mem_filter.mp hs).2.1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsne, hsPath⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨K.down_closed s hsK t hts ht, ht, ?_⟩
      rcases hsPath with ⟨hzero, hs0⟩ | ⟨i, hsi⟩
      · exact Or.inl ⟨hzero, hts.trans hs0⟩
      · exact Or.inr ⟨i, hts.trans hsi⟩
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem resolvedComplex_position :
    B.resolvedComplex.position = B.arrangementMesh.toPlaneComplex.position := rfl

@[simp] theorem resolvedComplex_cellCarrier
    (s : Finset B.arrangementMesh.toPlaneComplex.Vertex) :
    B.resolvedComplex.cellCarrier s =
      B.arrangementMesh.toPlaneComplex.cellCarrier s := rfl

theorem mem_resolvedComplex_simplexes_iff
    {s : Finset B.arrangementMesh.toPlaneComplex.Vertex} :
    s ∈ B.resolvedComplex.simplexes ↔
      s ∈ B.arrangementMesh.toPlaneComplex.simplexes ∧ B.IsResolvedFace s := by
  classical
  change s ∈ B.arrangementMesh.toPlaneComplex.simplexes.filter B.IsResolvedFace ↔ _
  exact Finset.mem_filter

/-- Every ordered vertex of the resolved path occurs as a zero-face of the selected complex. -/
theorem resolvedVertex_face (i : Fin (B.resolvedWalk.length + 1)) :
    ({B.resolvedWalk.getVert i.val} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes := by
  classical
  by_cases hzero : B.resolvedWalk.length = 0
  · have hi : i = 0 := Fin.ext (by omega)
    subst i
    apply B.mem_resolvedComplex_simplexes_iff.mpr
    refine ⟨?_, Finset.singleton_nonempty _, Or.inl ⟨hzero, subset_rfl⟩⟩
    simpa using B.arrangementVertex_face 0
  · have hpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
    by_cases hi : i.val < B.resolvedWalk.length
    · let j : Fin B.resolvedWalk.length := ⟨i.val, hi⟩
      have hsubset : ({B.resolvedWalk.getVert i.val} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ⊆
          {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} := by
        simp [j]
      have hsingleton := B.arrangementMesh.toPlaneComplex.down_closed _
        (B.resolvedEdge_mem_simplexes j) _ hsubset (Finset.singleton_nonempty _)
      exact B.mem_resolvedComplex_simplexes_iff.mpr
        ⟨hsingleton, Finset.singleton_nonempty _, Or.inr ⟨j, hsubset⟩⟩
    · have hilast : i.val = B.resolvedWalk.length := by omega
      let j : Fin B.resolvedWalk.length :=
        ⟨B.resolvedWalk.length - 1, Nat.sub_lt hpos (by omega)⟩
      have hsubset : ({B.resolvedWalk.getVert i.val} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ⊆
          {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} := by
        intro v hv
        simp only [Finset.mem_singleton] at hv
        subst v
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        congr 1
        change i.val = B.resolvedWalk.length - 1 + 1
        omega
      have hsingleton := B.arrangementMesh.toPlaneComplex.down_closed _
        (B.resolvedEdge_mem_simplexes j) _ hsubset (Finset.singleton_nonempty _)
      exact B.mem_resolvedComplex_simplexes_iff.mpr
        ⟨hsingleton, Finset.singleton_nonempty _, Or.inr ⟨j, hsubset⟩⟩

/-- Every ordered path vertex lies in the support of the selected complex. -/
theorem resolvedVertex_mem_support (i : Fin (B.resolvedWalk.length + 1)) :
    B.resolvedComplex.position (B.resolvedWalk.getVert i.val) ∈
      B.resolvedComplex.support := by
  apply B.resolvedComplex.cellCarrier_subset_support (B.resolvedVertex_face i)
  exact subset_convexHull ℝ _ ⟨B.resolvedWalk.getVert i.val,
    Finset.mem_singleton_self _, rfl⟩

theorem resolvedComplex_card_le_two {s : Finset B.resolvedComplex.Vertex}
    (hs : s ∈ B.resolvedComplex.simplexes) : s.card ≤ 2 := by
  have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
  rcases hface.2 with ⟨-, hs0⟩ | ⟨i, hsi⟩
  · have hc : s.card ≤ ({B.resolvedWalk.getVert 0} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex).card :=
      Finset.card_le_card hs0
    calc
      s.card ≤ 1 := by simpa only [Finset.card_singleton] using hc
      _ ≤ 2 := by omega
  · exact (Finset.card_le_card hsi).trans Finset.card_le_two

theorem resolvedComplex_support : B.resolvedComplex.support = B.resolvedCarrier := by
  classical
  unfold resolvedCarrier
  split_ifs with hzero
  · have hpathNil : B.resolvedWalk.Nil := by simpa [SimpleGraph.Walk.length_eq_zero_iff] using hzero
    have hstartEnd : B.arrangementVertex 0 = B.arrangementVertex (Fin.last B.n) :=
      hpathNil.eq
    apply Set.Subset.antisymm
    · intro x hx
      rw [PlaneComplex.support] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
      have hs0 : s ⊆ {B.resolvedWalk.getVert 0} := by
        rcases hface.2 with ⟨-, hs0⟩ | ⟨i, -⟩
        · exact hs0
        · exact isEmptyElim (hzero ▸ i)
      have hcarrier : B.resolvedComplex.cellCarrier s ⊆ {B.resolvedVertex 0} := by
        apply convexHull_min _ (convex_singleton _)
        rintro y ⟨v, hv, rfl⟩
        have hv0 : v = B.resolvedWalk.getVert 0 := by
          exact Finset.mem_singleton.mp (hs0 hv)
        subst v
        rfl
      exact hcarrier hxs
    · rintro x rfl
      rw [PlaneComplex.support]
      refine Set.mem_iUnion₂.mpr ⟨{B.resolvedWalk.getVert 0}, ?_, ?_⟩
      · apply B.mem_resolvedComplex_simplexes_iff.mpr
        refine ⟨?_, ?_⟩
        · have hstart : B.resolvedWalk.getVert 0 = B.arrangementVertex 0 := by simp
          change ({B.resolvedWalk.getVert 0} :
            Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
              B.arrangementMesh.toPlaneComplex.simplexes
          rw [hstart]
          exact B.arrangementVertex_face 0
        · exact ⟨Finset.singleton_nonempty _, Or.inl ⟨hzero, subset_rfl⟩⟩
      · exact subset_convexHull ℝ _
          ⟨B.resolvedWalk.getVert 0, Finset.mem_singleton_self _, rfl⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rw [PlaneComplex.support] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      obtain ⟨-, -, hsPath⟩ := B.mem_resolvedComplex_simplexes_iff.mp hs
      rcases hsPath with hsZero | ⟨i, hsi⟩
      · exact (hzero hsZero.1).elim
      · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [B.resolvedSegment_eq_cellCarrier i]
        exact convexHull_mono (Set.image_mono hsi) hxs
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [B.resolvedSegment_eq_cellCarrier i] at hxi
      rw [PlaneComplex.support]
      let s : Finset B.arrangementMesh.toPlaneComplex.Vertex :=
        {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)}
      refine Set.mem_iUnion₂.mpr ⟨s, ?_, hxi⟩
      apply B.mem_resolvedComplex_simplexes_iff.mpr
      exact ⟨B.resolvedEdge_mem_simplexes i, by
        refine ⟨by simp [s], Or.inr ⟨i, ?_⟩⟩
        exact subset_rfl⟩

/-- Affine coordinate from `0` to `1` along one resolved path edge. -/
noncomputable def resolvedEdgeParameter (i : Fin B.resolvedWalk.length) :
    Plane →ᵃ[ℝ] ℝ :=
  if _ : B.resolvedVertex i.castSucc 0 ≠ B.resolvedVertex i.succ 0 then
    (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0)⁻¹ •
      (cartesianX - AffineMap.const ℝ Plane (B.resolvedVertex i.castSucc 0))
  else
    (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1)⁻¹ •
      (cartesianY - AffineMap.const ℝ Plane (B.resolvedVertex i.castSucc 1))

theorem resolvedEdgeParameter_apply_left (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeParameter i (B.resolvedVertex i.castSucc) = 0 := by
  unfold resolvedEdgeParameter
  split_ifs <;> simp

theorem resolvedEdgeParameter_apply_right (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeParameter i (B.resolvedVertex i.succ) = 1 := by
  unfold resolvedEdgeParameter
  split_ifs with h0
  · change (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0)⁻¹ *
        (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr h0.symm)
  · have hne : B.resolvedVertex i.castSucc ≠ B.resolvedVertex i.succ := by
      intro heq
      exact (Fin.ne_of_lt i.castSucc_lt_succ) (B.resolvedVertex_injective heq)
    have h1 : B.resolvedVertex i.castSucc 1 ≠ B.resolvedVertex i.succ 1 := by
      intro h1
      apply hne
      exact plane_ext (not_ne_iff.mp h0) h1
    change (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1)⁻¹ *
        (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr h1.symm)

theorem resolvedEdgeParameter_lineMap (i : Fin B.resolvedWalk.length) (t : ℝ) :
    B.resolvedEdgeParameter i
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) = t := by
  rw [AffineMap.apply_lineMap, B.resolvedEdgeParameter_apply_left,
    B.resolvedEdgeParameter_apply_right]
  simp [AffineMap.lineMap_apply_module]

/-- The affine coordinate on edge `i`, shifted to the interval `[i,i+1]`. -/
noncomputable def resolvedEdgeGlobalParameter (i : Fin B.resolvedWalk.length) :
    Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane (i.val : ℝ) + B.resolvedEdgeParameter i

theorem resolvedEdgeGlobalParameter_apply_left (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeGlobalParameter i (B.resolvedVertex i.castSucc) = i.val := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i (B.resolvedVertex i.castSucc) = i.val
  rw [B.resolvedEdgeParameter_apply_left]
  simp

theorem resolvedEdgeGlobalParameter_apply_right (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeGlobalParameter i (B.resolvedVertex i.succ) = i.val + 1 := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i (B.resolvedVertex i.succ) = i.val + 1
  rw [B.resolvedEdgeParameter_apply_right]

theorem resolvedEdgeGlobalParameter_lineMap (i : Fin B.resolvedWalk.length) (t : ℝ) :
    B.resolvedEdgeGlobalParameter i
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) =
        i.val + t := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i
    (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) = i.val + t
  rw [B.resolvedEdgeParameter_lineMap]

private theorem getVert_index_eq {r s : ℕ} (hr : r ≤ B.resolvedWalk.length)
    (hs : s ≤ B.resolvedWalk.length)
    (h : B.resolvedWalk.getVert r = B.resolvedWalk.getVert s) : r = s :=
  B.resolvedPath.property.getVert_injOn hr hs h

theorem resolvedEdge_indices_close (i j : Fin B.resolvedWalk.length)
    (hinter : (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
      {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}).Nonempty) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨v, hv⟩ := hinter
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv.1 with hi | hi <;> rcases hv.2 with hj | hj
  · left
    apply Fin.ext
    exact B.getVert_index_eq i.isLt.le j.isLt.le (hi.symm.trans hj)
  · right; right
    exact B.getVert_index_eq i.isLt.le (by omega) (hi.symm.trans hj) |>.symm
  · right; left
    exact B.getVert_index_eq (by omega) j.isLt.le (hi.symm.trans hj)
  · left
    apply Fin.ext
    have := B.getVert_index_eq (r := i.val + 1) (s := j.val + 1)
      (by omega) (by omega) (hi.symm.trans hj)
    omega

theorem resolvedSegment_indices_close (i j : Fin B.resolvedWalk.length) {x : Plane}
    (hxi : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ))
    (hxj : x ∈ segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ)) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hx : x ∈ B.arrangementMesh.toPlaneComplex.cellCarrier
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}) := by
    rw [← B.resolvedSegment_inter i j]
    exact ⟨hxi, hxj⟩
  have hne : (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, PlaneComplex.cellCarrier] at hx
    simp at hx
  exact B.resolvedEdge_indices_close i j hne

theorem resolvedSegment_inter_of_succ_eq (i j : Fin B.resolvedWalk.length)
    (hij : i.val + 1 = j.val) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ∩
      segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) =
        {B.resolvedVertex i.succ} := by
  rw [B.resolvedSegment_inter i j]
  have hshared : B.resolvedWalk.getVert (i.val + 1) = B.resolvedWalk.getVert j.val := by
    rw [hij]
  have houter : B.resolvedWalk.getVert i.val ≠
      B.resolvedWalk.getVert (j.val + 1) := by
    intro h
    have heq := B.getVert_index_eq i.isLt.le (by omega) h
    omega
  have hleft : B.resolvedWalk.getVert i.val ≠ B.resolvedWalk.getVert j.val := by
    intro h
    have heq := B.getVert_index_eq i.isLt.le j.isLt.le h
    omega
  have hright : B.resolvedWalk.getVert (i.val + 1) ≠
      B.resolvedWalk.getVert (j.val + 1) := by
    intro h
    have heq := B.getVert_index_eq (by omega) (by omega) h
    omega
  have hinter :
      ({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} =
          {B.resolvedWalk.getVert (i.val + 1)} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hi | hi, hj | hj⟩
      · exact (hleft (hi.symm.trans hj)).elim
      · exact (houter (hi.symm.trans hj)).elim
      · exact hi
      · exact (hright (hi.symm.trans hj)).elim
    · intro hv
      exact ⟨Or.inr hv, Or.inl (hv.trans hshared)⟩
  rw [hinter, PlaneComplex.cellCarrier]
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position
        (B.resolvedWalk.getVert (i.val + 1))} := by
    ext x
    simp []
  rw [himage, convexHull_singleton]
  rfl

/-- The shifted affine edge parameters agree wherever two selected path edges meet. -/
theorem resolvedEdgeGlobalParameter_agree (i j : Fin B.resolvedWalk.length) {x : Plane}
    (hxi : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ))
    (hxj : x ∈ segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ)) :
    B.resolvedEdgeGlobalParameter i x = B.resolvedEdgeGlobalParameter j x := by
  rcases B.resolvedSegment_indices_close i j hxi hxj with rfl | hij | hji
  · rfl
  · have hxShared : x = B.resolvedVertex i.succ := by
      have hxInter : x ∈ segment ℝ (B.resolvedVertex i.castSucc)
          (B.resolvedVertex i.succ) ∩
        segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) := ⟨hxi, hxj⟩
      rw [B.resolvedSegment_inter_of_succ_eq i j hij] at hxInter
      exact hxInter
    have hvertex : B.resolvedVertex i.succ = B.resolvedVertex j.castSucc := by
      apply congrArg B.resolvedVertex
      apply Fin.ext
      exact hij
    rw [hxShared, B.resolvedEdgeGlobalParameter_apply_right, hvertex,
      B.resolvedEdgeGlobalParameter_apply_left]
    exact_mod_cast hij
  · have hxShared : x = B.resolvedVertex j.succ := by
      have hxInter : x ∈ segment ℝ (B.resolvedVertex j.castSucc)
          (B.resolvedVertex j.succ) ∩
        segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := ⟨hxj, hxi⟩
      rw [B.resolvedSegment_inter_of_succ_eq j i hji] at hxInter
      exact hxInter
    have hvertex : B.resolvedVertex j.succ = B.resolvedVertex i.castSucc := by
      apply congrArg B.resolvedVertex
      apply Fin.ext
      exact hji
    symm
    rw [hxShared, B.resolvedEdgeGlobalParameter_apply_right, hvertex,
      B.resolvedEdgeGlobalParameter_apply_left]
    exact_mod_cast hji

/-- Piecewise-affine coordinate along the whole resolved arc. -/
noncomputable def resolvedGlobalParameter (x : Plane) : ℝ :=
  by
    classical
    exact if h : ∃ i : Fin B.resolvedWalk.length,
        x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) then
      B.resolvedEdgeGlobalParameter (Classical.choose h) x
    else 0

theorem resolvedGlobalParameter_eq_on_edge (i : Fin B.resolvedWalk.length) {x : Plane}
    (hx : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ)) :
    B.resolvedGlobalParameter x = B.resolvedEdgeGlobalParameter i x := by
  unfold resolvedGlobalParameter
  split_ifs with h
  · exact B.resolvedEdgeGlobalParameter_agree (Classical.choose h) i
      (Classical.choose_spec h) hx
  · exact (h ⟨i, hx⟩).elim

theorem resolvedGlobalParameter_lineMap_of_mem (i : Fin B.resolvedWalk.length)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    B.resolvedGlobalParameter
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) =
        i.val + t := by
  rw [B.resolvedGlobalParameter_eq_on_edge i
    (lineMap_mem_segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ht)]
  exact B.resolvedEdgeGlobalParameter_lineMap i t

theorem resolvedGlobalParameter_injectiveOn :
    Set.InjOn B.resolvedGlobalParameter B.resolvedCarrier := by
  intro x hx y hy hxy
  unfold resolvedCarrier at hx hy
  split_ifs at hx hy with hzero
  · simpa using hx.trans hy.symm
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    rw [segment_eq_image_lineMap] at hxi hyj
    obtain ⟨t, ht, rfl⟩ := hxi
    obtain ⟨u, hu, rfl⟩ := hyj
    rw [B.resolvedGlobalParameter_lineMap_of_mem i ht,
      B.resolvedGlobalParameter_lineMap_of_mem j hu] at hxy
    by_cases hij : i.val = j.val
    · have htu : t = u := by
        have hijR : (i.val : ℝ) = j.val := by exact_mod_cast hij
        rw [hijR] at hxy
        linarith
      rw [show i = j by exact Fin.ext hij, htu]
    · rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hsucc : i.val + 1 = j.val := by
          have hle : i.val + 1 ≤ j.val := by omega
          have hle' : (j.val : ℝ) ≤ i.val + 1 := by
            linarith [ht.2, hu.1]
          have hleNat' : j.val ≤ i.val + 1 := by exact_mod_cast hle'
          exact Nat.le_antisymm hle hleNat'
        have ht1 : t = 1 := by
          have hsR : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hsucc
          rw [← hsR] at hxy
          linarith [hu.1, ht.2]
        have hu0 : u = 0 := by
          have hsR : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hsucc
          rw [← hsR, ht1] at hxy
          linarith
        have hvertex : B.resolvedVertex i.succ = B.resolvedVertex j.castSucc := by
          apply congrArg B.resolvedVertex
          exact Fin.ext hsucc
        simpa [ht1, hu0] using hvertex
      · have hsucc : j.val + 1 = i.val := by
          have hle : j.val + 1 ≤ i.val := by omega
          have hle' : (i.val : ℝ) ≤ j.val + 1 := by
            linarith [hu.2, ht.1]
          have hleNat' : i.val ≤ j.val + 1 := by exact_mod_cast hle'
          exact Nat.le_antisymm hle hleNat'
        have hu1 : u = 1 := by
          have hsR : (j.val : ℝ) + 1 = i.val := by exact_mod_cast hsucc
          rw [← hsR] at hxy
          linarith [ht.1, hu.2]
        have ht0 : t = 0 := by
          have hsR : (j.val : ℝ) + 1 = i.val := by exact_mod_cast hsucc
          rw [← hsR, hu1] at hxy
          linarith
        have hvertex : B.resolvedVertex j.succ = B.resolvedVertex i.castSucc := by
          apply congrArg B.resolvedVertex
          exact Fin.ext hsucc
        simpa [ht0, hu1] using hvertex.symm

theorem resolvedGlobalParameter_image :
    B.resolvedGlobalParameter '' B.resolvedCarrier =
      Set.Icc (0 : ℝ) B.resolvedWalk.length := by
  apply Set.Subset.antisymm
  · rintro r ⟨x, hx, rfl⟩
    unfold resolvedCarrier at hx
    split_ifs at hx with hzero
    · have hx0 : x = B.resolvedVertex 0 := hx
      subst x
      have hno : ¬∃ i : Fin B.resolvedWalk.length,
          B.resolvedVertex 0 ∈
            segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
        rintro ⟨i, -⟩
        exact isEmptyElim (hzero ▸ i)
      have hparam : B.resolvedGlobalParameter (B.resolvedVertex 0) = 0 := by
        unfold resolvedGlobalParameter
        simp [hno]
      constructor
      · rw [hparam]
      · rw [hparam, hzero]
        norm_num
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [segment_eq_image_lineMap] at hxi
      obtain ⟨t, ht, rfl⟩ := hxi
      rw [B.resolvedGlobalParameter_lineMap_of_mem i ht]
      constructor
      · exact add_nonneg (Nat.cast_nonneg _) ht.1
      · have hi : i.val + 1 ≤ B.resolvedWalk.length := i.isLt
        have hiR : (i.val : ℝ) + 1 ≤ B.resolvedWalk.length := by exact_mod_cast hi
        linarith [ht.2]
  · intro r hr
    by_cases hzero : B.resolvedWalk.length = 0
    · have hr0 : r = 0 := by
        rw [hzero] at hr
        norm_num at hr
        exact hr
      subst r
      refine ⟨B.resolvedVertex 0, ?_, ?_⟩
      · unfold resolvedCarrier
        simp [hzero]
      · have hno : ¬∃ i : Fin B.resolvedWalk.length,
            B.resolvedVertex 0 ∈
              segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
          rintro ⟨i, -⟩
          exact isEmptyElim (hzero ▸ i)
        unfold resolvedGlobalParameter
        simp [hno]
    · have hnpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
      by_cases hrn : r = B.resolvedWalk.length
      · let i : Fin B.resolvedWalk.length :=
          ⟨B.resolvedWalk.length - 1, Nat.sub_lt hnpos (by omega)⟩
        let x := B.resolvedVertex i.succ
        refine ⟨x, ?_, ?_⟩
        · unfold resolvedCarrier
          simp only [hzero, ↓reduceDIte]
          refine Set.mem_iUnion.mpr ⟨i, right_mem_segment ℝ _ _⟩
        · have hxLine : x = AffineMap.lineMap (B.resolvedVertex i.castSucc)
              (B.resolvedVertex i.succ) (1 : ℝ) := by
            change B.resolvedVertex i.succ =
              AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) (1 : ℝ)
            simp
          rw [hxLine]
          have hparam := B.resolvedGlobalParameter_lineMap_of_mem i
            (t := (1 : ℝ)) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
          rw [hparam]
          change ((B.resolvedWalk.length - 1 : ℕ) : ℝ) + 1 = r
          rw [hrn]
          exact_mod_cast Nat.sub_add_cancel hnpos
      · have hrlt : r < B.resolvedWalk.length := lt_of_le_of_ne hr.2 hrn
        let k : ℕ := ⌊r⌋₊
        have hklt : k < B.resolvedWalk.length := by
          exact (Nat.floor_lt hr.1).mpr hrlt
        let i : Fin B.resolvedWalk.length := ⟨k, hklt⟩
        let t : ℝ := r - k
        have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · dsimp [t, k]
            linarith [Nat.floor_le hr.1]
          · dsimp [t, k]
            linarith [Nat.lt_floor_add_one r]
        let x := AffineMap.lineMap (B.resolvedVertex i.castSucc)
          (B.resolvedVertex i.succ) t
        refine ⟨x, ?_, ?_⟩
        · unfold resolvedCarrier
          simp only [hzero, ↓reduceDIte]
          exact Set.mem_iUnion.mpr ⟨i, lineMap_mem_segment ℝ _ _ ht⟩
        · rw [show B.resolvedGlobalParameter x = i.val + t by
            exact B.resolvedGlobalParameter_lineMap_of_mem i ht]
          simp [i, t, k]

theorem resolvedGlobalParameter_start :
    B.resolvedGlobalParameter (B.resolvedVertex 0) = 0 := by
  by_cases hzero : B.resolvedWalk.length = 0
  · have hno : ¬∃ i : Fin B.resolvedWalk.length,
        B.resolvedVertex 0 ∈
          segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
      rintro ⟨i, -⟩
      exact isEmptyElim (hzero ▸ i)
    simp [resolvedGlobalParameter, hno]
  · let i : Fin B.resolvedWalk.length := ⟨0, Nat.pos_of_ne_zero hzero⟩
    have hleft : B.resolvedVertex 0 = B.resolvedVertex i.castSucc := by
      congr 1
    rw [hleft, B.resolvedGlobalParameter_eq_on_edge i (left_mem_segment ℝ _ _),
      B.resolvedEdgeGlobalParameter_apply_left]
    simp [i]

theorem resolvedGlobalParameter_finish :
    B.resolvedGlobalParameter (B.resolvedVertex (Fin.last B.resolvedWalk.length)) =
      B.resolvedWalk.length := by
  by_cases hzero : B.resolvedWalk.length = 0
  · have hlast : (Fin.last B.resolvedWalk.length) = 0 := Fin.ext (by simp [hzero])
    rw [hlast, B.resolvedGlobalParameter_start, hzero]
    norm_num
  · have hpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
    let i : Fin B.resolvedWalk.length :=
      ⟨B.resolvedWalk.length - 1, Nat.sub_lt hpos (by omega)⟩
    have hright : i.succ = Fin.last B.resolvedWalk.length := by
      apply Fin.ext
      change B.resolvedWalk.length - 1 + 1 = B.resolvedWalk.length
      omega
    rw [← hright, B.resolvedGlobalParameter_eq_on_edge i (right_mem_segment ℝ _ _),
      B.resolvedEdgeGlobalParameter_apply_right]
    dsimp [i]
    exact_mod_cast Nat.sub_add_cancel hpos

/-- Affine inclusion of the real axis into the plane. -/
def realAxisLinear : ℝ →ₗ[ℝ] Plane where
  toFun t := planePoint t 0
  map_add' := by intro x y; ext i ; fin_cases i <;> simp [planePoint]
  map_smul' := by intro c x; ext i ; fin_cases i <;> simp [planePoint]

/-- The `realAxisAffine` declaration. -/
def realAxisAffine : ℝ →ᵃ[ℝ] Plane := realAxisLinear.toAffineMap

@[simp] theorem realAxisAffine_apply (t : ℝ) : realAxisAffine t = planePoint t 0 := rfl

/-- Piecewise-affine straightening of the selected polygonal arc onto the real axis. -/
noncomputable def resolvedStraighten (x : Plane) : Plane :=
  realAxisAffine (B.resolvedGlobalParameter x)

theorem resolvedStraighten_start :
    B.resolvedStraighten (B.resolvedVertex 0) = planePoint 0 0 := by
  simp [resolvedStraighten, B.resolvedGlobalParameter_start]

theorem resolvedStraighten_finish :
    B.resolvedStraighten (B.resolvedVertex (Fin.last B.resolvedWalk.length)) =
      planePoint B.resolvedWalk.length 0 := by
  simp [resolvedStraighten, B.resolvedGlobalParameter_finish]

theorem resolvedStraighten_injectiveOn :
    Set.InjOn B.resolvedStraighten B.resolvedCarrier := by
  intro x hx y hy hxy
  apply B.resolvedGlobalParameter_injectiveOn hx hy
  have hcoord := congrArg (fun p : Plane => p 0) hxy
  exact hcoord

theorem resolvedStraighten_image :
    B.resolvedStraighten '' B.resolvedCarrier =
      segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) := by
  have himage : B.resolvedStraighten '' B.resolvedCarrier =
      realAxisAffine '' (B.resolvedGlobalParameter '' B.resolvedCarrier) := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨B.resolvedGlobalParameter y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [himage, B.resolvedGlobalParameter_image,
    ← segment_eq_Icc (show (0 : ℝ) ≤ B.resolvedWalk.length by positivity),
    image_segment (𝕜 := ℝ) realAxisAffine]
  rfl

theorem resolvedStraighten_affineOn_faces :
    ∀ s ∈ B.resolvedComplex.simplexes,
      IsAffineOn B.resolvedStraighten (B.resolvedComplex.cellCarrier s) := by
  intro s hs
  have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
  rcases hface.2 with ⟨hzero, hs0⟩ | ⟨i, hsi⟩
  · let g : Plane →ᵃ[ℝ] Plane :=
      realAxisAffine.comp (AffineMap.const ℝ Plane 0)
    refine ⟨g, ?_⟩
    intro x hx
    have hx0 : x = B.resolvedVertex 0 := by
      have hsubset : B.resolvedComplex.cellCarrier s ⊆ {B.resolvedVertex 0} := by
        apply convexHull_min _ (convex_singleton _)
        rintro y ⟨v, hv, rfl⟩
        have hv0 : v = B.resolvedWalk.getVert 0 := Finset.mem_singleton.mp (hs0 hv)
        subst v
        rfl
      exact hsubset hx
    subst x
    have hno : ¬∃ i : Fin B.resolvedWalk.length,
        B.resolvedVertex 0 ∈
          segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
      rintro ⟨i, -⟩
      exact isEmptyElim (hzero ▸ i)
    simp [resolvedStraighten, resolvedGlobalParameter, hno, g]
  · let g : Plane →ᵃ[ℝ] Plane :=
      realAxisAffine.comp (B.resolvedEdgeGlobalParameter i)
    refine ⟨g, ?_⟩
    intro x hx
    have hxEdge : x ∈ segment ℝ (B.resolvedVertex i.castSucc)
        (B.resolvedVertex i.succ) := by
      rw [B.resolvedSegment_eq_cellCarrier i]
      exact convexHull_mono (Set.image_mono hsi) hx
    change realAxisAffine (B.resolvedGlobalParameter x) =
      realAxisAffine (B.resolvedEdgeGlobalParameter i x)
    rw [B.resolvedGlobalParameter_eq_on_edge i hxEdge]

/-- The ordered broken-line data underlying the canonical simple graph path. -/
noncomputable def resolvedBrokenLine : BrokenLineData U where
  n := B.resolvedWalk.length
  vertex := B.resolvedVertex
  segment_subset := B.resolvedSegment_subset

theorem resolvedBrokenLine_start : B.resolvedBrokenLine.start = B.start :=
  B.resolvedVertex_start

theorem resolvedBrokenLine_finish : B.resolvedBrokenLine.finish = B.finish :=
  B.resolvedVertex_finish

theorem resolvedBrokenLine_vertex_injective :
    Function.Injective B.resolvedBrokenLine.vertex :=
  B.resolvedVertex_injective

end BrokenLineData

/-- A weak broken line can be resolved into a loop-free path in a finite straight-line graph,
with every graph edge contained in the same set.  This is the precise polygonal-arc form of
Moise Chapter 6, Theorem 1 used by the graph approximation argument. -/
theorem JoinedByBrokenLine.exists_polygonalArc {U : Set Plane} {a b : Plane}
    (h : JoinedByBrokenLine U a b) :
    ∃ B : BrokenLineData U,
      B.start = a ∧ B.finish = b ∧
      Nonempty (B.inSetGraph.Path
        (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n))) := by
  obtain ⟨B, hstart, hfinish⟩ := BrokenLineData.exists_data_of_joined h
  exact ⟨B, hstart, hfinish, B.exists_arrangement_path⟩

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification05_block_03
/- END ClassificationOfSurfaces.Moise.PolygonalArc -/
