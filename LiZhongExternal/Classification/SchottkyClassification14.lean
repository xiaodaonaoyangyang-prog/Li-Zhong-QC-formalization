/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification14: pinned classification sources; see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification08
import LiZhongExternal.Classification.SchottkyClassification09
import LiZhongExternal.Classification.SchottkyClassification04
import LiZhongExternal.Classification.SchottkyClassification05
import LiZhongExternal.Classification.SchottkyClassification12
import Mathlib.Analysis.Complex.Tietze
import LiZhongExternal.Classification.SchottkyClassification06
import LiZhongExternal.Classification.SchottkyClassification13
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/- BEGIN ClassificationOfSurfaces.Moise.PLApproximation | 5de5a5ea8a1003bafbca97a3dc3c47398665f3a8b28545e0288b060f0ecf44d6 -/
noncomputable section

section schottkyclassification14_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# PL approximation of homeomorphisms

The crux of the Moise route (Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 5-6):

* Ch. 5, Thms. 3-6 (combinatorial Schoenflies and cone extension): a PL homeomorphism between
  the boundaries of two triangles extends to a PL homeomorphism of the triangles;
* Ch. 6, Thm. 2: an embedding of a finite one-dimensional complex into the plane can be
  approximated, arbitrarily closely and fixing vertex images, by a PL embedding;
* Ch. 6, Thm. 3: an embedding of a finite combinatorial 2-manifold-with-boundary into the plane
  can be approximated, arbitrarily closely, by a PL embedding.

Moise's own remark (end of Ch. 8): the restriction to dimension 2 in the entire triangulation
proof is used *only* through Thm. 6.3.  This file is therefore the mathematical core of the
route.  Moise states Ch. 6 with strongly positive control functions `φ ≫ 0` to handle
non-compact complexes; our complexes are finite, so uniform `ε`-control is equivalent and the
statements below use it.

The full Jordan curve theorem (Ch. 4) is not used by these theorems: Thm. 6.2 needs only
broken-line connectivity (Ch. 1), and Thm. 6.3 needs the polygonal theorems of Ch. 2-3 through
the combinatorial Schoenflies theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Every closed triangle has an explicit polygonal presentation of its frontier. -/
theorem IsTriangle.exists_polygonalCircle {C : Set Plane} (hC : IsTriangle C) :
    ∃ J : PolygonalCircle, J.carrier = frontier C := by
  obtain ⟨p, hp, rfl⟩ := hC
  let E : Plane ≃ᵃ[ℝ] Plane :=
    triangleAffineEquiv standardTriangleVertex p
      standardTriangleVertex_affineIndependent hp
  have hedge : ∀ i : ZMod standardTriangleCircle.n,
      E '' standardTriangleCircle.edgeSegment i =
        segment ℝ (E (standardTriangleCircle.vertex i))
          (E (standardTriangleCircle.vertex (i + 1))) := by
    intro i
    exact image_segment ℝ E.toAffineMap _ _
  let J := standardTriangleCircle.mapEmbedding E E.injective.injOn hedge
  refine ⟨J, ?_⟩
  rw [show J.carrier = E '' standardTriangleCircle.carrier by
    exact standardTriangleCircle.mapEmbedding_carrier E E.injective.injOn hedge,
    standardTriangleCircle_carrier]
  change affineEquivHomeomorph E '' frontier
      (convexHull ℝ (Set.range standardTriangleVertex)) = _
  rw [(affineEquivHomeomorph E).image_frontier,
    show affineEquivHomeomorph E '' convexHull ℝ (Set.range standardTriangleVertex) =
        convexHull ℝ (Set.range p) by
      exact triangleAffineEquiv_image_convexHull standardTriangleVertex p
        standardTriangleVertex_affineIndependent hp]

/-- The topological interior of a full-dimensional plane simplex is its barycentric interior. -/
theorem interior_convexHull_fin3_eq_simplex_interior (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) :
    interior (convexHull ℝ (Set.range p)) =
      ({ points := p, independent := hp } : Affine.Simplex ℝ Plane 2).interior := by
  let b := planeAffineBasisOfTriple p hp
  let S : Affine.Simplex ℝ Plane 2 := { points := p, independent := hp }
  have hrange : Set.range (b : Fin 3 → Plane) = Set.range p := rfl
  rw [← hrange, interior_convexHull_affineBasis b]
  ext x
  simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_setOf_eq]
  constructor
  · intro hx
    let w : Fin 3 → ℝ := fun i => b.coord i x
    refine ⟨w, b.sum_coord_apply_eq_one x, ?_, ?_⟩
    · intro i
      have hi := hx i
      constructor
      · exact hi
      · have hsum := b.sum_coord_apply_eq_one x
        rw [Fin.sum_univ_three] at hsum
        have h0 := hx (0 : Fin 3)
        have h1 := hx (1 : Fin 3)
        have h2 := hx (2 : Fin 3)
        fin_cases i <;> dsimp [w] <;> nlinarith
    · exact b.affineCombination_coord_eq_self x
  · rintro ⟨w, hw, hwI, hwx⟩ i
    have hwx' : (Finset.univ.affineCombination ℝ p) w = x := by
      simpa [S] using hwx
    have hbp : (b : Fin 3 → Plane) = p := rfl
    rw [← hbp] at hwx'
    have hcoord := congrArg (b.coord i) hwx'.symm
    rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) hw] at hcoord
    exact hcoord ▸ (hwI i).1

/-- Every maximal face of a plane complex is a nondegenerate closed triangle. -/
theorem PlaneComplex.isTriangle_cellCarrier (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    IsTriangle (K.cellCarrier t) := by
  let T : K.toTriangleMesh.Triangle := ⟨t, ht⟩
  let q : Fin 3 → K.Vertex := K.toTriangleMesh.orderedVertex T
  let p : Fin 3 → Plane := K.position ∘ q
  refine ⟨p, K.toTriangleMesh.orderedVertex_affineIndependent T, ?_⟩
  rw [PlaneComplex.cellCarrier]
  congr 1
  change K.position '' (t : Set K.Vertex) = Set.range (K.position ∘ q)
  rw [Set.range_comp, show Set.range q = (t : Set K.Vertex) by
    exact K.toTriangleMesh.range_orderedVertex T]

/-- The frontier of a two-cell of a plane complex is covered facewise by its one-skeleton. -/
theorem PlaneComplex.frontier_cellCarrier_coveredBy_oneSkeleton (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    ∀ x ∈ frontier (K.cellCarrier t),
      ∃ s ∈ K.oneSkeleton.simplexes, x ∈ K.oneSkeleton.cellCarrier s ∧
        K.oneSkeleton.cellCarrier s ⊆ frontier (K.cellCarrier t) := by
  let T : K.toTriangleMesh.Triangle := ⟨t, ht⟩
  let q : Fin 3 → K.Vertex := K.toTriangleMesh.orderedVertex T
  let p : Fin 3 → Plane := K.position ∘ q
  have hp : AffineIndependent ℝ p := K.toTriangleMesh.orderedVertex_affineIndependent T
  let S : Affine.Simplex ℝ Plane 2 := { points := p, independent := hp }
  have hcell : K.cellCarrier t = S.closedInterior := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior S, PlaneComplex.cellCarrier]
    congr 1
    change K.position '' (t : Set K.Vertex) = Set.range (K.position ∘ q)
    rw [Set.range_comp, show Set.range q = (t : Set K.Vertex) by
      exact K.toTriangleMesh.range_orderedVertex T]
  have hfrontier : frontier (K.cellCarrier t) =
      ⋃ i : Fin 3, (S.faceOpposite i).closedInterior := by
    rw [hcell]
    have hclosed : IsClosed S.closedInterior := by
      rw [← Affine.Simplex.convexHull_eq_closedInterior S]
      exact (Set.finite_range p).isCompact_convexHull ℝ |>.isClosed
    rw [hclosed.frontier_eq,
      show interior S.closedInterior = S.interior by
        rw [← Affine.Simplex.convexHull_eq_closedInterior S]
        exact interior_convexHull_fin3_eq_simplex_interior p hp,
      S.closedInterior_sdiff_interior]
  intro x hx
  rw [hfrontier] at hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let qe : Fin 3 ↪ K.Vertex :=
    ⟨q, K.toTriangleMesh.orderedVertex_injective T⟩
  let s : Finset K.Vertex := (Finset.univ.erase i).map qe
  have hsSub : s ⊆ t := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
    exact K.toTriangleMesh.orderedVertex_mem T j
  have hscard : s.card = 2 := by
    change ((Finset.univ.erase i).map qe).card = 2
    rw [Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hsK : s ∈ K.simplexes := K.down_closed t (K.mem_simplexes_of_mem_cells ht)
    s hsSub (Finset.card_pos.mp (by omega))
  have hsOne : s ∈ K.oneSkeleton.simplexes :=
    K.mem_oneSkeleton_simplexes.mpr ⟨hsK, hscard.le⟩
  have hface : (S.faceOpposite i).closedInterior = K.cellCarrier s := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite i),
      PlaneComplex.cellCarrier, S.range_faceOpposite_points]
    congr 1
    ext z
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hji, rfl⟩
      refine ⟨q j, ?_, rfl⟩
      exact Finset.mem_map.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      exact ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩
  refine ⟨s, hsOne, ?_, ?_⟩
  · change x ∈ K.cellCarrier s
    rwa [← hface]
  · change K.cellCarrier s ⊆ frontier (K.cellCarrier t)
    rw [← hface, hfrontier]
    exact Set.subset_iUnion (fun i : Fin 3 => (S.faceOpposite i).closedInterior) i

theorem PlaneComplex.frontier_cellCarrier_subset_oneSkeleton_support (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    frontier (K.cellCarrier t) ⊆ K.oneSkeleton.support := by
  intro x hx
  obtain ⟨s, hs, hxs, -⟩ := K.frontier_cellCarrier_coveredBy_oneSkeleton ht x hx
  exact K.oneSkeleton.cellCarrier_subset_support hs hxs

/-- Every point of a pure complex lies in a maximal triangle. -/
theorem PlaneComplex.exists_cell_of_mem_support (K : PlaneComplex) (hpure : K.IsPure2)
    {x : Plane} (hx : x ∈ K.support) :
    ∃ t ∈ K.cells, x ∈ K.cellCarrier t := by
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
  exact ⟨t, Finset.mem_filter.mpr ⟨ht, htcard⟩,
    convexHull_mono (Set.image_mono hst) hxs⟩

/-- A vertex of a maximal triangle lies on its Euclidean frontier. -/
theorem PlaneComplex.position_mem_frontier_cellCarrier (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) {v : K.Vertex} (hv : v ∈ t) :
    K.position v ∈ frontier (K.cellCarrier t) := by
  let T : K.toTriangleMesh.Triangle := ⟨t, ht⟩
  have hvCell : K.position v ∈ K.cellCarrier t :=
    subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  rw [(K.isCompact_cellCarrier t).isClosed.frontier_eq]
  refine ⟨hvCell, ?_⟩
  intro hvInterior
  let v' : K.toTriangleMesh.Vertex := v
  have hv' : v' ∈ T.1 := hv
  have hdisjoint :=
    K.toTriangleMesh.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
      T (s := {v'}) (by simpa only [Finset.singleton_subset_iff] using hv') (by simp)
  have hvSingleton : K.toTriangleMesh.position v' ∈ convexHull ℝ
      (K.toTriangleMesh.position '' (({v'} : Finset K.toTriangleMesh.Vertex) :
        Set K.toTriangleMesh.Vertex)) :=
    subset_convexHull ℝ _ ⟨v', by simp, rfl⟩
  exact Set.disjoint_left.mp hdisjoint hvInterior hvSingleton

/-- The convex hull of at most two vertices of a maximal triangle lies in its frontier. -/
theorem PlaneComplex.convexHull_position_subset_frontier_cellCarrier (K : PlaneComplex)
    {s t : Finset K.Vertex} (ht : t ∈ K.cells) (hst : s ⊆ t) (hscard : s.card ≤ 2) :
    convexHull ℝ (K.position '' (s : Set K.Vertex)) ⊆ frontier (K.cellCarrier t) := by
  let T : K.toTriangleMesh.Triangle := ⟨t, ht⟩
  let s' : Finset K.toTriangleMesh.Vertex := s
  have hs'T : s' ⊆ T.1 := hst
  have hs'card : s'.card ≤ 2 := hscard
  have hdisjoint :=
    K.toTriangleMesh.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
      T hs'T hs'card
  intro x hx
  rw [(K.isCompact_cellCarrier t).isClosed.frontier_eq]
  refine ⟨convexHull_mono (Set.image_mono hst) hx, ?_⟩
  intro hxInterior
  exact Set.disjoint_left.mp hdisjoint hxInterior hx

/-- A used complex vertex outside a maximal face is not geometrically contained in that face. -/
theorem PlaneComplex.position_not_mem_cellCarrier_of_not_mem (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) {v : K.Vertex}
    (hvUsed : ({v} : Finset K.Vertex) ∈ K.simplexes) (hv : v ∉ t) :
    K.position v ∉ K.cellCarrier t := by
  intro hvCell
  have hvSingleton : K.position v ∈ K.cellCarrier ({v} : Finset K.Vertex) := by
    simp [PlaneComplex.cellCarrier]
  have hinter := K.face_inter ({v} : Finset K.Vertex) hvUsed t
    (K.mem_simplexes_of_mem_cells ht)
  have hempty : ({v} : Finset K.Vertex) ∩ t = ∅ := by simp [hv]
  have hp : K.position v ∈
      K.cellCarrier ({v} : Finset K.Vertex) ∩ K.cellCarrier t :=
    ⟨hvSingleton, hvCell⟩
  change K.position v ∈
    convexHull ℝ (K.position '' (({v} : Finset K.Vertex) : Set K.Vertex)) ∩
      convexHull ℝ (K.position '' (t : Set K.Vertex)) at hp
  rw [hinter, hempty] at hp
  simp at hp

/-- A graph face meets a maximal-cell frontier only over vertices shared with that cell. -/
theorem PlaneComplex.cellCarrier_inter_frontier_subset_sharedCarrier (K : PlaneComplex)
    {s t : Finset K.Vertex} (hs : s ∈ K.oneSkeleton.simplexes) (ht : t ∈ K.cells) :
    K.oneSkeleton.cellCarrier s ∩ frontier (K.cellCarrier t) ⊆
      K.cellCarrier (s ∩ t) := by
  rintro x ⟨hxs, hxFrontier⟩
  obtain ⟨u, hu, hxu, huFrontier⟩ :=
    K.frontier_cellCarrier_coveredBy_oneSkeleton ht x hxFrontier
  let uK : Finset K.Vertex := u
  have hsK : s ∈ K.simplexes := (K.mem_oneSkeleton_simplexes.mp hs).1
  have huK : uK ∈ K.simplexes := (K.mem_oneSkeleton_simplexes.mp hu).1
  have hxuK : x ∈ K.cellCarrier uK := hxu
  have huFrontierK : K.cellCarrier uK ⊆ frontier (K.cellCarrier t) := huFrontier
  have hinter := K.face_inter s hsK uK huK
  have hxInter : x ∈ K.cellCarrier (s ∩ uK) := by
    change x ∈ convexHull ℝ (K.position '' ((s ∩ uK : Finset K.Vertex) : Set K.Vertex))
    rw [← hinter]
    exact ⟨hxs, hxuK⟩
  have huSubT : uK ⊆ t := by
    by_contra hnot
    obtain ⟨w, hwu, hwnt⟩ := Finset.not_subset.mp hnot
    have hwCarrier : K.position w ∈ K.cellCarrier uK :=
      subset_convexHull ℝ _ ⟨w, hwu, rfl⟩
    have hwFrontier := huFrontierK hwCarrier
    have hwCell : K.position w ∈ K.cellCarrier t :=
      (K.isCompact_cellCarrier t).isClosed.frontier_subset hwFrontier
    have hwFace : ({w} : Finset K.Vertex) ∈ K.simplexes :=
      K.down_closed uK huK {w} (by simpa using hwu) (Finset.singleton_nonempty w)
    exact K.position_not_mem_cellCarrier_of_not_mem ht hwFace hwnt hwCell
  have hsub : s ∩ uK ⊆ s ∩ t := by
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hv).1, huSubT (Finset.mem_inter.mp hv).2⟩
  exact convexHull_mono (Set.image_mono hsub) hxInter

/-- Removing from a graph face the carrier of its vertices shared with a maximal triangle leaves
a preconnected set.  In dimension one this is a point, a segment, or a half-open segment. -/
theorem PlaneComplex.isPreconnected_cellCarrier_sdiff_sharedCarrier (K : PlaneComplex)
    {s t : Finset K.Vertex} (hs : s ∈ K.oneSkeleton.simplexes) (_ : t ∈ K.cells)
    (hnot : ¬s ⊆ t) :
    IsPreconnected (K.oneSkeleton.cellCarrier s \ K.cellCarrier (s ∩ t)) := by
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s
    (K.mem_oneSkeleton_simplexes.mp hs).1)
  have hsle : s.card ≤ 2 := (K.mem_oneSkeleton_simplexes.mp hs).2
  rcases (show s.card = 1 ∨ s.card = 2 by omega) with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hv : v ∉ t := by simpa using hnot
    have hinter : ({v} : Finset K.Vertex) ∩ t = ∅ := by simp [hv]
    rw [hinter]
    simp only [PlaneComplex.cellCarrier, Finset.coe_empty,
      Set.image_empty, convexHull_empty, Set.sdiff_empty]
    exact (convex_convexHull ℝ _).isPreconnected
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hstwo
    have hpq : K.position v ≠ K.position w := K.position_injective.ne hvw
    by_cases hv : v ∈ t
    · have hw : w ∉ t := by
        intro hw
        apply hnot
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have himage : K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex) =
          {K.position v, K.position w} := by ext z; simp [eq_comm]
      have hset : K.oneSkeleton.cellCarrier ({v, w} : Finset K.Vertex) \
          K.cellCarrier (({v, w} : Finset K.Vertex) ∩ t) =
          AffineMap.lineMap (K.position v) (K.position w) '' Set.Ioc (0 : ℝ) 1 := by
        rw [show ({v, w} : Finset K.Vertex) ∩ t = {v} by ext z; simp [hv, hw]]
        rw [show K.oneSkeleton.cellCarrier ({v, w} : Finset K.Vertex) =
            segment ℝ (K.position v) (K.position w) by
          change convexHull ℝ (K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex)) = _
          rw [himage, convexHull_pair],
          show K.cellCarrier ({v} : Finset K.Vertex) = {K.position v} by
            simp [PlaneComplex.cellCarrier], segment_eq_image_lineMap]
        ext x
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hne⟩
          refine ⟨a, ⟨?_, ha.2⟩, rfl⟩
          have ha0 : a ≠ 0 := by
            intro ha0
            apply hne
            simp [ha0]
          exact lt_of_le_of_ne ha.1 (Ne.symm ha0)
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨a, ⟨ha.1.le, ha.2⟩, rfl⟩, ?_⟩
          simp only [Set.mem_singleton_iff]
          intro heq
          have heq' : AffineMap.lineMap (K.position v) (K.position w) a =
              AffineMap.lineMap (K.position v) (K.position w) (0 : ℝ) := by
            calc
              _ = K.position v := heq
              _ = _ := by simp
          exact ha.1.ne' (AffineMap.lineMap_injective ℝ hpq heq')
      rw [hset]
      let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap (K.position v) (K.position w)
      exact (convex_Ioc (0 : ℝ) 1).isPreconnected.image line
        line.continuous_of_finiteDimensional.continuousOn
    · by_cases hw : w ∈ t
      · have hset : K.oneSkeleton.cellCarrier ({v, w} : Finset K.Vertex) \
            K.cellCarrier (({v, w} : Finset K.Vertex) ∩ t) =
            AffineMap.lineMap (K.position v) (K.position w) '' Set.Ico (0 : ℝ) 1 := by
          have himage : K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex) =
              {K.position v, K.position w} := by ext z; simp [eq_comm]
          rw [show ({v, w} : Finset K.Vertex) ∩ t = {w} by ext z; simp [hv, hw]]
          rw [show K.oneSkeleton.cellCarrier ({v, w} : Finset K.Vertex) =
              segment ℝ (K.position v) (K.position w) by
            change convexHull ℝ (K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex)) = _
            rw [himage, convexHull_pair],
            show K.cellCarrier ({w} : Finset K.Vertex) = {K.position w} by
              simp [PlaneComplex.cellCarrier], segment_eq_image_lineMap]
          ext x
          constructor
          · rintro ⟨⟨a, ha, rfl⟩, hne⟩
            refine ⟨a, ⟨ha.1, ?_⟩, rfl⟩
            have ha1 : a ≠ 1 := by
              intro ha1
              apply hne
              simp [ha1]
            exact lt_of_le_of_ne ha.2 ha1
          · rintro ⟨a, ha, rfl⟩
            refine ⟨⟨a, ⟨ha.1, ha.2.le⟩, rfl⟩, ?_⟩
            simp only [Set.mem_singleton_iff]
            intro heq
            have heq' : AffineMap.lineMap (K.position v) (K.position w) a =
                AffineMap.lineMap (K.position v) (K.position w) (1 : ℝ) := by
              calc
                _ = K.position w := heq
                _ = _ := by simp
            exact ha.2.ne (AffineMap.lineMap_injective ℝ hpq heq')
        rw [hset]
        let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap (K.position v) (K.position w)
        exact (convex_Ico (0 : ℝ) 1).isPreconnected.image line
          line.continuous_of_finiteDimensional.continuousOn
      · have hinter : ({v, w} : Finset K.Vertex) ∩ t = ∅ := by ext z; simp [hv, hw]
        rw [hinter]
        simp only [PlaneComplex.cellCarrier, Finset.coe_empty,
          Set.image_empty, convexHull_empty, Set.sdiff_empty]
        exact (convex_convexHull ℝ _).isPreconnected

/-- Refine a polygonal presentation of a complex support so that every used complex vertex is
an explicit polygon vertex. -/
theorem PolygonalCircle.exists_refinement_containing_complex_vertices
    (J : PolygonalCircle) (K : PlaneComplex) (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support) :
    ∃ J' : PolygonalCircle, J'.carrier = J.carrier ∧
      ∀ v : K.Vertex, J'.IsVertexPoint (K.position v) := by
  let F : Finset Plane := Finset.univ.image K.position
  have hF : ∀ p ∈ F, p ∈ J.carrier := by
    intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
    rw [← hsupport]
    exact hvertex v
  obtain ⟨J', hcarrier, hvertices⟩ := J.exists_refinement_vertices F hF
  refine ⟨J', hcarrier, fun v => hvertices (K.position v) ?_⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- If every vertex of a graph complex supported on a polygon is among the polygon vertices,
then each polygon edge lies in a single graph face. -/
theorem PlaneComplex.exists_face_containing_polygon_edge
    (K : PlaneComplex) (J : PolygonalCircle)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ J.carrier →
      J.IsVertexPoint (K.position v))
    (i : ZMod J.n) :
    ∃ s ∈ K.simplexes, J.edgeSegment i ⊆ K.cellCarrier s := by
  let P := J.vertex i
  let Q := J.vertex (i + 1)
  let m := AffineMap.lineMap P Q (1 / 2 : ℝ)
  have hPQ : P ≠ Q := J.adjacent_ne i
  have hmOpen : m ∈ openSegment ℝ P Q := by
    exact lineMap_mem_openSegment ℝ P Q (by constructor <;> norm_num)
  have hmEdge : m ∈ J.edgeSegment i :=
    openSegment_subset_segment ℝ P Q hmOpen
  have hmSupport : m ∈ K.support := by
    rw [hsupport]
    exact J.edgeSegment_subset_carrier i hmEdge
  rw [PlaneComplex.support] at hmSupport
  simp only [Set.mem_iUnion] at hmSupport
  obtain ⟨s, hs, hms⟩ := hmSupport
  have hm_ne_left : m ≠ P := by
    intro h
    rw [h] at hmOpen
    exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hmOpen)
  have hm_ne_right : m ≠ Q := by
    intro h
    rw [h] at hmOpen
    exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hmOpen)
  have hm_ne_vertex (v : K.Vertex) : m ≠ K.position v := by
    intro hmv
    have hvEdge : K.position v ∈ J.edgeSegment i := by
      rw [← hmv]
      exact hmEdge
    rcases (hvertex v (J.edgeSegment_subset_carrier i hvEdge)).mem_edgeSegment_iff i |>.mp
      hvEdge with hv | hv
    · exact hm_ne_left (hmv.trans hv)
    · exact hm_ne_right (hmv.trans hv)
  have hscard : s.card = 2 := by
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hsle := hgraph s hs
    have hone_or_two : s.card = 1 ∨ s.card = 2 := by omega
    rcases hone_or_two with hone | htwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hmv : m = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hms
      exact (hm_ne_vertex v hmv).elim
    · exact htwo
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hscard
  let A := K.position v
  let B := K.position w
  have hAB : A ≠ B := by
    intro h
    exact hvw (K.position_injective (by simpa [A, B] using h))
  have himage : K.position '' (({v, w} : Finset K.Vertex) : Set K.Vertex) =
      ({K.position v, K.position w} : Set Plane) := by
    ext x
    simp [eq_comm]
  have hmABSegment : m ∈ segment ℝ A B := by
    simpa only [PlaneComplex.cellCarrier, himage, convexHull_pair, A, B] using hms
  have hmAB : m ∈ openSegment ℝ A B := by
    rw [← insert_endpoints_openSegment] at hmABSegment
    rcases hmABSegment with h | h | h
    · exact (hm_ne_vertex v (by simpa [A] using h)).elim
    · exact (hm_ne_vertex w (by simpa [B] using h)).elim
    · exact h
  have hbaseAB : segment ℝ A B ⊆ J.carrier := by
    rw [← hsupport]
    simpa only [PlaneComplex.cellCarrier, himage, convexHull_pair, A, B] using
      (K.cellCarrier_subset_support hs)
  obtain ⟨y, hym, hyEdge, hyAB⟩ :=
    J.exists_second_basePoint_of_edge_inter_openSegment hAB hbaseAB hmEdge hmAB
  have hmPQline : m ∈ affineSpan ℝ ({P, Q} : Set Plane) :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨1 / 2, rfl⟩
  have hyPQline : y ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [PolygonalCircle.edgeSegment, segment_eq_image_lineMap] at hyEdge
    obtain ⟨r, -, hry⟩ := hyEdge
    exact ⟨r, by simpa [P, Q] using hry⟩
  have hmABline : m ∈ affineSpan ℝ ({A, B} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [openSegment_eq_image_lineMap] at hmAB
    exact ⟨hmAB.choose, hmAB.choose_spec.2⟩
  have hyABline : y ∈ affineSpan ℝ ({A, B} : Set Plane) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    rw [segment_eq_image_lineMap] at hyAB
    obtain ⟨r, -, hry⟩ := hyAB
    exact ⟨r, hry⟩
  have hlinePQ : affineSpan ℝ ({m, y} : Set Plane) =
      affineSpan ℝ ({P, Q} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hmPQline hyPQline hym.symm
  have hlineAB : affineSpan ℝ ({m, y} : Set Plane) =
      affineSpan ℝ ({A, B} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hmABline hyABline hym.symm
  have hABlinePQ : affineSpan ℝ ({A, B} : Set Plane) =
      affineSpan ℝ ({P, Q} : Set Plane) := hlineAB.symm.trans hlinePQ
  have hAline : A ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [← hABlinePQ]
    exact subset_affineSpan ℝ ({A, B} : Set Plane) (by simp)
  have hBline : B ∈ affineSpan ℝ ({P, Q} : Set Plane) := by
    rw [← hABlinePQ]
    exact subset_affineSpan ℝ ({A, B} : Set Plane) (by simp)
  have hAoutside : A ∉ openSegment ℝ P Q := by
    intro hAopen
    have hAedge : A ∈ J.edgeSegment i :=
      openSegment_subset_segment ℝ P Q hAopen
    rcases (hvertex v (J.edgeSegment_subset_carrier i hAedge)).mem_edgeSegment_iff i |>.mp
      hAedge with hA | hA
    · have hA' : A = P := by simpa [A, P] using hA
      rw [hA'] at hAopen
      exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hAopen)
    · have hA' : A = Q := by simpa [A, Q] using hA
      rw [hA'] at hAopen
      exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hAopen)
  have hBoutside : B ∉ openSegment ℝ P Q := by
    intro hBopen
    have hBedge : B ∈ J.edgeSegment i :=
      openSegment_subset_segment ℝ P Q hBopen
    rcases (hvertex w (J.edgeSegment_subset_carrier i hBedge)).mem_edgeSegment_iff i |>.mp
      hBedge with hB | hB
    · have hB' : B = P := by simpa [B, P] using hB
      rw [hB'] at hBopen
      exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hBopen)
    · have hB' : B = Q := by simpa [B, Q] using hB
      rw [hB'] at hBopen
      exact hPQ ((right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hBopen)
  refine ⟨{v, w}, hs, ?_⟩
  simpa only [PolygonalCircle.edgeSegment, P, Q, PlaneComplex.cellCarrier,
    himage, convexHull_pair, A, B] using
      segment_subset_of_midpoint_mem_openSegment hPQ hAline hBline hmAB
        hAoutside hBoutside

/-- A facewise-affine embedding of a graph complex supported on a polygon transports that
polygon to a polygon whose carrier is the exact image. -/
theorem PolygonalCircle.exists_mapEmbedding_of_affineOn_complex
    (J : PolygonalCircle) (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = J.carrier)
    (hvertex : ∀ v : K.Vertex, J.IsVertexPoint (K.position v))
    {f : Plane → Plane} (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    ∃ J' : PolygonalCircle, J'.carrier = f '' J.carrier := by
  have hinjJ : Set.InjOn f J.carrier := by simpa [← hsupport] using hinj
  have hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i =
        segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1))) := by
    intro i
    obtain ⟨s, hs, his⟩ :=
      K.exists_face_containing_polygon_edge J hgraph hsupport (fun v _ => hvertex v) i
    exact (haffine s hs).image_segment his
  let J' := J.mapEmbedding f hinjJ hedge
  exact ⟨J', J.mapEmbedding_carrier f hinjJ hedge⟩

/-- The image of a polygon under a PL embedding of its carrier is again a polygon. -/
theorem PolygonalCircle.exists_image_of_isPLOnSet_embedding (J : PolygonalCircle)
    {f : Plane → Plane} (hpl : IsPLOnSet J.carrier f)
    (hinj : Set.InjOn f J.carrier) :
    ∃ J' : PolygonalCircle, J'.carrier = f '' J.carrier := by
  obtain ⟨K, hKsupport, L, hLK, hLaffine⟩ := hpl
  let A : PlaneComplex := PlaneComplex.active L
  have hAsupport : A.support = J.carrier := by
    change (PlaneComplex.active L).support = J.carrier
    rw [L.active_support, hLK.1, hKsupport]
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    exact A.card_le_two_of_support_eq_frontier J.isCompact_closedRegion.isClosed
      (hAsupport.trans J.frontier_closedRegion.symm) hs
  have hAvertex : ∀ v : A.Vertex, A.position v ∈ A.support := by
    intro v
    change L.position v.1 ∈ (PlaneComplex.active L).support
    rw [L.active_support]
    exact v.2
  have hAaffine : ∀ s ∈ A.simplexes, IsAffineOn f (A.cellCarrier s) := by
    intro s hs
    exact Eq.mpr (congrArg (IsAffineOn f) (L.active_cellCarrier s))
      (hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs))
  obtain ⟨R, hRcarrier, hRvertices⟩ :=
    J.exists_refinement_containing_complex_vertices A hAsupport hAvertex
  have hARsupport : A.support = R.carrier := hAsupport.trans hRcarrier.symm
  obtain ⟨R', hR'image⟩ := R.exists_mapEmbedding_of_affineOn_complex A hAgraph
    hARsupport (fun v => hRvertices v) (by rw [hAsupport]; exact hinj) hAaffine
  exact ⟨R', by rw [hR'image, hRcarrier]⟩

/-- A connected set mapped off a polygon lies in its exterior as soon as one image point does.
This is the component argument used implicitly in Moise's proof of Chapter 6, Theorem 3. -/
theorem PolygonalCircle.mapsTo_exteriorRegion_of_isPreconnected (J : PolygonalCircle)
    {X : Type*} [TopologicalSpace X] {A : Set X} {f : X → Plane}
    (hA : IsPreconnected A)
    (hf : ContinuousOn f A) (hoff : Set.MapsTo f A J.carrierᶜ)
    (hexterior : ∃ x ∈ A, f x ∈ J.exteriorRegion) :
    Set.MapsTo f A J.exteriorRegion := by
  have himagePreconnected : IsPreconnected (f '' A) := hA.image f hf
  have himageSubset : f '' A ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    rw [J.interior_union_exterior]
    exact Set.image_subset_iff.mpr hoff
  obtain ⟨x, hxA, hxExterior⟩ := hexterior
  have hwitness : (f '' A ∩ J.exteriorRegion).Nonempty :=
    ⟨f x, ⟨x, hxA, rfl⟩, hxExterior⟩
  have hsub := himagePreconnected.subset_right_of_subset_union
    J.isOpen_interiorRegion J.isOpen_exteriorRegion
    J.disjoint_interior_exterior himageSubset hwitness
  exact Set.image_subset_iff.mp hsub

/-- Two polygonal disks have disjoint interiors if each boundary avoids the other interior and
the boundaries are genuinely different.  If the interiors met, connectedness would force one
bounded complementary component into the other; taking closures would then force every point of
its boundary into the other closed disk. -/
theorem PolygonalCircle.disjoint_interiorRegion_of_boundary_avoidance
    (J₁ J₂ : PolygonalCircle)
    (h₁₂ : Disjoint J₁.carrier J₂.interiorRegion)
    (h₂₁ : Disjoint J₂.carrier J₁.interiorRegion)
    (hdifferent : ∃ p ∈ J₂.carrier, p ∉ J₁.carrier) :
    Disjoint J₁.interiorRegion J₂.interiorRegion := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hJ₂off : J₂.interiorRegion ⊆ J₁.carrierᶜ := by
    intro y hy
    exact fun hyCarrier => Set.disjoint_left.mp h₁₂ hyCarrier hy
  have hJ₂split : J₂.interiorRegion ⊆ J₁.interiorRegion ∪ J₁.exteriorRegion := by
    rw [J₁.interior_union_exterior]
    exact hJ₂off
  have hJ₂inside : J₂.interiorRegion ⊆ J₁.interiorRegion :=
    J₂.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
      J₁.isOpen_interiorRegion J₁.isOpen_exteriorRegion
      J₁.disjoint_interior_exterior hJ₂split ⟨x, hx₂, hx₁⟩
  have hclosedSubset : J₂.closedRegion ⊆ J₁.closedRegion :=
    closure_mono hJ₂inside
  obtain ⟨p, hp₂, hpnot₁⟩ := hdifferent
  have hpClosed₂ : p ∈ J₂.closedRegion := by
    rw [J₂.closedRegion_eq_union]
    exact Or.inr hp₂
  have hpClosed₁ := hclosedSubset hpClosed₂
  rw [J₁.closedRegion_eq_union] at hpClosed₁
  rcases hpClosed₁ with hpInterior₁ | hpCarrier₁
  · exact Set.disjoint_left.mp h₂₁ hp₂ hpInterior₁
  · exact hpnot₁ hpCarrier₁

/-- The bounded region of a polygon lies in every closed ball containing its boundary. -/
theorem PolygonalCircle.closedRegion_subset_closedBall_of_carrier_subset
    (J : PolygonalCircle) {c : Plane} {r : ℝ}
    (hcarrier : J.carrier ⊆ Metric.closedBall c r) :
    J.closedRegion ⊆ Metric.closedBall c r := by
  have hr : 0 ≤ r := by
    have hv := hcarrier (J.vertex_mem_carrier 0)
    exact (dist_nonneg.trans (Metric.mem_closedBall.mp hv))
  have hinterior : J.interiorRegion ⊆ Metric.closedBall c r := by
    intro x hx
    rw [Metric.mem_closedBall]
    by_contra hnot
    have hdist : r < dist x c := lt_of_not_ge hnot
    let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap c x
    let ray : Set Plane := line '' Set.Ici (1 : ℝ)
    have hxRay : x ∈ ray := by
      refine ⟨1, Set.mem_Ici.mpr le_rfl, ?_⟩
      simp [line]
    have hrayPreconnected : IsPreconnected ray := by
      have hlineContinuous : ContinuousOn line (Set.Ici (1 : ℝ)) :=
        line.continuous_of_finiteDimensional.continuousOn
      exact (convex_Ici (1 : ℝ)).isPreconnected.image line hlineContinuous
    have hrayOff : ray ⊆ J.carrierᶜ := by
      rintro y ⟨t, ht, rfl⟩ hyCarrier
      have hyt := hcarrier hyCarrier
      rw [Metric.mem_closedBall] at hyt
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have hdformula : dist (AffineMap.lineMap c x t) c = t * dist x c := by
        rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht0, dist_comm c x]
      rw [hdformula] at hyt
      have hdle : dist x c ≤ t * dist x c :=
        by simpa using mul_le_mul_of_nonneg_right ht (dist_nonneg : 0 ≤ dist x c)
      exact (not_lt_of_ge (hdle.trans hyt)) hdist
    have hraySplit : ray ⊆ J.interiorRegion ∪ J.exteriorRegion := by
      rw [J.interior_union_exterior]
      exact hrayOff
    have hrayInside : ray ⊆ J.interiorRegion :=
      hrayPreconnected.subset_left_of_subset_union
        J.isOpen_interiorRegion J.isOpen_exteriorRegion
        J.disjoint_interior_exterior hraySplit ⟨x, hxRay, hx⟩
    obtain ⟨R, hR⟩ := J.isBounded_interiorRegion.subset_closedBall c
    let d := dist x c
    have hd : 0 < d := lt_of_le_of_lt hr hdist
    let t : ℝ := (|R| + 1) / d + 1
    have ht : 1 ≤ t := by
      dsimp [t]
      have : 0 ≤ (|R| + 1) / d := div_nonneg (by positivity) hd.le
      linarith
    let y := AffineMap.lineMap c x t
    have hyRay : y ∈ ray := ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hyBound := hR (hrayInside hyRay)
    rw [Metric.mem_closedBall] at hyBound
    have hydist : dist y c = t * d := by
      dsimp [y, d]
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) ht),
        dist_comm c x]
    rw [hydist] at hyBound
    have hRabs : R ≤ |R| := le_abs_self R
    dsimp [t] at hyBound
    field_simp [hd.ne'] at hyBound
    nlinarith
  rw [J.closedRegion_eq_union]
  exact Set.union_subset hinterior hcarrier

/-- A polygonal boundary with a continuous filling avoiding `p` has `p` on its unbounded side.

If `p` were inside the polygon, polygonal Schoenflies straightens its closed region to a
triangle. Radial projection from the image of `p`, followed by the inverse boundary
homeomorphism, would retract the source triangle onto its frontier, contradicting
`IsTriangle.no_retraction`. -/
theorem PolygonalCircle.mem_exteriorRegion_of_continuous_extension
    (J : PolygonalCircle) {C : Set Plane} (hC : IsTriangle C)
    {b F : Plane → Plane} {p : Plane}
    (hbcont : ContinuousOn b (frontier C))
    (hbinj : Set.InjOn b (frontier C))
    (hbimage : b '' frontier C = J.carrier)
    (hFcont : ContinuousOn F C)
    (hFeq : Set.EqOn F b (frontier C))
    (hpavoid : p ∉ F '' C) :
    p ∈ J.exteriorRegion := by
  have hCclosed : IsClosed C := hC.isCompact.isClosed
  have hpCarrier : p ∉ J.carrier := by
    intro hp
    rw [← hbimage] at hp
    obtain ⟨x, hx, hbx⟩ := hp
    apply hpavoid
    refine ⟨x, hCclosed.frontier_subset hx, ?_⟩
    rw [hFeq hx, hbx]
  have hpComplement : p ∈ J.carrierᶜ := hpCarrier
  rw [← J.interior_union_exterior] at hpComplement
  rcases hpComplement with hpInterior | hpExterior
  swap
  · exact hpExterior
  obtain ⟨straight, -, ⟨⟨D, hD, hboundary, hregion⟩, -⟩⟩ :=
    J.polygonal_schoenflies_rel Set.univ isOpen_univ (Set.subset_univ _)
  let q := straight p
  have hpClosedInterior : p ∈ interior J.closedRegion := by
    rwa [J.interior_closedRegion]
  have hqInterior : q ∈ interior D := by
    change straight p ∈ interior D
    rw [← hregion, ← straight.image_interior]
    exact ⟨p, hpClosedInterior, rfl⟩
  obtain ⟨R, hRcont, hRfix⟩ :=
    exists_radial_retraction_to_frontier hD.convex hD.isCompact.isBounded hqInterior
  let bD : frontier C → frontier D := fun x =>
    ⟨straight (b x.1), by
      rw [← hboundary, ← hbimage]
      exact ⟨b x.1, ⟨x.1, x.2, rfl⟩, rfl⟩⟩
  have hbDcont : Continuous bD := by
    apply Continuous.subtype_mk
    exact straight.continuous.comp
      (continuousOn_iff_continuous_restrict.mp hbcont)
  have hbDinj : Function.Injective bD := by
    intro x y hxy
    apply Subtype.ext
    apply hbinj x.2 y.2
    exact straight.injective (congrArg Subtype.val hxy)
  have hbDsurj : Function.Surjective bD := by
    intro y
    have hyImage : y.1 ∈ straight '' J.carrier := hboundary.symm ▸ y.2
    obtain ⟨z, hzCarrier, hzy⟩ := hyImage
    have hzImage : z ∈ b '' frontier C := hbimage.symm ▸ hzCarrier
    obtain ⟨x, hx, hbx⟩ := hzImage
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change straight (b x) = y.1
    rw [hbx, hzy]
  have hfrontierCompact : IsCompact (frontier C) :=
    hC.isCompact.of_isClosed_subset isClosed_frontier hCclosed.frontier_subset
  letI : CompactSpace (frontier C) :=
    isCompact_iff_compactSpace.mp hfrontierCompact
  let bHomeo : frontier C ≃ₜ frontier D :=
    (hbDcont.isClosedEmbedding hbDinj).isEmbedding.toHomeomorphOfSurjective hbDsurj
  let toPunctured : C → {x : Plane // x ≠ q} := fun x =>
    ⟨straight (F x.1), fun heq => by
      have hFp : F x.1 = p := straight.injective heq
      exact hpavoid ⟨x.1, x.2, hFp⟩⟩
  have htoPunctured : Continuous toPunctured := by
    apply Continuous.subtype_mk
    exact straight.continuous.comp
      (continuousOn_iff_continuous_restrict.mp hFcont)
  let r : C → frontier C := fun x => bHomeo.symm (R (toPunctured x))
  have hrcont : Continuous r :=
    bHomeo.symm.continuous.comp (hRcont.comp htoPunctured)
  have hrfix : ∀ z : frontier C,
      r ⟨z.1, hCclosed.frontier_subset z.2⟩ = z := by
    intro z
    have hto : toPunctured ⟨z.1, hCclosed.frontier_subset z.2⟩ =
        ⟨straight (b z.1), fun heq => by
          have hbp : b z.1 = p := straight.injective heq
          apply hpavoid
          exact ⟨z.1, hCclosed.frontier_subset z.2, by rw [hFeq z.2, hbp]⟩⟩ := by
      apply Subtype.ext
      exact congrArg straight (hFeq z.2)
    have hbDz : bD z =
        ⟨straight (b z.1), by
          rw [← hboundary, ← hbimage]
          exact ⟨b z.1, ⟨z.1, z.2, rfl⟩, rfl⟩⟩ := rfl
    have hRz : R (toPunctured ⟨z.1, hCclosed.frontier_subset z.2⟩) = bD z := by
      rw [hto, hbDz]
      apply Subtype.ext
      exact congrArg Subtype.val (hRfix (bD z))
    change bHomeo.symm
      (R (toPunctured ⟨z.1, hCclosed.frontier_subset z.2⟩)) = z
    rw [hRz]
    exact bHomeo.symm_apply_apply z
  exact False.elim (hC.no_retraction ⟨r, hrcont, hrfix⟩)

/-- A uniformly small perturbation of a triangle boundary has a uniformly small continuous
extension over the triangle.  This is the bounded, finite-dimensional Tietze extension theorem
applied to the displacement `b - h`. -/
theorem exists_continuous_extension_of_close_on_frontier
    {C : Set Plane} {b h : Plane → Plane} {r : ℝ}
    (hCclosed : IsClosed C) (hr : 0 < r)
    (hbcont : ContinuousOn b (frontier C)) (hhcont : ContinuousOn h C)
    (hclose : ∀ x ∈ frontier C, dist (b x) (h x) < r) :
    ∃ F : Plane → Plane,
      ContinuousOn F C ∧ Set.EqOn F b (frontier C) ∧
        ∀ x ∈ C, dist (F x) (h x) ≤ r := by
  let d : C(frontier C, Plane) :=
    ⟨fun x => b x.1 - h x.1,
      (continuousOn_iff_continuous_restrict.mp hbcont).sub
        (continuousOn_iff_continuous_restrict.mp
          (hhcont.mono hCclosed.frontier_subset))⟩
  letI : TietzeExtension (Metric.closedBall (0 : Plane) r) :=
    Metric.instTietzeExtensionClosedBall ℝ 0 hr
  have hdBall : ∀ x, d x ∈ Metric.closedBall (0 : Plane) r := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖b x.1 - h x.1‖ ≤ r
    rw [← dist_eq_norm]
    exact (hclose x.1 x.2).le
  obtain ⟨e, heBall, heq⟩ :=
    d.exists_forall_mem_restrict_eq isClosed_frontier hdBall
  let F : Plane → Plane := fun x => h x + e x
  refine ⟨F, hhcont.add e.continuous.continuousOn, ?_, ?_⟩
  · intro x hx
    have hex : e x = d ⟨x, hx⟩ := by
      exact congrArg (fun q : C(frontier C, Plane) => q ⟨x, hx⟩) heq
    change h x + e x = b x
    rw [hex]
    change h x + (b x - h x) = b x
    abel
  · intro x hx
    change dist (h x + e x) (h x) ≤ r
    rw [dist_eq_norm, add_sub_cancel_left]
    simpa [Metric.mem_closedBall, dist_zero_left] using heBall x

/-- PL maps compose on a polygon when the first map embeds it onto another polygon.

The proof refines the source polygon at the breakpoints of the first PL presentation and at the
preimages of the breakpoints of the second.  On the resulting cyclic edge complex both maps are
affine edge by edge. -/
theorem IsPLOnSet.comp_polygonal_embedding (J J' : PolygonalCircle)
    {f g : Plane → Plane} (hf : IsPLOnSet J.carrier f)
    (hinj : Set.InjOn f J.carrier) (himage : f '' J.carrier = J'.carrier)
    (hg : IsPLOnSet J'.carrier g) :
    IsPLOnSet J.carrier (g ∘ f) := by
  classical
  obtain ⟨K, hKsupport, L, hLK, hLaffine⟩ := hf
  let A : PlaneComplex := PlaneComplex.active L
  have hAsupport : A.support = J.carrier := by
    change (PlaneComplex.active L).support = J.carrier
    rw [L.active_support, hLK.1, hKsupport]
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    apply A.card_le_two_of_support_eq_frontier J.isCompact_closedRegion.isClosed
      (hAsupport.trans J.frontier_closedRegion.symm) hs
  have hAvertex : ∀ v : A.Vertex, A.position v ∈ A.support := by
    intro v
    change L.position v.1 ∈ (PlaneComplex.active L).support
    rw [L.active_support]
    exact v.2
  have hAaffine : ∀ s ∈ A.simplexes, IsAffineOn f (A.cellCarrier s) := by
    intro s hs
    exact Eq.mpr (congrArg (IsAffineOn f) (L.active_cellCarrier s))
      (hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs))
  obtain ⟨K', hK'support, L', hL'K', hL'affine⟩ := hg
  let B : PlaneComplex := PlaneComplex.active L'
  have hBsupport : B.support = J'.carrier := by
    change (PlaneComplex.active L').support = J'.carrier
    rw [L'.active_support, hL'K'.1, hK'support]
  have hBgraph : ∀ s ∈ B.simplexes, s.card ≤ 2 := by
    intro s hs
    apply B.card_le_two_of_support_eq_frontier J'.isCompact_closedRegion.isClosed
      (hBsupport.trans J'.frontier_closedRegion.symm) hs
  have hBvertex : ∀ v : B.Vertex, B.position v ∈ B.support := by
    intro v
    change L'.position v.1 ∈ (PlaneComplex.active L').support
    rw [L'.active_support]
    exact v.2
  have hBaffine : ∀ s ∈ B.simplexes, IsAffineOn g (B.cellCarrier s) := by
    intro s hs
    exact Eq.mpr (congrArg (IsAffineOn g) (L'.active_cellCarrier s))
      (hL'affine (s.map L'.activeEmbedding) (L'.mem_activeSimplexes.mp hs))
  have hBpreimage (v : B.Vertex) : ∃ x ∈ J.carrier, f x = B.position v := by
    have hv : B.position v ∈ J'.carrier := hBsupport ▸ hBvertex v
    rw [← himage] at hv
    obtain ⟨x, hx, hfx⟩ := hv
    exact ⟨x, hx, hfx⟩
  let preimage : B.Vertex → Plane := fun v => (hBpreimage v).choose
  have hpreimage_mem (v : B.Vertex) : preimage v ∈ J.carrier :=
    (hBpreimage v).choose_spec.1
  have hpreimage_eq (v : B.Vertex) : f (preimage v) = B.position v :=
    (hBpreimage v).choose_spec.2
  let breakpoints : Finset Plane :=
    (Finset.univ.image A.position) ∪ (Finset.univ.image preimage)
  have hbreakpoints : ∀ p ∈ breakpoints, p ∈ J.carrier := by
    intro p hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      rw [← hAsupport]
      exact hAvertex v
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      exact hpreimage_mem v
  obtain ⟨R, hRcarrier, hRvertices⟩ :=
    J.exists_refinement_vertices breakpoints hbreakpoints
  have hARsupport : A.support = R.carrier := hAsupport.trans hRcarrier.symm
  have hARvertices : ∀ v : A.Vertex, R.IsVertexPoint (A.position v) := by
    intro v
    apply hRvertices
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
  have hfEdge : ∀ i : ZMod R.n, IsAffineOn f (R.edgeSegment i) := by
    intro i
    obtain ⟨s, hs, his⟩ :=
      A.exists_face_containing_polygon_edge R hAgraph hARsupport
        (fun v _ => hARvertices v) i
    exact (hAaffine s hs).mono his
  have hedge : ∀ i : ZMod R.n,
      f '' R.edgeSegment i =
        segment ℝ (f (R.vertex i)) (f (R.vertex (i + 1))) := by
    intro i
    exact (hfEdge i).image_segment Set.Subset.rfl
  have hinjR : Set.InjOn f R.carrier := by
    rw [hRcarrier]
    exact hinj
  let R' : PolygonalCircle := R.mapEmbedding f hinjR hedge
  have hR'carrier : R'.carrier = J'.carrier := by
    calc
      R'.carrier = f '' R.carrier := R.mapEmbedding_carrier f hinjR hedge
      _ = f '' J.carrier := by rw [hRcarrier]
      _ = J'.carrier := himage
  have hBRsupport : B.support = R'.carrier := hBsupport.trans hR'carrier.symm
  have hBRvertices : ∀ v : B.Vertex, R'.IsVertexPoint (B.position v) := by
    intro v
    have hp : preimage v ∈ breakpoints :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
    obtain ⟨i, hi⟩ := hRvertices (preimage v) hp
    refine ⟨i, ?_⟩
    rw [R.mapEmbedding_vertex f hinjR hedge, hi, hpreimage_eq]
  have hgEdge : ∀ i : ZMod R'.n, IsAffineOn g (R'.edgeSegment i) := by
    intro i
    obtain ⟨s, hs, his⟩ :=
      B.exists_face_containing_polygon_edge R' hBgraph hBRsupport
        (fun v _ => hBRvertices v) i
    exact (hBaffine s hs).mono his
  have hcompEdge : ∀ i : ZMod R.n, IsAffineOn (g ∘ f) (R.edgeSegment i) := by
    intro i
    apply (hgEdge i).comp (hfEdge i)
    intro x hx
    change f x ∈ (R.mapEmbedding f hinjR hedge).edgeSegment i
    rw [R.mapEmbedding_edgeSegment f hinjR hedge i]
    exact ⟨x, hx, rfl⟩
  refine ⟨R.edgeComplex, R.edgeComplex_support.trans hRcarrier,
    R.edgeComplex, PlaneComplex.Subdivides.refl R.edgeComplex, ?_⟩
  intro s hs
  obtain ⟨-, i, hsi⟩ := R.mem_edgeFaces_iff.mp hs
  apply (hcompEdge i).mono
  have hpair : R.edgeComplex.cellCarrier
      ({i, i + 1} : Finset (ZMod R.n)) = R.edgeSegment i := by
    change convexHull ℝ (R.vertex '' (({i, i + 1} : Finset (ZMod R.n)) :
      Set (ZMod R.n))) = segment ℝ (R.vertex i) (R.vertex (i + 1))
    rw [← convexHull_pair]
    congr 1
    ext x
    simp [eq_comm]
  rw [← hpair]
  exact convexHull_mono (Set.image_mono hsi)

namespace PlaneComplex

/-- A finite plane complex is a combinatorial 2-manifold-with-boundary in the weak sense needed
by the approximation theorem: purely two-dimensional, with every edge in at most two cells.
(Moise additionally asks for connected vertex links; embeddability in the plane forces the link
conditions, so they are omitted from the hypothesis here — if the proof turns out to need them,
strengthen this predicate rather than weakening the theorem.) -/
def IsCombinatorial2ManifoldWithBoundary (K : PlaneComplex) : Prop :=
  K.IsPure2 ∧ ∀ e ∈ K.edges, (K.cells.filter fun s => e ⊆ s).card ≤ 2

/-- An injective map preserves the exact face-to-face intersection of two simplex carriers. -/
theorem image_cellCarrier_inter {K : PlaneComplex} {h : Plane → Plane}
    (hinj : Set.InjOn h K.support) {s t : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (ht : t ∈ K.simplexes) :
    h '' K.cellCarrier s ∩ h '' K.cellCarrier t =
      h '' K.cellCarrier (s ∩ t) := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨x, hxs, rfl⟩, z, hzt, hzx⟩
    have hxSupport := K.cellCarrier_subset_support hs hxs
    have hzSupport := K.cellCarrier_subset_support ht hzt
    have hzx' : z = x := hinj hzSupport hxSupport hzx
    subst z
    refine ⟨x, ?_, rfl⟩
    have hinter : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa only [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [← hinter]
    exact ⟨hxs, hzt⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst y
    have hsubS : K.cellCarrier (s ∩ t) ⊆ K.cellCarrier s :=
      convexHull_mono (Set.image_mono Finset.inter_subset_left)
    have hsubT : K.cellCarrier (s ∩ t) ⊆ K.cellCarrier t :=
      convexHull_mono (Set.image_mono Finset.inter_subset_right)
    exact ⟨⟨x, hsubS hx, rfl⟩, x, hsubT hx, rfl⟩

/-- Images of disjoint faces of an embedded finite graph admit disjoint metric thickenings. -/
theorem exists_disjoint_thickenings_image_cellCarriers {K : PlaneComplex}
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) {s t : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (ht : t ∈ K.simplexes) (hst : Disjoint s t) :
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

/-- A finite embedded two-complex has one positive separation radius which works for every
maximal cell and every complex vertex not belonging to that cell. -/
theorem exists_uniform_vertex_cell_separation (K : PlaneComplex)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (t : {t : Finset K.Vertex // t ∈ K.cells}) (v : K.Vertex),
        ({v} : Finset K.Vertex) ∈ K.simplexes → v ∉ t.1 →
          Disjoint (Metric.closedBall (h (K.position v)) r)
            (Metric.cthickening r (h '' K.cellCarrier t.1)) := by
  classical
  let I := Option ({t : Finset K.Vertex // t ∈ K.cells} × K.Vertex)
  let P : I → ℝ → Prop
    | none, _ => True
    | some (t, v), r =>
        v ∈ t.1 ∨ ({v} : Finset K.Vertex) ∉ K.simplexes ∨
          Disjoint (Metric.closedBall (h (K.position v)) r)
            (Metric.cthickening r (h '' K.cellCarrier t.1))
  have hlocal : ∀ i : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → P i r := by
    intro i
    rcases i with _ | ⟨t, v⟩
    · exact ⟨1, by norm_num, fun _ _ _ => trivial⟩
    · by_cases hvt : v ∈ t.1
      · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hvt⟩
      · by_cases hv : ({v} : Finset K.Vertex) ∈ K.simplexes
        swap
        · exact ⟨1, by norm_num, fun _ _ _ => Or.inr (Or.inl hv)⟩
        obtain ⟨ε, hε, hdis⟩ := K.exists_disjoint_thickenings_image_cellCarriers
          hcont hinj hv (K.mem_simplexes_of_mem_cells t.2)
          (Finset.disjoint_singleton_left.mpr hvt)
        refine ⟨ε, hε, fun r hr hrε => Or.inr (Or.inr ?_)⟩
        have hvCenter : h (K.position v) ∈ h '' K.cellCarrier {v} := by
          refine ⟨K.position v, subset_convexHull ℝ _ ?_, rfl⟩
          exact ⟨v, Finset.mem_singleton_self v, rfl⟩
        exact hdis.mono
          ((Metric.closedBall_subset_cthickening hvCenter r).trans
            (Metric.cthickening_subset_thickening' hε hrε _))
          (Metric.cthickening_subset_thickening' hε hrε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨r, hr, ?_⟩
  intro t v hv hvt
  have hP := huniform (some (t, v)) r hr (half_lt_self hε)
  rcases hP with hmem | hnotface | hdis
  · exact (hvt hmem).elim
  · exact (hnotface hv).elim
  · exact hdis

end PlaneComplex

namespace PlaneComplex

/-- A repositioning map is injective on the support of its source complex. -/
private theorem repositionMap_injOn_support (P : PlaneComplex)
    (qpos : P.Vertex → Plane) (qinj : Function.Injective qpos)
    (qaff : ∀ s ∈ P.simplexes, AffineIndependent ℝ fun v : s => qpos v)
    (qface : ∀ s ∈ P.simplexes, ∀ t ∈ P.simplexes,
      convexHull ℝ (qpos '' (s : Set P.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set P.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset P.Vertex) : Set P.Vertex))) :
    Set.InjOn (P.repositionMap qpos qinj qaff qface) P.support := by
  intro x hx y hy hxy
  have hxF : P.repositionMap qpos qinj qaff qface x =
      (P.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩).1 := by
    simp [PlaneComplex.repositionMap, hx]
  have hyF : P.repositionMap qpos qinj qaff qface y =
      (P.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩).1 := by
    simp [PlaneComplex.repositionMap, hy]
  have heq : P.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩ =
      P.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa [← hxF, ← hyF] using hxy
  exact congrArg Subtype.val
    ((P.repositionHomeomorphAll qpos qinj qaff qface).injective heq)

/-- A repositioning map carries the source support onto the repositioned support. -/
private theorem repositionMap_image_support (P : PlaneComplex)
    (qpos : P.Vertex → Plane) (qinj : Function.Injective qpos)
    (qaff : ∀ s ∈ P.simplexes, AffineIndependent ℝ fun v : s => qpos v)
    (qface : ∀ s ∈ P.simplexes, ∀ t ∈ P.simplexes,
      convexHull ℝ (qpos '' (s : Set P.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set P.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset P.Vertex) : Set P.Vertex))) :
    P.repositionMap qpos qinj qaff qface '' P.support =
      (P.reposition qpos qinj qaff qface).support := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P.support := hx
    have hFx : P.repositionMap qpos qinj qaff qface x =
        (P.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).1 := by
      simp [PlaneComplex.repositionMap, hx']
    rw [hFx]
    exact (P.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).2
  · intro hy
    obtain ⟨x, hx⟩ :=
      (P.repositionHomeomorphAll qpos qinj qaff qface).surjective ⟨y, hy⟩
    refine ⟨x.1, x.2, ?_⟩
    rw [show P.repositionMap qpos qinj qaff qface x.1 =
      (P.repositionHomeomorphAll qpos qinj qaff qface x).1 by
        simp [PlaneComplex.repositionMap, x.2]]
    exact congrArg Subtype.val hx

/-- Every face of a graph complex supporting a triangular frontier lies in an edge face. -/
private theorem exists_edge_face_of_support_eq_triangle (A : PlaneComplex)
    {C : Set Plane} (hC : IsTriangle C) (hAsupport : A.support = frontier C)
    (hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2)
    (hAvertex : ∀ v, A.position v ∈ A.support) :
    ∀ s ∈ A.simplexes, ∃ t ∈ A.simplexes, s ⊆ t ∧ t.card = 2 := by
  obtain ⟨J, hJcarrier⟩ := hC.exists_polygonalCircle
  have hAJsupport : A.support = J.carrier := hAsupport.trans hJcarrier.symm
  obtain ⟨R, hRcarrier, hRvertices⟩ :=
    J.exists_refinement_containing_complex_vertices A hAJsupport hAvertex
  have hARsupport : A.support = R.carrier := hAJsupport.trans hRcarrier.symm
  intro s hs
  have hspos : 0 < s.card := Finset.card_pos.mpr (A.nonempty_of_mem s hs)
  have hsle := hAgraph s hs
  rcases (show s.card = 1 ∨ s.card = 2 by omega) with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    obtain ⟨i, hi⟩ := hRvertices v
    obtain ⟨t, ht, hit⟩ := A.exists_face_containing_polygon_edge R hAgraph
      hARsupport (fun w _ => hRvertices w) i
    have hvIn : v ∈ t := by
      have hpBoth : A.position v ∈
          A.cellCarrier ({v} : Finset A.Vertex) ∩ A.cellCarrier t := by
        refine ⟨by simp [PlaneComplex.cellCarrier], hit ?_⟩
        rw [← hi]
        exact left_mem_segment ℝ _ _
      by_contra hvnot
      have hinter := A.face_inter ({v} : Finset A.Vertex) hs t ht
      have hempty : ({v} : Finset A.Vertex) ∩ t = ∅ := by simp [hvnot]
      rw [hempty] at hinter
      change A.position v ∈
        convexHull ℝ (A.position '' (({v} : Finset A.Vertex) : Set A.Vertex)) ∩
          convexHull ℝ (A.position '' (t : Set A.Vertex)) at hpBoth
      rw [hinter] at hpBoth
      simp at hpBoth
    have htcard : t.card = 2 := by
      have htpos : 0 < t.card := Finset.card_pos.mpr (A.nonempty_of_mem t ht)
      have htle := hAgraph t ht
      rcases (show t.card = 1 ∨ t.card = 2 by omega) with htone | httwo
      · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp htone
        have hleft : R.vertex i = A.position w := by
          simpa [PlaneComplex.cellCarrier] using
            hit (left_mem_segment ℝ (R.vertex i) (R.vertex (i + 1)))
        have hright : R.vertex (i + 1) = A.position w := by
          simpa [PlaneComplex.cellCarrier] using
            hit (right_mem_segment ℝ (R.vertex i) (R.vertex (i + 1)))
        exact (R.adjacent_ne i (hleft.trans hright.symm)).elim
      · exact httwo
    exact ⟨t, ht, by simpa using hvIn, htcard⟩
  · exact ⟨s, hs, Finset.Subset.rfl, hstwo⟩

end PlaneComplex

/-- A polygonal arc extracted from a broken line is the PL image of a straight segment. -/
theorem brokenLine_has_PL_segment_model {U : Set Plane} (B : BrokenLineData U) :
    ∃ (S : PlaneComplex) (F : Plane → Plane),
      S.support = segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) ∧
      IsPLOn S F ∧ Set.InjOn F S.support ∧ F '' S.support = B.resolvedCarrier ∧
      F (planePoint 0 0) = B.start ∧
      F (planePoint B.resolvedWalk.length 0) = B.finish := by
  let A : PlaneComplex := PlaneComplex.active B.resolvedComplex
  have hAvertex : ∀ v, A.position v ∈ A.support := by
    intro v
    change B.resolvedComplex.position v.1 ∈ A.support
    rw [B.resolvedComplex.active_support]
    exact v.2
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    have hsResolved := B.resolvedComplex.mem_activeSimplexes.mp hs
    calc
      s.card = (s.map B.resolvedComplex.activeEmbedding).card :=
        (Finset.card_map B.resolvedComplex.activeEmbedding).symm
      _ ≤ 2 := B.resolvedComplex_card_le_two hsResolved
  have hAaffine : ∀ s ∈ A.simplexes,
      IsAffineOn B.resolvedStraighten (A.cellCarrier s) := by
    intro s hs
    erw [B.resolvedComplex.active_cellCarrier]
    exact B.resolvedStraighten_affineOn_faces _
      (B.resolvedComplex.mem_activeSimplexes.mp hs)
  have hAinj : Set.InjOn B.resolvedStraighten A.support := by
    rw [B.resolvedComplex.active_support, B.resolvedComplex_support]
    exact B.resolvedStraighten_injectiveOn
  let S : PlaneComplex :=
    A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine
  have hSsupport : S.support =
      segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) := by
    change (A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine).support = _
    rw [A.mapGraph_support B.resolvedStraighten hAvertex hAinj hAgraph hAaffine,
      B.resolvedComplex.active_support, B.resolvedComplex_support,
      B.resolvedStraighten_image]
  let qpos : S.Vertex → Plane := A.position
  have qinj : Function.Injective qpos := A.position_injective
  have qaff : ∀ s ∈ S.simplexes, AffineIndependent ℝ fun v : s => qpos v := by
    intro s hs
    exact A.affineIndependent s hs
  have qface : ∀ s ∈ S.simplexes, ∀ t ∈ S.simplexes,
      convexHull ℝ (qpos '' (s : Set S.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set S.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset S.Vertex) : Set S.Vertex)) := by
    intro s hs t ht
    exact A.face_inter s hs t ht
  let F : Plane → Plane := S.repositionMap qpos qinj qaff qface
  have hRsupport : (S.reposition qpos qinj qaff qface).support = A.support := by
    rfl
  let v0R : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert 0, B.resolvedVertex_mem_support 0⟩
  let vnR : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert B.resolvedWalk.length,
      B.resolvedVertex_mem_support (Fin.last B.resolvedWalk.length)⟩
  let v0A : A.Vertex := v0R
  let vnA : A.Vertex := vnR
  let v0 : S.Vertex := v0A
  let vn : S.Vertex := vnA
  have hv0 : ({v0} : Finset S.Vertex) ∈ S.simplexes := by
    change ({v0R} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert 0} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face 0
  have hvn : ({vn} : Finset S.Vertex) ∈ S.simplexes := by
    change ({vnR} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert B.resolvedWalk.length} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face (Fin.last B.resolvedWalk.length)
  have hSpos0 : S.position v0 = planePoint 0 0 := by
    exact B.resolvedStraighten_start
  have hSposn : S.position vn = planePoint B.resolvedWalk.length 0 := by
    exact B.resolvedStraighten_finish
  have hqpos0 : qpos v0 = B.start := by
    exact B.resolvedVertex_start
  have hqposn : qpos vn = B.finish := by
    exact B.resolvedVertex_finish
  refine ⟨S, F, hSsupport, S.repositionMap_isPL qpos qinj qaff qface, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxF : F x =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hx]
    have hyF : F y =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hy]
    have heq : S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩ =
        S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [← hxF, ← hyF] using hxy
    exact congrArg Subtype.val
      ((S.repositionHomeomorphAll qpos qinj qaff qface).injective heq)
  · rw [← B.resolvedComplex_support, ← B.resolvedComplex.active_support,
      ← hRsupport]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ S.support := hx
      have hFx : F x =
          (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).1 := by
        simp [F, PlaneComplex.repositionMap, hx']
      rw [hFx]
      exact (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).2
    · intro hy
      obtain ⟨x, hx⟩ :=
        (S.repositionHomeomorphAll qpos qinj qaff qface).surjective ⟨y, hy⟩
      refine ⟨x.1, x.2, ?_⟩
      rw [show F x.1 =
        (S.repositionHomeomorphAll qpos qinj qaff qface x).1 by
          simp [F, PlaneComplex.repositionMap, x.2]]
      exact congrArg Subtype.val hx
  · calc
      F (planePoint 0 0) = F (S.position v0) := congrArg F hSpos0.symm
      _ = qpos v0 := S.repositionMap_position qpos qinj qaff qface v0 hv0
      _ = B.start := hqpos0
  · calc
      F (planePoint B.resolvedWalk.length 0) = F (S.position vn) :=
        congrArg F hSposn.symm
      _ = qpos vn := S.repositionMap_position qpos qinj qaff qface vn hvn
      _ = B.finish := hqposn

/-- **Theorem boundary** (Moise Ch. 5, Thms. 3-6: combinatorial Schoenflies / cone extension).

A map that is PL and injective on the frontier of a triangle, carrying it onto the frontier of a
second triangle, extends to a map of the closed triangles with the same properties.  Moise proves
this by coning from an interior point: the extension is linear on each segment from the cone
point to the boundary. -/
theorem pl_extension_of_triangle_boundary {C C' : Set Plane}
    (hC : IsTriangle C) (hC' : IsTriangle C') {f : Plane → Plane}
    (hpl : IsPLOnSet (frontier C) f) (hinj : Set.InjOn f (frontier C))
    (himage : f '' frontier C = frontier C') :
    ∃ F : Plane → Plane,
      Set.EqOn F f (frontier C) ∧ ContinuousOn F C ∧ Set.InjOn F C ∧
      F '' C = C' ∧ IsPLOnSet C F ∧
        Nonempty (FinitePLHomeomorphBetween F C C') := by
  obtain ⟨K, hKsupport, hplK⟩ := hpl
  obtain ⟨L, hLK, hLaffine⟩ := hplK
  let A : PlaneComplex := PlaneComplex.active L
  have hAsupport : A.support = frontier C := by
    change (PlaneComplex.active L).support = frontier C
    rw [L.active_support, hLK.1, hKsupport]
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    exact A.card_le_two_of_support_eq_frontier hC.isCompact.isClosed hAsupport hs
  have hAvertex : ∀ v, A.position v ∈ A.support := by
    intro v
    change L.position v.1 ∈ (PlaneComplex.active L).support
    rw [L.active_support]
    exact v.2
  have hAaffine : ∀ s ∈ A.simplexes, IsAffineOn f (A.cellCarrier s) := by
    intro s hs
    exact Eq.mpr (congrArg (IsAffineOn f) (L.active_cellCarrier s))
      (hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs))
  have hApure1 :=
    A.exists_edge_face_of_support_eq_triangle hC hAsupport hAgraph hAvertex
  have hinjA : Set.InjOn f A.support := by
    rw [hAsupport]
    exact hinj
  let B : PlaneComplex := A.mapGraph f hAvertex hinjA hAgraph hAaffine
  have hBsupport : B.support = frontier C' := by
    change (A.mapGraph f hAvertex hinjA hAgraph hAaffine).support = frontier C'
    rw [A.mapGraph_support f hAvertex hinjA hAgraph hAaffine,
      hAsupport, himage]
  obtain ⟨c, hc, hcavoid⟩ := hC.exists_interior_not_mem_range A.position
  obtain ⟨c', hc', hc'avoid⟩ := hC'.exists_interior_not_mem_range B.position
  let P : PlaneComplex :=
    A.cone C hC.convex c hc hcavoid hAgraph hAsupport
  let Q : PlaneComplex :=
    B.cone C' hC'.convex c' hc' hc'avoid
      (fun s hs => by exact hAgraph s hs) hBsupport
  have hPsupport : P.support = C := by
    exact A.cone_support_eq C hC.convex hC.isCompact c hc hcavoid hAgraph hAsupport
      hC.frontier_nonempty
  have hPpure : P.IsPure2 := by
    intro u hu
    change u ∈ A.coneSimplexes at hu
    obtain ⟨huNonempty, s, hs, hus⟩ := A.mem_coneSimplexes_iff.mp hu
    obtain ⟨e, he, hse, hecard⟩ := hApure1 s hs
    let T : Finset P.Vertex := insert none (A.liftFace e)
    refine ⟨T, ?_, ?_, ?_⟩
    · change T ∈ A.coneSimplexes
      exact A.mem_coneSimplexes_iff.mpr
        ⟨⟨none, Finset.mem_insert_self none _⟩, e, he, Finset.Subset.rfl⟩
    · apply hus.trans
      exact Finset.insert_subset_insert none (Finset.map_subset_map.mpr hse)
    · calc
        T.card = (A.liftFace e).card + 1 := by
          apply Finset.card_insert_of_notMem
          intro hn
          obtain ⟨v, hv, hnone⟩ := Finset.mem_map.mp hn
          exact Option.some_ne_none v hnone
        _ = e.card + 1 := by simp [PlaneComplex.liftFace]
        _ = 3 := by omega
  have hQsupport : Q.support = C' := by
    exact B.cone_support_eq C' hC'.convex hC'.isCompact c' hc' hc'avoid
      (fun s hs => by exact hAgraph s hs) hBsupport hC'.frontier_nonempty
  have hsimplexes : P.simplexes = Q.simplexes := by rfl
  let qpos : P.Vertex → Plane := Q.position
  have qinj : Function.Injective qpos := Q.position_injective
  have qaff : ∀ s ∈ P.simplexes, AffineIndependent ℝ fun v : s => qpos v := by
    intro s hs
    exact Q.affineIndependent s (hsimplexes ▸ hs)
  have qface : ∀ s ∈ P.simplexes, ∀ t ∈ P.simplexes,
      convexHull ℝ (qpos '' (s : Set P.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set P.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset P.Vertex) : Set P.Vertex)) := by
    intro s hs t ht
    exact Q.face_inter s (hsimplexes ▸ hs) t (hsimplexes ▸ ht)
  let F : Plane → Plane := P.repositionMap qpos qinj qaff qface
  have hRsupport : (P.reposition qpos qinj qaff qface).support = C' := by
    change Q.support = C'
    exact hQsupport
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxA : x ∈ A.support := by
      rw [hAsupport]
      exact hx
    rw [PlaneComplex.support] at hxA
    simp only [Set.mem_iUnion] at hxA
    obtain ⟨s, hs, hxs⟩ := hxA
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := A.exists_weights_of_mem_cellCarrier hxs
    let w : P.Vertex → ℝ := A.coneWeights z
    let t : Finset P.Vertex := A.liftFace s
    have ht : t ∈ P.simplexes := by
      change t ∈ A.coneSimplexes
      apply A.mem_coneSimplexes_iff.mpr
      refine ⟨?_, s, hs, Finset.subset_insert none (A.liftFace s)⟩
      obtain ⟨v, hv⟩ := A.nonempty_of_mem s hs
      exact ⟨some v, by simp [t, PlaneComplex.liftFace, hv]⟩
    have hwsupp : ∀ v ∉ t, w v = 0 := by
      intro v hv
      cases v with
      | none => rfl
      | some v =>
          exact hzsupp v (by
            intro hvs
            apply hv
            exact Finset.mem_map.mpr ⟨v, hvs, rfl⟩)
    have hw0 : ∀ v, 0 ≤ w v := by
      intro v
      cases v with
      | none => exact le_rfl
      | some v => exact hz0 v
    have hw1 : ∑ v, w v = 1 := by
      change ∑ v, A.coneWeights z v = 1
      rw [A.sum_coneWeights]
      exact hz1
    let xr : GeometricRealization P.Vertex P.simplexes :=
      ⟨w, ⟨hw0, hw1⟩, t, ht, hwsupp⟩
    have hPbary : P.baryEval w = x := by
      change (A.cone C hC.convex c hc hcavoid hAgraph hAsupport).baryEval
        (A.coneWeights z) = x
      rw [A.cone_baryEval_coneWeights]
      exact hzeval
    have hF : F x = (P.reposition qpos qinj qaff qface).baryEval w := by
      rw [← hPbary]
      exact P.repositionMap_apply_realization qpos qinj qaff qface xr
    have htarget : (P.reposition qpos qinj qaff qface).baryEval w =
        (A.mapGraph f hAvertex hinjA hAgraph hAaffine).baryEval z := by
      change (∑ o : Option A.Vertex, A.coneWeights z o • qpos o) =
        ∑ v : A.Vertex, z v • f (A.position v)
      rw [Fintype.sum_option]
      simp only [PlaneComplex.coneWeights_none, zero_smul, zero_add,
        PlaneComplex.coneWeights_some]
      apply Finset.sum_congr rfl
      intro v hv
      rfl
    have hboundary : (A.mapGraph f hAvertex hinjA hAgraph hAaffine).baryEval z = f x := by
      rw [A.mapGraph_baryEval_eq f hAvertex hinjA hAgraph hAaffine hs
        hzsupp hz0 hz1, hzeval]
    rw [hF, htarget, hboundary]
  · rw [← hPsupport]
    rw [continuousOn_iff_continuous_restrict]
    have hcont : Continuous fun z : P.support =>
        (P.repositionHomeomorphAll qpos qinj qaff qface z).1 :=
      continuous_subtype_val.comp
        (P.repositionHomeomorphAll qpos qinj qaff qface).continuous
    convert hcont using 1
    funext z
    simp [Set.restrict, F, PlaneComplex.repositionMap, z.2]
  · rw [← hPsupport]
    exact P.repositionMap_injOn_support qpos qinj qaff qface
  · rw [← hPsupport, ← hRsupport]
    exact P.repositionMap_image_support qpos qinj qaff qface
  · exact ⟨P, hPsupport, P.repositionMap_isPL qpos qinj qaff qface⟩
  · refine ⟨{
      complex := P
      support_eq := hPsupport
      pure := hPpure
      vertex_mem_support := ?_
      affineOn := ?_
      injOn := ?_
      image_eq := ?_ }⟩
    · intro v
      rw [hPsupport]
      cases v with
      | none =>
          change c ∈ C
          exact interior_subset hc
      | some v =>
          change A.position v ∈ C
          apply hC.isCompact.isClosed.frontier_subset
          rw [← hAsupport]
          exact hAvertex v
    · intro s hs
      exact P.repositionMap_affineOn_face qpos qinj qaff qface hs
    · rw [← hPsupport]
      exact P.repositionMap_injOn_support qpos qinj qaff qface
    · rw [← hPsupport, ← hRsupport]
      exact P.repositionMap_image_support qpos qinj qaff qface

/-- A PL embedding of a triangular boundary onto a polygon extends over the polygonal disk.

The target polygon is straightened by the finite PL Schoenflies homeomorphism, the triangular
boundary problem is solved by coning, and the result is pulled back through the inverse
straightening using common subdivision. -/
theorem pl_extension_of_triangle_to_polygon_boundary {C : Set Plane}
    (hC : IsTriangle C) (J : PolygonalCircle) {f : Plane → Plane}
    (hpl : IsPLOnSet (frontier C) f) (hinj : Set.InjOn f (frontier C))
    (himage : f '' frontier C = J.carrier) :
    ∃ F : Plane → Plane,
      Set.EqOn F f (frontier C) ∧ ContinuousOn F C ∧ Set.InjOn F C ∧
      F '' C = J.closedRegion ∧ IsPLOnSet C F ∧
        Nonempty (FinitePLHomeomorphBetween F C J.closedRegion) := by
  obtain ⟨straight, straightPL, ⟨⟨D, hD, hboundary, hregion⟩, hfix⟩⟩ :=
    J.polygonal_schoenflies_rel Set.univ isOpen_univ (Set.subset_univ _)
  have hstraightBoundary : IsPLOnSet J.carrier straight :=
    straightPL.isPLOnSet_polygonal_frontier J J.closedRegionMesh_support
  obtain ⟨JC, hJC⟩ := hC.exists_polygonalCircle
  have hplJC : IsPLOnSet JC.carrier f := by simpa only [hJC] using hpl
  have himageJC : f '' JC.carrier = J.carrier := by simpa only [hJC] using himage
  have hcompPL : IsPLOnSet (frontier C) (straight ∘ f) := by
    have hcomp := IsPLOnSet.comp_polygonal_embedding JC J hplJC
      (by simpa only [hJC] using hinj) himageJC hstraightBoundary
    simpa only [hJC] using hcomp
  have hcompImage : (straight ∘ f) '' frontier C = frontier D := by
    rw [Set.image_comp, himage, hboundary]
  obtain ⟨E, hEboundary, hEcontinuous, hEinj, hEimage, hEpl, ⟨Ecert⟩⟩ :=
    pl_extension_of_triangle_boundary hC hD hcompPL
      (by
        intro x hx y hy hxy
        exact hinj hx hy (straight.injective hxy)) hcompImage
  let straightOnRegion : FinitePLHomeomorphOn straight J.closedRegion :=
    straightPL.congrSet J.closedRegionMesh_support
  let inverseOnD : FinitePLHomeomorphOn straight.symm D :=
    straightOnRegion.symm.congrSet hregion
  let H : Plane → Plane := straight.symm ∘ E
  let Hcert₀ : FinitePLHomeomorphBetween H C (straight.symm '' D) :=
    Ecert.transAmbient inverseOnD
  have hinverseRegion : straight.symm '' D = J.closedRegion := by
    rw [← hregion, Set.image_image]
    simp
  let Hcert : FinitePLHomeomorphBetween H C J.closedRegion :=
    Hcert₀.congrTarget hinverseRegion
  refine ⟨H, ?_, Hcert.continuousOn, Hcert.injOn, Hcert.image_eq,
    Hcert.isPLOnSet, ⟨Hcert⟩⟩
  intro x hx
  change straight.symm (E x) = f x
  rw [hEboundary hx]
  exact straight.symm_apply_apply (f x)

/-- The named graph-replacement subdivision restricts to the frontier of each maximal triangle,
and its polygonal image bounds a certified PL cell extension. -/
theorem PlaneComplex.exists_graphReplacement_cell_extension (K : PlaneComplex)
    {h : Plane → Plane}
    (hcont : ContinuousOn h K.oneSkeleton.support)
    (hinj : Set.InjOn h K.oneSkeleton.support)
    (D : K.oneSkeleton.VertexDiskControl h)
    (C : K.oneSkeleton.CentralTubeControl hcont D)
    {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    ∃ (J : PolygonalCircle) (F : Plane → Plane),
      J.carrier = K.oneSkeleton.graphReplacementMap hcont D C ''
        frontier (K.cellCarrier t) ∧
      Set.EqOn F (K.oneSkeleton.graphReplacementMap hcont D C)
        (frontier (K.cellCarrier t)) ∧
      ContinuousOn F (K.cellCarrier t) ∧
      Set.InjOn F (K.cellCarrier t) ∧
      F '' K.cellCarrier t = J.closedRegion ∧
      IsPLOnSet (K.cellCarrier t) F ∧
      Nonempty (FinitePLHomeomorphBetween F (K.cellCarrier t) J.closedRegion) := by
  let G := K.oneSkeleton
  let g := G.graphReplacementMap hcont D C
  let R := G.graphReplacementSubdivision hcont D C
  let A := frontier (K.cellCarrier t)
  let S := R.restrictToSet A
  have hAcovered : ∀ x ∈ A, ∃ s ∈ G.simplexes,
      x ∈ G.cellCarrier s ∧ G.cellCarrier s ⊆ A := by
    intro x hx
    exact K.frontier_cellCarrier_coveredBy_oneSkeleton ht x hx
  have hSsupport : S.support = A := by
    change
      ((G.markedEdgeSubdivision (G.graphBreakpointPoint hcont D C)).restrictToSet A).support = A
    exact G.markedEdgeSubdivision_restrictToSet_support_eq
      (G.graphBreakpointPoint hcont D C) K.oneSkeleton_isGraph A hAcovered
  have haffineR : ∀ u ∈ R.simplexes,
      IsAffineOn g (R.cellCarrier u) := by
    exact G.graphReplacementMap_affineOn_subdivision K.oneSkeleton_isGraph hcont D C
  have hplA : IsPLOnSet A g := by
    refine ⟨S, hSsupport, S, PlaneComplex.Subdivides.refl S, ?_⟩
    intro u hu
    have huR : u ∈ R.simplexes :=
      (R.mem_restrictToSet_simplexes_iff A).mp hu |>.1
    exact haffineR u huR
  have hAgraphSupport : A ⊆ G.support := by
    intro x hx
    obtain ⟨s, hs, hxs, -⟩ := hAcovered x hx
    exact G.cellCarrier_subset_support hs hxs
  have hinjA : Set.InjOn g A :=
    (G.graphReplacementMap_injectiveOn K.oneSkeleton_isGraph hcont hinj D C).mono
      hAgraphSupport
  have htriangle : IsTriangle (K.cellCarrier t) := K.isTriangle_cellCarrier ht
  obtain ⟨J₀, hJ₀⟩ := htriangle.exists_polygonalCircle
  have hplJ₀ : IsPLOnSet J₀.carrier g := by
    rw [hJ₀]
    exact hplA
  have hinjJ₀ : Set.InjOn g J₀.carrier := by
    rw [hJ₀]
    exact hinjA
  obtain ⟨J, hJ⟩ := J₀.exists_image_of_isPLOnSet_embedding hplJ₀ hinjJ₀
  have hJimage : J.carrier = g '' frontier (K.cellCarrier t) := by
    rw [hJ, hJ₀]
  obtain ⟨F, hFboundary, hFcont, hFinj, hFimage, hFpl, hFcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary htriangle J hplA hinjA hJimage.symm
  exact ⟨J, F, hJimage, hFboundary, hFcont, hFinj, hFimage, hFpl, hFcert⟩

/-- A certified PL filling of the polygonalized boundary of one maximal face. -/
structure PlaneComplex.CellExtensionData (K : PlaneComplex) (g : Plane → Plane)
    (t : {t : Finset K.Vertex // t ∈ K.cells}) where
  /-- The `polygon` declaration. -/
  polygon : PolygonalCircle
  /-- The `map` declaration. -/
  map : Plane → Plane
  polygon_carrier : polygon.carrier = g '' frontier (K.cellCarrier t.1)
  eqOn_frontier : Set.EqOn map g (frontier (K.cellCarrier t.1))
  continuousOn : ContinuousOn map (K.cellCarrier t.1)
  injOn : Set.InjOn map (K.cellCarrier t.1)
  image_eq : map '' K.cellCarrier t.1 = polygon.closedRegion
  isPLOnSet : IsPLOnSet (K.cellCarrier t.1) map
  finitePL : Nonempty
    (FinitePLHomeomorphBetween map (K.cellCarrier t.1) polygon.closedRegion)

namespace PlaneComplex.CellExtensionData

variable {K : PlaneComplex} {g : Plane → Plane}
variable {t : {t : Finset K.Vertex // t ∈ K.cells}}

/-- The cell interior maps into the bounded complementary component of its polygonal boundary. -/
theorem mapsTo_interiorRegion (E : K.CellExtensionData g t) :
    Set.MapsTo E.map (interior (K.cellCarrier t.1)) E.polygon.interiorRegion := by
  intro x hx
  have hxCell : x ∈ K.cellCarrier t.1 := interior_subset hx
  have hFxClosed : E.map x ∈ E.polygon.closedRegion := by
    rw [← E.image_eq]
    exact ⟨x, hxCell, rfl⟩
  rw [E.polygon.closedRegion_eq_union] at hFxClosed
  rcases hFxClosed with hFxInterior | hFxCarrier
  · exact hFxInterior
  · rw [E.polygon_carrier] at hFxCarrier
    obtain ⟨y, hyFrontier, hy⟩ := hFxCarrier
    have hyCell : y ∈ K.cellCarrier t.1 :=
      (K.isCompact_cellCarrier t.1).isClosed.frontier_subset hyFrontier
    have hmapsEqual : E.map x = E.map y := by
      rw [E.eqOn_frontier hyFrontier]
      exact hy.symm
    have hxy : x = y := E.injOn hxCell hyCell hmapsEqual
    subst y
    exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier hx hyFrontier

/-- Cell extensions chosen from one boundary map agree wherever their source cells overlap. -/
theorem family_eqOn_cell_inter
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (t u : {t : Finset K.Vertex // t ∈ K.cells}) :
    Set.EqOn (E t).map (E u).map
      (K.cellCarrier t.1 ∩ K.cellCarrier u.1) := by
  intro x hx
  by_cases htu : t = u
  · subst u
    rfl
  have htuVal : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  let T : K.toTriangleMesh.Triangle := ⟨t.1, t.2⟩
  let U : K.toTriangleMesh.Triangle := ⟨u.1, u.2⟩
  have hxFrontierT : x ∈ frontier (K.cellCarrier t.1) := by
    rw [(K.isCompact_cellCarrier t.1).isClosed.frontier_eq]
    refine ⟨hx.1, ?_⟩
    intro hxInterior
    exact Set.disjoint_left.mp
      (K.toTriangleMesh.disjoint_interior_triangleCarrier_triangleCarrier
        (T := T) (U := U) htuVal) hxInterior hx.2
  have hxFrontierU : x ∈ frontier (K.cellCarrier u.1) := by
    rw [(K.isCompact_cellCarrier u.1).isClosed.frontier_eq]
    refine ⟨hx.2, ?_⟩
    intro hxInterior
    exact Set.disjoint_left.mp
      (K.toTriangleMesh.disjoint_interior_triangleCarrier_triangleCarrier
        (T := U) (U := T) htuVal.symm) hxInterior hx.1
  rw [(E t).eqOn_frontier hxFrontierT, (E u).eqOn_frontier hxFrontierU]

end PlaneComplex.CellExtensionData

/-- Glue a chosen family of cell extensions as a function.  Coherence on overlaps is proved
separately by `CellExtensionData.family_eqOn_cell_inter`. -/
noncomputable def PlaneComplex.cellwiseExtensionMap (K : PlaneComplex)
    {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t) :
    Plane → Plane := by
  classical
  exact fun x =>
    if hx : ∃ t : {t : Finset K.Vertex // t ∈ K.cells}, x ∈ K.cellCarrier t.1 then
      (E (Classical.choose hx)).map x
    else x

theorem PlaneComplex.cellwiseExtensionMap_eqOn_cell (K : PlaneComplex)
    {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (t : {t : Finset K.Vertex // t ∈ K.cells}) :
    Set.EqOn (K.cellwiseExtensionMap E) (E t).map (K.cellCarrier t.1) := by
  classical
  intro x hx
  have hexists : ∃ u : {u : Finset K.Vertex // u ∈ K.cells},
      x ∈ K.cellCarrier u.1 := ⟨t, hx⟩
  rw [cellwiseExtensionMap, dif_pos hexists]
  exact PlaneComplex.CellExtensionData.family_eqOn_cell_inter E
    (Classical.choose hexists) t ⟨(Classical.choose_spec hexists), hx⟩

/-- A finite coherent family of certified cell extensions glues to one PL map on the whole
complex.  The common witness cuts the source by every barycentric coordinate line occurring in
any local certificate. -/
theorem PlaneComplex.cellwiseExtensionMap_isPL (K : PlaneComplex)
    (hpure : K.IsPure2) {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t) :
    IsPLOn K (K.cellwiseExtensionMap E) := by
  classical
  let cert (t : {t : Finset K.Vertex // t ∈ K.cells}) :=
    Classical.choice (E t).finitePL
  let source := K.toTriangleMesh
  let lines : List (Plane →ᵃ[ℝ] ℝ) :=
    (Finset.univ : Finset {t : Finset K.Vertex // t ∈ K.cells}).toList.flatMap
      fun t => (cert t).complex.toTriangleMesh.coordinateLines
  let R := source.refineByLines lines
  have hRsource : R.toPlaneComplex.Subdivides source.toPlaneComplex :=
    source.refineByLines_subdivides lines
  have hRK : R.toPlaneComplex.Subdivides K :=
    hRsource.trans (K.toTriangleMesh_toPlaneComplex_subdivides hpure)
  refine ⟨R.toPlaneComplex, hRK, ?_⟩
  intro s hs
  obtain ⟨-, r, hr, hsr⟩ := R.mem_faces_iff.mp hs
  let T : R.Triangle := ⟨r, hr⟩
  have hTsimplex : T.1 ∈ R.toPlaneComplex.simplexes := by
    apply R.mem_faces_iff.mpr
    have hcard : T.1.card = 3 := R.card_triangle T.1 T.2
    exact ⟨Finset.card_pos.mp (by omega), T.1, T.2, Finset.Subset.rfl⟩
  obtain ⟨q, hq, hTq⟩ := hRK.2 T.1 hTsimplex
  obtain ⟨t, ht, hqt, htcard⟩ := hpure q hq
  have htcell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
  let tc : {t : Finset K.Vertex // t ∈ K.cells} := ⟨t, htcell⟩
  have hTcell : R.triangleCarrier T.1 ⊆ K.cellCarrier tc.1 := by
    exact hTq.trans (convexHull_mono (Set.image_mono hqt))
  let target := (cert tc).complex.toTriangleMesh
  have htargetSupport : target.toPlaneComplex.support = K.cellCarrier tc.1 := by
    exact ((cert tc).complex.toTriangleMesh_support (cert tc).pure).trans
      (cert tc).support_eq
  have hlinesTarget : ∀ a ∈ target.coordinateLines, a ∈ lines := by
    intro a ha
    dsimp [lines]
    rw [List.mem_flatMap]
    exact ⟨tc, by simp, ha⟩
  obtain ⟨z, hzInterior⟩ := R.interior_triangleCarrier_nonempty T
  have hhit : (interior (R.triangleCarrier T.1) ∩
      target.toPlaneComplex.support).Nonempty := by
    refine ⟨z, hzInterior, ?_⟩
    rw [htargetSupport]
    exact hTcell (interior_subset hzInterior)
  obtain ⟨U, hTU⟩ :=
    source.exists_target_triangle_of_refineByLines_of_interior_inter_support
      target lines hlinesTarget T hhit
  have hUcell : U.1 ∈ (cert tc).complex.cells := U.2
  have hUsimplex : U.1 ∈ (cert tc).complex.simplexes :=
    (cert tc).complex.mem_simplexes_of_mem_cells hUcell
  obtain ⟨a, ha⟩ := (cert tc).affineOn U.1 hUsimplex
  refine ⟨a, fun x hx => ?_⟩
  have hxT : x ∈ R.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono hsr) hx
  have hxCell : x ∈ K.cellCarrier tc.1 := hTcell hxT
  rw [K.cellwiseExtensionMap_eqOn_cell E tc hxCell]
  exact ha (hTU hxT)

/-- The side condition needed to glue cell extensions injectively: the embedded global graph
does not enter the bounded interior selected for any cell boundary. -/
def PlaneComplex.CellExtensionData.GraphAvoidsInteriors
    (K : PlaneComplex) {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t) : Prop :=
  ∀ t, Disjoint (g '' K.oneSkeleton.support) (E t).polygon.interiorRegion

/-- Moise's finite side-control condition: the polygonal disk selected for a cell contains no
complex vertex outside that cell.  For a graph embedding this finite condition implies
`GraphAvoidsInteriors`; the propagation along nonincident edges is the combinatorial content of
the last paragraph of Chapter 6, Theorem 3. -/
def PlaneComplex.CellExtensionData.VerticesAvoidClosedRegions
    (K : PlaneComplex) {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t) : Prop :=
  ∀ (t : {t : Finset K.Vertex // t ∈ K.cells}) (v : K.Vertex),
    ({v} : Finset K.Vertex) ∈ K.simplexes → v ∉ t.1 →
      g (K.position v) ∉ (E t).polygon.closedRegion

/-- Moise's finite vertex-avoidance condition propagates over every graph face. -/
theorem PlaneComplex.CellExtensionData.graphAvoidsInteriors_of_verticesAvoid
    {K : PlaneComplex} {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (hcont : ContinuousOn g K.oneSkeleton.support)
    (hinj : Set.InjOn g K.oneSkeleton.support)
    (hvertices : VerticesAvoidClosedRegions K E) :
    GraphAvoidsInteriors K E := by
  intro t
  rw [Set.disjoint_left]
  rintro p ⟨x, hxSupport, rfl⟩ hpInterior
  rw [PlaneComplex.support] at hxSupport
  simp only [Set.mem_iUnion] at hxSupport
  obtain ⟨s, hs, hxs⟩ := hxSupport
  have hsK : s ∈ K.simplexes := (K.mem_oneSkeleton_simplexes.mp hs).1
  have hscard : s.card ≤ 2 := (K.mem_oneSkeleton_simplexes.mp hs).2
  have hinteriorCarrierDisjoint :
      Disjoint (E t).polygon.interiorRegion (E t).polygon.carrier := by
    rw [← (E t).polygon.interior_closedRegion,
      ← (E t).polygon.frontier_closedRegion]
    exact disjoint_interior_frontier
  by_cases hst : s ⊆ t.1
  · have hxFrontier : x ∈ frontier (K.cellCarrier t.1) :=
      K.convexHull_position_subset_frontier_cellCarrier t.2 hst hscard hxs
    have hgCarrier : g x ∈ (E t).polygon.carrier := by
      rw [(E t).polygon_carrier]
      exact ⟨x, hxFrontier, rfl⟩
    exact Set.disjoint_left.mp hinteriorCarrierDisjoint hpInterior hgCarrier
  · let A := K.oneSkeleton.cellCarrier s \ K.cellCarrier (s ∩ t.1)
    have hApreconnected : IsPreconnected A :=
      K.isPreconnected_cellCarrier_sdiff_sharedCarrier hs t.2 hst
    have hAsupport : A ⊆ K.oneSkeleton.support :=
      Set.sdiff_subset.trans (K.oneSkeleton.cellCarrier_subset_support hs)
    have hAoff : Set.MapsTo g A (E t).polygon.carrierᶜ := by
      intro z hz hgz
      rw [(E t).polygon_carrier] at hgz
      obtain ⟨y, hyFrontier, hgy⟩ := hgz
      have hySupport : y ∈ K.oneSkeleton.support :=
        K.frontier_cellCarrier_subset_oneSkeleton_support t.2 hyFrontier
      have hzy : z = y := hinj (hAsupport hz) hySupport hgy.symm
      apply hz.2
      apply K.cellCarrier_inter_frontier_subset_sharedCarrier hs t.2
      exact ⟨hz.1, hzy ▸ hyFrontier⟩
    obtain ⟨v, hvs, hvnt⟩ := Finset.not_subset.mp hst
    have hvFace : ({v} : Finset K.Vertex) ∈ K.simplexes :=
      K.down_closed s hsK {v} (Finset.singleton_subset_iff.mpr hvs)
        (Finset.singleton_nonempty v)
    have hvCellS : K.position v ∈ K.oneSkeleton.cellCarrier s :=
      subset_convexHull ℝ _ ⟨v, hvs, rfl⟩
    have hvNotShared : K.position v ∉ K.cellCarrier (s ∩ t.1) := by
      intro hvShared
      have hvCellT : K.position v ∈ K.cellCarrier t.1 :=
        convexHull_mono (Set.image_mono Finset.inter_subset_right) hvShared
      exact K.position_not_mem_cellCarrier_of_not_mem t.2 hvFace hvnt hvCellT
    have hvA : K.position v ∈ A := ⟨hvCellS, hvNotShared⟩
    have hgvNotClosed := hvertices t v hvFace hvnt
    have hgvNotInterior : g (K.position v) ∉ (E t).polygon.interiorRegion := by
      intro hgv
      apply hgvNotClosed
      rw [(E t).polygon.closedRegion_eq_union]
      exact Or.inl hgv
    have hgvNotCarrier : g (K.position v) ∉ (E t).polygon.carrier := by
      intro hgv
      apply hgvNotClosed
      rw [(E t).polygon.closedRegion_eq_union]
      exact Or.inr hgv
    have hgvExterior : g (K.position v) ∈ (E t).polygon.exteriorRegion := by
      have hoff : g (K.position v) ∈ (E t).polygon.carrierᶜ := hgvNotCarrier
      rw [← (E t).polygon.interior_union_exterior] at hoff
      exact hoff.resolve_left hgvNotInterior
    have hAExterior : Set.MapsTo g A (E t).polygon.exteriorRegion :=
      (E t).polygon.mapsTo_exteriorRegion_of_isPreconnected hApreconnected
        (hcont.mono hAsupport) hAoff ⟨K.position v, hvA, hgvExterior⟩
    by_cases hxShared : x ∈ K.cellCarrier (s ∩ t.1)
    · have hsharedSub : s ∩ t.1 ⊆ t.1 := Finset.inter_subset_right
      have hsharedCard : (s ∩ t.1).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_left).trans hscard
      have hxFrontier : x ∈ frontier (K.cellCarrier t.1) :=
        K.convexHull_position_subset_frontier_cellCarrier t.2 hsharedSub
          hsharedCard hxShared
      have hgCarrier : g x ∈ (E t).polygon.carrier := by
        rw [(E t).polygon_carrier]
        exact ⟨x, hxFrontier, rfl⟩
      exact Set.disjoint_left.mp hinteriorCarrierDisjoint hpInterior hgCarrier
    · have hgExterior := hAExterior ⟨hxs, hxShared⟩
      exact Set.disjoint_left.mp (E t).polygon.disjoint_interior_exterior
        hpInterior hgExterior

/-- Under graph-side compatibility, the bounded interiors selected for distinct cells are
disjoint. -/
theorem PlaneComplex.CellExtensionData.disjoint_polygon_interiors
    {K : PlaneComplex} {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (hinjGraph : Set.InjOn g K.oneSkeleton.support)
    (hside : GraphAvoidsInteriors K E)
    (t u : {t : Finset K.Vertex // t ∈ K.cells}) (htu : t ≠ u) :
    Disjoint (E t).polygon.interiorRegion (E u).polygon.interiorRegion := by
  have hcarrierGraph (a : {a : Finset K.Vertex // a ∈ K.cells}) :
      (E a).polygon.carrier ⊆ g '' K.oneSkeleton.support := by
    intro p hp
    rw [(E a).polygon_carrier] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨x, K.frontier_cellCarrier_subset_oneSkeleton_support a.2 hx, rfl⟩
  have htuVal : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  have hnotSubset : ¬u.1 ⊆ t.1 := by
    intro hsub
    have heq : u.1 = t.1 := Finset.eq_of_subset_of_card_le hsub (by
      rw [K.card_of_mem_cells u.2, K.card_of_mem_cells t.2])
    exact htuVal heq.symm
  obtain ⟨w, hwu, hwnt⟩ := Finset.not_subset.mp hnotSubset
  have hwFace : ({w} : Finset K.Vertex) ∈ K.simplexes :=
    K.down_closed u.1 (K.mem_simplexes_of_mem_cells u.2) {w}
      (by simpa using hwu) (Finset.singleton_nonempty w)
  have hwFrontierU : K.position w ∈ frontier (K.cellCarrier u.1) :=
    K.position_mem_frontier_cellCarrier u.2 hwu
  have hpU : g (K.position w) ∈ (E u).polygon.carrier := by
    rw [(E u).polygon_carrier]
    exact ⟨K.position w, hwFrontierU, rfl⟩
  have hpNotT : g (K.position w) ∉ (E t).polygon.carrier := by
    intro hpT
    rw [(E t).polygon_carrier] at hpT
    obtain ⟨y, hyFrontier, hyEq⟩ := hpT
    have hwSupport : K.position w ∈ K.oneSkeleton.support :=
      K.frontier_cellCarrier_subset_oneSkeleton_support u.2 hwFrontierU
    have hySupport : y ∈ K.oneSkeleton.support :=
      K.frontier_cellCarrier_subset_oneSkeleton_support t.2 hyFrontier
    have hwy : K.position w = y := hinjGraph hwSupport hySupport hyEq.symm
    have hwCellT : K.position w ∈ K.cellCarrier t.1 := by
      rw [hwy]
      exact (K.isCompact_cellCarrier t.1).isClosed.frontier_subset hyFrontier
    exact K.position_not_mem_cellCarrier_of_not_mem t.2 hwFace hwnt hwCellT
  apply (E t).polygon.disjoint_interiorRegion_of_boundary_avoidance (E u).polygon
  · exact (hside u).mono_left (hcarrierGraph t)
  · exact (hside t).mono_left (hcarrierGraph u)
  · exact ⟨g (K.position w), hpU, hpNotT⟩

/-- Cellwise PL extensions form a global embedding once their polygon interiors avoid the global
one-skeleton. -/
theorem PlaneComplex.cellwiseExtensionMap_injOn (K : PlaneComplex)
    (hpure : K.IsPure2) {g : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (hinjGraph : Set.InjOn g K.oneSkeleton.support)
    (hside : PlaneComplex.CellExtensionData.GraphAvoidsInteriors K E) :
    Set.InjOn (K.cellwiseExtensionMap E) K.support := by
  intro x hx y hy hxy
  obtain ⟨t, ht, hxt⟩ := K.exists_cell_of_mem_support hpure hx
  obtain ⟨u, hu, hyu⟩ := K.exists_cell_of_mem_support hpure hy
  let tc : {t : Finset K.Vertex // t ∈ K.cells} := ⟨t, ht⟩
  let uc : {t : Finset K.Vertex // t ∈ K.cells} := ⟨u, hu⟩
  have hfx : K.cellwiseExtensionMap E x = (E tc).map x :=
    K.cellwiseExtensionMap_eqOn_cell E tc hxt
  have hfy : K.cellwiseExtensionMap E y = (E uc).map y :=
    K.cellwiseExtensionMap_eqOn_cell E uc hyu
  have hmapsEq : (E tc).map x = (E uc).map y :=
    hfx.symm.trans (hxy.trans hfy)
  by_cases htu : tc = uc
  · have htuValEq : t = u := congrArg Subtype.val htu
    have hyTc : y ∈ K.cellCarrier tc.1 := by
      dsimp [tc]
      rwa [htuValEq]
    rw [← htu] at hmapsEq
    exact (E tc).injOn hxt hyTc hmapsEq
  have htuVal : t ≠ u := fun h => htu (Subtype.ext h)
  by_cases hxInterior : x ∈ interior (K.cellCarrier t)
  · have hfxInterior : (E tc).map x ∈ (E tc).polygon.interiorRegion :=
      (E tc).mapsTo_interiorRegion hxInterior
    by_cases hyInterior : y ∈ interior (K.cellCarrier u)
    · have hfyInterior : (E uc).map y ∈ (E uc).polygon.interiorRegion :=
        (E uc).mapsTo_interiorRegion hyInterior
      have hdisjoint :=
        PlaneComplex.CellExtensionData.disjoint_polygon_interiors
          E hinjGraph hside tc uc htu
      exact False.elim <| Set.disjoint_left.mp hdisjoint hfxInterior
        (by rw [hmapsEq]; exact hfyInterior)
    · have hyFrontier : y ∈ frontier (K.cellCarrier u) := by
        rw [(K.isCompact_cellCarrier u).isClosed.frontier_eq]
        exact ⟨hyu, hyInterior⟩
      have hyGraph : y ∈ K.oneSkeleton.support :=
        K.frontier_cellCarrier_subset_oneSkeleton_support hu hyFrontier
      have hfyGraph : (E uc).map y ∈ g '' K.oneSkeleton.support :=
        ⟨y, hyGraph, (E uc).eqOn_frontier hyFrontier |>.symm⟩
      exact False.elim <| Set.disjoint_left.mp (hside tc) hfyGraph
        (by rw [← hmapsEq]; exact hfxInterior)
  · have hxFrontier : x ∈ frontier (K.cellCarrier t) := by
      rw [(K.isCompact_cellCarrier t).isClosed.frontier_eq]
      exact ⟨hxt, hxInterior⟩
    have hxGraph : x ∈ K.oneSkeleton.support :=
      K.frontier_cellCarrier_subset_oneSkeleton_support ht hxFrontier
    by_cases hyInterior : y ∈ interior (K.cellCarrier u)
    · have hfyInterior : (E uc).map y ∈ (E uc).polygon.interiorRegion :=
        (E uc).mapsTo_interiorRegion hyInterior
      have hfxGraph : (E tc).map x ∈ g '' K.oneSkeleton.support :=
        ⟨x, hxGraph, (E tc).eqOn_frontier hxFrontier |>.symm⟩
      exact False.elim <| Set.disjoint_left.mp (hside uc) hfxGraph
        (by rw [hmapsEq]; exact hfyInterior)
    · have hyFrontier : y ∈ frontier (K.cellCarrier u) := by
        rw [(K.isCompact_cellCarrier u).isClosed.frontier_eq]
        exact ⟨hyu, hyInterior⟩
      have hyGraph : y ∈ K.oneSkeleton.support :=
        K.frontier_cellCarrier_subset_oneSkeleton_support hu hyFrontier
      apply hinjGraph hxGraph hyGraph
      calc
        g x = (E tc).map x := ((E tc).eqOn_frontier hxFrontier).symm
        _ = (E uc).map y := hmapsEq
        _ = g y := (E uc).eqOn_frontier hyFrontier

/-- Quantitative control for the glued cell extension.  If `h` oscillates by less than `η` on
each cell and the polygonalized graph is `δ`-close to `h`, then every filled cell moves points by
less than `δ + 2 * η`. -/
theorem PlaneComplex.cellwiseExtensionMap_dist_lt (K : PlaneComplex)
    (hpure : K.IsPure2) {g h : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    {δ η : ℝ}
    (hsmall : ∀ t ∈ K.cells, ∀ x ∈ K.cellCarrier t, ∀ y ∈ K.cellCarrier t,
      dist (h x) (h y) < η)
    (hgraphClose : ∀ x ∈ K.oneSkeleton.support, dist (g x) (h x) < δ) :
    ∀ x ∈ K.support,
      dist (K.cellwiseExtensionMap E x) (h x) < δ + 2 * η := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := K.exists_cell_of_mem_support hpure hx
  let tc : {t : Finset K.Vertex // t ∈ K.cells} := ⟨t, ht⟩
  obtain ⟨v, hv⟩ := K.nonempty_of_mem t (K.mem_simplexes_of_mem_cells ht)
  let c := h (K.position v)
  have hvCell : K.position v ∈ K.cellCarrier t :=
    subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hcarrierBall : (E tc).polygon.carrier ⊆ Metric.closedBall c (δ + η) := by
    intro p hp
    rw [(E tc).polygon_carrier] at hp
    obtain ⟨z, hzFrontier, rfl⟩ := hp
    have hzCell : z ∈ K.cellCarrier t :=
      (K.isCompact_cellCarrier t).isClosed.frontier_subset hzFrontier
    have hzGraph : z ∈ K.oneSkeleton.support :=
      K.frontier_cellCarrier_subset_oneSkeleton_support ht hzFrontier
    rw [Metric.mem_closedBall]
    exact (calc
      dist (g z) c ≤ dist (g z) (h z) + dist (h z) c := dist_triangle _ _ _
      _ < δ + η := add_lt_add (hgraphClose z hzGraph)
        (hsmall t ht z hzCell (K.position v) hvCell)).le
  have hclosedBall : (E tc).polygon.closedRegion ⊆ Metric.closedBall c (δ + η) :=
    (E tc).polygon.closedRegion_subset_closedBall_of_carrier_subset hcarrierBall
  have hmapClosed : K.cellwiseExtensionMap E x ∈ (E tc).polygon.closedRegion := by
    rw [K.cellwiseExtensionMap_eqOn_cell E tc hxt, ← (E tc).image_eq]
    exact ⟨x, hxt, rfl⟩
  have hfirst : dist (K.cellwiseExtensionMap E x) c ≤ δ + η :=
    Metric.mem_closedBall.mp (hclosedBall hmapClosed)
  calc
    dist (K.cellwiseExtensionMap E x) (h x) ≤
        dist (K.cellwiseExtensionMap E x) c + dist c (h x) := dist_triangle _ _ _
    _ < (δ + η) + η := add_lt_add_of_le_of_lt hfirst
      (hsmall t ht (K.position v) hvCell x hxt)
    _ = δ + 2 * η := by ring

/-- Package the cell extension produced from the named graph replacement. -/
theorem PlaneComplex.nonempty_cellExtensionData_graphReplacement (K : PlaneComplex)
    {h : Plane → Plane}
    (hcont : ContinuousOn h K.oneSkeleton.support)
    (hinj : Set.InjOn h K.oneSkeleton.support)
    (D : K.oneSkeleton.VertexDiskControl h)
    (C : K.oneSkeleton.CentralTubeControl hcont D)
    (t : {t : Finset K.Vertex // t ∈ K.cells}) :
    Nonempty (K.CellExtensionData
      (K.oneSkeleton.graphReplacementMap hcont D C) t) := by
  obtain ⟨J, F, hcarrier, heq, hcontinuous, hinjective, himage, hpl, hcert⟩ :=
    K.exists_graphReplacement_cell_extension hcont hinj D C t.2
  exact ⟨{
    polygon := J
    map := F
    polygon_carrier := hcarrier
    eqOn_frontier := heq
    continuousOn := hcontinuous
    injOn := hinjective
    image_eq := himage
    isPLOnSet := hpl
    finitePL := hcert }⟩

/-- Any PL embedding of a triangular frontier has a certified polygonal-disk extension. -/
theorem PlaneComplex.nonempty_cellExtensionData_of_boundary_isPL (K : PlaneComplex)
    {g : Plane → Plane}
    (hginj : Set.InjOn g K.oneSkeleton.support)
    (t : {t : Finset K.Vertex // t ∈ K.cells})
    (hpl : IsPLOnSet (frontier (K.cellCarrier t.1)) g) :
    Nonempty (K.CellExtensionData g t) := by
  have hfrontierGraph : frontier (K.cellCarrier t.1) ⊆ K.oneSkeleton.support :=
    K.frontier_cellCarrier_subset_oneSkeleton_support t.2
  have hinjFrontier : Set.InjOn g (frontier (K.cellCarrier t.1)) :=
    hginj.mono hfrontierGraph
  have htriangle : IsTriangle (K.cellCarrier t.1) := K.isTriangle_cellCarrier t.2
  obtain ⟨J₀, hJ₀⟩ := htriangle.exists_polygonalCircle
  have hplJ₀ : IsPLOnSet J₀.carrier g := by simpa only [hJ₀] using hpl
  have hinjJ₀ : Set.InjOn g J₀.carrier := by simpa only [hJ₀] using hinjFrontier
  obtain ⟨J, hJ⟩ := J₀.exists_image_of_isPLOnSet_embedding hplJ₀ hinjJ₀
  have hJimage : J.carrier = g '' frontier (K.cellCarrier t.1) := by
    rw [hJ, hJ₀]
  obtain ⟨F, hFboundary, hFcont, hFinj, hFimage, hFpl, hFcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary htriangle J hpl hinjFrontier hJimage.symm
  exact ⟨{
    polygon := J
    map := F
    polygon_carrier := hJimage
    eqOn_frontier := hFboundary
    continuousOn := hFcont
    injOn := hFinj
    image_eq := hFimage
    isPLOnSet := hFpl
    finitePL := hFcert }⟩

/-- A close graph approximation preserves the side of every cell boundary.  Bounded Tietze
extension turns the boundary displacement into a filling which stays inside the prescribed
vertex-to-cell thickening; `PolygonalCircle.mem_exteriorRegion_of_continuous_extension` then
detects the unbounded side. -/
theorem PlaneComplex.CellExtensionData.verticesAvoidClosedRegions_of_close
    (K : PlaneComplex) {g h : Plane → Plane}
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells}, K.CellExtensionData g t)
    (hgcont : ContinuousOn g K.oneSkeleton.support)
    (hginj : Set.InjOn g K.oneSkeleton.support)
    (hhcont : ContinuousOn h K.support)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ (t : {t : Finset K.Vertex // t ∈ K.cells}) (v : K.Vertex),
      ({v} : Finset K.Vertex) ∈ K.simplexes → v ∉ t.1 →
        Disjoint (Metric.closedBall (h (K.position v)) r)
          (Metric.cthickening r (h '' K.cellCarrier t.1)))
    (hvertex : ∀ v : K.Vertex, ({v} : Finset K.Vertex) ∈ K.simplexes →
      g (K.position v) = h (K.position v))
    (hclose : ∀ x ∈ K.oneSkeleton.support, dist (g x) (h x) < r) :
    VerticesAvoidClosedRegions K E := by
  intro t v hv hvnt
  have htriangle : IsTriangle (K.cellCarrier t.1) := K.isTriangle_cellCarrier t.2
  have hfrontierGraph : frontier (K.cellCarrier t.1) ⊆ K.oneSkeleton.support :=
    K.frontier_cellCarrier_subset_oneSkeleton_support t.2
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      htriangle.isCompact.isClosed hr (hgcont.mono hfrontierGraph)
      (hhcont.mono (K.cellCarrier_subset_support
        (K.mem_simplexes_of_mem_cells t.2)))
      (fun x hx => hclose x (hfrontierGraph hx))
  have hpavoid : h (K.position v) ∉ F '' K.cellCarrier t.1 := by
    rintro ⟨x, hx, hFx⟩
    have hpBall : h (K.position v) ∈
        Metric.closedBall (h (K.position v)) r :=
      Metric.mem_closedBall_self hr.le
    have hFthick : F x ∈ Metric.cthickening r (h '' K.cellCarrier t.1) := by
      apply Metric.mem_cthickening_of_dist_le (F x) (h x) r
        (h '' K.cellCarrier t.1)
      · exact ⟨x, hx, rfl⟩
      · exact hFclose x hx
    exact Set.disjoint_left.mp (hsep t v hv hvnt) hpBall (hFx ▸ hFthick)
  have hpExterior : h (K.position v) ∈ (E t).polygon.exteriorRegion := by
    apply (E t).polygon.mem_exteriorRegion_of_continuous_extension htriangle
      (hgcont.mono hfrontierGraph) (hginj.mono hfrontierGraph)
      (E t).polygon_carrier.symm hFcont hFeq hpavoid
  have hpNotClosed : h (K.position v) ∉ (E t).polygon.closedRegion := by
    intro hpClosed
    exact Set.disjoint_left.mp (E t).polygon.disjoint_closedRegion_exteriorRegion
      hpClosed hpExterior
  simpa only [hvertex v hv] using hpNotClosed

/-- **Topological side-stability boundary** in Moise Ch. 6, Thm. 3.

The simultaneous graph replacement is performed in pairwise separated vertex disks and edge
tubes.  Consequently an original complex vertex outside a triangular face remains on the
unbounded side of the replacement polygon for that face.  Equivalently, it does not belong to
the polygonal closed disk selected by any certified extension.

This is the precise content hidden in Moise's sentence
`f(σ) ⊂ N(h(σ), εσ)`.  It is a planar side-preservation (or mod-two winding)
statement, not a metric convexity estimate: its proof compares the replacement boundary with
the original embedded boundary in the complement of the outside vertex. -/
theorem PlaneComplex.graphReplacement_verticesAvoidClosedRegions (K : PlaneComplex)
    {g h : Plane → Plane}
    (hgcont : ContinuousOn g K.oneSkeleton.support)
    (hginj : Set.InjOn g K.oneSkeleton.support)
    (hhcont : ContinuousOn h K.support)
    (E : ∀ t : {t : Finset K.Vertex // t ∈ K.cells},
      K.CellExtensionData g t)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ (t : {t : Finset K.Vertex // t ∈ K.cells}) (v : K.Vertex),
      ({v} : Finset K.Vertex) ∈ K.simplexes → v ∉ t.1 →
        Disjoint (Metric.closedBall (h (K.position v)) r)
          (Metric.cthickening r (h '' K.cellCarrier t.1)))
    (hvertex : ∀ v : K.Vertex, ({v} : Finset K.Vertex) ∈ K.simplexes →
      g (K.position v) = h (K.position v))
    (hclose : ∀ x ∈ K.oneSkeleton.support, dist (g x) (h x) < r) :
    CellExtensionData.VerticesAvoidClosedRegions K E := by
  exact CellExtensionData.verticesAvoidClosedRegions_of_close K E hgcont hginj hhcont
    hr hsep hvertex hclose

/-- Moise Ch. 6, Thm. 2: PL approximation on one-dimensional complexes.

An embedding of the support of a finite one-dimensional complex into the plane can be
`ε`-approximated by a PL embedding that agrees with it on every vertex.  Moise's proof: choose a
fine subdivision, replace each small arc by a broken line in a small neighborhood (Ch. 6, Thm. 1,
which rests on the broken-line connectivity of open connected sets, Ch. 1), keeping the broken
lines disjoint except at shared endpoints. -/
theorem pl_approximation_one_skeleton (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      (∀ v : K.Vertex, f (K.position v) = h (K.position v)) ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε := by
  exact K.exists_graph_PL_approximation hgraph hcont hinj hε

/-- Moise Ch. 6, Thm. 3 in the generality used by its proof: PL approximation of an embedded
pure finite two-complex in the plane.

An embedding of the support of a pure finite two-complex into the plane can be
`ε`-approximated by a PL embedding.  Moise's proof: approximate on the one-skeleton by
Thm. 6.2, then extend across each 2-cell by the combinatorial Schoenflies theorem
(`pl_extension_of_triangle_boundary`), with the subdivision chosen fine enough that the extended
images of distinct cells have disjoint interiors.

The face-to-face plane-complex axioms and purity already provide all incidence properties used
in the argument; no separate link or edge-degree hypothesis is needed. -/
theorem pl_approximation_pure_two_complex (K : PlaneComplex)
    (hpure : K.IsPure2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε := by
  classical
  let η := ε / 8
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨L₀, hL₀pure, hL₀K, hsmall₀⟩ :=
    K.exists_subdivision_image_dist_lt hpure hcont hη
  let L := PlaneComplex.used L₀
  have hLpure : L.IsPure2 := hL₀pure.used
  have hLK : L.Subdivides K := PlaneComplex.used_subdivides_left hL₀K
  have hsmallL : ∀ t ∈ L.cells, ∀ x ∈ L.cellCarrier t,
      ∀ y ∈ L.cellCarrier t, dist (h x) (h y) < η := by
    intro t ht x hx y hy
    have htSimplex : t ∈ L.simplexes := (Finset.mem_filter.mp ht).1
    have htCard : t.card = 3 := (Finset.mem_filter.mp ht).2
    have htMapSimplex : t.map L₀.usedEmbedding ∈ L₀.simplexes :=
      L₀.mem_usedSimplexes.mp htSimplex
    have htMapCard : (t.map L₀.usedEmbedding).card = 3 := by
      exact (Finset.card_map _).trans htCard
    have htMapCell : t.map L₀.usedEmbedding ∈ L₀.cells :=
      Finset.mem_filter.mpr ⟨htMapSimplex, htMapCard⟩
    apply hsmall₀ (t.map L₀.usedEmbedding) htMapCell x
    · exact (L₀.used_cellCarrier t).subset hx
    · exact (L₀.used_cellCarrier t).subset hy
  have hcontL : ContinuousOn h L.support := by
    rw [hLK.1]
    exact hcont
  have hinjL : Set.InjOn h L.support := by
    rw [hLK.1]
    exact hinj
  let G := L.oneSkeleton
  have hcontG : ContinuousOn h G.support :=
    hcontL.mono L.oneSkeleton_support_subset
  have hinjG₀ : Set.InjOn h G.support :=
    hinjL.mono L.oneSkeleton_support_subset
  obtain ⟨r, hr, hsep⟩ := L.exists_uniform_vertex_cell_separation hcontL hinjL
  let ρ := min r (ε / 4)
  have hρ : 0 < ρ := lt_min hr (div_pos hε (by norm_num))
  obtain ⟨g, hplG, hinjG, hvertex, hgraphClose, -, hfacewise⟩ :=
    G.exists_graph_PL_approximation_facewise L.oneSkeleton_isGraph hcontG hinjG₀ hρ
  have hgraphCloseR : ∀ x ∈ G.support, dist (g x) (h x) < r := by
    intro x hx
    exact (hgraphClose x hx).trans_le (min_le_left r (ε / 4))
  let E : ∀ t : {t : Finset L.Vertex // t ∈ L.cells}, L.CellExtensionData g t :=
    fun t => Classical.choice (L.nonempty_cellExtensionData_of_boundary_isPL hinjG t
      (hfacewise (frontier (L.cellCarrier t.1)) fun x hx =>
        L.frontier_cellCarrier_coveredBy_oneSkeleton t.2 x hx))
  have hvertices : PlaneComplex.CellExtensionData.VerticesAvoidClosedRegions L E :=
    L.graphReplacement_verticesAvoidClosedRegions hplG.continuousOn hinjG hcontL E
      hr hsep (fun v _ => hvertex v) hgraphCloseR
  have hside : PlaneComplex.CellExtensionData.GraphAvoidsInteriors L E := by
    exact PlaneComplex.CellExtensionData.graphAvoidsInteriors_of_verticesAvoid E
      hplG.continuousOn hinjG hvertices
  let f := L.cellwiseExtensionMap E
  refine ⟨f, IsPLOn.of_subdivision hLK (L.cellwiseExtensionMap_isPL hLpure E), ?_, ?_⟩
  · rw [← hLK.1]
    exact L.cellwiseExtensionMap_injOn hLpure E hinjG hside
  · intro x hx
    have hbound := L.cellwiseExtensionMap_dist_lt hLpure E hsmallL hgraphClose x
      (by rwa [hLK.1])
    dsimp [f]
    have hρle : ρ ≤ ε / 4 := min_le_right r (ε / 4)
    dsimp [η] at hbound
    linarith

/-- Moise Ch. 6, Thm. 3 for a finite combinatorial two-manifold with boundary.  This public
surface-shaped interface is a direct specialization of
`pl_approximation_pure_two_complex`. -/
theorem pl_approximation_two_manifold (K : PlaneComplex)
    (hsurface : K.IsCombinatorial2ManifoldWithBoundary)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε :=
  pl_approximation_pure_two_complex K hsurface.1 hcont hinj hε

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_01
/- END ClassificationOfSurfaces.Moise.PLApproximation -/

/- BEGIN ClassificationOfSurfaces.Moise.AdaptiveOpenCover | 9636d4051be8fc93ad60298294c2f06596b9bd12ecd103cf6f8a9ecb85279228 -/
section schottkyclassification14_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Adaptive triangulations subordinate to an open cover

The adaptive fan construction only needs a hereditary, locally attainable notion of a safe
midpoint face.  This file instantiates that interface with containment in one member of an open
cover.  In particular, the resulting locally finite triangulation has every closed triangle in
one prescribed control neighborhood.  Quantitative chart approximation can therefore choose
the neighborhoods first and reuse the conforming triangulation unchanged.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- An open cover of `U` by subsets which remain inside `U`. -/
structure AdaptiveOpenCover where
  /-- The `Index` declaration. -/
  Index : Type
  /-- The `set` declaration. -/
  set : Index → Set K.realization
  isOpen : ∀ i, IsOpen (set i)
  subset : ∀ i, set i ⊆ U
  covers : ∀ {p : K.realization}, p ∈ U → ∃ i, p ∈ set i

namespace AdaptiveOpenCover

variable (C : K.AdaptiveOpenCover U)

/-- A level face is cover-safe when its complete carrier lies in one cover member. -/
@[reducible]
def safety : K.AdaptiveSafety U where
  safe t := ∃ i, K.levelFaceCarrier t ⊆ C.set i
  carrier_subset := by
    rintro n t ⟨i, hi⟩
    exact hi.trans (C.subset i)
  hereditary := by
    rintro n m s t hts ⟨i, hi⟩
    exact ⟨i, hts.trans hi⟩

/-- Subordination to an open cover is locally attainable under repeated midpoint subdivision. -/
theorem safety_isAdmissible :
    @AdaptiveSafety.IsAdmissible K U C.safety := by
  letI : K.AdaptiveSafety U := C.safety
  refine { exists_safe := ?_, locally_parent_safe := ?_ }
  · intro _ p hp
    obtain ⟨i, hpi⟩ := C.covers hp
    letI : K.AdaptiveSafety (C.set i) := K.defaultAdaptiveSafety (C.set i)
    letI : AdaptiveSafety.IsAdmissible (K := K) (U := C.set i) :=
      K.defaultAdaptiveSafety_admissible (C.set i)
    obtain ⟨n, t, ht, hpt⟩ :=
      K.exists_safeLevelFace_containing (C.set i) (C.isOpen i) hpi
    refine ⟨n, t, ⟨i, ?_⟩, hpt⟩
    exact AdaptiveSafety.carrier_subset (K := K) (U := C.set i) ht
  · intro _ p
    obtain ⟨i, hpi⟩ := C.covers p.2
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (C.isOpen i) p.1 hpi
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε2
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨ε, hε, N, ?_⟩
    intro n hNn t hinter
    refine ⟨i, ?_⟩
    obtain ⟨z, hzFace, hzBall⟩ := hinter
    have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
      K.levelFaceCarrier_subset_parent n t hzFace
    have hpow : (1 / 2 : ℝ) ^ n < ε / 2 :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hNn).trans_lt hN
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    calc
      dist y p.1 ≤ dist y z + dist z p.1 := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + dist z p.1 := by
        gcongr
        exact K.dist_le_pow_of_mem_levelFaceCarrier
          (K.levelParentFace n t) hy hzParent
      _ < ε / 2 + ε / 2 := add_lt_add hpow hzBall
      _ = ε := by ring

/-- The conforming adaptive triangle complex subordinate to `C`. -/
noncomputable def locallyFiniteTriangleComplex (hU : IsOpen U) :
    LocallyFiniteTriangleComplex U := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveLocallyFiniteTriangleComplex U hU

/-- The cover-subordinate adaptive complex covers all of `U`. -/
theorem locallyFiniteTriangleComplex_support (hU : IsOpen U) :
    (locallyFiniteTriangleComplex K U C hU).support = Set.univ := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveLocallyFiniteTriangleComplex_support U hU

/-- Distinct faces of the cover-subordinate adaptive complex carry distinct vertex triples. -/
theorem faceVertices_injective (hU : IsOpen U) :
    Function.Injective (locallyFiniteTriangleComplex K U C hU).faceVertices := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveGlobalFanFaceVertices_injective U hU

/-- Every adaptive tile selected by `C` lies in one member of the cover. -/
theorem exists_cover_set_of_adaptiveFace
    (t : @IntrinsicTwoComplex.AdaptiveFace K U C.safety) :
    ∃ i, @IntrinsicTwoComplex.adaptiveFaceCarrier K U C.safety t ⊆ C.set i := by
  letI : K.AdaptiveSafety U := C.safety
  rcases t with ⟨(_ | n), t⟩
  · exact t.2
  · exact t.2.1

/-- Every closed triangle of the conforming fan triangulation lies in one cover member. -/
theorem exists_cover_set_of_complex_face (hU : IsOpen U)
    (f : (locallyFiniteTriangleComplex K U C hU).Face) :
    ∃ i, Subtype.val ''
        ((locallyFiniteTriangleComplex K U C hU).faceCarrier f) ⊆ C.set i := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  obtain ⟨i, hi⟩ := exists_cover_set_of_adaptiveFace K U C f.1
  refine ⟨i, ?_⟩
  rintro p ⟨q, hq, rfl⟩
  change q ∈ Set.range (K.adaptiveGlobalFanFaceMap U hU f) at hq
  erw [K.range_adaptiveGlobalFanFaceMap U hU] at hq
  exact hi (K.range_adaptiveFanFaceMap_subset_tile U hU f hq)

end AdaptiveOpenCover
end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_02
/- END ClassificationOfSurfaces.Moise.AdaptiveOpenCover -/

/- BEGIN ClassificationOfSurfaces.Moise.ChartPatch | 331bb424ad6e50ca6c5ce294780505e5add65270b0aaf5ec3c92fc357d8e73fc -/
section schottkyclassification14_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# A fixed polygonal patch inside the Rado chart models

The four-triangle diamond below has vertices `(+-3/4,0)` and `(0,+-3/4)`.  It lies in the open
unit disk and contains the closed radius-`1/2` disk in its interior.  Its right half gives the
corresponding half-disk patch.  These strict margins are the concrete base geometry for the
Rado induction.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The anisotropic linear equivalence carrying Moise's fixed diamond, with vertices
`(+-1,0),(0,+-2)`, to the radius-`3/4` axis diamond. -/
noncomputable def chartDiamondLinearEquiv : Plane ≃ₗ[ℝ] Plane where
  toFun p := !₂[(3 / 4 : ℝ) * p 0, (3 / 8 : ℝ) * p 1]
  invFun p := !₂[(4 / 3 : ℝ) * p 0, (8 / 3 : ℝ) * p 1]
  left_inv p := by
    ext i
    fin_cases i <;> simp <;> ring
  right_inv p := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r p := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Affine form of `chartDiamondLinearEquiv`. -/
noncomputable def chartDiamondAffineEquiv : Plane ≃ᵃ[ℝ] Plane :=
  chartDiamondLinearEquiv.toAffineEquiv

@[simp] theorem chartDiamondAffineEquiv_apply_zero (p : Plane) :
    chartDiamondAffineEquiv p 0 = (3 / 4 : ℝ) * p 0 := rfl

@[simp] theorem chartDiamondAffineEquiv_apply_one (p : Plane) :
    chartDiamondAffineEquiv p 1 = (3 / 8 : ℝ) * p 1 := rfl

@[simp] theorem chartDiamondAffineEquiv_symm_apply_zero (p : Plane) :
    chartDiamondAffineEquiv.symm p 0 = (4 / 3 : ℝ) * p 0 := rfl

@[simp] theorem chartDiamondAffineEquiv_symm_apply_one (p : Plane) :
    chartDiamondAffineEquiv.symm p 1 = (8 / 3 : ℝ) * p 1 := rfl

/-- The fixed four-triangle chart patch. -/
noncomputable def chartDiamondMesh : TriangleMesh :=
  (diamondFanMesh 0 (by norm_num) (by norm_num)).mapAffineEquiv chartDiamondAffineEquiv

/-- The fixed chart patch as a pure plane complex. -/
noncomputable def chartDiamondComplex : PlaneComplex :=
  chartDiamondMesh.toPlaneComplex

theorem chartDiamondComplex_pure : chartDiamondComplex.IsPure2 :=
  chartDiamondMesh.toPlaneComplex_isPure2

theorem chartDiamondComplex_support :
    chartDiamondComplex.support = chartDiamondAffineEquiv '' diamondPatch := by
  rw [chartDiamondComplex, chartDiamondMesh,
    TriangleMesh.mapAffineEquiv_support,
    diamondFanMesh_support]

private theorem chartDiamond_vertex_mem_closedBall (v : chartDiamondMesh.Vertex) :
    chartDiamondMesh.position v ∈ Metric.closedBall (0 : Plane) (3 / 4) := by
  have hs9 : Real.sqrt 9 = 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9), Real.sqrt_nonneg 9]
  have hs16 : Real.sqrt 16 = 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_nonneg 16]
  change dist (chartDiamondAffineEquiv (diamondFanPosition 0 v)) 0 ≤ 3 / 4
  rw [dist_zero_right]
  fin_cases v <;>
    simp [chartDiamondAffineEquiv, chartDiamondLinearEquiv, diamondFanPosition,
      planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;>
    norm_num [Real.sqrt_sq_eq_abs, hs9, hs16]

/-- The whole polygonal patch lies strictly inside the open unit disk. -/
theorem chartDiamondComplex_support_subset_ball :
    chartDiamondComplex.support ⊆ Metric.ball (0 : Plane) 1 := by
  intro x hx
  rw [chartDiamondComplex, TriangleMesh.toPlaneComplex_support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hclosed : x ∈ Metric.closedBall (0 : Plane) (3 / 4) := by
    apply convexHull_min ?_ (convex_closedBall (0 : Plane) (3 / 4)) hxt
    rintro y ⟨v, hv, rfl⟩
    exact chartDiamond_vertex_mem_closedBall v
  exact Metric.closedBall_subset_ball (by norm_num) hclosed

private theorem abs_add_abs_lt_three_four_of_mem_closedBall_half {x : Plane}
    (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
    |x 0| + |x 1| < 3 / 4 := by
  have hnorm : ‖x‖ ≤ 1 / 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hnormsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_two]
  have hsquares : (|x 0| + |x 1|) ^ 2 ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
    nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1)]
  have hnormnonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have habsnonneg : 0 ≤ |x 0| + |x 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [← hnormsq] at hsquares
  nlinarith

/-- The closed radius-`1/2` disk is contained in the interior of the polygonal patch. -/
theorem closedBall_half_subset_interior_chartDiamond :
    Metric.closedBall (0 : Plane) (1 / 2) ⊆ interior chartDiamondComplex.support := by
  intro x hx
  have hl1 := abs_add_abs_lt_three_four_of_mem_closedBall_half hx
  let q : Plane := chartDiamondAffineEquiv.symm x
  have hpp : x 0 + x 1 < 3 / 4 :=
    (add_le_add (le_abs_self _) (le_abs_self _)).trans_lt hl1
  have hpn : x 0 - x 1 < 3 / 4 := by
    have := add_le_add (le_abs_self (x 0)) (neg_le_abs (x 1))
    linarith
  have hnp : -x 0 + x 1 < 3 / 4 := by
    have := add_le_add (neg_le_abs (x 0)) (le_abs_self (x 1))
    linarith
  have hnn : -x 0 - x 1 < 3 / 4 := by
    have := add_le_add (neg_le_abs (x 0)) (neg_le_abs (x 1))
    linarith
  have hq : q ∈ StrictlyInDiamond := by
    change 0 < diamondSlackUR q ∧ 0 < diamondSlackUL q ∧
      0 < diamondSlackLR q ∧ 0 < diamondSlackLL q
    simp only [diamondSlackUR_eq, diamondSlackUL_eq, diamondSlackLR_eq,
      diamondSlackLL_eq, q, chartDiamondAffineEquiv_symm_apply_zero,
      chartDiamondAffineEquiv_symm_apply_one]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hqint : q ∈ interior diamondPatch := strictlyInDiamond_subset_interior hq
  rw [chartDiamondComplex_support]
  change x ∈ interior
    (chartDiamondAffineEquiv.toContinuousAffineEquiv.toHomeomorph '' diamondPatch)
  rw [← chartDiamondAffineEquiv.toContinuousAffineEquiv.toHomeomorph.image_interior]
  exact ⟨q, hqint, chartDiamondAffineEquiv.apply_symm_apply x⟩

/-- The two-triangle right half of the fixed chart diamond. -/
noncomputable def chartHalfDiamondMesh : TriangleMesh :=
  (@TriangleMesh.restrictTriangles (diamondFanMesh 0 (by norm_num) (by norm_num))
      (fun t : Finset (Fin 5) => 1 ∈ t) (fun t : Finset (Fin 5) => Finset.decidableMem (1 : Fin 5) t))
    |>.mapAffineEquiv chartDiamondAffineEquiv

/-- The right-half chart patch as a pure plane complex. -/
noncomputable def chartHalfDiamondComplex : PlaneComplex :=
  chartHalfDiamondMesh.toPlaneComplex

theorem chartHalfDiamondComplex_pure : chartHalfDiamondComplex.IsPure2 :=
  chartHalfDiamondMesh.toPlaneComplex_isPure2

private theorem restrictedRightDiamond_support :
    ((@TriangleMesh.restrictTriangles (diamondFanMesh 0 (by norm_num) (by norm_num))
      (fun t : Finset (Fin 5) => 1 ∈ t) (fun t : Finset (Fin 5) => Finset.decidableMem (1 : Fin 5) t)).toPlaneComplex.support) =
      diamondRightRegion := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t),
    convexHull ℝ (diamondFanPosition 0 '' (t : Set (Fin 5)))) = diamondRightRegion
  rw [← diamondFan_right_union (a := 0) (by norm_num) (by norm_num)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨t, ht, hxt⟩
    rcases Finset.mem_filter.mp ht with ⟨ht, h1t⟩
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp at h1t
    · exact Or.inl hxt
    · simp at h1t
    · exact Or.inr hxt
  · rintro (hxt | hxt)
    · exact ⟨{1, 2, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 4, 3}, by simp [diamondFanTriangles], hxt⟩

theorem chartHalfDiamondComplex_support :
    chartHalfDiamondComplex.support = chartDiamondAffineEquiv '' diamondRightRegion := by
  rw [chartHalfDiamondComplex, chartHalfDiamondMesh, TriangleMesh.mapAffineEquiv_support,
    restrictedRightDiamond_support]

theorem chartHalfDiamondComplex_support_subset_modelRegion :
    chartHalfDiamondComplex.support ⊆ ChartKind.halfDisk.modelRegion := by
  rw [chartHalfDiamondComplex_support]
  rintro x ⟨q, hq, rfl⟩
  refine ⟨chartDiamondComplex_support_subset_ball ?_, ?_⟩
  · rw [chartDiamondComplex_support]
    exact ⟨q, Or.inr hq, rfl⟩
  · have hq0 : 0 ≤ q 0 := by
      rw [diamondRightRegion] at hq
      change q ∈ {p : Plane | 0 ≤ cartesianX p}
      apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hq
      rintro y ⟨i, rfl⟩
      fin_cases i <;> simp [planePoint]
    exact mul_nonneg (by norm_num) hq0

theorem diamondRightRegion_eq_patch_inter_nonneg :
    diamondRightRegion = diamondPatch ∩ {p : Plane | 0 ≤ p 0} := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨Or.inr hp, ?_⟩
    rw [diamondRightRegion] at hp
    change p ∈ {q : Plane | 0 ≤ cartesianX q}
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨i, rfl⟩
    fin_cases i <;> simp [planePoint]
  · rintro p ⟨hp, hp0⟩
    change 0 ≤ p 0 at hp0
    rw [diamondPatch_eq_inDiamond] at hp
    rcases hp with ⟨hUR, hUL, hLR, hLL⟩
    rw [diamondSlackUR_eq] at hUR
    rw [diamondSlackUL_eq] at hUL
    rw [diamondSlackLR_eq] at hLR
    rw [diamondSlackLL_eq] at hLL
    let w : Fin 3 → ℝ :=
      ![(p 1 + 2 - 2 * p 0) / 4, (2 - 2 * p 0 - p 1) / 4, p 0]
    rw [diamondRightRegion]
    apply mem_convexHull_range_fin3_of_weights _ p w
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · simp [w]
      ring
    · ext i
      fin_cases i <;> simp [w, planePoint]
      all_goals ring

/-- The closed radius-`1/2` half-disk core is covered by the two-triangle half patch. -/
theorem halfCore_subset_chartHalfDiamond_support :
    ChartKind.halfDisk.modelCore ⊆ chartHalfDiamondComplex.support := by
  rintro x ⟨hxball, hx0⟩
  let q : Plane := chartDiamondAffineEquiv.symm x
  have hxint := closedBall_half_subset_interior_chartDiamond hxball
  have hxsupport : x ∈ chartDiamondComplex.support := interior_subset hxint
  rw [chartDiamondComplex_support] at hxsupport
  rcases hxsupport with ⟨q', hq', hq'x⟩
  have hq'eq : q' = q := by
    apply chartDiamondAffineEquiv.injective
    rw [hq'x, chartDiamondAffineEquiv.apply_symm_apply]
  subst q'
  have hq0 : 0 ≤ q 0 := by
    simp only [q, chartDiamondAffineEquiv_symm_apply_zero]
    exact mul_nonneg (by norm_num) hx0
  rw [chartHalfDiamondComplex_support, diamondRightRegion_eq_patch_inter_nonneg]
  exact ⟨q, ⟨hq', hq0⟩, chartDiamondAffineEquiv.apply_symm_apply x⟩

theorem chartHalfDiamond_support_eq_inter_halfPlane :
    chartHalfDiamondComplex.support = chartDiamondComplex.support ∩ HalfPlaneSet := by
  rw [chartHalfDiamondComplex_support, chartDiamondComplex_support,
    diamondRightRegion_eq_patch_inter_nonneg]
  ext x
  constructor
  · rintro ⟨q, ⟨hqPatch, hq0⟩, rfl⟩
    refine ⟨⟨q, hqPatch, rfl⟩, ?_⟩
    change 0 ≤ (3 / 4 : ℝ) * q 0
    exact mul_nonneg (by norm_num) hq0
  · rintro ⟨⟨q, hqPatch, hqx⟩, hx0⟩
    subst x
    have hq0 : 0 ≤ q 0 := by
      change 0 ≤ (3 / 4 : ℝ) * q 0 at hx0
      nlinarith
    exact ⟨q, ⟨hqPatch, hq0⟩, rfl⟩

/-- In barycentric coordinates on the fixed half-diamond, the normal coordinate is exactly the
weight of its unique positive-normal vertex, up to the fixed positive scale. -/
def chartHalfDiamondRightVertex : chartHalfDiamondComplex.Vertex := by
  change Fin 5
  exact 1

theorem chartHalfDiamond_baryEval_coordZero
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 =
      (3 / 4 : ℝ) * x.1 chartHalfDiamondRightVertex := by
  obtain ⟨t, ht, hsupport⟩ := x.2.2
  change Finset (Fin 5) at t
  have hzero : x.1 (0 : Fin 5) = 0 := by
    apply hsupport
    intro h0
    have ht' : t = {1, 2, 4} ∨ t = {1, 4, 3} := by
      rw [show chartHalfDiamondComplex.cells = chartHalfDiamondMesh.triangles by
        exact TriangleMesh.toPlaneComplex_cells chartHalfDiamondMesh] at ht
      change t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t) at ht
      obtain ⟨htFan, h1⟩ := Finset.mem_filter.mp ht
      simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at htFan
      rcases htFan with rfl | rfl | rfl | rfl
      · simp at h1
      · exact Or.inl rfl
      · simp at h1
      · exact Or.inr rfl
    rcases ht' with rfl | rfl
    · exact (by decide : (0 : Fin 5) ∉ ({1, 2, 4} : Finset (Fin 5))) h0
    · exact (by decide : (0 : Fin 5) ∉ ({1, 4, 3} : Finset (Fin 5))) h0
  change
    (∑ v : Fin 5, x.1 v • chartDiamondAffineEquiv (diamondFanPosition 0 v)) 0 =
      (3 / 4 : ℝ) * x.1 (1 : Fin 5)
  simp [chartDiamondAffineEquiv, chartDiamondLinearEquiv, diamondFanPosition, planePoint,
    Fin.sum_univ_succ, hzero]
  ring

theorem chartHalfDiamond_baryEval_coordZero_eq_zero_iff
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
      x.1 chartHalfDiamondRightVertex = 0 := by
  rw [chartHalfDiamond_baryEval_coordZero]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_zero]

/-- The `chartHalfDiamondUpperBoundaryEdge` declaration. -/
def chartHalfDiamondUpperBoundaryEdge :
    Finset chartHalfDiamondComplex.Vertex := by
  change Finset (Fin 5)
  exact {2, 4}

/-- The `chartHalfDiamondLowerBoundaryEdge` declaration. -/
def chartHalfDiamondLowerBoundaryEdge :
    Finset chartHalfDiamondComplex.Vertex := by
  change Finset (Fin 5)
  exact {4, 3}

theorem chartHalfDiamond_coordZero_iff_boundaryEdgeCarrier
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
      (∀ v ∉ chartHalfDiamondUpperBoundaryEdge, x.1 v = 0) ∨
      (∀ v ∉ chartHalfDiamondLowerBoundaryEdge, x.1 v = 0) := by
  rw [chartHalfDiamond_baryEval_coordZero_eq_zero_iff]
  obtain ⟨t, ht, hsupport⟩ := x.2.2
  change Finset (Fin 5) at t
  have ht' : t = {1, 2, 4} ∨ t = {1, 4, 3} := by
    rw [show chartHalfDiamondComplex.cells = chartHalfDiamondMesh.triangles by
      exact TriangleMesh.toPlaneComplex_cells chartHalfDiamondMesh] at ht
    change t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t) at ht
    obtain ⟨htFan, h1⟩ := Finset.mem_filter.mp ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at htFan
    rcases htFan with rfl | rfl | rfl | rfl
    · simp at h1
    · exact Or.inl rfl
    · simp at h1
    · exact Or.inr rfl
  constructor
  · intro hright
    rcases ht' with rfl | rfl
    · left
      intro v hv
      change Fin 5 at v
      fin_cases v
      · exact hsupport (0 : Fin 5)
          (by change (0 : Fin 5) ∉ ({1, 2, 4} : Finset (Fin 5)); decide)
      · exact hright
      · exact (hv (by change (2 : Fin 5) ∈ ({2, 4} : Finset (Fin 5)); decide)).elim
      · exact hsupport (3 : Fin 5)
          (by change (3 : Fin 5) ∉ ({1, 2, 4} : Finset (Fin 5)); decide)
      · exact (hv (by change (4 : Fin 5) ∈ ({2, 4} : Finset (Fin 5)); decide)).elim
    · right
      intro v hv
      change Fin 5 at v
      fin_cases v
      · exact hsupport (0 : Fin 5)
          (by change (0 : Fin 5) ∉ ({1, 4, 3} : Finset (Fin 5)); decide)
      · exact hright
      · exact hsupport (2 : Fin 5)
          (by change (2 : Fin 5) ∉ ({1, 4, 3} : Finset (Fin 5)); decide)
      · exact (hv (by change (3 : Fin 5) ∈ ({4, 3} : Finset (Fin 5)); decide)).elim
      · exact (hv (by change (4 : Fin 5) ∈ ({4, 3} : Finset (Fin 5)); decide)).elim
  · rintro (hupper | hlower)
    · apply hupper chartHalfDiamondRightVertex
      decide
    · apply hlower chartHalfDiamondRightVertex
      decide

/-- The finite polygonal patch assigned to a disk or half-disk chart model. -/
noncomputable def ChartKind.patchComplex : ChartKind → PlaneComplex
  | .disk => chartDiamondComplex
  | .halfDisk => chartHalfDiamondComplex

/-- The model-boundary condition appropriate to a chart kind.  A disk chart has no boundary
stratum; in a half-disk chart it is the zero normal-coordinate line. -/
def ChartKind.IsModelBoundary : (k : ChartKind) → Plane → Prop
  | .disk, _ => False
  | .halfDisk, p => p 0 = 0

/-- The explicit edge family carrying the model boundary in the fixed chart patch. -/
noncomputable def ChartKind.patchBoundaryEdges :
    (k : ChartKind) → Finset (Finset k.patchComplex.Vertex)
  | .disk => ∅
  | .halfDisk => {chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge}

/-- The fixed patch meets its model boundary exactly in the carrier of
`patchBoundaryEdges`. -/
theorem ChartKind.patchComplex_isModelBoundary_iff (k : ChartKind)
    (x : GeometricRealization k.patchComplex.Vertex k.patchComplex.cells) :
    k.IsModelBoundary (k.patchComplex.baryEval x.1) ↔
      ∃ e ∈ k.patchBoundaryEdges, ∀ v ∉ e, x.1 v = 0 := by
  cases k with
  | disk => simp [ChartKind.IsModelBoundary, ChartKind.patchBoundaryEdges]
  | halfDisk =>
      change chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
        ∃ e ∈
          ({chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge} :
            Finset (Finset chartHalfDiamondComplex.Vertex)),
          ∀ v ∉ e, x.1 v = 0
      erw [chartHalfDiamond_coordZero_iff_boundaryEdgeCarrier]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact ⟨chartHalfDiamondUpperBoundaryEdge, Or.inl rfl, h⟩
        · exact ⟨chartHalfDiamondLowerBoundaryEdge, Or.inr rfl, h⟩
      · rintro ⟨e, he | he, h⟩
        · subst e
          exact Or.inl h
        · subst e
          exact Or.inr h

/-- Facewise exposed form of the fixed patch boundary.  Every patch triangle meets the model
boundary in an intrinsic face of cardinality at most two. -/
theorem ChartKind.patchComplex_isModelBoundary_facewise (k : ChartKind) :
    ∀ t ∈ k.patchComplex.cells, ∃ b : Finset k.patchComplex.Vertex,
      b ⊆ t ∧ b.card ≤ 2 ∧
        ∀ x : GeometricRealization k.patchComplex.Vertex k.patchComplex.cells,
          (∀ v ∉ t, x.1 v = 0) →
            (k.IsModelBoundary (k.patchComplex.baryEval x.1) ↔
              ∀ v ∉ b, x.1 v = 0) := by
  cases k with
  | disk =>
      classical
      intro t ht
      refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro x hxt
      constructor
      · simp [ChartKind.IsModelBoundary]
      · intro hxEmpty
        have hxzero : ∀ v, x.1 v = 0 := by
          intro v
          exact hxEmpty v (by simp)
        have hsum : ∑ v, x.1 v = 0 := by simp [hxzero]
        linarith [x.2.1.2, hsum]
  | halfDisk =>
      intro t ht
      have hr1 : (1 : Fin 5) ∈ (show Finset (Fin 5) from t) := by
        have ht2 : t ∈ chartHalfDiamondMesh.triangles :=
          Eq.mp (congrArg (fun S => t ∈ S) (TriangleMesh.toPlaneComplex_cells chartHalfDiamondMesh)) ht
        change t ∈
          (diamondFanTriangles.filter fun u : Finset (Fin 5) => 1 ∈ u) at ht2
        exact ((Finset.mem_filter (p := fun u : Finset (Fin 5) => 1 ∈ u)).mp ht2).2
      classical
      let r : ChartKind.halfDisk.patchComplex.Vertex := by
        change Fin 5
        exact 1
      let b : Finset ChartKind.halfDisk.patchComplex.Vertex := t.erase r
      refine ⟨b, Finset.erase_subset _ _, ?_, ?_⟩
      · have hr : r ∈ t := hr1
        change (t.erase r).card ≤ 2
        rw [Finset.card_erase_of_mem hr]
        have htcard : t.card = 3 :=
          ChartKind.halfDisk.patchComplex.card_of_mem_cells ht
        omega
      · intro x hxt
        change chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
          ∀ v ∉ t.erase r, x.1 v = 0
        erw [chartHalfDiamond_baryEval_coordZero_eq_zero_iff,
          show chartHalfDiamondRightVertex = r by rfl]
        constructor
        · intro hrZero v hvb
          by_cases hvt : v ∈ t
          · have hvr : v = r := by
              by_contra hne
              exact hvb (Finset.mem_erase.mpr ⟨hne, hvt⟩)
            simpa [r, hvr] using hrZero
          · exact hxt v hvt
        · intro hx
          apply hx r
          simp []

/-- Every explicitly designated patch-boundary edge is an edge of the patch complex. -/
theorem ChartKind.mem_patchComplex_edges_of_mem_patchBoundaryEdges (k : ChartKind)
    {e : Finset k.patchComplex.Vertex} (he : e ∈ k.patchBoundaryEdges) :
    e ∈ k.patchComplex.cells.biUnion fun t => t.powersetCard 2 := by
  cases k with
  | disk => simp [ChartKind.patchBoundaryEdges] at he
  | halfDisk =>
      change e ∈
        ({chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge} :
          Finset (Finset chartHalfDiamondComplex.Vertex)) at he
      rcases Finset.mem_insert.mp he with he | he
      · rw [he]
        apply Finset.mem_biUnion.mpr
        refine ⟨({1, 2, 4} : Finset (Fin 5)), ?_, ?_⟩
        · change ({1, 2, 4} : Finset (Fin 5)) ∈
            diamondFanTriangles.filter fun t => 1 ∈ t
          decide
        · exact Finset.mem_powersetCard.mpr
            ⟨by change ({2, 4} : Finset (Fin 5)) ⊆ {1, 2, 4}; decide, by decide⟩
      · have he' := Finset.mem_singleton.mp he
        rw [he']
        apply Finset.mem_biUnion.mpr
        refine ⟨({1, 4, 3} : Finset (Fin 5)), ?_, ?_⟩
        · change ({1, 4, 3} : Finset (Fin 5)) ∈
            diamondFanTriangles.filter fun t => 1 ∈ t
          decide
        · exact Finset.mem_powersetCard.mpr
            ⟨by change ({4, 3} : Finset (Fin 5)) ⊆ {1, 4, 3}; decide, by decide⟩

theorem ChartKind.patchComplex_pure (k : ChartKind) : k.patchComplex.IsPure2 := by
  cases k with
  | disk => exact chartDiamondComplex_pure
  | halfDisk => exact chartHalfDiamondComplex_pure

/-- The four triangles in the fixed disk-chart patch have a connected dual graph. -/
theorem diamondFanTriangles_isDualConnected :
    TriangleFamily.IsDualConnected diamondFanTriangles := by
  change TriangleFamily.IsDualConnected
    ({{0, 4, 2}, {1, 2, 4}, {0, 3, 4}, {1, 4, 3}} :
      Finset (Finset (Fin 5)))
  have h₃ : TriangleFamily.IsDualConnected
      ({{1, 4, 3}} : Finset (Finset (Fin 5))) :=
    TriangleFamily.isDualConnected_singleton {1, 4, 3}
  have h₂₃ : TriangleFamily.IsDualConnected
      (insert {0, 3, 4} ({{1, 4, 3}} : Finset (Finset (Fin 5)))) := by
    apply TriangleFamily.isDualConnected_insert h₃ {0, 3, 4} ⟨{1, 4, 3}, by simp⟩
    exact ⟨{3, 4}, by decide, by decide, by decide⟩
  have h₁₂₃ : TriangleFamily.IsDualConnected
      (insert {1, 2, 4}
        (insert {0, 3, 4} ({{1, 4, 3}} : Finset (Finset (Fin 5))))) := by
    apply TriangleFamily.isDualConnected_insert h₂₃ {1, 2, 4} ⟨{1, 4, 3}, by simp⟩
    exact ⟨{1, 4}, by decide, by decide, by decide⟩
  apply TriangleFamily.isDualConnected_insert h₁₂₃ {0, 4, 2} ⟨{1, 2, 4}, by simp⟩
  exact ⟨{2, 4}, by decide, by decide, by decide⟩

/-- The two triangles in the fixed half-disk-chart patch have a connected dual graph. -/
theorem halfDiamondTriangles_isDualConnected :
    TriangleFamily.IsDualConnected
      (diamondFanTriangles.filter fun t => 1 ∈ t) := by
  change TriangleFamily.IsDualConnected
    ({{1, 2, 4}, {1, 4, 3}} : Finset (Finset (Fin 5)))
  have h₃ : TriangleFamily.IsDualConnected
      ({{1, 4, 3}} : Finset (Finset (Fin 5))) :=
    TriangleFamily.isDualConnected_singleton {1, 4, 3}
  apply TriangleFamily.isDualConnected_insert h₃ {1, 2, 4} ⟨{1, 4, 3}, by simp⟩
  exact ⟨{1, 4}, by decide, by decide, by decide⟩

/-- Every fixed chart patch starts with a connected dual graph. -/
theorem ChartKind.patchComplex_isDualConnected (k : ChartKind) :
    TriangleFamily.IsDualConnected k.patchComplex.cells := by
  cases k with
  | disk =>
      change TriangleFamily.IsDualConnected diamondFanTriangles
      exact diamondFanTriangles_isDualConnected
  | halfDisk =>
      change TriangleFamily.IsDualConnected
        (diamondFanTriangles.filter fun t => 1 ∈ t)
      exact halfDiamondTriangles_isDualConnected

theorem ChartKind.patchComplex_support_subset_modelRegion (k : ChartKind) :
    k.patchComplex.support ⊆ k.modelRegion := by
  cases k with
  | disk => exact chartDiamondComplex_support_subset_ball
  | halfDisk => exact chartHalfDiamondComplex_support_subset_modelRegion

theorem ChartKind.modelCore_subset_patchComplex_support (k : ChartKind) :
    k.modelCore ⊆ k.patchComplex.support := by
  cases k with
  | disk => exact closedBall_half_subset_interior_chartDiamond |>.trans interior_subset
  | halfDisk => exact halfCore_subset_chartHalfDiamond_support

/-- In model-region topology, the fixed chart core lies in the interior of the fixed polygonal
patch.  In the half-disk case this is relative interior, so edge-line core points are included. -/
theorem ChartKind.modelCore_subset_interior_patchInRegion (k : ChartKind) :
    {p : k.modelRegion | (p : Plane) ∈ k.modelCore} ⊆
      interior {p : k.modelRegion | (p : Plane) ∈ k.patchComplex.support} := by
  intro x hx
  cases k with
  | disk =>
      have hxint : (x : Plane) ∈ interior chartDiamondComplex.support :=
        closedBall_half_subset_interior_chartDiamond hx
      let O : Set (ChartKind.disk.modelRegion) :=
        Subtype.val ⁻¹' interior chartDiamondComplex.support
      have hOopen : IsOpen O :=
        isOpen_interior.preimage continuous_subtype_val
      have hOsub : O ⊆ {p : ChartKind.disk.modelRegion |
          (p : Plane) ∈ chartDiamondComplex.support} :=
        fun p hp => by
          change (p : Plane) ∈ interior chartDiamondComplex.support at hp
          exact (show interior chartDiamondComplex.support ⊆
            chartDiamondComplex.support from interior_subset) hp
      exact interior_maximal hOsub hOopen hxint
  | halfDisk =>
      have hxint : (x : Plane) ∈ interior chartDiamondComplex.support :=
        closedBall_half_subset_interior_chartDiamond hx.1
      let O : Set (ChartKind.halfDisk.modelRegion) :=
        Subtype.val ⁻¹' interior chartDiamondComplex.support
      have hOopen : IsOpen O :=
        isOpen_interior.preimage continuous_subtype_val
      have hOsub : O ⊆ {p : ChartKind.halfDisk.modelRegion |
          (p : Plane) ∈ chartHalfDiamondComplex.support} := by
        intro p hp
        change (p : Plane) ∈ interior chartDiamondComplex.support at hp
        rw [chartHalfDiamond_support_eq_inter_halfPlane]
        exact ⟨(show interior chartDiamondComplex.support ⊆
          chartDiamondComplex.support from interior_subset) hp, p.2.2⟩
      exact interior_maximal hOsub hOopen hxint

/-- Finite valence check for the four-triangle diamond fan. -/
theorem diamondFanTriangles_edge_valence (e : Finset (Fin 5)) (he : e.card = 2) :
    (diamondFanTriangles.filter fun t => e ⊆ t).card ≤ 2 := by
  decide +revert

/-- Finite valence check for the two-triangle half-diamond fan. -/
theorem halfDiamondTriangles_edge_valence (e : Finset (Fin 5)) :
    ((diamondFanTriangles.filter fun t => 1 ∈ t).filter fun t => e ⊆ t).card ≤ 2 := by
  decide +revert

theorem ChartKind.patchComplex_edge_valence (k : ChartKind)
    (e : Finset k.patchComplex.Vertex) (he : e.card = 2) :
    (k.patchComplex.cells.filter fun t => e ⊆ t).card ≤ 2 := by
  cases k with
  | disk =>
      change (chartDiamondMesh.toPlaneComplex.cells.filter fun t => e ⊆ t).card ≤ 2
      rw [TriangleMesh.toPlaneComplex_cells]
      change (diamondFanTriangles.filter fun t => e ⊆ t).card ≤ 2
      exact diamondFanTriangles_edge_valence e he
  | halfDisk =>
      change (chartHalfDiamondMesh.toPlaneComplex.cells.filter fun t => e ⊆ t).card ≤ 2
      rw [TriangleMesh.toPlaneComplex_cells]
      change ((diamondFanTriangles.filter fun t => 1 ∈ t).filter fun t => e ⊆ t).card ≤ 2
      exact halfDiamondTriangles_edge_valence e

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_03
/- END ClassificationOfSurfaces.Moise.ChartPatch -/

/- BEGIN ClassificationOfSurfaces.Moise.HalfPlanePolygon | 87050735616428c5405324a955d0d3d88b1a79f82853130f6bd4302c7fa43aa5 -/
section schottkyclassification14_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal disks in a half-plane

The bordered Radó step approximates the one-skeleton inside the closed right half-plane.  This
file records the elementary but important consequence: once the replacement polygon stays in
that half-plane, its bounded Schoenflies filling stays there as well.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The model closed half-plane is convex. -/
theorem convex_halfPlaneSet : Convex ℝ HalfPlaneSet := by
  have hlinear : IsLinearMap ℝ (fun v : Plane ↦ v 0) :=
    .mk (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  simpa [HalfPlaneSet] using convex_halfSpace_ge hlinear (0 : ℝ)

/-- A polygonal circle carried by the closed right half-plane bounds its disk there. -/
theorem PolygonalCircle.closedRegion_subset_halfPlane (J : PolygonalCircle)
    (hcarrier : J.carrier ⊆ HalfPlaneSet) :
    J.closedRegion ⊆ HalfPlaneSet := by
  have hinterior : J.interiorRegion ⊆ HalfPlaneSet := by
    intro x hx
    by_contra hnot
    have hxneg : x 0 < 0 := lt_of_not_ge hnot
    let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap 0 x
    let ray : Set Plane := line '' Set.Ici (1 : ℝ)
    have hxRay : x ∈ ray := by
      refine ⟨1, Set.mem_Ici.mpr le_rfl, ?_⟩
      simp [line]
    have hrayPreconnected : IsPreconnected ray := by
      exact (convex_Ici (1 : ℝ)).isPreconnected.image line
        line.continuous_of_finiteDimensional.continuousOn
    have hrayOff : ray ⊆ J.carrierᶜ := by
      rintro y ⟨t, ht, rfl⟩ hyCarrier
      have hyNonneg : 0 ≤ (AffineMap.lineMap 0 x t) 0 := hcarrier hyCarrier
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hyCoord : (AffineMap.lineMap 0 x t) 0 = t * x 0 := by
        simp [AffineMap.lineMap_apply]
      rw [hyCoord] at hyNonneg
      nlinarith
    have hraySplit : ray ⊆ J.interiorRegion ∪ J.exteriorRegion := by
      rw [J.interior_union_exterior]
      exact hrayOff
    have hrayInside : ray ⊆ J.interiorRegion :=
      hrayPreconnected.subset_left_of_subset_union
        J.isOpen_interiorRegion J.isOpen_exteriorRegion
        J.disjoint_interior_exterior hraySplit ⟨x, hxRay, hx⟩
    obtain ⟨R, hR⟩ := J.isBounded_interiorRegion.subset_closedBall (0 : Plane)
    let d := dist x 0
    have hd : 0 < d := dist_pos.mpr (by
      intro hxzero
      have hcoord : x 0 = (0 : Plane) 0 := congrArg (fun z : Plane ↦ z 0) hxzero
      simp only [PiLp.zero_apply] at hcoord
      linarith)
    let t : ℝ := (|R| + 1) / d + 1
    have ht : 1 ≤ t := by
      dsimp [t]
      have : 0 ≤ (|R| + 1) / d := div_nonneg (by positivity) hd.le
      linarith
    let y := AffineMap.lineMap (0 : Plane) x t
    have hyRay : y ∈ ray := ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hyBound := hR (hrayInside hyRay)
    rw [Metric.mem_closedBall] at hyBound
    have hydist : dist y 0 = t * d := by
      dsimp [y, d]
      rw [dist_lineMap_left, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num) ht), dist_comm 0 x]
    rw [hydist] at hyBound
    have hRabs : R ≤ |R| := le_abs_self R
    dsimp [t] at hyBound
    field_simp [hd.ne'] at hyBound
    nlinarith
  rw [J.closedRegion_eq_union]
  exact Set.union_subset hinterior hcarrier

/-- A plane-open subset of the closed half-plane cannot contain a point of its supporting
boundary line. -/
theorem coordZero_pos_of_mem_open_subset_halfPlane {O : Set Plane}
    (hO : IsOpen O) (hOH : O ⊆ HalfPlaneSet) {x : Plane} (hx : x ∈ O) :
    0 < x 0 := by
  have hxNonneg : 0 ≤ x 0 := hOH hx
  refine lt_of_le_of_ne hxNonneg ?_
  intro hxZero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let y : Plane := x - (ε / 2) • planePoint 1 0
  have hxy : dist y x < ε := by
    have hvertexNorm : ‖planePoint 1 0‖ = 1 := by
      simp [planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [dist_eq_norm]
    rw [show y - x = -(ε / 2) •
        planePoint 1 0 by
      simp [y, sub_eq_add_neg, add_assoc]]
    rw [norm_smul, norm_neg, hvertexNorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hyO : y ∈ O := hball (Metric.mem_ball.mpr hxy)
  have hyNonneg : 0 ≤ y 0 := hOH hyO
  have hyCoord : y 0 = x 0 - ε / 2 := by
    simp [y]
  rw [hyCoord, hxZero] at hyNonneg
  linarith

/-- The supporting line meets the filled polygonal disk only on its polygonal boundary. -/
theorem PolygonalCircle.mem_carrier_of_mem_closedRegion_coordZero
    (J : PolygonalCircle) (hcarrier : J.carrier ⊆ HalfPlaneSet)
    {x : Plane} (hx : x ∈ J.closedRegion) (hxZero : x 0 = 0) :
    x ∈ J.carrier := by
  rw [J.closedRegion_eq_union] at hx
  rcases hx with hxInterior | hxCarrier
  · have hxPos :=
      coordZero_pos_of_mem_open_subset_halfPlane J.isOpen_interiorRegion
        (by
          intro y hy
          exact J.closedRegion_subset_halfPlane hcarrier
            (by rw [J.closedRegion_eq_union]; exact Or.inl hy))
        hxInterior
    linarith
  · exact hxCarrier

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_04
/- END ClassificationOfSurfaces.Moise.HalfPlanePolygon -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary | cfaa8b34fda0dbb2681155fac308b259e9d8e52524e6f21c3856e018f1f9a856 -/
section schottkyclassification14_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal boundaries of intrinsic two-simplexes

The edge approximation of an intrinsic finite complex constructs each replacement edge in its
own finite line arrangement.  A two-cell extension needs the three edges of one abstract face in
one common plane complex.  This file enumerates only the one-dimensional arrangement faces which
actually carry those three edges, resolves all their segments simultaneously, and extracts the
resulting simple polygonal cycle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The selected replacement arc on cyclic edge `i` of the intrinsic face `t`. -/
noncomputable abbrev faceReplacementArc (t : K.Face) (i : ZMod 3) :=
  K.replacementArc hcont hinj D C (K.faceEdge t i)

/-- A one-dimensional face in the private arrangement of one replacement edge, together with
the proof that it is subordinate to that edge. -/
noncomputable abbrev FaceGraphSimplex (t : K.Face) (i : ZMod 3) :=
  {s : Finset (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.completeChain.arrangementMesh.toPlaneComplex.Vertex) //
    s ∈ (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.simplexes) ∧
      s.card ≤ 2 ∧
      (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
      (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeCarrier)}

noncomputable instance faceGraphSimplexFintype (t : K.Face) (i : ZMod 3) :
    Fintype (FaceGraphSimplex (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) :=
  by
    classical
    unfold FaceGraphSimplex
    infer_instance

/-- An ordered pair of vertices in a subordinate one-dimensional face, indexed also by the
abstract edge to which it belongs. -/
noncomputable abbrev FaceGraphSegment (t : K.Face) :=
  Σ i : ZMod 3, Σ s : FaceGraphSimplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i,
      ({v // v ∈ s.1} × {v // v ∈ s.1})

noncomputable instance faceGraphSegmentFintype (t : K.Face) :
    Fintype (FaceGraphSegment
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :=
  by
    classical
    unfold FaceGraphSegment
    infer_instance

/-- Segment labels for the common face arrangement.  The left summand lists actual graph
segments.  The right summand inserts the three abstract vertex images explicitly as degenerate
segments, making them canonical arrangement vertices. -/
noncomputable abbrev FaceBoundaryPiece (t : K.Face) :=
  FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ⊕ ZMod 3

noncomputable instance faceBoundaryPieceFintype (t : K.Face) :
    Fintype (FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :=
  by
    classical
    unfold FaceBoundaryPiece
    infer_instance

/-- The `faceGraphSegmentLeft` declaration. -/
noncomputable def faceGraphSegmentLeft (t : K.Face)
    (p : FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)

/-- The `faceGraphSegmentRight` declaration. -/
noncomputable def faceGraphSegmentRight (t : K.Face)
    (p : FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1)

/-- The `faceBoundaryLeft` declaration. -/
noncomputable def faceBoundaryLeft (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  Sum.elim (faceGraphSegmentLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (fun i => h (K.vertexPoint (K.faceUsedVertex t i))) p

/-- The `faceBoundaryRight` declaration. -/
noncomputable def faceBoundaryRight (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  Sum.elim (faceGraphSegmentRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (fun i => h (K.vertexPoint (K.faceUsedVertex t i))) p

/-- The union of the three complete replacement-edge carriers around one intrinsic face. -/
def faceReplacementCarrier (t : K.Face) : Set Plane :=
  ⋃ i : ZMod 3,
    (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.completeCarrier)

/-- Every listed family segment lies in the replacement boundary carrier. -/
theorem faceBoundaryPiece_segment_subset (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    segment ℝ
      (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
      (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ⊆
      faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  classical
  rcases p with p | i
  · let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    have hleft : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.1.1, p.2.2.1.2, rfl⟩
    have hright : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.2.1, p.2.2.2.2, rfl⟩
    change segment ℝ
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1) ⊆ _
    exact (((convex_convexHull ℝ _).segment_subset hleft hright).trans
      p.2.1.2.2.2).trans (Set.subset_iUnion (fun j : ZMod 3 =>
        (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j
          |>.completeCarrier)) p.1)
  · change segment ℝ (h (K.vertexPoint (K.faceUsedVertex t i)))
      (h (K.vertexPoint (K.faceUsedVertex t i))) ⊆ _
    rw [segment_same]
    rintro x rfl
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    apply (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.vertex_mem_completeCarrier)
    simp [faceUsedVertex]

/-- Every boundary-carrier point lies on one of the explicitly indexed family segments. -/
theorem exists_faceBoundaryPiece_segment (t : K.Face) {x : Plane}
    (hx : x ∈ faceReplacementCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    ∃ p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) := by
  classical
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hxi
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    ⟨s, hs, hcard, hsub⟩
  let p : FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
    Sum.inl ⟨i, q, ⟨v, hvs⟩, ⟨w, hws⟩⟩
  refine ⟨p, ?_⟩
  exact hxvw

/-- The common auxiliary chain listing every relevant segment around one intrinsic face. -/
noncomputable def faceBoundaryChain (t : K.Face) : BrokenLineData (Set.univ : Set Plane) :=
  BrokenLineData.segmentFamilyChain
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

/-- One finite plane complex carrying all three replacement edges face-to-face. -/
noncomputable def faceBoundaryComplex (t : K.Face) : PlaneComplex :=
  (faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    |>.arrangementMesh.toPlaneComplex).restrictedTo
      (faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

/-- The common face complex has exactly the union of the three replacement edges as support. -/
theorem faceBoundaryComplex_support (t : K.Face) :
    (faceBoundaryComplex (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).support =
      faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  classical
  let B := faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨p, hxp⟩ := K.exists_faceBoundaryPiece_segment t hx
  obtain ⟨s, hs, hxs, hsSegment⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) p hxp
  refine ⟨s, hs, hxs, ?_⟩
  exact hsSegment.trans (K.faceBoundaryPiece_segment_subset t p)

/-- The explicit degenerate family piece used to mark abstract corner `i`. -/
noncomputable def faceVertexPiece (t : K.Face) (i : ZMod 3) :
    FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
  Sum.inr i

/-- The canonical common-arrangement vertex at abstract corner `i`. -/
noncomputable def faceBoundaryVertex (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex :=
  let left := faceBoundaryLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let right := faceBoundaryRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  (BrokenLineData.segmentFamilyChain left right).arrangementVertex
    (BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)).castSucc

theorem faceBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position
        (K.faceBoundaryVertex t i) = h (K.vertexPoint (K.faceUsedVertex t i)) := by
  exact BrokenLineData.segmentFamily_arrangementVertex_position_left _ _
    (K.faceVertexPiece t i)

private theorem singleton_cellCarrier_eq_position {L : PlaneComplex} (v : L.Vertex) :
    L.cellCarrier {v} = {L.position v} := by
  rw [PlaneComplex.cellCarrier]
  have himage : L.position '' (({v} : Finset L.Vertex) : Set L.Vertex) =
      {L.position v} := by ext x; simp
  rw [himage, convexHull_singleton]

/-- Every abstract corner is a zero-face of the common boundary complex. -/
theorem faceBoundaryVertex_face (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex) ∈
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes := by
  classical
  let left := faceBoundaryLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let right := faceBoundaryRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let B := BrokenLineData.segmentFamilyChain left right
  let q := BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face q.castSucc, ?_⟩
  change B.arrangementMesh.toPlaneComplex.cellCarrier
    {B.arrangementVertex q.castSucc} ⊆ _
  rw [singleton_cellCarrier_eq_position,
    BrokenLineData.segmentFamily_arrangementVertex_position_left]
  rintro x rfl
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  apply (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
    |>.vertex_mem_completeCarrier)
  simp [faceUsedVertex]

/-- A family segment on edge `i` containing the given edge-carrier point, together with its
subordination to that one edge. -/
theorem exists_faceBoundaryPiece_segment_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier) :
    ∃ p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ∧
      segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ⊆
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  classical
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hx
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    ⟨s, hs, hcard, hsub⟩
  let vq : {u // u ∈ q.1} := ⟨v, hvs⟩
  let wq : {u // u ∈ q.1} := ⟨w, hws⟩
  let p : FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
    Sum.inl ⟨i, q, vq, wq⟩
  refine ⟨p, hxvw, ?_⟩
  have hvCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position v ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨v, hvs, rfl⟩
  have hwCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position w ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨w, hws, rfl⟩
  exact ((convex_convexHull ℝ _).segment_subset hvCarrier hwCarrier).trans hsub

/-- The common arrangement has a face subordinate to edge `i` through every point of that
edge. -/
theorem exists_faceBoundary_face_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier) :
    ∃ s ∈ (faceBoundaryChain
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
      |>.arrangementMesh.toPlaneComplex.simplexes),
      x ∈ (faceBoundaryChain
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ∧
      (faceBoundaryChain
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  obtain ⟨p, hxp, hpSub⟩ := K.exists_faceBoundaryPiece_segment_on_edge t i hx
  obtain ⟨s, hs, hxs, hsSub⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) p hxp
  exact ⟨s, hs, hxs, hsSub.trans hpSub⟩

/-- The subcomplex of the common face arrangement carried by cyclic edge `i`. -/
noncomputable def faceEdgeComplex (t : K.Face) (i : ZMod 3) : PlaneComplex :=
  (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).restrictedTo
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier

theorem faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).support =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  classical
  let B := faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  apply (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsub⟩ := K.exists_faceBoundary_face_on_edge t i hx
  have hsBoundary : s ∈ (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes := by
    apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
    exact ⟨hs, hsub.trans (Set.subset_iUnion (fun j : ZMod 3 =>
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j).completeCarrier) i)⟩
  exact ⟨s, hsBoundary, hxs, hsub⟩

private theorem faceBoundaryVertex_cellCarrier_subset_edge (t : K.Face)
    (i j : ZMod 3) (hj : j = i ∨ j = i + 1) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier
        {K.faceBoundaryVertex t j} ⊆
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  rw [singleton_cellCarrier_eq_position, K.faceBoundaryVertex_position t j]
  rintro x rfl
  apply (faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.vertex_mem_completeCarrier)
  rcases hj with rfl | rfl
  · simp [faceUsedVertex]
  · simp [faceUsedVertex]

theorem faceBoundaryVertex_face_edge_start (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).Vertex) ∈
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).simplexes := by
  apply ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t i,
    K.faceBoundaryVertex_cellCarrier_subset_edge t i i (Or.inl rfl)⟩

theorem faceBoundaryVertex_face_edge_finish (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t (i + 1)} : Finset
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).Vertex) ∈
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).simplexes := by
  apply ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t (i + 1),
    K.faceBoundaryVertex_cellCarrier_subset_edge t i (i + 1) (Or.inr rfl)⟩

theorem isPreconnected_faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    IsPreconnected (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).support := by
  rw [K.faceEdgeComplex_support t i]
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  rw [← A.completeTarget_support]
  exact A.isPreconnected_completeTarget_support

/-- A loop-free path through cyclic replacement edge `i`, oriented from corner `i` to corner
`i+1`. -/
noncomputable def faceEdgeVertexPath (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := ((faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
    |>.vertexGraph_reachable_of_isPreconnected
      (K.isPreconnected_faceEdgeComplex_support t i)
      (K.faceBoundaryVertex_face_edge_start t i)
      (K.faceBoundaryVertex_face_edge_finish t i)).exists_isPath
  exact ⟨⟨p, hp⟩⟩

theorem faceEdgeComplex_vertexGraph_le (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph ≤
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph := by
  intro v w hvw
  rw [(faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph_adj_iff] at hvw
  refine (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph_adj_iff.mpr ?_
  exact ⟨hvw.1, ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mp hvw.2 |>.1⟩

/-- The oriented edge path, regarded in the common boundary complex. -/
noncomputable def faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := (p.1.mapLe hle)
  refine ⟨q, ?_⟩
  exact p.property.mapLe hle

/-- Every vertex visited by the oriented path for edge `i` lies geometrically on that replacement
edge. -/
theorem faceBoundaryEdgePath_position_mem (t : K.Face) (i : ZMod 3)
    {v : (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hv : v ∈ (K.faceBoundaryEdgePath t i).1.support) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hvLocal : v ∈ p.1.support := by
    change v ∈ (p.1.mapLe hle).support at hv
    erw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact hv
  have hpos := (faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      |>.position_mem_support_of_mem_walk
        p.1
        (K.faceBoundaryVertex_face_edge_finish t i) hvLocal
  rw [K.faceEdgeComplex_support t i] at hpos
  exact hpos

/-- The straight geometric path traced by the selected graph path on one replacement edge. -/
noncomputable def faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Path
      ((faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).position
          (K.faceBoundaryVertex t i))
      ((faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).position
          (K.faceBoundaryVertex t (i + 1))) :=
  (faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).walkGeometricPath
      (K.faceEdgeVertexPath t i).1

/-- The selected finite graph path covers the entire polygonal replacement edge.  The key input
is that a connected subpath of an embedded arc containing both endpoints must be the whole arc. -/
theorem range_faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Set.range (K.faceEdgeGeometricPath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let B := faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let p := K.faceEdgeGeometricPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let e := K.faceEdge t i
  let A := faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hpSub : Set.range p ⊆ A.completeCarrier := by
    rw [← K.faceEdgeComplex_support t i]
    exact B.range_walkGeometricPath_subset_support
      (K.faceEdgeVertexPath t i).1 (K.faceBoundaryVertex_face_edge_finish t i)
  rcases K.faceEdge_endpoint_order t i with hforward | hreverse
  · have hsource : h (K.edgeFirstPoint e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        h (K.edgeFirstPoint e) = h (K.vertexPoint (K.faceUsedVertex t i)) :=
          congrArg h (K.edgeFirstPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t i) hforward.1)
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : h (K.edgeSecondPoint e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        h (K.edgeSecondPoint e) = h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
          congrArg h (K.edgeSecondPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t (i + 1)) hforward.2)
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath hsource htarget).trans A.range_completePath
    have harcInj : Function.Injective arc := by
      intro x y hxy
      exact A.completePath_injective hxy
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange
  · have hsource : h (K.edgeSecondPoint e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        h (K.edgeSecondPoint e) = h (K.vertexPoint (K.faceUsedVertex t i)) :=
          congrArg h (K.edgeSecondPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t i) hreverse.2)
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : h (K.edgeFirstPoint e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        h (K.edgeFirstPoint e) = h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
          congrArg h (K.edgeFirstPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t (i + 1)) hreverse.1)
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath.symm hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath.symm hsource htarget).trans
        ((Path.symm_range A.completePath).trans A.range_completePath)
    have harcInj : Function.Injective arc := by
      intro x y hxy
      change A.completePath.symm x = A.completePath.symm y at hxy
      change A.completePath (unitInterval.symm x) =
          A.completePath (unitInterval.symm y) at hxy
      exact unitInterval.symm_bijective.injective (A.completePath_injective hxy)
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange

/-- The same edge path, mapped into the common face-boundary complex, still covers the complete
replacement edge. -/
theorem range_faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).walkGeometricPath
        (K.faceBoundaryEdgePath t i).1) =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let A := faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  calc
    Set.range (B.walkGeometricPath (K.faceBoundaryEdgePath t i).1) =
        Set.range ((B.restrictedTo A.completeCarrier).walkGeometricPath p.1) := by
      exact B.range_walkGeometricPath_mapLe_restrictedTo A.completeCarrier p.1 hle
    _ = A.completeCarrier := K.range_faceEdgeGeometricPath t i

/-- Distinct cyclic corners remain distinct as vertices of the common arrangement. -/
theorem faceBoundaryVertex_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i ≠
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1) := by
  intro hv
  have hpos := congrArg
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position hv
  rw [K.faceBoundaryVertex_position t i,
    K.faceBoundaryVertex_position t (i + 1)] at hpos
  have hused : K.faceUsedVertex t i = K.faceUsedVertex t (i + 1) :=
    K.injective_vertexPoint (hinj hpos)
  exact K.faceVertex_ne_next t i
    (congrArg (fun v : K.UsedVertex => v.1) hused)

/-- Every oriented replacement-edge path contains at least one edge. -/
theorem faceBoundaryEdgePath_length_pos (t : K.Face) (i : ZMod 3) :
    0 < (K.faceBoundaryEdgePath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.length := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact K.faceBoundaryVertex_ne_next t i
    (SimpleGraph.Walk.eq_of_length_eq_zero hzero)

/-- Consecutive replacement-edge paths share only their common endpoint, which is removed from
the tail of the second path. -/
theorem faceBoundaryEdgePath_support_disjoint_next_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.support
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)).1.support.tail := by
  classical
  rw [List.disjoint_left]
  intro v hvi hvnext
  have hposi := K.faceBoundaryEdgePath_position_mem
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i hvi
  have hposnext := K.faceBoundaryEdgePath_position_mem
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
      (List.tail_subset _ hvnext)
  have hinter :
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier ∩
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)).completeCarrier :=
    ⟨hposi, hposnext⟩
  rw [K.faceReplacementCarrier_inter_next hcont hinj D C t i] at hinter
  have hposition :
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
        h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
    Set.mem_singleton_iff.mp hinter
  have hvCorner : v = K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1) :=
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
        (hposition.trans (K.faceBoundaryVertex_position t (i + 1)).symm)
  subst v
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  have hn := p.property.support_nodup
  rw [← p.1.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hvnext

/-- The first two oriented replacement edges form a simple path from corner `i` to the second
cyclic successor of `i`.  The unreduced successor expression keeps dependent elaboration cheap. -/
noncomputable def faceBoundaryTwoEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Path
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)) := by
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  refine ⟨p.1.append q.1, ?_⟩
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨p.property.support_nodup, q.property.support_nodup.tail,
    K.faceBoundaryEdgePath_support_disjoint_next_tail
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i⟩

/-- The tail of the first two boundary edges is disjoint from the tail of the closing edge. -/
theorem faceBoundaryTwoEdgePath_tail_disjoint_closing_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryTwoEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.support.tail
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
          (i + 1 + 1)).1.support.tail := by
  classical
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  rw [List.disjoint_left]
  intro v hvTwo hvr
  change v ∈ (p.1.append q.1).support.tail at hvTwo
  change v ∈ r.1.support.tail at hvr
  rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hvTwo
  rcases hvTwo with hvp | hvq
  · have hposp := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        (List.tail_subset _ hvp)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
    have hcycle : i + 1 + 1 + 1 = i := by
      calc
        i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
        _ = i + 0 := by rw [hthree]
        _ = i := add_zero i
    have hposp' :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1 + 1)).completeCarrier := by
      rw [hcycle]
      exact hposp
    have hinter :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1)).completeCarrier ∩
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1 + 1)).completeCarrier :=
      ⟨hposr, hposp'⟩
    rw [K.faceReplacementCarrier_inter_next hcont hinj D C t (i + 1 + 1)] at hinter
    have hpositionRaw :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t (i + 1 + 1 + 1))) :=
      Set.mem_singleton_iff.mp hinter
    have hposition :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t i)) := by
      rw [hcycle] at hpositionRaw
      exact hpositionRaw
    have hvCorner : v = K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t i).symm)
    subst v
    have hn := p.property.support_nodup
    rw [← p.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvp
  · have hposq := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
        (List.tail_subset _ hvq)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hinter :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1)).completeCarrier ∩
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1)).completeCarrier :=
      ⟨hposq, hposr⟩
    rw [K.faceReplacementCarrier_inter_next hcont hinj D C t (i + 1)] at hinter
    have hposition :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t (i + 1 + 1))) :=
      Set.mem_singleton_iff.mp hinter
    have hvCorner : v = K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1) :=
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t (i + 1 + 1)).symm)
    subst v
    have hn := r.property.support_nodup
    rw [← r.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvr

/-- The two-edge boundary path has length at least two. -/
theorem one_lt_faceBoundaryTwoEdgePath_length (t : K.Face) (i : ZMod 3) :
    1 < (K.faceBoundaryTwoEdgePath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.length := by
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  change 1 < (p.1.append q.1).length
  rw [SimpleGraph.Walk.length_append]
  have hp := K.faceBoundaryEdgePath_length_pos
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hq := K.faceBoundaryEdgePath_length_pos
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  change 0 < p.1.length at hp
  change 0 < q.1.length at hq
  omega

/-- The three oriented replacement-edge paths, with the final cyclic endpoint identified. -/
noncomputable def faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Walk
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) := by
  let p := K.faceBoundaryTwoEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  exact p.1.append (r.1.copy rfl hend)

/-- The boundary walk extracted from the common arrangement is a simple graph cycle. -/
theorem faceBoundaryCycleWalk_isCycle (t : K.Face) (i : ZMod 3) :
    (K.faceBoundaryCycleWalk
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).IsCycle := by
  let p := K.faceBoundaryTwoEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  change (p.1.append (r.1.copy rfl hend)).IsCycle
  apply p.property.isCycle_append
  · exact (SimpleGraph.Walk.isPath_copy r.1 rfl hend).mpr r.property
  · simpa only [SimpleGraph.Walk.support_copy] using
      K.faceBoundaryTwoEdgePath_tail_disjoint_closing_tail
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  · exact Or.inl (K.one_lt_faceBoundaryTwoEdgePath_length
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)

/-- The geometric range of the boundary cycle is the union of its three complete replacement
edges. -/
theorem range_faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).walkGeometricPath
        (K.faceBoundaryCycleWalk t i)) =
      (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier ∪
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            (i + 1)).completeCarrier ∪
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            (i + 1 + 1)).completeCarrier := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  change Set.range (B.walkGeometricPath
    ((p.1.append q.1).append (r.1.copy rfl hend))) = _
  rw [B.range_walkGeometricPath_append, B.range_walkGeometricPath_append,
    B.range_walkGeometricPath_copy, K.range_faceBoundaryEdgePath t i,
    K.range_faceBoundaryEdgePath t (i + 1),
    K.range_faceBoundaryEdgePath t (i + 1 + 1)]

/-- The simple polygonal circle formed by the three replacement edges around `t`. -/
noncomputable def facePolygonalCircle (t : K.Face) : PolygonalCircle :=
  (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).polygonalCircleOfCycle
      (K.faceBoundaryCycleWalk
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0)
      (K.faceBoundaryCycleWalk_isCycle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0)

/-- The extracted polygonal circle has exactly the prescribed three-edge replacement boundary. -/
theorem facePolygonalCircle_carrier (t : K.Face) :
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier =
      K.faceReplacementCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let p := K.faceBoundaryCycleWalk
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0
  let hp := K.faceBoundaryCycleWalk_isCycle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0
  rw [show K.facePolygonalCircle t = B.polygonalCircleOfCycle p hp by rfl,
    B.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath p hp,
    K.range_faceBoundaryCycleWalk t 0]
  let E : ZMod 3 → Set Plane := fun i =>
    (K.faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier
  change E 0 ∪ E (0 + 1) ∪ E (0 + 1 + 1) = ⋃ i, E i
  have hone : (0 : ZMod 3) + 1 = 1 := by decide
  have htwo : (1 : ZMod 3) + 1 = 2 := by decide
  rw [hone, htwo]
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (Set.union_subset
        (Set.subset_iUnion E 0)
        (Set.subset_iUnion E 1))
      (Set.subset_iUnion E 2)
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl hxi)
    · exact Or.inl (Or.inr hxi)
    · exact Or.inr hxi

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_05
/- END ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteFaceBoundary | 4cd7d71397d3d0b653a46ae3ebcdd9bc4c7c470d54abb72ac3ca023ff25ec07b -/
section schottkyclassification14_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal boundaries of locally finite two-simplexes

The globally coherent locally finite edge replacement assigns a finite polygonal arc to every
abstract edge. For each maximal face this file resolves its three edge complexes in one finite
line arrangement and extracts the resulting simple polygonal cycle. Shared abstract edges use
literally the same replacement arc, so adjacent face fillings will have identical boundaries.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}


/-- The selected replacement arc on cyclic edge `i` of the intrinsic face `t`. -/
noncomputable abbrev faceReplacementArc (t : K.Face) (i : ZMod 3) :=
  G.replacementArc (K.faceEdge t i)

/-- A one-dimensional face in the private arrangement of one replacement edge, together with
the proof that it is subordinate to that edge. -/
noncomputable abbrev FaceGraphSimplex (t : K.Face) (i : ZMod 3) :=
  {s : Finset (faceReplacementArc (G := G) t i
      |>.completeChain.arrangementMesh.toPlaneComplex.Vertex) //
    s ∈ (faceReplacementArc (G := G) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.simplexes) ∧
      s.card ≤ 2 ∧
      (faceReplacementArc (G := G) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
      (faceReplacementArc (G := G) t i
        |>.completeCarrier)}

noncomputable instance faceGraphSimplexFintype (t : K.Face) (i : ZMod 3) :
    Fintype (FaceGraphSimplex (G := G) t i) :=
  by
    classical
    unfold FaceGraphSimplex
    infer_instance

/-- An ordered pair of vertices in a subordinate one-dimensional face, indexed also by the
abstract edge to which it belongs. -/
noncomputable abbrev FaceGraphSegment (t : K.Face) :=
  Σ i : ZMod 3, Σ s : FaceGraphSimplex
    (G := G) t i,
      ({v // v ∈ s.1} × {v // v ∈ s.1})

noncomputable instance faceGraphSegmentFintype (t : K.Face) :
    Fintype (FaceGraphSegment
      (G := G) t) :=
  by
    classical
    unfold FaceGraphSegment
    infer_instance

/-- Segment labels for the common face arrangement.  The left summand lists actual graph
segments.  The right summand inserts the three abstract vertex images explicitly as degenerate
segments, making them canonical arrangement vertices. -/
noncomputable abbrev FaceBoundaryPiece (t : K.Face) :=
  FaceGraphSegment (G := G) t ⊕ ZMod 3

noncomputable instance faceBoundaryPieceFintype (t : K.Face) :
    Fintype (FaceBoundaryPiece
      (G := G) t) :=
  by
    classical
    unfold FaceBoundaryPiece
    infer_instance

/-- The `faceGraphSegmentLeft` declaration. -/
noncomputable def faceGraphSegmentLeft (t : K.Face)
    (p : FaceGraphSegment (G := G) t) :
    Plane :=
  (faceReplacementArc (G := G) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)

/-- The `faceGraphSegmentRight` declaration. -/
noncomputable def faceGraphSegmentRight (t : K.Face)
    (p : FaceGraphSegment (G := G) t) :
    Plane :=
  (faceReplacementArc (G := G) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1)

/-- The `faceBoundaryLeft` declaration. -/
noncomputable def faceBoundaryLeft (t : K.Face)
    (p : FaceBoundaryPiece (G := G) t) :
    Plane :=
  Sum.elim (faceGraphSegmentLeft (G := G) t)
    (fun i => G.vertexImage (K.faceVertex t i)) p

/-- The `faceBoundaryRight` declaration. -/
noncomputable def faceBoundaryRight (t : K.Face)
    (p : FaceBoundaryPiece (G := G) t) :
    Plane :=
  Sum.elim (faceGraphSegmentRight (G := G) t)
    (fun i => G.vertexImage (K.faceVertex t i)) p

/-- The union of the three complete replacement-edge carriers around one intrinsic face. -/
def faceReplacementCarrier (t : K.Face) : Set Plane :=
  ⋃ i : ZMod 3,
    (faceReplacementArc (G := G) t i
      |>.completeCarrier)

/-- Consecutive replacement edges around one face meet exactly at their shared cyclic
vertex. -/
theorem faceReplacementCarrier_inter_next (t : K.Face) (i : ZMod 3) :
    (faceReplacementArc (G := G) t i).completeCarrier ∩
        (faceReplacementArc (G := G) t (i + 1)).completeCarrier =
      {G.vertexImage (K.faceVertex t (i + 1))} := by
  let A := faceReplacementArc (G := G) t i
  let B := faceReplacementArc (G := G) t (i + 1)
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hx'⟩
    obtain ⟨v, hv, hxv⟩ := A.exists_shared_vertex_of_mem_completeCarriers
      (B := B) (K.faceEdge_ne_next t i) hx hx'
    have hv' : v = K.faceVertex t (i + 1) := by
      have hvMem : v ∈ (K.faceEdge t i).1 ∩ (K.faceEdge t (i + 1)).1 := hv
      rw [K.faceEdge_inter_next t i] at hvMem
      exact Finset.mem_singleton.mp hvMem
    rw [Set.mem_singleton_iff, hxv, hv']
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · apply A.vertex_mem_completeCarrier
      simp []
    · apply B.vertex_mem_completeCarrier
      simp [add_assoc]

/-- Every listed family segment lies in the replacement boundary carrier. -/
theorem faceBoundaryPiece_segment_subset (t : K.Face)
    (p : FaceBoundaryPiece (G := G) t) :
    segment ℝ
      (faceBoundaryLeft (G := G) t p)
      (faceBoundaryRight (G := G) t p) ⊆
      faceReplacementCarrier (G := G) t := by
  classical
  rcases p with p | i
  · let A := faceReplacementArc (G := G) t p.1
    have hleft : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.1.1, p.2.2.1.2, rfl⟩
    have hright : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.2.1, p.2.2.2.2, rfl⟩
    change segment ℝ
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1) ⊆ _
    exact (((convex_convexHull ℝ _).segment_subset hleft hright).trans
      p.2.1.2.2.2).trans (Set.subset_iUnion (fun j : ZMod 3 =>
        (faceReplacementArc (G := G) t j
          |>.completeCarrier)) p.1)
  · change segment ℝ (G.vertexImage (K.faceVertex t i))
      (G.vertexImage (K.faceVertex t i)) ⊆ _
    rw [segment_same]
    rintro x rfl
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    apply (faceReplacementArc (G := G) t i
      |>.vertex_mem_completeCarrier)
    simp

/-- Every boundary-carrier point lies on one of the explicitly indexed family segments. -/
theorem exists_faceBoundaryPiece_segment (t : K.Face) {x : Plane}
    (hx : x ∈ faceReplacementCarrier
      (G := G) t) :
    ∃ p : FaceBoundaryPiece (G := G) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (G := G) t p)
        (faceBoundaryRight (G := G) t p) := by
  classical
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let A := faceReplacementArc (G := G) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hxi
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (G := G) t i :=
    ⟨s, hs, hcard, hsub⟩
  let p : FaceBoundaryPiece
      (G := G) t :=
    Sum.inl ⟨i, q, ⟨v, hvs⟩, ⟨w, hws⟩⟩
  refine ⟨p, ?_⟩
  exact hxvw

/-- The common auxiliary chain listing every relevant segment around one intrinsic face. -/
noncomputable def faceBoundaryChain (t : K.Face) : BrokenLineData (Set.univ : Set Plane) :=
  BrokenLineData.segmentFamilyChain
    (faceBoundaryLeft (G := G) t)
    (faceBoundaryRight (G := G) t)

/-- One finite plane complex carrying all three replacement edges face-to-face. -/
noncomputable def faceBoundaryComplex (t : K.Face) : PlaneComplex :=
  (faceBoundaryChain (G := G) t
    |>.arrangementMesh.toPlaneComplex).restrictedTo
      (faceReplacementCarrier (G := G) t)

/-- The common face complex has exactly the union of the three replacement edges as support. -/
theorem faceBoundaryComplex_support (t : K.Face) :
    (faceBoundaryComplex (G := G) t).support =
      faceReplacementCarrier (G := G) t := by
  classical
  let B := faceBoundaryChain (G := G) t
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨p, hxp⟩ := K.exists_faceBoundaryPiece_segment t hx
  obtain ⟨s, hs, hxs, hsSegment⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (G := G) t)
    (faceBoundaryRight (G := G) t) p hxp
  refine ⟨s, hs, hxs, ?_⟩
  exact hsSegment.trans (K.faceBoundaryPiece_segment_subset t p)

/-- The explicit degenerate family piece used to mark abstract corner `i`. -/
noncomputable def faceVertexPiece (t : K.Face) (i : ZMod 3) :
    FaceBoundaryPiece (G := G) t :=
  Sum.inr i

/-- The canonical common-arrangement vertex at abstract corner `i`. -/
noncomputable def faceBoundaryVertex (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (G := G) t).Vertex :=
  let left := faceBoundaryLeft
    (G := G) t
  let right := faceBoundaryRight
    (G := G) t
  (BrokenLineData.segmentFamilyChain left right).arrangementVertex
    (BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)).castSucc

theorem faceBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (G := G) t).position
        (K.faceBoundaryVertex t i) = G.vertexImage (K.faceVertex t i) := by
  exact BrokenLineData.segmentFamily_arrangementVertex_position_left _ _
    (K.faceVertexPiece t i)

private theorem singleton_cellCarrier_eq_position {L : PlaneComplex} (v : L.Vertex) :
    L.cellCarrier {v} = {L.position v} := by
  rw [PlaneComplex.cellCarrier]
  have himage : L.position '' (({v} : Finset L.Vertex) : Set L.Vertex) =
      {L.position v} := by ext x; simp
  rw [himage, convexHull_singleton]

/-- Every abstract corner is a zero-face of the common boundary complex. -/
theorem faceBoundaryVertex_face (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceBoundaryComplex
        (G := G) t).Vertex) ∈
      (faceBoundaryComplex
        (G := G) t).simplexes := by
  classical
  let left := faceBoundaryLeft
    (G := G) t
  let right := faceBoundaryRight
    (G := G) t
  let B := BrokenLineData.segmentFamilyChain left right
  let q := BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face q.castSucc, ?_⟩
  change B.arrangementMesh.toPlaneComplex.cellCarrier
    {B.arrangementVertex q.castSucc} ⊆ _
  rw [singleton_cellCarrier_eq_position,
    BrokenLineData.segmentFamily_arrangementVertex_position_left]
  rintro x rfl
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  apply (faceReplacementArc (G := G) t i
    |>.vertex_mem_completeCarrier)
  simp

/-- A family segment on edge `i` containing the given edge-carrier point, together with its
subordination to that one edge. -/
theorem exists_faceBoundaryPiece_segment_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (G := G) t i).completeCarrier) :
    ∃ p : FaceBoundaryPiece (G := G) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (G := G) t p)
        (faceBoundaryRight (G := G) t p) ∧
      segment ℝ
        (faceBoundaryLeft (G := G) t p)
        (faceBoundaryRight (G := G) t p) ⊆
        (faceReplacementArc
          (G := G) t i).completeCarrier := by
  classical
  let A := faceReplacementArc (G := G) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hx
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (G := G) t i :=
    ⟨s, hs, hcard, hsub⟩
  let vq : {u // u ∈ q.1} := ⟨v, hvs⟩
  let wq : {u // u ∈ q.1} := ⟨w, hws⟩
  let p : FaceBoundaryPiece
      (G := G) t :=
    Sum.inl ⟨i, q, vq, wq⟩
  refine ⟨p, hxvw, ?_⟩
  have hvCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position v ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨v, hvs, rfl⟩
  have hwCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position w ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨w, hws, rfl⟩
  exact ((convex_convexHull ℝ _).segment_subset hvCarrier hwCarrier).trans hsub

/-- The common arrangement has a face subordinate to edge `i` through every point of that
edge. -/
theorem exists_faceBoundary_face_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (G := G) t i).completeCarrier) :
    ∃ s ∈ (faceBoundaryChain
        (G := G) t
      |>.arrangementMesh.toPlaneComplex.simplexes),
      x ∈ (faceBoundaryChain
          (G := G) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ∧
      (faceBoundaryChain
          (G := G) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
        (faceReplacementArc
          (G := G) t i).completeCarrier := by
  obtain ⟨p, hxp, hpSub⟩ := K.exists_faceBoundaryPiece_segment_on_edge t i hx
  obtain ⟨s, hs, hxs, hsSub⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (G := G) t)
    (faceBoundaryRight (G := G) t) p hxp
  exact ⟨s, hs, hxs, hsSub.trans hpSub⟩

/-- The subcomplex of the common face arrangement carried by cyclic edge `i`. -/
noncomputable def faceEdgeComplex (t : K.Face) (i : ZMod 3) : PlaneComplex :=
  (faceBoundaryComplex
    (G := G) t).restrictedTo
      (faceReplacementArc
        (G := G) t i).completeCarrier

theorem faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (G := G) t i).support =
      (faceReplacementArc
        (G := G) t i).completeCarrier := by
  classical
  let B := faceBoundaryChain (G := G) t
  apply (faceBoundaryComplex
    (G := G) t).restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsub⟩ := K.exists_faceBoundary_face_on_edge t i hx
  have hsBoundary : s ∈ (faceBoundaryComplex
      (G := G) t).simplexes := by
    apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
    exact ⟨hs, hsub.trans (Set.subset_iUnion (fun j : ZMod 3 =>
      (faceReplacementArc
        (G := G) t j).completeCarrier) i)⟩
  exact ⟨s, hsBoundary, hxs, hsub⟩

private theorem faceBoundaryVertex_cellCarrier_subset_edge (t : K.Face)
    (i j : ZMod 3) (hj : j = i ∨ j = i + 1) :
    (faceBoundaryComplex
      (G := G) t).cellCarrier
        {K.faceBoundaryVertex t j} ⊆
      (faceReplacementArc
        (G := G) t i).completeCarrier := by
  rw [singleton_cellCarrier_eq_position, K.faceBoundaryVertex_position t j]
  rintro x rfl
  apply (faceReplacementArc
    (G := G) t i
      |>.vertex_mem_completeCarrier)
  rcases hj with rfl | rfl
  · simp
  · simp

theorem faceBoundaryVertex_face_edge_start (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceEdgeComplex
        (G := G) t i).Vertex) ∈
      (faceEdgeComplex
        (G := G) t i).simplexes := by
  apply ((faceBoundaryComplex
    (G := G) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t i,
    K.faceBoundaryVertex_cellCarrier_subset_edge t i i (Or.inl rfl)⟩

theorem faceBoundaryVertex_face_edge_finish (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t (i + 1)} : Finset
      (faceEdgeComplex
        (G := G) t i).Vertex) ∈
      (faceEdgeComplex
        (G := G) t i).simplexes := by
  apply ((faceBoundaryComplex
    (G := G) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t (i + 1),
    K.faceBoundaryVertex_cellCarrier_subset_edge t i (i + 1) (Or.inr rfl)⟩

theorem isPreconnected_faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    IsPreconnected (faceEdgeComplex
      (G := G) t i).support := by
  rw [K.faceEdgeComplex_support t i]
  let A := faceReplacementArc (G := G) t i
  rw [← A.completeTarget_support]
  exact A.isPreconnected_completeTarget_support

/-- A loop-free path through cyclic replacement edge `i`, oriented from corner `i` to corner
`i+1`. -/
noncomputable def faceEdgeVertexPath (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (G := G) t i).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := ((faceEdgeComplex
      (G := G) t i)
    |>.vertexGraph_reachable_of_isPreconnected
      (K.isPreconnected_faceEdgeComplex_support t i)
      (K.faceBoundaryVertex_face_edge_start t i)
      (K.faceBoundaryVertex_face_edge_finish t i)).exists_isPath
  exact ⟨⟨p, hp⟩⟩

theorem faceEdgeComplex_vertexGraph_le (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (G := G) t i).vertexGraph ≤
      (faceBoundaryComplex
        (G := G) t).vertexGraph := by
  intro v w hvw
  rw [(faceEdgeComplex
    (G := G) t i).vertexGraph_adj_iff] at hvw
  refine (faceBoundaryComplex
    (G := G) t).vertexGraph_adj_iff.mpr ?_
  exact ⟨hvw.1, ((faceBoundaryComplex
    (G := G) t)
      |>.mem_restrictedTo_simplexes_iff _).mp hvw.2 |>.1⟩

/-- The oriented edge path, regarded in the common boundary complex. -/
noncomputable def faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (G := G) t).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  let p := K.faceEdgeVertexPath
    (G := G) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (G := G) t i
  let q := (p.1.mapLe hle)
  refine ⟨q, ?_⟩
  exact p.property.mapLe hle

/-- Every vertex visited by the oriented path for edge `i` lies geometrically on that replacement
edge. -/
theorem faceBoundaryEdgePath_position_mem (t : K.Face) (i : ZMod 3)
    {v : (faceBoundaryComplex
      (G := G) t).Vertex}
    (hv : v ∈ (K.faceBoundaryEdgePath t i).1.support) :
    (faceBoundaryComplex
      (G := G) t).position v ∈
      (faceReplacementArc
        (G := G) t i).completeCarrier := by
  let p := K.faceEdgeVertexPath
    (G := G) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (G := G) t i
  have hvLocal : v ∈ p.1.support := by
    change v ∈ (p.1.mapLe hle).support at hv
    erw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact hv
  have hpos := (faceEdgeComplex
    (G := G) t i)
      |>.position_mem_support_of_mem_walk
        p.1
        (K.faceBoundaryVertex_face_edge_finish t i) hvLocal
  rw [K.faceEdgeComplex_support t i] at hpos
  exact hpos

/-- The straight geometric path traced by the selected graph path on one replacement edge. -/
noncomputable def faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Path
      ((faceEdgeComplex
        (G := G) t i).position
          (K.faceBoundaryVertex t i))
      ((faceEdgeComplex
        (G := G) t i).position
          (K.faceBoundaryVertex t (i + 1))) :=
  (faceEdgeComplex
    (G := G) t i).walkGeometricPath
      (K.faceEdgeVertexPath t i).1

/-- The selected finite graph path covers the entire polygonal replacement edge.  The key input
is that a connected subpath of an embedded arc containing both endpoints must be the whole arc. -/
theorem range_faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Set.range (K.faceEdgeGeometricPath
      (G := G) t i) =
      (faceReplacementArc
        (G := G) t i).completeCarrier := by
  let B := faceEdgeComplex
    (G := G) t i
  let p := K.faceEdgeGeometricPath
    (G := G) t i
  let e := K.faceEdge t i
  let A := faceReplacementArc
    (G := G) t i
  have hpSub : Set.range p ⊆ A.completeCarrier := by
    rw [← K.faceEdgeComplex_support t i]
    exact B.range_walkGeometricPath_subset_support
      (K.faceEdgeVertexPath t i).1 (K.faceBoundaryVertex_face_edge_finish t i)
  rcases K.faceEdge_endpoint_order t i with hforward | hreverse
  · have hsource : G.vertexImage (K.edgeFirst e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        G.vertexImage (K.edgeFirst e) = G.vertexImage (K.faceVertex t i) :=
          congrArg G.vertexImage hforward.1
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : G.vertexImage (K.edgeSecond e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        G.vertexImage (K.edgeSecond e) = G.vertexImage (K.faceVertex t (i + 1)) :=
          congrArg G.vertexImage hforward.2
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath hsource htarget).trans A.range_completePath
    have harcInj : Function.Injective arc := by
      intro x y hxy
      exact A.completePath_injective hxy
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange
  · have hsource : G.vertexImage (K.edgeSecond e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        G.vertexImage (K.edgeSecond e) = G.vertexImage (K.faceVertex t i) :=
          congrArg G.vertexImage hreverse.2
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : G.vertexImage (K.edgeFirst e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        G.vertexImage (K.edgeFirst e) = G.vertexImage (K.faceVertex t (i + 1)) :=
          congrArg G.vertexImage hreverse.1
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath.symm hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath.symm hsource htarget).trans
        ((Path.symm_range A.completePath).trans A.range_completePath)
    have harcInj : Function.Injective arc := by
      intro x y hxy
      change A.completePath.symm x = A.completePath.symm y at hxy
      change A.completePath (unitInterval.symm x) =
          A.completePath (unitInterval.symm y) at hxy
      exact unitInterval.symm_bijective.injective (A.completePath_injective hxy)
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange

/-- The same edge path, mapped into the common face-boundary complex, still covers the complete
replacement edge. -/
theorem range_faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (G := G) t).walkGeometricPath
        (K.faceBoundaryEdgePath t i).1) =
      (faceReplacementArc
        (G := G) t i).completeCarrier := by
  let B := faceBoundaryComplex
    (G := G) t
  let A := faceReplacementArc
    (G := G) t i
  let p := K.faceEdgeVertexPath
    (G := G) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (G := G) t i
  calc
    Set.range (B.walkGeometricPath (K.faceBoundaryEdgePath t i).1) =
        Set.range ((B.restrictedTo A.completeCarrier).walkGeometricPath p.1) := by
      exact B.range_walkGeometricPath_mapLe_restrictedTo A.completeCarrier p.1 hle
    _ = A.completeCarrier := K.range_faceEdgeGeometricPath t i

/-- Distinct cyclic corners remain distinct as vertices of the common arrangement. -/
theorem faceBoundaryVertex_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceBoundaryVertex
        (G := G) t i ≠
      K.faceBoundaryVertex
        (G := G) t (i + 1) := by
  intro hv
  have hpos := congrArg
    (faceBoundaryComplex
      (G := G) t).position hv
  rw [K.faceBoundaryVertex_position t i,
    K.faceBoundaryVertex_position t (i + 1)] at hpos
  have hused : K.faceVertex t i = K.faceVertex t (i + 1) :=
    G.vertexImage_injective hpos
  exact K.faceVertex_ne_next t i hused

/-- Every oriented replacement-edge path contains at least one edge. -/
theorem faceBoundaryEdgePath_length_pos (t : K.Face) (i : ZMod 3) :
    0 < (K.faceBoundaryEdgePath
      (G := G) t i).1.length := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact K.faceBoundaryVertex_ne_next t i
    (SimpleGraph.Walk.eq_of_length_eq_zero hzero)

/-- Consecutive replacement-edge paths share only their common endpoint, which is removed from
the tail of the second path. -/
theorem faceBoundaryEdgePath_support_disjoint_next_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryEdgePath
        (G := G) t i).1.support
      (K.faceBoundaryEdgePath
        (G := G) t (i + 1)).1.support.tail := by
  classical
  rw [List.disjoint_left]
  intro v hvi hvnext
  have hposi := K.faceBoundaryEdgePath_position_mem
    (G := G) t i hvi
  have hposnext := K.faceBoundaryEdgePath_position_mem
    (G := G) t (i + 1)
      (List.tail_subset _ hvnext)
  have hinter :
      (faceBoundaryComplex
        (G := G) t).position v ∈
        (faceReplacementArc
          (G := G) t i).completeCarrier ∩
        (faceReplacementArc
          (G := G) t (i + 1)).completeCarrier :=
    ⟨hposi, hposnext⟩
  rw [K.faceReplacementCarrier_inter_next (G := G) t i] at hinter
  have hposition :
      (faceBoundaryComplex
        (G := G) t).position v =
        G.vertexImage (K.faceVertex t (i + 1)) :=
    Set.mem_singleton_iff.mp hinter
  have hvCorner : v = K.faceBoundaryVertex
      (G := G) t (i + 1) :=
    (faceBoundaryComplex
      (G := G) t).position_injective
        (hposition.trans (K.faceBoundaryVertex_position t (i + 1)).symm)
  subst v
  let p := K.faceBoundaryEdgePath
    (G := G) t (i + 1)
  have hn := p.property.support_nodup
  rw [← p.1.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hvnext

/-- The first two oriented replacement edges form a simple path from corner `i` to the second
cyclic successor of `i`.  The unreduced successor expression keeps dependent elaboration cheap. -/
noncomputable def faceBoundaryTwoEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (G := G) t).vertexGraph.Path
      (K.faceBoundaryVertex
        (G := G) t i)
      (K.faceBoundaryVertex
        (G := G) t (i + 1 + 1)) := by
  let p := K.faceBoundaryEdgePath
    (G := G) t i
  let q := K.faceBoundaryEdgePath
    (G := G) t (i + 1)
  refine ⟨p.1.append q.1, ?_⟩
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨p.property.support_nodup, q.property.support_nodup.tail,
    K.faceBoundaryEdgePath_support_disjoint_next_tail
      (G := G) t i⟩

/-- The tail of the first two boundary edges is disjoint from the tail of the closing edge. -/
theorem faceBoundaryTwoEdgePath_tail_disjoint_closing_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryTwoEdgePath
        (G := G) t i).1.support.tail
      (K.faceBoundaryEdgePath
        (G := G) t
          (i + 1 + 1)).1.support.tail := by
  classical
  let p := K.faceBoundaryEdgePath
    (G := G) t i
  let q := K.faceBoundaryEdgePath
    (G := G) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (G := G) t (i + 1 + 1)
  rw [List.disjoint_left]
  intro v hvTwo hvr
  change v ∈ (p.1.append q.1).support.tail at hvTwo
  change v ∈ r.1.support.tail at hvr
  rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hvTwo
  rcases hvTwo with hvp | hvq
  · have hposp := K.faceBoundaryEdgePath_position_mem
      (G := G) t i
        (List.tail_subset _ hvp)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (G := G) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
    have hcycle : i + 1 + 1 + 1 = i := by
      calc
        i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
        _ = i + 0 := by rw [hthree]
        _ = i := add_zero i
    have hposp' :
        (faceBoundaryComplex
          (G := G) t).position v ∈
          (faceReplacementArc
            (G := G) t
              (i + 1 + 1 + 1)).completeCarrier := by
      rw [hcycle]
      exact hposp
    have hinter :
        (faceBoundaryComplex
          (G := G) t).position v ∈
          (faceReplacementArc
            (G := G) t
              (i + 1 + 1)).completeCarrier ∩
          (faceReplacementArc
            (G := G) t
              (i + 1 + 1 + 1)).completeCarrier :=
      ⟨hposr, hposp'⟩
    rw [K.faceReplacementCarrier_inter_next (G := G) t (i + 1 + 1)] at hinter
    have hpositionRaw :
        (faceBoundaryComplex
          (G := G) t).position v =
          G.vertexImage (K.faceVertex t (i + 1 + 1 + 1)) :=
      Set.mem_singleton_iff.mp hinter
    have hposition :
        (faceBoundaryComplex
          (G := G) t).position v =
          G.vertexImage (K.faceVertex t i) := by
      rw [hcycle] at hpositionRaw
      exact hpositionRaw
    have hvCorner : v = K.faceBoundaryVertex
        (G := G) t i :=
      (faceBoundaryComplex
        (G := G) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t i).symm)
    subst v
    have hn := p.property.support_nodup
    rw [← p.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvp
  · have hposq := K.faceBoundaryEdgePath_position_mem
      (G := G) t (i + 1)
        (List.tail_subset _ hvq)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (G := G) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hinter :
        (faceBoundaryComplex
          (G := G) t).position v ∈
          (faceReplacementArc
            (G := G) t
              (i + 1)).completeCarrier ∩
          (faceReplacementArc
            (G := G) t
              (i + 1 + 1)).completeCarrier :=
      ⟨hposq, hposr⟩
    rw [K.faceReplacementCarrier_inter_next (G := G) t (i + 1)] at hinter
    have hposition :
        (faceBoundaryComplex
          (G := G) t).position v =
          G.vertexImage (K.faceVertex t (i + 1 + 1)) :=
      Set.mem_singleton_iff.mp hinter
    have hvCorner : v = K.faceBoundaryVertex
        (G := G) t (i + 1 + 1) :=
      (faceBoundaryComplex
        (G := G) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t (i + 1 + 1)).symm)
    subst v
    have hn := r.property.support_nodup
    rw [← r.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvr

/-- The two-edge boundary path has length at least two. -/
theorem one_lt_faceBoundaryTwoEdgePath_length (t : K.Face) (i : ZMod 3) :
    1 < (K.faceBoundaryTwoEdgePath
      (G := G) t i).1.length := by
  let p := K.faceBoundaryEdgePath
    (G := G) t i
  let q := K.faceBoundaryEdgePath
    (G := G) t (i + 1)
  change 1 < (p.1.append q.1).length
  rw [SimpleGraph.Walk.length_append]
  have hp := K.faceBoundaryEdgePath_length_pos
    (G := G) t i
  have hq := K.faceBoundaryEdgePath_length_pos
    (G := G) t (i + 1)
  change 0 < p.1.length at hp
  change 0 < q.1.length at hq
  omega

/-- The three oriented replacement-edge paths, with the final cyclic endpoint identified. -/
noncomputable def faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (G := G) t).vertexGraph.Walk
      (K.faceBoundaryVertex
        (G := G) t i)
      (K.faceBoundaryVertex
        (G := G) t i) := by
  let p := K.faceBoundaryTwoEdgePath
    (G := G) t i
  let r := K.faceBoundaryEdgePath
    (G := G) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (G := G) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (G := G) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (G := G) t j) hcycle
  exact p.1.append (r.1.copy rfl hend)

/-- The boundary walk extracted from the common arrangement is a simple graph cycle. -/
theorem faceBoundaryCycleWalk_isCycle (t : K.Face) (i : ZMod 3) :
    (K.faceBoundaryCycleWalk
      (G := G) t i).IsCycle := by
  let p := K.faceBoundaryTwoEdgePath
    (G := G) t i
  let r := K.faceBoundaryEdgePath
    (G := G) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (G := G) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (G := G) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (G := G) t j) hcycle
  change (p.1.append (r.1.copy rfl hend)).IsCycle
  apply p.property.isCycle_append
  · exact (SimpleGraph.Walk.isPath_copy r.1 rfl hend).mpr r.property
  · simpa only [SimpleGraph.Walk.support_copy] using
      K.faceBoundaryTwoEdgePath_tail_disjoint_closing_tail
        (G := G) t i
  · exact Or.inl (K.one_lt_faceBoundaryTwoEdgePath_length
      (G := G) t i)

/-- The geometric range of the boundary cycle is the union of its three complete replacement
edges. -/
theorem range_faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (G := G) t).walkGeometricPath
        (K.faceBoundaryCycleWalk t i)) =
      (faceReplacementArc
          (G := G) t i).completeCarrier ∪
        (faceReplacementArc
          (G := G) t
            (i + 1)).completeCarrier ∪
        (faceReplacementArc
          (G := G) t
            (i + 1 + 1)).completeCarrier := by
  let B := faceBoundaryComplex
    (G := G) t
  let p := K.faceBoundaryEdgePath
    (G := G) t i
  let q := K.faceBoundaryEdgePath
    (G := G) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (G := G) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (G := G) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (G := G) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (G := G) t j) hcycle
  change Set.range (B.walkGeometricPath
    ((p.1.append q.1).append (r.1.copy rfl hend))) = _
  rw [B.range_walkGeometricPath_append, B.range_walkGeometricPath_append,
    B.range_walkGeometricPath_copy, K.range_faceBoundaryEdgePath t i,
    K.range_faceBoundaryEdgePath t (i + 1),
    K.range_faceBoundaryEdgePath t (i + 1 + 1)]

/-- The simple polygonal circle formed by the three replacement edges around `t`. -/
noncomputable def facePolygonalCircle (t : K.Face) : PolygonalCircle :=
  (faceBoundaryComplex
    (G := G) t).polygonalCircleOfCycle
      (K.faceBoundaryCycleWalk
        (G := G) t 0)
      (K.faceBoundaryCycleWalk_isCycle
        (G := G) t 0)

/-- The extracted polygonal circle has exactly the prescribed three-edge replacement boundary. -/
theorem facePolygonalCircle_carrier (t : K.Face) :
    (K.facePolygonalCircle
      (G := G) t).carrier =
      K.faceReplacementCarrier
        (G := G) t := by
  let B := faceBoundaryComplex
    (G := G) t
  let p := K.faceBoundaryCycleWalk
    (G := G) t 0
  let hp := K.faceBoundaryCycleWalk_isCycle
    (G := G) t 0
  rw [show K.facePolygonalCircle t = B.polygonalCircleOfCycle p hp by rfl,
    B.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath p hp,
    K.range_faceBoundaryCycleWalk t 0]
  let E : ZMod 3 → Set Plane := fun i =>
    (K.faceReplacementArc
      (G := G) t i).completeCarrier
  change E 0 ∪ E (0 + 1) ∪ E (0 + 1 + 1) = ⋃ i, E i
  have hone : (0 : ZMod 3) + 1 = 1 := by decide
  have htwo : (1 : ZMod 3) + 1 = 2 := by decide
  rw [hone, htwo]
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (Set.union_subset
        (Set.subset_iUnion E 0)
        (Set.subset_iUnion E 1))
      (Set.subset_iUnion E 2)
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl hxi)
    · exact Or.inl (Or.inr hxi)
    · exact Or.inr hxi

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_06
/- END ClassificationOfSurfaces.Moise.LocallyFiniteFaceBoundary -/

/- BEGIN ClassificationOfSurfaces.Moise.PuncturedSurface | 119fab13e14e6638be27d7687f823b8de35f8e47a678816faec5b9047af8537a -/
section schottkyclassification14_block_07
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Punctured surface charts

The disk and half-disk models used by the Moise construction remain path-connected after
deleting finitely many points.  The disk case transports the corresponding theorem for the
Euclidean plane through `Homeomorph.unitBall`.  For a half-disk, we delete the finite preimage
under the fold from the doubled disk, connect there, and fold the resulting path back.

These local results are the input for proving that a connected surface remains connected after
deleting a finite set.  That theorem, in turn, rules out multiple dual components in a completed
surface triangulation.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Fold the open unit disk onto the open half-disk. -/
def foldDiskToHalfDisk :
    ChartKind.disk.modelRegion → ChartKind.halfDisk.modelRegion :=
  fun p => ⟨(foldPlaneToHalfSpace p).1, by
    constructor
    · have hp : (p : Plane) ∈ Metric.ball 0 1 := by
        exact p.2
      simpa only [Metric.mem_ball, dist_zero_right, norm_foldPlaneToHalfSpace] using hp
    · exact (foldPlaneToHalfSpace p).2⟩

/-- Folding the disk onto the half-disk is continuous. -/
theorem continuous_foldDiskToHalfDisk : Continuous foldDiskToHalfDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_foldPlaneToHalfSpace.comp continuous_subtype_val)

/-- The inverse image of a finite set under the disk fold is finite.  Each fiber is contained in
the two-point set consisting of a point and its reflection across the boundary line. -/
theorem finite_preimage_foldDiskToHalfDisk
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    (foldDiskToHalfDisk ⁻¹' s).Finite := by
  apply hs.preimage'
  intro q hq
  let candidates : Set Plane := {q.1, reflectAcrossHalfPlaneBoundary q.1}
  have hcandidates : candidates.Finite := by
    exact (Set.finite_singleton _).insert _
  have hpreCandidates :
      ((Subtype.val : ChartKind.disk.modelRegion → Plane) ⁻¹' candidates).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hcandidates
  apply hpreCandidates.subset
  intro p hp
  change foldDiskToHalfDisk p = q at hp
  have hval : (foldPlaneToHalfSpace (p : Plane)).1 = (q : Plane) :=
    congrArg Subtype.val hp
  have h0 : |(p : Plane) 0| = (q : Plane) 0 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 0) hval
  have h1 : (p : Plane) 1 = (q : Plane) 1 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 1) hval
  have hq0 : 0 ≤ (q : Plane) 0 := q.2.2
  rcases (abs_eq hq0).mp h0 with hpos | hneg
  · change (p : Plane) ∈ candidates
    exact Set.mem_insert_iff.mpr (Or.inl (plane_ext hpos h1))
  · change (p : Plane) ∈ candidates
    apply Set.mem_insert_iff.mpr
    right
    apply Set.mem_singleton_iff.mpr
    apply plane_ext
    · simpa [reflectAcrossHalfPlaneBoundary] using hneg
    · simpa [reflectAcrossHalfPlaneBoundary] using h1

/-- Folding the disk onto the half-disk is surjective. -/
theorem surjective_foldDiskToHalfDisk :
    Function.Surjective foldDiskToHalfDisk := by
  intro q
  let p : ChartKind.disk.modelRegion := ⟨q.1, by
    simpa [ChartKind.modelRegion] using q.2.1⟩
  refine ⟨p, Subtype.ext ?_⟩
  apply plane_ext
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, abs_of_nonneg q.2.2, p]
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, p]

/-- An open disk with finitely many points deleted is path-connected. -/
theorem diskModel_compl_finite_isPathConnected
    (s : Set ChartKind.disk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let e : Plane ≃ₜ ChartKind.disk.modelRegion := Homeomorph.unitBall
  rw [← e.isPathConnected_preimage]
  rw [preimage_compl]
  apply Set.Countable.isPathConnected_compl_of_one_lt_rank
  · apply Module.one_lt_rank_of_one_lt_finrank
    simp [Plane]
  · exact (Set.Finite.preimage e.injective.injOn hs).countable

/-- An open half-disk with finitely many points deleted is path-connected. -/
theorem halfDiskModel_compl_finite_isPathConnected
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  have hpre : (foldDiskToHalfDisk ⁻¹' s).Finite :=
    finite_preimage_foldDiskToHalfDisk s hs
  have hpath :
      IsPathConnected ((foldDiskToHalfDisk ⁻¹' s)ᶜ) :=
    diskModel_compl_finite_isPathConnected _ hpre
  have himage := hpath.image continuous_foldDiskToHalfDisk
  rw [← preimage_compl,
    Set.image_preimage_eq _ surjective_foldDiskToHalfDisk] at himage
  exact himage

/-- Either Moise chart model remains path-connected after deleting finitely many points. -/
theorem ChartKind.isPathConnected_compl_finite
    (k : ChartKind) (s : Set k.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  cases k with
  | disk => exact diskModel_compl_finite_isPathConnected s hs
  | halfDisk => exact halfDiskModel_compl_finite_isPathConnected s hs

/-- The underlying planar model region remains path-connected after deleting a finite ambient
set. -/
theorem ChartKind.isPathConnected_modelRegion_diff_finite
    (k : ChartKind) (s : Set Plane) (hs : s.Finite) :
    IsPathConnected (k.modelRegion \ s) := by
  let t : Set k.modelRegion :=
    (Subtype.val : k.modelRegion → Plane) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    k.isPathConnected_compl_finite t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- A Moise chart domain, as a subtype, remains path-connected after deleting finitely many
points. -/
theorem isPathConnected_compl_finite_subtype
    (s : Set c.domain) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let t : Set c.kind.modelRegion := c.chart.symm ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage c.chart.symm.injective.injOn hs
  have hmodel : IsPathConnected tᶜ :=
    c.kind.isPathConnected_compl_finite t ht
  have hpre : IsPathConnected (c.chart ⁻¹' tᶜ) :=
    c.chart.isPathConnected_preimage.mpr hmodel
  have heq : c.chart ⁻¹' t = s := by
    ext x
    simp [t]
  rw [preimage_compl, heq] at hpre
  exact hpre

/-- The ambient chart domain remains path-connected after deleting a finite subset of the
surface. -/
theorem isPathConnected_domain_diff_finite
    (s : Set S) (hs : s.Finite) :
    IsPathConnected (c.domain \ s) := by
  let t : Set c.domain := (Subtype.val : c.domain → S) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    c.isPathConnected_compl_finite_subtype t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

end MoiseChart

/-- A connected T1 space stays connected after deleting a finite set if every deleted point has
an open neighborhood whose complement of the whole finite set is path-connected.

For a putative separation of the complement, each deleted point is assigned to the unique side
containing its punctured neighborhood.  Restoring the assigned points then produces two disjoint
open sets covering the original connected space. -/
theorem isConnected_compl_finite_of_locally_pathConnected
    {S : Type*} [TopologicalSpace S] [T1Space S] [ConnectedSpace S]
    {F : Set S} (hF : F.Finite)
    (hlocal : ∀ p ∈ F, ∃ U : Set S,
      IsOpen U ∧ p ∈ U ∧ IsPathConnected (U \ F)) :
    IsConnected Fᶜ := by
  classical
  by_cases hFempty : F = ∅
  · simpa [hFempty] using
      (isConnected_univ : IsConnected (Set.univ : Set S))
  have hcomplNonempty : Fᶜ.Nonempty := by
    obtain ⟨p, hpF⟩ := Set.nonempty_iff_ne_empty.mpr hFempty
    obtain ⟨U, _hUopen, _hpU, hpath⟩ := hlocal p hpF
    obtain ⟨x, _hxU, hxF⟩ := hpath.nonempty
    exact ⟨x, hxF⟩
  refine ⟨hcomplNonempty, ?_⟩
  intro u v hu hv hcover hUne hVne
  by_contra hinter
  let A : Set S := Fᶜ ∩ u
  let B : Set S := Fᶜ ∩ v
  have hAopen : IsOpen A := hF.isClosed.isOpen_compl.inter hu
  have hBopen : IsOpen B := hF.isClosed.isOpen_compl.inter hv
  have hABcover : Fᶜ ⊆ A ∪ B := by
    intro x hx
    rcases hcover hx with hxu | hxv
    · exact Or.inl ⟨hx, hxu⟩
    · exact Or.inr ⟨hx, hxv⟩
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
  choose U hUopen hpU hUpath using
    fun p : F ↦ hlocal p.1 p.2
  have hside (p : F) :
      U p \ F ⊆ A ∨ U p \ F ⊆ B := by
    obtain ⟨x, hx⟩ := (hUpath p).nonempty
    rcases hABcover hx.2 with hxA | hxB
    · left
      exact (hUpath p).isConnected.isPreconnected.subset_left_of_subset_union
        hAopen hBopen hABdisjoint
        (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxA⟩
    · right
      exact (hUpath p).isConnected.isPreconnected.subset_right_of_subset_union
        hAopen hBopen hABdisjoint
        (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxB⟩
  let Left (p : F) : Prop := U p \ F ⊆ A
  have hright (p : F) (hp : ¬Left p) :
      U p \ F ⊆ B :=
    (hside p).resolve_left hp
  let W (p : F) : Set S := U p \ (F \ {p.1})
  have hWopen (p : F) : IsOpen (W p) := by
    exact (hUopen p).inter (hF.sdiff |>.isClosed.isOpen_compl)
  have hpW (p : F) : p.1 ∈ W p := by
    refine ⟨hpU p, ?_⟩
    rintro ⟨_, hpne⟩
    exact hpne rfl
  have eq_center_of_mem_W_of_mem_F (p : F) {x : S}
      (hxW : x ∈ W p) (hxF : x ∈ F) :
      x = p.1 := by
    by_contra hxp
    apply hxW.2
    exact ⟨hxF, by simpa using hxp⟩
  let L : Set S := {x | ∃ p : F, Left p ∧ x = p.1}
  let R : Set S := {x | ∃ p : F, ¬Left p ∧ x = p.1}
  let A' : Set S := A ∪ L
  let B' : Set S := B ∪ R
  have hA'open : IsOpen A' := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hx with hxA | ⟨p, hpLeft, rfl⟩
    · exact ⟨A, Set.subset_union_left, hAopen, hxA⟩
    · refine ⟨W p, ?_, hWopen p, hpW p⟩
      intro y hyW
      by_cases hyF : y ∈ F
      · right
        exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
      · left
        exact hpLeft ⟨hyW.1, hyF⟩
  have hB'open : IsOpen B' := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hx with hxB | ⟨p, hpLeft, rfl⟩
    · exact ⟨B, Set.subset_union_left, hBopen, hxB⟩
    · refine ⟨W p, ?_, hWopen p, hpW p⟩
      intro y hyW
      by_cases hyF : y ∈ F
      · right
        exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
      · left
        exact hright p hpLeft ⟨hyW.1, hyF⟩
  have hA'B'disjoint : Disjoint A' B' := by
    rw [Set.disjoint_left]
    intro x hxA' hxB'
    rcases hxA' with hxA | ⟨p, hpLeft, hp⟩
    · rcases hxB' with hxB | ⟨q, _hqLeft, hq⟩
      · exact Set.disjoint_left.mp hABdisjoint hxA hxB
      · exact hxA.1 (hq ▸ q.2)
    · rcases hxB' with hxB | ⟨q, hqLeft, hq⟩
      · exact hxB.1 (hp ▸ p.2)
      · apply hqLeft
        have hpq : p = q := by
          apply Subtype.ext
          exact hp.symm.trans hq
        simpa [hpq] using hpLeft
  have hA'B'cover : (Set.univ : Set S) ⊆ A' ∪ B' := by
    intro x _
    by_cases hxF : x ∈ F
    · let p : F := ⟨x, hxF⟩
      by_cases hpLeft : Left p
      · exact Or.inl (Or.inr ⟨p, hpLeft, rfl⟩)
      · exact Or.inr (Or.inr ⟨p, hpLeft, rfl⟩)
    · rcases hABcover hxF with hxA | hxB
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl hxB)
  have hA'ne : ((Set.univ : Set S) ∩ A').Nonempty := by
    obtain ⟨x, hxF, hxu⟩ := hUne
    exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxu⟩⟩
  have hB'ne : ((Set.univ : Set S) ∩ B').Nonempty := by
    obtain ⟨x, hxF, hxv⟩ := hVne
    exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxv⟩⟩
  obtain ⟨x, _, hxA', hxB'⟩ := isPreconnected_univ
    A' B' hA'open hB'open hA'B'cover hA'ne hB'ne
  exact Set.disjoint_left.mp hA'B'disjoint hxA' hxB'

/-- A connected surface charted on the Euclidean half-plane remains connected after deleting
finitely many points. -/
theorem isConnected_compl_finite_surface
    {S : Type*} [TopologicalSpace S] [T1Space S] [ConnectedSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {F : Set S} (hF : F.Finite) :
    IsConnected Fᶜ := by
  apply isConnected_compl_finite_of_locally_pathConnected hF
  intro p hpF
  obtain ⟨c, _hfaithful, hcore⟩ :=
    exists_moiseChart_core_mem_nhds S p
  refine ⟨c.domain, c.isOpen_domain, ?_,
    c.isPathConnected_domain_diff_finite F hF⟩
  exact c.core_subset_domain (mem_of_mem_nhds hcore)

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification14_block_07
/- END ClassificationOfSurfaces.Moise.PuncturedSurface -/
