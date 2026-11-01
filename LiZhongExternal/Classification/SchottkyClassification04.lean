/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification04: pinned classification sources; see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification03
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import LiZhongExternal.Classification.SchottkyClassification02
import Mathlib.Topology.Compactness.LocallyFinite

/- BEGIN ClassificationOfSurfaces.Moise.Anchors | 176ef9b5a42b320df1b4356be89615dbc62f1673f2be0ca80c38db90524522a2 -/
noncomputable section

section schottkyclassification04_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Positive anchors for the Moise plane structures

Concrete instances required by the definition-faithfulness rules
(`docs/AUTOFORMALIZATION_GUIDE.md`): the standard triangle with vertices `(0,0)`, `(1,0)`,
`(0,1)` realizes

* a `PolygonalCircle` (`standardTriangleCircle`): its boundary as a polygonal simple closed
  curve with three vertices and three edges; and
* a `PlaneComplex` (`standardTrianglePlaneComplex`): the full simplicial complex of the closed
  triangle, with three vertices, three edges and one 2-face (all seven nonempty vertex subsets).

Both geometric side conditions (`consecutive_inter`, `face_inter`) reduce to
`AffineIndependent.convexHull_inter`: convex hulls of subfamilies of an affinely independent
family intersect in the hull of the shared vertices.  The only genuinely geometric input is the
affine independence of the three vertices, proved from non-collinearity by coordinate
computation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The vertices of the standard triangle: `(0,0)`, `(1,0)`, `(0,1)`. -/
def standardTriangleVertex : Fin 3 → Plane :=
  ![!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]]

/-- The vertices of the standard triangle are not collinear. -/
theorem standardTriangle_not_collinear :
    ¬ Collinear ℝ ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]} : Set Plane) := by
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert _ _)).mp hcol
  obtain ⟨rB, hB⟩ := hv !₂[(1 : ℝ), 0] (by simp)
  obtain ⟨rC, hC⟩ := hv !₂[(0 : ℝ), 1] (by simp)
  have hB0 := congrArg (fun p : Plane => p 0) hB
  have hC0 := congrArg (fun p : Plane => p 0) hC
  have hC1 := congrArg (fun p : Plane => p 1) hC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_zero] at hB0 hC0 hC1
  rcases mul_eq_zero.mp hC0.symm with h | h
  · rw [h, zero_mul] at hC1
    exact one_ne_zero hC1
  · rw [h, mul_zero] at hB0
    exact one_ne_zero hB0

/-- The vertices of the standard triangle are affinely independent. -/
theorem standardTriangleVertex_affineIndependent :
    AffineIndependent ℝ standardTriangleVertex :=
  affineIndependent_iff_not_collinear_set.mpr standardTriangle_not_collinear

theorem standardTriangleVertex_injective :
    Function.Injective standardTriangleVertex :=
  standardTriangleVertex_affineIndependent.injective

/-- Any relabelling of the standard triangle vertices by an injective index vector is affinely
independent. -/
theorem standardTriangleVertex_triple_affineIndependent (a b c : Fin 3)
    (h : Function.Injective ![a, b, c]) :
    AffineIndependent ℝ
      ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c] := by
  have he : ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c]
      = standardTriangleVertex ∘ ![a, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [he]
  exact standardTriangleVertex_affineIndependent.comp_embedding ⟨![a, b, c], h⟩

/-- **Positive anchor** for `PolygonalCircle`: the boundary of the standard triangle with
vertices `(0,0)`, `(1,0)`, `(0,1)` is a polygonal simple closed curve. -/
def standardTriangleCircle : PolygonalCircle where
  n := 3
  three_le := le_rfl
  vertex := standardTriangleVertex
  adjacent_ne := fun i =>
    standardTriangleVertex_injective.ne ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  consecutive_inter := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hcase with rfl | rfl | rfl
    · rw [show (0 : ZMod 3) + 1 = 1 by decide, show (0 : ZMod 3) + 2 = 2 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 0 1 2 (by decide))
    · rw [show (1 : ZMod 3) + 1 = 2 by decide, show (1 : ZMod 3) + 2 = 0 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 1 2 0 (by decide))
    · rw [show (2 : ZMod 3) + 1 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 2 0 1 (by decide))
  nonadjacent_disjoint := fun i j h₁ h₂ h₃ =>
    absurd ((by decide : ∀ i j : ZMod 3, i ≠ j → i ≠ j + 1 → j = i + 1) i j h₁ h₂) h₃

/-- Three affinely independent points in the plane form an affine basis. -/
noncomputable def planeAffineBasisOfTriple (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) : AffineBasis (Fin 3) ℝ Plane where
  toFun := p
  ind' := hp
  tot' := hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])

/-- The interior of a full-dimensional plane triangle consists exactly of points with all
three barycentric coordinates positive. -/
theorem interior_convexHull_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) :
    interior (convexHull ℝ (Set.range b)) = {x | ∀ i, 0 < b.coord i x} := by
  have hC : convexHull ℝ (Set.range b) = {x | ∀ i, 0 ≤ b.coord i x} :=
    b.convexHull_eq_nonneg_coord
  apply Set.Subset.antisymm
  · intro x hx
    have hxC : x ∈ convexHull ℝ (Set.range b) := interior_subset hx
    have hxnonneg : ∀ i, 0 ≤ b.coord i x := by rwa [hC] at hxC
    intro i
    apply lt_of_le_of_ne (hxnonneg i)
    intro hzero
    have hzero' : b.coord i x = 0 := hzero.symm
    have hxi : x ≠ b i := by
      intro hxi
      rw [hxi, b.coord_apply_eq] at hzero'
      norm_num at hzero'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hx)
    let d := dist (b i) x
    have hd : 0 < d := by
      dsimp [d]
      exact dist_pos.mpr hxi.symm
    let δ := ε / (2 * d)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hd)
    let y := AffineMap.lineMap (b i) x (1 + δ)
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball]
      dsimp [y]
      rw [dist_lineMap_right, show (1 : ℝ) - (1 + δ) = -δ by ring,
        norm_neg, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * d < ε
      dsimp [δ]
      have hdne : d ≠ 0 := hd.ne'
      have heq : ε / (2 * d) * d = ε / 2 := by
        field_simp [hdne]
      rw [heq]
      linarith
    have hyC := hball hyball
    have hycoord : 0 ≤ b.coord i y := by
      rw [hC] at hyC
      exact hyC i
    have hcoord : b.coord i y = -δ := by
      dsimp [y]
      rw [AffineMap.apply_lineMap, b.coord_apply_eq, hzero']
      simp [AffineMap.lineMap_apply_module]
    rw [hcoord] at hycoord
    linarith
  · intro x hx
    let P : Set Plane := ⋂ i : Fin 3, (b.coord i) ⁻¹' Set.Ioi 0
    have hPopen : IsOpen P := by
      dsimp [P]
      exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage
        (b.coord i).continuous_of_finiteDimensional
    have hxP : x ∈ P := by
      simp only [P, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
      exact hx
    apply interior_maximal _ hPopen hxP
    intro y hy
    rw [hC]
    intro i
    have : 0 < b.coord i y := by
      have hi := Set.mem_iInter.mp hy i
      simpa only [Set.mem_preimage, Set.mem_Ioi] using hi
    exact this.le

/-- The standard triangle vertices, regarded as an affine basis of the plane. -/
noncomputable def standardTriangleAffineBasis : AffineBasis (Fin 3) ℝ Plane :=
  planeAffineBasisOfTriple standardTriangleVertex standardTriangleVertex_affineIndependent

/-- The standard triangle as an affine simplex. -/
noncomputable def standardTriangleSimplex : Affine.Simplex ℝ Plane 2 where
  points := standardTriangleVertex
  independent := standardTriangleVertex_affineIndependent

/-- The carrier of `standardTriangleCircle` is the frontier of the closed standard triangle. -/
theorem standardTriangleCircle_carrier :
    standardTriangleCircle.carrier =
      frontier (convexHull ℝ (Set.range standardTriangleVertex)) := by
  let S := standardTriangleSimplex
  have hclosed : IsClosed (convexHull ℝ (Set.range standardTriangleVertex)) :=
    ((Set.finite_range standardTriangleVertex).isCompact_convexHull ℝ).isClosed
  rw [hclosed.frontier_eq]
  have hinter : interior (convexHull ℝ (Set.range standardTriangleVertex)) =
      S.interior := by
    have hrange : Set.range (standardTriangleAffineBasis : Fin 3 → Plane) =
        Set.range standardTriangleVertex := rfl
    rw [← hrange, interior_convexHull_affineBasis standardTriangleAffineBasis]
    ext x
    simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_setOf_eq]
    constructor
    · intro hx
      let w : Fin 3 → ℝ := fun i => standardTriangleAffineBasis.coord i x
      refine ⟨w, standardTriangleAffineBasis.sum_coord_apply_eq_one x, ?_, ?_⟩
      · intro i
        have hi := hx i
        constructor
        · exact hi
        · have hsum := standardTriangleAffineBasis.sum_coord_apply_eq_one x
          rw [Fin.sum_univ_three] at hsum
          have h0 := hx (0 : Fin 3)
          have h1 := hx (1 : Fin 3)
          have h2 := hx (2 : Fin 3)
          fin_cases i <;> dsimp [w] <;> nlinarith
      · exact standardTriangleAffineBasis.affineCombination_coord_eq_self x
    · rintro ⟨w, hw, hwI, hwx⟩ i
      have hwx' : (Finset.univ.affineCombination ℝ
          (standardTriangleAffineBasis : Fin 3 → Plane)) w = x := by
        have hb : (standardTriangleAffineBasis : Fin 3 → Plane) =
            standardTriangleVertex := rfl
        rw [hb]
        simpa [S, standardTriangleSimplex] using hwx
      have hcoord := congrArg (standardTriangleAffineBasis.coord i) hwx'.symm
      rw [standardTriangleAffineBasis.coord_apply_combination_of_mem
        (Finset.mem_univ i) hw] at hcoord
      exact hcoord ▸ (hwI i).1
  have hclosedInterior : S.closedInterior =
      convexHull ℝ (Set.range standardTriangleVertex) := by
    exact (Affine.Simplex.convexHull_eq_closedInterior S).symm
  rw [← hclosedInterior]
  change standardTriangleCircle.carrier = S.closedInterior \ interior S.closedInterior
  rw [show interior S.closedInterior = S.interior by
    rw [hclosedInterior, hinter], S.closedInterior_sdiff_interior]
  have hface0 : (S.faceOpposite 0).closedInterior =
      segment ℝ (standardTriangleVertex 1) (standardTriangleVertex 2) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 0),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({0}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 1, standardTriangleVertex 2} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨1, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  have hface1 : (S.faceOpposite 1).closedInterior =
      segment ℝ (standardTriangleVertex 0) (standardTriangleVertex 2) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 1),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({1}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 0, standardTriangleVertex 2} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  have hface2 : (S.faceOpposite 2).closedInterior =
      segment ℝ (standardTriangleVertex 0) (standardTriangleVertex 1) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 2),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({2}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 0, standardTriangleVertex 1} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  ext x
  simp only [PolygonalCircle.carrier, PolygonalCircle.edgeSegment, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := hcases i
    rcases hcase with rfl | rfl | rfl
    · refine ⟨2, ?_⟩
      rw [hface2]
      change x ∈ segment ℝ (standardTriangleVertex 0)
        (standardTriangleVertex ((0 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (0 : ZMod 3) + (1 : ZMod 3) = 1 by decide] at hi
      convert hi using 1
    · refine ⟨0, ?_⟩
      rw [hface0]
      change x ∈ segment ℝ (standardTriangleVertex 1)
        (standardTriangleVertex ((1 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (1 : ZMod 3) + (1 : ZMod 3) = 2 by decide] at hi
      convert hi using 1
    · refine ⟨1, ?_⟩
      rw [hface1, segment_symm]
      change x ∈ segment ℝ (standardTriangleVertex 2)
        (standardTriangleVertex ((2 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (2 : ZMod 3) + (1 : ZMod 3) = 0 by decide] at hi
      convert hi using 1
  · rintro ⟨i, hi⟩
    have hcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hcases i with rfl | rfl | rfl
    · rw [hface0] at hi
      refine ⟨1, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 1)
        (standardTriangleVertex ((1 : ZMod 3) + (1 : ZMod 3)))
      rw [show (1 : ZMod 3) + (1 : ZMod 3) = 2 by decide]
      convert hi using 1
    · rw [hface1] at hi
      refine ⟨2, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 2)
        (standardTriangleVertex ((2 : ZMod 3) + (1 : ZMod 3)))
      rw [show (2 : ZMod 3) + (1 : ZMod 3) = 0 by decide, segment_symm]
      exact hi
    · rw [hface2] at hi
      refine ⟨0, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 0)
        (standardTriangleVertex ((0 : ZMod 3) + (1 : ZMod 3)))
      rw [show (0 : ZMod 3) + (1 : ZMod 3) = 1 by decide]
      convert hi using 1

/-- **Positive anchor** for `PlaneComplex`: the closed standard triangle as a simplicial
complex, with the seven nonempty subsets of its three vertices as faces. -/
noncomputable abbrev standardTrianglePlaneComplex : PlaneComplex where
  Vertex := Fin 3
  position := standardTriangleVertex
  position_injective := standardTriangleVertex_injective
  simplexes := Finset.univ.powerset.filter (·.Nonempty)
  nonempty_of_mem := fun _ hs => (Finset.mem_filter.mp hs).2
  card_le_three := by decide
  down_closed := by decide
  affineIndependent := fun s _ =>
    standardTriangleVertex_affineIndependent.comp_embedding (Function.Embedding.subtype _)
  face_inter := by
    intro s _ t _
    classical
    have hS : AffineIndependent ℝ
        ((↑) : (Finset.univ.image standardTriangleVertex) → Plane) :=
      affineIndependent_finset_coe standardTriangleVertex_affineIndependent fun a ha => by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        exact ⟨i, hi⟩
    have hmain := hS.convexHull_inter
      (t₁ := s.image standardTriangleVertex) (t₂ := t.image standardTriangleVertex)
      (Finset.image_subset_image (Finset.subset_univ s))
      (Finset.image_subset_image (Finset.subset_univ t))
    rw [← Finset.coe_inter, ← Finset.image_inter s t standardTriangleVertex_injective] at hmain
    simpa [Finset.coe_image] using hmain.symm

@[simp] theorem standardTrianglePlaneComplex_position :
    standardTrianglePlaneComplex.position = standardTriangleVertex := rfl

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification04_block_01
/- END ClassificationOfSurfaces.Moise.Anchors -/

/- BEGIN ClassificationOfSurfaces.Moise.ElementaryMove | d874d88ede6885736ddf12097a58b59d032819d50fdbea5ded7aaa3dae54609e -/
section schottkyclassification04_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The elementary supported move in polygonal Schoenflies

This is the normalized version of Moise Figure 3.3.  Four triangles fan from a point `(0,a)`
inside a fixed diamond.  Repositioning the fan point while fixing the four diamond vertices gives
a PL homeomorphism of the diamond, and hence an ambient homeomorphism by identity extension.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Vertices `0,1,2,3` are left, right, top, bottom; vertex `4` is the fan point. -/
def diamondFanPosition (a : ℝ) : Fin 5 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 2, planePoint 0 (-2), planePoint 0 a]

/-- The four maximal triangles in the fan of the diamond. -/
def diamondFanTriangles : Finset (Finset (Fin 5)) :=
  {{0, 4, 2}, {1, 2, 4}, {0, 3, 4}, {1, 4, 3}}

@[simp] theorem diamondFanPosition_apply_zero (a : ℝ) :
    diamondFanPosition a 0 = planePoint (-1) 0 := rfl

@[simp] theorem diamondFanPosition_apply_one (a : ℝ) :
    diamondFanPosition a 1 = planePoint 1 0 := rfl

@[simp] theorem diamondFanPosition_apply_two (a : ℝ) :
    diamondFanPosition a 2 = planePoint 0 2 := rfl

@[simp] theorem diamondFanPosition_apply_three (a : ℝ) :
    diamondFanPosition a 3 = planePoint 0 (-2) := rfl

@[simp] theorem diamondFanPosition_apply_four (a : ℝ) :
    diamondFanPosition a 4 = planePoint 0 a := rfl

theorem diamondFanPosition_injective {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    Function.Injective (diamondFanPosition a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [diamondFanPosition, planePoint] at hij ⊢
  all_goals linarith

private theorem affineIndependent_finset_of_range {V : Type}
    (position : V → Plane) {t : Finset V} (p : Fin 3 → V)
    (hp : AffineIndependent ℝ (position ∘ p)) (hrange : Set.range p = (t : Set V)) :
    AffineIndependent ℝ fun v : t => position v := by
  classical
  let eFun : Fin 3 → t := fun i => ⟨p i, by
    change p i ∈ (t : Set V)
    rw [← hrange]
    exact Set.mem_range_self i⟩
  have heBijective : Function.Bijective eFun := by
    constructor
    · intro i j hij
      apply hp.injective
      exact congrArg (fun v : t => position v) hij
    · rintro ⟨v, hv⟩
      have : v ∈ Set.range p := by rwa [hrange]
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, rfl⟩
  let e : Fin 3 ≃ t := Equiv.ofBijective eFun heBijective
  apply (affineIndependent_equiv e).mp
  convert hp using 1
  funext i
  rfl

theorem diamondFan_affineIndependent {a : ℝ} (ha0 : -2 < a) (ha2 : a < 2)
    {t : Finset (Fin 5)} (ht : t ∈ diamondFanTriangles) :
    AffineIndependent ℝ fun v : t => diamondFanPosition a v := by
  simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![0, 4, 2]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 0,
          diamondFanPosition a 4, diamondFanPosition a 2] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_zero, diamondFanPosition_apply_four,
          diamondFanPosition_apply_two, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![1, 2, 4]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 1,
          diamondFanPosition a 2, diamondFanPosition a 4] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_one, diamondFanPosition_apply_two,
          diamondFanPosition_apply_four, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![0, 3, 4]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 0,
          diamondFanPosition a 3, diamondFanPosition a 4] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_zero, diamondFanPosition_apply_three,
          diamondFanPosition_apply_four, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![1, 4, 3]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 1,
          diamondFanPosition a 4, diamondFanPosition a 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_one, diamondFanPosition_apply_four,
          diamondFanPosition_apply_three, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp

/-- Vertical separator for the upper and lower pairs of left/right fan triangles. -/
noncomputable def diamondVerticalAffine : Plane →ᵃ[ℝ] ℝ := cartesianX

/-- Separator through the left vertex and fan point. -/
noncomputable def diamondLeftAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a • cartesianX - cartesianY + AffineMap.const ℝ Plane a

/-- Separator through the right vertex and fan point. -/
noncomputable def diamondRightAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a • cartesianX + cartesianY - AffineMap.const ℝ Plane a

/-- Separator of the upper-left and lower-right opposite fan triangles. -/
noncomputable def diamondDownDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - cartesianY + AffineMap.const ℝ Plane a

/-- Separator of the upper-right and lower-left opposite fan triangles. -/
noncomputable def diamondUpDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + cartesianY - AffineMap.const ℝ Plane a

@[simp] theorem diamondVerticalAffine_apply (x y : ℝ) :
    diamondVerticalAffine (planePoint x y) = x := rfl

@[simp] theorem diamondLeftAffine_apply (a x y : ℝ) :
    diamondLeftAffine a (planePoint x y) = a * x - y + a := rfl

@[simp] theorem diamondRightAffine_apply (a x y : ℝ) :
    diamondRightAffine a (planePoint x y) = a * x + y - a := rfl

@[simp] theorem diamondDownDiagonalAffine_apply (a x y : ℝ) :
    diamondDownDiagonalAffine a (planePoint x y) = x - y + a := rfl

@[simp] theorem diamondUpDiagonalAffine_apply (a x y : ℝ) :
    diamondUpDiagonalAffine a (planePoint x y) = x + y - a := rfl

/-- Splitting one edge of a nondegenerate triangle at an interior parameter covers the original
triangle by the two resulting triangles. -/
theorem triangle_edge_split_union (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    convexHull ℝ (Set.range ![p 0, p 2, AffineMap.lineMap (p 0) (p 1) c]) ∪
        convexHull ℝ (Set.range ![p 1, p 2, AffineMap.lineMap (p 0) (p 1) c]) =
      convexHull ℝ (Set.range p) := by
  let s := standardTrianglePosition
  let e := triangleAffineEquiv s p standardTrianglePosition_affineIndependent hp
  have href := referenceEdgeSplit_union c hc0 hc1
  have hline : AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c = planePoint c 0 := by
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply, planePoint]
  have hcarrier0 :
      referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set _) =
        Set.range ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c] := by
    ext x
    change x ∈ referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set _) ↔
      x ∈ Set.range ![planePoint 0 0, planePoint 0 1,
        AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c]
    rw [hline]
    simp [referenceEdgeSplitPosition, planePoint]
    tauto
  have hcarrier1 :
      referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set _) =
        Set.range ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c] := by
    ext x
    change x ∈ referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set _) ↔
      x ∈ Set.range ![planePoint 1 0, planePoint 0 1,
        AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c]
    rw [hline]
    simp [referenceEdgeSplitPosition, planePoint]
    tauto
  have href' :
      convexHull ℝ (Set.range ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c]) ∪
          convexHull ℝ (Set.range ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c]) =
        convexHull ℝ (Set.range s) := by
    have href0 :
        convexHull ℝ (referenceEdgeSplitPosition c ''
            (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
          convexHull ℝ (referenceEdgeSplitPosition c ''
            (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
          convexHull ℝ (Set.range standardTrianglePosition) := by
      calc
        convexHull ℝ (referenceEdgeSplitPosition c ''
              (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
            convexHull ℝ (referenceEdgeSplitPosition c ''
              (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
            ⋃ t ∈ referenceEdgeSplitTriangles,
              convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set _)) := by
                ext x
                simp only [Set.mem_union, Set.mem_iUnion]
                constructor
                · rintro (hx | hx)
                  · exact ⟨{0, 2, 3}, by simp [referenceEdgeSplitTriangles], hx⟩
                  · exact ⟨{1, 2, 3}, by simp [referenceEdgeSplitTriangles], hx⟩
                · rintro ⟨t, ht, hxt⟩
                  simp only [referenceEdgeSplitTriangles, Finset.mem_insert,
                    Finset.mem_singleton] at ht
                  rcases ht with rfl | rfl
                  · exact Or.inl hxt
                  · exact Or.inr hxt
        _ = convexHull ℝ (Set.range standardTrianglePosition) := by
          simpa only [standardTrianglePosition] using href
    rw [hcarrier0, hcarrier1] at href0
    simpa [s] using href0
  have hImageHull (r : Fin 3 → Plane) :
      e '' convexHull ℝ (Set.range r) = convexHull ℝ (Set.range (e ∘ r)) := by
    change e.toAffineMap '' convexHull ℝ (Set.range r) = _
    rw [e.toAffineMap.image_convexHull]
    congr 1
    ext x
    simp [Set.mem_image]
  have himage := congrArg (fun A : Set Plane => e '' A) href'
  rw [Set.image_union, hImageHull, hImageHull, hImageHull] at himage
  have hcomp0 : e ∘ ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c] =
      ![p 0, p 2, AffineMap.lineMap (p 0) (p 1) c] := by
    funext i
    fin_cases i
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 0
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 2
    · exact triangleAffineEquiv_apply_lineMap s p
        standardTrianglePosition_affineIndependent hp 0 1 c
  have hcomp1 : e ∘ ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c] =
      ![p 1, p 2, AffineMap.lineMap (p 0) (p 1) c] := by
    funext i
    fin_cases i
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 1
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 2
    · exact triangleAffineEquiv_apply_lineMap s p
        standardTrianglePosition_affineIndependent hp 0 1 c
  have hcomp : e ∘ s = p := by
    funext i
    exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp i
  rw [hcomp0, hcomp1, hcomp] at himage
  exact himage

/-- The left triangular half of the fixed diamond. -/
def diamondLeftRegion : Set Plane :=
  convexHull ℝ (Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0])

/-- The right triangular half of the fixed diamond. -/
def diamondRightRegion : Set Plane :=
  convexHull ℝ (Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0])

/-- The fixed closed patch supporting the elementary move. -/
def diamondPatch : Set Plane := diamondLeftRegion ∪ diamondRightRegion

theorem isClosed_diamondPatch : IsClosed diamondPatch := by
  apply IsClosed.union
  · exact (Set.finite_range _).isClosed_convexHull ℝ
  · exact (Set.finite_range _).isClosed_convexHull ℝ

private theorem diamondCenter_lineMap (a : ℝ) :
    AffineMap.lineMap (planePoint 0 2) (planePoint 0 (-2)) ((2 - a) / 4) =
      planePoint 0 a := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply, planePoint] ; ring

private theorem diamondLeft_affineIndependent :
    AffineIndependent ℝ ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [planePoint, PiLp.sub_apply]

private theorem diamondRight_affineIndependent :
    AffineIndependent ℝ ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [planePoint, PiLp.sub_apply]

theorem diamondFan_left_union {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∪
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      diamondLeftRegion := by
  have hc0 : 0 < (2 - a) / 4 := by linarith
  have hc1 : (2 - a) / 4 < 1 := by linarith
  have hsplit := triangle_edge_split_union
    ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0]
    diamondLeft_affineIndependent ((2 - a) / 4) hc0 hc1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hsplit
  rw [diamondCenter_lineMap] at hsplit
  have htop : diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint (-1) 0, planePoint 0 2} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have hbottom : diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint (-1) 0, planePoint 0 (-2)} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have houter : Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0] =
      ({planePoint (-1) 0, planePoint 0 (-2), planePoint 0 2} : Set Plane) := by
    ext x
    simp
  rw [htop, hbottom, diamondLeftRegion, houter]
  simpa using hsplit

theorem diamondFan_right_union {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∪
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      diamondRightRegion := by
  have hc0 : 0 < (2 - a) / 4 := by linarith
  have hc1 : (2 - a) / 4 < 1 := by linarith
  have hsplit := triangle_edge_split_union
    ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0]
    diamondRight_affineIndependent ((2 - a) / 4) hc0 hc1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hsplit
  rw [diamondCenter_lineMap] at hsplit
  have htop : diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint 1 0, planePoint 0 2} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have hbottom : diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint 1 0, planePoint 0 (-2)} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have houter : Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0] =
      ({planePoint 1 0, planePoint 0 (-2), planePoint 0 2} : Set Plane) := by
    ext x
    simp
  rw [htop, hbottom, diamondRightRegion, houter]
  simpa using hsplit

private theorem diamondFan_inter_02_12 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {1, 2, 4} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 4, 2} {1, 2, 4} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp at hv ⊢

private theorem diamondFan_inter_03_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 3, 4} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 3, 4} {1, 4, 3} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp at hv ⊢

private theorem diamondFan_inter_02_03 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {0, 3, 4} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 4, 2} {0, 3, 4} (-diamondLeftAffine a)
  all_goals
    intro v hv
    fin_cases v <;> simp [diamondLeftAffine_apply] at hv ⊢ ; linarith

private theorem diamondFan_inter_12_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({1, 2, 4} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {1, 2, 4} {1, 4, 3} (diamondRightAffine a)
  all_goals
    intro v hv
    fin_cases v <;> simp [diamondRightAffine_apply] at hv ⊢ ; linarith

private theorem diamondFan_inter_02_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  let s : Finset (Fin 5) := {0, 4, 2}
  let t : Finset (Fin 5) := {1, 4, 3}
  let upperEdge : Finset (Fin 5) := {4, 2}
  let lowerEdge : Finset (Fin 5) := {4, 3}
  have hUpper :
      convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
          {p | (-diamondVerticalAffine) p = 0} =
        convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (s.image (diamondFanPosition a)) (-diamondVerticalAffine) (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [s] at hv ⊢)
    have hfilter : (s.image (diamondFanPosition a)).filter
        (fun p => (-diamondVerticalAffine) p = 0) =
        upperEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [s, upperEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [s, upperEdge] at hv ⊢
        · fin_cases v <;> simp [upperEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  have hLower :
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) ∩
          {p | diamondVerticalAffine p = 0} =
        convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (t.image (diamondFanPosition a)) diamondVerticalAffine (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [t] at hv ⊢)
    have hfilter : (t.image (diamondFanPosition a)).filter
        (fun p => diamondVerticalAffine p = 0) =
        lowerEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [t, lowerEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [t, lowerEdge] at hv ⊢
        · fin_cases v <;> simp [lowerEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  let horizontal : Plane →ᵃ[ℝ] ℝ := cartesianY - AffineMap.const ℝ Plane a
  have hEdges :
      convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) =
        {diamondFanPosition a 4} := by
    have h := convexHull_inter_of_affine_separation
      (upperEdge.image (diamondFanPosition a))
      (lowerEdge.image (diamondFanPosition a))
      ({diamondFanPosition a 4} : Finset Plane) horizontal
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [upperEdge, horizontal] at hv ⊢ ; linarith)
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [lowerEdge, horizontal] at hv ⊢ ; linarith)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [upperEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [upperEdge]⟩, by simp [horizontal]⟩)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [lowerEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [lowerEdge]⟩, by simp [horizontal]⟩)
    simpa only [Finset.coe_image, Finset.coe_singleton, convexHull_singleton] using h
  change convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) = _
  apply Set.Subset.antisymm
  · intro p hp
    have hxle : p 0 ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.1
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [s] at hv ⊢
    have hxge : 0 ≤ p 0 := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.2
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [t] at hv ⊢
    have hxzero : diamondVerticalAffine p = 0 := by
      change p 0 = 0
      linarith
    have hpUpper : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
      rw [← hUpper]
      exact ⟨hp.1, by simpa using hxzero⟩
    have hpLower : p ∈ convexHull ℝ
        (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
      rw [← hLower]
      exact ⟨hp.2, hxzero⟩
    have hpBoth : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) :=
      ⟨hpUpper, hpLower⟩
    rw [hEdges] at hpBoth
    have hp4 : p = diamondFanPosition a 4 := Set.mem_singleton_iff.mp hpBoth
    subst p
    exact subset_convexHull ℝ _ ⟨4, by simp [], rfl⟩
  · intro p hp
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hp,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hp⟩

private theorem diamondFan_inter_12_03 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({1, 2, 4} : Finset (Fin 5)) ∩ {0, 3, 4} : Finset (Fin 5)) : Set _)) := by
  let s : Finset (Fin 5) := {1, 2, 4}
  let t : Finset (Fin 5) := {0, 3, 4}
  let upperEdge : Finset (Fin 5) := {2, 4}
  let lowerEdge : Finset (Fin 5) := {3, 4}
  have hUpper :
      convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
          {p | diamondVerticalAffine p = 0} =
        convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (s.image (diamondFanPosition a)) diamondVerticalAffine (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [s] at hv ⊢)
    have hfilter : (s.image (diamondFanPosition a)).filter
        (fun p => diamondVerticalAffine p = 0) =
        upperEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [s, upperEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [s, upperEdge] at hv ⊢
        · fin_cases v <;> simp [upperEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  have hLower :
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) ∩
          {p | (-diamondVerticalAffine) p = 0} =
        convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (t.image (diamondFanPosition a)) (-diamondVerticalAffine) (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [t] at hv ⊢)
    have hfilter : (t.image (diamondFanPosition a)).filter
        (fun p => (-diamondVerticalAffine) p = 0) =
        lowerEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [t, lowerEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [t, lowerEdge] at hv ⊢
        · fin_cases v <;> simp [lowerEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  let horizontal : Plane →ᵃ[ℝ] ℝ := cartesianY - AffineMap.const ℝ Plane a
  have hEdges :
      convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) =
        {diamondFanPosition a 4} := by
    have h := convexHull_inter_of_affine_separation
      (upperEdge.image (diamondFanPosition a))
      (lowerEdge.image (diamondFanPosition a))
      ({diamondFanPosition a 4} : Finset Plane) horizontal
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [upperEdge, horizontal] at hv ⊢ ; linarith)
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [lowerEdge, horizontal] at hv ⊢ ; linarith)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [upperEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [upperEdge]⟩, by simp [horizontal]⟩)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [lowerEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [lowerEdge]⟩, by simp [horizontal]⟩)
    simpa only [Finset.coe_image, Finset.coe_singleton, convexHull_singleton] using h
  change convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) = _
  apply Set.Subset.antisymm
  · intro p hp
    have hxge : 0 ≤ p 0 := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.1
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [s] at hv ⊢
    have hxle : p 0 ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.2
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [t] at hv ⊢
    have hxzero : diamondVerticalAffine p = 0 := by
      change p 0 = 0
      linarith
    have hpUpper : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
      rw [← hUpper]
      exact ⟨hp.1, hxzero⟩
    have hpLower : p ∈ convexHull ℝ
        (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
      rw [← hLower]
      exact ⟨hp.2, by simpa using hxzero⟩
    have hpBoth : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) :=
      ⟨hpUpper, hpLower⟩
    rw [hEdges] at hpBoth
    have hp4 : p = diamondFanPosition a 4 := Set.mem_singleton_iff.mp hpBoth
    subst p
    exact subset_convexHull ℝ _ ⟨4, by simp [], rfl⟩
  · intro p hp
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hp,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hp⟩

/-- The four-triangle fan of a fixed diamond, with fan point `(0,a)`. -/
noncomputable def diamondFanMesh (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) : TriangleMesh where
  Vertex := Fin 5
  position := diamondFanPosition a
  position_injective := diamondFanPosition_injective ha0 ha1
  triangles := diamondFanTriangles
  card_triangle := by
    intro t ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  affineIndependent_triangle := fun t ht =>
    diamondFan_affineIndependent ha0 ha1 ht
  triangle_inter := by
    intro s hs t ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
    · simp
    · exact diamondFan_inter_02_12 ha0 ha1
    · exact diamondFan_inter_02_03 ha0 ha1
    · exact diamondFan_inter_02_13 ha0 ha1
    · simpa [Set.inter_comm, Finset.pair_comm] using diamondFan_inter_02_12 ha0 ha1
    · simp
    · exact diamondFan_inter_12_03 ha0 ha1
    · exact diamondFan_inter_12_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_02_03 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_12_03 ha0 ha1
    · simp
    · exact diamondFan_inter_03_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_02_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_12_13 ha0 ha1
    · simpa [Set.inter_comm, Finset.pair_comm] using diamondFan_inter_03_13 ha0 ha1
    · simp

theorem diamondFanMesh_support (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support = diamondPatch := by
  rw [TriangleMesh.toPlaneComplex_support, diamondPatch,
    ← diamondFan_left_union ha0 ha1, ← diamondFan_right_union ha0 ha1]
  change (⋃ t ∈ diamondFanTriangles,
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5)))) = _
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨t, ht, hxt⟩
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl hxt)
    · exact Or.inr (Or.inl hxt)
    · exact Or.inl (Or.inr hxt)
    · exact Or.inr (Or.inr hxt)
  · rintro ((hxt | hxt) | (hxt | hxt))
    · exact ⟨{0, 4, 2}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{0, 3, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 2, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 4, 3}, by simp [diamondFanTriangles], hxt⟩

/-- Slack from the upper-right side of the diamond. -/
noncomputable def diamondSlackUR : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 - 2 • cartesianX - cartesianY

/-- Slack from the upper-left side of the diamond. -/
noncomputable def diamondSlackUL : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 + 2 • cartesianX - cartesianY

/-- Slack from the lower-right side of the diamond. -/
noncomputable def diamondSlackLR : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 - 2 • cartesianX + cartesianY

/-- Slack from the lower-left side of the diamond. -/
noncomputable def diamondSlackLL : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 + 2 • cartesianX + cartesianY

theorem diamondSlackUR_apply (x y : ℝ) :
    diamondSlackUR (planePoint x y) = 2 - 2 * x - y := by
  simp [diamondSlackUR]

theorem diamondSlackUL_apply (x y : ℝ) :
    diamondSlackUL (planePoint x y) = 2 + 2 * x - y := by
  simp [diamondSlackUL]

theorem diamondSlackLR_apply (x y : ℝ) :
    diamondSlackLR (planePoint x y) = 2 - 2 * x + y := by
  simp [diamondSlackLR]

theorem diamondSlackLL_apply (x y : ℝ) :
    diamondSlackLL (planePoint x y) = 2 + 2 * x + y := by
  simp [diamondSlackLL]

@[simp] theorem diamondSlackUR_eq (p : Plane) :
    diamondSlackUR p = 2 - 2 * p 0 - p 1 := by
  simp [diamondSlackUR]

@[simp] theorem diamondSlackUL_eq (p : Plane) :
    diamondSlackUL p = 2 + 2 * p 0 - p 1 := by
  simp [diamondSlackUL]

@[simp] theorem diamondSlackLR_eq (p : Plane) :
    diamondSlackLR p = 2 - 2 * p 0 + p 1 := by
  simp [diamondSlackLR]

@[simp] theorem diamondSlackLL_eq (p : Plane) :
    diamondSlackLL p = 2 + 2 * p 0 + p 1 := by
  simp [diamondSlackLL]

theorem diamondSlackUR_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackUR ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 0 + 4 * x 3 + (2 - a) * x 4 := by
  change diamondSlackUR (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackUR_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

theorem diamondSlackUL_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackUL ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 1 + 4 * x 3 + (2 - a) * x 4 := by
  change diamondSlackUL (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackUL_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

theorem diamondSlackLR_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackLR ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 0 + 4 * x 2 + (2 + a) * x 4 := by
  change diamondSlackLR (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackLR_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

theorem diamondSlackLL_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackLL ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 1 + 4 * x 2 + (2 + a) * x 4 := by
  change diamondSlackLL (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackLL_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

/-- Closed four-halfspace description of the diamond. -/
def InDiamond (p : Plane) : Prop :=
  0 ≤ diamondSlackUR p ∧ 0 ≤ diamondSlackUL p ∧
    0 ≤ diamondSlackLR p ∧ 0 ≤ diamondSlackLL p

theorem diamondPatch_eq_inDiamond : diamondPatch = {p | InDiamond p} := by
  apply Set.Subset.antisymm
  · rintro p (hp | hp)
    all_goals
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage _ ) hp
        rintro q ⟨i, rfl⟩
        fin_cases i <;> simp []
  · intro p hp
    rcases hp with ⟨hUR, hUL, hLR, hLL⟩
    rw [diamondSlackUR_eq] at hUR
    rw [diamondSlackUL_eq] at hUL
    rw [diamondSlackLR_eq] at hLR
    rw [diamondSlackLL_eq] at hLL
    by_cases hx : p 0 ≤ 0
    · left
      rw [diamondLeftRegion]
      let w : Fin 3 → ℝ :=
        ![(p 1 + 2 + 2 * p 0) / 4, (2 + 2 * p 0 - p 1) / 4, -p 0]
      apply mem_convexHull_range_fin3_of_weights _ p w
      · intro i
        fin_cases i <;> simp [w] <;>
          change 0 ≤ _ at hUR hUL hLR hLL <;> linarith
      · simp [w]
        ring
      · ext i
        fin_cases i <;> simp [w, planePoint]
        all_goals ring
    · right
      rw [diamondRightRegion]
      have hx' : 0 ≤ p 0 := le_of_not_ge hx
      let w : Fin 3 → ℝ :=
        ![(p 1 + 2 - 2 * p 0) / 4, (2 - 2 * p 0 - p 1) / 4, p 0]
      apply mem_convexHull_range_fin3_of_weights _ p w
      · intro i
        fin_cases i <;> simp [w] <;>
          change 0 ≤ _ at hUR hUL hLR hLL <;> linarith
      · simp [w]
        ring
      · ext i
        fin_cases i <;> simp [w, planePoint]
        all_goals ring

/-- Points satisfying all four diamond inequalities strictly form an open subset of the patch. -/
def StrictlyInDiamond : Set Plane :=
  {p | 0 < diamondSlackUR p ∧ 0 < diamondSlackUL p ∧
    0 < diamondSlackLR p ∧ 0 < diamondSlackLL p}

theorem baryEval_mem_strictlyInDiamond_of_center_pos (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (h0 : ∀ v, 0 ≤ x v) (hsum : ∑ v, x v = 1) (h4 : 0 < x 4) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x ∈ StrictlyInDiamond := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [diamondSlackUR_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 0, h0 3]
  · rw [diamondSlackUL_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 1, h0 3]
  · rw [diamondSlackLR_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 0, h0 2]
  · rw [diamondSlackLL_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 1, h0 2]

theorem isOpen_strictlyInDiamond : IsOpen StrictlyInDiamond := by
  change IsOpen ((diamondSlackUR ⁻¹' Set.Ioi 0) ∩
    ((diamondSlackUL ⁻¹' Set.Ioi 0) ∩ ((diamondSlackLR ⁻¹' Set.Ioi 0) ∩
      (diamondSlackLL ⁻¹' Set.Ioi 0))))
  exact (isOpen_Ioi.preimage diamondSlackUR.continuous_of_finiteDimensional).inter
    ((isOpen_Ioi.preimage diamondSlackUL.continuous_of_finiteDimensional).inter
      ((isOpen_Ioi.preimage diamondSlackLR.continuous_of_finiteDimensional).inter
        (isOpen_Ioi.preimage diamondSlackLL.continuous_of_finiteDimensional)))

theorem strictlyInDiamond_subset_patch : StrictlyInDiamond ⊆ diamondPatch := by
  rw [diamondPatch_eq_inDiamond]
  rintro p ⟨hUR, hUL, hLR, hLL⟩
  exact ⟨hUR.le, hUL.le, hLR.le, hLL.le⟩

theorem strictlyInDiamond_subset_interior : StrictlyInDiamond ⊆ interior diamondPatch :=
  interior_maximal strictlyInDiamond_subset_patch isOpen_strictlyInDiamond

/-- The fixed abstract diamond fan with its center repositioned from height `a` to height `b`. -/
noncomputable def diamondFanReposition (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) : TriangleMesh :=
  (diamondFanMesh a ha0 ha1).reposition (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter

theorem diamondFanReposition_support (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support = diamondPatch := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ diamondFanTriangles,
    convexHull ℝ (diamondFanPosition b '' (t : Set (Fin 5)))) = diamondPatch
  simpa only [TriangleMesh.toPlaneComplex_support, diamondFanMesh] using
    diamondFanMesh_support b hb0 hb1

theorem diamondFanReposition_support_eq_source (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support =
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanReposition_support a b ha0 ha1 hb0 hb1).trans
    (diamondFanMesh_support a ha0 ha1).symm

theorem diamondFanReposition_baryEval_eq_of_center_zero (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (x : Fin 5 → ℝ) (h4 : x 4 = 0) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval x =
      (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x := by
  change (∑ v : Fin 5, x v • diamondFanPosition b v) =
    ∑ v : Fin 5, x v • diamondFanPosition a v
  simp [diamondFanPosition, Fin.sum_univ_succ, h4]

/-- Preserve barycentric coordinates while moving the fan point from `(0,a)` to `(0,b)`. -/
noncomputable def diamondFanSupportHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support ≃ₜ
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).repositionHomeomorph (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter

/-- The `diamondFanCenterRealization` declaration. -/
noncomputable def diamondFanCenterRealization (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x : Fin 5 → ℝ := Pi.single 4 1
  refine ⟨x, ⟨fun w => (Pi.single_nonneg.mpr zero_le_one : (0 : Fin 5 → ℝ) ≤ Pi.single 4 1) w, by simp [x]⟩, {0, 4, 2}, ?_, ?_⟩
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    simp only [x, Pi.single_apply]
    split_ifs with h
    · subst v
      simp at hv
    · rfl

@[simp] theorem diamondFanCenterRealization_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanCenterRealization a ha0 ha1).1 = planePoint 0 a := by
  change (∑ v : Fin 5, Pi.single 4 1 v • diamondFanPosition a v) = planePoint 0 a
  simp [Pi.single_apply]

theorem diamondFanSupportHomeomorph_center (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    ((diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1)
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1]
        rw [diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ : Plane) = planePoint 0 b := by
  let x := diamondFanCenterRealization a ha0 ha1
  have hxold :
      (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
        (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2 x =
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1]
        rw [diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ := by
    apply Subtype.ext
    exact diamondFanCenterRealization_baryEval a ha0 ha1
  change ((diamondFanMesh a ha0 ha1).repositionHomeomorph (diamondFanPosition b)
      (diamondFanPosition_injective hb0 hb1)
      (diamondFanMesh b hb0 hb1).affineIndependent_triangle
      (diamondFanMesh b hb0 hb1).triangle_inter
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ : Plane) = planePoint 0 b
  erw [TriangleMesh.coe_repositionHomeomorph_apply]
  have hinv :
      ((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
        (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm
          ⟨planePoint 0 a, by
            rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
            simp [InDiamond]
            constructor <;> linarith⟩ = x := by
    rw [← hxold]
    exact ((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
      (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm_apply_apply x
  rw [hinv]
  change (∑ v : Fin 5, Pi.single 4 1 v • diamondFanPosition b v) = planePoint 0 b
  simp [Pi.single_apply]

/-- The barycentric fan move, viewed as a self-homeomorphism of the original diamond support. -/
noncomputable def diamondFanPatchHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support ≃ₜ
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1).trans
    (Homeomorph.setCongr (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1))

theorem diamondFanPatchHomeomorph_apply_val (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (z : (diamondFanMesh a ha0 ha1).toPlaneComplex.support) :
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) =
      (diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) := by
  simp only [diamondFanPatchHomeomorph, Homeomorph.trans_apply]
  apply coe_setCongr_apply

theorem diamondFanPatchHomeomorph_fixed_frontier (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (p : Plane) (hp : p ∈ frontier (diamondFanMesh a ha0 ha1).toPlaneComplex.support) :
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
      ⟨p,
        (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩
      : Plane) = p := by
  let e := (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
  let z : (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
    ⟨p, (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩
  let x : GeometricRealization (Fin 5)
      (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := e.symm z
  let weights : Fin 5 → ℝ := x.1
  have hxstd : (∀ v, 0 ≤ weights v) ∧ ∑ v, weights v = 1 := by
    exact x.property.1
  have hxeval : (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval weights = p := by
    have he : e x = z := e.apply_symm_apply z
    exact congrArg Subtype.val he
  have hx4 : weights 4 = 0 := by
    by_contra hne
    have hpos : 0 < weights 4 := lt_of_le_of_ne (hxstd.1 4) (Ne.symm hne)
    have hstrict := baryEval_mem_strictlyInDiamond_of_center_pos a ha0 ha1 weights
      hxstd.1 hxstd.2 hpos
    have hint : p ∈ interior diamondPatch := by
      rw [← hxeval]
      exact strictlyInDiamond_subset_interior hstrict
    have hfront : p ∈ frontier diamondPatch := by
      simpa only [diamondFanMesh_support a ha0 ha1] using hp
    exact (Set.disjoint_left.1 disjoint_interior_frontier hint hfront)
  have hbary :
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval weights = p :=
    (diamondFanReposition_baryEval_eq_of_center_zero a b ha0 ha1 hb0 hb1 weights hx4).trans
      hxeval
  have hmove : (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) =
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval
        (((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
          (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm z).1 := by
    exact TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply
      (diamondFanMesh a ha0 ha1) (diamondFanPosition b)
      (diamondFanPosition_injective hb0 hb1)
      (diamondFanMesh b hb0 hb1).affineIndependent_triangle
      (diamondFanMesh b hb0 hb1).triangle_inter
      (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1) z
  calc
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
        ⟨p,
          (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩ :
      Plane) = (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) := rfl
    _ = _ := hmove
    _ = p := by simpa only [weights, x, e] using hbary

/-- The elementary fan move extended by the identity to the whole plane. -/
noncomputable def diamondFanAmbientHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) : Plane ≃ₜ Plane :=
  (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)

theorem diamondFanAmbientHomeomorph_center (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
  diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1 (planePoint 0 a) =
      planePoint 0 b := by
  erw [diamondFanAmbientHomeomorph, TriangleMesh.ambientRepositionHomeomorph,
    extendHomeomorphByIdentity_apply_mem _ _ _ (by
      rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
      simp [InDiamond]
      constructor <;> linarith)]
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨planePoint 0 a, by
      rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
      simp [InDiamond]
      constructor <;> linarith⟩ : Plane) = planePoint 0 b
  rw [diamondFanPatchHomeomorph_apply_val]
  exact diamondFanSupportHomeomorph_center a b ha0 ha1 hb0 hb1

theorem diamondFanAmbientHomeomorph_eqOn_compl (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    Set.EqOn (diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1) id diamondPatchᶜ := by
  intro p hp
  apply (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph_eqOn_compl
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)
  rwa [diamondFanMesh_support a ha0 ha1]

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification04_block_02
/- END ClassificationOfSurfaces.Moise.ElementaryMove -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicMidpointSubdivision | 8f0b3062360f81b0c33dfccfc93099b71657d84201b2addaa357f86015ed6b31 -/
section schottkyclassification04_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Midpoint subdivision of an intrinsic two-complex

This file constructs the intrinsic 1-to-4 subdivision used to make the source of Moise's
PL-approximation theorem fine.  A new vertex is attached to every old edge.  Each old triangle is
then divided into its three corner triangles and its central triangle.  Since edge midpoints are
indexed by the old edge itself, the construction is automatically coherent across adjacent
faces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

@[simp] theorem zmod3_three_add (i : ZMod 3) : 3 + i = i :=
  (by decide : ∀ i : ZMod 3, 3 + i = i) i

@[simp] theorem zmod3_add_three (i : ZMod 3) : i + 3 = i :=
  (by decide : ∀ i : ZMod 3, i + 3 = i) i

@[simp] theorem zmod3_one_add (i : ZMod 3) : 1 + i = i + 1 := by abel

@[simp] theorem zmod3_two_add (i : ZMod 3) : 2 + i = i + 2 := by abel

@[simp] theorem zmod3_add_two_add_one (i : ZMod 3) : i + 2 + 1 = i :=
  (by decide : ∀ i : ZMod 3, i + 2 + 1 = i) i

@[simp] theorem zmod3_add_one_add_one (i : ZMod 3) : i + 1 + 1 = i + 2 := by ring

@[simp] theorem zmod3_add_one_add_two (i : ZMod 3) : i + 1 + 2 = i :=
  (by decide : ∀ i : ZMod 3, i + 1 + 2 = i) i

@[simp] theorem zmod3_add_two_add_two (i : ZMod 3) : i + 2 + 2 = i + 1 :=
  (by decide : ∀ i : ZMod 3, i + 2 + 2 = i + 1) i

/-- Vertices of the midpoint subdivision: old vertices and one new vertex for every old edge. -/
abbrev MidpointVertex := K.Vertex ⊕ K.Edge

/-- The corner triangle at the `i`-th vertex of an old face. -/
noncomputable def midpointCornerFace (t : K.Face) (i : ZMod 3) :
    Finset K.MidpointVertex :=
  {Sum.inl (K.faceVertex t i), Sum.inr (K.faceEdge t i),
    Sum.inr (K.faceEdge t (i + 2))}

/-- The central triangle of the midpoint subdivision of an old face. -/
noncomputable def midpointCentralFace (t : K.Face) : Finset K.MidpointVertex :=
  Finset.univ.image (fun i : ZMod 3 => Sum.inr (K.faceEdge t i))

/-- The four midpoint triangles belonging to one old face. -/
noncomputable def midpointFacesOver (t : K.Face) : Finset (Finset K.MidpointVertex) :=
  (Finset.univ.image (K.midpointCornerFace t)) ∪ {K.midpointCentralFace t}

/-- All maximal faces in the midpoint subdivision. -/
noncomputable def midpointFaces : Finset (Finset K.MidpointVertex) :=
  K.faces.attach.biUnion K.midpointFacesOver

theorem faceEdge_ne_add_two (t : K.Face) (i : ZMod 3) :
    K.faceEdge t i ≠ K.faceEdge t (i + 2) := by
  intro h
  apply K.faceEdge_ne_next t (i + 2)
  have hcycle : i + 2 + 1 = i :=
    (by decide : ∀ i : ZMod 3, i + 2 + 1 = i) i
  rw [hcycle]
  exact h.symm

theorem faceEdge_injective (t : K.Face) : Function.Injective (K.faceEdge t) := by
  intro i j hij
  by_contra hne
  have hcases : j = i + 1 ∨ j = i + 2 := by
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · exact (hne h.symm).elim
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with rfl | rfl
  · exact K.faceEdge_ne_next t i hij
  · exact K.faceEdge_ne_add_two t i hij

theorem midpointCornerFace_card (t : K.Face) (i : ZMod 3) :
    (K.midpointCornerFace t i).card = 3 := by
  simp [midpointCornerFace, K.faceEdge_ne_add_two t i]

theorem midpointCentralFace_card (t : K.Face) :
    (K.midpointCentralFace t).card = 3 := by
  rw [midpointCentralFace, Finset.card_image_iff.mpr]
  · decide
  · intro i _ j _ hij
    exact K.faceEdge_injective t (Sum.inr.inj hij)

theorem midpointFacesOver_card (t : K.Face) {s : Finset K.MidpointVertex}
    (hs : s ∈ K.midpointFacesOver t) : s.card = 3 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hs | hs
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact K.midpointCornerFace_card t i
  · rw [Finset.mem_singleton.mp hs]
    exact K.midpointCentralFace_card t

/-- The finite abstract complex underlying midpoint subdivision. -/
noncomputable def midpointComplex : IntrinsicTwoComplex where
  Vertex := K.MidpointVertex
  faces := K.midpointFaces
  faces_card := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
    exact K.midpointFacesOver_card t hst

@[simp] theorem midpointComplex_faces : K.midpointComplex.faces = K.midpointFaces := rfl

/-- Every refined face remembers an old face which contains it geometrically. -/
theorem exists_parentFace_of_mem_midpointFaces
    {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFaces) :
    ∃ t : K.Face, s ∈ K.midpointFacesOver t := by
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
  exact ⟨t, hst⟩

/-- A chosen parent of a midpoint-subdivision face.  Geometric arguments use only
`midpointFace_mem_parent`; uniqueness is not needed for the adaptive open-complex
construction. -/
noncomputable def midpointParentFace (s : K.midpointComplex.Face) : K.Face :=
  Classical.choose (K.exists_parentFace_of_mem_midpointFaces s.2)

theorem midpointFace_mem_parent (s : K.midpointComplex.Face) :
    s.1 ∈ K.midpointFacesOver (K.midpointParentFace s) :=
  Classical.choose_spec (K.exists_parentFace_of_mem_midpointFaces s.2)

/-- Canonical old barycentric position of a midpoint-subdivision vertex. -/
noncomputable def midpointPosition : K.MidpointVertex → (K.Vertex → ℝ)
  | Sum.inl v => Pi.single v 1
  | Sum.inr e => fun v => if v ∈ e.1 then (2 : ℝ)⁻¹ else 0

@[simp] theorem midpointPosition_old (v : K.Vertex) :
    K.midpointPosition (Sum.inl v) = Pi.single v 1 := rfl

@[simp] theorem midpointPosition_edge_apply (e : K.Edge) (v : K.Vertex) :
    K.midpointPosition (Sum.inr e) v = if v ∈ e.1 then (2 : ℝ)⁻¹ else 0 := rfl

theorem midpointPosition_nonneg (w : K.MidpointVertex) (u : K.Vertex) :
    0 ≤ K.midpointPosition w u := by
  rcases w with v | e
  · by_cases h : u = v
    · subst u
      simp [midpointPosition]
    · simp [midpointPosition, h]
  · simp only [midpointPosition]
    split_ifs <;> norm_num

theorem sum_midpointPosition (w : K.MidpointVertex) :
    ∑ v, K.midpointPosition w v = 1 := by
  rcases w with v | e
  · simp [midpointPosition]
  · simp [midpointPosition, K.card_of_mem_edges e.2]

/-- Affine barycentric evaluation from midpoint coordinates to old coordinates. -/
noncomputable def midpointEvalAffine :
    (K.MidpointVertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (∑ w, (LinearMap.proj w).smulRight (K.midpointPosition w)).toAffineMap

@[simp] theorem midpointEvalAffine_apply (x : K.MidpointVertex → ℝ) :
    K.midpointEvalAffine x = ∑ w, x w • K.midpointPosition w := by
  simp [midpointEvalAffine]

theorem midpointEvalAffine_eq_sum_of_support {x : K.MidpointVertex → ℝ}
    {s : Finset K.MidpointVertex} (hsupp : ∀ w ∉ s, x w = 0) :
    K.midpointEvalAffine x = ∑ w ∈ s, x w • K.midpointPosition w := by
  rw [K.midpointEvalAffine_apply]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun w _ hw => by rw [hsupp w hw, zero_smul])).symm

theorem sum_eq_sum_of_midpointSupport {x : K.MidpointVertex → ℝ}
    {s : Finset K.MidpointVertex} (hsupp : ∀ w ∉ s, x w = 0) :
    ∑ w, x w = ∑ w ∈ s, x w :=
  (Finset.sum_subset (Finset.subset_univ s) (fun w _ hw => hsupp w hw)).symm

theorem exists_faceVertex_eq_of_mem (t : K.Face) {v : K.Vertex} (hv : v ∈ t.1) :
    ∃ i : ZMod 3, K.faceVertex t i = v := by
  let j : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hv⟩
  let i : ZMod 3 := ZMod.finEquiv 3 j
  refine ⟨i, ?_⟩
  simp [faceVertex, i, j]

theorem midpointCentralFace_eq (t : K.Face) (i : ZMod 3) :
    K.midpointCentralFace t =
      {Sum.inr (K.faceEdge t i), Sum.inr (K.faceEdge t (i + 1)),
        Sum.inr (K.faceEdge t (i + 2))} := by
  rw [midpointCentralFace]
  have hu : (Finset.univ : Finset (ZMod 3)) = {i, i + 1, i + 2} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j
  rw [hu]
  simp

theorem midpointEval_corner_self
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t i) =
      x (Sum.inl (K.faceVertex t i)) +
        (x (Sum.inr (K.faceEdge t i)) + x (Sum.inr (K.faceEdge t (i + 2)))) / 2 := by
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceVertex_ne_next t i,
    K.faceVertex_ne_add_two t i, K.faceEdge_ne_add_two t i]
  ring

theorem midpointEval_corner_next
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t (i + 1)) =
      x (Sum.inr (K.faceEdge t i)) / 2 := by
  have h12 : K.faceVertex t (i + 1) ≠ K.faceVertex t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceVertex_ne_next t (i + 1)
  have h10 : K.faceVertex t (i + 1) ≠ K.faceVertex t i :=
    (K.faceVertex_ne_next t i).symm
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceEdge_ne_add_two t i,
    h12, h10]
  ring

theorem midpointEval_corner_prev
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t (i + 2)) =
      x (Sum.inr (K.faceEdge t (i + 2))) / 2 := by
  have h20 : K.faceVertex t (i + 2) ≠ K.faceVertex t i :=
    (K.faceVertex_ne_add_two t i).symm
  have h21 : K.faceVertex t (i + 2) ≠ K.faceVertex t (i + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using (K.faceVertex_ne_next t (i + 1)).symm
  rw [K.midpointEvalAffine_eq_sum_of_support hx]
  simp [midpointCornerFace, midpointPosition, K.faceEdge_ne_add_two t i, h20, h21]
  ring

theorem midpointEval_central_coord
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0) :
    K.midpointEvalAffine x (K.faceVertex t i) =
      (x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 2)))) / 2 := by
  have h12 : K.faceVertex t (i + 1) ≠ K.faceVertex t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceVertex_ne_next t (i + 1)
  have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
  have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
  have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using K.faceEdge_ne_next t (i + 1)
  rw [K.midpointEvalAffine_eq_sum_of_support hx, K.midpointCentralFace_eq t i]
  simp [midpointPosition, he01, he02, he12, K.faceVertex_ne_next t i,
    K.faceVertex_ne_add_two t i]
  ring

/-- Coefficient of an old vertex recovered from a point of the subdivided simplex. -/
noncomputable def midpointRecoverOld (p : K.Vertex → ℝ) (v : K.Vertex) : ℝ :=
  max (2 * p v - 1) 0

/-- Coefficient of an edge midpoint recovered from old barycentric coordinates.  The formula is
symmetric in the two endpoints despite the arbitrary endpoint ordering. -/
noncomputable def midpointRecoverEdge (p : K.Vertex → ℝ) (e : K.Edge) : ℝ :=
  max 0 (min (2 * p (K.edgeFirst e))
    (min (2 * p (K.edgeSecond e))
      (2 * (p (K.edgeFirst e) + p (K.edgeSecond e)) - 1)))

/-- The inverse-coordinate formula for midpoint evaluation. -/
noncomputable def midpointRecover (p : K.Vertex → ℝ) : K.MidpointVertex → ℝ
  | Sum.inl v => K.midpointRecoverOld p v
  | Sum.inr e => K.midpointRecoverEdge p e

theorem midpointRecoverEdge_faceEdge (p : K.Vertex → ℝ) (t : K.Face) (i : ZMod 3) :
    K.midpointRecoverEdge p (K.faceEdge t i) =
      max 0 (min (2 * p (K.faceVertex t i))
        (min (2 * p (K.faceVertex t (i + 1)))
          (2 * (p (K.faceVertex t i) + p (K.faceVertex t (i + 1))) - 1))) := by
  rcases K.faceEdge_endpoint_order t i with h | h
  · simp [midpointRecoverEdge, h.1, h.2]
  · simp only [midpointRecoverEdge, h.1, h.2]
    congr 1
    ac_rfl

/-- Every old edge contained in a face is one of its three cyclic edges. -/
theorem exists_faceEdge_eq_of_subset (t : K.Face) (e : K.Edge) (het : e.1 ⊆ t.1) :
    ∃ i : ZMod 3, K.faceEdge t i = e := by
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem t (het (K.edgeFirst_mem e))
  obtain ⟨j, hj⟩ := K.exists_faceVertex_eq_of_mem t (het (K.edgeSecond_mem e))
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
    simp only [zmod3_add_two_add_one]
    rw [hi, hj]
    ext v
    simp [or_comm]

theorem faceEdge_subset_face (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 ⊆ t.1 := by
  intro v hv
  simp only [K.faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact K.faceVertex_mem t i
  · exact K.faceVertex_mem t (i + 1)

/-- Every vertex of a refined face is supported on its parent old face. -/
theorem midpointPosition_support_of_mem_face
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {w : K.MidpointVertex} (hw : w ∈ s) {v : K.Vertex} (hv : v ∉ t.1) :
    K.midpointPosition w v = 0 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hs | hs
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Pi.single_eq_of_ne (fun h => hv (by rw [h]; exact K.faceVertex_mem t i)) 1
    · have hvi : v ≠ K.faceVertex t i :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
      have hvj : v ≠ K.faceVertex t (i + 1) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 1))
      simp [midpointPosition, hvi, hvj]
    · have hvi : v ≠ K.faceVertex t (i + 2) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 2))
      have hvj : v ≠ K.faceVertex t (i + 2 + 1) :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 2 + 1))
      have hv0 : v ≠ K.faceVertex t i :=
        fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
      simp [midpointPosition, hvi, hv0]
  · rw [Finset.mem_singleton.mp hs] at hw
    rw [midpointCentralFace] at hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    have hvi : v ≠ K.faceVertex t i :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
    have hvj : v ≠ K.faceVertex t (i + 1) :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t (i + 1))
    simp [midpointPosition, hvi, hvj]

/-- The affine midpoint evaluation sends a refined face into its parent old face. -/
theorem midpointEvalAffine_support
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {x : K.MidpointVertex → ℝ} (hxs : ∀ w ∉ s, x w = 0) {v : K.Vertex}
    (hv : v ∉ t.1) :
    K.midpointEvalAffine x v = 0 := by
  classical
  rw [K.midpointEvalAffine_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w ∈ s
  · rw [Pi.smul_apply, K.midpointPosition_support_of_mem_face t hs hw hv, smul_zero]
  · rw [hxs w hw, zero_smul]
    rfl

/-- Every old vertex of a parent face receives positive weight from at least one vertex of each
midpoint child. -/
theorem exists_midpointPosition_pos_of_mem_parent
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {v : K.Vertex} (hv : v ∈ t.1) :
    ∃ w ∈ s, 0 < K.midpointPosition w v := by
  obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      hji | hji | hji
    · subst j
      refine ⟨Sum.inl (K.faceVertex t i), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
    · subst j
      refine ⟨Sum.inr (K.faceEdge t i), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
    · subst j
      refine ⟨Sum.inr (K.faceEdge t (i + 2)), ?_, ?_⟩
      · simp [midpointCornerFace]
      · simp [midpointPosition]
  · rw [Finset.mem_singleton.mp hcentral]
    refine ⟨Sum.inr (K.faceEdge t j), ?_, ?_⟩
    · simp [midpointCentralFace]
    · simp [midpointPosition]

/-- A point with strictly positive coordinates on a midpoint child maps to a point with strictly
positive coordinates on its parent. -/
theorem midpointEvalAffine_pos_on_parent
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {x : K.MidpointVertex → ℝ} (hxs : ∀ w ∉ s, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hxpos : ∀ w ∈ s, 0 < x w)
    {v : K.Vertex} (hv : v ∈ t.1) :
    0 < K.midpointEvalAffine x v := by
  obtain ⟨w, hws, hwpos⟩ := K.exists_midpointPosition_pos_of_mem_parent t hs hv
  rw [K.midpointEvalAffine_eq_sum_of_support hxs, Finset.sum_apply]
  apply Finset.sum_pos'
  · intro q hq
    exact mul_nonneg (hx0 q) (K.midpointPosition_nonneg q v)
  · exact ⟨w, hws, mul_pos (hxpos w hws) hwpos⟩

/-- A midpoint child has a unique old parent triangle. -/
theorem midpointFacesOver_parent_unique
    {t u : K.Face} {s : Finset K.MidpointVertex}
    (hst : s ∈ K.midpointFacesOver t)
    (hsu : s ∈ K.midpointFacesOver u) :
    t = u := by
  let x : K.MidpointVertex → ℝ :=
    fun w ↦ if w ∈ s then 1 else 0
  have hxs : ∀ w ∉ s, x w = 0 := by
    intro w hw
    simp [x, hw]
  have hx0 : ∀ w, 0 ≤ x w := by
    intro w
    simp only [x]
    split_ifs <;> norm_num
  have hxpos : ∀ w ∈ s, 0 < x w := by
    intro w hw
    simp [x, hw]
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro v hvt
    by_contra hvu
    have hpos :=
      K.midpointEvalAffine_pos_on_parent t hst hxs hx0 hxpos hvt
    have hzero :=
      K.midpointEvalAffine_support u hsu hxs hvu
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  · intro v hvu
    by_contra hvt
    have hpos :=
      K.midpointEvalAffine_pos_on_parent u hsu hxs hx0 hxpos hvu
    have hzero :=
      K.midpointEvalAffine_support t hst hxs hvt
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)

/-- Inside one old parent, a refined edge joining an old vertex to an old-edge midpoint belongs
to at most one midpoint child. -/
theorem midpointFacesOver_mixed_edge_card_le_one
    (t : K.Face) (v : K.Vertex) (e : K.Edge) :
    ((K.midpointFacesOver t).filter fun s ↦
      ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  obtain ⟨haOver, haEdge⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbOver, hbEdge⟩ := Finset.mem_filter.mp hb
  rw [midpointFacesOver, Finset.mem_union] at haOver hbOver
  rcases haOver with haCorner | haCentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp haCorner
    rcases hbOver with hbCorner | hbCentral
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbCorner
      have hvi :
          v = K.faceVertex t i := by
        have hv := haEdge
          (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
        simpa [midpointCornerFace] using hv
      have hvj :
          v = K.faceVertex t j := by
        have hv := hbEdge
          (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
        simpa [midpointCornerFace] using hv
      have hij : i = j :=
        K.faceVertex_injective t (hvi.symm.trans hvj)
      rw [hij]
    · rw [Finset.mem_singleton.mp hbCentral] at hbEdge
      have hv := hbEdge
        (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
      simp [midpointCentralFace] at hv
  · rw [Finset.mem_singleton.mp haCentral] at haEdge
    have hv := haEdge
      (Finset.mem_insert_self (Sum.inl v) {Sum.inr e})
    simp [midpointCentralFace] at hv

/-- An old edge whose midpoint occurs in a midpoint child belongs to that child's parent. -/
theorem edge_subset_parent_of_midpoint_mem
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    (e : K.Edge) (he : Sum.inr e ∈ s) :
    e.1 ⊆ t.1 := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he | he
    · exact (Sum.inr_ne_inl he).elim
    · rw [Sum.inr.inj he]
      exact K.faceEdge_subset_face t i
    · rw [Sum.inr.inj he]
      exact K.faceEdge_subset_face t (i + 2)
  · rw [Finset.mem_singleton.mp hcentral, midpointCentralFace] at he
    obtain ⟨i, -, he⟩ := Finset.mem_image.mp he
    rw [← Sum.inr.inj he]
    exact K.faceEdge_subset_face t i

/-- A midpoint child contains at most one old vertex. -/
theorem oldVertex_eq_of_mem_midpointFace
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    {v w : K.Vertex} (hv : Sum.inl v ∈ s) (hw : Sum.inl w ∈ s) :
    v = w := by
  rw [midpointFacesOver, Finset.mem_union] at hs
  rcases hs with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    have hv' : v = K.faceVertex t i := by
      simpa [midpointCornerFace] using hv
    have hw' : w = K.faceVertex t i := by
      simpa [midpointCornerFace] using hw
    exact hv'.trans hw'.symm
  · rw [Finset.mem_singleton.mp hcentral, midpointCentralFace] at hv
    simp at hv

/-- Two distinct edges of a triangular face cover the whole face. -/
theorem faceEdge_union_eq_face_of_ne
    (t : K.Face) {i j : ZMod 3} (hij : i ≠ j) :
    (K.faceEdge t i).1 ∪ (K.faceEdge t j).1 = t.1 := by
  rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
    h | h | h
  · exact (hij h.symm).elim
  · subst j
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (K.faceEdge_subset_face t i)
        (K.faceEdge_subset_face t (i + 1))
    · intro v hv
      obtain ⟨k, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
      rcases (by decide :
          ∀ i k : ZMod 3, k = i ∨ k = i + 1 ∨ k = i + 2) i k with
        rfl | rfl | rfl <;> simp []
  · subst j
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (K.faceEdge_subset_face t i)
        (K.faceEdge_subset_face t (i + 2))
    · intro v hv
      obtain ⟨k, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
      rcases (by decide :
          ∀ i k : ZMod 3, k = i ∨ k = i + 1 ∨ k = i + 2) i k with
        rfl | rfl | rfl <;> simp []

/-- Two distinct old edges determine their triangular parent. -/
theorem face_eq_of_two_edges_subset
    {t u : K.Face} {e d : K.Edge} (hed : e ≠ d)
    (het : e.1 ⊆ t.1) (hdt : d.1 ⊆ t.1)
    (heu : e.1 ⊆ u.1) (hdu : d.1 ⊆ u.1) :
    t = u := by
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset t e het
  obtain ⟨j, hj⟩ := K.exists_faceEdge_eq_of_subset t d hdt
  obtain ⟨k, hk⟩ := K.exists_faceEdge_eq_of_subset u e heu
  obtain ⟨l, hl⟩ := K.exists_faceEdge_eq_of_subset u d hdu
  have hij : i ≠ j := by
    intro h
    apply hed
    rw [← hi, ← hj, h]
  have hkl : k ≠ l := by
    intro h
    apply hed
    rw [← hk, ← hl, h]
  apply Subtype.ext
  calc
    t.1 = (K.faceEdge t i).1 ∪ (K.faceEdge t j).1 :=
      (K.faceEdge_union_eq_face_of_ne t hij).symm
    _ = e.1 ∪ d.1 := by rw [hi, hj]
    _ = (K.faceEdge u k).1 ∪ (K.faceEdge u l).1 := by rw [hk, hl]
    _ = u.1 := K.faceEdge_union_eq_face_of_ne u hkl

/-- In a fixed parent, two distinct midpoint vertices determine at most one corner child. -/
theorem midpointCornerFace_eq_of_two_midpoints_mem
    (t : K.Face) {i j : ZMod 3} {e d : K.Edge} (hed : e ≠ d)
    (hei : Sum.inr e ∈ K.midpointCornerFace t i)
    (hdi : Sum.inr d ∈ K.midpointCornerFace t i)
    (hej : Sum.inr e ∈ K.midpointCornerFace t j)
    (hdj : Sum.inr d ∈ K.midpointCornerFace t j) :
    K.midpointCornerFace t i = K.midpointCornerFace t j := by
  have hei' :
      e = K.faceEdge t i ∨ e = K.faceEdge t (i + 2) := by
    simpa [midpointCornerFace] using hei
  have hdi' :
      d = K.faceEdge t i ∨ d = K.faceEdge t (i + 2) := by
    simpa [midpointCornerFace] using hdi
  have hej' :
      e = K.faceEdge t j ∨ e = K.faceEdge t (j + 2) := by
    simpa [midpointCornerFace] using hej
  have hdj' :
      d = K.faceEdge t j ∨ d = K.faceEdge t (j + 2) := by
    simpa [midpointCornerFace] using hdj
  have hi :
      (e = K.faceEdge t i ∧ d = K.faceEdge t (i + 2)) ∨
        (e = K.faceEdge t (i + 2) ∧ d = K.faceEdge t i) := by
    rcases hei' with hei' | hei' <;> rcases hdi' with hdi' | hdi'
    · exact (hed (hei'.trans hdi'.symm)).elim
    · exact Or.inl ⟨hei', hdi'⟩
    · exact Or.inr ⟨hei', hdi'⟩
    · exact (hed (hei'.trans hdi'.symm)).elim
  have hj :
      (e = K.faceEdge t j ∧ d = K.faceEdge t (j + 2)) ∨
        (e = K.faceEdge t (j + 2) ∧ d = K.faceEdge t j) := by
    rcases hej' with hej' | hej' <;> rcases hdj' with hdj' | hdj'
    · exact (hed (hej'.trans hdj'.symm)).elim
    · exact Or.inl ⟨hej', hdj'⟩
    · exact Or.inr ⟨hej', hdj'⟩
    · exact (hed (hej'.trans hdj'.symm)).elim
  have hswap :
      ∀ a b : ZMod 3, a = b + 2 → a + 2 = b → False := by decide
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hij : i = j :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    rw [hij]
  · have h₁ : i = j + 2 :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    have h₂ : i + 2 = j :=
      K.faceEdge_injective t (hi.2.symm.trans hj.2)
    exact (hswap i j h₁ h₂).elim
  · have h₁ : j = i + 2 :=
      K.faceEdge_injective t (hj.1.symm.trans hi.1)
    have h₂ : j + 2 = i :=
      K.faceEdge_injective t (hj.2.symm.trans hi.2)
    exact (hswap j i h₁ h₂).elim
  · have hij : i + 2 = j + 2 :=
      K.faceEdge_injective t (hi.1.symm.trans hj.1)
    have : i = j := add_right_cancel hij
    rw [this]

/-- Within one old parent, the corner children incident to two distinct midpoint vertices form
a set of cardinality at most one. -/
theorem midpointCornerFaces_pair_card_le_one
    (t : K.Face) (e d : K.Edge) (hed : e ≠ d) :
    ((Finset.univ.image (K.midpointCornerFace t)).filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  obtain ⟨haCorner, haEdge⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbCorner, hbEdge⟩ := Finset.mem_filter.mp hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp haCorner
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbCorner
  apply K.midpointCornerFace_eq_of_two_midpoints_mem t hed
  · exact haEdge (by simp)
  · exact haEdge (by simp)
  · exact hbEdge (by simp)
  · exact hbEdge (by simp)

/-- Inside one old parent, a refined edge joining two old-edge midpoints belongs to at most two
midpoint children (one corner and the central child). -/
theorem midpointFacesOver_midpoint_edge_card_le_two
    (t : K.Face) (e d : K.Edge) (hed : e ≠ d) :
    ((K.midpointFacesOver t).filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  rw [midpointFacesOver, Finset.filter_union]
  refine (Finset.card_union_le _ _).trans ?_
  have hcorner := K.midpointCornerFaces_pair_card_le_one t e d hed
  have hcentral :
      (({K.midpointCentralFace t} : Finset (Finset K.MidpointVertex)).filter fun s ↦
        ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 1 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- Globally, a mixed old-vertex/midpoint edge inherits the valence bound of its old edge. -/
theorem midpoint_mixed_edge_valence
    (hK : K.HasSurfaceEdgeValence) (v : K.Vertex) (e : K.Edge) :
    (K.midpointComplex.faces.filter fun s ↦
      ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  let I := K.midpointComplex.faces.filter fun s ↦
    ({Sum.inl v, Sum.inr e} : Finset K.MidpointVertex) ⊆ s
  let P := K.faces.filter fun t ↦ e.1 ⊆ t
  let parentMap : I → P := fun s ↦ by
    let sf : K.midpointComplex.Face :=
      ⟨s.1, (Finset.mem_filter.mp s.2).1⟩
    refine ⟨K.midpointParentFace sf, Finset.mem_filter.mpr ⟨
      (K.midpointParentFace sf).2, ?_⟩⟩
    exact K.edge_subset_parent_of_midpoint_mem
      (K.midpointParentFace sf) (K.midpointFace_mem_parent sf) e
      ((Finset.mem_filter.mp s.2).2 (by simp))
  have hinj : Function.Injective parentMap := by
    intro a b hab
    have hparent :
        K.midpointParentFace
            (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face) =
          K.midpointParentFace
            (⟨b.1, (Finset.mem_filter.mp b.2).1⟩ : K.midpointComplex.Face) :=
      by
        have hparent := congrArg Subtype.val hab
        apply Subtype.ext
        simpa only [parentMap] using hparent
    apply Subtype.ext
    apply Finset.card_le_one_iff.mp
      (K.midpointFacesOver_mixed_edge_card_le_one
        (K.midpointParentFace
          (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face)) v e)
    · exact Finset.mem_filter.mpr ⟨
        K.midpointFace_mem_parent
          (⟨a.1, (Finset.mem_filter.mp a.2).1⟩ : K.midpointComplex.Face),
        (Finset.mem_filter.mp a.2).2⟩
    · exact Finset.mem_filter.mpr ⟨by
        rw [hparent]
        exact K.midpointFace_mem_parent
          (⟨b.1, (Finset.mem_filter.mp b.2).1⟩ : K.midpointComplex.Face),
        (Finset.mem_filter.mp b.2).2⟩
  change I.card ≤ 2
  exact (Finset.card_le_card_of_injective hinj).trans (hK e.1 e.2)

/-- Equality-normalized form of `midpoint_mixed_edge_valence`, convenient when the two
endpoints of the unordered edge are presented in the opposite order. -/
theorem midpoint_mixed_edge_valence_of_eq
    (hK : K.HasSurfaceEdgeValence) (v : K.Vertex) (e : K.Edge)
    (q : Finset K.MidpointVertex)
    (hq : q = {Sum.inl v, Sum.inr e}) :
    (K.midpointComplex.faces.filter fun s ↦ q ⊆ s).card ≤ 2 := by
  subst q
  exact K.midpoint_mixed_edge_valence hK v e

/-- Globally, an edge joining two distinct old-edge midpoints is contained in at most two
midpoint children.  The two old edges determine a single parent triangle. -/
theorem midpoint_midpoint_edge_valence
    (e d : K.Edge) (hed : e ≠ d) :
    (K.midpointComplex.faces.filter fun s ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s).card ≤ 2 := by
  let I := K.midpointComplex.faces.filter fun s ↦
    ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ s
  by_cases hI : I.Nonempty
  · obtain ⟨s, hs⟩ := hI
    let sf : K.midpointComplex.Face :=
      ⟨s, (Finset.mem_filter.mp hs).1⟩
    let t := K.midpointParentFace sf
    let J := (K.midpointFacesOver t).filter fun q ↦
      ({Sum.inr e, Sum.inr d} : Finset K.MidpointVertex) ⊆ q
    have heT : e.1 ⊆ t.1 :=
      K.edge_subset_parent_of_midpoint_mem t (K.midpointFace_mem_parent sf) e
        ((Finset.mem_filter.mp hs).2 (by simp))
    have hdT : d.1 ⊆ t.1 :=
      K.edge_subset_parent_of_midpoint_mem t (K.midpointFace_mem_parent sf) d
        ((Finset.mem_filter.mp hs).2 (by simp))
    have hsub : I ⊆ J := by
      intro q hq
      let qf : K.midpointComplex.Face :=
        ⟨q, (Finset.mem_filter.mp hq).1⟩
      let u := K.midpointParentFace qf
      have heU : e.1 ⊆ u.1 :=
        K.edge_subset_parent_of_midpoint_mem u (K.midpointFace_mem_parent qf) e
          ((Finset.mem_filter.mp hq).2 (by simp))
      have hdU : d.1 ⊆ u.1 :=
        K.edge_subset_parent_of_midpoint_mem u (K.midpointFace_mem_parent qf) d
          ((Finset.mem_filter.mp hq).2 (by simp))
      have htu : t = u :=
        K.face_eq_of_two_edges_subset hed heT hdT heU hdU
      exact Finset.mem_filter.mpr ⟨by
        rw [htu]
        exact K.midpointFace_mem_parent qf,
        (Finset.mem_filter.mp hq).2⟩
    change I.card ≤ 2
    exact (Finset.card_le_card hsub).trans
      (K.midpointFacesOver_midpoint_edge_card_le_two t e d hed)
  · have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    change I.card ≤ 2
    simp [hEmpty]

/-- Midpoint subdivision preserves the surface edge-valence bound. -/
theorem hasSurfaceEdgeValence_midpointComplex
    (hK : K.HasSurfaceEdgeValence) :
    K.midpointComplex.HasSurfaceEdgeValence := by
  intro q hq
  obtain ⟨a, b, hab, rfl⟩ :=
    Finset.card_eq_two.mp (K.midpointComplex.card_of_mem_edges hq)
  rcases a with v | e <;> rcases b with w | d
  · obtain ⟨s, hs, hsub⟩ :=
      K.midpointComplex.exists_face_of_mem_edges hq
    let sf : K.midpointComplex.Face := ⟨s, hs⟩
    have hvw : v = w :=
      K.oldVertex_eq_of_mem_midpointFace
        (K.midpointParentFace sf) (K.midpointFace_mem_parent sf)
        (hsub (Finset.mem_insert_self _ _)) (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    exact (hab (congrArg Sum.inl hvw)).elim
  · exact K.midpoint_mixed_edge_valence hK v d
  · exact K.midpoint_mixed_edge_valence_of_eq hK w e _
      (Finset.pair_comm _ _)
  · exact K.midpoint_midpoint_edge_valence e d fun hed ↦
      hab (congrArg Sum.inr hed)

theorem midpointRecoverOld_corner
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (v : K.Vertex) :
    K.midpointRecoverOld (K.midpointEvalAffine x) v = x (Sum.inl v) := by
  have hsum : x (Sum.inl (K.faceVertex t i)) +
      x (Sum.inr (K.faceEdge t i)) + x (Sum.inr (K.faceEdge t (i + 2))) = 1 := by
    rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
    simpa [midpointCornerFace, K.faceEdge_ne_add_two t i, add_assoc] using hx1
  by_cases hv : v ∈ t.1
  · obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_self t i hx]
      have heq : 2 * (x (Sum.inl (K.faceVertex t i)) +
          (x (Sum.inr (K.faceEdge t i)) +
            x (Sum.inr (K.faceEdge t (i + 2)))) / 2) - 1 =
          x (Sum.inl (K.faceVertex t i)) := by linarith
      rw [heq, max_eq_left (hx0 _)]
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_next t i hx]
      have hle : x (Sum.inr (K.faceEdge t i)) ≤ 1 := by
        linarith [hx0 (Sum.inl (K.faceVertex t i)),
          hx0 (Sum.inr (K.faceEdge t (i + 2)))]
      rw [max_eq_right (by linarith)]
      exact (hx (Sum.inl (K.faceVertex t (i + 1))) (by
        simp [midpointCornerFace, (K.faceVertex_ne_next t i).symm])).symm
    · subst j
      unfold midpointRecoverOld
      rw [K.midpointEval_corner_prev t i hx]
      have hle : x (Sum.inr (K.faceEdge t (i + 2))) ≤ 1 := by
        linarith [hx0 (Sum.inl (K.faceVertex t i)),
          hx0 (Sum.inr (K.faceEdge t i))]
      rw [max_eq_right (by linarith)]
      exact (hx (Sum.inl (K.faceVertex t (i + 2))) (by
        simp [midpointCornerFace, (K.faceVertex_ne_add_two t i).symm])).symm
  · have hface : K.midpointCornerFace t i ∈ K.midpointFacesOver t := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hp : K.midpointEvalAffine x v = 0 :=
      K.midpointEvalAffine_support t hface hx hv
    unfold midpointRecoverOld
    rw [hp]
    simp only [mul_zero, zero_sub, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
    have hvi : v ≠ K.faceVertex t i :=
      fun h => hv (by rw [h]; exact K.faceVertex_mem t i)
    exact (hx (Sum.inl v) (by simp [midpointCornerFace, hvi])).symm

theorem midpointRecoverOld_central
    (t : K.Face) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (v : K.Vertex) :
    K.midpointRecoverOld (K.midpointEvalAffine x) v = x (Sum.inl v) := by
  by_cases hv : v ∈ t.1
  · obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    have hsum : x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 1))) +
        x (Sum.inr (K.faceEdge t (i + 2))) = 1 := by
      rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
      have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
      have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
      have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
        simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
      simpa [K.midpointCentralFace_eq t i, he01, he02, he12, add_assoc] using hx1
    unfold midpointRecoverOld
    rw [K.midpointEval_central_coord t i hx]
    have hnonpos : 2 * ((x (Sum.inr (K.faceEdge t i)) +
        x (Sum.inr (K.faceEdge t (i + 2)))) / 2) - 1 ≤ 0 := by
      linarith [hx0 (Sum.inr (K.faceEdge t (i + 1)))]
    rw [max_eq_right hnonpos]
    exact (hx (Sum.inl (K.faceVertex t i)) (by simp [midpointCentralFace])).symm
  · have hface : K.midpointCentralFace t ∈ K.midpointFacesOver t :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hp : K.midpointEvalAffine x v = 0 :=
      K.midpointEvalAffine_support t hface hx hv
    unfold midpointRecoverOld
    rw [hp]
    simp only [mul_zero, zero_sub,
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
    exact (hx (Sum.inl v) (by simp [midpointCentralFace])).symm

theorem midpointRecoverEdge_corner
    (t : K.Face) (i : ZMod 3) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCornerFace t i, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (e : K.Edge) :
    K.midpointRecoverEdge (K.midpointEvalAffine x) e = x (Sum.inr e) := by
  let A := x (Sum.inl (K.faceVertex t i))
  let B := x (Sum.inr (K.faceEdge t i))
  let C := x (Sum.inr (K.faceEdge t (i + 2)))
  have hsum : A + B + C = 1 := by
    rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
    simpa [A, B, C, midpointCornerFace, K.faceEdge_ne_add_two t i, add_assoc] using hx1
  have hA0 : 0 ≤ A := hx0 _
  have hB0 : 0 ≤ B := hx0 _
  have hC0 : 0 ≤ C := hx0 _
  by_cases het : e.1 ⊆ t.1
  · obtain ⟨j, rfl⟩ := K.exists_faceEdge_eq_of_subset t e het
    rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
      h | h | h
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_self t i hx,
        K.midpointEval_corner_next t i hx]
      have hpSelf : 2 * (A + (B + C) / 2) = 1 + A := by linarith
      have hthird : 2 * (A + (B + C) / 2 + B / 2) - 1 = A + B := by linarith
      change max 0 (min (2 * (A + (B + C) / 2))
        (min (2 * (B / 2))
          (2 * (A + (B + C) / 2 + B / 2) - 1))) = B
      rw [hpSelf, show 2 * (B / 2) = B by ring, hthird]
      have hinner : min B (A + B) = B := min_eq_left (by linarith)
      rw [hinner, min_eq_right (by linarith), max_eq_right hB0]
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_next t i hx]
      simp only [zmod3_add_one_add_one]
      rw [
        K.midpointEval_corner_prev t i hx]
      have hthird : 2 * (B / 2 + C / 2) - 1 = -A := by linarith
      rw [hthird]
      have hnonpos : min (2 * (B / 2)) (min (2 * (C / 2)) (-A)) ≤ 0 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (neg_nonpos.mpr hA0))
      rw [max_eq_left hnonpos]
      exact (hx (Sum.inr (K.faceEdge t (i + 1))) (by
        have h10 : K.faceEdge t (i + 1) ≠ K.faceEdge t i :=
          (K.faceEdge_ne_next t i).symm
        have h12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
          simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
        simp [midpointCornerFace, h10, h12])).symm
    · subst j
      rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_corner_prev t i hx]
      simp only [zmod3_add_two_add_one]
      rw [
        K.midpointEval_corner_self t i hx]
      have hpSelf : 2 * (A + (B + C) / 2) = 1 + A := by linarith
      have hthird : 2 * (C / 2 + (A + (B + C) / 2)) - 1 = A + C := by linarith
      change max 0 (min (2 * (C / 2))
        (min (2 * (A + (B + C) / 2))
          (2 * (C / 2 + (A + (B + C) / 2)) - 1))) = C
      rw [show 2 * (C / 2) = C by ring, hpSelf, hthird]
      have hinner : min (1 + A) (A + C) = A + C := min_eq_right (by linarith)
      rw [hinner, min_eq_left (by linarith), max_eq_right hC0]
  · have hnotmem : Sum.inr e ∉ K.midpointCornerFace t i := by
      simp only [midpointCornerFace, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨Sum.inr_ne_inl, ?_, ?_⟩
      · intro heq
        apply het
        rw [Sum.inr.inj heq]
        exact K.faceEdge_subset_face t i
      · intro heq
        apply het
        rw [Sum.inr.inj heq]
        exact K.faceEdge_subset_face t (i + 2)
    have hface : K.midpointCornerFace t i ∈ K.midpointFacesOver t := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hend : K.edgeFirst e ∉ t.1 ∨ K.edgeSecond e ∉ t.1 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply het
      rw [K.edge_eq_pair]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2
    rw [midpointRecoverEdge]
    rcases hend with hfirst | hsecond
    · rw [K.midpointEvalAffine_support t hface hx hfirst, mul_zero]
      have hle : min 0
          (min (2 * K.midpointEvalAffine x (K.edgeSecond e))
            (2 * (0 + K.midpointEvalAffine x (K.edgeSecond e)) - 1)) ≤ 0 :=
        min_le_left _ _
      rw [max_eq_left hle]
      exact (hx (Sum.inr e) hnotmem).symm
    · rw [K.midpointEvalAffine_support t hface hx hsecond, mul_zero]
      have hle : min 0
          (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1) ≤ 0 := min_le_left _ _
      have hle' : min (2 * K.midpointEvalAffine x (K.edgeFirst e))
          (min 0 (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1)) ≤ 0 :=
        (min_le_right _ _).trans hle
      rw [max_eq_left hle']
      exact (hx (Sum.inr e) hnotmem).symm

theorem midpointRecoverEdge_central
    (t : K.Face) {x : K.MidpointVertex → ℝ}
    (hx : ∀ w ∉ K.midpointCentralFace t, x w = 0)
    (hx0 : ∀ w, 0 ≤ x w) (hx1 : ∑ w, x w = 1) (e : K.Edge) :
    K.midpointRecoverEdge (K.midpointEvalAffine x) e = x (Sum.inr e) := by
  by_cases het : e.1 ⊆ t.1
  · obtain ⟨i, rfl⟩ := K.exists_faceEdge_eq_of_subset t e het
    let A := x (Sum.inr (K.faceEdge t i))
    let B := x (Sum.inr (K.faceEdge t (i + 1)))
    let C := x (Sum.inr (K.faceEdge t (i + 2)))
    have hsum : A + B + C = 1 := by
      rw [K.sum_eq_sum_of_midpointSupport hx] at hx1
      have he01 : K.faceEdge t i ≠ K.faceEdge t (i + 1) := K.faceEdge_ne_next t i
      have he02 : K.faceEdge t i ≠ K.faceEdge t (i + 2) := K.faceEdge_ne_add_two t i
      have he12 : K.faceEdge t (i + 1) ≠ K.faceEdge t (i + 2) := by
        simpa only [zmod3_add_one_add_one] using K.faceEdge_ne_next t (i + 1)
      simpa [A, B, C, K.midpointCentralFace_eq t i, he01, he02, he12,
        add_assoc] using hx1
    have hA0 : 0 ≤ A := hx0 _
    have hB0 : 0 ≤ B := hx0 _
    have hC0 : 0 ≤ C := hx0 _
    rw [K.midpointRecoverEdge_faceEdge, K.midpointEval_central_coord t i hx]
    have hnext := K.midpointEval_central_coord t (i + 1) hx
    simp only [zmod3_add_one_add_two] at hnext
    rw [hnext]
    change max 0 (min (2 * ((A + C) / 2))
      (min (2 * ((B + A) / 2))
        (2 * ((A + C) / 2 + (B + A) / 2) - 1))) = A
    have hfirst : 2 * ((A + C) / 2) = A + C := by ring
    have hsecond : 2 * ((B + A) / 2) = B + A := by ring
    have hthird : 2 * ((A + C) / 2 + (B + A) / 2) - 1 = A := by linarith
    rw [hfirst, hsecond, hthird]
    have hinner : min (B + A) A = A := min_eq_right (by linarith)
    rw [hinner, min_eq_right (by linarith), max_eq_right hA0]
  · have hnotmem : Sum.inr e ∉ K.midpointCentralFace t := by
      intro he
      rw [midpointCentralFace] at he
      obtain ⟨j, -, heq⟩ := Finset.mem_image.mp he
      apply het
      rw [← Sum.inr.inj heq]
      exact K.faceEdge_subset_face t j
    have hface : K.midpointCentralFace t ∈ K.midpointFacesOver t :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hend : K.edgeFirst e ∉ t.1 ∨ K.edgeSecond e ∉ t.1 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply het
      rw [K.edge_eq_pair]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2
    rw [midpointRecoverEdge]
    rcases hend with hfirst | hsecond
    · rw [K.midpointEvalAffine_support t hface hx hfirst, mul_zero]
      have hle : min 0
          (min (2 * K.midpointEvalAffine x (K.edgeSecond e))
            (2 * (0 + K.midpointEvalAffine x (K.edgeSecond e)) - 1)) ≤ 0 :=
        min_le_left _ _
      rw [max_eq_left hle]
      exact (hx (Sum.inr e) hnotmem).symm
    · rw [K.midpointEvalAffine_support t hface hx hsecond, mul_zero]
      have hle : min 0
          (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1) ≤ 0 := min_le_left _ _
      have hle' : min (2 * K.midpointEvalAffine x (K.edgeFirst e))
          (min 0 (2 * (K.midpointEvalAffine x (K.edgeFirst e) + 0) - 1)) ≤ 0 :=
        (min_le_right _ _).trans hle
      rw [max_eq_left hle']
      exact (hx (Sum.inr e) hnotmem).symm

/-- Midpoint coordinates are uniquely recovered from their old barycentric image. -/
theorem midpointRecover_midpointEvalAffine (x : K.midpointComplex.realization) :
    K.midpointRecover (K.midpointEvalAffine x.1) = x.1 := by
  obtain ⟨s, hs, hxs⟩ := x.2.2
  obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
  rw [midpointFacesOver] at hst
  replace hst := Finset.mem_union.mp hst
  funext w
  rcases hst with hcorner | hcentral
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcorner
    rcases w with v | e
    · exact K.midpointRecoverOld_corner t i hxs x.2.1.1 x.2.1.2 v
    · exact K.midpointRecoverEdge_corner t i hxs x.2.1.1 x.2.1.2 e
  · rw [Finset.mem_singleton.mp hcentral] at hxs
    rcases w with v | e
    · exact K.midpointRecoverOld_central t hxs x.2.1.1 x.2.1.2 v
    · exact K.midpointRecoverEdge_central t hxs x.2.1.1 x.2.1.2 e

theorem injective_midpointEvalAffine_on_realization :
    Function.Injective (fun x : K.midpointComplex.realization => K.midpointEvalAffine x.1) := by
  intro x y hxy
  apply Subtype.ext
  exact (K.midpointRecover_midpointEvalAffine x).symm.trans
    ((congrArg K.midpointRecover hxy).trans (K.midpointRecover_midpointEvalAffine y))

theorem face_eq_image_faceVertex (t : K.Face) :
    t.1 = Finset.univ.image (K.faceVertex t) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem t hv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact K.faceVertex_mem t i

theorem sum_faceVertex_coords (t : K.Face) (p : K.Vertex → ℝ)
    (hsupp : ∀ v ∉ t.1, p v = 0) (hsum : ∑ v, p v = 1) (i : ZMod 3) :
    p (K.faceVertex t i) + p (K.faceVertex t (i + 1)) +
      p (K.faceVertex t (i + 2)) = 1 := by
  have hsum' : ∑ v ∈ t.1, p v = 1 := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ t.1) (fun v _ hv => hsupp v hv)
  rw [K.face_eq_image_faceVertex t, Finset.sum_image] at hsum'
  · have hu : (Finset.univ : Finset (ZMod 3)) = {i, i + 1, i + 2} := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j
    rw [hu] at hsum'
    have hi01 : i ≠ i + 1 := (by decide : ∀ i : ZMod 3, i ≠ i + 1) i
    have hi02 : i ≠ i + 2 := (by decide : ∀ i : ZMod 3, i ≠ i + 2) i
    have hi12 : i + 1 ≠ i + 2 := (by decide : ∀ i : ZMod 3, i + 1 ≠ i + 2) i
    simpa [hi01, hi02, hi12, add_assoc] using hsum'
  · exact fun a _ b _ hab => K.faceVertex_injective t hab

/-- Explicit inverse coordinates in a corner triangle. -/
noncomputable def midpointCornerWeights (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) : K.MidpointVertex → ℝ := fun w =>
  if w = Sum.inl (K.faceVertex t i) then 2 * p (K.faceVertex t i) - 1
  else if w = Sum.inr (K.faceEdge t i) then 2 * p (K.faceVertex t (i + 1))
  else if w = Sum.inr (K.faceEdge t (i + 2)) then 2 * p (K.faceVertex t (i + 2))
  else 0

@[simp] theorem midpointCornerWeights_old (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inl (K.faceVertex t i)) =
      2 * p (K.faceVertex t i) - 1 := by
  simp [midpointCornerWeights]

@[simp] theorem midpointCornerWeights_nextEdge (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inr (K.faceEdge t i)) =
      2 * p (K.faceVertex t (i + 1)) := by
  simp [midpointCornerWeights]

@[simp] theorem midpointCornerWeights_prevEdge (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    K.midpointCornerWeights t i p (Sum.inr (K.faceEdge t (i + 2))) =
      2 * p (K.faceVertex t (i + 2)) := by
  simp [midpointCornerWeights,
    (K.faceEdge_ne_add_two t i).symm]

theorem midpointCornerWeights_support (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) :
    ∀ w ∉ K.midpointCornerFace t i, K.midpointCornerWeights t i p w = 0 := by
  intro w hw
  simp only [midpointCornerWeights]
  split_ifs with h₁ h₂ h₃
  · exact (hw (by simp [midpointCornerFace, h₁])).elim
  · exact (hw (by simp [midpointCornerFace, h₂])).elim
  · exact (hw (by simp [midpointCornerFace, h₃])).elim
  · rfl

theorem midpointCornerWeights_nonneg (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ) (hp0 : ∀ v, 0 ≤ p v)
    (hi : (2 : ℝ)⁻¹ ≤ p (K.faceVertex t i)) :
    ∀ w, 0 ≤ K.midpointCornerWeights t i p w := by
  intro w
  simp only [midpointCornerWeights]
  split_ifs <;> linarith [hp0 (K.faceVertex t (i + 1)),
    hp0 (K.faceVertex t (i + 2))]

theorem sum_midpointCornerWeights (t : K.Face) (i : ZMod 3)
    (p : K.Vertex → ℝ)
    (hsum : p (K.faceVertex t i) + p (K.faceVertex t (i + 1)) +
      p (K.faceVertex t (i + 2)) = 1) :
    ∑ w, K.midpointCornerWeights t i p w = 1 := by
  rw [K.sum_eq_sum_of_midpointSupport (K.midpointCornerWeights_support t i p)]
  simp [midpointCornerFace, K.faceEdge_ne_add_two t i]
  linarith

/-- Explicit inverse coordinates in the central triangle. -/
noncomputable def midpointCentralWeights (t : K.Face) (p : K.Vertex → ℝ) :
    K.MidpointVertex → ℝ := fun w =>
  ∑ i : ZMod 3, if w = Sum.inr (K.faceEdge t i) then
    1 - 2 * p (K.faceVertex t (i + 2)) else 0

@[simp] theorem midpointCentralWeights_edge (t : K.Face) (p : K.Vertex → ℝ)
    (i : ZMod 3) :
    K.midpointCentralWeights t p (Sum.inr (K.faceEdge t i)) =
      1 - 2 * p (K.faceVertex t (i + 2)) := by
  rw [midpointCentralWeights]
  calc
    (∑ j : ZMod 3, if Sum.inr (K.faceEdge t i) = Sum.inr (K.faceEdge t j) then
        1 - 2 * p (K.faceVertex t (j + 2)) else 0) =
        (if Sum.inr (K.faceEdge t i) = Sum.inr (K.faceEdge t i) then
          1 - 2 * p (K.faceVertex t (i + 2)) else 0) := by
      apply Fintype.sum_eq_single i
      intro j hji
      rw [if_neg]
      intro h
      exact hji (K.faceEdge_injective t (Sum.inr.inj h).symm)
    _ = 1 - 2 * p (K.faceVertex t (i + 2)) := by simp

theorem midpointCentralWeights_support (t : K.Face) (p : K.Vertex → ℝ) :
    ∀ w ∉ K.midpointCentralFace t, K.midpointCentralWeights t p w = 0 := by
  intro w hw
  rw [midpointCentralWeights]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro h
  apply hw
  rw [midpointCentralFace]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩

theorem midpointCentralWeights_nonneg (t : K.Face) (p : K.Vertex → ℝ)
    (hle : ∀ i : ZMod 3, p (K.faceVertex t i) ≤ (2 : ℝ)⁻¹) :
    ∀ w, 0 ≤ K.midpointCentralWeights t p w := by
  intro w
  rw [midpointCentralWeights]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · linarith [hle (i + 2)]
  · rfl

theorem sum_midpointCentralWeights (t : K.Face) (p : K.Vertex → ℝ)
    (hsum : p (K.faceVertex t 0) + p (K.faceVertex t 1) +
      p (K.faceVertex t 2) = 1) :
    ∑ w, K.midpointCentralWeights t p w = 1 := by
  rw [K.sum_eq_sum_of_midpointSupport (K.midpointCentralWeights_support t p),
    K.midpointCentralFace_eq t 0]
  have he01 : K.faceEdge t 0 ≠ K.faceEdge t 1 := K.faceEdge_ne_next t 0
  have he02 : K.faceEdge t 0 ≠ K.faceEdge t 2 := K.faceEdge_ne_add_two t 0
  have he12 : K.faceEdge t 1 ≠ K.faceEdge t 2 := by
    have h12 : (1 : ZMod 3) + 1 = 2 := by decide
    simpa only [h12] using K.faceEdge_ne_next t 1
  rw [Finset.sum_insert (by simp [he01, he02]),
    Finset.sum_insert (by simp [he12]), Finset.sum_singleton,
    K.midpointCentralWeights_edge, K.midpointCentralWeights_edge,
    K.midpointCentralWeights_edge]
  simp only [zero_add]
  have h12 : (1 : ZMod 3) + 2 = 0 := by decide
  have h22 : (2 : ZMod 3) + 2 = 1 := by decide
  rw [h12, h22]
  linarith

/-- The four named midpoint children of an old face cover that old face. -/
theorem exists_midpoint_preimage_in_face (T : K.Face) (p : K.realization)
    (hpt : p ∈ K.faceCarrier T.1) :
    ∃ (x : K.midpointComplex.realization) (s : Finset K.MidpointVertex),
      s ∈ K.midpointFacesOver T ∧ x ∈ K.midpointComplex.faceCarrier s ∧
        K.midpointEvalAffine x.1 = p.1 := by
  have hsum (i : ZMod 3) : p.1 (K.faceVertex T i) +
      p.1 (K.faceVertex T (i + 1)) + p.1 (K.faceVertex T (i + 2)) = 1 :=
    K.sum_faceVertex_coords T p.1 hpt p.2.1.2 i
  by_cases hhigh : ∃ i : ZMod 3, (2 : ℝ)⁻¹ ≤ p.1 (K.faceVertex T i)
  · obtain ⟨i, hi⟩ := hhigh
    let y := K.midpointCornerWeights T i p.1
    have hy0 : ∀ w, 0 ≤ y w := K.midpointCornerWeights_nonneg T i p.1 p.2.1.1 hi
    have hy1 : ∑ w, y w = 1 := K.sum_midpointCornerWeights T i p.1 (hsum i)
    have hySupp : ∀ w ∉ K.midpointCornerFace T i, y w = 0 :=
      K.midpointCornerWeights_support T i p.1
    have hfaceOver : K.midpointCornerFace T i ∈ K.midpointFacesOver T := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hface : K.midpointCornerFace T i ∈ K.midpointComplex.faces := by
      change K.midpointCornerFace T i ∈ K.midpointFaces
      rw [midpointFaces]
      exact Finset.mem_biUnion.mpr ⟨T, by simp, hfaceOver⟩
    let z : K.midpointComplex.realization :=
      ⟨y, ⟨hy0, hy1⟩, K.midpointCornerFace T i, hface, hySupp⟩
    refine ⟨z, K.midpointCornerFace T i, hfaceOver, hySupp, ?_⟩
    change K.midpointEvalAffine y = p.1
    funext v
    by_cases hv : v ∈ T.1
    · obtain ⟨j, rfl⟩ := K.exists_faceVertex_eq_of_mem T hv
      rcases (by decide : ∀ i j : ZMod 3, j = i ∨ j = i + 1 ∨ j = i + 2) i j with
        h | h | h
      · subst j
        rw [K.midpointEval_corner_self T i hySupp]
        simp only [y, K.midpointCornerWeights_old, K.midpointCornerWeights_nextEdge,
          K.midpointCornerWeights_prevEdge]
        linarith [hsum i]
      · subst j
        rw [K.midpointEval_corner_next T i hySupp]
        simp [y]
      · subst j
        rw [K.midpointEval_corner_prev T i hySupp]
        simp [y]
    · rw [K.midpointEvalAffine_support T hfaceOver hySupp hv, hpt v hv]
  · have hle : ∀ i : ZMod 3, p.1 (K.faceVertex T i) ≤ (2 : ℝ)⁻¹ := by
      intro i
      exact le_of_not_ge (fun hi => hhigh ⟨i, hi⟩)
    let y := K.midpointCentralWeights T p.1
    have hy0 : ∀ w, 0 ≤ y w := K.midpointCentralWeights_nonneg T p.1 hle
    have hy1 : ∑ w, y w = 1 := K.sum_midpointCentralWeights T p.1 (hsum 0)
    have hySupp : ∀ w ∉ K.midpointCentralFace T, y w = 0 :=
      K.midpointCentralWeights_support T p.1
    have hfaceOver : K.midpointCentralFace T ∈ K.midpointFacesOver T :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hface : K.midpointCentralFace T ∈ K.midpointComplex.faces := by
      change K.midpointCentralFace T ∈ K.midpointFaces
      rw [midpointFaces]
      exact Finset.mem_biUnion.mpr ⟨T, by simp, hfaceOver⟩
    let z : K.midpointComplex.realization :=
      ⟨y, ⟨hy0, hy1⟩, K.midpointCentralFace T, hface, hySupp⟩
    refine ⟨z, K.midpointCentralFace T, hfaceOver, hySupp, ?_⟩
    change K.midpointEvalAffine y = p.1
    funext v
    by_cases hv : v ∈ T.1
    · obtain ⟨i, rfl⟩ := K.exists_faceVertex_eq_of_mem T hv
      rw [K.midpointEval_central_coord T i hySupp]
      simp only [y, K.midpointCentralWeights_edge]
      have hcycle : i + 2 + 2 = i + 1 := zmod3_add_two_add_two i
      rw [hcycle]
      linarith [hsum i]
    · rw [K.midpointEvalAffine_support T hfaceOver hySupp hv, hpt v hv]

/-- The four midpoint triangles cover every old face, hence the whole realization. -/
theorem surjective_midpointEvalAffine_on_realization :
    ∀ p : K.realization, ∃ x : K.midpointComplex.realization,
      K.midpointEvalAffine x.1 = p.1 := by
  intro p
  obtain ⟨t, ht, hpt⟩ := p.2.2
  obtain ⟨x, s, -, -, hx⟩ :=
    K.exists_midpoint_preimage_in_face ⟨t, ht⟩ p hpt
  exact ⟨x, hx⟩

theorem midpointEvalAffine_nonneg (x : K.midpointComplex.realization) (v : K.Vertex) :
    0 ≤ K.midpointEvalAffine x.1 v := by
  classical
  erw [K.midpointEvalAffine_apply]; rw [Finset.sum_apply]
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (x.2.1.1 w) (K.midpointPosition_nonneg w v)

theorem sum_midpointEvalAffine (x : K.midpointComplex.realization) :
    ∑ v, K.midpointEvalAffine x.1 v = 1 := by
  classical
  erw [K.midpointEvalAffine_apply]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ v, ∑ w, x.1 w * K.midpointPosition w v =
        ∑ w, ∑ v, x.1 w * K.midpointPosition w v := Finset.sum_comm
    _ = ∑ w, x.1 w * ∑ v, K.midpointPosition w v := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
    _ = ∑ w, x.1 w := Finset.sum_congr rfl fun w _ => by rw [K.sum_midpointPosition w, mul_one]
    _ = 1 := x.2.1.2

/-- Canonical affine map from the midpoint realization into the old realization. -/
noncomputable def midpointEval (x : K.midpointComplex.realization) : K.realization := by
  refine ⟨K.midpointEvalAffine x.1,
    ⟨K.midpointEvalAffine_nonneg x, K.sum_midpointEvalAffine x⟩, ?_⟩
  obtain ⟨s, hs, hxs⟩ := x.2.2
  obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
  exact ⟨t.1, t.2, fun v hv => K.midpointEvalAffine_support t hst hxs hv⟩

@[simp] theorem midpointEval_val (x : K.midpointComplex.realization) :
    (K.midpointEval x).1 = K.midpointEvalAffine x.1 := rfl

theorem continuous_midpointEval : Continuous K.midpointEval := by
  apply Continuous.subtype_mk
  exact K.midpointEvalAffine.continuous_of_finiteDimensional.comp continuous_subtype_val

theorem midpointEval_mem_parentFace
    (t : K.Face) {s : Finset K.MidpointVertex} (hs : s ∈ K.midpointFacesOver t)
    (x : K.midpointComplex.realization) (hx : x ∈ K.midpointComplex.faceCarrier s) :
    K.midpointEval x ∈ K.faceCarrier t.1 := by
  intro v hv
  exact K.midpointEvalAffine_support t hs hx hv

theorem midpointEval_affineOnFace
    {s : Finset K.MidpointVertex} (_ : s ∈ K.midpointFaces) :
    ∃ a : (K.MidpointVertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : K.midpointComplex.realization,
        x ∈ K.midpointComplex.faceCarrier s → (K.midpointEval x).1 = a x.1 :=
  ⟨K.midpointEvalAffine, fun _ _ => rfl⟩

theorem injective_midpointEval : Function.Injective K.midpointEval := by
  intro x y hxy
  apply K.injective_midpointEvalAffine_on_realization
  exact congrArg Subtype.val hxy

theorem surjective_midpointEval : Function.Surjective K.midpointEval := by
  intro p
  obtain ⟨x, hx⟩ := K.surjective_midpointEvalAffine_on_realization p
  exact ⟨x, Subtype.ext hx⟩

/-- The canonical midpoint realization map is a homeomorphism. -/
noncomputable def midpointHomeomorph :
    K.midpointComplex.realization ≃ₜ K.realization :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective K.midpointEval
      ⟨K.injective_midpointEval, K.surjective_midpointEval⟩)
    K.continuous_midpointEval

@[simp] theorem midpointHomeomorph_apply (x : K.midpointComplex.realization) :
    K.midpointHomeomorph x = K.midpointEval x := rfl

/-- The intrinsic 1-to-4 midpoint subdivision, with its canonical faithful realization map. -/
noncomputable def midpointSubdivision : K.Subdivision where
  refined := K.midpointComplex
  homeo := K.midpointHomeomorph
  affineOnFace := by
    intro s hs
    exact K.midpointEval_affineOnFace hs
  subordinate := by
    intro s hs
    obtain ⟨t, hst⟩ := K.exists_parentFace_of_mem_midpointFaces hs
    exact ⟨t.1, t.2, fun x hx => K.midpointEval_mem_parentFace t hst x hx⟩

@[simp] theorem midpointSubdivision_refined :
    K.midpointSubdivision.refined = K.midpointComplex := rfl

theorem midpointSubdivision_homeo_apply (x : K.midpointComplex.realization) :
    K.midpointSubdivision.homeo x = K.midpointEval x := rfl

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification04_block_03
/- END ClassificationOfSurfaces.Moise.IntrinsicMidpointSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.LocallyFiniteTriangulation | 5812bcae5af90486e204e5a2254f8d0bb2a3de7e08329ef32f9378f09f837eab -/
section schottkyclassification04_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Locally finite triangle complexes

Rado's induction in Moise Chapter 8 passes through locally finite, usually noncompact, PL
complexes.  Requiring every intermediate complex to be finite loses the frontier-vanishing
construction used in the induction step.  This file provides the corresponding ambient API while
keeping the existing finite `GeometricTriangulation` as the final output.

A face is parametrized by the standard simplex on its three global vertices.  The
`faceMap_eq_iff` field says both that parametrizations agree on common faces and that distinct
geometric points are never identified.  Thus the structure records the full face-to-face
condition, rather than only a family of carriers.  Local finiteness is imposed on the carrier
family in the ambient topology.

The main result is `LocallyFiniteTriangleComplex.toGeometricTriangulation`: on a compact
Hausdorff space, local finiteness makes the face type finite; the no-junk-vertices condition then
makes the vertex type finite, and finite closed pasting produces the required homeomorphism from
the canonical barycentric realization.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Extend barycentric coordinates on a finite face by zero to the global vertex type. -/
def extendFaceCoordinates {V : Type*} [DecidableEq V] (t : Finset V)
    (x : stdSimplex ℝ {v // v ∈ t}) : V → ℝ :=
  fun v ↦ if hv : v ∈ t then x ⟨v, hv⟩ else 0

@[simp] theorem extendFaceCoordinates_of_mem {V : Type*} [DecidableEq V]
    (t : Finset V) (x : stdSimplex ℝ {v // v ∈ t}) {v : V} (hv : v ∈ t) :
    extendFaceCoordinates t x v = x ⟨v, hv⟩ := by
  simp [extendFaceCoordinates, hv]

@[simp] theorem extendFaceCoordinates_of_notMem {V : Type*} [DecidableEq V]
    (t : Finset V) (x : stdSimplex ℝ {v // v ∈ t}) {v : V} (hv : v ∉ t) :
    extendFaceCoordinates t x v = 0 := by
  simp [extendFaceCoordinates, hv]

theorem stdSimplex_map_subtypeVal_eq_extendFaceCoordinates
    {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V)
    (x : stdSimplex ℝ {v // v ∈ t}) :
    (stdSimplex.map Subtype.val x : V → ℝ) = extendFaceCoordinates t x := by
  funext v
  by_cases hv : v ∈ t
  · let w : {w // w ∈ t} := ⟨v, hv⟩
    rw [extendFaceCoordinates_of_mem t x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter : Finset.univ.filter (fun q : {q // q ∈ t} ↦ q.1 = v) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ Subtype.ext h
      · exact fun h ↦ congrArg Subtype.val h
    rw [hfilter]
    simp [w]
  · rw [extendFaceCoordinates_of_notMem t x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty : Finset.univ.filter (fun w : {w // w ∈ t} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp

theorem extendFaceCoordinates_map_subset
    {V : Type*} [DecidableEq V] {e t : Finset V}
    (het : e ⊆ t) (x : stdSimplex ℝ {v // v ∈ e}) :
    extendFaceCoordinates t
        (stdSimplex.map (fun v : {v // v ∈ e} ↦ ⟨v.1, het v.2⟩) x) =
      extendFaceCoordinates e x := by
  funext v
  by_cases hve : v ∈ e
  · have hvt : v ∈ t := het hve
    rw [extendFaceCoordinates_of_mem t _ hvt,
      extendFaceCoordinates_of_mem e x hve]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    let w : {w // w ∈ e} := ⟨v, hve⟩
    have hfilter : Finset.univ.filter
        (fun q : {q // q ∈ e} ↦
          (⟨q.1, het q.2⟩ : {q // q ∈ t}) = ⟨v, hvt⟩) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        apply Subtype.ext
        simpa [w] using congrArg
          (fun z : {z // z ∈ t} ↦ z.1) h
      · intro h
        subst q
        rfl
    rw [hfilter]
    simp [w]
  · rw [extendFaceCoordinates_of_notMem e x hve]
    by_cases hvt : v ∈ t
    · rw [extendFaceCoordinates_of_mem t _ hvt]
      simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      have hempty : Finset.univ.filter
          (fun q : {q // q ∈ e} ↦
            (⟨q.1, het q.2⟩ : {q // q ∈ t}) = ⟨v, hvt⟩) = ∅ := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro h
        apply hve
        have hval : q.1 = v := congrArg (fun z : {z // z ∈ t} ↦ z.1) h
        simpa [hval] using q.2
      rw [hempty]
      simp
    · rw [extendFaceCoordinates_of_notMem t _ hvt]

/-! ## Relabeling a finite face along an embedding -/

/-- The vertices of a finite face are equivalent to the vertices of its image under an
embedding. -/
noncomputable def finsetMapSubtypeEquiv
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) :
    {a // a ∈ t} ≃ {b // b ∈ t.map e} := by
  classical
  let f : {a // a ∈ t} → {b // b ∈ t.map e} :=
    fun a ↦ ⟨e a.1, Finset.mem_map.mpr
      ⟨a.1, a.2, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hab)
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact hab

@[simp] theorem finsetMapSubtypeEquiv_apply_val
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) (a : {a // a ∈ t}) :
    (finsetMapSubtypeEquiv e t a).1 = e a.1 := rfl

/-- Pull simplex coordinates on a relabeled face back to the original face. -/
noncomputable def relabelFaceSimplex
    {A B : Type*}
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) :
    stdSimplex ℝ {a // a ∈ t} :=
  stdSimplex.map (finsetMapSubtypeEquiv e t).symm x

/-- Face relabeling along an embedding is onto. -/
theorem relabelFaceSimplex_surjective
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) :
    Function.Surjective (relabelFaceSimplex e t) := by
  classical
  intro x
  refine ⟨stdSimplex.map (finsetMapSubtypeEquiv e t) x, ?_⟩
  unfold relabelFaceSimplex
  rw [stdSimplex.map_comp_apply]
  have hcomp :
      (finsetMapSubtypeEquiv e t).symm ∘
          (finsetMapSubtypeEquiv e t) = id := by
    funext a
    exact (finsetMapSubtypeEquiv e t).symm_apply_apply a
  rw [hcomp, stdSimplex.map_id_apply]

/-- Pulling coordinates back along a face relabeling preserves the coordinate at every
original vertex. -/
theorem relabelFaceSimplex_extended_apply
    {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) (a : A) :
    extendFaceCoordinates t (relabelFaceSimplex e t x) a =
      extendFaceCoordinates (t.map e) x (e a) := by
  classical
  by_cases ha : a ∈ t
  · have hea : e a ∈ t.map e :=
      Finset.mem_map.mpr ⟨a, ha, rfl⟩
    rw [extendFaceCoordinates_of_mem t _ ha,
      extendFaceCoordinates_of_mem (t.map e) _ hea]
    simp only [relabelFaceSimplex, stdSimplex.map_coe,
      FunOnFinite.linearMap_apply_apply]
    let q : {b // b ∈ t.map e} := ⟨e a, hea⟩
    have hfilter :
        Finset.univ.filter
            (fun z : {b // b ∈ t.map e} ↦
              (finsetMapSubtypeEquiv e t).symm z = ⟨a, ha⟩) =
          {q} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hz
        apply (finsetMapSubtypeEquiv e t).symm.injective
        calc
          (finsetMapSubtypeEquiv e t).symm z = ⟨a, ha⟩ := hz
          _ = (finsetMapSubtypeEquiv e t).symm q := by
            rw [show q = finsetMapSubtypeEquiv e t ⟨a, ha⟩ by
              apply Subtype.ext
              rfl,
              (finsetMapSubtypeEquiv e t).symm_apply_apply]
      · intro hz
        subst z
        rw [show q = finsetMapSubtypeEquiv e t ⟨a, ha⟩ by
          apply Subtype.ext
          rfl,
          (finsetMapSubtypeEquiv e t).symm_apply_apply]
    rw [hfilter]
    simp [q]
  · have hea : e a ∉ t.map e := by
      intro hea
      obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
      exact ha (e.injective hba ▸ hb)
    rw [extendFaceCoordinates_of_notMem t _ ha,
      extendFaceCoordinates_of_notMem (t.map e) _ hea]

/-- Relabeling two faces by the same embedding preserves equality of their global
zero-extended coordinate functions. -/
theorem relabelFaceSimplex_extended_eq_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) {s t : Finset A}
    {x : stdSimplex ℝ {b // b ∈ s.map e}}
    {y : stdSimplex ℝ {b // b ∈ t.map e}} :
    extendFaceCoordinates s (relabelFaceSimplex e s x) =
        extendFaceCoordinates t (relabelFaceSimplex e t y) ↔
      extendFaceCoordinates (s.map e) x =
        extendFaceCoordinates (t.map e) y := by
  constructor
  · intro h
    funext b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [← relabelFaceSimplex_extended_apply e s x a,
        ← relabelFaceSimplex_extended_apply e t y a,
        congrFun h a]
    · have hbs : b ∉ s.map e := by
        intro hbs
        obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hbs
        exact hb ⟨a, hab⟩
      have hbt : b ∉ t.map e := by
        intro hbt
        obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hbt
        exact hb ⟨a, hab⟩
      rw [extendFaceCoordinates_of_notMem _ _ hbs,
        extendFaceCoordinates_of_notMem _ _ hbt]
  · intro h
    funext a
    rw [relabelFaceSimplex_extended_apply e s x a,
      relabelFaceSimplex_extended_apply e t y a,
      congrFun h (e a)]

/-- Relabeling does not change a weighted evaluation of the zero-extended coordinates. -/
theorem sum_extendFaceCoordinates_relabelFaceSimplex
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) (F : B → ℝ) :
    (∑ b : B, extendFaceCoordinates (t.map e) x b * F b) =
      ∑ a : A,
        extendFaceCoordinates t (relabelFaceSimplex e t x) a *
          F (e a) := by
  classical
  calc
    (∑ b : B, extendFaceCoordinates (t.map e) x b * F b) =
        ∑ b ∈ t.map e,
          extendFaceCoordinates (t.map e) x b * F b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [extendFaceCoordinates_of_notMem _ _ hb, zero_mul]
    _ = ∑ a ∈ t,
          extendFaceCoordinates (t.map e) x (e a) * F (e a) := by
      rw [Finset.sum_map]
    _ = ∑ a ∈ t,
          extendFaceCoordinates t (relabelFaceSimplex e t x) a *
            F (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [relabelFaceSimplex_extended_apply]
    _ = ∑ a : A,
          extendFaceCoordinates t (relabelFaceSimplex e t x) a *
            F (e a) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [extendFaceCoordinates_of_notMem _ _ ha, zero_mul]

/-- When the source face is the whole finite type, remove the vacuous membership subtype after
pulling coordinates back along an embedding. -/
noncomputable def univMapSubtypeEquiv
    {A B : Type*} [Fintype A]
    (e : A ↪ B) :
    {b // b ∈ (Finset.univ : Finset A).map e} ≃ A :=
  (finsetMapSubtypeEquiv e Finset.univ).symm.trans
    { toFun := fun a ↦ a.1
      invFun := fun a ↦ ⟨a, Finset.mem_univ a⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }

/-- Pull simplex coordinates on the image of a finite type back to that finite type. -/
noncomputable def relabelUnivSimplex
    {A B : Type*} [Fintype A]
    (e : A ↪ B)
    (x : stdSimplex ℝ {b // b ∈ (Finset.univ : Finset A).map e}) :
    stdSimplex ℝ A :=
  stdSimplex.map (univMapSubtypeEquiv e) x

/-- Pullback along an embedded whole finite vertex type is onto: its inverse simply pushes
coordinates forward along the inverse equivalence onto the image. -/
theorem relabelUnivSimplex_surjective
    {A B : Type*} [Fintype A]
    (e : A ↪ B) :
    Function.Surjective (relabelUnivSimplex e) := by
  classical
  intro x
  refine ⟨stdSimplex.map (univMapSubtypeEquiv e).symm x, ?_⟩
  unfold relabelUnivSimplex
  rw [stdSimplex.map_comp_apply]
  have hcomp :
      (univMapSubtypeEquiv e) ∘
          (univMapSubtypeEquiv e).symm = id := by
    funext a
    exact (univMapSubtypeEquiv e).apply_symm_apply a
  rw [hcomp, stdSimplex.map_id_apply]

/-- The whole-type relabeling preserves the coordinate of every embedded source vertex. -/
theorem relabelUnivSimplex_apply
    {A B : Type*} [Fintype A]
    [DecidableEq B]
    (e : A ↪ B)
    (x : stdSimplex ℝ {b // b ∈ (Finset.univ : Finset A).map e})
    (a : A) :
    relabelUnivSimplex e x a =
      extendFaceCoordinates ((Finset.univ : Finset A).map e) x (e a) := by
  classical
  let ea : {b // b ∈ (Finset.univ : Finset A).map e} :=
    ⟨e a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  rw [extendFaceCoordinates_of_mem _ _ ea.2]
  simp only [relabelUnivSimplex, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter
          (fun z : {b // b ∈ (Finset.univ : Finset A).map e} ↦
            univMapSubtypeEquiv e z = a) =
        {ea} := by
    have hea : univMapSubtypeEquiv e ea = a := by
      have heainv : (univMapSubtypeEquiv e).symm a = ea := by
        apply Subtype.ext
        rfl
      calc
        univMapSubtypeEquiv e ea =
            univMapSubtypeEquiv e ((univMapSubtypeEquiv e).symm a) :=
          congrArg (univMapSubtypeEquiv e) heainv.symm
        _ = a := (univMapSubtypeEquiv e).apply_symm_apply a
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hz
      apply (univMapSubtypeEquiv e).injective
      rw [hz, hea]
    · intro hz
      subst z
      exact hea
  rw [hfilter]
  simp [ea]

/-- An injective vertex map preserves the coordinate at each source vertex. -/
theorem stdSimplex_map_embedding_apply
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : stdSimplex ℝ A) (a : A) :
    stdSimplex.map e x (e a) = x a := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun q : A ↦ e q = e a) = {a} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact e.injective.eq_iff
  rw [hfilter]
  simp

/-- An injective vertex map has zero coordinate away from its image. -/
theorem stdSimplex_map_embedding_apply_of_notMem_range
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : stdSimplex ℝ A) {b : B}
    (hb : b ∉ Set.range e) :
    stdSimplex.map e x b = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun q : A ↦ e q = b) = ∅ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact fun hq ↦ hb ⟨q, hq⟩
  rw [hfilter]
  simp

/-- Relabel a finite face family along an embedding of its vertex type. -/
def relabelFaceFamily
    {A B : Type*} [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) : Finset (Finset B) := by
  exact F.image fun t ↦ t.map e

end Moise

namespace TriangleFamily

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- Regard a listed face as a face of the family obtained by injectively relabeling its
vertices. -/
def faceOfRelabel (e : A ↪ B) {faces : Finset (Finset A)} :
    Face faces → Face (Moise.relabelFaceFamily e faces) :=
  fun f => ⟨f.1.map e, Finset.mem_image.mpr ⟨f.1, f.2, rfl⟩⟩

omit [DecidableEq A] in
theorem faceOfRelabel_val (e : A ↪ B) {faces : Finset (Finset A)}
    (f : Face faces) : (faceOfRelabel e f).1 = f.1.map e :=
  rfl

omit [DecidableEq A] in
/-- Injective vertex relabeling preserves dual adjacency of listed faces. -/
theorem faceAdjacent_faceOfRelabel (e : A ↪ B) {faces : Finset (Finset A)}
    {f g : Face faces} (hfg : FaceAdjacent faces f g) :
    FaceAdjacent (Moise.relabelFaceFamily e faces)
      (faceOfRelabel e f) (faceOfRelabel e g) := by
  rcases hfg with ⟨edge, hedgeCard, hedgeLeft, hedgeRight⟩
  refine ⟨edge.map e, ?_, ?_, ?_⟩
  · simpa only [Finset.card_map] using hedgeCard
  · exact Finset.map_subset_map.mpr hedgeLeft
  · exact Finset.map_subset_map.mpr hedgeRight

omit [DecidableEq A] in
/-- Injective vertex relabeling carries a finite dual path to the relabeled family. -/
theorem reflTransGen_faceAdjacent_faceOfRelabel (e : A ↪ B)
    {faces : Finset (Finset A)} {f g : Face faces}
    (hfg : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent (Moise.relabelFaceFamily e faces))
      (faceOfRelabel e f) (faceOfRelabel e g) := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hab hbc ih =>
      exact ih.tail (faceAdjacent_faceOfRelabel e hbc)

omit [DecidableEq A] in
/-- Dual connectivity is preserved by an injective relabeling of the vertex type. -/
theorem isDualConnected_relabel (e : A ↪ B) {faces : Finset (Finset A)}
    (hfaces : IsDualConnected faces) :
    IsDualConnected (Moise.relabelFaceFamily e faces) := by
  intro f g
  obtain ⟨f', hf', hfeq⟩ := Finset.mem_image.mp f.2
  obtain ⟨g', hg', hgeq⟩ := Finset.mem_image.mp g.2
  let fs : Face faces := ⟨f', hf'⟩
  let gs : Face faces := ⟨g', hg'⟩
  have hpath :=
    reflTransGen_faceAdjacent_faceOfRelabel e (hfaces fs gs)
  have hfval : (faceOfRelabel e fs).1 = f.1 := by
    change f'.map e = f.1
    exact hfeq
  have hgval : (faceOfRelabel e gs).1 = g.1 := by
    change g'.map e = g.1
    exact hgeq
  have hfs : faceOfRelabel e fs = f := Subtype.ext hfval
  have hgs : faceOfRelabel e gs = g := Subtype.ext hgval
  rw [hfs, hgs] at hpath
  exact hpath

omit [DecidableEq A] [DecidableEq B] in
/-- Faces relabeled from different vertex types share an edge when the two source edges have the
same relabeled image. -/
theorem hasCrossEdge_relabel_of_mapped_edge_eq
    {C : Type*} [DecidableEq C]
    (eleft : A ↪ C) (eright : B ↪ C)
    {left : Finset (Finset A)} {right : Finset (Finset B)}
    (fleft : Face left) (fright : Face right)
    (edgeLeft : Finset A) (edgeRight : Finset B)
    (hedgeCard : edgeLeft.card = 2)
    (hedgeLeft : edgeLeft ⊆ fleft.1)
    (hedgeRight : edgeRight ⊆ fright.1)
    (hmap : edgeLeft.map eleft = edgeRight.map eright) :
    HasCrossEdge (Moise.relabelFaceFamily eleft left)
      (Moise.relabelFaceFamily eright right) := by
  refine
    ⟨faceOfRelabel eleft fleft, faceOfRelabel eright fright,
      edgeLeft.map eleft, ?_, ?_, ?_⟩
  · simpa only [Finset.card_map] using hedgeCard
  · exact Finset.map_subset_map.mpr hedgeLeft
  · rw [hmap]
    exact Finset.map_subset_map.mpr hedgeRight

/-- A shared edge remains a shared edge when both families are injectively relabeled. -/
theorem hasCrossEdge_relabel (e : A ↪ B)
    {left right : Finset (Finset A)} (hcross : HasCrossEdge left right) :
    HasCrossEdge (Moise.relabelFaceFamily e left)
      (Moise.relabelFaceFamily e right) := by
  rcases hcross with
    ⟨fleft, fright, edge, hedgeCard, hedgeLeft, hedgeRight⟩
  exact hasCrossEdge_relabel_of_mapped_edge_eq e e
    fleft fright edge edge hedgeCard hedgeLeft hedgeRight rfl

end TriangleFamily

namespace Moise

/-- Push a geometric realization forward along an injective relabeling of all vertices. -/
noncomputable def pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization A F →
      GeometricRealization B (relabelFaceFamily e F) := by
  intro x
  refine ⟨stdSimplex.map e ⟨x.1, x.2.1⟩,
    (stdSimplex.map e ⟨x.1, x.2.1⟩).2, ?_⟩
  obtain ⟨t, ht, hxt⟩ := x.2.2
  refine ⟨t.map e, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  intro b hb
  by_cases hbrange : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hbrange
    rw [stdSimplex_map_embedding_apply]
    apply hxt
    intro hat
    exact hb (Finset.mem_map.mpr ⟨a, hat, rfl⟩)
  · exact stdSimplex_map_embedding_apply_of_notMem_range e _ hbrange

/-- Pull a point of a relabeled realization back to its original vertex type. -/
noncomputable def pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization B (relabelFaceFamily e F) →
      GeometricRealization A F := by
  intro y
  let u : Finset B := Classical.choose y.2.2
  have huData := Classical.choose_spec y.2.2
  have hu : u ∈ relabelFaceFamily e F := huData.1
  have hyu : ∀ b ∉ u, y.1 b = 0 := huData.2
  let t : Finset A := Classical.choose (Finset.mem_image.mp hu)
  have htData := Classical.choose_spec (Finset.mem_image.mp hu)
  have ht : t ∈ F := htData.1
  have hut : t.map e = u := htData.2
  have hyt : ∀ b ∉ t.map e, y.1 b = 0 := by
    intro b hb
    apply hyu b
    rwa [← hut]
  let x : A → ℝ := fun a ↦ y.1 (e a)
  have hx_nonneg : ∀ a, 0 ≤ x a := fun a ↦ y.2.1.1 (e a)
  have hx_sum : ∑ a, x a = 1 := by
    calc
      ∑ a, x a = ∑ a ∈ t, x a := by
        symm
        apply Finset.sum_subset (Finset.subset_univ t)
        intro a _ ha
        apply hyt (e a)
        intro hea
        obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
        exact ha (e.injective hba ▸ hb)
      _ = ∑ b ∈ t.map e, y.1 b := by
        rw [Finset.sum_map]
      _ = ∑ b, y.1 b := by
        apply Finset.sum_subset (Finset.subset_univ (t.map e))
        intro b _ hb
        exact hyt b hb
      _ = 1 := y.2.1.2
  refine ⟨x, ⟨hx_nonneg, hx_sum⟩, t, ht, ?_⟩
  intro a ha
  apply hyt (e a)
  intro hea
  obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
  exact ha (e.injective hba ▸ hb)

@[simp] theorem pushGeometricRealization_val
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) :
    (pushGeometricRealization e F x).1 =
      stdSimplex.map e ⟨x.1, x.2.1⟩ := rfl

@[simp] theorem pushGeometricRealization_apply_embedding
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) (a : A) :
    (pushGeometricRealization e F x).1 (e a) = x.1 a := by
  rw [pushGeometricRealization_val,
    stdSimplex_map_embedding_apply]
  rfl

theorem pushGeometricRealization_apply_of_notMem_range
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) {b : B}
    (hb : b ∉ Set.range e) :
    (pushGeometricRealization e F x).1 b = 0 := by
  rw [pushGeometricRealization_val]
  exact stdSimplex_map_embedding_apply_of_notMem_range e _ hb

theorem pushGeometricRealization_val_eq_of_val_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F G : Finset (Finset A))
    (x : GeometricRealization A F)
    (y : GeometricRealization A G) (hxy : x.1 = y.1) :
    (pushGeometricRealization e F x).1 =
      (pushGeometricRealization e G y).1 := by
  funext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [pushGeometricRealization_apply_embedding,
      pushGeometricRealization_apply_embedding]
    exact congrFun hxy a
  · rw [pushGeometricRealization_apply_of_notMem_range e F x hb,
      pushGeometricRealization_apply_of_notMem_range e G y hb]

@[simp] theorem pullGeometricRealization_apply
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (y : GeometricRealization B (relabelFaceFamily e F)) (a : A) :
    (pullGeometricRealization e F y).1 a = y.1 (e a) := by
  rfl

@[simp] theorem pull_pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) :
    pullGeometricRealization e F (pushGeometricRealization e F x) = x := by
  apply Subtype.ext
  funext a
  rw [pullGeometricRealization_apply, pushGeometricRealization_val]
  exact stdSimplex_map_embedding_apply e ⟨x.1, x.2.1⟩ a

@[simp] theorem push_pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (y : GeometricRealization B (relabelFaceFamily e F)) :
    pushGeometricRealization e F (pullGeometricRealization e F y) = y := by
  apply Subtype.ext
  funext b
  by_cases hbrange : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hbrange
    rw [pushGeometricRealization_val]
    rw [stdSimplex_map_embedding_apply]
    exact pullGeometricRealization_apply e F y a
  · rw [pushGeometricRealization_val,
      stdSimplex_map_embedding_apply_of_notMem_range _ _ hbrange]
    obtain ⟨u, hu, hyu⟩ := y.2.2
    obtain ⟨t, -, hut⟩ := Finset.mem_image.mp hu
    symm
    apply hyu
    subst u
    intro hb
    obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hb
    exact hbrange ⟨a, hab⟩

theorem continuous_pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    Continuous (pushGeometricRealization e F) := by
  apply Continuous.subtype_mk
  have hin :
      Continuous fun x : GeometricRealization A F ↦
        (⟨x.1, x.2.1⟩ : stdSimplex ℝ A) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  exact continuous_subtype_val.comp
    ((stdSimplex.continuous_map e).comp hin)

theorem continuous_pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    Continuous (pullGeometricRealization e F) := by
  apply Continuous.subtype_mk
  change Continuous fun y :
      GeometricRealization B (relabelFaceFamily e F) ↦
        fun a ↦ y.1 (e a)
  exact continuous_pi fun a ↦
    (continuous_apply (e a)).comp continuous_subtype_val

/-- Relabeling a finite face family along a vertex embedding does not change its realization. -/
noncomputable def relabelGeometricRealizationHomeomorph
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization A F ≃ₜ
      GeometricRealization B (relabelFaceFamily e F) where
  toFun := pushGeometricRealization e F
  invFun := pullGeometricRealization e F
  left_inv := pull_pushGeometricRealization e F
  right_inv := push_pullGeometricRealization e F
  continuous_toFun := continuous_pushGeometricRealization e F
  continuous_invFun := continuous_pullGeometricRealization e F

/-- Weighted evaluation is unchanged by whole-type relabeling. -/
theorem sum_extendFaceCoordinates_relabelUnivSimplex
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B)
    (x : stdSimplex ℝ
      {b // b ∈ (Finset.univ : Finset A).map e})
    (F : B → ℝ) :
    (∑ b : B,
        extendFaceCoordinates
          ((Finset.univ : Finset A).map e) x b * F b) =
      ∑ a : A, relabelUnivSimplex e x a * F (e a) := by
  classical
  calc
    (∑ b : B,
        extendFaceCoordinates
          ((Finset.univ : Finset A).map e) x b * F b) =
        ∑ b ∈ (Finset.univ : Finset A).map e,
          extendFaceCoordinates
            ((Finset.univ : Finset A).map e) x b * F b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [extendFaceCoordinates_of_notMem _ _ hb, zero_mul]
    _ = ∑ a : A,
          extendFaceCoordinates
            ((Finset.univ : Finset A).map e) x (e a) *
              F (e a) := by
      rw [Finset.sum_map]
    _ = ∑ a : A, relabelUnivSimplex e x a * F (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [relabelUnivSimplex_apply]

/-- A sum over the subtype of a finite face is the corresponding sum of its zero-extended
coordinates over the underlying vertex set. -/
theorem sum_attach_mul_eq_sum_extendFaceCoordinates
    {V : Type*} [DecidableEq V] (t : Finset V)
  (x : stdSimplex ℝ {v // v ∈ t}) (F : V → ℝ) :
    (∑ v : {v // v ∈ t}, x v * F v.1) =
      ∑ v ∈ t, extendFaceCoordinates t x v * F v := by
  rw [Finset.univ_eq_attach]
  calc
    (∑ v ∈ t.attach, x v * F v.1) =
        ∑ v ∈ t.attach, extendFaceCoordinates t x v.1 * F v.1 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [extendFaceCoordinates_of_mem t x v.2]
    _ = ∑ v ∈ t, extendFaceCoordinates t x v * F v :=
      Finset.sum_attach t fun v ↦ extendFaceCoordinates t x v * F v

/-- Equal zero-extended coordinates give equal weighted sums against any scalar-valued
function on the global vertex type. -/
theorem sum_extendFaceCoordinates_eq_of_eq
    {V : Type*} [DecidableEq V] {s t : Finset V}
    (x : stdSimplex ℝ {v // v ∈ s}) (y : stdSimplex ℝ {v // v ∈ t})
    (hxy : extendFaceCoordinates s x = extendFaceCoordinates t y)
    (F : V → ℝ) :
    (∑ v : {v // v ∈ s}, x v * F v.1) =
      ∑ v : {v // v ∈ t}, y v * F v.1 := by
  rw [sum_attach_mul_eq_sum_extendFaceCoordinates s x F,
    sum_attach_mul_eq_sum_extendFaceCoordinates t y F]
  calc
    (∑ v ∈ s, extendFaceCoordinates s x v * F v) =
        ∑ v ∈ s ∪ t, extendFaceCoordinates s x v * F v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro v _ hv
      rw [extendFaceCoordinates_of_notMem s x hv, zero_mul]
    _ = ∑ v ∈ s ∪ t, extendFaceCoordinates t y v * F v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [congrFun hxy v]
    _ = ∑ v ∈ t, extendFaceCoordinates t y v * F v := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro v _ hv
      rw [extendFaceCoordinates_of_notMem t y hv, zero_mul]

/-- A locally finite family of parametrized triangles in an ambient topological space.

`vertex_used` excludes irrelevant vertices.  This matters in the compactness-to-finiteness
bridge: local finiteness controls the number of nonempty faces, and every vertex must then occur
in one of those faces. -/
structure LocallyFiniteTriangleComplex (S : Type*) [TopologicalSpace S] where
  /-- Global vertices, shared literally by incident faces. -/
  Vertex : Type
  /-- Equality of vertices is decidable so that faces are finite sets. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- Maximal two-dimensional faces. -/
  Face : Type
  /-- Equality of maximal faces is decidable. -/
  [faceDecidableEq : DecidableEq Face]
  /-- The three global vertices of a maximal face. -/
  faceVertices : Face → Finset Vertex
  /-- Every maximal face is a triangle. -/
  faceVertices_card : ∀ f, (faceVertices f).card = 3
  /-- Every declared global vertex occurs in a maximal face. -/
  vertex_used : ∀ v, ∃ f, v ∈ faceVertices f
  /-- Coordinate map of a closed triangle into the ambient space. -/
  faceMap : ∀ f, stdSimplex ℝ {v // v ∈ faceVertices f} → S
  /-- Each coordinate map is continuous. -/
  faceMap_continuous : ∀ f, Continuous (faceMap f)
  /-- Exact face-to-face compatibility and global injectivity, expressed in barycentric
  coordinates. -/
  faceMap_eq_iff : ∀ {f g} {x y},
    faceMap f x = faceMap g y ↔
      extendFaceCoordinates (faceVertices f) x =
        extendFaceCoordinates (faceVertices g) y
  /-- The closed triangle carriers form a locally finite family. -/
  locallyFinite : LocallyFinite fun f ↦ Set.range (faceMap f)

attribute [instance] LocallyFiniteTriangleComplex.vertexDecidableEq
attribute [instance] LocallyFiniteTriangleComplex.faceDecidableEq

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- The ambient carrier of one maximal face. -/
def faceCarrier (f : K.Face) : Set S :=
  Set.range (K.faceMap f)

/-- The ambient support of the locally finite complex. -/
def support : Set S :=
  ⋃ f, K.faceCarrier f

theorem faceCarrier_nonempty (f : K.Face) : (K.faceCarrier f).Nonempty := by
  have hne : (K.faceVertices f).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := K.faceVertices_card f
    rw [h] at this
    simp at this
  let v : {v // v ∈ K.faceVertices f} := ⟨hne.choose, hne.choose_spec⟩
  exact ⟨K.faceMap f (stdSimplex.vertex v), Set.mem_range_self _⟩

theorem faceMap_injective (f : K.Face) : Function.Injective (K.faceMap f) := by
  intro x y hxy
  have hcoords := K.faceMap_eq_iff.mp hxy
  apply stdSimplex.ext
  funext v
  have hv := congrFun hcoords v.1
  simpa only [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
    extendFaceCoordinates_of_mem (K.faceVertices f) y v.2] using hv

theorem isEmbedding_faceMap [T2Space S] (f : K.Face) :
    _root_.Topology.IsEmbedding (K.faceMap f) :=
  ((K.faceMap_continuous f).isClosedEmbedding (K.faceMap_injective f)).isEmbedding

theorem isCompact_faceCarrier (f : K.Face) : IsCompact (K.faceCarrier f) :=
  isCompact_range (K.faceMap_continuous f)

theorem isClosed_faceCarrier [T2Space S] (f : K.Face) : IsClosed (K.faceCarrier f) :=
  (K.isCompact_faceCarrier f).isClosed

theorem isClosed_support [T2Space S] : IsClosed K.support :=
  K.locallyFinite.isClosed_iUnion K.isClosed_faceCarrier

theorem extendFaceCoordinates_vertex (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) :
    extendFaceCoordinates (K.faceVertices f)
        (stdSimplex.vertex ⟨v, hv⟩) = Pi.single v 1 := by
  funext w
  by_cases hwv : w = v
  · subst w
    simp [extendFaceCoordinates, hv]
  · by_cases hw : w ∈ K.faceVertices f
    · have hsub : (⟨w, hw⟩ : {w // w ∈ K.faceVertices f}) ≠ ⟨v, hv⟩ := by
        exact fun h ↦ hwv (congrArg Subtype.val h)
      simp [extendFaceCoordinates, hw, hwv, hsub]
    · simp [extendFaceCoordinates, hw, hwv]

/-- A chosen maximal face incident to a global vertex. -/
noncomputable def incidentFace (v : K.Vertex) : K.Face :=
  Classical.choose (K.vertex_used v)

theorem mem_faceVertices_incidentFace (v : K.Vertex) :
    v ∈ K.faceVertices (K.incidentFace v) :=
  Classical.choose_spec (K.vertex_used v)

/-- The ambient point represented by a global vertex. -/
noncomputable def vertexPoint (v : K.Vertex) : S :=
  K.faceMap (K.incidentFace v)
    (stdSimplex.vertex ⟨v, K.mem_faceVertices_incidentFace v⟩)

/-- Every incident face parametrization sends a shared abstract vertex to the same ambient
point. -/
theorem faceMap_vertex_eq_vertexPoint (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) :
    K.faceMap f (stdSimplex.vertex ⟨v, hv⟩) = K.vertexPoint v := by
  apply K.faceMap_eq_iff.mpr
  rw [K.extendFaceCoordinates_vertex f hv,
    K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v)]

theorem vertexPoint_in_faceCarrier (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) : K.vertexPoint v ∈ K.faceCarrier f :=
  ⟨stdSimplex.vertex ⟨v, hv⟩, K.faceMap_vertex_eq_vertexPoint f hv⟩

theorem vertexPoint_injective : Function.Injective K.vertexPoint := by
  intro v w hvw
  have hcoords := K.faceMap_eq_iff.mp hvw
  rw [K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v),
    K.extendFaceCoordinates_vertex (K.incidentFace w)
      (K.mem_faceVertices_incidentFace w)] at hcoords
  by_contra hvw'
  have h := congrFun hcoords v
  simp [hvw'] at h

/-- Singleton carriers of the global vertices form a locally finite family. -/
theorem locallyFinite_vertexPoints :
    LocallyFinite fun v : K.Vertex ↦ ({K.vertexPoint v} : Set S) := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := K.locallyFinite x
  refine ⟨U, hUx, ?_⟩
  let F : Set K.Face := {f | (K.faceCarrier f ∩ U).Nonempty}
  let V : Set K.Vertex := ⋃ f ∈ F, (K.faceVertices f : Set K.Vertex)
  have hVfinite : V.Finite := hfinite.biUnion fun f _ ↦
    (K.faceVertices f).finite_toSet
  apply hVfinite.subset
  intro v hv
  obtain ⟨p, hpv, hpU⟩ := hv
  have hp : p = K.vertexPoint v := hpv
  subst p
  apply Set.mem_iUnion₂.mpr
  refine ⟨K.incidentFace v, ?_, K.mem_faceVertices_incidentFace v⟩
  exact ⟨K.vertexPoint v,
    K.vertexPoint_in_faceCarrier (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v), hpU⟩

/-! ## Cyclic data on a maximal face -/

/-- A chosen cyclic enumeration of the three vertices of a maximal face. -/
noncomputable def faceVertexEquiv (f : K.Face) : Fin 3 ≃ {v // v ∈ K.faceVertices f} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, K.faceVertices_card f])

/-- Cyclically indexed vertices of a maximal face. -/
noncomputable def faceVertex (f : K.Face) (i : ZMod 3) : K.Vertex :=
  (K.faceVertexEquiv f ((ZMod.finEquiv 3).symm i)).1

theorem faceVertex_mem (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ∈ K.faceVertices f :=
  (K.faceVertexEquiv f ((ZMod.finEquiv 3).symm i)).2

theorem faceVertex_injective (f : K.Face) : Function.Injective (K.faceVertex f) := by
  intro i j hij
  apply (ZMod.finEquiv 3).symm.injective
  apply (K.faceVertexEquiv f).injective
  exact Subtype.ext hij

theorem faceVertex_ne_next (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ≠ K.faceVertex f (i + 1) := by
  intro h
  have hi : i = i + 1 := K.faceVertex_injective f h
  have hone : (0 : ZMod 3) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z ↦ z - i) hi
      _ = 1 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 1) hone

theorem faceVertex_ne_add_two (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ≠ K.faceVertex f (i + 2) := by
  intro h
  have hi : i = i + 2 := K.faceVertex_injective f h
  have htwo : (0 : ZMod 3) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z ↦ z - i) hi
      _ = 2 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-! ## Edges -/

/-- A two-element vertex set contained in a maximal face. -/
def IsEdge (e : Finset K.Vertex) : Prop :=
  e.card = 2 ∧ ∃ f : K.Face, e ⊆ K.faceVertices f

/-- The edge type of a locally finite triangle complex. -/
abbrev Edge := {e : Finset K.Vertex // K.IsEdge e}

/-- The chosen first endpoint of an edge. -/
noncomputable def edgeFirst (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp e.2.1).choose

/-- The chosen second endpoint of an edge. -/
noncomputable def edgeSecond (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (e : K.Edge) :
    K.edgeFirst e ≠ K.edgeSecond e :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose_spec.1

theorem edge_eq_pair (e : K.Edge) :
    e.1 = {K.edgeFirst e, K.edgeSecond e} :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose_spec.2

theorem edgeFirst_mem (e : K.Edge) : K.edgeFirst e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

theorem edgeSecond_mem (e : K.Edge) : K.edgeSecond e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

/-- The edge joining two consecutive cyclic vertices of a maximal face. -/
noncomputable def faceEdge (f : K.Face) (i : ZMod 3) : K.Edge := by
  refine ⟨{K.faceVertex f i, K.faceVertex f (i + 1)}, ?_⟩
  refine ⟨?_, f, ?_⟩
  · simp [K.faceVertex_ne_next f i]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact K.faceVertex_mem f i
    · exact K.faceVertex_mem f (i + 1)

@[simp] theorem faceEdge_val (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 = {K.faceVertex f i, K.faceVertex f (i + 1)} := rfl

/-- Consecutive face edges share exactly their common cyclic vertex. -/
theorem faceEdge_inter_next (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 ∩ (K.faceEdge f (i + 1)).1 =
      {K.faceVertex f (i + 1)} := by
  ext v
  simp only [faceEdge_val, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton, add_assoc, one_add_one_eq_two]
  constructor
  · rintro ⟨hvi | hvi, hvnext | hvtwo⟩
    · exact (K.faceVertex_ne_next f i (hvi.symm.trans hvnext)).elim
    · exact (K.faceVertex_ne_add_two f i (hvi.symm.trans hvtwo)).elim
    · exact hvi
    · exact hvi
  · intro hv
    exact ⟨Or.inr hv, Or.inl hv⟩

theorem faceEdge_ne_next (f : K.Face) (i : ZMod 3) :
    K.faceEdge f i ≠ K.faceEdge f (i + 1) := by
  intro h
  have hval := congrArg (fun e : K.Edge ↦ e.1) h
  have hmem : K.faceVertex f i ∈ (K.faceEdge f (i + 1)).1 := by
    rw [← hval]
    simp
  simp only [faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hi | hi
  · exact K.faceVertex_ne_next f i hi
  · have hz : i = i + 2 := K.faceVertex_injective f (by
        simpa only [one_add_one_eq_two, add_assoc] using hi)
    have htwo : (0 : ZMod 3) = 2 := by
      calc
        0 = i - i := by abel
        _ = (i + 2) - i := congrArg (fun z ↦ z - i) hz
        _ = 2 := by abel
    exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- The arbitrary endpoint ordering of a cyclic face edge is one of its two cyclic
orientations. -/
theorem faceEdge_endpoint_order (f : K.Face) (i : ZMod 3) :
    (K.edgeFirst (K.faceEdge f i) = K.faceVertex f i ∧
        K.edgeSecond (K.faceEdge f i) = K.faceVertex f (i + 1)) ∨
      (K.edgeFirst (K.faceEdge f i) = K.faceVertex f (i + 1) ∧
        K.edgeSecond (K.faceEdge f i) = K.faceVertex f i) := by
  have hfirst := K.edgeFirst_mem (K.faceEdge f i)
  have hsecond := K.edgeSecond_mem (K.faceEdge f i)
  rw [K.faceEdge_val f i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
      (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
      (hfirst.trans hsecond.symm)).elim

/-- The standard one-simplex point at interval parameter `r`. -/
noncomputable def edgeSimplexPath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {v // v ∈ e.1} := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  let x := AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) r.1
  exact ⟨x, (convex_stdSimplex ℝ {v // v ∈ e.1}).lineMap_mem
    (stdSimplex.vertex a).2 (stdSimplex.vertex b).2 r.2⟩

theorem continuous_edgeSimplexPath (e : K.Edge) :
    Continuous (K.edgeSimplexPath e) := by
  apply Continuous.subtype_mk
  exact (AffineMap.lineMap (k := ℝ)
    (stdSimplex.vertex
      (⟨K.edgeFirst e, K.edgeFirst_mem e⟩ : {v // v ∈ e.1}) :
        {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex
      (⟨K.edgeSecond e, K.edgeSecond_mem e⟩ : {v // v ∈ e.1}) :
        {v // v ∈ e.1} → ℝ)).continuous_of_finiteDimensional.comp continuous_subtype_val

@[simp] theorem edgeSimplexPath_apply_first (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    K.edgeSimplexPath e r ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ = 1 - r.1 := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  change (K.edgeSimplexPath e r).1 a = 1 - r.1
  dsimp only [edgeSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  dsimp only [a, b] at hab ⊢
  simp [hab]

@[simp] theorem edgeSimplexPath_apply_second (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    K.edgeSimplexPath e r ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ = r.1 := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  change (K.edgeSimplexPath e r).1 b = r.1
  dsimp only [edgeSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  dsimp only [a, b] at hab ⊢
  simp [hab]

theorem edgeSimplexPath_injective (e : K.Edge) :
    Function.Injective (K.edgeSimplexPath e) := by
  intro r s hrs
  apply Subtype.ext
  have hcoord := congrArg
    (fun x : stdSimplex ℝ {v // v ∈ e.1} =>
      x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩) hrs
  simpa using hcoord

/-- A chosen maximal face incident to an edge. -/
noncomputable def edgeFace (e : K.Edge) : K.Face :=
  Classical.choose e.2.2

theorem edge_subset_faceVertices (e : K.Edge) :
    e.1 ⊆ K.faceVertices (K.edgeFace e) :=
  Classical.choose_spec e.2.2

/-- Include edge-local vertices into a chosen incident maximal face. -/
def edgeVertexToFace (e : K.Edge) :
    {v // v ∈ e.1} → {v // v ∈ K.faceVertices (K.edgeFace e)} :=
  fun v ↦ ⟨v.1, K.edge_subset_faceVertices e v.2⟩

theorem extendFaceCoordinates_map_edgeVertexToFace (e : K.Edge)
    (x : stdSimplex ℝ {v // v ∈ e.1}) :
    extendFaceCoordinates (K.faceVertices (K.edgeFace e))
        (stdSimplex.map (K.edgeVertexToFace e) x) =
      extendFaceCoordinates e.1 x := by
  unfold edgeVertexToFace
  exact extendFaceCoordinates_map_subset (K.edge_subset_faceVertices e) x

/-- Parametrization of a closed edge by its standard one-simplex. -/
noncomputable def edgeMap (e : K.Edge) (x : stdSimplex ℝ {v // v ∈ e.1}) : S :=
  K.faceMap (K.edgeFace e) (stdSimplex.map (K.edgeVertexToFace e) x)

/-- The canonical interval parametrization of an ambient edge carrier. -/
noncomputable def edgePath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) : S :=
  K.edgeMap e (K.edgeSimplexPath e r)

theorem edgeMap_eq_faceMap (e : K.Edge) (f : K.Face)
    (hef : e.1 ⊆ K.faceVertices f) (x : stdSimplex ℝ {v // v ∈ e.1}) :
    K.edgeMap e x = K.faceMap f
      (stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) x) := by
  apply K.faceMap_eq_iff.mpr
  calc
    extendFaceCoordinates (K.faceVertices (K.edgeFace e))
        (stdSimplex.map (K.edgeVertexToFace e) x) =
        extendFaceCoordinates e.1 x := by
          exact K.extendFaceCoordinates_map_edgeVertexToFace e x
    _ = extendFaceCoordinates (K.faceVertices f)
        (stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) x) :=
      (extendFaceCoordinates_map_subset hef x).symm

theorem continuous_edgeMap (e : K.Edge) : Continuous (K.edgeMap e) :=
  (K.faceMap_continuous (K.edgeFace e)).comp
    (stdSimplex.continuous_map (K.edgeVertexToFace e))

theorem continuous_edgePath (e : K.Edge) : Continuous (K.edgePath e) :=
  (K.continuous_edgeMap e).comp (K.continuous_edgeSimplexPath e)

theorem edgeMap_injective (e : K.Edge) : Function.Injective (K.edgeMap e) := by
  intro x y hxy
  have hcoords := K.faceMap_eq_iff.mp hxy
  have hcoords' : extendFaceCoordinates e.1 x = extendFaceCoordinates e.1 y := by
    calc
      extendFaceCoordinates e.1 x =
          extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) x) := by
        exact (K.extendFaceCoordinates_map_edgeVertexToFace e x).symm
      _ = extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) y) := hcoords
      _ = extendFaceCoordinates e.1 y := by
        exact K.extendFaceCoordinates_map_edgeVertexToFace e y
  apply stdSimplex.ext
  funext v
  have h := congrFun hcoords' v.1
  simpa only [extendFaceCoordinates_of_mem e.1 x v.2,
    extendFaceCoordinates_of_mem e.1 y v.2] using h

theorem edgePath_injective (e : K.Edge) : Function.Injective (K.edgePath e) :=
  (K.edgeMap_injective e).comp (K.edgeSimplexPath_injective e)

theorem range_edgeSimplexPath (e : K.Edge) :
    Set.range (K.edgeSimplexPath e) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩,
      mem_Icc_of_mem_stdSimplex x.2 ⟨K.edgeSecond e, K.edgeSecond_mem e⟩⟩
  refine ⟨r, ?_⟩
  apply stdSimplex.ext
  funext v
  by_cases hvFirst : v.1 = K.edgeFirst e
  · have hv : v = ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ := Subtype.ext hvFirst
    subst v
    rw [K.edgeSimplexPath_apply_first]
    have hsumPair :
        x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ +
            x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ = 1 := by
      let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
      let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
      have hab : a ≠ b := by
        intro h
        exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
      have huniv : (Finset.univ : Finset {v // v ∈ e.1}) = {a, b} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        have hw : w.1 = K.edgeFirst e ∨ w.1 = K.edgeSecond e := by
          simpa only [K.edge_eq_pair e, Finset.mem_insert, Finset.mem_singleton] using w.2
        rcases hw with hw | hw
        · exact Or.inl (Subtype.ext hw)
        · exact Or.inr (Subtype.ext hw)
      calc
        x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ +
            x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ =
            ∑ w : {w // w ∈ e.1}, x w := by
              change x a + x b =
                (Finset.univ : Finset {v // v ∈ e.1}).sum (fun w => x w)
              rw [huniv]
              simp [hab]
        _ = 1 := x.2.2
    change 1 - x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ =
      x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
    linarith
  · have hvSecond : v.1 = K.edgeSecond e := by
      have hv : v.1 = K.edgeFirst e ∨ v.1 = K.edgeSecond e := by
        simpa only [K.edge_eq_pair e, Finset.mem_insert, Finset.mem_singleton] using v.2
      exact hv.resolve_left hvFirst
    have hv : v = ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ := Subtype.ext hvSecond
    subst v
    rw [K.edgeSimplexPath_apply_second]

/-- The ambient carrier of an edge. -/
def edgeCarrier (e : K.Edge) : Set S :=
  Set.range (K.edgeMap e)

theorem range_edgePath (e : K.Edge) :
    Set.range (K.edgePath e) = K.edgeCarrier e := by
  apply Set.Subset.antisymm
  · rintro y ⟨r, rfl⟩
    exact ⟨K.edgeSimplexPath e r, rfl⟩
  · rintro y ⟨x, rfl⟩
    have hx : x ∈ Set.range (K.edgeSimplexPath e) := by
      rw [K.range_edgeSimplexPath e]
      exact Set.mem_univ x
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, rfl⟩

theorem edgeMap_vertex_eq_vertexPoint (e : K.Edge) (v : {v // v ∈ e.1}) :
    K.edgeMap e (stdSimplex.vertex v) = K.vertexPoint v.1 := by
  rw [edgeMap, stdSimplex.map_vertex]
  exact K.faceMap_vertex_eq_vertexPoint (K.edgeFace e)
    (K.edge_subset_faceVertices e v.2)

/-- Distinct edge carriers meet only at points represented by their shared abstract vertices. -/
theorem edgeCarrier_inter_subset_sharedVertices {e d : K.Edge} (hed : e ≠ d) :
    K.edgeCarrier e ∩ K.edgeCarrier d ⊆
      {p | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ p = K.vertexPoint v} := by
  rintro p ⟨⟨x, hxp⟩, ⟨y, hyp⟩⟩
  have hcoords₀ := K.faceMap_eq_iff.mp (hxp.trans hyp.symm)
  have hcoords : extendFaceCoordinates e.1 x = extendFaceCoordinates d.1 y := by
    calc
      extendFaceCoordinates e.1 x =
          extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) x) :=
        (K.extendFaceCoordinates_map_edgeVertexToFace e x).symm
      _ = extendFaceCoordinates (K.faceVertices (K.edgeFace d))
            (stdSimplex.map (K.edgeVertexToFace d) y) := hcoords₀
      _ = extendFaceCoordinates d.1 y :=
        K.extendFaceCoordinates_map_edgeVertexToFace d y
  have hex : ∃ v : {v // v ∈ e.1}, 0 < x v := by
    by_contra h
    push Not at h
    have hxzero : ∀ v : {v // v ∈ e.1}, x v = 0 := by
      intro v
      exact le_antisymm (h v) (x.2.1 v)
    have hsum : ∑ v, x v = 0 := by simp [hxzero]
    have hone : (1 : ℝ) = 0 := x.2.2.symm.trans hsum
    norm_num at hone
  obtain ⟨v, hvpos⟩ := hex
  have hvd : v.1 ∈ d.1 := by
    by_contra hvd
    have hc := congrFun hcoords v.1
    rw [extendFaceCoordinates_of_mem e.1 x v.2,
      extendFaceCoordinates_of_notMem d.1 y hvd] at hc
    linarith
  have hxzero : ∀ w : {w // w ∈ e.1}, w ≠ v → x w = 0 := by
    intro w hwv
    by_contra hxw
    have hxwpos : 0 < x w := lt_of_le_of_ne (x.2.1 w) (Ne.symm hxw)
    have hwd : w.1 ∈ d.1 := by
      by_contra hwd
      have hc := congrFun hcoords w.1
      rw [extendFaceCoordinates_of_mem e.1 x w.2,
        extendFaceCoordinates_of_notMem d.1 y hwd] at hc
      linarith
    have hvw : v.1 ≠ w.1 := by
      intro h
      exact hwv (Subtype.ext h.symm)
    let q : Finset K.Vertex := {v.1, w.1}
    have hqcard : q.card = 2 := by simp [q, hvw]
    have hqe : q ⊆ e.1 := by
      intro z hz
      simp only [q, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact v.2
      · exact w.2
    have hqd : q ⊆ d.1 := by
      intro z hz
      simp only [q, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hvd
      · exact hwd
    have hqeEq : q = e.1 :=
      Finset.eq_of_subset_of_card_le hqe (by rw [hqcard, e.2.1])
    have hqdEq : q = d.1 :=
      Finset.eq_of_subset_of_card_le hqd (by rw [hqcard, d.2.1])
    apply hed
    apply Subtype.ext
    exact hqeEq.symm.trans hqdEq
  have hxv : x v = 1 := by
    calc
      x v = ∑ w, x w := by
        rw [Finset.sum_eq_single v]
        · intro w _ hw
          exact hxzero w hw
        · simp
      _ = 1 := x.2.2
  have hxvertex : x = stdSimplex.vertex v := by
    apply stdSimplex.ext
    funext w
    by_cases hwv : w = v
    · subst w
      simp [hxv]
    · rw [hxzero w hwv]
      simp [hwv]
  refine ⟨v.1, v.2, hvd, ?_⟩
  rw [← hxp, hxvertex]
  exact K.edgeMap_vertex_eq_vertexPoint e v

theorem edgeCarrier_inter_eq_sharedVertices {e d : K.Edge} (hed : e ≠ d) :
    K.edgeCarrier e ∩ K.edgeCarrier d =
      {p | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ p = K.vertexPoint v} := by
  apply Set.Subset.antisymm (K.edgeCarrier_inter_subset_sharedVertices hed)
  rintro p ⟨v, hve, hvd, rfl⟩
  let ve : {w // w ∈ e.1} := ⟨v, hve⟩
  let vd : {w // w ∈ d.1} := ⟨v, hvd⟩
  exact ⟨⟨stdSimplex.vertex ve, K.edgeMap_vertex_eq_vertexPoint e ve⟩,
    ⟨stdSimplex.vertex vd, K.edgeMap_vertex_eq_vertexPoint d vd⟩⟩

theorem isCompact_edgeCarrier (e : K.Edge) : IsCompact (K.edgeCarrier e) :=
  isCompact_range (K.continuous_edgeMap e)

theorem edgeCarrier_subset_faceCarrier (e : K.Edge) :
    K.edgeCarrier e ⊆ K.faceCarrier (K.edgeFace e) := by
  rintro y ⟨x, rfl⟩
  exact ⟨stdSimplex.map (K.edgeVertexToFace e) x, rfl⟩

/-- Edge carriers inherit local finiteness from the maximal-face carriers. -/
theorem locallyFinite_edgeCarriers : LocallyFinite K.edgeCarrier := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := K.locallyFinite x
  refine ⟨U, hUx, ?_⟩
  let F : Set K.Face := {f | (K.faceCarrier f ∩ U).Nonempty}
  let E : Set K.Edge := ⋃ f ∈ F,
    {e : K.Edge | e.1 ∈ (K.faceVertices f).powersetCard 2}
  have hfiber (f : K.Face) :
      ({e : K.Edge | e.1 ∈ (K.faceVertices f).powersetCard 2} : Set K.Edge).Finite := by
    change ((fun e : K.Edge ↦ e.1) ⁻¹'
      ((K.faceVertices f).powersetCard 2 : Set (Finset K.Vertex))).Finite
    exact Set.Finite.preimage Subtype.val_injective.injOn
      ((K.faceVertices f).powersetCard 2).finite_toSet
  have hEfinite : E.Finite := hfinite.biUnion fun f _ ↦ hfiber f
  apply hEfinite.subset
  intro e he
  obtain ⟨p, hpEdge, hpU⟩ := he
  apply Set.mem_iUnion₂.mpr
  refine ⟨K.edgeFace e, ?_, ?_⟩
  · exact ⟨p, K.edgeCarrier_subset_faceCarrier e hpEdge, hpU⟩
  · exact Finset.mem_powersetCard.mpr
      ⟨K.edge_subset_faceVertices e, e.2.1⟩

theorem edgeSimplexPath_zero (e : K.Edge) :
    K.edgeSimplexPath e ⟨0, by simp⟩ =
      stdSimplex.vertex ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ := by
  apply stdSimplex.ext
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  change AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) 0 = stdSimplex.vertex a
  simp [AffineMap.lineMap_apply_module]

theorem edgeSimplexPath_one (e : K.Edge) :
    K.edgeSimplexPath e ⟨1, by simp⟩ =
      stdSimplex.vertex ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ := by
  apply stdSimplex.ext
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  change AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) 1 = stdSimplex.vertex b
  simp [AffineMap.lineMap_apply_module]

theorem edgePath_zero (e : K.Edge) :
    K.edgePath e ⟨0, by simp⟩ = K.vertexPoint (K.edgeFirst e) := by
  rw [edgePath, K.edgeSimplexPath_zero e,
    K.edgeMap_vertex_eq_vertexPoint e]

theorem edgePath_one (e : K.Edge) :
    K.edgePath e ⟨1, by simp⟩ = K.vertexPoint (K.edgeSecond e) := by
  rw [edgePath, K.edgeSimplexPath_one e,
    K.edgeMap_vertex_eq_vertexPoint e]

/-- The one-skeleton carrier of a locally finite triangle complex. -/
def oneSkeleton : Set S :=
  ⋃ e : K.Edge, K.edgeCarrier e

theorem edgeCarrier_subset_oneSkeleton (e : K.Edge) :
    K.edgeCarrier e ⊆ K.oneSkeleton :=
  Set.subset_iUnion (fun d : K.Edge ↦ K.edgeCarrier d) e

theorem locallyFinite_oneSkeleton_cover : LocallyFinite K.edgeCarrier :=
  K.locallyFinite_edgeCarriers

/-- The canonical interval parameter of a point known to lie on an edge carrier. -/
noncomputable def edgeParameter (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e) :
    Set.Icc (0 : ℝ) 1 :=
  Classical.choose (by rw [← K.range_edgePath e] at hp; exact hp)

theorem edgePath_edgeParameter (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e) :
    K.edgePath e (K.edgeParameter e p hp) = p :=
  Classical.choose_spec (by rw [← K.range_edgePath e] at hp; exact hp)

theorem edgeParameter_unique (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e)
    (r : Set.Icc (0 : ℝ) 1) (hr : K.edgePath e r = p) :
    K.edgeParameter e p hp = r := by
  apply K.edgePath_injective e
  rw [K.edgePath_edgeParameter e p hp, hr]

theorem vertexPoint_mem_edgeCarrier_iff (v : K.Vertex) (e : K.Edge) :
    K.vertexPoint v ∈ K.edgeCarrier e ↔ v ∈ e.1 := by
  constructor
  · rintro ⟨x, hx⟩
    have hcoords := K.faceMap_eq_iff.mp hx.symm
    rw [K.extendFaceCoordinates_map_edgeVertexToFace e x,
      K.extendFaceCoordinates_vertex (K.incidentFace v)
        (K.mem_faceVertices_incidentFace v)] at hcoords
    by_contra hve
    have h := congrFun hcoords v
    simp [extendFaceCoordinates, hve] at h
  · intro hve
    let w : {w // w ∈ e.1} := ⟨v, hve⟩
    exact ⟨stdSimplex.vertex w, K.edgeMap_vertex_eq_vertexPoint e w⟩

@[simp] theorem edgeParameter_vertexPoint_first (e : K.Edge) :
    K.edgeParameter e (K.vertexPoint (K.edgeFirst e))
      ((K.vertexPoint_mem_edgeCarrier_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e)) =
        ⟨0, by simp⟩ := by
  apply K.edgeParameter_unique
  exact K.edgePath_zero e

@[simp] theorem edgeParameter_vertexPoint_second (e : K.Edge) :
    K.edgeParameter e (K.vertexPoint (K.edgeSecond e))
      ((K.vertexPoint_mem_edgeCarrier_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e)) =
        ⟨1, by simp⟩ := by
  apply K.edgeParameter_unique
  exact K.edgePath_one e

theorem disjoint_vertexPoint_edgeCarrier {v : K.Vertex} {e : K.Edge}
    (hve : v ∉ e.1) : Disjoint ({K.vertexPoint v} : Set S) (K.edgeCarrier e) := by
  rw [Set.disjoint_singleton_left]
  exact fun h ↦ hve ((K.vertexPoint_mem_edgeCarrier_iff v e).mp h)

theorem isClosed_edgeCarrier [T2Space S] (e : K.Edge) : IsClosed (K.edgeCarrier e) :=
  (K.isCompact_edgeCarrier e).isClosed

/-- The interval parametrization with codomain restricted to the edge carrier. -/
noncomputable def edgePathToCarrier (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 → K.edgeCarrier e :=
  fun r ↦ ⟨K.edgePath e r, by rw [← K.range_edgePath e]; exact Set.mem_range_self r⟩

theorem continuous_edgePathToCarrier (e : K.Edge) :
    Continuous (K.edgePathToCarrier e) := by
  apply Continuous.subtype_mk
  exact K.continuous_edgePath e

theorem edgePathToCarrier_injective (e : K.Edge) :
    Function.Injective (K.edgePathToCarrier e) := by
  intro r s hrs
  apply K.edgePath_injective e
  exact congrArg Subtype.val hrs

theorem edgePathToCarrier_surjective (e : K.Edge) :
    Function.Surjective (K.edgePathToCarrier e) := by
  rintro ⟨p, hp⟩
  rw [← K.range_edgePath e] at hp
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl⟩

/-- Every closed edge carrier is canonically homeomorphic to the unit interval. -/
noncomputable def edgePathHomeomorph [T2Space S] (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 ≃ₜ K.edgeCarrier e :=
  ((K.continuous_edgePathToCarrier e).isClosedEmbedding
    (K.edgePathToCarrier_injective e)).isEmbedding.toHomeomorphOfSurjective
      (K.edgePathToCarrier_surjective e)

@[simp] theorem edgePathHomeomorph_apply [T2Space S] (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePathHomeomorph e r).1 = K.edgePath e r := rfl

theorem edgePathHomeomorph_symm_val [T2Space S] (e : K.Edge)
    (p : K.edgeCarrier e) :
    K.edgePath e ((K.edgePathHomeomorph e).symm p) = p.1 := by
  exact congrArg Subtype.val ((K.edgePathHomeomorph e).apply_symm_apply p)

/-- The union of all edges not incident to a fixed vertex is closed. -/
theorem isClosed_iUnion_edgeCarrier_notMem [T2Space S] (v : K.Vertex) :
    IsClosed (⋃ e : {e : K.Edge // v ∉ e.1}, K.edgeCarrier e.1) := by
  apply (K.locallyFinite_edgeCarriers.comp_injective Subtype.val_injective).isClosed_iUnion
  intro e
  exact K.isClosed_edgeCarrier e.1

theorem vertexPoint_not_mem_iUnion_edgeCarrier_notMem (v : K.Vertex) :
    K.vertexPoint v ∉ ⋃ e : {e : K.Edge // v ∉ e.1}, K.edgeCarrier e.1 := by
  intro hv
  obtain ⟨e, hve⟩ := Set.mem_iUnion.mp hv
  exact e.2 ((K.vertexPoint_mem_edgeCarrier_iff v e.1).mp hve)

/-- Local finiteness on a compact ambient space makes the type of maximal faces finite. -/
@[implicit_reducible] noncomputable def faceFintype [CompactSpace S] : Fintype K.Face :=
  K.locallyFinite.fintypeOfCompact K.faceCarrier_nonempty

/-- If the face type is finite and every vertex is used, then the global vertex type is finite. -/
theorem finite_vertex [Finite K.Face] : Finite K.Vertex := by
  apply Finite.of_finite_univ
  have hrepr : (Set.univ : Set K.Vertex) = ⋃ f : K.Face, (K.faceVertices f : Set K.Vertex) := by
    ext v
    simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_coe, true_iff]
    exact K.vertex_used v
  rw [hrepr]
  exact Set.finite_iUnion fun f ↦ (K.faceVertices f).finite_toSet

/-- The finite vertex instance induced by compactness and the no-junk-vertices condition. -/
@[implicit_reducible] noncomputable def vertexFintype [CompactSpace S] : Fintype K.Vertex := by
  letI : Fintype K.Face := K.faceFintype
  letI : Finite K.Vertex := K.finite_vertex
  exact Fintype.ofFinite K.Vertex

/-- The `compactFaceFintype` declaration. -/
noncomputable local instance compactFaceFintype [CompactSpace S] : Fintype K.Face :=
  K.faceFintype

/-- The `compactVertexFintype` declaration. -/
noncomputable local instance compactVertexFintype [CompactSpace S] : Fintype K.Vertex :=
  K.vertexFintype

/-- The finite intrinsic complex obtained from a compact locally finite triangle complex. -/
noncomputable def compactIntrinsic [CompactSpace S] : IntrinsicTwoComplex := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  exact
    { Vertex := K.Vertex
      faces := Finset.univ.image K.faceVertices
      faces_card := by
        intro t ht
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp ht
        exact K.faceVertices_card f }

@[simp] theorem compactIntrinsic_faces [CompactSpace S] :
    K.compactIntrinsic.faces = by
      letI : Fintype K.Face := K.faceFintype
      exact Finset.univ.image K.faceVertices := rfl

theorem compactIntrinsic_face_mem [CompactSpace S] (f : K.Face) :
    K.faceVertices f ∈ K.compactIntrinsic.faces := by
  letI : Fintype K.Face := K.faceFintype
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

/-- Restrict a global standard-simplex point supported on `t` to the coordinates indexed by
`t`. -/
noncomputable def restrictToFace [Fintype K.Vertex] (t : Finset K.Vertex)
    (x : stdSimplex ℝ K.Vertex) (hx : ∀ v ∉ t, x v = 0) :
    stdSimplex ℝ {v // v ∈ t} := by
  refine ⟨fun v ↦ x v.1, fun v ↦ x.2.1 v.1, ?_⟩
  calc
    ∑ v : {v // v ∈ t}, x v.1 = ∑ v ∈ t, x v := by
      exact Finset.sum_coe_sort t fun v ↦ x v
    _ = ∑ v, x v := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro v _ hv
      exact hx v hv
    _ = 1 := x.2.2

theorem extendFaceCoordinates_restrictToFace [Fintype K.Vertex]
    (t : Finset K.Vertex) (x : stdSimplex ℝ K.Vertex)
    (hx : ∀ v ∉ t, x v = 0) :
    extendFaceCoordinates t (K.restrictToFace t x hx) = x := by
  funext v
  by_cases hv : v ∈ t
  · rw [extendFaceCoordinates_of_mem t _ hv]
    rfl
  · simp [extendFaceCoordinates, hv, hx v hv]

/-- Every point of the compact realization is supported on one of the original maximal faces. -/
theorem exists_containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) :
    ∃ f : K.Face, ∀ v ∉ K.faceVertices f, x.1 v = 0 := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  rcases x.2.2 with ⟨t, ht, hxt⟩
  obtain ⟨f, -, hft⟩ := Finset.mem_image.mp ht
  subst hft
  exact ⟨f, hxt⟩

/-- A canonical maximal face containing a point of the compact realization. -/
noncomputable def containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) : K.Face :=
  Classical.choose (K.exists_containingFace x)

theorem supported_on_containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) :
    ∀ v ∉ K.faceVertices (K.containingFace x), x.1 v = 0 := by
  exact Classical.choose_spec (K.exists_containingFace x)

/-- Evaluation of the compact barycentric realization through the locally finite face maps. -/
noncomputable def compactEval [CompactSpace S]
    (x : K.compactIntrinsic.realization) : S := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  exact K.faceMap (K.containingFace x)
    (K.restrictToFace _ ⟨x.1, x.2.1⟩ (K.supported_on_containingFace x))

theorem compactEval_eq_faceMap [CompactSpace S]
    (f : K.Face) (x : K.compactIntrinsic.realization)
    (hx : ∀ v ∉ K.faceVertices f, x.1 v = 0) :
    K.compactEval x =
      K.faceMap f (K.restrictToFace (K.faceVertices f) ⟨x.1, x.2.1⟩ hx) := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  apply K.faceMap_eq_iff.mpr
  rw [K.extendFaceCoordinates_restrictToFace,
    K.extendFaceCoordinates_restrictToFace]

private theorem continuous_faceRestriction [CompactSpace S] (f : K.Face) :
    Continuous fun x :
      {x : K.compactIntrinsic.realization //
        x ∈ K.compactIntrinsic.faceCarrier (K.faceVertices f)} ↦
      K.restrictToFace (K.faceVertices f) ⟨x.1.1, x.1.2.1⟩ x.2 := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  apply Continuous.subtype_mk
  have houter : Continuous fun x :
      {x : K.compactIntrinsic.realization //
        x ∈ K.compactIntrinsic.faceCarrier (K.faceVertices f)} ↦ x.1 :=
    continuous_subtype_val
  have hinner : Continuous fun x : K.compactIntrinsic.realization ↦ x.1 :=
    continuous_subtype_val
  exact continuous_pi fun v ↦ (continuous_apply v.1).comp (hinner.comp houter)

theorem continuous_compactEval [CompactSpace S] : Continuous K.compactEval := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  let carriers : K.Face → Set K.compactIntrinsic.realization :=
    fun f ↦ K.compactIntrinsic.faceCarrier (K.faceVertices f)
  have hclosed : ∀ f, IsClosed (carriers f) :=
    fun f ↦ K.compactIntrinsic.faceCarrier_closed (K.faceVertices f)
  have hcover : (Set.univ : Set K.compactIntrinsic.realization) = ⋃ f, carriers f := by
    rw [K.compactIntrinsic.realization_eq_iUnion_faceCarrier]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, hxt⟩
      obtain ⟨f, -, hft⟩ := Finset.mem_image.mp t.2
      refine ⟨f, ?_⟩
      simpa only [carriers, hft] using hxt
    · rintro ⟨f, hxf⟩
      exact ⟨⟨K.faceVertices f, K.compactIntrinsic_face_mem f⟩, hxf⟩
  have hlocal : ∀ f, ContinuousOn K.compactEval (carriers f) := by
    intro f
    rw [continuousOn_iff_continuous_restrict]
    have hc := (K.faceMap_continuous f).comp (K.continuous_faceRestriction f)
    convert hc using 1
    funext x
    exact K.compactEval_eq_faceMap f x.1 x.2
  exact (locallyFinite_of_finite carriers).continuous hcover.symm hclosed hlocal

theorem injective_compactEval [CompactSpace S] : Function.Injective K.compactEval := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  intro x y hxy
  have hcoeff := K.faceMap_eq_iff.mp hxy
  rw [K.extendFaceCoordinates_restrictToFace,
    K.extendFaceCoordinates_restrictToFace] at hcoeff
  exact Subtype.ext hcoeff

/-- The compact evaluation has exactly the ambient support of the locally finite complex as its
range. -/
theorem range_compactEval [CompactSpace S] : Set.range K.compactEval = K.support := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    refine Set.mem_iUnion.mpr ⟨K.containingFace x, ?_⟩
    exact ⟨K.restrictToFace _ ⟨x.1, x.2.1⟩ (K.supported_on_containingFace x), rfl⟩
  · intro y hy
    obtain ⟨f, z, rfl⟩ := Set.mem_iUnion.mp hy
    let x0 : stdSimplex ℝ K.Vertex := stdSimplex.map Subtype.val z
    have hxSupport : ∀ v ∉ K.faceVertices f, x0 v = 0 := by
      intro v hv
      simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      have hempty :
          Finset.univ.filter (fun w : {w // w ∈ K.faceVertices f} ↦ w.1 = v) = ∅ := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun hw ↦ hv (hw ▸ w.2)
      rw [hempty]
      simp
    let x : K.compactIntrinsic.realization :=
      ⟨x0, x0.2, ⟨K.faceVertices f, K.compactIntrinsic_face_mem f, hxSupport⟩⟩
    refine ⟨x, ?_⟩
    rw [K.compactEval_eq_faceMap f x hxSupport]
    apply congrArg (K.faceMap f)
    ext w
    change x0 w.1 = z w
    simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter :
        Finset.univ.filter
          (fun q : {q // q ∈ K.faceVertices f} ↦ q.1 = w.1) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact Subtype.ext_iff.symm
    rw [hfilter]
    simp

/-- A locally finite triangle complex covering a compact Hausdorff space is an honest finite
geometric triangulation. -/
noncomputable def toGeometricTriangulation [CompactSpace S] [T2Space S]
    (hcovers : K.support = Set.univ) : GeometricTriangulation S := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  let e : K.compactIntrinsic.realization ≃ S :=
    Equiv.ofBijective K.compactEval ⟨K.injective_compactEval, by
      intro y
      have hy : y ∈ K.support := by rw [hcovers]; exact Set.mem_univ y
      rw [← K.range_compactEval] at hy
      exact hy⟩
  exact
    { Vertex := K.compactIntrinsic.Vertex
      faces := K.compactIntrinsic.faces
      faces_card := K.compactIntrinsic.faces_card
      homeo := Continuous.homeoOfEquivCompactToT2 (f := e) K.continuous_compactEval }

/-! ## Finite complexes on their own support -/

/-- Regard a finite ambient triangle complex as a complex whose ambient space is exactly its
support.  This is the finite gluing bridge used in the Rado induction: once a compatible finite
family of old and new triangles has been assembled, no separate ambient coverage proof is
needed. -/
noncomputable def onSupport [Finite K.Face] :
    LocallyFiniteTriangleComplex K.support where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := K.faceVertices
  faceVertices_card := K.faceVertices_card
  vertex_used := K.vertex_used
  faceMap := fun f x => ⟨K.faceMap f x,
    Set.mem_iUnion.mpr ⟨f, Set.mem_range_self x⟩⟩
  faceMap_continuous := fun f => by
    apply Continuous.subtype_mk
    exact K.faceMap_continuous f
  faceMap_eq_iff := by
    intro f g x y
    rw [Subtype.ext_iff]
    exact K.faceMap_eq_iff
  locallyFinite := locallyFinite_of_finite _

@[simp] theorem onSupport_faceVertices [Finite K.Face] (f : K.Face) :
    K.onSupport.faceVertices f = K.faceVertices f := rfl

@[simp] theorem onSupport_faceMap_val [Finite K.Face] (f : K.Face)
    (x : stdSimplex ℝ {v // v ∈ K.faceVertices f}) :
    (K.onSupport.faceMap f x).1 = K.faceMap f x := rfl

/-- The support-restricted complex covers its ambient support subtype. -/
theorem onSupport_support [Finite K.Face] : K.onSupport.support = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨p, hp⟩
  obtain ⟨f, hpf⟩ := Set.mem_iUnion.mp hp
  obtain ⟨x, rfl⟩ := hpf
  exact Set.mem_iUnion.mpr ⟨f, ⟨x, rfl⟩⟩

/-- A finite ambient triangle complex has compact support, independently of compactness of the
ambient space. -/
theorem isCompact_support_of_finite [Finite K.Face] : IsCompact K.support := by
  letI : Fintype K.Face := Fintype.ofFinite K.Face
  exact isCompact_iUnion fun f => K.isCompact_faceCarrier f

/-- A finite compatible triangle family triangulates its own support. -/
noncomputable def finiteSupportGeometricTriangulation [Finite K.Face] [T2Space S] :
    GeometricTriangulation K.support := by
  letI : CompactSpace K.support :=
    isCompact_iff_compactSpace.mp K.isCompact_support_of_finite
  exact K.onSupport.toGeometricTriangulation K.onSupport_support

end LocallyFiniteTriangleComplex

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- Include the standard simplex on one maximal face into the global barycentric realization. -/
noncomputable def faceStandardMap (t : K.Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) : K.realization := by
  let x0 : stdSimplex ℝ K.Vertex := stdSimplex.map Subtype.val x
  have hxSupport : ∀ v ∉ t.1, x0 v = 0 := by
    intro v hv
    simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty :
        Finset.univ.filter (fun w : {w // w ∈ t.1} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp
  exact ⟨x0, x0.2, ⟨t.1, t.2, hxSupport⟩⟩

/-- Restrict an intrinsic realization point supported on one maximal face to that face's
standard simplex. -/
noncomputable def restrictToFaceSimplex (t : K.Face) (x : K.realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    stdSimplex ℝ {v // v ∈ t.1} := by
  refine ⟨fun v ↦ x.1 v.1, fun v ↦ x.2.1.1 v.1, ?_⟩
  calc
    ∑ v : {v // v ∈ t.1}, x.1 v.1 = ∑ v ∈ t.1, x.1 v := by
      exact Finset.sum_coe_sort t.1 fun v ↦ x.1 v
    _ = ∑ v, x.1 v := by
      apply Finset.sum_subset (Finset.subset_univ t.1)
      intro v _ hv
      exact hx v hv
    _ = 1 := x.2.1.2

theorem faceStandardMap_val (t : K.Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) :
    (K.faceStandardMap t x).1 = extendFaceCoordinates t.1 x := by
  funext v
  by_cases hv : v ∈ t.1
  · let w : {w // w ∈ t.1} := ⟨v, hv⟩
    change (stdSimplex.map Subtype.val x : K.Vertex → ℝ) v = _
    rw [extendFaceCoordinates_of_mem t.1 x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter :
        Finset.univ.filter (fun q : {q // q ∈ t.1} ↦ q.1 = v) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ Subtype.ext h
      · exact fun h ↦ congrArg Subtype.val h
    rw [hfilter]
    simp [w]
  · change (stdSimplex.map Subtype.val x : K.Vertex → ℝ) v = _
    rw [extendFaceCoordinates_of_notMem t.1 x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty :
        Finset.univ.filter (fun w : {w // w ∈ t.1} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp

theorem faceStandardMap_restrictToFaceSimplex (t : K.Face) (x : K.realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    K.faceStandardMap t (K.restrictToFaceSimplex t x hx) = x := by
  apply Subtype.ext
  rw [K.faceStandardMap_val]
  funext v
  by_cases hv : v ∈ t.1
  · rw [extendFaceCoordinates_of_mem _ _ hv]
    rfl
  · rw [extendFaceCoordinates_of_notMem _ _ hv, hx v hv]

theorem continuous_faceStandardMap (t : K.Face) : Continuous (K.faceStandardMap t) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (stdSimplex.continuous_map Subtype.val)

/-- Regard a finite intrinsic complex with no unused vertices as a locally finite ambient
triangle complex. -/
noncomputable def toLocallyFiniteTriangleComplex {S : Type*} [TopologicalSpace S]
    (hused : ∀ v : K.Vertex, ∃ t ∈ K.faces, v ∈ t)
    (e : K.realization → S) (he : _root_.Topology.IsEmbedding e) :
    LocallyFiniteTriangleComplex S where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := fun t ↦ t.1
  faceVertices_card := fun t ↦ K.faces_card t.1 t.2
  vertex_used := by
    intro v
    obtain ⟨t, ht, hvt⟩ := hused v
    exact ⟨⟨t, ht⟩, hvt⟩
  faceMap := fun t x ↦ e (K.faceStandardMap t x)
  faceMap_continuous := fun t ↦ he.continuous.comp (K.continuous_faceStandardMap t)
  faceMap_eq_iff := by
    intro f g x y
    constructor
    · intro hxy
      have hsource : K.faceStandardMap f x = K.faceStandardMap g y := he.injective hxy
      rw [← K.faceStandardMap_val f x, ← K.faceStandardMap_val g y]
      exact congrArg Subtype.val hsource
    · intro hxy
      apply congrArg e
      apply Subtype.ext
      simpa only [K.faceStandardMap_val] using hxy
  locallyFinite := locallyFinite_of_finite _

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification04_block_04
/- END ClassificationOfSurfaces.Moise.LocallyFiniteTriangulation -/

/- BEGIN ClassificationOfSurfaces.Moise.PolygonalPolyhedron | a30f6b0a00059ea2a5e606249b5a965bd34ecfc285853c6df4502caed07e1a13 -/
section schottkyclassification04_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal Jordan regions as finite plane complexes

This file formalizes Moise Chapter 2, Theorem 2.  The finitely many affine lines containing the
edges of a polygon cut an enclosing triangle into a finite triangle mesh.  The triangles on the
bounded side of polygonal Jordan form the required finite complex.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- The linear functional whose zero set is parallel to the vector from `p` to `q`. -/
noncomputable def edgeNormalLinear (p q : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := (q - p) 0 * x 1 - (q - p) 1 * x 0
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- An affine equation for the line containing polygon edge `i`. -/
noncomputable def edgeLine (i : ZMod J.n) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x => edgeNormalLinear (J.vertex i) (J.vertex (i + 1))
      (x - J.vertex i))
    (edgeNormalLinear (J.vertex i) (J.vertex (i + 1))) (J.vertex i) (by
      intro x
      simp)

@[simp] theorem edgeLine_initial (i : ZMod J.n) :
    J.edgeLine i (J.vertex i) = 0 := by
  simp [edgeLine]

@[simp] theorem edgeLine_terminal (i : ZMod J.n) :
    J.edgeLine i (J.vertex (i + 1)) = 0 := by
  simp [edgeLine, edgeNormalLinear]
  ring

theorem edgeLine_eq_zero_of_mem_edgeSegment (i : ZMod J.n) {x : Plane}
    (hx : x ∈ J.edgeSegment i) : J.edgeLine i x = 0 := by
  rw [edgeSegment, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp [edgeLine, edgeNormalLinear]
  ring

theorem edgeLine_surjective (i : ZMod J.n) : Function.Surjective (J.edgeLine i) := by
  let dx : ℝ := (J.vertex (i + 1) - J.vertex i) 0
  let dy : ℝ := (J.vertex (i + 1) - J.vertex i) 1
  have hxy : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    push Not at h
    apply J.adjacent_ne i
    ext j
    fin_cases j
    · exact (sub_eq_zero.mp (by simpa [dx, PiLp.sub_apply] using h.1)).symm
    · exact (sub_eq_zero.mp (by simpa [dy, PiLp.sub_apply] using h.2)).symm
  have hden : dx ^ 2 + dy ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  intro y
  refine ⟨J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx, ?_⟩
  change (J.vertex (i + 1) - J.vertex i) 0 *
      (J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - J.vertex i) 1 -
      (J.vertex (i + 1) - J.vertex i) 1 *
      (J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - J.vertex i) 0 = y
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, planePoint_apply_zero,
    planePoint_apply_one, smul_eq_mul]
  ring_nf
  field_simp [hden]
  dsimp [dx, dy]
  ring_nf

theorem interior_edgeLine_nonneg (i : ZMod J.n) :
    interior {x | 0 ≤ J.edgeLine i x} = {x | 0 < J.edgeLine i x} := by
  let f := J.edgeLine i
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (J.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

theorem interior_edgeLine_nonpos (i : ZMod J.n) :
    interior {x | J.edgeLine i x ≤ 0} = {x | J.edgeLine i x < 0} := by
  let f := J.edgeLine i
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (J.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

/-- The finite list of supporting lines used in Moise's arrangement proof. -/
noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (ZMod J.n)).toList.map J.edgeLine

theorem edgeLine_mem_edgeLines (i : ZMod J.n) : J.edgeLine i ∈ J.edgeLines := by
  simp [edgeLines]

/-- A positive radius of a closed ball containing the closed polygonal region. -/
noncomputable def enclosingRadius : ℝ :=
  max (J.isCompact_closedRegion.isBounded.subset_closedBall (0 : Plane)).choose 1

theorem enclosingRadius_pos : 0 < J.enclosingRadius := by
  unfold enclosingRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem closedRegion_subset_enclosingBall :
    J.closedRegion ⊆ Metric.closedBall (0 : Plane) J.enclosingRadius := by
  intro x hx
  have h := (J.isCompact_closedRegion.isBounded.subset_closedBall (0 : Plane)).choose_spec hx
  rw [Metric.mem_closedBall] at h ⊢
  exact h.trans (le_max_left _ _)

/-- Vertices of a large triangle containing the ball of radius `R`. -/
def enclosingTriangleVertices (R : ℝ) : Fin 3 → Plane :=
  ![planePoint (-3 * R) (-2 * R), planePoint (3 * R) (-2 * R), planePoint 0 (4 * R)]

theorem enclosingTriangleVertices_affineIndependent {R : ℝ} (hR : 0 < R) :
    AffineIndependent ℝ (enclosingTriangleVertices R) := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem closedBall_subset_enclosingTriangle {R : ℝ} (hR : 0 < R) :
    Metric.closedBall (0 : Plane) R ⊆
      convexHull ℝ (Set.range (enclosingTriangleVertices R)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hx0 := PiLp.norm_apply_le (p := 2) x (0 : Fin 2)
  have hx1 := PiLp.norm_apply_le (p := 2) x (1 : Fin 2)
  simp only [Real.norm_eq_abs] at hx0 hx1
  have hx0lo : -R ≤ x 0 := by linarith [neg_abs_le (x 0)]
  have hx0hi : x 0 ≤ R := by linarith [le_abs_self (x 0)]
  have hx1lo : -R ≤ x 1 := by linarith [neg_abs_le (x 1)]
  have hx1hi : x 1 ≤ R := by linarith [le_abs_self (x 1)]
  let w : Fin 3 → ℝ :=
    ![(4 * R - x 1 - 2 * x 0) / (12 * R),
      (4 * R - x 1 + 2 * x 0) / (12 * R),
      (x 1 + 2 * R) / (6 * R)]
  apply mem_convexHull_range_fin3_of_weights _ x w
  · intro i
    fin_cases i
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
  · change (4 * R - x 1 - 2 * x 0) / (12 * R) +
        (4 * R - x 1 + 2 * x 0) / (12 * R) +
        (x 1 + 2 * R) / (6 * R) = 1
    field_simp [hR.ne']
    ring
  · ext i
    fin_cases i <;> simp [w, enclosingTriangleVertices, planePoint]
    all_goals field_simp [hR.ne']; ring

/-- The one-triangle seed mesh in which the supporting-line arrangement is constructed. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (enclosingTriangleVertices J.enclosingRadius)
    (enclosingTriangleVertices_affineIndependent J.enclosingRadius_pos)

theorem closedRegion_subset_enclosingMesh_support :
    J.closedRegion ⊆ J.enclosingMesh.toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact J.closedRegion_subset_enclosingBall.trans
    (closedBall_subset_enclosingTriangle J.enclosingRadius_pos)

/-- The finite mesh obtained by cutting the enclosing triangle along every polygon edge line. -/
noncomputable def arrangementMesh : TriangleMesh :=
  J.enclosingMesh.refineByLines J.edgeLines

theorem arrangementMesh_support :
    J.arrangementMesh.toPlaneComplex.support = J.enclosingMesh.toPlaneComplex.support :=
  J.enclosingMesh.refineByLines_support J.edgeLines

theorem arrangementMesh_isMonochromatic (i : ZMod J.n) :
    J.arrangementMesh.IsMonochromatic (J.edgeLine i) :=
  J.enclosingMesh.refineByLines_isMonochromatic_of_mem J.edgeLines (J.edgeLine_mem_edgeLines i)

theorem closedRegion_subset_arrangementMesh_support :
    J.closedRegion ⊆ J.arrangementMesh.toPlaneComplex.support := by
  rw [J.arrangementMesh_support]
  exact J.closedRegion_subset_enclosingMesh_support

/-- Carrier of one maximal triangle in the supporting-line arrangement. -/
noncomputable def arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) : Set Plane :=
  convexHull ℝ (J.arrangementMesh.position '' (t : Set _))

theorem convex_arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) :
    Convex ℝ (J.arrangementTriangleCarrier t) :=
  convex_convexHull ℝ _

theorem isClosed_arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) :
    IsClosed (J.arrangementTriangleCarrier t) :=
  (t.finite_toSet.image J.arrangementMesh.position).isClosed_convexHull ℝ

theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    (interior (J.arrangementTriangleCarrier t)).Nonempty := by
  apply (J.convex_arrangementTriangleCarrier t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t => J.arrangementMesh.position v) =
      J.arrangementMesh.position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  have hAI := J.arrangementMesh.affineIndependent_triangle t ht
  apply hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, J.arrangementMesh.card_triangle t ht]
  simp [Plane]

theorem closure_interior_arrangementTriangleCarrier
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    closure (interior (J.arrangementTriangleCarrier t)) = J.arrangementTriangleCarrier t := by
  calc
    closure (interior (J.arrangementTriangleCarrier t)) =
        closure (J.arrangementTriangleCarrier t) :=
      (J.convex_arrangementTriangleCarrier t).closure_interior_eq_closure_of_nonempty_interior
        (J.arrangementTriangleCarrier_interior_nonempty ht)
    _ = J.arrangementTriangleCarrier t := (J.isClosed_arrangementTriangleCarrier t).closure_eq

/-- Every open triangle chamber of the supporting-line arrangement misses the polygon. -/
theorem arrangementTriangle_interior_disjoint_carrier
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    Disjoint
      (interior (J.arrangementTriangleCarrier t))
      J.carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : J.edgeLine i x = 0 := J.edgeLine_eq_zero_of_mem_edgeSegment i hxi
  rcases J.arrangementMesh_isMonochromatic i t ht with hpos | hneg
  · have hsubset : J.arrangementTriangleCarrier t ⊆
        {y | 0 ≤ J.edgeLine i y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage (J.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [J.interior_edgeLine_nonneg i] at hxstrict
    change 0 < J.edgeLine i x at hxstrict
    linarith
  · have hsubset : J.arrangementTriangleCarrier t ⊆
        {y | J.edgeLine i y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage (J.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [J.interior_edgeLine_nonpos i] at hxstrict
    change J.edgeLine i x < 0 at hxstrict
    linarith

theorem arrangementTriangle_interior_side
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    interior (J.arrangementTriangleCarrier t) ⊆ J.interiorRegion ∨
      interior (J.arrangementTriangleCarrier t) ⊆ J.exteriorRegion := by
  let s := interior (J.arrangementTriangleCarrier t)
  have hsconn : IsPreconnected s :=
    (J.convex_arrangementTriangleCarrier t).interior.isPreconnected
  have hscarrier : s ⊆ J.carrierᶜ := by
    intro x hx
    exact Set.disjoint_left.mp (J.arrangementTriangle_interior_disjoint_carrier ht) hx
  have hsunion : s ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    rw [J.interior_union_exterior]
    exact hscarrier
  obtain ⟨x, hx⟩ := J.arrangementTriangleCarrier_interior_nonempty ht
  have hxside := hsunion hx
  rcases hxside with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union J.isOpen_interiorRegion
      J.isOpen_exteriorRegion J.disjoint_interior_exterior hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union J.isOpen_interiorRegion
      J.isOpen_exteriorRegion J.disjoint_interior_exterior hsunion ⟨x, hx, hxout⟩

/-- The arrangement chambers lying on the bounded side of the polygon. -/
def IsInteriorArrangementTriangle (t : Finset J.arrangementMesh.Vertex) : Prop :=
  interior (J.arrangementTriangleCarrier t) ⊆ J.interiorRegion

/-- The finite mesh formed by all bounded-side arrangement chambers. -/
noncomputable def closedRegionMesh : TriangleMesh :=
  by
    classical
    exact J.arrangementMesh.restrictTriangles J.IsInteriorArrangementTriangle

theorem closedRegionMesh_triangle_mem {t : Finset J.closedRegionMesh.Vertex} :
    t ∈ J.closedRegionMesh.triangles ↔
      t ∈ J.arrangementMesh.triangles ∧ J.IsInteriorArrangementTriangle t := by
  classical
  exact J.arrangementMesh.mem_restrictTriangles_triangles J.IsInteriorArrangementTriangle

theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles)
    (hinside : J.IsInteriorArrangementTriangle t) :
    J.arrangementTriangleCarrier t ⊆ J.closedRegion := by
  rw [← J.closure_interior_arrangementTriangleCarrier ht, closedRegion]
  exact closure_mono hinside

theorem closedRegionMesh_support_subset :
    J.closedRegionMesh.toPlaneComplex.support ⊆ J.closedRegion := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := J.closedRegionMesh_triangle_mem.mp ht
  exact J.arrangementTriangleCarrier_subset_closedRegion htarr htinside hxt

theorem interiorRegion_subset_closedRegionMesh_support :
    J.interiorRegion ⊆ J.closedRegionMesh.toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ J.closedRegion := by
    rw [J.closedRegion_eq_union]
    exact Or.inl hxinside
  have hxsupport := J.closedRegion_subset_arrangementMesh_support hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (J.arrangementTriangleCarrier t)) := by
    rw [J.closure_interior_arrangementTriangleCarrier ht]
    exact hxt
  have hxclosureInter :
      x ∈ closure (J.interiorRegion ∩ interior (J.arrangementTriangleCarrier t)) :=
    J.isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  have hmeet' :
      (J.interiorRegion ∩ interior (J.arrangementTriangleCarrier t)).Nonempty :=
    Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have hmeet :
      (interior (J.arrangementTriangleCarrier t) ∩ J.interiorRegion).Nonempty := by
    obtain ⟨y, hyinside, hyt⟩ := hmeet'
    exact ⟨y, hyt, hyinside⟩
  have htinside : J.IsInteriorArrangementTriangle t := by
    rcases J.arrangementTriangle_interior_side ht with hin | hout
    · exact hin
    · obtain ⟨y, hyt, hyinside⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp J.disjoint_interior_exterior hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, J.closedRegionMesh_triangle_mem.mpr ⟨ht, htinside⟩, hxt⟩

theorem closedRegionMesh_support :
    J.closedRegionMesh.toPlaneComplex.support = J.closedRegion := by
  apply Set.Subset.antisymm J.closedRegionMesh_support_subset
  rw [closedRegion]
  exact closure_minimal
    J.interiorRegion_subset_closedRegionMesh_support
    J.closedRegionMesh.toPlaneComplex.isCompact_support.isClosed

theorem disjoint_carrier_exteriorRegion : Disjoint J.carrier J.exteriorRegion := by
  rw [Set.disjoint_left]
  intro x hxcarrier hxexterior
  have hxcompl : x ∈ J.carrierᶜ := by
    rw [← J.interior_union_exterior]
    exact Or.inr hxexterior
  exact hxcompl hxcarrier

theorem disjoint_closedRegion_exteriorRegion : Disjoint J.closedRegion J.exteriorRegion := by
  rw [J.closedRegion_eq_union]
  exact J.disjoint_interior_exterior.sup_left J.disjoint_carrier_exteriorRegion

/-- The topological boundary of the closed polygonal disk is the original polygon. -/
theorem frontier_closedRegion : frontier J.closedRegion = J.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxclosed : x ∈ J.closedRegion := by
      have hx' := frontier_subset_closure hx
      simpa [J.isCompact_closedRegion.isClosed.closure_eq] using hx'
    rw [J.closedRegion_eq_union] at hxclosed
    rcases hxclosed with hxinside | hxcarrier
    · have hxint : x ∈ interior J.closedRegion :=
        interior_maximal (by rw [J.closedRegion_eq_union]; exact Set.subset_union_left)
          J.isOpen_interiorRegion hxinside
      exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier hxint hx
    · exact hxcarrier
  · intro x hxcarrier
    have hxclosed : x ∈ J.closedRegion := by
      rw [J.closedRegion_eq_union]
      exact Or.inr hxcarrier
    rw [J.isCompact_closedRegion.isClosed.frontier_eq]
    refine ⟨hxclosed, ?_⟩
    intro hxint
    have hxclosureExterior : x ∈ closure J.exteriorRegion :=
      frontier_subset_closure (J.frontier_exteriorRegion.symm ▸ hxcarrier)
    have hxclosureInter :
        x ∈ closure (interior J.closedRegion ∩ J.exteriorRegion) :=
      isOpen_interior.inter_closure ⟨hxint, hxclosureExterior⟩
    obtain ⟨y, hyint, hyexterior⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
    exact Set.disjoint_left.mp J.disjoint_closedRegion_exteriorRegion
      (interior_subset hyint) hyexterior

theorem interior_closedRegion : interior J.closedRegion = J.interiorRegion := by
  apply Set.Subset.antisymm
  · intro p hp
    have hpClosed : p ∈ J.closedRegion := interior_subset hp
    rw [J.closedRegion_eq_union] at hpClosed
    rcases hpClosed with hpInside | hpCarrier
    · exact hpInside
    · have hpFrontier : p ∈ frontier J.closedRegion := by
        rw [J.frontier_closedRegion]
        exact hpCarrier
      exact (Set.disjoint_left.mp disjoint_interior_frontier hp hpFrontier).elim
  · exact interior_maximal (by rw [J.closedRegion_eq_union]; exact Set.subset_union_left)
      J.isOpen_interiorRegion

theorem isConnected_closedRegion : IsConnected J.closedRegion := by
  rw [closedRegion]
  exact J.isConnected_interiorRegion.closure

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification04_block_05
/- END ClassificationOfSurfaces.Moise.PolygonalPolyhedron -/
