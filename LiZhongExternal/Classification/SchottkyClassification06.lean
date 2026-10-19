/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification06: pinned classification sources (upstream e3c7230f); see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification04
import LiZhongExternal.Classification.SchottkyClassification05

/- BEGIN ClassificationOfSurfaces.Moise.ThinKiteMove | d3158c14887c58cbc791c72aaaf4d9d53bfa57a43270853f36f71da2e75c59e7 -/
section schottkyclassification06_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Transporting the elementary move to a thin kite

The fixed diamond used to prove the barycentric fan move is too large for the relative
Schoenflies induction.  This file transports it piecewise-affinely to a kite whose lower and
upper margins are an arbitrary positive `δ`.  The two halves of the outer kite form a
two-triangle mesh, so the transport is supplied by the canonical realization homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Left, right, top, and bottom vertices of an axis-aligned kite. -/
def axisKitePosition (lo hi : ℝ) : Fin 4 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 hi, planePoint 0 lo]

@[simp] theorem axisKitePosition_zero (lo hi : ℝ) :
    axisKitePosition lo hi 0 = planePoint (-1) 0 := rfl

@[simp] theorem axisKitePosition_one (lo hi : ℝ) :
    axisKitePosition lo hi 1 = planePoint 1 0 := rfl

@[simp] theorem axisKitePosition_two (lo hi : ℝ) :
    axisKitePosition lo hi 2 = planePoint 0 hi := rfl

@[simp] theorem axisKitePosition_three (lo hi : ℝ) :
    axisKitePosition lo hi 3 = planePoint 0 lo := rfl

/-- The `axisKiteTriangles` declaration. -/
def axisKiteTriangles : Finset (Finset (Fin 4)) :=
  {{0, 2, 3}, {1, 2, 3}}

/-- The `axisKitePatch` declaration. -/
def axisKitePatch (lo hi : ℝ) : Set Plane :=
  convexHull ℝ (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
    convexHull ℝ (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _))

private theorem affineIndependent_finset_of_range_kite {V : Type}
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

theorem axisKitePosition_injective {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi) :
    Function.Injective (axisKitePosition lo hi) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [axisKitePosition, planePoint] at hij ⊢
  all_goals linarith

theorem axisKite_affineIndependent {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    {t : Finset (Fin 4)} (ht : t ∈ axisKiteTriangles) :
    AffineIndependent ℝ fun v : t => axisKitePosition lo hi v := by
  simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · apply affineIndependent_finset_of_range_kite (axisKitePosition lo hi) ![0, 2, 3]
    · have h : AffineIndependent ℝ ![axisKitePosition lo hi 0,
          axisKitePosition lo hi 2, axisKitePosition lo hi 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [axisKitePosition_zero, axisKitePosition_two, axisKitePosition_three,
          planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range_kite (axisKitePosition lo hi) ![1, 2, 3]
    · have h : AffineIndependent ℝ ![axisKitePosition lo hi 1,
          axisKitePosition lo hi 2, axisKitePosition lo hi 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [axisKitePosition_one, axisKitePosition_two, axisKitePosition_three,
          planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp

theorem axisKite_inter {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi) :
    convexHull ℝ (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∩
        convexHull ℝ (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
      convexHull ℝ (axisKitePosition lo hi ''
        ((({0, 2, 3} : Finset (Fin 4)) ∩ {1, 2, 3} : Finset (Fin 4)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (axisKitePosition lo hi)
    (axisKitePosition_injective hlo hhi) {0, 2, 3} {1, 2, 3} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp [axisKitePosition] at hv ⊢

/-- The `axisKiteMesh` declaration. -/
noncomputable def axisKiteMesh (lo hi : ℝ) (hlo : lo < 0) (hhi : 0 < hi) : TriangleMesh where
  Vertex := Fin 4
  position := axisKitePosition lo hi
  position_injective := axisKitePosition_injective hlo hhi
  triangles := axisKiteTriangles
  card_triangle := by
    intro t ht
    simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide
  affineIndependent_triangle := fun t ht => axisKite_affineIndependent hlo hhi ht
  triangle_inter := by
    intro s hs t ht
    simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simp
    · exact axisKite_inter hlo hhi
    · simpa [Set.inter_comm, Finset.inter_comm] using axisKite_inter hlo hhi
    · simp

theorem axisKiteMesh_support (lo hi : ℝ) (hlo : lo < 0) (hhi : 0 < hi) :
    (axisKiteMesh lo hi hlo hhi).toPlaneComplex.support = axisKitePatch lo hi := by
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [axisKiteMesh]
  change (⋃ t ∈ axisKiteTriangles,
    convexHull ℝ (axisKitePosition lo hi '' (t : Set (Fin 4)))) = _
  ext p
  simp [axisKiteTriangles, axisKitePatch]

theorem axisKitePatch_negTwo_two : axisKitePatch (-2) 2 = diamondPatch := by
  unfold axisKitePatch diamondPatch diamondLeftRegion diamondRightRegion
  congr 1 <;> apply congrArg (convexHull ℝ) <;> ext p <;>
    simp [axisKitePosition] <;> tauto

/-- Vertical scale used to compress the fixed diamond to a kite with margins `δ`. -/
noncomputable def thinKiteScale (δ : ℝ) : ℝ := (1 + 2 * δ) / 4

/-- The global piecewise-affine transport.  Writing the two affine pieces with `|x|` makes
continuity across the vertical diagonal immediate. -/
noncomputable def thinKiteMap (δ : ℝ) (p : Plane) : Plane :=
  planePoint (p 0) (thinKiteScale δ * p 1 + (1 - |p 0|) / 2)

/-- The `thinKiteInv` declaration. -/
noncomputable def thinKiteInv (δ : ℝ) (p : Plane) : Plane :=
  planePoint (p 0) ((p 1 - (1 - |p 0|) / 2) / thinKiteScale δ)

theorem thinKiteScale_pos {δ : ℝ} (hδ : 0 < δ) : 0 < thinKiteScale δ := by
  unfold thinKiteScale
  positivity

/-- The `thinKiteGlobalHomeomorph` declaration. -/
noncomputable def thinKiteGlobalHomeomorph (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane := by
  have hs : thinKiteScale δ ≠ 0 := (thinKiteScale_pos hδ).ne'
  have hleft : Function.LeftInverse (thinKiteInv δ) (thinKiteMap δ) := by
    intro p
    ext i
    fin_cases i
    · simp [thinKiteMap, thinKiteInv]
    · simp [thinKiteMap, thinKiteInv]
      field_simp [hs]
  have hright : Function.RightInverse (thinKiteInv δ) (thinKiteMap δ) := by
    intro p
    ext i
    fin_cases i
    · simp [thinKiteMap, thinKiteInv]
    · simp [thinKiteMap, thinKiteInv]
      field_simp [hs]
      ring
  exact
    { toEquiv := Equiv.mk (thinKiteMap δ) (thinKiteInv δ) hleft hright
      continuous_toFun := by
        unfold thinKiteMap thinKiteScale planePoint
        fun_prop
      continuous_invFun := by
        unfold thinKiteInv thinKiteScale planePoint
        fun_prop }

/-- The thin kite is the image of the fixed diamond under the explicit transport. -/
noncomputable def thinKitePatch (δ : ℝ) : Set Plane := thinKiteMap δ '' diamondPatch

/-- Every point of the thin kite lies in the tangent cone at its left base vertex. -/
theorem thinKitePatch_subset_leftCone {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane}
    (hp : p ∈ thinKitePatch δ) :
    0 ≤ p 0 + 1 ∧ -δ * (p 0 + 1) ≤ p 1 ∧ p 1 ≤ (1 + δ) * (p 0 + 1) := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  have hs : thinKiteScale δ = (1 + 2 * δ) / 4 := rfl
  constructor
  · simp only [thinKiteMap, planePoint_apply_zero]
    linarith
  · constructor
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith

/-- Every point of the thin kite lies in the tangent cone at its right base vertex. -/
theorem thinKitePatch_subset_rightCone {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane}
    (hp : p ∈ thinKitePatch δ) :
    0 ≤ 1 - p 0 ∧ -δ * (1 - p 0) ≤ p 1 ∧ p 1 ≤ (1 + δ) * (1 - p 0) := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  have hs : thinKiteScale δ = (1 + 2 * δ) / 4 := rfl
  constructor
  · simp only [thinKiteMap, planePoint_apply_zero]
    linarith
  · constructor
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith

/-- The triangle onto which the thin kite collapses when `δ = 0`. -/
def kiteTrianglePosition : Fin 3 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 1]

theorem kiteTrianglePosition_affineIndependent :
    AffineIndependent ℝ kiteTrianglePosition := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [kiteTrianglePosition, planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]

/-- A ray from the left base vertex whose coordinate direction lies in the original triangle
cone enters the triangle immediately. -/
theorem exists_leftBase_openSegment_mem_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint (-1) 0) (hx : 0 < q 0 + 1)
    (hy0 : 0 ≤ q 1) (hyx : q 1 ≤ q 0 + 1) :
    ∃ p ∈ segment ℝ (planePoint (-1) 0) q \ {planePoint (-1) 0},
      p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  let dx := q 0 + 1
  let dy := q 1
  let t : ℝ := 1 / (1 + dx + dy)
  have hden : 0 < 1 + dx + dy := by dsimp [dx, dy]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hden]
    dsimp [dx, dy]
    linarith
  let p := AffineMap.lineMap (planePoint (-1) 0) q t
  have hpSegment : p ∈ segment ℝ (planePoint (-1) 0) q := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hpNe : p ≠ planePoint (-1) 0 := by
    intro hp
    have hinj := AffineMap.lineMap_injective ℝ hq.symm
    apply ht.ne'
    apply hinj
    dsimp [p] at hp
    simpa using hp
  let w : Fin 3 → ℝ :=
    ![1 - t * (dx + dy) / 2, t * (dx - dy) / 2, t * dy]
  have hpTriangle : p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition p w
    · intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sub_nonneg, w,
                        Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
      · have htd : t * (dx + dy) < 1 := by
          dsimp [t]
          field_simp
          nlinarith
        linarith
      · nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hyx)]
      · exact mul_nonneg ht.le hy0
    · simp [w]
      ring
    · ext i
      fin_cases i <;>
        simp [w, p, kiteTrianglePosition, AffineMap.lineMap_apply_module,
          planePoint, dx, dy]
      all_goals ring
  exact ⟨p, ⟨hpSegment, by simpa using hpNe⟩, hpTriangle⟩

/-- A ray from the right base vertex whose direction lies in the original triangle cone enters
the triangle immediately. -/
theorem exists_rightBase_openSegment_mem_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint 1 0) (hx : 0 < 1 - q 0)
    (hy0 : 0 ≤ q 1) (hyx : q 1 ≤ 1 - q 0) :
    ∃ p ∈ segment ℝ (planePoint 1 0) q \ {planePoint 1 0},
      p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  let dx := 1 - q 0
  let dy := q 1
  let t : ℝ := 1 / (1 + dx + dy)
  have hden : 0 < 1 + dx + dy := by dsimp [dx, dy]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hden]
    dsimp [dx, dy]
    linarith
  let p := AffineMap.lineMap (planePoint 1 0) q t
  have hpSegment : p ∈ segment ℝ (planePoint 1 0) q := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hpNe : p ≠ planePoint 1 0 := by
    intro hp
    have hinj := AffineMap.lineMap_injective ℝ hq.symm
    apply ht.ne'
    apply hinj
    dsimp [p] at hp
    simpa using hp
  let w : Fin 3 → ℝ :=
    ![t * (dx - dy) / 2, 1 - t * (dx + dy) / 2, t * dy]
  have hpTriangle : p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition p w
    · intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, w, Fin.mk_one,
                        Matrix.cons_val_one, sub_nonneg, Fin.reduceFinMk, Matrix.cons_val]
      · nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hyx)]
      · have htd : t * (dx + dy) < 1 := by
          dsimp [t]
          field_simp
          nlinarith
        linarith
      · exact mul_nonneg ht.le hy0
    · simp [w]
      ring
    · ext i
      fin_cases i <;>
        simp [w, p, kiteTrianglePosition, AffineMap.lineMap_apply_module,
          planePoint, dx, dy]
      all_goals ring
  exact ⟨p, ⟨hpSegment, by simpa using hpNe⟩, hpTriangle⟩

/-- If a segment leaves the left base vertex without entering the triangle, its direction is
strictly outside the triangle tangent cone. -/
theorem leftBase_direction_outside_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint (-1) 0)
    (havoid : segment ℝ (planePoint (-1) 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0}) :
    q 0 + 1 ≤ 0 ∨
      (0 < q 0 + 1 ∧ (q 1 < 0 ∨ q 0 + 1 < q 1)) := by
  by_cases hx : q 0 + 1 ≤ 0
  · exact Or.inl hx
  right
  have hxpos : 0 < q 0 + 1 := lt_of_not_ge hx
  refine ⟨hxpos, ?_⟩
  by_contra hdir
  push Not at hdir
  obtain ⟨p, hpSegment, hpTriangle⟩ :=
    exists_leftBase_openSegment_mem_kiteTriangle hq hxpos hdir.1 hdir.2
  have hpLeft := havoid ⟨hpSegment.1, hpTriangle⟩
  exact hpSegment.2 (by simpa using hpLeft)

theorem rightBase_direction_outside_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint 1 0)
    (havoid : segment ℝ (planePoint 1 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0}) :
    1 - q 0 ≤ 0 ∨
      (0 < 1 - q 0 ∧ (q 1 < 0 ∨ 1 - q 0 < q 1)) := by
  by_cases hx : 1 - q 0 ≤ 0
  · exact Or.inl hx
  right
  have hxpos : 0 < 1 - q 0 := lt_of_not_ge hx
  refine ⟨hxpos, ?_⟩
  by_contra hdir
  push Not at hdir
  obtain ⟨p, hpSegment, hpTriangle⟩ :=
    exists_rightBase_openSegment_mem_kiteTriangle hq hxpos hdir.1 hdir.2
  have hpRight := havoid ⟨hpSegment.1, hpTriangle⟩
  exact hpSegment.2 (by simpa using hpRight)

/-- A segment leaving the left base vertex outside the triangle misses every sufficiently thin
kite except at that vertex. -/
theorem exists_thinKitePatch_inter_leftSegment_eq_singleton {q : Plane}
    (hq : q ≠ planePoint (-1) 0)
    (havoid : segment ℝ (planePoint (-1) 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ (planePoint (-1) 0) q = {planePoint (-1) 0} := by
  rcases leftBase_direction_outside_kiteTriangle hq havoid with hx | ⟨hx, hy | hy⟩
  · refine ⟨1, by norm_num, fun δ hδ _ => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hdx0 : q 0 + 1 = 0 := by
        rw [hcoord0] at hcone
        nlinarith
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hdx0, mul_zero] at hcone
      rw [hcoord1] at hcone
      have hdy0 : q 1 = 0 := by nlinarith
      exfalso
      apply hq
      apply plane_ext
      · simp only [planePoint_apply_zero]
        linarith
      · simpa [planePoint] using hdy0
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := -q 1 / (q 0 + 1)
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos (neg_pos.mpr hy) hx
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : δ * (q 0 + 1) < -q 1 := by
        dsimp [ε] at hδε
        exact (lt_div_iff₀ hx).mp hδε
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := q 1 / (q 0 + 1) - 1
    have hε : 0 < ε := by
      dsimp [ε]
      rw [sub_pos, one_lt_div hx]
      exact hy
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : (1 + δ) * (q 0 + 1) < q 1 := by
        dsimp [ε] at hδε
        rw [lt_sub_iff_add_lt] at hδε
        have := (lt_div_iff₀ hx).mp hδε
        nlinarith
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩

/-- A segment leaving the right base vertex outside the triangle misses every sufficiently thin
kite except at that vertex. -/
theorem exists_thinKitePatch_inter_rightSegment_eq_singleton {q : Plane}
    (hq : q ≠ planePoint 1 0)
    (havoid : segment ℝ (planePoint 1 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ (planePoint 1 0) q = {planePoint 1 0} := by
  rcases rightBase_direction_outside_kiteTriangle hq havoid with hx | ⟨hx, hy | hy⟩
  · refine ⟨1, by norm_num, fun δ hδ _ => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hdx0 : 1 - q 0 = 0 := by
        rw [hcoord0] at hcone
        nlinarith
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hdx0, mul_zero] at hcone
      rw [hcoord1] at hcone
      have hdy0 : q 1 = 0 := by nlinarith
      exfalso
      apply hq
      apply plane_ext
      · simp only [planePoint_apply_zero]
        linarith
      · simpa [planePoint] using hdy0
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := -q 1 / (1 - q 0)
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos (neg_pos.mpr hy) hx
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : δ * (1 - q 0) < -q 1 := by
        dsimp [ε] at hδε
        exact (lt_div_iff₀ hx).mp hδε
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := q 1 / (1 - q 0) - 1
    have hε : 0 < ε := by
      dsimp [ε]
      rw [sub_pos, one_lt_div hx]
      exact hy
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : (1 + δ) * (1 - q 0) < q 1 := by
        dsimp [ε] at hδε
        rw [lt_sub_iff_add_lt] at hδε
        have := (lt_div_iff₀ hx).mp hδε
        nlinarith
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩

theorem thinKiteMap_zero_mem_triangle {q : Plane} (hq : q ∈ diamondPatch) :
    thinKiteMap 0 q ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  let r := thinKiteMap 0 q
  let w : Fin 3 → ℝ := ![(1 - r 1 - r 0) / 2, (1 - r 1 + r 0) / 2, r 1]
  apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition r w
  · intro i
    fin_cases i <;> simp [w]
    all_goals
      by_cases hx : q 0 ≤ 0
      · simp [r, thinKiteMap, thinKiteScale, planePoint, abs_of_nonpos hx]
        linarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        simp [r, thinKiteMap, thinKiteScale, planePoint, abs_of_nonneg hx']
        linarith
  · simp [w]
    ring
  · ext i
    fin_cases i <;> simp [w, r, kiteTrianglePosition, thinKiteMap, planePoint]
    all_goals ring

/-- Every open neighborhood of the limiting triangle contains all sufficiently thin normalized
kites. -/
theorem exists_thinKitePatch_subset_open_normalized (U : Set Plane) (hU : IsOpen U)
    (htriangle : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → thinKitePatch δ ⊆ U := by
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  have hcontinuous : Continuous fun z : ℝ × Plane => thinKiteMap z.1 z.2 := by
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop
  have heventually : ∀ᶠ δ in nhds (0 : ℝ), ∀ q ∈ diamondPatch, thinKiteMap δ q ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro q hq
    apply hcontinuous.continuousAt.eventually
    exact hU.mem_nhds (htriangle (thinKiteMap_zero_mem_triangle hq))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [δ]
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine ⟨δ, hδ, fun η _ hη p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hp
  have hηball : η ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos]
    · dsimp [δ] at hη
      linarith
    · assumption
  exact hball hηball q hq

/-- A finite-mesh edge which meets the limiting triangle in at most one base endpoint is
avoided by every sufficiently thin kite, apart from that endpoint. -/
theorem exists_thinKitePatch_inter_segment_subset_baseEndpoints {a b : Plane}
    (hab : a ≠ b)
    (hinter : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
      {planePoint (-1) 0, planePoint 1 0})
    (hleftEndpoint : planePoint (-1) 0 ∈ segment ℝ a b →
      a = planePoint (-1) 0 ∨ b = planePoint (-1) 0)
    (hrightEndpoint : planePoint 1 0 ∈ segment ℝ a b →
      a = planePoint 1 0 ∨ b = planePoint 1 0)
    (hnotBoth : ¬(planePoint (-1) 0 ∈ segment ℝ a b ∧
      planePoint 1 0 ∈ segment ℝ a b)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ a b ⊆
        {planePoint (-1) 0, planePoint 1 0} := by
  by_cases hleft : planePoint (-1) 0 ∈ segment ℝ a b
  · have hright : planePoint 1 0 ∉ segment ℝ a b :=
      fun h => hnotBoth ⟨hleft, h⟩
    have havoid : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
        {planePoint (-1) 0} := by
      intro p hp
      have hpSegment := hp.1
      rcases hinter hp with hp | hp
      · simpa using hp
      · exact False.elim (hright (hp ▸ hpSegment))
    rcases hleftEndpoint hleft with ha | hb
    · subst a
      obtain ⟨ε, hε, hεavoid⟩ :=
        exists_thinKitePatch_inter_leftSegment_eq_singleton hab.symm havoid
      refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
      rw [hεavoid δ hδ hδε]
      simp
    · subst b
      have havoid' : segment ℝ (planePoint (-1) 0) a ∩
          convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0} := by
        rwa [segment_symm ℝ (planePoint (-1) 0) a]
      obtain ⟨ε, hε, hεavoid⟩ :=
        exists_thinKitePatch_inter_leftSegment_eq_singleton hab havoid'
      refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
      rw [segment_symm ℝ a (planePoint (-1) 0), hεavoid δ hδ hδε]
      simp
  · by_cases hright : planePoint 1 0 ∈ segment ℝ a b
    · have havoid : segment ℝ a b ∩
          convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0} := by
        intro p hp
        have hpSegment := hp.1
        rcases hinter hp with hp | hp
        · exact False.elim (hleft (hp ▸ hpSegment))
        · simpa using hp
      rcases hrightEndpoint hright with ha | hb
      · subst a
        obtain ⟨ε, hε, hεavoid⟩ :=
          exists_thinKitePatch_inter_rightSegment_eq_singleton hab.symm havoid
        refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
        rw [hεavoid δ hδ hδε]
        simp
      · subst b
        have havoid' : segment ℝ (planePoint 1 0) a ∩
            convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0} := by
          rwa [segment_symm ℝ (planePoint 1 0) a]
        obtain ⟨ε, hε, hεavoid⟩ :=
          exists_thinKitePatch_inter_rightSegment_eq_singleton hab havoid'
        refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
        rw [segment_symm ℝ a (planePoint 1 0), hεavoid δ hδ hδε]
        simp
    · have hdisjoint : Disjoint (segment ℝ a b)
          (convexHull ℝ (Set.range kiteTrianglePosition)) := by
        rw [Set.disjoint_left]
        intro p hpSegment hpTriangle
        rcases hinter ⟨hpSegment, hpTriangle⟩ with hp | hp
        · exact hleft (hp ▸ hpSegment)
        · exact hright (hp ▸ hpSegment)
      have hclosed : IsClosed (segment ℝ a b) := by
        rw [← convexHull_pair]
        exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp)).isClosed
      obtain ⟨ε, hε, hpatch⟩ := exists_thinKitePatch_subset_open_normalized
        (segment ℝ a b)ᶜ
        hclosed.isOpen_compl (by
          intro p hpTriangle hpSegment
          exact Set.disjoint_left.mp hdisjoint hpSegment hpTriangle)
      refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
      have hpCompl : p ∈ (segment ℝ a b)ᶜ := by
        exact hpatch δ hδ hδε hp.1
      exact False.elim (hpCompl hp.2)

/-- The `diamondOuterToThinKite` declaration. -/
noncomputable def diamondOuterToThinKite (δ : ℝ) (hδ : 0 < δ) :
    diamondPatch ≃ₜ thinKitePatch δ := by
  exact (thinKiteGlobalHomeomorph δ hδ).image diamondPatch

/-- The `thinKiteSource` declaration. -/
noncomputable def thinKiteSource (δ : ℝ) : ℝ := -2 / (1 + 2 * δ)

/-- The `thinKiteTarget` declaration. -/
noncomputable def thinKiteTarget (δ : ℝ) : ℝ := 2 / (1 + 2 * δ)

theorem thinKiteSource_lower {δ : ℝ} (hδ : 0 < δ) : -2 < thinKiteSource δ := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteSource, lt_div_iff₀ hd]
  nlinarith

theorem thinKiteSource_upper {δ : ℝ} (hδ : 0 < δ) : thinKiteSource δ < 2 := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteSource, div_lt_iff₀ hd]
  nlinarith

theorem thinKiteTarget_lower {δ : ℝ} (hδ : 0 < δ) : -2 < thinKiteTarget δ := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteTarget, lt_div_iff₀ hd]
  nlinarith

theorem thinKiteTarget_upper {δ : ℝ} (hδ : 0 < δ) : thinKiteTarget δ < 2 := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteTarget, div_lt_iff₀ hd]
  nlinarith

private noncomputable def diamondFanSpokeWeights (i : Fin 5) (c : ℝ) : Fin 5 → ℝ :=
  fun v => if v = i then 1 - c else if v = 4 then c else 0

private noncomputable def diamondFanLeftSpokeRealization (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x := diamondFanSpokeWeights 0 c
  refine ⟨x, ?_, {0, 4, 2}, ?_, ?_⟩
  · constructor
    · intro v
      fin_cases v <;> simp [x, diamondFanSpokeWeights] <;> linarith [hc.1, hc.2]
    · simp [x, diamondFanSpokeWeights, Fin.sum_univ_succ]
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    fin_cases v <;> simp [x, diamondFanSpokeWeights] at hv ⊢

private theorem diamondFanLeftSpokeRealization_baryEval (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanLeftSpokeRealization a ha0 ha1 c hc).1 =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c := by
  change (∑ v : Fin 5, diamondFanSpokeWeights 0 c v • diamondFanPosition a v) = _
  ext i
  fin_cases i <;>
    simp [diamondFanSpokeWeights, diamondFanPosition, AffineMap.lineMap_apply_module,
      Fin.sum_univ_succ, planePoint]

private noncomputable def diamondFanLeftSpokePoint (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    (diamondFanLeftSpokeRealization a ha0 ha1 c hc)

private theorem diamondFanLeftSpokePoint_val (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanLeftSpokePoint a ha0 ha1 c hc : Plane) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c :=
  diamondFanLeftSpokeRealization_baryEval a ha0 ha1 c hc

private theorem diamondFanAmbientHomeomorph_leftSpoke (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 b) c := by
  have hmem : AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c ∈
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support := by
    rw [← diamondFanLeftSpokePoint_val a ha0 ha1 c hc]
    exact (diamondFanLeftSpokePoint a ha0 ha1 c hc).property
  erw [diamondFanAmbientHomeomorph, TriangleMesh.ambientRepositionHomeomorph,
    extendHomeomorphByIdentity_apply_mem _ _ _ hmem]
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c, hmem⟩ : Plane) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 b) c
  rw [diamondFanPatchHomeomorph_apply_val]
  have hz :
      (⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c, hmem⟩ :
        (diamondFanMesh a ha0 ha1).toPlaneComplex.support) =
        diamondFanLeftSpokePoint a ha0 ha1 c hc := by
    apply Subtype.ext
    exact (diamondFanLeftSpokePoint_val a ha0 ha1 c hc).symm
  rw [hz]
  exact ((diamondFanMesh a ha0 ha1).coe_repositionHomeomorph_apply_realization
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanLeftSpokeRealization a ha0 ha1 c hc)).trans
      (diamondFanLeftSpokeRealization_baryEval b hb0 hb1 c hc)

private noncomputable def diamondFanRightSpokeRealization (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x := diamondFanSpokeWeights 1 c
  refine ⟨x, ?_, {1, 2, 4}, ?_, ?_⟩
  · constructor
    · intro v
      fin_cases v <;> simp [x, diamondFanSpokeWeights] <;> linarith [hc.1, hc.2]
    · simp [x, diamondFanSpokeWeights, Fin.sum_univ_succ]
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    fin_cases v <;> simp [x, diamondFanSpokeWeights] at hv ⊢

private theorem diamondFanRightSpokeRealization_baryEval (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanRightSpokeRealization a ha0 ha1 c hc).1 =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c := by
  change (∑ v : Fin 5, diamondFanSpokeWeights 1 c v • diamondFanPosition a v) = _
  ext i
  fin_cases i <;>
    simp [diamondFanSpokeWeights, diamondFanPosition, AffineMap.lineMap_apply_module,
      Fin.sum_univ_succ, planePoint]

private noncomputable def diamondFanRightSpokePoint (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    (diamondFanRightSpokeRealization a ha0 ha1 c hc)

private theorem diamondFanRightSpokePoint_val (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanRightSpokePoint a ha0 ha1 c hc : Plane) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c :=
  diamondFanRightSpokeRealization_baryEval a ha0 ha1 c hc

private theorem diamondFanAmbientHomeomorph_rightSpoke (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 b) c := by
  have hmem : AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c ∈
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support := by
    rw [← diamondFanRightSpokePoint_val a ha0 ha1 c hc]
    exact (diamondFanRightSpokePoint a ha0 ha1 c hc).property
  erw [diamondFanAmbientHomeomorph, TriangleMesh.ambientRepositionHomeomorph,
    extendHomeomorphByIdentity_apply_mem _ _ _ hmem]
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c, hmem⟩ : Plane) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 b) c
  rw [diamondFanPatchHomeomorph_apply_val]
  have hz :
      (⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c, hmem⟩ :
        (diamondFanMesh a ha0 ha1).toPlaneComplex.support) =
        diamondFanRightSpokePoint a ha0 ha1 c hc := by
    apply Subtype.ext
    exact (diamondFanRightSpokePoint_val a ha0 ha1 c hc).symm
  rw [hz]
  exact ((diamondFanMesh a ha0 ha1).coe_repositionHomeomorph_apply_realization
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanRightSpokeRealization a ha0 ha1 c hc)).trans
      (diamondFanRightSpokeRealization_baryEval b hb0 hb1 c hc)

@[simp] theorem thinKiteMap_source (δ : ℝ) (hδ : 0 < δ) :
    thinKiteMap δ (planePoint 0 (thinKiteSource δ)) = planePoint 0 0 := by
  ext i
  fin_cases i
  · simp [thinKiteMap]
  · simp only [thinKiteMap, thinKiteSource, Fin.isValue, planePoint_apply_zero, thinKiteScale,
      planePoint_apply_one, abs_zero, sub_zero, one_div, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

@[simp] theorem thinKiteMap_target (δ : ℝ) (hδ : 0 < δ) :
    thinKiteMap δ (planePoint 0 (thinKiteTarget δ)) = planePoint 0 1 := by
  ext i
  fin_cases i
  · simp [thinKiteMap]
  · simp only [thinKiteMap, thinKiteTarget, Fin.isValue, planePoint_apply_zero, thinKiteScale,
      planePoint_apply_one, abs_zero, sub_zero, one_div, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

theorem isClosed_thinKitePatch (δ : ℝ) : IsClosed (thinKitePatch δ) := by
  rw [thinKitePatch]
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  exact (hcompact.image (by
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop)).isClosed

/-- The `thinKiteAmbientHomeomorph` declaration. -/
noncomputable def thinKiteAmbientHomeomorph (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane :=
  (thinKiteGlobalHomeomorph δ hδ).symm.trans
    ((diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)).trans
        (thinKiteGlobalHomeomorph δ hδ))

private theorem thinKiteInv_leftSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteInv δ (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 (thinKiteSource δ)) c := by
  have habs : |c - 1| = 1 - c := by
    rw [abs_of_nonpos]
    · ring
    · linarith [hc.2]
  ext i
  fin_cases i
  · simp [thinKiteInv, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteInv, planePoint, AffineMap.lineMap_apply_module, Fin.isValue,
      PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_neg,
      mul_one, neg_sub, mul_zero, add_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, habs, sub_sub_cancel, zero_sub, thinKiteScale,
      Fin.mk_one, thinKiteSource, zero_add]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteInv_rightSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteInv δ (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 (thinKiteSource δ)) c := by
  have habs : |1 - c| = 1 - c := abs_of_nonneg (by linarith [hc.2])
  ext i
  fin_cases i
  · simp [thinKiteInv, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteInv, planePoint, AffineMap.lineMap_apply_module, Fin.isValue,
      PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one,
      mul_zero, add_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, habs,
      sub_sub_cancel, zero_sub, thinKiteScale, Fin.mk_one, thinKiteSource, zero_add]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteMap_leftTargetSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteMap δ
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 (thinKiteTarget δ)) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 1) c := by
  have habs : |c - 1| = 1 - c := by
    rw [abs_of_nonpos]
    · ring
    · linarith [hc.2]
  ext i
  fin_cases i
  · simp [thinKiteMap, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteMap, planePoint, thinKiteTarget,
      AffineMap.lineMap_apply_module, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_neg, mul_one, neg_sub, mul_zero,
      add_zero, thinKiteScale, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_add, habs, sub_sub_cancel, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteMap_rightTargetSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteMap δ
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 (thinKiteTarget δ)) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 1) c := by
  have habs : |1 - c| = 1 - c := abs_of_nonneg (by linarith [hc.2])
  ext i
  fin_cases i
  · simp [thinKiteMap, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteMap, planePoint, thinKiteTarget,
      AffineMap.lineMap_apply_module, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_one, mul_zero, add_zero, thinKiteScale,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add, habs, sub_sub_cancel,
      Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

theorem thinKiteAmbientHomeomorph_leftSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteAmbientHomeomorph δ hδ
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 1) c := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  change thinKiteMap δ
      (diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
        (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
        (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
        (thinKiteInv δ
          (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c))) = _
  rw [thinKiteInv_leftSpoke δ hδ c hc,
    diamondFanAmbientHomeomorph_leftSpoke, thinKiteMap_leftTargetSpoke δ hδ c hc]
  exact hc

theorem thinKiteAmbientHomeomorph_rightSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteAmbientHomeomorph δ hδ
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 1) c := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  change thinKiteMap δ
      (diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
        (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
        (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
        (thinKiteInv δ
          (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c))) = _
  rw [thinKiteInv_rightSpoke δ hδ c hc,
    diamondFanAmbientHomeomorph_rightSpoke, thinKiteMap_rightTargetSpoke δ hδ c hc]
  exact hc

theorem thinKiteAmbientHomeomorph_image_leftSpoke (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint (-1) 0) (planePoint 0 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 1) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨-, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (thinKiteAmbientHomeomorph_leftSpoke δ hδ c hc).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c,
      ⟨c, hc, rfl⟩, thinKiteAmbientHomeomorph_leftSpoke δ hδ c hc⟩

theorem thinKiteAmbientHomeomorph_image_rightSpoke (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint 1 0) (planePoint 0 0) =
      segment ℝ (planePoint 1 0) (planePoint 0 1) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨-, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (thinKiteAmbientHomeomorph_rightSpoke δ hδ c hc).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c,
      ⟨c, hc, rfl⟩, thinKiteAmbientHomeomorph_rightSpoke δ hδ c hc⟩

/-- The thin-kite homeomorphism is affine on every subsegment of its left base half. -/
theorem thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_leftSpoke
    (δ : ℝ) (hδ : 0 < δ) {a b : Plane}
    (ha : a ∈ segment ℝ (planePoint (-1) 0) (planePoint 0 0))
    (hb : b ∈ segment ℝ (planePoint (-1) 0) (planePoint 0 0)) :
    thinKiteAmbientHomeomorph δ hδ '' segment ℝ a b =
      segment ℝ (thinKiteAmbientHomeomorph δ hδ a)
        (thinKiteAmbientHomeomorph δ hδ b) := by
  rw [segment_eq_image_lineMap] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  let L := planePoint (-1) 0
  let C := planePoint 0 0
  let A := planePoint 0 1
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      thinKiteAmbientHomeomorph δ hδ
          (AffineMap.lineMap (AffineMap.lineMap L C s)
            (AffineMap.lineMap L C r) t) =
        AffineMap.lineMap
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap L C s))
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap L C r)) t := by
    have hsr : (1 - t) * s + t * r ∈ Set.Icc (0 : ℝ) 1 := by
      have hmem := (convex_Icc (0 : ℝ) 1).segment_subset hs hr
        (lineMap_mem_segment ℝ s r ht)
      simpa [AffineMap.lineMap_apply_module] using hmem
    rw [show AffineMap.lineMap (AffineMap.lineMap L C s)
          (AffineMap.lineMap L C r) t =
        AffineMap.lineMap L C ((1 - t) * s + t * r) by
      ext i
      fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> ring]
    rw [thinKiteAmbientHomeomorph_leftSpoke δ hδ _ hsr,
      thinKiteAmbientHomeomorph_leftSpoke δ hδ s hs,
      thinKiteAmbientHomeomorph_leftSpoke δ hδ r hr]
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply_module] ; ring
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simpa [L, C] using (hline t ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨AffineMap.lineMap (AffineMap.lineMap L C s)
      (AffineMap.lineMap L C r) t, ⟨t, ht, rfl⟩,
        by simpa [L, C] using hline t ht⟩

/-- The thin-kite homeomorphism is affine on every subsegment of its right base half. -/
theorem thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_rightSpoke
    (δ : ℝ) (hδ : 0 < δ) {a b : Plane}
    (ha : a ∈ segment ℝ (planePoint 0 0) (planePoint 1 0))
    (hb : b ∈ segment ℝ (planePoint 0 0) (planePoint 1 0)) :
    thinKiteAmbientHomeomorph δ hδ '' segment ℝ a b =
      segment ℝ (thinKiteAmbientHomeomorph δ hδ a)
        (thinKiteAmbientHomeomorph δ hδ b) := by
  rw [segment_symm] at ha hb
  rw [segment_eq_image_lineMap] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  let R := planePoint 1 0
  let C := planePoint 0 0
  let A := planePoint 0 1
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      thinKiteAmbientHomeomorph δ hδ
          (AffineMap.lineMap (AffineMap.lineMap R C s)
            (AffineMap.lineMap R C r) t) =
        AffineMap.lineMap
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap R C s))
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap R C r)) t := by
    have hsr : (1 - t) * s + t * r ∈ Set.Icc (0 : ℝ) 1 := by
      have hmem := (convex_Icc (0 : ℝ) 1).segment_subset hs hr
        (lineMap_mem_segment ℝ s r ht)
      simpa [AffineMap.lineMap_apply_module] using hmem
    rw [show AffineMap.lineMap (AffineMap.lineMap R C s)
          (AffineMap.lineMap R C r) t =
        AffineMap.lineMap R C ((1 - t) * s + t * r) by
      ext i
      fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> ring]
    rw [thinKiteAmbientHomeomorph_rightSpoke δ hδ _ hsr,
      thinKiteAmbientHomeomorph_rightSpoke δ hδ s hs,
      thinKiteAmbientHomeomorph_rightSpoke δ hδ r hr]
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply_module] ; ring
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simpa [R, C] using (hline t ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨AffineMap.lineMap (AffineMap.lineMap R C s)
      (AffineMap.lineMap R C r) t, ⟨t, ht, rfl⟩,
        by simpa [R, C] using hline t ht⟩

theorem baseSegment_eq_spokes :
    segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 0) ∪
        segment ℝ (planePoint 1 0) (planePoint 0 0) := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    by_cases hhalf : c ≤ (1 : ℝ) / 2
    · left
      rw [segment_eq_image_lineMap]
      refine ⟨2 * c, ⟨by linarith [hc.1], by linarith⟩, ?_⟩
      ext i
      fin_cases i <;>
        simp [AffineMap.lineMap_apply_module, planePoint]; ring
    · right
      rw [segment_eq_image_lineMap]
      refine ⟨2 - 2 * c, ⟨by linarith [hc.2], by linarith⟩, ?_⟩
      ext i
      fin_cases i <;>
        simp [AffineMap.lineMap_apply_module, planePoint]; ring
  · have hcenter : planePoint 0 0 ∈
        segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      rw [show planePoint 0 0 = AffineMap.lineMap
          (planePoint (-1) 0) (planePoint 1 0) ((1 : ℝ) / 2) by
        ext i
        fin_cases i <;>
          simp [AffineMap.lineMap_apply_module, planePoint]; ring]
      exact lineMap_mem_segment ℝ _ _ (by constructor <;> norm_num)
    apply Set.union_subset
    · exact (convex_segment (𝕜 := ℝ) (planePoint (-1) 0) (planePoint 1 0)).segment_subset
        (left_mem_segment ℝ _ _) hcenter
    · exact (convex_segment (𝕜 := ℝ) (planePoint (-1) 0) (planePoint 1 0)).segment_subset
        (right_mem_segment ℝ _ _) hcenter

theorem thinKiteAmbientHomeomorph_image_baseSegment (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 1) ∪
        segment ℝ (planePoint 1 0) (planePoint 0 1) := by
  rw [baseSegment_eq_spokes, Set.image_union,
    thinKiteAmbientHomeomorph_image_leftSpoke,
    thinKiteAmbientHomeomorph_image_rightSpoke]

theorem thinKiteAmbientHomeomorph_center (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ (planePoint 0 0) = planePoint 0 1 := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [show (thinKiteGlobalHomeomorph δ hδ).symm (planePoint 0 0) =
      planePoint 0 (thinKiteSource δ) by
    change thinKiteInv δ (planePoint 0 0) = planePoint 0 (thinKiteSource δ)
    ext i
    fin_cases i
    · simp [thinKiteInv]
    · simp only [thinKiteInv, Fin.isValue, planePoint_apply_zero, planePoint_apply_one, abs_zero,
        sub_zero, one_div, zero_sub, thinKiteScale, Fin.mk_one, thinKiteSource]
      have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
      field_simp [hd]
      ring]
  rw [diamondFanAmbientHomeomorph_center]
  exact thinKiteMap_target δ hδ

theorem thinKiteAmbientHomeomorph_eqOn_compl (δ : ℝ) (hδ : 0 < δ) :
    Set.EqOn (thinKiteAmbientHomeomorph δ hδ) id (thinKitePatch δ)ᶜ := by
  intro p hp
  have hpre : (thinKiteGlobalHomeomorph δ hδ).symm p ∉ diamondPatch := by
    intro hmem
    apply hp
    rw [thinKitePatch]
    refine ⟨(thinKiteGlobalHomeomorph δ hδ).symm p, hmem, ?_⟩
    simpa [thinKiteGlobalHomeomorph] using
      (thinKiteGlobalHomeomorph δ hδ).apply_symm_apply p
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [diamondFanAmbientHomeomorph_eqOn_compl _ _ _ _ _ _ hpre]
  simp

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_01
/- END ClassificationOfSurfaces.Moise.ThinKiteMove -/

/- BEGIN ClassificationOfSurfaces.Moise.CommonSubdivision | 2dc0ddf525209a38bde418b8a82d22c8b01179e0962f0176fac44acd3cd403bf -/
section schottkyclassification06_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Common subdivisions of finite plane triangle meshes

The finite common-refinement theorem used in Moise Chapter 5.  To make a source mesh
subordinate to a target mesh with the same support, cut it by every barycentric-coordinate
hyperplane of every target triangle.  The resulting chambers lie in target triangles.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An affine map which is injective on a nondegenerate closed triangle sends its three
vertices to an affinely independent triple.

The hypothesis is deliberately local.  This is the form needed when a facewise-affine
embedding is known to be injective only on the simplex on which its affine formula is valid. -/
theorem affineIndependent_comp_of_injOn_convexHull
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] V)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    AffineIndependent ℝ (f ∘ p) := by
  classical
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hw
  let B : ℝ := ∑ i : Fin 3, (|w₁ i| + |w₂ i|)
  have hB : 0 ≤ B := by
    exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  let r : ℝ := (6 * (B + 1))⁻¹
  have hden : 0 < 6 * (B + 1) := mul_pos (by norm_num) (by linarith)
  have hr : 0 < r := inv_pos.mpr hden
  have hrmul : r * (B + 1) = 1 / 6 := by
    dsimp only [r]
    rw [inv_mul_eq_div]
    field_simp [ne_of_gt hden]
  let u : Fin 3 → ℝ := fun _ => 1 / 3
  let x : Fin 3 → ℝ := AffineMap.lineMap u w₁ r
  let y : Fin 3 → ℝ := AffineMap.lineMap u w₂ r
  have hw₁lower (i : Fin 3) : -B ≤ w₁ i := by
    have hi :
        |w₁ i| ≤ ∑ j : Fin 3, (|w₁ j| + |w₂ j|) := by
      apply le_trans (le_add_of_nonneg_right (abs_nonneg (w₂ i)))
      exact Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (w₁ j)) (abs_nonneg (w₂ j)))
        (Finset.mem_univ i)
    exact (neg_le_of_abs_le hi)
  have hw₂lower (i : Fin 3) : -B ≤ w₂ i := by
    have hi :
        |w₂ i| ≤ ∑ j : Fin 3, (|w₁ j| + |w₂ j|) := by
      apply le_trans (le_add_of_nonneg_left (abs_nonneg (w₁ i)))
      exact Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (w₁ j)) (abs_nonneg (w₂ j)))
        (Finset.mem_univ i)
    exact (neg_le_of_abs_le hi)
  have hx0 (i : Fin 3) : 0 ≤ x i := by
    have hmul := mul_le_mul_of_nonneg_left (hw₁lower i) hr.le
    dsimp only [x, u]
    rw [AffineMap.lineMap_apply_module]
    change 0 ≤ (1 - r) * (1 / 3) + r * w₁ i
    nlinarith
  have hy0 (i : Fin 3) : 0 ≤ y i := by
    have hmul := mul_le_mul_of_nonneg_left (hw₂lower i) hr.le
    dsimp only [y, u]
    rw [AffineMap.lineMap_apply_module]
    change 0 ≤ (1 - r) * (1 / 3) + r * w₂ i
    nlinarith
  have hu : ∑ i : Fin 3, u i = 1 := by
    simp [u]
  have hxsum : ∑ i : Fin 3, x i = 1 := by
    simp only [x, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hu, hw₁]
    ring
  have hysum : ∑ i : Fin 3, y i = 1 := by
    simp only [y, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hu, hw₂]
    ring
  let px := Finset.univ.affineCombination ℝ p x
  let py := Finset.univ.affineCombination ℝ p y
  have hpx : px ∈ convexHull ℝ (Set.range p) := by
    exact affineCombination_mem_convexHull (fun i _ => hx0 i) hxsum
  have hpy : py ∈ convexHull ℝ (Set.range p) := by
    exact affineCombination_mem_convexHull (fun i _ => hy0 i) hysum
  have hfw :
      f (Finset.univ.affineCombination ℝ p w₁) =
        f (Finset.univ.affineCombination ℝ p w₂) := by
    rw [Finset.univ.map_affineCombination p w₁ hw₁ f,
      Finset.univ.map_affineCombination p w₂ hw₂ f]
    exact hw
  have hfxy : f px = f py := by
    change
      f (Finset.univ.affineCombination ℝ p x) =
        f (Finset.univ.affineCombination ℝ p y)
    rw [← Finset.univ.lineMap_affineCombination u w₁ r p,
      ← Finset.univ.lineMap_affineCombination u w₂ r p,
      f.apply_lineMap, f.apply_lineMap, hfw]
  have hpxy : px = py := hf hpx hpy hfxy
  have hxy : x = y :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ p).mp hp
      x y hxsum hysum hpxy
  funext i
  have hi := congrFun hxy i
  dsimp only [x, y, u] at hi
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hi
  change (1 - r) * (1 / 3) + r * w₁ i =
    (1 - r) * (1 / 3) + r * w₂ i at hi
  exact (mul_left_cancel₀ hr.ne' (by linarith : r * w₁ i = r * w₂ i))

/-- In the plane, local injectivity of an affine map on one nondegenerate triangle already
forces global injectivity. -/
theorem affineMap_injective_of_injOn_convexHull
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] Plane)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    Function.Injective f := by
  let q : Fin 3 → Plane := f ∘ p
  have hq : AffineIndependent ℝ q :=
    affineIndependent_comp_of_injOn_convexHull p hp f hf
  let e : Plane ≃ᵃ[ℝ] Plane := triangleAffineEquiv p q hp hq
  have hfe : f = e.toAffineMap := by
    apply AffineMap.ext_on
      ((hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp [Plane]))
    rintro x ⟨i, rfl⟩
    exact (triangleAffineEquiv_apply p q hp hq i).symm
  rw [hfe]
  exact e.injective

/-- The same local hypothesis makes a planar affine map surjective. -/
theorem affineMap_surjective_of_injOn_convexHull
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] Plane)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    Function.Surjective f := by
  let q : Fin 3 → Plane := f ∘ p
  have hq : AffineIndependent ℝ q :=
    affineIndependent_comp_of_injOn_convexHull p hp f hf
  let e : Plane ≃ᵃ[ℝ] Plane := triangleAffineEquiv p q hp hq
  have hfe : f = e.toAffineMap := by
    apply AffineMap.ext_on
      ((hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp [Plane]))
    rintro x ⟨i, rfl⟩
    exact (triangleAffineEquiv_apply p q hp hq i).symm
  rw [hfe]
  exact e.surjective

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Barycentric coordinates in one maximal mesh triangle, extended by zero to all mesh
vertices.  This is the triangle-mesh-native counterpart of `PlaneComplex.faceCoords`; keeping
the codomain definitionally equal to `M.Vertex → ℝ` avoids transports through
`M.toPlaneComplex.Vertex`. -/
noncomputable def triangleCoords (T : M.Triangle) :
    Plane →ᵃ[ℝ] (M.Vertex → ℝ) := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  exact AffineMap.pi fun v =>
    if hv : v ∈ T.1 then
      b.coord (M.triangleEquiv T ⟨v, hv⟩)
    else
      AffineMap.const ℝ Plane 0

@[simp] theorem triangleCoords_apply_of_mem (T : M.Triangle)
    {v : M.Vertex} (hv : v ∈ T.1) (p : Plane) :
    M.triangleCoords T p v =
      (affineBasisOfTriangle
        (M.position ∘ M.orderedVertex T)
        (M.orderedVertex_affineIndependent T)).coord
          (M.triangleEquiv T ⟨v, hv⟩) p := by
  classical
  simp [triangleCoords, hv]

@[simp] theorem triangleCoords_apply_of_notMem (T : M.Triangle)
    {v : M.Vertex} (hv : v ∉ T.1) (p : Plane) :
    M.triangleCoords T p v = 0 := by
  classical
  simp [triangleCoords, hv]

theorem triangleCoords_support (T : M.Triangle) (p : Plane) :
    ∀ v ∉ T.1, M.triangleCoords T p v = 0 :=
  fun _ hv => M.triangleCoords_apply_of_notMem T hv p

theorem sum_triangleCoords (T : M.Triangle) (p : Plane) :
    ∑ v, M.triangleCoords T p v = 1 := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  calc
    ∑ v, M.triangleCoords T p v =
        ∑ v ∈ T.1, M.triangleCoords T p v := by
      symm
      exact Finset.sum_subset (Finset.subset_univ T.1)
        (fun v _ hv => M.triangleCoords_apply_of_notMem T hv p)
    _ = ∑ v : T.1, M.triangleCoords T p v.1 := by
      rw [Finset.sum_coe_sort]
    _ =
        ∑ v : T.1, b.coord (M.triangleEquiv T v) p := by
      apply Finset.sum_congr rfl
      intro v hv
      exact M.triangleCoords_apply_of_mem T v.2 p
    _ = ∑ i : Fin 3, b.coord i p :=
      (M.triangleEquiv T).sum_comp (fun i => b.coord i p)
    _ = 1 := b.sum_coord_apply_eq_one p

theorem baryEval_triangleCoords (T : M.Triangle) (p : Plane) :
    M.toPlaneComplex.baryEval (M.triangleCoords T p) = p := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  rw [M.toPlaneComplex.baryEval_eq_sum_of_support
    (M.triangleCoords_support T p)]
  erw [← Finset.sum_coe_sort]
  calc
    ∑ v : T.1, M.triangleCoords T p v.1 • M.position v.1 =
        ∑ v : T.1, b.coord (M.triangleEquiv T v) p •
          M.position v.1 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [M.triangleCoords_apply_of_mem T v.2 p]
    _ = ∑ i : Fin 3, b.coord i p •
          M.position (M.orderedVertex T i) := by
      calc
        _ = ∑ v : T.1, b.coord (M.triangleEquiv T v) p •
            M.position (M.orderedVertex T (M.triangleEquiv T v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          congr 2
          exact congrArg Subtype.val
            ((M.triangleEquiv T).symm_apply_apply v).symm
        _ = _ :=
          (M.triangleEquiv T).sum_comp
            (fun i => b.coord i p • M.position (M.orderedVertex T i))
    _ = p := by
      change ∑ i : Fin 3, b.coord i p • b i = p
      exact b.linear_combination_coord_eq_self p

theorem triangleCoords_nonneg_of_mem (T : M.Triangle) {p : Plane}
    (hp : p ∈ M.triangleCarrier T.1) (v : M.Vertex) :
    0 ≤ M.triangleCoords T p v := by
  by_cases hv : v ∈ T.1
  · let k : Fin 3 := M.triangleEquiv T ⟨v, hv⟩
    rw [M.triangleCoords_apply_of_mem T hv p]
    change 0 ≤ M.oppositeCoord T k p
    exact M.oppositeCoord_nonneg_of_mem_parent T k hp
  · rw [M.triangleCoords_apply_of_notMem T hv p]

/-- The barycentric-coordinate hyperplanes of all maximal triangles. -/
noncomputable def coordinateLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset M.Triangle).toList.flatMap fun t =>
    (Finset.univ : Finset (Fin 3)).toList.map (M.oppositeCoord t)

theorem oppositeCoord_mem_coordinateLines (t : M.Triangle) (k : Fin 3) :
    M.oppositeCoord t k ∈ M.coordinateLines := by
  simp [coordinateLines]

/-- Cut `M` by every coordinate hyperplane of `N`. -/
noncomputable def refineTo (M N : TriangleMesh) : TriangleMesh :=
  M.refineByLines N.coordinateLines

theorem refineTo_support (N : TriangleMesh) :
    (M.refineTo N).toPlaneComplex.support = M.toPlaneComplex.support :=
  M.refineByLines_support N.coordinateLines

theorem refineTo_subdivides_left (N : TriangleMesh) :
    (M.refineTo N).toPlaneComplex.Subdivides M.toPlaneComplex :=
  M.refineByLines_subdivides N.coordinateLines

theorem refineTo_isMonochromatic (N : TriangleMesh) (t : N.Triangle) (k : Fin 3) :
    (M.refineTo N).IsMonochromatic (N.oppositeCoord t k) :=
  M.refineByLines_isMonochromatic_of_mem N.coordinateLines
    (N.oppositeCoord_mem_coordinateLines t k)

/-- The interior of a nonnegative affine half-space is its strictly positive half-space. -/
theorem interior_affine_nonneg_of_surjective (f : Plane →ᵃ[ℝ] ℝ)
    (hf : Function.Surjective f) :
    interior {x | 0 ≤ f x} = {x | 0 < f x} := by
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional hf).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

/-- The interior of a nonpositive affine half-space is its strictly negative half-space. -/
theorem interior_affine_nonpos_of_surjective (f : Plane →ᵃ[ℝ] ℝ)
    (hf : Function.Surjective f) :
    interior {x | f x ≤ 0} = {x | f x < 0} := by
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional hf).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

/-- Every maximal chamber of `M.refineTo N` lies in a maximal triangle of `N`, provided the
two original meshes have the same support. -/
theorem exists_target_triangle_of_refineTo
    (N : TriangleMesh) (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support)
    (T : (M.refineTo N).Triangle) :
    ∃ U : N.Triangle,
      (M.refineTo N).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  let R := M.refineTo N
  obtain ⟨x, hx⟩ := R.interior_triangleCarrier_nonempty T
  have hxSupport : x ∈ N.toPlaneComplex.support := by
    rw [← hsupport, ← M.refineTo_support N]
    rw [R.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨T.1, Set.mem_iUnion.mpr ⟨T.2, interior_subset hx⟩⟩
  rw [N.toPlaneComplex_support] at hxSupport
  simp only [Set.mem_iUnion] at hxSupport
  obtain ⟨u, hu, hxu⟩ := hxSupport
  let U : N.Triangle := ⟨u, hu⟩
  refine ⟨U, ?_⟩
  have hxCoordPos (k : Fin 3) : 0 < N.oppositeCoord U k x := by
    have hxnonneg : 0 ≤ N.oppositeCoord U k x :=
      N.oppositeCoord_nonneg_of_mem_parent U k hxu
    rcases M.refineTo_isMonochromatic N U k T.1 T.2 with hpos | hneg
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | 0 ≤ N.oppositeCoord U k p} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint := interior_mono hsubset hx
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonneg_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint
      exact hxint
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | N.oppositeCoord U k p ≤ 0} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint := interior_mono hsubset hx
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonpos_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint
      change N.oppositeCoord U k x < 0 at hxint
      linarith
  intro p hp
  let b := affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
    (N.orderedVertex_affineIndependent U)
  have hcarrier : N.triangleCarrier U.1 = {q | ∀ k : Fin 3, 0 ≤ b.coord k q} := by
    rw [TriangleMesh.triangleCarrier]
    have hrange : N.position '' (U.1 : Set N.Vertex) = Set.range b := by
      change N.position '' (U.1 : Set N.Vertex) =
        Set.range (N.position ∘ N.orderedVertex U)
      rw [Set.range_comp, N.range_orderedVertex U]
    rw [hrange, b.convexHull_eq_nonneg_coord]
  rw [hcarrier]
  intro k
  change 0 ≤ N.oppositeCoord U k p
  rcases M.refineTo_isMonochromatic N U k T.1 T.2 with hpos | hneg
  · apply convexHull_min ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k)) hp
    rintro q ⟨v, hv, rfl⟩
    exact hpos v hv
  · have hsubset : R.triangleCarrier T.1 ⊆ {q | N.oppositeCoord U k q ≤ 0} := by
      apply convexHull_min
      · rintro q ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
    have hpnonpos := hsubset hp
    have hxpos := hxCoordPos k
    have hxnonpos := hsubset (interior_subset hx)
    exfalso
    exact (not_lt_of_ge hxnonpos) hxpos

/-- A chamber cut by at least all target coordinate lines and whose interior meets the target
support lies in one target triangle. -/
theorem exists_target_triangle_of_refineByLines_of_interior_inter_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hlines : ∀ a ∈ N.coordinateLines, a ∈ lines)
    (T : (M.refineByLines lines).Triangle)
    (hhit : (interior ((M.refineByLines lines).triangleCarrier T.1) ∩
      N.toPlaneComplex.support).Nonempty) :
    ∃ U : N.Triangle,
      (M.refineByLines lines).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  let R := M.refineByLines lines
  obtain ⟨x, hxint, hxSupport⟩ := hhit
  rw [N.toPlaneComplex_support] at hxSupport
  simp only [Set.mem_iUnion] at hxSupport
  obtain ⟨u, hu, hxu⟩ := hxSupport
  let U : N.Triangle := ⟨u, hu⟩
  refine ⟨U, ?_⟩
  have hmono (k : Fin 3) : R.IsMonochromatic (N.oppositeCoord U k) :=
    M.refineByLines_isMonochromatic_of_mem lines
      (hlines _ (N.oppositeCoord_mem_coordinateLines U k))
  have hxCoordPos (k : Fin 3) : 0 < N.oppositeCoord U k x := by
    have hxnonneg : 0 ≤ N.oppositeCoord U k x :=
      N.oppositeCoord_nonneg_of_mem_parent U k hxu
    rcases hmono k T.1 T.2 with hpos | hneg
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | 0 ≤ N.oppositeCoord U k p} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint' := interior_mono hsubset hxint
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonneg_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint'
      exact hxint'
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | N.oppositeCoord U k p ≤ 0} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint' := interior_mono hsubset hxint
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonpos_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint'
      change N.oppositeCoord U k x < 0 at hxint'
      linarith
  intro p hp
  let b := affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
    (N.orderedVertex_affineIndependent U)
  have hcarrier : N.triangleCarrier U.1 = {q | ∀ k : Fin 3, 0 ≤ b.coord k q} := by
    rw [TriangleMesh.triangleCarrier]
    have hrange : N.position '' (U.1 : Set N.Vertex) = Set.range b := by
      change N.position '' (U.1 : Set N.Vertex) =
        Set.range (N.position ∘ N.orderedVertex U)
      rw [Set.range_comp, N.range_orderedVertex U]
    rw [hrange, b.convexHull_eq_nonneg_coord]
  rw [hcarrier]
  intro k
  change 0 ≤ N.oppositeCoord U k p
  rcases hmono k T.1 T.2 with hpos | hneg
  · apply convexHull_min ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k)) hp
    rintro q ⟨v, hv, rfl⟩
    exact hpos v hv
  · have hsubset : R.triangleCarrier T.1 ⊆ {q | N.oppositeCoord U k q ≤ 0} := by
      apply convexHull_min
      · rintro q ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
    have hxnonpos := hsubset (interior_subset hxint)
    exact False.elim ((not_lt_of_ge hxnonpos) (hxCoordPos k))

/-- A chamber whose interior meets the target support lies in one target triangle.  Unlike
`exists_target_triangle_of_refineTo`, the source and target supports need not agree. -/
theorem exists_target_triangle_of_refineTo_of_interior_inter_support
    (N : TriangleMesh) (T : (M.refineTo N).Triangle)
    (hhit : (interior ((M.refineTo N).triangleCarrier T.1) ∩
      N.toPlaneComplex.support).Nonempty) :
    ∃ U : N.Triangle,
      (M.refineTo N).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  exact M.exists_target_triangle_of_refineByLines_of_interior_inter_support N
    N.coordinateLines (fun _ ha => ha) T hhit

/-- Cut `M` by every face line of `N`, then retain exactly the chambers whose interiors meet
the support of `N`.  This is the unequal-support version of common refinement used in the local
Radó weld. -/
noncomputable def refineToSupport (N : TriangleMesh) : TriangleMesh :=
  by
    classical
    exact (M.refineTo N).restrictTriangles fun t ↦
      (interior ((M.refineTo N).triangleCarrier t) ∩
        N.toPlaneComplex.support).Nonempty

theorem refineToSupport_triangle_mem (N : TriangleMesh)
    {t : Finset (M.refineToSupport N).Vertex} :
    t ∈ (M.refineToSupport N).triangles ↔
      t ∈ (M.refineTo N).triangles ∧
        (interior ((M.refineTo N).triangleCarrier t) ∩
          N.toPlaneComplex.support).Nonempty := by
  classical
  exact (M.refineTo N).mem_restrictTriangles_triangles _

/-- If the source mesh contains the target support, restricting their line refinement recovers
the target support exactly. -/
theorem refineToSupport_support (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆ M.toPlaneComplex.support) :
    (M.refineToSupport N).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  classical
  let R := M.refineTo N
  let L := M.refineToSupport N
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    have htData := (M.refineToSupport_triangle_mem N).mp ht
    let T : R.Triangle := ⟨t, htData.1⟩
    obtain ⟨U, hTU⟩ :=
      M.exists_target_triangle_of_refineTo_of_interior_inter_support N T htData.2
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨U.1, Set.mem_iUnion.mpr ⟨U.2, hTU hxt⟩⟩
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    let U : N.Triangle := ⟨u, hu⟩
    have hinterior : interior (N.triangleCarrier u) ⊆
        L.toPlaneComplex.support := by
      intro y hy
      have hyN : y ∈ N.toPlaneComplex.support := by
        rw [TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion.mpr
          ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hy⟩⟩
      have hyR₀ : y ∈ (M.refineTo N).toPlaneComplex.support := by
        rw [M.refineTo_support N]
        exact hsub hyN
      have hyR : y ∈ R.toPlaneComplex.support := by
        simpa only [R] using hyR₀
      rw [TriangleMesh.toPlaneComplex_support] at hyR
      simp only [Set.mem_iUnion] at hyR
      obtain ⟨t, ht, hyt⟩ := hyR
      let T : R.Triangle := ⟨t, ht⟩
      have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
        rw [R.closure_interior_triangleCarrier T]
        exact hyt
      have hyInterClosure : y ∈ closure
          (interior (N.triangleCarrier u) ∩
            interior (R.triangleCarrier t)) :=
        isOpen_interior.inter_closure ⟨hy, hyClosure⟩
      obtain ⟨z, hzN, hzR⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
      have htKeep : t ∈ L.triangles :=
        (M.refineToSupport_triangle_mem N).mpr
          ⟨ht, ⟨z, hzR, by
            rw [TriangleMesh.toPlaneComplex_support]
            exact Set.mem_iUnion.mpr
              ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hzN⟩⟩⟩⟩
      rw [TriangleMesh.toPlaneComplex_support]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨htKeep, hyt⟩⟩
    change x ∈ N.triangleCarrier u at hxu
    rw [← N.closure_interior_triangleCarrier U] at hxu
    exact closure_minimal hinterior L.toPlaneComplex.isCompact_support.isClosed hxu

/-- The support-restricted refinement is a genuine subdivision of the smaller target mesh. -/
theorem refineToSupport_subdivides (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆ M.toPlaneComplex.support) :
    (M.refineToSupport N).toPlaneComplex.Subdivides N.toPlaneComplex := by
  constructor
  · exact M.refineToSupport_support N hsub
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := (M.refineToSupport N).mem_faces_iff.mp hs
    have htData := (M.refineToSupport_triangle_mem N).mp ht
    let T : (M.refineTo N).Triangle := ⟨t, htData.1⟩
    obtain ⟨U, hTU⟩ :=
      M.exists_target_triangle_of_refineTo_of_interior_inter_support N T htData.2
    refine ⟨U.1, N.mem_faces_iff.mpr ⟨?_, U.1, U.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [N.card_triangle U.1 U.2]; omega)
    · exact (convexHull_mono (Set.image_mono hst)).trans hTU

/-- `M.refineTo N` is a subdivision of `N` when the two meshes have the same support. -/
theorem refineTo_subdivides_right (N : TriangleMesh)
    (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support) :
    (M.refineTo N).toPlaneComplex.Subdivides N.toPlaneComplex := by
  constructor
  · exact (M.refineTo_support N).trans hsupport
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := (M.refineTo N).mem_faces_iff.mp hs
    let T : (M.refineTo N).Triangle := ⟨t, ht⟩
    obtain ⟨U, hTU⟩ := M.exists_target_triangle_of_refineTo N hsupport T
    refine ⟨U.1, N.mem_faces_iff.mpr ⟨?_, U.1, U.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [N.card_triangle U.1 U.2]; omega)
    · exact (convexHull_mono (Set.image_mono hst)).trans hTU

/-- Two finite plane triangle meshes with equal support have an explicit common subdivision. -/
theorem exists_common_subdivision (N : TriangleMesh)
    (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support) :
    ∃ R : TriangleMesh,
      R.toPlaneComplex.Subdivides M.toPlaneComplex ∧
        R.toPlaneComplex.Subdivides N.toPlaneComplex := by
  exact ⟨M.refineTo N, M.refineTo_subdivides_left N,
    M.refineTo_subdivides_right N hsupport⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Regard the two-dimensional faces of a plane complex as the maximal triangles of a mesh. -/
noncomputable def toTriangleMesh : TriangleMesh where
  Vertex := K.Vertex
  position := K.position
  position_injective := K.position_injective
  triangles := K.cells
  card_triangle := fun _ ht => K.card_of_mem_cells ht
  affineIndependent_triangle := fun t ht => K.affineIndependent t (K.mem_simplexes_of_mem_cells ht)
  triangle_inter := fun s hs t ht =>
    K.face_inter s (K.mem_simplexes_of_mem_cells hs) t (K.mem_simplexes_of_mem_cells ht)

@[simp] theorem toTriangleMesh_position : K.toTriangleMesh.position = K.position := rfl

@[simp] theorem toTriangleMesh_triangles : K.toTriangleMesh.triangles = K.cells := rfl

/-- Passing a pure two-dimensional complex to its maximal-triangle mesh preserves support. -/
theorem toTriangleMesh_support (hpure : K.IsPure2) :
    K.toTriangleMesh.toPlaneComplex.support = K.support := by
  rw [TriangleMesh.toPlaneComplex_support]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact K.cellCarrier_subset_support (K.mem_simplexes_of_mem_cells ht) hxt
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    have htcell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    exact ⟨t, htcell, convexHull_mono (Set.image_mono hst) hxs⟩

/-- The maximal-triangle mesh of a pure complex is a subdivision of the original complex. -/
theorem toTriangleMesh_toPlaneComplex_subdivides (hpure : K.IsPure2) :
    K.toTriangleMesh.toPlaneComplex.Subdivides K := by
  constructor
  · exact K.toTriangleMesh_support hpure
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := K.toTriangleMesh.mem_faces_iff.mp hs
    exact ⟨t, K.mem_simplexes_of_mem_cells ht,
      convexHull_mono (Set.image_mono hst)⟩

/-- Pure finite plane complexes with equal support have a common triangle-mesh subdivision. -/
theorem exists_common_subdivision {K L : PlaneComplex}
    (hKpure : K.IsPure2) (hLpure : L.IsPure2) (hsupport : K.support = L.support) :
    ∃ R : TriangleMesh,
      R.toPlaneComplex.Subdivides K ∧ R.toPlaneComplex.Subdivides L := by
  have hmeshSupport : K.toTriangleMesh.toPlaneComplex.support =
      L.toTriangleMesh.toPlaneComplex.support := by
    rw [K.toTriangleMesh_support hKpure, L.toTriangleMesh_support hLpure, hsupport]
  obtain ⟨R, hRK, hRL⟩ := K.toTriangleMesh.exists_common_subdivision
    L.toTriangleMesh hmeshSupport
  refine ⟨R, hRK.trans ?_, hRL.trans ?_⟩
  · constructor
    · exact K.toTriangleMesh_support hKpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := K.toTriangleMesh.mem_faces_iff.mp hs
      exact ⟨t, K.mem_simplexes_of_mem_cells ht,
        convexHull_mono (Set.image_mono hst)⟩
  · constructor
    · exact L.toTriangleMesh_support hLpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := L.toTriangleMesh.mem_faces_iff.mp hs
      exact ⟨t, L.mem_simplexes_of_mem_cells ht,
        convexHull_mono (Set.image_mono hst)⟩

end PlaneComplex

/-- An affine self-map of the plane which is injective on a set with nonempty interior is
injective everywhere. -/
theorem affineMap_injective_of_injOn_of_interior_nonempty
    (g : Plane →ᵃ[ℝ] Plane) {A : Set Plane} (hA : (interior A).Nonempty)
    (hinj : Set.InjOn g A) : Function.Injective g := by
  intro p q hpq
  by_contra hpqne
  obtain ⟨x, hx⟩ := hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let d : Plane := q - p
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpqne)
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let t : ℝ := r / (2 * ‖d‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hnorm)
  let y : Plane := t • d + x
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show y - x = t • d by simp [y]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hnormne : ‖d‖ ≠ 0 := hnorm.ne'
    field_simp [hnormne]
    nlinarith
  have hyA : y ∈ A := hball hyball
  have hxA : x ∈ A := interior_subset hx
  have hgy : g y = g x := by
    change g (t • d +ᵥ x) = g x
    rw [g.map_vadd, map_smul, show d = q -ᵥ p by rfl, g.linearMap_vsub, hpq,
      vsub_self, smul_zero, zero_vadd]
  have hyx : y = x := hinj hyA hxA hgy
  have htd : t • d = 0 := by
    change t • d + x = x at hyx
    exact add_right_cancel (hyx.trans (zero_add x).symm)
  exact hd ((smul_eq_zero.mp htd).resolve_left ht.ne')

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Map a complex through a facewise-affine map which is injective only on its support.

Unlike `mapComplex`, this construction does not require an irrelevant global injectivity
hypothesis.  The additional vertex hypothesis excludes unused vertices, whose images would not
be controlled by injectivity on the support. -/
noncomputable def mapComplexOn (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := by
    intro v w hvw
    exact K.position_injective (hinj (hvertex v) (hvertex w) hvw)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    by_cases hcard : s.card ≤ 2
    · let A : Finset Plane := s.image (f ∘ K.position)
      have hAcard : A.card ≤ 2 := Finset.card_image_le.trans hcard
      let e : s ↪ A :=
        { toFun := fun v =>
            ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
          inj' := by
            intro v w hvw
            apply Subtype.ext
            apply K.position_injective
            apply hinj (hvertex v) (hvertex w)
            exact congrArg Subtype.val hvw }
      exact (affineIndependent_finset_of_card_le_two A hAcard).comp_embedding e
    · have hcard3 : s.card = 3 := by
        have := K.card_le_three s hs
        omega
      obtain ⟨g, hfg⟩ := haffine s hs
      have hinterior : (interior (K.cellCarrier s)).Nonempty := by
        rw [PlaneComplex.cellCarrier]
        have hrange : Set.range (fun v : s => K.position v) =
            K.position '' (s : Set K.Vertex) := by
          ext x
          simp
        rw [← hrange]
        apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
        exact ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
          (by simp [hcard3, Plane])
      have hgInjOn : Set.InjOn g (K.cellCarrier s) := by
        intro x hx y hy hxy
        apply hinj (K.cellCarrier_subset_support hs hx) (K.cellCarrier_subset_support hs hy)
        rw [hfg hx, hfg hy]
        exact hxy
      have hgInj : Function.Injective g :=
        affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
      have hmap := (K.affineIndependent s hs).map' g hgInj
      convert hmap using 1
      funext v
      simpa only [Function.comp_apply] using
        hfg (subset_convexHull ℝ _ ⟨v, v.2, rfl⟩)
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hsource : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hsource]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

theorem mapComplexOn_cellCarrier (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapComplexOn f hvertex hinj haffine).cellCarrier s =
      f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

theorem mapComplexOn_support (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplexOn f hvertex hinj haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapComplexOn_cellCarrier f hvertex hinj haffine hs] at hxs
    obtain ⟨y, hys, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hys⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hys⟩, rfl⟩
    exact ⟨s, hs, by
      rw [K.mapComplexOn_cellCarrier f hvertex hinj haffine hs]
      exact ⟨y, hys, rfl⟩⟩

theorem IsPure2.mapComplexOn (hpure : K.IsPure2) (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplexOn f hvertex hinj haffine).IsPure2 := by
  intro s hs
  exact hpure s hs

/-- Map every face of a finite plane complex through a facewise-affine embedding. -/
noncomputable def mapComplex (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := by
    intro v w hvw
    exact K.position_injective (hinj hvw)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    by_cases hcard : s.card ≤ 2
    · let A : Finset Plane := s.image (f ∘ K.position)
      have hAcard : A.card ≤ 2 := (Finset.card_image_le.trans hcard)
      have hAI := affineIndependent_finset_of_card_le_two A hAcard
      let e : s ↪ A :=
        { toFun := fun v => ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
          inj' := by
            intro v w hvw
            apply Subtype.ext
            apply K.position_injective
            apply hinj
            exact congrArg Subtype.val hvw }
      exact hAI.comp_embedding e
    · have hcard3 : s.card = 3 := by
        have := K.card_le_three s hs
        omega
      obtain ⟨g, hfg⟩ := haffine s hs
      have hinterior : (interior (K.cellCarrier s)).Nonempty := by
        rw [PlaneComplex.cellCarrier]
        have hrange : Set.range (fun v : s => K.position v) =
            K.position '' (s : Set K.Vertex) := by
          ext x
          simp
        rw [← hrange]
        apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
        exact ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
          (by simp [hcard3, Plane])
      have hgInjOn : Set.InjOn g (K.cellCarrier s) := by
        intro x hx y hy hxy
        apply hinj
        rw [hfg hx, hfg hy]
        exact hxy
      have hgInj : Function.Injective g :=
        affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
      have hmap := (K.affineIndependent s hs).map' g hgInj
      convert hmap using 1
      funext v
      simpa only [Function.comp_apply] using
        hfg (subset_convexHull ℝ _ ⟨v, v.2, rfl⟩)
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.injOn.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hsource : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hsource]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

theorem mapComplex_cellCarrier (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapComplex f hinj haffine).cellCarrier s = f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

theorem mapComplex_support (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplex f hinj haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapComplex_cellCarrier f hinj haffine hs] at hxs
    obtain ⟨y, hys, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hys⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hys⟩, rfl⟩
    exact ⟨s, hs, by
      rw [K.mapComplex_cellCarrier f hinj haffine hs]
      exact ⟨y, hys, rfl⟩⟩

theorem IsPure2.mapComplex (hpure : K.IsPure2) (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplex f hinj haffine).IsPure2 := by
  intro s hs
  exact hpure s hs

/-- On every subdivision of the image complex, the inverse homeomorphism is affine facewise.
The proof enlarges each image face to a 2-face, where its affine witness is globally invertible. -/
theorem inverse_affineOn_of_subdivides_mapComplex
    (hpure : K.IsPure2) (h : Plane ≃ₜ Plane)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn h (K.cellCarrier s))
    {R : PlaneComplex}
    (hR : R.Subdivides (K.mapComplex h h.injective haffine)) :
    ∀ s ∈ R.simplexes, IsAffineOn h.symm (R.cellCarrier s) := by
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hR.2 s hs
  obtain ⟨t, ht, hut, htcard⟩ := hpure u hu
  have htcell : t ∈ K.simplexes := ht
  have hutCarrier :
      (K.mapComplex h h.injective haffine).cellCarrier u ⊆
        (K.mapComplex h h.injective haffine).cellCarrier t :=
    convexHull_mono (Set.image_mono hut)
  have hsTarget : R.cellCarrier s ⊆ h '' K.cellCarrier t := by
    exact hsu.trans (hutCarrier.trans_eq
      (K.mapComplex_cellCarrier h h.injective haffine htcell))
  obtain ⟨g, hgh⟩ := haffine t htcell
  have hinterior : (interior (K.cellCarrier t)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have hrange : Set.range (fun v : t => K.position v) =
        K.position '' (t : Set K.Vertex) := by
      ext x
      simp
    rw [← hrange]
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exact ((K.affineIndependent t htcell).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
      (by simp [htcard, Plane])
  have hgInjOn : Set.InjOn g (K.cellCarrier t) := by
    intro x hx y hy hxy
    apply h.injective
    rw [hgh hx, hgh hy]
    exact hxy
  have hgInj : Function.Injective g :=
    affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
  have hgLinearInj : Function.Injective g.linear := g.linear_injective_iff.mpr hgInj
  have hgLinearSurj : Function.Surjective g.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hgLinearInj
  have hgBij : Function.Bijective g := g.linear_bijective_iff.mp
    ⟨hgLinearInj, hgLinearSurj⟩
  let e : Plane ≃ᵃ[ℝ] Plane := AffineEquiv.ofBijective hgBij
  refine ⟨e.symm.toAffineMap, fun y hy => ?_⟩
  obtain ⟨x, hxt, hxy⟩ := hsTarget hy
  subst y
  change h.symm (h x) = e.symm (h x)
  rw [h.symm_apply_apply, hgh hxt]
  exact (e.symm_apply_apply x).symm

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_02
/- END ClassificationOfSurfaces.Moise.CommonSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.FreeTriangleMove | 8b37afc857119ad493869d06f06c8c59c6aff251ccbb0e1c13b3d1a3fe91559a -/
section schottkyclassification06_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The supported move at a free triangle

This file transports the normalized thin-kite move to an arbitrary plane triangle.  Compactness
supplies the small positive thickness required by the relative polygonal Schoenflies theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An affine equivalence of the plane, regarded as a homeomorphism. -/
noncomputable def affineEquivHomeomorph (e : Plane ≃ᵃ[ℝ] Plane) : Plane ≃ₜ Plane where
  toEquiv := e.toEquiv
  continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
  continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional

@[simp] theorem affineEquivHomeomorph_apply (e : Plane ≃ᵃ[ℝ] Plane) (p : Plane) :
    affineEquivHomeomorph e p = e p := rfl

@[simp] theorem affineEquivHomeomorph_symm_apply (e : Plane ≃ᵃ[ℝ] Plane) (p : Plane) :
    (affineEquivHomeomorph e).symm p = e.symm p := rfl

theorem affineEquivHomeomorph_image_segment (e : Plane ≃ᵃ[ℝ] Plane) (a b : Plane) :
    affineEquivHomeomorph e '' segment ℝ a b = segment ℝ (e a) (e b) := by
  exact image_segment ℝ e.toAffineMap a b

/-- Conjugate the normalized kite move by an affine coordinate system. -/
noncomputable def transportedThinKiteHomeomorph (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane :=
  (affineEquivHomeomorph e).symm.trans
    ((thinKiteAmbientHomeomorph δ hδ).trans (affineEquivHomeomorph e))

/-- The `transportedThinKitePatch` declaration. -/
def transportedThinKitePatch (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) : Set Plane :=
  e '' thinKitePatch δ

theorem transportedThinKiteHomeomorph_eqOn_compl (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) :
    Set.EqOn (transportedThinKiteHomeomorph e δ hδ) id
      (transportedThinKitePatch e δ)ᶜ := by
  intro p hp
  have hpre : e.symm p ∉ thinKitePatch δ := by
    intro hmem
    apply hp
    exact ⟨e.symm p, hmem, by simp⟩
  rw [transportedThinKiteHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    affineEquivHomeomorph_symm_apply,
    thinKiteAmbientHomeomorph_eqOn_compl δ hδ hpre]
  simp

theorem transportedThinKiteHomeomorph_image_baseSegment (e : Plane ≃ᵃ[ℝ] Plane)
    (δ : ℝ) (hδ : 0 < δ) :
    transportedThinKiteHomeomorph e δ hδ ''
        segment ℝ (e (planePoint (-1) 0)) (e (planePoint 1 0)) =
      segment ℝ (e (planePoint (-1) 0)) (e (planePoint 0 1)) ∪
        segment ℝ (e (planePoint 1 0)) (e (planePoint 0 1)) := by
  have hsegment (a b : Plane) :
      segment ℝ (e a) (e b) = e '' segment ℝ a b := by
    exact (image_segment ℝ e.toAffineMap a b).symm
  rw [hsegment, hsegment, hsegment, ← Set.image_union,
    ← thinKiteAmbientHomeomorph_image_baseSegment δ hδ]
  ext p
  simp [transportedThinKiteHomeomorph, Set.mem_image]

/-- A sufficiently thin transported kite lies in every open neighborhood of its limiting
triangle. -/
theorem exists_thinKitePatch_subset_open (e : Plane ≃ᵃ[ℝ] Plane)
    (U : Set Plane) (hU : IsOpen U)
    (htriangle : e '' convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ transportedThinKitePatch e δ ⊆ U := by
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  have hcontinuous : Continuous fun z : ℝ × Plane => e (thinKiteMap z.1 z.2) := by
    apply e.toAffineMap.continuous_of_finiteDimensional.comp
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop
  have heventually : ∀ᶠ δ in nhds (0 : ℝ),
      ∀ q ∈ diamondPatch, e (thinKiteMap δ q) ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro q hq
    apply hcontinuous.continuousAt.eventually
    apply hU.mem_nhds
    apply htriangle
    exact ⟨thinKiteMap 0 q, thinKiteMap_zero_mem_triangle hq, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [δ]
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  obtain ⟨r, ⟨q, hq, rfl⟩, rfl⟩ := hp
  exact hball hδball q hq

/-- Uniform version of `exists_thinKitePatch_subset_open`: every smaller positive thickness
also lies in the prescribed open set. -/
theorem exists_eventually_transportedThinKitePatch_subset_open
    (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (hU : IsOpen U)
    (htriangle : e '' convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch e δ ⊆ U := by
  have hopen : IsOpen (e ⁻¹' U) := hU.preimage e.toAffineMap.continuous_of_finiteDimensional
  have hpre : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ e ⁻¹' U := by
    intro p hp
    exact htriangle ⟨p, hp, rfl⟩
  obtain ⟨ε, hε, hpatch⟩ :=
    exists_thinKitePatch_subset_open_normalized (e ⁻¹' U) hopen hpre
  refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hp
  exact hpatch δ hδ hδε hq

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Order a triangle so that index `2` is a specified opposite vertex. -/
noncomputable def freeTriangleOrder (T : M.Triangle) (k : Fin 3) : Fin 3 → Plane :=
  fun i => M.position (M.orderedVertex T ((Equiv.swap 2 k) i))

theorem freeTriangleOrder_affineIndependent (T : M.Triangle) (k : Fin 3) :
    AffineIndependent ℝ (M.freeTriangleOrder T k) := by
  exact (M.orderedVertex_affineIndependent T).comp_embedding (Equiv.swap 2 k).toEmbedding

theorem range_freeTriangleOrder (T : M.Triangle) (k : Fin 3) :
    Set.range (M.freeTriangleOrder T k) = M.position '' (T.1 : Set M.Vertex) := by
  change Set.range ((M.position ∘ M.orderedVertex T) ∘ Equiv.swap 2 k) = _
  rw [EquivLike.range_comp]
  rw [Set.range_comp, M.range_orderedVertex T]

theorem triangle_eq_orderedVertices (T : M.Triangle) :
    T.1 = {M.orderedVertex T 0, M.orderedVertex T 1, M.orderedVertex T 2} := by
  ext v
  constructor
  · intro hv
    have hvRange : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact hv
    obtain ⟨i, rfl⟩ := hvRange
    fin_cases i <;> simp
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact M.orderedVertex_mem T 0
    · exact M.orderedVertex_mem T 1
    · exact M.orderedVertex_mem T 2

theorem triangleEdges_eq_orderedEdges (T : M.Triangle) :
    M.triangleEdges T.1 =
      {{M.orderedVertex T 0, M.orderedVertex T 1},
        {M.orderedVertex T 0, M.orderedVertex T 2},
        {M.orderedVertex T 1, M.orderedVertex T 2}} := by
  rw [triangleEdges, M.triangle_eq_orderedVertices T]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  ext e
  rw [Finset.mem_powersetCard]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hesub, hecard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
    have ha := hesub (by simp : a ∈ ({a, b} : Finset M.Vertex))
    have hb := hesub (by simp : b ∈ ({a, b} : Finset M.Vertex))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
  · intro he
    rcases he with rfl | rfl | rfl
    all_goals
      constructor
      · simp
      · simp_all

/-- Moise's first free-triangle case: the frontier meets the triangle in exactly its base edge. -/
def IsOneEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1)

/-- Moise's second free-triangle case: the frontier meets the triangle in exactly the two edges
through the apex. -/
def IsTwoEdgeFreeTriangle (T : M.Triangle) (k : Fin 3) : Prop :=
  frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)

/-- The `IsGeometricallyFreeTriangle` declaration. -/
def IsGeometricallyFreeTriangle (T : M.Triangle) : Prop :=
  ∃ k : Fin 3, M.IsOneEdgeFreeTriangle T k ∨ M.IsTwoEdgeFreeTriangle T k

/-- The relative interior of the base in the Figure 3.3 ordering misses both apex edges. -/
theorem freeTriangleBase_diff_endpoints_disjoint_apexEdges (T : M.Triangle) (k : Fin 3) :
    Disjoint
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) \
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1})
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  have habc : AffineIndependent ℝ ![a, b, c] := by
    convert M.freeTriangleOrder_affineIndependent T k using 1
    funext i
    fin_cases i <;> rfl
  have hbac : AffineIndependent ℝ ![b, a, c] := by
    convert habc.comp_embedding (Equiv.swap (0 : Fin 3) 1).toEmbedding using 1
    funext i
    fin_cases i <;> rfl
  have h0 : segment ℝ a b ∩ segment ℝ a c = {a} := by
    simpa only [segment_symm ℝ b a] using
      (segment_inter_segment_of_affineIndependent (x := b) (y := a) (z := c) hbac)
  have h1 : segment ℝ a b ∩ segment ℝ b c = {b} :=
    segment_inter_segment_of_affineIndependent (x := a) (y := b) (z := c) habc
  rw [Set.disjoint_left]
  change ∀ ⦃x⦄, x ∈ segment ℝ a b \ {a, b} →
    x ∈ segment ℝ a c ∪ segment ℝ b c → False
  rintro x ⟨hxBase, hxEnds⟩ (hxApex0 | hxApex1)
  · have hx : x ∈ ({a} : Set Plane) := by
      rw [← h0]
      exact ⟨hxBase, hxApex0⟩
    exact hxEnds (Or.inl (Set.mem_singleton_iff.mp hx))
  · have hx : x ∈ ({b} : Set Plane) := by
      rw [← h1]
      exact ⟨hxBase, hxApex1⟩
    exact hxEnds (Or.inr (Set.mem_singleton_iff.mp hx))

/-- The abstract mesh edge underlying the base in the Figure 3.3 ordering. -/
noncomputable def freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  (Finset.univ.erase k).image (M.orderedVertex T)

/-- The first abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge0 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 0),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

/-- The second abstract edge from a base endpoint to the apex. -/
noncomputable def freeTriangleApexEdge1 (T : M.Triangle) (k : Fin 3) : Finset M.Vertex :=
  {M.orderedVertex T ((Equiv.swap 2 k) 1),
    M.orderedVertex T ((Equiv.swap 2 k) 2)}

theorem freeTriangleBaseEdge_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleBaseEdge T k).card = 2 := by
  rw [freeTriangleBaseEdge, Finset.card_image_of_injective _ (M.orderedVertex_injective T),
    Finset.card_erase_of_mem (Finset.mem_univ k)]
  decide

theorem freeTriangleBaseEdge_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ⊆ T.1 := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact M.orderedVertex_mem T i

theorem freeTriangleBaseEdge_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleBaseEdge_subset T k, M.freeTriangleBaseEdge_card T k⟩⟩

theorem freeTriangleApexEdge0_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge0 T k).card = 2 := by
  rw [freeTriangleApexEdge0, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge1_card (T : M.Triangle) (k : Fin 3) :
    (M.freeTriangleApexEdge1 T k).card = 2 := by
  rw [freeTriangleApexEdge1, Finset.card_pair]
  exact (M.orderedVertex_injective T).ne <| (Equiv.swap 2 k).injective.ne (by decide)

theorem freeTriangleApexEdge0_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge0 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge0, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem freeTriangleApexEdge1_subset (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge1 T k ⊆ T.1 := by
  intro v hv
  simp only [freeTriangleApexEdge1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact M.orderedVertex_mem T _

theorem freeTriangleApexEdge0_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge0 T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleApexEdge0_subset T k, M.freeTriangleApexEdge0_card T k⟩⟩

theorem freeTriangleApexEdge1_mem_edges (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleApexEdge1 T k ∈ M.edges := by
  apply Finset.mem_biUnion.mpr
  exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr
    ⟨M.freeTriangleApexEdge1_subset T k, M.freeTriangleApexEdge1_card T k⟩⟩

theorem image_freeTriangleBaseEdge (T : M.Triangle) (k : Fin 3) :
    M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex) =
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  rw [Finset.image_insert, Finset.image_singleton]
  ext p
  simp [freeTriangleOrder, eq_comm]

theorem freeTriangleBaseEdge_eq_orderedPair (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleBaseEdge T k =
      {M.orderedVertex T ((Equiv.swap 2 k) 0),
        M.orderedVertex T ((Equiv.swap 2 k) 1)} := by
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  rw [Finset.image_insert, Finset.image_singleton]

theorem freeTriangleBaseEdge_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  rw [M.image_freeTriangleBaseEdge T k, convexHull_pair]

theorem freeTriangleApexEdge0_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge0 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge0, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem freeTriangleApexEdge1_carrier (T : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex)) =
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  rw [show M.position '' (M.freeTriangleApexEdge1 T k : Set M.Vertex) =
    {M.freeTriangleOrder T k 1, M.freeTriangleOrder T k 2} by
      ext p
      simp [freeTriangleApexEdge1, freeTriangleOrder, eq_comm]]
  exact convexHull_pair _ _

theorem triangleEdges_eq_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    M.triangleEdges T.1 =
      {M.freeTriangleBaseEdge T k, M.freeTriangleApexEdge0 T k,
        M.freeTriangleApexEdge1 T k} := by
  rw [M.triangleEdges_eq_orderedEdges T]
  have hindices : (Finset.univ.erase k : Finset (Fin 3)) =
      {(Equiv.swap 2 k) 0, (Equiv.swap 2 k) 1} := by
    fin_cases k <;> decide
  rw [freeTriangleBaseEdge, hindices]
  fin_cases k
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.zero_eta, Equiv.swap_apply_right,
      Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero,
      Finset.image_insert, Finset.image_singleton, freeTriangleApexEdge0,
      freeTriangleApexEdge1]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
      ↓reduceIte, zero_ne_one, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]
    have h10 : ({M.orderedVertex T 1, M.orderedVertex T 0} : Finset M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 1} := Finset.pair_comm _ _
    rw [h10]
    tauto
  · ext e
    simp only [Fin.isValue, Finset.pair_comm, Finset.mem_insert,
      Finset.mem_singleton, Fin.reduceFinMk, Equiv.swap_self,
      Equiv.refl_apply, Finset.image_insert, Finset.image_singleton,
      freeTriangleApexEdge0, freeTriangleApexEdge1]

/-- Every triangle vertex lies on one of the two apex edges. -/
theorem triangleVertex_mem_freeTriangleApexEdges (T : M.Triangle) (k : Fin 3)
    {v : M.Vertex} (hv : v ∈ T.1) :
    M.position v ∈
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  have hvRange : v ∈ Set.range (M.orderedVertex T) := by
    rw [M.range_orderedVertex T]
    exact hv
  obtain ⟨i, rfl⟩ := hvRange
  fin_cases k <;> fin_cases i <;>
    simp [freeTriangleOrder, Equiv.swap_apply_def, left_mem_segment,
      right_mem_segment]

-- Normalizing all six finite-order cases for the three geometric edges exceeds the default.
/-- The frontier of a maximal triangle is covered by the base and the two apex edges in every
Figure 3.3 ordering. -/
theorem frontier_triangleCarrier_subset_freeTriangleEdges (T : M.Triangle) (k : Fin 3) :
    frontier (M.triangleCarrier T.1) ⊆
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
        (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) := by
  intro p hp
  obtain ⟨e, hecard, heT, hpe⟩ := M.exists_edge_of_mem_frontier_triangle T.2 hp
  have he : e ∈ M.triangleEdges T.1 :=
    Finset.mem_powersetCard.mpr ⟨heT, hecard⟩
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext q; simp [eq_comm]]
    exact convexHull_pair _ _
  rw [M.triangleEdges_eq_orderedEdges T] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  have hpEdges : p ∈
      segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
        (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
          segment ℝ (M.position (M.orderedVertex T 1))
            (M.position (M.orderedVertex T 2))) := by
    rcases he with rfl | rfl | rfl
    · rw [hcarrier] at hpe
      exact Or.inl hpe
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inl hpe)
    · rw [hcarrier] at hpe
      exact Or.inr (Or.inr hpe)
  have horder :
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ∪
          (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) =
        segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 1)) ∪
          (segment ℝ (M.position (M.orderedVertex T 0)) (M.position (M.orderedVertex T 2)) ∪
            segment ℝ (M.position (M.orderedVertex T 1))
              (M.position (M.orderedVertex T 2))) := by
    ext x
    simp only [Set.mem_union]
    have hsymm (a b : Plane) : x ∈ segment ℝ a b ↔ x ∈ segment ℝ b a := by
      rw [segment_symm]
    have h01 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))
    have h02 := hsymm (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 2))
    have h12 := hsymm (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))
    fin_cases k
    · simp only [freeTriangleOrder, Fin.isValue, Fin.zero_eta, Equiv.swap_apply_right,
        Equiv.swap_apply_def, Fin.reduceEq, ↓reduceIte, one_ne_zero]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h12.mpr h))
        · exact Or.inr (Or.inl (h02.mpr h))
        · exact Or.inl (h01.mpr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (h01.mp h))
        · exact Or.inr (Or.inl (h02.mp h))
        · exact Or.inl (h12.mp h)
    · simp only [freeTriangleOrder, Fin.isValue, Fin.mk_one, Equiv.swap_apply_def, Fin.reduceEq,
        ↓reduceIte, zero_ne_one]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mpr h))
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (h12.mp h))
    · simp [freeTriangleOrder]
  rwa [horder]

theorem freeTriangleBaseSegment_eq_oppositeEdgeCarrier (T : M.Triangle) (k : Fin 3) :
    segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
      convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
  fin_cases k
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 2))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (0 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide]
    simp [convexHull_pair, segment_symm]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 2)) =
      convexHull ℝ (((Finset.univ.erase (1 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide]
    simp [convexHull_pair]
  · unfold freeTriangleOrder oppositeEdgePoints
    change segment ℝ (M.position (M.orderedVertex T 0))
        (M.position (M.orderedVertex T 1)) =
      convexHull ℝ (((Finset.univ.erase (2 : Fin 3)).image
        (M.position ∘ M.orderedVertex T) : Finset Plane) : Set Plane)
    rw [show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide]
    simp [convexHull_pair]

theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_one (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 1) :
    M.IsGeometricallyFreeTriangle T := by
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2.1
  refine ⟨k, Or.inl ?_⟩
  rw [IsOneEdgeFreeTriangle, M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices,
    hboundary]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [M.freeTriangleBaseSegment_eq_oppositeEdgeCarrier T k, hedge, Finset.coe_image]

/-- Moise's second free-triangle case: if exactly two edges of a triangle lie on the mesh
frontier, their common endpoint can be chosen as the apex of the Figure 3.3 move. -/
theorem isGeometricallyFreeTriangle_of_boundaryEdges_card_two (T : M.Triangle)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1)
    (hcard : (M.boundaryEdges T.1).card = 2) :
    M.IsGeometricallyFreeTriangle T := by
  have hproper : M.boundaryEdges T.1 ⊂ M.triangleEdges T.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨M.boundaryEdges_subset_triangleEdges T.1, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    rw [hcard, M.card_triangleEdges T.2] at this
    omega
  obtain ⟨e, heTriangle, heBoundary⟩ := Finset.exists_of_ssubset hproper
  have heData := Finset.mem_powersetCard.mp heTriangle
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T heData.1 heData.2
  have hboundary : M.boundaryEdges T.1 = (M.triangleEdges T.1).erase e := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      exact Finset.mem_erase.mpr
        ⟨fun hde => heBoundary (hde ▸ hd), M.boundaryEdges_subset_triangleEdges T.1 hd⟩
    · rw [hcard, Finset.card_erase_of_mem heTriangle, M.card_triangleEdges T.2]
  have h01 : M.orderedVertex T 0 ≠ M.orderedVertex T 1 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h02 : M.orderedVertex T 0 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have h12 : M.orderedVertex T 1 ≠ M.orderedVertex T 2 :=
    (M.orderedVertex_injective T).ne (by decide)
  have hEdge01Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge02Edge12 :
      {M.orderedVertex T 0, M.orderedVertex T 2} ≠
        ({M.orderedVertex T 1, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 2} : Set M.Vertex) =
        {M.orderedVertex T 1, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h01 h'.1) (fun h' => h02 h'.1)
  have hEdge01Edge02 :
      {M.orderedVertex T 0, M.orderedVertex T 1} ≠
        ({M.orderedVertex T 0, M.orderedVertex T 2} : Finset M.Vertex) := by
    intro h
    have hs : ({M.orderedVertex T 0, M.orderedVertex T 1} : Set M.Vertex) =
        {M.orderedVertex T 0, M.orderedVertex T 2} := by
      simpa using congrArg (fun d : Finset M.Vertex => (d : Set M.Vertex)) h
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h' => h12 h'.2) (fun h' => h02 h'.1)
  have hcarrier (a b : M.Vertex) :
      convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hUnion (a b : Finset M.Vertex) :
      (⋃ d ∈ ({a, b} : Finset (Finset M.Vertex)),
        convexHull ℝ (M.position '' (d : Set M.Vertex))) =
        convexHull ℝ (M.position '' (a : Set M.Vertex)) ∪
          convexHull ℝ (M.position '' (b : Set M.Vertex)) := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, Set.mem_union]
    constructor
    · rintro ⟨d, rfl | rfl, hp⟩
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨a, Or.inl rfl, hp⟩
      · exact ⟨b, Or.inr rfl, hp⟩
  refine ⟨k, Or.inr ?_⟩
  rw [IsTwoEdgeFreeTriangle,
    M.frontier_inter_triangleCarrier_eq_boundaryEdges T.2 hvertices, hboundary]
  fin_cases k
  · have he : e = {M.orderedVertex T 1, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (0 : Fin 3)) = _
      rw [show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 1, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 0, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hne rfl).elim
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge12, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12, Or.inr (Or.inl rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder, segment_symm, Equiv.swap_apply_def, Set.union_comm]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 2} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (1 : Fin 3)) = _
      rw [show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 2} =
          {{M.orderedVertex T 0, M.orderedVertex T 1},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (hne rfl).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02, Or.inl rfl⟩
        · exact ⟨hEdge02Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp only [freeTriangleOrder]
    simp only [Equiv.swap_apply_def]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one, zero_ne_one]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 0))
      (M.position (M.orderedVertex T 1))]
    rw [segment_symm ℝ (M.position (M.orderedVertex T 1))
      (M.position (M.orderedVertex T 2))]
  · have he : e = {M.orderedVertex T 0, M.orderedVertex T 1} := by
      apply Finset.image_injective M.position_injective
      rw [← hedge]
      change Finset.image (M.position ∘ M.orderedVertex T)
          (Finset.univ.erase (2 : Fin 3)) = _
      rw [show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
      simp
    rw [he, M.triangleEdges_eq_orderedEdges T]
    have herase :
        ({{M.orderedVertex T 0, M.orderedVertex T 1},
          {M.orderedVertex T 0, M.orderedVertex T 2},
          {M.orderedVertex T 1, M.orderedVertex T 2}} : Finset (Finset M.Vertex)).erase
            {M.orderedVertex T 0, M.orderedVertex T 1} =
          {{M.orderedVertex T 0, M.orderedVertex T 2},
            {M.orderedVertex T 1, M.orderedVertex T 2}} := by
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl | rfl⟩
        · exact (hne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hEdge01Edge02.symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨hEdge01Edge12.symm, Or.inr (Or.inr rfl)⟩
    rw [herase]
    rw [hUnion]
    rw [hcarrier, hcarrier]
    simp [freeTriangleOrder]

/-- The finite conclusion used by Moise's cutting induction.  Once a weakly free triangle has
an edge-neighbor and no isolated frontier vertex, its frontier trace is one of the two
configurations in Figure 3.3. -/
theorem isGeometricallyFreeTriangle_of_isFreeTriangle
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hvertices : M.HasNoIsolatedFrontierVertex T.1) :
    M.IsGeometricallyFreeTriangle T := by
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  rcases hcases with hcard | hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_one T hvertices hcard
  · exact M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two T hvertices hcard

/-- The exact diagonal configuration in the hard branch of Moise Chapter 3, Theorem 3.  If a
weakly free triangle is not one of the Figure 3.3 configurations, it has one boundary edge and
an isolated opposite boundary vertex; the other two edges are the cutting diagonals. -/
theorem exists_cutting_diagonal_configuration
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a b v : M.Vertex,
      a ≠ b ∧ v ≠ a ∧ v ≠ b ∧
      T.1 = {a, b, v} ∧ M.boundaryEdges T.1 = {{a, b}} ∧
      M.position v ∈ frontier M.toPlaneComplex.support := by
  rw [HasNoIsolatedFrontierVertex] at hnot
  push Not at hnot
  obtain ⟨v, hvFrontier, hvTriangle, hvBoundary⟩ := hnot
  have hvT : v ∈ T.1 :=
    M.vertex_mem_triangle_of_frontier_not_mem_boundaryEdges T v hvFrontier hvTriangle hvBoundary
  have hnonempty := M.boundaryEdges_nonempty_of_isFreeTriangle hfree
  have hle : (M.boundaryEdges T.1).card ≤ 2 :=
    M.card_boundaryEdges_le_two_of_neighbor T.2 U.2 hne hneighbors
  have hcardCases : (M.boundaryEdges T.1).card = 1 ∨
      (M.boundaryEdges T.1).card = 2 := by
    have hpos : 0 < (M.boundaryEdges T.1).card := Finset.card_pos.mpr hnonempty
    omega
  have hcard : (M.boundaryEdges T.1).card = 1 := by
    rcases hcardCases with hcard | hcard
    · exact hcard
    · exfalso
      obtain ⟨e, f, hef, hboundary⟩ := Finset.card_eq_two.mp hcard
      have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have hfMem : f ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
      have heData := M.mem_boundaryEdges_iff.mp heMem
      have hfData := M.mem_boundaryEdges_iff.mp hfMem
      have hvNotE : v ∉ e := by
        intro hve
        exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
      have hvNotF : v ∉ f := by
        intro hvf
        exact hvBoundary f hfMem (subset_convexHull ℝ _ ⟨v, hvf, rfl⟩)
      have heraseCard : (T.1.erase v).card = 2 := by
        rw [Finset.card_erase_of_mem hvT, M.card_triangle T.1 T.2]
      have heErase : e = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotE (hwv ▸ hw), heData.1 hw⟩)
          (by rw [heData.2.1, heraseCard])
      have hfErase : f = T.1.erase v :=
        Finset.eq_of_subset_of_card_le
          (fun w hw => Finset.mem_erase.mpr ⟨fun hwv => hvNotF (hwv ▸ hw), hfData.1 hw⟩)
          (by rw [hfData.2.1, heraseCard])
      exact hef (heErase.trans hfErase.symm)
  obtain ⟨e, hboundary⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  have hvNotE : v ∉ e := by
    intro hve
    exact hvBoundary e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp heData.2.1
  have hva : v ≠ a := fun h => hvNotE (h ▸ by simp)
  have hvb : v ≠ b := fun h => hvNotE (h ▸ by simp)
  have htriangle : T.1 = {a, b, v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact heData.1 (by simp)
      · exact heData.1 (by simp)
      · exact hvT
    · rw [M.card_triangle T.1 T.2]
      have hcardTriple : ({a, b, v} : Finset M.Vertex).card = 3 := by
        simp [hab, Ne.symm hva, Ne.symm hvb]
      omega
  exact ⟨a, b, v, hab, hva, hvb, htriangle, hboundary, hvFrontier⟩

/-- Affine coordinates taking the normalized kite triangle to `T`. -/
noncomputable def freeTriangleAffineEquiv (T : M.Triangle) (k : Fin 3) : Plane ≃ᵃ[ℝ] Plane :=
  triangleAffineEquiv kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k)

@[simp] theorem freeTriangleAffineEquiv_apply_vertex (T : M.Triangle) (k i : Fin 3) :
    M.freeTriangleAffineEquiv T k (kiteTrianglePosition i) = M.freeTriangleOrder T k i := by
  exact triangleAffineEquiv_apply kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k) i

theorem freeTriangleAffineEquiv_image_triangle (T : M.Triangle) (k : Fin 3) :
    M.freeTriangleAffineEquiv T k '' convexHull ℝ (Set.range kiteTrianglePosition) =
      M.triangleCarrier T.1 := by
  rw [triangleCarrier, ← M.range_freeTriangleOrder T k]
  exact triangleAffineEquiv_image_convexHull kiteTrianglePosition (M.freeTriangleOrder T k)
    kiteTrianglePosition_affineIndependent (M.freeTriangleOrder_affineIndependent T k)

/-- Every boundary edge other than the base of a one-edge move is avoided by all sufficiently
thin transported kites, except possibly at the two base endpoints. -/
theorem exists_transportedThinKitePatch_inter_boundaryEdge_subset_baseEndpoints
    (T : M.Triangle) (k : Fin 3)
    (htrace : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
    (e : Finset M.Vertex) (he : M.IsBoundaryEdge e)
    (hne : e ≠ M.freeTriangleBaseEdge T k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch (M.freeTriangleAffineEquiv T k) δ ∩
          convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
        {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  have hecard := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  let a := E.symm (M.position v)
  let b := E.symm (M.position w)
  have hab : a ≠ b := by
    intro hab
    apply hvw
    apply M.position_injective
    simpa [a, b] using congrArg E hab
  have hcarrier :
      convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) =
        segment ℝ (M.position v) (M.position w) := by
    rw [show M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hsegmentImage : E '' segment ℝ a b =
      segment ℝ (M.position v) (M.position w) := by
    calc
      E '' segment ℝ a b = segment ℝ (E a) (E b) :=
        image_segment ℝ E.toAffineMap a b
      _ = segment ℝ (M.position v) (M.position w) := by simp [a, b]
  have hbaseEdge := M.freeTriangleBaseEdge_mem_edges T k
  have hcommonCard :
      (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).card ≤ 1 := by
    by_contra hcard
    have hcardTwo :
        (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).card = 2 := by
      have hle := Finset.card_le_card
        (Finset.inter_subset_left : ({v, w} : Finset M.Vertex) ∩
          M.freeTriangleBaseEdge T k ⊆ {v, w})
      simp [hvw] at hle
      omega
    have heqLeft : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k = {v, w} :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by simp [hvw, hcardTwo])
    have heqRight : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k =
        M.freeTriangleBaseEdge T k :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcardTwo, M.freeTriangleBaseEdge_card T k])
    exact hne (heqLeft.symm.trans heqRight)
  have hinter : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
      {planePoint (-1) 0, planePoint 1 0} := by
    intro p hp
    have hpEdge : E p ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage]
      exact ⟨p, hp.1, rfl⟩
    have hpTriangle : E p ∈ M.triangleCarrier T.1 := by
      rw [← M.freeTriangleAffineEquiv_image_triangle T k]
      exact ⟨p, hp.2, rfl⟩
    have hpFrontier := M.boundaryEdgeCarrier_subset_frontier he hpEdge
    have hpBase : E p ∈ convexHull ℝ
        (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) := by
      rw [M.freeTriangleBaseEdge_carrier T k, ← htrace]
      exact ⟨hpFrontier, hpTriangle⟩
    have hpCommon : E p ∈ convexHull ℝ
        (M.position '' ((({v, w} : Finset M.Vertex) ∩
          M.freeTriangleBaseEdge T k : Finset M.Vertex) : Set M.Vertex)) := by
      rw [← M.edgeCarrier_inter_edgeCarrier he.1 hbaseEdge]
      exact ⟨hpEdge, hpBase⟩
    obtain hempty | hnonempty :=
        (({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k).eq_empty_or_nonempty
    · rw [hempty] at hpCommon
      simp at hpCommon
    · obtain ⟨x, hx⟩ := hnonempty
      have hsingle : ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k = {x} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hx, fun y hy => ?_⟩
        by_contra hyx
        have hpair : ({x, y} : Finset M.Vertex) ⊆
            ({v, w} : Finset M.Vertex) ∩ M.freeTriangleBaseEdge T k := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card hpair
        have hxy : x ≠ y := Ne.symm hyx
        have hcardPair : ({x, y} : Finset M.Vertex).card = 2 := by simp [hxy]
        rw [hcardPair] at this
        omega
      rw [hsingle] at hpCommon
      have hpEq : E p = M.position x := by simpa using hpCommon
      have hxBase : x ∈ M.freeTriangleBaseEdge T k := Finset.inter_subset_right hx
      have hxImage : M.position x ∈
          ({M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1} : Set Plane) := by
        rw [← M.image_freeTriangleBaseEdge T k]
        exact ⟨x, hxBase, rfl⟩
      rcases hxImage with hx0 | hx1
      · left
        apply E.injective
        rw [hpEq, hx0]
        simpa [E, kiteTrianglePosition] using
          (M.freeTriangleAffineEquiv_apply_vertex T k 0).symm
      · right
        apply E.injective
        rw [hpEq, hx1]
        simpa [E, kiteTrianglePosition] using
          (M.freeTriangleAffineEquiv_apply_vertex T k 1).symm
  let v0 := M.orderedVertex T ((Equiv.swap 2 k) 0)
  let v1 := M.orderedVertex T ((Equiv.swap 2 k) 1)
  have hE0 : E (planePoint (-1) 0) = M.position v0 := by
    calc
      E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
        simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
      _ = M.position v0 := rfl
  have hE1 : E (planePoint 1 0) = M.position v1 := by
    calc
      E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
        simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
      _ = M.position v1 := rfl
  have hleftEndpoint : planePoint (-1) 0 ∈ segment ℝ a b →
      a = planePoint (-1) 0 ∨ b = planePoint (-1) 0 := by
    intro hleft
    have hpEdge : M.position v0 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE0]
      exact ⟨planePoint (-1) 0, hleft, rfl⟩
    have hv0 : v0 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he.1 hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv0
    rcases hv0 with hv0 | hv0
    · left
      apply E.injective
      simp [a, hv0, hE0]
    · right
      apply E.injective
      simp [b, hv0, hE0]
  have hrightEndpoint : planePoint 1 0 ∈ segment ℝ a b →
      a = planePoint 1 0 ∨ b = planePoint 1 0 := by
    intro hright
    have hpEdge : M.position v1 ∈
        convexHull ℝ (M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex)) := by
      rw [hcarrier, ← hsegmentImage, ← hE1]
      exact ⟨planePoint 1 0, hright, rfl⟩
    have hv1 : v1 ∈ ({v, w} : Finset M.Vertex) :=
      M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (M.orderedVertex_mem T _) he.1 hpEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
    rcases hv1 with hv1 | hv1
    · left
      apply E.injective
      simp [a, hv1, hE1]
    · right
      apply E.injective
      simp [b, hv1, hE1]
  have hnotBoth : ¬(planePoint (-1) 0 ∈ segment ℝ a b ∧
      planePoint 1 0 ∈ segment ℝ a b) := by
    have hLR : planePoint (-1) 0 ≠ planePoint 1 0 := by
      intro h
      have := congrArg (fun p : Plane => p 0) h
      norm_num [planePoint] at this
    rintro ⟨hleft, hright⟩
    rcases hleftEndpoint hleft with ha0 | hb0
    · rcases hrightEndpoint hright with ha1 | hb1
      · exact hLR (ha0.symm.trans ha1)
      · have hv0 : v = v0 := by
          apply M.position_injective
          rw [← hE0, ← ha0]
          simp [a]
        have hw1 : w = v1 := by
          apply M.position_injective
          rw [← hE1, ← hb1]
          simp [b]
        apply hne
        rw [M.freeTriangleBaseEdge_eq_orderedPair T k, hv0, hw1]
    · rcases hrightEndpoint hright with ha1 | hb1
      · have hw0 : w = v0 := by
          apply M.position_injective
          rw [← hE0, ← hb0]
          simp [b]
        have hv1 : v = v1 := by
          apply M.position_injective
          rw [← hE1, ← ha1]
          simp [a]
        apply hne
        rw [M.freeTriangleBaseEdge_eq_orderedPair T k, hw0, hv1, Finset.pair_comm]
      · exact hLR (hb0.symm.trans hb1)
  obtain ⟨ε, hε, havoid⟩ := exists_thinKitePatch_inter_segment_subset_baseEndpoints
    hab hinter hleftEndpoint hrightEndpoint hnotBoth
  refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
  have hpEdge := hp.2
  obtain ⟨q, hqPatch, rfl⟩ := hp.1
  have hqSegment : q ∈ segment ℝ a b := by
    have : E q ∈ segment ℝ (M.position v) (M.position w) := by
      rwa [← hcarrier]
    rw [← hsegmentImage] at this
    obtain ⟨r, hr, hEq⟩ := this
    exact E.injective hEq ▸ hr
  rcases havoid δ hδ hδε ⟨hqPatch, hqSegment⟩ with hq | hq
  · left
    rw [hq]
    exact hE0
  · right
    rw [hq]
    exact hE1

private theorem exists_pos_uniform_finset {α : Type*}
    (s : Finset α) (P : α → ℝ → Prop)
    (hP : ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P x δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ∀ δ : ℝ, 0 < δ → δ < ε → P x δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨εx, hεx, hx⟩ := hP x (Finset.mem_insert_self x s)
      obtain ⟨εs, hεs, hs⟩ := ih fun y hy => hP y (Finset.mem_insert_of_mem hy)
      refine ⟨min εx εs, lt_min hεx hεs, ?_⟩
      intro y hy δ hδ hδε
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hx δ hδ (hδε.trans_le (min_le_left _ _))
      · exact hs y hy δ hδ (hδε.trans_le (min_le_right _ _))

/-- The one-edge Figure 3.3 push can be made relative both to a prescribed open set and to
the entire old boundary carrier away from the deleted triangle. -/
theorem exists_supported_triangle_push_fixing_boundaryCarrier
    (T : M.Triangle) (k : Fin 3)
    (htrace : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      Set.EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id Uᶜ ∧
        Set.EqOn (transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ)
          id (M.boundaryCarrier \ M.triangleCarrier T.1) ∧
        transportedThinKiteHomeomorph (M.freeTriangleAffineEquiv T k) δ hδ ''
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  classical
  let E := M.freeTriangleAffineEquiv T k
  obtain ⟨εU, hεU, hpatchU⟩ :=
      exists_eventually_transportedThinKitePatch_subset_open E U hU (by
    rw [M.freeTriangleAffineEquiv_image_triangle T k]
    exact hTU)
  let movingEdges := M.allBoundaryEdges.erase (M.freeTriangleBaseEdge T k)
  let P : Finset M.Vertex → ℝ → Prop := fun e δ =>
    transportedThinKitePatch E δ ∩
        convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      {M.freeTriangleOrder T k 0, M.freeTriangleOrder T k 1}
  have hlocal : ∀ e ∈ movingEdges, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P e δ := by
    intro e he
    have heData := Finset.mem_erase.mp he
    exact M.exists_transportedThinKitePatch_inter_boundaryEdge_subset_baseEndpoints
      T k htrace e (M.mem_allBoundaryEdges_iff.mp heData.2) heData.1
  obtain ⟨εB, hεB, hpatchB⟩ := exists_pos_uniform_finset movingEdges P hlocal
  let δ := min εU εB / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδU : δ < εU := by
    dsimp [δ]
    have hmin := min_le_left εU εB
    nlinarith [lt_min hεU hεB]
  have hδB : δ < εB := by
    dsimp [δ]
    have hmin := min_le_right εU εB
    nlinarith [lt_min hεU hεB]
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hmem
    exact hp (hpatchU δ hδ hδU hmem)
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl E δ hδ
    intro hpPatch
    have hpBoundary := hp.1
    change p ∈ ⋃ e ∈ M.allBoundaryEdges,
      convexHull ℝ (M.position '' (e : Set M.Vertex)) at hpBoundary
    obtain ⟨e, hpBoundary⟩ := Set.mem_iUnion.mp hpBoundary
    obtain ⟨heBoundary, hpEdge⟩ := Set.mem_iUnion.mp hpBoundary
    by_cases heBase : e = M.freeTriangleBaseEdge T k
    · subst e
      apply hp.2
      exact convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k)) hpEdge
    · have heMoving : e ∈ movingEdges :=
        Finset.mem_erase.mpr ⟨heBase, heBoundary⟩
      have hpEndpoint := hpatchB e heMoving δ hδ hδB ⟨hpPatch, hpEdge⟩
      apply hp.2
      rcases hpEndpoint with rfl | rfl
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 0),
          M.orderedVertex_mem T _, rfl⟩
      · exact subset_convexHull ℝ _ ⟨M.orderedVertex T ((Equiv.swap 2 k) 1),
          M.orderedVertex_mem T _, rfl⟩
  · have hmove := transportedThinKiteHomeomorph_image_baseSegment E δ hδ
    have h0 : E (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 0
    have h1 : E (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 1
    have h2 : E (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
      simpa [E, kiteTrianglePosition] using M.freeTriangleAffineEquiv_apply_vertex T k 2
    simpa only [E, h0, h1, h2] using hmove

/-- Moise's Figure 3.3 move in an arbitrary free triangle coordinate system, with support in a
prescribed open neighborhood of that triangle. -/
theorem exists_supported_triangle_push (T : M.Triangle) (k : Fin 3)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ h : Plane ≃ₜ Plane,
      Set.EqOn h id Uᶜ ∧
        h '' segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) =
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
            segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2) := by
  let e := M.freeTriangleAffineEquiv T k
  obtain ⟨δ, hδ, hpatch⟩ := exists_thinKitePatch_subset_open e U hU (by
    rw [M.freeTriangleAffineEquiv_image_triangle T k]
    exact hTU)
  let h := transportedThinKiteHomeomorph e δ hδ
  refine ⟨h, ?_, ?_⟩
  · intro p hp
    apply transportedThinKiteHomeomorph_eqOn_compl e δ hδ
    intro hmem
    exact hp (hpatch hmem)
  · have hmove := transportedThinKiteHomeomorph_image_baseSegment e δ hδ
    have h0 : e (planePoint (-1) 0) = M.freeTriangleOrder T k 0 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 0
    have h1 : e (planePoint 1 0) = M.freeTriangleOrder T k 1 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 1
    have h2 : e (planePoint 0 1) = M.freeTriangleOrder T k 2 := by
      simpa [e, kiteTrianglePosition] using
        M.freeTriangleAffineEquiv_apply_vertex T k 2
    simpa only [h, h0, h1, h2] using hmove

/-- The inverse Figure 3.3 move removes a triangle whose two apex edges lie on the frontier. -/
theorem exists_supported_triangle_pull (T : M.Triangle) (k : Fin 3)
    (U : Set Plane) (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ h : Plane ≃ₜ Plane,
      Set.EqOn h id Uᶜ ∧
        h '' (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
          segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) =
            segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  obtain ⟨g, hgfix, hgmove⟩ := M.exists_supported_triangle_push T k U hU hTU
  refine ⟨g.symm, ?_, ?_⟩
  · intro p hp
    have hgp : g p = p := hgfix hp
    exact g.symm_apply_eq.mpr hgp.symm
  · rw [← hgmove, Set.image_image]
    simp

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_03
/- END ClassificationOfSurfaces.Moise.FreeTriangleMove -/

/- BEGIN ClassificationOfSurfaces.Moise.GraphSubdivision | 29be3ab2363fc310c42ce77a5cd3fefbc0cd8a62819037ce9b4011bdbaa4a947 -/
section schottkyclassification06_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite line-arrangement subdivisions of plane graphs

This file supplies the source-side subdivision used in Moise Chapter 6, Theorem 2.  A finite
plane graph is encoded as one auxiliary broken line which traverses every edge (with harmless
connector segments between edges).  The line arrangement of that auxiliary chain resolves every
source edge.  Keeping only arrangement faces subordinate to an original face produces an honest
subdivision of the graph.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

theorem normalized_ge_of_line_nonneg {a b q t : ℝ}
    (hΔ : 0 < b - a) (hq : 0 ≤ q - ((1 - t) * a + t * b)) :
    t ≤ (b - a)⁻¹ * (q - a) := by
  have hbase : t * (b - a) ≤ q - a := by nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hΔ.le)
  calc
    t = (b - a)⁻¹ * (t * (b - a)) := by
      field_simp [hΔ.ne']
    _ ≤ (b - a)⁻¹ * (q - a) := h

theorem normalized_le_of_line_nonpos {a b q t : ℝ}
    (hΔ : 0 < b - a) (hq : q - ((1 - t) * a + t * b) ≤ 0) :
    (b - a)⁻¹ * (q - a) ≤ t := by
  have hbase : q - a ≤ t * (b - a) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hΔ.le)
  calc
    (b - a)⁻¹ * (q - a) ≤ (b - a)⁻¹ * (t * (b - a)) := h
    _ = t := by field_simp [hΔ.ne']

theorem normalized_le_of_line_nonneg_of_neg {a b q t : ℝ}
    (hΔ : b - a < 0) (hq : 0 ≤ q - ((1 - t) * a + t * b)) :
    (b - a)⁻¹ * (q - a) ≤ t := by
  have hbase : t * (b - a) ≤ q - a := by nlinarith
  have h := mul_le_mul_of_nonpos_left hbase (inv_nonpos.mpr hΔ.le)
  calc
    (b - a)⁻¹ * (q - a) ≤ (b - a)⁻¹ * (t * (b - a)) := h
    _ = t := by field_simp [hΔ.ne]

theorem normalized_ge_of_line_nonpos_of_neg {a b q t : ℝ}
    (hΔ : b - a < 0) (hq : q - ((1 - t) * a + t * b) ≤ 0) :
    t ≤ (b - a)⁻¹ * (q - a) := by
  have hbase : q - a ≤ t * (b - a) := by nlinarith
  have h := mul_le_mul_of_nonpos_left hbase (inv_nonpos.mpr hΔ.le)
  calc
    t = (b - a)⁻¹ * (t * (b - a)) := by
      field_simp [hΔ.ne]
    _ ≤ (b - a)⁻¹ * (q - a) := h

private theorem abs_sub_le_inv_nat_of_same_grid_side {D : ℕ} (hD : 0 < D)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hside : ∀ r : Fin (D + 1),
      (x ≤ r.val / (D : ℝ) ∧ y ≤ r.val / (D : ℝ)) ∨
        (r.val / (D : ℝ) ≤ x ∧ r.val / (D : ℝ) ≤ y)) :
    |x - y| ≤ 1 / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  wlog hxy : x ≤ y generalizing x y
  · have h := this hy hx (fun r => by
      rcases hside r with h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr ⟨h.2, h.1⟩) (le_of_not_ge hxy)
    rw [abs_sub_comm]
    exact h
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  by_cases hx1 : x = 1
  · have hy1 : y = 1 := le_antisymm hy.2 (hx1 ▸ hxy)
    rw [hx1, hy1]
    simp []
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    let z : ℝ := (D : ℝ) * x
    let k : ℕ := ⌊z⌋₊
    have hz0 : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) hx.1
    have hzD : z < D := by
      dsimp [z]
      nlinarith
    have hklt : k < D := (Nat.floor_lt hz0).mpr hzD
    let r : Fin (D + 1) := ⟨k + 1, by omega⟩
    have hxGrid : x < r.val / (D : ℝ) := by
      have hfloor : z < k + 1 := Nat.lt_floor_add_one z
      change (D : ℝ) * x < (k : ℝ) + 1 at hfloor
      dsimp [z, r]
      apply (lt_div_iff₀ hDreal).mpr
      simpa [mul_comm] using hfloor
    have hyGrid : y ≤ r.val / (D : ℝ) := by
      rcases hside r with h | h
      · exact h.2
      · exact (not_le_of_gt hxGrid h.1).elim
    have hk : (k : ℝ) ≤ z := Nat.floor_le hz0
    have hgridLe : r.val / (D : ℝ) ≤ x + 1 / (D : ℝ) := by
      dsimp [r, z] at hk ⊢
      apply (div_le_iff₀ hDreal).mpr
      calc
        ((k + 1 : ℕ) : ℝ) ≤ (D : ℝ) * x + 1 := by
          norm_num at hk ⊢
          linarith
        _ = (x + 1 / (D : ℝ)) * D := by
          field_simp [hDreal.ne']
    linarith

namespace PlaneComplex

variable (K : PlaneComplex)

/-- The `EdgeFace` declaration. -/
abbrev EdgeFace := {e : Finset K.Vertex // e ∈ K.edges}

/-- The `edgeEquiv` declaration. -/
noncomputable def edgeEquiv : K.EdgeFace ≃ Fin (Fintype.card K.EdgeFace) :=
  Fintype.equivFin K.EdgeFace

/-- The `edgeAt` declaration. -/
noncomputable def edgeAt (i : Fin (Fintype.card K.EdgeFace)) : K.EdgeFace :=
  K.edgeEquiv.symm i

/-- The `vertexEquiv` declaration. -/
noncomputable def vertexEquiv : K.Vertex ≃ Fin (Fintype.card K.Vertex) :=
  Fintype.equivFin K.Vertex

/-- The `vertexAt` declaration. -/
noncomputable def vertexAt (i : Fin (Fintype.card K.Vertex)) : K.Vertex :=
  K.vertexEquiv.symm i

theorem edgeAt_card (i : Fin (Fintype.card K.EdgeFace)) : (K.edgeAt i).1.card = 2 := by
  exact (Finset.mem_filter.mp (K.edgeAt i).2).2

/-- The `edgeFirst` declaration. -/
noncomputable def edgeFirst (i : Fin (Fintype.card K.EdgeFace)) : K.Vertex :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose

/-- The `edgeSecond` declaration. -/
noncomputable def edgeSecond (i : Fin (Fintype.card K.EdgeFace)) : K.Vertex :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeFirst i ≠ K.edgeSecond i :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose_spec.1

theorem edgeAt_eq (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeAt i).1 = {K.edgeFirst i, K.edgeSecond i} :=
  (Finset.card_eq_two.mp (K.edgeAt_card i)).choose_spec.choose_spec.2

theorem edgeAt_mem_simplexes (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeAt i).1 ∈ K.simplexes :=
  (Finset.mem_filter.mp (K.edgeAt i).2).1

/-- Affine coordinate from `0` to `1` on an enumerated source edge. -/
noncomputable def edgeParameter (i : Fin (Fintype.card K.EdgeFace)) :
    Plane →ᵃ[ℝ] ℝ :=
  if _ : K.position (K.edgeFirst i) 0 ≠ K.position (K.edgeSecond i) 0 then
    (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0)⁻¹ •
      (cartesianX - AffineMap.const ℝ Plane (K.position (K.edgeFirst i) 0))
  else
    (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1)⁻¹ •
      (cartesianY - AffineMap.const ℝ Plane (K.position (K.edgeFirst i) 1))

theorem edgeParameter_apply_first (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeParameter i (K.position (K.edgeFirst i)) = 0 := by
  unfold edgeParameter
  split_ifs <;> simp

theorem edgeParameter_apply_second (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeParameter i (K.position (K.edgeSecond i)) = 1 := by
  unfold edgeParameter
  split_ifs with hx
  · change (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0)⁻¹ *
      (K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hx.symm)
  · have hne : K.position (K.edgeFirst i) ≠ K.position (K.edgeSecond i) := by
      exact K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
    have hy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply hne
      exact plane_ext (not_ne_iff.mp hx) hy
    change (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1)⁻¹ *
      (K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hy.symm)

theorem edgeParameter_lineMap (i : Fin (Fintype.card K.EdgeFace)) (t : ℝ) :
    K.edgeParameter i
      (AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) t) = t := by
  rw [AffineMap.apply_lineMap, K.edgeParameter_apply_first,
    K.edgeParameter_apply_second]
  simp [AffineMap.lineMap_apply_module]

theorem edgeParameter_mem_Icc (i : Fin (Fintype.card K.EdgeFace)) {x : Plane}
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) : K.edgeParameter i x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier] at hx
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair] at hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simpa [K.edgeParameter_lineMap]

theorem lineMap_edgeParameter_eq (i : Fin (Fintype.card K.EdgeFace)) {x : Plane}
    (hx : x ∈ K.cellCarrier (K.edgeAt i).1) :
    AffineMap.lineMap (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i))
      (K.edgeParameter i x) = x := by
  rw [K.edgeAt_eq, PlaneComplex.cellCarrier] at hx
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair, segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [K.edgeParameter_lineMap]

theorem exists_edgeAt (e : K.EdgeFace) : ∃ i, K.edgeAt i = e := by
  exact K.edgeEquiv.symm.surjective e

theorem exists_vertexAt (v : K.Vertex) : ∃ i, K.vertexAt i = v := by
  exact K.vertexEquiv.symm.surjective v

/-- The auxiliary chain has one genuine edge segment at every even index; odd segments merely
connect one enumerated edge to the next and are discarded by `subordinateTo`. -/
noncomputable def edgeChain : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hv : k.val < 2 * m + q then
      K.position (K.vertexAt ⟨k.val - 2 * m, by omega⟩)
    else 0
  exact {
    n := 2 * m + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem edgeChain_vertex_even (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeChain.vertex ⟨2 * i.val, by
      change 2 * i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [edgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem edgeChain_vertex_odd (i : Fin (Fintype.card K.EdgeFace)) :
    K.edgeChain.vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [edgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem edgeChain_vertex_original (i : Fin (Fintype.card K.Vertex)) :
    K.edgeChain.vertex ⟨2 * Fintype.card K.EdgeFace + i.val, by
      change 2 * Fintype.card K.EdgeFace + i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [edgeChain]
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + i.val -
      2 * Fintype.card K.EdgeFace = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `edgeChainIndex` declaration. -/
noncomputable def edgeChainIndex (i : Fin (Fintype.card K.EdgeFace)) :
    Fin K.edgeChain.n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace :=
      Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem edgeChainIndex_castSucc (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeChainIndex i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem edgeChainIndex_succ (i : Fin (Fintype.card K.EdgeFace)) :
    (K.edgeChainIndex i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 <
          2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem edgeChain_segment (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        (K.edgeChain.vertex (K.edgeChainIndex i).castSucc)
        (K.edgeChain.vertex (K.edgeChainIndex i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [K.edgeChainIndex_castSucc, K.edgeChainIndex_succ,
    K.edgeChain_vertex_even, K.edgeChain_vertex_odd, K.edgeAt_eq,
    PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The ambient arrangement generated by all graph edges. -/
noncomputable def edgeArrangement : PlaneComplex :=
  K.edgeChain.arrangementMesh.toPlaneComplex

/-- The arrangement faces subordinate to the original graph. -/
noncomputable def edgeSubdivision : PlaneComplex :=
  K.edgeArrangement.subordinateTo K

theorem edgeSubdivision_support_eq (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.edgeSubdivision.support = K.support := by
  unfold edgeSubdivision edgeArrangement
  apply Set.Subset.antisymm
  · exact K.edgeChain.arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hsne := K.nonempty_of_mem s hs
    have hspos : 0 < s.card := Finset.card_pos.mpr hsne
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin (K.edgeChain.n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + i.val, by
          change 2 * Fintype.card K.EdgeFace + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ := K.edgeChain.exists_arrangementVertex_position_eq j
      let u : Finset K.edgeChain.arrangementMesh.toPlaneComplex.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply (K.edgeChain.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = K.edgeChain.arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            (K.edgeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset K.edgeChain.arrangementMesh.Vertex) :
                Set K.edgeChain.arrangementMesh.Vertex)) at hy
          have himage : K.edgeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset K.edgeChain.arrangementMesh.Vertex) :
                Set K.edgeChain.arrangementMesh.Vertex) =
              {K.edgeChain.arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              have hqw : q = w := Finset.mem_singleton.mp hq
              subst q
              rfl
            · intro hz
              have hz' : z = K.edgeChain.arrangementMesh.toPlaneComplex.position w :=
                Set.mem_singleton_iff.mp hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show K.edgeChain.vertex j = K.position v by
          rw [K.edgeChain_vertex_original i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        rw [K.edgeChain.arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.edgeChain_vertex_original i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          (K.edgeChain.vertex (K.edgeChainIndex i).castSucc)
          (K.edgeChain.vertex (K.edgeChainIndex i).succ) = K.cellCarrier s := by
        rw [K.edgeChain_segment i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        K.edgeChain.exists_face_on_segment (K.edgeChainIndex i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply (K.edgeChain.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

theorem edgeSubdivision_subdivides (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.edgeSubdivision.Subdivides K :=
  K.edgeArrangement.subordinateTo_subdivides K (K.edgeSubdivision_support_eq hgraph)

/-! ## Arbitrarily fine marked arrangements -/

/-- The `EdgeSample` declaration. -/
abbrev EdgeSample (cuts : ℕ) :=
  Fin (Fintype.card K.EdgeFace) × Fin (cuts + 2)

/-- The `edgeSampleEquiv` declaration. -/
noncomputable def edgeSampleEquiv (cuts : ℕ) :
    K.EdgeSample cuts ≃ Fin (Fintype.card (K.EdgeSample cuts)) :=
  Fintype.equivFin (K.EdgeSample cuts)

/-- The `edgeSamplePoint` declaration. -/
noncomputable def edgeSamplePoint (cuts : ℕ) (s : K.EdgeSample cuts) : Plane :=
  AffineMap.lineMap (K.position (K.edgeFirst s.1))
    (K.position (K.edgeSecond s.1)) (s.2.val / (cuts + 1 : ℝ))

theorem edgeParameter_samplePoint (cuts : ℕ) (s : K.EdgeSample cuts) :
    K.edgeParameter s.1 (K.edgeSamplePoint cuts s) = s.2.val / (cuts + 1 : ℝ) := by
  exact K.edgeParameter_lineMap s.1 _

/-- The auxiliary edge chain enlarged by `cuts` equally spaced interior marks on every edge.
The marks need not occur consecutively: their two coordinate lines are what refine the ambient
arrangement. -/
noncomputable def sampledEdgeChain (cuts : ℕ) : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let r := Fintype.card (K.EdgeSample cuts)
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + r + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hs : k.val < 2 * m + r then
      K.edgeSamplePoint cuts
        (K.edgeSampleEquiv cuts |>.symm ⟨k.val - 2 * m, by omega⟩)
    else if hv : k.val < 2 * m + r + q then
      K.position (K.vertexAt ⟨k.val - (2 * m + r), by omega⟩)
    else 0
  exact {
    n := 2 * m + r + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem sampledEdgeChain_vertex_even (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChain cuts).vertex ⟨2 * i.val, by
      change 2 * i.val < 2 * Fintype.card K.EdgeFace +
        Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem sampledEdgeChain_vertex_odd (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChain cuts).vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace +
        Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem sampledEdgeChain_vertex_sample (cuts : ℕ) (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).vertex
      ⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val, by
        change 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩ = K.edgeSamplePoint cuts s := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val -
      2 * Fintype.card K.EdgeFace = (K.edgeSampleEquiv cuts s).val := by omega
  have hfin : (⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val -
      2 * Fintype.card K.EdgeFace, by omega⟩ :
      Fin (Fintype.card (K.EdgeSample cuts))) = K.edgeSampleEquiv cuts s :=
    Fin.ext hsub
  rw [hfin, Equiv.symm_apply_apply]

/-- The `sampledEdgeChainSampleIndex` declaration. -/
noncomputable def sampledEdgeChainSampleIndex (cuts : ℕ) (s : K.EdgeSample cuts) :
    Fin ((K.sampledEdgeChain cuts).n + 1) :=
  ⟨2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val, by
    change 2 * Fintype.card K.EdgeFace + (K.edgeSampleEquiv cuts s).val <
      2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
        Fintype.card K.Vertex + 1
    omega⟩

theorem sampledEdgeArrangement_monochromatic_vertical (cuts : ℕ)
    (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).arrangementMesh.IsMonochromatic
      (BrokenLineData.verticalLine (K.edgeSamplePoint cuts s)) := by
  have h := (K.sampledEdgeChain cuts).arrangementMesh_monochromatic_verticalLine
    (K.sampledEdgeChainSampleIndex cuts s)
  have hj : (K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainSampleIndex cuts s) =
      K.edgeSamplePoint cuts s := by
    exact K.sampledEdgeChain_vertex_sample cuts s
  rw [hj] at h
  exact h

theorem sampledEdgeArrangement_monochromatic_horizontal (cuts : ℕ)
    (s : K.EdgeSample cuts) :
    (K.sampledEdgeChain cuts).arrangementMesh.IsMonochromatic
      (BrokenLineData.horizontalLine (K.edgeSamplePoint cuts s)) := by
  have h := (K.sampledEdgeChain cuts).arrangementMesh_monochromatic_horizontalLine
    (K.sampledEdgeChainSampleIndex cuts s)
  have hj : (K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainSampleIndex cuts s) =
      K.edgeSamplePoint cuts s := by
    exact K.sampledEdgeChain_vertex_sample cuts s
  rw [hj] at h
  exact h

/-- Every arrangement face lies wholly on one side of every rational mark on an original edge,
when measured in that edge's affine coordinate. -/
theorem sampledFace_parameter_side (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) (r : Fin (cuts + 2))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ v ∈ u, K.edgeParameter i
        ((K.sampledEdgeChain cuts).arrangementMesh.position v) ≤
          r.val / (cuts + 1 : ℝ)) ∨
      (∀ v ∈ u, r.val / (cuts + 1 : ℝ) ≤ K.edgeParameter i
        ((K.sampledEdgeChain cuts).arrangementMesh.position v)) := by
  let M := (K.sampledEdgeChain cuts).arrangementMesh
  let sample : K.EdgeSample cuts := (i, r)
  obtain ⟨-, T, hT, huT⟩ := M.mem_faces_iff.mp hu
  unfold edgeParameter
  split_ifs with hx
  · have hmono := K.sampledEdgeArrangement_monochromatic_vertical cuts sample
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - K.edgeSamplePoint cuts sample 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          have hne : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 ≠ 0 :=
            sub_ne_zero.mpr hx.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - K.edgeSamplePoint cuts sample 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 0 - K.edgeSamplePoint cuts sample 0 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          have hne : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 ≠ 0 :=
            sub_ne_zero.mpr hx.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 0 - K.edgeSamplePoint cuts sample 0 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
  · have hxy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
      exact plane_ext (not_ne_iff.mp hx) hy
    have hmono := K.sampledEdgeArrangement_monochromatic_horizontal cuts sample
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - K.edgeSamplePoint cuts sample 1 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          have hne : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 ≠ 0 :=
            sub_ne_zero.mpr hxy.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - K.edgeSamplePoint cuts sample 1 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 1 - K.edgeSamplePoint cuts sample 1 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          have hne : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 ≠ 0 :=
            sub_ne_zero.mpr hxy.symm
          exact lt_of_le_of_ne (le_of_not_gt hΔ) hne
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 1 - K.edgeSamplePoint cuts sample 1 ≤ 0 at hline
        simpa [edgeSamplePoint, sample, M, AffineMap.lineMap_apply_module] using hline

theorem sampledFaceCarrier_parameter_side (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) (r : Fin (cuts + 2))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u,
        K.edgeParameter i x ≤ r.val / (cuts + 1 : ℝ)) ∨
      (∀ x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u,
        r.val / (cuts + 1 : ℝ) ≤ K.edgeParameter i x) := by
  rcases K.sampledFace_parameter_side cuts i r hu with hle | hge
  · left
    intro x hx
    apply convexHull_min ?_ ((convex_Iic (r.val / (cuts + 1 : ℝ))).affine_preimage
      (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  · right
    intro x hx
    apply convexHull_min ?_ ((convex_Ici (r.val / (cuts + 1 : ℝ))).affine_preimage
      (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hge v hv

theorem sampledFace_parameter_diameter (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace))
    {u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex}
    (hu : u ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.simplexes)
    (hui : (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u ⊆
      K.cellCarrier (K.edgeAt i).1)
    {x y : Plane}
    (hx : x ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u)
    (hy : y ∈ (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.cellCarrier u) :
    |K.edgeParameter i x - K.edgeParameter i y| ≤ 1 / (cuts + 1 : ℝ) := by
  have hbound : |K.edgeParameter i x - K.edgeParameter i y| ≤
      1 / ((cuts + 1 : ℕ) : ℝ) := by
    apply abs_sub_le_inv_nat_of_same_grid_side (D := cuts + 1) (by omega)
      (K.edgeParameter_mem_Icc i (hui hx)) (K.edgeParameter_mem_Icc i (hui hy))
    intro r
    rcases K.sampledFaceCarrier_parameter_side cuts i r hu with hle | hge
    · left
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hle x hx
      · simpa only [Nat.cast_add, Nat.cast_one] using hle y hy
    · right
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hge x hx
      · simpa only [Nat.cast_add, Nat.cast_one] using hge y hy
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

theorem sampledEdgeChain_vertex_original (cuts : ℕ)
    (i : Fin (Fintype.card K.Vertex)) :
    (K.sampledEdgeChain cuts).vertex
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val -
      (2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts)) = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `sampledEdgeChainIndex` declaration. -/
noncomputable def sampledEdgeChainIndex (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) : Fin (K.sampledEdgeChain cuts).n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace +
      Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace :=
      Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem sampledEdgeChainIndex_castSucc (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChainIndex cuts i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val < 2 * Fintype.card K.EdgeFace +
          Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem sampledEdgeChainIndex_succ (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.sampledEdgeChainIndex cuts i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace +
          Fintype.card (K.EdgeSample cuts) + Fintype.card K.Vertex + 1
        omega⟩ := by
  rfl

theorem sampledEdgeChain_segment (cuts : ℕ)
    (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [K.sampledEdgeChainIndex_castSucc, K.sampledEdgeChainIndex_succ,
    K.sampledEdgeChain_vertex_even, K.sampledEdgeChain_vertex_odd, K.edgeAt_eq,
    PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The `sampledEdgeArrangement` declaration. -/
noncomputable def sampledEdgeArrangement (cuts : ℕ) : PlaneComplex :=
  (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex

/-- The `sampledEdgeSubdivision` declaration. -/
noncomputable def sampledEdgeSubdivision (cuts : ℕ) : PlaneComplex :=
  (K.sampledEdgeArrangement cuts).subordinateTo K

/-- Every point of an original graph face lies in a sampled-subdivision face contained in that
same original face. -/
theorem exists_sampledEdgeSubdivision_face_at (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {x : Plane}
    (hxs : x ∈ K.cellCarrier s) :
    ∃ u ∈ (K.sampledEdgeSubdivision cuts).simplexes,
      x ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u ∧
        (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆ K.cellCarrier s := by
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hscard := hgraph s hs
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxv : x = K.position v := by
      simpa [PlaneComplex.cellCarrier] using hxs
    obtain ⟨i, hi⟩ := K.exists_vertexAt v
    let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩
    obtain ⟨w, hwpos, hwface⟩ :=
      (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
    let u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex := {w}
    have huCarrier : (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆
        K.cellCarrier ({v} : Finset K.Vertex) := by
      intro y hy
      have hyw : y =
          (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
        change y ∈ convexHull ℝ
          ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
              Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
        have himage :
            (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
                (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                  Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
              {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
          ext z
          constructor
          · rintro ⟨q, hq, hz⟩
            rw [Finset.mem_singleton.mp hq] at hz
            exact hz.symm
          · intro hz
            exact ⟨w, Finset.mem_singleton_self w, hz.symm⟩
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hyw, hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
    have hu : u ∈ (K.sampledEdgeSubdivision cuts).simplexes := by
      apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      exact ⟨hwface, {v}, hs, huCarrier⟩
    refine ⟨u, hu, ?_, huCarrier⟩
    rw [hxv]
    change K.position v ∈ convexHull ℝ
      ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
        (u : Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex))
    exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
      rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]⟩
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have hsegment : segment ℝ
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
        ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
        K.cellCarrier s := by
      rw [K.sampledEdgeChain_segment cuts i, hi]
    obtain ⟨u, hu, hxu, huSegment⟩ :=
      (K.sampledEdgeChain cuts).exists_face_on_segment
        (K.sampledEdgeChainIndex cuts i) (hsegment.symm ▸ hxs)
    have huCarrier : (K.sampledEdgeSubdivision cuts).cellCarrier u ⊆
        K.cellCarrier s := by
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _
    refine ⟨u, ?_, hxu, huCarrier⟩
    apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    exact ⟨hu, s, hs, huCarrier⟩

theorem sampledEdgeSubdivision_support_eq (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.sampledEdgeSubdivision cuts).support = K.support := by
  unfold sampledEdgeSubdivision sampledEdgeArrangement
  apply Set.Subset.antisymm
  · exact (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
          change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
              Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ :=
        (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
      let u : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
          |>.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
          have himage : (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
              {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              have hqw : q = w := Finset.mem_singleton.mp hq
              subst q
              rfl
            · intro hz
              have hz' : z =
                  (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w :=
                Set.mem_singleton_iff.mp hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show (K.sampledEdgeChain cuts).vertex j = K.position v by
          rw [K.sampledEdgeChain_vertex_original cuts i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        erw [(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).castSucc)
          ((K.sampledEdgeChain cuts).vertex (K.sampledEdgeChainIndex cuts i).succ) =
          K.cellCarrier s := by
        rw [K.sampledEdgeChain_segment cuts i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        (K.sampledEdgeChain cuts).exists_face_on_segment
          (K.sampledEdgeChainIndex cuts i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

/-- Every original vertex position which lies in the graph support becomes an actual zero-face
of the sampled subdivision.  The extra original-vertex marks in `sampledEdgeChain` ensure this
even when the original abstract vertex was not itself used by a face. -/
theorem exists_sampledEdgeSubdivision_vertex_position_eq (cuts : ℕ) (v : K.Vertex)
    (hv : K.position v ∈ K.support) :
    ∃ w : (K.sampledEdgeSubdivision cuts).Vertex,
      (K.sampledEdgeSubdivision cuts).position w = K.position v ∧
        ({w} : Finset (K.sampledEdgeSubdivision cuts).Vertex) ∈
          (K.sampledEdgeSubdivision cuts).simplexes := by
  obtain ⟨i, hi⟩ := K.exists_vertexAt v
  let j : Fin ((K.sampledEdgeChain cuts).n + 1) :=
    ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
      change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
        2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
          Fintype.card K.Vertex + 1
      omega⟩
  obtain ⟨w, hwpos, hwface⟩ :=
    (K.sampledEdgeChain cuts).exists_arrangementVertex_position_eq j
  rw [PlaneComplex.support] at hv
  simp only [Set.mem_iUnion] at hv
  obtain ⟨s, hs, hvs⟩ := hv
  refine ⟨w, ?_, ?_⟩
  · change (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w = K.position v
    rw [hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
  · apply ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    refine ⟨hwface, s, hs, ?_⟩
    intro y hy
    have hyw : y =
        (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w := by
      change y ∈ convexHull ℝ
        ((K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
            Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex)) at hy
      have himage :
          (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.sampledEdgeChain cuts).arrangementMesh.Vertex) :
                Set (K.sampledEdgeChain cuts).arrangementMesh.Vertex) =
            {(K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w} := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [Finset.mem_singleton.mp hx]
          exact Set.mem_singleton _
        · intro hz
          have hz' : z =
              (K.sampledEdgeChain cuts).arrangementMesh.toPlaneComplex.position w :=
            Set.mem_singleton_iff.mp hz
          subst z
          exact ⟨w, Finset.mem_singleton_self w, rfl⟩
      rwa [himage, convexHull_singleton] at hy
    rw [hyw, hwpos, K.sampledEdgeChain_vertex_original cuts i, hi]
    exact hvs

theorem sampledEdgeSubdivision_subdivides (cuts : ℕ)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.sampledEdgeSubdivision cuts).Subdivides K :=
  (K.sampledEdgeArrangement cuts).subordinateTo_subdivides K
    (K.sampledEdgeSubdivision_support_eq cuts hgraph)

/-- A positive common upper bound for the lengths of all enumerated edges. -/
noncomputable def edgeLengthBound : ℝ :=
  1 + ∑ i : Fin (Fintype.card K.EdgeFace),
    dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i))

theorem edgeLengthBound_pos : 0 < K.edgeLengthBound := by
  unfold edgeLengthBound
  have hsum : 0 ≤ ∑ i : Fin (Fintype.card K.EdgeFace),
      dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) :=
    Finset.sum_nonneg fun _ _ => dist_nonneg
  linarith

theorem edge_length_lt_bound (i : Fin (Fintype.card K.EdgeFace)) :
    dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) <
      K.edgeLengthBound := by
  unfold edgeLengthBound
  have hi : dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) ≤
      ∑ j : Fin (Fintype.card K.EdgeFace),
        dist (K.position (K.edgeFirst j)) (K.position (K.edgeSecond j)) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (Fintype.card K.EdgeFace) =>
        dist (K.position (K.edgeFirst j)) (K.position (K.edgeSecond j)))
      (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  linarith

/-- Heine--Cantor plus the marked line arrangement: every finite embedded graph has a subordinate
subdivision whose faces have arbitrarily small image diameter under a continuous map. -/
theorem exists_sampledEdgeSubdivision_image_diameter_lt
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    {η : ℝ} (hη : 0 < η) :
    ∃ cuts : ℕ, ∀ u ∈ (K.sampledEdgeSubdivision cuts).simplexes,
      ∀ x ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u,
        ∀ y ∈ (K.sampledEdgeSubdivision cuts).cellCarrier u,
          dist (h x) (h y) < η := by
  have huc := K.isCompact_support.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (K.edgeLengthBound / δ)
  have hNreal : K.edgeLengthBound / δ < (N : ℝ) := hN
  have hratio : K.edgeLengthBound / (N + 1 : ℝ) < δ := by
    have hNpos : (0 : ℝ) < N + 1 := by positivity
    apply (div_lt_iff₀ hNpos).mpr
    have hmul : K.edgeLengthBound < δ * N := by
      have hmul' := (div_lt_iff₀ hδ).mp hNreal
      simpa [mul_comm] using hmul'
    nlinarith
  refine ⟨N, ?_⟩
  intro u hu x hx y hy
  obtain ⟨huA, s, hs, hus⟩ :=
    (K.sampledEdgeArrangement N |>.mem_subordinateTo_simplexes_iff K).mp hu
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hscard := hgraph s hs
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  have hxK : x ∈ K.support := K.cellCarrier_subset_support hs (hus hx)
  have hyK : y ∈ K.support := K.cellCarrier_subset_support hs (hus hy)
  rcases hcases with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxy : x = y := by
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hx
      have hyv : y = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hy
      exact hxv.trans hyv.symm
    subst y
    simpa using hη
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have husI : (K.sampledEdgeChain N).arrangementMesh.toPlaneComplex.cellCarrier u ⊆
        K.cellCarrier (K.edgeAt i).1 := by
      simpa [sampledEdgeArrangement, hi] using hus
    have hparam := K.sampledFace_parameter_diameter N i huA husI hx hy
    have hxline := K.lineMap_edgeParameter_eq i (husI hx)
    have hyline := K.lineMap_edgeParameter_eq i (husI hy)
    have hdistXY : dist x y < δ := by
      rw [← hxline, ← hyline, dist_lineMap_lineMap]
      have hparam' : dist (K.edgeParameter i x) (K.edgeParameter i y) ≤
          1 / (N + 1 : ℝ) := by
        simpa [Real.dist_eq] using hparam
      calc
        dist (K.edgeParameter i x) (K.edgeParameter i y) *
            dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) ≤
          (1 / (N + 1 : ℝ)) *
            dist (K.position (K.edgeFirst i)) (K.position (K.edgeSecond i)) :=
              mul_le_mul_of_nonneg_right hparam' dist_nonneg
        _ < (1 / (N + 1 : ℝ)) * K.edgeLengthBound := by
          exact mul_lt_mul_of_pos_left (K.edge_length_lt_bound i) (by positivity)
        _ = K.edgeLengthBound / (N + 1 : ℝ) := by ring
        _ < δ := hratio
    exact hmod x hxK y hyK hdistXY

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_04
/- END ClassificationOfSurfaces.Moise.GraphSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.OpenMidpointComplex | fd3630d4023d9f458ccc157376dc19b5ddaf82915619298c7107385ba9b25d0c -/
section schottkyclassification06_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Nested safe midpoint stages of an open polyhedron

For an open subset `U` of a finite intrinsic complex, retain at level `n` every midpoint
triangle whose whole carrier is contained in `U`.  These finite stages are nested and exhaust
`U`.  They are the finite layers used in Moise Chapter 8, Theorem 2 before adjacent frontier
subdivisions are reconciled by coning.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- The `n`-fold midpoint subdivision used at one safe stage. -/
noncomputable abbrev safeSubdivision (n : ℕ) : K.Subdivision :=
  K.iteratedMidpointSubdivision n

/-- Refined triangles whose complete transported carriers lie in the prescribed open set. -/
noncomputable def safeFaces (n : ℕ) :
    Finset (Finset (K.safeSubdivision n).refined.Vertex) := by
  classical
  exact (K.safeSubdivision n).refined.faces.filter fun t ↦
    ∀ x ∈ (K.safeSubdivision n).refined.faceCarrier t,
      (K.safeSubdivision n).homeo x ∈ U

/-- The finite intrinsic subcomplex retained at level `n`. -/
noncomputable abbrev safeStage (n : ℕ) : IntrinsicTwoComplex :=
  (K.safeSubdivision n).refined.restrictFaces
    (fun t ↦ t ∈ K.safeFaces U n)

/-- Include a safe stage into the original finite realization. -/
noncomputable def safeStageInclusion (n : ℕ) :
    (K.safeStage U n).realization → K.realization :=
  (K.safeSubdivision n).homeo ∘
    (K.safeSubdivision n).refined.restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n)

theorem isEmbedding_safeStageInclusion (n : ℕ) :
    _root_.Topology.IsEmbedding (K.safeStageInclusion U n) :=
  (K.safeSubdivision n).homeo.isEmbedding.comp
    ((K.safeSubdivision n).refined.isEmbedding_restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n))

/-- Carrier of one finite safe stage in the original realization. -/
noncomputable def safeStageSupport (n : ℕ) : Set K.realization :=
  Set.range (K.safeStageInclusion U n)

theorem isCompact_safeStageSupport (n : ℕ) :
    IsCompact (K.safeStageSupport U n) :=
  isCompact_range (K.isEmbedding_safeStageInclusion U n).continuous

theorem safeStageSupport_subset (n : ℕ) : K.safeStageSupport U n ⊆ U := by
  classical
  rintro z ⟨x, rfl⟩
  rcases x.2.2 with ⟨t, ht, hxt⟩
  have hsafe := (Finset.mem_filter.mp ((Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mp ht).2).2
  exact hsafe
    ((K.safeSubdivision n).refined.restrictFacesInclusion
      (fun s ↦ s ∈ K.safeFaces U n) x) hxt

/-- Every point of a retained old triangle is carried by a retained child at the next midpoint
level. -/
theorem safeStageSupport_mono (n : ℕ) :
    K.safeStageSupport U n ⊆ K.safeStageSupport U (n + 1) := by
  classical
  rintro z ⟨x, rfl⟩
  let R := K.safeSubdivision n
  let q : R.refined.realization :=
    R.refined.restrictFacesInclusion (fun t ↦ t ∈ K.safeFaces U n) x
  rcases x.2.2 with ⟨t, ht, hqt⟩
  have htSafeMem : t ∈ K.safeFaces U n := ((Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mp ht).2
  have htSafe := (Finset.mem_filter.mp htSafeMem).2
  let T : R.refined.Face := ⟨t, ((Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mp ht).1⟩
  obtain ⟨y, s, hsOver, hys, heval⟩ :=
    R.refined.exists_midpoint_preimage_in_face T q hqt
  have hsFace : s ∈ R.refined.midpointComplex.faces := by
    change s ∈ R.refined.midpointFaces
    rw [midpointFaces]
    exact Finset.mem_biUnion.mpr ⟨T, by simp, hsOver⟩
  have hsSafe : ∀ w ∈ R.refined.midpointComplex.faceCarrier s,
      R.homeo (R.refined.midpointHomeomorph w) ∈ U := by
    intro w hw
    apply htSafe
    exact R.refined.midpointEval_mem_parentFace T hsOver w hw
  have hsMem : s ∈ K.safeFaces U (n + 1) := by
    change s ∈ R.refined.midpointComplex.faces.filter fun t ↦
      ∀ x ∈ R.refined.midpointComplex.faceCarrier t,
        R.homeo (R.refined.midpointHomeomorph x) ∈ U
    exact Finset.mem_filter.mpr ⟨hsFace, hsSafe⟩
  let y' : (K.safeStage U (n + 1)).realization :=
    ⟨y.1, y.2.1, ⟨s, (Finset.mem_filter (p := fun t => t ∈ K.safeFaces U (n + 1))).mpr ⟨hsFace, hsMem⟩, hys⟩⟩
  refine ⟨y', ?_⟩
  apply Subtype.ext
  simp only [safeStageInclusion, Function.comp_apply]
  change (R.homeo (R.refined.midpointHomeomorph y)).1 =
    (R.homeo (R.refined.restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n) x)).1
  have harg : R.refined.midpointHomeomorph y =
      R.refined.restrictFacesInclusion (fun t ↦ t ∈ K.safeFaces U n) x := by
    apply Subtype.ext
    simpa only [R.refined.midpointHomeomorph_apply,
      R.refined.midpointEval_val] using heval
  exact congrArg (fun w : K.realization ↦ w.1) (congrArg R.homeo harg)

/-- Safe-stage supports are monotone in the subdivision level. -/
theorem safeStageSupport_mono_of_le {n m : ℕ} (hnm : n ≤ m) :
    K.safeStageSupport U n ⊆ K.safeStageSupport U m := by
  induction m, hnm using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ m _ ih => exact ih.trans (K.safeStageSupport_mono U m)

/-- A point of an open set is eventually carried by a safe midpoint triangle. -/
theorem mem_safeStageSupport_of_mem (hU : IsOpen U) {p : K.realization} (hp : p ∈ U) :
    ∃ n : ℕ, p ∈ K.safeStageSupport U n := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.safeSubdivision n
  let q : R.refined.realization := R.homeo.symm p
  rcases q.2.2 with ⟨t, ht, hqt⟩
  have htSafe : ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U := by
    intro x hxt
    apply hball
    rw [Metric.mem_ball]
    have hmesh := K.iteratedMidpointSubdivision_meshLE n t ht x hxt q hqt
    calc
      dist (R.homeo x) p = dist (R.homeo x) (R.homeo q) := by
        rw [R.homeo.apply_symm_apply p]
      _ ≤ (1 / 2 : ℝ) ^ n := hmesh
      _ < ε := hn
  have htMem : t ∈ K.safeFaces U n :=
    Finset.mem_filter.mpr ⟨ht, htSafe⟩
  let x : (K.safeStage U n).realization :=
    ⟨q.1, q.2.1, ⟨t, (Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mpr ⟨ht, htMem⟩, hqt⟩⟩
  refine ⟨n, x, ?_⟩
  exact R.homeo.apply_symm_apply p

/-- Every point of an open set eventually lies in the ambient interior of a finite safe stage.
This is stronger than mere exhaustion and is the compact-control input for the locally finite
shell construction. -/
theorem mem_interior_safeStageSupport_of_mem (hU : IsOpen U)
    {p : K.realization} (hp : p ∈ U) :
    ∃ n : ℕ, p ∈ interior (K.safeStageSupport U n) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε2
    (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.safeSubdivision n
  have hballSafe : Metric.ball p (ε / 2) ⊆ K.safeStageSupport U n := by
    intro z hz
    let q : R.refined.realization := R.homeo.symm z
    rcases q.2.2 with ⟨t, ht, hqt⟩
    have htSafe : ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U := by
      intro x hxt
      apply hball
      rw [Metric.mem_ball]
      have hmesh := K.iteratedMidpointSubdivision_meshLE n t ht x hxt q hqt
      calc
        dist (R.homeo x) p ≤ dist (R.homeo x) z + dist z p := dist_triangle _ _ _
        _ = dist (R.homeo x) (R.homeo q) + dist z p := by
          rw [R.homeo.apply_symm_apply z]
        _ ≤ (1 / 2 : ℝ) ^ n + dist z p := add_le_add hmesh le_rfl
        _ < ε / 2 + ε / 2 := add_lt_add hn hz
        _ = ε := by ring
    have htMem : t ∈ K.safeFaces U n :=
      Finset.mem_filter.mpr ⟨ht, htSafe⟩
    let x : (K.safeStage U n).realization :=
      ⟨q.1, q.2.1, ⟨t, (Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mpr ⟨ht, htMem⟩, hqt⟩⟩
    refine ⟨x, ?_⟩
    exact R.homeo.apply_symm_apply z
  refine ⟨n, interior_maximal hballSafe Metric.isOpen_ball ?_⟩
  exact Metric.mem_ball_self hε2

/-- A compact subset of an open polyhedron is eventually contained in the interior of one
finite safe stage. -/
theorem exists_safeStageSupport_interior_of_compact
    {C : Set K.realization} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ n : ℕ, C ⊆ interior (K.safeStageSupport U n) := by
  classical
  have hcover : C ⊆ ⋃ n : ℕ, interior (K.safeStageSupport U n) := by
    intro p hp
    obtain ⟨n, hn⟩ := K.mem_interior_safeStageSupport_of_mem U hU (hCU hp)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨stages, hstages⟩ := hC.elim_finite_subcover
    (fun n : ℕ ↦ interior (K.safeStageSupport U n))
    (fun _ ↦ isOpen_interior) hcover
  let N := stages.sup id
  refine ⟨N, ?_⟩
  intro p hp
  obtain ⟨n, hnStages, hpn⟩ := Set.mem_iUnion₂.mp (hstages hp)
  exact interior_mono
    (K.safeStageSupport_mono_of_le U (Finset.le_sup (f := id) hnStages)) hpn

section SafeExhaustion

variable (hU : IsOpen U)

/-- A later midpoint level whose safe support contains the given safe support in its interior.
The maximum with `n + 1` makes the selected levels strictly increase. -/
noncomputable def nextSafeStage (n : ℕ) : ℕ :=
  max (Classical.choose (K.exists_safeStageSupport_interior_of_compact U
    (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))) (n + 1)

theorem lt_nextSafeStage (n : ℕ) : n < K.nextSafeStage U hU n := by
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_right _ _)

theorem safeStageSupport_subset_interior_next (n : ℕ) :
    K.safeStageSupport U n ⊆ interior (K.safeStageSupport U (K.nextSafeStage U hU n)) := by
  let m := Classical.choose (K.exists_safeStageSupport_interior_of_compact U
    (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))
  have hm : K.safeStageSupport U n ⊆ interior (K.safeStageSupport U m) :=
    Classical.choose_spec (K.exists_safeStageSupport_interior_of_compact U
      (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))
  exact hm.trans (interior_mono (K.safeStageSupport_mono_of_le U (Nat.le_max_left _ _)))

/-- Cofinal levels selected so that consecutive finite supports are nested through interiors. -/
noncomputable def safeExhaustionIndex : ℕ → ℕ
  | 0 => 0
  | n + 1 => K.nextSafeStage U hU (safeExhaustionIndex n)

@[simp] theorem safeExhaustionIndex_zero : K.safeExhaustionIndex U hU 0 = 0 := rfl

@[simp] theorem safeExhaustionIndex_succ (n : ℕ) :
    K.safeExhaustionIndex U hU (n + 1) =
      K.nextSafeStage U hU (K.safeExhaustionIndex U hU n) := rfl

theorem safeExhaustionIndex_lt_succ (n : ℕ) :
    K.safeExhaustionIndex U hU n < K.safeExhaustionIndex U hU (n + 1) := by
  rw [K.safeExhaustionIndex_succ U hU n]
  exact K.lt_nextSafeStage U hU _

theorem id_le_safeExhaustionIndex (n : ℕ) : n ≤ K.safeExhaustionIndex U hU n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (K.safeExhaustionIndex_lt_succ U hU n))

theorem safeExhaustionIndex_mono {n m : ℕ} (hnm : n ≤ m) :
    K.safeExhaustionIndex U hU n ≤ K.safeExhaustionIndex U hU m := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (K.safeExhaustionIndex_lt_succ U hU m).le

/-- The selected compact exhaustion stage. -/
noncomputable def safeExhaustion (n : ℕ) : Set K.realization :=
  K.safeStageSupport U (K.safeExhaustionIndex U hU n)

theorem isCompact_safeExhaustion (n : ℕ) : IsCompact (K.safeExhaustion U hU n) :=
  K.isCompact_safeStageSupport U _

theorem safeExhaustion_subset (n : ℕ) : K.safeExhaustion U hU n ⊆ U :=
  K.safeStageSupport_subset U _

theorem safeExhaustion_subset_interior_succ (n : ℕ) :
    K.safeExhaustion U hU n ⊆ interior (K.safeExhaustion U hU (n + 1)) := by
  exact K.safeStageSupport_subset_interior_next U hU _

theorem safeExhaustion_mono (n : ℕ) :
    K.safeExhaustion U hU n ⊆ K.safeExhaustion U hU (n + 1) :=
  (K.safeExhaustion_subset_interior_succ U hU n).trans interior_subset

theorem safeExhaustion_mono_of_le {n m : ℕ} (hnm : n ≤ m) :
    K.safeExhaustion U hU n ⊆ K.safeExhaustion U hU m := by
  exact K.safeStageSupport_mono_of_le U
    (K.safeExhaustionIndex_mono U hU hnm)

theorem iUnion_safeExhaustion : (⋃ n : ℕ, K.safeExhaustion U hU n) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeExhaustion_subset U hU n hn
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, K.safeStageSupport_mono_of_le U (K.id_le_safeExhaustionIndex U hU n) hn⟩

theorem iUnion_interior_safeExhaustion :
    (⋃ n : ℕ, interior (K.safeExhaustion U hU n)) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeExhaustion_subset U hU n (interior_subset hn)
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_interior_safeStageSupport_of_mem U hU hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, interior_mono ?_ hn⟩
    exact K.safeStageSupport_mono_of_le U (K.id_le_safeExhaustionIndex U hU n)

/-- The compact shells of the selected exhaustion, regarded in the open subspace.  Shell zero
is the first compact stage; shell `n + 1` is the next stage with the interior of stage `n`
removed. -/
noncomputable def safeShell : ℕ → Set U
  | 0 => Subtype.val ⁻¹' K.safeExhaustion U hU 0
  | n + 1 => Subtype.val ⁻¹'
      (K.safeExhaustion U hU (n + 1) \ interior (K.safeExhaustion U hU n))

/-- The exhaustion shells are locally finite in `U`.  They may accumulate at the frontier in
the original compact realization, which is precisely why the ambient space here is the open
subspace. -/
theorem locallyFinite_safeShell : LocallyFinite (K.safeShell U hU) := by
  intro x
  have hxUnion : x.1 ∈ ⋃ n : ℕ, interior (K.safeExhaustion U hU n) := by
    rw [K.iUnion_interior_safeExhaustion U hU]
    exact x.2
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxUnion
  let V : Set U := Subtype.val ⁻¹' interior (K.safeExhaustion U hU k)
  refine ⟨V, ?_, ?_⟩
  · exact (isOpen_interior.preimage continuous_subtype_val).mem_nhds hxk
  · apply (Finset.finite_toSet (Finset.range (k + 1))).subset
    intro n hn
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hnlt
    have hkn : k + 1 ≤ n := Nat.le_of_not_gt hnlt
    rcases n with _ | n
    · omega
    · obtain ⟨y, hyShell, hyV⟩ := hn
      have hky : y.1 ∈ interior (K.safeExhaustion U hU n) := by
        exact interior_mono (K.safeExhaustion_mono_of_le U hU (by omega)) hyV
      exact hyShell.2 hky

end SafeExhaustion

/-- The nested finite safe stages cover exactly the prescribed open set. -/
theorem iUnion_safeStageSupport (hU : IsOpen U) :
    (⋃ n : ℕ, K.safeStageSupport U n) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeStageSupport_subset U n hn
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_05
/- END ClassificationOfSurfaces.Moise.OpenMidpointComplex -/

/- BEGIN ClassificationOfSurfaces.Moise.PlaneCycle | edb6d36ce01be6b914444c2b51a58c2d85a8b9692fb86106ac79490e5f8549b6 -/
section schottkyclassification06_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal circles from cycles in finite plane complexes

A simple graph cycle in the one-skeleton of a finite plane complex is automatically a
polygonal circle.  The exact segment-intersection axioms follow from the complex's face-to-face
law and the fact that a simple cycle has no repeated cyclic vertex.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex) {v : K.Vertex}

/-- The geometric segment carried by an edge of the vertex graph. -/
theorem cellCarrier_pair_of_adj {u w : K.Vertex} (_ : K.vertexGraph.Adj u w) :
    K.cellCarrier {u, w} = segment ℝ (K.position u) (K.position w) := by
  rw [PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({u, w} : Finset K.Vertex) : Set K.Vertex) =
      {K.position u, K.position w} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- A graph walk traces a canonical geometric path through the corresponding straight edges. -/
noncomputable def walkGeometricPath {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w) : Path (K.position u) (K.position w) := by
  induction p with
  | nil => exact Path.refl _
  | cons h p ih =>
      exact (Path.segment (K.position _) (K.position _)).trans ih

@[simp] theorem walkGeometricPath_nil (u : K.Vertex) :
    K.walkGeometricPath (SimpleGraph.Walk.nil : K.vertexGraph.Walk u u) =
      Path.refl (K.position u) := rfl

@[simp] theorem walkGeometricPath_cons {u w z : K.Vertex}
    (h : K.vertexGraph.Adj u w) (p : K.vertexGraph.Walk w z) :
    K.walkGeometricPath (SimpleGraph.Walk.cons h p) =
      (Path.segment (K.position u) (K.position w)).trans
        (K.walkGeometricPath p) := rfl

/-- The geometric path of a walk stays in the support of the complex, provided its final vertex
is an actual zero-face. -/
theorem range_walkGeometricPath_subset_support {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w)
    (hw : ({w} : Finset K.Vertex) ∈ K.simplexes) :
    Set.range (K.walkGeometricPath p) ⊆ K.support := by
  induction p with
  | nil =>
      rw [K.walkGeometricPath_nil, Path.refl_range]
      rintro x rfl
      exact K.cellCarrier_subset_support hw
        (by simp [PlaneComplex.cellCarrier])
  | cons h p ih =>
      rw [K.walkGeometricPath_cons, Path.trans_range, Path.range_segment,
        ← K.cellCarrier_pair_of_adj h]
      exact Set.union_subset
        (K.cellCarrier_subset_support h.2) (ih hw)

/-- Every straight edge of a walk occurs in the range of its geometric path. -/
theorem walkSegment_subset_range {u w : K.Vertex} (p : K.vertexGraph.Walk u w)
    (i : Fin p.length) :
    segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i.val + 1))) ⊆
      Set.range (K.walkGeometricPath p) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @cons u z w h p ih =>
      cases i using Fin.cases with
      | zero =>
          rw [K.walkGeometricPath_cons, Path.trans_range]
          apply Set.subset_union_of_subset_left
          rw [Path.range_segment]
          simp
      | succ i =>
          rw [K.walkGeometricPath_cons, Path.trans_range]
          apply Set.subset_union_of_subset_right
          simpa only [Fin.val_succ, SimpleGraph.Walk.getVert_cons_succ,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih i

/-- A nonconstant walk's geometric path is covered by its finitely many straight edges. -/
theorem exists_walkSegment_of_mem_range {u w : K.Vertex}
    (p : K.vertexGraph.Walk u w) (hp : 0 < p.length) {x : Plane}
    (hx : x ∈ Set.range (K.walkGeometricPath p)) :
    ∃ i : Fin p.length,
      x ∈ segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i.val + 1))) := by
  induction p with
  | nil => simp at hp
  | @cons u z w h p ih =>
      rw [K.walkGeometricPath_cons, Path.trans_range] at hx
      rcases hx with hxFirst | hxTail
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simpa only [Path.range_segment, SimpleGraph.Walk.getVert_zero,
          SimpleGraph.Walk.getVert_cons_succ] using hxFirst
      · by_cases hzero : p.length = 0
        · cases p with
          | nil =>
              refine ⟨⟨0, by simp⟩, ?_⟩
              rw [K.walkGeometricPath_nil, Path.refl_range] at hxTail
              have hxz : x = K.position z := Set.mem_singleton_iff.mp hxTail
              simpa only [hxz, SimpleGraph.Walk.getVert_zero,
                SimpleGraph.Walk.getVert_cons_succ] using
                  (right_mem_segment ℝ (K.position u) (K.position z))
          | cons h' q => simp at hzero
        · obtain ⟨i, hi⟩ := ih (Nat.pos_of_ne_zero hzero) hxTail
          refine ⟨i.succ, ?_⟩
          simpa only [Fin.val_succ, SimpleGraph.Walk.getVert_cons_succ,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

/-- Concatenating graph walks unions the ranges of their canonical geometric paths. -/
theorem range_walkGeometricPath_append {u v w : K.Vertex}
    (p : K.vertexGraph.Walk u v) (q : K.vertexGraph.Walk v w) :
    Set.range (K.walkGeometricPath (p.append q)) =
      Set.range (K.walkGeometricPath p) ∪ Set.range (K.walkGeometricPath q) := by
  induction p with
  | nil =>
      rw [SimpleGraph.Walk.nil_append, K.walkGeometricPath_nil, Path.refl_range]
      apply Set.Subset.antisymm Set.subset_union_right
      exact Set.union_subset
        (Set.singleton_subset_iff.mpr (Path.source_mem_range (K.walkGeometricPath q)))
        Set.Subset.rfl
  | cons h p ih =>
      rw [SimpleGraph.Walk.cons_append, K.walkGeometricPath_cons,
        K.walkGeometricPath_cons, Path.trans_range, Path.trans_range, ih,
        Set.union_assoc]

/-- Changing only a walk's dependent endpoint witnesses does not change its geometric range. -/
theorem range_walkGeometricPath_copy {u v u' v' : K.Vertex}
    (p : K.vertexGraph.Walk u v) (hu : u = u') (hv : v = v') :
    Set.range (K.walkGeometricPath (p.copy hu hv)) =
      Set.range (K.walkGeometricPath p) := by
  subst u'
  subst v'
  rfl

/-- Mapping a walk from a carrier restriction back to the ambient plane complex preserves its
geometric range. -/
theorem range_walkGeometricPath_mapLe_restrictedTo (C : Set Plane)
    {u v : (K.restrictedTo C).Vertex}
    (p : (K.restrictedTo C).vertexGraph.Walk u v)
    (hle : (K.restrictedTo C).vertexGraph ≤ K.vertexGraph) :
    Set.range (K.walkGeometricPath (p.mapLe hle)) =
      Set.range ((K.restrictedTo C).walkGeometricPath p) := by
  let p' : K.vertexGraph.Walk u v :=
    @SimpleGraph.Walk.mapLe K.Vertex (K.restrictedTo C).vertexGraph K.vertexGraph hle u v p
  change Set.range (K.walkGeometricPath p') =
    Set.range ((K.restrictedTo C).walkGeometricPath p)
  by_cases hzero : p.length = 0
  · cases p with
    | nil => rfl
    | cons h q => simp at hzero
  · have hpos : 0 < p.length := Nat.pos_of_ne_zero hzero
    have hlength : p'.length = p.length := by
      change (SimpleGraph.Walk.map (.ofLE hle) p).length = p.length
      exact SimpleGraph.Walk.length_map (.ofLE hle) p
    have hmap (n : ℕ) : p'.getVert n = p.getVert n := by
      change (SimpleGraph.Walk.map (.ofLE hle) p).getVert n = p.getVert n
      erw [SimpleGraph.Walk.getVert_map]
      exact SimpleGraph.Hom.ofLE_apply hle (p.getVert n)
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := K.exists_walkSegment_of_mem_range p'
        (by simpa [hlength] using hpos) hx
      let j : Fin p.length := ⟨i.val, by simpa [hlength] using i.isLt⟩
      apply (K.restrictedTo C).walkSegment_subset_range p j
      rw [hmap i.val, hmap (i.val + 1)] at hi
      simpa [j] using hi
    · intro x hx
      obtain ⟨i, hi⟩ := (K.restrictedTo C).exists_walkSegment_of_mem_range p hpos hx
      let j : Fin p'.length := ⟨i.val, by simpa only [hlength] using i.isLt⟩
      apply K.walkSegment_subset_range p' j
      rw [hmap i.val, hmap (i.val + 1)]
      exact hi

end PlaneComplex

/-- Change only the endpoint witnesses of a path.  Its underlying function, and hence its range
and injectivity, are unchanged. -/
def Path.copy {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') : Path a' b' where
  toFun := p
  continuous_toFun := p.continuous
  source' := p.source.trans ha
  target' := p.target.trans hb

@[simp] theorem Path.copy_apply {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') (t : unitInterval) :
    Path.copy p ha hb t = p t := rfl

@[simp] theorem Path.copy_range {X : Type*} [TopologicalSpace X] {a b a' b' : X}
    (p : Path a b) (ha : a = a') (hb : b = b') :
    Set.range (Path.copy p ha hb) = Set.range p := rfl

/-- A path contained in an embedded arc and joining the same endpoints covers that entire arc.
This is the order-convexity of connected subsets of the unit interval, transported through the
arc homeomorphism. -/
theorem Path.range_eq_of_subset_of_injective {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b : X} (arc path : Path a b) (harc : Function.Injective arc)
    (hsub : Set.range path ⊆ Set.range arc) :
    Set.range path = Set.range arc := by
  apply Set.Subset.antisymm hsub
  let e₀ : unitInterval ≃ Set.range arc := Equiv.ofInjective arc harc
  let e : unitInterval ≃ₜ Set.range arc :=
    Continuous.homeoOfEquivCompactToT2
      (f := e₀) (Continuous.subtype_mk arc.continuous fun t => ⟨t, rfl⟩)
  let R : Set (Set.range arc) := {x | x.1 ∈ Set.range path}
  have hvalR : ((↑) : Set.range arc → X) '' R = Set.range path := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have hR : IsPreconnected R := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hvalR]
    exact (isConnected_range path.continuous).isPreconnected
  have hpre : IsPreconnected (e ⁻¹' R) :=
    e.isPreconnected_preimage.mpr hR
  have hzero : (0 : unitInterval) ∈ e ⁻¹' R := by
    change (e 0).1 ∈ Set.range path
    change arc 0 ∈ Set.range path
    rw [arc.source]
    exact Path.source_mem_range path
  have hone : (1 : unitInterval) ∈ e ⁻¹' R := by
    change (e 1).1 ∈ Set.range path
    change arc 1 ∈ Set.range path
    rw [arc.target]
    exact Path.target_mem_range path
  have hord : Set.OrdConnected (e ⁻¹' R) :=
    isPreconnected_iff_ordConnected.mp hpre
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  have ht : t ∈ Set.Icc (0 : unitInterval) 1 := ⟨t.2.1, t.2.2⟩
  have htpre := hord.out hzero hone ht
  change (e t).1 ∈ Set.range path at htpre
  exact htpre

namespace PlaneComplex

variable (K : PlaneComplex) {v : K.Vertex}

private theorem cycle_index_injective (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    Function.Injective (fun i : ZMod p.length => p.getVert i.val) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro i j hij
  apply ZMod.val_injective
  apply hp.getVert_injOn'
  · simp only [Set.mem_setOf_eq]
    exact Nat.le_sub_one_of_lt i.val_lt
  · simp only [Set.mem_setOf_eq]
    exact Nat.le_sub_one_of_lt j.val_lt
  · exact hij

private theorem cycle_index_ne_next (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) : i ≠ i + 1 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro hi
  have hzero : (0 : ZMod p.length) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z => z - i) hi
      _ = 1 := by abel
  have hval := congrArg ZMod.val hzero
  have hone : (1 : ZMod p.length).val = 1 := by
    have hn3 := hp.three_le_length
    letI : Fact ((1 : ℕ) < p.length) := ⟨by omega⟩
    exact ZMod.val_one p.length
  rw [ZMod.val_zero, hone] at hval
  omega

private theorem cycle_index_ne_add_two (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) : i ≠ i + 2 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  intro hi
  have hzero : (0 : ZMod p.length) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z => z - i) hi
      _ = 2 := by abel
  have hval := congrArg ZMod.val hzero
  have htwo : (2 : ZMod p.length).val = 2 := by
    change ((2 : ℕ) : ZMod p.length).val = 2
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hp.three_le_length
  rw [ZMod.val_zero, htwo] at hval
  omega

private theorem cycle_next_val (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    (i + 1).val = if i.val + 1 < p.length then i.val + 1 else 0 := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  have hone : (1 : ZMod p.length).val = 1 := by
    have hn3 := hp.three_le_length
    letI : Fact ((1 : ℕ) < p.length) := ⟨by omega⟩
    exact ZMod.val_one p.length
  rw [ZMod.val_add, hone]
  split_ifs with hi
  · exact Nat.mod_eq_of_lt hi
  · have hil := i.val_lt
    have heq : i.val + 1 = p.length := by omega
    rw [heq, Nat.mod_self]

private theorem cycle_adj (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    K.vertexGraph.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  rw [cycle_next_val K p hp i]
  split_ifs with hi
  · exact p.adj_getVert_succ i.val_lt
  · have hil := i.val_lt
    have heq : i.val + 1 = p.length := by omega
    have hadj := p.adj_getVert_succ i.val_lt
    rw [heq, p.getVert_length] at hadj
    simpa using hadj

private theorem cycle_edge_face (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) ∈ K.simplexes :=
  (cycle_adj K p hp i).2

private theorem cycle_edge_carrier (p : K.vertexGraph.Walk v v) (_ : p.IsCycle)
    (i : ZMod p.length) :
    K.cellCarrier {p.getVert i.val, p.getVert (i + 1).val} =
      segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) := by
  rw [PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (p.getVert i.val), K.position (p.getVert (i + 1).val)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

private theorem cycle_edge_inter_next (p : K.vertexGraph.Walk v v) (hp : p.IsCycle)
    (i : ZMod p.length) :
    ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex) ∩
        {p.getVert (i + 1).val, p.getVert (i + 2).val} =
      {p.getVert (i + 1).val} := by
  have hinj := cycle_index_injective K p hp
  have hi1 : p.getVert i.val ≠ p.getVert (i + 1).val :=
    fun h => cycle_index_ne_next K p hp i (hinj h)
  have hi2 : p.getVert i.val ≠ p.getVert (i + 2).val :=
    fun h => cycle_index_ne_add_two K p hp i (hinj h)
  ext w
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hwi | hwi, hwnext | hwtwo⟩
    · exact (hi1 (hwi.symm.trans hwnext)).elim
    · exact (hi2 (hwi.symm.trans hwtwo)).elim
    · exact hwi
    · exact hwi
  · intro hw
    exact ⟨Or.inr hw, Or.inl hw⟩

/-- A simple cycle in a finite plane complex determines an honest polygonal circle. -/
noncomputable def polygonalCircleOfCycle (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    PolygonalCircle := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  let point : ZMod p.length → Plane := fun i => K.position (p.getVert i.val)
  refine {
    n := p.length
    three_le := hp.three_le_length
    vertex := point
    adjacent_ne := ?_
    consecutive_inter := ?_
    nonadjacent_disjoint := ?_ }
  · intro i hpos
    exact (cycle_adj K p hp i).ne (K.position_injective hpos)
  · intro i
    change segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) ∩
      segment ℝ (K.position (p.getVert (i + 1).val))
        (K.position (p.getVert (i + 2).val)) =
      {K.position (p.getVert (i + 1).val)}
    rw [← cycle_edge_carrier K p hp i]
    have hnextCarrier := cycle_edge_carrier K p hp (i + 1)
    rw [show i + 1 + 1 = i + 2 by ring] at hnextCarrier
    rw [← hnextCarrier]
    have hface := K.face_inter _ (cycle_edge_face K p hp i) _
      (cycle_edge_face K p hp (i + 1))
    rw [show i + 1 + 1 = i + 2 by ring] at hface
    change K.cellCarrier _ ∩ K.cellCarrier _ = K.cellCarrier _ at hface
    rw [cycle_edge_inter_next K p hp i] at hface
    rw [hface, PlaneComplex.cellCarrier]
    have himage : K.position ''
        (({p.getVert (i + 1).val} : Finset K.Vertex) : Set K.Vertex) =
        {point (i + 1)} := by
      ext x
      simp [point]
    rw [himage, convexHull_singleton]
  · intro i j hij hiprev hjnext
    rw [← cycle_edge_carrier K p hp i, ← cycle_edge_carrier K p hp j]
    have hdis : Disjoint
        ({p.getVert i.val, p.getVert (i + 1).val} : Finset K.Vertex)
        {p.getVert j.val, p.getVert (j + 1).val} := by
      rw [Finset.disjoint_left]
      intro w hwI hwJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwI hwJ
      have hinj := cycle_index_injective K p hp
      rcases hwI with hwi | hwi <;> rcases hwJ with hwj | hwj
      · exact hij (hinj (hwi.symm.trans hwj))
      · exact hiprev (hinj (hwi.symm.trans hwj))
      · exact hjnext (hinj (hwi.symm.trans hwj)).symm
      · exact hij (add_right_cancel (hinj (hwi.symm.trans hwj)))
    have hface := K.face_inter _ (cycle_edge_face K p hp i) _
      (cycle_edge_face K p hp j)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdis] at hface
    simpa [PlaneComplex.cellCarrier] using hface

/-- The polygonal carrier associated to a graph cycle is exactly the range of the canonical
piecewise-linear path around that cycle. -/
theorem polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath
    (p : K.vertexGraph.Walk v v) (hp : p.IsCycle) :
    (K.polygonalCircleOfCycle p hp).carrier =
      Set.range (K.walkGeometricPath p) := by
  have hn : 0 < p.length := lt_of_lt_of_le (by omega) hp.three_le_length
  letI : NeZero p.length := ⟨hn.ne'⟩
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃ i : ZMod p.length,
      segment ℝ (K.position (p.getVert i.val))
        (K.position (p.getVert (i + 1).val)) at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [cycle_next_val K p hp i] at hi
    by_cases hnext : i.val + 1 < p.length
    · rw [if_pos hnext] at hi
      exact K.walkSegment_subset_range p ⟨i.val, i.val_lt⟩ hi
    · rw [if_neg hnext] at hi
      have hlast : i.val + 1 = p.length := by
        have := i.val_lt
        omega
      have hedge := K.walkSegment_subset_range p ⟨i.val, i.val_lt⟩
      rw [hlast, p.getVert_length] at hedge
      apply hedge
      simpa only [p.getVert_zero] using hi
  · intro x hx
    obtain ⟨i, hi⟩ := K.exists_walkSegment_of_mem_range p hn hx
    change x ∈ ⋃ j : ZMod p.length,
      segment ℝ (K.position (p.getVert j.val))
        (K.position (p.getVert (j + 1).val))
    let j : ZMod p.length := i.val
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    have hj : j.val = i.val := by
      rw [show j = (i.val : ZMod p.length) by rfl, ZMod.val_natCast,
        Nat.mod_eq_of_lt i.isLt]
    rw [cycle_next_val K p hp j, hj]
    by_cases hnext : i.val + 1 < p.length
    · rw [if_pos hnext]
      exact hi
    · rw [if_neg hnext]
      have hlast : i.val + 1 = p.length := by
        have := i.isLt
        omega
      rw [hlast, p.getVert_length] at hi
      rw [p.getVert_zero]
      exact hi

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification06_block_06
/- END ClassificationOfSurfaces.Moise.PlaneCycle -/
