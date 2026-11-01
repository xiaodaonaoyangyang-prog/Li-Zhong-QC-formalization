/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification20: pinned classification sources; see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification19
import LiZhongExternal.Classification.SchottkyClassification03
import Mathlib.Analysis.Convex.GaugeRescale
import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin

/- BEGIN ClassificationOfSurfaces.DiskSquare | 7d4c49a4f40107a840073195a9f2b389a721ab5ee87749c9609d94aeb44e80d3 -/
noncomputable section

section schottkyclassification20_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# A square model for polygon cells

This file supplies the geometric cut-and-paste model used by Gallier--Xu P2.  The closed unit
square is treated as a convex disk.  Its boundary is parameterized explicitly by radial
projection of the Euclidean circle, and an arbitrary homeomorphism from the circle to the
frontier of a bounded convex disk is extended across `PolygonCell`.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex
open Metric Bornology Filter Set
open scoped Topology

namespace DiskSquare

/-- The sup norm of a complex number, used as the gauge of the centered square. -/
def maxAbs (z : ℂ) : ℝ :=
  max |z.re| |z.im|

@[simp]
theorem maxAbs_zero : maxAbs 0 = 0 := by
  simp [maxAbs]

theorem maxAbs_nonneg (z : ℂ) : 0 ≤ maxAbs z :=
  le_max_of_le_left (abs_nonneg z.re)

theorem abs_re_le_maxAbs (z : ℂ) : |z.re| ≤ maxAbs z :=
  le_max_left _ _

theorem abs_im_le_maxAbs (z : ℂ) : |z.im| ≤ maxAbs z :=
  le_max_right _ _

theorem maxAbs_eq_zero_iff {z : ℂ} : maxAbs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Complex.ext
    · have hre : |z.re| = 0 :=
        le_antisymm (abs_re_le_maxAbs z |>.trans_eq h) (abs_nonneg _)
      simpa using abs_eq_zero.mp hre
    · have him : |z.im| = 0 :=
        le_antisymm (abs_im_le_maxAbs z |>.trans_eq h) (abs_nonneg _)
      simpa using abs_eq_zero.mp him
  · rintro rfl
    exact maxAbs_zero

theorem maxAbs_pos {z : ℂ} (hz : z ≠ 0) : 0 < maxAbs z :=
  (maxAbs_nonneg z).lt_of_ne fun h ↦ hz ((maxAbs_eq_zero_iff.mp h.symm))

theorem maxAbs_le_norm (z : ℂ) : maxAbs z ≤ ‖z‖ := by
  apply max_le
  · exact abs_re_le_norm z
  · exact abs_im_le_norm z

theorem maxAbs_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    maxAbs (c • z) = c * maxAbs z := by
  simp only [maxAbs, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    abs_mul, abs_of_nonneg hc]
  by_cases h : |z.re| ≤ |z.im|
  · rw [max_eq_right h,
      max_eq_right (mul_le_mul_of_nonneg_left h hc)]
  · have h' : |z.im| ≤ |z.re| := le_of_not_ge h
    rw [max_eq_left h',
      max_eq_left (mul_le_mul_of_nonneg_left h' hc)]

theorem maxAbs_add_le (z w : ℂ) :
    maxAbs (z + w) ≤ maxAbs z + maxAbs w := by
  apply max_le
  · change |z.re + w.re| ≤ maxAbs z + maxAbs w
    exact (abs_add_le _ _).trans
      (add_le_add (abs_re_le_maxAbs z) (abs_re_le_maxAbs w))
  · change |z.im + w.im| ≤ maxAbs z + maxAbs w
    exact (abs_add_le _ _).trans
      (add_le_add (abs_im_le_maxAbs z) (abs_im_le_maxAbs w))

theorem maxAbs_div_of_pos (z : ℂ) {r : ℝ} (hr : 0 < r) :
    maxAbs (z / r) = maxAbs z / r := by
  simp only [maxAbs, Complex.div_ofReal_re, Complex.div_ofReal_im,
    abs_div, abs_of_pos hr, max_div_div_right hr.le]

theorem norm_le_sqrtTwo_mul_maxAbs (z : ℂ) :
    ‖z‖ ≤ Real.sqrt 2 * maxAbs z := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (maxAbs_nonneg _))]
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow]
  have hre := abs_re_le_maxAbs z
  have him := abs_im_le_maxAbs z
  have hreSq : z.re ^ 2 ≤ maxAbs z ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.re) (maxAbs_nonneg z)).2 hre
  have himSq : z.im ^ 2 ≤ maxAbs z ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) (maxAbs_nonneg z)).2 him
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- The centered closed unit square. -/
def square : Set ℂ :=
  {z | maxAbs z ≤ 1}

/-- The geometric boundary of the centered square. -/
def boundary : Set ℂ :=
  {z | maxAbs z = 1}

theorem continuous_maxAbs : Continuous maxAbs := by
  unfold maxAbs
  exact (Complex.continuous_re.abs.max Complex.continuous_im.abs)

theorem isClosed_square : IsClosed square := by
  exact isClosed_le continuous_maxAbs continuous_const

theorem zero_mem_square : (0 : ℂ) ∈ square := by
  simp [square]

theorem ball_zero_one_subset_square :
    Metric.ball (0 : ℂ) 1 ⊆ square := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact (maxAbs_le_norm z).trans hz.le

theorem square_mem_nhds_zero : square ∈ nhds (0 : ℂ) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
    ball_zero_one_subset_square

theorem convex_square : Convex ℝ square := by
  intro x hx y hy a b ha hb hab
  change maxAbs x ≤ 1 at hx
  change maxAbs y ≤ 1 at hy
  change maxAbs (a • x + b • y) ≤ 1
  calc
    maxAbs (a • x + b • y) ≤ maxAbs (a • x) + maxAbs (b • y) :=
      maxAbs_add_le _ _
    _ = a * maxAbs x + b * maxAbs y := by
      rw [maxAbs_smul_of_nonneg a ha, maxAbs_smul_of_nonneg b hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

theorem isBounded_square : IsBounded square := by
  apply Metric.isBounded_iff_subset_closedBall 0 |>.2
  refine ⟨Real.sqrt 2, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrtTwo_mul_maxAbs z).trans
    (mul_le_of_le_one_right (Real.sqrt_nonneg 2) hz)

theorem interior_square_nonempty : (interior square).Nonempty := by
  refine ⟨0, ?_⟩
  exact mem_interior_iff_mem_nhds.mpr square_mem_nhds_zero

theorem interior_square :
    interior square = {z | maxAbs z < 1} := by
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hnot
    have hzMem : z ∈ square :=
      (interior_subset : interior square ⊆ square) hz
    have hzSquare : maxAbs z ≤ 1 := hzMem
    have hEq : maxAbs z = 1 :=
      le_antisymm hzSquare (le_of_not_gt hnot)
    have hscale : ∀ ε : ℝ, 0 < ε →
        (1 + ε) • z ∉ square := by
      intro ε hε
      change ¬maxAbs ((1 + ε) • z) ≤ 1
      have hpos : 0 ≤ 1 + ε := by linarith
      rw [maxAbs_smul_of_nonneg (1 + ε) hpos, hEq]
      linarith
    have hopen : square ∈ nhds z :=
      mem_interior_iff_mem_nhds.mp hz
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp hopen
    let δ : ℝ := min (ε / (2 * ‖z‖)) (1 / 2)
    have hzNorm : 0 < ‖z‖ := by
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        simp at hEq
      exact norm_pos_iff.mpr hz0
    have hδ : 0 < δ := by
      exact lt_min (div_pos hε (by positivity)) (by norm_num)
    have hdist : dist ((1 + δ) • z) z < ε := by
      rw [dist_eq, add_smul, one_smul,
        show z + δ • z - z = δ • z by abel, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ]
      have hδle : δ ≤ ε / (2 * ‖z‖) := min_le_left _ _
      have hnorm : δ * ‖z‖ ≤ ε / 2 := by
        calc
          δ * ‖z‖ ≤ (ε / (2 * ‖z‖)) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hδle (norm_nonneg _)
          _ = ε / 2 := by field_simp
      linarith
    exact hscale δ hδ (hball hdist)
  · intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hpre :
        {w : ℂ | maxAbs w < 1} ∈ nhds z :=
      (isOpen_lt continuous_maxAbs continuous_const).mem_nhds hz
    exact Filter.mem_of_superset hpre fun w hw ↦ by
      change maxAbs w ≤ 1
      exact hw.le

theorem frontier_square :
    frontier square = boundary := by
  rw [frontier, isClosed_square.closure_eq, interior_square]
  ext z
  simp only [square, boundary, Set.mem_sdiff, Set.mem_setOf_eq, not_lt]
  constructor
  · exact fun h ↦ le_antisymm h.1 h.2
  · intro h
    exact ⟨h.le, h.ge⟩

/-- Radial projection of a nonzero point to the square boundary. -/
noncomputable def radialToBoundary (z : ℂ) (_hz : z ≠ 0) : ℂ :=
  z / maxAbs z

theorem radialToBoundary_maxAbs (z : ℂ) (hz : z ≠ 0) :
    maxAbs (radialToBoundary z hz) = 1 := by
  have hm : 0 < maxAbs z := maxAbs_pos hz
  unfold radialToBoundary
  rw [maxAbs_div_of_pos z hm]
  exact div_self hm.ne'

/-- The radial homeomorphism from the Euclidean unit circle to the centered square boundary. -/
noncomputable def circleBoundaryHomeomorph : Circle ≃ₜ boundary where
  toFun z := ⟨radialToBoundary z z.coe_ne_zero,
    radialToBoundary_maxAbs z z.coe_ne_zero⟩
  invFun z :=
    ⟨z.1 / ‖z.1‖, by
      have hz0 : z.1 ≠ 0 := by
        intro h
        have := z.2
        simp [boundary, h, maxAbs] at this
      have hnorm : ‖z.1 / (‖z.1‖ : ℂ)‖ = 1 := by
        rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr hz0)]
      simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hnorm⟩
  left_inv := by
    intro z
    apply Circle.ext
    change
      (radialToBoundary (z : ℂ) z.coe_ne_zero) /
          ‖radialToBoundary (z : ℂ) z.coe_ne_zero‖ =
        z
    have hm : 0 < maxAbs (z : ℂ) := maxAbs_pos z.coe_ne_zero
    have hnorm :
        ‖radialToBoundary (z : ℂ) z.coe_ne_zero‖ =
          1 / maxAbs (z : ℂ) := by
      rw [radialToBoundary, norm_div, norm_real, Real.norm_eq_abs,
        abs_of_pos hm, z.norm_coe]
    rw [hnorm, radialToBoundary]
    push_cast
    field_simp [hm.ne']
  right_inv := by
    intro z
    apply Subtype.ext
    have hz0 : z.1 ≠ 0 := by
      intro hz
      have := z.2
      simp [boundary, hz, maxAbs] at this
    have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hz0
    have hm : maxAbs z.1 = 1 := z.2
    change
      (z.1 / (‖z.1‖ : ℂ)) /
          (maxAbs (z.1 / (‖z.1‖ : ℂ)) : ℂ) =
        z.1
    have hmax :
        maxAbs (z.1 / ‖z.1‖) = 1 / ‖z.1‖ := by
      rw [maxAbs_div_of_pos z.1 hn, hm]
    rw [hmax]
    push_cast
    field_simp [hn.ne']
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : Circle ↦ (z : ℂ) / maxAbs (z : ℂ))
    exact continuous_subtype_val.div₀
      (Complex.continuous_ofReal.comp
        (continuous_maxAbs.comp continuous_subtype_val))
      fun z ↦ Complex.ofReal_ne_zero.mpr
        (maxAbs_pos (Circle.coe_ne_zero z)).ne'
  continuous_invFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : boundary ↦ z.1 / ‖z.1‖)
    exact continuous_subtype_val.div₀
      (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
      fun z ↦ Complex.ofReal_ne_zero.mpr <| by
        intro h
        have hz0 : z.1 = 0 := norm_eq_zero.mp h
        have := z.2
        simp [boundary, hz0, maxAbs] at this

theorem circleBoundaryHomeomorph_val (z : Circle) :
    (circleBoundaryHomeomorph z).1 =
      radialToBoundary z z.coe_ne_zero :=
  rfl

/-! ## Extending a chosen square-boundary parameterization -/

theorem exists_squareAmbientHomeomorph :
    ∃ h : ℂ ≃ₜ ℂ,
      h '' square = Metric.closedBall 0 1 ∧
      h '' boundary = Metric.sphere 0 1 := by
  obtain ⟨h, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      convex_square interior_square_nonempty isBounded_square
  refine ⟨h, ?_, ?_⟩
  · simpa only [isClosed_square.closure_eq] using hclosure
  · simpa only [frontier_square] using hfrontier

/-- A fixed ambient straightening of the centered square to the Euclidean unit disk. -/
noncomputable def squareAmbientHomeomorph : ℂ ≃ₜ ℂ :=
  Classical.choose exists_squareAmbientHomeomorph

theorem squareAmbientHomeomorph_image_square :
    squareAmbientHomeomorph '' square = Metric.closedBall 0 1 :=
  (Classical.choose_spec exists_squareAmbientHomeomorph).1

theorem squareAmbientHomeomorph_image_boundary :
    squareAmbientHomeomorph '' boundary = Metric.sphere 0 1 :=
  (Classical.choose_spec exists_squareAmbientHomeomorph).2

/-- Restrict the fixed ambient straightening to the closed square. -/
noncomputable def squareCellHomeomorph (n : ℕ) :
    square ≃ₜ PolygonCell n where
  toFun z :=
    ⟨squareAmbientHomeomorph z.1, by
      rw [← squareAmbientHomeomorph_image_square]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨squareAmbientHomeomorph.symm z.val, by
      have hz :
          squareAmbientHomeomorph
              (squareAmbientHomeomorph.symm z.val) ∈
            squareAmbientHomeomorph '' square := by
        rw [squareAmbientHomeomorph_image_square]
        simpa using z.property
      rcases hz with ⟨w, hw, heq⟩
      exact squareAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact squareAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact squareAmbientHomeomorph.apply_symm_apply z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.symm.continuous.comp PolygonCell.continuous_val

/-- The fixed square straightening restricted to its frontier. -/
noncomputable def boundaryCircleHomeomorph :
    boundary ≃ₜ Circle where
  toFun z :=
    ⟨squareAmbientHomeomorph z.1, by
      change squareAmbientHomeomorph z.1 ∈ Metric.sphere 0 1
      rw [← squareAmbientHomeomorph_image_boundary]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨squareAmbientHomeomorph.symm z, by
      have hz :
          squareAmbientHomeomorph (squareAmbientHomeomorph.symm z) ∈
            squareAmbientHomeomorph '' boundary := by
        rw [squareAmbientHomeomorph_image_boundary]
        simp [Submonoid.unitSphere]
      rcases hz with ⟨w, hw, heq⟩
      exact squareAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact squareAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply Circle.ext
    exact squareAmbientHomeomorph.apply_symm_apply z
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.symm.continuous.comp continuous_subtype_val

/-- Include the square frontier into the closed square. -/
def boundaryInclusion : C(boundary, square) where
  toFun z := ⟨z.1, z.2.le⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

theorem squareCellHomeomorph_boundary (n : ℕ) (z : boundary) :
    squareCellHomeomorph n (boundaryInclusion z) =
      PolygonCell.ofCircle n (boundaryCircleHomeomorph z) := by
  apply PolygonCell.ext
  rfl

/-- Extend any selected parameterization of the square frontier across a polygon cell. -/
noncomputable def cellSquareHomeomorph {n : ℕ}
    (b : Circle ≃ₜ boundary) :
    PolygonCell n ≃ₜ square :=
  (PolygonCell.radialHomeomorph
      (b.trans boundaryCircleHomeomorph)).trans
    (squareCellHomeomorph n).symm

/-- The convex extension agrees exactly with the prescribed boundary parameterization. -/
theorem cellSquareHomeomorph_ofCircle {n : ℕ}
    (b : Circle ≃ₜ boundary) (z : Circle) :
    cellSquareHomeomorph b (PolygonCell.ofCircle n z) =
      boundaryInclusion (b z) := by
  apply (squareCellHomeomorph n).injective
  rw [cellSquareHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, PolygonCell.radialHomeomorph_ofCircle,
    squareCellHomeomorph_boundary]
  rfl

/-! ## A distinguished polygon side on the right side of the square -/

/-- Boundary weights for a polygon whose final side is distinguished. -/
def finalSideWeights (l : ℕ) : List ℕ :=
  List.replicate l 3 ++ [l]

/-- Boundary weights for a polygon whose first side is distinguished. -/
def firstSideWeights (r : ℕ) : List ℕ :=
  r :: List.replicate r 3

theorem finalSideWeights_length (l : ℕ) :
    (finalSideWeights l).length = l + 1 := by
  simp [finalSideWeights]

theorem firstSideWeights_length (r : ℕ) :
    (firstSideWeights r).length = r + 1 := by
  simp [firstSideWeights]

@[simp]
theorem finalSideWeights_sum (l : ℕ) :
    (finalSideWeights l).sum = 4 * l := by
  simp [finalSideWeights]
  omega

@[simp]
theorem firstSideWeights_sum (r : ℕ) :
    (firstSideWeights r).sum = 4 * r := by
  simp [firstSideWeights]
  omega

theorem finalSideWeights_positive {l : ℕ} (hl : 0 < l) :
    WeightedCircle.Positive (finalSideWeights l) := by
  intro w hw
  simp only [finalSideWeights, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hw
  rcases hw with ⟨_hl, rfl⟩ | rfl <;> omega

theorem firstSideWeights_positive {r : ℕ} (hr : 0 < r) :
    WeightedCircle.Positive (firstSideWeights r) := by
  intro w hw
  simp only [firstSideWeights, List.mem_cons, List.mem_replicate] at hw
  rcases hw with rfl | ⟨_hr, rfl⟩ <;> omega

theorem finalSideWeights_ne_nil {l : ℕ} (_hl : 0 < l) :
    finalSideWeights l ≠ [] := by
  simpa only [List.ne_nil_iff_length_pos, finalSideWeights_length] using
    Nat.succ_pos l

theorem firstSideWeights_ne_nil {r : ℕ} (_hr : 0 < r) :
    firstSideWeights r ≠ [] := by
  simp [firstSideWeights]

/-- Rotate the circle counterclockwise by `π / 4`. -/
noncomputable def quarterRotation : Circle ≃ₜ Circle :=
  Homeomorph.mulLeft (Circle.exp (Real.pi / 4))

/-- Put the final side of an `(l+1)`-gon on the right side of the square. -/
noncomputable def finalSideBoundaryHomeomorph (l : ℕ) (hl : 0 < l) :
    Circle ≃ₜ boundary :=
  (WeightedCircle.circleHomeomorph
      (finalSideWeights l) (finalSideWeights_positive hl)
      (finalSideWeights_ne_nil hl)).trans
    (quarterRotation.trans circleBoundaryHomeomorph)

/-- Put the first side of an `(r+1)`-gon on the same square side, but with reversed traversal. -/
noncomputable def firstSideBoundaryHomeomorph (r : ℕ) (hr : 0 < r) :
    Circle ≃ₜ boundary :=
  (WeightedCircle.circleHomeomorph
      (firstSideWeights r) (firstSideWeights_positive hr)
      (firstSideWeights_ne_nil hr)).trans
    ((Homeomorph.inv Circle).trans
      (quarterRotation.trans circleBoundaryHomeomorph))

theorem abs_sin_le_cos_of_mem_Icc
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    |Real.sin θ| ≤ Real.cos θ := by
  have hquarter : Real.pi / 4 ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hhalf : -(Real.pi / 2) ≤ -(Real.pi / 4) := by
    linarith [Real.pi_pos]
  by_cases hnonneg : 0 ≤ θ
  · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      hnonneg (hθ.2.trans (by linarith [Real.pi_pos])))]
    rw [← Real.sin_pi_div_two_sub]
    have horder : θ ≤ Real.pi / 2 - θ := by
      linear_combination 2 * hθ.2
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · exact horder
  · have hθnonpos : θ ≤ 0 := le_of_not_ge hnonneg
    have hsinNonpos : Real.sin θ ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hθnonpos
        (by linarith [hθ.1, Real.pi_pos])
    have hsin :
        |Real.sin θ| = Real.sin (-θ) := by
      rw [Real.sin_neg, abs_of_nonpos hsinNonpos]
    rw [hsin, ← Real.cos_neg θ]
    rw [← Real.sin_pi_div_two_sub]
    have hnegLe : -θ ≤ Real.pi / 4 := by
      linarith [hθ.1]
    have horder : -θ ≤ Real.pi / 2 - (-θ) := by
      linear_combination 2 * hnegLe
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · exact horder

theorem radialToBoundary_re_eq_one_of_angle
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    (radialToBoundary (Circle.exp θ) (Circle.exp θ).coe_ne_zero).re = 1 := by
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
  have hmax :
      maxAbs (Circle.exp θ : ℂ) = Real.cos θ := by
    simp only [maxAbs, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, abs_of_nonneg hcos]
    exact max_eq_left (abs_sin_le_cos_of_mem_Icc hθ)
  have hcosPos : 0 < Real.cos θ := by
    have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
    have hcosQuarter : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 :=
      Real.cos_pi_div_four
    by_cases hθnonneg : 0 ≤ θ
    · have hle : θ ≤ Real.pi / 4 := hθ.2
      exact (hcosQuarter ▸ hsqrt).trans_le
        (Real.cos_le_cos_of_nonneg_of_le_pi hθnonneg
          (by linarith [Real.pi_pos]) hle)
    · have hneg : 0 ≤ -θ := by linarith
      have hle : -θ ≤ Real.pi / 4 := by linarith [hθ.1]
      rw [← Real.cos_neg θ]
      exact (hcosQuarter ▸ hsqrt).trans_le
        (Real.cos_le_cos_of_nonneg_of_le_pi hneg
          (by linarith [Real.pi_pos]) hle)
  unfold radialToBoundary
  rw [Complex.div_ofReal_re, hmax]
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  exact div_self hcosPos.ne'

theorem finalSideWeights_take_last (l : ℕ) :
    (finalSideWeights l).take l = List.replicate l 3 := by
  simp [finalSideWeights]

theorem finalSideWeights_get_last (l : ℕ) :
    (finalSideWeights l).get
        ⟨l, by simp only [finalSideWeights_length]; omega⟩ = l := by
  simp [finalSideWeights]

theorem firstSideWeights_get_zero (r : ℕ) :
    (firstSideWeights r).get
        ⟨0, by simp only [firstSideWeights_length]; omega⟩ = r := by
  simp [firstSideWeights]

theorem finalSideWeightedCircle_apply
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    WeightedCircle.circleHomeomorph
        (finalSideWeights l) (finalSideWeights_positive hl)
        (finalSideWeights_ne_nil hl)
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      Circle.exp
        (2 * Real.pi / (4 * l) *
          (3 * l + l * (t : ℝ))) := by
  let i :
      Fin (finalSideWeights l).length :=
    ⟨l, by simp only [finalSideWeights_length]; omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (finalSideWeights l) (finalSideWeights_positive hl)
      (finalSideWeights_ne_nil hl) i t
  rw [show PolygonCell.sideAngle (Fin.last l) t =
      2 * Real.pi / (finalSideWeights l).length *
        ((i : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [Fin.val_last, i, finalSideWeights_length]
    ring]
  rw [h]
  congr 1
  simp only [finalSideWeights_sum, finalSideWeights_get_last,
    i, finalSideWeights_take_last, List.sum_replicate,
    nsmul_eq_mul]
  push_cast
  ring

theorem firstSideWeightedCircle_apply
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    WeightedCircle.circleHomeomorph
        (firstSideWeights r) (firstSideWeights_positive hr)
        (firstSideWeights_ne_nil hr)
        (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      Circle.exp
        (2 * Real.pi / (4 * r) * (r * (t : ℝ))) := by
  let i :
      Fin (firstSideWeights r).length :=
    ⟨0, by simp only [firstSideWeights_length]; omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (firstSideWeights r) (firstSideWeights_positive hr)
      (firstSideWeights_ne_nil hr) i t
  rw [show PolygonCell.sideAngle (0 : Fin (r + 1)) t =
      2 * Real.pi / (firstSideWeights r).length *
        ((i : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, i,
      firstSideWeights_length]
    ring]
  rw [h]
  congr 1
  simp only [firstSideWeights_sum, firstSideWeights_get_zero,
    i, List.take_zero, List.sum_nil, Nat.cast_zero,
    zero_add]
  push_cast
  ring

theorem finalSideBoundaryHomeomorph_apply
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    finalSideBoundaryHomeomorph l hl
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      circleBoundaryHomeomorph
        (Circle.exp
          (-(Real.pi / 4) + Real.pi / 2 * (t : ℝ))) := by
  change
    circleBoundaryHomeomorph
        (quarterRotation
          (WeightedCircle.circleHomeomorph
            (finalSideWeights l) (finalSideWeights_positive hl)
            (finalSideWeights_ne_nil hl)
            (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)))) =
      _
  rw [finalSideWeightedCircle_apply l hl t]
  apply congrArg circleBoundaryHomeomorph
  change
    Circle.exp (Real.pi / 4) *
        Circle.exp
          (2 * Real.pi / (4 * l) *
            (3 * l + l * (t : ℝ))) =
      Circle.exp
        (-(Real.pi / 4) + Real.pi / 2 * (t : ℝ))
  rw [← Circle.exp_add]
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  have hlReal : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp [hlReal]
  ring

theorem firstSideBoundaryHomeomorph_apply
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    firstSideBoundaryHomeomorph r hr
        (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      circleBoundaryHomeomorph
        (Circle.exp
          (Real.pi / 4 - Real.pi / 2 * (t : ℝ))) := by
  change
    circleBoundaryHomeomorph
        (quarterRotation
          ((Homeomorph.inv Circle)
            (WeightedCircle.circleHomeomorph
              (firstSideWeights r) (firstSideWeights_positive hr)
              (firstSideWeights_ne_nil hr)
              (Circle.exp
                (PolygonCell.sideAngle (0 : Fin (r + 1)) t))))) =
      _
  rw [firstSideWeightedCircle_apply r hr t]
  apply congrArg circleBoundaryHomeomorph
  change
    Circle.exp (Real.pi / 4) *
        (Circle.exp
          (2 * Real.pi / (4 * r) * (r * (t : ℝ))))⁻¹ =
      Circle.exp
        (Real.pi / 4 - Real.pi / 2 * (t : ℝ))
  rw [← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrReal]
  ring

/-- The two fresh sides have exactly the same point of the local square after reversing the
right-child parameter. -/
theorem finalSide_eq_firstSide_symm
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) (t : unitInterval) :
    finalSideBoundaryHomeomorph l hl
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      firstSideBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1))
            (unitInterval.symm t))) := by
  rw [finalSideBoundaryHomeomorph_apply,
    firstSideBoundaryHomeomorph_apply]
  apply congrArg circleBoundaryHomeomorph
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  simp only [unitInterval.coe_symm_eq, Int.cast_zero, zero_mul, add_zero]
  ring

theorem finalSideBoundaryHomeomorph_re
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    (finalSideBoundaryHomeomorph l hl
      (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))).1.re = 1 := by
  rw [finalSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  apply radialToBoundary_re_eq_one_of_angle
  constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]

theorem firstSideBoundaryHomeomorph_re
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (firstSideBoundaryHomeomorph r hr
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin (r + 1)) t))).1.re = 1 := by
  rw [firstSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  apply radialToBoundary_re_eq_one_of_angle
  constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]

/-- Square model for the selected child of a nondegenerate P2 split. -/
noncomputable def finalSideCellHomeomorph (l : ℕ) (hl : 0 < l) :
    PolygonCell (l + 1) ≃ₜ square :=
  cellSquareHomeomorph (finalSideBoundaryHomeomorph l hl)

/-- Square model for the right child of a nondegenerate P2 split. -/
noncomputable def firstSideCellHomeomorph (r : ℕ) (hr : 0 < r) :
    PolygonCell (r + 1) ≃ₜ square :=
  cellSquareHomeomorph (firstSideBoundaryHomeomorph r hr)

@[simp]
theorem finalSideCellHomeomorph_side
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    finalSideCellHomeomorph l hl
        (PolygonCell.side (Fin.last l) t) =
      boundaryInclusion
        (finalSideBoundaryHomeomorph l hl
          (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))) := by
  exact cellSquareHomeomorph_ofCircle
    (finalSideBoundaryHomeomorph l hl)
    (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))

@[simp]
theorem firstSideCellHomeomorph_side
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    firstSideCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1)) t) =
      boundaryInclusion
        (firstSideBoundaryHomeomorph r hr
          (Circle.exp
            (PolygonCell.sideAngle (0 : Fin (r + 1)) t))) := by
  exact cellSquareHomeomorph_ofCircle
    (firstSideBoundaryHomeomorph r hr)
    (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t))

theorem finalSideCell_eq_firstSideCell_symm
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) (t : unitInterval) :
    (finalSideCellHomeomorph l hl
        (PolygonCell.side (Fin.last l) t)).1 =
      (firstSideCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1))
          (unitInterval.symm t))).1 := by
  rw [finalSideCellHomeomorph_side, firstSideCellHomeomorph_side]
  exact congrArg (fun z : boundary ↦ z.1)
    (finalSide_eq_firstSide_symm l r hl hr t)

theorem finalSideCellHomeomorph_side_re
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    (finalSideCellHomeomorph l hl
      (PolygonCell.side (Fin.last l) t)).1.re = 1 := by
  rw [finalSideCellHomeomorph_side]
  exact finalSideBoundaryHomeomorph_re l hl t

theorem firstSideCellHomeomorph_side_re
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (firstSideCellHomeomorph r hr
      (PolygonCell.side (0 : Fin (r + 1)) t)).1.re = 1 := by
  rw [firstSideCellHomeomorph_side]
  exact firstSideBoundaryHomeomorph_re r hr t

@[simp]
theorem finalSideBoundaryHomeomorph_zero_im
    (l : ℕ) (hl : 0 < l) :
    (finalSideBoundaryHomeomorph l hl
      (Circle.exp
        (PolygonCell.sideAngle (Fin.last l) 0))).1.im = -1 := by
  rw [finalSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  change
    (radialToBoundary
      (Circle.exp (-(Real.pi / 4) + Real.pi / 2 * (0 : ℝ)))
      _).im = -1
  unfold radialToBoundary
  rw [Complex.div_ofReal_im]
  simp only [mul_zero, add_zero, Circle.coe_exp, Complex.exp_ofReal_mul_I_im,
    Real.sin_neg, Real.sin_pi_div_four, maxAbs]
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg,
    Real.cos_pi_div_four]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hhalf : 0 < Real.sqrt 2 / 2 := div_pos hsqrt (by norm_num)
  rw [abs_of_pos hhalf, abs_neg, abs_of_pos hhalf, max_self]
  field_simp [hsqrt.ne']

@[simp]
theorem finalSideBoundaryHomeomorph_one_im
    (l : ℕ) (hl : 0 < l) :
    (finalSideBoundaryHomeomorph l hl
      (Circle.exp
        (PolygonCell.sideAngle (Fin.last l) 1))).1.im = 1 := by
  rw [finalSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  change
    (radialToBoundary
      (Circle.exp (-(Real.pi / 4) + Real.pi / 2 * (1 : ℝ)))
      _).im = 1
  unfold radialToBoundary
  rw [Complex.div_ofReal_im]
  simp only [mul_one, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  have hangle :
      -(Real.pi / 4) + Real.pi / 2 = Real.pi / 4 := by ring
  rw [hangle, Real.sin_pi_div_four]
  simp only [maxAbs, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hhalf : 0 < Real.sqrt 2 / 2 := div_pos hsqrt (by norm_num)
  rw [abs_of_pos hhalf, max_self]
  field_simp [hsqrt.ne']

/-- The distinguished final side covers every point of the local square's right edge. -/
theorem exists_finalSideCellHomeomorph_side_of_re_eq_one
    (l : ℕ) (hl : 0 < l) (z : square) (hz : z.1.re = 1) :
    ∃ t : unitInterval,
      finalSideCellHomeomorph l hl
        (PolygonCell.side (Fin.last l) t) = z := by
  have hzIm : z.1.im ∈ Set.Icc (-1 : ℝ) 1 := by
    have him := abs_im_le_maxAbs z.1 |>.trans z.2
    rw [abs_le] at him
    exact him
  let seamIm : unitInterval → ℝ := fun t ↦
    (finalSideCellHomeomorph l hl
      (PolygonCell.side (Fin.last l) t)).1.im
  have hcontinuous : Continuous seamIm := by
    dsimp [seamIm]
    fun_prop
  have hzero : seamIm 0 = -1 := by
    dsimp [seamIm]
    rw [finalSideCellHomeomorph_side]
    exact finalSideBoundaryHomeomorph_zero_im l hl
  have hone : seamIm 1 = 1 := by
    dsimp [seamIm]
    rw [finalSideCellHomeomorph_side]
    exact finalSideBoundaryHomeomorph_one_im l hl
  have hrange : z.1.im ∈ Set.range seamIm := by
    apply (intermediate_value_univ (0 : unitInterval) 1 hcontinuous)
    simpa only [hzero, hone] using hzIm
  rcases hrange with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply Complex.ext
  · exact (finalSideCellHomeomorph_side_re l hl t).trans hz.symm
  · exact ht

/-- The distinguished first side covers every point of the local square's right edge. -/
theorem exists_firstSideCellHomeomorph_side_of_re_eq_one
    (r : ℕ) (hr : 0 < r) (z : square) (hz : z.1.re = 1) :
    ∃ t : unitInterval,
      firstSideCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1)) t) = z := by
  obtain ⟨t, ht⟩ :=
    exists_finalSideCellHomeomorph_side_of_re_eq_one r hr z hz
  refine ⟨unitInterval.symm t, ?_⟩
  apply Subtype.ext
  exact (finalSideCell_eq_firstSideCell_symm r r hr hr t).symm.trans
    (congrArg Subtype.val ht)

/-! ## Gluing two square models along their right sides -/

/-- Place a local square as the left half of the outer square. -/
noncomputable def leftPlacement : C(square, square) where
  toFun z :=
    ⟨Complex.mk ((z.1.re - 1) / 2) z.1.im, by
      change max |(z.1.re - 1) / 2| |z.1.im| ≤ 1
      have hre := abs_re_le_maxAbs z.1 |>.trans z.2
      have him := abs_im_le_maxAbs z.1 |>.trans z.2
      rw [abs_le] at hre him
      apply max_le
      · rw [abs_le]
        constructor <;> linarith [hre.1, hre.2]
      · exact (abs_le.mpr him)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : square ↦
      Complex.mk ((z.1.re - 1) / 2) z.1.im)
    have hre : Continuous (fun z : square ↦ (z.1.re - 1) / 2) := by
      fun_prop
    have him : Continuous (fun z : square ↦ z.1.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    convert
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul
          (continuous_const : Continuous (fun _ : square ↦ Complex.I))) using 1
    funext z
    apply Complex.ext <;> simp

/-- Place a local square, reflected horizontally, as the right half of the outer square. -/
noncomputable def rightPlacement : C(square, square) where
  toFun z :=
    ⟨Complex.mk ((1 - z.1.re) / 2) z.1.im, by
      change max |(1 - z.1.re) / 2| |z.1.im| ≤ 1
      have hre := abs_re_le_maxAbs z.1 |>.trans z.2
      have him := abs_im_le_maxAbs z.1 |>.trans z.2
      rw [abs_le] at hre him
      apply max_le
      · rw [abs_le]
        constructor <;> linarith [hre.1, hre.2]
      · exact (abs_le.mpr him)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : square ↦
      Complex.mk ((1 - z.1.re) / 2) z.1.im)
    have hre : Continuous (fun z : square ↦ (1 - z.1.re) / 2) := by
      fun_prop
    have him : Continuous (fun z : square ↦ z.1.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    convert
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul
          (continuous_const : Continuous (fun _ : square ↦ Complex.I))) using 1
    funext z
    apply Complex.ext <;> simp

@[simp]
theorem leftPlacement_re (z : square) :
    (leftPlacement z).1.re = (z.1.re - 1) / 2 :=
  rfl

@[simp]
theorem leftPlacement_im (z : square) :
    (leftPlacement z).1.im = z.1.im :=
  rfl

@[simp]
theorem rightPlacement_re (z : square) :
    (rightPlacement z).1.re = (1 - z.1.re) / 2 :=
  rfl

@[simp]
theorem rightPlacement_im (z : square) :
    (rightPlacement z).1.im = z.1.im :=
  rfl

theorem leftPlacement_injective : Function.Injective leftPlacement := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have hre := congrArg (fun q : square ↦ q.1.re) h
    simp only [leftPlacement_re] at hre
    linarith
  · simpa only [leftPlacement_im] using
      congrArg (fun q : square ↦ q.1.im) h

theorem rightPlacement_injective : Function.Injective rightPlacement := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have hre := congrArg (fun q : square ↦ q.1.re) h
    simp only [rightPlacement_re] at hre
    linarith
  · simpa only [rightPlacement_im] using
      congrArg (fun q : square ↦ q.1.im) h

theorem leftPlacement_re_nonpos (z : square) :
    (leftPlacement z).1.re ≤ 0 := by
  have hre := abs_re_le_maxAbs z.1 |>.trans z.2
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (le_trans (le_abs_self _) hre)) (by norm_num)

theorem rightPlacement_re_nonneg (z : square) :
    0 ≤ (rightPlacement z).1.re := by
  have hre := abs_re_le_maxAbs z.1 |>.trans z.2
  exact div_nonneg (sub_nonneg.mpr (le_trans (le_abs_self _) hre))
    (by norm_num)

/-- The two placements agree on their common local right side. -/
theorem leftPlacement_eq_rightPlacement_of_re_eq_one
    (z w : square) (hreZ : z.1.re = 1) (hreW : w.1.re = 1)
    (him : z.1.im = w.1.im) :
    leftPlacement z = rightPlacement w := by
  apply Subtype.ext
  apply Complex.ext <;> simp [hreZ, hreW, him]

theorem exists_leftPlacement_of_re_nonpos
    (z : square) (hz : z.1.re ≤ 0) :
    ∃ w : square, leftPlacement w = z := by
  let w : ℂ := Complex.mk (2 * z.1.re + 1) z.1.im
  have hw : w ∈ square := by
    change max |2 * z.1.re + 1| |z.1.im| ≤ 1
    have hre := abs_re_le_maxAbs z.1 |>.trans z.2
    have him := abs_im_le_maxAbs z.1 |>.trans z.2
    rw [abs_le] at hre him
    apply max_le
    · rw [abs_le]
      constructor <;> linarith [hre.1, hz]
    · exact abs_le.mpr him
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply Complex.ext <;> simp [w]

theorem exists_rightPlacement_of_re_nonneg
    (z : square) (hz : 0 ≤ z.1.re) :
    ∃ w : square, rightPlacement w = z := by
  let w : ℂ := Complex.mk (1 - 2 * z.1.re) z.1.im
  have hw : w ∈ square := by
    change max |1 - 2 * z.1.re| |z.1.im| ≤ 1
    have hre := abs_re_le_maxAbs z.1 |>.trans z.2
    have him := abs_im_le_maxAbs z.1 |>.trans z.2
    rw [abs_le] at hre him
    apply max_le
    · rw [abs_le]
      constructor <;> linarith [hre.2, hz]
    · exact abs_le.mpr him
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply Complex.ext <;> simp [w]

theorem leftPlacement_or_rightPlacement (z : square) :
    (∃ w : square, leftPlacement w = z) ∨
      (∃ w : square, rightPlacement w = z) := by
  rcases le_total z.1.re 0 with h | h
  · exact Or.inl (exists_leftPlacement_of_re_nonpos z h)
  · exact Or.inr (exists_rightPlacement_of_re_nonneg z h)

/-! ## Gluing two square disks along their distinguished sides -/

/-- The disjoint union of the two local square disks. -/
abbrev SquarePair :=
  Sum square square

/--
The generating seam relation: the right side of the left local square is glued, point for
point, to the right side of the horizontally reflected right local square.
-/
inductive SeamGenerator : SquarePair → SquarePair → Prop
  | glue (z w : square) (hz : z.1.re = 1) (hw : w.1.re = 1)
      (him : z.1.im = w.1.im) :
      SeamGenerator (.inl z) (.inr w)

/-- The equivalence relation generated by the common side of the two square disks. -/
abbrev seamSetoid : Setoid SquarePair :=
  Relation.EqvGen.setoid SeamGenerator

/-- The topological quotient obtained by gluing the two local square disks along the seam. -/
abbrev SquareGluing :=
  Quotient seamSetoid

/-- Merge the two local squares into the left and right halves of one outer square. -/
noncomputable def squarePairMerge : SquarePair → square :=
  Sum.elim leftPlacement rightPlacement

theorem continuous_squarePairMerge :
    Continuous squarePairMerge :=
  leftPlacement.continuous.sumElim rightPlacement.continuous

theorem squarePairMerge_eq_of_seamGenerator
    {x y : SquarePair} (hxy : SeamGenerator x y) :
    squarePairMerge x = squarePairMerge y := by
  cases hxy with
  | glue z w hz hw him =>
      exact leftPlacement_eq_rightPlacement_of_re_eq_one z w hz hw him

/-- The merge map is constant on the equivalence closure of the seam relation. -/
theorem squarePairMerge_respects
    {x y : SquarePair} (hxy : Relation.EqvGen SeamGenerator x y) :
    squarePairMerge x = squarePairMerge y := by
  induction hxy with
  | rel _ _ h => exact squarePairMerge_eq_of_seamGenerator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem square_re_le_one (z : square) :
    z.1.re ≤ 1 :=
  (le_abs_self z.1.re).trans (abs_re_le_maxAbs z.1 |>.trans z.2)

/-- Equality between opposite merged summands can only occur on the declared seam. -/
theorem squarePairMerge_eqvGen_inl_inr
    (z w : square)
    (hzw : squarePairMerge (.inl z) = squarePairMerge (.inr w)) :
    Relation.EqvGen SeamGenerator (.inl z) (.inr w) := by
  have hre := congrArg (fun q : square ↦ q.1.re) hzw
  have hz : z.1.re = 1 := by
    simp only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_re, rightPlacement_re] at hre
    linarith [square_re_le_one z, square_re_le_one w]
  have hw : w.1.re = 1 := by
    simp only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_re, rightPlacement_re] at hre
    linarith [square_re_le_one z, square_re_le_one w]
  have him : z.1.im = w.1.im := by
    simpa only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_im, rightPlacement_im] using
        congrArg (fun q : square ↦ q.1.im) hzw
  exact Relation.EqvGen.rel _ _
    (SeamGenerator.glue z w hz hw him)

/--
No identifications are hidden by the planar merge: equality after merging is exactly generated
by equality inside one summand and the declared seam relation.
-/
theorem squarePairMerge_eqvGen_of_eq
    {x y : SquarePair} (hxy : squarePairMerge x = squarePairMerge y) :
    Relation.EqvGen SeamGenerator x y := by
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          have hzw : z = w := leftPlacement_injective hxy
          subst w
          exact Relation.EqvGen.refl _
      | inr w =>
          exact squarePairMerge_eqvGen_inl_inr z w hxy
  | inr z =>
      cases y with
      | inl w =>
          exact Relation.EqvGen.symm _ _
            (squarePairMerge_eqvGen_inl_inr w z hxy.symm)
      | inr w =>
          have hzw : z = w := rightPlacement_injective hxy
          subst w
          exact Relation.EqvGen.refl _

/-- The continuous map induced on the quotient by merging the two local squares. -/
noncomputable def squareGluingMap : C(SquareGluing, square) where
  toFun :=
    Quotient.lift squarePairMerge fun _ _ hxy ↦ squarePairMerge_respects hxy
  continuous_toFun :=
    continuous_squarePairMerge.quotient_lift fun _ _ hxy ↦
      squarePairMerge_respects hxy

@[simp]
theorem squareGluingMap_mk (x : SquarePair) :
    squareGluingMap (@Quotient.mk'' SquarePair seamSetoid x) =
      squarePairMerge x :=
  rfl

theorem squareGluingMap_injective :
    Function.Injective squareGluingMap := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
          apply Quotient.sound
          apply squarePairMerge_eqvGen_of_eq
          simpa only [squareGluingMap_mk] using hqr

theorem squareGluingMap_surjective :
    Function.Surjective squareGluingMap := by
  intro z
  rcases leftPlacement_or_rightPlacement z with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine ⟨@Quotient.mk'' SquarePair seamSetoid (.inl w), ?_⟩
    change leftPlacement w = z
    exact hw
  · refine ⟨@Quotient.mk'' SquarePair seamSetoid (.inr w), ?_⟩
    change rightPlacement w = z
    exact hw

theorem isCompact_square : IsCompact square :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_square, isBounded_square⟩

/-- Gluing two square disks along the selected sides is again a closed disk. -/
noncomputable def squareGluingHomeomorph : SquareGluing ≃ₜ square := by
  letI : CompactSpace square :=
    isCompact_iff_compactSpace.mp isCompact_square
  let e : SquareGluing ≃ square :=
    Equiv.ofBijective squareGluingMap
      ⟨squareGluingMap_injective, squareGluingMap_surjective⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) squareGluingMap.continuous

@[simp]
theorem squareGluingHomeomorph_apply (q : SquareGluing) :
    squareGluingHomeomorph q = squareGluingMap q :=
  rfl

/-! ## Transporting the seam model to two nondegenerate polygon cells -/

/-- The two polygon cells occurring in a nondegenerate, positively oriented P2 split. -/
abbrev ChildPair (l r : ℕ) :=
  Sum (PolygonCell (l + 1)) (PolygonCell (r + 1))

/--
The geometric seam relation on the two child cells, expressed through their square models.
This formulation records the entire common edge and is convenient for quotient-kernel arguments.
-/
inductive ChildSeamGenerator (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    ChildPair l r → ChildPair l r → Prop
  | glue (z : PolygonCell (l + 1)) (w : PolygonCell (r + 1))
      (hz : (finalSideCellHomeomorph l hl z).1.re = 1)
      (hw : (firstSideCellHomeomorph r hr w).1.re = 1)
      (him :
        (finalSideCellHomeomorph l hl z).1.im =
          (firstSideCellHomeomorph r hr w).1.im) :
      ChildSeamGenerator l r hl hr (.inl z) (.inr w)

/-! The equivalence relation generated by identifying the two child-cell seam edges. -/
/-- The setoid generated by identifying the two child-cell seam edges. -/
abbrev childSeamSetoid (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    Setoid (ChildPair l r) :=
  Relation.EqvGen.setoid (ChildSeamGenerator l r hl hr)

/-- The quotient of the two child polygon cells by their complete common side. -/
abbrev ChildGluing (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :=
  Quotient (childSeamSetoid l r hl hr)

/-- Straighten both P2 child cells simultaneously to their local square models. -/
noncomputable def childPairSquarePairHomeomorph
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    ChildPair l r ≃ₜ SquarePair :=
  Homeomorph.sumCongr
    (finalSideCellHomeomorph l hl)
    (firstSideCellHomeomorph r hr)

@[simp]
theorem childPairSquarePairHomeomorph_inl
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (z : PolygonCell (l + 1)) :
    childPairSquarePairHomeomorph l r hl hr (.inl z) =
      .inl (finalSideCellHomeomorph l hl z) :=
  rfl

@[simp]
theorem childPairSquarePairHomeomorph_inr
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (z : PolygonCell (r + 1)) :
    childPairSquarePairHomeomorph l r hl hr (.inr z) =
      .inr (firstSideCellHomeomorph r hr z) :=
  rfl

theorem childSeamGenerator_map
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    {x y : ChildPair l r}
    (hxy : ChildSeamGenerator l r hl hr x y) :
    SeamGenerator
      (childPairSquarePairHomeomorph l r hl hr x)
      (childPairSquarePairHomeomorph l r hl hr y) := by
  cases hxy with
  | glue z w hz hw him =>
      exact SeamGenerator.glue
        (finalSideCellHomeomorph l hl z)
        (firstSideCellHomeomorph r hr w) hz hw him

theorem childSeamGenerator_comap
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    {x y : ChildPair l r}
    (hxy :
      SeamGenerator
        (childPairSquarePairHomeomorph l r hl hr x)
        (childPairSquarePairHomeomorph l r hl hr y)) :
    ChildSeamGenerator l r hl hr x y := by
  cases x <;> cases y
  all_goals
    cases hxy
  case inl.inr.glue z w hz hw him =>
    exact ChildSeamGenerator.glue z w hz hw him

/-- The simultaneous child straightening identifies exactly the two generated seam relations. -/
theorem childSeam_eqvGen_iff
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x y : ChildPair l r) :
    Relation.EqvGen (ChildSeamGenerator l r hl hr) x y ↔
      Relation.EqvGen SeamGenerator
        (childPairSquarePairHomeomorph l r hl hr x)
        (childPairSquarePairHomeomorph l r hl hr y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (childSeamGenerator_map l r hl hr h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e := childPairSquarePairHomeomorph l r hl hr
    have hcomap :
        ∀ {u v : SquarePair}, Relation.EqvGen SeamGenerator u v →
          Relation.EqvGen (ChildSeamGenerator l r hl hr)
            (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          apply Relation.EqvGen.rel _ _
          apply childSeamGenerator_comap l r hl hr
          simpa only [e, Homeomorph.apply_symm_apply] using h
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using hcomap hxy

/-- The actual two-child polygon quotient of a nondegenerate P2 cut is a closed disk. -/
noncomputable def childGluingHomeomorph
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    ChildGluing l r hl hr ≃ₜ square :=
  (Homeomorph.Quotient.congr
      (childPairSquarePairHomeomorph l r hl hr)
      (childSeam_eqvGen_iff l r hl hr)).trans
    squareGluingHomeomorph

/-- A marked side of a polygon with at least two sides has no parameter self-overlap. -/
theorem PolygonCell.side_injective_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    Function.Injective (PolygonCell.side i) := by
  intro s t hst
  have hexp :
      Circle.exp (PolygonCell.sideAngle i s) =
        Circle.exp (PolygonCell.sideAngle i t) := by
    apply Circle.ext
    exact congrArg PolygonCell.val hst
  let a : ℝ := 2 * Real.pi * i.val / n
  let b : ℝ := 2 * Real.pi * (i.val + 1) / n
  have hnpos : 0 < (n : ℝ) := by positivity
  have hab : b - a < 2 * Real.pi := by
    have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnOne : (1 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnTwo
    have hcalc : b - a = (2 * Real.pi) / n := by
      dsimp [a, b]
      field_simp
      ring
    rw [hcalc, div_lt_iff₀ hnpos]
    nlinarith [Real.pi_pos]
  have hsMem : PolygonCell.sideAngle i s ∈ Set.Icc a b := by
    dsimp [PolygonCell.sideAngle, a, b]
    constructor
    · apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith [s.property.1, Real.pi_pos]
    · apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith [s.property.2, Real.pi_pos]
  have htMem : PolygonCell.sideAngle i t ∈ Set.Icc a b := by
    dsimp [PolygonCell.sideAngle, a, b]
    constructor
    · apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith [t.property.1, Real.pi_pos]
    · apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith [t.property.2, Real.pi_pos]
  have hangle :=
    Circle.exp_injOn_Icc hab hsMem htMem hexp
  apply Subtype.ext
  dsimp [PolygonCell.sideAngle] at hangle
  have hfactor : 2 * Real.pi / n ≠ 0 := by positivity
  have hargs :
      (i.val : ℝ) + (s : ℝ) =
        (i.val : ℝ) + (t : ℝ) := by
    apply mul_left_cancel₀ hfactor
    calc
      (2 * Real.pi / n) * ((i.val : ℝ) + (s : ℝ)) =
          2 * Real.pi * ((i.val : ℝ) + (s : ℝ)) / n := by ring
      _ = 2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / n := hangle
      _ = (2 * Real.pi / n) * ((i.val : ℝ) + (t : ℝ)) := by ring
  exact add_left_cancel hargs

/-- The parameter-level fresh-edge identification used by a positive P2 split. -/
inductive ParamChildSeamGenerator (l r : ℕ) :
    ChildPair l r → ChildPair l r → Prop
  | glue (t : unitInterval) :
      ParamChildSeamGenerator l r
        (.inl (PolygonCell.side (Fin.last l) t))
        (.inr
          (PolygonCell.side (0 : Fin (r + 1))
            (unitInterval.symm t)))

theorem paramChildSeamGenerator_to_childSeam
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    {x y : ChildPair l r}
    (hxy : ParamChildSeamGenerator l r x y) :
    ChildSeamGenerator l r hl hr x y := by
  cases hxy with
  | glue t =>
      refine ChildSeamGenerator.glue _ _
        (finalSideCellHomeomorph_side_re l hl t)
        (firstSideCellHomeomorph_side_re r hr (unitInterval.symm t)) ?_
      exact congrArg Complex.im
        (finalSideCell_eq_firstSideCell_symm l r hl hr t)

theorem childSeamGenerator_to_paramEqvGen
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    {x y : ChildPair l r}
    (hxy : ChildSeamGenerator l r hl hr x y) :
    Relation.EqvGen (ParamChildSeamGenerator l r) x y := by
  cases hxy with
  | glue z w hz hw him =>
      obtain ⟨t, ht⟩ :=
        exists_finalSideCellHomeomorph_side_of_re_eq_one l hl
          (finalSideCellHomeomorph l hl z) hz
      obtain ⟨u, hu⟩ :=
        exists_firstSideCellHomeomorph_side_of_re_eq_one r hr
          (firstSideCellHomeomorph r hr w) hw
      have hzSide : z = PolygonCell.side (Fin.last l) t := by
        apply (finalSideCellHomeomorph l hl).injective
        exact ht.symm
      have hwSide :
          w = PolygonCell.side (0 : Fin (r + 1)) u := by
        apply (firstSideCellHomeomorph r hr).injective
        exact hu.symm
      have hSquare :
          finalSideCellHomeomorph l hl z =
            firstSideCellHomeomorph r hr w := by
        apply Subtype.ext
        apply Complex.ext
        · exact hz.trans hw.symm
        · exact him
      have hside :
          PolygonCell.side (0 : Fin (r + 1)) u =
            PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t) := by
        apply (firstSideCellHomeomorph r hr).injective
        calc
          firstSideCellHomeomorph r hr
              (PolygonCell.side (0 : Fin (r + 1)) u) =
              firstSideCellHomeomorph r hr w := congrArg _ hwSide.symm
          _ = finalSideCellHomeomorph l hl z := hSquare.symm
          _ = finalSideCellHomeomorph l hl
              (PolygonCell.side (Fin.last l) t) := congrArg _ hzSide
          _ = firstSideCellHomeomorph r hr
              (PolygonCell.side (0 : Fin (r + 1))
                (unitInterval.symm t)) := by
                apply Subtype.ext
                exact finalSideCell_eq_firstSideCell_symm l r hl hr t
      have hut : u = unitInterval.symm t :=
        PolygonCell.side_injective_of_two_le
          (n := r + 1) (by omega) (0 : Fin (r + 1)) hside
      subst u
      rw [hzSide, hwSide]
      exact Relation.EqvGen.rel _ _
        (ParamChildSeamGenerator.glue t)

/-- The square-model seam is exactly the equivalence closure of the fresh-side parameter map. -/
theorem paramChildSeam_eqvGen_iff
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x y : ChildPair l r) :
    Relation.EqvGen (ParamChildSeamGenerator l r) x y ↔
      Relation.EqvGen (ChildSeamGenerator l r hl hr) x y := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (paramChildSeamGenerator_to_childSeam l r hl hr h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact childSeamGenerator_to_paramEqvGen l r hl hr h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-! The parameter-independent seam equivalence relation used by the quotient comparison. -/
/-- The setoid used by the parameter-independent quotient comparison. -/
abbrev paramChildSeamSetoid (l r : ℕ) :
    Setoid (ChildPair l r) :=
  Relation.EqvGen.setoid (ParamChildSeamGenerator l r)

/-- The quotient of the parameterized child pair by its seam relation. -/
abbrev ParamChildGluing (l r : ℕ) :=
  Quotient (paramChildSeamSetoid l r)

/--
Two nondegenerate P2 child polygons, glued by the precise reversed fresh-edge parameter, form a
closed disk.
-/
noncomputable def paramChildGluingHomeomorph
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    ParamChildGluing l r ≃ₜ square :=
  (Homeomorph.Quotient.congrRight
      (paramChildSeam_eqvGen_iff l r hl hr)).trans
    (childGluingHomeomorph l r hl hr)

/-! ## The external boundary arcs of the glued child disk -/

/-- The old-boundary arc of the selected child, before placing its square on the left. -/
noncomputable def finalOldArcLocal
    (l : ℕ) (hl : 0 < l) : C(Set.Icc (0 : ℝ) l, square) where
  toFun s :=
    finalSideCellHomeomorph l hl
      (PolygonCell.ofCircle (l + 1)
        (Circle.exp (2 * Real.pi * s.1 / (l + 1))))
  continuous_toFun := by
    apply (finalSideCellHomeomorph l hl).continuous.comp
    apply (PolygonCell.ofCircle (l + 1)).continuous.comp
    apply Circle.exp.continuous.comp
    fun_prop

/-- The old-boundary arc of the right child, before its horizontal reflection. -/
noncomputable def firstOldArcLocal
    (r : ℕ) (hr : 0 < r) : C(Set.Icc (0 : ℝ) r, square) where
  toFun s :=
    firstSideCellHomeomorph r hr
      (PolygonCell.ofCircle (r + 1)
        (Circle.exp
          (2 * Real.pi * (1 + s.1) / (r + 1))))
  continuous_toFun := by
    apply (firstSideCellHomeomorph r hr).continuous.comp
    apply (PolygonCell.ofCircle (r + 1)).continuous.comp
    apply Circle.exp.continuous.comp
    fun_prop

@[simp]
theorem finalOldArcLocal_apply
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    finalOldArcLocal l hl s =
      finalSideCellHomeomorph l hl
        (PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * s.1 / (l + 1)))) :=
  rfl

@[simp]
theorem firstOldArcLocal_apply
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    firstOldArcLocal r hr s =
      firstSideCellHomeomorph r hr
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (2 * Real.pi * (1 + s.1) / (r + 1)))) :=
  rfl

theorem finalOldArcLocal_re_eq_one_iff_endpoint
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    (finalOldArcLocal l hl s).1.re = 1 ↔
      s.1 = 0 ∨ s.1 = l := by
  constructor
  · intro hre
    obtain ⟨t, ht⟩ :=
      exists_finalSideCellHomeomorph_side_of_re_eq_one l hl
        (finalOldArcLocal l hl s) hre
    have hcell :
        PolygonCell.ofCircle (l + 1)
            (Circle.exp (2 * Real.pi * s.1 / (l + 1))) =
          PolygonCell.side (Fin.last l) t := by
      apply (finalSideCellHomeomorph l hl).injective
      exact ht.symm
    have hexp :
        Circle.exp (2 * Real.pi * s.1 / (l + 1)) =
          Circle.exp
            (2 * Real.pi * ((l : ℝ) + (t : ℝ)) / (l + 1)) := by
      apply Circle.ext
      simpa [PolygonCell.ofCircle, PolygonCell.side,
        PolygonCell.sideAngle] using congrArg PolygonCell.val hcell
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
    have hnpos : 0 < (l + 1 : ℝ) := by positivity
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    have heq :
        s.1 = (l : ℝ) + (t : ℝ) + (k : ℝ) * (l + 1) := by
      field_simp [hnpos.ne'] at hk
      nlinarith [Real.pi_pos]
    have hkUpper : (k : ℝ) ≤ 0 := by
      nlinarith [s.2.2, t.property.1, hnpos]
    have hkLower : (-1 : ℝ) ≤ k := by
      nlinarith [s.2.1, t.property.2, hnpos]
    have hkUpperInt : k ≤ 0 := by exact_mod_cast hkUpper
    have hkLowerInt : (-1 : ℤ) ≤ k := by exact_mod_cast hkLower
    have hkCases : k = -1 ∨ k = 0 := by omega
    rcases hkCases with rfl | rfl
    · left
      norm_num at heq
      nlinarith [s.2.1, t.property.2]
    · right
      norm_num at heq
      exact_mod_cast (by nlinarith [s.2.2, t.property.1] :
        s.1 = (l : ℝ))
  · intro hs
    rcases hs with hs | hs
    · have hs0 : s = ⟨0, by constructor <;> positivity⟩ :=
        Subtype.ext hs
      subst s
      rw [finalOldArcLocal_apply]
      norm_num
      change
        (finalSideCellHomeomorph l hl
          (PolygonCell.ofCircle (l + 1) 1)).1.re = 1
      have hcell :
          PolygonCell.ofCircle (l + 1) 1 =
            PolygonCell.side (Fin.last l) 1 := by
        change
          PolygonCell.ofCircle (l + 1) 1 =
            PolygonCell.ofCircle (l + 1)
              (Circle.exp (PolygonCell.sideAngle (Fin.last l) 1))
        apply congrArg (PolygonCell.ofCircle (l + 1))
        rw [← Circle.exp_zero]
        apply Circle.exp_eq_exp.mpr
        refine ⟨-1, ?_⟩
        simp [PolygonCell.sideAngle]
        field_simp [hl.ne']
        ring
      rw [hcell]
      exact finalSideCellHomeomorph_side_re l hl 1
    · have hsl : s = ⟨l, by simp⟩ := Subtype.ext hs
      subst s
      rw [finalOldArcLocal_apply]
      change
        (finalSideCellHomeomorph l hl
          (PolygonCell.ofCircle (l + 1)
            (Circle.exp (2 * Real.pi * l / (l + 1))))).1.re = 1
      have hcell :
          PolygonCell.ofCircle (l + 1)
              (Circle.exp (2 * Real.pi * l / (l + 1))) =
            PolygonCell.side (Fin.last l) 0 := by
        change
          PolygonCell.ofCircle (l + 1)
              (Circle.exp (2 * Real.pi * l / (l + 1))) =
            PolygonCell.ofCircle (l + 1)
              (Circle.exp
                (PolygonCell.sideAngle (Fin.last l) 0))
        apply congrArg (PolygonCell.ofCircle (l + 1))
        apply congrArg Circle.exp
        unfold PolygonCell.sideAngle
        simp only [Fin.val_last]
        push_cast
        ring
      rw [hcell]
      exact finalSideCellHomeomorph_side_re l hl 0

theorem finalOldArcLocal_zero_im
    (l : ℕ) (hl : 0 < l) :
    (finalOldArcLocal l hl ⟨0, by constructor <;> positivity⟩).1.im = 1 := by
  rw [finalOldArcLocal_apply]
  norm_num
  have hcell :
      PolygonCell.ofCircle (l + 1) 1 =
        PolygonCell.side (Fin.last l) 1 := by
    change
      PolygonCell.ofCircle (l + 1) 1 =
        PolygonCell.ofCircle (l + 1)
          (Circle.exp (PolygonCell.sideAngle (Fin.last l) 1))
    apply congrArg (PolygonCell.ofCircle (l + 1))
    rw [← Circle.exp_zero]
    apply Circle.exp_eq_exp.mpr
    refine ⟨-1, ?_⟩
    simp [PolygonCell.sideAngle]
    field_simp [hl.ne']
    ring
  rw [hcell, finalSideCellHomeomorph_side]
  exact finalSideBoundaryHomeomorph_one_im l hl

theorem finalOldArcLocal_last_im
    (l : ℕ) (hl : 0 < l) :
    (finalOldArcLocal l hl ⟨l, by simp⟩).1.im = -1 := by
  rw [finalOldArcLocal_apply]
  change
    (finalSideCellHomeomorph l hl
      (PolygonCell.ofCircle (l + 1)
        (Circle.exp (2 * Real.pi * l / (l + 1))))).1.im = -1
  have hcell :
      PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * l / (l + 1))) =
        PolygonCell.side (Fin.last l) 0 := by
    change
      PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * l / (l + 1))) =
        PolygonCell.ofCircle (l + 1)
          (Circle.exp
            (PolygonCell.sideAngle (Fin.last l) 0))
    apply congrArg (PolygonCell.ofCircle (l + 1))
    apply congrArg Circle.exp
    unfold PolygonCell.sideAngle
    simp only [Fin.val_last]
    push_cast
    ring
  rw [hcell, finalSideCellHomeomorph_side]
  exact finalSideBoundaryHomeomorph_zero_im l hl

theorem finalOldArcLocal_abs_im_eq_one_of_re_eq_one
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l)
    (hs : (finalOldArcLocal l hl s).1.re = 1) :
    |(finalOldArcLocal l hl s).1.im| = 1 := by
  rcases (finalOldArcLocal_re_eq_one_iff_endpoint l hl s).mp hs with h | h
  · have hs0 : s = ⟨0, by constructor <;> positivity⟩ := Subtype.ext h
    subst s
    rw [finalOldArcLocal_zero_im]
    norm_num
  · have hsl : s = ⟨l, by simp⟩ := Subtype.ext h
    subst s
    rw [finalOldArcLocal_last_im]
    norm_num

theorem firstOldArcLocal_re_eq_one_iff_endpoint
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    (firstOldArcLocal r hr s).1.re = 1 ↔
      s.1 = 0 ∨ s.1 = r := by
  constructor
  · intro hre
    obtain ⟨t, ht⟩ :=
      exists_firstSideCellHomeomorph_side_of_re_eq_one r hr
        (firstOldArcLocal r hr s) hre
    have hcell :
        PolygonCell.ofCircle (r + 1)
            (Circle.exp
              (2 * Real.pi * (1 + s.1) / (r + 1))) =
          PolygonCell.side (0 : Fin (r + 1)) t := by
      apply (firstSideCellHomeomorph r hr).injective
      exact ht.symm
    have hexp :
        Circle.exp
            (2 * Real.pi * (1 + s.1) / (r + 1)) =
          Circle.exp (2 * Real.pi * (t : ℝ) / (r + 1)) := by
      apply Circle.ext
      simpa [PolygonCell.ofCircle, PolygonCell.side,
        PolygonCell.sideAngle] using congrArg PolygonCell.val hcell
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
    have hnpos : 0 < (r + 1 : ℝ) := by positivity
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    have heq :
        1 + s.1 = (t : ℝ) + (k : ℝ) * (r + 1) := by
      field_simp [hnpos.ne'] at hk
      nlinarith [Real.pi_pos]
    have hkUpper : (k : ℝ) ≤ 1 := by
      nlinarith [s.2.2, t.property.1, hnpos]
    have hkLower : (0 : ℝ) ≤ k := by
      nlinarith [s.2.1, t.property.2, hnpos]
    have hkUpperInt : k ≤ 1 := by exact_mod_cast hkUpper
    have hkLowerInt : (0 : ℤ) ≤ k := by exact_mod_cast hkLower
    have hkCases : k = 0 ∨ k = 1 := by omega
    rcases hkCases with rfl | rfl
    · left
      norm_num at heq
      nlinarith [s.2.1, t.property.2]
    · right
      norm_num at heq
      exact_mod_cast (by nlinarith [s.2.2, t.property.1] :
        s.1 = (r : ℝ))
  · intro hs
    rcases hs with hs | hs
    · have hs0 : s = ⟨0, by constructor <;> positivity⟩ :=
        Subtype.ext hs
      subst s
      rw [firstOldArcLocal_apply]
      norm_num
      change
        (firstSideCellHomeomorph r hr
          (PolygonCell.ofCircle (r + 1)
            (Circle.exp (2 * Real.pi / (r + 1))))).1.re = 1
      have hcell :
          PolygonCell.ofCircle (r + 1)
              (Circle.exp (2 * Real.pi / (r + 1))) =
            PolygonCell.side (0 : Fin (r + 1)) 1 := by
        change
          PolygonCell.ofCircle (r + 1)
              (Circle.exp (2 * Real.pi / (r + 1))) =
            PolygonCell.ofCircle (r + 1)
              (Circle.exp
                (PolygonCell.sideAngle (0 : Fin (r + 1)) 1))
        apply congrArg (PolygonCell.ofCircle (r + 1))
        apply congrArg Circle.exp
        unfold PolygonCell.sideAngle
        norm_num
      rw [hcell]
      exact firstSideCellHomeomorph_side_re r hr 1
    · have hsr : s = ⟨r, by simp⟩ := Subtype.ext hs
      subst s
      rw [firstOldArcLocal_apply]
      change
        (firstSideCellHomeomorph r hr
          (PolygonCell.ofCircle (r + 1)
            (Circle.exp
              (2 * Real.pi * (1 + (r : ℝ)) / (r + 1))))).1.re = 1
      have hcell :
          PolygonCell.ofCircle (r + 1)
              (Circle.exp
                (2 * Real.pi * (1 + (r : ℝ)) / (r + 1))) =
            PolygonCell.side (0 : Fin (r + 1)) 0 := by
        apply PolygonCell.ext
        change
          (Circle.exp
              (2 * Real.pi * (1 + (r : ℝ)) / (r + 1)) : ℂ) =
            (Circle.exp (PolygonCell.sideAngle
              (0 : Fin (r + 1)) 0) : ℂ)
        apply congrArg (fun z : Circle ↦ (z : ℂ))
        apply Circle.exp_eq_exp.mpr
        refine ⟨1, ?_⟩
        simp [PolygonCell.sideAngle]
        field_simp [hr.ne']
        ring
      rw [hcell]
      exact firstSideCellHomeomorph_side_re r hr 0

theorem firstOldArcLocal_zero_im
    (r : ℕ) (hr : 0 < r) :
    (firstOldArcLocal r hr ⟨0, by constructor <;> positivity⟩).1.im = -1 := by
  rw [firstOldArcLocal_apply]
  norm_num
  have hcell :
      PolygonCell.ofCircle (r + 1)
          (Circle.exp (2 * Real.pi / (r + 1))) =
        PolygonCell.side (0 : Fin (r + 1)) 1 := by
    change
      PolygonCell.ofCircle (r + 1)
          (Circle.exp (2 * Real.pi / (r + 1))) =
        PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (PolygonCell.sideAngle (0 : Fin (r + 1)) 1))
    apply congrArg (PolygonCell.ofCircle (r + 1))
    apply congrArg Circle.exp
    unfold PolygonCell.sideAngle
    norm_num
  rw [hcell, firstSideCellHomeomorph_side]
  have h :=
    finalSide_eq_firstSide_symm r r hr hr (0 : unitInterval)
  have him := congrArg (fun z : boundary ↦ z.1.im) h
  calc
    (firstSideBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1)) 1))).1.im =
        (finalSideBoundaryHomeomorph r hr
          (Circle.exp
            (PolygonCell.sideAngle (Fin.last r) 0))).1.im := by
          simpa using him.symm
    _ = -1 := finalSideBoundaryHomeomorph_zero_im r hr

theorem firstOldArcLocal_last_im
    (r : ℕ) (hr : 0 < r) :
    (firstOldArcLocal r hr ⟨r, by simp⟩).1.im = 1 := by
  rw [firstOldArcLocal_apply]
  change
    (firstSideCellHomeomorph r hr
      (PolygonCell.ofCircle (r + 1)
        (Circle.exp
          (2 * Real.pi * (1 + (r : ℝ)) / (r + 1))))).1.im = 1
  have hcell :
      PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (2 * Real.pi * (1 + (r : ℝ)) / (r + 1))) =
        PolygonCell.side (0 : Fin (r + 1)) 0 := by
    apply PolygonCell.ext
    change
      (Circle.exp
          (2 * Real.pi * (1 + (r : ℝ)) / (r + 1)) : ℂ) =
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1)) 0) : ℂ)
    apply congrArg (fun z : Circle ↦ (z : ℂ))
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, ?_⟩
    simp [PolygonCell.sideAngle]
    field_simp [hr.ne']
    ring
  rw [hcell, firstSideCellHomeomorph_side]
  have h :=
    finalSide_eq_firstSide_symm r r hr hr (1 : unitInterval)
  have him := congrArg (fun z : boundary ↦ z.1.im) h
  calc
    (firstSideBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1)) 0))).1.im =
        (finalSideBoundaryHomeomorph r hr
          (Circle.exp
            (PolygonCell.sideAngle (Fin.last r) 1))).1.im := by
          simpa using him.symm
    _ = 1 := finalSideBoundaryHomeomorph_one_im r hr

theorem firstOldArcLocal_abs_im_eq_one_of_re_eq_one
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r)
    (hs : (firstOldArcLocal r hr s).1.re = 1) :
    |(firstOldArcLocal r hr s).1.im| = 1 := by
  rcases (firstOldArcLocal_re_eq_one_iff_endpoint r hr s).mp hs with h | h
  · have hs0 : s = ⟨0, by constructor <;> positivity⟩ := Subtype.ext h
    subst s
    rw [firstOldArcLocal_zero_im]
    norm_num
  · have hsr : s = ⟨r, by simp⟩ := Subtype.ext h
    subst s
    rw [firstOldArcLocal_last_im]
    norm_num

theorem finalOldArcLocal_mem_boundary
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    (finalOldArcLocal l hl s).1 ∈ boundary := by
  rw [finalOldArcLocal_apply]
  change
    maxAbs
      (cellSquareHomeomorph (finalSideBoundaryHomeomorph l hl)
        (PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * s.1 / (l + 1))))).1 = 1
  rw [cellSquareHomeomorph_ofCircle]
  exact
    (finalSideBoundaryHomeomorph l hl
      (Circle.exp (2 * Real.pi * s.1 / (l + 1)))).property

theorem firstOldArcLocal_mem_boundary
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    (firstOldArcLocal r hr s).1 ∈ boundary := by
  rw [firstOldArcLocal_apply]
  change
    maxAbs
      (cellSquareHomeomorph (firstSideBoundaryHomeomorph r hr)
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (2 * Real.pi * (1 + s.1) / (r + 1))))).1 = 1
  rw [cellSquareHomeomorph_ofCircle]
  exact
    (firstSideBoundaryHomeomorph r hr
      (Circle.exp
        (2 * Real.pi * (1 + s.1) / (r + 1)))).property

theorem leftPlacement_mem_boundary_of_mem_boundary
    (z : square) (hz : z.1 ∈ boundary)
    (hseam : z.1.re = 1 → |z.1.im| = 1) :
    (leftPlacement z).1 ∈ boundary := by
  change maxAbs (leftPlacement z).1 = 1
  apply le_antisymm (leftPlacement z).2
  change 1 ≤ max |(z.1.re - 1) / 2| |z.1.im|
  change max |z.1.re| |z.1.im| = 1 at hz
  rcases le_total |z.1.re| |z.1.im| with hle | hle
  · have him : |z.1.im| = 1 := by
      rw [max_eq_right hle] at hz
      exact hz
    rw [him]
    exact le_max_right _ _
  · have hreAbs : |z.1.re| = 1 := by
      rw [max_eq_left hle] at hz
      exact hz
    rcases eq_or_eq_neg_of_abs_eq (by simpa using hreAbs) with hre | hre
    · have him := hseam hre
      rw [him]
      exact le_max_right _ _
    · have hre' : z.1.re = -1 := by simpa using hre
      rw [hre']
      norm_num

theorem rightPlacement_mem_boundary_of_mem_boundary
    (z : square) (hz : z.1 ∈ boundary)
    (hseam : z.1.re = 1 → |z.1.im| = 1) :
    (rightPlacement z).1 ∈ boundary := by
  change maxAbs (rightPlacement z).1 = 1
  apply le_antisymm (rightPlacement z).2
  change 1 ≤ max |(1 - z.1.re) / 2| |z.1.im|
  change max |z.1.re| |z.1.im| = 1 at hz
  rcases le_total |z.1.re| |z.1.im| with hle | hle
  · have him : |z.1.im| = 1 := by
      rw [max_eq_right hle] at hz
      exact hz
    rw [him]
    exact le_max_right _ _
  · have hreAbs : |z.1.re| = 1 := by
      rw [max_eq_left hle] at hz
      exact hz
    rcases eq_or_eq_neg_of_abs_eq (by simpa using hreAbs) with hre | hre
    · have him := hseam hre
      rw [him]
      exact le_max_right _ _
    · have hre' : z.1.re = -1 := by simpa using hre
      rw [hre']
      norm_num

/-- The selected child's old boundary, placed on the outer square frontier. -/
noncomputable def finalOldArc
    (l : ℕ) (hl : 0 < l) : C(Set.Icc (0 : ℝ) l, boundary) where
  toFun s :=
    ⟨(leftPlacement (finalOldArcLocal l hl s)).1,
      leftPlacement_mem_boundary_of_mem_boundary
        (finalOldArcLocal l hl s)
        (finalOldArcLocal_mem_boundary l hl s)
        (finalOldArcLocal_abs_im_eq_one_of_re_eq_one l hl s)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun s : Set.Icc (0 : ℝ) l ↦
      (leftPlacement (finalOldArcLocal l hl s)).1)
    exact continuous_subtype_val.comp
      (leftPlacement.continuous.comp
        (finalOldArcLocal l hl).continuous)

/-- The right child's old boundary, reflected and placed on the outer square frontier. -/
noncomputable def firstOldArc
    (r : ℕ) (hr : 0 < r) : C(Set.Icc (0 : ℝ) r, boundary) where
  toFun s :=
    ⟨(rightPlacement (firstOldArcLocal r hr s)).1,
      rightPlacement_mem_boundary_of_mem_boundary
        (firstOldArcLocal r hr s)
        (firstOldArcLocal_mem_boundary r hr s)
        (firstOldArcLocal_abs_im_eq_one_of_re_eq_one r hr s)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun s : Set.Icc (0 : ℝ) r ↦
      (rightPlacement (firstOldArcLocal r hr s)).1)
    exact continuous_subtype_val.comp
      (rightPlacement.continuous.comp
        (firstOldArcLocal r hr).continuous)

@[simp]
theorem finalOldArc_val
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    (finalOldArc l hl s).1 =
      (leftPlacement (finalOldArcLocal l hl s)).1 :=
  rfl

theorem firstOldArc_val
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    (firstOldArc r hr s).1 =
      (rightPlacement (firstOldArcLocal r hr s)).1 :=
  rfl

theorem finalOldArc_zero_re (l : ℕ) (hl : 0 < l) :
    (finalOldArc l hl ⟨0, by constructor <;> positivity⟩).1.re = 0 := by
  rw [finalOldArc_val, leftPlacement_re]
  rw [(finalOldArcLocal_re_eq_one_iff_endpoint l hl _).2 (Or.inl rfl)]
  norm_num

theorem finalOldArc_zero_im (l : ℕ) (hl : 0 < l) :
    (finalOldArc l hl ⟨0, by constructor <;> positivity⟩).1.im = 1 := by
  exact finalOldArcLocal_zero_im l hl

theorem finalOldArc_last_re (l : ℕ) (hl : 0 < l) :
    (finalOldArc l hl ⟨l, by simp⟩).1.re = 0 := by
  rw [finalOldArc_val, leftPlacement_re]
  rw [(finalOldArcLocal_re_eq_one_iff_endpoint l hl _).2 (Or.inr rfl)]
  norm_num

theorem finalOldArc_last_im (l : ℕ) (hl : 0 < l) :
    (finalOldArc l hl ⟨l, by simp⟩).1.im = -1 := by
  exact finalOldArcLocal_last_im l hl

theorem firstOldArc_zero_re (r : ℕ) (hr : 0 < r) :
    (firstOldArc r hr ⟨0, by constructor <;> positivity⟩).1.re = 0 := by
  rw [firstOldArc_val, rightPlacement_re]
  rw [(firstOldArcLocal_re_eq_one_iff_endpoint r hr _).2 (Or.inl rfl)]
  norm_num

theorem firstOldArc_zero_im (r : ℕ) (hr : 0 < r) :
    (firstOldArc r hr ⟨0, by constructor <;> positivity⟩).1.im = -1 := by
  exact firstOldArcLocal_zero_im r hr

theorem firstOldArc_last_re (r : ℕ) (hr : 0 < r) :
    (firstOldArc r hr ⟨r, by simp⟩).1.re = 0 := by
  rw [firstOldArc_val, rightPlacement_re]
  rw [(firstOldArcLocal_re_eq_one_iff_endpoint r hr _).2 (Or.inr rfl)]
  norm_num

@[simp]
theorem firstOldArc_last_im (r : ℕ) (hr : 0 < r) :
    (firstOldArc r hr ⟨r, by simp⟩).1.im = 1 := by
  exact firstOldArcLocal_last_im r hr

theorem finalOldArc_re_nonpos
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    (finalOldArc l hl s).1.re ≤ 0 :=
  leftPlacement_re_nonpos (finalOldArcLocal l hl s)

theorem firstOldArc_re_nonneg
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    0 ≤ (firstOldArc r hr s).1.re :=
  rightPlacement_re_nonneg (firstOldArcLocal r hr s)

theorem finalOldArc_re_eq_zero_iff_endpoint
    (l : ℕ) (hl : 0 < l) (s : Set.Icc (0 : ℝ) l) :
    (finalOldArc l hl s).1.re = 0 ↔
      s.1 = 0 ∨ s.1 = l := by
  rw [finalOldArc_val, leftPlacement_re]
  constructor
  · intro h
    apply (finalOldArcLocal_re_eq_one_iff_endpoint l hl s).mp
    linarith
  · intro h
    rw [(finalOldArcLocal_re_eq_one_iff_endpoint l hl s).2 h]
    norm_num

theorem firstOldArc_re_eq_zero_iff_endpoint
    (r : ℕ) (hr : 0 < r) (s : Set.Icc (0 : ℝ) r) :
    (firstOldArc r hr s).1.re = 0 ↔
      s.1 = 0 ∨ s.1 = r := by
  rw [firstOldArc_val, rightPlacement_re]
  constructor
  · intro h
    apply (firstOldArcLocal_re_eq_one_iff_endpoint r hr s).mp
    linarith
  · intro h
    rw [(firstOldArcLocal_re_eq_one_iff_endpoint r hr s).2 h]
    norm_num

theorem finalOldArc_injective
    (l : ℕ) (hl : 0 < l) :
    Function.Injective (finalOldArc l hl) := by
  intro s t hst
  have hplacement :
      leftPlacement (finalOldArcLocal l hl s) =
        leftPlacement (finalOldArcLocal l hl t) := by
    apply Subtype.ext
    exact congrArg (fun q : boundary ↦ q.1) hst
  have hlocal :
      finalOldArcLocal l hl s = finalOldArcLocal l hl t :=
    leftPlacement_injective hplacement
  have hcell :
      PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * s.1 / (l + 1))) =
        PolygonCell.ofCircle (l + 1)
          (Circle.exp (2 * Real.pi * t.1 / (l + 1))) := by
    apply (finalSideCellHomeomorph l hl).injective
    simpa only [finalOldArcLocal_apply] using hlocal
  have hexp :
      Circle.exp (2 * Real.pi * s.1 / (l + 1)) =
        Circle.exp (2 * Real.pi * t.1 / (l + 1)) := by
    apply Circle.ext
    exact congrArg PolygonCell.val hcell
  let b : ℝ := 2 * Real.pi * l / (l + 1)
  have hb : b < 2 * Real.pi := by
    dsimp [b]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < l + 1)]
    nlinarith [Real.pi_pos]
  have hsMem :
      2 * Real.pi * s.1 / (l + 1) ∈ Set.Icc (0 : ℝ) b := by
    dsimp [b]
    constructor
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) s.2.1)
        (by positivity)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [s.2.2, Real.pi_pos]
  have htMem :
      2 * Real.pi * t.1 / (l + 1) ∈ Set.Icc (0 : ℝ) b := by
    dsimp [b]
    constructor
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) t.2.1)
        (by positivity)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [t.2.2, Real.pi_pos]
  have hangle :=
    Circle.exp_injOn_Icc (a := 0) (b := b) (by simpa using hb)
      hsMem htMem hexp
  apply Subtype.ext
  have hfactor : 0 < 2 * Real.pi / (l + 1 : ℝ) := by positivity
  have hsform :
      2 * Real.pi * s.1 / (l + 1) =
        (2 * Real.pi / (l + 1)) * s.1 := by ring
  have htform :
      2 * Real.pi * t.1 / (l + 1) =
        (2 * Real.pi / (l + 1)) * t.1 := by ring
  rw [hsform, htform] at hangle
  exact (mul_left_cancel₀ hfactor.ne' hangle)

theorem firstOldArc_injective
    (r : ℕ) (hr : 0 < r) :
    Function.Injective (firstOldArc r hr) := by
  intro s t hst
  have hplacement :
      rightPlacement (firstOldArcLocal r hr s) =
        rightPlacement (firstOldArcLocal r hr t) := by
    apply Subtype.ext
    exact congrArg (fun q : boundary ↦ q.1) hst
  have hlocal :
      firstOldArcLocal r hr s = firstOldArcLocal r hr t :=
    rightPlacement_injective hplacement
  have hcell :
      PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (2 * Real.pi * (1 + s.1) / (r + 1))) =
        PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (2 * Real.pi * (1 + t.1) / (r + 1))) := by
    apply (firstSideCellHomeomorph r hr).injective
    simpa only [firstOldArcLocal_apply] using hlocal
  have hexp :
      Circle.exp
          (2 * Real.pi * (1 + s.1) / (r + 1)) =
        Circle.exp
          (2 * Real.pi * (1 + t.1) / (r + 1)) := by
    apply Circle.ext
    exact congrArg PolygonCell.val hcell
  let a : ℝ := 2 * Real.pi / (r + 1)
  have hab : 2 * Real.pi - a < 2 * Real.pi := by
    dsimp [a]
    have : 0 < 2 * Real.pi / (r + 1 : ℝ) := by positivity
    linarith
  have hsMem :
      2 * Real.pi * (1 + s.1) / (r + 1) ∈
        Set.Icc a (2 * Real.pi) := by
    dsimp [a]
    constructor
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [s.2.1, Real.pi_pos]
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < r + 1)]
      nlinarith [s.2.2, Real.pi_pos]
  have htMem :
      2 * Real.pi * (1 + t.1) / (r + 1) ∈
        Set.Icc a (2 * Real.pi) := by
    dsimp [a]
    constructor
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [t.2.1, Real.pi_pos]
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < r + 1)]
      nlinarith [t.2.2, Real.pi_pos]
  have hangle :=
    Circle.exp_injOn_Icc (a := a) (b := 2 * Real.pi) hab
      hsMem htMem hexp
  apply Subtype.ext
  have hfactor : 0 < 2 * Real.pi / (r + 1 : ℝ) := by positivity
  have hsform :
      2 * Real.pi * (1 + s.1) / (r + 1) =
        (2 * Real.pi / (r + 1)) * (1 + s.1) := by ring
  have htform :
      2 * Real.pi * (1 + t.1) / (r + 1) =
        (2 * Real.pi / (r + 1)) * (1 + t.1) := by ring
  rw [hsform, htform] at hangle
  have hsum :
      (1 : ℝ) + s.1 = 1 + t.1 :=
    mul_left_cancel₀ hfactor.ne' hangle
  linarith

/-! ## The outer boundary assembled from the two old-boundary arcs -/

/-- A continuous coordinate, from `0` to `3`, along the left half of the square boundary.
It starts at the midpoint of the top edge, passes the two left corners, and ends at the
midpoint of the bottom edge. -/
noncomputable def leftPerimeter (z : boundary) : ℝ :=
  -z.1.re + (1 - z.1.im) / 2 + (1 - z.1.im) * (1 + z.1.re)

theorem continuous_leftPerimeter : Continuous leftPerimeter := by
  unfold leftPerimeter
  fun_prop

theorem boundary_left_cases (z : boundary) (hz : z.1.re ≤ 0) :
    z.1.re = -1 ∨ z.1.im = 1 ∨ z.1.im = -1 := by
  have hzBoundary := z.property
  change max |z.1.re| |z.1.im| = 1 at hzBoundary
  rcases (max_eq_iff.mp hzBoundary) with hre | him
  · rcases eq_or_eq_neg_of_abs_eq hre.1 with hrePos | hreNeg
    · exfalso
      linarith
    · exact Or.inl hreNeg
  · rcases eq_or_eq_neg_of_abs_eq him.1 with himPos | himNeg
    · exact Or.inr (Or.inl himPos)
    · exact Or.inr (Or.inr himNeg)

theorem boundary_right_cases (z : boundary) (hz : 0 ≤ z.1.re) :
    z.1.re = 1 ∨ z.1.im = 1 ∨ z.1.im = -1 := by
  have hzBoundary := z.property
  change max |z.1.re| |z.1.im| = 1 at hzBoundary
  rcases (max_eq_iff.mp hzBoundary) with hre | him
  · rcases eq_or_eq_neg_of_abs_eq hre.1 with hrePos | hreNeg
    · exact Or.inl hrePos
    · exfalso
      linarith
  · rcases eq_or_eq_neg_of_abs_eq him.1 with himPos | himNeg
    · exact Or.inr (Or.inl himPos)
    · exact Or.inr (Or.inr himNeg)

theorem leftPerimeter_mem_Icc
    (z : boundary) (hz : z.1.re ≤ 0) :
    leftPerimeter z ∈ Set.Icc (0 : ℝ) 3 := by
  have hre := abs_re_le_maxAbs z.1
  have him := abs_im_le_maxAbs z.1
  rw [z.property] at hre him
  rw [abs_le] at hre him
  rcases boundary_left_cases z hz with hzLeft | hzTop | hzBottom
  · simp only [leftPerimeter, hzLeft]
    constructor <;> linarith
  · simp only [leftPerimeter, hzTop]
    constructor <;> linarith
  · simp only [leftPerimeter, hzBottom]
    constructor <;> linarith

theorem leftPerimeter_injective
    {z w : boundary} (hz : z.1.re ≤ 0) (hw : w.1.re ≤ 0)
    (hzw : leftPerimeter z = leftPerimeter w) :
    z = w := by
  have hzRe := abs_re_le_maxAbs z.1
  have hzIm := abs_im_le_maxAbs z.1
  have hwRe := abs_re_le_maxAbs w.1
  have hwIm := abs_im_le_maxAbs w.1
  rw [z.property] at hzRe hzIm
  rw [w.property] at hwRe hwIm
  rw [abs_le] at hzRe hzIm hwRe hwIm
  rcases boundary_left_cases z hz with hzLeft | hzTop | hzBottom
  · rcases boundary_left_cases w hw with hwLeft | hwTop | hwBottom
    · apply Subtype.ext
      apply Complex.ext
      · linarith
      · simp only [leftPerimeter, hzLeft, hwLeft] at hzw
        linarith
    · simp only [leftPerimeter, hzLeft, hwTop] at hzw
      apply Subtype.ext
      apply Complex.ext
      · linarith
      · linarith
    · simp only [leftPerimeter, hzLeft, hwBottom] at hzw
      apply Subtype.ext
      apply Complex.ext
      · linarith
      · linarith
  · rcases boundary_left_cases w hw with hwLeft | hwTop | hwBottom
    · simp only [leftPerimeter, hzTop, hwLeft] at hzw
      apply Subtype.ext
      apply Complex.ext
      · linarith
      · linarith
    · apply Subtype.ext
      apply Complex.ext
      · simp only [leftPerimeter, hzTop, hwTop] at hzw
        linarith
      · linarith
    · exfalso
      simp only [leftPerimeter, hzTop, hwBottom] at hzw
      linarith
  · rcases boundary_left_cases w hw with hwLeft | hwTop | hwBottom
    · simp only [leftPerimeter, hzBottom, hwLeft] at hzw
      apply Subtype.ext
      apply Complex.ext
      · linarith
      · linarith
    · exfalso
      simp only [leftPerimeter, hzBottom, hwTop] at hzw
      linarith
    · apply Subtype.ext
      apply Complex.ext
      · simp only [leftPerimeter, hzBottom, hwBottom] at hzw
        linarith
      · linarith

/-- The analogous coordinate on the right half, oriented from bottom to top. -/
noncomputable def rightPerimeter (z : boundary) : ℝ :=
  leftPerimeter
    ⟨-z.1, by
      change maxAbs (-z.1) = 1
      have hzBoundary := z.property
      change maxAbs z.1 = 1 at hzBoundary
      simpa only [maxAbs, Complex.neg_re, Complex.neg_im, abs_neg] using
        hzBoundary⟩

theorem continuous_rightPerimeter : Continuous rightPerimeter := by
  unfold rightPerimeter
  exact continuous_leftPerimeter.comp
    (continuous_induced_rng.2 continuous_subtype_val.neg)

theorem rightPerimeter_mem_Icc
    (z : boundary) (hz : 0 ≤ z.1.re) :
    rightPerimeter z ∈ Set.Icc (0 : ℝ) 3 := by
  apply leftPerimeter_mem_Icc
  change -z.1.re ≤ 0
  linarith

theorem rightPerimeter_injective
    {z w : boundary} (hz : 0 ≤ z.1.re) (hw : 0 ≤ w.1.re)
    (hzw : rightPerimeter z = rightPerimeter w) :
    z = w := by
  have hneg :
      (⟨-z.1, by
          change maxAbs (-z.1) = 1
          have hzBoundary := z.property
          change maxAbs z.1 = 1 at hzBoundary
          simpa only [maxAbs, Complex.neg_re, Complex.neg_im, abs_neg] using
            hzBoundary⟩ : boundary) =
        ⟨-w.1, by
          change maxAbs (-w.1) = 1
          have hwBoundary := w.property
          change maxAbs w.1 = 1 at hwBoundary
          simpa only [maxAbs, Complex.neg_re, Complex.neg_im, abs_neg] using
            hwBoundary⟩ := by
    apply leftPerimeter_injective
    · change -z.1.re ≤ 0
      linarith
    · change -w.1.re ≤ 0
      linarith
    · exact hzw
  apply Subtype.ext
  have := congrArg (fun q : boundary ↦ q.1) hneg
  dsimp at this
  exact neg_injective this

@[simp]
theorem leftPerimeter_finalOldArc_zero (l : ℕ) (hl : 0 < l) :
    leftPerimeter
        (finalOldArc l hl ⟨0, by constructor <;> positivity⟩) =
      0 := by
  unfold leftPerimeter
  rw [finalOldArc_zero_re, finalOldArc_zero_im]
  norm_num

@[simp]
theorem leftPerimeter_finalOldArc_last (l : ℕ) (hl : 0 < l) :
    leftPerimeter (finalOldArc l hl ⟨l, by simp⟩) = 3 := by
  unfold leftPerimeter
  rw [finalOldArc_last_re, finalOldArc_last_im]
  norm_num

@[simp]
theorem rightPerimeter_firstOldArc_zero (r : ℕ) (hr : 0 < r) :
    rightPerimeter
        (firstOldArc r hr ⟨0, by constructor <;> positivity⟩) =
      0 := by
  unfold rightPerimeter leftPerimeter
  simp only [Complex.neg_re, Complex.neg_im]
  rw [firstOldArc_zero_re, firstOldArc_zero_im]
  norm_num

@[simp]
theorem rightPerimeter_firstOldArc_last (r : ℕ) (hr : 0 < r) :
    rightPerimeter (firstOldArc r hr ⟨r, by simp⟩) = 3 := by
  unfold rightPerimeter leftPerimeter
  simp only [Complex.neg_re, Complex.neg_im]
  rw [firstOldArc_last_re, firstOldArc_last_im]
  norm_num

theorem exists_finalOldArc_of_re_nonpos
    (l : ℕ) (hl : 0 < l) (z : boundary) (hz : z.1.re ≤ 0) :
    ∃ s : Set.Icc (0 : ℝ) l, finalOldArc l hl s = z := by
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) l) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let perimeter : Set.Icc (0 : ℝ) l → ℝ :=
    fun s ↦ leftPerimeter (finalOldArc l hl s)
  have hcontinuous : Continuous perimeter :=
    continuous_leftPerimeter.comp (finalOldArc l hl).continuous
  have hzRange : leftPerimeter z ∈ Set.range perimeter := by
    apply (intermediate_value_univ
      (⟨0, by constructor <;> positivity⟩ : Set.Icc (0 : ℝ) l)
      ⟨l, by simp⟩ hcontinuous)
    simpa only [perimeter, leftPerimeter_finalOldArc_zero,
      leftPerimeter_finalOldArc_last] using leftPerimeter_mem_Icc z hz
  rcases hzRange with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  apply leftPerimeter_injective (finalOldArc_re_nonpos l hl s) hz
  exact hs

theorem exists_firstOldArc_of_re_nonneg
    (r : ℕ) (hr : 0 < r) (z : boundary) (hz : 0 ≤ z.1.re) :
    ∃ s : Set.Icc (0 : ℝ) r, firstOldArc r hr s = z := by
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) r) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let perimeter : Set.Icc (0 : ℝ) r → ℝ :=
    fun s ↦ rightPerimeter (firstOldArc r hr s)
  have hcontinuous : Continuous perimeter :=
    continuous_rightPerimeter.comp (firstOldArc r hr).continuous
  have hzRange : rightPerimeter z ∈ Set.range perimeter := by
    apply (intermediate_value_univ
      (⟨0, by constructor <;> positivity⟩ : Set.Icc (0 : ℝ) r)
      ⟨r, by simp⟩ hcontinuous)
    simpa only [perimeter, rightPerimeter_firstOldArc_zero,
      rightPerimeter_firstOldArc_last] using rightPerimeter_mem_Icc z hz
  rcases hzRange with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  apply rightPerimeter_injective (firstOldArc_re_nonneg r hr s) hz
  exact hs

/-- Clip a parameter for the combined outer boundary to the left child's old arc. -/
def finalArcParameter (l r : ℕ) :
    Set.Icc (0 : ℝ) (l + r) → Set.Icc (0 : ℝ) l :=
  fun x ↦
    ⟨min x.1 l,
      ⟨le_min x.2.1 (Nat.cast_nonneg l), min_le_right _ _⟩⟩

theorem continuous_finalArcParameter (l r : ℕ) :
    Continuous (finalArcParameter l r) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val.min continuous_const

/-- Clip and translate a combined parameter to the right child's old arc. -/
def firstArcParameter (l r : ℕ) :
    Set.Icc (0 : ℝ) (l + r) → Set.Icc (0 : ℝ) r :=
  fun x ↦
    ⟨max (x.1 - l) 0,
      ⟨le_max_right _ _,
        max_le
          (by
            have hx := x.2.2
            linarith)
          (Nat.cast_nonneg r)⟩⟩

theorem continuous_firstArcParameter (l r : ℕ) :
    Continuous (firstArcParameter l r) := by
  apply continuous_induced_rng.2
  exact
    (continuous_subtype_val.sub continuous_const).max continuous_const

theorem finalOldArc_last_eq_firstOldArc_zero
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    finalOldArc l hl ⟨l, by simp⟩ =
      firstOldArc r hr ⟨0, by constructor <;> positivity⟩ := by
  apply Subtype.ext
  apply Complex.ext
  · exact (finalOldArc_last_re l hl).trans
      (firstOldArc_zero_re r hr).symm
  · exact (finalOldArc_last_im l hl).trans
      (firstOldArc_zero_im r hr).symm

/-- The full outer boundary path: the selected child's old sides followed by the right
child's old sides.  Its two endpoints both map to the top midpoint. -/
noncomputable def outerArc
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    C(Set.Icc (0 : ℝ) (l + r), boundary) where
  toFun x :=
    if x.1 ≤ l then
      finalOldArc l hl (finalArcParameter l r x)
    else
      firstOldArc r hr (firstArcParameter l r x)
  continuous_toFun := by
    apply Continuous.if_le
      ((finalOldArc l hl).continuous.comp
        (continuous_finalArcParameter l r))
      ((firstOldArc r hr).continuous.comp
        (continuous_firstArcParameter l r))
      continuous_subtype_val continuous_const
    intro x hx
    have hxValue : x.1 = l := hx
    have hfinal :
        finalArcParameter l r x =
          (⟨l, by simp⟩ : Set.Icc (0 : ℝ) l) := by
      apply Subtype.ext
      simp [finalArcParameter, hxValue]
    have hfirst :
        firstArcParameter l r x =
          (⟨0, by constructor <;> positivity⟩ :
            Set.Icc (0 : ℝ) r) := by
      apply Subtype.ext
      simp [firstArcParameter, hxValue]
    simpa only [Function.comp_apply, hfinal, hfirst] using
      finalOldArc_last_eq_firstOldArc_zero l r hl hr

theorem outerArc_apply_of_le
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : Set.Icc (0 : ℝ) (l + r)) (hx : x.1 ≤ l) :
    outerArc l r hl hr x =
      finalOldArc l hl
        ⟨x.1, ⟨x.2.1, hx⟩⟩ := by
  change
    (if x.1 ≤ l then
      finalOldArc l hl (finalArcParameter l r x)
    else
      firstOldArc r hr (firstArcParameter l r x)) = _
  rw [if_pos hx]
  apply congrArg (finalOldArc l hl)
  apply Subtype.ext
  simp [finalArcParameter, min_eq_left hx]

theorem outerArc_apply_of_not_le
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : Set.Icc (0 : ℝ) (l + r)) (hx : ¬x.1 ≤ l) :
    outerArc l r hl hr x =
      firstOldArc r hr
        ⟨x.1 - l,
          ⟨by linarith,
            by
              have hxUpper := x.2.2
              linarith⟩⟩ := by
  change
    (if x.1 ≤ l then
      finalOldArc l hl (finalArcParameter l r x)
    else
      firstOldArc r hr (firstArcParameter l r x)) = _
  rw [if_neg hx]
  apply congrArg (firstOldArc r hr)
  apply Subtype.ext
  simp [firstArcParameter, max_eq_left (by linarith : 0 ≤ x.1 - l)]

@[simp]
theorem outerArc_zero
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    outerArc l r hl hr
        ⟨0, by constructor <;> positivity⟩ =
      finalOldArc l hl
        ⟨0, by constructor <;> positivity⟩ := by
  apply outerArc_apply_of_le
  positivity

@[simp]
theorem outerArc_split
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    outerArc l r hl hr
        ⟨l, by
          constructor
          · exact Nat.cast_nonneg l
          · have _hrNonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
            linarith⟩ =
      finalOldArc l hl ⟨l, by simp⟩ := by
  apply outerArc_apply_of_le
  rfl

@[simp]
theorem outerArc_last
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    outerArc l r hl hr
        ⟨l + r, by
          constructor
          · positivity
          · rfl⟩ =
      firstOldArc r hr ⟨r, by simp⟩ := by
  rw [outerArc_apply_of_not_le]
  · congr 1
    apply Subtype.ext
    push_cast
    ring
  · have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
    push_cast
    linarith

theorem outerArc_endpoints
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    outerArc l r hl hr
        ⟨0, by constructor <;> positivity⟩ =
      outerArc l r hl hr
        ⟨l + r, by
          constructor
          · exact add_nonneg (Nat.cast_nonneg l) (Nat.cast_nonneg r)
          · rfl⟩ := by
  rw [outerArc_zero, outerArc_last]
  apply Subtype.ext
  apply Complex.ext
  · exact (finalOldArc_zero_re l hl).trans
      (firstOldArc_last_re r hr).symm
  · exact (finalOldArc_zero_im l hl).trans
      (firstOldArc_last_im r hr).symm

theorem outerArc_surjective
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    Function.Surjective (outerArc l r hl hr) := by
  intro z
  rcases le_total z.1.re 0 with hzLeft | hzRight
  · obtain ⟨s, hs⟩ := exists_finalOldArc_of_re_nonpos l hl z hzLeft
    let x : Set.Icc (0 : ℝ) (l + r) :=
      ⟨s.1, ⟨s.2.1, s.2.2.trans (by
        have _hrNonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        linarith)⟩⟩
    refine ⟨x, ?_⟩
    rw [outerArc_apply_of_le l r hl hr x s.2.2]
    simpa only [x] using hs
  · obtain ⟨s, hs⟩ := exists_firstOldArc_of_re_nonneg r hr z hzRight
    let x : Set.Icc (0 : ℝ) (l + r) :=
      ⟨l + s.1, by
        constructor
        · exact add_nonneg (Nat.cast_nonneg l) s.2.1
        · linarith [s.2.2]⟩
    refine ⟨x, ?_⟩
    by_cases hsZero : s.1 = 0
    · have hxValue : x.1 = l := by
        dsimp [x]
        linarith
      have hx :
          x = (⟨l, by
            constructor
            · exact Nat.cast_nonneg l
            · have _hrNonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
              linarith⟩ :
            Set.Icc (0 : ℝ) (l + r)) :=
        Subtype.ext hxValue
      have hsSubtype :
          s = (⟨0, by constructor <;> positivity⟩ :
            Set.Icc (0 : ℝ) r) :=
        Subtype.ext hsZero
      rw [hx, outerArc_split,
        finalOldArc_last_eq_firstOldArc_zero l r hl hr]
      rw [← hsSubtype]
      exact hs
    · have hxNot : ¬x.1 ≤ l := by
        dsimp [x]
        have hsPos : 0 < s.1 := lt_of_le_of_ne s.2.1 (Ne.symm hsZero)
        linarith
      rw [outerArc_apply_of_not_le l r hl hr x hxNot]
      simpa only [x, add_sub_cancel_left] using hs

theorem outerArc_cross_endpoints
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x y : Set.Icc (0 : ℝ) (l + r))
    (hx : x.1 ≤ l) (hy : ¬y.1 ≤ l)
    (hxy : outerArc l r hl hr x = outerArc l r hl hr y) :
    x.1 = 0 ∧ y.1 = l + r := by
  let sx : Set.Icc (0 : ℝ) l :=
    ⟨x.1, ⟨x.2.1, hx⟩⟩
  let ty : Set.Icc (0 : ℝ) r :=
    ⟨y.1 - l,
      ⟨by linarith,
        by
          have hyUpper := y.2.2
          linarith⟩⟩
  have harc :
      finalOldArc l hl sx = firstOldArc r hr ty := by
    rw [outerArc_apply_of_le l r hl hr x hx,
      outerArc_apply_of_not_le l r hl hr y hy] at hxy
    simpa only [sx, ty] using hxy
  have hre :=
    congrArg (fun q : boundary ↦ q.1.re) harc
  have hsNonpos := finalOldArc_re_nonpos l hl sx
  have htNonneg := firstOldArc_re_nonneg r hr ty
  have hsZero : (finalOldArc l hl sx).1.re = 0 := by
    apply le_antisymm hsNonpos
    linarith
  have htZero : (firstOldArc r hr ty).1.re = 0 := by
    apply le_antisymm
    · linarith
    · exact htNonneg
  have hsEndpoint :=
    (finalOldArc_re_eq_zero_iff_endpoint l hl sx).mp hsZero
  have htEndpoint :=
    (firstOldArc_re_eq_zero_iff_endpoint r hr ty).mp htZero
  have htNotZero : ty.1 ≠ 0 := by
    intro ht
    apply hy
    dsimp [ty] at ht
    linarith
  have htLast : ty.1 = r :=
    htEndpoint.resolve_left htNotZero
  have hsNotLast : sx.1 ≠ l := by
    intro hsLast
    have hsEq :
        sx = (⟨l, by simp⟩ : Set.Icc (0 : ℝ) l) :=
      Subtype.ext hsLast
    have htEq :
        ty = (⟨r, by simp⟩ : Set.Icc (0 : ℝ) r) :=
      Subtype.ext htLast
    have him := congrArg (fun q : boundary ↦ q.1.im) harc
    rw [hsEq, htEq, finalOldArc_last_im, firstOldArc_last_im] at him
    norm_num at him
  have hsFirst : sx.1 = 0 :=
    hsEndpoint.resolve_right hsNotLast
  constructor
  · exact hsFirst
  · dsimp [ty] at htLast
    linarith

theorem outerArc_eq_imp_endpointIdent
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x y : Set.Icc (0 : ℝ) (l + r))
    (hxy : outerArc l r hl hr x = outerArc l r hl hr y) :
    x = y ∨
      (x.1 = 0 ∧ y.1 = l + r) ∨
      (x.1 = l + r ∧ y.1 = 0) := by
  by_cases hx : x.1 ≤ l
  · by_cases hy : y.1 ≤ l
    · left
      have hxy' := hxy
      rw [outerArc_apply_of_le l r hl hr x hx,
        outerArc_apply_of_le l r hl hr y hy] at hxy'
      have hparameters := finalOldArc_injective l hl hxy'
      apply Subtype.ext
      exact congrArg (fun q : Set.Icc (0 : ℝ) l ↦ q.1) hparameters
    · exact Or.inr (Or.inl
        (outerArc_cross_endpoints l r hl hr x y hx hy hxy))
  · by_cases hy : y.1 ≤ l
    · have hcross :=
        outerArc_cross_endpoints l r hl hr y x hy hx hxy.symm
      exact Or.inr (Or.inr ⟨hcross.2, hcross.1⟩)
    · left
      have hxy' := hxy
      rw [outerArc_apply_of_not_le l r hl hr x hx,
        outerArc_apply_of_not_le l r hl hr y hy] at hxy'
      have hparameters := firstOldArc_injective r hr hxy'
      have hvalues :=
        congrArg (fun q : Set.Icc (0 : ℝ) r ↦ q.1) hparameters
      apply Subtype.ext
      push_cast at hvalues ⊢
      linarith

section OuterBoundary

variable (l r : ℕ) (hl : 0 < l) (hr : 0 < r)

variable [Fact (0 < (l + r : ℝ))]

/-- Remove the syntactic leading zero from the endpoint interval used by `AddCircle`. -/
def outerEndpointParameter :
    C(Set.Icc (0 : ℝ) (0 + (l + r)),
      Set.Icc (0 : ℝ) (l + r)) where
  toFun x :=
    ⟨x.1, by simpa only [zero_add] using x.2⟩
  continuous_toFun :=
    continuous_induced_rng.2 continuous_subtype_val

/-- The outer path with the syntactic endpoint interval used by `AddCircle.EndpointIdent`. -/
noncomputable def outerEndpointArc :
    C(Set.Icc (0 : ℝ) (0 + (l + r)), boundary) :=
  (outerArc l r hl hr).comp (outerEndpointParameter l r)

omit [Fact (0 < (l + r : ℝ))] in
@[simp]
theorem outerEndpointArc_apply
    (x : Set.Icc (0 : ℝ) (0 + (l + r))) :
    outerEndpointArc l r hl hr x =
      outerArc l r hl hr
        ⟨x.1, by simpa only [zero_add] using x.2⟩ :=
  rfl

theorem outerArc_endpointIdent
    (x y : Set.Icc (0 : ℝ) (0 + (l + r)))
    (hxy : AddCircle.EndpointIdent (l + r : ℝ) 0 x y) :
    outerEndpointArc l r hl hr x = outerEndpointArc l r hl hr y := by
  cases hxy
  rw [outerEndpointArc_apply, outerEndpointArc_apply]
  simpa only [zero_add] using outerArc_endpoints l r hl hr

/-- The pasted outer path after identifying its top endpoints. -/
noncomputable def outerBoundaryQuotMap :
    C(Quot (AddCircle.EndpointIdent (l + r : ℝ) 0), boundary) where
  toFun :=
    Quot.lift (outerEndpointArc l r hl hr)
      (outerArc_endpointIdent l r hl hr)
  continuous_toFun :=
    continuous_quot_lift (outerArc_endpointIdent l r hl hr)
      (outerEndpointArc l r hl hr).continuous

theorem outerBoundaryQuotMap_mk
    (x : Set.Icc (0 : ℝ) (0 + (l + r))) :
    outerBoundaryQuotMap l r hl hr (Quot.mk _ x) =
      outerEndpointArc l r hl hr x :=
  rfl

theorem outerBoundaryQuotMap_surjective :
    Function.Surjective (outerBoundaryQuotMap l r hl hr) := by
  intro z
  obtain ⟨x, hx⟩ := outerArc_surjective l r hl hr z
  let x' : Set.Icc (0 : ℝ) (0 + (l + r)) :=
    ⟨x.1, by simpa only [zero_add] using x.2⟩
  refine ⟨Quot.mk _ x', ?_⟩
  exact hx

theorem outerBoundaryQuotMap_injective :
    Function.Injective (outerBoundaryQuotMap l r hl hr) := by
  intro q₁ q₂ hq
  induction q₁ using Quot.inductionOn with
  | _ x =>
      induction q₂ using Quot.inductionOn with
      | _ y =>
          change
            outerEndpointArc l r hl hr x =
              outerEndpointArc l r hl hr y at hq
          let x' : Set.Icc (0 : ℝ) (l + r) :=
            ⟨x.1, by simpa only [zero_add] using x.2⟩
          let y' : Set.Icc (0 : ℝ) (l + r) :=
            ⟨y.1, by simpa only [zero_add] using y.2⟩
          have hq' :
              outerArc l r hl hr x' =
                outerArc l r hl hr y' :=
            hq
          rcases outerArc_eq_imp_endpointIdent l r hl hr x' y' hq' with
            hxy | hends | hends
          · have hvalues := congrArg Subtype.val hxy
            have : x = y := Subtype.ext hvalues
            subst y
            rfl
          · have hx :
                x =
                  (⟨0, by
                    constructor
                    · rfl
                    · positivity⟩ :
                    Set.Icc (0 : ℝ) (0 + (l + r))) :=
              Subtype.ext hends.1
            have hy :
                y =
                  (⟨0 + (l + r), by
                    constructor
                    · positivity
                    · rfl⟩ :
                    Set.Icc (0 : ℝ) (0 + (l + r))) := by
              apply Subtype.ext
              simpa only [zero_add] using hends.2
            rw [hx, hy]
            exact Quot.sound AddCircle.EndpointIdent.mk
          · have hx :
                x =
                  (⟨0 + (l + r), by
                    constructor
                    · positivity
                    · rfl⟩ :
                    Set.Icc (0 : ℝ) (0 + (l + r))) := by
              apply Subtype.ext
              simpa only [zero_add] using hends.1
            have hy :
                y =
                  (⟨0, by
                    constructor
                    · rfl
                    · positivity⟩ :
                    Set.Icc (0 : ℝ) (0 + (l + r))) :=
              Subtype.ext hends.2
            rw [hx, hy]
            exact (Quot.sound AddCircle.EndpointIdent.mk).symm

theorem outerBoundaryQuotMap_bijective :
    Function.Bijective (outerBoundaryQuotMap l r hl hr) :=
  ⟨outerBoundaryQuotMap_injective l r hl hr,
    outerBoundaryQuotMap_surjective l r hl hr⟩

/-- The endpoint quotient of the pasted old-boundary path is exactly the square boundary. -/
noncomputable def outerBoundaryQuotHomeomorph :
    Quot (AddCircle.EndpointIdent (l + r : ℝ) 0) ≃ₜ boundary :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (outerBoundaryQuotMap l r hl hr)
      (outerBoundaryQuotMap_bijective l r hl hr))
    (outerBoundaryQuotMap l r hl hr).continuous

@[simp]
theorem outerBoundaryQuotHomeomorph_mk
    (x : Set.Icc (0 : ℝ) (0 + (l + r))) :
    outerBoundaryQuotHomeomorph l r hl hr (Quot.mk _ x) =
      outerEndpointArc l r hl hr x :=
  rfl

/-- The additive circle parameterized by the old sides is the outer square boundary. -/
noncomputable def outerAddCircleHomeomorph :
    AddCircle (l + r : ℝ) ≃ₜ boundary := by
  letI : Fact (0 < (l + r : ℝ)) := ⟨by positivity⟩
  exact
    (AddCircle.homeoIccQuot (l + r : ℝ) 0).trans
      (outerBoundaryQuotHomeomorph l r hl hr)

/-- The exact boundary parameterization used to extend the old sides across the selected
source polygon. -/
noncomputable def outerBoundaryHomeomorph : Circle ≃ₜ boundary :=
  (AddCircle.homeomorphCircle
      (by positivity : (l + r : ℝ) ≠ 0)).symm.trans
    (outerAddCircleHomeomorph l r hl hr)

end OuterBoundary

theorem outerAddCircleHomeomorph_apply_of_mem_Ico
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : ℝ) (hx : x ∈ Set.Ico 0 (l + r : ℝ)) :
    outerAddCircleHomeomorph l r hl hr
        (x : AddCircle (l + r : ℝ)) =
      outerArc l r hl hr
        ⟨x, ⟨hx.1, hx.2.le⟩⟩ := by
  letI : Fact (0 < (l + r : ℝ)) := ⟨by positivity⟩
  unfold outerAddCircleHomeomorph
  simp only [Homeomorph.trans_apply]
  have hsource :
      (AddCircle.homeoIccQuot (l + r : ℝ) 0)
          (x : AddCircle (l + r : ℝ)) =
        Quot.mk _
          (⟨x, hx.1, by simpa only [zero_add] using hx.2.le⟩ :
            Set.Icc (0 : ℝ) (0 + (l + r))) := by
    change Quot.mk _
      (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco (l + r : ℝ) 0
          (x : AddCircle (l + r : ℝ)))) = _
    rw [AddCircle.equivIco, QuotientAddGroup.equivIcoMod_coe]
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact (toIcoMod_eq_self (Fact.out : 0 < (l + r : ℝ))).2
      (by simpa only [zero_add] using hx)
  rw [hsource, outerBoundaryQuotHomeomorph_mk,
    outerEndpointArc_apply]

theorem outerBoundaryHomeomorph_exp_of_mem_Ico
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : ℝ) (hx : x ∈ Set.Ico 0 (l + r : ℝ)) :
    outerBoundaryHomeomorph l r hl hr
        (Circle.exp (2 * Real.pi / (l + r) * x)) =
      outerArc l r hl hr
        ⟨x, ⟨hx.1, hx.2.le⟩⟩ := by
  have hperiod : (l + r : ℝ) ≠ 0 := by positivity
  rw [show
      Circle.exp (2 * Real.pi / (l + r) * x) =
        AddCircle.homeomorphCircle hperiod
          (x : AddCircle (l + r : ℝ)) by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]]
  unfold outerBoundaryHomeomorph
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  exact outerAddCircleHomeomorph_apply_of_mem_Ico l r hl hr x hx

theorem outerBoundaryHomeomorph_exp_of_mem_Icc
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (l + r : ℝ)) :
    outerBoundaryHomeomorph l r hl hr
        (Circle.exp (2 * Real.pi / (l + r) * x)) =
      outerArc l r hl hr ⟨x, hx⟩ := by
  by_cases hxLast : x = (l + r : ℝ)
  · subst x
    have hperiod : (l + r : ℝ) ≠ 0 := by positivity
    have hexp :
        Circle.exp
            (2 * Real.pi / (l + r : ℝ) * (l + r : ℝ)) =
          Circle.exp (2 * Real.pi / (l + r : ℝ) * 0) := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, ?_⟩
      field_simp [hperiod]
      ring
    rw [hexp]
    rw [outerBoundaryHomeomorph_exp_of_mem_Ico
      l r hl hr 0 (by constructor <;> positivity)]
    exact outerArc_endpoints l r hl hr
  · apply outerBoundaryHomeomorph_exp_of_mem_Ico
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hxLast⟩

/-- The combined real parameter of a polygon side. -/
def polygonSideParameter {n : ℕ} (i : Fin n) (t : unitInterval) :
    Set.Icc (0 : ℝ) n :=
  ⟨(i : ℝ) + (t : ℝ), by
    constructor
    · exact add_nonneg (Nat.cast_nonneg i) t.property.1
    · have hi : (i : ℝ) + 1 ≤ n := by
        exact_mod_cast i.isLt
      linarith [t.property.2]⟩

/-- The same parameter with the split side count displayed as a sum in `ℝ`. -/
def sourceSideParameter
    (l r : ℕ) (i : Fin (l + r)) (t : unitInterval) :
    Set.Icc (0 : ℝ) ((l : ℝ) + r) :=
  ⟨(i : ℝ) + (t : ℝ), by
    have h := (polygonSideParameter i t).2
    change
      0 ≤ (i : ℝ) + (t : ℝ) ∧
        (i : ℝ) + (t : ℝ) ≤ (l + r : ℕ) at h
    change
      0 ≤ (i : ℝ) + (t : ℝ) ∧
        (i : ℝ) + (t : ℝ) ≤ (l : ℝ) + r
    simpa only [Nat.cast_add] using h⟩

/-- Extend the exact outer-boundary parameterization across the unsplit source polygon. -/
noncomputable def sourceCellHomeomorph
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    PolygonCell (l + r) ≃ₜ square :=
  cellSquareHomeomorph (outerBoundaryHomeomorph l r hl hr)

theorem sourceCellHomeomorph_ofCircle_exp
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (l + r : ℝ)) :
    sourceCellHomeomorph l r hl hr
        (PolygonCell.ofCircle (l + r)
          (Circle.exp (2 * Real.pi / (l + r) * x))) =
      boundaryInclusion (outerArc l r hl hr ⟨x, hx⟩) := by
  rw [sourceCellHomeomorph, cellSquareHomeomorph_ofCircle,
    outerBoundaryHomeomorph_exp_of_mem_Icc]

theorem sourceCellHomeomorph_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin (l + r)) (t : unitInterval) :
    sourceCellHomeomorph l r hl hr (PolygonCell.side i t) =
      boundaryInclusion
        (outerArc l r hl hr (sourceSideParameter l r i t)) := by
  change
    sourceCellHomeomorph l r hl hr
        (PolygonCell.ofCircle (l + r)
          (Circle.exp (PolygonCell.sideAngle i t))) = _
  have hangle :
      PolygonCell.sideAngle i t =
        2 * Real.pi / (l + r : ℝ) *
          ((i : ℝ) + (t : ℝ)) := by
    unfold PolygonCell.sideAngle
    push_cast
    ring
  rw [hangle]
  exact sourceCellHomeomorph_ofCircle_exp l r hl hr
    ((i : ℝ) + (t : ℝ)) (sourceSideParameter l r i t).2

theorem boundaryInclusion_finalOldArc_polygonSide
    (l : ℕ) (hl : 0 < l) (i : Fin l) (t : unitInterval) :
    boundaryInclusion
        (finalOldArc l hl (polygonSideParameter i t)) =
      leftPlacement
        (finalSideCellHomeomorph l hl
          (PolygonCell.side (Fin.castAdd 1 i) t)) := by
  apply Subtype.ext
  change
    (leftPlacement
        (finalOldArcLocal l hl (polygonSideParameter i t))).1 =
      (leftPlacement
        (finalSideCellHomeomorph l hl
          (PolygonCell.side (Fin.castAdd 1 i) t))).1
  apply congrArg Subtype.val
  apply congrArg leftPlacement
  rw [finalOldArcLocal_apply, PolygonCell.side]
  apply congrArg (finalSideCellHomeomorph l hl)
  apply PolygonCell.ext
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply congrArg Circle.exp
  unfold PolygonCell.sideAngle polygonSideParameter
  simp only [Fin.val_castAdd]
  push_cast
  ring

theorem boundaryInclusion_firstOldArc_polygonSide
    (r : ℕ) (hr : 0 < r) (i : Fin r) (t : unitInterval) :
    boundaryInclusion
        (firstOldArc r hr (polygonSideParameter i t)) =
      rightPlacement
        (firstSideCellHomeomorph r hr
          (PolygonCell.side (i.addNat 1) t)) := by
  apply Subtype.ext
  change
    (rightPlacement
        (firstOldArcLocal r hr (polygonSideParameter i t))).1 =
      (rightPlacement
        (firstSideCellHomeomorph r hr
          (PolygonCell.side (i.addNat 1) t))).1
  apply congrArg Subtype.val
  apply congrArg rightPlacement
  rw [firstOldArcLocal_apply, PolygonCell.side]
  apply congrArg (firstSideCellHomeomorph r hr)
  apply PolygonCell.ext
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply congrArg Circle.exp
  unfold PolygonCell.sideAngle polygonSideParameter
  simp only [Fin.val_addNat]
  push_cast
  ring

theorem outerArc_source_left_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin l) (t : unitInterval) :
    outerArc l r hl hr
        (sourceSideParameter l r (Fin.castAdd r i) t) =
      finalOldArc l hl (polygonSideParameter i t) := by
  have hx :
      (sourceSideParameter l r (Fin.castAdd r i) t).1 ≤ l := by
    change (i : ℝ) + (t : ℝ) ≤ l
    exact (polygonSideParameter i t).2.2
  rw [outerArc_apply_of_le l r hl hr _ hx]
  apply congrArg (finalOldArc l hl)
  apply Subtype.ext
  rfl

theorem outerArc_source_right_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin r) (t : unitInterval) :
    outerArc l r hl hr
        (sourceSideParameter l r (Fin.natAdd l i) t) =
      firstOldArc r hr (polygonSideParameter i t) := by
  let x :=
    sourceSideParameter l r (Fin.natAdd l i) t
  let s := polygonSideParameter i t
  by_cases hsZero : s.1 = 0
  · have hxLe : x.1 ≤ l := by
      dsimp [x, sourceSideParameter, s, polygonSideParameter] at hsZero ⊢
      simp only [Nat.cast_add]
      linarith
    rw [outerArc_apply_of_le l r hl hr x hxLe]
    have hxLast :
        (⟨x.1, ⟨x.2.1, hxLe⟩⟩ : Set.Icc (0 : ℝ) l) =
          ⟨l, by simp⟩ := by
      apply Subtype.ext
      dsimp [x, sourceSideParameter, s, polygonSideParameter] at hsZero ⊢
      simp only [Nat.cast_add]
      linarith
    rw [hxLast, finalOldArc_last_eq_firstOldArc_zero l r hl hr]
    apply congrArg (firstOldArc r hr)
    apply Subtype.ext
    exact hsZero.symm
  · have hsPos : 0 < s.1 :=
      lt_of_le_of_ne s.2.1 (Ne.symm hsZero)
    have hxNot : ¬x.1 ≤ l := by
      dsimp [x, sourceSideParameter, s, polygonSideParameter] at hsPos ⊢
      simp only [Nat.cast_add]
      linarith
    rw [outerArc_apply_of_not_le l r hl hr x hxNot]
    apply congrArg (firstOldArc r hr)
    apply Subtype.ext
    dsimp [x, sourceSideParameter, s, polygonSideParameter]
    simp only [Nat.cast_add]
    ring

/-- On every old left side, the unsplit source polygon map agrees exactly with the
corresponding placed child side. -/
theorem sourceCellHomeomorph_left_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin l) (t : unitInterval) :
    sourceCellHomeomorph l r hl hr
        (PolygonCell.side (Fin.castAdd r i) t) =
      leftPlacement
        (finalSideCellHomeomorph l hl
          (PolygonCell.side (Fin.castAdd 1 i) t)) := by
  rw [sourceCellHomeomorph_side,
    outerArc_source_left_side,
    boundaryInclusion_finalOldArc_polygonSide]

/-- On every old right side, the unsplit source polygon map agrees exactly with the
corresponding reflected and placed child side. -/
theorem sourceCellHomeomorph_right_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin r) (t : unitInterval) :
    sourceCellHomeomorph l r hl hr
        (PolygonCell.side (Fin.natAdd l i) t) =
      rightPlacement
        (firstSideCellHomeomorph r hr
          (PolygonCell.side (i.addNat 1) t)) := by
  rw [sourceCellHomeomorph_side,
    outerArc_source_right_side,
    boundaryInclusion_firstOldArc_polygonSide]

@[simp]
theorem paramChildGluingHomeomorph_mk_inl
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (z : PolygonCell (l + 1)) :
    paramChildGluingHomeomorph l r hl hr
        (@Quotient.mk'' (ChildPair l r)
          (paramChildSeamSetoid l r) (.inl z)) =
      leftPlacement (finalSideCellHomeomorph l hl z) :=
  rfl

@[simp]
theorem paramChildGluingHomeomorph_mk_inr
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (z : PolygonCell (r + 1)) :
    paramChildGluingHomeomorph l r hl hr
        (@Quotient.mk'' (ChildPair l r)
          (paramChildSeamSetoid l r) (.inr z)) =
      rightPlacement (firstSideCellHomeomorph r hr z) :=
  rfl

/-- The complete local P2 equivalence: one unsplit polygon is homeomorphic to the quotient of
the two child polygons by their reversed fresh-side identification. -/
noncomputable def sourceChildGluingHomeomorph
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) :
    PolygonCell (l + r) ≃ₜ ParamChildGluing l r :=
  (sourceCellHomeomorph l r hl hr).trans
    (paramChildGluingHomeomorph l r hl hr).symm

/-- The local P2 homeomorphism sends every left source side to the corresponding selected-child
side class. -/
theorem sourceChildGluingHomeomorph_left_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin l) (t : unitInterval) :
    sourceChildGluingHomeomorph l r hl hr
        (PolygonCell.side (Fin.castAdd r i) t) =
      @Quotient.mk'' (ChildPair l r)
        (paramChildSeamSetoid l r)
        (.inl (PolygonCell.side (Fin.castAdd 1 i) t)) := by
  apply (paramChildGluingHomeomorph l r hl hr).injective
  rw [sourceChildGluingHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply,
    paramChildGluingHomeomorph_mk_inl,
    sourceCellHomeomorph_left_side]

/-- The local P2 homeomorphism sends every right source side to the corresponding right-child
side class. -/
theorem sourceChildGluingHomeomorph_right_side
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (i : Fin r) (t : unitInterval) :
    sourceChildGluingHomeomorph l r hl hr
        (PolygonCell.side (Fin.natAdd l i) t) =
      @Quotient.mk'' (ChildPair l r)
        (paramChildSeamSetoid l r)
        (.inr (PolygonCell.side (i.addNat 1) t)) := by
  apply (paramChildGluingHomeomorph l r hl hr).injective
  rw [sourceChildGluingHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply,
    paramChildGluingHomeomorph_mk_inr,
    sourceCellHomeomorph_right_side]

end DiskSquare

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification20_block_01
/- END ClassificationOfSurfaces.DiskSquare -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicCanonical | 38df8f546a41fa31c83338e7776b68f817a11e614d132de44e196c5dad373469 -/
section schottkyclassification20_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Canonical finite cyclic presentations

This file fixes the finite-cyclic endpoint of the Gallier--Xu normalization lane. A typed
one-face boundary word is enumerated by `Fin` exactly once, and the named normal forms use that
adapter. The sphere branch uses the ordinary-valid two-monogon presentation obtained from the
exceptional empty-word sphere by P2.

The orientable and nonorientable words remain the existing `NormalForm.orientableBoundaryWord`
and `NormalForm.nonOrientableBoundaryWord`; this file does not introduce another formulation of
the Lean-Eval representatives.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open SurfaceCellComplex

namespace FiniteCyclicPresentation

/-- The two existing projections from a signed dart to its unoriented edge agree. -/
theorem map_edgeOfDart_eq_map_edgeName {Edge : Type}
    (word : List (SignedDart Edge)) :
    word.map edgeOfDart = word.map SignedDart.edgeName := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      cases d <;> simp [edgeOfDart, SignedDart.edgeName, ih]

/-- Enumerate the edge names of a typed one-face signed boundary word. -/
@[reducible]
noncomputable def ofOneFaceWord {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) : FiniteCyclicPresentation where
  edgeCount := Fintype.card Edge
  faces := [word.map (SignedDart.mapEquiv (Fintype.equivFin Edge))]

theorem ofOneFaceWord_faces_length {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).faces.length = 1 := by
  simp [ofOneFaceWord]

theorem ofOneFaceWord_boundary_zero {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).boundary 0 =
      word.map (SignedDart.mapEquiv (Fintype.equivFin Edge)) := by
  rfl

theorem ofOneFaceWord_face_eq_zero {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    f = 0 := by
  apply Fin.ext
  have hf := f.isLt
  change f.val <
    [word.map (SignedDart.mapEquiv (Fintype.equivFin Edge))].length at hf
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hf
  change f.val = 0
  omega

theorem ofOneFaceWord_boundary {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    (ofOneFaceWord word).boundary f =
      word.map (SignedDart.mapEquiv (Fintype.equivFin Edge)) := by
  rw [ofOneFaceWord_face_eq_zero word f]
  exact ofOneFaceWord_boundary_zero word

/-- The original edge names are equivalent to the enumerated one-face presentation edges. -/
noncomputable def ofOneFaceWordEdgeEquiv {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    Edge ≃ (ofOneFaceWord word).Edge := by
  change Edge ≃ Fin (Fintype.card Edge)
  exact Fintype.equivFin Edge

theorem ofOneFaceWord_edgeMultiplicity {Edge : Type} [Fintype Edge]
    [DecidableEq Edge] (word : List (SignedDart Edge)) (e : Edge) :
    (ofOneFaceWord word).edgeMultiplicity
        (ofOneFaceWordEdgeEquiv word e) =
      (word.map edgeOfDart).count e := by
  classical
  simp only [edgeMultiplicity, ofOneFaceWord, faceEdgeMultiplicity,
    ofOneFaceWordEdgeEquiv, id_eq, boundary, List.get_eq_getElem, List.length_cons,
    List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero,
    List.map_map, Function.comp_def, edgeOfDart_mapEquiv, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, zero_add, smul_eq_mul, one_mul]
  have hmap :
      word.map (fun x => Fintype.equivFin Edge (edgeOfDart x)) =
        (word.map edgeOfDart).map (Fintype.equivFin Edge) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap]
  exact List.count_map_of_injective (word.map edgeOfDart)
    (Fintype.equivFin Edge) (Fintype.equivFin Edge).injective e

/-- A nonempty typed one-face word with surface edge multiplicities gives an ordinary-valid finite
cyclic presentation. -/
theorem ofOneFaceWord_isSurfaceValid {Edge : Type} [Fintype Edge]
    [DecidableEq Edge] (word : List (SignedDart Edge))
    (hne : word ≠ [])
    (hmultiplicity :
      ∀ e : Edge,
        (word.map edgeOfDart).count e = 1 ∨
          (word.map edgeOfDart).count e = 2) :
    (ofOneFaceWord word).IsSurfaceValid := by
  classical
  refine ⟨⟨0, by simp [ofOneFaceWord]⟩, ?_, ?_, ?_⟩
  · intro f
    rw [ofOneFaceWord_boundary]
    intro hmapped
    apply hne
    have hlength := congrArg List.length hmapped
    simpa using hlength
  · intro f g _h
    rw [ofOneFaceWord_face_eq_zero word f,
      ofOneFaceWord_face_eq_zero word g]
  · intro a
    let e := (ofOneFaceWordEdgeEquiv word).symm a
    have ha : a = ofOneFaceWordEdgeEquiv word e := by
      exact ((ofOneFaceWordEdgeEquiv word).apply_symm_apply a).symm
    rw [ha, ofOneFaceWord_edgeMultiplicity]
    exact hmultiplicity e

/-- Every enumerated one-face presentation is connected at the face-incidence level. -/
theorem ofOneFaceWord_isConnected {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).IsConnected := by
  refine ⟨⟨0, by simp [ofOneFaceWord]⟩, ?_⟩
  intro f g
  rw [ofOneFaceWord_face_eq_zero word f,
    ofOneFaceWord_face_eq_zero word g]

end FiniteCyclicPresentation

namespace NormalForm

/-- The single finite-cyclic target selected for each named normal form.

The admissibility predicate excludes the empty orientable word and the zero-crosscap
nonorientable word when ordinary surface validity is required. -/
noncomputable def canonicalPresentation : NormalForm → FiniteCyclicPresentation
  | .sphere => FiniteCyclicPresentation.twoMonogonSphere
  | .orientable p n =>
      FiniteCyclicPresentation.ofOneFaceWord (orientableBoundaryWord p n)
  | .nonOrientable p n =>
      FiniteCyclicPresentation.ofOneFaceWord (nonOrientableBoundaryWord p n)

@[simp]
theorem canonicalPresentation_sphere :
    canonicalPresentation .sphere =
      FiniteCyclicPresentation.twoMonogonSphere :=
  rfl

@[simp]
theorem canonicalPresentation_orientable (p n : ℕ) :
    canonicalPresentation (.orientable p n) =
      FiniteCyclicPresentation.ofOneFaceWord (orientableBoundaryWord p n) :=
  rfl

@[simp]
theorem canonicalPresentation_nonOrientable (p n : ℕ) :
    canonicalPresentation (.nonOrientable p n) =
      FiniteCyclicPresentation.ofOneFaceWord (nonOrientableBoundaryWord p n) :=
  rfl

/-- Every Eval-admissible canonical presentation has ordinary surface incidence validity. -/
theorem canonicalPresentation_isSurfaceValid
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    N.canonicalPresentation.IsSurfaceValid := by
  cases N with
  | sphere =>
      exact FiniteCyclicPresentation.twoMonogonSphere_isSurfaceValid
  | orientable p n =>
      apply FiniteCyclicPresentation.ofOneFaceWord_isSurfaceValid
      · exact orientableBoundaryWord_ne_nil hN
      · intro e
        have hocc := orientableBoundaryWord_edge_occurrences p n e
        rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hocc
        rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
        cases e <;> simp_all
  | nonOrientable p n =>
      apply FiniteCyclicPresentation.ofOneFaceWord_isSurfaceValid
      · exact nonOrientableBoundaryWord_ne_nil hN
      · intro e
        have hocc := nonOrientableBoundaryWord_edge_occurrences p n e
        rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hocc
        rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
        cases e <;> simp_all

/-- Canonical finite-cyclic presentations are face-incidence connected. -/
theorem canonicalPresentation_isConnected (N : NormalForm) :
    N.canonicalPresentation.IsConnected := by
  cases N with
  | sphere =>
      exact FiniteCyclicPresentation.twoMonogonSphere_isConnected
  | orientable p n =>
      exact FiniteCyclicPresentation.ofOneFaceWord_isConnected
        (orientableBoundaryWord p n)
  | nonOrientable p n =>
      exact FiniteCyclicPresentation.ofOneFaceWord_isConnected
        (nonOrientableBoundaryWord p n)

/-- Eval-admissible canonical presentations satisfy the packed Gallier--Xu input predicate. -/
theorem canonicalPresentation_isGallierValid
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    N.canonicalPresentation.IsGallierValid :=
  FiniteCyclicPresentation.isGallierValid_of_isSurfaceValid_of_isConnected
    (N.canonicalPresentation_isSurfaceValid hN)
    N.canonicalPresentation_isConnected

end NormalForm

end LeanEval.Topology.ClassificationOfSurfaces
end schottkyclassification20_block_02
/- END ClassificationOfSurfaces.FiniteCyclicCanonical -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicP1 | 01419082d3453cbac0fc44e0737f8090b0dd56ed298f175e5f70046b5a98e6a3 -/
section schottkyclassification20_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Gallier--Xu P1 edge subdivision

This file formalizes the first primitive subdivision from Gallier--Xu, Definition 6.3. For a
chosen oriented edge `a`, P1 globally replaces

* `a` by `b c`, and
* `a⁻¹` by `c⁻¹ b⁻¹`.

The canonical finite implementation retains every old edge name through `Fin.castSucc`, uses the
retained name of `a` for `b`, and uses `Fin.last` for the fresh edge `c`. A contraction deletes
the fresh edge and sends every retained edge back to its old name. This contraction is a left
inverse on words, including cyclic words, so P1 both preserves and reflects cyclic rotation.
The selected underlying edge uses its positive stored orientation canonically. The
`SignedPresentationIso` in `P1Subdivision` allows the two target edge names to be renamed and
reoriented when a different orientation convention is desired.

The presentation-level construction preserves face positions, copies the multiplicity of `a` to
both subdivided edges, and preserves ordinary validity, face-incidence connectivity, and
`IsGallierValid`. `P1Subdivision` closes the canonical construction under signed presentation
isomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P1

/-- Retain an old signed edge in the enlarged edge type. -/
def castSuccDart {n : ℕ} : SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos e.castSucc
  | .neg e => .neg e.castSucc

@[simp]
theorem castSuccDart_pos {n : ℕ} (e : Fin n) :
    castSuccDart (.pos e) = .pos e.castSucc :=
  rfl

@[simp]
theorem castSuccDart_neg {n : ℕ} (e : Fin n) :
    castSuccDart (.neg e) = .neg e.castSucc :=
  rfl

@[simp]
theorem edgeOfDart_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    edgeOfDart (castSuccDart d) = (edgeOfDart d).castSucc := by
  cases d <;> rfl

/-- The fresh second subedge in the canonical P1 expansion. -/
def freshEdge (n : ℕ) : Fin (n + 1) :=
  Fin.last n

/-- The retained first subedge in the canonical P1 expansion. -/
def firstSubedge {n : ℕ} (a : Fin n) : Fin (n + 1) :=
  a.castSucc

theorem firstSubedge_ne_freshEdge {n : ℕ} (a : Fin n) :
    firstSubedge a ≠ freshEdge n :=
  Fin.castSucc_ne_last a

/-- Substitute one signed occurrence according to Gallier--Xu P1. -/
def expandDart {n : ℕ} (a : Fin n) :
    SignedDart (Fin n) → List (SignedDart (Fin (n + 1)))
  | .pos e =>
      if e = a then
        [.pos (firstSubedge a), .pos (freshEdge n)]
      else
        [.pos e.castSucc]
  | .neg e =>
      if e = a then
        [.neg (freshEdge n), .neg (firstSubedge a)]
      else
        [.neg e.castSucc]

@[simp]
theorem expandDart_pos_self {n : ℕ} (a : Fin n) :
    expandDart a (.pos a) = [.pos (firstSubedge a), .pos (freshEdge n)] := by
  simp [expandDart]

@[simp]
theorem expandDart_neg_self {n : ℕ} (a : Fin n) :
    expandDart a (.neg a) = [.neg (freshEdge n), .neg (firstSubedge a)] := by
  simp [expandDart]

theorem expandDart_pos_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.pos e) = [.pos e.castSucc] := by
  simp [expandDart, h]

theorem expandDart_neg_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.neg e) = [.neg e.castSucc] := by
  simp [expandDart, h]

/-- P1 sends the opposite dart to the inverse of the substituted word. -/
@[simp]
theorem expandDart_flip {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandDart a d.flip = inverseWord (expandDart a d) := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]

theorem castSuccDart_mem_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    castSuccDart d ∈ expandDart a d := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]

/-- Contract one target dart: discard the fresh edge and retain every old edge. -/
def contractDart {n : ℕ} :
    SignedDart (Fin (n + 1)) → Option (SignedDart (Fin n))
  | .pos e => Fin.lastCases none (fun b ↦ some (.pos b)) e
  | .neg e => Fin.lastCases none (fun b ↦ some (.neg b)) e

@[simp]
theorem contractDart_pos_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.pos e.castSucc) = some (.pos e) := by
  simp [contractDart]

@[simp]
theorem contractDart_neg_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.neg e.castSucc) = some (.neg e) := by
  simp [contractDart]

@[simp]
theorem contractDart_pos_freshEdge (n : ℕ) :
    contractDart (.pos (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

@[simp]
theorem contractDart_neg_freshEdge (n : ℕ) :
    contractDart (.neg (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

/-- Apply P1 simultaneously to every occurrence in a linear representative of a cyclic word. -/
def expandWord {n : ℕ} (a : Fin n) (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  word.flatMap (expandDart a)

/-- Contract a P1 word by deleting the fresh subedge. -/
def contractWord {n : ℕ} (word : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  word.filterMap contractDart

@[simp]
theorem expandWord_nil {n : ℕ} (a : Fin n) :
    expandWord a [] = [] :=
  rfl

@[simp]
theorem expandWord_cons {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (word : List (SignedDart (Fin n))) :
    expandWord a (d :: word) = expandDart a d ++ expandWord a word :=
  rfl

theorem expandWord_singleton {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandWord a [d] = expandDart a d := by
  simp [expandWord]

@[simp]
theorem expandWord_append {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    expandWord a (left ++ right) = expandWord a left ++ expandWord a right := by
  simp [expandWord]

@[simp]
theorem contractWord_nil {n : ℕ} :
    contractWord ([] : List (SignedDart (Fin (n + 1)))) = [] :=
  rfl

@[simp]
theorem contractWord_append {n : ℕ}
    (left right : List (SignedDart (Fin (n + 1)))) :
    contractWord (left ++ right) = contractWord left ++ contractWord right := by
  simp [contractWord]

/-- Contracting one substituted occurrence returns that occurrence. -/
@[simp]
theorem contractWord_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    contractWord (expandDart a d) = [d] := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]

/-- Contracting the global P1 substitution returns the original word exactly. -/
@[simp]
theorem contractWord_expandWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    contractWord (expandWord a word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [expandWord_cons, contractWord_append, contractWord_expandDart, ih]
      rfl

@[simp]
theorem expandWord_eq_nil_iff {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a word = [] ↔ word = [] := by
  constructor
  · intro h
    have hcontract := congrArg contractWord h
    simpa only [contractWord_expandWord, contractWord_nil] using hcontract
  · rintro rfl
    rfl

/-- P1 commutes with reversal of an oriented cyclic boundary word. -/
@[simp]
theorem expandWord_inverseWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a (inverseWord word) = inverseWord (expandWord a word) := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      calc
        expandWord a (inverseWord (d :: word)) =
            expandWord a (inverseWord word ++ [d.flip]) := by
              simp [inverseWord]
        _ = expandWord a (inverseWord word) ++ expandWord a [d.flip] :=
          expandWord_append a _ _
        _ = inverseWord (expandWord a word) ++ inverseWord (expandDart a d) := by
          rw [ih, expandWord_singleton, expandDart_flip]
        _ = inverseWord (expandDart a d ++ expandWord a word) :=
          (inverseWord_append _ _).symm
        _ = inverseWord (expandWord a (d :: word)) :=
          rfl

/-- A list-valued substitution preserves cyclic rotation. -/
theorem expandWord_isRotated {n : ℕ} {a : Fin n}
    {left right : List (SignedDart (Fin n))}
    (h : left.IsRotated right) :
    (expandWord a left).IsRotated (expandWord a right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    expandWord a left ~r expandWord a (left.drop m ++ left.take m) := by
      have hexpand :=
        congrArg (expandWord a) hleft
      rw [hexpand]
      simp only [expandWord_append]
      exact List.isRotated_append
    _ = expandWord a (left.rotate k) := congrArg (expandWord a) hrotate.symm

/-- Contraction preserves cyclic rotation even when the cut passes through a subdivided pair. -/
theorem contractWord_isRotated {n : ℕ}
    {left right : List (SignedDart (Fin (n + 1)))}
    (h : left.IsRotated right) :
    (contractWord left).IsRotated (contractWord right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    contractWord left ~r contractWord (left.drop m ++ left.take m) := by
      have hcontract :=
        congrArg contractWord hleft
      rw [hcontract]
      simp only [contractWord_append]
      exact List.isRotated_append
    _ = contractWord (left.rotate k) := congrArg contractWord hrotate.symm

/-- P1 substitution preserves and reflects cyclic rotation. -/
@[simp]
theorem expandWord_isRotated_iff {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    (expandWord a left).IsRotated (expandWord a right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [contractWord_expandWord] using contractWord_isRotated h
  · exact expandWord_isRotated

/-- The occurrence of every retained edge survives the expansion. -/
theorem castSucc_edge_mem_expandWord {n : ℕ} {a e : Fin n}
    {word : List (SignedDart (Fin n))}
    (h : e ∈ word.map edgeOfDart) :
    e.castSucc ∈ (expandWord a word).map edgeOfDart := by
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  refine List.mem_map.mpr ⟨castSuccDart d, ?_, edgeOfDart_castSuccDart d⟩
  exact List.mem_flatMap.mpr ⟨d, hd, castSuccDart_mem_expandDart a d⟩

/-- Each retained edge has exactly its old word multiplicity after P1. -/
theorem count_expandWord_castSucc {n : ℕ} (a e : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count e =
      ((expandWord a word).map edgeOfDart).count e.castSucc := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]
      | neg b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]

/-- The fresh edge receives exactly the old multiplicity of the subdivided edge. -/
theorem count_expandWord_freshEdge {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count a =
      ((expandWord a word).map edgeOfDart).count (freshEdge n) := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]
      | neg b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]

/-- Canonical presentation-level P1 expansion. -/
def expand (P : FiniteCyclicPresentation) (a : P.Edge) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := P.faces.map (expandWord a)

@[simp]
theorem expand_edgeCount (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).edgeCount = P.edgeCount + 1 :=
  rfl

@[simp]
theorem expand_faces_length (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).faces.length = P.faces.length := by
  simp [expand]

/-- P1 preserves face positions. -/
def faceEquiv (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.Face ≃ (expand P a).Face :=
  finCongr (expand_faces_length P a).symm

@[simp]
theorem faceEquiv_apply_val (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (faceEquiv P a f).val = f.val :=
  rfl

@[simp]
theorem expand_boundary (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (expand P a).boundary (faceEquiv P a f) =
      expandWord a (P.boundary f) := by
  simp [boundary, List.get_eq_getElem, expand, faceEquiv]
  rfl

/-- P1 copies every retained edge's facewise multiplicity. -/
theorem faceEdgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f e =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f) e.castSucc := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_castSucc a e (P.boundary f)

/-- P1 gives the fresh edge the subdivided edge's facewise multiplicity. -/
theorem faceEdgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f a =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f)
        (freshEdge P.edgeCount) := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_freshEdge a (P.boundary f)

/-- P1 copies every retained edge's total multiplicity. -/
theorem edgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) :
    P.edgeMultiplicity e = (expand P a).edgeMultiplicity e.castSucc := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_castSucc P a e f

/-- P1 gives the fresh edge the subdivided edge's total multiplicity. -/
theorem edgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.edgeMultiplicity a =
      (expand P a).edgeMultiplicity (freshEdge P.edgeCount) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_freshEdge P a f

/-- P1 sends source face adjacency to target face adjacency. -/
theorem map_faceAdjacent
    (P : FiniteCyclicPresentation) (a : P.Edge) {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    (expand P a).FaceAdjacent (faceEquiv P a f) (faceEquiv P a g) := by
  rcases h with ⟨e, hef, heg⟩
  refine ⟨e.castSucc, ?_, ?_⟩
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord hef
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord heg

/-- P1 preserves ordinary finite-presentation incidence validity. -/
theorem expand_isSurfaceValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsSurfaceValid) :
    (expand P a).IsSurfaceValid := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := (faceEquiv P a).symm q
    have hboundary :
        (expand P a).boundary (faceEquiv P a f) =
          expandWord a (P.boundary f) :=
      expand_boundary P a f
    rw [(faceEquiv P a).apply_symm_apply] at hboundary
    have hexpanded : expandWord a (P.boundary f) = [] := by
      rw [← hboundary]
      exact hq
    exact h.2.1 f ((expandWord_eq_nil_iff a (P.boundary f)).mp hexpanded)
  · intro q r hqr
    let f := (faceEquiv P a).symm q
    let g := (faceEquiv P a).symm r
    have htargetBoundary :
        ((expand P a).boundary (faceEquiv P a f)).IsRotated
          ((expand P a).boundary (faceEquiv P a g)) := by
      have hq : faceEquiv P a f = q :=
        (faceEquiv P a).apply_symm_apply q
      have hr : faceEquiv P a g = r :=
        (faceEquiv P a).apply_symm_apply r
      rw [hq, hr]
      exact hqr
    rw [expand_boundary, expand_boundary] at htargetBoundary
    have htarget :
        (expandWord a (P.boundary f)).IsRotated
          (expandWord a (P.boundary g)) :=
      htargetBoundary
    have hsource :=
      (expandWord_isRotated_iff a (P.boundary f) (P.boundary g)).mp htarget
    have hfg := h.2.2.1 f g hsource
    calc
      q = faceEquiv P a f := ((faceEquiv P a).apply_symm_apply q).symm
      _ = faceEquiv P a g := congrArg (faceEquiv P a) hfg
      _ = r := (faceEquiv P a).apply_symm_apply r
  · intro e
    change Fin (P.edgeCount + 1) at e
    refine Fin.lastCases ?_ (fun b ↦ ?_) e
    · have hmultiplicity := h.2.2.2 a
      rw [edgeMultiplicity_expand_freshEdge P a] at hmultiplicity
      simpa only [freshEdge] using hmultiplicity
    · have hmultiplicity := h.2.2.2 b
      rw [edgeMultiplicity_expand_castSucc P a b] at hmultiplicity
      exact hmultiplicity

/-- P1 preserves connectedness of the face-edge incidence graph. -/
theorem expand_isConnected
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsConnected) :
    (expand P a).IsConnected := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 ((faceEquiv P a).symm q) ((faceEquiv P a).symm r)
  have hmapped := hchain.lift (faceEquiv P a) fun _ _ hadj ↦
    map_faceAdjacent P a hadj
  change Relation.ReflTransGen (expand P a).FaceAdjacent
    (faceEquiv P a ((faceEquiv P a).symm q))
    (faceEquiv P a ((faceEquiv P a).symm r)) at hmapped
  simpa only [(faceEquiv P a).apply_symm_apply] using hmapped

/-- P1 preserves the regular and exceptional branches of Gallier validity.

The exceptional branch is impossible here because selecting `a` already supplies an edge. -/
theorem expand_isGallierValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsGallierValid) :
    (expand P a).IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl
      ⟨expand_isSurfaceValid P a hregular.1,
        expand_isConnected P a hregular.2⟩
  · exact Fin.elim0 (Fin.cast hempty.edgeCount_eq_zero a)

end P1

/-- A Gallier--Xu P1 subdivision, closed under signed relabeling and cyclic face rotation.

This is a syntactic move relation and deliberately does not bundle source validity. The
preservation theorems below transport validity and connectivity when those hypotheses are
available. -/
def P1Subdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ a : P.Edge, Nonempty (SignedPresentationIso (P1.expand P a) Q)

namespace P1Subdivision

/-- The canonical expansion is a P1 subdivision. -/
theorem canonical (P : FiniteCyclicPresentation) (a : P.Edge) :
    P1Subdivision P (P1.expand P a) :=
  ⟨a, ⟨SignedPresentationIso.refl _⟩⟩

/-- P1 subdivisions preserve ordinary incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isSurfaceValid (P1.expand_isSurfaceValid P a h)

/-- P1 subdivisions preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isConnected (P1.expand_isConnected P a h)

/-- P1 subdivisions preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isGallierValid (P1.expand_isGallierValid P a h)

end P1Subdivision

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification20_block_03
/- END ClassificationOfSurfaces.FiniteCyclicP1 -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicRealization | cd686d8b3618b9142c64c924a9fdca3bd9e7685bf2c952b600bbdc9781c35460 -/
section schottkyclassification20_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal realization of finite cyclic presentations

This file gives `FiniteCyclicPresentation` a quotient-space semantics directly from its stored
face words. A boundary occurrence is a face together with an index in that face's word, so
repeated signed darts remain distinct polygon sides.

The pre-realization is the disjoint union of the standard polygonal disks indexed by the
presentation's faces. Internal sides are paired exactly when their signed darts have the same
underlying edge; equal signs use the same interval parameter and opposite signs use the reversed
parameter.

`FiniteCyclicPresentation.IsSurfaceValid` already includes nonempty face boundaries, unlike the
legacy cell-complex predicate. It therefore supplies the complete occurrence-pairing certificate
needed by this construction.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open scoped BigOperators
open SurfaceCellComplex

/-- A position in one of the stored cyclic face words. -/
abbrev BoundaryOccurrence (P : FiniteCyclicPresentation) :=
  Σ f : P.Face, Fin (P.boundary f).length

instance boundaryOccurrenceFintype (P : FiniteCyclicPresentation) :
    Fintype P.BoundaryOccurrence :=
  inferInstance

namespace BoundaryOccurrence

/-- The signed dart stored at a boundary occurrence. -/
def dart {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) : P.Dart :=
  (P.boundary o.1).get o.2

/-- The unoriented edge stored at a boundary occurrence. -/
def edge {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) : P.Edge :=
  edgeOfDart o.dart

@[simp]
theorem dart_mk (P : FiniteCyclicPresentation) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (show P.BoundaryOccurrence from ⟨f, i⟩).dart = (P.boundary f).get i :=
  rfl

@[simp]
theorem edge_mk (P : FiniteCyclicPresentation) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (show P.BoundaryOccurrence from ⟨f, i⟩).edge =
      edgeOfDart ((P.boundary f).get i) :=
  rfl

end BoundaryOccurrence

/-- The polygon side indexed by a boundary occurrence. -/
def occurrenceSide (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    PolygonGluing.Side P.Face fun f => (P.boundary f).length :=
  ⟨o.1, o.2⟩

@[simp]
theorem occurrenceSide_face (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    (P.occurrenceSide o).face = o.1 :=
  rfl

@[simp]
theorem occurrenceSide_index (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    (P.occurrenceSide o).index = o.2 :=
  rfl

/-- All boundary occurrences carrying the unoriented edge `e`. -/
noncomputable def edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge) :
    Finset P.BoundaryOccurrence := by
  classical
  exact Finset.univ.filter fun o => o.edge = e

@[simp]
theorem mem_edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge)
    (o : P.BoundaryOccurrence) :
    o ∈ P.edgeOccurrences e ↔ o.edge = e := by
  classical
  simp [edgeOccurrences]

private noncomputable def boundaryIndexCount
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (P.boundary f).length)).filter
    fun i => edgeOfDart ((P.boundary f).get i) = e).card

private theorem boundaryIndexCount_eq_faceEdgeMultiplicity
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) :
    P.boundaryIndexCount f e = P.faceEdgeMultiplicity f e := by
  classical
  unfold boundaryIndexCount faceEdgeMultiplicity
  let v : List.Vector P.Edge (P.boundary f).length :=
    List.Vector.ofFn fun i => edgeOfDart ((P.boundary f).get i)
  simpa [v, List.ofFn_comp'] using
    Fin.card_filter_univ_eq_vector_get_eq_count e v

/-- Total edge multiplicity is exactly the cardinality of the corresponding occurrence fiber. -/
theorem edgeMultiplicity_eq_card_edgeOccurrences
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    P.edgeMultiplicity e = (P.edgeOccurrences e).card := by
  classical
  let allOccurrences : Finset P.BoundaryOccurrence :=
    (Finset.univ : Finset P.Face).sigma fun f =>
      (Finset.univ : Finset (Fin (P.boundary f).length))
  have hall : allOccurrences = Finset.univ := by
    ext o
    simp [allOccurrences]
  calc
    P.edgeMultiplicity e =
        ∑ f : P.Face, P.boundaryIndexCount f e := by
      unfold edgeMultiplicity
      apply Finset.sum_congr rfl
      intro f _hf
      exact (P.boundaryIndexCount_eq_faceEdgeMultiplicity f e).symm
    _ = (allOccurrences.filter fun o => o.edge = e).card := by
      unfold boundaryIndexCount
      rw [show allOccurrences =
          (Finset.univ : Finset P.Face).sigma fun f =>
            (Finset.univ : Finset (Fin (P.boundary f).length)) by
        rfl]
      rw [← Finset.card_sigma]
      congr 1
      ext o
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    _ = (P.edgeOccurrences e).card := by
      rw [hall]
      rfl

@[simp]
theorem card_edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge) :
    (P.edgeOccurrences e).card = P.edgeMultiplicity e :=
  (P.edgeMultiplicity_eq_card_edgeOccurrences e).symm

/-- Two distinct occurrences of the same edge certify that the edge is internal. -/
theorem not_isBoundaryEdge_of_ne_of_edge_eq
    {P : FiniteCyclicPresentation} {o p : P.BoundaryOccurrence}
    (hop : o ≠ p) (hedge : p.edge = o.edge) :
    ¬P.IsBoundaryEdge o.edge := by
  intro hboundary
  have ho : o ∈ P.edgeOccurrences o.edge :=
    (P.mem_edgeOccurrences o.edge o).mpr rfl
  have hp : p ∈ P.edgeOccurrences o.edge :=
    (P.mem_edgeOccurrences o.edge p).mpr hedge
  have hcard : 1 < (P.edgeOccurrences o.edge).card :=
    Finset.one_lt_card.mpr ⟨o, ho, p, hp, hop⟩
  rw [P.card_edgeOccurrences, hboundary] at hcard
  omega

private theorem dart_eq_or_eq_flip_iff_edge_eq
    {P : FiniteCyclicPresentation} (x d : P.Dart) :
    x = d ∨ x = d.flip ↔ edgeOfDart x = edgeOfDart d := by
  cases x <;> cases d <;> simp [edgeOfDart, SignedDart.flip]

/-- A compatible gluing instruction between two distinct internal boundary occurrences. -/
structure BoundaryPairing (P : FiniteCyclicPresentation) where
  /-- The `source` declaration. -/
  source : P.BoundaryOccurrence
  /-- The `target` declaration. -/
  target : P.BoundaryOccurrence
  source_ne_target : source ≠ target
  source_not_boundary : ¬P.IsBoundaryEdge source.edge
  target_not_boundary : ¬P.IsBoundaryEdge target.edge
  /-- The `direction` declaration. -/
  direction : PolygonGluing.ParameterDirection
  compatible :
    match direction with
    | .same => target.dart = source.dart
    | .opposite => target.dart = source.dart.flip

namespace IsSurfaceValid

/-- A non-boundary edge of a valid presentation occurs exactly twice. -/
theorem edgeMultiplicity_eq_two_of_not_boundary
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid) {e : P.Edge}
    (he : ¬P.IsBoundaryEdge e) :
    P.edgeMultiplicity e = 2 := by
  rcases h.2.2.2 e with hone | htwo
  · exact False.elim (he hone)
  · exact htwo

/-- Every internal occurrence has a unique distinct partner carrying the same unoriented edge. -/
theorem exists_unique_partner
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃! target : P.BoundaryOccurrence,
      source ≠ target ∧ target.edge = source.edge := by
  have hcard : (P.edgeOccurrences source.edge).card = 2 := by
    rw [P.card_edgeOccurrences]
    exact h.edgeMultiplicity_eq_two_of_not_boundary hsource
  obtain ⟨o₁, o₂, hne, hindices⟩ := Finset.card_eq_two.mp hcard
  have hcover (o : P.BoundaryOccurrence) (ho : o.edge = source.edge) :
      o = o₁ ∨ o = o₂ := by
    have hmem : o ∈ P.edgeOccurrences source.edge :=
      (P.mem_edgeOccurrences source.edge o).mpr ho
    simpa [hindices] using hmem
  have ho₁ : o₁.edge = source.edge := by
    apply (P.mem_edgeOccurrences source.edge o₁).mp
    simp [hindices]
  have ho₂ : o₂.edge = source.edge := by
    apply (P.mem_edgeOccurrences source.edge o₂).mp
    simp [hindices]
  rcases hcover source rfl with hsource₁ | hsource₂
  · refine ⟨o₂, ⟨hsource₁.trans_ne hne, ho₂⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact False.elim (htarget.1 (hsource₁.trans htarget₁.symm))
    · exact htarget₂
  · refine ⟨o₁, ⟨hsource₂.trans_ne hne.symm, ho₁⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact htarget₁
    · exact False.elim (htarget.1 (hsource₂.trans htarget₂.symm))

/-- Every internal boundary occurrence is the source of a compatible polygon-side pairing. -/
theorem exists_pairing_source
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃ pairing : P.BoundaryPairing, pairing.source = source := by
  obtain ⟨target, ⟨hne, hedge⟩, _hunique⟩ :=
    h.exists_unique_partner source hsource
  have htarget : ¬P.IsBoundaryEdge target.edge := by
    rw [hedge]
    exact hsource
  rcases (dart_eq_or_eq_flip_iff_edge_eq target.dart source.dart).mpr hedge with
    hsame | hopposite
  · exact ⟨⟨source, target, hne, hsource, htarget, .same, hsame⟩, rfl⟩
  · exact ⟨⟨source, target, hne, hsource, htarget, .opposite, hopposite⟩, rfl⟩

end IsSurfaceValid

namespace BoundaryPairing

/-- The polygon-side identification associated to a compatible occurrence pairing. -/
def identification {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    PolygonGluing.Identification P.Face fun f => (P.boundary f).length where
  source := P.occurrenceSide pairing.source
  target := P.occurrenceSide pairing.target
  direction := pairing.direction

@[simp]
theorem identification_source {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.source = P.occurrenceSide pairing.source :=
  rfl

@[simp]
theorem identification_target {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.target = P.occurrenceSide pairing.target :=
  rfl

@[simp]
theorem identification_direction {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.direction = pairing.direction :=
  rfl

end BoundaryPairing

/-- All polygon-side identifications compatible with a valid finite cyclic presentation. -/
def polygonalIdentifications
    (P : FiniteCyclicPresentation) (_valid : P.IsSurfaceValid) :
    Set (PolygonGluing.Identification P.Face fun f => (P.boundary f).length) :=
  Set.range BoundaryPairing.identification

@[simp]
theorem pairing_identification_mem
    {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    pairing.identification ∈ P.polygonalIdentifications valid :=
  ⟨pairing, rfl⟩

/-- Every internal occurrence of a valid presentation starts a prescribed identification. -/
theorem IsSurfaceValid.exists_identification_source
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃ identification ∈ P.polygonalIdentifications h,
      identification.source = P.occurrenceSide source := by
  obtain ⟨pairing, hp⟩ := h.exists_pairing_source source hsource
  refine ⟨pairing.identification, pairing_identification_mem h pairing, ?_⟩
  rw [BoundaryPairing.identification_source, hp]

/-- The disjoint union of the polygonal cells encoded by the stored face words. -/
abbrev PolygonalPreRealization (P : FiniteCyclicPresentation) : Type :=
  PolygonGluing.PreRealization P.Face fun f => (P.boundary f).length

/-- The generated relation from all compatible internal occurrence pairings. -/
abbrev PolygonalGluingRel
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    Setoid P.PolygonalPreRealization :=
  PolygonGluing.setoid (P.polygonalIdentifications valid)

/-- The polygonal quotient realized directly from a valid finite cyclic presentation. -/
abbrev PolygonalRealization
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) : Type :=
  PolygonGluing.Realization (P.polygonalIdentifications valid)

/-- The quotient map from the disjoint union of face polygons. -/
def polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    P.PolygonalPreRealization → P.PolygonalRealization valid :=
  PolygonGluing.mk (P.polygonalIdentifications valid)

theorem continuous_polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    Continuous (P.polygonalMk valid) :=
  PolygonGluing.continuous_mk (P.polygonalIdentifications valid)

theorem isQuotientMap_polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    _root_.Topology.IsQuotientMap (P.polygonalMk valid) :=
  PolygonGluing.isQuotientMap_mk (P.polygonalIdentifications valid)

/-- Every compatible pairing identifies the corresponding side points in the quotient. -/
theorem polygonalMk_pairing_eq
    {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    P.polygonalMk valid (pairing.identification.source.point t) =
      P.polygonalMk valid
        (pairing.identification.target.point (pairing.identification.parameter t)) :=
  PolygonGluing.mk_source_eq_mk_target pairing.identification
    (pairing_identification_mem valid pairing) t

/-- Cut-and-paste data sufficient to compare two polygonal realizations.

The maps start on the two polygonal pre-realizations but land in the opposite quotient. This
asymmetric-looking formulation is deliberate: after a polygon is cut into two faces, the reverse
map need not lift continuously to the disjoint union of those faces, although it can be continuous
as a map to their glued quotient. -/
structure RealizationEquivData
    (P Q : FiniteCyclicPresentation) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) where
  /-- The `toPre` declaration. -/
  toPre : P.PolygonalPreRealization → Q.PolygonalRealization validQ
  /-- The `invPre` declaration. -/
  invPre : Q.PolygonalPreRealization → P.PolygonalRealization validP
  continuous_toPre : Continuous toPre
  continuous_invPre : Continuous invPre
  to_respects :
    ∀ x y, P.PolygonalGluingRel validP x y → toPre x = toPre y
  inv_respects :
    ∀ x y, Q.PolygonalGluingRel validQ x y → invPre x = invPre y
  left_inverse_mk :
    ∀ x, Quotient.lift invPre inv_respects (toPre x) = P.polygonalMk validP x
  right_inverse_mk :
    ∀ y, Quotient.lift toPre to_respects (invPre y) = Q.polygonalMk validQ y

namespace RealizationEquivData

/-- Descend the forward cut-and-paste map through the source gluing relation. -/
def toQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    P.PolygonalRealization validP → Q.PolygonalRealization validQ :=
  Quotient.lift data.toPre data.to_respects

/-- Descend the reverse cut-and-paste map through the target gluing relation. -/
def invQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Q.PolygonalRealization validQ → P.PolygonalRealization validP :=
  Quotient.lift data.invPre data.inv_respects

@[simp]
theorem toQuotient_polygonalMk
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ)
    (x : P.PolygonalPreRealization) :
    data.toQuotient (P.polygonalMk validP x) = data.toPre x :=
  rfl

@[simp]
theorem invQuotient_polygonalMk
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ)
    (y : Q.PolygonalPreRealization) :
    data.invQuotient (Q.polygonalMk validQ y) = data.invPre y :=
  rfl

theorem continuous_toQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Continuous data.toQuotient :=
  data.continuous_toPre.quotient_lift data.to_respects

theorem continuous_invQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Continuous data.invQuotient :=
  data.continuous_invPre.quotient_lift data.inv_respects

/-- Cut-and-paste data descend to a homeomorphism of the generated polygonal quotients. -/
noncomputable def homeomorph
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ where
  toFun := data.toQuotient
  invFun := data.invQuotient
  left_inv := by
    intro q
    induction q using Quotient.inductionOn'
    exact data.left_inverse_mk _
  right_inv := by
    intro q
    induction q using Quotient.inductionOn'
    exact data.right_inverse_mk _
  continuous_toFun := data.continuous_toQuotient
  continuous_invFun := data.continuous_invQuotient

end RealizationEquivData

/-- Quotient semantics for comparing two valid finite cyclic presentations. -/
def PolygonallyEquivalent
    (P Q : FiniteCyclicPresentation) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) : Prop :=
  Nonempty (P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ)

/-- A cut-and-paste certificate proves polygonal equivalence. -/
theorem RealizationEquivData.polygonallyEquivalent
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    PolygonallyEquivalent P Q validP validQ :=
  ⟨data.homeomorph⟩

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification20_block_04
/- END ClassificationOfSurfaces.FiniteCyclicRealization -/

/- BEGIN ClassificationOfSurfaces.FiniteCyclicTriangulation | a05589a72243788342b3a9f4585f8f04ea9d6199a37d91dbd8081f38e3847069 -/
section schottkyclassification20_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite cyclic presentations of triangulations

This file relabels the finite faces and unoriented edges of a surface triangulation by `Fin`.
Each oriented triangle boundary is transported to a cyclic word of signed finite edge names.
Incidence validity and dual connectivity then pass to the resulting
`FiniteCyclicPresentation`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

/-- Oriented triangulation edges and signed cell-complex darts carry the same data. -/
private def orientedEdgeSignedDartEquiv {Edge : Type*} :
    OrientedEdge Edge ≃ SignedDart Edge where
  toFun := signedDartOfOrientedEdge
  invFun
    | .pos e => .pos e
    | .neg e => .neg e
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro d
    cases d <;> rfl

private theorem orientedEdgeSignedDartEquiv_apply {Edge : Type*} (d : OrientedEdge Edge) :
    orientedEdgeSignedDartEquiv d = signedDartOfOrientedEdge d :=
  rfl

private theorem orientedEdgeSignedDartEquiv_edge {Edge : Type*} (d : OrientedEdge Edge) :
    (orientedEdgeSignedDartEquiv d).edge = d.edge :=
  signedDartOfOrientedEdge_edge d

end SurfaceCellComplex

namespace FiniteSurfaceTriangulation

open SurfaceCellComplex

variable {S : Type*} [TopologicalSpace S]

/-- Relabel an oriented triangulation edge by a signed `Fin` edge name. -/
noncomputable def finiteCyclicDartEquiv (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge ≃ SignedDart (Fin (Fintype.card T.Edge)) :=
  SurfaceCellComplex.orientedEdgeSignedDartEquiv.trans
    (SignedDart.mapEquiv (Fintype.equivFin T.Edge))

@[simp]
theorem edgeOfDart_finiteCyclicDartEquiv
    (T : FiniteSurfaceTriangulation S) (d : OrientedEdge T.Edge) :
    FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
      Fintype.equivFin T.Edge d.edge := by
  cases d <;> rfl

/-- Enumerate the faces and unoriented edges of a finite triangulation and retain its cyclic
signed triangle boundaries. -/
@[reducible]
noncomputable def toFiniteCyclicPresentation (T : FiniteSurfaceTriangulation S) :
    FiniteCyclicPresentation where
  edgeCount := Fintype.card T.Edge
  faces :=
    List.ofFn fun f : Fin (Fintype.card T.Triangle) =>
      (T.triangleBoundary ((Fintype.equivFin T.Triangle).symm f)).map
        T.finiteCyclicDartEquiv

theorem toFiniteCyclicPresentation_faces_length (T : FiniteSurfaceTriangulation S) :
    T.toFiniteCyclicPresentation.faces.length = Fintype.card T.Triangle := by
  simp [toFiniteCyclicPresentation]

/-- The original unoriented edge names are equivalent to the enumerated presentation edges. -/
noncomputable def finiteCyclicEdgeEquiv (T : FiniteSurfaceTriangulation S) :
    T.Edge ≃ T.toFiniteCyclicPresentation.Edge := by
  change T.Edge ≃ Fin (Fintype.card T.Edge)
  exact Fintype.equivFin T.Edge

theorem edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv
    (T : FiniteSurfaceTriangulation S) (d : OrientedEdge T.Edge) :
    FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
      T.finiteCyclicEdgeEquiv d.edge := by
  change FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
    Fintype.equivFin T.Edge d.edge
  exact T.edgeOfDart_finiteCyclicDartEquiv d

/-- The original triangles are equivalent to positions in the presentation's face list. -/
noncomputable def finiteCyclicFaceEquiv (T : FiniteSurfaceTriangulation S) :
    T.Triangle ≃ T.toFiniteCyclicPresentation.Face :=
  (Fintype.equivFin T.Triangle).trans
    (Fin.castOrderIso T.toFiniteCyclicPresentation_faces_length.symm).toEquiv

@[simp]
theorem finiteCyclicFaceEquiv_apply_val (T : FiniteSurfaceTriangulation S)
    (f : T.Triangle) :
    (T.finiteCyclicFaceEquiv f).val = (Fintype.equivFin T.Triangle f).val :=
  rfl

@[simp]
theorem finiteCyclicFaceEquiv_symm_apply_val (T : FiniteSurfaceTriangulation S)
    (f : T.toFiniteCyclicPresentation.Face) :
    (Fintype.equivFin T.Triangle (T.finiteCyclicFaceEquiv.symm f)).val = f.val := by
  simp [finiteCyclicFaceEquiv]

/-- Reading an enumerated face gives exactly the relabeled original triangle boundary. -/
theorem toFiniteCyclicPresentation_boundary_faceEquiv
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) :
    T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f) =
      (T.triangleBoundary f).map T.finiteCyclicDartEquiv := by
  simp [FiniteCyclicPresentation.boundary, toFiniteCyclicPresentation,
    finiteCyclicFaceEquiv]

theorem toFiniteCyclicPresentation_boundary_faceEquiv_length
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) :
    (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).length =
      (T.triangleBoundary f).length := by
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
  simp

/-- Reading a position in an enumerated boundary is the same as reading the corresponding
position before relabeling and then relabeling its dart. -/
theorem toFiniteCyclicPresentation_boundary_faceEquiv_get
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle)
    (i : Fin
      (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).length) :
    (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).get i =
      T.finiteCyclicDartEquiv
        ((T.triangleBoundary f).get
          (Fin.cast (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f) i)) := by
  have key : ∀ L, L = (T.triangleBoundary f).map T.finiteCyclicDartEquiv →
      ∀ (j : Fin L.length) (hj : L.length = (T.triangleBoundary f).length),
        L.get j = T.finiteCyclicDartEquiv ((T.triangleBoundary f).get (Fin.cast hj j)) := by
    intro L hL j hj
    subst hL
    simp
  exact key _ (T.toFiniteCyclicPresentation_boundary_faceEquiv f) i _

/-- Original triangle-boundary positions are canonically the boundary occurrences of the
enumerated cyclic presentation. -/
noncomputable def finiteCyclicOccurrenceEquiv (T : FiniteSurfaceTriangulation S) :
    T.BoundaryPosition ≃
      (Σ f : T.toFiniteCyclicPresentation.Face,
        Fin (T.toFiniteCyclicPresentation.boundary f).length) :=
  Equiv.sigmaCongr T.finiteCyclicFaceEquiv fun f =>
    (Fin.castOrderIso
      (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f).symm).toEquiv

@[simp]
theorem finiteCyclicOccurrenceEquiv_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.finiteCyclicOccurrenceEquiv o).1 = T.finiteCyclicFaceEquiv o.1 :=
  rfl

theorem finiteCyclicOccurrenceEquiv_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.finiteCyclicOccurrenceEquiv o).2.val = o.2.val :=
  rfl

theorem finiteCyclicOccurrenceEquiv_dart
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.toFiniteCyclicPresentation.boundary
      (T.finiteCyclicOccurrenceEquiv o).1).get
        (T.finiteCyclicOccurrenceEquiv o).2 =
      T.finiteCyclicDartEquiv o.orientedEdge := by
  rcases o with ⟨f, i⟩
  change (T.toFiniteCyclicPresentation.boundary
      (T.finiteCyclicFaceEquiv f)).get
        (Fin.cast
          (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f).symm i) =
    T.finiteCyclicDartEquiv ((T.triangleBoundary f).get i)
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv_get]
  congr

/-- Number of occurrences of an original unoriented edge in one stored triangle boundary. -/
noncomputable def boundaryEdgeCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) : ℕ := by
  classical
  exact ((T.triangleBoundary f).map OrientedEdge.edge).count e

/-- Total number of boundary positions occupied by an original unoriented edge. -/
noncomputable def edgeOccurrenceCount
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e).card

private noncomputable def boundaryIndexCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (T.triangleBoundary f).length)).filter
    fun i => ((T.triangleBoundary f).get i).edge = e).card

/-- Relabeling a face and an edge does not change the number of times that edge occurs in the
face boundary. -/
@[simp]
theorem toFiniteCyclicPresentation_faceEdgeMultiplicity
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) :
    T.toFiniteCyclicPresentation.faceEdgeMultiplicity
        (T.finiteCyclicFaceEquiv f) (T.finiteCyclicEdgeEquiv e) =
      T.boundaryEdgeCount f e := by
  classical
  unfold boundaryEdgeCount
  change
    ((T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).map
      FiniteCyclicPresentation.edgeOfDart).count (Fintype.equivFin T.Edge e) =
        ((T.triangleBoundary f).map OrientedEdge.edge).count e
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
  have hmap :
      ((T.triangleBoundary f).map T.finiteCyclicDartEquiv).map
          FiniteCyclicPresentation.edgeOfDart =
        ((T.triangleBoundary f).map OrientedEdge.edge).map
          T.finiteCyclicEdgeEquiv := by
    simp [List.map_map, finiteCyclicEdgeEquiv]
  rw [hmap]
  exact List.count_map_of_injective
    ((T.triangleBoundary f).map OrientedEdge.edge)
    T.finiteCyclicEdgeEquiv T.finiteCyclicEdgeEquiv.injective e

private theorem boundaryIndex_card_eq_boundaryEdgeCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) :
    T.boundaryIndexCount f e = T.boundaryEdgeCount f e := by
  classical
  unfold boundaryIndexCount boundaryEdgeCount
  let v : List.Vector T.Edge (T.triangleBoundary f).length :=
    List.Vector.ofFn fun i => ((T.triangleBoundary f).get i).edge
  simpa [v, List.ofFn_comp'] using
    Fin.card_filter_univ_eq_vector_get_eq_count e v

private theorem sum_boundaryEdgeCount_eq_edgeOccurrenceCount
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) :
    (∑ f : T.Triangle, T.boundaryEdgeCount f e) = T.edgeOccurrenceCount e := by
  classical
  unfold edgeOccurrenceCount
  let allPositions : Finset T.BoundaryPosition :=
    (Finset.univ : Finset T.Triangle).sigma fun f =>
      (Finset.univ : Finset (Fin (T.triangleBoundary f).length))
  have hall : allPositions = Finset.univ := by
    ext o
    simp [allPositions]
  calc
    (∑ f : T.Triangle, T.boundaryEdgeCount f e) =
        ∑ f : T.Triangle,
          T.boundaryIndexCount f e := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact (T.boundaryIndex_card_eq_boundaryEdgeCount f e).symm
    _ = (allPositions.filter fun o => o.edge = e).card := by
      unfold boundaryIndexCount
      rw [show allPositions =
          (Finset.univ : Finset T.Triangle).sigma fun f =>
            (Finset.univ : Finset (Fin (T.triangleBoundary f).length)) by
        rfl]
      rw [← Finset.card_sigma]
      congr 1
      ext o
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    _ = ((Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e).card := by
      rw [hall]

/-- The total multiplicity of an enumerated edge is the cardinality of its original boundary
position fiber. -/
theorem toFiniteCyclicPresentation_edgeMultiplicity
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) :
    T.toFiniteCyclicPresentation.edgeMultiplicity (T.finiteCyclicEdgeEquiv e) =
      T.edgeOccurrenceCount e := by
  classical
  unfold FiniteCyclicPresentation.edgeMultiplicity
  calc
    (∑ f : T.toFiniteCyclicPresentation.Face,
        T.toFiniteCyclicPresentation.faceEdgeMultiplicity f
          (T.finiteCyclicEdgeEquiv e)) =
        ∑ f : T.Triangle,
          T.toFiniteCyclicPresentation.faceEdgeMultiplicity
            (T.finiteCyclicFaceEquiv f) (T.finiteCyclicEdgeEquiv e) := by
      exact (Fintype.sum_equiv T.finiteCyclicFaceEquiv _ _ fun _ => rfl).symm
    _ = ∑ f : T.Triangle,
        T.boundaryEdgeCount f e := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact T.toFiniteCyclicPresentation_faceEdgeMultiplicity f e
    _ = T.edgeOccurrenceCount e :=
      T.sum_boundaryEdgeCount_eq_edgeOccurrenceCount e

private theorem edgeOccurrenceCount_eq_one_or_two
    {T : FiniteSurfaceTriangulation S} (h : T.IncidenceCertificate) (e : T.Edge) :
    T.edgeOccurrenceCount e = 1 ∨ T.edgeOccurrenceCount e = 2 := by
  classical
  unfold edgeOccurrenceCount
  let occurrences :=
    (Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e
  obtain ⟨o, ho⟩ := h.edge_used e
  have homem : o ∈ occurrences := by
    simp [occurrences, ho]
  have hpos : 0 < occurrences.card :=
    Finset.card_pos.mpr ⟨o, homem⟩
  have hle : occurrences.card ≤ 2 := by
    by_contra hnot
    have hgt : 2 < occurrences.card := by
      omega
    obtain ⟨o₀, o₁, o₂, ho₀, ho₁, ho₂, h₀₁, h₀₂, h₁₂⟩ :=
      Finset.two_lt_card_iff.mp hgt
    have hedge₀ : o₀.edge = e := (Finset.mem_filter.mp ho₀).2
    have hedge₁ : o₁.edge = e := (Finset.mem_filter.mp ho₁).2
    have hedge₂ : o₂.edge = e := (Finset.mem_filter.mp ho₂).2
    rcases h.edge_valence_le_two e o₀ o₁ o₂ hedge₀ hedge₁ hedge₂ with
      h₀₁' | h₀₂' | h₁₂'
    · exact h₀₁ h₀₁'
    · exact h₀₂ h₀₂'
    · exact h₁₂ h₁₂'
  change occurrences.card = 1 ∨ occurrences.card = 2
  omega

private theorem triangleAdjacent_to_finiteCyclicFaceAdjacent
    (T : FiniteSurfaceTriangulation S) {f g : T.Triangle}
    (h : T.TriangleAdjacent f g) :
    T.toFiniteCyclicPresentation.FaceAdjacent
      (T.finiteCyclicFaceEquiv f) (T.finiteCyclicFaceEquiv g) := by
  rcases h with ⟨df, hdf, dg, hdg, hedge⟩
  refine ⟨T.finiteCyclicEdgeEquiv df.edge, ?_, ?_⟩
  · rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    rw [List.map_map, List.mem_map]
    exact ⟨df, hdf, T.edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv df⟩
  · rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    rw [List.map_map, List.mem_map]
    refine ⟨dg, hdg, ?_⟩
    change FiniteCyclicPresentation.edgeOfDart
      (T.finiteCyclicDartEquiv dg) = T.finiteCyclicEdgeEquiv df.edge
    rw [T.edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv, hedge]

/-- An incidence certificate and nonempty stored face boundaries give a valid finite cyclic
presentation. The boundary hypothesis is separate because the legacy certificate permits an
otherwise vacuous empty boundary. -/
theorem toFiniteCyclicPresentation_isSurfaceValid
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate)
    (hboundary : ∀ f, T.triangleBoundary f ≠ []) :
    T.toFiniteCyclicPresentation.IsSurfaceValid := by
  classical
  refine ⟨Nonempty.map T.finiteCyclicFaceEquiv h.triangle_nonempty, ?_, ?_, ?_⟩
  · intro f
    rw [← T.finiteCyclicFaceEquiv.apply_symm_apply f]
    rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    simpa using hboundary (T.finiteCyclicFaceEquiv.symm f)
  · intro f g hrot
    let f' := T.finiteCyclicFaceEquiv.symm f
    let g' := T.finiteCyclicFaceEquiv.symm g
    have hf : f = T.finiteCyclicFaceEquiv f' :=
      (T.finiteCyclicFaceEquiv.apply_symm_apply f).symm
    have hg : g = T.finiteCyclicFaceEquiv g' :=
      (T.finiteCyclicFaceEquiv.apply_symm_apply g).symm
    have hrot' :
        ((T.triangleBoundary f').map T.finiteCyclicDartEquiv).IsRotated
          ((T.triangleBoundary g').map T.finiteCyclicDartEquiv) := by
      rw [hf, hg, T.toFiniteCyclicPresentation_boundary_faceEquiv,
        T.toFiniteCyclicPresentation_boundary_faceEquiv] at hrot
      exact hrot
    have horiginal :
        (T.triangleBoundary f').IsRotated (T.triangleBoundary g') := by
      simpa only [List.map_map, Equiv.symm_comp_self, List.map_id] using
        hrot'.map T.finiteCyclicDartEquiv.symm
    have hfg : f' = g' := h.boundary_rotated_injective f' g' horiginal
    calc
      f = T.finiteCyclicFaceEquiv f' :=
        (T.finiteCyclicFaceEquiv.apply_symm_apply f).symm
      _ = T.finiteCyclicFaceEquiv g' := congrArg T.finiteCyclicFaceEquiv hfg
      _ = g := T.finiteCyclicFaceEquiv.apply_symm_apply g
  · intro e
    let e' := T.finiteCyclicEdgeEquiv.symm e
    have hmultiplicity :=
      T.toFiniteCyclicPresentation_edgeMultiplicity e'
    have hcard := edgeOccurrenceCount_eq_one_or_two h e'
    rw [T.finiteCyclicEdgeEquiv.apply_symm_apply e] at hmultiplicity
    exact hmultiplicity.symm ▸ hcard

/-- A dual-connected incidence certificate gives connectivity of the enumerated finite cyclic
presentation. -/
theorem toFiniteCyclicPresentation_isConnected
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toFiniteCyclicPresentation.IsConnected := by
  refine ⟨Nonempty.map T.finiteCyclicFaceEquiv h.triangle_nonempty, ?_⟩
  intro f g
  let f' := T.finiteCyclicFaceEquiv.symm f
  let g' := T.finiteCyclicFaceEquiv.symm g
  have hpath :
      Relation.ReflTransGen T.toFiniteCyclicPresentation.FaceAdjacent
        (T.finiteCyclicFaceEquiv f') (T.finiteCyclicFaceEquiv g') :=
    Relation.ReflTransGen.lift T.finiteCyclicFaceEquiv
      (fun _ _ hadj => T.triangleAdjacent_to_finiteCyclicFaceAdjacent hadj)
      f' g'
      (h.dual_connected f' g')
  simpa [f', g'] using hpath

end FiniteSurfaceTriangulation

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- The finite cyclic presentation underlying a geometric triangulation. -/
@[reducible] noncomputable def toFiniteCyclicPresentation (T : GeometricTriangulation S) :
    FiniteCyclicPresentation :=
  T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation

/-- Surface incidence makes the cyclic presentation of a geometric triangulation valid. -/
theorem toFiniteCyclicPresentation_isSurfaceValid
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsSurfaceValid := by
  apply T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_isSurfaceValid
    (T.incidenceCertificate_of_surfaceIncidence h)
  intro f
  change T.triangleBoundary f ≠ []
  exact List.ne_nil_of_length_pos
    (lt_of_lt_of_eq (by decide : 0 < 3) (T.triangleBoundary_length f).symm)

/-- Surface incidence makes the cyclic presentation of a geometric triangulation connected. -/
theorem toFiniteCyclicPresentation_isConnected
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsConnected :=
  T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_isConnected
    (T.incidenceCertificate_of_surfaceIncidence h)

/-- A geometric surface triangulation therefore supplies the valid, connected finite signed
cyclic presentation needed by the normal-form lane. -/
theorem toFiniteCyclicPresentation_valid_and_connected
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsSurfaceValid ∧
      T.toFiniteCyclicPresentation.IsConnected :=
  ⟨T.toFiniteCyclicPresentation_isSurfaceValid h,
    T.toFiniteCyclicPresentation_isConnected h⟩

end GeometricTriangulation

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The named finite cyclic presentation obtained by enumerating the Radó triangulation of a
compact connected Eval surface. -/
noncomputable def compactEvalSurfaceFiniteCyclicPresentation :
    FiniteCyclicPresentation :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation

/-- The finite cyclic presentation attached to a compact connected Eval surface is valid. -/
theorem compact_eval_surface_finiteCyclicPresentation_isSurfaceValid :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsSurfaceValid :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation_isSurfaceValid
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S)

/-- The finite cyclic presentation attached to a compact connected Eval surface is connected. -/
theorem compact_eval_surface_finiteCyclicPresentation_isConnected :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsConnected :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation_isConnected
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S)

include S

/-- The Eval hypotheses therefore supply a valid, connected finite cyclic presentation, which is
the input expected by the Gallier--Xu normal-form lane. -/
theorem compact_eval_surface_has_valid_connected_finiteCyclicPresentation :
    ∃ P : FiniteCyclicPresentation, P.IsSurfaceValid ∧ P.IsConnected :=
  ⟨compactEvalSurfaceFiniteCyclicPresentation S,
    compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S,
    compact_eval_surface_finiteCyclicPresentation_isConnected S⟩

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification20_block_05
/- END ClassificationOfSurfaces.FiniteCyclicTriangulation -/

/- BEGIN ClassificationOfSurfaces.SphereCarrierGeometry | 6242ea99633cee9fc8ce5f7d916fe24b6df176507def164d1cf640ca35a2f085 -/
section schottkyclassification20_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Disk geometry for the sphere carrier

The faithful sphere presentation glues two monogons with opposite boundary directions. This file
records the elementary disk geometry needed to map those two cells to opposite hemispheres:
complex conjugation is a self-homeomorphism of every indexed polygon cell, and on a monogon it
turns the reversed boundary parameter back into the forward parameter.

The indexed cells are also compact. The instance is transported through the existing
homeomorphism with the closed unit disk, keeping this fact tied to the actual polygon carrier.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- Complex conjugation as a self-homeomorphism of an indexed polygon cell. -/
noncomputable def conjHomeomorph (n : ℕ) : PolygonCell n ≃ₜ PolygonCell n where
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
theorem conjHomeomorph_apply (n : ℕ) (z : PolygonCell n) :
    (conjHomeomorph n z).val = conj z.val :=
  rfl

/-- On a monogon, conjugation changes the reversed boundary parameter into the forward one. -/
theorem conj_side_symm_monogon (t : unitInterval) :
    conj ((side (0 : Fin 1) (unitInterval.symm t) : PolygonCell 1).val) =
      (side (0 : Fin 1) t : PolygonCell 1).val := by
  change conj (Circle.exp (sideAngle (0 : Fin 1) (unitInterval.symm t)) : ℂ) =
    (Circle.exp (sideAngle (0 : Fin 1) t) : ℂ)
  rw [← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  simp only [sideAngle, Fin.val_zero, Nat.cast_one, div_one, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul, unitInterval.coe_symm_eq]
  ring

/-- Every indexed polygon cell is compact through its identification with the closed unit disk. -/
noncomputable instance (n : ℕ) : CompactSpace (PolygonCell n) :=
  (closedUnitDiscHomeomorph n).symm.compactSpace

end PolygonCell

end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification20_block_06
/- END ClassificationOfSurfaces.SphereCarrierGeometry -/

/- BEGIN ClassificationOfSurfaces.CanonicalCoordinates | 7498ad92994060f5d52ef64a9c68c6b00d86f4474eb3c5b9963b153bcf7bda98 -/
section schottkyclassification20_block_07
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Carrier coordinates for canonical normal-form words

This file computes the closed-disk boundary coordinates of every canonical word position.
It reconciles the canonical positive boundary-block ordering with the trusted Eval relations'
negative angles using `Fin.rev` and integral periodicity. The resulting theorems send each of the
five canonical pairing families into the corresponding trusted equivalence closure.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces.NormalForm

open Complex
open SurfaceCellComplex

/-- The point on occurrence `i` of the canonical orientable one-face presentation. -/
noncomputable def orientableOccurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    (orientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((orientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t

/-- The carrier bridge sends occurrence `i` to the boundary parameter `(i+t)/|word|`. -/
theorem orientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (orientableBoundaryWord p n).length) := by
  simpa [orientableCellComplex, orientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (orientableBoundaryWord p n) i t

theorem orientableCarrier_handle_a_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem orientableCarrier_handle_a_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

theorem orientableCarrier_handle_b_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem orientableCarrier_handle_b_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 4 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

theorem orientableCarrier_boundary_c_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem orientableCarrier_boundary_h_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem orientableCarrier_boundary_c_neg {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/-- Reversing a finite index converts its real value to `n - j - 1`. -/
theorem fin_rev_cast_real {n : ℕ} (j : Fin n) :
    ((Fin.rev j : Fin n) : ℝ) = n - (j : ℝ) - 1 := by
  rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_iff.mpr j.isLt)]
  push_cast
  ring

/-- Trusted boundary source `Fin.rev j` is the second canonical `cⱼ` side, modulo one turn. -/
theorem orientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) :=
      (orientableCarrier_boundary_c_neg j t).symm

/-- Trusted boundary target `Fin.rev j` is the first canonical `cⱼ` side, modulo one turn. -/
theorem orientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) :=
      (orientableCarrier_boundary_c_pos j t).symm

/-- Every canonical `aᵢ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_handle_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_a_pos, orientableCarrier_handle_a_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.a (n := n) t i)

/-- Every canonical `bᵢ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_handle_b_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_b_pos, orientableCarrier_handle_b_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.b (n := n) t i)

/-- Every canonical `cⱼ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t))) := by
  rw [← orientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← orientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (OrientableRel.c (p := p) t (Fin.rev j)))

/-- The point on occurrence `i` of the canonical nonorientable one-face presentation. -/
noncomputable def nonOrientableOccurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    (nonOrientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((nonOrientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t

/-- The nonorientable carrier bridge sends occurrence `i` to `(i+t)/|word|`. -/
theorem nonOrientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (nonOrientableBoundaryWord p n).length) := by
  simpa [nonOrientableCellComplex, nonOrientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (nonOrientableBoundaryWord p n) i t

theorem nonOrientableCarrier_crosscap_a_first
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem nonOrientableCarrier_crosscap_a_second
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem nonOrientableCarrier_boundary_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem nonOrientableCarrier_boundary_h_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

theorem nonOrientableCarrier_boundary_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/-- Trusted boundary source `Fin.rev j` is the second nonorientable `cⱼ` side. -/
theorem nonOrientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) :=
      (nonOrientableCarrier_boundary_c_neg j t).symm

/-- Trusted boundary target `Fin.rev j` is the first nonorientable `cⱼ` side. -/
theorem nonOrientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) :=
      (nonOrientableCarrier_boundary_c_pos j t).symm

/-- Every canonical crosscap pairing maps into the trusted nonorientable closure. -/
theorem nonOrientableCarrier_crosscap_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t)) := by
  rw [nonOrientableCarrier_crosscap_a_first,
    nonOrientableCarrier_crosscap_a_second]
  exact Relation.EqvGen.rel _ _ (NonOrientableRel.a (n := n) t i)

/-- Every canonical boundary-seam pairing maps into the trusted nonorientable closure. -/
theorem nonOrientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t))) := by
  rw [← nonOrientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← nonOrientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (NonOrientableRel.c (p := p) t (Fin.rev j)))

end LeanEval.Topology.ClassificationOfSurfaces.NormalForm
end schottkyclassification20_block_07
/- END ClassificationOfSurfaces.CanonicalCoordinates -/
