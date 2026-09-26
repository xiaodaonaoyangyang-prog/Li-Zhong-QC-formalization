/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionM_ClosedCurveOps
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Section N: K₃,₃ and Geometric Graph Constructions
## HOL Light: Section N (Lines 25409–28399)

Three-element type, K₃,₃ graph properties, line-segment arcs,
polar coordinate continuity, and the vertex-disk lemma.

### Key HOL Light results
- `three_t` = `Fin 3` (three-element type)
- K₃,₃ is a graph; isomorphism criterion for K₃,₃
- Line segments `segment ℝ x y` are simple arcs when `x ≠ y`
- Polar coordinate maps are continuous
- `degree_vertex_disk_ver2`: vertex-disk construction for planar graphs
-/

open Set Metric Real

noncomputable section

/-! ## Three-element type (three_t) -/

-- HOL Light's `three_t` is a type with exactly 3 elements.
-- We use `Fin 3` throughout.

/-- `Fin 3` is finite with cardinality 3.
    HOL Light: `thr_finite` (line 25481). -/
theorem fin3_card : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3

/-! ## Graph constructor projections (mk_graph_t) -/

-- In our formalization, `Graph V E` already has `.vertexSet`, `.edgeSet`,
-- `.inc` as fields. The HOL Light `graph_edge_mk_graph`, etc., are
-- just projections, which are definitionally true for our structure.
-- HOL Light: `graph_edge_mk_graph` (line 25519),
--            `graph_vertex_mk_graph` (line 25525),
--            `graph_inc_mk_graph` (line 25531).

/-! ## K₃,₃ properties -/

-- K₃,₃ was defined in SectionI. These are its properties.

/-- K₃,₃ is a valid graph.
    HOL Light: `k33_isgraph` (line 25540). -/
theorem K33_isGraph : K33.edgeSet.Nonempty :=
  ⟨{1, 10}, by simp [K33]⟩

/-! ## Line segments as simple arcs -/

/-- A line segment between distinct points is a simple arc.
    HOL Light: `mk_segment_simple_arc_end` (line 25854). -/
theorem segment_isSimpleArcEnd {x y : E2'} (hne : x ≠ y) :
    IsSimpleArcEnd (segment ℝ x y) x y := by
  refine ⟨fun t => (1 - t) • x + t • y, ?_, ?_, ?_, ?_, ?_⟩
  · ext z; simp only [Set.mem_image, Set.mem_Icc, mem_segment_iff_param]
    constructor
    · rintro ⟨t, ht0, ht1, rfl⟩
      exact ⟨1 - t, ⟨by linarith, by linarith⟩, by module⟩
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨1 - t, by linarith, by linarith, by module⟩
  · fun_prop
  · intro s hs t ht hst
    have key : (s - t) • (y - x) = (0 : E2') := by
      have h := sub_eq_zero.mpr hst
      rwa [show (1 - s) • x + s • y - ((1 - t) • x + t • y) =
        (s - t) • (y - x) from by module] at h
    rcases smul_eq_zero.mp key with h | h
    · linarith
    · exact absurd (eq_comm.mp (sub_eq_zero.mp h)) hne
  · change (1 - 0) • x + 0 • y = x; module
  · change (1 - 1) • x + 1 • y = y; module


/-! ## Subset / Mathlib wrappers -/

/-- Subset of either part implies subset of union.
    HOL Light: `in_union` (line 26195). -/
theorem subset_union_of_subset_left_or_right {α : Type*}
    {X Y Z : Set α} (h : X ⊆ Y ∨ X ⊆ Z) : X ⊆ Y ∪ Z := by
  rcases h with h | h
  · exact h.trans subset_union_left
  · exact h.trans subset_union_right

/-- An infinite set's superset is infinite.
    HOL Light: `infinite_subset` (line 27484). -/
theorem Set.Infinite.mono' {α : Type*} {X Y : Set α}
    (hX : X.Infinite) (hXY : X ⊆ Y) : Y.Infinite :=
  hX.mono hXY

/-- Open intervals are infinite.
    HOL Light: `infinite_interval` (line 27538). -/
theorem Ioo_infinite {a b : ℝ} (hab : a < b) :
    (Ioo a b).Infinite :=
  Set.Ioo_infinite hab

/-! ## Polar coordinates -/

/-- r • cis t is always in E2' (trivial in Lean).
    HOL Light: `polar_euclid` (line 26683). -/
theorem polar_mem_E2 (r t : ℝ) : r • cis t ∈ (univ : Set E2') :=
  mem_univ _

/-- Distance between collinear polar points.
    HOL Light: `d_euclid_eq_arg` (line 26970). -/
theorem dist_smul_cis (r r' x : ℝ) :
    dist (r • cis x) (r' • cis x) = |r - r'| := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have : ‖cis x‖ = 1 := by
    unfold cis; rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two, point, sq_abs]
  rw [this, mul_one]

/-- Polar coordinate construction is continuous.
    HOL Light: `polar_cont` (line 27023). -/
theorem continuous_polar {f g : ℝ → ℝ} {p : E2'}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => p + f t • cis (g t)) := by
  have hcis : Continuous cis := by
    change Continuous (fun x => point (Real.cos x, Real.sin x))
    unfold point
    exact continuous_induced_rng.mpr (continuous_pi (fun i => by
      fin_cases i <;>
        simp only [WithLp.equiv_symm_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
          Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        fun_prop))
  exact continuous_const.add (hf.smul (hcis.comp hg))

/-! ## cis at specific angles -/

/-- cis 0 = e₁ = (1, 0).
    HOL Light: `cis0` (line 26000). -/
theorem cis_zero : cis 0 = point (1, 0) := by simp [cis]

/-- cis(π/2) = e₂ = (0, 1).
    HOL Light: `cispi2` (line 26008). -/
theorem cis_pi_div_two : cis (π / 2) = point (0, 1) := by
  ext i; fin_cases i <;>
  simp [cis, point_coord_zero, point_coord_one]

/-- cis(π) = (-1, 0).
    HOL Light: `cispi` (line 26041). -/
theorem cis_pi : cis π = point (-1, 0) := by
  ext i; fin_cases i <;>
  simp [cis, point_coord_zero, point_coord_one]

/-- cis(3π/2) = (0, -1).
    HOL Light: `cis3pi2` (line 26055). -/
theorem cis_three_pi_div_two : cis (3 * π / 2) = point (0, -1) := by
  have h : 3 * π / 2 = π / 2 + π := by ring
  ext i; fin_cases i <;>
  simp [cis, point_coord_zero, point_coord_one, h]

/-! ## Hyperplane definition (moved from Section O for use in degree4_vertex_hv) -/

/-- A hyperplane in E2' along coordinate `k` at value `c`.
    HOL Light: `hyperplane 2 ek (p k)` throughout Section N. -/
def hyperplane2 (k : Fin 2) (c : ℝ) : Set E2' := {x | x k = c}

/-! ## cis at axis angles has a zero coordinate -/

/-- For i < 4, cis(i * π / 2) has either coordinate 0 or coordinate 1 equal to 0.
    This is the key fact that makes mk_segment land in the hyperplane cross. -/
private theorem cis_axis_zero_coord (i : ℕ) (hi : i < 4) :
    (cis (↑i * π / 2)) 0 = 0 ∨ (cis (↑i * π / 2)) 1 = 0 := by
  interval_cases i
  · -- i = 0: cis 0 = (1, 0), so coordinate 1 is 0
    right; simp [cis, point_coord_one]
  · -- i = 1: cis(π/2) = (0, 1), so coordinate 0 is 0
    left; simp [cis, point_coord_zero]
  · -- i = 2: cis(π) = (-1, 0), so coordinate 1 is 0
    right; simp [cis, point_coord_one, show (2 : ℝ) * π / 2 = π from by ring]
  · -- i = 3: cis(3π/2) = (0, -1), so coordinate 0 is 0
    left; simp [cis, point_coord_zero, show (3 : ℝ) * π / 2 = π / 2 + π from by ring]

/-! ## Segment in hyperplane cross -/

/-- segment ℝ between p and p + r • cis(i·π/2) lies in the hyperplane cross.
    HOL Light: `mk_segment_hyperplane` (line 26193).
    Key insight: cis(i·π/2) is an axis vector — its other coordinate is 0,
    so the segment stays on one of the two axis-aligned hyperplanes through p. -/
theorem segment_hyperplane {p : E2'} {r : ℝ} {i : ℕ}
    (hi : i < 4) (_hr : 0 < r) :
    segment ℝ p (p + r • cis (↑i * π / 2)) ⊆
      hyperplane2 1 (p 1) ∪ hyperplane2 0 (p 0) := by
  intro z hz
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hz
  simp only [hyperplane2, Set.mem_union, Set.mem_setOf_eq]
  -- z = t • p + (1 - t) • (p + r • cis(i·π/2)) = p + (1-t) • r • cis(i·π/2)
  -- so z k = p k + (1-t) * r * cis(i·π/2) k
  have key : ∀ (k : Fin 2), (t • p + (1 - t) • (p + r • cis (↑i * π / 2))) k =
      p k + (1 - t) * r * (cis (↑i * π / 2)) k := by
    intro k
    have heq : t • p + (1 - t) • (p + r • cis (↑i * π / 2)) =
        p + ((1 - t) * r) • cis (↑i * π / 2) := by module
    change (t • p + (1 - t) • (p + r • cis (↑i * π / 2))) k =
        (p + ((1 - t) * r) • cis (↑i * π / 2)) k
    rw [heq]
  rcases cis_axis_zero_coord i hi with h0 | h1
  · right; rw [key 0, h0]; ring
  · left; rw [key 1, h1]; ring

/-! ## Norm of cis and polar nonzero -/

/-- cis t ≠ 0.
    HOL Light: `cis_nz` (line 26475). -/
theorem cis_ne_zero (t : ℝ) : cis t ≠ 0 := by
  intro h
  have := norm2_cis t
  rw [norm2, h, norm_zero] at this
  linarith

/-- r • cis t ≠ 0 when r ≠ 0.
    HOL Light: `polar_nz` (line 26486). -/
theorem smul_cis_ne_zero {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    r • cis t ≠ 0 := by
  intro h
  have := norm2_scale_cis r t
  rw [norm2, h, norm_zero, eq_comm, abs_eq_zero] at this
  exact hr this

/-! ## Distance from p to p + q -/

/-- dist p (p + r • cis t) = |r|.
    HOL Light: `d_euclidpq` (line 26505) specialized. -/
theorem dist_add_smul_cis (p : E2') (r t : ℝ) :
    dist p (p + r • cis t) = |r| := by
  rw [dist_eq_norm, show p - (p + r • cis t) = -(r • cis t) from by abel,
    norm_neg, norm_smul, Real.norm_eq_abs]
  have : ‖cis t‖ = 1 := by
    rw [← norm2, norm2_cis]
  rw [this, mul_one]

/-! ## Distance along a segment (parametric) -/

/-- Distance from p to a point on segment ℝ p q, parametrized.
    HOL Light: `d_euclid_mk_segment` (line 26281). -/
theorem dist_segment_param {p q : E2'} {a : ℝ}
    (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    dist p (a • p + (1 - a) • q) = (1 - a) * dist p q := by
  rw [dist_eq_norm]
  have : p - (a • p + (1 - a) • q) = (1 - a) • (p - q) := by module
  rw [this, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - a),
    ← dist_eq_norm]

/-! ## Segment endpoint uniqueness -/

/-- If p ≠ q and z is on segment ℝ p q at distance ≥ dist p q from p,
    then z = q.
    HOL Light: `mk_segment_eq` (line 26306). -/
theorem segment_eq_endpoint {p q z : E2'} (hne : p ≠ q)
    (hz : z ∈ segment ℝ p q) (hdist : dist p q ≤ dist p z) : z = q := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hz
  rw [dist_segment_param ht0 ht1] at hdist
  have hpq : 0 < dist p q := dist_pos.mpr hne
  have h1t : 1 ≤ 1 - t := le_of_mul_le_mul_right (by linarith) hpq
  have : t = 0 := by linarith
  subst this; simp

/-- Intersection of segment ℝ p x and segment ℝ p y (with shared endpoint p,
    x ≠ y on the boundary) is just {p}, provided the non-shared endpoints
    lie at distance exactly r from p and segments stay inside ball.
    HOL Light: `mk_segment_endpoint` (line 26330). -/
theorem segment_inter_eq_origin {p x y : E2'} (hne : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y)
    (hdx : dist p x = dist p y)
    : segment ℝ p x ∩ segment ℝ p y = {p} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hmx, hmy⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hmx
    obtain ⟨s, hs0, hs1, heq⟩ := mem_segment_iff_param.mp hmy
    -- t • p + (1-t) • x = s • p + (1-s) • y
    have key : (1 - t) • (x - p) = (1 - s) • (y - p) := by
      have h2 := sub_eq_zero.mpr heq
      have : (1 - t) • (x - p) - (1 - s) • (y - p) = 0 := by
        rw [show (1 - t) • (x - p) - (1 - s) • (y - p) =
          t • p + (1 - t) • x - (s • p + (1 - s) • y) from by module]
        exact h2
      exact sub_eq_zero.mp this
    have hnorm : (1 - t) * ‖x - p‖ = (1 - s) * ‖y - p‖ := by
      have h := congr_arg norm key
      simp only [norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1-t),
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1-s)] at h
      exact h
    rw [← dist_eq_norm', ← dist_eq_norm', hdx] at hnorm
    have hts : t = s := by nlinarith [dist_pos.mpr hpy]
    rw [hts] at key
    by_cases h1t : s = 1
    · subst h1t; rw [hts]; module
    · have h1s : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1t)
      have hsub : (1 - s) • ((x - p) - (y - p)) = (0 : E2') := by
        rw [smul_sub, sub_eq_zero]; exact key
      have : (x - p) - (y - p) = (0 : E2') := by
        rcases smul_eq_zero.mp hsub with h | h
        · exact absurd h h1s
        · exact h
      have : x - y = (0 : E2') := by rwa [sub_sub_sub_cancel_right] at this
      exact absurd (sub_eq_zero.mp this) hne
  · rintro rfl
    exact ⟨mem_segment_iff_param.mpr ⟨1, zero_le_one, le_refl _, by module⟩,
           mem_segment_iff_param.mpr ⟨1, zero_le_one, le_refl _, by module⟩⟩

/-! ## Axis-point distinctness -/

/-- Center of a ball is not on the boundary (when r ≠ 0). -/
theorem center_ne_boundary {p : E2'} {r t : ℝ} (hr : r ≠ 0) :
    p ≠ p + r • cis t := by
  intro h
  have h' := sub_eq_zero.mpr h
  rw [show p - (p + r • cis t) = -(r • cis t) from by abel, neg_eq_zero] at h'
  exact smul_cis_ne_zero hr t h'

/-- cis values at distinct axis angles (multiples of π/2) are distinct.
    HOL Light: `cis_distinct` (line 26423). -/
private theorem cis_axis_distinct {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    cis (↑i * π / 2) ≠ cis (↑j * π / 2) := by
  intro h
  have h0c := congr_arg (· (0 : Fin 2)) h
  have h1c := congr_arg (· (1 : Fin 2)) h
  interval_cases i <;> interval_cases j <;> (try exact absurd rfl hij) <;>
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      show (2 : ℝ) * π / 2 = π from by ring,
      show 3 * π / 2 = π / 2 + π from by ring,
      cis, point_coord_zero, point_coord_one,
      Real.cos_zero, Real.sin_zero,
      Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.cos_pi, Real.sin_pi,
      Real.cos_add, Real.sin_add,
      mul_zero, zero_mul, one_mul, zero_div,
      sub_zero, add_zero] at h0c h1c <;>
    linarith

/-- Translated axis points are distinct.
    HOL Light: `cis_distinct` (line 26423) with offset. -/
theorem axis_point_ne {p : E2'} {r : ℝ} {i j : ℕ}
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) (hr : 0 < r) :
    p + r • cis (↑i * π / 2) ≠ p + r • cis (↑j * π / 2) := by
  intro h
  exact cis_axis_distinct hi hj hij
    ((smul_right_injective E2' (ne_of_gt hr)) (add_left_cancel h))

/-! ## Segment in closed ball from center to boundary point -/

/-- segment ℝ from p to a boundary point stays inside the closed ball.
    HOL Light: part of `degree4_vertex_hv` (line 26525). -/
theorem segment_subset_closedBall {p q : E2'} {r : ℝ} (hr : 0 < r) (hq : dist p q = r) :
    segment ℝ p q ⊆ closedBall p r := by
  intro z hz
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hz
  rw [mem_closedBall, dist_comm, dist_segment_param ht0 ht1, hq]
  nlinarith

/-- segment ℝ from p to a boundary point intersects the sphere only at the endpoint.
    HOL Light: part of `degree4_vertex_hv` (line 26525). -/
theorem segment_inter_sphere {p q : E2'} {r : ℝ}
    (hr : 0 < r) (hpq : p ≠ q) (hq : dist p q = r) :
    segment ℝ p q ∩ {x | r ≤ dist p x} = {q} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hmem, hdist⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hmem
    rw [dist_segment_param ht0 ht1, hq] at hdist
    have : t = 0 := by nlinarith
    subst this; simp
  · rintro rfl
    exact ⟨mem_segment_iff_param.mpr ⟨0, le_refl _, zero_le_one, by module⟩, by rw [hq]⟩

/-! ## Construction of 4 axis-aligned radial segments -/

/-- 4 axis-aligned radial segments from center p.
    HOL Light: `degree4_vertex_hv` (line 26525). -/
theorem degree4_vertex_hv {r : ℝ} {p : E2'} (hr : 0 < r) :
    ∃ C : ℕ → Set E2',
      (∀ i, i < 4 → IsSimpleArcEnd (C i) p (p + r • cis (↑i * π / 2))) ∧
      (∀ i, i < 4 → C i = segment ℝ p (p + r • cis (↑i * π / 2))) ∧
      (∀ i j, i < 4 → j < 4 → i ≠ j → C i ∩ C j = {p}) ∧
      (∀ i, i < 4 → C i ∩ {x | r ≤ dist p x} =
        {p + r • cis (↑i * π / 2)}) ∧
      (∀ i, i < 4 → C i ⊆ closedBall p r) ∧
      (∀ i, i < 4 → C i ⊆ hyperplane2 1 (p 1) ∪ hyperplane2 0 (p 0)) := by
  refine ⟨fun i => segment ℝ p (p + r • cis (↑i * π / 2)),
    ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · -- IsSimpleArcEnd
    intro i _
    exact segment_isSimpleArcEnd (center_ne_boundary (ne_of_gt hr))
  · -- Pairwise intersection = {p}
    intro i j hi hj hij
    exact segment_inter_eq_origin (axis_point_ne hi hj hij hr)
      (center_ne_boundary (ne_of_gt hr))
      (center_ne_boundary (ne_of_gt hr))
      (by rw [dist_add_smul_cis, dist_add_smul_cis])
  · -- Intersection with sphere = {endpoint}
    intro i _
    exact segment_inter_sphere hr (center_ne_boundary (ne_of_gt hr))
      (by rw [dist_add_smul_cis, abs_of_pos hr])
  · -- Subset of closed ball
    intro i _
    exact segment_subset_closedBall hr
      (by rw [dist_add_smul_cis, abs_of_pos hr])
  · -- Subset of hyperplane cross
    intro i hi
    exact segment_hyperplane hi hr

/-! ## Segment path (linear interpolation of reals) -/

/-- Linear interpolation between two reals.
    HOL Light: `segpath` (line 27455). -/
def segpath (x y : ℝ) (t : ℝ) : ℝ := t * x + (1 - t) * y

/-- segpath endpoints.
    HOL Light: `segpath_end` (line 27527). -/
theorem segpath_end (x y : ℝ) : segpath x y 0 = y ∧ segpath x y 1 = x := by
  constructor <;> simp [segpath]

/-- segpath is continuous.
    HOL Light: part of `segpath_lemma` (line 27475). -/
theorem segpath_continuous (x y : ℝ) : Continuous (segpath x y) := by
  unfold segpath; fun_prop

/-- segpath preserves bounds on [0,1].
    HOL Light: part of `segpath_lemma` (line 27475). -/
theorem segpath_range {x y b : ℝ} (hx : 0 ≤ x) (hxb : x < b)
    (hy : 0 ≤ y) (hyb : y < b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ segpath x y t ∧ segpath x y t < b := by
  simp only [segpath]
  constructor
  · nlinarith
  · rcases eq_or_lt_of_le ht0 with rfl | ht_pos
    · simp; linarith
    · have : t * x < t * b := mul_lt_mul_of_pos_left hxb ht_pos
      have : (1 - t) * y ≤ (1 - t) * b :=
        mul_le_mul_of_nonneg_left (le_of_lt hyb) (by linarith)
      linarith [show t * b + (1 - t) * b = b from by ring]

/-- segpath is injective when x ≠ y.
    HOL Light: `segpath_inj` (line 27536). -/
theorem segpath_injective {x y : ℝ} (hne : x ≠ y) :
    Function.Injective (segpath x y) := by
  intro a b hab
  simp only [segpath] at hab
  have : (a - b) * (x - y) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd (sub_eq_zero.mp h) hne

/-- segpath separates distinct ordered pairs.
    HOL Light: part of `segpath_lemma` (line 27475). -/
theorem segpath_distinct {x x' y y' t : ℝ}
    (hx : x < x') (hy : y < y') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segpath x y t ≠ segpath x' y' t := by
  simp only [segpath]
  intro h
  have : 0 < t * (x' - x) + (1 - t) * (y' - y) := by
    rcases eq_or_lt_of_le ht0 with rfl | ht_pos
    · simp; linarith
    · have : 0 < t * (x' - x) := mul_pos ht_pos (by linarith)
      have : 0 ≤ (1 - t) * (y' - y) := mul_nonneg (by linarith) (by linarith)
      linarith
  linarith

/-! ## Spiral-arc parametrization and curve lemmas -/

/-- The spiral-arc parametrization used in degree_vertex_annulus.
    Maps t ∈ [0,1] to a point in the annulus around p. -/
def curvePath (p : E2') (r : ℝ) (g : ℝ → ℝ) (t : ℝ) : E2' :=
  p + (t * r + (1 - t) * (r / 2)) • cis (g t)

/-- Spiral arc image stays in the annulus.
    HOL Light: `curve_annulus_lemma` (line 27253). -/
theorem curve_annulus_lemma {r : ℝ} {g : ℝ → ℝ} {p : E2'} (hr : 0 < r)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    r / 2 ≤ dist p (curvePath p r g t) ∧
    dist p (curvePath p r g t) ≤ r := by
  simp only [curvePath, dist_add_smul_cis]
  have h_coeff : 0 ≤ t * r + (1 - t) * (r / 2) := by nlinarith
  rw [abs_of_nonneg h_coeff]
  constructor <;> nlinarith

/-- Spiral arc intersects inner circle only at starting point.
    HOL Light: `curve_circle_lemma` (line 27304). -/
theorem curve_circle_lemma {r : ℝ} {g : ℝ → ℝ} {p : E2'} (hr : 0 < r) :
    (curvePath p r g) '' Icc 0 1 ∩ {x | dist p x ≤ r / 2} =
      {p + (r / 2) • cis (g 0)} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq,
    Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hdist⟩
    simp only [curvePath, dist_add_smul_cis] at hdist
    have h_coeff : 0 ≤ t * r + (1 - t) * (r / 2) := by nlinarith
    rw [abs_of_nonneg h_coeff] at hdist
    have ht0' : t = 0 := by nlinarith
    subst ht0'; simp [curvePath]
  · rintro rfl
    exact ⟨⟨0, ⟨le_refl _, zero_le_one⟩, by simp [curvePath]⟩,
      by rw [dist_add_smul_cis, abs_of_pos (by linarith)]⟩

/-- Spiral arc is a simple arc (image of continuous injective map).
    HOL Light: `curve_simple_lemma` (line 27378). -/
theorem curve_simple_lemma {r : ℝ} {g : ℝ → ℝ} {p : E2'} (hr : 0 < r)
    (hg : Continuous g) :
    IsSimpleArcEnd ((curvePath p r g) '' Icc 0 1)
      (p + (r / 2) • cis (g 0)) (p + r • cis (g 1)) := by
  refine ⟨curvePath p r g, rfl, ?_, ?_, ?_, ?_⟩
  · -- Continuity
    exact continuous_polar
      (by fun_prop : Continuous (fun t => t * r + (1 - t) * (r / 2))) hg
  · -- Injectivity on [0,1]
    intro s hs t ht heq
    simp only [curvePath] at heq
    have hcancel : (s * r + (1 - s) * (r / 2)) • cis (g s) =
        (t * r + (1 - t) * (r / 2)) • cis (g t) := by
      have := heq; rwa [add_left_cancel_iff] at this
    -- Take norms: |coeff(s)| = |coeff(t)|
    have hcs : 0 ≤ s * r + (1 - s) * (r / 2) := by nlinarith [hs.1, hs.2]
    have hct : 0 ≤ t * r + (1 - t) * (r / 2) := by nlinarith [ht.1, ht.2]
    have hnorm : s * r + (1 - s) * (r / 2) = t * r + (1 - t) * (r / 2) := by
      have h1 := norm2_scale_cis (s * r + (1 - s) * (r / 2)) (g s)
      have h2 := norm2_scale_cis (t * r + (1 - t) * (r / 2)) (g t)
      rw [hcancel] at h1; rw [h1] at h2
      rwa [abs_of_nonneg hcs, abs_of_nonneg hct] at h2
    -- coeff is injective: slope = r/2 > 0
    nlinarith
  · -- f 0 = v
    simp [curvePath]
  · -- f 1 = v'
    simp [curvePath]

/-! ## Annulus arcs (degree_vertex_annulus) -/

/-- n disjoint arcs in the annulus connecting inner to outer endpoints.
    HOL Light: `degree_vertex_annulus` (line 27570). -/
theorem degree_vertex_annulus {n : ℕ} {r : ℝ} {p : E2'} {xx zz : ℕ → ℝ}
    (hr : 0 < r)
    (hxx_range : ∀ j, j < n → 0 ≤ xx j ∧ xx j < 2 * π)
    (hzz_range : ∀ j, j < n → 0 ≤ zz j ∧ zz j < 2 * π)
    (hxx_strict : ∀ i j, i < j → j < n → xx i < xx j)
    (hzz_strict : ∀ i j, i < j → j < n → zz i < zz j) :
    ∃ C : ℕ → Set E2',
      (∀ i, i < n → IsSimpleArcEnd (C i)
        (p + (r / 2) • cis (zz i)) (p + r • cis (xx i))) ∧
      (∀ i j, i < n → j < n → i ≠ j → C i ∩ C j = ∅) ∧
      (∀ i, i < n → C i ⊆ {x | r / 2 ≤ dist p x ∧ dist p x ≤ r}) ∧
      (∀ i, i < n → C i ∩ {x | dist p x ≤ r / 2} =
        {p + (r / 2) • cis (zz i)}) := by
  -- Define each arc as a curvePath with segpath angle interpolation
  refine ⟨fun i => curvePath p r (segpath (xx i) (zz i)) '' Icc 0 1,
    ?_, ?_, ?_, ?_⟩
  · -- Simple arc end with correct endpoints
    intro i hi
    have hse := segpath_end (xx i) (zz i)
    convert curve_simple_lemma (p := p) hr (segpath_continuous (xx i) (zz i))
      using 2 <;> [rw [hse.1]; rw [hse.2]]
  · -- Disjointness
    intro i j hi hj hij
    ext z; simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩ ⟨t, ⟨ht0, ht1⟩, heq⟩
    -- Cancel p from both sides
    unfold curvePath at heq
    have hcancel : (s * r + (1 - s) * (r / 2)) • cis (segpath (xx i) (zz i) s) =
        (t * r + (1 - t) * (r / 2)) • cis (segpath (xx j) (zz j) t) :=
      add_left_cancel heq.symm
    -- Take norms to get coefficient equality
    have hcs : 0 < s * r + (1 - s) * (r / 2) := by nlinarith
    have hct : 0 < t * r + (1 - t) * (r / 2) := by nlinarith
    have hcoeff : s * r + (1 - s) * (r / 2) = t * r + (1 - t) * (r / 2) := by
      have h1 := norm2_scale_cis (s * r + (1 - s) * (r / 2)) (segpath (xx i) (zz i) s)
      have h2 := norm2_scale_cis (t * r + (1 - t) * (r / 2)) (segpath (xx j) (zz j) t)
      rw [hcancel] at h1; rw [h1] at h2
      rwa [abs_of_nonneg (le_of_lt hcs), abs_of_nonneg (le_of_lt hct)] at h2
    -- Coefficient is injective → s = t
    have hst : s = t := by nlinarith
    subst hst
    -- Now cis values are equal
    have hcis_eq : cis (segpath (xx i) (zz i) s) =
        cis (segpath (xx j) (zz j) s) := by
      have hne : (s * r + (1 - s) * (r / 2)) ≠ 0 := ne_of_gt hcs
      have := congr_arg ((s * r + (1 - s) * (r / 2))⁻¹ • ·) hcancel
      simp only [inv_smul_smul₀ hne] at this; exact this
    -- segpath values are in [0, 2π), use polar_inj for angle equality
    have hgi := segpath_range (hxx_range i hi).1 (hxx_range i hi).2
        (hzz_range i hi).1 (hzz_range i hi).2 hs0 hs1
    have hgj := segpath_range (hxx_range j hj).1 (hxx_range j hj).2
        (hzz_range j hj).1 (hzz_range j hj).2 hs0 hs1
    have hangle : segpath (xx i) (zz i) s = segpath (xx j) (zz j) s := by
      have hpi := polar_inj (le_of_lt (zero_lt_one (α := ℝ)))
          (le_of_lt (zero_lt_one (α := ℝ)))
          (Set.mem_Ico.mpr ⟨hgi.1, hgi.2⟩) (Set.mem_Ico.mpr ⟨hgj.1, hgj.2⟩)
          (show (1 : ℝ) • cis (segpath (xx i) (zz i) s) =
                (1 : ℝ) • cis (segpath (xx j) (zz j) s) by simp [hcis_eq])
      rcases hpi with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h one_ne_zero
      · exact h
    -- But segpath_distinct gives a contradiction
    rcases Nat.lt_or_gt_of_ne hij with h_ij | h_ji
    · exact absurd hangle (segpath_distinct (hxx_strict i j h_ij hj)
        (hzz_strict i j h_ij hj) hs0 hs1)
    · exact absurd hangle.symm (segpath_distinct (hxx_strict j i h_ji hi)
        (hzz_strict j i h_ji hi) hs0 hs1)
  · -- Annulus subset
    intro i hi z hz
    simp only [Set.mem_image, Set.mem_Icc] at hz
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
    exact Set.mem_setOf.mpr (curve_annulus_lemma hr ht0 ht1)
  · -- Inner circle intersection
    intro i hi
    have hse := segpath_end (xx i) (zz i)
    have hcl := curve_circle_lemma (p := p) (g := segpath (xx i) (zz i)) hr
    rwa [hse.1] at hcl

/-! ## Full degree_vertex_disk (with angles, HOL Light version) -/

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: assembles rectilinear and annular arc pieces for 4 angles by combining
-- `degree4_vertex_hv` with `degree_vertex_annulus`; repeated `norm_num`/`linarith` discharges
-- on angle bounds and set containments accumulate to exceed the default budget.
/-- Full vertex-disk construction with hyperplane property.
    HOL Light: `degree_vertex_disk` (line 27699). -/
theorem degree_vertex_disk_angles {r : ℝ} {p : E2'} {xx : ℕ → ℝ}
    (hr : 0 < r)
    (hxx_range : ∀ j, j < 4 → 0 ≤ xx j ∧ xx j < 2 * π)
    (hxx_strict : ∀ i j, i < j → j < 4 → xx i < xx j) :
    ∃ C : ℕ → Set E2',
      (∀ i, i < 4 →
        (∃ C' C'' v, IsSimpleArcEnd C' p v ∧
          IsSimpleArcEnd C'' v (p + r • cis (xx i)) ∧
          C' ⊆ closedBall p (r / 2) ∧
          C' ∩ C'' = {v} ∧ C' ∪ C'' = C i) ∧
        IsSimpleArcEnd (C i) p (p + r • cis (xx i)) ∧
        C i ⊆ closedBall p r ∧
        C i ∩ closedBall p (r / 2) ⊆
          hyperplane2 1 (p 1) ∪ hyperplane2 0 (p 0)) ∧
      (∀ i j, i < 4 → j < 4 → i ≠ j → C i ∩ C j = {p}) := by
  -- Step 1: Get rectilinear arcs from degree4_vertex_hv at radius r/2
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  obtain ⟨C₁, hC₁arc, hC₁seg, hC₁inter, hC₁sphere, hC₁ball, hC₁hyp⟩ :=
    degree4_vertex_hv hr2
  -- Step 2: Get annular arcs from degree_vertex_annulus with zz j = j * π / 2
  have hzz_range : ∀ (j : ℕ), j < 4 →
      0 ≤ (j : ℝ) * π / 2 ∧ (j : ℝ) * π / 2 < 2 * π := by
    intro j hj
    refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg j) Real.pi_pos.le) (by norm_num), ?_⟩
    calc (j : ℝ) * π / 2 < 4 * π / 2 := by
          apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
          exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) Real.pi_pos
        _ = 2 * π := by ring
  have hzz_strict : ∀ (i j : ℕ), i < j → j < 4 →
      (i : ℝ) * π / 2 < (j : ℝ) * π / 2 := by
    intro i j hij _
    apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos
  obtain ⟨C₂, hC₂arc, hC₂disj, hC₂ann, hC₂circle⟩ :=
    degree_vertex_annulus (n := 4) (zz := fun (j : ℕ) => (j : ℝ) * π / 2)
      hr hxx_range hzz_range hxx_strict hzz_strict
  -- Step 3: Define composite arcs C i = C₁ i ∪ C₂ i
  -- C₁ i goes from p to p + (r/2) • cis(i * π/2)
  -- C₂ i goes from p + (r/2) • cis(i * π/2) to p + r • cis(xx i)
  refine ⟨fun i => C₁ i ∪ C₂ i, ?_, ?_⟩
  · -- First conjunct: all per-arc properties
    intro i hi
    have hC₁i := hC₁arc i hi
    have hC₂i := hC₂arc i hi
    -- The C₂ left endpoint matches C₁ right endpoint
    have hzz_eq : (fun (j : ℕ) => (j : ℝ) * π / 2) i = ↑i * π / 2 := rfl
    -- Intersection: C₁ i ∩ C₂ i = {v_i}
    have hint : C₁ i ∩ C₂ i = {p + (r / 2) • cis (↑i * π / 2)} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hz1, hz2⟩
        have hzd : dist p z ≤ r / 2 := by
          rw [dist_comm]; exact mem_closedBall.mp (hC₁ball i hi hz1)
        have hmem : z ∈ C₂ i ∩ {x | dist p x ≤ r / 2} := ⟨hz2, hzd⟩
        rw [hC₂circle i hi, Set.mem_singleton_iff] at hmem; exact hmem
      · intro heq; subst heq
        refine ⟨isSimpleArcEnd_mem_right hC₁i, ?_⟩
        convert isSimpleArcEnd_mem_left hC₂i using 2
    -- Per-arc properties
    refine ⟨⟨C₁ i, C₂ i, p + (r / 2) • cis (↑i * π / 2),
      hC₁i, ?_, hC₁ball i hi, hint, rfl⟩, ?_, ?_, ?_⟩
    · convert hC₂i using 2
    · exact isSimpleArcEnd_trans hC₁i (by convert hC₂i using 2) hint
    · apply Set.union_subset
      · exact (hC₁ball i hi).trans (closedBall_subset_closedBall (by linarith))
      · intro z hz; have := (hC₂ann i hi) hz
        exact mem_closedBall.mpr (by rw [dist_comm]; exact this.2)
    · intro z ⟨hz_union, hz_ball⟩
      rcases hz_union with hz1 | hz2
      · exact hC₁hyp i hi hz1
      · have hzd : dist p z ≤ r / 2 := by
          rw [dist_comm]; exact mem_closedBall.mp hz_ball
        have : z ∈ C₂ i ∩ {x | dist p x ≤ r / 2} := ⟨hz2, hzd⟩
        rw [hC₂circle i hi, Set.mem_singleton_iff] at this
        rw [this]; exact hC₁hyp i hi (isSimpleArcEnd_mem_right hC₁i)
  · -- Second conjunct: pairwise intersection = {p}
    intro i j hi hj hij
    ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hz_i, hz_j⟩
      by_cases hz_ball : z ∈ closedBall p (r / 2)
      · -- z in inner ball → in C₁ parts
        have hz1i : z ∈ C₁ i := by
          rcases hz_i with h | h
          · exact h
          · have hzd : dist p z ≤ r / 2 := by
              rw [dist_comm]; exact mem_closedBall.mp hz_ball
            have : z ∈ C₂ i ∩ {x | dist p x ≤ r / 2} := ⟨h, hzd⟩
            rw [hC₂circle i hi, Set.mem_singleton_iff] at this
            rw [this]; exact isSimpleArcEnd_mem_right (hC₁arc i hi)
        have hz1j : z ∈ C₁ j := by
          rcases hz_j with h | h
          · exact h
          · have hzd : dist p z ≤ r / 2 := by
              rw [dist_comm]; exact mem_closedBall.mp hz_ball
            have : z ∈ C₂ j ∩ {x | dist p x ≤ r / 2} := ⟨h, hzd⟩
            rw [hC₂circle j hj, Set.mem_singleton_iff] at this
            rw [this]; exact isSimpleArcEnd_mem_right (hC₁arc j hj)
        have := (hC₁inter i j hi hj hij).symm ▸ Set.mem_inter hz1i hz1j
        rwa [Set.mem_singleton_iff] at this
      · -- z not in inner ball → in C₂ parts → contradiction
        have hz2i : z ∈ C₂ i := by
          rcases hz_i with h | h
          · exact absurd (hC₁ball i hi h) hz_ball
          · exact h
        have hz2j : z ∈ C₂ j := by
          rcases hz_j with h | h
          · exact absurd (hC₁ball j hj h) hz_ball
          · exact h
        have habs := hC₂disj i j hi hj hij
        have hmem := Set.mem_inter hz2i hz2j
        rw [habs] at hmem; exact hmem.elim
    · intro heq; subst heq
      exact ⟨Set.mem_union_left _ (isSimpleArcEnd_mem_left (hC₁arc i hi)),
             Set.mem_union_left _ (isSimpleArcEnd_mem_left (hC₁arc j hj))⟩

/-- Center is in closed ball iff 0 ≤ r.
    HOL Light: `closed_ball2_center` (line 27338). -/
theorem mem_closedBall_self_iff {p : E2'} {r : ℝ} :
    p ∈ closedBall p r ↔ 0 ≤ r := by
  simp [mem_closedBall, dist_self]

/-! ## Cancellation (trivial in Lean) -/

/-- x = y + z ↔ x - y = z.
    HOL Light: `euclid_cancel1` (line 27371). -/
theorem eq_add_iff_sub_eq {x y z : E2'} :
    x = y + z ↔ x - y = z := by
  constructor
  · intro h; rw [h]; abel
  · intro h; rw [← h]; abel

/-- p + q = p + q' ↔ q = q'.
    HOL Light: `euclid_add_cancel` (line 27403). -/
theorem add_left_cancel_iff_E2 {p q q' : E2'} :
    p + q = p + q' ↔ q = q' := add_left_cancel_iff

/-! ## K₃,₃ isomorphism criterion -/

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: extracting distinct triples from `Finset.card = 3` and verifying
-- all 9 edge bijection conditions generates large `simp` goals on `Finset` membership.
/-- K₃,₃ isomorphism criterion: if sets A, B each have 3 elements,
    are disjoint, and E bijects onto A × B, the resulting graph is
    isomorphic to K₃,₃.
    HOL Light: `k33_iso` (line 25583). -/
theorem k33_iso {A B : Finset E2'} {E : Finset (Set E2')}
    {f : Set E2' → E2' × E2'}
    (hA : A.card = 3) (hB : B.card = 3)
    (hdisj : Disjoint (A : Set E2') B)
    (hbij : BijOn f (E : Set (Set E2')) (A ×ˢ B)) :
    GraphIsomorphic K33
      ⟨(A : Set E2') ∪ B, E, fun e => {(f e).1, (f e).2},
        fun e he => by
          have hmem := hbij.mapsTo he
          rw [Set.mem_prod] at hmem
          constructor
          · intro v hv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with rfl | rfl
            · exact Set.mem_union_left _ (Finset.mem_coe.mpr hmem.1)
            · exact Set.mem_union_right _ (Finset.mem_coe.mpr hmem.2)
          · have hne : (f e).1 ≠ (f e).2 := by
              intro heq
              have h1 := Finset.mem_coe.mpr hmem.1
              have h2 := Finset.mem_coe.mpr hmem.2
              rw [heq] at h1
              exact Set.disjoint_left.mp hdisj h1 h2
            rw [Set.ncard_eq_two]
            exact ⟨(f e).1, (f e).2, hne, rfl⟩⟩ := by
  -- Extract three elements from A and B
  obtain ⟨a₀, a₁, a₂, ha₀, ha₁, ha₂, ha01, ha02, ha12, hAeq⟩ :
      ∃ a₀ a₁ a₂, a₀ ∈ A ∧ a₁ ∈ A ∧ a₂ ∈ A ∧
        a₀ ≠ a₁ ∧ a₀ ≠ a₂ ∧ a₁ ≠ a₂ ∧ A = {a₀, a₁, a₂} := by
    rw [Finset.card_eq_three] at hA
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hA
    exact ⟨a, b, c, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)),
      hab, hac, hbc, rfl⟩
  obtain ⟨b₀, b₁, b₂, hb₀, hb₁, hb₂, hb01, hb02, hb12, hBeq⟩ :
      ∃ b₀ b₁ b₂, b₀ ∈ B ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        b₀ ≠ b₁ ∧ b₀ ≠ b₂ ∧ b₁ ≠ b₂ ∧ B = {b₀, b₁, b₂} := by
    rw [Finset.card_eq_three] at hB
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hB
    exact ⟨a, b, c, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)),
      hab, hac, hbc, rfl⟩
  -- Define the inverse of f
  set g := Function.invFunOn f (E : Set (Set E2'))
  have hg_right : ∀ p ∈ (A : Set E2') ×ˢ (B : Set E2'),
      f (g p) = p := hbij.surjOn.rightInvOn_invFunOn
  have hg_maps : ∀ p ∈ (A : Set E2') ×ˢ (B : Set E2'),
      g p ∈ (E : Set (Set E2')) :=
    hbij.surjOn.mapsTo_invFunOn
  have hg_left : ∀ e ∈ (E : Set (Set E2')), g (f e) = e :=
    hbij.injOn.leftInvOn_invFunOn
  -- Membership in A ×ˢ B
  have mem_prod : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ (A : Set E2') ×ˢ (B : Set E2') :=
    fun a ha b hb => ⟨Finset.mem_coe.mpr ha, Finset.mem_coe.mpr hb⟩
  -- Define vertex map: K33 vertices → E2'
  let u : ℕ → E2' := fun n =>
    if n = 1 then a₀ else if n = 2 then a₁ else if n = 3 then a₂
    else if n = 10 then b₀ else if n = 20 then b₁
    else if n = 30 then b₂ else a₀
  -- Define edge map via concrete pattern matching on K33 edges
  let v : Finset ℕ → Set E2' := fun e =>
    if e = {1, 10} then g (a₀, b₀)
    else if e = {2, 10} then g (a₁, b₀)
    else if e = {3, 10} then g (a₂, b₀)
    else if e = {1, 20} then g (a₀, b₁)
    else if e = {2, 20} then g (a₁, b₁)
    else if e = {3, 20} then g (a₂, b₁)
    else if e = {1, 30} then g (a₀, b₂)
    else if e = {2, 30} then g (a₁, b₂)
    else if e = {3, 30} then g (a₂, b₂)
    else ∅
  -- Precompute edge inequalities (avoids repeated `decide`)
  have he21 : ({2, 10} : Finset ℕ) ≠ {1, 10} := by decide
  have he31 : ({3, 10} : Finset ℕ) ≠ {1, 10} := by decide
  have he32 : ({3, 10} : Finset ℕ) ≠ {2, 10} := by decide
  have he41 : ({1, 20} : Finset ℕ) ≠ {1, 10} := by decide
  have he42 : ({1, 20} : Finset ℕ) ≠ {2, 10} := by decide
  have he43 : ({1, 20} : Finset ℕ) ≠ {3, 10} := by decide
  have he51 : ({2, 20} : Finset ℕ) ≠ {1, 10} := by decide
  have he52 : ({2, 20} : Finset ℕ) ≠ {2, 10} := by decide
  have he53 : ({2, 20} : Finset ℕ) ≠ {3, 10} := by decide
  have he54 : ({2, 20} : Finset ℕ) ≠ {1, 20} := by decide
  have he61 : ({3, 20} : Finset ℕ) ≠ {1, 10} := by decide
  have he62 : ({3, 20} : Finset ℕ) ≠ {2, 10} := by decide
  have he63 : ({3, 20} : Finset ℕ) ≠ {3, 10} := by decide
  have he64 : ({3, 20} : Finset ℕ) ≠ {1, 20} := by decide
  have he65 : ({3, 20} : Finset ℕ) ≠ {2, 20} := by decide
  have he71 : ({1, 30} : Finset ℕ) ≠ {1, 10} := by decide
  have he72 : ({1, 30} : Finset ℕ) ≠ {2, 10} := by decide
  have he73 : ({1, 30} : Finset ℕ) ≠ {3, 10} := by decide
  have he74 : ({1, 30} : Finset ℕ) ≠ {1, 20} := by decide
  have he75 : ({1, 30} : Finset ℕ) ≠ {2, 20} := by decide
  have he76 : ({1, 30} : Finset ℕ) ≠ {3, 20} := by decide
  have he81 : ({2, 30} : Finset ℕ) ≠ {1, 10} := by decide
  have he82 : ({2, 30} : Finset ℕ) ≠ {2, 10} := by decide
  have he83 : ({2, 30} : Finset ℕ) ≠ {3, 10} := by decide
  have he84 : ({2, 30} : Finset ℕ) ≠ {1, 20} := by decide
  have he85 : ({2, 30} : Finset ℕ) ≠ {2, 20} := by decide
  have he86 : ({2, 30} : Finset ℕ) ≠ {3, 20} := by decide
  have he87 : ({2, 30} : Finset ℕ) ≠ {1, 30} := by decide
  have he91 : ({3, 30} : Finset ℕ) ≠ {1, 10} := by decide
  have he92 : ({3, 30} : Finset ℕ) ≠ {2, 10} := by decide
  have he93 : ({3, 30} : Finset ℕ) ≠ {3, 10} := by decide
  have he94 : ({3, 30} : Finset ℕ) ≠ {1, 20} := by decide
  have he95 : ({3, 30} : Finset ℕ) ≠ {2, 20} := by decide
  have he96 : ({3, 30} : Finset ℕ) ≠ {3, 20} := by decide
  have he97 : ({3, 30} : Finset ℕ) ≠ {1, 30} := by decide
  have he98 : ({3, 30} : Finset ℕ) ≠ {2, 30} := by decide
  -- Helper: simplify v after case splitting on K33 edges
  -- Precompute vertex ≠ facts
  have hn21 : (2 : ℕ) ≠ 1 := by omega
  have hn31 : (3 : ℕ) ≠ 1 := by omega
  have hn32 : (3 : ℕ) ≠ 2 := by omega
  have hn101 : (10 : ℕ) ≠ 1 := by omega
  have hn102 : (10 : ℕ) ≠ 2 := by omega
  have hn103 : (10 : ℕ) ≠ 3 := by omega
  have hn201 : (20 : ℕ) ≠ 1 := by omega
  have hn202 : (20 : ℕ) ≠ 2 := by omega
  have hn203 : (20 : ℕ) ≠ 3 := by omega
  have hn2010 : (20 : ℕ) ≠ 10 := by omega
  have hn301 : (30 : ℕ) ≠ 1 := by omega
  have hn302 : (30 : ℕ) ≠ 2 := by omega
  have hn303 : (30 : ℕ) ≠ 3 := by omega
  have hn3010 : (30 : ℕ) ≠ 10 := by omega
  have hn3020 : (30 : ℕ) ≠ 20 := by omega
  -- Construct the isomorphism
  refine ⟨⟨u, v, ?_, ?_, ?_⟩⟩
  · -- vertexBij: BijOn u K33.vertexSet (↑A ∪ ↑B)
    constructor
    · -- mapsTo
      intro n hn
      simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff]
        at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [u, hAeq, hBeq]
    constructor
    · -- injOn
      intro n₁ hn₁ n₂ hn₂ heq
      simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff]
        at hn₁ hn₂
      have hdAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := by
        intro a haA b hbB hab
        exact absurd (hab ▸ Finset.mem_coe.mpr hbB)
          (Set.disjoint_left.mp hdisj (Finset.mem_coe.mpr haA))
      rcases hn₁ with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hn₂ with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [u, ite_true, ite_false, hn21, hn31, hn32,
          hn101, hn102, hn103, hn201, hn202, hn203, hn2010,
          hn301, hn302, hn303, hn3010, hn3020
        ] at heq ⊢ <;> (
        first
        | rfl
        | exact absurd heq ha01
        | exact absurd heq ha02
        | exact absurd heq ha12
        | exact absurd heq ha01.symm
        | exact absurd heq ha02.symm
        | exact absurd heq ha12.symm
        | exact absurd heq hb01
        | exact absurd heq hb02
        | exact absurd heq hb12
        | exact absurd heq hb01.symm
        | exact absurd heq hb02.symm
        | exact absurd heq hb12.symm
        | exact absurd heq (hdAB _ ha₀ _ hb₀)
        | exact absurd heq (hdAB _ ha₀ _ hb₁)
        | exact absurd heq (hdAB _ ha₀ _ hb₂)
        | exact absurd heq (hdAB _ ha₁ _ hb₀)
        | exact absurd heq (hdAB _ ha₁ _ hb₁)
        | exact absurd heq (hdAB _ ha₁ _ hb₂)
        | exact absurd heq (hdAB _ ha₂ _ hb₀)
        | exact absurd heq (hdAB _ ha₂ _ hb₁)
        | exact absurd heq (hdAB _ ha₂ _ hb₂)
        | exact absurd heq.symm (hdAB _ ha₀ _ hb₀)
        | exact absurd heq.symm (hdAB _ ha₀ _ hb₁)
        | exact absurd heq.symm (hdAB _ ha₀ _ hb₂)
        | exact absurd heq.symm (hdAB _ ha₁ _ hb₀)
        | exact absurd heq.symm (hdAB _ ha₁ _ hb₁)
        | exact absurd heq.symm (hdAB _ ha₁ _ hb₂)
        | exact absurd heq.symm (hdAB _ ha₂ _ hb₀)
        | exact absurd heq.symm (hdAB _ ha₂ _ hb₁)
        | exact absurd heq.symm (hdAB _ ha₂ _ hb₂))
    · -- surjOn
      intro x hx
      simp only [Set.mem_union] at hx
      rw [hAeq, hBeq] at hx
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with ((rfl | rfl | rfl) | (rfl | rfl | rfl))
      · exact ⟨1, by simp [K33], by simp [u]⟩
      · exact ⟨2, by simp [K33], by simp [u]⟩
      · exact ⟨3, by simp [K33], by simp [u]⟩
      · exact ⟨10, by simp [K33], by simp [u]⟩
      · exact ⟨20, by simp [K33], by simp [u]⟩
      · exact ⟨30, by simp [K33], by simp [u]⟩
  · -- edgeBij: BijOn v K33.edgeSet ↑E
    constructor
    · -- mapsTo
      intro e he
      simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff]
        at he
      rcases he with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
        simp only [v, ite_true, ite_false, he21, he31, he32,
          he41, he42, he43, he51, he52, he53, he54, he61,
          he62, he63, he64, he65, he71, he72, he73, he74,
          he75, he76, he81, he82, he83, he84, he85, he86,
          he87, he91, he92, he93, he94, he95, he96, he97,
          he98] <;>
        exact hg_maps _ (mem_prod _ ‹_› _ ‹_›)
    constructor
    · -- injOn: show v has a left inverse via f on K33.edgeSet
      -- Key: for each e ∈ K33.edgeSet, v e = g(pair(e)),
      -- so f(v e) = pair(e). Since pair is injective and
      -- f ∘ v = pair, v is injective.
      -- Define the pair map
      let pair : Finset ℕ → E2' × E2' := fun e =>
        if e = {1, 10} then (a₀, b₀)
        else if e = {2, 10} then (a₁, b₀)
        else if e = {3, 10} then (a₂, b₀)
        else if e = {1, 20} then (a₀, b₁)
        else if e = {2, 20} then (a₁, b₁)
        else if e = {3, 20} then (a₂, b₁)
        else if e = {1, 30} then (a₀, b₂)
        else if e = {2, 30} then (a₁, b₂)
        else if e = {3, 30} then (a₂, b₂)
        else (a₀, b₀)
      -- v = g ∘ pair on K33.edgeSet
      have hv_eq : ∀ e ∈ K33.edgeSet, v e = g (pair e) := by
        intro e he
        simp only [K33, Set.mem_insert_iff,
          Set.mem_singleton_iff] at he
        rcases he with rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;> rfl
      -- f(v e) = pair(e) for each K33 edge
      have hfv : ∀ e ∈ K33.edgeSet, f (v e) = pair e := by
        intro e he
        rw [hv_eq e he]
        have hpe : pair e ∈ (A : Set E2') ×ˢ (B : Set E2') := by
          simp only [K33, Set.mem_insert_iff,
            Set.mem_singleton_iff] at he
          rcases he with rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl <;>
            simp only [pair, ite_true, ite_false, he21, he31,
              he32, he41, he42, he43, he51, he52, he53, he54,
              he61, he62, he63, he64, he65, he71, he72, he73,
              he74, he75, he76, he81, he82, he83, he84, he85,
              he86, he87, he91, he92, he93, he94, he95, he96,
              he97, he98] <;>
            exact mem_prod _ ‹_› _ ‹_›
        exact hg_right _ hpe
      -- pair is injective on K33.edgeSet
      have hpair_inj : InjOn pair K33.edgeSet := by
        intro e₁ he₁ e₂ he₂ hpeq
        simp only [K33, Set.mem_insert_iff,
          Set.mem_singleton_iff] at he₁ he₂
        -- Deduce equality of first and second components
        have hdAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := by
          intro a haA b hbB hab
          exact absurd (hab ▸ Finset.mem_coe.mpr hbB)
            (Set.disjoint_left.mp hdisj
              (Finset.mem_coe.mpr haA))
        -- Extract component equalities
        have hfst := congr_arg Prod.fst hpeq
        have hsnd := congr_arg Prod.snd hpeq
        -- For each K33 edge, pair gives specific (aᵢ, bⱼ)
        -- Use component equalities + distinctness to conclude
        rcases he₁ with rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;>
          rcases he₂ with rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl <;>
          simp only [pair, ite_true, ite_false, he21, he31,
            he32, he41, he42, he43, he51, he52, he53, he54,
            he61, he62, he63, he64, he65, he71, he72, he73,
            he74, he75, he76, he81, he82, he83, he84, he85,
            he86, he87, he91, he92, he93, he94, he95, he96,
            he97, he98] at hfst hsnd ⊢ <;>
          first
          | rfl
          | (exfalso; exact ha01 hfst)
          | (exfalso; exact ha02 hfst)
          | (exfalso; exact ha12 hfst)
          | (exfalso; exact ha01 hfst.symm)
          | (exfalso; exact ha02 hfst.symm)
          | (exfalso; exact ha12 hfst.symm)
          | (exfalso; exact hb01 hsnd)
          | (exfalso; exact hb02 hsnd)
          | (exfalso; exact hb12 hsnd)
          | (exfalso; exact hb01 hsnd.symm)
          | (exfalso; exact hb02 hsnd.symm)
          | (exfalso; exact hb12 hsnd.symm)
      -- Now conclude: v is injective because f ∘ v = pair
      -- and pair is injective
      intro e₁ he₁ e₂ he₂ hveq
      exact hpair_inj he₁ he₂
        (by rw [← hfv _ he₁, ← hfv _ he₂, hveq])
    · -- surjOn
      intro e' he'
      have hfe := hbij.mapsTo he'
      rw [Set.mem_prod] at hfe
      obtain ⟨hfA, hfB⟩ := hfe
      rw [hAeq] at hfA; rw [hBeq] at hfB
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hfA hfB
      have hgl := hg_left _ he'  -- g (f e') = e'
      have hrw : ∀ (a b : E2'), (f e').1 = a → (f e').2 = b →
          g (a, b) = g (f e') := by
        intro a b h1 h2
        congr 1; exact Prod.ext h1.symm h2.symm
      rcases hfA with h1 | h1 | h1 <;> rcases hfB with h2 | h2 | h2
      -- 9 cases: provide K33 edge, membership, and v-image proof
      all_goals (simp only [v,] at *)
      · exact ⟨{1,10}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{1,20}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{1,30}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{2,10}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{2,20}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{2,30}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{3,10}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{3,20}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
      · exact ⟨{3,30}, by simp [K33], by rw [hrw _ _ h1 h2]; exact hgl⟩
  · -- preserves_inc
    intro e he
    simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff]
      at he
    rcases he with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      simp only [v, ite_true, ite_false, he21, he31, he32,
        he41, he42, he43, he51, he52, he53, he54, he61,
        he62, he63, he64, he65, he71, he72, he73, he74,
        he75, he76, he81, he82, he83, he84, he85, he86,
        he87, he91, he92, he93, he94, he95, he96, he97,
        he98, K33] <;> (
      rw [hg_right _ (mem_prod _ ‹_› _ ‹_›)]
      simp only [u,
        ]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_image, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨_, Or.inl rfl, rfl⟩
        · exact ⟨_, Or.inr rfl, rfl⟩
      · rintro ⟨n, rfl | rfl, rfl⟩ <;> simp)

/-! ## Finite set augmentation to sorted 4-tuple -/

/-- Augment a finite set of reals in [0, 2π) with at most 4 elements to a
    strictly increasing 4-element function covering the original set.
    HOL Light: `finite_augment` (line 28101) + `real_finite_increase` (line 20300). -/
private lemma finset_augment_sorted (S : Finset ℝ) (hcard : S.card ≤ 4)
    (hrange : ∀ a ∈ S, a ∈ Set.Ico (0 : ℝ) (2 * π)) :
    ∃ xx : ℕ → ℝ,
      (∀ j, j < 4 → 0 ≤ xx j ∧ xx j < 2 * π) ∧
      (∀ i j, i < j → j < 4 → xx i < xx j) ∧
      (∀ a ∈ S, ∃ k, k < 4 ∧ xx k = a) := by
  have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
  -- Step 1: Build a Finset T ⊇ S with T.card = 4 and T ⊆ Ico 0 (2π)
  have hcompl_inf : (Set.Ico (0 : ℝ) (2 * π) \ ↑S).Infinite :=
    (Set.Ico_infinite h2pi_pos).diff S.finite_toSet
  -- Extract 4 - S.card fresh elements from the complement
  obtain ⟨F, hF_sub, hF_fin, hF_ncard⟩ :=
    hcompl_inf.exists_subset_ncard_eq (4 - S.card)
  -- Convert F to a Finset
  set Ff := hF_fin.toFinset
  have hFf_card : Ff.card = 4 - S.card := by
    rw [← Set.ncard_eq_toFinset_card F hF_fin, hF_ncard]
  have hFf_disj : Disjoint S Ff := by
    rw [Finset.disjoint_left]
    intro a ha haf
    have : a ∈ F := hF_fin.mem_toFinset.mp haf
    have := hF_sub this
    exact (Set.mem_diff _).mp this |>.2 (Finset.mem_coe.mpr ha)
  set T := S ∪ Ff
  have hT_card : T.card = 4 := by
    rw [Finset.card_union_of_disjoint hFf_disj, hFf_card]; omega
  have hT_range : ∀ a ∈ T, a ∈ Set.Ico (0 : ℝ) (2 * π) := by
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · exact hrange a h
    · have := hF_sub (hF_fin.mem_toFinset.mp h)
      exact (Set.mem_diff _).mp this |>.1
  -- Step 2: Sort T using orderIsoOfFin
  set f := T.orderIsoOfFin hT_card
  refine ⟨fun i => if h : i < 4 then ↑(f ⟨i, h⟩) else 0, ?_, ?_, ?_⟩
  · -- Range: all values in [0, 2π)
    intro j hj
    simp only [dif_pos hj]
    exact hT_range _ (f ⟨j, hj⟩).2
  · -- Strictly increasing
    intro i j hij hj
    have hi : i < 4 := lt_trans hij hj
    simp only [dif_pos hi, dif_pos hj]
    exact f.strictMono hij
  · -- Covers S
    intro a ha
    have haT : a ∈ T := Finset.mem_union_left _ ha
    obtain ⟨k, hk⟩ : ∃ k : Fin 4, ↑(f k) = a := by
      obtain ⟨k, hk⟩ := f.surjective ⟨a, haT⟩
      exact ⟨k, congr_arg Subtype.val hk⟩
    exact ⟨k, k.2, by simp [k.2, hk]⟩

/-! ## Vertex-disk lemma -/

/-- The vertex-disk construction with hyperplane property.
    Constructs simple arcs from center to each boundary point, with
    inner/outer decomposition and the crucial hyperplane containment.
    HOL Light: `degree_vertex_disk_ver2` (line 28155). -/
theorem degree_vertex_disk {r : ℝ} {p : E2'} {X : Finset E2'}
    (hr : 0 < r) (hcard : X.card ≤ 4)
    (hX : ∀ x ∈ X, dist p x = r) :
    ∃ C : E2' → Set E2',
      (∀ i ∈ X,
        (∃ C' C'' v, IsSimpleArcEnd C' p v ∧
          IsSimpleArcEnd C'' v i ∧
          C' ⊆ closedBall p (r / 2) ∧
          C' ∩ C'' = {v} ∧ C' ∪ C'' = C i) ∧
        IsSimpleArcEnd (C i) p i ∧
        C i ⊆ closedBall p r ∧
        C i ∩ closedBall p (r / 2) ⊆
          hyperplane2 1 (p 1) ∪ hyperplane2 0 (p 0)) ∧
      (∀ i ∈ X, ∀ j ∈ X, i ≠ j → C i ∩ C j = {p}) := by
  -- Step 1: Points in X are distinct from p
  have hXne : ∀ x ∈ X, x ≠ p := by
    intro x hx heq; have := hX x hx; rw [heq, dist_self] at this; linarith
  -- Step 2: For each x ∈ X, represent x - p in polar coordinates
  -- and extract the angle. Since x = p + r • cis(angle), the angle
  -- determines x uniquely because r > 0 and angle ∈ [0, 2π).
  have hpolar : ∀ x ∈ X, ∃ t ∈ Set.Ico (0 : ℝ) (2 * π),
      x = p + r • cis t := by
    intro x hx
    obtain ⟨s, t, ht, hs, heq⟩ := polar_exist (x - p)
    refine ⟨t, ht, ?_⟩
    have hxp : x - p = s • cis t := heq
    have hsr : s = r := by
      have hdist := hX x hx
      rw [dist_comm] at hdist
      rw [dist_eq_norm, hxp, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs, ← norm2, norm2_cis, mul_one] at hdist
      linarith
    rw [hsr, sub_eq_iff_eq_add] at heq; rw [add_comm] at heq; exact heq
  -- Step 3: Define angle function (non-dependent) using classical choice
  -- For x ∉ X, angle x is arbitrary (say 0).
  set angle : E2' → ℝ := fun x =>
    if h : x ∈ X then (hpolar x h).choose else 0
  have hangle_range : ∀ x ∈ X, 0 ≤ angle x ∧ angle x < 2 * π := by
    intro x hx
    simp only [angle, dif_pos hx]
    exact ((hpolar x hx).choose_spec.1)
  have hangle_eq : ∀ x ∈ X, x = p + r • cis (angle x) := by
    intro x hx
    simp only [angle, dif_pos hx]
    exact (hpolar x hx).choose_spec.2
  -- Angle is injective on X
  have hangle_inj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → angle x ≠ angle y := by
    intro x hx y hy hxy hab
    exact hxy (by rw [hangle_eq x hx, hangle_eq y hy, hab])
  -- Step 4: Build sorted 4-element sequence containing all angles of X
  -- Since |X| ≤ 4 and angles are distinct reals in [0, 2π),
  -- we can augment to exactly 4 strictly increasing values.
  set AX := X.image angle
  have hAX_card : AX.card ≤ 4 := (Finset.card_image_le).trans hcard
  have hAX_range : ∀ a ∈ AX, a ∈ Set.Ico (0 : ℝ) (2 * π) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact Set.mem_Ico.mpr (hangle_range x hx)
  obtain ⟨xx, hxx_range, hxx_strict, hxx_cover_AX⟩ :=
    finset_augment_sorted AX hAX_card hAX_range
  have hxx_cover : ∀ x ∈ X, ∃ k, k < 4 ∧ xx k = angle x :=
    fun x hx => hxx_cover_AX (angle x) (Finset.mem_image_of_mem _ hx)
  -- Step 5: Apply degree_vertex_disk_angles
  obtain ⟨C₀, hC₀_props, hC₀_inter⟩ :=
    degree_vertex_disk_angles hr hxx_range hxx_strict
  -- Step 6: For each x ∈ X, find its index k with xx k = angle x,
  -- then C₀ k is a simple arc from p to p + r • cis(xx k) = x.
  refine ⟨fun x => if hx : x ∈ X then
    C₀ (hxx_cover x hx).choose
    else ∅, ?_, ?_⟩
  · -- Per-arc properties
    intro i hi
    simp only [dif_pos hi]
    set k := (hxx_cover i hi).choose with hk_def
    have hk := (hxx_cover i hi).choose_spec
    have hk_lt : k < 4 := hk.1
    have hk_eq : xx k = angle i := hk.2
    have hi_eq : i = p + r • cis (xx k) := by
      rw [hk_eq]; exact hangle_eq i hi
    obtain ⟨hdecomp, harc, hball, hhyp⟩ := hC₀_props k hk_lt
    constructor
    · obtain ⟨C', C'', v, hC', hC'', hC'sub, hint, hunion⟩ := hdecomp
      exact ⟨C', C'', v, hC', hi_eq ▸ hC'', hC'sub, hint, hunion⟩
    constructor
    · exact hi_eq ▸ harc
    exact ⟨hball, hhyp⟩
  · -- Pairwise intersection
    intro i hi j hj hij
    simp only [dif_pos hi, dif_pos hj]
    have hki := (hxx_cover i hi).choose_spec
    have hkj := (hxx_cover j hj).choose_spec
    have hkij : (hxx_cover i hi).choose ≠ (hxx_cover j hj).choose := by
      intro heq
      apply hij
      rw [hangle_eq i hi, hangle_eq j hj]
      congr 1; congr 1
      rw [← hki.2, ← hkj.2, heq]
    exact hC₀_inter _ _ hki.1 hkj.1 hkij

end
