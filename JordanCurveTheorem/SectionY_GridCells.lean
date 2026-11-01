/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionX_RationalApprox

/-!
# Section Y: Grid Cells and Planar Graph Rectagonality
## HOL Light: Section Y (Lines 46343–48689)

Edge containment in balls, integer point separation, decomposition of arcs into
finitely many segments through integer points, and the main theorem that every
planar graph with bounded degree is rectagonal.

### Key results
- `h_edge_ball`, `v_edge_ball`: edges contained in open balls of radius ½
- `h_edge_closed_ball`, `v_edge_closed_ball`: uniqueness from closed-ball intersection
- `connected_in_edge`: connected subsets of edge union lie in a single edge
- `d_euclid_pointI_pos`: integer points within distance < 1 are equal
- `simple_arc_finite_pointI`: arcs meet finitely many integer points
- `simple_arc_finite_lemma1`–`simple_arc_finite_lemma4`: arc decomposition
- `simple_arc_end_edge_closure`, `simple_arc_end_edge_full_closure`: endpoint closure
- `order_lt_imp_psegment`: strict-order edges form a psegment
- `planar_graph_rectagonal`: **Main theorem** — planar + finite + deg ≤ 4 → rectagonal
- `k33_nonplanar`: K₃,₃ is not planar

### HOL Light definitions translated here
- `mk_segment_vc`, `mk_segment_hc`: segment = closed vertical/horizontal edge
- `vc_edge`, `hc_edge`: closed vertical/horizontal edges
-/

namespace JordanCurveTheorem
open Set hiding up
open Metric

/-! ## §Y.1 Edge containment in balls -/

/-- Unit basis vector e₁ = (1, 0). HOL Light: `e1`. -/
private noncomputable def e1 : E2 := point (1, 0)

/-- Unit basis vector e₂ = (0, 1). HOL Light: `e2`. -/
private noncomputable def e2 : E2 := point (0, 1)

/-- HOL Light: `h_edge_ball` (line 46349).
A horizontal edge `hEdge m` is contained in the open ball of radius ½
centered at `pointI m + (1/2) * e1`. -/
theorem h_edge_ball (m : ℤ × ℤ) :
    hEdge m ⊆ Metric.ball (pointI m + (1 / 2 : ℝ) • e1) (1 / 2) := by
  intro z hz
  simp only [hEdge, Set.mem_setOf_eq] at hz
  obtain ⟨h0, h1, h2⟩ := hz
  rw [Metric.mem_ball, EuclideanSpace.dist_eq]
  have center0 : (pointI m + (1 / 2 : ℝ) • e1) 0 = ↑m.1 + 1 / 2 := by
    simp [pointI, e1]
  have center1 : (pointI m + (1 / 2 : ℝ) • e1) 1 = ↑m.2 := by
    simp [pointI, e1]
  have sum_eq : ∑ i : Fin 2, dist (z.ofLp i) ((pointI m + (1 / 2 : ℝ) • e1).ofLp i) ^ 2
      = (z 0 - (↑m.1 + 1 / 2)) ^ 2 + 0 := by
    rw [Fin.sum_univ_two]
    congr 1
    · rw [show z.ofLp 0 = z 0 from rfl,
          show (pointI m + (1 / 2 : ℝ) • e1).ofLp 0 = (pointI m + (1 / 2 : ℝ) • e1) 0 from rfl,
          center0, Real.dist_eq, sq_abs]
    · rw [show z.ofLp 1 = z 1 from rfl,
          show (pointI m + (1 / 2 : ℝ) • e1).ofLp 1 = (pointI m + (1 / 2 : ℝ) • e1) 1 from rfl,
          center1, h2, Real.dist_eq, sub_self, abs_zero, sq, mul_zero]
  rw [sum_eq, add_zero, Real.sqrt_sq_eq_abs, abs_lt]
  constructor <;> linarith

/-- HOL Light: `v_edge_ball` (line 46384).
A vertical edge `vEdge m` is contained in the open ball of radius ½
centered at `pointI m + (1/2) * e2`. -/
theorem v_edge_ball (m : ℤ × ℤ) :
    vEdge m ⊆ Metric.ball (pointI m + (1 / 2 : ℝ) • e2) (1 / 2) := by
  intro z hz
  simp only [vEdge, Set.mem_setOf_eq] at hz
  obtain ⟨h0, h1, h2⟩ := hz
  rw [Metric.mem_ball, EuclideanSpace.dist_eq]
  have center0 : (pointI m + (1 / 2 : ℝ) • e2) 0 = ↑m.1 := by
    simp [pointI, e2]
  have center1 : (pointI m + (1 / 2 : ℝ) • e2) 1 = ↑m.2 + 1 / 2 := by
    simp [pointI, e2]
  have sum_eq : ∑ i : Fin 2, dist (z.ofLp i) ((pointI m + (1 / 2 : ℝ) • e2).ofLp i) ^ 2
      = 0 + (z 1 - (↑m.2 + 1 / 2)) ^ 2 := by
    rw [Fin.sum_univ_two]
    congr 1
    · rw [show z.ofLp 0 = z 0 from rfl,
          show (pointI m + (1 / 2 : ℝ) • e2).ofLp 0 = (pointI m + (1 / 2 : ℝ) • e2) 0 from rfl,
          center0, h0, Real.dist_eq, sub_self, abs_zero, sq, mul_zero]
    · rw [show z.ofLp 1 = z 1 from rfl,
          show (pointI m + (1 / 2 : ℝ) • e2).ofLp 1 = (pointI m + (1 / 2 : ℝ) • e2) 1 from rfl,
          center1, Real.dist_eq, sq_abs]
  rw [sum_eq, zero_add, Real.sqrt_sq_eq_abs, abs_lt]
  constructor <;> linarith

/-! ## §Y.2 Auxiliary real analysis lemmas (many are in Mathlib) -/

-- `sqrt_frac` (line 46422): sqrt((n/m)^2) = n/m for n/m ≥ 0.
-- Already in Mathlib as `Real.sqrt_sq` / `abs_of_nonneg`.

-- `abs_dest_int_half` (line 46432): |real_of_int m - 1/2| ≥ 1/2.
-- This is a number-theory / real-analysis fact about the distance from
-- integers to 1/2.

/-- HOL Light: `abs_dest_int_half` (line 46432).
Half-integer gap: `|m - 1/2| ≥ 1/2` for any integer `m`. -/
theorem abs_dest_int_half (m : ℤ) : (1 : ℝ) / 2 ≤ |(m : ℝ) - 1 / 2| := by
  rcases le_or_gt (m : ℝ) 0 with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · have hm : (1 : ℝ) ≤ m := by
      have : (0 : ℤ) < m := by exact_mod_cast h
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]; linarith

-- `REAL_LT_SQUARE_ABS` (line 46463): |x| < |y| ↔ x² < y².
-- Already in Mathlib as `sq_lt_sq'` and related.

/-! ## §Y.3 Closed ball uniqueness for edges -/

/-- Squared Euclidean distance bound: dist(z,c) ≤ r implies the sum of
    squares of coordinate differences is at most r². -/
private lemma euclid_dist_le_sq {z c : E2} {r : ℝ} (hr : 0 ≤ r) (h : dist z c ≤ r) :
    (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2 ≤ r ^ 2 := by
  rw [EuclideanSpace.dist_eq] at h
  have hnn : 0 ≤ ∑ i : Fin 2, dist (z.ofLp i) (c.ofLp i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : ∑ i : Fin 2, dist (z.ofLp i) (c.ofLp i) ^ 2 ≤ r ^ 2 := by
    nlinarith [Real.sq_sqrt hnn,
      Real.sqrt_nonneg (∑ i : Fin 2, dist (z.ofLp i) (c.ofLp i) ^ 2)]
  rw [Fin.sum_univ_two] at h2
  have eq0 : dist (z.ofLp 0) (c.ofLp 0) ^ 2 = (z 0 - c 0) ^ 2 := by
    rw [show z.ofLp 0 = z 0 from rfl, show c.ofLp 0 = c 0 from rfl,
        Real.dist_eq, sq_abs]
  have eq1 : dist (z.ofLp 1) (c.ofLp 1) ^ 2 = (z 1 - c 1) ^ 2 := by
    rw [show z.ofLp 1 = z 1 from rfl, show c.ofLp 1 = c 1 from rfl,
        Real.dist_eq, sq_abs]
  linarith

/-- Closed vertical edge (edge ∪ endpoints).
    HOL Light: `vc_edge` (line ~47337). -/
def vcEdge (m : ℤ × ℤ) : Set E2 :=
  vEdge m ∪ {pointI m} ∪ {pointI (m.1, m.2 + 1)}

/-- Closed horizontal edge (edge ∪ endpoints).
    HOL Light: `hc_edge` (line ~47345). -/
def hcEdge (m : ℤ × ℤ) : Set E2 :=
  hEdge m ∪ {pointI m} ∪ {pointI (m.1 + 1, m.2)}

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: the proof case-splits on `isEdge` (hEdge vs. vEdge) and closes each
-- branch with `nlinarith` on squared distance inequalities, which is slow to discharge.
/-- HOL Light: `h_edge_closed_ball` (line 46478).
If an edge intersects the closed ball of radius ½ around
`pointI m + (1/2) * e1`, then it must be `hEdge m`. -/
theorem h_edge_closed_ball (e : Set E2) (m : ℤ × ℤ)
    (he : isEdge e)
    (hint : (e ∩ Metric.closedBall (pointI m + (1 / 2 : ℝ) • e1) (1 / 2)).Nonempty) :
    e = hEdge m := by
  obtain ⟨z, hz_e, hz_ball⟩ := hint
  rw [Metric.mem_closedBall] at hz_ball
  have c0 : (pointI m + (1 / 2 : ℝ) • e1) 0 = ↑m.1 + 1 / 2 := by simp [pointI, e1]
  have c1 : (pointI m + (1 / 2 : ℝ) • e1) 1 = ↑m.2 := by simp [pointI, e1]
  have hsq : (z 0 - (↑m.1 + 1 / 2)) ^ 2 + (z 1 - ↑m.2) ^ 2 ≤ (1 / 2) ^ 2 := by
    have := euclid_dist_le_sq (by norm_num : (0 : ℝ) ≤ 1 / 2) hz_ball
    rw [c0, c1] at this; exact this
  rcases he with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · -- e = hEdge m'
    simp only [hEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨h0, h1, h2⟩ := hz_e
    rw [h2] at hsq
    have hm2 : m'.2 = m.2 := by
      by_contra hne
      have : m'.2 - m.2 ≠ 0 := sub_ne_zero.mpr hne
      have := Int.one_le_abs this
      have : (1 : ℝ) ≤ |(↑m'.2 : ℝ) - ↑m.2| := by exact_mod_cast this
      nlinarith [sq_abs ((↑m'.2 : ℝ) - ↑m.2), sq_nonneg (z 0 - (↑m.1 + 1 / 2))]
    have hm2c : (↑m'.2 : ℝ) = ↑m.2 := by exact_mod_cast hm2
    have hzx_sq : (z 0 - (↑m.1 + 1 / 2)) ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [hm2c]
    have hzx_abs : |z 0 - (↑m.1 + 1 / 2)| ≤ 1 / 2 :=
      abs_le_of_sq_le_sq hzx_sq (by norm_num)
    have hm1 : m'.1 = m.1 := by
      have hzx_lo : (↑m.1 : ℝ) ≤ z 0 := by
        have := (abs_le.mp hzx_abs).1; linarith
      have hzx_hi : z 0 ≤ ↑m.1 + 1 := by
        have := (abs_le.mp hzx_abs).2; linarith
      exact le_antisymm
        (Int.lt_add_one_iff.mp
          (by exact_mod_cast (show (↑m'.1 : ℝ) < ↑m.1 + 1 by linarith)))
        (Int.lt_add_one_iff.mp
          (by exact_mod_cast (show (↑m.1 : ℝ) < ↑m'.1 + 1 by linarith)))
    congr 1; exact Prod.ext hm1 hm2
  · -- e = vEdge m': contradiction via abs_dest_int_half
    exfalso
    simp only [vEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨h0, h1, h2⟩ := hz_e
    rw [h0] at hsq
    have habs : (1 : ℝ) / 2 ≤ |((↑m'.1 : ℝ) - ↑m.1) - 1 / 2| := by
      have := abs_dest_int_half (m'.1 - m.1); push_cast at this ⊢; linarith
    have habs_sq : (1 / 2 : ℝ) ^ 2 ≤ ((↑m'.1 : ℝ) - ↑m.1 - 1 / 2) ^ 2 := by
      nlinarith [sq_abs ((↑m'.1 : ℝ) - ↑m.1 - 1 / 2)]
    have hring : ((↑m'.1 : ℝ) - (↑m.1 + 1 / 2)) ^ 2 =
        ((↑m'.1 : ℝ) - ↑m.1 - 1 / 2) ^ 2 := by ring
    have hz1_sq : (z 1 - ↑m.2) ^ 2 ≤ 0 := by nlinarith
    have hz1_eq : z 1 = ↑m.2 := by nlinarith [sq_nonneg (z 1 - ↑m.2)]
    have : (m'.2 : ℤ) < m.2 := by
      exact_mod_cast (show (↑m'.2 : ℝ) < ↑m.2 by linarith)
    have : (m.2 : ℤ) < m'.2 + 1 := by
      exact_mod_cast (show (↑m.2 : ℝ) < ↑m'.2 + 1 by linarith)
    omega

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: symmetric to `h_edge_closed_ball`; the vEdge case-split requires
-- `nlinarith` to refute hEdge membership via squared half-integer distance bounds.
/-- HOL Light: `v_edge_closed_ball` (line 46601).
If an edge intersects the closed ball of radius ½ around
`pointI m + (1/2) * e2`, then it must be `vEdge m`. -/
theorem v_edge_closed_ball (e : Set E2) (m : ℤ × ℤ)
    (he : isEdge e)
    (hint : (e ∩ Metric.closedBall (pointI m + (1 / 2 : ℝ) • e2) (1 / 2)).Nonempty) :
    e = vEdge m := by
  obtain ⟨z, hz_e, hz_ball⟩ := hint
  rw [Metric.mem_closedBall] at hz_ball
  have c0 : (pointI m + (1 / 2 : ℝ) • e2) 0 = ↑m.1 := by simp [pointI, e2]
  have c1 : (pointI m + (1 / 2 : ℝ) • e2) 1 = ↑m.2 + 1 / 2 := by simp [pointI, e2]
  have hsq : (z 0 - ↑m.1) ^ 2 + (z 1 - (↑m.2 + 1 / 2)) ^ 2 ≤ (1 / 2) ^ 2 := by
    have := euclid_dist_le_sq (by norm_num : (0 : ℝ) ≤ 1 / 2) hz_ball
    rw [c0, c1] at this; exact this
  rcases he with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · -- e = hEdge m': contradiction via abs_dest_int_half
    exfalso
    simp only [hEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨h0, h1, h2⟩ := hz_e
    rw [h2] at hsq
    have habs : (1 : ℝ) / 2 ≤ |((↑m'.2 : ℝ) - ↑m.2) - 1 / 2| := by
      have := abs_dest_int_half (m'.2 - m.2); push_cast at this ⊢; linarith
    have habs_sq : (1 / 2 : ℝ) ^ 2 ≤ ((↑m'.2 : ℝ) - ↑m.2 - 1 / 2) ^ 2 := by
      nlinarith [sq_abs ((↑m'.2 : ℝ) - ↑m.2 - 1 / 2)]
    have hring : ((↑m'.2 : ℝ) - (↑m.2 + 1 / 2)) ^ 2 =
        ((↑m'.2 : ℝ) - ↑m.2 - 1 / 2) ^ 2 := by ring
    have hz0_sq : (z 0 - ↑m.1) ^ 2 ≤ 0 := by nlinarith
    have hz0_eq : z 0 = ↑m.1 := by nlinarith [sq_nonneg (z 0 - ↑m.1)]
    have : (m'.1 : ℤ) < m.1 := by
      exact_mod_cast (show (↑m'.1 : ℝ) < ↑m.1 by linarith)
    have : (m.1 : ℤ) < m'.1 + 1 := by
      exact_mod_cast (show (↑m.1 : ℝ) < ↑m'.1 + 1 by linarith)
    omega
  · -- e = vEdge m'
    simp only [vEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨h0, h1, h2⟩ := hz_e
    rw [h0] at hsq
    have hm1 : m'.1 = m.1 := by
      by_contra hne
      have : m'.1 - m.1 ≠ 0 := sub_ne_zero.mpr hne
      have := Int.one_le_abs this
      have : (1 : ℝ) ≤ |(↑m'.1 : ℝ) - ↑m.1| := by exact_mod_cast this
      nlinarith [sq_abs ((↑m'.1 : ℝ) - ↑m.1),
        sq_nonneg (z 1 - (↑m.2 + 1 / 2))]
    have hm1c : (↑m'.1 : ℝ) = ↑m.1 := by exact_mod_cast hm1
    have hzy_sq : (z 1 - (↑m.2 + 1 / 2)) ^ 2 ≤ (1 / 2) ^ 2 := by
      nlinarith [hm1c]
    have hzy_abs : |z 1 - (↑m.2 + 1 / 2)| ≤ 1 / 2 :=
      abs_le_of_sq_le_sq hzy_sq (by norm_num)
    have hm2 : m'.2 = m.2 := by
      have hzy_lo : (↑m.2 : ℝ) ≤ z 1 := by
        have := (abs_le.mp hzy_abs).1; linarith
      have hzy_hi : z 1 ≤ ↑m.2 + 1 := by
        have := (abs_le.mp hzy_abs).2; linarith
      exact le_antisymm
        (Int.lt_add_one_iff.mp
          (by exact_mod_cast (show (↑m'.2 : ℝ) < ↑m.2 + 1 by linarith)))
        (Int.lt_add_one_iff.mp
          (by exact_mod_cast (show (↑m.2 : ℝ) < ↑m'.2 + 1 by linarith)))
    congr 1; exact Prod.ext hm1 hm2

/-! ## §Y.4 Connected subsets of edge union -/

/-- HOL Light: `connected_in_edge` (line 46724).
A connected subset of the union of all edges lies in a single edge. -/
theorem connected_in_edge (C : Set E2)
    (hconn : IsPreconnected C)
    (hC : C ⊆ ⋃₀ {e | isEdge e}) :
    ∃ e, isEdge e ∧ C ⊆ e := by
  by_cases hne : C.Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨e₀, he₀, hz_e₀⟩ := Set.mem_sUnion.mp (hC hz)
    rcases he₀ with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- e₀ = hEdge m
      refine ⟨hEdge m, Or.inl ⟨m, rfl⟩, ?_⟩
      set c := pointI m + (1 / 2 : ℝ) • e1
      have hC_sub :
          C ⊆ ball c (1/2) ∪ (closedBall c (1/2))ᶜ := by
        intro x hx
        obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp (hC hx)
        by_cases heq : u = hEdge m
        · left; exact h_edge_ball m (heq ▸ hxu)
        · right; intro hcb
          exact heq (h_edge_closed_ball u m hu ⟨x, hxu, hcb⟩)
      rcases hconn.subset_or_subset isOpen_ball
        Metric.isClosed_closedBall.isOpen_compl
        (disjoint_compl_right.mono_left ball_subset_closedBall)
        hC_sub with hsub | hsub
      · intro x hx
        obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp (hC hx)
        exact (h_edge_closed_ball u m hu
          ⟨x, hxu, ball_subset_closedBall (hsub hx)⟩) ▸ hxu
      · exact absurd
          (ball_subset_closedBall (h_edge_ball m hz_e₀)) (hsub hz)
    · -- e₀ = vEdge m
      refine ⟨vEdge m, Or.inr ⟨m, rfl⟩, ?_⟩
      set c := pointI m + (1 / 2 : ℝ) • e2
      have hC_sub :
          C ⊆ ball c (1/2) ∪ (closedBall c (1/2))ᶜ := by
        intro x hx
        obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp (hC hx)
        by_cases heq : u = vEdge m
        · left; exact v_edge_ball m (heq ▸ hxu)
        · right; intro hcb
          exact heq (v_edge_closed_ball u m hu ⟨x, hxu, hcb⟩)
      rcases hconn.subset_or_subset isOpen_ball
        Metric.isClosed_closedBall.isOpen_compl
        (disjoint_compl_right.mono_left ball_subset_closedBall)
        hC_sub with hsub | hsub
      · intro x hx
        obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp (hC hx)
        exact (v_edge_closed_ball u m hu
          ⟨x, hxu, ball_subset_closedBall (hsub hx)⟩) ▸ hxu
      · exact absurd
          (ball_subset_closedBall (v_edge_ball m hz_e₀)) (hsub hz)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨hEdge (0, 0), Or.inl ⟨(0, 0), rfl⟩,
      hne ▸ Set.empty_subset _⟩

/-! ## §Y.5 Integer point separation -/

-- `int_pow2_gt1` (line 46898): for nonzero integer x, 1 ≤ (real_of_int x)².
-- Follows from integer arithmetic.

/-- HOL Light: `d_euclid_pointI_pos` (line 46912).
If two integer lattice points are within Euclidean distance < 1 of each other,
they are equal. -/
private theorem int_sq_ge_one (x : ℤ) (hx : x ≠ 0) : (1 : ℝ) ≤ ((x : ℝ)) ^ 2 := by
  have : (1 : ℤ) ≤ x ^ 2 := by nlinarith [sq_abs x, Int.one_le_abs hx]
  exact_mod_cast this

/-- Two integer lattice points whose Euclidean distance is less than 1 must be equal;
    equivalently, distinct lattice points are always at distance at least 1 apart. -/
theorem d_euclid_pointI_pos (m n : ℤ × ℤ)
    (h : dist (pointI m) (pointI n) < 1) : m = n := by
  rw [dist_pointI_formula] at h
  have hsq : (↑m.1 - ↑n.1) ^ 2 + (↑m.2 - ↑n.2) ^ 2 < (1 : ℝ) := by
    have := Real.lt_sq_of_sqrt_lt h; norm_num at this ⊢; linarith
  by_contra hne
  have : m.1 ≠ n.1 ∨ m.2 ≠ n.2 := by
    by_contra habs; push Not at habs; exact hne (Prod.ext habs.1 habs.2)
  rcases this with h1 | h2
  · have := int_sq_ge_one (m.1 - n.1) (sub_ne_zero.mpr h1)
    push_cast at this; linarith [sq_nonneg ((↑m.2 : ℝ) - ↑n.2)]
  · have := int_sq_ge_one (m.2 - n.2) (sub_ne_zero.mpr h2)
    push_cast at this; linarith [sq_nonneg ((↑m.1 : ℝ) - ↑n.1)]

/-! ## §Y.6 Totally bounded integer points and finiteness -/

-- `totally_bounded_pointI` (line 46942): ∃ eps > 0, balls of radius eps around
-- integer points are disjoint. Immediate from d_euclid_pointI_pos with eps = 1/2.

/-- HOL Light: `simple_arc_finite_pointI` (line 46965).
A simple arc in ℝ² meets only finitely many integer lattice points. -/
theorem simple_arc_finite_pointI (e : Set E2')
    (harc : IsSimpleArc e) :
    ∃ X : Finset (ℤ × ℤ), ∀ m, pointI m ∈ e → m ∈ X := by
  obtain ⟨f, rfl, hf_cont, _⟩ := harc
  have hcpt : IsCompact (f '' Icc 0 1) := isCompact_Icc.image hf_cont
  obtain ⟨R, _, hR⟩ := hcpt.isBounded.exists_pos_norm_le
  refine ⟨(Finset.Icc (-⌈R⌉) ⌈R⌉) ×ˢ (Finset.Icc (-⌈R⌉) ⌈R⌉), ?_⟩
  intro m hm
  simp only [Finset.mem_product, Finset.mem_Icc]
  have hm_norm : ‖pointI m‖ ≤ R := hR _ hm
  have h1 : |↑m.1| ≤ R := le_trans
    (by rw [← pointI_coord_fst, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ _) hm_norm
  have h2 : |↑m.2| ≤ R := le_trans
    (by rw [← pointI_coord_snd, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ _) hm_norm
  have ceil_le : R ≤ ↑⌈R⌉ := Int.le_ceil R
  have bound (a : ℤ) (h : |↑a| ≤ R) :
      -⌈R⌉ ≤ a ∧ a ≤ ⌈R⌉ :=
    ⟨by exact_mod_cast show (↑(-⌈R⌉) : ℝ) ≤ ↑a by
                push_cast; linarith [(abs_le.mp h).1],
           by exact_mod_cast show (↑a : ℝ) ≤ ↑⌈R⌉ from
                le_trans (abs_le.mp h).2 ceil_le⟩
  exact ⟨bound m.1 h1, bound m.2 h2⟩

/-! ## §Y.7 Arc decomposition lemmas -/

/-- HOL Light: `simple_arc_finite_lemma1` (line 47005).
A simple arc end can be parameterized by a continuous injective function
on [0,1], with integer lattice points corresponding to a finite subset. -/
theorem simple_arc_finite_lemma1 (e : Set E2') (v v' : E2')
    (harc : IsSimpleArcEnd e v v') :
    ∃ (X : Set ℝ) (f : ℝ → E2'),
      X ⊆ Set.Icc 0 1 ∧ X.Finite ∧
      f 0 = v ∧ f 1 = v' ∧
      e = f '' Set.Icc 0 1 ∧
      Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (∃ m : ℤ × ℤ, f x = pointI m) ↔ x ∈ X := by
  obtain ⟨f, rfl, hfc, hfi, hf0, hf1⟩ := harc
  obtain ⟨Y, hY⟩ := simple_arc_finite_pointI _
    ⟨f, rfl, hfc, hfi⟩
  set X := {t ∈ Icc (0 : ℝ) 1 | ∃ m : ℤ × ℤ, f t = pointI m}
  refine ⟨X, f, fun x hx => hx.1, ?_,
    hf0, hf1, rfl, hfc, hfi, ?_⟩
  · apply Set.Finite.of_injOn (f := f)
        (t := pointI '' ↑Y)
    · intro t ⟨ht01, m, hfm⟩
      exact ⟨m, Finset.mem_coe.mpr (hY m ⟨t, ht01, hfm⟩),
        hfm.symm⟩
    · exact hfi.mono (fun x hx => hx.1)
    · exact Y.finite_toSet.image _
  · exact fun x hx => ⟨fun ⟨m, hm⟩ => ⟨hx, m, hm⟩,
      fun ⟨_, m, hm⟩ => ⟨m, hm⟩⟩

/-- HOL Light: `simple_arc_finite_lemma2` (line 47061).
Refined version of lemma1: the finite set is indexed by an increasing
sequence `t : ℕ → ℝ`. -/
theorem simple_arc_finite_lemma2 (e : Set E2') (v v' : E2')
    (harc : IsSimpleArcEnd e v v') :
    ∃ (N : ℕ) (t : ℕ → ℝ) (f : ℝ → E2'),
      (∀ i, i < N → t i ∈ Set.Icc 0 1) ∧
      f 0 = v ∧ f 1 = v' ∧
      e = f '' Set.Icc 0 1 ∧
      (∀ i j, i < j → i < N → j < N → t i < t j) ∧
      Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (∃ m : ℤ × ℤ, f x = pointI m) ↔ ∃ k, k < N ∧ x = t k := by
  obtain ⟨X, f, hX_sub, hX_fin, hf0, hf1, he, hfc, hfi, hiff⟩ :=
    simple_arc_finite_lemma1 e v v' harc
  let S := hX_fin.toFinset
  let L := S.sort (· ≤ ·)
  let N := L.length
  let t : ℕ → ℝ := fun i =>
    if h : i < N then L.get ⟨i, h⟩ else 0
  refine ⟨N, t, f, ?_, hf0, hf1, he, ?_, hfc, hfi, ?_⟩
  · intro i hi
    change (if h : i < N then L.get ⟨i, h⟩ else 0) ∈ _
    rw [dif_pos hi]
    exact hX_sub (hX_fin.mem_toFinset.mp
      ((Finset.mem_sort _).mp (L.get_mem ⟨i, hi⟩)))
  · intro i j hij hiN hjN
    change (if _ : i < N then _ else _) <
           (if _ : j < N then _ else _)
    rw [dif_pos hiN, dif_pos hjN]
    exact Finset.sortedLT_sort S
      (show (⟨i, hiN⟩ : Fin N) < ⟨j, hjN⟩ from hij)
  · intro x hx
    rw [hiff x hx]
    constructor
    · intro hxX
      have hxL : x ∈ L :=
        (Finset.mem_sort _).mpr (hX_fin.mem_toFinset.mpr hxX)
      obtain ⟨⟨k, hk⟩, hget⟩ := List.mem_iff_get.mp hxL
      refine ⟨k, hk, ?_⟩
      change x = if h : k < N then L.get ⟨k, h⟩ else 0
      rw [dif_pos hk]; exact hget.symm
    · intro ⟨k, hk, hxk⟩
      have : x = L.get ⟨k, hk⟩ := by
        have : x = (if h : k < N then L.get ⟨k, h⟩ else 0) :=
          hxk
        rwa [dif_pos hk] at this
      rw [this]
      exact hX_fin.mem_toFinset.mp
        ((Finset.mem_sort _).mp (L.get_mem ⟨k, hk⟩))

-- `connected_unions_common` (line 47090): union of connected sets with
-- pairwise nonempty intersection is connected. Already in Mathlib
-- as `IsPreconnected.iUnion` / similar.

-- `connect_real_open` (line 47155): open intervals (a, b) ⊂ ℝ are connected.
-- Already in Mathlib as `isPreconnected_Ioo`.

-- `int_neg_num_th` (line 47200): real_of_int(-n) = -n. Trivial coercion.

-- `closed_ball_subset_larger_open` (line 47209): closed_ball r ⊆ open_ball r'
-- when r < r'. Already in Mathlib as `Metric.closedBall_subset_ball`.

/-! ## §Y.8 Edge closure via simple arcs -/

/-- HOL Light: `simple_arc_end_edge_closure` (line 47221).
If a simple arc from `pointI m` to `pointI n` lies (except endpoints) in
edge `e`, then `pointI m` is in the closure of `e`. -/
theorem simple_arc_end_edge_closure (C : Set E2) (e : Set E2)
    (m n : ℤ × ℤ)
    (_he : isEdge e)
    (harc : IsSimpleArcEnd C (pointI m) (pointI n))
    (hC : ∀ x ∈ C, x ≠ pointI m → x ≠ pointI n → x ∈ e) :
    pointI m ∈ closure e := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, rfl, hf_cont, hf_inj, hf0, hf1⟩ := harc
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp
    hf_cont.continuousAt ε hε
  set t := min (δ / 2) (1 / 2) with ht_def
  have ht_pos : 0 < t := lt_min (by linarith) (by norm_num)
  have ht_lt1 : t < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ht_01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_lt ht_pos, le_of_lt ht_lt1⟩
  have hdist : dist (f t) (pointI m) < ε := by
    rw [← hf0]; apply hδ
    simp only [dist_zero_right, Real.norm_eq_abs,
      abs_of_pos ht_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hft_ne_m : f t ≠ pointI m := by
    intro h; rw [← hf0] at h
    exact absurd (hf_inj ht_01 (left_mem_Icc.mpr (by norm_num))
      h) (ne_of_gt ht_pos)
  have hft_ne_n : f t ≠ pointI n := by
    intro h; rw [← hf1] at h
    exact absurd (hf_inj ht_01 (right_mem_Icc.mpr (by norm_num))
      h) (ne_of_lt ht_lt1)
  exact ⟨f t,
    hC _ ⟨t, ht_01, rfl⟩ hft_ne_m hft_ne_n,
    by rw [dist_comm]; exact hdist⟩

/-! ## §Y.9 Closed edge = mk_segment -/

/-- `pointI (m.1, m.2 + 1)` — the lattice point above `m`.
    HOL Light: `up m`. -/
def up (m : ℤ × ℤ) : ℤ × ℤ := (m.1, m.2 + 1)

/-- `pointI (m.1 + 1, m.2)` — the lattice point to the right of `m`.
    HOL Light: `right m`. -/
def right (m : ℤ × ℤ) : ℤ × ℤ := (m.1 + 1, m.2)

/-- HOL Light: `vc_edge_pointI` (line 47349).
A closed vertical edge contains exactly `pointI m` and `pointI (up m)`. -/
theorem vcEdge_pointI (m n : ℤ × ℤ) :
    pointI n ∈ vcEdge m ↔ n = m ∨ n = up m := by
  simp only [vcEdge, up, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ((hv | hm) | hu)
    · simp only [vEdge, Set.mem_setOf_eq] at hv
      obtain ⟨h0, h1, h2⟩ := hv
      rw [pointI_coord_fst] at h0
      rw [pointI_coord_snd] at h1 h2
      exfalso
      have : (m.2 : ℤ) < n.2 := by exact_mod_cast h1
      have : (n.2 : ℤ) < m.2 + 1 := by exact_mod_cast h2
      omega
    · left
      have h0 : pointI n 0 = pointI m 0 := by rw [hm]
      have h1 : pointI n 1 = pointI m 1 := by rw [hm]
      rw [pointI_coord_fst, pointI_coord_fst] at h0
      rw [pointI_coord_snd, pointI_coord_snd] at h1
      exact Prod.ext (Int.cast_injective h0) (Int.cast_injective h1)
    · right
      have h0 : pointI n 0 = pointI (m.1, m.2 + 1) 0 := by rw [hu]
      have h1 : pointI n 1 = pointI (m.1, m.2 + 1) 1 := by rw [hu]
      rw [pointI_coord_fst, pointI_coord_fst] at h0
      rw [pointI_coord_snd, pointI_coord_snd] at h1
      exact Prod.ext (Int.cast_injective h0) (Int.cast_injective h1)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

/-- HOL Light: `hc_edge_pointI` (line 47362).
A closed horizontal edge contains exactly `pointI m` and `pointI (right m)`. -/
theorem hcEdge_pointI (m n : ℤ × ℤ) :
    pointI n ∈ hcEdge m ↔ n = m ∨ n = right m := by
  simp only [hcEdge, right, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ((hv | hm) | hu)
    · simp only [hEdge, Set.mem_setOf_eq] at hv
      obtain ⟨h0, h1, h2⟩ := hv
      rw [pointI_coord_fst] at h0 h1
      exfalso
      have : (m.1 : ℤ) < n.1 := by exact_mod_cast h0
      have : (n.1 : ℤ) < m.1 + 1 := by exact_mod_cast h1
      omega
    · left
      have h0 : pointI n 0 = pointI m 0 := by rw [hm]
      have h1 : pointI n 1 = pointI m 1 := by rw [hm]
      rw [pointI_coord_fst, pointI_coord_fst] at h0
      rw [pointI_coord_snd, pointI_coord_snd] at h1
      exact Prod.ext (Int.cast_injective h0) (Int.cast_injective h1)
    · right
      have h0 : pointI n 0 = pointI (m.1 + 1, m.2) 0 := by rw [hu]
      have h1 : pointI n 1 = pointI (m.1 + 1, m.2) 1 := by rw [hu]
      rw [pointI_coord_fst, pointI_coord_fst] at h0
      rw [pointI_coord_snd, pointI_coord_snd] at h1
      exact Prod.ext (Int.cast_injective h0) (Int.cast_injective h1)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: the proof uses `fin_cases` on `Fin 2` index and repeated `simp?`
-- calls on `point` coordinates, with `field_simp; ring` closing division goals.
/-- HOL Light: `mk_segment_v` (line 47375).
Vertical segment characterization. -/
theorem segment_vertical (r s b : ℝ) (hrs : r ≤ s) (x : E2') :
    x ∈ segment ℝ (point (b, r)) (point (b, s)) ↔
      ∃ t, r ≤ t ∧ t ≤ s ∧ x = point (b, t) := by
  simp only [mem_segment_iff_param, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht0, ht1, hx⟩
    refine ⟨t * r + (1 - t) * s, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · rw [hx]; ext i; fin_cases i <;> simp? [point] ; ring
  · rintro ⟨u, hru, hus, hx⟩
    by_cases hrs' : r = s
    · refine ⟨1, by norm_num, le_refl _, ?_⟩
      rw [hx]; ext i; fin_cases i <;> simp? [point] ; nlinarith
    · have hlt : r < s := lt_of_le_of_ne hrs hrs'
      have hne : s - r ≠ 0 := by linarith
      refine ⟨(s - u) / (s - r), ?_, ?_, ?_⟩
      · apply div_nonneg <;> linarith
      · rw [div_le_one (by linarith)]; linarith
      · rw [hx]; ext i; fin_cases i <;> simp? [point] <;> (field_simp; ring)

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: membership in `vcEdge` is established by `fin_cases` on `Fin 2`
-- coordinates and `simp?` on `pointI`/`point` definitions in each branch of the segment.
/-- HOL Light: `mk_segment_vc` (line 47420).
The segment from `pointI m` to `pointI (up m)` equals `vcEdge m`. -/
theorem segment_vc (m : ℤ × ℤ) :
    segment ℝ (pointI m) (pointI (up m)) = vcEdge m := by
  ext x
  simp only [mem_segment_iff_param, Set.mem_setOf_eq, vcEdge, up, vEdge,
    Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht0, ht1, hx⟩
    have hx0 : x 0 = ↑m.1 := by
      have := congr_arg (· 0) hx; simp? [pointI, point] at this; linarith
    have hx1 : x 1 = ↑m.2 + (1 - t) := by
      have := congr_arg (· 1) hx; simp? [pointI, point] at this; linarith
    by_cases ht0' : t = 0
    · exact Or.inr (by rw [hx, ht0']; ext i; fin_cases i <;> simp? [pointI, point])
    · by_cases ht1' : t = 1
      · exact Or.inl (Or.inr (by
          rw [hx, ht1']; ext i; fin_cases i <;> simp? [pointI, point]))
      · have h0t : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
        have ht1s : t < 1 := lt_of_le_of_ne ht1 ht1'
        exact Or.inl (Or.inl
          ⟨by rw [hx0], by rw [hx1]; linarith, by rw [hx1]; linarith⟩)
  · rintro ((⟨h0, h1, h2⟩ | hm) | hu)
    · refine ⟨↑m.2 + 1 - x 1, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · ext i; fin_cases i <;> simp? [pointI, point] <;> linarith
    · exact ⟨1, by norm_num, le_refl _,
        by rw [hm]; ext i; fin_cases i <;> simp? [pointI, point]⟩
    · exact ⟨0, le_refl _, by norm_num,
        by rw [hu]; ext i; fin_cases i <;> simp? [pointI, point]⟩

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: symmetric to `mk_segment_vc`; characterizing `hcEdge` membership
-- uses `fin_cases` on `Fin 2` coordinates and repeated `simp?`/`linarith` steps.
/-- HOL Light: `mk_segment_hc` (line 47453).
The segment from `pointI m` to `pointI (right m)` equals `hcEdge m`. -/
theorem segment_hc (m : ℤ × ℤ) :
    segment ℝ (pointI m) (pointI (right m)) = hcEdge m := by
  ext x
  simp only [mem_segment_iff_param, Set.mem_setOf_eq, hcEdge, right, hEdge,
    Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht0, ht1, hx⟩
    have hx0 : x 0 = ↑m.1 + (1 - t) := by
      have := congr_arg (· 0) hx; simp? [pointI, point] at this; linarith
    have hx1 : x 1 = ↑m.2 := by
      have := congr_arg (· 1) hx; simp? [pointI, point] at this; linarith
    by_cases ht0' : t = 0
    · exact Or.inr (by rw [hx, ht0']; ext i; fin_cases i <;> simp? [pointI, point])
    · by_cases ht1' : t = 1
      · exact Or.inl (Or.inr (by
          rw [hx, ht1']; ext i; fin_cases i <;> simp? [pointI, point]))
      · have h0t : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
        have ht1s : t < 1 := lt_of_le_of_ne ht1 ht1'
        exact Or.inl (Or.inl
          ⟨by rw [hx0]; linarith, by rw [hx0]; linarith, by rw [hx1]⟩)
  · rintro ((⟨h0, h1, h2⟩ | hm) | hu)
    · refine ⟨↑m.1 + 1 - x 0, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · ext i; fin_cases i <;> simp? [pointI, point] <;> linarith
    · exact ⟨1, by norm_num, le_refl _,
        by rw [hm]; ext i; fin_cases i <;> simp? [pointI, point]⟩
    · exact ⟨0, le_refl _, by norm_num,
        by rw [hu]; ext i; fin_cases i <;> simp? [pointI, point]⟩

/-- HOL Light: `simple_arc_end_edge_full_closure` (line 47485).
If an arc from `pointI m` to `pointI n` lies (except endpoints) in edge `e`,
then the arc equals the closure of `e`. -/
theorem simple_arc_end_edge_full_closure (C : Set E2) (e : Set E2)
    (m n : ℤ × ℤ) (he : isEdge e)
    (harc : IsSimpleArcEnd C (pointI m) (pointI n))
    (hC : ∀ x ∈ C, x ≠ pointI m → x ≠ pointI n → x ∈ e) :
    C = closure e := by
  have hmn : m ≠ n := by
    intro heq; subst heq
    obtain ⟨f, _, _, hinj, hf0, hf1⟩ := harc
    exact absurd (hinj (by norm_num : (0:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
      (hf0.trans hf1.symm)) (by norm_num)
  have hm_cl : pointI m ∈ closure e :=
    simple_arc_end_edge_closure C e m n he harc hC
  have hn_cl : pointI n ∈ closure e :=
    simple_arc_end_edge_closure C e n m he (isSimpleArcEnd_symm harc)
      (fun x hx hxn hxm => hC x hx hxm hxn)
  have hCcl : C ⊆ closure e := by
    intro x hx
    by_cases hxm : x = pointI m
    · exact hxm ▸ hm_cl
    · by_cases hxn : x = pointI n
      · exact hxn ▸ hn_cl
      · exact subset_closure (hC x hx hxm hxn)
  have hcl_eq_h : ∀ k' : ℤ × ℤ, closure (hEdge k') = hcEdge k' := by
    intro k'; ext z; constructor
    · intro hz; rw [closure_hEdge] at hz; obtain ⟨h0, h1, h2⟩ := hz
      simp only [hcEdge, Set.mem_union, Set.mem_singleton_iff, hEdge, Set.mem_setOf_eq]
      rcases lt_or_eq_of_le h0 with h0' | h0'
      · rcases lt_or_eq_of_le h1 with h1' | h1'
        · exact Or.inl (Or.inl ⟨h0', h1', h2⟩)
        · right; ext i; fin_cases i
          · simp? [pointI, point]; linarith
          · simp? [pointI, point]; exact h2
      · left; right; ext i; fin_cases i
        · simp? [pointI, point]; linarith
        · simp? [pointI, point]; exact h2
    · intro hz
      simp only [hcEdge, Set.mem_union, Set.mem_singleton_iff, hEdge, Set.mem_setOf_eq] at hz
      rcases hz with ((⟨h0, h1, h2⟩ | rfl) | rfl)
      · exact subset_closure ⟨h0, h1, h2⟩
      · rw [closure_hEdge]
        exact ⟨le_refl _, by rw [pointI_coord_fst]; push_cast; linarith, pointI_coord_snd k'⟩
      · rw [closure_hEdge]
        refine ⟨by rw [pointI_coord_fst]; push_cast; linarith,
               by rw [pointI_coord_fst]; push_cast; linarith, by simp? [pointI, point]⟩
  have hcl_eq_v : ∀ k' : ℤ × ℤ, closure (vEdge k') = vcEdge k' := by
    intro k'; ext z; constructor
    · intro hz; rw [closure_vEdge] at hz; obtain ⟨h0, h1, h2⟩ := hz
      simp only [vcEdge, Set.mem_union, Set.mem_singleton_iff, vEdge, Set.mem_setOf_eq]
      rcases lt_or_eq_of_le h1 with h1' | h1'
      · rcases lt_or_eq_of_le h2 with h2' | h2'
        · exact Or.inl (Or.inl ⟨h0, h1', h2'⟩)
        · right; ext i; fin_cases i
          · simp? [pointI, point]; exact h0
          · simp? [pointI, point]; linarith
      · left; right; ext i; fin_cases i
        · simp? [pointI, point]; exact h0
        · simp? [pointI, point]; linarith
    · intro hz
      simp only [vcEdge, Set.mem_union, Set.mem_singleton_iff, vEdge, Set.mem_setOf_eq] at hz
      rcases hz with ((⟨h0, h1, h2⟩ | rfl) | rfl)
      · exact subset_closure ⟨h0, h1, h2⟩
      · rw [closure_vEdge]
        exact ⟨pointI_coord_fst k', le_refl _, by rw [pointI_coord_snd]; push_cast; linarith⟩
      · rw [closure_vEdge]
        refine ⟨by simp? [pointI, point],
               by rw [pointI_coord_snd]; push_cast; linarith,
               by rw [pointI_coord_snd]; push_cast; linarith⟩
  rcases he with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hcl_mk : closure (hEdge k) = segment ℝ (pointI k) (pointI (right k)) :=
      (hcl_eq_h k).trans (segment_hc k).symm
    rw [hcl_mk]
    have hk_ne : pointI k ≠ pointI (right k) :=
      fun h => absurd (congr_arg Prod.fst (pointI_injective h)) (by simp only [right]; omega)
    have hcl_sae := segment_isSimpleArcEnd hk_ne
    have hCcl' : C ⊆ segment ℝ (pointI k) (pointI (right k)) := hcl_mk ▸ hCcl
    have hm_id : m = k ∨ m = right k :=
      (hcEdge_pointI k m).mp (segment_hc k ▸ hCcl' (by
        obtain ⟨f, rfl, _, _, hf0, _⟩ := harc; exact ⟨0, by norm_num, hf0⟩))
    have hn_id : n = k ∨ n = right k :=
      (hcEdge_pointI k n).mp (segment_hc k ▸ hCcl' (by
        obtain ⟨f, rfl, _, _, _, hf1⟩ := harc; exact ⟨1, by norm_num, hf1⟩))
    rcases hm_id with rfl | rfl <;> rcases hn_id with rfl | rfl
    · exact absurd rfl hmn
    · exact isSimpleArcEnd_inj harc hcl_sae
        (isSimpleArcEnd_isSimpleArc hcl_sae) hCcl' Subset.rfl
    · exact isSimpleArcEnd_inj harc (isSimpleArcEnd_symm hcl_sae)
        (isSimpleArcEnd_isSimpleArc hcl_sae) hCcl' Subset.rfl
    · exact absurd rfl hmn
  · have hcl_mk : closure (vEdge k) = segment ℝ (pointI k) (pointI (up k)) :=
      (hcl_eq_v k).trans (segment_vc k).symm
    rw [hcl_mk]
    have hk_ne : pointI k ≠ pointI (up k) :=
      fun h => absurd (congr_arg Prod.snd (pointI_injective h)) (by simp only [up]; omega)
    have hcl_sae := segment_isSimpleArcEnd hk_ne
    have hCcl' : C ⊆ segment ℝ (pointI k) (pointI (up k)) := hcl_mk ▸ hCcl
    have hm_id : m = k ∨ m = up k :=
      (vcEdge_pointI k m).mp (segment_vc k ▸ hCcl' (by
        obtain ⟨f, rfl, _, _, hf0, _⟩ := harc; exact ⟨0, by norm_num, hf0⟩))
    have hn_id : n = k ∨ n = up k :=
      (vcEdge_pointI k n).mp (segment_vc k ▸ hCcl' (by
        obtain ⟨f, rfl, _, _, _, hf1⟩ := harc; exact ⟨1, by norm_num, hf1⟩))
    rcases hm_id with rfl | rfl <;> rcases hn_id with rfl | rfl
    · exact absurd rfl hmn
    · exact isSimpleArcEnd_inj harc hcl_sae
        (isSimpleArcEnd_isSimpleArc hcl_sae) hCcl' Subset.rfl
    · exact isSimpleArcEnd_inj harc (isSimpleArcEnd_symm hcl_sae)
        (isSimpleArcEnd_isSimpleArc hcl_sae) hCcl' Subset.rfl
    · exact absurd rfl hmn

/-! ## §Y.10 Arc decomposition into segments -/

/-- HOL Light: `simple_arc_finite_lemma3` (line 47553).
Refined decomposition where each sub-arc between consecutive integer points
is the closure of exactly one edge. -/
theorem simple_arc_finite_lemma3 (Eset : Set (Set E2')) (e : Set E2')
    (v v' : E2')
    (harc : IsSimpleArcEnd e v v')
    (_hfin : Eset.Finite)
    (hcov : e ⊆ ⋃₀ Eset)
    (hv0 : epsHyper true (v 0) ∈ Eset) (hv1 : epsHyper false (v 1) ∈ Eset)
    (hv'0 : epsHyper true (v' 0) ∈ Eset) (hv'1 : epsHyper false (v' 1) ∈ Eset)
    (hform : ∀ e' ∈ Eset, ∃ z eps, e' = epsHyper eps z)
    (hint : ∀ z eps, epsHyper eps z ∈ Eset → ∃ j : ℕ, z = -(↑j : ℝ)) :
    ∃ (N : ℕ) (t : ℕ → ℝ) (f : ℝ → E2'),
      (∀ i, i < N → t i ∈ Set.Icc 0 1) ∧
      f 0 = v ∧ f 1 = v' ∧
      e = f '' Set.Icc 0 1 ∧
      (∀ i j, i < j → i < N → j < N → t i < t j) ∧
      Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        (∃ m : ℤ × ℤ, f x = pointI m) ↔ ∃ k, k < N ∧ x = t k) ∧
      0 = t 0 ∧ 1 = t (N - 1) ∧
      (∀ i, i + 1 < N → ∃ ed, isEdge ed ∧
        f '' {x | t i ≤ x ∧ x ≤ t (i + 1)} = closure ed) := by
  obtain ⟨N, t, f, ht_mem, hf0, hf1, he, ht_inc, hfc, hfi, hiff⟩ :=
    simple_arc_finite_lemma2 e v v' harc
  have hv_int : ∃ m : ℤ × ℤ, v = pointI m := by
    obtain ⟨j1, hj1⟩ := hint (v 0) true hv0
    obtain ⟨j2, hj2⟩ := hint (v 1) false hv1
    exact ⟨(-↑j1, -↑j2), by ext i; fin_cases i <;> simp? [pointI, point] <;>
      [rw [hj1]; rw [hj2]]⟩
  have hv'_int : ∃ m : ℤ × ℤ, v' = pointI m := by
    obtain ⟨j1, hj1⟩ := hint (v' 0) true hv'0
    obtain ⟨j2, hj2⟩ := hint (v' 1) false hv'1
    exact ⟨(-↑j1, -↑j2), by ext i; fin_cases i <;> simp? [pointI, point] <;>
      [rw [hj1]; rw [hj2]]⟩
  have hN_pos : 0 < N := by
    obtain ⟨m, hm⟩ := hv_int
    obtain ⟨k, hk, _⟩ := (hiff 0 (by norm_num)).mp ⟨m, hf0 ▸ hm⟩; omega
  have h0_t0 : (0 : ℝ) = t 0 := by
    obtain ⟨m, hm⟩ := hv_int
    obtain ⟨k, hk, h0k⟩ := (hiff 0 (by norm_num)).mp ⟨m, hf0 ▸ hm⟩
    by_contra h
    have hk0 : 0 < k :=
      Nat.pos_of_ne_zero (by intro heq; subst heq; exact h h0k)
    linarith [ht_inc 0 k hk0 hN_pos hk, (ht_mem 0 hN_pos).1]
  have h1_tN : (1 : ℝ) = t (N - 1) := by
    obtain ⟨m, hm⟩ := hv'_int
    obtain ⟨k, hk, h1k⟩ := (hiff 1 (by norm_num)).mp ⟨m, hf1 ▸ hm⟩
    by_contra h
    by_cases hkN : k = N - 1
    · exact h (hkN ▸ h1k)
    · have hN1 : N - 1 < N := Nat.sub_lt hN_pos (by norm_num)
      linarith [ht_inc k (N - 1) (by omega : k < N - 1) hk hN1,
        (ht_mem (N - 1) hN1).2]
  refine ⟨N, t, f, ht_mem, hf0, hf1, he, ht_inc, hfc, hfi, hiff,
    h0_t0, h1_tN, ?_⟩
  intro i hi
  have hi_lt : i < N := by omega
  have hti := ht_mem i hi_lt
  have hti1 := ht_mem (i + 1) hi
  have htii : t i < t (i + 1) :=
    ht_inc i (i + 1) (by omega) hi_lt hi
  obtain ⟨mi, hmi⟩ := (hiff (t i) hti).mpr ⟨i, hi_lt, rfl⟩
  obtain ⟨mi1, hmi1⟩ :=
    (hiff (t (i + 1)) hti1).mpr ⟨i + 1, hi, rfl⟩
  have ht_not_int : ∀ x, t i < x → x < t (i + 1) →
      0 ≤ x → x ≤ 1 → ¬∃ m : ℤ × ℤ, f x = pointI m := by
    intro x hxl hxr hx0 hx1 ⟨m, hm⟩
    obtain ⟨k, hk, rfl⟩ := (hiff x ⟨hx0, hx1⟩).mp ⟨m, hm⟩
    have : i < k := by
      by_contra h; push Not at h
      rcases h.eq_or_lt with rfl | h
      · exact lt_irrefl _ hxl
      · exact lt_asymm hxl (ht_inc k i h hk hi_lt)
    have : k < i + 1 := by
      by_contra h; push Not at h
      rcases h.eq_or_lt with rfl | h
      · exact lt_irrefl _ hxr
      · exact lt_asymm hxr (ht_inc (i + 1) k h hi hk)
    omega
  have hpt_edge : ∀ x, t i < x → x < t (i + 1) →
      ∃ ed, isEdge ed ∧ f x ∈ ed := by
    intro x hxl hxr
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hti.1], by linarith [hti1.2]⟩
    have hfx_e : f x ∈ e := by rw [he]; exact ⟨x, hx01, rfl⟩
    obtain ⟨s, hs_mem, hfx_s⟩ := hcov hfx_e
    obtain ⟨z, eps, rfl⟩ := hform s hs_mem
    obtain ⟨j, rfl⟩ := hint z eps hs_mem
    have hfx_nint := ht_not_int x hxl hxr hx01.1 hx01.2
    obtain ⟨ct, hct⟩ := cell_covers (f x)
    rcases ct with ⟨m⟩ | ⟨m⟩ | ⟨m⟩ | ⟨m⟩
    · simp only [CellType.toSet, Set.mem_singleton_iff] at hct
      exact absurd ⟨m, hct⟩ hfx_nint
    · exact ⟨hEdge m, Or.inl ⟨m, rfl⟩, hct⟩
    · exact ⟨vEdge m, Or.inr ⟨m, rfl⟩, hct⟩
    · exfalso
      simp only [CellType.toSet, squ, Set.mem_setOf_eq] at hct
      obtain ⟨hct1, hct2, hct3, hct4⟩ := hct
      dsimp [epsHyper] at hfx_s
      simp only [hyperplane2] at hfx_s
      rcases eps with _ | _
      · have : (m.2 : ℤ) < -↑j := by exact_mod_cast
          (show (↑m.2 : ℝ) < -(↑j : ℝ) by
            rw [← hfx_s]; exact hct3)
        have : -(↑j : ℤ) < m.2 + 1 := by exact_mod_cast
          (show -(↑j : ℝ) < (↑m.2 : ℝ) + 1 by
            rw [← hfx_s]; exact hct4)
        omega
      · have : (m.1 : ℤ) < -↑j := by exact_mod_cast
          (show (↑m.1 : ℝ) < -(↑j : ℝ) by
            rw [← hfx_s]; exact hct1)
        have : -(↑j : ℤ) < m.1 + 1 := by exact_mod_cast
          (show -(↑j : ℝ) < (↑m.1 : ℝ) + 1 by
            rw [← hfx_s]; exact hct2)
        omega
  have hS_conn : IsPreconnected
      (f '' Set.Ioo (t i) (t (i + 1))) :=
    isPreconnected_Ioo.image f hfc.continuousOn
  have hS_edge : f '' Set.Ioo (t i) (t (i + 1))
      ⊆ ⋃₀ {e | isEdge e} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ed, hed, h⟩ := hpt_edge x hx.1 hx.2
    exact Set.mem_sUnion.mpr ⟨ed, hed, h⟩
  obtain ⟨ed, hed, hS_sub⟩ :=
    connected_in_edge _ hS_conn hS_edge
  obtain ⟨g, hg_img, hg0, hg1, hg_inj, hg_cont⟩ :=
    arc_restrict hti.1 htii hti1.2
      (by norm_num : (0:ℝ) < 1) hfi hfc
  have harc_sub : IsSimpleArcEnd
      (f '' Set.Icc (t i) (t (i + 1)))
      (pointI mi) (pointI mi1) := by
    rw [← hmi, ← hmi1]
    exact ⟨g, hg_img.symm, hg_cont, hg_inj, hg0, hg1⟩
  have hint_ed :
      ∀ y ∈ f '' Set.Icc (t i) (t (i + 1)),
        y ≠ pointI mi → y ≠ pointI mi1 → y ∈ ed := by
    rintro _ ⟨x, ⟨hxl, hxr⟩, rfl⟩ hym hym1
    exact hS_sub (Set.mem_image_of_mem f ⟨by
      rcases hxl.eq_or_lt with h | h
      · exact absurd (h ▸ hmi) hym
      · exact h, by
      rcases hxr.eq_or_lt with h | h
      · exact absurd (h.symm ▸ hmi1) hym1
      · exact h⟩)
  refine ⟨ed, hed, ?_⟩
  change f '' Set.Icc (t i) (t (i + 1)) = closure ed
  exact simple_arc_end_edge_full_closure
    _ ed mi mi1 hed harc_sub hint_ed

/-! ## §Y.11 Order implies psegment (strict version) -/

/-- HOL Light: `order_lt_imp_psegment` (line 47920).
If f : ℕ → edge is injective and adjacency equals successor, then
the image forms a psegment. Stronger version of `order_imp_psegment`
with strict inequality in the hypothesis. -/
theorem order_lt_imp_psegment (f : ℕ → Set E2) (n : ℕ) (hn : 0 < n)
    (hinj : Set.InjOn f {p | p < n})
    (hedge : ∀ i, i < n → isEdge (f i))
    (hadj : ∀ i j, i < n → j < n → i < j →
      (cellAdj (f i) (f j) ↔ i + 1 = j)) :
    ∃ G : Segment, G.edges = (Finset.range n).image f ∧ G.isPsegment := by
  have hadj_sym : ∀ i j, i < n → j < n →
      (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [hadj i j hi hj hij]
      exact ⟨Or.inl, fun h => h.elim id (by omega)⟩
    · exact ⟨fun h => absurd h (cellAdj_irrefl _),
        fun h => by omega⟩
    · rw [cellAdj_symm, hadj j i hj hi hij]
      exact ⟨Or.inr, fun h => h.elim (by omega) id⟩
  have hinj' : ∀ i j, i < n → j < n → f i = f j → i = j :=
    fun i j hi hj => hinj hi hj
  obtain ⟨G, hG_ps, hG_edges⟩ :=
    order_imp_psegment f n hn hinj' hedge hadj_sym
  exact ⟨G, hG_edges, hG_ps⟩

/-! ## §Y.12 Arc to segment_end decomposition -/

/-- HOL Light: `simple_arc_finite_lemma4` (line 47945).
Given a simple arc end supported by eps-hyperplanes, the arc can be
decomposed into a `segment_end` with integer endpoints. -/
theorem simple_arc_finite_lemma4 (Eset : Set (Set E2')) (e : Set E2')
    (v v' : E2')
    (harc : IsSimpleArcEnd e v v')
    (hfin : Eset.Finite)
    (hcov : e ⊆ ⋃₀ Eset)
    (hv0 : epsHyper true (v 0) ∈ Eset) (hv1 : epsHyper false (v 1) ∈ Eset)
    (hv'0 : epsHyper true (v' 0) ∈ Eset) (hv'1 : epsHyper false (v' 1) ∈ Eset)
    (hform : ∀ e' ∈ Eset, ∃ z eps, e' = epsHyper eps z)
    (hint : ∀ z eps, epsHyper eps z ∈ Eset → ∃ j : ℕ, z = -(↑j : ℝ)) :
    ∃ (S : Finset (Set E2)) (a b : ℤ × ℤ),
      segment_end S a b ∧
      v = pointI a ∧ v' = pointI b ∧
      e = closure (⋃₀ ↑S) := by
  -- Step 1: Apply lemma3 to get the arc decomposition
  obtain ⟨N, t, f, ht_mem, hf0, hf1, he, ht_inc, hfc, hfi, hiff,
    h0_t0, h1_tN, hedge_sub⟩ :=
    simple_arc_finite_lemma3 Eset e v v' harc hfin hcov hv0 hv1 hv'0 hv'1
      hform hint
  -- Step 2: N ≥ 2 (at least one edge)
  have hN_ge2 : 2 ≤ N := by
    by_contra h; push Not at h; interval_cases N
    · simp at h0_t0 h1_tN; linarith
    · simp at h1_tN; linarith [h0_t0]
  have hN1_pos : 0 < N - 1 := by omega
  -- Step 3: Extract integer endpoints
  have hv_int : ∃ a : ℤ × ℤ, f (t 0) = pointI a :=
    (hiff (t 0) (ht_mem 0 (by omega))).mpr ⟨0, by omega, rfl⟩
  have hv'_int : ∃ b : ℤ × ℤ, f (t (N - 1)) = pointI b :=
    (hiff (t (N - 1)) (ht_mem (N - 1) (by omega))).mpr
      ⟨N - 1, by omega, rfl⟩
  obtain ⟨a, ha⟩ := hv_int
  obtain ⟨b, hb⟩ := hv'_int
  have hva : v = pointI a := by rw [← hf0, h0_t0]; exact ha
  have hv'b : v' = pointI b := by rw [← hf1, h1_tN]; exact hb
  -- Step 4: For each sub-interval, extract the edge
  have hedge_exists : ∀ i, i + 1 < N → ∃ ed, isEdge ed ∧
      f '' {x | t i ≤ x ∧ x ≤ t (i + 1)} = closure ed :=
    hedge_sub
  -- Define ed : ℕ → Set E2 using choice
  have hed_choice : ∀ i : ℕ, i < N - 1 →
      ∃ ed, isEdge ed ∧ f '' {x | t i ≤ x ∧ x ≤ t (i + 1)} = closure ed := by
    intro i hi; exact hedge_sub i (by omega)
  -- Use Classical.choice to define ed
  set ed : ℕ → Set E2 := fun i =>
    if h : i < N - 1 then (hed_choice i h).choose
    else ∅ with hed_def
  have hed_isEdge : ∀ i, i < N - 1 → isEdge (ed i) := by
    intro i hi; simp? [hed_def, hi]; exact (hed_choice i hi).choose_spec.1
  have hed_closure : ∀ i, i < N - 1 →
      f '' {x | t i ≤ x ∧ x ≤ t (i + 1)} = closure (ed i) := by
    intro i hi; simp? [hed_def, hi]; exact (hed_choice i hi).choose_spec.2
  -- Step 5: ed is injective on {0,..,N-2}
  have hed_inj : Set.InjOn ed {p | p < N - 1} := by
    intro i hi j hj hij
    simp only [Set.mem_setOf_eq] at hi hj
    by_contra h_ne
    -- WLOG i < j
    rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
    · -- Case i < j
      have hti_lt : t i < t (i + 1) := ht_inc i (i + 1) (by omega) (by omega) (by omega)
      have hfi_mem : f (t i) ∈ f '' {x | t i ≤ x ∧ x ≤ t (i + 1)} :=
        ⟨t i, ⟨le_refl _, le_of_lt hti_lt⟩, rfl⟩
      rw [hed_closure i hi, hij, ← hed_closure j hj] at hfi_mem
      obtain ⟨x, ⟨hxl, hxr⟩, hfx⟩ := hfi_mem
      have hti_01 : t i ∈ Set.Icc (0 : ℝ) 1 := ht_mem i (by omega)
      have hx_01 : x ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (ht_mem j (by omega)).1 hxl, le_trans hxr (ht_mem (j + 1) (by omega)).2⟩
      have hti_eq_x : t i = x := hfi hti_01 hx_01 hfx.symm
      subst hti_eq_x
      linarith [ht_inc i j h_lt (by omega) (by omega)]
    · -- Case j < i (symmetric)
      have htj_lt : t j < t (j + 1) := ht_inc j (j + 1) (by omega) (by omega) (by omega)
      have hfj_mem : f (t j) ∈ f '' {x | t j ≤ x ∧ x ≤ t (j + 1)} :=
        ⟨t j, ⟨le_refl _, le_of_lt htj_lt⟩, rfl⟩
      rw [hed_closure j hj, hij.symm, ← hed_closure i hi] at hfj_mem
      obtain ⟨x, ⟨hxl, hxr⟩, hfx⟩ := hfj_mem
      have htj_01 : t j ∈ Set.Icc (0 : ℝ) 1 := ht_mem j (by omega)
      have hx_01 : x ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (ht_mem i (by omega)).1 hxl, le_trans hxr (ht_mem (i + 1) (by omega)).2⟩
      have htj_eq_x : t j = x := hfi htj_01 hx_01 hfx.symm
      subst htj_eq_x
      linarith [ht_inc j i h_lt (by omega) (by omega)]
  -- Step 6: Adjacency ↔ successor
  -- closure(ed i) ∩ closure(ed j) ≠ ∅ iff |i - j| = 1
  -- The key insight: closure(ed i) = f '' [t i, t(i+1)] which is a compact set
  -- f(t(i+1)) is shared between ed i and ed(i+1)
  -- For non-consecutive i,j the closures don't share points (by injectivity of f)
  have hed_adj : ∀ i j, i < N - 1 → j < N - 1 → i < j →
      (cellAdj (ed i) (ed j) ↔ i + 1 = j) := by
    intro i j hi hj hij
    constructor
    · intro hadj
      obtain ⟨_, _, _, ⟨u, hu⟩⟩ := hadj
      -- u ∈ closure(ed i) ∩ closure(ed j)
      rw [← hed_closure i hi] at hu
      rw [← hed_closure j hj] at hu
      -- closure of f '' [ti, t(i+1)] = f '' [ti, t(i+1)] since image of compact
      -- under continuous is compact hence closed
      have hset_eq_i : {x | t i ≤ x ∧ x ≤ t (i + 1)} = Set.Icc (t i) (t (i + 1)) := by
        ext; simp [Set.mem_Icc]
      have hset_eq_j : {x | t j ≤ x ∧ x ≤ t (j + 1)} = Set.Icc (t j) (t (j + 1)) := by
        ext; simp [Set.mem_Icc]
      have hclosed_i : IsClosed (f '' {x | t i ≤ x ∧ x ≤ t (i + 1)}) := by
        rw [hset_eq_i]; exact (isCompact_Icc.image hfc).isClosed
      have hclosed_j : IsClosed (f '' {x | t j ≤ x ∧ x ≤ t (j + 1)}) := by
        rw [hset_eq_j]; exact (isCompact_Icc.image hfc).isClosed
      obtain ⟨⟨xi, ⟨hxi_l, hxi_r⟩, hfxi⟩, ⟨xj, ⟨hxj_l, hxj_r⟩, hfxj⟩⟩ := hu
      have hxi_01 : xi ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (ht_mem i (by omega)).1 hxi_l,
         le_trans hxi_r (ht_mem (i + 1) (by omega)).2⟩
      have hxj_01 : xj ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (ht_mem j (by omega)).1 hxj_l,
         le_trans hxj_r (ht_mem (j + 1) (by omega)).2⟩
      have hxij : xi = xj := hfi hxi_01 hxj_01 (hfxi.trans hfxj.symm)
      subst hxij
      -- xi ∈ [t i, t(i+1)] ∩ [t j, t(j+1)]
      -- Since i < j, t(i+1) ≤ t j unless i+1 = j
      by_contra h_ne
      have h_lt2 : i + 1 < j := by omega
      have : t (i + 1) < t j := ht_inc (i + 1) j h_lt2 (by omega) (by omega)
      linarith
    · intro h_eq; subst h_eq
      -- f(t(i+1)) is in closure of both ed i and ed(i+1)
      -- Need to show cellAdj (ed i) (ed (i+1))
      -- cellAdj requires: isCell (ed i), isCell (ed j), ed i ≠ ed j, closures intersect
      have hei : isEdge (ed i) := hed_isEdge i hi
      have hej : isEdge (ed (i + 1)) := hed_isEdge (i + 1) hj
      have hne : ed i ≠ ed (i + 1) := by
        intro h; exact absurd (hed_inj hi hj h) (by omega)
      have hti1_i : t (i + 1) ∈ {x | t i ≤ x ∧ x ≤ t (i + 1)} :=
        ⟨le_of_lt (ht_inc i (i + 1) (by omega) (by omega) (by omega)), le_refl _⟩
      have hti1_j : t (i + 1) ∈ {x | t (i + 1) ≤ x ∧ x ≤ t (i + 1 + 1)} :=
        ⟨le_refl _, le_of_lt (ht_inc (i + 1) (i + 1 + 1) (by omega) (by omega) (by omega))⟩
      have hfti1_cl_i : f (t (i + 1)) ∈ closure (ed i) := by
        rw [← hed_closure i hi]; exact ⟨t (i + 1), hti1_i, rfl⟩
      have hfti1_cl_j : f (t (i + 1)) ∈ closure (ed (i + 1)) := by
        rw [← hed_closure (i + 1) hj]; exact ⟨t (i + 1), hti1_j, rfl⟩
      exact ⟨isEdge_isCell hei, isEdge_isCell hej,
        hne, f (t (i + 1)), hfti1_cl_i, hfti1_cl_j⟩
  -- Step 7: Apply order_lt_imp_psegment
  obtain ⟨G, hG_edges, hG_ps⟩ :=
    order_lt_imp_psegment ed (N - 1) hN1_pos hed_inj hed_isEdge hed_adj
  -- Step 8: Show segment_end G.edges a b
  -- G.isPsegment gives us exactly two endpoints
  obtain ⟨ea, eb, heab, hea, heb, hend⟩ := hG_ps
  -- Show a and b are endpoints of G
  -- pointI a = f(t 0) ∈ closure(ed 0) and for no other edge
  -- pointI b = f(t(N-2)) ∈ closure(ed(N-2)) and for no other edge
  -- We need: numClosure G.edges a = 1 and numClosure G.edges b = 1
  -- This means: a is endpoint iff pointI a ∈ closure of exactly one edge in G.edges
  -- f(t 0) = pointI a ∈ closure(ed 0) (from hed_closure)
  -- f(t 0) ∉ closure(ed i) for i > 0 (from injectivity of f and ordering of t)
  have ha_in_ed0 : pointI a ∈ closure (ed 0) := by
    rw [← ha]
    have : f (t 0) ∈ f '' {x | t 0 ≤ x ∧ x ≤ t (0 + 1)} :=
      ⟨t 0, ⟨le_refl _, le_of_lt (ht_inc 0 1 (by omega) (by omega) (by omega))⟩, rfl⟩
    rwa [hed_closure 0 (by omega)] at this
  have ha_not_other : ∀ i, i < N - 1 → i ≠ 0 → pointI a ∉ closure (ed i) := by
    intro i hi hne
    rw [← hed_closure i hi]
    intro ⟨x, ⟨hxl, hxr⟩, hfx⟩
    have hx_01 : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (ht_mem i (by omega)).1 hxl,
       le_trans hxr (ht_mem (i + 1) (by omega)).2⟩
    have hfx' : f x = f (t 0) := by rw [ha]; exact hfx
    have hx_eq : x = t 0 := hfi hx_01 (ht_mem 0 (by omega)) hfx'
    subst hx_eq
    linarith [ht_inc 0 i (Nat.pos_of_ne_zero hne) (by omega) (by omega)]
  have hb_in_edN : pointI b ∈ closure (ed (N - 2)) := by
    rw [← hb]
    have hN2_lt : N - 2 < N - 1 := by omega
    have : f (t (N - 1)) ∈ f '' {x | t (N - 2) ≤ x ∧ x ≤ t (N - 2 + 1)} := by
      refine ⟨t (N - 1), ⟨le_of_lt (ht_inc (N - 2) (N - 1) (by omega) (by omega) (by omega)),
        ?_⟩, rfl⟩
      show t (N - 1) ≤ t (N - 2 + 1)
      have : N - 2 + 1 = N - 1 := by omega
      rw [this]
    rwa [hed_closure (N - 2) hN2_lt] at this
  have hb_not_other : ∀ i, i < N - 1 → i ≠ N - 2 → pointI b ∉ closure (ed i) := by
    intro i hi hne
    rw [← hed_closure i hi]
    intro ⟨x, ⟨hxl, hxr⟩, hfx⟩
    have hx_01 : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (ht_mem i (by omega)).1 hxl,
       le_trans hxr (ht_mem (i + 1) (by omega)).2⟩
    have hfx' : f x = f (t (N - 1)) := by rw [hb]; exact hfx
    have hx_eq : x = t (N - 1) := hfi hx_01 (ht_mem (N - 1) (by omega)) hfx'
    subst hx_eq
    linarith [ht_inc (i + 1) (N - 1) (by omega : i + 1 < N - 1) (by omega) (by omega)]
  -- Endpoints of G: numClosure G.edges m = 1 iff pointI m ∈ closure of exactly one edge
  -- G.edges = (Finset.range (N-1)).image ed
  -- The endpoint condition: G.isEndpoint m ↔ numClosure G.edges m = 1
  -- a is endpoint: pointI a ∈ closure(ed 0) only
  -- b is endpoint: pointI b ∈ closure(ed(N-2)) only
  -- We need to relate the endpoints ea, eb to a, b
  -- Since G has exactly 2 endpoints ea, eb with ea ≠ eb,
  -- and a, b are each endpoints, we have {ea, eb} = {a, b}
  have hab_ne : a ≠ b := by
    intro h; subst h
    have := isSimpleArcEnd_distinct harc
    rw [hva, hv'b] at this; exact this rfl
  -- Show G.isEndpoint a
  have hGa : G.isEndpoint a := by
    rw [Segment.isEndpoint]
    -- numClosure G.edges a = card of {e ∈ G.edges | pointI a ∈ closure e}
    -- G.edges = (Finset.range (N-1)).image ed
    -- pointI a ∈ closure(ed 0) and ∉ closure(ed i) for i ≠ 0
    -- So exactly one edge: ed 0
    rw [hG_edges]
    show numClosure ((Finset.range (N - 1)).image ed) a = 1
    simp only [numClosure, incidentEdges]
    -- Need to show the filter has exactly one element
    have : @Finset.filter _ (fun e => pointI a ∈ closure e) (Classical.decPred _)
        ((Finset.range (N - 1)).image ed) = {ed 0} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hcl⟩
        by_contra h
        exact ha_not_other i hi (fun h0 => h (by rw [h0])) hcl
      · intro h; subst h
        exact ⟨⟨0, by omega, rfl⟩, ha_in_ed0⟩
    rw [this]; simp
  -- Show G.isEndpoint b
  have hGb : G.isEndpoint b := by
    rw [Segment.isEndpoint, hG_edges]
    show numClosure ((Finset.range (N - 1)).image ed) b = 1
    simp only [numClosure, incidentEdges]
    have : @Finset.filter _ (fun e => pointI b ∈ closure e) (Classical.decPred _)
        ((Finset.range (N - 1)).image ed) = {ed (N - 2)} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hcl⟩
        by_contra h
        exact hb_not_other i hi (fun hN => h (by rw [hN])) hcl
      · intro h; subst h
        exact ⟨⟨N - 2, by omega, rfl⟩, hb_in_edN⟩
    rw [this]; simp
  -- Construct segment_end
  -- G has exactly 2 endpoints ea, eb with ea ≠ eb
  -- a and b are both endpoints, so {a, b} ⊆ {ea, eb}
  -- Since a ≠ b and ea ≠ eb, we get {a, b} = {ea, eb}
  have h_seg : segment_end G.edges a b := by
    refine ⟨G, rfl, hGa, hGb, hab_ne, fun m hm => ?_⟩
    -- We know: a = ea ∨ a = eb, b = ea ∨ b = eb, m = ea ∨ m = eb
    -- and a ≠ b, ea ≠ eb
    -- First establish a bijection between {a,b} and {ea,eb}
    rcases hend a hGa with ha_ea | ha_eb
    · -- a = ea
      rcases hend b hGb with hb_ea | hb_eb
      · -- b = ea, but a = ea so a = b, contradiction
        exact False.elim (absurd (ha_ea.trans hb_ea.symm) hab_ne)
      · -- a = ea, b = eb
        rcases hend m hm with hm_ea | hm_eb
        · left; exact hm_ea.trans ha_ea.symm
        · right; exact hm_eb.trans hb_eb.symm
    · -- a = eb
      rcases hend b hGb with hb_ea | hb_eb
      · -- a = eb, b = ea
        rcases hend m hm with hm_ea | hm_eb
        · right; exact hm_ea.trans hb_ea.symm
        · left; exact hm_eb.trans ha_eb.symm
      · -- b = eb, a = eb, so a = b, contradiction
        exact False.elim (absurd (ha_eb.trans hb_eb.symm) hab_ne)
  -- Step 9: Show e = closure (⋃₀ ↑G.edges)
  -- e = f '' [0,1] and each sub-interval maps to closure(ed i)
  -- G.edges = (Finset.range (N-1)).image ed
  -- ⋃₀ G.edges = ⋃ i < N-1, ed i
  -- closure(⋃₀ G.edges) = ⋃ i < N-1, closure(ed i) = ⋃ i < N-1, f '' [t i, t(i+1)] = f '' [0,1] = e
  refine ⟨G.edges, a, b, h_seg, hva, hv'b, ?_⟩
  -- Show e = closure (⋃₀ ↑G.edges)
  rw [he]
  apply Set.eq_of_subset_of_subset
  · -- f '' [0,1] ⊆ closure (⋃₀ ↑G.edges)
    rintro _ ⟨s, hs, rfl⟩
    -- Find which sub-interval s belongs to
    by_cases hs1 : s = 1
    · -- s = 1 → f 1 = pointI b ∈ closure(ed(N-2))
      rw [hs1, hf1, hv'b]
      have hmem : ed (N - 2) ∈ (G.edges : Set (Set E2)) := by
        rw [hG_edges]; exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨N - 2, Finset.mem_range.mpr (by omega), rfl⟩)
      exact closure_mono (Set.subset_sUnion_of_mem hmem) hb_in_edN
    · -- s < 1, find the sub-interval containing s
      have hs_lt1 : s < 1 := lt_of_le_of_ne hs.2 hs1
      -- Use the well-ordering of t to find i with t i ≤ s < t(i+1)
      -- Since s ∈ [0,1] and t 0 = 0 (from h0_t0) and t(N-1) = 1 (from h1_tN)
      -- there exists i < N-1 with t i ≤ s ≤ t(i+1)
      have : ∃ i, i < N - 1 ∧ t i ≤ s ∧ s ≤ t (i + 1) := by
        by_contra h_no
        push Not at h_no
        -- s ∈ [0,1], s < 1
        -- t 0 ≤ 0 ≤ s (using h0_t0)
        have h0s : t 0 ≤ s := by rw [← h0_t0]; exact hs.1
        -- Induction: for each i, if t i ≤ s then s < t i (contradiction) or s > t(i+1)
        have h_step : ∀ i, i < N - 1 → t i ≤ s → t (i + 1) < s := h_no
        -- Apply this repeatedly: t 0 ≤ s → t 1 < s → t 2 < s → ... → t(N-1) < s
        have : ∀ i, i < N → t i ≤ s := by
          intro i; induction i with
          | zero => intro; exact h0s
          | succ n ih =>
            intro hn
            exact le_of_lt (h_step n (by omega) (ih (by omega)))
        linarith [this (N - 1) (by omega), h1_tN]
      obtain ⟨i, hi, hle, hri⟩ := this
      -- f s ∈ f '' [t i, t(i+1)] = closure(ed i)
      have hfs_cl : f s ∈ closure (ed i) := by
        rw [← hed_closure i hi]
        exact ⟨s, ⟨hle, hri⟩, rfl⟩
      have hmem_i : ed i ∈ (G.edges : Set (Set E2)) := by
        rw [hG_edges]; exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
      exact closure_mono (Set.subset_sUnion_of_mem hmem_i) hfs_cl
  · -- closure (⋃₀ ↑G.edges) ⊆ f '' [0,1]
    -- ⋃₀ G.edges ⊆ f '' [0,1], and f '' [0,1] is compact hence closed
    apply closure_minimal
    · intro x hx
      obtain ⟨S, hS_mem, hx_S⟩ := Set.mem_sUnion.mp hx
      have hS_edge : S ∈ G.edges := Finset.mem_coe.mp hS_mem
      rw [hG_edges] at hS_edge
      obtain ⟨i, hi_range, rfl⟩ := Finset.mem_image.mp hS_edge
      rw [Finset.mem_range] at hi_range
      -- x ∈ ed i ⊆ closure(ed i) = f '' [t i, t(i+1)] ⊆ f '' [0,1]
      have : x ∈ closure (ed i) := subset_closure hx_S
      rw [← hed_closure i hi_range] at this
      obtain ⟨s, ⟨hsl, hsr⟩, rfl⟩ := this
      exact ⟨s, ⟨le_trans (ht_mem i (by omega)).1 hsl,
        le_trans hsr (ht_mem (i + 1) (by omega)).2⟩, rfl⟩
    · exact (IsCompact.image isCompact_Icc hfc).isClosed

/-! ## §Y.13 Psegment closure subset -/

/-- HOL Light: `psegment_cls` (line 48147).
Image of cls under pointI is contained in the closure of the union of edges. -/
theorem psegment_cls (S : Finset (Set E2))
    (_hps : ∃ G : Segment, G.edges = S ∧ G.isPsegment) :
    pointI '' (cls S : Set (ℤ × ℤ)) ⊆ closure (⋃₀ ↑S) := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨e, heS, hm_cl⟩ := hm
  exact closure_mono
    (Set.subset_sUnion_of_mem (Finset.mem_coe.mpr heS)) hm_cl

/-! ## §Y.14 THE MAIN THEOREM: planar graphs are rectagonal -/

/-- HOL Light: `planar_graph_rectagonal` (line 48163).
Every planar graph with finitely many edges and vertices, a nonempty edge set,
and degree at most 4 at every vertex is rectagonal. -/
theorem planar_graph_rectagonal {V E₀ : Type*} (G : HolGraph V E₀)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    isRectagonalGraph G := by
  -- Step 1: Get integer model H with eps-hyperplane support
  obtain ⟨H, Eset, hiso_GH, hgood, hEfin, hedge_cov, hvert_eps, hform, hint⟩ :=
    graph_int_model G hplanar hfin_e hfin_v hne hdeg
  -- Step 2: For each edge e of H, apply simple_arc_finite_lemma4
  -- to get segment_end decomposition
  have hedge_seg : ∀ e ∈ H.edgeSet, ∃ (S : Finset (Set E2)) (a b : ℤ × ℤ),
      segment_end S a b ∧
      H.inc e = {pointI a, pointI b} ∧
      e = closure (⋃₀ ↑S) := by
    intro e he
    -- Get the two endpoints of e
    have hgpg := hgood.1
    obtain ⟨v, v', hv, hv', hvv', harc⟩ := hgpg.edges_are_arcs e he
    -- v, v' are in H.vertexSet
    have hv_vtx : v ∈ H.vertexSet := (H.well_formed e he).1 hv
    have hv'_vtx : v' ∈ H.vertexSet := (H.well_formed e he).1 hv'
    -- Get eps-hyperplane membership for v, v'
    obtain ⟨hv0, hv1⟩ := hvert_eps v hv_vtx
    obtain ⟨hv'0, hv'1⟩ := hvert_eps v' hv'_vtx
    -- e is covered by Eset
    have hcov : e ⊆ ⋃₀ Eset := hedge_cov e he
    -- Apply simple_arc_finite_lemma4
    obtain ⟨S, a, b, hseg, hva, hv'b, heSab⟩ :=
      simple_arc_finite_lemma4 Eset e v v' harc hEfin hcov hv0 hv1 hv'0 hv'1
        hform (fun z eps h => hint z eps h)
    -- Show H.inc e = {pointI a, pointI b}
    -- Since H is a good plane graph, for edge e with v, v' ∈ H.inc e and v ≠ v',
    -- inc e has exactly 2 elements: v and v'
    -- We know v = pointI a and v' = pointI b
    have hinc_eq : H.inc e = {pointI a, pointI b} := by
      have hncard := (H.well_formed e he).2
      rw [← hva, ← hv'b]
      have : H.inc e = {v, v'} := by
        rw [Set.ncard_eq_two] at hncard
        obtain ⟨x, y, hxy, hinc⟩ := hncard
        rw [hinc]; rw [hinc] at hv hv'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
        rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
        · exact absurd rfl hvv'
        · rfl
        · simp [Set.pair_comm]
        · exact absurd rfl hvv'
      exact this
    exact ⟨S, a, b, hseg, hinc_eq, heSab⟩
  -- Step 3: Extract choice functions for S, a, b
  -- For each edge e, choose S(e), a(e), b(e)
  have h_choose : ∀ e ∈ H.edgeSet, ∃ (S : Finset (Set E2)) (a b : ℤ × ℤ),
      segment_end S a b ∧
      H.inc e = {pointI a, pointI b} ∧
      e = closure (⋃₀ ↑S) := hedge_seg
  -- Use classical choice to get functions
  classical
  set Se : Set E2' → Finset (Set E2) := fun e =>
    if h : e ∈ H.edgeSet then (h_choose e h).choose
    else ∅ with hSe_def
  set ae : Set E2' → ℤ × ℤ := fun e =>
    if h : e ∈ H.edgeSet then (h_choose e h).choose_spec.choose
    else (0, 0) with hae_def
  set be : Set E2' → ℤ × ℤ := fun e =>
    if h : e ∈ H.edgeSet then (h_choose e h).choose_spec.choose_spec.choose
    else (0, 0) with hbe_def
  have hSe_prop : ∀ e ∈ H.edgeSet,
      segment_end (Se e) (ae e) (be e) ∧
      H.inc e = {pointI (ae e), pointI (be e)} ∧
      e = closure (⋃₀ ↑(Se e)) := by
    intro e he
    have : Se e = (h_choose e he).choose := dif_pos he
    have : ae e = (h_choose e he).choose_spec.choose := dif_pos he
    have : be e = (h_choose e he).choose_spec.choose_spec.choose := dif_pos he
    rw [‹Se e = _›, ‹ae e = _›, ‹be e = _›]
    exact (h_choose e he).choose_spec.choose_spec.choose_spec
  -- Step 4: Each vertex of H is pointI of some integer pair
  have hvert_int : ∀ v ∈ H.vertexSet, ∃ m : ℤ × ℤ, v = pointI m := by
    intro v hv
    obtain ⟨hv0, hv1⟩ := hvert_eps v hv
    obtain ⟨j0, hj0⟩ := hint _ _ hv0
    obtain ⟨j1, hj1⟩ := hint _ _ hv1
    -- v 0 = -↑j0 and v 1 = -↑j1
    refine ⟨(-↑j0, -↑j1), ?_⟩
    ext i; fin_cases i
    · simp? [pointI, point]; exact hj0
    · simp? [pointI, point]; exact hj1
  -- Step 5: Choose vertex map mv : vertex → ℤ × ℤ
  set mv : E2' → ℤ × ℤ := fun v =>
    if h : v ∈ H.vertexSet then (hvert_int v h).choose
    else (0, 0) with hmv_def
  have hmv_prop : ∀ v ∈ H.vertexSet, v = pointI (mv v) := by
    intro v hv
    have : mv v = (hvert_int v hv).choose := dif_pos hv
    rw [this]; exact (hvert_int v hv).choose_spec
  -- Step 6: Construct the rectagonal graph J
  -- J has vertices = mv '' H.vertexSet, edges = Se '' H.edgeSet
  -- incidence = endpoint function
  -- We need to show isRectagonGraph J ∧ GraphIsomorphic J G
  -- Through H: J iso H iso G (by transitivity)
  -- The endpoints of Se e are ae e and be e (from segment_end)
  have hSe_endpoints : ∀ e ∈ H.edgeSet,
      {m : ℤ × ℤ | numClosure (Se e) m = 1} = {ae e, be e} := by
    intro e he
    obtain ⟨hseg, hinc, heq⟩ := hSe_prop e he
    obtain ⟨G, hGe, hGa, hGb, hab, huniq⟩ := hseg
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      rw [← hGe] at hm
      have : G.isEndpoint m := hm
      exact huniq m this
    · intro hm
      rcases hm with rfl | rfl
      · rw [← hGe]; exact hGa
      · rw [← hGe]; exact hGb
  -- ae e ≠ be e (from segment_end)
  have hab_ne : ∀ e ∈ H.edgeSet, ae e ≠ be e := by
    intro e he
    obtain ⟨hseg, _, _⟩ := hSe_prop e he
    exact hseg.choose_spec.2.2.2.1
  -- ae e and be e are in mv '' H.vertexSet
  have hae_vtx : ∀ e ∈ H.edgeSet, ae e ∈ mv '' H.vertexSet := by
    intro e he
    obtain ⟨_, hinc, _⟩ := hSe_prop e he
    have hvtx : pointI (ae e) ∈ H.vertexSet := by
      apply (H.well_formed e he).1; rw [hinc]; exact Set.mem_insert _ _
    have hmveq : mv (pointI (ae e)) = ae e :=
      pointI_injective (hmv_prop _ hvtx).symm
    exact ⟨pointI (ae e), hvtx, hmveq⟩
  have hbe_vtx : ∀ e ∈ H.edgeSet, be e ∈ mv '' H.vertexSet := by
    intro e he
    obtain ⟨_, hinc, _⟩ := hSe_prop e he
    have hvtx : pointI (be e) ∈ H.vertexSet :=
      (H.well_formed e he).1 (hinc ▸ Set.mem_insert_of_mem _ rfl)
    have hmveq : mv (pointI (be e)) = be e :=
      pointI_injective (hmv_prop _ hvtx).symm
    exact ⟨pointI (be e), hvtx, hmveq⟩
  -- mv is injective on H.vertexSet
  have hmv_inj : Set.InjOn mv H.vertexSet := by
    intro v₁ hv₁ v₂ hv₂ heq
    rw [hmv_prop v₁ hv₁, hmv_prop v₂ hv₂]
    exact congrArg pointI heq
  -- Se is injective on H.edgeSet
  have hSe_inj : Set.InjOn Se H.edgeSet := by
    intro e₁ he₁ e₂ he₂ heq
    obtain ⟨_, _, he1_eq⟩ := hSe_prop e₁ he₁
    obtain ⟨_, _, he2_eq⟩ := hSe_prop e₂ he₂
    rw [he1_eq, he2_eq, heq]
  -- Construct graph J
  set J : HolGraph (ℤ × ℤ) (Finset (Set E2)) :=
    { vertexSet := mv '' H.vertexSet
      edgeSet := Se '' H.edgeSet
      inc := fun S => {m | numClosure S m = 1}
      well_formed := by
        intro S hS
        obtain ⟨e, he, rfl⟩ := hS
        constructor
        · -- inc ⊆ vertexSet
          rw [hSe_endpoints e he]
          intro m hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with rfl | rfl
          · exact hae_vtx e he
          · exact hbe_vtx e he
        · -- ncard = 2
          rw [hSe_endpoints e he]
          exact Set.ncard_pair (hab_ne e he) } with hJ_def
  refine ⟨J, ?_, ?_⟩
  · -- isRectagonGraph J
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (a) Each edge has segment_end
      intro S hS
      obtain ⟨e, he, rfl⟩ := hS
      obtain ⟨hseg, _, _⟩ := hSe_prop e he
      exact ⟨ae e, be e, hseg⟩
    · -- (b) inc = endpoint set (by construction)
      intro S hS; rfl
    · -- (c) Edges are disjoint
      intro S₁ hS₁ S₂ hS₂ hne
      obtain ⟨e₁, he₁, rfl⟩ := hS₁
      obtain ⟨e₂, he₂, rfl⟩ := hS₂
      -- e₁ ≠ e₂ (since Se is injective and Se e₁ ≠ Se e₂)
      have hne_edge : e₁ ≠ e₂ := fun h => hne (congrArg Se h)
      -- If two distinct Finsets Se e₁ and Se e₂ share a common cell u,
      -- then u ⊆ e₁ ∩ e₂ ⊆ H.vertexSet (by edges_disjoint_interior).
      -- But u is an edge cell (h_edge or v_edge), which cannot contain a lattice
      -- point (hEdge_not_pointI / vEdge_not_pointI). Contradiction.
      rw [Finset.disjoint_left]
      intro u hu₁ hu₂
      -- u is an edge cell (from segment_end)
      obtain ⟨hseg₁, _, heq₁⟩ := hSe_prop e₁ he₁
      obtain ⟨hseg₂, _, heq₂⟩ := hSe_prop e₂ he₂
      have hG₁ := hseg₁.choose_spec.1
      have hG₂ := hseg₂.choose_spec.1
      have hedge₁ : isEdge u := by
        rw [← hG₁] at hu₁; exact hseg₁.choose.all_edges u hu₁
      -- u ⊆ e₁: u ∈ Se e₁ → u ⊆ ⋃₀ Se e₁ ⊆ closure(⋃₀ Se e₁) = e₁
      have hu_sub₁ : u ⊆ e₁ := by
        have : (u : Set E2) ⊆ ⋃₀ ↑(Se e₁) :=
          Set.subset_sUnion_of_mem (Finset.mem_coe.mpr hu₁)
        calc (u : Set E2) ⊆ ⋃₀ ↑(Se e₁) := this
          _ ⊆ closure (⋃₀ ↑(Se e₁)) := subset_closure
          _ = e₁ := heq₁.symm
      have hu_sub₂ : u ⊆ e₂ := by
        have : (u : Set E2) ⊆ ⋃₀ ↑(Se e₂) :=
          Set.subset_sUnion_of_mem (Finset.mem_coe.mpr hu₂)
        calc (u : Set E2) ⊆ ⋃₀ ↑(Se e₂) := this
          _ ⊆ closure (⋃₀ ↑(Se e₂)) := subset_closure
          _ = e₂ := heq₂.symm
      -- u ⊆ e₁ ∩ e₂ ⊆ H.vertexSet
      have hu_vtx : u ⊆ H.vertexSet :=
        Set.subset_inter hu_sub₁ hu_sub₂ |>.trans
          (hgood.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne_edge)
      -- u is nonempty
      obtain ⟨z, hz⟩ := cell_nonempty (isEdge_isCell hedge₁)
      -- z ∈ H.vertexSet, so z = pointI m for some m
      obtain ⟨m, hm⟩ := hvert_int z (hu_vtx hz)
      -- But z ∈ u which is an h_edge or v_edge, contradicting pointI not in edge cells
      rcases hedge₁ with ⟨p, hp⟩ | ⟨p, hp⟩
      · exact hEdge_not_pointI p m (hp ▸ hm ▸ hz)
      · exact vEdge_not_pointI p m (hp ▸ hm ▸ hz)
    · -- (d) cls intersection = endpoint intersection
      -- cls(Se e₁) ∩ cls(Se e₂) = {m | numClosure (Se e₁) m = 1} ∩ {m | numClosure (Se e₂) m = 1}
      intro S₁ hS₁ S₂ hS₂ hne
      obtain ⟨e₁, he₁, rfl⟩ := hS₁
      obtain ⟨e₂, he₂, rfl⟩ := hS₂
      have hne_edge : e₁ ≠ e₂ := fun h => hne (congrArg Se h)
      ext m
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · -- ⊆: if m ∈ cls(Se e₁) ∩ cls(Se e₂), then numClosure = 1 for both
        intro ⟨hm₁, hm₂⟩
        -- pointI m ∈ closure(⋃₀ Se e₁) = e₁ (by psegment_cls)
        obtain ⟨hseg₁, hinc₁, heq₁⟩ := hSe_prop e₁ he₁
        obtain ⟨hseg₂, hinc₂, heq₂⟩ := hSe_prop e₂ he₂
        have hps₁ : ∃ G : Segment, G.edges = Se e₁ ∧ G.isPsegment := by
          obtain ⟨G, hGe, hGa, hGb, hab, huniq⟩ := hseg₁
          exact ⟨G, hGe, ae e₁, be e₁, hab, hGa, hGb, huniq⟩
        have hps₂ : ∃ G : Segment, G.edges = Se e₂ ∧ G.isPsegment := by
          obtain ⟨G, hGe, hGa, hGb, hab, huniq⟩ := hseg₂
          exact ⟨G, hGe, ae e₂, be e₂, hab, hGa, hGb, huniq⟩
        have hpI₁ : pointI m ∈ closure (⋃₀ ↑(Se e₁)) :=
          psegment_cls (Se e₁) hps₁ ⟨m, hm₁, rfl⟩
        have hpI₂ : pointI m ∈ closure (⋃₀ ↑(Se e₂)) :=
          psegment_cls (Se e₂) hps₂ ⟨m, hm₂, rfl⟩
        -- pointI m ∈ e₁ ∩ e₂ ⊆ H.vertexSet
        have hpI_in₁ : pointI m ∈ e₁ := heq₁ ▸ hpI₁
        have hpI_in₂ : pointI m ∈ e₂ := heq₂ ▸ hpI₂
        have hpI_vtx : pointI m ∈ H.vertexSet :=
          hgood.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne_edge
            ⟨hpI_in₁, hpI_in₂⟩
        -- H.inc eᵢ = {pointI (ae eᵢ), pointI (be eᵢ)}
        -- pointI m ∈ eᵢ and pointI m ∈ H.vertexSet → pointI m ∈ H.inc eᵢ
        -- (by vertex_on_edge from IsPlaneGraph)
        have hm_inc₁ : pointI m ∈ H.inc e₁ :=
          hgood.1.vertex_on_edge e₁ he₁ (pointI m) hpI_vtx hpI_in₁
        have hm_inc₂ : pointI m ∈ H.inc e₂ :=
          hgood.1.vertex_on_edge e₂ he₂ (pointI m) hpI_vtx hpI_in₂
        -- H.inc eᵢ = {pointI (ae eᵢ), pointI (be eᵢ)}
        -- So m = ae eᵢ or m = be eᵢ
        rw [hinc₁] at hm_inc₁
        rw [hinc₂] at hm_inc₂
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_inc₁ hm_inc₂
        -- m is endpoint of Se e₁ and Se e₂
        -- numClosure(Se eᵢ) m = 1 iff m ∈ {ae eᵢ, be eᵢ}
        have hm_ep₁ : m ∈ ({ae e₁, be e₁} : Set (ℤ × ℤ)) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases hm_inc₁ with h | h
          · left; exact pointI_injective h
          · right; exact pointI_injective h
        have hm_ep₂ : m ∈ ({ae e₂, be e₂} : Set (ℤ × ℤ)) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases hm_inc₂ with h | h
          · left; exact pointI_injective h
          · right; exact pointI_injective h
        exact ⟨(hSe_endpoints e₁ he₁ ▸ hm_ep₁ : m ∈ {m | numClosure (Se e₁) m = 1}),
               (hSe_endpoints e₂ he₂ ▸ hm_ep₂ : m ∈ {m | numClosure (Se e₂) m = 1})⟩
      · -- ⊇: if numClosure = 1 for both, then m ∈ cls both
        intro ⟨hm₁, hm₂⟩
        obtain ⟨hseg₁, _, _⟩ := hSe_prop e₁ he₁
        obtain ⟨hseg₂, _, _⟩ := hSe_prop e₂ he₂
        have hall₁ : ∀ u ∈ Se e₁, isEdge u := by
          intro u hu; rw [← hseg₁.choose_spec.1] at hu; exact hseg₁.choose.all_edges u hu
        have hall₂ : ∀ u ∈ Se e₂, isEdge u := by
          intro u hu; rw [← hseg₂.choose_spec.1] at hu; exact hseg₂.choose.all_edges u hu
        exact ⟨endpoint_subset_cls (Se e₁) hall₁ hm₁,
               endpoint_subset_cls (Se e₂) hall₂ hm₂⟩
  · -- GraphIsomorphic J G
    -- Build GraphIsomorphic J H, then compose with GraphIsomorphic H G
    -- Helper: all edges of Se e are isEdge
    have hSe_all_edges : ∀ e ∈ H.edgeSet, ∀ u ∈ Se e, isEdge u := by
      intro e he u hu
      obtain ⟨hseg, _, _⟩ := hSe_prop e he
      rw [← hseg.choose_spec.1] at hu; exact hseg.choose.all_edges u hu
    -- Helper: mv (pointI m) = m for all m in mv '' H.vertexSet
    have hmv_pointI : ∀ v ∈ H.vertexSet, mv (pointI (mv v)) = mv v := by
      intro v hv
      have h1 : pointI (mv v) = v := (hmv_prop v hv).symm
      rw [h1]
    -- Helper: pointI (mv v) = v for all v in H.vertexSet
    have hpointI_mv : ∀ v ∈ H.vertexSet, pointI (mv v) = v := by
      intro v hv; exact (hmv_prop v hv).symm
    -- Helper: closure (⋃₀ ↑(Se e)) = e for all e in H.edgeSet
    have hclosure_Se : ∀ e ∈ H.edgeSet, closure (⋃₀ ↑(Se e)) = e := by
      intro e he; exact (hSe_prop e he).2.2.symm
    have hiso_JH : GraphIsomorphic J H := by
      constructor
      exact {
        vertexMap := pointI
        edgeMap := fun S => closure (⋃₀ ↑S)
        vertexBij := by
          refine ⟨?_, ?_, ?_⟩
          · intro m hm
            obtain ⟨v, hv, rfl⟩ := hm
            rw [hpointI_mv v hv]; exact hv
          · intro m₁ _ m₂ _ h; exact pointI_injective h
          · intro v hv; exact ⟨mv v, ⟨v, hv, rfl⟩, hpointI_mv v hv⟩
        edgeBij := by
          refine ⟨?_, ?_, ?_⟩
          · intro S hS
            obtain ⟨e, he, rfl⟩ := hS
            simp only; rw [hclosure_Se e he]; exact he
          · intro S₁ hS₁ S₂ hS₂ heq
            obtain ⟨e₁, he₁, rfl⟩ := hS₁
            obtain ⟨e₂, he₂, rfl⟩ := hS₂
            simp only at heq
            have : e₁ = e₂ := (hclosure_Se e₁ he₁).symm.trans heq |>.trans (hclosure_Se e₂ he₂)
            exact congrArg Se this
          · intro e he
            exact ⟨Se e, ⟨e, he, rfl⟩, by simp only; exact hclosure_Se e he⟩
        preserves_inc := by
          intro S hS
          obtain ⟨e, he, rfl⟩ := hS
          obtain ⟨_, hinc, heq⟩ := hSe_prop e he
          change H.inc (closure (⋃₀ ↑(Se e))) = pointI '' {m | numClosure (Se e) m = 1}
          rw [hclosure_Se e he]
          show H.inc e = pointI '' {m | numClosure (Se e) m = 1}
          rw [hSe_endpoints e he, Set.image_pair, hinc]
      }
    -- Compose: J iso H, then H iso G (from symmetry of G iso H)
    -- Need Nonempty instances for graphIsomorphic_symm
    have hJ_vtx_ne : J.vertexSet.Nonempty := by
      obtain ⟨e, he⟩ := hne
      have he' := hiso_GH.some.edgeBij.mapsTo he
      have h2 := (H.well_formed _ he').2
      rw [Set.ncard_eq_two] at h2
      obtain ⟨v, _, _, hinc_eq⟩ := h2
      have hv_vtx : v ∈ H.vertexSet :=
        (H.well_formed _ he').1 (hinc_eq ▸ Set.mem_insert _ _)
      exact ⟨mv v, v, hv_vtx, rfl⟩
    have hJ_edg_ne : J.edgeSet.Nonempty := by
      obtain ⟨e, he⟩ := hne
      have he' := hiso_GH.some.edgeBij.mapsTo he
      exact ⟨Se _, _, he', rfl⟩
    haveI : Nonempty J.vertexSet := hJ_vtx_ne.to_subtype
    haveI : Nonempty J.edgeSet := hJ_edg_ne.to_subtype
    -- graphIsomorphic_symm needs Nonempty V and Nonempty E₀
    have he_G := hne.choose_spec
    have hv_G : G.vertexSet.Nonempty := by
      have h2 := (G.well_formed _ he_G).2
      rw [Set.ncard_eq_two] at h2
      obtain ⟨v, _, _, _⟩ := h2
      exact ⟨v, (G.well_formed _ he_G).1 (by rw [‹G.inc _ = _›]; exact Set.mem_insert _ _)⟩
    haveI : Nonempty V := ⟨hv_G.choose⟩
    haveI : Nonempty E₀ := ⟨hne.choose⟩
    exact graphIsomorphic_trans hiso_JH (graphIsomorphic_symm hiso_GH)

/-! ## §Y.15 K₃,₃ is not planar -/

-- `cartesian_finite` (line 48500): Cartesian product of finite sets is finite.
-- Already in Mathlib as `Set.Finite.prod`.

-- `three_t_finite` / `three_t_size3` (line 48510, 48522):
-- finite type with 3 elements. We use `Fin 3` in Lean.

/-- HOL Light: `k33_nonplanar` (line 48541).
The complete bipartite graph K₃,₃ is not planar.
This follows from `planar_graph_rectagonal` and `rectagon_graph_k33_false`. -/
theorem k33_nonplanar : ¬IsPlanarGraph K33 := by
  intro hplanar
  have hfin_e : K33.edgeSet.Finite :=
    (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _
        (Set.finite_singleton _))))))))).subset
      (fun e he => he)
  have hfin_v : K33.vertexSet.Finite :=
    (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _
        (Set.finite_singleton _)))))).subset (fun v hv => hv)
  have hne : K33.edgeSet.Nonempty := ⟨{1, 10}, Set.mem_insert _ _⟩
  have hdeg : ∀ v, (K33.edgeAround v).ncard ≤ 4 := by
    intro v
    by_cases hv : v ∈ K33.vertexSet
    · -- v is one of {1, 2, 3, 10, 20, 30}; each has degree 3 ≤ 4
      simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      have hfin_ea : (K33.edgeAround v).Finite := hfin_e.subset (fun e h => h.1)
      -- We show edgeAround v ⊆ a concrete 3-element set, then bound its ncard
      suffices ∃ (a b c : Finset ℕ), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          K33.edgeAround v ⊆ ({a, b, c} : Set (Finset ℕ)) by
        obtain ⟨a, b, c, hab, hac, hbc, hsub⟩ := this
        apply le_trans (Set.ncard_le_ncard hsub
          (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))))
        rw [Set.ncard_insert_of_notMem (by simp [Set.mem_insert_iff, hab, hac])
            (Set.Finite.insert _ (Set.finite_singleton _)),
          Set.ncard_insert_of_notMem (by simp [hbc]) (Set.finite_singleton _),
          Set.ncard_singleton]
        omega
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨{1,10},{1,20},{1,30}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
      · exact ⟨{2,10},{2,20},{2,30}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
      · exact ⟨{3,10},{3,20},{3,30}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
      · exact ⟨{1,10},{2,10},{3,10}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
      · exact ⟨{1,20},{2,20},{3,20}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
      · exact ⟨{1,30},{2,30},{3,30}, by decide, by decide, by decide, fun e he => by
          simp only [HolGraph.edgeAround, K33, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_coe] at he
          rcases he.1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp_all (config := { decide := true })⟩
    · rw [HolGraph.edgeAround_empty K33 v hv, Set.ncard_empty]
      exact Nat.zero_le _
  exact rectagon_graph_k33_false (planar_graph_rectagonal K33 hplanar hfin_e hfin_v hne hdeg)

end JordanCurveTheorem
