/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionY_GridCells

/-!
# Section Z: Complement of a Simple Arc is Connected
## HOL Light: Section Z (Lines 48690–50960)

Grid approximation to curves and connectivity of unions of edge-connected
components.  The key construction wraps an arc image in a grid of cells
(`grid33`, `grid`) and the main theorem `conn2_sequence` establishes that
a point in the unbounded set of each pair of consecutive grids remains in
the unbounded set of the full union.

### Key definitions
- `grid33`: 3×3 rectangle grid centred at an integer point
- `grid`: union of `grid33` cells along an arc's floor-image

### Key theorems
- `grid33_conn2`, `grid_conn2`: grid cells are 2-connected
- `floor_abs`, `d_euclid_floor`: floor–distance bridge lemmas
- `grid_image_bounded`: the arc image avoids the unbounded set of its grid
- `conn2_sequence_lemma1`–`conn2_sequence_lemma5`: sequence connectivity lemmas
- `conn2_sequence`: **Main theorem** — unboundedness propagates through a
  sequence of 2-connected edge sets
-/

namespace JordanCurveTheorem

/-! ## §Z.1 Grid definitions -/

/-- HOL Light: `grid33` (line 48696).
    3×3 rectangle grid centred at integer point `m`. -/
noncomputable def grid33 (m : ℤ × ℤ) : Finset (Set E2) :=
  rectangle_grid (m.1 - 1, m.2 - 1) (m.1 + 2, m.2 + 2)

/-- HOL Light: `grid` (line 48700).
    Union of `grid33` cells along the floor-images of an arc `f` sampled at
    `N + 1` evenly spaced points. -/
noncomputable def grid (f : ℝ → E2) (N : ℕ) : Finset (Set E2) :=
  (Finset.range (N + 1)).biUnion fun i =>
    grid33 (⌊(f (↑i / ↑N)) 0⌋, ⌊(f (↑i / ↑N)) 1⌋)

/-! ## §Z.2 Basic grid properties -/

/-- HOL Light: `grid33_conn2` (line 48705). -/
theorem grid33_conn2 (m : ℤ × ℤ) : conn2 (grid33 m) := by
  simp only [grid33,
    show m.1 + 2 = (m.1 - 1) + ↑(2 + 1) by push_cast; ring,
    show m.2 + 2 = (m.2 - 1) + ↑(2 + 1) by push_cast; ring]
  exact rectangle_grid_conn2 2 2 _

-- HOL Light: `grid_finite` (line 48724).
-- Not applicable to Lean: `grid f N` is a `Finset`, hence inherently finite.

/-- HOL Light: `grid33_edge` (line 48739). -/
theorem grid33_edge (m : ℤ × ℤ) : ∀ e ∈ grid33 m, isEdge e := by
  intro e he; exact rectangle_grid_edge _ _ e he

/-- HOL Light: `grid_edge` (line 48746). -/
theorem grid_edge (f : ℝ → E2) (N : ℕ) : ∀ e ∈ grid f N, isEdge e := by
  intro e he
  simp only [grid, Finset.mem_biUnion] at he
  obtain ⟨i, _, hi⟩ := he
  exact grid33_edge _ e hi

/-! ## §Z.3 Floor lemmas -/

/-- HOL Light: `floor_add_num` (line 48771).
    Mathlib equivalent: `Int.floor_add_natCast`. -/
theorem floor_add_num (x : ℝ) (m : ℕ) : ⌊x + ↑m⌋ = ⌊x⌋ + (↑m : ℤ) :=
  Int.floor_add_natCast x m

/-- HOL Light: `floor_abs` (line 48781). -/
theorem floor_abs (x y : ℝ) (m : ℕ) (h : |x - y| ≤ ↑m) :
    |(⌊x⌋ : ℤ) - ⌊y⌋| ≤ ↑m := by
  rw [abs_le] at h
  rw [abs_le]
  constructor
  · have := Int.floor_le_floor (show y ≤ x + ↑m by linarith)
    rw [Int.floor_add_natCast] at this; omega
  · have := Int.floor_le_floor (show x ≤ y + ↑m by linarith)
    rw [Int.floor_add_natCast] at this; omega

/-- HOL Light: `d_euclid_floor` (line 48818). -/
theorem d_euclid_floor (x y : E2) (i : Fin 2) (h : dist x y < 1) :
    |(⌊x i⌋ : ℤ) - ⌊y i⌋| ≤ 1 := by
  have hle : |x i - y i| ≤ 1 := by
    calc |x i - y i| = ‖(x - y) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) i
    _ = dist x y := (dist_eq_norm x y).symm
    _ ≤ 1 := le_of_lt h
  have := floor_abs (x i) (y i) 1 (by push_cast; exact hle)
  simpa using this

-- HOL Light: `real_eq_div` (line 48846).
-- Mathlib equivalent: `div_eq_iff`.

/-! ## §Z.4 Grid connectivity -/

/-- Helper: an hEdge belongs to any grid33 whose center is within ℤ-distance 1. -/
private theorem hEdge_mem_grid33 {a b : ℤ × ℤ}
    (h0 : |a.1 - b.1| ≤ 1) (h1 : |a.2 - b.2| ≤ 1) :
    hEdge a ∈ grid33 b := by
  simp only [grid33]
  rw [rectangle_grid_h]
  rw [abs_le] at h0 h1
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Helper: extending a biUnion of conn2 edge-sets by one more conn2 edge-set
    that shares an edge with it. -/
private theorem conn2_biUnion_step (G : ℕ → Finset (Set E2)) (k : ℕ)
    (hconn : conn2 ((Finset.range (k + 1)).biUnion G))
    (hconnNew : conn2 (G (k + 1)))
    (hEdgeG : ∀ i e, e ∈ G i → isEdge e)
    (hne : (G (k + 1) ∩ (Finset.range (k + 1)).biUnion G).Nonempty) :
    conn2 ((Finset.range (k + 2)).biUnion G) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, Finset.range_add_one, Finset.biUnion_insert]
  exact conn2_union_edge (hEdgeG _)
    (fun e he => by rw [Finset.mem_biUnion] at he; obtain ⟨i, _, hi⟩ := he; exact hEdgeG i e hi)
    hconnNew hconn hne

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: inductive proof over a `biUnion` with complex `grid33` membership
-- goals; repeated `isDefEq` checks on floor expressions dominate elaboration cost.
/-- HOL Light: `grid_conn2_induct_lemma` (line 48860). -/
theorem grid_conn2_induct_lemma (k : ℕ) (f : ℝ → E2) (N : ℕ) (hk : k ≤ N)
    (hdist : ∀ i, i < N → dist (f (↑i / ↑N)) (f (↑(i + 1) / ↑N)) < 1) :
    conn2 ((Finset.range (k + 1)).biUnion fun i =>
      grid33 (⌊(f (↑i / ↑N)) 0⌋, ⌊(f (↑i / ↑N)) 1⌋)) := by
  induction k with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.range_one, Finset.singleton_biUnion]
    exact grid33_conn2 _
  | succ k ih =>
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    have hkN : k < N := Nat.lt_of_succ_le hk
    specialize ih hk'
    -- Pre-compute membership facts (use wildcards to avoid expensive isDefEq on dist)
    have h0 := d_euclid_floor _ _ 0 (hdist k hkN)
    have h1 := d_euclid_floor _ _ 1 (hdist k hkN)
    have hmemNew : hEdge (⌊(f (↑k / ↑N)) 0⌋, ⌊(f (↑k / ↑N)) 1⌋) ∈
        grid33 (⌊(f (↑(k + 1) / ↑N)) 0⌋, ⌊(f (↑(k + 1) / ↑N)) 1⌋) :=
      hEdge_mem_grid33 (by simpa using h0) (by simpa using h1)
    have hmemOld : hEdge (⌊(f (↑k / ↑N)) 0⌋, ⌊(f (↑k / ↑N)) 1⌋) ∈
        grid33 (⌊(f (↑k / ↑N)) 0⌋, ⌊(f (↑k / ↑N)) 1⌋) :=
      hEdge_mem_grid33 (by simp) (by simp)
    exact conn2_biUnion_step
      (fun i => grid33 (⌊(f (↑i / ↑N)) 0⌋, ⌊(f (↑i / ↑N)) 1⌋))
      k ih (grid33_conn2 _) (fun i e he => grid33_edge _ e he)
      ⟨_, Finset.mem_inter.mpr ⟨hmemNew,
        Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hmemOld⟩⟩⟩

/-- HOL Light: `grid_conn2` (line 48955). -/
theorem grid_conn2 (f : ℝ → E2) (N : ℕ)
    (hdist : ∀ i, i < N → dist (f (↑i / ↑N)) (f (↑(i + 1) / ↑N)) < 1) :
    conn2 (grid f N) :=
  grid_conn2_induct_lemma N f N le_rfl hdist

/-! ## §Z.5 Uniform continuity and partition -/

/-- HOL Light: `simple_arc_uniformly_continuous` (line 49008).
    Wrapper around Mathlib's compact-uniform-continuity. -/
theorem simple_arc_uniformly_continuous (f : ℝ → E2)
    (hf : Continuous f) (_hinj : Set.InjOn f (Set.Icc 0 1)) :
    UniformContinuousOn f (Set.Icc 0 1) :=
  isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn

/-- HOL Light: `num_abs_of_int_mono` (line 49060). -/
theorem num_abs_of_int_mono (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a.natAbs ≤ b.natAbs := by
  omega

/-- HOL Light: `floor_num` (line 49087).
    Mathlib equivalent: `Int.floor_natCast`. -/
theorem floor_num (n : ℕ) : ⌊(↑n : ℝ)⌋ = (↑n : ℤ) :=
  Int.floor_natCast n

/-- HOL Light: `floor_neg_num` (line 49096). -/
theorem floor_neg_num (n : ℕ) : ⌊-(↑n : ℝ)⌋ = -(↑n : ℤ) := by
  rw [Int.floor_neg, Int.ceil_natCast]

/-- HOL Light: `delta_partition_lemma` (line 49105). -/
theorem delta_partition_lemma (delta : ℝ) (hd : 0 < delta) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i ≤ N ∧ |↑i / ↑N - x| < delta := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hN0 : 0 < N := by
    rcases N with _ | N
    · simp at hN; linarith [div_pos one_pos hd]
    · omega
  have hNr : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN0
  refine ⟨N, hN0, fun x hx0 hx1 => ⟨⌊x * ↑N⌋₊, ?_, ?_⟩⟩
  · -- ⌊x * N⌋₊ ≤ N
    have hfl : (⌊x * ↑N⌋₊ : ℝ) ≤ x * ↑N := Nat.floor_le (mul_nonneg hx0 hNr.le)
    exact_mod_cast hfl.trans (by nlinarith : x * (↑N : ℝ) ≤ ↑N)
  · -- |⌊x * N⌋₊ / N - x| < delta
    have hfl : (⌊x * ↑N⌋₊ : ℝ) ≤ x * ↑N := Nat.floor_le (mul_nonneg hx0 hNr.le)
    have hlt : x * ↑N < ↑⌊x * ↑N⌋₊ + 1 := Nat.lt_floor_add_one _
    have h1 : ↑⌊x * ↑N⌋₊ / ↑N ≤ x := by
      rwa [div_le_iff₀ hNr]
    have h2 : x - ↑⌊x * ↑N⌋₊ / ↑N < delta := by
      have : x - ↑⌊x * ↑N⌋₊ / ↑N = (x * ↑N - ↑⌊x * ↑N⌋₊) / ↑N := by
        field_simp
      rw [this, div_lt_iff₀ hNr]
      have : 1 < delta * ↑N := by
        have := (div_lt_iff₀ hd).mp hN
        linarith
      nlinarith
    rw [abs_sub_lt_iff]; constructor <;> linarith

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: `Filter.mem_inf_principal` unfolding and `Metric.mem_uniformity_dist`
-- instantiation on a uniform-continuity witness produce slow unification chains.
/-- HOL Light: `simple_arc_ball_cover` (line 49163). -/
theorem simple_arc_ball_cover (f : ℝ → E2)
    (hf : Continuous f) (hinj : Set.InjOn f (Set.Icc 0 1)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i ≤ N ∧ dist (f (↑i / ↑N)) (f x) < 1 := by
  have huc := simple_arc_uniformly_continuous f hf hinj
  -- Extract δ using filter approach (avoids Metric.uniformContinuousOn_iff timeout)
  have hent : {p : E2 × E2 | dist p.1 p.2 < 1} ∈ uniformity E2 :=
    Metric.dist_mem_uniformity one_pos
  have hV : (fun x : ℝ × ℝ => (f x.1, f x.2)) ⁻¹' {p : E2 × E2 | dist p.1 p.2 < 1}
      ∈ uniformity ℝ ⊓ Filter.principal (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := huc hent
  rw [Filter.mem_inf_principal] at hV
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨N, hN, hpart⟩ := delta_partition_lemma δ hδ0
  refine ⟨N, hN, fun x hx0 hx1 => ?_⟩
  obtain ⟨i, hiN, hdist⟩ := hpart x hx0 hx1
  refine ⟨i, hiN, ?_⟩
  have hNr : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hiIcc : (↑i / ↑N : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Nat.cast_nonneg i) hNr.le,
     (div_le_one hNr).mpr (by exact_mod_cast hiN)⟩
  have hmem : ((↑i / ↑N : ℝ), x) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 1 :=
    Set.mk_mem_prod hiIcc ⟨hx0, hx1⟩
  exact hδ (show dist (↑i / ↑N : ℝ) x < δ by rwa [Real.dist_eq]) hmem

/-! ## §Z.6 Bounded / unbounded set differences -/

/-- HOL Light: `unbounded_diff` (line 49210). -/
theorem unbounded_diff (G : Finset (Set E2)) :
    {x | UnboundedSet G x} =
      complementCurve G \ {x | BoundedSet G x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_diff, UnboundedSet, BoundedSet, not_and, not_not]
  constructor
  · intro hunb
    exact ⟨unbounded_subset_complementCurve G hunb, fun _ => hunb⟩
  · intro ⟨hcomp, h⟩
    exact h ⟨x, mem_connectedComponentIn hcomp⟩

/-- HOL Light: `bounded_diff` (line 49222). -/
theorem bounded_diff (G : Finset (Set E2)) :
    {x | BoundedSet G x} =
      complementCurve G \ {x | UnboundedSet G x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_diff, BoundedSet, UnboundedSet]
  constructor
  · intro ⟨hne, hn⟩
    exact ⟨connectedComponentIn_nonempty_iff.mp hne, hn⟩
  · intro ⟨hcomp, hn⟩
    exact ⟨⟨x, mem_connectedComponentIn hcomp⟩, hn⟩

/-! ## §Z.7 Grid containment and image boundedness -/

/-- HOL Light: `rectangle_grid_subset` (line 49234). -/
theorem rectangle_grid_subset (p q r s : ℤ × ℤ)
    (h1 : p.1 ≤ r.1) (h2 : p.2 ≤ r.2) (h3 : s.1 ≤ q.1) (h4 : s.2 ≤ q.2) :
    rectangle_grid r s ⊆ rectangle_grid p q := by
  intro e he
  simp only [rectangle_grid, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc] at he ⊢
  rcases he with ⟨m, ⟨⟨hm1, hm2⟩, hm3, hm4⟩, rfl⟩ | ⟨m, ⟨⟨hm1, hm2⟩, hm3, hm4⟩, rfl⟩
  · left; exact ⟨m, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩
  · right; exact ⟨m, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩

/-- HOL Light: `grid_image_bounded` (line 49249). -/
theorem grid_image_bounded (f : ℝ → E2)
    (hf : Continuous f) (hinj : Set.InjOn f (Set.Icc 0 1)) :
    ∃ N : ℕ, 0 < N ∧
      Disjoint (f '' Set.Icc 0 1) {x | UnboundedSet (grid f N) x} := by
  obtain ⟨N, hN, hcover⟩ := simple_arc_ball_cover f hf hinj
  refine ⟨N, hN, Set.disjoint_left.mpr fun y hy hunb => ?_⟩
  obtain ⟨x', hx'mem, rfl⟩ := hy
  obtain ⟨i, hiN, hdist⟩ := hcover x' hx'mem.1 hx'mem.2
  -- grid33 at floor(f(i/N)) is a subset of grid f N
  set m₀ := (⌊(f (↑i / ↑N)) 0⌋, ⌊(f (↑i / ↑N)) 1⌋) with hm₀_def
  have hE_sub : grid33 m₀ ⊆ grid f N := by
    intro e he; simp only [grid, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_range.mpr (by omega), he⟩
  -- f x' not in curve cells of grid33 m₀ (from being unbounded in the full grid)
  have hcc : f x' ∉ ⋃₀ (curveCells (grid33 m₀) : Set (Set E2)) :=
    unbounded_set_curve_cell_empty (grid33 m₀) (grid f N) _ hunb hE_sub
  -- floor of f x'
  set m₁ := (⌊(f x') 0⌋, ⌊(f x') 1⌋) with hm₁_def
  -- unit square rectagon at m₁ is inside grid33 m₀
  have h0 := d_euclid_floor _ _ 0 hdist
  have h1 := d_euclid_floor _ _ 1 hdist
  have hE'_sub : rectangle_grid m₁ (m₁.1 + 1, m₁.2 + 1) ⊆ grid33 m₀ := by
    simp only [grid33]
    apply rectangle_grid_subset <;> simp only [hm₀_def, hm₁_def]
    · rw [abs_le] at h0; omega
    · rw [abs_le] at h1; omega
    · rw [abs_le] at h0; omega
    · rw [abs_le] at h1; omega
  -- E' is a rectagon
  obtain ⟨R, hR⟩ := rectagon_rectangle_grid_sq m₁
  -- f x' not in curve cells of E' (via subset monotonicity)
  have hcc' : f x' ∉ ⋃₀ (curveCells (R.edges) : Set (Set E2)) := by
    rw [hR]
    exact fun h => hcc (curveCells_sUnion_mono
      (hE'_sub.trans (by rfl : grid33 m₀ ⊆ grid33 m₀)) h)
  -- Edge membership in R.edges (via rectangle_grid_sq)
  have hRsq := rectangle_grid_sq m₁
  have hh_in : hEdge m₁ ∈ R.edges := by
    rw [hR, hRsq]; exact Finset.mem_insert_self _ _
  have hv_in : vEdge m₁ ∈ R.edges := by
    rw [hR, hRsq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _))))
  -- f x' ∈ squ m₁ (coordinate not an integer → strictly inside the unit square)
  have hfx_squ : f x' ∈ squ m₁ := by
    simp only [squ, Set.mem_setOf_eq, hm₁_def, gt_iff_lt]
    refine ⟨?_, Int.lt_floor_add_one _, ?_, Int.lt_floor_add_one _⟩
    · -- ↑⌊(f x') 0⌋ < (f x') 0
      by_contra hle; push Not at hle
      have heq0 : (f x') 0 = ↑⌊(f x') 0⌋ := le_antisymm hle (Int.floor_le _)
      exact hcc' <| by
        by_cases heq1 : (f x') 1 = ↑⌊(f x') 1⌋
        · exact Set.mem_sUnion.mpr ⟨{pointI m₁},
            (curveCells_cls R.toSegment m₁).mpr
              ⟨hEdge m₁, hh_in,
               (pointI_mem_closure_hEdge m₁ m₁).mpr ⟨rfl, Or.inl rfl⟩⟩,
            show f x' ∈ ({pointI m₁} : Set E2) from by
              rw [Set.mem_singleton_iff]; ext i; fin_cases i
              · exact heq0.trans (pointI_coord_fst m₁).symm
              · exact heq1.trans (pointI_coord_snd m₁).symm⟩
        · exact Set.mem_sUnion.mpr ⟨vEdge m₁,
            (curveCells_edge R.edges _ (Or.inr ⟨m₁, rfl⟩)).mpr hv_in,
            show f x' ∈ vEdge m₁ from ⟨heq0, lt_of_le_of_ne (Int.floor_le _)
              (Ne.symm heq1), Int.lt_floor_add_one _⟩⟩
    · -- ↑⌊(f x') 1⌋ < (f x') 1
      by_contra hle; push Not at hle
      have heq1 : (f x') 1 = ↑⌊(f x') 1⌋ := le_antisymm hle (Int.floor_le _)
      exact hcc' <| by
        by_cases heq0 : (f x') 0 = ↑⌊(f x') 0⌋
        · exact Set.mem_sUnion.mpr ⟨{pointI m₁},
            (curveCells_cls R.toSegment m₁).mpr
              ⟨hEdge m₁, hh_in,
               (pointI_mem_closure_hEdge m₁ m₁).mpr ⟨rfl, Or.inl rfl⟩⟩,
            show f x' ∈ ({pointI m₁} : Set E2) from by
              rw [Set.mem_singleton_iff]; ext i; fin_cases i
              · exact heq0.trans (pointI_coord_fst m₁).symm
              · exact heq1.trans (pointI_coord_snd m₁).symm⟩
        · exact Set.mem_sUnion.mpr ⟨hEdge m₁,
            (curveCells_edge R.edges _ (Or.inl ⟨m₁, rfl⟩)).mpr hh_in,
            show f x' ∈ hEdge m₁ from ⟨lt_of_le_of_ne (Int.floor_le _)
              (Ne.symm heq0), Int.lt_floor_add_one _, heq1⟩⟩
  -- numLower R.edges m₁ = 1 (only hEdge m₁ counts, not hEdge (up m₁))
  have hnum : numLower R.edges m₁ = 1 := by
    change numLower R.edges (m₁.1, m₁.2) = 1
    rw [numLower_step, if_pos (show hEdge (m₁.1, m₁.2) ∈ R.edges from hh_in)]
    suffices numLower R.edges (m₁.1, m₁.2 - 1) = 0 by omega
    unfold numLower; classical
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he; push Not; intro k hk hek
    rw [hek, hR, hRsq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h | h
    · have := (hEdge_inj _ _).mp h; simp only [Prod.ext_iff] at this; omega
    · have heq := (hEdge_inj _ _).mp h
      unfold up at heq
      have hk2 : k = m₁.2 + 1 := (Prod.mk.inj heq).2
      linarith
    · exact absurd h (hEdge_ne_vEdge _ _)
    · exact absurd h (hEdge_ne_vEdge _ _)
  -- parCell false → BoundedSet R.edges (f x') via odd_bounded
  have hpar : parCell false R.edges (squ m₁) :=
    (parCell_squ R.toSegment m₁ false).mpr
      (by change false = decide (Even (numLower R.edges m₁)); rw [hnum]; decide)
  have hbnd_R : BoundedSet R.edges (f x') := by
    have hmem : f x' ∈ ⋃₀ {C | parCell false R.edges C} :=
      Set.mem_sUnion.mpr ⟨squ m₁, hpar, hfx_squ⟩
    rwa [odd_bounded R, Set.mem_setOf_eq] at hmem
  -- Propagate BoundedSet: R.edges → grid33 m₀ → grid f N
  have hbnd_E := bounded_avoidance_subset R.edges (grid33 m₀) (f x')
    hbnd_R (hR ▸ hE'_sub) (grid33_edge m₀) (conn2_rectagon R) hcc
  exact bounded_unbounded_disj (grid f N) (f x')
    ⟨bounded_avoidance_subset (grid33 m₀) (grid f N) (f x') hbnd_E hE_sub
      (grid_edge f N) (grid33_conn2 m₀)
      (unbounded_set_curve_cell_empty (grid f N) (grid f N) _ hunb (fun a ha => ha)), hunb⟩

/-! ## §Z.8 Sequence connectivity lemmas -/

/-- HOL Light: `conn2_sequence_lemma1` (line 49337). -/
theorem conn2_sequence_lemma1 (k N : ℕ) (G : ℕ → Finset (Set E2))
    (hk : k ≤ N) (hconn : ∀ i, i ≤ N → conn2 (G i))
    (hedge : ∀ i, i ≤ N → ∀ e ∈ G i, isEdge e)
    (hinter : ∀ i, i + 1 ≤ N → (G i ∩ G (i + 1)).Nonempty) :
    conn2 ((Finset.range (k + 1)).biUnion G) := by
  induction k with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.range_one, Finset.singleton_biUnion]
    exact hconn 0 (by omega)
  | succ k ih =>
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    specialize ih hk'
    rw [Finset.range_add_one, Finset.biUnion_insert]
    apply conn2_union_edge
    · intro e he; exact hedge (k + 1) hk e he
    · intro e he; rw [Finset.mem_biUnion] at he; obtain ⟨i, hi, hie⟩ := he
      rw [Finset.mem_range] at hi; exact hedge i (by omega) e hie
    · exact hconn (k + 1) hk
    · exact ih
    · obtain ⟨e, he⟩ := hinter k (by omega)
      rw [Finset.mem_inter] at he
      exact ⟨e, Finset.mem_inter.mpr ⟨he.2,
        Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), he.1⟩⟩⟩

/-- HOL Light: `thread_finite_union` (line 49425). -/
theorem thread_finite_union {ι : Type*}
    (A : Finset (Set E2) → Set (Set E2))
    (S : Finset ι) (G : ι → Finset (Set E2))
    (hunion : ∀ a b, A (a ∪ b) = A a ∪ A b)
    (hempty : A ∅ = ∅) :
    A (S.biUnion G) = ⋃ i ∈ S, A (G i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert a s ha ih =>
    simp only [Finset.biUnion_insert, hunion, ih, Finset.set_biUnion_insert]

/-- HOL Light: `conn2_sequence_lemma2` (line 49464). -/
theorem conn2_sequence_lemma2 (G : ℕ → Finset (Set E2)) (N : ℕ) (p : E2)
    (hN : 0 < N) (_hconn : ∀ i, i ≤ N → conn2 (G i))
    (hedge : ∀ i, i ≤ N → ∀ e ∈ G i, isEdge e)
    (_hinter : ∀ i, i + 1 ≤ N → (G i ∩ G (i + 1)).Nonempty)
    (hunbnd : ∀ i, i + 1 ≤ N → UnboundedSet (G i ∪ G (i + 1)) p)
    (hnotunbnd : ¬UnboundedSet ((Finset.range (N + 1)).biUnion G) p) :
    BoundedSet ((Finset.range (N + 1)).biUnion G) p := by
  set U := (Finset.range (N + 1)).biUnion G with hU_def
  have hUedge : ∀ e ∈ U, isEdge e := by
    intro e he; rw [hU_def, Finset.mem_biUnion] at he
    obtain ⟨i, hi, hie⟩ := he
    exact hedge i (by rw [Finset.mem_range] at hi; omega) e hie
  by_cases hp : p ∈ complementCurve U
  · exact (bounded_unbounded_union U hUedge hp).resolve_right hnotunbnd
  · exfalso
    rw [complementCurve, Set.mem_compl_iff, not_not] at hp
    have hdistr : curveCells U =
        ⋃ i ∈ Finset.range (N + 1), curveCells (G i) := by
      rw [hU_def]
      exact thread_finite_union curveCells _ G curveCells_union curveCells_empty
    rw [hdistr] at hp
    obtain ⟨C, hCmem, hpC⟩ := Set.mem_sUnion.mp hp
    rw [Set.mem_iUnion₂] at hCmem
    obtain ⟨j, hjrange, hCj⟩ := hCmem
    rw [Finset.mem_range] at hjrange
    have hpGj : p ∈ ⋃₀ (curveCells (G j) : Set (Set E2)) :=
      Set.mem_sUnion.mpr ⟨C, hCj, hpC⟩
    by_cases hjN : j < N
    · exact absurd hpGj (unbounded_set_curve_cell_empty (G j) (G j ∪ G (j + 1)) p
        (hunbnd j (by omega)) Finset.subset_union_left)
    · have hjN' : j = N := by omega
      rw [hjN'] at hpGj
      have hunbN := hunbnd (N - 1) (by omega)
      rw [show N - 1 + 1 = N from by omega] at hunbN
      exact absurd hpGj (unbounded_set_curve_cell_empty (G N) (G (N - 1) ∪ G N) p
        hunbN Finset.subset_union_right)

/-- HOL Light: `conn2_sequence_lemma3` (line 49544). -/
theorem conn2_sequence_lemma3 (G : ℕ → Finset (Set E2)) (N : ℕ)
    (hedge : ∀ i, i ≤ N → ∀ e ∈ G i, isEdge e) :
    ∀ e ∈ (Finset.range (N + 1)).biUnion G, isEdge e := by
  intro e he
  rw [Finset.mem_biUnion] at he
  obtain ⟨i, hi, hie⟩ := he
  rw [Finset.mem_range] at hi
  exact hedge i (by omega) e hie

/-- HOL Light: `unbounded_avoidance_subset_ver2` (line 49559). -/
theorem unbounded_avoidance_subset_ver2 (E E' : Finset (Set E2)) (x : E2)
    (hunbnd : UnboundedSet E' x)
    (hEE' : E ⊆ E') (_hedge : ∀ e ∈ E', isEdge e)
    (_hconn : conn2 E) :
    UnboundedSet E x := by
  -- complementCurve E' ⊆ complementCurve E (more edges ⇒ more curve cells ⇒ smaller complement)
  have hcomp : complementCurve E' ⊆ complementCurve E :=
    Set.compl_subset_compl.mpr (Set.sUnion_mono (curveCells_mono hEE'))
  -- Connected component is monotone in the ambient set
  have hmono := connectedComponentIn_mono x hcomp
  -- Lift Unbounded through subset inclusion
  obtain ⟨r, hr⟩ := hunbnd
  exact ⟨r, fun s hs => hmono (hr s hs)⟩

/-- HOL Light: `conn2_sequence_lemma4` (line 49578). -/
theorem conn2_sequence_lemma4 (G : ℕ → Finset (Set E2)) (N : ℕ) (p : E2)
    (hN : 0 < N) (hconn : ∀ i, i ≤ N → conn2 (G i))
    (hedge : ∀ i, i ≤ N → ∀ e ∈ G i, isEdge e)
    (hinter : ∀ i, i + 1 ≤ N → (G i ∩ G (i + 1)).Nonempty)
    (hunbnd : ∀ i, i + 1 ≤ N → UnboundedSet (G i ∪ G (i + 1)) p)
    (hbnd : BoundedSet ((Finset.range (N + 1)).biUnion G) p) :
    ∃ (C : Rectagon) (i j : ℕ),
      BoundedSet C.edges p ∧ i + 1 < j ∧ j ≤ N ∧
      C.edges ⊆ (Finset.Icc i j).biUnion G ∧
      ∀ (C' : Rectagon) (i' j' : ℕ),
        BoundedSet C'.edges p → i' < j' → j' ≤ N →
        C'.edges ⊆ (Finset.Icc i' j').biUnion G →
        j - i ≤ j' - i' ∧
          (j - i = j' - i' →
            (C.edges \ G (i + 1)).card ≤ (C'.edges \ G (i' + 1)).card) := by
  classical
  -- Step 1: Get initial rectagon surrounding the bounded component
  have hconn_full := conn2_sequence_lemma1 N N G le_rfl hconn hedge hinter
  obtain ⟨R₀, hR₀sub, hR₀bnd⟩ :=
    rectagon_surround_conn2 _ hconn_full (conn2_sequence_lemma3 G N hedge)
  -- Step 2: Minimize j - i over all valid (C, i, j) triples
  let P (d : ℕ) : Prop := ∃ (C : Rectagon) (i j : ℕ),
    j - i = d ∧ BoundedSet C.edges p ∧ i < j ∧ j ≤ N ∧
    C.edges ⊆ (Finset.Icc i j).biUnion G
  have hexd : ∃ d, P d := by
    refine ⟨N, R₀, 0, N, by omega, hR₀bnd p hbnd, hN, le_rfl, ?_⟩
    intro e he
    obtain ⟨k, hk, hke⟩ := Finset.mem_biUnion.mp (hR₀sub he)
    rw [Finset.mem_range] at hk
    exact Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hke⟩
  obtain ⟨C₁, i₁, j₁, hd₁, hC₁bnd, hij₁, hj₁N, hC₁sub⟩ :=
    Nat.find_spec hexd
  -- Step 3: Among triples with minimal gap, minimize |C \ G(i+1)|
  let Q (c : ℕ) : Prop := ∃ (C : Rectagon) (i j : ℕ),
    (C.edges \ G (i + 1)).card = c ∧ j - i = Nat.find hexd ∧
    BoundedSet C.edges p ∧ i < j ∧ j ≤ N ∧
    C.edges ⊆ (Finset.Icc i j).biUnion G
  have hexc : ∃ c, Q c :=
    ⟨_, C₁, i₁, j₁, rfl, hd₁, hC₁bnd, hij₁, hj₁N, hC₁sub⟩
  obtain ⟨C, i, j, hceq, hdeq, hCbnd, hij, hjN, hCsub⟩ :=
    Nat.find_spec hexc
  -- Step 4: Show i + 1 < j (if j = i+1, C ⊆ G i ∪ G(i+1) → unbounded,
  --   contradicting bounded)
  have hi1j : i + 1 < j := by
    by_contra hle; push Not at hle
    have hjieq : j = i + 1 := by omega
    have hCsub' : C.edges ⊆ G i ∪ G (i + 1) := by
      intro e he
      obtain ⟨k, hk, hke⟩ := Finset.mem_biUnion.mp (hCsub he)
      rw [Finset.mem_Icc] at hk
      rcases Nat.eq_or_lt_of_le hk.1 with rfl | hlt
      · exact Finset.mem_union_left _ hke
      · have : k = i + 1 := by omega
        subst this; exact Finset.mem_union_right _ hke
    exact bounded_unbounded_disj _ _ ⟨hCbnd,
      unbounded_avoidance_subset_ver2 C.edges (G i ∪ G (i + 1)) p
        (hunbnd i (by omega)) hCsub'
        (fun e he => by
          rcases Finset.mem_union.mp he with h | h
          · exact hedge i (by omega) e h
          · exact hedge (i + 1) (by omega) e h)
        (conn2_rectagon C)⟩
  -- Step 5: Assemble result with minimality
  refine ⟨C, i, j, hCbnd, hi1j, hjN, hCsub,
    fun C' i' j' hC'bnd hi'j' hj'N hC'sub => ⟨?_, ?_⟩⟩
  · -- j - i ≤ j' - i' from Phase 2 minimization
    have := Nat.find_min' hexd
      (show P (j' - i') from
        ⟨C', i', j', rfl, hC'bnd, hi'j', hj'N, hC'sub⟩)
    omega
  · -- Card minimality when gaps are equal
    intro hgap_eq
    have := Nat.find_min' hexc
      (show Q ((C'.edges \ G (i' + 1)).card) from
        ⟨C', i', j', rfl, by omega, hC'bnd, hi'j', hj'N, hC'sub⟩)
    omega

/-! ## §Z.9 Rectagon cutting and splicing -/

/-- HOL Light: `endpoint_sub_rectagon` (line 49697). -/
theorem endpoint_sub_rectagon (C : Finset (Set E2)) (G : Rectagon) (m : ℤ × ℤ)
    (hCG : C ⊆ G.edges) (hep : numClosure C m = 1) :
    ∃! e, e ∈ G.edges ∧ e ∉ C ∧ pointI m ∈ closure e := by
  -- numClosure G.edges m = 2 (rectagon has even degree; monotonicity forces 2)
  have hG2 : numClosure G.edges m = 2 := by
    have h1 := numClosure_mono hCG m; rw [hep] at h1
    have h2 := G.even_degree m; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2; omega
  rw [numClosure_eq_one_iff] at hep
  obtain ⟨e₀, ⟨he₀C, he₀cl⟩, he₀uniq⟩ := hep
  rw [numClosure_eq_two_iff] at hG2
  obtain ⟨a, b, hab, haG, hbG, hacl, hbcl, huniq⟩ := hG2
  rcases huniq e₀ (hCG he₀C) he₀cl with rfl | rfl
  · -- e₀ = a: b is the complementary edge
    exact ⟨b, ⟨hbG, fun hbC => hab (he₀uniq b ⟨hbC, hbcl⟩).symm, hbcl⟩,
      fun e ⟨heG, heC, hecl⟩ => by
        rcases huniq e heG hecl with rfl | rfl
        · exact absurd he₀C heC
        · rfl⟩
  · -- e₀ = b: a is the complementary edge
    exact ⟨a, ⟨haG, fun haC => hab (he₀uniq a ⟨haC, hacl⟩), hacl⟩,
      fun e ⟨heG, heC, hecl⟩ => by
        rcases huniq e heG hecl with rfl | rfl
        · rfl
        · exact absurd he₀C heC⟩

/-- HOL Light: `cut_rectagon_unique` (line 49752). -/
theorem cut_rectagon_unique (E : Rectagon) (A B C : Finset (Set E2)) (m n : ℤ × ℤ)
    (hA : A ⊆ E.edges) (hB : B ⊆ E.edges) (hC : C ⊆ E.edges)
    (hAse : segment_end A m n) (hBse : segment_end B m n) (hCse : segment_end C m n)
    (hE : E.edges = A ∪ B) (_hAB : Disjoint A B) :
    C = A ∨ C = B := by
  classical
  -- Key: if A' has segment_end m n, A' ⊆ E.edges, A' ∩ C nonempty → A' ⊆ C
  suffices key : ∀ A' ⊆ E.edges, segment_end A' m n →
      (A' ∩ C).Nonempty → A' ⊆ C by
    have hC_AB : C ⊆ A ∪ B := hE ▸ hC
    have hCne : C.Nonempty := by
      obtain ⟨SC, hSCeq, _, _, _, _⟩ := hCse; rw [← hSCeq]; exact SC.nonempty
    by_cases hAC : (A ∩ C).Nonempty
    · by_cases hBC : (B ∩ C).Nonempty
      · -- Both nonempty → A ∪ B ⊆ C → C = E.edges → contradicts rectagon even degree
        exfalso
        have hE_C : E.edges ⊆ C := hE ▸ Finset.union_subset (key A hA hAse hAC)
          (key B hB hBse hBC)
        have hCE : C = E.edges := le_antisymm hC hE_C
        obtain ⟨SC, hSCeq, hSCm, _, _, _⟩ := hCse
        rw [Segment.isEndpoint, hSCeq, hCE] at hSCm
        have := E.even_degree m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
      · -- A ∩ C nonempty, B ∩ C empty → C = A
        left; ext e; constructor
        · intro he
          rcases Finset.mem_union.mp (hC_AB he) with h | h
          · exact h
          · exact absurd ⟨e, Finset.mem_inter.mpr ⟨h, he⟩⟩ hBC
        · exact fun he => key A hA hAse hAC he
    · by_cases hBC : (B ∩ C).Nonempty
      · -- A ∩ C empty, B ∩ C nonempty → C = B
        right; ext e; constructor
        · intro he
          rcases Finset.mem_union.mp (hC_AB he) with h | h
          · exact absurd ⟨e, Finset.mem_inter.mpr ⟨h, he⟩⟩ hAC
          · exact h
        · exact fun he => key B hB hBse hBC he
      · -- Both empty → C empty, contradicts nonemptiness
        exact absurd (by
          obtain ⟨e, he⟩ := hCne
          rcases Finset.mem_union.mp (hC_AB he) with h | h
          · exact (hAC ⟨e, Finset.mem_inter.mpr ⟨h, he⟩⟩).elim
          · exact (hBC ⟨e, Finset.mem_inter.mpr ⟨h, he⟩⟩).elim) id
  -- Proof of `key`: inductive subset argument
  intro A' hA'E hA'se hA'Cne
  obtain ⟨SA', hSA'eq, hSA'm, hSA'n, _, hSA'ep⟩ := hA'se
  have hIS : SA'.isInductiveSubset (A' ∩ C) :=
    ⟨hSA'eq ▸ Finset.inter_subset_left, hA'Cne, fun e he e' he' hne hcl => by
      rw [hSA'eq] at he'; rw [Finset.mem_inter] at he ⊢
      refine ⟨he', ?_⟩
      by_contra he'C
      have hie : isEdge e := SA'.all_edges e (hSA'eq ▸ he.1)
      have hie' : isEdge e' := SA'.all_edges e' (hSA'eq ▸ he')
      have hadj : cellAdj e e' :=
        ⟨isEdge_isCell hie, isEdge_isCell hie', hne, hcl⟩
      set q := adjv e e' with hq_def
      have hqe := adjv_closure_left e e' hie hie' hadj
      have hqe' := adjv_closure_right e e' hie hie' hadj
      -- Rectagon.subset_endpoint: numClosure C q = 1
      have hposC : 0 < numClosure C q :=
        Finset.card_pos.mpr
          ⟨e, Finset.mem_filter.mpr ⟨he.2, hqe⟩⟩
      have hposDiff : 0 < numClosure (E.edges \ C) q :=
        Finset.card_pos.mpr ⟨e', Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hA'E he', he'C⟩, hqe'⟩⟩
      have hnC1 := E.subset_endpoint C q hC hposC hposDiff
      -- q is endpoint of C → q = m or q = n
      obtain ⟨SC, hSCeq, _, _, _, hSCep⟩ := hCse
      rcases hSCep q (show SC.isEndpoint q by
        rw [Segment.isEndpoint, hSCeq]; exact hnC1) with rfl | rfl
      · -- q = m: numClosure_eq_one_iff gives uniqueness, contradicting e ≠ e'
        rw [Segment.isEndpoint, hSA'eq] at hSA'm
        obtain ⟨_, _, huniq⟩ := (numClosure_eq_one_iff A' q).mp hSA'm
        exact hne ((huniq e ⟨he.1, hqe⟩).trans (huniq e' ⟨he', hqe'⟩).symm)
      · rw [Segment.isEndpoint, hSA'eq] at hSA'n
        obtain ⟨_, _, huniq⟩ := (numClosure_eq_one_iff A' q).mp hSA'n
        exact hne ((huniq e ⟨he.1, hqe⟩).trans (huniq e' ⟨he', hqe'⟩).symm)⟩
  have hAC_eq := SA'.isInductiveSubset_eq (A' ∩ C) hIS
  rw [hSA'eq] at hAC_eq
  exact fun e he => (Finset.mem_inter.mp (hAC_eq.symm ▸ he)).2

section EdgeComponent
attribute [local instance] Classical.propDecidable

/-- Connected component of edge `e` in an edge set `G`. -/
private noncomputable def edgeComponentOf (G : Finset (Set E2)) (e : Set E2) :
    Finset (Set E2) :=
  G.filter fun f =>
    ∀ S : Finset (Set E2), S ⊆ G → S.Nonempty →
      (∀ a ∈ S, ∀ b ∈ G, a ≠ b → (closure a ∩ closure b).Nonempty → b ∈ S) →
      e ∈ S → f ∈ S

private theorem mem_edgeComponentOf {G : Finset (Set E2)} {e f : Set E2} :
    f ∈ edgeComponentOf G e ↔ f ∈ G ∧
      (∀ S : Finset (Set E2), S ⊆ G → S.Nonempty →
        (∀ a ∈ S, ∀ b ∈ G, a ≠ b → (closure a ∩ closure b).Nonempty → b ∈ S) →
        e ∈ S → f ∈ S) :=
  Finset.mem_filter

private theorem edgeComponentOf_subset {G : Finset (Set E2)} {e : Set E2} :
    edgeComponentOf G e ⊆ G := Finset.filter_subset _ _

private theorem edgeComponentOf_mem {G : Finset (Set E2)} {e : Set E2} (he : e ∈ G) :
    e ∈ edgeComponentOf G e :=
  mem_edgeComponentOf.mpr ⟨he, fun _ _ _ _ hes => hes⟩

private theorem edgeComponentOf_closed {G : Finset (Set E2)} {e : Set E2}
    (a : Set E2) (ha : a ∈ edgeComponentOf G e) (b : Set E2) (hb : b ∈ G)
    (hab : a ≠ b) (hint : (closure a ∩ closure b).Nonempty) :
    b ∈ edgeComponentOf G e :=
  mem_edgeComponentOf.mpr ⟨hb, fun S hSG hSne hScl hSe =>
    hScl a ((mem_edgeComponentOf.mp ha).2 S hSG hSne hScl hSe) b hb hab hint⟩

end EdgeComponent

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: constructing a `Segment` from an edge component requires
-- verifying the connectivity predicate over all subsets, triggering deep `simp`/`omega` chains.
private theorem edgeComponentOf_isSegment (E : Segment) (G : Finset (Set E2))
    (hGE : G ⊆ E.edges) (e : Set E2) (he : e ∈ G) :
    ∃ S : Segment, S.edges = edgeComponentOf G e := by
  classical
  set J := edgeComponentOf G e with hJ_def
  have hJG : J ⊆ G := edgeComponentOf_subset
  have hJE : J ⊆ E.edges := hJG.trans hGE
  have hne : J.Nonempty := ⟨e, edgeComponentOf_mem he⟩
  have hedge : ∀ f ∈ J, isEdge f := fun f hf => E.all_edges f (hJE hf)
  have hdeg : ∀ m, numClosure J m ∈ ({0, 1, 2} : Set ℕ) := by
    intro m; have h1 := E.degree_bound m; have h2 := numClosure_mono hJE m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢; omega
  have hJclosed : ∀ a ∈ J, ∀ b ∈ G, a ≠ b →
      (closure a ∩ closure b).Nonempty → b ∈ J :=
    fun a ha b hb hab hint => edgeComponentOf_closed a ha b hb hab hint
  -- Connectivity: any nonempty adjacency-closed subset T of J equals J
  have hconn : ∀ T ⊆ (↑J : Set _), T.Nonempty →
      (∀ C ∈ T, ∀ C' ∈ (↑J : Set _), cellAdj C C' → C' ∈ T) → T = (↑J : Set _) := by
    intro T hTJ hTne hTcl
    by_contra hne_eq
    have hstrict : ∃ f ∈ J, f ∉ T := by
      by_contra hall; simp only [not_exists, not_and, not_not] at hall
      exact hne_eq (Set.Subset.antisymm hTJ (fun x hx => hall x (Finset.mem_coe.mp hx)))
    obtain ⟨f₀, hf₀J, hf₀T⟩ := hstrict
    -- Helper: J \ T is closed under adjacency in G
    have hVclosed : ∀ a, a ∈ J → a ∉ T → ∀ b ∈ G, a ≠ b →
        (closure a ∩ closure b).Nonempty → b ∈ J ∧ b ∉ T := by
      intro a haJ haT b hbG hab hint
      refine ⟨hJclosed a haJ b hbG hab hint, fun hbT => haT ?_⟩
      exact hTcl b hbT a (Finset.mem_coe.mpr haJ)
        ⟨isEdge_isCell (hedge b (hJclosed a haJ b hbG hab hint)),
         isEdge_isCell (hedge a haJ), hab.symm,
         Set.inter_comm (closure a) (closure b) ▸ hint⟩
    by_cases heT : e ∈ T
    · -- e ∈ T: show every f ∈ J is in T via the edgeComponentOf property
      have hfT : ∀ f ∈ J, f ∈ T := by
        intro f hfJ
        have hfp := (mem_edgeComponentOf.mp hfJ).2
        have hfF := hfp (J.filter fun g => g ∈ T)
          (fun g hg => hJG (Finset.mem_of_mem_filter g hg))
          ⟨e, Finset.mem_filter.mpr ⟨edgeComponentOf_mem he, heT⟩⟩
          (fun a ha b hbG hab hint => by
            have haJ := Finset.mem_of_mem_filter a ha
            have haT := (Finset.mem_filter.mp ha).2
            have hbJ := hJclosed a haJ b hbG hab hint
            have hbT := hTcl a haT b (Finset.mem_coe.mpr hbJ)
              ⟨isEdge_isCell (hedge a haJ), isEdge_isCell (E.all_edges b (hGE hbG)), hab, hint⟩
            exact Finset.mem_filter.mpr ⟨hbJ, hbT⟩)
          (Finset.mem_filter.mpr ⟨edgeComponentOf_mem he, heT⟩)
        exact (Finset.mem_filter.mp hfF).2
      exact hf₀T (hfT f₀ hf₀J)
    · -- e ∉ T: show every f ∈ J is NOT in T, contradicting T nonempty ⊆ J
      have hfnT : ∀ f ∈ J, f ∉ T := by
        intro f hfJ
        have hfp := (mem_edgeComponentOf.mp hfJ).2
        exact (Finset.mem_filter.mp (hfp (J.filter fun g => g ∉ T)
          (fun g hg => hJG (Finset.mem_of_mem_filter g hg))
          ⟨e, Finset.mem_filter.mpr ⟨edgeComponentOf_mem he, heT⟩⟩
          (fun a ha b hbG hab hint => by
            have haJ := Finset.mem_of_mem_filter a ha
            have hanT := (Finset.mem_filter.mp ha).2
            obtain ⟨hbJ, hbnT⟩ := hVclosed a haJ hanT b hbG hab hint
            exact Finset.mem_filter.mpr ⟨hbJ, hbnT⟩)
          (Finset.mem_filter.mpr ⟨edgeComponentOf_mem he, heT⟩))).2
      obtain ⟨t, ht⟩ := hTne
      exact hfnT t (Finset.mem_coe.mp (hTJ ht)) ht
  exact ⟨⟨J, hne, hedge, hdeg, hconn⟩, rfl⟩

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: `edgeComponentOf_isSegment` is invoked on a dynamically built `Segment`
-- wrapper, and subsequent closure/endpoint reasoning involves many `Finset.sdiff` rewrites.
/-- HOL Light: `conn2_sequence_lemma5` (line 49928). -/
theorem conn2_sequence_lemma5 (C : Rectagon) (E : Finset (Set E2))
    (hnotE : ¬E ⊆ C.edges)
    (hpseg : ∃ S : Segment, S.edges = E ∧ S.isPsegment)
    (hep : {m | numClosure E m = 1} ⊆ cls C.edges) :
    ∃ E' ⊆ E, (∃ S : Segment, S.edges = E' ∧ S.isPsegment) ∧
      Disjoint E' C.edges ∧
      cls E' ∩ cls C.edges = {m | numClosure E' m = 1} := by
  classical
  obtain ⟨SE, hSEeq, hSEpseg⟩ := hpseg
  -- Build a Segment wrapper with edges = E
  let SE' : Segment := ⟨E,
    show E.Nonempty by rw [← hSEeq]; exact SE.nonempty,
    fun f hf => SE.all_edges f (hSEeq.symm ▸ hf),
    fun m => by have := SE.degree_bound m; rwa [hSEeq] at this,
    fun T hTE hTne hTcl => by
      have := SE.connected T (show T ⊆ (↑SE.edges : Set _) by rwa [hSEeq]) hTne
        (fun a ha b hb hadj => hTcl a ha b (show b ∈ (↑E : Set _) by rwa [← hSEeq]) hadj)
      rwa [← hSEeq]⟩
  -- Step 1: Find e ∈ E \ C.edges
  have hne_diff : (E \ C.edges).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
    exact hnotE
  obtain ⟨e₀, he₀⟩ := hne_diff
  rw [Finset.mem_sdiff] at he₀
  -- Step 2: Connected component J of e₀ in E \ C.edges
  set G := E \ C.edges
  have hGE : G ⊆ E := Finset.sdiff_subset
  obtain ⟨SJ, hSJeq⟩ := edgeComponentOf_isSegment SE' G hGE e₀
    (Finset.mem_sdiff.mpr he₀)
  set J := edgeComponentOf G e₀
  have hJG : J ⊆ G := edgeComponentOf_subset
  have hJE : J ⊆ E := hJG.trans hGE
  have hJC : Disjoint J C.edges := by
    rw [Finset.disjoint_left]; intro x hxJ hxC
    exact (Finset.mem_sdiff.mp (hJG hxJ)).2 hxC
  -- Step 2b: J is a psegment (not a rectagon)
  have hJpseg : SJ.isPsegment := by
    rcases SJ.endpoint_count with hall | hps
    · exfalso
      obtain ⟨a, _, _, hSEa, _, _⟩ := hSEpseg
      -- Construct a Rectagon from J using the no-endpoints hypothesis
      have heven : ∀ m, numClosure J m ∈ ({0, 2} : Set ℕ) := by
        intro m; have hd := SJ.degree_bound m; rw [hSJeq] at hd
        have hno := hall m; rw [Segment.isEndpoint, hSJeq] at hno
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd ⊢
        rcases hd with h | h | h
        · left; exact h
        · exact absurd h hno
        · right; exact h
      have hJne : J.Nonempty := by rw [← hSJeq]; exact SJ.nonempty
      let RJ : Rectagon := ⟨J, hJne,
        fun f hf => SE'.all_edges f (hJE hf), heven,
        fun T hTJ hTne hTcl => by
          have := SJ.connected T (show T ⊆ (↑SJ.edges : Set _) by rwa [hSJeq]) hTne
            (fun c hc c' hc' hadj => hTcl c hc c' (show c' ∈ (↑J : Set _) by rwa [← hSJeq]) hadj)
          rwa [← hSJeq]⟩
      have h_eq : J = E := rectagon_subset_eq RJ SE' hJE
      rw [Segment.isEndpoint, hSEeq] at hSEa
      exact hall a (show SJ.isEndpoint a by
        rw [Segment.isEndpoint, hSJeq, h_eq]; exact hSEa)
    · exact hps
  -- Step 2c: endpoints of J ⊆ cls C.edges
  have hep_J : {m | numClosure J m = 1} ⊆ cls C.edges := by
    intro m hm; simp only [Set.mem_setOf_eq] at hm
    have hle := numClosure_mono hJE m
    have hEdeg : numClosure E m ∈ ({0, 1, 2} : Set ℕ) := by
      have := SE.degree_bound m; rwa [hSEeq] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hEdeg
    rcases hEdeg with h | h | h
    · exfalso; omega
    · exact hep (Set.mem_setOf_eq.mpr h)
    · -- numClosure E m = 2, numClosure J m = 1
      obtain ⟨ea, eb, heab, heaE, hebE, heacl, hebcl, heuniq⟩ :=
        (numClosure_eq_two_iff E m).mp h
      obtain ⟨ej, hejP, hejuniq⟩ := (numClosure_eq_one_iff J m).mp hm
      have hejE := hJE hejP.1
      have hejcl := hejP.2
      have hejJ := hejP.1
      rcases heuniq ej hejE hejcl with h_eq | h_eq
      · -- h_eq : ej = ea
        rw [h_eq] at hejJ hejcl hejuniq
        suffices hcl : eb ∈ C.edges by exact ⟨eb, hcl, hebcl⟩
        by_contra hebC
        have hebG : eb ∈ G := Finset.mem_sdiff.mpr ⟨hebE, hebC⟩
        have hebJ := edgeComponentOf_closed ea hejJ eb hebG heab
          ⟨pointI m, heacl, hebcl⟩
        exact heab (hejuniq eb ⟨hebJ, hebcl⟩).symm
      · -- h_eq : ej = eb
        rw [h_eq] at hejJ hejcl hejuniq
        suffices hcl : ea ∈ C.edges by exact ⟨ea, hcl, heacl⟩
        by_contra heaC
        have heaG : ea ∈ G := Finset.mem_sdiff.mpr ⟨heaE, heaC⟩
        have heaJ := edgeComponentOf_closed eb hejJ ea heaG heab.symm
          ⟨pointI m, hebcl, heacl⟩
        exact heab (hejuniq ea ⟨heaJ, heacl⟩)
  -- Step 3: Minimize over all valid psegments
  let X : Set (Finset (Set E2)) := {J' | J' ⊆ E ∧
    (∃ S : Segment, S.edges = J' ∧ S.isPsegment) ∧
    Disjoint J' C.edges ∧ {m | numClosure J' m = 1} ⊆ cls C.edges}
  have hXne : X.Nonempty := ⟨J, hJE, ⟨SJ, hSJeq, hJpseg⟩, hJC, hep_J⟩
  have hXfin : X.Finite :=
    (Finset.finite_toSet E.powerset).subset (fun S hS => Finset.mem_powerset.mpr hS.1)
  obtain ⟨z, hzX, hzmin⟩ := exists_min_image_nat hXne hXfin (f := fun J' => J'.card)
  obtain ⟨hzE, ⟨Sz, hSzeq, hSzpseg⟩, hzC, hzep⟩ := hzX
  -- Step 4: cls z ∩ cls C.edges = {m | numClosure z m = 1}
  refine ⟨z, hzE, ⟨Sz, hSzeq, hSzpseg⟩, hzC, ?_⟩
  ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; constructor
  · -- → : x ∈ cls z ∩ cls C → numClosure z x = 1
    intro ⟨hxz, hxC⟩
    have hzdeg := Sz.degree_bound x; rw [hSzeq] at hzdeg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzdeg
    rcases hzdeg with h | h | h
    · exfalso; obtain ⟨f, hf, hfcl⟩ := hxz
      exact (numClosure_eq_zero_iff z x).mp h f hf hfcl
    · exact h
    · -- numClosure z x = 2: cut z at x for contradiction with minimality
      exfalso
      obtain ⟨za, zb, hzab, hSza, hSzb, hSzep_m⟩ := hSzpseg
      have hse : segment_end z za zb := ⟨Sz, hSzeq, hSza, hSzb, hzab, hSzep_m⟩
      have hxa : x ≠ za := by
        intro heq; rw [heq] at h
        have h1 := hSza; rw [Segment.isEndpoint, hSzeq] at h1; omega
      have hxb : x ≠ zb := by
        intro heq; rw [heq] at h
        have h1 := hSzb; rw [Segment.isEndpoint, hSzeq] at h1; omega
      obtain ⟨A, B, hzAB, hABdisj, _, hAse, hBse⟩ :=
        cut_psegment hse hxz hxa hxb
      have hAz : A ⊆ z := hzAB ▸ Finset.subset_union_left
      have hAX : A ∈ X := by
        refine ⟨hAz.trans hzE, ?_, Disjoint.mono_left hAz hzC, ?_⟩
        · obtain ⟨SA, hSAeq, hSAa, hSAx, _, hSAep_m⟩ := hAse
          exact ⟨SA, hSAeq, za, x, hxa.symm, hSAa, hSAx, hSAep_m⟩
        · intro m' hm'; simp only [Set.mem_setOf_eq] at hm'
          obtain ⟨SA, hSAeq, hSAa, hSAx, _, hSAep_m⟩ := hAse
          have hm'ep : SA.isEndpoint m' := by rw [Segment.isEndpoint, hSAeq]; exact hm'
          rcases hSAep_m m' hm'ep with rfl | rfl
          · have h1 := hSza; rw [Segment.isEndpoint, hSzeq] at h1; exact hzep h1
          · exact hxC
      have hAne : A ≠ z := by
        intro heq; obtain ⟨SB, hSBeq, _, _, _, _⟩ := hBse
        obtain ⟨f, hf⟩ := SB.nonempty; rw [hSBeq] at hf
        have hfz : f ∈ z := hzAB ▸ Finset.mem_union_right _ hf
        exact Finset.disjoint_left.mp (heq ▸ hABdisj) hfz hf
      exact absurd (card_subset_lt hAz hAne) (Nat.not_lt.mpr (hzmin A hAX))
  · -- ← : numClosure z x = 1 → x ∈ cls z ∩ cls C
    intro hm
    exact ⟨endpoint_subset_cls z (fun f hf => Sz.all_edges f (hSzeq.symm ▸ hf)) hm,
           hzep hm⟩

set_option maxHeartbeats 1600000 in
-- Elevated heartbeats: the splice construction requires reasoning about `numClosure` additivity
-- across `Finset.sdiff` and union, involving many `card_union_of_disjoint` and `omega` steps.
/-- HOL Light: `conn_splice` (line 50116). -/
theorem conn_splice (E AE B : Finset (Set E2)) (a b a' b' : ℤ × ℤ)
    (hE : segment_end E a b) (hAE : segment_end AE a' b') (hB : segment_end B a' b')
    (hAEE : AE ⊆ E) :
    ∃ B' : Finset (Set E2), segment_end B' a b ∧ B' ⊆ (E \ AE) ∪ B := by
  classical
  set J := (E \ AE) ∪ B with hJdef
  obtain ⟨SE, hSEeq, hSEa, hSEb, hab, hSEep⟩ := hE
  obtain ⟨SAE, hSAEeq, hSAEa', hSAEb', ha'b', hSAEep⟩ := hAE
  have hEedge : ∀ e ∈ E, isEdge e := fun e he => SE.all_edges e (hSEeq ▸ he)
  have hBJ : B ⊆ J := Finset.subset_union_right
  have hEAEJ : E \ AE ⊆ J := Finset.subset_union_left
  -- numClosure additivity: E = AE ∪ (E \ AE) disjoint
  have nc_add : ∀ m, numClosure E m = numClosure AE m + numClosure (E \ AE) m := by
    intro m; conv_lhs => rw [show E = AE ∪ (E \ AE) from (Finset.union_sdiff_of_subset hAEE).symm]
    unfold numClosure incidentEdges; rw [Finset.filter_union]
    exact Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun x hx1 hx2 =>
      (Finset.mem_sdiff.mp (Finset.mem_of_mem_filter x hx2)).2
        (Finset.mem_of_mem_filter x hx1))
  -- Boundary points between AE and E\AE are endpoints of AE
  have hboundary : ∀ v : ℤ × ℤ, 0 < numClosure AE v → 0 < numClosure (E \ AE) v →
      v = a' ∨ v = b' := by
    intro v hAEv hEAEv
    have hEv := nc_add v
    have hEdeg : numClosure E v ≤ 2 := by
      have := SE.degree_bound v; rw [hSEeq] at this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
    have : numClosure AE v = 1 := by omega
    exact hSAEep v (show SAE.isEndpoint v by rw [Segment.isEndpoint, hSAEeq]; exact this)
  -- Claim: ∀ x ∈ cls J, x = a' ∨ ∃ P ⊆ J, segment_end P x a'
  suffices hpass : ∀ x, x ∈ cls J → x = a' ∨ ∃ P ⊆ J, segment_end P x a' by
    -- Derive conn J
    have hconnJ : conn J := by
      intro x y hxJ hyJ hxy
      rcases hpass x hxJ with hxa' | ⟨Px, hPxJ, hPx⟩
      · rcases hpass y hyJ with hya' | ⟨Py, hPyJ, hPy⟩
        · exact absurd (hxa'.trans hya'.symm) hxy
        · exact ⟨Py, hPyJ, by rw [hxa']; exact (segment_end_symm Py y a').mp hPy⟩
      · rcases hpass y hyJ with hya' | ⟨Py, hPyJ, hPy⟩
        · exact ⟨Px, hPxJ, by rw [hya']; exact hPx⟩
        · obtain ⟨U, hU, hUse⟩ := segment_end_trans hPx
            ((segment_end_symm Py y a').mp hPy) hxy
          exact ⟨U, hU.trans (Finset.union_subset hPxJ hPyJ), hUse⟩
    -- Show a, b ∈ cls J
    have hep_cls : ∀ c, numClosure E c = 1 → c ∈ cls J := by
      intro c hc
      obtain ⟨e, he, _⟩ := (numClosure_eq_one_iff E c).mp hc
      by_cases heAE : e ∈ AE
      · have hcAEge : 1 ≤ numClosure AE c := Finset.card_pos.mpr
          ⟨e, Finset.mem_filter.mpr ⟨heAE, he.2⟩⟩
        have hcAEle := numClosure_mono hAEE c
        have hcAE1 : numClosure AE c = 1 := by omega
        rcases hSAEep c (show SAE.isEndpoint c by
          rw [Segment.isEndpoint, hSAEeq]; exact hcAE1) with rfl | rfl
        · exact cls_subset hBJ (segment_end_cls hB)
        · exact cls_subset hBJ (segment_end_cls2 hB)
      · exact cls_subset hEAEJ ⟨e, Finset.mem_sdiff.mpr ⟨he.1, heAE⟩, he.2⟩
    have haJ := hep_cls a (by rw [Segment.isEndpoint, hSEeq] at hSEa; exact hSEa)
    have hbJ := hep_cls b (by rw [Segment.isEndpoint, hSEeq] at hSEb; exact hSEb)
    obtain ⟨B', hB'J, hB'⟩ := hconnJ a b haJ hbJ hab
    exact ⟨B', hB', hB'J⟩
  -- Prove hpass
  intro x hxJ
  by_cases hxa : x = a'; · left; exact hxa
  right
  by_cases hxb : x = b'
  · exact ⟨B, hBJ, by rw [hxb]; exact (segment_end_symm B a' b').mp hB⟩
  by_cases hxB : x ∈ cls B
  · obtain ⟨B1, _, hBeq, _, _, hB1se, _⟩ := cut_psegment hB hxB hxa hxb
    exact ⟨B1, (show B1 ⊆ B from hBeq ▸ Finset.subset_union_left).trans hBJ,
      (segment_end_symm B1 a' x).mp hB1se⟩
  · -- x ∉ cls B, x ∈ cls(E \ AE)
    have hxEAE : x ∈ cls (E \ AE) := by
      rw [hJdef, cls_union] at hxJ; exact hxJ.elim id (fun h => absurd h hxB)
    by_contra hno; push Not at hno
    -- No path from x to b' either (compose with B to get path to a')
    have hno_b : ∀ P, P ⊆ J → ¬segment_end P x b' := by
      intro P hPJ hP
      obtain ⟨U, hU, hUse⟩ := segment_end_trans hP
        ((segment_end_symm B b' a').mpr hB) hxa
      exact hno U (hU.trans (Finset.union_subset hPJ hBJ)) hUse
    -- Bad vertices can't be a' or b'
    have hbad_neq : ∀ y, (∀ P, P ⊆ J → ¬segment_end P y a') →
        (∀ P, P ⊆ J → ¬segment_end P y b') → y ≠ a' ∧ y ≠ b' := by
      intro y hya hyb; constructor
      · intro h; rw [h] at hyb; exact hyb B hBJ hB
      · intro h; rw [h] at hya; exact hya B hBJ ((segment_end_symm B a' b').mp hB)
    -- Define bad set T
    let T : Set (Set E2) := {e | e ∈ (E : Finset (Set E2)) ∧
      e ∉ (AE : Finset (Set E2)) ∧
      ∃ y : ℤ × ℤ, pointI y ∈ closure e ∧
        (∀ P, P ⊆ J → ¬segment_end P y a') ∧ (∀ P, P ⊆ J → ¬segment_end P y b')}
    have hTE : T ⊆ (↑SE.edges : Set _) := by
      intro e ⟨heE, _⟩; simp only [hSEeq]; exact heE
    obtain ⟨e₀, he₀, he₀cl⟩ := hxEAE
    have hTne : T.Nonempty := ⟨e₀, (Finset.mem_sdiff.mp he₀).1,
      (Finset.mem_sdiff.mp he₀).2, x, he₀cl, hno, hno_b⟩
    -- T is inductive in SE
    have hTind : ∀ C ∈ T, ∀ C' ∈ (↑SE.edges : Set _), cellAdj C C' → C' ∈ T := by
      rintro C ⟨hCE, hCAE, y, hyCl, hy_no_a, hy_no_b⟩ C' hC'SE hadj
      have hCE' : C ∈ E := hCE
      have hC'E : C' ∈ E := by simpa [hSEeq] using hC'SE
      have hCedge := hEedge C hCE'; have hC'edge := hEedge C' hC'E
      have hy_ne_a := (hbad_neq y hy_no_a hy_no_b).1
      have hy_ne_b := (hbad_neq y hy_no_a hy_no_b).2
      have hvC := adjv_closure_left C C' hCedge hC'edge hadj
      have hvC' := adjv_closure_right C C' hCedge hC'edge hadj
      have hCJ : ({C} : Finset _) ⊆ J :=
        Finset.singleton_subset_iff.mpr
          (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hCE', hCAE⟩))
      -- If shared point = a': path y → a' via {C}. Contradiction.
      by_cases hva : adjv C C' = a'
      · exfalso
        have hyv : y ≠ adjv C C' := fun h => hy_ne_a (h.trans hva)
        exact hy_no_a {C} hCJ (hva ▸ segment_end_sing hyCl hvC hyv hCedge)
      by_cases hvb : adjv C C' = b'
      · exfalso
        have hyv : y ≠ adjv C C' := fun h => hy_ne_b (h.trans hvb)
        exact hy_no_b {C} hCJ (hvb ▸ segment_end_sing hyCl hvC hyv hCedge)
      · -- Shared point ∉ {a', b'}: C' ∉ AE by degree argument
        have hC'nAE : C' ∉ AE := by
          intro hC'AE
          have h1 : 0 < numClosure AE (adjv C C') := Finset.card_pos.mpr
            ⟨C', Finset.mem_filter.mpr ⟨hC'AE, hvC'⟩⟩
          have h2 : 0 < numClosure (E \ AE) (adjv C C') := Finset.card_pos.mpr
            ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hCE', hCAE⟩, hvC⟩⟩
          rcases hboundary _ h1 h2 with rfl | rfl <;> contradiction
        -- v has no path to a' or b'
        have hv_no_a : ∀ P, P ⊆ J → ¬segment_end P (adjv C C') a' := by
          intro P hPJ hP
          by_cases hyv : y = adjv C C'
          · exact hy_no_a P hPJ (hyv ▸ hP)
          · obtain ⟨U, hU, hUse⟩ := segment_end_trans
              (segment_end_sing hyCl hvC hyv hCedge) hP hy_ne_a
            exact hy_no_a U (hU.trans (Finset.union_subset hCJ hPJ)) hUse
        have hv_no_b : ∀ P, P ⊆ J → ¬segment_end P (adjv C C') b' := by
          intro P hPJ hP
          by_cases hyv : y = adjv C C'
          · exact hy_no_b P hPJ (hyv ▸ hP)
          · obtain ⟨U, hU, hUse⟩ := segment_end_trans
              (segment_end_sing hyCl hvC hyv hCedge) hP hy_ne_b
            exact hy_no_b U (hU.trans (Finset.union_subset hCJ hPJ)) hUse
        exact ⟨hC'E, hC'nAE, adjv C C', hvC', hv_no_a, hv_no_b⟩
    -- Apply connectivity: T = (↑SE.edges : Set _)
    have hTeqE := SE.connected T hTE hTne hTind
    -- Contradiction: AE ∩ T = ∅ but T = E ⊇ AE
    obtain ⟨eAE, heAE⟩ := SAE.nonempty
    have : eAE ∈ T := by
      rw [hTeqE]; change eAE ∈ SE.edges; rw [hSEeq]; exact hAEE (hSAEeq ▸ heAE)
    exact this.2.1 (hSAEeq ▸ heAE)

/-! ## §Z.10 Main theorem -/

set_option maxHeartbeats 3200000 in
-- Elevated heartbeats: the main theorem orchestrates `conn_splice`, `conn2_sequence_lemma4/5`,
-- and K₃,₃ planarity arguments in a long by-contradiction proof with many `Finset.biUnion`
-- membership goals; the combined elaboration cost requires 3.2× the default budget.
/-- HOL Light: `conn2_sequence` (line 50389).
    **Main theorem of section Z.** If each pair of consecutive 2-connected
    edge sets has an unbounded complement, then their full union does too,
    provided the curve cells of non-adjacent sets are disjoint. -/
theorem conn2_sequence (G : ℕ → Finset (Set E2)) (N : ℕ) (p : E2)
    (hN : 0 < N) (hconn : ∀ i, i ≤ N → conn2 (G i))
    (hedge : ∀ i, i ≤ N → ∀ e ∈ G i, isEdge e)
    (hinter : ∀ i, i + 1 ≤ N → (G i ∩ G (i + 1)).Nonempty)
    (hdisjoint : ∀ i j, i < j → j ≤ N → i + 1 ≠ j →
      Disjoint (curveCells (G i) : Set (Set E2)) (curveCells (G j)))
    (hunbnd : ∀ i, i + 1 ≤ N → UnboundedSet (G i ∪ G (i + 1)) p) :
    UnboundedSet ((Finset.range (N + 1)).biUnion G) p := by
  classical
  by_contra hnotunbnd
  -- === Part A: BoundedSet and minimal certificate (C, i₀, j₀) ===
  have hbnd := conn2_sequence_lemma2 G N p hN hconn hedge hinter hunbnd hnotunbnd
  obtain ⟨C, i₀, j₀, hCbnd, hij₀, hj₀N, hCsub, hmin⟩ :=
    conn2_sequence_lemma4 G N p hN hconn hedge hinter hunbnd hbnd
  -- === Part B: Find ei ∈ C ∩ G(i₀) and ej ∈ C ∩ G(j₀) ===
  have ⟨ei, heiC, heiGi, heiNotGk⟩ : ∃ ei ∈ C.edges,
      ei ∈ G i₀ ∧ ∀ k, i₀ < k → k ≤ j₀ → ei ∉ G k := by
    by_contra h; push Not at h
    have hCsub' : C.edges ⊆ (Finset.Icc (i₀ + 1) j₀).biUnion G := by
      intro e he
      obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp (hCsub he)
      rw [Finset.mem_Icc] at hk
      if hki : i₀ = k then
        obtain ⟨k', hk'gt, hk'le, hek'⟩ := h e he (hki ▸ hek)
        exact Finset.mem_biUnion.mpr ⟨k', Finset.mem_Icc.mpr ⟨by omega, hk'le⟩, hek'⟩
      else
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, hk.2⟩, hek⟩
    have ⟨hle, _⟩ := hmin C (i₀ + 1) j₀ hCbnd (by omega) hj₀N hCsub'; omega
  have ⟨ej, hejC, hejGj, hejNotGk⟩ : ∃ ej ∈ C.edges,
      ej ∈ G j₀ ∧ ∀ k, i₀ ≤ k → k < j₀ → ej ∉ G k := by
    by_contra h; push Not at h
    have hCsub' : C.edges ⊆ (Finset.Icc i₀ (j₀ - 1)).biUnion G := by
      intro e he
      obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp (hCsub he)
      rw [Finset.mem_Icc] at hk
      if hkj : k = j₀ then
        obtain ⟨k', hk'ge, hk'lt, hek'⟩ := h e he (hkj ▸ hek)
        exact Finset.mem_biUnion.mpr ⟨k', Finset.mem_Icc.mpr ⟨hk'ge, by omega⟩, hek'⟩
      else
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk.1, by omega⟩, hek⟩
    have ⟨hle, _⟩ := hmin C i₀ (j₀ - 1) hCbnd (by omega) (by omega) hCsub'; omega
  have heiGi1 : ei ∉ G (i₀ + 1) := heiNotGk (i₀ + 1) (by omega) (by omega)
  have hejGi1 : ej ∉ G (i₀ + 1) := hejNotGk (i₀ + 1) (by omega) (by omega)
  -- === Part C: Define Ci, CiS and show CiS is psegment ===
  let Ci := C.edges.filter (fun e => e ∈ G i₀ ∧ ∀ k, i₀ < k → k ≤ j₀ → e ∉ G k)
  have heiCi : ei ∈ Ci := Finset.mem_filter.mpr ⟨heiC, heiGi, heiNotGk⟩
  have hejnotCi : ej ∉ Ci := by
    rw [Finset.mem_filter]; push Not; intro _ _; exact ⟨j₀, by omega, le_refl _, hejGj⟩
  have hCiC : Ci ⊆ C.edges := Finset.filter_subset _ _
  obtain ⟨SCiS, hSCiSeq⟩ :=
    edgeComponentOf_isSegment C.toSegment Ci hCiC ei heiCi
  set CiS := edgeComponentOf Ci ei with hCiS_def
  have hCiSCi : CiS ⊆ Ci := edgeComponentOf_subset
  have hCiSC : CiS ⊆ C.edges := hCiSCi.trans hCiC
  have heiCiS : ei ∈ CiS := edgeComponentOf_mem heiCi
  have hejnotCiS : ej ∉ CiS := fun h => hejnotCi (hCiSCi h)
  -- CiS is psegment (not rectagon — if it were, rectagon_subset_eq forces CiS = C, but ej ∉ CiS)
  have hCiSpseg : SCiS.isPsegment := by
    rcases SCiS.endpoint_count with hall | hps
    · exfalso
      have heven : ∀ m, numClosure CiS m ∈ ({0, 2} : Set ℕ) := by
        intro m; have hd := SCiS.degree_bound m; rw [hSCiSeq] at hd
        have hno := hall m; rw [Segment.isEndpoint, hSCiSeq] at hno
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        rcases hd with h | h | h
        · simp [h]
        · exact absurd h hno
        · simp [h]
      have hne : CiS.Nonempty := by rw [← hSCiSeq]; exact SCiS.nonempty
      let RCiS : Rectagon := ⟨CiS, hne,
        fun f hf => C.all_edges f (hCiSC hf), heven,
        fun T hT hTne hTcl => by
          simp only [show CiS = SCiS.edges from hSCiSeq.symm] at hT hTcl ⊢
          exact SCiS.connected T hT hTne hTcl⟩
      exact hejnotCiS (by
        have h : CiS = C.edges := rectagon_subset_eq RCiS C.toSegment hCiSC
        rw [h]; exact hejC)
    · exact hps
  -- Endpoints of CiS
  obtain ⟨a, b, hab, ha_ep, hb_ep, huniq_ep⟩ := hCiSpseg
  rw [Segment.isEndpoint, hSCiSeq] at ha_ep hb_ep
  -- === Part D: Endpoints of CiS ∈ cls(G(i₀+1)) ===
  -- Helper: singleton in curveCells from an edge
  have sCC : ∀ (F : Finset (Set E2)) (e : Set E2) (m : ℤ × ℤ),
      e ∈ F → pointI m ∈ closure e → ({pointI m} : Set E2) ∈ curveCells F := by
    intro F e m heF hcl; simp only [curveCells, Set.mem_union, Set.mem_setOf]; right
    exact ⟨m, rfl, closure_mono (Set.subset_sUnion_of_mem (Finset.mem_coe.mpr heF)) hcl⟩
  have ep_in_cls : ∀ m, numClosure CiS m = 1 → m ∈ cls (G (i₀ + 1)) := by
    intro m hm
    obtain ⟨e, ⟨heC, heNotCiS, hcl_e⟩, _⟩ := endpoint_sub_rectagon CiS C m hCiSC hm
    -- e ∉ Ci (because e is adj to CiS and not in CiS, but CiS is the component)
    have heNotCi : e ∉ Ci := by
      intro heCi
      obtain ⟨e', ⟨he'mem, he'cl⟩, _⟩ := (numClosure_eq_one_iff CiS m).mp hm
      exact heNotCiS (edgeComponentOf_closed e' he'mem e heCi
        (fun h => heNotCiS (h ▸ he'mem)) ⟨pointI m, he'cl, hcl_e⟩)
    -- Get e' ∈ CiS ⊆ G(i₀) at m
    obtain ⟨e', ⟨he'CiS, he'cl⟩, _⟩ := (numClosure_eq_one_iff CiS m).mp hm
    have he'Gi : e' ∈ G i₀ := ((Finset.mem_filter.mp (hCiSCi he'CiS)).2).1
    -- Step 1: e ∉ G(y) for y > i₀+1 (by curveCells disjointness)
    have hNotGy : ∀ y, i₀ + 1 < y → y ≤ N → e ∉ G y := by
      intro y hygt hyN heGy
      exact Set.disjoint_left.mp (hdisjoint i₀ y (by omega) hyN (by omega))
        (sCC (G i₀) e' m he'Gi he'cl) (sCC (G y) e m heGy hcl_e)
    -- e ∈ Icc(i₀, j₀).biUnion G
    obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp (hCsub heC)
    rw [Finset.mem_Icc] at hk
    -- Show e ∈ G(i₀+1) by case analysis on k
    suffices hGoal : e ∈ G (i₀ + 1) from ⟨e, hGoal, hcl_e⟩
    by_cases hki : k = i₀
    · -- e ∈ G(i₀): since e ∉ Ci, ∃ k' > i₀ with e ∈ G(k')
      rw [Finset.mem_filter] at heNotCi; push Not at heNotCi
      obtain ⟨k', hk'gt, hk'le, hek'⟩ := heNotCi heC (hki ▸ hek)
      -- k' can't be > i₀+1 by Step 1, so k' = i₀+1
      by_contra hne
      have hk'ne : k' ≠ i₀ + 1 := fun h => hne (h ▸ hek')
      exact hNotGy k' (by omega) (by omega) hek'
    · by_cases hki1 : k = i₀ + 1
      · exact hki1 ▸ hek
      · exfalso; exact hNotGy k (by omega) (by omega) hek
  -- Endpoints a, b ∈ cls(G(i₀+1))
  have ha_cls : a ∈ cls (G (i₀ + 1)) := ep_in_cls a ha_ep
  have hb_cls : b ∈ cls (G (i₀ + 1)) := ep_in_cls b hb_ep
  -- Endpoints a, b ∈ cls(C.edges)
  have ha_clsC : a ∈ cls C.edges := cls_subset hCiSC (endpoint_subset_cls CiS
    (fun f hf => C.all_edges f (hCiSC hf)) ha_ep)
  have hb_clsC : b ∈ cls C.edges := cls_subset hCiSC (endpoint_subset_cls CiS
    (fun f hf => C.all_edges f (hCiSC hf)) hb_ep)
  -- segment_end CiS a b
  have hCiS_se : segment_end CiS a b :=
    ⟨SCiS, hSCiSeq,
      show SCiS.isEndpoint a by rw [Segment.isEndpoint, hSCiSeq]; exact ha_ep,
      show SCiS.isEndpoint b by rw [Segment.isEndpoint, hSCiSeq]; exact hb_ep,
      hab, fun m hm =>
      huniq_ep m (show SCiS.isEndpoint m by rw [Segment.isEndpoint]; exact hm)⟩
  -- === Part E: Cut C at a, b; build X; choose minimal E ===
  obtain ⟨A, B, hA_se, hB_se, hCAB, hABdisj, hABcls⟩ :=
    cut_rectagon_cls C hab ha_clsC hb_clsC
  -- Identify which half contains ei and which contains ej
  have heiAB : ei ∈ A ∨ ei ∈ B :=
    Finset.mem_union.mp (hCAB ▸ heiC)
  have hejAB : ej ∈ A ∨ ej ∈ B :=
    Finset.mem_union.mp (hCAB ▸ hejC)
  -- CiS ⊆ C, so CiS ⊆ A ∪ B
  -- By cut_rectagon_unique: CiS is segment_end a b and CiS ⊆ C, so CiS = A or CiS = B
  obtain hCiS_eq_A | hCiS_eq_B := cut_rectagon_unique C A B CiS a b
    (show A ⊆ C.edges from hCAB ▸ Finset.subset_union_left)
    (show B ⊆ C.edges from hCAB ▸ Finset.subset_union_right)
    hCiSC hA_se hB_se hCiS_se hCAB hABdisj
  · -- CiS = A: so ei ∈ A and ej ∈ B
    rw [hCiS_eq_A] at hejnotCiS heiCiS
    have hejB : ej ∈ B := hejAB.resolve_left hejnotCiS
    -- Swap so that A contains ei and B contains ej (already the case here)
    -- Build path set X ⊆ C ∪ G(i₀+1) from a to b avoiding ei, ej
    -- Existence: G(i₀+1) is conn2 → conn → has path from a to b ⊆ G(i₀+1) ⊆ C ∪ G(i₀+1)
    have hconn_succ := conn2_imp_conn (hedge (i₀ + 1) (by omega)) (hconn (i₀ + 1) (by omega))
    obtain ⟨S₀, hS₀sub, hS₀se⟩ := hconn_succ a b ha_cls hb_cls hab
    -- S₀ ⊆ G(i₀+1) ⊆ C.edges ∪ G(i₀+1)
    have hS₀X : S₀ ⊆ C.edges ∪ G (i₀ + 1) := hS₀sub.trans Finset.subset_union_right
    have hS₀_no_ei : ei ∉ S₀ := fun h => heiGi1 (hS₀sub h)
    have hS₀_no_ej : ej ∉ S₀ := fun h => hejGi1 (hS₀sub h)
    -- Minimize |S \ C.edges| over all such paths
    let X : Set (Finset (Set E2)) := {S | S ⊆ C.edges ∪ G (i₀ + 1) ∧
      ei ∉ S ∧ ej ∉ S ∧ segment_end S a b}
    have hXne : X.Nonempty := ⟨S₀, hS₀X, hS₀_no_ei, hS₀_no_ej, hS₀se⟩
    have hXfin : X.Finite :=
      ((C.edges ∪ G (i₀ + 1)).powerset.finite_toSet).subset
        (fun S hS => Finset.mem_powerset.mpr hS.1)
    obtain ⟨E, ⟨hEsub, hEnoei, hEnoej, hEse⟩, hEmin⟩ :=
      exists_min_image_nat hXne hXfin (f := fun S => (S \ C.edges).card)
    -- E is not a subset of C (otherwise it equals A or B, contradicting ei/ej avoidance)
    have hEnotC : ¬E ⊆ C.edges := by
      intro hEC
      obtain hEA | hEB := cut_rectagon_unique C A B E a b
        (hCAB ▸ Finset.subset_union_left) (hCAB ▸ Finset.subset_union_right) hEC
        hA_se hB_se hEse hCAB hABdisj
      · exact hEnoei (hEA ▸ heiCiS)
      · exact hEnoej (hEB ▸ hejB)
    -- === Part F: Apply lemma5 to get E' ===
    have hEpseg : ∃ S : Segment, S.edges = E ∧ S.isPsegment := by
      have ⟨SE, hSEeq, ha_ep', hb_ep', _, huniq'⟩ := hEse
      exact ⟨SE, hSEeq, a, b, hab, ha_ep', hb_ep', huniq'⟩
    have hEep : {m | numClosure E m = 1} ⊆ cls C.edges := by
      intro m hm; simp only [Set.mem_setOf] at hm
      have ⟨SE, hSEeq, _, _, _, huniq'⟩ := hEse
      have : m = a ∨ m = b :=
        huniq' m (show SE.isEndpoint m by rw [Segment.isEndpoint, hSEeq]; exact hm)
      rcases this with rfl | rfl <;> assumption
    obtain ⟨E', hE'E, ⟨SE', hSE'eq, hSE'pseg⟩, hE'C, hE'cls⟩ :=
      conn2_sequence_lemma5 C E hEnotC hEpseg hEep
    -- === Part G: E' ⊆ G(i₀+1) (via conn_splice + minimality) ===
    -- E' endpoints
    have hSE'pseg_save := hSE'pseg
    obtain ⟨a', b', hab', ha'_ep, hb'_ep, huniq'_ep⟩ := hSE'pseg
    rw [Segment.isEndpoint, hSE'eq] at ha'_ep hb'_ep
    have hE'_endpoint_set : {m | numClosure E' m = 1} = {a', b'} := by
      ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hm; exact huniq'_ep m
          (show SE'.isEndpoint m by rwa [Segment.isEndpoint, hSE'eq])
      · rintro (rfl | rfl) <;> assumption
    have hE'se : segment_end E' a' b' :=
      ⟨SE', hSE'eq,
        show SE'.isEndpoint a' by rw [Segment.isEndpoint, hSE'eq]; exact ha'_ep,
        show SE'.isEndpoint b' by rw [Segment.isEndpoint, hSE'eq]; exact hb'_ep,
        hab', huniq'_ep⟩
    -- Show E' ⊆ G(i₀+1): E' ⊆ E ⊆ C ∪ G(i₀+1), and E' disjoint from C
    have hE'Gi1 : E' ⊆ G (i₀ + 1) := by
      intro e he
      have he_sub := hEsub (hE'E he)
      rw [Finset.mem_union] at he_sub
      rcases he_sub with heC | heGi1
      · exact absurd heC (Finset.disjoint_left.mp hE'C he)
      · exact heGi1
    -- a', b' ∈ cls C.edges (from hE'cls)
    have ha'_clsC : a' ∈ cls C.edges := by
      have h := hE'cls ▸ hE'_endpoint_set ▸ (show a' ∈ ({a', b'} : Set _) from
        Set.mem_insert _ _)
      exact h.2
    have hb'_clsC : b' ∈ cls C.edges := by
      have h := hE'cls ▸ hE'_endpoint_set ▸ (show b' ∈ ({a', b'} : Set _) from
        Set.mem_insert_of_mem _ rfl)
      exact h.2
    -- === Part H: ∃ E'' / ¬∃ E'' case split ===
    -- If ∃ E'' ⊆ C avoiding ei, ej with segment_end a' b': use conn_splice to contradict
    -- E's minimality. Otherwise, cut at a', b' and build the triple.
    by_cases hE'' : ∃ (E'' : Finset (Set E2)),
        E'' ⊆ C.edges ∧ ei ∉ E'' ∧ ej ∉ E'' ∧ segment_end E'' a' b'
    · -- Case ∃ E'': conn_splice gives a smaller element of X
      obtain ⟨E'', hE''C, hE''noei, hE''noej, hE''se⟩ := hE''
      obtain ⟨B', hB'se, hB'sub⟩ := conn_splice E E' E'' a b a' b' hEse hE'se hE''se hE'E
      have hB'X : B' ∈ X := by
        refine ⟨?_, ?_, ?_, hB'se⟩
        · intro e he; have := hB'sub he; rw [Finset.mem_union] at this
          rcases this with heD | heE''
          · exact hEsub (Finset.mem_sdiff.mp heD).1
          · exact Finset.mem_union_left _ (hE''C heE'')
        · intro hei; have := hB'sub hei; rw [Finset.mem_union] at this
          rcases this with h | h
          · exact hEnoei (Finset.mem_sdiff.mp h).1
          · exact hE''noei h
        · intro hej; have := hB'sub hej; rw [Finset.mem_union] at this
          rcases this with h | h
          · exact hEnoej (Finset.mem_sdiff.mp h).1
          · exact hE''noej h
      -- |B' \ C| < |E \ C|: B' \ C ⊆ (E \ E') \ C ⊊ E \ C
      have hcard_lt : (B' \ C.edges).card < (E \ C.edges).card := by
        have hbcsub : B' \ C.edges ⊆ (E \ C.edges) \ E' := by
          intro e he; rw [Finset.mem_sdiff] at he ⊢
          rw [Finset.mem_sdiff]; constructor
          · have := hB'sub he.1; rw [Finset.mem_union] at this
            rcases this with h | h
            · exact ⟨(Finset.mem_sdiff.mp h).1, he.2⟩
            · exact absurd (hE''C h) he.2
          · intro heE'
            have hmem := hB'sub he.1; rw [Finset.mem_union] at hmem
            rcases hmem with hh | hh
            · exact (Finset.mem_sdiff.mp hh).2 heE'
            · exact absurd (hE''C hh) (Finset.disjoint_left.mp hE'C heE')
        have hE'ne : E'.Nonempty := by rw [← hSE'eq]; exact SE'.nonempty
        have hE'sub_EC : E' ⊆ E \ C.edges := by
          intro e he
          rw [Finset.mem_sdiff]; exact ⟨hE'E he, Finset.disjoint_left.mp hE'C he⟩
        calc (B' \ C.edges).card
            ≤ ((E \ C.edges) \ E').card := Finset.card_le_card hbcsub
          _ < (E \ C.edges).card := card_subset_lt Finset.sdiff_subset (by
              intro heq; obtain ⟨e₀, he₀⟩ := hE'ne
              have := hE'sub_EC he₀; rw [← heq] at this
              exact (Finset.mem_sdiff.mp this).2 he₀)
      exact absurd (hEmin B' hB'X) (Nat.not_le.mpr hcard_lt)
    · -- Case ¬∃ E'': cut C at a', b' and build isPsegmentTriple
      push Not at hE''
      obtain ⟨A', B', hA'_se, hB'_se, hCA'B', hA'B'disj, hA'B'cls⟩ :=
        cut_rectagon_cls C hab' ha'_clsC hb'_clsC
      -- ei, ej in different halves (using ¬∃ E'')
      have heiA'B' : ei ∈ A' ∨ ei ∈ B' :=
        Finset.mem_union.mp (hCA'B' ▸ heiC)
      have hejA'B' : ej ∈ A' ∨ ej ∈ B' :=
        Finset.mem_union.mp (hCA'B' ▸ hejC)
      have hei_ej_diff : (ei ∈ A' ∧ ej ∈ B') ∨ (ei ∈ B' ∧ ej ∈ A') := by
        rcases heiA'B' with heiA' | heiB' <;> rcases hejA'B' with hejA' | hejB'
        · exfalso; exact hE'' B' (show B' ⊆ C.edges from hCA'B' ▸ Finset.subset_union_right)
            (Finset.disjoint_left.mp hA'B'disj heiA')
            (Finset.disjoint_left.mp hA'B'disj hejA') hB'_se
        · left; exact ⟨heiA', hejB'⟩
        · right; exact ⟨heiB', hejA'⟩
        · exfalso; exact hE'' A' (show A' ⊆ C.edges from hCA'B' ▸ Finset.subset_union_left)
            (Finset.disjoint_right.mp hA'B'disj heiB')
            (Finset.disjoint_right.mp hA'B'disj hejB') hA'_se
      -- Helper: derive final contradiction given half assignments
      -- Fei = half with ei, Fej = half with ej
      suffices hgoal : ∀ (Fei Fej : Finset (Set E2)),
          segment_end Fei a' b' → segment_end Fej a' b' →
          C.edges = Fei ∪ Fej → Disjoint Fei Fej → cls Fei ∩ cls Fej = {a', b'} →
          ei ∈ Fei → ej ∈ Fej → False by
        rcases hei_ej_diff with ⟨heiA', hejB'⟩ | ⟨heiB', hejA'⟩
        · exact hgoal A' B' hA'_se hB'_se hCA'B' hA'B'disj hA'B'cls heiA' hejB'
        · exact hgoal B' A' hB'_se hA'_se
            (hCA'B'.trans (Finset.union_comm A' B')) hA'B'disj.symm
            (Set.inter_comm (cls A') (cls B') ▸ hA'B'cls) heiB' hejA'
      intro Fei Fej hFei_se hFej_se hCFeFj hFeFjdisj hFeFjcls heiF hejF
      -- Disjointness with E'
      have hFeiE'disj : Disjoint Fei E' :=
        Disjoint.mono_left (hCFeFj ▸ Finset.subset_union_left) hE'C.symm
      have hFejE'disj : Disjoint Fej E' :=
        Disjoint.mono_left (hCFeFj ▸ Finset.subset_union_right) hE'C.symm
      -- cls intersections
      have hcls_FeiE : cls Fei ∩ cls E' = {a', b'} := by
        apply Set.Subset.antisymm
        · intro m ⟨hm1, hm2⟩
          have hmem : m ∈ cls E' ∩ cls C.edges :=
            Set.mem_inter hm2 (cls_subset (hCFeFj ▸ Finset.subset_union_left) hm1)
          rw [hE'cls, hE'_endpoint_set] at hmem; exact hmem
        · intro m hm
          exact ⟨(show m ∈ cls Fei ∩ cls Fej from hFeFjcls ▸ hm).1,
            endpoint_subset_cls E'
              (fun f hf => SE'.all_edges f (hSE'eq.symm ▸ hf))
              (show m ∈ {x | numClosure E' x = 1} from hE'_endpoint_set ▸ hm)⟩
      have hcls_FejE : cls Fej ∩ cls E' = {a', b'} := by
        apply Set.Subset.antisymm
        · intro m ⟨hm1, hm2⟩
          have hmem : m ∈ cls E' ∩ cls C.edges :=
            Set.mem_inter hm2 (cls_subset (hCFeFj ▸ Finset.subset_union_right) hm1)
          rw [hE'cls, hE'_endpoint_set] at hmem; exact hmem
        · intro m hm
          exact ⟨(show m ∈ cls Fei ∩ cls Fej from hFeFjcls ▸ hm).2,
            endpoint_subset_cls E'
              (fun f hf => SE'.all_edges f (hSE'eq.symm ▸ hf))
              (show m ∈ {x | numClosure E' x = 1} from hE'_endpoint_set ▸ hm)⟩
      -- Endpoint sets
      have hFei_ep : {m | numClosure Fei m = 1} = {a', b'} := by
        obtain ⟨S, hSeq, hSa, hSb, _, huniq⟩ := hFei_se
        ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
        · intro hm; exact huniq m (by rw [Segment.isEndpoint, hSeq]; exact hm)
        · rintro (rfl | rfl) <;> [rwa [Segment.isEndpoint, hSeq] at hSa;
            rwa [Segment.isEndpoint, hSeq] at hSb]
      have hFej_ep : {m | numClosure Fej m = 1} = {a', b'} := by
        obtain ⟨S, hSeq, hSa, hSb, _, huniq⟩ := hFej_se
        ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
        · intro hm; exact huniq m (by rw [Segment.isEndpoint, hSeq]; exact hm)
        · rintro (rfl | rfl) <;> [rwa [Segment.isEndpoint, hSeq] at hSa;
            rwa [Segment.isEndpoint, hSeq] at hSb]
      -- Build isPsegmentTriple Fei Fej E'
      have htrip : isPsegmentTriple Fei Fej E' := by
        have ⟨SFei, hSFeieq, ha'Fei, hb'Fei, _, huniqFei⟩ := hFei_se
        have ⟨SFej, hSFejeq, ha'Fej, hb'Fej, _, huniqFej⟩ := hFej_se
        refine ⟨⟨SFei, hSFeieq, ?_⟩, ⟨SFej, hSFejeq, ?_⟩, ⟨SE', hSE'eq, hSE'pseg_save⟩,
          ⟨C, hCFeFj⟩, ?_, ?_,
          hFeFjdisj, hFeiE'disj, hFejE'disj,
          ?_, ?_, ?_, hFei_ep.trans hFej_ep.symm, hFej_ep.trans hE'_endpoint_set.symm⟩
        · exact ⟨a', b', hab', ha'Fei, hb'Fei, huniqFei⟩
        · exact ⟨a', b', hab', ha'Fej, hb'Fej, huniqFej⟩
        · exact segment_end_union_rectagon hFei_se hE'se hFeiE'disj hcls_FeiE
        · exact segment_end_union_rectagon hFej_se hE'se hFejE'disj hcls_FejE
        · rw [hFeFjcls, hFei_ep]
        · rw [hcls_FejE, hFei_ep]
        · rw [hcls_FeiE, hFei_ep]
      -- === Part I: Final contradiction via bounded_triple_inner_union ===
      -- BoundedSet(Fej ∪ E' ∪ Fei) p via bounded_avoidance_subset
      have hCsub_range : C.edges ⊆ (Finset.range (N + 1)).biUnion G := by
        intro e he; obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp (hCsub he)
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr
          (by rw [Finset.mem_Icc] at hk; omega), hek⟩
      have hFEFsub : Fej ∪ E' ∪ Fei ⊆ (Finset.range (N + 1)).biUnion G := by
        intro e he; rw [Finset.mem_union, Finset.mem_union] at he
        rcases he with (heFej | heE') | heFei
        · exact hCsub_range (hCFeFj ▸ Finset.mem_union_right _ heFej)
        · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_range.mpr (by omega), hE'Gi1 heE'⟩
        · exact hCsub_range (hCFeFj ▸ Finset.mem_union_left _ heFei)
      have hFEF_bnd : BoundedSet (Fej ∪ E' ∪ Fei) p := by
        apply bounded_avoidance_subset C.edges _ p hCbnd
        · intro e he; rw [Finset.mem_union, Finset.mem_union]
          rw [hCFeFj, Finset.mem_union] at he
          rcases he with heFei | heFej
          · right; exact heFei
          · left; left; exact heFej
        · intro e he; rw [Finset.mem_union, Finset.mem_union] at he
          rcases he with (heFej | heE') | heFei
          · exact C.all_edges e (hCFeFj ▸ Finset.mem_union_right _ heFej)
          · exact hedge (i₀ + 1) (by omega) e (hE'Gi1 heE')
          · exact C.all_edges e (hCFeFj ▸ Finset.mem_union_left _ heFei)
        · exact conn2_rectagon C
        · exact bounded_set_curve_cell_empty _ _ p hbnd hFEFsub
      -- Apply bounded_triple_inner_union (rotated: Fej E' Fei)
      have htrip' := isPsegmentTriple_rotate htrip
      have hFEF_split := bounded_triple_inner_union Fej E' Fei htrip'
      have hp_split := hFEF_split (Set.mem_setOf.mpr hFEF_bnd)
      rw [Set.mem_union, Set.mem_setOf, Set.mem_setOf] at hp_split
      rcases hp_split with hFejE_bnd | hEFei_bnd
      · -- Contradiction: BoundedSet(Fej ∪ E') p but card diff < C
        obtain ⟨R, hR⟩ := htrip.2.2.2.2.2.1 -- Rectagon for Fej ∪ E'
        have hRsub : R.edges ⊆ (Finset.Icc i₀ j₀).biUnion G := by
          rw [hR]; intro e he; rw [Finset.mem_union] at he
          rcases he with heFej | heE'
          · exact hCsub (hCFeFj ▸ Finset.mem_union_right _ heFej)
          · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
              hE'Gi1 heE'⟩
        have ⟨_, hcard⟩ := hmin R i₀ j₀ (hR ▸ hFejE_bnd) (by omega) hj₀N hRsub
        have := hcard rfl
        have : (R.edges \ G (i₀ + 1)).card < (C.edges \ G (i₀ + 1)).card := by
          rw [hR]; apply card_subset_lt
          · intro e he; rw [Finset.mem_sdiff] at he ⊢; rw [Finset.mem_union] at he
            rcases he.1 with heFej | heE'
            · exact ⟨hCFeFj ▸ Finset.mem_union_right _ heFej, he.2⟩
            · exact absurd (hE'Gi1 heE') he.2
          · intro heq
            have : ei ∈ C.edges \ G (i₀ + 1) := Finset.mem_sdiff.mpr ⟨heiC, heiGi1⟩
            rw [← heq, Finset.mem_sdiff, Finset.mem_union] at this
            exact this.1.elim (Finset.disjoint_left.mp hFeFjdisj heiF)
              (Finset.disjoint_left.mp hFeiE'disj heiF)
        omega
      · -- Contradiction: BoundedSet(E' ∪ Fei) p but card diff < C
        obtain ⟨R, hR⟩ := htrip.2.2.2.2.1 -- Rectagon for Fei ∪ E'
        have hRsub : R.edges ⊆ (Finset.Icc i₀ j₀).biUnion G := by
          rw [hR]; intro e he; rw [Finset.mem_union] at he
          rcases he with heFei | heE'
          · exact hCsub (hCFeFj ▸ Finset.mem_union_left _ heFei)
          · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
              hE'Gi1 heE'⟩
        have ⟨_, hcard⟩ := hmin R i₀ j₀ (show BoundedSet R.edges p by
          rw [hR, Finset.union_comm]; exact hEFei_bnd) (by omega) hj₀N hRsub
        have := hcard rfl
        have : (R.edges \ G (i₀ + 1)).card < (C.edges \ G (i₀ + 1)).card := by
          rw [hR]; apply card_subset_lt
          · intro e he; rw [Finset.mem_sdiff] at he ⊢; rw [Finset.mem_union] at he
            rcases he.1 with heFei | heE'
            · exact ⟨hCFeFj ▸ Finset.mem_union_left _ heFei, he.2⟩
            · exact absurd (hE'Gi1 heE') he.2
          · intro heq
            have : ej ∈ C.edges \ G (i₀ + 1) := Finset.mem_sdiff.mpr ⟨hejC, hejGi1⟩
            rw [← heq, Finset.mem_sdiff, Finset.mem_union] at this
            exact this.1.elim (Finset.disjoint_right.mp hFeFjdisj hejF)
              (Finset.disjoint_left.mp hFejE'disj hejF)
        omega
  · -- CiS = B: symmetric — ei ∈ B, ej ∈ A
    rw [hCiS_eq_B] at hejnotCiS heiCiS
    have hejA : ej ∈ A := hejAB.resolve_right hejnotCiS
    -- Same proof with A ↔ B swapped
    have hconn_succ := conn2_imp_conn (hedge (i₀ + 1) (by omega)) (hconn (i₀ + 1) (by omega))
    obtain ⟨S₀, hS₀sub, hS₀se⟩ := hconn_succ a b ha_cls hb_cls hab
    let X : Set (Finset (Set E2)) := {S | S ⊆ C.edges ∪ G (i₀ + 1) ∧
      ei ∉ S ∧ ej ∉ S ∧ segment_end S a b}
    have hXne : X.Nonempty := ⟨S₀, hS₀sub.trans Finset.subset_union_right,
      fun h => heiGi1 (hS₀sub h), fun h => hejGi1 (hS₀sub h), hS₀se⟩
    have hXfin : X.Finite :=
      ((C.edges ∪ G (i₀ + 1)).powerset.finite_toSet).subset
        (fun S hS => Finset.mem_powerset.mpr hS.1)
    obtain ⟨E, ⟨hEsub, hEnoei, hEnoej, hEse⟩, hEmin⟩ :=
      exists_min_image_nat hXne hXfin (f := fun S => (S \ C.edges).card)
    have hEnotC : ¬E ⊆ C.edges := by
      intro hEC
      obtain hEA | hEB := cut_rectagon_unique C A B E a b
        (hCAB ▸ Finset.subset_union_left) (hCAB ▸ Finset.subset_union_right) hEC
        hA_se hB_se hEse hCAB hABdisj
      · exact hEnoej (hEA ▸ hejA)
      · exact hEnoei (hEB ▸ heiCiS)
    have hEpseg : ∃ S : Segment, S.edges = E ∧ S.isPsegment := by
      have ⟨SE, hSEeq, ha_ep', hb_ep', _, huniq'⟩ := hEse
      exact ⟨SE, hSEeq, a, b, hab, ha_ep', hb_ep', huniq'⟩
    have hEep : {m | numClosure E m = 1} ⊆ cls C.edges := by
      intro m hm; simp only [Set.mem_setOf] at hm
      have ⟨SE, hSEeq, _, _, _, huniq'⟩ := hEse
      rcases huniq' m (show SE.isEndpoint m by
        rw [Segment.isEndpoint, hSEeq]; exact hm) with rfl | rfl
      · exact ha_clsC
      · exact hb_clsC
    obtain ⟨E', hE'E, ⟨SE', hSE'eq, hSE'pseg⟩, hE'C, hE'cls⟩ :=
      conn2_sequence_lemma5 C E hEnotC hEpseg hEep
    have hSE'pseg_save := hSE'pseg
    obtain ⟨a', b', hab', ha'_ep, hb'_ep, huniq'_ep⟩ := hSE'pseg
    rw [Segment.isEndpoint, hSE'eq] at ha'_ep hb'_ep
    have hE'_endpoint_set : {m | numClosure E' m = 1} = {a', b'} := by
      ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
      · intro hm; exact huniq'_ep m
          (show SE'.isEndpoint m by rwa [Segment.isEndpoint, hSE'eq])
      · rintro (rfl | rfl) <;> assumption
    have hE'se : segment_end E' a' b' :=
      ⟨SE', hSE'eq,
        show SE'.isEndpoint a' by rw [Segment.isEndpoint, hSE'eq]; exact ha'_ep,
        show SE'.isEndpoint b' by rw [Segment.isEndpoint, hSE'eq]; exact hb'_ep,
        hab', huniq'_ep⟩
    have hE'Gi1 : E' ⊆ G (i₀ + 1) := by
      intro e he; have := hEsub (hE'E he); rw [Finset.mem_union] at this
      exact this.resolve_left (Finset.disjoint_left.mp hE'C he)
    have ha'_clsC : a' ∈ cls C.edges := by
      have h := hE'cls ▸ hE'_endpoint_set ▸ (show a' ∈ ({a', b'} : Set _) from
        Set.mem_insert _ _); exact h.2
    have hb'_clsC : b' ∈ cls C.edges := by
      have h := hE'cls ▸ hE'_endpoint_set ▸ (show b' ∈ ({a', b'} : Set _) from
        Set.mem_insert_of_mem _ rfl); exact h.2
    -- Same ∃ E'' / ¬∃ E'' case split
    by_cases hE''case : ∃ (E'' : Finset (Set E2)),
        E'' ⊆ C.edges ∧ ei ∉ E'' ∧ ej ∉ E'' ∧ segment_end E'' a' b'
    · obtain ⟨E'', hE''C, hE''noei, hE''noej, hE''se⟩ := hE''case
      obtain ⟨B', hB'se, hB'sub⟩ := conn_splice E E' E'' a b a' b' hEse hE'se hE''se hE'E
      have hB'X : B' ∈ X := by
        refine ⟨?_, ?_, ?_, hB'se⟩
        · intro e he; have := hB'sub he; rw [Finset.mem_union] at this
          rcases this with h | h
          · exact hEsub (Finset.mem_sdiff.mp h).1
          · exact Finset.mem_union_left _ (hE''C h)
        · intro hei; have := hB'sub hei; rw [Finset.mem_union] at this
          rcases this with h | h
          · exact hEnoei (Finset.mem_sdiff.mp h).1
          · exact hE''noei h
        · intro hej; have := hB'sub hej; rw [Finset.mem_union] at this
          rcases this with h | h
          · exact hEnoej (Finset.mem_sdiff.mp h).1
          · exact hE''noej h
      have hcard_lt : (B' \ C.edges).card < (E \ C.edges).card := by
        have hbcsub : B' \ C.edges ⊆ (E \ C.edges) \ E' := by
          intro e he; rw [Finset.mem_sdiff] at he ⊢; rw [Finset.mem_sdiff]; constructor
          · have := hB'sub he.1; rw [Finset.mem_union] at this; rcases this with h | h
            · exact ⟨(Finset.mem_sdiff.mp h).1, he.2⟩
            · exact absurd (hE''C h) he.2
          · intro heE'
            have hmem := hB'sub he.1; rw [Finset.mem_union] at hmem
            rcases hmem with hh | hh
            · exact (Finset.mem_sdiff.mp hh).2 heE'
            · exact absurd (hE''C hh) (Finset.disjoint_left.mp hE'C heE')
        have hE'ne : E'.Nonempty := by rw [← hSE'eq]; exact SE'.nonempty
        calc (B' \ C.edges).card
            ≤ ((E \ C.edges) \ E').card := Finset.card_le_card hbcsub
          _ < (E \ C.edges).card := card_subset_lt Finset.sdiff_subset (by
              intro heq; obtain ⟨e₀, he₀⟩ := hE'ne
              have := Finset.mem_sdiff.mpr ⟨hE'E he₀, Finset.disjoint_left.mp hE'C he₀⟩
              rw [← heq] at this; exact (Finset.mem_sdiff.mp this).2 he₀)
      exact absurd (hEmin B' hB'X) (Nat.not_le.mpr hcard_lt)
    · push Not at hE''case
      obtain ⟨A', B', hA'_se, hB'_se, hCA'B', hA'B'disj, hA'B'cls⟩ :=
        cut_rectagon_cls C hab' ha'_clsC hb'_clsC
      have hei_ej_diff : (ei ∈ A' ∧ ej ∈ B') ∨ (ei ∈ B' ∧ ej ∈ A') := by
        have heiAB' := Finset.mem_union.mp (hCA'B' ▸ heiC)
        have hejAB' := Finset.mem_union.mp (hCA'B' ▸ hejC)
        rcases heiAB' with heiA' | heiB' <;> rcases hejAB' with hejA' | hejB'
        · exfalso; exact hE''case B' (show B' ⊆ C.edges from hCA'B' ▸ Finset.subset_union_right)
            (Finset.disjoint_left.mp hA'B'disj heiA')
            (Finset.disjoint_left.mp hA'B'disj hejA') hB'_se
        · left; exact ⟨heiA', hejB'⟩
        · right; exact ⟨heiB', hejA'⟩
        · exfalso; exact hE''case A' (show A' ⊆ C.edges from hCA'B' ▸ Finset.subset_union_left)
            (Finset.disjoint_right.mp hA'B'disj heiB')
            (Finset.disjoint_right.mp hA'B'disj hejB') hA'_se
      suffices hgoal : ∀ (Fei Fej : Finset (Set E2)),
          segment_end Fei a' b' → segment_end Fej a' b' →
          C.edges = Fei ∪ Fej → Disjoint Fei Fej → cls Fei ∩ cls Fej = {a', b'} →
          ei ∈ Fei → ej ∈ Fej → False by
        rcases hei_ej_diff with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hgoal A' B' hA'_se hB'_se hCA'B' hA'B'disj hA'B'cls h1 h2
        · exact hgoal B' A' hB'_se hA'_se (hCA'B'.trans (Finset.union_comm A' B'))
            hA'B'disj.symm (Set.inter_comm (cls A') (cls B') ▸ hA'B'cls) h1 h2
      intro Fei Fej hFei_se hFej_se hCFeFj hFeFjdisj hFeFjcls heiF hejF
      have hFeiE'disj : Disjoint Fei E' :=
        Disjoint.mono_left (hCFeFj ▸ Finset.subset_union_left) hE'C.symm
      have hFejE'disj : Disjoint Fej E' :=
        Disjoint.mono_left (hCFeFj ▸ Finset.subset_union_right) hE'C.symm
      have hcls_FeiE : cls Fei ∩ cls E' = {a', b'} := by
        apply Set.Subset.antisymm
        · intro m ⟨hm1, hm2⟩
          have hmem : m ∈ cls E' ∩ cls C.edges :=
            Set.mem_inter hm2 (cls_subset (hCFeFj ▸ Finset.subset_union_left) hm1)
          rw [hE'cls, hE'_endpoint_set] at hmem; exact hmem
        · intro m hm
          exact ⟨(show m ∈ cls Fei ∩ cls Fej from hFeFjcls ▸ hm).1,
            endpoint_subset_cls E'
              (fun f hf => SE'.all_edges f (hSE'eq.symm ▸ hf))
              (show m ∈ {x | numClosure E' x = 1} from hE'_endpoint_set ▸ hm)⟩
      have hcls_FejE : cls Fej ∩ cls E' = {a', b'} := by
        apply Set.Subset.antisymm
        · intro m ⟨hm1, hm2⟩
          have hmem : m ∈ cls E' ∩ cls C.edges :=
            Set.mem_inter hm2 (cls_subset (hCFeFj ▸ Finset.subset_union_right) hm1)
          rw [hE'cls, hE'_endpoint_set] at hmem; exact hmem
        · intro m hm
          exact ⟨(show m ∈ cls Fei ∩ cls Fej from hFeFjcls ▸ hm).2,
            endpoint_subset_cls E'
              (fun f hf => SE'.all_edges f (hSE'eq.symm ▸ hf))
              (show m ∈ {x | numClosure E' x = 1} from hE'_endpoint_set ▸ hm)⟩
      have hFei_ep : {m | numClosure Fei m = 1} = {a', b'} := by
        obtain ⟨S, hSeq, hSa, hSb, _, huniq⟩ := hFei_se
        ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
        · intro hm; exact huniq m (by rw [Segment.isEndpoint, hSeq]; exact hm)
        · rintro (rfl | rfl) <;> [rwa [Segment.isEndpoint, hSeq] at hSa;
            rwa [Segment.isEndpoint, hSeq] at hSb]
      have hFej_ep : {m | numClosure Fej m = 1} = {a', b'} := by
        obtain ⟨S, hSeq, hSa, hSb, _, huniq⟩ := hFej_se
        ext m; simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
        · intro hm; exact huniq m (by rw [Segment.isEndpoint, hSeq]; exact hm)
        · rintro (rfl | rfl) <;> [rwa [Segment.isEndpoint, hSeq] at hSa;
            rwa [Segment.isEndpoint, hSeq] at hSb]
      have htrip : isPsegmentTriple Fei Fej E' := by
        have ⟨SFei, hSFeieq, ha'Fei, hb'Fei, _, huniqFei⟩ := hFei_se
        have ⟨SFej, hSFejeq, ha'Fej, hb'Fej, _, huniqFej⟩ := hFej_se
        refine ⟨⟨SFei, hSFeieq, ?_⟩, ⟨SFej, hSFejeq, ?_⟩, ⟨SE', hSE'eq, hSE'pseg_save⟩,
          ⟨C, hCFeFj⟩, ?_, ?_, hFeFjdisj, hFeiE'disj, hFejE'disj,
          ?_, ?_, ?_, hFei_ep.trans hFej_ep.symm, hFej_ep.trans hE'_endpoint_set.symm⟩
        · exact ⟨a', b', hab', ha'Fei, hb'Fei, huniqFei⟩
        · exact ⟨a', b', hab', ha'Fej, hb'Fej, huniqFej⟩
        · exact segment_end_union_rectagon hFei_se hE'se hFeiE'disj hcls_FeiE
        · exact segment_end_union_rectagon hFej_se hE'se hFejE'disj hcls_FejE
        · rw [hFeFjcls, hFei_ep]
        · rw [hcls_FejE, hFei_ep]
        · rw [hcls_FeiE, hFei_ep]
      have hCsub_range : C.edges ⊆ (Finset.range (N + 1)).biUnion G := by
        intro e he; obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp (hCsub he)
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr
          (by rw [Finset.mem_Icc] at hk; omega), hek⟩
      have hFEFsub : Fej ∪ E' ∪ Fei ⊆ (Finset.range (N + 1)).biUnion G := by
        intro e he; rw [Finset.mem_union, Finset.mem_union] at he
        rcases he with (h | h) | h
        · exact hCsub_range (hCFeFj ▸ Finset.mem_union_right _ h)
        · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_range.mpr (by omega), hE'Gi1 h⟩
        · exact hCsub_range (hCFeFj ▸ Finset.mem_union_left _ h)
      have hFEF_bnd : BoundedSet (Fej ∪ E' ∪ Fei) p := by
        apply bounded_avoidance_subset C.edges _ p hCbnd
        · intro e he; rw [Finset.mem_union, Finset.mem_union]
          rw [hCFeFj, Finset.mem_union] at he
          rcases he with h | h
          · right; exact h
          · left; left; exact h
        · intro e he; rw [Finset.mem_union, Finset.mem_union] at he
          rcases he with (h | h) | h
          · exact C.all_edges e (hCFeFj ▸ Finset.mem_union_right _ h)
          · exact hedge (i₀ + 1) (by omega) e (hE'Gi1 h)
          · exact C.all_edges e (hCFeFj ▸ Finset.mem_union_left _ h)
        · exact conn2_rectagon C
        · exact bounded_set_curve_cell_empty _ _ p hbnd hFEFsub
      have htrip' := isPsegmentTriple_rotate htrip
      have hp_split := (bounded_triple_inner_union Fej E' Fei htrip')
        (Set.mem_setOf.mpr hFEF_bnd)
      rw [Set.mem_union, Set.mem_setOf, Set.mem_setOf] at hp_split
      rcases hp_split with hFejE_bnd | hEFei_bnd
      · obtain ⟨R, hR⟩ := htrip.2.2.2.2.2.1
        have hRsub : R.edges ⊆ (Finset.Icc i₀ j₀).biUnion G := by
          rw [hR]; intro e he; rw [Finset.mem_union] at he
          rcases he with h | h
          · exact hCsub (hCFeFj ▸ Finset.mem_union_right _ h)
          · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
              hE'Gi1 h⟩
        have ⟨_, hcard⟩ := hmin R i₀ j₀ (hR ▸ hFejE_bnd) (by omega) hj₀N hRsub
        have := hcard rfl
        have : (R.edges \ G (i₀ + 1)).card < (C.edges \ G (i₀ + 1)).card := by
          rw [hR]; apply card_subset_lt
          · intro e he; rw [Finset.mem_sdiff] at he ⊢; rw [Finset.mem_union] at he
            rcases he.1 with h | h
            · exact ⟨hCFeFj ▸ Finset.mem_union_right _ h, he.2⟩
            · exact absurd (hE'Gi1 h) he.2
          · intro heq
            have : ei ∈ C.edges \ G (i₀ + 1) := Finset.mem_sdiff.mpr ⟨heiC, heiGi1⟩
            rw [← heq, Finset.mem_sdiff, Finset.mem_union] at this
            exact this.1.elim (Finset.disjoint_left.mp hFeFjdisj heiF)
              (Finset.disjoint_left.mp hFeiE'disj heiF)
        omega
      · obtain ⟨R, hR⟩ := htrip.2.2.2.2.1
        have hRsub : R.edges ⊆ (Finset.Icc i₀ j₀).biUnion G := by
          rw [hR]; intro e he; rw [Finset.mem_union] at he
          rcases he with h | h
          · exact hCsub (hCFeFj ▸ Finset.mem_union_left _ h)
          · exact Finset.mem_biUnion.mpr ⟨i₀ + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
              hE'Gi1 h⟩
        have ⟨_, hcard⟩ := hmin R i₀ j₀ (show BoundedSet R.edges p by
          rw [hR, Finset.union_comm]; exact hEFei_bnd) (by omega) hj₀N hRsub
        have := hcard rfl
        have : (R.edges \ G (i₀ + 1)).card < (C.edges \ G (i₀ + 1)).card := by
          rw [hR]; apply card_subset_lt
          · intro e he; rw [Finset.mem_sdiff] at he ⊢; rw [Finset.mem_union] at he
            rcases he.1 with h | h
            · exact ⟨hCFeFj ▸ Finset.mem_union_left _ h, he.2⟩
            · exact absurd (hE'Gi1 h) he.2
          · intro heq
            have : ej ∈ C.edges \ G (i₀ + 1) := Finset.mem_sdiff.mpr ⟨hejC, hejGi1⟩
            rw [← heq, Finset.mem_sdiff, Finset.mem_union] at this
            exact this.1.elim (Finset.disjoint_right.mp hFeFjdisj hejF)
              (Finset.disjoint_left.mp hFejE'disj hejF)
        omega

end JordanCurveTheorem
