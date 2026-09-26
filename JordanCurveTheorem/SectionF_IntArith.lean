/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionE_Parity

/-!
# Section F: Integer Arithmetic, Closed Squares, Component Filling, and Reflections
## HOL Light: Section F (Lines 9413–12021)

This section covers:
- Integer absolute value (`num_abs_of_int`) — handled by `Int.natAbs` in Mathlib
- Grid navigation inverses (`right_left`)
- Closed unit squares (`squc`) and proof that `closure (squ p) = squc p`
- Edge adjacency of squares (`adj_edge`)
- Connected component filling: every component of `ctop G` contains a square,
  and every square in a component has a nearby edge of G
- Along-segment analysis (`along_seg`)
- Reflections (`reflAf`, `reflBf`, `reflCf`) and their homeomorphism properties
- `IMAGE2` (lifting a map to act on sets of sets)
- General homeomorphism lemmas (bijection, closedness preservation)

Key downstream definitions: `squc`, `adj_edge`, `along_seg`, `reflAf`, `reflBf`,
`reflCf`, `reflAi`, `reflBi`, `reflCi`, `IMAGE2`.
-/

open Set Topology

noncomputable section

/-! ## Grid navigation inverses -/

/-- `right` and `left` are inverses, `up` and `down` are inverses,
    and `up`/`right` commute.
    HOL Light: `right_left` (line 9535). -/
@[simp] theorem right_left (m : ℤ × ℤ) : right (left m) = m := by
  simp [right, left]
@[simp] theorem left_right (m : ℤ × ℤ) : left (right m) = m := by
  simp [right, left]
@[simp] theorem up_down (m : ℤ × ℤ) : up (down m) = m := by
  simp [up, down]
@[simp] theorem down_up (m : ℤ × ℤ) : down (up m) = m := by
  simp [up, down]

/-! ## Closed unit square -/

/-- The closed unit square with bottom-left corner at `pointI m`.
    HOL Light: `squc p` (line 9548). -/
def squc (m : ℤ × ℤ) : Set E2 :=
  {z | (↑m.1 : ℝ) ≤ z 0 ∧ z 0 ≤ ↑m.1 + 1 ∧
       (↑m.2 : ℝ) ≤ z 1 ∧ z 1 ≤ ↑m.2 + 1}

/-- The closed square is closed.
    HOL Light: `squc_closed` (line 9602). -/
theorem squc_isClosed (m : ℤ × ℤ) : IsClosed (squc m) := by
  simp only [squc, setOf_and]
  apply IsClosed.inter _ (IsClosed.inter _ (IsClosed.inter _ _))
  all_goals (first
    | exact isClosed_le continuous_const (by fun_prop)
    | exact isClosed_le (by fun_prop) continuous_const)

/-- The open square is contained in the closed square.
    HOL Light: `squ_subset_sqc` (line 9613). -/
theorem squ_subset_squc (m : ℤ × ℤ) : squ m ⊆ squc m := by
  intro z hz
  simp only [squ, mem_setOf_eq] at hz
  simp only [squc, mem_setOf_eq]
  exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩

/-- The closed square decomposes as the union of interior, edges,
    and corners.
    HOL Light: `squc_union` (line 9916). -/
theorem squc_union (m : ℤ × ℤ) :
    squc m = {pointI m} ∪ {pointI (right m)} ∪
             {pointI (up m)} ∪ {pointI (right (up m))} ∪
             hEdge m ∪ hEdge (up m) ∪
             vEdge m ∪ vEdge (right m) ∪
             squ m := by
  ext z; constructor
  · -- (⊆) squc → union
    intro hz
    simp only [squc, Set.mem_setOf_eq] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    -- Case split: z 0 = m.1, m.1 < z 0 < m.1+1, z 0 = m.1+1
    -- and: z 1 = m.2, m.2 < z 1 < m.2+1, z 1 = m.2+1
    simp only [Set.mem_union, Set.mem_singleton_iff,
      hEdge, vEdge, squ, Set.mem_setOf_eq]
    rcases h1.eq_or_lt with hx | hx
    · -- z 0 = ↑m.1
      rcases h3.eq_or_lt with hy | hy
      · -- pointI m: left^8
        left; left; left; left; left; left; left; left
        ext i; fin_cases i <;> simp [pointI, point,
            WithLp.equiv, ← hx, ← hy]
      · rcases h4.eq_or_lt with hy' | hy'
        · -- pointI (up m): left^5 · right
          left; left; left; left; left; left; right
          ext i; fin_cases i <;> simp [pointI, point, up,
              WithLp.equiv, ← hx, ← hy']
        · -- vEdge m
          left; left; right
          exact ⟨hx.symm, hy, hy'⟩
    · rcases h2.eq_or_lt with hx' | hx'
      · -- z 0 = ↑m.1 + 1
        rcases h3.eq_or_lt with hy | hy
        · -- pointI (right m): left^7 · right
          left; left; left; left; left; left; left; right
          ext i; fin_cases i <;> simp [pointI, point, right,
              WithLp.equiv, ← hx', ← hy]
        · rcases h4.eq_or_lt with hy' | hy'
          · -- pointI (right (up m))
            left; left; left; left; left; right
            ext i; fin_cases i <;> simp [pointI, point,
                right, up, WithLp.equiv, ← hx', ← hy']
          · -- vEdge (right m)
            left; right
            simp only [right]
            push_cast; exact ⟨hx', hy, hy'⟩
      · -- ↑m.1 < z 0 < ↑m.1 + 1
        rcases h3.eq_or_lt with hy | hy
        · -- hEdge m
          left; left; left; left; right
          exact ⟨hx, hx', hy.symm⟩
        · rcases h4.eq_or_lt with hy' | hy'
          · -- hEdge (up m)
            left; left; left; right
            simp only [up]
            push_cast; exact ⟨hx, hx', hy'⟩
          · -- squ m (interior)
            right; exact ⟨hx, hx', hy, hy'⟩
  · -- (⊇) union → squc
    simp only [Set.mem_union, Set.mem_singleton_iff,
      squc, hEdge, vEdge, squ, Set.mem_setOf_eq,
      up, right]
    rintro ((((((((hz | hz) | hz) | hz) | hz)
      | hz) | hz) | hz) | hz)
    all_goals first
    | (subst hz; simp only [pointI_coord_fst, pointI_coord_snd]
       push_cast; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (obtain ⟨h1, h2, h3, h4⟩ := hz
       refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (obtain ⟨h1, h2, h3⟩ := hz
       push_cast at *; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: the closure witness uses a convex combination whose membership in
-- `squ` requires `simp`/`nlinarith` on four coordinate inequalities simultaneously.
/-- The closure of an open unit square is the closed unit
    square. Uses convex-combination witness with center.
    HOL Light: `squ_closure` (line 10186). -/
theorem squ_closure (m : ℤ × ℤ) :
    closure (squ m) = squc m := by
  apply Subset.antisymm
  · exact closure_minimal (squ_subset_squc m)
      (squc_isClosed m)
  · intro z hz
    simp only [squc, mem_setOf_eq] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    set c : E2 := (WithLp.equiv 2 _).symm
      ![↑m.1 + (1 : ℝ) / 2, ↑m.2 + (1 : ℝ) / 2]
    set t := min (ε / 2) (1 / 2 : ℝ)
    have ht : 0 < t := by positivity
    have hth : t ≤ 1 / 2 := min_le_right _ _
    have hte : t ≤ ε / 2 := min_le_left _ _
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    set w := (1 - t) • z + t • c
    refine ⟨w, ?_, ?_⟩
    · simp only [squ, mem_setOf_eq, w, c, gt_iff_lt]
      simp only [one_div, WithLp.equiv_symm_apply,
        Fin.isValue, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      have hx0 := mul_nonneg h1t
        (show (0 : ℝ) ≤ z.ofLp 0 - ↑m.1 by linarith)
      have hx1 := mul_nonneg h1t
        (show (0 : ℝ) ≤ ↑m.1 + 1 - z.ofLp 0
          by linarith)
      have hy0 := mul_nonneg h1t
        (show (0 : ℝ) ≤ z.ofLp 1 - ↑m.2 by linarith)
      have hy1 := mul_nonneg h1t
        (show (0 : ℝ) ≤ ↑m.2 + 1 - z.ofLp 1
          by linarith)
      exact ⟨by nlinarith, by nlinarith,
        by nlinarith, by nlinarith⟩
    · rw [dist_comm, dist_eq_norm]
      have key : w - z = t • (c - z) := by
        ext i; simp [w, smul_eq_mul]; ring
      rw [key, norm_smul, Real.norm_of_nonneg ht.le]
      have hdc : dist c z < 1 := by
        rw [EuclideanSpace.dist_eq]
        have hlt : ∑ i : Fin 2,
            dist (c.ofLp i) (z.ofLp i) ^ 2 < 1 := by
          simp only [Fin.sum_univ_two, c,
            WithLp.equiv_symm_apply, Fin.isValue,
            Matrix.cons_val_zero,
            Matrix.cons_val_one,
            Matrix.cons_val_fin_one, Real.dist_eq]
          have := (abs_sub_le_iff.mpr
            ⟨by linarith, by linarith⟩ :
            |↑m.1 + 1 / 2 - z.ofLp 0| ≤ 1 / 2)
          have := (abs_sub_le_iff.mpr
            ⟨by linarith, by linarith⟩ :
            |↑m.2 + 1 / 2 - z.ofLp 1| ≤ 1 / 2)
          nlinarith [sq_abs (↑m.1 + 1 / 2 - z.ofLp 0),
            sq_abs (↑m.2 + 1 / 2 - z.ofLp 1)]
        calc Real.sqrt _ < Real.sqrt 1 :=
              Real.sqrt_lt_sqrt
                (Finset.sum_nonneg fun i _ =>
                  by positivity)
                hlt
          _ = 1 := by simp
      calc t * ‖c - z‖
          = t * dist c z := by rw [dist_eq_norm]
        _ < t * 1 := mul_lt_mul_of_pos_left hdc ht
        _ ≤ ε / 2 := by linarith
        _ < ε := by linarith

/-- A horizontal edge is in the closure of the square below.
    HOL Light: `squ_closure_h` (line 9936). -/
theorem squ_closure_h (m : ℤ × ℤ) :
    hEdge m ⊆ closure (squ m) := by
  rw [squ_closure]; intro z hz
  simp only [hEdge, squc, mem_setOf_eq] at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.2.1],
    by linarith [hz.2.2], by linarith [hz.2.2]⟩

/-- A horizontal edge is in the closure of the square
    above.
    HOL Light: `squ_closure_up_h` (line 9981). -/
theorem squ_closure_up_h (m : ℤ × ℤ) :
    hEdge (up m) ⊆ closure (squ m) := by
  rw [squ_closure]; intro z hz
  simp only [hEdge, up, squc, mem_setOf_eq] at hz ⊢
  push_cast at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.2.1],
    by linarith [hz.2.2], by linarith [hz.2.2]⟩

/-- HOL Light: `squ_closure_down_h` (line 10026). -/
theorem squ_closure_down_h (m : ℤ × ℤ) :
    hEdge m ⊆ closure (squ (down m)) := by
  rw [squ_closure]; intro z hz
  simp only [hEdge, down, squc, mem_setOf_eq] at hz ⊢
  push_cast at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.2.1],
    by linarith [hz.2.2], by linarith [hz.2.2]⟩

/-- A vertical edge is in the closure of the square to the
    right.
    HOL Light: `squ_closure_v` (line 10040). -/
theorem squ_closure_v (m : ℤ × ℤ) :
    vEdge m ⊆ closure (squ m) := by
  rw [squ_closure]; intro z hz
  simp only [vEdge, squc, mem_setOf_eq] at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.1],
    by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- HOL Light: `squ_closure_right_v` (line 10085). -/
theorem squ_closure_right_v (m : ℤ × ℤ) :
    vEdge (right m) ⊆ closure (squ m) := by
  rw [squ_closure]; intro z hz
  simp only [vEdge, right, squc, mem_setOf_eq] at hz ⊢
  push_cast at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.1],
    by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- HOL Light: `squ_closure_left_v` (line 10134). -/
theorem squ_closure_left_v (m : ℤ × ℤ) :
    vEdge m ⊆ closure (squ (left m)) := by
  rw [squ_closure]; intro z hz
  simp only [vEdge, left, squc, mem_setOf_eq] at hz ⊢
  push_cast at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.1],
    by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-! ## Edge adjacency of squares -/

/-- Two cells are edge-adjacent if they are distinct and share an edge
    in both closures.
    HOL Light: `adj_edge` (line 10219). -/
def adjEdge (x y : Set E2) : Prop :=
  x ≠ y ∧ ∃ e : Set E2, isEdge e ∧ e ⊆ closure x ∧ e ⊆ closure y

/-- Edge adjacency is symmetric.
    HOL Light: `adj_edge_sym` (line 10223). -/
theorem adjEdge_symm (x y : Set E2) : adjEdge x y ↔ adjEdge y x := by
  simp only [adjEdge]; constructor <;> intro ⟨hne, e, he, h1, h2⟩ <;>
    exact ⟨hne.symm, e, he, h2, h1⟩

/-- Squares are edge-adjacent to their left neighbor.
    HOL Light: `adj_edge_left` (line 10232). -/
theorem adjEdge_left (m : ℤ × ℤ) :
    adjEdge (squ m) (squ (left m)) := by
  refine ⟨?_, vEdge m, Or.inr ⟨m, rfl⟩,
    squ_closure_v m, squ_closure_left_v m⟩
  intro h
  have : (WithLp.equiv 2 _).symm
      (![↑m.1 + (1 : ℝ) / 2, ↑m.2 + (1 : ℝ) / 2])
      ∈ squ (left m) :=
    h ▸ (by simp [squ, WithLp.equiv]; norm_num)
  simp [squ, left, WithLp.equiv] at this
  linarith [this.2.1]

/-- HOL Light: `adj_edge_right` (line 10251). -/
theorem adjEdge_right (m : ℤ × ℤ) :
    adjEdge (squ m) (squ (right m)) := by
  refine ⟨?_, vEdge (right m), Or.inr ⟨right m, rfl⟩,
    squ_closure_right_v m, squ_closure_v (right m)⟩
  intro h
  have : (WithLp.equiv 2 _).symm
      (![↑m.1 + (1 : ℝ) / 2, ↑m.2 + (1 : ℝ) / 2])
      ∈ squ (right m) :=
    h ▸ (by simp [squ, WithLp.equiv]; norm_num)
  simp [squ, right, WithLp.equiv] at this
  linarith [this.1]

/-- HOL Light: `adj_edge_down` (line 10269). -/
theorem adjEdge_down (m : ℤ × ℤ) :
    adjEdge (squ m) (squ (down m)) := by
  refine ⟨?_, hEdge m, Or.inl ⟨m, rfl⟩,
    squ_closure_h m, squ_closure_down_h m⟩
  intro h
  have : (WithLp.equiv 2 _).symm
      (![↑m.1 + (1 : ℝ) / 2, ↑m.2 + (1 : ℝ) / 2])
      ∈ squ (down m) :=
    h ▸ (by simp [squ, WithLp.equiv]; norm_num)
  simp only [squ, down, mem_setOf_eq, gt_iff_lt,
    WithLp.equiv_symm_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at this
  push_cast at this; linarith [this.2.2]

/-- HOL Light: `adj_edge_up` (line 10288). -/
theorem adjEdge_up (m : ℤ × ℤ) :
    adjEdge (squ m) (squ (up m)) := by
  refine ⟨?_, hEdge (up m), Or.inl ⟨up m, rfl⟩,
    squ_closure_up_h m, squ_closure_h (up m)⟩
  intro h
  have : (WithLp.equiv 2 _).symm
      (![↑m.1 + (1 : ℝ) / 2, ↑m.2 + (1 : ℝ) / 2])
      ∈ squ (up m) :=
    h ▸ (by simp [squ, WithLp.equiv]; norm_num)
  simp only [squ, up, mem_setOf_eq, gt_iff_lt,
    WithLp.equiv_symm_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at this
  push_cast at this; linarith [this.2.2]

/-! ## Component containment lemmas -/

/-- A cell not in curveCells lies in the complement. -/
private theorem cell_subset_complementCurve' (G : Segment)
    {C : Set E2} (hC : isCell C)
    (hnot : C ∉ curveCells G.edges) :
    C ⊆ complementCurve G.edges := by
  intro z hz
  simp only [complementCurve, mem_compl_iff, mem_sUnion]
  push Not; intro S hS hzS
  obtain ⟨ctS, rfl⟩ :=
    curveCells_subset_cell G.edges G.all_edges S hS
  obtain ⟨ctC, rfl⟩ := hC
  obtain ⟨_, _, huniq⟩ := cell_partition z
  have := (huniq ctC hz).trans (huniq ctS hzS).symm
  subst this; exact hnot hS

/-- Squares lie in the complement of the curve. -/
private theorem squ_subset_complementCurve (G : Segment)
    (m : ℤ × ℤ) : squ m ⊆ complementCurve G.edges :=
  cell_subset_complementCurve' G ⟨.squ m, rfl⟩
    (curveCells_not_squ G m)

/-- If an edge in G touches a lattice point, the point
    is in the union of curve cells. -/
private theorem edge_in_G_pointI_in_curveCells
    (G : Segment) {e : Set E2} (heG : e ∈ G.edges)
    {m : ℤ × ℤ} (hcl : pointI m ∈ closure e) :
    pointI m ∈ ⋃₀ (curveCells G.edges : Set (Set E2)) :=
  Set.mem_sUnion.mpr ⟨{pointI m},
    Set.mem_union_right _
      ⟨m, rfl, closure_mono
        (Set.subset_sUnion_of_mem
          (Finset.mem_coe.mpr heG)) hcl⟩, rfl⟩

/-- A connected component is a subset of the complement of the curve.
    HOL Light: `component_unions` (line 10322). -/
theorem component_subset_complementCurve (G : Segment) (x : E2) :
    connectedComponentIn (complementCurve G.edges) x ⊆
      complementCurve G.edges :=
  connectedComponentIn_subset _ _

/-- If a horizontal edge is in a component, then a surrounding rectangle
    is in the component.
    HOL Light: `comp_h_rect` (line 10331). -/
theorem comp_hEdge_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : hEdge m ⊆
      connectedComponentIn (complementCurve G.edges) x) :
    rectangle (m.1, m.2 - 1) (m.1 + 1, m.2 + 1) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzE⟩ := hEdge_nonempty m
  have h1 : z ∈ rectangle (m.1, m.2 - 1)
      (m.1 + 1, m.2 + 1) := by
    rw [rectangle_h_decomp m]
    exact Or.inl (Or.inr hzE)
  have h2 : rectangle (m.1, m.2 - 1) (m.1 + 1, m.2 + 1)
      ⊆ complementCurve G.edges := by
    rw [rectangle_h_decomp m]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G (down m))
        (fun w hw =>
          connectedComponentIn_subset _ _ (h hw)))
      (squ_subset_complementCurve G m)
  have hpc := (rectangle_convex (m.1, m.2 - 1)
    (m.1 + 1, m.2 + 1)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (h hzE)).ge

/-- If a vertical edge is in a component, then a surrounding rectangle
    is in the component.
    HOL Light: `comp_v_rect` (line 10376). -/
theorem comp_vEdge_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : vEdge m ⊆
      connectedComponentIn (complementCurve G.edges) x) :
    rectangle (m.1 - 1, m.2) (m.1 + 1, m.2 + 1) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzE⟩ := vEdge_nonempty m
  have h1 : z ∈ rectangle (m.1 - 1, m.2)
      (m.1 + 1, m.2 + 1) := by
    rw [rectangle_v_decomp m]
    exact Or.inl (Or.inr hzE)
  have h2 : rectangle (m.1 - 1, m.2) (m.1 + 1, m.2 + 1)
      ⊆ complementCurve G.edges := by
    rw [rectangle_v_decomp m]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G (left m))
        (fun w hw =>
          connectedComponentIn_subset _ _ (h hw)))
      (squ_subset_complementCurve G m)
  have hpc := (rectangle_convex (m.1 - 1, m.2)
    (m.1 + 1, m.2 + 1)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (h hzE)).ge

set_option maxHeartbeats 200000 in
-- Elevated heartbeats: convexity requires `nlinarith` to close four coordinate inequalities
-- involving products of `a`, `1 - a`, and differences of `PiLp` components.
/-- `longV m` is convex.
    HOL Light: `long_v_convex` (line 10421). -/
theorem longV_convex (m : ℤ × ℤ) : Convex ℝ (longV m) := by
  intro x hx y hy a b ha hb hab
  simp only [longV, mem_setOf_eq] at hx hy ⊢
  simp only [smul_eq_mul, PiLp.add_apply,
    PiLp.smul_apply]
  have hb1 : b = 1 - a := by linarith
  subst hb1
  refine ⟨?_, ?_, ?_⟩
  · rw [hx.1, hy.1]; ring
  · nlinarith [
      mul_nonneg ha (le_of_lt (show (0 : ℝ) <
        x.ofLp 1 - (↑m.2 - 1) by linarith [hx.2.1])),
      mul_nonneg (show (0:ℝ) ≤ 1 - a by linarith)
        (le_of_lt (show (0:ℝ) <
          y.ofLp 1 - (↑m.2 - 1)
          by linarith [hy.2.1])),
      show a * (x.ofLp 1 - (↑m.2 - 1)) +
        (1 - a) * (y.ofLp 1 - (↑m.2 - 1)) =
        a * x.ofLp 1 + (1 - a) * y.ofLp 1 -
          (↑m.2 - 1) from by ring]
  · nlinarith [
      mul_nonneg ha (le_of_lt (show (0 : ℝ) <
        (↑m.2 + 1) - x.ofLp 1
        by linarith [hx.2.2])),
      mul_nonneg (show (0:ℝ) ≤ 1 - a by linarith)
        (le_of_lt (show (0:ℝ) <
          (↑m.2 + 1) - y.ofLp 1
          by linarith [hy.2.2])),
      show a * ((↑m.2 + 1) - x.ofLp 1) +
        (1 - a) * ((↑m.2 + 1) - y.ofLp 1) =
        (↑m.2 + 1) - (a * x.ofLp 1 +
          (1 - a) * y.ofLp 1) from by ring]

/-- If pointI m is in a component, then longV m is in the component.
    HOL Light: `comp_pointI_long` (line 10442). -/
theorem comp_pointI_longV (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : pointI m ∈
      connectedComponentIn (complementCurve G.edges) x) :
    longV m ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  have hcomp := connectedComponentIn_subset _ _ h
  have h1 : pointI m ∈ longV m := by
    simp only [longV, mem_setOf_eq,
      pointI_coord_fst, pointI_coord_snd]
    exact ⟨by norm_cast, by linarith,
      by linarith⟩
  have h2 : longV m ⊆ complementCurve G.edges := by
    rw [longV_union]
    refine Set.union_subset
      (Set.union_subset ?_ ?_) ?_
    · have : vEdge (down m) ∉ G.edges := by
        intro hvG; exact hcomp
          (edge_in_G_pointI_in_curveCells G hvG
            ((pointI_mem_closure_vEdge m (down m)).mpr
              ⟨by simp [down],
               Or.inr (by simp [down])⟩))
      exact cell_subset_complementCurve' G
        ⟨.vEdge (down m), rfl⟩
        (mt (curveCells_vEdge G (down m)).mp this)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz; subst hz
      exact hcomp
    · have : vEdge m ∉ G.edges := by
        intro hvG; exact hcomp
          (edge_in_G_pointI_in_curveCells G hvG
            ((pointI_mem_closure_vEdge m m).mpr
              ⟨rfl, Or.inl rfl⟩))
      exact cell_subset_complementCurve' G
        ⟨.vEdge m, rfl⟩
        (mt (curveCells_vEdge G m).mp this)
  exact ((longV_convex m).isPreconnected.subset_connectedComponentIn
    h1 h2).trans (connectedComponentIn_eq h).ge

/-- If h_edge m is in the component, then squ m is in the component.
    HOL Light: `comp_h_squ` (line 10498). -/
theorem comp_hEdge_squ (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : hEdge m ⊆
      connectedComponentIn (complementCurve G.edges) x) :
    squ m ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  have hrect := comp_hEdge_rect G m x h
  rw [rectangle_h_decomp m] at hrect
  exact Set.subset_union_right.trans hrect

/-- If v_edge m is in the component, then squ m is in the component.
    HOL Light: `comp_v_squ` (line 10517). -/
theorem comp_vEdge_squ (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : vEdge m ⊆
      connectedComponentIn (complementCurve G.edges) x) :
    squ m ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  have hrect := comp_vEdge_rect G m x h
  rw [rectangle_v_decomp m] at hrect
  exact Set.subset_union_right.trans hrect

/-- If pointI m is in the component, then squ m is in the component.
    HOL Light: `comp_p_squ` (line 10536). -/
theorem comp_pointI_squ (G : Segment) (m : ℤ × ℤ) (x : E2)
    (h : pointI m ∈
      connectedComponentIn (complementCurve G.edges) x) :
    squ m ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  have hlV := comp_pointI_longV G m x h
  rw [longV_union] at hlV
  exact comp_vEdge_squ G m x
    (Set.subset_union_right.trans hlV)

/-- A nonempty component of ctop G contains some square.
    HOL Light: `comp_squ` (line 10553). -/
theorem comp_contains_squ (G : Segment) (x : E2)
    (hne : (connectedComponentIn
      (complementCurve G.edges) x).Nonempty) :
    ∃ m, squ m ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  -- Use unions_cellOf_component: component = ⋃₀ cellOf'(component)
  rw [← unions_cellOf_component G x] at hne
  obtain ⟨z, hz⟩ := hne
  rw [Set.mem_sUnion] at hz
  obtain ⟨C, ⟨⟨ct, rfl⟩, hCK⟩, hzC⟩ := hz
  match ct with
  | .point m => exact ⟨m, comp_pointI_squ G m x
      (hCK (Set.mem_singleton_iff.mpr rfl))⟩
  | .hEdge m => exact ⟨m, comp_hEdge_squ G m x hCK⟩
  | .vEdge m => exact ⟨m, comp_vEdge_squ G m x hCK⟩
  | .squ m => exact ⟨m, hCK⟩

/-! ## Rectangle extension lemmas (used for flood fill) -/

/-- If squ m is in the component and v_edge m is not in G,
    then the left rectangle is in the component.
    HOL Light: `comp_squ_left_rect_v` (line 10584). -/
theorem comp_squ_left_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hv : vEdge m ∉ G.edges) :
    rectangle (m.1 - 1, m.2) (m.1 + 1, m.2 + 1) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzS⟩ := squ_nonempty m
  have h1 : z ∈ rectangle (m.1 - 1, m.2)
      (m.1 + 1, m.2 + 1) := by
    rw [rectangle_v_decomp m]; exact Or.inr hzS
  have h2 : rectangle (m.1 - 1, m.2) (m.1 + 1, m.2 + 1)
      ⊆ complementCurve G.edges := by
    rw [rectangle_v_decomp m]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G (left m))
        (cell_subset_complementCurve' G
          ⟨.vEdge m, rfl⟩
          (mt (curveCells_vEdge G m).mp hv)))
      (squ_subset_complementCurve G m)
  have hpc := (rectangle_convex (m.1 - 1, m.2)
    (m.1 + 1, m.2 + 1)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (hsqu hzS)).ge

/-- HOL Light: `comp_squ_right_rect` (line 10712). -/
theorem comp_squ_right_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hv : vEdge (right m) ∉ G.edges) :
    rectangle (m.1, m.2) (m.1 + 2, m.2 + 1) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzS⟩ := squ_nonempty m
  have hrect : rectangle (m.1, m.2) (m.1 + 2, m.2 + 1) =
      squ m ∪ vEdge (right m) ∪ squ (right m) := by
    have := rectangle_v_decomp (right m)
    rw [left_right] at this
    convert this using 2 <;> ext <;> simp [right] ; omega
  have h1 : z ∈ rectangle (m.1, m.2) (m.1 + 2, m.2 + 1) := by
    rw [hrect]; exact Or.inl (Or.inl hzS)
  have h2 : rectangle (m.1, m.2) (m.1 + 2, m.2 + 1) ⊆
      complementCurve G.edges := by
    rw [hrect]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G m)
        (cell_subset_complementCurve' G
          ⟨.vEdge (right m), rfl⟩
          (mt (curveCells_vEdge G (right m)).mp hv)))
      (squ_subset_complementCurve G (right m))
  have hpc := (rectangle_convex (m.1, m.2)
    (m.1 + 2, m.2 + 1)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (hsqu hzS)).ge

/-- HOL Light: `comp_squ_down_rect` (line 10784). -/
theorem comp_squ_down_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hh : hEdge m ∉ G.edges) :
    rectangle (m.1, m.2 - 1) (m.1 + 1, m.2 + 1) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzS⟩ := squ_nonempty m
  have h1 : z ∈ rectangle (m.1, m.2 - 1)
      (m.1 + 1, m.2 + 1) := by
    rw [rectangle_h_decomp m]; exact Or.inr hzS
  have h2 : rectangle (m.1, m.2 - 1) (m.1 + 1, m.2 + 1)
      ⊆ complementCurve G.edges := by
    rw [rectangle_h_decomp m]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G (down m))
        (cell_subset_complementCurve' G
          ⟨.hEdge m, rfl⟩
          (mt (curveCells_hEdge G m).mp hh)))
      (squ_subset_complementCurve G m)
  have hpc := (rectangle_convex (m.1, m.2 - 1)
    (m.1 + 1, m.2 + 1)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (hsqu hzS)).ge

/-- HOL Light: `comp_squ_up_rect` (line 10862). -/
theorem comp_squ_up_rect (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hh : hEdge (up m) ∉ G.edges) :
    rectangle (m.1, m.2) (m.1 + 1, m.2 + 2) ⊆
      connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨z, hzS⟩ := squ_nonempty m
  have hrect : rectangle (m.1, m.2) (m.1 + 1, m.2 + 2) =
      squ m ∪ hEdge (up m) ∪ squ (up m) := by
    have := rectangle_h_decomp (up m)
    rw [down_up] at this
    convert this using 2 <;> ext <;> simp [up] ; omega
  have h1 : z ∈ rectangle (m.1, m.2) (m.1 + 1, m.2 + 2) := by
    rw [hrect]; exact Or.inl (Or.inl hzS)
  have h2 : rectangle (m.1, m.2) (m.1 + 1, m.2 + 2) ⊆
      complementCurve G.edges := by
    rw [hrect]
    exact Set.union_subset
      (Set.union_subset
        (squ_subset_complementCurve G m)
        (cell_subset_complementCurve' G
          ⟨.hEdge (up m), rfl⟩
          (mt (curveCells_hEdge G (up m)).mp hh)))
      (squ_subset_complementCurve G (up m))
  have hpc := (rectangle_convex (m.1, m.2)
    (m.1 + 1, m.2 + 2)).isPreconnected
  exact (hpc.subset_connectedComponentIn h1 h2).trans
    (connectedComponentIn_eq (hsqu hzS)).ge

/-- If squ m is in the component and no edge of G borders it,
    then all 4 neighboring squares are in the component.
    HOL Light: `comp_squ_right_left` (line 10883). -/
theorem comp_squ_neighbors (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hno : ∀ e ∈ G.edges, ¬(e ⊆ closure (squ m))) :
    squ (left m) ⊆ connectedComponentIn (complementCurve G.edges) x ∧
    squ (right m) ⊆ connectedComponentIn (complementCurve G.edges) x ∧
    squ (down m) ⊆ connectedComponentIn (complementCurve G.edges) x ∧
    squ (up m) ⊆ connectedComponentIn (complementCurve G.edges) x := by
  have hvl : vEdge m ∉ G.edges :=
    fun h => hno _ h (squ_closure_v m)
  have hvr : vEdge (right m) ∉ G.edges :=
    fun h => hno _ h (squ_closure_right_v m)
  have hhd : hEdge m ∉ G.edges :=
    fun h => hno _ h (squ_closure_h m)
  have hhu : hEdge (up m) ∉ G.edges :=
    fun h => hno _ h (squ_closure_up_h m)
  have hl := comp_squ_left_rect G m x hsqu hvl
  have hr := comp_squ_right_rect G m x hsqu hvr
  have hd := comp_squ_down_rect G m x hsqu hhd
  have hu := comp_squ_up_rect G m x hsqu hhu
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- left: squ(left m) ⊆ rectangle_v m ⊆ component
    rw [rectangle_v_decomp m] at hl
    exact (Set.subset_union_left.trans
      Set.subset_union_left).trans hl
  · -- right: squ(right m) ⊆ rect (m.1,m.2)(m.1+2,m.2+1)
    have hrect : rectangle (m.1, m.2) (m.1 + 2, m.2 + 1) =
        squ m ∪ vEdge (right m) ∪ squ (right m) := by
      have := rectangle_v_decomp (right m)
      rw [left_right] at this
      convert this using 2 <;> ext <;> simp [right] ; omega
    rw [hrect] at hr
    exact Set.subset_union_right.trans hr
  · -- down: squ(down m) ⊆ rectangle_h m ⊆ component
    rw [rectangle_h_decomp m] at hd
    exact (Set.subset_union_left.trans
      Set.subset_union_left).trans hd
  · -- up: squ(up m) ⊆ rect (m.1,m.2)(m.1+1,m.2+2)
    have hrect : rectangle (m.1, m.2) (m.1 + 1, m.2 + 2) =
        squ m ∪ hEdge (up m) ∪ squ (up m) := by
      have := rectangle_h_decomp (up m)
      rw [down_up] at this
      convert this using 2 <;> ext <;> simp [up] ; omega
    rw [hrect] at hu
    exact Set.subset_union_right.trans hu

/-- Grid induction: reducing L1 distance by moving to a neighbor.
    HOL Light: `squ_induct` (line 10930). -/
theorem squ_induct (G : Segment) (m n : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hno : ∀ k, squ k ⊆ connectedComponentIn (complementCurve G.edges) x →
           ∀ e ∈ G.edges, ¬(e ⊆ closure (squ k))) :
    squ n ⊆ connectedComponentIn (complementCurve G.edges) x := by
  suffices ∀ d n, d = (n.1 - m.1).natAbs +
      (n.2 - m.2).natAbs →
      squ n ⊆ connectedComponentIn
        (complementCurve G.edges) x by
    exact this _ n rfl
  intro d; induction d with
  | zero =>
    intro n hn
    have : n = m := Prod.ext (by omega) (by omega)
    subst this; exact hsqu
  | succ d ih =>
    intro n hn
    -- Find neighbor p of n closer to m
    by_cases hfst : n.1 = m.1
    · -- x-coords equal → move vertically
      by_cases hlt : n.2 < m.2
      · -- n below m: go up. p = up n, then n = down p
        have hp : d = ((up n).1 - m.1).natAbs +
            ((up n).2 - m.2).natAbs := by
          simp only [up]; omega
        have := comp_squ_neighbors G (up n) x
          (ih (up n) hp) (hno (up n) (ih (up n) hp))
        rw [down_up] at this; exact this.2.2.1
      · -- n above m: go down. p = down n
        have hne : n.2 ≠ m.2 := by omega
        have hgt : n.2 > m.2 := by omega
        have hp : d = ((down n).1 - m.1).natAbs +
            ((down n).2 - m.2).natAbs := by
          simp only [down]; omega
        have := comp_squ_neighbors G (down n) x
          (ih (down n) hp) (hno (down n) (ih (down n) hp))
        rw [up_down] at this; exact this.2.2.2
    · -- x-coords differ → move horizontally
      by_cases hlt : n.1 < m.1
      · -- n left of m: go right. p = right n
        have hp : d = ((right n).1 - m.1).natAbs +
            ((right n).2 - m.2).natAbs := by
          simp only [right]; omega
        have := comp_squ_neighbors G (right n) x
          (ih (right n) hp)
          (hno (right n) (ih (right n) hp))
        rw [left_right] at this; exact this.1
      · -- n right of m: go left. p = left n
        have hgt : n.1 > m.1 := by omega
        have hp : d = ((left n).1 - m.1).natAbs +
            ((left n).2 - m.2).natAbs := by
          simp only [left]; omega
        have := comp_squ_neighbors G (left n) x
          (ih (left n) hp)
          (hno (left n) (ih (left n) hp))
        rw [right_left] at this; exact this.2.1

/-- If no edge of G touches any square in the component,
    then every square is in the component (flood fill).
    HOL Light: `comp_squ_fill` (line 11019). -/
theorem comp_squ_fill (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hno : ∀ k, squ k ⊆ connectedComponentIn (complementCurve G.edges) x →
           ∀ e ∈ G.edges, ¬(e ⊆ closure (squ k))) :
    ∀ n, squ n ⊆ connectedComponentIn (complementCurve G.edges) x := by
  intro n; exact squ_induct G m n x hsqu hno

/-- Every square in a nonempty component has a nearby edge of G.
    HOL Light: `comp_squ_adj` (line 11062). -/
theorem comp_squ_adj (G : Segment) (m : ℤ × ℤ) (x : E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x) :
    ∃ p e, e ∈ G.edges ∧ e ⊆ closure (squ p) ∧
      squ p ⊆ connectedComponentIn (complementCurve G.edges) x := by
  by_contra h; push Not at h
  have hfill : ∀ n, squ n ⊆ connectedComponentIn
      (complementCurve G.edges) x :=
    comp_squ_fill G m x hsqu
      (fun k hk e he hsub => h k e he hsub hk)
  obtain ⟨e, heG⟩ := G.nonempty
  rcases G.all_edges e heG with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact h q _ heG (squ_closure_h q) (hfill q)
  · exact h q _ heG (squ_closure_v q) (hfill q)

/-! ## Along-segment analysis -/

/-- `alongSeg G e x` means G contains edge e, and there is a square p
    with e in the closure of squ p, and squ p in the component of x.
    HOL Light: `along_seg` (line 11100). -/
def alongSeg (G : Finset (Set E2)) (e : Set E2) (x : E2) : Prop :=
  e ∈ G ∧
  ∃ p, e ⊆ closure (squ p) ∧
    squ p ⊆ connectedComponentIn (complementCurve G) x

/-- At a midpoint of a segment, the third edge through the point must
    equal one of the two.
    HOL Light: `midpoint_exclusion` (line 11119). -/
theorem midpoint_exclusion (G : Segment) (m : ℤ × ℤ)
    (e e' e'' : Set E2)
    (hG : e ∈ G.edges) (hG' : e' ∈ G.edges) (hG'' : e'' ∈ G.edges)
    (hne : e ≠ e')
    (he : pointI m ∈ closure e) (he' : pointI m ∈ closure e')
    (he'' : pointI m ∈ closure e'') :
    e'' = e ∨ e'' = e' := by
  open Classical in
  have he_i : e ∈ incidentEdges G.edges m :=
    (@Finset.mem_filter _ _
      (Classical.decPred _)).mpr ⟨hG, he⟩
  open Classical in
  have he'_i : e' ∈ incidentEdges G.edges m :=
    (@Finset.mem_filter _ _
      (Classical.decPred _)).mpr ⟨hG', he'⟩
  open Classical in
  have he''_i : e'' ∈ incidentEdges G.edges m :=
    (@Finset.mem_filter _ _
      (Classical.decPred _)).mpr ⟨hG'', he''⟩
  have hbd := G.degree_bound m
  unfold numClosure at hbd
  by_contra h; push Not at h; obtain ⟨hne1, hne2⟩ := h
  have hsub : {e, e', e''} ⊆ incidentEdges G.edges m :=
    Finset.insert_subset he_i
      (Finset.insert_subset he'_i
        (Finset.singleton_subset_iff.mpr he''_i))
  have hcard3 : ({e, e', e''} : Finset _).card = 3 := by
    rw [Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · exact mt Finset.mem_singleton.mp hne2.symm
    · rw [Finset.mem_insert, Finset.mem_singleton]
      push Not; exact ⟨hne, hne1.symm⟩
  have hle : (incidentEdges G.edges m).card ≤ 2 := by
    have := G.degree_bound m
    unfold numClosure at this
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at this
    omega
  have h3le : 3 ≤ (incidentEdges G.edges m).card :=
    hcard3 ▸ Finset.card_le_card hsub
  omega

/-- General along-segment witness.
    HOL Light: `along_lemma6` (line 11261). -/
theorem along_lemma6 (G : Segment) (m : ℤ × ℤ) (x : E2)
    (e : Set E2)
    (hsqu : squ m ⊆ connectedComponentIn (complementCurve G.edges) x)
    (hv : vEdge m ∈ G.edges) (he : e ∈ G.edges)
    (hcl : pointI m ∈ closure e) :
    ∃ p, e ⊆ closure (squ p) ∧
      squ p ⊆ connectedComponentIn (complementCurve G.edges) x := by
  -- Helper: vEdges and hEdges are always distinct sets
  have hv_ne_h : ∀ a b : ℤ × ℤ, vEdge a ≠ hEdge b := by
    intro a b hab
    obtain ⟨z, hz⟩ := vEdge_nonempty a
    have hzh : z ∈ hEdge b := hab ▸ hz
    simp only [vEdge, hEdge, Set.mem_setOf_eq] at hz hzh
    have hlt : b.1 < a.1 := by
      exact_mod_cast (show (↑b.1 : ℝ) < ↑a.1 from
        by linarith [hz.1, hzh.1])
    have hge : (↑b.1 + 1 : ℝ) ≤ ↑a.1 := by
      have : b.1 + 1 ≤ a.1 := by omega
      exact_mod_cast this
    linarith [hz.1, hzh.2.1]
  rcases G.all_edges e he with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · -- e = hEdge m'
    rw [pointI_mem_closure_hEdge] at hcl
    rcases hcl with ⟨h2, h1 | h1⟩
    · -- m' = m
      have hm' : m' = m := Prod.ext (by omega) h2.symm
      rw [hm']; exact ⟨m, squ_closure_h m, hsqu⟩
    · -- m' = left m (along_lemma5 pattern)
      have hm' : m' = left m :=
        Prod.ext (by simp only [left]; omega)
          (by simp only [left]; exact h2.symm)
      rw [hm'] at he ⊢
      -- along_lemma3: hEdge m ∉ G, vEdge(down m) ∉ G
      have hhm : hEdge m ∉ G.edges := by
        intro hh
        rcases midpoint_exclusion G m (vEdge m)
          (hEdge (left m)) (hEdge m) hv he hh
          (hv_ne_h m (left m))
          ((pointI_mem_closure_vEdge m m).mpr
            ⟨rfl, Or.inl rfl⟩)
          ((pointI_mem_closure_hEdge m (left m)).mpr
            ⟨rfl, Or.inr (by simp only [left, sub_add_cancel])⟩)
          ((pointI_mem_closure_hEdge m m).mpr
            ⟨rfl, Or.inl rfl⟩) with h | h
        · exact absurd h.symm (hv_ne_h m m)
        · exact absurd
            (congr_arg Prod.fst ((hEdge_inj _ _).mp h))
            (by simp only [left]; omega)
      have hvdm : vEdge (down m) ∉ G.edges := by
        intro hvd
        rcases midpoint_exclusion G m (vEdge m)
          (hEdge (left m)) (vEdge (down m)) hv he hvd
          (hv_ne_h m (left m))
          ((pointI_mem_closure_vEdge m m).mpr
            ⟨rfl, Or.inl rfl⟩)
          ((pointI_mem_closure_hEdge m (left m)).mpr
            ⟨rfl, Or.inr (by simp only [left, sub_add_cancel])⟩)
          ((pointI_mem_closure_vEdge m (down m)).mpr
            ⟨by simp [down],
              Or.inr (by simp [down])⟩) with h | h
        · exact absurd
            (congr_arg Prod.snd ((vEdge_inj _ _).mp h))
            (by simp [down])
        · exact absurd h (hv_ne_h (down m) (left m))
      -- Path: squ m → squ(down m) → squ(left(down m))
      have hd := comp_squ_down_rect G m x hsqu hhm
      rw [rectangle_h_decomp m] at hd
      have hdm : squ (down m) ⊆
          connectedComponentIn
            (complementCurve G.edges) x :=
        (Set.subset_union_left.trans
          Set.subset_union_left).trans hd
      have hl := comp_squ_left_rect G (down m) x hdm hvdm
      rw [rectangle_v_decomp (down m)] at hl
      have hldm : squ (left (down m)) ⊆
          connectedComponentIn
            (complementCurve G.edges) x :=
        (Set.subset_union_left.trans
          Set.subset_union_left).trans hl
      have hul : up (left (down m)) = left m := by
        ext <;> simp [up, left, down]
      exact ⟨left (down m),
        hul ▸ squ_closure_up_h (left (down m)), hldm⟩
  · -- e = vEdge m'
    rw [pointI_mem_closure_vEdge] at hcl
    rcases hcl with ⟨h1, h2 | h2⟩
    · -- m' = m
      have hm' : m' = m := Prod.ext (by omega) (by omega)
      rw [hm']; exact ⟨m, squ_closure_v m, hsqu⟩
    · -- m' = down m (along_lemma4 pattern)
      have hm' : m' = down m :=
        Prod.ext (by simp [down]; omega)
          (by simp [down]; omega)
      rw [hm'] at he ⊢
      -- along_lemma2: hEdge m ∉ G
      have hne : vEdge m ≠ vEdge (down m) := by
        intro h
        exact absurd
          (congr_arg Prod.snd ((vEdge_inj _ _).mp h))
          (by simp [down]; omega)
      have hhm : hEdge m ∉ G.edges := by
        intro hh
        rcases midpoint_exclusion G m (vEdge m)
          (vEdge (down m)) (hEdge m) hv he hh hne
          ((pointI_mem_closure_vEdge m m).mpr
            ⟨rfl, Or.inl rfl⟩)
          ((pointI_mem_closure_vEdge m (down m)).mpr
            ⟨by simp [down],
              Or.inr (by simp [down])⟩)
          ((pointI_mem_closure_hEdge m m).mpr
            ⟨rfl, Or.inl rfl⟩) with h | h
        · exact absurd h.symm (hv_ne_h m m)
        · exact absurd h.symm (hv_ne_h (down m) m)
      -- comp_squ_down_rect: squ(down m) ⊆ component
      have hd := comp_squ_down_rect G m x hsqu hhm
      rw [rectangle_h_decomp m] at hd
      exact ⟨down m, squ_closure_v (down m),
        (Set.subset_union_left.trans
          Set.subset_union_left).trans hd⟩

/-! ## Reflections -/

/-- Reflection across the vertical line x = r (on ℝ²).
    HOL Light: `reflAf r` (line 11314). -/
def reflAf (r : ℤ) (z : E2) : E2 :=
  (WithLp.equiv 2 _).symm ![2 * (↑r : ℝ) - z 0, z 1]

/-- Reflection on the integer grid: (a, b) ↦ (2r - a, b).
    HOL Light: `reflAi r` (line 11317). -/
def reflAi (r : ℤ) (m : ℤ × ℤ) : ℤ × ℤ := (2 * r - m.1, m.2)

/-- Reflection across the horizontal line y = r (on ℝ²).
    HOL Light: `reflBf r` (line 11320). -/
def reflBf (r : ℤ) (z : E2) : E2 :=
  (WithLp.equiv 2 _).symm ![z 0, 2 * (↑r : ℝ) - z 1]

/-- HOL Light: `reflBi r` (line 11323). -/
def reflBi (r : ℤ) (m : ℤ × ℤ) : ℤ × ℤ := (m.1, 2 * r - m.2)

/-- Reflection swapping coordinates (on ℝ²).
    HOL Light: `reflCf` (line 11326). -/
def reflCf (z : E2) : E2 :=
  (WithLp.equiv 2 _).symm ![z 1, z 0]

/-- HOL Light: `reflCi` (line 11329). -/
def reflCi (m : ℤ × ℤ) : ℤ × ℤ := (m.2, m.1)

-- ── Involution properties ────────────────────────────────────────────

/-- HOL Light: `reflAf_inv` (line 11332). -/
theorem reflAf_inv (r : ℤ) (z : E2) :
    reflAf r (reflAf r z) = z := by
  simp only [reflAf]
  ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- HOL Light: `reflBf_inv` (line 11344). -/
theorem reflBf_inv (r : ℤ) (z : E2) :
    reflBf r (reflBf r z) = z := by
  simp only [reflBf]
  ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- HOL Light: `reflCf_inv` (line 11354). -/
theorem reflCf_inv (z : E2) : reflCf (reflCf z) = z := by
  simp only [reflCf]
  ext i; fin_cases i <;> simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,
                                    Matrix.cons_val_zero,Matrix.cons_val_one,
                                    Matrix.cons_val_fin_one,Fin.zero_eta,Fin.mk_one]

/-- HOL Light: `reflAi_inv` (line 11363). -/
theorem reflAi_inv (r : ℤ) (m : ℤ × ℤ) :
    reflAi r (reflAi r m) = m := by
  simp [reflAi]

/-- HOL Light: `reflBi_inv` (line 11372). -/
theorem reflBi_inv (r : ℤ) (m : ℤ × ℤ) :
    reflBi r (reflBi r m) = m := by
  simp [reflBi]

/-- HOL Light: `reflCi_inv` (line 11381). -/
theorem reflCi_inv (m : ℤ × ℤ) :
    reflCi (reflCi m) = m := by
  simp [reflCi]

-- ── Continuity and homeomorphisms ────────────────────────────────────

/-- HOL Light: `reflA_cont` (line 11514). -/
theorem reflAf_continuous (r : ℤ) : Continuous (reflAf r) := by
  unfold reflAf
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi; intro i; fin_cases i
  · exact continuous_const.sub (PiLp.continuous_apply 2 _ 0)
  · exact PiLp.continuous_apply 2 _ 1

/-- HOL Light: `reflB_cont` (line 11546). -/
theorem reflBf_continuous (r : ℤ) : Continuous (reflBf r) := by
  unfold reflBf
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi; intro i; fin_cases i
  · exact PiLp.continuous_apply 2 _ 0
  · exact continuous_const.sub (PiLp.continuous_apply 2 _ 1)

/-- HOL Light: `reflC_cont` (line 11578). -/
theorem reflCf_continuous : Continuous reflCf := by
  unfold reflCf
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi; intro i; fin_cases i
  · exact PiLp.continuous_apply 2 _ 1
  · exact PiLp.continuous_apply 2 _ 0

/-- reflAf r is a homeomorphism (involution ⟹ bijective + continuous).
    HOL Light: `reflA_homeo` (line 11605). -/
def reflAf_homeo (r : ℤ) : E2 ≃ₜ E2 where
  toFun := reflAf r
  invFun := reflAf r
  left_inv := reflAf_inv r
  right_inv := reflAf_inv r
  continuous_toFun := reflAf_continuous r
  continuous_invFun := reflAf_continuous r

/-- reflBf r is a homeomorphism.
    HOL Light: `reflB_homeo` (line 11622). -/
def reflBf_homeo (r : ℤ) : E2 ≃ₜ E2 where
  toFun := reflBf r
  invFun := reflBf r
  left_inv := reflBf_inv r
  right_inv := reflBf_inv r
  continuous_toFun := reflBf_continuous r
  continuous_invFun := reflBf_continuous r

/-- reflCf is a homeomorphism.
    HOL Light: `reflC_homeo` (line 11639). -/
def reflCf_homeo : E2 ≃ₜ E2 where
  toFun := reflCf
  invFun := reflCf
  left_inv := reflCf_inv
  right_inv := reflCf_inv
  continuous_toFun := reflCf_continuous
  continuous_invFun := reflCf_continuous

-- ── Reflections on edges ─────────────────────────────────────────────

/-- IMAGE reflAf on h_edge gives an h_edge.
    HOL Light: `reflA_h_edge` (line 11658). -/
theorem reflAf_hEdge (r : ℤ) (m : ℤ × ℤ) :
    reflAf r '' (hEdge m) = hEdge (left (reflAi r m)) := by
  ext z; simp only [reflAf, hEdge, left, reflAi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,sub_add_cancel,Int.cast_sub,Int.cast_mul,
               Int.cast_ofNat,Int.cast_one,gt_iff_lt,sub_lt_sub_iff_left]
    exact ⟨by linarith, by linarith, hw3⟩
  · intro ⟨h1, h2, h3⟩
    push_cast at h1 h2 h3
    refine ⟨(WithLp.equiv 2 _).symm ![2 * ↑r - z 0, z 1], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt];
      exact ⟨by linarith, by linarith, h3⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- IMAGE reflAf on v_edge gives a v_edge.
    HOL Light: `reflA_v_edge` (line 11692). -/
theorem reflAf_vEdge (r : ℤ) (m : ℤ × ℤ) :
    reflAf r '' (vEdge m) = vEdge (reflAi r m) := by
  ext z; simp only [reflAf, vEdge, reflAi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
               gt_iff_lt,sub_right_inj]
    exact ⟨by linarith, hw2, hw3⟩
  · intro ⟨h1, h2, h3⟩
    push_cast at h1 h2 h3
    refine ⟨(WithLp.equiv 2 _).symm ![2 * ↑r - z 0, z 1], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt];
      exact ⟨by linarith, h2, h3⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- reflAf sends edges to edges.
    HOL Light: `reflA_edge` (line 11709). -/
theorem reflAf_isEdge (r : ℤ) (e : Set E2) (he : isEdge e) :
    isEdge (reflAf r '' e) := by
  rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [reflAf_hEdge]; left; exact ⟨_, rfl⟩
  · rw [reflAf_vEdge]; right; exact ⟨_, rfl⟩

/-- IMAGE reflBf on v_edge gives a v_edge.
    HOL Light: `reflB_v_edge` (line 11725). -/
theorem reflBf_vEdge (r : ℤ) (m : ℤ × ℤ) :
    reflBf r '' (vEdge m) =
      vEdge (down (reflBi r m)) := by
  ext z; simp only [reflBf, vEdge, down, reflBi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,sub_add_cancel,Int.cast_sub,Int.cast_mul,
               Int.cast_ofNat,Int.cast_one,gt_iff_lt,sub_lt_sub_iff_left]
    exact ⟨hw1, by linarith, by linarith⟩
  · intro ⟨h1, h2, h3⟩
    push_cast at h1 h2 h3
    refine ⟨(WithLp.equiv 2 _).symm ![z 0, 2 * ↑r - z 1], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt];
      exact ⟨h1, by linarith, by linarith⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- IMAGE reflBf on h_edge gives an h_edge.
    HOL Light: `reflB_h_edge` (line 11759). -/
theorem reflBf_hEdge (r : ℤ) (m : ℤ × ℤ) :
    reflBf r '' (hEdge m) = hEdge (reflBi r m) := by
  ext z; simp only [reflBf, hEdge, reflBi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
               gt_iff_lt,sub_right_inj]
    exact ⟨hw1, hw2, by linarith⟩
  · intro ⟨h1, h2, h3⟩
    push_cast at h1 h2 h3
    refine ⟨(WithLp.equiv 2 _).symm ![z 0, 2 * ↑r - z 1], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt];
      exact ⟨h1, h2, by linarith⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv, Fin.isValue, Equiv.coe_fn_symm_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_sub_cancel, Fin.zero_eta, Fin.mk_one]

/-- reflBf sends edges to edges.
    HOL Light: `reflB_edge` (line 11776). -/
theorem reflBf_isEdge (r : ℤ) (e : Set E2) (he : isEdge e) :
    isEdge (reflBf r '' e) := by
  rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [reflBf_hEdge]; left; exact ⟨_, rfl⟩
  · rw [reflBf_vEdge]; right; exact ⟨_, rfl⟩

/-- IMAGE reflCf on v_edge gives an h_edge (swaps edge types).
    HOL Light: `reflC_vh_edge` (line 11792). -/
theorem reflCf_vEdge (m : ℤ × ℤ) :
    reflCf '' (vEdge m) = hEdge (reflCi m) := by
  ext z; simp only [reflCf, vEdge, hEdge, reflCi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt]
    exact ⟨hw2, hw3, hw1⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨(WithLp.equiv 2 _).symm ![z 1, z 0], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt]; exact ⟨h3, h1, h2⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,
                                        Matrix.cons_val_zero,Matrix.cons_val_one,
                                        Matrix.cons_val_fin_one,Fin.zero_eta,Fin.mk_one]

/-- IMAGE reflCf on h_edge gives a v_edge.
    HOL Light: `reflC_hv_edge` (line 11809). -/
theorem reflCf_hEdge (m : ℤ × ℤ) :
    reflCf '' (hEdge m) = vEdge (reflCi m) := by
  ext z; simp only [reflCf, hEdge, vEdge, reflCi, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
               Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt]
    exact ⟨hw3, hw1, hw2⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨(WithLp.equiv 2 _).symm ![z 1, z 0], ?_, ?_⟩
    · simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,Matrix.cons_val_zero,
                 Matrix.cons_val_one,Matrix.cons_val_fin_one,gt_iff_lt]; exact ⟨h2, h3, h1⟩
    · ext i; fin_cases i <;> simp only [WithLp.equiv,Fin.isValue,Equiv.coe_fn_symm_mk,
                                        Matrix.cons_val_zero,Matrix.cons_val_one,
                                        Matrix.cons_val_fin_one,Fin.zero_eta,Fin.mk_one]

/-- reflCf sends edges to edges.
    HOL Light: `reflC_edge` (line 11826). -/
theorem reflCf_isEdge (e : Set E2) (he : isEdge e) :
    isEdge (reflCf '' e) := by
  rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [reflCf_hEdge]; right; exact ⟨_, rfl⟩
  · rw [reflCf_vEdge]; left; exact ⟨_, rfl⟩

/-! ## IMAGE2 (lifting a map to act on sets of sets) -/

/-- Lifting a point-map to a set-of-sets map.
    HOL Light: `IMAGE2` (line 11655). -/
def IMAGE2 (f : E2 → E2) (U : Set (Set E2)) : Set (Set E2) :=
  (f '' ·) '' U

/-! ## General homeomorphism lemmas -/

/-- A homeomorphism induces a bijection on sets.
    HOL Light: `homeo_bij` (line 11842). -/
theorem Homeomorph.image_bijective (f : E2 ≃ₜ E2) :
    Function.Bijective (f '' · : Set E2 → Set E2) := by
  constructor
  · intro A B h
    ext x
    simp only [] at h
    constructor <;> intro hx
    · have : f x ∈ f '' B := h ▸ Set.mem_image_of_mem f hx
      exact (f.injective.mem_set_image).mp this
    · have : f x ∈ f '' A := h ▸ Set.mem_image_of_mem f hx
      exact (f.injective.mem_set_image).mp this
  · exact fun S => ⟨f.symm '' S, by ext x; simp⟩

/-- A homeomorphism preserves closedness.
    HOL Light: `homeo_closed` (line 11972). -/
theorem Homeomorph.isClosed_image_iff (f : E2 ≃ₜ E2)
    (A : Set E2) :
    IsClosed (f '' A) ↔ IsClosed A := by
  constructor
  · intro h
    have h2 := f.symm.isClosedMap _ h
    simpa only [Set.image_image, f.symm_apply_apply, Set.image_id'] using h2
  · exact f.isClosedMap _

/-! ## Euclidean distance formula -/

/-- Explicit distance formula for lattice points.
    HOL Light: `d_euclid_point` (line 11490). -/
theorem dist_pointI_formula (m n : ℤ × ℤ) :
    dist (pointI m) (pointI n) =
      Real.sqrt ((↑m.1 - ↑n.1) ^ 2 +
        (↑m.2 - ↑n.2) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp only [Fin.sum_univ_two, pointI, point,
    WithLp.equiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.dist_eq, Fin.isValue]
  congr 1 <;> rw [sq_abs]

end
