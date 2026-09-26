/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionA_CellGeometry
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Section B: Cell Complex Topology
## HOL Light: Section B (Lines 2684–3553)

Basic topology of cell complexes and set operations on cells.
Establishes that edges and squares are open, computes closures of all
cell types, and proves that cells are locally connected via adjacency.

### Key HOL Light results
- `closure_h_edge`, `closure_v_edge`, `closure_squ`
- Open/closed set properties for cell types
- Boundary characterizations
-/

open Set Topology Metric

noncomputable section

/-! ## Continuity of coordinate projections (key tool) -/

/-- Coordinate projection from E2 is continuous. -/
theorem continuous_coord (i : Fin 2) :
    Continuous (fun z : E2 => z i) :=
  PiLp.continuous_apply 2 _ i

private theorem continuous_coord0 : Continuous (fun z : E2 => z 0) :=
  continuous_coord 0

private theorem continuous_coord1 : Continuous (fun z : E2 => z 1) :=
  continuous_coord 1

/-! ## Openness of cells -/

/-- Open unit squares are open in the Euclidean topology.
    HOL Light: derived from half-plane intersections (lines 2684–2720). -/
theorem squ_isOpen (m : ℤ × ℤ) : IsOpen (squ m) :=
  (isOpen_lt continuous_const continuous_coord0).and <|
    (isOpen_lt continuous_coord0 continuous_const).and <|
      (isOpen_lt continuous_const continuous_coord1).and
        (isOpen_lt continuous_coord1 continuous_const)

-- Note: hEdge and vEdge are NOT open in the ambient ℝ² topology; they are
-- 1-dimensional. The original skeleton statements were geometrically incorrect.
-- The correct statements below assert openness in the appropriate subspace
-- topology. We remove the false ambient-topology statements.

/-- Horizontal edges are open in the subspace topology of their row. -/
theorem hEdge_isOpen_in_row (m : ℤ × ℤ) :
    IsOpen ((Subtype.val ⁻¹' (hEdge m)) : Set (row m.2)) := by
  -- The ambient open set {z | z 0 > m.1 ∧ z 0 < m.1 + 1} restricts to the
  -- same preimage in row m.2, since the y-constraint is automatic.
  have hopen : IsOpen {z : E2 | z 0 > (↑m.1 : ℝ) ∧ z 0 < ↑m.1 + 1} :=
    (isOpen_lt continuous_const continuous_coord0).inter
      (isOpen_lt continuous_coord0 continuous_const)
  have heq : (Subtype.val ⁻¹' (hEdge m) : Set (row m.2)) =
      Subtype.val ⁻¹' {z : E2 | z 0 > (↑m.1 : ℝ) ∧ z 0 < ↑m.1 + 1} := by
    ext ⟨z, hz⟩
    simp only [hEdge, mem_setOf_eq, row] at hz ⊢
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hz⟩⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- Vertical edges are open in the subspace topology of their column. -/
theorem vEdge_isOpen_in_col (m : ℤ × ℤ) :
    IsOpen ((Subtype.val ⁻¹' (vEdge m)) : Set (col m.1)) := by
  have hopen : IsOpen {z : E2 | z 1 > (↑m.2 : ℝ) ∧ z 1 < ↑m.2 + 1} :=
    (isOpen_lt continuous_const continuous_coord1).inter
      (isOpen_lt continuous_coord1 continuous_const)
  have heq : (Subtype.val ⁻¹' (vEdge m) : Set (col m.1)) =
      Subtype.val ⁻¹' {z : E2 | z 1 > (↑m.2 : ℝ) ∧ z 1 < ↑m.2 + 1} := by
    ext ⟨z, hz⟩
    simp only [vEdge, mem_setOf_eq, col] at hz ⊢
    exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hz, h1, h2⟩⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- Singleton lattice points are closed. -/
theorem pointI_isClosed (m : ℤ × ℤ) : IsClosed ({pointI m} : Set E2) :=
  isClosed_singleton

/-! ## Auxiliary: constructing E2 witnesses with controlled coordinates -/

/-- Build an E2 point from two real coordinates. -/
private def mkE2' (x y : ℝ) : E2 := point (x, y)

@[simp]
private theorem mkE2'_coord0 (x y : ℝ) : mkE2' x y 0 = x := point_coord_zero x y

@[simp]
private theorem mkE2'_coord1 (x y : ℝ) : mkE2' x y 1 = y := point_coord_one x y

/-- Distance between two E2 points with one coordinate equal. -/
private theorem dist_mkE2'_same_snd (a b c : ℝ) :
    dist (mkE2' a c) (mkE2' b c) = |a - b| := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq,
    show (mkE2' a c).ofLp = ![a, c] from rfl,
    show (mkE2' b c).ofLp = ![b, c] from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [sub_self, abs_zero, sq_abs, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs]

private theorem dist_mkE2'_same_fst (a b c : ℝ) :
    dist (mkE2' c a) (mkE2' c b) = |a - b| := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq,
    show (mkE2' c a).ofLp = ![c, a] from rfl,
    show (mkE2' c b).ofLp = ![c, b] from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [sub_self, abs_zero, sq_abs, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add]
  rw [Real.sqrt_sq_eq_abs]

/-- Distance in E2 is at most the Chebyshev distance. -/
private theorem dist_le_of_coord_le {z w : E2} {d : ℝ}
    (h0 : |z 0 - w 0| ≤ d) (h1 : |z 1 - w 1| ≤ d) (hd : 0 ≤ d) :
    dist z w ≤ d * Real.sqrt 2 := by
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i : Fin 2, dist (z.ofLp i) (w.ofLp i) ^ 2)
      ≤ Real.sqrt (d ^ 2 + d ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_two, Real.dist_eq]
        have h0' : |z 0 - w 0| ^ 2 ≤ d ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (z 0 - w 0)]) h0
        have h1' : |z 1 - w 1| ^ 2 ≤ d ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (z 1 - w 1)]) h1
        linarith
    _ = d * Real.sqrt 2 := by
        rw [← two_mul, mul_comm, Real.sqrt_mul (sq_nonneg d),
          Real.sqrt_sq hd]

/-- Clamp x to the open interval (a, b), moving it at most δ. If a < b and
    a ≤ x ≤ b, return x' ∈ (a, b) with |x - x'| < δ for any δ > 0. -/
private theorem exists_clamp_open {a b x : ℝ} (hab : a < b) (hle : a ≤ x) (hle' : x ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x', a < x' ∧ x' < b ∧ |x - x'| < δ := by
  by_cases hxa : a = x
  · -- x is the left endpoint: pick min(a + δ/2, (a+b)/2)
    have hmid : a < (a + b) / 2 := by linarith
    refine ⟨min (a + δ / 2) ((a + b) / 2), ?_, ?_, ?_⟩
    · exact lt_min (by linarith) hmid
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · rw [← hxa]
      have hge : a ≤ min (a + δ / 2) ((a + b) / 2) :=
        le_min (by linarith) hmid.le
      rw [show a - min (a + δ / 2) ((a + b) / 2) =
        -(min (a + δ / 2) ((a + b) / 2) - a) from by ring,
        abs_neg, abs_of_nonneg (by linarith)]
      linarith [min_le_left (a + δ / 2) ((a + b) / 2)]
  · by_cases hxb : x = b
    · -- x is the right endpoint: pick max(b - δ/2, (a+b)/2)
      have hmid : (a + b) / 2 < b := by linarith
      have hlt := max_lt (show b - δ / 2 < b by linarith) hmid
      refine ⟨max (b - δ / 2) ((a + b) / 2), ?_, ?_, ?_⟩
      · exact lt_of_lt_of_le (by linarith : a < (a + b) / 2)
          (le_max_right _ _)
      · exact hlt
      · rw [hxb, abs_of_nonneg (by linarith)]
        linarith [le_max_left (b - δ / 2) ((a + b) / 2)]
    · -- x is strictly interior
      exact ⟨x, lt_of_le_of_ne hle (fun h => hxa h),
             lt_of_le_of_ne hle' hxb, by simp [hδ]⟩

/-! ## Closures of cells -/

-- The closure computations are the technical core of Section B.
-- Strategy: show the target closed set (a) is closed, (b) contains the cell,
-- and (c) every point in it is a limit of cell points.
-- Part (c): given z in the closed cell, find w in the open cell within dist ε
-- of z. We clamp the boundary coordinates into the strict interior.

/-- The closure of a horizontal edge is a closed horizontal segment.
    HOL Light: `h_edge_closure` (line 2856). -/
theorem closure_hEdge (m : ℤ × ℤ) :
    closure (hEdge m) =
      {z : E2 | (↑m.1 : ℝ) ≤ z 0 ∧ z 0 ≤ ↑m.1 + 1 ∧ z 1 = ↑m.2} := by
  apply subset_antisymm
  · -- closure ⊆ closed set: the closed set is closed and contains hEdge
    apply closure_minimal
    · intro z ⟨h1, h2, h3⟩; exact ⟨le_of_lt h1, le_of_lt h2, h3⟩
    · exact (isClosed_le continuous_const continuous_coord0).and <|
        (isClosed_le continuous_coord0 continuous_const).and
          (isClosed_eq continuous_coord1 continuous_const)
  · -- closed set ⊆ closure: every point in the closed segment is a limit
    intro z ⟨h1, h2, h3⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    -- We need w ∈ hEdge m ∩ U.
    -- Construct w with w 1 = m.2 and w 0 ∈ (m.1, m.1+1) close to z 0.
    have hab : (↑m.1 : ℝ) < ↑m.1 + 1 := by linarith
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := exists_clamp_open hab h1 h2 hε
    refine ⟨mkE2' x' (↑m.2), ?_, ?_⟩
    · -- w is in U (it's in the ball)
      apply hball
      rw [Metric.mem_ball]
      calc dist (mkE2' x' ↑m.2) z
          = dist (mkE2' x' (z 1)) z := by rw [h3]
        _ = dist (mkE2' x' (z 1)) (mkE2' (z 0) (z 1)) := by
            congr 1
            symm; apply (WithLp.equiv 2 _).injective
            funext i; fin_cases i <;> simp [mkE2']
        _ = |x' - z 0| := dist_mkE2'_same_snd x' (z 0) (z 1)
        _ = |z 0 - x'| := by rw [abs_sub_comm]
        _ < ε := hx'3
    · -- w ∈ hEdge m
      exact ⟨by simp [hx'1], by simp [hx'2], by simp⟩

/-- The closure of a vertical edge is a closed vertical segment.
    HOL Light: `v_edge_closure` (line 3052). -/
theorem closure_vEdge (m : ℤ × ℤ) :
    closure (vEdge m) =
      {z : E2 | z 0 = (↑m.1 : ℝ) ∧ (↑m.2 : ℝ) ≤ z 1 ∧ z 1 ≤ ↑m.2 + 1} := by
  apply subset_antisymm
  · apply closure_minimal
    · intro z ⟨h1, h2, h3⟩; exact ⟨h1, le_of_lt h2, le_of_lt h3⟩
    · exact (isClosed_eq continuous_coord0 continuous_const).and <|
        (isClosed_le continuous_const continuous_coord1).and
          (isClosed_le continuous_coord1 continuous_const)
  · intro z ⟨h1, h2, h3⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hab : (↑m.2 : ℝ) < ↑m.2 + 1 := by linarith
    obtain ⟨y', hy'1, hy'2, hy'3⟩ := exists_clamp_open hab h2 h3 hε
    refine ⟨mkE2' (↑m.1) y', ?_, ?_⟩
    · apply hball
      rw [Metric.mem_ball]
      calc dist (mkE2' ↑m.1 y') z
          = dist (mkE2' (z 0) y') z := by rw [h1]
        _ = dist (mkE2' (z 0) y') (mkE2' (z 0) (z 1)) := by
            congr 1
            symm; apply (WithLp.equiv 2 _).injective
            funext i; fin_cases i <;> simp [mkE2']
        _ = |y' - z 1| := dist_mkE2'_same_fst y' (z 1) (z 0)
        _ = |z 1 - y'| := by rw [abs_sub_comm]
        _ < ε := hy'3
    · exact ⟨by simp, by simp [hy'1], by simp [hy'2]⟩

/-- The closure of an open unit square is the closed unit square.
    HOL Light: follows from half-plane closures (lines 2684–2920). -/
theorem closure_squ (m : ℤ × ℤ) :
    closure (squ m) =
      {z : E2 | (↑m.1 : ℝ) ≤ z 0 ∧ z 0 ≤ ↑m.1 + 1 ∧
                (↑m.2 : ℝ) ≤ z 1 ∧ z 1 ≤ ↑m.2 + 1} := by
  apply subset_antisymm
  · apply closure_minimal
    · exact fun z ⟨h1, h2, h3, h4⟩ =>
        ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩
    · exact (isClosed_le continuous_const continuous_coord0).and <|
        (isClosed_le continuous_coord0 continuous_const).and <|
          (isClosed_le continuous_const continuous_coord1).and
            (isClosed_le continuous_coord1 continuous_const)
  · intro z ⟨h1, h2, h3, h4⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    -- Clamp both coordinates into the open interior
    have habx : (↑m.1 : ℝ) < ↑m.1 + 1 := by linarith
    have haby : (↑m.2 : ℝ) < ↑m.2 + 1 := by linarith
    -- We need |x-x'| and |y-y'| both small enough that the L2 distance < ε.
    -- Using ε / 2 for each coordinate suffices since sqrt(2) * (ε/2) < ε.
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := exists_clamp_open habx h1 h2 hε2
    obtain ⟨y', hy'1, hy'2, hy'3⟩ := exists_clamp_open haby h3 h4 hε2
    refine ⟨mkE2' x' y', ?_, ?_⟩
    · apply hball
      rw [Metric.mem_ball]
      have hle : dist (mkE2' x' y') z ≤ (ε / 2) * Real.sqrt 2 := by
        have hzext : z = mkE2' (z 0) (z 1) := by
          symm; apply (WithLp.equiv 2 _).injective
          funext i; fin_cases i <;> simp [mkE2']
        rw [hzext]
        exact dist_le_of_coord_le
          (by simp only [Fin.isValue, mkE2'_coord0]; rw [abs_sub_comm]; exact le_of_lt hx'3)
          (by simp only [Fin.isValue, mkE2'_coord1]; rw [abs_sub_comm]; exact le_of_lt hy'3)
          (le_of_lt hε2)
      calc dist (mkE2' x' y') z ≤ (ε / 2) * Real.sqrt 2 := hle
        _ < ε := by
            rw [div_mul_eq_mul_div]
            have : Real.sqrt 2 < 2 := by
              calc Real.sqrt 2 < Real.sqrt 4 :=
                Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
              _ = 2 := by
                rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
                  Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
            nlinarith
    · exact ⟨by simp [hx'1], by simp [hx'2], by simp [hy'1], by simp [hy'2]⟩

/-- The closure of a lattice point is itself. -/
theorem closure_pointI (m : ℤ × ℤ) :
    closure ({pointI m} : Set E2) = {pointI m} :=
  IsClosed.closure_eq isClosed_singleton

/-! ## Boundary membership -/

/-- A lattice point is in the closure of a horizontal edge iff it is
    an endpoint of that edge. -/
theorem pointI_mem_closure_hEdge (m n : ℤ × ℤ) :
    pointI m ∈ closure (hEdge n) ↔ m.2 = n.2 ∧ (m.1 = n.1 ∨ m.1 = n.1 + 1) := by
  rw [closure_hEdge]
  simp only [mem_setOf_eq, pointI_coord_fst, pointI_coord_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have : m.2 = n.2 := by exact_mod_cast h3
    refine ⟨this, ?_⟩
    have : n.1 ≤ m.1 := by exact_mod_cast h1
    have : m.1 ≤ n.1 + 1 := by exact_mod_cast h2
    omega
  · rintro ⟨h3, h12⟩
    refine ⟨by exact_mod_cast (show n.1 ≤ m.1 by omega),
            by exact_mod_cast (show m.1 ≤ n.1 + 1 by omega),
            by exact_mod_cast h3⟩

/-- A lattice point is in the closure of a vertical edge iff it is
    an endpoint of that edge. -/
theorem pointI_mem_closure_vEdge (m n : ℤ × ℤ) :
    pointI m ∈ closure (vEdge n) ↔ m.1 = n.1 ∧ (m.2 = n.2 ∨ m.2 = n.2 + 1) := by
  rw [closure_vEdge]
  simp only [mem_setOf_eq, pointI_coord_fst, pointI_coord_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have : m.1 = n.1 := by exact_mod_cast h1
    refine ⟨this, ?_⟩
    have : n.2 ≤ m.2 := by exact_mod_cast h2
    have : m.2 ≤ n.2 + 1 := by exact_mod_cast h3
    omega
  · rintro ⟨h1, h23⟩
    refine ⟨by exact_mod_cast h1,
            by exact_mod_cast (show n.2 ≤ m.2 by omega),
            by exact_mod_cast (show m.2 ≤ n.2 + 1 by omega)⟩

/-- A lattice point is in the closure of a square iff it is a corner. -/
theorem pointI_mem_closure_squ (m n : ℤ × ℤ) :
    pointI m ∈ closure (squ n) ↔
      (m.1 = n.1 ∨ m.1 = n.1 + 1) ∧ (m.2 = n.2 ∨ m.2 = n.2 + 1) := by
  rw [closure_squ]
  simp only [mem_setOf_eq, pointI_coord_fst, pointI_coord_snd]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    constructor
    · have : n.1 ≤ m.1 := by exact_mod_cast h1
      have : m.1 ≤ n.1 + 1 := by exact_mod_cast h2
      omega
    · have : n.2 ≤ m.2 := by exact_mod_cast h3
      have : m.2 ≤ n.2 + 1 := by exact_mod_cast h4
      omega
  · rintro ⟨h12, h34⟩
    refine ⟨by exact_mod_cast (show n.1 ≤ m.1 by omega),
            by exact_mod_cast (show m.1 ≤ n.1 + 1 by omega),
            by exact_mod_cast (show n.2 ≤ m.2 by omega),
            by exact_mod_cast (show m.2 ≤ n.2 + 1 by omega)⟩

/-! ## Adjacency theorems (moved from SectionA where closure was unavailable) -/

-- Helper: hEdge m is a cell
private theorem isCell_hEdge (m : ℤ × ℤ) : isCell (hEdge m) := ⟨.hEdge m, rfl⟩
private theorem isCell_vEdge (m : ℤ × ℤ) : isCell (vEdge m) := ⟨.vEdge m, rfl⟩
private theorem isCell_squ (m : ℤ × ℤ) : isCell (squ m) := ⟨.squ m, rfl⟩
private theorem isCell_pointI (m : ℤ × ℤ) : isCell ({pointI m} : Set E2) := ⟨.point m, rfl⟩

-- Helper: hEdge is distinct from a singleton lattice point
private theorem hEdge_ne_pointI (m n : ℤ × ℤ) : hEdge m ≠ ({pointI n} : Set E2) := by
  intro h
  have := hEdge_nonempty m
  rw [h] at this
  obtain ⟨z, hz⟩ := this
  rw [mem_singleton_iff] at hz
  exact hEdge_not_pointI m n (h ▸ mem_singleton_iff.mpr rfl)

private theorem hEdge_ne_squ (m n : ℤ × ℤ) : hEdge m ≠ squ n := by
  intro h
  have := hEdge_nonempty m
  rw [h] at this
  obtain ⟨z, hz⟩ := this
  have hmem : z ∈ hEdge m := h ▸ hz
  have hsmem : z ∈ squ n := hz
  obtain ⟨_, _, hy⟩ := hmem
  obtain ⟨_, _, hy2, hy3⟩ := hsmem
  rw [hy] at hy2 hy3
  have := Int.cast_lt (R := ℝ).mp hy2
  have := Int.cast_lt (R := ℝ).mp (show (↑m.2 : ℝ) < ↑(n.2 + 1) by push_cast; linarith)
  omega

private theorem vEdge_ne_pointI (m n : ℤ × ℤ) : vEdge m ≠ ({pointI n} : Set E2) := by
  intro h
  have := vEdge_nonempty m
  rw [h] at this
  obtain ⟨z, hz⟩ := this
  rw [mem_singleton_iff] at hz
  exact vEdge_not_pointI m n (h ▸ mem_singleton_iff.mpr rfl)

private theorem vEdge_ne_squ (m n : ℤ × ℤ) : vEdge m ≠ squ n := by
  intro h
  have := vEdge_nonempty m
  rw [h] at this
  obtain ⟨z, hz⟩ := this
  have hmem : z ∈ vEdge m := h ▸ hz
  have hsmem : z ∈ squ n := hz
  obtain ⟨hx, _, _⟩ := hmem
  obtain ⟨hx2, hx3, _, _⟩ := hsmem
  rw [hx] at hx2 hx3
  have := Int.cast_lt (R := ℝ).mp hx2
  have := Int.cast_lt (R := ℝ).mp (show (↑m.1 : ℝ) < ↑(n.1 + 1) by push_cast; linarith)
  omega

/-- The left vertex `pointI m` is adjacent to the horizontal edge `hEdge m`. -/
theorem hEdge_adj_left (m : ℤ × ℤ) :
    cellAdj (hEdge m) {pointI m} := by
  refine ⟨isCell_hEdge m, isCell_pointI m, hEdge_ne_pointI m m, ?_⟩
  exact ⟨pointI m,
    by rw [closure_hEdge, mem_setOf_eq]
       simp only [pointI_coord_fst, pointI_coord_snd]
       exact ⟨le_refl _, by linarith, trivial⟩,
    by rw [closure_pointI]; exact mem_singleton_iff.mpr rfl⟩

/-- The right vertex `pointI (m.1 + 1, m.2)` is adjacent to the horizontal edge `hEdge m`. -/
theorem hEdge_adj_right (m : ℤ × ℤ) :
    cellAdj (hEdge m) {pointI (m.1 + 1, m.2)} := by
  refine ⟨isCell_hEdge m, isCell_pointI _, hEdge_ne_pointI m _, ?_⟩
  refine ⟨pointI (m.1 + 1, m.2), ?_, ?_⟩
  · rw [closure_hEdge, mem_setOf_eq]
    simp only [pointI_coord_fst, pointI_coord_snd]
    push_cast
    exact ⟨by linarith, le_refl _, trivial⟩
  · rw [closure_pointI]; exact mem_singleton_iff.mpr rfl

/-- The horizontal edge `hEdge m` is adjacent to the open square `squ m` directly above it. -/
theorem hEdge_adj_squ_above (m : ℤ × ℤ) :
    cellAdj (hEdge m) (squ m) := by
  refine ⟨isCell_hEdge m, isCell_squ m, hEdge_ne_squ m m, ?_⟩
  -- The midpoint of the edge is in the closure of both
  refine ⟨mkE2' ((↑m.1 : ℝ) + 1/2) (↑m.2), ?_, ?_⟩
  · rw [closure_hEdge, mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith
  · rw [closure_squ, mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith

/-- The horizontal edge `hEdge m` is adjacent to the open square
    `squ (m.1, m.2 - 1)` directly below it. -/
theorem hEdge_adj_squ_below (m : ℤ × ℤ) :
    cellAdj (hEdge m) (squ (m.1, m.2 - 1)) := by
  refine ⟨isCell_hEdge m, isCell_squ _, hEdge_ne_squ m _, ?_⟩
  refine ⟨mkE2' ((↑m.1 : ℝ) + 1/2) (↑m.2), ?_, ?_⟩
  · rw [closure_hEdge, mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith
  · rw [closure_squ, mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith

/-- The bottom vertex `pointI m` is adjacent to the vertical edge `vEdge m`. -/
theorem vEdge_adj_bottom (m : ℤ × ℤ) :
    cellAdj (vEdge m) {pointI m} := by
  refine ⟨isCell_vEdge m, isCell_pointI m, vEdge_ne_pointI m m, ?_⟩
  exact ⟨pointI m,
    by rw [closure_vEdge, mem_setOf_eq]
       simp only [pointI_coord_fst, pointI_coord_snd]
       exact ⟨trivial, le_refl _, by linarith⟩,
    by rw [closure_pointI]; exact mem_singleton_iff.mpr rfl⟩

/-- The top vertex `pointI (m.1, m.2 + 1)` is adjacent to the vertical edge `vEdge m`. -/
theorem vEdge_adj_top (m : ℤ × ℤ) :
    cellAdj (vEdge m) {pointI (m.1, m.2 + 1)} := by
  refine ⟨isCell_vEdge m, isCell_pointI _, vEdge_ne_pointI m _, ?_⟩
  refine ⟨pointI (m.1, m.2 + 1), ?_, ?_⟩
  · rw [closure_vEdge, mem_setOf_eq]
    simp only [pointI_coord_fst, pointI_coord_snd]
    push_cast
    exact ⟨trivial, by linarith, le_refl _⟩
  · rw [closure_pointI]; exact mem_singleton_iff.mpr rfl

/-- The vertical edge `vEdge m` is adjacent to the open square `squ m` directly to its right. -/
theorem vEdge_adj_squ_right (m : ℤ × ℤ) :
    cellAdj (vEdge m) (squ m) := by
  refine ⟨isCell_vEdge m, isCell_squ m, vEdge_ne_squ m m, ?_⟩
  refine ⟨mkE2' (↑m.1) ((↑m.2 : ℝ) + 1/2), ?_, ?_⟩
  · rw [closure_vEdge, mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith
  · rw [closure_squ, mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith

/-- The vertical edge `vEdge m` is adjacent to the open square
    `squ (m.1 - 1, m.2)` directly to its left. -/
theorem vEdge_adj_squ_left (m : ℤ × ℤ) :
    cellAdj (vEdge m) (squ (m.1 - 1, m.2)) := by
  refine ⟨isCell_vEdge m, isCell_squ _, vEdge_ne_squ m _, ?_⟩
  refine ⟨mkE2' (↑m.1) ((↑m.2 : ℝ) + 1/2), ?_, ?_⟩
  · rw [closure_vEdge, mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith
  · rw [closure_squ, mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkE2'] ; linarith

/-! ## Incident edge characterization (moved from SectionA) -/

/-- A lattice point is in the closure of an edge iff the edge is one of the
    four edges incident to that point.
    HOL Light: used in `num_closure_le_four` (line 3138). -/
theorem incident_edges_characterize (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) (e : Set E2) (he : e ∈ G) :
    pointI m ∈ closure e ↔
      e = hEdge (m.1 - 1, m.2) ∨ e = hEdge m ∨
      e = vEdge (m.1, m.2 - 1) ∨ e = vEdge m := by
  constructor
  · intro hmem
    rcases hG e he with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · -- e = hEdge n
      rw [pointI_mem_closure_hEdge] at hmem
      obtain ⟨hy, hx⟩ := hmem
      rcases hx with h1 | h1
      · right; left; congr 1; exact Prod.ext h1.symm hy.symm
      · left; congr 1
        exact Prod.ext (show n.1 = m.1 - 1 by omega) hy.symm
    · -- e = vEdge n
      rw [pointI_mem_closure_vEdge] at hmem
      obtain ⟨hx, hy⟩ := hmem
      rcases hy with h1 | h1
      · right; right; right; congr 1; exact Prod.ext hx.symm h1.symm
      · right; right; left; congr 1
        exact Prod.ext hx.symm (show n.2 = m.2 - 1 by omega)
  · rintro (rfl | rfl | rfl | rfl)
    · rw [pointI_mem_closure_hEdge]; exact ⟨rfl, by omega⟩
    · rw [pointI_mem_closure_hEdge]; exact ⟨rfl, Or.inl rfl⟩
    · rw [pointI_mem_closure_vEdge]; exact ⟨rfl, by omega⟩
    · rw [pointI_mem_closure_vEdge]; exact ⟨rfl, Or.inl rfl⟩

open Classical in
/-- At most 4 edges can be incident to a lattice point. -/
theorem numClosure_le_four (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    numClosure G m ≤ 4 := by
  unfold numClosure incidentEdges
  -- Every element of the filtered set is one of 4 edges
  have hsub : G.filter (fun e => pointI m ∈ closure e) ⊆
    ({hEdge (m.1 - 1, m.2), hEdge m, vEdge (m.1, m.2 - 1), vEdge m} : Finset (Set E2)) := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    exact (incident_edges_characterize G hG m e he.1).mp he.2
  calc (G.filter (fun e => pointI m ∈ closure e)).card
      ≤ ({hEdge (m.1 - 1, m.2), hEdge m, vEdge (m.1, m.2 - 1), vEdge m} :
          Finset (Set E2)).card := Finset.card_le_card hsub
    _ ≤ 4 := by
        have h1 := Finset.card_insert_le (hEdge (m.1 - 1, m.2))
          ({hEdge m, vEdge (m.1, m.2 - 1), vEdge m} : Finset (Set E2))
        have h2 := Finset.card_insert_le (hEdge m)
          ({vEdge (m.1, m.2 - 1), vEdge m} : Finset (Set E2))
        have h3 := Finset.card_insert_le (vEdge (m.1, m.2 - 1))
          ({vEdge m} : Finset (Set E2))
        simp only [Finset.card_singleton] at *
        omega

/-! ## Cell closure containment -/

/-- The closure of a cell is contained in the union of cells adjacent to it
    plus itself. -/
theorem cell_closure_subset (ct : CellType) :
    closure ct.toSet ⊆ ⋃ ct' : CellType,
      {z | z ∈ ct'.toSet ∧ (ct'.toSet = ct.toSet ∨ cellAdj ct.toSet ct'.toSet)} := by
  intro z hz
  rw [mem_iUnion]
  -- Every point belongs to some cell
  obtain ⟨ct', hct'⟩ := cell_covers z
  refine ⟨ct', hct', ?_⟩
  by_cases heq : ct' = ct
  · -- Same cell type
    left; rw [heq]
  · -- Different cell type: adjacency
    right
    have hne : ct.toSet ≠ ct'.toSet := by
      intro h
      have hdj := cell_disjoint heq
      rw [Set.disjoint_left] at hdj
      exact hdj hct' (h ▸ hct')
    exact ⟨⟨ct, rfl⟩, ⟨ct', rfl⟩, hne, ⟨z, hz, subset_closure hct'⟩⟩

/-! ## Connected components of cells -/

-- The open cells are all convex, hence path-connected, hence connected.
-- We prove path-connectedness first and derive connectedness.

private theorem combo_strict_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u v c : ℝ} (hu : c < u) (hv : c < v) : c < a * u + b * v := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [show b = 1 from by linarith]; linarith
  · have := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu ha')
      (mul_le_mul_of_nonneg_left hv.le hb)
    linarith [show a * c + b * c = c from by rw [← add_mul, hab, one_mul]]

private theorem combo_strict_lt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u v c : ℝ} (hu : u < c) (hv : v < c) : a * u + b * v < c := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [show b = 1 from by linarith]; linarith
  · have := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu ha')
      (mul_le_mul_of_nonneg_left hv.le hb)
    linarith [show a * c + b * c = c from by rw [← add_mul, hab, one_mul]]

/-- The open unit square is convex as a set. -/
-- HOL Light: `squ_convex` (line 2726, derived from half-plane convexity).
private theorem squ_convex (m : ℤ × ℤ) : Convex ℝ (squ m) := by
  intro x hx y hy a b ha hb hab
  simp only [squ, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  exact ⟨combo_strict_lt ha hb hab hx.1 hy.1,
    combo_strict_lt' ha hb hab hx.2.1 hy.2.1,
    combo_strict_lt ha hb hab hx.2.2.1 hy.2.2.1,
    combo_strict_lt' ha hb hab hx.2.2.2 hy.2.2.2⟩

/-- Horizontal edges are convex. -/
-- HOL Light: `h_edge_convex` (line 2759).
private theorem hEdge_convex (m : ℤ × ℤ) : Convex ℝ (hEdge m) := by
  intro x hx y hy a b ha hb hab
  simp only [hEdge, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  exact ⟨combo_strict_lt ha hb hab hx.1 hy.1,
    combo_strict_lt' ha hb hab hx.2.1 hy.2.1,
    by rw [hx.2.2, hy.2.2, ← add_mul, hab, one_mul]⟩

/-- Vertical edges are convex. -/
-- HOL Light: `v_edge_convex` (line 2955).
private theorem vEdge_convex (m : ℤ × ℤ) : Convex ℝ (vEdge m) := by
  intro x hx y hy a b ha hb hab
  simp only [vEdge, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  exact ⟨by rw [hx.1, hy.1, ← add_mul, hab, one_mul],
    combo_strict_lt ha hb hab hx.2.1 hy.2.1,
    combo_strict_lt' ha hb hab hx.2.2 hy.2.2⟩

/-- Each open cell is path-connected (stronger than connected). -/
theorem hEdge_isPathConnected (m : ℤ × ℤ) : IsPathConnected (hEdge m) :=
  (hEdge_convex m).isPathConnected (hEdge_nonempty m)

/-- Each open vertical edge is path-connected. -/
theorem vEdge_isPathConnected (m : ℤ × ℤ) : IsPathConnected (vEdge m) :=
  (vEdge_convex m).isPathConnected (vEdge_nonempty m)

/-- Each open square is path-connected. -/
theorem squ_isPathConnected (m : ℤ × ℤ) : IsPathConnected (squ m) :=
  (squ_convex m).isPathConnected (squ_nonempty m)

/-- Each open cell (hEdge, vEdge, squ) is connected. -/
theorem hEdge_isConnected (m : ℤ × ℤ) : IsConnected (hEdge m) :=
  (hEdge_isPathConnected m).isConnected

/-- Each open vertical edge is connected. -/
theorem vEdge_isConnected (m : ℤ × ℤ) : IsConnected (vEdge m) :=
  (vEdge_isPathConnected m).isConnected

/-- Each open square is connected. -/
theorem squ_isConnected (m : ℤ × ℤ) : IsConnected (squ m) :=
  (squ_isPathConnected m).isConnected

/-! ## Set lower finiteness and parity -/

/-- The set of lower horizontal edges is finite.
    HOL Light: `finite_set_lower` (line 3276). -/
theorem finite_setLower (G : Finset (Set E2)) (n : ℤ × ℤ) :
    Set.Finite (setLower G n) :=
  (Finset.finite_toSet G |>.preimage
    (fun m₁ _ m₂ _ h => (hEdge_inj m₁ m₂).mp h)).subset
    fun _m hm => hm.1

/-- Even parity for squares reduces to the parity of `numLower`.
    HOL Light: `even_cell_squ` (line 3336). -/
theorem even_cell_squ (G : Finset (Set E2)) (m : ℤ × ℤ) :
    evenCell G (squ m) ↔ Even (numLower G m) := by
  constructor
  · rintro ⟨m', hm', heven⟩
    rcases hm' with h | h | h | h
    · exact absurd h (squ_ne_pointI_set m m')
    · exact absurd h (squ_ne_hEdge m m')
    · exact absurd h (squ_ne_vEdge m m')
    · have := (squ_inj m m').mp h; subst this; exact heven
  · exact fun h => ⟨m, Or.inr (Or.inr (Or.inr rfl)), h⟩

/-! ## Edge membership (trivial from definition) -/

/-- A horizontal edge is an edge.
    HOL Light: `edge_h` (line 3130). -/
theorem isEdge_hEdge (m : ℤ × ℤ) : isEdge (hEdge m) :=
  Or.inl ⟨m, rfl⟩

/-- A vertical edge is an edge.
    HOL Light: `edge_v` (line 3136). -/
theorem isEdge_vEdge (m : ℤ × ℤ) : isEdge (vEdge m) :=
  Or.inr ⟨m, rfl⟩

end
