/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order

/-!
# Section A: Cell Geometry Foundations
## HOL Light: Pre-sections (Lines 1–2683)

Cell decomposition of ℝ² into four types of cells indexed by integer lattice
points: lattice points, horizontal edges, vertical edges, and open unit squares.
This is the combinatorial backbone of the discrete Jordan Curve Theorem.

### Key HOL Light definitions formalized here
- `point`, `dest_pt` (~1119): Constructor/destructor for points in ℝ²
- `pointI` (~1247): Integer lattice points
- `floor` (~1309): Floor function (Lean uses `Int.floor`)
- `h_edge` (~1500): Open horizontal unit edges
- `v_edge` (~1507): Open vertical unit edges
- `squ` (~1510): Open unit squares
- `row`, `col` (~1514): Row and column strips
- `cell` (~1999): Union of all cell types
- `top2` (~2089): Standard topology on ℝ² (Lean uses typeclass)
- `adj` (~2091): Adjacency relation on cells
- `num_closure` (~2050): Number of incident edges at a lattice point
- `edge` subset of `cell`
-/

open Set Topology Metric

noncomputable section

/-! ## Points in ℝ² -/

/-- The Euclidean plane, ℝ². HOL Light: `euclid 2` (used throughout). -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- A point in ℝ² from a pair of reals.
    HOL Light: `point` (line 1119). -/
abbrev point (p : ℝ × ℝ) : E2 := (WithLp.equiv 2 _).symm ![p.1, p.2]

/-- Extract coordinates from a point in ℝ².
    HOL Light: `dest_pt` (line 1122). -/
def destPoint (z : E2) : ℝ × ℝ := (z 0, z 1)

/-- An integer lattice point.
    HOL Light: `pointI` (line 1247). -/
def pointI (m : ℤ × ℤ) : E2 := point (↑m.1, ↑m.2)

-- ── Auxiliary: coordinate access for point/pointI ──
-- HOL Light: coord01 (line 1133), split into two @[simp] lemmas.
/-- The first coordinate of `point (a, b)` is `a`.
    HOL Light: `coord01` (line 1133). -/
@[simp]
theorem point_coord_zero (a b : ℝ) : (point (a, b)) 0 = a := by
  simp [point, WithLp.equiv]

/-- The second coordinate of `point (a, b)` is `b`.
    HOL Light: `coord01` (line 1133). -/
@[simp]
theorem point_coord_one (a b : ℝ) : (point (a, b)) 1 = b := by
  simp [point, WithLp.equiv]

-- ── pointI lemmas ──

/-- The first coordinate of `pointI m` is `m.1` as a real number. -/
theorem pointI_coord_fst (m : ℤ × ℤ) : pointI m 0 = (m.1 : ℝ) := by
  simp [pointI]

/-- The second coordinate of `pointI m` is `m.2` as a real number. -/
theorem pointI_coord_snd (m : ℤ × ℤ) : pointI m 1 = (m.2 : ℝ) := by
  simp [pointI]

-- HOL Light: `point_inj` (line 1156)
/-- The constructor `point` is injective: equal points have equal coordinate pairs.
    HOL Light: `point_inj` (line 1156). -/
theorem point_injective : Function.Injective (fun p : ℝ × ℝ => point p) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have h0 : (point (a₁, b₁)) 0 = (point (a₂, b₂)) 0 := congrArg (· 0) h
  have h1 : (point (a₁, b₁)) 1 = (point (a₂, b₂)) 1 := congrArg (· 1) h
  simp only [Fin.isValue, point_coord_zero, point_coord_one] at h0 h1
  exact Prod.ext h0 h1

-- HOL Light: `pointI_inj` (line 1520)
/-- The constructor `pointI` is injective: equal lattice points have equal integer pairs.
    HOL Light: `pointI_inj` (line 1520). -/
theorem pointI_injective : Function.Injective pointI := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have h0 : (pointI (a₁, b₁)) 0 = (pointI (a₂, b₂)) 0 := congrArg (· 0) h
  have h1 : (pointI (a₁, b₁)) 1 = (pointI (a₂, b₂)) 1 := congrArg (· 1) h
  simp only [Fin.isValue, pointI_coord_fst, Int.cast_inj, pointI_coord_snd] at h0 h1
  exact Prod.ext (Int.cast_injective h0) (Int.cast_injective h1)

/-- Two integer lattice points are equal as elements of E2 if and only if their
    index pairs are equal. -/
theorem pointI_eq_iff (m n : ℤ × ℤ) : pointI m = pointI n ↔ m = n :=
  ⟨fun h => pointI_injective h, fun h => congrArg pointI h⟩

-- ── Point algebra ──

/-- Every point in E2 is `point (z 0, z 1)`.
    HOL Light: `point_onto` (line 1175). -/
theorem point_surjective (z : E2) : z = point (z 0, z 1) := by
  apply (WithLp.equiv 2 _).injective
  funext i; fin_cases i <;> simp [point, WithLp.equiv]

/-- Scalar multiplication distributes through `point`.
    HOL Light: `point_scale` (line 1278). -/
@[simp] theorem point_smul (a x y : ℝ) : a • point (x, y) = point (a * x, a * y) := by
  apply (WithLp.equiv 2 _).injective
  funext i; fin_cases i <;> simp [point, WithLp.equiv, PiLp.smul_apply, smul_eq_mul]

/-- Addition distributes through `point`.
    HOL Light: `point_add` (line 1290). -/
@[simp] theorem point_add (x₁ y₁ x₂ y₂ : ℝ) :
    point (x₁, y₁) + point (x₂, y₂) = point (x₁ + x₂, y₁ + y₂) := by
  apply (WithLp.equiv 2 _).injective
  funext i; fin_cases i <;> simp [point, WithLp.equiv, PiLp.add_apply]

/-! ## Floor function -/

-- Lean already has `Int.floor` in Mathlib. We record the key interface lemmas.

/-- HOL Light: `floor_ineq` (line 1320). -/
theorem floor_spec (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/-- HOL Light: `floor_range` (line 1482). -/
theorem floor_range (x : ℝ) (m : ℤ) : ⌊x⌋ = m ↔ (↑m : ℝ) ≤ x ∧ x < ↑m + 1 :=
  Int.floor_eq_iff

/-- HOL Light: `floor_mono` (line 1442). -/
theorem floor_mono {x y : ℝ} (h : x ≤ y) : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono h

/-! ## Edges and squares -/

/-- Open horizontal unit edge from `pointI m` to `pointI (m.1 + 1, m.2)`.
    HOL Light: `h_edge m`. -/
def hEdge (m : ℤ × ℤ) : Set E2 :=
  {z | z 0 > (↑m.1 : ℝ) ∧ z 0 < ↑m.1 + 1 ∧ z 1 = ↑m.2}

/-- Open vertical unit edge from `pointI m` to `pointI (m.1, m.2 + 1)`.
    HOL Light: `v_edge m`. -/
def vEdge (m : ℤ × ℤ) : Set E2 :=
  {z | z 0 = (↑m.1 : ℝ) ∧ z 1 > ↑m.2 ∧ z 1 < ↑m.2 + 1}

/-- Open unit square with bottom-left corner at `pointI m`.
    HOL Light: `squ m`. -/
def squ (m : ℤ × ℤ) : Set E2 :=
  {z | z 0 > (↑m.1 : ℝ) ∧ z 0 < ↑m.1 + 1 ∧
       z 1 > (↑m.2 : ℝ) ∧ z 1 < ↑m.2 + 1}

/-- A row strip: all points with y-coordinate equal to integer `k`.
    HOL Light: `row k`. -/
def row (k : ℤ) : Set E2 := {z | z 1 = (↑k : ℝ)}

/-- A column strip: all points with x-coordinate equal to integer `k`.
    HOL Light: `col k`. -/
def col (k : ℤ) : Set E2 := {z | z 0 = (↑k : ℝ)}

-- ── Helper: construct specific E2 points ──

/-- Construct a point in E2 with given coordinates. -/
private def mkE2 (x y : ℝ) : E2 := point (x, y)

-- ── Helper for floor equality ──

/-- The floor of `x` equals `m` when `m ≤ x < m + 1`. -/
theorem floor_eq_of_bounds {x : ℝ} {m : ℤ} (h1 : (↑m : ℝ) ≤ x) (h2 : x < ↑m + 1) :
    ⌊x⌋ = m := by
  have hle : m ≤ ⌊x⌋ := Int.le_floor.mpr h1
  have : x < (↑(m + 1) : ℝ) := by push_cast; linarith
  have hle2 : ⌊x⌋ < m + 1 := by
    by_contra h
    push Not at h
    have : (↑(m + 1) : ℝ) ≤ x := Int.le_floor.mp h
    linarith
  omega

/-- The floor of `x` equals `m` when `m < x < m + 1` (strict lower bound). -/
theorem floor_eq_of_strict_bounds {x : ℝ} {m : ℤ}
    (h1 : (↑m : ℝ) < x) (h2 : x < ↑m + 1) : ⌊x⌋ = m :=
  floor_eq_of_bounds (le_of_lt h1) h2

-- ── Square floor membership ──

/-- For z in squ m, the floor of the x-coordinate is m.1.
    HOL Light: `square_floor0` (line 1906). -/
theorem squ_floor_fst {z : E2} {m : ℤ × ℤ} (h : z ∈ squ m) : ⌊z 0⌋ = m.1 :=
  floor_eq_of_strict_bounds h.1 h.2.1

/-- For z in squ m, the floor of the y-coordinate is m.2.
    HOL Light: `square_floor1` (line 1925). -/
theorem squ_floor_snd {z : E2} {m : ℤ × ℤ} (h : z ∈ squ m) : ⌊z 1⌋ = m.2 :=
  floor_eq_of_strict_bounds h.2.2.1 h.2.2.2

-- ── Edge disjointness ──
-- HOL Light: `h_edge_disj` (line 1578), `v_edge_disj` (line 1689),
-- `hv_edge` (line 1766), `square_disj` (line 1962).

/-- Distinct horizontal edges are disjoint sets.
    HOL Light: `h_edge_disj` (line 1578). -/
theorem hEdge_disjoint_of_ne {m n : ℤ × ℤ} (h : m ≠ n) :
    Disjoint (hEdge m) (hEdge n) := by
  rw [Set.disjoint_left]
  intro z hzm hzn
  simp only [hEdge, mem_setOf_eq] at hzm hzn
  obtain ⟨hm0, hm1, hmy⟩ := hzm
  obtain ⟨hn0, hn1, hny⟩ := hzn
  have heqy : m.2 = n.2 := by exact_mod_cast hmy.symm.trans hny
  have hfm : ⌊z 0⌋ = m.1 := floor_eq_of_strict_bounds hm0 hm1
  have hfn : ⌊z 0⌋ = n.1 := floor_eq_of_strict_bounds hn0 hn1
  have heqx : m.1 = n.1 := by linarith [hfm, hfn]
  exact h (Prod.ext heqx heqy)

/-- Distinct vertical edges are disjoint sets.
    HOL Light: `v_edge_disj` (line 1689). -/
theorem vEdge_disjoint_of_ne {m n : ℤ × ℤ} (h : m ≠ n) :
    Disjoint (vEdge m) (vEdge n) := by
  rw [Set.disjoint_left]
  intro z hzm hzn
  simp only [vEdge, mem_setOf_eq] at hzm hzn
  obtain ⟨hmx, hm0, hm1⟩ := hzm
  obtain ⟨hnx, hn0, hn1⟩ := hzn
  have heqx : m.1 = n.1 := by exact_mod_cast hmx.symm.trans hnx
  have hfm : ⌊z 1⌋ = m.2 := floor_eq_of_strict_bounds hm0 hm1
  have hfn : ⌊z 1⌋ = n.2 := floor_eq_of_strict_bounds hn0 hn1
  have heqy : m.2 = n.2 := by linarith [hfm, hfn]
  exact h (Prod.ext heqx heqy)

/-- Any horizontal edge and any vertical edge are disjoint: their y-constraints conflict.
    HOL Light: `hv_edge` (line 1766). -/
theorem hEdge_vEdge_disjoint (m n : ℤ × ℤ) :
    Disjoint (hEdge m) (vEdge n) := by
  rw [Set.disjoint_left]
  intro z hzh hzv
  simp only [hEdge, vEdge, mem_setOf_eq] at hzh hzv
  obtain ⟨hh0, hh1, hhy⟩ := hzh
  obtain ⟨hvx, hv0, hv1⟩ := hzv
  -- z 1 = m.2 (an integer) from hEdge, but m.2 < z 1 < m.2 + 1 ... no,
  -- actually the constraint from vEdge is n.2 < z 1 < n.2 + 1, and from
  -- hEdge is z 1 = m.2.  So z 1 is an integer (= m.2) but strictly between
  -- n.2 and n.2 + 1, which is impossible for consecutive integers.
  rw [hhy] at hv0 hv1
  have h1 : (n.2 : ℤ) < m.2 := by exact_mod_cast hv0
  have h2 : (m.2 : ℤ) < n.2 + 1 := by
    have : (↑m.2 : ℝ) < ↑n.2 + 1 := hv1
    exact_mod_cast this
  omega

/-- Distinct squares are disjoint sets.
    HOL Light: `square_disj` (line 1962). -/
theorem squ_disjoint_of_ne {m n : ℤ × ℤ} (h : m ≠ n) :
    Disjoint (squ m) (squ n) := by
  rw [Set.disjoint_left]
  intro z hzm hzn
  simp only [squ, mem_setOf_eq] at hzm hzn
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hzm
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hzn
  have hfx_m : ⌊z 0⌋ = m.1 := floor_eq_of_strict_bounds hm0 hm1
  have hfx_n : ⌊z 0⌋ = n.1 := floor_eq_of_strict_bounds hn0 hn1
  have hfy_m : ⌊z 1⌋ = m.2 := floor_eq_of_strict_bounds hm2 hm3
  have hfy_n : ⌊z 1⌋ = n.2 := floor_eq_of_strict_bounds hn2 hn3
  exact h (Prod.ext (by linarith [hfx_m, hfx_n]) (by linarith [hfy_m, hfy_n]))

-- ── Nonemptiness ──

/-- Every horizontal edge is nonempty: the midpoint of the interval witnesses this. -/
theorem hEdge_nonempty (m : ℤ × ℤ) : (hEdge m).Nonempty := by
  refine ⟨mkE2 ((↑m.1 : ℝ) + 1/2) (↑m.2), ?_⟩
  simp only [hEdge, mem_setOf_eq, mkE2, point_coord_zero, point_coord_one]
  exact ⟨by linarith, by linarith, trivial⟩

/-- Every vertical edge is nonempty: the midpoint of the interval witnesses this. -/
theorem vEdge_nonempty (m : ℤ × ℤ) : (vEdge m).Nonempty := by
  refine ⟨mkE2 (↑m.1) ((↑m.2 : ℝ) + 1/2), ?_⟩
  simp only [vEdge, mem_setOf_eq, mkE2, point_coord_zero, point_coord_one]
  exact ⟨trivial, by linarith, by linarith⟩

/-- Every open unit square is nonempty: the centre point witnesses this. -/
theorem squ_nonempty (m : ℤ × ℤ) : (squ m).Nonempty := by
  refine ⟨mkE2 ((↑m.1 : ℝ) + 1/2) ((↑m.2 : ℝ) + 1/2), ?_⟩
  simp only [squ, mem_setOf_eq, mkE2, point_coord_zero, point_coord_one]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## Cell types -/

/-- The four types of cells in the integer grid decomposition of ℝ².
    HOL Light: `cell C` (line 1999). -/
inductive CellType where
  | point (m : ℤ × ℤ)   -- singleton lattice point
  | hEdge (m : ℤ × ℤ)   -- open horizontal edge
  | vEdge (m : ℤ × ℤ)   -- open vertical edge
  | squ   (m : ℤ × ℤ)   -- open unit square

/-- The set of points in a cell. -/
def CellType.toSet : CellType → Set E2
  | .point m => {pointI m}
  | .hEdge m => _root_.hEdge m
  | .vEdge m => _root_.vEdge m
  | .squ m   => _root_.squ m

/-- A set is a cell if it arises from one of the four cell types.
    HOL Light: `cell C`. -/
def isCell (C : Set E2) : Prop :=
  ∃ ct : CellType, C = ct.toSet

open Classical in
/-- Determine the cell type of a point from its coordinates.
    Every point of ℝ² belongs to exactly one cell type depending on
    whether its coordinates are integers or not. -/
def cellOf (z : E2) : CellType :=
  let x := z 0; let y := z 1
  if hx : ∃ m : ℤ, x = ↑m then
    if hy : ∃ n : ℤ, y = ↑n then
      .point (hx.choose, hy.choose)
    else
      .vEdge (⟨⌊x⌋, ⌊y⌋⟩)
  else
    if hy : ∃ n : ℤ, y = ↑n then
      .hEdge (⟨⌊x⌋, hy.choose⟩)
    else
      .squ (⟨⌊x⌋, ⌊y⌋⟩)

/-- Every point belongs to some cell. -/
theorem cell_covers (z : E2) : ∃ ct : CellType, z ∈ ct.toSet := by
  by_cases hx : ∃ m : ℤ, z 0 = ↑m <;> by_cases hy : ∃ n : ℤ, z 1 = ↑n
  · -- Both coordinates are integers: lattice point
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨.point (m, n), ?_⟩
    simp only [CellType.toSet, mem_singleton_iff, pointI]
    apply (WithLp.equiv 2 _).injective
    funext i; fin_cases i <;> simp [point, WithLp.equiv, hm, hn]
  · -- x is integer, y is not: vertical edge
    obtain ⟨m, hm⟩ := hx
    refine ⟨.vEdge (m, ⌊z 1⌋), ?_⟩
    simp only [CellType.toSet, vEdge, mem_setOf_eq]
    have hfly := floor_spec (z 1)
    refine ⟨hm, ?_, hfly.2⟩
    exact lt_of_le_of_ne hfly.1
      (fun h => hy ⟨⌊z 1⌋, by exact h.symm⟩)
  · -- x is not integer, y is integer: horizontal edge
    obtain ⟨n, hn⟩ := hy
    refine ⟨.hEdge (⌊z 0⌋, n), ?_⟩
    simp only [CellType.toSet, hEdge, mem_setOf_eq]
    have hflx := floor_spec (z 0)
    refine ⟨?_, hflx.2, hn⟩
    exact lt_of_le_of_ne hflx.1
      (fun h => hx ⟨⌊z 0⌋, by exact h.symm⟩)
  · -- Neither coordinate is integer: square
    refine ⟨.squ (⌊z 0⌋, ⌊z 1⌋), ?_⟩
    simp only [CellType.toSet, squ, mem_setOf_eq]
    have hflx := floor_spec (z 0)
    have hfly := floor_spec (z 1)
    refine ⟨?_, hflx.2, ?_, hfly.2⟩
    · exact lt_of_le_of_ne hflx.1
        (fun h => hx ⟨⌊z 0⌋, by exact h.symm⟩)
    · exact lt_of_le_of_ne hfly.1
        (fun h => hy ⟨⌊z 1⌋, by exact h.symm⟩)

/-- Auxiliary: a point in a singleton cell has integer coordinates. -/
theorem mem_pointI_singleton {z : E2} {m : ℤ × ℤ} (h : z ∈ ({pointI m} : Set E2)) :
    z 0 = ↑m.1 ∧ z 1 = ↑m.2 := by
  rw [mem_singleton_iff] at h
  exact ⟨by rw [h]; exact pointI_coord_fst m, by rw [h]; exact pointI_coord_snd m⟩

/-- Auxiliary: membership in hEdge implies non-integer x and integer y. -/
theorem mem_hEdge_coords {z : E2} {m : ℤ × ℤ} (h : z ∈ hEdge m) :
    (↑m.1 : ℝ) < z 0 ∧ z 0 < ↑m.1 + 1 ∧ z 1 = ↑m.2 := h

/-- Auxiliary: membership in vEdge implies integer x and non-integer y. -/
theorem mem_vEdge_coords {z : E2} {m : ℤ × ℤ} (h : z ∈ vEdge m) :
    z 0 = ↑m.1 ∧ (↑m.2 : ℝ) < z 1 ∧ z 1 < ↑m.2 + 1 := h

/-- Auxiliary: membership in squ implies non-integer x and y. -/
theorem mem_squ_coords {z : E2} {m : ℤ × ℤ} (h : z ∈ squ m) :
    (↑m.1 : ℝ) < z 0 ∧ z 0 < ↑m.1 + 1 ∧ (↑m.2 : ℝ) < z 1 ∧ z 1 < ↑m.2 + 1 := h

/-- No point in a horizontal edge is a lattice point. -/
theorem hEdge_not_pointI (m n : ℤ × ℤ) : pointI n ∉ hEdge m := by
  simp only [hEdge, mem_setOf_eq, pointI_coord_fst, pointI_coord_snd, not_and]
  intro h1 h2
  have hlt1 : m.1 < n.1 := by exact_mod_cast h1
  have hlt2 : n.1 < m.1 + 1 := by exact_mod_cast h2
  omega

/-- No point in a vertical edge is a lattice point. -/
theorem vEdge_not_pointI (m n : ℤ × ℤ) : pointI n ∉ vEdge m := by
  simp only [vEdge, mem_setOf_eq, pointI_coord_fst, pointI_coord_snd, not_and]
  intro _ h1 h2
  have hlt1 : m.2 < n.2 := by exact_mod_cast h1
  have hlt2 : n.2 < m.2 + 1 := by exact_mod_cast h2
  omega

/-- No lattice point is in a square. -/
theorem squ_not_pointI (m n : ℤ × ℤ) : pointI n ∉ squ m := by
  simp only [squ, mem_setOf_eq, pointI_coord_fst, pointI_coord_snd, not_and]
  intro h1 h2 _ _
  have hlt1 : m.1 < n.1 := by exact_mod_cast h1
  have hlt2 : n.1 < m.1 + 1 := by exact_mod_cast h2
  omega

-- ── Cell type injectivity ──

/-- HOL Light: `h_edge_inj` (line 3249). -/
theorem hEdge_inj (m n : ℤ × ℤ) : hEdge m = hEdge n ↔ m = n := by
  constructor
  · intro h
    by_contra hne
    have hdis := hEdge_disjoint_of_ne hne
    obtain ⟨z, hz⟩ := hEdge_nonempty m
    exact Set.disjoint_left.mp hdis hz (h ▸ hz)
  · rintro rfl; rfl

/-- HOL Light: `v_edge_inj` (line 3258). -/
theorem vEdge_inj (m n : ℤ × ℤ) : vEdge m = vEdge n ↔ m = n := by
  constructor
  · intro h
    by_contra hne
    have hdis := vEdge_disjoint_of_ne hne
    obtain ⟨z, hz⟩ := vEdge_nonempty m
    exact Set.disjoint_left.mp hdis hz (h ▸ hz)
  · rintro rfl; rfl

/-- HOL Light: `squ_inj` (line 3267). -/
theorem squ_inj (m n : ℤ × ℤ) : squ m = squ n ↔ m = n := by
  constructor
  · intro h
    by_contra hne
    have hdis := squ_disjoint_of_ne hne
    obtain ⟨z, hz⟩ := squ_nonempty m
    exact Set.disjoint_left.mp hdis hz (h ▸ hz)
  · rintro rfl; rfl

-- ── Cell type discrimination ──

/-- HOL Light: `hv_edgeV2` (line 3224). -/
theorem hEdge_ne_vEdge (m n : ℤ × ℤ) : hEdge m ≠ vEdge n := by
  intro h
  obtain ⟨z, hz⟩ := hEdge_nonempty m
  exact Set.disjoint_left.mp (hEdge_vEdge_disjoint m n) hz (h ▸ hz)

/-- HOL Light: `square_v_edgeV2` (line 3232). -/
theorem squ_ne_vEdge (m n : ℤ × ℤ) : squ m ≠ vEdge n := by
  intro h
  obtain ⟨z, hz⟩ := squ_nonempty m
  have hmem : z ∈ vEdge n := h ▸ hz
  obtain ⟨hx1, hx2, _, _⟩ := mem_squ_coords hz
  obtain ⟨hxv, _, _⟩ := mem_vEdge_coords hmem
  rw [hxv] at hx1 hx2
  have : m.1 < n.1 := by exact_mod_cast hx1
  have : n.1 < m.1 + 1 := by push_cast at hx2; exact_mod_cast hx2
  omega

/-- HOL Light: `square_h_edgeV2` (line 3240). -/
theorem squ_ne_hEdge (m n : ℤ × ℤ) : squ m ≠ hEdge n := by
  intro h
  obtain ⟨z, hz⟩ := squ_nonempty m
  have hmem : z ∈ hEdge n := h ▸ hz
  obtain ⟨_, _, hy1, hy2⟩ := mem_squ_coords hz
  obtain ⟨_, _, hyv⟩ := mem_hEdge_coords hmem
  rw [hyv] at hy1 hy2
  have : m.2 < n.2 := by exact_mod_cast hy1
  have : n.2 < m.2 + 1 := by push_cast at hy2; exact_mod_cast hy2
  omega

/-- HOL Light: `h_edge_pointIv2` (line 3181). -/
theorem hEdge_ne_pointI_set (m n : ℤ × ℤ) : hEdge m ≠ ({pointI n} : Set E2) :=
  fun h => hEdge_not_pointI m n (show pointI n ∈ hEdge m from h ▸ rfl)
/-- A vertical edge is never equal to a singleton lattice-point set.
    HOL Light: `v_edge_pointIv2` (line 3181). -/
theorem vEdge_ne_pointI_set (m n : ℤ × ℤ) : vEdge m ≠ ({pointI n} : Set E2) :=
  fun h => vEdge_not_pointI m n (show pointI n ∈ vEdge m from h ▸ rfl)
/-- A square is never equal to a singleton lattice-point set.
    HOL Light: `square_pointIv2` (line 3181). -/
theorem squ_ne_pointI_set (m n : ℤ × ℤ) : squ m ≠ ({pointI n} : Set E2) :=
  fun h => squ_not_pointI m n (show pointI n ∈ squ m from h ▸ rfl)
/-- Distinct cells (of any types) are disjoint sets.
    HOL Light: `cell_disjoint` (line 1999). -/
theorem cell_disjoint {c₁ c₂ : CellType} (h : c₁ ≠ c₂) :
    Disjoint c₁.toSet c₂.toSet := by
  match c₁, c₂ with
  | .point m, .point n =>
    rw [Set.disjoint_left]
    intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hm hn
    exact h (by rw [CellType.point.injEq]; exact pointI_injective (hm.symm ▸ hn))
  | .point m, .hEdge n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hm
    exact hEdge_not_pointI n m (hm ▸ hn)
  | .point m, .vEdge n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hm
    exact vEdge_not_pointI n m (hm ▸ hn)
  | .point m, .squ n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hm
    exact squ_not_pointI n m (hm ▸ hn)
  | .hEdge m, .point n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hn
    exact hEdge_not_pointI m n (hn ▸ hm)
  | .hEdge m, .hEdge n =>
    exact hEdge_disjoint_of_ne (fun heq => h (heq ▸ rfl))
  | .hEdge m, .vEdge n =>
    exact hEdge_vEdge_disjoint m n
  | .hEdge m, .squ n =>
    rw [Set.disjoint_left]; intro z hm hn
    obtain ⟨_, _, hmy⟩ := mem_hEdge_coords hm
    obtain ⟨_, _, hny, hny'⟩ := mem_squ_coords hn
    rw [hmy] at hny hny'
    have : n.2 < m.2 := by exact_mod_cast hny
    have : m.2 < n.2 + 1 := by push_cast at hny'; exact_mod_cast hny'
    omega
  | .vEdge m, .point n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hn
    exact vEdge_not_pointI m n (hn ▸ hm)
  | .vEdge m, .hEdge n =>
    exact (hEdge_vEdge_disjoint n m).symm
  | .vEdge m, .vEdge n =>
    exact vEdge_disjoint_of_ne (fun heq => h (heq ▸ rfl))
  | .vEdge m, .squ n =>
    rw [Set.disjoint_left]; intro z hm hn
    obtain ⟨hmx, _, _⟩ := mem_vEdge_coords hm
    obtain ⟨hnx, hnx', _, _⟩ := mem_squ_coords hn
    rw [hmx] at hnx hnx'
    have : n.1 < m.1 := by exact_mod_cast hnx
    have : m.1 < n.1 + 1 := by push_cast at hnx'; exact_mod_cast hnx'
    omega
  | .squ m, .point n =>
    rw [Set.disjoint_left]; intro z hm hn
    rw [CellType.toSet, mem_singleton_iff] at hn
    exact squ_not_pointI m n (hn ▸ hm)
  | .squ m, .hEdge n =>
    rw [Set.disjoint_left]; intro z hm hn
    obtain ⟨_, _, hmy, hmy'⟩ := mem_squ_coords hm
    obtain ⟨_, _, hny⟩ := mem_hEdge_coords hn
    rw [hny] at hmy hmy'
    have : m.2 < n.2 := by exact_mod_cast hmy
    have : n.2 < m.2 + 1 := by push_cast at hmy'; exact_mod_cast hmy'
    omega
  | .squ m, .vEdge n =>
    rw [Set.disjoint_left]; intro z hm hn
    obtain ⟨hmx, hmx', _, _⟩ := mem_squ_coords hm
    obtain ⟨hnx, _, _⟩ := mem_vEdge_coords hn
    rw [hnx] at hmx hmx'
    have : m.1 < n.1 := by exact_mod_cast hmx
    have : n.1 < m.1 + 1 := by push_cast at hmx'; exact_mod_cast hmx'
    omega
  | .squ m, .squ n =>
    exact squ_disjoint_of_ne (fun heq => h (heq ▸ rfl))

/-- The cells partition ℝ²: every point of ℝ² belongs to exactly one cell.
    HOL Light: `cell_partition`. -/
theorem cell_partition :
    (∀ z : E2, ∃! ct : CellType, z ∈ ct.toSet) := by
  intro z
  obtain ⟨ct, hct⟩ := cell_covers z
  exact ⟨ct, hct, fun ct' hct' => by
    by_contra h
    have hdis := cell_disjoint (Ne.symm h)
    exact absurd hct' (Set.disjoint_left.mp hdis hct)⟩

/-- Every cell is nonempty.
    HOL Light: `cell_nonempty` (line 3205). -/
theorem cell_nonempty {C : Set E2} (h : isCell C) : C.Nonempty := by
  obtain ⟨ct, rfl⟩ := h
  match ct with
  | .point m => exact ⟨pointI m, mem_singleton_iff.mpr rfl⟩
  | .hEdge m => exact hEdge_nonempty m
  | .vEdge m => exact vEdge_nonempty m
  | .squ m   => exact squ_nonempty m

/-! ## Topology on ℝ² -/

-- `top2` in HOL Light is `top_of_metric (euclid 2, d_euclid)`.
-- In Lean/Mathlib this is the standard `TopologicalSpace` instance on
-- `EuclideanSpace ℝ (Fin 2)`, so no definition needed.

/-! ## Adjacency -/

/-- Two cells are adjacent if they are distinct and their closures intersect.
    HOL Light: `adj X Y` (line 2091). -/
def cellAdj (X Y : Set E2) : Prop :=
  isCell X ∧ isCell Y ∧ X ≠ Y ∧ (closure X ∩ closure Y).Nonempty

-- HOL Light: `adj_symm` (line 2097).
/-- Cell adjacency is symmetric: `X` is adjacent to `Y` iff `Y` is adjacent to `X`.
    HOL Light: `adj_symm` (line 2097). -/
theorem cellAdj_symm {X Y : Set E2} :
    cellAdj X Y ↔ cellAdj Y X := by
  unfold cellAdj
  constructor
  · rintro ⟨hX, hY, hne, hI⟩
    exact ⟨hY, hX, hne.symm, by rwa [Set.inter_comm]⟩
  · rintro ⟨hY, hX, hne, hI⟩
    exact ⟨hX, hY, hne.symm, by rwa [Set.inter_comm]⟩

-- HOL Light: `adj_irrefl` (line 2108).
/-- Cell adjacency is irreflexive: no cell is adjacent to itself.
    HOL Light: `adj_irrefl` (line 2108). -/
theorem cellAdj_irrefl (X : Set E2) :
    ¬cellAdj X X :=
  fun ⟨_, _, hne, _⟩ => hne rfl

-- The adjacency proofs require closure computations (closure_hEdge etc.)
-- which are established in Section B. The concrete adjacency theorems
-- (hEdge_adj_left, hEdge_adj_right, hEdge_adj_squ_above, etc.) are
-- stated and proved in SectionB_CellTopology.lean where the closure
-- results are available.

/-! ## Edges (union of horizontal and vertical edges) -/

/-- A set is an edge if it is a horizontal or vertical unit edge.
    HOL Light: `edge C` (line 3120). -/
def isEdge (C : Set E2) : Prop :=
  (∃ m, C = hEdge m) ∨ (∃ m, C = vEdge m)

/-- Every edge (horizontal or vertical) is a cell.
    HOL Light: `edge C` implies `cell C` (line 3120). -/
theorem isEdge_isCell {C : Set E2} (h : isEdge C) : isCell C := by
  cases h with
  | inl h => obtain ⟨m, hm⟩ := h; exact ⟨.hEdge m, hm⟩
  | inr h => obtain ⟨m, hm⟩ := h; exact ⟨.vEdge m, hm⟩

/-! ## Num closure (number of incident edges at a lattice point) -/

/-- The set of edges in `G` incident to lattice point `m` (whose closure
    contains `pointI m`).
    HOL Light: used inside `num_closure`. -/
def incidentEdges (G : Finset (Set E2)) (m : ℤ × ℤ) : Finset (Set E2) :=
  @Finset.filter _ (fun e => pointI m ∈ closure e) (Classical.decPred _) G

/-- The number of edges in `G` incident to `pointI m`.
    HOL Light: `num_closure G x` (line 3138). -/
def numClosure (G : Finset (Set E2)) (m : ℤ × ℤ) : ℕ :=
  (incidentEdges G m).card

-- numClosure_le_four and incident_edges_characterize require closure
-- computations from Section B. They are stated and proved in
-- SectionB_CellTopology.lean alongside the adjacency theorems.

/-! ## Num lower (for parity counting) -/

/-- The number of horizontal edges in `G` at column `m.1` at or below
    row `m.2`. Used for parity classification.
    HOL Light: `num_lower G n` (line 3141).
    This definition takes a `Finset` of edges for computability.
    The `Rectagon`-specific version is in SectionE_Parity. -/
noncomputable def numLower (G : Finset (Set E2)) (m : ℤ × ℤ) : ℕ :=
  @Finset.card _ (@Finset.filter _ (fun e => ∃ k : ℤ, k ≤ m.2 ∧ e = hEdge (m.1, k))
    (Classical.decPred _) G)

/-! ## Lattice navigation -/

/-- Move one step up in the grid.
    HOL Light: `up` (line 3349). -/
def up (m : ℤ × ℤ) : ℤ × ℤ := (m.1, m.2 + 1)

/-- Move one step down in the grid.
    HOL Light: `down` (line 3346). -/
def down (m : ℤ × ℤ) : ℤ × ℤ := (m.1, m.2 - 1)

/-- Move one step left in the grid.
    HOL Light: `left` (line 3347). -/
def left (m : ℤ × ℤ) : ℤ × ℤ := (m.1 - 1, m.2)

/-- Move one step right in the grid.
    HOL Light: `right` (line 3348). -/
def right (m : ℤ × ℤ) : ℤ × ℤ := (m.1 + 1, m.2)

/-! ## Set lower and parity -/

/-- The set of integer points m' with hEdge m' in G, same column as n,
    and row at or below n.2. Used for parity counting.
    HOL Light: `set_lower` (line 3144). -/
def setLower (G : Finset (Set E2)) (n : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {m | hEdge m ∈ G ∧ m.1 = n.1 ∧ m.2 ≤ n.2}

/-- A cell has even parity w.r.t. an edge set G if its numLower is even.
    HOL Light: `even_cell` (line 3155). -/
def evenCell (G : Finset (Set E2)) (C : Set E2) : Prop :=
  ∃ m : ℤ × ℤ, (C = ({pointI m} : Set E2) ∨ C = hEdge m ∨ C = vEdge m ∨ C = squ m) ∧
    Even (numLower G m)

end
