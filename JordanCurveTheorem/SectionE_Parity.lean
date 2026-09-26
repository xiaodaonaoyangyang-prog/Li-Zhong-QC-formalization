/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionD_SegmentInduction

/-!
# Section E: Parity and Curve Cells
## HOL Light: Section E (Lines 7357–9412)

The core combinatorial machinery: rectangles, curve cells, the parity
classification `par_cell`, the induced topology `ctop` on the complement
of a rectagon, and openness/connectivity of parity regions. This is the
**combinatorial heart** of the Jordan property for grid curves.

### Key HOL Light definitions
- `rectangle` (line 7361): Open rectangle between grid points
- `curve_cell` (line 7825): Edges of G plus midpoint singletons
- `par_cell` (line 8083): Parity cell classification
- `ctop` (line 8463): Induced topology on complement of curve cells
- `cell_of` (line 9359): Cells contained in a given set

### Key HOL Light theorems
- `rectangle_open` (line 7390): Rectangles are open in `top2`
- `rectangle_convex` (line 7398): Rectangles are convex
- `rectangle_h/v` (line 7506/7580): Rectangles decompose into edges+squares
- `curve_closure` (line 7905): closure(⋃G) = ⋃(curve_cell G)
- `par_cell_squ` (line 8134): par_cell eps G (squ m) ↔ eps = Even(numLower G m)
- `par_cell_disjoint` (line 8190): par_cell eps ∩ par_cell ¬eps = ∅
- `par_cell_nonempty` (line 8230): Both parity regions are nonempty
- `par_cell_partition` (line 8280): Parity regions partition ctop
- `par_cell_open` (line 8520): Parity regions are open in ctop
- `par_cell_comp` (line 8620): Connected components stay in one parity
- `convex_connected/component` (line 8710/8780): Convexity → connectivity
- `unions_cell_of` (line 9370): Cells of a component cover it
-/

open Set Topology

noncomputable section

/-! ## Rectangles -/

/-- Open rectangle between grid points `p` and `q`.
    HOL Light: `rectangle p q` (line 7361). -/
def rectangle (p q : ℤ × ℤ) : Set E2 :=
  {z | z 0 > (↑p.1 : ℝ) ∧ z 0 < ↑q.1 ∧ z 1 > (↑p.2 : ℝ) ∧ z 1 < ↑q.2}

/-- Rectangles are open in the Euclidean topology.
    HOL Light: `rectangle_open` (line 7390). -/
theorem rectangle_isOpen (p q : ℤ × ℤ) : IsOpen (rectangle p q) := by
  have hc0 : Continuous (fun z : E2 => z 0) := by fun_prop
  have hc1 : Continuous (fun z : E2 => z 1) := by fun_prop
  have : rectangle p q = {z : E2 | (↑p.1 : ℝ) < z 0} ∩ {z | z 0 < ↑q.1} ∩
      {z | (↑p.2 : ℝ) < z 1} ∩ {z | z 1 < ↑q.2} := by
    ext z; simp only [rectangle, mem_inter_iff, mem_setOf_eq]; tauto
  rw [this]
  exact ((isOpen_lt continuous_const hc0).inter
    (isOpen_lt hc0 continuous_const)).inter
    (isOpen_lt continuous_const hc1) |>.inter (isOpen_lt hc1 continuous_const)

/-- Rectangles are convex.
    HOL Light: `rectangle_convex` (line 7398). -/
theorem rectangle_convex (p q : ℤ × ℤ) : Convex ℝ (rectangle p q) := by
  intro x hx y hy a b ha hb hab
  simp only [rectangle, mem_setOf_eq] at *
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have coord : ∀ i : Fin 2,
      (a • x + b • y) i = a * (x i) + b * (y i) := fun i => by
    show (a • x + b • y).ofLp i = a * x.ofLp i + b * y.ofLp i
    simp [
      smul_eq_mul]
  rw [coord 0, coord 1]
  have auxgt : ∀ u v c : ℝ, u > c → v > c → a * u + b * v > c := by
    intro u v c hu hv
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab; subst hab; simpa
    · have h1 : a * c < a * u := by nlinarith
      have h2 : b * c ≤ b * v := by nlinarith
      have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith
  have auxlt : ∀ u v c : ℝ, u < c → v < c → a * u + b * v < c := by
    intro u v c hu hv
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab; subst hab; simpa
    · have h1 : a * u < a * c := by nlinarith
      have h2 : b * v ≤ b * c := by nlinarith
      have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith
  exact ⟨auxgt _ _ _ hx1 hy1, auxlt _ _ _ hx2 hy2,
         auxgt _ _ _ hx3 hy3, auxlt _ _ _ hx4 hy4⟩

/-- `squ m` is a rectangle.
    HOL Light: `rectangle_squ` (line 7403). -/
theorem squ_eq_rectangle (m : ℤ × ℤ) :
    squ m = rectangle m (m.1 + 1, m.2 + 1) := by
  ext z; simp only [squ, rectangle, mem_setOf_eq]; push_cast; tauto

/-- A rectangle decomposes horizontally into squ(down p) ∪ hEdge(p) ∪ squ(p).
    HOL Light: `rectangle_h` (line 7506). -/
theorem rectangle_h_decomp (p : ℤ × ℤ) :
    rectangle (p.1, p.2 - 1) (p.1 + 1, p.2 + 1) =
      squ (down p) ∪ hEdge p ∪ squ p := by
  ext z; simp only [rectangle, squ, hEdge, down, mem_setOf_eq, mem_union]; push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases lt_trichotomy (z 1) (↑p.2 : ℝ) with hlt | heq | hgt
    · left; left; exact ⟨h1, h2, h3, by linarith⟩
    · exact Or.inl (Or.inr ⟨h1, h2, heq⟩)
    · exact Or.inr ⟨h1, h2, hgt, h4⟩
  · rintro ((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, h3, by linarith⟩
    · exact ⟨h1, h2, by linarith, by linarith⟩
    · exact ⟨h1, h2, by linarith, h4⟩

/-- A rectangle decomposes vertically into squ(left p) ∪ vEdge(p) ∪ squ(p).
    HOL Light: `rectangle_v` (line 7580). -/
theorem rectangle_v_decomp (p : ℤ × ℤ) :
    rectangle (p.1 - 1, p.2) (p.1 + 1, p.2 + 1) =
      squ (left p) ∪ vEdge p ∪ squ p := by
  ext z; simp only [rectangle, squ, vEdge, left, mem_setOf_eq, mem_union]; push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases lt_trichotomy (z 0) (↑p.1 : ℝ) with hlt | heq | hgt
    · left; left; exact ⟨h1, by linarith, h3, h4⟩
    · left; right; exact ⟨heq, h3, h4⟩
    · right; exact ⟨hgt, h2, h3, h4⟩
  · rintro ((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, by linarith, h3, h4⟩
    · exact ⟨by linarith, by linarith, h2, h3⟩
    · exact ⟨by linarith, h2, h3, h4⟩

/-- The 2×2 rectangle decomposes into 4 squares, 4 edges, and 1 point.
    HOL Light: `two_two_nine` (line 7730). -/
theorem two_two_nine (p : ℤ × ℤ) :
    rectangle (p.1 - 1, p.2 - 1) (p.1 + 1, p.2 + 1) =
      squ (p.1 - 1, p.2 - 1) ∪ squ (p.1 - 1, p.2) ∪
      squ (p.1, p.2 - 1) ∪ squ p ∪
      hEdge (left p) ∪ hEdge p ∪
      vEdge (down p) ∪ vEdge p ∪ {pointI p} := by
  ext z; simp only [rectangle, squ, hEdge, vEdge, left, down,
    mem_setOf_eq, mem_union, mem_singleton_iff]; push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases lt_trichotomy (z 0) (↑p.1 : ℝ) with hx_lt | hx_eq | hx_gt
    · rcases lt_trichotomy (z 1) (↑p.2 : ℝ) with hy_lt | hy_eq | hy_gt
      · left; left; left; left; left; left; left; left
        exact ⟨h1, by linarith, h3, by linarith⟩
      · left; left; left; left; right
        exact ⟨h1, by linarith, hy_eq⟩
      · left; left; left; left; left; left; left; right
        exact ⟨h1, by linarith, hy_gt, h4⟩
    · rcases lt_trichotomy (z 1) (↑p.2 : ℝ) with hy_lt | hy_eq | hy_gt
      · left; left; right; exact ⟨hx_eq, h3, by linarith⟩
      · right; show z = pointI p
        ext i; fin_cases i <;>
          simp only [pointI_coord_fst, pointI_coord_snd, Fin.zero_eta, Fin.mk_one,
            Fin.isValue] <;> assumption
      · left; right; exact ⟨hx_eq, hy_gt, h4⟩
    · rcases lt_trichotomy (z 1) (↑p.2 : ℝ) with hy_lt | hy_eq | hy_gt
      · left; left; left; left; left; left; right
        exact ⟨hx_gt, h2, h3, by linarith⟩
      · left; left; left; right; exact ⟨hx_gt, h2, hy_eq⟩
      · left; left; left; left; left; right
        exact ⟨hx_gt, h2, hy_gt, h4⟩
  · intro h
    rcases h with (((((((h|h)|h)|h)|h)|h)|h)|h)|h
    <;> first
      | (obtain ⟨_,_,_,_⟩ := h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
      | (obtain ⟨_,_,_⟩ := h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
      | (subst h; simp only [pointI_coord_fst, pointI_coord_snd]
         exact ⟨by linarith, by linarith, by linarith, by linarith⟩)

/-! ## Curve cells -/

/-- The set of cells that a segment passes through: the edges themselves
    plus the singleton lattice point cells at vertices in the closure.
    HOL Light: `curve_cell G` (line 7825). -/
def curveCells (G : Finset (Set E2)) : Set (Set E2) :=
  ↑G ∪ {C | ∃ m : ℤ × ℤ, C = {pointI m} ∧ pointI m ∈ closure (⋃₀ ↑G)}

/-- Curve cells are cells.
    HOL Light: `curve_cell_cell` (line 7835). -/
theorem curveCells_subset_cell (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    ∀ C ∈ curveCells G, isCell C := by
  intro C hC
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hC
  rcases hC with h | ⟨m, rfl, -⟩
  · exact isEdge_isCell (hG C h)
  · exact ⟨.point m, rfl⟩

/-- `curve_cell G (h_edge m) = G (h_edge m)` for segments.
    HOL Light: `curve_cell_h` (line 7855). -/
theorem curveCells_hEdge (G : Segment) (m : ℤ × ℤ) :
    hEdge m ∈ curveCells G.edges ↔ hEdge m ∈ G.edges := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro (h | ⟨n, heq, -⟩)
    · exact h
    · exact absurd heq (hEdge_ne_pointI_set m n)
  · exact Or.inl

/-- `curve_cell G (v_edge m) = G (v_edge m)` for segments.
    HOL Light: `curve_cell_v` (line 7870). -/
theorem curveCells_vEdge (G : Segment) (m : ℤ × ℤ) :
    vEdge m ∈ curveCells G.edges ↔ vEdge m ∈ G.edges := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro (h | ⟨n, heq, -⟩)
    · exact h
    · exact absurd heq (vEdge_ne_pointI_set m n)
  · exact Or.inl

/-- Squares are never curve cells.
    HOL Light: `curve_cell_squ` (line 7898). -/
theorem curveCells_not_squ (G : Segment) (m : ℤ × ℤ) :
    squ m ∉ curveCells G.edges := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq, not_or]
  constructor
  · intro hmem
    have := G.all_edges (squ m) hmem
    rcases this with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact absurd hn (squ_ne_hEdge m n)
    · exact absurd hn (squ_ne_vEdge m n)
  · push Not; intro n heq; exact absurd heq (squ_ne_pointI_set m n)

/-- `closure(⋃G) = ⋃(curve_cell G)` for segments.
    HOL Light: `curve_closure` (line 7905). -/
theorem curve_closure (G : Segment) :
    closure (⋃₀ ↑G.edges) = ⋃₀ (curveCells G.edges) := by
  apply subset_antisymm
  · -- ⊆: closure(⋃₀ edges) ⊆ ⋃₀ curveCells
    rw [((↑G.edges : Set (Set E2)).toFinite).closure_sUnion]
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨e, he, hze⟩ := hz
    rcases G.all_edges e he with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- e = hEdge m
      rw [closure_hEdge] at hze
      obtain ⟨h1, h2, h3⟩ := hze
      rcases eq_or_lt_of_le h1 with h1eq | h1lt
      · -- z 0 = ↑m.1: left endpoint pointI m
        have : z = pointI m := by
          ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
        subst this
        exact mem_sUnion.mpr ⟨{pointI m}, mem_union_right _ ⟨m, rfl,
          closure_mono (subset_sUnion_of_mem he)
            ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)⟩, rfl⟩
      · rcases lt_or_eq_of_le h2 with h2lt | h2eq
        · -- interior of hEdge m
          exact mem_sUnion.mpr ⟨hEdge m, mem_union_left _ he, h1lt, h2lt, h3⟩
        · -- z 0 = ↑m.1 + 1: right endpoint pointI (m.1+1, m.2)
          have : z = pointI (m.1 + 1, m.2) := by
            ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
          subst this
          exact mem_sUnion.mpr ⟨{pointI (m.1 + 1, m.2)},
            mem_union_right _ ⟨(m.1 + 1, m.2), rfl,
              closure_mono (subset_sUnion_of_mem he)
                ((pointI_mem_closure_hEdge (m.1 + 1, m.2) m).mpr
                  ⟨rfl, Or.inr rfl⟩)⟩, rfl⟩
    · -- e = vEdge m
      rw [closure_vEdge] at hze
      obtain ⟨h1, h2, h3⟩ := hze
      rcases eq_or_lt_of_le h2 with h2eq | h2lt
      · -- z 1 = ↑m.2: bottom endpoint pointI m
        have : z = pointI m := by
          ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
        subst this
        exact mem_sUnion.mpr ⟨{pointI m}, mem_union_right _ ⟨m, rfl,
          closure_mono (subset_sUnion_of_mem he)
            ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)⟩, rfl⟩
      · rcases lt_or_eq_of_le h3 with h3lt | h3eq
        · -- interior of vEdge m
          exact mem_sUnion.mpr ⟨vEdge m, mem_union_left _ he, h1, h2lt, h3lt⟩
        · -- z 1 = ↑m.2 + 1: top endpoint pointI (m.1, m.2+1)
          have : z = pointI (m.1, m.2 + 1) := by
            ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
          subst this
          exact mem_sUnion.mpr ⟨{pointI (m.1, m.2 + 1)},
            mem_union_right _ ⟨(m.1, m.2 + 1), rfl,
              closure_mono (subset_sUnion_of_mem he)
                ((pointI_mem_closure_vEdge (m.1, m.2 + 1) m).mpr
                  ⟨rfl, Or.inr rfl⟩)⟩, rfl⟩
  · -- ⊇: ⋃₀ curveCells ⊆ closure(⋃₀ edges)
    intro z hz
    rw [mem_sUnion] at hz
    obtain ⟨C, hC, hzC⟩ := hz
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hC
    rcases hC with hCG | ⟨m, rfl, hm⟩
    · exact subset_closure (mem_sUnion.mpr ⟨C, hCG, hzC⟩)
    · rw [mem_singleton_iff] at hzC; subst hzC; exact hm

/-- The curve of a segment is closed.
    HOL Light: `curve_closed` (line 8470). -/
theorem curve_closed (G : Segment) :
    IsClosed (⋃₀ (curveCells G.edges)) := by
  rw [← curve_closure G]; exact isClosed_closure

/-! ## Parity cell classification -/

/-- The parity of a cell relative to a segment: `par_cell eps G C` holds
    when `C` is a cell with `numLower G m` having the right parity,
    AND `C` doesn't intersect the curve.
    HOL Light: `par_cell eps G C` (line 8083). -/
def parCell (eps : Bool) (G : Finset (Set E2)) (C : Set E2) : Prop :=
  (∃ m : ℤ × ℤ,
    (C = {pointI m} ∨ C = hEdge m ∨ C = vEdge m ∨ C = squ m) ∧
    eps = decide (Even (numLower G m))) ∧
  C ∩ ⋃₀ (curveCells G) = ∅

/-- `par_cell` for squares simplifies to a parity check.
    HOL Light: `par_cell_squ` (line 8134). -/
theorem parCell_squ (G : Segment) (m : ℤ × ℤ) (eps : Bool) :
    parCell eps G.edges (squ m) ↔ eps = decide (Even (numLower G.edges m)) := by
  unfold parCell
  constructor
  · rintro ⟨⟨n, hcell, heps⟩, _⟩
    rcases hcell with heq | heq | heq | heq
    · exact absurd heq (squ_ne_pointI_set m n)
    · exact absurd heq (squ_ne_hEdge m n)
    · exact absurd heq (squ_ne_vEdge m n)
    · rw [(squ_inj m n).mp heq]; exact heps
  · intro h
    refine ⟨⟨m, Or.inr (Or.inr (Or.inr rfl)), h⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz_squ, hz_curve⟩
    rw [Set.mem_sUnion] at hz_curve
    obtain ⟨S, hS_mem, hz_S⟩ := hz_curve
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS_mem
    rcases hS_mem with hS_G | ⟨k, rfl, _⟩
    · rcases G.all_edges S hS_G with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · exact Set.disjoint_left.mp
          (cell_disjoint (show CellType.squ m ≠ CellType.hEdge p from nofun)) hz_squ hz_S
      · exact Set.disjoint_left.mp
          (cell_disjoint (show CellType.squ m ≠ CellType.vEdge p from nofun)) hz_squ hz_S
    · rw [mem_singleton_iff] at hz_S; exact squ_not_pointI m k (hz_S ▸ hz_squ)

/-- `par_cell` for h-edges requires the edge to NOT be in G.
    HOL Light: `par_cell_h` (line 8100). -/
theorem parCell_hEdge (G : Segment) (m : ℤ × ℤ) (eps : Bool) :
    parCell eps G.edges (hEdge m) ↔
      hEdge m ∉ G.edges ∧ eps = decide (Even (numLower G.edges m)) := by
  unfold parCell
  constructor
  · rintro ⟨⟨n, hcell, heps⟩, hdis⟩
    rcases hcell with heq | heq | heq | heq
    · exact absurd heq.symm (hEdge_ne_pointI_set m n).symm
    · have hmn := (hEdge_inj m n).mp heq
      constructor
      · intro hmem
        have hcc : hEdge m ∈ (curveCells G.edges : Set (Set E2)) := by
          simp only [curveCells, mem_union, Finset.mem_coe]; exact Or.inl hmem
        have ⟨z, hz⟩ := hEdge_nonempty m
        have : z ∈ hEdge m ∩ ⋃₀ curveCells G.edges :=
          ⟨hz, Set.mem_sUnion.mpr ⟨hEdge m, hcc, hz⟩⟩
        rw [hdis] at this; exact this
      · rw [hmn]; exact heps
    · exact absurd heq (hEdge_ne_vEdge m n)
    · exact absurd heq.symm (squ_ne_hEdge n m)
  · rintro ⟨hnotG, heps⟩
    refine ⟨⟨m, Or.inr (Or.inl rfl), heps⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz_h, hz_curve⟩
    rw [Set.mem_sUnion] at hz_curve
    obtain ⟨S, hS_mem, hz_S⟩ := hz_curve
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS_mem
    rcases hS_mem with hS_G | ⟨k, rfl, _⟩
    · rcases G.all_edges S hS_G with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · by_cases heq : m = p
        · exact hnotG (heq ▸ hS_G)
        · exact Set.disjoint_left.mp (cell_disjoint (show CellType.hEdge m ≠ CellType.hEdge p from
            fun h => heq (CellType.hEdge.inj h))) hz_h hz_S
      · exact Set.disjoint_left.mp
          (cell_disjoint (show CellType.hEdge m ≠ CellType.vEdge p from nofun)) hz_h hz_S
    · rw [mem_singleton_iff] at hz_S; exact hEdge_not_pointI m k (hz_S ▸ hz_h)

/-- `par_cell` for v-edges requires the edge to NOT be in G.
    HOL Light: `par_cell_v` (line 8117). -/
theorem parCell_vEdge (G : Segment) (m : ℤ × ℤ) (eps : Bool) :
    parCell eps G.edges (vEdge m) ↔
      vEdge m ∉ G.edges ∧ eps = decide (Even (numLower G.edges m)) := by
  unfold parCell
  constructor
  · rintro ⟨⟨n, hcell, heps⟩, hdis⟩
    rcases hcell with heq | heq | heq | heq
    · exact absurd heq.symm (vEdge_ne_pointI_set m n).symm
    · exact absurd heq.symm (hEdge_ne_vEdge n m)
    · have hmn := (vEdge_inj m n).mp heq
      constructor
      · intro hmem
        have hcc : vEdge m ∈ (curveCells G.edges : Set (Set E2)) := by
          simp only [curveCells, mem_union, Finset.mem_coe]; exact Or.inl hmem
        have ⟨z, hz⟩ := vEdge_nonempty m
        have : z ∈ vEdge m ∩ ⋃₀ curveCells G.edges :=
          ⟨hz, Set.mem_sUnion.mpr ⟨vEdge m, hcc, hz⟩⟩
        rw [hdis] at this; exact this
      · rw [hmn]; exact heps
    · exact absurd heq.symm (squ_ne_vEdge n m)
  · rintro ⟨hnotG, heps⟩
    refine ⟨⟨m, Or.inr (Or.inr (Or.inl rfl)), heps⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz_v, hz_curve⟩
    rw [Set.mem_sUnion] at hz_curve
    obtain ⟨S, hS_mem, hz_S⟩ := hz_curve
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS_mem
    rcases hS_mem with hS_G | ⟨k, rfl, _⟩
    · rcases G.all_edges S hS_G with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · exact Set.disjoint_left.mp
          (cell_disjoint (show CellType.vEdge m ≠ CellType.hEdge p from nofun)) hz_v hz_S
      · by_cases heq : m = p
        · exact hnotG (heq ▸ hS_G)
        · exact Set.disjoint_left.mp (cell_disjoint (show CellType.vEdge m ≠ CellType.vEdge p from
            fun h => heq (CellType.vEdge.inj h))) hz_v hz_S
    · rw [mem_singleton_iff] at hz_S; exact vEdge_not_pointI m k (hz_S ▸ hz_v)

/-- `par_cell` for singleton points requires numClosure = 0.
    HOL Light: `par_cell_point` (line 8160). -/
theorem parCell_point (G : Segment) (m : ℤ × ℤ) (eps : Bool) :
    parCell eps G.edges ({pointI m}) ↔
      numClosure G.edges m = 0 ∧ eps = decide (Even (numLower G.edges m)) := by
  unfold parCell
  constructor
  · rintro ⟨⟨n, hcell, heps⟩, hdis⟩
    rcases hcell with heq | heq | heq | heq
    · have hmn := pointI_injective (Set.singleton_eq_singleton_iff.mp heq)
      constructor
      · -- numClosure = 0: pointI m is not in any curve cell
        rw [numClosure, incidentEdges, Finset.card_eq_zero]; ext e
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro he hcl
        have : pointI m ∈ ({pointI m} : Set E2) ∩ ⋃₀ curveCells G.edges := by
          refine ⟨rfl, Set.mem_sUnion.mpr ?_⟩
          exact ⟨{pointI m}, Or.inr ⟨m, rfl, by
            rw [((↑G.edges : Set (Set E2)).toFinite).closure_sUnion, Set.mem_iUnion₂]
            exact ⟨e, he, hcl⟩⟩, rfl⟩
        rw [hdis] at this; exact this
      · rw [hmn]; exact heps
    · exact absurd heq.symm (hEdge_ne_pointI_set n m)
    · exact absurd heq.symm (vEdge_ne_pointI_set n m)
    · exact absurd heq.symm (squ_ne_pointI_set n m)
  · rintro ⟨hnum, heps⟩
    refine ⟨⟨m, Or.inl rfl, heps⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz_pt, hz_curve⟩
    rw [mem_singleton_iff] at hz_pt; subst hz_pt
    rw [Set.mem_sUnion] at hz_curve
    obtain ⟨S, hS_mem, hz_S⟩ := hz_curve
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS_mem
    rcases hS_mem with hS_G | ⟨k, rfl, _⟩
    · rcases G.all_edges S hS_G with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · exact hEdge_not_pointI p m hz_S
      · exact vEdge_not_pointI p m hz_S
    · rw [mem_singleton_iff] at hz_S
      have hkm := pointI_injective hz_S; subst hkm
      rw [numClosure, incidentEdges, Finset.card_eq_zero] at hnum
      rename_i h
      rw [((↑G.edges : Set (Set E2)).toFinite).closure_sUnion, Set.mem_iUnion₂] at h
      obtain ⟨e, he, hcl⟩ := h
      have : e ∈ @Finset.filter _ (fun e => pointI m ∈ closure e)
          (Classical.decPred _) G.edges := by
        simp only [Finset.mem_filter]; exact ⟨he, hcl⟩
      rw [hnum] at this; exact absurd this (by simp)

/-- The two parity classes are disjoint.
    HOL Light: `par_cell_disjoint` (line 8190). -/
theorem parCell_disjoint (G : Finset (Set E2)) (eps : Bool) (C : Set E2) :
    ¬(parCell eps G C ∧ parCell (!eps) G C) := by
  rintro ⟨⟨⟨m, hcell_m, hm⟩, _⟩, ⟨⟨n, hcell_n, hn⟩, _⟩⟩
  have hne : eps ≠ !eps := by cases eps <;> simp
  suffices m = n by subst this; exact hne (hm.trans hn.symm)
  rcases hcell_m with rfl | rfl | rfl | rfl <;> rcases hcell_n with h | h | h | h
  <;> first
    | exact pointI_injective (Set.singleton_eq_singleton_iff.mp h)
    | exact (hEdge_inj m n).mp h
    | exact (vEdge_inj m n).mp h
    | exact (squ_inj m n).mp h
    | exact absurd h (hEdge_ne_pointI_set m n)
    | exact absurd h (vEdge_ne_pointI_set m n)
    | exact absurd h (squ_ne_pointI_set m n)
    | exact absurd h.symm (hEdge_ne_pointI_set n m)
    | exact absurd h.symm (vEdge_ne_pointI_set n m)
    | exact absurd h.symm (squ_ne_pointI_set n m)
    | exact absurd h (hEdge_ne_vEdge m n)
    | exact absurd h.symm (hEdge_ne_vEdge n m)
    | exact absurd h (squ_ne_hEdge m n)
    | exact absurd h.symm (squ_ne_hEdge n m)
    | exact absurd h (squ_ne_vEdge m n)
    | exact absurd h.symm (squ_ne_vEdge n m)

/-- Both parity regions are nonempty for rectagons.
    HOL Light: `par_cell_nonempty` (line 8230). -/
theorem parCell_nonempty (R : Rectagon) (eps : Bool) :
    ∃ C, parCell eps R.edges C := by
  obtain ⟨e, he⟩ := R.nonempty
  rcases R.all_edges e he with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- hEdge m ∈ R.edges: squ m and squ (down m) have opposite parities
    by_cases h : eps = decide (Even (numLower R.edges m))
    · exact ⟨squ m, (parCell_squ R.toSegment m eps).mpr h⟩
    · refine ⟨squ (down m), (parCell_squ R.toSegment (down m) eps).mpr ?_⟩
      have hstep := numLower_step R.edges m.1 m.2
      simp only [down, Prod.mk.eta] at hstep ⊢
      rw [hstep, if_pos he] at h
      cases eps <;>
        simp only [Nat.even_add_one, Nat.not_even_iff_odd, false_eq_decide_iff,
          Nat.not_odd_iff_even, true_eq_decide_iff] at h ⊢ <;>
        first
          | exact h
          | exact decide_eq_false (Nat.not_even_iff_odd.mpr h)
          | exact decide_eq_true h
          | exact (decide_eq_false (Nat.not_even_iff_odd.mpr h)).symm
          | exact (decide_eq_true h).symm
  · -- vEdge m ∈ R.edges: squ m and squ (left m) have opposite parities
    by_cases h : eps = decide (Even (numLower R.edges m))
    · exact ⟨squ m, (parCell_squ R.toSegment m eps).mpr h⟩
    · refine ⟨squ (left m), (parCell_squ R.toSegment (left m) eps).mpr ?_⟩
      have hopp := squ_left_odd R m he
      rw [even_cell_squ, even_cell_squ] at hopp
      change eps = decide (Even (numLower R.edges (left m)))
      by_cases hm : Even (numLower R.edges m)
      · have : ¬Even (numLower R.edges (left m)) :=
          fun h' => hopp ⟨fun _ => hm, fun _ => h'⟩
        cases eps <;> simp_all
      · have : Even (numLower R.edges (left m)) := by
          by_contra h'; exact hopp ⟨fun hx => absurd hx h', fun hx => absurd hx hm⟩
        cases eps <;> simp_all

/-! ## Parity propagation across edges -/

/-- A non-curve h-edge has the same parity as its two adjacent squares.
    HOL Light: `par_cell_h_squ` (line 8334). -/
theorem parCell_hEdge_squ (G : Segment) (m : ℤ × ℤ) (eps : Bool)
    (h : parCell eps G.edges (hEdge m)) :
    parCell eps G.edges (squ m) ∧ parCell eps G.edges (squ (down m)) := by
  rw [parCell_hEdge] at h
  obtain ⟨hnotG, heps⟩ := h
  constructor
  · rw [parCell_squ]; exact heps
  · rw [parCell_squ]
    -- numLower G m = numLower G (down m) since hEdge m ∉ G
    suffices heq : numLower G.edges m = numLower G.edges (down m) by
      rw [heq] at heps; exact heps
    simp only [numLower, down]
    refine congrArg Finset.card ?_
    classical
    ext e
    constructor
    · intro hx
      obtain ⟨he, k, hk, rfl⟩ := Finset.mem_filter.mp hx
      by_cases hkm : k = m.2
      · subst hkm; exact absurd he hnotG
      · exact Finset.mem_filter.mpr ⟨he, k, by omega, rfl⟩
    · intro hx
      obtain ⟨he, k, hk, rfl⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨he, k, by omega, rfl⟩

/-- A non-curve v-edge of a rectagon has the same parity as its two adjacent squares.
    HOL Light: `par_cell_v_squ` (line 8347). -/
theorem parCell_vEdge_squ (R : Rectagon) (m : ℤ × ℤ) (eps : Bool)
    (h : parCell eps R.edges (vEdge m)) :
    parCell eps R.edges (squ m) ∧ parCell eps R.edges (squ (left m)) := by
  have : parCell eps R.toSegment.edges (vEdge m) := h
  rw [parCell_vEdge] at this
  obtain ⟨hnotG, heps⟩ := this
  constructor
  · exact (parCell_squ R.toSegment m eps).mpr heps
  · apply (parCell_squ R.toSegment (left m) eps).mpr
    have hleft := squ_left_even R m hnotG
    rw [even_cell_squ, even_cell_squ] at hleft
    rw [heps]; congr 1; exact propext hleft.symm

/-- A non-curve lattice point of a rectagon has the same parity as
    its adjacent h-edges.
    HOL Light: `par_cell_point_h` (line 8420). -/
theorem parCell_point_hEdge (R : Rectagon) (m : ℤ × ℤ) (eps : Bool)
    (h : parCell eps R.edges ({pointI m})) :
    parCell eps R.edges (hEdge m) ∧ parCell eps R.edges (hEdge (left m)) := by
  have hp : parCell eps R.toSegment.edges ({pointI m}) := h
  rw [parCell_point] at hp
  obtain ⟨hnum, heps⟩ := hp
  rw [numClosure_eq_zero_iff] at hnum
  have hh : hEdge m ∉ R.edges := fun hmem =>
    hnum _ hmem ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
  have hhl : hEdge (left m) ∉ R.edges := fun hmem =>
    hnum _ hmem ((pointI_mem_closure_hEdge m (left m)).mpr
      ⟨rfl, Or.inr (by simp [left])⟩)
  have hv : vEdge m ∉ R.edges := fun hmem =>
    hnum _ hmem ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
  constructor
  · exact (parCell_hEdge R.toSegment m eps).mpr ⟨hh, heps⟩
  · apply (parCell_hEdge R.toSegment (left m) eps).mpr
    refine ⟨hhl, ?_⟩
    have hleft := squ_left_even R m hv
    rw [even_cell_squ, even_cell_squ] at hleft
    rw [heps]; congr 1; exact propext hleft.symm

/-! ## The complement of the curve -/

/-- The complement of the curve cells — the "carrier" of ctop.
    HOL Light: `UNIONS(ctop G) = euclid 2 DIFF UNIONS(curve_cell G)`. -/
def complementCurve (G : Finset (Set E2)) : Set E2 :=
  (⋃₀ (curveCells G : Set (Set E2)))ᶜ

/-- The parity regions are open in the standard topology.
    HOL Light: `par_cell_open` (line 8520). -/
theorem parCell_open (R : Rectagon) (eps : Bool) :
    IsOpen (⋃₀ {C | parCell eps R.edges C}) := by
  rw [isOpen_iff_forall_mem_open]
  intro z ⟨C, hC, hzC⟩
  -- Reconstruct the cell type info while keeping hC intact
  have ⟨⟨m, hcell, heps⟩, hdis⟩ := hC
  rcases hcell with rfl | rfl | rfl | rfl
  · -- C = {pointI m}
    have hp := parCell_point_hEdge R m eps hC
    have hh_r := parCell_hEdge_squ R.toSegment m eps hp.1
    have hh_l := parCell_hEdge_squ R.toSegment (left m) eps hp.2
    -- Need vEdge parities. Get them from the squares via parCell_vEdge_squ.
    -- squ m has parCell eps (from hh_r.1). squ (left m) has parCell eps (from hh_l.1).
    -- vEdge m ∉ R.edges (follows from numClosure = 0 at m + parcel_point conditions)
    -- Then parCell_vEdge: vEdge m ∉ R.edges ∧ same parity
    -- Actually, we can derive the vEdge parity from the nearby squares.
    -- But parCell_vEdge_squ goes the other direction: vEdge → square.
    -- We need: square → vEdge (reverse direction is NOT available).
    -- Instead: show vEdge m ∉ R.edges (from numClosure = 0) then construct parCell directly.
    have hpt := (parCell_point R.toSegment m eps).mp hC
    have hnum := hpt.1
    rw [numClosure_eq_zero_iff] at hnum
    have hv_not : vEdge m ∉ R.edges := fun hmem =>
      hnum _ hmem ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
    have hv_d_not : vEdge (down m) ∉ R.edges := fun hmem =>
      hnum _ hmem ((pointI_mem_closure_vEdge m (down m)).mpr
        ⟨by simp [down], Or.inr (by simp [down])⟩)
    have hv := (parCell_vEdge R.toSegment m eps).mpr ⟨hv_not, heps⟩
    -- For vEdge (down m), need numLower at (down m) = numLower at m (same as for hEdge)
    -- Actually, numLower for vEdge (down m) uses coordinate (down m) = (m.1, m.2-1)
    -- which has same numLower as m when hEdge m ∉ R.edges
    have hh_not : hEdge m ∉ R.edges := fun hmem =>
      hnum _ hmem ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
    have hstep := numLower_step R.edges m.1 m.2
    simp only [Prod.mk.eta, if_neg hh_not, Nat.add_zero] at hstep
    have hv_d := (parCell_vEdge R.toSegment (down m) eps).mpr
      ⟨hv_d_not, by simp only [down]
                    change eps = decide (Even (numLower R.edges (m.1, m.2 - 1)))
                    rw [← hstep]; exact heps⟩
    -- Now all 9 cells in the 2×2 rectangle have parity eps
    refine ⟨rectangle (m.1 - 1, m.2 - 1) (m.1 + 1, m.2 + 1), fun w hw => ?_,
      rectangle_isOpen _ _, ?_⟩
    · rw [two_two_nine] at hw
      simp only [Set.mem_union, Set.mem_singleton_iff] at hw
      rcases hw with (((((((hw|hw)|hw)|hw)|hw)|hw)|hw)|hw)|hw
      · exact ⟨_, hh_l.2, hw⟩
      · exact ⟨_, hh_l.1, hw⟩
      · exact ⟨_, hh_r.2, hw⟩
      · exact ⟨_, hh_r.1, hw⟩
      · exact ⟨_, hp.2, hw⟩
      · exact ⟨_, hp.1, hw⟩
      · exact ⟨_, hv_d, hw⟩
      · exact ⟨_, hv, hw⟩
      · subst hw; exact ⟨_, hC, rfl⟩
    · rw [Set.mem_singleton_iff] at hzC; subst hzC
      simp only [rectangle, Set.mem_setOf_eq, pointI_coord_fst, pointI_coord_snd]
      push_cast; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- C = hEdge m
    have hhs := parCell_hEdge_squ R.toSegment m eps hC
    refine ⟨rectangle (m.1, m.2 - 1) (m.1 + 1, m.2 + 1), fun w hw => ?_,
      rectangle_isOpen _ _, ?_⟩
    · rw [rectangle_h_decomp] at hw
      simp only [Set.mem_union] at hw
      rcases hw with (hw | hw) | hw
      · exact ⟨_, hhs.2, hw⟩
      · exact ⟨_, hC, hw⟩
      · exact ⟨_, hhs.1, hw⟩
    · simp only [hEdge, Set.mem_setOf_eq] at hzC
      simp only [rectangle, Set.mem_setOf_eq]; push_cast
      exact ⟨hzC.1, hzC.2.1, by linarith, by linarith⟩
  · -- C = vEdge m
    have hvs := parCell_vEdge_squ R m eps hC
    refine ⟨rectangle (m.1 - 1, m.2) (m.1 + 1, m.2 + 1), fun w hw => ?_,
      rectangle_isOpen _ _, ?_⟩
    · rw [rectangle_v_decomp] at hw
      simp only [Set.mem_union] at hw
      rcases hw with (hw | hw) | hw
      · exact ⟨_, hvs.2, hw⟩
      · exact ⟨_, hC, hw⟩
      · exact ⟨_, hvs.1, hw⟩
    · simp only [vEdge, Set.mem_setOf_eq] at hzC
      simp only [rectangle, Set.mem_setOf_eq]; push_cast
      exact ⟨by linarith, by linarith, hzC.2.1, hzC.2.2⟩
  · -- C = squ m: the square is already open
    refine ⟨squ m, Set.subset_sUnion_of_mem hC, squ_eq_rectangle m ▸ rectangle_isOpen _ _, hzC⟩

/-! ## Parity partition -/

/-- The two parity regions partition the complement of the curve.
    HOL Light: `par_cell_partition` (line 8280). -/
theorem parCell_partition (G : Segment) (eps : Bool) :
    ⋃₀ {C | parCell eps G.edges C} ∪ ⋃₀ {C | parCell (!eps) G.edges C} =
      complementCurve G.edges := by
  ext z; constructor
  · -- ⊆: parCell cells don't intersect curve cells
    rintro (⟨C, hC, hzC⟩ | ⟨C, hC, hzC⟩)
    all_goals {
      simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion]
      push Not; intro S hS hzS
      have := hC.2; rw [Set.eq_empty_iff_forall_notMem] at this
      exact this z ⟨hzC, Set.mem_sUnion.mpr ⟨S, hS, hzS⟩⟩ }
  · -- ⊇: z ∈ complement → its cell has some parity
    intro hz
    obtain ⟨ct, hzct, huniq⟩ := cell_partition z
    -- Show ct.toSet ∩ ⋃₀ curveCells G.edges = ∅
    have hnocurve : ct.toSet ∩ ⋃₀ curveCells G.edges = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro w ⟨hw_ct, hw_curve⟩
      rw [Set.mem_sUnion] at hw_curve
      obtain ⟨S, hS_cc, hw_S⟩ := hw_curve
      have hS_cell := curveCells_subset_cell G.edges G.all_edges S hS_cc
      obtain ⟨ct', rfl⟩ := hS_cell
      -- By cell_partition uniqueness: ct = ct'
      have ⟨_, _, huniq'⟩ := cell_partition w
      have : ct = ct' := (huniq' ct hw_ct).trans (huniq' ct' hw_S).symm
      subst this
      -- So ct.toSet ∈ curveCells, hence z ∈ ⋃₀ curveCells
      have : z ∈ ⋃₀ (curveCells G.edges : Set (Set E2)) :=
        Set.mem_sUnion.mpr ⟨ct.toSet, hS_cc, hzct⟩
      exact (hz : z ∈ complementCurve G.edges) this
    -- Build parCell for the unique cell
    match ct with
    | .point m =>
      by_cases h : eps = decide (Even (numLower G.edges m))
      · left; exact ⟨_, ⟨⟨m, Or.inl rfl, h⟩, hnocurve⟩, hzct⟩
      · right; refine ⟨_, ⟨⟨m, Or.inl rfl, ?_⟩, hnocurve⟩, hzct⟩
        cases eps <;>
          simp only [false_eq_decide_iff, Nat.not_even_iff_odd, Nat.not_odd_iff_even,
            Bool.not_false, true_eq_decide_iff, Bool.not_true] at h ⊢ <;> exact h
    | .hEdge m =>
      by_cases h : eps = decide (Even (numLower G.edges m))
      · left; exact ⟨_, ⟨⟨m, Or.inr (Or.inl rfl), h⟩, hnocurve⟩, hzct⟩
      · right; refine ⟨_, ⟨⟨m, Or.inr (Or.inl rfl), ?_⟩, hnocurve⟩, hzct⟩
        cases eps <;>
          simp only [false_eq_decide_iff, Nat.not_even_iff_odd, Nat.not_odd_iff_even,
            Bool.not_false, true_eq_decide_iff, Bool.not_true] at h ⊢ <;> exact h
    | .vEdge m =>
      by_cases h : eps = decide (Even (numLower G.edges m))
      · left; exact ⟨_, ⟨⟨m, Or.inr (Or.inr (Or.inl rfl)), h⟩, hnocurve⟩, hzct⟩
      · right; refine ⟨_, ⟨⟨m, Or.inr (Or.inr (Or.inl rfl)), ?_⟩, hnocurve⟩, hzct⟩
        cases eps <;>
          simp only [false_eq_decide_iff, Nat.not_even_iff_odd, Nat.not_odd_iff_even,
            Bool.not_false, true_eq_decide_iff, Bool.not_true] at h ⊢ <;> exact h
    | .squ m =>
      by_cases h : eps = decide (Even (numLower G.edges m))
      · left; exact ⟨_, ⟨⟨m, Or.inr (Or.inr (Or.inr rfl)), h⟩, hnocurve⟩, hzct⟩
      · right; refine ⟨_, ⟨⟨m, Or.inr (Or.inr (Or.inr rfl)), ?_⟩, hnocurve⟩, hzct⟩
        cases eps <;>
          simp only [false_eq_decide_iff, Nat.not_even_iff_odd, Nat.not_odd_iff_even,
            Bool.not_false, true_eq_decide_iff, Bool.not_true] at h ⊢ <;> exact h

/-- An intersection of a parity region with the other parity region is empty.
    HOL Light: `par_cell_union_disjoint` (line 8580). -/
theorem parCell_union_disjoint (G : Finset (Set E2)) (eps : Bool) :
    ⋃₀ {C | parCell eps G C} ∩ ⋃₀ {C | parCell (!eps) G C} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_sUnion] at hz1 hz2
  obtain ⟨C₁, hC₁, hz_C₁⟩ := hz1
  obtain ⟨C₂, hC₂, hz_C₂⟩ := hz2
  have hcell₁ : isCell C₁ := by
    obtain ⟨⟨m, hm, _⟩, _⟩ := hC₁
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨.point m, rfl⟩
    · exact ⟨.hEdge m, rfl⟩
    · exact ⟨.vEdge m, rfl⟩
    · exact ⟨.squ m, rfl⟩
  have hcell₂ : isCell C₂ := by
    obtain ⟨⟨m, hm, _⟩, _⟩ := hC₂
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨.point m, rfl⟩
    · exact ⟨.hEdge m, rfl⟩
    · exact ⟨.vEdge m, rfl⟩
    · exact ⟨.squ m, rfl⟩
  obtain ⟨ct₁, rfl⟩ := hcell₁
  obtain ⟨ct₂, rfl⟩ := hcell₂
  have : ct₁ = ct₂ := by
    have ⟨_, _, huniq⟩ := cell_partition z
    exact (huniq ct₁ hz_C₁).trans (huniq ct₂ hz_C₂).symm
  subst this
  exact parCell_disjoint G eps _ ⟨hC₁, hC₂⟩

/-! ## Connected components and parity -/

/-- Connected components of the complement stay in one parity region.
    HOL Light: `par_cell_comp` (line 8620). -/
theorem parCell_comp (R : Rectagon) (eps : Bool) (x : E2) :
    connectedComponentIn (complementCurve R.edges) x ⊆
      ⋃₀ {C | parCell eps R.edges C} ∨
    connectedComponentIn (complementCurve R.edges) x ⊆
      ⋃₀ {C | parCell (!eps) R.edges C} := by
  -- The complement = A ∪ B (two parity regions), disjoint, both open
  have hKsub : connectedComponentIn (complementCurve R.edges) x ⊆
      ⋃₀ {C | parCell eps R.edges C} ∪ ⋃₀ {C | parCell (!eps) R.edges C} := by
    intro z hz
    change z ∈ ⋃₀ {C | parCell eps R.toSegment.edges C} ∪
      ⋃₀ {C | parCell (!eps) R.toSegment.edges C}
    rw [parCell_partition R.toSegment eps]
    exact connectedComponentIn_subset _ _ hz
  by_contra h; push Not at h; obtain ⟨hKA, hKB⟩ := h
  obtain ⟨a, haK, haA⟩ := Set.not_subset.mp hKA
  obtain ⟨b, hbK, hbB⟩ := Set.not_subset.mp hKB
  -- K preconnected, K ∩ A ≠ ∅, K ∩ B ≠ ∅  ⟹  K ∩ (A ∩ B) ≠ ∅
  obtain ⟨c, _, hcA, hcB⟩ := isPreconnected_connectedComponentIn _ _
    (parCell_open R eps) (parCell_open R (!eps)) hKsub
    ⟨b, hbK, (hKsub hbK).resolve_right hbB⟩ ⟨a, haK, (hKsub haK).resolve_left haA⟩
  -- But A ∩ B = ∅
  exact Set.eq_empty_iff_forall_notMem.mp (parCell_union_disjoint R.edges eps) c ⟨hcA, hcB⟩

/-- Convex subsets of the complement are preconnected.
    HOL Light: `convex_connected` (line 8710). -/
theorem convex_connected_ctop (G : Segment) (Z : Set E2)
    (hconv : Convex ℝ Z) (_hZ : Z ⊆ complementCurve G.edges) :
    IsPreconnected Z := hconv.isPreconnected

/-- Coordinate decomposition for convex combinations in E2. -/
private lemma combo_coord (x y : E2) (a b : ℝ) (i : Fin 2) :
    (a • x + b • y) i = a * (x i) + b * (y i) := by
  show (a • x + b • y).ofLp i = a * x.ofLp i + b * y.ofLp i
  simp [smul_eq_mul]

private lemma combo_gt (a b u v c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u > c) (hv : v > c) : a * u + b * v > c := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simpa
  · linarith [show a * c < a * u from by nlinarith,
      show b * c ≤ b * v from by nlinarith,
      show a * c + b * c = c from by rw [← add_mul, hab, one_mul]]

private lemma combo_lt (a b u v c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u < c) (hv : v < c) : a * u + b * v < c := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simpa
  · linarith [show a * u < a * c from by nlinarith,
      show b * v ≤ b * c from by nlinarith,
      show a * c + b * c = c from by rw [← add_mul, hab, one_mul]]

private lemma combo_eq (a b u v c : ℝ) (hab : a + b = 1)
    (hu : u = c) (hv : v = c) : a * u + b * v = c := by
  rw [hu, hv, ← add_mul, hab, one_mul]

/-- Cells are convex.
    HOL Light: `cell_convex` (line 8820). -/
theorem cell_convex (C : Set E2) (hC : isCell C) : Convex ℝ C := by
  obtain ⟨ct, rfl⟩ := hC
  match ct with
  | .point m => exact convex_singleton _
  | .squ m => change Convex ℝ (squ m); rw [squ_eq_rectangle]; exact rectangle_convex _ _
  | .hEdge m =>
    change Convex ℝ (hEdge m)
    intro x hx y hy a b ha hb hab
    simp only [hEdge, mem_setOf_eq] at *
    rw [combo_coord x y a b 0, combo_coord x y a b 1]
    exact ⟨combo_gt a b _ _ _ ha hb hab hx.1 hy.1,
           combo_lt a b _ _ _ ha hb hab hx.2.1 hy.2.1,
           combo_eq a b _ _ _ hab hx.2.2 hy.2.2⟩
  | .vEdge m =>
    change Convex ℝ (vEdge m)
    intro x hx y hy a b ha hb hab
    simp only [vEdge, mem_setOf_eq] at *
    rw [combo_coord x y a b 0, combo_coord x y a b 1]
    exact ⟨combo_eq a b _ _ _ hab hx.1 hy.1,
           combo_gt a b _ _ _ ha hb hab hx.2.1 hy.2.1,
           combo_lt a b _ _ _ ha hb hab hx.2.2 hy.2.2⟩

/-! ## Cell_of and component structure -/

/-- The cells contained in a set.
    HOL Light: `cell_of C` (line 9359). -/
def cellOf' (S : Set E2) : Set (Set E2) :=
  {A | isCell A ∧ A ⊆ S}

/-- The cells of a connected component cover it.
    HOL Light: `unions_cell_of` (line 9370). -/
theorem unions_cellOf_component (G : Segment) (x : E2) :
    ⋃₀ (cellOf' (connectedComponentIn (complementCurve G.edges) x)) =
      connectedComponentIn (complementCurve G.edges) x := by
  ext z; simp only [Set.mem_sUnion, cellOf', Set.mem_setOf_eq]
  constructor
  · -- ⊆: trivial from cellOf' definition
    rintro ⟨A, ⟨_, hAK⟩, hzA⟩; exact hAK hzA
  · -- ⊇: z ∈ K → the unique cell containing z is in cellOf'
    intro hzK
    have hzcomp : z ∈ complementCurve G.edges := connectedComponentIn_subset _ _ hzK
    obtain ⟨ct, hzct, huniq⟩ := cell_partition z
    -- ct.toSet ⊆ complement: if some w ∈ ct.toSet ∩ curveCells, cell uniqueness gives
    -- ct = that curve cell, so z ∈ curveCells, contradicting z ∈ complement
    have hct_comp : ct.toSet ⊆ complementCurve G.edges := by
      intro w hw
      simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion]; push Not
      intro S hS hwS
      obtain ⟨ct', rfl⟩ := curveCells_subset_cell G.edges G.all_edges S hS
      have ⟨_, _, huniq'⟩ := cell_partition w
      have h_eq : ct = ct' := (huniq' ct hw).trans (huniq' ct' hwS).symm
      exact hzcomp (Set.mem_sUnion.mpr ⟨ct'.toSet, hS, h_eq ▸ hzct⟩)
    -- ct.toSet is convex → preconnected, and it meets K at z
    -- So ct.toSet ⊆ connectedComponentIn complement z = K
    have hct_K : ct.toSet ⊆ connectedComponentIn (complementCurve G.edges) x := by
      rw [connectedComponentIn_eq hzK]
      exact (cell_convex ct.toSet ⟨ct, rfl⟩).isPreconnected.subset_connectedComponentIn
        hzct hct_comp
    exact ⟨ct.toSet, ⟨⟨ct, rfl⟩, hct_K⟩, hzct⟩

/-! ## par_cell ⊆ cell -/

/-- Every parity cell is a cell.
    HOL Light: `par_cell_cell` (line 8257). -/
theorem parCell_isCell {eps : Bool} {G : Finset (Set E2)}
    {C : Set E2} (h : parCell eps G C) : isCell C := by
  obtain ⟨⟨m, hm, _⟩, _⟩ := h
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨.point m, rfl⟩
  · exact ⟨.hEdge m, rfl⟩
  · exact ⟨.vEdge m, rfl⟩
  · exact ⟨.squ m, rfl⟩

/-! ## Extended vertical segment -/

/-- The extended vertical segment at lattice point `m`, spanning from
    `pointI (m.1, m.2 - 1)` to `pointI (m.1, m.2 + 1)` (open).
    HOL Light: `long_v p` (line 7650). -/
def longV (m : ℤ × ℤ) : Set E2 :=
  {z : E2 | z 0 = (↑m.1 : ℝ) ∧
    (↑m.2 : ℝ) - 1 < z 1 ∧ z 1 < (↑m.2 : ℝ) + 1}

/-- The extended vertical segment decomposes as the union of
    the lower vertical edge, the lattice point, and the upper
    vertical edge.
    HOL Light: `long_v_union` (line 7771). -/
theorem longV_union (m : ℤ × ℤ) :
    longV m = vEdge (down m) ∪ {pointI m} ∪ vEdge m := by
  ext z
  simp only [longV, vEdge, down, Set.mem_setOf_eq,
    Set.mem_union, Set.mem_singleton_iff]
  push_cast
  constructor
  · rintro ⟨hx, hlo, hhi⟩
    by_cases h1 : z 1 < ↑m.2
    · exact Or.inl (Or.inl ⟨hx, by linarith, by linarith⟩)
    · push Not at h1
      rcases eq_or_lt_of_le h1 with h2 | h2
      · exact Or.inl (Or.inr (by
          ext i; fin_cases i <;>
            simp [pointI, point, ← h2, hx]))
      · exact Or.inr ⟨hx, h2, hhi⟩
  · rintro ((⟨hx, hlo, hhi⟩ | hz) | ⟨hx, hlo, hhi⟩)
    · exact ⟨hx, by linarith, by linarith⟩
    · refine ⟨?_, ?_, ?_⟩ <;> (rw [hz]; simp [pointI, point])
    · exact ⟨hx, by linarith, hhi⟩

end
