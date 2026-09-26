/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionT_GridConstruction

/-!
# Section U: Parity Selection and Psegment Triples
## HOL Light: Section U (Lines 41110–42259)

SECTION NOT FORMALIZED — run full pipeline from instruction_section.prompt.md

Defines the parity function selecting the unique parity class containing a given cell,
and the notion of psegment triples (three pairwise-disjoint psegments whose pairwise
unions form rectagons). The main result is `trap_odd_cell`: at least one segment of
a psegment triple lies in the odd parity region of the union of the other two.
-/

open Set Metric Topology Function

namespace JordanCurveTheorem

/-! ## §U.1 Cell membership in families of cells -/

/-- HOL Light: `cell_ununion` (line 41115).
If C is a cell, C u holds, V is a family of cells, and (⋃₀ V) u, then V C. -/
theorem cell_ununion {V : Set (Set E2)} {C : Set E2} {u : E2}
    (hC : isCell C) (hu_C : u ∈ C) (hV : ∀ D ∈ V, isCell D)
    (hu_V : u ∈ ⋃₀ V) : C ∈ V := by
  obtain ⟨D, hDV, huD⟩ := Set.mem_sUnion.mp hu_V
  obtain ⟨ct_C, rfl⟩ := hC
  obtain ⟨ct_D, rfl⟩ := hV D hDV
  have ⟨_, _, huniq⟩ := cell_partition u
  have : ct_C = ct_D := (huniq ct_C hu_C).trans (huniq ct_D huD).symm
  rwa [this]

/-- HOL Light: `par_cell_cell_partition` (line 41133).
Every cell is in one of the two parity classes or is a curve cell. -/
theorem parCell_cell_partition_segment (G : Segment) (eps : Bool) (C : Set E2)
    (hC : isCell C) :
    parCell eps G.edges C ∨ parCell (!eps) G.edges C ∨ C ∈ curveCells G.edges := by
  by_cases hcurve : C ∈ curveCells G.edges
  · exact Or.inr (Or.inr hcurve)
  · have hne := cell_nonempty hC
    obtain ⟨u, hu⟩ := hne
    have hu_comp : u ∈ complementCurve G.edges := by
      simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion]; push Not
      intro S hS huS
      exact hcurve (cell_ununion hC hu (curveCells_subset_cell G.edges G.all_edges)
        (Set.mem_sUnion.mpr ⟨S, hS, huS⟩))
    have := (parCell_partition G eps).symm ▸ hu_comp
    rcases this with ⟨D, hD, hu_D⟩ | ⟨D, hD, hu_D⟩
    · have hD_cell : isCell D := by
        obtain ⟨⟨m, hcell_m, _⟩, _⟩ := hD
        rcases hcell_m with rfl | rfl | rfl | rfl <;>
          first
          | exact ⟨.point m, rfl⟩
          | exact ⟨.hEdge m, rfl⟩
          | exact ⟨.vEdge m, rfl⟩
          | exact ⟨.squ m, rfl⟩
      obtain ⟨ct_C, rfl⟩ := hC
      obtain ⟨ct_D, rfl⟩ := hD_cell
      have ⟨_, _, huniq⟩ := cell_partition u
      have : ct_C = ct_D := (huniq ct_C hu).trans (huniq ct_D hu_D).symm
      subst this; exact Or.inl hD
    · have hD_cell : isCell D := by
        obtain ⟨⟨m, hcell_m, _⟩, _⟩ := hD
        rcases hcell_m with rfl | rfl | rfl | rfl <;>
          first
          | exact ⟨.point m, rfl⟩
          | exact ⟨.hEdge m, rfl⟩
          | exact ⟨.vEdge m, rfl⟩
          | exact ⟨.squ m, rfl⟩
      obtain ⟨ct_C, rfl⟩ := hC
      obtain ⟨ct_D, rfl⟩ := hD_cell
      have ⟨_, _, huniq⟩ := cell_partition u
      have : ct_C = ct_D := (huniq ct_C hu).trans (huniq ct_D hu_D).symm
      subst this; exact Or.inr (Or.inl hD)

/-- HOL Light: `par_cell_curve_cell_disj` (line 41168).
Parity cells and curve cells are disjoint (as families of cells). -/
theorem parCell_curveCells_disjoint (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    (eps : Bool) :
    {C | parCell eps G C} ∩ curveCells G = ∅ := by
  ext C; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hpar hcurve
  have ⟨_, hdis⟩ := hpar
  have hC_cell := curveCells_subset_cell G hG C hcurve
  have ⟨z, hz⟩ := cell_nonempty hC_cell
  exact Set.eq_empty_iff_forall_notMem.mp hdis z ⟨hz, Set.mem_sUnion.mpr ⟨C, hcurve, hz⟩⟩

/-- HOL Light: `curve_cell_edge` (line 41186).
For an edge e, `curveCells G e ↔ G e` (i.e. edge cells are curve cells iff in G). -/
theorem curveCells_edge (G : Finset (Set E2)) (e : Set E2) (he : isEdge e) :
    e ∈ curveCells G ↔ e ∈ G := by
  rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
    constructor
    · rintro (h | ⟨n, heq, -⟩)
      · exact h
      · exact absurd heq (hEdge_ne_pointI_set m n)
    · exact Or.inl
  · simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
    constructor
    · rintro (h | ⟨n, heq, -⟩)
      · exact h
      · exact absurd heq (vEdge_ne_pointI_set m n)
    · exact Or.inl

/-! ## §U.2 Parity selection -/

/-- HOL Light: `parity_select` (line 41115).
`paritySelect G C` picks the unique `eps : Bool` such that `parCell eps G C` holds.
Uses classical choice. -/
noncomputable def paritySelect (G : Finset (Set E2)) (C : Set E2) : Bool :=
  Classical.epsilon (fun eps => parCell eps G C)

/-- HOL Light: `parity` (line 41198).
For a segment G and a cell C not in `curveCells G`, `paritySelect G C` gives the
correct parity. -/
theorem paritySelect_spec (G : Segment) (C : Set E2)
    (hC : isCell C) (hnotcurve : C ∉ curveCells G.edges) :
    parCell (paritySelect G.edges C) G.edges C := by
  unfold paritySelect
  have : ∃ eps, parCell eps G.edges C := by
    rcases parCell_cell_partition_segment G true C hC with h | h | h
    · exact ⟨true, h⟩
    · exact ⟨false, by simpa using h⟩
    · exact absurd h hnotcurve
  exact Classical.epsilon_spec this

/-- HOL Light: `parity_unique` (line 41211).
If `parCell eps G C` holds for a segment G, then `eps = paritySelect G C`. -/
theorem paritySelect_unique (G : Segment) (C : Set E2) (eps : Bool)
    (h : parCell eps G.edges C) :
    eps = paritySelect G.edges C := by
  have hC : isCell C := by
    obtain ⟨⟨m, hcell, _⟩, _⟩ := h
    rcases hcell with rfl | rfl | rfl | rfl
    · exact ⟨.point m, rfl⟩
    · exact ⟨.hEdge m, rfl⟩
    · exact ⟨.vEdge m, rfl⟩
    · exact ⟨.squ m, rfl⟩
  have hnotcurve : C ∉ curveCells G.edges := by
    intro hcurve
    have ⟨z, hz⟩ := cell_nonempty hC
    exact Set.eq_empty_iff_forall_notMem.mp h.2 z
      ⟨hz, Set.mem_sUnion.mpr ⟨C, hcurve, hz⟩⟩
  have hpar := paritySelect_spec G C hC hnotcurve
  by_contra hne
  have hswap : paritySelect G.edges C = !eps := by
    cases eps <;> cases hp : (paritySelect G.edges C) <;> simp_all
  rw [hswap] at hpar
  exact parCell_disjoint G.edges eps C ⟨h, hpar⟩

/-- HOL Light: `unions_curve_cell` (line 41236).
For a cell C in a finite edge set G:
`C ∩ ⋃₀ curveCells G = ∅ ↔ C ∉ curveCells G`. -/
theorem cell_inter_curveCells_empty_iff (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    (C : Set E2) (hC : isCell C) :
    C ∩ ⋃₀ (curveCells G : Set (Set E2)) = ∅ ↔ C ∉ curveCells G := by
  constructor
  · intro hdis hcurve
    have ⟨z, hz⟩ := cell_nonempty hC
    exact Set.eq_empty_iff_forall_notMem.mp hdis z
      ⟨hz, Set.mem_sUnion.mpr ⟨C, hcurve, hz⟩⟩
  · intro hnotcurve
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz_C, hz_curve⟩
    rw [Set.mem_sUnion] at hz_curve
    obtain ⟨S, hS, hz_S⟩ := hz_curve
    have : C ∈ curveCells G := cell_ununion hC hz_C (curveCells_subset_cell G hG)
      (Set.mem_sUnion.mpr ⟨S, hS, hz_S⟩)
    exact hnotcurve this

/-! ## §U.3 Even/odd number lower for unions -/

/-- HOL Light: `even_num_lower_union` (line 41266).
The parity of `numLower (A ∪ B) m` decomposes over disjoint unions. -/
theorem even_numLower_union (A B : Finset (Set E2)) (m : ℤ × ℤ)
    (_hfA : ∀ e ∈ A, isEdge e) (_hfB : ∀ e ∈ B, isEdge e)
    (hdisj : Disjoint A B) :
    Even (numLower (A ∪ B) m) ↔ (Even (numLower A m) ↔ Even (numLower B m)) := by
  -- numLower is Finset.card of a filter. For disjoint A, B:
  -- filter(A ∪ B) = filter(A) ∪ filter(B), disjoint
  -- so card(A ∪ B) = card(A) + card(B)
  have key : numLower (A ∪ B) m = numLower A m + numLower B m := by
    simp only [numLower, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rw [key, Nat.even_add]

/-- HOL Light: `eq_pair_exchange` (line 41291).
`((a = b) ↔ (c = d)) ↔ ((a = c) ↔ (b = d))` for booleans. -/
theorem eq_pair_exchange (a b c d : Bool) :
    ((a = b) ↔ (c = d)) ↔ ((a = c) ↔ (b = d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-! ## §U.4 Parity for specific cell types -/

/-- HOL Light: `parity_point` (line 41298).
For a segment A and a lattice point p not in curveCells A,
`paritySelect A {pointI p} = decide (Even (numLower A p))`. -/
theorem paritySelect_point (A : Segment) (p : ℤ × ℤ)
    (hnotcurve : {pointI p} ∉ curveCells A.edges) :
    paritySelect A.edges {pointI p} = decide (Even (numLower A.edges p)) := by
  symm; apply paritySelect_unique
  exact ⟨⟨p, Or.inl rfl, rfl⟩, (cell_inter_curveCells_empty_iff A.edges A.all_edges _
      ⟨.point p, rfl⟩).mpr hnotcurve⟩

/-- HOL Light: `parity_h` (line 41316).
For a segment A and h-edge not in A:
`paritySelect A (hEdge p) = decide (Even (numLower A p))`. -/
theorem paritySelect_hEdge (A : Segment) (p : ℤ × ℤ)
    (hnotA : hEdge p ∉ A.edges) :
    paritySelect A.edges (hEdge p) = decide (Even (numLower A.edges p)) := by
  symm; apply paritySelect_unique
  exact (parCell_hEdge A p _).mpr ⟨hnotA, rfl⟩

/-- HOL Light: `parity_v` (line 41333).
For a segment A and v-edge not in A:
`paritySelect A (vEdge p) = decide (Even (numLower A p))`. -/
theorem paritySelect_vEdge (A : Segment) (p : ℤ × ℤ)
    (hnotA : vEdge p ∉ A.edges) :
    paritySelect A.edges (vEdge p) = decide (Even (numLower A.edges p)) := by
  symm; apply paritySelect_unique
  exact (parCell_vEdge A p _).mpr ⟨hnotA, rfl⟩

/-- HOL Light: `parity_squ` (line 41350).
For a segment A: `paritySelect A (squ p) = decide (Even (numLower A p))`. -/
theorem paritySelect_squ (A : Segment) (p : ℤ × ℤ) :
    paritySelect A.edges (squ p) = decide (Even (numLower A.edges p)) := by
  symm; apply paritySelect_unique
  exact (parCell_squ A p _).mpr rfl

/-! ## §U.5 Parity of unions -/

/-- HOL Light: `parity_union` (line 41366).
For disjoint segments A, B with A ∪ B also a segment, and a cell C not in
curveCells of either:
`paritySelect (A ∪ B) C = decide (paritySelect A C = paritySelect B C)`. -/
theorem paritySelect_union (A B : Segment)
    (hAB : ∃ sAB : Segment, sAB.edges = A.edges ∪ B.edges)
    (hdisj : Disjoint A.edges B.edges)
    (C : Set E2) (hC : isCell C)
    (hnotA : C ∉ curveCells A.edges) (hnotB : C ∉ curveCells B.edges) :
    paritySelect (A.edges ∪ B.edges) C =
      decide (paritySelect A.edges C = paritySelect B.edges C) := by
  obtain ⟨sAB, hsAB⟩ := hAB
  obtain ⟨ct, rfl⟩ := hC
  -- Helper: once paritySelect reduces to numLower for all three segments, boolean reasoning closes
  have bstep : ∀ (p : ℤ × ℤ),
      paritySelect sAB.edges ct.toSet = decide (Even (numLower sAB.edges p)) →
      paritySelect A.edges ct.toSet = decide (Even (numLower A.edges p)) →
      paritySelect B.edges ct.toSet = decide (Even (numLower B.edges p)) →
      paritySelect (A.edges ∪ B.edges) ct.toSet =
        decide (paritySelect A.edges ct.toSet = paritySelect B.edges ct.toSet) := by
    intro p h1 h2 h3
    have hlhs : paritySelect (A.edges ∪ B.edges) ct.toSet =
        paritySelect sAB.edges ct.toSet := by congr 1; exact hsAB.symm
    rw [hlhs, h1, h2, h3]
    have heq : numLower sAB.edges p = numLower (A.edges ∪ B.edges) p := by
      congr 1
    have heven := even_numLower_union A.edges B.edges p A.all_edges B.all_edges hdisj
    rw [← heq] at heven
    exact decide_eq_decide.mpr (heven.trans decide_eq_decide.symm)
  -- Case split: .point | .hEdge | .vEdge | .squ
  rcases ct with p | p | p | p
  · -- point
    have hAB' : ({pointI p} : Set E2) ∉ curveCells sAB.edges := by
      rw [hsAB, curveCells_union]
      intro h; rcases h with h | h
      · exact hnotA h
      · exact hnotB h
    exact bstep p (paritySelect_point sAB p hAB')
      (paritySelect_point A p hnotA) (paritySelect_point B p hnotB)
  · -- hEdge
    have hA : hEdge p ∉ A.edges := fun h => hnotA ((curveCells_hEdge A p).mpr h)
    have hB : hEdge p ∉ B.edges := fun h => hnotB ((curveCells_hEdge B p).mpr h)
    have hAB' : hEdge p ∉ sAB.edges := by
      rw [hsAB]; simp only [Finset.mem_union, not_or]; exact ⟨hA, hB⟩
    exact bstep p (paritySelect_hEdge sAB p hAB')
      (paritySelect_hEdge A p hA) (paritySelect_hEdge B p hB)
  · -- vEdge
    have hA : vEdge p ∉ A.edges := fun h => hnotA ((curveCells_vEdge A p).mpr h)
    have hB : vEdge p ∉ B.edges := fun h => hnotB ((curveCells_vEdge B p).mpr h)
    have hAB' : vEdge p ∉ sAB.edges := by
      rw [hsAB]; simp only [Finset.mem_union, not_or]; exact ⟨hA, hB⟩
    exact bstep p (paritySelect_vEdge sAB p hAB')
      (paritySelect_vEdge A p hA) (paritySelect_vEdge B p hB)
  · -- squ
    exact bstep p (paritySelect_squ sAB p) (paritySelect_squ A p) (paritySelect_squ B p)

/-! ## §U.6 Component characterization via simple arcs -/

/-- HOL Light: `ctop_comp_open` (line 41526).
Connected components of `complementCurve G` are open in `E2'`. -/
theorem isOpen_connectedComponent_complementCurve (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e)
    (x : E2) :
    IsOpen (connectedComponentIn (complementCurve G) x) := by
  have hopen : IsOpen (complementCurve G) := by
    rw [complementCurve, isOpen_compl_iff, ← curve_closure_finset G hG]
    exact isClosed_closure
  exact hopen.connectedComponentIn

/-- HOL Light: `component_simple_arc` (line 41408).
For a finite edge set G, x ≠ y:
`connectedComponentIn (complementCurve G) x y ↔
  ∃ C, IsSimpleArcEnd C x y ∧ C ∩ ⋃₀ curveCells G = ∅`. -/
theorem component_simple_arc (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e)
    (x y : E2) (hne : x ≠ y) :
    y ∈ connectedComponentIn (complementCurve G) x ↔
      ∃ C : Set E2, IsSimpleArcEnd C x y ∧
        C ∩ ⋃₀ (curveCells G : Set (Set E2)) = ∅ := by
  constructor
  · -- Forward: y in connected component → simple arc avoiding curve
    intro hy
    have hxS : x ∈ complementCurve G :=
      connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩
    have hxC : x ∈ connectedComponentIn (complementCurve G) x := by
      simp only [connectedComponentIn, hxS, ↓reduceDIte, mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, exists_true_left]
      exact mem_connectedComponent
    have hconn : IsConnected (connectedComponentIn (complementCurve G) x) :=
      ⟨⟨y, hy⟩, isPreconnected_connectedComponentIn⟩
    have hpath := pathConnected_of_isConnected_isOpen
      (isOpen_connectedComponent_complementCurve G hG x) hconn x hxC y hy
    rcases hpath with rfl | ⟨C, hC_arc, hC_sub⟩
    · exact absurd rfl hne
    · have hsub := hC_sub.trans (connectedComponentIn_subset (complementCurve G) x)
      refine ⟨C, hC_arc, Set.eq_empty_iff_forall_notMem.mpr fun z ⟨hz1, hz2⟩ => ?_⟩
      have hmem := hsub hz1
      simp only [complementCurve, Set.mem_compl_iff] at hmem
      exact hmem hz2
  · -- Backward: simple arc → y in connected component
    rintro ⟨C, hC_arc, hC_disj⟩
    have hC_pc : IsPreconnected C :=
      (simpleArc_isConnected C (isSimpleArcEnd_isSimpleArc hC_arc)).2
    have hC_sub : C ⊆ complementCurve G := by
      intro z hz; simp only [complementCurve, Set.mem_compl_iff]
      exact fun habs =>
        Set.eq_empty_iff_forall_notMem.mp hC_disj z ⟨hz, habs⟩
    exact hC_pc.subset_connectedComponentIn
      (isSimpleArcEnd_mem_left hC_arc) (hC_sub) (isSimpleArcEnd_mem_right hC_arc)

/-! ## §U.7 Psegment triples -/

/-- HOL Light: `psegment_triple` (line 41602).
Three psegments A, B, C forming a triple: all pairwise disjoint, pairwise unions are
rectagons, and they share the same pair of endpoints. -/
def isPsegmentTriple (A B C : Finset (Set E2)) : Prop :=
  (∃ sA : Segment, sA.edges = A ∧ sA.isPsegment) ∧
  (∃ sB : Segment, sB.edges = B ∧ sB.isPsegment) ∧
  (∃ sC : Segment, sC.edges = C ∧ sC.isPsegment) ∧
  (∃ rAB : Rectagon, rAB.edges = A ∪ B) ∧
  (∃ rAC : Rectagon, rAC.edges = A ∪ C) ∧
  (∃ rBC : Rectagon, rBC.edges = B ∪ C) ∧
  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
  cls A ∩ cls B = {m | numClosure A m = 1} ∧
  cls B ∩ cls C = {m | numClosure A m = 1} ∧
  cls A ∩ cls C = {m | numClosure A m = 1} ∧
  {m | numClosure A m = 1} = {m | numClosure B m = 1} ∧
  {m | numClosure B m = 1} = {m | numClosure C m = 1}

/-- HOL Light: `psegment_triple3` (line 41619).
Cyclic permutation: `isPsegmentTriple A B C → isPsegmentTriple B C A`. -/
theorem isPsegmentTriple_rotate {A B C : Finset (Set E2)}
    (h : isPsegmentTriple A B C) : isPsegmentTriple B C A := by
  obtain ⟨hA, hB, hC, hAB, hAC, hBC, dAB, dAC, dBC,
          h10, h11, h12, h13, h14⟩ := h
  refine ⟨hB, hC, hA, hBC, ?_, ?_, dBC, dAB.symm, dAC.symm, ?_, ?_, ?_, h14, ?_⟩
  · obtain ⟨r, hr⟩ := hAB; exact ⟨r, hr.trans (Finset.union_comm A B)⟩
  · obtain ⟨r, hr⟩ := hAC; exact ⟨r, hr.trans (Finset.union_comm A C)⟩
  · exact h11.trans h13
  · rw [Set.inter_comm]; exact h12.trans h13
  · rw [Set.inter_comm]; exact h10.trans h13
  · exact (h13.trans h14).symm

/-- HOL Light: `psegment_triple2` (line 41629).
Swap first and last: `isPsegmentTriple A B C → isPsegmentTriple C B A`. -/
theorem isPsegmentTriple_swap {A B C : Finset (Set E2)}
    (h : isPsegmentTriple A B C) : isPsegmentTriple C B A := by
  obtain ⟨hA, hB, hC, hAB, hAC, hBC, dAB, dAC, dBC,
          h10, h11, h12, h13, h14⟩ := h
  have endAC := h13.trans h14
  refine ⟨hC, hB, hA, ?_, ?_, ?_, dBC.symm, dAC.symm, dAB.symm,
          ?_, ?_, ?_, h14.symm, h13.symm⟩
  · obtain ⟨r, hr⟩ := hBC; exact ⟨r, hr.trans (Finset.union_comm B C)⟩
  · obtain ⟨r, hr⟩ := hAC; exact ⟨r, hr.trans (Finset.union_comm A C)⟩
  · obtain ⟨r, hr⟩ := hAB; exact ⟨r, hr.trans (Finset.union_comm A B)⟩
  · rw [Set.inter_comm]; exact h11.trans endAC
  · rw [Set.inter_comm]; exact h10.trans endAC
  · rw [Set.inter_comm]; exact h12.trans endAC

/-! ## §U.8 Parity closure -/

/-- HOL Light: `unions_empty_imp_empty` (line 41637).
If ⋃₀ A ∩ ⋃₀ B = ∅ and every member of A is nonempty, then A ∩ B = ∅. -/
theorem sUnion_inter_empty_of_nonempty {A B : Set (Set E2)}
    (hinter : ⋃₀ A ∩ ⋃₀ B = ∅) (hne : ∀ C ∈ A, C.Nonempty) :
    A ∩ B = ∅ := by
  ext C; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hCA hCB
  obtain ⟨z, hz⟩ := hne C hCA
  exact Set.eq_empty_iff_forall_notMem.mp hinter z
    ⟨Set.mem_sUnion.mpr ⟨C, hCA, hz⟩, Set.mem_sUnion.mpr ⟨C, hCB, hz⟩⟩

/-- HOL Light: `par_cell_closure` (line 41651).
If A ⊆ parCell eps G and A is a finite edge set inside a rectagon G, then
curveCells A ∩ parCell (!eps) G = ∅. -/
theorem parCell_closure (G : Rectagon) (A : Finset (Set E2)) (eps : Bool)
    (hA_edge : ∀ e ∈ A, isEdge e)
    (hA_sub : ∀ e ∈ A, parCell eps G.edges e) :
    (curveCells A : Set (Set E2)) ∩ {C | parCell (!eps) G.edges C} = ∅ := by
  apply sUnion_inter_empty_of_nonempty
  · -- ⋃₀ curveCells A ∩ ⋃₀ {C | parCell (!eps) G.edges C} = ∅
    rw [← curve_closure_finset A hA_edge]
    -- closure(⋃₀ ↑A) ∩ ⋃₀ {C | parCell (!eps) G.edges C} = ∅
    have h_sub : ⋃₀ (↑A : Set (Set E2)) ⊆ (⋃₀ {C | parCell (!eps) G.edges C})ᶜ := by
      intro x hx habs
      exact Set.eq_empty_iff_forall_notMem.mp (parCell_union_disjoint G.edges eps) x
        ⟨Set.mem_sUnion.mpr (by
          obtain ⟨e, heA, hxe⟩ := Set.mem_sUnion.mp hx
          exact ⟨e, hA_sub e heA, hxe⟩), habs⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hz1, hz2⟩
    exact closure_minimal h_sub (isClosed_compl_iff.mpr (parCell_open G (!eps))) hz1 hz2
  · exact fun C hC =>
      cell_nonempty (curveCells_subset_cell A hA_edge C hC)

/-- HOL Light: `cell_unions_disj` (line 41736).
For two families of cells, they are disjoint iff their unions are disjoint. -/
theorem cell_unions_disjoint_iff {U V : Set (Set E2)}
    (hU : ∀ C ∈ U, isCell C) (hV : ∀ C ∈ V, isCell C) :
    U ∩ V = ∅ ↔ ⋃₀ U ∩ ⋃₀ V = ∅ := by
  constructor
  · intro hdisj
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hzU, hzV⟩
    rw [Set.mem_sUnion] at hzU hzV
    obtain ⟨C, hCU, hzC⟩ := hzU
    obtain ⟨D, hDV, hzD⟩ := hzV
    have : C = D := by
      obtain ⟨ct_C, rfl⟩ := hU C hCU
      obtain ⟨ct_D, rfl⟩ := hV D hDV
      have ⟨_, _, huniq⟩ := cell_partition z
      exact congrArg _ ((huniq ct_C hzC).trans (huniq ct_D hzD).symm)
    exact Set.eq_empty_iff_forall_notMem.mp hdisj C ⟨hCU, this ▸ hDV⟩
  · intro hdisj
    exact sUnion_inter_empty_of_nonempty hdisj fun C hC => cell_nonempty (hU C hC)

/-- HOL Light: `unions_curve_cell_par_cell_disj` (line 41763).
⋃₀ (parCell eps G) ∩ ⋃₀ curveCells G = ∅. -/
theorem sUnion_parCell_inter_curveCells_empty (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (eps : Bool) :
    ⋃₀ {C | parCell eps G C} ∩ ⋃₀ (curveCells G : Set (Set E2)) = ∅ := by
  rw [← cell_unions_disjoint_iff
    (fun C hC => by
      obtain ⟨⟨m, hcell, _⟩, _⟩ := hC
      rcases hcell with rfl | rfl | rfl | rfl
      · exact ⟨.point m, rfl⟩
      · exact ⟨.hEdge m, rfl⟩
      · exact ⟨.vEdge m, rfl⟩
      · exact ⟨.squ m, rfl⟩)
    (curveCells_subset_cell G hG)]
  exact parCell_curveCells_disjoint G hG eps

/-! ## §U.9 Simple arc in parity region -/

/-- HOL Light: `par_cell_simple_arc` (line 41779).
Two points in ⋃₀ (parCell eps G) (for a rectagon G) are connected by a simple arc
inside that region. -/
theorem parCell_simple_arc (G : Rectagon) (eps : Bool) (x y : E2) (hne : x ≠ y) :
    (x ∈ ⋃₀ {C | parCell eps G.edges C} ∧ y ∈ ⋃₀ {C | parCell eps G.edges C}) ↔
      ∃ C : Set E2, IsSimpleArcEnd C x y ∧ C ⊆ ⋃₀ {C | parCell eps G.edges C} := by
  constructor
  · -- Forward: both in parCell region → simple arc in region
    intro ⟨hx, hy⟩
    have heq := parCell_union_comp G eps hx
    have hy_comp : y ∈ connectedComponentIn (complementCurve G.edges) x :=
      heq ▸ hy
    rw [component_simple_arc G.edges G.all_edges x y hne] at hy_comp
    obtain ⟨C, hC_arc, hC_disj⟩ := hy_comp
    refine ⟨C, hC_arc, ?_⟩
    have hC_sub_comp : C ⊆ complementCurve G.edges := by
      intro z hz; simp only [complementCurve, Set.mem_compl_iff]
      exact fun habs =>
        Set.eq_empty_iff_forall_notMem.mp hC_disj z ⟨hz, habs⟩
    have hC_pc : IsPreconnected C :=
      (simpleArc_isConnected C (isSimpleArcEnd_isSimpleArc hC_arc)).2
    have hC_in := hC_pc.subset_connectedComponentIn
      (isSimpleArcEnd_mem_left hC_arc) hC_sub_comp
    rw [← heq] at hC_in; exact hC_in
  · -- Backward: simple arc in region → both endpoints in region
    rintro ⟨C, hC_arc, hC_sub⟩
    exact ⟨hC_sub (isSimpleArcEnd_mem_left hC_arc),
           hC_sub (isSimpleArcEnd_mem_right hC_arc)⟩

/-! ## §U.10 Trapping lemmas -/

/-- HOL Light: `trap_triple_seg` (line 41830).
If C ⊆ parCell (!eps) (A ∪ B) in a psegment triple, then
parCell eps (A ∪ B) ⊆ parCell eps' (A ∪ C) ∨ parCell eps (A ∪ B) ⊆ parCell (!eps') (A ∪ C). -/
theorem trap_triple_seg (A B C : Finset (Set E2)) (eps eps' : Bool)
    (htrip : isPsegmentTriple A B C)
    (hC_sub : ∀ e ∈ C, parCell (!eps) (A ∪ B) e) :
    (∀ e, parCell eps (A ∪ B) e → parCell eps' (A ∪ C) e) ∨
    (∀ e, parCell eps (A ∪ B) e → parCell (!eps') (A ∪ C) e) := by
  obtain ⟨_, _, ⟨sC, hsC, _⟩, ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, _, dAB, dAC, dBC,
          _, _, _, _, _⟩ := htrip
  have hAB_edge : ∀ f ∈ (A ∪ B : Finset (Set E2)), isEdge f :=
    fun f hf => rAB.all_edges f (hrAB ▸ hf)
  have hAC_edge : ∀ f ∈ (A ∪ C : Finset (Set E2)), isEdge f :=
    fun f hf => rAC.all_edges f (hrAC ▸ hf)
  have hC_edge : ∀ f ∈ (C : Finset (Set E2)), isEdge f :=
    fun f hf => sC.all_edges f (hsC ▸ hf)
  -- Step 1: Every cell in parCell eps (A∪B) is in parCell eps' or (!eps') of A∪C.
  have hcell_disj : ∀ e, parCell eps (A ∪ B) e →
      parCell eps' (A ∪ C) e ∨ parCell (!eps') (A ∪ C) e := by
    intro e he
    have hcell := parCell_isCell he
    rcases parCell_cell_partition_segment rAC.toSegment eps' e hcell with h | h | h
    · left; exact hrAC ▸ h
    · right; exact hrAC ▸ h
    · -- e ∈ curveCells(rAC.edges) = curveCells(A∪C): contradiction
      rw [show rAC.toSegment.edges = A ∪ C from hrAC, curveCells_union] at h
      rcases h with hA | hC_curve
      · -- e ∈ curveCells A ⊆ curveCells(A∪B): contradicts par_cell disj
        have hmem : e ∈ curveCells (A ∪ B) := curveCells_union A B ▸ Or.inl hA
        exact (Set.eq_empty_iff_forall_notMem.mp
          (parCell_curveCells_disjoint (A ∪ B) hAB_edge eps) e ⟨he, hmem⟩).elim
      · -- e ∈ curveCells C: parCell_closure gives curveCells C ∩ parCell eps (A∪B) = ∅
        have hcl := parCell_closure rAB C (!eps) hC_edge
          (fun f hf => hrAB ▸ hC_sub f hf)
        simp only [Bool.not_not] at hcl; simp_rw [hrAB] at hcl
        exact (Set.eq_empty_iff_forall_notMem.mp hcl e ⟨hC_curve, he⟩).elim
  -- Step 2: by contradiction, assume neither disjunct holds
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx_eps, hx_not_eps'⟩, ⟨x', hx'_eps, hx'_not_neps'⟩⟩ := hcon
  have hx_neps' : parCell (!eps') (A ∪ C) x :=
    (hcell_disj x hx_eps).resolve_left hx_not_eps'
  have hx'_eps' : parCell eps' (A ∪ C) x' :=
    (hcell_disj x' hx'_eps).resolve_right hx'_not_neps'
  -- Step 3: get points u ∈ x, u' ∈ x'
  have ⟨u, hu⟩ := cell_nonempty (parCell_isCell hx_eps)
  have ⟨u', hu'⟩ := cell_nonempty (parCell_isCell hx'_eps)
  have hu_par : u ∈ ⋃₀ {C | parCell eps (A ∪ B) C} :=
    Set.mem_sUnion.mpr ⟨x, hx_eps, hu⟩
  have hu'_par : u' ∈ ⋃₀ {C | parCell eps (A ∪ B) C} :=
    Set.mem_sUnion.mpr ⟨x', hx'_eps, hu'⟩
  -- Step 4: case split on u = u'
  by_cases huu' : u = u'
  · -- x = x' by cell uniqueness → contradiction
    subst huu'
    obtain ⟨_, _, huniq⟩ := cell_partition u
    have hxx : x = x' := by
      obtain ⟨ct, rfl⟩ := parCell_isCell hx_eps
      obtain ⟨ct', rfl⟩ := parCell_isCell hx'_eps
      exact congrArg _ ((huniq ct hu).trans (huniq ct' hu').symm)
    subst hxx; exact parCell_disjoint (A ∪ C) eps' x ⟨hx'_eps', hx_neps'⟩
  · -- Get a simple arc C' in ⋃₀(parCell eps rAB.edges) connecting u, u'
    have hu_rAB : u ∈ ⋃₀ {D | parCell eps rAB.edges D} := by
      simp_rw [hrAB]; exact hu_par
    have hu'_rAB : u' ∈ ⋃₀ {D | parCell eps rAB.edges D} := by
      simp_rw [hrAB]; exact hu'_par
    obtain ⟨C', hC'_arc, hC'_sub⟩ :=
      (parCell_simple_arc rAB eps u u' huu').mp ⟨hu_rAB, hu'_rAB⟩
    -- Convert C' ⊆ ⋃₀(parCell eps rAB.edges) to A ∪ B
    have hC'_sub_AB : C' ⊆ ⋃₀ {D | parCell eps (A ∪ B) D} := by
      intro z hz; have := hC'_sub hz; simp_rw [hrAB] at this; exact this
    -- C' ∩ ⋃₀(curveCells A) = ∅
    have hC'_disj_A : C' ∩ ⋃₀ (curveCells A : Set (Set E2)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z ⟨hz1, hz2⟩
      have hz_AB : z ∈ ⋃₀ (curveCells (A ∪ B) : Set (Set E2)) := by
        rw [curveCells_union, Set.sUnion_union]; exact Set.mem_union_left _ hz2
      exact Set.eq_empty_iff_forall_notMem.mp
        (sUnion_parCell_inter_curveCells_empty (A ∪ B) hAB_edge eps)
        z ⟨hC'_sub_AB hz1, hz_AB⟩
    -- C' ∩ ⋃₀(curveCells C) = ∅
    have hC'_disj_C : C' ∩ ⋃₀ (curveCells C : Set (Set E2)) = ∅ := by
      have hcl := parCell_closure rAB C (!eps) hC_edge (fun f hf => hrAB ▸ hC_sub f hf)
      simp only [Bool.not_not] at hcl; simp_rw [hrAB] at hcl
      have hcl_pt := (cell_unions_disjoint_iff (curveCells_subset_cell C hC_edge)
        (fun D hD => parCell_isCell hD)).mp hcl
      rw [Set.eq_empty_iff_forall_notMem]
      intro z ⟨hz1, hz2⟩
      exact Set.eq_empty_iff_forall_notMem.mp hcl_pt z ⟨hz2, hC'_sub_AB hz1⟩
    -- C' ∩ ⋃₀(curveCells(A∪C)) = ∅
    have hC'_disj_AC : C' ∩ ⋃₀ (curveCells (A ∪ C) : Set (Set E2)) = ∅ := by
      rw [curveCells_union, Set.sUnion_union, Set.inter_union_distrib_left,
        hC'_disj_A, hC'_disj_C, Set.empty_union]
    -- u' ∈ connectedComponentIn(complementCurve(A∪C)) u
    have hu_comp : u' ∈ connectedComponentIn (complementCurve (A ∪ C)) u :=
      (component_simple_arc (A ∪ C) hAC_edge u u' huu').mpr
        ⟨C', hC'_arc, hC'_disj_AC⟩
    -- u ∈ ⋃₀(parCell(!eps')(A∪C)) and u' ∈ ⋃₀(parCell eps'(A∪C))
    have hu_neps'_mem : u ∈ ⋃₀ {D | parCell (!eps') (A ∪ C) D} :=
      Set.mem_sUnion.mpr ⟨x, hx_neps', hu⟩
    have hu'_eps'_mem : u' ∈ ⋃₀ {D | parCell eps' (A ∪ C) D} :=
      Set.mem_sUnion.mpr ⟨x', hx'_eps', hu'⟩
    -- ⋃₀(parCell(!eps')(A∪C)) = connectedComponentIn ... u
    have heq_neps' := parCell_union_comp rAC (!eps') (by simp_rw [hrAC]; exact hu_neps'_mem)
    simp_rw [hrAC] at heq_neps'
    -- u' is in the (!eps') component via hu_comp
    have hu'_in_neps' : u' ∈ ⋃₀ {D | parCell (!eps') (A ∪ C) D} :=
      heq_neps' ▸ hu_comp
    -- Disjointness contradiction
    exact Set.eq_empty_iff_forall_notMem.mp
      (parCell_union_disjoint (A ∪ C) eps') u'
      ⟨hu'_eps'_mem, hu'_in_neps'⟩

/-- HOL Light: `parity_even_cell` (line 41974).
For a rectagon G: `paritySelect G (squ m) = decide (evenCell G (squ m))`. -/
theorem paritySelect_eq_evenCell (G : Rectagon) (m : ℤ × ℤ) :
    paritySelect G.edges (squ m) = @decide (evenCell G.edges (squ m))
      (Classical.dec _) := by
  have h : paritySelect G.edges (squ m) = decide (Even (numLower G.edges m)) :=
    paritySelect_squ G.toSegment m
  rw [h]; simp [even_cell_squ]

/-- HOL Light: `par_cell_squ_neg` (line 41985).
`parCell (!eps) G (squ m) ↔ ¬ parCell eps G (squ m)` for segments. -/
theorem parCell_squ_neg (G : Segment) (m : ℤ × ℤ) (eps : Bool) :
    parCell (!eps) G.edges (squ m) ↔ ¬ parCell eps G.edges (squ m) := by
  constructor
  · intro h hpar
    exact parCell_disjoint G.edges eps (squ m) ⟨hpar, h⟩
  · intro h
    rcases parCell_cell_partition_segment G eps (squ m) ⟨.squ m, rfl⟩ with hT | hF | hc
    · exact absurd hT h
    · exact hF
    · exact absurd hc (curveCells_not_squ G m)

/-- HOL Light: `triple_par_cell_distinct` (line 42000).
In a psegment triple, `parCell eps (A ∪ B) ≠ parCell eps' (A ∪ C)`. -/
theorem triple_parCell_distinct (A B C : Finset (Set E2)) (eps eps' : Bool)
    (htrip : isPsegmentTriple A B C) :
    {e | parCell eps (A ∪ B) e} ≠ {e | parCell eps' (A ∪ C) e} := by
  intro h
  obtain ⟨_, ⟨sB, hsB, _⟩, _, ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, _,
          dAB, _, dBC, _, _, _, _, _⟩ := htrip
  -- Find e ∈ B \ (A ∪ C)
  obtain ⟨e, heB⟩ := sB.nonempty.coe_sort
  have heA : e ∉ A := Finset.disjoint_left.mp dAB.symm (hsB ▸ heB)
  have heC : e ∉ C := Finset.disjoint_left.mp dBC (hsB ▸ heB)
  have he_AB : e ∈ (A ∪ B : Finset (Set E2)) := Finset.mem_union.mpr (Or.inr (hsB ▸ heB))
  have he_nAC : e ∉ (A ∪ C : Finset (Set E2)) := by
    simp only [Finset.mem_union, not_or]; exact ⟨heA, heC⟩
  -- Abstract contradiction: if paritySelect differs for A∪B but agrees for A∪C at two squares → ⊥
  suffices h_abs : ∀ (s₁ s₂ : ℤ × ℤ),
      paritySelect (A ∪ B) (squ s₁) ≠ paritySelect (A ∪ B) (squ s₂) →
      paritySelect (A ∪ C) (squ s₁) = paritySelect (A ∪ C) (squ s₂) →
      False by
    -- Edge type case split
    rcases sB.all_edges e (hsB ▸ heB) with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- hEdge m: numLower changes for A∪B, stays for A∪C
      have keyAB : rAB.toSegment.edges = A ∪ B := hrAB
      have keyAC : rAC.toSegment.edges = A ∪ C := hrAC
      exact h_abs m (m.1, m.2 - 1)
        (by -- paritySelect(A∪B)(squ m) ≠ paritySelect(A∪B)(squ(m.1,m.2-1))
          have h1 := paritySelect_squ rAB.toSegment m
          have h2 := paritySelect_squ rAB.toSegment (m.1, m.2 - 1)
          rw [keyAB] at h1 h2; rw [h1, h2]
          have step := numLower_step (A ∪ B) m.1 m.2
          simp only [if_pos he_AB] at step; rw [step]
          intro heq
          have : ¬(Even (numLower (A ∪ B) (m.1, m.2 - 1) + 1) ↔
              Even (numLower (A ∪ B) (m.1, m.2 - 1))) := by
            intro ⟨h1, h2⟩
            rcases Nat.even_or_odd (numLower (A ∪ B) (m.1, m.2 - 1)) with he | ho
            · exact absurd (h2 he) (Nat.not_even_iff_odd.mpr (he.add_one))
            · exact absurd (h1 (ho.add_one)) (Nat.not_even_iff_odd.mpr ho)
          exact this (decide_eq_decide.mp heq))
        (by -- paritySelect(A∪C)(squ m) = paritySelect(A∪C)(squ(m.1,m.2-1))
          have h1 := paritySelect_squ rAC.toSegment m
          have h2 := paritySelect_squ rAC.toSegment (m.1, m.2 - 1)
          rw [keyAC] at h1 h2; rw [h1, h2]
          have step := numLower_step (A ∪ C) m.1 m.2
          simp only [if_neg he_nAC] at step; rw [step, Nat.add_zero])
    · -- vEdge m: squ_left_odd/even
      have keyAB : rAB.toSegment.edges = A ∪ B := hrAB
      have keyAC : rAC.toSegment.edges = A ∪ C := hrAC
      exact h_abs (left m) m
        (by -- paritySelect(A∪B)(squ(left m)) ≠ paritySelect(A∪B)(squ m)
          have hodd := squ_left_odd rAB m (show vEdge m ∈ rAB.edges by rw [hrAB]; exact he_AB)
          have h1 := paritySelect_squ rAB.toSegment (left m)
          have h2 := paritySelect_squ rAB.toSegment m
          rw [keyAB] at h1 h2; rw [h1, h2]
          intro heq; apply hodd
          rw [even_cell_squ, even_cell_squ, hrAB]; exact decide_eq_decide.mp heq)
        (by -- paritySelect(A∪C)(squ(left m)) = paritySelect(A∪C)(squ m)
          have heven := squ_left_even rAC m (show vEdge m ∉ rAC.edges by rw [hrAC]; exact he_nAC)
          have h1 := paritySelect_squ rAC.toSegment (left m)
          have h2 := paritySelect_squ rAC.toSegment m
          rw [keyAC] at h1 h2; rw [h1, h2]
          simp only [even_cell_squ, hrAC] at heven; exact decide_eq_decide.mpr heven)
  -- Prove the abstract contradiction
  intro s₁ s₂ hne heq
  -- From set equality h: parCell iff at every cell, in particular squ s₁ and squ s₂
  have hmem : ∀ m, parCell eps (A ∪ B) (squ m) ↔ parCell eps' (A ∪ C) (squ m) :=
    fun m => Set.ext_iff.mp h (squ m)
  -- Convert to paritySelect via pc_iff
  have keyAB : rAB.toSegment.edges = A ∪ B := hrAB
  have keyAC : rAC.toSegment.edges = A ∪ C := hrAC
  have pc_AB : ∀ m (b : Bool), parCell b (A ∪ B) (squ m) ↔
      b = paritySelect (A ∪ B) (squ m) := by
    intro m b; rw [← keyAB]; constructor
    · exact paritySelect_unique rAB.toSegment (squ m) b
    · intro hb; rw [hb]
      exact paritySelect_spec rAB.toSegment (squ m)
        ⟨.squ m, rfl⟩ (curveCells_not_squ rAB.toSegment m)
  have pc_AC : ∀ m (b : Bool), parCell b (A ∪ C) (squ m) ↔
      b = paritySelect (A ∪ C) (squ m) := by
    intro m b; rw [← keyAC]; constructor
    · exact paritySelect_unique rAC.toSegment (squ m) b
    · intro hb; rw [hb]
      exact paritySelect_spec rAC.toSegment (squ m)
        ⟨.squ m, rfl⟩ (curveCells_not_squ rAC.toSegment m)
  -- At s₁: (eps = ps_AB(s₁)) ↔ (eps' = ps_AC(s₁))
  have iff₁ : (eps = paritySelect (A ∪ B) (squ s₁)) ↔
      (eps' = paritySelect (A ∪ C) (squ s₁)) := by
    rw [← pc_AB s₁ eps, ← pc_AC s₁ eps']; exact hmem s₁
  -- At s₂: (eps = ps_AB(s₂)) ↔ (eps' = ps_AC(s₂))
  have iff₂ : (eps = paritySelect (A ∪ B) (squ s₂)) ↔
      (eps' = paritySelect (A ∪ C) (squ s₂)) := by
    rw [← pc_AB s₂ eps, ← pc_AC s₂ eps']; exact hmem s₂
  -- Since ps_AC(s₁) = ps_AC(s₂):
  rw [heq] at iff₁
  -- Now: (eps = ps_AB(s₁)) ↔ (eps' = ps_AC(s₂)) and (eps = ps_AB(s₂)) ↔ (eps' = ps_AC(s₂))
  -- So: (eps = ps_AB(s₁)) ↔ (eps = ps_AB(s₂))
  have : paritySelect (A ∪ B) (squ s₁) = paritySelect (A ∪ B) (squ s₂) := by
    rcases Bool.eq_false_or_eq_true eps with rfl | rfl <;>
    rcases Bool.eq_false_or_eq_true (paritySelect (A ∪ B) (squ s₁)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (paritySelect (A ∪ B) (squ s₂)) with h2 | h2 <;>
    simp_all
  exact hne this

/-- HOL Light: `triple_in_comp` (line 42117).
If C is not in parCell eps (A ∪ B), then C ⊆ parCell (!eps) (A ∪ B). -/
theorem triple_in_comp (A B C : Finset (Set E2)) (eps : Bool)
    (htrip : isPsegmentTriple A B C)
    (hC_not : ¬∀ e ∈ C, parCell eps (A ∪ B) e) :
    ∀ e ∈ C, parCell (!eps) (A ∪ B) e := by
  obtain ⟨_, _, ⟨sC, hsC, _⟩, ⟨rAB, hrAB⟩, _, _, _, dAC, dBC,
          _, h11, h12, h13, h14⟩ := htrip
  have h_disj : Disjoint sC.edges rAB.edges := by
    rw [hsC, hrAB]
    exact Finset.disjoint_union_right.mpr ⟨dAC.symm, dBC.symm⟩
  have h_cls : ∀ m, m ∈ cls rAB.edges ∩ cls sC.edges → sC.isEndpoint m := by
    intro m hm
    rw [hrAB, cls_union, hsC, Set.union_inter_distrib_right] at hm
    rw [Segment.isEndpoint, hsC]
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : m ∈ ({m | numClosure A m = 1} : Set (ℤ × ℤ)) := by
        rw [← h12]; exact ⟨h1, h2⟩
      rw [h13, h14] at this; exact this
    · have : m ∈ ({m | numClosure A m = 1} : Set (ℤ × ℤ)) := by
        rw [← h11]; exact ⟨h1, h2⟩
      rw [h13, h14] at this; exact this
  obtain ⟨eps', h_eps'⟩ := segment_in_comp rAB sC h_disj h_cls
  by_cases he : eps' = eps
  · subst he; exfalso; apply hC_not
    intro e heC
    have := h_eps' e (by rw [hsC]; exact heC)
    rw [hrAB] at this; exact this
  · have : eps' = !eps := by cases eps <;> cases eps' <;> simp_all
    subst this; intro e heC
    have := h_eps' e (by rw [hsC]; exact heC)
    rw [hrAB] at this; exact this

/-- HOL Light: `trap_odd_cell` (line 42143).
In a psegment triple, at least one segment lies entirely in parCell false of the
union of the other two. This is the main result of Section U. -/
theorem trap_odd_cell (A B C : Finset (Set E2))
    (htrip : isPsegmentTriple A B C) :
    (∀ e ∈ A, parCell false (B ∪ C) e) ∨
    (∀ e ∈ B, parCell false (A ∪ C) e) ∨
    (∀ e ∈ C, parCell false (A ∪ B) e) := by
  by_contra h_neg
  -- Recover ¬∀ forms
  have hA_neg : ¬∀ e ∈ A, parCell false (B ∪ C) e := by
    intro h; exact h_neg (Or.inl h)
  have hB_neg : ¬∀ e ∈ B, parCell false (A ∪ C) e := by
    intro h; exact h_neg (Or.inr (Or.inl h))
  have hC_neg : ¬∀ e ∈ C, parCell false (A ∪ B) e := by
    intro h; exact h_neg (Or.inr (Or.inr h))
  -- By triple_in_comp: each segment is in parCell true of the other union
  -- triple_in_comp A B C false trip hC_neg : isPsegmentTriple A B C required for C
  have hC_T : ∀ e ∈ C, parCell true (A ∪ B) e :=
    triple_in_comp A B C false htrip hC_neg
  -- For A: need isPsegmentTriple B C A — use rotate
  have hA_T : ∀ e ∈ A, parCell true (B ∪ C) e :=
    triple_in_comp B C A false (isPsegmentTriple_rotate htrip) hA_neg
  -- For B: need isPsegmentTriple C A B — use rotate∘rotate
  -- triple_in_comp gives ∀ e ∈ B, parCell true (C ∪ A) e
  have hB_neg' : ¬∀ e ∈ B, parCell false (C ∪ A) e := by
    rwa [Finset.union_comm] at hB_neg
  have hB_T' : ∀ e ∈ B, parCell true (C ∪ A) e :=
    triple_in_comp C A B false (isPsegmentTriple_rotate (isPsegmentTriple_rotate htrip)) hB_neg'
  have hB_T : ∀ e ∈ B, parCell true (A ∪ C) e := by
    intro e he; rw [Finset.union_comm]; exact hB_T' e he
  -- Key lemma: for A' B' with isPsegmentTriple A' B' C,
  -- C ⊆ T(A'∪B'), A' ⊆ T(B'∪C) → F(A'∪B') ⊆ T(B'∪C)
  have h_key : ∀ A' B' : Finset (Set E2),
      isPsegmentTriple A' B' C →
      (∀ e ∈ C, parCell true (A' ∪ B') e) →
      (∀ e ∈ A', parCell true (B' ∪ C) e) →
      ∀ e, parCell false (A' ∪ B') e → parCell true (B' ∪ C) e := by
    intro A' B' htrip' hC_T' hA_T' e he
    -- isPsegmentTriple B' A' C
    have htripBA'C : isPsegmentTriple B' A' C :=
      isPsegmentTriple_rotate (isPsegmentTriple_swap htrip')
    have hC_BA' : ∀ e ∈ C, parCell true (B' ∪ A') e := by
      intro e he; rw [Finset.union_comm]; exact hC_T' e he
    -- trap_triple_seg(B', A', C, F, T): F(B'∪A') → T(B'∪C) or F(B'∪A') → F(B'∪C)
    rcases trap_triple_seg B' A' C false true htripBA'C hC_BA' with hsub1 | hsub1
    · -- F(B'∪A') → T(B'∪C)
      exact hsub1 e (by rwa [Finset.union_comm])
    · -- F(B'∪A') → F(B'∪C)
      have htripBCA' : isPsegmentTriple B' C A' := isPsegmentTriple_rotate htrip'
      rcases trap_triple_seg B' C A' false false htripBCA' hA_T' with hsub2 | hsub2
      · -- F(B'∪C) → F(B'∪A')
        have heq : {e | parCell false (B' ∪ A') e} = {e | parCell false (B' ∪ C) e} := by
          ext x; exact ⟨hsub1 x, hsub2 x⟩
        exact absurd heq (triple_parCell_distinct B' A' C false false htripBA'C)
      · -- F(B'∪C) → T(B'∪A')
        have hF_BA : parCell false (B' ∪ A') e := by rwa [Finset.union_comm]
        have hT_BA : parCell true (B' ∪ A') e :=
          hsub2 e (hsub1 e hF_BA)
        exact absurd ⟨hT_BA, hF_BA⟩ (parCell_disjoint (B' ∪ A') true e)
  -- Apply h_key
  have hFAB_TBC : ∀ e, parCell false (A ∪ B) e → parCell true (B ∪ C) e :=
    h_key A B htrip hC_T hA_T
  have htripBA : isPsegmentTriple B A C :=
    isPsegmentTriple_rotate (isPsegmentTriple_swap htrip)
  have hFBA_TAC : ∀ e, parCell false (B ∪ A) e → parCell true (A ∪ C) e :=
    h_key B A htripBA (by intro e he; rw [Finset.union_comm]; exact hC_T e he) hB_T
  -- Extract segments and rectagon from htrip
  obtain ⟨⟨sA, hsA, hA_ps⟩, ⟨sB, hsB, hB_ps⟩, ⟨sC, hsC, _⟩,
          ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
          dAB, dAC, dBC, _, _, _, _, _⟩ := htrip
  -- Get u ∈ parCell false (A∪B) — nonempty
  obtain ⟨u, hu⟩ := parCell_nonempty rAB false
  rw [show rAB.edges = A ∪ B from hrAB] at hu
  -- u ∈ T(B∪C) and T(A∪C)
  have hu_BC : parCell true (B ∪ C) u := hFAB_TBC u hu
  have hu_AC : parCell true (A ∪ C) u :=
    hFBA_TAC u (by rw [Finset.union_comm]; exact hu)
  -- u is a cell
  have hu_cell : isCell u := parCell_isCell hu
  -- u ∉ curveCells X for X ∈ {A, B, C}
  have hAB_edge : ∀ f ∈ (A ∪ B : Finset (Set E2)), isEdge f :=
    fun f hf => rAB.all_edges f (hrAB ▸ hf)
  have hBC_edge : ∀ f ∈ (B ∪ C : Finset (Set E2)), isEdge f :=
    fun f hf => rBC.all_edges f (hrBC ▸ hf)
  have hncA : u ∉ curveCells A := by
    intro hcu
    have hmem : u ∈ curveCells (A ∪ B) := by
      rw [curveCells_union]; exact Set.mem_union_left _ hcu
    exact (Set.eq_empty_iff_forall_notMem.mp
      (parCell_curveCells_disjoint (A ∪ B) hAB_edge false) u ⟨hu, hmem⟩).elim
  have hncB : u ∉ curveCells B := by
    intro hcu
    have hmem : u ∈ curveCells (A ∪ B) := by
      rw [curveCells_union]; exact Set.mem_union_right _ hcu
    exact (Set.eq_empty_iff_forall_notMem.mp
      (parCell_curveCells_disjoint (A ∪ B) hAB_edge false) u ⟨hu, hmem⟩).elim
  have hncC : u ∉ curveCells C := by
    intro hcu
    have hmem : u ∈ curveCells (B ∪ C) := by
      rw [curveCells_union]; exact Set.mem_union_right _ hcu
    exact (Set.eq_empty_iff_forall_notMem.mp
      (parCell_curveCells_disjoint (B ∪ C) hBC_edge true) u ⟨hu_BC, hmem⟩).elim
  -- Apply paritySelect_union three times
  have hdAB : Disjoint sA.edges sB.edges := hsA ▸ hsB ▸ dAB
  have hdBC : Disjoint sB.edges sC.edges := hsB ▸ hsC ▸ dBC
  have hdAC : Disjoint sA.edges sC.edges := hsA ▸ hsC ▸ dAC
  have h_AB := paritySelect_union sA sB
    ⟨rAB.toSegment, by simp only [Rectagon.toSegment]; rw [hrAB, hsA, hsB]⟩
    hdAB u hu_cell (by rwa [hsA]) (by rwa [hsB])
  have h_BC := paritySelect_union sB sC
    ⟨rBC.toSegment, by simp only [Rectagon.toSegment]; rw [hrBC, hsB, hsC]⟩
    hdBC u hu_cell (by rwa [hsB]) (by rwa [hsC])
  have h_AC := paritySelect_union sA sC
    ⟨rAC.toSegment, by simp only [Rectagon.toSegment]; rw [hrAC, hsA, hsC]⟩
    hdAC u hu_cell (by rwa [hsA]) (by rwa [hsC])
  -- paritySelect_unique + rewrite
  have key_AB : paritySelect (A ∪ B) u = false := by
    have hrw : rAB.toSegment.edges = A ∪ B := hrAB
    have hu' : parCell false rAB.toSegment.edges u := by rwa [hrw]
    have h := paritySelect_unique rAB.toSegment u false hu'
    rw [hrw] at h; exact h.symm
  have key_BC : paritySelect (B ∪ C) u = true := by
    have hrw : rBC.toSegment.edges = B ∪ C := hrBC
    have hu' : parCell true rBC.toSegment.edges u := by rwa [hrw]
    have h := paritySelect_unique rBC.toSegment u true hu'
    rw [hrw] at h; exact h.symm
  have key_AC : paritySelect (A ∪ C) u = true := by
    have hrw : rAC.toSegment.edges = A ∪ C := hrAC
    have hu' : parCell true rAC.toSegment.edges u := by rwa [hrw]
    have h := paritySelect_unique rAC.toSegment u true hu'
    rw [hrw] at h; exact h.symm
  -- Rewrite paritySelect_union using segment edge equalities and key values
  rw [hsA, hsB] at h_AB; rw [hsB, hsC] at h_BC; rw [hsA, hsC] at h_AC
  rw [key_AB] at h_AB; rw [key_BC] at h_BC; rw [key_AC] at h_AC
  have hne_AB : paritySelect A u ≠ paritySelect B u := by
    intro h; simp [h] at h_AB
  have heq_BC : paritySelect B u = paritySelect C u := by
    by_contra h; simp [h] at h_BC
  have heq_AC : paritySelect A u = paritySelect C u := by
    by_contra h; simp [h] at h_AC
  -- A ≠ B, B = C, A = C ⟹ A = B — contradiction
  exact hne_AB (heq_AC.trans heq_BC.symm)

end JordanCurveTheorem
