/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionAA_RectagApprox

/-!
# Section BB: K₃,₃ Data Construction
## HOL Light: Section BB (Lines 54219–55681)

Construct the specific K₃,₃ graph data from a hypothetical one-sided
Jordan curve. Includes `jordan_curve_no_inj3`: there cannot exist three
points outside a simple closed curve such that every pair is connected
by an arc meeting the curve.

### Key theorems
- `jordan_curve_seg3`: A simple closed curve can be split into 3 disjoint simple arcs
- `simple_arc_sep_three_t`: Separate three arcs meeting at one point
- `k33_planar_graph_data_expand`: Expand K₃,₃ data with nice intersection properties
- `no_k33_planar_graph_data`: K₃,₃ graph data leads to False (using nonplanarity)
- `jordan_curve_no_inj3`: No 3 injective points outside a closed curve
  all pair-connected by arcs meeting the curve
-/

namespace JordanCurveTheorem

open Set Finset Metric Filter Topology

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: `fin_cases` on `Fin 3` for the 3-arc index and repeated `norm_num`
-- discharges on interval bound arithmetic (`1/8`, `3/8`, `5/8`, etc.) are slow to elaborate.
/-- HOL Light: `jordan_curve_seg3` (line 54225).
A simple closed curve can be split into 3 pairwise disjoint simple arcs. -/
theorem jordan_curve_seg3 {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    ∃ s : Fin 3 → Set E2',
      (∀ i, s i ⊆ C ∧ IsSimpleArc (s i)) ∧
      (∀ i j, (s i ∩ s j).Nonempty → i = j) := by
  obtain ⟨f, hfC, hcont, hinj, hperiod⟩ := hC
  -- Use intervals [(2k+1)/8, (2k+2)/8] for k=0,1,2 as disjoint subarcs
  let lo : Fin 3 → ℝ := ![1/8, 3/8, 5/8]
  let hi : Fin 3 → ℝ := ![1/4, 1/2, 3/4]
  have hbds : ∀ i : Fin 3, 0 < lo i ∧ lo i < hi i ∧ hi i < 1 := by
    intro i; fin_cases i <;> simp [lo, hi] <;> norm_num
  refine ⟨fun i => f '' Icc (lo i) (hi i), fun i => ?_, fun i j h => ?_⟩
  · constructor
    · -- Subset
      rw [hfC]; intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨t, ⟨(hbds i).1.le.trans ht.1, ht.2.trans (hbds i).2.2.le⟩, rfl⟩
    · -- SimpleArc
      exact isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_segment hcont hinj hperiod
        ⟨(hbds i).1.le, (hbds i).2.1, (hbds i).2.2.le, Or.inl (hbds i).1⟩)
  · obtain ⟨x, hxi, hxj⟩ := h
    obtain ⟨ti, hti, rfl⟩ := hxi
    obtain ⟨tj, htj, htjeq⟩ := hxj
    have hti_ico : ti ∈ Ico (0 : ℝ) 1 :=
      ⟨(hbds i).1.le.trans hti.1, hti.2.trans_lt (hbds i).2.2⟩
    have htj_ico : tj ∈ Ico (0 : ℝ) 1 :=
      ⟨(hbds j).1.le.trans htj.1, htj.2.trans_lt (hbds j).2.2⟩
    have heq := hinj htj_ico hti_ico htjeq; subst heq
    -- ti is in both intervals; derive contradiction for i ≠ j
    by_contra h_ne
    have h1 := hti.1; have h2 := hti.2; have h3 := htj.1; have h4 := htj.2
    -- lo i ≤ ti ≤ hi i, lo j ≤ ti ≤ hi j, so intervals overlap; but they don't when i ≠ j
    fin_cases i <;> fin_cases j <;> simp_all [lo, hi] <;> linarith

-- HOL Light: `abs3_distinct` (line 54321).
-- Not applicable to Lean: Fin 3 elements are pairwise distinct by `decide`.

-- HOL Light: `three_t_enum` (line 54336).
-- Not applicable to Lean: we use `![a, b, c]` directly.

/-- HOL Light: `three_t_univ` (line 54354).
A predicate holds for all of `Fin 3` if it holds for 0, 1, and 2. -/
theorem fin3_forall {P : Fin 3 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i; fin_cases i <;> assumption

/-- HOL Light: `simple_arc_sep_three_t` (line 54369).
Given three arcs from `x` to `p i` (i : Fin 3) with no cross-visits,
we can find refined arcs with pairwise singleton intersections. -/
theorem simple_arc_sep_three_t {C : Fin 3 → Set E2'} {x : E2'}
    {p : Fin 3 → E2'}
    (hC : ∀ i, IsSimpleArcEnd (C i) x (p i))
    (hCp : ∀ i j, p j ∈ C i → i = j) :
    ∃ (C' : Fin 3 → Set E2') (x' : E2'),
      (∀ i, IsSimpleArcEnd (C' i) x' (p i)) ∧
      (∀ i j, i ≠ j → C' i ∩ C' j = {x'}) ∧
      (∀ A : Set E2', (∀ i, C i ⊆ A) → ∀ i, C' i ⊆ A) := by
  have hpn : ∀ i j, i ≠ j → p j ∉ C i := fun i j h hm => h (hCp i j hm)
  obtain ⟨x', C₁', C₂', C₃', hSub, hC₁', hC₂', hC₃', h12, h23, h31⟩ :=
    simple_arc_sep (subset_refl (C 0 ∪ C 1 ∪ C 2))
      (hC 0) (hpn 0 1 (by decide)) (hpn 0 2 (by decide))
      (hC 1) (hpn 1 0 (by decide)) (hpn 1 2 (by decide))
      (hC 2) (hpn 2 0 (by decide)) (hpn 2 1 (by decide))
  refine ⟨![C₁', C₂', C₃'], x', fun i => ?_, fun i j hij => ?_, fun U hU i => ?_⟩
  · fin_cases i <;> simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · fin_cases i <;> fin_cases j <;>
      simp only [] at hij ⊢ <;>
      first | contradiction | exact h12 | exact h23 | exact h31
            | (rw [inter_comm]; first | exact h12 | exact h23 | exact h31)
  · have hAll : C₁' ∪ C₂' ∪ C₃' ⊆ U :=
      hSub.trans (union_subset (union_subset (hU 0) (hU 1)) (hU 2))
    fin_cases i <;>
      simp only [] <;>
      intro x hx <;> apply hAll
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

/-- HOL Light: `transpose` (line 54413).
Transpose a two-argument function. -/
def transpose' (Q : α → β → γ) (i : β) (j : α) : γ := Q j i

/-- HOL Light: `transpose2` (line 54419).
Double transposition is the identity. -/
theorem transpose'_transpose' (Q : α → β → γ) :
    transpose' (transpose' Q) = Q := by
  ext i j; rfl

/-- HOL Light: `k33_planar_graph_data_expand` (line 54428).
Given K₃,₃ graph data with basic properties, we can refine it so that
arcs sharing an endpoint have singleton intersection at that endpoint. -/
theorem k33_planar_graph_data_expand
    {q : Fin 3 → Fin 3 → E2'} {A : Fin 3 → E2'}
    {CA : Fin 3 → Fin 3 → Set E2'} {B : Fin 3 → E2'}
    {CB : Fin 3 → Fin 3 → Set E2'}
    (_hq_inj : ∀ i j i' j', q i j = q i' j' → i = i' ∧ j = j')
    (hCA : ∀ i j, IsSimpleArcEnd (CA i j) (A i) (q i j))
    (hCB : ∀ i j, IsSimpleArcEnd (CB i j) (B j) (q i j))
    (hCBCA : ∀ i j i' j' u, u ∈ CB i j → u ∈ CA i' j' →
      i = i' ∧ j = j' ∧ u = q i j)
    (hCA_row : ∀ i j i' j', (CA i j ∩ CA i' j').Nonempty → i = i')
    (hCB_col : ∀ i j i' j', (CB i j ∩ CB i' j').Nonempty → j = j') :
    ∃ (A' : Fin 3 → E2') (CA' : Fin 3 → Fin 3 → Set E2')
      (B' : Fin 3 → E2') (CB' : Fin 3 → Fin 3 → Set E2'),
      (∀ i j, IsSimpleArcEnd (CA' i j) (A' i) (q i j)) ∧
      (∀ i j, IsSimpleArcEnd (CB' i j) (B' j) (q i j)) ∧
      (∀ i j i' j' u, u ∈ CB' i j → u ∈ CA' i' j' →
        i = i' ∧ j = j' ∧ u = q i j) ∧
      (∀ i j i' j', (CA' i j ∩ CA' i' j').Nonempty → i = i') ∧
      (∀ i j i' j', (CB' i j ∩ CB' i' j').Nonempty → j = j') ∧
      (∀ i j k, j ≠ k → CA' i j ∩ CA' i k = {A' i}) ∧
      (∀ i j k, j ≠ k → CB' j i ∩ CB' k i = {B' i}) := by
  -- Step 1: Refine each row. For each i, apply simple_arc_sep_three_t to CA i
  have hrow : ∀ i, ∃ (CA'_i : Fin 3 → Set E2') (A'_i : E2'),
      (∀ j, IsSimpleArcEnd (CA'_i j) A'_i (q i j)) ∧
      (∀ j k, j ≠ k → CA'_i j ∩ CA'_i k = {A'_i}) ∧
      (∀ U, (∀ j, CA i j ⊆ U) → ∀ j, CA'_i j ⊆ U) := by
    intro i; apply simple_arc_sep_three_t (fun j => hCA i j)
    intro j j' hm
    exact ((hCBCA i j' i j _ (isSimpleArcEnd_mem_right (hCB i j')) hm).2.1).symm
  choose CA'₀ A'₀ hCA'₀_arc hCA'₀_inter hCA'₀_sub using hrow
  -- Step 2: Show refined CA' preserves row-disjointness
  have hCA'_row : ∀ i j i' j', (CA'₀ i j ∩ CA'₀ i' j').Nonempty → i = i' := by
    intro i j i' j' ⟨u, hu1, hu2⟩
    have h1 : ∃ k, u ∈ CA i k := by
      have := hCA'₀_sub i (⋃ k, CA i k) (fun j => subset_iUnion (CA i) j) j hu1
      exact mem_iUnion.mp this
    have h2 : ∃ k, u ∈ CA i' k := by
      have := hCA'₀_sub i' (⋃ k, CA i' k) (fun j => subset_iUnion (CA i') j) j' hu2
      exact mem_iUnion.mp this
    obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
    exact hCA_row i k1 i' k2 ⟨u, hk1, hk2⟩
  -- Step 3: Refine each column. For each j, apply simple_arc_sep_three_t to CB · j
  have hcol : ∀ j, ∃ (CB'_j : Fin 3 → Set E2') (B'_j : E2'),
      (∀ i, IsSimpleArcEnd (CB'_j i) B'_j (q i j)) ∧
      (∀ i k, i ≠ k → CB'_j i ∩ CB'_j k = {B'_j}) ∧
      (∀ U, (∀ i, CB i j ⊆ U) → ∀ i, CB'_j i ⊆ U) := by
    intro j; apply simple_arc_sep_three_t (fun i => hCB i j)
    intro i i' hm
    exact (hCBCA i j i' j _ hm (isSimpleArcEnd_mem_right (hCA i' j))).1
  choose CB'₀ B'₀ hCB'₀_arc hCB'₀_inter hCB'₀_sub using hcol
  -- Step 4: Show refined CB' preserves column-disjointness
  have hCB'_col : ∀ i j i' j', (CB'₀ j i ∩ CB'₀ j' i').Nonempty → j = j' := by
    intro i j i' j' ⟨u, hu1, hu2⟩
    have h1 : ∃ k, u ∈ CB k j := by
      have := hCB'₀_sub j (⋃ k, CB k j) (fun i => subset_iUnion (fun k => CB k j) i) i hu1
      exact mem_iUnion.mp this
    have h2 : ∃ k, u ∈ CB k j' := by
      have := hCB'₀_sub j' (⋃ k, CB k j') (fun i => subset_iUnion (fun k => CB k j') i) i' hu2
      exact mem_iUnion.mp this
    obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
    exact hCB_col k1 j k2 j' ⟨u, hk1, hk2⟩
  -- Step 5: Show cross condition for refined arcs
  have hCBCA' : ∀ i j i' j' u, u ∈ CB'₀ j i → u ∈ CA'₀ i' j' →
      i = i' ∧ j = j' ∧ u = q i j := by
    intro i j i' j' u hu_cb hu_ca
    -- Trace back to original arcs
    have ⟨k1, hk1⟩ : ∃ k, u ∈ CB k j := by
      have := hCB'₀_sub j (⋃ k, CB k j) (fun i => subset_iUnion (fun k => CB k j) i) i hu_cb
      exact mem_iUnion.mp this
    have ⟨k2, hk2⟩ : ∃ k, u ∈ CA i' k := by
      have := hCA'₀_sub i' (⋃ k, CA i' k) (fun j => subset_iUnion (CA i') j) j' hu_ca
      exact mem_iUnion.mp this
    have hcross := hCBCA k1 j i' k2 u hk1 hk2
    -- k1 = i', j = k2, u = q k1 j = q i' j
    have hk1_eq : k1 = i' := hcross.1
    have hk2_eq : k2 = j := hcross.2.1.symm
    have hu_eq : u = q i' j := by rw [hcross.2.2, hk1_eq]
    -- Now show i = i', j = j', u = q i j
    have hi_eq : i = i' := by
      by_contra h_ne
      have h_inter := hCB'₀_inter j i i' h_ne
      have hm : u ∈ CB'₀ j i ∩ CB'₀ j i' :=
        ⟨hu_cb, hu_eq ▸ isSimpleArcEnd_mem_right (hCB'₀_arc j i')⟩
      rw [h_inter] at hm; simp only [mem_singleton_iff] at hm
      -- u = B'₀ j, but also u = q i' j, so B'₀ j = q i' j
      -- But isSimpleArcEnd (CB'₀ j i') (B'₀ j) (q i' j) has distinct endpoints
      exact isSimpleArcEnd_distinct (hCB'₀_arc j i') (hm.symm ▸ hu_eq)
    have hj_eq : j = j' := by
      by_contra h_ne
      have h_inter := hCA'₀_inter i' j j' h_ne
      have hm : u ∈ CA'₀ i' j ∩ CA'₀ i' j' :=
        ⟨hu_eq ▸ isSimpleArcEnd_mem_right (hCA'₀_arc i' j), hu_ca⟩
      rw [h_inter] at hm; simp only [mem_singleton_iff] at hm
      exact isSimpleArcEnd_distinct (hCA'₀_arc i' j) (hm.symm ▸ hu_eq)
    exact ⟨hi_eq, hj_eq, by rw [hi_eq]; exact hu_eq⟩
  -- Package results
  exact ⟨A'₀, CA'₀, B'₀, fun i j => CB'₀ j i, fun i j => hCA'₀_arc i j,
    fun i j => hCB'₀_arc j i,
    fun i j i' j' u h1 h2 => hCBCA' i j i' j' u h1 h2,
    hCA'_row,
    fun i j i' j' h => hCB'_col i j i' j' h,
    fun i j k hjk => hCA'₀_inter i j k hjk,
    fun i j k hjk => hCB'₀_inter i j k hjk⟩

-- HOL Light: `three_t_size3` (line 54628).
-- Not applicable to Lean: `Fintype.card_fin 3` in Mathlib.

/-- HOL Light: `no_k33_planar_graph_data` (line 54637).
The existence of K₃,₃ graph data in the plane leads to a contradiction
(K₃,₃ is not planar). -/
theorem no_k33_planar_graph_data
    {q : Fin 3 → Fin 3 → E2'} {A : Fin 3 → E2'}
    {CA : Fin 3 → Fin 3 → Set E2'} {B : Fin 3 → E2'}
    {CB : Fin 3 → Fin 3 → Set E2'}
    (hq_inj : ∀ i j i' j', q i j = q i' j' → i = i' ∧ j = j')
    (hCA : ∀ i j, IsSimpleArcEnd (CA i j) (A i) (q i j))
    (hCB : ∀ i j, IsSimpleArcEnd (CB i j) (B j) (q i j))
    (hCBCA : ∀ i j i' j' u, u ∈ CB i j → u ∈ CA i' j' →
      i = i' ∧ j = j' ∧ u = q i j)
    (hCA_row : ∀ i j i' j', (CA i j ∩ CA i' j').Nonempty → i = i')
    (hCB_col : ∀ i j i' j', (CB i j ∩ CB i' j').Nonempty → j = j') :
    False := by
  -- Step 1: Get expanded data with singleton intersections
  obtain ⟨A', CA', B', CB', hCA', hCB', hCBCA', hCA'_row, hCB'_col, hCA'_sing, hCB'_sing⟩ :=
    k33_planar_graph_data_expand hq_inj hCA hCB hCBCA hCA_row hCB_col
  -- Step 2: Define edge arcs CE i j = CA' i j ∪ CB' i j
  -- Each CE i j is a simple arc from A' i to B' j
  have hCE_arc : ∀ i j, IsSimpleArcEnd (CA' i j ∪ CB' i j) (A' i) (B' j) := by
    intro i j
    apply isSimpleArcEnd_trans (hCA' i j)
    · exact isSimpleArcEnd_symm (hCB' i j)
    · ext x; constructor
      · rintro ⟨hx1, hx2⟩
        have := (hCBCA' i j i j x hx2 hx1).2.2
        simp only [mem_singleton_iff]; exact this
      · intro hx; simp only [mem_singleton_iff] at hx; subst hx
        exact ⟨isSimpleArcEnd_mem_right (hCA' i j), isSimpleArcEnd_mem_right (hCB' i j)⟩
    -- NOTE: need isSimpleArcEnd_symm to reverse CB' i j from (B' j, q i j) to (q i j, B' j)
  -- Step 3: Key injectivity and disjointness facts
  have hA'_inj : Function.Injective A' := fun i i' h =>
    hCA'_row i 0 i' 0 ⟨A' i, isSimpleArcEnd_mem_left (hCA' i 0),
      h ▸ isSimpleArcEnd_mem_left (hCA' i' 0)⟩
  have hB'_inj : Function.Injective B' := fun j j' h =>
    hCB'_col 0 j 0 j' ⟨B' j, isSimpleArcEnd_mem_left (hCB' 0 j),
      h ▸ isSimpleArcEnd_mem_left (hCB' 0 j')⟩
  have hAB'_ne : ∀ i j, A' i ≠ B' j := by
    intro i j h
    -- A' i ∈ CA' i j (left endpoint), if A' i = B' j, then B' j ∈ CA' i j
    -- Also B' j ∈ CB' i j (left endpoint of CB' i j from B' j to q i j)
    -- Cross condition: B' j ∈ CB' i j ∩ CA' i j implies B' j = q i j
    have h1 : A' i ∈ CA' i j := isSimpleArcEnd_mem_left (hCA' i j)
    have h2 : B' j ∈ CB' i j := isSimpleArcEnd_mem_left (hCB' i j)
    have h3 : A' i ∈ CB' i j := h ▸ h2
    have := (hCBCA' i j i j (A' i) h3 h1).2.2
    -- A' i = q i j, but A' i is left endpoint, q i j is right endpoint → distinct
    exact isSimpleArcEnd_distinct (hCA' i j) this
  -- Step 4: Auxiliary membership facts
  classical
  let CE : Fin 3 → Fin 3 → Set E2' := fun i j => CA' i j ∪ CB' i j
  -- A' i' ∈ CA' i j ⟹ i' = i
  have hCA'_mem_A : ∀ i i' j, A' i' ∈ CA' i j → i = i' :=
    fun i i' j h => hCA'_row i j i' j ⟨A' i', h, isSimpleArcEnd_mem_left (hCA' i' j)⟩
  -- B' j' ∈ CB' i j ⟹ j' = j
  have hCB'_mem_B : ∀ i j j', B' j' ∈ CB' i j → j = j' :=
    fun i j j' h => hCB'_col i j i j' ⟨B' j', h, isSimpleArcEnd_mem_left (hCB' i j')⟩
  -- ¬(A' i' ∈ CB' i j)
  have hCB'_not_A : ∀ i j i', A' i' ∉ CB' i j := by
    intro i j i' h
    have hall := hCBCA' i j i' j (A' i') h (isSimpleArcEnd_mem_left (hCA' i' j))
    have hi : i = i' := hall.1; subst hi
    exact isSimpleArcEnd_distinct (hCA' i j) hall.2.2
  -- ¬(B' j' ∈ CA' i j)
  have hCA'_not_B : ∀ i j j', B' j' ∉ CA' i j := by
    intro i j j' h
    have hall := hCBCA' i j' i j (B' j') (isSimpleArcEnd_mem_left (hCB' i j')) h
    exact isSimpleArcEnd_distinct (hCB' i j') hall.2.2
  -- Step 5: CE intersection properties
  -- CE i j ∩ range A' = {A' i}
  have hCE_A : ∀ i j, CE i j ∩ range A' = {A' i} := by
    intro i j; ext x
    simp only [CE, Set.mem_inter_iff, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx_ce, i', rfl⟩
      rcases hx_ce with hx | hx
      · exact congrArg A' (hCA'_mem_A i i' j hx).symm
      · exact absurd hx (hCB'_not_A i j i')
    · rintro rfl; exact ⟨Or.inl (isSimpleArcEnd_mem_left (hCA' i j)), i, rfl⟩
  -- CE i j ∩ range B' = {B' j}
  have hCE_B : ∀ i j, CE i j ∩ range B' = {B' j} := by
    intro i j; ext x
    simp only [CE, Set.mem_inter_iff, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx_ce, j', rfl⟩
      rcases hx_ce with hx | hx
      · exact absurd hx (hCA'_not_B i j j')
      · exact congrArg B' (hCB'_mem_B i j j' hx).symm
    · rintro rfl; exact ⟨Or.inr (isSimpleArcEnd_mem_left (hCB' i j)), j, rfl⟩
  -- CE i j ∩ CE i' j' nonempty ⟹ i = i' ∨ j = j'
  have hCE_rowcol : ∀ i j i' j', (CE i j ∩ CE i' j').Nonempty → i = i' ∨ j = j' := by
    intro i j i' j' ⟨u, hu1, hu2⟩
    by_contra h; push Not at h
    simp only [CE, Set.mem_union] at hu1 hu2
    rcases hu1 with h1 | h1 <;> rcases hu2 with h2 | h2
    · exact h.1 (hCA'_row i j i' j' ⟨u, h1, h2⟩)
    · exact h.1 (hCBCA' i' j' i j u h2 h1).1.symm
    · exact h.1 (hCBCA' i j i' j' u h1 h2).1
    · exact h.2 (hCB'_col i j i' j' ⟨u, h1, h2⟩)
  -- j ≠ j' ⟹ CE i j ∩ CE i j' = {A' i}
  have hCE_same_row : ∀ i j j', j ≠ j' → CE i j ∩ CE i j' = {A' i} := by
    intro i j j' hjj'; ext x
    simp only [CE, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · have := hCA'_sing i j j' hjj'
        rw [Set.eq_singleton_iff_unique_mem] at this
        exact this.2 x ⟨h1, h2⟩
      · exact absurd (hCBCA' i j' i j x h2 h1).2.1.symm hjj'
      · exact absurd (hCBCA' i j i j' x h1 h2).2.1 hjj'
      · exact absurd (hCB'_col i j i j' ⟨x, h1, h2⟩) hjj'
    · rintro rfl; exact ⟨Or.inl (isSimpleArcEnd_mem_left (hCA' i j)),
                          Or.inl (isSimpleArcEnd_mem_left (hCA' i j'))⟩
  -- i ≠ i' ⟹ CE i j ∩ CE i' j = {B' j}
  have hCE_same_col : ∀ i i' j, i ≠ i' → CE i j ∩ CE i' j = {B' j} := by
    intro i i' j hii'; ext x
    simp only [CE, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (hCA'_row i j i' j ⟨x, h1, h2⟩) hii'
      · exact absurd (hCBCA' i' j i j x h2 h1).1 hii'.symm
      · exact absurd (hCBCA' i j i' j x h1 h2).1 hii'
      · have := hCB'_sing j i i' hii'
        rw [Set.eq_singleton_iff_unique_mem] at this
        exact this.2 x ⟨h1, h2⟩
    · rintro rfl; exact ⟨Or.inr (isSimpleArcEnd_mem_left (hCB' i j)),
                          Or.inr (isSimpleArcEnd_mem_left (hCB' i' j))⟩
  -- Step 6: CE is injective
  have hCE_inj : ∀ i j i' j', CE i j = CE i' j' → i = i' ∧ j = j' := by
    intro i j i' j' heq
    have hinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc (hCE_arc i j))
    have hne : (CE i j ∩ CE i' j').Nonempty := by
      obtain ⟨x, hx⟩ := hinf.nonempty; exact ⟨x, hx, heq ▸ hx⟩
    rcases hCE_rowcol i j i' j' hne with hi | hj
    · subst hi; by_contra h
      have hjne : j ≠ j' := fun hj => h ⟨rfl, hj⟩
      have hfin := hCE_same_row i j j' hjne
      have hsub : CE i j ⊆ {A' i} := fun x hx =>
        hfin ▸ (⟨hx, heq ▸ hx⟩ : x ∈ CE i j ∩ CE i j')
      exact hinf.not_finite ((Set.finite_singleton _).subset hsub)
    · subst hj; by_contra h
      have hine : i ≠ i' := fun hi => h ⟨hi, rfl⟩
      have hfin := hCE_same_col i i' j hine
      have hsub : CE i j ⊆ {B' j} := fun x hx =>
        hfin ▸ (⟨hx, heq ▸ hx⟩ : x ∈ CE i j ∩ CE i' j)
      exact hinf.not_finite ((Set.finite_singleton _).subset hsub)
  -- Step 7: Construct Finsets and bijection
  let Afin : Finset E2' := Finset.image A' Finset.univ
  let Bfin : Finset E2' := Finset.image B' Finset.univ
  let g : Fin 3 × Fin 3 → Set E2' := fun p => CE p.1 p.2
  have hg_inj : Function.Injective g := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    exact Prod.ext (hCE_inj i j i' j' heq).1
      (hCE_inj i j i' j' heq).2
  let Efin : Finset (Set E2') := Finset.image g Finset.univ
  have hh_left : ∀ p, Function.invFun g (g p) = p :=
    congr_fun (Function.invFun_comp hg_inj)
  let f : Set E2' → E2' × E2' :=
    fun e => (A' (Function.invFun g e).1, B' (Function.invFun g e).2)
  have hAcard : Afin.card = 3 := by
    simp [Afin, Finset.card_image_of_injective _ hA'_inj]
  have hBcard : Bfin.card = 3 := by
    simp [Bfin, Finset.card_image_of_injective _ hB'_inj]
  have hdisj : Disjoint (Afin : Set E2') Bfin := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Afin, Bfin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at hx1 hx2
    obtain ⟨i, rfl⟩ := hx1; obtain ⟨j, hj⟩ := hx2
    exact hAB'_ne i j hj.symm
  -- Step 8: BijOn f Efin (Afin ×ˢ Bfin)
  have hbij : BijOn f (Efin : Set (Set E2'))
      ((Afin : Set E2') ×ˢ Bfin) := by
    constructor
    · -- MapsTo
      intro e he
      simp only [Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at he
      obtain ⟨⟨i, j⟩, rfl⟩ := he
      simp only [f, hh_left, Set.mem_prod, Finset.mem_coe, Afin, Bfin, Finset.mem_image]
      exact ⟨⟨i, Finset.mem_univ _, rfl⟩, ⟨j, Finset.mem_univ _, rfl⟩⟩
    constructor
    · -- InjOn
      intro e₁ he₁ e₂ he₂ hfe
      simp only [Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at he₁ he₂
      obtain ⟨⟨i₁, j₁⟩, rfl⟩ := he₁; obtain ⟨⟨i₂, j₂⟩, rfl⟩ := he₂
      simp only [f, hh_left, Prod.mk.injEq] at hfe
      have hi := hA'_inj hfe.1; have hj := hB'_inj hfe.2
      exact congrArg g (Prod.ext hi hj)
    · -- SurjOn
      intro ⟨a, b⟩ hab
      simp only [Afin, Bfin, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_prod,
                  Set.mem_range] at hab
      obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hab
      refine ⟨g (i, j), ?_, by simp [f, hh_left]⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  -- Step 9: Construct graph, apply k33_iso, and show plane graph
  have hwf : ∀ e ∈ (Efin : Set (Set E2')),
      {(f e).1, (f e).2} ⊆ (↑Afin : Set E2') ∪ ↑Bfin ∧
      ({(f e).1, (f e).2} : Set E2').ncard = 2 := by
    intro e he
    simp only [Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at he
    obtain ⟨⟨i, j⟩, rfl⟩ := he; simp only [f, hh_left]
    refine ⟨?_, Set.ncard_pair (hAB'_ne i j)⟩
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Set.mem_union_left _
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · exact Set.mem_union_right _
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  let G : HolGraph E2' (Set E2') :=
    ⟨↑Afin ∪ ↑Bfin, ↑Efin, fun e => {(f e).1, (f e).2}, hwf⟩
  have hiso : GraphIsomorphic K33 G := k33_iso hAcard hBcard hdisj hbij
  have hplane : IsPlaneGraph G := by
    constructor
    · -- edges_are_arcs: each edge is a simple arc
      intro e he
      simp only [G, Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
                  Set.mem_range] at he
      obtain ⟨⟨i, j⟩, rfl⟩ := he
      simp only [G, f, hh_left]
      exact ⟨A' i, B' j, Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl,
        hAB'_ne i j, hCE_arc i j⟩
    · -- vertex_on_edge: vertices on edge ⟹ incident
      intro e he v hv hve
      simp only [G, Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
      obtain ⟨⟨i, j⟩, rfl⟩ := he
      simp only [G, f, hh_left, Set.mem_insert_iff, Set.mem_singleton_iff]
      simp only [G, Afin, Bfin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
                  Set.mem_union, Set.mem_range] at hv
      rcases hv with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · have := hCE_A i j; rw [Set.eq_singleton_iff_unique_mem] at this
        exact Or.inl (this.2 _ ⟨hve, i', rfl⟩)
      · have := hCE_B i j; rw [Set.eq_singleton_iff_unique_mem] at this
        exact Or.inr (this.2 _ ⟨hve, j', rfl⟩)
    · -- edges_disjoint_interior: different edges only meet at vertices
      intro e₁ e₂ he₁ he₂ hne
      simp only [G, Efin, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at he₁ he₂
      obtain ⟨⟨i₁, j₁⟩, rfl⟩ := he₁; obtain ⟨⟨i₂, j₂⟩, rfl⟩ := he₂
      simp only [G, Afin, Bfin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have hne_ij : ¬(i₁ = i₂ ∧ j₁ = j₂) := by
        rintro ⟨rfl, rfl⟩; exact hne rfl
      intro x ⟨hx1, hx2⟩
      rcases hCE_rowcol i₁ j₁ i₂ j₂ ⟨x, hx1, hx2⟩ with hi | hj
      · subst hi; have hjne : j₁ ≠ j₂ := fun h => hne_ij ⟨rfl, h⟩
        have := hCE_same_row i₁ j₁ j₂ hjne
        rw [Set.eq_singleton_iff_unique_mem] at this
        have := this.2 x ⟨hx1, hx2⟩; subst this
        exact Set.mem_union_left _ (Set.mem_range.mpr ⟨i₁, rfl⟩)
      · subst hj; have hine : i₁ ≠ i₂ := fun h => hne_ij ⟨h, rfl⟩
        have := hCE_same_col i₁ i₂ j₁ hine
        rw [Set.eq_singleton_iff_unique_mem] at this
        have := this.2 x ⟨hx1, hx2⟩; subst this
        exact Set.mem_union_right _ (Set.mem_range.mpr ⟨j₁, rfl⟩)
  -- Step 11: K₃,₃ is planar → contradiction
  exact k33_nonplanar ⟨G, hplane, hiso⟩

/-- HOL Light: `simple_arc_midpoint` (line 55052).
A simple arc has an interior point (distinct from both endpoints). -/
theorem isSimpleArcEnd_midpoint {C : Set E2'} {v w : E2'}
    (hC : IsSimpleArcEnd C v w) :
    ∃ u, u ∈ C ∧ u ≠ v ∧ u ≠ w := by
  have hinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc hC)
  have hfin : Set.Finite ({v, w} : Set E2') := Set.Finite.insert v (Set.finite_singleton w)
  obtain ⟨u, hu⟩ := (hinf.diff hfin).nonempty
  rw [mem_diff] at hu
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
  exact ⟨u, hu.1, hu.2.1, hu.2.2⟩

/-- HOL Light: `simple_arc_choose_end` (line 55074).
Every simple arc has endpoints, i.e. is a `IsSimpleArcEnd`. -/
theorem isSimpleArc_choose_end {C : Set E2'} (hC : IsSimpleArc C) :
    ∃ v w, IsSimpleArcEnd C v w := by
  obtain ⟨f, hfC, hcont, hinj⟩ := hC
  exact ⟨f 0, f 1, f, hfC, hcont, hinj, rfl, rfl⟩

/-- HOL Light: `cut_arc_replace` (line 55091).
If A ⊆ B and both are simple arcs containing u, v with u ≠ v,
then `cutArc B u v = cutArc A u v`. -/
theorem cutArc_replace {A B : Set E2'} {u v : E2'}
    (hAB : A ⊆ B) (hA : IsSimpleArc A) (hB : IsSimpleArc B)
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) :
    cutArc B u v = cutArc A u v :=
  cutArc_unique hB ((cutArc_subset hA hu hv huv).trans hAB)
    (cutArc_isSimpleArcEnd hA hu hv huv)

/-- HOL Light: `cut_arc_order` (line 55113).
If `u` is an interior point of arc `C` from `v` to `w`,
then `w ∉ cutArc C v u`. -/
theorem cutArc_order {C : Set E2'} {u v w : E2'}
    (hC : IsSimpleArcEnd C v w) (hu : u ∈ C) (huv : u ≠ v) (huw : u ≠ w) :
    w ∉ cutArc C v u := by
  intro hw_in
  have hSA := isSimpleArcEnd_isSimpleArc hC
  have hinter := (cutArc_inter hC hu huv huw).1
  have hArc := cutArc_isSimpleArcEnd hSA hu (isSimpleArcEnd_mem_right hC) huw
  have hw_in2 := isSimpleArcEnd_mem_right hArc
  have : w ∈ cutArc C v u ∩ cutArc C u w := ⟨hw_in, hw_in2⟩
  rw [hinter] at this
  simp only [Set.mem_singleton_iff] at this
  exact huw this.symm

/-- HOL Light: `jordan_curve_no_inj3` (line 55139).
There cannot exist 3 injective points outside a simple closed curve
such that every pair is connected by an arc meeting the curve.
This is the first direction of the Jordan Curve Theorem. -/
theorem jordan_curve_no_inj3 {C : Set E2'} {p : Fin 3 → E2'}
    (hC : IsSimpleClosedCurve C)
    (hp_inj : Function.Injective p)
    (hp_out : ∀ i, p i ∉ C)
    (hp_conn : ∀ i j A, IsSimpleArcEnd A (p i) (p j) →
      (A ∩ C).Nonempty) :
    False := by
  -- Step 1: Split C into 3 disjoint simple arcs s 0, s 1, s 2
  obtain ⟨s, hs_sub_arc, hs_disj⟩ := jordan_curve_seg3 hC
  -- Step 2: For each arc s j, choose endpoints v j, w j and a midpoint B j
  have hs_end : ∀ j, ∃ v w, IsSimpleArcEnd (s j) v w := fun j =>
    isSimpleArc_choose_end (hs_sub_arc j).2
  choose v w hs_arc using hs_end
  have hB_mid : ∀ j, ∃ u, u ∈ s j ∧ u ≠ v j ∧ u ≠ w j := fun j =>
    isSimpleArcEnd_midpoint (hs_arc j)
  choose B hB_mem hB_nv hB_nw using hB_mid
  -- Step 3: For each (i,j), use jordan_curve_access to get arcs from p i to B j
  have hE_exists : ∀ i j, ∃ Eij : Set E2',
      IsSimpleArcEnd Eij (p i) (B j) ∧
      Eij ∩ C ⊆ s j ∧
      ∀ e, e ∈ Eij → e ∉ C → p i ≠ e → Disjoint (cutArc Eij (p i) e) C := by
    intro i j
    apply jordan_curve_access hC (hs_arc j) (hs_sub_arc j).1
      (hB_mem j) (hB_nv j) (hB_nw j) (hp_out i)
    obtain ⟨i', hi'⟩ := fin3_not_sing i
    exact ⟨p i', hp_inj.ne hi', hp_out i', hp_conn i i'⟩
  choose E hE_arc hE_sub hE_cut using hE_exists
  -- Step 4: Cross-visit properties of E
  -- If u ∈ E i j ∩ E i' j' ∩ C, then j = j'
  have hE_C_visit : ∀ i j i' j' u,
      u ∈ E i j → u ∈ E i' j' → u ∈ C → j = j' := by
    intro i j i' j' u h1 h2 hCu
    exact hs_disj j j'
      ⟨u, hE_sub i j ⟨h1, hCu⟩, hE_sub i' j' ⟨h2, hCu⟩⟩
  -- If u ∈ E i j ∩ E i' j' and u ∉ C, then i = i'
  have hE_nonC_visit : ∀ i j i' j' u, u ∈ E i j → u ∈ E i' j' → u ∉ C → i = i' := by
    intro i j i' j' u hu1 hu2 huC
    by_contra hne
    -- Build an arc from p i to p i' avoiding C
    have hpne : p i ≠ p i' := hp_inj.ne hne
    by_cases hupi : u = p i
    · -- u = p i: cutArc(E i' j', p i', p i) avoids C
      subst hupi
      have hSA := isSimpleArcEnd_isSimpleArc (hE_arc i' j')
      have hpi_ne : p i' ≠ p i := hpne.symm
      have hCA := cutArc_isSimpleArcEnd hSA hu2 (isSimpleArcEnd_mem_left (hE_arc i' j')) hpi_ne.symm
      have hDisj := hE_cut i' j' (p i) hu2 huC hpi_ne
      rw [cutArc_symm] at hDisj
      exact (hp_conn i' i _ (isSimpleArcEnd_symm hCA)).not_disjoint hDisj
    · by_cases hupi' : u = p i'
      · -- u = p i': cutArc(E i j, p i, p i') avoids C
        subst hupi'
        have hSA := isSimpleArcEnd_isSimpleArc (hE_arc i j)
        have hCA := cutArc_isSimpleArcEnd hSA (isSimpleArcEnd_mem_left (hE_arc i j)) hu1 hpne
        have hDisj := hE_cut i j (p i') hu1 huC hpne
        exact (hp_conn i i' _ hCA).not_disjoint hDisj
      · -- u ≠ p i, u ≠ p i': combine two cutArcs avoiding C
        have hSA1 := isSimpleArcEnd_isSimpleArc (hE_arc i j)
        have hSA2 := isSimpleArcEnd_isSimpleArc (hE_arc i' j')
        have hCA1 := cutArc_isSimpleArcEnd hSA1 (isSimpleArcEnd_mem_left (hE_arc i j)) hu1
          (Ne.symm hupi)
        have hDisj1 := hE_cut i j u hu1 huC (Ne.symm hupi)
        have hCA2 := cutArc_isSimpleArcEnd hSA2 (isSimpleArcEnd_mem_left (hE_arc i' j')) hu2
          (Ne.symm hupi')
        have hDisj2 := hE_cut i' j' u hu2 huC (Ne.symm hupi')
        obtain ⟨U, hU_arc, hU_sub⟩ := isSimpleArcEnd_subset_trans hCA1
          (isSimpleArcEnd_symm hCA2) hpne
        obtain ⟨x, hxU, hxC⟩ := hp_conn i i' U hU_arc
        rcases hU_sub hxU with hx1 | hx2
        · exact Set.disjoint_left.mp hDisj1 hx1 hxC
        · exact Set.disjoint_left.mp hDisj2 hx2 hxC
  -- Step 5: First restriction — extract subarcs E'' meeting other arcs at single points
  have hRestr1 : ∀ i j, ∃ E'' u'',
      E'' ⊆ E i j ∧ IsSimpleArcEnd E'' u'' (B j) ∧
      E'' ∩ (⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k) = {u''} ∧
      E'' ∩ {B j} = {B j} := by
    intro i j
    have hSA := isSimpleArcEnd_isSimpleArc (hE_arc i j)
    -- K = ⋃_{k≠j} E i k is closed (finite union of closed arcs)
    have hKcl : IsClosed (⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k) :=
      (Set.Finite.subset Set.finite_univ (Set.subset_univ _)).isClosed_biUnion
        (fun k _ => isSimpleArcEnd_isClosed (hE_arc i k))
    -- K' = {B j} is closed
    -- E ∩ K ∩ K' = ∅: B j ∈ s j, so B j ∈ C, and the cross-visit property implies
    -- E i k hits C only in s k; B j ∈ s j, so k = j, contradiction with k ≠ j
    have hdisj : (E i j) ∩ (⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k) ∩ {B j} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x ⟨⟨hx1, hx2⟩, hx3⟩
      simp only [Set.mem_singleton_iff] at hx3; subst hx3
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx2
      obtain ⟨k, hkj, hxk⟩ := hx2
      have hBjC : B j ∈ C := (hs_sub_arc j).1 (hB_mem j)
      have := hE_C_visit i j i k (B j) hx1 hxk hBjC
      exact hkj this.symm
    -- E ∩ K is nonempty (p i is in E i j and in E i j' for j' ≠ j)
    have hCK : ((E i j) ∩ (⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k)).Nonempty := by
      obtain ⟨j', hj'⟩ := fin3_not_sing j
      exact ⟨p i, isSimpleArcEnd_mem_left (hE_arc i j),
        Set.mem_biUnion hj'.symm (isSimpleArcEnd_mem_left (hE_arc i j'))⟩
    -- E ∩ {B j} is nonempty
    have hCK' : ((E i j) ∩ {B j}).Nonempty :=
      ⟨B j, isSimpleArcEnd_mem_right (hE_arc i j), Set.mem_singleton _⟩
    obtain ⟨D, v, v', hDsub, hD, hvK, hv'Bj⟩ :=
      isSimpleArcEnd_restriction hSA hKcl isClosed_singleton hdisj hCK hCK'
    -- v' = B j
    have hv'_eq : v' = B j :=
      Set.mem_singleton_iff.mp
        (hv'Bj ▸ Set.mem_singleton v' : v' ∈ D ∩ ({B j} : Set E2')).2
    subst hv'_eq
    exact ⟨D, v, hDsub, hD, hvK, hv'Bj⟩
  choose E'' u1 hE''_sub hE''_arc hE''_K hE''_Bj using hRestr1
  -- Step 6: Second restriction — extract subarcs E' meeting s j at single points
  have hRestr2 : ∀ i j, ∃ E' u' u₁',
      E' ⊆ E'' i j ∧ IsSimpleArcEnd E' u₁' u' ∧
      E' ∩ {u1 i j} = {u₁'} ∧ E' ∩ s j = {u'} := by
    intro i j
    have hSA := isSimpleArcEnd_isSimpleArc (hE''_arc i j)
    have hKcl : IsClosed {u1 i j} := isClosed_singleton
    have hK'cl : IsClosed (s j) := isSimpleArcEnd_isClosed (hs_arc j)
    -- E'' ∩ {u1} ∩ s j = ∅: u1 ∈ ⋃_{k≠j} E i k, so u1 ∈ E i k for some k ≠ j.
    -- Also u1 ∈ E'' ⊆ E i j. If u1 ∈ s j ⊆ C, then by cross-visit j = k, contra k ≠ j.
    have hdisj : (E'' i j) ∩ {u1 i j} ∩ s j = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro x ⟨⟨_, hx2⟩, hx3⟩
      simp only [Set.mem_singleton_iff] at hx2; subst hx2
      -- u1 i j ∈ E'' i j ∩ ⋃_{k≠j} E i k = {u1 i j}, so u1 ∈ some E i k with k ≠ j
      have hu1_mem : u1 i j ∈ ⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k := by
        have : u1 i j ∈ E'' i j ∩ (⋃ k ∈ ({k | k ≠ j} : Set (Fin 3)), E i k) :=
          hE''_K i j ▸ Set.mem_singleton _
        exact this.2
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hu1_mem
      obtain ⟨k, hkj, hxk⟩ := hu1_mem
      have hu1_E := hE''_sub i j (isSimpleArcEnd_mem_left (hE''_arc i j))
      have hxC : u1 i j ∈ C := (hs_sub_arc j).1 hx3
      exact hkj (hE_C_visit i j i k _ hu1_E hxk hxC).symm
    -- E'' ∩ {u1} is nonempty
    have hCK : ((E'' i j) ∩ {u1 i j}).Nonempty :=
      ⟨u1 i j, isSimpleArcEnd_mem_left (hE''_arc i j), Set.mem_singleton _⟩
    -- E'' ∩ s j is nonempty (B j ∈ E'' and B j ∈ s j)
    have hCK' : ((E'' i j) ∩ s j).Nonempty :=
      ⟨B j, isSimpleArcEnd_mem_right (hE''_arc i j), hB_mem j⟩
    obtain ⟨D, v, v', hDsub, hD, hvU, hv'sj⟩ :=
      isSimpleArcEnd_restriction hSA hKcl hK'cl hdisj hCK hCK'
    -- v = u1 i j
    have hv_eq : v = u1 i j := by
      have : v ∈ D ∩ {u1 i j} := hvU ▸ Set.mem_singleton v
      exact Set.mem_singleton_iff.mp this.2
    subst hv_eq
    exact ⟨D, v', u1 i j, hDsub, hD, hvU, hv'sj⟩
  choose E' u2 u1' hE'_sub hE'_arc hE'_u1 hE'_sj using hRestr2
  -- Show u1' = u1 (the left endpoint of E' equals the left endpoint from the first restriction)
  have hu1'_eq : ∀ i j, u1' i j = u1 i j := by
    intro i j
    exact Set.mem_singleton_iff.mp
      (hE'_u1 i j ▸ Set.mem_singleton (u1' i j) : u1' i j ∈ E' i j ∩ {u1 i j}).2
  -- Step 7: Choose midpoints q on E' arcs
  have hq_mid : ∀ i j, ∃ qij, qij ∈ E' i j ∧ qij ≠ u1 i j ∧ qij ≠ u2 i j := by
    intro i j; rw [← hu1'_eq]; exact isSimpleArcEnd_midpoint (hE'_arc i j)
  choose q hq_E' hq_nu1 hq_nu2 using hq_mid
  -- Key properties of q
  have hq_E'' : ∀ i j, q i j ∈ E'' i j := fun i j => hE'_sub i j (hq_E' i j)
  have hq_E : ∀ i j, q i j ∈ E i j := fun i j => hE''_sub i j (hq_E'' i j)
  have hq_not_sj : ∀ i j, q i j ∉ s j := by
    intro i j h
    have := hE'_sj i j ▸ (show q i j ∈ E' i j ∩ s j from ⟨hq_E' i j, h⟩)
    exact hq_nu2 i j (Set.mem_singleton_iff.mp this)
  have hq_not_C : ∀ i j, q i j ∉ C :=
    fun i j h => hq_not_sj i j (hE_sub i j ⟨hq_E i j, h⟩)
  -- CutArc ordering: cutArc(E i j, q, B j) only visits E i j (not E i k for k ≠ j)
  have hCB_col_key : ∀ i j k x, x ∈ E i k → x ∈ cutArc (E i j) (q i j) (B j) →
      j = k := by
    intro i j k x hxk hx_cut
    by_contra hjk
    -- cutArc(E i j, q, B j) = cutArc(E'' i j, q, B j) by cutArc_replace
    have hSA_E := isSimpleArcEnd_isSimpleArc (hE_arc i j)
    have hSA_E'' := isSimpleArcEnd_isSimpleArc (hE''_arc i j)
    have hq_B_ne : q i j ≠ B j := by
      intro h; exact hq_not_sj i j (h ▸ hB_mem j)
    have hcut_eq : cutArc (E i j) (q i j) (B j) = cutArc (E'' i j) (q i j) (B j) :=
      cutArc_replace (hE''_sub i j) hSA_E'' hSA_E (hq_E'' i j)
        (isSimpleArcEnd_mem_right (hE''_arc i j)) hq_B_ne
    rw [hcut_eq] at hx_cut
    -- x ∈ cutArc(E'' i j, q, B j) ⊆ E'' i j
    have hx_E'' : x ∈ E'' i j := cutArc_subset hSA_E'' (hq_E'' i j)
      (isSimpleArcEnd_mem_right (hE''_arc i j)) hq_B_ne hx_cut
    -- x ∈ E'' i j ∩ E i k, and k ≠ j, so x ∈ ⋃_{k'≠j} E i k'
    have hx_K : x ∈ E'' i j ∩ (⋃ k' ∈ ({k' | k' ≠ j} : Set (Fin 3)), E i k') :=
      ⟨hx_E'', Set.mem_biUnion (Ne.symm hjk) hxk⟩
    rw [hE''_K i j] at hx_K; simp only [Set.mem_singleton_iff] at hx_K
    -- x = u1 i j
    subst hx_K
    -- But u1 i j ∉ cutArc(E'' i j, q, B j) by cutArc_order + cutArc_symm
    have h_order : u1 i j ∉ cutArc (E'' i j) (B j) (q i j) := by
      apply cutArc_order (isSimpleArcEnd_symm (hE''_arc i j)) (hq_E'' i j)
        hq_B_ne (hq_nu1 i j)
    rw [cutArc_symm] at h_order
    exact h_order hx_cut
  -- Step 8: q i j ≠ p i
  have hq_ne_p : ∀ i j, q i j ≠ p i := by
    intro i j heq
    obtain ⟨j', hj'⟩ := fin3_not_sing j
    have hpi_ne_Bj : p i ≠ B j := fun h => hp_out i ((hs_sub_arc j).1 (h ▸ hB_mem j))
    have hSA := isSimpleArcEnd_isSimpleArc (hE_arc i j)
    have hcut : IsSimpleArcEnd (cutArc (E i j) (p i) (B j)) (p i) (B j) :=
      cutArc_isSimpleArcEnd hSA (isSimpleArcEnd_mem_left (hE_arc i j))
        (isSimpleArcEnd_mem_right (hE_arc i j)) hpi_ne_Bj
    have := hCB_col_key i j j' (p i) (isSimpleArcEnd_mem_left (hE_arc i j')) (by
      rw [heq]; exact isSimpleArcEnd_mem_left hcut)
    exact hj' this
  have hq_ne_B : ∀ i j, q i j ≠ B j := fun i j h => hq_not_sj i j (h ▸ hB_mem j)
  -- Step 9: Define CA and CB
  let CA : Fin 3 → Fin 3 → Set E2' := fun i j => cutArc (E i j) (p i) (q i j)
  let CB : Fin 3 → Fin 3 → Set E2' := fun i j => cutArc (E i j) (q i j) (B j)
  -- IsSimpleArcEnd properties
  have hCA_arc : ∀ i j, IsSimpleArcEnd (CA i j) (p i) (q i j) :=
    fun i j => cutArc_isSimpleArcEnd
      (isSimpleArcEnd_isSimpleArc (hE_arc i j))
      (isSimpleArcEnd_mem_left (hE_arc i j)) (hq_E i j) (hq_ne_p i j).symm
  have hCB_arc : ∀ i j, IsSimpleArcEnd (CB i j) (q i j) (B j) :=
    fun i j => cutArc_isSimpleArcEnd
      (isSimpleArcEnd_isSimpleArc (hE_arc i j))
      (hq_E i j) (isSimpleArcEnd_mem_right (hE_arc i j)) (hq_ne_B i j)
  -- CA ∩ C = ∅
  have hCA_disj : ∀ i j, Disjoint (CA i j) C := fun i j =>
    hE_cut i j (q i j) (hq_E i j) (hq_not_C i j) (hq_ne_p i j).symm
  -- CA ⊆ E, CB ⊆ E
  have hCA_sub : ∀ i j, CA i j ⊆ E i j := fun i j =>
    cutArc_subset (isSimpleArcEnd_isSimpleArc (hE_arc i j))
      (isSimpleArcEnd_mem_left (hE_arc i j)) (hq_E i j) (hq_ne_p i j).symm
  have hCB_sub : ∀ i j, CB i j ⊆ E i j := fun i j =>
    cutArc_subset (isSimpleArcEnd_isSimpleArc (hE_arc i j))
      (hq_E i j) (isSimpleArcEnd_mem_right (hE_arc i j)) (hq_ne_B i j)
  -- Step 10: Apply no_k33_planar_graph_data with A := p, B := B
  apply no_k33_planar_graph_data (A := p) (B := B) (CA := CA)
    (CB := fun i j => CB i j) (q := q)
  · -- q_inj: q i j = q i' j' → i = i' ∧ j = j'
    intro i j i' j' heq
    -- q i j ∈ CB i j (left endpoint) and q i' j' ∈ CA i' j' (right endpoint)
    have h1 : q i j ∈ CB i j := isSimpleArcEnd_mem_left (hCB_arc i j)
    have h2 : q i j ∈ CA i' j' := heq ▸ isSimpleArcEnd_mem_right (hCA_arc i' j')
    -- Both in E i j and E i' j'
    have h1E : q i j ∈ E i j := hCB_sub i j h1
    have h2E : q i j ∈ E i' j' := hCA_sub i' j' h2
    have hi : i = i' := hE_nonC_visit i j i' j' _ h1E h2E (hq_not_C i j)
    subst hi
    exact ⟨rfl, hCB_col_key i j j' (q i j) h2E h1⟩
  · -- hCA: IsSimpleArcEnd (CA i j) (p i) (q i j)
    exact hCA_arc
  · -- hCB: IsSimpleArcEnd (CB i j) (B j) (q i j)
    intro i j; exact isSimpleArcEnd_symm (hCB_arc i j)
  · -- hCBCA: cross condition
    intro i j i' j' u hu_cb hu_ca
    -- u ∈ CB i j ⊆ E i j, u ∈ CA i' j' ⊆ E i' j'
    have huE1 : u ∈ E i j := hCB_sub i j hu_cb
    have huE2 : u ∈ E i' j' := hCA_sub i' j' hu_ca
    by_cases hi : i = i'
    · -- i = i': determine j = j' and u = q i j
      subst hi
      -- j = j' from CB column key
      have hj : j = j' := hCB_col_key i j j' u huE2 hu_cb
      subst hj
      refine ⟨rfl, rfl, ?_⟩
      -- u ∈ CA i j ∩ CB i j = {q i j}
      have hinter := (cutArc_inter (hE_arc i j) (hq_E i j) (hq_ne_p i j) (hq_ne_B i j)).1
      have hmem : u ∈ cutArc (E i j) (p i) (q i j) ∩ cutArc (E i j) (q i j) (B j) :=
        ⟨hu_ca, hu_cb⟩
      rw [hinter] at hmem
      exact Set.mem_singleton_iff.mp hmem
    · -- i ≠ i': contradiction via CA ∩ C = ∅
      -- u ∈ CB i j ⊆ E i j, u ∈ CA i' j' ⊆ E i' j'
      -- If u ∈ C: impossible since u ∈ CA i' j' and CA i' j' ∩ C = ∅
      exfalso
      have huC : u ∉ C := Set.disjoint_left.mp (hCA_disj i' j') hu_ca
      exact hi (hE_nonC_visit i j i' j' u huE1 huE2 huC)
  · -- hCA_row: CA i j ∩ CA i' j' nonempty → i = i'
    intro i j i' j' ⟨u, hu1, hu2⟩
    have huE1 : u ∈ E i j := hCA_sub i j hu1
    have huE2 : u ∈ E i' j' := hCA_sub i' j' hu2
    have huC : u ∉ C := Set.disjoint_left.mp (hCA_disj i j) hu1
    exact hE_nonC_visit i j i' j' u huE1 huE2 huC
  · -- hCB_col: CB i j ∩ CB i' j' nonempty → j = j'
    intro i j i' j' ⟨u, hu1, hu2⟩
    by_cases hi : i = i'
    · -- Same row: use cutArc ordering
      subst hi
      exact hCB_col_key i j j' u (hCB_sub i j' hu2) hu1
    · -- Different rows: use cross-visit to show j = j'
      have huE1 : u ∈ E i j := hCB_sub i j hu1
      have huE2 : u ∈ E i' j' := hCB_sub i' j' hu2
      -- u ∈ CB i j ⊆ E i j; if u ∈ C then u ∈ s j. Also u ∈ E i' j',
      -- and if u ∈ C then E i' j' ∩ C ⊆ s j' gives u ∈ s j'.
      -- So u ∈ s j ∩ s j' gives j = j'.
      -- If u ∉ C then i = i' from non-C cross-visit, contradicting hi.
      by_cases huC : u ∈ C
      · exact hE_C_visit i j i' j' u huE1 huE2 huC
      · exact absurd (hE_nonC_visit i j i' j' u huE1 huE2 huC) hi

end JordanCurveTheorem
