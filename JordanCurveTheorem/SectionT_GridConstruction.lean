/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionS_BoundedUnbounded

/-!
# Section T: Rectagon Components and Bounded/Unbounded Regions
## HOL Light: Section T (Lines 39525–41109)

This section generalizes Section E curve-cell results from `Segment` to arbitrary
finite edge sets (`Finset (Set E2)` with `∀ e ∈ G, isEdge e`), and develops the
theory of bounded/unbounded components of the complement of a rectagon.

Key definitions:
- `Unbounded C` — the set `C` extends arbitrarily far to the right along the x-axis
- `UnboundedSet G x` — the connected component of `x` in `complementCurve G` is unbounded
- `BoundedSet G x` — the connected component of `x` is nonempty and not unbounded

Key results:
- For rectagons, the unbounded region equals the "even" parity cells
- For rectagons, the bounded region equals the "odd" parity cells (and is unique)
- Segment insertion and endpoint selection lemmas for the Jordan curve theorem
-/

open Set Metric Topology Function

namespace JordanCurveTheorem

/-! ## §T.1 Generalized curve cell lemmas (_ver2) -/

-- These generalize Section E results from `Segment` to `Finset (Set E2)`
-- with `∀ e ∈ G, isEdge e`. The originals in Section E only used `Segment`
-- for `G.all_edges`, so the generalizations are straightforward.

/-- HOL Light: `curve_cell_h_ver2` (line 39525).
`hEdge m ∈ curveCells G ↔ hEdge m ∈ G` for any finite edge set.
Trivially follows because `curveCells` is already defined for `Finset (Set E2)`
and `hEdge` is never a singleton point set. -/
theorem curveCells_hEdge_finset (G : Finset (Set E2))
    (_hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    hEdge m ∈ curveCells G ↔ hEdge m ∈ G := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro (h | ⟨n, heq, -⟩)
    · exact h
    · exact absurd heq (hEdge_ne_pointI_set m n)
  · exact Or.inl

/-- HOL Light: `curve_cell_v_ver2` (line 39539).
`vEdge m ∈ curveCells G ↔ vEdge m ∈ G` for any finite edge set. -/
theorem curveCells_vEdge_finset (G : Finset (Set E2))
    (_hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    vEdge m ∈ curveCells G ↔ vEdge m ∈ G := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro (h | ⟨n, heq, -⟩)
    · exact h
    · exact absurd heq (vEdge_ne_pointI_set m n)
  · exact Or.inl

/-- HOL Light: `curve_closure_ver2` (line 39553).
`closure(⋃₀ G) = ⋃₀ curveCells G` for any finite edge set. -/
theorem curve_closure_finset (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    closure (⋃₀ ↑G) = ⋃₀ (curveCells G : Set (Set E2)) := by
  apply subset_antisymm
  · -- ⊆: closure(⋃₀ edges) ⊆ ⋃₀ curveCells
    rw [((↑G : Set (Set E2)).toFinite).closure_sUnion]
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨e, he, hze⟩ := hz
    rcases hG e he with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- e = hEdge m
      rw [closure_hEdge] at hze
      obtain ⟨h1, h2, h3⟩ := hze
      rcases eq_or_lt_of_le h1 with h1eq | h1lt
      · have : z = pointI m := by
          ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
        subst this
        exact mem_sUnion.mpr ⟨{pointI m}, mem_union_right _ ⟨m, rfl,
          closure_mono (subset_sUnion_of_mem he)
            ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)⟩, rfl⟩
      · rcases lt_or_eq_of_le h2 with h2lt | h2eq
        · exact mem_sUnion.mpr ⟨hEdge m, mem_union_left _ he, h1lt, h2lt, h3⟩
        · have : z = pointI (m.1 + 1, m.2) := by
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
      · have : z = pointI m := by
          ext i; fin_cases i <;> simp [pointI_coord_fst, pointI_coord_snd]
 <;> linarith
        subst this
        exact mem_sUnion.mpr ⟨{pointI m}, mem_union_right _ ⟨m, rfl,
          closure_mono (subset_sUnion_of_mem he)
            ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)⟩, rfl⟩
      · rcases lt_or_eq_of_le h3 with h3lt | h3eq
        · exact mem_sUnion.mpr ⟨vEdge m, mem_union_left _ he, h1, h2lt, h3lt⟩
        · have : z = pointI (m.1, m.2 + 1) := by
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

/-- HOL Light: `curve_cell_h_inter_ver2` (line 39615).
A horizontal edge not in `G` has empty intersection with `⋃₀ G`. -/
theorem curveCells_hEdge_inter_finset (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    (m : ℤ × ℤ) (hm : hEdge m ∉ G) :
    hEdge m ∩ ⋃₀ ↑G = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z ⟨hz_h, hz_union⟩
  rw [Set.mem_sUnion] at hz_union
  obtain ⟨S, hSG, hz_S⟩ := hz_union
  rcases hG S hSG with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · by_cases heq : m = p
    · exact hm (heq ▸ hSG)
    · exact Set.disjoint_left.mp (cell_disjoint (show CellType.hEdge m ≠ CellType.hEdge p from
        fun h => heq (CellType.hEdge.inj h))) hz_h hz_S
  · exact Set.disjoint_left.mp
      (cell_disjoint (show CellType.hEdge m ≠ CellType.vEdge p from nofun)) hz_h hz_S

/-- HOL Light: `curve_cell_v_inter_ver2` (line 39633).
A vertical edge not in `G` has empty intersection with `⋃₀ G`. -/
theorem curveCells_vEdge_inter_finset (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    (m : ℤ × ℤ) (hm : vEdge m ∉ G) :
    vEdge m ∩ ⋃₀ ↑G = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z ⟨hz_v, hz_union⟩
  rw [Set.mem_sUnion] at hz_union
  obtain ⟨S, hSG, hz_S⟩ := hz_union
  rcases hG S hSG with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact Set.disjoint_left.mp
      (cell_disjoint (show CellType.vEdge m ≠ CellType.hEdge p from nofun)) hz_v hz_S
  · by_cases heq : m = p
    · exact hm (heq ▸ hSG)
    · exact Set.disjoint_left.mp (cell_disjoint (show CellType.vEdge m ≠ CellType.vEdge p from
        fun h => heq (CellType.vEdge.inj h))) hz_v hz_S

/-- HOL Light: `curve_cell_squ_ver2` (line 39651).
Squares are never in `curveCells G` for finite edge sets. -/
theorem curveCells_not_squ_finset (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    squ m ∉ curveCells G := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq, not_or]
  constructor
  · intro hmem
    rcases hG (squ m) hmem with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact absurd hn (squ_ne_hEdge m n)
    · exact absurd hn (squ_ne_vEdge m n)
  · push Not; intro n heq; exact absurd heq (squ_ne_pointI_set m n)

/-- HOL Light: `curve_cell_squ_inter_ver2` (line 39671).
Squares have empty intersection with the curve cells of a finite edge set. -/
theorem curveCells_squ_inter_finset (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    squ m ∩ ⋃₀ (curveCells G : Set (Set E2)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z ⟨hz_squ, hz_curve⟩
  rw [Set.mem_sUnion] at hz_curve
  obtain ⟨S, hS_mem, hz_S⟩ := hz_curve
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS_mem
  rcases hS_mem with hS_G | ⟨k, rfl, _⟩
  · rcases hG S hS_G with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact Set.disjoint_left.mp
        (cell_disjoint (show CellType.squ m ≠ CellType.hEdge p from nofun)) hz_squ hz_S
    · exact Set.disjoint_left.mp
        (cell_disjoint (show CellType.squ m ≠ CellType.vEdge p from nofun)) hz_squ hz_S
  · rw [mem_singleton_iff] at hz_S; exact squ_not_pointI m k (hz_S ▸ hz_squ)

/-- HOL Light: `curve_point_unions_ver2` (line 39690).
The union of curve cells equals `⋃₀ G ∪ {pointI m | pointI m ∈ closure(⋃₀ G)}`. -/
theorem curve_point_unions_finset (G : Finset (Set E2)) (_hG : ∀ e ∈ G, isEdge e) :
    ⋃₀ (curveCells G : Set (Set E2)) =
      ⋃₀ ↑G ∪
        {x | ∃ m : ℤ × ℤ, x = pointI m ∧ pointI m ∈ closure (⋃₀ ↑G)} := by
  ext z
  simp only [mem_sUnion, curveCells, mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro ⟨C, hC | ⟨m, rfl, hm⟩, hzC⟩
    · exact Or.inl ⟨C, hC, hzC⟩
    · rw [mem_singleton_iff] at hzC
      exact Or.inr ⟨m, hzC, hzC ▸ hm⟩
  · rintro (⟨C, hCG, hzC⟩ | ⟨m, rfl, hm⟩)
    · exact ⟨C, Or.inl hCG, hzC⟩
    · exact ⟨{pointI m}, Or.inr ⟨m, rfl, hm⟩, rfl⟩

/-- HOL Light: `curve_cell_not_point_ver2` (line 39716).
If `C ∈ curveCells G` and `C` is not a singleton point set, then `C ∈ G`. -/
theorem curveCells_not_point_finset (G : Finset (Set E2)) (_hG : ∀ e ∈ G, isEdge e)
    (C : Set E2) (hC : C ∈ curveCells G) (hpt : ∀ m : ℤ × ℤ, C ≠ {pointI m}) :
    C ∈ G := by
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hC
  rcases hC with h | ⟨m, rfl, _⟩
  · exact h
  · exact absurd rfl (hpt m)

/-- HOL Light: `curve_closed_ver2` (line 39738).
The union of curve cells of a finite edge set is closed. -/
theorem isClosed_curveCells_finset (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    IsClosed (⋃₀ (curveCells G : Set (Set E2))) := by
  rw [← curve_closure_finset G hG]; exact isClosed_closure

-- HOL Light 1079: `ctop_top2_ver2` — Not applicable to Lean: uses Mathlib topology directly.
-- HOL Light 1080: `convex_connected_ver2` — Not applicable to Lean: uses Mathlib's
--   `Convex.isPreconnected` directly.
-- HOL Light 1081: `convex_component_ver2` — Not applicable to Lean: uses Mathlib's
--   `IsPreconnected.subset_connectedComponentIn` directly.

/-- HOL Light: `unions_cell_of_ver2` (line 39844).
The cells of a connected component cover it, generalized to finite edge sets. -/
theorem unions_cellOf_component_finset (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) (x : E2) :
    ⋃₀ (cellOf' (connectedComponentIn (complementCurve G) x)) =
      connectedComponentIn (complementCurve G) x := by
  ext z; simp only [Set.mem_sUnion, cellOf', Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, ⟨_, hAK⟩, hzA⟩; exact hAK hzA
  · intro hzK
    have hzcomp : z ∈ complementCurve G := connectedComponentIn_subset _ _ hzK
    obtain ⟨ct, hzct, huniq⟩ := cell_partition z
    have hct_comp : ct.toSet ⊆ complementCurve G := by
      intro w hw
      simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion]; push Not
      intro S hS hwS
      obtain ⟨ct', rfl⟩ := curveCells_subset_cell G hG S hS
      have ⟨_, _, huniq'⟩ := cell_partition w
      have h_eq : ct = ct' := (huniq' ct hw).trans (huniq' ct' hwS).symm
      exact hzcomp (Set.mem_sUnion.mpr ⟨ct'.toSet, hS, h_eq ▸ hzct⟩)
    have hct_K : ct.toSet ⊆ connectedComponentIn (complementCurve G) x := by
      rw [connectedComponentIn_eq hzK]
      exact (cell_convex ct.toSet ⟨ct, rfl⟩).isPreconnected.subset_connectedComponentIn
        hzct hct_comp
    exact ⟨ct.toSet, ⟨⟨ct, rfl⟩, hct_K⟩, hzct⟩

/-! ## §T.2 Unbounded definition and curve cell basics -/

/-- A set is unbounded if it contains points `(s, 0)` for arbitrarily large `s`.
    HOL Light: `unbounded` (line 39890). -/
def Unbounded (C : Set E2) : Prop :=
  ∃ r : ℝ, ∀ s : ℝ, r ≤ s → point (s, 0) ∈ C

/-- HOL Light: `curve_cell_empty` (line 39898).
The curve cells of the empty edge set are empty. -/
theorem curveCells_empty : curveCells (∅ : Finset (Set E2)) = ∅ := by
  simp [curveCells, Finset.coe_empty, sUnion_empty]

/-- HOL Light: `curve_cell_union` (line 39913).
Curve cells distribute over union: `curveCells (A ∪ B) = curveCells A ∪ curveCells B`. -/
theorem curveCells_union (A B : Finset (Set E2)) :
    curveCells (A ∪ B) = curveCells A ∪ curveCells B := by
  simp only [curveCells, Finset.coe_union, sUnion_union, closure_union]
  ext C; simp only [mem_union, Finset.mem_coe, mem_setOf_eq]
  constructor
  · rintro ((hA | hB) | ⟨m, rfl, hm | hm⟩)
    · exact Or.inl (Or.inl hA)
    · exact Or.inr (Or.inl hB)
    · exact Or.inl (Or.inr ⟨m, rfl, hm⟩)
    · exact Or.inr (Or.inr ⟨m, rfl, hm⟩)
  · rintro ((hA | ⟨m, rfl, hm⟩) | (hB | ⟨m, rfl, hm⟩))
    · exact Or.inl (Or.inl hA)
    · exact Or.inr ⟨m, rfl, Or.inl hm⟩
    · exact Or.inl (Or.inr hB)
    · exact Or.inr ⟨m, rfl, Or.inr hm⟩

-- HOL Light 1086: `insert_sing` — Not applicable to Lean: this is just `Finset.insert_eq`.

/-- HOL Light: `curve_cell_sing` (line 39944).
Curve cells of a singleton edge set `{e}` where `isEdge e`. -/
theorem curveCells_sing (e : Set E2) (he : isEdge e) :
    curveCells ({e} : Finset (Set E2)) =
      {e} ∪ {{pointI m} | m ∈ {m : ℤ × ℤ | pointI m ∈ closure e}} := by
  ext C
  simp only [curveCells, Finset.coe_singleton, sUnion_singleton, mem_union,
    mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨m, rfl, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨m, hm, rfl⟩
  · rintro (rfl | ⟨m, hm, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl, hm⟩

/-! ## §T.3 Unbounded components -/

/-- HOL Light: `unbounded_elt` (line 39976).
Every curve cell is bounded in the x-coordinate direction. -/
theorem unbounded_elt (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    ∃ r : ℝ, ∀ x ∈ ⋃₀ (curveCells G : Set (Set E2)), x 0 < r := by
  revert hG
  induction G using Finset.induction with
  | empty =>
    intro _
    exact ⟨0, fun x hx => by simp [curveCells_empty] at hx⟩
  | @insert e G' hne ih =>
    intro hG
    have hG' : ∀ e' ∈ G', isEdge e' := fun e' he' => hG e' (Finset.mem_insert_of_mem he')
    have he : isEdge e := hG e (Finset.mem_insert_self e G')
    obtain ⟨r', hr'⟩ := ih hG'
    -- Bound x-coordinate for closure of single edge e
    obtain ⟨r_e, hr_e⟩ : ∃ r_e : ℝ, ∀ x ∈ closure e, x 0 < r_e := by
      rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨↑m.1 + 2, fun x hx => by rw [closure_hEdge] at hx; linarith [hx.2.1]⟩
      · exact ⟨↑m.1 + 1, fun x hx => by
          rw [closure_vEdge] at hx; linarith [hx.1]⟩
    -- Combine bounds using curveCells_union
    refine ⟨max r' r_e, fun x hx => ?_⟩
    have key : ⋃₀ (curveCells (insert e G') : Set (Set E2)) =
        closure e ∪ ⋃₀ (curveCells G' : Set (Set E2)) := by
      rw [Finset.insert_eq, curveCells_union, sUnion_union,
          ← curve_closure_finset {e} (fun e' he' => by rwa [Finset.mem_singleton.mp he'])]
      simp only [Finset.coe_singleton, Set.sUnion_singleton]
    rw [key] at hx
    rcases hx with h | h
    · exact lt_of_lt_of_le (hr_e x h) (le_max_right r' r_e)
    · exact lt_of_lt_of_le (hr' x h) (le_max_left r' r_e)

/-- HOL Light: `mk_segment_convex` (line 39998).
The segment `segment ℝ x y` is convex. -/
theorem segment_convex (x y : E2') : Convex ℝ (segment ℝ x y) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨t₁, ht₁0, ht₁1, rfl⟩ := mem_segment_iff_param.mp hu
  obtain ⟨t₂, ht₂0, ht₂1, rfl⟩ := mem_segment_iff_param.mp hv
  apply mem_segment_iff_param.mpr
  refine ⟨a * t₁ + b * t₂, add_nonneg (mul_nonneg ha ht₁0) (mul_nonneg hb ht₂0), ?_, ?_⟩
  · calc a * t₁ + b * t₂
        ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left ht₁1 ha)
            (mul_le_mul_of_nonneg_left ht₂1 hb)
      _ = 1 := by linarith
  · have h1 : a * (1 - t₁) + b * (1 - t₂) = 1 - (a * t₁ + b * t₂) := by linarith
    have h2 : a • (t₁ • x + (1 - t₁) • y) + b • (t₂ • x + (1 - t₂) • y) =
        (a * t₁ + b * t₂) • x + (a * (1 - t₁) + b * (1 - t₂)) • y := by module
    rw [h1] at h2; exact h2

/-- HOL Light: `mk_segment_h` (line 40026).
A horizontal segment between `(r, b)` and `(s, b)` with `r ≤ s`. -/
theorem segment_horizontal (r s b : ℝ) (hrs : r ≤ s) :
    segment ℝ (point (r, b)) (point (s, b)) =
      {z : E2 | ∃ t, r ≤ t ∧ t ≤ s ∧ z = point (t, b)} := by
  ext z
  simp only [mem_segment_iff_param, mem_setOf_eq, point_smul, point_add]
  constructor
  · rintro ⟨a, ha0, ha1, rfl⟩
    refine ⟨a * r + (1 - a) * s, by nlinarith, by nlinarith, ?_⟩
    exact congrArg point (Prod.ext rfl (by ring))
  · rintro ⟨t, htr, hts, rfl⟩
    by_cases heq : r = s
    · have ht : t = r := le_antisymm (by linarith) htr
      subst ht; subst heq
      exact ⟨0, le_refl _, zero_le_one,
        (congrArg point (Prod.ext (by ring) (by ring))).symm⟩
    · have hlt : r < s := lt_of_le_of_ne hrs heq
      have hne : (s - r : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
      refine ⟨(s - t) / (s - r), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith : (0 : ℝ) < s - r)).mpr (by linarith), ?_⟩
      exact (congrArg point (Prod.ext (by field_simp [hne]; ring) (by ring))).symm

/-- HOL Light: `unbounded_comp` (line 40086).
There exists a point whose connected component in `complementCurve G` is unbounded. -/
theorem unbounded_comp (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    ∃ x : E2, Unbounded (connectedComponentIn (complementCurve G) x) := by
  obtain ⟨r, hr⟩ := unbounded_elt G hG
  refine ⟨point (r, 0), r, fun s hrs => ?_⟩
  -- The segment from (r,0) to (s,0) lies in complementCurve G
  have hZ_sub : segment ℝ (point (r, 0)) (point (s, 0)) ⊆ complementCurve G := by
    rw [segment_horizontal r s 0 hrs]
    rintro z ⟨t, hrt, _, rfl⟩
    simp only [complementCurve, Set.mem_compl_iff]
    intro hmem
    have h := hr _ hmem; simp at h; linarith
  -- point(r, 0) is in the segment
  have hr_seg : point (r, 0) ∈ segment ℝ (point (r, 0)) (point (s, 0)) := by
    rw [segment_horizontal r s 0 hrs]; exact ⟨r, le_refl _, hrs, rfl⟩
  -- point(s, 0) is in the segment
  have hs_seg : point (s, 0) ∈ segment ℝ (point (r, 0)) (point (s, 0)) := by
    rw [segment_horizontal r s 0 hrs]; exact ⟨s, hrs, le_refl _, rfl⟩
  -- Convexity → preconnected → contained in component
  exact (segment_convex _ _).isPreconnected.subset_connectedComponentIn
    hr_seg hZ_sub hs_seg

/-- HOL Light: `unbounded_comp_unique` (line 40154).
All unbounded components are the same connected component. -/
theorem unbounded_comp_unique (G : Finset (Set E2)) (_hG : ∀ e ∈ G, isEdge e)
    {x y : E2}
    (hx : Unbounded (connectedComponentIn (complementCurve G) x))
    (hy : Unbounded (connectedComponentIn (complementCurve G) y)) :
    connectedComponentIn (complementCurve G) x =
      connectedComponentIn (complementCurve G) y := by
  obtain ⟨rx, hrx⟩ := hx
  obtain ⟨ry, hry⟩ := hy
  have hsx := hrx (max rx ry) (le_max_left _ _)
  have hsy := hry (max rx ry) (le_max_right _ _)
  exact (connectedComponentIn_eq hsx).trans (connectedComponentIn_eq hsy).symm

/-! ## §T.4 Bounded/Unbounded sets -/

/-- `UnboundedSet G x` holds when the connected component of `x` in
    `complementCurve G` is unbounded.
    HOL Light: `unbounded_set` (line 40225). -/
def UnboundedSet (G : Finset (Set E2)) (x : E2) : Prop :=
  Unbounded (connectedComponentIn (complementCurve G) x)

/-- `BoundedSet G x` holds when the connected component of `x` in
    `complementCurve G` is nonempty and not unbounded.
    HOL Light: `bounded_set` (line 40229). -/
def BoundedSet (G : Finset (Set E2)) (x : E2) : Prop :=
  (connectedComponentIn (complementCurve G) x).Nonempty ∧
    ¬Unbounded (connectedComponentIn (complementCurve G) x)

/-- HOL Light: `bounded_unbounded_disj` (line 40239).
`BoundedSet` and `UnboundedSet` are disjoint predicates. -/
theorem bounded_unbounded_disj (G : Finset (Set E2)) (x : E2) :
    ¬(BoundedSet G x ∧ UnboundedSet G x) := by
  rintro ⟨⟨_, hb⟩, hu⟩
  exact hb hu

/-- HOL Light: `bounded_unbounded_union` (line 40253).
Every point in the complement is either bounded or unbounded. -/
theorem bounded_unbounded_union (G : Finset (Set E2)) (_hG : ∀ e ∈ G, isEdge e)
    {x : E2} (hx : x ∈ complementCurve G) :
    BoundedSet G x ∨ UnboundedSet G x := by
  by_cases h : Unbounded (connectedComponentIn (complementCurve G) x)
  · exact Or.inr h
  · exact Or.inl ⟨⟨x, mem_connectedComponentIn hx⟩, h⟩

/-- HOL Light: `bounded_subset_unions` (line 40289).
Bounded points lie in the complement of the curve. -/
theorem bounded_subset_complementCurve (G : Finset (Set E2)) :
    {x | BoundedSet G x} ⊆ complementCurve G := by
  intro x ⟨hne, _⟩
  exact connectedComponentIn_nonempty_iff.mp hne

/-- HOL Light: `unbounded_subset_unions` (line 40306).
Unbounded points lie in the complement of the curve. -/
theorem unbounded_subset_complementCurve (G : Finset (Set E2)) :
    {x | UnboundedSet G x} ⊆ complementCurve G := by
  intro x hx
  obtain ⟨r, hr⟩ := hx
  have := hr r le_rfl
  exact connectedComponentIn_nonempty_iff.mp ⟨_, this⟩

/-- HOL Light: `unbounded_set_nonempty` (line 40322).
The set of unbounded points is nonempty for any finite edge set. -/
theorem unboundedSet_nonempty (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e) :
    ∃ x, UnboundedSet G x :=
  unbounded_comp G hG

/-- HOL Light: `unbounded_set_comp` (line 40339).
If `x` is unbounded, its connected component is exactly the set of all
unbounded points. -/
theorem unboundedSet_comp (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    {x : E2} (hx : UnboundedSet G x) :
    connectedComponentIn (complementCurve G) x = {y | UnboundedSet G y} := by
  ext y
  simp only [mem_setOf_eq]
  constructor
  · intro hy
    change Unbounded _
    rwa [(connectedComponentIn_eq hy).symm]
  · intro hy
    have heq := unbounded_comp_unique G hG hx hy
    have : y ∈ connectedComponentIn (complementCurve G) y :=
      mem_connectedComponentIn (unbounded_subset_complementCurve G hy)
    rwa [heq]

/-- HOL Light: `unbounded_set_comp_elt` (line 40361).
For unbounded `x` and any `y` in its component, `y` is also unbounded. -/
theorem unboundedSet_comp_elt (G : Finset (Set E2)) (hG : ∀ e ∈ G, isEdge e)
    {x y : E2} (hx : UnboundedSet G x)
    (hy : y ∈ connectedComponentIn (complementCurve G) x) :
    UnboundedSet G y := by
  rwa [unboundedSet_comp G hG hx] at hy

/-! ## §T.5 Parity and boundedness for rectagons -/

/-- If `hEdge m ⊆ closure (squ p)` then `p = m` or `p = down m`.
    HOL Light: `squc_h` (line 14227). -/
private theorem squc_h {m p : ℤ × ℤ} (h : hEdge m ⊆ closure (squ p)) :
    p = m ∨ p = down m := by
  have hcl : closure (hEdge m) ⊆ closure (squ p) := closure_minimal h isClosed_closure
  have hl : pointI m ∈ closure (squ p) :=
    hcl ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
  have hr : pointI (m.1 + 1, m.2) ∈ closure (squ p) :=
    hcl ((pointI_mem_closure_hEdge (m.1 + 1, m.2) m).mpr ⟨rfl, Or.inr rfl⟩)
  rw [squ_closure] at hl hr
  simp only [squc, mem_setOf_eq, pointI_coord_fst, pointI_coord_snd] at hl hr
  push_cast at hr
  have hp1 : p.1 = m.1 := by
    exact_mod_cast le_antisymm hl.1 (show (↑m.1 : ℝ) ≤ ↑p.1 by linarith [hr.2.1])
  have hp2 : p.2 = m.2 ∨ p.2 = m.2 - 1 := by
    have : p.2 ≤ m.2 := by exact_mod_cast (hl.2.2.1 : (↑p.2 : ℝ) ≤ ↑m.2)
    have : m.2 - 1 ≤ p.2 := by
      exact_mod_cast show (↑(m.2 - 1) : ℝ) ≤ ↑p.2 by push_cast; linarith [hl.2.2.2]
    omega
  rcases hp2 with h2 | h2
  · left; ext <;> omega
  · right; exact Prod.ext (by simp [down]; omega) (by simp [down]; omega)
/-- If `vEdge m ⊆ closure (squ p)` then `p = m` or `p = left m`.
    HOL Light: `squc_v` (line 14230 analog). -/
private theorem squc_v {m p : ℤ × ℤ} (h : vEdge m ⊆ closure (squ p)) :
    p = m ∨ p = left m := by
  have hcl : closure (vEdge m) ⊆ closure (squ p) := closure_minimal h isClosed_closure
  have hl : pointI m ∈ closure (squ p) :=
    hcl ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
  have hr : pointI (m.1, m.2 + 1) ∈ closure (squ p) :=
    hcl ((pointI_mem_closure_vEdge (m.1, m.2 + 1) m).mpr ⟨rfl, Or.inr rfl⟩)
  rw [squ_closure] at hl hr
  simp only [squc, mem_setOf_eq, pointI_coord_fst, pointI_coord_snd] at hl hr
  push_cast at hr
  have hp2 : p.2 = m.2 := by exact_mod_cast le_antisymm hl.2.2.1 (by linarith [hr.2.2.2])
  have hp1 : p.1 = m.1 ∨ p.1 = m.1 - 1 := by
    have h1 : p.1 ≤ m.1 := by exact_mod_cast (hl.1 : (↑p.1 : ℝ) ≤ ↑m.1)
    have h2 : m.1 - 1 ≤ p.1 := by
      have : (↑(m.1 - 1) : ℝ) ≤ ↑p.1 := by push_cast; linarith [hl.2.1]
      exact_mod_cast this
    omega
  rcases hp1 with h1 | h1
  · left; ext <;> omega
  · right; exact Prod.ext (by simp [left]; omega) (by simp [left]; omega)

-- Helper: non-G edge elimination at a shared vertex
private theorem notInG_of_ne_both (G : Segment) (m : ℤ × ℤ)
    {C C' e : Set E2} (hCG : C ∈ G.edges) (hC'G : C' ∈ G.edges)
    (hne : C ≠ C') (hmC : pointI m ∈ closure C) (hmC' : pointI m ∈ closure C')
    (hme : pointI m ∈ closure e) (heC : e ≠ C) (heC' : e ≠ C') :
    e ∉ G.edges := by
  intro he
  rcases midpoint_exclusion G m C C' e hCG hC'G he hne hmC hmC' hme with rfl | rfl
  · exact heC rfl
  · exact heC' rfl

-- Helper: adjacency closure for Segment.connected  (along_lemma9 in HOL Light)
-- Direct proof using comp_squ expansion through non-G edges at the shared vertex.
private theorem along_adj_step (G : Segment) (x : E2)
    {C C' : Set E2} (hCG : C ∈ G.edges) (hC'G : C' ∈ G.edges)
    (hadj : cellAdj C C')
    (hp : ∃ p, C ⊆ closure (squ p) ∧
      squ p ⊆ connectedComponentIn (complementCurve G.edges) x) :
    ∃ q, C' ⊆ closure (squ q) ∧
      squ q ⊆ connectedComponentIn (complementCurve G.edges) x := by
  obtain ⟨p, hCp, hpcomp⟩ := hp
  have hCe := G.all_edges C hCG
  have hC'e := G.all_edges C' hC'G
  set m := adjv C C'
  have hm_C := adjv_closure_left C C' hCe hC'e hadj
  have hm_C' := adjv_closure_right C C' hCe hC'e hadj
  have hne := hadj.2.2.1
  -- Any edge at m that is neither C nor C' is not in G.
  have notG : ∀ e, pointI m ∈ closure e → e ≠ C → e ≠ C' → e ∉ G.edges :=
    fun e he heC heC' => notInG_of_ne_both G m hCG hC'G hne hm_C hm_C' he heC heC'
  -- Closures for the 4 edges at m
  have hm_hm : pointI m ∈ closure (hEdge m) :=
    (pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩
  have hm_hlm : pointI m ∈ closure (hEdge (left m)) :=
    (pointI_mem_closure_hEdge m (left m)).mpr ⟨rfl, Or.inr (by simp [left])⟩
  have hm_vm : pointI m ∈ closure (vEdge m) :=
    (pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩
  have hm_vdm : pointI m ∈ closure (vEdge (down m)) :=
    (pointI_mem_closure_vEdge m (down m)).mpr ⟨by simp [down], Or.inr (by simp [down])⟩
  set comp := connectedComponentIn (complementCurve G.edges) x
  -- Step helpers: expand component through a non-G edge.
  have go_left : ∀ n, squ n ⊆ comp → vEdge n ∉ G.edges → squ (left n) ⊆ comp := by
    intro n hn hvn
    have h := comp_squ_left_rect G n x hn hvn
    rw [rectangle_v_decomp n] at h
    exact (Set.subset_union_left.trans Set.subset_union_left).trans h
  have go_right : ∀ n, squ n ⊆ comp →
      vEdge (right n) ∉ G.edges → squ (right n) ⊆ comp := by
    intro n hn hvn
    have h := comp_squ_right_rect G n x hn hvn
    have hrect : rectangle (n.1, n.2) (n.1 + 2, n.2 + 1) =
        rectangle ((right n).1 - 1, (right n).2) ((right n).1 + 1, (right n).2 + 1) := by
      congr 1 <;> ext <;> simp [right] ; omega
    rw [hrect, rectangle_v_decomp (right n)] at h
    exact Set.subset_union_right.trans h
  have go_down : ∀ n, squ n ⊆ comp → hEdge n ∉ G.edges → squ (down n) ⊆ comp := by
    intro n hn hhn
    have h := comp_squ_down_rect G n x hn hhn
    rw [rectangle_h_decomp n] at h
    exact (Set.subset_union_left.trans Set.subset_union_left).trans h
  have go_up : ∀ n, squ n ⊆ comp → hEdge (up n) ∉ G.edges → squ (up n) ⊆ comp := by
    intro n hn hhn
    have h := comp_squ_up_rect G n x hn hhn
    have hrect : rectangle (n.1, n.2) (n.1 + 1, n.2 + 2) =
        rectangle ((up n).1, (up n).2 - 1) ((up n).1 + 1, (up n).2 + 1) := by
      congr 1 <;> ext <;> simp [up] ; omega
    rw [hrect, rectangle_h_decomp (up n)] at h
    exact Set.subset_union_right.trans h
  -- Coordinate identities used throughout (precomputed)
  have lr_cancel : ∀ n : ℤ × ℤ, left (right n) = n := by
    intro n; ext <;> simp [left, right]
  have rl_cancel : ∀ n : ℤ × ℤ, right (left n) = n := by
    intro n; ext <;> simp [right, left]
  have ud_cancel : ∀ n : ℤ × ℤ, up (down n) = n := by
    intro n; ext <;> simp [up, down]
  have du_cancel : ∀ n : ℤ × ℤ, down (up n) = n := by
    intro n; ext <;> simp [down, up]
  have ld_eq_dl : ∀ n : ℤ × ℤ, left (down n) = down (left n) := by
    intro n; ext <;> simp [left, down]
  have rd_eq_dr : ∀ n : ℤ × ℤ, right (down n) = down (right n) := by
    intro n; ext <;> simp [right, down]
  -- Derive: given squ n ⊆ comp for some square at m, reach all 4 squares at m
  -- through the 2 non-G edges. The pattern depends on which edges are C, C'.
  -- We case-split on C being hEdge or vEdge, then on which vertex of C is m.
  -- Key: use named hypotheses from squc_h/squc_v (NOT rfl) to avoid Lean 4.29 rfl-elimination.
  --  squ (down (right n)) ⊆ comp := fun n h1 h2 h3 => go_down _ (go_right n h1 h2) h3
  have go_left_down : ∀ n, squ n ⊆ comp → vEdge n ∉ G.edges → hEdge (left n) ∉ G.edges →
      squ (down (left n)) ⊆ comp := fun n h1 h2 h3 => go_down _ (go_left n h1 h2) h3
  have go_right_up : ∀ n, squ n ⊆ comp →
      vEdge (right n) ∉ G.edges → hEdge (up (right n)) ∉ G.edges →
      squ (up (right n)) ⊆ comp := fun n h1 h2 h3 => go_up _ (go_right n h1 h2) h3
  have go_left_up : ∀ n, squ n ⊆ comp → vEdge n ∉ G.edges → hEdge (up (left n)) ∉ G.edges →
      squ (up (left n)) ⊆ comp := fun n h1 h2 h3 => go_up _ (go_left n h1 h2) h3
  have go_down_left : ∀ n, squ n ⊆ comp → hEdge n ∉ G.edges → vEdge (down n) ∉ G.edges →
      squ (left (down n)) ⊆ comp := fun n h1 h2 h3 => go_left _ (go_down n h1 h2) h3
  have go_down_right : ∀ n, squ n ⊆ comp → hEdge n ∉ G.edges → vEdge (right (down n)) ∉ G.edges →
      squ (right (down n)) ⊆ comp := fun n h1 h2 h3 => go_right _ (go_down n h1 h2) h3
  have go_up_left : ∀ n, squ n ⊆ comp → hEdge (up n) ∉ G.edges → vEdge (up n) ∉ G.edges →
      squ (left (up n)) ⊆ comp := fun n h1 h2 h3 => go_left _ (go_up n h1 h2) h3
  have go_up_right : ∀ n, squ n ⊆ comp → hEdge (up n) ∉ G.edges → vEdge (right (up n)) ∉ G.edges →
      squ (right (up n)) ⊆ comp := fun n h1 h2 h3 => go_right _ (go_up n h1 h2) h3
  rcases hCe with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- C = hEdge j. squc_h: p = j ∨ p = down j.
    rw [pointI_mem_closure_hEdge] at hm_C
    rcases squc_h hCp with hp_eq | hp_eq <;> subst p
    · -- p = j. squ j ⊆ comp, hEdge j ∈ G.
      rcases hm_C with ⟨hm2, hm1 | hm1⟩
      · -- m.1 = j.1, m.2 = j.2, so m = j.
        have hmj : m = j := Prod.ext (by omega) (by omega)
        have hadj_eq : adjv (hEdge j) C' = j := hmj
        clear_value m
        rw [hmj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · -- k = j → contradiction
            exact absurd (congrArg hEdge (Prod.ext hk1.symm hk2.symm : k = j)) hne.symm
          · -- k = left j
            have hkj : k = left j := Prod.ext (by simp [left]; omega) (by simp [left]; omega)
            subst hkj
            have hvm : vEdge j ∉ G.edges := notG _ hm_vm
              (fun h => absurd h (hEdge_ne_vEdge j j).symm)
              (fun h => absurd h (hEdge_ne_vEdge (left j) j).symm)
            exact ⟨left j, squ_closure_h (left j), go_left j hpcomp hvm⟩
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = j
            have hkj : k = j := Prod.ext hk1.symm hk2.symm
            rw [hkj]
            exact ⟨j, squ_closure_v j, hpcomp⟩
          · -- k = down j
            have hkj : k = down j := Prod.ext (by simp [down]; omega) (by simp [down]; omega)
            subst hkj
            have hvm : vEdge j ∉ G.edges := notG _ hm_vm
              (fun h => absurd h (hEdge_ne_vEdge j j).symm)
              ((vEdge_inj _ _).not.mpr (by simp [down, Prod.ext_iff]; omega))
            have hhlj : hEdge (left j) ∉ G.edges := notG _ hm_hlm
              ((hEdge_inj _ _).not.mpr (by simp [left, Prod.ext_iff]; try omega))
              (fun h => absurd h (hEdge_ne_vEdge (left j) (down j)))
            exact ⟨down (left j),
              ld_eq_dl j ▸ squ_closure_left_v (down j),
              go_down (left j) (go_left j hpcomp hvm) hhlj⟩
      · -- m.1 = j.1 + 1, m.2 = j.2, so m = right j.
        have hmrj : m = right j := Prod.ext (by simp [right]; omega) (by simp [right]; omega)
        have hadj_eq : adjv (hEdge j) C' = right j := hmrj
        clear_value m
        rw [hmrj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        -- Note: left(right j) = j, right(right j) = right(right j), etc.
        simp only [lr_cancel] at hm_hlm
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · -- k = right j. C' = hEdge(right j).
            have hkrj : k = right j := Prod.ext (by omega) (by omega)
            subst hkrj
            have hvm : vEdge (right j) ∉ G.edges := notG _ hm_vm
              (fun h => absurd h (hEdge_ne_vEdge j (right j)).symm)
              (fun h => absurd h (hEdge_ne_vEdge (right j) (right j)).symm)
            exact ⟨right j, squ_closure_h (right j),
              go_right j hpcomp hvm⟩
          · -- k = j → C' = hEdge j = C, contradiction
            exact absurd (congrArg hEdge (Prod.ext (by simp [right] at *; omega)
              (by simp [right] at *; omega) : k = j)) hne.symm
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = right j. vEdge(right j) ⊆ closure(squ j).
            have hkrj : k = right j := Prod.ext hk1.symm hk2.symm
            subst hkrj
            exact ⟨j, squ_closure_right_v j, hpcomp⟩
          · -- k = down(right j). C' = vEdge(down(right j)).
            have hkdrj : k = down (right j) := Prod.ext
              (by simp [down, right] at *; omega) (by simp [down, right] at *; omega)
            subst hkdrj
            have hvm : vEdge (right j) ∉ G.edges := notG _ hm_vm
              (fun h => absurd h (hEdge_ne_vEdge j (right j)).symm)
              ((vEdge_inj _ _).not.mpr (by simp [down, right, Prod.ext_iff]; omega))
            have hhm : hEdge (right j) ∉ G.edges := notG _ hm_hm
              ((hEdge_inj _ _).not.mpr (by simp [right, Prod.ext_iff]; try omega))
              (fun h => absurd h (hEdge_ne_vEdge (right j) (down (right j))))
            -- Path: squ j →[vEdge(right j)]→ squ(right j) →[hEdge(right j)]→ squ(down(right j))
            have hsrj := go_right j hpcomp hvm
            have hsdrj := go_down (right j) hsrj hhm
            exact ⟨down (right j), squ_closure_v (down (right j)), hsdrj⟩
    · -- p = down j. squ(down j) ⊆ comp, hEdge j ∈ G.
      rcases hm_C with ⟨hm2, hm1 | hm1⟩
      · -- m.1 = j.1, m.2 = j.2, so m = j.
        have hmj : m = j := Prod.ext (by omega) (by omega)
        have hadj_eq : adjv (hEdge j) C' = j := hmj
        clear_value m
        rw [hmj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · exact absurd (congrArg hEdge (Prod.ext hk1.symm hk2.symm : k = j)) hne.symm
          · have hkj : k = left j := Prod.ext (by simp [left]; omega) (by simp [left]; omega)
            subst hkj
            have hvdj : vEdge (down j) ∉ G.edges := notG _ hm_vdm
              (fun h => absurd h.symm (hEdge_ne_vEdge j (down j)))
              (fun h => absurd h.symm (hEdge_ne_vEdge (left j) (down j)))
            have hsdlj := go_left (down j) hpcomp hvdj
            rw [ld_eq_dl j] at hsdlj
            exact ⟨down (left j), squ_closure_down_h (left j), hsdlj⟩
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = j. C' = vEdge j. Path through non-G edges.
            have hjk : j = k := Prod.ext hk1 hk2
            subst hjk
            have hvdj : vEdge (down j) ∉ G.edges := notG _ hm_vdm
              (fun h => absurd h.symm (hEdge_ne_vEdge j (down j)))
              ((vEdge_inj _ _).not.mpr (by simp [down, Prod.ext_iff]; try omega))
            have hhlj : hEdge (left j) ∉ G.edges := notG _ hm_hlm
              ((hEdge_inj _ _).not.mpr (by simp [left, Prod.ext_iff]; try omega))
              (fun h => absurd h (hEdge_ne_vEdge (left j) j))
            have hsdlj := go_left (down j) hpcomp hvdj
            rw [ld_eq_dl j] at hsdlj
            have hslj := go_up (down (left j)) hsdlj (show hEdge (up (down (left j))) ∉ G.edges
              by rw [ud_cancel]; exact hhlj)
            rw [ud_cancel (left j)] at hslj
            exact ⟨left j, squ_closure_left_v j, hslj⟩
          · -- k = down j. vEdge(down j) ⊆ closure(squ(down j)).
            have hkj : k = down j := Prod.ext (by simp [down]; omega) (by simp [down]; omega)
            subst hkj
            exact ⟨down j, squ_closure_v (down j), hpcomp⟩
      · -- m.1 = j.1 + 1, m.2 = j.2, so m = right j.
        have hmrj : m = right j := Prod.ext (by simp [right]; omega) (by simp [right]; omega)
        have hadj_eq : adjv (hEdge j) C' = right j := hmrj
        clear_value m
        rw [hmrj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        simp only [lr_cancel] at hm_hlm
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · have hkrj : k = right j := Prod.ext (by omega) (by omega)
            subst hkrj
            have hvdrj : vEdge (down (right j)) ∉ G.edges := notG _ hm_vdm
              (fun h => absurd h (hEdge_ne_vEdge j (down (right j))).symm)
              (fun h => absurd h (hEdge_ne_vEdge (right j) (down (right j))).symm)
            have hrdj : right (down j) = down (right j) := by
              ext <;> simp [right, down]
            have hsdj := go_right (down j) hpcomp (hrdj ▸ hvdrj)
            rw [hrdj] at hsdj
            exact ⟨down (right j), squ_closure_down_h (right j), hsdj⟩
          · exact absurd (congrArg hEdge (Prod.ext (by simp [right] at *; omega)
              (by simp [right] at *; omega) : k = j)) hne.symm
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · have hkrj : k = right j := Prod.ext (by omega) (by omega)
            subst hkrj
            have hhrj : hEdge (right j) ∉ G.edges := notG _ hm_hm
              ((hEdge_inj _ _).not.mpr (by simp [right, Prod.ext_iff]; try omega))
              (fun h => absurd h (hEdge_ne_vEdge (right j) (right j)))
            have hvdrj : vEdge (down (right j)) ∉ G.edges := notG _ hm_vdm
              (hEdge_ne_vEdge j (down (right j))).symm
              ((vEdge_inj _ _).not.mpr (by simp [down, right, Prod.ext_iff]; try omega))
            have hrdj : right (down j) = down (right j) := by
              ext <;> simp [right, down]
            have hsdrj := go_right (down j) hpcomp (hrdj ▸ hvdrj)
            rw [hrdj] at hsdrj
            have hsrj := go_up (down (right j)) hsdrj (show hEdge (up (down (right j))) ∉ G.edges
              by rw [ud_cancel]; exact hhrj)
            rw [ud_cancel (right j)] at hsrj
            exact ⟨right j, squ_closure_v (right j), hsrj⟩
          · have hkdrj : k = down (right j) := Prod.ext
              (by simp [down, right] at *; omega) (by simp [down, right] at *; omega)
            subst hkdrj
            have hrdj : right (down j) = down (right j) := by
              ext <;> simp [right, down]
            exact ⟨down j, hrdj ▸ squ_closure_right_v (down j), hpcomp⟩
  · -- C = vEdge j. squc_v: p = j ∨ p = left j.
    rcases squc_v hCp with hp_eq | hp_eq <;> subst p
    · -- p = j. squ j ⊆ comp, vEdge j ∈ G.
      rw [pointI_mem_closure_vEdge] at hm_C
      rcases hm_C with ⟨hm1, hm2 | hm2⟩
      · -- m = j
        have hmj : m = j := Prod.ext (by omega) (by omega)
        have hadj_eq : adjv (vEdge j) C' = j := hmj
        exact along_lemma6 G j x C' hpcomp hCG hC'G (hadj_eq ▸ hm_C')
      · -- m = up j
        have hmuj : m = up j := Prod.ext (by simp [up]; omega) (by simp [up]; omega)
        have hadj_eq : adjv (vEdge j) C' = up j := hmuj
        clear_value m
        rw [hmuj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · -- k = up j. hEdge(up j) ⊆ closure(squ j).
            have hkuj : k = up j := Prod.ext (by simp [up] at *; omega) (by simp [up] at *; omega)
            subst hkuj
            exact ⟨j, squ_closure_up_h j, hpcomp⟩
          · -- k = left(up j). Navigate: squ j → squ(up j) → squ(left(up j)).
            have hkluj : k = left (up j) := Prod.ext
              (by simp [left, up] at *; omega) (by simp [left, up] at *; omega)
            subst hkluj
            have hhuj : hEdge (up j) ∉ G.edges := notG _ hm_hm
              (fun h => absurd h (hEdge_ne_vEdge (up j) j))
              ((hEdge_inj _ _).not.mpr (by simp [left, up, Prod.ext_iff] at *; try omega))
            have hvuj : vEdge (up j) ∉ G.edges := notG _ hm_vm
              ((vEdge_inj _ _).not.mpr (by simp [up, Prod.ext_iff] at *; try omega))
              (fun h => absurd h.symm (hEdge_ne_vEdge (left (up j)) (up j)))
            exact ⟨left (up j), squ_closure_h (left (up j)),
              go_left (up j) (go_up j hpcomp hhuj) hvuj⟩
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = up j. Navigate: squ j →[hEdge(up j)]→ squ(up j).
            have hkuj : k = up j := Prod.ext (by simp [up] at *; omega) (by simp [up] at *; omega)
            subst hkuj
            have hhuj : hEdge (up j) ∉ G.edges := notG _ hm_hm
              (fun h => absurd h (hEdge_ne_vEdge (up j) j))
              (fun h => absurd h (hEdge_ne_vEdge (up j) (up j)))
            exact ⟨up j, squ_closure_v (up j), go_up j hpcomp hhuj⟩
          · -- k = j → vEdge j = C, contradiction
            exact absurd (congrArg vEdge (Prod.ext (by simp [up] at *; omega)
              (by simp [up] at *; omega) : k = j)) hne.symm
    · -- p = left j. squ(left j) ⊆ comp, vEdge j ∈ G.
      rw [pointI_mem_closure_vEdge] at hm_C
      rcases hm_C with ⟨hm1, hm2 | hm2⟩
      · -- m.1 = j.1, m.2 = j.2, so m = j.
        have hmj : m = j := Prod.ext (by omega) (by omega)
        have hadj_eq : adjv (vEdge j) C' = j := hmj
        clear_value m
        rw [hmj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · -- k = j. Navigate: squ(left j) → squ(down(left j)) → squ(down j).
            have : j = k := Prod.ext hk1 hk2; subst this
            have hhlj : hEdge (left j) ∉ G.edges := notG _ hm_hlm
              (fun h => absurd h (hEdge_ne_vEdge (left j) j))
              ((hEdge_inj _ _).not.mpr (by simp [left, Prod.ext_iff]; try omega))
            have hvdj : vEdge (down j) ∉ G.edges := notG _ hm_vdm
              ((vEdge_inj _ _).not.mpr (by simp [down, Prod.ext_iff]; try omega))
              (fun h => absurd h (hEdge_ne_vEdge j (down j)).symm)
            have hsdlj := go_down (left j) hpcomp hhlj
            have hrdlj : right (down (left j)) = down j := by
              ext <;> simp [right, down, left]
            have hsdj := go_right (down (left j)) hsdlj (hrdlj ▸ hvdj)
            rw [hrdlj] at hsdj
            exact ⟨down j, squ_closure_down_h j, hsdj⟩
          · -- k = left j. hEdge(left j) ⊆ closure(squ(left j)).
            have hkj : k = left j :=
              Prod.ext (by simp [left] at *; omega) (by simp [left] at *; omega)
            subst hkj
            exact ⟨left j, squ_closure_h (left j), hpcomp⟩
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = j → C' = vEdge j = C, contradiction
            exact absurd (congrArg vEdge (Prod.ext hk1.symm hk2.symm : k = j)) hne.symm
          · -- k = down j. Navigate: squ(left j) →[hEdge(left j)]→ squ(down(left j)).
            have hkj : k = down j :=
              Prod.ext (by simp [down] at *; omega) (by simp [down] at *; omega)
            subst hkj
            have hhlj : hEdge (left j) ∉ G.edges := notG _ hm_hlm
              (fun h => absurd h (hEdge_ne_vEdge (left j) j))
              (fun h => absurd h (hEdge_ne_vEdge (left j) (down j)))
            exact ⟨down (left j), ld_eq_dl j ▸ squ_closure_left_v (down j),
              go_down (left j) hpcomp hhlj⟩
      · -- m.2 = j.2 + 1, so m = up j.
        have hmuj : m = up j := Prod.ext (by simp [up]; omega) (by simp [up]; omega)
        have hadj_eq : adjv (vEdge j) C' = up j := hmuj
        clear_value m
        rw [hmuj] at hm_vm hm_hlm hm_hm hm_vdm notG
        rw [hadj_eq] at hm_C'
        simp only [du_cancel] at hm_vdm
        rcases hC'e with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · -- C' = hEdge k
          rw [pointI_mem_closure_hEdge] at hm_C'
          rcases hm_C' with ⟨hk2, hk1 | hk1⟩
          · -- k = up j. Navigate: squ(left j) → squ(up(left j)) → squ(up j).
            have hkuj : k = up j := Prod.ext
              (by simp [up] at *; omega) (by simp [up] at *; omega)
            subst hkuj
            have hvuj : vEdge (up j) ∉ G.edges := notG _ hm_vm
              ((vEdge_inj _ _).not.mpr (by simp only [up, Prod.ext_iff]; omega))
              (fun h => absurd h (hEdge_ne_vEdge (up j) (up j)).symm)
            have hhluj : hEdge (left (up j)) ∉ G.edges := notG _ hm_hlm
              (fun h => absurd h (hEdge_ne_vEdge (left (up j)) j))
              ((hEdge_inj _ _).not.mpr (by simp only [left, up, Prod.ext_iff]; omega))
            have hsulj := go_up (left j) hpcomp hhluj
            -- right (up (left j)) = up j by computation
            have hrulj : right (up (left j)) = up j := by
              ext <;> simp [right, up, left]
            have hsuj := go_right (up (left j)) hsulj (show vEdge (right (up (left j))) ∉ G.edges
              by rw [hrulj]; exact hvuj)
            rw [hrulj] at hsuj
            exact ⟨up j, squ_closure_h (up j), hsuj⟩
          · -- k = left(up j). hEdge(left(up j)) ⊆ closure(squ(left j)).
            have hkluj : k = left (up j) := Prod.ext
              (by simp [left, up] at *; omega) (by simp [left, up] at *; omega)
            subst hkluj
            exact ⟨left j, squ_closure_up_h (left j), hpcomp⟩
        · -- C' = vEdge k
          rw [pointI_mem_closure_vEdge] at hm_C'
          rcases hm_C' with ⟨hk1, hk2 | hk2⟩
          · -- k = up j. Navigate: squ(left j) →[hEdge(up(left j))]→ squ(up(left j)).
            have hkuj : k = up j := Prod.ext
              (by simp only [up] at hk1 hk2 ⊢; omega) (by simp only [up] at hk1 hk2 ⊢; omega)
            subst hkuj
            have hhluj : hEdge (left (up j)) ∉ G.edges := notG _ hm_hlm
              (fun h => absurd h (hEdge_ne_vEdge (left (up j)) j))
              (fun h => absurd h (hEdge_ne_vEdge (left (up j)) (up j)))
            have hsulj := go_up (left j) hpcomp hhluj
            exact ⟨left (up j), squ_closure_left_v (up j), hsulj⟩
          · -- k = j → vEdge k = vEdge j = C, but C' ≠ C
            exact absurd (congrArg vEdge (Prod.ext (by simp only [up] at hk1 hk2 ⊢; omega)
              (by simp only [up] at hk1 hk2 ⊢; omega) : k = j)) (hne.symm)
/-- For a Segment G with nonempty component at x, every edge e ∈ G has a
    square witness: e ⊆ closure(squ p) with squ p in the component.
    HOL Light: `along_lemma11` (line 14892). -/
theorem along_lemma11 (G : Segment) (x : E2)
    (e : Set E2)
    (hne : (connectedComponentIn (complementCurve G.edges) x).Nonempty)
    (he : e ∈ G.edges) :
    ∃ p, e ⊆ closure (squ p) ∧
      squ p ⊆ connectedComponentIn (complementCurve G.edges) x := by
  set comp := connectedComponentIn (complementCurve G.edges) x
  set S : Set (Set E2) := {e' ∈ ↑G.edges |
    ∃ p, e' ⊆ closure (squ p) ∧ squ p ⊆ comp}
  suffices hS_eq : S = ↑G.edges by
    have : e ∈ S := hS_eq ▸ Finset.mem_coe.mpr he
    exact this.2
  apply G.connected S (fun _ he' => he'.1)
  · -- S is nonempty
    obtain ⟨m, hm⟩ := comp_contains_squ G x hne
    obtain ⟨p, e₀, he₀G, he₀sub, hpsub⟩ := comp_squ_adj G m x hm
    exact ⟨e₀, ⟨Finset.mem_coe.mpr he₀G, p, he₀sub, hpsub⟩⟩
  · -- S is adjacency-closed
    intro C hC C' hC'G hadj
    exact ⟨hC'G, along_adj_step G x (Finset.mem_coe.mp hC.1) (Finset.mem_coe.mp hC'G) hadj hC.2⟩


/-- The unbounded set is contained in the even parity cells.
    HOL Light: `unbounded_even_subset` (line 40272). -/
theorem unbounded_even_subset (G : Rectagon) :
    {x | UnboundedSet G.edges x} ⊆ ⋃₀ {C | parCell true G.edges C} := by
  intro x (hx : UnboundedSet G.edges x)
  rcases parCell_comp G true x with hT | hF
  · exact hT (mem_connectedComponentIn (unbounded_subset_complementCurve G.edges hx))
  · exfalso
    obtain ⟨r, hr⟩ := unbounded_elt G.edges G.all_edges
    obtain ⟨r', hr'⟩ := hx
    set s : ℤ := ⌊max r r'⌋ + 1
    have hs_r : r < (s : ℝ) := by
      have := Int.lt_floor_add_one (max r r')
      calc r ≤ max r r' := le_max_left _ _
        _ < ↑(⌊max r r'⌋ + 1) := by push_cast; linarith
    have hs_r' : r' ≤ (s : ℝ) := by
      have := Int.lt_floor_add_one (max r r')
      calc r' ≤ max r r' := le_max_right _ _
        _ ≤ ↑(⌊max r r'⌋ + 1) := by push_cast; linarith
    have hps : point (↑s, 0) ∈ connectedComponentIn (complementCurve G.edges) x :=
      hr' ↑s (by exact_mod_cast hs_r')
    have hps_F : point (↑s, 0) ∈ ⋃₀ {C | parCell false G.edges C} := hF hps
    have hps_eq : pointI (s, 0) = point (↑s, 0) := by
      ext i; fin_cases i <;> simp [pointI, point]
    have hps_not_curve : pointI (s, 0) ∉ ⋃₀ (curveCells G.edges : Set (Set E2)) := by
      intro hmem; have := hr (pointI (s, 0)) hmem
      simp only [pointI_coord_fst] at this; linarith
    have hnum : numClosure G.edges (s, 0) = 0 := by
      rw [numClosure_eq_zero_iff]; intro e he hcl
      exact hps_not_curve (Set.mem_sUnion.mpr ⟨{pointI (s, 0)},
        Set.mem_union_right _ ⟨(s, 0), rfl, closure_mono
          (Set.subset_sUnion_of_mem (Finset.mem_coe.mpr he)) hcl⟩,
        Set.mem_singleton _⟩)
    have hlow : numLower G.edges (s, 0) = 0 := by
      open Classical in
      unfold numLower
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      push Not; intro k hk hek
      rw [hek] at he
      have hcl : pointI (s, k) ∈ closure (⋃₀ ↑G.edges) :=
        closure_mono (Set.subset_sUnion_of_mem (Finset.mem_coe.mpr he))
          ((pointI_mem_closure_hEdge (s, k) (s, k)).mpr ⟨rfl, Or.inl rfl⟩)
      have hmem : pointI (s, k) ∈ ⋃₀ (curveCells G.edges : Set (Set E2)) :=
        Set.mem_sUnion.mpr ⟨{pointI (s, k)},
          Set.mem_union_right _ ⟨(s, k), rfl, hcl⟩, rfl⟩
      have h_in := hr (pointI (s, k)) hmem
      simp only [pointI_coord_fst] at h_in; linarith
    have hT : parCell true G.edges {pointI (s, 0)} :=
      (parCell_point G.toSegment (s, 0) true).mpr ⟨hnum, by
        change true = decide (Even (numLower G.edges (s, 0))); rw [hlow]; decide⟩
    have hps_T : pointI (s, 0) ∈ ⋃₀ {C | parCell true G.edges C} :=
      Set.mem_sUnion.mpr ⟨{pointI (s, 0)}, hT, Set.mem_singleton _⟩
    exact Set.eq_empty_iff_forall_notMem.mp
      (parCell_union_disjoint G.edges true) (pointI (s, 0))
      ⟨hps_T, hps_eq ▸ hps_F⟩

/-- HOL Light: `odd_bounded_subset` (line 40432).
The odd parity cells are contained in the bounded set. -/
theorem odd_bounded_subset (G : Rectagon) :
    ⋃₀ {C | parCell false G.edges C} ⊆ {x | BoundedSet G.edges x} := by
  intro x hx; change BoundedSet G.edges x
  constructor
  · -- x ∈ complementCurve G → comp x nonempty
    have hxcomp : x ∈ complementCurve G.edges := by
      change x ∈ complementCurve G.toSegment.edges
      rw [← parCell_partition G.toSegment true]
      exact Set.mem_union_right _ hx
    exact ⟨x, mem_connectedComponentIn hxcomp⟩
  · -- ¬ Unbounded
    intro hu
    have hxT := unbounded_even_subset G hu
    exact Set.eq_empty_iff_forall_notMem.mp
      (parCell_union_disjoint G.edges true) x ⟨hxT, hx⟩

/-- HOL Light: `unique_bounded` (line 40488).
For a rectagon, all bounded points lie in the same connected component. -/
theorem unique_bounded (G : Rectagon) {x y : E2}
    (hx : BoundedSet G.edges x) (hy : BoundedSet G.edges y) :
    connectedComponentIn (complementCurve G.edges) x =
      connectedComponentIn (complementCurve G.edges) y := by
  obtain ⟨m, hm⟩ := G.has_h_edge
  obtain ⟨u, hu⟩ := unboundedSet_nonempty G.edges G.all_edges
  have hu_ne : (connectedComponentIn (complementCurve G.edges) u).Nonempty := by
    obtain ⟨r, hr⟩ := hu; exact ⟨_, hr r le_rfl⟩
  obtain ⟨px, hpxs, hpxc⟩ := along_lemma11 G.toSegment x (hEdge m) hx.1 hm
  obtain ⟨py, hpys, hpyc⟩ := along_lemma11 G.toSegment y (hEdge m) hy.1 hm
  obtain ⟨pu, hpus, hpuc⟩ := along_lemma11 G.toSegment u (hEdge m) hu_ne hm
  -- px, py, pu ∈ {m, down m}
  have hpx := squc_h hpxs; have hpy := squc_h hpys; have hpu := squc_h hpus
  -- Helper: if two components share a square, they\'re equal
  have share : ∀ p : ℤ × ℤ, ∀ a b : E2,
      squ p ⊆ connectedComponentIn (complementCurve G.edges) a →
      squ p ⊆ connectedComponentIn (complementCurve G.edges) b →
      connectedComponentIn (complementCurve G.edges) a =
        connectedComponentIn (complementCurve G.edges) b := by
    intro p a b ha hb
    obtain ⟨z, hz⟩ := squ_nonempty p
    exact (connectedComponentIn_eq (ha hz)).trans (connectedComponentIn_eq (hb hz)).symm
  -- Helper: bounded ≠ unbounded component
  have bnd_ne_unb : ∀ a : E2, BoundedSet G.edges a →
      connectedComponentIn (complementCurve G.edges) a ≠
        connectedComponentIn (complementCurve G.edges) u := by
    intro a ha heq; exact ha.2 (heq ▸ hu)
  -- Pigeonhole: px, py, pu ∈ {m, down m} → some pair matches
  by_cases hxy : px = py
  · exact share px x y hpxc (hxy ▸ hpyc)
  · -- px ≠ py → pu matches one of them
    have : pu = px ∨ pu = py := by
      rcases hpx with h1 | h1 <;> rcases hpy with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · rcases hpu with h3 | h3
        · exact .inl (h3.trans h1.symm)
        · exact .inr (h3.trans h2.symm)
      · rcases hpu with h3 | h3
        · exact .inr (h3.trans h2.symm)
        · exact .inl (h3.trans h1.symm)
      · exact absurd (h1.trans h2.symm) hxy
    rcases this with rfl | rfl
    · exact absurd (share _ x u hpxc hpuc) (bnd_ne_unb x hx)
    · exact absurd (share _ y u hpyc hpuc) (bnd_ne_unb y hy)

/-- HOL Light: `odd_bounded` (line 40520).
The odd parity cells equal the bounded set. -/
theorem odd_bounded (G : Rectagon) :
    ⋃₀ {C | parCell false G.edges C} = {x | BoundedSet G.edges x} := by
  apply Set.Subset.antisymm (odd_bounded_subset G)
  intro x hx
  obtain ⟨C, hC⟩ := parCell_nonempty G false
  have hC_cell : isCell C := by
    obtain ⟨⟨n, hn, _⟩, _⟩ := hC
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨.point n, rfl⟩
    · exact ⟨.hEdge n, rfl⟩
    · exact ⟨.vEdge n, rfl⟩
    · exact ⟨.squ n, rfl⟩
  obtain ⟨z, hz⟩ := cell_nonempty hC_cell
  have hzF : z ∈ ⋃₀ {C | parCell false G.edges C} :=
    Set.mem_sUnion.mpr ⟨C, hC, hz⟩
  have hzB : BoundedSet G.edges z := odd_bounded_subset G hzF
  have heq := unique_bounded G hx hzB
  have hcomp_F : connectedComponentIn (complementCurve G.edges) z ⊆
      ⋃₀ {C | parCell false G.edges C} := by
    rcases parCell_comp G true z with hT | hF
    · exfalso
      exact Set.eq_empty_iff_forall_notMem.mp
        (parCell_union_disjoint G.edges true) z
        ⟨hT (mem_connectedComponentIn (bounded_subset_complementCurve G.edges hzB)), hzF⟩
    · exact hF
  exact hcomp_F (heq ▸ mem_connectedComponentIn
    (bounded_subset_complementCurve G.edges hx))

/-- HOL Light: `unbounded_even` (line 40559).
The unbounded set equals the even parity cells. -/
theorem unbounded_even (G : Rectagon) :
    {x | UnboundedSet G.edges x} = ⋃₀ {C | parCell true G.edges C} := by
  apply Set.Subset.antisymm (unbounded_even_subset G)
  intro x hx; change UnboundedSet G.edges x
  have hxcomp : x ∈ complementCurve G.edges := by
    change x ∈ complementCurve G.toSegment.edges
    rw [← parCell_partition G.toSegment true]; exact Set.mem_union_left _ hx
  rcases bounded_unbounded_union G.edges G.all_edges hxcomp with hB | hU
  · exfalso
    have hxF : x ∈ ⋃₀ {C | parCell false G.edges C} := by
      rw [odd_bounded G]; exact hB
    exact Set.eq_empty_iff_forall_notMem.mp
      (parCell_union_disjoint G.edges true) x ⟨hx, hxF⟩
  · exact hU

/-! ## §T.6 Par cell component equality -/

/-- HOL Light: `par_cell_union_comp` (line 40597).
If `x` is in a parity region, then that region equals the connected component
of `x`. -/
theorem parCell_union_comp (G : Rectagon) (eps : Bool)
    {x : E2} (hx : x ∈ ⋃₀ {C | parCell eps G.edges C}) :
    ⋃₀ {C | parCell eps G.edges C} =
      connectedComponentIn (complementCurve G.edges) x := by
  have hxcomp : x ∈ complementCurve G.edges := by
    change x ∈ complementCurve G.toSegment.edges
    rw [← parCell_partition G.toSegment true]
    cases eps with
    | true => exact Set.mem_union_left _ hx
    | false => exact Set.mem_union_right _ hx
  cases eps with
  | true =>
    rw [← unbounded_even G]
    have hxU : UnboundedSet G.edges x := by
      change x ∈ {y | UnboundedSet G.edges y}; rw [unbounded_even]; exact hx
    exact (unboundedSet_comp G.edges G.all_edges hxU).symm
  | false =>
    apply Set.Subset.antisymm
    · intro y hy
      have hyB : BoundedSet G.edges y := odd_bounded_subset G hy
      have hxB : BoundedSet G.edges x := odd_bounded_subset G hx
      have heq := unique_bounded G hyB hxB
      exact heq ▸ mem_connectedComponentIn
        (bounded_subset_complementCurve G.edges hyB)
    · rcases parCell_comp G true x with hT | hF
      · exfalso
        exact Set.eq_empty_iff_forall_notMem.mp
          (parCell_union_disjoint G.edges true) x
          ⟨hT (mem_connectedComponentIn hxcomp), hx⟩
      · exact hF

-- HOL Light 1108: `edge_cell` — Not applicable to Lean: already `isEdge_isCell` in SectionA.

/-- HOL Light: `edge_subset_ctop` (line 40682).
Disjoint edges from `G` lie in the complement of `G`. -/
theorem edge_subset_complementCurve (G A : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (hA : ∀ e ∈ A, isEdge e)
    (hDisj : Disjoint A G) :
    (⋃₀ ↑A) ⊆ complementCurve G := by
  intro z hz
  simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion]; push Not
  intro S hS hzS
  rw [Set.mem_sUnion] at hz
  obtain ⟨e, heA, hze⟩ := hz
  have he_cell := isEdge_isCell (hA e heA)
  obtain ⟨ct_e, rfl⟩ := he_cell
  have hS_cell := curveCells_subset_cell G hG S hS
  obtain ⟨ct_S, rfl⟩ := hS_cell
  have ⟨_, _, huniq⟩ := cell_partition z
  have : ct_e = ct_S := (huniq ct_e hze).trans (huniq ct_S hzS).symm
  subst this
  simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS
  rcases hS with hSG | ⟨m, heq, _⟩
  · exact Finset.disjoint_left.mp hDisj heA hSG
  · rcases hA ct_e.toSet heA with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact absurd (hp.symm.trans heq) (hEdge_ne_pointI_set p m)
    · exact absurd (hp.symm.trans heq) (vEdge_ne_pointI_set p m)

/-- HOL Light: `par_cell_pointI` (line 40729).
A singleton lattice point has a specific parity iff it lies in the corresponding
parity region. -/
theorem parCell_pointI_iff (G : Finset (Set E2)) (eps : Bool) (m : ℤ × ℤ) :
    parCell eps G {pointI m} ↔ pointI m ∈ ⋃₀ {C | parCell eps G C} := by
  constructor
  · exact fun h =>
      Set.mem_sUnion.mpr ⟨{pointI m}, h, Set.mem_singleton _⟩
  · intro h
    rw [Set.mem_sUnion] at h
    obtain ⟨C, hC, hm⟩ := h
    obtain ⟨⟨n, hcell, heps⟩, hdis⟩ := hC
    rcases hcell with rfl | rfl | rfl | rfl
    · rw [Set.mem_singleton_iff] at hm
      have h_eq := pointI_injective hm; subst m
      exact ⟨⟨n, Or.inl rfl, heps⟩, hdis⟩
    · exact absurd hm (hEdge_not_pointI n m)
    · exact absurd hm (vEdge_not_pointI n m)
    · exact absurd hm (squ_not_pointI n m)

/-- HOL Light: `par_cell_pointI_trichot` (line 40748).
Every lattice point is in one of the two parity classes or in the closure `cls`. -/
theorem parCell_pointI_trichot (G : Rectagon) (eps : Bool) (m : ℤ × ℤ) :
    parCell eps G.edges {pointI m} ∨ parCell (!eps) G.edges {pointI m} ∨
      m ∈ cls G.edges := by
  by_cases hcomp : pointI m ∈ complementCurve G.edges
  · have hpart : pointI m ∈ ⋃₀ {C | parCell eps G.toSegment.edges C} ∪
        ⋃₀ {C | parCell (!eps) G.toSegment.edges C} := by
      rw [parCell_partition G.toSegment eps]; exact hcomp
    rcases hpart with hT | hF
    · exact Or.inl ((parCell_pointI_iff G.edges eps m).mpr hT)
    · exact Or.inr (Or.inl ((parCell_pointI_iff G.edges (!eps) m).mpr hF))
  · right; right
    simp only [complementCurve, Set.mem_compl_iff, not_not] at hcomp
    rw [Set.mem_sUnion] at hcomp
    obtain ⟨S, hS, hzS⟩ := hcomp
    simp only [curveCells, mem_union, Finset.mem_coe, mem_setOf_eq] at hS
    rcases hS with hSG | ⟨k, rfl, hk⟩
    · rcases G.all_edges S hSG with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · exact absurd hzS (hEdge_not_pointI p m)
      · exact absurd hzS (vEdge_not_pointI p m)
    · rw [Set.mem_singleton_iff] at hzS
      have := pointI_injective hzS; subst this
      simp only [cls, mem_setOf_eq]
      rw [((↑G.edges : Set (Set E2)).toFinite).closure_sUnion, Set.mem_iUnion₂] at hk
      obtain ⟨e, he, hcl⟩ := hk
      exact ⟨e, he, hcl⟩

/-- HOL Light: `par_cell_nbd` (line 40784).
If a lattice point has parity `eps` and an edge `e` is incident to it
(not in `G`), then `e` also has parity `eps`. -/
theorem parCell_nbd (G : Rectagon) (eps : Bool) (m : ℤ × ℤ) (e : Set E2)
    (hpar : parCell eps G.edges {pointI m}) (he : isEdge e)
    (hcl : pointI m ∈ closure e) :
    parCell eps G.edges e := by
  have hpt := (parCell_point G.toSegment m eps).mp hpar
  obtain ⟨hnum, heps⟩ := hpt
  rw [numClosure_eq_zero_iff] at hnum
  rcases he with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · -- e = hEdge m'
    rw [pointI_mem_closure_hEdge] at hcl
    obtain ⟨hm2, hm1 | hm1⟩ := hcl
    · have heq : m' = m := Prod.ext hm1.symm hm2.symm
      rw [heq]
      exact (parCell_point_hEdge G m eps hpar).1
    · have heq : m' = left m :=
        Prod.ext (by simp [left]; omega) (by simp [left]; omega)
      rw [heq]
      exact (parCell_point_hEdge G m eps hpar).2
  · -- e = vEdge m'
    rw [pointI_mem_closure_vEdge] at hcl
    obtain ⟨hm1, hm2 | hm2⟩ := hcl
    · have heq : m' = m := Prod.ext hm1.symm hm2.symm
      rw [heq]
      have hv_not : vEdge m ∉ G.edges := fun hmem =>
        hnum _ hmem
          ((pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
      exact (parCell_vEdge G.toSegment m eps).mpr ⟨hv_not, heps⟩
    · have heq : m' = down m :=
        Prod.ext (by simp [down]; omega) (by simp [down]; omega)
      rw [heq]
      have hv_d_not : vEdge (down m) ∉ G.edges := fun hmem =>
        hnum _ hmem ((pointI_mem_closure_vEdge m (down m)).mpr
          ⟨by simp [down], Or.inr (by simp [down])⟩)
      have hh_not : hEdge m ∉ G.edges := fun hmem =>
        hnum _ hmem
          ((pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩)
      have hstep := numLower_step G.edges m.1 m.2
      simp only [Prod.mk.eta, if_neg hh_not, Nat.add_zero]
        at hstep
      exact (parCell_vEdge G.toSegment (down m) eps).mpr
        ⟨hv_d_not, by
          simp only [down]
          change eps = decide (Even (numLower G.edges (m.1, m.2 - 1)))
          rw [← hstep]; exact heps⟩

/-! ## §T.7 Adding segments -/

/-- HOL Light: `segment_in_comp` (line 40840).
A segment disjoint from `G` whose closure meets `cls G` only at endpoints
lies entirely in one parity region. -/
theorem segment_in_comp (G : Rectagon) (A : Segment)
    (hDisj : Disjoint A.edges G.edges)
    (hCls : ∀ m, m ∈ cls G.edges ∩ cls A.edges → A.isEndpoint m) :
    ∃ eps : Bool, ∀ e ∈ A.edges, parCell eps G.edges e := by
  -- Step 1: pick any edge e₀ ∈ A.edges
  obtain ⟨e₀, he₀⟩ := A.nonempty
  have he₀_edge := A.all_edges e₀ he₀
  -- Step 2: e₀ ∉ G.edges, lies in complementCurve G
  have he₀_comp : (↑e₀ : Set E2) ⊆ complementCurve G.edges :=
    fun z hz => edge_subset_complementCurve G.edges A.edges G.all_edges
      A.all_edges hDisj
      (Set.mem_sUnion.mpr ⟨e₀, Finset.mem_coe.mpr he₀, hz⟩)
  -- Step 3: pick z ∈ e₀ and find its parity
  obtain ⟨z, hz⟩ := cell_nonempty (isEdge_isCell he₀_edge)
  have hz_comp := he₀_comp hz
  have hz_part : z ∈ ⋃₀ {C | parCell true G.toSegment.edges C} ∪
      ⋃₀ {C | parCell false G.toSegment.edges C} := by
    rw [show (false : Bool) = !true from rfl, parCell_partition G.toSegment true]; exact hz_comp
  -- Step 4: determine eps s.t. parCell eps G.edges e₀
  have ⟨eps, hpar_e₀⟩ : ∃ eps : Bool, parCell eps G.edges e₀ := by
    have find_eps : ∀ C, C ∈ {C | parCell true G.toSegment.edges C} ∪
        {C | parCell false G.toSegment.edges C} → z ∈ C →
        ∃ eps : Bool, parCell eps G.edges e₀ := by
      intro C hC hzC
      have hC_cell : isCell C := by
        rcases hC with ⟨⟨n, hn, _⟩, _⟩ | ⟨⟨n, hn, _⟩, _⟩ <;>
          rcases hn with rfl | rfl | rfl | rfl <;>
          first
          | exact ⟨.point _, rfl⟩
          | exact ⟨.hEdge _, rfl⟩
          | exact ⟨.vEdge _, rfl⟩
          | exact ⟨.squ _, rfl⟩
      obtain ⟨ct_C, rfl⟩ := hC_cell
      obtain ⟨ct_e, rfl⟩ := isEdge_isCell he₀_edge
      have : ct_C = ct_e := by
        have ⟨_, _, hu⟩ := cell_partition z
        exact (hu ct_C hzC).trans (hu ct_e hz).symm
      subst this
      rcases hC with hT | hF
      · exact ⟨true, hT⟩
      · exact ⟨false, hF⟩
    rcases hz_part with ⟨C, hC, hzC⟩ | ⟨C, hC, hzC⟩
    · exact find_eps C (Or.inl hC) hzC
    · exact find_eps C (Or.inr hC) hzC
  -- Step 5: use A.connected to propagate parity
  refine ⟨eps, fun e he => ?_⟩
  set S : Set (Set E2) := {e | e ∈ A.edges ∧ parCell eps G.edges e}
  have hS_sub : S ⊆ ↑A.edges := fun e he => he.1
  have hS_ne : S.Nonempty := ⟨e₀, he₀, hpar_e₀⟩
  have hS_closed :
      ∀ C' ∈ S, ∀ C'' ∈ ↑A.edges, cellAdj C' C'' → C'' ∈ S := by
    intro C' ⟨hC'A, hC'par⟩ C'' hC''A hadj
    have hC'_edge := A.all_edges C' hC'A
    have hC''_edge := A.all_edges C'' hC''A
    set m := adjv C' C'' with m_def
    have hm_C' := adjv_closure_left C' C'' hC'_edge hC''_edge hadj
    have hm_C'' := adjv_closure_right C' C'' hC'_edge hC''_edge hadj
    have hm_A : m ∈ cls A.edges := ⟨C', hC'A, hm_C'⟩
    -- m ∉ cls G.edges (otherwise numClosure A m = 1 but ≥ 2)
    have hm_notG : m ∉ cls G.edges := by
      intro hm_G
      have hep := hCls m ⟨hm_G, hm_A⟩
      simp only [Segment.isEndpoint] at hep
      have hC'_inc : C' ∈ incidentEdges A.edges m := by
        simp only [incidentEdges, Finset.mem_filter]
        exact ⟨hC'A, hm_C'⟩
      have hC''_inc : C'' ∈ incidentEdges A.edges m := by
        simp only [incidentEdges, Finset.mem_filter]
        exact ⟨hC''A, hm_C''⟩
      have : 2 ≤ (incidentEdges A.edges m).card :=
        Finset.one_lt_card.mpr ⟨C', hC'_inc, C'', hC''_inc, hadj.2.2.1⟩
      rw [numClosure] at hep; omega
    -- By trichotomy: parCell eps G.edges {pointI m}
    have hm_par : parCell eps G.edges {pointI m} := by
      rcases parCell_pointI_trichot G eps m with h | h | h
      · exact h
      · exfalso
        exact parCell_disjoint G.edges eps C'
          ⟨hC'par, parCell_nbd G (!eps) m C' h hC'_edge hm_C'⟩
      · exact absurd h hm_notG
    exact ⟨hC''A, parCell_nbd G eps m C'' hm_par hC''_edge hm_C''⟩
  have hS_eq := A.connected S hS_sub hS_ne hS_closed
  have : (e : Set E2) ∈ S := by rw [hS_eq]; exact he
  exact this.2

/-- HOL Light: `segment_end_select` (line 40919).
Given a segment from `a` to `b` where `a ∉ cls E` and `b ∈ cls E`,
there is a sub-segment from `a` to some `c ∈ cls E` whose closure meets
`cls E` only at `c`. -/
theorem segment_end_select {E A : Finset (Set E2)} {a b : ℤ × ℤ}
    (_hE : ∀ e ∈ E, isEdge e) (hA : segment_end A a b)
    (hna : a ∉ cls E) (hb : b ∈ cls E) :
    ∃ B c, segment_end B a c ∧ c ∈ cls E ∧ B ⊆ A ∧ cls B ∩ cls E = {c} := by
  -- Strong induction on A.card
  suffices h : ∀ n (A' : Finset (Set E2)) (b' : ℤ × ℤ),
      A'.card = n → segment_end A' a b' → b' ∈ cls E →
      ∃ B c, segment_end B a c ∧ c ∈ cls E ∧ B ⊆ A' ∧
        cls B ∩ cls E = {c} from
    h A.card A b rfl hA hb
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro A' b' hn hA' hb'
  -- Check if cls A' ∩ cls E = {b'}
  by_cases hcls : cls A' ∩ cls E = {b'}
  · exact ⟨A', b', hA', hb', Finset.Subset.refl A', hcls⟩
  · -- There exists m ∈ cls A' ∩ cls E with m ≠ b'
    have hb_mem : b' ∈ cls A' ∩ cls E :=
      Set.mem_inter (segment_end_cls2 hA') hb'
    have ⟨m, hm_mem, hm_ne⟩ : ∃ m ∈ cls A' ∩ cls E, m ≠ b' := by
      by_contra h'; push Not at h'
      exact hcls (Set.eq_singleton_iff_unique_mem.mpr ⟨hb_mem, h'⟩)
    have hm_A := hm_mem.1
    have hm_E := hm_mem.2
    -- m ≠ a (since a ∉ cls E but m ∈ cls E)
    have hma : m ≠ a := fun heq => hna (heq ▸ hm_E)
    -- Cut A' at m: get A1 (a↔m) and A2 (m↔b')
    obtain ⟨A1, A2, hAeq, hDisj12, _, hA1_seg, _⟩ :=
      cut_psegment hA' hm_A hma hm_ne
    -- A1.card < n
    have hA1_lt : A1.card < n := by
      rw [← hn, hAeq, Finset.card_union_of_disjoint hDisj12]
      have : 0 < A2.card :=
        Finset.card_pos.mpr (segment_end_finite ‹segment_end A2 m b'›)
      omega
    have hA1_sub : A1 ⊆ A' := by
      rw [hAeq]; exact Finset.subset_union_left
    -- Apply IH to A1
    obtain ⟨B, c, hBseg, hcE, hBA1, hBcls⟩ :=
      ih A1.card hA1_lt A1 m rfl hA1_seg hm_E
    exact ⟨B, c, hBseg, hcE, hBA1.trans hA1_sub, hBcls⟩

/-- HOL Light: `endpoint_cls` (line 41003).
Points with `numClosure = 1` (endpoints) are in `cls`. -/
theorem endpoint_subset_cls (G : Finset (Set E2)) (_hG : ∀ e ∈ G, isEdge e) :
    {m | numClosure G m = 1} ⊆ cls G := by
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  simp only [cls, Set.mem_setOf_eq]
  have hpos : 0 < numClosure G m := by omega
  rw [numClosure] at hpos
  have hne := Finset.card_pos.mp hpos
  obtain ⟨e, he⟩ := hne
  simp only [incidentEdges, Finset.mem_filter] at he
  exact ⟨e, he.1, he.2⟩

/-- HOL Light: `conn2_proper` (line 41033).
A proper 2-connected sub-edge-set of a 2-connected set has a complementary
psegment whose closure meets the sub-set exactly at the psegment's endpoints. -/
theorem conn2_proper {G H : Finset (Set E2)}
    (hG : ∀ e ∈ G, isEdge e) (hcG : conn2 G) (hcH : conn2 H)
    (hHG : H ⊆ G) (hne : H ≠ G) :
    ∃ A, A ⊆ G ∧ Disjoint A H ∧
      (∃ S : Segment, S.isPsegment ∧ S.edges = A) ∧
      cls H ∩ cls A = {m | numClosure A m = 1} := by
  have hHedge : ∀ e ∈ H, isEdge e := fun e he => hG e (hHG he)
  by_cases hcls : cls G ⊆ cls H
  · -- Case 1: cls G ⊆ cls H — pick any edge in G \ H
    have ⟨e, heG, heH⟩ : ∃ e ∈ G, e ∉ H := by
      by_contra h; push Not at h
      exact hne (le_antisymm hHG h)
    have he : isEdge e := hG e heG
    refine ⟨{e}, Finset.singleton_subset_iff.mpr heG,
      Finset.disjoint_singleton_left.mpr heH, ?_, ?_⟩
    · obtain ⟨S, hSe, hSps⟩ := single_edge_isPsegment e he
      exact ⟨S, hSps, hSe⟩
    · -- cls H ∩ cls {e} = {m | numClosure {e} m = 1}
      -- For a single edge: cls {e} = {m | numClosure {e} m = 1}
      have h_cls_ep : cls ({e} : Finset (Set E2)) = {m | numClosure ({e} : Finset _) m = 1} := by
        ext m; simp only [cls, Set.mem_setOf_eq]
        exact ⟨fun ⟨f, hf, hmf⟩ =>
            (endpoint_closure_singleton e he m).mpr (Finset.mem_singleton.mp hf ▸ hmf),
          fun hm => endpoint_subset_cls {e}
            (fun f hf => Finset.mem_singleton.mp hf ▸ he) hm⟩
      -- cls {e} ⊆ cls G ⊆ cls H, so cls H ∩ cls {e} = cls {e}
      rw [Set.inter_eq_right.mpr
        ((cls_subset (Finset.singleton_subset_iff.mpr heG)).trans hcls), h_cls_ep]
  · -- Case 2: ¬(cls G ⊆ cls H) — construct a segment from two trimmed paths
    obtain ⟨a, haG, haH⟩ := Set.not_subset.mp hcls
    have hclsHG : cls H ⊆ cls G := cls_subset hHG
    -- Get two distinct points b ≠ c in cls H via a single edge
    have hHne : H.Nonempty := Finset.card_pos.mp (by have := hcH.1; omega)
    obtain ⟨e₁, he₁⟩ := hHne
    obtain ⟨b, c, hbc, hcls_eq⟩ :=
      Set.ncard_eq_two.mp (cls_edge_size2 (hHedge e₁ he₁))
    have hb_clsH : b ∈ cls H :=
      cls_subset (Finset.singleton_subset_iff.mpr he₁)
        (hcls_eq ▸ Set.mem_insert b {c})
    have hc_clsH : c ∈ cls H :=
      cls_subset (Finset.singleton_subset_iff.mpr he₁)
        (hcls_eq ▸ Set.mem_insert_iff.mpr (Or.inr rfl))
    have hab : a ≠ b := fun h => haH (h ▸ hb_clsH)
    have hac : a ≠ c := fun h => haH (h ▸ hc_clsH)
    -- Path 1: conn2 G gives segment U with segment_end U a b and c ∉ cls U
    obtain ⟨U, hUG, hUab, hUc⟩ :=
      hcG.2 a b c haG (hclsHG hb_clsH) hab hbc hac
    -- Trim U against H → get B, c' with cls B ∩ cls H = {c'}
    obtain ⟨B, c', hBac', hc'H, hBU, hclsBI⟩ :=
      segment_end_select hHedge hUab haH hb_clsH
    have hBG : B ⊆ G := hBU.trans hUG
    have hc_notB : c ∉ cls B := fun h => hUc (cls_subset hBU h)
    have hac' : a ≠ c' := fun h => haH (h ▸ hc'H)
    have hcc' : c ≠ c' := by
      intro heq; exact hc_notB (heq ▸ segment_end_cls2 hBac')
    -- Path 2: conn2 G gives segment V with segment_end V a c and c' ∉ cls V
    obtain ⟨V, hVG, hVac, hVc'⟩ :=
      hcG.2 a c c' haG (hclsHG hc_clsH) hac hcc' hac'
    -- Trim V against H → get B', c'' with cls B' ∩ cls H = {c''}
    obtain ⟨B', c'', hB'ac'', hc''H, hB'V, hclsB'I⟩ :=
      segment_end_select hHedge hVac haH hc_clsH
    have hB'G : B' ⊆ G := hB'V.trans hVG
    have hc'_notB' : c' ∉ cls B' := fun h => hVc' (cls_subset hB'V h)
    have hc''c' : c'' ≠ c' := by
      intro heq; exact hc'_notB' (heq ▸ segment_end_cls2 hB'ac'')
    -- Show B ∩ H = ∅ (edge in B∩H → cls has 2 pts ⊆ singleton, contradiction)
    have hBH : Disjoint B H := by
      rw [Finset.disjoint_left]
      intro u hu huH
      have hsub : cls ({u} : Finset (Set E2)) ⊆ ({c'} : Set (ℤ × ℤ)) := by
        intro m hm
        have : m ∈ cls B ∩ cls H :=
          ⟨cls_subset (Finset.singleton_subset_iff.mpr hu) hm,
           cls_subset (Finset.singleton_subset_iff.mpr huH) hm⟩
        rwa [hclsBI] at this
      have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton c')
      have h2 := cls_edge_size2 (hG u (hBG hu))
      rw [Set.ncard_singleton] at h1; omega
    -- Similarly B' ∩ H = ∅
    have hB'H : Disjoint B' H := by
      rw [Finset.disjoint_left]
      intro u hu huH
      have hsub : cls ({u} : Finset (Set E2)) ⊆ ({c''} : Set (ℤ × ℤ)) := by
        intro m hm
        have : m ∈ cls B' ∩ cls H :=
          ⟨cls_subset (Finset.singleton_subset_iff.mpr hu) hm,
           cls_subset (Finset.singleton_subset_iff.mpr huH) hm⟩
        rwa [hclsB'I] at this
      have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton c'')
      have h2 := cls_edge_size2 (hG u (hB'G hu))
      rw [Set.ncard_singleton] at h1; omega
    -- Reverse B and concatenate with B': segment_end W c' c''
    have hBca' : segment_end B c' a := (segment_end_symm B a c').mp hBac'
    obtain ⟨W, hWsub, hWseg⟩ :=
      segment_end_trans hBca' hB'ac'' hc''c'.symm
    -- Build the final result
    refine ⟨W, hWsub.trans (Finset.union_subset hBG hB'G), ?_, ?_, ?_⟩
    · -- Disjoint W H
      rw [Finset.disjoint_left]
      intro u hu huH
      have huBB' := hWsub hu
      rw [Finset.mem_union] at huBB'
      rcases huBB' with huB | huB'
      · exact (Finset.disjoint_left.mp hBH) huB huH
      · exact (Finset.disjoint_left.mp hB'H) huB' huH
    · -- ∃ S, S.isPsegment ∧ S.edges = W
      obtain ⟨S, hSe, hSc', hSc'', _, hSend⟩ := hWseg
      exact ⟨S, ⟨c', c'', hc''c'.symm, hSc', hSc'', hSend⟩, hSe⟩
    · -- cls H ∩ cls W = {m | numClosure W m = 1}
      obtain ⟨S, hSe, hSc', hSc'', _, hSend⟩ := hWseg
      have hWedge : ∀ e ∈ W, isEdge e :=
        fun e he => hG e (hWsub.trans (Finset.union_subset hBG hB'G) he)
      ext m; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; constructor
      · -- (→) m ∈ cls H ∩ cls W → numClosure W m = 1
        intro ⟨hm_clsH, hm_clsW⟩
        have hm_clsBB' : m ∈ cls B ∪ cls B' := by
          rw [← cls_union]; exact cls_subset hWsub hm_clsW
        rcases hm_clsBB' with hm_clsB | hm_clsB'
        · have hmem : m ∈ ({c'} : Set (ℤ × ℤ)) := by
            rw [← hclsBI]; exact ⟨hm_clsB, hm_clsH⟩
          rw [Set.mem_singleton_iff.mp hmem, ← hSe]; exact hSc'
        · have hmem : m ∈ ({c''} : Set (ℤ × ℤ)) := by
            rw [← hclsB'I]; exact ⟨hm_clsB', hm_clsH⟩
          rw [Set.mem_singleton_iff.mp hmem, ← hSe]; exact hSc''
      · -- (←) numClosure W m = 1 → m ∈ cls H ∩ cls W
        intro hm
        have hm_cls : m ∈ cls W := endpoint_subset_cls W hWedge hm
        have hm_ep : S.isEndpoint m := by rw [Segment.isEndpoint, hSe]; exact hm
        rcases hSend m hm_ep with rfl | rfl
        · exact ⟨hc'H, hm_cls⟩
        · exact ⟨hc''H, hm_cls⟩

end JordanCurveTheorem
