/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionL_ArcTopology

/-!
# Section M: Simple Arc Endpoints & Separation
## HOL Light: Section M (Lines 24220–25408)

Simple arc endpoint membership and closedness, plus the arc-separation
lemma used in the Jordan curve theorem proof.

### Key HOL Light results
- Endpoints of a simple arc belong to the arc
- Simple arcs are closed
- Three arcs from a common center can be refined so their pairwise
  intersections are exactly the common center
-/

open Set

/-! ## Endpoint membership -/

/-- The first endpoint belongs to the arc.
    HOL Light: `simple_arc_end_end` (line 24347). -/
theorem isSimpleArcEnd_mem_left {C : Set E2'} {v v' : E2'}
    (h : IsSimpleArcEnd C v v') : v ∈ C := by
  obtain ⟨f, rfl, _, _, hf0, _⟩ := h
  exact ⟨0, left_mem_Icc.mpr zero_le_one, hf0⟩

/-- The second endpoint belongs to the arc.
    HOL Light: `simple_arc_end_end2` (line 24359). -/
theorem isSimpleArcEnd_mem_right {C : Set E2'} {v v' : E2'}
    (h : IsSimpleArcEnd C v v') : v' ∈ C := by
  obtain ⟨f, rfl, _, _, _, hf1⟩ := h
  exact ⟨1, right_mem_Icc.mpr zero_le_one, hf1⟩

/-! ## Closedness -/

/-- A simple arc is closed (compact image of compact set is closed).
    HOL Light: `simple_arc_end_closed` (line 24291). -/
theorem isSimpleArcEnd_isClosed {C : Set E2'} {v v' : E2'}
    (h : IsSimpleArcEnd C v v') : IsClosed C :=
  (isSimpleArc_compact (isSimpleArcEnd_isSimpleArc h)).isClosed

/-! ## Arc separation helpers -/

/-- If C ∩ K = {v} and C' ⊆ C, then C' ∩ K ⊆ {v}. -/
private theorem inter_singleton_subset {C C' K : Set E2'} {v : E2'}
    (hCK : C ∩ K = {v}) (hsub : C' ⊆ C) : C' ∩ K ⊆ {v} := by
  intro y ⟨hyC', hyK⟩
  have : y ∈ C ∩ K := ⟨hsub hyC', hyK⟩
  rwa [hCK] at this

/-- Cut an arc at an interior point, keeping the half ending at v'. -/
private theorem arc_subarc_right {C : Set E2'} {v v' w : E2'}
    (hC : IsSimpleArcEnd C v v') (hw : w ∈ C)
    (hwv : w ≠ v) (hwv' : w ≠ v') :
    ∃ C', C' ⊆ C ∧ IsSimpleArcEnd C' w v' := by
  obtain ⟨C₁, C₂, _, hC₂, _, hunion⟩ :=
    isSimpleArcEnd_cut hC hw hwv hwv'
  exact ⟨C₂, hunion ▸ subset_union_right, hC₂⟩

/-- Three arcs from a common center: refine so C₁' meets C₂', C₃'
    each in exactly {x'}, plus side conditions.
    HOL Light: `simple_arc_sep3` (line 24316). -/
private theorem simple_arc_sep3 {A : Set E2'} {C₁ C₂ C₃ : Set E2'}
    {x p₁ p₂ p₃ : E2'}
    (hA : C₁ ∪ C₂ ∪ C₃ ⊆ A)
    (hC₁ : IsSimpleArcEnd C₁ x p₁) (h12 : p₂ ∉ C₁) (h13 : p₃ ∉ C₁)
    (hC₂ : IsSimpleArcEnd C₂ x p₂) (h21 : p₁ ∉ C₂) (h23 : p₃ ∉ C₂)
    (hC₃ : IsSimpleArcEnd C₃ x p₃) (h31 : p₁ ∉ C₃) (h32 : p₂ ∉ C₃) :
    ∃ x' C₁' C₂' C₃',
      C₁' ∪ C₂' ∪ C₃' ⊆ A ∧
      IsSimpleArcEnd C₁' x' p₁ ∧
      IsSimpleArcEnd C₂' x' p₂ ∧
      IsSimpleArcEnd C₃' x' p₃ ∧
      C₁' ∩ C₂' = {x'} ∧
      C₁' ∩ C₃' = {x'} ∧
      p₃ ∉ C₂' ∧ p₂ ∉ C₃' := by
  -- Setup: K = C₂ ∪ C₃
  have hK_cl : IsClosed (C₂ ∪ C₃) :=
    (isSimpleArcEnd_isClosed hC₂).union (isSimpleArcEnd_isClosed hC₃)
  have hdisjKp : C₁ ∩ (C₂ ∪ C₃) ∩ {p₁} = ∅ := by
    ext y; simp only [mem_inter_iff, mem_union, mem_singleton_iff,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨_, h⟩ rfl; exact h.elim h21 h31
  have hCK : (C₁ ∩ (C₂ ∪ C₃)).Nonempty :=
    ⟨x, isSimpleArcEnd_mem_left hC₁,
      Or.inl (isSimpleArcEnd_mem_left hC₂)⟩
  have hCp₁ : (C₁ ∩ {p₁}).Nonempty :=
    ⟨p₁, isSimpleArcEnd_mem_right hC₁, rfl⟩
  -- Restriction
  obtain ⟨C₁', x', v', hC₁'sub, hC₁'arc, hC₁'K, hC₁'p⟩ :=
    isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc hC₁)
      hK_cl isClosed_singleton hdisjKp hCK hCp₁
  -- v' = p₁
  have hv'p₁ : v' = p₁ := by
    have : {v'} ⊆ ({p₁} : Set E2') := hC₁'p ▸ inter_subset_right
    rwa [singleton_subset_iff, mem_singleton_iff] at this
  rw [hv'p₁] at hC₁'arc hC₁'p; clear hv'p₁ v'
  -- x' properties
  have hx'K : x' ∈ C₂ ∪ C₃ := by
    have : x' ∈ C₁' ∩ (C₂ ∪ C₃) := by rw [hC₁'K]; rfl
    exact this.2
  have hx'C₁ : x' ∈ C₁ := hC₁'sub (isSimpleArcEnd_mem_left hC₁'arc)
  have hx'p₂ : x' ≠ p₂ := fun h => by subst h; exact h12 hx'C₁
  have hx'p₃ : x' ≠ p₃ := fun h => by subst h; exact h13 hx'C₁
  have hC₁'A : C₁' ⊆ A := hC₁'sub.trans <|
    (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
      (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_left) |>.trans hA
  -- Helper: from C₁'∩K={x'}, any C'⊆C₁ has C'∩C₂ and C'∩C₃ ⊆ {x'}
  have hC₁_C₂_sub : ∀ y, y ∈ C₁' → y ∈ C₂ → y = x' := by
    intro y hy₁ hy₂
    have : y ∈ C₁' ∩ (C₂ ∪ C₃) := ⟨hy₁, Or.inl hy₂⟩
    rwa [hC₁'K, mem_singleton_iff] at this
  have hC₁_C₃_sub : ∀ y, y ∈ C₁' → y ∈ C₃ → y = x' := by
    intro y hy₁ hy₃
    have : y ∈ C₁' ∩ (C₂ ∪ C₃) := ⟨hy₁, Or.inr hy₃⟩
    rwa [hC₁'K, mem_singleton_iff] at this
  -- Case x' = x
  by_cases hx'x : x' = x
  · have hC₁'eq : C₁' = C₁ := by
      rw [hx'x] at hC₁'arc
      exact isSimpleArcEnd_inj hC₁'arc hC₁
        (isSimpleArcEnd_isSimpleArc hC₁) hC₁'sub Subset.rfl
    rw [hx'x, hC₁'eq] at hC₁_C₂_sub hC₁_C₃_sub
    refine ⟨x, C₁, C₂, C₃, hA, hC₁, hC₂, hC₃, ?_, ?_, h23, h32⟩
    · ext y; simp only [mem_inter_iff, mem_singleton_iff]
      exact ⟨fun ⟨h₁, h₂⟩ => hC₁_C₂_sub y h₁ h₂,
        fun h => h ▸ ⟨isSimpleArcEnd_mem_left hC₁,
          isSimpleArcEnd_mem_left hC₂⟩⟩
    · ext y; simp only [mem_inter_iff, mem_singleton_iff]
      exact ⟨fun ⟨h₁, h₃⟩ => hC₁_C₃_sub y h₁ h₃,
        fun h => h ▸ ⟨isSimpleArcEnd_mem_left hC₁,
          isSimpleArcEnd_mem_left hC₃⟩⟩
  · -- Case x' ≠ x: cut C₁ at x'
    have hx'p₁ : x' ≠ p₁ := isSimpleArcEnd_distinct hC₁'arc
    obtain ⟨Cx, C₁'', hCxarc, hC₁''arc, hCxC₁''int, hCxC₁''un⟩ :=
      isSimpleArcEnd_cut hC₁ hx'C₁ hx'x hx'p₁
    have hC₁''eq : C₁'' = C₁' :=
      isSimpleArcEnd_inj hC₁''arc hC₁'arc
        (isSimpleArcEnd_isSimpleArc hC₁) (hCxC₁''un ▸ subset_union_right)
        hC₁'sub
    rw [hC₁''eq] at hCxC₁''int hCxC₁''un
    have hCxsub : Cx ⊆ C₁ := hCxC₁''un ▸ subset_union_left
    -- Helper: prove C₁' ∩ D = {x'} when D ⊆ K and x' ∈ D
    have mk_inter (D : Set E2') (hDK : D ⊆ C₂ ∪ C₃) (hx'D : x' ∈ D) :
        C₁' ∩ D = {x'} := by
      ext y; constructor
      · rintro ⟨hyC₁', hyD⟩
        have : y ∈ C₁' ∩ (C₂ ∪ C₃) := ⟨hyC₁', hDK hyD⟩
        rwa [hC₁'K, mem_singleton_iff] at this
      · intro hy; rw [mem_singleton_iff] at hy; subst hy
        exact ⟨isSimpleArcEnd_mem_left hC₁'arc, hx'D⟩
    -- Helper: prove Cx ∩ D = {x'} when D ⊆ C₁' and x' ∈ D
    have mk_inter_Cx (D : Set E2') (hDC' : D ⊆ Cx)
        (hx'D : x' ∈ D) : C₁' ∩ D = {x'} := by
      ext y; constructor
      · rintro ⟨hyC₁', hyD⟩
        have : y ∈ Cx ∩ C₁' := ⟨hDC' hyD, hyC₁'⟩
        rwa [hCxC₁''int, mem_singleton_iff] at this
      · intro hy; rw [mem_singleton_iff] at hy; subst hy
        exact ⟨isSimpleArcEnd_mem_left hC₁'arc, hx'D⟩
    -- Helper for subset A
    have hCxA : Cx ⊆ A := hCxsub.trans <|
      (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
        (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_left) |>.trans hA
    have hC₂A : C₂ ⊆ A := (show C₂ ⊆ C₁ ∪ C₂ from
      subset_union_right).trans (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from
        subset_union_left) |>.trans hA
    have hC₃A : C₃ ⊆ A :=
      (show C₃ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_right).trans hA
    -- Process by membership
    rcases hx'K with hx'C₂ | hx'C₃
    · -- x' ∈ C₂: cut C₂ at x'
      obtain ⟨C₂', hC₂'sub, hC₂'arc⟩ :=
        arc_subarc_right hC₂ hx'C₂ hx'x hx'p₂
      have hC₁'C₂' : C₁' ∩ C₂' = {x'} :=
        mk_inter C₂' (hC₂'sub.trans (show C₂ ⊆ C₂ ∪ C₃ from
          subset_union_left)) (isSimpleArcEnd_mem_left hC₂'arc)
      by_cases hx'C₃ : x' ∈ C₃
      · -- x' ∈ C₂ ∩ C₃
        obtain ⟨C₃', hC₃'sub, hC₃'arc⟩ :=
          arc_subarc_right hC₃ hx'C₃ hx'x hx'p₃
        refine ⟨x', C₁', C₂', C₃', ?_, hC₁'arc, hC₂'arc,
          hC₃'arc, hC₁'C₂',
          mk_inter C₃' (hC₃'sub.trans (show C₃ ⊆ C₂ ∪ C₃ from
            subset_union_right))
            (isSimpleArcEnd_mem_left hC₃'arc),
          fun h => h23 (hC₂'sub h), fun h => h32 (hC₃'sub h)⟩
        exact union_subset (union_subset hC₁'A (hC₂'sub.trans hC₂A))
          (hC₃'sub.trans hC₃A)
      · -- x' ∈ C₂, x' ∉ C₃: find a bridge from C' to C₃
        have hCx_C₃_disj : Cx ∩ C₃ ∩ {x'} = ∅ := by
          ext y; simp only [mem_inter_iff, mem_singleton_iff,
            mem_empty_iff_false, iff_false, not_and]
          rintro ⟨_, hyC₃⟩ rfl; exact hx'C₃ hyC₃
        have hCxC₃ne : (Cx ∩ C₃).Nonempty :=
          ⟨x, isSimpleArcEnd_mem_left hCxarc,
            isSimpleArcEnd_mem_left hC₃⟩
        have hCxx'ne : (Cx ∩ {x'}).Nonempty :=
          ⟨x', isSimpleArcEnd_mem_right hCxarc, rfl⟩
        obtain ⟨C₃a, v₃, w₃, hC₃asub, hC₃aarc, hC₃aC₃, hC₃ax'⟩ :=
          isSimpleArcEnd_restriction
            (isSimpleArcEnd_isSimpleArc hCxarc)
            (isSimpleArcEnd_isClosed hC₃) isClosed_singleton
            hCx_C₃_disj hCxC₃ne hCxx'ne
        -- w₃ = x'
        have hw₃ : w₃ = x' := by
          have : {w₃} ⊆ ({x'} : Set E2') := hC₃ax' ▸ inter_subset_right
          rwa [singleton_subset_iff, mem_singleton_iff] at this
        rw [hw₃] at hC₃aarc; clear hw₃ hC₃ax' w₃
        -- v₃ ∈ C₃
        have hv₃C₃ : v₃ ∈ C₃ := by
          have : {v₃} ⊆ (C₃ : Set E2') := hC₃aC₃ ▸ inter_subset_right
          rwa [singleton_subset_iff] at this
        have hC₃asub₁ : C₃a ⊆ C₁ := hC₃asub.trans hCxsub
        have hC₃ap₃ : p₃ ∉ C₃a := fun h => h13 (hC₃asub₁ h)
        have hC₁'C₃a : C₁' ∩ C₃a = {x'} :=
          mk_inter_Cx C₃a hC₃asub (isSimpleArcEnd_mem_right hC₃aarc)
        -- Sub-case: v₃ = x
        by_cases hv₃x : v₃ = x
        · rw [hv₃x] at hC₃aarc hC₃aC₃
          -- Form (C₃ ∪ C₃a): arc from p₃ to x'
          -- C₃: x→p₃, C₃a: x→x', intersection C₃∩C₃a={x}
          have hC₃_C₃a_int : C₃ ∩ C₃a ⊆ {x} := by
            rw [Set.inter_comm]; exact inter_singleton_subset hC₃aC₃ Subset.rfl
          have hC₃' := isSimpleArcEnd_symm <| isSimpleArcEnd_concat
            (isSimpleArcEnd_symm hC₃) hC₃aarc hC₃_C₃a_int
          -- C₃ ∪ C₃a is an arc from p₃ to x'
          refine ⟨x', C₁', C₂', C₃ ∪ C₃a, ?_, hC₁'arc, hC₂'arc,
            hC₃', hC₁'C₂', ?_,
            fun h => h23 (hC₂'sub h), ?_⟩
          · -- Subset A
            exact union_subset (union_subset hC₁'A (hC₂'sub.trans hC₂A))
              (union_subset hC₃A (hC₃asub₁.trans <|
                (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
                  (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from
                    subset_union_left) |>.trans hA))
          · -- C₁' ∩ (C₃ ∪ C₃a) = {x'}
            ext y; constructor
            · rintro ⟨hyC₁', hyC₃C₃a⟩
              rcases hyC₃C₃a with hyC₃ | hyC₃a
              · exact hC₁_C₃_sub y hyC₁' hyC₃
              · have : y ∈ C₁' ∩ C₃a := ⟨hyC₁', hyC₃a⟩
                rwa [hC₁'C₃a, mem_singleton_iff] at this
            · intro hy; rw [mem_singleton_iff] at hy; subst hy
              exact ⟨isSimpleArcEnd_mem_left hC₁'arc,
                Or.inr (isSimpleArcEnd_mem_right hC₃aarc)⟩
          · -- p₂ ∉ C₃ ∪ C₃a
            intro hp₂; rcases hp₂ with hp₂C₃ | hp₂C₃a
            · exact h32 hp₂C₃
            · exact h12 (hC₃asub₁ hp₂C₃a)
        · -- Sub-case: v₃ ≠ x: cut C₃ at v₃
          have hv₃p₃ : v₃ ≠ p₃ := by
            intro h; rw [h] at hC₃aarc
            exact hC₃ap₃ (isSimpleArcEnd_mem_left hC₃aarc)
          obtain ⟨C₃x, C₃b, hC₃xarc, hC₃barc, hC₃xC₃bint,
            hC₃xC₃bun⟩ :=
            isSimpleArcEnd_cut hC₃ hv₃C₃ hv₃x hv₃p₃
          -- C₃a: v₃→x', C₃b: v₃→p₃
          -- Form: (C₃a symm) ∪ C₃b = arc from x' to p₃
          -- Intersection: C₃a ∩ C₃b ⊆ C₃a ∩ C₃ ∩ (C₃x ∪ C₃b)
          -- C₃a ∩ C₃ = {v₃}, so C₃a ∩ C₃b ⊆ {v₃}
          have hC₃a_C₃b_int : C₃a ∩ C₃b ⊆ {v₃} := by
            intro y ⟨hyC₃a, hyC₃b⟩
            have hyC₃ : y ∈ C₃ := (hC₃xC₃bun ▸ subset_union_right) hyC₃b
            have : y ∈ C₃a ∩ C₃ := ⟨hyC₃a, hyC₃⟩
            rwa [hC₃aC₃, mem_singleton_iff] at this
          have hC₃'arc := isSimpleArcEnd_concat
            (isSimpleArcEnd_symm hC₃aarc) hC₃barc hC₃a_C₃b_int
          have hC₃bsub : C₃b ⊆ C₃ := hC₃xC₃bun ▸ subset_union_right
          refine ⟨x', C₁', C₂', C₃a ∪ C₃b, ?_, hC₁'arc, hC₂'arc,
            hC₃'arc, hC₁'C₂', ?_,
            fun h => h23 (hC₂'sub h), ?_⟩
          · -- Subset A
            exact union_subset (union_subset hC₁'A (hC₂'sub.trans hC₂A))
              (union_subset (hC₃asub₁.trans <|
                (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
                  (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from
                    subset_union_left) |>.trans hA) (hC₃bsub.trans hC₃A))
          · -- C₁' ∩ (C₃a ∪ C₃b) = {x'}
            ext y; constructor
            · rintro ⟨hyC₁', hyC₃ab⟩
              rcases hyC₃ab with hyC₃a | hyC₃b
              · have : y ∈ C₁' ∩ C₃a := ⟨hyC₁', hyC₃a⟩
                rwa [hC₁'C₃a, mem_singleton_iff] at this
              · exact hC₁_C₃_sub y hyC₁' (hC₃bsub hyC₃b)
            · intro hy; rw [mem_singleton_iff] at hy; subst hy
              exact ⟨isSimpleArcEnd_mem_left hC₁'arc,
                Or.inl (isSimpleArcEnd_mem_right hC₃aarc)⟩
          · -- p₂ ∉ C₃a ∪ C₃b
            intro hp₂; rcases hp₂ with hp₂C₃a | hp₂C₃b
            · exact h12 (hC₃asub₁ hp₂C₃a)
            · exact h32 (hC₃bsub hp₂C₃b)
    · -- x' ∈ C₃: symmetric case
      obtain ⟨C₃', hC₃'sub, hC₃'arc⟩ :=
        arc_subarc_right hC₃ hx'C₃ hx'x hx'p₃
      have hC₁'C₃' : C₁' ∩ C₃' = {x'} :=
        mk_inter C₃' (hC₃'sub.trans (show C₃ ⊆ C₂ ∪ C₃ from
          subset_union_right)) (isSimpleArcEnd_mem_left hC₃'arc)
      by_cases hx'C₂ : x' ∈ C₂
      · -- x' ∈ C₃ ∩ C₂
        obtain ⟨C₂', hC₂'sub, hC₂'arc⟩ :=
          arc_subarc_right hC₂ hx'C₂ hx'x hx'p₂
        refine ⟨x', C₁', C₂', C₃', ?_, hC₁'arc, hC₂'arc,
          hC₃'arc,
          mk_inter C₂' (hC₂'sub.trans (show C₂ ⊆ C₂ ∪ C₃ from
            subset_union_left))
            (isSimpleArcEnd_mem_left hC₂'arc),
          hC₁'C₃',
          fun h => h23 (hC₂'sub h), fun h => h32 (hC₃'sub h)⟩
        exact union_subset (union_subset hC₁'A (hC₂'sub.trans hC₂A))
          (hC₃'sub.trans hC₃A)
      · -- x' ∈ C₃, x' ∉ C₂: find bridge from Cx to C₂
        have hCx_C₂_disj : Cx ∩ C₂ ∩ {x'} = ∅ := by
          ext y; simp only [mem_inter_iff, mem_singleton_iff,
            mem_empty_iff_false, iff_false, not_and]
          rintro ⟨_, hyC₂⟩ rfl; exact hx'C₂ hyC₂
        have hCxC₂ne : (Cx ∩ C₂).Nonempty :=
          ⟨x, isSimpleArcEnd_mem_left hCxarc,
            isSimpleArcEnd_mem_left hC₂⟩
        have hCxx'ne : (Cx ∩ {x'}).Nonempty :=
          ⟨x', isSimpleArcEnd_mem_right hCxarc, rfl⟩
        obtain ⟨C₂a, v₂, w₂, hC₂asub, hC₂aarc, hC₂aC₂, hC₂ax'⟩ :=
          isSimpleArcEnd_restriction
            (isSimpleArcEnd_isSimpleArc hCxarc)
            (isSimpleArcEnd_isClosed hC₂) isClosed_singleton
            hCx_C₂_disj hCxC₂ne hCxx'ne
        -- w₂ = x'
        have hw₂ : w₂ = x' := by
          have : {w₂} ⊆ ({x'} : Set E2') := hC₂ax' ▸ inter_subset_right
          rwa [singleton_subset_iff, mem_singleton_iff] at this
        rw [hw₂] at hC₂aarc; clear hw₂ hC₂ax' w₂
        -- v₂ ∈ C₂
        have hv₂C₂ : v₂ ∈ C₂ := by
          have : {v₂} ⊆ (C₂ : Set E2') := hC₂aC₂ ▸ inter_subset_right
          rwa [singleton_subset_iff] at this
        have hC₂asub₁ : C₂a ⊆ C₁ := hC₂asub.trans hCxsub
        have hC₂ap₂ : p₂ ∉ C₂a := fun h => h12 (hC₂asub₁ h)
        have hC₁'C₂a : C₁' ∩ C₂a = {x'} :=
          mk_inter_Cx C₂a hC₂asub (isSimpleArcEnd_mem_right hC₂aarc)
        by_cases hv₂x : v₂ = x
        · rw [hv₂x] at hC₂aarc hC₂aC₂
          have hC₂_C₂a_int : C₂ ∩ C₂a ⊆ {x} := by
            rw [Set.inter_comm]; exact inter_singleton_subset hC₂aC₂ Subset.rfl
          have hC₂' := isSimpleArcEnd_symm <| isSimpleArcEnd_concat
            (isSimpleArcEnd_symm hC₂) hC₂aarc hC₂_C₂a_int
          refine ⟨x', C₁', C₂ ∪ C₂a, C₃', ?_, hC₁'arc, hC₂',
            hC₃'arc, ?_, hC₁'C₃',
            ?_, fun h => h32 (hC₃'sub h)⟩
          · exact union_subset (union_subset hC₁'A
              (union_subset hC₂A (hC₂asub₁.trans <|
                (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
                  (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from
                    subset_union_left) |>.trans hA)))
              (hC₃'sub.trans hC₃A)
          · ext y; constructor
            · rintro ⟨hyC₁', hyC₂C₂a⟩
              rcases hyC₂C₂a with hyC₂ | hyC₂a
              · exact hC₁_C₂_sub y hyC₁' hyC₂
              · have : y ∈ C₁' ∩ C₂a := ⟨hyC₁', hyC₂a⟩
                rwa [hC₁'C₂a, mem_singleton_iff] at this
            · intro hy; rw [mem_singleton_iff] at hy; subst hy
              exact ⟨isSimpleArcEnd_mem_left hC₁'arc,
                Or.inr (isSimpleArcEnd_mem_right hC₂aarc)⟩
          · intro hp₃; rcases hp₃ with hp₃C₂ | hp₃C₂a
            · exact h23 hp₃C₂
            · exact h13 (hC₂asub₁ hp₃C₂a)
        · have hv₂p₂ : v₂ ≠ p₂ := by
            intro h; rw [h] at hC₂aarc
            exact hC₂ap₂ (isSimpleArcEnd_mem_left hC₂aarc)
          obtain ⟨C₂x, C₂b, hC₂xarc, hC₂barc, hC₂xC₂bint,
            hC₂xC₂bun⟩ :=
            isSimpleArcEnd_cut hC₂ hv₂C₂ hv₂x hv₂p₂
          have hC₂a_C₂b_int : C₂a ∩ C₂b ⊆ {v₂} := by
            intro y ⟨hyC₂a, hyC₂b⟩
            have hyC₂ : y ∈ C₂ := (hC₂xC₂bun ▸ subset_union_right) hyC₂b
            have : y ∈ C₂a ∩ C₂ := ⟨hyC₂a, hyC₂⟩
            rwa [hC₂aC₂, mem_singleton_iff] at this
          have hC₂'arc := isSimpleArcEnd_concat
            (isSimpleArcEnd_symm hC₂aarc) hC₂barc hC₂a_C₂b_int
          have hC₂bsub : C₂b ⊆ C₂ := hC₂xC₂bun ▸ subset_union_right
          refine ⟨x', C₁', C₂a ∪ C₂b, C₃', ?_, hC₁'arc, hC₂'arc,
            hC₃'arc, ?_, hC₁'C₃',
            ?_, fun h => h32 (hC₃'sub h)⟩
          · exact union_subset (union_subset hC₁'A
              (union_subset (hC₂asub₁.trans <|
                (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
                  (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from
                    subset_union_left) |>.trans hA) (hC₂bsub.trans hC₂A)))
              (hC₃'sub.trans hC₃A)
          · ext y; constructor
            · rintro ⟨hyC₁', hyC₂ab⟩
              rcases hyC₂ab with hyC₂a | hyC₂b
              · have : y ∈ C₁' ∩ C₂a := ⟨hyC₁', hyC₂a⟩
                rwa [hC₁'C₂a, mem_singleton_iff] at this
              · exact hC₁_C₂_sub y hyC₁' (hC₂bsub hyC₂b)
            · intro hy; rw [mem_singleton_iff] at hy; subst hy
              exact ⟨isSimpleArcEnd_mem_left hC₁'arc,
                Or.inl (isSimpleArcEnd_mem_right hC₂aarc)⟩
          · intro hp₃; rcases hp₃ with hp₃C₂a | hp₃C₂b
            · exact h13 (hC₂asub₁ hp₃C₂a)
            · exact h23 (hC₂bsub hp₃C₂b)

/-- Two arcs meeting C₁ in {x}: refine to all three {x'}.
    HOL Light: `simple_arc_sep2` (line 25118). -/
private theorem simple_arc_sep2 {A : Set E2'} {C₁ C₂ C₃ : Set E2'}
    {x p₁ p₂ p₃ : E2'}
    (hA : C₁ ∪ C₂ ∪ C₃ ⊆ A)
    (hC₁ : IsSimpleArcEnd C₁ x p₁)
    (hC₂ : IsSimpleArcEnd C₂ x p₂)
    (hC₃ : IsSimpleArcEnd C₃ x p₃)
    (h12 : C₁ ∩ C₂ = {x}) (h13 : C₁ ∩ C₃ = {x})
    (h23n : p₃ ∉ C₂) (h32n : p₂ ∉ C₃) :
    ∃ x' C₁' C₂' C₃',
      C₁' ∪ C₂' ∪ C₃' ⊆ A ∧
      IsSimpleArcEnd C₁' x' p₁ ∧
      IsSimpleArcEnd C₂' x' p₂ ∧
      IsSimpleArcEnd C₃' x' p₃ ∧
      C₁' ∩ C₂' = {x'} ∧
      C₂' ∩ C₃' = {x'} ∧
      C₃' ∩ C₁' = {x'} := by
  -- Restrict C₂ between C₃ and {p₂}
  have hC₃cl : IsClosed C₃ := isSimpleArcEnd_isClosed hC₃
  have hdisjp₂ : C₂ ∩ C₃ ∩ {p₂} = ∅ := by
    ext y; simp only [mem_inter_iff, mem_singleton_iff,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨_, _⟩ rfl; exact h32n ‹_›
  have hC₂C₃ne : (C₂ ∩ C₃).Nonempty :=
    ⟨x, isSimpleArcEnd_mem_left hC₂, isSimpleArcEnd_mem_left hC₃⟩
  have hC₂p₂ : (C₂ ∩ {p₂}).Nonempty :=
    ⟨p₂, isSimpleArcEnd_mem_right hC₂, rfl⟩
  obtain ⟨C₂', v, w, hC₂'sub, hC₂'arc, hC₂'C₃, hC₂'p₂⟩ :=
    isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc hC₂)
      hC₃cl isClosed_singleton hdisjp₂ hC₂C₃ne hC₂p₂
  -- w = p₂
  have hwp₂ : w = p₂ := by
    have : {w} ⊆ ({p₂} : Set E2') := hC₂'p₂ ▸ inter_subset_right
    rwa [singleton_subset_iff, mem_singleton_iff] at this
  rw [hwp₂] at hC₂'arc hC₂'p₂; clear hwp₂ w
  -- v ∈ C₃ and v ∈ C₂
  have hvC₃ : v ∈ C₃ := by
    have : {v} ⊆ (C₃ : Set E2') := hC₂'C₃ ▸ inter_subset_right
    rwa [singleton_subset_iff] at this
  have hvC₂ : v ∈ C₂ := hC₂'sub (isSimpleArcEnd_mem_left hC₂'arc)
  have hvp₃ : v ≠ p₃ := fun h => h23n (h ▸ hvC₂)
  -- Easy case: v = x  
  by_cases hvx : v = x
  · rw [hvx] at hC₂'arc hC₂'C₃
    have hC₂'eq : C₂' = C₂ :=
      isSimpleArcEnd_inj hC₂'arc hC₂
        (isSimpleArcEnd_isSimpleArc hC₂) hC₂'sub Subset.rfl
    rw [hC₂'eq] at hC₂'C₃
    refine ⟨x, C₁, C₂, C₃, hA, hC₁, hC₂, hC₃, h12, hC₂'C₃,
      Set.inter_comm C₁ C₃ ▸ h13⟩
  · -- General case: v ≠ x, v ∈ C₂ ∩ C₃
    -- Cut C₃ at v → C₃x: x→v, C₃v: v→p₃
    obtain ⟨C₃x, C₃v, hC₃xarc, hC₃varc, hC₃xC₃vint, hC₃xC₃vun⟩ :=
      isSimpleArcEnd_cut hC₃ hvC₃ hvx hvp₃
    have hC₃xsub : C₃x ⊆ C₃ := hC₃xC₃vun ▸ subset_union_left
    have hC₃vsub : C₃v ⊆ C₃ := hC₃xC₃vun ▸ subset_union_right
    -- x ∉ C₂' (since x ∈ C₂' → x ∈ C₂' ∩ C₃ = {v} → x = v, contradiction)
    have hxC₂' : x ∉ C₂' := by
      intro hx; have : x ∈ C₂' ∩ C₃ := ⟨hx, isSimpleArcEnd_mem_left hC₃⟩
      rw [hC₂'C₃, mem_singleton_iff] at this; exact hvx this.symm
    -- x ∉ C₃v (since x ∈ C₃v → x ∈ C₃x ∩ C₃v = {v} → x = v)
    have hxC₃v : x ∉ C₃v := by
      intro hx
      have : x ∈ C₃x ∩ C₃v :=
        ⟨isSimpleArcEnd_mem_left hC₃xarc, hx⟩
      rw [hC₃xC₃vint, mem_singleton_iff] at this; exact hvx this.symm
    -- C₃x ∩ C₁ = {x}
    have hC₃xC₁ : C₃x ∩ C₁ = {x} := by
      ext y; simp only [mem_inter_iff, mem_singleton_iff]; constructor
      · rintro ⟨hyC₃x, hyC₁⟩
        have : y ∈ C₁ ∩ C₃ := ⟨hyC₁, hC₃xsub hyC₃x⟩
        rwa [h13, mem_singleton_iff] at this
      · rintro rfl
        exact ⟨isSimpleArcEnd_mem_left hC₃xarc,
          isSimpleArcEnd_mem_left hC₁⟩
    -- New C₁' = C₁ ∪ C₃x, arc from v to p₁
    -- trans: C₃x reversed (v→x) + C₁ (x→p₁), inter C₃x ∩ C₁ = {x}
    have hNewC₁ : IsSimpleArcEnd (C₃x ∪ C₁) v p₁ :=
      isSimpleArcEnd_trans (isSimpleArcEnd_symm hC₃xarc) hC₁ hC₃xC₁
    -- (C₃x ∪ C₁) ∩ C₂' = {v}
    have hI12 : (C₃x ∪ C₁) ∩ C₂' = {v} := by
      ext y; simp only [mem_inter_iff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hyC₃xC₁, hyC₂'⟩
        rcases hyC₃xC₁ with hyC₃x | hyC₁
        · have : y ∈ C₂' ∩ C₃ := ⟨hyC₂', hC₃xsub hyC₃x⟩
          rwa [hC₂'C₃, mem_singleton_iff] at this
        · exfalso
          have hyeq : y ∈ C₁ ∩ C₂ := ⟨hyC₁, hC₂'sub hyC₂'⟩
          rw [h12, mem_singleton_iff] at hyeq
          exact hxC₂' (hyeq ▸ hyC₂')
      · rintro rfl
        exact ⟨Or.inl (isSimpleArcEnd_mem_right hC₃xarc),
          isSimpleArcEnd_mem_left hC₂'arc⟩
    -- C₂' ∩ C₃v = {v}
    have hI23 : C₂' ∩ C₃v = {v} := by
      ext y; simp only [mem_inter_iff, mem_singleton_iff]; constructor
      · rintro ⟨hyC₂', hyC₃v⟩
        have : y ∈ C₂' ∩ C₃ := ⟨hyC₂', hC₃vsub hyC₃v⟩
        rwa [hC₂'C₃, mem_singleton_iff] at this
      · rintro rfl
        exact ⟨isSimpleArcEnd_mem_left hC₂'arc,
          isSimpleArcEnd_mem_left hC₃varc⟩
    -- C₃v ∩ (C₃x ∪ C₁) = {v}
    have hI31 : C₃v ∩ (C₃x ∪ C₁) = {v} := by
      ext y; simp only [mem_inter_iff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hyC₃v, hyC₃xC₁⟩
        rcases hyC₃xC₁ with hyC₃x | hyC₁
        · have : y ∈ C₃x ∩ C₃v := ⟨hyC₃x, hyC₃v⟩
          rwa [hC₃xC₃vint, mem_singleton_iff] at this
        · exfalso
          have hyeq : y ∈ C₁ ∩ C₃ := ⟨hyC₁, hC₃vsub hyC₃v⟩
          rw [h13, mem_singleton_iff] at hyeq
          exact hxC₃v (hyeq ▸ hyC₃v)
      · rintro rfl
        exact ⟨isSimpleArcEnd_mem_left hC₃varc,
          Or.inl (isSimpleArcEnd_mem_right hC₃xarc)⟩
    -- Subset A
    have hC₁A : C₁ ⊆ A :=
      (show C₁ ⊆ C₁ ∪ C₂ from subset_union_left).trans
        (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_left) |>.trans hA
    have hC₂A : C₂ ⊆ A :=
      (show C₂ ⊆ C₁ ∪ C₂ from subset_union_right).trans
        (show C₁ ∪ C₂ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_left) |>.trans hA
    have hC₃A : C₃ ⊆ A :=
      (show C₃ ⊆ C₁ ∪ C₂ ∪ C₃ from subset_union_right).trans hA
    have hAsub : (C₃x ∪ C₁) ∪ C₂' ∪ C₃v ⊆ A :=
      union_subset (union_subset
        (union_subset (hC₃xsub.trans hC₃A) hC₁A) (hC₂'sub.trans hC₂A))
        (hC₃vsub.trans hC₃A)
    exact ⟨v, C₃x ∪ C₁, C₂', C₃v, hAsub, hNewC₁, hC₂'arc,
      hC₃varc, hI12, hI23, hI31⟩

/-- Three arcs from a common center can be refined so their pairwise
    intersections are exactly the common center.
    HOL Light: `simple_arc_sep` (line 25098). -/
theorem simple_arc_sep {A : Set E2'} {C₁ C₂ C₃ : Set E2'}
    {x p₁ p₂ p₃ : E2'}
    (hA : C₁ ∪ C₂ ∪ C₃ ⊆ A)
    (hC₁ : IsSimpleArcEnd C₁ x p₁) (h12 : p₂ ∉ C₁) (h13 : p₃ ∉ C₁)
    (hC₂ : IsSimpleArcEnd C₂ x p₂) (h21 : p₁ ∉ C₂) (h23 : p₃ ∉ C₂)
    (hC₃ : IsSimpleArcEnd C₃ x p₃) (h31 : p₁ ∉ C₃) (h32 : p₂ ∉ C₃) :
    ∃ x' C₁' C₂' C₃',
      C₁' ∪ C₂' ∪ C₃' ⊆ A ∧
      IsSimpleArcEnd C₁' x' p₁ ∧
      IsSimpleArcEnd C₂' x' p₂ ∧
      IsSimpleArcEnd C₃' x' p₃ ∧
      C₁' ∩ C₂' = {x'} ∧
      C₂' ∩ C₃' = {x'} ∧
      C₃' ∩ C₁' = {x'} := by
  obtain ⟨x', C₁', C₂', C₃', hAsub, hC₁', hC₂', hC₃',
    h₁₂, h₁₃, h₂₃, h₃₂⟩ :=
    simple_arc_sep3 hA hC₁ h12 h13 hC₂ h21 h23 hC₃ h31 h32
  exact simple_arc_sep2 hAsub hC₁' hC₂' hC₃' h₁₂ h₁₃ h₂₃ h₃₂
