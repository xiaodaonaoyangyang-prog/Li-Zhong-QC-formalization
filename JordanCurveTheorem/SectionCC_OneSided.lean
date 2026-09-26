/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionBB_K33Data

/-!
# Section CC: One-Sided Curves → K₃,₃ Embedding
## HOL Light: Section CC (Lines 55682–58066)

The main contradiction argument: if a simple closed curve is "one-sided"
(its complement is path-connected), then we can embed K₃,₃ in the plane,
contradicting nonplanarity.

### Key results
- `OneSidedJordanCurve`: definition of one-sided curve
- `JordanCurveK33Data`: the K₃,₃ data structure
- `jordanCurveK33Data_exists`: if one-sided, K₃,₃ data exists
- `jordanCurveK33_planeCriterion`: the constructed graph is a plane graph
-/

noncomputable section

open Set Function Metric Filter Topology

namespace JordanCurveTheorem

/-! ## Part 1: Basic properties of simple closed curves -/

/-- HOL Light: `simple_closed_curve_compact` (line 55686). -/
theorem isSimpleClosedCurve_isCompact {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    IsCompact C := by
  obtain ⟨f, rfl, hf, _, _⟩ := hC
  exact isCompact_Icc.image_of_continuousOn hf.continuousOn

/-- HOL Light: `simple_closed_curve_closed` (line 56568). -/
theorem isSimpleClosedCurve_isClosed {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    IsClosed C :=
  (isSimpleClosedCurve_isCompact hC).isClosed

/-- HOL Light: `simple_closed_curve_nonempty` (line 56166). -/
theorem isSimpleClosedCurve_nonempty {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    C.Nonempty := by
  obtain ⟨f, rfl, _, _, _⟩ := hC
  exact ⟨f 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩

/-- HOL Light: `simple_closed_curve_2pt` (line 56179). -/
theorem isSimpleClosedCurve_2pt {C : Set E2'} {p : E2'}
    (hC : IsSimpleClosedCurve C) (hp : p ∈ C) :
    ∃ q ∈ C, q ≠ p := by
  obtain ⟨f, rfl, hf, hinj, hf01⟩ := hC
  obtain ⟨t, ht, rfl⟩ := hp
  by_cases ht0 : t = 0 ∨ t = 1
  · refine ⟨f (1/2), mem_image_of_mem _ (by constructor <;> norm_num), ?_⟩
    intro heq
    have h0 : (0 : ℝ) ∈ Ico 0 1 := left_mem_Ico.mpr zero_lt_one
    have h12 : (1/2 : ℝ) ∈ Ico 0 1 := ⟨by norm_num, by norm_num⟩
    rcases ht0 with rfl | rfl
    · exact absurd (hinj h0 h12 heq.symm) (by norm_num)
    · exact absurd (hinj h0 h12 (hf01.trans heq.symm)) (by norm_num)
  · push Not at ht0
    refine ⟨f 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one), ?_⟩
    intro heq
    exact ht0.1 (hinj (left_mem_Ico.mpr zero_lt_one)
      ⟨ht.1, lt_of_le_of_ne ht.2 ht0.2⟩ heq).symm

/-! ## Part 2: Extremal coordinates -/

/-- HOL Light: `ymaxQ` (line 55832). Supremum of y-coordinates on a curve. -/
def ymaxQ (C : Set E2') : ℝ := sSup ((fun p : E2' => p 1) '' C)

/-- HOL Light: `yminQ` (line 55833). Infimum of y-coordinates on a curve. -/
def yminQ (C : Set E2') : ℝ := sInf ((fun p : E2' => p 1) '' C)

/-- HOL Light: `xmaxQ` (line 55834). Supremum of x-coordinates on a curve. -/
def xmaxQ (C : Set E2') : ℝ := sSup ((fun p : E2' => p 0) '' C)

/-- HOL Light: `xminQ` (line 55835). Infimum of x-coordinates on a curve. -/
def xminQ (C : Set E2') : ℝ := sInf ((fun p : E2' => p 0) '' C)

/-- HOL Light: `ymaxQ_exists` (line 55900) + `ymaxQexists_lemma` (line 55713). -/
theorem ymaxQ_exists {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    ∃ p ∈ C, p 1 = ymaxQ C := by
  obtain ⟨x, hx, heq⟩ := (isSimpleClosedCurve_isCompact hC).exists_sSup_image_eq
    (isSimpleClosedCurve_nonempty hC) (PiLp.continuous_apply 2 _ 1).continuousOn
  exact ⟨x, hx, heq.symm⟩

/-- HOL Light: `ymaxQ_max` (line 55992). Renamed to `le_ymaxQ`. -/
theorem le_ymaxQ {C : Set E2'} (hC : IsSimpleClosedCurve C) {p : E2'} (hp : p ∈ C) :
    p 1 ≤ ymaxQ C :=
  le_csSup ((isSimpleClosedCurve_isCompact hC).image
    (PiLp.continuous_apply 2 _ 1)).bddAbove (mem_image_of_mem _ hp)

/-- HOL Light: `yminQ_exists` (line 55917) + `yminQexists_lemma` (line 55747). -/
theorem yminQ_exists {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    ∃ p ∈ C, p 1 = yminQ C := by
  obtain ⟨x, hx, heq⟩ := (isSimpleClosedCurve_isCompact hC).exists_sInf_image_eq
    (isSimpleClosedCurve_nonempty hC) (PiLp.continuous_apply 2 _ 1).continuousOn
  exact ⟨x, hx, heq.symm⟩

/-- HOL Light: `yminQ_min` (line 56024). Renamed to `yminQ_le`. -/
theorem yminQ_le {C : Set E2'} (hC : IsSimpleClosedCurve C) {p : E2'} (hp : p ∈ C) :
    yminQ C ≤ p 1 :=
  csInf_le ((isSimpleClosedCurve_isCompact hC).image
    (PiLp.continuous_apply 2 _ 1)).bddBelow (mem_image_of_mem _ hp)

/-- HOL Light: `xmaxQ_exists` (line 55942). -/
theorem xmaxQ_exists {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    ∃ p ∈ C, p 0 = xmaxQ C := by
  obtain ⟨x, hx, heq⟩ := (isSimpleClosedCurve_isCompact hC).exists_sSup_image_eq
    (isSimpleClosedCurve_nonempty hC) (PiLp.continuous_apply 2 _ 0).continuousOn
  exact ⟨x, hx, heq.symm⟩

/-- HOL Light: `xmaxQ_max` (line 56053). Renamed to `le_xmaxQ`. -/
theorem le_xmaxQ {C : Set E2'} (hC : IsSimpleClosedCurve C) {p : E2'} (hp : p ∈ C) :
    p 0 ≤ xmaxQ C :=
  le_csSup ((isSimpleClosedCurve_isCompact hC).image
    (PiLp.continuous_apply 2 _ 0)).bddAbove (mem_image_of_mem _ hp)

/-- HOL Light: `xminQ_exists` (line 55967). -/
theorem xminQ_exists {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    ∃ p ∈ C, p 0 = xminQ C := by
  obtain ⟨x, hx, heq⟩ := (isSimpleClosedCurve_isCompact hC).exists_sInf_image_eq
    (isSimpleClosedCurve_nonempty hC) (PiLp.continuous_apply 2 _ 0).continuousOn
  exact ⟨x, hx, heq.symm⟩

/-- HOL Light: `xminQ_min` (line 56107). Renamed to `xminQ_le`. -/
theorem xminQ_le {C : Set E2'} (hC : IsSimpleClosedCurve C) {p : E2'} (hp : p ∈ C) :
    xminQ C ≤ p 0 :=
  csInf_le ((isSimpleClosedCurve_isCompact hC).image
    (PiLp.continuous_apply 2 _ 0)).bddBelow (mem_image_of_mem _ hp)

/-! ## Part 3: Structural lemmas -/

/-- HOL Light: `simple_closed_curve_nsubset_arc` (line 56237).
A simple closed curve cannot be a subset of a simple arc. -/
theorem isSimpleClosedCurve_not_subset_arc {C E : Set E2'}
    (hC : IsSimpleClosedCurve C) (hE : IsSimpleArc E) : ¬(C ⊆ E) := by
  intro hCE
  obtain ⟨p, hp⟩ := isSimpleClosedCurve_nonempty hC
  obtain ⟨q, hq, hqp⟩ := isSimpleClosedCurve_2pt hC hp
  obtain ⟨C₁, C₂, hC₁, hC₂, hunion, hinter⟩ :=
    isSimpleClosedCurve_cut hC hp hq hqp.symm
  rw [← hunion] at hCE
  have h₁ := cutArc_unique hE (subset_union_left.trans hCE) hC₁
  have h₂ := cutArc_unique hE (subset_union_right.trans hCE) hC₂
  have heq : C₁ = C₂ := h₁.symm.trans h₂
  have hfin : C₁ = {p, q} := by rw [← heq] at hinter; rwa [inter_self] at hinter
  exact isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc (hfin ▸ hC₁))
    (hfin ▸ (Set.finite_singleton q).insert p)

/-- HOL Light: `xmin_lt_xmax` (line 56268). -/
theorem xminQ_lt_xmaxQ {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    xminQ C < xmaxQ C := by
  by_contra h; push Not at h
  have hle : xminQ C ≤ xmaxQ C := by
    obtain ⟨p, hp, _⟩ := xminQ_exists hC; exact (xminQ_le hC hp).trans (le_xmaxQ hC hp)
  have heq : xminQ C = xmaxQ C := le_antisymm hle h
  have hx : ∀ p ∈ C, p 0 = xminQ C := fun p hp =>
    le_antisymm (heq ▸ le_xmaxQ hC hp) (xminQ_le hC hp)
  obtain ⟨p, hp⟩ := isSimpleClosedCurve_nonempty hC
  obtain ⟨q, hq, hpq⟩ := isSimpleClosedCurve_2pt hC hp
  have hyneq : p 1 ≠ q 1 := by
    intro he; apply hpq
    ext i; fin_cases i
    · exact (hx _ hq).trans (hx _ hp).symm
    · exact he.symm
  have hymlt : yminQ C < ymaxQ C := by
    by_contra hym; push Not at hym
    have hyle := (yminQ_le hC hp).trans (le_ymaxQ hC hp)
    have hyeq := le_antisymm hyle hym
    exact hyneq ((le_antisymm (hyeq ▸ le_ymaxQ hC hp) (yminQ_le hC hp)).trans
      (le_antisymm (hyeq ▸ le_ymaxQ hC hq) (yminQ_le hC hq)).symm)
  have hsub : C ⊆ segment ℝ (point (xminQ C, yminQ C)) (point (xminQ C, ymaxQ C)) := by
    intro x hxC; rw [segment_vertical _ _ _ hymlt.le]
    exact ⟨x 1, yminQ_le hC hxC, le_ymaxQ hC hxC, by
      ext i; fin_cases i <;> simp [hx x hxC]⟩
  exact isSimpleClosedCurve_not_subset_arc hC
    (isSimpleArcEnd_isSimpleArc (segment_isSimpleArcEnd (fun h =>
      hymlt.ne (congr_arg Prod.snd (point_injective h))))) hsub

/-- HOL Light: `ymin_lt_ymax` (line 56431). -/
theorem yminQ_lt_ymaxQ {C : Set E2'} (hC : IsSimpleClosedCurve C) :
    yminQ C < ymaxQ C := by
  by_contra h; push Not at h
  have hyle := (yminQ_le hC (yminQ_exists hC).choose_spec.1).trans
    (le_ymaxQ hC (yminQ_exists hC).choose_spec.1)
  have hyeq := le_antisymm hyle h
  have hy : ∀ p ∈ C, p 1 = yminQ C := fun p hp =>
    le_antisymm (hyeq ▸ le_ymaxQ hC hp) (yminQ_le hC hp)
  have hxlt := xminQ_lt_xmaxQ hC
  have hsub : C ⊆ segment ℝ (point (xminQ C, yminQ C)) (point (xmaxQ C, yminQ C)) := by
    intro x hxC; rw [segment_horizontal _ _ _ hxlt.le]
    exact ⟨x 0, xminQ_le hC hxC, le_xmaxQ hC hxC, by
      ext i; fin_cases i <;> simp [hy x hxC]⟩
  exact isSimpleClosedCurve_not_subset_arc hC
    (isSimpleArcEnd_isSimpleArc (segment_isSimpleArcEnd (fun h =>
      hxlt.ne (congr_arg Prod.fst (point_injective h))))) hsub

/-- HOL Light: `simple_arc_end_IVT` (line 57015).
Intermediate value theorem for arcs: if an arc goes from v to w,
and v i ≤ y ≤ w i, then some point on the arc has coordinate i equal to y. -/
theorem isSimpleArcEnd_IVT {C : Set E2'} {v w : E2'} {i : Fin 2} {y : ℝ}
    (hC : IsSimpleArcEnd C v w) (hvy : v i ≤ y) (hyw : y ≤ w i) :
    ∃ u ∈ C, u i = y := by
  obtain ⟨f, rfl, hf, _, hf0, hf1⟩ := hC
  have hfi : ContinuousOn (fun t => f t i) (Icc 0 1) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn hf.continuousOn
  have hmem : y ∈ Icc (f 0 i) (f 1 i) := by simp only [hf0, hf1]; exact ⟨hvy, hyw⟩
  obtain ⟨t, ht, htval⟩ := intermediate_value_Icc zero_le_one hfi hmem
  exact ⟨f t, mem_image_of_mem _ ht, htval⟩

/-! ## Part 4: Construction mk_C -/

/-- HOL Light: `simple_closed_curve_mk_C` (line 56584).
Construct an arc C connecting a top point v1 to a bottom point v2,
meeting Q in exactly {v1, v2}, passing to the right of Q. -/
theorem isSimpleClosedCurve_mk_C {Q : Set E2'}
    (hQ : IsSimpleClosedCurve Q) :
    ∃ C v1 v2, IsSimpleArcEnd C v1 v2 ∧
      C ∩ Q = {v1, v2} ∧
      v2 1 = yminQ Q ∧
      v1 1 = ymaxQ Q ∧
      (∀ x ∈ C, x 1 = yminQ Q ∨ x 1 = ymaxQ Q ∨ xmaxQ Q < x 0) := by
  -- Setup: extremal points and coordinates
  obtain ⟨pbot, hpbotQ, hpbot_y⟩ := yminQ_exists hQ
  obtain ⟨ptop, hptopQ, hptop_y⟩ := ymaxQ_exists hQ
  have hxle : xminQ Q ≤ xmaxQ Q := by linarith [xminQ_lt_xmaxQ hQ]
  have hyle : yminQ Q ≤ ymaxQ Q := by linarith [yminQ_lt_ymaxQ hQ]
  have hymlt : yminQ Q < ymaxQ Q := yminQ_lt_ymaxQ hQ
  set R := xmaxQ Q + 1
  have hR_bound : ∀ p ∈ Q, p 0 < R := fun p hp => by linarith [le_xmaxQ hQ hp]
  have hR_ge_xmin : xminQ Q ≤ R := by linarith
  -- Key points
  set a2 := point (R, yminQ Q) -- bottom-right corner
  set b1 := point (R, ymaxQ Q) -- top-right corner
  -- a2 and b1 are NOT in Q (their x-coord is R > xmaxQ)
  have ha2_nQ : a2 ∉ Q := fun h => by
    linarith [hR_bound a2 h, show a2 0 = R from by simp [a2, point]]
  have hb1_nQ : b1 ∉ Q := fun h => by
    linarith [hR_bound b1 h, show b1 0 = R from by simp [b1, point]]
  -- Bottom segment Ca: horizontal at yminQ from xminQ to R
  set Ca := segment ℝ (point (xminQ Q, yminQ Q)) a2
  have hCa_arc := segment_isSimpleArcEnd (show point (xminQ Q, yminQ Q) ≠ a2 by
    simp only [a2]; intro h; have := congrArg (· 0) h; simp [point] at this; linarith)
  -- Top segment Cb: horizontal at ymaxQ from xminQ to R
  set Cb := segment ℝ (point (xminQ Q, ymaxQ Q)) b1
  have hCb_arc := segment_isSimpleArcEnd (show point (xminQ Q, ymaxQ Q) ≠ b1 by
    simp only [b1]; intro h; have := congrArg (· 0) h; simp [point] at this; linarith)
  -- Vertical segment Cc: from a2 to b1
  set Cc := segment ℝ a2 b1
  have hab_ne : a2 ≠ b1 := by
    simp only [a2, b1]; intro h; have := congrArg (· 1) h; simp [point] at this; linarith
  have hCc_arc := segment_isSimpleArcEnd hab_ne
  -- Q is closed
  have hQcl : IsClosed Q := (isSimpleClosedCurve_isCompact hQ).isClosed
  -- Restrict bottom segment: get sub-arc from v2 (in Q) to a2
  have hCa_sa := isSimpleArcEnd_isSimpleArc hCa_arc
  have hCaQ_cl : IsClosed (Ca ∩ Q) := (isSimpleArc_compact hCa_sa).isClosed.inter hQcl
  have hCa_CaQ_nonempty : (Ca ∩ (Ca ∩ Q)).Nonempty := by
    have hpbot_Ca : pbot ∈ Ca := by
      rw [show Ca = segment ℝ (point (xminQ Q, yminQ Q)) a2 from rfl,
          segment_horizontal _ _ _ hR_ge_xmin]
      exact ⟨pbot 0, xminQ_le hQ hpbotQ, by linarith [le_xmaxQ hQ hpbotQ],
        by ext i; fin_cases i <;> simp [point, hpbot_y]⟩
    exact ⟨pbot, hpbot_Ca, hpbot_Ca, hpbotQ⟩
  have hCa_a2_nonempty : (Ca ∩ {a2}).Nonempty :=
    ⟨a2, isSimpleArcEnd_mem_right hCa_arc, mem_singleton _⟩
  have hCa_disj : Ca ∩ (Ca ∩ Q) ∩ {a2} = ∅ := by
    rw [Set.inter_assoc]
    ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨_, ⟨_, hxQ⟩, rfl⟩; exact ha2_nQ hxQ
  -- Apply restriction to bottom segment
  obtain ⟨Ca', v2, w2, hCa'sub, hCa'arc, hCa'Q, hCa'a2⟩ :=
    isSimpleArcEnd_restriction hCa_sa hCaQ_cl isClosed_singleton
      hCa_disj hCa_CaQ_nonempty hCa_a2_nonempty
  -- w2 = a2 (the restriction endpoint at {a2})
  have hw2_a2 : w2 = a2 := by
    have : {w2} ⊆ ({a2} : Set E2') := by rw [← hCa'a2]; exact Set.inter_subset_right
    exact mem_singleton_iff.mp (Set.singleton_subset_iff.mp this)
  subst hw2_a2
  -- v2 ∈ Q and v2 1 = yminQ (on horizontal at yminQ)
  have hv2_mem : v2 ∈ Ca' ∩ (Ca ∩ Q) := by rw [hCa'Q]; exact mem_singleton _
  have hv2Q : v2 ∈ Q := hv2_mem.2.2
  have hv2_y : v2 1 = yminQ Q := by
    have hv2Ca : v2 ∈ Ca := hv2_mem.2.1
    rw [show Ca = segment ℝ (point (xminQ Q, yminQ Q)) a2 from rfl,
        segment_horizontal _ _ _ hR_ge_xmin] at hv2Ca
    obtain ⟨t, _, _, rfl⟩ := hv2Ca; simp [point]
  -- Similarly restrict top segment
  have hCb_sa := isSimpleArcEnd_isSimpleArc hCb_arc
  have hCbQ_cl : IsClosed (Cb ∩ Q) := (isSimpleArc_compact hCb_sa).isClosed.inter hQcl
  have hCb_CbQ_nonempty : (Cb ∩ (Cb ∩ Q)).Nonempty := by
    have hptop_Cb : ptop ∈ Cb := by
      rw [show Cb = segment ℝ (point (xminQ Q, ymaxQ Q)) b1 from rfl,
          segment_horizontal _ _ _ hR_ge_xmin]
      exact ⟨ptop 0, xminQ_le hQ hptopQ, by linarith [le_xmaxQ hQ hptopQ],
        by ext i; fin_cases i <;> simp [point, hptop_y]⟩
    exact ⟨ptop, hptop_Cb, hptop_Cb, hptopQ⟩
  have hCb_b1_nonempty : (Cb ∩ {b1}).Nonempty :=
    ⟨b1, isSimpleArcEnd_mem_right hCb_arc, mem_singleton _⟩
  have hCb_disj : Cb ∩ (Cb ∩ Q) ∩ {b1} = ∅ := by
    rw [Set.inter_assoc]
    ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨_, ⟨_, hxQ⟩, rfl⟩; exact hb1_nQ hxQ
  obtain ⟨Cb', v1, w1, hCb'sub, hCb'arc, hCb'Q, hCb'b1⟩ :=
    isSimpleArcEnd_restriction hCb_sa hCbQ_cl isClosed_singleton
      hCb_disj hCb_CbQ_nonempty hCb_b1_nonempty
  have hw1_b1 : w1 = b1 := by
    have : {w1} ⊆ ({b1} : Set E2') := by rw [← hCb'b1]; exact Set.inter_subset_right
    exact mem_singleton_iff.mp (Set.singleton_subset_iff.mp this)
  subst hw1_b1
  have hv1_mem : v1 ∈ Cb' ∩ (Cb ∩ Q) := by rw [hCb'Q]; exact mem_singleton _
  have hv1Q : v1 ∈ Q := hv1_mem.2.2
  have hv1_y : v1 1 = ymaxQ Q := by
    have hv1Cb : v1 ∈ Cb := hv1_mem.2.1
    rw [show Cb = segment ℝ (point (xminQ Q, ymaxQ Q)) b1 from rfl,
        segment_horizontal _ _ _ hR_ge_xmin] at hv1Cb
    obtain ⟨t, _, _, rfl⟩ := hv1Cb; simp [point]
  -- Concatenate: Ca' (v2→a2) + Cc (a2→b1) + Cb'_sym (b1→v1)
  -- First join Ca' and Cc
  have ha2_Ca' : a2 ∈ Ca' := isSimpleArcEnd_mem_right hCa'arc
  have hb1_Cb' : b1 ∈ Cb' := isSimpleArcEnd_mem_right hCb'arc
  have hCa'Cc_inter : Ca' ∩ Cc = {a2} := by
    ext x; simp only [mem_inter_iff, mem_singleton_iff]; constructor
    · rintro ⟨hx1, hx2⟩
      have hxCa : x ∈ Ca := hCa'sub hx1
      rw [show Ca = segment ℝ (point (xminQ Q, yminQ Q)) a2 from rfl,
          segment_horizontal _ _ _ hR_ge_xmin] at hxCa
      obtain ⟨t1, _, _, rfl⟩ := hxCa
      rw [show Cc = segment ℝ a2 b1 from rfl, segment_vertical _ _ _ hyle] at hx2
      obtain ⟨t2, _, _, heq⟩ := hx2
      have h0 := congrArg (· 0) heq; simp [point] at h0
      have h1 := congrArg (· 1) heq; simp [point] at h1
      ext i; fin_cases i <;> simp [point, a2, R, ← h0]
    · rintro rfl; exact ⟨ha2_Ca', isSimpleArcEnd_mem_left hCc_arc⟩
  have hCa'Cc := isSimpleArcEnd_trans hCa'arc hCc_arc hCa'Cc_inter
  -- Join (Ca' ∪ Cc) with Cb'_sym (reversed Cb')
  have hCb'_sym := isSimpleArcEnd_symm hCb'arc -- b1 → v1
  have hCa'CcCb_inter : (Ca' ∪ Cc) ∩ Cb' = {b1} := by
    ext x; simp only [mem_inter_iff, mem_union, mem_singleton_iff]; constructor
    · rintro ⟨hx1 | hx1, hx2⟩
      · exfalso
        have hxCa : x ∈ Ca := hCa'sub hx1
        have hxCb : x ∈ Cb := hCb'sub hx2
        rw [show Ca = segment ℝ (point (xminQ Q, yminQ Q)) a2 from rfl,
            segment_horizontal _ _ _ hR_ge_xmin] at hxCa
        rw [show Cb = segment ℝ (point (xminQ Q, ymaxQ Q)) b1 from rfl,
            segment_horizontal _ _ _ hR_ge_xmin] at hxCb
        obtain ⟨_, _, _, rfl⟩ := hxCa
        obtain ⟨_, _, _, heq⟩ := hxCb
        have := congrArg (· 1) heq; simp [point] at this; linarith
      · have hxCb : x ∈ Cb := hCb'sub hx2
        rw [show Cc = segment ℝ a2 b1 from rfl, segment_vertical _ _ _ hyle] at hx1
        rw [show Cb = segment ℝ (point (xminQ Q, ymaxQ Q)) b1 from rfl,
            segment_horizontal _ _ _ hR_ge_xmin] at hxCb
        obtain ⟨t1, _, _, rfl⟩ := hx1
        obtain ⟨t2, _, _, heq⟩ := hxCb
        have h0 := congrArg (· 0) heq; simp [point] at h0
        have h1 := congrArg (· 1) heq; simp [point] at h1
        ext i; fin_cases i <;> simp [point, b1, R, ← h1]
    · rintro rfl; exact ⟨Or.inr (isSimpleArcEnd_mem_right hCc_arc), hb1_Cb'⟩
  -- C = (Ca' ∪ Cc) ∪ Cb' is arc from v2 to v1
  set C := (Ca' ∪ Cc) ∪ Cb'
  have hC_arc : IsSimpleArcEnd C v2 v1 :=
    isSimpleArcEnd_trans hCa'Cc hCb'_sym hCa'CcCb_inter
  -- Verify C ∩ Q = {v1, v2}
  have hCQ : C ∩ Q = {v1, v2} := by
    ext x; simp only [C, mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨(hx1 | hx1) | hx1, hxQ⟩
      · have : x ∈ Ca' ∩ (Ca ∩ Q) := ⟨hx1, hCa'sub hx1, hxQ⟩
        rw [hCa'Q] at this; right; exact mem_singleton_iff.mp this
      · exfalso
        rw [show Cc = segment ℝ a2 b1 from rfl, segment_vertical _ _ _ hyle] at hx1
        obtain ⟨_, _, _, rfl⟩ := hx1
        have := hR_bound _ hxQ; simp [point] at this
      · have : x ∈ Cb' ∩ (Cb ∩ Q) := ⟨hx1, hCb'sub hx1, hxQ⟩
        rw [hCb'Q] at this; left; exact mem_singleton_iff.mp this
    · rintro (rfl | rfl)
      · exact ⟨Or.inr hv1_mem.1, hv1Q⟩
      · exact ⟨Or.inl (Or.inl hv2_mem.1), hv2Q⟩
  -- Verify coordinate property
  have hC_coords : ∀ x ∈ C, x 1 = yminQ Q ∨ x 1 = ymaxQ Q ∨ xmaxQ Q < x 0 := by
    intro x hx
    simp only [C, mem_union] at hx
    rcases hx with (hx | hx) | hx
    · have h : x ∈ segment ℝ (point (xminQ Q, yminQ Q)) (point (R, yminQ Q)) := hCa'sub hx
      rw [segment_horizontal _ _ _ hR_ge_xmin] at h
      obtain ⟨_, _, _, rfl⟩ := h; left; simp [point]
    · have h : x ∈ segment ℝ (point (R, yminQ Q)) (point (R, ymaxQ Q)) := hx
      rw [segment_vertical _ _ _ hyle] at h
      obtain ⟨_, _, _, rfl⟩ := h; right; right; simp [point, R]
    · have h : x ∈ segment ℝ (point (xminQ Q, ymaxQ Q)) (point (R, ymaxQ Q)) := hCb'sub hx
      rw [segment_horizontal _ _ _ hR_ge_xmin] at h
      obtain ⟨_, _, _, rfl⟩ := h; right; left; simp [point]
  exact ⟨C, v1, v2, isSimpleArcEnd_symm hC_arc, hCQ, hv2_y, hv1_y, hC_coords⟩

/-! ## Part 5: Construction mk_ABD -/

/-- HOL Light: `simple_closed_curve_mk_ABD` (line 57049).
Given v1 (top) and v2 (bottom) on Q, cut Q into arcs A and B,
and construct a horizontal arc D through the middle. -/
theorem isSimpleClosedCurve_mk_ABD {Q : Set E2'} {v1 v2 : E2'}
    (hQ : IsSimpleClosedCurve Q)
    (hv1 : v1 ∈ Q) (hv2 : v2 ∈ Q)
    (hv2_ymin : v2 1 = yminQ Q) (hv1_ymax : v1 1 = ymaxQ Q) :
    ∃ A B D w1 w2,
      IsSimpleArcEnd A v1 v2 ∧
      IsSimpleArcEnd B v1 v2 ∧
      A ∪ B = Q ∧
      A ∩ B = {v1, v2} ∧
      w1 ≠ v1 ∧ w1 ≠ v2 ∧ w2 ≠ v1 ∧ w2 ≠ v2 ∧
      w1 ∈ A ∧ w2 ∈ B ∧
      IsSimpleArcEnd D w1 w2 ∧
      D ∩ Q = {w1, w2} ∧
      (∀ x ∈ D, yminQ Q < x 1 ∧ x 1 < ymaxQ Q ∧ x 0 ≤ xmaxQ Q) := by
  -- Step 1: key constants
  have hymlt := yminQ_lt_ymaxQ hQ
  have hv12_ne : v1 ≠ v2 := by
    intro h; rw [h] at hv1_ymax; linarith [hv2_ymin.symm.trans hv1_ymax]
  -- Step 2: cut Q at v1, v2
  obtain ⟨A, B, hA_arc, hB_arc, hAB_union, hAB_inter⟩ :=
    isSimpleClosedCurve_cut hQ hv1 hv2 hv12_ne
  -- Step 3: horizontal segment at ymid
  let ymid := (yminQ Q + ymaxQ Q) / 2
  have hymid_lb : yminQ Q < ymid := by change yminQ Q < (yminQ Q + ymaxQ Q) / 2; linarith
  have hymid_ub : ymid < ymaxQ Q := by change (yminQ Q + ymaxQ Q) / 2 < ymaxQ Q; linarith
  have hxle : xminQ Q ≤ xmaxQ Q := (xminQ_lt_xmaxQ hQ).le
  have hxlt : xminQ Q < xmaxQ Q := xminQ_lt_xmaxQ hQ
  let p1 := point (xminQ Q, ymid)
  let p2 := point (xmaxQ Q, ymid)
  have hp12_ne : p1 ≠ p2 := by
    intro h; have := congrArg (· 0) h; simp [point, p1, p2] at this; linarith
  -- Segment C
  set Seg := segment ℝ p1 p2 with hSeg_def
  have hSeg_arc := segment_isSimpleArcEnd hp12_ne
  have hSeg_sa := isSimpleArcEnd_isSimpleArc hSeg_arc
  -- All points on Seg have y = ymid
  have hSeg_y : ∀ x ∈ Seg, x 1 = ymid := by
    intro x hx; rw [hSeg_def, segment_horizontal _ _ _ hxle] at hx
    obtain ⟨t, _, _, rfl⟩ := hx; simp [point]
  -- Coordinate bounds on Seg
  have hSeg_bounds : ∀ x ∈ Seg, yminQ Q < x 1 ∧ x 1 < ymaxQ Q ∧ x 0 ≤ xmaxQ Q := by
    intro x hx
    have hxy := hSeg_y x hx
    rw [hSeg_def, segment_horizontal _ _ _ hxle] at hx
    obtain ⟨t, _, hts, rfl⟩ := hx
    simp only [Fin.isValue, point_coord_one, point_coord_zero]
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Step 4: Seg ∩ Q doesn't contain v1, v2 (y-coordinate mismatch)
  have hv1_nmid : v1 1 ≠ ymid := by rw [hv1_ymax]; linarith
  have hv2_nmid : v2 1 ≠ ymid := by rw [hv2_ymin]; linarith
  -- Step 5: A∩Seg, B∩Seg are closed, disjoint
  have hQcl := isSimpleClosedCurve_isClosed hQ
  have hAcl : IsClosed A :=
    (isSimpleArc_compact (isSimpleArcEnd_isSimpleArc hA_arc)).isClosed
  have hBcl : IsClosed B :=
    (isSimpleArc_compact (isSimpleArcEnd_isSimpleArc hB_arc)).isClosed
  have hSegcl : IsClosed Seg :=
    (isSimpleArc_compact hSeg_sa).isClosed
  have hASeg_cl : IsClosed (A ∩ Seg) := hAcl.inter hSegcl
  have hBSeg_cl : IsClosed (B ∩ Seg) := hBcl.inter hSegcl
  have hASeg_BSeg_disj : Seg ∩ (A ∩ Seg) ∩ (B ∩ Seg) = ∅ := by
    ext x; simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hxSeg, hxA, _⟩, hxB, _⟩
    have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩
    rw [hAB_inter] at hxAB
    simp only [mem_insert_iff, mem_singleton_iff] at hxAB
    rcases hxAB with rfl | rfl
    · exact hv1_nmid (hSeg_y _ hxSeg)
    · exact hv2_nmid (hSeg_y _ hxSeg)
  -- Step 6: IVT → A∩Seg nonempty, B∩Seg nonempty
  -- Each arc connects v1 (y=ymaxQ) to v2 (y=yminQ), so crosses y=ymid
  have hA_sub_Q : A ⊆ Q := by rw [← hAB_union]; exact Set.subset_union_left
  have hB_sub_Q : B ⊆ Q := by rw [← hAB_union]; exact Set.subset_union_right
  have hIVT_arc : ∀ E, IsSimpleArcEnd E v1 v2 → E ⊆ Q → (Seg ∩ (E ∩ Seg)).Nonempty := by
    intro E hE hEQ
    -- Use IVT: arc from v1 (y=ymaxQ) to v2 (y=yminQ) crosses y=ymid
    -- Apply to reversed arc (v2 → v1)
    obtain ⟨u, huE, hu_y⟩ := isSimpleArcEnd_IVT (i := 1) (y := ymid)
      (isSimpleArcEnd_symm hE) (by rw [hv2_ymin]; linarith) (by rw [hv1_ymax]; linarith)
    -- u ∈ E with u 1 = ymid, and u ∈ Q (since E ⊆ Q)
    have huQ := hEQ huE
    -- u ∈ Seg: need u 0 ∈ [xminQ Q, xmaxQ Q] and u 1 = ymid
    have hu_Seg : u ∈ Seg := by
      rw [hSeg_def, segment_horizontal _ _ _ hxle]
      exact ⟨u 0, xminQ_le hQ huQ, le_xmaxQ hQ huQ,
        by ext i; fin_cases i <;> simp [point, hu_y]⟩
    exact ⟨u, hu_Seg, huE, hu_Seg⟩
  have hASeg_nonempty : (Seg ∩ (A ∩ Seg)).Nonempty := hIVT_arc A hA_arc hA_sub_Q
  have hBSeg_nonempty : (Seg ∩ (B ∩ Seg)).Nonempty := hIVT_arc B hB_arc hB_sub_Q
  -- Step 7: Apply restriction
  obtain ⟨D, w1, w2, hDsub, hD_arc, hDASeg, hDBSeg⟩ :=
    isSimpleArcEnd_restriction hSeg_sa hASeg_cl hBSeg_cl
      hASeg_BSeg_disj hASeg_nonempty hBSeg_nonempty
  -- Pre-derive key memberships
  have hw1_mem : w1 ∈ D ∩ (A ∩ Seg) := by rw [hDASeg]; exact mem_singleton _
  have hw2_mem : w2 ∈ D ∩ (B ∩ Seg) := by rw [hDBSeg]; exact mem_singleton _
  have hw1D : w1 ∈ D := hw1_mem.1
  have hw1A : w1 ∈ A := hw1_mem.2.1
  have hw1Seg : w1 ∈ Seg := hw1_mem.2.2
  have hw2D : w2 ∈ D := hw2_mem.1
  have hw2B : w2 ∈ B := hw2_mem.2.1
  have hw2Seg : w2 ∈ Seg := hw2_mem.2.2
  have hw1_ymid : w1 1 = ymid := hSeg_y _ hw1Seg
  have hw2_ymid : w2 1 = ymid := hSeg_y _ hw2Seg
  -- ≠ proofs: w has y=ymid, but v1 has y=ymaxQ ≠ ymid, v2 has y=yminQ ≠ ymid
  have hw1_ne_v1 : w1 ≠ v1 := fun h => hv1_nmid (h ▸ hw1_ymid)
  have hw1_ne_v2 : w1 ≠ v2 := fun h => hv2_nmid (h ▸ hw1_ymid)
  have hw2_ne_v1 : w2 ≠ v1 := fun h => hv1_nmid (h ▸ hw2_ymid)
  have hw2_ne_v2 : w2 ≠ v2 := fun h => hv2_nmid (h ▸ hw2_ymid)
  -- D ∩ Q = {w1, w2}
  have hDQ : D ∩ Q = {w1, w2} := by
    rw [← hAB_union]
    ext x; simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxD, hxAB⟩
      have hxSeg : x ∈ Seg := hDsub hxD
      rcases hxAB with hxA | hxB
      · have : x ∈ D ∩ (A ∩ Seg) := ⟨hxD, hxA, hxSeg⟩
        rw [hDASeg] at this; left; exact mem_singleton_iff.mp this
      · have : x ∈ D ∩ (B ∩ Seg) := ⟨hxD, hxB, hxSeg⟩
        rw [hDBSeg] at this; right; exact mem_singleton_iff.mp this
    · rintro (rfl | rfl)
      · exact ⟨hw1D, Or.inl hw1A⟩
      · exact ⟨hw2D, Or.inr hw2B⟩
  -- Final assembly
  exact ⟨A, B, D, w1, w2, hA_arc, hB_arc, hAB_union, hAB_inter,
    hw1_ne_v1, hw1_ne_v2, hw2_ne_v1, hw2_ne_v2,
    hw1A, hw2B, hD_arc, hDQ,
    fun x hxD => hSeg_bounds x (hDsub hxD)⟩

/-! ## Part 6: One-sided definition and mk_E -/

/-- HOL Light: `one_sided_jordan_curve` (line 57231).
A simple closed curve is one-sided if any two points outside it
can be connected by an arc avoiding it. -/
def OneSidedJordanCurve (Q : Set E2') : Prop :=
  ∀ v w : E2', v ∉ Q → w ∉ Q → v ≠ w →
    ∃ C : Set E2', IsSimpleArcEnd C v w ∧ C ∩ Q = ∅

/-- HOL Light: `simple_closed_curve_mk_E` (line 57237).
Given arcs C and D disjoint from each other, both not subsets of Q,
and Q is one-sided, construct arc E with specific intersection properties. -/
theorem isSimpleClosedCurve_mk_E {Q C D : Set E2'}
    (_hQ : IsSimpleClosedCurve Q) (hOS : OneSidedJordanCurve Q)
    (hCnQ : ¬(C ⊆ Q)) (hDnQ : ¬(D ⊆ Q))
    (hCa : IsSimpleArc C) (hDa : IsSimpleArc D)
    (hCD : C ∩ D = ∅) :
    ∃ E x1 x2, IsSimpleArcEnd E x1 x2 ∧
      E ∩ C = {x2} ∧ E ∩ D = {x1} ∧ E ∩ Q = ∅ := by
  -- Get c ∈ C \ Q and d ∈ D \ Q
  have ⟨c, hcC, hcQ⟩ : ∃ c ∈ C, c ∉ Q := by
    by_contra h; push Not at h; exact hCnQ h
  have ⟨d, hdD, hdQ⟩ : ∃ d ∈ D, d ∉ Q := by
    by_contra h; push Not at h; exact hDnQ h
  -- c ≠ d (since c ∈ C, d ∈ D, and C ∩ D = ∅)
  have hcd : c ≠ d := by
    intro heq; have : c ∈ C ∩ D := ⟨hcC, heq ▸ hdD⟩; rw [hCD] at this; exact this
  -- By one-sidedness, get arc C' from c to d avoiding Q
  obtain ⟨C', hC'arc, hC'Q⟩ := hOS c d hcQ hdQ hcd
  -- Apply isSimpleArcEnd_restriction to C' with K = C, K' = D
  have hdisj : C' ∩ C ∩ D = ∅ := by rw [Set.inter_assoc, hCD, Set.inter_empty]
  have hC'C : (C' ∩ C).Nonempty := ⟨c, isSimpleArcEnd_mem_left hC'arc, hcC⟩
  have hC'D : (C' ∩ D).Nonempty := ⟨d, isSimpleArcEnd_mem_right hC'arc, hdD⟩
  obtain ⟨E, v, v', hEsub, hEarc, hEC, hED⟩ :=
    isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc hC'arc)
      (isSimpleArc_compact hCa).isClosed (isSimpleArc_compact hDa).isClosed
      hdisj hC'C hC'D
  -- E ∩ Q = ∅ (since E ⊆ C' and C' ∩ Q = ∅)
  have hEQ : E ∩ Q = ∅ := by
    have h : E ∩ Q ⊆ C' ∩ Q := Set.inter_subset_inter_left Q hEsub
    rw [hC'Q] at h; exact Set.subset_empty_iff.mp h
  -- x2 = v (in C), x1 = v' (in D), need IsSimpleArcEnd E v' v
  exact ⟨E, v', v, isSimpleArcEnd_symm hEarc, hEC, hED, hEQ⟩

/-! ## Part 7: K₃,₃ data structure -/

/-- HOL Light: `jordan_curve_k33_data` (line 57314).
The K₃,₃ data for a one-sided simple closed curve. -/
structure JordanCurveK33Data (Q : Set E2') where
  A : Set E2'
  B : Set E2'
  C : Set E2'
  D : Set E2'
  E : Set E2'
  v1 : E2'
  v2 : E2'
  w1 : E2'
  w2 : E2'
  x1 : E2'
  x2 : E2'
  hQ : IsSimpleClosedCurve Q
  hA : IsSimpleArcEnd A v1 v2
  hB : IsSimpleArcEnd B v1 v2
  hC_arc : IsSimpleArcEnd C v1 v2
  hD : IsSimpleArcEnd D w1 w2
  hE : IsSimpleArcEnd E x1 x2
  hw1_ne_v1 : w1 ≠ v1
  hw1_ne_v2 : w1 ≠ v2
  hw2_ne_v1 : w2 ≠ v1
  hw2_ne_v2 : w2 ≠ v2
  hAw1 : w1 ∈ A
  hBw2 : w2 ∈ B
  hAB : A ∪ B = Q
  hABinter : A ∩ B = {v1, v2}
  hDQ : D ∩ Q = {w1, w2}
  hCD : C ∩ D = ∅
  hCQ : C ∩ Q = {v1, v2}
  hEC : E ∩ C = {x2}
  hED : E ∩ D = {x1}
  hEQ : E ∩ Q = ∅

/-- HOL Light: `jordan_curve_k33_data_exist` (line 57338). -/
theorem jordanCurveK33Data_exists {Q : Set E2'}
    (hQ : IsSimpleClosedCurve Q) (hOS : OneSidedJordanCurve Q) :
    Nonempty (JordanCurveK33Data Q) := by
  -- Step 1: Construct arc C
  obtain ⟨C, v1, v2, hCend, hCQ, hv2_ymin, hv1_ymax, hCprop⟩ :=
    isSimpleClosedCurve_mk_C hQ
  have hv1Q : v1 ∈ Q := by
    have : v1 ∈ C ∩ Q := by rw [hCQ]; exact mem_insert _ _
    exact this.2
  have hv2Q : v2 ∈ Q := by
    have : v2 ∈ C ∩ Q := by rw [hCQ]; exact mem_insert_of_mem _ (mem_singleton _)
    exact this.2
  -- Step 2: Construct arcs A, B and horizontal arc D
  obtain ⟨A, B, D, w1, w2, hAend, hBend, hAB, hABint,
    hw1v1, hw1v2, hw2v1, hw2v2, hAw1, hBw2, hDend, hDQ, hDprop⟩ :=
    isSimpleClosedCurve_mk_ABD hQ hv1Q hv2Q hv2_ymin hv1_ymax
  -- Step 3: Show C ∩ D = ∅ (C at extremal heights or right of Q, D strictly between)
  have hCD : C ∩ D = ∅ := by
    ext x; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxC hxD
    obtain hh1 | hh1 | hh1 := hCprop x hxC <;> obtain ⟨hD1, hD2, hD3⟩ := hDprop x hxD
    · linarith
    · linarith
    · linarith
  -- Step 4: C and D are not subsets of Q (both are infinite arcs with finite Q-intersection)
  have hCnQ : ¬(C ⊆ Q) := by
    intro h
    have hCeq := (Set.inter_eq_left.mpr h).symm.trans hCQ
    have := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc hCend)
    rw [hCeq] at this
    exact this ((Set.finite_singleton v2).insert v1)
  have hDnQ : ¬(D ⊆ Q) := by
    intro h
    have hDeq := (Set.inter_eq_left.mpr h).symm.trans hDQ
    have := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc hDend)
    rw [hDeq] at this
    exact this ((Set.finite_singleton w2).insert w1)
  -- Step 5: Construct arc E via one-sidedness
  obtain ⟨E, x1, x2, hEend, hEC, hED, hEQ⟩ :=
    isSimpleClosedCurve_mk_E hQ hOS hCnQ hDnQ
      (isSimpleArcEnd_isSimpleArc hCend) (isSimpleArcEnd_isSimpleArc hDend) hCD
  -- Assemble the K33 data structure
  exact ⟨{
    A := A, B := B, C := C, D := D, E := E,
    v1 := v1, v2 := v2, w1 := w1, w2 := w2, x1 := x1, x2 := x2,
    hQ := hQ, hA := hAend, hB := hBend, hC_arc := hCend,
    hD := hDend, hE := hEend,
    hw1_ne_v1 := hw1v1, hw1_ne_v2 := hw1v2,
    hw2_ne_v1 := hw2v1, hw2_ne_v2 := hw2v2,
    hAw1 := hAw1, hBw2 := hBw2,
    hAB := hAB, hABinter := hABint,
    hDQ := hDQ, hCD := hCD,
    hCQ := hCQ, hEC := hEC, hED := hED, hEQ := hEQ
  }⟩

/-! ## Part 8: Membership lemmas -/

/-- HOL Light: `jordan_curve_x` (line 57415). -/
theorem JordanCurveK33Data.x_mem {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.x1 ∉ Q ∧ d.x2 ∉ Q ∧ d.x1 ∉ d.A ∧ d.x2 ∉ d.A ∧
    d.x1 ∉ d.B ∧ d.x2 ∉ d.B ∧
    d.x1 ∉ d.C ∧ d.x2 ∈ d.C ∧ d.x1 ∈ d.D ∧ d.x2 ∉ d.D ∧
    d.x1 ∈ d.E ∧ d.x2 ∈ d.E := by
  have hx1E := isSimpleArcEnd_mem_left d.hE
  have hx2E := isSimpleArcEnd_mem_right d.hE
  have hx12 := isSimpleArcEnd_distinct d.hE
  have hx1Q : d.x1 ∉ Q := by
    intro h; have := d.hEQ ▸ show d.x1 ∈ d.E ∩ Q from ⟨hx1E, h⟩; exact this
  have hx2Q : d.x2 ∉ Q := by
    intro h; have := d.hEQ ▸ show d.x2 ∈ d.E ∩ Q from ⟨hx2E, h⟩; exact this
  have hAsub : d.A ⊆ Q :=
    fun x hx => d.hAB ▸ mem_union_left _ hx
  have hBsub : d.B ⊆ Q :=
    fun x hx => d.hAB ▸ mem_union_right _ hx
  have hx2C : d.x2 ∈ d.C := by
    have : d.x2 ∈ d.E ∩ d.C := by rw [d.hEC]; exact mem_singleton _
    exact this.2
  have hx1C : d.x1 ∉ d.C := fun h => by
    have hmem : d.x1 ∈ d.E ∩ d.C := ⟨hx1E, h⟩
    rw [d.hEC] at hmem; exact hx12 (mem_singleton_iff.mp hmem)
  have hx1D : d.x1 ∈ d.D := by
    have : d.x1 ∈ d.E ∩ d.D := by rw [d.hED]; exact mem_singleton _
    exact this.2
  have hx2D : d.x2 ∉ d.D := fun h => by
    have hmem : d.x2 ∈ d.E ∩ d.D := ⟨hx2E, h⟩
    rw [d.hED] at hmem; exact hx12.symm (mem_singleton_iff.mp hmem)
  exact ⟨hx1Q, hx2Q, fun h => hx1Q (hAsub h), fun h => hx2Q (hAsub h),
    fun h => hx1Q (hBsub h), fun h => hx2Q (hBsub h),
    hx1C, hx2C, hx1D, hx2D, hx1E, hx2E⟩

private lemma not_mem_of_inter_pair {S T : Set E2'} {x a b : E2'}
    (hST : S ∩ T = {a, b}) (hxST : x ∈ S ∩ T)
    (hxa : x ≠ a) (hxb : x ≠ b) : False := by
  rw [hST] at hxST
  simp only [mem_insert_iff, mem_singleton_iff] at hxST
  exact hxST.elim (fun h => hxa h) (fun h => hxb h)

/-- HOL Light: `jordan_curve_v` (line 57455). -/
theorem JordanCurveK33Data.v_mem {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.v1 ∈ Q ∧ d.v2 ∈ Q ∧ d.v1 ∈ d.A ∧ d.v2 ∈ d.A ∧
    d.v1 ∈ d.B ∧ d.v2 ∈ d.B ∧ d.v1 ∈ d.C ∧ d.v2 ∈ d.C ∧
    d.v1 ∉ d.D ∧ d.v2 ∉ d.D ∧ d.v1 ∉ d.E ∧ d.v2 ∉ d.E := by
  have hv1A := isSimpleArcEnd_mem_left d.hA
  have hv2A := isSimpleArcEnd_mem_right d.hA
  have hv1B := isSimpleArcEnd_mem_left d.hB
  have hv2B := isSimpleArcEnd_mem_right d.hB
  have hv1C := isSimpleArcEnd_mem_left d.hC_arc
  have hv2C := isSimpleArcEnd_mem_right d.hC_arc
  have hv1Q : d.v1 ∈ Q := by have := d.hAB ▸ show d.v1 ∈ d.A ∪ d.B from Or.inl hv1A; exact this
  have hv2Q : d.v2 ∈ Q := by have := d.hAB ▸ show d.v2 ∈ d.A ∪ d.B from Or.inl hv2A; exact this
  have hv1D : d.v1 ∉ d.D := fun h =>
    not_mem_of_inter_pair d.hDQ ⟨h, hv1Q⟩ d.hw1_ne_v1.symm d.hw2_ne_v1.symm
  have hv2D : d.v2 ∉ d.D := fun h =>
    not_mem_of_inter_pair d.hDQ ⟨h, hv2Q⟩ d.hw1_ne_v2.symm d.hw2_ne_v2.symm
  have hv1E : d.v1 ∉ d.E := by
    intro h; have := d.hEQ ▸ show d.v1 ∈ d.E ∩ Q from ⟨h, hv1Q⟩; exact this
  have hv2E : d.v2 ∉ d.E := by
    intro h; have := d.hEQ ▸ show d.v2 ∈ d.E ∩ Q from ⟨h, hv2Q⟩; exact this
  exact ⟨hv1Q, hv2Q, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, hv1D, hv2D, hv1E, hv2E⟩

/-- HOL Light: `jordan_curve_w` (line 57489). -/
theorem JordanCurveK33Data.w_mem {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.w1 ∈ Q ∧ d.w2 ∈ Q ∧ d.w1 ∈ d.A ∧ d.w2 ∉ d.A ∧
    d.w1 ∉ d.B ∧ d.w2 ∈ d.B ∧ d.w1 ∉ d.C ∧ d.w2 ∉ d.C ∧
    d.w1 ∈ d.D ∧ d.w2 ∈ d.D ∧ d.w1 ∉ d.E ∧ d.w2 ∉ d.E := by
  have hw1D := isSimpleArcEnd_mem_left d.hD
  have hw2D := isSimpleArcEnd_mem_right d.hD
  have hw1Q : d.w1 ∈ Q := by have := d.hAB ▸ show d.w1 ∈ d.A ∪ d.B from Or.inl d.hAw1; exact this
  have hw2Q : d.w2 ∈ Q := by have := d.hAB ▸ show d.w2 ∈ d.A ∪ d.B from Or.inr d.hBw2; exact this
  have hw2A : d.w2 ∉ d.A := fun h =>
    not_mem_of_inter_pair d.hABinter ⟨h, d.hBw2⟩ d.hw2_ne_v1 d.hw2_ne_v2
  have hw1B : d.w1 ∉ d.B := fun h =>
    not_mem_of_inter_pair d.hABinter ⟨d.hAw1, h⟩ d.hw1_ne_v1 d.hw1_ne_v2
  have hw1C : d.w1 ∉ d.C := fun h =>
    not_mem_of_inter_pair d.hCQ ⟨h, hw1Q⟩ d.hw1_ne_v1 d.hw1_ne_v2
  have hw2C : d.w2 ∉ d.C := fun h =>
    not_mem_of_inter_pair d.hCQ ⟨h, hw2Q⟩ d.hw2_ne_v1 d.hw2_ne_v2
  have hw1E : d.w1 ∉ d.E := by
    intro h; have := d.hEQ ▸ show d.w1 ∈ d.E ∩ Q from ⟨h, hw1Q⟩; exact this
  have hw2E : d.w2 ∉ d.E := by
    intro h; have := d.hEQ ▸ show d.w2 ∈ d.E ∩ Q from ⟨h, hw2Q⟩; exact this
  exact ⟨hw1Q, hw2Q, d.hAw1, hw2A, hw1B, d.hBw2, hw1C, hw2C, hw1D, hw2D, hw1E, hw2E⟩

/-! ## Part 9: Size and disjointness -/

/-- HOL Light: `jordan_curve_AP_size3` (line 57527).
The three A-partition vertices are distinct. -/
theorem JordanCurveK33Data.AP_card3 {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.w1 ≠ d.w2 ∧ d.x2 ≠ d.w1 ∧ d.x2 ≠ d.w2 := by
  have hx := d.x_mem; have hw := d.w_mem
  exact ⟨(isSimpleArcEnd_distinct d.hD),
    fun h => hx.2.1 (h ▸ hw.1), fun h => hx.2.1 (h ▸ hw.2.1)⟩

/-- HOL Light: `jordan_curve_BP_size3` (line 57557).
The three B-partition vertices are distinct. -/
theorem JordanCurveK33Data.BP_card3 {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.v1 ≠ d.v2 ∧ d.x1 ≠ d.v1 ∧ d.x1 ≠ d.v2 := by
  have hx := d.x_mem; have hv := d.v_mem
  exact ⟨(isSimpleArcEnd_distinct d.hA),
    fun h => hx.1 (h ▸ hv.1), fun h => hx.1 (h ▸ hv.2.1)⟩

/-- HOL Light: `jordan_curve_AP_BP_empty` (line 57582).
The two vertex sets are disjoint. -/
theorem JordanCurveK33Data.AP_BP_disjoint {Q : Set E2'} (d : JordanCurveK33Data Q) :
    ({d.w1, d.w2, d.x2} : Set E2') ∩ {d.v1, d.v2, d.x1} = ∅ := by
  have hx := d.x_mem; have hv := d.v_mem; have hw := d.w_mem
  ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_empty_iff_false,
    iff_false, not_and]
  rintro (h1 | h1 | h1) <;> subst h1 <;>
    rintro (h2 | h2 | h2)
  · exact d.hw1_ne_v1 h2
  · exact d.hw1_ne_v2 h2
  · exact hx.1 (h2 ▸ hw.1)
  · exact d.hw2_ne_v1 h2
  · exact d.hw2_ne_v2 h2
  · exact hx.1 (h2 ▸ hw.2.1)
  · exact hx.2.1 (h2 ▸ hv.1)
  · exact hx.2.1 (h2 ▸ hv.2.1)
  · have : d.x2 ∈ d.E ∩ d.D := by
      rw [d.hED]; rw [← h2]; exact mem_singleton _
    exact (isSimpleArcEnd_distinct d.hE) (mem_singleton_iff.mp (by
      rw [← d.hED]; exact this)).symm

/-! ## Part 10: Utility lemmas -/

/-- HOL Light: `has_size_le9` (line 57634).
A set of at most 9 named elements has cardinality ≤ 9. -/
theorem card_le_9_of_insert {x1 x2 x3 x4 x5 x6 x7 x8 x9 : E2'} :
    ({x1, x2, x3, x4, x5, x6, x7, x8, x9} : Set E2').ncard ≤ 9 := by
  have h8 := Set.ncard_insert_le x1 {x2, x3, x4, x5, x6, x7, x8, x9}
  have h7 := Set.ncard_insert_le x2 {x3, x4, x5, x6, x7, x8, x9}
  have h6 := Set.ncard_insert_le x3 {x4, x5, x6, x7, x8, x9}
  have h5 := Set.ncard_insert_le x4 {x5, x6, x7, x8, x9}
  have h4 := Set.ncard_insert_le x5 {x6, x7, x8, x9}
  have h3 := Set.ncard_insert_le x6 {x7, x8, x9}
  have h2 := Set.ncard_insert_le x7 {x8, x9}
  have h1 := Set.ncard_insert_le x8 {x9}
  have h0 := Set.ncard_singleton x9
  omega

/-- HOL Light: `card_surj_bij` (line 57670).
A surjection from a finite set to a set of at most the same cardinality
is a bijection. -/
theorem card_surj_bij {α β : Type*} {f : α → β} {X : Set α} {Y : Set β}
    (hfin : X.Finite) (hcard : X.ncard ≤ Y.ncard)
    (hsurj : ∀ y ∈ Y, ∃ x ∈ X, f x = y) :
    Set.BijOn f X Y := by
  have hSurj : Set.SurjOn f X Y := hsurj
  have hfin_img := hfin.image f
  have himg_eq : f '' X = Y :=
    (Set.eq_of_subset_of_ncard_le hSurj
      ((Set.ncard_image_le hfin).trans hcard) hfin_img).symm
  refine ⟨fun x hx => himg_eq ▸ Set.mem_image_of_mem f hx, ?_, hSurj⟩
  -- Show InjOn f X by contradiction
  intro x₁ hx₁ x₂ hx₂ hfx
  by_contra hne
  have hx₂_diff : x₂ ∈ X \ {x₁} := by
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨hx₂, fun h => hne h.symm⟩
  have himg_eq2 : f '' X = f '' (X \ {x₁}) := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hzx : z = x₁
      · exact ⟨x₂, hx₂_diff, by rw [← hfx, ← hzx]⟩
      · exact Set.mem_image_of_mem f
          (Set.mem_diff_singleton.mpr ⟨hz, hzx⟩)
    · exact Set.image_mono Set.diff_subset
  have h1 : Y.ncard ≤ (X \ {x₁}).ncard := by
    rw [← himg_eq, himg_eq2]
    exact Set.ncard_image_le (hfin.subset Set.diff_subset)
  have h2 : (X \ {x₁}).ncard < X.ncard := by
    apply Set.ncard_lt_ncard _ hfin
    refine ⟨Set.diff_subset, fun h => ?_⟩
    have := h hx₁; simp at this
  omega

/-- HOL Light: `cut_arc_simple2` (line 57935).
Cutting a simple arc at two of its points gives a simple arc. -/
theorem cutArc_isSimpleArc {C : Set E2'} {v w : E2'}
    (hC : IsSimpleArc C) (hv : v ∈ C) (hw : w ∈ C) (hvw : v ≠ w) :
    IsSimpleArc (cutArc C v w) :=
  isSimpleArcEnd_isSimpleArc (cutArc_isSimpleArcEnd hC hv hw hvw)

/-! ## Part 11: k33f / incf definitions and lemmas -/

/-- HOL Light: `select_inter` (line 57726).
Select the unique element in A ∩ C. -/
def selectInter (A C : Set E2') : E2' :=
  Classical.epsilon (fun x => x ∈ A ∧ x ∈ C)

/-- HOL Light: `k33f` (line 57728).
Maps an edge to its (AP-vertex, BP-vertex) pair. -/
def k33f' (AP BP : Set E2') (e : Set E2') : E2' × E2' :=
  (selectInter AP e, selectInter BP e)

/-- HOL Light: `incf` (line 57730).
Converts a pair-valued function into a set-valued incidence function. -/
def incf (f : Set E2' → E2' × E2') (e : Set E2') : Set E2' :=
  {(f e).1, (f e).2}

/-- HOL Light: `k33f_value` (line 57733). -/
theorem k33f_value {AP BP e : Set E2'} {a b : E2'}
    (hA : AP ∩ e = {a}) (hB : BP ∩ e = {b}) :
    k33f' AP BP e = (a, b) := by
  simp only [k33f', selectInter, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · have ha : a ∈ AP ∧ a ∈ e := by rw [← mem_inter_iff]; rw [hA]; exact mem_singleton a
    have heps := Classical.epsilon_spec (p := fun x => x ∈ AP ∧ x ∈ e) ⟨a, ha⟩
    exact mem_singleton_iff.mp (hA ▸ mem_inter heps.1 heps.2)
  · have hb : b ∈ BP ∧ b ∈ e := by rw [← mem_inter_iff]; rw [hB]; exact mem_singleton b
    have heps := Classical.epsilon_spec (p := fun x => x ∈ BP ∧ x ∈ e) ⟨b, hb⟩
    exact mem_singleton_iff.mp (hB ▸ mem_inter heps.1 heps.2)

/-- HOL Light: `incf_value` (line 57752). -/
theorem incf_value {AP BP e : Set E2'} {a b : E2'}
    (hA : AP ∩ e = {a}) (hB : BP ∩ e = {b}) :
    incf (k33f' AP BP) e = {a, b} := by
  unfold incf; rw [k33f_value hA hB]

/-- HOL Light: `incf_V` (line 57764). -/
theorem incf_V {AP BP e : Set E2'}
    (hA : (AP ∩ e).ncard = 1) (hB : (BP ∩ e).ncard = 1) :
    incf (k33f' AP BP) e = e ∩ (AP ∪ BP) := by
  rw [Set.ncard_eq_one] at hA hB
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  rw [incf_value ha hb, inter_union_distrib_left, ← inter_comm AP e, ha,
    ← inter_comm BP e, hb, singleton_union]

/-- HOL Light: `k33f_E` (line 57784). -/
theorem k33f_E {Q : Set E2'} (d : JordanCurveK33Data Q) :
    ({d.w1, d.w2, d.x2} : Set E2') ∩ d.E = {d.x2} ∧
    ({d.v1, d.v2, d.x1} : Set E2') ∩ d.E = {d.x1} := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx1E, hx2E⟩ := d.x_mem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hv1E, hv2E⟩ := d.v_mem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hw1E, hw2E⟩ := d.w_mem
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨h1 | h1 | h1, h2⟩
      · subst h1; exact absurd h2 hw1E
      · subst h1; exact absurd h2 hw2E
      · exact h1
    · rintro h; subst h; exact ⟨Or.inr (Or.inr rfl), hx2E⟩
  · ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨h1 | h1 | h1, h2⟩
      · subst h1; exact absurd h2 hv1E
      · subst h1; exact absurd h2 hv2E
      · exact h1
    · rintro h; subst h; exact ⟨Or.inr (Or.inr rfl), hx1E⟩

/-- HOL Light: `k33f_cut_lemma` (line 57808) + `k33f_cut` (line 57870) combined.
Intersection properties of cut arcs with the two vertex sets. -/
theorem k33f_cut {C : Set E2'} {v1 v2 w : E2'} {AP BP : Set E2'}
    (hC : IsSimpleArcEnd C v1 v2)
    (hw : w ∈ C) (hw1 : w ≠ v1) (hw2 : w ≠ v2)
    (hAP : AP ∩ C = {v1, v2})
    (hBP : BP ∩ C = {w}) :
    AP ∩ cutArc C v1 w = {v1} ∧
    BP ∩ cutArc C v1 w = {w} ∧
    AP ∩ cutArc C v2 w = {v2} ∧
    BP ∩ cutArc C v2 w = {w} := by
  have hCa := isSimpleArcEnd_isSimpleArc hC
  have hv1 := isSimpleArcEnd_mem_left hC
  have hv2 := isSimpleArcEnd_mem_right hC
  have hCA1 := cutArc_isSimpleArcEnd hCa hv1 hw hw1.symm
  have hCA2e := cutArc_isSimpleArcEnd hCa hv2 hw hw2.symm
  have hCA1s := cutArc_subset hCa hv1 hw hw1.symm
  have hCA2s := cutArc_subset hCa hv2 hw hw2.symm
  -- cutArc_inter gives us the key decomposition
  obtain ⟨hinter, hunion⟩ := cutArc_inter hC hw hw1 hw2
  rw [cutArc_symm C w v2] at hinter hunion
  -- v2 ∉ cutArc C v1 w (because if it were, v2 ∈ inter = {w}, so v2 = w)
  have hv2_not : v2 ∉ cutArc C v1 w := by
    intro h
    have hmem : v2 ∈ cutArc C v1 w ∩ cutArc C v2 w :=
      ⟨h, isSimpleArcEnd_mem_left hCA2e⟩
    rw [hinter] at hmem
    exact hw2 (mem_singleton_iff.mp hmem).symm
  -- v1 ∉ cutArc C v2 w
  have hv1_not : v1 ∉ cutArc C v2 w := by
    intro h
    have hmem : v1 ∈ cutArc C v1 w ∩ cutArc C v2 w :=
      ⟨isSimpleArcEnd_mem_left hCA1, h⟩
    rw [hinter] at hmem
    exact hw1 (mem_singleton_iff.mp hmem).symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;>
    simp only [mem_inter_iff, mem_singleton_iff] <;> constructor
  -- AP ∩ cutArc C v1 w = {v1}
  · rintro ⟨hxAP, hxC1⟩
    have hxC : x ∈ C := hCA1s hxC1
    have : x ∈ ({v1, v2} : Set E2') := by rw [← hAP]; exact ⟨hxAP, hxC⟩
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxC1) hv2_not
  · intro h; rw [h]
    exact ⟨(show v1 ∈ AP ∩ C by rw [hAP]; exact mem_insert _ _).1,
           isSimpleArcEnd_mem_left hCA1⟩
  -- BP ∩ cutArc C v1 w = {w}
  · rintro ⟨hxBP, hxC1⟩
    have hxC : x ∈ C := hCA1s hxC1
    have : x ∈ ({w} : Set E2') := by rw [← hBP]; exact ⟨hxBP, hxC⟩
    exact mem_singleton_iff.mp this
  · intro h; rw [h]
    exact ⟨(show w ∈ BP ∩ C by rw [hBP]; exact mem_singleton _).1,
           isSimpleArcEnd_mem_right hCA1⟩
  -- AP ∩ cutArc C v2 w = {v2}
  · rintro ⟨hxAP, hxC2⟩
    have hxC : x ∈ C := hCA2s hxC2
    have : x ∈ ({v1, v2} : Set E2') := by rw [← hAP]; exact ⟨hxAP, hxC⟩
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with h1 | h1
    · exact absurd (h1 ▸ hxC2) hv1_not
    · exact h1
  · intro h; rw [h]
    exact ⟨(show v2 ∈ AP ∩ C by rw [hAP]; exact mem_insert_of_mem _ (mem_singleton _)).1,
           isSimpleArcEnd_mem_left hCA2e⟩
  -- BP ∩ cutArc C v2 w = {w}
  · rintro ⟨hxBP, hxC2⟩
    have hxC : x ∈ C := hCA2s hxC2
    have : x ∈ ({w} : Set E2') := by rw [← hBP]; exact ⟨hxBP, hxC⟩
    exact mem_singleton_iff.mp this
  · intro h; rw [h]
    exact ⟨(show w ∈ BP ∩ C by rw [hBP]; exact mem_singleton _).1,
           isSimpleArcEnd_mem_right hCA2e⟩

/-! ## Part 12: K₃,₃ graph construction -/

/-- Helper: if AP and BP each intersect e and are disjoint, the incidence function
gives a 2-element subset of AP ∪ BP. -/
private lemma well_formed_edge {AP BP e : Set E2'}
    (h1 : ∃ x, x ∈ AP ∧ x ∈ e) (h2 : ∃ y, y ∈ BP ∧ y ∈ e)
    (hdisj : AP ∩ BP = ∅) :
    {(k33f' AP BP e).1, (k33f' AP BP e).2} ⊆ AP ∪ BP ∧
    ({(k33f' AP BP e).1, (k33f' AP BP e).2} : Set E2').ncard = 2 := by
  unfold k33f' selectInter
  set a := Classical.epsilon (fun x => x ∈ AP ∧ x ∈ e)
  set b := Classical.epsilon (fun x => x ∈ BP ∧ x ∈ e)
  have ha := Classical.epsilon_spec h1
  have hb := Classical.epsilon_spec h2
  refine ⟨?_, Set.ncard_eq_two.mpr ⟨a, b, ?_, rfl⟩⟩
  · rintro x (rfl | rfl)
    · exact mem_union_left _ ha.1
    · exact mem_union_right _ hb.1
  · intro heq
    have : a ∈ AP ∩ BP := ⟨ha.1, heq ▸ hb.1⟩
    rw [hdisj] at this; exact this

/-- Helper: if inc = e ∩ vertexSet and e is a SimpleArcEnd with endpoints in vertexSet,
then the edge satisfies the arc condition of IsPlaneGraph. -/
private lemma edge_is_arc {G : HolGraph E2' (Set E2')} {e : Set E2'} {v w : E2'}
    (hinc : G.inc e = e ∩ G.vertexSet)
    (harc : IsSimpleArcEnd e v w)
    (hv : v ∈ G.vertexSet) (hw : w ∈ G.vertexSet) :
    ∃ v' w', v' ∈ G.inc e ∧ w' ∈ G.inc e ∧ v' ≠ w' ∧ IsSimpleArcEnd e v' w' :=
  ⟨v, w,
    by rw [hinc]; exact ⟨isSimpleArcEnd_mem_left harc, hv⟩,
    by rw [hinc]; exact ⟨isSimpleArcEnd_mem_right harc, hw⟩,
    isSimpleArcEnd_distinct harc,
    harc⟩

/-- HOL Light: `jordan_curve_k33` (line 57895).
The K₃,₃ plane graph constructed from K₃,₃ data. -/
def jordanCurveK33 {Q : Set E2'} (d : JordanCurveK33Data Q) :
    HolGraph E2' (Set E2') where
  vertexSet := {d.w1, d.w2, d.x2} ∪ {d.v1, d.v2, d.x1}
  edgeSet := {d.E,
    cutArc d.A d.v1 d.w1, cutArc d.A d.v2 d.w1,
    cutArc d.B d.v1 d.w2, cutArc d.B d.v2 d.w2,
    cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2,
    cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1}
  inc := fun e => {(k33f' {d.w1, d.w2, d.x2} {d.v1, d.v2, d.x1} e).1,
                   (k33f' {d.w1, d.w2, d.x2} {d.v1, d.v2, d.x1} e).2}
  well_formed := by
    have hdisj := d.AP_BP_disjoint
    -- Membership facts from x_mem, v_mem, w_mem
    obtain ⟨hx1Q, hx2Q, _, _, _, _, _, hx2C, hx1D, _, hx1E, hx2E⟩ := d.x_mem
    obtain ⟨hv1Q, hv2Q, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, _, _, _, _⟩ := d.v_mem
    obtain ⟨hw1Q, hw2Q, _, _, _, _, _, _, hw1D, hw2D, _, _⟩ := d.w_mem
    -- Ne facts: x2 ∉ Q but v1,v2 ∈ Q, so x2 ≠ v1/v2. x1 ∉ Q but w1,w2 ∈ Q, so x1 ≠ w1/w2.
    have hx2v1 : d.x2 ≠ d.v1 := fun h => hx2Q (h ▸ hv1Q)
    have hx2v2 : d.x2 ≠ d.v2 := fun h => hx2Q (h ▸ hv2Q)
    have hx1w1 : d.x1 ≠ d.w1 := fun h => hx1Q (h ▸ hw1Q)
    have hx1w2 : d.x1 ≠ d.w2 := fun h => hx1Q (h ▸ hw2Q)
    -- Convenient abbreviation for cutArc_isSimpleArcEnd
    have hAsa := isSimpleArcEnd_isSimpleArc d.hA
    have hBsa := isSimpleArcEnd_isSimpleArc d.hB
    have hCsa := isSimpleArcEnd_isSimpleArc d.hC_arc
    have hDsa := isSimpleArcEnd_isSimpleArc d.hD
    -- 9-way case analysis
    intro e he
    simp only [mem_insert_iff, mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- Edge: E
    · exact well_formed_edge ⟨d.x2, by simp, hx2E⟩ ⟨d.x1, by simp, hx1E⟩ hdisj
    -- Edge: cutArc A v1 w1
    · have hca := cutArc_isSimpleArcEnd hAsa hv1A d.hAw1 d.hw1_ne_v1.symm
      exact well_formed_edge ⟨d.w1, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v1, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc A v2 w1
    · have hca := cutArc_isSimpleArcEnd hAsa hv2A d.hAw1 d.hw1_ne_v2.symm
      exact well_formed_edge ⟨d.w1, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v2, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc B v1 w2
    · have hca := cutArc_isSimpleArcEnd hBsa hv1B d.hBw2 d.hw2_ne_v1.symm
      exact well_formed_edge ⟨d.w2, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v1, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc B v2 w2
    · have hca := cutArc_isSimpleArcEnd hBsa hv2B d.hBw2 d.hw2_ne_v2.symm
      exact well_formed_edge ⟨d.w2, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v2, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc C v1 x2
    · have hca := cutArc_isSimpleArcEnd hCsa hv1C hx2C hx2v1.symm
      exact well_formed_edge ⟨d.x2, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v1, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc C v2 x2
    · have hca := cutArc_isSimpleArcEnd hCsa hv2C hx2C hx2v2.symm
      exact well_formed_edge ⟨d.x2, by simp, isSimpleArcEnd_mem_right hca⟩
        ⟨d.v2, by simp, isSimpleArcEnd_mem_left hca⟩ hdisj
    -- Edge: cutArc D w1 x1
    · have hca := cutArc_isSimpleArcEnd hDsa hw1D hx1D hx1w1.symm
      exact well_formed_edge ⟨d.w1, by simp, isSimpleArcEnd_mem_left hca⟩
        ⟨d.x1, by simp, isSimpleArcEnd_mem_right hca⟩ hdisj
    -- Edge: cutArc D w2 x1
    · have hca := cutArc_isSimpleArcEnd hDsa hw2D hx1D hx1w2.symm
      exact well_formed_edge ⟨d.w2, by simp, isSimpleArcEnd_mem_left hca⟩
        ⟨d.x1, by simp, isSimpleArcEnd_mem_right hca⟩ hdisj

/-- HOL Light: `jordan_curve_k33_plane_criterion` (line 57945).
The K₃,₃ graph satisfies the plane graph criterion. -/
theorem jordanCurveK33_planeCriterion {Q : Set E2'} (d : JordanCurveK33Data Q)
    (hG_graph : ∀ e ∈ (jordanCurveK33 d).edgeSet,
      (({d.w1, d.w2, d.x2} : Set E2') ∩ e).ncard = 1 ∧
      (({d.v1, d.v2, d.x1} : Set E2') ∩ e).ncard = 1)
    (hG_disjoint : ∀ e e', e ∈ (jordanCurveK33 d).edgeSet →
      e' ∈ (jordanCurveK33 d).edgeSet → e ≠ e' →
      e ∩ e' ⊆ (jordanCurveK33 d).vertexSet) :
    IsPlaneGraph (jordanCurveK33 d) := by
  -- Key fact: inc e = e ∩ vertexSet for all edges
  have hinc : ∀ e ∈ (jordanCurveK33 d).edgeSet,
      (jordanCurveK33 d).inc e = e ∩ (jordanCurveK33 d).vertexSet :=
    fun e he => incf_V (hG_graph e he).1 (hG_graph e he).2
  -- Membership/arc facts
  obtain ⟨_, _, _, _, _, _, _, hx2C, hx1D, _, hx1E, hx2E⟩ := d.x_mem
  obtain ⟨_, _, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, _, _, _, _⟩ := d.v_mem
  obtain ⟨_, _, _, _, _, _, _, _, hw1D, hw2D, _, _⟩ := d.w_mem
  have hx2v1 : d.x2 ≠ d.v1 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).1)
  have hx2v2 : d.x2 ≠ d.v2 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).2.1)
  have hx1w1 : d.x1 ≠ d.w1 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).1)
  have hx1w2 : d.x1 ≠ d.w2 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).2.1)
  have hAsa := isSimpleArcEnd_isSimpleArc d.hA
  have hBsa := isSimpleArcEnd_isSimpleArc d.hB
  have hCsa := isSimpleArcEnd_isSimpleArc d.hC_arc
  have hDsa := isSimpleArcEnd_isSimpleArc d.hD
  -- Vertex memberships in vertexSet
  have hv1V : d.v1 ∈ (jordanCurveK33 d).vertexSet := Or.inr (by simp)
  have hv2V : d.v2 ∈ (jordanCurveK33 d).vertexSet := Or.inr (by simp)
  have hw1V : d.w1 ∈ (jordanCurveK33 d).vertexSet := Or.inl (by simp)
  have hw2V : d.w2 ∈ (jordanCurveK33 d).vertexSet := Or.inl (by simp)
  have hx1V : d.x1 ∈ (jordanCurveK33 d).vertexSet := Or.inr (by simp)
  have hx2V : d.x2 ∈ (jordanCurveK33 d).vertexSet := Or.inl (by simp)
  refine ⟨?_, ?_, hG_disjoint⟩
  · -- edges_are_arcs
    intro e he
    have hinc_e := hinc e he
    simp only [jordanCurveK33, mem_insert_iff, mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact edge_is_arc hinc_e d.hE hx1V hx2V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hAsa hv1A d.hAw1 d.hw1_ne_v1.symm) hv1V hw1V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hAsa hv2A d.hAw1 d.hw1_ne_v2.symm) hv2V hw1V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hBsa hv1B d.hBw2 d.hw2_ne_v1.symm) hv1V hw2V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hBsa hv2B d.hBw2 d.hw2_ne_v2.symm) hv2V hw2V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hCsa hv1C hx2C hx2v1.symm) hv1V hx2V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hCsa hv2C hx2C hx2v2.symm) hv2V hx2V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hDsa hw1D hx1D hx1w1.symm) hw1V hx1V
    · exact edge_is_arc hinc_e
        (cutArc_isSimpleArcEnd hDsa hw2D hx1D hx1w2.symm) hw2V hx1V
  · -- vertex_on_edge
    intro e he v hv_vert hv_e
    rw [hinc e he]; exact ⟨hv_e, hv_vert⟩

end JordanCurveTheorem

end
