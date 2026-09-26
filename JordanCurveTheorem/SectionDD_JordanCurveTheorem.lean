/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionCC_OneSided

/-!
# Section DD: The Jordan Curve Theorem
## HOL Light: Section DD (Lines 58067–59200)

The final assembly: every simple closed curve in ℝ² separates the plane
into exactly two connected components, each open and connected, whose
common boundary is the curve.

### Key theorems
- `jordan_curve_not_one_sided` (~58672): No simple closed curve is one-sided
- **`JORDAN_CURVE_THEOREM`** (~58997): The main theorem
- `JORDAN_CURVE_DEFS` (~59116): Self-contained definitions (Not applicable to Lean)

### Proof Logic
1. Apply `jordan_curve_not_one_sided` → ∃ v, w in different components
2. Define A = component(v), B = component(w)
3. Verify: A, B are open, connected, nonempty, disjoint from C
4. A ∪ B ∪ C = ℝ²: by contradiction using `jordan_curve_no_inj3`
   (a third point x ∉ A ∪ B ∪ C would give 3 separated points)
-/

namespace JordanCurveTheorem

open Set Function EuclideanSpace

/-! ## §DD.1: K₃,₃ data: pairwise arc intersections -/

-- cartesian_size (line 58071): |A×B| = |A|·|B|
-- Mathlib: `Finset.card_product`

-- jordan_k33f_bij (line 58098): BIJ + SING properties
-- The BIJ part is already `k33f_E` from SectionCC.
-- The SING part (each edge meets AP/BP in exactly one element) is needed for
-- `jordanCurveK33_planeCriterion`. We prove it as `jordanCurveK33_sing`.

/-- HOL Light: `jordan_k33f_bij` (line 58098), SING part.
Each edge of the K₃,₃ graph meets AP in exactly one vertex and BP in exactly one vertex. -/
theorem jordanCurveK33_sing {Q : Set E2'} (d : JordanCurveK33Data Q)
    (e : Set E2') (he : e ∈ (jordanCurveK33 d).edgeSet) :
    (({d.w1, d.w2, d.x2} : Set E2') ∩ e).ncard = 1 ∧
    (({d.v1, d.v2, d.x1} : Set E2') ∩ e).ncard = 1 := by
  obtain ⟨_, _, hx1A, hx2A, hx1B, hx2B, hx1C, hx2C, hx1D, hx2D, _, _⟩ := d.x_mem
  obtain ⟨_, _, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, hv1D, hv2D, _, _⟩ := d.v_mem
  obtain ⟨_, _, _, hw2A, hw1B, _, hw1C, hw2C, hw1D, hw2D, _, _⟩ := d.w_mem
  set AP := ({d.w1, d.w2, d.x2} : Set E2')
  set BP := ({d.v1, d.v2, d.x1} : Set E2')
  -- Intersection facts for k33f_cut
  have hBP_A : BP ∩ d.A = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_A : AP ∩ d.A = {d.w1} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨Or.inl rfl, d.hAw1⟩
  have hBP_B : BP ∩ d.B = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_B : AP ∩ d.B = {d.w2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨by simp, d.hBw2⟩
  have hBP_C : BP ∩ d.C = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_C : AP ∩ d.C = {d.x2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨by simp, hx2C⟩
  have hAP_D : AP ∩ d.D = {d.w1, d.w2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hBP_D : BP ∩ d.D = {d.x1} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨by simp, hx1D⟩
  -- Apply k33f_cut for each arc
  have hx2v1 : d.x2 ≠ d.v1 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).1)
  have hx2v2 : d.x2 ≠ d.v2 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).2.1)
  have hx1w1 : d.x1 ≠ d.w1 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).1)
  have hx1w2 : d.x1 ≠ d.w2 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).2.1)
  obtain ⟨hA1bp, hA1ap, hA2bp, hA2ap⟩ :=
    k33f_cut d.hA d.hAw1 d.hw1_ne_v1 d.hw1_ne_v2 hBP_A hAP_A
  obtain ⟨hB1bp, hB1ap, hB2bp, hB2ap⟩ :=
    k33f_cut d.hB d.hBw2 d.hw2_ne_v1 d.hw2_ne_v2 hBP_B hAP_B
  obtain ⟨hC1bp, hC1ap, hC2bp, hC2ap⟩ :=
    k33f_cut d.hC_arc hx2C hx2v1 hx2v2 hBP_C hAP_C
  obtain ⟨hD1ap, hD1bp, hD2ap, hD2bp⟩ :=
    k33f_cut d.hD hx1D hx1w1 hx1w2 hAP_D hBP_D
  obtain ⟨hE_ap, hE_bp⟩ := k33f_E d
  -- 9-case analysis
  dsimp only [jordanCurveK33] at he
  simp only [mem_insert_iff, mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hE_ap ▸ ncard_singleton _, hE_bp ▸ ncard_singleton _⟩
  · exact ⟨hA1ap ▸ ncard_singleton _, hA1bp ▸ ncard_singleton _⟩
  · exact ⟨hA2ap ▸ ncard_singleton _, hA2bp ▸ ncard_singleton _⟩
  · exact ⟨hB1ap ▸ ncard_singleton _, hB1bp ▸ ncard_singleton _⟩
  · exact ⟨hB2ap ▸ ncard_singleton _, hB2bp ▸ ncard_singleton _⟩
  · exact ⟨hC1ap ▸ ncard_singleton _, hC1bp ▸ ncard_singleton _⟩
  · exact ⟨hC2ap ▸ ncard_singleton _, hC2bp ▸ ncard_singleton _⟩
  · exact ⟨hD1ap ▸ ncard_singleton _, hD1bp ▸ ncard_singleton _⟩
  · exact ⟨hD2ap ▸ ncard_singleton _, hD2bp ▸ ncard_singleton _⟩

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: verifying all 9 edge-image membership and distinctness conditions for
-- the K₃,₃ isomorphism involves `simp` on `Finset.card_insert_of_notMem` chains and multiple
-- `Set.disjoint_left` discharges over the full arc-intersection data.
/-- HOL Light: `jordan_curve_k33_isk33` (line 58220).
The K₃,₃ graph is isomorphic to K₃,₃. -/
theorem jordanCurveK33_isk33 {Q : Set E2'} (d : JordanCurveK33Data Q)
    (_hQ : OneSidedJordanCurve Q) :
    GraphIsomorphic K33 (jordanCurveK33 d) := by
  -- Membership facts
  obtain ⟨_, _, hx1A, hx2A, hx1B, hx2B, hx1C, hx2C, hx1D, hx2D, hx1E, hx2E⟩ := d.x_mem
  obtain ⟨_, _, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, hv1D, hv2D, _, _⟩ := d.v_mem
  obtain ⟨_, _, _, hw2A, hw1B, _, hw1C, hw2C, hw1D, hw2D, hw1E, hw2E⟩ := d.w_mem
  set AP := ({d.w1, d.w2, d.x2} : Set E2') with hAP_def
  set BP := ({d.v1, d.v2, d.x1} : Set E2') with hBP_def
  -- Vertex set distinctness
  obtain ⟨h_w12, h_x2w1, h_x2w2⟩ := d.AP_card3
  obtain ⟨h_v12, h_x1v1, h_x1v2⟩ := d.BP_card3
  -- Finset card = 3
  have hAcard : ({d.w1, d.w2, d.x2} : Finset E2').card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h_w12, h_x2w1.symm]),
        Finset.card_insert_of_notMem (by simp [h_x2w2.symm]),
        Finset.card_singleton]
  have hBcard : ({d.v1, d.v2, d.x1} : Finset E2').card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h_v12, h_x1v1.symm]),
        Finset.card_insert_of_notMem (by simp [h_x1v2.symm]),
        Finset.card_singleton]
  -- Disjointness
  have hdisj : Disjoint (({d.w1, d.w2, d.x2} : Finset E2') : Set E2')
      ({d.v1, d.v2, d.x1} : Finset E2') := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact Set.disjoint_iff_inter_eq_empty.mpr d.AP_BP_disjoint
  -- Full arc intersection facts for k33f_cut
  have hBP_A : BP ∩ d.A = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_A : AP ∩ d.A = {d.w1} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨Or.inl rfl, d.hAw1⟩
  have hBP_B : BP ∩ d.B = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_B : AP ∩ d.B = {d.w2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨Or.inr (Or.inl rfl), d.hBw2⟩
  have hBP_C : BP ∩ d.C = {d.v1, d.v2} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hAP_C : AP ∩ d.C = {d.x2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hx2C⟩
  have hAP_D : AP ∩ d.D = {d.w1, d.w2} := by
    ext x; simp only [AP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> exact ⟨by simp, ‹_›⟩
  have hBP_D : BP ∩ d.D = {d.x1} := by
    ext x; simp only [BP, mem_inter_iff, mem_insert_iff, mem_singleton_iff]; constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩ <;> simp_all
    · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hx1D⟩
  -- k33f_cut for arcs A, B, C, D
  have hA_cut := k33f_cut d.hA d.hAw1 d.hw1_ne_v1 d.hw1_ne_v2 hBP_A hAP_A
  have hB_cut := k33f_cut d.hB d.hBw2 d.hw2_ne_v1 d.hw2_ne_v2 hBP_B hAP_B
  have hx2_ne_v1 : d.x2 ≠ d.v1 := fun h => hx2A (h ▸ hv1A)
  have hx2_ne_v2 : d.x2 ≠ d.v2 := fun h => hx2A (h ▸ hv2A)
  have hC_cut := k33f_cut d.hC_arc hx2C hx2_ne_v1 hx2_ne_v2 hBP_C hAP_C
  have hx1_ne_w1 : d.x1 ≠ d.w1 := fun h => hx1A (h ▸ d.hAw1)
  have hx1_ne_w2 : d.x1 ≠ d.w2 := fun h => hx1B (h ▸ d.hBw2)
  have hD_cut := k33f_cut d.hD hx1D hx1_ne_w1 hx1_ne_w2 hAP_D hBP_D
  obtain ⟨hAP_E, hBP_E⟩ := k33f_E d
  -- BijOn via card_surj_bij (using Finset ncard)
  set EFS : Finset (Set E2') := {d.E, cutArc d.A d.v1 d.w1, cutArc d.A d.v2 d.w1,
    cutArc d.B d.v1 d.w2, cutArc d.B d.v2 d.w2,
    cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2,
    cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1}
  have hbij : BijOn (k33f' AP BP) (↑EFS : Set (Set E2'))
      ((({d.w1, d.w2, d.x2} : Finset E2') : Set E2') ×ˢ
       (({d.v1, d.v2, d.x1} : Finset E2') : Set E2')) := by
    rw [← Finset.coe_product]
    apply card_surj_bij EFS.finite_toSet
    · -- ncard inequality
      rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_product, hAcard, hBcard]
      have h1 : ({cutArc d.D d.w2 d.x1} : Finset (Set E2')).card = 1 :=
        Finset.card_singleton _
      have h2 := @Finset.card_insert_le (Set E2') _ (cutArc d.D d.w1 d.x1)
        ({cutArc d.D d.w2 d.x1} : Finset _)
      have h3 := @Finset.card_insert_le (Set E2') _ (cutArc d.C d.v2 d.x2)
        ({cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1} : Finset _)
      have h4 := @Finset.card_insert_le (Set E2') _ (cutArc d.C d.v1 d.x2)
        ({cutArc d.C d.v2 d.x2, cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1} : Finset _)
      have h5 := @Finset.card_insert_le (Set E2') _ (cutArc d.B d.v2 d.w2)
        ({cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2, cutArc d.D d.w1 d.x1,
          cutArc d.D d.w2 d.x1} : Finset _)
      have h6 := @Finset.card_insert_le (Set E2') _ (cutArc d.B d.v1 d.w2)
        ({cutArc d.B d.v2 d.w2, cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2,
          cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1} : Finset _)
      have h7 := @Finset.card_insert_le (Set E2') _ (cutArc d.A d.v2 d.w1)
        ({cutArc d.B d.v1 d.w2, cutArc d.B d.v2 d.w2, cutArc d.C d.v1 d.x2,
          cutArc d.C d.v2 d.x2, cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1} : Finset _)
      have h8 := @Finset.card_insert_le (Set E2') _ (cutArc d.A d.v1 d.w1)
        ({cutArc d.A d.v2 d.w1, cutArc d.B d.v1 d.w2, cutArc d.B d.v2 d.w2,
          cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2, cutArc d.D d.w1 d.x1,
          cutArc d.D d.w2 d.x1} : Finset _)
      have h9 := @Finset.card_insert_le (Set E2') _ d.E
        ({cutArc d.A d.v1 d.w1, cutArc d.A d.v2 d.w1, cutArc d.B d.v1 d.w2,
          cutArc d.B d.v2 d.w2, cutArc d.C d.v1 d.x2, cutArc d.C d.v2 d.x2,
          cutArc d.D d.w1 d.x1, cutArc d.D d.w2 d.x1} : Finset _)
      simp only [EFS] at *; omega
    · -- Surjectivity
      intro ⟨a, b⟩ hab
      rw [Finset.coe_product] at hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_prod,
        mem_insert_iff, mem_singleton_iff] at hab
      obtain ⟨ha, hb⟩ := hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      -- Helper: n × mem_insert_of_mem + target
      · -- (w1,v1) → cutArc A v1 w1 (pos 1)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
          k33f_value hA_cut.2.1 hA_cut.1⟩
      · -- (w1,v2) → cutArc A v2 w1 (pos 2)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))), k33f_value hA_cut.2.2.2 hA_cut.2.2.1⟩
      · -- (w1,x1) → cutArc D w1 x1 (pos 7)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _)))))))), k33f_value hD_cut.1 hD_cut.2.1⟩
      · -- (w2,v1) → cutArc B v1 w2 (pos 3)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))),
          k33f_value hB_cut.2.1 hB_cut.1⟩
      · -- (w2,v2) → cutArc B v2 w2 (pos 4)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))))), k33f_value hB_cut.2.2.2 hB_cut.2.2.1⟩
      · -- (w2,x1) → cutArc D w2 x1 (pos 8 = singleton)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))))))))), k33f_value hD_cut.2.2.1 hD_cut.2.2.2⟩
      · -- (x2,v1) → cutArc C v1 x2 (pos 5)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _)))))), k33f_value hC_cut.2.1 hC_cut.1⟩
      · -- (x2,v2) → cutArc C v2 x2 (pos 6)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))),
          k33f_value hC_cut.2.2.2 hC_cut.2.2.1⟩
      · -- (x2,x1) → E (pos 0)
        exact ⟨_, Finset.mem_coe.mpr (Finset.mem_insert_self _ _), k33f_value hAP_E hBP_E⟩
  -- Apply k33_iso and convert
  have hiso := k33_iso hAcard hBcard hdisj hbij
  convert hiso using 1
  simp only [jordanCurveK33, EFS, AP, BP, Finset.coe_insert, Finset.coe_singleton]

/-- HOL Light: `jordan_curve_k33_data_inter` (line 58257).
All 10 pairwise intersections of the five arcs A, B, C, D, E. -/
theorem jordanCurveK33Data_inter {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.A ∩ d.B = {d.v1, d.v2} ∧
    d.A ∩ d.C = {d.v1, d.v2} ∧
    d.A ∩ d.D = {d.w1} ∧
    d.A ∩ d.E = ∅ ∧
    d.B ∩ d.C = {d.v1, d.v2} ∧
    d.B ∩ d.D = {d.w2} ∧
    d.B ∩ d.E = ∅ ∧
    d.C ∩ d.D = ∅ ∧
    d.C ∩ d.E = {d.x2} ∧
    d.D ∩ d.E = {d.x1} := by
  have hAsub : d.A ⊆ Q := fun x hx => d.hAB ▸ mem_union_left _ hx
  have hBsub : d.B ⊆ Q := fun x hx => d.hAB ▸ mem_union_right _ hx
  have hv1A := isSimpleArcEnd_mem_left d.hA
  have hv2A := isSimpleArcEnd_mem_right d.hA
  have hv1B := isSimpleArcEnd_mem_left d.hB
  have hv2B := isSimpleArcEnd_mem_right d.hB
  have hv1C := isSimpleArcEnd_mem_left d.hC_arc
  have hv2C := isSimpleArcEnd_mem_right d.hC_arc
  have hw1D := isSimpleArcEnd_mem_left d.hD
  have hw2D := isSimpleArcEnd_mem_right d.hD
  -- A ∩ C = {v1, v2}: C ∩ A ⊆ C ∩ Q = {v1,v2}, and {v1,v2} ⊆ A ∩ C
  have hAC : d.A ∩ d.C = {d.v1, d.v2} := by
    ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro ⟨hxA, hxC⟩
      have : x ∈ d.C ∩ Q := ⟨hxC, hAsub hxA⟩; rw [d.hCQ] at this
      simpa using this
    · rintro (rfl | rfl) <;> exact ⟨‹_›, ‹_›⟩
  -- B ∩ C = {v1, v2}: similar
  have hBC : d.B ∩ d.C = {d.v1, d.v2} := by
    ext x; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro ⟨hxB, hxC⟩
      have : x ∈ d.C ∩ Q := ⟨hxC, hBsub hxB⟩; rw [d.hCQ] at this
      simpa using this
    · rintro (rfl | rfl) <;> exact ⟨‹_›, ‹_›⟩
  -- w2 ∉ A: if w2 ∈ A then w2 ∈ A ∩ B = {v1,v2}, contradicting hw2_ne_v1/v2
  have hw2A : d.w2 ∉ d.A := by
    intro h; have := d.hABinter ▸ show d.w2 ∈ d.A ∩ d.B from ⟨h, d.hBw2⟩
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with h1 | h1 <;> [exact d.hw2_ne_v1 h1; exact d.hw2_ne_v2 h1]
  -- w1 ∉ B: if w1 ∈ B then w1 ∈ A ∩ B = {v1,v2}
  have hw1B : d.w1 ∉ d.B := by
    intro h; have := d.hABinter ▸ show d.w1 ∈ d.A ∩ d.B from ⟨d.hAw1, h⟩
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with h1 | h1 <;> [exact d.hw1_ne_v1 h1; exact d.hw1_ne_v2 h1]
  -- A ∩ D = {w1}
  have hAD : d.A ∩ d.D = {d.w1} := by
    ext x; simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · intro ⟨hxA, hxD⟩
      have : x ∈ d.D ∩ Q := ⟨hxD, hAsub hxA⟩; rw [d.hDQ] at this
      simp only [mem_insert_iff, mem_singleton_iff] at this
      rcases this with rfl | rfl
      · rfl
      · exact absurd hxA hw2A
    · rintro rfl; exact ⟨d.hAw1, hw1D⟩
  -- B ∩ D = {w2}
  have hBD : d.B ∩ d.D = {d.w2} := by
    ext x; simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · intro ⟨hxB, hxD⟩
      have : x ∈ d.D ∩ Q := ⟨hxD, hBsub hxB⟩; rw [d.hDQ] at this
      simp only [mem_insert_iff, mem_singleton_iff] at this
      rcases this with rfl | rfl
      · exact absurd hxB hw1B
      · rfl
    · rintro rfl; exact ⟨d.hBw2, hw2D⟩
  -- A ∩ E = ∅: E ∩ Q = ∅, A ⊆ Q
  have hAE : d.A ∩ d.E = ∅ := by
    ext x; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxA hxE
    have : x ∈ d.E ∩ Q := ⟨hxE, hAsub hxA⟩; rw [d.hEQ] at this; exact this
  -- B ∩ E = ∅
  have hBE : d.B ∩ d.E = ∅ := by
    ext x; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxB hxE
    have : x ∈ d.E ∩ Q := ⟨hxE, hBsub hxB⟩; rw [d.hEQ] at this; exact this
  exact ⟨d.hABinter, hAC, hAD, hAE, hBC, hBD, hBE, d.hCD,
    inter_comm d.E d.C ▸ d.hEC, inter_comm d.E d.D ▸ d.hED⟩

/-- HOL Light: `jordan_curve_edge_inter` (line 58328).
Distinct arcs from {A,B,C,D,E} intersect within the vertex set. -/
theorem jordanCurveK33_edge_inter {Q : Set E2'} (d : JordanCurveK33Data Q)
    (U V : Set E2')
    (hU : U ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
    (hV : V ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
    (hne : U ≠ V) :
    U ∩ V ⊆ {d.w1, d.w2, d.x2} ∪ {d.v1, d.v2, d.x1} := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE⟩ :=
    jordanCurveK33Data_inter d
  set V6 := ({d.w1, d.w2, d.x2} : Set E2') ∪ {d.v1, d.v2, d.x1}
  have hv1 : d.v1 ∈ V6 := mem_union_right _ (mem_insert _ _)
  have hv2 : d.v2 ∈ V6 := mem_union_right _ (mem_insert_of_mem _ (mem_insert _ _))
  have hw1 : d.w1 ∈ V6 := mem_union_left _ (mem_insert _ _)
  have hw2 : d.w2 ∈ V6 := mem_union_left _ (mem_insert_of_mem _ (mem_insert _ _))
  have hx1 : d.x1 ∈ V6 :=
    mem_union_right _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  have hx2 : d.x2 ∈ V6 :=
    mem_union_left _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  simp only [mem_insert_iff, mem_singleton_iff] at hU hV
  rcases hU with rfl | rfl | rfl | rfl | rfl <;>
    rcases hV with rfl | rfl | rfl | rfl | rfl <;>
    try exact absurd rfl hne
  -- A∩B, A∩C → {v1,v2}; A∩D → {w1}; A∩E → ∅
  · rw [hAB]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hAC]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hAD]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hw1
  · rw [hAE]; exact empty_subset _
  -- B∩A, B∩C → {v1,v2}; B∩D → {w2}; B∩E → ∅
  · rw [inter_comm, hAB]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hBC]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hBD]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hw2
  · rw [hBE]; exact empty_subset _
  -- C∩A, C∩B → {v1,v2}; C∩D → ∅; C∩E → {x2}
  · rw [inter_comm, hAC]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [inter_comm, hBC]; intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hCD]; exact empty_subset _
  · rw [hCE]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hx2
  -- D∩A → {w1}; D∩B → {w2}; D∩C → ∅; D∩E → {x1}
  · rw [inter_comm, hAD]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hw1
  · rw [inter_comm, hBD]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hw2
  · rw [inter_comm, hCD]; exact empty_subset _
  · rw [hDE]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hx1
  -- E∩A, E∩B → ∅; E∩C → {x2}; E∩D → {x1}
  · rw [inter_comm, hAE]; exact empty_subset _
  · rw [inter_comm, hBE]; exact empty_subset _
  · rw [inter_comm, hCE]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hx2
  · rw [inter_comm, hDE]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hx1

/-! ## §DD.2: K₃,₃ planarity chain -/

/-- HOL Light: `jordan_curve_k33_plane_criterion2` (line 58328).
Edge disjointness + K₃,₃ data implies plane graph. -/
theorem jordanCurveK33_planeCriterion2 {Q : Set E2'} (d : JordanCurveK33Data Q)
    (hG_disjoint : ∀ e e', e ∈ (jordanCurveK33 d).edgeSet →
      e' ∈ (jordanCurveK33 d).edgeSet → e ≠ e' →
      e ∩ e' ⊆ (jordanCurveK33 d).vertexSet) :
    IsPlaneGraph (jordanCurveK33 d) :=
  jordanCurveK33_planeCriterion d (fun e he => jordanCurveK33_sing d e he) hG_disjoint

/-- HOL Light: `jordan_curve_edge_arc` (line 58358).
Every edge of the K₃,₃ graph is a simple arc. -/
theorem jordanCurveK33_edge_arc {Q : Set E2'} (d : JordanCurveK33Data Q)
    (e : Set E2') (he : e ∈ (jordanCurveK33 d).edgeSet) :
    IsSimpleArc e := by
  obtain ⟨_, _, _, _, _, _, _, hx2C, hx1D, _, _, _⟩ := d.x_mem
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
  dsimp only [jordanCurveK33] at he
  simp only [mem_insert_iff, mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSimpleArcEnd_isSimpleArc d.hE
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hAsa hv1A d.hAw1 d.hw1_ne_v1.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hAsa hv2A d.hAw1 d.hw1_ne_v2.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hBsa hv1B d.hBw2 d.hw2_ne_v1.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hBsa hv2B d.hBw2 d.hw2_ne_v2.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hCsa hv1C hx2C hx2v1.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hCsa hv2C hx2C hx2v2.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hDsa hw1D hx1D hx1w1.symm)
  · exact isSimpleArcEnd_isSimpleArc
      (cutArc_isSimpleArcEnd hDsa hw2D hx1D hx1w2.symm)

/-- HOL Light: `jordan_curve_guider_inj` (line 58389).
If an edge is a subset of two guides U,V ∈ {A,B,C,D,E}, then U = V. -/
theorem jordanCurveK33_guider_inj {Q : Set E2'} (d : JordanCurveK33Data Q)
    (e U V : Set E2')
    (he : e ∈ (jordanCurveK33 d).edgeSet)
    (hU : U ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
    (hV : V ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
    (heU : e ⊆ U) (heV : e ⊆ V) : U = V := by
  by_contra hne
  have hinf := isSimpleArc_infinite (jordanCurveK33_edge_arc d e he)
  have hV6 := jordanCurveK33_edge_inter d U V hU hV hne
  have hfin : ({d.w1, d.w2, d.x2} ∪ {d.v1, d.v2, d.x1} : Set E2').Finite :=
    (((finite_singleton _).insert _).insert _).union (((finite_singleton _).insert _).insert _)
  exact hinf (hfin.subset hV6 |>.subset (subset_inter heU heV))

/-- HOL Light: `jordan_curve_guider_disj` (line 58431).
The five arcs A,B,C,D,E are pairwise distinct. -/
theorem jordanCurveK33Data_disj {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.A ≠ d.B ∧ d.A ≠ d.C ∧ d.A ≠ d.D ∧ d.A ≠ d.E ∧
    d.B ≠ d.C ∧ d.B ≠ d.D ∧ d.B ≠ d.E ∧
    d.C ≠ d.D ∧ d.C ≠ d.E ∧ d.D ≠ d.E := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE⟩ :=
    jordanCurveK33Data_inter d
  have hAinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc d.hA)
  have hBinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc d.hB)
  have hCinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc d.hC_arc)
  have hDinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc d.hD)
  have hEinf := isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc d.hE)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    [(rw [← h, inter_self] at hAB; exact hAinf (hAB ▸ (finite_singleton _).insert _));
     (rw [← h, inter_self] at hAC; exact hAinf (hAC ▸ (finite_singleton _).insert _));
     (rw [← h, inter_self] at hAD; exact hAinf (hAD ▸ finite_singleton _));
     (rw [← h, inter_self] at hAE; exact hAinf (hAE ▸ finite_empty));
     (rw [← h, inter_self] at hBC; exact hBinf (hBC ▸ (finite_singleton _).insert _));
     (rw [← h, inter_self] at hBD; exact hBinf (hBD ▸ finite_singleton _));
     (rw [← h, inter_self] at hBE; exact hBinf (hBE ▸ finite_empty));
     (rw [← h, inter_self] at hCD; exact hCinf (hCD ▸ finite_empty));
     (rw [← h, inter_self] at hCE; exact hCinf (hCE ▸ finite_singleton _));
     (rw [← h, inter_self] at hDE; exact hDinf (hDE ▸ finite_singleton _))]

/-- HOL Light: `jordan_curve_guider_enum` (line 58462).
Each edge is a subset of one of the five arcs. -/
theorem jordanCurveK33_guider_enum {Q : Set E2'} (d : JordanCurveK33Data Q) :
    d.E ⊆ d.E ∧
    cutArc d.A d.v1 d.w1 ⊆ d.A ∧
    cutArc d.A d.v2 d.w1 ⊆ d.A ∧
    cutArc d.B d.v1 d.w2 ⊆ d.B ∧
    cutArc d.B d.v2 d.w2 ⊆ d.B ∧
    cutArc d.C d.v1 d.x2 ⊆ d.C ∧
    cutArc d.C d.v2 d.x2 ⊆ d.C ∧
    cutArc d.D d.w1 d.x1 ⊆ d.D ∧
    cutArc d.D d.w2 d.x1 ⊆ d.D := by
  obtain ⟨_, _, _, _, _, _, _, hx2C, hx1D, _, hx1E, hx2E⟩ := d.x_mem
  obtain ⟨_, _, hv1A, hv2A, hv1B, hv2B, hv1C, hv2C, _, _, _, _⟩ := d.v_mem
  obtain ⟨_, _, _, _, _, _, _, _, hw1D, hw2D, _, _⟩ := d.w_mem
  have hAsa := isSimpleArcEnd_isSimpleArc d.hA
  have hBsa := isSimpleArcEnd_isSimpleArc d.hB
  have hCsa := isSimpleArcEnd_isSimpleArc d.hC_arc
  have hDsa := isSimpleArcEnd_isSimpleArc d.hD
  have hx2v1 : d.x2 ≠ d.v1 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).1)
  have hx2v2 : d.x2 ≠ d.v2 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).2.1)
  have hx1w1 : d.x1 ≠ d.w1 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).1)
  have hx1w2 : d.x1 ≠ d.w2 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).2.1)
  exact ⟨Subset.rfl,
    cutArc_subset hAsa hv1A d.hAw1 d.hw1_ne_v1.symm,
    cutArc_subset hAsa hv2A d.hAw1 d.hw1_ne_v2.symm,
    cutArc_subset hBsa hv1B d.hBw2 d.hw2_ne_v1.symm,
    cutArc_subset hBsa hv2B d.hBw2 d.hw2_ne_v2.symm,
    cutArc_subset hCsa hv1C hx2C hx2v1.symm,
    cutArc_subset hCsa hv2C hx2C hx2v2.symm,
    cutArc_subset hDsa hw1D hx1D hx1w1.symm,
    cutArc_subset hDsa hw2D hx1D hx1w2.symm⟩

/-- HOL Light: `jordan_curve_guider_exists` (line 58491).
Every graph edge has a guide arc in {A,B,C,D,E}. -/
theorem jordanCurveK33_guider_exists {Q : Set E2'} (d : JordanCurveK33Data Q)
    (e : Set E2') (he : e ∈ (jordanCurveK33 d).edgeSet) :
    ∃ U, U ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')) ∧ e ⊆ U := by
  obtain ⟨hE, hAv1w1, hAv2w1, hBv1w2, hBv2w2, hCv1x2, hCv2x2, hDw1x1, hDw2x1⟩ :=
    jordanCurveK33_guider_enum d
  dsimp only [jordanCurveK33] at he
  simp only [mem_insert_iff, mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨d.E, by simp, hE⟩
  · exact ⟨d.A, by simp, hAv1w1⟩
  · exact ⟨d.A, by simp, hAv2w1⟩
  · exact ⟨d.B, by simp, hBv1w2⟩
  · exact ⟨d.B, by simp, hBv2w2⟩
  · exact ⟨d.C, by simp, hCv1x2⟩
  · exact ⟨d.C, by simp, hCv2x2⟩
  · exact ⟨d.D, by simp, hDw1x1⟩
  · exact ⟨d.D, by simp, hDw2x1⟩

/-- HOL Light: `jordan_curve_guider_sep_lemma` (line 58510).
Each guide determines precisely which cut-arcs the edge can be. -/
theorem jordanCurveK33_guider_sep_lemma {Q : Set E2'} (d : JordanCurveK33Data Q)
    (e : Set E2') (he : e ∈ (jordanCurveK33 d).edgeSet) :
    (e ⊆ d.A → e = cutArc d.A d.v1 d.w1 ∨ e = cutArc d.A d.v2 d.w1) ∧
    (e ⊆ d.B → e = cutArc d.B d.v1 d.w2 ∨ e = cutArc d.B d.v2 d.w2) ∧
    (e ⊆ d.C → e = cutArc d.C d.v1 d.x2 ∨ e = cutArc d.C d.v2 d.x2) ∧
    (e ⊆ d.D → e = cutArc d.D d.w1 d.x1 ∨ e = cutArc d.D d.w2 d.x1) ∧
    (e ⊆ d.E → e = d.E) := by
  obtain ⟨_, hAv1w1, hAv2w1, hBv1w2, hBv2w2, hCv1x2, hCv2x2, hDw1x1, hDw2x1⟩ :=
    jordanCurveK33_guider_enum d
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE⟩ :=
    jordanCurveK33Data_disj d
  have he' := he
  dsimp only [jordanCurveK33] at he
  simp only [mem_insert_iff, mem_singleton_iff] at he
  have ctr (G U : Set E2') (hG : G ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
      (hU : U ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
      (hne : G ≠ U) (heG : e ⊆ G) (heU : e ⊆ U) : False :=
    hne (jordanCurveK33_guider_inj d e G U he' hG hU heG heU)
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAE.symm Subset.rfl h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBE.symm Subset.rfl h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hCE.symm Subset.rfl h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hDE.symm Subset.rfl h).elim, fun _ => rfl⟩
  · exact ⟨fun _ => Or.inl rfl, fun h => (ctr _ _ (by simp) (by simp) hAB hAv1w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAC hAv1w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAD hAv1w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAE hAv1w1 h).elim⟩
  · exact ⟨fun _ => Or.inr rfl, fun h => (ctr _ _ (by simp) (by simp) hAB hAv2w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAC hAv2w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAD hAv2w1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hAE hAv2w1 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAB.symm hBv1w2 h).elim, fun _ => Or.inl rfl,
      fun h => (ctr _ _ (by simp) (by simp) hBC hBv1w2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBD hBv1w2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBE hBv1w2 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAB.symm hBv2w2 h).elim, fun _ => Or.inr rfl,
      fun h => (ctr _ _ (by simp) (by simp) hBC hBv2w2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBD hBv2w2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBE hBv2w2 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAC.symm hCv1x2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBC.symm hCv1x2 h).elim, fun _ => Or.inl rfl,
      fun h => (ctr _ _ (by simp) (by simp) hCD hCv1x2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hCE hCv1x2 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAC.symm hCv2x2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBC.symm hCv2x2 h).elim, fun _ => Or.inr rfl,
      fun h => (ctr _ _ (by simp) (by simp) hCD hCv2x2 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hCE hCv2x2 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAD.symm hDw1x1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBD.symm hDw1x1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hCD.symm hDw1x1 h).elim, fun _ => Or.inl rfl,
      fun h => (ctr _ _ (by simp) (by simp) hDE hDw1x1 h).elim⟩
  · exact ⟨fun h => (ctr _ _ (by simp) (by simp) hAD.symm hDw2x1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hBD.symm hDw2x1 h).elim,
      fun h => (ctr _ _ (by simp) (by simp) hCD.symm hDw2x1 h).elim, fun _ => Or.inr rfl,
      fun h => (ctr _ _ (by simp) (by simp) hDE hDw2x1 h).elim⟩

/-- HOL Light: `cut_arc_inter_lemma` (line 58537).
If u is an interior point of R, the two cut arcs at u intersect within {u}. -/
theorem cutArc_inter_lemma {X : Set E2'} {R : Set E2'} {u v w : E2'}
    (hu : u ∈ X) (hR : IsSimpleArcEnd R v w) (hRu : u ∈ R)
    (huv : u ≠ v) (huw : u ≠ w) :
    cutArc R v u ∩ cutArc R w u ⊆ X := by
  have ⟨hint, _⟩ := cutArc_inter hR hRu huv huw
  rw [cutArc_symm R u w] at hint
  rw [hint]; intro x hx; simp only [mem_singleton_iff] at hx; subst hx; exact hu

/-- HOL Light: `jordan_curve_cut_inter` (line 58557).
The four pairs of cut-arcs sharing an arc each intersect ⊆ vertex set. -/
theorem jordanCurveK33_cut_inter {Q : Set E2'} (d : JordanCurveK33Data Q) :
    cutArc d.A d.v1 d.w1 ∩ cutArc d.A d.v2 d.w1 ⊆ (jordanCurveK33 d).vertexSet ∧
    cutArc d.B d.v1 d.w2 ∩ cutArc d.B d.v2 d.w2 ⊆ (jordanCurveK33 d).vertexSet ∧
    cutArc d.C d.v1 d.x2 ∩ cutArc d.C d.v2 d.x2 ⊆ (jordanCurveK33 d).vertexSet ∧
    cutArc d.D d.w1 d.x1 ∩ cutArc d.D d.w2 d.x1 ⊆ (jordanCurveK33 d).vertexSet := by
  obtain ⟨_, _, _, _, _, _, _, hx2C, hx1D, _, _, _⟩ := d.x_mem
  have hx2v1 : d.x2 ≠ d.v1 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).1)
  have hx2v2 : d.x2 ≠ d.v2 := fun h => (d.x_mem).2.1 (h ▸ (d.v_mem).2.1)
  have hx1w1 : d.x1 ≠ d.w1 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).1)
  have hx1w2 : d.x1 ≠ d.w2 := fun h => (d.x_mem).1 (h ▸ (d.w_mem).2.1)
  have hw1V : d.w1 ∈ (jordanCurveK33 d).vertexSet :=
    show d.w1 ∈ ({d.w1, d.w2, d.x2} : Set E2') ∪ {d.v1, d.v2, d.x1} from
      Or.inl (mem_insert _ _)
  have hw2V : d.w2 ∈ (jordanCurveK33 d).vertexSet :=
    show d.w2 ∈ ({d.w1, d.w2, d.x2} : Set E2') ∪ {d.v1, d.v2, d.x1} from
      Or.inl (mem_insert_of_mem _ (mem_insert _ _))
  have hx2V : d.x2 ∈ (jordanCurveK33 d).vertexSet :=
    show d.x2 ∈ ({d.w1, d.w2, d.x2} : Set E2') ∪ {d.v1, d.v2, d.x1} from
      Or.inl (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  have hx1V : d.x1 ∈ (jordanCurveK33 d).vertexSet :=
    show d.x1 ∈ ({d.w1, d.w2, d.x2} : Set E2') ∪ {d.v1, d.v2, d.x1} from
      Or.inr (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  exact ⟨
    cutArc_inter_lemma hw1V d.hA d.hAw1 d.hw1_ne_v1 d.hw1_ne_v2,
    cutArc_inter_lemma hw2V d.hB d.hBw2 d.hw2_ne_v1 d.hw2_ne_v2,
    cutArc_inter_lemma hx2V d.hC_arc hx2C hx2v1 hx2v2,
    cutArc_inter_lemma hx1V d.hD hx1D hx1w1 hx1w2⟩

/-- HOL Light: `jordan_curve_guider_separate` (line 58583).
Two distinct edges sharing the same guide arc intersect within the vertex set. -/
theorem jordanCurveK33_guider_separate {Q : Set E2'} (d : JordanCurveK33Data Q)
    {U e e' : Set E2'}
    (hU : U ∈ ({d.A, d.B, d.C, d.D, d.E} : Set (Set E2')))
    (heU : e ⊆ U) (he'U : e' ⊆ U)
    (he : e ∈ (jordanCurveK33 d).edgeSet)
    (he' : e' ∈ (jordanCurveK33 d).edgeSet)
    (hne : e ≠ e') :
    e ∩ e' ⊆ (jordanCurveK33 d).vertexSet := by
  obtain ⟨hA_ci, hB_ci, hC_ci, hD_ci⟩ := jordanCurveK33_cut_inter d
  obtain ⟨hA_sep, hB_sep, hC_sep, hD_sep, hE_sep⟩ := jordanCurveK33_guider_sep_lemma d e he
  obtain ⟨hA_sep', hB_sep', hC_sep', hD_sep', hE_sep'⟩ := jordanCurveK33_guider_sep_lemma d e' he'
  simp only [mem_insert_iff, mem_singleton_iff] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl
  -- U = A: e,e' ∈ {cutArc A v1 w1, cutArc A v2 w1}, e ≠ e' → use cut_inter
  · rcases hA_sep heU with rfl | rfl <;> rcases hA_sep' he'U with rfl | rfl
    · exact absurd rfl hne
    · exact hA_ci
    · rw [inter_comm]; exact hA_ci
    · exact absurd rfl hne
  · rcases hB_sep heU with rfl | rfl <;> rcases hB_sep' he'U with rfl | rfl
    · exact absurd rfl hne
    · exact hB_ci
    · rw [inter_comm]; exact hB_ci
    · exact absurd rfl hne
  · rcases hC_sep heU with rfl | rfl <;> rcases hC_sep' he'U with rfl | rfl
    · exact absurd rfl hne
    · exact hC_ci
    · rw [inter_comm]; exact hC_ci
    · exact absurd rfl hne
  · rcases hD_sep heU with rfl | rfl <;> rcases hD_sep' he'U with rfl | rfl
    · exact absurd rfl hne
    · exact hD_ci
    · rw [inter_comm]; exact hD_ci
    · exact absurd rfl hne
  · exact absurd (hE_sep heU ▸ (hE_sep' he'U).symm) hne

/-- HOL Light: `jordan_curve_k33_plane` (line 58634).
The K₃,₃ graph constructed from one-sided data is a plane graph. -/
theorem jordanCurveK33_isPlaneGraph {Q : Set E2'} (d : JordanCurveK33Data Q) :
    IsPlaneGraph (jordanCurveK33 d) := by
  apply jordanCurveK33_planeCriterion2
  intro e e' he he' hne
  obtain ⟨U, hU, heU⟩ := jordanCurveK33_guider_exists d e he
  obtain ⟨V, hV, he'V⟩ := jordanCurveK33_guider_exists d e' he'
  by_cases hUV : U = V
  · subst hUV; exact jordanCurveK33_guider_separate d hU heU he'V he he' hne
  · exact (inter_subset_inter heU he'V).trans (jordanCurveK33_edge_inter d U V hU hV hUV)

/-- HOL Light: `jordan_curve_not_one_sided` (line 58671).
No simple closed curve in ℝ² is one-sided. -/
theorem jordan_curve_not_one_sided {Q : Set E2'}
    (hQ : IsSimpleClosedCurve Q) :
    ¬ OneSidedJordanCurve Q := by
  intro hOS
  have ⟨d⟩ := jordanCurveK33Data_exists hQ hOS
  exact k33_nonplanar
    ⟨jordanCurveK33 d, jordanCurveK33_isPlaneGraph d,
     jordanCurveK33_isk33 d hOS⟩

/-! ## §DD.3: Component topology -/

/-- HOL Light: `component_simple_arc_ver2` (line 58713).
In the complement of a closed set, two distinct points are in the same
connected component iff there exists a simple arc between them avoiding the set. -/
theorem component_simple_arc_ver2 {G : Set E2'} {x y : E2'}
    (hG : IsClosed G) (hxy : x ≠ y) :
    y ∈ connectedComponentIn Gᶜ x ↔
    ∃ C, IsSimpleArcEnd C x y ∧ Disjoint C G := by
  constructor
  · intro hy
    have hxGc : x ∈ Gᶜ := by
      by_contra hx
      simp only [connectedComponentIn, dif_neg hx] at hy
      exact hy.elim
    have hopen : IsOpen Gᶜ := hG.isOpen_compl
    have hAconn : IsPreconnected (connectedComponentIn Gᶜ x) :=
      isPreconnected_connectedComponentIn
    have hAne : (connectedComponentIn Gᶜ x).Nonempty :=
      ⟨x, mem_connectedComponentIn hxGc⟩
    have hAconnected : IsConnected (connectedComponentIn Gᶜ x) := ⟨hAne, hAconn⟩
    have hAopen : IsOpen (connectedComponentIn Gᶜ x) :=
      IsOpen.connectedComponentIn hopen
    have hpc := pathConnected_of_isConnected_isOpen hAopen hAconnected
    have hx := mem_connectedComponentIn hxGc
    rcases hpc x hx y hy with rfl | ⟨C, hC, hCsub⟩
    · exact absurd rfl hxy
    · exact ⟨C, hC, Set.disjoint_of_subset_left
        (hCsub.trans (connectedComponentIn_subset Gᶜ x)) disjoint_compl_left⟩
  · rintro ⟨C, hC, hCG⟩
    have hCsub : C ⊆ Gᶜ := Set.subset_compl_iff_disjoint_left.mpr hCG.symm
    have hxC := isSimpleArcEnd_mem_left hC
    have hyC := isSimpleArcEnd_mem_right hC
    have hconn := (isSimpleArc_isConnected (isSimpleArcEnd_isSimpleArc hC)).isPreconnected
    exact (hconn.subset_connectedComponentIn hxC hCsub) hyC

/-- HOL Light: `component_properties` (line 58847).
Component of v in complement of closed C: open, connected, nonempty,
disjoint from C, contains v, and membership is characterized by arcs. -/
theorem component_properties {C : Set E2'} {v : E2'}
    (hC : IsClosed C) (hv : v ∉ C) :
    let A := connectedComponentIn Cᶜ v
    IsOpen A ∧ IsPreconnected A ∧ A.Nonempty ∧ Disjoint A C ∧ v ∈ A ∧
    ∀ w, w ≠ v → (w ∈ A ↔ ∃ P, IsSimpleArcEnd P v w ∧ Disjoint P C) := by
  intro A
  have hvCc : v ∈ Cᶜ := mem_compl hv
  have hopen : IsOpen Cᶜ := hC.isOpen_compl
  have hAopen : IsOpen A := IsOpen.connectedComponentIn hopen
  have hAconn : IsPreconnected A := isPreconnected_connectedComponentIn
  have hvA : v ∈ A := mem_connectedComponentIn hvCc
  have hAne : A.Nonempty := ⟨v, hvA⟩
  have hAsub : A ⊆ Cᶜ := connectedComponentIn_subset Cᶜ v
  have hAC : Disjoint A C := Set.disjoint_of_subset_left hAsub disjoint_compl_left
  refine ⟨hAopen, hAconn, hAne, hAC, hvA, fun w hw => ?_⟩
  exact component_simple_arc_ver2 hC hw.symm

/-! ## §DD.4: The Jordan Curve Theorem -/

/-- HOL Light: `JORDAN_CURVE_THEOREM` (line 59014).
**The Jordan Curve Theorem.** Every simple closed curve in ℝ² separates
the plane into exactly two regions: there exist open connected sets A, B
with A ∩ B = ∅, A ∩ C = ∅, B ∩ C = ∅, and A ∪ B ∪ C = ℝ². -/
theorem jordan_curve_theorem {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsSimpleClosedCurve C) :
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen A ∧ IsOpen B ∧
      IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = Set.univ := by
  -- Step 1: Not one-sided → ∃ v w separated by C
  have hNOS := jordan_curve_not_one_sided hC
  unfold OneSidedJordanCurve at hNOS; push Not at hNOS
  obtain ⟨v, w, hv, hw, hvw, hconn⟩ := hNOS
  -- hconn : ∀ P, ¬(IsSimpleArcEnd P v w ∧ P ∩ C = ∅)
  have hClosed := isSimpleClosedCurve_isClosed hC
  -- Step 2: Define and characterize components
  set A := connectedComponentIn Cᶜ v
  set B := connectedComponentIn Cᶜ w
  obtain ⟨hAo, hAc, hAne, hAC, hvA, hAchar⟩ := component_properties hClosed hv
  obtain ⟨hBo, hBc, hBne, hBC, hwB, hBchar⟩ := component_properties hClosed hw
  -- hconn already has type ∀ P, IsSimpleArcEnd P v w → (P ∩ C).Nonempty (after push Not)
  refine ⟨A, B, hAo, hBo, ⟨hAne, hAc⟩, ⟨hBne, hBc⟩, ?_, hAC, hBC, ?_⟩
  -- Step 3a: Disjoint A B
  · rw [Set.disjoint_left]; intro u huA huB
    -- u ∈ A and u ∈ B → A = B via connectedComponentIn_eq
    have hAeq := connectedComponentIn_eq huA  -- A = compIn Cᶜ u
    have hBeq := connectedComponentIn_eq huB  -- B = compIn Cᶜ u
    have hAB : A = B := hAeq.trans hBeq.symm
    have hvB : v ∈ B := hAB ▸ hvA
    obtain ⟨P, hP, hPdisj⟩ := (hBchar v hvw).mp hvB
    obtain ⟨x, hx⟩ := hconn P (isSimpleArcEnd_symm hP)
    exact absurd hx.2 (Set.disjoint_left.mp hPdisj hx.1)
  -- Step 3b: A ∪ B ∪ C = univ
  · ext x; simp only [mem_union, mem_univ, iff_true]
    by_contra hx
    have hxC : x ∉ C := fun h => hx (Or.inr h)
    have hxA : x ∉ A := fun h => hx (Or.inl (Or.inl h))
    have hxB : x ∉ B := fun h => hx (Or.inl (Or.inr h))
    have hxv : x ≠ v := fun h => hxA (h ▸ hvA)
    have hxw : x ≠ w := fun h => hxB (h ▸ hwB)
    -- Any arc from v to x meets C
    have hvx_hits : ∀ P, IsSimpleArcEnd P v x → (P ∩ C).Nonempty := by
      intro P hP; by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      exact hxA ((hAchar x hxv).mpr
        ⟨P, hP, Set.disjoint_iff_inter_eq_empty.mpr hne⟩)
    -- Any arc from w to x meets C
    have hwx_hits : ∀ P, IsSimpleArcEnd P w x → (P ∩ C).Nonempty := by
      intro P hP; by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      exact hxB ((hBchar x hxw).mpr
        ⟨P, hP, Set.disjoint_iff_inter_eq_empty.mpr hne⟩)
    -- Apply jordan_curve_no_inj3 with p = ![v, w, x]
    exact jordan_curve_no_inj3 hC
      (show Function.Injective (![v, w, x]) by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
      (show ∀ i, (![v, w, x]) i ∉ C by
        intro i; fin_cases i <;> simp [hv, hw, hxC])
      (show ∀ i j P, IsSimpleArcEnd P ((![v, w, x]) i) ((![v, w, x]) j) →
          (P ∩ C).Nonempty by
        intro i j P hP
        fin_cases i <;> fin_cases j <;>
          simp only [] at hP ⊢
        all_goals first
          | exact absurd rfl (isSimpleArcEnd_distinct hP)
          | exact hconn P hP
          | exact hconn P (isSimpleArcEnd_symm hP)
          | exact hvx_hits P hP
          | exact hvx_hits P (isSimpleArcEnd_symm hP)
          | exact hwx_hits P hP
          | exact hwx_hits P (isSimpleArcEnd_symm hP))

-- JORDAN_CURVE_DEFS (line 59137): Not applicable to Lean.
-- It is a self-contained packaging of HOL Light definitions for presentation.
-- In Lean, all definitions (IsSimpleClosedCurve, etc.) are already available
-- through the import chain.

end JordanCurveTheorem
