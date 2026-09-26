/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionR_AdvancedParity

/-!
# Section S: 2-Connectivity and Rectangle Grids
## HOL Light: Section S (Lines 37553–39524)

This section develops the theory of 2-connected subgraphs of the grid:
- `segment_end`: a segment with two specified endpoints
- `conn`: edge sets such that any two closure points are joined by a sub-segment
- `conn2`: 2-connected edge sets (any segment can avoid a third point)
- `rectangle_grid`: rectangular grids of edges
- Key results: rectagons are conn2, rectangle grids are conn2, conn2 sets contain rectagons
-/

open Set Metric Topology Function

-- Helper: numClosure additivity for disjoint unions
private theorem numClosure_disjoint_union {A B : Finset (Set E2)} (hDisj : Disjoint A B)
    (m : ℤ × ℤ) : numClosure (A ∪ B) m = numClosure A m + numClosure B m := by
  open Classical in
  unfold numClosure incidentEdges; rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hDisj.mono (Finset.filter_subset _ A) (Finset.filter_subset _ B))

-- Helper: cls membership ↔ numClosure positive
private theorem cls_iff_numClosure_pos {E : Finset (Set E2)} {m : ℤ × ℤ} :
    m ∈ cls E ↔ 0 < numClosure E m := by
  constructor
  · rintro ⟨e, he, hcl⟩
    have : ¬numClosure E m = 0 := by
      rw [numClosure_eq_zero_iff]; push Not; exact ⟨e, he, hcl⟩
    omega
  · intro h
    by_contra hc; simp only [cls, Set.mem_setOf_eq, not_exists] at hc
    push Not at hc
    have : numClosure E m = 0 := (numClosure_eq_zero_iff E m).mpr (fun e he => hc e he)
    omega

/-! ## §S.1 Definitions -/

/-- HOL Light: `segment_end` (line 37589).
`segment_end E a b` means E forms a psegment (connected edge set with exactly two
degree-1 vertices) whose two endpoints are a and b. -/
def segment_end (E : Finset (Set E2)) (a b : ℤ × ℤ) : Prop :=
  ∃ (G : Segment), G.edges = E ∧ G.isEndpoint a ∧ G.isEndpoint b ∧ a ≠ b ∧
    (∀ m, G.isEndpoint m → m = a ∨ m = b)

/-- HOL Light: `conn` (line 37593).
E is connected: any two distinct closure points are joined by a sub-segment. -/
def conn (E : Finset (Set E2)) : Prop :=
  ∀ a b, a ∈ cls E → b ∈ cls E → a ≠ b → ∃ S ⊆ E, segment_end S a b

/-- HOL Light: `conn2` (line 37597).
E is 2-connected: has ≥2 edges, and for any three pairwise-distinct points a, b, c
with a, b in cls E, there is a sub-segment from a to b whose closure avoids c. -/
def conn2 (E : Finset (Set E2)) : Prop :=
  2 ≤ E.card ∧
  ∀ a b c, a ∈ cls E → b ∈ cls E → a ≠ b → b ≠ c → a ≠ c →
    ∃ S ⊆ E, segment_end S a b ∧ c ∉ cls S

/-- HOL Light: `rectangle_grid` (line 38863).
The set of edges in the rectangular grid from p to q.
Horizontal edges: h_edge m with p.1 ≤ m.1, m.1+1 ≤ q.1, p.2 ≤ m.2 ≤ q.2.
Vertical edges: v_edge m with p.1 ≤ m.1 ≤ q.1, p.2 ≤ m.2, m.2+1 ≤ q.2. -/
noncomputable def rectangle_grid (p q : ℤ × ℤ) : Finset (Set E2) :=
  ((Finset.Icc p.1 (q.1 - 1)) ×ˢ (Finset.Icc p.2 q.2)).image (fun m => hEdge m) ∪
  ((Finset.Icc p.1 q.1) ×ˢ (Finset.Icc p.2 (q.2 - 1))).image (fun m => vEdge m)

/-! ## §S.2 Basic segment_end properties -/

/-- HOL Light: `segment_end_symm` (line 37605). -/
theorem segment_end_symm (S : Finset (Set E2)) (a b : ℤ × ℤ) :
    segment_end S a b ↔ segment_end S b a := by
  constructor <;> intro ⟨G, hEdges, hea, heb, hab, huniq⟩
  · exact ⟨G, hEdges, heb, hea, hab.symm, fun m hm => (huniq m hm).symm⟩
  · exact ⟨G, hEdges, heb, hea, hab.symm, fun m hm => (huniq m hm).symm⟩

/-- HOL Light: `segment_end_disj` (line 37622). -/
theorem segment_end_disj {S : Finset (Set E2)} {a b : ℤ × ℤ}
    (h : segment_end S a b) : a ≠ b := by
  obtain ⟨_, _, _, _, hab, _⟩ := h; exact hab

/-- HOL Light: `segment_end_inj` (line 37791).
For a fixed segment and one endpoint, the other endpoint is uniquely determined. -/
theorem segment_end_inj {S : Finset (Set E2)} {a b c : ℤ × ℤ}
    (hab : segment_end S a b) (hac : segment_end S a c) : b = c := by
  obtain ⟨G₁, rfl, ha₁, hb₁, hab₁, huniq₁⟩ := hab
  obtain ⟨G₂, hE₂, _, hc₂, hac₁, _⟩ := hac
  -- c is an endpoint of G₁ (same edge set)
  have hc₁ : G₁.isEndpoint c := by
    have h : numClosure G₂.edges c = 1 := hc₂
    rwa [hE₂] at h
  rcases huniq₁ c hc₁ with hca | hcb
  · exact absurd hca hac₁.symm
  · exact hcb.symm

/-- HOL Light: `segment_end_finite` (line 37808).
In Lean, Finset is automatically finite. We provide this for compatibility. -/
theorem segment_end_finite {S : Finset (Set E2)} {a b : ℤ × ℤ}
    (h : segment_end S a b) : S.Nonempty := by
  obtain ⟨G, hE, _, _, _, _⟩ := h; rw [← hE]; exact G.nonempty

/-- HOL Light: `segment_end_cls` (line 37987). -/
theorem segment_end_cls {A : Finset (Set E2)} {a b : ℤ × ℤ}
    (h : segment_end A a b) : a ∈ cls A := by
  obtain ⟨G, hE, ha, _, _, _⟩ := h
  -- a is an endpoint, so numClosure = 1, so ∃ edge incident to a
  rw [← hE]
  have := G.terminalEdge_prop a ha
  exact ⟨G.terminalEdge a, this.1, this.2⟩

/-- HOL Light: `segment_end_cls2` (line 37995). -/
theorem segment_end_cls2 {A : Finset (Set E2)} {a b : ℤ × ℤ}
    (h : segment_end A a b) : b ∈ cls A := by
  rw [segment_end_symm] at h; exact segment_end_cls h

/-- HOL Light: `segment_end_sing` (line 38466).
A single edge with two distinct closure points forms a segment with those endpoints. -/
theorem segment_end_sing {a b : ℤ × ℤ} {e : Set E2}
    (ha : pointI a ∈ closure e) (hb : pointI b ∈ closure e)
    (hab : a ≠ b) (he : isEdge e) : segment_end {e} a b := by
  obtain ⟨G, hGe, a', b', hab', ha', hb', huniq⟩ := single_edge_isPsegment e he
  -- a and b are endpoints of G (same edge set {e})
  have ha_ep : G.isEndpoint a := by
    have h : numClosure G.edges a = 1 := by
      rw [hGe]; unfold numClosure
      have : incidentEdges ({e} : Finset (Set E2)) a = {e} := by
        ext x; simp only [incidentEdges, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨And.left, fun hx => ⟨hx, hx ▸ ha⟩⟩
      simp [this]
    exact h
  have hb_ep : G.isEndpoint b := by
    have h : numClosure G.edges b = 1 := by
      rw [hGe]; unfold numClosure
      have : incidentEdges ({e} : Finset (Set E2)) b = {e} := by
        ext x; simp only [incidentEdges, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨And.left, fun hx => ⟨hx, hx ▸ hb⟩⟩
      simp [this]
    exact h
  refine ⟨G, hGe, ha_ep, hb_ep, hab, fun m hm => ?_⟩
  rcases huniq a ha_ep with ha1 | ha2 <;> rcases huniq b hb_ep with hb1 | hb2
  · exact absurd (ha1.trans hb1.symm) hab
  · rcases huniq m hm with hm | hm
    · left; rw [hm, ← ha1]
    · right; rw [hm, ← hb2]
  · rcases huniq m hm with hm | hm
    · right; rw [hm, ← hb1]
    · left; rw [hm, ← ha2]
  · exact absurd (ha2.trans hb2.symm) hab

/-! ## §S.3 Segment cutting and unions -/

/-- HOL Light: `cut_psegment` (line 37637).
A segment from a to b can be cut at an intermediate closure point c
into two disjoint segments a↔c and c↔b. -/
theorem cut_psegment {E : Finset (Set E2)} {a b c : ℤ × ℤ}
    (hS : segment_end E a b) (hc : c ∈ cls E) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ A B : Finset (Set E2), E = A ∪ B ∧ Disjoint A B ∧
      cls A ∩ cls B = {c} ∧ segment_end A a c ∧ segment_end B c b := by
  -- Extract segment G and its psegment structure
  obtain ⟨G, rfl, ha_ep, hb_ep, hab, huniq⟩ := hS
  have hG_ps : G.isPsegment := ⟨a, b, hab, ha_ep, hb_ep, huniq⟩
  -- numClosure at c = 2 (c ∈ cls so > 0; c not endpoint so ≠ 1; degree_bound ≤ 2)
  have hc_nc : numClosure G.edges c = 2 := by
    have hc_pos := cls_iff_numClosure_pos.mp hc
    have hd := G.degree_bound c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    have : numClosure G.edges c ≠ 1 := fun h =>
      (huniq c h).elim hca hcb
    omega
  -- Get linear ordering of edges
  set N := G.edges.card with hN_def
  have hN_pos : 0 < N := G.nonempty.card_pos
  obtain ⟨f, hfmem, hfinj, hfsurj, hf0, hflast, hfadj⟩ :=
    G.psegment_order hG_ps a b ha_ep hb_ep hab
  have hfedge : ∀ i, i < N → isEdge (f i) :=
    fun i hi => G.all_edges _ (hfmem i hi)
  -- Closure facts for a and b
  have hcl_a0 : pointI a ∈ closure (f 0) := by
    rw [hf0]; exact (G.terminalEdge_prop a ha_ep).2
  have hcl_bN : pointI b ∈ closure (f (N - 1)) := by
    rw [hflast hN_pos]; exact (G.terminalEdge_prop b hb_ep).2
  -- Find two edges through c and their consecutive indices
  obtain ⟨ec1, ec2, hne12, hec1, hec2, hcl_c1, hcl_c2, _⟩ :=
    (numClosure_eq_two_iff G.edges c).mp hc_nc
  obtain ⟨j1, hj1lt, hfj1⟩ := hfsurj ec1 hec1
  obtain ⟨j2, hj2lt, hfj2⟩ := hfsurj ec2 hec2
  have hj12 : j1 ≠ j2 := fun h => hne12 (hfj1 ▸ hfj2 ▸ congrArg f h)
  have h_c1 : pointI c ∈ closure (f j1) := hfj1 ▸ hcl_c1
  have h_c2 : pointI c ∈ closure (f j2) := hfj2 ▸ hcl_c2
  have hadj12 : cellAdj (f j1) (f j2) :=
    closure_imp_cellAdj _ _ c (isEdge_isCell (hfedge j1 hj1lt))
      (isEdge_isCell (hfedge j2 hj2lt)) h_c1 h_c2
      (fun h => hj12 (hfinj j1 j2 hj1lt hj2lt h))
  -- Get k such that f(k) and f(k+1) both contain c
  obtain ⟨k, hkN, hcl_ck, hcl_ck1⟩ :
      ∃ k, k + 1 < N ∧ pointI c ∈ closure (f k) ∧
        pointI c ∈ closure (f (k + 1)) := by
    rcases (hfadj j1 j2 hj1lt hj2lt).mp hadj12 with h | h
    · exact ⟨j1, by omega, h_c1, h ▸ h_c2⟩
    · exact ⟨j2, by omega, h_c2, h ▸ h_c1⟩
  -- Build psegments for each half
  obtain ⟨PA, hPAps, hPAedges⟩ := order_imp_psegment f (k + 1) (by omega)
    (fun i j hi hj => hfinj i j (by omega) (by omega))
    (fun i hi => hfedge i (by omega))
    (fun i j hi hj => hfadj i j (by omega) (by omega))
  obtain ⟨PB, hPBps, hPBedges⟩ := order_imp_psegment_shift f (k + 1) N hkN
    (fun i j hilo hihi hjlo hjhi => hfinj i j hihi hjhi)
    (fun i _ hi => hfedge i hi)
    (fun i j _ hi _ hj => hfadj i j hi hj)
  -- Subset and partition
  have hPA_sub : PA.edges ⊆ G.edges := by
    rw [hPAedges]; intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact hfmem i (by have := Finset.mem_range.mp hi; omega)
  have hGeqAB : G.edges = PA.edges ∪ PB.edges := by
    rw [hPAedges, hPBedges]; ext e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · intro he; obtain ⟨i, hi, hfi⟩ := hfsurj e he
      by_cases h : i < k + 1
      · exact Or.inl ⟨i, h, hfi⟩
      · exact Or.inr ⟨i, ⟨by omega, hi⟩, hfi⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, ⟨_, hi⟩, rfl⟩) <;>
        exact hfmem i (by omega)
  have hDisjAB : Disjoint PA.edges PB.edges := by
    rw [hPAedges, hPBedges, Finset.disjoint_left]
    intro e he hbe
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, hfij⟩ := Finset.mem_image.mp hbe
    have := hfinj i j (by have := Finset.mem_range.mp hi; omega)
      (Finset.mem_Ico.mp hj).2 hfij.symm
    have := Finset.mem_range.mp hi
    have := (Finset.mem_Ico.mp hj).1; omega
  have hEdiff : G.edges \ PA.edges = PB.edges := by
    ext e; simp only [Finset.mem_sdiff]; constructor
    · intro ⟨he, hna⟩
      rw [hGeqAB] at he
      exact (Finset.mem_union.mp he).resolve_left hna
    · intro h
      exact ⟨hGeqAB ▸ Finset.mem_union.mpr (Or.inr h),
        Finset.disjoint_left.mp hDisjAB.symm h⟩
  -- Key edge membership facts
  have hf0_PA : f 0 ∈ PA.edges := by
    rw [hPAedges]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hfk_PA : f k ∈ PA.edges := by
    rw [hPAedges]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hfk1_PB : f (k + 1) ∈ PB.edges := by
    rw [hPBedges]
    exact Finset.mem_image.mpr
      ⟨k + 1, Finset.mem_Ico.mpr ⟨le_refl _, hkN⟩, rfl⟩
  have hfN1_PB : f (N - 1) ∈ PB.edges := by
    rw [hPBedges]
    exact Finset.mem_image.mpr
      ⟨N - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  -- Endpoint calculations
  have hncA_a : numClosure PA.edges a = 1 := by
    have hadd := numClosure_disjoint_union hDisjAB a
    rw [← hGeqAB] at hadd
    have ha1 : numClosure G.edges a = 1 := ha_ep
    have hpos : 0 < numClosure PA.edges a :=
      cls_iff_numClosure_pos.mp ⟨f 0, hf0_PA, hcl_a0⟩
    omega
  have hncA_c : numClosure PA.edges c = 1 :=
    psegment_subset_endpoint G hG_ps PA.edges c hPA_sub
      (cls_iff_numClosure_pos.mp ⟨f k, hfk_PA, hcl_ck⟩)
      (by rw [hEdiff]
          exact cls_iff_numClosure_pos.mp ⟨f (k + 1), hfk1_PB, hcl_ck1⟩)
  have hncB_c : numClosure PB.edges c = 1 := by
    have hadd := numClosure_disjoint_union hDisjAB c
    rw [← hGeqAB, hc_nc, hncA_c] at hadd; omega
  have hncB_b : numClosure PB.edges b = 1 := by
    have hadd := numClosure_disjoint_union hDisjAB b
    rw [← hGeqAB] at hadd
    have hb1 : numClosure G.edges b = 1 := hb_ep
    have hpos : 0 < numClosure PB.edges b :=
      cls_iff_numClosure_pos.mp ⟨f (N - 1), hfN1_PB, hcl_bN⟩
    omega
  -- Build segment_end for each half
  have hsegA : segment_end PA.edges a c :=
    ⟨PA, rfl, hncA_a, hncA_c, Ne.symm hca,
     fun q hq => PA.two_endpoint_bound c a hncA_c hncA_a
       (Ne.symm hca) q hq⟩
  have hsegB : segment_end PB.edges c b :=
    ⟨PB, rfl, hncB_c, hncB_b, hcb,
     fun q hq => PB.two_endpoint_bound b c hncB_b hncB_c hcb q hq⟩
  -- cls PA.edges ∩ cls PB.edges = {c}
  have hcls : cls PA.edges ∩ cls PB.edges = {c} := by
    ext p; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hp_A, hp_B⟩
      have hpA := cls_iff_numClosure_pos.mp hp_A
      have hpB' : 0 < numClosure (G.edges \ PA.edges) p := by
        rw [hEdiff]; exact cls_iff_numClosure_pos.mp hp_B
      have hep : numClosure PA.edges p = 1 :=
        psegment_subset_endpoint G hG_ps PA.edges p hPA_sub hpA hpB'
      rcases PA.two_endpoint_bound c a hncA_c hncA_a
          (Ne.symm hca) p hep with hp_eq | hp_eq
      · -- p = a: numClosure G.edges a = 1, but both halves ≥ 1
        exfalso
        rw [hp_eq] at hp_B
        have hadd := numClosure_disjoint_union hDisjAB a
        rw [← hGeqAB] at hadd
        have ha1 : numClosure G.edges a = 1 := ha_ep
        have hpB_pos := cls_iff_numClosure_pos.mp hp_B
        omega
      · exact hp_eq
    · intro hp; subst hp
      exact ⟨⟨f k, hfk_PA, hcl_ck⟩, ⟨f (k + 1), hfk1_PB, hcl_ck1⟩⟩
  exact ⟨PA.edges, PB.edges, hGeqAB, hDisjAB, hcls, hsegA, hsegB⟩

/-- HOL Light: `segment_superset_endpoint` (line 37817).
If E is a segment, S ⊆ E, k is an endpoint of S (numClosure 1), and
E \ S has no edges incident to k, then k is an endpoint of E. -/
theorem segment_superset_endpoint {G : Segment} {S : Finset (Set E2)} {k : ℤ × ℤ}
    (hSG : S ⊆ G.edges) (hk : numClosure S k = 1)
    (hDiff : numClosure (G.edges \ S) k = 0) :
    G.isEndpoint k := by
  change numClosure G.edges k = 1
  have h_eq : G.edges = S ∪ (G.edges \ S) := (Finset.union_sdiff_of_subset hSG).symm
  rw [h_eq, numClosure_disjoint_union disjoint_sdiff_self_right]
  omega

/-- HOL Light: `segment_end_union_lemma` (line 37836).
Chain two disjoint segments sharing exactly one endpoint. -/
theorem segment_end_union_lemma {A B : Finset (Set E2)} {a b c : ℤ × ℤ}
    (hA : segment_end A a b) (hB : segment_end B b c)
    (hDisj : Disjoint A B) (hCls : cls A ∩ cls B = {b}) :
    segment_end (A ∪ B) a c := by
  obtain ⟨GA, rfl, ha_ep, hb_ep_A, hab, huniqA⟩ := hA
  obtain ⟨GB, hEB, hb_ep_B, hc_ep, hbc, huniqB⟩ := hB
  have hDisj' : Disjoint GA.edges GB.edges := by rwa [hEB]
  have hShare : ∀ n, 0 < numClosure GA.edges n →
      0 < numClosure GB.edges n → n = b := by
    intro n hn1 hn2
    have h1 := cls_iff_numClosure_pos.mpr hn1
    have h2 := cls_iff_numClosure_pos.mpr hn2; rw [hEB] at h2
    exact Set.mem_singleton_iff.mp (hCls ▸ Set.mem_inter h1 h2)
  obtain ⟨G, hG⟩ := segment_union GA GB b hb_ep_A hb_ep_B hDisj' hShare
  -- a ≠ c
  have hac : a ≠ c := by
    intro h; subst h
    have ha_B : a ∈ cls B := by
      rw [← hEB]; exact cls_iff_numClosure_pos.mpr (by rw [hc_ep]; omega)
    have ha_A : a ∈ cls GA.edges := cls_iff_numClosure_pos.mpr (by rw [ha_ep]; omega)
    exact hab (Set.mem_singleton_iff.mp (hCls ▸ Set.mem_inter ha_A ha_B))
  -- a endpoint of G
  have ha_G : G.isEndpoint a := by
    change numClosure G.edges a = 1; rw [hG, numClosure_disjoint_union hDisj']
    have : numClosure GB.edges a = 0 := by
      rw [numClosure_eq_zero_iff]; intro e he hcl
      have hB : a ∈ cls B := by rw [← hEB]; exact ⟨e, he, hcl⟩
      have hA : a ∈ cls GA.edges := cls_iff_numClosure_pos.mpr (by rw [ha_ep]; omega)
      exact hab (Set.mem_singleton_iff.mp (hCls ▸ Set.mem_inter hA hB))
    have : numClosure GA.edges a = 1 := ha_ep; omega
  -- c endpoint of G
  have hc_G : G.isEndpoint c := by
    change numClosure G.edges c = 1; rw [hG, numClosure_disjoint_union hDisj']
    have : numClosure GA.edges c = 0 := by
      rw [numClosure_eq_zero_iff]; intro e he hcl
      have hA : c ∈ cls GA.edges := ⟨e, he, hcl⟩
      have hB : c ∈ cls B := by
        rw [← hEB]; exact cls_iff_numClosure_pos.mpr (by rw [hc_ep]; omega)
      exact hbc.symm (Set.mem_singleton_iff.mp (hCls ▸ Set.mem_inter hA hB))
    have : numClosure GB.edges c = 1 := hc_ep; omega
  -- uniqueness of endpoints
  have huniq : ∀ k, G.isEndpoint k → k = a ∨ k = c := by
    intro k hk
    rw [show G.isEndpoint k ↔ numClosure G.edges k = 1 from Iff.rfl,
      hG, numClosure_disjoint_union hDisj'] at hk
    have hGA := GA.degree_bound k; have hGB := GB.degree_bound k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hGA hGB
    rcases hGA with h0 | h1 | h2
    · -- GA has 0 edges at k, so GB has 1
      right; rcases huniqB k (show GB.isEndpoint k by change numClosure GB.edges k = 1; omega)
        with hkb | hkc
      · exfalso; rw [hkb] at h0
        have : numClosure GA.edges b = 1 := hb_ep_A; omega
      · exact hkc
    · -- GA has 1 edge at k, so GB has 0
      left; rcases huniqA k (show GA.isEndpoint k from h1) with hka | hkb
      · exact hka
      · exfalso; rw [hkb] at hk h1
        have : numClosure GB.edges b = 1 := hb_ep_B; omega
    · omega -- 2 + anything ≠ 1 in ℕ
  exact ⟨G, by rw [hG, hEB], ha_G, hc_G, hac, huniq⟩

/-- HOL Light: `segment_end_union` (line 37967).
Chain two segments sharing exactly one closure point (disjointness not required). -/
theorem segment_end_union {A B : Finset (Set E2)} {a b c : ℤ × ℤ}
    (hA : segment_end A a b) (hB : segment_end B b c)
    (hCls : cls A ∩ cls B = {b}) :
    segment_end (A ∪ B) a c := by
  have hDisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u hu_A hu_B
    obtain ⟨GA, hGA, _, _, _, _⟩ := hA
    have he := GA.all_edges u (by rw [hGA]; exact hu_A)
    have hmem : ∀ m, pointI m ∈ closure u → m = b := by
      intro m hm
      have : m ∈ cls A ∩ cls B := ⟨⟨u, hu_A, hm⟩, ⟨u, hu_B, hm⟩⟩
      rw [hCls, Set.mem_singleton_iff] at this; exact this
    rcases he with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have h1 := hmem n ((pointI_mem_closure_hEdge n n).mpr ⟨rfl, Or.inl rfl⟩)
      have h2 := hmem (n.1 + 1, n.2)
        ((pointI_mem_closure_hEdge (n.1 + 1, n.2) n).mpr ⟨rfl, Or.inr rfl⟩)
      have := congr_arg Prod.fst h1; have := congr_arg Prod.fst h2; omega
    · have h1 := hmem n ((pointI_mem_closure_vEdge n n).mpr ⟨rfl, Or.inl rfl⟩)
      have h2 := hmem (n.1, n.2 + 1)
        ((pointI_mem_closure_vEdge (n.1, n.2 + 1) n).mpr ⟨rfl, Or.inr rfl⟩)
      have := congr_arg Prod.snd h1; have := congr_arg Prod.snd h2; omega
  exact segment_end_union_lemma hA hB hDisj hCls

/-- HOL Light: `segment_end_trans` (line 38017).
Transitivity: segments a↔b and b↔c with a ≠ c give a segment a↔c in their union. -/
theorem segment_end_trans {R S : Finset (Set E2)} {a b c : ℤ × ℤ}
    (hR : segment_end R a b) (hS : segment_end S b c) (hac : a ≠ c) :
    ∃ U ⊆ R ∪ S, segment_end U a c := by
  -- Strong induction on R'.card + S'.card
  set T := R ∪ S with hT_def
  suffices h : ∀ n, ∀ (R' S' : Finset (Set E2)) (b' : ℤ × ℤ),
      R'.card + S'.card = n → R' ⊆ T → S' ⊆ T →
      segment_end R' a b' → segment_end S' b' c →
      ∃ U ⊆ T, segment_end U a c by
    exact h _ R S b rfl Finset.subset_union_left Finset.subset_union_right hR hS
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro R' S' b' hn hR'T hS'T hR' hS'
    -- Check if cls R' ∩ cls S' = {b'}
    by_cases hcls : cls R' ∩ cls S' = {b'}
    · -- Direct case: use segment_end_union
      exact ⟨R' ∪ S', Finset.union_subset hR'T hS'T, segment_end_union hR' hS' hcls⟩
    · -- There exists u ∈ cls R' ∩ cls S' with u ≠ b'
      have hb'_mem : b' ∈ cls R' ∩ cls S' :=
        Set.mem_inter (segment_end_cls2 hR') (segment_end_cls hS')
      have ⟨u, hu_mem, hu_ne⟩ : ∃ u ∈ cls R' ∩ cls S', u ≠ b' := by
        by_contra h'; push Not at h'
        exact hcls (Set.eq_singleton_iff_unique_mem.mpr ⟨hb'_mem, h'⟩)
      have hu_R' : u ∈ cls R' := hu_mem.1
      have hu_S' : u ∈ cls S' := hu_mem.2
      by_cases hau : u = a
      · -- u = a: a ∈ cls S'. Cut S' at a to extract segment a→c.
        subst hau
        obtain ⟨_, SB, _, _, _, _, hSB_seg⟩ :=
          cut_psegment hS' hu_S' hu_ne hac
        exact ⟨SB, (show SB ⊆ S' by rw [‹S' = _›]; exact Finset.subset_union_right).trans hS'T,
          hSB_seg⟩
      · by_cases hcu : u = c
        · -- u = c: c ∈ cls R'. Cut R' at c to extract segment a→c.
          subst hcu
          obtain ⟨RA, _, _, _, _, hRA_seg, _⟩ :=
            cut_psegment hR' hu_R' hau hu_ne
          exact ⟨RA,
            (show RA ⊆ R' by rw [‹R' = _›]; exact Finset.subset_union_left).trans hR'T,
            hRA_seg⟩
        · -- u ≠ a, u ≠ b', u ≠ c. Cut both R' and S' at u, apply IH.
          obtain ⟨RA, RB, hR'eq, hRDis, _, hRA_seg, hRB_seg⟩ :=
            cut_psegment hR' hu_R' hau hu_ne
          obtain ⟨SA, SB, hS'eq, hSDis, _, _, hSB_seg⟩ :=
            cut_psegment hS' hu_S' hu_ne hcu
          -- RA.card + SB.card < R'.card + S'.card = n
          have hRA_lt : RA.card < R'.card := by
            rw [hR'eq, Finset.card_union_of_disjoint hRDis]
            have : 0 < RB.card := Finset.card_pos.mpr (segment_end_finite hRB_seg)
            omega
          have hSB_lt : SB.card < S'.card := by
            rw [hS'eq, Finset.card_union_of_disjoint hSDis]
            have : 0 < SA.card := Finset.card_pos.mpr (segment_end_finite ‹segment_end SA b' u›)
            omega
          exact ih (RA.card + SB.card) (by omega) RA SB u rfl
            ((show RA ⊆ R' by rw [hR'eq]; exact Finset.subset_union_left).trans hR'T)
            ((show SB ⊆ S' by rw [hS'eq]; exact Finset.subset_union_right).trans hS'T)
            hRA_seg hSB_seg

/-- HOL Light: `segment_end_union_rectagon` (line 38985).
Two disjoint segments with the same pair of endpoints form a rectagon. -/
theorem segment_end_union_rectagon {A B : Finset (Set E2)} {m p : ℤ × ℤ}
    (hA : segment_end A m p) (hB : segment_end B m p)
    (hDisj : Disjoint A B) (hCls : cls A ∩ cls B = {m, p}) :
    ∃ (G : Rectagon), G.edges = A ∪ B := by
  obtain ⟨GA, hGA, hAm, hAp, hmp, huniqA⟩ := hA
  obtain ⟨GB, hGB, hBm, hBp, _, huniqB⟩ := hB
  -- Extract numeric endpoint facts for omega
  have hAm_nc : numClosure GA.edges m = 1 := hAm
  have hAp_nc : numClosure GA.edges p = 1 := hAp
  have hBm_nc : numClosure GB.edges m = 1 := hBm
  have hBp_nc : numClosure GB.edges p = 1 := hBp
  have hDisj' : Disjoint GA.edges GB.edges := hGA ▸ hGB ▸ hDisj
  have hShare : ∀ n, (0 < numClosure GA.edges n ∧ 0 < numClosure GB.edges n) ↔
      (n = m ∨ n = p) := by
    intro n; constructor
    · intro ⟨h1, h2⟩
      have h1' : n ∈ cls A := by rw [← hGA]; exact cls_iff_numClosure_pos.mpr h1
      have h2' : n ∈ cls B := by rw [← hGB]; exact cls_iff_numClosure_pos.mpr h2
      have hmem := hCls ▸ Set.mem_inter h1' h2'
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    · rintro (rfl | rfl)
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩
  obtain ⟨G, hG⟩ := segment_union_rectagon GA GB m p hmp hAm hBm hAp hBp hDisj' hShare
  exact ⟨G, by rw [hG, hGA, hGB]⟩

/-! ## §S.4 Closure set (cls) properties -/

/-- HOL Light: `cls_subset` (line 37937). -/
theorem cls_subset {A B : Finset (Set E2)} (h : A ⊆ B) : cls A ⊆ cls B := by
  intro m ⟨e, he, hcl⟩; exact ⟨e, h he, hcl⟩

/-- HOL Light: `cls_union` (line 38157). -/
theorem cls_union (A B : Finset (Set E2)) : cls (A ∪ B) = cls A ∪ cls B := by
  ext m; simp only [cls, Set.mem_setOf_eq, Finset.mem_union, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hcl⟩
    · left; exact ⟨e, he, hcl⟩
    · right; exact ⟨e, he, hcl⟩
  · rintro (⟨e, he, hcl⟩ | ⟨e, he, hcl⟩)
    · exact ⟨e, Or.inl he, hcl⟩
    · exact ⟨e, Or.inr he, hcl⟩

/-- HOL Light: `cls_empty` (line 38218). -/
theorem cls_empty : cls (∅ : Finset (Set E2)) = ∅ := by
  ext m; simp [cls]

/-- HOL Light: `finite_cls` (line 38226). -/
theorem finite_cls {E : Finset (Set E2)} (hE : ∀ e ∈ E, isEdge e) :
    Set.Finite (cls E) := by
  induction E using Finset.induction with
  | empty => rw [cls_empty]; exact Set.finite_empty
  | @insert a s has ih =>
    have h_eq : (insert a s : Finset (Set E2)) = {a} ∪ s := by
      ext; simp [Finset.mem_insert]
    rw [h_eq, cls_union]
    apply Set.Finite.union _ (ih (fun e he => hE e (Finset.mem_insert_of_mem he)))
    rw [cls_singleton]
    rcases hE a (Finset.mem_insert_self a s) with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · apply Set.Finite.subset (Set.toFinite {n, (n.1 + 1, n.2)})
      intro p hp; simp only [Set.mem_setOf_eq] at hp
      rw [pointI_mem_closure_hEdge] at hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      obtain ⟨h2, h1 | h1⟩ := hp
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2
    · apply Set.Finite.subset (Set.toFinite {n, (n.1, n.2 + 1)})
      intro p hp; simp only [Set.mem_setOf_eq] at hp
      rw [pointI_mem_closure_vEdge] at hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      obtain ⟨h1, h2 | h2⟩ := hp
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2

/-- HOL Light: `cls_h` (line 39022). -/
theorem cls_h (m : ℤ × ℤ) :
    cls ({hEdge m} : Finset (Set E2)) = {m, right m} := by
  ext p; simp only [cls_singleton, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, pointI_mem_closure_hEdge]
  constructor
  · rintro ⟨h2, h1 | h1⟩
    · left; exact Prod.ext h1 h2
    · right; unfold right; exact Prod.ext h1 h2
  · rintro (hp | hp)
    · subst hp; exact ⟨rfl, Or.inl rfl⟩
    · subst hp; simp [right]

/-- HOL Light: `cls_v` (line 39028). -/
theorem cls_v (m : ℤ × ℤ) :
    cls ({vEdge m} : Finset (Set E2)) = {m, up m} := by
  ext p; simp only [cls_singleton, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, pointI_mem_closure_vEdge]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · left; exact Prod.ext h1 h2
    · right; unfold up; exact Prod.ext h1 h2
  · rintro (hp | hp)
    · subst hp; exact ⟨rfl, Or.inl rfl⟩
    · subst hp; simp [up]

/-- HOL Light: `cls_edge_size2` (line 38377). -/
theorem cls_edge_size2 {e : Set E2} (he : isEdge e) :
    (cls ({e} : Finset (Set E2))).ncard = 2 := by
  rcases he with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [cls_h]; exact Set.ncard_pair (by
      unfold right; intro h; exact absurd (congr_arg Prod.fst h) (by omega))
  · rw [cls_v]; exact Set.ncard_pair (by
      unfold up; intro h; exact absurd (congr_arg Prod.snd h) (by omega))

/-! ## §S.5 Cardinality and finiteness -/

/-- HOL Light: `card_subset_lt` (line 38003).
Proper subset of a finite set has strictly smaller cardinality. -/
theorem card_subset_lt {α : Type*} {A B : Finset α} (hAB : A ⊆ B) (hne : A ≠ B) :
    A.card < B.card :=
  Finset.card_lt_card ⟨hAB, fun h => hne (Finset.Subset.antisymm hAB h)⟩

/-- HOL Light: `infinite_int` (line 38253). -/
theorem infinite_int : Infinite ℤ := inferInstance

/-- HOL Light: `infinite_intpair` (line 38261). -/
theorem infinite_intpair : Infinite (ℤ × ℤ) := inferInstance

/-- HOL Light: `not_cls_exists` (line 38271).
For any finite edge set, there exists a lattice point not in its closure. -/
theorem not_cls_exists {E : Finset (Set E2)} (hE : ∀ e ∈ E, isEdge e) :
    ∃ c, c ∉ cls E := by
  by_contra h; push Not at h
  have : cls E = Set.univ := Set.eq_univ_of_forall h
  exact absurd (this ▸ finite_cls hE) Set.infinite_univ.not_finite

/-- HOL Light: `has_size1` (line 38298). -/
theorem has_size1 {α : Type*} {X : Finset α} : X.card = 1 ↔ ∃ a, X = {a} :=
  Finset.card_eq_one

/-- HOL Light: `card_has_subset` (line 38354). -/
theorem card_has_subset {α : Type*} {A : Finset α} {n : ℕ}
    (hn : n ≤ A.card) : ∃ B ⊆ A, B.card = n := by
  classical
  induction n with
  | zero => exact ⟨∅, Finset.empty_subset A, Finset.card_empty⟩
  | succ k ih =>
    obtain ⟨B, hBA, hBk⟩ := ih (Nat.le_of_succ_le hn)
    have hne : B ≠ A := by intro h; subst h; omega
    obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
      by_contra h; push Not at h
      exact hne (Finset.Subset.antisymm hBA h)
    exact ⟨insert a B, Finset.insert_subset_iff.mpr ⟨haA, hBA⟩,
      by rw [Finset.card_insert_of_notMem haB, hBk]⟩

/-- HOL Light: `card_gt_3` (line 38310). -/
theorem card_gt_3 {α : Type*} {X : Finset α} :
    3 ≤ X.card ↔ ∃ a b c, a ∈ X ∧ b ∈ X ∧ c ∈ X ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  constructor
  · intro h
    obtain ⟨Y, hYX, hY⟩ := card_has_subset h
    rw [Finset.card_eq_three] at hY
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hY
    refine ⟨a, b, c, hYX (Finset.mem_insert_self a _), ?_, ?_, hab, hac, hbc⟩
    · exact hYX (Finset.mem_insert_of_mem (Finset.mem_insert_self b {c}))
    · exact hYX (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self c)))
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
    have hsub : ({a, b, c} : Finset _) ⊆ X :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hb,
        Finset.singleton_subset_iff.mpr hc⟩⟩
    have hcard : ({a, b, c} : Finset _).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]),
          Finset.card_singleton]
    linarith [Finset.card_le_card hsub]

/-- HOL Light: `has_size2_subset_ne` (line 38450).
A set of ncard 2 containing {a,b} with a ≠ b must equal {a,b}. -/
theorem has_size2_subset_ne {X : Set (ℤ × ℤ)} {a b : ℤ × ℤ}
    (hX : X.ncard = 2) (hab : a ≠ b) (ha : a ∈ X) (hb : b ∈ X) :
    X = {a, b} := by
  have hfin : X.Finite := by
    by_contra h; rw [Set.not_finite] at h
    simp [Set.Infinite.ncard h] at hX
  have hsub : ({a, b} : Set _) ⊆ X :=
    Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩
  have hcard_sub : ({a, b} : Set _).ncard = 2 := Set.ncard_pair hab
  exact ((Set.subset_iff_eq_of_ncard_le (by omega) hfin).mp hsub).symm

/-! ## §S.6 Connectivity theorems -/

/-- HOL Light: `conn_union` (line 38165). -/
theorem conn_union {E E' : Finset (Set E2)}
    (hE : conn E) (hE' : conn E') (hcls : (cls E ∩ cls E').Nonempty) :
    conn (E ∪ E') := by
  obtain ⟨u, hu_E, hu_E'⟩ := hcls
  intro a b ha hb hab
  rw [cls_union] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · -- Both in cls E
    obtain ⟨S, hSE, hSeg⟩ := hE a b ha hb hab
    exact ⟨S, hSE.trans Finset.subset_union_left, hSeg⟩
  · -- a ∈ cls E, b ∈ cls E'
    by_cases hau : a = u
    · subst hau
      obtain ⟨S, hSE', hSeg⟩ := hE' a b hu_E' hb hab
      exact ⟨S, hSE'.trans Finset.subset_union_right, hSeg⟩
    · by_cases hbu : b = u
      · subst hbu
        obtain ⟨S, hSE, hSeg⟩ := hE a b ha hu_E hab
        exact ⟨S, hSE.trans Finset.subset_union_left, hSeg⟩
      · obtain ⟨S₁, hS₁E, hS₁seg⟩ := hE a u ha hu_E hau
        obtain ⟨S₂, hS₂E', hS₂seg⟩ := hE' u b hu_E' hb (Ne.symm hbu)
        obtain ⟨U, hU, hUseg⟩ := segment_end_trans hS₁seg hS₂seg hab
        exact ⟨U, hU.trans (Finset.union_subset_union hS₁E hS₂E'), hUseg⟩
  · -- a ∈ cls E', b ∈ cls E (symmetric)
    by_cases hau : a = u
    · subst hau
      obtain ⟨S, hSE, hSeg⟩ := hE a b hu_E hb hab
      exact ⟨S, hSE.trans Finset.subset_union_left, hSeg⟩
    · by_cases hbu : b = u
      · subst hbu
        obtain ⟨S, hSE', hSeg⟩ := hE' a b ha hu_E' hab
        exact ⟨S, hSE'.trans Finset.subset_union_right, hSeg⟩
      · obtain ⟨S₁, hS₁E', hS₁seg⟩ := hE' a u ha hu_E' hau
        obtain ⟨S₂, hS₂E, hS₂seg⟩ := hE u b hu_E hb (Ne.symm hbu)
        obtain ⟨U, hU, hUseg⟩ := segment_end_trans hS₁seg hS₂seg hab
        exact ⟨U, hU.trans (Finset.union_subset
          (hS₁E'.trans Finset.subset_union_right)
          (hS₂E.trans Finset.subset_union_left)), hUseg⟩
  · -- Both in cls E'
    obtain ⟨S, hSE', hSeg⟩ := hE' a b ha hb hab
    exact ⟨S, hSE'.trans Finset.subset_union_right, hSeg⟩

/-- HOL Light: `conn2_imp_conn` (line 38285). -/
theorem conn2_imp_conn {E : Finset (Set E2)} (hE : ∀ e ∈ E, isEdge e) (hc : conn2 E) :
    conn E := by
  obtain ⟨_, hconn2⟩ := hc
  obtain ⟨c, hc_not⟩ := not_cls_exists hE
  intro a b ha hb hab
  obtain ⟨S, hSE, hSeg, _⟩ := hconn2 a b c ha hb hab
    (fun h => hc_not (h ▸ hb)) (fun h => hc_not (h ▸ ha))
  exact ⟨S, hSE, hSeg⟩

/-- HOL Light: `conn2_cls3` (line 38385). -/
theorem conn2_cls3 {E : Finset (Set E2)} (hE : ∀ e ∈ E, isEdge e) (hc : conn2 E) :
    3 ≤ (cls E).ncard := by
  obtain ⟨hcard, _⟩ := hc
  -- Find two distinct edges
  obtain ⟨B, hBE, hBcard⟩ := card_has_subset hcard
  rw [Finset.card_eq_two] at hBcard
  obtain ⟨a, b, hab, rfl⟩ := hBcard
  have haE := hBE (Finset.mem_insert_self a {b})
  have hbE := hBE (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have ha_edge := hE a haE; have hb_edge := hE b hbE
  have hca := cls_edge_size2 ha_edge
  have hcb := cls_edge_size2 hb_edge
  have ha_sub := cls_subset (show ({a} : Finset _) ⊆ E from Finset.singleton_subset_iff.mpr haE)
  have hb_sub := cls_subset (show ({b} : Finset _) ⊆ E from Finset.singleton_subset_iff.mpr hbE)
  have hne : cls ({a} : Finset _) ≠ cls ({b} : Finset _) :=
    fun h => hab (cls_injective a b ha_edge hb_edge h)
  have hfin := finite_cls hE
  -- Extract elements from 2-element sets
  rw [Set.ncard_eq_two] at hca hcb
  obtain ⟨x, y, hxy, hca_eq⟩ := hca
  obtain ⟨u, v, huv, hcb_eq⟩ := hcb
  -- Membership helpers
  have hx_mem : x ∈ cls ({a} : Finset _) := by rw [hca_eq]; exact Set.mem_insert x {y}
  have hy_mem : y ∈ cls ({a} : Finset _) := by rw [hca_eq]; exact Set.mem_insert_of_mem x rfl
  have hu_mem : u ∈ cls ({b} : Finset _) := by rw [hcb_eq]; exact Set.mem_insert u {v}
  have hv_mem : v ∈ cls ({b} : Finset _) := by rw [hcb_eq]; exact Set.mem_insert_of_mem u rfl
  -- Find an element in cls {b} not in cls {a}
  have h_diff : ∃ w, w ∈ cls ({b} : Finset _) ∧ w ∉ cls ({a} : Finset _) := by
    by_contra h; push Not at h
    have hsub : cls ({b} : Finset _) ⊆ cls ({a} : Finset _) := fun z hz => h z hz
    have hca_2 : (cls ({a} : Finset _)).ncard = 2 := by rw [hca_eq]; exact Set.ncard_pair hxy
    exact hne ((has_size2_subset_ne hca_2 huv (hsub hu_mem) (hsub hv_mem)).trans hcb_eq.symm)
  obtain ⟨w, hw_b, hw_a⟩ := h_diff
  -- x, y, w are 3 distinct elements of cls E
  have hxE := ha_sub hx_mem
  have hyE := ha_sub hy_mem
  have hwE := hb_sub hw_b
  have hxw : x ≠ w := fun h => hw_a (h ▸ hx_mem)
  have hyw : y ≠ w := fun h => hw_a (h ▸ hy_mem)
  -- {x, y, w} ⊆ cls E has ncard ≥ 3
  have h3 : ({x, y, w} : Set _).ncard = 3 := by
    have hw_notin : w ∉ ({x, y} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hxw, Ne.symm hyw⟩
    have h_eq : ({x, y, w} : Set (ℤ × ℤ)) = insert w {x, y} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, Set.ncard_insert_of_notMem hw_notin, Set.ncard_pair hxy]
  calc (cls E).ncard
      ≥ ({x, y, w} : Set _).ncard := Set.ncard_le_ncard
          (Set.insert_subset hxE (Set.insert_subset hyE (Set.singleton_subset_iff.mpr hwE))) hfin
    _ = 3 := h3

/-- HOL Light: `conn2_no1` (line 38482).
In a conn2 set, no lattice point has degree 1. -/
theorem conn2_no1 {E : Finset (Set E2)} (hE : ∀ e ∈ E, isEdge e) (hc : conn2 E)
    (m : ℤ × ℤ) : numClosure E m ≠ 1 := by
  intro hm1
  -- m has exactly one edge e through it
  rw [numClosure_eq_one_iff] at hm1
  obtain ⟨e, ⟨he, hcl_e⟩, huniq_e⟩ := hm1
  -- cls {e} has 2 elements, giving another vertex n on e
  have he_edge := hE e he
  have hce := cls_edge_size2 he_edge
  rw [Set.ncard_eq_two] at hce
  obtain ⟨p, q, hpq, hce_eq⟩ := hce
  -- Find which of p, q is m
  have hm_cls : m ∈ cls ({e} : Finset _) := ⟨e, Finset.mem_singleton_self e, hcl_e⟩
  rw [hce_eq] at hm_cls
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_cls
  have hp_mem : p ∈ cls ({e} : Finset _) := by rw [hce_eq]; exact Set.mem_insert p {q}
  have hq_mem : q ∈ cls ({e} : Finset _) := by rw [hce_eq]; exact Set.mem_insert_of_mem p rfl
  -- n is the other vertex
  obtain ⟨n, hn_cls_e, hmn⟩ : ∃ n, n ∈ cls ({e} : Finset _) ∧ m ≠ n := by
    rcases hm_cls with hmp | hmq
    · exact ⟨q, hq_mem, hmp ▸ hpq⟩
    · exact ⟨p, hp_mem, hmq ▸ hpq.symm⟩
  have hn_E := cls_subset (Finset.singleton_subset_iff.mpr he : ({e} : Finset _) ⊆ E) hn_cls_e
  have hm_E : m ∈ cls E := ⟨e, he, hcl_e⟩
  -- Find a third vertex c ≠ m, c ≠ n using conn2_cls3
  have h3 := conn2_cls3 hE hc
  have hfin := finite_cls hE
  have hpair_sub : ({m, n} : Set _) ⊆ cls E :=
    Set.insert_subset hm_E (Set.singleton_subset_iff.mpr hn_E)
  obtain ⟨c, hc_E, hc_nm⟩ : ∃ c ∈ cls E, c ∉ ({m, n} : Set _) := by
    by_contra h; push Not at h
    have : cls E = {m, n} := Set.Subset.antisymm h hpair_sub
    rw [this, Set.ncard_pair hmn] at h3; omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc_nm
  -- Use conn2 to find S ⊆ E with segment_end S m c, n ∉ cls S
  obtain ⟨_, hconn2⟩ := hc
  obtain ⟨S, hSE, hSeg, hn_not⟩ := hconn2 m c n hm_E hc_E
    (Ne.symm hc_nm.1) hc_nm.2 hmn
  -- S has an edge through m (from segment_end_cls)
  obtain ⟨es, hes, hcl_es⟩ := segment_end_cls hSeg
  -- Since numClosure E m = 1 and es ∈ S ⊆ E, es = e
  have hes_eq : es = e := huniq_e es ⟨hSE hes, hcl_es⟩
  -- So e ∈ S, so cls {e} ⊆ cls S, so n ∈ cls S — contradiction!
  have he_in_S : e ∈ S := by rwa [← hes_eq]
  exact hn_not (cls_subset (Finset.singleton_subset_iff.mpr he_in_S :
    ({e} : Finset _) ⊆ S) hn_cls_e)

/-- HOL Light: `conn2_union` (line 38594).
Union of two conn2 sets sharing ≥2 closure points is conn2. -/
theorem conn2_union {A B : Finset (Set E2)}
    (_hA : ∀ e ∈ A, isEdge e) (_hB : ∀ e ∈ B, isEdge e)
    (hcA : conn2 A) (hcB : conn2 B)
    (h : ∃ a b, a ≠ b ∧ a ∈ cls A ∩ cls B ∧ b ∈ cls A ∩ cls B) :
    conn2 (A ∪ B) := by
  obtain ⟨a₀, b₀, hab₀, ⟨ha₀A, ha₀B⟩, ⟨hb₀A, hb₀B⟩⟩ := h
  refine ⟨?_, ?_⟩
  · -- 2 ≤ (A ∪ B).card
    calc 2 ≤ A.card := hcA.1
      _ ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_left
  · intro a' b' c ha' hb' hab' hbc' hac'
    rw [cls_union] at ha' hb'
    -- Helper to find a shared point d ≠ c
    have hd_exists : ∃ d, d ∈ cls A ∧ d ∈ cls B ∧ d ≠ c := by
      by_cases hca₀ : c = a₀
      · exact ⟨b₀, hb₀A, hb₀B, by subst hca₀; exact Ne.symm hab₀⟩
      · exact ⟨a₀, ha₀A, ha₀B, Ne.symm hca₀⟩
    rcases ha' with ha'A | ha'B
    · -- a' ∈ cls A
      rcases hb' with hb'A | hb'B
      · -- Both in cls A
        obtain ⟨S, hSA, hSeg, hcS⟩ := hcA.2 a' b' c ha'A hb'A hab' hbc' hac'
        exact ⟨S, hSA.trans Finset.subset_union_left, hSeg, hcS⟩
      · -- a' ∈ cls A, b' ∈ cls B
        obtain ⟨d, hdA, hdB, hdc⟩ := hd_exists
        by_cases had : a' = d
        · subst had
          obtain ⟨S, hSB, hSeg, hcS⟩ := hcB.2 a' b' c hdB hb'B hab' hbc' hac'
          exact ⟨S, hSB.trans Finset.subset_union_right, hSeg, hcS⟩
        · by_cases hbd : b' = d
          · subst hbd
            obtain ⟨S, hSA, hSeg, hcS⟩ :=
              hcA.2 a' b' c ha'A hdA hab' hdc hac'
            exact ⟨S, hSA.trans Finset.subset_union_left, hSeg, hcS⟩
          · obtain ⟨SA, hSAA, hSAseg, hcSA⟩ :=
              hcA.2 a' d c ha'A hdA had hdc hac'
            obtain ⟨SB, hSBB, hSBseg, hcSB⟩ :=
              hcB.2 d b' c hdB hb'B (Ne.symm hbd) hbc' hdc
            obtain ⟨U, hU, hUseg⟩ := segment_end_trans hSAseg hSBseg hab'
            refine ⟨U, hU.trans (Finset.union_subset_union hSAA hSBB),
              hUseg, fun hcU => ?_⟩
            have := cls_subset hU hcU
            rw [cls_union] at this; exact this.elim hcSA hcSB
    · -- a' ∈ cls B
      rcases hb' with hb'A | hb'B
      · -- a' ∈ cls B, b' ∈ cls A
        obtain ⟨d, hdA, hdB, hdc⟩ := hd_exists
        by_cases had : a' = d
        · subst had
          obtain ⟨S, hSA, hSeg, hcS⟩ :=
            hcA.2 a' b' c hdA hb'A hab' hbc' hac'
          exact ⟨S, hSA.trans Finset.subset_union_left, hSeg, hcS⟩
        · by_cases hbd : b' = d
          · subst hbd
            obtain ⟨S, hSB, hSeg, hcS⟩ :=
              hcB.2 a' b' c ha'B hdB hab' hdc hac'
            exact ⟨S, hSB.trans Finset.subset_union_right, hSeg, hcS⟩
          · obtain ⟨SB, hSBB, hSBseg, hcSB⟩ :=
              hcB.2 a' d c ha'B hdB had hdc hac'
            obtain ⟨SA, hSAA, hSAseg, hcSA⟩ :=
              hcA.2 d b' c hdA hb'A (Ne.symm hbd) hbc' hdc
            obtain ⟨U, hU, hUseg⟩ := segment_end_trans hSBseg hSAseg hab'
            refine ⟨U, hU.trans (Finset.union_subset
              (hSBB.trans Finset.subset_union_right)
              (hSAA.trans Finset.subset_union_left)),
              hUseg, fun hcU => ?_⟩
            have := cls_subset hU hcU
            rw [cls_union] at this; exact this.elim hcSB hcSA
      · -- Both in cls B
        obtain ⟨S, hSB, hSeg, hcS⟩ :=
          hcB.2 a' b' c ha'B hb'B hab' hbc' hac'
        exact ⟨S, hSB.trans Finset.subset_union_right, hSeg, hcS⟩

/-- HOL Light: `conn2_union_edge` (line 39154).
Union of two conn2 sets that share an edge is conn2. -/
theorem conn2_union_edge {A B : Finset (Set E2)}
    (hA : ∀ e ∈ A, isEdge e) (hB : ∀ e ∈ B, isEdge e)
    (hcA : conn2 A) (hcB : conn2 B)
    (hne : (A ∩ B).Nonempty) :
    conn2 (A ∪ B) := by
  obtain ⟨u, hu⟩ := hne
  have huA : u ∈ A := Finset.mem_inter.mp hu |>.1
  have huB : u ∈ B := Finset.mem_inter.mp hu |>.2
  have he : isEdge u := hA u huA
  -- cls {u} has 2 elements
  have hsize := cls_edge_size2 he
  rw [Set.ncard_eq_two] at hsize
  obtain ⟨a, b, hab, hcls_eq⟩ := hsize
  have ha_cls : a ∈ cls ({u} : Finset _) := by rw [hcls_eq]; exact Set.mem_insert a {b}
  have hb_cls : b ∈ cls ({u} : Finset _) := by rw [hcls_eq]; exact Set.mem_insert_of_mem a rfl
  have ha_A : a ∈ cls A := cls_subset (Finset.singleton_subset_iff.mpr huA) ha_cls
  have hb_A : b ∈ cls A := cls_subset (Finset.singleton_subset_iff.mpr huA) hb_cls
  have ha_B : a ∈ cls B := cls_subset (Finset.singleton_subset_iff.mpr huB) ha_cls
  have hb_B : b ∈ cls B := cls_subset (Finset.singleton_subset_iff.mpr huB) hb_cls
  exact conn2_union hA hB hcA hcB ⟨a, b, hab, ⟨ha_A, ha_B⟩, ⟨hb_A, hb_B⟩⟩

/-! ## §S.7 Cutting rectagons (closure version) -/

/-- HOL Light: `cut_rectagon_cls` (line 38757).
Any rectagon splits at two distinct closure points into two disjoint segments. -/
theorem cut_rectagon_cls (G : Rectagon) {m n : ℤ × ℤ} (hmn : m ≠ n)
    (hm : m ∈ cls G.edges) (hn : n ∈ cls G.edges) :
    ∃ A B : Finset (Set E2), segment_end A m n ∧ segment_end B m n ∧
      G.edges = A ∪ B ∧ Disjoint A B ∧ cls A ∩ cls B = {m, n} := by
  -- Get edge touching m and cyclic ordering
  obtain ⟨em, hem, hcl_m⟩ := hm
  obtain ⟨f, hfmem, hfinj, hfsurj, hflast, hfcl0, hfadj⟩ :=
    G.cyclic_order em m hem hcl_m
  set N := G.edges.card with hN_def
  have hN2 : 2 ≤ N := by
    have := G.not_singleton; have := G.nonempty.card_pos; omega
  have hfedge : ∀ i, i < N → isEdge (f i) := fun i hi => G.all_edges _ (hfmem i hi)
  -- m is on f(0) and f(N-1)
  have hcl_m_last : pointI m ∈ closure (f (N - 1)) := hflast ▸ hcl_m
  have hwrap_adj : cellAdj (f (N - 1)) (f 0) :=
    (hfadj (N - 1) 0 (by omega) (by omega)).mpr
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  -- Degree of n is 2
  have hn_deg : numClosure G.edges n = 2 := by
    have hd := G.even_degree n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    have := cls_iff_numClosure_pos.mp hn; omega
  -- Find the two edges through n and their indices
  obtain ⟨en1, en2, hne12, hen1, hen2, hcl_n1, hcl_n2, _⟩ :=
    (numClosure_eq_two_iff G.edges n).mp hn_deg
  obtain ⟨j1, hj1lt, hfj1⟩ := hfsurj en1 hen1
  obtain ⟨j2, hj2lt, hfj2⟩ := hfsurj en2 hen2
  have hj12 : j1 ≠ j2 := fun h => hne12 (hfj1 ▸ hfj2 ▸ congrArg f h)
  have h_n1 : pointI n ∈ closure (f j1) := hfj1 ▸ hcl_n1
  have h_n2 : pointI n ∈ closure (f j2) := hfj2 ▸ hcl_n2
  -- These two edges are adjacent (share lattice point n)
  have hadj12 : cellAdj (f j1) (f j2) :=
    closure_imp_cellAdj _ _ n (isEdge_isCell (hfedge j1 hj1lt))
      (isEdge_isCell (hfedge j2 hj2lt)) h_n1 h_n2
      (fun h => hj12 (hfinj j1 j2 hj1lt hj2lt h))
  -- Find k s.t. f(k), f(k+1) both contain n, with k+1 < N
  -- (wrap-around case gives m = n via adjv_unique, contradiction)
  obtain ⟨k, hkN, hcl_nk, hcl_nk1⟩ :
      ∃ k, k + 1 < N ∧ pointI n ∈ closure (f k) ∧
        pointI n ∈ closure (f (k + 1)) := by
    have hcadj := (hfadj j1 j2 hj1lt hj2lt).mp hadj12
    have hwrap1 : ¬(j1 = 0 ∧ j2 = N - 1) := by
      rintro ⟨rfl, rfl⟩
      exact hmn ((adjv_unique _ _ m (hfedge _ (by omega)) (hfedge 0 (by omega))
        hwrap_adj hcl_m_last hfcl0).trans
        (adjv_unique _ _ n (hfedge _ (by omega)) (hfedge 0 (by omega))
          hwrap_adj h_n2 h_n1).symm)
    have hwrap2 : ¬(j1 = N - 1 ∧ j2 = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hmn ((adjv_unique _ _ m (hfedge _ (by omega)) (hfedge 0 (by omega))
        hwrap_adj hcl_m_last hfcl0).trans
        (adjv_unique _ _ n (hfedge _ (by omega)) (hfedge 0 (by omega))
          hwrap_adj h_n1 h_n2).symm)
    rcases hcadj with h | h | h | h
    · exact ⟨j1, by omega, h_n1, h ▸ h_n2⟩
    · exact ⟨j2, by omega, h_n2, h ▸ h_n1⟩
    · exact absurd h hwrap1
    · exact absurd h hwrap2
  -- Build psegments for each half of the cycle
  have hAdj_A : ∀ i j, i < k + 1 → j < k + 1 →
      (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj; constructor
    · intro hadj
      rcases (hfadj i j (by omega) (by omega)).mp hadj with h | h | ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · omega
      · omega
    · exact fun h => (hfadj i j (by omega) (by omega)).mpr
        (h.elim Or.inl fun h => Or.inr (Or.inl h))
  have hAdj_B : ∀ i j, k + 1 ≤ i → i < N → k + 1 ≤ j → j < N →
      (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hilo hihi hjlo hjhi; constructor
    · intro hadj
      rcases (hfadj i j hihi hjhi).mp hadj with h | h | ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · omega
      · omega
    · exact fun h => (hfadj i j hihi hjhi).mpr
        (h.elim Or.inl fun h => Or.inr (Or.inl h))
  obtain ⟨PA, hPAps, hPAedges⟩ := order_imp_psegment f (k + 1) (by omega)
    (fun i j hi hj => hfinj i j (by omega) (by omega))
    (fun i hi => hfedge i (by omega)) hAdj_A
  obtain ⟨PB, hPBps, hPBedges⟩ := order_imp_psegment_shift f (k + 1) N hkN
    (fun i j hilo hihi hjlo hjhi => hfinj i j hihi hjhi)
    (fun i _ hi => hfedge i hi) hAdj_B
  -- Subset, union, disjoint
  have hPA_sub : PA.edges ⊆ G.edges := by
    rw [hPAedges]; intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact hfmem i (by have := Finset.mem_range.mp hi; omega)
  have hGeqAB : G.edges = PA.edges ∪ PB.edges := by
    rw [hPAedges, hPBedges]; ext e
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro he; obtain ⟨i, hi, hfi⟩ := hfsurj e he
      by_cases h : i < k + 1
      · exact Or.inl ⟨i, h, hfi⟩
      · exact Or.inr ⟨i, ⟨by omega, hi⟩, hfi⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, ⟨_, hi⟩, rfl⟩) <;> exact hfmem i (by omega)
  have hDisjAB : Disjoint PA.edges PB.edges := by
    rw [hPAedges, hPBedges, Finset.disjoint_left]
    intro e he hbe
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, hfij⟩ := Finset.mem_image.mp hbe
    have := hfinj i j (by have := Finset.mem_range.mp hi; omega)
      (Finset.mem_Ico.mp hj).2 hfij.symm
    have := Finset.mem_range.mp hi; have := (Finset.mem_Ico.mp hj).1; omega
  have hEdiff : G.edges \ PA.edges = PB.edges := by
    ext e; simp only [Finset.mem_sdiff]; constructor
    · intro ⟨he, hna⟩
      rw [hGeqAB] at he; exact (Finset.mem_union.mp he).resolve_left hna
    · intro h
      refine ⟨?_, Finset.disjoint_left.mp hDisjAB.symm h⟩
      rw [hGeqAB]; exact Finset.mem_union.mpr (Or.inr h)
  -- Key membership facts
  have hf0_PA : f 0 ∈ PA.edges := by
    rw [hPAedges]; exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hfk_PA : f k ∈ PA.edges := by
    rw [hPAedges]; exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hfk1_PB : f (k + 1) ∈ PB.edges := by
    rw [hPBedges]
    exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_Ico.mpr ⟨le_refl _, hkN⟩, rfl⟩
  have hfN1_PB : f (N - 1) ∈ PB.edges := by
    rw [hPBedges]
    exact Finset.mem_image.mpr ⟨N - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  -- numClosure = 1 at m and n via Rectagon.subset_endpoint
  have hncA_m : numClosure PA.edges m = 1 :=
    G.subset_endpoint PA.edges m hPA_sub
      (cls_iff_numClosure_pos.mp ⟨f 0, hf0_PA, hfcl0⟩)
      (by rw [hEdiff]; exact cls_iff_numClosure_pos.mp ⟨f (N - 1), hfN1_PB, hcl_m_last⟩)
  have hncA_n : numClosure PA.edges n = 1 :=
    G.subset_endpoint PA.edges n hPA_sub
      (cls_iff_numClosure_pos.mp ⟨f k, hfk_PA, hcl_nk⟩)
      (by rw [hEdiff]; exact cls_iff_numClosure_pos.mp ⟨f (k + 1), hfk1_PB, hcl_nk1⟩)
  have hncB_m : numClosure PB.edges m = 1 := by
    have hadd := numClosure_disjoint_union hDisjAB m
    rw [← hGeqAB, hncA_m] at hadd
    have hd := G.even_degree m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd; omega
  have hncB_n : numClosure PB.edges n = 1 := by
    have hadd := numClosure_disjoint_union hDisjAB n
    rw [← hGeqAB, hncA_n] at hadd
    have hd := G.even_degree n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd; omega
  -- Endpoints
  have hPAm : PA.isEndpoint m := hncA_m
  have hPAn : PA.isEndpoint n := hncA_n
  have hPBm : PB.isEndpoint m := hncB_m
  have hPBn : PB.isEndpoint n := hncB_n
  -- segment_end
  have hsegA : segment_end PA.edges m n :=
    ⟨PA, rfl, hPAm, hPAn, hmn,
     fun q hq => PA.two_endpoint_bound n m hPAn hPAm hmn q hq⟩
  have hsegB : segment_end PB.edges m n :=
    ⟨PB, rfl, hPBm, hPBn, hmn,
     fun q hq => PB.two_endpoint_bound n m hPBn hPBm hmn q hq⟩
  -- cls PA.edges ∩ cls PB.edges = {m, n}
  have hcls : cls PA.edges ∩ cls PB.edges = {m, n} := by
    ext p; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hp_A, hp_B⟩
      have hpA := cls_iff_numClosure_pos.mp hp_A
      have hpB : 0 < numClosure (G.edges \ PA.edges) p := by
        rw [hEdiff]; exact cls_iff_numClosure_pos.mp hp_B
      exact PA.two_endpoint_bound n m hPAn hPAm hmn p
        (G.subset_endpoint PA.edges p hPA_sub hpA hpB)
    · rintro (rfl | rfl)
      · exact ⟨⟨f 0, hf0_PA, hfcl0⟩, ⟨f (N - 1), hfN1_PB, hcl_m_last⟩⟩
      · exact ⟨⟨f k, hfk_PA, hcl_nk⟩, ⟨f (k + 1), hfk1_PB, hcl_nk1⟩⟩
  exact ⟨PA.edges, PB.edges, hsegA, hsegB, hGeqAB, hDisjAB, hcls⟩

/-- HOL Light: `conn2_rectagon` (line 38826).
Every rectagon is 2-connected. -/
theorem conn2_rectagon (G : Rectagon) : conn2 G.edges := by
  refine ⟨?_, ?_⟩
  · -- 2 ≤ G.edges.card: find an hEdge and a vEdge
    obtain ⟨m, hm⟩ := G.has_h_edge
    obtain ⟨n, hn⟩ := G.has_v_edge
    calc 2 = ({hEdge m, vEdge n} : Finset (Set E2)).card := by
              rw [Finset.card_pair (hEdge_ne_vEdge m n)]
         _ ≤ G.edges.card := Finset.card_le_card
              (Finset.insert_subset_iff.mpr ⟨hm, Finset.singleton_subset_iff.mpr hn⟩)
  · -- For any a, b ∈ cls G.edges with a ≠ b, and c ≠ a, c ≠ b, find S ⊆ G.edges avoiding c
    intro a b c ha hb hab hbc hac
    obtain ⟨A, B, hsegA, hsegB, hGeqAB, hDisjAB, hcls⟩ := cut_rectagon_cls G hab ha hb
    by_cases hcA : c ∈ cls A
    · -- c ∈ cls A, so c ∉ cls B (since cls A ∩ cls B = {a, b} and c ≠ a, c ≠ b)
      have hcB : c ∉ cls B := by
        intro hcB
        have : c ∈ cls A ∩ cls B := ⟨hcA, hcB⟩
        rw [hcls] at this
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
        rcases this with rfl | rfl
        · exact hac rfl
        · exact hbc rfl
      exact ⟨B, hGeqAB ▸ Finset.subset_union_right, hsegB, hcB⟩
    · -- c ∉ cls A: take A
      exact ⟨A, hGeqAB ▸ Finset.subset_union_left, hsegA, hcA⟩

/-! ## §S.8 Rectangle grid -/

/-- HOL Light: `rectangle_grid_h` (line 38868). -/
theorem rectangle_grid_h (p q : ℤ × ℤ) (m : ℤ × ℤ) :
    hEdge m ∈ rectangle_grid p q ↔
      p.1 ≤ m.1 ∧ m.1 + 1 ≤ q.1 ∧ p.2 ≤ m.2 ∧ m.2 ≤ q.2 := by
  simp only [rectangle_grid, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · rintro (⟨n, ⟨⟨h1a, h1b⟩, h2a, h2b⟩, heq⟩ | ⟨n, _, heq⟩)
    · have := (hEdge_inj n m).mp heq; subst this
      exact ⟨h1a, by omega, h2a, h2b⟩
    · exact absurd heq.symm (hEdge_ne_vEdge m n)
  · rintro ⟨h1, h2, h3, h4⟩
    left; exact ⟨m, ⟨⟨h1, by omega⟩, h3, h4⟩, rfl⟩

/-- HOL Light: `rectangle_grid_v` (line 38878). -/
theorem rectangle_grid_v (p q : ℤ × ℤ) (m : ℤ × ℤ) :
    vEdge m ∈ rectangle_grid p q ↔
      p.1 ≤ m.1 ∧ m.1 ≤ q.1 ∧ p.2 ≤ m.2 ∧ m.2 + 1 ≤ q.2 := by
  simp only [rectangle_grid, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · rintro (⟨n, _, heq⟩ | ⟨n, ⟨⟨h1a, h1b⟩, h2a, h2b⟩, heq⟩)
    · exact absurd heq (hEdge_ne_vEdge n m)
    · have := (vEdge_inj n m).mp heq; subst this
      exact ⟨h1a, h1b, h2a, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    right; exact ⟨m, ⟨⟨h1, h2⟩, h3, by omega⟩, rfl⟩

/-- HOL Light: `rectangle_grid_edge` (line 38887). -/
theorem rectangle_grid_edge (p q : ℤ × ℤ) :
    ∀ e ∈ rectangle_grid p q, isEdge e := by
  intro e he
  simp only [rectangle_grid, Finset.mem_union, Finset.mem_image] at he
  rcases he with ⟨n, _, rfl⟩ | ⟨n, _, rfl⟩
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩


/-! ## §S.6 Unit square grid -/

/-- HOL Light: `rectangle_grid_sq` (line 38895).
The 1×1 grid is exactly the 4 edges of the unit square. -/
theorem rectangle_grid_sq (p : ℤ × ℤ) :
    rectangle_grid p (p.1 + 1, p.2 + 1) =
      {hEdge p, hEdge (up p), vEdge p, vEdge (right p)} := by
  ext e; constructor <;> intro he
  · rcases rectangle_grid_edge p (p.1 + 1, p.2 + 1) e he
      with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [rectangle_grid_h] at he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨h1, h2, h3, h4⟩ := he
      rcases show m.2 = p.2 ∨ m.2 = p.2 + 1 from by omega
        with h | h
      · left; congr 1; ext <;> omega
      · right; left; show hEdge m = hEdge (up p); congr 1
        ext <;> simp [up] <;> omega
    · rw [rectangle_grid_v] at he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨h1, h2, h3, h4⟩ := he
      rcases show m.1 = p.1 ∨ m.1 = p.1 + 1 from by omega
        with h | h
      · right; right; left; congr 1; ext <;> omega
      · right; right; right
        show vEdge m = vEdge (right p)
        congr 1; ext <;> simp [right] <;> omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · rw [rectangle_grid_h]
      exact ⟨le_refl _, by omega, le_refl _, by omega⟩
    · rw [rectangle_grid_h]; simp only [up]
      constructor <;> omega
    · rw [rectangle_grid_v]
      exact ⟨le_refl _, by omega, le_refl _, by omega⟩
    · rw [rectangle_grid_v]; simp only [right]
      constructor <;> omega

/-! ## §S.7 Closure of unit square grid -/

/-- HOL Light: `rectangle_grid_sq_cls` (line 38950).
Closure of the 1×1 grid is the 4 corner points. -/
theorem rectangle_grid_sq_cls (p : ℤ × ℤ) :
    cls (rectangle_grid p (p.1 + 1, p.2 + 1)) =
      {p, right p, up p, up (right p)} := by
  rw [rectangle_grid_sq]
  have h4 : ({hEdge p, hEdge (up p), vEdge p,
      vEdge (right p)} : Finset (Set E2)) =
      {hEdge p} ∪ ({hEdge (up p)} ∪
        ({vEdge p} ∪ {vEdge (right p)})) := by
    ext x; simp [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h4, cls_union, cls_union, cls_union,
    cls_h, cls_h, cls_v, cls_v]
  have hcomm : right (up p) = up (right p) := by
    ext <;> simp [up, right]
  ext m
  simp only [Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ((rfl | rfl) | (rfl | rfl) |
      (rfl | rfl) | rfl | rfl)
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ## §S.8 Unit square is a rectagon -/

/-- HOL Light: `rectagon_rectangle_grid_sq` (line 39034).
The 1×1 grid forms a rectagon. -/
theorem rectagon_rectangle_grid_sq (p : ℤ × ℤ) :
    ∃ (G : Rectagon),
      G.edges = rectangle_grid p (p.1 + 1, p.2 + 1) := by
  rw [rectangle_grid_sq]
  have hcl_h_p1 : pointI p ∈ closure (hEdge p) :=
    (pointI_mem_closure_hEdge p p).mpr ⟨rfl, Or.inl rfl⟩
  have hcl_h_p2 : pointI (right p) ∈ closure (hEdge p) :=
    (pointI_mem_closure_hEdge (right p) p).mpr
      ⟨by simp [right], Or.inr (by simp [right])⟩
  have hcl_v_p1 : pointI p ∈ closure (vEdge p) :=
    (pointI_mem_closure_vEdge p p).mpr ⟨rfl, Or.inl rfl⟩
  have hcl_v_p2 : pointI (up p) ∈ closure (vEdge p) :=
    (pointI_mem_closure_vEdge (up p) p).mpr
      ⟨by simp [up], Or.inr (by simp [up])⟩
  have hcl_hu_p1 :
      pointI (up p) ∈ closure (hEdge (up p)) :=
    (pointI_mem_closure_hEdge (up p) (up p)).mpr
      ⟨rfl, Or.inl rfl⟩
  have hcl_hu_p2 :
      pointI (up (right p)) ∈ closure (hEdge (up p)) :=
    (pointI_mem_closure_hEdge (up (right p)) (up p)).mpr
      ⟨by simp [up, right], Or.inr (by simp [up, right])⟩
  have hcl_vr_p1 :
      pointI (right p) ∈ closure (vEdge (right p)) :=
    (pointI_mem_closure_vEdge (right p) (right p)).mpr
      ⟨rfl, Or.inl rfl⟩
  have hcl_vr_p2 :
      pointI (up (right p)) ∈ closure (vEdge (right p)) :=
    (pointI_mem_closure_vEdge (up (right p)) (right p)).mpr
      ⟨by simp [up, right], Or.inr (by simp [up, right])⟩
  have hp_ne_rp : p ≠ right p := by
    simp [right, Prod.ext_iff]
  have hp_ne_up : p ≠ up p := by
    simp [up, Prod.ext_iff]
  have hup_ne_upr : up p ≠ up (right p) := by
    simp [up, right, Prod.ext_iff]
  have hrp_ne_upr : right p ≠ up (right p) := by
    simp [up, right, Prod.ext_iff]
  have seg_hp : segment_end {hEdge p} p (right p) :=
    segment_end_sing hcl_h_p1 hcl_h_p2 hp_ne_rp
      (Or.inl ⟨p, rfl⟩)
  have seg_vp : segment_end {vEdge p} p (up p) :=
    segment_end_sing hcl_v_p1 hcl_v_p2 hp_ne_up
      (Or.inr ⟨p, rfl⟩)
  have seg_hu :
      segment_end {hEdge (up p)} (up p) (up (right p)) :=
    segment_end_sing hcl_hu_p1 hcl_hu_p2 hup_ne_upr
      (Or.inl ⟨up p, rfl⟩)
  have seg_vr :
      segment_end {vEdge (right p)} (right p)
        (up (right p)) :=
    segment_end_sing hcl_vr_p1 hcl_vr_p2 hrp_ne_upr
      (Or.inr ⟨right p, rfl⟩)
  have hcls1 : cls ({vEdge p} : Finset _) ∩
      cls ({hEdge (up p)} : Finset _) = {up p} := by
    rw [cls_v, cls_h]; ext m
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      cases h1 with
      | inl h1 =>
        cases h2 with
        | inl h2 =>
          exact absurd (h1.symm.trans h2) hp_ne_up
        | inr h2 =>
          exact absurd (h1.symm.trans h2)
            (by simp [up, right, Prod.ext_iff])
      | inr h1 => exact h1
    · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
  have seg_left :
      segment_end ({vEdge p} ∪ {hEdge (up p)}) p
        (up (right p)) :=
    segment_end_union seg_vp seg_hu hcls1
  have hcls2 : cls ({hEdge p} : Finset _) ∩
      cls ({vEdge (right p)} : Finset _) = {right p} := by
    rw [cls_h, cls_v]; ext m
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      cases h1 with
      | inl h1 =>
        cases h2 with
        | inl h2 =>
          exact absurd (h1.symm.trans h2) hp_ne_rp
        | inr h2 =>
          exact absurd (h1.symm.trans h2)
            (by simp [up, right, Prod.ext_iff])
      | inr h1 => exact h1
    · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
  have seg_right :
      segment_end ({hEdge p} ∪ {vEdge (right p)}) p
        (up (right p)) :=
    segment_end_union seg_hp seg_vr hcls2
  have hDisj :
      Disjoint ({vEdge p} ∪ {hEdge (up p)} : Finset _)
        ({hEdge p} ∪ {vEdge (right p)}) := by
    rw [Finset.disjoint_left]; intro e he he'
    simp only [Finset.mem_union, Finset.mem_singleton]
      at he he'
    rcases he with rfl | rfl
    · rcases he' with h | h
      · exact absurd h (hEdge_ne_vEdge p p).symm
      · exact absurd ((vEdge_inj p (right p)).mp h)
          hp_ne_rp
    · rcases he' with h | h
      · exact absurd ((hEdge_inj (up p) p).mp h)
          (Ne.symm hp_ne_up)
      · exact absurd h
          (hEdge_ne_vEdge (up p) (right p))
  have hcomm : right (up p) = up (right p) := by
    ext <;> simp [up, right]
  have hClsInt :
      cls ({vEdge p} ∪ {hEdge (up p)} : Finset _) ∩
        cls ({hEdge p} ∪ {vEdge (right p)}) =
        {p, up (right p)} := by
    rw [cls_union, cls_union, cls_v, cls_h, cls_h, cls_v]
    ext m
    simp only [Set.mem_inter_iff, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with (h1 | h1) | h1 | h1 <;>
        rcases h2 with (h2 | h2) | h2 | h2 <;>
        first
        | exact Or.inl h1
        | exact Or.inl h2
        | exact Or.inr (h1.trans hcomm)
        | exact Or.inr h2
        | (exfalso;
           have := h1.symm.trans h2;
           simp [up, right, Prod.ext_iff] at this)
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (Or.inl rfl),
               Or.inl (Or.inl rfl)⟩
      · refine ⟨?_, ?_⟩
        · right; right; rfl
        · right; right; rfl
  obtain ⟨G, hG⟩ := segment_end_union_rectagon seg_left
    seg_right hDisj hClsInt
  refine ⟨G, ?_⟩
  rw [hG]; ext e
  simp only [Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

/-! ## §S.9 Horizontal strip is conn2 -/

/-- HOL Light: `rectangle_grid_h_conn2` (line 39179).
Any (n+1)×1 rectangle grid is conn2. -/
theorem rectangle_grid_h_conn2 (n : ℕ) (p : ℤ × ℤ) :
    conn2 (rectangle_grid p
      (p.1 + ↑(n + 1), p.2 + 1)) := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one]
    obtain ⟨G, hG⟩ := rectagon_rectangle_grid_sq p
    rw [← hG]; exact conn2_rectagon G
  | succ n ih =>
    have key : rectangle_grid p
        (p.1 + ↑(n + 2), p.2 + 1) =
        rectangle_grid p (p.1 + ↑(n + 1), p.2 + 1) ∪
        rectangle_grid (p.1 + ↑(n + 1), p.2)
          (p.1 + ↑(n + 2), p.2 + 1) := by
      ext e; simp only [Finset.mem_union]; constructor
      · intro he
        rcases rectangle_grid_edge p _ e he
          with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · simp only [rectangle_grid_h] at he ⊢
          obtain ⟨h1, h2, h3, h4⟩ := he
          by_cases hle : m.1 + 1 ≤ p.1 + ↑(n + 1)
          · left; exact ⟨h1, hle, h3, h4⟩
          · right; push Not at hle
            refine ⟨?_, h2, h3, h4⟩; push_cast; omega
        · simp only [rectangle_grid_v] at he ⊢
          obtain ⟨h1, h2, h3, h4⟩ := he
          by_cases hle : m.1 ≤ p.1 + ↑(n + 1)
          · left; exact ⟨h1, hle, h3, h4⟩
          · right; push Not at hle
            refine ⟨?_, h2, h3, h4⟩; push_cast; omega
      · rintro (he | he)
        · rcases rectangle_grid_edge p _ e he
            with ⟨m, rfl⟩ | ⟨m, rfl⟩
          · rw [rectangle_grid_h] at he ⊢
            refine ⟨he.1, ?_, he.2.2.1, he.2.2.2⟩
            push_cast at he; omega
          · rw [rectangle_grid_v] at he ⊢
            refine ⟨he.1, ?_, he.2.2.1, he.2.2.2⟩
            push_cast at he; omega
        · rcases rectangle_grid_edge _ _ e he
            with ⟨m, rfl⟩ | ⟨m, rfl⟩
          · rw [rectangle_grid_h] at he ⊢
            refine ⟨?_, he.2.1, he.2.2.1, he.2.2.2⟩
            push_cast at he; omega
          · rw [rectangle_grid_v] at he ⊢
            refine ⟨?_, he.2.1, he.2.2.1, he.2.2.2⟩
            push_cast at he; omega
    have hright_eq :
        rectangle_grid (p.1 + ↑(n + 1), p.2)
          (p.1 + ↑(n + 2), p.2 + 1) =
        rectangle_grid (p.1 + ↑(n + 1), p.2)
          ((p.1 + ↑(n + 1)) + 1, (p.2 : ℤ) + 1) := by
      congr 1 ; simp; ring
    have hright_conn2 :
        conn2 (rectangle_grid (p.1 + ↑(n + 1), p.2)
          (p.1 + ↑(n + 2), p.2 + 1)) := by
      rw [hright_eq]
      obtain ⟨G, hG⟩ :=
        rectagon_rectangle_grid_sq (p.1 + ↑(n + 1), p.2)
      rw [← hG]; exact conn2_rectagon G
    have hshared :
        (rectangle_grid p
          (p.1 + ↑(n + 1), p.2 + 1) ∩
        rectangle_grid (p.1 + ↑(n + 1), p.2)
          (p.1 + ↑(n + 2), p.2 + 1)).Nonempty := by
      refine ⟨vEdge (p.1 + ↑(n + 1), p.2),
        Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [rectangle_grid_v]; push_cast
        exact ⟨by omega, le_refl _, le_refl _, by omega⟩
      · rw [rectangle_grid_v]; push_cast
        exact ⟨le_refl _, by omega, le_refl _, by omega⟩
    rw [key]
    exact conn2_union_edge (rectangle_grid_edge p _)
      (rectangle_grid_edge _ _) ih hright_conn2 hshared

/-! ## §S.10 Full rectangle grid is conn2 -/

set_option maxHeartbeats 400000 in
-- Elevated heartbeats: the double induction on `m` and `n` requires repeated `simp` and
-- `omega` steps to decompose `rectangle_grid` into horizontal strips and verify edge membership.
/-- HOL Light: `rectangle_grid_conn2` (line 39292).
Any (n+1)×(m+1) rectangle grid is conn2. -/
theorem rectangle_grid_conn2 (m n : ℕ) (p : ℤ × ℤ) :
    conn2 (rectangle_grid p
      (p.1 + ↑(n + 1), p.2 + ↑(m + 1))) := by
  induction m with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one]
    exact rectangle_grid_h_conn2 n p
  | succ m ih =>
    have key : rectangle_grid p
        (p.1 + ↑(n + 1), p.2 + ↑(m + 2)) =
        rectangle_grid p
          (p.1 + ↑(n + 1), p.2 + ↑(m + 1)) ∪
        rectangle_grid (p.1, p.2 + ↑(m + 1))
          (p.1 + ↑(n + 1), p.2 + ↑(m + 2)) := by
      ext e; simp only [Finset.mem_union]; constructor
      · intro he
        rcases rectangle_grid_edge p _ e he
          with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp only [rectangle_grid_h] at he ⊢
          obtain ⟨h1, h2, h3, h4⟩ := he
          by_cases hle : k.2 ≤ p.2 + ↑(m + 1)
          · left; exact ⟨h1, h2, h3, hle⟩
          · right; push Not at hle
            refine ⟨h1, h2, ?_, h4⟩; push_cast; omega
        · simp only [rectangle_grid_v] at he ⊢
          obtain ⟨h1, h2, h3, h4⟩ := he
          by_cases hle : k.2 + 1 ≤ p.2 + ↑(m + 1)
          · left; exact ⟨h1, h2, h3, hle⟩
          · right; push Not at hle
            refine ⟨h1, h2, ?_, h4⟩; push_cast; omega
      · rintro (he | he)
        · rcases rectangle_grid_edge p _ e he
            with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · rw [rectangle_grid_h] at he ⊢
            refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
            push_cast at he; omega
          · rw [rectangle_grid_v] at he ⊢
            refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
            push_cast at he; omega
        · rcases rectangle_grid_edge _ _ e he
            with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · rw [rectangle_grid_h] at he ⊢
            refine ⟨he.1, he.2.1, ?_, he.2.2.2⟩
            push_cast at he; omega
          · rw [rectangle_grid_v] at he ⊢
            refine ⟨he.1, he.2.1, ?_, he.2.2.2⟩
            push_cast at he; omega
    have htop_conn2 :
        conn2 (rectangle_grid (p.1, p.2 + ↑(m + 1))
          (p.1 + ↑(n + 1), p.2 + ↑(m + 2))) := by
      convert rectangle_grid_h_conn2 n
        (p.1, p.2 + ↑(m + 1)) using 3
      push_cast; ring
    have hshared :
        (rectangle_grid p
          (p.1 + ↑(n + 1), p.2 + ↑(m + 1)) ∩
        rectangle_grid (p.1, p.2 + ↑(m + 1))
          (p.1 + ↑(n + 1),
            p.2 + ↑(m + 2))).Nonempty := by
      refine ⟨hEdge (p.1, p.2 + ↑(m + 1)),
        Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [rectangle_grid_h]; push_cast
        exact ⟨le_refl _, by omega, by omega, le_refl _⟩
      · rw [rectangle_grid_h]; push_cast
        exact ⟨le_refl _, by omega, le_refl _, by omega⟩
    rw [key]
    exact conn2_union_edge (rectangle_grid_edge p _)
      (rectangle_grid_edge _ _) ih htop_conn2 hshared

/-! ## §S.11 conn2 contains a rectagon -/

open Classical in
/-- HOL Light: `conn2_has_rectagon` (line 39408).
Every 2-connected edge set contains a rectagon. -/
theorem conn2_has_rectagon {E : Finset (Set E2)}
    (hE : ∀ e ∈ E, isEdge e) (hc : conn2 E) :
    ∃ B ⊆ E, ∃ (G : Rectagon), G.edges = B := by
  obtain ⟨hcard, hconn2⟩ := hc
  have hne : E.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨e, heE⟩ := hne
  have he_edge := hE e heE
  have hce := cls_edge_size2 he_edge
  rw [Set.ncard_eq_two] at hce
  obtain ⟨a, b, hab, hce_eq⟩ := hce
  -- Step 1: a, b are cls-points
  have ha_cls_e : a ∈ cls ({e} : Finset _) := by
    rw [hce_eq]; exact Set.mem_insert a {b}
  have hb_cls_e : b ∈ cls ({e} : Finset _) := by
    rw [hce_eq]; exact Set.mem_insert_of_mem a rfl
  have ha_E : a ∈ cls E :=
    cls_subset (Finset.singleton_subset_iff.mpr heE) ha_cls_e
  have hb_E : b ∈ cls E :=
    cls_subset (Finset.singleton_subset_iff.mpr heE) hb_cls_e
  -- Step 2: Find second edge through a
  have ha_inc : e ∈ incidentEdges E a := by
    simp only [incidentEdges, Finset.mem_filter]
    obtain ⟨e₀, he₀, hcl⟩ := ha_cls_e
    exact ⟨heE, Finset.mem_singleton.mp he₀ ▸ hcl⟩
  obtain ⟨e', he'_inc, he'_ne⟩ :
      ∃ e' ∈ incidentEdges E a, e' ≠ e := by
    by_contra h
    push Not at h
    have hcard_le :
        (incidentEdges E a).card ≤ 1 := by
      calc (incidentEdges E a).card
          ≤ ({e} : Finset _).card :=
            Finset.card_le_card (fun x hx =>
              Finset.mem_singleton.mpr (h x hx))
        _ = 1 := Finset.card_singleton e
    have h1 := cls_iff_numClosure_pos.mp ha_E
    have h2 := conn2_no1 hE ⟨hcard, hconn2⟩ a
    have : numClosure E a =
        (incidentEdges E a).card := rfl
    omega
  have he'E : e' ∈ E :=
    (Finset.mem_filter.mp he'_inc).1
  have hcl_e'_a : pointI a ∈ closure e' :=
    (Finset.mem_filter.mp he'_inc).2
  have he'_edge := hE e' he'E
  -- Step 3: Get second endpoint c
  have hce' := cls_edge_size2 he'_edge
  rw [Set.ncard_eq_two] at hce'
  obtain ⟨p', q', hpq', hce'_eq⟩ := hce'
  have ha_in_e' : a ∈ cls ({e'} : Finset _) :=
    ⟨e', Finset.mem_singleton_self e', hcl_e'_a⟩
  rw [hce'_eq] at ha_in_e'
  simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha_in_e'
  obtain ⟨c, hac, hce'_eq'⟩ :
      ∃ c, a ≠ c ∧
        cls ({e'} : Finset _) = {a, c} := by
    rcases ha_in_e' with rfl | rfl
    · exact ⟨q', hpq', hce'_eq⟩
    · exact ⟨p', hpq'.symm,
        by rw [hce'_eq, Set.pair_comm]⟩
  have ha_cls_e' : a ∈ cls ({e'} : Finset _) := by
    rw [hce'_eq']
    exact Set.mem_insert a {c}
  have hc_cls_e' : c ∈ cls ({e'} : Finset _) := by
    rw [hce'_eq']
    exact Set.mem_insert_of_mem a rfl
  have hc_E : c ∈ cls E :=
    cls_subset (Finset.singleton_subset_iff.mpr he'E)
      hc_cls_e'
  -- Step 4: b ≠ c (otherwise e = e')
  have hcb : c ≠ b := by
    intro heq; subst heq
    have : cls ({e} : Finset _) =
        cls ({e'} : Finset _) := by
      rw [hce_eq, hce'_eq']
    exact he'_ne
      (cls_injective e e' he_edge he'_edge this).symm
  -- Step 5: Get segment S from b to c avoiding a
  obtain ⟨S, hSE, hSeg, ha_not⟩ :=
    hconn2 b c a hb_E hc_E hcb.symm hac.symm hab.symm
  -- Step 6: Build single-edge segments
  have hcl_a_e : pointI a ∈ closure e := by
    obtain ⟨e₀, he₀, hcl₀⟩ := ha_cls_e
    rwa [Finset.mem_singleton.mp he₀] at hcl₀
  have hcl_b_e : pointI b ∈ closure e := by
    obtain ⟨e₀, he₀, hcl₀⟩ := hb_cls_e
    rwa [Finset.mem_singleton.mp he₀] at hcl₀
  have hcl_c_e' : pointI c ∈ closure e' := by
    obtain ⟨e₀, he₀, hcl₀⟩ := hc_cls_e'
    rwa [Finset.mem_singleton.mp he₀] at hcl₀
  have seg_e : segment_end {e} b a :=
    segment_end_sing hcl_b_e hcl_a_e hab.symm he_edge
  have seg_e' : segment_end {e'} a c :=
    segment_end_sing hcl_e'_a hcl_c_e' hac he'_edge
  -- Step 7: Chain e and e' through a
  have hcls_ee' : cls ({e} : Finset _) ∩
      cls ({e'} : Finset _) = {a} := by
    rw [hce_eq, hce'_eq']; ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact h1
      · exact h1
      · exact h2
      · exact absurd (h1.symm.trans h2) hcb.symm
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  have seg_chain : segment_end ({e} ∪ {e'}) b c :=
    segment_end_union seg_e seg_e' hcls_ee'
  -- Step 8: Disjointness
  have he_notS : e ∉ S := fun h =>
    ha_not (cls_subset
      (Finset.singleton_subset_iff.mpr h) ha_cls_e)
  have he'_notS : e' ∉ S := fun h =>
    ha_not (cls_subset
      (Finset.singleton_subset_iff.mpr h) ha_cls_e')
  have hDisj : Disjoint S ({e} ∪ {e'}) := by
    rw [Finset.disjoint_left]; intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact he_notS hx
    · exact he'_notS hx
  -- Step 9: Intersection is {b, c}
  have hClsInt :
      cls S ∩ cls ({e} ∪ {e'}) = {b, c} := by
    rw [cls_union, hce_eq, hce'_eq']; ext x
    simp only [Set.mem_inter_iff, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hx_S, hx_ee'⟩
      rcases hx_ee' with (rfl | rfl) | rfl | rfl
      · exact absurd hx_S ha_not
      · exact Or.inl rfl
      · exact absurd hx_S ha_not
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨segment_end_cls hSeg,
              Or.inl (Or.inr rfl)⟩
      · exact ⟨segment_end_cls2 hSeg,
              Or.inr (Or.inr rfl)⟩
  -- Step 10: Build rectagon
  obtain ⟨G, hG⟩ := segment_end_union_rectagon hSeg
    seg_chain hDisj hClsInt
  exact ⟨G.edges,
    hG ▸ Finset.union_subset hSE
      (Finset.union_subset
        (Finset.singleton_subset_iff.mpr heE)
        (Finset.singleton_subset_iff.mpr he'E)),
    G, rfl⟩
