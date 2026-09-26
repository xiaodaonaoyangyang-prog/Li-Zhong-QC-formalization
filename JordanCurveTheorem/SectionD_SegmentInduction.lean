/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionC_Rectagons

/-!
# Section D: Segment Induction and Parity
## HOL Light: Section D (Lines 4784–7356)

Inductive structure of segments: inductive sets, sub-segments, terminal edges,
the induction principle for segments, part-below constructions, and the key
parity result `squ_left_par` that controls how parity changes across vertical
edges.

### Key HOL Light definitions
- `inductive_set` (line 4789): Adjacency-closed nonempty subset
- `segment_of` (line 4839): Smallest inductive set containing an edge
- `part_below` (line 5440): Edges below a given vertex
- `terminal_edge` (line 5671): The unique edge at an endpoint
- `target_set` (line 6851): Target of the terminal edge bijection

### Key HOL Light theorems
- `rectagon_subset` (line 5076): A rectagon inside a segment equals it
- `num_closure0` (line 5890): numClosure = 0 characterization
- `num_closure2` (line 5917): numClosure = 2 characterization
- `terminal_endpoint` (line 5680): Terminal edge properties
- `terminal_edge_bij` (line 7180): Bijection from endpoints to target_set
- `target_set_even` (line 7290): Target set has even cardinality
- `squ_left_par` (line 7350): Parity changes across v_edge iff v_edge ∈ G
-/

open Set Topology

noncomputable section

/-! ## numClosure characterizations -/

/-- `numClosure G m = 0` iff no edge of `G` is incident to `pointI m`.
    HOL Light: `num_closure0` (line 5890). -/
theorem numClosure_eq_zero_iff (G : Finset (Set E2)) (m : ℤ × ℤ) :
    numClosure G m = 0 ↔ ∀ e ∈ G, pointI m ∉ closure e := by
  open Classical in
  simp only [numClosure, incidentEdges, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- `numClosure G m = 2` iff exactly two edges of `G` are incident to `pointI m`.
    HOL Light: `num_closure2` (line 5917). -/
theorem numClosure_eq_two_iff (G : Finset (Set E2)) (m : ℤ × ℤ) :
    numClosure G m = 2 ↔
      ∃ a b, a ≠ b ∧ a ∈ G ∧ b ∈ G ∧ pointI m ∈ closure a ∧ pointI m ∈ closure b ∧
        ∀ e ∈ G, pointI m ∈ closure e → e = a ∨ e = b := by
  open Classical in
  simp only [numClosure, incidentEdges]
  constructor
  · intro h
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp h
    refine ⟨a, b, hab, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      first
      | (have := heq ▸ Finset.mem_insert_self a {b}
         simp only [Finset.mem_filter] at this; exact this.1)
      | (have := heq ▸ Finset.mem_insert_self a {b}
         simp only [Finset.mem_filter] at this; exact this.2)
      | (have := heq ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b))
         simp only [Finset.mem_filter] at this; exact this.1)
      | (have := heq ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b))
         simp only [Finset.mem_filter] at this; exact this.2)
      | (intro e he hcl
         have hmem : e ∈ Finset.filter (fun e => pointI m ∈ closure e) G :=
           Finset.mem_filter.mpr ⟨he, hcl⟩
         rw [heq] at hmem
         simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; exact hmem) }
  · rintro ⟨a, b, hab, ha, hb, hcla, hclb, huniq⟩
    apply Finset.card_eq_two.mpr
    exact ⟨a, b, hab, by
      ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨he, hcl⟩ => huniq e he hcl,
        fun h => h.elim (fun h => h ▸ ⟨ha, hcla⟩) (fun h => h ▸ ⟨hb, hclb⟩)⟩⟩

/-! ## Inductive sets -/

/-- An inductive subset of a segment `G`: a nonempty subset closed under
    adjacency within `G`.
    HOL Light: `inductive_set G S` (line 4789). -/
def Segment.isInductiveSubset (G : Segment) (S : Finset (Set E2)) : Prop :=
  S ⊆ G.edges ∧ S.Nonempty ∧
    ∀ e ∈ S, ∀ e' ∈ G.edges, e ≠ e' →
      (closure e ∩ closure e').Nonempty → e' ∈ S

/-- The whole edge set is an inductive subset of itself.
    HOL Light: `inductive_univ` (line 4795). -/
theorem Segment.isInductiveSubset_self (G : Segment) :
    G.isInductiveSubset G.edges :=
  ⟨Finset.Subset.refl _, G.nonempty, fun _ _ _ he' _ _ => he'⟩

/-- Every inductive subset of a connected segment equals the full edge set. -/
theorem Segment.isInductiveSubset_eq (G : Segment) (S : Finset (Set E2))
    (hS : G.isInductiveSubset S) : S = G.edges := by
  have hconn := G.connected ↑S hS.1 (Finset.coe_nonempty.mpr hS.2.1)
  have hadj : ∀ C ∈ (↑S : Set _), ∀ C' ∈ (↑G.edges : Set (Set E2)),
      cellAdj C C' → C' ∈ (↑S : Set _) := by
    intro e he e' he' hadj
    exact Finset.mem_coe.mpr (hS.2.2 e (Finset.mem_coe.mp he)
      e' (Finset.mem_coe.mp he') hadj.2.2.1 hadj.2.2.2)
  have := hconn hadj
  ext x; constructor
  · exact fun h => hS.1 h
  · intro h; exact (this ▸ Finset.mem_coe.mpr h : x ∈ (↑S : Set _))

/-- The smallest inductive subset containing edge `e`.
    HOL Light: `segment_of G e` (line 4839). -/
noncomputable def Segment.segmentOf (G : Segment) (e : Set E2) : Finset (Set E2) :=
  open Classical in
  G.edges.filter (fun f => ∀ S : Finset (Set E2), G.isInductiveSubset S → e ∈ S → f ∈ S)

/-- segmentOf of a connected segment equals the full edge set. -/
theorem Segment.segmentOf_eq_edges (G : Segment) (e : Set E2)
    (_he : e ∈ G.edges) : G.segmentOf e = G.edges := by
  ext f; simp only [Segment.segmentOf, Finset.mem_filter]
  exact ⟨fun ⟨hf, _⟩ => hf,
    fun hf => ⟨hf, fun S hS _ => (G.isInductiveSubset_eq S hS ▸ hf : f ∈ S)⟩⟩

/-- `segmentOf` is an inductive subset.
    HOL Light: `inductive_segment` (line 4845). -/
theorem Segment.segmentOf_isInductive (G : Segment) (e : Set E2)
    (he : e ∈ G.edges) : G.isInductiveSubset (G.segmentOf e) := by
  rw [G.segmentOf_eq_edges e he]; exact G.isInductiveSubset_self

/-- `segmentOf` contains the starting edge.
    HOL Light: `segment_of_in` (line 4900). -/
theorem Segment.segmentOf_mem (G : Segment) (e : Set E2) (he : e ∈ G.edges) :
    e ∈ G.segmentOf e := by
  rw [G.segmentOf_eq_edges e he]; exact he

/-- `segmentOf` is a subset of `G`.
    HOL Light: `segment_of_G` (line 4856). -/
theorem Segment.segmentOf_subset (G : Segment) (e : Set E2)
    (he : e ∈ G.edges) : G.segmentOf e ⊆ G.edges := by
  rw [G.segmentOf_eq_edges e he]

/-- `segmentOf` from two edges in the same component are equal.
    HOL Light: `segment_of_eq` (line 4950). -/
theorem Segment.segmentOf_eq (G : Segment) (e f : Set E2)
    (he : e ∈ G.edges) (hf : f ∈ G.segmentOf e) :
    G.segmentOf e = G.segmentOf f := by
  have hfG : f ∈ G.edges := G.segmentOf_subset e he hf
  rw [G.segmentOf_eq_edges e he, G.segmentOf_eq_edges f hfG]

/-- `segmentOf P e` forms a segment when P is a subsegment of a segment.
    HOL Light: `segment_of_segment` (line 4993). -/
theorem Segment.segmentOf_isSegment (G P : Segment) (e : Set E2)
    (_hPG : P.edges ⊆ G.edges) (he : e ∈ P.edges) :
    ∃ S : Segment, S.edges = P.segmentOf e := by
  rw [P.segmentOf_eq_edges e he]; exact ⟨P, rfl⟩

/-! ## Rectagon maximality -/

/-- A rectagon contained in a segment must equal the segment.
    HOL Light: `rectagon_subset` (line 5076). -/
theorem rectagon_subset_eq (R : Rectagon) (G : Segment) (h : R.edges ⊆ G.edges) :
    R.edges = G.edges := by
  -- R.edges is an inductive subset of G, so it equals G.edges
  apply G.isInductiveSubset_eq
  refine ⟨h, R.nonempty, ?_⟩
  intro e heR e' he'G hne hinter
  -- e ∈ R, e' ∈ G, e ≠ e', closure(e) ∩ closure(e') ≠ ∅
  -- At the shared point m, numClosure(R, m) ∈ {0, 2}
  obtain ⟨z, hz1, hz2⟩ := hinter
  -- z is in closures of two distinct edges, so it's a lattice point
  obtain ⟨m, rfl⟩ := edges_share_lattice_point e e'
    (R.all_edges e heR) (G.all_edges e' he'G) hne z ⟨hz1, hz2⟩
  -- numClosure(R, m) ≥ 1 since e ∈ R with pointI m ∈ closure e
  have hRdeg := R.even_degree m
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hRdeg
  have hRpos : numClosure R.edges m ≥ 1 := by
    by_contra h0; push Not at h0
    have := (numClosure_eq_zero_iff R.edges m).mp (by omega)
    exact this e heR hz1
  -- So numClosure(R, m) = 2
  have hR2 : numClosure R.edges m = 2 := by omega
  -- Suppose e' ∉ R
  by_contra he'nR
  -- Then e, and two edges from R at m, and e' give ≥ 3 distinct edges at m in G
  obtain ⟨a, b, hab, haR, hbR, hacl, hbcl, huniq⟩ :=
    (numClosure_eq_two_iff R.edges m).mp hR2
  -- e' is incident to m and in G but not in R
  -- e' ≠ a and e' ≠ b (since a, b ∈ R but e' ∉ R)
  have he'na : e' ≠ a := fun h => he'nR (h ▸ haR)
  have he'nb : e' ≠ b := fun h => he'nR (h ▸ hbR)
  -- numClosure(G, m) ≥ 3: a, b, e' are 3 distinct edges in G incident to m
  have hGdeg := G.degree_bound m
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hGdeg
  have : numClosure G.edges m ≥ 3 := by
    classical
    -- At least 3 elements in incidentEdges: a, b, e'
    have ha_in : a ∈ incidentEdges G.edges m :=
      Finset.mem_filter.mpr ⟨h haR, hacl⟩
    have hb_in : b ∈ incidentEdges G.edges m :=
      Finset.mem_filter.mpr ⟨h hbR, hbcl⟩
    have he'_in : e' ∈ incidentEdges G.edges m :=
      Finset.mem_filter.mpr ⟨he'G, hz2⟩
    have hcard : (incidentEdges G.edges m).card ≥ 3 := by
      have hbe' : b ≠ e' := Ne.symm he'nb
      have h1 : ({e'} : Finset _).card = 1 := Finset.card_singleton _
      have h2 : b ∉ ({e'} : Finset _) := Finset.notMem_singleton.mpr hbe'
      have h3 : ({b, e'} : Finset _).card = 2 := by
        rw [Finset.card_insert_of_notMem h2, h1]
      have h4 : a ∉ ({b, e'} : Finset _) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not; exact ⟨hab, Ne.symm he'na⟩
      have h5 : ({a, b, e'} : Finset _).card = 3 := by
        rw [Finset.card_insert_of_notMem h4, h3]
      have hsub : ({a, b, e'} : Finset _) ⊆ incidentEdges G.edges m := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact ha_in
        · exact hb_in
        · exact he'_in
      linarith [Finset.card_le_card hsub, h5]
    exact hcard
  omega

/-- Every rectagon has at least one horizontal edge.
    HOL Light: `rectagon_h_edge` (line 5165). -/
theorem Rectagon.has_h_edge (G : Rectagon) : ∃ m, hEdge m ∈ G.edges := by
  by_contra hall; push Not at hall
  -- All edges are vEdge
  have hv : ∀ e ∈ G.edges, ∃ m, e = vEdge m := by
    intro e he; rcases G.all_edges e he with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact absurd he (hall m)
    · exact ⟨m, rfl⟩
  -- Pick any edge and extract its coordinate
  obtain ⟨e₀, he₀⟩ := G.nonempty
  obtain ⟨m₀, rfl⟩ := hv e₀ he₀
  -- Build the set of y-coordinates of all vEdges
  let yCoords := G.edges.image (fun e => open Classical in
    if h : ∃ m, e = vEdge m then (Classical.choose h).2 else 0)
  have hyNe : yCoords.Nonempty := ⟨m₀.2, Finset.mem_image.mpr ⟨vEdge m₀, he₀, by
    rw [dif_pos ⟨m₀, rfl⟩]
    exact congr_arg Prod.snd ((vEdge_inj _ _).mp
      (Classical.choose_spec (⟨m₀, rfl⟩ : ∃ m, vEdge m₀ = vEdge m)).symm)⟩⟩
  obtain ⟨y_min, hy_mem, hy_min⟩ := yCoords.exists_min_image id hyNe
  simp only [id] at hy_min
  obtain ⟨e_min, he_min, hy_eq⟩ := Finset.mem_image.mp hy_mem
  obtain ⟨m_min, rfl⟩ := hv e_min he_min
  rw [dif_pos ⟨m_min, rfl⟩] at hy_eq
  have hchoose := Classical.choose_spec (⟨m_min, rfl⟩ : ∃ m, vEdge m_min = vEdge m)
  have hchoose_eq := (vEdge_inj _ _).mp hchoose.symm
  rw [hchoose_eq] at hy_eq
  -- At bottom endpoint m_min: vEdge m_min is the only incident edge
  -- because any other vEdge n incident to m_min would have n.2 = m_min.2 or n.2 = m_min.2 - 1
  -- n.2 = m_min.2 - 1 contradicts minimality; n.2 = m_min.2 with same x gives n = m_min
  have hdeg := G.even_degree m_min
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdeg
  have hpos : 0 < numClosure G.edges m_min := by
    rw [Nat.pos_iff_ne_zero]; intro h0
    exact ((numClosure_eq_zero_iff G.edges m_min).mp h0 _ he_min)
      ((pointI_mem_closure_vEdge m_min m_min).mpr ⟨rfl, Or.inl rfl⟩)
  have htwo : numClosure G.edges m_min = 2 := by omega
  obtain ⟨a, b, hab, haG, hbG, hacl, hbcl, huniq⟩ :=
    (numClosure_eq_two_iff G.edges m_min).mp htwo
  obtain ⟨ma, rfl⟩ := hv a haG; obtain ⟨mb, rfl⟩ := hv b hbG
  rw [pointI_mem_closure_vEdge] at hacl hbcl
  obtain ⟨hax, hay⟩ := hacl; obtain ⟨hbx, hby⟩ := hbcl
  -- Both ma.2 ≥ y_min by minimality
  have hay_ge : ma.2 ≥ y_min := hy_min ma.2
    (Finset.mem_image.mpr ⟨vEdge ma, haG, by
      rw [dif_pos ⟨ma, rfl⟩]
      exact congr_arg Prod.snd ((vEdge_inj _ _).mp
        (Classical.choose_spec (⟨ma, rfl⟩ : ∃ m, vEdge ma = vEdge m)).symm)⟩)
  have hby_ge : mb.2 ≥ y_min := hy_min mb.2
    (Finset.mem_image.mpr ⟨vEdge mb, hbG, by
      rw [dif_pos ⟨mb, rfl⟩]
      exact congr_arg Prod.snd ((vEdge_inj _ _).mp
        (Classical.choose_spec (⟨mb, rfl⟩ : ∃ m, vEdge mb = vEdge m)).symm)⟩)
  rw [← hy_eq] at hay_ge hby_ge
  -- ma.2 ∈ {m_min.2, m_min.2 - 1} and ma.2 ≥ m_min.2 → ma.2 = m_min.2
  have hma_eq : ma = m_min :=
    Prod.ext (by omega) (by rcases hay with h1 | h1 <;> omega)
  have hmb_eq : mb = m_min :=
    Prod.ext (by omega) (by rcases hby with h1 | h1 <;> omega)
  exact absurd (congr_arg vEdge (hma_eq.trans hmb_eq.symm)) hab

/-- Every rectagon has at least one vertical edge.
    HOL Light: `rectagon_v_edge` (line 5380). -/
theorem Rectagon.has_v_edge (G : Rectagon) : ∃ m, vEdge m ∈ G.edges := by
  by_contra hall; push Not at hall
  have hh : ∀ e ∈ G.edges, ∃ m, e = hEdge m := by
    intro e he; rcases G.all_edges e he with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m, rfl⟩
    · exact absurd he (hall m)
  obtain ⟨e₀, he₀⟩ := G.nonempty; obtain ⟨m₀, rfl⟩ := hh e₀ he₀
  let xCoords := G.edges.image (fun e => open Classical in
    if h : ∃ m, e = hEdge m then (Classical.choose h).1 else 0)
  have hxNe : xCoords.Nonempty := ⟨m₀.1, Finset.mem_image.mpr ⟨hEdge m₀, he₀, by
    rw [dif_pos ⟨m₀, rfl⟩]
    exact congr_arg Prod.fst ((hEdge_inj _ _).mp
      (Classical.choose_spec (⟨m₀, rfl⟩ : ∃ m, hEdge m₀ = hEdge m)).symm)⟩⟩
  obtain ⟨x_min, hx_mem, hx_min⟩ := xCoords.exists_min_image id hxNe
  simp only [id] at hx_min
  obtain ⟨e_min, he_min, hx_eq⟩ := Finset.mem_image.mp hx_mem
  obtain ⟨m_min, rfl⟩ := hh e_min he_min
  rw [dif_pos ⟨m_min, rfl⟩] at hx_eq
  have hchoose_eq := (hEdge_inj _ _).mp
    (Classical.choose_spec (⟨m_min, rfl⟩ : ∃ m, hEdge m_min = hEdge m)).symm
  rw [hchoose_eq] at hx_eq
  -- At left endpoint m_min: degree constraints force contradiction
  have hdeg := G.even_degree m_min
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdeg
  have hpos : 0 < numClosure G.edges m_min := by
    rw [Nat.pos_iff_ne_zero]; intro h0
    exact ((numClosure_eq_zero_iff G.edges m_min).mp h0 _ he_min)
      ((pointI_mem_closure_hEdge m_min m_min).mpr ⟨rfl, Or.inl rfl⟩)
  have htwo : numClosure G.edges m_min = 2 := by omega
  obtain ⟨a, b, hab, haG, hbG, hacl, hbcl, huniq⟩ :=
    (numClosure_eq_two_iff G.edges m_min).mp htwo
  obtain ⟨ma, rfl⟩ := hh a haG; obtain ⟨mb, rfl⟩ := hh b hbG
  rw [pointI_mem_closure_hEdge] at hacl hbcl
  obtain ⟨hay, hax⟩ := hacl; obtain ⟨hby, hbx⟩ := hbcl
  have hax_ge : ma.1 ≥ x_min := hx_min ma.1
    (Finset.mem_image.mpr ⟨hEdge ma, haG, by
      rw [dif_pos ⟨ma, rfl⟩]
      exact congr_arg Prod.fst ((hEdge_inj _ _).mp
        (Classical.choose_spec (⟨ma, rfl⟩ : ∃ m, hEdge ma = hEdge m)).symm)⟩)
  have hbx_ge : mb.1 ≥ x_min := hx_min mb.1
    (Finset.mem_image.mpr ⟨hEdge mb, hbG, by
      rw [dif_pos ⟨mb, rfl⟩]
      exact congr_arg Prod.fst ((hEdge_inj _ _).mp
        (Classical.choose_spec (⟨mb, rfl⟩ : ∃ m, hEdge mb = hEdge m)).symm)⟩)
  rw [← hx_eq] at hax_ge hbx_ge
  -- ma.1 ∈ {m_min.1, m_min.1 - 1} and ma.1 ≥ m_min.1 → ma.1 = m_min.1
  have hma_eq : ma = m_min :=
    Prod.ext (by rcases hax with h1 | h1 <;> omega) (by omega)
  have hmb_eq : mb = m_min :=
    Prod.ext (by rcases hbx with h1 | h1 <;> omega) (by omega)
  exact absurd (congr_arg hEdge (hma_eq.trans hmb_eq.symm)) hab

/-! ## Sub-segments -/

/-- A sub-segment of `G` is a subset of `G`'s edges that also forms a segment. -/
def Segment.isSubsegment (G G' : Segment) : Prop :=
  G'.edges ⊆ G.edges

/-! ## Terminal edges -/

/-- A terminal edge of a psegment is an edge incident to an endpoint.
    HOL Light: concept used in terminal_edge construction. -/
def Segment.isTerminalEdge (G : Segment) (e : Set E2) : Prop :=
  e ∈ G.edges ∧ ∃ m : ℤ × ℤ, G.isEndpoint m ∧ pointI m ∈ closure e

/-- The unique edge at an endpoint (Hilbert's choice).
    HOL Light: `terminal_edge G m` (line 5671). -/
noncomputable def Segment.terminalEdge (G : Segment) (m : ℤ × ℤ) : Set E2 :=
  open Classical in if h : G.isEndpoint m then
    Classical.choose ((numClosure_eq_one_iff G.edges m).mp h)
  else ∅

/-- `terminalEdge` is a valid edge in the segment incident to `m`.
    HOL Light: `terminal_endpoint` (line 5680). -/
theorem Segment.terminalEdge_prop (G : Segment) (m : ℤ × ℤ) (hm : G.isEndpoint m) :
    G.terminalEdge m ∈ G.edges ∧ pointI m ∈ closure (G.terminalEdge m) := by
  unfold Segment.terminalEdge
  rw [dif_pos hm]
  exact (Classical.choose_spec ((numClosure_eq_one_iff G.edges m).mp hm)).1

/-- `terminalEdge` is the unique edge at an endpoint.
    HOL Light: `terminal_unique` (line 5693). -/
theorem Segment.terminalEdge_unique (G : Segment) (m : ℤ × ℤ) (hm : G.isEndpoint m)
    (e : Set E2) (he : e ∈ G.edges) (hcl : pointI m ∈ closure e) :
    e = G.terminalEdge m := by
  unfold Segment.terminalEdge; rw [dif_pos hm]
  have spec := Classical.choose_spec ((numClosure_eq_one_iff G.edges m).mp hm)
  have huniq : ∀ y, y ∈ G.edges ∧ pointI m ∈ closure y →
    y = Classical.choose ((numClosure_eq_one_iff G.edges m).mp hm) := spec.2
  exact huniq e ⟨he, hcl⟩

/-- Every psegment has a terminal edge.
    HOL Light: follows from endpoint existence + terminal_edge. -/
theorem Segment.psegment_has_terminal (G : Segment) (hG : G.isPsegment) :
    ∃ e, G.isTerminalEdge e := by
  obtain ⟨a, _, _, ha, _, _⟩ := hG
  obtain ⟨e, ⟨he, hcl⟩, _⟩ := (numClosure_eq_one_iff G.edges a).mp ha
  exact ⟨e, he, a, ha, hcl⟩

/-- A rectagon has no endpoints.
    HOL Light: `rectagon_endpoint0` (line 7273). -/
theorem Rectagon.endpoint_card_zero (G : Rectagon) (m : ℤ × ℤ) :
    ¬G.toSegment.isEndpoint m :=
  G.toSegment_no_endpoints m

/-! ## Removing a terminal edge -/

/-- Removing a terminal edge from a psegment with ≥ 2 edges yields a segment.
    HOL Light: consequence of segment structure theorems. -/
theorem Segment.remove_terminal (G : Segment) (_hG : G.isPsegment)
    (e : Set E2) (he : G.isTerminalEdge e) (hcard : 1 < G.edges.card) :
    ∃ G' : Segment, G'.edges = G.edges.erase e ∧
      (G'.isPsegment ∨ ∃ R : Rectagon, R.edges = G'.edges) := by
  obtain ⟨heG, m, hm, hcl⟩ := he
  have hne : G.edges ≠ {e} := by
    intro h; rw [h, Finset.card_singleton] at hcard; omega
  obtain ⟨G', hG'eq⟩ := Segment.segment_delete G e m heG hm hcl hne
  refine ⟨G', hG'eq, ?_⟩
  rcases G'.endpoint_count with h | h
  · -- G' has no endpoints → build a Rectagon
    right; exact ⟨{
      edges := G'.edges
      nonempty := G'.nonempty
      all_edges := G'.all_edges
      even_degree := by
        intro p
        have hd := G'.degree_bound p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd ⊢
        have := h p
        simp only [Segment.isEndpoint] at this
        omega
      connected := G'.connected
    }, rfl⟩
  · left; exact h

/-- Removing a terminal edge from a psegment preserves the other endpoint.
    HOL Light: consequence of segment structure theorems. -/
theorem Segment.remove_terminal_preserves_endpoint (G : Segment) (_hG : G.isPsegment)
    (e : Set E2) (he : G.isTerminalEdge e) (hcard : 1 < G.edges.card)
    (m : ℤ × ℤ) (hm : G.isEndpoint m) (hm_not : pointI m ∉ closure e) :
    ∃ G' : Segment, G'.edges = G.edges.erase e ∧ G'.isEndpoint m := by
  obtain ⟨heG, m₀, hm₀, hcl₀⟩ := he
  have hne : G.edges ≠ {e} := by
    intro h; rw [h, Finset.card_singleton] at hcard; omega
  obtain ⟨G', hG'eq⟩ := Segment.segment_delete G e m₀ heG hm₀ hcl₀ hne
  refine ⟨G', hG'eq, ?_⟩
  -- m is not on e, so incidentEdges is unchanged
  simp only [Segment.isEndpoint, numClosure] at hm ⊢
  rw [hG'eq]
  have : incidentEdges (G.edges.erase e) m = incidentEdges G.edges m := by
    simp only [incidentEdges]
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨⟨_, hx⟩, hcl'⟩; exact ⟨hx, hcl'⟩
    · intro ⟨hx, hcl'⟩; exact ⟨⟨fun h => hm_not (h ▸ hcl'), hx⟩, hcl'⟩
  rw [this]; exact hm

/-! ## Segment induction -/

/-- Induction principle for psegments: a property holds for all psegments
    if it holds for single-edge psegments and is preserved under removal
    of a terminal edge.
    HOL Light: structural induction on segments. -/
theorem psegment_induction
    (P : Segment → Prop)
    (h_single : ∀ G : Segment, G.isPsegment → G.edges.card = 1 → P G)
    (h_step : ∀ G : Segment, G.isPsegment → G.edges.card > 1 →
      (∀ G' : Segment, G'.isPsegment → G'.edges ⊂ G.edges → P G') → P G) :
    ∀ G : Segment, G.isPsegment → P G := by
  intro G hps
  by_cases hcard : G.edges.card = 1
  · exact h_single G hps hcard
  · have hgt : G.edges.card > 1 := by
      have := G.nonempty
      obtain ⟨e, he⟩ := this
      have hpos : G.edges.card ≥ 1 := Finset.card_pos.mpr ⟨e, he⟩
      omega
    exact h_step G hps hgt (fun G' hps' hlt =>
      have : G'.edges.card < G.edges.card := Finset.card_lt_card hlt
      psegment_induction P h_single h_step G' hps')
termination_by G => G.edges.card

/-- Induction principle for segments (general, including rectagon case). -/
theorem segment_induction
    (P : Segment → Prop)
    (h_single : ∀ G : Segment, G.edges.card = 1 → P G)
    (h_step : ∀ G : Segment,
      (∀ G' : Segment, G'.edges ⊂ G.edges → P G') → P G) :
    ∀ G : Segment, P G := by
  intro G
  apply h_step
  intro G' hG'
  have : G'.edges.card < G.edges.card := Finset.card_lt_card hG'
  exact segment_induction P h_single h_step G'
termination_by G => G.edges.card

/-! ## Part below -/

/-- The part of a rectagon below vertex `m`: vertical edges in the same column
    at or below `m`, plus horizontal edges at or below `m` that touch the
    vertical line through `m`.
    HOL Light: `part_below G m` (line 5440). -/
noncomputable def partBelow (G : Finset (Set E2)) (m : ℤ × ℤ) : Finset (Set E2) :=
  let pred : Set E2 → Prop := fun e =>
    (∃ n, e = vEdge n ∧ n.2 ≤ m.2 ∧ n.1 = m.1) ∨
    (∃ n, e = hEdge n ∧ n.2 ≤ m.2 ∧ pointI (m.1, n.2) ∈ closure (hEdge n))
  @Finset.filter _ pred (Classical.decPred pred) G

/-- `partBelow` is a subset of `G`.
    HOL Light: `part_below_subset` (line 6930). -/
theorem partBelow_subset (G : Finset (Set E2)) (m : ℤ × ℤ) :
    partBelow G m ⊆ G := by
  intro e he; simp only [partBelow, Finset.mem_filter] at he; exact he.1

/-- `partBelow` is finite when `G` is.
    HOL Light: `part_below_finite` (line 6921). -/
theorem partBelow_card_le (G : Finset (Set E2)) (m : ℤ × ℤ) :
    (partBelow G m).card ≤ G.card :=
  Finset.card_le_card (partBelow_subset G m)

/-! ## Endpoint characterization in subrectagon -/

/-- An endpoint of a subset P of a rectagon G corresponds to a pair of
    adjacent edges, one in P and one in G \ P.
    HOL Light: `endpoint_subrectagon` (line 5964). -/
theorem endpoint_subrectagon (R : Rectagon) (P : Finset (Set E2))
    (hP : P ⊆ R.edges) (m : ℤ × ℤ) :
    numClosure P m = 1 ↔
      ∃ e e', e ∈ P ∧ e' ∈ R.edges ∧ e' ∉ P ∧ e ≠ e' ∧
        pointI m ∈ closure e ∧ pointI m ∈ closure e' := by
  open Classical in
  constructor
  · intro h1
    have hR := R.even_degree m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    have hmono := numClosure_mono hP m
    have hR2 : numClosure R.edges m = 2 := by omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    have he_mem : e ∈ incidentEdges P m := he ▸ Finset.mem_singleton_self e
    have heP : e ∈ P := (Finset.mem_filter.mp he_mem).1
    have hecl : pointI m ∈ closure e := (Finset.mem_filter.mp he_mem).2
    obtain ⟨a, b, hab, haR, hbR, hacl, hbcl, huniq⟩ :=
      (numClosure_eq_two_iff R.edges m).mp hR2
    have heR : e ∈ R.edges := hP heP
    -- e is a or b
    have h_ne_filter : ∀ f, f ∈ P → pointI m ∈ closure f → f = e := by
      intro f hfP hfcl
      have : f ∈ incidentEdges P m := Finset.mem_filter.mpr ⟨hfP, hfcl⟩
      rw [he] at this; exact Finset.mem_singleton.mp this
    rcases huniq e heR hecl with he_eq | he_eq
    · -- e = a
      have hbnP : b ∉ P := by
        intro hbP; have := h_ne_filter b hbP hbcl  -- b = e
        exact hab (he_eq.symm.trans this.symm)      -- a = e = b
      exact ⟨e, b, heP, hbR, hbnP, fun h => hab (he_eq.symm.trans h), hecl, hbcl⟩
    · -- e = b
      have hanP : a ∉ P := by
        intro haP; have := h_ne_filter a haP hacl   -- a = e
        exact hab (this.trans he_eq)                 -- a = e = b
      exact ⟨e, a, heP, haR, hanP, fun h => hab (h.symm.trans he_eq), hecl, hacl⟩
  · rintro ⟨e, e', heP, he'R, he'nP, hne, hecl, he'cl⟩
    have hR := R.even_degree m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    have heR : e ∈ R.edges := hP heP
    have hRpos : numClosure R.edges m ≥ 1 := by
      by_contra h0; push Not at h0
      exact (numClosure_eq_zero_iff R.edges m).mp (by omega) e heR hecl
    have hR2 : numClosure R.edges m = 2 := by omega
    obtain ⟨a, b, hab, haR, hbR, hacl, hbcl, huniq⟩ :=
      (numClosure_eq_two_iff R.edges m).mp hR2
    -- Every edge in P at m is also in R at m, hence equals a or b.
    -- e' ∉ P is one of {a, b}, so the other is the only possible P-member at m.
    have : incidentEdges P m = {e} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton, incidentEdges]
      constructor
      · intro ⟨hxP, hxcl⟩
        -- x touches m and is in P ⊆ R, so x ∈ {a,b}; similarly e, e' ∈ {a,b}
        -- With e ≠ e', e' ∉ P, x ∈ P: deduce x = e
        have hxR := hP hxP
        rcases huniq x hxR hxcl with hx | hx <;>
          rcases huniq e heR hecl with he1 | he1 <;>
            rcases huniq e' he'R he'cl with he2 | he2
        -- 8 cases: (x=a|b, e=a|b, e'=a|b)
        · exact absurd (he1.trans he2.symm) hne    -- e=a,e'=a → e=e'
        · exact hx.trans he1.symm                  -- x=a,e=a → x=e
        · exact absurd (he2.symm ▸ hx ▸ hxP) he'nP -- x=a,e'=a → a∈P
        · exact absurd (he1.trans he2.symm) hne    -- e=b,e'=b → e=e'
        · exact absurd (he1.trans he2.symm) hne    -- e=a,e'=a → e=e'
        · exact absurd (he2.symm ▸ hx ▸ hxP) he'nP -- x=b,e'=b → b∈P
        · exact hx.trans he1.symm                  -- x=b,e=b → x=e
        · exact absurd (he1.trans he2.symm) hne    -- e=b,e'=b → e=e'
      · intro hxe; exact ⟨hxe ▸ heP, hxe ▸ hecl⟩
    simp only [numClosure]; rw [this, Finset.card_singleton]

/-! ## Endpoint counting -/

/-- A non-rectagon sub-segment of a segment has an even number of endpoints.
    The number of endpoints of a psegment is always 2.
    HOL Light: `endpoint_even` (line 5847) / `endpoint_size2` (line 3719). -/
theorem endpoint_even (G : Segment) (P : Segment)
    (_hPG : P.edges ⊆ G.edges)
    (hnotR : ¬∃ R : Rectagon, R.edges = P.edges) :
    ∃ a b : ℤ × ℤ, a ≠ b ∧ P.isEndpoint a ∧ P.isEndpoint b ∧
      ∀ m, P.isEndpoint m → m = a ∨ m = b := by
  rcases P.endpoint_count with h | h
  · -- P has no endpoints → can build Rectagon → contradiction
    exfalso; apply hnotR
    exact ⟨{
      edges := P.edges
      nonempty := P.nonempty
      all_edges := P.all_edges
      even_degree := by
        intro p
        have hd := P.degree_bound p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd ⊢
        have := h p; simp only [Segment.isEndpoint] at this; omega
      connected := P.connected
    }, rfl⟩
  · exact h

/-! ## Target set and bijection -/

/-- The target set for the terminal edge bijection.
    HOL Light: `target_set G m` (line 6851). -/
noncomputable def targetSet (G : Finset (Set E2)) (m : ℤ × ℤ) : Finset (Set E2) :=
  let pred : Set E2 → Prop := fun e =>
    (∃ n, e = hEdge n ∧ n ∈ setLower G m) ∨
    (∃ n, e = hEdge n ∧ n ∈ setLower G (left m)) ∨
    (e = vEdge m ∧ vEdge m ∈ G)
  @Finset.filter _ pred (Classical.decPred pred) G

/-- `targetSet` is a subset of `G`.
    HOL Light: `target_set_subset` (line 6860). -/
theorem targetSet_subset (G : Finset (Set E2)) (m : ℤ × ℤ) :
    targetSet G m ⊆ G := by
  intro e he; simp only [targetSet, Finset.mem_filter] at he; exact he.1

/-- Membership in partBelow for vEdge.
    HOL Light: `part_below_v`. -/
private theorem partBelow_vEdge (G : Finset (Set E2)) (m n : ℤ × ℤ) :
    vEdge n ∈ partBelow G m ↔ vEdge n ∈ G ∧ n.2 ≤ m.2 ∧ n.1 = m.1 := by
  classical
  simp only [partBelow, Finset.mem_filter]
  constructor
  · rintro ⟨hG, (⟨n', hv, hn2, hn1⟩ | ⟨n', hh, _, _⟩)⟩
    · have := (vEdge_inj n n').mp hv
      exact ⟨hG, this ▸ hn2, this ▸ hn1⟩
    · exact absurd hh.symm (hEdge_ne_vEdge n' n)
  · rintro ⟨hG, h2, h1⟩
    exact ⟨hG, Or.inl ⟨n, rfl, h2, h1⟩⟩

/-- Membership in partBelow for hEdge — matches HOL Light `part_below_h`.
    `hEdge n ∈ partBelow G m ↔ setLower G m n ∨ setLower G (left m) n`. -/
private theorem partBelow_hEdge (G : Finset (Set E2)) (m n : ℤ × ℤ) :
    hEdge n ∈ partBelow G m ↔
      hEdge n ∈ G ∧ n.2 ≤ m.2 ∧ (n.1 = m.1 ∨ n.1 = m.1 - 1) := by
  classical
  simp only [partBelow, Finset.mem_filter]
  constructor
  · rintro ⟨hG, (⟨n', hv, _, _⟩ | ⟨n', hh, hn2, hcl⟩)⟩
    · exact absurd hv (hEdge_ne_vEdge n n')
    · have heq := (hEdge_inj n n').mp hh
      rw [← heq] at hn2 hcl
      rw [pointI_mem_closure_hEdge] at hcl
      refine ⟨hG, hn2, ?_⟩
      rcases hcl.2 with h | h
      · left; omega
      · right; omega
  · rintro ⟨hG, h2, (h1 | h1)⟩
    · refine ⟨hG, Or.inr ⟨n, rfl, h2, ?_⟩⟩
      rw [pointI_mem_closure_hEdge]; exact ⟨rfl, Or.inl (by omega)⟩
    · refine ⟨hG, Or.inr ⟨n, rfl, h2, ?_⟩⟩
      rw [pointI_mem_closure_hEdge]; exact ⟨rfl, Or.inr (by omega)⟩

/-! ## Parity across vertical edges — the key result -/

/-- `evenCell G (squ m)` simplifies to `Even (numLower G m)`.
    HOL Light: `even_cell_squ` (line 3305). -/
theorem evenCell_squ_iff (G : Finset (Set E2)) (m : ℤ × ℤ) :
    evenCell G (squ m) → Even (numLower G m) :=
  (even_cell_squ G m).mp

/-- **targetSet cardinality decomposition**: When `vEdge m ∉ G`, `targetSet` contains only
    hEdges from `setLower G m` and `setLower G (left m)`, and its cardinality equals
    `numLower G m + numLower G (left m)`.
    When `vEdge m ∈ G`, it's one more. -/
private theorem targetSet_card_eq (G : Finset (Set E2)) (m : ℤ × ℤ) :
    (targetSet G m).card = numLower G m + numLower G (left m) +
      if vEdge m ∈ G then 1 else 0 := by
  classical
  -- Define three sub-finsets of G
  let A := G.filter (fun e => ∃ k : ℤ, k ≤ m.2 ∧ e = hEdge (m.1, k))
  let B := G.filter (fun e => ∃ k : ℤ, k ≤ m.2 ∧ e = hEdge (m.1 - 1, k))
  let C := G.filter (fun e => e = vEdge m ∧ vEdge m ∈ G)
  -- Step 1: targetSet G m = A ∪ B ∪ C
  have hTS : targetSet G m = A ∪ B ∪ C := by
    ext e; simp only [targetSet, Finset.mem_filter, Finset.mem_union, A, B, C]
    constructor
    · rintro ⟨hG, (⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩ | hv)⟩
      · have hmem : n ∈ setLower G m := hn
        unfold setLower at hmem
        left; left; exact ⟨hG, n.2, hmem.2.2, by congr 1; ext <;> simp [hmem.2.1]⟩
      · have hmem : n ∈ setLower G (left m) := hn
        unfold setLower left at hmem
        left; right; exact ⟨hG, n.2, hmem.2.2, by congr 1; ext <;> simp [hmem.2.1]⟩
      · right; exact ⟨hG, hv⟩
    · rintro ((⟨hG, k, hk, rfl⟩ | ⟨hG, k, hk, rfl⟩) | ⟨hG, heq, hv⟩)
      · refine ⟨hG, Or.inl ⟨(m.1, k), rfl, ?_⟩⟩
        show (m.1, k) ∈ setLower G m
        exact ⟨hG, rfl, hk⟩
      · refine ⟨hG, Or.inr (Or.inl ⟨(m.1 - 1, k), rfl, ?_⟩)⟩
        show (m.1 - 1, k) ∈ setLower G (left m)
        exact ⟨hG, rfl, hk⟩
      · exact ⟨hG, Or.inr (Or.inr ⟨heq, hv⟩)⟩
  -- Step 2: A, B, C are pairwise disjoint
  have hAB : Disjoint A B := by
    apply Finset.disjoint_filter.mpr
    intro e _
    rintro ⟨k, _, rfl⟩ ⟨k', _, hek'⟩
    have h := (hEdge_inj _ _).mp hek'
    simp only [Prod.mk.injEq] at h; omega
  have hAC : Disjoint A C := by
    apply Finset.disjoint_filter.mpr
    intro e _
    rintro ⟨_, _, rfl⟩ ⟨heq, _⟩
    exact hEdge_ne_vEdge _ _ heq
  have hBC : Disjoint B C := by
    apply Finset.disjoint_filter.mpr
    intro e _
    rintro ⟨_, _, rfl⟩ ⟨heq, _⟩
    exact hEdge_ne_vEdge _ _ heq
  have hABC : Disjoint (A ∪ B) C :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  -- Step 3: Compute cardinality
  rw [hTS, Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB]
  -- Goal: A.card + B.card + C.card = numLower G m + numLower G (left m) + ite ...
  -- A and numLower G m are both card of the same filter, so A.card = numLower G m
  -- Similarly for B. C is 0 or 1 based on membership.
  suffices hAB_eq : A.card + B.card = numLower G m + numLower G (left m) by
    suffices hC_eq : C.card = if vEdge m ∈ G then 1 else 0 by omega
    split
    · next hv =>
      have hCeq : C = {vEdge m} := by
        ext e; constructor
        · intro he
          have : e ∈ G ∧ (e = vEdge m ∧ vEdge m ∈ G) := Finset.mem_filter.mp he
          exact Finset.mem_singleton.mpr this.2.1
        · intro he
          have := Finset.mem_singleton.mp he
          exact Finset.mem_filter.mpr ⟨this ▸ hv, this, hv⟩
      rw [hCeq, Finset.card_singleton]
    · next hv =>
      have hCeq : C = ∅ := by
        ext e; constructor
        · intro he
          exact absurd (Finset.mem_filter.mp he).2.2 hv
        · intro he; exact absurd he (Finset.notMem_empty e)
      rw [hCeq, Finset.card_empty]
  -- A.card = numLower G m and B.card = numLower G (left m)
  -- These are definitionally equal
  rfl

/-- numLower "step": adding one row adds at most one hEdge.
    `numLower G (c, j) = numLower G (c, j-1) + if hEdge (c,j) ∈ G then 1 else 0`. -/
theorem numLower_step (G : Finset (Set E2)) (c j : ℤ) :
    numLower G (c, j) = numLower G (c, j - 1) + if hEdge (c, j) ∈ G then 1 else 0 := by
  classical
  simp only [numLower]
  -- Split the filter {e ∈ G | ∃ k ≤ j, e = hEdge(c,k)} into
  -- {e ∈ G | ∃ k ≤ j-1, e = hEdge(c,k)} ∪ (if hEdge(c,j) ∈ G then {hEdge(c,j)} else ∅)
  have hsplit : ∀ e : Set E2, (∃ k : ℤ, k ≤ j ∧ e = hEdge (c, k)) ↔
      (∃ k : ℤ, k ≤ j - 1 ∧ e = hEdge (c, k)) ∨ e = hEdge (c, j) := by
    intro e; constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases hkj : k ≤ j - 1
      · exact Or.inl ⟨k, hkj, rfl⟩
      · have : k = j := by omega
        subst this; exact Or.inr rfl
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨j, le_refl j, rfl⟩
  -- Factor the filter using this split
  have hfilt_eq : G.filter (fun e => ∃ k : ℤ, k ≤ j ∧ e = hEdge (c, k)) =
      G.filter (fun e => ∃ k : ℤ, k ≤ j - 1 ∧ e = hEdge (c, k)) ∪
      G.filter (fun e => e = hEdge (c, j)) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hG, h⟩
      rcases (hsplit e).mp h with h1 | h2
      · exact Or.inl ⟨hG, h1⟩
      · exact Or.inr ⟨hG, h2⟩
    · rintro (⟨hG, h1⟩ | ⟨hG, h2⟩)
      · exact ⟨hG, (hsplit e).mpr (Or.inl h1)⟩
      · exact ⟨hG, (hsplit e).mpr (Or.inr h2)⟩
  -- The two parts are disjoint
  have hdisj : Disjoint (G.filter (fun e => ∃ k : ℤ, k ≤ j - 1 ∧ e = hEdge (c, k)))
      (G.filter (fun e => e = hEdge (c, j))) := by
    apply Finset.disjoint_filter.mpr
    intro e _
    rintro ⟨k, hk, rfl⟩ heq
    have := (hEdge_inj _ _).mp heq
    simp only [Prod.mk.injEq] at this; omega
  rw [hfilt_eq, Finset.card_union_of_disjoint hdisj]
  -- The second filter has card 0 or 1
  congr 1
  split
  · next hm =>
    have : G.filter (fun e => e = hEdge (c, j)) = {hEdge (c, j)} := by
      ext e; simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ hm, h⟩⟩
    rw [this, Finset.card_singleton]
  · next hm =>
    have : G.filter (fun e => e = hEdge (c, j)) = ∅ := by
      ext e; constructor
      · intro he; exact absurd (Finset.mem_filter.mp he).2 (by
          rcases Finset.mem_filter.mp he with ⟨hG, heq⟩
          rw [heq] at hG; exact absurd hG hm)
      · intro he; exact absurd he (Finset.notMem_empty e)
    rw [this, Finset.card_empty]

/-- `numClosure G m` equals the sum of four indicator functions for the four
    edges incident to the lattice point `m`. -/
private theorem numClosure_indicators (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) (m : ℤ × ℤ) :
    numClosure G m =
      (if hEdge (m.1 - 1, m.2) ∈ G then 1 else 0) +
      (if hEdge m ∈ G then 1 else 0) +
      (if vEdge (m.1, m.2 - 1) ∈ G then 1 else 0) +
      (if vEdge m ∈ G then 1 else 0) := by
  classical
  simp only [numClosure, incidentEdges]
  have hfilt : G.filter (fun e => pointI m ∈ closure e) =
      G.filter (fun e => e = hEdge (m.1 - 1, m.2) ∨ e = hEdge m ∨
        e = vEdge (m.1, m.2 - 1) ∨ e = vEdge m) := by
    ext e; simp only [Finset.mem_filter, and_congr_right_iff]
    exact fun he => incident_edges_characterize G hG m e he
  rw [hfilt, Finset.filter_or, Finset.filter_or, Finset.filter_or]
  set A := G.filter (fun e => e = hEdge (m.1 - 1, m.2))
  set B := G.filter (fun e => e = hEdge m)
  set C := G.filter (fun e => e = vEdge (m.1, m.2 - 1))
  set D := G.filter (fun e => e = vEdge m)
  have card_ite : ∀ (x : Set E2), (G.filter (fun e => e = x)).card =
      if x ∈ G then 1 else 0 := by
    intro x; rw [Finset.filter_eq']; split
    · exact Finset.card_singleton x
    · exact Finset.card_empty
  have disj : ∀ (x y : Set E2), x ≠ y →
      Disjoint (G.filter (fun e => e = x)) (G.filter (fun e => e = y)) :=
    fun x y hne => Finset.disjoint_filter.mpr fun e _ h1 h2 => hne (h1 ▸ h2)
  have hne_hh : hEdge (m.1 - 1, m.2) ≠ hEdge m := by
    intro h; have := (hEdge_inj _ _).mp h; simp [Prod.ext_iff] at this
  have hne_vv : vEdge (m.1, m.2 - 1) ≠ vEdge m := by
    intro h; have := (vEdge_inj _ _).mp h; simp [Prod.ext_iff] at this
  have hCD : Disjoint C D := disj _ _ hne_vv
  have hBCD : Disjoint B (C ∪ D) :=
    Finset.disjoint_union_right.mpr ⟨disj _ _ (hEdge_ne_vEdge _ _),
      disj _ _ (hEdge_ne_vEdge _ _)⟩
  have hABCD : Disjoint A (B ∪ (C ∪ D)) :=
    Finset.disjoint_union_right.mpr ⟨disj _ _ hne_hh,
      Finset.disjoint_union_right.mpr ⟨disj _ _ (hEdge_ne_vEdge _ _),
        disj _ _ (hEdge_ne_vEdge _ _)⟩⟩
  rw [Finset.card_union_of_disjoint hABCD, Finset.card_union_of_disjoint hBCD,
      Finset.card_union_of_disjoint hCD, card_ite, card_ite, card_ite, card_ite]
  omega

/-- For any finite set of edges, there exists a row strictly below all
    edge coordinates. -/
private lemma exists_below_all_edges (G : Finset (Set E2))
    (hG : ∀ e ∈ G, isEdge e) :
    ∃ j₀ : ℤ, ∀ e ∈ G, ∀ n : ℤ × ℤ,
      (e = hEdge n ∨ e = vEdge n) → j₀ < n.2 := by
  classical
  induction G using Finset.cons_induction with
  | empty => exact ⟨0, fun e he => absurd he (Finset.notMem_empty e)⟩
  | cons a s ha ih =>
    have hG_s : ∀ e ∈ s, isEdge e :=
      fun e he => hG e (Finset.mem_cons.mpr (Or.inr he))
    obtain ⟨j₀, hj₀⟩ := ih hG_s
    have ha_edge := hG a (Finset.mem_cons.mpr (Or.inl rfl))
    rcases ha_edge with ⟨m, rfl⟩ | ⟨m, rfl⟩
    all_goals refine ⟨min j₀ (m.2 - 1), fun e he n hn => ?_⟩
    all_goals rcases Finset.mem_cons.mp he with rfl | he_s
    · rcases hn with ⟨heq⟩ | ⟨heq⟩
      · have := (hEdge_inj _ _).mp heq; simp [Prod.ext_iff] at this; omega
      · exact absurd heq (hEdge_ne_vEdge _ _)
    · exact lt_of_le_of_lt (min_le_left _ _) (hj₀ e he_s n hn)
    · rcases hn with ⟨heq⟩ | ⟨heq⟩
      · exact absurd heq.symm (hEdge_ne_vEdge _ _)
      · have := (vEdge_inj _ _).mp heq; simp [Prod.ext_iff] at this; omega
    · exact lt_of_le_of_lt (min_le_left _ _) (hj₀ e he_s n hn)

/-- Below all edge coordinates, the target set is empty. -/
private lemma targetSet_empty_below (G : Finset (Set E2)) (c j : ℤ)
    (hbelow : ∀ e ∈ G, ∀ n : ℤ × ℤ,
      (e = hEdge n ∨ e = vEdge n) → j < n.2) :
    (targetSet G (c, j)).card = 0 := by
  rw [Finset.card_eq_zero]; apply Finset.subset_empty.mp
  intro e he
  simp only [targetSet, Finset.mem_filter] at he
  rcases he.2 with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩ | ⟨rfl, hv⟩
  · simp only [setLower, Set.mem_setOf_eq] at hn
    exact absurd hn.2.2 (by have := hbelow _ he.1 n (Or.inl rfl); omega)
  · simp only [setLower, Set.mem_setOf_eq, left] at hn
    exact absurd hn.2.2 (by have := hbelow _ he.1 n (Or.inl rfl); omega)
  · exact absurd (hbelow _ hv (c, j) (Or.inr rfl)) (by omega)

/-- The target set has even cardinality.
    HOL Light: `target_set_even` (line 7197).

    Proof by row induction using `Int.inductionOn'`. The key step: going from
    row `j-1` to row `j`, the change in `|targetSet|` has the same parity as
    `numClosure R.edges (c,j)`, which is always even for a rectagon. -/
theorem targetSet_even (R : Rectagon) (m : ℤ × ℤ) :
    Even (targetSet R.edges m).card := by
  -- Suffices to show for all j with fixed column c = m.1
  suffices h : ∀ j : ℤ, Even (targetSet R.edges (m.1, j)).card by
    have := h m.2; rwa [Prod.mk.eta] at this
  -- Step lemma: parity at row j equals parity at row j-1
  have step : ∀ j : ℤ,
      Even (targetSet R.edges (m.1, j)).card ↔
      Even (targetSet R.edges (m.1, j - 1)).card := by
    intro j
    rw [targetSet_card_eq, targetSet_card_eq]
    simp only [left]
    rw [numLower_step R.edges m.1 j, numLower_step R.edges (m.1 - 1) j]
    set a := numLower R.edges (m.1, j - 1)
    set b := numLower R.edges (m.1 - 1, j - 1)
    set h1 := if hEdge (m.1, j) ∈ R.edges then 1 else 0
    set h2 := if hEdge (m.1 - 1, j) ∈ R.edges then 1 else 0
    set v1 := if vEdge (m.1, j) ∈ R.edges then 1 else 0
    set v0 := if vEdge (m.1, j - 1) ∈ R.edges then 1 else 0
    -- The rectagon has even degree at vertex (m.1, j)
    have hdeg := R.even_degree (m.1, j)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdeg
    have hcount : numClosure R.edges (m.1, j) = h2 + h1 + v0 + v1 :=
      numClosure_indicators R.edges R.all_edges (m.1, j)
    -- The sum h2 + h1 + v0 + v1 is even (0 or 2)
    have hsum_even : Even (h2 + h1 + v0 + v1) := by
      rcases hdeg with h0 | h2eq
      · rw [hcount] at h0; exact ⟨0, by omega⟩
      · rw [hcount] at h2eq; exact ⟨1, by omega⟩
    -- Key parity fact: Even(h1+h2+v1) ↔ Even(v0)
    have key : Even (h1 + h2 + v1) ↔ Even v0 := by
      have htot : Even ((h1 + h2 + v1) + v0) := by
        have : h1 + h2 + v1 + v0 = h2 + h1 + v0 + v1 := by omega
        rw [this]; exact hsum_even
      exact Nat.even_add.mp htot
    -- Rewrite LHS and RHS to separate the common (a+b) from the indicator sums
    have lhs_eq : (a + h1) + (b + h2) + v1 = (a + b) + (h1 + h2 + v1) := by
      omega
    have rhs_eq : a + b + v0 = (a + b) + v0 := by omega
    rw [lhs_eq, rhs_eq]
    constructor
    · intro he; rw [Nat.even_add] at he ⊢; exact he.trans key
    · intro he; rw [Nat.even_add] at he ⊢; exact he.trans key.symm
  -- Find a base row below all edges
  obtain ⟨j₀, hj₀⟩ := exists_below_all_edges R.edges R.all_edges
  have hbase : Even (targetSet R.edges (m.1, j₀)).card := by
    rw [targetSet_empty_below R.edges m.1 j₀ hj₀]; exact ⟨0, rfl⟩
  -- Use Int.inductionOn' from base j₀ to any j
  intro j
  exact Int.inductionOn' j j₀ hbase
    (fun k _ hk => by
      have := (step (k + 1)).mpr; simp only [show k + 1 - 1 = k from by omega] at this
      exact this hk)
    (fun k _ hk => (step k).mp hk)

/-- **THE KEY RESULT**: Parity is preserved across a vertical edge iff
    the vertical edge is NOT in the rectagon.
    HOL Light: `squ_left_par` (line 7350).
    Follows from `squ_left_even` + `squ_left_odd`. -/
theorem squ_left_par (R : Rectagon) (m : ℤ × ℤ) :
    (evenCell R.edges (squ (left m)) ↔ evenCell R.edges (squ m)) ↔
      vEdge m ∉ R.edges := by
  constructor
  · -- If parities agree, then vEdge m ∉ R.edges
    -- Contrapositive: if vEdge m ∈ R.edges, parities disagree
    intro hpar hv
    -- vEdge m ∈ R.edges
    -- By targetSet_card_eq and targetSet_even:
    -- |targetSet| = numLower m + numLower (left m) + 1 is even
    -- So numLower m + numLower (left m) is odd
    -- But hpar says Even(numLower(left m)) ↔ Even(numLower m)
    -- i.e., Even(numLower(left m) + numLower m), contradiction with odd.
    have hcard := targetSet_card_eq R.edges m
    have heven := targetSet_even R m
    rw [hcard, if_pos hv] at heven
    rw [even_cell_squ, even_cell_squ] at hpar
    have hS : Even (numLower R.edges (left m) + numLower R.edges m) :=
      Nat.even_add.mpr hpar
    -- heven : Even(numLower m + numLower (left m) + 1), hS : Even(numLower (left m) + numLower m)
    -- Derive False: (a + b + 1) even and (b + a) even is impossible
    obtain ⟨k, hk⟩ := hS
    obtain ⟨j, hj⟩ := heven
    omega
  · -- If vEdge m ∉ R.edges, then parities agree
    intro hv
    -- |targetSet| = numLower m + numLower (left m) + 0 is even
    -- So numLower m + numLower (left m) is even
    -- By Nat.even_add: Even(numLower(left m)) ↔ Even(numLower m)
    have hcard := targetSet_card_eq R.edges m
    have heven := targetSet_even R m
    rw [hcard, if_neg hv, Nat.add_zero] at heven
    rw [even_cell_squ, even_cell_squ]
    rw [Nat.add_comm] at heven
    exact Nat.even_add.mp heven

/-- Crossing a vertical edge does not change parity when the edge is NOT in G.
    HOL Light: `squ_left_even` (line 7305). Follows from squ_left_par. -/
theorem squ_left_even (R : Rectagon) (m : ℤ × ℤ)
    (hm : vEdge m ∉ R.edges) :
    evenCell R.edges (squ (left m)) ↔ evenCell R.edges (squ m) :=
  (squ_left_par R m).mpr hm

/-- Crossing a vertical edge flips parity when the edge IS in G.
    HOL Light: `squ_left_odd` (line 7330). Follows from squ_left_par. -/
theorem squ_left_odd (R : Rectagon) (m : ℤ × ℤ)
    (hm : vEdge m ∈ R.edges) :
    ¬(evenCell R.edges (squ (left m)) ↔ evenCell R.edges (squ m)) :=
  fun h => absurd hm ((squ_left_par R m).mp h)

end
