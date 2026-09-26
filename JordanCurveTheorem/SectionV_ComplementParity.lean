/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionU_Grid33

/-!
# Section V: Complement Topology for Segments
## HOL Light: Section V (Lines 42260–44059)

2-connectedness properties and the relationship between complement
topology and parity. Key results include star avoidance lemmas,
bounded/unbounded triple avoidance, and `bounded_triple_inner_union`.
-/

open Set Metric Topology Function

namespace JordanCurveTheorem

noncomputable section

/-! ## §V.1 Parity complement and closure -/

/-- HOL Light: `euclid_diff_par_cell` (line 42265).
The complement of one parity region equals the other parity region union
the curve cells. -/
theorem euclid_diff_parCell (G : Segment) (eps : Bool) :
    (Set.univ : Set E2) \ ⋃₀ {C | parCell (!eps) G.edges C} =
      ⋃₀ {C | parCell eps G.edges C} ∪ ⋃₀ (curveCells G.edges : Set (Set E2)) := by
  ext x; constructor
  · intro ⟨_, hx_not⟩
    -- x ∈ complementCurve G ∨ x ∈ ⋃₀ curveCells G
    by_cases hcurve : x ∈ ⋃₀ (curveCells G.edges : Set (Set E2))
    · exact Set.mem_union_right _ hcurve
    · -- x ∈ complementCurve G, so by parCell_partition x is in parCell eps or parCell (!eps)
      have hcomp : x ∈ complementCurve G.edges := by
        rw [complementCurve, Set.mem_compl_iff]; exact hcurve
      rw [← parCell_partition G eps] at hcomp
      rcases hcomp with h | h
      · exact Set.mem_union_left _ h
      · exact absurd h hx_not
  · intro hx
    refine ⟨Set.mem_univ _, ?_⟩
    rcases hx with heps | hcurve
    · -- x ∈ ⋃₀ parCell eps G, disjoint from ⋃₀ parCell (!eps) G
      intro habs
      exact Set.eq_empty_iff_forall_notMem.mp
        (parCell_union_disjoint G.edges eps) x ⟨heps, habs⟩
    · -- x ∈ ⋃₀ curveCells G, disjoint from ⋃₀ parCell (!eps) G
      intro habs
      exact Set.eq_empty_iff_forall_notMem.mp
        (sUnion_parCell_inter_curveCells_empty G.edges G.all_edges (!eps)) x
        ⟨habs, hcurve⟩

/-- HOL Light: `par_cell_closure_cell` (line 42313).
If a cell `d` is contained in the closure of a parity cell `C`,
then `d` has the same parity or is a curve cell. -/
theorem parCell_closure_cell (G : Rectagon) (C d : Set E2) (eps : Bool)
    (_hC : isCell C) (hd : isCell d)
    (hd_sub : d ⊆ closure C)
    (hpar : parCell eps G.edges C) :
    parCell eps G.edges d ∨ d ∈ curveCells G.edges := by
  rcases parCell_cell_partition_segment G.toSegment eps d hd with h | h | h
  · exact Or.inl h
  · -- parCell (!eps) G d: contradiction
    exfalso
    -- C ⊆ ⋃₀ parCell eps G ⊆ (⋃₀ parCell (!eps) G)ᶜ
    have hC_sub : C ⊆ (⋃₀ {C | parCell (!eps) G.edges C})ᶜ := by
      intro z hz
      rw [Set.mem_compl_iff]; intro habs
      exact Set.eq_empty_iff_forall_notMem.mp
        (parCell_union_disjoint G.edges eps) z
        ⟨Set.mem_sUnion.mpr ⟨C, hpar, hz⟩, habs⟩
    -- closure C ⊆ (⋃₀ parCell (!eps) G)ᶜ since (⋃₀ parCell (!eps) G)ᶜ is closed
    have hclosed : IsClosed (⋃₀ {C | parCell (!eps) G.edges C})ᶜ :=
      (parCell_open G (!eps)).isClosed_compl
    have hcl_sub : closure C ⊆ (⋃₀ {C | parCell (!eps) G.edges C})ᶜ :=
      closure_minimal hC_sub hclosed
    -- d ⊆ closure C ⊆ (⋃₀ parCell (!eps) G)ᶜ, but d ⊆ ⋃₀ parCell (!eps) G
    have hd_in : d ⊆ ⋃₀ {C | parCell (!eps) G.edges C} :=
      fun z hz => Set.mem_sUnion.mpr ⟨d, h, hz⟩
    obtain ⟨u, hu⟩ := cell_nonempty hd
    exact (hcl_sub (hd_sub hu)) (hd_in hu)
  · exact Or.inr h

/-- HOL Light: `rectagon_curve` (line 42381).
A simple arc avoiding curve cells lies in a single component. -/
theorem rectagon_curve (G : Finset (Set E2))
    (_hGedge : ∀ e ∈ G, isEdge e)
    (C : Set E2) (a b : E2) (harc : IsSimpleArcEnd C a b)
    (hdisj : C ∩ ⋃₀ (curveCells G : Set (Set E2)) = ∅) :
    C ⊆ connectedComponentIn (complementCurve G) a := by
  have hC_sub : C ⊆ complementCurve G := by
    intro z hz
    rw [complementCurve, Set.mem_compl_iff]
    exact fun habs => Set.eq_empty_iff_forall_notMem.mp hdisj z ⟨hz, habs⟩
  have ha_mem : a ∈ C := isSimpleArcEnd_mem_left harc
  have hC_pc : IsPreconnected C :=
    (simpleArc_isConnected C (isSimpleArcEnd_isSimpleArc harc)).2
  exact hC_pc.subset_connectedComponentIn ha_mem hC_sub

/-- HOL Light: `curve_cell_imp_subset` (line 42489).
Monotonicity of curve cells. -/
theorem curveCells_mono {A B : Finset (Set E2)} (h : A ⊆ B) :
    (curveCells A : Set (Set E2)) ⊆ curveCells B := by
  have : B = A ∪ (B \ A) := by ext x; simp [Finset.mem_union]; tauto
  rw [this, curveCells_union]
  exact Set.subset_union_left

/-! ## §V.2 Star avoidance -/

/-- HOL Light: `star_avoidance_lemma1` (line 42410).
Under rectagon inclusion and parity constraints, a bounded point in `E`
is either bounded or unbounded in `E' \ B`. -/
theorem star_avoidance_lemma1 (E E' : Finset (Set E2)) (R : Rectagon)
    (B : Finset (Set E2)) (x : E2)
    (_hbnd : BoundedSet E x)
    (_hEE' : E ⊆ E') (hE'edge : ∀ e ∈ E', isEdge e)
    (_hR : R.edges ⊆ E)
    (_hnotcurveB : x ∉ ⋃₀ (curveCells B : Set (Set E2)))
    (_hBpar : ∀ e ∈ B, parCell false R.edges e)
    (hnotcurveE' : x ∉ ⋃₀ (curveCells E' : Set (Set E2))) :
    BoundedSet (E' \ B) x ∨ UnboundedSet (E' \ B) x := by
  -- x ∈ complementCurve (E' \ B) because curveCells (E' \ B) ⊆ curveCells E'
  have hx_comp : x ∈ complementCurve (E' \ B) := by
    rw [complementCurve, Set.mem_compl_iff]
    intro hmem
    exact hnotcurveE' (Set.sUnion_mono (curveCells_mono Finset.sdiff_subset) hmem)
  exact bounded_unbounded_union (E' \ B)
    (fun e he => hE'edge e (Finset.mem_sdiff.mp he).1) hx_comp

/-- HOL Light: `unbound_set_x_axis` (line 42502).
Points far enough along the x-axis are unbounded. -/
theorem unboundedSet_x_axis (G : Finset (Set E2))
    (hedge : ∀ e ∈ G, isEdge e) :
    ∃ r : ℝ, ∀ s : ℝ, r ≤ s → UnboundedSet G (point (s, 0)) := by
  obtain ⟨u, hu⟩ := unboundedSet_nonempty G hedge
  have hr := hu
  obtain ⟨r, hr⟩ := hr
  exact ⟨r, fun s hs => unboundedSet_comp_elt G hedge hu (hr s hs)⟩

/-- HOL Light: `star_avoidance` (line 42515).
If `E' \ B` is unbounded at `x`, then `E` is unbounded at `x`
(under rectagon/parity constraints). -/
theorem star_avoidance (E E' : Finset (Set E2)) (R : Rectagon)
    (B : Finset (Set E2)) (x : E2)
    (hunbnd : UnboundedSet (E' \ B) x)
    (hEE' : E ⊆ E') (hE'edge : ∀ e ∈ E', isEdge e)
    (hR : R.edges ⊆ E)
    (hBedge : ∀ e ∈ B, isEdge e)
    (hnotcurveB : x ∉ ⋃₀ (curveCells B : Set (Set E2)))
    (hBpar : ∀ e ∈ B, parCell false R.edges e)
    (hnotcurveE' : x ∉ ⋃₀ (curveCells E' : Set (Set E2))) :
    UnboundedSet E x := by
  set E'' := E' \ B with hE''def
  have hE''edge : ∀ e ∈ E'', isEdge e := fun e he => hE'edge e (Finset.mem_sdiff.mp he).1
  -- R ⊆ E'': R ⊆ E ⊆ E', and R ∩ B = ∅ because e ∈ R ∩ B gives parCell false R e,
  -- but e ∈ R.edges ∈ curveCells R, contradiction with parCell's disjointness condition
  have hR_E'' : R.edges ⊆ E'' := by
    intro e he; rw [hE''def, Finset.mem_sdiff]
    refine ⟨hEE' (hR he), fun hB => ?_⟩
    have hp := (hBpar e hB).2
    have he_curve : e ∈ curveCells R.edges :=
      (curveCells_edge R.edges e (R.all_edges e he)).mpr he
    have ⟨z, hz⟩ := cell_nonempty (curveCells_subset_cell R.edges R.all_edges e he_curve)
    exact Set.eq_empty_iff_forall_notMem.mp hp z
      ⟨hz, Set.mem_sUnion.mpr ⟨e, he_curve, hz⟩⟩
  -- Get large s where point(s,0) is in component(E'', x) and unbounded in R
  obtain ⟨rR, hrR⟩ := unboundedSet_x_axis R.edges R.all_edges
  obtain ⟨rE, hrE⟩ : ∃ r, ∀ s, r ≤ s → point (s, 0) ∈
      connectedComponentIn (complementCurve E'') x := hunbnd
  set s := max rR rE with hs_def
  have hps_comp : point (s, 0) ∈ connectedComponentIn (complementCurve E'') x :=
    hrE s (le_max_right _ _)
  have hps_unbR : UnboundedSet R.edges (point (s, 0)) := hrR s (le_max_left _ _)
  -- Auxiliary: E ⊆ E'' ∪ B
  have hE_sub : (↑E : Set (Set E2)) ⊆ ↑E'' ∪ ↑B := by
    intro e he
    by_cases hB : e ∈ B
    · exact Set.mem_union_right _ (Finset.mem_coe.mpr hB)
    · exact Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hEE' he, hB⟩))
  have hEedge : ∀ e ∈ E, isEdge e := fun e he => hE'edge e (hEE' he)
  -- Auxiliary: curveCells_sUnion_mono inline (defined later in file)
  have curveCells_sUnion_mono' : ∀ {H G : Finset (Set E2)}, H ⊆ G →
      ⋃₀ (curveCells H : Set (Set E2)) ⊆ ⋃₀ (curveCells G : Set (Set E2)) :=
    fun h => Set.sUnion_mono (curveCells_mono h)
  -- x ∉ curveCells E (since E ⊆ E' and x ∉ curveCells E')
  have hx_notcurveE : x ∉ ⋃₀ (curveCells E : Set (Set E2)) :=
    fun hmem => hnotcurveE' (curveCells_sUnion_mono' hEE' hmem)
  -- parCell_closure: curveCells B ∩ ⋃₀ parCell true R = ∅
  have hclosure := parCell_closure R B false hBedge hBpar
  have hB_T_disj : ⋃₀ (curveCells B : Set (Set E2)) ∩
      ⋃₀ {C | parCell true R.edges C} = ∅ :=
    (cell_unions_disjoint_iff
      (fun C hC => curveCells_subset_cell B hBedge C hC)
      (fun C (hC : parCell true R.edges C) => parCell_isCell hC)).mp hclosure
  -- Helper: given an arc Ct from x to some point y, avoiding curveCells E'',
  -- show Ct also avoids curveCells E (using Ct ⊆ even parity region of R).
  suffices h : ∀ t, s ≤ t →
      point (t, 0) ∈ connectedComponentIn (complementCurve E) x by
    exact ⟨s, h⟩
  intro t hts
  -- point(t,0) ∈ component(E'', x)
  have hpt_compE'' : point (t, 0) ∈ connectedComponentIn (complementCurve E'') x :=
    hrE t (le_trans (le_max_right _ _) hts)
  by_cases hxt : x = point (t, 0)
  · -- trivial: x = point(t,0)
    subst hxt; exact mem_connectedComponentIn (by
      rw [complementCurve, Set.mem_compl_iff]
      exact fun hmem => hnotcurveE' (curveCells_sUnion_mono' hEE' hmem))
  · -- x ≠ point(t,0): get arc Ct from x to point(t,0) in E''
    rw [component_simple_arc E'' hE''edge x (point (t, 0)) hxt] at hpt_compE''
    obtain ⟨Ct, hCt_arc, hCt_disj⟩ := hpt_compE''
    -- Ct avoids curveCells R (since R ⊆ E'')
    have hCt_disjR : Ct ∩ ⋃₀ (curveCells R.edges : Set (Set E2)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro z ⟨hz1, hz2⟩
      exact Set.eq_empty_iff_forall_notMem.mp hCt_disj z
        ⟨hz1, curveCells_sUnion_mono' hR_E'' hz2⟩
    -- Ct ⊆ component(R, x)
    have hCt_compR := rectagon_curve R.edges R.all_edges Ct x (point (t, 0))
      hCt_arc hCt_disjR
    -- point(t,0) ∈ component(R, x), so component(R, x) = component(R, point(t,0))
    have hpt_in_compR : point (t, 0) ∈
        connectedComponentIn (complementCurve R.edges) x :=
      hCt_compR (isSimpleArcEnd_mem_right hCt_arc)
    -- point(t,0) is unbounded in R
    have hpt_unbR : UnboundedSet R.edges (point (t, 0)) :=
      hrR t (le_trans (le_max_left _ _) hts)
    -- x is unbounded in R
    have hx_unbR : UnboundedSet R.edges x := by
      have heq := connectedComponentIn_eq hpt_in_compR
      change Unbounded (connectedComponentIn (complementCurve R.edges) x)
      rw [heq]; exact hpt_unbR
    -- Ct ⊆ component(R, x) = {unbounded in R} = ⋃₀ parCell true R
    have hCt_even : Ct ⊆ ⋃₀ {C | parCell true R.edges C} := by
      intro z hz
      have hz_comp := hCt_compR hz
      rw [unboundedSet_comp R.edges R.all_edges hx_unbR] at hz_comp
      exact (unbounded_even R).symm ▸ hz_comp
    -- Ct avoids curveCells B (curveCells B ⊆ ⋃₀ parCell false R, disjoint from even)
    have hCt_disjB : Ct ∩ ⋃₀ (curveCells B : Set (Set E2)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro z ⟨hz1, hz2⟩
      exact Set.eq_empty_iff_forall_notMem.mp hB_T_disj z ⟨hz2, hCt_even hz1⟩
    -- Ct avoids curveCells E (since curveCells E ⊆ curveCells E'' ∪ curveCells B)
    have hCt_disjE : Ct ∩ ⋃₀ (curveCells E : Set (Set E2)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro z ⟨hz1, hz2⟩
      have hEsub : E ⊆ E'' ∪ B := by
        intro e he
        by_cases hB : e ∈ B
        · exact Finset.mem_union_right _ hB
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hEE' he, hB⟩)
      have hzEB := curveCells_sUnion_mono' hEsub hz2
      rw [curveCells_union, Set.sUnion_union] at hzEB
      rcases hzEB with h | h
      · exact Set.eq_empty_iff_forall_notMem.mp hCt_disj z ⟨hz1, h⟩
      · exact Set.eq_empty_iff_forall_notMem.mp hCt_disjB z ⟨hz1, h⟩
    -- Use backward direction of component_simple_arc for E
    rw [component_simple_arc E hEedge x (point (t, 0)) hxt]
    exact ⟨Ct, hCt_arc, hCt_disjE⟩

/-- HOL Light: `star_avoidance_contrp` (line 42640).
Contrapositive: if `E` is bounded then `E' \ B` is bounded. -/
theorem star_avoidance_contrp (E E' : Finset (Set E2)) (R : Rectagon)
    (B : Finset (Set E2)) (x : E2)
    (hbnd : BoundedSet E x)
    (hEE' : E ⊆ E') (hE'edge : ∀ e ∈ E', isEdge e)
    (hR : R.edges ⊆ E)
    (hBedge : ∀ e ∈ B, isEdge e)
    (hnotcurveB : x ∉ ⋃₀ (curveCells B : Set (Set E2)))
    (hBpar : ∀ e ∈ B, parCell false R.edges e)
    (hnotcurveE' : x ∉ ⋃₀ (curveCells E' : Set (Set E2))) :
    BoundedSet (E' \ B) x := by
  rcases star_avoidance_lemma1 E E' R B x hbnd hEE' hE'edge hR
    hnotcurveB hBpar hnotcurveE' with h | h
  · exact h
  · exfalso
    exact (bounded_unbounded_disj E x).elim
      ⟨hbnd, star_avoidance E E' R B x h hEE' hE'edge hR hBedge
        hnotcurveB hBpar hnotcurveE'⟩

/-! ## §V.3 Bounded/unbounded avoidance -/

/-- HOL Light: `bounded_avoidance_subset` (line 42651).
Bounded in subset ⟹ bounded in superset (with `conn2` and no curve cells). -/
theorem bounded_avoidance_subset (E E' : Finset (Set E2)) (x : E2)
    (hbnd : BoundedSet E x)
    (hEE' : E ⊆ E') (hE'edge : ∀ e ∈ E', isEdge e)
    (hconn : conn2 E)
    (hnotcurve : x ∉ ⋃₀ (curveCells E' : Set (Set E2))) :
    BoundedSet E' x := by
  have hEedge : ∀ e ∈ E, isEdge e := fun e he => hE'edge e (hEE' he)
  obtain ⟨B, hBE, R, hR⟩ := conn2_has_rectagon hEedge hconn
  have hRE : R.edges ⊆ E := hR ▸ hBE
  have h := star_avoidance_contrp E E' R ∅ x hbnd hEE' hE'edge hRE
    (fun _ h => absurd h (by simp))
    (by simp [curveCells_empty])
    (fun _ h => absurd h (by simp)) hnotcurve
  rwa [Finset.sdiff_empty] at h

/-- HOL Light: `unbounded_avoidance_subset` (line 42667).
Unbounded in superset ⟹ unbounded in subset (with `conn2`). -/
theorem unbounded_avoidance_subset (E E' : Finset (Set E2)) (x : E2)
    (hunbnd : UnboundedSet E' x)
    (hEE' : E ⊆ E') (hE'edge : ∀ e ∈ E', isEdge e)
    (hconn : conn2 E)
    (hnotcurve : x ∉ ⋃₀ (curveCells E' : Set (Set E2))) :
    UnboundedSet E x := by
  have hEedge : ∀ e ∈ E, isEdge e := fun e he => hE'edge e (hEE' he)
  obtain ⟨B, hBE, R, hR⟩ := conn2_has_rectagon hEedge hconn
  have hRE : R.edges ⊆ E := hR ▸ hBE
  have hunbnd' : UnboundedSet (E' \ ∅) x := by rwa [Finset.sdiff_empty]
  exact star_avoidance E E' R ∅ x hunbnd' hEE' hE'edge hRE
    (fun _ h => absurd h (by simp))
    (by simp [curveCells_empty])
    (fun _ h => absurd h (by simp)) hnotcurve

/-! ## §V.4 Set-theoretic lemmas -/

/-- HOL Light: `diff_unchange` (line 42680).
`A \ B = A ↔ A ∩ B = ∅` -/
theorem diff_unchange {α : Type*} (A B : Set α) :
    A \ B = A ↔ A ∩ B = ∅ :=
  sdiff_eq_left.trans disjoint_iff_inter_eq_empty

/-- HOL Light: `union_diff2` (line 42694).
`(A ∪ B) \ A = B \ A` -/
theorem union_diff2 {α : Type*} (A B : Set α) :
    (A ∪ B) \ A = B \ A := by
  ext x; simp only [Set.mem_diff, Set.mem_union]; tauto

/-! ## §V.5 Triple avoidance -/

/-- HOL Light: `unbounded_triple_avoidance` (line 42704).
If `A ⊆ parCell false (B ∪ C)` and `x` is unbounded in `B ∪ C`,
then `x` is unbounded in `A ∪ B ∪ C`. -/
theorem unbounded_triple_avoidance (A B C : Finset (Set E2)) (x : E2)
    (htrip : isPsegmentTriple A B C)
    (hA : ∀ e ∈ A, parCell false (B ∪ C) e)
    (hunbnd : UnboundedSet (B ∪ C) x) :
    UnboundedSet (A ∪ B ∪ C) x := by
  -- Extract data from isPsegmentTriple
  obtain ⟨⟨sA, hsA, hpA⟩, ⟨sB, hsB, hpB⟩, ⟨sC, hsC, hpC⟩,
    ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
    hABdisj, hACdisj, hBCdisj, _⟩ := htrip
  -- Auxiliary edge facts
  have hAedge : ∀ e ∈ A, isEdge e := fun e he => sA.all_edges e (hsA ▸ he)
  have hBCedge : ∀ e ∈ B ∪ C, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · exact sB.all_edges e (hsB ▸ h)
    · exact sC.all_edges e (hsC ▸ h)
  have hE'edge : ∀ e ∈ A ∪ B ∪ C, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact sA.all_edges e (hsA ▸ h')
      · exact sB.all_edges e (hsB ▸ h')
    · exact sC.all_edges e (hsC ▸ h)
  -- (A ∪ B ∪ C) \ A = B ∪ C
  have hsdiff : (A ∪ B ∪ C) \ A = B ∪ C := by
    ext e; constructor
    · intro he
      have ⟨hmem, hnotA⟩ := Finset.mem_sdiff.mp he
      rcases Finset.mem_union.mp hmem with hab | hc
      · rcases Finset.mem_union.mp hab with ha | hb
        · exact absurd ha hnotA
        · exact Finset.mem_union.mpr (Or.inl hb)
      · exact Finset.mem_union.mpr (Or.inr hc)
    · intro he
      rcases Finset.mem_union.mp he with hb | hc
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hb))),
           Finset.disjoint_right.mp hABdisj hb⟩
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union.mpr (Or.inr hc),
           Finset.disjoint_right.mp hACdisj hc⟩
  -- R = rBC with edges B ∪ C
  have hR : rBC.edges ⊆ A ∪ B ∪ C := by
    rw [hrBC]; intro e he
    rcases Finset.mem_union.mp he with hb | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hb)))
    · exact Finset.mem_union.mpr (Or.inr hc)
  have hBpar' : ∀ e ∈ A, parCell false rBC.edges e := fun e he => hrBC ▸ hA e he
  -- x ∉ ⋃₀ curveCells A: by parCell_closure + unbounded_even
  have hnotcurveA : x ∉ ⋃₀ (curveCells A : Set (Set E2)) := by
    intro hmem
    have hcl := parCell_closure rBC A false hAedge (fun e he => hBpar' e he)
    simp only [Bool.not_false] at hcl
    have hdisjU := (cell_unions_disjoint_iff
      (curveCells_subset_cell A hAedge)
      (fun D hD => parCell_isCell (hD : parCell true rBC.edges D))).mp hcl
    have hunbnd_rBC : UnboundedSet rBC.edges x := hrBC ▸ hunbnd
    have hxinpar : x ∈ ⋃₀ {D | parCell true rBC.edges D} :=
      (unbounded_even rBC).symm ▸ hunbnd_rBC
    exact Set.eq_empty_iff_forall_notMem.mp hdisjU x ⟨hmem, hxinpar⟩
  -- x ∉ ⋃₀ curveCells (A ∪ B ∪ C)
  have hnotcurveE' : x ∉ ⋃₀ (curveCells (A ∪ B ∪ C) : Set (Set E2)) := by
    rw [show A ∪ B ∪ C = A ∪ (B ∪ C) from Finset.union_assoc A B C,
      curveCells_union, Set.sUnion_union]
    intro hmem; rcases hmem with hA' | hBC'
    · exact hnotcurveA hA'
    · have hdisjBC := sUnion_parCell_inter_curveCells_empty (B ∪ C) hBCedge true
      have hxinpar : x ∈ ⋃₀ {D | parCell true (↑(B ∪ C)) D} := by
        rw [← hrBC]; exact (unbounded_even rBC).symm ▸ (hrBC ▸ hunbnd)
      exact Set.eq_empty_iff_forall_notMem.mp hdisjBC x ⟨hxinpar, hBC'⟩
  rw [← hsdiff] at hunbnd
  exact star_avoidance (A ∪ B ∪ C) (A ∪ B ∪ C) rBC A x hunbnd
    (Finset.Subset.refl _) hE'edge (hrBC ▸ hR) hAedge hnotcurveA
    (hrBC ▸ hBpar') hnotcurveE'

/-- HOL Light: `unbounded_set_comp_elt_eq` (line 42779).
If `x` is unbounded, the unbounded set equals the component of `x`. -/
theorem unboundedSet_comp_elt_eq (G : Finset (Set E2))
    (hGedge : ∀ e ∈ G, isEdge e)
    (x : E2) (hx : UnboundedSet G x) :
    {y | UnboundedSet G y} = connectedComponentIn (complementCurve G) x :=
  (unboundedSet_comp G hGedge hx).symm

/-- HOL Light: `outer_segment_even` (line 42791).
If `A ⊆ parCell false (B ∪ C)` then `C ⊆ parCell true (A ∪ B)`. -/
theorem outer_segment_even (A B C : Finset (Set E2))
    (htrip : isPsegmentTriple A B C)
    (hA : ∀ e ∈ A, parCell false (B ∪ C) e) :
    ∀ e ∈ C, parCell true (A ∪ B) e := by
  -- Extract triple data, keep htrip intact for later use
  have htrip' := htrip
  obtain ⟨⟨sA, hsA, hpA⟩, ⟨sB, hsB, hpB⟩, ⟨sC, hsC, hpC⟩,
    ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
    hABdisj, hACdisj, hBCdisj, _, hcls2, hcls3, hend1, hend2⟩ := htrip
  -- Edge facts
  have hAedge : ∀ e ∈ A, isEdge e := fun e he => sA.all_edges e (hsA ▸ he)
  have hBedge : ∀ e ∈ B, isEdge e := fun e he => sB.all_edges e (hsB ▸ he)
  have hCedge : ∀ e ∈ C, isEdge e := fun e he => sC.all_edges e (hsC ▸ he)
  -- segment_in_comp: C ⊆ parCell eps (A∪B) for some eps
  have hCdisj : Disjoint sC.edges rAB.edges := by
    rw [hrAB, hsC]; exact Finset.disjoint_union_right.mpr ⟨hACdisj.symm, hBCdisj.symm⟩
  have hcls' : ∀ m, m ∈ cls rAB.edges ∩ cls sC.edges → sC.isEndpoint m := by
    intro m hm; rw [hrAB, hsC] at hm
    -- cls (A ∪ B) ∩ cls C ⊆ endpoint sC
    -- From triple: cls A ∩ cls C = {numClosure A m = 1} and
    --   {numClosure A m = 1} = {numClosure C m = 1}
    -- And for psegment sC, isEndpoint ↔ numClosure C m = 1
    -- cls (A∪B) = cls A ∪ cls B, so we split
    have hmC := Set.inter_subset_right hm
    have hmAB := Set.inter_subset_left hm
    rw [cls_union] at hmAB
    rcases hmAB with hmA | hmB
    · -- m ∈ cls A ∩ cls C → numClosure A m = 1 → numClosure C m = 1 → endpoint
      have h1 : m ∈ {m | numClosure A m = 1} := hcls3 ▸ (⟨hmA, hmC⟩ : m ∈ cls A ∩ cls C)
      have h2 : m ∈ {m | numClosure C m = 1} := (hend1.trans hend2) ▸ h1
      rw [Segment.isEndpoint, hsC]; exact h2
    · -- m ∈ cls B ∩ cls C
      have h1 : m ∈ {m | numClosure A m = 1} := hcls2 ▸ (⟨hmB, hmC⟩ : m ∈ cls B ∩ cls C)
      have h2 : m ∈ {m | numClosure C m = 1} := (hend1.trans hend2) ▸ h1
      rw [Segment.isEndpoint, hsC]; exact h2
  obtain ⟨eps, heps⟩ := segment_in_comp rAB sC hCdisj hcls'
  -- If eps = true, done
  by_cases heq : eps = true
  · subst heq; intro e he; rw [← hrAB]; exact heps e (hsC ▸ he)
  · -- eps = false: derive contradiction
    exfalso
    have hfeps : eps = false := by cases eps <;> simp_all
    subst hfeps
    -- Get edge u ∈ C
    obtain ⟨u, huC⟩ : C.Nonempty := by rw [← hsC]; exact sC.nonempty
    -- Get unbounded witness for B∪C
    have hBCedge : ∀ e ∈ (B ∪ C : Finset _), isEdge e := by
      intro e he; rcases Finset.mem_union.mp he with h | h
      · exact hBedge e h
      · exact hCedge e h
    obtain ⟨u', hu'⟩ := unboundedSet_nonempty (B ∪ C) hBCedge
    -- along_lemma11: find square p adjacent to edge u, connected to u'
    have hcomp_ne : (connectedComponentIn (complementCurve rBC.toSegment.edges) u').Nonempty := by
      rw [show rBC.toSegment.edges = (B ∪ C : Finset _) from hrBC]
      obtain ⟨r, hr⟩ := hu'; exact ⟨_, hr r le_rfl⟩
    obtain ⟨p, hp_sub, hp_comp⟩ := along_lemma11 rBC.toSegment u' u hcomp_ne
      (by rw [show rBC.toSegment.edges = (B ∪ C : Finset _) from hrBC]
          exact Finset.mem_union.mpr (Or.inr huC))
    -- Get u'' ∈ squ p
    obtain ⟨u'', hu''_squ⟩ := cell_nonempty (⟨.squ p, rfl⟩ : isCell (squ p))
    -- u'' is in the connected component of u', hence unbounded in B∪C
    have hu''_comp : u'' ∈ connectedComponentIn (complementCurve rBC.toSegment.edges) u' :=
      hp_comp hu''_squ
    have hu''_unbnd_BC : UnboundedSet (B ∪ C) u'' := by
      have heq := unboundedSet_comp_elt_eq (B ∪ C) hBCedge u' hu'
      change u'' ∈ {y | UnboundedSet (↑(B ∪ C)) y}
      rw [heq]
      show u'' ∈ connectedComponentIn (complementCurve (↑(B ∪ C))) u'
      rw [show (↑(B ∪ C) : Finset _) = rBC.toSegment.edges from hrBC.symm]
      exact hu''_comp
    -- u'' unbounded in A∪B∪C (via unbounded_triple_avoidance)
    have hu''_unbnd_ABC : UnboundedSet (A ∪ B ∪ C) u'' :=
      unbounded_triple_avoidance A B C u'' htrip' hA hu''_unbnd_BC
    -- u'' ∉ curveCells(A∪B∪C)
    have hu''_notcurve : u'' ∉ ⋃₀ (curveCells (A ∪ B ∪ C) : Set (Set E2)) := by
      have := unbounded_subset_complementCurve (↑(A ∪ B ∪ C)) hu''_unbnd_ABC
      rwa [complementCurve, Set.mem_compl_iff] at this
    -- edge conditions for A∪B∪C
    have hABCedge : ∀ e ∈ (A ∪ B ∪ C : Finset _), isEdge e := by
      intro e he
      rcases Finset.mem_union.mp he with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact hAedge e h'
        · exact hBedge e h'
      · exact hCedge e h
    -- u'' unbounded in A∪B
    have hu''_unbnd_AB : UnboundedSet (A ∪ B) u'' := by
      rw [← hrAB]
      exact unbounded_avoidance_subset rAB.edges (A ∪ B ∪ C) u''
        (hrAB ▸ hu''_unbnd_ABC)
        (hrAB ▸ Finset.subset_union_left)
        hABCedge (hrAB ▸ conn2_rectagon rAB)
        hu''_notcurve
    -- unbounded_even: u'' ∈ ⋃₀ {C | parCell true rAB.edges C}
    have hu''_in_parTrue : u'' ∈ ⋃₀ {C | parCell true rAB.edges C} := by
      rw [← unbounded_even rAB, hrAB]; exact hu''_unbnd_AB
    -- cell_ununion: squ p ∈ {C | parCell true rAB.edges C}
    have hsqu_parTrue : parCell true rAB.edges (squ p) :=
      cell_ununion (⟨.squ p, rfl⟩ : isCell (squ p)) hu''_squ
        (fun D hD => parCell_isCell hD) hu''_in_parTrue
    -- parCell_closure_cell: u (edge) is parCell true or curveCells
    have hu_cell : isCell u := isEdge_isCell (hCedge u huC)
    have hu_sub_cl : u ⊆ closure (squ p) := hp_sub
    rcases parCell_closure_cell rAB (squ p) u true (⟨.squ p, rfl⟩) hu_cell hu_sub_cl
      hsqu_parTrue with hpar_u | hcurve_u
    · -- parCell true rAB.edges u contradicts parCell false rAB.edges u
      have hpar_false : parCell false rAB.edges u := heps u (hsC ▸ huC)
      exact parCell_disjoint rAB.edges true u ⟨hpar_u, by simp [hpar_false]⟩
    · -- u ∈ curveCells rAB.edges → u ∈ rAB.edges (since u is edge)
      rw [hrAB] at hcurve_u
      have := (curveCells_edge (A ∪ B) u (hCedge u huC)).mp hcurve_u
      -- u ∈ A∪B but u ∈ C and C disjoint from A∪B
      rcases Finset.mem_union.mp this with hA' | hB'
      · exact absurd hA' (Finset.disjoint_right.mp hACdisj huC)
      · exact absurd hB' (Finset.disjoint_right.mp hBCdisj huC)

/-! ## §V.6 Curve cell and cls (moved before meeting_lemma which needs it) -/

/-- HOL Light: `curve_cell_cls` (line 43140).
For a segment `G`, `{pointI m}` is a curve cell iff `m ∈ cls G`. -/
theorem curveCells_cls (G : Segment) (m : ℤ × ℤ) :
    ({pointI m} ∈ curveCells G.edges) ↔ m ∈ cls G.edges := by
  constructor
  · intro h
    simp only [curveCells, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq] at h
    rcases h with h | ⟨m', hm', hcl⟩
    · exfalso
      rcases G.all_edges _ h with ⟨n, hn⟩ | ⟨n, hn⟩
      · exact hEdge_ne_pointI_set n m hn.symm
      · exact vEdge_ne_pointI_set n m hn.symm
    · have heq : m = m' := pointI_injective (Set.singleton_eq_singleton_iff.mp hm')
      rw [← heq] at hcl
      rw [G.edges.finite_toSet.closure_sUnion] at hcl
      rw [Set.mem_iUnion₂] at hcl
      obtain ⟨e, he, hcl⟩ := hcl
      exact ⟨e, he, hcl⟩
  · intro ⟨e, he, hcl⟩
    simp only [curveCells, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
    right; exact ⟨m, rfl, closure_mono (Set.subset_sUnion_of_mem he) hcl⟩

/-! ## §V.7 Meeting lemma and parity union -/

/-- HOL Light: `meeting_lemma` (line 42884).
Under certain conditions, a segment `C` meeting a parity-`eps` set `B`
at a common vertex inherits the same parity. -/
theorem meeting_lemma (R : Rectagon) (B : Finset (Set E2))
    (sC : Segment) (v : ℤ × ℤ) (eps : Bool)
    (hBpar : ∀ e ∈ B, parCell eps R.edges e)
    (hCR : Disjoint sC.edges R.edges)
    (hcls : cls R.edges ∩ cls sC.edges ⊆ {m | sC.isEndpoint m})
    (hclsC : v ∈ cls sC.edges) (hclsB : v ∈ cls B)
    (hnotR : v ∉ cls R.edges) (hBedge : ∀ e ∈ B, isEdge e) :
    ∀ e ∈ sC.edges, parCell eps R.edges e := by
  -- By segment_in_comp, C lies in some parCell eps' R
  obtain ⟨eps', heps'⟩ := segment_in_comp R sC hCR (fun m hm => hcls hm)
  -- If eps' = eps, done
  by_cases heq : eps' = eps
  · subst heq; exact heps'
  · -- eps' = !eps: derive contradiction
    exfalso
    have hne : eps' = !eps := by cases eps <;> cases eps' <;> simp_all
    -- v ∈ cls B means ∃ eB ∈ B, pointI v ∈ closure eB
    obtain ⟨eB, heB, hveB⟩ := hclsB
    -- eB has parCell eps R, so {pointI v} ∈ parCell eps R ∨ curveCells R
    have heB_cell : isCell eB := isEdge_isCell (hBedge eB heB)
    have : parCell eps R.edges {pointI v} ∨ {pointI v} ∈ curveCells R.edges := by
      apply parCell_closure_cell R eB {pointI v} eps heB_cell ⟨.point v, rfl⟩
      · intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hveB
      · exact hBpar eB heB
    rcases this with hpv | hcurve
    · -- {pointI v} has parCell eps R
      -- v ∈ cls sC means ∃ eC ∈ sC.edges, pointI v ∈ closure eC
      obtain ⟨eC, heC, hveC⟩ := hclsC
      -- By parCell_nbd: parCell eps R eC
      have heC_edge := sC.all_edges eC heC
      have hpar_eC := parCell_nbd R eps v eC hpv heC_edge hveC
      -- But C ⊆ parCell eps' R and eC ∈ C, so parCell eps' R eC
      have hpar_eC' := heps' eC heC
      -- parCell eps R eC ∧ parCell (!eps) R eC: contradiction
      rw [hne] at hpar_eC'
      exact parCell_disjoint R.edges eps eC ⟨hpar_eC, hpar_eC'⟩
    · -- {pointI v} ∈ curveCells R
      -- curveCells_cls says {pointI v} ∈ curveCells R ↔ v ∈ cls R
      have : v ∈ cls R.edges := (curveCells_cls R.toSegment v).mp hcurve
      exact hnotR this

/-- HOL Light: `parity_union_triple` (line 42928).
Parity of `B ∪ C` decomposes as equality of individual parities. -/
theorem parity_union_triple (sB sC : Segment) (sBC : Segment)
    (hBC : sBC.edges = sB.edges ∪ sC.edges)
    (hdisj : Disjoint sB.edges sC.edges)
    (A : Finset (Set E2)) (e : Set E2)
    (hAB : Disjoint A sB.edges) (hAC : Disjoint A sC.edges)
    (hAedge : ∀ a ∈ A, isEdge a) (he : e ∈ A) :
    paritySelect (sB.edges ∪ sC.edges) e =
      decide (paritySelect sB.edges e = paritySelect sC.edges e) := by
  have he_edge := hAedge e he
  have hnotB : e ∉ curveCells sB.edges :=
    fun hc => Finset.disjoint_right.mp hAB ((curveCells_edge sB.edges e he_edge).mp hc) he
  have hnotC : e ∉ curveCells sC.edges :=
    fun hc => Finset.disjoint_right.mp hAC ((curveCells_edge sC.edges e he_edge).mp hc) he
  exact paritySelect_union sB sC ⟨sBC, hBC⟩ hdisj e (isEdge_isCell he_edge) hnotB hnotC

/-- HOL Light: `parity_union_triple_even` (line 42948).
If `A ⊆ parCell true (B ∪ C)` then `parity B e = parity C e` for `e ∈ A`. -/
theorem parity_union_triple_even (sA sB sC : Segment) (sBC : Segment)
    (hBC : sBC.edges = sB.edges ∪ sC.edges)
    (hdisj : Disjoint sB.edges sC.edges)
    (hAB : Disjoint sA.edges sB.edges) (hAC : Disjoint sA.edges sC.edges)
    (e : Set E2) (he : e ∈ sA.edges)
    (hApar : ∀ a ∈ sA.edges, parCell true (sB.edges ∪ sC.edges) a) :
    paritySelect sB.edges e = paritySelect sC.edges e := by
  have h := parity_union_triple sB sC sBC hBC hdisj sA.edges e hAB hAC
    sA.all_edges he
  have hpar := hApar e he
  rw [← hBC] at hpar
  have hsel := (paritySelect_unique sBC e true hpar).symm
  rw [hBC] at hsel
  rw [hsel] at h
  exact decide_eq_true_eq.mp h.symm

/-- HOL Light: `parity_union_triple_odd` (line 42965).
If `A ⊆ parCell false (B ∪ C)` then `parity B e ≠ parity C e` for `e ∈ A`. -/
theorem parity_union_triple_odd (sB sC : Segment) (sBC : Segment)
    (hBC : sBC.edges = sB.edges ∪ sC.edges)
    (hdisj : Disjoint sB.edges sC.edges)
    (A : Finset (Set E2)) (e : Set E2)
    (hAB : Disjoint A sB.edges) (hAC : Disjoint A sC.edges)
    (hAedge : ∀ a ∈ A, isEdge a) (he : e ∈ A)
    (hApar : ∀ a ∈ A, parCell false (sB.edges ∪ sC.edges) a) :
    ¬(paritySelect sB.edges e = paritySelect sC.edges e) := by
  have h := parity_union_triple sB sC sBC hBC hdisj A e hAB hAC hAedge he
  have hpar := hApar e he
  rw [← hBC] at hpar
  have hsel := (paritySelect_unique sBC e false hpar).symm
  rw [hBC] at hsel
  rw [hsel] at h
  exact decide_eq_false_iff_not.mp h.symm

/-! ## §V.7 Parity implications -/

/-- HOL Light: `par_cell_even_imp` (line 42982).
Even parity deduction from two even parity containments. -/
theorem parCell_even_imp (A B C D : Finset (Set E2))
    (htrip : isPsegmentTriple A B D)
    (sC : Segment) (hCedges : sC.edges = C)
    (hcls : cls (A ∪ B) ∩ cls C ⊆ {m | sC.isEndpoint m})
    (hAC : Disjoint A C) (hBC : Disjoint B C) (hCD : Disjoint C D)
    (hCBD : ∀ e ∈ C, parCell true (B ∪ D) e)
    (hCAD : ∀ e ∈ C, parCell true (A ∪ D) e) :
    ∀ e ∈ C, parCell true (A ∪ B) e := by
  -- Extract triple data
  obtain ⟨⟨sA, hsA, _⟩, ⟨sB, hsB, _⟩, ⟨sD, hsD, _⟩,
    ⟨rAB, hrAB⟩, ⟨rAD, hrAD⟩, ⟨rBD, hrBD⟩,
    hABdisj, hADdisj, hBDdisj, _⟩ := htrip
  -- segment_in_comp: C ⊆ parCell eps (A∪B) for some eps
  have hCdisj : Disjoint sC.edges rAB.edges := by
    rw [hrAB, hCedges]
    exact Finset.disjoint_union_right.mpr ⟨hAC.symm, hBC.symm⟩
  have hcls' : ∀ m, m ∈ cls rAB.edges ∩ cls sC.edges → sC.isEndpoint m := by
    intro m hm; rw [hrAB, hCedges] at hm; exact hcls hm
  obtain ⟨eps, heps⟩ := segment_in_comp rAB sC hCdisj hcls'
  -- If eps = true, done
  by_cases heq : eps = true
  · subst heq; intro e he; rw [← hrAB]; exact heps e (hCedges ▸ he)
  · -- eps = false: derive contradiction
    exfalso
    have hfalse : eps = false := by cases eps <;> simp_all
    subst hfalse
    -- Take e ∈ C
    have ⟨e, heC⟩ : C.Nonempty := by rw [← hCedges]; exact sC.nonempty
    -- parity_union_triple_even: paritySelect A e = paritySelect D e
    have hAD_eq : paritySelect sA.edges e = paritySelect sD.edges e :=
      parity_union_triple_even sC sA sD rAD.toSegment
        (by simp only [Rectagon.toSegment]; rw [hrAD, hsA, hsD])
        (by rw [hsA, hsD]; exact hADdisj)
        (by rw [hCedges, hsA]; exact hAC.symm)
        (by rw [hCedges, hsD]; exact hCD)
        e (by rw [hCedges]; exact heC)
        (fun a ha => by rw [hsA, hsD]; exact hCAD a (hCedges ▸ ha))
    -- parity_union_triple_even: paritySelect B e = paritySelect D e
    have hBD_eq : paritySelect sB.edges e = paritySelect sD.edges e :=
      parity_union_triple_even sC sB sD rBD.toSegment
        (by simp only [Rectagon.toSegment]; rw [hrBD, hsB, hsD])
        (by rw [hsB, hsD]; exact hBDdisj)
        (by rw [hCedges, hsB]; exact hBC.symm)
        (by rw [hCedges, hsD]; exact hCD)
        e (by rw [hCedges]; exact heC)
        (fun a ha => by rw [hsB, hsD]; exact hCBD a (hCedges ▸ ha))
    -- Combine: paritySelect A e = paritySelect B e
    have hAB_eq : paritySelect sA.edges e = paritySelect sB.edges e :=
      hAD_eq.trans hBD_eq.symm
    -- parity_union_triple: paritySelect (A∪B) e = decide(paritySelect A e = paritySelect B e)
    have hpt := parity_union_triple sA sB rAB.toSegment
      (by simp only [Rectagon.toSegment]; rw [hrAB, hsA, hsB])
      (by rw [hsA, hsB]; exact hABdisj) C e
      (by rw [hsA]; exact hAC.symm)
      (by rw [hsB]; exact hBC.symm)
      (fun a ha => sC.all_edges a (hCedges ▸ ha)) (hCedges ▸ heC)
    -- paritySelect (A∪B) e = true since A and B parities agree
    have hpt_val : paritySelect (sA.edges ∪ sB.edges) e = true := by
      rw [hpt]; simp [hAB_eq]
    -- But C ⊆ parCell false (A∪B) from eps=false
    have hpar_false : parCell false rAB.edges e := heps e (hCedges ▸ heC)
    have hsel := paritySelect_unique rAB.toSegment e false hpar_false
    simp only [Rectagon.toSegment] at hsel
    rw [hrAB] at hsel
    -- hsel : false = paritySelect (A ∪ B) e, hpt_val uses sA.edges ∪ sB.edges
    rw [hsA, hsB] at hpt_val
    -- false = true: contradiction
    simp [hsel.symm] at hpt_val

/-- HOL Light: `par_cell_odd_imp` (line 43059).
Mixed parity deduction. -/
theorem parCell_odd_imp (A B C D : Finset (Set E2))
    (htrip : isPsegmentTriple A B D)
    (sC : Segment) (hCedges : sC.edges = C)
    (hcls : cls (A ∪ B) ∩ cls C ⊆ {m | sC.isEndpoint m})
    (hAC : Disjoint A C) (hBC : Disjoint B C) (hCD : Disjoint C D)
    (hCBD : ∀ e ∈ C, parCell false (B ∪ D) e)
    (hCAD : ∀ e ∈ C, parCell true (A ∪ D) e) :
    ∀ e ∈ C, parCell false (A ∪ B) e := by
  -- Extract triple data
  obtain ⟨⟨sA, hsA, _⟩, ⟨sB, hsB, _⟩, ⟨sD, hsD, _⟩,
    ⟨rAB, hrAB⟩, ⟨rAD, hrAD⟩, ⟨rBD, hrBD⟩,
    hABdisj, hADdisj, hBDdisj, _⟩ := htrip
  -- segment_in_comp: C ⊆ parCell eps (A∪B) for some eps
  have hCdisj : Disjoint sC.edges rAB.edges := by
    rw [hrAB, hCedges]; exact Finset.disjoint_union_right.mpr ⟨hAC.symm, hBC.symm⟩
  have hcls' : ∀ m, m ∈ cls rAB.edges ∩ cls sC.edges → sC.isEndpoint m := by
    intro m hm; rw [hrAB, hCedges] at hm; exact hcls hm
  obtain ⟨eps, heps⟩ := segment_in_comp rAB sC hCdisj hcls'
  -- If eps = false, done
  by_cases heq : eps = false
  · subst heq; intro e he; rw [← hrAB]; exact heps e (hCedges ▸ he)
  · -- eps = true: derive contradiction
    exfalso
    have htrue : eps = true := by cases eps <;> simp_all
    subst htrue
    -- Take e ∈ C
    have ⟨e, heC⟩ : C.Nonempty := by rw [← hCedges]; exact sC.nonempty
    -- parity_union_triple_even: paritySelect A e = paritySelect D e
    have hAD_eq : paritySelect sA.edges e = paritySelect sD.edges e :=
      parity_union_triple_even sC sA sD rAD.toSegment
        (by simp only [Rectagon.toSegment]; rw [hrAD, hsA, hsD])
        (by rw [hsA, hsD]; exact hADdisj)
        (by rw [hCedges, hsA]; exact hAC.symm)
        (by rw [hCedges, hsD]; exact hCD)
        e (by rw [hCedges]; exact heC)
        (fun a ha => by rw [hsA, hsD]; exact hCAD a (hCedges ▸ ha))
    -- parity_union_triple_odd: ¬(paritySelect B e = paritySelect D e)
    have hBD_neq : ¬(paritySelect sB.edges e = paritySelect sD.edges e) :=
      parity_union_triple_odd sB sD rBD.toSegment
        (by simp only [Rectagon.toSegment]; rw [hrBD, hsB, hsD])
        (by rw [hsB, hsD]; exact hBDdisj) sC.edges e
        (by rw [hCedges, hsB]; exact hBC.symm)
        (by rw [hCedges, hsD]; exact hCD)
        sC.all_edges (by rw [hCedges]; exact heC)
        (fun a ha => by rw [hsB, hsD]; exact hCBD a (hCedges ▸ ha))
    -- Combine: paritySelect A e ≠ paritySelect B e
    have hAB_neq : ¬(paritySelect sA.edges e = paritySelect sB.edges e) := by
      intro h; exact hBD_neq (hAD_eq.symm.trans h).symm
    -- parity_union_triple: paritySelect (A∪B) e = decide(paritySelect A e = paritySelect B e)
    have hpt := parity_union_triple sA sB rAB.toSegment
      (by simp only [Rectagon.toSegment]; rw [hrAB, hsA, hsB])
      (by rw [hsA, hsB]; exact hABdisj) C e
      (by rw [hsA]; exact hAC.symm)
      (by rw [hsB]; exact hBC.symm)
      (fun a ha => sC.all_edges a (hCedges ▸ ha)) (hCedges ▸ heC)
    -- paritySelect (A∪B) e = false since parities disagree
    have hpt_val : paritySelect (sA.edges ∪ sB.edges) e = false := by
      rw [hpt]; simp [hAB_neq]
    -- But C ⊆ parCell true (A∪B) from eps=true
    have hpar_true : parCell true rAB.edges e := heps e (hCedges ▸ heC)
    have hsel := paritySelect_unique rAB.toSegment e true hpar_true
    simp only [Rectagon.toSegment] at hsel
    rw [hrAB] at hsel
    -- true = false: contradiction
    rw [hsA, hsB] at hpt_val
    simp [hsel.symm] at hpt_val

/-! ## §V.9 2-connectedness -/

/-- HOL Light: `conn2_rect_diff_inner` (line 43151).
Removing the inner parity region from a 2-connected set preserves
2-connectedness. -/
theorem conn2_rect_diff_inner (E : Finset (Set E2)) (R : Rectagon)
    (hconn : conn2 E) (hEedge : ∀ e ∈ E, isEdge e)
    (hR : R.edges ⊆ E) :
    conn2 (E \ (E.filter fun e => @decide (parCell false R.edges e) (Classical.dec _))) := by
  -- Abbreviate J
  let J := E.filter (fun e => @decide (parCell false R.edges e) (Classical.dec _))
  -- Membership characterization for J
  have hJ_mem : ∀ e, e ∈ J ↔ e ∈ E ∧ parCell false R.edges e := by
    intro e; simp only [J, Finset.mem_filter]
    constructor
    · rintro ⟨he, hd⟩; exact ⟨he, by simpa using hd⟩
    · rintro ⟨he, hp⟩; exact ⟨he, by simpa using hp⟩
  -- Membership characterization for E \ J
  have hEJ_mem : ∀ e, e ∈ E \ J ↔ e ∈ E ∧ ¬parCell false R.edges e := by
    intro e; constructor
    · intro h; refine ⟨Finset.mem_sdiff.mp h |>.1, fun hp => ?_⟩
      exact (Finset.mem_sdiff.mp h).2 ((hJ_mem e).mpr ⟨(Finset.mem_sdiff.mp h).1, hp⟩)
    · rintro ⟨he, hnp⟩; exact Finset.mem_sdiff.mpr ⟨he, fun hJ => hnp ((hJ_mem e).mp hJ).2⟩
  -- R ⊆ E \ J (rectagon edges are NOT in the inner parity region)
  have hR_sub : R.edges ⊆ E \ J := by
    intro e he
    rw [hEJ_mem]
    refine ⟨hR he, fun hpar => ?_⟩
    have hcurve : e ∈ curveCells R.edges := (curveCells_edge R.edges e (R.all_edges e he)).mpr he
    have := parCell_curveCells_disjoint R.edges R.all_edges false
    rw [Set.eq_empty_iff_forall_notMem] at this
    exact this e ⟨hpar, hcurve⟩
  -- J ⊆ E
  have hJ_sub_E : J ⊆ E := Finset.filter_subset _ _
  -- Card bound: 2 ≤ (E \ J).card
  have hcard : 2 ≤ (E \ J).card := by
    have hRconn : conn2 R.edges := conn2_rectagon R
    exact le_trans hRconn.1 (Finset.card_le_card hR_sub)
  -- (E \ J) ∪ J = E
  have hEJ_union : E \ J ∪ J = E := Finset.sdiff_union_self_eq_union.trans
    (Finset.union_eq_left.mpr hJ_sub_E)
  -- E \ J edge predicate
  have hEJ_edge : ∀ e ∈ E \ J, isEdge e := fun e he => hEedge e (Finset.sdiff_subset he)
  -- J edges are parCell false R
  have hJ_par : ∀ e ∈ J, parCell false R.edges e := fun e he => ((hJ_mem e).mp he).2
  -- conn2 (E \ J)
  refine ⟨hcard, ?_⟩
  intro a b c ha hb hab hbc hac
  -- a, b ∈ cls (E\J) ⊆ cls E
  have ha_E : a ∈ cls E := cls_subset Finset.sdiff_subset ha
  have hb_E : b ∈ cls E := cls_subset Finset.sdiff_subset hb
  -- Use conn2 of E: get S ⊆ E with segment_end S a b and c ∉ cls S
  obtain ⟨S, hSE, hSab, hSc⟩ := hconn.2 a b c ha_E hb_E hab hbc hac
  -- If S ⊆ E \ J, we're done
  by_cases hSsub : S ⊆ E \ J
  · exact ⟨S, hSsub, hSab, hSc⟩
  -- Otherwise: S ∩ J ≠ ∅. Reroute S around J using paths through R.
  -- a, b are in cls (E\J), so for each endpoint m, either parCell T R {pointI m} or m ∈ cls R
  -- Key helper: endpoint classification
  have endpoint_class : ∀ m, m ∈ cls (E \ J) →
      parCell true R.edges {pointI m} ∨ m ∈ cls R.edges := by
    intro m hm
    -- parCell_cell_partition_segment gives 3 cases for {pointI m}
    rcases parCell_cell_partition_segment R.toSegment true {pointI m} ⟨.point m, rfl⟩ with
      hT | hF | hcurve
    · left; simp only [Rectagon.toSegment] at hT; exact hT
    · -- parCell false R {pointI m}: then m ∉ cls (E\J), contradiction
      simp only [Bool.not_true, Rectagon.toSegment] at hF
      exfalso
      -- m ∈ cls (E\J) means ∃ e ∈ E\J such that pointI m ∈ closure e
      obtain ⟨e, he, hcl⟩ := hm
      -- e ∈ E\J, so ¬parCell false R e
      have hne : ¬parCell false R.edges e := ((hEJ_mem e).mp he).2
      -- parCell_nbd: from parCell false R {pointI m} and closure, we get parCell false R e
      -- But first we need e to be an edge
      have he_edge : isEdge e := hEJ_edge e he
      have : parCell false R.edges e := parCell_nbd R false m e hF he_edge hcl
      exact hne this
    · -- {pointI m} ∈ curveCells R: this means m ∈ cls R
      right
      simp only [Rectagon.toSegment] at hcurve
      exact (curveCells_cls R.toSegment m).mp (by simp only [Rectagon.toSegment]; exact hcurve)
  -- For each endpoint m that is also in cls R, the conn2 of R gives paths through R ⊆ E\J
  -- conn2 of R
  have hRconn : conn2 R.edges := conn2_rectagon R
  -- R.edges are edges
  have hRedge : ∀ e ∈ R.edges, isEdge e := R.all_edges
  -- cls (E\J) respects union: cls ((E\J) ∪ J) = cls (E\J) ∪ cls J = cls E
  -- Key: if m ∈ cls (E\J) and parCell T R {pointI m}, then ¬cls J m
  have endpoint_not_cls_J : ∀ m, parCell true R.edges {pointI m} → ¬(m ∈ cls J) := by
    intro m hT hclsJ
    obtain ⟨e, he, hcl⟩ := hclsJ
    have hpar := hJ_par e he
    -- parCell_nbd: from parCell true R {pointI m} and closure, parCell true R e
    have he_edge : isEdge e := hEedge e (hJ_sub_E he)
    have hTe : parCell true R.edges e := parCell_nbd R true m e hT he_edge hcl
    -- But e has parCell false R e, contradiction
    exact parCell_disjoint R.edges false e ⟨hpar, hTe⟩
  -- Endpoint a: either parCell T R {pointI a} (hence ¬cls J a) or cls R a
  have ha_class := endpoint_class a ha
  -- Endpoint b: either parCell T R {pointI b} (hence ¬cls J b) or cls R b
  have hb_class := endpoint_class b hb
  -- Helper: for endpoints in parCell T R, all edges at that vertex in S are in E\J
  -- (because cls J m = false, so edges at m are not in J, hence in E\J)
  -- We use the cls union: a ∈ cls S ⊆ cls E = cls (E\J) ∪ cls J
  -- Since S ⊆ E and S has segment_end S a b, a ∈ cls S
  have ha_cls_S : a ∈ cls S := segment_end_cls hSab
  have hb_cls_S : b ∈ cls S := segment_end_cls2 hSab
  -- Get an edge in S touching J
  -- S ⊄ E\J, so ∃ u ∈ S with u ∈ J
  have hSJ_ne : ∃ u, u ∈ S ∧ u ∈ J := by
    by_contra h; push Not at h
    exact hSsub fun e he => Finset.mem_sdiff.mpr ⟨hSE he, h e he⟩
  -- The full path surgery: reroute S around J using conn2(R) paths
  -- Step 1: Find m ∈ cls R ∩ cls S (a shared closure point)
  -- If no such m exists, S is disjoint from R∪J closure-wise,
  -- so segment_in_comp gives S ⊆ parCell eps R for some eps,
  -- which (since S ⊆ E and S intersects J) leads to a contradiction.
  have find_m : ∃ m, m ∈ cls R.edges ∧ m ∈ cls S := by
    by_contra h_no_m
    push Not at h_no_m
    -- S is disjoint from R in closure
    have hRS_disj : Disjoint S R.edges := by
      rw [Finset.disjoint_left]
      intro e hS hRe
      -- e ∈ S and e ∈ R.edges
      -- e is an edge, so has 2 closure points
      obtain ⟨a', b', _, hcl_a, _, _⟩ := edge_two_endpoints e (hRedge e hRe)
      exact h_no_m a' ⟨e, hRe, hcl_a⟩ ⟨e, hS, hcl_a⟩
    -- cls S ∩ cls R = ∅
    have hcls_disj : ∀ m, ¬(m ∈ cls R.edges ∧ m ∈ cls S) := by
      intro m ⟨h1, h2⟩; exact h_no_m m h1 h2
    -- segment_in_comp: S entirely in one parCell region
    -- Need: S is a segment, i.e., get the Segment from segment_end
    obtain ⟨sS, hsS, _, _, _, _⟩ := hSab
    -- Need: all endpoints of sS are in cls R ∩ cls sS
    -- segment_in_comp needs: Disjoint S R.edges ∧
    -- ∀ m, m ∈ cls R ∩ cls S → sS.isEndpoint m
    -- Since cls R ∩ cls S = ∅ (by hcls_disj), the condition is vacuously true
    have hep_cond : ∀ m', m' ∈ cls R.edges ∩ cls sS.edges → sS.isEndpoint m' := by
      intro m' hm'; exfalso; exact hcls_disj m' ⟨hm'.1, hsS ▸ hm'.2⟩
    have hSR_disj : Disjoint sS.edges R.edges := hsS ▸ hRS_disj
    obtain ⟨eps, heps⟩ := segment_in_comp R sS hSR_disj hep_cond
    -- S has an edge u in J (parCell false R), but all edges of S have parCell eps R
    obtain ⟨u, huS, huJ⟩ := hSJ_ne
    have hpar_u := heps u (hsS ▸ huS)
    have hpar_F := hJ_par u huJ
    -- eps must be false
    by_cases he : eps = false
    · subst he
      -- All edges of S have parCell false R, so S ⊆ J
      -- But a ∈ cls S and a ∈ cls (E\J), meaning a ∈ cls (E\J)
      -- From endpoint_class, parCell true R {pointI a} or a ∈ cls R
      -- If parCell true R {pointI a}: a ∉ cls J, but all S edges
      -- are in J so a ∈ cls J, contradiction
      -- If a ∈ cls R: but a ∈ cls S ⊆ cls J (all of S parCell false), contradiction with h_no_m
      have hS_sub_J : S ⊆ J := by
        intro e he; rw [hJ_mem]; exact ⟨hSE he, heps e (hsS ▸ he)⟩
      have ha_cls_J : a ∈ cls J := cls_subset hS_sub_J ha_cls_S
      rcases ha_class with hTa | hRa
      · exact endpoint_not_cls_J a hTa ha_cls_J
      · exact h_no_m a hRa ha_cls_S
    · -- eps = true: parCell true R u and parCell false R u, contradiction
      have : eps = true := by cases eps <;> simp_all
      subst this
      exact parCell_disjoint R.edges false u ⟨hpar_F, hpar_u⟩
  obtain ⟨m, hm_R, hm_S⟩ := find_m
  -- m ∈ cls R.edges ∩ cls S
  -- m ≠ c: since c ∉ cls S
  have hmc : m ≠ c := fun h => hSc (h ▸ hm_S)
  -- R ∪ J edges are edges
  have hRJ_edge : ∀ e ∈ R.edges ∪ J, isEdge e := by
    intro e he; rw [Finset.mem_union] at he
    exact he.elim (hRedge e) (fun hJ => hEedge e (hJ_sub_E hJ))
  -- Step 2: Build a path from endpoint x to m through E\J
  -- This is the core path surgery helper, used for both a and b
  -- x is an endpoint of S with segment_end S x y for some y
  have build_path : ∀ x y, x ∈ cls (E \ J) → segment_end S x y → x ≠ y →
      x ≠ m → x ≠ c →
      ∃ S_x ⊆ E \ J, segment_end S_x x m ∧ c ∉ cls S_x := by
    intro x y hx_EJ hSxy hxy hxm hxc
    rcases endpoint_class x hx_EJ with hTx | hRx
    · -- Case: parCell true R {pointI x}, so x ∉ cls J and x ∉ cls R
      have hx_not_cls_J : x ∉ cls J := endpoint_not_cls_J x hTx
      have hx_not_cls_R : x ∉ cls R.edges := by
        intro hRx
        have hcurve : {pointI x} ∈ curveCells R.edges := by
          have := (curveCells_cls R.toSegment x).mpr
            (by simp only [Rectagon.toSegment]; exact hRx)
          simp only [Rectagon.toSegment] at this; exact this
        have hempty := parCell_curveCells_disjoint R.edges R.all_edges true
        rw [Set.eq_empty_iff_forall_notMem] at hempty
        exact hempty {pointI x} ⟨hTx, hcurve⟩
      -- x ∉ cls (R ∪ J)
      have hx_not_cls_RJ : x ∉ cls (R.edges ∪ J) := by
        rw [cls_union]; exact fun h => h.elim hx_not_cls_R hx_not_cls_J
      -- m ∈ cls (R ∪ J)
      have hm_cls_RJ : m ∈ cls (R.edges ∪ J) := by
        rw [cls_union]; exact .inl hm_R
      -- Get S' ⊆ S with segment_end S' x m:
      -- if m = y, S' = S; otherwise, cut_psegment
      have ⟨S', hS'_sub, hS'_end⟩ : ∃ S' ⊆ S, segment_end S' x m := by
        by_cases hmy : m = y
        · subst hmy; exact ⟨S, Finset.Subset.refl _, hSxy⟩
        · obtain ⟨A, _, hE_eq, _, _, hA_end, _⟩ :=
            cut_psegment hSxy hm_S hxm.symm (show m ≠ y from hmy)
          exact ⟨A, hE_eq ▸ Finset.subset_union_left, hA_end⟩
      -- All edges of R ∪ J are edges
      -- Apply segment_end_select to S' with E = R ∪ J
      obtain ⟨B, c', hB_end, hc'_RJ, hB_sub_S', hB_cls⟩ :=
        segment_end_select hRJ_edge hS'_end hx_not_cls_RJ hm_cls_RJ
      -- B ⊆ S' ⊆ S ⊆ E, and B ∩ J = ∅ (B only touches R∪J at c')
      have hB_sub_E : B ⊆ E := Finset.Subset.trans hB_sub_S' (Finset.Subset.trans hS'_sub hSE)
      -- B doesn't intersect R ∪ J (except at cls-point c')
      -- From hB_cls: cls B ∩ cls (R∪J) = {c'}, B ⊆ S' which is a subsegment
      -- Key: if e ∈ B ∩ J, then e is an edge, both endpoints ∈ cls B ∩ cls J ⊆ cls B ∩ cls (R∪J)
      -- But cls B ∩ cls (R∪J) = {c'}, so both endpoints = c'
      -- An edge can't have both endpoints equal, contradiction
      have hB_not_J : ∀ e ∈ B, e ∉ J := by
        intro e heB heJ
        obtain ⟨p, q, hpq, hp, hq, _⟩ :=
          edge_two_endpoints e (hEedge e (hB_sub_E heB))
        have hp_cls_B : p ∈ cls B := ⟨e, heB, hp⟩
        have hq_cls_B : q ∈ cls B := ⟨e, heB, hq⟩
        have hp_cls_RJ : p ∈ cls (R.edges ∪ J) := by
          rw [cls_union]; exact .inr ⟨e, heJ, hp⟩
        have hq_cls_RJ : q ∈ cls (R.edges ∪ J) := by
          rw [cls_union]; exact .inr ⟨e, heJ, hq⟩
        have hp_eq : p = c' := by
          have : p ∈ ({c'} : Set _) := hB_cls ▸ ⟨hp_cls_B, hp_cls_RJ⟩
          exact Set.mem_singleton_iff.mp this
        have hq_eq : q = c' := by
          have : q ∈ ({c'} : Set _) := hB_cls ▸ ⟨hq_cls_B, hq_cls_RJ⟩
          exact Set.mem_singleton_iff.mp this
        exact hpq (hp_eq.trans hq_eq.symm)
      -- B ⊆ E \ J
      have hB_sub_EJ : B ⊆ E \ J := by
        intro e he; exact Finset.mem_sdiff.mpr ⟨hB_sub_E he, hB_not_J e he⟩
      -- c ∉ cls B (since cls B ⊆ cls S' ⊆ cls S and c ∉ cls S)
      have hcB : c ∉ cls B :=
        fun hc => hSc (cls_subset
          (Finset.Subset.trans hB_sub_S' hS'_sub) hc)
      -- c' ∈ cls (R ∪ J), need c' ∈ cls R.edges
      -- c' ∈ cls (E\J) since c' ∈ cls B and B ⊆ E\J
      have hc'_EJ : c' ∈ cls (E \ J) := cls_subset hB_sub_EJ (segment_end_cls2 hB_end)
      have hc'_cls_R : c' ∈ cls R.edges := by
        rw [cls_union] at hc'_RJ
        rcases hc'_RJ with h | hc'J
        · exact h
        · -- c' ∈ cls J, but endpoint_class gives parCell true or cls R
          rcases endpoint_class c' hc'_EJ with hTc' | hRc'
          · exact absurd hc'J (endpoint_not_cls_J c' hTc')
          · exact hRc'
      -- Case split: c' = m
      by_cases hc'm : c' = m
      · -- B is the path from x to m
        subst hc'm; exact ⟨B, hB_sub_EJ, hB_end, hcB⟩
      · -- c' ≠ m: use conn2(R) to get path from c' to m through R ⊆ E\J
        -- c' ≠ c: since c' ∈ cls B ⊆ cls S and c ∉ cls S
        have hc'c : c' ≠ c := fun h => hcB (h ▸ segment_end_cls2 hB_end)
        obtain ⟨T, hT_sub, hT_end, hTc⟩ :=
          hRconn.2 c' m c hc'_cls_R hm_R hc'm hmc hc'c
        -- T ⊆ R ⊆ E\J
        have hT_sub_EJ : T ⊆ E \ J := Finset.Subset.trans hT_sub hR_sub
        -- Concatenate B and T: segment_end B x c', segment_end T c' m
        obtain ⟨U, hU_sub, hU_end⟩ := segment_end_trans hB_end hT_end hxm
        exact ⟨U, Finset.Subset.trans hU_sub (Finset.union_subset hB_sub_EJ hT_sub_EJ),
          hU_end, fun hc => by
            have := cls_subset hU_sub hc
            rw [cls_union] at this
            exact this.elim hcB hTc⟩
    · -- Case: x ∈ cls R.edges
      -- Use conn2(R): get S'' ⊆ R with segment_end S'' m x and c ∉ cls S''
      obtain ⟨S'', hS''_sub, hS''_end, hS''_c⟩ :=
        hRconn.2 m x c hm_R hRx hxm.symm hxc hmc
      -- S'' ⊆ R ⊆ E\J
      exact ⟨S'', Finset.Subset.trans hS''_sub hR_sub,
        (segment_end_symm S'' m x).mp hS''_end, hS''_c⟩
  -- Specialize for a
  have build_path_a : a ≠ m → ∃ S_a ⊆ E \ J, segment_end S_a a m ∧ c ∉ cls S_a :=
    fun ham => build_path a b ha hSab hab ham hac
  -- Specialize for b
  have build_path_b : b ≠ m → ∃ S_b ⊆ E \ J, segment_end S_b b m ∧ c ∉ cls S_b :=
    fun hbm => build_path b a hb ((segment_end_symm S a b).mp hSab) hab.symm hbm hbc
  -- Step 4: Combine paths using segment_end_trans
  -- Case split on whether a = m or b = m
  by_cases ham : a = m
  · -- a = m: just need path from b to a through E\J
    subst ham
    by_cases hba : b = a
    · exact absurd hba.symm hab
    have ⟨S_b, hS_b_sub, hS_b_end, hS_b_c⟩ := build_path_b hba
    exact ⟨S_b, hS_b_sub, (segment_end_symm S_b b a).mp hS_b_end, hS_b_c⟩
  · by_cases hbm : b = m
    · -- b = m: just need path from a to m = b through E\J
      subst hbm
      exact build_path_a ham
    · -- Neither a = m nor b = m: build both paths and concatenate
      have ⟨S_a, hS_a_sub, hS_a_end, hS_a_c⟩ := build_path_a ham
      have ⟨S_b, hS_b_sub, hS_b_end, hS_b_c⟩ := build_path_b hbm
      -- Concatenate: segment_end_trans S_a S_b' a m b (with S_b reversed to go from m to b)
      have hS_b_end' : segment_end S_b m b := (segment_end_symm S_b b m).mp hS_b_end
      obtain ⟨U, hU_sub, hU_end⟩ := segment_end_trans hS_a_end hS_b_end' hab
      refine ⟨U, ?_, hU_end, ?_⟩
      · -- U ⊆ S_a ∪ S_b ⊆ E\J
        exact Finset.Subset.trans hU_sub (Finset.union_subset hS_a_sub hS_b_sub)
      · -- c ∉ cls U ⊆ cls (S_a ∪ S_b) = cls S_a ∪ cls S_b
        intro hc
        have hc_union := cls_subset hU_sub hc
        rw [cls_union] at hc_union
        exact hc_union.elim hS_a_c hS_b_c

/-- HOL Light: `conn2_psegment_triple` (line 43461).
A 2-connected non-rectagon set decomposes into a psegment triple
with one component in the false parity region. -/
theorem conn2_psegment_triple (E : Finset (Set E2))
    (hconn : conn2 E) (hEedge : ∀ e ∈ E, isEdge e)
    (hnotRect : ¬∃ (R : Rectagon), R.edges = E) :
    ∃ A B C : Finset (Set E2),
      isPsegmentTriple A B C ∧ A ⊆ E ∧ B ⊆ E ∧ C ⊆ E ∧
      (∀ e ∈ A, parCell false (B ∪ C) e) := by
  -- BACK_TAC: suffice to find any psegment triple ⊆ E
  suffices h : ∃ A B C : Finset (Set E2),
      isPsegmentTriple A B C ∧ A ⊆ E ∧ B ⊆ E ∧ C ⊆ E by
    obtain ⟨A, B, C, htrip, hAE, hBE, hCE⟩ := h
    rcases trap_odd_cell A B C htrip with hA | hB | hC
    · exact ⟨A, B, C, htrip, hAE, hBE, hCE, hA⟩
    · have htrip' := isPsegmentTriple_rotate htrip
      refine ⟨B, C, A, htrip', hBE, hCE, hAE, fun e he => ?_⟩
      rw [Finset.union_comm]; exact hB e he
    · have htrip' := isPsegmentTriple_swap htrip
      refine ⟨C, B, A, htrip', hCE, hBE, hAE, fun e he => ?_⟩
      rw [Finset.union_comm]; exact hC e he
  -- Find a rectagon R ⊆ E
  obtain ⟨_, hRE, R, rfl⟩ := conn2_has_rectagon hEedge hconn
  have hne' : R.edges ≠ E := fun heq => hnotRect ⟨R, heq⟩
  -- Find psegment A disjoint from R
  obtain ⟨A, hAE, hAR, ⟨sA, hsAps, hsA⟩, hcls⟩ :=
    conn2_proper hEedge hconn (conn2_rectagon R) hRE hne'
  -- Get endpoints a, b of A
  obtain ⟨a, b, hab, ha, hb, huniq⟩ := sA.psegment_two_endpoints hsAps
  -- a, b ∈ cls R.edges
  have ha_cls_R : a ∈ cls R.edges := by
    have ha' : numClosure A a = 1 := by rw [← hsA]; exact ha
    have : a ∈ cls R.edges ∩ cls A := hcls ▸ ha'
    exact this.1
  have hb_cls_R : b ∈ cls R.edges := by
    have hb' : numClosure A b = 1 := by rw [← hsA]; exact hb
    have : b ∈ cls R.edges ∩ cls A := hcls ▸ hb'
    exact this.1
  -- Cut R at a, b to get B', C'
  obtain ⟨B', C', hseB, hseC, hRBC, hBC_disj, hBC_cls⟩ :=
    cut_rectagon_cls R hab ha_cls_R hb_cls_R
  -- Extract Segment witnesses
  obtain ⟨sB, hsB, hsBa, hsBb, _, huniqB⟩ := hseB
  obtain ⟨sC, hsC, hsCa, hsCb, _, huniqC⟩ := hseC
  -- Subsets and disjointness
  have hBE : B' ⊆ E := (hRBC ▸ Finset.subset_union_left : B' ⊆ R.edges).trans hRE
  have hCE : C' ⊆ E := (hRBC ▸ Finset.subset_union_right : C' ⊆ R.edges).trans hRE
  have hAB_disj : Disjoint A B' :=
    hAR.mono_right (hRBC ▸ Finset.subset_union_left : B' ⊆ R.edges)
  have hAC_disj : Disjoint A C' :=
    hAR.mono_right (hRBC ▸ Finset.subset_union_right : C' ⊆ R.edges)
  -- Endpoint sets
  have hep : {m | numClosure A m = 1} = {a, b} := by
    ext m; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      exact huniq m (by rw [Segment.isEndpoint, hsA]; exact hm)
    · rintro (rfl | rfl)
      · rw [← hsA]; exact ha
      · rw [← hsA]; exact hb
  have hepB : {m | numClosure B' m = 1} = {a, b} := by
    ext m; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      exact huniqB m (by rw [Segment.isEndpoint, hsB]; exact hm)
    · rintro (rfl | rfl)
      · rw [← hsB]; exact hsBa
      · rw [← hsB]; exact hsBb
  have hepC : {m | numClosure C' m = 1} = {a, b} := by
    ext m; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      exact huniqC m (by rw [Segment.isEndpoint, hsC]; exact hm)
    · rintro (rfl | rfl)
      · rw [← hsC]; exact hsCa
      · rw [← hsC]; exact hsCb
  -- segment_end data
  have hseA : segment_end A a b := ⟨sA, hsA, ha, hb, hab, huniq⟩
  have hseB' : segment_end B' a b := ⟨sB, hsB, hsBa, hsBb, hab, huniqB⟩
  have hseC' : segment_end C' a b := ⟨sC, hsC, hsCa, hsCb, hab, huniqC⟩
  -- cls intersections
  have hBsub : cls B' ⊆ cls R.edges :=
    cls_subset (hRBC ▸ Finset.subset_union_left : B' ⊆ R.edges)
  have hCsub : cls C' ⊆ cls R.edges :=
    cls_subset (hRBC ▸ Finset.subset_union_right : C' ⊆ R.edges)
  have hclsAB : cls A ∩ cls B' = {m | numClosure A m = 1} := by
    rw [hep]; ext m
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hmA, hmB⟩
      have hmR : m ∈ cls R.edges := hBsub hmB
      have hm_nc : numClosure A m = 1 := by
        have : m ∈ cls R.edges ∩ cls A := ⟨hmR, hmA⟩
        rw [hcls] at this; exact this
      exact huniq m (by rw [Segment.isEndpoint, hsA]; exact hm_nc)
    · rintro (rfl | rfl)
      · exact ⟨segment_end_cls hseA, segment_end_cls hseB'⟩
      · exact ⟨segment_end_cls2 hseA, segment_end_cls2 hseB'⟩
  have hclsAC : cls A ∩ cls C' = {m | numClosure A m = 1} := by
    rw [hep]; ext m
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hmA, hmC⟩
      have hmR : m ∈ cls R.edges := hCsub hmC
      have hm_nc : numClosure A m = 1 := by
        have : m ∈ cls R.edges ∩ cls A := ⟨hmR, hmA⟩
        rw [hcls] at this; exact this
      exact huniq m (by rw [Segment.isEndpoint, hsA]; exact hm_nc)
    · rintro (rfl | rfl)
      · exact ⟨segment_end_cls hseA, segment_end_cls hseC'⟩
      · exact ⟨segment_end_cls2 hseA, segment_end_cls2 hseC'⟩
  have hclsBC : cls B' ∩ cls C' = {m | numClosure A m = 1} := by rw [hep]; exact hBC_cls
  -- Rectagon unions
  have hrAB : ∃ rAB : Rectagon, rAB.edges = A ∪ B' :=
    segment_end_union_rectagon hseA hseB' hAB_disj (hclsAB.trans hep)
  have hrAC : ∃ rAC : Rectagon, rAC.edges = A ∪ C' :=
    segment_end_union_rectagon hseA hseC' hAC_disj (hclsAC.trans hep)
  have hrBC : ∃ rBC : Rectagon, rBC.edges = B' ∪ C' := ⟨R, hRBC⟩
  -- Build the triple
  have hsBps : sB.isPsegment := ⟨a, b, hab, hsBa, hsBb, huniqB⟩
  have hsCps : sC.isPsegment := ⟨a, b, hab, hsCa, hsCb, huniqC⟩
  refine ⟨A, B', C', ?_, hAE, hBE, hCE⟩
  exact ⟨⟨sA, hsA, hsAps⟩, ⟨sB, hsB, hsBps⟩, ⟨sC, hsC, hsCps⟩,
    hrAB, hrAC, hrBC, hAB_disj, hAC_disj, hBC_disj,
    hclsAB, hclsBC, hclsAC, hep.trans hepB.symm, hepB.trans hepC.symm⟩

/-- HOL Light: `rectagon_surround_conn2` (line 43524).
Every 2-connected edge set contains a rectagon whose bounded region
contains that of the whole set. -/
theorem rectagon_surround_conn2 (G : Finset (Set E2))
    (hconn : conn2 G) (hGedge : ∀ e ∈ G, isEdge e) :
    ∃ (R : Rectagon), R.edges ⊆ G ∧
      ∀ x, BoundedSet G x → BoundedSet R.edges x := by
  -- Strong induction on G.card
  suffices h : ∀ n (E : Finset (Set E2)), E.card = n → conn2 E → (∀ e ∈ E, isEdge e) →
      ∃ (R : Rectagon), R.edges ⊆ E ∧ ∀ x, BoundedSet E x → BoundedSet R.edges x from
    h G.card G rfl hconn hGedge
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro E hn hconn_E hEedge
  -- Case: E is already a rectagon
  by_cases hrect : ∃ (R : Rectagon), R.edges = E
  · obtain ⟨R, hR⟩ := hrect
    exact ⟨R, hR ▸ Finset.Subset.refl _, fun x hx => hR ▸ hx⟩
  · -- E is not a rectagon: use conn2_psegment_triple
    obtain ⟨A, B, C, htrip, hAE, hBE, hCE, heps⟩ :=
      conn2_psegment_triple E hconn_E hEedge hrect
    -- Extract the rectagon rBC with rBC.edges = B ∪ C
    obtain ⟨⟨sA, hsA, hsAps⟩, _, _, _, _, ⟨rBC, hrBC⟩, _, _, _, _, _, _, _, _⟩ := htrip
    -- heps : ∀ e ∈ A, parCell false (B ∪ C) e
    -- A ⊆ E, and all edges of A have parCell false rBC
    have hA_par : ∀ e ∈ A, parCell false rBC.edges e := by
      intro e he; rw [hrBC]; exact heps e he
    -- Let J = E ∩ parCell false rBC
    let J := E.filter (fun e => @decide (parCell false rBC.edges e) (Classical.dec _))
    -- A ⊆ J (A ⊆ E and A ⊆ parCell false rBC)
    have hA_sub_J : A ⊆ J := by
      intro e he
      simp only [J, Finset.mem_filter]
      exact ⟨hAE he, by simpa using hA_par e he⟩
    -- A is nonempty (psegment triple has nonempty components)
    have hA_ne : A.Nonempty := hsA ▸ sA.nonempty
    -- J is nonempty
    have hJ_ne : J.Nonempty := hA_ne.mono hA_sub_J
    -- rBC ⊆ E (B ⊆ E and C ⊆ E)
    have hRBC_sub : rBC.edges ⊆ E := by
      rw [hrBC]; exact Finset.union_subset hBE hCE
    -- conn2 (E \ J): by conn2_rect_diff_inner
    have hconn_EJ : conn2 (E \ J) := conn2_rect_diff_inner E rBC hconn_E hEedge hRBC_sub
    -- (E \ J).card < E.card
    have hcard_lt : (E \ J).card < E.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset
        (Finset.filter_subset _ _) hJ_ne)
    -- E \ J edges are edges
    have hEJ_edge : ∀ e ∈ E \ J, isEdge e := fun e he => hEedge e (Finset.sdiff_subset he)
    -- Bounded preservation: for any x, BoundedSet E x → BoundedSet (E \ J) x
    -- Use star_avoidance_contrp with E' = E, B = J, R = rBC
    have hbnd_pres : ∀ x, BoundedSet E x → BoundedSet (E \ J) x := by
      intro x hx
      have hx_not_curve_E : x ∉ ⋃₀ (curveCells E : Set (Set E2)) :=
        bounded_subset_complementCurve E (Set.mem_setOf.mpr hx)
      have hJ_par : ∀ e ∈ J, parCell false rBC.edges e := by
        intro e he; simp only [J, Finset.mem_filter] at he; simpa using he.2
      have hJ_edge : ∀ e ∈ J, isEdge e := by
        intro e he; exact hEedge e (Finset.filter_subset _ _ he)
      exact star_avoidance_contrp E E rBC J x hx (Finset.Subset.refl _) hEedge
        hRBC_sub hJ_edge
        (fun hmem => hx_not_curve_E
          (Set.sUnion_mono (curveCells_mono (Finset.filter_subset _ _)) hmem))
        hJ_par hx_not_curve_E
    -- Recurse
    obtain ⟨R, hR_sub, hR_bnd⟩ := ih (E \ J).card (hn ▸ hcard_lt) (E \ J) rfl hconn_EJ hEJ_edge
    exact ⟨R, Finset.Subset.trans hR_sub Finset.sdiff_subset,
      fun x hx => hR_bnd x (hbnd_pres x hx)⟩

/-! ## §V.10 Curve cell subset and bounded/unbounded -/

/-- HOL Light: `curve_cell_subset` (line 43619).
Monotonicity of unions of curve cells. -/
theorem curveCells_sUnion_mono {H G : Finset (Set E2)} (h : H ⊆ G) :
    ⋃₀ (curveCells H : Set (Set E2)) ⊆ ⋃₀ (curveCells G : Set (Set E2)) := by
  apply Set.sUnion_mono; exact curveCells_mono h

/-- HOL Light: `bounded_set_curve_cell_empty` (line 43634).
Bounded points avoid curve cells of subsets. -/
theorem bounded_set_curve_cell_empty (H G : Finset (Set E2)) (x : E2)
    (hbnd : BoundedSet G x) (hHG : H ⊆ G) :
    x ∉ ⋃₀ (curveCells H : Set (Set E2)) := by
  have hx := bounded_subset_complementCurve G hbnd
  rw [complementCurve, Set.mem_compl_iff] at hx
  exact fun hmem => hx (curveCells_sUnion_mono hHG hmem)

/-- HOL Light: `unbounded_set_curve_cell_empty` (line 43649).
Unbounded points avoid curve cells of subsets. -/
theorem unbounded_set_curve_cell_empty (H G : Finset (Set E2)) (x : E2)
    (hunbnd : UnboundedSet G x) (hHG : H ⊆ G) :
    x ∉ ⋃₀ (curveCells H : Set (Set E2)) := by
  have hx := unbounded_subset_complementCurve G hunbnd
  rw [complementCurve, Set.mem_compl_iff] at hx
  exact fun hmem => hx (curveCells_sUnion_mono hHG hmem)

/-! ## §V.11 Triple avoidance for bounded sets -/

/-- HOL Light: `bounded_triple_avoidance` (line 43664).
If `A ⊆ parCell false (B ∪ C)` then bounded set of `A ∪ B ∪ C`
is contained in bounded set of `B ∪ C`. -/
theorem bounded_triple_avoidance (A B C : Finset (Set E2))
    (htrip : isPsegmentTriple A B C)
    (hA : ∀ e ∈ A, parCell false (B ∪ C) e) :
    {x | BoundedSet (A ∪ B ∪ C) x} ⊆ {x | BoundedSet (B ∪ C) x} := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  -- Proof by contradiction: assume BoundedSet (A∪B∪C) x but ¬BoundedSet (B∪C) x
  by_contra hnotBC
  -- Extract triple data
  have ⟨⟨sA, hsA, hpA⟩, ⟨sB, hsB, hpB⟩, ⟨sC, hsC, hpC⟩,
    ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
    hABdisj, hACdisj, hBCdisj, _⟩ := htrip
  have hAedge : ∀ e ∈ A, isEdge e := fun e he => sA.all_edges e (hsA ▸ he)
  have hE'edge : ∀ e ∈ A ∪ B ∪ C, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact sA.all_edges e (hsA ▸ h')
      · exact sB.all_edges e (hsB ▸ h')
    · exact sC.all_edges e (hsC ▸ h)
  have hR : rBC.edges ⊆ A ∪ B ∪ C := by
    rw [hrBC]; intro e he
    rcases Finset.mem_union.mp he with hb | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hb)))
    · exact Finset.mem_union.mpr (Or.inr hc)
  -- x ∉ ⋃₀ curveCells A and x ∉ ⋃₀ curveCells (A∪B∪C)
  have hnotcurveA := bounded_set_curve_cell_empty A (A ∪ B ∪ C) x hx
    (Finset.subset_union_left.trans Finset.subset_union_left)
  have hnotcurveE' := bounded_set_curve_cell_empty (A ∪ B ∪ C) (A ∪ B ∪ C) x hx
    (Finset.Subset.refl _)
  -- Apply star_avoidance_lemma1
  have hsdiff : (A ∪ B ∪ C) \ A = B ∪ C := by
    ext e; constructor
    · intro he
      have ⟨hmem, hnotA⟩ := Finset.mem_sdiff.mp he
      rcases Finset.mem_union.mp hmem with hab | hc
      · rcases Finset.mem_union.mp hab with ha | hb
        · exact absurd ha hnotA
        · exact Finset.mem_union.mpr (Or.inl hb)
      · exact Finset.mem_union.mpr (Or.inr hc)
    · intro he
      rcases Finset.mem_union.mp he with hb | hc
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hb))),
           Finset.disjoint_right.mp hABdisj hb⟩
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union.mpr (Or.inr hc),
           Finset.disjoint_right.mp hACdisj hc⟩
  have hBpar' : ∀ e ∈ A, parCell false rBC.edges e := fun e he => hrBC ▸ hA e he
  have hlem := star_avoidance_lemma1 (A ∪ B ∪ C) (A ∪ B ∪ C) rBC A x hx
    (Finset.Subset.refl _) hE'edge (hrBC ▸ hR) hnotcurveA (hrBC ▸ hBpar') hnotcurveE'
  rw [hsdiff] at hlem
  rcases hlem with hbnd | hunbnd
  · exact hnotBC hbnd
  · -- Unbounded in B∪C → unbounded in A∪B∪C → contradiction
    have hunbndABC := unbounded_triple_avoidance A B C x htrip hA hunbnd
    exact bounded_unbounded_disj (A ∪ B ∪ C) x ⟨hx, hunbndABC⟩

/-- HOL Light: `bounded_euclid` (line 43718). -/
theorem bounded_euclid (G : Finset (Set E2)) (x : E2)
    (hbnd : BoundedSet G x) :
    x ∈ complementCurve G :=
  bounded_subset_complementCurve G hbnd

/-- HOL Light: `unbounded_euclid` (line 43729). -/
theorem unbounded_euclid (G : Finset (Set E2)) (x : E2)
    (hunbnd : UnboundedSet G x) :
    x ∈ complementCurve G :=
  unbounded_subset_complementCurve G hunbnd

/-! ## §V.12 Inner union -/

/-- HOL Light: `bounded_triple_inner_union` (line 43740).
The bounded set of `A ∪ B ∪ C` is contained in the union of bounded
sets of `A ∪ B` and `B ∪ C`. -/
theorem bounded_triple_inner_union (A B C : Finset (Set E2))
    (htrip : isPsegmentTriple A B C) :
    {x | BoundedSet (A ∪ B ∪ C) x} ⊆
      {x | BoundedSet (A ∪ B) x} ∪ {x | BoundedSet (B ∪ C) x} := by
  -- Extract triple data
  have ⟨⟨sA, hsA, hpA⟩, ⟨sB, hsB, hpB⟩, ⟨sC, hsC, hpC⟩,
    ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
    hABdisj, hACdisj, hBCdisj, _, _, _, _, _⟩ := htrip
  -- All edges are edges
  have hAedge : ∀ e ∈ A, isEdge e := fun e he => sA.all_edges e (hsA ▸ he)
  have hBedge : ∀ e ∈ B, isEdge e := fun e he => sB.all_edges e (hsB ▸ he)
  have hCedge : ∀ e ∈ C, isEdge e := fun e he => sC.all_edges e (hsC ▸ he)
  have hABedge : ∀ e ∈ A ∪ B, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · exact hAedge e h
    · exact hBedge e h
  have hBCedge : ∀ e ∈ B ∪ C, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · exact hBedge e h
    · exact hCedge e h
  have hABCedge : ∀ e ∈ A ∪ B ∪ C, isEdge e := by
    intro e he; rcases Finset.mem_union.mp he with h | h
    · exact hABedge e h
    · exact hCedge e h
  -- Use trap_odd_cell on triple (C, A, B) to split into 3 cases
  have htrip_CAB : isPsegmentTriple C A B :=
    isPsegmentTriple_rotate (isPsegmentTriple_rotate htrip)
  rcases trap_odd_cell C A B htrip_CAB with hC_odd | hA_odd | hB_odd
  · -- Case 1: ∀ e ∈ C, parCell false (A ∪ B) e
    -- bounded_triple_avoidance C A B gives bounded(C∪A∪B) ⊆ bounded(A∪B)
    have hsub := bounded_triple_avoidance C A B htrip_CAB hC_odd
    intro x hx; left
    have hx' : BoundedSet (C ∪ A ∪ B) x := by
      simp only [Set.mem_setOf_eq] at hx ⊢
      have : A ∪ B ∪ C = C ∪ A ∪ B := by ext; simp [Finset.mem_union, or_comm, or_assoc]
      rwa [this] at hx
    exact Set.mem_setOf_eq.mpr (hsub hx')
  · -- Case 2: ∀ e ∈ A, parCell false (C ∪ B) e
    -- This is ∀ e ∈ A, parCell false (B ∪ C) e (up to union comm)
    have hA_odd' : ∀ e ∈ A, parCell false (B ∪ C) e := by
      intro e he; have := hA_odd e he; rwa [Finset.union_comm] at this
    have hsub := bounded_triple_avoidance A B C htrip hA_odd'
    intro x hx; right
    exact Set.mem_setOf_eq.mpr (hsub hx)
  · -- Case 3: ∀ e ∈ B, parCell false (C ∪ A) e (HARD CASE)
    -- Rewrite as ∀ e ∈ B, parCell false (A ∪ C) e
    have hB_odd' : ∀ e ∈ B, parCell false (A ∪ C) e := by
      intro e he; have := hB_odd e he; rwa [Finset.union_comm] at this
    -- Prove: bounded(A∪B∪C) ⊆ bounded(A∪B) ∪ bounded(B∪C)
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
    -- By contradiction: assume ¬bounded(A∪B) and ¬bounded(B∪C)
    by_contra h_neg
    push Not at h_neg
    obtain ⟨hnotAB, hnotBC⟩ := h_neg
    -- x ∈ complementCurve (A∪B∪C), hence in complementCurve (A∪B) and (B∪C)
    have hx_comp : x ∈ complementCurve (A ∪ B ∪ C) := bounded_euclid _ _ hx
    have hcomp_mono : ∀ H G : Finset (Set E2), H ⊆ G →
        complementCurve G ⊆ complementCurve H := by
      intro H G hHG z hz
      simp only [complementCurve, Set.mem_compl_iff, Set.mem_sUnion] at hz ⊢
      exact fun ⟨S, hS, hzS⟩ => hz ⟨S, curveCells_mono hHG hS, hzS⟩
    have hx_compAB : x ∈ complementCurve (A ∪ B) :=
      hcomp_mono _ _ Finset.subset_union_left hx_comp
    have hBC_sub_ABC : B ∪ C ⊆ A ∪ B ∪ C := by
      intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
      · exact Finset.mem_union.mpr (Or.inr h)
    have hx_compBC : x ∈ complementCurve (B ∪ C) :=
      hcomp_mono _ _ hBC_sub_ABC hx_comp
    -- Since ¬bounded and in complement: unbounded
    have hxUAB : UnboundedSet (A ∪ B) x :=
      (bounded_unbounded_union _ hABedge hx_compAB).resolve_left hnotAB
    have hxUBC : UnboundedSet (B ∪ C) x :=
      (bounded_unbounded_union _ hBCedge hx_compBC).resolve_left hnotBC
    -- Get the cell u containing x
    -- x ∈ ⋃₀ {C | parCell true (A∪B)} via unbounded_even applied to rAB
    have hxAB_even : x ∈ ⋃₀ {D | parCell true (A ∪ B) D} := by
      have h1 : x ∈ {x | UnboundedSet rAB.edges x} := hrAB ▸ hxUAB
      rw [unbounded_even rAB] at h1; rwa [hrAB] at h1
    have hxBC_even : x ∈ ⋃₀ {D | parCell true (B ∪ C) D} := by
      have h1 : x ∈ {x | UnboundedSet rBC.edges x} := hrBC ▸ hxUBC
      rw [unbounded_even rBC] at h1; rwa [hrBC] at h1
    -- Extract cells: x ∈ u, parCell true (A∪B) u, and x ∈ v, parCell true (B∪C) v
    obtain ⟨u, hu_parAB, hxu⟩ := hxAB_even
    obtain ⟨v, hv_parBC, hxv⟩ := hxBC_even
    -- parCell implies isCell
    have hu_cell : isCell u := parCell_isCell hu_parAB
    have hv_cell : isCell v := parCell_isCell hv_parBC
    -- Since both u and v contain x, and they are cells, u = v
    have huv : u = v := by
      obtain ⟨ctu, rfl⟩ := hu_cell
      obtain ⟨ctv, rfl⟩ := hv_cell
      obtain ⟨w, _, huniq⟩ := cell_partition x
      exact congr_arg CellType.toSet ((huniq ctu hxu).trans (huniq ctv hxv).symm)
    -- So parCell true (A∪B) u and parCell true (B∪C) u
    have hu_parBC : parCell true (B ∪ C) u := huv ▸ hv_parBC
    -- u ∉ curveCells (A∪B), u ∉ curveCells (B∪C)
    have hnotcurveAB : u ∉ (curveCells (A ∪ B) : Set (Set E2)) := by
      intro h
      have := (parCell_curveCells_disjoint (A ∪ B) hABedge true)
      rw [Set.eq_empty_iff_forall_notMem] at this
      exact this u ⟨hu_parAB, h⟩
    have hnotcurveBC : u ∉ (curveCells (B ∪ C) : Set (Set E2)) := by
      intro h
      have := (parCell_curveCells_disjoint (B ∪ C) hBCedge true)
      rw [Set.eq_empty_iff_forall_notMem] at this
      exact this u ⟨hu_parBC, h⟩
    -- u ∉ curveCells A, u ∉ curveCells B, u ∉ curveCells C
    have hu_notA : u ∉ curveCells A :=
      fun h => hnotcurveAB (curveCells_mono Finset.subset_union_left h)
    have hu_notB : u ∉ curveCells B :=
      fun h => hnotcurveAB (curveCells_mono Finset.subset_union_right h)
    have hu_notC : u ∉ curveCells C :=
      fun h => hnotcurveBC (curveCells_mono Finset.subset_union_right h)
    -- Use paritySelect_unique to get paritySelect values
    have hpsAB : true = paritySelect (A ∪ B) u := by
      have h := paritySelect_unique rAB.toSegment u true (by
        show parCell true rAB.toSegment.edges u
        simp only [Rectagon.toSegment]; rwa [hrAB])
      simp only [Rectagon.toSegment] at h; rw [hrAB] at h; exact h
    have hpsBC : true = paritySelect (B ∪ C) u := by
      have h := paritySelect_unique rBC.toSegment u true (by
        show parCell true rBC.toSegment.edges u
        simp only [Rectagon.toSegment]; rwa [hrBC])
      simp only [Rectagon.toSegment] at h; rw [hrBC] at h; exact h
    -- paritySelect_union for A∪B:
    -- paritySelect (A∪B) u = decide(paritySelect A u = paritySelect B u)
    have hsAB_seg : ∃ sAB : Segment, sAB.edges = sA.edges ∪ sB.edges :=
      ⟨rAB.toSegment, by simp only [Rectagon.toSegment]; rw [hrAB, hsA, hsB]⟩
    have hpsAB_eq := paritySelect_union sA sB hsAB_seg
      (by rw [hsA, hsB]; exact hABdisj) u hu_cell
      (by rw [hsA]; exact hu_notA) (by rw [hsB]; exact hu_notB)
    rw [hsA, hsB] at hpsAB_eq
    -- paritySelect_union for B∪C:
    -- paritySelect (B∪C) u = decide(paritySelect B u = paritySelect C u)
    have hsBC_seg : ∃ sBC : Segment, sBC.edges = sB.edges ∪ sC.edges :=
      ⟨rBC.toSegment, by simp only [Rectagon.toSegment]; rw [hrBC, hsB, hsC]⟩
    have hpsBC_eq := paritySelect_union sB sC hsBC_seg
      (by rw [hsB, hsC]; exact hBCdisj) u hu_cell
      (by rw [hsB]; exact hu_notB) (by rw [hsC]; exact hu_notC)
    rw [hsB, hsC] at hpsBC_eq
    -- From hpsAB and hpsAB_eq: paritySelect A u = paritySelect B u
    rw [hpsAB_eq] at hpsAB
    have hAeqB : paritySelect A u = paritySelect B u := by simpa using hpsAB.symm
    -- From hpsBC and hpsBC_eq: paritySelect B u = paritySelect C u
    rw [hpsBC_eq] at hpsBC
    have hBeqC : paritySelect B u = paritySelect C u := by simpa using hpsBC.symm
    -- Hence paritySelect A u = paritySelect C u
    have hAeqC : paritySelect A u = paritySelect C u := hAeqB.trans hBeqC
    -- u ∉ curveCells (A∪C) via curveCells_union
    have hnotcurveAC : u ∉ (curveCells (A ∪ C) : Set (Set E2)) := by
      rw [curveCells_union]; exact fun h => h.elim hu_notA hu_notC
    -- paritySelect_union for A∪C
    have hsAC_seg : ∃ sAC : Segment, sAC.edges = sA.edges ∪ sC.edges :=
      ⟨rAC.toSegment, by simp only [Rectagon.toSegment]; rw [hrAC, hsA, hsC]⟩
    have hpsAC_eq := paritySelect_union sA sC hsAC_seg
      (by rw [hsA, hsC]; exact hACdisj) u hu_cell
      (by rw [hsA]; exact hu_notA) (by rw [hsC]; exact hu_notC)
    rw [hsA, hsC] at hpsAC_eq
    -- paritySelect (A∪C) u = decide(paritySelect A u = paritySelect C u) = true
    have hpsAC_true : paritySelect (A ∪ C) u = true := by
      rw [hpsAC_eq]; simp [hAeqC]
    -- parCell true (A∪C) u via paritySelect_spec
    have hu_parAC : parCell true (A ∪ C) u := by
      have h := paritySelect_spec rAC.toSegment u hu_cell
        (by rw [show rAC.toSegment.edges = A ∪ C from
              by simp only [Rectagon.toSegment]; rw [hrAC]]; exact hnotcurveAC)
      simp only [Rectagon.toSegment] at h; rw [hrAC, hpsAC_true] at h; exact h
    -- x ∈ UnboundedSet (A∪C)
    have hxUAC : UnboundedSet (A ∪ C) x := by
      have hx_in : x ∈ ⋃₀ {D | parCell true (A ∪ C) D} := ⟨u, hu_parAC, hxu⟩
      rw [show A ∪ C = rAC.edges from hrAC.symm] at hx_in
      have := (unbounded_even rAC).symm ▸ hx_in
      rwa [hrAC] at this
    -- Apply unbounded_triple_avoidance on triple (B, C, A)
    have htrip_BCA : isPsegmentTriple B C A :=
      isPsegmentTriple_rotate htrip
    have hB_odd_CA : ∀ e ∈ B, parCell false (C ∪ A) e := by
      intro e he; have := hB_odd' e he; rwa [Finset.union_comm] at this
    have hxUCA : UnboundedSet (C ∪ A) x := by
      rwa [show C ∪ A = A ∪ C from Finset.union_comm C A]
    have hxU_BCA : UnboundedSet (B ∪ C ∪ A) x :=
      unbounded_triple_avoidance B C A x htrip_BCA hB_odd_CA hxUCA
    -- Rewrite B∪C∪A = A∪B∪C
    have hBCA_eq : B ∪ C ∪ A = A ∪ B ∪ C := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [hBCA_eq] at hxU_BCA
    exact absurd ⟨hx, hxU_BCA⟩ (bounded_unbounded_disj _ _)

end

end JordanCurveTheorem
