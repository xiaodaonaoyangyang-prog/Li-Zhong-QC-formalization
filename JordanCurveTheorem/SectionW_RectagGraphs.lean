/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionV_ComplementParity
/-!
# Section W: Rectagonal Graphs and K₃,₃
## HOL Light: Section W (Lines 44060–45372)
Connect rectagonal graph embeddings to planarity. If a rectagon graph
is isomorphic to K₃,₃, its embedding gives a plane graph isomorphic
to K₃,₃, contradicting nonplanarity.
### Key HOL Light definitions
- `rectagon_graph`: A graph whose edges are psegments with disjoint interiors
- `rectagonal_graph`: A graph isomorphic to a rectagon graph
- `k33_rectagon_hyp`: Hypothesis for K₃,₃ non-rectagonality argument
### Key HOL Light results
- `k33_rectagon_hyp_false`: The K₃,₃ rectagon hypothesis is always false
- `rectagon_graph_k33_false`: K₃,₃ is not rectagonal
-/
open Set Topology
namespace JordanCurveTheorem
noncomputable section
/-! ## §W.1 Definitions -/
/-- HOL Light: `rectagon_graph` (line 44064).
A graph whose edges are psegments with disjoint interiors and endpoint-only
closure intersections. The incidence of each edge equals its endpoint set. -/
def isRectagonGraph (G : HolGraph (ℤ × ℤ) (Finset (Set E2))) : Prop :=
  (∀ e ∈ G.edgeSet, ∃ a b, segment_end e a b) ∧
  (∀ e ∈ G.edgeSet, G.inc e = {m | numClosure e m = 1}) ∧
  (∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' → Disjoint e e') ∧
  (∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' →
    cls e ∩ cls e' = {m | numClosure e m = 1} ∩ {m | numClosure e' m = 1})
/-- HOL Light: `rectagonal_graph` (line 44076).
A graph is rectagonal if it is isomorphic to some rectagon graph. -/
def isRectagonalGraph {V E : Type*} (G : HolGraph V E) : Prop :=
  ∃ H : HolGraph (ℤ × ℤ) (Finset (Set E2)), isRectagonGraph H ∧ GraphIsomorphic H G
/-- HOL Light: `k33_rectagon_hyp` (line 44079).
The hypothesis for the K₃,₃ rectagon argument: a rectagon R with three
pairwise-disjoint psegments f(0), f(1), f(2) forming triples with
complementary halves of R, such that every f(j) meets both halves. -/
def k33RectagonHyp (R : Rectagon) (f : Fin 3 → Finset (Set E2)) : Prop :=
  (∀ i j : Fin 3, i ≠ j → cls (f i) ∩ cls (f j) = ∅) ∧
  (∀ i j : Fin 3, i ≠ j → Disjoint (f i) (f j)) ∧
  (∀ i : Fin 3, ∃ A B : Finset (Set E2),
    R.edges = A ∪ B ∧
    isPsegmentTriple A B (f i) ∧
    (∀ j : Fin 3, (cls (f j) ∩ cls A).Nonempty ∧ (cls (f j) ∩ cls B).Nonempty) ∧
    (∀ j : Fin 3, i ≠ j → cls (f j) ∩ cls A ∩ cls B = ∅))
/-! ## §W.2 Parity arguments -/
/-- HOL Light: `k33_rectagon_two_even` (line 44092).
If f(i) ⊆ parCell false R, then for all j ≠ i, f(j) ⊆ parCell true R. -/
theorem k33_rectagon_two_even (R : Rectagon) (f : Fin 3 → Finset (Set E2))
    (i : Fin 3) (h : k33RectagonHyp R f)
    (hfi : ∀ e ∈ f i, parCell false R.edges e) :
    ∀ j : Fin 3, j ≠ i → ∀ e ∈ f j, parCell true R.edges e := by
  obtain ⟨hclsij, hdisjij, hdecomp⟩ := h
  obtain ⟨A, B, hR, htripi, hmeet, hclsABempty⟩ := hdecomp i
  rw [hR] at hfi ⊢
  -- Keep an un-destructed copy
  have htripi' := htripi
  obtain ⟨⟨sA, hsA, _⟩, ⟨sB, hsB, _⟩, _,
    _, ⟨rAfI, hrAfI⟩, ⟨rBfI, hrBfI⟩,
    _, _, _, _, _, _, _, _⟩ := htripi
  -- Rotated triples
  have htripFiAB := isPsegmentTriple_rotate (isPsegmentTriple_rotate htripi')
  -- outer_segment_even on both sides
  have hBtrue : ∀ e ∈ B, parCell true (f i ∪ A) e :=
    outer_segment_even _ _ _ htripFiAB hfi
  have hAtrue : ∀ e ∈ A, parCell true (f i ∪ B) e :=
    outer_segment_even _ _ _ (isPsegmentTriple_swap htripi')
      (by rwa [Finset.union_comm B A])
  -- For each j ≠ i, show f(j) ⊆ parCell true (A ∪ B)
  intro j hji
  -- Get j-th decomposition for segment and triple data
  obtain ⟨Aj, Bj, hRj, htripj, _, _⟩ := hdecomp j
  obtain ⟨_, _, ⟨sJ, hsJ, _⟩, _, _, _, _, hAjFj, hBjFj,
    _, h11j, h12j, h13j, h14j⟩ := htripj
  -- f(j) disjoint from A, B, and f(i)
  have hAjBj : Aj ∪ Bj = A ∪ B := hRj.symm.trans hR
  have hfjAuB : Disjoint (f j) (A ∪ B) := by
    rw [← hAjBj]; exact Finset.disjoint_union_right.mpr ⟨hAjFj.symm, hBjFj.symm⟩
  have hfjA : Disjoint (f j) A :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hfjAuB
  have hfjB : Disjoint (f j) B :=
    Finset.disjoint_of_subset_right Finset.subset_union_right hfjAuB
  have hfjFi : Disjoint (f j) (f i) := hdisjij j i hji
  -- Cls conditions
  have hclsFiFj : cls (f i) ∩ cls (f j) = ∅ := hclsij i j hji.symm
  have hclsFjAB : cls (f j) ∩ cls A ∩ cls B = ∅ := hclsABempty j hji.symm
  -- Endpoint subset for cls (A ∪ B)
  have hclsABfj_sub : cls (A ∪ B) ∩ cls (f j) ⊆ {m | sJ.isEndpoint m} := by
    intro m ⟨hmAB, hmfj⟩
    change numClosure sJ.edges m = 1; rw [hsJ]
    rw [← hAjBj, cls_union] at hmAB
    rcases hmAB with hmAj | hmBj
    · have := Set.mem_inter hmAj hmfj; rw [h12j, h13j, h14j] at this; exact this
    · have := Set.mem_inter hmBj hmfj; rw [h11j, h13j, h14j] at this; exact this
  -- Witness points from nonempty intersections
  obtain ⟨hclsJA, hclsJB⟩ := hmeet j
  obtain ⟨u, huFj, huA⟩ := hclsJA
  obtain ⟨u', hu'Fj, hu'B⟩ := hclsJB
  -- u ∉ cls B, u' ∉ cls A (from cls (f j) ∩ cls A ∩ cls B = ∅)
  have hu_notB : u ∉ cls B := by
    intro habs
    have hm : u ∈ cls (f j) ∩ cls A ∩ cls B := ⟨⟨huFj, huA⟩, habs⟩
    simp only [hclsFjAB, Set.mem_empty_iff_false] at hm
  have hu'_notA : u' ∉ cls A := by
    intro habs
    have hm : u' ∈ cls (f j) ∩ cls A ∩ cls B := ⟨⟨hu'Fj, habs⟩, hu'B⟩
    simp only [hclsFjAB, Set.mem_empty_iff_false] at hm
  -- u, u' ∉ cls (f i) (from cls (f i) ∩ cls (f j) = ∅)
  have hu_notFi : u ∉ cls (f i) := by
    intro habs
    have hm : u ∈ cls (f i) ∩ cls (f j) := ⟨habs, huFj⟩
    simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  have hu'_notFi : u' ∉ cls (f i) := by
    intro habs
    have hm : u' ∈ cls (f i) ∩ cls (f j) := ⟨habs, hu'Fj⟩
    simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  -- Cls subset conditions for meeting_lemma on both sides
  have hclsAfI_sub : cls rAfI.edges ∩ cls sJ.edges ⊆ {m | sJ.isEndpoint m} := by
    rw [hrAfI, hsJ, cls_union]
    intro m ⟨hmAfI, hmfj⟩
    rcases hmAfI with hmA | hmfI
    · exact hclsABfj_sub ⟨by rw [cls_union]; exact Or.inl hmA, hmfj⟩
    · have hm : m ∈ cls (f i) ∩ cls (f j) := ⟨hmfI, hmfj⟩
      simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  have hclsBfI_sub : cls rBfI.edges ∩ cls sJ.edges ⊆ {m | sJ.isEndpoint m} := by
    rw [hrBfI, hsJ, cls_union]
    intro m ⟨hmBfI, hmfj⟩
    rcases hmBfI with hmB | hmfI
    · exact hclsABfj_sub ⟨by rw [cls_union]; exact Or.inr hmB, hmfj⟩
    · have hm : m ∈ cls (f i) ∩ cls (f j) := ⟨hmfI, hmfj⟩
      simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  -- A-side meeting_lemma: R = rAfI (A ∪ f i), B' = B, sC = sJ, v = u', eps = true
  -- Need u' ∉ cls rAfI.edges
  have hu'_notAfI : u' ∉ cls rAfI.edges := by
    rw [hrAfI, cls_union]; intro h_abs
    rcases h_abs with hA | hFi
    · exact hu'_notA hA
    · exact hu'_notFi hFi
  -- Disjointness
  have hfjAfI : Disjoint sJ.edges rAfI.edges := by
    rw [hsJ, hrAfI]; exact Finset.disjoint_union_right.mpr ⟨hfjA, hfjFi⟩
  have hBtrue_rAfI : ∀ e ∈ B, parCell true rAfI.edges e := by
    intro e he; rw [hrAfI, Finset.union_comm A (f i)]; exact hBtrue e he
  -- Apply meeting_lemma for A-side
  have hfjAfI_par : ∀ e ∈ sJ.edges, parCell true rAfI.edges e :=
    meeting_lemma rAfI B sJ u' true hBtrue_rAfI hfjAfI hclsAfI_sub
      (hsJ ▸ hu'Fj) hu'B hu'_notAfI (fun e he => sB.all_edges e (hsB ▸ he))
  -- B-side meeting_lemma: R = rBfI (B ∪ f i), B' = A, sC = sJ, v = u, eps = true
  have hu_notBfI : u ∉ cls rBfI.edges := by
    rw [hrBfI, cls_union]; intro h_abs
    rcases h_abs with hB | hFi
    · exact hu_notB hB
    · exact hu_notFi hFi
  have hfjBfI : Disjoint sJ.edges rBfI.edges := by
    rw [hsJ, hrBfI]; exact Finset.disjoint_union_right.mpr ⟨hfjB, hfjFi⟩
  have hAtrue_rBfI : ∀ e ∈ A, parCell true rBfI.edges e := by
    intro e he; rw [hrBfI, Finset.union_comm B (f i)]; exact hAtrue e he
  have hfjBfI_par : ∀ e ∈ sJ.edges, parCell true rBfI.edges e :=
    meeting_lemma rBfI A sJ u true hAtrue_rBfI hfjBfI hclsBfI_sub
      (hsJ ▸ huFj) huA hu_notBfI (fun e he => sA.all_edges e (hsA ▸ he))
  -- parCell_even_imp: A = A, B = B, C = f(j), D = f(i)
  have hfjAuB_true : ∀ e ∈ f j, parCell true (A ∪ B) e := by
    apply parCell_even_imp A B (f j) (f i) htripi' sJ hsJ hclsABfj_sub
      hfjA.symm hfjB.symm hfjFi
    · -- f(j) ⊆ parCell true (B ∪ f(i))
      intro e he
      have := hfjBfI_par e (hsJ ▸ he)
      rwa [hrBfI] at this
    · -- f(j) ⊆ parCell true (A ∪ f(i))
      intro e he
      have := hfjAfI_par e (hsJ ▸ he)
      rwa [hrAfI] at this
  exact hfjAuB_true
/-- HOL Light: `psegment_triple_odd_even` (line 44309).
Given a psegment triple with C ⊆ parCell true (A ∪ B), one can rearrange
A, B to get A' ⊆ parCell false (B' ∪ C) and B' ⊆ parCell true (A' ∪ C). -/
theorem psegment_triple_odd_even (A B C : Finset (Set E2))
    (htrip : isPsegmentTriple A B C)
    (hC : ∀ e ∈ C, parCell true (A ∪ B) e) :
    ∃ A' B', isPsegmentTriple A' B' C ∧
      (∀ e ∈ C, parCell true (A' ∪ B') e) ∧
      (∀ e ∈ A', parCell false (B' ∪ C) e) ∧
      (∀ e ∈ B', parCell true (A' ∪ C) e) ∧
      A ∪ B = A' ∪ B' ∧
      cls A ∩ cls B = cls A' ∩ cls B' ∧
      (∀ P : Finset (Set E2) → Prop, P A ∧ P B → P A' ∧ P B') := by
  by_cases hAF : ∀ e ∈ A, parCell false (B ∪ C) e
  · -- Case 1: A ⊆ parCell false (B∪C), so A' = A, B' = B
    -- Need B ⊆ parCell true (A∪C): by outer_segment_even on triple (A,C,B)
    have htripACB : isPsegmentTriple A C B :=
      isPsegmentTriple_swap (isPsegmentTriple_rotate htrip)
    refine ⟨A, B, htrip, hC, hAF, ?_, rfl, rfl, fun _ h => h⟩
    exact outer_segment_even A C B htripACB (by rwa [Finset.union_comm C B])
  · -- Case 2: A ⊄ parCell false (B∪C)
    rcases trap_odd_cell A B C htrip with hAF' | hBF | hCF
    · exact absurd hAF' hAF
    · -- B ⊆ parCell false (A∪C), so A' = B, B' = A
      have htripBAC : isPsegmentTriple B A C :=
        isPsegmentTriple_rotate (isPsegmentTriple_swap htrip)
      refine ⟨B, A, htripBAC, ?_, ?_, ?_,
        (Finset.union_comm A B), (Set.inter_comm (cls A) (cls B)),
        fun _ ⟨hPA, hPB⟩ => ⟨hPB, hPA⟩⟩
      · rwa [Finset.union_comm B A]
      · intro e he; exact hBF e he
      · -- A ⊆ parCell true (B∪C): by outer_segment_even on triple (B,C,A)
        exact outer_segment_even B C A (isPsegmentTriple_rotate htrip)
          (by rwa [Finset.union_comm C A])
    · -- C ⊆ parCell false (A∪B): contradicts C ⊆ parCell true (A∪B)
      exfalso
      obtain ⟨_, _, ⟨sC, hsC, _⟩, _⟩ := htrip
      obtain ⟨e, he⟩ := sC.nonempty
      exact parCell_disjoint (A ∪ B) false e ⟨hCF e (hsC ▸ he), hC e (hsC ▸ he)⟩
/-- HOL Light: `k33_rectagon_two_odd` (line 44349).
If f(i) ⊆ parCell true R, then for all j ≠ i, f(j) ⊆ parCell false R. -/
theorem k33_rectagon_two_odd (R : Rectagon) (f : Fin 3 → Finset (Set E2))
    (i : Fin 3) (h : k33RectagonHyp R f)
    (hfi : ∀ e ∈ f i, parCell true R.edges e) :
    ∀ j : Fin 3, j ≠ i → ∀ e ∈ f j, parCell false R.edges e := by
  obtain ⟨hclsij, hdisjij, hdecomp⟩ := h
  obtain ⟨A, B, hR, htripi, hmeet, hclsABempty⟩ := hdecomp i
  rw [hR] at hfi ⊢
  -- Apply psegment_triple_odd_even to rearrange A, B
  obtain ⟨A', B', htripA'B', _, hA'false, hB'true, hABunion, hclsABeq, hProp⟩ :=
    psegment_triple_odd_even A B (f i) htripi hfi
  -- Extract triple data for A', B'
  have htripA'B'' := htripA'B'
  obtain ⟨⟨sA', hsA', _⟩, ⟨sB', hsB', _⟩, _,
    _, ⟨rA'fI, hrA'fI⟩, ⟨rB'fI, hrB'fI⟩,
    _, _, _, _, _, _, _, _⟩ := htripA'B'
  -- For each j ≠ i
  intro j hji
  -- Get j-th decomposition
  obtain ⟨Aj, Bj, hRj, htripj, _, _⟩ := hdecomp j
  obtain ⟨_, _, ⟨sJ, hsJ, _⟩, _, _, _, _, hAjFj, hBjFj,
    _, h11j, h12j, h13j, h14j⟩ := htripj
  -- f(j) disjoint from A ∪ B = A' ∪ B'
  have hAjBj : Aj ∪ Bj = A ∪ B := hRj.symm.trans hR
  have hfjAuB : Disjoint (f j) (A ∪ B) := by
    rw [← hAjBj]; exact Finset.disjoint_union_right.mpr ⟨hAjFj.symm, hBjFj.symm⟩
  -- Transfer disjointness from A, B to A', B' using hProp
  have ⟨hfjA', hfjB'⟩ := hProp (fun X => Disjoint (f j) X)
    ⟨Finset.disjoint_of_subset_right Finset.subset_union_left hfjAuB,
     Finset.disjoint_of_subset_right Finset.subset_union_right hfjAuB⟩
  have hfjFi : Disjoint (f j) (f i) := hdisjij j i hji
  -- Cls conditions
  have hclsFiFj : cls (f i) ∩ cls (f j) = ∅ := hclsij i j hji.symm
  -- Transfer nonempty intersection: cls(f j) ∩ cls A' and cls(f j) ∩ cls B' nonempty
  have ⟨hclsJA', hclsJB'⟩ := hProp (fun X => (cls (f j) ∩ cls X).Nonempty) (hmeet j)
  -- Transfer cls A' ∩ cls B' intersection condition
  have hclsFjA'B' : cls (f j) ∩ cls A' ∩ cls B' = ∅ := by
    have h1 := hclsABempty j hji.symm -- cls (f j) ∩ cls A ∩ cls B = ∅
    rw [Set.inter_assoc, hclsABeq] at h1; rwa [Set.inter_assoc]
  -- Endpoint subset for cls (A' ∪ B')
  have hclsA'B'fj_sub : cls (A' ∪ B') ∩ cls (f j) ⊆ {m | sJ.isEndpoint m} := by
    rw [← hABunion]
    intro m ⟨hmAB, hmfj⟩
    change numClosure sJ.edges m = 1; rw [hsJ]
    rw [← hAjBj, cls_union] at hmAB
    rcases hmAB with hmAj | hmBj
    · have := Set.mem_inter hmAj hmfj; rw [h12j, h13j, h14j] at this; exact this
    · have := Set.mem_inter hmBj hmfj; rw [h11j, h13j, h14j] at this; exact this
  -- Witness points
  obtain ⟨u, huFj, huA'⟩ := hclsJA'
  obtain ⟨u', hu'Fj, hu'B'⟩ := hclsJB'
  -- Exclusion conditions
  have hu_notB' : u ∉ cls B' := by
    intro habs
    have hm : u ∈ cls (f j) ∩ cls A' ∩ cls B' := ⟨⟨huFj, huA'⟩, habs⟩
    simp only [hclsFjA'B', Set.mem_empty_iff_false] at hm
  have hu'_notA' : u' ∉ cls A' := by
    intro habs
    have hm : u' ∈ cls (f j) ∩ cls A' ∩ cls B' := ⟨⟨hu'Fj, habs⟩, hu'B'⟩
    simp only [hclsFjA'B', Set.mem_empty_iff_false] at hm
  have hu_notFi : u ∉ cls (f i) := by
    intro habs
    have hm : u ∈ cls (f i) ∩ cls (f j) := ⟨habs, huFj⟩
    simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  have hu'_notFi : u' ∉ cls (f i) := by
    intro habs
    have hm : u' ∈ cls (f i) ∩ cls (f j) := ⟨habs, hu'Fj⟩
    simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  -- Cls subset for meeting_lemma
  have hclsA'fI_sub : cls rA'fI.edges ∩ cls sJ.edges ⊆ {m | sJ.isEndpoint m} := by
    rw [hrA'fI, hsJ, cls_union]
    intro m ⟨hmA'fI, hmfj⟩
    rcases hmA'fI with hmA' | hmfI
    · exact hclsA'B'fj_sub ⟨by rw [cls_union]; exact Or.inl hmA', hmfj⟩
    · have hm : m ∈ cls (f i) ∩ cls (f j) := ⟨hmfI, hmfj⟩
      simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  have hclsB'fI_sub : cls rB'fI.edges ∩ cls sJ.edges ⊆ {m | sJ.isEndpoint m} := by
    rw [hrB'fI, hsJ, cls_union]
    intro m ⟨hmB'fI, hmfj⟩
    rcases hmB'fI with hmB' | hmfI
    · exact hclsA'B'fj_sub ⟨by rw [cls_union]; exact Or.inr hmB', hmfj⟩
    · have hm : m ∈ cls (f i) ∩ cls (f j) := ⟨hmfI, hmfj⟩
      simp only [hclsFiFj, Set.mem_empty_iff_false] at hm
  -- B'-side meeting_lemma (eps = false): R = rB'fI, B'' = A', v = u
  have hu_notB'fI : u ∉ cls rB'fI.edges := by
    rw [hrB'fI, cls_union]; intro h_abs
    rcases h_abs with hB' | hFi
    · exact hu_notB' hB'
    · exact hu_notFi hFi
  have hfjB'fI : Disjoint sJ.edges rB'fI.edges := by
    rw [hsJ, hrB'fI]; exact Finset.disjoint_union_right.mpr ⟨hfjB', hfjFi⟩
  have hA'false_rB'fI : ∀ e ∈ A', parCell false rB'fI.edges e := by
    intro e he; rw [hrB'fI]; exact hA'false e he
  have hfjB'fI_par : ∀ e ∈ sJ.edges, parCell false rB'fI.edges e :=
    meeting_lemma rB'fI A' sJ u false hA'false_rB'fI hfjB'fI hclsB'fI_sub
      (hsJ ▸ huFj) huA' hu_notB'fI (fun e he => sA'.all_edges e (hsA' ▸ he))
  -- A'-side meeting_lemma (eps = true): R = rA'fI, B'' = B', v = u'
  have hu'_notA'fI : u' ∉ cls rA'fI.edges := by
    rw [hrA'fI, cls_union]; intro h_abs
    rcases h_abs with hA' | hFi
    · exact hu'_notA' hA'
    · exact hu'_notFi hFi
  have hfjA'fI : Disjoint sJ.edges rA'fI.edges := by
    rw [hsJ, hrA'fI]; exact Finset.disjoint_union_right.mpr ⟨hfjA', hfjFi⟩
  have hB'true_rA'fI : ∀ e ∈ B', parCell true rA'fI.edges e := by
    intro e he; rw [hrA'fI]; exact hB'true e he
  have hfjA'fI_par : ∀ e ∈ sJ.edges, parCell true rA'fI.edges e :=
    meeting_lemma rA'fI B' sJ u' true hB'true_rA'fI hfjA'fI hclsA'fI_sub
      (hsJ ▸ hu'Fj) hu'B' hu'_notA'fI (fun e he => sB'.all_edges e (hsB' ▸ he))
  -- parCell_odd_imp: A = A', B = B', C = f(j), D = f(i)
  have hfjA'B'_false : ∀ e ∈ f j, parCell false (A' ∪ B') e := by
    apply parCell_odd_imp A' B' (f j) (f i) htripA'B'' sJ hsJ hclsA'B'fj_sub
      hfjA'.symm hfjB'.symm hfjFi
    · -- f(j) ⊆ parCell false (B' ∪ f(i))
      intro e he
      have := hfjB'fI_par e (hsJ ▸ he); rwa [hrB'fI] at this
    · -- f(j) ⊆ parCell true (A' ∪ f(i))
      intro e he
      have := hfjA'fI_par e (hsJ ▸ he); rwa [hrA'fI] at this
  rwa [hABunion]
/-! ## §W.3 Fin 3 utility lemmas -/
/-- HOL Light: `three_t_not_sing` (line 44562).
For any element of Fin 3, there exists a different element. -/
theorem fin3_not_sing (i : Fin 3) : ∃ j : Fin 3, i ≠ j := by
  fin_cases i <;> simp (config := { decide := true })
/-- HOL Light: `three_t_not_pair` (line 44595).
For any two elements of Fin 3, there exists a third distinct from both. -/
theorem fin3_not_pair (i j : Fin 3) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> simp (config := { decide := true })
/-- HOL Light: `three_delete_size` (line 44638).
Removing one element from Fin 3 gives a set of size 2. -/
theorem fin3_erase_card (i : Fin 3) : (Finset.univ.erase i).card = 2 := by
  fin_cases i <;> decide
/-- HOL Light: `bool_three_delete_bij` (line 44670).
There exists a bijection from Bool to (Fin 3 \ {i}). -/
theorem bool_fin3_delete_bij (i : Fin 3) :
    ∃ b : Bool → Fin 3, Function.Injective b ∧ (∀ e, b e ≠ i) ∧
      (∀ j : Fin 3, j ≠ i → ∃ e, j = b e) := by
  -- Get two distinct elements ≠ i
  obtain ⟨j, hj⟩ := fin3_not_sing i
  obtain ⟨k, hki, hkj⟩ := fin3_not_pair i j
  refine ⟨fun e => if e then j else k, ?_, ?_, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · intro e; cases e
    · exact hki
    · exact hj.symm
  · intro m hm
    -- m ≠ i, so m must be j or k since |Fin 3| = 3
    have : m = j ∨ m = k := by
      by_contra h; push Not at h
      have h1 := h.1; have h2 := h.2
      -- Now m ≠ i, m ≠ j, m ≠ k, but i, j, k cover Fin 3
      fin_cases m <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    rcases this with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
/-! ## §W.4 Key results -/
/-- HOL Light: `k33_rectagon_hyp_odd_exist` (line 44678).
Under k33_rectagon_hyp, some f(i) lies in parCell false R. -/
theorem k33_rectagon_hyp_odd_exist (R : Rectagon) (f : Fin 3 → Finset (Set E2))
    (h : k33RectagonHyp R f) : ∃ i, ∀ e ∈ f i, parCell false R.edges e := by
  -- Try i = 0. If f(0) ⊆ parCell false R, done.
  by_cases hj0 : ∀ e ∈ f 0, parCell false R.edges e
  · exact ⟨0, hj0⟩
  · -- f(0) not entirely in parCell false. Use segment_in_comp.
    obtain ⟨A, B, hR, htrip, _, _⟩ := h.2.2 0
    obtain ⟨_, _, ⟨sJ, hsJ, _⟩, _, _, _, _, hAC, hBC, _, h11, h12, h13, h14⟩ := htrip
    -- Disjointness: f(0) disjoint from R.edges = A ∪ B
    have hDisjR : Disjoint sJ.edges R.edges := by
      rw [hsJ, hR]; exact Finset.disjoint_union_right.mpr ⟨hAC.symm, hBC.symm⟩
    -- Closure condition: cls R ∩ cls (f 0) ⊆ endpoints of f 0
    have hEndEq : {m | numClosure A m = 1} = {m | numClosure (f 0) m = 1} :=
      h13.trans h14
    have hCls : ∀ m, m ∈ cls R.edges ∩ cls sJ.edges → sJ.isEndpoint m := by
      intro m ⟨hmR, hmS⟩
      simp only [Segment.isEndpoint, hsJ]
      rw [hR, cls_union] at hmR
      rw [hsJ] at hmS
      rcases hmR with hmA | hmB
      · have := Set.mem_inter hmA hmS
        rw [h12, hEndEq] at this; exact this
      · have := Set.mem_inter hmB hmS
        rw [h11, hEndEq] at this; exact this
    -- segment_in_comp: f(0) is in some parCell eps
    obtain ⟨eps, heps⟩ := segment_in_comp R sJ hDisjR hCls
    -- eps can't be false
    match eps with
    | false => exact absurd (fun e he => heps e (hsJ ▸ he)) hj0
    | true =>
      -- f(0) ⊆ parCell true R. By k33_rectagon_two_odd, f(1) ⊆ parCell false R.
      exact ⟨1, k33_rectagon_two_odd R f 0 h
        (fun e he => heps e (hsJ ▸ he)) 1 (by decide)⟩
/-- HOL Light: `k33_rectagon_hyp_false` (line 44710).
THE KEY PARITY RESULT: k33RectagonHyp is always false. -/
theorem k33_rectagon_hyp_false (R : Rectagon) (f : Fin 3 → Finset (Set E2)) :
    ¬k33RectagonHyp R f := by
  intro h
  -- Get i with f(i) ⊆ parCell false R
  obtain ⟨i, hfi⟩ := k33_rectagon_hyp_odd_exist R f h
  -- For all j ≠ i, f(j) ⊆ parCell true R
  have htrue := k33_rectagon_two_even R f i h hfi
  -- Pick j ≠ i
  obtain ⟨j, hij⟩ := fin3_not_sing i
  -- f(j) ⊆ parCell true R
  have hfj := htrue j hij.symm
  -- By k33_rectagon_two_odd with j, for all k ≠ j, f(k) ⊆ parCell false R
  have hfalse := k33_rectagon_two_odd R f j h hfj
  -- Pick k ≠ i and k ≠ j
  obtain ⟨k, hki, hkj⟩ := fin3_not_pair i j
  -- f(k) ∈ parCell true R AND parCell false R
  have hkT := htrue k hki
  have hkF := hfalse k hkj
  -- f(k) is nonempty: get isPsegmentTriple for some index
  have ⟨Ak, Bk, _, htripk, _⟩ := h.2.2 k
  have ⟨_, _, ⟨sK, hsK, _⟩, _⟩ := htripk
  obtain ⟨e, he⟩ := sK.nonempty
  exact parCell_disjoint R.edges true e ⟨hkT e (hsK ▸ he), hkF e (hsK ▸ he)⟩
/-! ## §W.5 Helpers for K₃,₃ construction -/
/-- Three segments with same endpoints, pairwise disjoint with matching closures,
form an isPsegmentTriple. Used in k33_rectag_to_hyp. -/
private theorem isPsegmentTriple_of_segment_end
    {A B C : Finset (Set E2)} {m p : ℤ × ℤ}
    (hA : segment_end A m p) (hB : segment_end B m p) (hC : segment_end C m p)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hclsAB : cls A ∩ cls B = ({m, p} : Set _))
    (hclsAC : cls A ∩ cls C = ({m, p} : Set _))
    (hclsBC : cls B ∩ cls C = ({m, p} : Set _)) :
    isPsegmentTriple A B C := by
  obtain ⟨GA, hGA, haA, hbA, hmp, huniqA⟩ := hA
  obtain ⟨GB, hGB, haB, hbB, _, huniqB⟩ := hB
  obtain ⟨GC, hGC, haC, hbC, _, huniqC⟩ := hC
  have hA' : segment_end A m p := ⟨GA, hGA, haA, hbA, hmp, huniqA⟩
  have hB' : segment_end B m p := ⟨GB, hGB, haB, hbB, hmp, huniqB⟩
  have hC' : segment_end C m p := ⟨GC, hGC, haC, hbC, hmp, huniqC⟩
  have epOf : ∀ (G : Segment) (E : Finset (Set E2)) (a b : ℤ × ℤ),
      G.edges = E → G.isEndpoint a → G.isEndpoint b → a ≠ b →
      (∀ x, G.isEndpoint x → x = a ∨ x = b) →
      {x : ℤ × ℤ | numClosure E x = 1} = ({a, b} : Set _) := by
    intro G E a b hE ha hb hab huniq; ext x
    simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => huniq x (show numClosure G.edges x = 1 by rw [hE]; exact hx),
      fun h => by rcases h with rfl | rfl <;> [exact hE ▸ ha; exact hE ▸ hb]⟩
  have hepA := epOf GA A m p hGA haA hbA hmp huniqA
  have hepB := epOf GB B m p hGB haB hbB hmp huniqB
  have hepC := epOf GC C m p hGC haC hbC hmp huniqC
  obtain ⟨rAB, hrAB⟩ := segment_end_union_rectagon hA' hB' hAB hclsAB
  obtain ⟨rAC, hrAC⟩ := segment_end_union_rectagon hA' hC' hAC hclsAC
  obtain ⟨rBC, hrBC⟩ := segment_end_union_rectagon hB' hC' hBC hclsBC
  exact ⟨⟨GA, hGA, m, p, hmp, haA, hbA, huniqA⟩,
    ⟨GB, hGB, m, p, hmp, haB, hbB, huniqB⟩,
    ⟨GC, hGC, m, p, hmp, haC, hbC, huniqC⟩,
    ⟨rAB, hrAB⟩, ⟨rAC, hrAC⟩, ⟨rBC, hrBC⟩,
    hAB, hAC, hBC,
    hclsAB.trans hepA.symm, hclsBC.trans hepA.symm, hclsAC.trans hepA.symm,
    hepA.trans hepB.symm, hepB.trans hepC.symm⟩


-- Elevated heartbeats: §W.6 contains multiple `fin_cases` on `Fin 3` and `Fin 3 × Fin 3`
-- (9 cases each) for K₃,₃ vertex/edge membership and injectivity proofs; the default
-- budget is insufficient for the combined elaboration of this section.
set_option linter.style.setOption false in
set_option maxHeartbeats 800000

/-! ## §W.6 Rectagonal K₃,₃ characterization -/

private def leftV : Fin 3 → ℕ | 0 => 1 | 1 => 2 | 2 => 3
private def rightV : Fin 3 → ℕ | 0 => 10 | 1 => 20 | 2 => 30

private theorem leftV_mem (i : Fin 3) : leftV i ∈ K33.vertexSet := by
  fin_cases i <;> simp [leftV, K33]

private theorem rightV_mem (j : Fin 3) : rightV j ∈ K33.vertexSet := by
  fin_cases j <;> simp [rightV, K33]

private theorem leftV_ne_rightV (i j : Fin 3) : leftV i ≠ rightV j := by
  fin_cases i <;> fin_cases j <;> simp [leftV, rightV]

private theorem leftV_injective : Function.Injective leftV := by
  intro i₁ i₂ h; fin_cases i₁ <;> fin_cases i₂ <;> simp_all [leftV]

private theorem rightV_injective : Function.Injective rightV := by
  intro j₁ j₂ h; fin_cases j₁ <;> fin_cases j₂ <;> simp_all [rightV]

private theorem edge_mem (i j : Fin 3) :
    ({leftV i, rightV j} : Finset ℕ) ∈ K33.edgeSet := by
  fin_cases i <;> fin_cases j <;> simp only [leftV, rightV] <;>
    change _ ∈ ({{1, 10}, {2, 10}, {3, 10}, {1, 20}, {2, 20}, {3, 20},
                  {1, 30}, {2, 30}, {3, 30}} : Set (Finset ℕ)) <;>
    simp

private theorem finset_eq_imp' (i₁ j₁ i₂ j₂ : Fin 3)
    (h : ({leftV i₁, rightV j₁} : Finset ℕ) = {leftV i₂, rightV j₂}) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  constructor
  · have h₁ : leftV i₁ ∈ ({leftV i₂, rightV j₂} : Finset ℕ) :=
      h ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₁
    exact h₁.elim (fun h => leftV_injective h)
      (fun h => absurd h (leftV_ne_rightV i₁ j₂))
  · have h₂ : rightV j₁ ∈ ({leftV i₂, rightV j₂} : Finset ℕ) := by
      rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₂
    exact h₂.elim (fun h => absurd h.symm (leftV_ne_rightV i₂ j₁))
      (fun h => rightV_injective h)

set_option maxHeartbeats 1600000 in
-- Elevated heartbeats: the biconditional proof unfolds K₃,₃ graph isomorphisms and constructs
-- `segment_end` embeddings for all 9 pairs in `Fin 3 × Fin 3`, generating many `simp` and
-- `fin_cases` goals that together push elaboration well past the default limit.
/-- HOL Light: `rectagonal_graph_k33` (line 44772).
K₃,₃ is rectagonal iff there exist segment_end embeddings with injective
vertex maps and disjoint closure intersections. -/
theorem rectagonal_graph_k33 :
    isRectagonalGraph K33 ↔
    ∃ (f : Fin 3 × Fin 3 → Finset (Set E2))
      (uA uB : Fin 3 → ℤ × ℤ),
      Function.Injective uA ∧
      Function.Injective uB ∧
      (∀ i : Fin 3 × Fin 3, segment_end (f i) (uA i.1) (uB i.2)) ∧
      (∀ i j, (f i ∩ f j).Nonempty → i = j) ∧
      (∀ i j, i ≠ j → cls (f i) ∩ cls (f j) =
        {m | numClosure (f i) m = 1} ∩ {m | numClosure (f j) m = 1}) := by
  constructor
  · -- FORWARD
    rintro ⟨H, ⟨h_pseg, h_inc, h_disj, h_cls⟩, hiso⟩
    obtain ⟨siso⟩ := @graphIsomorphic_symm _ _ _ _
      ⟨((0 : ℤ), (0 : ℤ))⟩ ⟨(∅ : Finset (Set E2))⟩ _ _ hiso
    refine ⟨fun ij => siso.edgeMap {leftV ij.1, rightV ij.2},
            fun i => siso.vertexMap (leftV i),
            fun j => siso.vertexMap (rightV j), ?_, ?_, ?_, ?_, ?_⟩
    · -- uA injective
      exact fun i₁ i₂ h => leftV_injective
        (siso.vertexBij.injOn (leftV_mem i₁) (leftV_mem i₂) h)
    · -- uB injective
      exact fun j₁ j₂ h => rightV_injective
        (siso.vertexBij.injOn (rightV_mem j₁) (rightV_mem j₂) h)
    · -- segment_end
      intro ⟨i, j⟩
      have hfe := siso.edgeBij.mapsTo (edge_mem i j)
      have hset : {m | numClosure (siso.edgeMap {leftV i, rightV j}) m = 1} =
          ({siso.vertexMap (leftV i), siso.vertexMap (rightV j)} : Set _) := by
        rw [← h_inc _ hfe, siso.preserves_inc _ (edge_mem i j)]
        change siso.vertexMap '' (↑({leftV i, rightV j} : Finset ℕ) : Set ℕ) = _
        rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair]
      obtain ⟨a, b, G, hGe, ha, hb, _, huniq⟩ := h_pseg _ hfe
      refine ⟨G, hGe, ?_, ?_, ?_, ?_⟩
      · rw [Segment.isEndpoint, hGe]
        have : siso.vertexMap (leftV i) ∈
            {m | numClosure (siso.edgeMap {leftV i, rightV j}) m = 1} := by
          rw [hset]; exact Set.mem_insert _ _
        exact this
      · rw [Segment.isEndpoint, hGe]
        have : siso.vertexMap (rightV j) ∈
            {m | numClosure (siso.edgeMap {leftV i, rightV j}) m = 1} := by
          rw [hset]; exact Set.mem_insert_of_mem _ rfl
        exact this
      · exact fun heq => absurd (siso.vertexBij.injOn (leftV_mem i) (rightV_mem j) heq)
          (leftV_ne_rightV i j)
      · intro m hm; rw [Segment.isEndpoint, hGe] at hm
        have hmem : m ∈
            ({siso.vertexMap (leftV i), siso.vertexMap (rightV j)} : Set _) := by
          rw [← hset]; exact hm
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    · -- (f i ∩ f j).Nonempty → i = j
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne; by_contra hne_ij
      have hne_e : siso.edgeMap {leftV i₁, rightV j₁} ≠
          siso.edgeMap {leftV i₂, rightV j₂} := by
        intro heq; apply hne_ij
        have := finset_eq_imp' i₁ j₁ i₂ j₂
          (siso.edgeBij.injOn (edge_mem i₁ j₁) (edge_mem i₂ j₂) heq)
        exact Prod.ext this.1 this.2
      have := Finset.disjoint_iff_inter_eq_empty.mp
        (h_disj _ (siso.edgeBij.mapsTo (edge_mem i₁ j₁)) _
          (siso.edgeBij.mapsTo (edge_mem i₂ j₂)) hne_e)
      rw [this] at hne; exact Finset.not_nonempty_empty hne
    · -- cls intersection
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne
      have hne_e : siso.edgeMap {leftV i₁, rightV j₁} ≠
          siso.edgeMap {leftV i₂, rightV j₂} := by
        intro heq; exact hne (Prod.ext
          (finset_eq_imp' i₁ j₁ i₂ j₂
            (siso.edgeBij.injOn (edge_mem i₁ j₁) (edge_mem i₂ j₂) heq)).1
          (finset_eq_imp' i₁ j₁ i₂ j₂
            (siso.edgeBij.injOn (edge_mem i₁ j₁) (edge_mem i₂ j₂) heq)).2)
      exact h_cls _ (siso.edgeBij.mapsTo (edge_mem i₁ j₁)) _
        (siso.edgeBij.mapsTo (edge_mem i₂ j₂)) hne_e
  · -- BACKWARD
    rintro ⟨f, uA, uB, hinjA, hinjB, hseg, hfjdisj, hcls⟩
    have huAuB : ∀ i j, uA i ≠ uB j := fun i j => segment_end_disj (hseg (i, j))
    have hf_inj : Function.Injective f := by
      intro ij₁ ij₂ heq; apply hfjdisj
      rw [heq, Finset.inter_self]; exact segment_end_finite (hseg ij₂)
    have seg_ep : ∀ ij : Fin 3 × Fin 3,
        {m | numClosure (f ij) m = 1} = ({uA ij.1, uB ij.2} : Set _) := by
      intro ⟨i, j⟩
      obtain ⟨G, hGe, ha, hb, _, huniq⟩ := hseg (i, j)
      ext m; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun hm => huniq m (by rwa [Segment.isEndpoint, hGe]),
             fun h => by rcases h with rfl | rfl <;> rwa [← hGe]⟩
    have huB_not_rangeA : ∀ j, uB j ∉ Set.range uA :=
      fun j ⟨i, hi⟩ => absurd hi (huAuB i j)
    have invA_left : ∀ i, Function.invFun uA (uA i) = i :=
      fun i => hinjA (Function.invFun_eq ⟨i, rfl⟩)
    have invB_left : ∀ j, Function.invFun uB (uB j) = j :=
      fun j => hinjB (Function.invFun_eq ⟨j, rfl⟩)
    have invF_left : ∀ ij, Function.invFun f (f ij) = ij :=
      fun ij => hf_inj (Function.invFun_eq ⟨ij, rfl⟩)
    let H : HolGraph (ℤ × ℤ) (Finset (Set E2)) :=
      { vertexSet := Set.range uA ∪ Set.range uB
        edgeSet := Set.range f
        inc := fun e => {m | numClosure e m = 1}
        well_formed := fun e he => by
          obtain ⟨ij, rfl⟩ := he
          rw [seg_ep ij]; constructor
          · intro m hm
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
            rcases hm with rfl | rfl
            · exact Set.mem_union_left _ ⟨ij.1, rfl⟩
            · exact Set.mem_union_right _ ⟨ij.2, rfl⟩
          · exact Set.ncard_pair (huAuB ij.1 ij.2) }
    refine ⟨H, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro e ⟨ij, rfl⟩; exact ⟨uA ij.1, uB ij.2, hseg ij⟩
    · exact fun _ _ => rfl
    · intro e₁ he₁ e₂ he₂ hne
      obtain ⟨ij₁, rfl⟩ := he₁; obtain ⟨ij₂, rfl⟩ := he₂
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hne (congrArg f (hfjdisj _ _ ⟨x, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩))
    · intro e₁ he₁ e₂ he₂ hne
      obtain ⟨ij₁, rfl⟩ := he₁; obtain ⟨ij₂, rfl⟩ := he₂
      exact hcls ij₁ ij₂ (fun h => hne (congrArg f h))
    · -- GraphIsomorphic H K33
      let vm : ℤ × ℤ → ℕ := fun v =>
        if v ∈ Set.range uA then leftV (Function.invFun uA v)
        else rightV (Function.invFun uB v)
      let em : Finset (Set E2) → Finset ℕ := fun e =>
        let ij := Function.invFun f e
        {leftV ij.1, rightV ij.2}
      have hvm_uA : ∀ i, vm (uA i) = leftV i := fun i => by
        simp only [vm, Set.mem_range, exists_apply_eq_apply, ite_true, invA_left]
      have hvm_uB : ∀ j, vm (uB j) = rightV j := fun j => by
        simp only [vm, show ¬(uB j ∈ Set.range uA) from huB_not_rangeA j, ite_false,
          invB_left]
      have hem_f : ∀ ij : Fin 3 × Fin 3,
          em (f ij) = {leftV ij.1, rightV ij.2} := fun ij => by
        simp only [em, invF_left]
      refine ⟨⟨vm, em, ?_, ?_, ?_⟩⟩
      · -- vertexBij
        refine ⟨?_, ?_, ?_⟩
        · intro v hv; rcases hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
          · rw [hvm_uA]; exact leftV_mem i
          · rw [hvm_uB]; exact rightV_mem j
        · intro v₁ hv₁ v₂ hv₂ heq
          rcases hv₁ with ⟨i₁, rfl⟩ | ⟨j₁, rfl⟩ <;>
            rcases hv₂ with ⟨i₂, rfl⟩ | ⟨j₂, rfl⟩
          · rw [hvm_uA, hvm_uA] at heq; exact congrArg uA (leftV_injective heq)
          · rw [hvm_uA, hvm_uB] at heq; exact absurd heq (leftV_ne_rightV i₁ j₂)
          · rw [hvm_uB, hvm_uA] at heq; exact absurd heq.symm (leftV_ne_rightV i₂ j₁)
          · rw [hvm_uB, hvm_uB] at heq; exact congrArg uB (rightV_injective heq)
        · intro n hn
          simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
          rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨uA 0, Set.mem_union_left _ ⟨0, rfl⟩, hvm_uA 0⟩
          · exact ⟨uA 1, Set.mem_union_left _ ⟨1, rfl⟩, hvm_uA 1⟩
          · exact ⟨uA 2, Set.mem_union_left _ ⟨2, rfl⟩, hvm_uA 2⟩
          · exact ⟨uB 0, Set.mem_union_right _ ⟨0, rfl⟩, hvm_uB 0⟩
          · exact ⟨uB 1, Set.mem_union_right _ ⟨1, rfl⟩, hvm_uB 1⟩
          · exact ⟨uB 2, Set.mem_union_right _ ⟨2, rfl⟩, hvm_uB 2⟩
      · -- edgeBij
        refine ⟨?_, ?_, ?_⟩
        · intro e he; obtain ⟨ij, rfl⟩ := he; rw [hem_f]; exact edge_mem ij.1 ij.2
        · intro e₁ he₁ e₂ he₂ heq
          obtain ⟨ij₁, rfl⟩ := he₁; obtain ⟨ij₂, rfl⟩ := he₂
          rw [hem_f, hem_f] at heq
          exact congrArg f (Prod.ext (finset_eq_imp' _ _ _ _ heq).1
            (finset_eq_imp' _ _ _ _ heq).2)
        · intro ek hek
          simp only [K33, Set.mem_insert_iff, Set.mem_singleton_iff] at hek
          rcases hek with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first
            | exact ⟨f (0, 0), ⟨(0, 0), rfl⟩, hem_f _⟩
            | exact ⟨f (1, 0), ⟨(1, 0), rfl⟩, hem_f _⟩
            | exact ⟨f (2, 0), ⟨(2, 0), rfl⟩, hem_f _⟩
            | exact ⟨f (0, 1), ⟨(0, 1), rfl⟩, hem_f _⟩
            | exact ⟨f (1, 1), ⟨(1, 1), rfl⟩, hem_f _⟩
            | exact ⟨f (2, 1), ⟨(2, 1), rfl⟩, hem_f _⟩
            | exact ⟨f (0, 2), ⟨(0, 2), rfl⟩, hem_f _⟩
            | exact ⟨f (1, 2), ⟨(1, 2), rfl⟩, hem_f _⟩
            | exact ⟨f (2, 2), ⟨(2, 2), rfl⟩, hem_f _⟩
      · -- preserves_inc
        intro e he; obtain ⟨ij, rfl⟩ := he
        change (↑(em (f ij)) : Set ℕ) = vm '' {m | numClosure (f ij) m = 1}
        rw [hem_f, seg_ep ij, Set.image_pair, hvm_uA, hvm_uB]
        simp [Finset.coe_insert, Finset.coe_singleton]

set_option maxHeartbeats 800000 in
-- Elevated heartbeats: constructing `k33RectagonHyp` from 9 `segment_end` embeddings
-- requires verifying pairwise disjointness and closure intersection conditions over all
-- pairs in `Fin 3 × Fin 3`, resulting in a long chain of `Finset` membership goals.
/-- Given K₃,₃ rectagonal embedding data, construct k33RectagonHyp.
This is the core construction of `rectagon_graph_k33_false`.
HOL Light: lines 45048–45369 (~320 lines). -/
theorem k33_rectag_to_hyp
    (f : Fin 3 × Fin 3 → Finset (Set E2))
    (uA uB : Fin 3 → ℤ × ℤ)
    (hinjA : Function.Injective uA) (hinjB : Function.Injective uB)
    (hseg : ∀ i : Fin 3 × Fin 3, segment_end (f i) (uA i.1) (uB i.2))
    (hfjdisj : ∀ i j, (f i ∩ f j).Nonempty → i = j)
    (hcls : ∀ i j, i ≠ j → cls (f i) ∩ cls (f j) =
      {m | numClosure (f i) m = 1} ∩ {m | numClosure (f j) m = 1}) :
    ∃ (R : Rectagon) (diag : Fin 3 → Finset (Set E2)), k33RectagonHyp R diag := by
  have huAuB : ∀ i j, uA i ≠ uB j := by
    intro i j; exact segment_end_disj (hseg (i, j))
  -- Pairwise disjoint edges: f(i,j) ∩ f(i',j') = ∅ when (i,j) ≠ (i',j')
  have hfij_disj : ∀ i j : Fin 3 × Fin 3, i ≠ j → Disjoint (f i) (f j) := by
    intro i j hne
    rw [Finset.disjoint_left]
    intro e hi hj
    exact hne (hfjdisj i j ⟨e, Finset.mem_inter.mpr ⟨hi, hj⟩⟩)
  -- cls diag disjoint
  have hcls_diag : ∀ i j : Fin 3, i ≠ j →
      cls (f (i, i)) ∩ cls (f (j, j)) = ∅ := by
    intro i j hne
    have hpair : (i, i) ≠ (j, j) := by intro h; exact hne (Prod.mk.inj h).1
    rw [hcls _ _ hpair]
    ext m; simp only [Set.mem_inter_iff, Set.mem_setOf, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hm1 hm2
    -- m is endpoint of both f(i,i) and f(j,j)
    obtain ⟨Gi, hGi, _, _, _, huniqI⟩ := hseg (i, i)
    obtain ⟨Gj, hGj, _, _, _, huniqJ⟩ := hseg (j, j)
    have hm_i : m = uA i ∨ m = uB i :=
      huniqI m (show numClosure Gi.edges m = 1 by rw [hGi]; exact hm1)
    have hm_j : m = uA j ∨ m = uB j :=
      huniqJ m (show numClosure Gj.edges m = 1 by rw [hGj]; exact hm2)
    rcases hm_i with hi | hi <;> rcases hm_j with hj | hj
    · exact absurd (hinjA (hi.symm.trans hj)) hne
    · exact absurd (hi.symm.trans hj) (huAuB i j)
    · exact absurd (hj.symm.trans hi) (huAuB j i)
    · exact absurd (hinjB (hi.symm.trans hj)) hne
  -- Disjoint diagonal edges
  have hdiag_disj : ∀ i j : Fin 3, i ≠ j → Disjoint (f (i, i)) (f (j, j)) := by
    intro i j hne; exact hfij_disj _ _ (by intro h; exact hne (Prod.mk.inj h).1)
  -- Endpoint helper: endpoints of f(p) are exactly {uA p.1, uB p.2}
  have hep : ∀ (p : Fin 3 × Fin 3) (m : ℤ × ℤ),
      numClosure (f p) m = 1 → m = uA p.1 ∨ m = uB p.2 := by
    intro p m hm
    obtain ⟨G, hG, _, _, _, huniq⟩ := hseg p
    exact huniq m (show numClosure G.edges m = 1 by rw [hG]; exact hm)
  have hep_set : ∀ p : Fin 3 × Fin 3,
      {m : ℤ × ℤ | numClosure (f p) m = 1} = ({uA p.1, uB p.2} : Set _) := by
    intro p; ext m
    simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact hep p m
    · obtain ⟨G, hG, ha, hb, _, _⟩ := hseg p
      rintro (rfl | rfl)
      · exact hG ▸ ha
      · exact hG ▸ hb
  -- cls intersection = endpoint intersection for distinct edges
  have hcls_ep : ∀ (p q : Fin 3 × Fin 3), p ≠ q →
      cls (f p) ∩ cls (f q) =
        ({uA p.1, uB p.2} : Set _) ∩ {uA q.1, uB q.2} := by
    intro p q hne; rw [hcls _ _ hne, hep_set p, hep_set q]
  -- Endpoint membership helper: endpoint is in cls
  have hep_cls : ∀ (p : Fin 3 × Fin 3), uA p.1 ∈ cls (f p) ∧ uB p.2 ∈ cls (f p) := by
    intro p; exact ⟨segment_end_cls (hseg p), segment_end_cls2 (hseg p)⟩
  -- 4-way intersection emptiness helper
  have hint_empty : ∀ (a₁ a₂ b₁ b₂ : ℤ × ℤ),
      a₁ ≠ b₁ → a₁ ≠ b₂ → a₂ ≠ b₁ → a₂ ≠ b₂ →
      ({a₁, a₂} : Set _) ∩ {b₁, b₂} = ∅ := by
    intro a₁ a₂ b₁ b₂ h1 h2 h3 h4
    ext m; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> rintro (rfl | rfl) <;> contradiction
  -- Singleton intersection helper
  have hint_sing : ∀ (a b₁ b₂ : ℤ × ℤ), a ≠ b₁ → a ≠ b₂ → b₁ ≠ b₂ →
      ({a, b₁} : Set _) ∩ {a, b₂} = {a} := by
    intro a b₁ b₂ h1 h2 h3
    ext m; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨h1', h2'⟩
      rcases h1' with rfl | rfl
      · rfl
      · rcases h2' with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h3
    · intro h; exact ⟨Or.inl h, Or.inl h⟩
  -- Main construction
  -- For each i, get b : Bool → Fin 3 with b e ≠ i and b injective
  -- Define A(eps) = f(i, b eps) ∪ (f(b(!eps), i) ∪ f(b(!eps), b eps))
  have key : ∀ i : Fin 3,
      ∃ A : Bool → Finset (Set E2),
        (∀ eps, segment_end (A eps) (uA i) (uB i)) ∧
        Disjoint (A true) (A false) ∧
        (cls (A true) ∩ cls (A false) = ({uA i, uB i} : Set _)) ∧
        (∀ eps, Disjoint (A eps) (f (i, i))) ∧
        (∀ eps, cls (A eps) ∩ cls (f (i, i)) = ({uA i, uB i} : Set _)) ∧
        (∀ j : Fin 3, ∀ eps : Bool, (cls (f (j, j)) ∩ cls (A eps)).Nonempty) ∧
        (∀ e, e ∈ A true ∪ A false ↔ ∃ a b : Fin 3, a ≠ b ∧ e ∈ f (a, b)) := by
    intro i
    obtain ⟨b, hb_inj, hb_ne, hb_surj⟩ := bool_fin3_delete_bij i
    have hbTF : b true ≠ b false := fun h => Bool.noConfusion (hb_inj h)
    -- All pairs from AT/AF are distinct from (i,i)
    have hne_ib : ∀ e, (i, b e) ≠ (i, i) := fun e => by simp [Prod.mk.injEq, hb_ne e]
    have hne_bi : ∀ e, (b e, i) ≠ (i, i) := fun e => by simp [Prod.mk.injEq, hb_ne e]
    have hne_bb : ∀ e, (b (!e), b e) ≠ (i, i) := fun e => by
      simp [Prod.mk.injEq, hb_ne (!e)]
    -- Define A(eps)
    refine ⟨fun eps => f (i, b eps) ∪ (f (b (!eps), i) ∪ f (b (!eps), b eps)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (1) segment_end (A eps) (uA i) (uB i)
      intro eps
      -- Chain 1: f(b(!eps), i) ∪ f(b(!eps), b eps) from uB(i) to uB(b eps)
      have h_s1 : segment_end (f (b (!eps), i)) (uA (b (!eps))) (uB i) := hseg _
      have h_s1' : segment_end (f (b (!eps), i)) (uB i) (uA (b (!eps))) :=
        (segment_end_symm _ _ _).mp h_s1
      have h_s2 : segment_end (f (b (!eps), b eps)) (uA (b (!eps))) (uB (b eps)) := hseg _
      have h_cls1 : cls (f (b (!eps), i)) ∩ cls (f (b (!eps), b eps)) =
          ({uA (b (!eps))} : Set _) := by
        rw [hcls_ep _ _ (by intro h; exact (hb_ne eps).symm (congr_arg Prod.snd h))]
        exact hint_sing _ _ _
          (huAuB _ _)
          (huAuB _ _)
          (fun h => (hb_ne eps).symm (hinjB h))
      have h_chain1 : segment_end (f (b (!eps), i) ∪ f (b (!eps), b eps))
          (uB i) (uB (b eps)) :=
        segment_end_union h_s1' h_s2 h_cls1
      -- Chain 2: f(i, b eps) ∪ chain1 from uA(i) to uB(i)
      have h_s3 : segment_end (f (i, b eps)) (uA i) (uB (b eps)) := hseg _
      have h_chain1' : segment_end (f (b (!eps), i) ∪ f (b (!eps), b eps))
          (uB (b eps)) (uB i) :=
        (segment_end_symm _ _ _).mp h_chain1
      have h_cls2 : cls (f (i, b eps)) ∩
          cls (f (b (!eps), i) ∪ f (b (!eps), b eps)) =
          ({uB (b eps)} : Set _) := by
        rw [cls_union]
        -- Distribute and compute
        rw [Set.inter_union_distrib_left,
          hcls_ep _ _ (by intro h; exact (hb_ne (!eps)).symm (congr_arg Prod.fst h)),
          hcls_ep _ _ (by intro h; exact (hb_ne (!eps)).symm (congr_arg Prod.fst h))]
        -- Both intersections: one is empty, one is {uB(b eps)}
        have : ({uA i, uB (b eps)} : Set _) ∩ {uA (b (!eps)), uB i} = ∅ :=
          hint_empty _ _ _ _
            (fun h => absurd (hinjA h) (hb_ne (!eps)).symm)
            (huAuB _ _) (huAuB _ _).symm
            (fun h => absurd (hinjB h) (hb_ne eps))
        have : ({uA i, uB (b eps)} : Set _) ∩ {uA (b (!eps)), uB (b eps)} =
            {uB (b eps)} := by
          rw [Set.pair_comm (uA i), Set.pair_comm (uA (b (!eps)))]
          exact hint_sing _ _ _ (huAuB _ _).symm (huAuB _ _).symm
            (fun h => (hb_ne (!eps)).symm (hinjA h))
        simp only [*, Set.empty_union]
      exact segment_end_union h_s3 h_chain1' h_cls2
    · -- (2) Disjoint (A true) (A false)
      rw [Finset.disjoint_left]
      intro e heT heF
      simp only [Finset.mem_union] at heT heF
      rcases heT with heT | heT | heT <;> rcases heF with heF | heF | heF <;> {
        have heq := hfjdisj _ _ ⟨e, Finset.mem_inter.mpr ⟨heT, heF⟩⟩
        first
        | exact hbTF (congr_arg Prod.snd heq)
        | exact hbTF.symm (congr_arg Prod.snd heq)
        | exact hbTF (congr_arg Prod.fst heq)
        | exact hbTF.symm (congr_arg Prod.fst heq)
        | exact (hb_ne _) (congr_arg Prod.fst heq)
        | exact (hb_ne _).symm (congr_arg Prod.fst heq) }
    · -- (3) cls (A true) ∩ cls (A false) = {uA i, uB i}
      apply Set.Subset.antisymm
      · -- Subset direction: any element is uA i or uB i
        intro m ⟨hmT, hmF⟩
        simp only [cls_union, Set.mem_union] at hmT hmF
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hmT with hmT | hmT | hmT <;> rcases hmF with hmF | hmF | hmF <;> {
          have hm := Set.mem_inter hmT hmF
          rw [hcls_ep _ _ (by intro h; first
            | exact hbTF (congr_arg Prod.snd h)
            | exact hbTF.symm (congr_arg Prod.fst h)
            | exact (hb_ne _).symm (congr_arg Prod.fst h)
            | exact (hb_ne _) (congr_arg Prod.fst h))] at hm
          simp only [Set.mem_inter_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hm
          obtain ⟨hp, hq⟩ := hm
          rcases hp with hp | hp <;> rcases hq with hq | hq
          all_goals first
            | left; exact hp
            | left; exact hq
            | right; exact hp
            | right; exact hq
            | exact absurd (hp.symm.trans hq) (huAuB _ _)
            | exact absurd (hp.symm.trans hq) (huAuB _ _).symm
            | exact absurd (hinjA (hp.symm.trans hq)) hbTF
            | exact absurd (hinjA (hp.symm.trans hq)) hbTF.symm
            | exact absurd (hinjA (hp.symm.trans hq)) (hb_ne _)
            | exact absurd (hinjA (hp.symm.trans hq)) (hb_ne _).symm
            | exact absurd (hinjB (hp.symm.trans hq)) hbTF }
      · -- Superset direction: uA i and uB i are in both halves
        intro m hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        constructor
        · -- m ∈ cls (A true)
          simp only [cls_union, Set.mem_union]
          rcases hm with rfl | rfl
          · left; exact (hep_cls (i, b true)).1
          · right; left; exact (hep_cls (b false, i)).2
        · -- m ∈ cls (A false)
          simp only [cls_union, Set.mem_union]
          rcases hm with rfl | rfl
          · left; exact (hep_cls (i, b false)).1
          · right; left; exact (hep_cls (b true, i)).2
    · -- (4) Disjoint (A eps) (f (i, i))
      intro eps
      rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨hfij_disj _ _ (hne_ib eps),
        hfij_disj _ _ (hne_bi (!eps)), hfij_disj _ _ (hne_bb eps)⟩
    · -- (5) cls (A eps) ∩ cls (f (i, i)) = {uA i, uB i}
      intro eps
      apply Set.Subset.antisymm
      · -- Subset: use cls intersection conditions
        intro m ⟨hmA, hmii⟩
        simp only [cls_union, Set.mem_union] at hmA
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hmA with hmA | hmA | hmA <;> {
          have hm := Set.mem_inter hmA hmii
          rw [show (_, _) = (i, i) from rfl, hcls_ep _ (i, i) (by
            first | exact hne_ib eps | exact hne_bi (!eps) | exact hne_bb eps)] at hm
          simp only [Set.mem_inter_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hm
          obtain ⟨hp, hq⟩ := hm
          rcases hp with hp | hp <;> rcases hq with hq | hq
          all_goals first
            | left; exact hp
            | left; exact hq
            | right; exact hp
            | right; exact hq
            }
      · -- Superset
        intro m hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        constructor
        · simp only [cls_union, Set.mem_union]
          rcases hm with rfl | rfl
          · left; exact (hep_cls (i, b eps)).1
          · right; left; exact (hep_cls (b (!eps), i)).2
        · rcases hm with rfl | rfl
          · exact (hep_cls (i, i)).1
          · exact (hep_cls (i, i)).2
    · -- (6) Meeting conditions: cls(f(j,j)) ∩ cls(A eps) is nonempty
      intro j eps
      by_cases hji : j = i
      · -- j = i: uA i is in both
        rw [hji]
        exact ⟨uA i, (hep_cls (i, i)).1,
          by simp only [cls_union, mem_union]; left; exact (hep_cls (i, b eps)).1⟩
      · -- j ≠ i: j = b e for some e
        obtain ⟨e, rfl⟩ := hb_surj j hji
        by_cases he : e = eps
        · -- e = eps: f(b eps, b eps) shares uB(b eps) with f(i, b eps) ∈ A(eps)
          rw [he]
          exact ⟨uB (b eps),
            (hep_cls (b eps, b eps)).2,
            by simp only [cls_union, mem_union]; left; exact (hep_cls (i, b eps)).2⟩
        · -- e ≠ eps: e = !eps
          have he' : e = !eps := by
            cases e <;> cases eps <;> first | rfl | exact absurd rfl he
          subst he'
          exact ⟨uA (b (!eps)),
            (hep_cls (b (!eps), b (!eps))).1,
            by simp only [cls_union, mem_union]; right; left; exact (hep_cls (b (!eps), i)).1⟩
    · -- (7) Characterization: e ∈ A(T) ∪ A(F) ↔ ∃ a b, a ≠ b ∧ e ∈ f(a,b)
      intro e; constructor
      · -- Forward: each term in A has distinct indices
        intro he
        simp only [Finset.mem_union] at he
        rcases he with (h | h | h) | (h | h | h)
        · exact ⟨i, b true, (hb_ne true).symm, h⟩
        · exact ⟨b false, i, hb_ne false, h⟩
        · exact ⟨b false, b true, fun h => absurd (hb_inj h) (by simp), h⟩
        · exact ⟨i, b false, (hb_ne false).symm, h⟩
        · exact ⟨b true, i, hb_ne true, h⟩
        · exact ⟨b true, b false, fun h => absurd (hb_inj h) (by simp), h⟩
      · -- Backward: every off-diagonal f(a,c) with a ≠ c is in A(T) ∪ A(F)
        rintro ⟨a, c, hac, he⟩
        simp only [Finset.mem_union]
        have ha : a = i ∨ ∃ ea, a = b ea := by
          by_cases h : a = i
          · left; exact h
          · right; exact hb_surj a h
        have hc : c = i ∨ ∃ ec, c = b ec := by
          by_cases h : c = i
          · left; exact h
          · right; exact hb_surj c h
        rcases ha with rfl | ⟨ea, rfl⟩
        · -- a = i
          rcases hc with rfl | ⟨ec, rfl⟩
          · exact absurd rfl hac
          · -- a = i, c = b ec: f(i, b ec) ∈ A(ec)
            cases ec
            · right; left; exact he
            · left; left; exact he
        · -- a = b ea
          rcases hc with rfl | ⟨ec, rfl⟩
          · -- a = b ea, c = i: f(b ea, i) ∈ A(ea)
            cases ea
            · left; right; left; exact he
            · right; right; left; exact he
          · -- a = b ea, c = b ec: f(b ea, b ec) with ea ≠ ec
            have hea_ne : ea ≠ ec := fun h => hac (congrArg b h)
            cases ea <;> cases ec
            · exact absurd rfl hea_ne
            · left; right; right; exact he
            · right; right; right; exact he
            · exact absurd rfl hea_ne
  -- Assemble
  obtain ⟨_, hA₀_seg, hA₀_disj, hA₀_cls, _, _, _, hA₀_char⟩ := key 0
  obtain ⟨R, hR⟩ := segment_end_union_rectagon (hA₀_seg true) (hA₀_seg false) hA₀_disj hA₀_cls
  -- Provide witnesses
  refine ⟨R, fun i => f (i, i), hcls_diag, hdiag_disj, fun i => ?_⟩
  obtain ⟨Aᵢ, hAᵢ_seg, hAᵢ_disj, hAᵢ_cls, hAᵢ_fi, hAᵢ_ficls, hAᵢ_meet, hAᵢ_char⟩ := key i
  -- R.edges = Aᵢ true ∪ Aᵢ false
  have hReq : R.edges = Aᵢ true ∪ Aᵢ false := by
    rw [hR]; ext e; rw [hA₀_char, hAᵢ_char]
  refine ⟨Aᵢ true, Aᵢ false, hReq, ?_, ?_, ?_⟩
  · -- isPsegmentTriple (Aᵢ true) (Aᵢ false) (f(i,i))
    exact isPsegmentTriple_of_segment_end (hAᵢ_seg true) (hAᵢ_seg false) (hseg (i, i))
      hAᵢ_disj (hAᵢ_fi true) (hAᵢ_fi false)
      hAᵢ_cls (hAᵢ_ficls true) (hAᵢ_ficls false)
  · -- Meeting conditions
    intro j; exact ⟨hAᵢ_meet j true, hAᵢ_meet j false⟩
  · -- cls disjointness
    intro j hne
    rw [Set.eq_empty_iff_forall_notMem]
    intro m ⟨⟨hmj, hmt⟩, hmf⟩
    have hm_cls : m ∈ cls (Aᵢ true) ∩ cls (Aᵢ false) := Set.mem_inter hmt hmf
    rw [hAᵢ_cls] at hm_cls
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_cls
    have hmii : m ∈ cls (f (i, i)) := by
      rcases hm_cls with rfl | rfl
      · exact (hep_cls (i, i)).1
      · exact (hep_cls (i, i)).2
    exact absurd (Set.mem_inter hmii hmj) (by rw [hcls_diag i j hne]; exact id)
/-- HOL Light: `rectagon_graph_k33_false` (line 44978).
K₃,₃ is not rectagonal. This is the main result of Section W. -/
theorem rectagon_graph_k33_false : ¬isRectagonalGraph K33 := by
  rw [rectagonal_graph_k33]
  intro ⟨f, uA, uB, hinjA, hinjB, hseg, hfjdisj, hcls⟩
  obtain ⟨R, diag, hhyp⟩ := k33_rectag_to_hyp f uA uB hinjA hinjB hseg hfjdisj hcls
  exact k33_rectagon_hyp_false R diag hhyp
end
end JordanCurveTheorem
