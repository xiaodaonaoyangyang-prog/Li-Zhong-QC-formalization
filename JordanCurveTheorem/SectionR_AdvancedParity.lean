/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionQ_RectagProps

/-!
# Section R: Advanced Parity
## HOL Light: Section R (Lines 34879–37552)

Inductive set restrictions, segment unions, linear and cyclic ordering
of edges in psegments and rectagons, the closure-lattice-point map `cls`,
the adjacency vertex `adjv`, and the main `cut_rectagon` theorem that splits
a rectagon into two psegments.
-/

open Set Metric Topology Function

noncomputable section

/-! ## Raw inductive subset (on Finsets, not requiring Segment structure) -/

/-- An inductive subset of a Finset of edges: a nonempty subset closed
    under adjacency (sharing a closure point) within the edge set.
    This generalizes `Segment.isInductiveSubset` to raw Finsets, which is
    needed for proving segment union theorems.
    HOL Light: `inductive_set G S` (line 4789). -/
def isInductiveSubsetOf (G S : Finset (Set E2)) : Prop :=
  S ⊆ G ∧ S.Nonempty ∧
    ∀ e ∈ S, ∀ e' ∈ G, e ≠ e' →
      (closure e ∩ closure e').Nonempty → e' ∈ S

/-- `Segment.isInductiveSubset` is equivalent to `isInductiveSubsetOf` on edges. -/
theorem Segment.isInductiveSubset_iff_raw (G : Segment) (S : Finset (Set E2)) :
    G.isInductiveSubset S ↔ isInductiveSubsetOf G.edges S := by
  simp only [Segment.isInductiveSubset, isInductiveSubsetOf]

/-! ## Inductive set lemmas -/

/-- Restricting an inductive subset to a sub-segment yields an inductive
    subset of the sub-segment.
    HOL Light: `inductive_set_restrict` (line 34884). -/
theorem inductiveSubsetOf_restrict {G : Finset (Set E2)} {S : Finset (Set E2)}
    (A : Segment) (hGS : isInductiveSubsetOf G S)
    (hI : (S ∩ A.edges).Nonempty) (hA : A.edges ⊆ G) :
    A.isInductiveSubset (S ∩ A.edges) := by
  obtain ⟨hSG, _, hAdj⟩ := hGS
  refine ⟨Finset.inter_subset_right, hI, ?_⟩
  intro e he e' he' hne hinter
  rw [Finset.mem_inter] at he
  have heS := he.1
  have heA := he.2
  have he'G := hA he'
  have he'S := hAdj e heS e' he'G hne hinter
  exact Finset.mem_inter.mpr ⟨he'S, he'⟩

/-- If S is inductive in A ∪ B, both A and B share endpoint m,
    and A ⊆ S, then S meets B.
    HOL Light: `inductive_set_adj` (line 34898). -/
theorem inductiveSubsetOf_adj (A B : Segment)
    (S : Finset (Set E2)) (m : ℤ × ℤ)
    (hS : isInductiveSubsetOf (A.edges ∪ B.edges) S)
    (hBm : B.isEndpoint m) (hAm : A.isEndpoint m)
    (hAS : A.edges ⊆ S) :
    (S ∩ B.edges).Nonempty := by
  obtain ⟨hSG, _, hAdj⟩ := hS
  -- Get the terminal edge of B at m
  obtain ⟨hfB, hfcl⟩ := B.terminalEdge_prop m hBm
  set f := B.terminalEdge m
  -- Get an edge e ∈ A.edges with pointI m ∈ closure e
  have hAm_pos : 0 < numClosure A.edges m := by
    simp only [Segment.isEndpoint] at hAm; omega
  obtain ⟨e, heA, hecl⟩ : ∃ e ∈ A.edges, pointI m ∈ closure e := by
    classical
    simp only [numClosure, incidentEdges] at hAm_pos
    obtain ⟨e, he⟩ := Finset.card_pos.mp hAm_pos
    simp only [Finset.mem_filter] at he
    exact ⟨e, he.1, he.2⟩
  have heS : e ∈ S := hAS heA
  by_cases hfA : f ∈ A.edges
  · -- f ∈ A.edges, so f ∈ S from hAS
    exact ⟨f, Finset.mem_inter.mpr ⟨hAS hfA, hfB⟩⟩
  · -- f ∉ A.edges, so e ≠ f
    have hne : e ≠ f := fun h => hfA (h ▸ heA)
    have hfU : f ∈ A.edges ∪ B.edges :=
      Finset.mem_union.mpr (Or.inr hfB)
    have hinter : (closure e ∩ closure f).Nonempty :=
      ⟨pointI m, hecl, hfcl⟩
    have hfS : f ∈ S := hAdj e heS f hfU hne hinter
    exact ⟨f, Finset.mem_inter.mpr ⟨hfS, hfB⟩⟩

/-- If S is inductive in A ∪ B, S meets A, and A, B share an endpoint,
    then S = A ∪ B.
    HOL Light: `inductive_set_join` (line 34934). -/
theorem inductiveSubsetOf_join (A B : Segment)
    (S : Finset (Set E2))
    (hSA : (S ∩ A.edges).Nonempty)
    (hShared : ∃ m, A.isEndpoint m ∧ B.isEndpoint m)
    (hS : isInductiveSubsetOf (A.edges ∪ B.edges) S) :
    S = A.edges ∪ B.edges := by
  obtain ⟨m, hAm, hBm⟩ := hShared
  -- S ∩ A.edges is an inductive subset of A
  have hRA := inductiveSubsetOf_restrict A hS hSA (Finset.subset_union_left)
  -- By isInductiveSubset_eq, S ∩ A.edges = A.edges
  have hSA_eq := A.isInductiveSubset_eq (S ∩ A.edges) hRA
  -- So A.edges ⊆ S
  have hAS : A.edges ⊆ S := by
    intro e he
    have hmem : e ∈ S ∩ A.edges := by rw [hSA_eq]; exact he
    exact (Finset.mem_inter.mp hmem).1
  -- By inductiveSubsetOf_adj, S ∩ B.edges is nonempty
  have hSB := inductiveSubsetOf_adj A B S m hS hBm hAm hAS
  -- S ∩ B.edges is an inductive subset of B
  have hRB := inductiveSubsetOf_restrict B hS hSB (Finset.subset_union_right)
  -- By isInductiveSubset_eq, S ∩ B.edges = B.edges
  have hSB_eq := B.isInductiveSubset_eq (S ∩ B.edges) hRB
  have hBS : B.edges ⊆ S := by
    intro e he
    have hmem : e ∈ S ∩ B.edges := by rw [hSB_eq]; exact he
    exact (Finset.mem_inter.mp hmem).1
  -- S = A.edges ∪ B.edges
  ext e; constructor
  · exact fun he => hS.1 he
  · intro he; rcases Finset.mem_union.mp he with h | h
    · exact hAS h
    · exact hBS h

/-! ## Segment unions -/

/-- The union of two segments sharing exactly one endpoint is a segment.
    HOL Light: `segment_union` (line 34970). -/
theorem segment_union (A B : Segment) (m : ℤ × ℤ)
    (hAm : A.isEndpoint m) (hBm : B.isEndpoint m)
    (hDisj : Disjoint A.edges B.edges)
    (hShare : ∀ n, 0 < numClosure A.edges n →
      0 < numClosure B.edges n → n = m) :
    ∃ G : Segment, G.edges = A.edges ∪ B.edges := by
  -- numClosure additivity for disjoint union
  have nc_add : ∀ n, numClosure (A.edges ∪ B.edges) n =
      numClosure A.edges n + numClosure B.edges n := by
    intro n; open Classical in
    unfold numClosure incidentEdges; rw [Finset.filter_union]
    exact Finset.card_union_of_disjoint
      (hDisj.mono (Finset.filter_subset _ A.edges) (Finset.filter_subset _ B.edges))
  refine ⟨⟨A.edges ∪ B.edges, ?_, ?_, ?_, ?_⟩, rfl⟩
  -- nonempty
  · exact A.nonempty.mono Finset.subset_union_left
  -- all_edges
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact A.all_edges e h
    · exact B.all_edges e h
  -- degree_bound
  · intro n; rw [nc_add]
    have hA := A.degree_bound n; have hB := B.degree_bound n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
    by_cases hApos : 0 < numClosure A.edges n <;>
      by_cases hBpos : 0 < numClosure B.edges n
    · have := hShare n hApos hBpos; subst this
      simp only [Segment.isEndpoint] at hAm hBm; omega
    · omega
    · omega
    · omega
  -- connected
  · intro S hS hSne hSclosed
    -- Helper: if S meets X, then (↑X.edges : Set _) ⊆ S
    have absorb : ∀ X : Segment, X.edges ⊆ A.edges ∪ B.edges →
        (S ∩ (↑X.edges : Set _)).Nonempty → (↑X.edges : Set _) ⊆ S := by
      intro X hXsub hSX
      have hcl : ∀ C ∈ S ∩ (↑X.edges : Set _), ∀ C' ∈ (↑X.edges : Set _),
          cellAdj C C' → C' ∈ S ∩ (↑X.edges : Set _) := by
        intro C ⟨hCS, hCX⟩ C' hC'X hadj
        exact ⟨hSclosed C hCS C'
          (Finset.mem_coe.mpr (hXsub (Finset.mem_coe.mp hC'X))) hadj, hC'X⟩
      have heq := X.connected (S ∩ (↑X.edges : Set _)) Set.inter_subset_right hSX hcl
      intro x hx
      have : x ∈ S ∩ (↑X.edges : Set _) := by rw [heq]; exact hx
      exact this.1
    -- Helper: if X.edges ⊆ S, X,Y share endpoint m, X ∩ Y = ∅, then S meets Y
    have bridge : ∀ (X Y : Segment),
        Y.edges ⊆ A.edges ∪ B.edges →
        X.isEndpoint m → Y.isEndpoint m → Disjoint X.edges Y.edges →
        (↑X.edges : Set _) ⊆ S → (S ∩ (↑Y.edges : Set _)).Nonempty := by
      intro X Y hYsub hXm hYm hXYdisj hXS
      obtain ⟨heX, hclX⟩ := X.terminalEdge_prop m hXm
      obtain ⟨heY, hclY⟩ := Y.terminalEdge_prop m hYm
      have hne : X.terminalEdge m ≠ Y.terminalEdge m := by
        intro h
        have hmem : X.terminalEdge m ∈ X.edges ∩ Y.edges :=
          Finset.mem_inter.mpr ⟨heX, h ▸ heY⟩
        exact absurd hmem (Finset.disjoint_iff_inter_eq_empty.mp hXYdisj ▸
          Finset.notMem_empty _)
      have hadj : cellAdj (X.terminalEdge m) (Y.terminalEdge m) :=
        ⟨isEdge_isCell (X.all_edges _ heX), isEdge_isCell (Y.all_edges _ heY),
         hne, ⟨pointI m, hclX, hclY⟩⟩
      exact ⟨Y.terminalEdge m,
        hSclosed _ (hXS (Finset.mem_coe.mpr heX)) _
          (Finset.mem_coe.mpr (hYsub heY)) hadj,
        Finset.mem_coe.mpr heY⟩
    -- Main: case split on where the first element of S lives
    obtain ⟨e₀, he₀S⟩ := hSne
    have he₀U := hS he₀S
    simp only [Finset.coe_union, Set.mem_union] at he₀U
    suffices hABS : (↑A.edges : Set _) ⊆ S ∧ (↑B.edges : Set _) ⊆ S by
      apply Set.Subset.antisymm hS
      intro x hx
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hABS.1 (Finset.mem_coe.mpr h)
      · exact hABS.2 (Finset.mem_coe.mpr h)
    rcases he₀U with he₀A | he₀B
    · have hAS := absorb A Finset.subset_union_left ⟨e₀, he₀S, he₀A⟩
      have hBS := absorb B Finset.subset_union_right
        (bridge A B Finset.subset_union_right hAm hBm hDisj hAS)
      exact ⟨hAS, hBS⟩
    · have hBS := absorb B Finset.subset_union_right ⟨e₀, he₀S, he₀B⟩
      have hAS := absorb A Finset.subset_union_left
        (bridge B A Finset.subset_union_left hBm hAm hDisj.symm hBS)
      exact ⟨hAS, hBS⟩

/-- In a segment, any endpoint belongs to {m, p} when m ≠ p are both endpoints.
    HOL Light: `two_endpoint_segment` (line 35057). -/
theorem Segment.two_endpoint_bound (G : Segment)
    (p m : ℤ × ℤ) (hp : G.isEndpoint p) (hm : G.isEndpoint m) (hmp : m ≠ p)
    (q : ℤ × ℤ) (hq : G.isEndpoint q) :
    q = m ∨ q = p := by
  rcases G.endpoint_count with h | ⟨a, b, hab, ha, hb, huniq⟩
  · exact absurd hm (h m)
  · have hqa := huniq q hq
    rcases huniq m hm with rfl | rfl
    · rcases huniq p hp with rfl | rfl
      · exact absurd rfl hmp
      · exact hqa
    · rcases huniq p hp with rfl | rfl
      · rcases hqa with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      · exact absurd rfl hmp

/-- Propositional extensionality: (A → B) ∧ (B → A) → (A = B).
    HOL Light: `EQ_ANTISYM` (line 35070).
    In Lean 4 this is `propext (Iff.intro h1 h2)`. -/
theorem eq_antisym_prop (A B : Prop) (h1 : A → B) (h2 : B → A) : A = B :=
  propext ⟨h1, h2⟩

/-- The union of two segments sharing exactly two endpoints (and satisfying a
    parity condition) is a rectagon.
    HOL Light: `segment_union2` (line 35078). -/
theorem segment_union_rectagon (A B : Segment) (m p : ℤ × ℤ)
    (hmp : m ≠ p)
    (hAm : A.isEndpoint m) (hBm : B.isEndpoint m)
    (hAp : A.isEndpoint p) (hBp : B.isEndpoint p)
    (hDisj : Disjoint A.edges B.edges)
    (hShare : ∀ n, (0 < numClosure A.edges n ∧ 0 < numClosure B.edges n) ↔
      (n = m ∨ n = p)) :
    ∃ G : Rectagon, G.edges = A.edges ∪ B.edges := by
  -- numClosure additivity for disjoint union
  have nc_add : ∀ n, numClosure (A.edges ∪ B.edges) n =
      numClosure A.edges n + numClosure B.edges n := by
    intro n; open Classical in
    unfold numClosure incidentEdges; rw [Finset.filter_union]
    exact Finset.card_union_of_disjoint
      (hDisj.mono (Finset.filter_subset _ A.edges) (Finset.filter_subset _ B.edges))
  -- Any endpoint of A or B is m or p
  have hA_ep : ∀ q, A.isEndpoint q → q = m ∨ q = p :=
    fun q hq => A.two_endpoint_bound p m hAp hAm hmp q hq
  have hB_ep : ∀ q, B.isEndpoint q → q = m ∨ q = p :=
    fun q hq => B.two_endpoint_bound p m hBp hBm hmp q hq
  -- Endpoint iff: numClosure A n = 1 ↔ numClosure B n = 1
  have ep_iff : ∀ n, numClosure A.edges n = 1 ↔ numClosure B.edges n = 1 := by
    intro n; constructor
    · intro h; rcases hA_ep n h with rfl | rfl <;> assumption
    · intro h; rcases hB_ep n h with rfl | rfl <;> assumption
  refine ⟨⟨A.edges ∪ B.edges, ?_, ?_, ?_, ?_⟩, rfl⟩
  -- nonempty
  · exact A.nonempty.mono Finset.subset_union_left
  -- all_edges
  · intro e he; rcases Finset.mem_union.mp he with h | h
    · exact A.all_edges e h
    · exact B.all_edges e h
  -- even_degree: numClosure(A ∪ B, n) ∈ {0, 2}
  · intro n; rw [nc_add]
    have hA := A.degree_bound n; have hB := B.degree_bound n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
    by_cases hA0 : numClosure A.edges n = 0
    · have : numClosure B.edges n ≠ 1 := fun h => by
        have := (ep_iff n).mpr h; omega
      omega
    · by_cases hA1 : numClosure A.edges n = 1
      · have := (ep_iff n).mp hA1; omega
      · have : numClosure B.edges n ≠ 1 := fun h => by
          have := (ep_iff n).mpr h; omega
        have : numClosure B.edges n ≠ 2 := by
          intro h
          have : 0 < numClosure A.edges n ∧ 0 < numClosure B.edges n := by omega
          rcases (hShare n).mp this with rfl | rfl
          · simp only [Segment.isEndpoint] at hAm; omega
          · simp only [Segment.isEndpoint] at hAp; omega
        omega
  -- connected
  · intro S hS hSne hSclosed
    have absorb : ∀ X : Segment, X.edges ⊆ A.edges ∪ B.edges →
        (S ∩ (↑X.edges : Set _)).Nonempty → (↑X.edges : Set _) ⊆ S := by
      intro X hXsub hSX
      have hcl : ∀ C ∈ S ∩ (↑X.edges : Set _), ∀ C' ∈ (↑X.edges : Set _),
          cellAdj C C' → C' ∈ S ∩ (↑X.edges : Set _) := by
        intro C ⟨hCS, hCX⟩ C' hC'X hadj
        exact ⟨hSclosed C hCS C'
          (Finset.mem_coe.mpr (hXsub (Finset.mem_coe.mp hC'X))) hadj, hC'X⟩
      have heq := X.connected (S ∩ (↑X.edges : Set _)) Set.inter_subset_right hSX hcl
      intro x hx
      have hmem : x ∈ S ∩ (↑X.edges : Set _) := by rw [heq]; exact hx
      exact hmem.1
    have bridge : ∀ (X Y : Segment),
        Y.edges ⊆ A.edges ∪ B.edges →
        X.isEndpoint m → Y.isEndpoint m → Disjoint X.edges Y.edges →
        (↑X.edges : Set _) ⊆ S → (S ∩ (↑Y.edges : Set _)).Nonempty := by
      intro X Y hYsub hXm hYm hXYdisj hXS
      obtain ⟨heX, hclX⟩ := X.terminalEdge_prop m hXm
      obtain ⟨heY, hclY⟩ := Y.terminalEdge_prop m hYm
      have hne : X.terminalEdge m ≠ Y.terminalEdge m := by
        intro h
        have hmem : X.terminalEdge m ∈ X.edges ∩ Y.edges :=
          Finset.mem_inter.mpr ⟨heX, h ▸ heY⟩
        exact absurd hmem (Finset.disjoint_iff_inter_eq_empty.mp hXYdisj ▸
          Finset.notMem_empty _)
      have hadj : cellAdj (X.terminalEdge m) (Y.terminalEdge m) :=
        ⟨isEdge_isCell (X.all_edges _ heX), isEdge_isCell (Y.all_edges _ heY),
         hne, ⟨pointI m, hclX, hclY⟩⟩
      exact ⟨Y.terminalEdge m,
        hSclosed _ (hXS (Finset.mem_coe.mpr heX)) _
          (Finset.mem_coe.mpr (hYsub heY)) hadj,
        Finset.mem_coe.mpr heY⟩
    obtain ⟨e₀, he₀S⟩ := hSne
    have he₀U := hS he₀S
    simp only [Finset.coe_union, Set.mem_union] at he₀U
    suffices hABS : (↑A.edges : Set _) ⊆ S ∧ (↑B.edges : Set _) ⊆ S by
      apply Set.Subset.antisymm hS
      intro x hx
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hABS.1 (Finset.mem_coe.mpr h)
      · exact hABS.2 (Finset.mem_coe.mpr h)
    rcases he₀U with he₀A | he₀B
    · have hAS := absorb A Finset.subset_union_left ⟨e₀, he₀S, he₀A⟩
      have hBS := absorb B Finset.subset_union_right
        (bridge A B Finset.subset_union_right hAm hBm hDisj hAS)
      exact ⟨hAS, hBS⟩
    · have hBS := absorb B Finset.subset_union_right ⟨e₀, he₀S, he₀B⟩
      have hAS := absorb A Finset.subset_union_left
        (bridge B A Finset.subset_union_left hBm hAm hDisj.symm hBS)
      exact ⟨hAS, hBS⟩

/-! ## Cardinality / injection / bijection lemmas -/

/-- An injection from a finite set to another implies Card A ≤ Card B.
    HOL Light: `card_inj` (line 35218).
    Lean/Mathlib: `Finset.card_le_card_of_injOn`. -/
theorem card_le_of_injOn' {α β : Type*} (f : α → β) (A : Finset α)
    (B : Finset β)
    (hInj : ∀ a ∈ A, f a ∈ B)
    (hInjective : ∀ a₁ ∈ A, ∀ a₂ ∈ A, f a₁ = f a₂ → a₁ = a₂) :
    A.card ≤ B.card := by
  classical
  have hinj : Set.InjOn f (↑A : Set _) := fun a ha b hb => hInjective a ha b hb
  have himg : A.image f ⊆ B := by
    intro x hx; simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx; exact hInj a ha
  calc A.card = (A.image f).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ B.card := Finset.card_le_card himg

/-- An injection into a set of the same cardinality is a bijection.
    HOL Light: `inj_bij_size` (line 35234). -/
theorem inj_bij_of_card_eq {α β : Type*}
    (f : α → β) (A : Finset α) (B : Finset β)
    (hCard : B.card = A.card)
    (hInj : ∀ a ∈ A, f a ∈ B)
    (hInjective : ∀ a₁ ∈ A, ∀ a₂ ∈ A, f a₁ = f a₂ → a₁ = a₂) :
    ∀ b ∈ B, ∃ a ∈ A, f a = b := by
  classical
  have himg_sub : A.image f ⊆ B := by
    intro x hx; simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx; exact hInj a ha
  have himg : A.image f = B :=
    Finset.eq_of_subset_of_card_le himg_sub (by
      rw [hCard, Finset.card_image_of_injOn
        (fun a ha b hb => hInjective a ha b hb)])
  intro b hb; rw [← himg] at hb
  simp only [Finset.mem_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb; exact ⟨a, ha, rfl⟩

/-- The empty function bijects ∅ to ∅.
    HOL Light: `bij_empty` (line 35254). -/
theorem bij_empty' {α β : Type*} (f : α → β) :
    Set.BijOn f ∅ ∅ :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

/-- A bijection on singletons iff f a = b.
    HOL Light: `bij_sing` (line 35260). -/
theorem bij_singleton {α β : Type*}
    (f : α → β) (a : α) (b : β) :
    (∀ x ∈ ({a} : Finset α), f x ∈ ({b} : Finset β)) ∧
    (∀ x₁ ∈ ({a} : Finset α), ∀ x₂ ∈ ({a} : Finset α),
      f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ y ∈ ({b} : Finset β), ∃ x ∈ ({a} : Finset α), f x = y) ↔
    f a = b := by
  classical
  constructor
  · rintro ⟨h1, _, _⟩; simpa using h1 a (Finset.mem_singleton.mpr rfl)
  · intro h
    exact ⟨fun x hx => by
        simp only [Finset.mem_singleton] at hx; subst hx
        simp only [h, Finset.mem_singleton],
      fun x₁ h1 x₂ h2 _ => by
        simp only [Finset.mem_singleton] at h1 h2; rw [h1, h2],
      fun y hy => by
        simp only [Finset.mem_singleton] at hy
        exact ⟨a, Finset.mem_singleton.mpr rfl, by rw [hy]; exact h⟩⟩

/-- Card of a singleton is 1.
    HOL Light: `card_sing` (line 35271).
    Lean/Mathlib: `Finset.card_singleton`. -/
theorem card_singleton' {α : Type*} (a : α) :
    ({a} : Finset α).card = 1 :=
  Finset.card_singleton a

/-- {a, a} = {a}.
    HOL Light: `pair_indistinct` (line 35280).
    Lean/Mathlib: `Finset.pair_eq_singleton_iff`. -/
theorem pair_self_eq {α : Type*} [DecidableEq α] (a : α) :
    ({a, a} : Finset α) = {a} := by
  simp

/-- {a, b} has card 2 implies a ≠ b.
    HOL Light: `has_size2_distinct` (line 35287). -/
theorem pair_card_two_ne {α : Type*} [DecidableEq α] (a b : α)
    (h : ({a, b} : Finset α).card = 2) : a ≠ b := by
  intro hab; subst hab; simp at h

/-- A 2-element subset of {a, b} equals {a, b}.
    HOL Light: `has_size2_subset` (line 35296). -/
theorem subset_pair_of_card_two {α : Type*} [DecidableEq α]
    (X : Finset α) (a b : α) (hcard : X.card = 2)
    (hSub : X ⊆ {a, b}) : X = {a, b} := by
  apply Finset.eq_of_subset_of_card_le hSub
  have := Finset.card_insert_le a ({b} : Finset α)
  rw [Finset.card_singleton] at this; omega

/-- Enlarging the codomain preserves injectivity.
    HOL Light: `inj_subset2` (line 35310). -/
theorem injOn_subset_range {α β : Type*} (f : α → β)
    (s : Set α) (t t' : Set β) (h : Set.InjOn f s)
    (_ht : t ⊆ t') : Set.InjOn f s := h

/-! ## Terminal adjacency -/

/-- In a non-singleton segment, the terminal edge at an endpoint has a
    unique adjacent edge.
    HOL Light: `terminal_adj` (line 35318). -/
theorem Segment.terminal_adj (G : Segment) (b : ℤ × ℤ) (hb : G.isEndpoint b)
    (hns : G.edges.card ≠ 1) :
    ∃! e, e ∈ G.edges ∧ e ≠ G.terminalEdge b ∧
      (closure (G.terminalEdge b) ∩ closure e).Nonempty := by
  classical
  set t := G.terminalEdge b
  obtain ⟨htG, htcl_b⟩ := G.terminalEdge_prop b hb
  have ht_edge := G.all_edges t htG
  obtain ⟨c₁, c₂, hne_c, hc₁, hc₂, hlp⟩ := edge_two_endpoints t ht_edge
  have at_ep : ∀ m, G.isEndpoint m → pointI m ∈ closure t →
      ∀ e' ∈ G.edges, pointI m ∈ closure e' → e' = t :=
    fun m hm hcl e' he' hcl' =>
      (G.terminalEdge_unique m hm e' he' hcl').trans
        (G.terminalEdge_unique m hm t htG hcl).symm
  have not_both_ep : ¬ (G.isEndpoint c₁ ∧ G.isEndpoint c₂) := by
    rintro ⟨h1, h2⟩
    have : G.isInductiveSubset {t} :=
      ⟨Finset.singleton_subset_iff.mpr htG, ⟨t, Finset.mem_singleton_self t⟩, by
        intro e he e' he' hne hinter
        rw [Finset.mem_singleton.mp he] at hinter hne
        obtain ⟨z, hzt, hze'⟩ := hinter
        obtain ⟨k, hk⟩ := edges_share_lattice_point t e' ht_edge
          (G.all_edges e' he') hne z ⟨hzt, hze'⟩
        rw [hk] at hze'
        rcases hlp k (hk ▸ hzt) with heq | heq
        · rw [heq] at hze'
          exact absurd (at_ep c₁ h1 hc₁ e' he' hze') hne.symm
        · rw [heq] at hze'
          exact absurd (at_ep c₂ h2 hc₂ e' he' hze') hne.symm⟩
    rw [(G.isInductiveSubset_eq {t} this).symm, Finset.card_singleton] at hns
    exact hns rfl
  suffices ∀ q, pointI q ∈ closure t → q ≠ b →
      (∀ m, pointI m ∈ closure t → m = b ∨ m = q) →
      ¬ G.isEndpoint q →
      ∃! e, e ∈ G.edges ∧ e ≠ t ∧ (closure t ∩ closure e).Nonempty by
    rcases hlp b htcl_b with hbc | hbc
    · exact this c₂ hc₂ (fun h => hne_c (hbc.symm.trans h.symm))
        (fun m hm => by rcases hlp m hm with h | h
                        · exact Or.inl (h.trans hbc.symm)
                        · exact Or.inr h)
        (fun h => not_both_ep ⟨hbc ▸ hb, h⟩)
    · exact this c₁ hc₁ (fun h => hne_c (h.trans hbc))
        (fun m hm => by rcases hlp m hm with h | h
                        · exact Or.inr h
                        · exact Or.inl (h.trans hbc.symm))
        (fun h => not_both_ep ⟨h, hbc ▸ hb⟩)
  intro q hq_cl hq_ne hlp' hq_ne_ep
  have hq_nc2 : numClosure G.edges q = 2 := by
    have hd := G.degree_bound q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    have : 0 < numClosure G.edges q :=
      Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨htG, hq_cl⟩⟩
    simp only [Segment.isEndpoint] at hq_ne_ep; omega
  obtain ⟨f₁, f₂, hne_f, hf₁G, hf₂G, hf₁cl, hf₂cl, huniq⟩ :=
    (numClosure_eq_two_iff G.edges q).mp hq_nc2
  have shared_q : ∀ e' ∈ G.edges, e' ≠ t →
      (closure t ∩ closure e').Nonempty → pointI q ∈ closure e' := by
    intro e' he' hne hinter
    obtain ⟨z, hzt, hze'⟩ := hinter
    obtain ⟨k, hk⟩ := edges_share_lattice_point t e' ht_edge
      (G.all_edges e' he') (Ne.symm hne) z ⟨hzt, hze'⟩
    rw [hk] at hze'
    rcases hlp' k (hk ▸ hzt) with heq | heq
    · rw [heq] at hze'
      exact absurd (at_ep b hb htcl_b e' he' hze') hne
    · rw [heq] at hze'; exact hze'
  rcases huniq t htG hq_cl with ht1 | ht2
  · exact ⟨f₂, ⟨hf₂G, fun h => hne_f.symm (h.trans ht1),
      ⟨pointI q, hq_cl, hf₂cl⟩⟩, fun e' ⟨he', hne_t, hint⟩ =>
        (huniq e' he' (shared_q e' he' hne_t hint)).elim
          (fun h => absurd (ht1 ▸ h) hne_t) id⟩
  · exact ⟨f₁, ⟨hf₁G, fun h => hne_f (h.trans ht2),
      ⟨pointI q, hq_cl, hf₁cl⟩⟩, fun e' ⟨he', hne_t, hint⟩ =>
        (huniq e' he' (shared_q e' he' hne_t hint)).elim
          id (fun h => absurd (ht2 ▸ h) hne_t)⟩

/-! ## Linear ordering of psegment edges -/

/-- Inductive lemma: the edges of a psegment can be linearly ordered so
    consecutive elements are adjacent.
    HOL Light: `psegment_order_induct_lemma` (line 35471). -/
theorem psegment_order_induct_lemma (n : ℕ) :
    ∀ (G : Segment), G.isPsegment → G.edges.card = n →
      ∀ (a b : ℤ × ℤ), G.isEndpoint a → G.isEndpoint b → a ≠ b →
        ∃ f : ℕ → Set E2,
          (∀ i, i < n → f i ∈ G.edges) ∧
          (∀ i j, i < n → j < n → f i = f j → i = j) ∧
          (∀ e ∈ G.edges, ∃ i, i < n ∧ f i = e) ∧
          f 0 = G.terminalEdge a ∧
          (0 < n → f (n - 1) = G.terminalEdge b) ∧
          (∀ i j, i < n → j < n →
            (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) := by
  classical
  induction n with
  | zero =>
    intro G _ hcard a _ ha _ _
    exfalso
    rw [Segment.isEndpoint] at ha
    simp only [numClosure, incidentEdges] at ha
    have h2 := Finset.card_le_card
      (Finset.filter_subset (fun e => pointI a ∈ closure e) G.edges)
    rw [hcard] at h2; omega
  | succ n ih =>
    intro G hps hcard a b ha hb hab
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- n = 0, card G.edges = 1 (single edge)
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
      have he_mem : e ∈ G.edges := by rw [he]; exact Finset.mem_singleton_self e
      have ha_cl : pointI a ∈ closure e := by
        obtain ⟨e', ⟨he', hcl⟩, _⟩ := (numClosure_eq_one_iff G.edges a).mp ha
        rw [he, Finset.mem_singleton] at he'; exact he' ▸ hcl
      have hb_cl : pointI b ∈ closure e := by
        obtain ⟨e', ⟨he', hcl⟩, _⟩ := (numClosure_eq_one_iff G.edges b).mp hb
        rw [he, Finset.mem_singleton] at he'; exact he' ▸ hcl
      have hmem : ∀ e' ∈ G.edges, e' = e := by
        intro e' he'; rw [he] at he'; exact Finset.mem_singleton.mp he'
      refine ⟨fun _ => e, fun _ _ => he_mem, fun i j hi hj _ => by omega,
        fun e' he' => ⟨0, Nat.zero_lt_one, (hmem e' he').symm⟩, ?_, ?_,
        fun i j hi hj => ⟨fun ⟨_, _, h, _⟩ => absurd rfl h,
          fun h => by exfalso; rcases h with h | h <;> omega⟩⟩
      · change e = G.terminalEdge a
        exact G.terminalEdge_unique a ha e he_mem ha_cl
      · intro _; change e = G.terminalEdge b
        exact G.terminalEdge_unique b hb e he_mem hb_cl
    · -- n ≥ 1, card G.edges = n + 1 ≥ 2. Inductive step.
      set t := G.terminalEdge b with ht_def
      -- Derive that every endpoint is a or b
      have huniq : ∀ m, G.isEndpoint m → m = a ∨ m = b := by
        obtain ⟨a', b', _, _, _, h⟩ := hps
        intro m hm
        rcases h a ha with rfl | rfl <;> rcases h b hb with rfl | rfl
        · exact absurd rfl hab
        · exact h m hm
        · exact Or.comm.mp (h m hm)
        · exact absurd rfl hab
      obtain ⟨htG, hbcl⟩ := G.terminalEdge_prop b hb
      have ht_edge := G.all_edges t htG
      obtain ⟨c₁, c₂, hne_c, hc₁, hc₂, hcl_all⟩ := edge_two_endpoints t ht_edge
      -- Identify the other lattice point b' on edge t
      obtain ⟨b', hb'ne, hb'cl, hcl_all'⟩ :
          ∃ b', b' ≠ b ∧ pointI b' ∈ closure t ∧
            (∀ m, pointI m ∈ closure t → m = b ∨ m = b') := by
        rcases hcl_all b hbcl with rfl | rfl
        · exact ⟨c₂, hne_c.symm, hc₂, hcl_all⟩
        · exact ⟨c₁, hne_c, hc₁, fun m hm => (hcl_all m hm).symm⟩
      -- Key: a is NOT on edge t
      have ha_off_t : pointI a ∉ closure t := by
        intro hcl
        rcases hcl_all' a hcl with rfl | rfl
        · exact hab rfl
        · -- a = b': both a,b on t, both have numClosure = 1
          have he_a : ∀ e ∈ G.edges, pointI a ∈ closure e → e = t :=
            fun e he hcle => (G.terminalEdge_unique a ha e he hcle).trans
              (G.terminalEdge_unique a ha t htG hcl).symm
          have he_b : ∀ e ∈ G.edges, pointI b ∈ closure e → e = t :=
            fun e he hcle => (G.terminalEdge_unique b hb e he hcle).trans
              (G.terminalEdge_unique b hb t htG hbcl).symm
          have hS : ({t} : Set _) = (↑G.edges : Set _) := by
            apply G.connected
            · intro x hx; exact Finset.mem_coe.mpr
                ((Set.mem_singleton_iff.mp hx) ▸ htG)
            · exact ⟨t, Set.mem_singleton t⟩
            · intro C hC C' hC' hadj
              rw [Set.mem_singleton_iff.mp hC] at hadj
              obtain ⟨_, _, hne, ⟨z, hz1, hz2⟩⟩ := hadj
              obtain ⟨m, hm⟩ := edges_share_lattice_point t C' ht_edge
                (G.all_edges C' (Finset.mem_coe.mp hC')) hne z ⟨hz1, hz2⟩
              rw [hm] at hz2
              rcases hcl_all' m (hm ▸ hz1) with rfl | rfl
              · exact absurd (he_b C' (Finset.mem_coe.mp hC') hz2)
                  (Ne.symm hne)
              · exact absurd (he_a C' (Finset.mem_coe.mp hC') hz2)
                  (Ne.symm hne)
          have hsing : G.edges = {t} := by
            ext x; simp only [Finset.mem_singleton]
            exact ⟨fun hx => Set.mem_singleton_iff.mp (hS ▸ Finset.mem_coe.mpr hx),
              fun hx => hx ▸ htG⟩
          rw [hsing, Finset.card_singleton] at hcard; omega
      -- b' ≠ a
      have hab' : b' ≠ a := by intro h; subst h; exact ha_off_t hb'cl
      -- b' is a midpoint of G (numClosure = 2)
      have hb'mid : G.isMidpoint b' := by
        rw [Segment.isMidpoint]
        have hd := G.degree_bound b'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        have hge1 : 0 < numClosure G.edges b' :=
          Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨htG, hb'cl⟩⟩
        have : ¬G.isEndpoint b' := by
          intro hep; rcases huniq b' hep with rfl | rfl
          · exact ha_off_t hb'cl
          · exact hb'ne rfl
        rw [Segment.isEndpoint] at this; omega
      -- Delete terminal edge at b to get segment G'
      have hne_sing : G.edges ≠ {t} := by
        intro h; rw [h, Finset.card_singleton] at hcard; omega
      obtain ⟨G', hG'eq⟩ := Segment.segment_delete G t b htG hb hbcl hne_sing
      -- Card of G'
      have hG'card : G'.edges.card = n := by
        rw [hG'eq, Finset.card_erase_of_mem htG]; omega
      -- numClosure changes
      have nc_erase_on : ∀ m, pointI m ∈ closure t →
          numClosure (G.edges.erase t) m = numClosure G.edges m - 1 := by
        intro m hm; simp only [numClosure, incidentEdges]
        rw [show Finset.filter (fun e => pointI m ∈ closure e) (G.edges.erase t) =
            (Finset.filter (fun e => pointI m ∈ closure e) G.edges).erase t from by
          ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto]
        exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨htG, hm⟩)
      have nc_erase_off : ∀ m, pointI m ∉ closure t →
          numClosure (G.edges.erase t) m = numClosure G.edges m := by
        intro m hm; simp only [numClosure, incidentEdges]; congr 1
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨⟨_, hx⟩, hcl⟩ => ⟨hx, hcl⟩,
          fun ⟨hx, hcl⟩ => ⟨⟨fun h => hm (h ▸ hcl), hx⟩, hcl⟩⟩
      -- G' endpoints
      have hG'a : G'.isEndpoint a := by
        rw [Segment.isEndpoint, hG'eq, nc_erase_off a ha_off_t]; exact ha
      have hG'b' : G'.isEndpoint b' := by
        rw [Segment.isEndpoint, hG'eq, nc_erase_on b' hb'cl]
        show numClosure G.edges b' - 1 = 1; rw [hb'mid]
      -- G' is a psegment
      have hG'ps : G'.isPsegment := by
        refine ⟨a, b', hab'.symm, hG'a, hG'b', fun m hm => ?_⟩
        rw [Segment.isEndpoint, hG'eq] at hm
        by_cases hm_on : pointI m ∈ closure t
        · rw [nc_erase_on m hm_on] at hm
          rcases hcl_all' m hm_on with rfl | rfl
          · simp only [Segment.isEndpoint] at hb; omega
          · exact Or.inr rfl
        · rw [nc_erase_off m hm_on] at hm
          rcases huniq m (show G.isEndpoint m from hm) with rfl | rfl
          · exact Or.inl rfl
          · exact absurd hbcl hm_on
      -- Apply IH to G'
      obtain ⟨f, hfmem, hfinj, hfsurj, hf0, hflast, hfadj⟩ :=
        ih G' hG'ps hG'card a b' hG'a hG'b' hab'.symm
      -- Define g(i) = if i < n then f(i) else t
      set g := fun i => if i < n then f i else t with hg_def
      have hg_lt : ∀ i, i < n → g i = f i := fun i hi => by simp [hg_def, hi]
      have hg_n : g n = t := by simp [hg_def]
      -- Helper: b has numClosure 0 in G'
      have hncb0 : numClosure (G.edges.erase t) b = 0 := by
        rw [nc_erase_on b hbcl]; simp only [Segment.isEndpoint] at hb; omega
      -- Helper: f i ∈ G.edges.erase t
      have hfi_erase : ∀ i, i < n → f i ∈ G.edges.erase t :=
        fun i hi => hG'eq ▸ hfmem i hi
      refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- g i ∈ G.edges for i < n + 1
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hg_lt i hi']; exact Finset.mem_of_mem_erase (hfi_erase i hi')
        · rw [hg_n]; exact htG
      · -- injectivity
        intro i j hi hj heq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · rw [hg_lt i hi', hg_lt j hj'] at heq
            exact hfinj i j hi' hj' heq
          · rw [hg_lt i hi', hg_n] at heq
            exact absurd heq (Finset.ne_of_mem_erase (hfi_erase i hi'))
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · rw [hg_n, hg_lt j hj'] at heq
            exact absurd heq.symm (Finset.ne_of_mem_erase (hfi_erase j hj'))
          · rfl
      · -- surjectivity
        intro e' he'
        by_cases he'_t : e' = t
        · exact ⟨n, Nat.lt_succ_iff.mpr le_rfl, he'_t ▸ hg_n⟩
        · have he'G' : e' ∈ G'.edges :=
            hG'eq ▸ Finset.mem_erase.mpr ⟨he'_t, he'⟩
          obtain ⟨i, hi, hfi⟩ := hfsurj e' he'G'
          exact ⟨i, Nat.lt_succ_of_lt hi, (hg_lt i hi).symm ▸ hfi⟩
      · -- g 0 = G.terminalEdge a
        rw [hg_lt 0 hn_pos, hf0]
        obtain ⟨hta_mem, hta_cl⟩ := G'.terminalEdge_prop a hG'a
        have h1 : G'.terminalEdge a ∈ G.edges :=
          Finset.mem_of_mem_erase (hG'eq ▸ hta_mem)
        exact G.terminalEdge_unique a ha (G'.terminalEdge a) h1 hta_cl
      · -- g n = G.terminalEdge b
        intro _
        rw [show n + 1 - 1 = n from Nat.succ_sub_one n, hg_n]
      · -- adjacency
        intro i₁ j₁ hi₁ hj₁
        -- Use by_cases to avoid rfl-substitution of n
        by_cases hi_lt : i₁ < n
        · by_cases hj_lt : j₁ < n
          · -- Both i₁, j₁ < n: use IH
            rw [hg_lt i₁ hi_lt, hg_lt j₁ hj_lt]; exact hfadj i₁ j₁ hi_lt hj_lt
          · -- i₁ < n, j₁ = n
            have hj_eq : j₁ = n := by omega
            rw [hg_lt i₁ hi_lt, hj_eq, hg_n]
            constructor
            · intro hadj; left
              obtain ⟨_, _, hne_fi_t, ⟨z, hz1, hz2⟩⟩ := hadj
              obtain ⟨m, hm⟩ := edges_share_lattice_point (f i₁) t
                (G.all_edges (f i₁)
                  (Finset.mem_of_mem_erase (hfi_erase i₁ hi_lt)))
                ht_edge hne_fi_t z ⟨hz1, hz2⟩
              rw [hm] at hz1 hz2
              rcases hcl_all' m hz2 with heq_m | heq_m
              · exfalso
                rw [← heq_m] at hncb0
                simp only [numClosure, incidentEdges] at hncb0
                have hmem : f i₁ ∈ Finset.filter
                    (fun e => pointI m ∈ closure e) (G.edges.erase t) :=
                  Finset.mem_filter.mpr ⟨hfi_erase i₁ hi_lt, hz1⟩
                rw [Finset.card_eq_zero.mp hncb0] at hmem
                exact Finset.notMem_empty _ hmem
              · have hfi_tb' :=
                  G'.terminalEdge_unique b' hG'b' (f i₁) (hfmem i₁ hi_lt) (heq_m ▸ hz1)
                have hfn_tb' := hflast hn_pos
                have := hfinj i₁ (n - 1) hi_lt (by omega)
                  (hfi_tb'.trans hfn_tb'.symm)
                omega
            · intro h
              rcases h with h | h
              · have hi_eq : i₁ = n - 1 := by omega
                rw [hi_eq, hflast hn_pos]
                obtain ⟨htb', htb'_cl⟩ := G'.terminalEdge_prop b' hG'b'
                exact ⟨isEdge_isCell (G.all_edges _
                    (Finset.mem_of_mem_erase (hG'eq ▸ htb'))),
                  isEdge_isCell ht_edge,
                  Finset.ne_of_mem_erase (hG'eq ▸ htb'),
                  ⟨pointI b', htb'_cl, hb'cl⟩⟩
              · omega
        · by_cases hj_lt : j₁ < n
          · -- i₁ = n, j₁ < n: symmetric
            have hi_eq : i₁ = n := by omega
            rw [hi_eq, hg_n, hg_lt j₁ hj_lt, cellAdj_symm]
            constructor
            · intro hadj; right
              obtain ⟨_, _, hne_fj_t, ⟨z, hz1, hz2⟩⟩ := hadj
              obtain ⟨m, hm⟩ := edges_share_lattice_point (f j₁) t
                (G.all_edges (f j₁)
                  (Finset.mem_of_mem_erase (hfi_erase j₁ hj_lt)))
                ht_edge hne_fj_t z ⟨hz1, hz2⟩
              rw [hm] at hz1 hz2
              rcases hcl_all' m hz2 with heq_m | heq_m
              · exfalso
                rw [← heq_m] at hncb0
                simp only [numClosure, incidentEdges] at hncb0
                have hmem : f j₁ ∈ Finset.filter
                    (fun e => pointI m ∈ closure e) (G.edges.erase t) :=
                  Finset.mem_filter.mpr ⟨hfi_erase j₁ hj_lt, hz1⟩
                rw [Finset.card_eq_zero.mp hncb0] at hmem
                exact Finset.notMem_empty _ hmem
              · have hfj_tb' :=
                  G'.terminalEdge_unique b' hG'b' (f j₁) (hfmem j₁ hj_lt) (heq_m ▸ hz1)
                have hfn_tb' := hflast hn_pos
                have := hfinj j₁ (n - 1) hj_lt (by omega)
                  (hfj_tb'.trans hfn_tb'.symm)
                omega
            · intro h
              rcases h with h | h
              · omega
              · have hj_eq : j₁ = n - 1 := by omega
                rw [hj_eq, hflast hn_pos]
                obtain ⟨htb', htb'_cl⟩ := G'.terminalEdge_prop b' hG'b'
                exact ⟨isEdge_isCell (G.all_edges _
                    (Finset.mem_of_mem_erase (hG'eq ▸ htb'))),
                  isEdge_isCell ht_edge,
                  Finset.ne_of_mem_erase (hG'eq ▸ htb'),
                  ⟨pointI b', htb'_cl, hb'cl⟩⟩
          · -- i₁ = j₁ = n
            have hi_eq : i₁ = n := by omega
            have hj_eq : j₁ = n := by omega
            rw [hi_eq, hj_eq]
            simp only [cellAdj]; constructor
            · intro ⟨_, _, h, _⟩; exact absurd rfl h
            · intro h; omega
/-- The edges of a psegment can be linearly ordered.
    HOL Light: `psegment_order` (line 35733). -/
theorem Segment.psegment_order (G : Segment) (hG : G.isPsegment)
    (a b : ℤ × ℤ) (ha : G.isEndpoint a) (hb : G.isEndpoint b) (hab : a ≠ b) :
    ∃ f : ℕ → Set E2,
      (∀ i, i < G.edges.card → f i ∈ G.edges) ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        f i = f j → i = j) ∧
      (∀ e ∈ G.edges, ∃ i, i < G.edges.card ∧ f i = e) ∧
      f 0 = G.terminalEdge a ∧
      (0 < G.edges.card → f (G.edges.card - 1) = G.terminalEdge b) ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) :=
  psegment_order_induct_lemma G.edges.card G hG rfl a b ha hb hab

/-- Variant of psegment ordering starting from one endpoint.
    HOL Light: `psegment_order'` (line 35744). -/
theorem Segment.psegment_order' (G : Segment) (hG : G.isPsegment)
    (m : ℤ × ℤ) (hm : G.isEndpoint m) :
    ∃ f : ℕ → Set E2,
      (∀ i, i < G.edges.card → f i ∈ G.edges) ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        f i = f j → i = j) ∧
      (∀ e ∈ G.edges, ∃ i, i < G.edges.card ∧ f i = e) ∧
      f 0 = G.terminalEdge m ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) := by
  have hps := hG
  obtain ⟨a, b, hab, ha, hb, huniq⟩ := hps
  rcases huniq m hm with rfl | rfl
  · obtain ⟨f, hf1, hf2, hf3, hf4, _, hf6⟩ :=
      G.psegment_order hG m b hm hb hab
    exact ⟨f, hf1, hf2, hf3, hf4, hf6⟩
  · obtain ⟨f, hf1, hf2, hf3, hf4, _, hf6⟩ :=
      G.psegment_order hG m a hm ha (Ne.symm hab)
    exact ⟨f, hf1, hf2, hf3, hf4, hf6⟩

/-! ## Rectagon structure lemmas -/

/-- A rectagon is not a singleton edge set.
    HOL Light: `rectagon_nonsing` (line 35995). -/
theorem Rectagon.not_singleton (G : Rectagon) : G.edges.card ≠ 1 := by
  intro h1
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
  obtain ⟨a, _, _, ha, _, _⟩ := edge_two_endpoints e
    (G.all_edges e (he ▸ Finset.mem_singleton_self e))
  have hd := G.even_degree a
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  have : numClosure G.edges a = 1 := by
    rw [he]
    simp only [numClosure, incidentEdges]
    have : @Finset.filter _ (fun e' => pointI a ∈ closure e')
        (Classical.decPred _) {e} = {e} := by
      rw [Finset.filter_singleton, if_pos ha]
    rw [this]; exact Finset.card_singleton e
  omega

/-- A nonempty subset of a rectagon with all even degrees equals the
    full edge set.
    HOL Light: `rectagon_2` (line 36025). -/
theorem Rectagon.subset_even_eq (G : Rectagon)
    (S : Finset (Set E2)) (hSG : S ⊆ G.edges) (hne : S.Nonempty)
    (heven : ∀ m : ℤ × ℤ, numClosure S m ∈ ({0, 2} : Set ℕ)) :
    S = G.edges := by
  -- S is an inductive subset of G.toSegment, hence equals G.edges
  apply G.toSegment.isInductiveSubset_eq
  refine ⟨hSG, hne, ?_⟩
  intro e heS e' he'G hne' hinter
  -- The shared closure point is a lattice point
  obtain ⟨z, hz1, hz2⟩ := hinter
  obtain ⟨m, rfl⟩ := edges_share_lattice_point e e'
    (G.all_edges e (hSG heS)) (G.all_edges e' he'G) hne' z ⟨hz1, hz2⟩
  classical
  -- numClosure S m ≥ 1 (e ∈ S, incident to m), so = 2
  have hncS_pos : 0 < numClosure S m :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hz1⟩⟩
  have hncS : numClosure S m = 2 := by
    have := heven m; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
  -- numClosure G.edges m = 2
  have hncG : numClosure G.edges m = 2 := by
    have := G.even_degree m; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    have := numClosure_mono hSG m; omega
  -- Extract the two edges at m in S and G
  obtain ⟨a, b, hab, haS, hbS, hcla, hclb, huniqS⟩ :=
    (numClosure_eq_two_iff S m).mp hncS
  obtain ⟨a', b', hab', ha'G, hb'G, hcla', hclb', huniqG⟩ :=
    (numClosure_eq_two_iff G.edges m).mp hncG
  -- a, b ∈ S ⊆ G.edges, so each is a' or b'
  have hcab := huniqG a (hSG haS) hcla
  have hdab := huniqG b (hSG hbS) hclb
  -- e' ∈ G incident to m, so e' = a' or b'
  rcases huniqG e' he'G hz2 with rfl | rfl
  · -- e' = a': show a' ∈ S
    rcases hcab with rfl | rfl
    · exact haS
    · rcases hdab with rfl | rfl
      · exact hbS
      · exact absurd rfl hab
  · -- e' = b': show b' ∈ S
    rcases hcab with rfl | rfl
    · rcases hdab with rfl | rfl
      · exact absurd rfl hab.symm
      · exact hbS
    · exact haS

/-- Two cells sharing a closure point (and distinct) are adjacent.
    HOL Light: `closure_imp_adj` (line 36149). -/
theorem closure_imp_cellAdj (X Y : Set E2) (m : ℤ × ℤ)
    (hX : isCell X) (hY : isCell Y)
    (hXm : pointI m ∈ closure X) (hYm : pointI m ∈ closure Y)
    (hne : X ≠ Y) :
    cellAdj X Y :=
  ⟨hX, hY, hne, ⟨pointI m, hXm, hYm⟩⟩

/-- Endpoints of an inductive subset are endpoints of the whole segment.
    HOL Light: `inductive_set_endpoint` (line 36156). -/
theorem inductiveSubsetOf_endpoint_sub (G : Segment)
    (S : Finset (Set E2)) (hS : G.isInductiveSubset S) :
    ∀ m, numClosure S m = 1 → G.isEndpoint m := by
  have hSeq := G.isInductiveSubset_eq S hS
  intro m hm
  rw [Segment.isEndpoint, ← hSeq]; exact hm

/-- The endpoint set of a single edge equals its closure lattice points.
    HOL Light: `endpoint_closure` (line 36185). -/
theorem endpoint_closure_singleton (e : Set E2) (_he : isEdge e) :
    ∀ m : ℤ × ℤ,
      (numClosure ({e} : Finset (Set E2)) m = 1) ↔
      pointI m ∈ closure e := by
  classical
  intro m; unfold numClosure incidentEdges; constructor
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
    have hmem := hx ▸ Finset.mem_singleton_self x
    rw [Finset.mem_filter, Finset.mem_singleton] at hmem
    exact hmem.1 ▸ hmem.2
  · intro h
    have : Finset.filter (fun x => pointI m ∈ closure x) ({e} : Finset _) = {e} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, hx ▸ h⟩⟩
    rw [this]; exact Finset.card_singleton e


/-- Raw endpoint lemma for adjacency-closed subsets of degree-≤-2 Finsets. -/
private theorem raw_endpoint_of_inductive
    (G S : Finset (Set E2)) (hSG : S ⊆ G) (_hAll : ∀ e ∈ G, isEdge e)
    (hDeg : ∀ m, numClosure G m ∈ ({0, 1, 2} : Set ℕ))
    (hClosed : ∀ e ∈ S, ∀ e' ∈ G, e ≠ e' →
      (closure e ∩ closure e').Nonempty → e' ∈ S)
    (m : ℤ × ℤ) (hm : numClosure S m = 1) : numClosure G m = 1 := by
  have hle := numClosure_mono hSG m
  obtain ⟨f, ⟨hfS, hfcl⟩, hfuniq⟩ := (numClosure_eq_one_iff S m).mp hm
  by_contra hne; have hGm := hDeg m
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hGm
  have hGm2 : numClosure G m = 2 := by omega
  obtain ⟨a, b, hab, haG, hbG, hacl, hbcl, huniq⟩ :=
    (numClosure_eq_two_iff G m).mp hGm2
  rcases huniq f (hSG hfS) hfcl with rfl | rfl
  · exact hab (hfuniq b ⟨hClosed f hfS b hbG hab ⟨pointI m, hacl, hbcl⟩, hbcl⟩).symm
  · exact hab (hfuniq a ⟨hClosed f hfS a haG (Ne.symm hab)
      ⟨pointI m, hfcl, hacl⟩, hacl⟩)

/-- Parity: a nonempty Finset of edges cannot have exactly one odd-degree vertex. -/
private theorem odd_numClosure_not_unique :
    ∀ k, ∀ (S : Finset (Set E2)), S.card = k → S.Nonempty →
      (∀ e ∈ S, isEdge e) → ∀ m, ¬Even (numClosure S m) →
        ∃ n, n ≠ m ∧ ¬Even (numClosure S n) := by
  intro k; induction k using Nat.strongRecOn with | _ k ih => ?_
  intro S hcard hne hall m hm_odd
  classical
  have hpos : 0 < numClosure S m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm_odd)
  obtain ⟨f, hfS, hfcl⟩ : ∃ f ∈ S, pointI m ∈ closure f := by
    simp only [numClosure, incidentEdges] at hpos
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  obtain ⟨a, b, hab, ha, hb, hlp⟩ := edge_two_endpoints f (hall f hfS)
  obtain ⟨m', hm'cl, hm'ne⟩ : ∃ m', pointI m' ∈ closure f ∧ m' ≠ m := by
    rcases hlp m hfcl with rfl | rfl
    · exact ⟨b, hb, Ne.symm hab⟩
    · exact ⟨a, ha, hab⟩
  by_cases hm'_even : Even (numClosure S m')
  · have hcard' : (S.erase f).card < k := by
      rw [← hcard]; exact Finset.card_erase_lt_of_mem hfS
    have nc_m'_S' : numClosure (S.erase f) m' = numClosure S m' - 1 := by
      simp only [numClosure, incidentEdges, Finset.filter_erase]
      exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hfS, hm'cl⟩)
    have hm'ge : 1 ≤ numClosure S m' :=
      Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨hfS, hm'cl⟩⟩
    have hm'_odd' : ¬Even (numClosure (S.erase f) m') := by
      rw [nc_m'_S']; obtain ⟨k, hk⟩ := hm'_even; intro ⟨j, hj⟩; omega
    have nc_m_S' : numClosure (S.erase f) m = numClosure S m - 1 := by
      simp only [numClosure, incidentEdges, Finset.filter_erase]
      exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hfS, hfcl⟩)
    have hm_even' : Even (numClosure (S.erase f) m) := by
      rw [nc_m_S']; obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hm_odd
      exact ⟨k, by omega⟩
    by_cases hS'ne : (S.erase f).Nonempty
    · obtain ⟨n, hn_ne, hn_odd⟩ := ih _ hcard' (S.erase f) rfl hS'ne
        (fun e he => hall e (Finset.mem_of_mem_erase he)) m' hm'_odd'
      have hn_ne_m : n ≠ m := fun h => by subst h; exact hn_odd hm_even'
      have hn_not_cl : pointI n ∉ closure f := by
        intro hncl
        rcases hlp n hncl with hn_eq | hn_eq <;> rcases hlp m hfcl with hm_eq | hm_eq
        · exact hn_ne_m (hn_eq.trans hm_eq.symm)
        · exact hn_ne ((hlp m' hm'cl).elim
            (fun h => hn_eq.trans h.symm) (fun h => absurd (h.trans hm_eq.symm) hm'ne))
        · exact hn_ne ((hlp m' hm'cl).elim
            (fun h => absurd (h.trans hm_eq.symm) hm'ne) (fun h => hn_eq.trans h.symm))
        · exact hn_ne_m (hn_eq.trans hm_eq.symm)
      have nc_n : numClosure (S.erase f) n = numClosure S n := by
        simp only [numClosure, incidentEdges, Finset.filter_erase]; congr 1
        exact Finset.erase_eq_self.mpr (fun h => hn_not_cl (Finset.mem_filter.mp h).2)
      exact ⟨n, hn_ne_m, nc_n ▸ hn_odd⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'ne
      have hS_sing : S = {f} := by
        ext x; simp only [Finset.mem_singleton]; constructor
        · intro hx; by_contra h
          exact Finset.notMem_empty x (hS'ne ▸ Finset.mem_erase.mpr ⟨h, hx⟩)
        · intro h; subst h; exact hfS
      exfalso; rw [hS_sing] at hm'_even
      simp only [numClosure, incidentEdges,
        Finset.filter_singleton, if_pos hm'cl, Finset.card_singleton] at hm'_even
      exact Nat.not_even_one hm'_even
  · exact ⟨m', hm'ne, hm'_even⟩

-- Rectagon edge operations


/-- Deleting one edge from a rectagon gives a psegment.
    HOL Light: `rectagon_delete` (line 36197). -/
theorem Rectagon.delete_psegment (G : Rectagon) (e : Set E2)
    (he : e ∈ G.edges) :
    ∃ P : Segment, P.isPsegment ∧ P.edges = G.edges.erase e := by
  classical
  set E' := G.edges.erase e with hE'_def
  have he_edge := G.all_edges e he
  obtain ⟨a, b, hab, ha_cl, hb_cl, hcl_all⟩ := edge_two_endpoints e he_edge
  have hncG_a : numClosure G.edges a = 2 := by
    have := G.even_degree a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    have : 0 < numClosure G.edges a :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ha_cl⟩⟩; omega
  have hncG_b : numClosure G.edges b = 2 := by
    have := G.even_degree b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    have : 0 < numClosure G.edges b :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hb_cl⟩⟩; omega
  have nc_erase_on : ∀ m, pointI m ∈ closure e →
      numClosure E' m = numClosure G.edges m - 1 := by
    intro m hm; simp only [numClosure, incidentEdges, E']
    rw [show Finset.filter (fun e' => pointI m ∈ closure e') (G.edges.erase e) =
        (Finset.filter (fun e' => pointI m ∈ closure e') G.edges).erase e from by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto]
    exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨he, hm⟩)
  have nc_erase_off : ∀ m, pointI m ∉ closure e →
      numClosure E' m = numClosure G.edges m := by
    intro m hm; simp only [numClosure, incidentEdges, E']; congr 1
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, hx⟩, hcl⟩ => ⟨hx, hcl⟩,
      fun ⟨hx, hcl⟩ => ⟨⟨fun h => hm (h ▸ hcl), hx⟩, hcl⟩⟩
  have hncE'_a : numClosure E' a = 1 := by rw [nc_erase_on a ha_cl, hncG_a]
  have hncE'_b : numClosure E' b = 1 := by rw [nc_erase_on b hb_cl, hncG_b]
  have hne : E'.Nonempty := by
    have hns := G.not_singleton
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    have : G.edges = {e} := by
      ext x; simp only [Finset.mem_singleton]; constructor
      · intro hx; by_contra hne
        exact Finset.notMem_empty x (h ▸ Finset.mem_erase.mpr ⟨hne, hx⟩)
      · intro hx; subst hx; exact he
    rw [this, Finset.card_singleton] at hns; exact hns rfl
  have hdeg : ∀ m, numClosure E' m ∈ ({0, 1, 2} : Set ℕ) := by
    intro m
    have h1 : numClosure E' m ≤ numClosure G.edges m :=
      hE'_def ▸ numClosure_mono (Finset.erase_subset e G.edges) m
    have h2 := G.even_degree m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with h | h <;> omega
  have hall : ∀ f ∈ E', isEdge f := fun f hf => G.all_edges f (Finset.mem_of_mem_erase hf)
  have hep_sub : ∀ m, numClosure E' m = 1 → m = a ∨ m = b := by
    intro m hm; by_contra h; push Not at h
    have : pointI m ∉ closure e := fun hcl => (hcl_all m hcl).elim h.1 h.2
    rw [nc_erase_off m this] at hm
    have := G.even_degree m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
  have hconn : ∀ S ⊆ (↑E' : Set _), S.Nonempty →
      (∀ C ∈ S, ∀ C' ∈ (↑E' : Set _), cellAdj C C' → C' ∈ S) → S = (↑E' : Set _) := by
    intro S hSE' hSne hSclosed
    set S_fin := E'.filter (fun x => x ∈ S) with hS_fin_def
    have hS_fin_toSet : (↑S_fin : Set _) = S := by
      ext x; simp only [hS_fin_def, Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Finset.mem_coe.mp (hSE' h), h⟩⟩
    have hS_fin_sub : S_fin ⊆ E' := Finset.filter_subset _ _
    have hS_fin_ne : S_fin.Nonempty := by
      obtain ⟨x, hx⟩ := hSne
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp (hSE' hx), hx⟩⟩
    have he_nmem : e ∉ S_fin := fun h => (Finset.mem_erase.mp (hS_fin_sub h)).1 rfl
    have hS_fin_closed : ∀ f ∈ S_fin, ∀ f' ∈ E', f ≠ f' →
        (closure f ∩ closure f').Nonempty → f' ∈ S_fin := by
      intro f hf f' hf' hfne hinter
      have hadj : cellAdj f f' :=
        ⟨isEdge_isCell (hall f (hS_fin_sub hf)),
         isEdge_isCell (hall f' hf'), hfne, hinter⟩
      exact Finset.mem_filter.mpr ⟨hf',
        hSclosed f (Finset.mem_filter.mp hf).2 f' (Finset.mem_coe.mpr hf') hadj⟩
    have hS_deg_off : ∀ m, pointI m ∉ closure e →
        numClosure S_fin m ∈ ({0, 2} : Set ℕ) := by
      intro m hm_off
      have hle := numClosure_mono hS_fin_sub m
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra h; push Not at h
      have hS1 : numClosure S_fin m = 1 := by
        have hGm := G.even_degree m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hGm
        rw [nc_erase_off m hm_off] at hle; omega
      have := raw_endpoint_of_inductive E' S_fin hS_fin_sub hall hdeg
        hS_fin_closed m hS1
      rw [nc_erase_off m hm_off] at this
      have := G.even_degree m
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
    have hS_a_le : numClosure S_fin a ≤ 1 :=
      le_trans (numClosure_mono hS_fin_sub a) (hncE'_a ▸ le_refl _)
    have hS_b_le : numClosure S_fin b ≤ 1 :=
      le_trans (numClosure_mono hS_fin_sub b) (hncE'_b ▸ le_refl _)
    have hS_parity : numClosure S_fin a = numClosure S_fin b := by
      by_contra h
      have : (numClosure S_fin a = 1 ∧ numClosure S_fin b = 0) ∨
             (numClosure S_fin a = 0 ∧ numClosure S_fin b = 1) := by omega
      rcases this with ⟨ha1, hb0⟩ | ⟨ha0, hb1⟩
      · have : ¬Even (numClosure S_fin a) := by rw [ha1]; exact Nat.not_even_one
        obtain ⟨n, hna, hn_odd⟩ := odd_numClosure_not_unique S_fin.card
          S_fin rfl hS_fin_ne (fun f hf => hall f (hS_fin_sub hf)) a this
        have hn_on : pointI n ∈ closure e := by
          by_contra hn_off; have := hS_deg_off n hn_off
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          exact hn_odd (this.elim (· ▸ Even.zero) (· ▸ even_two))
        rcases hcl_all n hn_on with rfl | rfl
        · exact hna rfl
        · exact hn_odd (hb0 ▸ Even.zero)
      · have : ¬Even (numClosure S_fin b) := by rw [hb1]; exact Nat.not_even_one
        obtain ⟨n, hnb, hn_odd⟩ := odd_numClosure_not_unique S_fin.card
          S_fin rfl hS_fin_ne (fun f hf => hall f (hS_fin_sub hf)) b this
        have hn_on : pointI n ∈ closure e := by
          by_contra hn_off; have := hS_deg_off n hn_off
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          exact hn_odd (this.elim (· ▸ Even.zero) (· ▸ even_two))
        rcases hcl_all n hn_on with rfl | rfl
        · exact hn_odd (ha0 ▸ Even.zero)
        · exact hnb rfl
    rcases Nat.eq_zero_or_pos (numClosure S_fin a) with ha0 | ha_pos
    · exfalso
      have hb0 : numClosure S_fin b = 0 := by omega
      have hS_closed_G : ∀ C ∈ S, ∀ C' ∈ (↑G.edges : Set _),
          cellAdj C C' → C' ∈ S := by
        intro C hC C' hC' hadj
        by_cases hC'e : C' = e
        · exfalso; rw [hC'e] at hadj
          obtain ⟨z, hz1, hz2⟩ := hadj.2.2.2
          obtain ⟨k, hk⟩ := edges_share_lattice_point C e
            (hall C (Finset.mem_coe.mp (hSE' hC))) he_edge hadj.2.2.1 z ⟨hz1, hz2⟩
          have hCS : C ∈ S_fin :=
            Finset.mem_filter.mpr ⟨Finset.mem_coe.mp (hSE' hC), hC⟩
          rw [hk] at hz2; rcases hcl_all k hz2 with rfl | rfl
          · have : 0 < numClosure S_fin k := by
              simp only [numClosure, incidentEdges]
              exact Finset.card_pos.mpr ⟨C, Finset.mem_filter.mpr ⟨hCS, hk ▸ hz1⟩⟩
            omega
          · have : 0 < numClosure S_fin k := by
              simp only [numClosure, incidentEdges]
              exact Finset.card_pos.mpr ⟨C, Finset.mem_filter.mpr ⟨hCS, hk ▸ hz1⟩⟩
            omega
        · exact hSclosed C hC C'
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hC'e, Finset.mem_coe.mp hC'⟩)) hadj
      have heq := G.connected S (fun x hx => Finset.mem_coe.mpr
        (Finset.mem_of_mem_erase (Finset.mem_coe.mp (hSE' hx)))) hSne hS_closed_G
      exact (Finset.mem_erase.mp (Finset.mem_coe.mp (hSE' (heq ▸
        Finset.mem_coe.mpr he)))).1 rfl
    · have ha1 : numClosure S_fin a = 1 := by omega
      have hb1 : numClosure S_fin b = 1 := by omega
      have hins_eq : insert e S_fin = G.edges := by
        apply G.subset_even_eq
        · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxS
          · exact he
          · exact Finset.mem_of_mem_erase (hS_fin_sub hxS)
        · exact ⟨e, Finset.mem_insert_self e S_fin⟩
        · intro m
          have e_disj : Disjoint ({e} : Finset _) S_fin :=
            Finset.disjoint_singleton_left.mpr he_nmem
          rw [show insert e S_fin = {e} ∪ S_fin from rfl]
          have nc_add : numClosure ({e} ∪ S_fin) m =
              numClosure ({e} : Finset _) m + numClosure S_fin m := by
            simp only [numClosure, incidentEdges, Finset.filter_union]
            exact Finset.card_union_of_disjoint
              (e_disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
          rw [nc_add]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          by_cases hm_on : pointI m ∈ closure e
          · have hcl1 : numClosure ({e} : Finset _) m = 1 := by
              simp only [numClosure, incidentEdges]
              rw [Finset.filter_singleton, if_pos hm_on, Finset.card_singleton]
            rcases hcl_all m hm_on with rfl | rfl
            · rw [hcl1, ha1]; right; rfl
            · rw [hcl1, hb1]; right; rfl
          · have hcl0 : numClosure ({e} : Finset _) m = 0 := by
              simp only [numClosure, incidentEdges]
              rw [Finset.filter_singleton, if_neg hm_on, Finset.card_empty]
            rw [hcl0, Nat.zero_add]
            exact hS_deg_off m hm_on
      have hS_fin_eq : S_fin = E' := by
        have h1 : (insert e S_fin).erase e = S_fin := Finset.erase_insert he_nmem
        rw [← h1, hins_eq]
      rw [← hS_fin_toSet, hS_fin_eq]
  refine ⟨⟨E', hne, hall, hdeg, hconn⟩, ?_, rfl⟩
  exact ⟨a, b, hab, hncE'_a, hncE'_b, fun m hm => hep_sub m hm⟩

/-- A lattice point in the closure of a deleted edge becomes an endpoint.
    HOL Light: `rectagon_delete_end` (line 36459). -/
theorem Rectagon.delete_endpoint (G : Rectagon) (e : Set E2) (m : ℤ × ℤ)
    (he : e ∈ G.edges) (hcl : pointI m ∈ closure e) :
    ∀ P : Segment, P.edges = G.edges.erase e →
      P.isEndpoint m := by
  classical
  intro P hPeq
  simp only [Segment.isEndpoint, hPeq]
  have ie_erase : incidentEdges (G.edges.erase e) m =
      (incidentEdges G.edges m).erase e := by
    simp only [incidentEdges]
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have nc_erase : numClosure (G.edges.erase e) m = numClosure G.edges m - 1 := by
    simp only [numClosure, ie_erase]
    exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨he, hcl⟩)
  have hd := G.even_degree m
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  have hpos : 0 < numClosure G.edges m := by
    simp only [numClosure, incidentEdges]
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hcl⟩⟩
  omega

/-- In a rectagon, edge adjacency corresponds to being at a shared endpoint
    of the deleted graph.
    HOL Light: `rectagon_adj` (line 36295). -/
theorem Rectagon.adj_iff_terminal (G : Rectagon) (e f : Set E2)
    (he : e ∈ G.edges) (hf : f ∈ G.edges) :
    cellAdj e f ↔
      ∃ (P : Segment) (a : ℤ × ℤ),
        P.edges = G.edges.erase e ∧ P.isEndpoint a ∧
        f = P.terminalEdge a := by
  constructor
  · -- (→) cellAdj e f → ∃ P a, ...
    intro hadj
    have he_edge := G.all_edges e he
    have hf_edge := G.all_edges f hf
    obtain ⟨P, _, hPeq⟩ := G.delete_psegment e he
    -- Extract the shared lattice point from cellAdj
    obtain ⟨p, hpe, hpf⟩ := hadj.2.2.2
    obtain ⟨m, rfl⟩ := edges_share_lattice_point e f he_edge hf_edge hadj.2.2.1 p ⟨hpe, hpf⟩
    have hPm : P.isEndpoint m := G.delete_endpoint e m he hpe P hPeq
    have hfP : f ∈ P.edges :=
      hPeq ▸ Finset.mem_erase.mpr ⟨Ne.symm hadj.2.2.1, hf⟩
    exact ⟨P, m, hPeq, hPm, P.terminalEdge_unique m hPm f hfP hpf⟩
  · -- (←) ∃ P a, ... → cellAdj e f
    rintro ⟨P, a, hPeq, hPa, rfl⟩
    obtain ⟨htP, htcl⟩ := P.terminalEdge_prop a hPa
    have htG : P.terminalEdge a ∈ G.edges := by
      rw [hPeq] at htP; exact Finset.mem_of_mem_erase htP
    have htne : P.terminalEdge a ≠ e := by
      rw [hPeq] at htP; exact (Finset.mem_erase.mp htP).1
    have ha_cle : pointI a ∈ closure e := by
      by_contra he_not
      have : numClosure (G.edges.erase e) a = numClosure G.edges a := by
        simp only [numClosure, incidentEdges]; congr 1
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨⟨_, hx⟩, hcl⟩ ↦ ⟨hx, hcl⟩,
          fun ⟨hx, hcl⟩ ↦ ⟨⟨fun h ↦ he_not (h ▸ hcl), hx⟩, hcl⟩⟩
      rw [← hPeq] at this; rw [hPa] at this
      have hd := G.even_degree a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd; omega
    exact ⟨isEdge_isCell (G.all_edges e he), isEdge_isCell (G.all_edges _ htG),
      Ne.symm htne, ⟨pointI a, ha_cle, htcl⟩⟩

/-- The edges of a rectagon can be cyclically ordered: there exists a
    bijection f from {0, ..., |E|-1} to E where consecutive (and
    wrap-around) indices correspond to adjacent edges.
    HOL Light: `rectagon_order` (line 36612). -/
theorem Rectagon.cyclic_order (G : Rectagon) (e : Set E2) (m : ℤ × ℤ)
    (he : e ∈ G.edges) (hcl : pointI m ∈ closure e) :
    ∃ f : ℕ → Set E2,
      (∀ i, i < G.edges.card → f i ∈ G.edges) ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        f i = f j → i = j) ∧
      (∀ g ∈ G.edges, ∃ i, i < G.edges.card ∧ f i = g) ∧
      f (G.edges.card - 1) = e ∧
      pointI m ∈ closure (f 0) ∧
      (∀ i j, i < G.edges.card → j < G.edges.card →
        (cellAdj (f i) (f j) ↔
          (i + 1 = j ∨ j + 1 = i ∨
           (i = 0 ∧ j = G.edges.card - 1) ∨
           (i = G.edges.card - 1 ∧ j = 0)))) := by
  classical
  -- Delete e to get psegment P
  obtain ⟨P, hPps, hPeq⟩ := G.delete_psegment e he
  have he_edge := G.all_edges e he
  have hPm : P.isEndpoint m := G.delete_endpoint e m he hcl P hPeq
  -- Get the other endpoint n of P
  have hPps' := hPps
  obtain ⟨a₀, b₀, hab₀, ha₀, hb₀, huniq₀⟩ := hPps
  obtain ⟨n, hn_ep, hmn⟩ : ∃ n, P.isEndpoint n ∧ m ≠ n := by
    rcases huniq₀ m hPm with rfl | rfl
    · exact ⟨b₀, hb₀, hab₀⟩
    · exact ⟨a₀, ha₀, hab₀.symm⟩
  -- Cardinalities
  have hPcard : P.edges.card = G.edges.card - 1 := by
    rw [hPeq, Finset.card_erase_of_mem he]
  have hGge2 : 2 ≤ G.edges.card := by
    have := G.not_singleton; have := G.nonempty.card_pos; omega
  have hPpos : 0 < P.edges.card := by omega
  -- Lattice points on e are endpoints of P, hence m or n
  have hcl_mn : ∀ k, pointI k ∈ closure e → k = m ∨ k = n :=
    fun k hk => P.two_endpoint_bound n m hn_ep hPm hmn k
      (G.delete_endpoint e k he hk P hPeq)
  -- n is on closure(e)
  obtain ⟨c₁, c₂, hne_c, hc₁, hc₂, _⟩ := edge_two_endpoints e he_edge
  have hn_cl : pointI n ∈ closure e := by
    rcases hcl_mn c₁ hc₁ with rfl | rfl
    · rcases hcl_mn c₂ hc₂ with h | rfl
      · exact absurd h.symm hne_c
      · exact hc₂
    · exact hc₁
  -- Psegment ordering of P
  obtain ⟨f', hfmem, hfinj, hfsurj, hf0, hflast, hfadj⟩ :=
    P.psegment_order hPps' m n hPm hn_ep hmn
  -- Define g: extend f' with e at the last position
  set g := fun i => if i < G.edges.card - 1 then f' i else e with hg_def
  have hg_lt : ∀ i, i < G.edges.card - 1 → g i = f' i := fun i hi => if_pos hi
  have hg_last : g (G.edges.card - 1) = e := if_neg (by omega)
  -- f'(i) ∈ G.edges.erase e
  have hfi_erase : ∀ i, i < G.edges.card - 1 → f' i ∈ G.edges.erase e :=
    fun i hi => hPeq ▸ hfmem i (by omega)
  -- Key: e is adjacent to f'(j) iff j = 0 or j = card-2
  have adj_e : ∀ j, j < G.edges.card - 1 →
      (cellAdj e (f' j) ↔ (j = 0 ∨ j = G.edges.card - 2)) := by
    intro j hj; constructor
    · intro ⟨_, _, hne, ⟨z, hz1, hz2⟩⟩
      obtain ⟨k, hk⟩ := edges_share_lattice_point e (f' j) he_edge
        (G.all_edges _ (Finset.mem_of_mem_erase (hfi_erase j hj))) hne z ⟨hz1, hz2⟩
      rw [hk] at hz1 hz2
      rcases hcl_mn k hz1 with heq | heq
      · left; rw [heq] at hz2
        exact hfinj j 0 (by omega) (by omega)
          ((P.terminalEdge_unique m hPm (f' j) (hfmem j (by omega)) hz2).trans hf0.symm)
      · right; rw [heq] at hz2
        have := hfinj j (P.edges.card - 1) (by omega) (by omega)
          ((P.terminalEdge_unique n hn_ep (f' j) (hfmem j (by omega)) hz2).trans
            (hflast hPpos).symm)
        omega
    · intro h; rcases h with rfl | rfl
      · rw [hf0]; obtain ⟨htm, htm_cl⟩ := P.terminalEdge_prop m hPm
        exact ⟨isEdge_isCell he_edge, isEdge_isCell (P.all_edges _ htm),
          Ne.symm (Finset.mem_erase.mp (hPeq ▸ htm)).1, ⟨pointI m, hcl, htm_cl⟩⟩
      · have hfn : f' (G.edges.card - 2) = P.terminalEdge n := by
          rw [show G.edges.card - 2 = P.edges.card - 1 from by omega]; exact hflast hPpos
        rw [hfn]; obtain ⟨htn, htn_cl⟩ := P.terminalEdge_prop n hn_ep
        exact ⟨isEdge_isCell he_edge, isEdge_isCell (P.all_edges _ htn),
          Ne.symm (Finset.mem_erase.mp (hPeq ▸ htn)).1, ⟨pointI n, hn_cl, htn_cl⟩⟩
  -- Prove all properties
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) g i ∈ G.edges
  · intro i hi; by_cases hi' : i < G.edges.card - 1
    · rw [hg_lt i hi']; exact Finset.mem_of_mem_erase (hfi_erase i hi')
    · rw [show i = G.edges.card - 1 from by omega, hg_last]; exact he
  -- (2) injectivity
  · intro i j hi hj heq; by_cases hi' : i < G.edges.card - 1
    · by_cases hj' : j < G.edges.card - 1
      · rw [hg_lt i hi', hg_lt j hj'] at heq; exact hfinj i j (by omega) (by omega) heq
      · rw [hg_lt i hi', show j = G.edges.card - 1 from by omega, hg_last] at heq
        exact absurd heq (Finset.mem_erase.mp (hfi_erase i hi')).1
    · by_cases hj' : j < G.edges.card - 1
      · rw [show i = G.edges.card - 1 from by omega, hg_last, hg_lt j hj'] at heq
        exact absurd heq.symm (Finset.mem_erase.mp (hfi_erase j hj')).1
      · omega
  -- (3) surjectivity
  · intro e' he'; by_cases he'_eq : e' = e
    · exact ⟨G.edges.card - 1, by omega, he'_eq ▸ hg_last⟩
    · have he'P : e' ∈ P.edges := by rw [hPeq]; exact Finset.mem_erase.mpr ⟨he'_eq, he'⟩
      obtain ⟨i, hi, hfi⟩ := hfsurj e' he'P
      exact ⟨i, by omega, (hg_lt i (by omega)).trans hfi⟩
  -- (4) g(card-1) = e
  · exact hg_last
  -- (5) pointI m ∈ closure(g 0)
  · rw [hg_lt 0 (by omega), hf0]; exact (P.terminalEdge_prop m hPm).2
  -- (6) adjacency
  · intro i j hi hj; by_cases hi' : i < G.edges.card - 1
    · by_cases hj' : j < G.edges.card - 1
      · -- Both < card - 1: use psegment ordering
        rw [hg_lt i hi', hg_lt j hj']; constructor
        · intro hadj; rcases (hfadj i j (by omega) (by omega)).mp hadj with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · intro h; apply (hfadj i j (by omega) (by omega)).mpr
          rcases h with h | h | ⟨_, h⟩ | ⟨h, _⟩
          <;> [exact Or.inl h; exact Or.inr h; omega; omega]
      · -- i < card-1, j = card-1
        rw [hg_lt i hi', show j = G.edges.card - 1 from by omega, hg_last]; constructor
        · intro hadj; rcases (adj_e i hi').mp (cellAdj_symm.mp hadj) with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
          · exact Or.inl (by omega)
        · intro h; apply cellAdj_symm.mpr
          rcases h with h | h | ⟨rfl, _⟩ | ⟨h, _⟩
          · exact (adj_e i hi').mpr (Or.inr (by omega))
          · omega
          · exact (adj_e 0 (by omega)).mpr (Or.inl rfl)
          · omega
    · by_cases hj' : j < G.edges.card - 1
      · -- i = card-1, j < card-1
        rw [show i = G.edges.card - 1 from by omega, hg_last, hg_lt j hj']; constructor
        · intro hadj; rcases (adj_e j hj').mp hadj with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
          · exact Or.inr (Or.inl (by omega))
        · intro h
          rcases h with h | h | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · omega
          · exact (adj_e j hj').mpr (Or.inr (by omega))
          · omega
          · exact (adj_e 0 (by omega)).mpr (Or.inl rfl)
      · -- i = j = card-1
        rw [show i = G.edges.card - 1 from by omega,
            show j = G.edges.card - 1 from by omega, hg_last]; constructor
        · intro ⟨_, _, h, _⟩; exact absurd rfl h
        · intro h; rcases h with h | h | ⟨h, _⟩ | ⟨_, h⟩ <;> omega

/-! ## cls: Closure lattice points of an edge set -/

/-- The set of lattice points in the closure of any edge in E.
    HOL Light: `cls E` (line 36907). -/
def cls (E : Finset (Set E2)) : Set (ℤ × ℤ) :=
  {m | ∃ e ∈ E, pointI m ∈ closure e}

/-- cls of a singleton edge set.
    HOL Light: `cls_edge` (line 36910). -/
theorem cls_singleton (e : Set E2) :
    cls {e} = {m | pointI m ∈ closure e} := by
  ext m; simp [cls, Finset.mem_singleton]

/-- cls is injective on vertical edges.
    HOL Light: `cls_inj_lemma_v` (line 36919). -/
theorem cls_inj_vEdge (m n : ℤ × ℤ) (h : cls {vEdge m} = cls {vEdge n}) :
    m = n := by
  have hm : pointI m ∈ closure (vEdge n) := by
    have : m ∈ cls {vEdge n} := by
      rw [← h, cls_singleton]; exact (pointI_mem_closure_vEdge m m).mpr ⟨rfl, Or.inl rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  have hm' : pointI (m.1, m.2 + 1) ∈ closure (vEdge n) := by
    have : (m.1, m.2 + 1) ∈ cls {vEdge n} := by
      rw [← h, cls_singleton]
      exact (pointI_mem_closure_vEdge _ m).mpr ⟨rfl, Or.inr rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  rw [pointI_mem_closure_vEdge] at hm hm'
  exact Prod.ext hm.1
    (by rcases hm.2 with h1 | h1 <;> rcases hm'.2 with h2 | h2 <;> omega)

/-- cls is injective on horizontal edges.
    HOL Light: `cls_inj_lemma_h` (line 36937). -/
theorem cls_inj_hEdge (m n : ℤ × ℤ) (h : cls {hEdge m} = cls {hEdge n}) :
    m = n := by
  have hm : pointI m ∈ closure (hEdge n) := by
    have : m ∈ cls {hEdge n} := by
      rw [← h, cls_singleton]; exact (pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  have hm' : pointI (m.1 + 1, m.2) ∈ closure (hEdge n) := by
    have : (m.1 + 1, m.2) ∈ cls {hEdge n} := by
      rw [← h, cls_singleton]
      exact (pointI_mem_closure_hEdge _ m).mpr ⟨rfl, Or.inr rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  rw [pointI_mem_closure_hEdge] at hm hm'
  exact Prod.ext
    (by rcases hm.2 with h1 | h1 <;> rcases hm'.2 with h2 | h2 <;> omega) hm.1

/-- cls distinguishes horizontal and vertical edges.
    HOL Light: `cls_inj_lemma_hv` (line 36955). -/
theorem cls_ne_hv (m n : ℤ × ℤ) : cls {hEdge m} ≠ cls {vEdge n} := by
  intro h
  have hm : pointI m ∈ closure (vEdge n) := by
    have : m ∈ cls {vEdge n} := by
      rw [← h, cls_singleton]; exact (pointI_mem_closure_hEdge m m).mpr ⟨rfl, Or.inl rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  have hm' : pointI (m.1 + 1, m.2) ∈ closure (vEdge n) := by
    have : (m.1 + 1, m.2) ∈ cls {vEdge n} := by
      rw [← h, cls_singleton]
      exact (pointI_mem_closure_hEdge _ m).mpr ⟨rfl, Or.inr rfl⟩
    rwa [cls_singleton, Set.mem_setOf_eq] at this
  rw [pointI_mem_closure_vEdge] at hm hm'
  obtain ⟨h1, _⟩ := hm; obtain ⟨h2, _⟩ := hm'; omega

/-- cls is injective on edges.
    HOL Light: `cls_inj` (line 36973). -/
theorem cls_injective (e f : Set E2) (he : isEdge e) (hf : isEdge f)
    (h : cls {e} = cls {f}) : e = f := by
  rcases he with ⟨me, rfl⟩ | ⟨me, rfl⟩ <;> rcases hf with ⟨mf, rfl⟩ | ⟨mf, rfl⟩
  · exact congrArg hEdge (cls_inj_hEdge me mf h)
  · exact absurd h (cls_ne_hv me mf)
  · exact absurd h.symm (cls_ne_hv mf me)
  · exact congrArg vEdge (cls_inj_vEdge me mf h)
/-- A linear chain of adjacent edges forms a psegment.
    HOL Light: `order_imp_psegment` (line 35763). -/
theorem order_imp_psegment (f : ℕ → Set E2) (n : ℕ) (hn : 0 < n)
    (hInj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hEdge : ∀ i, i < n → isEdge (f i))
    (hAdj : ∀ i j, i < n → j < n →
      (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) :
    ∃ G : Segment, G.isPsegment ∧
      G.edges = Finset.image f (Finset.range n) := by
  classical
  -- Shared closure point ⇒ consecutive indices
  have consec : ∀ (m : ℤ × ℤ) i j, i < n → j < n → i ≠ j →
      pointI m ∈ closure (f i) → pointI m ∈ closure (f j) →
      i + 1 = j ∨ j + 1 = i := fun m i j hi hj hij hci hcj =>
    (hAdj i j hi hj).mp (closure_imp_cellAdj _ _ m
      (isEdge_isCell (hEdge i hi)) (isEdge_isCell (hEdge j hj)) hci hcj
      (fun h => hij (hInj i j hi hj h)))
  set E := Finset.image f (Finset.range n) with hE_def
  have f_inj : Set.InjOn f ↑(Finset.range n) :=
    fun i hi j hj => hInj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  have mem_E : ∀ i, i < n → f i ∈ E :=
    fun i hi => Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have mem_E_inv : ∀ e ∈ E, ∃ i, i < n ∧ f i = e := fun e he => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he; exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  -- Relate numClosure to an index filter
  have nc_eq : ∀ m : ℤ × ℤ, numClosure E m =
      ((Finset.range n).filter (fun i => pointI m ∈ closure (f i))).card := by
    intro m
    have img_eq : Finset.image f
        ((Finset.range n).filter (fun i => pointI m ∈ closure (f i))) =
        incidentEdges E m := by
      ext e; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range,
        incidentEdges, Finset.mem_filter]
      exact ⟨fun ⟨i, ⟨hi, hcl⟩, hfi⟩ => hfi ▸ ⟨mem_E i hi, hcl⟩,
        fun ⟨he, hcl⟩ => by
          obtain ⟨i, hi, hfi⟩ := mem_E_inv e he; subst hfi; exact ⟨i, ⟨hi, hcl⟩, rfl⟩⟩
    rw [numClosure, ← img_eq, Finset.card_image_of_injOn
      (f_inj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
  -- 1. Degree bound: numClosure E m ≤ 2
  have h_deg : ∀ m : ℤ × ℤ, numClosure E m ∈ ({0, 1, 2} : Set ℕ) := by
    intro m; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [nc_eq]; set I := (Finset.range n).filter (fun i => pointI m ∈ closure (f i))
    suffices I.card ≤ 2 by omega
    by_contra hgt; push Not at hgt
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp (by omega)
    obtain ⟨hi_r, hi_c⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj_r, hj_c⟩ := Finset.mem_filter.mp hj
    obtain ⟨hk_r, hk_c⟩ := Finset.mem_filter.mp hk
    have := consec m i j (Finset.mem_range.mp hi_r) (Finset.mem_range.mp hj_r) hij hi_c hj_c
    have := consec m i k (Finset.mem_range.mp hi_r) (Finset.mem_range.mp hk_r) hik hi_c hk_c
    have := consec m j k (Finset.mem_range.mp hj_r) (Finset.mem_range.mp hk_r) hjk hj_c hk_c
    omega
  -- 2. Connectivity
  have h_conn : ∀ S ⊆ (↑E : Set _), S.Nonempty →
      (∀ C ∈ S, ∀ C' ∈ (↑E : Set _), cellAdj C C' → C' ∈ S) → S = (↑E : Set _) := by
    intro S hS ⟨s, hs⟩ hcl
    obtain ⟨i₀, hi₀, rfl⟩ := mem_E_inv s (Finset.mem_coe.mp (hS hs))
    have step_up : ∀ j, j < n → f j ∈ S → j + 1 < n → f (j + 1) ∈ S :=
      fun j hj hjS hjn => hcl _ hjS _ (Finset.mem_coe.mpr (mem_E _ hjn))
        ((hAdj j (j + 1) hj hjn).mpr (Or.inl rfl))
    have step_dn : ∀ j, j < n → f j ∈ S → 0 < j → f (j - 1) ∈ S :=
      fun j hj hjS hj0 => hcl _ hjS _ (Finset.mem_coe.mpr (mem_E _ (by omega)))
        ((hAdj j (j - 1) hj (by omega)).mpr (Or.inr (by omega)))
    have up : ∀ k, i₀ + k < n → f (i₀ + k) ∈ S := by
      intro k; induction k with
      | zero => simp only [add_zero]; exact fun _ => hs
      | succ k ih => intro hk; exact step_up _ (Nat.lt_of_succ_lt hk) (ih (Nat.lt_of_succ_lt hk)) hk
    have dn : ∀ k, k ≤ i₀ → f (i₀ - k) ∈ S := by
      intro k; induction k with
      | zero => exact fun _ => by simp only [tsub_zero]; exact hs
      | succ k ih => intro hk; exact step_dn (i₀ - k) (by omega) (ih (by omega)) (by omega)
    ext e; exact ⟨fun he => hS he, fun he => by
      obtain ⟨j, hj, rfl⟩ := mem_E_inv e (Finset.mem_coe.mp he)
      by_cases h : i₀ ≤ j
      · have := up (j - i₀) (by omega)
        rwa [show i₀ + (j - i₀) = j from by omega] at this
      · have := dn (i₀ - j) (by omega : i₀ - j ≤ i₀)
        rwa [Nat.sub_sub_self (by omega : j ≤ i₀)] at this⟩
  -- 3. Build the segment
  set G : Segment := ⟨E, ⟨f 0, mem_E 0 hn⟩,
    fun e he => by obtain ⟨i, hi, rfl⟩ := mem_E_inv e he; exact hEdge i hi,
    h_deg, h_conn⟩
  refine ⟨G, ?_, rfl⟩
  -- 4. Show isPsegment via endpoint_count
  rcases G.endpoint_count with hall | hps
  · exfalso
    obtain ⟨a, b, hab, ha_cl, hb_cl, huniq⟩ := edge_two_endpoints (f 0) (hEdge 0 hn)
    have deg2 : ∀ p, pointI p ∈ closure (f 0) → numClosure E p ≥ 2 := by
      intro p hp
      have h1 : numClosure E p ≥ 1 := by
        rw [nc_eq]; exact Finset.one_le_card.mpr
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hp⟩⟩
      have h2 := h_deg p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
      have h3 : numClosure E p ≠ 1 := fun h => hall p h
      omega
    have sec : ∀ p, pointI p ∈ closure (f 0) →
        1 < n ∧ pointI p ∈ closure (f 1) := by
      intro p hp
      have hge2 := deg2 p hp; rw [nc_eq] at hge2
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by linarith)
      obtain ⟨hi_r, hi_c⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj_r, hj_c⟩ := Finset.mem_filter.mp hj
      obtain ⟨k, hk, hk0, hkp⟩ : ∃ k, k < n ∧ k ≠ 0 ∧ pointI p ∈ closure (f k) := by
        by_cases h : i = 0
        · exact ⟨j, Finset.mem_range.mp hj_r, fun h' => hij (h.trans h'.symm), hj_c⟩
        · exact ⟨i, Finset.mem_range.mp hi_r, h, hi_c⟩
      have hk1 : k = 1 := by have := consec p 0 k hn hk (by omega) hp hkp; omega
      exact ⟨hk1 ▸ hk, hk1 ▸ hkp⟩
    obtain ⟨hn2, ha_f1⟩ := sec a ha_cl
    obtain ⟨_, hb_f1⟩ := sec b hb_cl
    have h_cls : cls {f 0} = cls {f 1} := by
      ext p; simp only [cls_singleton, Set.mem_setOf]
      exact ⟨fun hp => by rcases huniq p hp with rfl | rfl <;> assumption,
        fun hp => by
          obtain ⟨c, d, _, _, _, huniq'⟩ := edge_two_endpoints (f 1) (hEdge 1 hn2)
          rcases huniq' a ha_f1 with rfl | rfl <;> rcases huniq' b hb_f1 with rfl | rfl <;>
            rcases huniq' p hp with rfl | rfl
          all_goals first | exact ha_cl | exact hb_cl | exact absurd rfl hab⟩
    exact absurd (cls_injective _ _ (hEdge 0 hn) (hEdge 1 hn2) h_cls)
      (fun h => absurd (hInj 0 1 hn hn2 h) (by omega))
  · exact hps

/-- A linear chain of adjacent edges with shifted indices forms a psegment.
    HOL Light: `order_imp_psegment_shift` (line 36871). -/
theorem order_imp_psegment_shift (f : ℕ → Set E2) (lo hi : ℕ)
    (hlt : lo < hi)
    (hInj : ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi →
      f i = f j → i = j)
    (hEdge : ∀ i, lo ≤ i → i < hi → isEdge (f i))
    (hAdj : ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi →
      (cellAdj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i))) :
    ∃ G : Segment, G.isPsegment ∧
      G.edges = Finset.image f (Finset.Ico lo hi) := by
  set g : ℕ → Set E2 := fun i => f (i + lo) with hg_def
  set n := hi - lo with hn_def
  have hn_pos : 0 < n := by omega
  have hgInj : ∀ i j, i < n → j < n → g i = g j → i = j := by
    intro i j hi hj hgij
    have := hInj (i + lo) (j + lo) (by omega) (by omega) (by omega) (by omega) hgij
    omega
  have hgEdge : ∀ i, i < n → isEdge (g i) := by
    intro i hi; exact hEdge (i + lo) (by omega) (by omega)
  have hgAdj : ∀ i j, i < n → j < n →
      (cellAdj (g i) (g j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    constructor
    · intro hadj
      have := (hAdj (i + lo) (j + lo) (by omega) (by omega)
        (by omega) (by omega)).mp hadj
      omega
    · intro h
      apply (hAdj (i + lo) (j + lo) (by omega) (by omega)
        (by omega) (by omega)).mpr
      omega
  obtain ⟨G, hGps, hGedges⟩ := order_imp_psegment g n hn_pos hgInj hgEdge hgAdj
  refine ⟨G, hGps, ?_⟩
  rw [hGedges]
  ext e; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico, g]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i + lo, ⟨by omega, by omega⟩, rfl⟩
  · rintro ⟨i, ⟨hlo, hhi⟩, rfl⟩; exact ⟨i - lo, by omega, by congr 1; omega⟩


/-! ## adjv: The shared lattice point of two adjacent edges -/

/-- The unique shared lattice point of two adjacent edges.
    HOL Light: `adjv e f` (line 36988). -/
noncomputable def adjv (e f : Set E2) : ℤ × ℤ :=
  open Classical in
  if h : ∃ m : ℤ × ℤ, pointI m ∈ closure e ∧ pointI m ∈ closure f then
    Classical.choose h
  else (0, 0)


/-- `adjv` lies in the closure of the first edge (when they are adjacent edges).
    HOL Light: `adjv_adj` (line 36992). -/
theorem adjv_closure_left (e f : Set E2) (he : isEdge e) (hf : isEdge f)
    (hadj : cellAdj e f) :
    pointI (adjv e f) ∈ closure e := by
  have hexists : ∃ m : ℤ × ℤ, pointI m ∈ closure e ∧ pointI m ∈ closure f := by
    obtain ⟨z, hz_e, hz_f⟩ := hadj.2.2.2
    rcases he with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hf with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [closure_hEdge] at hz_e hz_f; simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h2 : a.2 = b.2 := by exact_mod_cast he3.symm.trans hf3
      have hne : a.1 ≠ b.1 := fun h => hadj.2.2.1 (congrArg hEdge (Prod.ext h h2))
      have : a.1 ≤ b.1 + 1 := by
        exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 + 1 from le_trans he1 hf2)
      have : b.1 ≤ a.1 + 1 := by
        exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 + 1 from le_trans hf1 he2)
      rcases (show a.1 + 1 = b.1 ∨ b.1 + 1 = a.1 from by omega) with hab | hab
      · exact ⟨b, (pointI_mem_closure_hEdge _ _).mpr ⟨h2.symm, Or.inr (by omega)⟩,
            (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, Or.inl rfl⟩,
            (pointI_mem_closure_hEdge _ _).mpr ⟨h2, Or.inr (by omega)⟩⟩
    · rw [closure_hEdge] at hz_e; rw [closure_vEdge] at hz_f
      simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : b.1 = a.1 ∨ b.1 = a.1 + 1 := by
        have : a.1 ≤ b.1 := by exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 by linarith)
        have : b.1 ≤ a.1 + 1 := by exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 + 1 by linarith)
        omega
      have h2 : a.2 = b.2 ∨ a.2 = b.2 + 1 := by
        have : b.2 ≤ a.2 := by exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 by linarith)
        have : a.2 ≤ b.2 + 1 := by exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 + 1 by linarith)
        omega
      exact ⟨(b.1, a.2), (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, h1⟩,
        (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, h2⟩⟩
    · rw [closure_vEdge] at hz_e; rw [closure_hEdge] at hz_f
      simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : a.1 = b.1 ∨ a.1 = b.1 + 1 := by
        have : b.1 ≤ a.1 := by exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 by linarith)
        have : a.1 ≤ b.1 + 1 := by exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 + 1 by linarith)
        omega
      have h2 : b.2 = a.2 ∨ b.2 = a.2 + 1 := by
        have : a.2 ≤ b.2 := by exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 by linarith)
        have : b.2 ≤ a.2 + 1 := by exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 + 1 by linarith)
        omega
      exact ⟨(a.1, b.2), (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, h2⟩,
        (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, h1⟩⟩
    · rw [closure_vEdge] at hz_e hz_f; simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : a.1 = b.1 := by exact_mod_cast he1.symm.trans hf1
      have hne : a.2 ≠ b.2 := fun h => hadj.2.2.1 (congrArg vEdge (Prod.ext h1 h))
      have : a.2 ≤ b.2 + 1 := by
        exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 + 1 from le_trans he2 hf3)
      have : b.2 ≤ a.2 + 1 := by
        exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 + 1 from le_trans hf2 he3)
      rcases (show a.2 + 1 = b.2 ∨ b.2 + 1 = a.2 from by omega) with hab | hab
      · exact ⟨b, (pointI_mem_closure_vEdge _ _).mpr ⟨h1.symm, Or.inr (by omega)⟩,
            (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, Or.inl rfl⟩,
            (pointI_mem_closure_vEdge _ _).mpr ⟨h1, Or.inr (by omega)⟩⟩
  simp only [adjv, dif_pos hexists]
  exact (Classical.choose_spec hexists).1

/-- `adjv` lies in the closure of the second edge (when they are adjacent edges).
    HOL Light: `adjv_adj2` (line 37003). -/
theorem adjv_closure_right (e f : Set E2) (he : isEdge e) (hf : isEdge f)
    (hadj : cellAdj e f) :
    pointI (adjv e f) ∈ closure f := by
  have hexists : ∃ m : ℤ × ℤ, pointI m ∈ closure e ∧ pointI m ∈ closure f := by
    obtain ⟨z, hz_e, hz_f⟩ := hadj.2.2.2
    rcases he with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hf with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [closure_hEdge] at hz_e hz_f; simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h2 : a.2 = b.2 := by exact_mod_cast he3.symm.trans hf3
      have hne : a.1 ≠ b.1 := fun h => hadj.2.2.1 (congrArg hEdge (Prod.ext h h2))
      have : a.1 ≤ b.1 + 1 := by
        exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 + 1 from le_trans he1 hf2)
      have : b.1 ≤ a.1 + 1 := by
        exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 + 1 from le_trans hf1 he2)
      rcases (show a.1 + 1 = b.1 ∨ b.1 + 1 = a.1 from by omega) with hab | hab
      · exact ⟨b, (pointI_mem_closure_hEdge _ _).mpr ⟨h2.symm, Or.inr (by omega)⟩,
            (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, Or.inl rfl⟩,
            (pointI_mem_closure_hEdge _ _).mpr ⟨h2, Or.inr (by omega)⟩⟩
    · rw [closure_hEdge] at hz_e; rw [closure_vEdge] at hz_f
      simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : b.1 = a.1 ∨ b.1 = a.1 + 1 := by
        have : a.1 ≤ b.1 := by exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 by linarith)
        have : b.1 ≤ a.1 + 1 := by exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 + 1 by linarith)
        omega
      have h2 : a.2 = b.2 ∨ a.2 = b.2 + 1 := by
        have : b.2 ≤ a.2 := by exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 by linarith)
        have : a.2 ≤ b.2 + 1 := by exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 + 1 by linarith)
        omega
      exact ⟨(b.1, a.2), (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, h1⟩,
        (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, h2⟩⟩
    · rw [closure_vEdge] at hz_e; rw [closure_hEdge] at hz_f
      simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : a.1 = b.1 ∨ a.1 = b.1 + 1 := by
        have : b.1 ≤ a.1 := by exact_mod_cast (show (↑b.1 : ℝ) ≤ ↑a.1 by linarith)
        have : a.1 ≤ b.1 + 1 := by exact_mod_cast (show (↑a.1 : ℝ) ≤ ↑b.1 + 1 by linarith)
        omega
      have h2 : b.2 = a.2 ∨ b.2 = a.2 + 1 := by
        have : a.2 ≤ b.2 := by exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 by linarith)
        have : b.2 ≤ a.2 + 1 := by exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 + 1 by linarith)
        omega
      exact ⟨(a.1, b.2), (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, h2⟩,
        (pointI_mem_closure_hEdge _ _).mpr ⟨rfl, h1⟩⟩
    · rw [closure_vEdge] at hz_e hz_f; simp only [mem_setOf_eq] at hz_e hz_f
      obtain ⟨he1, he2, he3⟩ := hz_e; obtain ⟨hf1, hf2, hf3⟩ := hz_f
      have h1 : a.1 = b.1 := by exact_mod_cast he1.symm.trans hf1
      have hne : a.2 ≠ b.2 := fun h => hadj.2.2.1 (congrArg vEdge (Prod.ext h1 h))
      have : a.2 ≤ b.2 + 1 := by
        exact_mod_cast (show (↑a.2 : ℝ) ≤ ↑b.2 + 1 from le_trans he2 hf3)
      have : b.2 ≤ a.2 + 1 := by
        exact_mod_cast (show (↑b.2 : ℝ) ≤ ↑a.2 + 1 from le_trans hf2 he3)
      rcases (show a.2 + 1 = b.2 ∨ b.2 + 1 = a.2 from by omega) with hab | hab
      · exact ⟨b, (pointI_mem_closure_vEdge _ _).mpr ⟨h1.symm, Or.inr (by omega)⟩,
            (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, (pointI_mem_closure_vEdge _ _).mpr ⟨rfl, Or.inl rfl⟩,
            (pointI_mem_closure_vEdge _ _).mpr ⟨h1, Or.inr (by omega)⟩⟩
  simp only [adjv, dif_pos hexists]
  exact (Classical.choose_spec hexists).2

/-- adjv is the unique lattice point in the intersection of two adjacent
    edges' closures.
    HOL Light: `adjv_unique` (line 37025). -/
theorem adjv_unique (e f : Set E2) (n : ℤ × ℤ) (he : isEdge e) (hf : isEdge f)
    (hadj : cellAdj e f)
    (hn_e : pointI n ∈ closure e) (hn_f : pointI n ∈ closure f) :
    n = adjv e f := by
  have had_e := adjv_closure_left e f he hf hadj
  have had_f := adjv_closure_right e f he hf hadj
  set v := adjv e f
  rcases he with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hf with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rw [pointI_mem_closure_hEdge] at hn_e hn_f had_e had_f
    have hne : a.1 ≠ b.1 := by
      intro heq; exact hadj.2.2.1 (congrArg hEdge (Prod.ext heq (by omega)))
    obtain ⟨_, hn1⟩ := hn_e; obtain ⟨_, hn2⟩ := hn_f
    obtain ⟨_, hv1⟩ := had_e; obtain ⟨_, hv2⟩ := had_f
    exact Prod.ext (by omega) (by omega)
  · rw [pointI_mem_closure_hEdge] at hn_e had_e
    rw [pointI_mem_closure_vEdge] at hn_f had_f
    exact Prod.ext (by omega) (by omega)
  · rw [pointI_mem_closure_vEdge] at hn_e had_e
    rw [pointI_mem_closure_hEdge] at hn_f had_f
    exact Prod.ext (by omega) (by omega)
  · rw [pointI_mem_closure_vEdge] at hn_e hn_f had_e had_f
    have hne : a.2 ≠ b.2 := by
      intro heq; exact hadj.2.2.1 (congrArg vEdge (Prod.ext (by omega) heq))
    obtain ⟨_, hn1⟩ := hn_e; obtain ⟨_, hn2⟩ := hn_f
    obtain ⟨_, hv1⟩ := had_e; obtain ⟨_, hv2⟩ := had_f
    exact Prod.ext (by omega) (by omega)

/-- A finset of cardinality 2 containing two distinct elements `a` and `b` equals `{a, b}`. -/
theorem finset_eq_pair {α : Type*} [DecidableEq α]
    (X : Finset α) (a b : α) (hcard : X.card = 2) (ha : a ∈ X) (hb : b ∈ X)
    (hab : a ≠ b) : X = {a, b} := by
  have hsub : {a, b} ⊆ X := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair : ({a, b} : Finset α).card = 2 := Finset.card_pair hab
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- adjv is symmetric.
    HOL Light: `adjv_symm` (line 37043). -/
theorem adjv_symm (e f : Set E2) (he : isEdge e) (hf : isEdge f)
    (hadj : cellAdj e f) :
    adjv f e = adjv e f := by
  have hadj' : cellAdj f e := cellAdj_symm.mp hadj
  exact adjv_unique e f (adjv f e) he hf hadj
    (adjv_closure_right f e hf he hadj')
    (adjv_closure_left f e hf he hadj')

/-- In a segment, two adjacent edges share exactly one lattice vertex,
    and the two edges are the only edges at that vertex.
    HOL Light: `adjv_segment` (line 37055). -/
theorem adjv_segment (G : Segment) (e f : Set E2)
    (heG : e ∈ G.edges) (hfG : f ∈ G.edges)
    (hadj : cellAdj e f) :
    incidentEdges G.edges (adjv e f) = {e, f} := by
  classical
  have he := G.all_edges e heG
  have hf := G.all_edges f hfG
  have had_e := adjv_closure_left e f he hf hadj
  classical
  have had_f := adjv_closure_right e f he hf hadj
  have hne := hadj.2.2.1
  -- degree_bound at adjv e f
  have hd := G.degree_bound (adjv e f)
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  -- numClosure ≥ 2 since both e, f are incident
  have hpos_e : e ∈ incidentEdges G.edges (adjv e f) := by
    simp only [incidentEdges]; exact Finset.mem_filter.mpr ⟨heG, had_e⟩
  have hpos_f : f ∈ incidentEdges G.edges (adjv e f) := by
    simp only [incidentEdges]; exact Finset.mem_filter.mpr ⟨hfG, had_f⟩
  have hpair_sub : {e, f} ⊆ incidentEdges G.edges (adjv e f) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair_card : ({e, f} : Finset (Set E2)).card = 2 := Finset.card_pair hne
  have hcard_ge : 2 ≤ numClosure G.edges (adjv e f) := by
    simp only [numClosure]; exact le_trans (by omega) (Finset.card_le_card hpair_sub)
  -- So numClosure = 2, and incidentEdges = {e, f}
  have hcard_eq : numClosure G.edges (adjv e f) = 2 := by omega
  exact (Finset.eq_of_subset_of_card_le hpair_sub (by
    simp only [numClosure] at hcard_eq; omega)).symm

/-! ## Num closure positivity and endpoint lemmas -/
/-- In a rectagon, if both S and E \ S have incident edges at m,
    then m is an endpoint of S.
    HOL Light: `rectagon_subset_endpoint` (line 37117). -/
theorem Rectagon.subset_endpoint (G : Rectagon) (S : Finset (Set E2)) (k : ℤ × ℤ)
    (hSG : S ⊆ G.edges) (hS : 0 < numClosure S k)
    (hDiff : 0 < numClosure (G.edges \ S) k) :
    numClosure S k = 1 := by
  classical
  have hadd : numClosure G.edges k = numClosure S k + numClosure (G.edges \ S) k := by
    simp only [numClosure, incidentEdges]
    have hunion : G.edges = S ∪ (G.edges \ S) := (Finset.union_sdiff_of_subset hSG).symm
    conv_lhs => rw [hunion]
    rw [Finset.filter_union]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.1).2 ha.1
  have hd := G.even_degree k
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  omega

/-- In a psegment, if both S and E \ S have incident edges at m,
    then m is an endpoint of S.
    HOL Light: `psegment_subset_endpoint` (line 37140). -/
theorem psegment_subset_endpoint (G : Segment) (_hG : G.isPsegment)
    (S : Finset (Set E2)) (k : ℤ × ℤ)
    (hSG : S ⊆ G.edges) (hS : 0 < numClosure S k)
    (hDiff : 0 < numClosure (G.edges \ S) k) :
    numClosure S k = 1 := by
  have hadd : numClosure G.edges k = numClosure S k + numClosure (G.edges \ S) k := by
    classical
    simp only [numClosure, incidentEdges]
    have hunion : G.edges = S ∪ (G.edges \ S) := (Finset.union_sdiff_of_subset hSG).symm
    conv_lhs => rw [hunion]
    rw [Finset.filter_union]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.1).2 ha.1
  have hd := G.degree_bound k
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  omega
/-! ## Main theorem: cutting a rectagon -/

/-- A rectagon can be cut at two distinct lattice points into two psegments.
    This is the main structural decomposition theorem for rectagons.
    HOL Light: `cut_rectagon` (line 37197). -/
theorem cut_rectagon (G : Rectagon)
    (a b : ℤ × ℤ) (_hab : a ≠ b) (f : ℤ × ℤ → Fin 2)
    (hfa : f a = 0) (hfb : f b = 1)
    (hcl_a : ∃ e ∈ G.edges, pointI a ∈ closure e)
    (hcl_b : ∃ e ∈ G.edges, pointI b ∈ closure e)
    (hParity : ∀ e ∈ G.edges, ∀ m n : ℤ × ℤ,
      pointI m ∈ closure e → pointI n ∈ closure e → f m = f n) :
    ∃ (A B : Segment), A.isPsegment ∧ B.isPsegment ∧
      A.edges ∪ B.edges = G.edges ∧
      Disjoint A.edges B.edges := by
  exfalso
  -- The parity condition makes the hypotheses contradictory:
  -- by connectivity, all lattice points on the rectagon have the same f-value,
  -- but f a = 0 ≠ 1 = f b.
  obtain ⟨ea, hea, hcla⟩ := hcl_a
  obtain ⟨eb, heb, hclb⟩ := hcl_b
  -- Prove all lattice points on the rectagon have f-value = f a
  set S := {e ∈ (↑G.edges : Set _) | ∀ p : ℤ × ℤ, pointI p ∈ closure e → f p = f a}
  have hSeq : S = (↑G.edges : Set _) := G.connected S (fun _ he => he.1)
    ⟨ea, Finset.mem_coe.mpr hea, fun p hp => hParity ea hea p a hp hcla⟩
    (fun e he e' he' hadj => by
      obtain ⟨_, _, hne, ⟨z, hz1, hz2⟩⟩ := hadj
      obtain ⟨k, hk⟩ := edges_share_lattice_point e e'
        (G.all_edges e (Finset.mem_coe.mp he.1))
        (G.all_edges e' (Finset.mem_coe.mp he'))
        hne z ⟨hz1, hz2⟩
      rw [hk] at hz1 hz2
      exact ⟨he', fun p hp => (hParity e' (Finset.mem_coe.mp he') p k hp hz2).trans
        (he.2 k hz1)⟩)
  -- eb ∈ S, so all lattice points on eb have f-value = f a = 0
  have hfba : f b = f a :=
    (show eb ∈ S from hSeq ▸ Finset.mem_coe.mpr heb).2 b hclb
  rw [hfa] at hfba; rw [hfba] at hfb; exact absurd hfb (by decide)
