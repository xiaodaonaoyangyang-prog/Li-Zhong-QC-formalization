/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionB_CellTopology

/-!
# Section C: Rectagons and Segments
## HOL Light: Section C (Lines 3554–4783)

The fundamental combinatorial curve objects on the integer grid: rectagons
(grid analogs of simple closed curves), segments (grid analogs of arcs),
and psegments (proper segments with exactly two endpoints).

### Key HOL Light definitions
- `rectagon` (~3562): Finite nonempty connected set of edges, every lattice
  point has 0 or 2 incident edges
- `segment` (~3570): Like rectagon but allows 0, 1, or 2 incident edges
- `psegment` (~3578): Segment that is not a rectagon (has exactly 2 endpoints)
- `endpoint` (~3591), `midpoint` (~3594): Lattice points with 1 or 2
  incident edges
- `other_end` (~4290): Given one endpoint of a psegment, the other endpoint
-/

open Set Topology

noncomputable section

/-! ## numClosure helpers for singleton edge sets -/

/-- For a singleton edge set, numClosure is at most 1. -/
private theorem numClosure_singleton_le_one (e : Set E2) (m : ℤ × ℤ) :
    numClosure {e} m ≤ 1 := by
  open Classical in
  unfold numClosure incidentEdges
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _))
    (by simp)

/-- numClosure of a singleton is 1 iff the lattice point is in the
    closure. -/
private theorem numClosure_singleton_eq_one (e : Set E2) (m : ℤ × ℤ) :
    numClosure {e} m = 1 ↔ pointI m ∈ closure e := by
  open Classical in
  unfold numClosure incidentEdges
  constructor
  · intro h; by_contra hne
    have : @Finset.filter _ (fun e' => pointI m ∈ closure e')
        (Classical.decPred _) {e} = ∅ := by
      rw [Finset.filter_singleton, if_neg hne]
    rw [this] at h; simp at h
  · intro h
    have : @Finset.filter _ (fun e' => pointI m ∈ closure e')
        (Classical.decPred _) {e} = {e} := by
      rw [Finset.filter_singleton, if_pos h]
    rw [this]; simp

/-! ## Rectagons -/

/-- A rectagon is a finite, nonempty, connected set of edges where every
    lattice point has 0 or 2 incident edges from the set.
    This is the grid analog of a simple closed curve.
    HOL Light: `rectagon` (line 3562). -/
structure Rectagon where
  edges : Finset (Set E2)
  nonempty : edges.Nonempty
  all_edges : ∀ e ∈ edges, isEdge e
  even_degree : ∀ m : ℤ × ℤ,
    numClosure edges m ∈ ({0, 2} : Set ℕ)
  connected : ∀ S : Set (Set E2), S ⊆ ↑edges → S.Nonempty →
    (∀ C ∈ S, ∀ C' ∈ (↑edges : Set (Set E2)), cellAdj C C' → C' ∈ S) →
    S = ↑edges

/-- A lattice point is a midpoint of a rectagon if it has exactly 2
    incident edges. -/
def Rectagon.isMidpoint (G : Rectagon) (m : ℤ × ℤ) : Prop :=
  numClosure G.edges m = 2

/-- Every lattice point on a rectagon has degree 0 or 2.
    HOL Light: follows from `rectagon` definition (line 3562). -/
theorem Rectagon.degree_zero_or_midpoint (G : Rectagon) (m : ℤ × ℤ) :
    numClosure G.edges m = 0 ∨ G.isMidpoint m := by
  have h := G.even_degree m
  simp only [Rectagon.isMidpoint, mem_insert_iff, mem_singleton_iff] at h ⊢
  exact h

/-! ## Segments -/

/-- A segment is like a rectagon but allows endpoints: every lattice point
    has 0, 1, or 2 incident edges.
    HOL Light: `segment` (line 3570). -/
structure Segment where
  edges : Finset (Set E2)
  nonempty : edges.Nonempty
  all_edges : ∀ e ∈ edges, isEdge e
  degree_bound : ∀ m : ℤ × ℤ,
    numClosure edges m ∈ ({0, 1, 2} : Set ℕ)
  connected : ∀ S : Set (Set E2), S ⊆ ↑edges → S.Nonempty →
    (∀ C ∈ S, ∀ C' ∈ (↑edges : Set (Set E2)), cellAdj C C' → C' ∈ S) →
    S = ↑edges

/-- An endpoint of a segment is a lattice point with exactly 1 incident edge.
    HOL Light: `endpoint` (line 3591). -/
def Segment.isEndpoint (G : Segment) (m : ℤ × ℤ) : Prop :=
  numClosure G.edges m = 1

/-- A midpoint of a segment is a lattice point with exactly 2 incident edges.
    HOL Light: `midpoint` (line 3594). -/
def Segment.isMidpoint (G : Segment) (m : ℤ × ℤ) : Prop :=
  numClosure G.edges m = 2

/-- A lattice point is "off" a segment if it has no incident edges. -/
def Segment.isOff (G : Segment) (m : ℤ × ℤ) : Prop :=
  numClosure G.edges m = 0

/-- Every lattice point is either off, an endpoint, or a midpoint.
    HOL Light: follows from `segment` definition (line 3570). -/
theorem Segment.trichotomy (G : Segment) (m : ℤ × ℤ) :
    G.isOff m ∨ G.isEndpoint m ∨ G.isMidpoint m := by
  have h := G.degree_bound m
  simp only [Segment.isOff, Segment.isEndpoint, Segment.isMidpoint,
    mem_insert_iff, mem_singleton_iff] at h ⊢
  rcases h with h | h | h <;> omega

/-! ## Psegments (proper segments) -/

/-- A psegment (proper segment) is a segment that is not a rectagon,
    i.e., it has exactly 2 endpoints.
    HOL Light: `psegment` (line 3578). -/
def Segment.isPsegment (G : Segment) : Prop :=
  ∃ a b : ℤ × ℤ, a ≠ b ∧ G.isEndpoint a ∧ G.isEndpoint b ∧
    ∀ m, G.isEndpoint m → m = a ∨ m = b

/-! ## numClosure monotonicity and basic properties -/

/-- Monotonicity of numClosure: if G ⊆ G' then
    numClosure G m ≤ numClosure G' m.
    HOL Light: `num_closure_mono` (line 3621). -/
theorem numClosure_mono {G G' : Finset (Set E2)} (h : G ⊆ G')
    (m : ℤ × ℤ) : numClosure G m ≤ numClosure G' m := by
  open Classical in
  unfold numClosure incidentEdges
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ h)

/-- numClosure = 1 iff there is exactly one incident edge (unique edge).
    HOL Light: `num_closure1` (line 4748). -/
theorem numClosure_eq_one_iff (G : Finset (Set E2)) (m : ℤ × ℤ) :
    numClosure G m = 1 ↔ ∃! e, e ∈ G ∧ pointI m ∈ closure e := by
  open Classical in
  unfold numClosure incidentEdges
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨e, he⟩
    have hemem := he ▸ Finset.mem_singleton_self e
    rw [Finset.mem_filter] at hemem
    exact ⟨e, hemem, fun e' ⟨he'm, he'cl⟩ => by
      have : e' ∈ @Finset.filter _ (fun e' => pointI m ∈ closure e')
          (Classical.decPred _) G := Finset.mem_filter.mpr ⟨he'm, he'cl⟩
      rw [he] at this; exact Finset.mem_singleton.mp this⟩
  · rintro ⟨e, ⟨hem, hecl⟩, huniq⟩
    refine ⟨e, ?_⟩
    ext e'
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2⟩; exact huniq e' ⟨h1, h2⟩
    · intro h; subst h; exact ⟨hem, hecl⟩

/-! ## Edge endpoint structure -/

/-- Every edge has exactly 2 lattice endpoints in its closure.
    For hEdge m: the endpoints are m and (m.1+1, m.2).
    For vEdge m: the endpoints are m and (m.1, m.2+1).
    HOL Light: `two_endpoint` (line 3700). -/
theorem edge_two_endpoints (e : Set E2) (he : isEdge e) :
    ∃ a b : ℤ × ℤ, a ≠ b ∧ pointI a ∈ closure e ∧
      pointI b ∈ closure e ∧
      ∀ m, pointI m ∈ closure e → m = a ∨ m = b := by
  rcases he with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · refine ⟨n, (n.1 + 1, n.2), ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (Prod.ext_iff.mp h).1 (by omega)
    · rw [pointI_mem_closure_hEdge]; exact ⟨rfl, Or.inl rfl⟩
    · rw [pointI_mem_closure_hEdge]; exact ⟨rfl, Or.inr rfl⟩
    · intro m hm; rw [pointI_mem_closure_hEdge] at hm
      obtain ⟨h2, h1⟩ := hm
      cases h1 with
      | inl h => left; exact Prod.ext h h2
      | inr h => right; exact Prod.ext h h2
  · refine ⟨n, (n.1, n.2 + 1), ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (Prod.ext_iff.mp h).2 (by omega)
    · rw [pointI_mem_closure_vEdge]; exact ⟨rfl, Or.inl rfl⟩
    · rw [pointI_mem_closure_vEdge]; exact ⟨rfl, Or.inr rfl⟩
    · intro m hm; rw [pointI_mem_closure_vEdge] at hm
      obtain ⟨h1, h2⟩ := hm
      cases h2 with
      | inl h => left; exact Prod.ext h1 h
      | inr h => right; exact Prod.ext h1 h

/-- An edge in a segment with a lattice point in its closure means that
    point is a midpoint or endpoint.
    HOL Light: `edge_midend` (line 3750). -/
theorem Segment.edge_midend (G : Segment) (e : Set E2) (m : ℤ × ℤ)
    (he : e ∈ G.edges) (hm : pointI m ∈ closure e) :
    G.isMidpoint m ∨ G.isEndpoint m := by
  have hd := G.degree_bound m
  simp only [mem_insert_iff, mem_singleton_iff, Segment.isMidpoint,
    Segment.isEndpoint] at hd ⊢
  have hge : numClosure G.edges m ≥ 1 := by
    open Classical in
    unfold numClosure incidentEdges
    exact Finset.one_le_card.mpr
      ⟨e, Finset.mem_filter.mpr ⟨he, hm⟩⟩
  omega

/-- At an endpoint, there is exactly one incident edge.
    HOL Light: `endpoint_edge` (line 3660). -/
theorem Segment.endpoint_unique_edge (G : Segment) (m : ℤ × ℤ)
    (hm : G.isEndpoint m) :
    ∃! e, e ∈ G.edges ∧ pointI m ∈ closure e := by
  rw [Segment.isEndpoint] at hm
  exact (numClosure_eq_one_iff G.edges m).mp hm

/-- A segment with an endpoint cannot have all degrees in {0, 2},
    so it is not a rectagon.
    HOL Light: `endpoint_psegment` (line 3635). -/
theorem Segment.endpoint_not_rectagon_degree (G : Segment) (m : ℤ × ℤ)
    (hm : G.isEndpoint m) :
    ¬(∀ m : ℤ × ℤ, numClosure G.edges m ∈ ({0, 2} : Set ℕ)) := by
  intro h
  have := h m
  simp only [mem_insert_iff, mem_singleton_iff] at this
  rw [Segment.isEndpoint] at hm; omega

/-! ## Single edge psegment -/

/-- A single edge forms a segment. -/
private def singleEdgeSegment (e : Set E2) (he : isEdge e) : Segment where
  edges := {e}
  nonempty := Finset.singleton_nonempty e
  all_edges := by simp [he]
  degree_bound := by
    intro m
    have h := numClosure_singleton_le_one e m
    simp only [mem_insert_iff, mem_singleton_iff]; omega
  connected := by
    intro S hS hSne _
    ext x
    constructor
    · intro hx
      have := hS hx
      simp only [Finset.coe_singleton, mem_singleton_iff] at this
      simp only [Finset.mem_coe, Finset.mem_singleton]; exact this
    · intro hx
      simp only [Finset.mem_coe, Finset.mem_singleton] at hx
      obtain ⟨y, hy⟩ := hSne
      have hys := hS hy
      simp only [Finset.coe_singleton, mem_singleton_iff] at hys
      rw [hx, ← hys]; exact hy

/-- A single edge forms a psegment.
    HOL Light: `psegment_edge` (line 4155). -/
theorem single_edge_isPsegment (e : Set E2) (he : isEdge e) :
    ∃ G : Segment, G.edges = {e} ∧ G.isPsegment := by
  refine ⟨singleEdgeSegment e he, rfl, ?_⟩
  have hedge : (singleEdgeSegment e he).edges = {e} := rfl
  rcases he with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · -- hEdge n: endpoints are n and (n.1 + 1, n.2)
    refine ⟨n, (n.1 + 1, n.2), ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (Prod.ext_iff.mp h).1 (by omega)
    · change numClosure {hEdge n} n = 1
      rw [numClosure_singleton_eq_one, pointI_mem_closure_hEdge]
      exact ⟨rfl, Or.inl rfl⟩
    · change numClosure {hEdge n} (n.1 + 1, n.2) = 1
      rw [numClosure_singleton_eq_one, pointI_mem_closure_hEdge]
      exact ⟨rfl, Or.inr rfl⟩
    · intro m hm
      change numClosure {hEdge n} m = 1 at hm
      rw [numClosure_singleton_eq_one, pointI_mem_closure_hEdge] at hm
      obtain ⟨h2, h1⟩ := hm
      cases h1 with
      | inl h => left; exact Prod.ext h h2
      | inr h => right; exact Prod.ext h h2
  · -- vEdge n: endpoints are n and (n.1, n.2 + 1)
    refine ⟨n, (n.1, n.2 + 1), ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (Prod.ext_iff.mp h).2 (by omega)
    · change numClosure {vEdge n} n = 1
      rw [numClosure_singleton_eq_one, pointI_mem_closure_vEdge]
      exact ⟨rfl, Or.inl rfl⟩
    · change numClosure {vEdge n} (n.1, n.2 + 1) = 1
      rw [numClosure_singleton_eq_one, pointI_mem_closure_vEdge]
      exact ⟨rfl, Or.inr rfl⟩
    · intro m hm
      change numClosure {vEdge n} m = 1 at hm
      rw [numClosure_singleton_eq_one, pointI_mem_closure_vEdge] at hm
      obtain ⟨h1, h2⟩ := hm
      cases h2 with
      | inl h => left; exact Prod.ext h1 h
      | inr h => right; exact Prod.ext h1 h

/-! ## Adjacency and midpoints -/

/-- Two distinct edges share at most a lattice point in their closures.
    HOL Light: `inter_lattice` (line 3800). -/
theorem edges_share_lattice_point (e e' : Set E2) (he : isEdge e) (he' : isEdge e')
    (hne : e ≠ e') (z : E2) (hz : z ∈ closure e ∩ closure e') :
    ∃ m : ℤ × ℤ, z = pointI m := by
  rcases he with ⟨n1, rfl⟩ | ⟨n1, rfl⟩ <;> rcases he' with ⟨n2, rfl⟩ | ⟨n2, rfl⟩
  · -- hEdge n1, hEdge n2
    rw [closure_hEdge, closure_hEdge] at hz
    simp only [mem_inter_iff, mem_setOf_eq] at hz
    obtain ⟨⟨h1a, h1b, h1c⟩, ⟨h2a, h2b, h2c⟩⟩ := hz
    have hneq : n1 ≠ n2 := fun h => hne (congrArg hEdge h)
    -- z 1 is an integer (= n1.2 = n2.2)
    -- z 0 ∈ [n1.1, n1.1+1] ∩ [n2.1, n2.1+1], and since n1 ≠ n2 with same y,
    -- z 0 must be at the boundary, hence an integer
    have hy : n1.2 = n2.2 := by exact_mod_cast h1c.symm.trans h2c
    have hxne : n1.1 ≠ n2.1 := fun h => hneq (Prod.ext h hy)
    -- z 0 is an integer: it must equal either n1.1, n1.1+1, n2.1, or n2.1+1
    -- Since intervals are [n.1, n.1+1], the intersection for different n is a single integer point
    have : ∃ k : ℤ, z 0 = ↑k := by
      rcases lt_or_gt_of_ne hxne with h | h
      · have hle : n1.1 + 1 ≤ n2.1 := by omega
        have h5 : (↑n2.1 : ℝ) ≤ z 0 := h2a
        have h6 : z 0 ≤ ↑n2.1 := by
          have : (↑(n1.1 + 1 : ℤ) : ℝ) ≤ ↑n2.1 := Int.cast_le.mpr hle
          push_cast at this ⊢; linarith
        exact ⟨n2.1, le_antisymm h6 h5⟩
      · have hle : n2.1 + 1 ≤ n1.1 := by omega
        have h5 : (↑n1.1 : ℝ) ≤ z 0 := h1a
        have h6 : z 0 ≤ ↑n1.1 := by
          have : (↑(n2.1 + 1 : ℤ) : ℝ) ≤ ↑n1.1 := Int.cast_le.mpr hle
          push_cast at this ⊢; linarith
        exact ⟨n1.1, le_antisymm h6 h5⟩
    obtain ⟨k, hk⟩ := this
    exact ⟨(k, n1.2), by
      simp only [pointI, point]; apply (WithLp.equiv 2 _).injective
      funext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, WithLp.equiv_apply,
          WithLp.equiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        [exact hk; exact h1c]⟩
  · -- hEdge n1, vEdge n2: z 1 = n1.2 (from hEdge), z 0 = n2.1 (from vEdge)
    rw [closure_hEdge, closure_vEdge] at hz
    simp only [mem_inter_iff, mem_setOf_eq] at hz
    obtain ⟨⟨_, _, h1c⟩, ⟨h2a, _, _⟩⟩ := hz
    exact ⟨(n2.1, n1.2), by
      simp only [pointI, point]; apply (WithLp.equiv 2 _).injective
      funext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, WithLp.equiv_apply,
          WithLp.equiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        [exact h2a; exact h1c]⟩
  · -- vEdge n1, hEdge n2
    rw [closure_vEdge, closure_hEdge] at hz
    simp only [mem_inter_iff, mem_setOf_eq] at hz
    obtain ⟨⟨h1a, _, _⟩, ⟨_, _, h2c⟩⟩ := hz
    exact ⟨(n1.1, n2.2), by
      simp only [pointI, point]; apply (WithLp.equiv 2 _).injective
      funext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, WithLp.equiv_apply,
          WithLp.equiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        [exact h1a; exact h2c]⟩
  · -- vEdge n1, vEdge n2
    rw [closure_vEdge, closure_vEdge] at hz
    simp only [mem_inter_iff, mem_setOf_eq] at hz
    obtain ⟨⟨h1a, h1b, h1c⟩, ⟨h2a, h2b, h2c⟩⟩ := hz
    have hneq : n1 ≠ n2 := fun h => hne (congrArg vEdge h)
    have hx : n1.1 = n2.1 := by exact_mod_cast h1a.symm.trans h2a
    have hyne : n1.2 ≠ n2.2 := fun h => hneq (Prod.ext hx h)
    have : ∃ k : ℤ, z 1 = ↑k := by
      rcases lt_or_gt_of_ne hyne with h | h
      · have hle : n1.2 + 1 ≤ n2.2 := by omega
        have h5 : (↑n2.2 : ℝ) ≤ z 1 := h2b
        have h6 : z 1 ≤ ↑n2.2 := by
          have : (↑(n1.2 + 1 : ℤ) : ℝ) ≤ ↑n2.2 := Int.cast_le.mpr hle
          push_cast at this ⊢; linarith
        exact ⟨n2.2, le_antisymm h6 h5⟩
      · have hle : n2.2 + 1 ≤ n1.2 := by omega
        have h5 : (↑n1.2 : ℝ) ≤ z 1 := h1b
        have h6 : z 1 ≤ ↑n1.2 := by
          have : (↑(n2.2 + 1 : ℤ) : ℝ) ≤ ↑n1.2 := Int.cast_le.mpr hle
          push_cast at this ⊢; linarith
        exact ⟨n1.2, le_antisymm h6 h5⟩
    obtain ⟨k, hk⟩ := this
    exact ⟨(n1.1, k), by
      simp only [pointI, point]; apply (WithLp.equiv 2 _).injective
      funext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, WithLp.equiv_apply,
          WithLp.equiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] <;>
        [exact h1a; exact hk]⟩

/-- Two distinct edges in a segment that share a closure point must meet at
    a midpoint.
    HOL Light: `inter_midpoint` (line 4070). -/
theorem Segment.inter_midpoint (G : Segment) (e e' : Set E2)
    (he : e ∈ G.edges) (he' : e' ∈ G.edges) (hne : e ≠ e')
    (m : ℤ × ℤ) (hm : pointI m ∈ closure e ∩ closure e') :
    G.isMidpoint m := by
  have hd := G.degree_bound m
  simp only [mem_insert_iff, mem_singleton_iff, Segment.isMidpoint] at hd ⊢
  open Classical in
  have hge : numClosure G.edges m ≥ 2 := by
    unfold numClosure incidentEdges
    have h1 : e ∈ Finset.filter (fun e => pointI m ∈ closure e) G.edges :=
      Finset.mem_filter.mpr ⟨he, hm.1⟩
    have h2 : e' ∈ Finset.filter (fun e => pointI m ∈ closure e) G.edges :=
      Finset.mem_filter.mpr ⟨he', hm.2⟩
    have : ({e, e'} : Finset (Set E2)) ⊆
        Finset.filter (fun e => pointI m ∈ closure e) G.edges := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc Finset.card (Finset.filter (fun e => pointI m ∈ closure e) G.edges)
        ≥ Finset.card {e, e'} := Finset.card_le_card this
      _ = 2 := by rw [Finset.card_pair hne]
  omega

/-- Midpoints and endpoints of a segment are disjoint.
    HOL Light: `mid_end_disj` (line 3597). -/
theorem Segment.mid_end_disjoint (G : Segment) (m : ℤ × ℤ) :
    ¬(G.isMidpoint m ∧ G.isEndpoint m) := by
  intro ⟨h1, h2⟩; rw [Segment.isMidpoint] at h1; rw [Segment.isEndpoint] at h2
  omega

/-- If edge e is in segment G and G has more than one edge, then e has a
    midpoint in G (a lattice point on e with degree 2).
    HOL Light: `midpoint_exists` (line 4130). -/
theorem Segment.midpoint_exists (G : Segment) (e : Set E2) (he : e ∈ G.edges)
    (hne : G.edges ≠ {e}) :
    ∃ m, pointI m ∈ closure e ∧ G.isMidpoint m := by
  by_contra hall
  push Not at hall
  -- Every lattice point on e is an endpoint, not a midpoint
  have h_ep : ∀ m, pointI m ∈ closure e → G.isEndpoint m := by
    intro m hm
    rcases G.edge_midend e m he hm with h | h
    · exact absurd h (hall m hm)
    · exact h
  -- Show {e} is a connectivity-closed subset of ↑G.edges
  have hset : ({e} : Set (Set E2)) ⊆ ↑G.edges := by
    simp [he]
  have hnonempty : ({e} : Set (Set E2)).Nonempty := ⟨e, rfl⟩
  have hclosed : ∀ C ∈ ({e} : Set (Set E2)), ∀ C' ∈ (↑G.edges : Set _),
      cellAdj C C' → C' ∈ ({e} : Set (Set E2)) := by
    intro C hC C' hC'mem hadj
    simp only [mem_singleton_iff] at hC
    rw [hC] at hadj
    simp only [Finset.mem_coe] at hC'mem
    -- e and C' are adjacent edges, so they share a closure point
    obtain ⟨_, _, hne', ⟨z, hz1, hz2⟩⟩ := hadj
    -- The shared point must be a lattice point
    obtain ⟨m, hm⟩ := edges_share_lattice_point e C'
      (G.all_edges e he) (G.all_edges C' hC'mem) hne' z ⟨hz1, hz2⟩
    subst hm
    -- m is in closure of e, so m is an endpoint
    have hep := h_ep m hz1
    -- But m is also in closure of C', so numClosure ≥ 2, contradicting endpoint (= 1)
    have hmid := G.inter_midpoint e C' he hC'mem hne' m ⟨hz1, hz2⟩
    exact absurd ⟨hmid, hep⟩ (Segment.mid_end_disjoint G m)
  have heq := G.connected ({e} : Set (Set E2)) hset hnonempty hclosed
  -- heq : {e} = ↑G.edges, need to derive G.edges = {e}
  apply absurd _ hne
  ext x; simp only [Finset.mem_singleton]
  constructor
  · intro hx
    exact mem_singleton_iff.mp (heq ▸ Finset.mem_coe.mpr hx)
  · intro hx; subst hx; exact he

/-! ## Deleting a terminal edge -/

/-- Deleting a terminal edge from a segment with more than one edge
    gives a segment.
    HOL Light: `segment_delete` (line 4357). -/
theorem Segment.segment_delete (G : Segment) (e : Set E2) (m : ℤ × ℤ)
    (he : e ∈ G.edges) (hm : G.isEndpoint m) (hcl : pointI m ∈ closure e)
    (hne : G.edges ≠ {e}) :
    ∃ G' : Segment, G'.edges = G.edges.erase e := by
  -- e has a midpoint m' (since G has >1 edge)
  obtain ⟨m', hm'cl, hm'mid⟩ := G.midpoint_exists e he hne
  have hmm' : m ≠ m' := by
    intro heq; rw [heq, Segment.isEndpoint] at hm
    rw [Segment.isMidpoint] at hm'mid; omega
  -- e has exactly 2 lattice points
  obtain ⟨a, b, hab, ha, hb, huniq⟩ := edge_two_endpoints e (G.all_edges e he)
  -- Any lattice point on e other than m must be m'
  have hm'_other : ∀ p, pointI p ∈ closure e → p ≠ m → p = m' := by
    intro p hp hpm
    have h1 := huniq p hp
    have h2 := huniq m hcl
    have h3 := huniq m' hm'cl
    -- p, m, m' all ∈ {a, b}, p ≠ m, m ≠ m' → p = m'
    rcases h1 with rfl | rfl
    · -- p = a
      rcases h3 with rfl | h3
      · -- m' = a = p, done
        rfl
      · -- m' = b; then m = b (else m = a = p, contradicting hpm)
        rcases h2 with rfl | rfl
        · exact absurd rfl hpm
        · exact absurd h3.symm hmm'
    · -- p = b
      rcases h3 with h3 | rfl
      · -- m' = a; then m = b (else m = a = m', contradicting hmm')
        rcases h2 with rfl | rfl
        · exact absurd h3.symm hmm'
        · exact absurd rfl hpm
      · -- m' = b = p, done
        rfl
  -- m' has degree 2: extract the pair {e, e'} from the filter
  open Classical in
  have hm'deg : (G.edges.filter (fun x => pointI m' ∈ closure x)).card = 2 := by
    rw [Segment.isMidpoint] at hm'mid; exact hm'mid
  obtain ⟨x, y, hxy, hfilt_eq⟩ := Finset.card_eq_two.mp hm'deg
  have he_filt : e ∈ ({x, y} : Finset _) := by
    rw [← hfilt_eq]; exact Finset.mem_filter.mpr ⟨he, hm'cl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at he_filt
  -- Extract e' as the other element of the pair
  obtain ⟨e', he'G, he'm', hee'⟩ : ∃ e', e' ∈ G.edges ∧
      pointI m' ∈ closure e' ∧ e' ≠ e := by
    rcases he_filt with rfl | rfl
    · have : y ∈ G.edges.filter (fun z => pointI m' ∈ closure z) := by
        rw [hfilt_eq]; simp
      exact ⟨y, (Finset.mem_filter.mp this).1, (Finset.mem_filter.mp this).2, hxy.symm⟩
    · have : x ∈ G.edges.filter (fun z => pointI m' ∈ closure z) := by
        rw [hfilt_eq]; simp
      exact ⟨x, (Finset.mem_filter.mp this).1, (Finset.mem_filter.mp this).2, hxy⟩
  -- Any edge in the m'-filter (other than e) is e'
  have h_filt_other : ∀ f, f ∈ G.edges → pointI m' ∈ closure f → f ≠ e → f = e' := by
    intro f hf hfm' hfe_f
    have hf_filt : f ∈ G.edges.filter (fun z => pointI m' ∈ closure z) :=
      Finset.mem_filter.mpr ⟨hf, hfm'⟩
    have he'_filt : e' ∈ G.edges.filter (fun z => pointI m' ∈ closure z) :=
      Finset.mem_filter.mpr ⟨he'G, he'm'⟩
    have he_filt' : e ∈ G.edges.filter (fun z => pointI m' ∈ closure z) :=
      Finset.mem_filter.mpr ⟨he, hm'cl⟩
    rw [hfilt_eq] at hf_filt he'_filt he_filt'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf_filt he_filt he'_filt he_filt'
    -- e, f, e' ∈ {x, y}, e ≠ f, e ≠ e' → f = e'
    -- Simple: e = x ∨ e = y, f = x ∨ f = y, e' = x ∨ e' = y
    -- If e = x: since e ≠ f, f = y; since e ≠ e', e' = y; so f = y = e'
    -- If e = y: since e ≠ f, f = x; since e ≠ e', e' = x; so f = x = e'
    have hfv : f = x ∨ f = y := hf_filt
    have hev : e = x ∨ e = y := he_filt
    have he'v : e' = x ∨ e' = y := he'_filt
    rcases hev with hev | hev
    · -- e = x: f ≠ x (since f ≠ e), so f = y; e' ≠ x, so e' = y
      have hfnx : f ≠ x := fun h => hfe_f (h.trans hev.symm)
      have he'nx : e' ≠ x := fun h => hee' (h.trans hev.symm)
      exact (hfv.resolve_left hfnx).trans (he'v.resolve_left he'nx).symm
    · -- e = y: f ≠ y, so f = x; e' ≠ y, so e' = x
      have hfny : f ≠ y := fun h => hfe_f (h.trans hev.symm)
      have he'ny : e' ≠ y := fun h => hee' (h.trans hev.symm)
      exact (hfv.resolve_right hfny).trans (he'v.resolve_right he'ny).symm
  -- Key: any edge adjacent to e must be e' (unique neighbor)
  have h_unique_adj : ∀ f, f ∈ G.edges → cellAdj e f → f = e' := by
    intro f hf hadj
    obtain ⟨_, _, hfe, ⟨z, hz1, hz2⟩⟩ := hadj
    obtain ⟨p, hp⟩ := edges_share_lattice_point e f
      (G.all_edges e he) (G.all_edges f hf) hfe z ⟨hz1, hz2⟩
    subst hp
    by_cases hpm : p = m
    · -- p = m: f incident to endpoint m, but e is unique edge at m → f = e, contradiction
      have huniq_e := (numClosure_eq_one_iff G.edges m).mp
        (by rwa [Segment.isEndpoint] at hm)
      obtain ⟨u, ⟨huG, hucl⟩, huniq_u⟩ := huniq_e
      have heu := huniq_u e ⟨he, hcl⟩
      have hpm_hz2 : pointI m ∈ closure f := hpm ▸ hz2
      have hfu := huniq_u f ⟨hf, hpm_hz2⟩
      exact absurd (heu.trans hfu.symm) hfe
    · -- p ≠ m: then p = m', so f is in the m'-filter
      have hpm' := hm'_other p hz1 hpm
      have hz2' : pointI m' ∈ closure f := hpm' ▸ hz2
      exact h_filt_other f hf hz2' hfe.symm
  -- Construct the new segment
  have h_er_ne : (G.edges.erase e).Nonempty :=
    ⟨e', Finset.mem_erase.mpr ⟨hee', he'G⟩⟩
  refine ⟨⟨G.edges.erase e, h_er_ne, ?_, ?_, ?_⟩, rfl⟩
  -- all_edges
  · exact fun f hf => G.all_edges f (Finset.mem_of_mem_erase hf)
  -- degree_bound
  · intro p
    have h1 := numClosure_mono (Finset.erase_subset e G.edges) p
    have h2 := G.degree_bound p
    simp only [mem_insert_iff, mem_singleton_iff] at h2 ⊢; omega
  -- connected
  · intro S hS hSne hSclosed
    by_cases he'S : e' ∈ S
    · -- Case: e' ∈ S → insert e S is connectivity-closed in G
      have hIS_sub : insert e S ⊆ ↑G.edges := by
        intro x hx; rcases hx with rfl | hx
        · exact Finset.mem_coe.mpr he
        · exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp (hS hx)))
      have hISclosed : ∀ C ∈ insert e S, ∀ C' ∈ (↑G.edges : Set _),
          cellAdj C C' → C' ∈ insert e S := by
        intro C hC C' hC'mem hadj
        rcases hC with rfl | hC
        · -- C = e: only neighbor is e', which is in S
          have := h_unique_adj C' (Finset.mem_coe.mp hC'mem) hadj
          exact Or.inr (this ▸ he'S)
        · by_cases hC'e : C' = e
          · exact hC'e ▸ Or.inl rfl
          · have hCer : C ∈ (↑(G.edges.erase e) : Set _) := hS hC
            have hC'er : C' ∈ (↑(G.edges.erase e) : Set _) :=
              Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hC'e, Finset.mem_coe.mp hC'mem⟩)
            exact Or.inr (hSclosed C hC C' hC'er hadj)
      have heq := G.connected (insert e S) hIS_sub ⟨e, Or.inl rfl⟩ hISclosed
      -- insert e S = ↑G.edges → S = ↑(G.edges.erase e)
      ext x; constructor
      · exact fun hx => hS hx
      · intro hx
        have hxer := Finset.mem_coe.mp hx
        have hxG : x ∈ (↑G.edges : Set _) := Finset.mem_coe.mpr (Finset.mem_of_mem_erase hxer)
        have hxIns : x ∈ insert e S := heq ▸ hxG
        rcases hxIns with rfl | h
        · exact absurd (Finset.mem_erase.mp hxer).1 (not_not.mpr rfl)
        · exact h
    · -- Case: e' ∉ S → S is connectivity-closed in G directly
      have hSG : S ⊆ ↑G.edges := fun x hx =>
        Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp (hS hx)))
      have hSclosedG : ∀ C ∈ S, ∀ C' ∈ (↑G.edges : Set _), cellAdj C C' → C' ∈ S := by
        intro C hC C' hC'mem hadj
        by_cases hC'e : C' = e
        · -- C' = e → C adj to e → C = e' ∉ S, contradiction
          exfalso
          have : C = e' := h_unique_adj C (Finset.mem_coe.mp (hSG hC))
            ((cellAdj_symm (X := C) (Y := e)).mp (hC'e ▸ hadj))
          exact he'S (this ▸ hC)
        · have hCer : C ∈ (↑(G.edges.erase e) : Set _) := hS hC
          have hC'er : C' ∈ (↑(G.edges.erase e) : Set _) :=
            Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hC'e, Finset.mem_coe.mp hC'mem⟩)
          exact hSclosed C hC C' hC'er hadj
      exfalso
      have heq := G.connected S hSG hSne hSclosedG
      have : e ∈ S := heq ▸ Finset.mem_coe.mpr he
      have : e ∉ (↑(G.edges.erase e) : Set _) := by
        simp
      exact this (hS ‹e ∈ S›)

/-! ## Endpoint count (hard theorem — requires structural induction) -/

/-- A segment either has no endpoints (i.e., it's a rectagon) or it has
    exactly two endpoints (i.e., it's a psegment).
    HOL Light: `endpoint_size2` (line 4411) + `rectagon_endpoint` (line 3610). -/
theorem Segment.endpoint_count (G : Segment) :
    (∀ m, ¬G.isEndpoint m) ∨ G.isPsegment := by
  open Classical in
  by_cases h : ∃ m, G.isEndpoint m
  · right; obtain ⟨m₀, hm₀⟩ := h
    suffices hs : ∀ n, ∀ G : Segment, G.edges.card = n →
        (∃ m, G.isEndpoint m) → G.isPsegment from
      hs G.edges.card G rfl ⟨m₀, hm₀⟩
    intro n; refine Nat.strong_induction_on n ?_
    intro n ih G hn ⟨m, hm⟩
    -- Get unique edge e at endpoint m
    obtain ⟨e, ⟨heG, hecl⟩, huniq⟩ := (numClosure_eq_one_iff G.edges m).mp
      (by rwa [Segment.isEndpoint] at hm)
    -- Single edge case
    by_cases hne : G.edges = {e}
    · -- G has exactly one edge: isPsegment
      obtain ⟨G', hG'eq, hG'ps⟩ := single_edge_isPsegment e (G.all_edges e heG)
      -- G and G' have the same edges
      have : G.edges = G'.edges := by rw [hG'eq, hne]
      -- Transfer isPsegment: the endpoints are the same because numClosure is the same
      unfold Segment.isPsegment at hG'ps ⊢
      obtain ⟨a, b, hab, ha, hb, huniq'⟩ := hG'ps
      refine ⟨a, b, hab, ?_, ?_, ?_⟩
      · rwa [Segment.isEndpoint, ← this] at ha
      · rwa [Segment.isEndpoint, ← this] at hb
      · intro p hp; exact huniq' p (by rwa [Segment.isEndpoint, this] at hp)
    · -- G has >1 edge: delete terminal edge e
      obtain ⟨G', hG'eq⟩ := G.segment_delete e m heG hm hecl hne
      obtain ⟨m', hm'cl, hm'mid⟩ := G.midpoint_exists e heG hne
      have hmm' : m ≠ m' := by
        intro heq; simp only [Segment.isEndpoint, Segment.isMidpoint] at hm hm'mid
        rw [heq] at hm; omega
      obtain ⟨a, b, hab, ha, hb, hlp⟩ := edge_two_endpoints e (G.all_edges e heG)
      -- Helper: incidentEdges commutes with erase for non-incident points
      have ie_erase_noninc : ∀ p, pointI p ∉ closure e →
          incidentEdges (G.edges.erase e) p = incidentEdges G.edges p := by
        intro p hpe
        simp only [incidentEdges]
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨⟨_, hx⟩, hcl'⟩ => ⟨hx, hcl'⟩,
          fun ⟨hx, hcl'⟩ => ⟨⟨fun h => hpe (h ▸ hcl'), hx⟩, hcl'⟩⟩
      -- Helper: incidentEdges commutes with erase for incident points
      have ie_erase_inc : ∀ p, pointI p ∈ closure e →
          incidentEdges (G.edges.erase e) p = (incidentEdges G.edges p).erase e := by
        intro p hp
        simp only [incidentEdges]
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      -- numClosure transfer
      have nc_noninc : ∀ p, pointI p ∉ closure e →
          numClosure (G.edges.erase e) p = numClosure G.edges p := by
        intro p hpe; simp only [numClosure, ie_erase_noninc p hpe]
      have nc_inc : ∀ p, pointI p ∈ closure e →
          numClosure (G.edges.erase e) p = numClosure G.edges p - 1 := by
        intro p hp; simp only [numClosure, ie_erase_inc p hp]
        exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨heG, hp⟩)
      -- m' is an endpoint of G' (degree drops from 2 to 1)
      have hm'_G' : G'.isEndpoint m' := by
        simp only [Segment.isEndpoint, hG'eq, nc_inc m' hm'cl]
        simp only [Segment.isMidpoint] at hm'mid; omega
      -- G' has fewer edges
      have hG'card : G'.edges.card < n := by
        rw [hG'eq, ← hn]; exact Finset.card_erase_lt_of_mem heG
      -- IH gives G' is a psegment
      have hG'ps := ih G'.edges.card hG'card G' rfl ⟨m', hm'_G'⟩
      obtain ⟨a', b', hab', ha', hb', huniq'⟩ := hG'ps
      -- m is not an endpoint of G' (degree drops from 1 to 0)
      have hm_off_G' : ¬G'.isEndpoint m := by
        simp only [Segment.isEndpoint, hG'eq, nc_inc m hecl]
        simp only [Segment.isEndpoint] at hm; omega
      -- Only m and m' are lattice points on e
      have on_e_eq : ∀ p, pointI p ∈ closure e → p = m ∨ p = m' := by
        intro p hp
        have hp_ab := hlp p hp
        have hm_ab := hlp m hecl
        have hm'_ab := hlp m' hm'cl
        -- p, m, m' ∈ {a, b}, m ≠ m' → p ∈ {m, m'}
        rcases hp_ab with rfl | rfl <;> rcases hm_ab with hm_eq | hm_eq <;>
          rcases hm'_ab with hm'_eq | hm'_eq
        -- 8 branches: (p=a|b) × (m=a|b) × (m'=a|b)
        -- Contradictory when m=a,m'=a or m=b,m'=b (since m≠m')
        -- Solve p=m when p and m match, p=m' when p and m' match
        all_goals first
          | left; exact hm_eq.symm
          | right; exact hm'_eq.symm
          | (exfalso; exact hmm' (hm_eq.trans hm'_eq.symm))
      -- Find the "other" endpoint m'' of G' (not m')
      obtain ⟨m'', hm''_G', hm''_ne_m'⟩ : ∃ m'', G'.isEndpoint m'' ∧ m'' ≠ m' := by
        rcases huniq' m' hm'_G' with rfl | rfl
        · exact ⟨b', hb', hab'.symm⟩  -- hab' : m' ≠ b' after subst
        · exact ⟨a', ha', hab'⟩  -- hab' : a' ≠ m' after subst
      -- m'' is not on e
      have hm''_not_on_e : pointI m'' ∉ closure e := by
        intro h; rcases on_e_eq m'' h with rfl | rfl
        · exact hm_off_G' hm''_G'
        · exact hm''_ne_m' rfl
      -- m'' is also endpoint of G
      have hm''_G : G.isEndpoint m'' := by
        simp only [Segment.isEndpoint] at hm''_G' ⊢
        rw [hG'eq, nc_noninc m'' hm''_not_on_e] at hm''_G'; exact hm''_G'
      -- G's endpoints are exactly {m, m''}
      have hm_ne_m'' : m ≠ m'' := fun h => hm_off_G' (h ▸ hm''_G')
      refine ⟨m, m'', hm_ne_m'', hm, hm''_G, ?_⟩
      intro p hp
      by_cases hpe : pointI p ∈ closure e
      · rcases on_e_eq p hpe with rfl | rfl
        · left; rfl
        · -- p = m': midpoint of G, not endpoint
          exfalso; simp only [Segment.isEndpoint, Segment.isMidpoint] at hp hm'mid; omega
      · -- p not on e → endpoint of G' → in {a', b'}
        have hp_G' : G'.isEndpoint p := by
          simp only [Segment.isEndpoint] at hp ⊢
          rw [hG'eq, nc_noninc p hpe]; exact hp
        rcases huniq' p hp_G' with rfl | rfl
        · rcases huniq' m' hm'_G' with hm'eq | hm'eq
          · -- m' = a' = p → contradiction
            exfalso; rw [hm'eq] at hm'mid
            simp only [Segment.isEndpoint, Segment.isMidpoint] at hp hm'mid; omega
          · -- m' = b'. Since m'' is endpoint of G': m'' = a' or b'.
            -- m'' ≠ m' = b', so m'' = a' = p → right
            rcases huniq' m'' hm''_G' with h | h
            · right; exact h.symm
            · exfalso; exact hm''_ne_m' (h.trans hm'eq.symm)
        · rcases huniq' m' hm'_G' with hm'eq | hm'eq
          · -- m' = a'. m'' ≠ m' = a', so m'' = b' = p → right
            rcases huniq' m'' hm''_G' with h | h
            · exfalso; exact hm''_ne_m' (h.trans hm'eq.symm)
            · right; exact h.symm
          · -- m' = b' = p → contradiction
            exfalso; rw [hm'eq] at hm'mid
            simp only [Segment.isEndpoint, Segment.isMidpoint] at hp hm'mid; omega
  · push Not at h; exact Or.inl h

/-! ## Other end -/

/-- Given one endpoint of a psegment, there exists the other.
    HOL Light: `other_end` (line 4290). -/
theorem Segment.other_end_exists (G : Segment) (hG : G.isPsegment)
    (m : ℤ × ℤ) (hm : G.isEndpoint m) :
    ∃ m', m' ≠ m ∧ G.isEndpoint m' := by
  obtain ⟨a, b, hab, ha, hb, huniq⟩ := hG
  rcases huniq m hm with rfl | rfl
  · exact ⟨b, hab.symm, hb⟩
  · exact ⟨a, hab, ha⟩

/-- Every psegment has exactly two endpoints. -/
theorem Segment.psegment_two_endpoints (G : Segment) (hG : G.isPsegment) :
    ∃ a b : ℤ × ℤ, a ≠ b ∧ G.isEndpoint a ∧ G.isEndpoint b ∧
      ∀ m, G.isEndpoint m → m = a ∨ m = b := hG

/-! ## Conversion between Rectagon and Segment -/

/-- Every rectagon is also a segment (with no endpoints).
    HOL Light: `rectagon_segment` (line 3581). -/
def Rectagon.toSegment (G : Rectagon) : Segment where
  edges := G.edges
  nonempty := G.nonempty
  all_edges := G.all_edges
  degree_bound := by
    intro m
    have h := G.even_degree m
    simp only [mem_insert_iff, mem_singleton_iff] at h ⊢
    rcases h with h | h <;> omega
  connected := G.connected

/-- A rectagon viewed as a segment has no endpoints.
    HOL Light: `rectagon_endpoint` (line 3610). -/
theorem Rectagon.toSegment_no_endpoints (G : Rectagon) :
    ∀ m : ℤ × ℤ, ¬G.toSegment.isEndpoint m := by
  intro m h
  simp only [Segment.isEndpoint, Rectagon.toSegment] at h
  have hd := G.even_degree m
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  omega

/-! ## Union of edges (geometric realization) -/

/-- The geometric realization of a set of edges: the union of all edge
    sets. -/
def edgeUnion (G : Finset (Set E2)) : Set E2 := ⋃₀ ↑G

/-- The geometric realization of a rectagon. -/
def Rectagon.carrier (G : Rectagon) : Set E2 := edgeUnion G.edges

/-- The geometric realization of a segment. -/
def Segment.carrier (G : Segment) : Set E2 := edgeUnion G.edges

end
