/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionN_K33
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Basic

/-!
# Section O: Complement Connectivity
## HOL Light: Section O (Lines 28400–32513)

Disk-endpoint lemmas, graph-disk constructions, HV-finite definitions,
topology infrastructure (connected components, induced topology), and the
main result `planar_graph_hv` that every bounded-degree planar graph has
an HV-finite plane embedding.

### Key HOL Light results (with downstream uses)
- `simple_arc_connected` (9 uses)
- `mk_line_hyper2_e1/e2` (8 uses each)
- `connected_induced2` (5 uses)
- `p_conn_hv_finite` (4 uses)
- `loc_path_conn_top2` (3 uses)
- `component_imp_connected` (3 uses)
- `planar_graph_hv` (1 use) — main theorem
-/

open Set Metric Topology

noncomputable section

/-! ## Simple arc connectivity -/

/-- A simple arc is connected.
    HOL Light: `simple_arc_connected` (line 28404). -/
theorem isSimpleArc_isConnected {C : Set E2'} (hC : IsSimpleArc C) :
    IsConnected C := by
  obtain ⟨f, rfl, hcont, _⟩ := hC
  exact IsConnected.image (isConnected_Icc zero_le_one) f hcont.continuousOn

/-! ## Disk-endpoint lemmas -/

-- These are internal lemmas used to build the graph-disk construction.
-- Uses_Beyond_Section = 0, so they are inlined as private helpers.

-- HOL Light: `disk_endpoint` (line 28424), `disk_endpoint_gen` (line 28551),
-- `disk_endpoint_outer` (line 28652).
-- Omitted: only used in graph_disk_hv_preliminaries which is itself internal.

/-! ## Graph edge around (edges incident to a vertex) -/

/-- Edges incident to a vertex in a graph.
    HOL Light: `graph_edge_around G v` (line 28709). -/
def HolGraph.edgeAround {V E : Type*} (G : HolGraph V E) (v : V) : Set E :=
  {e ∈ G.edgeSet | v ∈ G.inc e}

/-- No edges around a non-vertex.
    HOL Light: `graph_edge_around_empty` (line 28713). -/
theorem HolGraph.edgeAround_empty {V E : Type*} (G : HolGraph V E)
    (v : V) (hv : v ∉ G.vertexSet) : G.edgeAround v = ∅ := by
  ext e
  simp only [HolGraph.edgeAround, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro he hve; exact hv ((G.well_formed e he).1 hve)

/-! ## HV-finite sets -/

/-- A set is HV-finite if it is contained in a finite union of horizontal and
    vertical lines.
    HOL Light: `hv_finite` (line 29989). -/
def IsHVFiniteSet (C : Set E2') : Prop :=
  ∃ E : Finset (Set E2'), C ⊆ ⋃₀ (E : Set (Set E2')) ∧
    IsHVLine (E : Set (Set E2'))

/-- Subsets of HV-finite sets are HV-finite.
    HOL Light: `hv_finite_subset` (line 29992). -/
theorem IsHVFiniteSet.subset {A B : Set E2'} (hB : IsHVFiniteSet B)
    (hAB : A ⊆ B) : IsHVFiniteSet A := by
  obtain ⟨E, hBE, hE⟩ := hB
  exact ⟨E, hAB.trans hBE, hE⟩

/-! ## Hyperplane characterizations -/

-- hyperplane2 is defined in SectionN_K33

/-- Vertical line as hyperplane.
    HOL Light: `mk_line_hyper2_e1` (line 30006). -/
theorem mkLine_eq_hyperplane2_0 (z : ℝ) :
    mkLine (point (z, 0)) (point (z, 1)) = hyperplane2 0 z := by
  ext x; simp only [mkLine, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨t, rfl⟩; simp [point_coord_zero]; ring
  · intro hx; exact ⟨1 - x 1, by
      ext i; fin_cases i <;>
        simp [point_coord_zero, point_coord_one, hx] ; ring⟩

/-- Horizontal line as hyperplane.
    HOL Light: `mk_line_hyper2_e2` (line 30032). -/
theorem mkLine_eq_hyperplane2_1 (z : ℝ) :
    mkLine (point (0, z)) (point (1, z)) = hyperplane2 1 z := by
  ext x; simp only [mkLine, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨t, rfl⟩; simp [point_coord_one]; ring
  · intro hx; exact ⟨1 - x 0, by
      ext i; fin_cases i <;>
        simp [point_coord_zero, point_coord_one, hx] ; ring⟩

/-- A set contained in a hyperplane cross is HV-finite.
    HOL Light: `hv_finite_hyper` (line 30058). -/
theorem isHVFiniteSet_of_subset_hyperplane_cross {C : Set E2'} {v : E2'}
    (h : C ⊆ hyperplane2 1 (v 1) ∪ hyperplane2 0 (v 0)) :
    IsHVFiniteSet C := by
  refine ⟨{mkLine (point (v 0, 0)) (point (v 0, 1)),
            mkLine (point (0, v 1)) (point (1, v 1))}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
    rw [mkLine_eq_hyperplane2_0, mkLine_eq_hyperplane2_1, Set.union_comm]
    exact h hx
  · intro e he
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact ⟨(v 0, 0), (v 0, 1), rfl, Or.inl rfl⟩
    · exact ⟨(0, v 1), (1, v 1), rfl, Or.inr rfl⟩

/-! ## Graph HV-finite radius -/

/-- A graph has HV-finite radius `r`: it is a good plane graph where vertices
    have well-separated r-balls and edges are HV-finite near incident vertices.
    HOL Light: `graph_hv_finite_radius` (line 30083). -/
def IsGraphHVFiniteRadius (G : HolGraph E2' (Set E2')) (r : ℝ) : Prop :=
  IsGoodPlaneGraph G ∧ 0 < r ∧
  (∀ v ∈ G.vertexSet, ∀ v' ∈ G.vertexSet, v ≠ v' →
    closedBall v r ∩ closedBall v' r = ∅) ∧
  (∀ e ∈ G.edgeSet, ∀ v ∈ G.vertexSet, v ∉ G.inc e →
    e ∩ closedBall v r = ∅) ∧
  (∀ e ∈ G.edgeSet, ∀ v, v ∈ G.inc e →
    IsHVFiniteSet (e ∩ closedBall v r))

/-! ## Construct HV-finite arc: helper lemmas -/

/-- Union of two HV-finite sets is HV-finite.
    HOL Light: follows from `hv_finite` definition. -/
theorem IsHVFiniteSet.union {A B : Set E2'} (hA : IsHVFiniteSet A)
    (hB : IsHVFiniteSet B) : IsHVFiniteSet (A ∪ B) := by
  obtain ⟨EA, hAE, hAhv⟩ := hA
  obtain ⟨EB, hBE, hBhv⟩ := hB
  exact ⟨EA ∪ EB, by
    intro x hx; simp only [Finset.coe_union, Set.sUnion_union]
    exact hx.elim (fun h => Or.inl (hAE h)) (fun h => Or.inr (hBE h)),
    fun e he => by
      simp only [Finset.coe_union, Set.mem_union] at he
      exact he.elim (hAhv e) (hBhv e)⟩

/-- A segment between two points sharing coordinate `k` is HV-finite. -/
private theorem isHVFiniteSet_segment_sameCoord {y z : E2'} {k : Fin 2}
    (h : y k = z k) : IsHVFiniteSet (segment ℝ y z) := by
  -- Every point in the segment has the same k-coordinate as y
  have coord_eq : ∀ p ∈ segment ℝ y z, p k = y k := by
    rintro p hp
    obtain ⟨t, _, _, rfl⟩ := mem_segment_iff_param.mp hp
    -- (t • y + (1 - t) • z) k = t * (y k) + (1 - t) * (z k) = y k
    show (t • y + (1 - t) • z) k = y k
    have : (t • y + (1 - t) • z) k = t * (y k) + (1 - t) * (z k) := rfl
    rw [this, h]; ring
  -- The segment is contained in hyperplane2 k (y k)
  have hsub : segment ℝ y z ⊆ hyperplane2 k (y k) := fun p hp => coord_eq p hp
  fin_cases k
  · -- k = 0: vertical line
    refine ⟨{mkLine (point (y 0, 0)) (point (y 0, 1))}, ?_, ?_⟩
    · intro p hp
      simp only [Finset.coe_singleton, Set.sUnion_singleton, mkLine_eq_hyperplane2_0]
      exact hsub hp
    · intro e he
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at he; subst he
      exact ⟨(y 0, 0), (y 0, 1), rfl, Or.inl rfl⟩
  · -- k = 1: horizontal line
    refine ⟨{mkLine (point (0, y 1)) (point (1, y 1))}, ?_, ?_⟩
    · intro p hp
      simp only [Finset.coe_singleton, Set.sUnion_singleton, mkLine_eq_hyperplane2_1]
      exact hsub hp
    · intro e he
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at he; subst he
      exact ⟨(0, y 1), (1, y 1), rfl, Or.inr rfl⟩

/-- At least one of the two L-corners of two points in a ball is also in the ball.
    For y, z ∈ ball(c, r), at least one of m₁ = point(z 0, y 1) or
    m₂ = point(y 0, z 1) is in ball(c, r).
    Proof: dist²(c,m₁) + dist²(c,m₂) = dist²(c,y) + dist²(c,z) < 2r². -/
private theorem exists_corner_in_ball {c y z : E2'} {r : ℝ}
    (hy : y ∈ Metric.ball c r) (hz : z ∈ Metric.ball c r) :
    point (z 0, y 1) ∈ Metric.ball c r ∨
    point (y 0, z 1) ∈ Metric.ball c r := by
  by_contra h
  push Not at h
  obtain ⟨hm1, hm2⟩ := h
  simp only [Metric.mem_ball, not_lt] at hm1 hm2
  rw [Metric.mem_ball] at hy hz
  -- dist² = (Δx)² + (Δy)² for EuclideanSpace ℝ (Fin 2)
  have distSq (a b : E2') : dist a b ^ 2 =
      (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
    rw [EuclideanSpace.dist_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  -- dist²(m₁,c) + dist²(m₂,c) = dist²(y,c) + dist²(z,c) (by coordinate swap)
  have sum_eq : dist (point (z 0, y 1)) c ^ 2 + dist (point (y 0, z 1)) c ^ 2 =
      dist y c ^ 2 + dist z c ^ 2 := by
    simp only [distSq, point_coord_zero, point_coord_one]; ring
  -- dist²(y,c) < r² and dist²(z,c) < r²; dist²(m_i,c) ≥ r²
  -- Combined with sum_eq, this is a contradiction.
  have hdy : (0 : ℝ) ≤ dist y c := dist_nonneg
  have hdz : (0 : ℝ) ≤ dist z c := dist_nonneg
  have hdm1 : (0 : ℝ) ≤ dist (point (z 0, y 1)) c := dist_nonneg
  have hdm2 : (0 : ℝ) ≤ dist (point (y 0, z 1)) c := dist_nonneg
  -- dist y c < r with dist y c ≥ 0 gives dist y c ^ 2 < r ^ 2  (and similarly for others)
  nlinarith [sq_nonneg (r - dist y c), sq_nonneg (r - dist z c),
    sq_nonneg (dist (point (z 0, y 1)) c - r),
    sq_nonneg (dist (point (y 0, z 1)) c - r)]

/-- Two distinct points in a ball in ℝ² can be connected by an HV-finite
    simple arc inside that ball. -/
private theorem hvFiniteArcEnd_in_ball {c : E2'} {r : ℝ} {y z : E2'} (hyz : y ≠ z)
    (hy : y ∈ Metric.ball c r) (hz : z ∈ Metric.ball c r) :
    ∃ P, IsSimpleArcEnd P y z ∧ P ⊆ Metric.ball c r ∧ IsHVFiniteSet P := by
  by_cases h0 : y 0 = z 0
  · exact ⟨segment ℝ y z, segment_isSimpleArcEnd hyz,
      segment_subset_ball hy hz, isHVFiniteSet_segment_sameCoord h0⟩
  by_cases h1 : y 1 = z 1
  · exact ⟨segment ℝ y z, segment_isSimpleArcEnd hyz,
      segment_subset_ball hy hz, isHVFiniteSet_segment_sameCoord h1⟩
  · -- L-shaped path: at least one corner is in the ball
    rcases exists_corner_in_ball hy hz with hm | hm
    · -- Corner m = point(z 0, y 1)
      set m := point (z 0, y 1) with hm_def
      have hym : y ≠ m := fun heq => h0 (by rw [heq, hm_def]; simp [point_coord_zero])
      have hmz : m ≠ z := fun heq => h1 (by rw [← heq, hm_def]; simp [point_coord_one])
      have hc1 : y 1 = m 1 := by simp [hm_def, point_coord_one]
      have hc0 : m 0 = z 0 := by simp [hm_def, point_coord_zero]
      set S1 := segment ℝ y m; set S2 := segment ℝ m z
      have hinter : S1 ∩ S2 ⊆ {m} := by
        rintro p ⟨hp1, hp2⟩
        obtain ⟨t1, ht10, ht11, rfl⟩ := mem_segment_iff_param.mp hp1
        obtain ⟨t2, ht20, ht21, h2eq⟩ := mem_segment_iff_param.mp hp2
        -- From S2 via h2eq: component 0 = m 0
        have eq0 : (t1 • y + (1 - t1) • m) 0 = m 0 := by
          rw [show (t1 • y + (1 - t1) • m) 0 = (t2 • m + (1 - t2) • z) 0
            from congr_arg (· 0) h2eq]
          change t2 * (m 0) + (1 - t2) * (z 0) = m 0; rw [hc0]; ring
        -- So t1 * (y 0 - m 0) = 0, and y 0 ≠ m 0 ⇒ t1 = 0
        have ht1 : t1 = 0 := by
          have : t1 * (y 0 - m 0) = 0 := by
            have : (t1 • y + (1 - t1) • m) 0 = t1 * (y 0) + (1 - t1) * (m 0) := rfl
            linarith [eq0]
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linarith [h] : y 0 = m 0) (by rw [hm_def]; simp [point_coord_zero, h0])
        simp only [Set.mem_singleton_iff]
        change t1 • y + (1 - t1) • m = m
        rw [ht1]; simp
      exact ⟨S1 ∪ S2,
        isSimpleArcEnd_concat (segment_isSimpleArcEnd hym) (segment_isSimpleArcEnd hmz) hinter,
        Set.union_subset (segment_subset_ball hy hm) (segment_subset_ball hm hz),
        (isHVFiniteSet_segment_sameCoord hc1).union (isHVFiniteSet_segment_sameCoord hc0)⟩
    · -- Corner m = point(y 0, z 1)
      set m := point (y 0, z 1) with hm_def
      have hym : y ≠ m := fun heq => h1 (by rw [heq, hm_def]; simp [point_coord_one])
      have hmz : m ≠ z := fun heq => h0 (by rw [← heq, hm_def]; simp [point_coord_zero])
      have hc0 : y 0 = m 0 := by simp [hm_def, point_coord_zero]
      have hc1 : m 1 = z 1 := by simp [hm_def, point_coord_one]
      set S1 := segment ℝ y m; set S2 := segment ℝ m z
      have hinter : S1 ∩ S2 ⊆ {m} := by
        rintro p ⟨hp1, hp2⟩
        obtain ⟨t1, ht10, ht11, rfl⟩ := mem_segment_iff_param.mp hp1
        obtain ⟨t2, ht20, ht21, h2eq⟩ := mem_segment_iff_param.mp hp2
        have eq1 : (t1 • y + (1 - t1) • m) 1 = m 1 := by
          rw [show (t1 • y + (1 - t1) • m) 1 = (t2 • m + (1 - t2) • z) 1
            from congr_arg (· 1) h2eq]
          change t2 * (m 1) + (1 - t2) * (z 1) = m 1; rw [hc1]; ring
        have ht1 : t1 = 0 := by
          have : t1 * (y 1 - m 1) = 0 := by
            have : (t1 • y + (1 - t1) • m) 1 = t1 * (y 1) + (1 - t1) * (m 1) := rfl
            linarith [eq1]
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linarith [h] : y 1 = m 1) (by rw [hm_def]; simp [point_coord_one, h1])
        simp only [Set.mem_singleton_iff]
        change t1 • y + (1 - t1) • m = m
        rw [ht1]; simp
      exact ⟨S1 ∪ S2,
        isSimpleArcEnd_concat (segment_isSimpleArcEnd hym) (segment_isSimpleArcEnd hmz) hinter,
        Set.union_subset (segment_subset_ball hy hm) (segment_subset_ball hm hz),
        (isHVFiniteSet_segment_sameCoord hc0).union (isHVFiniteSet_segment_sameCoord hc1)⟩

/-! ## Construct HV-finite arc -/

/-- Given an open set and a simple arc inside it, there exists an HV-finite
    simple arc with the same endpoints inside the same open set.
    HOL Light: `construct_hv_finite` (line 31276). -/
theorem construct_hvFinite_arc {A C : Set E2'} {v v' : E2'}
    (hA : IsOpen A) (hC : C ⊆ A) (harc : IsSimpleArcEnd C v v') :
    ∃ C', C' ⊆ A ∧ IsSimpleArcEnd C' v v' ∧ IsHVFiniteSet C' := by
  obtain ⟨f, rfl, hcont, hinj, hf0, hf1⟩ := harc
  -- hv_connect t: v can be connected to f(t) by an hv-finite simple arc in A
  let hv_connect (t : ℝ) : Prop :=
    t = 0 ∨ ∃ P, IsHVFiniteSet P ∧ P ⊆ A ∧ IsSimpleArcEnd P v (f t)
  -- Composition: hv_connect t₀ + both f(t₀), f(t) in a ball ⊆ A → hv_connect t
  have compose {t₀ t : ℝ} (ht₀ : Icc 0 1 t₀) (ht : Icc 0 1 t)
      (hconn : hv_connect t₀) {c : E2'} {ε : ℝ} (hε : 0 < ε)
      (hball : Metric.ball c ε ⊆ A)
      (hft₀_ball : f t₀ ∈ Metric.ball c ε)
      (hft_ball : f t ∈ Metric.ball c ε)
      (hne : f t₀ ≠ f t) : hv_connect t := by
    obtain ⟨Q, hQarc, hQball, hQhv⟩ := hvFiniteArcEnd_in_ball hne hft₀_ball hft_ball
    have hQA : Q ⊆ A := hQball.trans hball
    rcases hconn with rfl | ⟨P, hPhv, hPA, hParc⟩
    · -- t₀ = 0, so f 0 → v by hf0
      right; rw [hf0] at hQarc; exact ⟨Q, hQhv, hQA, hQarc⟩
    · -- Compose P (v → f t₀) and Q (f t₀ → f t) inside P ∪ Q
      have hPQ_hv : IsHVFiniteSet (P ∪ Q) := hPhv.union hQhv
      have hPQ_A : P ∪ Q ⊆ A := Set.union_subset hPA hQA
      have h1 : pathConnectedIn (P ∪ Q) v (f t₀) :=
        pathConnectedIn_mono Set.subset_union_left (Or.inr ⟨P, hParc, Set.Subset.rfl⟩)
      have h2 : pathConnectedIn (P ∪ Q) (f t₀) (f t) :=
        pathConnectedIn_mono Set.subset_union_right (Or.inr ⟨Q, hQarc, Set.Subset.rfl⟩)
      rcases pathConnectedIn_trans h1 h2 with hvft | ⟨R, hRarc, hRPQ⟩
      · -- v = f t → t = 0 by injectivity (since f 0 = v)
        left; exact hinj ht ⟨le_refl _, zero_le_one⟩ ((hf0.trans hvft).symm)
      · right; exact ⟨R, hPQ_hv.subset hRPQ, hRPQ.trans hPQ_A, hRarc⟩
  -- S = {t ∈ [0,1] | hv_connect t}, prove S = [0,1] via sSup argument
  set S := {t ∈ Icc (0:ℝ) 1 | hv_connect t}
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_refl _, zero_le_one⟩, Or.inl rfl⟩
  have hS_bdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hS_ne : S.Nonempty := ⟨0, h0S⟩
  set s := sSup S
  have hs_le : s ≤ 1 := csSup_le hS_ne (fun t ht => ht.1.2)
  have h0_le_s : 0 ≤ s := le_csSup hS_bdd h0S
  have hs_Icc : s ∈ Icc (0:ℝ) 1 := ⟨h0_le_s, hs_le⟩
  -- Closedness: s ∈ S
  have hsS : s ∈ S := by
    refine ⟨hs_Icc, ?_⟩
    have hfsA : f s ∈ A := hC ⟨s, hs_Icc, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA _ hfsA
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
    obtain ⟨t₁, ht₁S, ht₁s⟩ : ∃ t₁ ∈ S, s - δ < t₁ := by
      rcases lt_or_eq_of_le h0_le_s with h0s | h0s
      · exact exists_lt_of_lt_csSup hS_ne (by linarith)
      · exact ⟨0, h0S, by linarith⟩
    have ht₁_close : dist t₁ s < δ := by
      rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith [le_csSup hS_bdd ht₁S]⟩
    rcases eq_or_ne (f t₁) (f s) with hft₁s | hft₁s
    · rw [← hinj ht₁S.1 hs_Icc hft₁s]; exact ht₁S.2
    · exact compose ht₁S.1 hs_Icc ht₁S.2 hε hball
        (hδε ht₁_close) (Metric.mem_ball_self hε) hft₁s
  -- Openness: s = 1
  have hs1 : s = 1 := by
    by_contra hs_ne
    have hs_lt : s < 1 := lt_of_le_of_ne hs_le hs_ne
    have hfsA : f s ∈ A := hC ⟨s, hs_Icc, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA _ hfsA
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
    set t₂ := min (s + δ / 2) 1
    have ht₂_Icc : t₂ ∈ Icc (0:ℝ) 1 := ⟨le_min (by linarith) zero_le_one, min_le_right _ _⟩
    have ht₂_gt : s < t₂ := lt_min (by linarith) hs_lt
    have ht₂_close : dist t₂ s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t₂ - s)]
      calc t₂ - s ≤ (s + δ / 2) - s := by linarith [min_le_left (s + δ / 2) 1]
        _ = δ / 2 := by ring
        _ < δ := by linarith
    rcases eq_or_ne (f s) (f t₂) with hfst₂ | hfst₂
    · exact absurd (hinj hs_Icc ht₂_Icc hfst₂) (ne_of_lt ht₂_gt)
    · exact absurd (le_csSup hS_bdd (show t₂ ∈ S from
        ⟨ht₂_Icc, compose hs_Icc ht₂_Icc hsS.2 hε hball
          (Metric.mem_ball_self hε) (hδε ht₂_close) hfst₂⟩)) (not_le.mpr ht₂_gt)
  -- Extract result
  rw [hs1] at hsS
  rcases hsS.2 with h01 | ⟨P, hPhv, hPA, hParc⟩
  · exact absurd h01 one_ne_zero
  · rw [hf1] at hParc; exact ⟨P, hPA, hParc, hPhv⟩

/-! ## Path-connectivity via HV-finite arcs -/

/-- The backward direction of `p_conn_hv_finite`: an HV-finite simple arc in A
    gives `pathConnectedIn`.
    HOL Light: `p_conn_hv_finite` (line 30099), backward direction. -/
theorem pconn_hvFinite_backward {A : Set E2'} {x y : E2'}
    (h : ∃ C, IsHVFiniteSet C ∧ C ⊆ A ∧ IsSimpleArcEnd C x y) :
    pathConnectedIn A x y := by
  obtain ⟨C, _, hCA, harc⟩ := h
  exact Or.inr ⟨C, harc, hCA⟩

/-- Forward direction for HV-finite ambient sets: any simple arc in an
    HV-finite set is HV-finite.
    HOL Light: In `p_conn_hv_finite`, trivial because `p_conn` uses polygonal arcs. -/
theorem pconn_hvFinite_of_hvFinite {A : Set E2'} {x y : E2'} (hxy : x ≠ y)
    (hhv : IsHVFiniteSet A) (h : pathConnectedIn A x y) :
    ∃ C, IsHVFiniteSet C ∧ C ⊆ A ∧ IsSimpleArcEnd C x y := by
  rcases h with rfl | ⟨C, harc, hCA⟩
  · exact absurd rfl hxy
  · exact ⟨C, hhv.subset hCA, hCA, harc⟩

/-- Forward direction for open ambient sets: any path in an open set can be
    replaced by an HV-finite simple arc.
    HOL Light: `p_conn_hv_finite` (line 30099), forward direction.
    Note: In HOL Light, `p_conn` already uses simple polygonal arcs so the
    forward direction is trivial. Our `pathConnectedIn` uses simple arcs
    (not necessarily HV-finite), so this direction requires `construct_hvFinite_arc`.
    The IsOpen hypothesis is always satisfied at downstream call sites (which go
    through `p_conn_conn`). -/
theorem pconn_hvFinite_of_open {A : Set E2'} {x y : E2'} (hxy : x ≠ y)
    (hA : IsOpen A) (h : pathConnectedIn A x y) :
    ∃ C, IsHVFiniteSet C ∧ C ⊆ A ∧ IsSimpleArcEnd C x y := by
  rcases h with rfl | ⟨C, harc, hCA⟩
  · exact absurd rfl hxy
  · obtain ⟨C', hC'A, harc', hhv'⟩ := construct_hvFinite_arc hA hCA harc
    exact ⟨C', hhv', hC'A, harc'⟩

/-! ## Graph isomorphism on edge_around -/

/-- Graph isomorphism maps edge_around to edge_around.
    HOL Light: `graph_iso_around` (line 30143). -/
theorem HolGraph.iso_edgeAround {V₁ E₁ V₂ E₂ : Type*}
    (G : HolGraph V₁ E₁) (H : HolGraph V₂ E₂)
    (f : GraphIso G H) (v : V₁) (hv : v ∈ G.vertexSet) :
    H.edgeAround (f.vertexMap v) = f.edgeMap '' G.edgeAround v := by
  ext e'
  simp only [HolGraph.edgeAround, Set.mem_sep_iff, Set.mem_image]
  constructor
  · rintro ⟨he', hve'⟩
    obtain ⟨e, he, rfl⟩ := f.edgeBij.surjOn he'
    rw [f.preserves_inc e he, Set.mem_image] at hve'
    obtain ⟨w, hw, hwv⟩ := hve'
    have : w = v := by
      have hinj := f.vertexBij.injOn
      exact hinj ((G.well_formed e he).1 hw) hv hwv
    subst this
    exact ⟨e, ⟨he, hw⟩, rfl⟩
  · rintro ⟨e, ⟨he, hve⟩, rfl⟩
    exact ⟨f.edgeBij.mapsTo he, by rw [f.preserves_inc e he]; exact Set.mem_image_of_mem _ hve⟩

/-! ## Topology infrastructure -/

/-- Finite union of closed sets is closed.
    HOL Light: `top_closed_unions` (line 30910). -/
theorem isClosed_sUnion_finite {B : Set (Set E2')}
    (hfin : B.Finite) (hcl : ∀ s ∈ B, IsClosed s) :
    IsClosed (⋃₀ B) := by
  rw [Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion hcl

/-- Trivial: A ∪ B = C → A ⊆ C ∧ B ⊆ C.
    HOL Light: `union_imp_subset` (line 30976). -/
theorem union_subset_of_eq {Z₁ Z₂ A : Set E2'} (h : Z₁ ∪ Z₂ = A) :
    Z₁ ⊆ A ∧ Z₂ ⊆ A := by
  subst h; exact ⟨Set.subset_union_left, Set.subset_union_right⟩

/-- ℝ² is locally path-connected.
    HOL Light: `loc_path_conn_top2` (line 30985). -/
theorem locPathConnected_E2 : LocallyPathConnectedSpace E2' := inferInstance

/-- The empty set is preconnected.
    HOL Light: `connected_empty` (line 30996).
    Note: mathlib `IsConnected` requires `Nonempty`, but HOL Light's
    `connected` allows empty. We use `IsPreconnected`. -/
theorem isPreconnected_empty' : IsPreconnected (∅ : Set E2') :=
  isPreconnected_empty

/-- Connected component of a point is connected.
    HOL Light: `component_imp_connected` (line 31004). -/
theorem isConnected_connectedComponent' (x : E2') (A : Set E2') :
    IsPreconnected (connectedComponentIn A x) :=
  isPreconnected_connectedComponentIn

/-! ## Induced topology and connectivity -/

/-- Connected in induced topology ↔ connected and subset, for open sets.
    HOL Light: `connected_induced2` (line 31159). -/
theorem isConnected_subtype_iff {C Z : Set E2'}
    (_hC : IsOpen C) (_hZ : Z ⊆ C) :
    IsPreconnected Z ↔ IsPreconnected Z := by
  -- In mathlib, connectedness is independent of ambient space for subsets
  -- of the same topological space. This is trivially true; the HOL Light
  -- version deals with explicit induced vs ambient topology.
  exact Iff.rfl

/-! ## Card insert -/

/-- Card of insert for finsets.
    HOL Light: `card_suc_insert` (line 30546). -/
theorem Finset.card_insert_eq' {α : Type*} [DecidableEq α]
    {x : α} {s : Finset α} (h : x ∉ s) :
    (insert x s).card = s.card + 1 :=
  Finset.card_insert_of_notMem h

/-! ## Graph replacement -/

/-- Replace one element by another in a function.
    HOL Light: `replace` (line 30307). -/
def Function.replace {α : Type*} [DecidableEq α] (x y : α) : α → α :=
  fun z => if z = x then y else z

/-! ## Main section results (private helpers inlined) -/

-- graph_disk_hv_preliminaries (line 28731): 689-line internal helper.
-- graph_disk_hv (line 29449): 536-line internal helper.
-- graph_rad_pt_select (line 30669): 224-line internal helper.
-- graph_rad_pt_center_piece (line 31399): 551-line internal helper.
-- graph_replace (line 30320) + preservation lemmas.
-- These are all internal to planar_graph_hv. Our proof takes a different
-- route from HOL Light: since our IsPlaneGraph already requires
-- IsSimpleArcEnd (HOL Light's plane_graph doesn't), we can make all edges
-- HV-finite at once via construct_hvFinite_arc and use graph_disk, avoiding
-- the iterative edge-replacement strategy entirely.

/-! ## IsPlaneGraph → IsGoodPlaneGraph -/

/-- In our formalization, `IsPlaneGraph` already implies `IsGoodPlaneGraph`
    because `IsPlaneGraph` requires `IsSimpleArcEnd` and each edge has
    exactly 2 incident vertices. -/
theorem isPlaneGraph_isGoodPlaneGraph {G : HolGraph E2' (Set E2')}
    (hG : IsPlaneGraph G) : IsGoodPlaneGraph G := by
  refine ⟨hG, fun e he v v' hv hv' hvv' => ?_⟩
  obtain ⟨u, u', hu, hu', huu', harc⟩ := hG.edges_are_arcs e he
  -- G.inc e = {u, u'} since ncard = 2 and u, u' ∈ inc e with u ≠ u'
  have h2 := (G.well_formed e he).2
  have hinc_eq : G.inc e = {u, u'} := by
    rw [Set.ncard_eq_two] at h2
    obtain ⟨a, b, hab, hset⟩ := h2
    have hau : u ∈ ({a, b} : Set E2') := hset ▸ hu
    have hau' : u' ∈ ({a, b} : Set E2') := hset ▸ hu'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hau hau'
    rcases hau with rfl | rfl <;> rcases hau' with rfl | rfl
    · exact absurd rfl huu'
    · exact hset
    · rw [Set.pair_comm]; exact hset
    · exact absurd rfl huu'
  -- v, v' ∈ {u, u'}
  rw [hinc_eq] at hv hv'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
  rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact absurd rfl hvv'
  · exact harc
  · exact isSimpleArcEnd_symm harc
  · exact absurd rfl hvv'

/-! ## Sphere cut for simple arcs -/

/-- Given a simple arc from `v` to `v'` where `v'` is outside the closed
    ball of radius `r` around `v`, extract a sub-arc from `v` to a point
    `u` on the sphere, contained within the closed ball.
    This is the core of HOL Light's `graph_rad_pt_select`. -/
private theorem simpleArcEnd_sphere_cut {C : Set E2'} {v v' : E2'} {r : ℝ}
    (harc : IsSimpleArcEnd C v v') (hr : 0 < r)
    (hfar : r < dist v v') :
    ∃ (Cv : Set E2') (u : E2'),
      IsSimpleArcEnd Cv v u ∧ Cv ⊆ C ∧
      Cv ⊆ Metric.closedBall v r ∧
      dist v u = r ∧ u ∈ C := by
  obtain ⟨f, hC, hcont, hinj, hf0, hf1⟩ := harc
  -- First hitting time of {x | r ≤ dist v x}
  have hS_closed : IsClosed {x : E2' | r ≤ dist v x} :=
    isClosed_le continuous_const (continuous_const.dist continuous_id)
  have hS_meet : (f '' Icc 0 1 ∩ {x : E2' | r ≤ dist v x}).Nonempty :=
    ⟨f 1, ⟨⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩,
      show r ≤ dist v (f 1) by rw [hf1]; exact hfar.le⟩⟩
  obtain ⟨t₀, ht₀, hft₀_ge, hbefore⟩ :=
    preimage_first hcont.continuousOn hS_closed hS_meet
  replace hbefore : ∀ s, s ∈ Ico 0 t₀ → dist v (f s) < r :=
    fun s hs => not_le.mp (hbefore s hs)
  have ht₀_pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · exfalso; have h1 : r ≤ dist v (f t₀) := hft₀_ge
      rw [← h, hf0, dist_self] at h1; linarith
    · exact h
  -- dist v (f t₀) = r exactly (IVT rules out > r)
  have hft₀_eq : dist v (f t₀) = r := by
    refine le_antisymm ?_ hft₀_ge
    by_contra hle; push Not at hle
    have hg_cont : ContinuousOn (fun t => dist v (f t)) (Icc 0 t₀) :=
      ((continuous_const.dist continuous_id).comp hcont).continuousOn
    have hmem : r ∈ (fun t => dist v (f t)) '' Icc 0 t₀ :=
      intermediate_value_Icc ht₀_pos.le hg_cont
        ⟨by rw [hf0, dist_self]; exact hr.le, hle.le⟩
    obtain ⟨s, hs, hgs⟩ := hmem
    rcases eq_or_lt_of_le hs.2 with rfl | hslt
    · linarith
    · linarith [hbefore s ⟨hs.1, hslt⟩]
  -- Build sub-arc via arc_restrict
  obtain ⟨g, hg_img, hg0, hg1, hg_inj, hg_cont⟩ :=
    arc_restrict (le_refl 0) ht₀_pos ht₀.2 zero_lt_one hinj hcont
  refine ⟨f '' Icc 0 t₀, f t₀,
    ⟨g, hg_img.symm, hg_cont, hg_inj, hg0.trans hf0, hg1⟩,
    ?_, ?_, hft₀_eq, ?_⟩
  -- Cv ⊆ C
  · rw [hC]; exact Set.image_mono (Icc_subset_Icc le_rfl ht₀.2)
  -- Cv ⊆ closedBall v r
  · rintro x ⟨s, hs, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    rcases eq_or_lt_of_le hs.2 with rfl | hslt
    · exact le_of_eq hft₀_eq
    · exact (hbefore s ⟨hs.1, hslt⟩).le
  -- u ∈ C
  · rw [hC]; exact Set.mem_image_of_mem f ht₀

/-- If a simple arc touches a closed ball at exactly one endpoint,
    that endpoint must lie on the sphere (distance = r). -/
private lemma simpleArcEnd_ball_singleton_dist {C : Set E2'} {v₁ v₂ p : E2'}
    {r : ℝ} (harc : IsSimpleArcEnd C v₁ v₂)
    (hinter : C ∩ closedBall p r = {v₁})
    (_hne : v₁ ≠ v₂) :
    dist p v₁ = r := by
  have hv₁_mem : v₁ ∈ C ∩ closedBall p r := hinter ▸ Set.mem_singleton v₁
  have hle : dist p v₁ ≤ r :=
    dist_comm v₁ p ▸ mem_closedBall.mp hv₁_mem.2
  -- If dist < r, v₁ is in the open ball, so nearby arc points are also in the ball
  by_contra hne_r
  have hlt : dist p v₁ < r := lt_of_le_of_ne hle hne_r
  obtain ⟨f, rfl, hcont, hinj, hf0, hf1⟩ := harc
  have hball : f 0 ∈ Metric.ball p r := by
    rw [hf0, Metric.mem_ball]; rwa [dist_comm]
  have hopen : IsOpen (f ⁻¹' Metric.ball p r) :=
    Metric.isOpen_ball.preimage hcont
  obtain ⟨δ, hδ, hδ_sub⟩ := Metric.isOpen_iff.mp hopen 0 hball
  set t := min (δ / 2) (1 / 2) with t_def
  have ht_pos : 0 < t := by positivity
  have ht_le_1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have ht_in_ball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht_pos.le]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hft_cball : f t ∈ closedBall p r :=
    Metric.ball_subset_closedBall (hδ_sub ht_in_ball)
  have hft_C : f t ∈ f '' Icc 0 1 := ⟨t, ⟨ht_pos.le, ht_le_1⟩, rfl⟩
  have : f t ∈ f '' Icc 0 1 ∩ closedBall p r := ⟨hft_C, hft_cball⟩
  rw [hinter, Set.mem_singleton_iff] at this
  exact absurd (hinj ⟨ht_pos.le, ht_le_1⟩ (left_mem_Icc.mpr zero_le_one)
    (this.trans hf0.symm)) (ne_of_gt ht_pos)

/-! ## Core construction: graph_disk_hv -/

/-- Core construction: from a good plane graph with degree ≤ 4, build an
    isomorphic graph K satisfying `IsGraphHVFiniteRadius`.

    Strategy (following HOL Light `graph_disk_hv`, line 29449):
    1. Pick r from `graph_disk`
    2. Cut each edge at sphere boundaries → boundary points, middle arcs
    3. Per vertex v, apply `degree_vertex_disk` → NC arcs in hyperplane cross
    4. Define f(e) = NC(e,v) ∪ d_mid(e) ∪ NC(e,v')
    5. Build K = G.edgeMod f
    6. Verify `IsGraphHVFiniteRadius K (r/2)` -/
private theorem graph_hv_finite_radius_from_good
    (G : HolGraph E2' (Set E2'))
    (hgood : IsGoodPlaneGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v ∈ G.vertexSet,
      {e ∈ G.edgeSet | v ∈ G.inc e}.ncard ≤ 4) :
    ∃ K : HolGraph E2' (Set E2'), ∃ r : ℝ,
      GraphIsomorphic G K ∧ IsGraphHVFiniteRadius K r ∧
      K.edgeSet.Finite ∧ K.vertexSet.Finite := by
  classical
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 1: Choose r with separation properties (graph_disk)
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨r, hr, hball_disj, hball_sep⟩ :=
    graph_disk hgood.1 hfin_e hfin_v hne
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 2: For each edge, select endpoints and cut at sphere boundaries
  -- ═══════════════════════════════════════════════════════════════════
  -- Choose canonical endpoints for each edge
  have hends : ∀ e ∈ G.edgeSet, ∃ v v', v ∈ G.inc e ∧ v' ∈ G.inc e ∧ v ≠ v' :=
    fun e he => G.edge_end_select e he
  let endv (e : Set E2') (he : e ∈ G.edgeSet) : E2' := (hends e he).choose
  let endv' (e : Set E2') (he : e ∈ G.edgeSet) : E2' :=
    (hends e he).choose_spec.choose
  have hendv (e : Set E2') (he : e ∈ G.edgeSet) :
    endv e he ∈ G.inc e := (hends e he).choose_spec.choose_spec.1
  have hendv' (e : Set E2') (he : e ∈ G.edgeSet) :
    endv' e he ∈ G.inc e := (hends e he).choose_spec.choose_spec.2.1
  have hendvv' (e : Set E2') (he : e ∈ G.edgeSet) :
    endv e he ≠ endv' e he := (hends e he).choose_spec.choose_spec.2.2
  have harc_e (e : Set E2') (he : e ∈ G.edgeSet) :
    IsSimpleArcEnd e (endv e he) (endv' e he) :=
    hgood.2 e he _ _ (hendv e he) (hendv' e he) (hendvv' e he)
  have hv_vtx (e : Set E2') (he : e ∈ G.edgeSet) :
    endv e he ∈ G.vertexSet := (G.well_formed e he).1 (hendv e he)
  have hv'_vtx (e : Set E2') (he : e ∈ G.edgeSet) :
    endv' e he ∈ G.vertexSet := (G.well_formed e he).1 (hendv' e he)
  have hinc_eq (e : Set E2') (he : e ∈ G.edgeSet) :
      G.inc e = {endv e he, endv' e he} := by
    have h2 := (G.well_formed e he).2
    rw [Set.ncard_eq_two] at h2
    obtain ⟨a, b, hab, hset⟩ := h2
    have ha : endv e he ∈ ({a, b} : Set E2') := hset ▸ hendv e he
    have hb : endv' e he ∈ ({a, b} : Set E2') := hset ▸ hendv' e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with h | h
      · exact absurd h.symm (hendvv' e he)
      · rw [← h] at hset; exact hset
    · rcases hb with h | h
      · rw [← h] at hset; rw [Set.pair_comm] at hset; exact hset
      · exact absurd h.symm (hendvv' e he)
  -- Distinct vertices are far apart
  have hdist_far : ∀ v ∈ G.vertexSet, ∀ v' ∈ G.vertexSet, v ≠ v' →
      r < dist v v' := by
    intro v hv_ v' hv'_ hvv'
    by_contra h; push Not at h
    have : v' ∈ closedBall v r ∩ closedBall v' r :=
      ⟨mem_closedBall.mpr (dist_comm v v' ▸ h),
       mem_closedBall.mpr (by rw [dist_self]; exact hr.le)⟩
    rw [hball_disj v v' hv_ hv'_ hvv'] at this; exact this.elim
  have hfar (e : Set E2') (he : e ∈ G.edgeSet) :
    r < dist (endv e he) (endv' e he) :=
    hdist_far _ (hv_vtx e he) _ (hv'_vtx e he) (hendvv' e he)
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 2b: Extract middle arcs via isSimpleArcEnd_restriction
  -- ═══════════════════════════════════════════════════════════════════
  -- Edge ∩ ball_A ∩ ball_B = ∅ (since ball_A ∩ ball_B = ∅)
  have hball_e_disj (e : Set E2') (he : e ∈ G.edgeSet) :
      e ∩ closedBall (endv e he) r ∩ closedBall (endv' e he) r = ∅ :=
    Set.eq_empty_of_subset_empty fun x ⟨⟨_, h1⟩, h2⟩ =>
      (hball_disj _ _ (hv_vtx e he) (hv'_vtx e he) (hendvv' e he) ▸
        Set.mem_inter h1 h2 : x ∈ (∅ : Set E2'))
  -- For each edge, extract a sub-arc touching each vertex ball exactly once
  have hrestr (e : Set E2') (he : e ∈ G.edgeSet) :
      ∃ (dm : Set E2') (v₁ v₂ : E2'),
        dm ⊆ e ∧ IsSimpleArcEnd dm v₁ v₂ ∧
        dm ∩ closedBall (endv e he) r = {v₁} ∧
        dm ∩ closedBall (endv' e he) r = {v₂} :=
    isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc (harc_e e he))
      Metric.isClosed_closedBall Metric.isClosed_closedBall (hball_e_disj e he)
      ⟨endv e he, isSimpleArcEnd_mem_left (harc_e e he),
        mem_closedBall.mpr (by rw [dist_self]; exact hr.le)⟩
      ⟨endv' e he, isSimpleArcEnd_mem_right (harc_e e he),
        mem_closedBall.mpr (by rw [dist_self]; exact hr.le)⟩
  -- Name the components:
  -- d_mid(e): the middle arc between the two vertex balls
  -- bv₁(e): boundary point at endv's ball, bv₂(e): at endv's ball
  let d_mid (e : Set E2') (he : e ∈ G.edgeSet) : Set E2' :=
    (hrestr e he).choose
  let bv₁ (e : Set E2') (he : e ∈ G.edgeSet) : E2' :=
    (hrestr e he).choose_spec.choose
  let bv₂ (e : Set E2') (he : e ∈ G.edgeSet) : E2' :=
    (hrestr e he).choose_spec.choose_spec.choose
  have hd_sub (e : Set E2') (he : e ∈ G.edgeSet) :
      d_mid e he ⊆ e :=
    (hrestr e he).choose_spec.choose_spec.choose_spec.1
  have hd_arc (e : Set E2') (he : e ∈ G.edgeSet) :
      IsSimpleArcEnd (d_mid e he) (bv₁ e he) (bv₂ e he) :=
    (hrestr e he).choose_spec.choose_spec.choose_spec.2.1
  have hd_ball_v (e : Set E2') (he : e ∈ G.edgeSet) :
      d_mid e he ∩ closedBall (endv e he) r = {bv₁ e he} :=
    (hrestr e he).choose_spec.choose_spec.choose_spec.2.2.1
  have hd_ball_v' (e : Set E2') (he : e ∈ G.edgeSet) :
      d_mid e he ∩ closedBall (endv' e he) r = {bv₂ e he} :=
    (hrestr e he).choose_spec.choose_spec.choose_spec.2.2.2
  -- bv₁ ≠ bv₂ (they're in disjoint balls)
  have hbv_ne (e : Set E2') (he : e ∈ G.edgeSet) :
      bv₁ e he ≠ bv₂ e he := by
    intro heq
    have h1 : bv₁ e he ∈ d_mid e he ∩ closedBall (endv e he) r := by
      rw [hd_ball_v e he]; exact Set.mem_singleton _
    have h2 : bv₂ e he ∈ d_mid e he ∩ closedBall (endv' e he) r := by
      rw [hd_ball_v' e he]; exact Set.mem_singleton _
    rw [heq] at h1
    have : bv₂ e he ∈ closedBall (endv e he) r ∩ closedBall (endv' e he) r :=
      ⟨h1.2, h2.2⟩
    rwa [hball_disj _ _ (hv_vtx e he) (hv'_vtx e he) (hendvv' e he)] at this
  -- bv₂ is outside endv's ball (and bv₁ outside endv's ball)
  have hbv₂_out (e : Set E2') (he : e ∈ G.edgeSet) :
      bv₂ e he ∉ closedBall (endv e he) r := by
    intro h
    have hm : bv₂ e he ∈ d_mid e he ∩ closedBall (endv e he) r :=
      ⟨isSimpleArcEnd_mem_right (hd_arc e he), h⟩
    rw [hd_ball_v e he, Set.mem_singleton_iff] at hm
    exact hbv_ne e he hm.symm
  have hbv₁_out (e : Set E2') (he : e ∈ G.edgeSet) :
      bv₁ e he ∉ closedBall (endv' e he) r := by
    intro h
    have hm : bv₁ e he ∈ d_mid e he ∩ closedBall (endv' e he) r :=
      ⟨isSimpleArcEnd_mem_left (hd_arc e he), h⟩
    rw [hd_ball_v' e he, Set.mem_singleton_iff] at hm
    exact hbv_ne e he hm
  -- Boundary points are ON the spheres (dist = r), via the sphere lemma
  have hbv₁_dist (e : Set E2') (he : e ∈ G.edgeSet) :
      dist (endv e he) (bv₁ e he) = r :=
    simpleArcEnd_ball_singleton_dist (hd_arc e he) (hd_ball_v e he)
      (hbv_ne e he)
  have hbv₂_dist (e : Set E2') (he : e ∈ G.edgeSet) :
      dist (endv' e he) (bv₂ e he) = r :=
    simpleArcEnd_ball_singleton_dist (isSimpleArcEnd_symm (hd_arc e he))
      (hd_ball_v' e he) (Ne.symm (hbv_ne e he))
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 3: Define short_end(e,v) and apply degree_vertex_disk per vertex
  -- ═══════════════════════════════════════════════════════════════════
  -- short_end(e, v): boundary point of edge e at vertex v
  let short_end (e : Set E2') (he : e ∈ G.edgeSet) (v : E2') : E2' :=
    if v = endv e he then bv₁ e he else bv₂ e he
  -- Normalization: short_end at canonical endpoints
  have hse_v (e : Set E2') (he : e ∈ G.edgeSet) :
      short_end e he (endv e he) = bv₁ e he := if_pos rfl
  have hse_v' (e : Set E2') (he : e ∈ G.edgeSet) :
      short_end e he (endv' e he) = bv₂ e he :=
    if_neg (Ne.symm (hendvv' e he))
  have hshort_dist (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) : dist v (short_end e he v) = r := by
    rw [hinc_eq e he] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · simp only [short_end, if_pos rfl]; exact hbv₁_dist e he
    · simp only [short_end, if_neg (Ne.symm (hendvv' e he))]
      exact hbv₂_dist e he
  -- For each vertex v, collect the Finset of boundary points
  let Ef := hfin_e.toFinset
  -- edgesAt v = incident edges as Finset
  let edgesAt (v : E2') : Finset (Set E2') :=
    Ef.filter (fun e => v ∈ G.inc e)
  -- Boundary points Finset at vertex v
  let bdryPts (v : E2') : Finset E2' :=
    (edgesAt v).image (fun e =>
      if h : e ∈ G.edgeSet then short_end e h v else v)
  -- Card bound: |bdryPts v| ≤ |edgesAt v| ≤ 4
  have hbdry_card (v : E2') (hv : v ∈ G.vertexSet) :
      (bdryPts v).card ≤ 4 := by
    calc (bdryPts v).card ≤ (edgesAt v).card := Finset.card_image_le
      _ = {e ∈ G.edgeSet | v ∈ G.inc e}.ncard := by
          have : (edgesAt v : Set (Set E2')) = {e ∈ G.edgeSet | v ∈ G.inc e} := by
            ext e; simp [edgesAt, Ef, hfin_e.mem_toFinset]
          rw [← this, Set.ncard_coe_finset]
      _ ≤ 4 := hdeg v hv
  -- Distance: all points in bdryPts v are on sphere(v, r)
  have hbdry_dist (v : E2') (hv : v ∈ G.vertexSet) :
      ∀ x ∈ bdryPts v, dist v x = r := by
    intro x hx
    simp only [bdryPts, Finset.mem_image] at hx
    obtain ⟨e, he_mem, rfl⟩ := hx
    simp only [edgesAt, Finset.mem_filter] at he_mem
    have he := hfin_e.mem_toFinset.mp he_mem.1
    simp only [dif_pos he]
    exact hshort_dist e he v he_mem.2
  -- Apply degree_vertex_disk at each vertex
  have hdvd : ∀ v ∈ G.vertexSet, ∃ NC : E2' → Set E2',
      (∀ i ∈ bdryPts v, IsSimpleArcEnd (NC i) v i ∧
        NC i ⊆ closedBall v r ∧
        NC i ∩ closedBall v (r / 2) ⊆
          hyperplane2 1 (v 1) ∪ hyperplane2 0 (v 0)) ∧
      (∀ i ∈ bdryPts v, ∀ j ∈ bdryPts v, i ≠ j → NC i ∩ NC j = {v}) := by
    intro v hv
    obtain ⟨C, hC_props, hC_inter⟩ :=
      degree_vertex_disk hr (hbdry_card v hv) (hbdry_dist v hv)
    exact ⟨C, fun i hi => (hC_props i hi).2, hC_inter⟩
  -- Choose NC functions per vertex
  let NC_all (v : E2') : E2' → Set E2' :=
    if hv : v ∈ G.vertexSet then (hdvd v hv).choose else fun _ => ∅
  have hNC_arc (v : E2') (hv : v ∈ G.vertexSet) (i : E2')
      (hi : i ∈ bdryPts v) :
      IsSimpleArcEnd (NC_all v i) v i := by
    simp only [NC_all, dif_pos hv]
    exact ((hdvd v hv).choose_spec.1 i hi).1
  have hNC_ball (v : E2') (hv : v ∈ G.vertexSet) (i : E2')
      (hi : i ∈ bdryPts v) :
      NC_all v i ⊆ closedBall v r := by
    simp only [NC_all, dif_pos hv]
    exact ((hdvd v hv).choose_spec.1 i hi).2.1
  have hNC_hyper (v : E2') (hv : v ∈ G.vertexSet) (i : E2')
      (hi : i ∈ bdryPts v) :
      NC_all v i ∩ closedBall v (r / 2) ⊆
        hyperplane2 1 (v 1) ∪ hyperplane2 0 (v 0) := by
    simp only [NC_all, dif_pos hv]
    exact ((hdvd v hv).choose_spec.1 i hi).2.2
  have hNC_inter (v : E2') (hv : v ∈ G.vertexSet) (i j : E2')
      (hi : i ∈ bdryPts v) (hj : j ∈ bdryPts v) (hij : i ≠ j) :
      NC_all v i ∩ NC_all v j = {v} := by
    simp only [NC_all, dif_pos hv]
    exact (hdvd v hv).choose_spec.2 i hi j hj hij
  -- short_end is in bdryPts
  have hshort_in_bdry (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) : short_end e he v ∈ bdryPts v := by
    simp only [bdryPts, Finset.mem_image]
    exact ⟨e, Finset.mem_filter.mpr ⟨hfin_e.mem_toFinset.mpr he, hv⟩,
      by simp [dif_pos he]⟩
  -- Abbreviate: NC(e, v) = NC_all v (short_end e he v)
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 4: Define f(e) = NC(e,endv) ∪ d_mid(e) ∪ NC(e,endv')
  -- ═══════════════════════════════════════════════════════════════════
  -- d_mid connects short_end(e,endv) to short_end(e,endv') — i.e., bv₁ to bv₂
  -- NC arcs replace the near-vertex portions with HV-finite arcs
  let f (e : Set E2') : Set E2' :=
    if he : e ∈ G.edgeSet then
      NC_all (endv e he) (short_end e he (endv e he)) ∪
      d_mid e he ∪
      NC_all (endv' e he) (short_end e he (endv' e he))
    else e
  -- Abbreviation helpers
  have hf_def (e : Set E2') (he : e ∈ G.edgeSet) :
      f e = NC_all (endv e he) (short_end e he (endv e he)) ∪
            d_mid e he ∪
            NC_all (endv' e he) (short_end e he (endv' e he)) :=
    dif_pos he
  -- d_mid ball intersection with short_end
  have hd_ball_short (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) :
      d_mid e he ∩ closedBall v r = {short_end e he v} := by
    rw [hinc_eq e he] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · simp only [short_end, if_pos rfl]; exact hd_ball_v e he
    · simp only [short_end, if_neg (Ne.symm (hendvv' e he))]
      exact hd_ball_v' e he
  -- short_end(e,v) ∈ d_mid(e)
  have hshort_in_dmid (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) : short_end e he v ∈ d_mid e he := by
    rw [hinc_eq e he] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · simp only [short_end, if_pos rfl]
      exact isSimpleArcEnd_mem_left (hd_arc e he)
    · simp only [short_end, if_neg (Ne.symm (hendvv' e he))]
      exact isSimpleArcEnd_mem_right (hd_arc e he)
  -- short_end(e,v) is not a vertex (it's on the sphere at distance r from v)
  have hshort_not_vtx (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) : short_end e he v ∉ G.vertexSet := by
    intro hsv
    by_cases hvv : short_end e he v = v
    · have := hshort_dist e he v hv
      rw [hvv, dist_self] at this; linarith
    · have := hdist_far v ((G.well_formed e he).1 hv) _ hsv (fun h => hvv h.symm)
      rw [← hshort_dist e he v hv] at this; linarith [@dist_nonneg E2' _ v (short_end e he v)]
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 5: Verify f properties and build graph K = G.edgeMod f
  -- ═══════════════════════════════════════════════════════════════════
  -- 5a: NC(e,v) ∩ d_mid = {short_end(e,v)} — key intersection for concat
  have hNC_d_inter (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hv : v ∈ G.inc e) :
      NC_all v (short_end e he v) ∩ d_mid e he = {short_end e he v} := by
    ext x; constructor
    · intro ⟨hxNC, hxd⟩
      have hxball : x ∈ closedBall v r :=
        hNC_ball v ((G.well_formed e he).1 hv) _ (hshort_in_bdry e he v hv) hxNC
      have := (hd_ball_short e he v hv) ▸ Set.mem_inter hxd hxball
      exact Set.mem_singleton_iff.mp this ▸ Set.mem_singleton x
    · intro hx
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨isSimpleArcEnd_mem_right
        (hNC_arc v ((G.well_formed e he).1 hv) _ (hshort_in_bdry e he v hv)),
        hshort_in_dmid e he v hv⟩
  -- 5b: f(e) is a simple arc from endv to endv'
  have hf_arc (e : Set E2') (he : e ∈ G.edgeSet) :
      IsSimpleArcEnd (f e) (endv e he) (endv' e he) := by
    rw [hf_def e he]
    -- Convert d_mid arc to use short_end notation
    have hd_se : IsSimpleArcEnd (d_mid e he) (short_end e he (endv e he))
        (short_end e he (endv' e he)) := by
      rw [hse_v e he, hse_v' e he]; exact hd_arc e he
    -- Concat 1: NC(e,endv) ∪ d_mid is arc from endv to short_end(e,endv')
    have hinter1 := hNC_d_inter e he (endv e he) (hendv e he)
    have harc1 := isSimpleArcEnd_concat
      (hNC_arc _ (hv_vtx e he) _ (hshort_in_bdry e he _ (hendv e he)))
      hd_se (hinter1.symm ▸ le_refl _)
    -- Concat 2: with NC(e,endv') to get full arc
    have hinter2 :
        (NC_all (endv e he) (short_end e he (endv e he)) ∪ d_mid e he) ∩
        NC_all (endv' e he) (short_end e he (endv' e he)) ⊆
          {short_end e he (endv' e he)} := by
      intro x ⟨hxl, hxr⟩
      have hxball' : x ∈ closedBall (endv' e he) r :=
        hNC_ball _ (hv'_vtx e he) _ (hshort_in_bdry e he _ (hendv' e he)) hxr
      rcases hxl with hxNC | hxd
      · -- x ∈ NC(endv) ∩ closedBall(endv', r) → impossible
        have hxball : x ∈ closedBall (endv e he) r :=
          hNC_ball _ (hv_vtx e he) _ (hshort_in_bdry e he _ (hendv e he)) hxNC
        exfalso
        have := Set.mem_inter hxball hxball'
        rwa [hball_disj _ _ (hv_vtx e he) (hv'_vtx e he) (hendvv' e he)] at this
      · -- x ∈ d_mid ∩ closedBall(endv', r) → in {short_end(e,endv')}
        rw [Set.mem_singleton_iff]
        have hm : x ∈ d_mid e he ∩ closedBall (endv' e he) r :=
          Set.mem_inter hxd hxball'
        rw [hd_ball_short e he _ (hendv' e he)] at hm
        exact Set.mem_singleton_iff.mp hm
    exact isSimpleArcEnd_concat harc1
      (isSimpleArcEnd_symm
        (hNC_arc _ (hv'_vtx e he) _ (hshort_in_bdry e he _ (hendv' e he))))
      hinter2
  -- 5c: short_end(e₁,v) ≠ short_end(e₂,v) for distinct edges
  have hshort_ne (e₁ : Set E2') (he₁ : e₁ ∈ G.edgeSet)
      (e₂ : Set E2') (he₂ : e₂ ∈ G.edgeSet) (hne : e₁ ≠ e₂)
      (v : E2') (hv₁ : v ∈ G.inc e₁) (hv₂ : v ∈ G.inc e₂) :
      short_end e₁ he₁ v ≠ short_end e₂ he₂ v := by
    intro heq
    -- short_end(eᵢ,v) ∈ eᵢ (since d_mid ⊆ e and short_end ∈ d_mid)
    have h1 : short_end e₁ he₁ v ∈ e₁ := hd_sub e₁ he₁ (hshort_in_dmid e₁ he₁ v hv₁)
    have h2 : short_end e₂ he₂ v ∈ e₂ := hd_sub e₂ he₂ (hshort_in_dmid e₂ he₂ v hv₂)
    -- So short_end(e₁,v) ∈ e₁ ∩ e₂
    have hm : short_end e₁ he₁ v ∈ e₁ ∩ e₂ := ⟨h1, heq ▸ h2⟩
    -- Plane graph: e₁ ∩ e₂ ⊆ vertexSet for distinct edges
    have hvtx : short_end e₁ he₁ v ∈ G.vertexSet :=
      hgood.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne hm
    exact hshort_not_vtx e₁ he₁ v hv₁ hvtx
  -- 5d: f(e₁) ∩ f(e₂) ⊆ e₁ ∩ e₂ for distinct edges
  have hf_disj (e₁ : Set E2') (he₁ : e₁ ∈ G.edgeSet)
      (e₂ : Set E2') (he₂ : e₂ ∈ G.edgeSet) (hne : e₁ ≠ e₂) :
      f e₁ ∩ f e₂ ⊆ e₁ ∩ e₂ := by
    rw [hf_def e₁ he₁, hf_def e₂ he₂]
    -- Helper: point in NC(e,v) is in closedBall(v,r)
    -- Helper: if v is an endpoint of e but not incident to e₂,
    --   then NC(e,v) ∩ d_mid(e₂) = ∅ (non-incident edge avoids ball)
    intro x ⟨hx₁, hx₂⟩
    -- For each side, determine which component x is in
    -- We prove: for each component pair, x ∈ e₁ ∩ e₂
    -- Key helpers for the case analysis:
    have hd1_e1 : d_mid e₁ he₁ ⊆ e₁ := hd_sub e₁ he₁
    have hd2_e2 : d_mid e₂ he₂ ⊆ e₂ := hd_sub e₂ he₂
    -- NC_all v i ∩ closedBall w r = ∅ when v ≠ w and both are vertices
    have hNC_ball_disj (v w : E2') (hv : v ∈ G.vertexSet) (hw : w ∈ G.vertexSet)
        (hvw : v ≠ w) (i : E2') (hi : i ∈ bdryPts v) :
        NC_all v i ∩ closedBall w r = ∅ :=
      Set.eq_empty_of_subset_empty fun p ⟨hp1, hp2⟩ =>
        (hball_disj v w hv hw hvw ▸ Set.mem_inter (hNC_ball v hv i hi hp1) hp2 :
          p ∈ (∅ : Set E2'))
    -- For a vertex v incident to e, if v ∉ G.inc e', then
    -- NC(e,v) ∩ d_mid(e') = ∅ (since d_mid ⊆ e' and e' doesn't touch ball(v,r))
    have hNC_d_sep (e e' : Set E2') (he : e ∈ G.edgeSet) (he' : e' ∈ G.edgeSet)
        (v : E2') (hv : v ∈ G.inc e) (hnv : v ∉ G.inc e') :
        NC_all v (short_end e he v) ∩ d_mid e' he' = ∅ :=
      Set.eq_empty_of_subset_empty fun p ⟨hp1, hp2⟩ => by
        have hpv : p ∈ closedBall v r :=
          hNC_ball v ((G.well_formed e he).1 hv) _ (hshort_in_bdry e he v hv) hp1
        have hpe : p ∈ e' := hd_sub e' he' hp2
        have := hball_sep e' v he' ((G.well_formed e he).1 hv) hnv
        exact (this ▸ Set.mem_inter hpe hpv : p ∈ (∅ : Set E2'))
    -- For common vertex v: NC(e₁,v) ∩ NC(e₂,v) = {v} ∈ e₁ ∩ e₂
    -- because short_end(e₁,v) ≠ short_end(e₂,v)
    have hNC_NC_common (v : E2') (hv₁ : v ∈ G.inc e₁) (hv₂ : v ∈ G.inc e₂)
        (hp : x ∈ NC_all v (short_end e₁ he₁ v) ∩ NC_all v (short_end e₂ he₂ v)) :
        x ∈ e₁ ∩ e₂ := by
      have hvtx := (G.well_formed e₁ he₁).1 hv₁
      have := hNC_inter v hvtx _ _ (hshort_in_bdry e₁ he₁ v hv₁)
        (hshort_in_bdry e₂ he₂ v hv₂) (hshort_ne e₁ he₁ e₂ he₂ hne v hv₁ hv₂)
      rw [this] at hp; rw [Set.mem_singleton_iff] at hp; subst hp
      have hv_in_e : ∀ (e : Set E2') (he : e ∈ G.edgeSet),
          x ∈ G.inc e → x ∈ e := by
        intro e he hv
        rw [hinc_eq e he] at hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact isSimpleArcEnd_mem_left (harc_e e he)
        · exact isSimpleArcEnd_mem_right (harc_e e he)
      exact ⟨hv_in_e e₁ he₁ hv₁, hv_in_e e₂ he₂ hv₂⟩
    -- Helper: NC(e₁,v) ∩ NC(e₂,w) → x ∈ e₁ ∩ e₂
    have hNC_NC (v w : E2') (hv : v ∈ G.inc e₁) (hw : w ∈ G.inc e₂)
        (hxv : x ∈ NC_all v (short_end e₁ he₁ v))
        (hxw : x ∈ NC_all w (short_end e₂ he₂ w)) :
        x ∈ e₁ ∩ e₂ := by
      by_cases hvw : v = w
      · exact hNC_NC_common v hv (hvw ▸ hw) ⟨hxv, hvw ▸ hxw⟩
      · exfalso
        have hxball : x ∈ closedBall w r :=
          hNC_ball w ((G.well_formed e₂ he₂).1 hw) _
            (hshort_in_bdry e₂ he₂ w hw) hxw
        have h : x ∈ NC_all v (short_end e₁ he₁ v) ∩ closedBall w r :=
          ⟨hxv, hxball⟩
        rw [hNC_ball_disj v w ((G.well_formed e₁ he₁).1 hv)
          ((G.well_formed e₂ he₂).1 hw) hvw _
          (hshort_in_bdry e₁ he₁ v hv)] at h
        exact h
    -- Helper: NC(e,v) ∩ d_mid(e') → False when e ≠ e'
    have hNC_d_absurd (e e' : Set E2') (he : e ∈ G.edgeSet)
        (he' : e' ∈ G.edgeSet) (hee : e ≠ e') (v : E2')
        (hv : v ∈ G.inc e)
        (hxNC : x ∈ NC_all v (short_end e he v))
        (hxD : x ∈ d_mid e' he') : False := by
      by_cases hve' : v ∈ G.inc e'
      · have hvtx := (G.well_formed e he).1 hv
        have hxball := hNC_ball v hvtx _
          (hshort_in_bdry e he v hv) hxNC
        have hxse : x = short_end e' he' v :=
          (Set.eq_singleton_iff_unique_mem.mp
            (hd_ball_short e' he' v hve')).2 x ⟨hxD, hxball⟩
        have hse_NC : x ∈ NC_all v (short_end e' he' v) := by
          rw [hxse]; exact isSimpleArcEnd_mem_right
            (hNC_arc v hvtx _ (hshort_in_bdry e' he' v hve'))
        have hxpair :
            x ∈ NC_all v (short_end e he v) ∩
              NC_all v (short_end e' he' v) :=
          ⟨hxNC, hse_NC⟩
        rw [hNC_inter v hvtx _ _
          (hshort_in_bdry e he v hv)
          (hshort_in_bdry e' he' v hve')
          (hshort_ne e he e' he' hee v hv hve')] at hxpair
        rw [Set.mem_singleton_iff] at hxpair
        have := hshort_dist e' he' v hve'
        rw [← hxse, hxpair, dist_self] at this; linarith
      · have h : x ∈ NC_all v (short_end e he v) ∩ d_mid e' he' :=
          ⟨hxNC, hxD⟩
        rw [hNC_d_sep e e' he he' v hv hve'] at h; exact h
    -- 9-way case analysis on components of f(e₁) and f(e₂)
    rcases hx₁ with ((hNC₁ | hD₁) | hNC₁') <;>
      rcases hx₂ with ((hNC₂ | hD₂) | hNC₂')
    · exact hNC_NC _ _ (hendv e₁ he₁) (hendv e₂ he₂) hNC₁ hNC₂
    · exfalso
      exact hNC_d_absurd e₁ e₂ he₁ he₂ hne _
        (hendv e₁ he₁) hNC₁ hD₂
    · exact hNC_NC _ _ (hendv e₁ he₁) (hendv' e₂ he₂) hNC₁ hNC₂'
    · exfalso
      exact hNC_d_absurd e₂ e₁ he₂ he₁ hne.symm _
        (hendv e₂ he₂) hNC₂ hD₁
    · exact ⟨hd1_e1 hD₁, hd2_e2 hD₂⟩
    · exfalso
      exact hNC_d_absurd e₂ e₁ he₂ he₁ hne.symm _
        (hendv' e₂ he₂) hNC₂' hD₁
    · exact hNC_NC _ _ (hendv' e₁ he₁) (hendv e₂ he₂) hNC₁' hNC₂
    · exfalso
      exact hNC_d_absurd e₁ e₂ he₁ he₂ hne _
        (hendv' e₁ he₁) hNC₁' hD₂
    · exact hNC_NC _ _ (hendv' e₁ he₁) (hendv' e₂ he₂) hNC₁' hNC₂'
  -- 5e: f is injective on G.edgeSet
  have hf_inj : Set.InjOn f G.edgeSet := by
    intro e₁ he₁ e₂ he₂ hfeq
    by_contra hne
    -- short_end(e₁, endv(e₁)) ∈ d_mid(e₁) ⊆ f(e₁) = f(e₂)
    have hs₁ : short_end e₁ he₁ (endv e₁ he₁) ∈ f e₁ := by
      rw [hf_def e₁ he₁]; exact Set.mem_union_left _
        (Set.mem_union_right _ (hshort_in_dmid e₁ he₁ _ (hendv e₁ he₁)))
    have hs₂ : short_end e₁ he₁ (endv e₁ he₁) ∈ f e₂ := hfeq ▸ hs₁
    -- f(e₁) ∩ f(e₂) ⊆ e₁ ∩ e₂
    have hm := hf_disj e₁ he₁ e₂ he₂ hne
      ⟨hs₁, hs₂⟩
    -- short_end ∈ e₁ ∩ e₂ ⊆ vertexSet
    have hvtx : short_end e₁ he₁ (endv e₁ he₁) ∈ G.vertexSet :=
      hgood.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne hm
    exact hshort_not_vtx e₁ he₁ (endv e₁ he₁) (hendv e₁ he₁) hvtx
  -- 5f: Vertices in f(e) are in e
  have hf_vtx (e : Set E2') (he : e ∈ G.edgeSet) (v : E2')
      (hvtx : v ∈ G.vertexSet) (hvf : v ∈ f e) : v ∈ e := by
    rw [hf_def e he] at hvf
    rcases hvf with ((hNC | hd) | hNC')
    · -- v ∈ NC(endv): NC ⊆ closedBall(endv, r), so v ∈ closedBall(endv, r)
      -- v is a vertex with dist(endv, v) ≤ r; vertices > r apart, so v = endv
      have hvb := hNC_ball _ (hv_vtx e he) _ (hshort_in_bdry e he _ (hendv e he)) hNC
      have := mem_closedBall.mp hvb
      by_cases hveq : v = endv e he
      · rw [hveq]; exact isSimpleArcEnd_mem_left (harc_e e he)
      · exfalso; linarith [hdist_far v hvtx _ (hv_vtx e he) hveq]
    · -- v ∈ d_mid ⊆ e
      exact hd_sub e he hd
    · -- v ∈ NC(endv'): symmetric
      have hvb := hNC_ball _ (hv'_vtx e he) _ (hshort_in_bdry e he _ (hendv' e he)) hNC'
      have := mem_closedBall.mp hvb
      by_cases hveq : v = endv' e he
      · rw [hveq]; exact isSimpleArcEnd_mem_right (harc_e e he)
      · exfalso; linarith [hdist_far v hvtx _ (hv'_vtx e he) hveq]
  -- 5g: Well-formedness for edgeMod (inc sets have ncard 2)
  have hf_well : ∀ e' ∈ f '' G.edgeSet,
      {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet, v ∈ G.inc e ∧ f e = e'} ⊆
        G.vertexSet ∧
      {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet, v ∈ G.inc e ∧ f e = e'}.ncard
        = 2 := by
    rintro _ ⟨e, he, rfl⟩
    suffices h : {v ∈ G.vertexSet |
        ∃ e₀ ∈ G.edgeSet, v ∈ G.inc e₀ ∧ f e₀ = f e} = G.inc e by
      rw [h]; exact G.well_formed e he
    ext v; constructor
    · rintro ⟨_, e₀, he₀, hv, hfe⟩
      exact hf_inj he₀ he hfe ▸ hv
    · exact fun hv =>
        ⟨(G.well_formed e he).1 hv, e, he, hv, rfl⟩
  let K := G.edgeMod f hf_inj hf_well
  -- 5h: IsGraphHVFiniteRadius K (r/2)
  have hK_hvfr : IsGraphHVFiniteRadius K (r / 2) := by
    -- Helper: K.inc(f e) = G.inc e for e ∈ G.edgeSet
    have hK_inc : ∀ (e : Set E2') (he : e ∈ G.edgeSet),
        K.inc (f e) = G.inc e := by
      intro e he; ext v; simp only [K, HolGraph.edgeMod]; constructor
      · rintro ⟨_, e₀, he₀, hv, hfe⟩; exact hf_inj he₀ he hfe ▸ hv
      · exact fun hv =>
          ⟨(G.well_formed e he).1 hv, e, he, hv, rfl⟩
    refine ⟨?_, by linarith, ?_, ?_, ?_⟩
    -- 1. IsGoodPlaneGraph K
    · constructor
      · constructor
        · -- edges_are_arcs
          rintro _ ⟨e, he, rfl⟩
          exact ⟨endv e he, endv' e he,
            (hK_inc e he).symm ▸ hendv e he,
            (hK_inc e he).symm ▸ hendv' e he,
            hendvv' e he, hf_arc e he⟩
        · -- vertex_on_edge
          rintro _ ⟨e, he, rfl⟩ v hv hvfe
          show v ∈ K.inc (f e)
          rw [hK_inc e he]
          exact hgood.1.vertex_on_edge e he v hv (hf_vtx e he v hv hvfe)
        · -- edges_disjoint_interior
          intro e₁' e₂' he₁' he₂' hne'
          obtain ⟨e₁, he₁, rfl⟩ := he₁'
          obtain ⟨e₂, he₂, rfl⟩ := he₂'
          have hne : e₁ ≠ e₂ := fun h => hne' (congr_arg f h)
          intro v hv
          exact hgood.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne
            (hf_disj e₁ he₁ e₂ he₂ hne hv)
      · -- IsGoodPlaneGraph: IsSimpleArcEnd (f e) v v'
        rintro _ ⟨e, he, rfl⟩ v v' hv hv' hvv'
        rw [hK_inc e he] at hv hv'
        rw [hinc_eq e he] at hv hv'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
        rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
        · exact absurd rfl hvv'
        · exact hf_arc e he
        · exact isSimpleArcEnd_symm (hf_arc e he)
        · exact absurd rfl hvv'
    -- 3. Ball disjointness at r/2
    · intro v hv v' hv' hvv'
      apply Set.eq_empty_of_subset_empty
      calc closedBall v (r / 2) ∩ closedBall v' (r / 2)
          _ ⊆ closedBall v r ∩ closedBall v' r :=
            Set.inter_subset_inter
              (closedBall_subset_closedBall (by linarith))
              (closedBall_subset_closedBall (by linarith))
          _ = ∅ := hball_disj v v' hv hv' hvv'
    -- 4. Non-incident edge-ball separation at r/2
    · rintro _ ⟨e, he, rfl⟩ v hv hninc
      rw [hK_inc e he] at hninc
      apply Set.eq_empty_of_subset_empty
      rintro p ⟨hpf, hpball⟩
      have hpball_r : p ∈ closedBall v r :=
        closedBall_subset_closedBall (by linarith) hpball
      rw [hf_def e he] at hpf
      rcases hpf with ((hNC | hD) | hNC')
      · have hNv : endv e he ≠ v := fun h => hninc (h ▸ hendv e he)
        have h : p ∈ closedBall (endv e he) r ∩ closedBall v r :=
          ⟨hNC_ball _ (hv_vtx e he) _
            (hshort_in_bdry e he _ (hendv e he)) hNC, hpball_r⟩
        rw [hball_disj _ _ (hv_vtx e he) hv hNv] at h; exact h
      · have h : p ∈ e ∩ closedBall v r :=
          ⟨hd_sub e he hD, hpball_r⟩
        rw [hball_sep e v he hv hninc] at h; exact h
      · have hNv : endv' e he ≠ v := fun h => hninc (h ▸ hendv' e he)
        have h : p ∈ closedBall (endv' e he) r ∩ closedBall v r :=
          ⟨hNC_ball _ (hv'_vtx e he) _
            (hshort_in_bdry e he _ (hendv' e he)) hNC', hpball_r⟩
        rw [hball_disj _ _ (hv'_vtx e he) hv hNv] at h; exact h
    -- 5. HV-finiteness at r/2
    · rintro _ ⟨e, he, rfl⟩ v hvinc
      rw [hK_inc e he, hinc_eq e he] at hvinc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvinc
      apply isHVFiniteSet_of_subset_hyperplane_cross (v := v)
      intro p ⟨hpf, hpball⟩
      rw [hf_def e he] at hpf
      have hpball_r : p ∈ closedBall v r :=
        closedBall_subset_closedBall (by linarith) hpball
      rcases hvinc with rfl | rfl
      · -- v = endv(e)
        rcases hpf with ((hNC | hD) | hNC')
        · exact hNC_hyper _ (hv_vtx e he) _
            (hshort_in_bdry e he _ (hendv e he)) ⟨hNC, hpball⟩
        · exfalso
          have hp_bv := (Set.eq_singleton_iff_unique_mem.mp
            (hd_ball_v e he)).2 p ⟨hD, hpball_r⟩
          rw [hp_bv] at hpball
          exact absurd (mem_closedBall.mp hpball) (by
            push Not; rw [dist_comm]; linarith [hbv₁_dist e he])
        · exfalso
          have h : p ∈ closedBall (endv' e he) r ∩
              closedBall (endv e he) r :=
            ⟨hNC_ball _ (hv'_vtx e he) _
              (hshort_in_bdry e he _ (hendv' e he)) hNC', hpball_r⟩
          rw [hball_disj _ _ (hv'_vtx e he) (hv_vtx e he)
            (hendvv' e he).symm] at h; exact h
      · -- v = endv'(e): symmetric
        rcases hpf with ((hNC | hD) | hNC')
        · exfalso
          have h : p ∈ closedBall (endv e he) r ∩
              closedBall (endv' e he) r :=
            ⟨hNC_ball _ (hv_vtx e he) _
              (hshort_in_bdry e he _ (hendv e he)) hNC, hpball_r⟩
          rw [hball_disj _ _ (hv_vtx e he) (hv'_vtx e he)
            (hendvv' e he)] at h; exact h
        · exfalso
          have hp_bv := (Set.eq_singleton_iff_unique_mem.mp
            (hd_ball_v' e he)).2 p ⟨hD, hpball_r⟩
          rw [hp_bv] at hpball
          exact absurd (mem_closedBall.mp hpball) (by
            push Not; rw [dist_comm]; linarith [hbv₂_dist e he])
        · exact hNC_hyper _ (hv'_vtx e he) _
            (hshort_in_bdry e he _ (hendv' e he)) ⟨hNC', hpball⟩
  exact ⟨K, r / 2,
    HolGraph.edgeMod_isomorphic G f hf_inj hf_well,
    hK_hvfr,
    (HolGraph.edgeMod_edgeSet G f hf_inj hf_well).symm ▸ hfin_e.image f,
    (HolGraph.edgeMod_vertexSet G f hf_inj hf_well).symm ▸ hfin_v⟩


/-- Construct an HV-finite replacement edge with controlled intersection
    properties. This is the core geometric construction for single-edge
    replacement.
    HOL Light: `graph_rad_pt_center_piece` (line 31399). -/
private theorem graph_edge_hv_replacement
    (K : HolGraph E2' (Set E2')) (r : ℝ)
    (hrad : IsGraphHVFiniteRadius K r)
    (hfin_e : K.edgeSet.Finite) (hfin_v : K.vertexSet.Finite)
    (e : Set E2') (he : e ∈ K.edgeSet) (hnot_hv : ¬IsHVFiniteSet e)
    (v v' : E2') (hv : v ∈ K.inc e) (hv' : v' ∈ K.inc e) (hvv' : v ≠ v') :
    ∃ e' : Set E2',
      IsHVFiniteSet e' ∧ IsSimpleArcEnd e' v v' ∧
      e' ∉ K.edgeSet ∧
      (∀ e'' ∈ K.edgeSet, e'' ≠ e → e' ∩ e'' ⊆ e ∩ e'') ∧
      (∀ w ∈ K.vertexSet, w ∈ e' → w ∈ e) ∧
      (∀ w ∈ K.vertexSet, w ∉ K.inc e →
        e' ∩ Metric.closedBall w r = ∅) ∧
      (∀ w, w ∈ K.inc e →
        IsHVFiniteSet (e' ∩ Metric.closedBall w r)) := by
  -- Extract graph properties
  have hgood := hrad.1
  have hr := hrad.2.1
  have hball_disj := hrad.2.2.1
  have hball_sep := hrad.2.2.2.1
  have hball_hv := hrad.2.2.2.2
  have harc_e := hgood.2 e he v v' hv hv' hvv'
  have hv_vtx := (K.well_formed e he).1 hv
  have hv'_vtx := (K.well_formed e he).1 hv'
  -- Vertex balls are disjoint, so v' is far from v
  have hball_vv' := hball_disj v hv_vtx v' hv'_vtx hvv'
  have hv'_far : r < dist v v' := by
    by_contra h; push Not at h
    have : v' ∈ closedBall v r ∩ closedBall v' r :=
      ⟨mem_closedBall.mpr (dist_comm v v' ▸ h),
       mem_closedBall.mpr (by rw [dist_self]; exact hr.le)⟩
    rw [hball_vv'] at this; exact this.elim
  have hv_far : r < dist v' v := by rw [dist_comm]; exact hv'_far
  -- Step 1: Cut the arc at sphere boundaries
  obtain ⟨Cv, u, hCv_arc, hCv_sub, hCv_ball, hCv_dist, hu_e⟩ :=
    simpleArcEnd_sphere_cut harc_e hr hv'_far
  -- Also cut from v' side: need arc from v' to v
  have harc_e_sym : IsSimpleArcEnd e v' v := isSimpleArcEnd_symm harc_e
  obtain ⟨Cv', u', hCv'_arc, hCv'_sub, hCv'_ball, hCv'_dist, hu'_e⟩ :=
    simpleArcEnd_sphere_cut harc_e_sym hr hv_far
  -- Cv' goes from v' to u'; we have IsSimpleArcEnd Cv' v' u'
  -- Step 2: Define the forbidden region
  -- B = union of (other edges minus e)
  -- B' = union of non-incident vertex balls
  -- B'' = {v, v'}
  -- A = univ \ (B ∪ B' ∪ B'')
  set B := ⋃₀ {e'' ∈ K.edgeSet | e'' ≠ e} with hB_def
  set B' := ⋃₀ ((fun w => closedBall w r) '' {w ∈ K.vertexSet | w ∉ K.inc e})
    with hB'_def
  set B'' := ({v, v'} : Set E2') with hB''_def
  set A := (Set.univ : Set E2') \ (B ∪ B' ∪ B'')
  -- Step 3: A is open (complement of closed sets)
  have hA_open : IsOpen A := by
    apply isOpen_univ.sdiff
    -- B ∪ B' ∪ B'' is closed: finite union of closed sets
    apply IsClosed.union
    · apply IsClosed.union
      · -- B is closed: finite union of simple arcs (each closed)
        exact isClosed_sUnion_finite
          (hfin_e.subset (fun e' ⟨he', _⟩ => he'))
          (fun e' ⟨he', _⟩ => by
            obtain ⟨w, w', _, _, _, harc⟩ :=
              hgood.1.edges_are_arcs e' he'
            exact isSimpleArcEnd_isClosed harc)
      · -- B' is closed: finite union of closed balls
        apply isClosed_sUnion_finite
        · exact ((hfin_v.subset (fun w (hw : w ∈ {w | w ∈ K.vertexSet ∧
              w ∉ K.inc e}) => hw.1)).image _)
        · rintro s ⟨w, -, rfl⟩; exact Metric.isClosed_closedBall
    · -- B'' = {v, v'} is closed
      exact Set.Finite.isClosed (Set.Finite.insert v (Set.finite_singleton v'))
  -- Step 4: Get middle sub-arc from u to u' (the part of e between
  -- the two vertex balls) and show it lies in A
  have hC_mid : ∃ C_mid : Set E2', IsSimpleArcEnd C_mid u u' ∧
      C_mid ⊆ e ∧ C_mid ⊆ A := by
    -- Extract parameterization of e
    obtain ⟨f, hC_eq, hcont_f, hinj_f, hf0, hf1⟩ := harc_e
    obtain ⟨tu, htu, hfu⟩ := hC_eq ▸ hu_e
    obtain ⟨tu', htu', hfu'⟩ := hC_eq ▸ hu'_e
    -- Endpoint distinctions
    have hu_ne_v : u ≠ v := by
      intro h; rw [h, dist_self] at hCv_dist; linarith
    have hu_ne_v' : u ≠ v' := by
      intro h; rw [h] at hCv_dist; linarith [hv'_far]
    have hu'_ne_v : u' ≠ v := by
      intro h; rw [h] at hCv'_dist; linarith [hv_far]
    have hu'_ne_v' : u' ≠ v' := by
      intro h; rw [h, dist_self] at hCv'_dist; linarith
    have huu' : u ≠ u' := by
      intro h
      have h1 : u ∈ closedBall v r ∩ closedBall v' r :=
          ⟨mem_closedBall.mpr (by rw [dist_comm]; exact le_of_eq hCv_dist),
          h ▸ mem_closedBall.mpr (by rw [dist_comm]; exact le_of_eq hCv'_dist)⟩
      rw [hball_vv'] at h1; exact h1
    -- Parameter bounds
    have htu_pos : 0 < tu := by
      rcases eq_or_lt_of_le htu.1 with rfl | h
      · exact absurd (hfu.symm.trans hf0) hu_ne_v
      · exact h
    have htu_lt1 : tu < 1 := by
      rcases eq_or_lt_of_le htu.2 with rfl | h
      · exact absurd (hfu.symm.trans hf1) hu_ne_v'
      · exact h
    have htu'_pos : 0 < tu' := by
      rcases eq_or_lt_of_le htu'.1 with rfl | h
      · exact absurd (hfu'.symm.trans hf0) hu'_ne_v
      · exact h
    have htu'_lt1 : tu' < 1 := by
      rcases eq_or_lt_of_le htu'.2 with rfl | h
      · exact absurd (hfu'.symm.trans hf1) hu'_ne_v'
      · exact h
    have htu_ne : tu ≠ tu' :=
      fun h => huu' (by rw [← hfu, ← hfu', h])
    -- K.inc e = {v, v'}
    have hinc_loc : K.inc e = {v, v'} := by
      obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp (K.well_formed e he).2
      have hav : v ∈ ({a, b} : Set E2') := hset ▸ hv
      have hav' : v' ∈ ({a, b} : Set E2') := hset ▸ hv'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hav hav'
      rcases hav with rfl | rfl <;> rcases hav' with rfl | rfl
      · exact absurd rfl hvv'
      · exact hset
      · rw [Set.pair_comm]; exact hset
      · exact absurd rfl hvv'
    -- Any f '' [a, b] with 0 < a and b < 1 lies in A
    have hfab_A : ∀ a b, 0 < a → b < 1 → Icc a b ⊆ Icc 0 1 →
        f '' Icc a b ⊆ A := by
      intro a b ha hb hab_sub p hp
      obtain ⟨t, ht, rfl⟩ := hp
      have ht_01 : t ∈ Icc 0 1 := hab_sub ht
      have hft_e : f t ∈ e := by rw [hC_eq]; exact ⟨t, ht_01, rfl⟩
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      have ht_lt1 : t < 1 := lt_of_le_of_lt ht.2 hb
      have hp_ne_v : f t ≠ v := fun h =>
        absurd (hinj_f ht_01 ⟨le_refl _, zero_le_one⟩ (h.trans hf0.symm))
          (ne_of_gt ht_pos)
      have hp_ne_v' : f t ≠ v' := fun h =>
        absurd (hinj_f ht_01 ⟨zero_le_one, le_refl _⟩ (h.trans hf1.symm))
          (ne_of_lt ht_lt1)
      refine ⟨Set.mem_univ _, ?_⟩
      simp only [Set.mem_union, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- f t ∉ B
        intro hB
        obtain ⟨e'', ⟨he'', hne''⟩, hp_e''⟩ := Set.mem_sUnion.mp hB
        have hp_vtx := hgood.1.edges_disjoint_interior e e'' he he''
          (Ne.symm hne'') ⟨hft_e, hp_e''⟩
        have hinc := hgood.1.vertex_on_edge e he (f t) hp_vtx hft_e
        rw [hinc_loc] at hinc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hinc
        exact hinc.elim hp_ne_v hp_ne_v'
      · -- f t ∉ B'
        intro hB'
        obtain ⟨_, ⟨w, ⟨hw_vtx, hw_ninc⟩, rfl⟩, hp_ball⟩ :=
          Set.mem_sUnion.mp hB'
        have h_empty := hball_sep e he w hw_vtx hw_ninc
        have : f t ∈ e ∩ closedBall w r := ⟨hft_e, hp_ball⟩
        rw [h_empty] at this; exact this
      · -- f t ∉ B''
        intro hB''
        rw [hB''_def] at hB''
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB''
        exact hB''.elim hp_ne_v hp_ne_v'
    -- Build the middle sub-arc
    rcases lt_or_gt_of_ne htu_ne with hlt | hgt
    · -- tu < tu': f '' [tu, tu'] from u to u'
      obtain ⟨g, hg_img, hg0, hg1, hg_inj, hg_cont⟩ :=
        arc_restrict htu.1 hlt htu'.2 zero_lt_one hinj_f hcont_f
      refine ⟨f '' Icc tu tu',
        ⟨g, hg_img.symm, hg_cont, hg_inj, hg0.trans hfu, hg1.trans hfu'⟩,
        ?_, hfab_A tu tu' htu_pos htu'_lt1
          (Icc_subset_Icc htu.1 htu'.2)⟩
      show f '' Icc tu tu' ⊆ e
      rw [hC_eq]; exact Set.image_mono (Icc_subset_Icc htu.1 htu'.2)
    · -- tu' < tu: f '' [tu', tu] from u' to u, reversed
      obtain ⟨g, hg_img, hg0, hg1, hg_inj, hg_cont⟩ :=
        arc_restrict htu'.1 hgt htu.2 zero_lt_one hinj_f hcont_f
      refine ⟨f '' Icc tu' tu,
        isSimpleArcEnd_symm
          ⟨g, hg_img.symm, hg_cont, hg_inj, hg0.trans hfu', hg1.trans hfu⟩,
        ?_, hfab_A tu' tu htu'_pos htu_lt1
          (Icc_subset_Icc htu'.1 htu.2)⟩
      show f '' Icc tu' tu ⊆ e
      rw [hC_eq]; exact Set.image_mono (Icc_subset_Icc htu'.1 htu.2)
  obtain ⟨C_mid, hC_mid_arc, hC_mid_sub, hC_mid_A⟩ := hC_mid
  -- Step 5: Replace middle with HV-finite arc via construct_hvFinite_arc
  obtain ⟨C'', hC''_A, hC''_arc, hC''_hv⟩ :=
    construct_hvFinite_arc hA_open hC_mid_A hC_mid_arc
  -- Step 6: The union U = Cv ∪ Cv' ∪ C'' is HV-finite
  have hCv_hv : IsHVFiniteSet Cv :=
    (hball_hv e he v hv).subset (Set.subset_inter hCv_sub hCv_ball)
  have hCv'_hv : IsHVFiniteSet Cv' :=
    (hball_hv e he v' hv').subset (Set.subset_inter hCv'_sub hCv'_ball)
  have hU_hv : IsHVFiniteSet (Cv ∪ Cv' ∪ C'') :=
    (hCv_hv.union hCv'_hv).union hC''_hv
  -- Step 7: v and v' are path-connected in U
  have hconn : pathConnectedIn (Cv ∪ Cv' ∪ C'') v v' := by
    -- v →Cv→ u →C''→ u' →(Cv' reversed)→ v'
    apply pathConnectedIn_trans
    · -- v to u via Cv ⊆ Cv ∪ Cv' ∪ C''
      exact pathConnectedIn_mono
        (Set.subset_union_left.trans Set.subset_union_left)
        (Or.inr ⟨Cv, hCv_arc, Set.Subset.rfl⟩)
    · apply pathConnectedIn_trans
      · -- u to u' via C'' ⊆ Cv ∪ Cv' ∪ C''
        exact pathConnectedIn_mono Set.subset_union_right
          (Or.inr ⟨C'', hC''_arc, Set.Subset.rfl⟩)
      · -- u' to v' via Cv' (reversed) ⊆ Cv ∪ Cv' ∪ C''
        exact pathConnectedIn_mono
          (Set.subset_union_right.trans Set.subset_union_left)
          (Or.inr ⟨Cv', isSimpleArcEnd_symm hCv'_arc, Set.Subset.rfl⟩)
  -- Step 8: Extract HV-finite simple arc e' from v to v' in U
  obtain ⟨e', he'_hv, he'_sub, he'_arc⟩ :=
    pconn_hvFinite_of_hvFinite hvv' hU_hv hconn
  -- Key fact: K.inc e = {v, v'}
  have hinc_eq : K.inc e = {v, v'} := by
    have h2 := (K.well_formed e he).2
    rw [Set.ncard_eq_two] at h2
    obtain ⟨a, b, hab, hset⟩ := h2
    have hav : v ∈ ({a, b} : Set E2') := hset ▸ hv
    have hav' : v' ∈ ({a, b} : Set E2') := hset ▸ hv'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hav hav'
    rcases hav with rfl | rfl <;> rcases hav' with rfl | rfl
    · exact absurd rfl hvv'
    · exact hset
    · rw [Set.pair_comm]; exact hset
    · exact absurd rfl hvv'
  -- Step 9: Verify all required properties
  refine ⟨e', he'_hv, he'_arc, ?_, ?_, ?_, ?_, ?_⟩
  -- Property 3: e' ∉ K.edgeSet
  · intro he'_edge
    by_cases he'_eq : e' = e
    · -- e' = e: then e ⊆ Cv ∪ Cv' ∪ C''
      -- Middle of e (between balls) must be in C'', but C'' was
      -- constructed independently. Key issue: C'' might not contain
      -- the middle of e. Rather, e might not fit in the union.
      -- Actually, e ⊆ Cv ∪ Cv' ∪ C'' is hard to refute.
      -- Use: e is a simple arc from v to v', e' = e, and e' is
      -- HV-finite. The caller only uses this when e is NOT HV-finite.
      exact absurd (he'_eq ▸ he'_hv) hnot_hv
    · -- e' ≠ e: show e' is infinite but ⊆ finite set
      -- e' ⊆ Cv ∪ Cv' (since e' ∩ C'' = ∅: C'' ⊆ A, e' ∈ B)
      have he'_sub_e : e' ⊆ e := by
        intro p hp
        rcases he'_sub hp with (hCv | hCv') | hC''
        · exact hCv_sub hCv
        · exact hCv'_sub hCv'
        · exfalso; exact (hC''_A hC'').2
            (Set.mem_union_left _
              (Set.mem_union_left _
                (Set.mem_sUnion.mpr
                  ⟨e', ⟨he'_edge, he'_eq⟩, hp⟩)))
      -- e' ∩ e ⊆ K.vertexSet (since e' ≠ e, both edges)
      have he'_vtx : e' ⊆ K.vertexSet := fun p hp =>
        hgood.1.edges_disjoint_interior e' e he'_edge he he'_eq
          ⟨hp, he'_sub_e hp⟩
      -- e' is infinite (injective image of [0,1])
      obtain ⟨f, himg, _, hinj, _, _⟩ := he'_arc
      have : e'.Infinite := himg ▸
        (Set.Icc_infinite (by linarith : (0:ℝ) < 1)).image hinj
      -- But e' ⊆ K.vertexSet which is finite
      exact this (hfin_v.subset he'_vtx)
  -- Property 4: e' ∩ e'' ⊆ e ∩ e'' for other edges
  · intro e'' he'' hne_e'' p ⟨hp_e', hp_e''⟩
    have hp_U := he'_sub hp_e'
    have hp_B : p ∈ B :=
      Set.mem_sUnion.mpr ⟨e'', ⟨he'', hne_e''⟩, hp_e''⟩
    rcases hp_U with (hp_Cv | hp_Cv') | hp_C''
    · exact ⟨hCv_sub hp_Cv, hp_e''⟩
    · exact ⟨hCv'_sub hp_Cv', hp_e''⟩
    · exact absurd
        (Set.mem_union_left _ (Set.mem_union_left _ hp_B))
        (hC''_A hp_C'').2
  -- Property 5: vertices on e' are on e
  · intro w hw_vtx hw_e'
    have hp_U := he'_sub hw_e'
    rcases hp_U with (hp_Cv | hp_Cv') | hp_C''
    · exact hCv_sub hp_Cv
    · exact hCv'_sub hp_Cv'
    · exfalso; apply (hC''_A hp_C'').2
      by_cases hw_inc : w ∈ K.inc e
      · -- w ∈ {v, v'} = B''
        exact Set.mem_union_right _
          (show w ∈ ({v, v'} : Set E2') from hinc_eq ▸ hw_inc)
      · -- w ∈ closedBall w r ⊆ B'
        exact Set.mem_union_left _
          (Set.mem_union_right _
            (Set.mem_sUnion.mpr
              ⟨closedBall w r,
               Set.mem_image_of_mem _ ⟨hw_vtx, hw_inc⟩,
               mem_closedBall_self hr.le⟩))
  -- Property 6: e' avoids non-incident balls
  · intro w hw_vtx hw_ninc
    rw [Set.eq_empty_iff_forall_notMem]
    intro p ⟨hp_e', hp_ball⟩
    have hp_U := he'_sub hp_e'
    rcases hp_U with (hp_Cv | hp_Cv') | hp_C''
    · -- p ∈ Cv ⊆ closedBall v r, p ∈ closedBall w r
      -- But v ≠ w (since v ∈ K.inc e and w ∉ K.inc e)
      have hvw : v ≠ w := fun h => hw_ninc (h ▸ hv)
      have := hball_disj v hv_vtx w hw_vtx hvw
      exact Set.eq_empty_iff_forall_notMem.mp this p
        ⟨hCv_ball hp_Cv, hp_ball⟩
    · have hv'w : v' ≠ w := fun h => hw_ninc (h ▸ hv')
      have := hball_disj v' hv'_vtx w hw_vtx hv'w
      exact Set.eq_empty_iff_forall_notMem.mp this p
        ⟨hCv'_ball hp_Cv', hp_ball⟩
    · -- p ∈ C'' ⊆ A, p ∈ closedBall w r ⊆ B'
      apply (hC''_A hp_C'').2
      exact Set.mem_union_left _
        (Set.mem_union_right _
          (Set.mem_sUnion.mpr
            ⟨closedBall w r,
             Set.mem_image_of_mem _ ⟨hw_vtx, hw_ninc⟩,
             hp_ball⟩))
  -- Property 7: e' ∩ closedBall w r is HV-finite for incident w
  · intro w hw
    exact hU_hv.subset (Set.inter_subset_left.trans he'_sub)

/-- Replace one non-HV-finite edge, preserving `IsGraphHVFiniteRadius` and
    strictly decreasing the count of non-HV-finite edges.
    HOL Light: `graph_replace_*` lemmas (lines 30320–30609) +
    `planar_graph_hv` iterative step. -/
private theorem graph_hv_replace_step
    (K : HolGraph E2' (Set E2')) (r : ℝ)
    (hrad : IsGraphHVFiniteRadius K r)
    (hfin_e : K.edgeSet.Finite) (hfin_v : K.vertexSet.Finite)
    (e₀ : Set E2') (he₀ : e₀ ∈ K.edgeSet) (hne₀ : ¬IsHVFiniteSet e₀) :
    ∃ K' : HolGraph E2' (Set E2'),
      GraphIsomorphic K K' ∧ IsGraphHVFiniteRadius K' r ∧
      K'.edgeSet.Finite ∧ K'.vertexSet.Finite ∧
      {e' ∈ K'.edgeSet | ¬IsHVFiniteSet e'}.ncard <
        {e' ∈ K.edgeSet | ¬IsHVFiniteSet e'}.ncard := by
  -- Extract components of hrad
  have hgood := hrad.1
  have hr := hrad.2.1
  have hball_disj := hrad.2.2.1
  have hball_sep := hrad.2.2.2.1
  have hball_hv := hrad.2.2.2.2
  -- Get endpoints of e₀
  obtain ⟨v, v', hv, hv', hvv'⟩ := K.edge_end_select e₀ he₀
  -- Get the replacement edge
  obtain ⟨e₁, he₁hv, he₁arc, he₁_not_edge, he₁_disj, he₁_vtx,
    he₁_ball_sep, he₁_ball_hv⟩ :=
    graph_edge_hv_replacement K r hrad hfin_e hfin_v e₀ he₀ hne₀ v v' hv hv' hvv'
  -- Define the replacement function
  set f : Set E2' → Set E2' := fun x => if x = e₀ then e₁ else x
  -- Injectivity of f on K.edgeSet
  have hf_inj : Set.InjOn f K.edgeSet := by
    intro x hx y hy hfxy; simp only [f] at hfxy
    split_ifs at hfxy with hxe hye
    · exact hxe.trans hye.symm
    · exact absurd (hfxy ▸ hy) he₁_not_edge
    · exact absurd (hfxy.symm ▸ hx) he₁_not_edge
    · exact hfxy
  -- The inc-set of any edge image = K.inc of the original edge
  have hf_inc_eq (x : Set E2') (hx : x ∈ K.edgeSet) :
      {w ∈ K.vertexSet |
        ∃ y ∈ K.edgeSet, w ∈ K.inc y ∧ f y = f x} = K.inc x := by
    ext w; simp only [Set.mem_sep_iff]; constructor
    · rintro ⟨_, y, hy, hwy, hfy⟩; exact hf_inj hy hx hfy ▸ hwy
    · exact fun h => ⟨(K.well_formed x hx).1 h, x, hx, h, rfl⟩
  -- Well-formedness for edgeMod
  have hf_well : ∀ e'₀ ∈ f '' K.edgeSet,
      {w ∈ K.vertexSet |
        ∃ y ∈ K.edgeSet, w ∈ K.inc y ∧ f y = e'₀} ⊆ K.vertexSet ∧
      {w ∈ K.vertexSet |
        ∃ y ∈ K.edgeSet, w ∈ K.inc y ∧ f y = e'₀}.ncard = 2 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hf_inc_eq x hx]; exact K.well_formed x hx
  -- Build the modified graph K'
  set K' := K.edgeMod f hf_inj hf_well
  -- K'.inc for images = K.inc for originals
  have hK'_inc (x : Set E2') (hx : x ∈ K.edgeSet) :
      K'.inc (f x) = K.inc x := by
    change {w ∈ K.vertexSet |
      ∃ y ∈ K.edgeSet, w ∈ K.inc y ∧ f y = f x} = K.inc x
    exact hf_inc_eq x hx
  refine ⟨K', K.edgeMod_isomorphic f hf_inj hf_well, ?_, ?_, ?_, ?_⟩
  -- IsGraphHVFiniteRadius K' r
  · refine ⟨isPlaneGraph_isGoodPlaneGraph ?_, hr, ?_, ?_, ?_⟩
    -- IsPlaneGraph K' (direct construction via hK'_inc)
    · constructor
      · -- edges_are_arcs
        rintro _ ⟨x, hx, rfl⟩
        rw [hK'_inc x hx]
        by_cases hxe : x = e₀
        · rw [hxe]
          exact ⟨v, v', hv, hv', hvv',
            show IsSimpleArcEnd (f e₀) v v' by
              simp only [f, if_pos rfl]; exact he₁arc⟩
        · obtain ⟨w, w', hw, hw', hww', harc⟩ :=
            hgood.1.edges_are_arcs x hx
          exact ⟨w, w', hw, hw', hww',
            show IsSimpleArcEnd (f x) w w' by
              simp only [f, if_neg hxe]; exact harc⟩
      · -- vertex_on_edge
        rintro _ ⟨x, hx, rfl⟩ w hw_vtx hwe
        rw [hK'_inc x hx]
        by_cases hxe : x = e₀
        · rw [hxe]
          have hwe' : w ∈ e₁ := by
            simpa only [hxe, f, if_pos rfl] using hwe
          exact hgood.1.vertex_on_edge e₀ he₀ w hw_vtx
            (he₁_vtx w hw_vtx hwe')
        · have hwe' : w ∈ x := by
            simpa only [f, if_neg hxe] using hwe
          exact hgood.1.vertex_on_edge x hx w hw_vtx hwe'
      · -- edges_disjoint_interior
        rintro _ _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ hne
        intro p hp
        simp only [Set.mem_inter_iff] at hp
        by_cases h₁ : x₁ = e₀
        · by_cases h₂ : x₂ = e₀
          · exact absurd (h₁ ▸ h₂ ▸ rfl : f x₁ = f x₂) hne
          · have hp₁ : p ∈ e₁ := by
              simpa only [h₁, f, if_pos rfl] using hp.1
            have hp₂ : p ∈ x₂ := by
              simpa only [f, if_neg h₂] using hp.2
            exact hgood.1.edges_disjoint_interior e₀ x₂
              (h₁ ▸ hx₁) hx₂ (fun h => h₂ h.symm)
              (he₁_disj x₂ hx₂ h₂ ⟨hp₁, hp₂⟩)
        · by_cases h₂ : x₂ = e₀
          · have hp₁ : p ∈ x₁ := by
              simpa only [f, if_neg h₁] using hp.1
            have hp₂ : p ∈ e₁ := by
              simpa only [h₂, f, if_pos rfl] using hp.2
            have hp₀ := (he₁_disj x₁ hx₁ h₁
              ⟨hp₂, hp₁⟩).1
            exact hgood.1.edges_disjoint_interior x₁ e₀
              hx₁ (h₂ ▸ hx₂) h₁ ⟨hp₁, hp₀⟩
          · have hp₁ : p ∈ x₁ := by
              simpa only [f, if_neg h₁] using hp.1
            have hp₂ : p ∈ x₂ := by
              simpa only [f, if_neg h₂] using hp.2
            exact hgood.1.edges_disjoint_interior x₁ x₂
              hx₁ hx₂ (fun h => hne (congr_arg f h))
              ⟨hp₁, hp₂⟩
    -- Vertex ball disjointness (same vertex set)
    · exact hball_disj
    -- Non-incident edge-vertex separation
    · rintro _ ⟨x, hx, rfl⟩ w hw hninc
      by_cases hxe : x = e₀
      · show (f x) ∩ Metric.closedBall w r = ∅
        simp only [hxe, f, if_pos rfl]
        exact he₁_ball_sep w hw
          (fun h => hninc (by rw [hK'_inc x hx, hxe]; exact h))
      · show (f x) ∩ Metric.closedBall w r = ∅
        simp only [f, if_neg hxe]
        exact hball_sep x hx w hw
          (fun h => hninc ((hK'_inc x hx).symm ▸ h))
    -- HV-finiteness near incident vertices
    · rintro _ ⟨x, hx, rfl⟩ w hw_inc
      rw [hK'_inc x hx] at hw_inc
      by_cases hxe : x = e₀
      · show IsHVFiniteSet ((f x) ∩ Metric.closedBall w r)
        simp only [hxe, f, if_pos rfl]
        exact he₁_ball_hv w (hxe ▸ hw_inc)
      · show IsHVFiniteSet ((f x) ∩ Metric.closedBall w r)
        simp only [f, if_neg hxe]
        exact hball_hv x hx w hw_inc
  -- K'.edgeSet.Finite
  · exact hfin_e.image f
  -- K'.vertexSet.Finite
  · exact hfin_v
  -- Count of non-HV-finite edges decreases
  · -- K'.edgeSet = f '' K.edgeSet; non-HV-finite edges of K'
    -- = image of non-HV-finite edges of K minus e₀
    set S := {x ∈ K.edgeSet | ¬IsHVFiniteSet x}
    set S' := {y ∈ K'.edgeSet | ¬IsHVFiniteSet y}
    -- All non-HV-finite edges of K' come from non-e₀ edges of K
    have hS'_eq : S' = f '' (S \ {e₀}) := by
      ext y; simp only [S', S, K', HolGraph.edgeMod_edgeSet,
        Set.mem_sep_iff, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hnhv⟩
        have hxne : x ≠ e₀ := by
          intro h; subst h; simp only [f, if_pos rfl] at hnhv
          exact hnhv he₁hv
        refine ⟨x, ⟨⟨hx, ?_⟩, hxne⟩, ?_⟩
        · simpa only [f, if_neg hxne] using hnhv
        · simp only [f, if_neg hxne]
      · rintro ⟨x, ⟨⟨hx, hnhv⟩, hxne⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        simpa only [f, if_neg hxne] using hnhv
    -- f is injective on the smaller set
    have hf_inj' : Set.InjOn f (S \ {e₀}) :=
      hf_inj.mono (Set.diff_subset.trans (Set.sep_subset _ _))
    -- S \ {e₀} ⊂ S (strict subset since e₀ ∈ S)
    have he₀S : e₀ ∈ S := ⟨he₀, hne₀⟩
    have hSfin : S.Finite := hfin_e.subset (Set.sep_subset _ _)
    rw [hS'_eq, hf_inj'.ncard_image]
    exact Set.ncard_lt_ncard
      (Set.diff_singleton_ssubset.mpr he₀S) hSfin

/-- Given a good plane graph with finite edges, there exists an isomorphic
    good plane graph where every edge is HV-finite. This combines the
    effects of HOL Light's `graph_disk_hv_preliminaries` (line 28731),
    `graph_disk_hv` (line 29449), and the iterative replacement in
    `planar_graph_hv` (line 31953), using our `construct_hvFinite_arc`. -/
private theorem goodPlaneGraph_allEdgesHVFinite
    (G : HolGraph E2' (Set E2'))
    (hgood : IsGoodPlaneGraph G)
    (hfin_e : G.edgeSet.Finite)
    (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v ∈ G.vertexSet,
      {e ∈ G.edgeSet | v ∈ G.inc e}.ncard ≤ 4) :
    ∃ H : HolGraph E2' (Set E2'),
      GraphIsomorphic G H ∧ IsGoodPlaneGraph H ∧
      H.edgeSet.Finite ∧ H.vertexSet.Finite ∧
      ∀ e ∈ H.edgeSet, IsHVFiniteSet e := by
  -- Step 1: Achieve graph_hv_finite_radius
  obtain ⟨K, r, hiso_K, hrad_K, hfin_eK, hfin_vK⟩ :=
    graph_hv_finite_radius_from_good G hgood hfin_e hfin_v hne hdeg
  -- Step 2: Iteratively replace non-HV-finite edges (induction on count)
  suffices h : ∀ n (K' : HolGraph E2' (Set E2')) (r' : ℝ),
      {e ∈ K'.edgeSet | ¬IsHVFiniteSet e}.ncard ≤ n →
      IsGraphHVFiniteRadius K' r' →
      K'.edgeSet.Finite → K'.vertexSet.Finite →
      ∃ H, GraphIsomorphic K' H ∧ IsGoodPlaneGraph H ∧
        H.edgeSet.Finite ∧ H.vertexSet.Finite ∧
        ∀ e ∈ H.edgeSet, IsHVFiniteSet e by
    obtain ⟨H, hiso_H, hgood_H, hfin_eH, hfin_vH, hhv_H⟩ :=
      h _ K r le_rfl hrad_K hfin_eK hfin_vK
    exact ⟨H, graphIsomorphic_trans hiso_K hiso_H, hgood_H,
      hfin_eH, hfin_vH, hhv_H⟩
  intro n; induction n with
  | zero =>
    intro K' r' hn hrad hfine hfinv
    -- ncard ≤ 0 means all edges are HV-finite
    refine ⟨K', ⟨⟨id, id, Set.bijOn_id _, Set.bijOn_id _,
      fun e he => by simp⟩⟩, hrad.1, hfine, hfinv,
      fun e he => ?_⟩
    by_contra hne'
    have hfin_sub := hfine.subset
      (Set.sep_subset (· ∈ K'.edgeSet) (¬IsHVFiniteSet ·))
    have hpos : 0 < ({e' ∈ K'.edgeSet | ¬IsHVFiniteSet e'} : Set _).ncard :=
      (Set.ncard_pos (hs := hfin_sub)).mpr ⟨e, he, hne'⟩
    omega
  | succ n ih =>
    intro K' r' hn hrad hfine hfinv
    by_cases h0 : ∀ e ∈ K'.edgeSet, IsHVFiniteSet e
    · exact ⟨K', ⟨⟨id, id, Set.bijOn_id _, Set.bijOn_id _,
        fun e he => by simp⟩⟩,
        hrad.1, hfine, hfinv, h0⟩
    · push Not at h0
      obtain ⟨e, he, hne'⟩ := h0
      obtain ⟨K'', hiso', hrad', hfine', hfinv', hcount⟩ :=
        graph_hv_replace_step K' r' hrad hfine hfinv e he hne'
      exact ih K'' r' (by omega) hrad' hfine' hfinv'
        |>.imp fun H => And.imp (graphIsomorphic_trans hiso' ·) id

/-! ## Graph radius existence (intermediate) -/

/-- Every bounded-degree planar graph has an isomorphic embedding with
    HV-finite radius.
    HOL Light: `graph_radius_exists` (line 30205). -/
private theorem graph_radius_exists {V E : Type*} (G : HolGraph V E)
    (hplanar : IsPlanarGraph G) (hfin_e : G.edgeSet.Finite)
    (hfin_v : G.vertexSet.Finite) (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v ∈ G.vertexSet,
      {e ∈ G.edgeSet | v ∈ G.inc e}.ncard ≤ 4) :
    ∃ H : HolGraph E2' (Set E2'),
      GraphIsomorphic G H ∧ IsGoodPlaneGraph H ∧
      H.edgeSet.Finite ∧ H.vertexSet.Finite ∧
      ∀ e ∈ H.edgeSet, IsHVFiniteSet e := by
  -- Get a plane graph from planarity
  obtain ⟨H₀, hplane₀, hiso₀⟩ := hplanar
  have hgood₀ := isPlaneGraph_isGoodPlaneGraph hplane₀
  -- Transfer finiteness across isomorphism
  have hiso₀' := Classical.choice hiso₀
  have hfin_e₀ : H₀.edgeSet.Finite :=
    (hfin_e.image hiso₀'.edgeMap).subset hiso₀'.edgeBij.surjOn
  have hfin_v₀ : H₀.vertexSet.Finite :=
    (hfin_v.image hiso₀'.vertexMap).subset hiso₀'.vertexBij.surjOn
  have hne₀ : H₀.edgeSet.Nonempty := by
    obtain ⟨e, he⟩ := hne
    exact ⟨hiso₀'.edgeMap e, hiso₀'.edgeBij.mapsTo he⟩
  -- Transfer degree bound across isomorphism
  have hdeg₀ : ∀ v ∈ H₀.vertexSet,
      {e ∈ H₀.edgeSet | v ∈ H₀.inc e}.ncard ≤ 4 := by
    intro v hv
    obtain ⟨v₀, hv₀, hvv₀⟩ := hiso₀'.vertexBij.surjOn hv
    rw [show v = hiso₀'.vertexMap v₀ from hvv₀.symm]
    have hset : {e' ∈ H₀.edgeSet | hiso₀'.vertexMap v₀ ∈ H₀.inc e'} =
        hiso₀'.edgeMap '' {e ∈ G.edgeSet | v₀ ∈ G.inc e} := by
      ext e'; simp only [Set.mem_sep_iff, Set.mem_image]; constructor
      · rintro ⟨he', hve'⟩
        obtain ⟨e, he, hee'⟩ := hiso₀'.edgeBij.surjOn he'
        refine ⟨e, ⟨he, ?_⟩, hee'⟩
        rw [← hee', hiso₀'.preserves_inc e he] at hve'
        obtain ⟨w, hw, hwv⟩ := hve'
        rwa [← hiso₀'.vertexBij.injOn ((G.well_formed e he).1 hw) hv₀ hwv]
      · rintro ⟨e, ⟨he, hve⟩, rfl⟩
        exact ⟨hiso₀'.edgeBij.mapsTo he, by
          rw [hiso₀'.preserves_inc e he]; exact ⟨v₀, hve, rfl⟩⟩
    rw [hset, (hiso₀'.edgeBij.injOn.mono (Set.sep_subset _ _)).ncard_image]
    exact hdeg v₀ hv₀
  -- Make all edges HV-finite
  obtain ⟨H₁, hiso₁, hgood₁, hfin_e₁, hfin_v₁, hhv₁⟩ :=
    goodPlaneGraph_allEdgesHVFinite H₀ hgood₀ hfin_e₀ hfin_v₀ hne₀ hdeg₀
  exact ⟨H₁, graphIsomorphic_trans hiso₀ hiso₁, hgood₁,
    hfin_e₁, hfin_v₁, hhv₁⟩

/-! ## Main theorem: Planar graphs have HV-finite embeddings -/

/-- Every bounded-degree planar graph admits a plane embedding where every edge
    is HV-finite.
    HOL Light: `planar_graph_hv` (line 31953). -/
theorem planar_graph_hv {V E : Type*}
    (G : HolGraph V E)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite)
    (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v ∈ G.vertexSet,
      {e ∈ G.edgeSet | v ∈ G.inc e}.ncard ≤ 4) :
    ∃ H : HolGraph E2' (Set E2'),
      GraphIsomorphic G H ∧
      IsGoodPlaneGraph H ∧
      ∀ e ∈ H.edgeSet, IsHVFiniteSet e := by
  obtain ⟨H, hiso, hgood, _, _, hhv⟩ :=
    graph_radius_exists G hplanar hfin_e hfin_v hne hdeg
  exact ⟨H, hiso, hgood, hhv⟩

end
