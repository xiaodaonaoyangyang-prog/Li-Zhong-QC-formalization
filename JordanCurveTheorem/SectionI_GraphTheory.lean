/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionH_Symmetries
import Mathlib.Topology.UnitInterval

/-!
# Section I: Graph Theory
## HOL Light: Section I (Lines 14931–17774)

Abstract graph theory: graphs, graph isomorphism, paths, cycles,
connectivity, 2-connectivity, simple arcs, simple closed curves,
plane graphs, and planar graphs.

### Key HOL Light definitions
- `graph_vertex`, `graph_edge`, `graph_inc`: Graph structure
- `graph_iso`, `graph_isomorphic`: Graph isomorphism
- `graph_path`, `graph_cycle`: Paths and cycles in graphs
- `graph_connected`, `graph_2_connected`: Connectivity notions
- `simple_arc`, `simple_closed_curve`: Topological curve definitions
- `plane_graph`, `planar_graph`: Planarity
-/

open Set Topology unitInterval

noncomputable section

/-! ## The Euclidean plane (re-export for downstream) -/

/-- Alias for `E2`, the Euclidean plane ℝ².
    Defined in SectionA; re-exported here for downstream readability. -/
abbrev E2' := E2

/-! ## Abstract graphs -/

/-- An abstract graph with vertex type `V` and edge type `E`.
    HOL Light: `(A,B)graph_t` with `graph_vertex`, `graph_edge`, `graph_inc`.
    Each edge is incident to exactly 2 (distinct) vertices. -/
structure HolGraph (V E : Type*) where
  vertexSet : Set V
  edgeSet : Set E
  inc : E → Set V
  well_formed : ∀ e ∈ edgeSet, inc e ⊆ vertexSet ∧ (inc e).ncard = 2

/-- A graph is well-formed: every edge is incident to exactly 2 vertices. -/
theorem HolGraph.edge_has_two_vertices {V E : Type*} (G : HolGraph V E) (e : E)
    (he : e ∈ G.edgeSet) : (G.inc e).ncard = 2 :=
  (G.well_formed e he).2

/-- The two vertices of an edge. -/
theorem HolGraph.edge_pair {V E : Type*} (G : HolGraph V E) (e : E) (he : e ∈ G.edgeSet) :
    ∃ u v : V, u ≠ v ∧ G.inc e = {u, v} :=
  Set.ncard_eq_two.mp (G.well_formed e he).2

/-! ## Graph isomorphism -/

/-- Graph isomorphism: a pair of bijections preserving incidence.
    HOL Light: `graph_iso`. -/
structure GraphIso {V₁ E₁ V₂ E₂ : Type*}
    (G : HolGraph V₁ E₁) (H : HolGraph V₂ E₂) where
  vertexMap : V₁ → V₂
  edgeMap : E₁ → E₂
  vertexBij : Set.BijOn vertexMap G.vertexSet H.vertexSet
  edgeBij : Set.BijOn edgeMap G.edgeSet H.edgeSet
  preserves_inc : ∀ e ∈ G.edgeSet,
    H.inc (edgeMap e) = vertexMap '' (G.inc e)

/-- Two graphs are isomorphic.
    HOL Light: `graph_isomorphic G H`. -/
def GraphIsomorphic {V₁ E₁ V₂ E₂ : Type*}
    (G : HolGraph V₁ E₁) (H : HolGraph V₂ E₂) : Prop :=
  Nonempty (GraphIso G H)

/-- Graph isomorphism is symmetric: if `G` is isomorphic to `H`, then `H` is isomorphic to `G`. -/
theorem graphIsomorphic_symm {V₁ E₁ V₂ E₂ : Type*}
    [Nonempty V₁] [Nonempty E₁]
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂} :
    GraphIsomorphic G H → GraphIsomorphic H G := by
  rintro ⟨iso⟩
  refine ⟨⟨Function.invFunOn iso.vertexMap G.vertexSet,
    Function.invFunOn iso.edgeMap G.edgeSet,
    iso.vertexBij.symm iso.vertexBij.invOn_invFunOn.symm,
    iso.edgeBij.symm iso.edgeBij.invOn_invFunOn.symm, ?_⟩⟩
  intro e' he'
  obtain ⟨e, he, rfl⟩ := iso.edgeBij.surjOn he'
  rw [iso.edgeBij.injOn.leftInvOn_invFunOn he, iso.preserves_inc e he,
      iso.vertexBij.injOn.invFunOn_image (G.well_formed e he).1]

/-- Graph isomorphism is transitive: if `G ≅ H` and `H ≅ K`, then `G ≅ K`. -/
theorem graphIsomorphic_trans {V₁ E₁ V₂ E₂ V₃ E₃ : Type*}
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂} {K : HolGraph V₃ E₃} :
    GraphIsomorphic G H → GraphIsomorphic H K → GraphIsomorphic G K := by
  rintro ⟨iso₁⟩ ⟨iso₂⟩
  exact ⟨⟨iso₂.vertexMap ∘ iso₁.vertexMap, iso₂.edgeMap ∘ iso₁.edgeMap,
    iso₂.vertexBij.comp iso₁.vertexBij,
    iso₂.edgeBij.comp iso₁.edgeBij,
    fun e he => by
      rw [Function.comp_apply, iso₂.preserves_inc _ (iso₁.edgeBij.mapsTo he),
          iso₁.preserves_inc e he, Set.image_comp]⟩⟩

/-! ## Paths in graphs -/

/-- A path in a graph of length `n`.
    HOL Light: `graph_path G f n`. -/
structure GraphPath {V E : Type*} (G : HolGraph V E) (n : ℕ) where
  vertices : Fin (n + 1) → V
  edges : Fin n → E
  vertices_inj : Function.Injective vertices
  vertices_in : ∀ i, vertices i ∈ G.vertexSet
  edges_inj : Function.Injective edges
  edges_in : ∀ i, edges i ∈ G.edgeSet
  incidence : ∀ i : Fin n,
    G.inc (edges i) = {vertices i.castSucc, vertices i.succ}

/-- A cycle in a graph: a closed path.
    HOL Light: `graph_cycle G f n`. -/
structure GraphCycle {V E : Type*} (G : HolGraph V E) (n : ℕ) where
  vertices : Fin n → V
  edges : Fin n → E
  n_ge_3 : n ≥ 3
  vertices_inj : Function.Injective vertices
  vertices_in : ∀ i, vertices i ∈ G.vertexSet
  edges_inj : Function.Injective edges
  edges_in : ∀ i, edges i ∈ G.edgeSet
  incidence : ∀ i : Fin n,
    G.inc (edges i) = {vertices i, vertices ⟨(i + 1) % n, Nat.mod_lt _ (by omega)⟩}

/-! ## Graph connectivity -/

/-- A graph is connected if every pair of vertices is connected by a path.
    HOL Light: `graph_connected G`. -/
def HolGraph.IsConnected {V E : Type*} (G : HolGraph V E) : Prop :=
  ∀ v ∈ G.vertexSet, ∀ w ∈ G.vertexSet, v ≠ w →
    ∃ n, ∃ p : GraphPath G n, p.vertices 0 = v ∧
      p.vertices ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = w

/-- A graph is 2-connected if removing any single vertex leaves it connected.
    HOL Light: `graph_2_connected G`. -/
def HolGraph.Is2Connected {V E : Type*} (G : HolGraph V E) : Prop :=
  G.vertexSet.ncard ≥ 3 ∧
  G.IsConnected ∧
  ∀ v ∈ G.vertexSet,
    let G' : HolGraph V E := {
      vertexSet := G.vertexSet \ {v}
      edgeSet := {e ∈ G.edgeSet | v ∉ G.inc e}
      inc := G.inc
      well_formed := fun e ⟨he, hv⟩ =>
        ⟨fun _w hw => ⟨(G.well_formed e he).1 hw, fun h => hv (h ▸ hw)⟩,
         (G.well_formed e he).2⟩
    }
    G'.IsConnected

/-! ## Simple arcs and simple closed curves -/

/-- A simple arc in ℝ² is the image of an injective continuous map from [0,1].
    HOL Light: `simple_arc top2 C`. -/
def IsSimpleArc (C : Set E2') : Prop :=
  ∃ f : ℝ → E2',
    C = f '' Icc 0 1 ∧
    Continuous f ∧
    Set.InjOn f (Icc 0 1)

/-- A simple closed curve in ℝ² is the image of a continuous map from [0,1]
    that is injective on [0,1) and satisfies f(0) = f(1).
    HOL Light: `simple_closed_curve top2 C`. -/
def IsSimpleClosedCurve (C : Set E2') : Prop :=
  ∃ f : ℝ → E2',
    C = f '' Icc 0 1 ∧
    Continuous f ∧
    Set.InjOn f (Ico 0 1) ∧
    f 0 = f 1

/-- A simple arc with specified endpoints.
    HOL Light: `simple_arc_end C v v'`. -/
def IsSimpleArcEnd (C : Set E2')
    (v v' : E2') : Prop :=
  ∃ f : ℝ → E2',
    C = f '' Icc 0 1 ∧
    Continuous f ∧
    Set.InjOn f (Icc 0 1) ∧
    f 0 = v ∧ f 1 = v'

/-- Every simple arc end is a simple arc. -/
theorem isSimpleArcEnd_isSimpleArc {C : Set E2'}
    {v v' : E2'} (h : IsSimpleArcEnd C v v') :
    IsSimpleArc C := by
  obtain ⟨f, hC, hcont, hinj, _, _⟩ := h
  exact ⟨f, hC, hcont, hinj⟩

/-- A simple arc that is not a single point has well-defined endpoints. -/
theorem simpleArc_has_endpoints {C : Set E2'} (hC : IsSimpleArc C) :
    ∃ v v', IsSimpleArcEnd C v v' := by
  obtain ⟨f, hfC, hcont, hinj⟩ := hC
  exact ⟨f 0, f 1, f, hfC, hcont, hinj, rfl, rfl⟩

/-! ## Plane graphs and planar graphs -/

/-- A plane graph: a graph embedded in ℝ² where vertices are points, edges are
    simple arcs between their endpoints, and distinct edge arcs intersect only
    at shared vertices.
    HOL Light: `plane_graph G`. -/
structure IsPlaneGraph (G : HolGraph E2' (Set E2')) : Prop where
  edges_are_arcs : ∀ e ∈ G.edgeSet,
    ∃ v v', v ∈ G.inc e ∧ v' ∈ G.inc e ∧ v ≠ v' ∧ IsSimpleArcEnd e v v'
  vertex_on_edge : ∀ e ∈ G.edgeSet, ∀ v ∈ G.vertexSet,
    v ∈ e → v ∈ G.inc e
  edges_disjoint_interior : ∀ e₁ e₂, e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
    e₁ ≠ e₂ → e₁ ∩ e₂ ⊆ G.vertexSet

/-- A graph is planar if it is isomorphic to some plane graph.
    HOL Light: `planar_graph G`. -/
def IsPlanarGraph {V E : Type*} (G : HolGraph V E) : Prop :=
  ∃ H : HolGraph E2' (Set E2'),
    IsPlaneGraph H ∧ GraphIsomorphic G H

/-- Planarity is preserved under graph isomorphism. -/
theorem isPlanarGraph_of_isomorphic {V₁ E₁ V₂ E₂ : Type*}
    [Nonempty V₁] [Nonempty E₁]
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂}
    (hiso : GraphIsomorphic G H) (hG : IsPlanarGraph G) :
    IsPlanarGraph H := by
  obtain ⟨H', hplane, hGH'⟩ := hG
  exact ⟨H', hplane, graphIsomorphic_trans (graphIsomorphic_symm hiso) hGH'⟩

/-! ## Subgraphs -/

/-- A subgraph of `G` induced by a subset of edges. -/
def HolGraph.edgeSubgraph {V E : Type*} (G : HolGraph V E) (S : Set E) (hS : S ⊆ G.edgeSet) :
    HolGraph V E where
  vertexSet := {v ∈ G.vertexSet | ∃ e ∈ S, v ∈ G.inc e}
  edgeSet := S
  inc := G.inc
  well_formed := fun e he =>
    ⟨fun _v hv => ⟨(G.well_formed e (hS he)).1 hv, e, he, hv⟩, (G.well_formed e (hS he)).2⟩

/-- Subgraphs of planar graphs are planar. -/
theorem subgraph_planar {V E : Type*} (G : HolGraph V E)
    (hG : IsPlanarGraph G) (S : Set E) (hS : S ⊆ G.edgeSet) :
    IsPlanarGraph (G.edgeSubgraph S hS) := by
  obtain ⟨H, hplane, ⟨iso⟩⟩ := hG
  have hS'sub : iso.edgeMap '' S ⊆ H.edgeSet := by
    rintro _ ⟨e, heS, rfl⟩; exact iso.edgeBij.mapsTo (hS heS)
  refine ⟨H.edgeSubgraph (iso.edgeMap '' S) hS'sub, ?_, ⟨?_⟩⟩
  · -- IsPlaneGraph (H.edgeSubgraph ...)
    refine ⟨fun e he => hplane.edges_are_arcs e (hS'sub he),
      fun e he v hv hve => hplane.vertex_on_edge e (hS'sub he) v hv.1 hve,
      fun e₁ e₂ he₁ he₂ hne x hx => ?_⟩
    have hxV := hplane.edges_disjoint_interior e₁ e₂ (hS'sub he₁) (hS'sub he₂) hne hx
    exact ⟨hxV, e₁, he₁, hplane.vertex_on_edge e₁ (hS'sub he₁) x hxV hx.1⟩
  · -- GraphIso (G.edgeSubgraph S hS) (H.edgeSubgraph ...)
    exact {
      vertexMap := iso.vertexMap
      edgeMap := iso.edgeMap
      vertexBij := by
        refine ⟨fun v hv => ?_, iso.vertexBij.injOn.mono (fun _ hv => hv.1),
          fun w hw => ?_⟩
        · obtain ⟨hvG, e, heS, hve⟩ := hv
          refine ⟨iso.vertexBij.mapsTo hvG, iso.edgeMap e, ⟨e, heS, rfl⟩, ?_⟩
          rw [iso.preserves_inc e (hS heS)]
          exact Set.mem_image_of_mem _ hve
        · obtain ⟨hwH, e', ⟨e, heS, rfl⟩, hwe⟩ := hw
          rw [iso.preserves_inc e (hS heS)] at hwe
          obtain ⟨v, hve, rfl⟩ := hwe
          exact ⟨v, ⟨(G.well_formed e (hS heS)).1 hve, e, heS, hve⟩, rfl⟩
      edgeBij := (iso.edgeBij.injOn.mono hS).bijOn_image
      preserves_inc := fun e heS => iso.preserves_inc e (hS heS)
    }

/-! ## K₃,₃ graph -/

/-- The complete bipartite graph K₃,₃.
    HOL Light: `K33` (line 14976). -/
def K33 : HolGraph ℕ (Finset ℕ) where
  vertexSet := {1, 2, 3, 10, 20, 30}
  edgeSet := {{1, 10}, {2, 10}, {3, 10}, {1, 20}, {2, 20}, {3, 20},
              {1, 30}, {2, 30}, {3, 30}}
  inc := fun e => (e : Set ℕ)
  well_formed := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, by rw [Set.ncard_coe_finset]; decide⟩ <;>
      intro v hv <;>
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;>
      omega

/-! ## Piecewise functions (joinf) -/

/-- Piecewise join: `f` when `x < a`, `g` when `x ≥ a`.
    HOL Light: `joinf f g a` (metric_spaces.ml, line 7849). -/
def joinf {β : Type*} (f g : ℝ → β) (a : ℝ) (x : ℝ) : β :=
  if x < a then f x else g x

/-- On a domain strictly below the cutpoint, `joinf` equals `f`.
    HOL Light: `joinf_inj_below` (line 17177). -/
theorem joinf_injOn_below {β : Type*} {f g : ℝ → β} {a : ℝ} {S : Set ℝ}
    (hS : S ⊆ {x | x < a}) :
    Set.InjOn (joinf f g a) S ↔ Set.InjOn f S := by
  have key : ∀ z ∈ S, joinf f g a z = f z := fun z hz =>
    if_pos (show z < a from hS hz)
  constructor
  · intro h x hx y hy hfxy
    exact h hx hy (by rw [key x hx, key y hy]; exact hfxy)
  · intro h x hx y hy hxy
    rw [key x hx, key y hy] at hxy; exact h hx hy hxy

/-- On a domain at or above the cutpoint, `joinf` equals `g`.
    HOL Light: `joinf_inj_above` (line 17198). -/
theorem joinf_injOn_above {β : Type*} {f g : ℝ → β} {a : ℝ} {S : Set ℝ}
    (hS : S ⊆ {x | a ≤ x}) :
    Set.InjOn (joinf f g a) S ↔ Set.InjOn g S := by
  have key : ∀ z ∈ S, joinf f g a z = g z := fun z hz =>
    if_neg (not_lt.mpr (show a ≤ z from hS hz))
  constructor
  · intro h x hx y hy hgxy
    exact h hx hy (by rw [key x hx, key y hy]; exact hgxy)
  · intro h x hx y hy hxy
    rw [key x hx, key y hy] at hxy; exact h hx hy hxy

/-- Image of `joinf` below cutpoint equals image of `f`.
    HOL Light: `joinf_image_below` (line 17216). -/
theorem joinf_image_below {β : Type*} {f g : ℝ → β} {a : ℝ} {S : Set ℝ}
    (hS : S ⊆ {x | x < a}) :
    joinf f g a '' S = f '' S := by
  ext y; simp only [Set.mem_image]; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (if_pos (show x < a from hS hx)).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, if_pos (show x < a from hS hx)⟩

/-- Image of `joinf` above cutpoint equals image of `g`.
    HOL Light: `joinf_image_above` (line 17237). -/
theorem joinf_image_above {β : Type*} {f g : ℝ → β} {a : ℝ} {S : Set ℝ}
    (hS : S ⊆ {x | a ≤ x}) :
    joinf f g a '' S = g '' S := by
  ext y; simp only [Set.mem_image]; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (if_neg (not_lt.mpr (show a ≤ x from hS hx))).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, if_neg (not_lt.mpr (show a ≤ x from hS hx))⟩

/-- Injectivity on a union follows from injectivity on each part with disjoint
    images. HOL Light: `inj_split` (line 17144). -/
theorem injOn_union_of_disjoint_images {α β : Type*} {A B : Set α}
    {f : α → β}
    (hfA : Set.InjOn f A) (hfB : Set.InjOn f B)
    (hdisj : Disjoint (f '' A) (f '' B)) :
    Set.InjOn f (A ∪ B) := by
  intro x hx y hy hfxy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact hfA hxA hyA hfxy
  · exact absurd (⟨y, hyB, hfxy.symm⟩ : f x ∈ f '' B)
      (Set.disjoint_left.mp hdisj ⟨x, hxA, rfl⟩)
  · exact absurd (⟨x, hxB, hfxy⟩ : f y ∈ f '' B)
      (Set.disjoint_left.mp hdisj ⟨y, hyA, rfl⟩)
  · exact hfB hxB hyB hfxy

/-! ## Affine lines and segments -/

/-- The affine line through `x` and `y`: {t • x + (1-t) • y | t : ℝ}.
    HOL Light: `mk_line x y` (misc_defs_and_lemmas.ml, line 1824). -/
def mkLine (x y : E2') : Set E2' :=
  {z | ∃ t : ℝ, z = t • x + (1 - t) • y}

/-- Two distinct points on a line determine it.
    HOL Light: `mk_line_2` (line 15323). -/
theorem mkLine_eq_of_mem {x y p q : E2'}
    (hp : p ∈ mkLine x y) (hq : q ∈ mkLine x y) (hpq : p ≠ q) :
    mkLine x y = mkLine p q := by
  obtain ⟨sp, rfl⟩ := hp
  obtain ⟨sq, rfl⟩ := hq
  have hne : sp ≠ sq := fun h => hpq (by rw [h])
  have hsub_ne : sp - sq ≠ 0 := sub_ne_zero.mpr hne
  ext z; simp only [mkLine, Set.mem_setOf_eq]; constructor
  · rintro ⟨t, rfl⟩
    set u := (t - sq) / (sp - sq)
    have hu : t = u * sp + (1 - u) * sq := by simp only [u]; field_simp; ring
    refine ⟨u, ?_⟩; rw [hu]; module
  · rintro ⟨u, rfl⟩
    exact ⟨u * sp + (1 - u) * sq, by module⟩

/-- Characterization of `segment ℝ x y` via a single parameter `t ∈ [0,1]`.
    This bridges mathlib's two-parameter definition with the one-parameter form
    used in HOL Light's `mk_segment`. -/
theorem mem_segment_iff_param {x y z : E2'} :
    z ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • x + (1 - t) • y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a, ha, by linarith, by rw [show 1 - a = b from by linarith]⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, 1 - t, ht0, sub_nonneg.mpr ht1, by ring, rfl⟩

/-- Open balls in ℝ² are convex: if two points are in a ball, so is the
    segment between them.
    HOL Light: `openball_mk_segment_end` (line 15615). -/
theorem segment_subset_ball {x : E2'} {e : ℝ} {u v : E2'}
    (hu : u ∈ Metric.ball x e) (hv : v ∈ Metric.ball x e) :
    segment ℝ u v ⊆ Metric.ball x e :=
  (convex_ball x e).segment_subset hu hv

/-- A segment between distinct points is a simple arc (injective continuous
    image of [0,1]).
    HOL Light: `mk_segment_inj_image` (line 15687). -/
theorem segment_isSimpleArc {x y : E2'} (hxy : x ≠ y) :
    IsSimpleArc (segment ℝ x y) := by
  refine ⟨fun t : ℝ => t • x + (1 - t) • y, ?_, ?_, ?_⟩
  · ext z; simp only [Set.mem_image, mem_segment_iff_param]
    constructor
    · rintro ⟨t, ht0, ht1, rfl⟩; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩; exact ⟨t, ht0, ht1, rfl⟩
  · fun_prop
  · intro s hs t ht hst
    have key : (s - t) • (x - y) = (0 : E2') := by
      have h := sub_eq_zero.mpr hst
      rwa [show s • x + (1 - s) • y - (t • x + (1 - t) • y) =
        (s - t) • (x - y) from by module] at h
    rcases smul_eq_zero.mp key with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) hxy

/-! ## Simple polygonal arcs -/

/-- A predicate for sets of horizontal/vertical lines.
    HOL Light: `hv_line` (line 15031). -/
def IsHVLine (E : Set (Set E2')) : Prop :=
  ∀ e ∈ E, ∃ p q : ℝ × ℝ,
    e = mkLine (point p) (point q) ∧ (p.1 = q.1 ∨ p.2 = q.2)

/-- A simple polygonal arc: a simple arc covered by finitely many edges
    satisfying a predicate `PE`.
    HOL Light: `simple_polygonal_arc PE C` (line 15021). -/
def IsSimplePolygonalArc (PE : Set (Set E2') → Prop) (C : Set E2') : Prop :=
  IsSimpleArc C ∧ ∃ E : Finset (Set E2'), C ⊆ ⋃₀ (E : Set (Set E2')) ∧ PE (E : Set (Set E2'))

/-- A nondegenerate horizontal segment is a simple polygonal arc with HV edges.
    HOL Light: `h_simple_polygonal` (line 15841). -/
theorem h_simple_polygonal {x : E2'} {e : ℝ} (he : e ≠ 0) :
    IsSimplePolygonalArc IsHVLine
      (segment ℝ x (point (x 0 + e, x 1))) := by
  set y := point (x 0 + e, x 1) with hy_def
  have hxy : x ≠ y := by
    intro heq
    apply he
    have h0 : x 0 = y 0 := congrArg (· 0) heq
    simp only [hy_def, point_coord_zero] at h0; linarith
  constructor
  · exact segment_isSimpleArc hxy
  · refine ⟨{mkLine x y}, ?_, ?_⟩
    · intro z hz
      obtain ⟨t, _, _, htdef⟩ := mem_segment_iff_param.mp hz
      simp only [Set.mem_sUnion, Finset.coe_singleton, Set.mem_singleton_iff]
      exact ⟨mkLine x y, rfl, t, htdef⟩
    · intro L hL
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hL; subst hL
      have hx_eq : x = point (x 0, x 1) := by ext i; fin_cases i <;> simp
      rw [hx_eq]
      exact ⟨(x 0, x 1), (x 0 + e, x 1), rfl, Or.inr rfl⟩

/-! ## Arc reparametrization -/

/-- Reparametrize an injective arc to a new interval with reversed orientation.
    HOL Light: `arc_reparameter_rev` (line 16356). -/
theorem arc_reparameter_rev {f : ℝ → E2'} {a b c d : ℝ}
    (hcont : Continuous f) (hinj : Set.InjOn f (Icc c d))
    (hab : a < b) (hcd : c < d) :
    ∃ g : ℝ → E2',
      Continuous g ∧
      Set.InjOn g (Icc a b) ∧
      g a = f d ∧ g b = f c ∧
      f '' Icc c d = g '' Icc a b := by
  have hba_pos : (0 : ℝ) < b - a := by linarith
  have hba_ne : b - a ≠ 0 := ne_of_gt hba_pos
  have hdc_ne : c - d ≠ 0 := by linarith
  -- Affine map φ(t) = d + (t - a) * (c - d) / (b - a), so φ(a) = d, φ(b) = c
  set φ : ℝ → ℝ := fun t => d + (t - a) * (c - d) / (b - a) with hφ_def
  have hφa : φ a = d := by simp [hφ_def]
  have hφb : φ b = c := by simp only [hφ_def]; field_simp; ring
  have hφ_maps : ∀ t ∈ Icc a b, φ t ∈ Icc c d := by
    intro t ⟨hat, htb⟩
    have h_numer_nonpos : (t - a) * (c - d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have h_frac : (t - a) * (c - d) / (b - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h_numer_nonpos hba_pos.le
    have h_frac_ge : c - d ≤ (t - a) * (c - d) / (b - a) := by
      rw [le_div_iff₀ hba_pos]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hφ_inj : Set.InjOn φ (Icc a b) := by
    intro s _ t _ heq
    have h1 : (s - a) * (c - d) / (b - a) = (t - a) * (c - d) / (b - a) := by
      simp only [hφ_def] at heq; linarith
    have h2 : (s - a) * (c - d) = (t - a) * (c - d) := by
      rwa [div_left_inj' hba_ne] at h1
    linarith [mul_right_cancel₀ hdc_ne h2]
  refine ⟨f ∘ φ, hcont.comp (by fun_prop), hinj.comp hφ_inj hφ_maps, ?_, ?_, ?_⟩
  · change f (φ a) = f d; rw [hφa]
  · change f (φ b) = f c; rw [hφb]
  · rw [Set.image_comp]; congr 1
    ext u; constructor
    · -- Icc c d ⊆ φ '' Icc a b
      intro hu
      obtain ⟨hcu, hud⟩ := Set.mem_Icc.mp hu
      set t₀ := a + (u - d) * (b - a) / (c - d)
      refine ⟨t₀, ⟨?_, ?_⟩, ?_⟩
      · -- t₀ ≥ a: (u-d)*(b-a)/(c-d) ≥ 0 since u-d ≤ 0, b-a > 0, c-d < 0
        linarith [div_nonneg_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (by linarith : u - d ≤ 0) hba_pos.le)
          (by linarith : c - d ≤ 0)]
      · -- t₀ ≤ b: (u-d)*(b-a)/(c-d) ≤ b-a
        have : (u - d) * (b - a) / (c - d) ≤ b - a := by
          rw [div_le_iff_of_neg (by linarith : c - d < 0)]
          nlinarith
        linarith
      · -- φ(t₀) = u
        simp only [hφ_def, t₀]; field_simp; ring
    · -- φ '' Icc a b ⊆ Icc c d
      rintro ⟨t, ht, rfl⟩; exact hφ_maps t ht

/-- Reparametrize an injective arc to a new interval with same orientation.
    HOL Light: `arc_reparameter_gen` (line 16491). -/
theorem arc_reparameter_gen {f : ℝ → E2'} {a b c d : ℝ}
    (hcont : Continuous f) (hinj : Set.InjOn f (Icc c d))
    (hab : a < b) (hcd : c < d) :
    ∃ g : ℝ → E2',
      Continuous g ∧
      Set.InjOn g (Icc a b) ∧
      g a = f c ∧ g b = f d ∧
      f '' Icc c d = g '' Icc a b := by
  have hba_pos : (0 : ℝ) < b - a := by linarith
  have hba_ne : b - a ≠ 0 := ne_of_gt hba_pos
  have hdc_pos : (0 : ℝ) < d - c := by linarith
  set φ : ℝ → ℝ := fun t => c + (t - a) * (d - c) / (b - a) with hφ_def
  have hφa : φ a = c := by simp [hφ_def]
  have hφb : φ b = d := by simp only [hφ_def]; field_simp; ring
  have hφ_maps : ∀ t ∈ Icc a b, φ t ∈ Icc c d := by
    intro t ⟨hat, htb⟩
    have h_numer_nonneg : 0 ≤ (t - a) * (d - c) :=
      mul_nonneg (by linarith) (by linarith)
    have h_frac : 0 ≤ (t - a) * (d - c) / (b - a) :=
      div_nonneg h_numer_nonneg hba_pos.le
    have h_frac_le : (t - a) * (d - c) / (b - a) ≤ d - c := by
      rw [div_le_iff₀ hba_pos]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hφ_inj : Set.InjOn φ (Icc a b) := by
    intro s _ t _ heq
    have h1 : (s - a) * (d - c) / (b - a) = (t - a) * (d - c) / (b - a) := by
      simp only [hφ_def] at heq; linarith
    have h2 : (s - a) * (d - c) = (t - a) * (d - c) := by
      rwa [div_left_inj' hba_ne] at h1
    linarith [mul_right_cancel₀ (ne_of_gt hdc_pos) h2]
  refine ⟨f ∘ φ, hcont.comp (by fun_prop), hinj.comp hφ_inj hφ_maps, ?_, ?_, ?_⟩
  · change f (φ a) = f c; rw [hφa]
  · change f (φ b) = f d; rw [hφb]
  · rw [Set.image_comp]; congr 1
    ext u; constructor
    · intro hu
      obtain ⟨hcu, hud⟩ := Set.mem_Icc.mp hu
      set t₀ := a + (u - c) * (b - a) / (d - c)
      refine ⟨t₀, ⟨?_, ?_⟩, ?_⟩
      · linarith [div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ u - c) hba_pos.le)
          hdc_pos.le]
      · have : (u - c) * (b - a) / (d - c) ≤ b - a := by
          rw [div_le_iff₀ hdc_pos]; nlinarith
        linarith
      · simp only [hφ_def, t₀]; field_simp; ring
    · rintro ⟨t, ht, rfl⟩; exact hφ_maps t ht

/-- Restrict an arc to a subinterval and reparametrize.
    HOL Light: `arc_restrict` (line 17091). -/
theorem arc_restrict {f : ℝ → E2'} {a b c d t t' : ℝ}
    (htt' : c ≤ t) (htt'' : t < t') (ht'd : t' ≤ d)
    (hab : a < b) (himg : Set.InjOn f (Icc c d))
    (hcont : Continuous f) :
    ∃ g : ℝ → E2',
      g '' Icc a b = f '' Icc t t' ∧
      g a = f t ∧ g b = f t' ∧
      Set.InjOn g (Icc a b) ∧
      Continuous g := by
  have htt'_le : t ≤ t' := le_of_lt htt''
  have hinj_sub : Set.InjOn f (Icc t t') :=
    himg.mono (Icc_subset_Icc htt' ht'd)
  obtain ⟨g, hg_cont, hg_inj, hga, hgb, himg_eq⟩ :=
    arc_reparameter_gen hcont hinj_sub hab htt''
  exact ⟨g, himg_eq.symm, hga, hgb, hg_inj, hg_cont⟩

/-! ## First hitting time -/

/-- First parameter where the image of a continuous function hits a closed set.
    HOL Light: `preimage_first` (line 17037). -/
theorem preimage_first {f : ℝ → E2'} {a b : ℝ} {C : Set E2'}
    (hcont : ContinuousOn f (Icc a b))
    (hC : IsClosed C) (hmeet : (f '' Icc a b ∩ C).Nonempty) :
    ∃ t, t ∈ Icc a b ∧ f t ∈ C ∧ ∀ s, s ∈ Ico a t → f s ∉ C := by
  -- The preimage S = {t ∈ [a,b] | f(t) ∈ C} is closed and nonempty in [a,b]
  set S := {t ∈ Icc a b | f t ∈ C} with hS_def
  have hS_nonempty : S.Nonempty := by
    obtain ⟨z, ⟨⟨t, ht, rfl⟩, hz⟩⟩ := hmeet
    exact ⟨t, ht, hz⟩
  have hS_bdd_below : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hS_closed : IsClosed S := by
    have : S = Icc a b ∩ f ⁻¹' C := by ext t; simp [hS_def]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
  -- Take t₀ = inf S
  set t₀ := sInf S with ht₀_def
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd_below
  refine ⟨t₀, ht₀_mem.1, ht₀_mem.2, fun s hs => ?_⟩
  intro hfs
  have hs_mem : s ∈ S := ⟨⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 ht₀_mem.1.2)⟩, hfs⟩
  have := csInf_le hS_bdd_below hs_mem
  linarith [hs.2]

end
