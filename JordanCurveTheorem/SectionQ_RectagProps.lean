/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionP_Automation

/-!
# Section Q: Rectagon Properties
## HOL Light: Section Q (Lines 34153–34878)

Lines through points, hyperplane intersections, graph isomorphism
transfer lemmas, point formulas for transformations, hyperplane images,
and the main `graph_support_init` theorem.
-/

open Set Metric Topology Function

noncomputable section

/-! ## mkLine and hyperplane relationships -/

/-- If two points have equal first coordinates, the line through them is
    contained in the vertical hyperplane at that coordinate.
    HOL Light: `mk_line_hyper2_fst` (line 34156). -/
theorem mkLine_hyper2_fst (x y : ℝ × ℝ) (h : x.1 = y.1) :
    mkLine (point x) (point y) ⊆ hyperplane2 0 x.1 := by
  by_cases hxy : x = y
  · subst hxy; rw [mkLine_self]; intro z hz; simp only [mem_singleton_iff] at hz; subst hz
    simp [hyperplane2]
  · have hne : x.2 ≠ y.2 := fun h2 => hxy (Prod.ext h h2)
    rw [show mkLine (point x) (point y) = hyperplane2 0 x.1 from by
      rw [← mkLine_eq_hyperplane2_0 x.1]
      exact (mkLine_eq_of_mem
        (by rw [mkLine_eq_hyperplane2_0]; simp [hyperplane2])
        (by rw [mkLine_eq_hyperplane2_0]; simp [hyperplane2, h])
        (fun heq => hne (congr_arg Prod.snd (point_injective heq)))).symm]

/-- If two points have equal second coordinates, the line through them is
    contained in the horizontal hyperplane at that coordinate.
    HOL Light: `mk_line_hyper2_snd` (line 34183). -/
theorem mkLine_hyper2_snd (x y : ℝ × ℝ) (h : x.2 = y.2) :
    mkLine (point x) (point y) ⊆ hyperplane2 1 x.2 := by
  by_cases hxy : x = y
  · subst hxy; rw [mkLine_self]; intro z hz; simp only [mem_singleton_iff] at hz; subst hz
    simp [hyperplane2]
  · have hne : x.1 ≠ y.1 := fun h1 => hxy (Prod.ext h1 h)
    rw [show mkLine (point x) (point y) = hyperplane2 1 x.2 from by
      rw [← mkLine_eq_hyperplane2_1 x.2]
      exact (mkLine_eq_of_mem
        (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2])
        (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2, h])
        (fun heq => hne (congr_arg Prod.fst (point_injective heq)))).symm]

/-- Every element of an HV-line set is contained in some hyperplane.
    HOL Light: `hv_line_hyper` (line 34207). -/
theorem hv_line_hyper {E : Set (Set E2')} {e : Set E2'}
    (hHV : IsHVLine E) (he : e ∈ E) :
    ∃ z, e ⊆ hyperplane2 0 z ∨ e ⊆ hyperplane2 1 z := by
  obtain ⟨p, q, rfl, hpq⟩ := hHV e he
  cases hpq with
  | inl hfst => exact ⟨p.1, Or.inl (mkLine_hyper2_fst p q hfst)⟩
  | inr hsnd => exact ⟨p.2, Or.inr (mkLine_hyper2_snd p q hsnd)⟩

/-- A finite HV-line set can be refined to a finite set of hyperplanes
    with the same union coverage.
    HOL Light: `hv_line_hyper2` (line 34231). -/
theorem hv_line_hyper2 {E : Set (Set E2')} (hHV : IsHVLine E) (hfin : E.Finite) :
    ∃ E' : Set (Set E2'), ⋃₀ E ⊆ ⋃₀ E' ∧ E'.Finite ∧
      ∀ e ∈ E', ∃ z, e = hyperplane2 0 z ∨ e = hyperplane2 1 z := by
  have choice : ∀ e : Set E2', ∃ H : Set E2',
      (e ∈ E → e ⊆ H) ∧ (∃ z, H = hyperplane2 0 z ∨ H = hyperplane2 1 z) := by
    intro e; by_cases he : e ∈ E
    · obtain ⟨z, hz⟩ := hv_line_hyper hHV he
      cases hz with
      | inl h => exact ⟨hyperplane2 0 z, fun _ => h, z, Or.inl rfl⟩
      | inr h => exact ⟨hyperplane2 1 z, fun _ => h, z, Or.inr rfl⟩
    · exact ⟨hyperplane2 0 0, fun h => absurd h he, 0, Or.inl rfl⟩
  choose f hf_sub hf_hyp using choice
  refine ⟨f '' E, ?_, hfin.image f, ?_⟩
  · intro x hx
    obtain ⟨e, he, hex⟩ := mem_sUnion.mp hx
    exact mem_sUnion.mpr ⟨f e, mem_image_of_mem f he, hf_sub e he hex⟩
  · rintro _ ⟨e, _, rfl⟩; exact hf_hyp e

/-! ## Graph isomorphism transfer lemmas -/

/-- Graph isomorphism preserves edge set finiteness.
    HOL Light: `finite_graph_edge` (line 34265). -/
theorem finite_graph_edge {V₁ E₁ V₂ E₂ : Type*}
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂}
    (hfin : G.edgeSet.Finite) (hiso : GraphIsomorphic G H) :
    H.edgeSet.Finite := by
  obtain ⟨f⟩ := hiso
  exact (hfin.image f.edgeMap).subset f.edgeBij.surjOn

/-- Graph isomorphism preserves vertex set finiteness.
    HOL Light: `finite_graph_vertex` (line 34274). -/
theorem finite_graph_vertex {V₁ E₁ V₂ E₂ : Type*}
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂}
    (hfin : G.vertexSet.Finite) (hiso : GraphIsomorphic G H) :
    H.vertexSet.Finite := by
  obtain ⟨f⟩ := hiso
  exact (hfin.image f.vertexMap).subset f.vertexBij.surjOn

/-- Graph isomorphism preserves edge set nonemptiness.
    HOL Light: `graph_edge_nonempty` (line 34283). -/
theorem graph_edge_nonempty {V₁ E₁ V₂ E₂ : Type*}
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂}
    (hne : G.edgeSet.Nonempty) (hiso : GraphIsomorphic G H) :
    H.edgeSet.Nonempty := by
  obtain ⟨f⟩ := hiso
  obtain ⟨e, he⟩ := hne
  exact ⟨f.edgeMap e, f.edgeBij.mapsTo he⟩

/-- The edge-around set is finite if the edge set is finite.
    HOL Light: `graph_edge_around_finite` (line 34294). -/
theorem HolGraph.edgeAround_finite {V E : Type*} (G : HolGraph V E)
    (v : V) (hfin : G.edgeSet.Finite) :
    (G.edgeAround v).Finite :=
  hfin.subset (fun _e he => he.1)

/-- Graph isomorphism preserves the degree-at-most-4 property.
    HOL Light: `graph_edge_around4` (line 34305). -/
theorem graphIso_edgeAround_le4 {V₁ E₁ V₂ E₂ : Type*}
    {G : HolGraph V₁ E₁} {H : HolGraph V₂ E₂}
    (hfin : G.edgeSet.Finite)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4)
    (hiso : GraphIsomorphic G H) :
    ∀ v, (H.edgeAround v).ncard ≤ 4 := by
  obtain ⟨f⟩ := hiso
  intro v
  by_cases hv : v ∈ H.vertexSet
  · -- v is a vertex of H: find preimage v' via the bijection
    obtain ⟨v', hv', rfl⟩ := f.vertexBij.surjOn hv
    rw [G.iso_edgeAround H f v' hv']
    calc (f.edgeMap '' G.edgeAround v').ncard
        ≤ (G.edgeAround v').ncard := Set.ncard_image_le (G.edgeAround_finite v' hfin)
      _ ≤ 4 := hdeg v'
  · -- v is not a vertex: edgeAround is empty
    rw [H.edgeAround_empty v hv, Set.ncard_empty]
    omega

/-! ## Hyperplane support for planar graphs -/

/-- A planar graph with bounded degree can be realized as a good plane graph
    whose edges and vertices are supported by hyperplanes.
    HOL Light: `graph_near_support` (line 34338). -/
theorem graph_near_support {V E : Type*} (G : HolGraph V E)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    ∃ (H : HolGraph E2' (Set E2')) (S : Set (Set E2')),
      GraphIsomorphic G H ∧ S.Finite ∧ IsGoodPlaneGraph H ∧
      (∀ e ∈ H.edgeSet, e ⊆ ⋃₀ S) ∧
      (∀ v ∈ H.vertexSet, hyperplane2 0 (v 0) ∈ S ∧ hyperplane2 1 (v 1) ∈ S) ∧
      (∀ e ∈ S, ∃ z, e = hyperplane2 0 z ∨ e = hyperplane2 1 z) := by
  -- Step 1: Get H with good plane graph and HV-finite edges
  obtain ⟨H, hiso, hgood, hhvf⟩ :=
    planar_graph_hv G hplanar hfin_e hfin_v hne (fun v hv => hdeg v)
  -- Step 2: For each edge, choose a finite hyperplane cover via hv_line_hyper2
  have hedge : ∀ e : Set E2', ∃ E' : Set (Set E2'),
      (e ∈ H.edgeSet → e ⊆ ⋃₀ E') ∧ E'.Finite ∧
      (∀ e' ∈ E', ∃ z, e' = hyperplane2 0 z ∨ e' = hyperplane2 1 z) := by
    intro e; by_cases he : e ∈ H.edgeSet
    · obtain ⟨Ef, hEf_sub, hEf_hv⟩ := hhvf e he
      obtain ⟨E', hE'_sub, hE'_fin, hE'_hyp⟩ := hv_line_hyper2 hEf_hv (Ef.finite_toSet)
      exact ⟨E', fun _ => hEf_sub.trans hE'_sub, hE'_fin, hE'_hyp⟩
    · exact ⟨∅, fun h => absurd h he, finite_empty, fun _ h => (h.elim)⟩
  choose Ef hEf_sub hEf_fin hEf_hyp using hedge
  -- Step 3: Construct the combined set S
  have hH_fin_e : H.edgeSet.Finite := finite_graph_edge hfin_e hiso
  have hH_fin_v : H.vertexSet.Finite := finite_graph_vertex hfin_v hiso
  let A := (fun v : E2' => hyperplane2 0 (v 0)) '' H.vertexSet
  let B := (fun v : E2' => hyperplane2 1 (v 1)) '' H.vertexSet
  let C := ⋃₀ (Ef '' H.edgeSet)
  refine ⟨H, A ∪ B ∪ C, hiso, ?_, hgood, ?_, ?_, ?_⟩
  · -- S is finite
    apply Set.Finite.union
    · exact (hH_fin_v.image _).union (hH_fin_v.image _)
    · apply Set.Finite.sUnion (hH_fin_e.image Ef)
      rintro _ ⟨e, _, rfl⟩; exact hEf_fin e
  · -- edges ⊆ ⋃₀ S
    intro e he
    calc e ⊆ ⋃₀ Ef e := hEf_sub e he
      _ ⊆ ⋃₀ C := Set.sUnion_mono (Set.subset_sUnion_of_mem (Set.mem_image_of_mem Ef he))
      _ ⊆ ⋃₀ (A ∪ B ∪ C) := Set.sUnion_mono (Set.subset_union_right)
  · -- vertices have their hyperplanes in S
    intro v hv; constructor
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_image_of_mem _ hv))
    · exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_image_of_mem _ hv))
  · -- all elements of S are hyperplanes
    intro e he
    rcases he with (⟨_, hv, rfl⟩ | ⟨_, hv, rfl⟩) | hC
    · exact ⟨_, Or.inl rfl⟩
    · exact ⟨_, Or.inr rfl⟩
    · obtain ⟨Ee, ⟨e', _, rfl⟩, he⟩ := mem_sUnion.mp hC
      exact hEf_hyp e' e he

/-! ## Point formulas for transformations -/

/-- Point formula for horizontal translation.
    HOL Light: `h_translate_point` (line 34441). -/
@[simp] theorem hTranslate_point (u v r : ℝ) :
    hTranslate r (point (u, v)) = point (u + r, v) := by
  ext i; simp only [hTranslate]; fin_cases i <;>
    simp [point, WithLp.equiv, Matrix.vecHead, Matrix.vecTail]

/-- Point formula for vertical translation.
    HOL Light: `v_translate_point` (line 34449). -/
@[simp] theorem vTranslate_point (u v r : ℝ) :
    vTranslate r (point (u, v)) = point (u, v + r) := by
  ext i; simp only [vTranslate]; fin_cases i <;>
    simp [point, WithLp.equiv, Matrix.vecHead, Matrix.vecTail]

/-! ## Hyperplane images under translations -/

/-- Horizontal translation shifts vertical hyperplanes.
    HOL Light: `hyperplane1_h_translate` (line 34457). -/
theorem hyperplane1_hTranslate (z r : ℝ) :
    hTranslate r '' hyperplane2 0 z = hyperplane2 0 (z + r) := by
  rw [← mkLine_eq_hyperplane2_0 z, ← mkLine_eq_hyperplane2_0 (z + r)]
  rw [(hTranslate_vCompat r) (z, 0) (z, 1) rfl]
  simp

/-- Horizontal translation preserves horizontal hyperplanes.
    HOL Light: `hyperplane2_h_translate` (line 34468). -/
theorem hyperplane2_hTranslate (z r : ℝ) :
    hTranslate r '' hyperplane2 1 z = hyperplane2 1 z := by
  ext w; simp only [Set.mem_image, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [hTranslate, Fin.isValue, WithLp.equiv_symm_apply, WithLp.toLp_add,
      WithLp.toLp_ofLp, PiLp.add_apply, one_ne_zero, ↓reduceIte, add_zero]
    exact hp
  · intro hw
    refine ⟨hTranslate (-r) w, ?_, ?_⟩
    · simp only [hTranslate, Fin.isValue, WithLp.equiv_symm_apply, WithLp.toLp_add,
        WithLp.toLp_ofLp, PiLp.add_apply, one_ne_zero, ↓reduceIte, add_zero]
      exact hw
    · have := hTranslate_leftInverse (-r) w; simp only [neg_neg] at this; exact this

/-- Vertical translation shifts horizontal hyperplanes.
    HOL Light: `hyperplane2_v_translate` (line 34487). -/
theorem hyperplane2_vTranslate (z r : ℝ) :
    vTranslate r '' hyperplane2 1 z = hyperplane2 1 (z + r) := by
  rw [← mkLine_eq_hyperplane2_1 z, ← mkLine_eq_hyperplane2_1 (z + r)]
  rw [(vTranslate_hCompat r) (0, z) (1, z) rfl]
  simp

/-- Vertical translation preserves vertical hyperplanes.
    HOL Light: `hyperplane1_v_translate` (line 34498). -/
theorem hyperplane1_vTranslate (z r : ℝ) :
    vTranslate r '' hyperplane2 0 z = hyperplane2 0 z := by
  ext w; simp only [Set.mem_image, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [vTranslate, Fin.isValue, WithLp.equiv_symm_apply, WithLp.toLp_add,
      WithLp.toLp_ofLp, PiLp.add_apply, zero_ne_one, ↓reduceIte, add_zero]
    exact hp
  · intro hw
    refine ⟨vTranslate (-r) w, ?_, ?_⟩
    · simp only [vTranslate, Fin.isValue, WithLp.equiv_symm_apply, WithLp.toLp_add,
        WithLp.toLp_ofLp, PiLp.add_apply, zero_ne_one, ↓reduceIte, add_zero]
      exact hw
    · have := vTranslate_leftInverse (-r) w; simp only [neg_neg] at this; exact this

/-! ## Point formulas for scaling -/

/-- Point formula for r_scale.
    HOL Light: `r_scale_point` (line 34534). -/
@[simp] theorem rScale_point (r u v : ℝ) :
    rScale r (point (u, v)) = point (if 0 < u then r * u else u, v) := by
  simp only [rScale, point_coord_zero, point_coord_one]; split_ifs <;> rfl

/-- Point formula for u_scale.
    HOL Light: `u_scale_point` (line 34543). -/
@[simp] theorem uScale_point (r u v : ℝ) :
    uScale r (point (u, v)) = point (u, if 0 < v then r * v else v) := by
  simp only [uScale, point_coord_zero, point_coord_one]; split_ifs <;> rfl

/-! ## Hyperplane images under scaling -/

/-- r_scale preserves horizontal hyperplanes.
    HOL Light: `hyperplane2_r_scale` (line 34550). -/
theorem hyperplane2_rScale {r : ℝ} (hr : 0 < r) (z : ℝ) :
    rScale r '' hyperplane2 1 z = hyperplane2 1 z := by
  ext w; simp only [Set.mem_image, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨p, hp, rfl⟩; simp only [rScale]; split_ifs <;> simp [hp]
  · intro hw; refine ⟨rScale r⁻¹ w, by
      simp only [rScale]; split_ifs <;> simp [hw], ?_⟩
    have := rScale_leftInverse (inv_pos.mpr hr) w; simp only [inv_inv] at this; exact this

/-- r_scale acts on vertical hyperplanes.
    HOL Light: `hyperplane1_r_scale` (line 34577). -/
theorem hyperplane1_rScale {r : ℝ} (hr : 0 < r) (z : ℝ) :
    rScale r '' hyperplane2 0 z = hyperplane2 0 (if 0 < z then r * z else z) := by
  rw [← mkLine_eq_hyperplane2_0 z, ← mkLine_eq_hyperplane2_0 (if 0 < z then r * z else z)]
  rw [(rScale_vCompat hr) (z, 0) (z, 1) rfl]
  simp

/-- u_scale preserves vertical hyperplanes.
    HOL Light: `hyperplane1_u_scale` (line 34591). -/
theorem hyperplane1_uScale {r : ℝ} (hr : 0 < r) (z : ℝ) :
    uScale r '' hyperplane2 0 z = hyperplane2 0 z := by
  ext w; simp only [Set.mem_image, hyperplane2, Set.mem_setOf_eq]; constructor
  · rintro ⟨p, hp, rfl⟩; simp only [uScale]; split_ifs <;> simp [hp]
  · intro hw; refine ⟨uScale r⁻¹ w, by
      simp only [uScale]; split_ifs <;> simp [hw], ?_⟩
    have := uScale_leftInverse (inv_pos.mpr hr) w; simp only [inv_inv] at this; exact this

/-- u_scale acts on horizontal hyperplanes.
    HOL Light: `hyperplane2_u_scale` (line 34618). -/
theorem hyperplane2_uScale {r : ℝ} (hr : 0 < r) (z : ℝ) :
    uScale r '' hyperplane2 1 z = hyperplane2 1 (if 0 < z then r * z else z) := by
  rw [← mkLine_eq_hyperplane2_1 z, ← mkLine_eq_hyperplane2_1 (if 0 < z then r * z else z)]
  rw [(uScale_hCompat hr) (0, z) (1, z) rfl]
  simp

/-! ## homeomorphism_compose -/

-- HOL Light: `homeomorphism_compose` (line 34631).
-- Mathlib equivalent: `Homeomorph.trans` composes two `E2' ≃ₜ E2'`.

/-! ## Hyperplane injectivity -/

/-- Vertical hyperplanes are injective in their parameter.
    HOL Light: `hyperplane1_inj` (line 34653). -/
theorem hyperplane2_0_injective : Injective (hyperplane2 0) := by
  intro z w h
  have hmem : point (z, 0) ∈ hyperplane2 0 z := by simp [hyperplane2]
  rw [h] at hmem
  simpa [hyperplane2] using hmem

/-- Horizontal hyperplanes are injective in their parameter.
    HOL Light: `hyperplane2_inj` (line 34668). -/
theorem hyperplane2_1_injective : Injective (hyperplane2 1) := by
  intro z w h
  have hmem : point (0, z) ∈ hyperplane2 1 z := by simp [hyperplane2]
  rw [h] at hmem
  simpa [hyperplane2] using hmem

/-! ## Main result: graph support with positive coordinates -/

/-- A planar graph with bounded degree can be realized as a good plane graph
    supported by hyperplanes with strictly positive parameters.
    HOL Light: `graph_support_init` (line 34685). -/
theorem graph_support_init {V E : Type*} (G : HolGraph V E)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    ∃ (H : HolGraph E2' (Set E2')) (S : Set (Set E2')),
      GraphIsomorphic G H ∧ S.Finite ∧ IsGoodPlaneGraph H ∧
      (∀ e ∈ H.edgeSet, e ⊆ ⋃₀ S) ∧
      (∀ v ∈ H.vertexSet, hyperplane2 0 (v 0) ∈ S ∧ hyperplane2 1 (v 1) ∈ S) ∧
      (∀ e ∈ S, ∃ z, 0 < z ∧
        (e = hyperplane2 0 z ∨ e = hyperplane2 1 z)) := by
  -- Step 1: Apply graph_near_support
  obtain ⟨H, S₀, hiso₀, hS₀_fin, hgood, hedge_sub, hvert_hyp, hS₀_hyp⟩ :=
    graph_near_support G hplanar hfin_e hfin_v hne hdeg
  -- Step 2: Split S₀ into vertical (EH) and horizontal (EV) hyperplane sets
  -- Extract the z-parameter sets
  let zV : Set ℝ := {z | hyperplane2 0 z ∈ S₀}
  let zH : Set ℝ := {z | hyperplane2 1 z ∈ S₀}
  -- These sets are finite (since S₀ is finite and hyperplane2 is injective)
  have hzV_fin : zV.Finite := by
    have : zV ⊆ (hyperplane2 0) ⁻¹' S₀ := Set.Subset.rfl
    exact (hS₀_fin.preimage (hyperplane2_0_injective.injOn)).subset this
  have hzH_fin : zH.Finite := by
    have : zH ⊆ (hyperplane2 1) ⁻¹' S₀ := Set.Subset.rfl
    exact (hS₀_fin.preimage (hyperplane2_1_injective.injOn)).subset this
  -- Step 3: Find lower bounds for the z-parameter sets
  obtain ⟨t', ht'⟩ : ∃ t' : ℝ, ∀ z ∈ zV, t' ≤ z := by
    by_cases hne' : zV.Nonempty
    · exact ⟨sInf zV, fun z hz => csInf_le hzV_fin.bddBelow hz⟩
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne'⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ∀ z ∈ zH, t ≤ z := by
    by_cases hne' : zH.Nonempty
    · exact ⟨sInf zH, fun z hz => csInf_le hzH_fin.bddBelow hz⟩
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne'⟩
  -- Step 4: Define the shifting homeomorphism
  let f := (vTranslate_homeomorph (1 - t)).trans (hTranslate_homeomorph (1 - t'))
  -- Key: f x = hTranslate (1 - t') (vTranslate (1 - t) x)
  -- Step 5: The shifted hyperplane formulas
  have hf_eq : ∀ x, f x = hTranslate (1 - t') (vTranslate (1 - t) x) := fun _ => rfl
  have hf_image : ∀ S, f '' S = hTranslate (1 - t') '' (vTranslate (1 - t) '' S) := by
    intro S; ext x; simp only [Set.mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨vTranslate (1 - t) y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  have hf_hyp0 : ∀ z, f '' hyperplane2 0 z = hyperplane2 0 (z - t' + 1) := by
    intro z; rw [hf_image]; rw [hyperplane1_vTranslate, hyperplane1_hTranslate]; ring_nf
  have hf_hyp1 : ∀ z, f '' hyperplane2 1 z = hyperplane2 1 (z - t + 1) := by
    intro z; rw [hf_image]; rw [hyperplane2_vTranslate, hyperplane2_hTranslate]; ring_nf
  -- Step 6: Construct the result
  have hH_good := hgood
  have hH_plane : IsPlaneGraph H := hgood.1
  -- The image graph
  let H' := planeGraphImage f H hH_plane
  -- The shifted support set: IMAGE2 f S₀ = (f '' ·) '' S₀
  let S' := (f '' ·) '' S₀
  refine ⟨H', S', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- GraphIsomorphic G H'
    exact graphIsomorphic_trans hiso₀ (planeGraphImage_iso f H hH_plane)
  · -- S'.Finite
    exact hS₀_fin.image _
  · -- IsGoodPlaneGraph H'
    exact planeGraphImage_goodPlaneGraph f H ⟨hH_plane, hH_good.2⟩
  · -- ∀ e ∈ H'.edgeSet, e ⊆ ⋃₀ S'
    intro e' he'
    rw [planeGraphImage_edgeSet] at he'
    obtain ⟨e, he, rfl⟩ := he'
    -- e ⊆ ⋃₀ S₀, so f '' e ⊆ f '' (⋃₀ S₀) = ⋃₀ (f '' · '' S₀) = ⋃₀ S'
    calc f '' e ⊆ f '' (⋃₀ S₀) := Set.image_mono (hedge_sub e he)
      _ = ⋃₀ ((f '' ·) '' S₀) := Set.image_sUnion
      _ = ⋃₀ S' := rfl
  · -- ∀ v ∈ H'.vertexSet, hyperplane2 0 (v 0) ∈ S' ∧ hyperplane2 1 (v 1) ∈ S'
    intro v hv
    rw [planeGraphImage_vertexSet] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨hw0, hw1⟩ := hvert_hyp w hw
    -- f w = hTranslate (1-t') (vTranslate (1-t) w)
    have hfw : (f w : E2') = hTranslate (1 - t') (vTranslate (1 - t) w) := rfl
    constructor
    · -- hyperplane2 0 ((f w) 0) ∈ S'
      have hcoord : (f w : E2') 0 = w 0 + (1 - t') := by
        simp [hfw, hTranslate, vTranslate, WithLp.equiv]
      rw [hcoord, show w 0 + (1 - t') = w 0 - t' + 1 from by ring]
      rw [← hf_hyp0]
      exact Set.mem_image_of_mem _ hw0
    · -- hyperplane2 1 ((f w) 1) ∈ S'
      have hcoord : (f w : E2') 1 = w 1 + (1 - t) := by
        simp [hfw, hTranslate, vTranslate, WithLp.equiv]
      rw [hcoord, show w 1 + (1 - t) = w 1 - t + 1 from by ring]
      rw [← hf_hyp1]
      exact Set.mem_image_of_mem _ hw1
  · -- ∀ e ∈ S', ∃ z, 0 < z ∧ (e = hyperplane2 0 z ∨ e = hyperplane2 1 z)
    intro e' he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨z, hz_e⟩ := hS₀_hyp e he
    rcases hz_e with rfl | rfl
    · -- e = hyperplane2 0 z, so f '' e = hyperplane2 0 (z - t' + 1)
      simp only [hf_hyp0]
      refine ⟨z - t' + 1, ?_, Or.inl rfl⟩
      have : z ∈ zV := he
      linarith [ht' z this]
    · -- e = hyperplane2 1 z, so f '' e = hyperplane2 1 (z - t + 1)
      simp only [hf_hyp1]
      refine ⟨z - t + 1, ?_, Or.inr rfl⟩
      have : z ∈ zH := he
      linarith [ht z this]

/-! ## Hyperplane distinguishing -/

/-- Vertical and horizontal hyperplanes are always distinct.
    HOL Light: `hyperplane_ne` (line 34851). -/
theorem hyperplane_ne (z z' : ℝ) : hyperplane2 0 z ≠ hyperplane2 1 z' := by
  intro h
  have hmem : point (z, z' + 1) ∈ hyperplane2 0 z := by simp [hyperplane2]
  rw [h] at hmem
  simp [hyperplane2] at hmem

end
