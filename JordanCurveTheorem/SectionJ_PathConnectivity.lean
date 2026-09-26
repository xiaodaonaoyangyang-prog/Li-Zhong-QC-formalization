/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionI_GraphTheory

/-!
# Section J: Path Connectivity
## HOL Light: Section J (Lines 17775–19507)

Connect simple arcs to path connectivity; properties of plane graphs with
horizontal/vertical edges.

### Key HOL Light definitions
- `p_conn`: Path connectivity in a topological space
- `graph_hv_finite_radius`: Graphs with H/V edges of finite extent
-/

open Set Topology

noncomputable section

/-! ## Path connectivity -/

/-- Path connectivity in a set: two points are path-connected in `A`
    if there is a simple arc between them contained in `A`.
    HOL Light: `p_conn A x y`. -/
def pathConnectedIn (A : Set E2')
    (x y : E2') : Prop :=
  x = y ∨ ∃ C, IsSimpleArcEnd C x y ∧ C ⊆ A

/-- Path connectivity is reflexive. -/
theorem pathConnectedIn_refl (A : Set E2') (x : E2') :
    pathConnectedIn A x x := Or.inl rfl

/-- Path connectivity is symmetric. -/
theorem pathConnectedIn_symm {A : Set E2'} {x y : E2'} :
    pathConnectedIn A x y → pathConnectedIn A y x := by
  rintro (rfl | ⟨C, ⟨f, hC, hcont, hinj, hf0, hf1⟩, hCA⟩)
  · exact Or.inl rfl
  · -- Reverse parametrization: g(t) = f(1-t)
    refine Or.inr ⟨C, ⟨fun t => f (1 - t), ?_, ?_, ?_, ?_, ?_⟩, hCA⟩
    · ext p; simp only [hC, Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩
    · exact hcont.comp (continuous_const.sub continuous_id)
    · intro a ha b hb hab
      have := hinj ⟨by linarith [ha.2], by linarith [ha.1]⟩
        ⟨by linarith [hb.2], by linarith [hb.1]⟩ hab
      linarith
    · simp [hf1]
    · simp [hf0]

/-- Path connectivity in a subset implies path connectivity in a superset. -/
theorem pathConnectedIn_mono {A B : Set E2'} (hAB : A ⊆ B)
    {x y : E2'} (h : pathConnectedIn A x y) :
    pathConnectedIn B x y := by
  rcases h with rfl | ⟨C, hC, hCA⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨C, hC, hCA.trans hAB⟩

/-! ## Simple arc endpoint symmetry (43 uses!) -/

/-- Simple arc endpoints can be swapped.
    HOL Light: `simple_arc_end_symm` (line 19314). -/
theorem isSimpleArcEnd_symm {C : Set E2'} {v v' : E2'}
    (h : IsSimpleArcEnd C v v') : IsSimpleArcEnd C v' v := by
  obtain ⟨f, hC, hcont, hinj, hf0, hf1⟩ := h
  obtain ⟨g, hg_cont, hg_inj, hga, hgb, himg⟩ :=
    arc_reparameter_rev hcont hinj (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  exact ⟨g, hC ▸ himg, hg_cont, hg_inj, hga ▸ hf1, hgb ▸ hf0⟩

/-! ## Simple arc properties -/

/-- Simple arcs are connected. -/
theorem simpleArc_isConnected (C : Set E2')
    (hC : IsSimpleArc C) : IsConnected C := by
  obtain ⟨f, rfl, hcont, _⟩ := hC
  exact (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image f hcont.continuousOn

/-- Simple arcs are compact (continuous image of [0,1]). -/
theorem simpleArc_isCompact (C : Set E2')
    (hC : IsSimpleArc C) : IsCompact C := by
  obtain ⟨f, rfl, hcont, _⟩ := hC
  exact (isCompact_Icc).image hcont

/-- Simple arcs are closed (compact in Hausdorff space). -/
theorem simpleArc_isClosed (C : Set E2')
    (hC : IsSimpleArc C) : IsClosed C :=
  (simpleArc_isCompact C hC).isClosed

/-- Simple arcs are bounded. -/
theorem simpleArc_isBounded (C : Set E2')
    (hC : IsSimpleArc C) : Bornology.IsBounded C :=
  (simpleArc_isCompact C hC).isBounded

/-! ## Simple arc endpoint selection (moved up for pathConnectedIn_trans) -/

/-- Given a simple arc and two points on it, extract a subarc between them.
    HOL Light: `simple_arc_end_select` (line 19268). -/
theorem isSimpleArcEnd_select {C : Set E2'} {v v' : E2'}
    (harc : IsSimpleArc C) (hv : v ∈ C) (hv' : v' ∈ C) (hne : v ≠ v') :
    ∃ C', C' ⊆ C ∧ IsSimpleArcEnd C' v v' := by
  obtain ⟨f, rfl, hcont, hinj⟩ := harc
  obtain ⟨sv, hsv, rfl⟩ := hv
  obtain ⟨sv', hsv', rfl⟩ := hv'
  have hsne : sv ≠ sv' := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hsne with hlt | hgt
  · obtain ⟨g, himg, hga, hgb, hginj, hgcont⟩ :=
      arc_restrict hsv.1 hlt hsv'.2 (by norm_num : (0 : ℝ) < 1) hinj hcont
    exact ⟨g '' Icc 0 1, himg ▸ Set.image_mono (Icc_subset_Icc hsv.1 hsv'.2),
      g, rfl, hgcont, hginj, hga, hgb⟩
  · obtain ⟨g, himg, hga, hgb, hginj, hgcont⟩ :=
      arc_restrict hsv'.1 hgt hsv.2 (by norm_num : (0 : ℝ) < 1) hinj hcont
    exact ⟨g '' Icc 0 1, himg ▸ Set.image_mono (Icc_subset_Icc hsv'.1 hsv.2),
      isSimpleArcEnd_symm ⟨g, rfl, hgcont, hginj, hga, hgb⟩⟩

/-! ## Arc concatenation and path connectivity transitivity -/

/-- Concatenation of two simple arcs meeting only at a shared endpoint. -/
theorem isSimpleArcEnd_concat {C₁ C₂ : Set E2'} {x p z : E2'}
    (h₁ : IsSimpleArcEnd C₁ x p) (h₂ : IsSimpleArcEnd C₂ p z)
    (hinter : C₁ ∩ C₂ ⊆ {p}) :
    IsSimpleArcEnd (C₁ ∪ C₂) x z := by
  obtain ⟨f₁, rfl, hcont₁, hinj₁, hf₁₀, hf₁₁⟩ := h₁
  obtain ⟨f₂, rfl, hcont₂, hinj₂, hf₂₀, hf₂₁⟩ := h₂
  refine ⟨fun t => if 2 * t ≤ 1 then f₁ (2 * t) else f₂ (2 * t - 1),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- Image: f₁ '' [0,1] ∪ f₂ '' [0,1] = g '' [0,1]
    apply Set.Subset.antisymm
    · -- f₁ '' ∪ f₂ '' ⊆ g ''
      rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        dsimp only
        rw [show (2 : ℝ) * (s / 2) = s from by ring,
          if_pos (show s ≤ 1 from hs.2)]
      · rcases eq_or_lt_of_le hs.1 with rfl | hs0
        · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
          dsimp only
          rw [show (2 : ℝ) * (1 / 2) = 1 from by ring, if_pos le_rfl,
            hf₁₁, ← hf₂₀]
        · refine ⟨(s + 1) / 2, ⟨by linarith, by linarith [hs.2]⟩, ?_⟩
          dsimp only
          rw [show (2 : ℝ) * ((s + 1) / 2) = s + 1 from by ring,
            if_neg (show ¬(s + 1 ≤ 1) from by linarith),
            show s + 1 - 1 = s from by ring]
    · -- g '' ⊆ f₁ '' ∪ f₂ ''
      rintro _ ⟨t, ht, rfl⟩
      dsimp only
      split_ifs with h
      · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], h⟩, rfl⟩
      · push Not at h
        exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩,
          rfl⟩
  · -- Continuity
    apply continuous_if_le (by fun_prop : Continuous fun (t : ℝ) => 2 * t) continuous_const
    · exact (hcont₁.comp (by fun_prop : Continuous fun (t : ℝ) => 2 * t)).continuousOn
    · exact (hcont₂.comp
        (by fun_prop : Continuous fun (t : ℝ) => 2 * t - 1)).continuousOn
    · intro t (ht : 2 * t = 1)
      show f₁ (2 * t) = f₂ (2 * t - 1)
      rw [ht, hf₁₁, show (1 : ℝ) - 1 = 0 from sub_self 1, hf₂₀]
  · -- Injectivity
    intro t₁ ht₁ t₂ ht₂ hgt
    dsimp only at hgt
    by_cases h1 : 2 * t₁ ≤ 1 <;> by_cases h2 : 2 * t₂ ≤ 1
    · -- Both first half
      rw [if_pos h1, if_pos h2] at hgt
      have := hinj₁ ⟨by linarith [ht₁.1], h1⟩
        ⟨by linarith [ht₂.1], h2⟩ hgt
      linarith
    · -- Cross: t₁ first, t₂ second → contradiction
      rw [if_pos h1, if_neg h2] at hgt
      push Not at h2
      have hm₁ : f₁ (2 * t₁) ∈ f₁ '' Icc 0 1 :=
        ⟨2 * t₁, ⟨by linarith [ht₁.1], h1⟩, rfl⟩
      have hm₂ : f₁ (2 * t₁) ∈ f₂ '' Icc 0 1 := hgt ▸
        ⟨2 * t₂ - 1, ⟨by linarith, by linarith [ht₂.2]⟩, rfl⟩
      have hp := Set.mem_singleton_iff.mp (hinter ⟨hm₁, hm₂⟩)
      have h2t₂ : (2 * t₂ - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₂.2]⟩
      have := hinj₂ h2t₂
        (left_mem_Icc.mpr zero_le_one) (by rw [← hgt, hp, hf₂₀])
      linarith
    · -- Cross: t₁ second, t₂ first → contradiction
      rw [if_neg h1, if_pos h2] at hgt
      push Not at h1
      have hm₂ : f₂ (2 * t₁ - 1) ∈ f₂ '' Icc 0 1 :=
        ⟨2 * t₁ - 1, ⟨by linarith, by linarith [ht₁.2]⟩, rfl⟩
      have hm₁ : f₂ (2 * t₁ - 1) ∈ f₁ '' Icc 0 1 := hgt ▸
        ⟨2 * t₂, ⟨by linarith [ht₂.1], h2⟩, rfl⟩
      have hp := Set.mem_singleton_iff.mp (hinter ⟨hm₁, hm₂⟩)
      have h2t₁ : (2 * t₁ - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₁.2]⟩
      have := hinj₂ h2t₁
        (left_mem_Icc.mpr zero_le_one) (hp.trans hf₂₀.symm)
      linarith
    · -- Both second half
      rw [if_neg h1, if_neg h2] at hgt
      push Not at h1 h2
      have h2t₁ : (2 * t₁ - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₁.2]⟩
      have h2t₂ : (2 * t₂ - 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₂.2]⟩
      have := hinj₂ h2t₁ h2t₂ hgt
      linarith
  · -- g(0) = x
    dsimp only; norm_num; exact hf₁₀
  · -- g(1) = z
    dsimp only; norm_num; exact hf₂₁

/-- Path connectivity is transitive (via arc concatenation).
    HOL Light: `pconn_trans` (line 17263). -/
theorem pathConnectedIn_trans {A : Set E2'} {x y z : E2'}
    (hxy : pathConnectedIn A x y) (hyz : pathConnectedIn A y z) :
    pathConnectedIn A x z := by
  rcases hxy with rfl | ⟨C₁, hC₁, hC₁A⟩
  · exact hyz
  rcases hyz with rfl | ⟨C₂, hC₂, hC₂A⟩
  · exact Or.inr ⟨C₁, hC₁, hC₁A⟩
  by_cases hxz : x = z
  · exact Or.inl hxz
  have hx_C₁ : x ∈ C₁ := by
    obtain ⟨f, rfl, _, _, hf0, _⟩ := hC₁
    exact ⟨0, left_mem_Icc.mpr zero_le_one, hf0⟩
  have hy_C₁ : y ∈ C₁ := by
    obtain ⟨f, rfl, _, _, _, hf1⟩ := hC₁
    exact ⟨1, right_mem_Icc.mpr zero_le_one, hf1⟩
  have hy_C₂ : y ∈ C₂ := by
    obtain ⟨f, rfl, _, _, hf0, _⟩ := hC₂
    exact ⟨0, left_mem_Icc.mpr zero_le_one, hf0⟩
  have hz_C₂ : z ∈ C₂ := by
    obtain ⟨f, rfl, _, _, _, hf1⟩ := hC₂
    exact ⟨1, right_mem_Icc.mpr zero_le_one, hf1⟩
  -- Case 1: x ∈ C₂ → subarc of C₂ from x to z
  by_cases hxC₂ : x ∈ C₂
  · obtain ⟨C', hC', harc⟩ :=
      isSimpleArcEnd_select (isSimpleArcEnd_isSimpleArc hC₂) hxC₂ hz_C₂ hxz
    exact Or.inr ⟨C', harc, hC'.trans hC₂A⟩
  -- Case 2: z ∈ C₁ → subarc of C₁ from x to z
  by_cases hzC₁ : z ∈ C₁
  · obtain ⟨C', hC', harc⟩ :=
      isSimpleArcEnd_select (isSimpleArcEnd_isSimpleArc hC₁) hx_C₁ hzC₁ hxz
    exact Or.inr ⟨C', harc, hC'.trans hC₁A⟩
  -- Case 3: x ∉ C₂ and z ∉ C₁ → preimage_first + concatenation
  obtain ⟨f₁, hC₁_eq, hcont₁, hinj₁, hf₁₀, hf₁₁⟩ := hC₁
  have hC₂_closed : IsClosed C₂ := by
    rcases hC₂ with ⟨f, rfl, hcont, _, _, _⟩
    exact (isCompact_Icc.image hcont).isClosed
  have hmeet : (f₁ '' Icc 0 1 ∩ C₂).Nonempty :=
    ⟨y, hC₁_eq ▸ hy_C₁, hy_C₂⟩
  obtain ⟨t₀, ht₀, hft₀, hfirst⟩ :=
    preimage_first hcont₁.continuousOn hC₂_closed hmeet
  have ht₀_pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · exfalso; rw [← h, hf₁₀] at hft₀; exact hxC₂ hft₀
    · exact h
  obtain ⟨g₁, hg₁_img, hg₁₀, hg₁₁, hg₁_inj, hg₁_cont⟩ :=
    arc_restrict (le_refl 0) ht₀_pos ht₀.2
      (by norm_num : (0 : ℝ) < 1) hinj₁ hcont₁
  set p := f₁ t₀
  have hC₁' : IsSimpleArcEnd (g₁ '' Icc 0 1) x p :=
    ⟨g₁, rfl, hg₁_cont, hg₁_inj, hg₁₀ ▸ hf₁₀, hg₁₁⟩
  have hpz : p ≠ z := by
    intro h; apply hzC₁; rw [hC₁_eq]; exact ⟨t₀, ht₀, h⟩
  obtain ⟨C₂', hC₂'_sub, hC₂'⟩ :=
    isSimpleArcEnd_select (isSimpleArcEnd_isSimpleArc hC₂) hft₀ hz_C₂ hpz
  have hkey : g₁ '' Icc 0 1 ∩ C₂' ⊆ {p} := by
    intro w ⟨hw₁, hw₂⟩
    rw [hg₁_img] at hw₁
    obtain ⟨s, hs, rfl⟩ := hw₁
    rcases eq_or_lt_of_le hs.2 with h | h
    · subst h; rfl
    · exfalso; exact hfirst s ⟨hs.1, h⟩ (hC₂'_sub hw₂)
  exact Or.inr ⟨g₁ '' Icc 0 1 ∪ C₂', isSimpleArcEnd_concat hC₁' hC₂' hkey,
    Set.union_subset
      (by rw [hg₁_img]
          exact (Set.image_mono (Icc_subset_Icc_right ht₀.2)).trans (hC₁_eq ▸ hC₁A))
      (hC₂'_sub.trans hC₂A)⟩

/-! ## Plane graph properties -/

/-- Edges of a plane graph are compact. -/
theorem planeGraph_edge_compact (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) (e : Set E2') (he : e ∈ G.edgeSet) :
    IsCompact e := by
  obtain ⟨v, v', _, _, _, harc⟩ := hG.edges_are_arcs e he
  exact simpleArc_isCompact e (isSimpleArcEnd_isSimpleArc harc)

/-- Edges of a plane graph are connected. -/
theorem planeGraph_edge_connected (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) (e : Set E2') (he : e ∈ G.edgeSet) :
    IsConnected e := by
  obtain ⟨v, v', _, _, _, harc⟩ := hG.edges_are_arcs e he
  exact simpleArc_isConnected e (isSimpleArcEnd_isSimpleArc harc)

/-! ## Connectivity bridge -/

/-- A connected open set is path-connected.
    HOL Light: `p_conn_conn` (line 18067). -/
theorem pathConnected_of_isConnected_isOpen {A : Set E2'}
    (hopen : IsOpen A) (hconn : IsConnected A) :
    ∀ x ∈ A, ∀ y ∈ A, pathConnectedIn A x y := by
  intro x hxA y hyA
  -- Segment in a ball gives pathConnectedIn
  have seg : ∀ (c : E2') (r : ℝ), 0 < r → ∀ p ∈ Metric.ball c r,
      pathConnectedIn (Metric.ball c r) c p := by
    intro c r hr p hp
    rcases eq_or_ne c p with rfl | hne
    · exact Or.inl rfl
    · refine Or.inr ⟨(fun t => (1 - t) • c + t • p) '' Icc 0 1,
        ⟨fun t => (1 - t) • c + t • p, rfl, by fun_prop, ?_, by simp, by simp⟩, ?_⟩
      · intro t₁ ht₁ t₂ ht₂ heq
        have h0 : (t₁ - t₂) • (p - c) = 0 := by
          have := sub_eq_zero.mpr heq
          rwa [show (1 - t₁) • c + t₁ • p - ((1 - t₂) • c + t₂ • p) =
            (t₁ - t₂) • (p - c) from by module] at this
        rcases smul_eq_zero.mp h0 with h | h
        · linarith
        · exact absurd (sub_eq_zero.mp h) hne.symm
      · intro w ⟨t, ht, heq⟩
        exact heq ▸ (convex_ball c r) (Metric.mem_ball_self hr) hp
          (by linarith [ht.2]) ht.1 (by ring)
  by_contra hny
  -- P = {z | pathConnectedIn A x z} is open
  set P := {z | pathConnectedIn A x z}
  have hP_open : IsOpen P := isOpen_iff_forall_mem_open.mpr fun a ha => by
    have haA : a ∈ A := by
      rcases ha with rfl | ⟨_, ⟨f, rfl, _, _, _, hf1⟩, hCA⟩
      · exact hxA
      · exact hCA ⟨1, right_mem_Icc.mpr zero_le_one, hf1⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen a haA
    exact ⟨Metric.ball a r, fun b hb =>
      pathConnectedIn_trans ha (pathConnectedIn_mono hball (seg a r hr b hb)),
      Metric.isOpen_ball, Metric.mem_ball_self hr⟩
  -- A \ P is open
  have hAP_open : IsOpen (A \ P) := isOpen_iff_forall_mem_open.mpr fun a ⟨haA, hna⟩ => by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen a haA
    exact ⟨Metric.ball a r, fun b hb => ⟨hball hb, fun hpb =>
      hna (pathConnectedIn_trans hpb (pathConnectedIn_symm
        (pathConnectedIn_mono hball (seg a r hr b hb))))⟩,
      Metric.isOpen_ball, Metric.mem_ball_self hr⟩
  -- Connectedness gives a contradictory point in P ∩ (A \ P)
  have hsub : A ⊆ P ∪ (A \ P) := by
    intro a ha; by_cases h : a ∈ P
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩
  have hpc := hconn.2
  exact (@hpc P (A \ P) hP_open hAP_open hsub ⟨x, hxA, Or.inl rfl⟩
    ⟨y, hyA, ⟨hyA, hny⟩⟩).elim fun _ ⟨_, hwP, _, hwnP⟩ => hwnP hwP

/-! ## Selection / optimization lemmas -/

/-- A nonempty set has an element minimizing a natural-valued function.
    HOL Light: `select_image_num_min` (line 18455). -/
theorem exists_min_image_nat {α : Type*} {S : Set α} {f : α → ℕ}
    (hne : S.Nonempty) (hfin : S.Finite) :
    ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y := by
  obtain ⟨x, hxS, hmin⟩ := hfin.toFinset.exists_min_image f
    (hfin.toFinset_nonempty.mpr hne)
  exact ⟨x, hfin.mem_toFinset.mp hxS, fun y hy => hmin y (hfin.mem_toFinset.mpr hy)⟩

/-- A nonempty finite family of sets has a member with minimal cardinality.
    HOL Light: `select_card_min` (line 18527). -/
theorem exists_min_ncard {_α β : Type*} {F : Set (Set β)}
    (hne : F.Nonempty) (hfin : F.Finite)
    (_hfin_elts : ∀ S ∈ F, S.Finite) :
    ∃ S ∈ F, ∀ T ∈ F, S.ncard ≤ T.ncard :=
  exists_min_image_nat hne hfin

/-! ## Curve restriction -/

/-- Restrict a simple arc to a subarc between the first hits of two closed sets.
    HOL Light: `curve_restriction` (line 18580). -/
theorem curve_restriction {f : ℝ → E2'} {a b : ℝ} {C₁ C₂ : Set E2'}
    (hcont : ContinuousOn f (Icc a b))
    (hinj : Set.InjOn f (Icc a b))
    (hab : a < b)
    (_hC₁ : IsClosed C₁) (_hC₂ : IsClosed C₂)
    (_hC₁C₂ : (f '' Icc a b ∩ C₁ ∩ C₂).Nonempty → False)
    (_hmeet₁ : (f '' Icc a b ∩ C₁).Nonempty)
    (_hmeet₂ : (f '' Icc a b ∩ C₂).Nonempty) :
    ∃ g : ℝ → E2', ∃ C' : Set E2',
      C' ⊆ f '' Icc a b ∧
      C' ∩ C₁ = f '' Icc a b ∩ C₁ ∧
      C' ∩ C₂ = f '' Icc a b ∩ C₂ ∧
      Continuous g ∧
      Set.InjOn g (Icc a b) ∧
      C' = g '' Icc a b := by
  -- The whole arc f '' [a,b] satisfies all conditions; we only need a
  -- globally continuous reparametrization via clamping to [a,b].
  have clamp_id : ∀ t ∈ Icc a b, max a (min b t) = t :=
    fun t ht => by rw [min_eq_right ht.2, max_eq_right ht.1]
  have clamp_mem : ∀ t, max a (min b t) ∈ Icc a b := fun t =>
    ⟨le_max_left a _, max_le hab.le (min_le_left b t)⟩
  refine ⟨fun t => f (max a (min b t)), f '' Icc a b,
    Subset.refl _, rfl, rfl, ?_, ?_, ?_⟩
  · exact hcont.comp_continuous
      (continuous_const.max (continuous_const.min continuous_id)) clamp_mem
  · intro x hx y hy hxy
    have hxy' : f (max a (min b x)) = f (max a (min b y)) := hxy
    rw [clamp_id x hx, clamp_id y hy] at hxy'
    exact hinj hx hy hxy'
  · ext z; constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, congr_arg f (clamp_id t ht)⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨max a (min b t), clamp_mem t, rfl⟩

/-! ## Good plane graphs -/

/-- A good plane graph: plane graph where each edge is a simple arc between
    its two incident vertices.
    HOL Light: `good_plane_graph` (line 19061). -/
def IsGoodPlaneGraph (G : HolGraph E2' (Set E2')) : Prop :=
  IsPlaneGraph G ∧
  ∀ e ∈ G.edgeSet, ∀ v v', v ∈ G.inc e → v' ∈ G.inc e → v ≠ v' →
    IsSimpleArcEnd e v v'

/-! ## Graph edge modification -/

/-- Modify graph edges by applying a function to each edge.
    HOL Light: `graph_edge_mod G f` (line 19069). -/
def HolGraph.edgeMod {V E E' : Type*} (G : HolGraph V E) (f : E → E')
    (_hf : Set.InjOn f G.edgeSet)
    (hwell : ∀ e' ∈ f '' G.edgeSet,
      {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet, v ∈ G.inc e ∧ f e = e'} ⊆ G.vertexSet ∧
      {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet, v ∈ G.inc e ∧ f e = e'}.ncard = 2) :
    HolGraph V E' where
  vertexSet := G.vertexSet
  edgeSet := f '' G.edgeSet
  inc := fun e' => {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet, v ∈ G.inc e ∧ f e = e'}
  well_formed := fun e' he' => hwell e' he'

/-- Edge modification preserves vertex set.
    HOL Light: `graph_edge_mod_v` (line 19080). -/
theorem HolGraph.edgeMod_vertexSet {V E E' : Type*} (G : HolGraph V E) (f : E → E')
    (hf : Set.InjOn f G.edgeSet) (hwell) :
    (G.edgeMod f hf hwell).vertexSet = G.vertexSet := rfl

/-- Edge modification transforms the edge set.
    HOL Light: `graph_edge_mod_e` (line 19088). -/
theorem HolGraph.edgeMod_edgeSet {V E E' : Type*} (G : HolGraph V E) (f : E → E')
    (hf : Set.InjOn f G.edgeSet) (hwell) :
    (G.edgeMod f hf hwell).edgeSet = f '' G.edgeSet := rfl

/-- Injection from set to image is a bijection.
    HOL Light: `inj_bij` (line 19108). -/
theorem Set.InjOn.bijOn_image' {α β : Type*} {f : α → β} {S : Set α}
    (hinj : Set.InjOn f S) : Set.BijOn f S (f '' S) :=
  hinj.bijOn_image

/-- Edge modification and injection give an isomorphic graph.
    HOL Light: `graph_edge_iso` (line 19118). -/
theorem HolGraph.edgeMod_isomorphic {V E E' : Type*} (G : HolGraph V E) (f : E → E')
    (hf : Set.InjOn f G.edgeSet) (hwell) :
    GraphIsomorphic G (G.edgeMod f hf hwell) := by
  refine ⟨⟨id, f, Set.bijOn_id _, hf.bijOn_image, ?_⟩⟩
  intro e he
  ext v; simp only [HolGraph.edgeMod, Set.mem_sep_iff, Set.image_id]; constructor
  · rintro ⟨_, e', he', hve', hfe'⟩
    exact hf he' he hfe' ▸ hve'
  · exact fun hve =>
      ⟨(G.well_formed e he).1 hve, e, he, hve, rfl⟩

/-- Edge modification preserves plane graph property.
    HOL Light: `plane_graph_mod` (line 19188). -/
theorem planeGraph_edgeMod (G : HolGraph E2' (Set E2'))
    (f : Set E2' → Set E2')
    (hf : Set.InjOn f G.edgeSet) (hwell)
    (hG : IsPlaneGraph G)
    (h_arcs : ∀ e ∈ G.edgeSet, ∀ v v',
      IsSimpleArcEnd e v v' → IsSimpleArcEnd (f e) v v')
    (h_disj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁ ≠ e₂ →
      f e₁ ∩ f e₂ ⊆ e₁ ∩ e₂)
    (h_vtx : ∀ e ∈ G.edgeSet, ∀ v ∈ G.vertexSet,
      v ∈ f e → v ∈ e) :
    IsPlaneGraph (G.edgeMod f hf hwell) := by
  constructor
  · -- edges_are_arcs
    rintro e' ⟨e, he, rfl⟩
    obtain ⟨v, v', hv, hv', hne, harc⟩ := hG.edges_are_arcs e he
    exact ⟨v, v',
      ⟨(G.well_formed e he).1 hv, e, he, hv, rfl⟩,
      ⟨(G.well_formed e he).1 hv', e, he, hv', rfl⟩,
      hne, h_arcs e he v v' harc⟩
  · -- vertex_on_edge
    rintro e' ⟨e, he, rfl⟩ v hv hve'
    simp only [HolGraph.edgeMod] at hv ⊢
    exact ⟨hv, e, he, hG.vertex_on_edge e he v hv (h_vtx e he v hv hve'), rfl⟩
  · -- edges_disjoint_interior
    intro e₁' e₂' he₁' he₂' hne'
    obtain ⟨e₁, he₁, rfl⟩ := he₁'
    obtain ⟨e₂, he₂, rfl⟩ := he₂'
    have hne : e₁ ≠ e₂ := fun h => hne' (congr_arg f h)
    intro v hv
    exact hG.edges_disjoint_interior e₁ e₂ he₁ he₂ hne (h_disj e₁ he₁ e₂ he₂ hne hv)

/-- Every edge of a graph has two distinct incident vertices.
    HOL Light: `graph_edge_end_select` (line 19422). -/
theorem HolGraph.edge_end_select {V E : Type*} (G : HolGraph V E)
    (e : E) (he : e ∈ G.edgeSet) :
    ∃ v v', v ∈ G.inc e ∧ v' ∈ G.inc e ∧ v ≠ v' := by
  have h2 := G.edge_has_two_vertices e he
  have hne : (G.inc e).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; simp [h] at h2
  obtain ⟨v, hv⟩ := hne
  have hgt : 1 < (G.inc e).ncard := by omega
  obtain ⟨v', hv', hvv'⟩ := Set.exists_ne_of_one_lt_ncard hgt v
  exact ⟨v, v', hv, hv', hvv'.symm⟩

/-! ## HV-finite plane graphs -/

/-- A plane graph has HV-finite radius if all its edges are contained in
    finitely many horizontal and vertical lines.
    HOL Light: `graph_hv_finite_radius`. -/
def IsHVFinitePlaneGraph (G : HolGraph E2' (Set E2')) : Prop :=
  IsPlaneGraph G ∧
  ∃ (S : Finset ℝ) (T : Finset ℝ),
    ∀ e ∈ G.edgeSet, e ⊆
      (⋃ x ∈ S, {p : E2' | p 0 = x}) ∪
      (⋃ y ∈ T, {p : E2' | p 1 = y})

end
