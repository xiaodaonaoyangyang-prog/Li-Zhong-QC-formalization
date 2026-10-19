import LiZhongQC.Ch09.S31_FiniteType
import LiZhongExternal.Topology.InvarianceOfDomain

open Complex Set Metric Filter Topology
open scoped Manifold ContDiff Real

noncomputable section

namespace LiZhongQC

universe u

/-- A punctured disc in `ℂ` is connected: it is the image of `(0, r) × S¹` under `(t, u) ↦ c + t u`. -/
theorem s82lc_punctured_ball_preconnected (c : ℂ) {r : ℝ} (hr : 0 < r) : IsPreconnected (ball c r \ {c}) := by
  have hS : IsConnected (sphere (0 : ℂ) 1) :=
    isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one
  have hP := (isConnected_Ioo hr).prod hS
  have himg : (fun p : ℝ × ℂ => c + (p.1 : ℂ) * p.2) '' (Ioo 0 r ×ˢ sphere (0 : ℂ) 1) = ball c r \ {c} := by
    ext z
    constructor
    · rintro ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
      have hw1 : ‖w‖ = 1 := by simpa using hw
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht.1]
        exact ht.2
      · intro h
        have h0 : (t : ℂ) * w = 0 := by simpa using h
        rcases mul_eq_zero.1 h0 with h1 | h1
        · exact ht.1.ne' (by exact_mod_cast h1)
        · rw [h1, norm_zero] at hw1
          exact zero_ne_one hw1
    · rintro ⟨hz, hzc⟩
      have hne : z - c ≠ 0 := sub_ne_zero.2 hzc
      have hpos : 0 < ‖z - c‖ := norm_pos_iff.2 hne
      refine ⟨(‖z - c‖, (z - c) / (‖z - c‖ : ℂ)), ⟨⟨hpos, ?_⟩, ?_⟩, ?_⟩
      · rw [mem_ball, dist_eq_norm] at hz
        exact hz
      · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
          div_self hpos.ne']
      · have hc : (‖z - c‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        show c + (‖z - c‖ : ℂ) * ((z - c) / (‖z - c‖ : ℂ)) = z
        rw [mul_div_cancel₀ _ hc]
        ring
  rw [← himg]
  exact (hP.image _ (by fun_prop)).isPreconnected

/-- Connected punctured neighbourhoods: every neighbourhood `W` of a point `p` of a surface contains a connected
set `B` with `p ∉ B` and `B ∪ {p}` a neighbourhood of `p` (a punctured chart disc). -/
theorem s82lc_punctured_nhds {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) {W : Set X}
    (hW : W ∈ 𝓝 p) :
    ∃ B : Set X, B ⊆ W ∧ IsPreconnected B ∧ p ∉ B ∧ B.Nonempty ∧ insert p B ∈ 𝓝 p := by
  set φ := chartAt ℂ p with hφ
  have hpS : p ∈ φ.source := mem_chart_source ℂ p
  have hT : φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source) ∈ 𝓝 (φ p) := by
    have h1 : W ∩ φ.source ∈ 𝓝 (φ.symm (φ p)) := by
      rw [φ.left_inv hpS]
      exact Filter.inter_mem hW (φ.open_source.mem_nhds hpS)
    exact Filter.inter_mem (φ.open_target.mem_nhds (φ.map_source hpS))
      ((φ.continuousAt_symm (φ.map_source hpS)).preimage_mem_nhds h1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hT
  have hbt : ball (φ p) r ⊆ φ.target := fun z hz => (hball hz).1
  refine ⟨φ.symm '' (ball (φ p) r \ {φ p}), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hball hz.1).2.1
  · exact (s82lc_punctured_ball_preconnected (φ p) hr).image _
      (φ.continuousOn_symm.mono fun z hz => hbt hz.1)
  · rintro ⟨z, hz, hzp⟩
    apply hz.2
    rw [mem_singleton_iff, ← hzp, φ.right_inv (hbt hz.1)]
  · obtain ⟨w, hw⟩ : (ball (φ p) r \ {φ p}).Nonempty := by
      refine ⟨φ p + (r / 2 : ℝ), ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      · intro h
        have : ((r / 2 : ℝ) : ℂ) = 0 := by simpa using h
        have : r / 2 = 0 := by exact_mod_cast this
        linarith
    exact ⟨_, w, hw, rfl⟩
  · have heq : insert p (φ.symm '' (ball (φ p) r \ {φ p})) = φ.symm '' ball (φ p) r := by
      ext x
      constructor
      · rintro (hx | ⟨z, hz, rfl⟩)
        · rw [hx]
          exact ⟨φ p, mem_ball_self hr, φ.left_inv hpS⟩
        · exact ⟨z, hz.1, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        by_cases hzp : z = φ p
        · left
          rw [hzp, φ.left_inv hpS]
        · right
          exact ⟨z, ⟨hz, hzp⟩, rfl⟩
    rw [heq, φ.symm_image_eq_source_inter_preimage hbt]
    exact Filter.inter_mem (φ.open_source.mem_nhds hpS)
      ((φ.continuousAt hpS).preimage_mem_nhds (ball_mem_nhds _ hr))

/-- The complement of a finite set of a surface accumulates at every point. -/
theorem s82lc_nhdsWithin_compl_neBot {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X]
    {P : Set X} (hP : P.Finite) (p : X) : (𝓝[Pᶜ] p).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro W hW
  have hW' : W ∩ (P \ {p})ᶜ ∈ 𝓝 p :=
    Filter.inter_mem hW ((hP.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl)
  obtain ⟨B, hBW, -, hpB, ⟨x, hx⟩, -⟩ := s82lc_punctured_nhds p hW'
  refine ⟨x, (hBW hx).1, fun hxP => (hBW hx).2 ⟨hxP, ?_⟩⟩
  rintro rfl
  exact hpB hx

/-- **Limits at the punctures.**  Let `G` be continuous off a finite set `P₀` of a surface, with values off a
finite set `P₁` of a compact Hausdorff space, and proper in the sense that the points of `P₀ᶜ` mapped near a point
`y ∉ P₁` stay in a compact subset of `P₀ᶜ`.  Then `G` has a limit in `P₁` at every point of `P₀`. -/
theorem s82lc_tendsto_puncture {X₀ X₁ : Type*} [TopologicalSpace X₀] [ChartedSpace ℂ X₀] [T2Space X₀]
    [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁] {P₀ : Set X₀} {P₁ : Set X₁} (hP₀ : P₀.Finite)
    (hP₁ : P₁.Finite) {G : X₀ → X₁} (hG : ContinuousOn G P₀ᶜ)
    (hprop : ∀ y ∉ P₁, ∃ V ∈ 𝓝 y, ∃ Q : Set X₀, IsCompact Q ∧ Q ⊆ P₀ᶜ ∧ ∀ x ∉ P₀, G x ∈ V → x ∈ Q)
    {p : X₀} (hp : p ∈ P₀) : ∃ p' ∈ P₁, Tendsto G (𝓝[P₀ᶜ] p) (𝓝 p') := by
  have hNe := s82lc_nhdsWithin_compl_neBot hP₀ p
  -- every cluster value lies in `P₁`
  have hcl : ∀ y, MapClusterPt y (𝓝[P₀ᶜ] p) G → y ∈ P₁ := by
    intro y hy
    by_contra hyP
    obtain ⟨V, hV, Q, hQ, hQP, hGQ⟩ := hprop y hyP
    have hpQ : Qᶜ ∈ 𝓝 p := hQ.isClosed.isOpen_compl.mem_nhds fun h => hQP h hp
    have hev : ∀ᶠ x in 𝓝[P₀ᶜ] p, ¬ G x ∈ V := by
      filter_upwards [nhdsWithin_le_nhds hpQ, self_mem_nhdsWithin] with x hxQ hxP hxV
      exact hxQ (hGQ x hxP hxV)
    obtain ⟨x, hx1, hx2⟩ := ((mapClusterPt_iff_frequently.1 hy V hV).and_eventually hev).exists
    exact hx2 hx1
  -- connected punctured neighbourhoods in the filter
  have hbasis : ∀ T ∈ 𝓝[P₀ᶜ] p, ∃ B ⊆ T, IsPreconnected B ∧ B ⊆ P₀ᶜ ∧ B ∈ 𝓝[P₀ᶜ] p := by
    intro T hT
    obtain ⟨W₀, hW₀, hW₀T⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hT
    have hW' : W₀ ∩ (P₀ \ {p})ᶜ ∈ 𝓝 p :=
      Filter.inter_mem hW₀ ((hP₀.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨B, hBW, hBc, hpB, -, hBn⟩ := s82lc_punctured_nhds p hW'
    have hBP : B ⊆ P₀ᶜ := by
      intro x hx hxP
      refine (hBW hx).2 ⟨hxP, ?_⟩
      rintro rfl
      exact hpB hx
    refine ⟨B, fun x hx => hW₀T ⟨(hBW hx).1, hBP hx⟩, hBc, hBP, ?_⟩
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨_, hBn, ?_⟩
    rintro x ⟨(rfl | hx), hxP⟩
    · exact absurd hp hxP
    · exact hx
  -- uniqueness of the cluster value
  obtain ⟨U, hU, hUd⟩ := hP₁.t2_separation
  have huniq : ∀ y₁ y₂, MapClusterPt y₁ (𝓝[P₀ᶜ] p) G → MapClusterPt y₂ (𝓝[P₀ᶜ] p) G → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂
    by_contra hne
    have hy₁ := hcl y₁ h₁
    have hy₂ := hcl y₂ h₂
    set W := (⋃ z ∈ P₁, U z)ᶜ with hWdef
    have hWc : IsClosed W := by
      rw [hWdef, isClosed_compl_iff]
      exact isOpen_biUnion fun z _ => (hU z).2
    have hfreq : ∃ᶠ x in 𝓝[P₀ᶜ] p, G x ∈ W := by
      rw [Filter.frequently_iff]
      intro T hT
      obtain ⟨B, hBT, hBc, hBP, hBN⟩ := hbasis T hT
      obtain ⟨x₁, hx₁U, hx₁B⟩ :=
        ((mapClusterPt_iff_frequently.1 h₁ (U y₁) ((hU y₁).2.mem_nhds (hU y₁).1)).and_eventually hBN).exists
      obtain ⟨x₂, hx₂U, hx₂B⟩ :=
        ((mapClusterPt_iff_frequently.1 h₂ (U y₂) ((hU y₂).2.mem_nhds (hU y₂).1)).and_eventually hBN).exists
      by_contra hall
      push Not at hall
      have hsub : G '' B ⊆ U y₁ ∪ ⋃ z ∈ P₁ \ {y₁}, U z := by
        rintro _ ⟨x, hx, rfl⟩
        have := hall x (hBT hx)
        rw [hWdef, Set.notMem_compl_iff, mem_iUnion₂] at this
        obtain ⟨z, hz, hxz⟩ := this
        by_cases hzy : z = y₁
        · exact Or.inl (hzy ▸ hxz)
        · exact Or.inr (mem_iUnion₂.2 ⟨z, ⟨hz, hzy⟩, hxz⟩)
      have hpre : IsPreconnected (G '' B) := hBc.image G (hG.mono hBP)
      obtain ⟨_, -, h1, h2⟩ := hpre (U y₁) (⋃ z ∈ P₁ \ {y₁}, U z) (hU y₁).2
        (isOpen_biUnion fun z _ => (hU z).2) hsub ⟨G x₁, ⟨x₁, hx₁B, rfl⟩, hx₁U⟩
        ⟨G x₂, ⟨x₂, hx₂B, rfl⟩, mem_iUnion₂.2 ⟨y₂, ⟨hy₂, fun h => hne h.symm⟩, hx₂U⟩⟩
      obtain ⟨z, hz, hz2⟩ := mem_iUnion₂.1 h2
      exact Set.disjoint_left.1 (hUd hy₁ hz.1 (Ne.symm hz.2)) h1 hz2
    obtain ⟨y, hyW, hy⟩ := hWc.isCompact.exists_mapClusterPt_of_frequently hfreq
    have hyP := hcl y hy
    exact hyW (mem_iUnion₂.2 ⟨y, hyP, (hU y).1⟩)
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_mapClusterPt (f := 𝓝[P₀ᶜ] p) (u := G) (by simp)
  exact ⟨y, hcl y hy, tendsto_nhds_of_unique_mapClusterPt fun z hz => huniq z y hz hy⟩

/-- The extension of `ι₁ ∘ f ∘ ι₀⁻¹` over the punctures, as a continuous map sending punctures to punctures. -/
theorem s82lc_extend_continuous {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n g' n' : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g' n' 0)
    (f : S₀ ≃ₜ S) :
    ∃ fb : F₀.X.carrier → F₁.X.carrier, Continuous fb ∧ (∀ s, fb (F₀.ι s) = F₁.ι (f s)) ∧
      ∀ p ∈ F₀.P, fb p ∈ F₁.P := by
  classical
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  have hrange₁ : range F₁.ι = (↑F₁.P : Set F₁.X.carrier)ᶜ := by
    rw [F₁.range_ι]; simp
  -- `S₀` is nonempty: the complement of the punctures is
  obtain ⟨x₀⟩ := (inferInstance : Nonempty F₀.X.carrier)
  have hne := s82lc_nhdsWithin_compl_neBot (P := (↑F₀.P : Set F₀.X.carrier)) F₀.P.finite_toSet x₀
  obtain ⟨x₁, hx₁⟩ := hne.nonempty_of_mem self_mem_nhdsWithin
  rw [← hrange₀] at hx₁
  obtain ⟨s₀, -⟩ := hx₁
  have : Nonempty S₀ := ⟨s₀⟩
  set G : F₀.X.carrier → F₁.X.carrier := fun x => F₁.ι (f (Function.invFun F₀.ι x)) with hG
  have hinv : ∀ s, Function.invFun F₀.ι (F₀.ι s) = s :=
    Function.leftInverse_invFun F₀.embedding.injective
  have hGι : ∀ s, G (F₀.ι s) = F₁.ι (f s) := fun s => by
    show F₁.ι (f (Function.invFun F₀.ι (F₀.ι s))) = _
    rw [hinv]
  -- `G` is continuous off the punctures
  have hGc : ContinuousOn G (↑F₀.P)ᶜ := by
    rw [← hrange₀]
    set e := F₀.embedding.isEmbedding.toHomeomorph with he
    have heq : ∀ x : range F₀.ι, Function.invFun F₀.ι x = e.symm x := by
      intro x
      apply F₀.embedding.injective
      have h1 : F₀.ι (e.symm x) = x := congrArg Subtype.val (e.apply_symm_apply x)
      rw [h1]
      exact Function.invFun_eq x.2
    rw [continuousOn_iff_continuous_domRestrict]
    refine (F₁.embedding.continuous.comp (f.continuous.comp e.symm.continuous)).congr fun x => ?_
    show F₁.ι (f (e.symm x)) = F₁.ι (f (Function.invFun F₀.ι x))
    rw [heq]
  -- properness of `G`
  have hprop : ∀ y ∉ (↑F₁.P : Set F₁.X.carrier), ∃ V ∈ 𝓝 y, ∃ Q : Set F₀.X.carrier, IsCompact Q ∧
      Q ⊆ (↑F₀.P)ᶜ ∧ ∀ x ∉ (↑F₀.P : Set F₀.X.carrier), G x ∈ V → x ∈ Q := by
    intro y hy
    rw [← Set.mem_compl_iff, ← hrange₁] at hy
    obtain ⟨t, rfl⟩ := hy
    have := ChartedSpace.locallyCompactSpace ℂ S
    obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds t
    refine ⟨F₁.ι '' C, F₁.embedding.image_mem_nhds.2 hC, F₀.ι '' (f.symm '' C),
      (hCc.image f.symm.continuous).image F₀.embedding.continuous, ?_, ?_⟩
    · rw [← hrange₀]
      exact image_subset_range _ _
    · intro x hx hxV
      rw [← Set.mem_compl_iff, ← hrange₀] at hx
      obtain ⟨s, rfl⟩ := hx
      rw [hGι] at hxV
      obtain ⟨c, hc, hcs⟩ := hxV
      refine ⟨s, ⟨c, hc, ?_⟩, rfl⟩
      rw [F₁.embedding.injective hcs, f.symm_apply_apply]
  have hlim := fun p (hp : p ∈ (↑F₀.P : Set F₀.X.carrier)) =>
    s82lc_tendsto_puncture F₀.P.finite_toSet F₁.P.finite_toSet hGc hprop hp
  set fb : F₀.X.carrier → F₁.X.carrier := fun x =>
    if hx : x ∈ (↑F₀.P : Set F₀.X.carrier) then (hlim x hx).choose else G x with hfb
  have hfbG : ∀ x ∉ (↑F₀.P : Set F₀.X.carrier), fb x = G x := fun x hx => by
    rw [hfb]; exact dite_eq_right_of_eq_false (eq_false hx)
  refine ⟨fb, continuous_iff_continuousAt.2 fun x => ?_, fun s => ?_, fun p hp => ?_⟩
  · by_cases hx : x ∈ (↑F₀.P : Set F₀.X.carrier)
    · -- at a puncture: the limit, since `fb = G` on a punctured neighbourhood
      have hpx : fb x = (hlim x hx).choose := by rw [hfb]; exact dite_eq_left_of_eq_true (eq_true hx)
      have hT := (hlim x hx).choose_spec.2
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hpx]
      have hmem : (↑F₀.P : Set F₀.X.carrier)ᶜ ∈ 𝓝[{x}ᶜ] x := by
        refine mem_nhdsWithin.2 ⟨(↑F₀.P \ {x} : Set F₀.X.carrier)ᶜ,
          (F₀.P.finite_toSet.sdiff).isClosed.isOpen_compl, fun h => h.2 rfl, ?_⟩
        rintro z ⟨hz1, hz2⟩ hzP
        exact hz1 ⟨hzP, hz2⟩
      refine ((hT.mono_left (nhdsWithin_le_of_mem hmem)).congr' ?_)
      filter_upwards [hmem] with z hz
      exact (hfbG z hz).symm
    · have hev : fb =ᶠ[𝓝 x] G := by
        filter_upwards [F₀.P.finite_toSet.isClosed.isOpen_compl.mem_nhds hx] with z hz
        exact hfbG z hz
      exact ((hGc.continuousAt (F₀.P.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)).congr hev.symm)
  · have hs : F₀.ι s ∉ (↑F₀.P : Set F₀.X.carrier) := by
      rw [← Set.mem_compl_iff, ← hrange₀]; exact ⟨s, rfl⟩
    rw [hfbG _ hs, hGι]
  · have hpx : fb p = (hlim p hp).choose := by rw [hfb]; exact dite_eq_left_of_eq_true (eq_true hp)
    rw [hpx]
    exact (hlim p hp).choose_spec.1

/-- **W2.** -/
theorem s82lc_extend_homeomorph {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n g' n' : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g' n' 0)
    (f : S₀ ≃ₜ S) :
    ∃ fb : F₀.X.carrier ≃ₜ F₁.X.carrier, (∀ s, fb (F₀.ι s) = F₁.ι (f s)) ∧ fb '' ↑F₀.P = ↑F₁.P := by
  obtain ⟨a, ha, haι, haP⟩ := s82lc_extend_continuous F₀ F₁ f
  obtain ⟨b, hb, hbι, hbP⟩ := s82lc_extend_continuous F₁ F₀ f.symm
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  have hrange₁ : range F₁.ι = (↑F₁.P : Set F₁.X.carrier)ᶜ := by
    rw [F₁.range_ι]; simp
  have hd₀ : Dense (range F₀.ι) := by
    rw [hrange₀, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    exact mem_closure_iff_nhdsWithin_neBot.2 (s82lc_nhdsWithin_compl_neBot F₀.P.finite_toSet x)
  have hd₁ : Dense (range F₁.ι) := by
    rw [hrange₁, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    exact mem_closure_iff_nhdsWithin_neBot.2 (s82lc_nhdsWithin_compl_neBot F₁.P.finite_toSet x)
  have hba : ∀ x, b (a x) = x := by
    have := Continuous.ext_on hd₀ (hb.comp ha) continuous_id (f := b ∘ a) (g := id) (by
      rintro _ ⟨s, rfl⟩
      show b (a (F₀.ι s)) = F₀.ι s
      rw [haι, hbι, f.symm_apply_apply])
    exact fun x => congrFun this x
  have hab : ∀ y, a (b y) = y := by
    have := Continuous.ext_on hd₁ (ha.comp hb) continuous_id (f := a ∘ b) (g := id) (by
      rintro _ ⟨s, rfl⟩
      show a (b (F₁.ι s)) = F₁.ι s
      rw [hbι, haι, f.apply_symm_apply])
    exact fun y => congrFun this y
  refine ⟨⟨⟨a, b, hba, hab⟩, ha, hb⟩, haι, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact haP x hx
  · intro hy
    exact ⟨b y, hbP y hy, hab y⟩

/-- **Local normal form** of a non-constant analytic germ: `h = h(c) + ψ^e` with `e > 0` and `ψ` a local coordinate
(`ψ(c) = 0`, `ψ'(c) ≠ 0`). -/
theorem s82lc_normal_form {h : ℂ → ℂ} {c : ℂ} (hh : AnalyticAt ℂ h c) (hnc : ¬ ∀ᶠ z in 𝓝 c, h z = h c) :
    ∃ (e : ℕ) (ψ : ℂ → ℂ), 0 < e ∧ AnalyticAt ℂ ψ c ∧ ψ c = 0 ∧ deriv ψ c ≠ 0 ∧
      ∀ᶠ z in 𝓝 c, h z = h c + ψ z ^ e := by
  have hsub : AnalyticAt ℂ (fun z => h z - h c) c := hh.sub analyticAt_const
  have hnc' : ¬ ∀ᶠ z in 𝓝 c, h z - h c = 0 := fun H => hnc (H.mono fun z hz => sub_eq_zero.1 hz)
  obtain ⟨e, g, hg, hg0, hgeq⟩ := hsub.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnc'
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exfalso
      have := hgeq.self_of_nhds
      simp only [sub_self, pow_zero, one_smul] at this
      exact hg0 this.symm
    · exact he
  -- an analytic `e`-th root of `g`
  set b : ℂ := g c ^ ((e : ℂ)⁻¹) with hb
  have hbe : b ^ e = g c := cpow_nat_inv_pow _ he.ne'
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hbe
    exact hg0 hbe.symm
  have hq : AnalyticAt ℂ (fun z => g z / g c) c := hg.div analyticAt_const hg0
  have hq1 : (fun z => g z / g c) c ∈ slitPlane := by
    simp only [div_self hg0]
    exact one_mem_slitPlane
  have hroot : AnalyticAt ℂ (fun z => (g z / g c) ^ ((e : ℂ)⁻¹)) c := hq.cpow analyticAt_const hq1
  set w : ℂ → ℂ := fun z => b * (g z / g c) ^ ((e : ℂ)⁻¹) with hw
  have hwa : AnalyticAt ℂ w c := analyticAt_const.mul hroot
  have hwe : ∀ z, w z ^ e = g z := fun z => by
    simp only [hw, mul_pow, cpow_nat_inv_pow _ he.ne']
    field_simp
    rw [hbe, mul_comm]
  have hwc : w c = b := by
    rw [hw]
    simp only [div_self hg0, one_cpow, mul_one]
  refine ⟨e, fun z => (z - c) * w z, he, (analyticAt_id.sub analyticAt_const).mul hwa, by simp, ?_, ?_⟩
  · have hd : HasDerivAt (fun z => (z - c) * w z) (1 * w c + (c - c) * deriv w c) c :=
      ((hasDerivAt_id c).sub_const c).mul hwa.differentiableAt.hasDerivAt
    rw [hd.deriv, sub_self, zero_mul, add_zero, one_mul, hwc]
    exact hb0
  · filter_upwards [hgeq] with z hz
    rw [mul_pow, hwe, ← smul_eq_mul, ← hz]
    ring

/-- At most `e` preimages: if `h = h(c) + ψ^e` with `ψ` injective on `U₀`, every fibre of `h` meets `U₀` in at most
`e` points. -/
theorem s82lc_fibre_le {h ψ : ℂ → ℂ} {c : ℂ} {e : ℕ} (he : 0 < e) {U₀ : Set ℂ} (hinj : InjOn ψ U₀)
    (heq : ∀ z ∈ U₀, h z = h c + ψ z ^ e) (t : ℂ) :
    (U₀ ∩ h ⁻¹' {t}).Finite ∧ (U₀ ∩ h ⁻¹' {t}).ncard ≤ e := by
  classical
  set R := Polynomial.nthRootsFinset e (t - h c) with hR
  have hmaps : MapsTo ψ (U₀ ∩ h ⁻¹' {t}) (R : Set ℂ) := by
    intro z hz
    rw [hR, Polynomial.nthRootsFinset_toSet he, mem_ofPred_eq]
    have := heq z hz.1
    rw [show h z = t from hz.2] at this
    rw [this]
    ring
  have hRc : (R : Set ℂ).ncard ≤ e := by
    rw [Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots e _)
  have hfin : (U₀ ∩ h ⁻¹' {t}).Finite :=
    Set.Finite.of_finite_image ((R.finite_toSet).subset (hmaps.image_subset)) (hinj.mono inter_subset_left)
  refine ⟨hfin, ?_⟩
  calc (U₀ ∩ h ⁻¹' {t}).ncard = (ψ '' (U₀ ∩ h ⁻¹' {t})).ncard :=
        ((hinj.mono inter_subset_left).ncard_image).symm
    _ ≤ (R : Set ℂ).ncard := Set.ncard_le_ncard hmaps.image_subset R.finite_toSet
    _ ≤ e := hRc

/-- At least `e` preimages: if `h = h(c) + ψ^e` near `c` with `ψ` a local coordinate, every value `t ≠ h(c)` close
to `h(c)` is taken at `e` distinct points of any given neighbourhood of `c`. -/
theorem s82lc_fibre_ge {h ψ : ℂ → ℂ} {c : ℂ} {e : ℕ} (he : 0 < e) (hψ : AnalyticAt ℂ ψ c) (hψ0 : ψ c = 0)
    (hψ' : deriv ψ c ≠ 0) (heq : ∀ᶠ z in 𝓝 c, h z = h c + ψ z ^ e) {U : Set ℂ} (hU : U ∈ 𝓝 c) :
    ∀ᶠ t in 𝓝[≠] (h c), ∃ z : Fin e → ℂ, Function.Injective z ∧ ∀ j, z j ∈ U ∧ h (z j) = t := by
  have hs : HasStrictDerivAt ψ (deriv ψ c) c := hψ.hasStrictDerivAt
  set L := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph ψ with hL
  have hLc : (L : ℂ → ℂ) = ψ := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph_coe
  have hcL : c ∈ L.source := (hs.hasStrictFDerivAt_equiv hψ').mem_toOpenPartialHomeomorph_source
  -- a ball `B(0, ρ)` in the target whose preimage lies in `U` and in the domain of the normal form
  have hW : U ∩ {z | h z = h c + ψ z ^ e} ∈ 𝓝 c := Filter.inter_mem hU heq
  have hT : L.target ∩ L.symm ⁻¹' (U ∩ {z | h z = h c + ψ z ^ e}) ∈ 𝓝 (L c) := by
    have h1 : U ∩ {z | h z = h c + ψ z ^ e} ∈ 𝓝 (L.symm (L c)) := by rwa [L.left_inv hcL]
    exact Filter.inter_mem (L.open_target.mem_nhds (L.map_source hcL))
      ((L.continuousAt_symm (L.map_source hcL)).preimage_mem_nhds h1)
  rw [hLc, hψ0] at hT
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hT
  have hρe : 0 < ρ ^ e := pow_pos hρ e
  -- values `t` with `0 < |t - h c| < ρ^e`
  have hev : ∀ᶠ t in 𝓝[≠] (h c), t ∈ ball (h c) (ρ ^ e) := nhdsWithin_le_nhds (ball_mem_nhds _ hρe)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
  set a : ℂ := t - h c with ha
  have ha0 : a ≠ 0 := sub_ne_zero.2 htne
  set τ : ℂ := a ^ ((e : ℂ)⁻¹) with hτ
  have hτe : τ ^ e = a := cpow_nat_inv_pow _ he.ne'
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hτe
    exact ha0 hτe.symm
  have hτn : ‖τ‖ < ρ := by
    have h1 : ‖τ‖ ^ e < ρ ^ e := by
      rw [← norm_pow, hτe, ha, ← dist_eq_norm]
      exact ht
    exact lt_of_pow_lt_pow_left₀ e hρ.le h1
  set ζ := Complex.exp (2 * Real.pi * I / e) with hζ
  have hprim : IsPrimitiveRoot ζ e := Complex.isPrimitiveRoot_exp e he.ne'
  have hζn : ‖ζ‖ = 1 := by
    have := hprim.norm'_eq_one he.ne'
    exact this
  set v : Fin e → ℂ := fun j => τ * ζ ^ (j : ℕ) with hv
  have hvb : ∀ j, v j ∈ ball (0 : ℂ) ρ := fun j => by
    rw [mem_ball_zero_iff, hv]
    simp only [norm_mul, norm_pow, hζn, one_pow, mul_one]
    exact hτn
  have hvinj : Function.Injective v := by
    intro i j hij
    have h1 : ζ ^ (i : ℕ) = ζ ^ (j : ℕ) := mul_left_cancel₀ hτ0 hij
    exact Fin.ext (hprim.pow_inj i.2 j.2 h1)
  refine ⟨fun j => L.symm (v j), ?_, fun j => ⟨(hball (hvb j)).2.1, ?_⟩⟩
  · intro i j hij
    exact hvinj (L.symm.injOn (hball (hvb i)).1 (hball (hvb j)).1 hij)
  · have h1 := (hball (hvb j)).2.2
    have h2 : ψ (L.symm (v j)) = v j := by
      rw [← hLc]
      exact L.right_inv (hball (hvb j)).1
    show h (L.symm (v j)) = t
    rw [show h (L.symm (v j)) = h c + ψ (L.symm (v j)) ^ e from h1, h2, hv]
    simp only [mul_pow, ← pow_mul]
    rw [mul_comm (j : ℕ) e, pow_mul, hprim.pow_eq_one, one_pow, mul_one, hτe, ha]
    ring

section ManifoldLocal

variable {Y X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The chart expression `h_y = φ_{pr y} ∘ pr ∘ φ_y⁻¹` of a holomorphic map is holomorphic on an open neighbourhood
of `φ_y(y)` inside the chart target on which `pr ∘ φ_y⁻¹` stays in the chart source at `pr y`. -/
theorem s82lc_chart_expr {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) :
    ∃ W : Set ℂ, IsOpen W ∧ chartAt ℂ y y ∈ W ∧ W ⊆ (chartAt ℂ y).target ∧
      (∀ z ∈ W, pr ((chartAt ℂ y).symm z) ∈ (chartAt ℂ (pr y)).source) ∧
      DifferentiableOn ℂ (fun z => chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z))) W := by
  set φ := chartAt ℂ y
  set v := chartAt ℂ (pr y)
  set W := φ.target ∩ φ.symm ⁻¹' (pr ⁻¹' v.source) with hW
  have hWo : IsOpen W := φ.isOpen_inter_preimage_symm (v.open_source.preimage hpr.continuous)
  refine ⟨W, hWo, ⟨φ.map_source (mem_chart_source ℂ y), ?_⟩, inter_subset_left, fun z hz => hz.2, ?_⟩
  · show pr (φ.symm (φ y)) ∈ v.source
    rw [φ.left_inv (mem_chart_source ℂ y)]
    exact mem_chart_source ℂ _
  · intro z hz
    have hp : φ.symm z ∈ φ.source := φ.map_target hz.1
    have h := ((s23_mdifferentiableAt_iff (f := pr) (x := y) (y := pr y) hp hz.2).1 (hpr _)).2
    rw [φ.right_inv hz.1] at h
    exact h.differentiableWithinAt

omit [IsManifold 𝓘(ℂ) ω Y] in
/-- A nonempty open set of a surface is infinite. -/
theorem s82lc_open_infinite [T2Space Y] {U : Set Y} (hU : IsOpen U) {y : Y} (hy : y ∈ U) : U.Infinite := by
  have := s82lc_nhdsWithin_compl_neBot (P := ({y} : Set Y)) (Set.finite_singleton y) y
  exact infinite_of_mem_nhds y (hU.mem_nhds hy)

/-- Fibres that are finite and nonempty prevent the chart expression from being locally constant. -/
theorem s82lc_not_locally_const [T2Space Y] {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr)
    (hfib : ∀ x, (pr ⁻¹' {x}).ncard ≠ 0) (y : Y) :
    ¬ ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
      chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) := by
  intro hev
  obtain ⟨W, hWo, hcW, hWt, hWs, -⟩ := s82lc_chart_expr hpr y
  set φ := chartAt ℂ y
  set v := chartAt ℂ (pr y)
  obtain ⟨O, hOsub, hOo, hcO⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem hev (hWo.mem_nhds hcW))
  -- `pr` is constant on the open set `φ⁻¹ O`
  have hconst : φ.source ∩ φ ⁻¹' O ⊆ pr ⁻¹' {pr y} := by
    intro t ht
    have hz := hOsub ht.2
    have h1 : v (pr (φ.symm (φ t))) = v (pr (φ.symm (φ y))) := hz.1
    rw [φ.left_inv ht.1, φ.left_inv (mem_chart_source ℂ y)] at h1
    have h2 : pr t ∈ v.source := by
      have := hWs _ hz.2
      rwa [φ.left_inv ht.1] at this
    exact v.injOn h2 (mem_chart_source ℂ _) h1
  have hinf : (φ.source ∩ φ ⁻¹' O).Infinite :=
    s82lc_open_infinite (φ.isOpen_inter_preimage hOo) ⟨mem_chart_source ℂ y, hcO⟩
  exact hfib (pr y) (Set.Infinite.ncard (hinf.mono hconst))

/-- **Transfer of the lower bound** to surfaces: if the chart expression at `y` is `h(c) + ψ^e`, then every point
`x' ≠ pr y` near `pr y` has `e` distinct preimages in any given neighbourhood of `y`. -/
theorem s82lc_manifold_fibre_ge {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) {e : ℕ} {ψ : ℂ → ℂ}
    (he : 0 < e) (hψ : AnalyticAt ℂ ψ (chartAt ℂ y y)) (hψ0 : ψ (chartAt ℂ y y) = 0)
    (hψ' : deriv ψ (chartAt ℂ y y) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
      chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ e) {U : Set Y} (hU : U ∈ 𝓝 y) :
    ∀ᶠ x' in 𝓝[≠] (pr y), ∃ z : Fin e → Y, Function.Injective z ∧ ∀ j, z j ∈ U ∧ pr (z j) = x' := by
  obtain ⟨W, hWo, hcW, hWt, hWs, -⟩ := s82lc_chart_expr hpr y
  set φ := chartAt ℂ y
  set v := chartAt ℂ (pr y)
  set h : ℂ → ℂ := fun z => v (pr (φ.symm z)) with hh
  have hU' : W ∩ φ.symm ⁻¹' U ∈ 𝓝 (φ y) := by
    refine Filter.inter_mem (hWo.mem_nhds hcW) ?_
    have : U ∈ 𝓝 (φ.symm (φ y)) := by rwa [φ.left_inv (mem_chart_source ℂ y)]
    exact (φ.continuousAt_symm (φ.map_source (mem_chart_source ℂ y))).preimage_mem_nhds this
  have hge := s82lc_fibre_ge (h := h) he hψ hψ0 hψ' heq hU'
  have hhc : h (φ y) = v (pr y) := by
    show v (pr (φ.symm (φ y))) = v (pr y)
    rw [φ.left_inv (mem_chart_source ℂ y)]
  rw [hhc] at hge
  -- `v` maps a punctured neighbourhood of `pr y` into a punctured neighbourhood of `v (pr y)`
  have hv : Tendsto v (𝓝[≠] (pr y)) (𝓝[≠] (v (pr y))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((v.continuousAt (mem_chart_source ℂ _)).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [nhdsWithin_le_nhds (v.open_source.mem_nhds (mem_chart_source ℂ (pr y))),
      self_mem_nhdsWithin] with x' hx' hne
    exact fun h' => hne (v.injOn hx' (mem_chart_source ℂ _) h')
  filter_upwards [hv.eventually hge, nhdsWithin_le_nhds (v.open_source.mem_nhds (mem_chart_source ℂ (pr y)))]
    with x' hx' hxs
  obtain ⟨z, hzi, hz⟩ := hx'
  refine ⟨fun j => φ.symm (z j), fun i j hij => hzi (φ.symm.injOn (hWt (hz i).1.1) (hWt (hz j).1.1) hij),
    fun j => ⟨(hz j).1.2, ?_⟩⟩
  have h1 : v (pr (φ.symm (z j))) = v x' := (hz j).2
  exact v.injOn (hWs _ (hz j).1.1) hxs h1

/-- **Transfer of the upper bound**: near `y`, every fibre of `pr` has at most `e` points. -/
theorem s82lc_manifold_fibre_le {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) {e : ℕ} {ψ : ℂ → ℂ}
    (he : 0 < e) (hψ : AnalyticAt ℂ ψ (chartAt ℂ y y)) (hψ' : deriv ψ (chartAt ℂ y y) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
      chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ e) :
    ∃ U₀ : Set Y, IsOpen U₀ ∧ y ∈ U₀ ∧ ∀ x', (U₀ ∩ pr ⁻¹' {x'}).Finite ∧ (U₀ ∩ pr ⁻¹' {x'}).ncard ≤ e := by
  obtain ⟨W, hWo, hcW, hWt, hWs, -⟩ := s82lc_chart_expr hpr y
  set φ := chartAt ℂ y
  set v := chartAt ℂ (pr y)
  set h : ℂ → ℂ := fun z => v (pr (φ.symm z)) with hh
  have hs : HasStrictDerivAt ψ (deriv ψ (φ y)) (φ y) := hψ.hasStrictDerivAt
  set L := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph ψ with hL
  have hLc : (L : ℂ → ℂ) = ψ := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph_coe
  have hcL : φ y ∈ L.source := (hs.hasStrictFDerivAt_equiv hψ').mem_toOpenPartialHomeomorph_source
  obtain ⟨O, hOsub, hOo, hcO⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem heq
    (Filter.inter_mem (hWo.mem_nhds hcW) (L.open_source.mem_nhds hcL)))
  have hinj : InjOn ψ O := by
    rw [← hLc]
    exact L.injOn.mono fun z hz => (hOsub hz).2.2
  have heqO : ∀ z ∈ O, h z = h (φ y) + ψ z ^ e := fun z hz => (hOsub hz).1
  refine ⟨φ.source ∩ φ ⁻¹' O, φ.isOpen_inter_preimage hOo, ⟨mem_chart_source ℂ y, hcO⟩, fun x' => ?_⟩
  obtain ⟨hfin, hle⟩ := s82lc_fibre_le (h := h) he hinj heqO (v x')
  have hmaps : InjOn φ (φ.source ∩ φ ⁻¹' O ∩ pr ⁻¹' {x'}) := φ.injOn.mono fun t ht => ht.1.1
  have himg : φ '' (φ.source ∩ φ ⁻¹' O ∩ pr ⁻¹' {x'}) ⊆ O ∩ h ⁻¹' {v x'} := by
    rintro _ ⟨t, ⟨⟨hts, htO⟩, htx⟩, rfl⟩
    refine ⟨htO, ?_⟩
    show v (pr (φ.symm (φ t))) = v x'
    rw [φ.left_inv hts, show pr t = x' from htx]
  have hfin' : (φ.source ∩ φ ⁻¹' O ∩ pr ⁻¹' {x'}).Finite :=
    Set.Finite.of_finite_image (hfin.subset himg) hmaps
  refine ⟨hfin', ?_⟩
  calc (φ.source ∩ φ ⁻¹' O ∩ pr ⁻¹' {x'}).ncard = (φ '' (φ.source ∩ φ ⁻¹' O ∩ pr ⁻¹' {x'})).ncard :=
        (hmaps.ncard_image).symm
    _ ≤ (O ∩ h ⁻¹' {v x'}).ncard := Set.ncard_le_ncard himg hfin
    _ ≤ e := hle

end ManifoldLocal

/-- A local holomorphic coordinate: an analytic `ψ` with `ψ'(c) ≠ 0` restricts to an open partial homeomorphism
with source inside a given neighbourhood of `c`, holomorphic in both directions. -/
theorem s82lc_local_coordinate {ψ : ℂ → ℂ} {c : ℂ} (hψ : AnalyticAt ℂ ψ c) (hψ' : deriv ψ c ≠ 0) {U : Set ℂ}
    (hU : U ∈ 𝓝 c) :
    ∃ L : OpenPartialHomeomorph ℂ ℂ, c ∈ L.source ∧ L.source ⊆ U ∧ (L : ℂ → ℂ) = ψ ∧
      DifferentiableOn ℂ L L.source ∧ DifferentiableOn ℂ L.symm L.target := by
  have hs : HasStrictDerivAt ψ (deriv ψ c) c := hψ.hasStrictDerivAt
  set L₀ := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph ψ with hL₀
  have hLc : (L₀ : ℂ → ℂ) = ψ := (hs.hasStrictFDerivAt_equiv hψ').toOpenPartialHomeomorph_coe
  have hcL : c ∈ L₀.source := (hs.hasStrictFDerivAt_equiv hψ').mem_toOpenPartialHomeomorph_source
  -- near `c`, `ψ` is analytic with nonzero derivative
  have hgood : ∀ᶠ z in 𝓝 c, AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 := by
    have hcont : ContinuousAt (deriv ψ) c := hψ.deriv.continuousAt
    exact hψ.eventually_analyticAt.and (hcont.eventually_ne hψ')
  obtain ⟨O, hOsub, hOo, hcO⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem hgood hU)
  refine ⟨L₀.restrOpen O hOo, ⟨hcL, hcO⟩, fun z hz => (hOsub hz.2).2, hLc, ?_, ?_⟩
  · intro z hz
    have : AnalyticAt ℂ ψ z := (hOsub hz.2).1.1
    show DifferentiableWithinAt ℂ (L₀ : ℂ → ℂ) _ z
    rw [hLc]
    exact this.differentiableAt.differentiableWithinAt
  · intro b hb
    set L := L₀.restrOpen O hOo
    have ha : L.symm b ∈ L.source := L.map_target hb
    have h1 : AnalyticAt ℂ ψ (L.symm b) := (hOsub ha.2).1.1
    have h2 : deriv ψ (L.symm b) ≠ 0 := (hOsub ha.2).1.2
    have hcoe : (L : ℂ → ℂ) = ψ := hLc
    have hd : HasDerivAt L (deriv ψ (L.symm b)) (L.symm b) := by
      rw [hcoe]
      exact h1.differentiableAt.hasDerivAt
    exact (L.hasDerivAt_symm hb h2 hd).differentiableAt.differentiableWithinAt

/-- Properness of a map from a compact space: if the fibre over `x` lies in an open set `U`, then so does the
preimage of a neighbourhood of `x`. -/
theorem s82lc_preimage_nhds_subset {Y X : Type*} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace X]
    [T2Space X] {pr : Y → X} (hpr : Continuous pr) {x : X} {U : Set Y} (hU : IsOpen U)
    (hxU : pr ⁻¹' {x} ⊆ U) : ∃ N ∈ 𝓝 x, pr ⁻¹' N ⊆ U := by
  have hK : IsCompact (pr '' Uᶜ) := (hU.isClosed_compl.isCompact).image hpr
  refine ⟨(pr '' Uᶜ)ᶜ, hK.isClosed.isOpen_compl.mem_nhds ?_, ?_⟩
  · rintro ⟨t, ht, htx⟩
    exact ht (hxU htx)
  · intro t ht
    by_contra htU
    exact ht ⟨t, htU, rfl⟩

/-- `k` distinct points of a finite set `F` force `k ≤ ncard F`. -/
theorem s82lc_le_ncard {α : Type*} {F : Set α} (hF : F.Finite) {k : ℕ} {z : Fin k → α}
    (hz : Function.Injective z) (hzF : ∀ j, z j ∈ F) : k ≤ F.ncard := by
  have h := Set.ncard_le_ncard (s := range z) (t := F) (by rintro _ ⟨j, rfl⟩; exact hzF j) hF
  rwa [Set.ncard_range_of_injective hz, Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-- The complement of a finite set `P` is in the punctured neighbourhood filter of every point. -/
theorem s82lc_compl_mem_nhdsNE {X : Type*} [TopologicalSpace X] [T1Space X] {P : Set X} (hP : P.Finite) (x : X) :
    Pᶜ ∈ 𝓝[≠] x := by
  refine mem_nhdsWithin.2 ⟨(P \ {x})ᶜ, (hP.sdiff).isClosed.isOpen_compl, fun h => h.2 rfl, ?_⟩
  rintro z ⟨hz1, hz2⟩ hzP
  exact hz1 ⟨hzP, hz2⟩

/-- **Branching index.**  For a holomorphic map of closed Riemann surfaces whose fibres have two points off a
finite set `P` and one point over `P`, the chart expression at `y` is `h(c) + ψ^e` with `ψ` a local coordinate and
`e = 2` over `P`, `e = 1` elsewhere. -/
theorem s82lc_branch_index {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) (y : Y.carrier) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (chartAt ℂ y y) ∧ ψ (chartAt ℂ y y) = 0 ∧ deriv ψ (chartAt ℂ y y) ≠ 0 ∧
      (pr y ∈ P → ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
        chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ 2) ∧
      (pr y ∉ P → ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
        chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ 1) := by
  have hfib0 : ∀ x, (pr ⁻¹' {x}).ncard ≠ 0 := by
    intro x
    by_cases hx : x ∈ P
    · rw [hpr.2.2.2 x hx]; exact one_ne_zero
    · rw [hpr.2.2.1 x hx]; exact two_ne_zero
  have hfin : ∀ x, (pr ⁻¹' {x}).Finite := fun x => Set.finite_of_ncard_ne_zero (hfib0 x)
  -- the normal form at any point
  have hnf : ∀ y' : Y.carrier, ∃ (e : ℕ) (ψ : ℂ → ℂ), 0 < e ∧ AnalyticAt ℂ ψ (chartAt ℂ y' y') ∧
      ψ (chartAt ℂ y' y') = 0 ∧ deriv ψ (chartAt ℂ y' y') ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ y' y'), chartAt ℂ (pr y') (pr ((chartAt ℂ y').symm z)) =
        chartAt ℂ (pr y') (pr ((chartAt ℂ y').symm (chartAt ℂ y' y'))) + ψ z ^ e := by
    intro y'
    obtain ⟨W, hWo, hcW, -, -, hWd⟩ := s82lc_chart_expr hpr.1 y'
    exact s82lc_normal_form (hWd.analyticAt (hWo.mem_nhds hcW)) (s82lc_not_locally_const hpr.1 hfib0 y')
  obtain ⟨e, ψ, he, hψ, hψ0, hψ', heq⟩ := hnf y
  refine ⟨ψ, hψ, hψ0, hψ', fun hyP => ?_, fun hyP => ?_⟩
  all_goals have hPf : (↑P : Set X.carrier).Finite := P.finite_toSet
  all_goals have hNe : (𝓝[≠] (pr y)).NeBot := s82lc_nhdsWithin_compl_neBot (Set.finite_singleton (pr y)) (pr y)
  · 
    -- the fibre over `pr y` is `{y}`
    have hfy : pr ⁻¹' {pr y} = {y} := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hpr.2.2.2 _ hyP)
      have hy : y ∈ pr ⁻¹' {pr y} := rfl
      rw [ha] at hy ⊢
      rw [mem_singleton_iff.1 hy]
    -- at most two preimages near `y` (two distinct points over a nearby `x' ∉ P`)
    have hle2 : e ≤ 2 := by
      have hge := s82lc_manifold_fibre_ge hpr.1 y he hψ hψ0 hψ' heq (Filter.univ_mem)
      obtain ⟨x', ⟨z, hz, hzx⟩, hx'P⟩ := (hge.and (s82lc_compl_mem_nhdsNE hPf (pr y))).exists
      have := s82lc_le_ncard (hfin x') hz fun j => (hzx j).2
      rwa [hpr.2.2.1 x' hx'P] at this
    -- at least two: near `pr y` every fibre lies in a neighbourhood of `y` with at most `e` points of a fibre
    have hge2 : 2 ≤ e := by
      obtain ⟨U₀, hU₀o, hyU₀, hU₀⟩ := s82lc_manifold_fibre_le hpr.1 y he hψ hψ' heq
      obtain ⟨N, hN, hNU⟩ := s82lc_preimage_nhds_subset hpr.1.continuous hU₀o (by rw [hfy]; simpa using hyU₀)
      have hNe' := s82lc_nhdsWithin_compl_neBot hPf (pr y)
      obtain ⟨x', hx'N, hx'P⟩ := hNe'.nonempty_of_mem
        (Filter.inter_mem (nhdsWithin_le_nhds hN) (self_mem_nhdsWithin (s := (↑P : Set X.carrier)ᶜ)))
      have hsub : pr ⁻¹' {x'} = U₀ ∩ pr ⁻¹' {x'} := by
        ext t
        exact ⟨fun ht => ⟨hNU (show pr t ∈ N from (mem_singleton_iff.1 ht).symm ▸ hx'N), ht⟩, fun ht => ht.2⟩
      have := (hU₀ x').2
      rw [← hsub, hpr.2.2.1 x' hx'P] at this
      exact this
    have : e = 2 := le_antisymm hle2 hge2
    rw [← this]
    exact heq
  · -- a second point `y'` of the fibre; disjoint neighbourhoods of `y` and `y'`
    obtain ⟨a, b, hab, hfab⟩ := Set.ncard_eq_two.1 (hpr.2.2.1 _ hyP)
    have hyab : y = a ∨ y = b := by
      have : y ∈ pr ⁻¹' {pr y} := rfl
      rw [hfab] at this
      exact this
    obtain ⟨y', hy'ne, hy'⟩ : ∃ y', y ≠ y' ∧ pr y' = pr y := by
      rcases hyab with rfl | rfl
      · refine ⟨b, hab, ?_⟩
        have : b ∈ pr ⁻¹' {pr y} := by rw [hfab]; exact Or.inr rfl
        exact this
      · refine ⟨a, hab.symm, ?_⟩
        have : a ∈ pr ⁻¹' {pr y} := by rw [hfab]; exact Or.inl rfl
        exact this
    obtain ⟨U, U', hUo, hU'o, hyU, hy'U', hUU'⟩ := t2_separation hy'ne
    obtain ⟨e', ψ', he', hψ₂, hψ₂0, hψ₂', heq'⟩ := hnf y'
    have hge := s82lc_manifold_fibre_ge hpr.1 y he hψ hψ0 hψ' heq (hUo.mem_nhds hyU)
    have hge' := s82lc_manifold_fibre_ge hpr.1 y' he' hψ₂ hψ₂0 hψ₂' heq' (hU'o.mem_nhds hy'U')
    rw [hy'] at hge'
    obtain ⟨x', ⟨⟨z, hz, hzx⟩, ⟨z', hz', hzx'⟩⟩, hx'P⟩ :=
      ((hge.and hge').and (s82lc_compl_mem_nhdsNE hPf (pr y))).exists
    -- `e + e'` distinct points over `x'`
    set w : Fin (e + e') → Y.carrier := fun j => Sum.elim z z' (finSumFinEquiv.symm j) with hw
    have hwi : Function.Injective w := by
      intro i j hij
      apply finSumFinEquiv.symm.injective
      rcases hi : finSumFinEquiv.symm i with i' | i' <;> rcases hj : finSumFinEquiv.symm j with j' | j' <;>
        simp only [hw, hi, hj, Sum.elim_inl, Sum.elim_inr] at hij
      · rw [hz hij]
      · exact absurd ((hzx i').1) (Set.disjoint_left.1 hUU'.symm (hij ▸ (hzx' j').1))
      · exact absurd ((hzx j').1) (Set.disjoint_left.1 hUU'.symm (hij.symm ▸ (hzx' i').1))
      · rw [hz' hij]
    have hwF : ∀ j, w j ∈ pr ⁻¹' {x'} := by
      intro j
      rcases hj : finSumFinEquiv.symm j with j' | j'
      · simp only [hw, hj, Sum.elim_inl]; exact (hzx j').2
      · simp only [hw, hj, Sum.elim_inr]; exact (hzx' j').2
    have := s82lc_le_ncard (hfin x') hwi hwF
    rw [hpr.2.2.1 x' hx'P] at this
    have he1 : e = 1 := by omega
    rw [← he1]
    exact heq

section ManifoldCharts

variable {Y X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- An open partial homeomorphism of `ℂ` holomorphic in both directions is analytic in both directions. -/
theorem s82lc_contMDiffOn_of_differentiableOn {L : OpenPartialHomeomorph ℂ ℂ} (hL : DifferentiableOn ℂ L L.source) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω L L.source :=
  contMDiffOn_iff_contDiffOn.2 (hL.contDiffOn L.open_source)

/-- **Local inverse** off the branch points: if the chart expression at `y` is `h(c) + ψ` with `ψ` a local
coordinate, `pr` is a local biholomorphism at `y`. -/
theorem s82lc_local_inverse {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) {ψ : ℂ → ℂ}
    (hψ : AnalyticAt ℂ ψ (chartAt ℂ y y)) (hψ' : deriv ψ (chartAt ℂ y y) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
      chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ 1) :
    ∃ e : OpenPartialHomeomorph Y X, y ∈ e.source ∧ EqOn pr e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  obtain ⟨W, hWo, hcW, hWt, hWs, -⟩ := s82lc_chart_expr hpr y
  set φ := chartAt ℂ y with hφ
  set v := chartAt ℂ (pr y) with hv
  set hc := v (pr (φ.symm (φ y))) with hhc
  have hcy : hc = v (pr y) := by rw [hhc, φ.left_inv (mem_chart_source ℂ y)]
  have hA : AnalyticAt ℂ (fun z => hc + ψ z) (φ y) := analyticAt_const.add hψ
  have hA' : deriv (fun z => hc + ψ z) (φ y) ≠ 0 := by
    rw [deriv_const_add]; exact hψ'
  obtain ⟨L, hcL, hLO, hLc, hLd, hLsd⟩ := s82lc_local_coordinate hA hA'
    (Filter.inter_mem heq (hWo.mem_nhds hcW))
  have hLh : ∀ z ∈ L.source, L z = v (pr (φ.symm z)) := fun z hz => by
    rw [hLc]
    have := (hLO hz).1
    simp only [pow_one] at this
    exact this.symm
  refine ⟨φ.trans (L.trans v.symm), ?_, ?_, ?_⟩
  · refine ⟨mem_chart_source ℂ y, hcL, ?_⟩
    show L (φ y) ∈ v.target
    rw [hLh _ hcL, φ.left_inv (mem_chart_source ℂ y)]
    exact v.map_source (mem_chart_source ℂ _)
  · intro t ht
    have h1 : φ t ∈ L.source := ht.2.1
    show pr t = v.symm (L (φ t))
    rw [hLh _ h1, φ.left_inv ht.1, v.left_inv]
    have := hWs _ (hLO h1).2
    rwa [φ.left_inv ht.1] at this
  · intro x' hx'
    set e := φ.trans (L.trans v.symm)
    have hts : e.symm x' ∈ e.source := e.map_target hx'
    have hx'e : e (e.symm x') = x' := e.right_inv hx'
    set t := e.symm x'
    have h1 : φ t ∈ L.source := hts.2.1
    have h2 : L (φ t) ∈ v.target := hts.2.2
    have hx'v : x' = v.symm (L (φ t)) := hx'e.symm
    have hx'src : x' ∈ v.source := by rw [hx'v]; exact v.map_target h2
    have hvx : v x' = L (φ t) := by rw [hx'v, v.right_inv h2]
    have hLt : L (φ t) ∈ L.target := L.map_source h1
    have hφt : φ t ∈ φ.target := φ.map_source hts.1
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) v x' := mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hx'src
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) L.symm (v x') := by
      rw [hvx]
      exact ((hLsd _ hLt).differentiableAt (L.open_target.mem_nhds hLt)).mdifferentiableAt
    have hm3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ.symm (L.symm (v x')) := by
      rw [hvx, L.left_inv h1]
      exact mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ y) hφt
    exact (hm3.comp x' (hm2.comp x' hm1)).mdifferentiableWithinAt

/-- **Square-root chart** at a branch point: if the chart expression at `y` is `h(c) + ψ²` with `ψ` a local
coordinate, then `v ∘ pr = u²` for maximal-atlas charts `u` at `y` (with `u y = 0` and round target) and `v` at
`pr y` (with `v (pr y) = 0`). -/
theorem s82lc_sqrt_chart {pr : Y → X} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) {ψ : ℂ → ℂ}
    (hψ : AnalyticAt ℂ ψ (chartAt ℂ y y)) (hψ0 : ψ (chartAt ℂ y y) = 0) (hψ' : deriv ψ (chartAt ℂ y y) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (chartAt ℂ y y), chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm z)) =
      chartAt ℂ (pr y) (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) + ψ z ^ 2) :
    ∃ (u : OpenPartialHomeomorph Y ℂ) (v : OpenPartialHomeomorph X ℂ) (r : ℝ),
      u ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y ∧ v ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧
      y ∈ u.source ∧ u y = 0 ∧ 0 < r ∧ u.target = ball 0 r ∧ pr '' u.source ⊆ v.source ∧
      ∀ t ∈ u.source, v (pr t) = u t ^ 2 := by
  obtain ⟨W, hWo, hcW, hWt, hWs, -⟩ := s82lc_chart_expr hpr y
  set φ := chartAt ℂ y with hφ
  set v := chartAt ℂ (pr y) with hv
  set hc := v (pr (φ.symm (φ y))) with hhc
  obtain ⟨L, hcL, hLO, hLc, hLd, hLsd⟩ := s82lc_local_coordinate hψ hψ'
    (Filter.inter_mem heq (hWo.mem_nhds hcW))
  -- the chart `u₀ = L ∘ φ` and its round restriction `u`
  set u₀ := φ.trans L with hu₀
  have hyu₀ : y ∈ u₀.source := ⟨mem_chart_source ℂ y, hcL⟩
  have hu₀y : u₀ y = 0 := by
    show L (φ y) = 0
    rw [hLc]; exact hψ0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 u₀.open_target 0 (by rw [← hu₀y]; exact u₀.map_source hyu₀)
  have hso : IsOpen (u₀.source ∩ u₀ ⁻¹' ball 0 r) := u₀.isOpen_inter_preimage isOpen_ball
  set u := u₀.restrOpen (u₀.source ∩ u₀ ⁻¹' ball 0 r) hso with hu
  -- the translated chart `v' = v - h(c)`
  set τ : OpenPartialHomeomorph ℂ ℂ := (Homeomorph.addRight (-hc)).toOpenPartialHomeomorph with hτ
  set v' := v.trans τ with hv'
  have hτs : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω τ τ.source :=
    contMDiffOn_iff_contDiffOn.2 (by
      show ContDiffOn ℂ ω (fun z => z + -hc) _
      exact (contDiff_id.add contDiff_const).contDiffOn)
  have hτs' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω τ.symm τ.target :=
    contMDiffOn_iff_contDiffOn.2 (by
      show ContDiffOn ℂ ω (fun z => z - -hc) _
      exact (contDiff_id.sub contDiff_const).contDiffOn)
  have hφm := contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) y)
  have hφm' := contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) y)
  have hvm := contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (pr y))
  have hvm' := contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (pr y))
  have hLm := s82lc_contMDiffOn_of_differentiableOn hLd
  have hLm' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω L.symm L.target :=
    contMDiffOn_iff_contDiffOn.2 (hLsd.contDiffOn L.open_target)
  have hLh : ∀ z ∈ L.source, v (pr (φ.symm z)) = hc + L z ^ 2 := fun z hz => by
    rw [hLc]; exact (hLO hz).1
  refine ⟨u, v', r, ?_, ?_, ⟨hyu₀, hyu₀, show u₀ y ∈ ball (0 : ℂ) r by rw [hu₀y]; exact mem_ball_self hr⟩, hu₀y, hr, ?_, ?_, ?_⟩
  · refine IsManifold.mem_maximalAtlas_iff_contMDiffOn _ |>.2 ⟨?_, ?_⟩
    · exact hLm.comp (hφm.mono fun t ht => ht.1.1) fun t ht => ht.1.2
    · refine hφm'.comp (hLm'.mono fun w hw => hw.1.1) fun w hw => hw.1.2
  · refine IsManifold.mem_maximalAtlas_iff_contMDiffOn _ |>.2 ⟨?_, ?_⟩
    · exact hτs.comp (hvm.mono fun t ht => ht.1) fun t ht => ht.2
    · exact hvm'.comp (hτs'.mono fun w hw => hw.1) fun w hw => hw.2
  · ext w
    constructor
    · rintro ⟨hwt, -, hb⟩
      have h1 : u₀ (u₀.symm w) = w := u₀.right_inv hwt
      have hb' : u₀ (u₀.symm w) ∈ ball (0 : ℂ) r := hb
      rwa [h1] at hb'
    · intro hw
      have hwt : w ∈ u₀.target := hball hw
      exact ⟨hwt, u₀.map_target hwt, by
        show u₀ (u₀.symm w) ∈ ball 0 r
        rw [u₀.right_inv hwt]; exact hw⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : φ t ∈ L.source := ht.1.2
    have := hWs _ (hLO h1).2
    rw [φ.left_inv ht.1.1] at this
    exact ⟨this, trivial⟩
  · intro t ht
    have h1 : φ t ∈ L.source := ht.1.2
    have := hLh _ h1
    rw [φ.left_inv ht.1.1] at this
    show v (pr t) + -hc = L (φ t) ^ 2
    rw [this]
    ring

end ManifoldCharts

/-- **W1** (local form of a two-sheeted branched cover). -/
theorem s82lc_local_form {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) :
    IsCoveringMapOn pr (↑P)ᶜ ∧
      (∀ y, pr y ∉ P → ∃ e : OpenPartialHomeomorph Y.carrier X.carrier, y ∈ e.source ∧ EqOn pr e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) ∧
      ∀ y, pr y ∈ P → ∃ (u : OpenPartialHomeomorph Y.carrier ℂ) (v : OpenPartialHomeomorph X.carrier ℂ) (r : ℝ),
        u ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y.carrier ∧ v ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X.carrier ∧
        y ∈ u.source ∧ u y = 0 ∧ 0 < r ∧ u.target = ball 0 r ∧ pr '' u.source ⊆ v.source ∧
        ∀ t ∈ u.source, v (pr t) = u t ^ 2 := by
  have hloc : ∀ y, pr y ∉ P → ∃ e : OpenPartialHomeomorph Y.carrier X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
    intro y hy
    obtain ⟨ψ, hψ, -, hψ', -, h1⟩ := s82lc_branch_index hpr y
    exact s82lc_local_inverse hpr.1 y hψ hψ' (h1 hy)
  refine ⟨IsCoveringMapOn.of_isLocalHomeomorphOn hpr.1.continuous (IsLocalHomeomorphOn.mk _ _ fun y hy => ?_),
    hloc, fun y hy => ?_⟩
  · obtain ⟨e, he, heq, -⟩ := hloc y hy
    exact ⟨e, he, heq⟩
  · obtain ⟨ψ, hψ, hψ0, hψ', h2, -⟩ := s82lc_branch_index hpr y
    exact s82lc_sqrt_chart hpr.1 y hψ hψ0 hψ' (h2 hy)

/-- **Extension over the branch points**: a continuous map `Φ` of `Y ∖ pr⁻¹ P` covering a homeomorphism `k` of `X`
that preserves `P` extends continuously to `Y` (the points over `P` are single and go to the point over the image). -/
theorem s82lc_extend_lift {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1)
    (k : X.carrier ≃ₜ X.carrier) (hk : k '' ↑P = ↑P) (Φ : (pr ⁻¹' (↑P)ᶜ : Set Y.carrier) → Y.carrier)
    (hΦ : Continuous Φ) (hΦk : ∀ y, pr (Φ y) = k (pr y)) :
    ∃ Ψ : Y.carrier → Y.carrier, Continuous Ψ ∧ (∀ y, pr (Ψ y) = k (pr y)) ∧
      ∀ y : (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), Ψ y = Φ y := by
  classical
  have hkP : ∀ x, x ∈ P → k x ∈ P := fun x hx => by
    have : k x ∈ k '' ↑P := mem_image_of_mem _ hx
    rw [hk] at this
    exact this
  set Ψ : Y.carrier → Y.carrier := fun y =>
    if hy : pr y ∈ P then (hpr.2.1 (k (pr y))).choose else Φ ⟨y, hy⟩ with hΨ
  have hΨP : ∀ y (hy : pr y ∈ P), Ψ y = (hpr.2.1 (k (pr y))).choose := fun y hy => by
    rw [hΨ]; exact dite_eq_left_of_eq_true (eq_true hy)
  have hΨc : ∀ y (hy : pr y ∉ P), Ψ y = Φ ⟨y, hy⟩ := fun y hy => by
    rw [hΨ]; exact dite_eq_right_of_eq_false (eq_false hy)
  have hpk : ∀ y, pr (Ψ y) = k (pr y) := by
    intro y
    by_cases hy : pr y ∈ P
    · rw [hΨP y hy]; exact (hpr.2.1 _).choose_spec
    · rw [hΨc y hy]; exact hΦk _
  have hopen : IsOpen (pr ⁻¹' (↑P : Set X.carrier)ᶜ) :=
    P.finite_toSet.isClosed.isOpen_compl.preimage hpr.1.continuous
  refine ⟨Ψ, continuous_iff_continuousAt.2 fun y => ?_, hpk, fun y => hΨc y y.2⟩
  by_cases hy : pr y ∈ P
  · -- at a point over `P`: the fibre over `k (pr y)` is the single point `Ψ y`
    rw [ContinuousAt, (nhds_basis_opens (Ψ y)).tendsto_right_iff]
    rintro U ⟨hU, hUo⟩
    have hfib : pr ⁻¹' {k (pr y)} ⊆ U := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hpr.2.2.2 _ (hkP _ hy))
      have h1 : Ψ y ∈ pr ⁻¹' {k (pr y)} := hpk y
      rw [ha] at h1 ⊢
      rw [← mem_singleton_iff.1 h1]
      simpa using hU
    obtain ⟨N, hN, hNU⟩ := s82lc_preimage_nhds_subset hpr.1.continuous hUo hfib
    have : ∀ᶠ y' in 𝓝 y, k (pr y') ∈ N :=
      (k.continuous.comp hpr.1.continuous).continuousAt.preimage_mem_nhds hN
    filter_upwards [this] with y' hy'
    exact hNU (show pr (Ψ y') ∈ N by rw [hpk]; exact hy')
  · have hemb : Topology.IsOpenEmbedding (Subtype.val : (pr ⁻¹' (↑P : Set X.carrier)ᶜ) → Y.carrier) :=
      hopen.isOpenEmbedding_subtypeVal
    have hcomp : Ψ ∘ Subtype.val = Φ := funext fun y' => hΨc y' y'.2
    exact (hemb.continuousAt_iff (g := Ψ) (x := (⟨y, hy⟩ : (pr ⁻¹' (↑P : Set X.carrier)ᶜ : Set Y.carrier)))).1
      (by rw [hcomp]; exact hΦ.continuousAt)

/-- Lifting a homotopy of maps `Y ∖ pr⁻¹ P → X ∖ P` along the covering `pr` (Mathlib's homotopy lifting). -/
theorem s82lc_lift_homotopy {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hcov : IsCoveringMapOn pr (↑P)ᶜ) (M : C(unitInterval × (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), X.carrier))
    (hM : ∀ t y, M (t, y) ∉ P) (f₀ : C((pr ⁻¹' (↑P)ᶜ : Set Y.carrier), (pr ⁻¹' (↑P)ᶜ : Set Y.carrier)))
    (h0 : ∀ y, M (0, y) = pr (f₀ y)) :
    ∃ M' : C(unitInterval × (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), (pr ⁻¹' (↑P)ᶜ : Set Y.carrier)),
      (∀ t y, pr (M' (t, y)) = M (t, y)) ∧ ∀ y, M' (0, y) = f₀ y := by
  have cov := hcov.isCoveringMap_restrictPreimage
  set Mc : C(unitInterval × (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), ((↑P)ᶜ : Set X.carrier)) :=
    ⟨fun ty => ⟨M ty, hM ty.1 ty.2⟩, M.continuous.subtype_mk _⟩ with hMc
  have h0' : ∀ a, Mc (0, a) = ((↑P : Set X.carrier)ᶜ.restrictPreimage pr) (f₀ a) := fun a =>
    Subtype.ext (h0 a)
  refine ⟨cov.liftHomotopy Mc f₀ h0', fun t y => ?_, cov.liftHomotopy_zero Mc f₀ h0'⟩
  have := congrFun (cov.liftHomotopy_lifts Mc f₀ h0') (t, y)
  exact congrArg Subtype.val this

/-- Uniqueness of path lifting along `pr` over `X ∖ P`. -/
theorem s82lc_path_lift_unique {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hcov : IsCoveringMapOn pr (↑P)ᶜ) {γ₁ γ₂ : unitInterval → (pr ⁻¹' (↑P)ᶜ : Set Y.carrier)}
    (h₁ : Continuous γ₁) (h₂ : Continuous γ₂) (he : ∀ t, pr (γ₁ t) = pr (γ₂ t)) (h0 : γ₁ 0 = γ₂ 0) :
    γ₁ 1 = γ₂ 1 := by
  have cov := hcov.isCoveringMap_restrictPreimage
  have := cov.eq_of_comp_eq h₁ h₂ (funext fun t => Subtype.ext (he t)) 0 h0
  rw [this]

/-- **W4.** -/
theorem s82lc_lift {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1)
    (h : X.carrier ≃ₜ X.carrier) (hP : h '' ↑P = ↑P)
    (K : C(unitInterval × ((↑P)ᶜ : Set X.carrier), X.carrier)) (hK0 : ∀ x, K (0, x) = x)
    (hK1 : ∀ x, K (1, x) = h x) (hKP : ∀ t x, K (t, x) ∉ P) :
    ∃ F : Y.carrier ≃ₜ Y.carrier, (∀ y, pr (F y) = h (pr y)) ∧
      ∃ L : C(unitInterval × (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), Y.carrier),
        (∀ y, L (0, y) = y) ∧ ∀ y, L (1, y) = F y := by
  classical
  have hcov := (s82lc_local_form hpr).1
  set Yc := (pr ⁻¹' (↑P : Set X.carrier)ᶜ : Set Y.carrier) with hYc
  have hsymmP : h.symm '' ↑P = ↑P := by
    calc h.symm '' ↑P = h.symm '' (h '' ↑P) := by rw [hP]
      _ = ↑P := by rw [← Set.image_comp]; simp
  have hinvc : ∀ x : X.carrier, x ∉ P → h.symm x ∉ P := fun x hx hx' => by
    have : h (h.symm x) ∈ h '' ↑P := mem_image_of_mem _ hx'
    rw [hP, h.apply_symm_apply] at this
    exact hx this
  -- the lift `H₁` of `K ∘ (id × pr)` from the identity, and `F° = H₁(1, ·)`
  set M₁ : C(unitInterval × Yc, X.carrier) :=
    ⟨fun ty => K (ty.1, ⟨pr ty.2, ty.2.2⟩), K.continuous.comp (continuous_fst.prodMk
      ((hpr.1.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩ with hM₁
  obtain ⟨H₁, hH₁, hH₁0⟩ := s82lc_lift_homotopy hcov M₁ (fun t y => hKP _ _) (ContinuousMap.id Yc)
    (fun y => hK0 _)
  -- the lift `H₂` of the reversed homotopy `K(1 - t, h⁻¹ ∘ pr)` from the identity, and `G° = H₂(1, ·)`
  set M₂ : C(unitInterval × Yc, X.carrier) :=
    ⟨fun ty => K (unitInterval.symm ty.1, ⟨h.symm (pr ty.2), hinvc _ ty.2.2⟩),
      K.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((h.symm.continuous.comp (hpr.1.continuous.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk
          _))⟩ with hM₂
  obtain ⟨H₂, hH₂, hH₂0⟩ := s82lc_lift_homotopy hcov M₂ (fun t y => hKP _ _) (ContinuousMap.id Yc)
    (fun y => by
      show K (unitInterval.symm 0, _) = pr y
      rw [unitInterval.symm_zero, hK1, h.apply_symm_apply])
  set F₀ : Yc → Yc := fun y => H₁ (1, y) with hF₀
  set G₀ : Yc → Yc := fun y => H₂ (1, y) with hG₀
  have hF₀c : Continuous F₀ := H₁.continuous.comp (continuous_const.prodMk continuous_id)
  have hG₀c : Continuous G₀ := H₂.continuous.comp (continuous_const.prodMk continuous_id)
  have hF₀p : ∀ y, pr (F₀ y) = h (pr y) := fun y => by
    show pr (H₁ (1, y)) = _
    rw [hH₁]
    exact hK1 _
  have hG₀p : ∀ y, pr (G₀ y) = h.symm (pr y) := fun y => by
    show pr (H₂ (1, y)) = _
    rw [hH₂]
    show K (unitInterval.symm 1, _) = _
    rw [unitInterval.symm_one, hK0]
  -- `G° ∘ F° = id` and `F° ∘ G° = id` by uniqueness of path lifting
  have hGF : ∀ y, G₀ (F₀ y) = y := by
    intro y
    have := s82lc_path_lift_unique hcov (γ₁ := fun t => H₂ (t, F₀ y)) (γ₂ := fun t => H₁ (unitInterval.symm t, y))
      (H₂.continuous.comp (continuous_id.prodMk continuous_const))
      (H₁.continuous.comp (unitInterval.continuous_symm.prodMk continuous_const))
      (fun t => by
        rw [hH₂, hH₁]
        exact congrArg (fun x : ((↑P : Set X.carrier)ᶜ : Set X.carrier) => K (unitInterval.symm t, x))
          (Subtype.ext (show h.symm (pr (F₀ y)) = pr y by rw [hF₀p, h.symm_apply_apply])))
      (by
        show H₂ (0, F₀ y) = H₁ (unitInterval.symm 0, y)
        rw [hH₂0, unitInterval.symm_zero]
        rfl)
    simp only [unitInterval.symm_one] at this
    rw [hH₁0] at this
    exact this
  have hFG : ∀ w, F₀ (G₀ w) = w := by
    intro w
    have := s82lc_path_lift_unique hcov (γ₁ := fun t => H₁ (t, G₀ w)) (γ₂ := fun t => H₂ (unitInterval.symm t, w))
      (H₁.continuous.comp (continuous_id.prodMk continuous_const))
      (H₂.continuous.comp (unitInterval.continuous_symm.prodMk continuous_const))
      (fun t => by
        rw [hH₁, hH₂]
        show K (t, _) = K (unitInterval.symm (unitInterval.symm t), _)
        rw [unitInterval.symm_symm]
        exact congrArg (fun x : ((↑P : Set X.carrier)ᶜ : Set X.carrier) => K (t, x))
          (Subtype.ext (show pr (G₀ w) = h.symm (pr w) from hG₀p w)))
      (by
        show H₁ (0, G₀ w) = H₂ (unitInterval.symm 0, w)
        rw [hH₁0, unitInterval.symm_zero]
        rfl)
    simp only [unitInterval.symm_one] at this
    rw [hH₂0] at this
    exact this
  -- extend over the branch points
  obtain ⟨F, hFc, hFp, hFe⟩ := s82lc_extend_lift hpr h hP (fun y => (F₀ y : Y.carrier))
    (continuous_subtype_val.comp hF₀c) hF₀p
  obtain ⟨G, hGc, hGp, hGe⟩ := s82lc_extend_lift hpr h.symm hsymmP (fun y => (G₀ y : Y.carrier))
    (continuous_subtype_val.comp hG₀c) hG₀p
  -- two points of the same fibre over `P` coincide
  have hsingle : ∀ a b : Y.carrier, pr a = pr b → pr a ∈ P → a = b := by
    intro a b hab ha
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hpr.2.2.2 _ ha)
    have h1 : a ∈ pr ⁻¹' {pr a} := rfl
    have h2 : b ∈ pr ⁻¹' {pr a} := hab.symm
    rw [hc] at h1 h2
    rw [mem_singleton_iff.1 h1, mem_singleton_iff.1 h2]
  have hGF' : ∀ y, G (F y) = y := by
    intro y
    by_cases hy : pr y ∈ P
    · refine hsingle _ _ ?_ ?_
      · rw [hGp, hFp, h.symm_apply_apply]
      · rw [hGp, hFp, h.symm_apply_apply]; exact hy
    · have h1 : F y = F₀ ⟨y, hy⟩ := hFe ⟨y, hy⟩
      have hF₀mem : (F₀ ⟨y, hy⟩ : Y.carrier) ∈ Yc := (F₀ ⟨y, hy⟩).2
      rw [h1, show G (F₀ ⟨y, hy⟩ : Y.carrier) = G₀ (F₀ ⟨y, hy⟩) from hGe (F₀ ⟨y, hy⟩), hGF]
  have hFG' : ∀ w, F (G w) = w := by
    intro w
    by_cases hw : pr w ∈ P
    · refine hsingle _ _ ?_ ?_
      · rw [hFp, hGp, h.apply_symm_apply]
      · rw [hFp, hGp, h.apply_symm_apply]; exact hw
    · have h1 : G w = G₀ ⟨w, hw⟩ := hGe ⟨w, hw⟩
      rw [h1, show F (G₀ ⟨w, hw⟩ : Y.carrier) = F₀ (G₀ ⟨w, hw⟩) from hFe (G₀ ⟨w, hw⟩), hFG]
  refine ⟨⟨⟨F, G, hGF', hFG'⟩, hFc, hGc⟩, hFp, ⟨fun ty => (H₁ ty : Y.carrier),
    continuous_subtype_val.comp H₁.continuous⟩, fun y => ?_, fun y => ?_⟩
  · show (H₁ (0, y) : Y.carrier) = y
    rw [hH₁0]; rfl
  · show (H₁ (1, y) : Y.carrier) = F y
    rw [hFe y]

/-- A continuous injective map on an open subset of `ℂ` is an open partial homeomorphism (invariance of domain). -/
theorem s82lc_openPartialHomeomorph_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn f U)
    (hi : InjOn f U) : ∃ L : OpenPartialHomeomorph ℂ ℂ, L.source = U ∧ (L : ℂ → ℂ) = f ∧ L.target = f '' U := by
  set e := hi.toPartialEquiv f U with he
  have ho : IsOpenMap (e.source.domRestrict e) := by
    intro V hV
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hV
    have himg : e.source.domRestrict e '' (Subtype.val ⁻¹' W) = f '' (U ∩ W) := by
      ext z
      constructor
      · rintro ⟨⟨x, hx⟩, hxW, rfl⟩
        exact ⟨x, ⟨hx, hxW⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxW⟩, rfl⟩
        exact ⟨⟨x, hx⟩, hxW, rfl⟩
    rw [himg]
    exact LiZhongExternal.Topology.invariance_of_domain_finiteDimensional f (U ∩ W) (hU.inter hW)
      (hc.mono inter_subset_left) (hi.mono inter_subset_left)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e hc ho hU, rfl, rfl, rfl⟩

/-- There is no continuous square root of `z` on a circle around `0`. -/
theorem s82lc_no_sqrt_on_circle {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ} (hκ : ContinuousOn κ (sphere 0 r))
    (hsq : ∀ x ∈ sphere (0 : ℂ) r, κ x ^ 2 = x) : False := by
  set γ : ℝ → ℂ := fun θ => r * Complex.exp (θ * I) with hγ
  have hγs : ∀ θ, γ θ ∈ sphere (0 : ℂ) r := fun θ => by
    simp [hγ, norm_exp_ofReal_mul_I, abs_of_pos hr]
  have hγc : Continuous γ := by fun_prop
  set g : ℝ → ℂ := fun θ => κ (γ θ) with hg
  set h : ℝ → ℂ := fun θ => (Real.sqrt r : ℂ) * Complex.exp (θ / 2 * I) with hh
  have hgc : ContinuousOn g (Icc 0 (2 * π)) :=
    hκ.comp_continuous hγc hγs |>.continuousOn
  have hhc : ContinuousOn h (Icc 0 (2 * π)) := by
    apply Continuous.continuousOn
    fun_prop
  have hsq' : EqOn (g ^ 2) (h ^ 2) (Icc 0 (2 * π)) := by
    intro θ _
    simp only [Pi.pow_apply, hg, hh]
    rw [hsq _ (hγs θ), mul_pow, ← Complex.exp_nat_mul, ← ofReal_pow, Real.sq_sqrt hr.le]
    simp only [hγ]
    congr 2
    push_cast
    ring
  have hne : ∀ {θ : ℝ}, θ ∈ Icc 0 (2 * π) → h θ ≠ 0 := fun _ => by
    simp only [hh]
    exact mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hr).ne') (Complex.exp_ne_zero _)
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_refl _, by positivity⟩
  have h2 : (2 * π) ∈ Icc (0 : ℝ) (2 * π) := ⟨by positivity, le_refl _⟩
  have hg02 : g 0 = g (2 * π) := by
    simp only [hg, hγ]
    congr 1
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I]
    simp
  have hh2 : h (2 * π) = - h 0 := by
    simp only [hh]
    rw [show ((2 * π : ℝ) : ℂ) / 2 * I = π * I by push_cast; ring, Complex.exp_pi_mul_I]
    simp
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hr).ne'
  have hh0 : h 0 = Real.sqrt r := by simp [hh]
  rcases isPreconnected_Icc.eq_or_eq_neg_of_sq_eq hgc hhc hsq' hne with H | H
  · have e1 := H h0
    have e2 := H h2
    rw [← hg02, e1, hh2, hh0] at e2
    exact hs (by linear_combination e2 / 2)
  · have e1 := H h0
    have e2 := H h2
    simp only [Pi.neg_apply] at e1 e2
    rw [← hg02, e1, hh2, hh0] at e2
    exact hs (by linear_combination -e2 / 2)

/-- **Exp-lift on a half-plane.**  If `φ` is continuous and nonvanishing on the punctured disc `B(0, R) ∖ {0}`, then
`s ↦ φ(eˢ)` has a continuous logarithm `Λ` on the half-plane `Re s < log R`, and `Λ(s + 2πim) = Λ(s) + 2πimn` for a
fixed integer `n` (the winding number of `φ`). -/
theorem s82lc_exp_lift {φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hφc : ContinuousOn φ (ball 0 R \ {0}))
    (hφ0 : ∀ z ∈ ball (0 : ℂ) R \ {0}, φ z ≠ 0) :
    ∃ Λ : ℂ → ℂ, ContinuousOn Λ {s : ℂ | s.re < Real.log R} ∧
      (∀ s : ℂ, s.re < Real.log R → Complex.exp (Λ s) = φ (Complex.exp s)) ∧
      ∃ n : ℤ, ∀ s : ℂ, s.re < Real.log R → ∀ m : ℤ,
        Λ (s + m * (2 * π * I)) = Λ s + m * n * (2 * π * I) := by
  classical
  set S : Set ℂ := {s : ℂ | s.re < Real.log R} with hS
  have hSo : IsOpen S := isOpen_lt Complex.continuous_re continuous_const
  have hSc : Convex ℝ S := convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear _
  have hexpS : ∀ s ∈ S, Complex.exp s ∈ ball (0 : ℂ) R \ {0} := fun s hs => by
    refine ⟨?_, Complex.exp_ne_zero s⟩
    rw [mem_ball_zero_iff, Complex.norm_exp]
    calc Real.exp s.re < Real.exp (Real.log R) := Real.exp_lt_exp.2 hs
      _ = R := Real.exp_log hR
  have hsh : ∀ s ∈ S, ∀ m : ℤ, s + m * (2 * π * I) ∈ S := fun s hs m => by
    have hs' : s.re < Real.log R := hs
    show (s + m * (2 * π * I)).re < Real.log R
    simpa using hs'
  set s₀ : ℂ := ((Real.log R - 1 : ℝ) : ℂ) with hs₀
  have hs₀S : s₀ ∈ S := by
    show (((Real.log R - 1 : ℝ) : ℂ)).re < Real.log R
    simp
  -- the homotopy `t ↦ φ (exp (s₀ + t (s - s₀)))` from a constant, lifted along `exp`
  have hseg : ∀ (t : unitInterval) (s : S), s₀ + (t : ℂ) * ((s : ℂ) - s₀) ∈ S := by
    intro t s
    have := hSc hs₀S s.2 (sub_nonneg.2 t.2.2) t.2.1 (by ring)
    convert this using 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  set H : C(unitInterval × S, {z : ℂ // z ≠ 0}) :=
    ⟨fun ts => ⟨φ (Complex.exp (s₀ + (ts.1 : ℂ) * ((ts.2 : ℂ) - s₀))), hφ0 _ (hexpS _ (hseg ts.1 ts.2))⟩, by
      refine Continuous.subtype_mk ?_ _
      refine hφc.comp_continuous ?_ fun ts => hexpS _ (hseg ts.1 ts.2)
      fun_prop⟩ with hH
  set L₀ : ℂ := Complex.log (φ (Complex.exp s₀)) with hL₀
  have hφs₀ : φ (Complex.exp s₀) ≠ 0 := hφ0 _ (hexpS _ hs₀S)
  have h0 : ∀ s, H (0, s) = (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}))
      ((ContinuousMap.const S L₀) s) := fun s => by
    apply Subtype.ext
    show φ (Complex.exp (s₀ + ((0 : unitInterval) : ℂ) * ((s : ℂ) - s₀))) = Complex.exp L₀
    rw [hL₀, Complex.exp_log hφs₀]
    simp
  have cov := Complex.isCoveringMap_exp
  set Λ' := cov.liftHomotopy H (ContinuousMap.const S L₀) h0 with hΛ'
  have hlift : ∀ s : S, Complex.exp (Λ' (1, s)) = φ (Complex.exp s) := fun s => by
    have := congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H (ContinuousMap.const S L₀) h0) (1, s))
    simp only [Function.comp_apply] at this
    rw [this]
    show φ (Complex.exp (s₀ + ((1 : unitInterval) : ℂ) * ((s : ℂ) - s₀))) = _
    congr 2
    simp
  set Λ : ℂ → ℂ := fun s => if hs : s ∈ S then Λ' (1, ⟨s, hs⟩) else 0 with hΛ
  have hΛS : ∀ s (hs : s ∈ S), Λ s = Λ' (1, ⟨s, hs⟩) := fun s hs => by
    rw [hΛ]; exact dite_eq_left_of_eq_true (eq_true hs)
  have hΛc : ContinuousOn Λ S := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (Λ'.continuous.comp ((continuous_const (y := (1 : unitInterval))).prodMk continuous_id)).congr fun s => ?_
    exact (hΛS s s.2).symm
  have hΛe : ∀ s ∈ S, Complex.exp (Λ s) = φ (Complex.exp s) := fun s hs => by
    rw [hΛS s hs]; exact hlift ⟨s, hs⟩
  refine ⟨Λ, hΛc, hΛe, ?_⟩
  -- periodicity: `Λ ∘ (· + 2πi)` and `Λ + 2πin` are lifts of the same map agreeing at `s₀`
  have hper0 : Complex.exp (Λ (s₀ + 2 * π * I)) = Complex.exp (Λ s₀) := by
    rw [hΛe _ (by simpa using hsh s₀ hs₀S 1), hΛe _ hs₀S, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hper0
  have : PreconnectedSpace S := Subtype.preconnectedSpace hSc.isPreconnected
  have hper : ∀ s ∈ S, Λ (s + 2 * π * I) = Λ s + n * (2 * π * I) := by
    set g₁ : S → ℂ := fun s => Λ (s + 2 * π * I) with hg₁
    set g₂ : S → ℂ := fun s => Λ s + n * (2 * π * I) with hg₂
    have hS1 : ∀ s : S, (s : ℂ) + 2 * π * I ∈ S := fun s => by simpa using hsh s s.2 1
    have hg₁c : Continuous g₁ := by
      have := hΛc.comp_continuous (f := fun s : S => (s : ℂ) + 2 * π * I) (by fun_prop) hS1
      exact this
    have hg₂c : Continuous g₂ := by
      exact (hΛc.comp_continuous continuous_subtype_val fun s => s.2).add
        (continuous_const (y := (n : ℂ) * (2 * π * I)))
    have hcomp : (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ g₁ =
        (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ g₂ := by
      funext s
      apply Subtype.ext
      show Complex.exp (Λ (s + 2 * π * I)) = Complex.exp (Λ s + n * (2 * π * I))
      rw [hΛe _ (hS1 s), Complex.exp_add (Λ s), hΛe _ s.2, Complex.exp_add (s : ℂ), Complex.exp_two_pi_mul_I,
        mul_one, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have heq := cov.eq_of_comp_eq hg₁c hg₂c hcomp ⟨s₀, hs₀S⟩ hn
    intro s hs
    exact congrFun heq ⟨s, hs⟩
  refine ⟨n, fun s hs m => ?_⟩
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have e : s + (((m : ℤ) + 1 : ℤ) : ℂ) * (2 * π * I) = (s + ((m : ℤ) : ℂ) * (2 * π * I)) + 2 * π * I := by
      push_cast; ring
    rw [e, hper _ (hsh s hs m), ih]
    push_cast
    ring
  | pred m ih =>
    have e : s + ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * I) = (s + ((-(m : ℤ) - 1 : ℤ) : ℂ) * (2 * π * I)) + 2 * π * I := by
      push_cast; ring
    have h1 := hper _ (hsh s hs (-(m : ℤ) - 1))
    rw [← e, ih] at h1
    rw [show Λ (s + ((-(m : ℤ) - 1 : ℤ) : ℂ) * (2 * π * I)) =
      Λ s + ((-(m : ℤ) : ℤ) : ℂ) * n * (2 * π * I) - n * (2 * π * I) from by rw [h1]; ring]
    push_cast
    ring

/-- A local continuous branch of `log` near `w₀ ≠ 0`. -/
theorem s82lc_local_log {w₀ : ℂ} (hw₀ : w₀ ≠ 0) :
    ContinuousAt (fun z => Complex.log (z / w₀) + Complex.log w₀) w₀ ∧
      ∀ z, z ≠ 0 → Complex.exp (Complex.log (z / w₀) + Complex.log w₀) = z ∧
        (Complex.log (z / w₀) + Complex.log w₀).re = Real.log ‖z‖ := by
  refine ⟨?_, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : (fun z : ℂ => z / w₀) w₀ ∈ slitPlane := by
      simp only [div_self hw₀]; exact one_mem_slitPlane
    exact ((continuousAt_id.div_const w₀).clog h1).add continuousAt_const
  · rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz hw₀), Complex.exp_log hw₀, div_mul_cancel₀ _ hw₀]
  · rw [Complex.add_re, Complex.log_re, Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz) (norm_ne_zero_iff.2 hw₀)]
    ring

/-- **Topological square root.**  For a continuous injective `φ` near `0` with `φ(0) = 0` there is a continuous
injective `σ` near `0` with `σ(w)² = φ(w²)` and `σ(0) = 0`. -/
theorem s82lc_topological_sqrt {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (h0D : (0 : ℂ) ∈ D)
    (hφc : ContinuousOn φ D) (hφi : InjOn φ D) (hφ0 : φ 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ σ : ℂ → ℂ, (∀ w ∈ ball (0 : ℂ) ρ, w ^ 2 ∈ D ∧ σ w ^ 2 = φ (w ^ 2)) ∧
      ContinuousOn σ (ball 0 ρ) ∧ InjOn σ (ball 0 ρ) ∧ σ 0 = 0 := by
  classical
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.1 hD 0 h0D
  have hφ0' : ∀ z ∈ ball (0 : ℂ) R \ {0}, φ z ≠ 0 := fun z hz h => by
    have := hφi (hRD hz.1) h0D (h.trans hφ0.symm)
    exact hz.2 this
  obtain ⟨Λ, hΛc, hΛe, n, hΛp⟩ := s82lc_exp_lift hR (hφc.mono fun z hz => hRD hz.1) hφ0'
  set S : Set ℂ := {s : ℂ | s.re < Real.log R} with hS
  have hSo : IsOpen S := isOpen_lt Complex.continuous_re continuous_const
  set ρ := Real.sqrt R with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hR
  have hball : ∀ w ∈ ball (0 : ℂ) ρ, w ^ 2 ∈ ball (0 : ℂ) R := fun w hw => by
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_pow]
    calc ‖w‖ ^ 2 < ρ ^ 2 := by gcongr
      _ = R := Real.sq_sqrt hR.le
  -- the doubled logarithm of a point of the punctured disc lies in the half-plane
  have hlogS : ∀ ζ : ℂ, Complex.exp ζ ∈ ball (0 : ℂ) ρ → 2 * ζ ∈ S := fun ζ hζ => by
    have h1 : ‖Complex.exp ζ‖ ^ 2 < R := by
      have := hball _ hζ
      rwa [mem_ball_zero_iff, norm_pow] at this
    show (2 * ζ).re < Real.log R
    have h2 : (2 * ζ).re = Real.log (‖Complex.exp ζ‖ ^ 2) := by
      rw [Complex.norm_exp, ← Real.exp_nat_mul, Real.log_exp]
      simp
    rw [h2]
    exact Real.log_lt_log (pow_pos (norm_pos_iff.2 (Complex.exp_ne_zero ζ)) 2) h1
  set σ : ℂ → ℂ := fun w => if w = 0 then 0 else Complex.exp (Λ (2 * Complex.log w) / 2) with hσ
  -- the key formula: `σ(e^ζ) = exp(Λ(2ζ)/2)` for every logarithm `ζ`
  have hKF : ∀ ζ : ℂ, Complex.exp ζ ∈ ball (0 : ℂ) ρ → σ (Complex.exp ζ) = Complex.exp (Λ (2 * ζ) / 2) := by
    intro ζ hζ
    have hne := Complex.exp_ne_zero ζ
    have h1 : σ (Complex.exp ζ) = Complex.exp (Λ (2 * Complex.log (Complex.exp ζ)) / 2) := by
      rw [hσ]; simp [hne]
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (Complex.exp_log hne)
    have h2 : 2 * Complex.log (Complex.exp ζ) = 2 * ζ + ((2 * m : ℤ) : ℂ) * (2 * π * I) := by
      rw [hm]; push_cast; ring
    rw [h1, h2, hΛp _ (hlogS ζ hζ)]
    rw [show (Λ (2 * ζ) + ((2 * m : ℤ) : ℂ) * n * (2 * π * I)) / 2 =
      Λ (2 * ζ) / 2 + ((m * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hσsq : ∀ w ∈ ball (0 : ℂ) ρ, σ w ^ 2 = φ (w ^ 2) := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]; simp [hσ, hφ0]
    · have := hKF (Complex.log w) (by rwa [Complex.exp_log hw0])
      rw [Complex.exp_log hw0] at this
      rw [this, ← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (Λ (2 * Complex.log w) / 2) = Λ (2 * Complex.log w)
        by push_cast; ring, hΛe _ (hlogS _ (by rwa [Complex.exp_log hw0])), show 2 * Complex.log w =
        (2 : ℕ) * Complex.log w by norm_num, Complex.exp_nat_mul, Complex.exp_log hw0]
  -- `σ(-w) = (-1)ⁿ σ(w)`
  have hσneg : ∀ w ∈ ball (0 : ℂ) ρ, w ≠ 0 → σ (-w) = (-1) ^ n * σ w := by
    intro w hw hw0
    have hw' : Complex.exp (Complex.log w) ∈ ball (0 : ℂ) ρ := by rwa [Complex.exp_log hw0]
    have e1 : -w = Complex.exp (Complex.log w + π * I) := by
      rw [Complex.exp_add, Complex.exp_log hw0, Complex.exp_pi_mul_I]; ring
    have hmem : Complex.exp (Complex.log w + π * I) ∈ ball (0 : ℂ) ρ := by
      rw [← e1, mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.1 hw
    rw [e1, hKF _ hmem, show 2 * (Complex.log w + π * I) = 2 * Complex.log w + ((1 : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring, hΛp _ (hlogS _ hw'), ← Complex.exp_log hw0, hKF _ hw', Complex.exp_log hw0]
    rw [show (Λ (2 * Complex.log w) + ((1 : ℤ) : ℂ) * n * (2 * π * I)) / 2 =
      (n : ℂ) * (π * I) + Λ (2 * Complex.log w) / 2 by push_cast; ring, Complex.exp_add,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
  -- continuity
  have hσc : ContinuousOn σ (ball 0 ρ) := by
    intro w hw
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hw0 : w = 0
    · subst hw0
      have hσ0 : σ 0 = 0 := by simp [hσ]
      rw [ContinuousAt, hσ0, tendsto_zero_iff_norm_tendsto_zero]
      have hφt : Tendsto (fun z : ℂ => φ (z ^ 2)) (𝓝 0) (𝓝 0) := by
        have h1 : Tendsto (fun z : ℂ => z ^ 2) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_pow 2).tendsto (0 : ℂ)
        have h2 := (hφc.continuousAt (hD.mem_nhds h0D)).tendsto
        rw [hφ0] at h2
        exact h2.comp h1
      have h3 : Tendsto (fun z : ℂ => Real.sqrt ‖φ (z ^ 2)‖) (𝓝 0) (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_norm_zero.comp hφt)
        rw [Real.sqrt_zero] at this
        exact this
      refine h3.congr' ?_
      filter_upwards [ball_mem_nhds (0 : ℂ) hρ0] with z hz
      show Real.sqrt ‖φ (z ^ 2)‖ = ‖σ z‖
      rw [← hσsq z hz, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    · obtain ⟨hℓc, hℓ⟩ := s82lc_local_log hw0
      set ℓ : ℂ → ℂ := fun z => Complex.log (z / w) + Complex.log w with hℓdef
      have hev : ∀ᶠ z in 𝓝 w, σ z = Complex.exp (Λ (2 * ℓ z) / 2) := by
        filter_upwards [ball_mem_nhds w (norm_pos_iff.2 hw0), isOpen_ball.mem_nhds hw] with z hz hzb
        have hz0 : z ≠ 0 := by
          intro h; rw [h, mem_ball, dist_zero_left] at hz; exact lt_irrefl _ hz
        have := hKF (ℓ z) (by rw [(hℓ z hz0).1]; exact hzb)
        rwa [(hℓ z hz0).1] at this
      refine ContinuousAt.congr ?_ (Filter.EventuallyEq.symm hev)
      have h2S : 2 * ℓ w ∈ S := by
        apply hlogS
        rw [(hℓ w hw0).1]; exact hw
      have hΛw : ContinuousAt Λ (2 * ℓ w) := hΛc.continuousAt (hSo.mem_nhds h2S)
      exact Complex.continuous_exp.continuousAt.comp
        ((hΛw.comp (f := fun z => 2 * ℓ z) (continuousAt_const.mul hℓc)).div_const 2)
  have hσ0 : σ 0 = 0 := by simp [hσ]
  have hσne : ∀ w ∈ ball (0 : ℂ) ρ, w ≠ 0 → σ w ≠ 0 := fun w hw hw0 h => by
    have := hσsq w hw
    rw [h, zero_pow two_ne_zero] at this
    exact hφ0' _ ⟨hball w hw, pow_ne_zero 2 hw0⟩ this.symm
  -- injectivity; the case `σ(-w) = σ(w)` contradicts the absence of a continuous square root on a circle
  have hodd : (-1 : ℂ) ^ n ≠ 1 := by
    intro heven
    have hσeven : ∀ w ∈ ball (0 : ℂ) ρ, σ (-w) = σ w := fun w hw => by
      by_cases hw0 : w = 0
      · rw [hw0, neg_zero]
      · rw [hσneg w hw hw0, heven, one_mul]
    obtain ⟨L, hLs, hLc, hLt⟩ := s82lc_openPartialHomeomorph_of_injOn (U := ball (0 : ℂ) R) isOpen_ball
      (hφc.mono hRD) (hφi.mono hRD)
    have h0t : (0 : ℂ) ∈ L.target := by
      rw [hLt]; exact ⟨0, mem_ball_self hR, hφ0⟩
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 L.open_target 0 h0t
    set r := ε / 2 with hr
    have hr0 : 0 < r := by positivity
    have hsph : sphere (0 : ℂ) r ⊆ L.target := fun x hx => hεt (by
      rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hx; rw [hx]; linarith)
    have hLsymm : ∀ x ∈ L.target, L.symm x ∈ ball (0 : ℂ) R := fun x hx => by
      rw [← hLs]; exact L.map_target hx
    have hLφ : ∀ x ∈ L.target, φ (L.symm x) = x := fun x hx => by
      rw [← hLc]; exact L.right_inv hx
    have hsqrt_ball : ∀ t ∈ ball (0 : ℂ) R, ∀ w : ℂ, w ^ 2 = t → w ∈ ball (0 : ℂ) ρ := fun t ht w hw => by
      rw [mem_ball_zero_iff] at ht ⊢
      have h1 : ‖w‖ ^ 2 < ρ ^ 2 := by
        rw [Real.sq_sqrt hR.le, ← norm_pow, hw]; exact ht
      exact lt_of_pow_lt_pow_left₀ 2 hρ0.le h1
    set κ : ℂ → ℂ := fun x => σ (L.symm x ^ ((2 : ℂ)⁻¹)) with hκ
    have hsq2 : ∀ t : ℂ, (t ^ ((2 : ℂ)⁻¹)) ^ 2 = t := fun t => by
      simp
    have hκsq : ∀ x ∈ sphere (0 : ℂ) r, κ x ^ 2 = x := fun x hx => by
      have ht := hLsymm x (hsph hx)
      rw [hκ, hσsq _ (hsqrt_ball _ ht _ (hsq2 _)), hsq2, hLφ x (hsph hx)]
    -- `κ` is continuous on the circle: locally it is `σ` of a continuous square root, since `σ` is even
    have hκc : ContinuousOn κ (sphere 0 r) := by
      intro x₀ hx₀
      have hx₀t := hsph hx₀
      set t₀ := L.symm x₀
      have ht₀ : t₀ ≠ 0 := by
        intro h
        have := hLφ x₀ hx₀t
        rw [show L.symm x₀ = t₀ from rfl, h, hφ0] at this
        rw [← this, mem_sphere_zero_iff_norm, norm_zero] at hx₀
        exact hr0.ne hx₀
      set w₀ := t₀ ^ ((2 : ℂ)⁻¹)
      set sq : ℂ → ℂ := fun x => w₀ * (L.symm x / t₀) ^ ((2 : ℂ)⁻¹) with hsqd
      have hsqc : ContinuousAt sq x₀ := by
        have h1 : (fun x => L.symm x / t₀) x₀ ∈ slitPlane := by
          rw [show (fun x => L.symm x / t₀) x₀ = 1 from div_self ht₀]; exact one_mem_slitPlane
        exact continuousAt_const.mul (((L.continuousAt_symm hx₀t).div_const t₀).cpow continuousAt_const h1)
      have hsqsq : ∀ x, sq x ^ 2 = L.symm x := fun x => by
        rw [hsqd, mul_pow, hsq2, hsq2, mul_div_cancel₀ _ ht₀]
      have hsq0 : sq x₀ = w₀ := by
        show w₀ * (L.symm x₀ / t₀) ^ ((2 : ℂ)⁻¹) = w₀
        rw [show L.symm x₀ / t₀ = 1 from div_self ht₀, Complex.one_cpow, mul_one]
      have hw₀b : w₀ ∈ ball (0 : ℂ) ρ := hsqrt_ball _ (hLsymm x₀ hx₀t) _ (hsq2 _)
      have hev : ∀ᶠ x in 𝓝 x₀, κ x = σ (sq x) := by
        filter_upwards [L.open_target.mem_nhds hx₀t] with x hx
        have ht := hLsymm x hx
        have h1 : (L.symm x ^ ((2 : ℂ)⁻¹)) ^ 2 = sq x ^ 2 := by rw [hsq2, hsqsq]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
        · rw [hκ]; simp only; rw [h]
        · rw [hκ]; simp only; rw [h, hσeven _ (hsqrt_ball _ ht _ (hsqsq x))]
      refine (ContinuousAt.congr ?_ (Filter.EventuallyEq.symm hev)).continuousWithinAt
      have : ContinuousAt σ (sq x₀) := by
        rw [hsq0]; exact hσc.continuousAt (isOpen_ball.mem_nhds hw₀b)
      exact this.comp hsqc
    exact s82lc_no_sqrt_on_circle hr0 hκc hκsq
  have hσi : InjOn σ (ball 0 ρ) := by
    intro w₁ hw₁ w₂ hw₂ h
    have h1 : φ (w₁ ^ 2) = φ (w₂ ^ 2) := by rw [← hσsq w₁ hw₁, ← hσsq w₂ hw₂, h]
    have h2 : w₁ ^ 2 = w₂ ^ 2 := hφi (hRD (hball w₁ hw₁)) (hRD (hball w₂ hw₂)) h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · exact h3
    · by_cases hw0 : w₂ = 0
      · rw [h3, hw0, neg_zero]
      · exfalso
        rw [h3, hσneg w₂ hw₂ hw0] at h
        have h4 : ((-1 : ℂ) ^ n - 1) * σ w₂ = 0 := by rw [sub_mul, one_mul, h, sub_self]
        rcases mul_eq_zero.1 h4 with h5 | h5
        · exact hodd (sub_eq_zero.1 h5)
        · exact hσne w₂ hw₂ hw0 h5
  exact ⟨ρ, hρ0, σ, fun w hw => ⟨hRD (hball w hw), hσsq w hw⟩, hσc, hσi, hσ0⟩

/-- A continuous square root of a nonvanishing analytic function is analytic. -/
theorem s82lc_analyticAt_of_sq {T A : ℂ → ℂ} {w₀ : ℂ} {O : Set ℂ} (hO : O ∈ 𝓝 w₀) (hT : ContinuousOn T O)
    (hA : AnalyticAt ℂ A w₀) (hA0 : A w₀ ≠ 0) (heq : ∀ᶠ w in 𝓝 w₀, T w ^ 2 = A w) : AnalyticAt ℂ T w₀ := by
  obtain ⟨r, hr, hr0, hrsq, -⟩ := exists_analyticAt_sq_eq hA hA0
  have hev : ∀ᶠ w in 𝓝 w₀, (w ∈ O ∧ T w ^ 2 = A w) ∧ (r w ≠ 0 ∧ AnalyticAt ℂ r w) :=
    ((Filter.eventually_mem_set.2 hO).and heq).and
      ((hr.continuousAt.eventually_ne hr0).and hr.eventually_analyticAt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hTc : ContinuousOn T (ball w₀ ε) := hT.mono fun w hw => (hball w hw).1.1
  have hrc : ContinuousOn r (ball w₀ ε) := fun w hw => (hball w hw).2.2.continuousAt.continuousWithinAt
  have hsq : EqOn (T ^ 2) (r ^ 2) (ball w₀ ε) := fun w hw => by
    simp only [Pi.pow_apply]
    rw [(hball w hw).1.2, hrsq]
  rcases (convex_ball w₀ ε).isPreconnected.eq_or_eq_neg_of_sq_eq hTc hrc hsq
    (fun hw => (hball _ hw).2.1) with h | h
  · exact hr.congr (Filter.eventually_of_mem (ball_mem_nhds w₀ hε) fun w hw => (h hw).symm)
  · exact hr.neg.congr (Filter.eventually_of_mem (ball_mem_nhds w₀ hε) fun w hw => (h hw).symm)

/-- **Transported charts.**  At every point `t` of the cover there is a chart `c` of `Y` (holomorphic or a square
root chart) and a chart `κ` of `X₁` with `c^m = κ ∘ fb ∘ pr₀` on the source of `c` (`m = 1` off the branch points,
`m = 2` at a branch point, which is then the only point of the source over `P₀` and the only zero of `c`). -/
theorem s82lc_transport_chart {Y X₀ X₁ : ClosedRS.{u}} {P₀ : Finset X₀.carrier} {pr₀ : Y.carrier → X₀.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ P₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P₀, (pr₀ ⁻¹' {x}).ncard = 1)
    (fb : X₀.carrier ≃ₜ X₁.carrier) (t : Y.carrier) :
    ∃ (c : OpenPartialHomeomorph Y.carrier ℂ) (κ : OpenPartialHomeomorph X₁.carrier ℂ) (m : ℕ),
      t ∈ c.source ∧ κ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X₁.carrier ∧ (m = 1 ∨ m = 2) ∧
      (∀ y ∈ c.source, fb (pr₀ y) ∈ κ.source ∧ c y ^ m = κ (fb (pr₀ y))) ∧
      (∀ y ∈ c.source, pr₀ y ∈ P₀ → y = t ∧ m = 2) ∧ (m = 2 → ∀ y ∈ c.source, c y = 0 → y = t) ∧
      (m = 2 → pr₀ t ∈ P₀) := by
  classical
  obtain ⟨-, hreg, hbr⟩ := s82lc_local_form hpr₀
  have hPo : IsOpen (pr₀ ⁻¹' (↑P₀ : Set X₀.carrier)ᶜ) :=
    P₀.finite_toSet.isClosed.isOpen_compl.preimage hpr₀.1.continuous
  by_cases ht : pr₀ t ∈ P₀
  · -- a branch point
    obtain ⟨u, v, r, hu, hv, htu, hut, hr, hutg, husrc, huv⟩ := hbr t ht
    set p := pr₀ t
    set κ₀ := chartAt ℂ (fb p) with hκ₀
    set τ : OpenPartialHomeomorph ℂ ℂ := (Homeomorph.addRight (-(κ₀ (fb p)))).toOpenPartialHomeomorph with hτ
    set κ := κ₀.trans τ with hκ
    have hκm : κ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X₁.carrier := by
      refine IsManifold.mem_maximalAtlas_iff_contMDiffOn _ |>.2 ⟨?_, ?_⟩
      · have h1 := contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω)
          (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (fb p))
        have h2 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω τ τ.source := contMDiffOn_iff_contDiffOn.2 (by
          show ContDiffOn ℂ ω (fun z => z + -(κ₀ (fb p))) _
          exact (contDiff_id.add contDiff_const).contDiffOn)
        exact h2.comp (h1.mono fun z hz => hz.1) fun z hz => hz.2
      · have h1 := contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω)
          (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (fb p))
        have h2 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω τ.symm τ.target := contMDiffOn_iff_contDiffOn.2 (by
          show ContDiffOn ℂ ω (fun z => z - -(κ₀ (fb p))) _
          exact (contDiff_id.sub contDiff_const).contDiffOn)
        exact h1.comp (h2.mono fun z hz => hz.1) fun z hz => hz.2
    have hκsrc : κ.source = κ₀.source := by
      rw [hκ, OpenPartialHomeomorph.trans_source]
      simp [hτ]
    have hκp : κ (fb p) = 0 := by
      show κ₀ (fb p) + -(κ₀ (fb p)) = 0
      ring
    -- the map `φ = κ ∘ fb ∘ v⁻¹`
    have hW : IsOpen (fb ⁻¹' κ.source ∩ ((↑P₀ : Set X₀.carrier) \ {p})ᶜ) :=
      (κ.open_source.preimage fb.continuous).inter (P₀.finite_toSet.sdiff).isClosed.isOpen_compl
    set D := v.target ∩ v.symm ⁻¹' (fb ⁻¹' κ.source ∩ ((↑P₀ : Set X₀.carrier) \ {p})ᶜ) with hD
    have hDo : IsOpen D := v.isOpen_inter_preimage_symm hW
    have hpv : p ∈ v.source := husrc ⟨t, htu, rfl⟩
    have hvp : v p = 0 := by rw [huv t htu, hut]; ring
    have h0D : (0 : ℂ) ∈ D := by
      have h0t : (0 : ℂ) ∈ v.target := by rw [← hvp]; exact v.map_source hpv
      refine ⟨h0t, ?_⟩
      show v.symm 0 ∈ fb ⁻¹' κ.source ∩ ((↑P₀ : Set X₀.carrier) \ {p})ᶜ
      rw [← hvp, v.left_inv hpv]
      refine ⟨?_, fun h => h.2 rfl⟩
      show fb p ∈ κ.source
      rw [hκsrc]; exact mem_chart_source ℂ _
    set φ : ℂ → ℂ := fun z => κ (fb (v.symm z)) with hφ
    have hφc : ContinuousOn φ D :=
      κ.continuousOn.comp (fb.continuous.comp_continuousOn (v.continuousOn_symm.mono fun z hz => hz.1))
        fun z hz => hz.2.1
    have hφi : InjOn φ D := by
      intro z₁ hz₁ z₂ hz₂ h
      have h1 := κ.injOn hz₁.2.1 hz₂.2.1 h
      exact v.symm.injOn hz₁.1 hz₂.1 (fb.injective h1)
    have hφ0 : φ 0 = 0 := by
      show κ (fb (v.symm 0)) = 0
      conv_lhs => rw [← hvp]
      rw [v.left_inv hpv, hκp]
    obtain ⟨ρ, hρ, σ, hσD, hσc, hσi, hσ0⟩ := s82lc_topological_sqrt hDo h0D hφc hφi hφ0
    set ρ' := min ρ r with hρ'
    have hρ'0 : 0 < ρ' := lt_min hρ hr
    have hbsub : ball (0 : ℂ) ρ' ⊆ ball 0 ρ := ball_subset_ball (min_le_left _ _)
    obtain ⟨Lσ, hLs, hLc, -⟩ := s82lc_openPartialHomeomorph_of_injOn (isOpen_ball (x := (0 : ℂ)) (ε := ρ'))
      (hσc.mono hbsub) (hσi.mono hbsub)
    have hso : IsOpen (pr₀ ⁻¹' ((↑P₀ : Set X₀.carrier) \ {p})ᶜ) :=
      (P₀.finite_toSet.sdiff).isClosed.isOpen_compl.preimage hpr₀.1.continuous
    set c := (u.restrOpen _ hso).trans Lσ with hc
    have hcsrc : ∀ y, y ∈ c.source ↔ y ∈ u.source ∧ pr₀ y ∉ (↑P₀ : Set X₀.carrier) \ {p} ∧ u y ∈ ball 0 ρ' := by
      intro y
      rw [hc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source, hLs]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    have hcy : ∀ y, c y = σ (u y) := fun y => by
      show Lσ (u y) = σ (u y)
      rw [hLc]
    refine ⟨c, κ, 2, (hcsrc t).2 ⟨htu, fun h => h.2 rfl, by rw [hut]; exact mem_ball_self hρ'0⟩, hκm,
      Or.inr rfl, fun y hy => ?_, fun y hy hyP => ?_, fun _ y hy hy0 => ?_, fun _ => ht⟩
    · obtain ⟨hyu, -, hyb⟩ := (hcsrc y).1 hy
      have hpy : pr₀ y ∈ v.source := husrc ⟨y, hyu, rfl⟩
      obtain ⟨hD1, hsq⟩ := hσD (u y) (hbsub hyb)
      rw [← huv y hyu] at hD1 hsq
      have hvy : v.symm (v (pr₀ y)) = pr₀ y := v.left_inv hpy
      refine ⟨?_, ?_⟩
      · have := hD1.2.1
        rwa [hvy] at this
      · rw [hcy, hsq]
        show κ (fb (v.symm (v (pr₀ y)))) = _
        rw [hvy]
    · obtain ⟨hyu, hyP', -⟩ := (hcsrc y).1 hy
      have hyp : pr₀ y = p := by
        by_contra h
        exact hyP' ⟨hyP, h⟩
      refine ⟨?_, rfl⟩
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hpr₀.2.2.2 _ ht)
      have h1 : y ∈ pr₀ ⁻¹' {p} := hyp
      have h2 : t ∈ pr₀ ⁻¹' {p} := rfl
      rw [ha] at h1 h2
      rw [mem_singleton_iff.1 h1, mem_singleton_iff.1 h2]
    · obtain ⟨hyu, -, hyb⟩ := (hcsrc y).1 hy
      rw [hcy] at hy0
      have h1 : u y = 0 := hσi (hbsub hyb) (mem_ball_self hρ) (hy0.trans hσ0.symm)
      exact u.injOn hyu htu (h1.trans hut.symm)
  · -- a regular point
    obtain ⟨e, hte, heq, -⟩ := hreg t ht
    set κ := chartAt ℂ (fb (pr₀ t)) with hκ
    set c := ((e.restrOpen _ hPo).trans fb.toOpenPartialHomeomorph).trans κ with hc
    have hcsrc : ∀ y ∈ c.source, y ∈ e.source ∧ pr₀ y ∉ P₀ ∧ fb (pr₀ y) ∈ κ.source := by
      intro y hy
      have hy' := hy
      rw [hc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.restrOpen_source] at hy'
      obtain ⟨⟨⟨hye, hyP⟩, -⟩, hyκ⟩ := hy'
      refine ⟨hye, hyP, ?_⟩
      have : (e y) = pr₀ y := (heq hye).symm
      simpa [this] using hyκ
    refine ⟨c, κ, 1, ?_, IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) _, Or.inl rfl, fun y hy => ?_,
      fun y hy hyP => absurd hyP (hcsrc y hy).2.1, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · rw [hc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.restrOpen_source]
      refine ⟨⟨⟨hte, ht⟩, trivial⟩, ?_⟩
      show fb ((e.restrOpen _ hPo) t) ∈ κ.source
      show fb (e t) ∈ κ.source
      rw [← heq hte]
      exact mem_chart_source ℂ _
    · obtain ⟨hye, -, hyκ⟩ := hcsrc y hy
      refine ⟨hyκ, ?_⟩
      show κ (fb (e y)) ^ 1 = κ (fb (pr₀ y))
      rw [pow_one, ← heq hye]

/-- Transitions between maximal-atlas charts of a Riemann surface are analytic. -/
theorem s82lc_chart_transition_analyticAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {κ₁ κ₂ : OpenPartialHomeomorph X ℂ} (h₁ : κ₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (h₂ : κ₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {a : ℂ} (ha : a ∈ κ₁.target) (ha2 : κ₁.symm a ∈ κ₂.source) :
    AnalyticAt ℂ (fun z => κ₂ (κ₁.symm z)) a := by
  set N := κ₁.target ∩ κ₁.symm ⁻¹' κ₂.source with hN
  have hNo : IsOpen N := κ₁.isOpen_inter_preimage_symm κ₂.open_source
  have hd : DifferentiableOn ℂ (fun z => κ₂ (κ₁.symm z)) N := by
    intro z hz
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) κ₁.symm z :=
      (contMDiffAt_symm_of_mem_maximalAtlas h₁ hz.1).mdifferentiableAt (by simp)
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) κ₂ (κ₁.symm z) :=
      (contMDiffAt_of_mem_maximalAtlas h₂ hz.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.1 (hm2.comp z hm1)).differentiableWithinAt
  exact hd.analyticAt (hNo.mem_nhds ⟨ha, ha2⟩)

/-- **Transitions of the transported atlas are analytic.** -/
theorem s82lc_transition_analytic {Y X₀ X₁ : ClosedRS.{u}} {P₀ : Finset X₀.carrier} {pr₀ : Y.carrier → X₀.carrier}
    (fb : X₀.carrier ≃ₜ X₁.carrier) (c : Y.carrier → OpenPartialHomeomorph Y.carrier ℂ)
    (κ : Y.carrier → OpenPartialHomeomorph X₁.carrier ℂ) (m : Y.carrier → ℕ)
    (hκm : ∀ t, κ t ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X₁.carrier) (hm : ∀ t, m t = 1 ∨ m t = 2)
    (hcm : ∀ t, ∀ y ∈ (c t).source, fb (pr₀ y) ∈ (κ t).source ∧ c t y ^ m t = κ t (fb (pr₀ y)))
    (hbr : ∀ t, ∀ y ∈ (c t).source, pr₀ y ∈ P₀ → y = t ∧ m t = 2)
    (hz : ∀ t, m t = 2 → ∀ y ∈ (c t).source, c t y = 0 → y = t) (hb2 : ∀ t, m t = 2 → pr₀ t ∈ P₀)
    (t₁ t₂ : Y.carrier) {w : ℂ} (hw : w ∈ (c t₁).target) (hw2 : (c t₁).symm w ∈ (c t₂).source) :
    AnalyticAt ℂ (fun w => c t₂ ((c t₁).symm w)) w := by
  set O := (c t₁).target ∩ (c t₁).symm ⁻¹' (c t₂).source with hO
  have hOo : IsOpen O := (c t₁).isOpen_inter_preimage_symm (c t₂).open_source
  have hwO : w ∈ O := ⟨hw, hw2⟩
  set T : ℂ → ℂ := fun w => c t₂ ((c t₁).symm w) with hT
  have hTc : ContinuousOn T O :=
    (c t₂).continuousOn.comp ((c t₁).continuousOn_symm.mono fun z hz => hz.1) fun z hz => hz.2
  set A : ℂ → ℂ := fun w => κ t₂ ((κ t₁).symm (w ^ m t₁)) with hA
  -- on `O`, `T^{m₂} = A`
  have hTA : ∀ w' ∈ O, (c t₁).symm w' ∈ (c t₁).source ∧ (κ t₁).symm (w' ^ m t₁) = fb (pr₀ ((c t₁).symm w')) ∧
      T w' ^ m t₂ = A w' := by
    intro w' hw'
    set y := (c t₁).symm w'
    have hy1 : y ∈ (c t₁).source := (c t₁).map_target hw'.1
    have hcy : c t₁ y = w' := (c t₁).right_inv hw'.1
    obtain ⟨hk1, he1⟩ := hcm t₁ y hy1
    have hinv : (κ t₁).symm (w' ^ m t₁) = fb (pr₀ y) := by
      rw [← hcy, he1, (κ t₁).left_inv hk1]
    refine ⟨hy1, hinv, ?_⟩
    rw [hA]
    simp only
    rw [hinv]
    exact (hcm t₂ y hw'.2).2
  obtain ⟨hy1, hinv, -⟩ := hTA w hwO
  have hAa : AnalyticAt ℂ A w := by
    have hk1 := (hcm t₁ _ hy1).1
    have ha : w ^ m t₁ ∈ (κ t₁).target := by
      rw [← (c t₁).right_inv hw, (hcm t₁ _ hy1).2]
      exact (κ t₁).map_source hk1
    have ha2 : (κ t₁).symm (w ^ m t₁) ∈ (κ t₂).source := by
      rw [hinv]; exact (hcm t₂ _ hw2).1
    exact (s82lc_chart_transition_analyticAt (hκm t₁) (hκm t₂) ha ha2).comp (f := fun w : ℂ => w ^ m t₁)
      (by fun_prop)
  have hev : ∀ᶠ w' in 𝓝 w, T w' ^ m t₂ = A w' :=
    Filter.eventually_of_mem (hOo.mem_nhds hwO) fun w' hw' => (hTA w' hw').2.2
  rcases hm t₂ with h1 | h2
  · rw [h1] at hev
    exact hAa.congr (hev.mono fun w' hw' => by rw [← hw', pow_one])
  · rw [h2] at hev
    by_cases hA0 : A w = 0
    · -- `T w = 0`: the point over `w` is the branch point `t₂`, which forces `t₁ = t₂`
      have hT0 : T w = 0 := by
        have := hev.self_of_nhds
        rw [hA0] at this
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have hyt : (c t₁).symm w = t₂ := hz t₂ h2 _ hw2 hT0
      have hbp := hb2 t₂ h2
      rw [← hyt] at hbp
      have ht : (c t₁).symm w = t₁ := (hbr t₁ _ hy1 hbp).1
      have h12 : t₁ = t₂ := ht.symm.trans hyt
      subst h12
      refine analyticAt_id.congr (Filter.eventually_of_mem ((c t₁).open_target.mem_nhds hw) fun w' hw' => ?_)
      exact ((c t₁).right_inv hw').symm
    · exact s82lc_analyticAt_of_sq (hOo.mem_nhds hwO) hTc hAa hA0 hev

/-- **W3** (transport of the cover). -/
theorem s82lc_transport {Y X₀ X₁ : ClosedRS.{u}} {P₀ : Finset X₀.carrier} {pr₀ : Y.carrier → X₀.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ P₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P₀, (pr₀ ⁻¹' {x}).ncard = 1)
    (fb : X₀.carrier ≃ₜ X₁.carrier) :
    ∃ (Y₁ : ClosedRS.{u}) (e : Y.carrier ≃ₜ Y₁.carrier) (pr₁ : Y₁.carrier → X₁.carrier),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ ∀ y, pr₁ (e y) = fb (pr₀ y) := by
  classical
  choose c κ m hts hκm hm hcm hbr hz hb2 using fun t => s82lc_transport_chart hpr₀ fb t
  set eU : ULift.{u} Y.carrier ≃ₜ Y.carrier := Homeomorph.ulift with heU
  set C : Y.carrier → OpenPartialHomeomorph (ULift.{u} Y.carrier) ℂ :=
    fun t => eU.toOpenPartialHomeomorph.trans (c t) with hC
  let cs : ChartedSpace ℂ (ULift.{u} Y.carrier) :=
    { atlas := range fun z : ULift.{u} Y.carrier => C z.down
      chartAt := fun z => C z.down
      mem_chart_source := fun z => ⟨trivial, hts z.down⟩
      chart_mem_atlas := fun z => ⟨z, rfl⟩ }
  have hman : IsManifold 𝓘(ℂ) ω (ULift.{u} Y.carrier) := by
    refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
    obtain ⟨z₁, rfl⟩ := he
    obtain ⟨z₂, rfl⟩ := he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ,
      Set.preimage_id, Function.id_comp, Function.comp_id]
    have hso : IsOpen ((C z₁.down).symm ≫ₕ C z₂.down).source := ((C z₁.down).symm ≫ₕ C z₂.down).open_source
    refine DifferentiableOn.contDiffOn (fun w hw => ?_) hso
    have hw' : w ∈ (c z₁.down).target ∧ (c z₁.down).symm w ∈ (c z₂.down).source := by
      simpa [hC, OpenPartialHomeomorph.trans_source, heU] using hw
    have := s82lc_transition_analytic fb c κ m hκm hm hcm hbr hz hb2 z₁.down z₂.down hw'.1 hw'.2
    exact this.differentiableAt.differentiableWithinAt
  have hT2 : T2Space (ULift.{u} Y.carrier) := eU.isEmbedding.t2Space
  have hcomp : CompactSpace (ULift.{u} Y.carrier) := eU.symm.compactSpace
  have hconn : ConnectedSpace (ULift.{u} Y.carrier) := eU.symm.surjective.connectedSpace eU.symm.continuous
  refine ⟨⟨ULift.{u} Y.carrier⟩, eU.symm, fun z => fb (pr₀ z.down), ?_, fun y => rfl⟩
  intro z
  set t := z.down
  set χ := chartAt ℂ (fb (pr₀ t))
  have hzs : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
  have hfz : fb (pr₀ z.down) ∈ χ.source := mem_chart_source ℂ _
  refine (s23_mdifferentiableAt_iff (f := fun z : ULift.{u} Y.carrier => fb (pr₀ z.down)) hzs hfz).2
    ⟨(fb.continuous.comp (hpr₀.1.continuous.comp eU.continuous)).continuousAt, ?_⟩
  -- in charts: `w ↦ χ (κ_t⁻¹ (w^m))`
  have hct : chartAt ℂ z z = c t t := rfl
  have hcz : ∀ w, (chartAt ℂ z).symm w = ULift.up ((c t).symm w) := fun w => rfl
  have hEq : (fun w => χ (fb (pr₀ ((chartAt ℂ z).symm w).down))) =ᶠ[𝓝 (chartAt ℂ z z)]
      fun w => χ ((κ t).symm (w ^ m t)) := by
    rw [hct]
    filter_upwards [(c t).open_target.mem_nhds ((c t).map_source (hts t))] with w hw
    rw [hcz]
    show χ (fb (pr₀ ((c t).symm w))) = χ ((κ t).symm (w ^ m t))
    have hy := (c t).map_target hw
    obtain ⟨hk, he⟩ := hcm t _ hy
    rw [← (c t).right_inv hw, he, (κ t).left_inv hk, (c t).right_inv hw]
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hEq)
  rw [hct]
  obtain ⟨hk, he⟩ := hcm t t (hts t)
  have ha : c t t ^ m t ∈ (κ t).target := by rw [he]; exact (κ t).map_source hk
  have ha2 : (κ t).symm (c t t ^ m t) ∈ χ.source := by rw [he, (κ t).left_inv hk]; exact hfz
  exact ((s82lc_chart_transition_analyticAt (hκm t) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) _) ha ha2).comp
    (f := fun w : ℂ => w ^ m t) (by fun_prop)).differentiableAt

end LiZhongQC
