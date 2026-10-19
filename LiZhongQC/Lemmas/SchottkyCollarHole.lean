import LiZhongQC.Lemmas.QDReflectionEndpointProbe
/-!
# Step 2 of stub B: the hole of a collar curve (round78; prefix `s31qh_` for helpers)

`s31qc_hole_of_collar_curve`: the pull-back `F.ι ∘ s` of a collar curve of the Schottky double tends, along the whole
real diameter, to the boundary of a single hole `D j`.  Cluster points avoid the range of `F.ι` (a `J`-fixed point is
not in `ιd(S)`), the punctures (`s31qr_original_puncture_endpoint`: the limit would be in `Pd`) and the interiors of the
holes; the topological core `s31qh_core` (compactness, disjoint neighbourhoods, connectedness of the diameter) then
selects one hole.
-/

open Complex Set Metric Filter Topology Function
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
universe u

/-- In a compact space, if every cluster point of `f` along `L` lies in `C`, then `f` tends to `𝓝ˢ C`. -/
theorem s31qh_tendsto_nhdsSet {X α : Type*} [TopologicalSpace X] [CompactSpace X] {f : α → X} {L : Filter α}
    {C : Set X} (h : ∀ x, MapClusterPt x L f → x ∈ C) : Tendsto f L (𝓝ˢ C) := by
  rw [(hasBasis_nhdsSet C).tendsto_right_iff]
  rintro U ⟨hUo, hCU⟩
  by_contra hne
  rw [not_eventually] at hne
  have hfr : ∃ᶠ x in map f L, x ∈ Uᶜ := frequently_map.2 hne
  haveI : NeBot (map f L ⊓ 𝓟 Uᶜ) := frequently_iff_neBot.1 hfr
  obtain ⟨x, hxU, hx⟩ := hUo.isClosed_compl.isCompact.exists_clusterPt (f := map f L ⊓ 𝓟 Uᶜ) inf_le_right
  exact hxU (hCU (h x (hx.mono inf_le_left)))

/-- Finitely many pairwise disjoint compact sets in a Hausdorff space have pairwise disjoint open neighbourhoods. -/
theorem s31qh_disjoint_nhds {X : Type*} [TopologicalSpace X] [T2Space X] {m : ℕ} (K : Fin m → Set X)
    (hK : ∀ k, IsCompact (K k)) (hd : Pairwise (Disjoint on K)) :
    ∃ W : Fin m → Set X, (∀ k, IsOpen (W k)) ∧ (∀ k, K k ⊆ W k) ∧ Pairwise (Disjoint on W) := by
  have hsep : ∀ k l : Fin m, k ≠ l → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ K k ⊆ U ∧ K l ⊆ V ∧ Disjoint U V :=
    fun k l hkl => SeparatedNhds.of_isCompact_isCompact (hK k) (hK l) (hd hkl)
  choose U V hUo hVo hKU hKV hUV using hsep
  refine ⟨fun k => ⋂ l, ⋂ (h : l ≠ k), U k l h.symm ∩ V l k h, fun k => ?_, fun k => ?_, fun k l hkl => ?_⟩
  · exact isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun h => (hUo _ _ _).inter (hVo _ _ _)
  · exact subset_iInter fun l => subset_iInter fun h => subset_inter (hKU _ _ _) (hKV _ _ _)
  · have h1 : (⋂ l', ⋂ (h : l' ≠ k), U k l' h.symm ∩ V l' k h) ⊆ U k l hkl :=
      (iInter_subset _ l).trans ((iInter_subset _ hkl.symm).trans inter_subset_left)
    have h2 : (⋂ l', ⋂ (h : l' ≠ l), U l l' h.symm ∩ V l' l h) ⊆ V k l hkl :=
      (iInter_subset _ k).trans ((iInter_subset _ hkl).trans inter_subset_right)
    exact (hUV k l hkl).mono h1 h2

/-- **The topological core of step 2.**  Let `f` be continuous on the upper half of `ball 0 r` with values in a compact
Hausdorff space, and suppose that at every point `y` of the real diameter all cluster points of `f` along
`𝓝[Im > 0] y` lie in the union of finitely many pairwise disjoint compact sets `K k`.  Then one index `j` works for the
whole diameter: `f → 𝓝ˢ (K j)` along `𝓝[Im > 0] y` for every `y`. -/
theorem s31qh_core {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {m : ℕ} (K : Fin m → Set X)
    (hK : ∀ k, IsCompact (K k)) (hd : Pairwise (Disjoint on K)) {r : ℝ} (hr : 0 < r) {f : ℂ → X}
    (hf : ContinuousOn f {z : ℂ | z ∈ ball (0 : ℂ) r ∧ 0 < z.im})
    (hcl : ∀ y : ℝ, |y| < r → ∀ x, MapClusterPt x (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) f → ∃ k, x ∈ K k) :
    ∃ j : Fin m, ∀ y : ℝ, |y| < r → Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝ˢ (K j)) := by
  obtain ⟨W, hWo, hKW, hWd⟩ := s31qh_disjoint_nhds K hK hd
  set H : Set ℂ := {z : ℂ | 0 < z.im} with hH
  -- `P y k`: near `y`, the upper half is mapped into `W k`
  set P : ℝ → Fin m → Prop := fun y k => ∃ ε > 0, ∀ z : ℂ, ‖z - y‖ < ε → 0 < z.im → f z ∈ W k with hP
  have hunion : ∀ y : ℝ, |y| < r → ∀ᶠ z in 𝓝[H] (y : ℂ), f z ∈ ⋃ k, W k := by
    intro y hy
    have h := s31qh_tendsto_nhdsSet (C := ⋃ k, K k) (L := 𝓝[H] (y : ℂ)) (f := f)
      (fun x hx => mem_iUnion.2 (hcl y hy x hx))
    exact h ((isOpen_iUnion hWo).mem_nhdsSet.2 (iUnion_mono hKW))
  -- every `y` has an index
  have hex : ∀ y : ℝ, |y| < r → ∃ k, P y k := by
    intro y hy
    have h1 := hunion y hy
    have h2 : ∀ᶠ z in 𝓝[H] (y : ℂ), z ∈ ball (0 : ℂ) r :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hy))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    -- the half ball is preconnected and its image lies in one `W k`
    set Hb : Set ℂ := ball (y : ℂ) ε ∩ H with hHb
    have hHbc : IsPreconnected Hb := ((convex_ball _ _).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected
    have hHbne : ((y : ℂ) + (ε / 2 : ℝ) * I) ∈ Hb := by
      refine ⟨?_, by simp [hH]; positivity⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hfc : ContinuousOn f Hb := hf.mono fun z hz => ⟨(hball hz).2, hz.2⟩
    have himg : IsPreconnected (f '' Hb) := hHbc.image f hfc
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hball hHbne).1
    refine ⟨k, ε, hε, fun z hz hzi => ?_⟩
    have hzHb : z ∈ Hb := ⟨by rwa [mem_ball, dist_eq_norm], hzi⟩
    have hsub : f '' Hb ⊆ W k ∪ ⋃ l ∈ ({k}ᶜ : Set (Fin m)), W l := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 (hball hw).1
      by_cases hlk : l = k
      · left; rwa [← hlk]
      · right; exact mem_biUnion (show l ∈ ({k}ᶜ : Set (Fin m)) from hlk) hl
    have hdisj : Disjoint (W k) (⋃ l ∈ ({k}ᶜ : Set (Fin m)), W l) := by
      rw [disjoint_iUnion_right]; intro l; rw [disjoint_iUnion_right]; intro hl
      exact hWd (Ne.symm hl)
    have := himg.subset_left_of_subset_union (hWo k) (isOpen_biUnion fun l _ => hWo l) hdisj hsub
      ⟨f _, mem_image_of_mem f hHbne, hk⟩
    exact this (mem_image_of_mem f hzHb)
  -- two indices at nearby points agree
  have hagree : ∀ y y' : ℝ, ∀ k k', ∀ ε > 0, ∀ ε' > 0, |y - y'| < min ε ε' →
      (∀ z : ℂ, ‖z - y‖ < ε → 0 < z.im → f z ∈ W k) → (∀ z : ℂ, ‖z - y'‖ < ε' → 0 < z.im → f z ∈ W k') →
      k = k' := by
    intro y y' k k' ε hε ε' hε' hyy' h1 h2
    by_contra hkk
    set δ : ℝ := min ε ε' - |y - y'| with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    set z : ℂ := (y : ℂ) + (δ / 2 : ℝ) * I with hz
    have hzi : 0 < z.im := by simp [hz]; positivity
    have hnz : ‖(δ / 2 : ℝ) * I‖ = δ / 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hz1 : ‖z - y‖ < ε := by
      rw [hz, add_sub_cancel_left, hnz]; linarith [min_le_left ε ε', abs_nonneg (y - y')]
    have hz2 : ‖z - y'‖ < ε' := by
      have : z - y' = ((y - y' : ℝ) : ℂ) + (δ / 2 : ℝ) * I := by rw [hz]; push_cast; ring
      rw [this]
      calc _ ≤ ‖((y - y' : ℝ) : ℂ)‖ + ‖(δ / 2 : ℝ) * I‖ := norm_add_le _ _
        _ = |y - y'| + δ / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, hnz]
        _ < ε' := by linarith [min_le_right ε ε']
    exact Set.disjoint_left.1 (hWd hkk) (h1 z hz1 hzi) (h2 z hz2 hzi)
  -- the index is constant along the diameter
  obtain ⟨j, hj⟩ := hex 0 (by simpa using hr)
  have hconst : ∀ y : ℝ, |y| < r → P y j := by
    set T : Set ℝ := {y | |y| < r ∧ P y j} with hT
    set T' : Set ℝ := {y | |y| < r ∧ ∃ k, k ≠ j ∧ P y k} with hT'
    have hIoo : Ioo (-r) r = {y : ℝ | |y| < r} := by ext y; simp [abs_lt]
    have hopen : ∀ k, IsOpen {y : ℝ | |y| < r ∧ P y k} := by
      intro k
      rw [Metric.isOpen_iff]
      rintro y ⟨hy, ε, hε, hε'⟩
      refine ⟨min (ε / 2) (r - |y|), lt_min (by positivity) (by linarith), fun y' hy' => ⟨?_, ε / 2, by positivity,
        fun z hz hzi => hε' z ?_ hzi⟩⟩
      · rw [mem_ball, Real.dist_eq] at hy'
        have := abs_sub_abs_le_abs_sub y' y
        linarith [min_le_right (ε / 2) (r - |y|)]
      · rw [mem_ball, Real.dist_eq] at hy'
        calc ‖z - y‖ = ‖(z - y') + ((y' - y : ℝ) : ℂ)‖ := by push_cast; ring_nf
          _ ≤ ‖z - y'‖ + ‖((y' - y : ℝ) : ℂ)‖ := norm_add_le _ _
          _ < ε / 2 + ε / 2 := by
              rw [Complex.norm_real, Real.norm_eq_abs]
              linarith [min_le_left (ε / 2) (r - |y|)]
          _ = ε := by ring
    have hTo : IsOpen T := hopen j
    have hT'o : IsOpen T' := by
      have : T' = ⋃ k ∈ ({j}ᶜ : Set (Fin m)), {y : ℝ | |y| < r ∧ P y k} := by
        ext y; simp only [hT', mem_iUnion, mem_setOf_eq, mem_compl_iff, mem_singleton_iff, exists_prop]
        constructor
        · rintro ⟨hy, k, hk, hP⟩; exact ⟨k, hk, hy, hP⟩
        · rintro ⟨k, hk, hy, hP⟩; exact ⟨hy, k, hk, hP⟩
      rw [this]; exact isOpen_biUnion fun k _ => hopen k
    have hcover : {y : ℝ | |y| < r} ⊆ T ∪ T' := by
      intro y hy
      obtain ⟨k, hk⟩ := hex y hy
      by_cases hkj : k = j
      · left; exact ⟨hy, hkj ▸ hk⟩
      · right; exact ⟨hy, k, hkj, hk⟩
    have hTT' : Disjoint T T' := by
      rw [Set.disjoint_left]
      rintro y ⟨-, ε, hε, h1⟩ ⟨-, k, hk, ε', hε', h2⟩
      exact hk (hagree y y j k ε hε ε' hε' (by rw [sub_self, abs_zero]; exact lt_min hε hε') h1 h2).symm
    have hpc : IsPreconnected {y : ℝ | |y| < r} := by rw [← hIoo]; exact isPreconnected_Ioo
    have := hpc.subset_left_of_subset_union hTo hT'o hTT' hcover ⟨0, by simpa using hr, by simpa using hr, hj⟩
    exact fun y hy => (this hy).2
  -- conclusion
  refine ⟨j, fun y hy => s31qh_tendsto_nhdsSet fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hcl y hy x hx
  by_cases hkj : k = j
  · rwa [← hkj]
  · exfalso
    obtain ⟨ε, hε, hεW⟩ := hconst y hy
    have hev : ∀ᶠ z in 𝓝[H] (y : ℂ), f z ∈ W j :=
      Metric.mem_nhdsWithin_iff.2 ⟨ε, hε, fun z hz => hεW z (by
        have := hz.1; rwa [mem_ball, dist_eq_norm] at this) hz.2⟩
    -- `x ∈ W k` open, so `f` is frequently in `W k`, which is disjoint from `W j`
    have hfreq : ∃ᶠ z in 𝓝[H] (y : ℂ), f z ∈ W k := hx.frequently ((hWo k).mem_nhds (hKW k hk))
    obtain ⟨z, hz1, hz2⟩ := (hfreq.and_eventually hev).exists
    exact Set.disjoint_left.1 (hWd hkj) hz1 hz2

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- **Step 2 of stub B**: a collar curve `γ` of the double (`γ(upper half) ⊆ ιd(S)`, `γ(real diameter)` fixed by `J`)
pulls back, through `F.ι ∘ s` with `ιd ∘ s = γ`, to a curve tending to the boundary of one hole `D j` along the whole
diameter. -/
theorem s31qc_hole_of_collar_curve [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {r : ℝ} (hr : 0 < r) {γ : ℂ → Xd.carrier} (hγ : ContinuousOn γ (ball 0 r))
    (hup : ∀ z ∈ ball 0 r, 0 < z.im → γ z ∈ range ιd)
    (hreal : ∀ z ∈ ball 0 r, z.im = 0 → J (γ z) = γ z)
    (s : ℂ → S) (hs : ∀ z ∈ ball 0 r, 0 < z.im → ιd (s z) = γ z) :
    ∃ j : Fin m, ∀ y : ℝ, |y| < r →
      Tendsto (fun z => F.ι (s z)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝ˢ (frontier (F.D j))) := by
  have _hm := hm
  have _hup := hup
  set H : Set ℂ := {z : ℂ | 0 < z.im} with hH
  set U : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) r ∧ 0 < z.im} with hU
  -- the boundary values of `γ`
  have hyb : ∀ y : ℝ, |y| < r → (y : ℂ) ∈ ball (0 : ℂ) r := fun y hy => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hfix : ∀ y : ℝ, |y| < r → γ y ∉ (Pd : Set Xd.carrier) ∧ γ y ∉ range ιd := by
    intro y hy
    have hJ : J (γ y) = γ y := hreal _ (hyb y hy) (Complex.ofReal_im y)
    have hmem : γ y ∈ {x | J x = x} := hJ
    rw [hd.fixed_curves] at hmem
    refine ⟨hmem.2, ?_⟩
    rintro ⟨s₁, hs₁⟩
    have h2 : γ y ∈ range (J ∘ ιd) := ⟨s₁, by simp only [Function.comp, hs₁, hJ]⟩
    exact Set.disjoint_left.1 hd.disjoint ⟨s₁, hs₁⟩ h2
  -- continuity of `s` and of `F.ι ∘ s` on the upper half disc
  have hsc : ContinuousOn s U := by
    rw [hd.embedding.isInducing.continuousOn_iff]
    exact (hγ.mono fun z hz => hz.1).congr fun z hz => hs z hz.1 hz.2
  have hfc : ContinuousOn (fun z => F.ι (s z)) U := F.embedding.continuous.comp_continuousOn hsc
  -- cluster points lie on the hole boundaries
  have hcl : ∀ y : ℝ, |y| < r → ∀ x, MapClusterPt x (𝓝[H] (y : ℂ)) (fun z => F.ι (s z)) →
      ∃ k, x ∈ frontier (F.D k) := by
    intro y hy x hx
    obtain ⟨Uf, hUfL, hUfx⟩ := mapClusterPt_iff_ultrafilter.1 hx
    -- `ιd ∘ s → γ y` along `Uf`
    have hev : ∀ᶠ z in 𝓝[H] (y : ℂ), ιd (s z) = γ z := by
      have h1 : ∀ᶠ z in 𝓝[H] (y : ℂ), z ∈ ball (0 : ℂ) r := nhdsWithin_le_nhds (isOpen_ball.mem_nhds (hyb y hy))
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hzH using hs z hz hzH
    have hγt : Tendsto γ (𝓝[H] (y : ℂ)) (𝓝 (γ y)) :=
      ((hγ _ (hyb y hy)).continuousAt (isOpen_ball.mem_nhds (hyb y hy))).tendsto.mono_left nhdsWithin_le_nhds
    have hιs : Tendsto (fun z => ιd (s z)) (Uf : Filter ℂ) (𝓝 (γ y)) :=
      (hγt.congr' (hev.mono fun z hz => hz.symm)).mono_left hUfL
    by_cases hxr : x ∈ range F.ι
    · exfalso
      obtain ⟨s₁, rfl⟩ := hxr
      have h1 : Tendsto s (Uf : Filter ℂ) (𝓝 s₁) := F.embedding.isInducing.tendsto_nhds_iff.2 hUfx
      have h2 : Tendsto (fun z => ιd (s z)) (Uf : Filter ℂ) (𝓝 (ιd s₁)) :=
        (hd.embedding.continuous.tendsto s₁).comp h1
      exact (hfix y hy).2 ⟨s₁, tendsto_nhds_unique h2 hιs⟩
    · have hx' : x ∈ (↑F.P ∪ ⋃ j, F.D j : Set F.X.carrier) := by
        by_contra h
        exact hxr (F.range_ι ▸ h)
      rcases hx' with hxP | hxD
      · exfalso
        have : Nonempty S := inferInstance
        obtain ⟨q, ⟨hqP, hqt⟩, -⟩ := s31qr_original_puncture_endpoint F hd hxP
        have h1 : Tendsto s (Uf : Filter ℂ) (comap F.ι (𝓝 x)) := tendsto_comap_iff.2 hUfx
        have h2 := hqt.comp h1
        have : q = γ y := tendsto_nhds_unique h2 hιs
        exact (hfix y hy).1 (this ▸ hqP)
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hxD
        refine ⟨k, ?_⟩
        have hDc : IsClosed (F.D k) := (s31eg_disc_compact (F.disc k)).isClosed
        rw [frontier, hDc.closure_eq]
        refine ⟨hk, fun hint => ?_⟩
        -- `F.ι ∘ s` would enter `F.D k`, which misses the range of `F.ι`
        have hev2 : ∀ᶠ z in (Uf : Filter ℂ), F.ι (s z) ∈ interior (F.D k) :=
          hUfx (isOpen_interior.mem_nhds hint)
        obtain ⟨z, hz⟩ := hev2.exists
        have hzr : F.ι (s z) ∈ range F.ι := mem_range_self _
        rw [F.range_ι] at hzr
        exact hzr (Or.inr (mem_iUnion.2 ⟨k, interior_subset hz⟩))
  -- the topological core
  have hK : ∀ k, IsCompact (frontier (F.D k)) := fun k => isClosed_frontier.isCompact
  have hdisj : Pairwise (Disjoint on fun k => frontier (F.D k)) := fun k l hkl => by
    have h1 : frontier (F.D k) ⊆ F.D k := by
      rw [frontier, (s31eg_disc_compact (F.disc k)).isClosed.closure_eq]; exact sdiff_subset
    have h2 : frontier (F.D l) ⊆ F.D l := by
      rw [frontier, (s31eg_disc_compact (F.disc l)).isClosed.closure_eq]; exact sdiff_subset
    exact (F.disjoint hkl).mono h1 h2
  exact s31qh_core (fun k => frontier (F.D k)) hK hdisj hr hfc hcl

end LiZhongQC
