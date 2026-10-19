import LiZhongQC.Lemmas.S32wStripComponent

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Pointwise ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- **Local half-ball data.**  In a small ball around a point of the lifted seam, `Q = p⁻¹(ιd(S))` is exactly the
`A`-side half-ball and `Q' = p⁻¹(J ιd(S))` the other one. -/
theorem s32w_local_halfball_data {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P)
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ')
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ))
    (a : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ)) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ q, Jt q = q → ∃ r : ℝ, 0 < r ∧ r ≤ ((a • q : UpperHalfPlane) : ℂ).im ∧
      ∀ τ : UpperHalfPlane, ‖((a • τ : UpperHalfPlane) : ℂ) - ((a • q : UpperHalfPlane) : ℂ)‖ < r →
        ((P τ ∈ range ιd ↔ 0 < s * ((a • τ : UpperHalfPlane) : ℂ).re) ∧
         (P τ ∈ range (J ∘ ιd) ↔ s * ((a • τ : UpperHalfPlane) : ℂ).re < 0)) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : UpperHalfPlane → ℂ, ∀ τ, w τ = ((a • τ : UpperHalfPlane) : ℂ) := ⟨_, fun _ => rfl⟩
  have hwim : ∀ τ, 0 < (w τ).im := fun τ => by rw [hw]; exact (a • τ).im_pos
  have hwinj : ∀ τ τ', w τ = w τ' → τ = τ' := fun τ τ' h => by
    rw [hw, hw] at h
    exact MulAction.injective a (UpperHalfPlane.ext h)
  have hfixiff : ∀ τ, Jt τ = τ ↔ (w τ).re = 0 := fun τ => by rw [hw]; exact s32w_fix_iff ha τ
  have hFixOff : ∀ x : Xd.carrier, J x = x → x ∉ range ιd ∧ x ∉ range (J ∘ ιd) := by
    intro x hx
    constructor
    · intro hxr
      have hmem : x ∈ {x | J x = x} := hx
      rw [hd.fixed_curves, hd.embedding.isOpen_range.frontier_eq] at hmem
      exact hmem.1.2 hxr
    · rintro ⟨s', hs'⟩
      have h1 : ιd s' = x := by
        have : J (J (ιd s')) = ιd s' := hd.involution.1 _
        simp only [Function.comp_apply] at hs'
        rw [hs', hx] at this
        exact this.symm
      have hmem : x ∈ {x | J x = x} := hx
      rw [hd.fixed_curves, hd.embedding.isOpen_range.frontier_eq] at hmem
      exact hmem.1.2 ⟨s', h1⟩
  obtain ⟨s, hs, hloc⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ q, Jt q = q → ∃ W : Set UpperHalfPlane,
      IsOpen W ∧ q ∈ W ∧ (∀ τ ∈ W, 0 < s * (w τ).re → P τ ∈ range ιd) ∧
      (∀ τ ∈ W, s * (w τ).re < 0 → P τ ∈ range (J ∘ ιd)) := by
    rcases s32w_side_constant F hd hΓ hfree hP hfib hlift a ha with hL | hR
    · refine ⟨1, Or.inl rfl, fun q hq => ?_⟩
      obtain ⟨W, hWo, hqW, h1, h2⟩ := hL q hq
      exact ⟨W, hWo, hqW, fun τ hτ h => h1 τ hτ (by rw [hw] at h; simpa using h),
        fun τ hτ h => h2 τ hτ (by rw [hw] at h; simpa using h)⟩
    · refine ⟨-1, Or.inr rfl, fun q hq => ?_⟩
      obtain ⟨W, hWo, hqW, h1, h2⟩ := hR q hq
      exact ⟨W, hWo, hqW, fun τ hτ h => h2 τ hτ (by rw [hw] at h; simpa using h),
        fun τ hτ h => h1 τ hτ (by rw [hw] at h; simpa using h)⟩
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨s, hs, fun q hq => ?_⟩
  obtain ⟨W, hWo, hqW, h1, h2⟩ := hloc q hq
  have himg : IsOpen (w '' W) := by
    have : w '' W = ((↑) : UpperHalfPlane → ℂ) '' ((a • ·) '' W) := by
      rw [Set.image_image]; ext z; simp [hw]
    rw [this]
    exact UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ((Homeomorph.smul a).isOpenMap _ hWo)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 himg (w q) ⟨q, hqW, rfl⟩
  have hqim : 0 < ((a • q : UpperHalfPlane) : ℂ).im := (a • q).im_pos
  have hsub : ∀ τ, ‖w τ - w q‖ < min r₀ ((a • q : UpperHalfPlane) : ℂ).im → τ ∈ W := by
    intro τ hτ
    have hmem : w τ ∈ ball (w q) r₀ := by
      rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hτ (min_le_left _ _)
    obtain ⟨τ', hτ'W, hτ'⟩ := hball hmem
    exact (hwinj _ _ hτ') ▸ hτ'W
  refine ⟨min r₀ ((a • q : UpperHalfPlane) : ℂ).im, lt_min hr₀ hqim, min_le_right _ _, fun τ hτ => ?_⟩
  have hτ' : ‖w τ - w q‖ < min r₀ ((a • q : UpperHalfPlane) : ℂ).im := by rw [hw, hw]; exact hτ
  have hτW := hsub τ hτ'
  rw [← hw]
  constructor
  · constructor
    · intro hPτ
      by_contra hneg
      push_neg at hneg
      rcases hneg.lt_or_eq with hlt | heq
      · exact (Set.disjoint_left.1 hd.disjoint) hPτ (h2 τ hτW hlt)
      · have hre : (w τ).re = 0 := by
          rcases mul_eq_zero.1 heq with h | h
          · exact absurd h hs0
          · exact h
        have hfx := (hfixiff τ).2 hre
        exact (hFixOff _ (by rw [← hlift, hfx])).1 hPτ
    · intro hpos
      exact h1 τ hτW hpos
  · constructor
    · intro hPτ
      by_contra hneg
      push_neg at hneg
      rcases hneg.lt_or_eq with hlt | heq
      · exact (Set.disjoint_left.1 hd.disjoint) (h1 τ hτW hlt) hPτ
      · have hre : (w τ).re = 0 := by
          rcases mul_eq_zero.1 heq.symm with h | h
          · exact absurd h hs0
          · exact h
        have hfx := (hfixiff τ).2 hre
        exact (hFixOff _ (by rw [← hlift, hfx])).2 hPτ
    · intro hneg
      exact h2 τ hτW hneg

/-- Transport of a maximal preconnected piece along a homeomorphism that carries `Qa` onto `Qb`. -/
theorem s32w_maxpiece_image {Qa Qb Cm : Set UpperHalfPlane} (T : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hT : ∀ τ, τ ∈ Qa ↔ T τ ∈ Qb)
    (hmax : ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Qa → (D ∩ Cm).Nonempty → D ⊆ Cm) :
    ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Qb → (D ∩ T '' Cm).Nonempty → D ⊆ T '' Cm := by
  intro D hD hDQ ⟨x, hxD, y, hyC, hyx⟩
  have hpre : IsPreconnected (T.symm '' D) := hD.image _ T.symm.continuous.continuousOn
  have hQ : T.symm '' D ⊆ Qa := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hT _).2 (by rw [T.apply_symm_apply]; exact hDQ hz)
  have hne : (T.symm '' D ∩ Cm).Nonempty := by
    refine ⟨T.symm x, ⟨x, hxD, rfl⟩, ?_⟩
    rw [← hyx, T.symm_apply_apply]
    exact hyC
  have hsub := hmax _ hpre hQ hne
  intro z hz
  exact ⟨T.symm z, hsub ⟨z, hz, rfl⟩, T.apply_symm_apply z⟩

/-- A closed piece meets `Q` only inside the piece. -/
theorem s32w_closure_piece {Q C : Set UpperHalfPlane} (hCne : C.Nonempty) (hCconn : IsPreconnected C) (hCQ : C ⊆ Q)
    (hmax : ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Q → (D ∩ C).Nonempty → D ⊆ C) :
    closure C ∩ Q ⊆ C := by
  have hpre : IsPreconnected (closure C ∩ Q) :=
    hCconn.subset_closure (fun x hx => ⟨subset_closure hx, hCQ hx⟩) inter_subset_left
  obtain ⟨c, hc⟩ := hCne
  exact hmax _ hpre inter_subset_right ⟨c, ⟨subset_closure hc, hCQ hc⟩, hc⟩

/-- The upper half-plane is preconnected. -/
theorem s32w_hp_preconnected : PreconnectedSpace UpperHalfPlane := by
  refine ⟨?_⟩
  rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image, Set.image_univ]
  have h : Set.range ((↑) : UpperHalfPlane → ℂ) = {z : ℂ | 0 < z.im} := by
    ext z
    constructor
    · rintro ⟨τ, rfl⟩
      exact τ.im_pos
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  rw [h]
  exact (convex_halfSpace_im_gt 0).isPreconnected

/-- **Local structure of the two lifted halves.**  Around every point of the upper half-plane there is an open set
`U` meeting `Q = p⁻¹(ιd(S))` and `Q' = p⁻¹(J ιd(S))` in preconnected sets, with the seam structure and a reflection
of `U` exchanging `U ∩ Q` and `U ∩ Q'` when both are nonempty. -/
theorem s32w_local_structure {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P) (hPhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P)
    (hPd : ∀ τ, P τ ∉ (↑Pd : Set Xd.carrier))
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ') (hinv : ∀ γ ∈ Γ, ∀ τ, P (γ • τ) = P τ)
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ)) (x : UpperHalfPlane) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ x ∈ U ∧
      IsPreconnected (U ∩ {τ | P τ ∈ range ιd}) ∧ IsPreconnected (U ∩ {τ | P τ ∈ range (J ∘ ιd)}) ∧
      ((U ∩ {τ | P τ ∈ range ιd}).Nonempty → x ∈ closure (U ∩ {τ | P τ ∈ range ιd})) ∧
      ((U ∩ {τ | P τ ∈ range (J ∘ ιd)}).Nonempty → x ∈ closure (U ∩ {τ | P τ ∈ range (J ∘ ιd)})) ∧
      (∀ σ ∈ U, P σ ∈ range ιd ∨ P σ ∈ range (J ∘ ιd) ∨ σ ∈ closure (U ∩ {τ | P τ ∈ range ιd})) ∧
      ((U ∩ {τ | P τ ∈ range ιd}).Nonempty → (U ∩ {τ | P τ ∈ range (J ∘ ιd)}).Nonempty →
        ∃ R : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (R τ) = J (P τ)) ∧
          ∀ τ ∈ U, R τ ∈ U ∧ R (R τ) = τ) := by
  classical
  set Q : Set UpperHalfPlane := {τ | P τ ∈ range ιd} with hQdef
  set Q' : Set UpperHalfPlane := {τ | P τ ∈ range (J ∘ ιd)} with hQ'def
  have hJinv : ∀ y, J (J y) = y := hd.involution.1
  have hQo : IsOpen Q := hd.embedding.isOpen_range.preimage hP.continuous
  have hQ'o : IsOpen Q' :=
    (J.isOpenEmbedding.comp hd.embedding).isOpen_range.preimage hP.continuous
  have hdisj : ∀ τ, τ ∈ Q → τ ∈ Q' → False := fun τ h1 h2 => Set.disjoint_left.1 hd.disjoint h1 h2
  have htri : ∀ y : UpperHalfPlane, y ∈ Q ∨ y ∈ Q' ∨ J (P y) = P y := by
    intro y
    have h : P y ∈ (Set.univ : Set Xd.carrier) := Set.mem_univ _
    rw [← hd.cover] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h (hPd y)
  have hlc := locallyConnectedSpace_iff_subsets_isOpen_isConnected.1
    (inferInstance : LocallyConnectedSpace UpperHalfPlane)
  rcases htri x with hx | hx | hx
  · -- interior point of `Q`
    obtain ⟨V, hVQ, hVo, hxV, hVc⟩ := hlc x Q (hQo.mem_nhds hx)
    have hVQ' : V ∩ Q' = ∅ := by
      ext τ
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hτ hτ'
      exact hdisj τ (hVQ hτ) hτ'
    refine ⟨V, hVo, hxV, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Set.inter_eq_left.2 hVQ]; exact hVc.isPreconnected
    · rw [hVQ']; exact isPreconnected_empty
    · intro _
      rw [Set.inter_eq_left.2 hVQ]
      exact subset_closure hxV
    · intro h
      rw [hVQ'] at h
      exact absurd h (Set.not_nonempty_empty)
    · intro σ hσ
      exact Or.inl (hVQ hσ)
    · intro _ h
      rw [hVQ'] at h
      exact absurd h (Set.not_nonempty_empty)
  · -- interior point of `Q'`
    obtain ⟨V, hVQ, hVo, hxV, hVc⟩ := hlc x Q' (hQ'o.mem_nhds hx)
    have hVQ' : V ∩ Q = ∅ := by
      ext τ
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hτ hτ'
      exact hdisj τ hτ' (hVQ hτ)
    refine ⟨V, hVo, hxV, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hVQ']; exact isPreconnected_empty
    · rw [Set.inter_eq_left.2 hVQ]; exact hVc.isPreconnected
    · intro h
      rw [hVQ'] at h
      exact absurd h (Set.not_nonempty_empty)
    · intro _
      rw [Set.inter_eq_left.2 hVQ]
      exact subset_closure hxV
    · intro σ hσ
      exact Or.inr (Or.inl (hVQ hσ))
    · intro h
      rw [hVQ'] at h
      exact absurd h (Set.not_nonempty_empty)
  · -- point over the fixed curves
    obtain ⟨γ, hγ, hγx⟩ := hfib (Jt x) x (by rw [hlift, hx])
    set J'' : UpperHalfPlane ≃ₜ UpperHalfPlane := Jt.trans (Homeomorph.smul γ) with hJ''def
    have hJ''app : ∀ τ, J'' τ = γ • Jt τ := fun τ => rfl
    have hJ''lift : ∀ τ, P (J'' τ) = J (P τ) := fun τ => by rw [hJ''app, hinv γ hγ, hlift]
    have hJ''fix : J'' x = x := by rw [hJ''app]; exact hγx
    have hanti := s32w_lift_antiholo_loc hP hPhol hd.involution (Jt := J'') hJ''lift
    obtain ⟨a, ha⟩ := s32w_reflection_form J'' hanti hJ''fix
    obtain ⟨s, hs, hdata⟩ := s32w_local_halfball_data F hd hΓ hfree hP hfib hJ''lift a ha
    obtain ⟨r, hr, hrim, hball⟩ := hdata x hJ''fix
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = ((a • x : UpperHalfPlane) : ℂ) := ⟨_, rfl⟩
    rw [← hcdef] at hrim hball
    have hfix0 : c.re = 0 := by rw [hcdef]; exact (s32w_fix_iff ha x).1 hJ''fix
    have hwc : Continuous fun τ : UpperHalfPlane => ((a • τ : UpperHalfPlane) : ℂ) :=
      UpperHalfPlane.continuous_coe.comp (continuous_const_smul a)
    obtain ⟨B, hBdef⟩ : ∃ B : Set UpperHalfPlane,
        B = {τ | ‖((a • τ : UpperHalfPlane) : ℂ) - c‖ < r} := ⟨_, rfl⟩
    have hBmem : ∀ τ, τ ∈ B ↔ ‖((a • τ : UpperHalfPlane) : ℂ) - c‖ < r := fun τ => by subst hBdef; exact Iff.rfl
    have hBo : IsOpen B := by
      rw [hBdef]
      exact isOpen_lt (continuous_norm.comp (hwc.sub continuous_const)) continuous_const
    have hxB : x ∈ B := by
      rw [hBmem, hcdef, sub_self, norm_zero]
      exact hr
    have hdat : ∀ τ ∈ B, (τ ∈ Q ↔ 0 < s * ((a • τ : UpperHalfPlane) : ℂ).re) ∧
        (τ ∈ Q' ↔ s * ((a • τ : UpperHalfPlane) : ℂ).re < 0) :=
      fun τ hτ => hball τ ((hBmem τ).1 hτ)
    have hBQ : B ∩ Q = {τ | ‖((a • τ : UpperHalfPlane) : ℂ) - c‖ < r ∧
        0 < s * ((a • τ : UpperHalfPlane) : ℂ).re} := by
      ext τ
      constructor
      · rintro ⟨hb, hq⟩
        exact ⟨(hBmem τ).1 hb, ((hdat τ hb).1).1 hq⟩
      · rintro ⟨hb, hq⟩
        exact ⟨(hBmem τ).2 hb, ((hdat τ ((hBmem τ).2 hb)).1).2 hq⟩
    have hBQ' : B ∩ Q' = {τ | ‖((a • τ : UpperHalfPlane) : ℂ) - c‖ < r ∧
        0 < (-s) * ((a • τ : UpperHalfPlane) : ℂ).re} := by
      ext τ
      constructor
      · rintro ⟨hb, hq⟩
        have := ((hdat τ hb).2).1 hq
        exact ⟨(hBmem τ).1 hb, by linarith⟩
      · rintro ⟨hb, hq⟩
        exact ⟨(hBmem τ).2 hb, ((hdat τ ((hBmem τ).2 hb)).2).2 (by linarith)⟩
    have hs' : -s = 1 ∨ -s = -1 := by
      rcases hs with h | h
      · right; simp [h]
      · left; simp [h]
    have hside : ∀ q ∈ B, ((a • q : UpperHalfPlane) : ℂ).re = 0 → ∀ W ∈ 𝓝 q,
        (∃ τ ∈ W ∩ B, 0 < s * ((a • τ : UpperHalfPlane) : ℂ).re) ∧
        (∃ τ ∈ W ∩ B, s * ((a • τ : UpperHalfPlane) : ℂ).re < 0) := by
      intro q hqB hq0 W hW
      obtain ⟨⟨τ₁, h1, h1'⟩, ⟨τ₂, h2, h2'⟩⟩ :=
        s32w_near_sides a hq0 (Filter.inter_mem hW (hBo.mem_nhds hqB))
      rcases hs with h | h
      · rw [h]
        exact ⟨⟨τ₁, h1, by linarith⟩, ⟨τ₂, h2, by linarith⟩⟩
      · rw [h]
        exact ⟨⟨τ₂, h2, by linarith⟩, ⟨τ₁, h1, by linarith⟩⟩
    have hclB : ∀ q ∈ B, ((a • q : UpperHalfPlane) : ℂ).re = 0 →
        q ∈ closure (B ∩ Q) ∧ q ∈ closure (B ∩ Q') := by
      intro q hqB hq0
      constructor
      · rw [mem_closure_iff_nhds]
        intro W hW
        obtain ⟨⟨τ, hτ, hpos⟩, -⟩ := hside q hqB hq0 W hW
        exact ⟨τ, hτ.1, hτ.2, ((hdat τ hτ.2).1).2 hpos⟩
      · rw [mem_closure_iff_nhds]
        intro W hW
        obtain ⟨-, ⟨τ, hτ, hneg⟩⟩ := hside q hqB hq0 W hW
        exact ⟨τ, hτ.1, hτ.2, ((hdat τ hτ.2).2).2 hneg⟩
    have hcovB : ∀ σ ∈ B, σ ∈ Q ∨ σ ∈ Q' ∨ σ ∈ closure (B ∩ Q) := by
      intro σ hσ
      rcases lt_trichotomy (s * ((a • σ : UpperHalfPlane) : ℂ).re) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inl (((hdat σ hσ).2).2 hlt))
      · right; right
        have hre : ((a • σ : UpperHalfPlane) : ℂ).re = 0 := by
          rcases mul_eq_zero.1 heq with h | h
          · exact absurd h hs0
          · exact h
        exact (hclB σ hσ hre).1
      · exact Or.inl (((hdat σ hσ).1).2 hgt)
    have hRsym : ∀ τ ∈ B, J'' τ ∈ B ∧ J'' (J'' τ) = τ := by
      intro τ hτ
      constructor
      · rw [hBmem, ha τ]
        have hcc : conj c = -c := by
          apply Complex.ext <;> simp [hfix0]
        have h1 : -conj ((a • τ : UpperHalfPlane) : ℂ) - c =
            -conj (((a • τ : UpperHalfPlane) : ℂ) - c) := by
          rw [map_sub, hcc]; ring
        rw [h1, norm_neg, Complex.norm_conj]
        exact (hBmem τ).1 hτ
      · apply MulAction.injective a
        apply UpperHalfPlane.ext
        rw [ha, ha]
        simp
    refine ⟨B, hBo, hxB, ?_, ?_, ?_, ?_, hcovB, ?_⟩
    · rw [hBQ]; exact s32w_halfball_preconnected a hs c hrim
    · rw [hBQ']; exact s32w_halfball_preconnected a hs' c hrim
    · intro _; exact (hclB x hxB (by rw [← hcdef]; exact hfix0)).1
    · intro _; exact (hclB x hxB (by rw [← hcdef]; exact hfix0)).2
    · intro _ _
      exact ⟨J'', hJ''lift, hRsym⟩

/-- **(b4) Generation by tiles.**  A homeomorphism `Φ` of the upper half-plane commuting with the stabiliser of the
lifted half `C` and with every lift of `J` fixing a point of `closure C` commutes with all of `Γ`. -/
theorem s32w_tile_generation {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P) (hPhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P)
    (hPd : ∀ τ, P τ ∉ (↑Pd : Set Xd.carrier))
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ') (hinv : ∀ γ ∈ Γ, ∀ τ, P (γ • τ) = P τ)
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ))
    {C : Set UpperHalfPlane} (hCne : C.Nonempty) (hCconn : IsPreconnected C)
    (hCQ : ∀ τ ∈ C, P τ ∈ range ιd)
    (hCmax : ∀ D : Set UpperHalfPlane, IsPreconnected D → (∀ τ ∈ D, P τ ∈ range ιd) →
      (D ∩ C).Nonempty → D ⊆ C)
    {Φ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hstab : ∀ g ∈ Γ, g • C = C → ∀ τ, Φ (g • τ) = g • Φ τ)
    (hrefl : ∀ J' : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (J' τ) = J (P τ)) →
      (∃ τ ∈ closure C, J' τ = τ) → ∀ τ, Φ (J' τ) = J' (Φ τ)) :
    ∀ γ ∈ Γ, ∀ τ, Φ (γ • τ) = γ • Φ τ := by
  classical
  haveI : PreconnectedSpace UpperHalfPlane := s32w_hp_preconnected
  have hJinv : ∀ y, J (J y) = y := hd.involution.1
  set Q : Set UpperHalfPlane := {τ | P τ ∈ range ιd} with hQdef
  set Q' : Set UpperHalfPlane := {τ | P τ ∈ range (J ∘ ιd)} with hQ'def
  set K : Set UpperHalfPlane := closure C with hKdef
  have hCQ' : C ⊆ Q := fun τ hτ => hCQ τ hτ
  have hmaxC : ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Q → (D ∩ C).Nonempty → D ⊆ C :=
    fun D hD hDQ hne => hCmax D hD (fun τ hτ => hDQ hτ) hne
  have hLS : ∀ x : UpperHalfPlane, ∃ U : Set UpperHalfPlane, IsOpen U ∧ x ∈ U ∧
      IsPreconnected (U ∩ Q) ∧ IsPreconnected (U ∩ Q') ∧
      ((U ∩ Q).Nonempty → x ∈ closure (U ∩ Q)) ∧ ((U ∩ Q').Nonempty → x ∈ closure (U ∩ Q')) ∧
      (∀ σ ∈ U, σ ∈ Q ∨ σ ∈ Q' ∨ σ ∈ closure (U ∩ Q)) ∧
      ((U ∩ Q).Nonempty → (U ∩ Q').Nonempty → ∃ R : UpperHalfPlane ≃ₜ UpperHalfPlane,
        (∀ τ, P (R τ) = J (P τ)) ∧ ∀ τ ∈ U, R τ ∈ U ∧ R (R τ) = τ) :=
    fun x => s32w_local_structure F hd hΓ hfree hP hPhol hPd hfib hinv hlift x
  -- tiles
  obtain ⟨Tile, hTile⟩ : ∃ Tile : (UpperHalfPlane ≃ₜ UpperHalfPlane) → Prop, ∀ T, Tile T ↔
      ((∀ τ, P (T τ) = P τ) ∨ (∀ τ, P (T τ) = J (P τ))) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Comm, hComm⟩ : ∃ Comm : (UpperHalfPlane ≃ₜ UpperHalfPlane) → Prop,
      ∀ T, Comm T ↔ ∀ τ, Φ (T τ) = T (Φ τ) := ⟨_, fun _ => Iff.rfl⟩
  have hTrans : ∀ T T' : UpperHalfPlane ≃ₜ UpperHalfPlane, Tile T → Tile T' → Tile (T.trans T') := by
    intro T T' hT hT'
    rw [hTile] at hT hT' ⊢
    rcases hT with hT | hT <;> rcases hT' with hT' | hT'
    · left; intro τ; show P (T' (T τ)) = _; rw [hT', hT]
    · right; intro τ; show P (T' (T τ)) = _; rw [hT', hT]
    · right; intro τ; show P (T' (T τ)) = _; rw [hT', hT]
    · left; intro τ; show P (T' (T τ)) = _; rw [hT', hT, hJinv]
  have hTsymm : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, Tile T → Tile T.symm := by
    intro T hT
    rw [hTile] at hT ⊢
    rcases hT with hT | hT
    · left
      intro σ
      have h := hT (T.symm σ)
      rw [T.apply_symm_apply] at h
      exact h.symm
    · right
      intro σ
      have h := hT (T.symm σ)
      rw [T.apply_symm_apply] at h
      rw [h, hJinv]
  have hsmTile : ∀ g ∈ Γ, Tile (Homeomorph.smul g : UpperHalfPlane ≃ₜ UpperHalfPlane) :=
    fun g hg => (hTile _).2 (Or.inl fun τ => hinv g hg τ)
  have hQT : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = P τ) → ∀ τ, τ ∈ Q ↔ T τ ∈ Q := by
    intro T hT τ
    show P τ ∈ range ιd ↔ P (T τ) ∈ range ιd
    rw [hT]
  have hQT' : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = J (P τ)) →
      ∀ τ, τ ∈ Q ↔ T τ ∈ Q' := by
    intro T hT τ
    show P τ ∈ range ιd ↔ P (T τ) ∈ range (J ∘ ιd)
    rw [hT]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, by show J (ιd s) = J (P τ); rw [hs]⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      have h1 : J (ιd s) = J (P τ) := hs
      exact J.injective h1
  have hpieceJ : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = J (P τ)) →
      ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Q' → (D ∩ T '' C).Nonempty → D ⊆ T '' C :=
    fun T hT => s32w_maxpiece_image T (hQT' T hT) hmaxC
  have hpieceΓ : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = P τ) →
      ∀ D : Set UpperHalfPlane, IsPreconnected D → D ⊆ Q → (D ∩ T '' C).Nonempty → D ⊆ T '' C :=
    fun T hT => s32w_maxpiece_image T (hQT T hT) hmaxC
  have himgΓ : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = P τ) → T '' C ⊆ Q := by
    intro T hT y hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact (hQT T hT c).1 (hCQ' hc)
  have himgJ : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (T τ) = J (P τ)) → T '' C ⊆ Q' := by
    intro T hT y hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact (hQT' T hT c).1 (hCQ' hc)
  have hTK : ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, T '' K = closure (T '' C) :=
    fun T => T.image_closure C
  have hmemK : ∀ (T : UpperHalfPlane ≃ₜ UpperHalfPlane) (σ : UpperHalfPlane), σ ∈ T '' C → σ ∈ T '' K := by
    intro T σ h
    rw [hTK]
    exact subset_closure h
  have hmemKcl : ∀ (T : UpperHalfPlane ≃ₜ UpperHalfPlane) (σ : UpperHalfPlane),
      σ ∈ closure (T '' C) → σ ∈ T '' K := by
    intro T σ h
    rw [hTK]
    exact h
  -- closure geometry of the half
  have hJAo : IsOpen (range (J ∘ ιd)) := (J.isOpenEmbedding.comp hd.embedding).isOpen_range
  have hF1 : ∀ z ∈ K, P z ∈ closure (range ιd) := fun z hz =>
    map_mem_closure hP.continuous hz (fun c hc => hCQ c hc)
  have hF2 : ∀ y, y ∈ closure (range ιd) → y ∈ range (J ∘ ιd) → False := fun y h1 h2 =>
    Set.disjoint_left.1 (hd.disjoint.closure_left hJAo) h1 h2
  have hseam : ∀ z ∈ K, P z ∉ range ιd → J (P z) = P z := by
    intro z hz hnot
    have h : P z ∈ frontier (range ιd) \ (↑Pd : Set Xd.carrier) :=
      ⟨by rw [hd.embedding.isOpen_range.frontier_eq]; exact ⟨hF1 z hz, hnot⟩, hPd z⟩
    rw [← hd.fixed_curves] at h
    exact h
  -- translates of the half
  have hgC0 : ∀ g ∈ Γ, ∀ c₀ ∈ C, g • c₀ ∈ C → g • C = C := by
    intro g hg c₀ hc₀ hgc₀
    have hsub : ∀ h ∈ Γ, ∀ c₁ ∈ C, h • c₁ ∈ C → ∀ y ∈ C, h • y ∈ C := by
      intro h hh c₁ hc₁ hhc₁ y hy
      have hpre : IsPreconnected ((Homeomorph.smul h : UpperHalfPlane ≃ₜ UpperHalfPlane) '' C) :=
        hCconn.image _ (Homeomorph.smul h).continuous.continuousOn
      have hshape : ∀ τ, P ((Homeomorph.smul h : UpperHalfPlane ≃ₜ UpperHalfPlane) τ) = P τ :=
        fun τ => hinv h hh τ
      have := hmaxC _ hpre (himgΓ _ hshape) ⟨h • c₁, ⟨c₁, hc₁, rfl⟩, hhc₁⟩
      exact this ⟨y, hy, rfl⟩
    have hsub1 := hsub g hg c₀ hc₀ hgc₀
    have hsub2 := hsub g⁻¹ (Γ.inv_mem hg) (g • c₀) hgc₀ (by rw [inv_smul_smul]; exact hc₀)
    apply Set.Subset.antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hsub1 c hc
    · intro y hy
      exact ⟨g⁻¹ • y, hsub2 y hy, smul_inv_smul g y⟩
  have hgC : ∀ g ∈ Γ, ∀ k ∈ K, g • k ∈ K → g • C = C := by
    intro g hg k hk hgk
    obtain ⟨U, hUo, hzU, hUQ, -, -, -, -, -⟩ := hLS (g • k)
    obtain ⟨y1, hy1U, hy1C⟩ := mem_closure_iff.1 hgk U hUo hzU
    have hk' : g • k ∈ closure ((Homeomorph.smul g : UpperHalfPlane ≃ₜ UpperHalfPlane) '' C) := by
      rw [← (Homeomorph.smul g).image_closure]
      exact ⟨k, hk, rfl⟩
    obtain ⟨y2, hy2U, c2, hc2C, hc2⟩ := mem_closure_iff.1 hk' U hUo hzU
    have hshape : ∀ τ, P ((Homeomorph.smul g : UpperHalfPlane ≃ₜ UpperHalfPlane) τ) = P τ :=
      fun τ => hinv g hg τ
    have hUC : U ∩ Q ⊆ C := hmaxC _ hUQ inter_subset_right ⟨y1, ⟨hy1U, hCQ' hy1C⟩, hy1C⟩
    have hy2Q : y2 ∈ Q := himgΓ _ hshape ⟨c2, hc2C, hc2⟩
    have hgc2 : g • c2 = y2 := hc2
    exact hgC0 g hg c2 hc2C (by rw [hgc2]; exact hUC ⟨hy2U, hy2Q⟩)
  -- two lifts of `P` agreeing at a point agree
  have hunique : ∀ (T : UpperHalfPlane ≃ₜ UpperHalfPlane) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ τ, P (T τ) = P τ) → (∀ τ, P (g • τ) = P τ) → ∀ k, T k = g • k → ∀ τ, T τ = g • τ := by
    intro T g hT hg k hk τ
    have h := (T2Space.isSeparatedMap P).eq_of_comp_eq hP.isLocallyInjective T.continuous
      (continuous_const_smul g) (funext fun τ => (hT τ).trans (hg τ).symm) k hk
    exact congrFun h τ
  -- a tile moving a point of the closed half into it commutes with `Φ`
  have hS0 : ∀ S : UpperHalfPlane ≃ₜ UpperHalfPlane, Tile S → ∀ k ∈ K, S k ∈ K → Comm S := by
    intro S hS k hk hSk
    rw [hComm]
    have hPk : P (S k) = P k := by
      rcases (hTile S).1 hS with h | h
      · exact h k
      · have hn : P k ∉ range ιd := by
          intro hmem
          apply hF2 (P (S k)) (hF1 _ hSk)
          rw [h k]
          obtain ⟨s, hs⟩ := hmem
          exact ⟨s, by show J (ιd s) = J (P k); rw [hs]⟩
        rw [h k]
        exact hseam k hk hn
    obtain ⟨g, hg, hgk⟩ := hfib k (S k) hPk.symm
    have hgCC : g • C = C := hgC g hg k hk (by rw [hgk]; exact hSk)
    have hcg := hstab g hg hgCC
    rcases (hTile S).1 hS with h | h
    · have hSg : ∀ τ, S τ = g • τ :=
        hunique S g h (fun τ => hinv g hg τ) k hgk.symm
      intro τ
      rw [hSg, hSg]
      exact hcg τ
    · set S' : UpperHalfPlane ≃ₜ UpperHalfPlane := S.trans (Homeomorph.smul g⁻¹) with hS'
      have hS'app : ∀ τ, S' τ = g⁻¹ • S τ := fun τ => rfl
      have hS'lift : ∀ τ, P (S' τ) = J (P τ) := fun τ => by
        rw [hS'app, hinv g⁻¹ (Γ.inv_mem hg), h]
      have hS'fix : S' k = k := by rw [hS'app, ← hgk, inv_smul_smul]
      have hc' := hrefl S' hS'lift ⟨k, hk, hS'fix⟩
      have hSτ : ∀ σ, S σ = g • S' σ := fun σ => by rw [hS'app, smul_inv_smul]
      intro τ
      rw [hSτ τ, hSτ (Φ τ), hcg, hc']
  -- tiles meeting in a point are simultaneously commuting
  have hS : ∀ T T' : UpperHalfPlane ≃ₜ UpperHalfPlane, Tile T → Tile T' → ∀ z, z ∈ T '' K →
      z ∈ T' '' K → Comm T → Comm T' := by
    intro T T' hT hT' z hz hz' hcT
    obtain ⟨k, hk, hkz⟩ := hz
    obtain ⟨k', hk', hk'z⟩ := hz'
    set S : UpperHalfPlane ≃ₜ UpperHalfPlane := T.trans T'.symm with hSdef
    have hSapp : ∀ τ, S τ = T'.symm (T τ) := fun τ => rfl
    have hSk : S k ∈ K := by
      rw [hSapp, hkz, ← hk'z, T'.symm_apply_apply]
      exact hk'
    have hcS := (hComm S).1 (hS0 S (hTrans T T'.symm hT (hTsymm T' hT')) k hk hSk)
    have hcT' := (hComm T).1 hcT
    rw [hComm]
    intro σ
    obtain ⟨τ, rfl⟩ : ∃ τ, S τ = σ := ⟨S.symm σ, S.apply_symm_apply σ⟩
    have h1 : ∀ τ', T' (S τ') = T τ' := fun τ' => by
      rw [hSapp]; exact T'.apply_symm_apply _
    rw [h1, hcS τ, h1, hcT' τ]
  -- local finiteness of the tiles
  have hLF : ∀ x : UpperHalfPlane, ∃ U : Set UpperHalfPlane, IsOpen U ∧ x ∈ U ∧
      ∀ T : UpperHalfPlane ≃ₜ UpperHalfPlane, Tile T → (T '' K ∩ U).Nonempty → x ∈ T '' K := by
    intro x
    obtain ⟨U, hUo, hxU, hUQ, hUQ', hcl, hcl', -, -⟩ := hLS x
    refine ⟨U, hUo, hxU, ?_⟩
    intro T hT hne
    obtain ⟨z, hzT, hzU⟩ := hne
    have hzT' := hzT
    rw [hTK] at hzT'
    obtain ⟨y, hyU, hyT⟩ := mem_closure_iff.1 hzT' U hUo hzU
    apply hmemKcl
    rcases (hTile T).1 hT with h | h
    · have hyQ := himgΓ T h hyT
      have hsub : U ∩ Q ⊆ T '' C :=
        hpieceΓ T h _ hUQ inter_subset_right ⟨y, ⟨hyU, hyQ⟩, hyT⟩
      exact closure_mono hsub (hcl ⟨y, hyU, hyQ⟩)
    · have hyQ := himgJ T h hyT
      have hsub : U ∩ Q' ⊆ T '' C :=
        hpieceJ T h _ hUQ' inter_subset_right ⟨y, ⟨hyU, hyQ⟩, hyT⟩
      exact closure_mono hsub (hcl' ⟨y, hyU, hyQ⟩)
  have hclosed : ∀ Pr : (UpperHalfPlane ≃ₜ UpperHalfPlane) → Prop,
      IsClosed {τ : UpperHalfPlane | ∃ T, Tile T ∧ Pr T ∧ τ ∈ T '' K} := by
    intro Pr
    refine closure_subset_iff_isClosed.1 (fun x hx => ?_)
    obtain ⟨U, hUo, hxU, hLFU⟩ := hLF x
    obtain ⟨z, hzU, T, hT, hPr, hzT⟩ := mem_closure_iff.1 hx U hUo hxU
    exact ⟨T, hT, hPr, hLFU T hT ⟨z, hzT, hzU⟩⟩
  -- the tiles cover: the union is open
  have hRopen : IsOpen {τ : UpperHalfPlane | ∃ T, Tile T ∧ τ ∈ T '' K} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨T, hT, hxT⟩ := hx
    obtain ⟨U, hUo, hxU, hUQ, hUQ', hcl, hcl', hcov, hrf⟩ := hLS x
    refine Filter.mem_of_superset (hUo.mem_nhds hxU) ?_
    have hxT' := hxT
    rw [hTK] at hxT'
    obtain ⟨y, hyU, hyT⟩ := mem_closure_iff.1 hxT' U hUo hxU
    intro σ hσ
    rcases (hTile T).1 hT with h | h
    · -- `T` covers the identity
      have hyQ := himgΓ T h hyT
      have hsub : U ∩ Q ⊆ T '' C :=
        hpieceΓ T h _ hUQ inter_subset_right ⟨y, ⟨hyU, hyQ⟩, hyT⟩
      rcases hcov σ hσ with hσQ | hσQ' | hσcl
      · exact ⟨T, hT, hmemK T σ (hsub ⟨hσ, hσQ⟩)⟩
      · obtain ⟨R_, hRlift, hRU⟩ := hrf ⟨y, hyU, hyQ⟩ ⟨σ, hσ, hσQ'⟩
        have hRσ : R_ σ ∈ U ∩ Q := by
          refine ⟨(hRU σ hσ).1, ?_⟩
          refine (hQT' R_ hRlift (R_ σ)).2 ?_
          rw [(hRU σ hσ).2]
          exact hσQ'
        obtain ⟨c, hcC, hcσ⟩ := hsub hRσ
        have hRT : Tile (T.trans R_) := hTrans T R_ hT ((hTile R_).2 (Or.inr hRlift))
        refine ⟨T.trans R_, hRT, hmemK _ σ ⟨c, hcC, ?_⟩⟩
        show R_ (T c) = σ
        rw [hcσ]
        exact (hRU σ hσ).2
      · exact ⟨T, hT, hmemKcl T σ (closure_mono hsub hσcl)⟩
    · -- `T` covers `J`
      have hyQ := himgJ T h hyT
      have hsub : U ∩ Q' ⊆ T '' C :=
        hpieceJ T h _ hUQ' inter_subset_right ⟨y, ⟨hyU, hyQ⟩, hyT⟩
      have hJcase : ∀ R_ : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, P (R_ τ) = J (P τ)) →
          (∀ τ ∈ U, R_ τ ∈ U ∧ R_ (R_ τ) = τ) → ∀ τ ∈ U ∩ Q, τ ∈ (T.trans R_) '' C := by
        intro R_ hRlift hRU τ hτ
        have hRτ : R_ τ ∈ U ∩ Q' := ⟨(hRU τ hτ.1).1, (hQT' R_ hRlift τ).1 hτ.2⟩
        obtain ⟨c, hcC, hcτ⟩ := hsub hRτ
        refine ⟨c, hcC, ?_⟩
        show R_ (T c) = τ
        rw [hcτ]
        exact (hRU τ hτ.1).2
      rcases hcov σ hσ with hσQ | hσQ' | hσcl
      · obtain ⟨R_, hRlift, hRU⟩ := hrf ⟨σ, hσ, hσQ⟩ ⟨y, hyU, hyQ⟩
        have hRT : Tile (T.trans R_) := hTrans T R_ hT ((hTile R_).2 (Or.inr hRlift))
        exact ⟨T.trans R_, hRT, hmemK _ σ (hJcase R_ hRlift hRU σ ⟨hσ, hσQ⟩)⟩
      · exact ⟨T, hT, hmemK T σ (hsub ⟨hσ, hσQ'⟩)⟩
      · obtain ⟨τ₀, hτ₀⟩ : (U ∩ Q).Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, closure_empty] at hσcl
          exact hσcl
        obtain ⟨R_, hRlift, hRU⟩ := hrf ⟨τ₀, hτ₀⟩ ⟨y, hyU, hyQ⟩
        have hRT : Tile (T.trans R_) := hTrans T R_ hT ((hTile R_).2 (Or.inr hRlift))
        have hsub2 : U ∩ Q ⊆ (T.trans R_) '' C := hJcase R_ hRlift hRU
        exact ⟨T.trans R_, hRT, hmemKcl _ σ (closure_mono hsub2 hσcl)⟩
  have hRuniv : ∀ τ : UpperHalfPlane, ∃ T, Tile T ∧ τ ∈ T '' K := by
    have hrefT : Tile (Homeomorph.refl UpperHalfPlane) := (hTile _).2 (Or.inl fun τ => rfl)
    obtain ⟨τ₀, hτ₀⟩ := hCne
    have hcl : IsClosed {τ : UpperHalfPlane | ∃ T, Tile T ∧ τ ∈ T '' K} := by
      have h := hclosed (fun _ => True)
      simp only [true_and] at h
      exact h
    have hcut := (IsClopen.eq_univ ⟨hcl, hRopen⟩
      ⟨τ₀, ⟨Homeomorph.refl UpperHalfPlane, hrefT, ⟨τ₀, subset_closure hτ₀, rfl⟩⟩⟩)
    intro τ
    have : τ ∈ {τ : UpperHalfPlane | ∃ T, Tile T ∧ τ ∈ T '' K} := by
      rw [hcut]; exact Set.mem_univ _
    exact this
  -- partition into commuting and non-commuting tiles
  have hdisj : ∀ τ, ¬ ((∃ T, Tile T ∧ Comm T ∧ τ ∈ T '' K) ∧ (∃ T, Tile T ∧ ¬ Comm T ∧ τ ∈ T '' K)) := by
    rintro τ ⟨⟨T, hT, hcT, hτ⟩, ⟨T', hT', hcT', hτ'⟩⟩
    exact hcT' (hS T T' hT hT' τ hτ hτ' hcT)
  have hEuniv : ∀ τ : UpperHalfPlane, ∃ T, Tile T ∧ Comm T ∧ τ ∈ T '' K := by
    have hFc := hclosed (fun T => ¬ Comm T)
    have hEeq : {τ : UpperHalfPlane | ∃ T, Tile T ∧ Comm T ∧ τ ∈ T '' K} =
        {τ : UpperHalfPlane | ∃ T, Tile T ∧ ¬ Comm T ∧ τ ∈ T '' K}ᶜ := by
      ext τ
      constructor
      · intro h hF
        exact hdisj τ ⟨h, hF⟩
      · intro hF
        obtain ⟨T, hT, hτ⟩ := hRuniv τ
        by_cases hc : Comm T
        · exact ⟨T, hT, hc, hτ⟩
        · exact absurd ⟨T, hT, hc, hτ⟩ hF
    have hEo : IsClopen {τ : UpperHalfPlane | ∃ T, Tile T ∧ Comm T ∧ τ ∈ T '' K} := by
      refine ⟨hclosed Comm, ?_⟩
      rw [hEeq]
      exact hFc.isOpen_compl
    have hrefT : Tile (Homeomorph.refl UpperHalfPlane) := (hTile _).2 (Or.inl fun τ => rfl)
    have hcommrefl : Comm (Homeomorph.refl UpperHalfPlane) := (hComm _).2 fun τ => rfl
    obtain ⟨τ₀, hτ₀⟩ := hCne
    have hcut := hEo.eq_univ ⟨τ₀, ⟨Homeomorph.refl UpperHalfPlane, hrefT, hcommrefl,
      ⟨τ₀, subset_closure hτ₀, rfl⟩⟩⟩
    intro τ
    have : τ ∈ {τ : UpperHalfPlane | ∃ T, Tile T ∧ Comm T ∧ τ ∈ T '' K} := by
      rw [hcut]; exact Set.mem_univ _
    exact this
  -- conclusion
  intro γ hγ τ
  obtain ⟨τ₀, hτ₀⟩ := hCne
  obtain ⟨T, hT, hcT, hmem⟩ := hEuniv (γ • τ₀)
  obtain ⟨k, hk, hkτ⟩ := hmem
  set S : UpperHalfPlane ≃ₜ UpperHalfPlane := (Homeomorph.smul γ).trans T.symm with hSdef
  have hSapp : ∀ σ, S σ = T.symm (γ • σ) := fun σ => rfl
  have hSτ₀ : S τ₀ ∈ K := by
    rw [hSapp, ← hkτ, T.symm_apply_apply]
    exact hk
  have hcS := (hComm S).1 (hS0 S (hTrans _ _ (hsmTile γ hγ) (hTsymm T hT)) τ₀ (subset_closure hτ₀) hSτ₀)
  have hcT' := (hComm T).1 hcT
  have hγT : ∀ σ, γ • σ = T (S σ) := fun σ => (T.apply_symm_apply (γ • σ)).symm
  calc Φ (γ • τ) = Φ (T (S τ)) := by rw [hγT τ]
    _ = T (Φ (S τ)) := hcT' (S τ)
    _ = T (S (Φ τ)) := by rw [hcS τ]
    _ = γ • Φ τ := (hγT (Φ τ)).symm

end LiZhongQC
