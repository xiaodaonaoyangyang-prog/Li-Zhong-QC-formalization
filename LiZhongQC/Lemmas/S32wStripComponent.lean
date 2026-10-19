import LiZhongQC.Lemmas.S32wSideConstant
import LiZhongQC.Lemmas.S32wHalfDeckAgree
import LiZhongQC.Lemmas.S32wHalvesSelfmap

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Pointwise ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- A diagonal element of `SL(2,ℝ)` acts on `ℍ` by multiplication with the positive number `a²`. -/
theorem s32w_diag_smul_coe (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h01 : M 0 1 = 0) (h10 : M 1 0 = 0)
    (z : UpperHalfPlane) : ((M • z : UpperHalfPlane) : ℂ) = (((M 0 0) ^ 2 : ℝ) : ℂ) * (z : ℂ) := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rw [Matrix.det_fin_two, h01, h10] at h
    linarith
  have ha0 : M 0 0 ≠ 0 := by intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  have hd : M 1 1 = (M 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  rw [h36t_coe_smul, h01, h10, hd]
  have haC : ((M 0 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  push_cast
  field_simp
  ring

/-- The half-ball (in the coordinate `a`) on the side `s` of the imaginary axis is preconnected. -/
theorem s32w_halfball_preconnected (a : Matrix.SpecialLinearGroup (Fin 2) ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (c : ℂ) {r : ℝ} (hr : r ≤ c.im) :
    IsPreconnected {τ : UpperHalfPlane | ‖((a • τ : UpperHalfPlane) : ℂ) - c‖ < r ∧
      0 < s * ((a • τ : UpperHalfPlane) : ℂ).re} := by
  set K : Set ℂ := Metric.ball c r ∩ {z : ℂ | 0 < s * z.re} with hK
  have hKc : Convex ℝ K := by
    refine (convex_ball c r).inter ?_
    rcases hs with rfl | rfl
    · simpa using convex_halfSpace_re_gt (0 : ℝ)
    · simpa [neg_pos] using convex_halfSpace_re_lt (0 : ℝ)
  have hKr : K ⊆ range ((↑) : UpperHalfPlane → ℂ) := by
    intro z hz
    have h1 : ‖z - c‖ < r := by simpa [dist_eq_norm] using hz.1
    have h2 : |z.im - c.im| ≤ ‖z - c‖ := by
      have := Complex.abs_im_le_norm (z - c)
      simpa using this
    have h3 : 0 < z.im := by
      have := (abs_le.1 h2).1
      linarith
    exact ⟨⟨z, h3⟩, rfl⟩
  have hE : IsPreconnected (((↑) : UpperHalfPlane → ℂ) ⁻¹' K) := by
    rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset hKr]
    exact hKc.isPreconnected
  have := ((Homeomorph.smul a).isPreconnected_preimage (s := ((↑) : UpperHalfPlane → ℂ) ⁻¹' K)).2 hE
  convert this using 1
  ext τ
  simp [hK, dist_eq_norm]

/-- **(b3a)** The seam element of a lifted reflection preserves every maximal preconnected piece `C` of the lifted
half whose closure meets the seam line. -/
theorem s32w_stab_of_seam_element {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P)
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ') (hinv : ∀ γ ∈ Γ, ∀ τ, P (γ • τ) = P τ)
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ))
    (a : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ))
    {C : Set UpperHalfPlane} (hCconn : IsPreconnected C) (hCQ : ∀ τ ∈ C, P τ ∈ range ιd)
    (hCmax : ∀ D : Set UpperHalfPlane, IsPreconnected D → (∀ τ ∈ D, P τ ∈ range ιd) →
      (D ∩ C).Nonempty → D ⊆ C)
    {q' : UpperHalfPlane} (hq' : q' ∈ closure C) (hfix' : Jt q' = q')
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδΓ : δ ∈ Γ)
    (hd1 : (a * δ * a⁻¹) 0 1 = 0) (hd2 : (a * δ * a⁻¹) 1 0 = 0) :
    δ • C = C := by
  classical
  -- the coordinate `w = a • ·`
  obtain ⟨w, hw⟩ : ∃ w : UpperHalfPlane → ℂ, ∀ τ, w τ = ((a • τ : UpperHalfPlane) : ℂ) := ⟨_, fun _ => rfl⟩
  have hwc : Continuous w := by
    have : w = fun τ => ((a • τ : UpperHalfPlane) : ℂ) := funext hw
    rw [this]
    exact UpperHalfPlane.continuous_coe.comp (continuous_const_smul a)
  have hwim : ∀ τ, 0 < (w τ).im := fun τ => by rw [hw]; exact (a • τ).im_pos
  have hwinj : ∀ τ τ', w τ = w τ' → τ = τ' := fun τ τ' h => by
    rw [hw, hw] at h
    exact MulAction.injective a (UpperHalfPlane.ext h)
  have hfixiff : ∀ τ, Jt τ = τ ↔ (w τ).re = 0 := fun τ => by rw [hw]; exact s32w_fix_iff ha τ
  have hFixOff : ∀ x : Xd.carrier, J x = x → x ∉ range ιd := by
    intro x hx hxr
    have hmem : x ∈ {x | J x = x} := hx
    rw [hd.fixed_curves, hd.embedding.isOpen_range.frontier_eq] at hmem
    exact hmem.1.2 hxr
  have hQL : ∀ τ, Jt τ = τ → P τ ∉ range ιd := fun τ hτ => hFixOff _ (by rw [← hlift, hτ])
  -- the side of the seam lying over `ιd(S)`
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
  -- the multiplier of `δ` in the coordinate `a`
  have hMdiag := s32w_diag_smul_coe (a * δ * a⁻¹) hd1 hd2
  have hδw : ∀ τ, w (δ • τ) = (((a * δ * a⁻¹) 0 0 ^ 2 : ℝ) : ℂ) * w τ := by
    intro τ
    rw [hw, hw, show a • δ • τ = (a * δ * a⁻¹) • a • τ by simp [mul_smul]]
    exact hMdiag _
  obtain ⟨p2, hp2def⟩ : ∃ p2 : ℝ, p2 = (a * δ * a⁻¹) 0 0 ^ 2 := ⟨_, rfl⟩
  rw [← hp2def] at hδw
  have hp2 : 0 < p2 := by
    have hdet : (a * δ * a⁻¹) 0 0 * (a * δ * a⁻¹) 1 1 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe (a * δ * a⁻¹)
      rw [Matrix.det_fin_two, hd1, hd2] at h
      linarith
    have : (a * δ * a⁻¹) 0 0 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
    rw [hp2def]; positivity
  have hδre : ∀ τ, (w (δ • τ)).re = p2 * (w τ).re := fun τ => by
    rw [hδw]; simp [Complex.re_ofReal_mul]
  have hδdist : ∀ τ τ', ‖w (δ • τ) - w (δ • τ')‖ = p2 * ‖w τ - w τ'‖ := fun τ τ' => by
    rw [hδw, hδw, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp2.le]
  have hδinv : ∀ τ, P (δ • τ) = P τ := fun τ => hinv δ hδΓ τ
  have hballo : ∀ (τ : UpperHalfPlane) (r : ℝ), 0 < r →
      {τ'' : UpperHalfPlane | ‖w τ'' - w τ‖ < r} ∈ 𝓝 τ := fun τ r hr =>
    (isOpen_lt (continuous_norm.comp (hwc.sub continuous_const)) continuous_const).mem_nhds
      (by simpa using hr)
  -- local half-balls at seam points
  have hlocal : ∀ q, Jt q = q → ∃ r, 0 < r ∧ r ≤ (w q).im ∧
      {τ | ‖w τ - w q‖ < r ∧ 0 < s * (w τ).re} ⊆ {τ | P τ ∈ range ιd} ∧
      (∀ τ, ‖w τ - w q‖ < r → P τ ∈ range ιd → 0 < s * (w τ).re) := by
    intro q hq
    obtain ⟨W, hWo, hqW, h1, h2⟩ := hloc q hq
    have himg : IsOpen (w '' W) := by
      have : w '' W = ((↑) : UpperHalfPlane → ℂ) '' ((a • ·) '' W) := by
        rw [Set.image_image]; ext z; simp [hw]
      rw [this]
      exact UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ((Homeomorph.smul a).isOpenMap _ hWo)
    obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 himg (w q) ⟨q, hqW, rfl⟩
    have hsub : ∀ τ, ‖w τ - w q‖ < min r₀ (w q).im → τ ∈ W := by
      intro τ hτ
      have hmem : w τ ∈ ball (w q) r₀ := by
        rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hτ (min_le_left _ _)
      obtain ⟨τ', hτ'W, hτ'⟩ := hball hmem
      exact (hwinj _ _ hτ') ▸ hτ'W
    refine ⟨min r₀ (w q).im, lt_min hr₀ (hwim q), min_le_right _ _, ?_, ?_⟩
    · intro τ hτ
      exact h1 τ (hsub τ hτ.1) hτ.2
    · intro τ hτ hPτ
      have hτW := hsub τ hτ
      by_contra hneg
      push_neg at hneg
      rcases hneg.lt_or_eq with hlt | heq
      · exact (Set.disjoint_left.1 hd.disjoint) hPτ (h2 τ hτW hlt)
      · have hre : (w τ).re = 0 := by
          rcases mul_eq_zero.1 heq with h | h
          · exact absurd h hs0
          · exact h
        exact hQL τ ((hfixiff τ).2 hre) hPτ
  -- points of the A-side near a seam point
  have hAside : ∀ q, Jt q = q → ∀ r : ℝ, 0 < r → ∃ τ, ‖w τ - w q‖ < r ∧ 0 < s * (w τ).re := by
    intro q hq r hr
    have hq0 : ((a • q : UpperHalfPlane) : ℂ).re = 0 := by rw [← hw]; exact (hfixiff q).1 hq
    obtain ⟨⟨τ₁, h1, h1'⟩, ⟨τ₂, h2, h2'⟩⟩ := s32w_near_sides a hq0 (hballo q r hr)
    rcases hs with rfl | rfl
    · exact ⟨τ₁, h1, by rw [hw]; simpa using h1'⟩
    · exact ⟨τ₂, h2, by rw [hw]; simpa using h2'⟩
  -- Good and Bad points
  have hopen : ∀ R : UpperHalfPlane → Prop,
      IsOpen {τ : UpperHalfPlane | ∃ r > 0, ∀ τ', ‖w τ' - w τ‖ < r → 0 < s * (w τ').re → R τ'} := by
    intro R
    refine isOpen_iff_mem_nhds.2 fun τ hτ => ?_
    obtain ⟨r, hr, h⟩ := hτ
    filter_upwards [hballo τ (r / 2) (half_pos hr)] with τ'' hτ''
    refine ⟨r / 2, half_pos hr, fun τ' h1 h2 => h τ' ?_ h2⟩
    calc ‖w τ' - w τ‖ ≤ ‖w τ' - w τ''‖ + ‖w τ'' - w τ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < r / 2 + r / 2 := add_lt_add h1 hτ''
      _ = r := by ring
  have hU₁o := hopen (fun τ' => τ' ∈ C)
  have hU₂o := hopen (fun τ' => τ' ∉ C)
  -- on the seam each point is Good or Bad
  have hdich : ∀ q, Jt q = q → (∃ r > 0, ∀ τ', ‖w τ' - w q‖ < r → 0 < s * (w τ').re → τ' ∈ C) ∨
      (∃ r > 0, ∀ τ', ‖w τ' - w q‖ < r → 0 < s * (w τ').re → τ' ∉ C) := by
    intro q hq
    obtain ⟨r, hr, hrim, hbQ, -⟩ := hlocal q hq
    have hpre' : IsPreconnected {τ : UpperHalfPlane | ‖w τ - w q‖ < r ∧ 0 < s * (w τ).re} := by
      have e : {τ : UpperHalfPlane | ‖w τ - w q‖ < r ∧ 0 < s * (w τ).re} =
          {τ : UpperHalfPlane | ‖((a • τ : UpperHalfPlane) : ℂ) - w q‖ < r ∧
            0 < s * ((a • τ : UpperHalfPlane) : ℂ).re} := by
        ext τ; simp only [mem_setOf_eq, hw]
      rw [e]
      exact s32w_halfball_preconnected a hs (w q) hrim
    by_cases hne : ({τ : UpperHalfPlane | ‖w τ - w q‖ < r ∧ 0 < s * (w τ).re} ∩ C).Nonempty
    · left
      have hsubC := hCmax _ hpre' hbQ hne
      exact ⟨r, hr, fun τ' h1 h2 => hsubC ⟨h1, h2⟩⟩
    · right
      exact ⟨r, hr, fun τ' h1 h2 hC' => hne ⟨τ', ⟨h1, h2⟩, hC'⟩⟩
  have hnotboth : ∀ q, Jt q = q → (∃ r > 0, ∀ τ', ‖w τ' - w q‖ < r → 0 < s * (w τ').re → τ' ∈ C) →
      (∃ r > 0, ∀ τ', ‖w τ' - w q‖ < r → 0 < s * (w τ').re → τ' ∉ C) → False := by
    rintro q hq ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, h₂⟩
    obtain ⟨τ, hτ1, hτ2⟩ := hAside q hq (min r₁ r₂) (lt_min hr₁ hr₂)
    exact h₂ τ (lt_of_lt_of_le hτ1 (min_le_right _ _)) hτ2
      (h₁ τ (lt_of_lt_of_le hτ1 (min_le_left _ _)) hτ2)
  -- `q'` is Good
  have hq'good : ∃ r > 0, ∀ τ', ‖w τ' - w q'‖ < r → 0 < s * (w τ').re → τ' ∈ C := by
    rcases hdich q' hfix' with h | h
    · exact h
    · exfalso
      obtain ⟨r, hr, hr'⟩ := h
      obtain ⟨r₁, hr₁, hr₁im, hbQ, hside⟩ := hlocal q' hfix'
      obtain ⟨τ₁, hτ₁N, hτ₁C⟩ := mem_closure_iff_nhds.1 hq' _ (hballo q' (min r r₁) (lt_min hr hr₁))
      have hτ₁N' : ‖w τ₁ - w q'‖ < min r r₁ := hτ₁N
      have hpos := hside τ₁ (lt_of_lt_of_le hτ₁N' (min_le_right _ _)) (hCQ τ₁ hτ₁C)
      exact hr' τ₁ (lt_of_lt_of_le hτ₁N' (min_le_left _ _)) hpos hτ₁C
  -- every seam point is Good (connectedness of the seam)
  have hallgood : ∀ q, Jt q = q →
      ∃ r > 0, ∀ τ', ‖w τ' - w q‖ < r → 0 < s * (w τ').re → τ' ∈ C := by
    intro q hq
    rcases hdich q hq with h | h
    · exact h
    · exfalso
      have hconn := s32w_seam_connected a
      have hcov : {τ : UpperHalfPlane | ((a • τ : UpperHalfPlane) : ℂ).re = 0} ⊆
          {τ : UpperHalfPlane | ∃ r > 0, ∀ τ', ‖w τ' - w τ‖ < r → 0 < s * (w τ').re → τ' ∈ C} ∪
          {τ : UpperHalfPlane | ∃ r > 0, ∀ τ', ‖w τ' - w τ‖ < r → 0 < s * (w τ').re → τ' ∉ C} := by
        intro z hz
        exact hdich z ((hfixiff z).2 (by rw [hw]; exact hz))
      obtain ⟨z, hzL, hz1, hz2⟩ := hconn _ _ (hopen (fun τ' => τ' ∈ C)) (hopen (fun τ' => τ' ∉ C)) hcov
        ⟨q', (by show ((a • q' : UpperHalfPlane) : ℂ).re = 0; rw [← hw]; exact (hfixiff q').1 hfix'), hq'good⟩
        ⟨q, (by show ((a • q : UpperHalfPlane) : ℂ).re = 0; rw [← hw]; exact (hfixiff q).1 hq), h⟩
      exact hnotboth z ((hfixiff z).2 (by rw [hw]; exact hzL)) hz1 hz2
  -- `δ` moves a point of `C` near `q'` into `C`
  have hδq' : Jt (δ • q') = δ • q' := by
    rw [hfixiff, hδre, (hfixiff q').1 hfix', mul_zero]
  obtain ⟨r₁, hr₁, h₁⟩ := hallgood q' hfix'
  obtain ⟨r₂, hr₂, h₂⟩ := hallgood (δ • q') hδq'
  obtain ⟨τ, hτ1, hτ2⟩ := hAside q' hfix' (min r₁ (r₂ / p2)) (lt_min hr₁ (div_pos hr₂ hp2))
  have hτC : τ ∈ C := h₁ τ (lt_of_lt_of_le hτ1 (min_le_left _ _)) hτ2
  have hδτC : δ • τ ∈ C := by
    apply h₂
    · rw [hδdist]
      have h3 : ‖w τ - w q'‖ < r₂ / p2 := lt_of_lt_of_le hτ1 (min_le_right _ _)
      calc p2 * ‖w τ - w q'‖ < p2 * (r₂ / p2) := mul_lt_mul_of_pos_left h3 hp2
        _ = r₂ := by field_simp
    · rw [hδre]
      have : s * (p2 * (w τ).re) = p2 * (s * (w τ).re) := by ring
      rw [this]
      exact mul_pos hp2 hτ2
  have hδCpre : IsPreconnected (δ • C) := by
    have := hCconn.image (fun x => δ • x) (continuous_const_smul δ).continuousOn
    rwa [Set.image_smul] at this
  have hδCQ : ∀ τ' ∈ δ • C, P τ' ∈ range ιd := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hδinv]
    exact hCQ y hy
  have hmeet : ((δ • C) ∩ C).Nonempty := ⟨δ • τ, ⟨τ, hτC, rfl⟩, hδτC⟩
  have hsub1 : δ • C ⊆ C := hCmax _ hδCpre hδCQ hmeet
  have hmax2 : ∀ D : Set UpperHalfPlane, IsPreconnected D → (∀ τ ∈ D, P τ ∈ range ιd) →
      (D ∩ δ • C).Nonempty → D ⊆ δ • C := by
    intro D hD hDQ ⟨x, hxD, y, hyC, hyx⟩
    have hpre : IsPreconnected ((fun z => δ⁻¹ • z) '' D) :=
      hD.image _ (continuous_const_smul δ⁻¹).continuousOn
    have hQ' : ∀ τ' ∈ (fun z => δ⁻¹ • z) '' D, P τ' ∈ range ιd := by
      rintro _ ⟨z, hz, rfl⟩
      rw [show P (δ⁻¹ • z) = P z from hinv δ⁻¹ (Γ.inv_mem hδΓ) z]
      exact hDQ z hz
    have hne : ((fun z => δ⁻¹ • z) '' D ∩ C).Nonempty := by
      refine ⟨δ⁻¹ • x, ⟨x, hxD, rfl⟩, ?_⟩
      rw [← hyx, inv_smul_smul]
      exact hyC
    have hsub := hCmax _ hpre hQ' hne
    intro z hz
    have := hsub ⟨z, hz, rfl⟩
    exact ⟨δ⁻¹ • z, this, by simp⟩
  have hsub2 : C ⊆ δ • C := hmax2 C hCconn hCQ ⟨δ • τ, hδτC, ⟨τ, hτC, rfl⟩⟩
  exact Set.Subset.antisymm hsub1 hsub2

/-- The reflection of the double restricts to the punctured double. -/
theorem s32w_restrict_reflection {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    {F : FiniteTypeStructure S g n m} {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd) :
    ∃ Jd : puncturedOpens Pd ≃ₜ puncturedOpens Pd, ∀ y, (Jd y : Xd.carrier) = J y := by
  have hJinv : ∀ x, J (J x) = x := hd.involution.1
  have hJPd : ∀ y : puncturedOpens Pd, J (y : Xd.carrier) ∉ (↑Pd : Set Xd.carrier) := by
    intro y hP
    apply y.2
    have : (y : Xd.carrier) ∈ J '' (↑Pd : Set Xd.carrier) := ⟨_, hP, hJinv _⟩
    rwa [hd.Pd_invariant] at this
  exact ⟨{ toFun := fun y => ⟨J y, hJPd y⟩
           invFun := fun y => ⟨J y, hJPd y⟩
           left_inv := fun y => Subtype.ext (hJinv _)
           right_inv := fun y => Subtype.ext (hJinv _)
           continuous_toFun := Continuous.subtype_mk (J.continuous.comp continuous_subtype_val) _
           continuous_invFun := Continuous.subtype_mk (J.continuous.comp continuous_subtype_val) _ },
    fun _ => rfl⟩

/-- `ℍ → puncturedOpens Pd → Xd` is a holomorphic local homeomorphism with the fibre properties of `p`. -/
theorem s32w_P_facts {Xd : ClosedRS.{u}} {Pd : Finset Xd.carrier}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → puncturedOpens Pd}
    (hp : IsUniformization Γ p) :
    IsLocalHomeomorph (fun τ => ((p τ : puncturedOpens Pd) : Xd.carrier)) ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => ((p τ : puncturedOpens Pd) : Xd.carrier)) ∧
    (∀ τ τ', ((p τ : puncturedOpens Pd) : Xd.carrier) = ((p τ' : puncturedOpens Pd) : Xd.carrier) →
      ∃ γ ∈ Γ, γ • τ = τ') ∧
    (∀ γ ∈ Γ, ∀ τ, ((p (γ • τ) : puncturedOpens Pd) : Xd.carrier) = ((p τ : puncturedOpens Pd) : Xd.carrier)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Topology.IsOpenEmbedding.isLocalHomeomorph
      (puncturedOpens Pd).isOpen.isOpenEmbedding_subtypeVal).comp hp.1.isLocalHomeomorph
  · exact ((contMDiff_subtype_val (n := ω) (U := puncturedOpens Pd)).mdifferentiable (by simp)).comp hp.2.1
  · intro τ τ' h
    exact (hp.2.2.2 τ τ').1 (Subtype.ext h)
  · intro γ hγ τ
    exact congrArg Subtype.val ((hp.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm

/-- **(b3)** The lifts `F`, `G' = γ₁ F'` of two symmetric maps conjugate each boundary reflection `J'` of the lifted half
in the same way. -/
theorem s32w_boundary_reflection_agree {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : IsFuchsian Γ₀) (hfree₀ : ActsFreely Γ₀)
    (hfree₁ : ActsFreely Γ₁)
    {p₀ : UpperHalfPlane → puncturedOpens Pd₀} {p₁ : UpperHalfPlane → puncturedOpens Pd₁}
    (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {fdp fdp' : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁}
    (hfdpJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (fdp y' : Xd₁.carrier) = J₁ (fdp y))
    (hfdpJ' : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (fdp' y' : Xd₁.carrier) = J₁ (fdp' y))
    {F F' : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ fdp F) (hF' : IsLift p₀ p₁ fdp' F')
    {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ₁ : γ₁ ∈ Γ₁)
    {C : Set UpperHalfPlane} (hCconn : IsPreconnected C)
    (hCQ : ∀ τ ∈ C, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀)
    (hCmax : ∀ D : Set UpperHalfPlane, IsPreconnected D →
      (∀ τ ∈ D, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀) → (D ∩ C).Nonempty → D ⊆ C)
    (hconj : ∀ g ∈ Γ₀, g • C = C → ∀ τ, F (g • F.symm τ) = γ₁ • F' (g • F'.symm (γ₁⁻¹ • τ)))
    {J' : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hJ' : ∀ τ, ((p₀ (J' τ) : puncturedOpens Pd₀) : Xd₀.carrier) = J₀ ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier))
    {q' : UpperHalfPlane} (hq' : q' ∈ closure C) (hfix' : J' q' = q') :
    ∀ τ, F (J' (F.symm τ)) = γ₁ • F' (J' (F'.symm (γ₁⁻¹ • τ))) := by
  classical
  obtain ⟨hP₀loc, hP₀hol, hfib₀, hinv₀⟩ := s32w_P_facts hp₀
  obtain ⟨hP₁loc, hP₁hol, hfib₁, hinv₁⟩ := s32w_P_facts hp₁
  obtain ⟨Jd₀, hJd₀⟩ := s32w_restrict_reflection hd₀
  obtain ⟨Jd₁, hJd₁⟩ := s32w_restrict_reflection hd₁
  obtain ⟨hAc, -, hFixc⟩ := s32w_punctured_facts F₀ hd₀
  have hFixDc : IsCompact {y : puncturedOpens Pd₀ | Jd₀ y = y} := by
    have : {y : puncturedOpens Pd₀ | Jd₀ y = y} = {y : puncturedOpens Pd₀ | J₀ (y : Xd₀.carrier) = y} := by
      ext y; simp only [mem_setOf_eq, Subtype.ext_iff, hJd₀]
    rw [this]; exact hFixc
  have hdp : ∀ y, fdp (Jd₀ y) = Jd₁ (fdp y) := fun y =>
    Subtype.ext (by rw [hJd₁, hfdpJ y (Jd₀ y) (hJd₀ y)])
  have hdp' : ∀ y, fdp' (Jd₀ y) = Jd₁ (fdp' y) := fun y =>
    Subtype.ext (by rw [hJd₁, hfdpJ' y (Jd₀ y) (hJd₀ y)])
  have hJ'd : ∀ τ, p₀ (J' τ) = Jd₀ (p₀ τ) := fun τ => Subtype.ext (by rw [hJd₀]; exact hJ' τ)
  have hanti := s32w_lift_antiholo_loc hP₀loc hP₀hol hd₀.involution (Jt := J') hJ'
  obtain ⟨a, ha, δ, hδΓ, hδcomm, hδnt, d1, d2, d3⟩ :=
    s32w_seam_element hΓ₀ hfree₀ hp₀ hFixDc hJ'd hanti hfix'
  have hδC : δ • C = C :=
    s32w_stab_of_seam_element F₀ hd₀ hΓ₀ hfree₀ hP₀loc hfib₀ hinv₀ hJ' a ha hCconn hCQ hCmax hq' hfix' hδΓ d1 d2
  have hc := hconj δ hδΓ hδC
  obtain ⟨δ₁, hδ₁Γ, hδ₁⟩ := h23l_deck hp₀ hp₁ hF hδΓ
  set G' : UpperHalfPlane ≃ₜ UpperHalfPlane := F'.trans (Homeomorph.smul γ₁) with hG'def
  have hG'app : ∀ τ, G' τ = γ₁ • F' τ := fun τ => rfl
  have hG'symm : ∀ σ, G'.symm σ = F'.symm (γ₁⁻¹ • σ) := fun σ => by
    apply G'.injective
    rw [G'.apply_symm_apply, hG'app, F'.apply_symm_apply, smul_inv_smul]
  have hG'δ : ∀ τ, G' (δ • τ) = δ₁ • G' τ := by
    intro τ
    have h1 := hc (G' τ)
    rw [hδ₁ (F.symm (G' τ)), F.apply_symm_apply] at h1
    have h2 : F'.symm (γ₁⁻¹ • G' τ) = τ := by
      rw [hG'app, inv_smul_smul, F'.symm_apply_apply]
    rw [h2] at h1
    exact h1.symm
  have hp₁γ : ∀ γ ∈ Γ₁, ∀ σ, p₁ (γ • σ) = p₁ σ := fun γ hγ σ =>
    ((hp₁.2.2.2 σ (γ • σ)).2 ⟨γ, hγ, rfl⟩).symm
  have hp₁G' : ∀ σ, p₁ (G' σ) = p₁ (F' σ) := fun σ => hp₁γ γ₁ hγ₁ (F' σ)
  -- the conjugated reflections
  set R : UpperHalfPlane ≃ₜ UpperHalfPlane := (F.symm.trans J').trans F with hRdef
  set R' : UpperHalfPlane ≃ₜ UpperHalfPlane := (G'.symm.trans J').trans G' with hR'def
  have hRapp : ∀ σ, R σ = F (J' (F.symm σ)) := fun σ => rfl
  have hR'app : ∀ σ, R' σ = G' (J' (G'.symm σ)) := fun σ => rfl
  have hRlift : ∀ σ, ((p₁ (R σ) : puncturedOpens Pd₁) : Xd₁.carrier) =
      J₁ ((p₁ σ : puncturedOpens Pd₁) : Xd₁.carrier) := by
    intro σ
    rw [hRapp, hF, hJ'd, hdp, ← hJd₁]
    congr 1
    rw [← hF (F.symm σ), F.apply_symm_apply]
  have hR'lift : ∀ σ, ((p₁ (R' σ) : puncturedOpens Pd₁) : Xd₁.carrier) =
      J₁ ((p₁ σ : puncturedOpens Pd₁) : Xd₁.carrier) := by
    intro σ
    rw [hR'app, hp₁G', hF', hJ'd, hdp', ← hJd₁]
    congr 1
    rw [← hF' (G'.symm σ), ← hp₁G', G'.apply_symm_apply]
  have hantiR := s32w_lift_antiholo_loc hP₁loc hP₁hol hd₁.involution (Jt := R) hRlift
  have hantiR' := s32w_lift_antiholo_loc hP₁loc hP₁hol hd₁.involution (Jt := R') hR'lift
  have hRfix : R (F q') = F q' := by rw [hRapp, F.symm_apply_apply, hfix']
  have hR'fix : R' (G' q') = G' q' := by rw [hR'app, G'.symm_apply_apply, hfix']
  obtain ⟨aR, haR⟩ := s32w_reflection_form R hantiR hRfix
  obtain ⟨aR', haR'⟩ := s32w_reflection_form R' hantiR' hR'fix
  have hFsymmδ : ∀ σ, F.symm (δ₁ • σ) = δ • F.symm σ := by
    intro σ
    apply F.injective
    rw [F.apply_symm_apply, hδ₁, F.apply_symm_apply]
  have hG'symmδ : ∀ σ, G'.symm (δ₁ • σ) = δ • G'.symm σ := by
    intro σ
    apply G'.injective
    rw [G'.apply_symm_apply, hG'δ, G'.apply_symm_apply]
  have hRδ : ∀ σ, R (δ₁ • σ) = δ₁ • R σ := by
    intro σ
    rw [hRapp, hRapp, hFsymmδ, hδcomm, hδ₁]
  have hR'δ : ∀ σ, R' (δ₁ • σ) = δ₁ • R' σ := by
    intro σ
    rw [hR'app, hR'app, hG'symmδ, hδcomm, hG'δ]
  have hnt₁ : ¬ ∀ σ : UpperHalfPlane, δ₁ • σ = σ := by
    intro h
    apply hδnt
    intro τ
    have h1 := hδ₁ τ
    rw [h (F τ)] at h1
    exact F.injective h1
  have hagree := s32w_reflections_agree R R' δ₁ (fun σ h => hfree₁ δ₁ hδ₁Γ σ h) hnt₁ hRδ hR'δ
    aR aR' haR haR'
  intro τ
  calc F (J' (F.symm τ)) = R τ := rfl
    _ = R' τ := hagree τ
    _ = G' (J' (G'.symm τ)) := rfl
    _ = γ₁ • F' (J' (F'.symm (γ₁⁻¹ • τ))) := by rw [hG'app, hG'symm]

end LiZhongQC
