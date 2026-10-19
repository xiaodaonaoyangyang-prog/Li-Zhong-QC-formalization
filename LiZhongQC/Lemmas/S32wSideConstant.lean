import LiZhongQC.Lemmas.S32wSideDichotomy

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

universe u

/-- Near a point of the axis `Re (a • τ) = 0` there are points on both sides. -/
theorem s32w_near_sides (a : Matrix.SpecialLinearGroup (Fin 2) ℝ) {q : UpperHalfPlane}
    (hq : ((a • q : UpperHalfPlane) : ℂ).re = 0) {W : Set UpperHalfPlane} (hW : W ∈ 𝓝 q) :
    (∃ τ ∈ W, 0 < ((a • τ : UpperHalfPlane) : ℂ).re) ∧ (∃ τ ∈ W, ((a • τ : UpperHalfPlane) : ℂ).re < 0) := by
  obtain ⟨T, hT0, hTc, hRT⟩ : ∃ T : ℝ → UpperHalfPlane, T 0 = q ∧ Continuous T ∧
      ∀ s, ((a • T s : UpperHalfPlane) : ℂ).re = s := by
    refine ⟨fun s => a⁻¹ • (⟨((a • q : UpperHalfPlane) : ℂ) + (s : ℂ), by simpa using (a • q).im_pos⟩ :
      UpperHalfPlane), ?_, ?_, ?_⟩
    · apply MulAction.injective a
      apply UpperHalfPlane.ext
      simp
    · refine continuous_const_smul a⁻¹ |>.comp ?_
      refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
      exact continuous_const.add Complex.continuous_ofReal
    · intro s
      simp only [smul_inv_smul]
      have h0 : (a • q).re = 0 := hq
      simp [h0]
  have hTW : ∀ᶠ s in 𝓝 (0 : ℝ), T s ∈ W := by
    refine hTc.continuousAt.eventually ?_
    rw [hT0]; exact hW
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1 hTW
  refine ⟨⟨T (ε / 2), hεW (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith), ?_⟩,
    ⟨T (-(ε / 2)), hεW (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith), ?_⟩⟩
  · rw [hRT]; exact half_pos hε
  · rw [hRT]; linarith [half_pos hε]

/-- The axis `{τ | Re (a • τ) = 0}` is preconnected. -/
theorem s32w_seam_connected (a : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsPreconnected {τ : UpperHalfPlane | ((a • τ : UpperHalfPlane) : ℂ).re = 0} := by
  have hrange : {τ : UpperHalfPlane | ((a • τ : UpperHalfPlane) : ℂ).re = 0} =
      range (fun y : Set.Ioi (0 : ℝ) => a⁻¹ • (⟨(y : ℝ) * Complex.I, by simp; exact y.2⟩ : UpperHalfPlane)) := by
    ext τ
    constructor
    · intro hτ
      have h0 : ((a • τ : UpperHalfPlane) : ℂ).re = 0 := hτ
      refine ⟨⟨((a • τ : UpperHalfPlane) : ℂ).im, (a • τ).im_pos⟩, ?_⟩
      apply MulAction.injective a
      apply UpperHalfPlane.ext
      simp only [smul_inv_smul]
      have h0' : (a • τ).re = 0 := h0
      apply Complex.ext <;> simp [h0']
    · rintro ⟨y, rfl⟩
      show ((a • a⁻¹ • (⟨(y : ℝ) * Complex.I, _⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ).re = 0
      simp
  rw [hrange]
  haveI : ConnectedSpace (Set.Ioi (0 : ℝ)) := Subtype.connectedSpace isConnected_Ioi
  refine isPreconnected_range ?_
  refine continuous_const_smul a⁻¹ |>.comp ?_
  refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
  exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const

/-- **L4c.**  The side of the seam lying over `ιd(S)` is the same along the whole lifted seam. -/
theorem s32w_side_constant {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P)
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ')
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ))
    (a : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ)) :
    (∀ q, Jt q = q → ∃ W : Set UpperHalfPlane, IsOpen W ∧ q ∈ W ∧
        (∀ τ ∈ W, 0 < ((a • τ : UpperHalfPlane) : ℂ).re → P τ ∈ range ιd) ∧
        (∀ τ ∈ W, ((a • τ : UpperHalfPlane) : ℂ).re < 0 → P τ ∈ range (J ∘ ιd))) ∨
    (∀ q, Jt q = q → ∃ W : Set UpperHalfPlane, IsOpen W ∧ q ∈ W ∧
        (∀ τ ∈ W, 0 < ((a • τ : UpperHalfPlane) : ℂ).re → P τ ∈ range (J ∘ ιd)) ∧
        (∀ τ ∈ W, ((a • τ : UpperHalfPlane) : ℂ).re < 0 → P τ ∈ range ιd)) := by
  set L : Set UpperHalfPlane := {τ | ((a • τ : UpperHalfPlane) : ℂ).re = 0} with hL
  have hLfix : ∀ τ, τ ∈ L ↔ Jt τ = τ := fun τ => (s32w_fix_iff ha τ).symm
  set Ul : Set UpperHalfPlane := {τ | ∃ W : Set UpperHalfPlane, IsOpen W ∧ τ ∈ W ∧
        (∀ τ' ∈ W, 0 < ((a • τ' : UpperHalfPlane) : ℂ).re → P τ' ∈ range ιd) ∧
        (∀ τ' ∈ W, ((a • τ' : UpperHalfPlane) : ℂ).re < 0 → P τ' ∈ range (J ∘ ιd))} with hUl
  set Ur : Set UpperHalfPlane := {τ | ∃ W : Set UpperHalfPlane, IsOpen W ∧ τ ∈ W ∧
        (∀ τ' ∈ W, 0 < ((a • τ' : UpperHalfPlane) : ℂ).re → P τ' ∈ range (J ∘ ιd)) ∧
        (∀ τ' ∈ W, ((a • τ' : UpperHalfPlane) : ℂ).re < 0 → P τ' ∈ range ιd)} with hUr
  have hUlo : IsOpen Ul := by
    refine isOpen_iff_mem_nhds.2 fun τ hτ => ?_
    obtain ⟨W, hWo, hτW, h1, h2⟩ := hτ
    exact Filter.mem_of_superset (hWo.mem_nhds hτW) fun τ' hτ' => ⟨W, hWo, hτ', h1, h2⟩
  have hUro : IsOpen Ur := by
    refine isOpen_iff_mem_nhds.2 fun τ hτ => ?_
    obtain ⟨W, hWo, hτW, h1, h2⟩ := hτ
    exact Filter.mem_of_superset (hWo.mem_nhds hτW) fun τ' hτ' => ⟨W, hWo, hτ', h1, h2⟩
  have hcov : L ⊆ Ul ∪ Ur := by
    intro q hq
    obtain ⟨W, hWo, hqW, h⟩ := s32w_side_dichotomy F hd hΓ hfree hP hfib hlift a ha q ((hLfix q).1 hq)
    rcases h with h | h
    · exact Or.inl ⟨W, hWo, hqW, h⟩
    · exact Or.inr ⟨W, hWo, hqW, h⟩
  have hdisj : ∀ q ∈ L, q ∈ Ul → q ∈ Ur → False := by
    rintro q hq ⟨W₁, hW₁o, hqW₁, h11, h12⟩ ⟨W₂, hW₂o, hqW₂, h21, h22⟩
    obtain ⟨⟨τ, hτW, hτpos⟩, -⟩ := s32w_near_sides a hq ((hW₁o.inter hW₂o).mem_nhds ⟨hqW₁, hqW₂⟩)
    have h1 := h11 τ hτW.1 hτpos
    have h2 := h21 τ hτW.2 hτpos
    exact (Set.disjoint_left.1 hd.disjoint) h1 (by simpa [Function.comp] using h2)
  have hpre := s32w_seam_connected a
  by_cases hLne : L.Nonempty
  · by_cases hl : ∃ q ∈ L, q ∈ Ul
    · left
      -- `L ⊆ Ul`
      have hsub : L ⊆ Ul := by
        by_contra hnot
        rw [Set.not_subset] at hnot
        obtain ⟨q', hq'L, hq'⟩ := hnot
        have hq'r : q' ∈ Ur := (hcov hq'L).resolve_left hq'
        obtain ⟨q, hqL, hql⟩ := hl
        obtain ⟨z, hz⟩ := hpre Ul Ur hUlo hUro hcov ⟨q, hqL, hql⟩ ⟨q', hq'L, hq'r⟩
        exact hdisj z hz.1 hz.2.1 hz.2.2
      intro q hq
      obtain ⟨W, hWo, hqW, h1, h2⟩ := hsub ((hLfix q).2 hq)
      exact ⟨W, hWo, hqW, h1, h2⟩
    · right
      push_neg at hl
      intro q hq
      have := (hcov ((hLfix q).2 hq)).resolve_left (hl q ((hLfix q).2 hq))
      obtain ⟨W, hWo, hqW, h1, h2⟩ := this
      exact ⟨W, hWo, hqW, h1, h2⟩
  · left
    intro q hq
    exact absurd ⟨q, (hLfix q).2 hq⟩ hLne

end LiZhongQC
