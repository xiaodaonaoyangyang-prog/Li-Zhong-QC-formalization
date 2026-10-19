import LiZhongQC.Lemmas.S32wReflectionsAgree
import LiZhongQC.Lemmas.S32wSeamCoordinate

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

universe u

/-- The fixed set of a reflection-form lift is the imaginary axis in the coordinate `a`. -/
theorem s32w_fix_iff {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} {a : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ))
    (τ : UpperHalfPlane) : Jt τ = τ ↔ ((a • τ : UpperHalfPlane) : ℂ).re = 0 := by
  constructor
  · intro h
    have h1 := ha τ
    rw [h] at h1
    have := congrArg Complex.re h1
    simp at this
    show (a • τ).re = 0
    linarith
  · intro h
    have h' : (a • τ).re = 0 := h
    apply MulAction.injective a
    apply UpperHalfPlane.ext
    rw [ha]
    apply Complex.ext <;> simp [h']

/-- Near a point where `P` is a local homeomorphism with `P ∘ Jt = J ∘ P`, `P τ = P (Jt τ)` forces `Jt τ = τ`. -/
theorem s32w_local_fix {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Y} (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ')
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} {q : UpperHalfPlane} (hq : Jt q = q) :
    ∀ᶠ τ in 𝓝 q, P (Jt τ) = P τ → Jt τ = τ := by
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds q
  have hC : IsCompact (K ∪ Jt '' K) := hKc.union (hKc.image Jt.continuous)
  have hE := hΓ _ hC
  have hall : ∀ᶠ τ in 𝓝 q, ∀ γ ∈ {γ ∈ Γ | ((γ • ·) '' (K ∪ Jt '' K) ∩ (K ∪ Jt '' K)).Nonempty},
      (γ • q ≠ q → γ • τ ≠ Jt τ) := by
    refine (Filter.eventually_all_finite hE).2 fun γ _ => ?_
    by_cases hγ : γ • q = q
    · exact Eventually.of_forall fun τ h => absurd hγ h
    · have hopen : IsOpen {τ : UpperHalfPlane | γ • τ ≠ Jt τ} :=
        isOpen_ne_fun (continuous_const_smul γ) Jt.continuous
      have hqm : q ∈ {τ : UpperHalfPlane | γ • τ ≠ Jt τ} := by
        show γ • q ≠ Jt q
        rw [hq]; exact hγ
      filter_upwards [hopen.mem_nhds hqm] with τ hτ _ using hτ
  filter_upwards [hKn, hall] with τ hτK hτ hP
  obtain ⟨γ, hγΓ, hγτ⟩ := hfib τ (Jt τ) hP.symm
  have hγE : γ ∈ {γ ∈ Γ | ((γ • ·) '' (K ∪ Jt '' K) ∩ (K ∪ Jt '' K)).Nonempty} := by
    refine ⟨hγΓ, Jt τ, ⟨τ, Or.inl hτK, hγτ⟩, Or.inr ⟨τ, hτK, rfl⟩⟩
  by_cases hγq : γ • q = q
  · rcases hfree γ hγΓ q hγq with h | h
    · rw [h, one_smul] at hγτ
      exact hγτ.symm
    · rw [h] at hγτ
      have : (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) • τ = (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ :=
        s32w_neg_smul 1 τ
      rw [this, one_smul] at hγτ
      exact hγτ.symm
  · exact absurd hγτ (hτ γ hγE hγq)

/-- **L4b.**  Near a point `q` of the lifted seam, one side of the seam lies over `ιd(S)` and the other over
`J(ιd(S))`. -/
theorem s32w_side_dichotomy {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {P : UpperHalfPlane → Xd.carrier} (hP : IsLocalHomeomorph P)
    (hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ')
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ))
    (a : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ))
    (q : UpperHalfPlane) (hq : Jt q = q) :
    ∃ W : Set UpperHalfPlane, IsOpen W ∧ q ∈ W ∧
      (((∀ τ ∈ W, 0 < ((a • τ : UpperHalfPlane) : ℂ).re → P τ ∈ range ιd) ∧
          (∀ τ ∈ W, ((a • τ : UpperHalfPlane) : ℂ).re < 0 → P τ ∈ range (J ∘ ιd))) ∨
        ((∀ τ ∈ W, 0 < ((a • τ : UpperHalfPlane) : ℂ).re → P τ ∈ range (J ∘ ιd)) ∧
          (∀ τ ∈ W, ((a • τ : UpperHalfPlane) : ℂ).re < 0 → P τ ∈ range ιd))) := by
  have hxJ : J (P q) = P q := by rw [← hlift, hq]
  obtain ⟨κ, r, hr, hsrc, hκ0, heq, hup, hlow, hreal, -, -⟩ := s32w_seam_coordinate F hd hxJ
  obtain ⟨e, hqe, hPe⟩ := hP q
  have hxe : P q ∈ e.target := by rw [hPe]; exact e.map_source hqe
  have hVev := s32w_local_fix (Jt := Jt) hΓ hfree hfib hq
  -- the local chart `g = e.symm ∘ κ`
  set gmap : ℂ → UpperHalfPlane := fun z => e.symm (κ z) with hg
  have hκc : ContinuousAt κ 0 := κ.continuousAt (hsrc (mem_ball_self hr))
  have hκt : ∀ᶠ z in 𝓝 (0 : ℂ), κ z ∈ e.target := by
    refine hκc.eventually (e.open_target.mem_nhds ?_)
    rw [hκ0]; exact hxe
  have hgc : ContinuousAt gmap 0 := by
    refine (e.continuousAt_symm ?_).comp hκc
    rw [hκ0]; exact hxe
  have hg0 : gmap 0 = q := by
    show e.symm (κ 0) = q
    rw [hκ0, hPe]
    exact e.left_inv hqe
  have hVn : ∀ᶠ z in 𝓝 (0 : ℂ), gmap z ∈ {τ | P (Jt τ) = P τ → Jt τ = τ} := by
    refine hgc.eventually ?_
    rw [hg0]
    exact hVev
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.1 (hκt.and hVn)
  set ρ := min ρ₀ r with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hr
  have hball : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := ball_subset_ball (min_le_right _ _)
  have hballρ₀ : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) ρ₀ := ball_subset_ball (min_le_left _ _)
  have hκtρ : ∀ z ∈ ball (0 : ℂ) ρ, κ z ∈ e.target := fun z hz => (hρ₀sub (hballρ₀ hz)).1
  have hVρ : ∀ z ∈ ball (0 : ℂ) ρ, P (Jt (gmap z)) = P (gmap z) → Jt (gmap z) = gmap z :=
    fun z hz => (hρ₀sub (hballρ₀ hz)).2
  have hPg : ∀ z ∈ ball (0 : ℂ) ρ, P (gmap z) = κ z := fun z hz => by
    show P (e.symm (κ z)) = κ z
    rw [hPe]
    exact e.right_inv (hκtρ z hz)
  -- the neighbourhood `W`
  set W : Set UpperHalfPlane := gmap '' ball (0 : ℂ) ρ with hW
  have hWo : IsOpen W := by
    have h1 : IsOpen (κ '' ball (0 : ℂ) ρ) :=
      κ.isOpen_image_of_subset_source isOpen_ball (fun z hz => hsrc (hball hz))
    have h2 : κ '' ball (0 : ℂ) ρ ⊆ e.symm.source := by
      rintro _ ⟨z, hz, rfl⟩
      exact hκtρ z hz
    have h3 := e.symm.isOpen_image_of_subset_source h1 h2
    have h4 : W = e.symm '' (κ '' ball (0 : ℂ) ρ) := by
      rw [hW]; exact (Set.image_image _ _ _).symm
    rw [h4]
    exact h3
  have hqW : q ∈ W := ⟨0, mem_ball_self hρ, hg0⟩
  refine ⟨W, hWo, hqW, ?_⟩
  -- representation of points of `W`
  have hrep : ∀ τ ∈ W, ∃ z ∈ ball (0 : ℂ) ρ, P τ = κ z := by
    rintro τ ⟨z, hz, rfl⟩
    exact ⟨z, hz, hPg z hz⟩
  -- the two halves of `W`
  set Cp : Set UpperHalfPlane := gmap '' (ball (0 : ℂ) ρ ∩ {z | 0 < z.im}) with hCp
  set Cm : Set UpperHalfPlane := gmap '' (ball (0 : ℂ) ρ ∩ {z | z.im < 0}) with hCm
  have hgcont : ContinuousOn gmap (ball (0 : ℂ) ρ) := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    refine (e.continuousAt_symm (hκtρ z hz)).comp ?_
    exact κ.continuousAt (hsrc (hball hz))
  have hCpc : IsPreconnected Cp :=
    (((convex_ball (0 : ℂ) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected).image gmap
      (hgcont.mono inter_subset_left)
  have hCmc : IsPreconnected Cm :=
    (((convex_ball (0 : ℂ) ρ).inter (convex_halfSpace_im_lt 0)).isPreconnected).image gmap
      (hgcont.mono inter_subset_left)
  -- the value of `Re (a • ·)`
  obtain ⟨Rf, hRf⟩ : ∃ Rf : UpperHalfPlane → ℝ, ∀ τ, Rf τ = ((a • τ : UpperHalfPlane) : ℂ).re :=
    ⟨fun τ => ((a • τ : UpperHalfPlane) : ℂ).re, fun _ => rfl⟩
  have hRfc : Continuous Rf := by
    have : Continuous fun τ : UpperHalfPlane => ((a • τ : UpperHalfPlane) : ℂ) :=
      UpperHalfPlane.continuous_coe.comp (continuous_const_smul a)
    have h2 := Complex.continuous_re.comp this
    have : Rf = fun τ => ((a • τ : UpperHalfPlane) : ℂ).re := funext hRf
    rw [this]
    exact h2
  -- points of `W` off the seam lie in `Cp ∪ Cm`
  have hoff : ∀ τ ∈ W, Rf τ ≠ 0 → τ ∈ Cp ∨ τ ∈ Cm := by
    rintro τ ⟨z, hz, rfl⟩ hne
    have hzim : z.im ≠ 0 := by
      intro hzi
      apply hne
      have hJx : J (κ z) = κ z := hreal z (hball hz) hzi
      have hP1 : P (Jt (gmap z)) = P (gmap z) := by
        rw [hlift, hPg z hz]; exact hJx
      rw [hRf]
      exact (s32w_fix_iff ha _).1 (hVρ z hz hP1)
    rcases lt_or_gt_of_ne hzim with h | h
    · exact Or.inr ⟨z, ⟨hz, h⟩, rfl⟩
    · exact Or.inl ⟨z, ⟨hz, h⟩, rfl⟩
  -- `Cp` and `Cm` avoid the seam
  have hoffC : ∀ z ∈ ball (0 : ℂ) ρ, z.im ≠ 0 → Rf (gmap z) ≠ 0 := by
    intro z hz hzi h0
    rw [hRf] at h0
    have hfx := (s32w_fix_iff ha _).2 h0
    have h1 : J (κ z) = κ z := by rw [← hPg z hz, ← hlift, hfx]
    obtain ⟨hcb, hκc⟩ := heq z (hball hz)
    rw [← hκc] at h1
    have := κ.injOn (hsrc hcb) (hsrc (hball hz)) h1
    have him := congrArg Complex.im this
    rw [Complex.conj_im] at him
    apply hzi
    linarith
  have hsideC : ∀ C : Set UpperHalfPlane, IsPreconnected C → (∀ τ ∈ C, Rf τ ≠ 0) →
      (∀ τ ∈ C, 0 < Rf τ) ∨ (∀ τ ∈ C, Rf τ < 0) := by
    intro C hC hne
    have h := (hC.image Rf hRfc.continuousOn).subset_or_subset (isOpen_Ioi (a := (0 : ℝ)))
      (isOpen_Iio (a := (0 : ℝ))) (Set.disjoint_left.2 fun x h1 h2 => lt_asymm (show 0 < x from h1) (show x < 0 from h2)) (by
        rintro _ ⟨τ, hτ, rfl⟩
        rcases lt_or_gt_of_ne (hne τ hτ) with h' | h'
        · exact Or.inr h'
        · exact Or.inl h')
    rcases h with h | h
    · exact Or.inl fun τ hτ => h ⟨τ, hτ, rfl⟩
    · exact Or.inr fun τ hτ => h ⟨τ, hτ, rfl⟩
  have hsideP := hsideC Cp hCpc (by rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩; exact hoffC z hz (ne_of_gt hzi))
  have hsideM := hsideC Cm hCmc (by rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩; exact hoffC z hz (ne_of_lt hzi))
  have hPCp : ∀ τ ∈ Cp, P τ ∈ range ιd := by
    rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩
    rw [hPg z hz]
    exact hup z (hball hz) hzi
  have hPCm : ∀ τ ∈ Cm, P τ ∈ range (J ∘ ιd) := by
    rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩
    rw [hPg z hz]
    exact hlow z (hball hz) hzi
  -- `W` meets both sides of the seam
  have hRq : Rf q = 0 := by rw [hRf]; exact (s32w_fix_iff ha q).1 hq
  obtain ⟨T, hT0, hTc, hRT⟩ : ∃ T : ℝ → UpperHalfPlane, T 0 = q ∧ Continuous T ∧ ∀ s, Rf (T s) = s := by
    have hpos : ∀ s : ℝ, 0 < ((a • q : UpperHalfPlane) : ℂ).im := fun s => (a • q).im_pos
    refine ⟨fun s => a⁻¹ • (⟨((a • q : UpperHalfPlane) : ℂ) + (s : ℂ), by simpa using (a • q).im_pos⟩ :
      UpperHalfPlane), ?_, ?_, ?_⟩
    · apply MulAction.injective a
      apply UpperHalfPlane.ext
      simp
    · refine continuous_const_smul a⁻¹ |>.comp ?_
      refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
      exact continuous_const.add Complex.continuous_ofReal
    · intro s
      rw [hRf]
      simp only [smul_inv_smul]
      have h0 : (a • q).re = 0 := by have h5 := hRq; rw [hRf] at h5; exact h5
      simp [h0]
  have hTW : ∀ᶠ s in 𝓝 (0 : ℝ), T s ∈ W := by
    refine hTc.continuousAt.eventually (hWo.mem_nhds ?_)
    rw [hT0]; exact hqW
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1 hTW
  have hTp : T (ε / 2) ∈ W := hεW (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
  have hTm : T (-(ε / 2)) ∈ W := hεW (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith)
  have hRp : 0 < Rf (T (ε / 2)) := by rw [hRT]; exact half_pos hε
  have hRm : Rf (T (-(ε / 2))) < 0 := by rw [hRT]; linarith [half_pos hε]
  -- conclude
  have hret : ∀ τ, (0 < ((a • τ : UpperHalfPlane) : ℂ).re ↔ 0 < Rf τ) := fun τ => by rw [hRf]
  have hret' : ∀ τ, (((a • τ : UpperHalfPlane) : ℂ).re < 0 ↔ Rf τ < 0) := fun τ => by rw [hRf]
  rcases hsideP with hP' | hP' <;> rcases hsideM with hM' | hM'
  · -- both halves on the positive side: `T(-ε/2)` is nowhere
    exfalso
    rcases hoff _ hTm hRm.ne with h | h
    · exact absurd (hP' _ h) (not_lt.2 hRm.le)
    · exact absurd (hM' _ h) (not_lt.2 hRm.le)
  · left
    refine ⟨fun τ hτ hpos => ?_, fun τ hτ hneg => ?_⟩
    · rw [hret] at hpos
      rcases hoff τ hτ hpos.ne' with h | h
      · exact hPCp τ h
      · exact absurd (hM' τ h) (not_lt.2 hpos.le)
    · rw [hret'] at hneg
      rcases hoff τ hτ hneg.ne with h | h
      · exact absurd (hP' τ h) (not_lt.2 hneg.le)
      · exact hPCm τ h
  · right
    refine ⟨fun τ hτ hpos => ?_, fun τ hτ hneg => ?_⟩
    · rw [hret] at hpos
      rcases hoff τ hτ hpos.ne' with h | h
      · exact absurd (hP' τ h) (not_lt.2 hpos.le)
      · exact hPCm τ h
    · rw [hret'] at hneg
      rcases hoff τ hτ hneg.ne with h | h
      · exact hPCp τ h
      · exact absurd (hM' τ h) (not_lt.2 hneg.le)
  · exfalso
    rcases hoff _ hTp hRp.ne' with h | h
    · exact absurd (hP' _ h) (not_lt.2 hRp.le)
    · exact absurd (hM' _ h) (not_lt.2 hRp.le)

end LiZhongQC
