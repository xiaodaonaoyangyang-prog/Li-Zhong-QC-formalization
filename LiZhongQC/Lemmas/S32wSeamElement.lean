import LiZhongQC.Lemmas.S32wReflectionForm

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- An element of `SL(2,ℝ)` acting trivially on `ℍ` is `±1`. -/
theorem s32w_smul_trivial (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : ∀ w : UpperHalfPlane, g • w = w) :
    g = 1 ∨ g = -1 := by
  obtain ⟨e1, e2⟩ := s32w_stab_I g (h UpperHalfPlane.I)
  have h2 : ((g • (⟨2 * Complex.I, by simp⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = 2 * Complex.I :=
    congrArg (fun u : UpperHalfPlane => (u : ℂ)) (h ⟨2 * Complex.I, by simp⟩)
  rw [h36t_coe_smul] at h2
  have hden : ((g 1 0 : ℂ) * (2 * Complex.I) + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) (⟨2 * Complex.I, by simp⟩ : UpperHalfPlane)
    simpa [UpperHalfPlane.denom] using this
  change ((g 0 0 : ℂ) * (2 * Complex.I) + g 0 1) / ((g 1 0 : ℂ) * (2 * Complex.I) + g 1 1) = 2 * Complex.I at h2
  rw [div_eq_iff hden] at h2
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp at hre him
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  have hβ : g 0 1 = 0 := by
    linarith
  have hα : g 0 0 ^ 2 = 1 := by
    rw [e1, e2, hβ] at hdet
    nlinarith
  have hα' : g 0 0 = 1 ∨ g 0 0 = -1 := by
    have : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hα' with h' | h'
  · left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h', e1, e2, hβ]
  · right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h', e1, e2, hβ]

/-- Two elements of `SL(2,ℝ)` with the same action on `ℍ` are equal up to sign. -/
theorem s32w_smul_eq (g k : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : ∀ w : UpperHalfPlane, g • w = k • w) :
    g = k ∨ g = -k := by
  have h1 : k⁻¹ * g = 1 ∨ k⁻¹ * g = -1 := by
    apply s32w_smul_trivial
    intro w
    rw [mul_smul, h w, ← mul_smul, inv_mul_cancel, one_smul]
  rcases h1 with h1 | h1
  · left
    calc g = k * (k⁻¹ * g) := by group
      _ = k := by rw [h1, mul_one]
  · right
    calc g = k * (k⁻¹ * g) := by group
      _ = -k := by rw [h1]; simp

/-- **Diagonal form.**  If a non-trivial element `δ` of a freely acting group commutes with the
anti-holomorphic reflection `J̃ = a⁻¹ c a`, then `a δ a⁻¹` is a diagonal matrix with `|λ| ≠ 1`. -/
theorem s32w_commute_diag (Jt : UpperHalfPlane ≃ₜ UpperHalfPlane) (a δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : ∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ))
    (hcomm : ∀ τ, Jt (δ • τ) = δ • Jt τ)
    (hfree : ∀ τ : UpperHalfPlane, δ • τ = τ → δ = 1 ∨ δ = -1)
    (hnt : ¬ ∀ τ : UpperHalfPlane, δ • τ = τ) :
    (a * δ * a⁻¹) 0 1 = 0 ∧ (a * δ * a⁻¹) 1 0 = 0 ∧ |(a * δ * a⁻¹) 0 0| ≠ 1 := by
  obtain ⟨c, hc⟩ := s32w_refl_exists
  obtain ⟨σ, hσ⟩ := s32w_sigma_exists
  set M := a * δ * a⁻¹ with hM
  have hJc : ∀ τ, a • Jt τ = c (a • τ) := by
    intro τ
    apply UpperHalfPlane.ext
    rw [ha, hc]
  have hcc : ∀ τ, c (c τ) = τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [hc, hc]
    simp
  -- `M` commutes with `c`
  have hMc : ∀ w : UpperHalfPlane, c (M • w) = M • c w := by
    intro w
    have e1 : a • (a⁻¹ • w) = w := by simp
    have e2 : a • (δ • (a⁻¹ • w)) = M • w := by rw [hM]; simp [mul_smul]
    have h1 := hJc (a⁻¹ • w)
    rw [e1] at h1
    have h2 := hJc (δ • a⁻¹ • w)
    rw [e2, hcomm] at h2
    calc c (M • w) = a • δ • Jt (a⁻¹ • w) := h2.symm
      _ = M • (a • Jt (a⁻¹ • w)) := by rw [hM]; simp [mul_smul]
      _ = M • c w := by rw [h1]
  have hσM : ∀ v : UpperHalfPlane, σ M • v = M • v := by
    intro v
    have h1 := hMc (c v)
    rw [s32w_refl_smul c hc σ hσ, hcc] at h1
    exact h1
  have hMw : ∀ w : UpperHalfPlane, M • w = w → δ • (a⁻¹ • w) = a⁻¹ • w := by
    intro w hw
    have : δ • (a⁻¹ • w) = a⁻¹ • (M • w) := by rw [hM]; simp [mul_smul]
    rw [this, hw]
  have hdetM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rwa [Matrix.det_fin_two] at h
  have htriv : (δ = 1 ∨ δ = -1) → False := by
    intro h
    apply hnt
    intro τ
    rcases h with h | h
    · rw [h, one_smul]
    · rw [h]
      apply UpperHalfPlane.ext
      rw [h36t_coe_smul]
      simp [Matrix.SpecialLinearGroup.coe_neg]
  obtain ⟨s00, s01, s10, s11⟩ := hσ M
  rcases s32w_smul_eq _ _ hσM with h | h
  · -- `σ M = M`: off-diagonal entries vanish
    have h01 : M 0 1 = 0 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 0 1) h
      simp only [s01] at this
      linarith
    have h10 : M 1 0 = 0 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 1 0) h
      simp only [s10] at this
      linarith
    refine ⟨h01, h10, fun habs => ?_⟩
    rw [h01, h10] at hdetM
    have hp : M 0 0 = 1 ∨ M 0 0 = -1 := by
      rcases abs_eq (zero_le_one' ℝ) |>.mp habs with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    have hp0 : M 0 0 ≠ 0 := by rcases hp with h' | h' <;> rw [h'] <;> norm_num
    have hp1 : M 1 1 = M 0 0 := by
      rcases hp with h' | h' <;> rw [h'] at hdetM ⊢ <;> linarith
    have hfixw : ∀ w : UpperHalfPlane, M • w = w := by
      intro w
      apply UpperHalfPlane.ext
      rw [h36t_coe_smul, h01, h10, hp1]
      push_cast
      have : ((M 0 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp0
      rw [add_zero, zero_mul, zero_add]
      exact mul_div_cancel_left₀ _ this
    exact htriv (hfree _ (hMw UpperHalfPlane.I (hfixw _)))
  · -- `σ M = -M`: `M` swaps `0` and `∞`, so it fixes a point
    exfalso
    have h00 : M 0 0 = 0 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 0 0) h
      simp only [s00, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at this
      linarith
    have h11 : M 1 1 = 0 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 1 1) h
      simp only [s11, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at this
      linarith
    rw [h00, h11] at hdetM
    have hq : M 0 1 ≠ 0 := by
      intro h0
      rw [h0] at hdetM
      norm_num at hdetM
    set v : UpperHalfPlane := ⟨(|M 0 1| : ℝ) * Complex.I, by simpa using abs_pos.mpr hq⟩ with hv
    have hfixv : M • v = v := by
      apply UpperHalfPlane.ext
      rw [h36t_coe_smul, h00, h11]
      simp only [hv]
      have hqC : ((M 0 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
      have hrC : ((M 1 0 : ℝ) : ℂ) = -((M 0 1 : ℝ) : ℂ)⁻¹ := by
        have : M 1 0 = -(M 0 1)⁻¹ := by field_simp; linarith
        rw [this]; push_cast; ring
      have habs : ((|M 0 1| : ℝ) : ℂ) ^ 2 = ((M 0 1 : ℝ) : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
      have habsC : ((|M 0 1| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hq
      push_cast
      simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero]
      rw [hrC]
      have hden : (-((M 0 1 : ℝ) : ℂ)⁻¹) * (((|M 0 1| : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        apply mul_ne_zero
        · simpa using hqC
        · exact mul_ne_zero habsC Complex.I_ne_zero
      rw [div_eq_iff hden]
      have key : ((|M 0 1| : ℝ) : ℂ) * Complex.I * ((-((M 0 1 : ℝ) : ℂ)⁻¹) * (((|M 0 1| : ℝ) : ℂ) * Complex.I))
          = ((|M 0 1| : ℝ) : ℂ) ^ 2 * ((M 0 1 : ℝ) : ℂ)⁻¹ := by
        linear_combination (-(((|M 0 1| : ℝ) : ℂ) ^ 2 * ((M 0 1 : ℝ) : ℂ)⁻¹)) * Complex.I_sq
      rw [key, habs]
      field_simp
    exact htriv (hfree _ (hMw _ hfixv))

/-- A compact set of the quotient is covered by the image of a compact set of `ℍ`. -/
theorem s32w_compact_lift {D : Type*} [TopologicalSpace D] {p : UpperHalfPlane → D} (hcov : IsCoveringMap p)
    (hsurj : Function.Surjective p) {K : Set D} (hK : IsCompact K) :
    ∃ Ω : Set UpperHalfPlane, IsCompact Ω ∧ ∀ x ∈ K, ∃ ω ∈ Ω, p ω = x := by
  have hopen : IsOpenMap p := hcov.isLocalHomeomorph.isOpenMap
  have hW : ∀ x : D, ∃ W : Set UpperHalfPlane, IsCompact W ∧ W ∈ 𝓝 (Classical.choose (hsurj x)) :=
    fun x => exists_compact_mem_nhds _
  choose W hWc hWn using hW
  have hU : ∀ x ∈ K, p '' W x ∈ 𝓝 x := by
    intro x _
    have h1 := hopen.image_mem_nhds (hWn x)
    rwa [Classical.choose_spec (hsurj x)] at h1
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => p '' W x) hU
  refine ⟨⋃ x ∈ t, W x, t.finite_toSet.isCompact_biUnion fun x _ => hWc x, fun x hx => ?_⟩
  have := hcover hx
  simp only [mem_iUnion] at this
  obtain ⟨y, hy, ω, hω, rfl⟩ := this
  exact ⟨ω, mem_iUnion₂.mpr ⟨y, hy, hω⟩, rfl⟩

/-- **L2.**  Let `ℍ → D` be a uniformization by a free Fuchsian group and let `J̃` be an anti-holomorphic
lift to `ℍ` of a self-map `Jd` of `D` with compact fixed set, `J̃` having a fixed point.  Then `J̃ = a⁻¹ c a`
is a reflection, and some non-trivial deck transformation `δ` commutes with `J̃` and is diagonal
hyperbolic in the coordinate `a`: it translates along the geodesic `Fix J̃ = a⁻¹(iℝ₊)`. -/
theorem s32w_seam_element {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → D}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {Jd : D ≃ₜ D} (hKc : IsCompact {x | Jd x = x})
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, p (Jt τ) = Jd (p τ))
    (hanti : DifferentiableOn ℂ (fun z => conj (liftToC Jt z)) upperHalf)
    {τ₀ : UpperHalfPlane} (hfix : Jt τ₀ = τ₀) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ τ : UpperHalfPlane, ((a • Jt τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ)) ∧
      ∃ δ ∈ Γ, (∀ τ, Jt (δ • τ) = δ • Jt τ) ∧ (¬ ∀ τ : UpperHalfPlane, δ • τ = τ) ∧
        (a * δ * a⁻¹) 0 1 = 0 ∧ (a * δ * a⁻¹) 1 0 = 0 ∧ |(a * δ * a⁻¹) 0 0| ≠ 1 := by
  obtain ⟨a, ha⟩ := s32w_reflection_form Jt hanti hfix
  refine ⟨a, ha, ?_⟩
  obtain ⟨c, hc⟩ := s32w_refl_exists
  -- the geodesic `Fix J̃`
  obtain ⟨y, hy0, hyge⟩ : ∃ y : ℕ → ℝ, (∀ n, 0 < y n) ∧ ∀ n : ℕ, (n : ℝ) + 1 ≤ y n :=
    ⟨fun n => Real.exp n, fun n => Real.exp_pos _, fun n => Real.add_one_le_exp _⟩
  obtain ⟨L, hLa⟩ : ∃ L : ℕ → UpperHalfPlane, ∀ n, ((a • L n : UpperHalfPlane) : ℂ) = (y n : ℝ) * Complex.I :=
    ⟨fun n => a⁻¹ • (⟨(y n : ℝ) * Complex.I, by simpa using hy0 n⟩ : UpperHalfPlane),
      fun n => by simp⟩
  have hLfix : ∀ n, Jt (L n) = L n := by
    intro n
    apply (MulAction.injective a)
    apply UpperHalfPlane.ext
    rw [ha, hLa]
    simp
  -- deck normaliser
  have hdeck : ∀ γ ∈ Γ, ∃ κ ∈ Γ, ∀ τ, Jt (γ • τ) = κ • Jt τ :=
    fun γ hγ => h23l_deck (f := Jd) hp hp (fun τ => hlift τ) hγ
  choose! κ hκΓ hκ using hdeck
  -- a compact set of lifts of the fixed set
  obtain ⟨Ω, hΩc, hΩ⟩ := s32w_compact_lift hp.1 hp.2.2.1 hKc
  have hex : ∀ n : ℕ, ∃ γ ∈ Γ, ∃ ω ∈ Ω, γ • L n = ω := by
    intro n
    have hpK : p (L n) ∈ {x | Jd x = x} := by
      show Jd (p (L n)) = p (L n)
      rw [← hlift, hLfix]
    obtain ⟨ω, hωΩ, hω⟩ := hΩ _ hpK
    obtain ⟨γ, hγ, hγω⟩ := (hp.2.2.2 (L n) ω).1 hω.symm
    exact ⟨γ, hγ, ω, hωΩ, hγω⟩
  choose γ hγΓ ω hωΩ hγL using hex
  set ε : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun n => γ n * κ (γ n)⁻¹ with hεdef
  have hεΓ : ∀ n, ε n ∈ Γ := fun n => Γ.mul_mem (hγΓ n) (hκΓ _ (Γ.inv_mem (hγΓ n)))
  have hε : ∀ n τ, ε n • Jt τ = γ n • Jt ((γ n)⁻¹ • τ) := by
    intro n τ
    rw [hεdef, mul_smul, hκ _ (Γ.inv_mem (hγΓ n))]
  have hεfix : ∀ n, ε n • Jt (ω n) = ω n := by
    intro n
    rw [hε, ← hγL n, inv_smul_smul, hLfix]
  -- finiteness
  have hCc : IsCompact (Ω ∪ Jt '' Ω) := hΩc.union (hΩc.image Jt.continuous)
  have hfin := hΓ _ hCc
  have hmem : ∀ n, ε n ∈ {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty} := by
    intro n
    refine ⟨hεΓ n, ε n • Jt (ω n), ⟨Jt (ω n), Or.inr ⟨ω n, hωΩ n, rfl⟩, rfl⟩, ?_⟩
    rw [hεfix]
    exact Or.inl (hωΩ n)
  haveI : Finite {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty} := hfin.to_subtype
  obtain ⟨e₀, he₀⟩ := Finite.exists_infinite_fiber (fun n : ℕ => (⟨ε n, hmem n⟩ :
    {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty}))
  set N : Set ℕ := (fun n : ℕ => (⟨ε n, hmem n⟩ :
    {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty})) ⁻¹' {e₀} with hN
  have hNinf : N.Infinite := Set.infinite_coe_iff.mp he₀
  have hNε : ∀ n ∈ N, ∀ m ∈ N, ε n = ε m := by
    intro n hn m hm
    have h1 : (⟨ε n, hmem n⟩ : {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty}) = e₀ := hn
    have h2 : (⟨ε m, hmem m⟩ : {g ∈ Γ | ((g • ·) '' (Ω ∪ Jt '' Ω) ∩ (Ω ∪ Jt '' Ω)).Nonempty}) = e₀ := hm
    exact congrArg Subtype.val (h1.trans h2.symm)
  -- two indices with different actions
  obtain ⟨n, hn, m, hm, hnm⟩ : ∃ n ∈ N, ∃ m ∈ N, ¬ ∀ τ : UpperHalfPlane, γ n • τ = γ m • τ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n₀, hn₀⟩ := hNinf.nonempty
    have hQc : IsCompact ((fun q : UpperHalfPlane => (a • (γ n₀)⁻¹ • q)) '' Ω) :=
      hΩc.image (by
        have : Continuous fun q : UpperHalfPlane => (γ n₀)⁻¹ • q := continuous_const_smul _
        exact (continuous_const_smul a).comp this)
    obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn (f := UpperHalfPlane.im)
      UpperHalfPlane.continuous_im.continuousOn
    obtain ⟨k, hk, hkgt⟩ := hNinf.exists_gt ⌈B⌉₊
    have h1 : (γ n₀)⁻¹ • ω k = L k := by
      rw [← hγL k, hcon k hk n₀ hn₀, inv_smul_smul]
    have h2 := hB (a • (γ n₀)⁻¹ • ω k) ⟨ω k, hωΩ k, rfl⟩
    rw [h1] at h2
    have him : UpperHalfPlane.im (a • L k) = y k := by
      have := congrArg Complex.im (hLa k)
      simpa using this
    rw [him, Real.norm_of_nonneg (hy0 k).le] at h2
    have h3 := hyge k
    have h4 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    have h5 : (⌈B⌉₊ : ℝ) < k := by exact_mod_cast hkgt
    linarith
  have hδΓ : (γ n)⁻¹ * γ m ∈ Γ := Γ.mul_mem (Γ.inv_mem (hγΓ n)) (hγΓ m)
  have hεnm : ∀ τ, γ n • Jt ((γ n)⁻¹ • τ) = γ m • Jt ((γ m)⁻¹ • τ) := by
    intro τ
    rw [← hε, ← hε, hNε n hn m hm]
  have hδcomm : ∀ τ, Jt (((γ n)⁻¹ * γ m) • τ) = ((γ n)⁻¹ * γ m) • Jt τ := by
    intro τ'
    have h := hεnm (γ m • τ')
    rw [inv_smul_smul, ← mul_smul] at h
    calc Jt (((γ n)⁻¹ * γ m) • τ') = (γ n)⁻¹ • (γ n • Jt (((γ n)⁻¹ * γ m) • τ')) := by
          rw [inv_smul_smul]
      _ = (γ n)⁻¹ • γ m • Jt τ' := by rw [h]
      _ = ((γ n)⁻¹ * γ m) • Jt τ' := by rw [mul_smul]
  have hnt : ¬ ∀ τ : UpperHalfPlane, ((γ n)⁻¹ * γ m) • τ = τ := by
    intro h
    apply hnm
    intro τ
    have h1 := congrArg (fun u => γ n • u) (h τ)
    simp only [mul_smul, smul_inv_smul] at h1
    exact h1.symm
  obtain ⟨d1, d2, d3⟩ := s32w_commute_diag Jt a _ ha hδcomm (hfree _ hδΓ) hnt
  exact ⟨_, hδΓ, hδcomm, hnt, d1, d2, d3⟩

end LiZhongQC
