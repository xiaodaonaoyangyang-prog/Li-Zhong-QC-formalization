import LiZhongQC.Ch07.S27_TeichmullerExistence

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- A holomorphic homeomorphism of `ℍ` is a Möbius transformation. -/
theorem s32w_hol_bij_smul (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hF : DifferentiableOn ℂ (liftToC F) upperHalf) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F τ = m • τ := by
  have hconf : IsConformalOnto (liftToC F) upperHalf upperHalf := by
    refine ⟨hF, ?_, ?_⟩
    · intro z hz w hw hzw
      have h1 := h23l_liftToC_eq F hz
      have h2 := h23l_liftToC_eq F hw
      rw [h1, h2] at hzw
      have := F.injective (UpperHalfPlane.ext hzw)
      have h3 := congrArg (fun u : UpperHalfPlane => (u : ℂ)) this
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz),
        UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < w.im from hw)] using h3
    · ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [h23l_liftToC_eq F hz]
        exact (F _).im_pos
      · intro hw
        have hw' : 0 < w.im := hw
        refine ⟨((F.symm ⟨w, hw'⟩ : UpperHalfPlane) : ℂ), (F.symm ⟨w, hw'⟩).im_pos, ?_⟩
        rw [h23l_liftToC_eq F (F.symm ⟨w, hw'⟩).im_pos]
        simp
  exact utm_eq_smul_of_isKQC_one F (isKQC_one_of_conformal isOpen_upperHalf hconf)

/-- The reflection `τ ↦ -conj τ` as a homeomorphism of `ℍ`. -/
theorem s32w_refl_exists : ∃ c : UpperHalfPlane ≃ₜ UpperHalfPlane, ∀ τ, ((c τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ) := by
  have hpos : ∀ τ : UpperHalfPlane, 0 < (-conj (τ : ℂ)).im := by
    intro τ
    simpa using τ.im_pos
  have hcont : Continuous fun τ : UpperHalfPlane => (⟨-conj (τ : ℂ), hpos τ⟩ : UpperHalfPlane) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
      ((Complex.continuous_conj.comp UpperHalfPlane.continuous_coe).neg)
  refine ⟨⟨⟨fun τ => ⟨-conj (τ : ℂ), hpos τ⟩, fun τ => ⟨-conj (τ : ℂ), hpos τ⟩, ?_, ?_⟩, hcont, hcont⟩,
    fun τ => rfl⟩
  · intro τ
    apply UpperHalfPlane.ext
    simp
  · intro τ
    apply UpperHalfPlane.ext
    simp

/-- Conjugation by `diag(1,-1)` as a monoid homomorphism of `SL(2,ℝ)`. -/
theorem s32w_sigma_exists : ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ g, σ g 0 0 = g 0 0 ∧ σ g 0 1 = -g 0 1 ∧ σ g 1 0 = -g 1 0 ∧ σ g 1 1 = g 1 1 := by
  have hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (!![g 0 0, -g 0 1; -g 1 0, g 1 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    intro g
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨{ toFun := fun g => ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], hdet g⟩
            map_one' := ?_
            map_mul' := ?_ }, fun g => ⟨rfl, rfl, rfl, rfl⟩⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  · intro g h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (_ : ℝ) = ((!![g 0 0, -g 0 1; -g 1 0, g 1 1] * !![h 0 0, -h 0 1; -h 1 0, h 1 1] :
      Matrix (Fin 2) (Fin 2) ℝ) i j)
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The reflection intertwines `g` with `σ g`. -/
theorem s32w_refl_smul (c : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hc : ∀ τ, ((c τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hσ : ∀ g, σ g 0 0 = g 0 0 ∧ σ g 0 1 = -g 0 1 ∧ σ g 1 0 = -g 1 0 ∧ σ g 1 1 = g 1 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    c (g • τ) = σ g • c τ := by
  apply UpperHalfPlane.ext
  obtain ⟨h00, h01, h10, h11⟩ := hσ g
  rw [hc, h36t_coe_smul, h36t_coe_smul, hc, h00, h01, h10, h11]
  have hden : ((g 1 0 : ℂ) * τ + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom] using this
  have hden'' : (g 1 0 : ℂ) * conj (τ : ℂ) + g 1 1 ≠ 0 := by
    intro h
    apply hden
    have := congrArg conj h
    simpa using this
  have hden' : (-(g 1 0 : ℂ)) * (-conj (τ : ℂ)) + g 1 1 ≠ 0 := by
    have : (-(g 1 0 : ℂ)) * (-conj (τ : ℂ)) + g 1 1 = (g 1 0 : ℂ) * conj (τ : ℂ) + g 1 1 := by ring
    rw [this]; exact hden''
  push_cast
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal]
  rw [← neg_div, div_eq_div_iff hden'' hden']
  ring

/-- Rotations in `SL(2,ℝ)`. -/
theorem s32w_rot_exists (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    ∃ r : Matrix.SpecialLinearGroup (Fin 2) ℝ, r 0 0 = α ∧ r 0 1 = β ∧ r 1 0 = -β ∧ r 1 1 = α := by
  refine ⟨⟨!![α, β; -β, α], ?_⟩, rfl, rfl, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  nlinarith

/-- An element of `SL(2,ℝ)` fixing `i` is a rotation. -/
theorem s32w_stab_I (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : m • UpperHalfPlane.I = UpperHalfPlane.I) :
    m 1 1 = m 0 0 ∧ m 1 0 = -m 0 1 := by
  have h1 := congrArg (fun u : UpperHalfPlane => (u : ℂ)) h
  simp only [h36t_coe_smul, UpperHalfPlane.coe_I] at h1
  have hden : ((m 1 0 : ℂ) * Complex.I + m 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (m : GL (Fin 2) ℝ) UpperHalfPlane.I
    simpa [UpperHalfPlane.denom] using this
  rw [div_eq_iff hden] at h1
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp at hre him
  constructor <;> linarith

/-- Normalisation: every point of `ℍ` is moved to `i` by an element of `SL(2,ℝ)`. -/
theorem s32w_move_to_I (τ : UpperHalfPlane) :
    ∃ b : Matrix.SpecialLinearGroup (Fin 2) ℝ, b • τ = UpperHalfPlane.I := by
  have hy : 0 < τ.im := τ.im_pos
  have hs : 0 < Real.sqrt τ.im := Real.sqrt_pos.mpr hy
  have hss : Real.sqrt τ.im * Real.sqrt τ.im = τ.im := Real.mul_self_sqrt hy.le
  have hdet : (!![(Real.sqrt τ.im)⁻¹, -τ.re * (Real.sqrt τ.im)⁻¹; 0, Real.sqrt τ.im] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, inv_mul_cancel₀ hs.ne']
  obtain ⟨b, h00, h01, h10, h11⟩ : ∃ b : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      b 0 0 = (Real.sqrt τ.im)⁻¹ ∧ b 0 1 = -τ.re * (Real.sqrt τ.im)⁻¹ ∧ b 1 0 = 0 ∧ b 1 1 = Real.sqrt τ.im :=
    ⟨⟨_, hdet⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨b, ?_⟩
  apply UpperHalfPlane.ext
  rw [h36t_coe_smul, h00, h01, h10, h11]
  simp only [UpperHalfPlane.coe_I]
  have hsC : ((Real.sqrt τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hssC : ((Real.sqrt τ.im : ℝ) : ℂ) * (Real.sqrt τ.im : ℝ) = (τ.im : ℂ) := by exact_mod_cast hss
  have hyC : (τ.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hτ : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  push_cast
  rw [hτ, div_eq_iff (by simpa using hsC)]
  field_simp
  rw [← hssC]
  ring

/-- **L1.** An anti-holomorphic self-homeomorphism of `ℍ` with a fixed point is conjugate in
`PSL(2,ℝ)` to the reflection `τ ↦ -conj τ`. -/
theorem s32w_reflection_form (J : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hanti : DifferentiableOn ℂ (fun z => conj (liftToC J z)) upperHalf)
    {τ₀ : UpperHalfPlane} (hfix : J τ₀ = τ₀) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ : UpperHalfPlane,
      ((a • J τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ) := by
  obtain ⟨c, hc⟩ := s32w_refl_exists
  obtain ⟨σ, hσ⟩ := s32w_sigma_exists
  have hcc : ∀ τ, c (c τ) = τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [hc, hc]
    simp
  -- `J ∘ c` is holomorphic
  have hhol : DifferentiableOn ℂ (liftToC (c.trans J)) upperHalf := by
    have key : ∀ z ∈ upperHalf, liftToC (c.trans J) z = conj ((fun u => conj (liftToC J (-u))) (conj z)) := by
      intro z hz
      have hz' : 0 < z.im := hz
      have hpos : 0 < (-conj z).im := by simpa using hz'
      simp only [liftToC, hz', hpos, dif_pos, Complex.conj_conj, Complex.neg_re, map_neg]
      simp only [Homeomorph.trans_apply]
      congr 2
      apply UpperHalfPlane.ext
      simp [hc]
    refine DifferentiableOn.congr (f := fun z => conj ((fun u => conj (liftToC J (-u))) (conj z))) ?_ key
    intro z hz
    have hz' : 0 < z.im := hz
    have hpos : (-conj z) ∈ upperHalf := by
      show 0 < (-conj z).im
      simpa using hz'
    have h1 : DifferentiableAt ℂ (fun u => conj (liftToC J u)) (-conj z) :=
      (hanti _ hpos).differentiableAt (isOpen_upperHalf.mem_nhds hpos)
    have h2 : DifferentiableAt ℂ (fun u => conj (liftToC J (-u))) (conj z) := by
      have := h1.comp (conj z) (differentiableAt_id.neg)
      simpa [Function.comp_def] using this
    exact (differentiableAt_conj_conj_iff.mpr h2).differentiableWithinAt
  obtain ⟨m, hm⟩ := s32w_hol_bij_smul _ hhol
  have hJ : ∀ τ, J τ = m • c τ := by
    intro τ
    have := hm (c τ)
    simp only [Homeomorph.trans_apply, hcc] at this
    exact this
  obtain ⟨b, hb⟩ := s32w_move_to_I τ₀
  -- m' = b m σ(b⁻¹) fixes i
  set m' := b * m * σ b⁻¹ with hm'
  have hcI : c UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [hc]
    simp
  have hbinv : b⁻¹ • UpperHalfPlane.I = τ₀ := by
    rw [← hb]; simp
  have hm'I : m' • UpperHalfPlane.I = UpperHalfPlane.I := by
    have h1 : σ b⁻¹ • UpperHalfPlane.I = c τ₀ := by
      have := s32w_refl_smul c hc σ hσ b⁻¹ UpperHalfPlane.I
      rw [hcI, hbinv] at this
      exact this.symm
    rw [hm', mul_smul, mul_smul, h1, ← hJ, hfix, hb]
  obtain ⟨e1, e2⟩ := s32w_stab_I m' hm'I
  have hdet' : m' 0 0 * m' 1 1 - m' 0 1 * m' 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe m'
    rwa [Matrix.det_fin_two] at h
  have hαβ : m' 0 0 ^ 2 + m' 0 1 ^ 2 = 1 := by
    rw [e1, e2] at hdet'
    nlinarith
  obtain ⟨φ, hα, hβ⟩ : ∃ φ : ℝ, m' 0 0 = Real.cos (2 * φ) ∧ m' 0 1 = Real.sin (2 * φ) := by
    set x : ℂ := ⟨m' 0 0, m' 0 1⟩ with hx
    have hn2 : ‖x‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hx]
      nlinarith
    have hn : ‖x‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn2
    have h1 := Complex.norm_mul_cos_arg x
    have h2 := Complex.norm_mul_sin_arg x
    rw [hn, one_mul] at h1 h2
    refine ⟨Complex.arg x / 2, ?_, ?_⟩ <;> rw [show 2 * (Complex.arg x / 2) = Complex.arg x by ring]
    · simpa [hx] using h1.symm
    · simpa [hx] using h2.symm
  have hcs : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq φ
  obtain ⟨r, r00, r01, r10, r11⟩ := s32w_rot_exists (Real.cos φ) (-Real.sin φ) (by nlinarith)
  have hrm : r * m' = σ r := by
    apply Matrix.SpecialLinearGroup.ext
    obtain ⟨s00, s01, s10, s11⟩ := hσ r
    have hc2 : m' 0 0 = 2 * Real.cos φ ^ 2 - 1 := by rw [hα, Real.cos_two_mul]
    have hs2 : m' 0 1 = 2 * Real.sin φ * Real.cos φ := by rw [hβ, Real.sin_two_mul]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, r00, r01, r10, r11, s00, s01, s10, s11, e1, e2, hc2, hs2] <;>
      first
        | ring1
        | linear_combination (2 * Real.cos φ) * hcs
        | linear_combination (-2 * Real.cos φ) * hcs
        | linear_combination (2 * Real.sin φ) * hcs
        | linear_combination (-2 * Real.sin φ) * hcs
  have hbm : b * m = m' * σ b := by
    rw [hm', mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have ham : (r * b) * m = σ (r * b) := by
    rw [mul_assoc, hbm, ← mul_assoc, hrm, map_mul]
  refine ⟨r * b, fun τ => ?_⟩
  rw [hJ, ← mul_smul, ham, ← s32w_refl_smul c hc σ hσ, hc]

end LiZhongQC
