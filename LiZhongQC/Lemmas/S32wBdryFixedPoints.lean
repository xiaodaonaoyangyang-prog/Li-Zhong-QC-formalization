import LiZhongQC.Ch07.S27_TeichmullerExistence
import LiZhongQC.Lemmas.LengthSpectrum

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- For a hyperbolic `γ` with `c = 0`: `ad = 1`, `|a| ≠ 1`, and `d - a ≠ 0`. -/
theorem s32w_c0_facts {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    (hc : γ 1 0 = 0) : γ 0 0 * γ 1 1 = 1 ∧ |γ 0 0| ≠ 1 ∧ γ 1 1 - γ 0 0 ≠ 0 := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := hnf_sl2_det γ
    rw [hc, mul_zero, sub_zero] at h
    exact h
  have ha0 : γ 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have hd' : γ 1 1 = (γ 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have ha1 : |γ 0 0| ≠ 1 := by
    intro h1
    have hsq : γ 0 0 ^ 2 = 1 := by
      have := sq_abs (γ 0 0)
      rw [h1] at this
      linarith
    have hdd : γ 1 1 = γ 0 0 := by
      rw [hd']
      field_simp
      linarith
    rw [hdd] at hγ
    have : |γ 0 0 + γ 0 0| = 2 := by
      rw [← two_mul, abs_mul, h1]
      norm_num
    linarith
  refine ⟨hdet, ha1, fun h => ?_⟩
  have hdd : γ 1 1 = γ 0 0 := by linarith
  have hsq : γ 0 0 ^ 2 = 1 := by
    have : γ 0 0 * γ 0 0 = 1 := by rw [hdd] at hdet; exact hdet
    nlinarith
  apply ha1
  have h2 : |γ 0 0| ^ 2 = 1 := by rw [sq_abs]; exact hsq
  nlinarith [abs_nonneg (γ 0 0)]

/-- The forward orbits of a hyperbolic matrix with `c = 0` tend to its attracting fixed point. -/
theorem s32w_forward_attractor_c0 {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : 2 < |γ 0 0 + γ 1 1|) (hc : γ 1 0 = 0) (w : UpperHalfPlane) :
    Tendsto (fun n : ℕ => (((γ ^ n • w : UpperHalfPlane) : ℂ) : ExtPlane))
      atTop (𝓝 (attractingFixedPoint γ)) := by
  obtain ⟨hdet, ha1, hda⟩ := s32w_c0_facts hγ hc
  have hdetC : ((γ 0 0 : ℝ) : ℂ) * (γ 1 1 : ℝ) = 1 := by exact_mod_cast hdet
  have hdaC : ((γ 1 1 : ℝ) : ℂ) - (γ 0 0 : ℝ) ≠ 0 := by exact_mod_cast hda
  set zs : ℂ := ((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) with hzs
  have hzs' : zs * (((γ 1 1 : ℝ) : ℂ) - (γ 0 0 : ℝ)) = (γ 0 1 : ℝ) := by
    rw [hzs]
    push_cast
    exact div_mul_cancel₀ _ hdaC
  have hsmul : ∀ u : UpperHalfPlane,
      ((γ • u : UpperHalfPlane) : ℂ) = ((γ 0 0 : ℝ) : ℂ) ^ 2 * u + (γ 0 0 : ℝ) * (γ 0 1 : ℝ) := by
    intro u
    rw [h36t_coe_smul]
    have hcC : ((γ 1 0 : ℝ) : ℂ) = 0 := by rw [hc]; simp
    show mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u = _
    rw [hcC]
    exact hnf_mobiusFn_of_c_zero hdetC u
  have hfix : ((γ 0 0 : ℝ) : ℂ) ^ 2 * zs + (γ 0 0 : ℝ) * (γ 0 1 : ℝ) = zs := by
    linear_combination (-(((γ 0 0 : ℝ) : ℂ))) * hzs' + zs * hdetC
  have hiter : ∀ n : ℕ, ((γ ^ n • w : UpperHalfPlane) : ℂ) =
      (((γ 0 0 : ℝ) : ℂ) ^ 2) ^ n * ((w : ℂ) - zs) + zs := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, hsmul, ih, pow_succ]
      linear_combination hfix
  rcases lt_or_gt_of_ne ha1 with hlt | hgt
  · -- `|a| < 1`: the attracting point is finite
    rw [attractingFixedPoint, if_pos hc, if_neg (not_lt.2 hlt.le)]
    have hq : ‖((γ 0 0 : ℝ) : ℂ) ^ 2‖ < 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [abs_nonneg (γ 0 0)]
    have h0 := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const ((w : ℂ) - zs)
    rw [zero_mul] at h0
    have h1 : Tendsto (fun n : ℕ => ((γ ^ n • w : UpperHalfPlane) : ℂ)) atTop (𝓝 zs) := by
      have := h0.add_const zs
      rw [zero_add] at this
      exact this.congr fun n => (hiter n).symm
    exact (OnePoint.continuous_coe.tendsto _).comp h1
  · -- `|a| > 1`: the attracting point is `∞`
    rw [attractingFixedPoint, if_pos hc, if_pos hgt]
    have hzsim : zs.im = 0 := by
      rw [hzs]
      exact Complex.ofReal_im _
    have hwpos : 0 < ‖(w : ℂ) - zs‖ := by
      rw [norm_pos_iff]
      intro h
      have := congrArg Complex.im h
      simp only [Complex.sub_im, hzsim, sub_zero, Complex.zero_im] at this
      exact absurd this w.im_pos.ne'
    have hq : 1 < ‖((γ 0 0 : ℝ) : ℂ) ^ 2‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      nlinarith
    have hX : Tendsto (fun n : ℕ => ‖(((γ 0 0 : ℝ) : ℂ) ^ 2) ^ n * ((w : ℂ) - zs)‖) atTop atTop := by
      have := (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hwpos
      refine this.congr fun n => ?_
      rw [norm_mul, norm_pow _ n]
    have hY : Tendsto (fun n : ℕ => ‖(((γ 0 0 : ℝ) : ℂ) ^ 2) ^ n * ((w : ℂ) - zs)‖ + -‖zs‖)
        atTop atTop := tendsto_atTop_add_const_right _ _ hX
    refine s27l_tendsto_extInf (w := fun n : ℕ => ((γ ^ n • w : UpperHalfPlane) : ℂ)) ?_
    refine tendsto_atTop_mono (fun n => ?_) hY
    have h := norm_sub_norm_le (((γ 0 0 : ℝ) : ℂ) ^ 2 ^ n * ((w : ℂ) - zs)) 0
    have e : (((γ 0 0 : ℝ) : ℂ) ^ 2) ^ n * ((w : ℂ) - zs) =
        ((γ ^ n • w : UpperHalfPlane) : ℂ) - zs := by
      rw [hiter n]
      ring
    rw [e]
    have := norm_sub_le (((γ ^ n • w : UpperHalfPlane) : ℂ)) zs
    linarith [norm_nonneg zs]

/-- The forward orbits of a hyperbolic matrix tend to its attracting fixed point. -/
theorem s32w_forward_attractor {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : 2 < |γ 0 0 + γ 1 1|) (w : UpperHalfPlane) :
    Tendsto (fun n : ℕ => (((γ ^ n • w : UpperHalfPlane) : ℂ) : ExtPlane))
      atTop (𝓝 (attractingFixedPoint γ)) := by
  by_cases hc : γ 1 0 = 0
  · exact s32w_forward_attractor_c0 hγ hc w
  · exact s30ls_b3_forward_attractor hγ hc w

/-- The attracting fixed point of `γ⁻¹` is the repelling fixed point of `γ`. -/
theorem s32w_attracting_inv {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|) :
    attractingFixedPoint γ⁻¹ = repellingFixedPoint γ := by
  have e00 : (γ⁻¹) 0 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e01 : (γ⁻¹) 0 1 = -γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e10 : (γ⁻¹) 1 0 = -γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e11 : (γ⁻¹) 1 1 = γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  unfold attractingFixedPoint repellingFixedPoint
  rw [e00, e01, e10, e11]
  by_cases hc : γ 1 0 = 0
  · have hc' : -γ 1 0 = 0 := by rw [hc]; simp
    rw [if_pos hc', if_pos hc]
    obtain ⟨hdet, ha1, hda⟩ := s32w_c0_facts hγ hc
    have hab : |γ 0 0| * |γ 1 1| = 1 := by rw [← abs_mul, hdet]; simp
    have hval : -γ 0 1 / (γ 0 0 - γ 1 1) = γ 0 1 / (γ 1 1 - γ 0 0) := by
      rw [neg_div, ← div_neg, neg_sub]
    rcases lt_or_gt_of_ne ha1 with hlt | hgt
    · have hd1 : 1 < |γ 1 1| := by
        by_contra hcon
        push_neg at hcon
        nlinarith [abs_nonneg (γ 0 0), abs_nonneg (γ 1 1)]
      rw [if_pos hd1, if_neg (not_lt.2 hlt.le)]
    · have hd1 : ¬ 1 < |γ 1 1| := by
        intro hcon
        nlinarith [abs_nonneg (γ 0 0), abs_nonneg (γ 1 1)]
      rw [if_neg hd1, if_pos hgt, hval]
  · have hc' : ¬ (-γ 1 0 = 0) := by simpa using hc
    rw [if_neg hc', if_neg hc]
    have key : (γ 1 1 - γ 0 0 + Real.sign (γ 1 1 + γ 0 0) * Real.sqrt ((γ 1 1 + γ 0 0) ^ 2 - 4)) /
        (2 * -γ 1 0) = (γ 0 0 - γ 1 1 - Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) /
        (2 * γ 1 0) := by
      rw [add_comm (γ 1 1) (γ 0 0)]
      field_simp
      ring
    rw [key]

/-- Attracting fixed point goes to the attracting fixed point (any hyperbolic `γ`, `δ`). -/
theorem s32w_bdry_attracting {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb)
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR : RepresentsConj F γ δ)
    (hγ : 2 < |γ 0 0 + γ 1 1|) (hδ : 2 < |δ 0 0 + δ 1 1|) :
    Gb (attractingFixedPoint γ) = attractingFixedPoint δ := by
  have hF : ∀ x, F (γ • x) = δ • F x := by
    intro x
    have h := hR (F x)
    rw [F.symm_apply_apply] at h
    exact h.symm
  have hiter : ∀ (n : ℕ) (x : UpperHalfPlane), F (γ ^ n • x) = δ ^ n • F x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', mul_smul, hF, ih, pow_succ', mul_smul]
  set w₀ : UpperHalfPlane := UpperHalfPlane.I with hw₀
  have hlim1 := s32w_forward_attractor hγ w₀
  have hσ : attractingFixedPoint γ ∈ closure (toExt upperHalf) :=
    mem_closure_of_tendsto hlim1 (Eventually.of_forall fun n => ⟨_, (γ ^ n • w₀).coe_im_pos, rfl⟩)
  have hGc := hG.2.1.continuousWithinAt hσ
  have htend : Tendsto (fun n : ℕ => Gb (((γ ^ n • w₀ : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
      (𝓝 (Gb (attractingFixedPoint γ))) := hGc.tendsto.comp (s27l_tendsto_within hlim1)
  have hGb : ∀ n : ℕ, Gb (((γ ^ n • w₀ : UpperHalfPlane) : ℂ) : ExtPlane) =
      (((δ ^ n • F w₀ : UpperHalfPlane) : ℂ) : ExtPlane) := by
    intro n
    rw [h36t_ext_coe hG, hiter]
  have hlim2 := s32w_forward_attractor hδ (F w₀)
  exact tendsto_nhds_unique (htend.congr hGb) hlim2

/-- The boundary extension of a lift sends the attracting and repelling fixed points of a hyperbolic `γ` to
those of the hyperbolic `δ` representing `F ∘ γ ∘ F⁻¹`. -/
theorem s32w_bdry_fixed_points {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb)
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR : RepresentsConj F γ δ)
    (hγ : 2 < |γ 0 0 + γ 1 1|) (hδ : 2 < |δ 0 0 + δ 1 1|) :
    Gb (attractingFixedPoint γ) = attractingFixedPoint δ ∧
      Gb (repellingFixedPoint γ) = repellingFixedPoint δ := by
  refine ⟨s32w_bdry_attracting hG hR hγ hδ, ?_⟩
  have hR' : RepresentsConj F γ⁻¹ δ⁻¹ := by
    intro τ
    have h := hR (δ⁻¹ • τ)
    rw [smul_inv_smul] at h
    have h2 : F.symm τ = γ • F.symm (δ⁻¹ • τ) := by
      have h4 := congrArg F.symm h
      rwa [F.symm_apply_apply] at h4
    have h3 : γ⁻¹ • F.symm τ = F.symm (δ⁻¹ • τ) := by
      rw [h2, inv_smul_smul]
    rw [h3, F.apply_symm_apply]
  have htr : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ, |M⁻¹ 0 0 + M⁻¹ 1 1| = |M 0 0 + M 1 1| := by
    intro M
    have e00 : (M⁻¹) 0 0 = M 1 1 := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have e11 : (M⁻¹) 1 1 = M 0 0 := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [e00, e11, add_comm]
  have h := s32w_bdry_attracting hG hR' (by rw [htr]; exact hγ) (by rw [htr]; exact hδ)
  rwa [s32w_attracting_inv hγ, s32w_attracting_inv hδ] at h

end LiZhongQC
