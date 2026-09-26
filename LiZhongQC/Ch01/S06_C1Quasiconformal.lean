import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Lemmas.Quadrilateral
import LiZhongQC.Lemmas.ImageQuad
import LiZhongQC.Lemmas.Winding

/-!
# §6 C¹ 类拟共形映射 — Quasiconformal mappings of class `C¹`

* §6.1 formal derivatives: first order expansion, chain rules (6.2), (6.4), (6.5),
  conjugation rule (6.3), Cauchy–Riemann equations
* §6.2 complex characteristic `μ_f` (6.6) and dilatation quotient `D_f` (6.7);
  the image ellipse of an infinitesimal circle
* Definition 6.1 (classical quasiconformal maps)          — `IsC1Quasiconformal`
* examples: affine maps, `z/(1-|z|²)`
* §6.4 Beltrami equation
* §6.5 composition formula (6.8), compositions of `C¹` q.c. maps
* Theorem 6.1 (quasi-invariance of the modulus)            — `thm6_1_modulus_quasi_invariance`
* Definition 6.2 (maximal dilatation `K[f]`)               — `maxDilatationC1`
* Theorem 6.2 (Grötzsch)                                   — `thm6_2_grotzsch`,
                                                              `thm6_2_grotzsch_eq_iff`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## §6.1 Formal derivatives -/

/-- The first order expansion: `f(z) = f(z₀) + ∂_z f(z₀)(z - z₀) + ∂_{z̄} f(z₀)(z̄ - z̄₀) + o(|z - z₀|)`,
i.e. the real differential is `h ↦ ∂_z f · h + ∂_{z̄} f · h̄`. -/
theorem fderiv_eq_dz_dzbar {f : ℂ → ℂ} {z₀ : ℂ} (_hf : DifferentiableAt ℝ f z₀) (h : ℂ) :
    fderiv ℝ f z₀ h = dz f z₀ * h + dzbar f z₀ * conj h := by
  have hL : fderiv ℝ f z₀ h = (h.re : ℂ) * fderiv ℝ f z₀ 1 + (h.im : ℂ) * fderiv ℝ f z₀ I := by
    conv_lhs => rw [← Complex.re_add_im h]
    rw [show (h.re : ℂ) + h.im * I = h.re • (1 : ℂ) + h.im • I by simp, map_add, map_smul,
      map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL, dz, dzbar]
  conv_rhs => rw [← Complex.re_add_im h]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((h.im : ℂ) * fderiv ℝ f z₀ I) * I_sq

/-- The derivative of `f̄`: `(f̄)'(h) = conj (f'(h))`. -/
theorem fderiv_conj_comp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h : ℂ) :
    fderiv ℝ (fun w => conj (f w)) z h = conj (fderiv ℝ f z h) := by
  have hd : HasFDerivAt (fun w => conj (f w)) ((conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt
  rw [hd.fderiv]
  rfl

/-- Chain rule (6.2), first formula: `∂_z(g∘f) = (∂_w g ∘ f) ∂_z f + (∂_{w̄} g ∘ f) ∂_z f̄`. -/
theorem eq6_2_dz_comp {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g (f z)) :
    dz (g ∘ f) z = dz g (f z) * dz f z + dzbar g (f z) * dz (fun w => conj (f w)) z := by
  have h1 : fderiv ℝ (g ∘ f) z 1 =
      dz g (f z) * fderiv ℝ f z 1 + dzbar g (f z) * conj (fderiv ℝ f z 1) := by
    rw [fderiv_comp z hg hf, ContinuousLinearMap.comp_apply, fderiv_eq_dz_dzbar hg]
  have hI : fderiv ℝ (g ∘ f) z I =
      dz g (f z) * fderiv ℝ f z I + dzbar g (f z) * conj (fderiv ℝ f z I) := by
    rw [fderiv_comp z hg hf, ContinuousLinearMap.comp_apply, fderiv_eq_dz_dzbar hg]
  have hc1 := fderiv_conj_comp hf 1
  have hcI := fderiv_conj_comp hf I
  set A := dz g (f z)
  set B := dzbar g (f z)
  unfold dz
  rw [h1, hI, hc1, hcI]
  ring

/-- Chain rule (6.2), second formula: `∂_{z̄}(g∘f) = (∂_w g ∘ f) ∂_{z̄} f + (∂_{w̄} g ∘ f) ∂_{z̄} f̄`. -/
theorem eq6_2_dzbar_comp {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g (f z)) :
    dzbar (g ∘ f) z = dz g (f z) * dzbar f z + dzbar g (f z) * dzbar (fun w => conj (f w)) z := by
  have h1 : fderiv ℝ (g ∘ f) z 1 =
      dz g (f z) * fderiv ℝ f z 1 + dzbar g (f z) * conj (fderiv ℝ f z 1) := by
    rw [fderiv_comp z hg hf, ContinuousLinearMap.comp_apply, fderiv_eq_dz_dzbar hg]
  have hI : fderiv ℝ (g ∘ f) z I =
      dz g (f z) * fderiv ℝ f z I + dzbar g (f z) * conj (fderiv ℝ f z I) := by
    rw [fderiv_comp z hg hf, ContinuousLinearMap.comp_apply, fderiv_eq_dz_dzbar hg]
  have hc1 := fderiv_conj_comp hf 1
  have hcI := fderiv_conj_comp hf I
  set A := dz g (f z)
  set B := dzbar g (f z)
  unfold dzbar
  rw [h1, hI, hc1, hcI]
  ring

/-- (6.3): `conj(∂_z f) = ∂_{z̄} f̄` and `conj(∂_{z̄} f) = ∂_z f̄`. -/
theorem eq6_3 {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    conj (dz f z) = dzbar (fun w => conj (f w)) z ∧
      conj (dzbar f z) = dz (fun w => conj (f w)) z := by
  simp only [dz, dzbar, fderiv_conj_comp hf, map_div₀, map_sub, map_add, map_mul, Complex.conj_I,
    map_ofNat]
  constructor <;> ring

/-- The Cauchy–Riemann equations `∂_{z̄} f = 0`; for holomorphic `f`, `∂_z f = f'`. -/
theorem cauchyRiemann_iff {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ dzbar f z = 0 := by
  constructor
  · intro hf
    refine ⟨hf.restrictScalars ℝ, ?_⟩
    have e : ∀ x, fderiv ℝ f z x = fderiv ℂ f z x := fun x => by
      rw [hf.fderiv_restrictScalars ℝ]
      rfl
    have hI : fderiv ℂ f z I = I * fderiv ℂ f z 1 := by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [dzbar, e, e, hI]
    linear_combination (fderiv ℂ f z 1 / 2) * I_sq
  · rintro ⟨hf, hb⟩
    refine (differentiableAt_iff_restrictScalars ℝ hf).2
      ⟨ContinuousLinearMap.toSpanSingleton ℂ (dz f z), ?_⟩
    ext h
    simp [fderiv_eq_dz_dzbar hf h, hb, mul_comm]

theorem dz_eq_deriv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : dz f z = deriv f z := by
  have e : ∀ x, fderiv ℝ f z x = fderiv ℂ f z x := fun x => by
    rw [hf.fderiv_restrictScalars ℝ]
    rfl
  have hI : fderiv ℂ f z I = I * fderiv ℂ f z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [dz, e, e, hI, fderiv_apply_one_eq_deriv]
  linear_combination (-deriv f z / 2) * I_sq

/-- (6.4): the chain rule when the inner map `f` is holomorphic. -/
theorem eq6_4 {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℝ g (f z)) :
    dz (g ∘ f) z = dz g (f z) * deriv f z ∧ dzbar (g ∘ f) z = dzbar g (f z) * conj (deriv f z) := by
  have hfR := hf.restrictScalars ℝ
  have hb : dzbar f z = 0 := (cauchyRiemann_iff.1 hf).2
  obtain ⟨h1, h2⟩ := eq6_3 hfR
  constructor
  · rw [eq6_2_dz_comp hfR hg, dz_eq_deriv hf, ← h2, hb, map_zero, mul_zero, add_zero]
  · rw [eq6_2_dzbar_comp hfR hg, ← h1, dz_eq_deriv hf, hb, mul_zero, zero_add]

/-- (6.5): the chain rule when the outer map `g` is holomorphic. -/
theorem eq6_5 {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℂ g (f z)) :
    dz (g ∘ f) z = deriv g (f z) * dz f z ∧ dzbar (g ∘ f) z = deriv g (f z) * dzbar f z := by
  have hgR := hg.restrictScalars ℝ
  have hb : dzbar g (f z) = 0 := (cauchyRiemann_iff.1 hg).2
  exact ⟨by rw [eq6_2_dz_comp hf hgR, dz_eq_deriv hg, hb, zero_mul, add_zero],
    by rw [eq6_2_dzbar_comp hf hgR, dz_eq_deriv hg, hb, zero_mul, add_zero]⟩

/-! ## §6.2 Complex characteristic and dilatation quotient -/

/-- The Jacobian of a differentiable map is `|∂_z f|² - |∂_{z̄} f|²`. -/
theorem det_fderiv_eq_jacobian {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    LinearMap.det (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) = jacobian f z := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  rw [fderiv_eq_dz_dzbar hf, fderiv_eq_dz_dzbar hf, jacobian, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, one_re, one_im, I_re, I_im, map_one, Complex.conj_I,
    neg_re, neg_im]
  ring

/-- The linear approximation maps circles to ellipses: for `|∂_z f| > |∂_{z̄} f|` the largest
and smallest values of `|∂_z f + ∂_{z̄} f e^{-2iθ}|` are `|∂_z f| ± |∂_{z̄} f|`, attained at
`θ₀ = ½ arg(∂_{z̄} f / ∂_z f)` and `θ₀ + π/2`, so the axis ratio is `D_f`. -/
theorem ellipse_axes {f : ℂ → ℂ} {z : ℂ} (h : ‖dzbar f z‖ < ‖dz f z‖) :
    (∀ θ : ℝ, ‖dz f z + dzbar f z * exp (-(2 * θ) * I)‖ ≤ ‖dz f z‖ + ‖dzbar f z‖ ∧
      ‖dz f z‖ - ‖dzbar f z‖ ≤ ‖dz f z + dzbar f z * exp (-(2 * θ) * I)‖) ∧
    (let θ₀ := arg (dzbar f z / dz f z) / 2
     ‖dz f z + dzbar f z * exp (-(2 * θ₀) * I)‖ = ‖dz f z‖ + ‖dzbar f z‖) ∧
    (‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖) = dilatationQuotient f z := by
  set p := dz f z
  set q := dzbar f z
  have hp : 0 < ‖p‖ := (norm_nonneg _).trans_lt h
  have hp0 : p ≠ 0 := norm_pos_iff.1 hp
  have he : ∀ θ : ℝ, ‖q * exp (-(2 * θ) * I)‖ = ‖q‖ := fun θ => by
    rw [norm_mul, show (-(2 * (θ : ℂ)) * I) = ((-(2 * θ) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
  refine ⟨fun θ => ⟨(norm_add_le _ _).trans (by rw [he θ]), ?_⟩, ?_, ?_⟩
  · have := norm_sub_le (p + q * exp (-(2 * θ) * I)) (q * exp (-(2 * θ) * I))
    rw [add_sub_cancel_right, he θ] at this
    linarith
  · show ‖p + q * exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I)‖ = ‖p‖ + ‖q‖
    have h2 : exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I) * exp (arg (q / p) * I) = 1 := by
      rw [← Complex.exp_add, show -(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I + (arg (q / p) : ℂ) * I
        = 0 by push_cast; ring, Complex.exp_zero]
    have hq : q * exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I) = p * (‖q / p‖ : ℂ) := by
      calc q * exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I)
          = p * (q / p) * exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I) := by
            rw [mul_div_assoc', mul_div_right_comm, div_self hp0, one_mul]
        _ = p * ((‖q / p‖ : ℂ) * exp (arg (q / p) * I)) *
            exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
        _ = p * ‖q / p‖ *
            (exp (-(2 * ((arg (q / p) / 2 : ℝ) : ℂ)) * I) * exp (arg (q / p) * I)) := by
            ring
        _ = p * ‖q / p‖ := by rw [h2, mul_one]
    rw [hq, show p + p * (‖q / p‖ : ℂ) = p * ((1 + ‖q / p‖ : ℝ) : ℂ) by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_div, mul_add, mul_one,
      mul_div_assoc', mul_div_right_comm, div_self hp.ne', one_mul]
  · have h1 : 1 - ‖q‖ / ‖p‖ ≠ 0 := by
      rw [one_sub_div hp.ne']
      exact div_ne_zero (sub_pos.2 h).ne' hp.ne'
    rw [dilatationQuotient, complexDilatation, norm_div, div_eq_div_iff (sub_pos.2 h).ne' h1,
      one_add_div hp.ne', one_sub_div hp.ne']
    ring

/-! ## §6.3 Definition 6.1 -/

/-- **Definition 6.1** (经典拟共形映射).  `f` is a `C¹` quasiconformal map of `D` (with
constant `K ≥ 1`): a `C¹` homeomorphism of `D` onto `f(D)` with `|∂_{z̄} f| < |∂_z f|` and
`D_f ≤ K` everywhere in `D`. -/
def IsC1Quasiconformal (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  IsOpen D ∧ 1 ≤ K ∧ ContDiffOn ℝ 1 f D ∧ IsHomeomorphOnto f D (f '' D) ∧
    ∀ z ∈ D, ‖dzbar f z‖ < ‖dz f z‖ ∧ dilatationQuotient f z ≤ K

/-- The orientation preserving affine map `w = Az + B z̄ + C` (`|A| > |B|`) is a `C¹`
quasiconformal map with `μ = B/A` and `D_f = (|A| + |B|)/(|A| - |B|)`. -/
theorem affine_isC1Quasiconformal {A B C : ℂ} (h : ‖B‖ < ‖A‖) :
    IsC1Quasiconformal (fun z => A * z + B * conj z + C) univ ((‖A‖ + ‖B‖) / (‖A‖ - ‖B‖)) ∧
      ∀ z, complexDilatation (fun z => A * z + B * conj z + C) z = B / A ∧
        dilatationQuotient (fun z => A * z + B * conj z + C) z = (‖A‖ + ‖B‖) / (‖A‖ - ‖B‖) := by
  set f : ℂ → ℂ := fun z => A * z + B * conj z + C with hf_def
  have hA : 0 < ‖A‖ := (norm_nonneg _).trans_lt h
  have hA0 : A ≠ 0 := norm_pos_iff.1 hA
  have hd : ∀ z, HasFDerivAt f (A • ContinuousLinearMap.id ℝ ℂ + B • (conjCLE : ℂ →L[ℝ] ℂ)) z :=
    fun z => (((hasFDerivAt_id z).const_mul A).add
      ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul B)).add_const C
  have hdz : ∀ z, dz f z = A := fun z => by
    rw [dz, (hd z).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination ((B - A) / 2) * I_sq
  have hdzbar : ∀ z, dzbar f z = B := fun z => by
    rw [dzbar, (hd z).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination ((A - B) / 2) * I_sq
  have hμ : ∀ z, complexDilatation f z = B / A := fun z => by
    rw [complexDilatation, hdz, hdzbar]
  have hD : ∀ z, dilatationQuotient f z = (‖A‖ + ‖B‖) / (‖A‖ - ‖B‖) := fun z => by
    have h1 : 1 - ‖B‖ / ‖A‖ ≠ 0 := by
      rw [one_sub_div hA.ne']
      exact div_ne_zero (sub_pos.2 h).ne' hA.ne'
    rw [dilatationQuotient, hμ, norm_div, div_eq_div_iff h1 (sub_pos.2 h).ne', one_add_div hA.ne',
      one_sub_div hA.ne']
    ring
  -- the explicit inverse `w ↦ (Ā(w - C) - B conj(w - C))/(|A|² - |B|²)`
  set D : ℂ := (‖A‖ : ℂ) ^ 2 - (‖B‖ : ℂ) ^ 2 with hD_def
  have hD0 : D ≠ 0 := by
    rw [hD_def]
    exact_mod_cast (show 0 < ‖A‖ ^ 2 - ‖B‖ ^ 2 by nlinarith [norm_nonneg B]).ne'
  have hDc : conj D = D := by
    rw [hD_def, map_sub, map_pow, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]
  have hAA : A * conj A = (‖A‖ : ℂ) ^ 2 := Complex.mul_conj' A
  have hBB : B * conj B = (‖B‖ : ℂ) ^ 2 := Complex.mul_conj' B
  set g : ℂ → ℂ := fun w => (conj A * (w - C) - B * conj (w - C)) / D with hg_def
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg_def, hf_def]
    dsimp only
    rw [div_eq_iff hD0, hD_def]
    simp only [map_add, map_sub, map_mul, Complex.conj_conj]
    linear_combination z * hAA - z * hBB
  have hfg : ∀ w, A * g w + B * conj (g w) = w - C := fun w => by
    have hgw : g w * D = conj A * (w - C) - B * conj (w - C) := div_mul_cancel₀ _ hD0
    have hcgw : conj (g w) * D = A * conj (w - C) - conj B * (w - C) := by
      have := congrArg conj hgw
      simpa only [map_mul, map_sub, Complex.conj_conj, hDc] using this
    apply mul_right_cancel₀ hD0
    rw [hD_def] at hgw hcgw ⊢
    linear_combination A * hgw + B * hcgw + (w - C) * hAA - (w - C) * hBB
  have hg_cont : Continuous g :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).sub
      (continuous_const.mul (Complex.continuous_conj.comp (continuous_id.sub continuous_const)))).div_const
      _
  refine ⟨⟨isOpen_univ, ?_, ?_, ⟨fun z _ => (hd z).continuousAt.continuousWithinAt,
    fun x _ y _ hxy => by rw [← hgf x, ← hgf y, hxy], rfl, ?_⟩, fun z _ => ?_⟩,
    fun z => ⟨hμ z, hD z⟩⟩
  · rw [le_div_iff₀ (sub_pos.2 h)]
    linarith [norm_nonneg B]
  · exact (((contDiff_const.mul contDiff_id).add
      (contDiff_const.mul (conjCLE : ℂ →L[ℝ] ℂ).contDiff)).add contDiff_const).contDiffOn
  · refine hg_cont.continuousOn.congr fun w hw => ?_
    obtain ⟨z, -, rfl⟩ := hw
    have hinv := Function.invFunOn_eq (f := f) (s := univ) ⟨z, mem_univ _, rfl⟩
    rw [← hgf (Function.invFunOn f univ (f z)), hinv]
  · rw [hdz, hdzbar]
    exact ⟨h, (hD z).le⟩

/-- The map `z ↦ z/(1 - |z|²)` written algebraically as `z (1 - z z̄)⁻¹`. -/
theorem discMap_eq :
    (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) = fun w => w * (1 - w * conj w)⁻¹ := by
  funext w
  rw [Complex.mul_conj', div_eq_mul_inv]

theorem discMap_hasFDerivAt {z : ℂ} (hu : 1 - z * conj z ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun w : ℂ => w * (1 - w * conj w)⁻¹) L z ∧
      ∀ h, L h = z * ((1 - z * conj z)⁻¹ * (z * conj h + conj z * h) * (1 - z * conj z)⁻¹) +
        (1 - z * conj z)⁻¹ * h := by
  have hc : HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hs := ((hasFDerivAt_id (𝕜 := ℝ) z).mul hc).const_sub 1
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hu).comp z hs
  refine ⟨_, (hasFDerivAt_id (𝕜 := ℝ) z).mul hi, fun h => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, id_eq]
  ring

/-- §6.3, the example `w = z/(1-|z|²)`: `∂_z f = 1/(1-|z|²)²` and `∂_z̄ f = z²/(1-|z|²)²`.

*Correction.*  The book prints `∂_z̄ f = |z|²/(1-|z|²)²`, and correspondingly `μ_f(z) = |z|²`
(`discMap_dilatationQuotient`), substituting the modulus for the value; the correct values are
`z²/(1-|z|²)²` and `μ_f(z) = z²`.  Only `|μ_f|` enters `D_f`, so the book's conclusion
`D_f = (1+|z|²)/(1-|z|²)` — the point of the example — is unaffected. -/
theorem discMap_dz_dzbar {z : ℂ} (hz : ‖z‖ < 1) :
    dz (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = 1 / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ∧
      dzbar (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = z ^ 2 / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 := by
  have hu : 1 - z * conj z ≠ 0 := by
    rw [Complex.mul_conj']
    exact_mod_cast (show (0 : ℝ) < 1 - ‖z‖ ^ 2 by nlinarith [norm_nonneg z]).ne'
  obtain ⟨L, hL, hLh⟩ := discMap_hasFDerivAt hu
  have hv : (1 - z * conj z) * (1 - z * conj z)⁻¹ = 1 := mul_inv_cancel₀ hu
  rw [discMap_eq, dz, dzbar, hL.fderiv, hLh, hLh, ← Complex.mul_conj']
  simp only [div_eq_mul_inv, one_mul, ← inv_pow, map_one, Complex.conj_I]
  constructor
  · linear_combination (1 / 2 * (z ^ 2 * (1 - z * conj z)⁻¹ ^ 2 -
      z * conj z * (1 - z * conj z)⁻¹ ^ 2 - (1 - z * conj z)⁻¹)) * I_sq -
      (1 - z * conj z)⁻¹ * hv
  · linear_combination (1 / 2 * (-z ^ 2 * (1 - z * conj z)⁻¹ ^ 2 +
      z * conj z * (1 - z * conj z)⁻¹ ^ 2 + (1 - z * conj z)⁻¹)) * I_sq

theorem discMap_dilatationQuotient {z : ℂ} (hz : ‖z‖ < 1) :
    dilatationQuotient (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z =
      (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := discMap_dz_dzbar hz
  have hu : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < 1 - ‖z‖ ^ 2 by nlinarith [norm_nonneg z]).ne'
  have hμ : complexDilatation (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = z ^ 2 := by
    rw [complexDilatation, h1, h2, one_div, div_inv_eq_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hu)]
  rw [dilatationQuotient, hμ, norm_pow]

/-- The inverse `w ↦ 2w/(1 + √(1 + 4|w|²))` of `z ↦ z/(1 - |z|²)`. -/
def discMapInv (w : ℂ) : ℂ := ((2 / (1 + √(1 + 4 * ‖w‖ ^ 2)) : ℝ) : ℂ) * w

theorem continuous_discMapInv : Continuous discMapInv := by
  unfold discMapInv
  refine (Complex.continuous_ofReal.comp ?_).mul continuous_id
  exact continuous_const.div (continuous_const.add (Real.continuous_sqrt.comp
    (continuous_const.add (continuous_const.mul (continuous_norm.pow 2))))) fun w => by positivity

theorem norm_discMapInv_lt (w : ℂ) : ‖discMapInv w‖ < 1 := by
  have hs := Real.sqrt_nonneg (1 + 4 * ‖w‖ ^ 2)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + 4 * ‖w‖ ^ 2 by positivity)
  have hw := norm_nonneg w
  rw [discMapInv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_mul_eq_mul_div, div_lt_one (by positivity)]
  nlinarith

theorem discMap_discMapInv (w : ℂ) : discMapInv w / (1 - (‖discMapInv w‖ : ℂ) ^ 2) = w := by
  obtain ⟨s, hs_def⟩ : ∃ s, s = √(1 + 4 * ‖w‖ ^ 2) := ⟨_, rfl⟩
  have hs : 0 ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + 4 * ‖w‖ ^ 2 := by rw [hs_def]; exact Real.sq_sqrt (by positivity)
  have h1s : 0 < 1 + s := by linarith
  have hdef : discMapInv w = ((2 / (1 + s) : ℝ) : ℂ) * w := by rw [discMapInv, hs_def]
  have hn : ‖discMapInv w‖ = 2 / (1 + s) * ‖w‖ := by
    rw [hdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos two_pos h1s).le]
  have key : 1 - (2 / (1 + s) * ‖w‖) ^ 2 = 2 / (1 + s) := by
    rw [div_mul_eq_mul_div, div_pow, one_sub_div (pow_pos h1s 2).ne',
      div_eq_div_iff (pow_pos h1s 2).ne' h1s.ne']
    linear_combination (1 + s) * hs2
  have hne : ((2 / (1 + s) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (div_pos two_pos h1s).ne'
  rw [hn, show (1 : ℂ) - ((2 / (1 + s) * ‖w‖ : ℝ) : ℂ) ^ 2 =
    ((1 - (2 / (1 + s) * ‖w‖) ^ 2 : ℝ) : ℂ) by push_cast; ring, key, hdef,
    mul_div_right_comm, div_self hne, one_mul]

theorem discMapInv_discMap {z : ℂ} (hz : ‖z‖ < 1) :
    discMapInv (z / (1 - (‖z‖ : ℂ) ^ 2)) = z := by
  have hρ : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hρ' : 1 - ‖z‖ ^ 2 ≠ 0 := hρ.ne'
  have hcast : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖z / (1 - (‖z‖ : ℂ) ^ 2)‖ = ‖z‖ / (1 - ‖z‖ ^ 2) := by
    rw [norm_div, hcast, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have hq : 0 ≤ (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) := div_nonneg (by positivity) hρ.le
  have hs : √(1 + 4 * ‖z / (1 - (‖z‖ : ℂ) ^ 2)‖ ^ 2) = (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
    rw [hn, ← Real.sqrt_sq hq]
    congr 1
    field_simp
    ring
  have h2 : 2 / (1 + (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2)) = 1 - ‖z‖ ^ 2 := by
    have : 1 + (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) = 2 / (1 - ‖z‖ ^ 2) := by
      rw [one_add_div hρ']; ring
    rw [this, div_div_eq_mul_div, mul_div_cancel_left₀ _ two_ne_zero]
  have hne : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ'
  rw [discMapInv, hs, h2, hcast, mul_div_assoc', mul_div_right_comm, div_self hne, one_mul]

/-- The example `w = z/(1 - |z|²)`: a homeomorphism of `Δ` onto `ℂ` with `μ_f = z²` and
`D_f = (1 + |z|²)/(1 - |z|²)`. -/
theorem example_disc_to_plane :
    IsHomeomorphOnto (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) unitDisc univ ∧
      ∀ z ∈ unitDisc,
        dz (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = 1 / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ∧
        dzbar (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = z ^ 2 / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ∧
        dilatationQuotient (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) z = (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  have hmem : ∀ {z : ℂ}, z ∈ unitDisc ↔ ‖z‖ < 1 := by simp [unitDisc]
  refine ⟨⟨fun z hz => ?_, fun x hx y hy hxy => ?_, ?_, ?_⟩, fun z hz =>
    ⟨(discMap_dz_dzbar (hmem.1 hz)).1, (discMap_dz_dzbar (hmem.1 hz)).2,
      discMap_dilatationQuotient (hmem.1 hz)⟩⟩
  · have hu : 1 - z * conj z ≠ 0 := by
      rw [Complex.mul_conj']
      exact_mod_cast (show (0 : ℝ) < 1 - ‖z‖ ^ 2 by nlinarith [norm_nonneg z, hmem.1 hz]).ne'
    obtain ⟨L, hL, -⟩ := discMap_hasFDerivAt hu
    rw [discMap_eq]
    exact hL.continuousAt.continuousWithinAt
  · calc x = discMapInv (x / (1 - (‖x‖ : ℂ) ^ 2)) := (discMapInv_discMap (hmem.1 hx)).symm
      _ = discMapInv (y / (1 - (‖y‖ : ℂ) ^ 2)) := congrArg discMapInv hxy
      _ = y := discMapInv_discMap (hmem.1 hy)
  · exact eq_univ_of_forall fun w =>
      ⟨discMapInv w, hmem.2 (norm_discMapInv_lt w), discMap_discMapInv w⟩
  · refine continuous_discMapInv.continuousOn.congr fun w _ => ?_
    have hex : ∃ a ∈ unitDisc, (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) a = w :=
      ⟨discMapInv w, hmem.2 (norm_discMapInv_lt w), discMap_discMapInv w⟩
    exact (discMapInv_discMap (hmem.1 (Function.invFunOn_mem hex))).symm.trans
      (congrArg discMapInv (Function.invFunOn_eq hex))

/-- The map `z/(1 - |z|²)` is quasiconformal in every disc `{|z| < r}`, `r < 1`, but not in `Δ`. -/
theorem example_disc_to_plane_qc :
    (∀ r : ℝ, 0 < r → r < 1 → IsC1Quasiconformal (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) (ball 0 r)
      ((1 + r ^ 2) / (1 - r ^ 2))) ∧
    ∀ K : ℝ, ¬ IsC1Quasiconformal (fun z : ℂ => z / (1 - (‖z‖ : ℂ) ^ 2)) unitDisc K := by
  have hmem : ∀ {z : ℂ}, z ∈ unitDisc ↔ ‖z‖ < 1 := by simp [unitDisc]
  obtain ⟨⟨hcont, hinj, -, -⟩, hder⟩ := example_disc_to_plane
  refine ⟨fun r hr0 hr1 => ?_, fun K hK => ?_⟩
  · have hsub : ball (0 : ℂ) r ⊆ unitDisc := fun z hz =>
      hmem.2 ((mem_ball_zero_iff.1 hz).trans hr1)
    have hr2 : 0 < 1 - r ^ 2 := by nlinarith
    refine ⟨isOpen_ball, ?_, ?_, ⟨hcont.mono hsub, hinj.mono hsub, rfl, ?_⟩, fun z hz => ?_⟩
    · rw [le_div_iff₀ hr2]
      nlinarith
    · intro z hz
      have hu : 1 - z * conj z ≠ 0 := by
        rw [Complex.mul_conj']
        exact_mod_cast (show (0 : ℝ) < 1 - ‖z‖ ^ 2 by
          nlinarith [norm_nonneg z, mem_ball_zero_iff.1 hz]).ne'
      rw [discMap_eq]
      exact (contDiffAt_id.mul ((contDiffAt_const.sub (contDiffAt_id.mul
        (conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt)).inv hu)).contDiffWithinAt
    · refine continuous_discMapInv.continuousOn.congr ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [(hinj.mono hsub).leftInvOn_invFunOn hz, discMapInv_discMap (hmem.1 (hsub hz))]
    · have hz1 : ‖z‖ < r := mem_ball_zero_iff.1 hz
      have hz1' : ‖z‖ < 1 := hz1.trans hr1
      obtain ⟨h1, h2, h3⟩ := hder z (hmem.2 hz1')
      have hu : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast (show (0 : ℝ) < 1 - ‖z‖ ^ 2 by nlinarith [norm_nonneg z]).ne'
      refine ⟨?_, ?_⟩
      · rw [h1, h2]
        simp only [norm_div, norm_pow, norm_one]
        rw [div_lt_div_iff_of_pos_right (pow_pos (norm_pos_iff.2 hu) 2)]
        nlinarith [norm_nonneg z]
      · rw [h3, div_le_div_iff₀ (by nlinarith [norm_nonneg z]) hr2]
        nlinarith [norm_nonneg z]
  · obtain ⟨-, hK1, -, -, hq⟩ := hK
    have hK0 : 0 < K + 1 := by linarith
    obtain ⟨t, ht⟩ : ∃ t, t = K / (K + 1) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hK0.le
    have ht1 : t < 1 := by rw [ht]; exact (div_lt_one hK0).2 (by linarith)
    have e : t * (K + 1) = K := by rw [ht]; exact div_mul_cancel₀ _ hK0.ne'
    have hz : ‖((√t : ℝ) : ℂ)‖ ^ 2 = t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ht0]
    have hz1 : ‖((√t : ℝ) : ℂ)‖ < 1 := by nlinarith [norm_nonneg ((√t : ℝ) : ℂ)]
    have hD := (hq _ (hmem.2 hz1)).2
    rw [(hder _ (hmem.2 hz1)).2.2, hz, div_le_iff₀ (by linarith)] at hD
    nlinarith

/-! ## §6.4 The Beltrami equation -/

/-- §6.4: a `C¹` quasiconformal map is a classical homeomorphic solution of the Beltrami
equation `∂_{z̄} w = μ ∂_z w` with `|μ| ≤ k = (K-1)/(K+1) < 1`. -/
theorem c1qc_beltrami {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsC1Quasiconformal f D K) :
    ∀ z ∈ D, dzbar f z = complexDilatation f z * dz f z ∧
      ‖complexDilatation f z‖ ≤ (K - 1) / (K + 1) := by
  intro z hz
  obtain ⟨-, hK, -, -, hD⟩ := hf
  obtain ⟨hlt, hDK⟩ := hD z hz
  have hdz : dz f z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlt
    exact (norm_nonneg _).not_gt hlt
  have hm1 : ‖complexDilatation f z‖ < 1 := by
    rw [complexDilatation, norm_div, div_lt_one (norm_pos_iff.2 hdz)]
    exact hlt
  refine ⟨(div_mul_cancel₀ _ hdz).symm, ?_⟩
  unfold dilatationQuotient at hDK
  rw [div_le_iff₀ (by linarith)] at hDK
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- §6.4: the real form of the Beltrami equation, with `μ = a + ib`:
`(1-a)u_x - (1+a)v_y = b(u_y - v_x)` and `(1-a)v_x + (1+a)u_y = b(u_x + v_y)`. -/
theorem beltrami_real_form {f : ℂ → ℂ} {z : ℂ} (_hf : DifferentiableAt ℝ f z) (μ : ℂ) :
    dzbar f z = μ * dz f z ↔
      ((1 - μ.re) * (fderiv ℝ f z 1).re - (1 + μ.re) * (fderiv ℝ f z I).im =
          μ.im * ((fderiv ℝ f z I).re - (fderiv ℝ f z 1).im) ∧
        (1 - μ.re) * (fderiv ℝ f z 1).im + (1 + μ.re) * (fderiv ℝ f z I).re =
          μ.im * ((fderiv ℝ f z 1).re + (fderiv ℝ f z I).im)) := by
  rw [dzbar, dz, Complex.ext_iff]
  simp only [div_ofNat_re, div_ofNat_im, add_re, add_im, sub_re, sub_im, mul_re, mul_im, I_re,
    I_im]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-! ## §6.5 Compositions -/

/-- (6.8): `μ_{g∘f} = (μ_f + (μ_g ∘ f) τ)/(1 + μ̄_f (μ_g ∘ f) τ)`, `τ = conj(f_z)/f_z`. -/
theorem eq6_8_complexDilatation_comp {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g (f z)) (hfz : dz f z ≠ 0) (hgz : dz g (f z) ≠ 0)
    (hμf : ‖complexDilatation f z‖ < 1) (hμg : ‖complexDilatation g (f z)‖ < 1) :
    complexDilatation (g ∘ f) z =
      (complexDilatation f z + complexDilatation g (f z) * (conj (dz f z) / dz f z)) /
        (1 + conj (complexDilatation f z) * complexDilatation g (f z) * (conj (dz f z) / dz f z)) := by
  have h2 := eq6_2_dz_comp hf hg
  have h3 := eq6_2_dzbar_comp hf hg
  obtain ⟨c1, c2⟩ := eq6_3 hf
  rw [← c2] at h2
  rw [← c1] at h3
  have hgb : dzbar g (f z) = complexDilatation g (f z) * dz g (f z) := (div_mul_cancel₀ _ hgz).symm
  have hfb : dzbar f z = complexDilatation f z * dz f z := (div_mul_cancel₀ _ hfz).symm
  have hτ : ‖conj (complexDilatation f z) * complexDilatation g (f z) * (conj (dz f z) / dz f z)‖
      < 1 := by
    rw [norm_mul, norm_mul, norm_conj, norm_div, norm_conj, div_self (norm_ne_zero_iff.2 hfz),
      mul_one]
    nlinarith [norm_nonneg (complexDilatation f z), norm_nonneg (complexDilatation g (f z))]
  have hden : 1 + conj (complexDilatation f z) * complexDilatation g (f z) *
      (conj (dz f z) / dz f z) ≠ 0 := by
    intro h
    have h' : conj (complexDilatation f z) * complexDilatation g (f z) * (conj (dz f z) / dz f z)
        = -1 := by linear_combination h
    rw [h', norm_neg, norm_one] at hτ
    exact lt_irrefl _ hτ
  set μf := complexDilatation f z
  set μg := complexDilatation g (f z)
  set A := dz g (f z)
  set p := dz f z
  rw [complexDilatation, h2, h3, hgb, hfb]
  have hL : A * p + μg * A * conj (μf * p) ≠ 0 := by
    rw [show A * p + μg * A * conj (μf * p) =
      A * p * (1 + conj μf * μg * (conj p / p)) by field_simp; simp only [map_mul]; ring]
    exact mul_ne_zero (mul_ne_zero hgz hfz) hden
  rw [div_eq_div_iff hL hden]
  field_simp
  simp only [map_mul]
  ring

/-- §6.5: composing with a conformal map on the left does not change `μ`. -/
theorem complexDilatation_comp_conformal_left {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℂ g (f z)) (hg' : deriv g (f z) ≠ 0) :
    complexDilatation (g ∘ f) z = complexDilatation f z := by
  obtain ⟨h1, h2⟩ := eq6_5 hf hg
  rw [complexDilatation, complexDilatation, h1, h2, mul_div_mul_left _ _ hg']

/-- §6.5: composing with a conformal map on the right: `μ_{g∘f} = (μ_g ∘ f) conj(f')/f'`, in
particular `|μ_{g∘f}| = |μ_g ∘ f|`. -/
theorem complexDilatation_comp_conformal_right {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (_hf' : deriv f z ≠ 0) (hg : DifferentiableAt ℝ g (f z)) :
    complexDilatation (g ∘ f) z = complexDilatation g (f z) * (conj (deriv f z) / deriv f z) := by
  obtain ⟨h1, h2⟩ := eq6_4 hf hg
  rw [complexDilatation, complexDilatation, h1, h2, mul_div_mul_comm]

/-- The algebra behind §6.5: with `P = A p + B q̄`, `Q = A q + B p̄` (the chain rule (6.2)) one has
`|P|² - |Q|² = (|A|² - |B|²)(|p|² - |q|²)` and `|P| + |Q| ≤ (|A| + |B|)(|p| + |q|)`, hence the
dilatation quotients multiply at most. -/
theorem dilatation_comp_le_aux {p q A B P Q : ℂ} {K K₁ : ℝ} (hP : P = A * p + B * conj q)
    (hQ : Q = A * q + B * conj p) (hpq : ‖q‖ < ‖p‖) (hAB : ‖B‖ < ‖A‖)
    (hK : (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) ≤ K) (hK₁ : (‖A‖ + ‖B‖) / (‖A‖ - ‖B‖) ≤ K₁) :
    ‖Q‖ < ‖P‖ ∧ (‖P‖ + ‖Q‖) / (‖P‖ - ‖Q‖) ≤ K₁ * K := by
  have hJ : ‖P‖ ^ 2 - ‖Q‖ ^ 2 = (‖A‖ ^ 2 - ‖B‖ ^ 2) * (‖p‖ ^ 2 - ‖q‖ ^ 2) := by
    subst hP hQ
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, mul_re, mul_im, conj_re,
      conj_im]
    ring
  have hsum : ‖P‖ + ‖Q‖ ≤ (‖A‖ + ‖B‖) * (‖p‖ + ‖q‖) := by
    subst hP hQ
    have h1 := norm_add_le (A * p) (B * conj q)
    have h2 := norm_add_le (A * q) (B * conj p)
    simp only [norm_mul, norm_conj] at h1 h2
    linarith
  have hpq2 : 0 < ‖p‖ - ‖q‖ := sub_pos.2 hpq
  have hAB2 : 0 < ‖A‖ - ‖B‖ := sub_pos.2 hAB
  have hq0 := norm_nonneg q
  have hB0 := norm_nonneg B
  have hX : 0 < (‖A‖ ^ 2 - ‖B‖ ^ 2) * (‖p‖ ^ 2 - ‖q‖ ^ 2) := by
    apply mul_pos <;> nlinarith
  have hPQ : ‖Q‖ < ‖P‖ := by
    by_contra hc
    have := not_lt.1 hc
    nlinarith [norm_nonneg P, norm_nonneg Q]
  refine ⟨hPQ, ?_⟩
  have ht : 0 < ‖P‖ - ‖Q‖ := sub_pos.2 hPQ
  have hs : 0 < ‖P‖ + ‖Q‖ := by linarith [norm_nonneg Q]
  rw [div_le_iff₀ hpq2] at hK
  rw [div_le_iff₀ hAB2] at hK₁
  rw [div_le_iff₀ ht]
  have hprod : (‖A‖ + ‖B‖) * (‖p‖ + ‖q‖) ≤ K₁ * K * ((‖A‖ - ‖B‖) * (‖p‖ - ‖q‖)) := by
    have e1 := mul_le_mul_of_nonneg_right hK₁ (by linarith : (0 : ℝ) ≤ ‖p‖ + ‖q‖)
    have e2 := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ K₁ * (‖A‖ - ‖B‖))
    linarith
  have key : (‖P‖ + ‖Q‖) * (‖P‖ + ‖Q‖) ≤ (K₁ * K * (‖P‖ - ‖Q‖)) * (‖P‖ + ‖Q‖) := by
    calc (‖P‖ + ‖Q‖) * (‖P‖ + ‖Q‖)
        ≤ ((‖A‖ + ‖B‖) * (‖p‖ + ‖q‖)) * ((‖A‖ + ‖B‖) * (‖p‖ + ‖q‖)) :=
          mul_self_le_mul_self hs.le hsum
      _ ≤ (K₁ * K * ((‖A‖ - ‖B‖) * (‖p‖ - ‖q‖))) * ((‖A‖ + ‖B‖) * (‖p‖ + ‖q‖)) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = (K₁ * K * (‖P‖ - ‖Q‖)) * (‖P‖ + ‖Q‖) := by
          have e : (‖P‖ - ‖Q‖) * (‖P‖ + ‖Q‖) = (‖A‖ ^ 2 - ‖B‖ ^ 2) * (‖p‖ ^ 2 - ‖q‖ ^ 2) := by
            rw [← hJ]; ring
          linear_combination (-(K₁ * K)) * e
  exact le_of_mul_le_mul_right key hs

/-- §6.5: the composition of `C¹` quasiconformal maps with constants `K` and `K₁` is a `C¹`
quasiconformal map with constant `K₁ K`. -/
theorem c1qc_comp {f g : ℂ → ℂ} {D D₁ : Set ℂ} {K K₁ : ℝ} (hf : IsC1Quasiconformal f D K)
    (hg : IsC1Quasiconformal g D₁ K₁) (hsub : f '' D ⊆ D₁) :
    IsC1Quasiconformal (g ∘ f) D (K₁ * K) := by
  obtain ⟨hD, hK, hfC, ⟨hfc, hfi, -, hfinv⟩, hfq⟩ := hf
  obtain ⟨hD₁, hK₁, hgC, ⟨hgc, hgi, -, hginv⟩, hgq⟩ := hg
  have hmaps : MapsTo f D D₁ := fun z hz => hsub (mem_image_of_mem f hz)
  refine ⟨hD, one_le_mul_of_one_le_of_one_le hK₁ hK, hgC.comp hfC hmaps,
    ⟨hgc.comp hfc hmaps, hgi.comp hfi hmaps, rfl, ?_⟩, fun z hz => ?_⟩
  · -- the inverse of `g ∘ f` is `f⁻¹ ∘ g⁻¹`
    have hmaps' : MapsTo (Function.invFunOn g D₁) ((g ∘ f) '' D) (f '' D) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Function.comp_apply, hgi.leftInvOn_invFunOn (hmaps hz)]
      exact mem_image_of_mem f hz
    refine (hfinv.comp (hginv.mono ?_) hmaps').congr ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact mem_image_of_mem g (hmaps hz)
    · rintro _ ⟨z, hz, rfl⟩
      rw [(hgi.comp hfi hmaps).leftInvOn_invFunOn hz]
      show z = Function.invFunOn f D (Function.invFunOn g D₁ (g (f z)))
      rw [hgi.leftInvOn_invFunOn (hmaps hz), hfi.leftInvOn_invFunOn hz]
  · obtain ⟨hlt, hDf⟩ := hfq z hz
    obtain ⟨hlt₁, hDg⟩ := hgq (f z) (hmaps hz)
    have hfd : DifferentiableAt ℝ f z :=
      (hfC.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hz)
    have hgd : DifferentiableAt ℝ g (f z) :=
      (hgC.differentiableOn one_ne_zero).differentiableAt (hD₁.mem_nhds (hmaps hz))
    obtain ⟨c1, c2⟩ := eq6_3 hfd
    have hP := eq6_2_dz_comp hfd hgd
    have hQ := eq6_2_dzbar_comp hfd hgd
    rw [← c2] at hP
    rw [← c1] at hQ
    obtain ⟨h1, h2⟩ := dilatation_comp_le_aux hP hQ hlt hlt₁
      ((ellipse_axes hlt).2.2.trans_le hDf) ((ellipse_axes hlt₁).2.2.trans_le hDg)
    refine ⟨h1, ?_⟩
    rw [← (ellipse_axes h1).2.2]
    exact h2

/-! ## §6.7 Maximal dilatation and Grötzsch's theorem -/

/-- **Definition 6.2**: the maximal dilatation `K[f] = sup_{z ∈ D} D_f(z)` of a `C¹` map. -/
def maxDilatationC1 (f : ℂ → ℂ) (D : Set ℂ) : ℝ := sSup (dilatationQuotient f '' D)

/-- `f` is a `C¹` quasiconformal map of the rectangle `R(0,a,a+bi,bi)` onto `R'(0,a',a'+b'i,b'i)`
preserving the vertices in order. -/
def IsC1QCRectMap (f : ℂ → ℂ) (a b a' b' : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧
    (∃ K, IsC1Quasiconformal f (rectangle a b) K) ∧ f '' rectangle a b = rectangle a' b' ∧
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f (rectangle a b) (rectangle a' b') F ∧
      ∀ i, F (rectVert a b i) = rectVert a' b' i

/-! ### The length–area argument on rectangles (proof of Theorem 6.1 for rectangles) -/

/-- A locally Lipschitz curve in `U` followed by a `C¹` map on `U` is locally Lipschitz. -/
theorem locallyLipschitzOn_comp_of_contDiffOn {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) {γ : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hγ : LocallyLipschitzOn s γ) (hmaps : MapsTo γ s U) : LocallyLipschitzOn s (g ∘ γ) := by
  intro t ht
  obtain ⟨K₁, V₁, hV₁, hK₁⟩ := hγ ht
  have hcd : ContDiffAt ℝ 1 g (γ t) := hg.contDiffAt (hU.mem_nhds (hmaps ht))
  obtain ⟨K₂, V₂, hV₂, hK₂⟩ := hcd.exists_lipschitzOnWith
  have hcont : ContinuousAt γ t := hγ.continuousOn.continuousAt (hs.mem_nhds ht)
  refine ⟨K₂ * K₁, V₁ ∩ γ ⁻¹' V₂,
    inter_mem hV₁ (mem_nhdsWithin_of_mem_nhds (hcont.preimage_mem_nhds hV₂)), ?_⟩
  exact hK₂.comp (hK₁.mono inter_subset_left) fun x hx => hx.2

theorem closure_toExt_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closure (toExt (rectangle a b)) = toExt (Icc 0 a ×ℂ Icc 0 b) := by
  rw [closure_toExt_of_isBounded (isBounded_rectangle a b), rectangle_eq_reProdIm,
    closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]

/-- A boundary extension of a homeomorphism of `R(0,a,a+bi,bi)` onto `R(0,a',a'+b'i,b'i)` keeping
the vertices maps the bottom and top edges onto the bottom and top edges. -/
theorem rect_homeoExtension_sides {h : ℂ → ℂ} {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (himg : h '' rectangle a b = rectangle a' b')
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) :
    H '' toExt (Icc 0 a ×ℂ {0}) = toExt (Icc 0 a' ×ℂ {0}) ∧
      H '' toExt (Icc 0 a ×ℂ {b}) = toExt (Icc 0 a' ×ℂ {b'}) := by
  have hfr : frontier (toExt (rectangle a b)) ⊆ closure (toExt (rectangle a b)) :=
    frontier_subset_closure
  have hvert : ∀ i, rectVert a b i ∈ closure (toExt (rectangle a b)) := by
    intro i
    rw [closure_toExt_rectangle ha hb]
    fin_cases i <;> simp [rectVert, toExt, mem_reProdIm, ha.le, hb.le]
  have hFr := hH.image_frontier (isOpen_rectangle a b) (isOpen_rectangle a' b') himg
  have hb0 := image_boundaryArc_of_injOn isClosed_closure hH.2.1 hH.2.2.1 hfr (hvert 0) (hvert 1)
    (hvert 2)
  have hb2 := image_boundaryArc_of_injOn isClosed_closure hH.2.1 hH.2.2.1 hfr (hvert 2) (hvert 3)
    (hvert 0)
  rw [boundaryArc_frontier_toExt_rectangle_bottom ha hb, hFr, hv, hv, hv,
    boundaryArc_frontier_toExt_rectangle_bottom ha' hb'] at hb0
  rw [boundaryArc_frontier_toExt_rectangle_top ha hb, hFr, hv, hv, hv,
    boundaryArc_frontier_toExt_rectangle_top ha' hb'] at hb2
  exact ⟨hb0, hb2⟩

/-- The image of a vertical segment of `R` joins the bottom and top edges of `R'`. -/
theorem rect_comp_vertSeg_mem {h : ℂ → ℂ} {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (himg : h '' rectangle a b = rectangle a' b')
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    ∃ γ ∈ rectJoiningCurves a' b', γ.toFun = h ∘ (vertSeg b x).toFun := by
  obtain ⟨hbot, htop⟩ := rect_homeoExtension_sides ha hb ha' hb' himg hH hv
  obtain ⟨htr, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩ := vertSeg_mem hb hx
  have hmaps : MapsTo (vertSeg b x).toFun (Ioo 0 1) (rectangle a b) := fun t ht =>
    htr (mem_image_of_mem _ ht)
  have hforth : ∀ {l : Filter ℝ} {p : ℂ} {A : Set ℂ}, Ioo (0 : ℝ) 1 ∈ l →
      p ∈ Icc 0 a ×ℂ Icc 0 b → H (p : ExtPlane) ∈ toExt A →
      Tendsto (vertSeg b x).toFun l (𝓝 p) → ∃ p' ∈ A, Tendsto (h ∘ (vertSeg b x).toFun) l (𝓝 p') := by
    intro l p A hl hpC hFp hpγ
    obtain ⟨p', hp', hpp'⟩ := hFp
    refine ⟨p', hp', ?_⟩
    have hpC' : (p : ExtPlane) ∈ closure (toExt (rectangle a b)) := by
      rw [closure_toExt_rectangle ha hb]
      exact mem_image_of_mem _ hpC
    have h1 := hH.tendsto_comp hpC' ((eventually_mem_set.2 hl).mono fun t ht => hmaps ht)
      ((OnePoint.continuous_coe.tendsto p).comp hpγ)
    rw [← hpp'] at h1
    exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 h1
  refine ⟨⟨h ∘ (vertSeg b x).toFun, locallyLipschitzOn_comp_of_contDiffOn (isOpen_rectangle a b) hC
    isOpen_Ioo (vertSeg b x).locallyLipschitzOn hmaps⟩, ⟨?_, ?_, ?_⟩, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    show h ((vertSeg b x).toFun t) ∈ rectangle a' b'
    rw [← himg]
    exact mem_image_of_mem h (hmaps ht)
  · refine hforth (Ioo_mem_nhdsGT zero_lt_one)
      ⟨hp.1, by show p.im ∈ Icc 0 b; rw [show p.im = 0 from hp.2]; exact ⟨le_rfl, hb.le⟩⟩ ?_ hpγ
    rw [← hbot]
    exact mem_image_of_mem H (mem_image_of_mem _ hp)
  · refine hforth (Ioo_mem_nhdsLT zero_lt_one)
      ⟨hq.1, by show q.im ∈ Icc 0 b; rw [show q.im = b from hq.2]; exact ⟨hb.le, le_rfl⟩⟩ ?_ hqγ
    rw [← htop]
    exact mem_image_of_mem H (mem_image_of_mem _ hq)

/-- (6.10)–(6.12) along vertical segments: the image of `{x + iy : 0 < y < b}` joins the bottom
and top edges of `R'`, so `b' ≤ ∫₀ᵇ (|∂_z h| + |∂_{z̄} h|)(x + iy) dy`. -/
theorem rect_vertSeg_length_le {h : ℂ → ℂ} {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (himg : h '' rectangle a b = rectangle a' b')
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    ENNReal.ofReal b' ≤ ∫⁻ y in Ioo 0 b,
      ENNReal.ofReal (‖dz h ((x : ℂ) + (y : ℂ) * I)‖ + ‖dzbar h ((x : ℂ) + (y : ℂ) * I)‖) := by
  obtain ⟨γ', hγ', hγ'eq⟩ := rect_comp_vertSeg_mem ha hb ha' hb' hC himg hH hv hx
  have hmaps : MapsTo (vertSeg b x).toFun (Ioo 0 1) (rectangle a b) := fun t ht =>
    (vertSeg_mem hb hx).1 (mem_image_of_mem _ ht)
  refine (LRCurve.ofReal_le_rhoLength_one hb' hγ').trans (le_of_le_of_eq ?_
    (vertSeg_rhoLength (x := x) hb (fun z => ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖))))
  unfold LRCurve.rhoLength
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hz := hmaps ht
  have hhd : DifferentiableAt ℝ h ((vertSeg b x).toFun t) :=
    (hC.differentiableOn one_ne_zero).differentiableAt ((isOpen_rectangle a b).mem_nhds hz)
  have hγd : HasDerivAt (vertSeg b x).toFun ((b : ℂ) * I) t := by
    show HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * ((b : ℂ) * I)) ((b : ℂ) * I) t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const ((b : ℂ) * I)).const_add (x : ℂ)
  have hd : deriv γ'.toFun t = fderiv ℝ h ((vertSeg b x).toFun t) ((b : ℂ) * I) := by
    rw [hγ'eq]
    exact (HasFDerivAt.comp_hasDerivAt (x := t) hhd.hasFDerivAt hγd).deriv
  simp only [Pi.one_apply, one_mul]
  rw [hd, hγd.deriv, fderiv_eq_dz_dzbar hhd, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ((norm_add_le _ _).trans (le_of_eq ?_))
  simp only [norm_mul, norm_conj]
  ring

theorem measurable_dz (h : ℂ → ℂ) : Measurable (dz h) :=
  ((measurable_fderiv_apply_const ℝ h (1 : ℂ)).sub
    (measurable_const.mul (measurable_fderiv_apply_const ℝ h I))).div_const 2

theorem measurable_dzbar (h : ℂ → ℂ) : Measurable (dzbar h) :=
  ((measurable_fderiv_apply_const ℝ h (1 : ℂ)).add
    (measurable_const.mul (measurable_fderiv_apply_const ℝ h I))).div_const 2

theorem continuousOn_dz_dzbar {h : ℂ → ℂ} {U : Set ℂ} (hC : ContDiffOn ℝ 1 h U) (hU : IsOpen U) :
    ContinuousOn (dz h) U ∧ ContinuousOn (dzbar h) U := by
  have hd := hC.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun z => fderiv ℝ h z 1) U := hd.clm_apply continuousOn_const
  have hI : ContinuousOn (fun z => fderiv ℝ h z I) U := hd.clm_apply continuousOn_const
  exact ⟨(h1.sub (continuousOn_const.mul hI)).div_const 2,
    (h1.add (continuousOn_const.mul hI)).div_const 2⟩

/-- The integral estimates of the length–area argument for a `C¹` quasiconformal map of
`R(0,a,a+bi,bi)` onto `R(0,a',a'+b'i,b'i)` keeping the vertices (the proof of Theorem 6.1 with the
vertical segments): (6.10)–(6.13), Schwarz's inequality (6.14), and `∬_R J = a'b'`. -/
theorem grotzsch_vertical_integrals {h : ℂ → ℂ} {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) :
    ENNReal.ofReal b' * ENNReal.ofReal a ≤
        ∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) ∧
      (∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖)) ^ 2 ≤
        (∫⁻ z in rectangle a b, ENNReal.ofReal (dilatationQuotient h z)) *
          ∫⁻ z in rectangle a b, ENNReal.ofReal (jacobian h z) ∧
      ∫⁻ z in rectangle a b, ENNReal.ofReal (jacobian h z) =
        ENNReal.ofReal a' * ENNReal.ofReal b' := by
  have hRm : MeasurableSet (rectangle a b) := (isOpen_rectangle a b).measurableSet
  have hdiff : ∀ z ∈ rectangle a b, DifferentiableAt ℝ h z := fun z hz =>
    (hC.differentiableOn one_ne_zero).differentiableAt ((isOpen_rectangle a b).mem_nhds hz)
  have hdzm : Measurable (dz h) :=
    ((measurable_fderiv_apply_const ℝ h (1 : ℂ)).sub
      (measurable_const.mul (measurable_fderiv_apply_const ℝ h I))).div_const 2
  have hdzbarm : Measurable (dzbar h) :=
    ((measurable_fderiv_apply_const ℝ h (1 : ℂ)).add
      (measurable_const.mul (measurable_fderiv_apply_const ℝ h I))).div_const 2
  have hμm : Measurable (complexDilatation h) := hdzbarm.div hdzm
  have hDm : Measurable (dilatationQuotient h) :=
    (measurable_const.add hμm.norm).div (measurable_const.sub hμm.norm)
  have hJm : Measurable (jacobian h) := (hdzm.norm.pow_const 2).sub (hdzbarm.norm.pow_const 2)
  have hρm : Measurable fun z => ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) :=
    ENNReal.measurable_ofReal.comp (hdzm.norm.add hdzbarm.norm)
  have hDeq : ∀ z ∈ rectangle a b,
      dilatationQuotient h z = (‖dz h z‖ + ‖dzbar h z‖) / (‖dz h z‖ - ‖dzbar h z‖) := fun z hz =>
    (ellipse_axes (hlt z hz)).2.2.symm
  have hD0 : ∀ z ∈ rectangle a b, 0 ≤ dilatationQuotient h z := fun z hz => by
    rw [hDeq z hz]
    exact div_nonneg (by positivity) (sub_pos.2 (hlt z hz)).le
  have hJ0 : ∀ z ∈ rectangle a b, 0 < jacobian h z := fun z hz => by
    have := hlt z hz
    unfold jacobian
    nlinarith [norm_nonneg (dzbar h z)]
  have hDJ : ∀ z ∈ rectangle a b,
      dilatationQuotient h z * jacobian h z = (‖dz h z‖ + ‖dzbar h z‖) ^ 2 := fun z hz => by
    rw [hDeq z hz, jacobian, div_mul_eq_mul_div, div_eq_iff (sub_pos.2 (hlt z hz)).ne']
    ring
  -- (6.10)–(6.13)
  have hA : ENNReal.ofReal b' * ENNReal.ofReal a ≤
      ∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) := by
    calc ENNReal.ofReal b' * ENNReal.ofReal a = ∫⁻ _ in Ioo 0 a, ENNReal.ofReal b' := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ ≤ ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b,
            ENNReal.ofReal (‖dz h ((x : ℂ) + (y : ℂ) * I)‖ + ‖dzbar h ((x : ℂ) + (y : ℂ) * I)‖) :=
          setLIntegral_mono' measurableSet_Ioo fun x hx =>
            rect_vertSeg_length_le ha hb ha' hb' hC himg hH hv hx
      _ = ∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) :=
          (setLIntegral_rectangle hρm).symm
  -- Schwarz's inequality (6.14)
  have hB : (∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖)) ^ 2 ≤
      (∫⁻ z in rectangle a b, ENNReal.ofReal (dilatationQuotient h z)) *
        ∫⁻ z in rectangle a b, ENNReal.ofReal (jacobian h z) := by
    have h1 := setLIntegral_mul_sq_le (s := rectangle a b)
      (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hDm))
      (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hJm))
    have e1 : ∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) =
        ∫⁻ z in rectangle a b, ENNReal.ofReal √(dilatationQuotient h z) *
          ENNReal.ofReal √(jacobian h z) := by
      refine setLIntegral_congr_fun hRm fun z hz => ?_
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul (hD0 z hz), hDJ z hz,
        Real.sqrt_sq (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have e2 : ∫⁻ z in rectangle a b, ENNReal.ofReal √(dilatationQuotient h z) ^ 2 =
        ∫⁻ z in rectangle a b, ENNReal.ofReal (dilatationQuotient h z) := by
      refine setLIntegral_congr_fun hRm fun z hz => ?_
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hD0 z hz)]
    have e3 : ∫⁻ z in rectangle a b, ENNReal.ofReal √(jacobian h z) ^ 2 =
        ∫⁻ z in rectangle a b, ENNReal.ofReal (jacobian h z) := by
      refine setLIntegral_congr_fun hRm fun z hz => ?_
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hJ0 z hz).le]
    rw [e1, ← e2, ← e3]
    exact h1
  -- `∬_R J_h = m(R') = a'b'`
  have hJ : ∫⁻ z in rectangle a b, ENNReal.ofReal (jacobian h z) =
      ENNReal.ofReal a' * ENNReal.ofReal b' := by
    have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hRm
      (fun z hz => (hdiff z hz).hasFDerivAt.hasFDerivWithinAt) hinj (fun _ => 1)
    simp only [mul_one, setLIntegral_const, one_mul, himg, volume_rectangle] at hcv
    rw [hcv]
    refine setLIntegral_congr_fun hRm fun z hz => ?_
    have e : (fderiv ℝ h z).det = jacobian h z := det_fderiv_eq_jacobian (hdiff z hz)
    rw [e, abs_of_pos (hJ0 z hz)]
  exact ⟨hA, hB, hJ⟩

/-- The length–area inequality for a `C¹` quasiconformal map of `R(0,a,a+bi,bi)` onto
`R(0,a',a'+b'i,b'i)` keeping the vertices, with `D_h ≤ K`: `a b' ≤ K a' b`
(the proof of Theorem 6.1 with the vertical segments, (6.10)–(6.14)). -/
theorem grotzsch_vertical {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) :
    a * b' ≤ K * (a' * b) := by
  obtain ⟨hA, hB, hJ⟩ := grotzsch_vertical_integrals ha hb ha' hb' hC hinj himg hlt hH hv
  have hRm : MeasurableSet (rectangle a b) := (isOpen_rectangle a b).measurableSet
  have hK0 : 0 ≤ K := by
    have hz0 : (⟨a / 2, b / 2⟩ : ℂ) ∈ rectangle a b :=
      ⟨half_pos ha, half_lt_self ha, half_pos hb, half_lt_self hb⟩
    refine le_trans ?_ (hK _ hz0)
    rw [← (ellipse_axes (hlt _ hz0)).2.2]
    exact div_nonneg (by positivity) (sub_pos.2 (hlt _ hz0)).le
  have hC' : ∫⁻ z in rectangle a b, ENNReal.ofReal (dilatationQuotient h z) ≤
      ENNReal.ofReal K * (ENNReal.ofReal a * ENNReal.ofReal b) := by
    calc ∫⁻ z in rectangle a b, ENNReal.ofReal (dilatationQuotient h z)
        ≤ ∫⁻ _ in rectangle a b, ENNReal.ofReal K :=
          setLIntegral_mono' hRm fun z hz => ENNReal.ofReal_le_ofReal (hK z hz)
      _ = ENNReal.ofReal K * (ENNReal.ofReal a * ENNReal.ofReal b) := by
          rw [setLIntegral_const, volume_rectangle]
  have hchain : ENNReal.ofReal ((b' * a) ^ 2) ≤ ENNReal.ofReal (K * (a * b) * (a' * b')) := by
    rw [ENNReal.ofReal_pow (mul_pos hb' ha).le, ENNReal.ofReal_mul hb'.le,
      ENNReal.ofReal_mul (mul_nonneg hK0 (mul_pos ha hb).le), ENNReal.ofReal_mul hK0,
      ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul ha'.le]
    calc (ENNReal.ofReal b' * ENNReal.ofReal a) ^ 2
        ≤ (∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖)) ^ 2 :=
          pow_le_pow_left' hA 2
      _ ≤ _ := hB
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal a * ENNReal.ofReal b) *
            (ENNReal.ofReal a' * ENNReal.ofReal b') := by
          rw [hJ]
          exact mul_le_mul_left hC' _
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hK0 (mul_pos ha hb).le)
    (mul_pos ha' hb').le)] at hchain
  have hpos : 0 < a * b' := mul_pos ha hb'
  nlinarith

/-! ### Exchanging the roles of the sides: the reflection `z ↦ i z̄` -/

/-- The anti-conformal involution `z ↦ i z̄`, exchanging `R(0,b,b+ai,ai)` and `R(0,a,a+bi,bi)`. -/
def rectSwap (z : ℂ) : ℂ := I * conj z

theorem rectSwap_rectSwap (z : ℂ) : rectSwap (rectSwap z) = z := by
  simp only [rectSwap, map_mul, Complex.conj_I, Complex.conj_conj]
  linear_combination (-z) * I_sq

theorem continuous_rectSwap : Continuous rectSwap :=
  continuous_const.mul Complex.continuous_conj

theorem rectSwap_mem_rectangle {a b : ℝ} {z : ℂ} (hz : z ∈ rectangle b a) :
    rectSwap z ∈ rectangle a b := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hre : (rectSwap z).re = z.im := by simp [rectSwap]
  have him : (rectSwap z).im = z.re := by simp [rectSwap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; exact h3
  · rw [hre]; exact h4
  · rw [him]; exact h1
  · rw [him]; exact h2

theorem rectSwap_image_rectangle {a b : ℝ} : rectSwap '' rectangle b a = rectangle a b := by
  refine subset_antisymm ?_ fun z hz =>
    ⟨rectSwap z, rectSwap_mem_rectangle hz, rectSwap_rectSwap z⟩
  rintro _ ⟨z, hz, rfl⟩
  exact rectSwap_mem_rectangle hz

/-- `z ↦ i z̄` as a homeomorphism of `ℂ`. -/
def rectSwapHomeomorph : ℂ ≃ₜ ℂ where
  toFun := rectSwap
  invFun := rectSwap
  left_inv := rectSwap_rectSwap
  right_inv := rectSwap_rectSwap
  continuous_toFun := continuous_rectSwap
  continuous_invFun := continuous_rectSwap

/-- Conjugating by `z ↦ i z̄` preserves `|∂_z|` and `|∂_{z̄}|`. -/
theorem dz_dzbar_rectSwap_conj {h : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ h (rectSwap z)) :
    dz (rectSwap ∘ h ∘ rectSwap) z = conj (dz h (rectSwap z)) ∧
      dzbar (rectSwap ∘ h ∘ rectSwap) z = -conj (dzbar h (rectSwap z)) := by
  have hσ : ∀ w, HasFDerivAt rectSwap (I • (conjCLE : ℂ →L[ℝ] ℂ)) w := fun w =>
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul I
  have hd' : HasFDerivAt (rectSwap ∘ h ∘ rectSwap)
      ((I • (conjCLE : ℂ →L[ℝ] ℂ)).comp
        ((fderiv ℝ h (rectSwap z)).comp (I • (conjCLE : ℂ →L[ℝ] ℂ)))) z :=
    (hσ _).comp z (hd.hasFDerivAt.comp z (hσ z))
  simp only [dz, dzbar, hd'.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, map_one, Complex.conj_I, map_sub, map_add, map_mul, map_div₀, map_ofNat,
    mul_neg, I_mul_I, neg_neg, mul_one]
  constructor
  · linear_combination (-(conj (fderiv ℝ h (rectSwap z) 1)) / 2) * I_sq
  · linear_combination (conj (fderiv ℝ h (rectSwap z) 1) / 2) * I_sq

/-- `z ↦ i z̄` maps the vertices `0, b, b+ai, ai` to `0, bi, a+bi, a`. -/
theorem rectSwap_rectVert (a b : ℝ) (i : Fin 4) :
    OnePoint.map rectSwap (rectVert b a i) = rectVert a b (-i) := by
  fin_cases i
  · show ((rectSwap 0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
    simp [rectSwap]
  · show ((rectSwap (b : ℂ) : ℂ) : ExtPlane) = (((b : ℂ) * I : ℂ) : ExtPlane)
    rw [rectSwap, Complex.conj_ofReal, mul_comm]
  · show ((rectSwap ((b : ℂ) + (a : ℂ) * I) : ℂ) : ExtPlane) =
      (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane)
    congr 1
    simp only [rectSwap, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(a : ℂ)) * I_sq
  · show ((rectSwap ((a : ℂ) * I) : ℂ) : ExtPlane) = (((a : ℝ) : ℂ) : ExtPlane)
    congr 1
    simp only [rectSwap, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(a : ℂ)) * I_sq

/-- The map `z ↦ i · conj (h (i z̄))` of `R(0,b,b+ai,ai)` onto `R(0,b',b'+a'i,a'i)` satisfies the
hypotheses of the length–area argument whenever `h` does. -/
theorem rectSwap_conj_data {h : ℂ → ℂ} {a b a' b' K : ℝ} (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) :
    ContDiffOn ℝ 1 (rectSwap ∘ h ∘ rectSwap) (rectangle b a) ∧
      InjOn (rectSwap ∘ h ∘ rectSwap) (rectangle b a) ∧
      (rectSwap ∘ h ∘ rectSwap) '' rectangle b a = rectangle b' a' ∧
      (∀ z ∈ rectangle b a,
        ‖dzbar (rectSwap ∘ h ∘ rectSwap) z‖ < ‖dz (rectSwap ∘ h ∘ rectSwap) z‖) ∧
      (∀ z ∈ rectangle b a, dilatationQuotient (rectSwap ∘ h ∘ rectSwap) z ≤ K) ∧
      ∃ H' : ExtPlane → ExtPlane,
        IsHomeoExtension (rectSwap ∘ h ∘ rectSwap) (rectangle b a) (rectangle b' a') H' ∧
        ∀ i, H' (rectVert b a i) = rectVert b' a' i := by
  set e := rectSwapHomeomorph.onePointCongr with he
  have hmaps : MapsTo rectSwap (rectangle b a) (rectangle a b) := fun z hz =>
    rectSwap_mem_rectangle hz
  have hσinj : Function.Injective rectSwap := fun x y hxy => by
    rw [← rectSwap_rectSwap x, hxy, rectSwap_rectSwap]
  have hσC : ContDiff ℝ 1 rectSwap := contDiff_const.mul (conjCLE : ℂ →L[ℝ] ℂ).contDiff
  have hdiff : ∀ z ∈ rectangle b a, DifferentiableAt ℝ h (rectSwap z) := fun z hz =>
    (hC.differentiableOn one_ne_zero).differentiableAt ((isOpen_rectangle a b).mem_nhds (hmaps hz))
  have hnorm : ∀ z ∈ rectangle b a, ‖dz (rectSwap ∘ h ∘ rectSwap) z‖ = ‖dz h (rectSwap z)‖ ∧
      ‖dzbar (rectSwap ∘ h ∘ rectSwap) z‖ = ‖dzbar h (rectSwap z)‖ := fun z hz => by
    obtain ⟨h1, h2⟩ := dz_dzbar_rectSwap_conj (hdiff z hz)
    rw [h1, h2, norm_neg, norm_conj, norm_conj]
    exact ⟨rfl, rfl⟩
  have hlt' : ∀ z ∈ rectangle b a,
      ‖dzbar (rectSwap ∘ h ∘ rectSwap) z‖ < ‖dz (rectSwap ∘ h ∘ rectSwap) z‖ := fun z hz => by
    rw [(hnorm z hz).1, (hnorm z hz).2]
    exact hlt _ (hmaps hz)
  have hK' : ∀ z ∈ rectangle b a, dilatationQuotient (rectSwap ∘ h ∘ rectSwap) z ≤ K :=
    fun z hz => by
      have hq : dilatationQuotient (rectSwap ∘ h ∘ rectSwap) z =
          dilatationQuotient h (rectSwap z) := by
        simp only [dilatationQuotient, complexDilatation, norm_div, (hnorm z hz).1,
          (hnorm z hz).2]
      rw [hq]
      exact hK _ (hmaps hz)
  have himg' : (rectSwap ∘ h ∘ rectSwap) '' rectangle b a = rectangle b' a' := by
    rw [image_comp, image_comp, rectSwap_image_rectangle, himg, rectSwap_image_rectangle]
  have htoExt : ∀ S : Set ℂ, e '' toExt S = toExt (rectSwap '' S) := fun S => by
    unfold toExt
    rw [image_image, image_image]
    rfl
  have hcl1 : e '' closure (toExt (rectangle b a)) = closure (toExt (rectangle a b)) := by
    rw [Homeomorph.image_closure, htoExt, rectSwap_image_rectangle]
  have hcl2 : e '' closure (toExt (rectangle a' b')) = closure (toExt (rectangle b' a')) := by
    rw [Homeomorph.image_closure, htoExt, rectSwap_image_rectangle]
  have hemaps : MapsTo e (closure (toExt (rectangle b a))) (closure (toExt (rectangle a b))) :=
    fun p hp => by rw [← hcl1]; exact mem_image_of_mem e hp
  have hH' : IsHomeoExtension (rectSwap ∘ h ∘ rectSwap) (rectangle b a) (rectangle b' a')
      (e ∘ H ∘ e) := by
    refine ⟨fun z hz => ?_, e.continuous.comp_continuousOn
      (hH.2.1.comp e.continuous.continuousOn hemaps),
      e.injective.injOn.comp (hH.2.2.1.comp e.injective.injOn hemaps) (mapsTo_univ _ _), ?_⟩
    · show e (H (OnePoint.map rectSwap (z : ExtPlane))) = _
      rw [OnePoint.map_some, hH.1 _ (hmaps hz)]
      rfl
    · rw [image_comp, image_comp, hcl1, hH.2.2.2, hcl2]
  have hvert : ∀ i, (e ∘ H ∘ e) (rectVert b a i) = rectVert b' a' i := fun i => by
    show OnePoint.map rectSwap (H (OnePoint.map rectSwap (rectVert b a i))) = _
    rw [rectSwap_rectVert a b i, hv, rectSwap_rectVert b' a', neg_neg]
  exact ⟨hσC.contDiffOn.comp (hC.comp hσC.contDiffOn hmaps) (mapsTo_univ _ _),
    hσinj.injOn.comp (hinj.comp hσinj.injOn hmaps) (mapsTo_univ _ _), himg', hlt', hK', _, hH',
    hvert⟩

/-- The length–area inequality along horizontal segments, `a' b ≤ K a b'`: `grotzsch_vertical`
applied to `z ↦ i · conj (h (i z̄))`, a map of `R(0,b,b+ai,ai)` onto `R(0,b',b'+a'i,a'i)`. -/
theorem grotzsch_horizontal {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) :
    a' * b ≤ K * (a * b') := by
  obtain ⟨hC', hinj', himg', hlt', hK', H', hH', hvert⟩ :=
    rectSwap_conj_data hC hinj himg hlt hK hH hv
  have key := grotzsch_vertical hb ha hb' ha' hC' hinj' himg' hlt' hK' hH' hvert
  linarith

/-- **Theorem 6.2** (Grötzsch).  `K[f] ≥ max(a'b/(ab'), ab'/(a'b))`. -/
theorem thm6_2_grotzsch {f : ℂ → ℂ} {a b a' b' : ℝ} (hf : IsC1QCRectMap f a b a' b') :
    max (a' * b / (a * b')) (a * b' / (a' * b)) ≤ maxDilatationC1 f (rectangle a b) := by
  obtain ⟨ha, hb, ha', hb', ⟨K₀, hK₀⟩, himg, F, hF, hv⟩ := hf
  obtain ⟨-, -, hC, ⟨-, hinj, -, -⟩, hq⟩ := hK₀
  have hbdd : BddAbove (dilatationQuotient f '' rectangle a b) :=
    ⟨K₀, by rintro _ ⟨z, hz, rfl⟩; exact (hq z hz).2⟩
  have hDK : ∀ z ∈ rectangle a b, dilatationQuotient f z ≤ maxDilatationC1 f (rectangle a b) :=
    fun z hz => le_csSup hbdd (mem_image_of_mem _ hz)
  have hlt : ∀ z ∈ rectangle a b, ‖dzbar f z‖ < ‖dz f z‖ := fun z hz => (hq z hz).1
  have h1 := grotzsch_vertical ha hb ha' hb' hC hinj himg hlt hDK hF hv
  have h2 := grotzsch_horizontal ha hb ha' hb' hC hinj himg hlt hDK hF hv
  refine max_le ?_ ?_
  · rw [div_le_iff₀ (mul_pos ha hb')]
    exact h2
  · rw [div_le_iff₀ (mul_pos ha' hb)]
    exact h1

/-! ### Winding-number inputs for Theorem 6.1 (spliced from -2c's Part S development,
sw_partS_scratch.lean and s6_1_scratch.lean): `W2'`, `W5`, `W7` for the `C¹`/jacobian
setting (the general homeomorphism versions live in `Lemmas/Winding.lean`), plus the
open-mapping and `1`-q.c.-from-conformal helpers needed by Theorem 6.1 below. -/

theorem lift_change_circle_eq_two_pi_I_of_jacobian_pos {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : DifferentiableAt ℝ f z₀) (hJ : 0 < jacobian f z₀) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀) →
      L 1 - L 0 = 2 * π * I := by
  have hab : ‖dzbar f z₀‖ < ‖dz f z₀‖ := by
    have := hJ
    rw [jacobian] at this
    nlinarith [norm_nonneg (dzbar f z₀), norm_nonneg (dz f z₀)]
  set a := dz f z₀ with hadef
  set b := dzbar f z₀ with hbdef
  have ha0 : a ≠ 0 := norm_pos_iff.1 ((norm_nonneg b).trans_lt hab)
  set ε : ℝ := (‖a‖ - ‖b‖) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hstrict : HasFDerivAt f (fderiv ℝ f z₀) z₀ := hf.hasFDerivAt
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ x : ℂ, ‖x - z₀‖ < δ →
      ‖f x - f z₀ - fderiv ℝ f z₀ (x - z₀)‖ ≤ ε * ‖x - z₀‖ := by
    have h := hstrict.isLittleO
    rw [Asymptotics.isLittleO_iff] at h
    have hev := h hεpos
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδe⟩ := hev
    refine ⟨δ, hδpos, fun x hx => ?_⟩
    have := hδe (show dist x z₀ < δ by rwa [Complex.dist_eq])
    simpa using this
  refine ⟨δ, hδpos, fun ρ hρpos hρδ L hLcont hLexp => ?_⟩
  set γ : ℝ → ℂ := fun t => f (z₀ + ρ * Complex.exp (2 * π * I * t)) - f z₀ with hγdef
  set β : ℝ → ℂ := fun t => (ρ : ℂ) * (a * Complex.exp (2 * π * I * t) +
    b * Complex.exp (-(2 * π * I * t))) with hβdef
  set α : ℝ → ℂ := fun t => (ρ : ℂ) * a * Complex.exp (2 * π * I * t) with hαdef
  have hγcont : ContinuousOn γ (Icc 0 1) := by
    have heq : Set.EqOn γ (fun t => Complex.exp (L t)) (Icc 0 1) := fun t ht => (hLexp t ht).symm
    exact (Complex.continuous_exp.comp_continuousOn hLcont).congr heq
  have hβcont : ContinuousOn β (Icc 0 1) := by
    fun_prop
  have hαcont : ContinuousOn α (Icc 0 1) := by fun_prop
  have hexp1 : Complex.exp (2 * (π : ℂ) * I * (1 : ℝ)) = 1 := by
    rw [Complex.ofReal_one, mul_one]; exact Complex.exp_two_pi_mul_I
  have hexp0 : Complex.exp (2 * (π : ℂ) * I * (0 : ℝ)) = 1 := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hexpneg1 : Complex.exp (-(2 * (π : ℂ) * I * (1 : ℝ))) = 1 := by
    rw [Complex.exp_neg, hexp1, inv_one]
  have hexpneg0 : Complex.exp (-(2 * (π : ℂ) * I * (0 : ℝ))) = 1 := by
    rw [Complex.exp_neg, hexp0, inv_one]
  have hγ1 : γ 1 = γ 0 := by rw [hγdef]; simp only; rw [hexp1, hexp0]
  have hβ1 : β 1 = β 0 := by
    rw [hβdef]; simp only; rw [hexp1, hexp0, hexpneg1, hexpneg0]
  have hα1 : α 1 = α 0 := by rw [hαdef]; simp only; rw [hexp1, hexp0]
  -- pointwise: `fderiv ℝ f z₀ (x - z₀) = β t` at `x := z₀ + ρ e^{2πit}`
  have hnorm1 : ∀ t : ℝ, ‖Complex.exp (2 * (π : ℂ) * I * (t : ℝ))‖ = 1 := by
    intro t
    have heq : (2 : ℂ) * (π : ℂ) * I * (t : ℝ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [heq]
    exact norm_exp_ofReal_mul_I _
  have hconjexp : ∀ t : ℝ, conj (Complex.exp (2 * (π : ℂ) * I * (t : ℝ))) =
      Complex.exp (-(2 * (π : ℂ) * I * (t : ℝ))) := by
    intro t
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hfd : ∀ t ∈ Icc (0 : ℝ) 1,
      fderiv ℝ f z₀ ((ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ))) = β t := by
    intro t _
    rw [fderiv_eq_dz_dzbar hf, ← hadef, ← hbdef, hβdef]
    simp only [map_mul, Complex.conj_ofReal, hconjexp]
    ring
  have hxnorm : ∀ t : ℝ, ‖(ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ))‖ = ρ := by
    intro t
    rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
  have hδρ : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - β t‖ ≤ ε * ρ := by
    intro t ht
    have hlt : ‖(ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ))‖ < δ := by
      rw [hxnorm]; exact hρδ
    have hb := hδ (z₀ + (ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ))) (by
      rw [show z₀ + (ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) - z₀ =
        (ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) from by ring]
      exact hlt)
    rw [show z₀ + (ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) - z₀ =
      (ρ : ℂ) * Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) from by ring, hfd t ht, hxnorm] at hb
    rw [hγdef]
    simpa using hb
  have hβnorm : ∀ t : ℝ, ‖β t‖ = ρ * ‖a + b * Complex.exp (-(2 * ((2 * π * t : ℝ) : ℂ)) * I)‖ := by
    intro t
    rw [hβdef]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
    congr 1
    have hexpsum : Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) *
        Complex.exp (-(2 * ((2 * π * t : ℝ) : ℂ)) * I) =
        Complex.exp (-(2 * (π : ℂ) * I * (t : ℝ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfactor : a * Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) +
        b * Complex.exp (-(2 * (π : ℂ) * I * (t : ℝ))) =
        Complex.exp (2 * (π : ℂ) * I * (t : ℝ)) *
          (a + b * Complex.exp (-(2 * ((2 * π * t : ℝ) : ℂ)) * I)) := by
      linear_combination (-b) * hexpsum
    rw [hfactor, norm_mul, hnorm1, one_mul]
  have hβlow : ∀ t : ℝ, ρ * (‖a‖ - ‖b‖) ≤ ‖β t‖ := by
    intro t
    rw [hβnorm]
    have hlow := ((ellipse_axes hab).1 (2 * π * t)).2
    exact mul_le_mul_of_nonneg_left hlow hρpos.le
  have hβne : ∀ t ∈ Icc (0 : ℝ) 1, β t ≠ 0 := by
    intro t _ h0
    have := hβlow t
    rw [h0] at this
    simp only [norm_zero] at this
    nlinarith [hab]
  have hclose1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - β t‖ < ‖β t‖ := by
    intro t ht
    calc ‖γ t - β t‖ ≤ ε * ρ := hδρ t ht
      _ = ρ * ((‖a‖ - ‖b‖) / 2) := by rw [hεdef]; ring
      _ < ρ * (‖a‖ - ‖b‖) := by
          apply mul_lt_mul_of_pos_left _ hρpos
          linarith
      _ ≤ ‖β t‖ := hβlow t
  have hnormneg1 : ∀ t : ℝ, ‖Complex.exp (-(2 * (π : ℂ) * I * (t : ℝ)))‖ = 1 := by
    intro t
    have heq : -(2 * (π : ℂ) * I * (t : ℝ)) = ((-(2 * π * t) : ℝ) : ℂ) * I := by push_cast; ring
    rw [heq]; exact norm_exp_ofReal_mul_I _
  have hβαdiff : ∀ t : ℝ, β t - α t = (ρ : ℂ) * b * Complex.exp (-(2 * (π : ℂ) * I * (t : ℝ))) := by
    intro t
    rw [hβdef, hαdef]; simp only; ring
  have hclose2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖β t - α t‖ < ‖α t‖ := by
    intro t _
    rw [hβαdiff, hαdef]
    simp only
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρpos.le, hnormneg1, hnorm1, mul_one, mul_one]
    exact mul_lt_mul_of_pos_left hab hρpos
  obtain ⟨Lβ, hLβcont, hLβexp0⟩ := exists_continuousOn_log_lift hβcont hβne
  have hLβexp : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lβ t) = β t := fun t ht => by
    rw [hLβexp0 t ht, sub_zero]
  have hρane : (ρ : ℂ) * a ≠ 0 := mul_ne_zero (by exact_mod_cast hρpos.ne') ha0
  set Lα : ℝ → ℂ := fun t => Complex.log ((ρ : ℂ) * a) + 2 * (π : ℂ) * I * (t : ℝ) with hLαdef
  have hLαcont : ContinuousOn Lα (Icc 0 1) := by fun_prop
  have hLαexp : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lα t) = α t := by
    intro t _
    rw [hLαdef]
    simp only
    rw [Complex.exp_add, Complex.exp_log hρane, hαdef]
  have hstep1 := lift_change_eq_of_norm_sub_lt hγcont hβcont hγ1 hβ1 hclose1 hLcont hLβcont
    hLexp hLβexp
  have hstep2 := lift_change_eq_of_norm_sub_lt hβcont hαcont hβ1 hα1 hclose2 hLβcont hLαcont
    hLβexp hLαexp
  have hLα10 : Lα 1 - Lα 0 = 2 * π * I := by
    rw [hLαdef]
    simp only
    push_cast
    ring
  rw [hstep1, hstep2, hLα10]

theorem hasDerivAt_mobiusFn {a b c d z : ℂ} (h : c * z + d ≠ 0) :
    HasDerivAt (mobiusFn a b c d) ((a * d - b * c) / (c * z + d) ^ 2) z := by
  have h1 : HasDerivAt (fun w => a * w + b) a z := by
    simpa using (hasDerivAt_id z).const_mul a |>.add_const b
  have h2 : HasDerivAt (fun w => c * w + d) c z := by
    simpa using (hasDerivAt_id z).const_mul c |>.add_const d
  have := h1.div h2 h
  convert this using 1
  · rfl
  · field_simp
    ring

theorem cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos {g : ℂ → ℂ}
    {G : ExtPlane → ExtPlane} (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hgs : g '' upperHalf = upperHalf) {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf)
    (hgd : DifferentiableAt ℝ g z₀) (hJ : 0 < jacobian g z₀) :
    ∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) →
        CyclicStrictMono y := by
  by_cases hinf : G extInf = extInf
  · intro x hx y hy
    have hloc := lift_change_circle_eq_two_pi_I_of_jacobian_pos hgd hJ
    exact cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hG hgs hinf hz₀ hloc x hx y hy
  · have hGfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
      IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hgs hG
    have hinfmem : extInf ∈ frontier (toExt upperHalf) := by
      rw [scExt_frontier_toExt_upperHalf]; exact Or.inr rfl
    have hGinfmem : G extInf ∈ frontier (toExt upperHalf) := hGfr ▸ mem_image_of_mem G hinfmem
    rw [scExt_frontier_toExt_upperHalf] at hGinfmem
    obtain ⟨r, hr⟩ : ∃ r : ℝ, G extInf = (((r : ℝ) : ℂ) : ExtPlane) := by
      rcases hGinfmem with h | h
      · obtain ⟨z, hz, hzeq⟩ := h
        exact ⟨z.re, by rw [← hzeq]; congr 1; exact Complex.ext_iff.2 ⟨rfl, hz⟩⟩
      · exact absurd h hinf
    have hdetM : (0 : ℝ) * (-r) - (-1) * (1 : ℝ) = 1 := by ring
    have hdetMpos : (0 : ℝ) < (0 : ℝ) * (-r) - (-1) * (1 : ℝ) := by rw [hdetM]; norm_num
    have hdetMC : ((0 : ℝ) : ℂ) * ((-r : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
      have h0 : ((0 : ℝ) * (-r) - (-1) * (1 : ℝ) : ℝ) ≠ 0 := hdetMpos.ne'
      exact_mod_cast h0
    set M : ℂ → ℂ := mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) with hMdef
    set E : ExtPlane ≃ₜ ExtPlane :=
      mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) hdetMC with hEdef
    have hEapp : ∀ w : ExtPlane, E w = mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ)
        ((-r : ℝ) : ℂ) w := fun w => rfl
    have hMconf : IsConformalOnto M upperHalf upperHalf := isConformalOnto_mobius_upperHalf hdetMpos
    have hEmaps : ∀ w ∈ upperHalf, E (w : ExtPlane) = ((M w : ℂ) : ExtPlane) := fun w hw => by
      rw [hEapp]
      exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetMpos.ne' hw)
    have hEimg : E '' toExt upperHalf = toExt upperHalf := mobiusExt_image_toExt_upperHalf hdetMpos
    have hgmaps : MapsTo g upperHalf upperHalf := fun z hz => hgs ▸ mem_image_of_mem g hz
    have hMgext : IsHomeoExtension (M ∘ g) upperHalf upperHalf (E ∘ G) :=
      IsHomeoExtension.comp_homeomorph hG hgmaps E hEmaps hEimg
    have hMgs : (M ∘ g) '' upperHalf = upperHalf := by
      rw [image_comp, hgs, hMconf.2.2]
    have hEGinf : (E ∘ G) extInf = extInf := by
      show E (G extInf) = extInf
      rw [hr, hEapp]
      have hden0 : (1 : ℂ) * ((r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) = 0 := by push_cast; ring
      exact mobiusExt_coe_of_eq_zero hden0
    have hgz0mem : g z₀ ∈ upperHalf := hgmaps hz₀
    have hgz0ner : g z₀ ≠ ((r : ℝ) : ℂ) := by
      intro h
      have him : (g z₀).im = 0 := by rw [h]; simp
      have hpos : 0 < (g z₀).im := hgz0mem
      linarith
    have hden : ((1:ℝ) : ℂ) * g z₀ + ((-r : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hgz0ner
      push_cast at h
      linear_combination h
    have hMdiff : DifferentiableAt ℂ M (g z₀) := (hasDerivAt_mobiusFn hden).differentiableAt
    have hMgd : DifferentiableAt ℝ (M ∘ g) z₀ := (hMdiff.restrictScalars ℝ).comp z₀ hgd
    obtain ⟨hdzMg, hdzbarMg⟩ := eq6_5 hgd hMdiff
    have hMderivne : deriv M (g z₀) ≠ 0 := by
      rw [hMdef,
        (hasDerivAt_mobiusFn (a := ((0 : ℝ) : ℂ)) (b := ((-1 : ℝ) : ℂ)) hden).deriv]
      exact div_ne_zero hdetMC (pow_ne_zero 2 hden)
    have hJMg : 0 < jacobian (M ∘ g) z₀ := by
      rw [jacobian, hdzMg, hdzbarMg]
      simp only [norm_mul]
      have hexp : (‖deriv M (g z₀)‖ * ‖dz g z₀‖) ^ 2 - (‖deriv M (g z₀)‖ * ‖dzbar g z₀‖) ^ 2 =
          ‖deriv M (g z₀)‖ ^ 2 * (‖dz g z₀‖ ^ 2 - ‖dzbar g z₀‖ ^ 2) := by ring
      rw [hexp, ← jacobian]
      exact mul_pos (pow_pos (norm_pos_iff.2 hMderivne) 2) hJ
    have hloc' := lift_change_circle_eq_two_pi_I_of_jacobian_pos hMgd hJMg
    have hW5core :=
      cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hMgext hMgs hEGinf hz₀ hloc'
    intro x hx y hy
    have hxi_mem : ∀ i, (((x i : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := by
      intro i
      apply frontier_subset_closure
      rw [scExt_frontier_toExt_upperHalf]
      exact Or.inl ⟨(x i : ℝ), rfl, rfl⟩
    have hinfclos : extInf ∈ closure (toExt upperHalf) := frontier_subset_closure hinfmem
    have hyner : ∀ i, y i ≠ r := by
      intro i heq
      have h1 : G (((x i : ℝ) : ℂ) : ExtPlane) = G extInf := by rw [hy i, heq, hr]
      have h2 := hG.2.2.1 (hxi_mem i) hinfclos h1
      exact OnePoint.coe_ne_infty _ h2
    set y' : Fin 4 → ℝ := fun i => -1 / (y i - r) with hy'def
    have hEGvert : ∀ i, (E ∘ G) (((x i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
      intro i
      show E (G (((x i : ℝ) : ℂ) : ExtPlane)) = _
      rw [hy i, hEapp]
      have hden2 : ((1:ℝ) : ℂ) * ((y i : ℝ) : ℂ) + ((-r : ℝ) : ℂ) ≠ 0 := by
        have hne : (y i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hyner i)
        intro h
        apply hne
        have h' : ((y i - r : ℝ) : ℂ) = 0 := by push_cast at h ⊢; linear_combination h
        exact_mod_cast h'
      rw [mobiusExt_coe hden2]
      congr 1
      show mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) ((y i : ℝ) : ℂ) =
        (((y' i : ℝ)) : ℂ)
      rw [mobiusFn, hy'def]
      simp only
      push_cast
      congr 1 <;> ring
    have hy'cyc : CyclicStrictMono y' := hW5core x hx y' hEGvert
    have hdetInv : (0 : ℝ) < r * 0 - (-1) * 1 := by norm_num
    have hy'ne0 : ∀ i, y' i ≠ 0 := by
      intro i h
      rw [hy'def] at h
      simp only [neg_div, neg_eq_zero, div_eq_zero_iff] at h
      rcases h with h | h
      · norm_num at h
      · exact hyner i (sub_eq_zero.mp h)
    have hMinv : ∀ i, mobiusExt ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        (((y' i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane) := by
      intro i
      have hden3 : ((1:ℝ) : ℂ) * ((y' i : ℝ) : ℂ) + ((0 : ℝ) : ℂ) ≠ 0 := by
        push_cast
        simpa using hy'ne0 i
      rw [mobiusExt_coe hden3]
      congr 1
      show mobiusFn ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((y' i : ℝ) : ℂ) =
        ((y i : ℝ) : ℂ)
      rw [mobiusFn, hy'def]
      simp only
      have hne : (y i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hyner i)
      have hneC : ((y i : ℝ) : ℂ) - ((r : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.2 (hyner i)
      push_cast
      field_simp
      ring
    exact automorphism_upperHalf_preserves_cyclicOrder hdetInv y' hy'cyc y hMinv

theorem cyclicStrictMono_of_conformalOnto_upperHalf {D : Set ℂ} (hD : IsOpen D)
    {φ₁ φ₂ : ℂ → ℂ} {Φ₁ Φ₂ : ExtPlane → ExtPlane}
    (h₁ : IsConformalOnto φ₁ D upperHalf) (hΦ₁ : IsHomeoExtension φ₁ D upperHalf Φ₁)
    (h₂ : IsConformalOnto φ₂ D upperHalf) (hΦ₂ : IsHomeoExtension φ₂ D upperHalf Φ₂)
    {v : Fin 4 → ExtPlane} (hv : ∀ i, v i ∈ closure (toExt D)) {x y : Fin 4 → ℝ}
    (hx : CyclicStrictMono x) (hvx : ∀ i, Φ₁ (v i) = (((x i : ℝ) : ℂ) : ExtPlane))
    (hvy : ∀ i, Φ₂ (v i) = (((y i : ℝ) : ℂ) : ExtPlane)) :
    CyclicStrictMono y := by
  set ψ : ℂ → ℂ := Function.invFunOn φ₁ D with hψdef
  have hψconf : IsConformalOnto ψ upperHalf D := h₁.symm hD
  set g : ℂ → ℂ := φ₂ ∘ ψ with hgdef
  set Ginv : ExtPlane → ExtPlane := Function.invFunOn Φ₁ (closure (toExt D)) with hGinvdef
  have hΨinvExt : IsHomeoExtension ψ upperHalf D Ginv := isHomeoExtension_invFunOn h₁ hΦ₁
  set G : ExtPlane → ExtPlane := Φ₂ ∘ Ginv with hGdef
  have hGext : IsHomeoExtension g upperHalf upperHalf G :=
    IsHomeoExtension.comp hΦ₂ hΨinvExt hψconf.mapsTo
  have hgs : g '' upperHalf = upperHalf := by
    rw [hgdef, image_comp, hψconf.2.2, h₂.2.2]
  have hz₀mem : (I : ℂ) ∈ upperHalf := by simp [upperHalf]
  have hψId : DifferentiableAt ℂ ψ I :=
    hψconf.1.differentiableAt (scExt_isOpen_upperHalf.mem_nhds hz₀mem)
  have hψIdom : ψ I ∈ D := hψconf.mapsTo hz₀mem
  have hφ2d : DifferentiableAt ℂ φ₂ (ψ I) := h₂.1.differentiableAt (hD.mem_nhds hψIdom)
  have hgdiffOn : DifferentiableOn ℂ g upperHalf := h₂.1.comp hψconf.1 hψconf.mapsTo
  have hginj : InjOn g upperHalf := h₂.2.1.comp hψconf.2.1 hψconf.mapsTo
  have hgdAtC : DifferentiableAt ℂ g I :=
    hgdiffOn.differentiableAt (scExt_isOpen_upperHalf.mem_nhds hz₀mem)
  have hgd : DifferentiableAt ℝ g I := hgdAtC.restrictScalars ℝ
  have hgdzbar : dzbar g I = 0 := (cauchyRiemann_iff.1 hgdAtC).2
  have hgderivne : deriv g I ≠ 0 :=
    deriv_ne_zero_of_injOn scExt_isOpen_upperHalf hgdiffOn hginj hz₀mem
  have hgdz : dz g I = deriv g I := dz_eq_deriv hgdAtC
  have hJg : 0 < jacobian g I := by
    rw [jacobian, hgdz, hgdzbar, norm_zero]
    have h0 : (0:ℝ) < ‖deriv g I‖ := norm_pos_iff.2 hgderivne
    nlinarith [sq_nonneg (0:ℝ)]
  have hW5 := cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos hGext hgs hz₀mem hgd hJg
  have hGxy : ∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane) := by
    intro i
    show Φ₂ (Ginv (((x i : ℝ) : ℂ) : ExtPlane)) = _
    rw [← hvx i, hGinvdef, hΦ₁.2.2.1.leftInvOn_invFunOn (hv i)]
    exact hvy i
  exact hW5 x hx y hGxy

theorem isOpen_image_of_jacobian_pos {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hJ : ∀ z ∈ U, 0 < jacobian f z) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hfd : DifferentiableAt ℝ f z :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)
  have hcda : ContDiffAt ℝ 1 f z := hf.contDiffAt (hU.mem_nhds hz)
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f z) z := hcda.hasStrictFDerivAt (by norm_num)
  have hdetne : LinearMap.det ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    rw [det_fderiv_eq_jacobian hfd]
    exact (hJ z hz).ne'
  set e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfDetNeZero ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) hdetne).toContinuousLinearEquiv
    with hedef
  have heeq : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := ContinuousLinearMap.ext fun x => rfl
  have hstrict' : HasStrictFDerivAt f (e : ℂ →L[ℝ] ℂ) z := heeq ▸ hstrict
  have hmap : map f (𝓝 z) = 𝓝 (f z) := hstrict'.map_nhds_eq_of_equiv
  rw [← hmap]
  exact Filter.image_mem_map (hU.mem_nhds hz)

theorem isC1Quasiconformal_of_isConformalOnto {φ : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hφ : IsConformalOnto φ U V) : IsC1Quasiconformal φ U 1 := by
  have hd := hφ.1
  have hinj := hφ.2.1
  have himg := hφ.2.2
  have hdzbar : ∀ z ∈ U, dzbar φ z = 0 :=
    fun z hz => (cauchyRiemann_iff.1 (hd.differentiableAt (hU.mem_nhds hz))).2
  have hdz : ∀ z ∈ U, dz φ z = deriv φ z :=
    fun z hz => dz_eq_deriv (hd.differentiableAt (hU.mem_nhds hz))
  have hdne : ∀ z ∈ U, deriv φ z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hU hd hinj hz
  have hsymm : IsConformalOnto (Function.invFunOn φ U) V U := hφ.symm hU
  refine ⟨hU, le_refl 1, ?_, ⟨hd.continuousOn, hinj, rfl, ?_⟩, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℂ (⊤ : ℕ∞) φ U := (hd.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
    exact (h1.restrict_scalars ℝ).of_le (by exact_mod_cast le_top)
  · rw [himg]; exact hsymm.1.continuousOn
  · have hzpos : 0 < ‖dz φ z‖ := by rw [hdz z hz]; exact norm_pos_iff.2 (hdne z hz)
    have h1 : ‖dzbar φ z‖ = 0 := by rw [hdzbar z hz]; simp
    refine ⟨by rw [h1]; exact hzpos, ?_⟩
    have hμ : complexDilatation φ z = 0 := by rw [complexDilatation, hdzbar z hz]; simp
    rw [dilatationQuotient, hμ]; norm_num

/-! ## §6.6 Theorem 6.1 -/

/-- **Theorem 6.1** (共形模的拟不变性).  If `f : D → D'` is a `C¹` quasiconformal map with
`D_f ≤ K`, then for every quadrilateral `Q` with `Q̄ ⊆ D` the image `f(Q)(f(z₁),…,f(z₄))` is a
quadrilateral and `M(Q)/K ≤ M(f(Q)) ≤ K M(Q)`. -/
theorem thm6_1_modulus_quasi_invariance {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsC1Quasiconformal f D K) (Q : TopQuad) (hQ : closure (toExt Q.dom) ⊆ toExt D) :
    ∃ Q' : TopQuad, Q.IsImageUnder Q' f ∧ Q.modulus / K ≤ Q'.modulus ∧
      Q'.modulus ≤ K * Q.modulus := by
  obtain ⟨hD, hK1, hfC, hfhom, hfq⟩ := hf
  have hQdomD : Q.dom ⊆ D := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hQ (subset_closure (mem_image_of_mem _ hz))
    rw [← OnePoint.coe_injective hwz]; exact hw
  have hQopen : IsOpen Q.dom := Q.isTopQuad.1.1
  have hfCQ : ContDiffOn ℝ 1 f Q.dom := hfC.mono hQdomD
  have hJpos : ∀ z ∈ Q.dom, 0 < jacobian f z := by
    intro z hz
    have hlt := (hfq z (hQdomD hz)).1
    rw [jacobian]
    nlinarith [norm_nonneg (dzbar f z)]
  have hfo : IsOpen (f '' Q.dom) := isOpen_image_of_jacobian_pos hQopen hfCQ hJpos
  obtain ⟨hfQJD, hfQext, hfQfr⟩ :=
    image_isJordanDomain_of_open hD hfhom.1 hfhom.2.1 hQ hfo
  have hfQclosD : closure (toExt (f '' Q.dom)) ⊆ toExt (f '' D) :=
    closure_toExt_image_subset hfhom.1 hQ (subset_refl _)
  have hfQbdd : Bornology.IsBounded (f '' Q.dom) := by
    apply isBounded_of_extInf_notMem_closure_toExt
    intro hmem
    exact extInf_notMem_toExt (f '' D) (hfQclosD hmem)
  obtain ⟨φ'0, hφ'0, Φ'0, hΦ'0⟩ :=
    exists_conformalOnto_upperHalf_of_isJordanDomain hfQJD hfQbdd
  set v : Fin 4 → ExtPlane := fun i => OnePoint.map f (Q.vert i) with hvdef
  have hvfr : ∀ i, v i ∈ frontier (toExt (f '' Q.dom)) := fun i =>
    hfQfr ▸ mem_image_of_mem _ (Q.isTopQuad.2.1 i)
  obtain ⟨φ', Φ', x', hφ', hΦ', hx'⟩ :=
    exists_uniformizer_finite_vertices hfo hφ'0 hΦ'0 hvfr
  -- step (B): orientation
  obtain ⟨hQJ, hQv, φQ, ΦQ, x, hφQ, hΦQ, hxcyc, hxQ⟩ := Q.isTopQuad
  set ψ : ℂ → ℂ := Function.invFunOn φQ Q.dom with hψdef
  have hψconf : IsConformalOnto ψ upperHalf Q.dom := hφQ.symm hQopen
  set g : ℂ → ℂ := φ' ∘ f ∘ ψ with hgdef
  obtain ⟨z1, hz1⟩ := hQJ.2.1.nonempty
  set z₀ : ℂ := φQ z1 with hz₀def
  have hz₀mem : z₀ ∈ upperHalf := hφQ.2.2 ▸ mem_image_of_mem φQ hz1
  have hψz₀ : ψ z₀ = z1 := hφQ.2.1.leftInvOn_invFunOn hz1
  have hψd : DifferentiableAt ℂ ψ z₀ :=
    hψconf.1.differentiableAt (scExt_isOpen_upperHalf.mem_nhds hz₀mem)
  have hfd1 : DifferentiableAt ℝ f z1 :=
    (hfCQ.differentiableOn one_ne_zero).differentiableAt (hQopen.mem_nhds hz1)
  have hφ'd : DifferentiableAt ℂ φ' (f z1) := by
    have hmem : f z1 ∈ f '' Q.dom := mem_image_of_mem f hz1
    exact hφ'.1.differentiableAt (hfo.mem_nhds hmem)
  have hψder_ne : deriv ψ z₀ ≠ 0 :=
    deriv_ne_zero_of_injOn scExt_isOpen_upperHalf hψconf.1 hψconf.2.1 hz₀mem
  have hφ'der_ne : deriv φ' (f z1) ≠ 0 :=
    deriv_ne_zero_of_injOn hfo hφ'.1 hφ'.2.1 (mem_image_of_mem f hz1)
  obtain ⟨hdz1, hdzbar1⟩ := eq6_4 hψd (hψz₀ ▸ hfd1)
  have hfψd : DifferentiableAt ℝ (f ∘ ψ) z₀ := (hψz₀ ▸ hfd1).comp z₀ (hψd.restrictScalars ℝ)
  have hfψz₀ : (f ∘ ψ) z₀ = f z1 := by rw [Function.comp_apply, hψz₀]
  have hφ'd' : DifferentiableAt ℂ φ' ((f ∘ ψ) z₀) := hfψz₀ ▸ hφ'd
  obtain ⟨hdz2, hdzbar2⟩ := eq6_5 hfψd hφ'd'
  have hgeq : g = φ' ∘ (f ∘ ψ) := rfl
  have hgd : DifferentiableAt ℝ g z₀ := by
    rw [hgeq]
    exact hφ'd'.restrictScalars ℝ |>.comp z₀ hfψd
  have hdzg : dz g z₀ = deriv φ' (f z1) * (dz f z1 * deriv ψ z₀) := by
    rw [hgeq, hdz2, hfψz₀, hdz1, hψz₀]
  have hdzbarg : dzbar g z₀ = deriv φ' (f z1) * (dzbar f z1 * conj (deriv ψ z₀)) := by
    rw [hgeq, hdzbar2, hfψz₀, hdzbar1, hψz₀]
  have hJf1 : 0 < jacobian f z1 := hJpos z1 hz1
  have hJg : 0 < jacobian g z₀ := by
    rw [jacobian, hdzg, hdzbarg]
    simp only [norm_mul, Complex.norm_conj]
    have h1 : (0:ℝ) < ‖deriv φ' (f z1)‖ ^ 2 := by positivity
    have h2 : (0:ℝ) < ‖deriv ψ z₀‖ ^ 2 := by positivity
    have hexp : (‖deriv φ' (f z1)‖ * (‖dz f z1‖ * ‖deriv ψ z₀‖)) ^ 2 -
        (‖deriv φ' (f z1)‖ * (‖dzbar f z1‖ * ‖deriv ψ z₀‖)) ^ 2 =
        ‖deriv φ' (f z1)‖ ^ 2 * ‖deriv ψ z₀‖ ^ 2 * (‖dz f z1‖ ^ 2 - ‖dzbar f z1‖ ^ 2) := by ring
    rw [hexp, ← jacobian]
    exact mul_pos (mul_pos h1 h2) hJf1
  set Ginv : ExtPlane → ExtPlane := Function.invFunOn ΦQ (closure (toExt Q.dom)) with hGinvdef
  have hΦQinjC : InjOn ΦQ (closure (toExt Q.dom)) := hΦQ.2.2.1
  set G : ExtPlane → ExtPlane := Φ' ∘ (OnePoint.map f) ∘ Ginv with hGdef
  have hGdef' : G = Φ' ∘ ((OnePoint.map f) ∘ Ginv) := rfl
  have hGinvExt : IsHomeoExtension ψ upperHalf Q.dom Ginv := isHomeoExtension_invFunOn hφQ hΦQ
  have hstep1 : IsHomeoExtension (f ∘ ψ) upperHalf (f '' Q.dom) ((OnePoint.map f) ∘ Ginv) :=
    IsHomeoExtension.comp hfQext hGinvExt hψconf.mapsTo
  have hfψmaps : MapsTo (f ∘ ψ) upperHalf (f '' Q.dom) :=
    fun z hz => mem_image_of_mem f (hψconf.mapsTo hz)
  have hGext : IsHomeoExtension g upperHalf upperHalf G := by
    rw [hgeq, hGdef']
    exact IsHomeoExtension.comp hΦ' hstep1 hfψmaps
  have hgs : g '' upperHalf = upperHalf := by
    rw [hgeq, image_comp, image_comp, hψconf.2.2, hφ'.2.2]
  have hGvert : ∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((x' i : ℝ) : ℂ) : ExtPlane) := by
    intro i
    show Φ' (OnePoint.map f (Ginv (((x i : ℝ) : ℂ) : ExtPlane))) = _
    rw [← hxQ i, hGinvdef]
    have hQvi : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    rw [hΦQinjC.leftInvOn_invFunOn hQvi]
    exact hx' i
  have hW5 := cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos hGext hgs hz₀mem hgd hJg
  have hx'cyc : CyclicStrictMono x' := hW5 x hxcyc x' hGvert
  set Q' : TopQuad := ⟨f '' Q.dom, v, hfQJD, hvfr, φ', Φ', x', hφ', hΦ', hx'cyc, hx'⟩ with hQ'def
  have hQ'Image : Q.IsImageUnder Q' f := ⟨rfl, fun i => rfl⟩
  -- step (C): modulus, via rectangles and Grötzsch
  obtain ⟨a, b, ρ, ha, hb, hρconf, Ψρ, hΨρext, hΨρv⟩ := thm1_1_exists_rectangle Q
  obtain ⟨a', b', ρ', ha', hb', hρ'conf, Ψρ', hΨρ'ext, hΨρ'v⟩ := thm1_1_exists_rectangle Q'
  have hQmod : Q.modulus = a / b := modulus_eq_of_equivRect Q ⟨ρ, ha, hb, hρconf, Ψρ, hΨρext, hΨρv⟩
  have hQ'mod : Q'.modulus = a' / b' :=
    modulus_eq_of_equivRect Q' ⟨ρ', ha', hb', hρ'conf, Ψρ', hΨρ'ext, hΨρ'v⟩
  set ρinv : ℂ → ℂ := Function.invFunOn ρ Q.dom with hρinvdef
  have hρinvconf : IsConformalOnto ρinv (rectangle a b) Q.dom := hρconf.symm hQopen
  have hρ1qc : IsC1Quasiconformal ρinv (rectangle a b) 1 :=
    isC1Quasiconformal_of_isConformalOnto (isOpen_rectangle a b) hρinvconf
  have hfQC1 : IsC1Quasiconformal f Q.dom K := by
    refine ⟨hQopen, hK1, hfCQ, ?_, fun z hz => hfq z (hQdomD hz)⟩
    refine ⟨hfhom.1.mono hQdomD, hfhom.2.1.mono hQdomD, rfl, ?_⟩
    have heq : Set.EqOn (Function.invFunOn f Q.dom) (Function.invFunOn f D) (f '' Q.dom) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [(hfhom.2.1.mono hQdomD).leftInvOn_invFunOn hz, hfhom.2.1.leftInvOn_invFunOn (hQdomD hz)]
    exact (hfhom.2.2.2.mono (image_mono hQdomD)).congr heq
  have hρ'1qc : IsC1Quasiconformal ρ' (f '' Q.dom) 1 :=
    isC1Quasiconformal_of_isConformalOnto hfo hρ'conf
  have hcomp1 : IsC1Quasiconformal (f ∘ ρinv) (rectangle a b) (K * 1) :=
    c1qc_comp hρ1qc hfQC1 (le_of_eq hρinvconf.2.2)
  have hcomp2 : IsC1Quasiconformal (ρ' ∘ (f ∘ ρinv)) (rectangle a b) (1 * (K * 1)) := by
    refine c1qc_comp hcomp1 hρ'1qc ?_
    rw [image_comp, hρinvconf.2.2]
  set F : ℂ → ℂ := ρ' ∘ f ∘ ρinv with hFdef
  have hFeq : F = ρ' ∘ (f ∘ ρinv) := rfl
  have hFqc : IsC1Quasiconformal F (rectangle a b) K := by
    rw [hFeq, show K = 1 * (K * 1) by ring]
    exact hcomp2
  have hFimg : F '' rectangle a b = rectangle a' b' := by
    rw [hFeq, image_comp, image_comp, hρinvconf.2.2, hρ'conf.2.2]
  have hΨρinvExt : IsHomeoExtension ρinv (rectangle a b) Q.dom
      (Function.invFunOn Ψρ (closure (toExt Q.dom))) := isHomeoExtension_invFunOn hρconf hΨρext
  have hstepF1 : IsHomeoExtension (f ∘ ρinv) (rectangle a b) (f '' Q.dom)
      ((OnePoint.map f) ∘ (Function.invFunOn Ψρ (closure (toExt Q.dom)))) :=
    IsHomeoExtension.comp hfQext hΨρinvExt hρinvconf.mapsTo
  have hfρinvmaps : MapsTo (f ∘ ρinv) (rectangle a b) (f '' Q.dom) :=
    fun z hz => mem_image_of_mem f (hρinvconf.mapsTo hz)
  set Ψ : ExtPlane → ExtPlane :=
    Ψρ' ∘ (OnePoint.map f) ∘ (Function.invFunOn Ψρ (closure (toExt Q.dom))) with hΨdef
  have hΨext : IsHomeoExtension F (rectangle a b) (rectangle a' b') Ψ := by
    rw [hFeq, hΨdef]
    exact IsHomeoExtension.comp hΨρ'ext hstepF1 hfρinvmaps
  have hΨv : ∀ i, Ψ (rectVert a b i) = rectVert a' b' i := by
    intro i
    show Ψρ' (OnePoint.map f (Function.invFunOn Ψρ (closure (toExt Q.dom)) (rectVert a b i))) = _
    rw [← hΨρv i]
    have hQvi : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    rw [hΨρext.2.2.1.leftInvOn_invFunOn hQvi]
    exact hΨρ'v i
  have hFrectmap : IsC1QCRectMap F a b a' b' := ⟨ha, hb, ha', hb', ⟨K, hFqc⟩, hFimg, Ψ, hΨext, hΨv⟩
  have hgrotzsch := thm6_2_grotzsch hFrectmap
  have hFbdd : BddAbove (dilatationQuotient F '' rectangle a b) :=
    ⟨K, by rintro _ ⟨z, hz, rfl⟩; exact (hFqc.2.2.2.2 z hz).2⟩
  have hne : (rectangle a b).Nonempty := by
    refine ⟨(a / 2 : ℝ) + (b / 2 : ℝ) * I, ?_⟩
    have hre : ((a / 2 : ℝ) + (b / 2 : ℝ) * I).re = a / 2 := by simp
    have him : ((a / 2 : ℝ) + (b / 2 : ℝ) * I).im = b / 2 := by simp
    simp only [rectangle, mem_setOf_eq, hre, him]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hmaxle : maxDilatationC1 F (rectangle a b) ≤ K :=
    csSup_le (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact (hFqc.2.2.2.2 z hz).2)
  have hboth := hgrotzsch.trans hmaxle
  rw [max_le_iff] at hboth
  obtain ⟨hb1, hb2⟩ := hboth
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hb1' : a' * b ≤ K * (a * b') := by
    rw [div_le_iff₀ (mul_pos ha hb')] at hb1; linarith
  have hb2' : a * b' ≤ K * (a' * b) := by
    rw [div_le_iff₀ (mul_pos ha' hb)] at hb2; linarith
  refine ⟨Q', hQ'Image, ?_, ?_⟩
  · rw [hQmod, hQ'mod, div_div, div_le_div_iff₀ (mul_pos hb hK0) hb']
    nlinarith [hb2']
  · rw [hQmod, hQ'mod, show K * (a / b) = (K * a) / b from (mul_div_assoc K a b).symm,
      div_le_div_iff₀ hb' hb]
    nlinarith [hb1']

/-! ### The equality case of Grötzsch's theorem -/

/-- A nonnegative function continuous on an open set `U` with vanishing integral over `U` is zero
on `U`. -/
theorem eqOn_zero_of_setLIntegral_ofReal_eq_zero {φ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hφm : Measurable φ) (hφc : ContinuousOn φ U) (hφ0 : ∀ z ∈ U, 0 ≤ φ z)
    (h : ∫⁻ z in U, ENNReal.ofReal (φ z) = 0) : ∀ z ∈ U, φ z = 0 := by
  have h' := (lintegral_eq_zero_iff (f := fun z => ENNReal.ofReal (φ z))
    (ENNReal.measurable_ofReal.comp hφm)).1 h
  have heq := Measure.eqOn_open_of_ae_eq h' hU
    (ENNReal.continuous_ofReal.comp_continuousOn hφc) continuousOn_const
  intro z hz
  have h1 := heq hz
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (hφ0 z hz)

/-- The dilatation quotient of `½(α + β) z + ½(α - β) z̄` (`α, β > 0`) is `max(α/β, β/α)`. -/
theorem dilatationQuotient_affine_real {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (z : ℂ) :
    dilatationQuotient (fun z => (1 / 2 : ℂ) * ((α + β : ℝ) : ℂ) * z +
      (1 / 2 : ℂ) * ((α - β : ℝ) : ℂ) * conj z) z = max (α / β) (β / α) := by
  have hA : (1 / 2 : ℂ) * ((α + β : ℝ) : ℂ) = (((α + β) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hB : (1 / 2 : ℂ) * ((α - β : ℝ) : ℂ) = (((α - β) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hpos : 0 < (α + β) / 2 := by positivity
  have hlt : ‖(((α - β) / 2 : ℝ) : ℂ)‖ < ‖(((α + β) / 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hpos, abs_lt]
    constructor <;> linarith
  have e := ((affine_isC1Quasiconformal (C := 0) hlt).2 z).2
  simp only [add_zero] at e
  rw [hA, hB, e, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hpos]
  rcases le_total β α with hle | hle
  · rw [abs_of_nonneg (by linarith : 0 ≤ (α - β) / 2), max_eq_left,
      show (α + β) / 2 + (α - β) / 2 = α by ring, show (α + β) / 2 - (α - β) / 2 = β by ring]
    rw [div_le_div_iff₀ hα hβ]
    nlinarith
  · rw [abs_of_nonpos (by linarith : (α - β) / 2 ≤ 0), max_eq_right,
      show (α + β) / 2 + -((α - β) / 2) = β by ring, show (α + β) / 2 - -((α - β) / 2) = α by ring]
    rw [div_le_div_iff₀ hβ hα]
    nlinarith

/-- Along a vertical segment the image curve rises by `b'`:
`b' ≤ ∫₀ᵇ Re(∂_z h - ∂_{z̄} h)(x + iy) dy`. -/
theorem rect_vertSeg_im_le {h : ℂ → ℂ} {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (himg : h '' rectangle a b = rectangle a' b')
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    ENNReal.ofReal b' ≤ ∫⁻ y in Ioo 0 b,
      ENNReal.ofReal (dz h ((x : ℂ) + (y : ℂ) * I) - dzbar h ((x : ℂ) + (y : ℂ) * I)).re := by
  obtain ⟨γ', hγ', hγ'eq⟩ := rect_comp_vertSeg_mem ha hb ha' hb' hC himg hH hv hx
  have hmaps : MapsTo (vertSeg b x).toFun (Ioo 0 1) (rectangle a b) := fun t ht =>
    (vertSeg_mem hb hx).1 (mem_image_of_mem _ ht)
  refine (LRCurve.ofReal_le_lintegral_im_deriv hb' hγ').trans (le_of_le_of_eq ?_
    (vertSeg_rhoLength (x := x) hb (fun z => ENNReal.ofReal (dz h z - dzbar h z).re)))
  unfold LRCurve.rhoLength
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hz := hmaps ht
  have hhd : DifferentiableAt ℝ h ((vertSeg b x).toFun t) :=
    (hC.differentiableOn one_ne_zero).differentiableAt ((isOpen_rectangle a b).mem_nhds hz)
  have hγd : HasDerivAt (vertSeg b x).toFun ((b : ℂ) * I) t := by
    show HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * ((b : ℂ) * I)) ((b : ℂ) * I) t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const ((b : ℂ) * I)).const_add (x : ℂ)
  have hd : deriv γ'.toFun t = fderiv ℝ h ((vertSeg b x).toFun t) ((b : ℂ) * I) := by
    rw [hγ'eq]
    exact (HasFDerivAt.comp_hasDerivAt (x := t) hhd.hasFDerivAt hγd).deriv
  show ENNReal.ofReal (deriv γ'.toFun t).im ≤
    ENNReal.ofReal (dz h ((vertSeg b x).toFun t) - dzbar h ((vertSeg b x).toFun t)).re *
      ‖deriv (vertSeg b x).toFun t‖ₑ
  have hre : (dz h ((vertSeg b x).toFun t) * ((b : ℂ) * I) +
      dzbar h ((vertSeg b x).toFun t) * conj ((b : ℂ) * I)).im =
      b * (dz h ((vertSeg b x).toFun t) - dzbar h ((vertSeg b x).toFun t)).re := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_im, mul_re, ofReal_re, ofReal_im,
      I_re, I_im, neg_re, neg_im, sub_re, add_im]
    ring
  rw [hd, hγd.deriv, fderiv_eq_dz_dzbar hhd, hre, ENNReal.ofReal_mul hb.le,
    show ‖(b : ℂ) * I‖ₑ = ENNReal.ofReal b by
      rw [← ofReal_norm, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hb.le],
    mul_comm (ENNReal.ofReal b)]

theorem ennreal_eq_zero_of_add_le_self {x y : ℝ≥0∞} (hx : x ≠ ⊤) (h : x + y ≤ x) : y = 0 :=
  le_antisymm ((ENNReal.add_le_add_iff_left hx).1 (by rwa [add_zero])) zero_le

/-- The equality case of the length–area argument: if `K a'b = ab'` then `D_h = K` and
`|∂_z h| + |∂_{z̄} h| = b'/b` everywhere in `R` (equality in (6.10)–(6.14)). -/
theorem grotzsch_vertical_eq_aux {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) (hKeq : K * (a' * b) = a * b') :
    ∀ z ∈ rectangle a b, dilatationQuotient h z = K ∧ ‖dz h z‖ + ‖dzbar h z‖ = b' / b := by
  obtain ⟨hA, -, hJ⟩ := grotzsch_vertical_integrals ha hb ha' hb' hC hinj himg hlt hH hv
  have hRo := isOpen_rectangle a b
  have hRm : MeasurableSet (rectangle a b) := hRo.measurableSet
  obtain ⟨hdzc, hdzbarc⟩ := continuousOn_dz_dzbar hC hRo
  have hdzm := measurable_dz h
  have hdzbarm := measurable_dzbar h
  have hJm : Measurable (jacobian h) := (hdzm.norm.pow_const 2).sub (hdzbarm.norm.pow_const 2)
  have hgm : Measurable fun z => ‖dz h z‖ + ‖dzbar h z‖ := hdzm.norm.add hdzbarm.norm
  have hDeq : ∀ z ∈ rectangle a b,
      dilatationQuotient h z = (‖dz h z‖ + ‖dzbar h z‖) / (‖dz h z‖ - ‖dzbar h z‖) := fun z hz =>
    (ellipse_axes (hlt z hz)).2.2.symm
  have hJ0 : ∀ z ∈ rectangle a b, 0 < jacobian h z := fun z hz => by
    have := hlt z hz
    unfold jacobian
    nlinarith [norm_nonneg (dzbar h z)]
  have hD0 : ∀ z ∈ rectangle a b, 0 ≤ dilatationQuotient h z := fun z hz => by
    rw [hDeq z hz]
    exact div_nonneg (by positivity) (sub_pos.2 (hlt z hz)).le
  have hDJ : ∀ z ∈ rectangle a b,
      dilatationQuotient h z * jacobian h z = (‖dz h z‖ + ‖dzbar h z‖) ^ 2 := fun z hz => by
    rw [hDeq z hz, jacobian, div_mul_eq_mul_div, div_eq_iff (sub_pos.2 (hlt z hz)).ne']
    ring
  have hK0 : 0 ≤ K := by
    have hz0 : (⟨a / 2, b / 2⟩ : ℂ) ∈ rectangle a b :=
      ⟨half_pos ha, half_lt_self ha, half_pos hb, half_lt_self hb⟩
    exact (hD0 _ hz0).trans (hK _ hz0)
  have hJc : ContinuousOn (jacobian h) (rectangle a b) :=
    (hdzc.norm.pow 2).sub (hdzbarc.norm.pow 2)
  have hgc : ContinuousOn (fun z => ‖dz h z‖ + ‖dzbar h z‖) (rectangle a b) :=
    hdzc.norm.add hdzbarc.norm
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = a' / a := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; exact div_pos ha' ha
  have hta : t * a = a' := by rw [ht_def]; exact div_mul_cancel₀ a' ha.ne'
  have hg0 : ∀ z ∈ rectangle a b, 0 ≤ ‖dz h z‖ + ‖dzbar h z‖ := fun z _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  -- `2 t g ≤ t² D + J`
  have hamgm : ∀ z ∈ rectangle a b, 0 ≤ t ^ 2 * dilatationQuotient h z + jacobian h z -
      2 * t * (‖dz h z‖ + ‖dzbar h z‖) := fun z hz => by
    have h4 : t ^ 2 * (dilatationQuotient h z * jacobian h z) =
        t ^ 2 * (‖dz h z‖ + ‖dzbar h z‖) ^ 2 := by rw [hDJ z hz]
    nlinarith [sq_nonneg (t * (‖dz h z‖ + ‖dzbar h z‖) - jacobian h z), hJ0 z hz]
  have hΦ0 : ∀ z ∈ rectangle a b,
      0 ≤ t ^ 2 * K + jacobian h z - 2 * t * (‖dz h z‖ + ‖dzbar h z‖) := fun z hz => by
    nlinarith [hamgm z hz, hK z hz, sq_nonneg t]
  have hΦm : Measurable fun z => t ^ 2 * K + jacobian h z - 2 * t * (‖dz h z‖ + ‖dzbar h z‖) :=
    (measurable_const.add hJm).sub (measurable_const.mul hgm)
  have hΦc : ContinuousOn
      (fun z => t ^ 2 * K + jacobian h z - 2 * t * (‖dz h z‖ + ‖dzbar h z‖)) (rectangle a b) :=
    (continuousOn_const.add hJc).sub (continuousOn_const.mul hgc)
  have h2t : (0 : ℝ) ≤ 2 * t := mul_nonneg two_pos.le ht.le
  have htK : 0 ≤ t ^ 2 * K := mul_nonneg (sq_nonneg t) hK0
  have hsplit : (∫⁻ z in rectangle a b, ENNReal.ofReal (2 * t * (‖dz h z‖ + ‖dzbar h z‖))) +
      ∫⁻ z in rectangle a b,
        ENNReal.ofReal (t ^ 2 * K + jacobian h z - 2 * t * (‖dz h z‖ + ‖dzbar h z‖)) =
      ENNReal.ofReal (t ^ 2 * K) * (ENNReal.ofReal a * ENNReal.ofReal b) +
        ENNReal.ofReal a' * ENNReal.ofReal b' := by
    rw [← lintegral_add_left (f := fun z => ENNReal.ofReal (2 * t * (‖dz h z‖ + ‖dzbar h z‖)))
        (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm)),
      ← volume_rectangle a b, ← setLIntegral_const, ← hJ,
      ← lintegral_add_left (f := fun _ => ENNReal.ofReal (t ^ 2 * K)) measurable_const]
    refine setLIntegral_congr_fun hRm fun z hz => ?_
    rw [← ENNReal.ofReal_add (mul_nonneg h2t (hg0 z hz)) (hΦ0 z hz),
      ← ENNReal.ofReal_add htK (hJ0 z hz).le]
    congr 1
    ring
  have hlow : ENNReal.ofReal (2 * t) * (ENNReal.ofReal b' * ENNReal.ofReal a) ≤
      ∫⁻ z in rectangle a b, ENNReal.ofReal (2 * t * (‖dz h z‖ + ‖dzbar h z‖)) := by
    calc ENNReal.ofReal (2 * t) * (ENNReal.ofReal b' * ENNReal.ofReal a)
        ≤ ENNReal.ofReal (2 * t) *
            ∫⁻ z in rectangle a b, ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖) := by gcongr
      _ = _ := by
        rw [← lintegral_const_mul (f := fun z => ENNReal.ofReal (‖dz h z‖ + ‖dzbar h z‖)) _
          (ENNReal.measurable_ofReal.comp hgm)]
        refine setLIntegral_congr_fun hRm fun z hz => ?_
        rw [← ENNReal.ofReal_mul h2t]
  have hnum : t ^ 2 * K * (a * b) + a' * b' = 2 * t * (b' * a) := by
    linear_combination (t * K * b - b') * hta + t * hKeq
  have hN : ENNReal.ofReal (t ^ 2 * K) * (ENNReal.ofReal a * ENNReal.ofReal b) +
      ENNReal.ofReal a' * ENNReal.ofReal b' =
      ENNReal.ofReal (2 * t) * (ENNReal.ofReal b' * ENNReal.ofReal a) := by
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul ha'.le, ← ENNReal.ofReal_mul hb'.le,
      ← ENNReal.ofReal_mul htK, ← ENNReal.ofReal_mul h2t,
      ← ENNReal.ofReal_add (mul_nonneg htK (mul_pos ha hb).le) (mul_pos ha' hb').le, hnum]
  have hfin : ENNReal.ofReal (t ^ 2 * K) * (ENNReal.ofReal a * ENNReal.ofReal b) +
      ENNReal.ofReal a' * ENNReal.ofReal b' ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hX : ∫⁻ z in rectangle a b, ENNReal.ofReal (2 * t * (‖dz h z‖ + ‖dzbar h z‖)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_self_add.trans hsplit.le)
  have hY := ennreal_eq_zero_of_add_le_self hX (hsplit.le.trans (hN.le.trans hlow))
  have hΦz := eqOn_zero_of_setLIntegral_ofReal_eq_zero hRo hΦm hΦc hΦ0 hY
  intro z hz
  have hΦ : t ^ 2 * K + jacobian h z - 2 * t * (‖dz h z‖ + ‖dzbar h z‖) = 0 := hΦz z hz
  have hA0 := hamgm z hz
  have hKD := hK z hz
  have hDK : dilatationQuotient h z = K := by nlinarith [mul_pos ht ht]
  refine ⟨hDK, ?_⟩
  have hJg : K * jacobian h z = (‖dz h z‖ + ‖dzbar h z‖) ^ 2 := by rw [← hDK]; exact hDJ z hz
  have hsq : (t * K - (‖dz h z‖ + ‖dzbar h z‖)) ^ 2 = 0 := by
    linear_combination K * hΦ - hJg
  have hg : ‖dz h z‖ + ‖dzbar h z‖ = t * K := by
    have := (pow_eq_zero_iff two_ne_zero).1 hsq
    linarith
  rw [hg, eq_div_iff hb.ne']
  refine mul_right_cancel₀ ha.ne' ?_
  linear_combination (K * b) * hta + hKeq

theorem convex_rectangle (a b : ℝ) : Convex ℝ (rectangle a b) := by
  rw [rectangle_eq_reProdIm]
  exact ((convex_Ioo 0 a).linear_preimage Complex.reLm).inter
    ((convex_Ioo 0 b).linear_preimage Complex.imLm)

/-- In the equality case `∂_z h` and `∂_{z̄} h` are the real constants `½(a'/a ± b'/b)`: the images
of the vertical segments rise vertically (equality in (6.10) and (6.12)). -/
theorem grotzsch_vertical_eq_derivs {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) (hKeq : K * (a' * b) = a * b') :
    ∀ z ∈ rectangle a b, dz h z = (((a' / a + b' / b) / 2 : ℝ) : ℂ) ∧
      dzbar h z = (((a' / a - b' / b) / 2 : ℝ) : ℂ) := by
  have hDg := grotzsch_vertical_eq_aux ha hb ha' hb' hC hinj himg hlt hK hH hv hKeq
  have hRo := isOpen_rectangle a b
  have hRm : MeasurableSet (rectangle a b) := hRo.measurableSet
  obtain ⟨hdzc, hdzbarc⟩ := continuousOn_dz_dzbar hC hRo
  have hdzm := measurable_dz h
  have hdzbarm := measurable_dzbar h
  have hpos : 0 < b' / b := div_pos hb' hb
  have hr_le : ∀ z ∈ rectangle a b, (dz h z - dzbar h z).re ≤ b' / b := fun z hz => by
    rw [← (hDg z hz).2]
    exact (Complex.re_le_norm _).trans (norm_sub_le _ _)
  have hrm : Measurable fun z => (dz h z - dzbar h z).re :=
    Complex.measurable_re.comp (hdzm.sub hdzbarm)
  have hφm : Measurable fun z => b' / b - max (dz h z - dzbar h z).re 0 :=
    measurable_const.sub (hrm.max measurable_const)
  have hφc : ContinuousOn (fun z => b' / b - max (dz h z - dzbar h z).re 0) (rectangle a b) :=
    continuousOn_const.sub
      (ContinuousOn.sup (Complex.continuous_re.comp_continuousOn (hdzc.sub hdzbarc))
        continuousOn_const)
  have hφ0 : ∀ z ∈ rectangle a b, 0 ≤ b' / b - max (dz h z - dzbar h z).re 0 := fun z hz =>
    sub_nonneg.2 (max_le (hr_le z hz) hpos.le)
  have hlow : ENNReal.ofReal b' * ENNReal.ofReal a ≤
      ∫⁻ z in rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0) := by
    calc ENNReal.ofReal b' * ENNReal.ofReal a = ∫⁻ _ in Ioo 0 a, ENNReal.ofReal b' := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ ≤ ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b,
            ENNReal.ofReal (dz h ((x : ℂ) + (y : ℂ) * I) - dzbar h ((x : ℂ) + (y : ℂ) * I)).re :=
          setLIntegral_mono' measurableSet_Ioo fun x hx =>
            rect_vertSeg_im_le ha hb ha' hb' hC himg hH hv hx
      _ = ∫⁻ z in rectangle a b, ENNReal.ofReal (dz h z - dzbar h z).re :=
          (setLIntegral_rectangle (ENNReal.measurable_ofReal.comp hrm)).symm
      _ = ∫⁻ z in rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0) := by
          congr 1
          funext z
          rcases le_total (dz h z - dzbar h z).re 0 with hr | hr
          · rw [max_eq_right hr, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hr]
          · rw [max_eq_left hr]
  have hpt : ∀ z ∈ rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0) +
      ENNReal.ofReal (b' / b - max (dz h z - dzbar h z).re 0) = ENNReal.ofReal (b' / b) :=
    fun z hz => by rw [← ENNReal.ofReal_add (le_max_right _ _) (hφ0 z hz), add_sub_cancel]
  have hsplit : (∫⁻ z in rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0)) +
      ∫⁻ z in rectangle a b, ENNReal.ofReal (b' / b - max (dz h z - dzbar h z).re 0) =
      ENNReal.ofReal b' * ENNReal.ofReal a := by
    calc (∫⁻ z in rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0)) +
          ∫⁻ z in rectangle a b, ENNReal.ofReal (b' / b - max (dz h z - dzbar h z).re 0)
        = ∫⁻ z in rectangle a b, (ENNReal.ofReal (max (dz h z - dzbar h z).re 0) +
            ENNReal.ofReal (b' / b - max (dz h z - dzbar h z).re 0)) :=
          (lintegral_add_left (f := fun z => ENNReal.ofReal (max (dz h z - dzbar h z).re 0))
            (ENNReal.measurable_ofReal.comp (hrm.max measurable_const)) _).symm
      _ = ∫⁻ _ in rectangle a b, ENNReal.ofReal (b' / b) := setLIntegral_congr_fun hRm hpt
      _ = ENNReal.ofReal b' * ENNReal.ofReal a := by
          rw [setLIntegral_const, volume_rectangle, ← ENNReal.ofReal_mul ha.le,
            ← ENNReal.ofReal_mul hpos.le, ← ENNReal.ofReal_mul hb'.le]
          congr 1
          rw [div_mul_eq_mul_div, div_eq_iff hb.ne']
          ring
  have hX : ∫⁻ z in rectangle a b, ENNReal.ofReal (max (dz h z - dzbar h z).re 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (le_self_add.trans hsplit.le)
  have hY := ennreal_eq_zero_of_add_le_self hX (hsplit.le.trans hlow)
  have hφz := eqOn_zero_of_setLIntegral_ofReal_eq_zero hRo hφm hφc hφ0 hY
  intro z hz
  obtain ⟨hDK, hgz⟩ := hDg z hz
  have hφ : b' / b - max (dz h z - dzbar h z).re 0 = 0 := hφz z hz
  have hr : (dz h z - dzbar h z).re = b' / b := by
    rcases le_total (dz h z - dzbar h z).re 0 with h1 | h1
    · rw [max_eq_right h1] at hφ
      linarith
    · rw [max_eq_left h1] at hφ
      linarith
  rw [sub_re] at hr
  have h1 := Complex.re_le_norm (dz h z)
  have h2 : -(dzbar h z).re ≤ ‖dzbar h z‖ := by
    have := Complex.re_le_norm (-dzbar h z)
    rwa [neg_re, norm_neg] at this
  have hpre : (dz h z).re = ‖dz h z‖ := by linarith
  have hqre : (dzbar h z).re = -‖dzbar h z‖ := by linarith
  have hpim : (dz h z).im = 0 := by
    have h3 := Complex.sq_norm (dz h z)
    rw [Complex.normSq_apply, ← hpre] at h3
    exact mul_self_eq_zero.1 (by nlinarith)
  have hqim : (dzbar h z).im = 0 := by
    have h3 := Complex.sq_norm (dzbar h z)
    rw [Complex.normSq_apply, hqre] at h3
    exact mul_self_eq_zero.1 (by nlinarith)
  have hlt' := hlt z hz
  have hE : (‖dz h z‖ + ‖dzbar h z‖) / (‖dz h z‖ - ‖dzbar h z‖) = K :=
    (ellipse_axes hlt').2.2.trans hDK
  have hKpos : 0 < K := by
    rw [← hE]
    exact div_pos (by linarith [norm_nonneg (dzbar h z)]) (sub_pos.2 hlt')
  rw [div_eq_iff (sub_pos.2 hlt').ne'] at hE
  have hKa : K * (a' / a) = b' / b := by
    rw [mul_div_assoc', div_eq_div_iff ha.ne' hb.ne']
    linear_combination hKeq
  have hd : ‖dz h z‖ - ‖dzbar h z‖ = a' / a := by
    apply mul_left_cancel₀ hKpos.ne'
    rw [hKa, ← hE, hgz]
  constructor
  · apply Complex.ext
    · simp only [ofReal_re]
      rw [hpre]
      linarith
    · simp only [ofReal_im]
      exact hpim
  · apply Complex.ext
    · simp only [ofReal_re]
      rw [hqre]
      linarith
    · simp only [ofReal_im]
      exact hqim

/-- The equality case along the vertical segments: `h` is the affine map
`½(a'/a + b'/b) z + ½(a'/a - b'/b) z̄` on `R`. -/
theorem grotzsch_vertical_eq {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) (hKeq : K * (a' * b) = a * b') :
    ∀ z ∈ rectangle a b, h z = (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
      (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z := by
  have hder := grotzsch_vertical_eq_derivs ha hb ha' hb' hC hinj himg hlt hK hH hv hKeq
  set L : ℂ → ℂ := fun z => (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
    (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z with hL
  have hRo := isOpen_rectangle a b
  have hdiff : ∀ z ∈ rectangle a b, DifferentiableAt ℝ h z := fun z hz =>
    (hC.differentiableOn one_ne_zero).differentiableAt (hRo.mem_nhds hz)
  have hLd : ∀ z, HasFDerivAt L (((1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ)) •
      ContinuousLinearMap.id ℝ ℂ + ((1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ)) •
        (conjCLE : ℂ →L[ℝ] ℂ)) z := fun z =>
    ((hasFDerivAt_id z).const_mul _).add ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul _)
  have hzero : ∀ z ∈ rectangle a b, fderiv ℝ (fun w => h w - L w) z = 0 := fun z hz => by
    show fderiv ℝ (h - L) z = 0
    rw [fderiv_sub (hdiff z hz) (hLd z).differentiableAt, (hLd z).fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
      fderiv_eq_dz_dzbar (hdiff z hz), (hder z hz).1, (hder z hz).2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply]
    push_cast
    ring
  have hconst : ∀ z ∈ rectangle a b, ∀ w ∈ rectangle a b, h z - L z = h w - L w :=
    fun z hz w hw => by
      have hdo : DifferentiableOn ℝ (fun w => h w - L w) (rectangle a b) := fun u hu =>
        ((hdiff u hu).sub (hLd u).differentiableAt).differentiableWithinAt
      exact (convex_rectangle a b).is_const_of_fderivWithin_eq_zero hdo
        (fun u hu => by rw [fderivWithin_of_isOpen hRo hu, hzero u hu]) hz hw
  have hz₀ : (⟨a / 2, b / 2⟩ : ℂ) ∈ rectangle a b :=
    ⟨half_pos ha, half_lt_self ha, half_pos hb, half_lt_self hb⟩
  obtain ⟨C, hC_def⟩ : ∃ C, C = h ⟨a / 2, b / 2⟩ - L ⟨a / 2, b / 2⟩ := ⟨_, rfl⟩
  have hhL : ∀ z ∈ rectangle a b, h z = L z + C := fun z hz => by
    have h1 := hconst z hz _ hz₀
    linear_combination h1 - hC_def
  have hmemR : ∀ᶠ z in 𝓝[rectangle a b] (0 : ℂ), z ∈ rectangle a b := self_mem_nhdsWithin
  have h0cl : (0 : ℂ) ∈ closure (rectangle a b) := by
    rw [rectangle_eq_reProdIm, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]
    exact ⟨⟨le_rfl, ha.le⟩, ⟨le_rfl, hb.le⟩⟩
  haveI : (𝓝[rectangle a b] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h0cl
  have hlimH : Tendsto h (𝓝[rectangle a b] 0) (𝓝 0) := by
    have hp : ((0 : ℂ) : ExtPlane) ∈ closure (toExt (rectangle a b)) := by
      rw [closure_toExt_rectangle ha hb]
      exact mem_image_of_mem _ ⟨⟨le_rfl, ha.le⟩, ⟨le_rfl, hb.le⟩⟩
    have h1 := hH.tendsto_comp hp hmemR
      ((OnePoint.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds)
    have h0 : H ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := hv 0
    rw [h0] at h1
    exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 h1
  have hlimL : Tendsto (fun z => L z + C) (𝓝[rectangle a b] 0) (𝓝 C) := by
    have hL0 : L 0 = 0 := by simp [hL]
    have h1 : Tendsto (fun z => L z + C) (𝓝 (0 : ℂ)) (𝓝 (L 0 + C)) :=
      ((continuous_iff_continuousAt.2 fun z => (hLd z).continuousAt).add
        (continuous_const (y := C))).tendsto (0 : ℂ)
    rw [hL0, zero_add] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hC0 : C = 0 :=
    tendsto_nhds_unique (hlimL.congr' (hmemR.mono fun z hz => (hhL z hz).symm)) hlimH
  intro z hz
  rw [hhL z hz, hC0, add_zero, hL]

/-- The equality case along the horizontal segments (via `z ↦ i z̄`): if `K a b' = a' b` then `h`
is the affine map `½(a'/a + b'/b) z + ½(a'/a - b'/b) z̄` on `R`. -/
theorem grotzsch_horizontal_eq {h : ℂ → ℂ} {a b a' b' K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hC : ContDiffOn ℝ 1 h (rectangle a b))
    (hinj : InjOn h (rectangle a b)) (himg : h '' rectangle a b = rectangle a' b')
    (hlt : ∀ z ∈ rectangle a b, ‖dzbar h z‖ < ‖dz h z‖)
    (hK : ∀ z ∈ rectangle a b, dilatationQuotient h z ≤ K)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h (rectangle a b) (rectangle a' b') H)
    (hv : ∀ i, H (rectVert a b i) = rectVert a' b' i) (hKeq : K * (a * b') = a' * b) :
    ∀ z ∈ rectangle a b, h z = (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
      (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z := by
  obtain ⟨hC', hinj', himg', hlt', hK', H', hH', hvert⟩ :=
    rectSwap_conj_data hC hinj himg hlt hK hH hv
  have key := grotzsch_vertical_eq hb ha hb' ha' hC' hinj' himg' hlt' hK' hH' hvert
    (by linear_combination hKeq)
  intro w hw
  have e2 : h w = rectSwap ((rectSwap ∘ h ∘ rectSwap) (rectSwap w)) := by
    simp only [Function.comp_apply, rectSwap_rectSwap]
  rw [e2, key (rectSwap w) (rectSwap_mem_rectangle hw)]
  simp only [rectSwap, map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj,
    Complex.conj_I, neg_neg, map_div₀, map_one, map_ofNat]
  push_cast
  linear_combination (-(1 / 2) * ((a' : ℂ) / a + (b' : ℂ) / b) * w +
    (1 / 2) * ((b' : ℂ) / b - (a' : ℂ) / a) * conj w) * I_sq

/-- **Theorem 6.2** (equality case): equality holds iff `f` is the affine map
`f(z) = ½(a'/a + b'/b) z + ½(a'/a - b'/b) z̄`. -/
theorem thm6_2_grotzsch_eq_iff {f : ℂ → ℂ} {a b a' b' : ℝ} (hf : IsC1QCRectMap f a b a' b') :
    maxDilatationC1 f (rectangle a b) = max (a' * b / (a * b')) (a * b' / (a' * b)) ↔
      ∀ z ∈ rectangle a b,
        f z = (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
          (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z := by
  obtain ⟨ha, hb, ha', hb', ⟨K₀, hK₀⟩, himg, F, hF, hv⟩ := hf
  obtain ⟨-, -, hC, ⟨-, hinj, -, -⟩, hq⟩ := hK₀
  have hbdd : BddAbove (dilatationQuotient f '' rectangle a b) :=
    ⟨K₀, by rintro _ ⟨z, hz, rfl⟩; exact (hq z hz).2⟩
  have hDK : ∀ z ∈ rectangle a b, dilatationQuotient f z ≤ maxDilatationC1 f (rectangle a b) :=
    fun z hz => le_csSup hbdd (mem_image_of_mem _ hz)
  have hlt : ∀ z ∈ rectangle a b, ‖dzbar f z‖ < ‖dz f z‖ := fun z hz => (hq z hz).1
  constructor
  · intro hK
    rcases le_total (a * b' / (a' * b)) (a' * b / (a * b')) with hle | hle
    · -- `K[f] = a'b/(ab')`: equality along the horizontal segments
      rw [max_eq_left hle] at hK
      refine grotzsch_horizontal_eq ha hb ha' hb' hC hinj himg hlt hDK hF hv ?_
      rw [hK, div_mul_cancel₀ _ (mul_pos ha hb').ne']
    · -- `K[f] = ab'/(a'b)`: equality along the vertical segments
      rw [max_eq_right hle] at hK
      refine grotzsch_vertical_eq ha hb ha' hb' hC hinj himg hlt hDK hF hv ?_
      rw [hK, div_mul_cancel₀ _ (mul_pos ha' hb).ne']
  · intro hEq
    have hα : 0 < a' / a := div_pos ha' ha
    have hβ : 0 < b' / b := div_pos hb' hb
    have hDz : ∀ z ∈ rectangle a b,
        dilatationQuotient f z = max (a' * b / (a * b')) (a * b' / (a' * b)) := fun z hz => by
      have hev : f =ᶠ[𝓝 z] fun z => (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
          (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z :=
        Filter.eventuallyEq_of_mem ((isOpen_rectangle a b).mem_nhds hz) hEq
      have hfd := hev.fderiv_eq (𝕜 := ℝ)
      have e : dilatationQuotient f z = dilatationQuotient (fun z =>
          (1 / 2 : ℂ) * ((a' / a + b' / b : ℝ) : ℂ) * z +
            (1 / 2 : ℂ) * ((a' / a - b' / b : ℝ) : ℂ) * conj z) z := by
        simp only [dilatationQuotient, complexDilatation, dz, dzbar, hfd]
      rw [e, dilatationQuotient_affine_real hα hβ, div_div_div_eq, div_div_div_eq]
      congr 1
      ring
    have hne : (rectangle a b).Nonempty :=
      ⟨⟨a / 2, b / 2⟩, half_pos ha, half_lt_self ha, half_pos hb, half_lt_self hb⟩
    have himD : dilatationQuotient f '' rectangle a b =
        {max (a' * b / (a * b')) (a * b' / (a' * b))} := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hDz z hz
      · intro hw
        rw [mem_singleton_iff] at hw
        obtain ⟨z, hz⟩ := hne
        exact ⟨z, hz, (hDz z hz).trans hw.symm⟩
    show sSup (dilatationQuotient f '' rectangle a b) = _
    rw [himD, csSup_singleton]

end LiZhongQC
