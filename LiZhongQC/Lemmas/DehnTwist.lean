import LiZhongQC.Lemmas.DehnTwistGeometry

/-!
# Proposed M2 contracts for the Dehn-twist programme

STATIC ONLY: UNFROZEN, UNELABORATED, and UNPROVED. The imported M1 module is
archive-only. No new global definition, structure, instance, or axiom is proposed.
All geometric objects are existential witnesses or explicit parameters.
The local model F is deliberately not asserted to be a global lift of T.
-/

open Set Filter Topology
open scoped UpperHalfPlane
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

/-- A smooth profile with the prescribed tails has globally bounded derivative:
the derivative is continuous on the compact transition interval and zero off it. -/
theorem s28m_model_profile {a : ℝ} (ha : 0 < a) :
    ∃ (ρ : ℝ → ℝ) (C : ℝ), ContDiff ℝ 1 ρ ∧ 0 ≤ C ∧
      (∀ t : ℝ, |deriv ρ t| ≤ C) ∧ (∀ t : ℝ, 0 ≤ ρ t ∧ ρ t ≤ 1) ∧
      (∀ t : ℝ, t ≤ -a → ρ t = 0) ∧ (∀ t : ℝ, a ≤ t → ρ t = 1) := by
  let ρ : ℝ → ℝ := fun t => Real.smoothTransition ((t + a) / (2 * a))
  have hρ : ContDiff ℝ 1 ρ := by
    change ContDiff ℝ 1 (fun t => Real.smoothTransition ((t + a) / (2 * a)))
    exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)
  have hleft : ∀ t : ℝ, t ≤ -a → ρ t = 0 := by
    intro t ht
    change Real.smoothTransition ((t + a) / (2 * a)) = 0
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have hright : ∀ t : ℝ, a ≤ t → ρ t = 1 := by
    intro t ht
    change Real.smoothTransition ((t + a) / (2 * a)) = 1
    apply Real.smoothTransition.one_of_one_le
    exact (one_le_div (by positivity : 0 < 2 * a)).2 (by linarith)
  obtain ⟨D, hD⟩ := ((isCompact_Icc : IsCompact (Icc (-a) a)).image
    hρ.continuous_deriv_one.abs).isBounded.bddAbove
  refine ⟨ρ, max 0 D, hρ, le_max_left _ _, ?_, ?_, hleft, hright⟩
  · intro t
    by_cases ht : t ∈ Icc (-a) a
    · exact (hD ⟨t, ht, rfl⟩).trans (le_max_right _ _)
    · have hzero : deriv ρ t = 0 := by
        rcases lt_or_ge t (-a) with hlt | hge
        · have heq : ρ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
            filter_upwards [Iio_mem_nhds hlt] with u hu
            exact hleft u hu.le
          simpa only [deriv_const] using heq.deriv_eq
        · have hgt : a < t := by
            by_contra h
            exact ht ⟨hge, le_of_not_gt h⟩
          have heq : ρ =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hgt] with u hu
            exact hright u hu.le
          simpa only [deriv_const] using heq.deriv_eq
      rw [hzero, abs_zero]
      exact le_max_left _ _
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- **Profile and shear witnesses.** In coordinates t = Re(w)/Im(w), the map
w |-> exp(k log(l) rho(t)) w preserves t. Thus the inverse is the shear at -k,
even without monotonicity of rho. The profile is C1 and constant on both tails.
The explicit derivative bound makes the later QC estimate uniform on H. -/
theorem s28m_twist_model {l a : ℝ} (hl : 1 < l) (ha : 0 < a) :
    ∃ (ρ : ℝ → ℝ) (C : ℝ) (F : ℤ → (ℍ ≃ₜ ℍ)),
      ContDiff ℝ 1 ρ ∧ 0 ≤ C ∧ (∀ t : ℝ, |deriv ρ t| ≤ C) ∧
      (∀ t : ℝ, 0 ≤ ρ t ∧ ρ t ≤ 1) ∧
      (∀ t : ℝ, t ≤ -a → ρ t = 0) ∧
      (∀ t : ℝ, a ≤ t → ρ t = 1) ∧
      F 0 = Homeomorph.refl ℍ ∧
      (∀ (m n : ℤ) (w : ℍ), F (m + n) w = F m (F n w)) ∧
      (∀ (k : ℤ) (w : ℍ), ((F k w : ℍ) : ℂ) =
        (Real.exp ((k : ℝ) * Real.log l * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ)) := by
  -- The exponential shear construction itself works for any real log(l).
  -- The frozen hl is retained; it supplies the geometric dilation elsewhere.
  have _h := hl
  obtain ⟨ρ, C, hρ, hC, hderiv, hrange, hleft, hright⟩ := s28m_model_profile ha
  obtain ⟨D, hD, hDc⟩ := s28m_far_scale
  let A : ℝ → ℍ → ℍ := fun u w => D (u * ρ ((w : ℂ).re / w.im)) w
  have hformula : ∀ (u : ℝ) (w : ℍ), ((A u w : ℍ) : ℂ) =
      (Real.exp (u * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ) := by
    intro u w
    exact hD _ w
  have hratio : ∀ (u : ℝ) (w : ℍ), (A u w : ℂ).re / (A u w).im =
      (w : ℂ).re / w.im := by
    intro u w
    change (A u w : ℂ).re / (A u w : ℂ).im = (w : ℂ).re / (w : ℂ).im
    rw [hformula, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    exact mul_div_mul_left _ _ (Real.exp_ne_zero _)
  have hzero : ∀ w : ℍ, A 0 w = w := by
    intro w
    apply UpperHalfPlane.coe_injective
    rw [hformula, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  have hadd : ∀ (u v : ℝ) (w : ℍ), A (u + v) w = A u (A v w) := by
    intro u v w
    apply UpperHalfPlane.coe_injective
    rw [hformula (u + v) w, hformula u (A v w), hratio v w, hformula v w]
    rw [add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc]
  have hc : ∀ u : ℝ, Continuous (A u) := by
    intro u
    have ht : Continuous (fun w : ℍ => (w : ℂ).re / w.im) :=
      UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im
        (fun w => w.im_pos.ne')
    exact hDc.comp ((continuous_const.mul (hρ.continuous.comp ht)).prodMk continuous_id)
  let F : ℤ → (ℍ ≃ₜ ℍ) := fun k =>
    { toEquiv :=
        { toFun := A ((k : ℝ) * Real.log l)
          invFun := A (-((k : ℝ) * Real.log l))
          left_inv := fun w => by
            rw [← hadd, neg_add_cancel]
            exact hzero w
          right_inv := fun w => by
            rw [← hadd, add_neg_cancel]
            exact hzero w }
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  refine ⟨ρ, C, F, hρ, hC, hderiv, hrange, hleft, hright, ?_, ?_, ?_⟩
  · apply Homeomorph.ext
    intro w
    change A (((0 : ℤ) : ℝ) * Real.log l) w = w
    rw [Int.cast_zero, zero_mul]
    exact hzero w
  · intro m n w
    change A (((m + n : ℤ) : ℝ) * Real.log l) w =
      A ((m : ℝ) * Real.log l) (A ((n : ℝ) * Real.log l) w)
    rw [Int.cast_add, add_mul]
    exact hadd _ _ _
  · intro k w
    exact hformula _ w

/-- The constant tails and bounded derivative give a global shear bound. -/
theorem s28m_twist_profile_shear_bound {a C : ℝ} (ha : 0 < a)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hC : 0 ≤ C)
    (hderiv : ∀ t : ℝ, |deriv ρ t| ≤ C)
    (hleft : ∀ t : ℝ, t ≤ -a → ρ t = 0)
    (hright : ∀ t : ℝ, a ≤ t → ρ t = 1)
    (A t : ℝ) :
    |A * deriv ρ t| * (1 + t ^ 2) ≤ |A| * C * (1 + a ^ 2) := by
  -- The tail argument is local constancy; the frozen C1 premise is not needed here.
  have _hρ := hρ
  by_cases ht : |t| ≤ a
  · have hsq : t ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    rw [abs_mul]
    have h1 := mul_le_mul_of_nonneg_left (hderiv t) (abs_nonneg A)
    have h2 := mul_le_mul_of_nonneg_left (show 1 + t ^ 2 ≤ 1 + a ^ 2 by linarith)
      (mul_nonneg (abs_nonneg A) hC)
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
  · have hzero : deriv ρ t = 0 := by
      have hout : t < -a ∨ a < t := by
        rcases lt_abs.mp (lt_of_not_ge ht) with h | h
        · exact Or.inr h
        · exact Or.inl (by linarith)
      rcases hout with hleft' | hright'
      · have heq : ρ =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
          filter_upwards [Iio_mem_nhds hleft'] with x hx
          exact hleft x (le_of_lt hx)
        rw [heq.deriv_eq, deriv_const]
      · have heq : ρ =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
          filter_upwards [Ioi_mem_nhds hright'] with x hx
          exact hright x (le_of_lt hx)
        rw [heq.deriv_eq, deriv_const]
    rw [hzero]
    simp only [mul_zero, abs_zero, zero_mul]
    positivity

/-- Real C1 regularity only on the genuine upper-half-plane domain. -/
theorem s28m_twist_formula_contDiffOn {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (A : ℝ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ upperHalf, f z =
      (Real.exp (A * ρ (z.re / z.im)) : ℂ) * z) :
    ContDiffOn ℝ 1 f upperHalf := by
  have ht : ContDiffOn ℝ 1 (fun z : ℂ => z.re / z.im) upperHalf :=
    Complex.reCLM.contDiff.contDiffOn.div Complex.imCLM.contDiff.contDiffOn
      (fun z hz => ne_of_gt hz)
  have hp : ContDiffOn ℝ 1 (fun z : ℂ => ρ (z.re / z.im)) upperHalf :=
    hρ.comp_contDiffOn ht
  have he : ContDiffOn ℝ 1 (fun z : ℂ => Real.exp (A * ρ (z.re / z.im))) upperHalf :=
    (contDiffOn_const.mul hp).exp
  have hc : ContDiffOn ℝ 1 (fun z : ℂ =>
      (Real.exp (A * ρ (z.re / z.im)) : ℂ) * z) upperHalf :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn he).mul contDiffOn_id
  exact hc.congr hf

/-- Exact Wirtinger values; the local formula permits any extension outside H. -/
theorem s28m_twist_formula_wirtinger {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (A : ℝ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ upperHalf, f z =
      (Real.exp (A * ρ (z.re / z.im)) : ℂ) * z)
    {z : ℂ} (hz : z ∈ upperHalf) :
    let t : ℝ := z.re / z.im
    let d : ℝ := A * deriv ρ t
    let r : ℝ := Real.exp (A * ρ t)
    dz f z = (r : ℂ) * (1 + Complex.I * (d : ℂ) * (1 + (t : ℂ) ^ 2) / 2) ∧
    dzbar f z = (r : ℂ) * (d : ℂ) / 2 *
      ((t : ℂ) + Complex.I) * (1 - Complex.I * (t : ℂ)) := by
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hi := (hasDerivAt_inv hy).comp_hasFDerivAt z Complex.imCLM.hasFDerivAt
  have ht := Complex.reCLM.hasFDerivAt.mul hi
  have hp := (hρ.differentiable_one (z.re * z.im⁻¹)).hasDerivAt.comp_hasFDerivAt z ht
  have he := (hp.const_mul A).exp
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z he
  have hd := hc.mul (hasFDerivAt_id z)
  change HasFDerivAt (fun w : ℂ =>
    (Real.exp (A * ρ (w.re * w.im⁻¹)) : ℂ) * w) _ z at hd
  simp only [Pi.mul_apply, Function.comp_apply, Complex.reCLM_apply,
    Complex.ofRealCLM_apply, id_eq] at hd
  have heq : f =ᶠ[𝓝 z] (fun w : ℂ =>
      (Real.exp (A * ρ (w.re * w.im⁻¹)) : ℂ) * w) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    simpa only [div_eq_mul_inv] using hf w hw
  dsimp only
  constructor
  · rw [dz, heq.fderiv_eq, hd.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    simp only [← div_eq_mul_inv]
    apply Complex.ext <;> simp only [pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
      <;> field_simp [hy] <;> ring
  · rw [dzbar, heq.fderiv_eq, hd.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    simp only [← div_eq_mul_inv]
    apply Complex.ext <;> simp only [pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
      <;> field_simp [hy] <;> ring

/-- Positive Jacobian and a coarse distortion bound for the two expressions. -/
theorem s28m_twist_wirtinger_bound {r t d B : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hd : |d| * (1 + t ^ 2) ≤ B) :
    let u : ℂ := (r : ℂ) * (1 + Complex.I * (d : ℂ) * (1 + (t : ℂ) ^ 2) / 2)
    let v : ℂ := (r : ℂ) * (d : ℂ) / 2 *
      ((t : ℂ) + Complex.I) * (1 - Complex.I * (t : ℂ))
    ‖v‖ < ‖u‖ ∧ (‖u‖ + ‖v‖) / (‖u‖ - ‖v‖) ≤ (2 + B) ^ 2 := by
  dsimp only
  set u : ℂ := (r : ℂ) * (1 + Complex.I * (d : ℂ) * (1 + (t : ℂ) ^ 2) / 2)
  set v : ℂ := (r : ℂ) * (d : ℂ) / 2 *
    ((t : ℂ) + Complex.I) * (1 - Complex.I * (t : ℂ))
  have hu : ‖u‖ ^ 2 = r ^ 2 + r ^ 2 * d ^ 2 * (1 + t ^ 2) ^ 2 / 4 := by
    rw [Complex.sq_norm]
    simp [u, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hv : ‖v‖ ^ 2 = r ^ 2 * d ^ 2 * (1 + t ^ 2) ^ 2 / 4 := by
    rw [Complex.sq_norm]
    simp [v, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hgap : ‖v‖ < ‖u‖ := by
    nlinarith [norm_nonneg u, norm_nonneg v, sq_pos_of_pos hr]
  have hnv : ‖v‖ = r * |d| * (1 + t ^ 2) / 2 := by
    have hh : 0 ≤ r * |d| * (1 + t ^ 2) / 2 := by positivity
    have he : (r * |d| * (1 + t ^ 2) / 2) ^ 2 =
        r ^ 2 * d ^ 2 * (1 + t ^ 2) ^ 2 / 4 := by
      simp only [div_pow, mul_pow, sq_abs]
      ring
    nlinarith [norm_nonneg v]
  have hvB : 2 * ‖v‖ ≤ r * B := by
    rw [hnv]
    nlinarith [mul_le_mul_of_nonneg_left hd hr.le]
  have huB : ‖u‖ ≤ r + ‖v‖ := by
    nlinarith [norm_nonneg u, norm_nonneg v, mul_nonneg hr.le (norm_nonneg v)]
  have hsum : ‖u‖ + ‖v‖ ≤ r * (1 + B) := by linarith
  have hprod : (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) = r ^ 2 := by nlinarith
  have hratio : (‖u‖ + ‖v‖) / (‖u‖ - ‖v‖) = (‖u‖ + ‖v‖) ^ 2 / r ^ 2 := by
    apply (div_eq_div_iff (sub_pos.mpr hgap).ne' (pow_ne_zero 2 hr.ne')).mpr
    nlinarith [hprod]
  refine ⟨hgap, ?_⟩
  rw [hratio]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  have hsquare := mul_self_le_mul_self (add_nonneg (norm_nonneg u) (norm_nonneg v)) hsum
  have hBsq : (1 + B) ^ 2 ≤ (2 + B) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hBsq (sq_nonneg r)]

/-- **QC of the plane model.** In logarithmic polar coordinates the derivative
is a shear with off-diagonal entry -k log(l) (1+t^2) rho'(t).
Outside [-a,a] it is conformal; inside, the displayed derivative bound is uniform.
The witness K may depend on k. No uniform QC bound over all integer powers is claimed. -/
theorem s28m_twist_model_qc {l a C : ℝ} (hl : 1 < l) (ha : 0 < a)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hC : 0 ≤ C)
    (hderiv : ∀ t : ℝ, |deriv ρ t| ≤ C)
    (hleft : ∀ t : ℝ, t ≤ -a → ρ t = 0)
    (hright : ∀ t : ℝ, a ≤ t → ρ t = 1)
    {F : ℤ → (ℍ ≃ₜ ℍ)}
    (hformula : ∀ (k : ℤ) (w : ℍ), ((F k w : ℍ) : ℂ) =
      (Real.exp ((k : ℝ) * Real.log l * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ)) :
    ∀ k : ℤ, ∃ K : ℝ, IsKQC (liftToC (F k)) upperHalf K := by
  -- The QC bound works for every real A; l > 1 is needed by the twist geometry.
  have _hl := hl
  intro k
  let A : ℝ := (k : ℝ) * Real.log l
  let B : ℝ := |A| * C * (1 + a ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfm : ∀ z ∈ upperHalf, liftToC (F k) z =
      (Real.exp (A * ρ (z.re / z.im)) : ℂ) * z := by
    intro z hz
    calc
      liftToC (F k) z = ((F k (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) :=
        h23l_liftToC_coe (F k) ⟨z, hz⟩
      _ = _ := hformula k ⟨z, hz⟩
  refine ⟨(2 + B) ^ 2, isKQC_of_isC1Quasiconformal ?_⟩
  refine ⟨isOpen_upperHalf, by nlinarith, s28m_twist_formula_contDiffOn hρ A hfm, ?_, ?_⟩
  · exact qcl_f_isHomeomorphOnto_of_injOn isOpen_upperHalf
      (h23l_liftToC_continuousOn (F k).continuous) (h23l_liftToC_injOn (F k))
  · intro z hz
    obtain ⟨hdz, hdzbar⟩ := s28m_twist_formula_wirtinger hρ A hfm hz
    have hb := s28m_twist_profile_shear_bound ha hρ hC hderiv hleft hright A (z.re / z.im)
    obtain ⟨hstrict, hquot⟩ := s28m_twist_wirtinger_bound
      (Real.exp_pos (A * ρ (z.re / z.im))) hB hb
    rw [← hdz, ← hdzbar] at hstrict hquot
    refine ⟨hstrict, ?_⟩
    have hn : 0 < ‖dz (liftToC (F k)) z‖ := (norm_nonneg _).trans_lt hstrict
    have hden : 1 - ‖dzbar (liftToC (F k)) z‖ / ‖dz (liftToC (F k)) z‖ ≠ 0 := by
      rw [one_sub_div hn.ne']
      exact div_ne_zero (sub_pos.mpr hstrict).ne' hn.ne'
    have he : dilatationQuotient (liftToC (F k)) z =
        (‖dz (liftToC (F k)) z‖ + ‖dzbar (liftToC (F k)) z‖) /
        (‖dz (liftToC (F k)) z‖ - ‖dzbar (liftToC (F k)) z‖) := by
      rw [dilatationQuotient, complexDilatation, norm_div,
        div_eq_div_iff hden (sub_pos.mpr hstrict).ne', one_add_div hn.ne', one_sub_div hn.ne']
      ring
    rw [he]
    exact hquot

/-- The hyperbolic displacement of a positive dilation in angular coordinates. -/
theorem s28m_twist_cosh_scale {w v : ℍ} {r : ℝ} (hr : 0 < r)
    (hv : (v : ℂ) = (r : ℂ) * (w : ℂ)) :
    Real.cosh (dist w v) =
      1 + (r - 1) ^ 2 / (2 * r * (w.im / ‖(w : ℂ)‖) ^ 2) := by
  have hi : v.im = r * w.im := by
    have h := congrArg Complex.im hv
    rw [Complex.im_ofReal_mul] at h
    simpa using h
  have hd : dist (w : ℂ) (v : ℂ) ^ 2 = (r - 1) ^ 2 * ‖(w : ℂ)‖ ^ 2 := by
    rw [dist_eq_norm, hv]
    have heq : (w : ℂ) - (r : ℂ) * (w : ℂ) = ((1 - r : ℝ) : ℂ) * (w : ℂ) := by
      push_cast
      ring
    rw [heq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [UpperHalfPlane.cosh_dist, hi, hd]
  have hn : ‖(w : ℂ)‖ ≠ 0 := (norm_pos_iff.2 w.ne_zero).ne'
  have hw : w.im ≠ 0 := w.im_pos.ne'
  field_simp [hr.ne', hw, hn]

/-- Action commutation with a dilation forces the image of i onto its axis.
This uses invariant displacement and the cosh formula, without choosing a
matrix representative modulo the central kernel. -/
theorem s28m_twist_axis_of_commute
    {g₀ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hcomm : ∀ w : ℍ, δ • (g₀ • w) = g₀ • (δ • w)) :
    ((δ • UpperHalfPlane.I : ℍ) : ℂ).re = 0 := by
  have hl0 : 0 < l := by linarith
  let v : ℍ := δ • UpperHalfPlane.I
  have hd : dist v (g₀ • v) = dist UpperHalfPlane.I (g₀ • UpperHalfPlane.I) := by
    dsimp [v]
    rw [← hcomm, dist_smul]
  have hc := congrArg Real.cosh hd
  rw [s28m_twist_cosh_scale hl0 (hdil v),
    s28m_twist_cosh_scale hl0 (hdil UpperHalfPlane.I)] at hc
  have hi : UpperHalfPlane.I.im / ‖(UpperHalfPlane.I : ℂ)‖ = 1 := by simp
  rw [hi, one_pow, mul_one] at hc
  have hn : (l - 1) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith)
  have he : (l - 1) ^ 2 / (2 * l * (v.im / ‖(v : ℂ)‖) ^ 2) =
      (l - 1) ^ 2 / (2 * l) := by linarith
  have hden : 2 * l * (v.im / ‖(v : ℂ)‖) ^ 2 = 2 * l := by
    apply inv_injective
    apply mul_left_cancel₀ hn
    simpa only [div_eq_mul_inv] using he
  have hspos : 0 < v.im / ‖(v : ℂ)‖ := div_pos v.im_pos (norm_pos_iff.2 v.ne_zero)
  have hsq : (v.im / ‖(v : ℂ)‖) ^ 2 = 1 := by
    apply mul_left_cancel₀ (show 2 * l ≠ 0 by positivity)
    simpa only [mul_one] using hden
  have hs : v.im / ‖(v : ℂ)‖ = 1 := by nlinarith
  exact s28m_collar_axis_of_one (by rw [hs])

/-- Covering uniqueness on a preconnected subset: this is the subset version
of the installed global `h23l_lifts_differ`, using Mathlib's eqOn theorem. -/
theorem s28m_twist_lifts_eqOn {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) {U : Set ℍ} (hU : IsPreconnected U)
    {q : ℍ} (hq : q ∈ U) {F₁ F₂ : ℍ → ℍ}
    (h₁ : ContinuousOn F₁ U) (h₂ : ContinuousOn F₂ U)
    (hproj : ∀ w ∈ U, p (F₁ w) = p (F₂ w)) :
    ∃ δ ∈ Γ, ∀ w ∈ U, F₁ w = δ • F₂ w := by
  obtain ⟨δ, hδ, hδq⟩ := (hp.2.2.2 (F₂ q) (F₁ q)).1 (hproj q hq).symm
  refine ⟨δ, hδ, ?_⟩
  apply hp.1.eqOn_of_comp_eqOn hU h₁ ((continuous_const_smul δ).comp_continuousOn h₂)
  · intro w hw
    exact (hproj w hw).trans ((hp.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩)
  · exact hq
  · exact hδq.symm

/-- A dilation with bounded displacement on a set of arbitrarily small positive
angular coordinate is the identity there. This is the quantitative FAR step. -/
theorem s28m_twist_bounded_dilation_on {E : Set ℍ} {G : ℍ → ℍ} {r B : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B)
    (hG : ∀ w ∈ E, ((G w : ℍ) : ℂ) = (r : ℂ) * (w : ℂ))
    (hbound : ∀ w ∈ E, dist (G w) w ≤ B)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ w ∈ E, w.im / ‖(w : ℂ)‖ < ε) :
    ∀ w ∈ E, G w = w := by
  have hr1 : r = 1 := by
    by_contra hne
    let A : ℝ := (r - 1) ^ 2
    let D : ℝ := 2 * r * (Real.cosh B - 1)
    have hA : 0 < A := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
    have hD : 0 ≤ D := mul_nonneg (by positivity) (sub_nonneg.2 (Real.one_le_cosh B))
    let ε : ℝ := Real.sqrt (A / (D + 1))
    have hε : 0 < ε := Real.sqrt_pos.2 (div_pos hA (by linarith))
    have hεsq : ε ^ 2 = A / (D + 1) := Real.sq_sqrt (by positivity)
    obtain ⟨w, hw, hσ⟩ := hsmall ε hε
    have hσpos : 0 < w.im / ‖(w : ℂ)‖ := div_pos w.im_pos (norm_pos_iff.2 w.ne_zero)
    have hcs : Real.cosh (dist w (G w)) ≤ Real.cosh B := by
      apply Real.cosh_le_cosh.2
      rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hB, dist_comm]
      exact hbound w hw
    have hc : Real.cosh (dist w (G w)) =
        1 + A / (2 * r * (w.im / ‖(w : ℂ)‖) ^ 2) := by
      exact s28m_twist_cosh_scale hr (hG w hw)
    rw [hc] at hcs
    have hlow : A ≤ D * (w.im / ‖(w : ℂ)‖) ^ 2 := by
      have h := (div_le_iff₀ (by positivity : 0 < 2 * r * (w.im / ‖(w : ℂ)‖) ^ 2)).1
        (show A / (2 * r * (w.im / ‖(w : ℂ)‖) ^ 2) ≤ Real.cosh B - 1 by linarith)
      dsimp [D]
      nlinarith
    have hsq : (w.im / ‖(w : ℂ)‖) ^ 2 < A / (D + 1) := by nlinarith
    have hu := (lt_div_iff₀ (by linarith : 0 < D + 1)).1 hsq
    nlinarith [sq_pos_of_pos hσpos]
  intro w hw
  apply UpperHalfPlane.ext
  simpa only [hr1, Complex.ofReal_one, one_mul] using hG w hw

/-- Compatible local integer actions descend through an open projection and
glue to the identity on an open exterior. All maps remain local to this proof. -/
theorem s28m_twist_glue_family {S : Type*} [TopologicalSpace S]
    {p : ℍ → S} (hpc : Continuous p) (hpo : IsOpenMap p)
    {U E : Set ℍ} (hU : IsOpen U) (hE : IsOpen E)
    (hcover : ∀ x : S, (∃ w ∈ U, p w = x) ∨ (∃ w ∈ E, p w = x))
    {F : ℤ → (ℍ ≃ₜ ℍ)}
    (hF0 : ∀ w : ℍ, F 0 w = w)
    (hFadd : ∀ (m n : ℤ) (w : ℍ), F (m + n) w = F m (F n w))
    (hFU : ∀ (k : ℤ) (w : ℍ), w ∈ U → F k w ∈ U)
    (hcompat : ∀ (k : ℤ) (w v : ℍ), w ∈ U → v ∈ U → p w = p v →
      p (F k w) = p (F k v))
    (hoverlap : ∀ (k : ℤ) (w v : ℍ), w ∈ U → v ∈ E → p w = p v →
      p (F k w) = p w) :
    ∃ T : ℤ → (S ≃ₜ S), T 0 = Homeomorph.refl S ∧
      (∀ (m n : ℤ) (x : S), T (m + n) x = T m (T n x)) ∧
      (∀ (k : ℤ) (w : ℍ), w ∈ U → T k (p w) = p (F k w)) ∧
      (∀ (k : ℤ) (w : ℍ), w ∈ E → T k (p w) = p w) := by
  classical
  let t : ℤ → S → S := fun k x =>
    if hx : ∃ w ∈ U, p w = x then p (F k hx.choose) else x
  have htU : ∀ (k : ℤ) (w : ℍ), w ∈ U → t k (p w) = p (F k w) := by
    intro k w hw
    dsimp only [t]
    split_ifs with hx
    · exact hcompat k hx.choose w hx.choose_spec.1 hw hx.choose_spec.2
    · exact False.elim (hx ⟨w, hw, rfl⟩)
  have htE : ∀ (k : ℤ) (w : ℍ), w ∈ E → t k (p w) = p w := by
    intro k w hw
    dsimp only [t]
    split_ifs with hx
    · exact (hoverlap k hx.choose w hx.choose_spec.1 hw hx.choose_spec.2).trans hx.choose_spec.2
    · rfl
  have htc : ∀ k : ℤ, Continuous (t k) := by
    intro k
    apply continuous_iff_continuousAt.2
    intro x
    rcases hcover x with hx | hx
    · obtain ⟨w, hw, rfl⟩ := hx
      have heq : (fun v : ℍ => t k (p v)) =ᶠ[𝓝 w] (fun v => p (F k v)) := by
        filter_upwards [hU.mem_nhds hw] with v hv
        exact htU k v hv
      have hloc := (hpc.comp (F k).continuous).continuousAt.congr_of_eventuallyEq heq
      change Tendsto (t k) (𝓝 (p w)) (𝓝 (t k (p w)))
      rw [← hpo.map_nhds_eq hpc.continuousAt, tendsto_map'_iff]
      exact hloc
    · obtain ⟨w, hw, rfl⟩ := hx
      have heq : (fun v : ℍ => t k (p v)) =ᶠ[𝓝 w] p := by
        filter_upwards [hE.mem_nhds hw] with v hv
        exact htE k v hv
      have hloc := hpc.continuousAt.congr_of_eventuallyEq heq
      change Tendsto (t k) (𝓝 (p w)) (𝓝 (t k (p w)))
      rw [← hpo.map_nhds_eq hpc.continuousAt, tendsto_map'_iff]
      exact hloc
  have ht0 : ∀ x : S, t 0 x = x := by
    intro x
    rcases hcover x with hx | hx
    · obtain ⟨w, hw, rfl⟩ := hx
      rw [htU 0 w hw, hF0]
    · obtain ⟨w, hw, rfl⟩ := hx
      exact htE 0 w hw
  have htadd : ∀ (m n : ℤ) (x : S), t (m + n) x = t m (t n x) := by
    intro m n x
    rcases hcover x with hx | hx
    · obtain ⟨w, hw, rfl⟩ := hx
      rw [htU (m + n) w hw, htU n w hw, htU m (F n w) (hFU n w hw), hFadd]
    · obtain ⟨w, hw, rfl⟩ := hx
      rw [htE (m + n) w hw, htE n w hw, htE m w hw]
  let T : ℤ → (S ≃ₜ S) := fun k =>
    { toEquiv :=
        { toFun := t k
          invFun := t (-k)
          left_inv := fun x => by rw [← htadd, neg_add_cancel, ht0]
          right_inv := fun x => by rw [← htadd, add_neg_cancel, ht0] }
      continuous_toFun := htc k
      continuous_invFun := htc (-k) }
  refine ⟨T, ?_, htadd, htU, htE⟩
  ext x
  exact ht0 x

/-- Positive radial scaling preserves both real-to-imaginary ratio and sigma. -/
theorem s28m_twist_scale_coords {w v : ℍ} {r : ℝ} (hr : 0 < r)
    (hv : (v : ℂ) = (r : ℂ) * (w : ℂ)) :
    (v : ℂ).re / v.im = (w : ℂ).re / w.im ∧
      v.im / ‖(v : ℂ)‖ = w.im / ‖(w : ℂ)‖ := by
  have hi : v.im = r * w.im := by
    have h := congrArg Complex.im hv
    rw [Complex.im_ofReal_mul] at h
    simpa using h
  have hre : (v : ℂ).re = r * (w : ℂ).re := by
    rw [hv, Complex.re_ofReal_mul]
  have hn : ‖(v : ℂ)‖ = r * ‖(w : ℂ)‖ := by
    rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  constructor
  · rw [hre, hi, mul_div_mul_left _ _ hr.ne']
  · rw [hi, hn, mul_div_mul_left _ _ hr.ne']

/-- The displayed shear formula determines its integer action and dilation commutation. -/
theorem s28m_twist_formula_laws {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    {ρ : ℝ → ℝ} {F : ℤ → (ℍ ≃ₜ ℍ)}
    (hformula : ∀ (k : ℤ) (w : ℍ), ((F k w : ℍ) : ℂ) =
      (Real.exp ((k : ℝ) * Real.log l * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ)) :
    (∀ w : ℍ, F 0 w = w) ∧
      (∀ (m n : ℤ) (w : ℍ), F (m + n) w = F m (F n w)) ∧
      (∀ (k : ℤ) (w : ℍ), (F k w).im / ‖(F k w : ℂ)‖ = w.im / ‖(w : ℂ)‖) ∧
      (∀ (k j : ℤ) (w : ℍ), F k (g₀ ^ j • w) = g₀ ^ j • F k w) := by
  have hcoords := fun k w => s28m_twist_scale_coords (Real.exp_pos _) (hformula k w)
  refine ⟨?_, ?_, fun k w => (hcoords k w).2, ?_⟩
  · intro w
    apply UpperHalfPlane.ext
    simp only [hformula, Int.cast_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  · intro m n w
    apply UpperHalfPlane.ext
    rw [hformula (m + n) w, hformula m (F n w), (hcoords n w).1, hformula n w]
    rw [Int.cast_add, add_mul, add_mul, Real.exp_add, Complex.ofReal_mul]
    ring
  · intro k j w
    have hp : ((g₀ ^ j • w : ℍ) : ℂ) = ((l ^ j : ℝ) : ℂ) * (w : ℂ) := by
      rw [s28m_far_zpow hl hdil, Complex.ofReal_zpow]
    have hratio := (s28m_twist_scale_coords (zpow_pos (by linarith) j) hp).1
    apply UpperHalfPlane.ext
    rw [hformula k (g₀ ^ j • w), hratio, s28m_far_zpow hl hdil j w,
      s28m_far_zpow hl hdil j (F k w), hformula k w]
    ring

/-- A point outside the inner angular collar lies in a constant profile tail. -/
theorem s28m_twist_small_sigma_tail {a s : ℝ} (ha : 0 < a)
    (hsa : s = 1 / Real.sqrt (1 + a ^ 2)) {w : ℍ}
    (hw : w.im / ‖(w : ℂ)‖ < s) :
    (w : ℂ).re / w.im ≤ -a ∨ a ≤ (w : ℂ).re / w.im := by
  -- The implication also holds for nonpositive a, when the two tails already cover R.
  have _ha := ha
  by_contra h
  push Not at h
  have hlo : -a * w.im < (w : ℂ).re := (lt_div_iff₀ w.im_pos).1 h.1
  have hhi : (w : ℂ).re < a * w.im := (div_lt_iff₀ w.im_pos).1 h.2
  have hre : (w : ℂ).re ^ 2 ≤ (a * w.im) ^ 2 := by
    have hp : 0 ≤ (a * w.im - (w : ℂ).re) * ((w : ℂ).re + a * w.im) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hn : ‖(w : ℂ)‖ ^ 2 = (w : ℂ).re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_im]
    ring
  have hsqrt : 0 < Real.sqrt (1 + a ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : (Real.sqrt (1 + a ^ 2) * w.im) ^ 2 = (1 + a ^ 2) * w.im ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hnorm : ‖(w : ℂ)‖ ≤ Real.sqrt (1 + a ^ 2) * w.im := by
    nlinarith [norm_nonneg (w : ℂ), mul_pos hsqrt w.im_pos]
  have hσ : 1 / Real.sqrt (1 + a ^ 2) ≤ w.im / ‖(w : ℂ)‖ := by
    apply (div_le_div_iff₀ hsqrt (norm_pos_iff.2 w.ne_zero)).2
    nlinarith
  rw [hsa] at hw
  exact (not_le_of_gt hw) hσ

/-- A horizontal segment in the larger collar joins shell points in both tails.
Only connectedness of this segment is needed, not connectedness of the exterior. -/
theorem s28m_twist_shell_segment {s₁ s a : ℝ} (hs₁s : s₁ < s)
    (ha : 0 < a) (hsa : s = 1 / Real.sqrt (1 + a ^ 2)) :
    ∃ (V : Set ℍ) (qL qR : ℍ), IsPreconnected V ∧ qL ∈ V ∧ qR ∈ V ∧
      (∀ w ∈ V, s₁ < w.im / ‖(w : ℂ)‖) ∧
      qL.im / ‖(qL : ℂ)‖ < s ∧ qR.im / ‖(qR : ℂ)‖ < s ∧
      (qL : ℂ).re / qL.im ≤ -a ∧ a ≤ (qR : ℂ).re / qR.im := by
  let q : ℝ → ℍ := fun t => ⟨⟨t, 1⟩, by norm_num⟩
  have hqc : Continuous q := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.2
    change Continuous (fun t : ℝ => (⟨t, 1⟩ : ℂ))
    convert (Complex.continuous_ofReal.add continuous_const :
      Continuous (fun t : ℝ => (t : ℂ) + Complex.I)) using 1
    funext t
    apply Complex.ext <;> simp
  have hqim : ∀ t : ℝ, (q t).im = 1 := fun _ => rfl
  have hqre : ∀ t : ℝ, (q t : ℂ).re = t := fun _ => rfl
  have hqnorm : ∀ t : ℝ, ‖(q t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
    intro t
    rw [Complex.norm_def, Complex.normSq_apply]
    change Real.sqrt (t * t + 1 * 1) = Real.sqrt (1 + t ^ 2)
    congr 1
    ring
  have hqsig : ∀ t : ℝ, (q t).im / ‖(q t : ℂ)‖ = 1 / Real.sqrt (1 + t ^ 2) := by
    intro t
    rw [hqim, hqnorm]
  have hnb : {t : ℝ | s₁ < (q t).im / ‖(q t : ℂ)‖} ∈ 𝓝 a := by
    apply (isOpen_lt continuous_const (s28m_far_sig_continuous.comp hqc)).mem_nhds
    change s₁ < (q a).im / ‖(q a : ℂ)‖
    rw [hqsig, ← hsa]
    exact hs₁s
  obtain ⟨b, d, had, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnb
  obtain ⟨c, hac, hcd⟩ := exists_between had.2
  have hc : 0 < c := ha.trans hac
  have hcσ : s₁ < 1 / Real.sqrt (1 + c ^ 2) := by
    have h := hsub (show c ∈ Set.Ioo b d from ⟨had.1.trans hac, hcd⟩)
    change s₁ < (q c).im / ‖(q c : ℂ)‖ at h
    rwa [hqsig] at h
  have hcsmall : 1 / Real.sqrt (1 + c ^ 2) < s := by
    rw [hsa]
    apply one_div_lt_one_div_of_lt (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  let V : Set ℍ := q '' Set.Icc (-c) c
  have hnegV : q (-c) ∈ V := ⟨-c, ⟨le_rfl, by linarith⟩, rfl⟩
  have hposV : q c ∈ V := ⟨c, ⟨by linarith, le_rfl⟩, rfl⟩
  refine ⟨V, q (-c), q c, isPreconnected_Icc.image q hqc.continuousOn,
    hnegV, hposV, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [hqsig]
    apply lt_of_lt_of_le hcσ
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    have hm : 0 ≤ (c - t) * (c + t) := mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith
  · simpa only [hqsig, neg_sq] using hcsmall
  · simpa only [hqsig] using hcsmall
  · rw [hqre, hqim, div_one]
    linarith
  · rw [hqre, hqim, div_one]
    exact hac.le

/-- **Descend the local collar maps.** Put s = 1/sqrt(1+a^2), so sigma >= s
means |Re/Im| <= a. On the larger open collar sigma > s1 use the local model;
outside all closed s-collars use the identity. On overlaps the two model tails
are respectively id and g0^k, which have the same projection under p.
Different representations of the same collar differ by a power of g0.
The output laws are pointwise to avoid conventions for multiplication of homeomorphisms. -/
theorem s28m_twist_descend {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ)
    {l s₁ s a : ℝ} (hl : 1 < l) (hs₁ : 0 < s₁) (hs₁s : s₁ < s) (hs : s < 1)
    (ha : 0 < a) (hsa : s = 1 / Real.sqrt (1 + a ^ 2))
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    {ρ : ℝ → ℝ}
    (hleft : ∀ t : ℝ, t ≤ -a → ρ t = 0)
    (hright : ∀ t : ℝ, a ≤ t → ρ t = 1)
    {F : ℤ → (ℍ ≃ₜ ℍ)}
    (hformula : ∀ (k : ℤ) (w : ℍ), ((F k w : ℍ) : ℂ) =
      (Real.exp ((k : ℝ) * Real.log l * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ)) :
    ∃ T : ℤ → (S ≃ₜ S),
      T 0 = Homeomorph.refl S ∧
      (∀ (m n : ℤ) (x : S), T (m + n) x = T m (T n x)) ∧
      (∀ (k : ℤ) (w : ℍ), s₁ < w.im / ‖(w : ℂ)‖ → T k (p w) = p (F k w)) ∧
      (∀ (k : ℤ) (w : ℍ),
        (∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w) →
        T k (p w) = p w) := by
  classical
  -- The upper bound on s is needed by the geometric programme, but not by this gluing step.
  have _hs := hs
  let U : Set ℍ := {w | s₁ < w.im / ‖(w : ℂ)‖}
  let E : Set ℍ := {w | ∀ γ ∈ Γ, ∀ v : ℍ,
    s ≤ v.im / ‖(v : ℂ)‖ → γ • v ≠ w}
  have hdeck : ∀ γ ∈ Γ, ∀ w : ℍ, p (γ • w) = p w := by
    intro γ hγ w
    exact ((hp.2.2.2 w (γ • w)).2 ⟨γ, hγ, rfl⟩).symm
  have hU : IsOpen U := isOpen_lt continuous_const s28m_far_sig_continuous
  have hE : IsOpen E := s28m_far_isOpen_E hΓ hg₀ hl hdil (by linarith)
  obtain ⟨hF0, hFadd, hFsig, hFcomm⟩ := s28m_twist_formula_laws hl hdil hformula
  have hcover : ∀ x : S, (∃ w ∈ U, p w = x) ∨ (∃ w ∈ E, p w = x) := by
    intro x
    obtain ⟨w, hw⟩ := hp.2.2.1 x
    by_cases hwE : w ∈ E
    · exact Or.inr ⟨w, hwE, hw⟩
    · change ¬ (∀ γ ∈ Γ, ∀ v : ℍ, s ≤ v.im / ‖(v : ℂ)‖ → γ • v ≠ w) at hwE
      push Not at hwE
      obtain ⟨γ, hγ, v, hv, heq⟩ := hwE
      refine Or.inl ⟨v, lt_of_lt_of_le hs₁s hv, ?_⟩
      rw [← heq, hdeck γ hγ] at hw
      exact hw
  have hcompat : ∀ (k : ℤ) (w v : ℍ), w ∈ U → v ∈ U → p w = p v →
      p (F k w) = p (F k v) := by
    intro k w v hw hv hpwv
    obtain ⟨γ, hγ, hγwv⟩ := (hp.2.2.2 w v).1 hpwv
    have hpower : ∃ j : ℤ, ∀ z : ℍ, γ • z = g₀ ^ j • z := by
      by_contra hn
      push Not at hn
      exact hdisj γ hγ hn w v (le_of_lt hw) (le_of_lt hv) hγwv
    obtain ⟨j, hj⟩ := hpower
    have hvw : v = g₀ ^ j • w := hγwv.symm.trans (hj w)
    rw [hvw, hFcomm, hdeck (g₀ ^ j) (Γ.zpow_mem hg₀ j)]
  have hoverlap : ∀ (k : ℤ) (w v : ℍ), w ∈ U → v ∈ E → p w = p v →
      p (F k w) = p w := by
    intro k w v _hw hv hpwv
    obtain ⟨γ, hγ, hγwv⟩ := (hp.2.2.2 w v).1 hpwv
    have hwE : w ∈ E := by
      intro δ hδ z hz hδzw
      apply hv (γ * δ) (Γ.mul_mem hγ hδ) z hz
      rw [mul_smul, hδzw, hγwv]
    have hwsmall : w.im / ‖(w : ℂ)‖ < s := by
      by_contra hn
      exact hwE 1 Γ.one_mem w (le_of_not_gt hn) (one_smul _ _)
    rcases s28m_twist_small_sigma_tail ha hsa hwsmall with hneg | hpos
    · have hFw : F k w = w := by
        apply UpperHalfPlane.ext
        rw [hformula, hleft _ hneg]
        simp
      rw [hFw]
    · have hFw : F k w = g₀ ^ k • w := by
        apply UpperHalfPlane.ext
        rw [hformula, hright _ hpos, mul_one, s28m_far_zpow hl hdil]
        rw [← Real.log_zpow, Real.exp_log (zpow_pos (by linarith) k), Complex.ofReal_zpow]
      rw [hFw, hdeck (g₀ ^ k) (Γ.zpow_mem hg₀ k)]
  exact s28m_twist_glue_family hp.1.continuous hp.1.isOpenMap hU hE hcover
    hF0 hFadd (fun k w hw => by change s₁ < (F k w).im / ‖(F k w : ℂ)‖; rw [hFsig]; exact hw)
    hcompat hoverlap

/-- Deck pre/postcomposition retains the same plane QC constant. -/
theorem s28m_twist_deck_comp_qc {F H : ℍ ≃ₜ ℍ} {K : ℝ}
    (hF : IsKQC (liftToC F) upperHalf K)
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hH : ∀ w : ℍ, H w = γ • F (δ • w)) :
    IsKQC (liftToC H) upperHalf K := by
  have heq : H = ((Homeomorph.smul δ).trans F).trans (Homeomorph.smul γ) := by
    apply Homeomorph.ext
    intro w
    exact hH w
  rw [heq]
  exact s30w_isKQC_conj hF δ γ

/-- Equal projections on an open set transfer a uniform local QC bound. -/
theorem s28m_twist_lift_local_qc {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) {L M : ℍ ≃ₜ ℍ} {K : ℝ}
    (hM : IsKQC (liftToC M) upperHalf K)
    {U : Set ℍ} (hU : IsOpen U)
    (hproj : ∀ w ∈ U, p (L w) = p (M w)) :
    ∀ w ∈ U, ∃ V : Set ℂ,
      IsOpen V ∧ (w : ℂ) ∈ V ∧ V ⊆ upperHalf ∧ IsKQC (liftToC L) V K := by
  intro w hw
  obtain ⟨δ, hδ, hδw⟩ := (hp.2.2.2 (M w) (L w)).mp (hproj w hw).symm
  let N : ℍ ≃ₜ ℍ := M.trans (Homeomorph.smul δ)
  have hN : IsKQC (liftToC N) upperHalf K :=
    s28m_twist_deck_comp_qc hM δ 1 (fun x => by simp [N])
  obtain ⟨O, hOo, hwO, hOi⟩ := hp.1.isLocalHomeomorph.isLocallyInjective (L w)
  let W : Set ℍ := U ∩ L ⁻¹' O ∩ N ⁻¹' O
  have hWo : IsOpen W := (hU.inter (hOo.preimage L.continuous)).inter (hOo.preimage N.continuous)
  have hwW : w ∈ W := ⟨⟨hw, hwO⟩, by simpa [N, hδw] using hwO⟩
  have heq : ∀ x ∈ W, L x = N x := by
    intro x hx
    apply hOi hx.1.2 hx.2
    exact (hproj x hx.1.1).trans ((hp.2.2.2 (M x) (N x)).mpr ⟨δ, hδ, rfl⟩)
  let V : Set ℂ := ((↑) : ℍ → ℂ) '' W
  have hVo : IsOpen V := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap W hWo
  have hVH : V ⊆ upperHalf := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact x.im_pos
  refine ⟨V, hVo, ⟨w, hwW, rfl⟩, hVH, ?_⟩
  refine ad_isKQC_congr (ac_t_isKQC_restrict hN hVo hVH) ?_
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [h23l_liftToC_coe, h23l_liftToC_coe, heq x hx]

/-- **QC descends locally.** Any T satisfying the local collar and exterior
formulas has QC members when the plane models do. Lift T using exists_lift;
on each member of the open cover, covering uniqueness makes the lift a conformal
deck translate of the corresponding model. Glue the local uniform K estimates. -/
theorem s28m_twist_qc {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ)
    {l s₁ s : ℝ} (hl : 1 < l) (hs₁ : 0 < s₁) (hs₁s : s₁ < s) (hs : s < 1)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    {F : ℤ → (ℍ ≃ₜ ℍ)} (hFqc : ∀ k : ℤ, ∃ K : ℝ, IsKQC (liftToC (F k)) upperHalf K)
    {T : ℤ → (S ≃ₜ S)}
    (hcollar : ∀ (k : ℤ) (w : ℍ), s₁ < w.im / ‖(w : ℂ)‖ → T k (p w) = p (F k w))
    (hexterior : ∀ (k : ℤ) (w : ℍ),
      (∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w) → T k (p w) = p w) :
    ∀ k : ℤ, IsQCRS (T k) := by
  classical
  -- The upper restriction on s is geometric input; local QC only uses 0 < s.
  have _hs := hs
  intro k
  obtain ⟨K, hK⟩ := hFqc k
  obtain ⟨v₀, hv₀⟩ := hp.2.2.1 (T k (p UpperHalfPlane.I))
  obtain ⟨L, hL, _hL₀⟩ := exists_lift hp hp (T k) UpperHalfPlane.I v₀ hv₀
  have hdeck : ∀ γ ∈ Γ, ∀ w : ℍ, p (γ • w) = p w := by
    intro γ hγ w
    exact ((hp.2.2.2 w (γ • w)).mpr ⟨γ, hγ, rfl⟩).symm
  let E : Set ℍ := {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ,
    s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w}
  have hEo : IsOpen E := s28m_far_isOpen_E hΓ hg₀ hl hdil (lt_trans hs₁ hs₁s)
  have hUo : IsOpen {w : ℍ | s₁ < w.im / ‖(w : ℂ)‖} :=
    isOpen_lt continuous_const s28m_far_sig_continuous
  have hid : IsKQC (liftToC (Homeomorph.refl ℍ)) upperHalf K := by
    have hi := (isKQC_one_of_conformal isOpen_upperHalf (isConformalOnto_id upperHalf)).mono hK.2.1
    refine ad_isKQC_congr hi ?_
    intro z hz
    exact h23l_liftToC_coe (Homeomorph.refl ℍ) ⟨z, hz⟩
  have hLK : IsKQC (liftToC L) upperHalf K := by
    refine s23_lg isOpen_upperHalf hK.2.1 (h23l_liftToC_injOn L) ?_
    intro z hz
    let w : ℍ := ⟨z, hz⟩
    by_cases hwE : w ∈ E
    · have hproj : ∀ x ∈ E, p (L x) = p ((Homeomorph.refl ℍ) x) := by
        intro x hx
        exact (hL x).trans (hexterior k x hx)
      exact s28m_twist_lift_local_qc hp hid hEo hproj w hwE
    · change ¬ (∀ γ ∈ Γ, ∀ v : ℍ, s ≤ v.im / ‖(v : ℂ)‖ → γ • v ≠ w) at hwE
      push Not at hwE
      obtain ⟨γ, hγ, v, hv, hvw⟩ := hwE
      let N : ℍ ≃ₜ ℍ := (Homeomorph.smul γ⁻¹).trans (F k)
      have hN : IsKQC (liftToC N) upperHalf K :=
        s28m_twist_deck_comp_qc hK 1 γ⁻¹ (fun x => by simp [N])
      let W : Set ℍ := {x : ℍ | s₁ < (γ⁻¹ • x).im / ‖((γ⁻¹ • x : ℍ) : ℂ)‖}
      have hWo : IsOpen W := hUo.preimage (continuous_const_smul γ⁻¹)
      have hwW : w ∈ W := by
        change s₁ < (γ⁻¹ • w).im / ‖((γ⁻¹ • w : ℍ) : ℂ)‖
        rw [← hvw, inv_smul_smul]
        exact lt_of_lt_of_le hs₁s hv
      have hproj : ∀ x ∈ W, p (L x) = p (N x) := by
        intro x hx
        change p (L x) = p (F k (γ⁻¹ • x))
        rw [hL x, ← hdeck γ⁻¹ (Γ.inv_mem hγ) x]
        exact hcollar k (γ⁻¹ • x) hx
      exact s28m_twist_lift_local_qc hp hN hWo hproj w hwW
  exact ⟨K, s27v_isKQCRS_of_lift hp hp hL hLK⟩

/-- **A homotopically trivial map has a bounded commuting lift.** Use the
installed homotopy/deck conjugacy theorem and adjust a lift by a deck element.
The displacement of the adjusted lift is Gamma-invariant and continuous, so
compact orbit representatives bound it. No isotopy hypothesis is required. -/
theorem s28m_homotopic_commuting_lift {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (f : S ≃ₜ S)
    (hhom : ContinuousMap.Homotopic (f : C(S, S)) (ContinuousMap.id S)) :
    ∃ (G : ℍ ≃ₜ ℍ) (B : ℝ), IsLift p p f G ∧ 0 ≤ B ∧
      (∀ γ ∈ Γ, ∀ w : ℍ, G (γ • w) = γ • G w) ∧
      (∀ w : ℍ, dist (G w) w ≤ B) := by
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (f (p UpperHalfPlane.I))
  obtain ⟨F, hF, -⟩ := exists_lift hp hp f UpperHalfPlane.I τ₁ hτ₁
  have hid : IsLift p p (Homeomorph.refl S) (Homeomorph.refl ℍ) := fun _ => rfl
  have hhom' : ContinuousMap.Homotopic (f : C(S, S))
      ((Homeomorph.refl S : S ≃ₜ S) : C(S, S)) := hhom
  obtain ⟨δ, hδ, hrel⟩ :=
    (thm23_1_homotopy_iff hp hp f (Homeomorph.refl S) hF hid).1 hhom'
  let G : ℍ ≃ₜ ℍ := F.trans (Homeomorph.smul δ⁻¹)
  have hGcomm : ∀ γ ∈ Γ, ∀ w : ℍ, G (γ • w) = γ • G w := by
    intro γ hγ w
    have h := hrel γ hγ (F w)
    change F (γ • F.symm (F w)) = δ • (γ • (δ⁻¹ • F w)) at h
    rw [F.symm_apply_apply] at h
    change δ⁻¹ • F (γ • w) = γ • (δ⁻¹ • F w)
    rw [h, inv_smul_smul]
  have hGlift : IsLift p p f G := by
    intro w
    change p (δ⁻¹ • F w) = f (p w)
    calc
      p (δ⁻¹ • F w) = p (F w) :=
        ((hp.2.2.2 (F w) (δ⁻¹ • F w)).2 ⟨δ⁻¹, Γ.inv_mem hδ, rfl⟩).symm
      _ = f (p w) := hF w
  obtain ⟨D, hD⟩ := s27l_bounded_displacement hp G.continuous hGcomm
  exact ⟨G, max 0 D, hGlift, le_max_left _ _, hGcomm,
    fun w => (hD w).trans (le_max_right _ _)⟩

/-- **Fix the adjacent exterior component.** A bounded commuting lift whose
projection is the identity on the exterior is the identity on any component
containing a shell point. Covering uniqueness gives a constant deck action there;
g0-invariance makes that action commute with the dilation. The action is itself
a dilation, and FAR contradicts bounded displacement unless its factor is 1. -/
theorem s28m_component_fixed {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ)
    {l s₁ s : ℝ} (hl : 1 < l) (hs₁ : 0 < s₁) (hs₁s : s₁ < s) (hs : s < 1)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    (hstab : ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w')
    {G : ℍ ≃ₜ ℍ} {B : ℝ}
    (hcomm : ∀ γ ∈ Γ, ∀ w : ℍ, G (γ • w) = γ • G w)
    (hbound : ∀ w : ℍ, dist (G w) w ≤ B)
    (hproj : ∀ w : ℍ,
      (∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w) → p (G w) = p w)
    {q : ℍ} (hq₁ : s₁ ≤ q.im / ‖(q : ℂ)‖) (hq₂ : q.im / ‖(q : ℂ)‖ < s) :
    ∀ w ∈ connectedComponentIn
      {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} q,
      G w = w := by
  let E : Set ℍ := {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ,
    s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w}
  let C : Set ℍ := connectedComponentIn E q
  have hqE : q ∈ E := s28m_far_shell_mem hl hdil hdisj hs₁s hq₁ hq₂
  have hqC : q ∈ C := mem_connectedComponentIn hqE
  have hCE : C ⊆ E := connectedComponentIn_subset E q
  have hdeck : ∀ γ ∈ Γ, ∀ w : ℍ, p (γ • w) = p w := by
    intro γ hγ w
    exact ((hp.2.2.2 w (γ • w)).2 ⟨γ, hγ, rfl⟩).symm
  obtain ⟨δ, hδ, hδC⟩ := s28m_twist_lifts_eqOn hp isPreconnected_connectedComponentIn hqC
    G.continuous.continuousOn continuous_id.continuousOn (fun w hw => hproj w (hCE hw))
  simp only [id_eq] at hδC
  have hgq : g₀ • q ∈ C := by
    simpa only [zpow_one] using s28m_far_comp_zpow hg₀ hl hdil hdisj hs₁s hq₁ hq₂ 1 hqC
  have hcommq : δ • (g₀ • q) = g₀ • (δ • q) := by
    rw [← hδC (g₀ • q) hgq, ← hδC q hqC]
    exact hcomm g₀ hg₀ q
  have hcommδ : ∀ w : ℍ, δ • (g₀ • w) = g₀ • (δ • w) := by
    have heq : (fun w : ℍ => δ • (g₀ • w)) = (fun w : ℍ => g₀ • (δ • w)) := by
      apply hp.1.eq_of_comp_eq
        ((continuous_const_smul δ).comp (continuous_const_smul g₀))
        ((continuous_const_smul g₀).comp (continuous_const_smul δ))
        ?_ q hcommq
      funext w
      change p (δ • (g₀ • w)) = p (g₀ • (δ • w))
      rw [hdeck δ hδ, hdeck g₀ hg₀, hdeck g₀ hg₀, hdeck δ hδ]
    exact fun w => congrFun heq w
  obtain ⟨j, hj⟩ := hstab δ hδ UpperHalfPlane.I (by simp)
    (s28m_twist_axis_of_commute hl hdil hcommδ)
  have hr : 0 < l ^ j := zpow_pos (by linarith) _
  have hB : 0 ≤ B := dist_nonneg.trans (hbound q)
  apply s28m_twist_bounded_dilation_on (E := C) (G := G) hr hB
  · intro w hw
    rw [hδC w hw, hj w, s28m_far_zpow hl hdil, Complex.ofReal_zpow]
  · intro w _
    exact hbound w
  · intro ε hε
    exact s28m_far hΓ hg₀ hl hdil hs₁ hs₁s hs hdisj hstab hq₁ hq₂ hε

/-- **Detect the twist number by homotopy.** The bounded commuting lift is
the identity at both shell sides. On the connected larger collar it differs from
F k by one deck action. The left tail forces that action to be the identity;
the right tail then forces l^k = 1, hence k = 0. This works for separating collars
as well: no crossing element or connectedness of the surface complement is assumed. -/
theorem s28m_twist_homotopy_detect {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ)
    {l s₁ s a : ℝ} (hl : 1 < l) (hs₁ : 0 < s₁) (hs₁s : s₁ < s) (hs : s < 1)
    (ha : 0 < a) (hsa : s = 1 / Real.sqrt (1 + a ^ 2))
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    (hstab : ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w')
    {ρ : ℝ → ℝ}
    (hleft : ∀ t : ℝ, t ≤ -a → ρ t = 0)
    (hright : ∀ t : ℝ, a ≤ t → ρ t = 1)
    {F : ℤ → (ℍ ≃ₜ ℍ)}
    (hformula : ∀ (k : ℤ) (w : ℍ), ((F k w : ℍ) : ℂ) =
      (Real.exp ((k : ℝ) * Real.log l * ρ ((w : ℂ).re / w.im)) : ℂ) * (w : ℂ))
    {T : ℤ → (S ≃ₜ S)}
    (hcollar : ∀ (k : ℤ) (w : ℍ), s₁ < w.im / ‖(w : ℂ)‖ → T k (p w) = p (F k w))
    (hexterior : ∀ (k : ℤ) (w : ℍ),
      (∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w) → T k (p w) = p w) :
    ∀ k : ℤ, ContinuousMap.Homotopic (T k : C(S, S)) (ContinuousMap.id S) → k = 0 := by
  intro k hhom
  obtain ⟨G, B, hG, _hB, hcomm, hbound⟩ := s28m_homotopic_commuting_lift hp (T k) hhom
  obtain ⟨V, qm, qp, hVc, hqmV, hqpV, hVcollar, hqms, hqps, hqmtail, hqptail⟩ :=
    s28m_twist_shell_segment hs₁s ha hsa
  have hprojE : ∀ w : ℍ,
      (∀ γ ∈ Γ, ∀ v : ℍ, s ≤ v.im / ‖(v : ℂ)‖ → γ • v ≠ w) → p (G w) = p w := by
    intro w hw
    exact (hG w).trans (hexterior k w hw)
  have hfix : ∀ q : ℍ, s₁ ≤ q.im / ‖(q : ℂ)‖ → q.im / ‖(q : ℂ)‖ < s → G q = q := by
    intro q hq₁ hq₂
    have hqE := s28m_far_shell_mem hl hdil hdisj hs₁s hq₁ hq₂
    exact s28m_component_fixed hp hΓ hg₀ hl hs₁ hs₁s hs hdil hdisj hstab
      hcomm hbound hprojE hq₁ hq₂ q (mem_connectedComponentIn hqE)
  have hGm : G qm = qm := hfix qm (hVcollar qm hqmV).le hqms
  have hGp : G qp = qp := hfix qp (hVcollar qp hqpV).le hqps
  have hFm : F k qm = qm := by
    apply UpperHalfPlane.ext
    rw [hformula, hleft _ hqmtail]
    simp
  have hGF : Set.EqOn G (F k) V := by
    apply hp.1.eqOn_of_comp_eqOn hVc G.continuous.continuousOn
      (F k).continuous.continuousOn ?_ hqmV (hGm.trans hFm.symm)
    intro w hw
    exact (hG w).trans (hcollar k w (hVcollar w hw))
  have hFp : F k qp = qp := (hGF hqpV).symm.trans hGp
  have him : Real.exp ((k : ℝ) * Real.log l) * qp.im = qp.im := by
    have heq := hformula k qp
    rw [hFp, hright _ hqptail, mul_one] at heq
    have hi := congrArg Complex.im heq
    rw [Complex.im_ofReal_mul] at hi
    exact hi.symm
  have hexp : Real.exp ((k : ℝ) * Real.log l) = 1 := by
    nlinarith [qp.im_pos]
  have hzero : (k : ℝ) * Real.log l = 0 := by
    have h := congrArg Real.log hexp
    simpa only [Real.log_exp, Real.log_one] using h
  have hk : (k : ℝ) = 0 := (mul_eq_zero.1 hzero).resolve_right (Real.log_pos hl).ne'
  exact_mod_cast hk

/-- **M2 output for M3.** A compact Riemann surface of genus greater than one
admits an integer family of QC twists with distinct homotopy classes. The addition
law identifies T k with the kth power of T 1 without choosing a new group convention.
Orientation preservation follows from the installed QC implication. -/
theorem s28m_dehn_twist_family {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) :
    ∃ T : ℤ → (S ≃ₜ S),
      T 0 = Homeomorph.refl S ∧
      (∀ (m n : ℤ) (x : S), T (m + n) x = T m (T n x)) ∧
      (∀ k : ℤ, IsQCRS (T k)) ∧
      (∀ m n : ℤ, ContinuousMap.Homotopic (T m : C(S, S)) (T n : C(S, S)) → m = n) := by
  let : CompactSpace S := hS.1
  obtain ⟨Γ, p, hΓ, hfree, hp⟩ := s22hg_exists_fuchsian_uniformization hg hS
  have hc : IsCocompact Γ := utm_exists_compact_translate hp
  obtain ⟨γ, hγ, hγone, hγneg⟩ := s27g_exists_ne_one hp
  have hnt : ∃ γ ∈ Γ, ∃ w : ℍ, γ • w ≠ w := by
    refine ⟨γ, hγ, UpperHalfPlane.I, ?_⟩
    intro heq
    rcases hfree γ hγ UpperHalfPlane.I heq with h | h
    · exact hγone h
    · exact hγneg h
  obtain ⟨g₀, w₀, hg₀, hnt₀, -, hmin⟩ := s28m_min_disp hΓ hfree hc hnt
  obtain ⟨A, l, hl, -, hg₀', hdil, hmin'⟩ :=
    s28m_min_hyperbolic hΓ hfree hc hg₀ hnt₀ hmin
  obtain ⟨hp', hΓ', -, -⟩ := s28m_conj_uniformization hp hΓ hfree hc A
  have hstab := s28m_stab_axis hg₀' hl hdil hmin'
  obtain ⟨s₁, hs₁, hs₁one, hdisj⟩ := s28m_collar hΓ' hg₀' hl hdil hstab
  let s : ℝ := (s₁ + 1) / 2
  have hs₁s : s₁ < s := by
    change s₁ < (s₁ + 1) / 2
    linarith
  have hs : s < 1 := by
    change (s₁ + 1) / 2 < 1
    linarith
  have hspos : 0 < s := hs₁.trans hs₁s
  have hsquare : s ^ 2 < 1 := by nlinarith
  have haarg : 0 < 1 / s ^ 2 - 1 := by
    have hinv : 1 < 1 / s ^ 2 := (one_lt_div (sq_pos_of_pos hspos)).2 hsquare
    linarith
  let a : ℝ := Real.sqrt (1 / s ^ 2 - 1)
  have ha : 0 < a := Real.sqrt_pos.2 haarg
  have haa : a ^ 2 = 1 / s ^ 2 - 1 := Real.sq_sqrt haarg.le
  have hsa : s = 1 / Real.sqrt (1 + a ^ 2) := by
    have heq : 1 + a ^ 2 = (1 / s) ^ 2 := by
      rw [haa, div_pow (1 : ℝ) s 2, one_pow]
      ring
    rw [heq, Real.sqrt_sq (le_of_lt (one_div_pos.mpr hspos)), one_div_one_div]
  obtain ⟨ρ, C, F, hρ, hC, hderiv, -, hleft, hright, -, -, hformula⟩ :=
    s28m_twist_model hl ha
  have hFqc := s28m_twist_model_qc hl ha hρ hC hderiv hleft hright hformula
  obtain ⟨T, hTzero, hTadd, hcollar, hexterior⟩ :=
    s28m_twist_descend hp' hΓ' hg₀' hl hs₁ hs₁s hs ha hsa hdil hdisj
      hleft hright hformula
  have hTqc := s28m_twist_qc hp' hΓ' hg₀' hl hs₁ hs₁s hs hdil hFqc
    hcollar hexterior
  have hdetect := s28m_twist_homotopy_detect hp' hΓ' hg₀' hl hs₁ hs₁s hs
    ha hsa hdil hdisj hstab hleft hright hformula hcollar hexterior
  refine ⟨T, hTzero, hTadd, hTqc, ?_⟩
  intro m n hhom
  have hcomp := hhom.comp (ContinuousMap.Homotopic.refl ((T (-n) : S ≃ₜ S) : C(S, S)))
  have hleftcomp : (T m : C(S, S)).comp (T (-n) : C(S, S)) =
      (T (m - n) : C(S, S)) := by
    ext x
    change T m (T (-n) x) = T (m - n) x
    rw [← hTadd, ← sub_eq_add_neg]
  have hrightcomp : (T n : C(S, S)).comp (T (-n) : C(S, S)) =
      ContinuousMap.id S := by
    ext x
    change T n (T (-n) x) = x
    rw [← hTadd, add_neg_cancel, hTzero]
    rfl
  rw [hleftcomp, hrightcomp] at hcomp
  have hzero := hdetect (m - n) hcomp
  exact sub_eq_zero.mp hzero

end LiZhongQC
