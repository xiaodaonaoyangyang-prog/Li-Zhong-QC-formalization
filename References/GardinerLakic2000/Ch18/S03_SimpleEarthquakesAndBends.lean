import References.GardinerLakic2000.Ch18.S02_GeneralEarthquakes

/-!
# Gardiner–Lakic 2000, Ch. 18 §18.3 Simple earthquakes and bends

Source `teichmuller.txt`, lines 13365–13451 (Chapter 18, §18.3).

* Example 1 (a simple earthquake, (18.1), (18.2), l. 13368) — `para18_3_simple_earthquake`
* Example 2 (a simple bend, (18.3), (18.4), l. 13391) — `para18_3_simple_bend`
* Unlabelled (`H(x log|x|) = −πE`, `H(E) = B/π`, l. 13410–13426; signs [CORRECTION]) — `para18_3_hilbert_E`
* Formulas (18.5), (18.6) (the earthquake and bending vector fields `E_ab`, `B_ab` of the line joining `a` to `b`,
  l. 13430–13437) — `earthquakeVF`, `bendVF`
* Definition (the functional `L_ab(φ) = π ∫_a^b φ(z) (z − a)(z − b)/(a − b) dz` on `A(ℍ)`, l. 13444) —
  `lFunctionalAB`
* Theorem 3 (l. 13450) — `thm18_3`

Not items: "`L_ab` is a bounded linear functional" (l. 13446, U−); the hyperbolic distance `t/2` remark (l. 13387).
Modelling: `ℝ̄`-vector fields are real functions on `ℝ`; `H` is §16.7's `hilbertPV` applied to the normalized
representative `zNormalize` (l. 12537; `zNormalize B = B`, `zNormalize E = E − x`). **[CORRECTION]** The printed
signs `H(x log|x|) = −πE`, `H(E) = B/π` (l. 13423–13426) are those of the standard Hilbert transform
(`Im F = H(Re F)` for `F = z log z`, holomorphic in `ℍ`); with the book's (16.23)/(16.24) (kernel `1/(ξ − x)`) they
flip: `H(x log|x|) = π(E − x) ≡ πE` and `H(E − x) ≡ −B/π`. `L_ab` integrates along the semicircle of `ℍ` from `a` to `b`
(`φ` is holomorphic in `ℍ`; the book's "from `a` to `b`"). Theorem 3 [reading, leader calibration E0.9]: "`Re L`,
`Im L` represent infinitesimal thinning and left twisting along `L_ab`" is: under the Chapter 3 pairing, with a
tangent vector identified with the real functional `φ ↦ Re ∬_ℍ μ φ` of its Beltrami differential
`μ = ∂̄Ṽ` (`Ṽ` the extension (16.18), `LiZhongQC.beurlingAhlfors`), the class of `B_ab` is `c₁ Re L_ab` and the class
of `E_ab` is `c₂ Im L_ab` for constants `c₁, c₂ > 0`; fattening and right twisting are the negatives. The check at
`a = 0`, `b = ∞` (Stokes: `∬_ℍ ∂̄Ṽ φ = (1/2i) ∫_ℝ V φ`, and `z log z ≡ B − iπE` holomorphic in `ℍ`) gives `c₁ = 1/2`,
`c₂ = 1/(2π)`, with the book's signs.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (upperHalf maxDilatation beurlingAhlfors dzbar toExt)

/-- Helper for `para18_3_simple_earthquake` (§18.3). On `ℍ` the extension `z ↦ e^{t(π − arg z)/π} z` is
`e^t z Q(z) \overline{Q(z)}` with the holomorphic `Q(z) = exp(iκ log z)`, `κ = t/(2π)` (`|Q|² = e^{−2κ arg z}`). -/
theorem gl18_quake_eq (t : ℝ) {w : ℂ} :
    Complex.exp (t * (π - arg w) / π) * w =
      Complex.exp t * w * Complex.exp (I * ((t / (2 * π) : ℝ) : ℂ) * log w) *
        conj (Complex.exp (I * ((t / (2 * π) : ℝ) : ℂ) * log w)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [mul_assoc (Complex.exp t * w), Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (I * ((t / (2 * π) : ℝ) : ℂ) * log w).re = -(t / (2 * π)) * arg w := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.log_im]
    ring
  rw [hre, ← Real.exp_nat_mul, Complex.ofReal_exp]
  rw [mul_comm (Complex.exp t * w), ← mul_assoc, ← Complex.exp_add]
  congr 1
  rw [mul_comm]
  congr 1
  push_cast
  field_simp
  ring

/-- Helper for `para18_3_simple_earthquake` (§18.3). The dilatation quotient of the extension is the constant
`(√(1 + κ²) + |κ|)/(√(1 + κ²) − |κ|)`, `κ = t/(2π)`, on `ℍ`. -/
theorem gl18_quake_quot (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (‖LiZhongQC.dz (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z‖ +
        ‖dzbar (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z‖) /
      (‖LiZhongQC.dz (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z‖ -
        ‖dzbar (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z‖) =
      (Real.sqrt (1 + (t / (2 * π)) ^ 2) + |t / (2 * π)|) / (Real.sqrt (1 + (t / (2 * π)) ^ 2) - |t / (2 * π)|) := by
  set κ : ℝ := t / (2 * π) with hκ
  have hzs : z ∈ slitPlane := Or.inr hz.ne'
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  set Q : ℂ → ℂ := fun w => Complex.exp (I * (κ : ℂ) * log w) with hQ
  set u : ℂ → ℂ := fun w => Complex.exp t * w * Q w with hu
  -- `Q` and `u` are holomorphic at `z`
  have hQd : HasDerivAt Q (Q z * (I * κ * z⁻¹)) z := by
    have h1 := ((Complex.hasStrictDerivAt_log hzs).hasDerivAt.const_mul (I * (κ : ℂ))).cexp
    simpa [hQ, mul_comm, mul_left_comm, mul_assoc] using h1
  have hud : HasDerivAt u (Complex.exp t * (Q z + z * (Q z * (I * κ * z⁻¹)))) z := by
    have h1 := ((hasDerivAt_id z).const_mul (Complex.exp t)).mul hQd
    convert h1 using 1
    · funext w; simp [hu]
    · simp; ring
  have hQh : DifferentiableAt ℂ Q z := hQd.differentiableAt
  have huh : DifferentiableAt ℂ u z := hud.differentiableAt
  -- the extension equals `u · conj Q` near `z`
  have hev : (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) =ᶠ[𝓝 z] fun w => u w * conj (Q w) := by
    refine Eventually.of_forall fun w => ?_
    simp only [hu, hQ]
    rw [gl18_quake_eq t]
  have hf : fderiv ℝ (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z =
      fderiv ℝ (fun w => u w * conj (Q w)) z := hev.fderiv_eq
  have hdzF : LiZhongQC.dz (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z =
      LiZhongQC.dz (fun w => u w * conj (Q w)) z := by
    unfold LiZhongQC.dz
    rw [hf]
  have hdzbF : dzbar (fun w : ℂ => Complex.exp (t * (π - arg w) / π) * w) z =
      dzbar (fun w => u w * conj (Q w)) z := by
    unfold dzbar
    rw [hf]
  have hQR : DifferentiableAt ℝ Q z := hQh.restrictScalars ℝ
  have huR : DifferentiableAt ℝ u z := huh.restrictScalars ℝ
  have hcQR : DifferentiableAt ℝ (fun w => conj (Q w)) z :=
    (Complex.conjCLE.differentiableAt).comp z hQR
  have hdzbQ : dzbar Q z = 0 := (LiZhongQC.cauchyRiemann_iff.1 hQh).2
  have hdzbu : dzbar u z = 0 := (LiZhongQC.cauchyRiemann_iff.1 huh).2
  have hdzQ : LiZhongQC.dz Q z = Q z * (I * κ * z⁻¹) := by rw [LiZhongQC.dz_eq_deriv hQh, hQd.deriv]
  have hdzu : LiZhongQC.dz u z = Complex.exp t * (Q z + z * (Q z * (I * κ * z⁻¹))) := by
    rw [LiZhongQC.dz_eq_deriv huh, hud.deriv]
  have hA : LiZhongQC.dz (fun w => u w * conj (Q w)) z = conj (Q z) * (Complex.exp t * Q z * (1 + I * κ)) := by
    rw [LiZhongQC.dz_mul huR hcQR, LiZhongQC.dz_conj hQR, hdzbQ, map_zero, mul_zero, zero_add, hdzu]
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination (conj (Q z) * Complex.exp t * Q z * I * κ) * hzz
  have hB : dzbar (fun w => u w * conj (Q w)) z = Complex.exp t * z * Q z * conj (Q z * (I * κ * z⁻¹)) := by
    rw [LiZhongQC.dzbar_mul huR hcQR, LiZhongQC.dzbar_conj hQR, hdzbu, hdzQ]
    simp only [hu]
    ring
  -- norms
  have hQn : 0 < ‖Q z‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have het : ‖Complex.exp t‖ = Real.exp t := by rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t)]
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hn1 : ‖1 + I * (κ : ℂ)‖ = Real.sqrt (1 + κ ^ 2) := by
    rw [show (1 : ℂ) + I * κ = ⟨1, κ⟩ by apply Complex.ext <;> simp, Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  have hn2 : ‖I * (κ : ℂ) * z⁻¹‖ = |κ| / ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, div_eq_mul_inv]
  set c : ℝ := Real.exp t * ‖Q z‖ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hdzn : ‖LiZhongQC.dz (fun w => u w * conj (Q w)) z‖ = c * Real.sqrt (1 + κ ^ 2) := by
    rw [hA, norm_mul, Complex.norm_conj, norm_mul, norm_mul, het, hn1, hc]
    ring
  have hdzbn : ‖dzbar (fun w => u w * conj (Q w)) z‖ = c * |κ| := by
    rw [hB, norm_mul, Complex.norm_conj, norm_mul, norm_mul, norm_mul, het, hn2, hc]
    field_simp
  rw [hdzF, hdzbF, hdzn, hdzbn, ← mul_add, ← mul_sub, mul_div_mul_left _ _ hcpos.ne']

/-- Helper for `para18_3_simple_earthquake` (§18.3). `K + 1/K = 2 + 4κ²` for
`K = (√(1 + κ²) + |κ|)/(√(1 + κ²) − |κ|)`. -/
theorem gl18_quake_K (κ : ℝ) :
    (Real.sqrt (1 + κ ^ 2) + |κ|) / (Real.sqrt (1 + κ ^ 2) - |κ|) +
      1 / ((Real.sqrt (1 + κ ^ 2) + |κ|) / (Real.sqrt (1 + κ ^ 2) - |κ|)) = 2 + 4 * κ ^ 2 := by
  have hs : Real.sqrt (1 + κ ^ 2) ^ 2 = 1 + κ ^ 2 := Real.sq_sqrt (by positivity)
  have ha : |κ| ^ 2 = κ ^ 2 := sq_abs κ
  have hlt : |κ| < Real.sqrt (1 + κ ^ 2) := by
    rw [← Real.sqrt_sq (abs_nonneg κ), ha]
    exact Real.sqrt_lt_sqrt (sq_nonneg κ) (by linarith)
  have h1 : 0 < Real.sqrt (1 + κ ^ 2) - |κ| := by linarith
  have h2 : 0 < Real.sqrt (1 + κ ^ 2) + |κ| := by positivity
  rw [one_div_div]
  field_simp
  nlinarith [hs, ha]

/-- **Example 1** (a simple earthquake, (18.1), (18.2), §18.3, l. 13368). `h_t(x) = eᵗx` for `x ≥ 0`, `x` for `x ≤ 0`:
`h_{s+t} = h_s ∘ h_t`, `d/dt h_t(x) = E(h_t(x))` with `E(x) = max(x, 0)`, and `h̃_t(re^{iθ}) = e^{t(π − θ)/π} r e^{iθ}`
extends `h_t` to `ℍ` with dilatation `K`, `K + 1/K = 2 + (t/π)²`. -/
theorem para18_3_simple_earthquake :
    let h : ℝ → ℝ → ℝ := fun t x => if 0 ≤ x then Real.exp t * x else x
    let E : ℝ → ℝ := fun x => if 0 ≤ x then x else 0
    let F : ℝ → ℂ → ℂ := fun t z => Complex.exp (t * (π - arg z) / π) * z
    (∀ s t x, h (s + t) x = h s (h t x)) ∧ (∀ t x, HasDerivAt (fun t => h t x) (E (h t x)) t) ∧
      (∀ t : ℝ, ∀ x : ℝ, x ≠ 0 → Tendsto (F t) (𝓝[upperHalf] (x : ℂ)) (𝓝 (h t x : ℂ))) ∧
      ∀ t : ℝ, (maxDilatation (F t) upperHalf).toReal + 1 / (maxDilatation (F t) upperHalf).toReal =
        2 + (t / π) ^ 2 := by
  intro h E F
  refine ⟨fun s t x => ?_, fun t x => ?_, fun t x hx => ?_, fun t => ?_⟩
  · -- the flow property
    simp only [h]
    by_cases hx : 0 ≤ x
    · have h1 : 0 ≤ Real.exp t * x := mul_nonneg (Real.exp_pos t).le hx
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left h1, Real.exp_add]
      ring
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]
  · -- the infinitesimal generator `E`
    simp only [h, E]
    by_cases hx : 0 ≤ x
    · have h1 : 0 ≤ Real.exp t * x := mul_nonneg (Real.exp_pos t).le hx
      simp only [ite_eq_left hx, ite_eq_left h1]
      exact (Real.hasDerivAt_exp t).mul_const x
    · simp only [ite_eq_right hx]
      exact hasDerivAt_const t x
  · -- boundary values
    simp only [F, h]
    have hg : Continuous fun θ : ℝ => Complex.exp (t * (π - θ) / π) := by fun_prop
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · -- `arg z → π` from `ℍ` at a negative point
      have harg : Tendsto arg (𝓝[upperHalf] (x : ℂ)) (𝓝 π) :=
        (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by simpa using hneg) (by simp)).mono_left
          (nhdsWithin_mono _ fun z (hz : z ∈ upperHalf) => show 0 ≤ z.im from le_of_lt hz)
      have h1 := ((hg.tendsto π).comp harg).mul (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (x : ℂ))))
      rw [ite_eq_right (not_le.2 hneg)]
      convert h1 using 2 <;> simp
    · -- `arg z → 0` at a positive point
      have hslit : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hpos)
      have harg : Tendsto arg (𝓝[upperHalf] (x : ℂ)) (𝓝 0) := by
        have := (Complex.continuousAt_arg hslit).tendsto
        rw [Complex.arg_ofReal_of_nonneg hpos.le] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h1 := ((hg.tendsto 0).comp harg).mul (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (x : ℂ))))
      rw [ite_eq_left hpos.le]
      have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      convert h1 using 2
      · simp
      · push_cast
        rw [sub_zero, mul_div_assoc, div_self hπc, mul_one]
  · -- the maximal dilatation
    have hmeas : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
    have hne : volume.restrict upperHalf ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact (LiZhongQC.isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩)
    set K : ℝ := (Real.sqrt (1 + (t / (2 * π)) ^ 2) + |t / (2 * π)|) /
      (Real.sqrt (1 + (t / (2 * π)) ^ 2) - |t / (2 * π)|) with hK
    have hKpos : 0 < K := by
      have hs : Real.sqrt (1 + (t / (2 * π)) ^ 2) ^ 2 = 1 + (t / (2 * π)) ^ 2 := Real.sq_sqrt (by positivity)
      have hlt : |t / (2 * π)| < Real.sqrt (1 + (t / (2 * π)) ^ 2) := by
        rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      exact div_pos (by positivity) (by linarith)
    have hae : (fun z => ENNReal.ofReal ((‖LiZhongQC.dz (F t) z‖ + ‖dzbar (F t) z‖) /
        (‖LiZhongQC.dz (F t) z‖ - ‖dzbar (F t) z‖))) =ᵐ[volume.restrict upperHalf] fun _ => ENNReal.ofReal K := by
      refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_)
      simp only [F]
      rw [gl18_quake_quot t hz]
    unfold maxDilatation
    rw [essSup_congr_ae hae, essSup_const _ hne, ENNReal.toReal_ofReal hKpos.le, hK, gl18_quake_K]
    field_simp
    ring

/-- Helper for `para18_3_simple_bend` (§18.3). `|x|^a · sign x = x^a` for `x > 0`. -/
theorem gl18_bend_pos {x a : ℝ} (hx : 0 < x) : |x| ^ a * Real.sign x = x ^ a := by
  rw [abs_of_pos hx, Real.sign_of_pos hx, mul_one]

/-- Helper for `para18_3_simple_bend` (§18.3). `|x|^a · sign x = −(−x)^a` for `x < 0`. -/
theorem gl18_bend_neg {x a : ℝ} (hx : x < 0) : |x| ^ a * Real.sign x = -(-x) ^ a := by
  rw [abs_of_neg hx, Real.sign_of_neg hx, mul_neg_one]

/-- Helper for `para18_3_simple_bend` (§18.3). The extension `z ↦ |z|^{a-1} z` has constant dilatation quotient
`a` off `0` (`a ≥ 1`), from the radial-stretch derivatives `s15_ra_dz`, `s15_ra_dzbar`. -/
theorem gl18_bend_quot {a : ℝ} (ha : 1 ≤ a) {z : ℂ} (hz : z ≠ 0) :
    (‖LiZhongQC.dz (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z‖ +
        ‖dzbar (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z‖) /
      (‖LiZhongQC.dz (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z‖ -
        ‖dzbar (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z‖) = a := by
  have hev : (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) =ᶠ[𝓝 z] fun w : ℂ => ‖w‖ ^ (a - 1) • w := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [Real.rpow_sub_one (norm_ne_zero_iff.2 hw), Complex.real_smul]
  have hf : fderiv ℝ (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z = fderiv ℝ (fun w : ℂ => ‖w‖ ^ (a - 1) • w) z :=
    hev.fderiv_eq
  have hdz : LiZhongQC.dz (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z =
      LiZhongQC.dz (fun w : ℂ => ‖w‖ ^ (a - 1) • w) z := by
    unfold LiZhongQC.dz
    rw [hf]
  have hdzb : dzbar (fun w : ℂ => ((‖w‖ ^ a / ‖w‖ : ℝ) : ℂ) * w) z = dzbar (fun w : ℂ => ‖w‖ ^ (a - 1) • w) z := by
    unfold dzbar
    rw [hf]
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hzp : 0 < ‖z‖ ^ (a - 1) := Real.rpow_pos_of_pos hpos _
  have hk := LiZhongQC.s15_ra_key hz (a - 1)
  have hsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have hn1 : ‖LiZhongQC.dz (fun w : ℂ => ‖w‖ ^ (a - 1) • w) z‖ = (a - 1 + 2) / 2 * ‖z‖ ^ (a - 1) := by
    rw [LiZhongQC.s15_ra_dz hz]
    exact Complex.norm_of_nonneg (by nlinarith)
  have hn2 : ‖dzbar (fun w : ℂ => ‖w‖ ^ (a - 1) • w) z‖ = (a - 1) / 2 * ‖z‖ ^ (a - 1) := by
    rw [LiZhongQC.s15_ra_dzbar hz, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := Real.rpow_nonneg (norm_nonneg z) (a - 1 - 2); nlinarith), hsq, ← hk]
    ring
  rw [hdz, hdzb, hn1, hn2]
  have : (a - 1 + 2) / 2 * ‖z‖ ^ (a - 1) - (a - 1) / 2 * ‖z‖ ^ (a - 1) = ‖z‖ ^ (a - 1) := by ring
  rw [this, div_eq_iff hzp.ne']
  ring

/-- **Example 2** (a simple bend, (18.3), (18.4), §18.3, l. 13391). `h_t(x) = |x|^{eᵗ} sign(x)`: `h_{s+t} = h_s ∘ h_t`,
`d/dt h_t(x) = B(h_t(x))` with `B(x) = x log|x|`, and `h̃_t(re^{iθ}) = r^{eᵗ} e^{iθ}` extends `h_t` to `ℍ` with
dilatation `eᵗ` (`t ≥ 0`). -/
theorem para18_3_simple_bend :
    let h : ℝ → ℝ → ℝ := fun t x => |x| ^ Real.exp t * Real.sign x
    let B : ℝ → ℝ := fun x => x * Real.log |x|
    let F : ℝ → ℂ → ℂ := fun t z => (‖z‖ ^ Real.exp t / ‖z‖ : ℝ) * z
    (∀ s t x, h (s + t) x = h s (h t x)) ∧ (∀ t x, x ≠ 0 → HasDerivAt (fun t => h t x) (B (h t x)) t) ∧
      (∀ t : ℝ, ∀ x : ℝ, x ≠ 0 → Tendsto (F t) (𝓝[upperHalf] (x : ℂ)) (𝓝 (h t x : ℂ))) ∧
      ∀ t : ℝ, 0 ≤ t → (maxDilatation (F t) upperHalf).toReal = Real.exp t := by
  intro h B F
  refine ⟨fun s t x => ?_, fun t x hx => ?_, fun t x hx => ?_, fun t ht => ?_⟩
  · -- the flow property
    simp only [h]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have h1 : 0 < (-x) ^ Real.exp t := Real.rpow_pos_of_pos (by linarith) _
      rw [gl18_bend_neg hx, gl18_bend_neg hx, gl18_bend_neg (by linarith : -(-x) ^ Real.exp t < 0), neg_neg,
        ← Real.rpow_mul (by linarith), Real.exp_add, mul_comm (Real.exp s)]
    · simp
    · have h1 : 0 < x ^ Real.exp t := Real.rpow_pos_of_pos hx _
      rw [gl18_bend_pos hx, gl18_bend_pos hx, gl18_bend_pos h1, ← Real.rpow_mul hx.le, Real.exp_add,
        mul_comm (Real.exp s)]
  · -- the infinitesimal generator `B`
    simp only [h, B]
    have hax : 0 < |x| := abs_pos.2 hx
    have hd : HasDerivAt (fun t => |x| ^ Real.exp t * Real.sign x)
        (Real.log |x| * Real.exp t * |x| ^ Real.exp t * Real.sign x) t :=
      ((Real.hasDerivAt_exp t).const_rpow hax).mul_const _
    convert hd using 1
    have hs : |Real.sign x| = 1 := by
      rcases lt_or_gt_of_ne hx with h' | h'
      · rw [Real.sign_of_neg h', abs_neg, abs_one]
      · rw [Real.sign_of_pos h', abs_one]
    rw [abs_mul, hs, mul_one, abs_of_pos (Real.rpow_pos_of_pos hax _), Real.log_rpow hax]
    ring
  · -- boundary values
    simp only [F, h]
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hc : ContinuousAt (fun z : ℂ => ((‖z‖ ^ Real.exp t / ‖z‖ : ℝ) : ℂ) * z) (x : ℂ) := by
      have hn : ‖(x : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 hx'
      refine ContinuousAt.mul ?_ continuousAt_id
      refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact ((continuous_norm.continuousAt.rpow_const (Or.inl hn)).div continuous_norm.continuousAt hn)
    have hval : ((‖(x : ℂ)‖ ^ Real.exp t / ‖(x : ℂ)‖ : ℝ) : ℂ) * (x : ℂ) = ((|x| ^ Real.exp t * Real.sign x : ℝ) : ℂ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rcases lt_or_gt_of_ne hx with h' | h'
      · rw [Real.sign_of_neg h', abs_of_neg h']
        push_cast
        field_simp
      · rw [Real.sign_of_pos h', abs_of_pos h']
        push_cast
        field_simp
    rw [← hval]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- the maximal dilatation is `eᵗ`
    have ha : 1 ≤ Real.exp t := Real.one_le_exp ht
    have hmeas : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
    have hne : volume.restrict upperHalf ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact (LiZhongQC.isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩)
    have hae : (fun z => ENNReal.ofReal ((‖LiZhongQC.dz (F t) z‖ + ‖dzbar (F t) z‖) /
        (‖LiZhongQC.dz (F t) z‖ - ‖dzbar (F t) z‖))) =ᵐ[volume.restrict upperHalf]
        fun _ => ENNReal.ofReal (Real.exp t) := by
      refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_)
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp [upperHalf] at hz
      simp only [F]
      rw [gl18_bend_quot ha hz0]
    unfold maxDilatation
    rw [essSup_congr_ae hae, essSup_const _ hne, ENNReal.toReal_ofReal (Real.exp_pos t).le]

/-- Helper for `para18_3_hilbert_E` (§18.3, C0). Both fields grow slower than `x²`, so their coefficients at `∞`
(`zInfCoeff`) are `0`: `x log|x|/x² → 0` and `max(x, 0)/x² → 0` as `x → ±∞`. -/
theorem gl18_he_zinf :
    Tendsto (fun x : ℝ => ((x * Real.log |x| : ℝ) : ℂ) / (x : ℂ) ^ 2) (cocompact ℝ) (𝓝 0) ∧
      Tendsto (fun x : ℝ => ((max x 0 : ℝ) : ℂ) / (x : ℂ) ^ 2) (cocompact ℝ) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hA : Tendsto (fun x : ℝ => Real.log |x| / x) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]
    constructor
    · have h3 := (h1.comp tendsto_neg_atBot_atTop).neg
      rw [neg_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_lt_atBot 0] with x hx
      rw [Function.comp_apply, abs_of_neg hx, div_neg, neg_neg]
    · refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [abs_of_pos hx]
  have hB : Tendsto (fun x : ℝ => max x 0 / x ^ 2) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]
    constructor
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_atBot 0] with x hx
      rw [max_eq_right hx.le, zero_div]
    · refine tendsto_inv_atTop_zero.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [max_eq_left hx.le]
      field_simp
  have hc : ∀ {f : ℝ → ℝ}, Tendsto f (cocompact ℝ) (𝓝 0) →
      Tendsto (fun x => ((f x : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := fun h => by
    have h' := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h'
    exact h'
  constructor
  · refine (hc hA).congr fun x => ?_
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      push_cast
      field_simp
  · refine (hc hB).congr fun x => ?_
    push_cast
    rfl

/-- Helper for `para18_3_hilbert_E` (§18.3, C0). The integrand of (A) off `ξ = x`:
`ξ log|ξ| · kernelR x ξ = x log|ξ| (1/(ξ − x) − 1/(ξ − 1))`, since `ξ kernelR x ξ = x (1/(ξ − x) − 1/(ξ − 1))` (at
`ξ = 0, 1` both sides are `0`). -/
theorem gl18_he_kernel_A (x ξ : ℝ) (hξ : ξ ≠ x) :
    ((ξ * Real.log |ξ| : ℝ) : ℂ) * kernelR x ξ = ((x * (Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1))) : ℝ) : ℂ) := by
  show ((ξ * Real.log |ξ| : ℝ) : ℂ) * ((x : ℂ) * (x - 1) / ((ξ : ℂ) * (ξ - 1) * (ξ - x))) = _
  by_cases h0 : ξ = 0
  · subst h0
    simp
  by_cases h1 : ξ = 1
  · subst h1
    simp
  have h0' : (ξ : ℂ) ≠ 0 := by exact_mod_cast h0
  have h1' : (ξ : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h1)
  have hx' : (ξ : ℂ) - x ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hξ)
  push_cast
  field_simp
  ring

/-- Helper for `para18_3_hilbert_E` (§18.3, C0). The integrand of (B) off `ξ = x`: the normalized field is
`max(ξ, 0) − ξ = max(−ξ, 0)`, so the integrand is `−x (1/(ξ − x) − 1/(ξ − 1))` for `ξ < 0` and `0` for `ξ ≥ 0`. -/
theorem gl18_he_kernel_B (x ξ : ℝ) (hξ : ξ ≠ x) :
    (((max ξ 0 : ℝ) : ℂ) - ξ) * kernelR x ξ = ((if ξ < 0 then -x * (1 / (ξ - x) - 1 / (ξ - 1)) else 0 : ℝ) : ℂ) := by
  show (((max ξ 0 : ℝ) : ℂ) - ξ) * ((x : ℂ) * (x - 1) / ((ξ : ℂ) * (ξ - 1) * (ξ - x))) = _
  by_cases hneg : ξ < 0
  · simp only [hneg, ↓reduceIte]
    rw [max_eq_right hneg.le]
    have h0' : (ξ : ℂ) ≠ 0 := by exact_mod_cast hneg.ne
    have h1' : (ξ : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (show ξ ≠ 1 by linarith))
    have hx' : (ξ : ℂ) - x ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hξ)
    push_cast
    field_simp
    ring
  · simp only [hneg, ↓reduceIte]
    rw [max_eq_left (not_lt.1 hneg)]
    simp

/-- Helper for `para18_3_hilbert_E` (§18.3, C0). Evaluation of `hilbertPV`: if the integrand is a real function `g`
off `ξ = x` and the truncated integrals of `g` tend to `L`, then `H V(x) = L/π`. -/
theorem gl18_he_pv_eval {V : ℂ → ℂ} {x : ℝ} {g : ℝ → ℝ} {L : ℝ} (hV : ∀ ξ : ℝ, ξ ≠ x → V ξ * kernelR x ξ = (g ξ : ℂ))
    (hg : Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, g ξ) (𝓝[>] 0) (𝓝 L)) :
    hilbertPV V x = ((L / π : ℝ) : ℂ) := by
  show limUnder (𝓝[>] (0 : ℝ)) (fun ε => (1 / π) * ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, V ξ * kernelR x ξ) = _
  refine Tendsto.limUnder_eq ?_
  have hc : Tendsto (fun ε : ℝ => (1 / (π : ℂ)) * ((∫ ξ in {ξ : ℝ | ε < |ξ - x|}, g ξ : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((1 / (π : ℂ)) * (L : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto L).comp hg).const_mul (1 / (π : ℂ))
  rw [show ((L / π : ℝ) : ℂ) = (1 / (π : ℂ)) * (L : ℂ) by push_cast; ring]
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  congr 1
  rw [← integral_complex_ofReal]
  have hS : MeasurableSet {ξ : ℝ | ε < |ξ - x|} := measurableSet_lt measurable_const (by fun_prop)
  refine setIntegral_congr_fun hS fun ξ hξ => (hV ξ fun h => ?_).symm
  rw [mem_ofPred_eq, h, sub_self, abs_zero] at hξ
  exact absurd hξ (not_lt.2 (le_of_lt hε))

/-- Helper for `para18_3_hilbert_E` (§18.3, C2). Splitting a truncated integral at `0`, with `ξ = −u` on the negative
half-line (the point `ξ = 0` is null). -/
theorem gl18_he_split {f : ℝ → ℝ} {x ε : ℝ} (hf : IntegrableOn f {ξ : ℝ | ε < |ξ - x|}) :
    ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, f ξ =
      (∫ u in {u : ℝ | 0 < u ∧ ε < |u - x|}, f u) + ∫ u in {u : ℝ | 0 < u ∧ ε < |u + x|}, f (-u) := by
  rw [← integral_inter_add_sdiff measurableSet_Ioi hf]
  have hpos : ({ξ : ℝ | ε < |ξ - x|} ∩ Ioi 0 : Set ℝ) = {u : ℝ | 0 < u ∧ ε < |u - x|} :=
    Set.ext fun u => by
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi]
      exact and_comm
  -- the negative half-line, reflected (the point `0` is null)
  have h1 : ∫ ξ in {ξ : ℝ | ε < |ξ - x|} \ Ioi 0, f ξ = ∫ ξ in {ξ : ℝ | ε < |ξ - x|} ∩ Iio 0, f ξ := by
    rw [sdiff_eq, compl_Ioi]
    exact setIntegral_congr_set (EventuallyEqSet.inter (by rfl) Iio_ae_eq_Iic.symm)
  have h2 : (Neg.neg ⁻¹' ({ξ : ℝ | ε < |ξ - x|} ∩ Iio 0) : Set ℝ) = {u : ℝ | 0 < u ∧ ε < |u + x|} :=
    Set.ext fun u => by
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Iio]
      rw [show -u - x = -(u + x) by ring, abs_neg, neg_lt_zero, and_comm]
  rw [hpos, h1, ← (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f ({ξ : ℝ | ε < |ξ - x|} ∩ Iio 0), h2]

/-- Helper for `para18_3_hilbert_E` (§18.3, C2). For `f` integrable on `(0, ∞)`, excising a shrinking interval
around `y` does not change the integral in the limit (dominated convergence). -/
theorem gl18_he_trunc {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (y : ℝ) :
    Tendsto (fun ε : ℝ => ∫ u in {u : ℝ | 0 < u ∧ ε < |u - y|}, f u) (𝓝[>] 0) (𝓝 (∫ u in Ioi 0, f u)) := by
  have hm : ∀ ε : ℝ, MeasurableSet {u : ℝ | ε < |u - y|} := fun ε =>
    measurableSet_lt measurable_const (by fun_prop)
  have e : ∀ ε : ℝ, ∫ u in {u : ℝ | 0 < u ∧ ε < |u - y|}, f u =
      ∫ u in Ioi 0, {u : ℝ | ε < |u - y|}.indicator f u := fun ε => (setIntegral_indicator (hm ε)).symm
  rw [show (fun ε : ℝ => ∫ u in {u : ℝ | 0 < u ∧ ε < |u - y|}, f u) =
    fun ε : ℝ => ∫ u in Ioi 0, {u : ℝ | ε < |u - y|}.indicator f u from funext e]
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖f u‖)
    (Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε => Eventually.of_forall fun u => norm_indicator_le_norm_self _ _) hf.norm ?_
  have hne : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), u ≠ y :=
    ae_restrict_of_ae (by filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)] with u hu using hu)
  filter_upwards [hne] with u hu
  have hpos : 0 < |u - y| := abs_pos.2 (sub_ne_zero.2 hu)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  rw [indicator_of_mem (show u ∈ {u : ℝ | ε < |u - y|} from hε.2)]

/-- Helper for `para18_3_hilbert_E` (§18.3, C2b, the principal value isolated). The compensator
`1/(u − y) − 1/(u + 1)` is integrable on `(0, ∞)` off a neighbourhood of `y`, and its principal value is `−log y`: on
`(0, y − ε) ∪ (y + ε, ∞)` the antiderivative `log|u − y| − log(u + 1)` gives
`log(y + ε + 1) − log(y − ε + 1) − log y` (the `log ε` terms cancel). -/
theorem gl18_he_comp {y : ℝ} (hy : 0 < y) :
    (∀ ε > 0, IntegrableOn (fun u : ℝ => 1 / (u - y) - 1 / (u + 1)) {u : ℝ | 0 < u ∧ ε < |u - y|}) ∧
      Tendsto (fun ε : ℝ => ∫ u in {u : ℝ | 0 < u ∧ ε < |u - y|}, (1 / (u - y) - 1 / (u + 1))) (𝓝[>] 0)
        (𝓝 (-Real.log y)) := by
  -- on `(a, ∞)`, `a > y`: the antiderivative `log(u − y) − log(u + 1)` (increasing, tending to `0`)
  have hF : ∀ u : ℝ, y < u → HasDerivAt (fun u => Real.log (u - y) - Real.log (u + 1))
      (1 / (u - y) - 1 / (u + 1)) u := fun u hu => by
    have h1 := ((hasDerivAt_id' u).sub_const y).log (by linarith : u - y ≠ 0)
    have h2 := ((hasDerivAt_id' u).add_const 1).log (by linarith : u + 1 ≠ 0)
    exact h1.sub h2
  have hFpos : ∀ u : ℝ, y < u → 0 ≤ 1 / (u - y) - 1 / (u + 1) := fun u hu => by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hFlim : Tendsto (fun u => Real.log (u - y) - Real.log (u + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => 1 - (y + 1) / (u + 1)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := y + 1)).div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
    rw [Real.log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop y] with u hu
    have hu1 : u + 1 ≠ 0 := by linarith
    rw [Function.comp_apply, ← Real.log_div (by linarith) (by linarith)]
    congr 1
    field_simp
    ring
  have hIoi : ∀ a : ℝ, y < a → IntegrableOn (fun u : ℝ => 1 / (u - y) - 1 / (u + 1)) (Ioi a) ∧
      ∫ u in Ioi a, (1 / (u - y) - 1 / (u + 1)) = 0 - (Real.log (a - y) - Real.log (a + 1)) := fun a ha => by
    have hc : ContinuousWithinAt (fun u => Real.log (u - y) - Real.log (u + 1)) (Ici a) a :=
      (hF a ha).continuousAt.continuousWithinAt
    have hd : ∀ u ∈ Ioi a, HasDerivAt (fun u => Real.log (u - y) - Real.log (u + 1)) (1 / (u - y) - 1 / (u + 1)) u :=
      fun u hu => hF u (ha.trans hu)
    have hp : ∀ u ∈ Ioi a, 0 ≤ 1 / (u - y) - 1 / (u + 1) := fun u hu => hFpos u (ha.trans hu)
    exact ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp hFlim, integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp hFlim⟩
  -- on `[0, y − ε]`: the antiderivative `log(y − u) − log(u + 1)`
  have hG : ∀ u : ℝ, u < y → 0 ≤ u → HasDerivAt (fun u => Real.log (y - u) - Real.log (u + 1))
      (1 / (u - y) - 1 / (u + 1)) u := fun u hu hu1 => by
    have h1 := ((hasDerivAt_id' u).const_sub y).log (by linarith : y - u ≠ 0)
    have h2 := ((hasDerivAt_id' u).add_const 1).log (by linarith : u + 1 ≠ 0)
    refine (h1.sub h2).congr_deriv ?_
    have : y - u ≠ 0 := by linarith
    have : u - y ≠ 0 := by linarith
    field_simp
    ring
  have hIcc : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun u : ℝ => 1 / (u - y) - 1 / (u + 1)) (Icc 0 (y - ε)) := by
    intro ε hε
    refine ContinuousOn.integrableOn_Icc fun u hu => ?_
    have h1 : u - y ≠ 0 := by linarith [hu.2]
    have h2 : u + 1 ≠ 0 := by linarith [hu.1]
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_const.div ((continuous_id.sub continuous_const).continuousAt) (by simpa using h1)).sub
      (continuousAt_const.div ((continuous_id.add continuous_const).continuousAt) (by simpa using h2))
  have hsub : ∀ ε : ℝ, 0 < ε → {u : ℝ | 0 < u ∧ ε < |u - y|} ⊆ Icc 0 (y - ε) ∪ Ioi (y + ε) := by
    intro ε hε u hu
    obtain ⟨hu0, hu1⟩ := hu
    rcases lt_abs.1 hu1 with h | h
    · exact Or.inr (by rw [mem_Ioi]; linarith)
    · exact Or.inl ⟨hu0.le, by linarith⟩
  refine ⟨fun ε hε => ((hIcc ε hε).union (hIoi (y + ε) (by linarith)).1).mono_set (hsub ε hε), ?_⟩
  -- the truncated integral is `log(y + ε + 1) − log(y − ε + 1) − log y` for `0 < ε < y`
  have hval : ∀ ε : ℝ, 0 < ε → ε < y → ∫ u in {u : ℝ | 0 < u ∧ ε < |u - y|}, (1 / (u - y) - 1 / (u + 1)) =
      Real.log (y + ε + 1) - Real.log (y - ε + 1) - Real.log y := by
    intro ε hε hεy
    have hS : {u : ℝ | 0 < u ∧ ε < |u - y|} = Ioo 0 (y - ε) ∪ Ioi (y + ε) := by
      ext u
      simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi, lt_abs]
      constructor
      · rintro ⟨h0, h | h⟩
        · exact Or.inr (by linarith)
        · exact Or.inl ⟨h0, by linarith⟩
      · rintro (⟨h0, h⟩ | h)
        · exact ⟨h0, Or.inr (by linarith)⟩
        · exact ⟨by linarith, Or.inl (by linarith)⟩
    obtain ⟨hint2, hval2⟩ := hIoi (y + ε) (by linarith)
    have hint1 : IntegrableOn (fun u : ℝ => 1 / (u - y) - 1 / (u + 1)) (Ioo 0 (y - ε)) :=
      (hIcc ε hε).mono_set Ioo_subset_Icc_self
    have hle : (0 : ℝ) ≤ y - ε := by linarith
    have hval1 : ∫ u in Ioo 0 (y - ε), (1 / (u - y) - 1 / (u + 1)) =
        (Real.log (y - (y - ε)) - Real.log (y - ε + 1)) - (Real.log (y - 0) - Real.log (0 + 1)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u => Real.log (y - u) - Real.log (u + 1)) (fun u hu => ?_)
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).2 (hIcc ε hε))
      rw [uIcc_of_le hle] at hu
      exact hG u (by linarith [hu.2]) hu.1
    rw [hS, setIntegral_union (Set.disjoint_left.2 fun u h1 h2 => by
      rw [mem_Ioo] at h1
      rw [mem_Ioi] at h2
      linarith) measurableSet_Ioi hint1 hint2, hval1, hval2]
    rw [show y - (y - ε) = ε by ring, show y + ε - y = ε by ring, sub_zero, zero_add, Real.log_one]
    ring
  have hcont : ContinuousAt (fun ε : ℝ => Real.log (y + ε + 1) - Real.log (y - ε + 1) - Real.log y) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => Real.log (y + ε + 1)) 0 :=
      (Real.continuousAt_log (by linarith)).comp (f := fun ε : ℝ => y + ε + 1) (by fun_prop)
    have h2 : ContinuousAt (fun ε : ℝ => Real.log (y - ε + 1)) 0 :=
      (Real.continuousAt_log (by linarith)).comp (f := fun ε : ℝ => y - ε + 1) (by fun_prop)
    exact (h1.sub h2).sub continuousAt_const
  have hlim := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
  rw [show Real.log (y + 0 + 1) - Real.log (y - 0 + 1) - Real.log y = -Real.log y by ring_nf] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hy] with ε hε
  exact (hval ε hε.1 hε.2).symm

/-- Helper for `gl18_he_K`, `gl18_he_g` and `gl18_he_A0` (§18.3): the inversion `u = y/v` of `(0, ∞)`,
`∫₀^∞ f(u) du = ∫₀^∞ f(y/v) y/v² dv` (`integral_comp_rpow_Ioi` with `p = −1` after the scaling `u = y w`). -/
theorem gl18_he_inv (f : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ u in Ioi 0, f u = ∫ v in Ioi 0, f (y / v) * (y / v ^ 2) := by
  have h1 : ∫ w in Ioi 0, f (y * w) * y = ∫ u in Ioi 0, f u := by
    rw [integral_mul_const, integral_comp_mul_left_Ioi f 0 hy, mul_zero, smul_eq_mul]
    field_simp
  have h2 := integral_comp_rpow_Ioi (fun w => f (y * w) * y) (show (-1 : ℝ) ≠ 0 by norm_num)
  rw [h1] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv' : 0 < v := hv
  simp only [smul_eq_mul]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, abs_neg, abs_one, one_mul, Real.rpow_neg_one,
    Real.rpow_neg hv'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- Helper for `para18_3_hilbert_E` (§18.3): the dominating function `(|log u| + 1)/(u + 1)²` is integrable on
`(0, ∞)`: on `(0, 1]` it is at most `|log u| + 1`, on `(1, ∞)` at most `3 u^{−3/2}` (`log u ≤ 2√u`). -/
theorem gl18_he_dom : IntegrableOn (fun u : ℝ => (|Real.log u| + 1) / (u + 1) ^ 2) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hmeas : Measurable fun u : ℝ => (|Real.log u| + 1) / (u + 1) ^ 2 := by fun_prop
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hlog : IntegrableOn Real.log (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 intervalIntegral.intervalIntegrable_log'
    have hb : IntegrableOn (fun u : ℝ => |Real.log u| + 1) (Ioc 0 1) :=
      hlog.abs.add (integrableOn_const (by simp) (by simp))
    refine hb.mono' hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
    have hu0 : 0 < u := hu.1
    have h1 : 1 ≤ (u + 1) ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) h1
  · have hp : IntegrableOn (fun u : ℝ => 3 * u ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 3
    refine hp.mono' hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu1 : 1 < u := hu
    have hu0 : 0 < u := by linarith
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    have hs : Real.log u ≤ 2 * u ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div hu0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith
    have hs1 : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu1.le (by norm_num)
    have hsq : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_add hu0]
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hlog0, div_le_iff₀ (by positivity)]
    have h2 : u ^ 2 ≤ (u + 1) ^ 2 := by nlinarith
    have h3 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := by positivity
    calc Real.log u + 1 ≤ 3 * u ^ (1 / 2 : ℝ) := by linarith
      _ = 3 * u ^ (-(3 / 2 : ℝ)) * u ^ 2 := by rw [mul_assoc, hsq]
      _ ≤ 3 * u ^ (-(3 / 2 : ℝ)) * (u + 1) ^ 2 := by gcongr

/-- Helper for `para18_3_hilbert_E` (§18.3): integrability on `(0, ∞)` from the bound
`|f u| ≤ C (|log u| + 1)/(u + 1)²` (`gl18_he_dom`). -/
theorem gl18_he_intg {f : ℝ → ℝ} (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {C : ℝ}
    (hb : ∀ u : ℝ, 0 < u → |f u| ≤ C * ((|Real.log u| + 1) / (u + 1) ^ 2)) : IntegrableOn f (Ioi 0) :=
  (gl18_he_dom.const_mul C).mono' hm (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
    rw [Real.norm_eq_abs]
    exact hb u hu)

/-- Helper for `gl18_he_J_pos`, `gl18_he_J_neg` and `gl18_he_B_lim` (§18.3): integrability on a truncation from the
two half-lines (`ξ = −u` on the negative one; the point `0` is null). -/
theorem gl18_he_halves {f : ℝ → ℝ} {x ε : ℝ} (h1 : IntegrableOn f {u : ℝ | 0 < u ∧ ε < |u - x|})
    (h2 : IntegrableOn (fun u => f (-u)) {u : ℝ | 0 < u ∧ ε < |u + x|}) : IntegrableOn f {ξ : ℝ | ε < |ξ - x|} := by
  have hneg : IntegrableOn f ({ξ : ℝ | ε < |ξ - x|} ∩ Iio 0) := by
    have h2' : (Neg.neg ⁻¹' ({ξ : ℝ | ε < |ξ - x|} ∩ Iio 0) : Set ℝ) = {u : ℝ | 0 < u ∧ ε < |u + x|} :=
      Set.ext fun u => by
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Iio]
        rw [show -u - x = -(u + x) by ring, abs_neg, neg_lt_zero, and_comm]
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding, h2']
    exact h2
  have hzero : IntegrableOn f ({ξ : ℝ | ε < |ξ - x|} ∩ {0}) := by
    have h0 : volume ({ξ : ℝ | ε < |ξ - x|} ∩ {0}) = 0 :=
      measure_mono_null inter_subset_right (measure_singleton 0)
    rw [IntegrableOn, Measure.restrict_eq_zero.2 h0]
    exact integrable_zero_measure
  have hpos : IntegrableOn f ({ξ : ℝ | ε < |ξ - x|} ∩ Ioi 0) :=
    h1.mono_set fun u hu => ⟨hu.2, hu.1⟩
  have hcov : {ξ : ℝ | ε < |ξ - x|} ⊆ ({ξ : ℝ | ε < |ξ - x|} ∩ Ioi 0) ∪
      (({ξ : ℝ | ε < |ξ - x|} ∩ Iio 0) ∪ ({ξ : ℝ | ε < |ξ - x|} ∩ {0})) := by
    intro ξ hξ
    rcases lt_trichotomy ξ 0 with h | h | h
    · exact Or.inr (Or.inl ⟨hξ, h⟩)
    · exact Or.inr (Or.inr ⟨hξ, h⟩)
    · exact Or.inl ⟨hξ, h⟩
  exact (hpos.union (hneg.union hzero)).mono_set hcov

/-- Helper for `gl18_he_g` (§18.3): `|log u − log y| ≤ 2|u − y|/y` for `u ≥ y/2 > 0`
(`log t ≤ t − 1` and `log t ≥ 1 − 1/t` at `t = u/y`). -/
theorem gl18_he_logd {u y : ℝ} (hy : 0 < y) (hu : y / 2 ≤ u) : |Real.log u - Real.log y| ≤ 2 * |u - y| / y := by
  have hu0 : 0 < u := by linarith
  rw [← Real.log_div hu0.ne' hy.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos hu0 hy)
  have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hy)
  rw [inv_div] at h2
  have e1 : u / y - 1 = (u - y) / y := by field_simp
  have e2 : 1 - y / u = (u - y) / u := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_le]
  have hyu : (u - y) / y ≤ 2 * |u - y| / y := by
    rw [div_le_div_iff_of_pos_right hy]
    linarith [le_abs_self (u - y), abs_nonneg (u - y)]
  have hyu' : -(2 * |u - y| / y) ≤ (u - y) / u := by
    rcases le_total 0 (u - y) with h | h
    · have : 0 ≤ (u - y) / u := div_nonneg h hu0.le
      have : 0 ≤ 2 * |u - y| / y := by positivity
      linarith
    · rw [abs_of_nonpos h, neg_le, ← neg_div, div_le_iff₀ hu0]
      have : -(u - y) * (y / 2) ≤ -(u - y) * u := mul_le_mul_of_nonneg_left hu (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ hy] at *
      nlinarith
  constructor <;> linarith

/-- Helper for `gl18_he_g` and `gl18_he_A0` (§18.3): `|log u/(u − 1)| ≤ 8 (|log u| + 1)/(u + 1)` for `u > 0` (at
`u = 1` the left side is `0`). -/
theorem gl18_he_logq {u : ℝ} (hu : 0 < u) : |Real.log u / (u - 1)| ≤ 8 * (|Real.log u| + 1) / (u + 1) := by
  have hl0 := abs_nonneg (Real.log u)
  rcases eq_or_ne u 1 with rfl | hu1
  · simp only [sub_self, div_zero, abs_zero]
    positivity
  rw [abs_div, div_le_div_iff₀ (abs_pos.2 (sub_ne_zero.2 hu1)) (by linarith)]
  have h1 := Real.log_le_sub_one_of_pos hu
  have h2 := Real.one_sub_inv_le_log_of_pos hu
  rcases lt_or_ge u (1 / 2) with hlt | hge
  · -- `|u − 1| ≥ 1/2`
    have : 1 / 2 ≤ |u - 1| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    nlinarith
  · rcases lt_or_ge u 3 with hlt3 | hge3
    · -- `|log u| ≤ 2|u − 1|`
      have hlb : |Real.log u| ≤ 2 * |u - 1| := by
        rw [abs_le]
        have hinv : u⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hu (by norm_num)]
          linarith
        constructor
        · rcases le_total u 1 with h | h
          · rw [abs_of_nonpos (by linarith)]
            have : 1 - u⁻¹ = (u - 1) * u⁻¹ := by field_simp
            nlinarith [mul_le_mul_of_nonneg_left hinv (by linarith : (0 : ℝ) ≤ 1 - u)]
          · rw [abs_of_nonneg (by linarith)]
            nlinarith [Real.log_nonneg h]
        · linarith [le_abs_self (u - 1), abs_nonneg (u - 1)]
      nlinarith [abs_nonneg (u - 1)]
    · -- `u − 1 ≥ (u + 1)/2`
      rw [abs_of_pos (by linarith : (0 : ℝ) < u - 1)]
      nlinarith

/-- Helper for `gl18_he_rat` and `gl18_he_K` (§18.3): `|1/(v + 1) − 1/(v + y)| ≤ (|y − 1|/min(1, y))/(v + 1)²` for
`v > 0` (`v + y ≥ min(1, y)(v + 1)`). -/
theorem gl18_he_ratb {y : ℝ} (hy : 0 < y) {v : ℝ} (hv : 0 < v) :
    |1 / (v + 1) - 1 / (v + y)| ≤ |y - 1| / min 1 y / (v + 1) ^ 2 := by
  have hm : 0 < min 1 y := lt_min one_pos hy
  have h1 : 0 < v + 1 := by linarith
  have h2 : 0 < v + y := by linarith
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h3 : min 1 y * (v + 1) ≤ v + y := by
    rcases le_total y 1 with h | h
    · rw [min_eq_right h]
      nlinarith
    · rw [min_eq_left h]
      linarith
  have e : 1 / (v + 1) - 1 / (v + y) = (y - 1) / ((v + 1) * (v + y)) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (mul_pos h1 h2), div_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_left h3 h1.le])

/-- Helper for `gl18_he_K` and `gl18_he_B_lim` (§18.3): `∫₀^∞ (1/(v + 1) − 1/(v + y)) dv = log y`, with
integrability (antiderivative `log(v + 1) − log(v + y) → 0`). -/
theorem gl18_he_rat {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => 1 / (v + 1) - 1 / (v + y)) (Ioi 0) ∧
      ∫ v in Ioi 0, (1 / (v + 1) - 1 / (v + y)) = Real.log y := by
  have hm : 0 < min 1 y := lt_min one_pos hy
  have hint : IntegrableOn (fun v : ℝ => 1 / (v + 1) - 1 / (v + y)) (Ioi 0) := by
    refine gl18_he_intg (Measurable.aestronglyMeasurable (by fun_prop)) (C := |y - 1| / min 1 y) fun v hv => ?_
    refine (gl18_he_ratb hy hv).trans ?_
    rw [div_eq_mul_one_div (|y - 1| / min 1 y)]
    gcongr
    linarith [abs_nonneg (Real.log v)]
  refine ⟨hint, ?_⟩
  have hd : ∀ v ∈ Ioi (0 : ℝ), HasDerivAt (fun v => Real.log (v + 1) - Real.log (v + y))
      (1 / (v + 1) - 1 / (v + y)) v := fun v hv => by
    have hv' : (0 : ℝ) < v := hv
    have h1 := ((hasDerivAt_id' v).add_const 1).log (by linarith : v + 1 ≠ 0)
    have h2 := ((hasDerivAt_id' v).add_const y).log (by linarith : v + y ≠ 0)
    exact h1.sub h2
  have hc : ContinuousWithinAt (fun v => Real.log (v + 1) - Real.log (v + y)) (Ici 0) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => Real.log (v + 1)) 0 :=
      (Real.continuousAt_log (by norm_num)).comp (f := fun v : ℝ => v + 1) (by fun_prop)
    have h2 : ContinuousAt (fun v : ℝ => Real.log (v + y)) 0 :=
      (Real.continuousAt_log (by simp only [zero_add]; exact hy.ne')).comp (f := fun v : ℝ => v + y) (by fun_prop)
    exact (h1.sub h2).continuousWithinAt
  have hlim : Tendsto (fun v => Real.log (v + 1) - Real.log (v + y)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun v : ℝ => 1 + (1 - y) / (v + y)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := 1 - y)).div_atTop (tendsto_atTop_add_const_right _ y tendsto_id)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    have hv1 : v + y ≠ 0 := by linarith
    rw [Function.comp_apply, ← Real.log_div (by linarith) (by linarith)]
    congr 1
    field_simp
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint hlim]
  simp

/-- Helper for `para18_3_hilbert_E` (§18.3, C2a). `K(y) = ∫₀^∞ log u (1/(u + 1) − 1/(u + y)) du = (log y)²/2`: the
inversion `u ↦ y/u` sends the integrand to `(log y − log u)(1/(u + 1) − 1/(u + y))`, so
`2K = log y ∫₀^∞ (1/(u + 1) − 1/(u + y)) du = (log y)²`. -/
theorem gl18_he_K {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => Real.log u * (1 / (u + 1) - 1 / (u + y))) (Ioi 0) ∧
      ∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u + y)) = Real.log y ^ 2 / 2 := by
  obtain ⟨hr, hrv⟩ := gl18_he_rat hy
  have hint : IntegrableOn (fun u : ℝ => Real.log u * (1 / (u + 1) - 1 / (u + y))) (Ioi 0) := by
    refine gl18_he_intg (Measurable.aestronglyMeasurable (by fun_prop)) (C := |y - 1| / min 1 y) fun u hu => ?_
    have hb := gl18_he_ratb hy hu
    have hl0 := abs_nonneg (Real.log u)
    rw [abs_mul]
    calc |Real.log u| * |1 / (u + 1) - 1 / (u + y)| ≤ (|Real.log u| + 1) * (|y - 1| / min 1 y / (u + 1) ^ 2) :=
          mul_le_mul (by linarith) hb (abs_nonneg _) (by positivity)
      _ = |y - 1| / min 1 y * ((|Real.log u| + 1) / (u + 1) ^ 2) := by ring
  refine ⟨hint, ?_⟩
  -- the inversion `u = y/v`: `k(y/v) y/v² = (log y − log v)(1/(v + 1) − 1/(v + y))`
  have hinv : ∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u + y)) =
      ∫ v in Ioi 0, Real.log (y / v) * (1 / (y / v + 1) - 1 / (y / v + y)) * (y / v ^ 2) :=
    gl18_he_inv _ hy
  have hpt : ∀ v ∈ Ioi (0 : ℝ), Real.log (y / v) * (1 / (y / v + 1) - 1 / (y / v + y)) * (y / v ^ 2) =
      Real.log y * (1 / (v + 1) - 1 / (v + y)) - Real.log v * (1 / (v + 1) - 1 / (v + y)) := by
    intro v hv
    have hv' : 0 < v := hv
    rw [Real.log_div hy.ne' hv'.ne']
    have h1 : v + 1 ≠ 0 := by linarith
    have h2 : v + y ≠ 0 := by linarith
    have h3 : y / v + 1 ≠ 0 := by positivity
    have h4 : y / v + y ≠ 0 := by positivity
    have h5 : v ≠ 0 := hv'.ne'
    field_simp
    ring
  have h2 : ∫ v in Ioi 0, Real.log (y / v) * (1 / (y / v + 1) - 1 / (y / v + y)) * (y / v ^ 2) =
      Real.log y * Real.log y - ∫ v in Ioi 0, Real.log v * (1 / (v + 1) - 1 / (v + y)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hr.const_mul (Real.log y)) hint,
      integral_const_mul, hrv]
  have h3 := hinv.trans h2
  linarith

/-- Helper for `gl18_he_g` (§18.3): the regularized integrand is dominated by `C (|log u| + 1)/(u + 1)²`.
- Far out (`u ≥ 2y + 3`): `g = log u (y − 1)/((u − y)(u − 1)) − log y (y + 1)/((u − y)(u + 1))`.
- Elsewhere: the difference quotient is at most `2(|log u| + |log y| + 1)/y` (`gl18_he_logd`), `|log u/(u − 1)|` at
  most `8(|log u| + 1)` (`gl18_he_logq`), and `(u + 1)² < (2y + 4)²`. -/
theorem gl18_he_gbound {y : ℝ} (hy : 0 < y) : ∃ C : ℝ, ∀ u : ℝ, 0 < u →
    |(Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1)| ≤
      C * ((|Real.log u| + 1) / (u + 1) ^ 2) := by
  have hly := abs_nonneg (Real.log y)
  have hy1 := abs_nonneg (y - 1)
  refine ⟨(4 * |y - 1| + 2 * |Real.log y| * (y + 1)) + ((2 + 2 * |Real.log y|) / y + 8 + |Real.log y|) *
    (2 * y + 4) ^ 2, fun u hu => ?_⟩
  have hl0 := abs_nonneg (Real.log u)
  have hu1 : 0 < u + 1 := by linarith
  have hq : 0 ≤ (|Real.log u| + 1) / (u + 1) ^ 2 := by positivity
  have hC₁0 : 0 ≤ 4 * |y - 1| + 2 * |Real.log y| * (y + 1) := by positivity
  have hC₂0 : 0 ≤ ((2 + 2 * |Real.log y|) / y + 8 + |Real.log y|) * (2 * y + 4) ^ 2 := by positivity
  rcases le_or_gt (2 * y + 3) u with huR | huR
  · -- far region
    have hpa : 0 < u - y := by linarith
    have hpb : 0 < u - 1 := by linarith
    have e : (Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1) =
        Real.log u * (y - 1) / ((u - y) * (u - 1)) - Real.log y * (y + 1) / ((u - y) * (u + 1)) := by
      have := hpa.ne'
      have := hpb.ne'
      have := hu1.ne'
      field_simp
      ring
    rw [e]
    have hA : |Real.log u * (y - 1) / ((u - y) * (u - 1))| ≤ 4 * |y - 1| * |Real.log u| / (u + 1) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hpa hpb), div_le_div_iff₀ (mul_pos hpa hpb) (by positivity)]
      have h4 : (u + 1) ^ 2 ≤ 4 * ((u - y) * (u - 1)) := by nlinarith
      nlinarith [mul_nonneg hl0 hy1]
    have hB : |Real.log y * (y + 1) / ((u - y) * (u + 1))| ≤ 2 * |Real.log y| * (y + 1) / (u + 1) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hpa hu1), abs_of_pos (by linarith : (0 : ℝ) < y + 1),
        div_le_div_iff₀ (mul_pos hpa hu1) (by positivity)]
      have h4 : (u + 1) ^ 2 ≤ 2 * ((u - y) * (u + 1)) := by nlinarith
      nlinarith [mul_nonneg hly (by linarith : (0 : ℝ) ≤ y + 1)]
    have hsum : 4 * |y - 1| * |Real.log u| / (u + 1) ^ 2 + 2 * |Real.log y| * (y + 1) / (u + 1) ^ 2 ≤
        (4 * |y - 1| + 2 * |Real.log y| * (y + 1)) * ((|Real.log u| + 1) / (u + 1) ^ 2) := by
      rw [← add_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hl0 hy1, mul_nonneg hly hy.le]) (by positivity)
    calc _ ≤ |Real.log u * (y - 1) / ((u - y) * (u - 1))| + |Real.log y * (y + 1) / ((u - y) * (u + 1))| :=
          abs_sub _ _
      _ ≤ _ := (add_le_add hA hB).trans hsum
      _ ≤ _ := by nlinarith [mul_nonneg hC₂0 hq]
  · -- near region
    have hD : |(Real.log u - Real.log y) / (u - y)| ≤ 2 * (|Real.log u| + |Real.log y| + 1) / y := by
      rcases lt_or_ge u (y / 2) with h | h
      · have hd : y / 2 ≤ |u - y| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        rw [abs_div, div_le_div_iff₀ (by linarith) hy]
        have := abs_sub (Real.log u) (Real.log y)
        nlinarith
      · rcases eq_or_ne u y with rfl | hne
        · simp only [sub_self, div_zero, abs_zero]
          positivity
        · have hpos : 0 < |u - y| := abs_pos.2 (sub_ne_zero.2 hne)
          rw [abs_div, div_le_iff₀ hpos]
          have h2 := gl18_he_logd hy h
          have h3 : 2 * |u - y| / y ≤ 2 * (|Real.log u| + |Real.log y| + 1) / y * |u - y| := by
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hy]
            nlinarith [mul_nonneg (add_nonneg hl0 hly) hpos.le]
          linarith
    have hL : |Real.log u / (u - 1)| ≤ 8 * (|Real.log u| + 1) := by
      exact (gl18_he_logq hu).trans (div_le_self (by positivity) (by linarith))
    have hE : |Real.log y / (u + 1)| ≤ |Real.log y| * (|Real.log u| + 1) := by
      rw [abs_div, abs_of_pos hu1, div_le_iff₀ hu1]
      nlinarith [mul_nonneg hly (mul_nonneg hl0 hu.le), mul_nonneg hly hl0, mul_nonneg hly hu.le]
    have hsum : |(Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1)| ≤
        ((2 + 2 * |Real.log y|) / y + 8 + |Real.log y|) * (|Real.log u| + 1) := by
      have h1 := abs_add_le ((Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1)) (Real.log y / (u + 1))
      have h2 := abs_sub ((Real.log u - Real.log y) / (u - y)) (Real.log u / (u - 1))
      have h3 : 2 * (|Real.log u| + |Real.log y| + 1) / y ≤ (2 + 2 * |Real.log y|) / y * (|Real.log u| + 1) := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hy]
        nlinarith
      nlinarith
    have hR : (|Real.log u| + 1) ≤ (2 * y + 4) ^ 2 * ((|Real.log u| + 1) / (u + 1) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have : (u + 1) ^ 2 ≤ (2 * y + 4) ^ 2 := by nlinarith
      nlinarith
    have h0 : 0 ≤ (2 + 2 * |Real.log y|) / y + 8 + |Real.log y| := by positivity
    calc _ ≤ ((2 + 2 * |Real.log y|) / y + 8 + |Real.log y|) * (|Real.log u| + 1) := hsum
      _ ≤ ((2 + 2 * |Real.log y|) / y + 8 + |Real.log y|) * ((2 * y + 4) ^ 2 * ((|Real.log u| + 1) / (u + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hR h0
      _ ≤ _ := by nlinarith [mul_nonneg hC₁0 hq]

/-- Helper for `para18_3_hilbert_E` (§18.3, C2b). The regularized integrand
`g(u) = (log u − log y)/(u − y) − log u/(u − 1) + log y/(u + 1)` (removable at `u = y` and `u = 1`, `O(log u/u²)` at
`∞`) is integrable on `(0, ∞)` with integral `(log y)²/2`: the inversion `u ↦ y/u` sends `g` to
`−g + log y (1/(u + 1) − 1/(u + y))`. This replaces the principal value at `y` by an ordinary integral (no asymmetric
excision is needed). -/
theorem gl18_he_g {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => (Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1))
        (Ioi 0) ∧
      ∫ u in Ioi 0, ((Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1)) =
        Real.log y ^ 2 / 2 := by
  obtain ⟨C, hC⟩ := gl18_he_gbound hy
  obtain ⟨hr, hrv⟩ := gl18_he_rat hy
  have hint : IntegrableOn (fun u : ℝ => (Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) +
      Real.log y / (u + 1)) (Ioi 0) :=
    gl18_he_intg (Measurable.aestronglyMeasurable (by fun_prop)) hC
  refine ⟨hint, ?_⟩
  -- the inversion `u = y/v`: `g(y/v) y/v² = −g(v) + log y (1/(v + 1) − 1/(v + y))` for `v ∉ {1, y}`
  have hinv : ∫ u in Ioi 0, ((Real.log u - Real.log y) / (u - y) - Real.log u / (u - 1) + Real.log y / (u + 1)) =
      ∫ v in Ioi 0, ((Real.log (y / v) - Real.log y) / (y / v - y) - Real.log (y / v) / (y / v - 1) +
        Real.log y / (y / v + 1)) * (y / v ^ 2) :=
    gl18_he_inv _ hy
  have hpt : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Ioi (0 : ℝ) →
      ((Real.log (y / v) - Real.log y) / (y / v - y) - Real.log (y / v) / (y / v - 1) + Real.log y / (y / v + 1)) *
        (y / v ^ 2) =
      Real.log y * (1 / (v + 1) - 1 / (v + y)) -
        ((Real.log v - Real.log y) / (v - y) - Real.log v / (v - 1) + Real.log y / (v + 1)) := by
    have h1 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := measure_eq_zero_iff_ae_notMem.1 (measure_singleton 1)
    have h2 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ y := measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)
    filter_upwards [h1, h2] with v hv1 hvy hv
    have hv' : 0 < v := hv
    rw [Real.log_div hy.ne' hv'.ne']
    have a1 : v + 1 ≠ 0 := by linarith
    have a2 : v + y ≠ 0 := by linarith
    have a3 : v - y ≠ 0 := sub_ne_zero.2 hvy
    have a4 : v - 1 ≠ 0 := sub_ne_zero.2 hv1
    have a5 : v ≠ 0 := hv'.ne'
    have a6 : y / v - y ≠ 0 := by
      rw [show y / v - y = y * (1 - v) / v by field_simp]
      exact div_ne_zero (mul_ne_zero hy.ne' (sub_ne_zero.2 (Ne.symm hv1))) a5
    have a7 : y / v - 1 ≠ 0 := by
      rw [show y / v - 1 = (y - v) / v by field_simp]
      exact div_ne_zero (sub_ne_zero.2 (Ne.symm hvy)) a5
    have a8 : y / v + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h2 : ∫ v in Ioi 0, ((Real.log (y / v) - Real.log y) / (y / v - y) - Real.log (y / v) / (y / v - 1) +
        Real.log y / (y / v + 1)) * (y / v ^ 2) =
      Real.log y * Real.log y -
        ∫ v in Ioi 0, ((Real.log v - Real.log y) / (v - y) - Real.log v / (v - 1) + Real.log y / (v + 1)) := by
    rw [setIntegral_congr_ae measurableSet_Ioi hpt, integral_sub (hr.const_mul (Real.log y)) hint,
      integral_const_mul, hrv]
  have h3 := hinv.trans h2
  linarith

/-- Helper for `gl18_he_A0` (§18.3): `∫₀¹ (−log v) vⁿ dv = 1/(n + 1)²`, with integrability (antiderivative
`v^{n+1}/(n + 1)² − v^{n+1} log v/(n + 1)`, continuous at `0`). -/
theorem gl18_he_logpow (n : ℕ) :
    IntegrableOn (fun v : ℝ => -Real.log v * v ^ n) (Ioc 0 1) ∧
      ∫ v in Ioc 0 1, -Real.log v * v ^ n = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hii : IntervalIntegrable (fun v : ℝ => -Real.log v * v ^ n) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.neg.mul_continuousOn (continuousOn_pow n)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hii, ?_⟩
  have hc : Continuous fun v : ℝ => v ^ (n + 1) * Real.log v := by
    have : (fun v : ℝ => v ^ (n + 1) * Real.log v) = fun v => v ^ n * (v * Real.log v) := by
      funext v
      ring
    rw [this]
    exact (continuous_pow n).mul Real.continuous_mul_log
  have hd : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun v : ℝ => v ^ (n + 1) / ((n : ℝ) + 1) ^ 2 - v ^ (n + 1) * Real.log v / ((n : ℝ) + 1))
      (-Real.log v * v ^ n) v := by
    intro v hv
    have hv0 : v ≠ 0 := hv.1.ne'
    have h1 := (hasDerivAt_pow (n + 1) v).div_const (((n : ℝ) + 1) ^ 2)
    have h2 := ((hasDerivAt_pow (n + 1) v).mul (Real.hasDerivAt_log hv0)).div_const ((n : ℝ) + 1)
    refine (h1.sub h2).congr_deriv ?_
    push_cast
    field_simp
    ring
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (((continuous_pow (n + 1)).div_const _).sub (hc.div_const _)).continuousOn hd hii]
  simp

/-- Helper for `gl18_he_A0` (§18.3): `Σ_{k ≥ 0} 1/(2k + 1)² = π²/8`, the odd part of `ζ(2) = π²/6`
(`hasSum_zeta_two`; the even part is `ζ(2)/4`). -/
theorem gl18_he_odd : HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have hz : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
    have h := hz.mul_left (1 / 4)
    rw [show 1 / 4 * (π ^ 2 / 6) = π ^ 2 / 24 by ring] at h
    have e : (fun k : ℕ => f (2 * k)) = fun i => 1 / 4 * f i := funext fun k => by
      simp only [hf]
      push_cast
      ring
    rw [e]
    exact h
  have ho : Summable fun k : ℕ => f (2 * k + 1) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun a b h => by
      simp only at h
      omega
  have hval : π ^ 2 / 24 + ∑' k : ℕ, f (2 * k + 1) = π ^ 2 / 6 :=
    (HasSum.even_add_odd (f := f) he ho.hasSum).unique hz
  have : ∑' k : ℕ, f (2 * k + 1) = π ^ 2 / 8 := by linarith
  rw [← this]
  exact ho.hasSum

/-- Helper for `gl18_he_A0` (§18.3): `∫₀¹ (−log v)/(1 − v²) dv = π²/8`, by `−log v/(1 − v²) = Σ (−log v) v^{2k}`
(nonnegative terms, `integral_tsum_of_summable_integral_norm`), `gl18_he_logpow` and `gl18_he_odd`. -/
theorem gl18_he_half : ∫ v in Ioc 0 1, -Real.log v / (1 - v ^ 2) = π ^ 2 / 8 := by
  have hF : ∀ k : ℕ, Integrable (fun v : ℝ => -Real.log v * v ^ (2 * k)) (volume.restrict (Ioc 0 1)) :=
    fun k => (gl18_he_logpow (2 * k)).1
  have hnn : ∀ k : ℕ, ∀ v ∈ Ioc (0 : ℝ) 1, 0 ≤ -Real.log v * v ^ (2 * k) := fun k v hv =>
    mul_nonneg (neg_nonneg.2 (Real.log_nonpos hv.1.le hv.2)) (pow_nonneg hv.1.le _)
  have hI : ∀ k : ℕ, ∫ v in Ioc 0 1, ‖-Real.log v * v ^ (2 * k)‖ = 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
    intro k
    rw [setIntegral_congr_fun measurableSet_Ioc fun v hv => Real.norm_of_nonneg (hnn k v hv),
      (gl18_he_logpow (2 * k)).2]
    push_cast
    ring
  have hsum := integral_tsum_of_summable_integral_norm hF (by simp_rw [hI]; exact gl18_he_odd.summable)
  have hvals : ∀ k : ℕ, ∫ v in Ioc 0 1, -Real.log v * v ^ (2 * k) = 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
    intro k
    rw [(gl18_he_logpow (2 * k)).2]
    push_cast
    ring
  simp_rw [hvals] at hsum
  rw [gl18_he_odd.tsum_eq] at hsum
  rw [hsum]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  -- `Σ (−log v) v^{2k} = (−log v)/(1 − v²)` on `(0, 1]`
  rcases eq_or_lt_of_le hv.2 with h1 | h1
  · subst h1
    simp
  · have hv2 : v ^ 2 < 1 := by nlinarith [hv.1]
    have hg := tsum_geometric_of_lt_one (sq_nonneg v) hv2
    show -Real.log v / (1 - v ^ 2) = ∑' k : ℕ, -Real.log v * v ^ (2 * k)
    simp_rw [pow_mul]
    rw [tsum_mul_left, hg, div_eq_mul_inv]

/-- Helper for `para18_3_hilbert_E` (§18.3, C2c). The constant: `∫₀^∞ log u (1/(u + 1) − 1/(u − 1)) du
= −2 ∫₀^∞ log u/(u² − 1) du = −π²/2` (fold by `u ↦ 1/u` onto `(0, 1)`, expand `−log v/(1 − v²) = Σ (−log v) v^{2k}`,
`∫₀¹ (−log v) vⁿ dv = 1/(n + 1)²`, and `Σ 1/(2k + 1)² = π²/8` from `hasSum_zeta_two`). -/
theorem gl18_he_A0 :
    IntegrableOn (fun u : ℝ => Real.log u * (1 / (u + 1) - 1 / (u - 1))) (Ioi 0) ∧
      ∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u - 1)) = -(π ^ 2 / 2) := by
  -- `a₀(u) = 2 log u/(1 − u²)`; bound `|a₀| ≤ 16 (|log u| + 1)/(u + 1)²` (`gl18_he_logq`)
  have hint : IntegrableOn (fun u : ℝ => Real.log u * (1 / (u + 1) - 1 / (u - 1))) (Ioi 0) := by
    refine gl18_he_intg (Measurable.aestronglyMeasurable (by fun_prop)) (C := 16) fun u hu => ?_
    have hu1 : 0 < u + 1 := by linarith
    have hq := gl18_he_logq hu
    rcases eq_or_ne u 1 with rfl | hne
    · simp only [Real.log_one, zero_mul, abs_zero]
      positivity
    have hne' : u - 1 ≠ 0 := sub_ne_zero.2 hne
    have e : Real.log u * (1 / (u + 1) - 1 / (u - 1)) = -2 * (Real.log u / (u - 1)) / (u + 1) := by
      field_simp
      ring
    rw [e, abs_div, abs_mul, abs_of_pos hu1, div_le_iff₀ hu1]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have h3 : 8 * (|Real.log u| + 1) / (u + 1) * (u + 1) = 8 * (|Real.log u| + 1) := by field_simp
    have h4 : 16 * ((|Real.log u| + 1) / (u + 1) ^ 2) * (u + 1) = 2 * (8 * (|Real.log u| + 1) / (u + 1)) := by
      field_simp
      ring
    rw [h4]
    linarith
  refine ⟨hint, ?_⟩
  -- the inversion `u = 1/v` swaps `(1, ∞)` and `(0, 1)` and fixes `a₀(u) du`
  have hsplit : ∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u - 1)) =
      (∫ u in Ioc 0 1, Real.log u * (1 / (u + 1) - 1 / (u - 1))) +
        ∫ u in Ioi 1, Real.log u * (1 / (u + 1) - 1 / (u - 1)) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union (Set.disjoint_left.2 fun u h1 h2 => by
      rw [mem_Ioc] at h1
      rw [mem_Ioi] at h2
      linarith) measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  have hsym : ∫ u in Ioi 1, Real.log u * (1 / (u + 1) - 1 / (u - 1)) =
      ∫ u in Ioc 0 1, Real.log u * (1 / (u + 1) - 1 / (u - 1)) := by
    have h := gl18_he_inv ((Ioi 1).indicator fun u : ℝ => Real.log u * (1 / (u + 1) - 1 / (u - 1))) one_pos
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi zero_le_one)] at h
    rw [h, integral_Ioc_eq_integral_Ioo, ← Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 < v := hv
    rcases lt_or_ge v 1 with h1 | h1
    · have hmem : 1 / v ∈ Ioi (1 : ℝ) := by
        rw [mem_Ioi, lt_div_iff₀ hv0]
        linarith
      rw [indicator_of_mem hmem, indicator_of_mem (show v ∈ Iio (1 : ℝ) from h1)]
      show Real.log (1 / v) * (1 / (1 / v + 1) - 1 / (1 / v - 1)) * (1 / v ^ 2) =
        Real.log v * (1 / (v + 1) - 1 / (v - 1))
      have e : Real.log (1 / v) = -Real.log v := by rw [one_div, Real.log_inv]
      rw [e]
      have a1 : v - 1 ≠ 0 := by linarith
      have a2 : v + 1 ≠ 0 := by linarith
      have a3 : 1 / v + 1 ≠ 0 := by positivity
      have a4 : 1 / v - 1 ≠ 0 := by
        rw [sub_ne_zero]
        exact (mem_Ioi.1 hmem).ne'
      have a5 : v ≠ 0 := hv0.ne'
      field_simp
      ring
    · have hnmem : 1 / v ∉ Ioi (1 : ℝ) := by
        rw [mem_Ioi, not_lt, div_le_one hv0]
        exact h1
      rw [indicator_of_notMem hnmem, indicator_of_notMem (show v ∉ Iio (1 : ℝ) from not_lt.2 h1), zero_mul]
  have hhalf : ∫ u in Ioc 0 1, Real.log u * (1 / (u + 1) - 1 / (u - 1)) = -2 * (π ^ 2 / 8) := by
    rw [← gl18_he_half, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rcases eq_or_lt_of_le hv.2 with h1 | h1
    · subst h1
      simp
    · have hv1 : v - 1 ≠ 0 := by linarith
      have hv2 : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1]
      have hv3 : v + 1 ≠ 0 := by linarith [hv.1]
      field_simp
      ring
  rw [hsplit, hsym, hhalf]
  ring

/-- Helper for `para18_3_hilbert_E` (§18.3, C2d). For `x > 0` the principal value
`J(x) = PV∫ log|ξ| (1/(ξ − x) − 1/(ξ − 1)) dξ` is `0`: the negative half-line gives `K(x)`, the positive one
`G(x) − (log x)²` (`g` plus `log x` times the compensator), and `K + G − (log x)² = 0`. -/
theorem gl18_he_J_pos {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1))) (𝓝[>] 0)
      (𝓝 0) := by
  obtain ⟨hKi, hKv⟩ := gl18_he_K hx
  obtain ⟨hgi, hgv⟩ := gl18_he_g hx
  obtain ⟨hci, hcl⟩ := gl18_he_comp hx
  -- on `(0, ∞)`: `g` plus `log x` times the compensator; on `(−∞, 0)`, with `ξ = −u`: the integrand of `K(x)`
  have hF : ∀ u : ℝ, Real.log |u| * (1 / (u - x) - 1 / (u - 1)) =
      ((Real.log u - Real.log x) / (u - x) - Real.log u / (u - 1) + Real.log x / (u + 1)) +
        Real.log x * (1 / (u - x) - 1 / (u + 1)) := fun u => by
    rw [Real.log_abs]
    ring
  have hFn : ∀ u : ℝ, Real.log |-u| * (1 / (-u - x) - 1 / (-u - 1)) =
      Real.log u * (1 / (u + 1) - 1 / (u + x)) := fun u => by
    rw [abs_neg, Real.log_abs, show -u - x = -(u + x) by ring, show -u - 1 = -(u + 1) by ring, div_neg, div_neg]
    ring
  have hlim := ((gl18_he_trunc hgi x).add (hcl.const_mul (Real.log x))).const_add
    (∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u + x)))
  rw [hKv, hgv, show Real.log x ^ 2 / 2 + (Real.log x ^ 2 / 2 + Real.log x * -Real.log x) = 0 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
  have hneg : {u : ℝ | 0 < u ∧ ε < |u + x|} = Ioi 0 := Set.ext fun u => by
    simp only [mem_ofPred_eq, mem_Ioi]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [abs_of_pos (by linarith)]
    linarith [hε.2]
  have hTi : IntegrableOn (fun u : ℝ => Real.log |u| * (1 / (u - x) - 1 / (u - 1)))
      {u : ℝ | 0 < u ∧ ε < |u - x|} := by
    simp_rw [hF]
    exact (hgi.mono_set fun u hu => hu.1).add ((hci ε hε.1).const_mul _)
  have hNi : IntegrableOn (fun u : ℝ => Real.log |-u| * (1 / (-u - x) - 1 / (-u - 1)))
      {u : ℝ | 0 < u ∧ ε < |u + x|} := by
    simp_rw [hFn, hneg]
    exact hKi
  rw [gl18_he_split (gl18_he_halves hTi hNi), hneg]
  simp_rw [hFn, hF]
  rw [integral_add (hgi.mono_set fun u hu => hu.1) ((hci ε hε.1).const_mul _), integral_const_mul, hKv]
  ring

/-- Helper for `para18_3_hilbert_E` (§18.3, C2d). For `x = −y < 0` the principal value `J(x)` is `−π²`: the positive
half-line gives `A₀ − K(y)`, the negative one `A₀ − G(y) + (log y)²`, and the total is `2A₀ = −π²`. -/
theorem gl18_he_J_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1))) (𝓝[>] 0)
      (𝓝 (-(π ^ 2))) := by
  have hy : 0 < -x := by linarith
  obtain ⟨hKi, hKv⟩ := gl18_he_K hy
  obtain ⟨hgi, hgv⟩ := gl18_he_g hy
  obtain ⟨hci, hcl⟩ := gl18_he_comp hy
  obtain ⟨hAi, hAv⟩ := gl18_he_A0
  -- on `(0, ∞)`: `a₀ − k(−x)`; on `(−∞, 0)`, with `ξ = −u`: `a₀ − g(−x) − log(−x)` times the compensator
  have hF : ∀ u : ℝ, Real.log |u| * (1 / (u - x) - 1 / (u - 1)) =
      Real.log u * (1 / (u + 1) - 1 / (u - 1)) - Real.log u * (1 / (u + 1) - 1 / (u + -x)) := fun u => by
    rw [Real.log_abs]
    ring
  have hFn : ∀ u : ℝ, Real.log |-u| * (1 / (-u - x) - 1 / (-u - 1)) =
      Real.log u * (1 / (u + 1) - 1 / (u - 1)) -
        (((Real.log u - Real.log (-x)) / (u - -x) - Real.log u / (u - 1) + Real.log (-x) / (u + 1)) +
          Real.log (-x) * (1 / (u - -x) - 1 / (u + 1))) := fun u => by
    rw [abs_neg, Real.log_abs, show -u - x = -(u - -x) by ring, show -u - 1 = -(u + 1) by ring, div_neg, div_neg]
    ring
  have hlim := ((gl18_he_trunc hAi (-x)).sub ((gl18_he_trunc hgi (-x)).add (hcl.const_mul (Real.log (-x))))).const_add
    ((∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u - 1))) -
      ∫ u in Ioi 0, Real.log u * (1 / (u + 1) - 1 / (u + -x)))
  rw [hAv, hKv, hgv, show -(π ^ 2 / 2) - Real.log (-x) ^ 2 / 2 + (-(π ^ 2 / 2) -
    (Real.log (-x) ^ 2 / 2 + Real.log (-x) * -Real.log (-x))) = -(π ^ 2) by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hy] with ε hε
  have hpos : {u : ℝ | 0 < u ∧ ε < |u - x|} = Ioi 0 := Set.ext fun u => by
    simp only [mem_ofPred_eq, mem_Ioi]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [abs_of_pos (by linarith)]
    linarith [hε.2]
  have hT : {u : ℝ | 0 < u ∧ ε < |u + x|} = {u : ℝ | 0 < u ∧ ε < |u - -x|} := by
    simp only [sub_neg_eq_add]
  have hTi : IntegrableOn (fun u : ℝ => Real.log |u| * (1 / (u - x) - 1 / (u - 1)))
      {u : ℝ | 0 < u ∧ ε < |u - x|} := by
    simp_rw [hF, hpos]
    exact hAi.sub hKi
  have hNi : IntegrableOn (fun u : ℝ => Real.log |-u| * (1 / (-u - x) - 1 / (-u - 1)))
      {u : ℝ | 0 < u ∧ ε < |u + x|} := by
    simp_rw [hFn, hT]
    exact (hAi.mono_set fun u hu => hu.1).sub ((hgi.mono_set fun u hu => hu.1).add ((hci ε hε.1).const_mul _))
  rw [gl18_he_split (gl18_he_halves hTi hNi), hpos, hT]
  simp_rw [hFn, hF]
  have hgT : IntegrableOn (fun u : ℝ => (Real.log u - Real.log (-x)) / (u - -x) - Real.log u / (u - 1) +
      Real.log (-x) / (u + 1)) {u : ℝ | 0 < u ∧ ε < |u - -x|} := hgi.mono_set fun u hu => hu.1
  have hcT : IntegrableOn (fun u : ℝ => Real.log (-x) * (1 / (u - -x) - 1 / (u + 1)))
      {u : ℝ | 0 < u ∧ ε < |u - -x|} := (hci ε hε.1).const_mul _
  have hsT : IntegrableOn (fun u : ℝ => ((Real.log u - Real.log (-x)) / (u - -x) - Real.log u / (u - 1) +
      Real.log (-x) / (u + 1)) + Real.log (-x) * (1 / (u - -x) - 1 / (u + 1))) {u : ℝ | 0 < u ∧ ε < |u - -x|} :=
    hgT.add hcT
  rw [integral_sub hAi hKi, integral_sub (hAi.mono_set fun u hu => hu.1) hsT, integral_add hgT hcT,
    integral_const_mul, hAv, hKv]

/-- Helper for `para18_3_hilbert_E` (§18.3, C1). The truncated integrals of (B) tend to `−x log|x|`: with `ξ = −u`,
they are `−x ∫₀^∞ (1/(u + 1) − 1/(u + x)) du = −x log x` for `x > 0`, `−x` times the compensator's principal value
(`gl18_he_comp`) for `x < 0`, and `0` for `x = 0`. -/
theorem gl18_he_B_lim (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|},
        (if ξ < 0 then -x * (1 / (ξ - x) - 1 / (ξ - 1)) else 0)) (𝓝[>] 0) (𝓝 (-x * Real.log |x|)) := by
  -- the integrand vanishes on `[0, ∞)`; with `ξ = −u` it is `−x (1/(u + 1) − 1/(u + x))` on `u > 0`
  have hz : ∀ u : ℝ, 0 < u → (if u < 0 then -x * (1 / (u - x) - 1 / (u - 1)) else 0) = 0 := fun u hu => by
    simp only [show ¬ u < 0 from not_lt.2 hu.le, ↓reduceIte]
  have hn : ∀ u : ℝ, 0 < u → (if -u < 0 then -x * (1 / (-u - x) - 1 / (-u - 1)) else 0) =
      -x * (1 / (u + 1) - 1 / (u + x)) := fun u hu => by
    simp only [show -u < 0 by linarith, ↓reduceIte]
    rw [show -u - x = -(u + x) by ring, show -u - 1 = -(u + 1) by ring, div_neg, div_neg]
    ring
  have hm : ∀ ε : ℝ, MeasurableSet {u : ℝ | 0 < u ∧ ε < |u - x|} := fun ε =>
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_const (by fun_prop : Measurable fun u : ℝ => |u - x|))
  have hzero : ∀ ε : ℝ, ∫ u in {u : ℝ | 0 < u ∧ ε < |u - x|},
      (if u < 0 then -x * (1 / (u - x) - 1 / (u - 1)) else 0) = 0 := fun ε => by
    rw [setIntegral_congr_fun (hm ε) fun u hu => hz u hu.1]
    exact integral_zero _ _
  have hzi : ∀ ε : ℝ, IntegrableOn (fun u : ℝ => if u < 0 then -x * (1 / (u - x) - 1 / (u - 1)) else 0)
      {u : ℝ | 0 < u ∧ ε < |u - x|} := fun ε =>
    integrableOn_zero.congr_fun (fun u hu => (hz u hu.1).symm) (hm ε)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- `x < 0`: `x` times the compensator at `−x`
    have hy : 0 < -x := by linarith
    obtain ⟨hci, hcl⟩ := gl18_he_comp hy
    rw [abs_of_neg hx]
    have hlim := hcl.const_mul x
    rw [show x * -Real.log (-x) = -x * Real.log (-x) by ring] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hT : {u : ℝ | 0 < u ∧ ε < |u + x|} = {u : ℝ | 0 < u ∧ ε < |u - -x|} := by
      simp only [sub_neg_eq_add]
    have hmT : MeasurableSet {u : ℝ | 0 < u ∧ ε < |u - -x|} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_const (by fun_prop : Measurable fun u : ℝ => |u - -x|))
    have hn' : ∀ u : ℝ, 0 < u → (if -u < 0 then -x * (1 / (-u - x) - 1 / (-u - 1)) else 0) =
        x * (1 / (u - -x) - 1 / (u + 1)) := fun u hu => by
      rw [hn u hu]
      ring
    have hni : IntegrableOn (fun u : ℝ => if -u < 0 then -x * (1 / (-u - x) - 1 / (-u - 1)) else 0)
        {u : ℝ | 0 < u ∧ ε < |u + x|} := by
      rw [hT]
      exact IntegrableOn.congr_fun ((hci ε hε).const_mul x) (fun u hu => (hn' u hu.1).symm) hmT
    rw [gl18_he_split (gl18_he_halves (hzi ε) hni), hzero, zero_add, hT,
      setIntegral_congr_fun hmT fun u hu => hn' u hu.1, integral_const_mul]
  · simp only [neg_zero, zero_mul, ite_self, integral_zero, abs_zero, Real.log_zero]
    exact tendsto_const_nhds
  · -- `x > 0`: eventually the constant `−x log x`
    obtain ⟨hri, hrv⟩ := gl18_he_rat hx
    rw [abs_of_pos hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    have hneg : {u : ℝ | 0 < u ∧ ε < |u + x|} = Ioi 0 := Set.ext fun u => by
      simp only [mem_ofPred_eq, mem_Ioi]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rw [abs_of_pos (by linarith)]
      linarith [hε.2]
    have hni : IntegrableOn (fun u : ℝ => if -u < 0 then -x * (1 / (-u - x) - 1 / (-u - 1)) else 0)
        {u : ℝ | 0 < u ∧ ε < |u + x|} := by
      rw [hneg]
      exact IntegrableOn.congr_fun (hri.const_mul (-x)) (fun u hu => (hn u hu).symm) measurableSet_Ioi
    rw [gl18_he_split (gl18_he_halves (hzi ε) hni), hzero, zero_add, hneg,
      setIntegral_congr_fun measurableSet_Ioi fun u hu => hn u hu, integral_const_mul, hrv]

/-- **Unlabelled** (§18.3, l. 13410–13426). Modulo quadratic polynomials and for the normalized representatives,
`H(x log|x|) = πE(x)` and `H(E) = −(1/π) x log|x|` [CORRECTION: the printed `−πE`, `B/π` are the standard-sign
values]. -/
theorem para18_3_hilbert_E :
    (∃ a b c : ℂ, ∀ x : ℝ, hilbertPV (zNormalize fun z : ℂ => ((z.re * Real.log |z.re| : ℝ) : ℂ)) x =
      (π : ℂ) * ((max x 0 : ℝ) : ℂ) + a * x ^ 2 + b * x + c) ∧
    ∃ a b c : ℂ, ∀ x : ℝ, hilbertPV (zNormalize fun z : ℂ => ((max z.re 0 : ℝ) : ℂ)) x =
      -((x * Real.log |x| / π : ℝ) : ℂ) + a * x ^ 2 + b * x + c := by
  obtain ⟨hzA, hzB⟩ := gl18_he_zinf
  -- the normalized representatives: `zNormalize (x log|x|) = x log|x|`, `zNormalize max(x, 0) = max(x, 0) − x`
  have hNA : zNormalize (fun z : ℂ => ((z.re * Real.log |z.re| : ℝ) : ℂ)) =
      fun z : ℂ => ((z.re * Real.log |z.re| : ℝ) : ℂ) := by
    funext z
    have hc : zInfCoeff (fun z : ℂ => ((z.re * Real.log |z.re| : ℝ) : ℂ)) = 0 := hzA.limUnder_eq
    show _ - _ - (_ - _) * z - zInfCoeff _ * (z ^ 2 - z) = _
    rw [hc]
    simp
  have hNB : zNormalize (fun z : ℂ => ((max z.re 0 : ℝ) : ℂ)) = fun z : ℂ => ((max z.re 0 : ℝ) : ℂ) - z := by
    funext z
    have hc : zInfCoeff (fun z : ℂ => ((max z.re 0 : ℝ) : ℂ)) = 0 := hzB.limUnder_eq
    show _ - _ - (_ - _) * z - zInfCoeff _ * (z ^ 2 - z) = _
    rw [hc]
    norm_num
  refine ⟨⟨0, -π, 0, fun x => ?_⟩, ⟨0, 0, 0, fun x => ?_⟩⟩
  · -- (A): `H(x log|x|)(x) = (x/π) J(x)`, `J = 0` for `x > 0`, `J = −π²` for `x < 0`
    rw [hNA]
    have hV : ∀ ξ : ℝ, ξ ≠ x → (fun z : ℂ => ((z.re * Real.log |z.re| : ℝ) : ℂ)) ξ * kernelR x ξ =
        ((x * (Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1))) : ℝ) : ℂ) := fun ξ hξ => gl18_he_kernel_A x ξ hξ
    have hlim : ∀ L : ℝ, Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|},
        Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1))) (𝓝[>] 0) (𝓝 L) →
        Tendsto (fun ε : ℝ => ∫ ξ in {ξ : ℝ | ε < |ξ - x|},
          x * (Real.log |ξ| * (1 / (ξ - x) - 1 / (ξ - 1)))) (𝓝[>] 0) (𝓝 (x * L)) := fun L h =>
      (h.const_mul x).congr fun ε => (integral_const_mul _ _).symm
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [gl18_he_pv_eval hV (hlim _ (gl18_he_J_neg hx)), max_eq_right hx.le]
      have e : x * -(π ^ 2) / π = -π * x := by
        field_simp
      rw [e]
      push_cast
      ring
    · rw [gl18_he_pv_eval (L := 0) hV (by simp only [zero_mul, integral_zero]; exact tendsto_const_nhds)]
      simp
    · rw [gl18_he_pv_eval hV (hlim _ (gl18_he_J_pos hx)), max_eq_left hx.le]
      push_cast
      ring
  · -- (B): `H(max(x, 0) − x)(x) = −x log|x|/π`
    rw [hNB]
    have hV : ∀ ξ : ℝ, ξ ≠ x → (fun z : ℂ => ((max z.re 0 : ℝ) : ℂ) - z) ξ * kernelR x ξ =
        ((if ξ < 0 then -x * (1 / (ξ - x) - 1 / (ξ - 1)) else 0 : ℝ) : ℂ) := fun ξ hξ => gl18_he_kernel_B x ξ hξ
    rw [gl18_he_pv_eval hV (gl18_he_B_lim x)]
    push_cast
    ring

/-- **Formula (18.5)** (§18.3, l. 13430). `E_ab(x) = (x − a)(x − b)/(a − b)` for `a ≤ x ≤ b`, `0` otherwise. -/
def earthquakeVF (a b x : ℝ) : ℝ := if a ≤ x ∧ x ≤ b then (x - a) * (x - b) / (a - b) else 0

/-- **Formula (18.6)** (§18.3, l. 13437). `B_ab(x) = ((x − a)(x − b)/(a − b)) log|(x − a)/(x − b)|`. -/
def bendVF (a b x : ℝ) : ℝ := (x - a) * (x - b) / (a - b) * Real.log |(x - a) / (x - b)|

/-- **Definition** (§18.3, l. 13444). `L_ab(φ) = π ∫_a^b φ(z) (z − a)(z − b)/(a − b) dz`, along the semicircle
`z(θ) = (a + b)/2 + ((b − a)/2) e^{i(π − θ)}`, `0 ≤ θ ≤ π`. -/
def lFunctionalAB (a b : ℝ) (φ : ℂ → ℂ) : ℂ :=
  π * ∫ θ in (0 : ℝ)..π, φ ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ))) *
    (((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - a) *
      ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - b) / (a - b)) *
    (-(I * ((b - a) / 2 * Complex.exp (I * (π - θ)))))

/-- Helper for `thm18_3` (§18.3, I1). Membership in `A(ℍ)` gives an integrable function holomorphic on `ℍ`. -/
theorem gl18_aSpace_upperHalf {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceOpen (toExt upperHalf)) :
    Integrable φ ∧ DifferentiableOn ℂ φ upperHalf := by
  obtain ⟨⟨hi, hd, -⟩, -⟩ := hφ
  refine ⟨hi, hd.mono fun z hz => ?_⟩
  simp only [mem_ofPred_eq, mem_compl_iff, not_not]
  exact ⟨z, hz, rfl⟩

/-- Helper for `thm18_3` (§18.3, S1). `ex₂(h) = T ∘ ex₁(h)` for the real-linear `T(w) = Re w + 2i Im w`. -/
theorem gl18_ba2_eq_comp (h : ℝ → ℝ) :
    beurlingAhlfors h 2 =
      (Complex.reCLM.smulRight (1 : ℂ) + (2 : ℝ) • Complex.imCLM.smulRight I : ℂ →L[ℝ] ℂ) ∘ beurlingAhlfors h 1 := by
  funext w
  simp only [Function.comp_apply, beurlingAhlfors]
  simp [Complex.real_smul]
  ring

/-- Helper for `thm18_3` (§18.3, S1). `∂̄ ex₂(h)` is a real combination of the partials of `ex₁(h)`. -/
theorem gl18_ba2_dzbar_eq {h : ℝ → ℝ} (hh : Continuous h) {z : ℂ} (hz : 0 < z.im) :
    dzbar (beurlingAhlfors h 2) z =
      ((((fderiv ℝ (beurlingAhlfors h 1) z 1).re - 2 * (fderiv ℝ (beurlingAhlfors h 1) z I).im : ℝ) : ℂ) +
        ((2 * (fderiv ℝ (beurlingAhlfors h 1) z 1).im + (fderiv ℝ (beurlingAhlfors h 1) z I).re : ℝ) : ℂ) * I) /
        2 := by
  have hzU : z ∈ upperHalf := hz
  set T : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (1 : ℂ) + (2 : ℝ) • Complex.imCLM.smulRight I with hT
  have hTapp : ∀ w : ℂ, T w = (w.re : ℂ) + ((2 * w.im : ℝ) : ℂ) * I := by
    intro w
    simp [hT, Complex.real_smul]
    ring
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors h 1) z :=
    ((LiZhongQC.ba_f1h_contDiffOn hh).contDiffAt (LiZhongQC.isOpen_upperHalf.mem_nhds hzU)).differentiableAt
      one_ne_zero
  have hfd : fderiv ℝ (beurlingAhlfors h 2) z = T.comp (fderiv ℝ (beurlingAhlfors h 1) z) := by
    rw [gl18_ba2_eq_comp]
    exact (T.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  unfold dzbar
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTapp, hTapp]
  congr 1
  set p := fderiv ℝ (beurlingAhlfors h 1) z 1
  set q := fderiv ℝ (beurlingAhlfors h 1) z I
  push_cast
  linear_combination (2 * (q.im : ℂ)) * Complex.I_sq

/-- Helper for `thm18_3` (§18.3, S1). `∫_a^b h = c₀(b − a) + c₁(b² − a²)/2 + ∫_a^b (h − (c₀ + c₁t))`. -/
theorem gl18_integral_affine_split {h : ℝ → ℝ} (hh : Continuous h) (c₀ c₁ a b : ℝ) :
    ∫ t in a..b, h t = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 + ∫ t in a..b, (h t - (c₀ + c₁ * t)) := by
  have hlin : Continuous fun t : ℝ => c₀ + c₁ * t := by fun_prop
  have hA : ∫ t in a..b, (c₀ + c₁ * t) = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_add (f := fun _ => c₀) (g := fun t => c₁ * t) intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ => c₁ * t).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
    ring
  have e : (fun t => h t) = fun t => (c₀ + c₁ * t) + (h t - (c₀ + c₁ * t)) := by
    funext t
    ring
  rw [e, intervalIntegral.integral_add (f := fun t => c₀ + c₁ * t) (g := fun t => h t - (c₀ + c₁ * t))
    (hlin.intervalIntegrable _ _) ((hh.sub hlin).intervalIntegrable _ _), hA]

/-- Helper for `thm18_3` (§18.3, S1). The linear bound behind S1: with `|aᵢ|, |bᵢ| ≤ M`,
`|−(a₊ − a₋)/2 + (b₊ − b₋)| + |(a₊ − 2a₀ + a₋) + (a₊ + a₋)/2 − (b₊ + b₋)/2| ≤ 9M`. -/
theorem gl18_ba_bound_alg {M ap am a0 bp bm : ℝ} (hp : |ap| ≤ M) (hm : |am| ≤ M) (h0 : |a0| ≤ M)
    (hbp : |bp| ≤ M) (hbm : |bm| ≤ M) :
    |-(ap - am) / 2 + (bp - bm)| + |(ap - 2 * a0 + am) + (ap + am) / 2 - (bp + bm) / 2| ≤ 9 * M := by
  obtain ⟨hp1, hp2⟩ := abs_le.1 hp
  obtain ⟨hm1, hm2⟩ := abs_le.1 hm
  obtain ⟨h01, h02⟩ := abs_le.1 h0
  obtain ⟨hbp1, hbp2⟩ := abs_le.1 hbp
  obtain ⟨hbm1, hbm2⟩ := abs_le.1 hbm
  rcases abs_cases (-(ap - am) / 2 + (bp - bm)) with ⟨e1, -⟩ | ⟨e1, -⟩ <;>
  rcases abs_cases ((ap - 2 * a0 + am) + (ap + am) / 2 - (bp + bm) / 2) with ⟨e2, -⟩ | ⟨e2, -⟩ <;>
  · rw [e1, e2]
    linarith

/-- Helper for `thm18_3` (§18.3, S1). The local `∂̄`-bound for the Beurling–Ahlfors extension (`r = 2`): if
`|h(t) − (c₀ + c₁ t)| ≤ M` on `[x − y, x + y]`, then `|∂̄ ex(h)(x + iy)| ≤ 8M/y` (the formula of `ba_f1_partials` only
sees second differences of `h` at scale `y`, and kills affine functions). -/
theorem gl18_ba_dzbar_le {h : ℝ → ℝ} (hh : Continuous h) {z : ℂ} (hz : 0 < z.im) {c₀ c₁ M : ℝ}
    (hM : ∀ t ∈ Icc (z.re - z.im) (z.re + z.im), |h t - (c₀ + c₁ * t)| ≤ M) :
    ‖dzbar (beurlingAhlfors h 2) z‖ ≤ 8 * M / z.im := by
  have hzU : z ∈ upperHalf := hz
  obtain ⟨h1, hI⟩ := LiZhongQC.ba_f1_partials hh hzU
  rw [gl18_ba2_dzbar_eq hh hz, h1, hI]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  set x := z.re with hx
  set y := z.im with hy
  set R : ℝ → ℝ := fun t => h t - (c₀ + c₁ * t) with hR
  have hRc : Continuous R := hh.sub (by fun_prop)
  have hRb : ∀ t ∈ Icc (x - y) (x + y), |R t| ≤ M := hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hRb x ⟨by linarith, by linarith⟩)
  have hint : ∀ a b : ℝ, x - y ≤ a → a ≤ b → b ≤ x + y → |∫ t in a..b, R t| ≤ M * (b - a) := by
    intro a b ha hab hb
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M) (f := R)
      fun t ht => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le hab] at ht
        exact hRb t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  have hb : ∀ I : ℝ, |I| ≤ M * y → |I / y| ≤ M := fun I hI => by
    rw [abs_div, abs_of_pos hz, div_le_iff₀ hz]
    exact hI
  have hbp : |(∫ t in x..(x + y), R t) / y| ≤ M :=
    hb _ (by simpa using hint x (x + y) (by linarith) (by linarith) le_rfl)
  have hbm : |(∫ t in (x - y)..x, R t) / y| ≤ M :=
    hb _ (by simpa using hint (x - y) x le_rfl (by linarith) (by linarith))
  have halg := gl18_ba_bound_alg (hRb (x + y) ⟨by linarith, le_rfl⟩) (hRb (x - y) ⟨le_rfl, by linarith⟩)
    (hRb x ⟨by linarith, by linarith⟩) hbp hbm
  -- the final estimate, for real parts `U`, `W` of `2 ∂̄` given through `U y`, `W y`
  have key : ∀ U W : ℝ,
      U * y = -(R (x + y) - R (x - y)) / 2 + ((∫ t in x..(x + y), R t) / y - (∫ t in (x - y)..x, R t) / y) →
      W * y = (R (x + y) - 2 * R x + R (x - y)) + (R (x + y) + R (x - y)) / 2 -
        ((∫ t in x..(x + y), R t) / y + (∫ t in (x - y)..x, R t) / y) / 2 →
      ‖((U : ℂ) + (W : ℂ) * I) / 2‖ ≤ 8 * M / y := by
    intro U W hU hW
    have hsum : |U| + |W| ≤ 9 * M / y := by
      rw [le_div_iff₀ hz, add_mul, ← abs_of_pos hz, ← abs_mul, ← abs_mul, hU, hW]
      exact halg
    rw [norm_div, Complex.norm_ofNat]
    have hn : ‖(U : ℂ) + (W : ℂ) * I‖ ≤ |U| + |W| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    have h8 : 9 * M / y ≤ 16 * M / y := div_le_div_of_nonneg_right (by linarith) hz.le
    have h10 : 2 * (8 * M / y) = 16 * M / y := by ring
    linarith
  have hval : ∀ t, h t = c₀ + c₁ * t + R t := fun t => by simp only [hR]; ring
  have hsp : ∀ a b : ℝ, ∫ t in a..b, h t = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 + ∫ t in a..b, R t :=
    gl18_integral_affine_split hh c₀ c₁
  have hadd : ∫ t in (x - y)..(x + y), R t = (∫ t in (x - y)..x, R t) + ∫ t in x..(x + y), R t :=
    (intervalIntegral.integral_add_adjacent_intervals (hRc.intervalIntegrable _ _)
      (hRc.intervalIntegrable _ _)).symm
  have hy0 : y ≠ 0 := hz.ne'
  refine key _ _ ?_ ?_
  · rw [hsp x (x + y), hsp (x - y) x, hval (x + y), hval (x - y)]
    field_simp
    ring
  · rw [hsp (x - y) (x + y), hadd, hval (x + y), hval (x - y), hval x]
    field_simp
    ring

/-- Helper for `thm18_3` (§18.3, S9). The Beurling–Ahlfors extension (`r = 2`) of a continuous `h` is real
differentiable on `ℍ`. -/
theorem gl18_ba_differentiableOn {h : ℝ → ℝ} (hh : Continuous h) :
    DifferentiableOn ℝ (beurlingAhlfors h 2) upperHalf := by
  rw [gl18_ba2_eq_comp]
  exact (ContinuousLinearMap.differentiable _).comp_differentiableOn
    ((LiZhongQC.ba_f1h_contDiffOn hh).differentiableOn one_ne_zero)

/-- Helper for `thm18_3` (§18.3, S9). Linear growth of `h` gives linear growth of its extension on `ℍ̄`. -/
theorem gl18_ba_growth {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ} (hC : ∀ t, |h t| ≤ C * (1 + |t|)) :
    ∀ z : ℂ, 0 ≤ z.im → ‖beurlingAhlfors h 2 z‖ ≤ 6 * C * (1 + ‖z‖) := by
  intro z hz
  have _hh := hh
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    simpa using this
  set K := C * (1 + |z.re| + z.im) with hK
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, |h (z.re + t * z.im)| ≤ K ∧ |h (z.re - t * z.im)| ≤ K := by
    intro t ht
    have h1 : |z.re + t * z.im| ≤ |z.re| + z.im := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hz]
      nlinarith [ht.2]
    have h2 : |z.re - t * z.im| ≤ |z.re| + z.im := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hz]
      nlinarith [ht.2]
    exact ⟨(hC _).trans (by rw [hK]; nlinarith), (hC _).trans (by rw [hK]; nlinarith)⟩
  have hint : ∀ f : ℝ → ℝ, (∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ 2 * K) → |∫ t in (0 : ℝ)..1, f t| ≤ 2 * K := by
    intro f hf
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 2 * K) (f := f)
      fun t ht => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact hf t ⟨ht.1.le, ht.2⟩
    simpa using this
  have hs := hint (fun t => h (z.re + t * z.im) + h (z.re - t * z.im)) fun t ht =>
    (abs_add_le _ _).trans (by linarith [(hpt t ht).1, (hpt t ht).2])
  have hd := hint (fun t => h (z.re + t * z.im) - h (z.re - t * z.im)) fun t ht =>
    (abs_sub _ _).trans (by linarith [(hpt t ht).1, (hpt t ht).2])
  unfold beurlingAhlfors
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul]
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
  have hK' : K ≤ C * (1 + 2 * ‖z‖) := by rw [hK]; nlinarith
  norm_num
  nlinarith

/-- Helper for `thm18_3` (§18.3, S2). `E_ab(x) = P(clamp x)` with `P(x) = (x − a)(x − b)/(a − b)` and
`clamp x = max a (min x b)`. -/
theorem gl18_earthquakeVF_eq_clamp {a b : ℝ} (hab : a < b) (x : ℝ) :
    earthquakeVF a b x = (max a (min x b) - a) * (max a (min x b) - b) / (a - b) := by
  unfold earthquakeVF
  by_cases hx : a ≤ x ∧ x ≤ b
  · rw [ite_eq_left hx, min_eq_left hx.2, max_eq_right hx.1]
  · rw [ite_eq_right hx]
    rcases not_and_or.1 hx with h | h
    · push Not at h
      rw [max_eq_left (min_le_of_left_le h.le)]
      ring
    · push Not at h
      rw [min_eq_right h.le, max_eq_right hab.le]
      ring

/-- Helper for `thm18_3` (§18.3, S2). `E_ab` is `1`-Lipschitz. -/
theorem gl18_earthquakeVF_lipschitz {a b : ℝ} (hab : a < b) : LipschitzWith 1 (earthquakeVF a b) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, gl18_earthquakeVF_eq_clamp hab]
  set cs := max a (min s b)
  set ct := max a (min t b)
  have hcs : a ≤ cs ∧ cs ≤ b := ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hct : a ≤ ct ∧ ct ≤ b := ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hc : |cs - ct| ≤ |s - t| := by
    have h1 : |min s b - min t b| ≤ |s - t| := abs_min_sub_min_le_max s b t b |>.trans (by simp)
    exact (abs_max_sub_max_le_max a (min s b) a (min t b)).trans (by simpa using h1)
  have hab' : 0 < b - a := by linarith
  have e : (cs - a) * (cs - b) / (a - b) - (ct - a) * (ct - b) / (a - b) =
      (cs - ct) * (a + b - cs - ct) / (b - a) := by
    have h1 : a - b ≠ 0 := by linarith
    have h2 : b - a ≠ 0 := by linarith
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_pos hab', div_le_iff₀ hab']
  have h2 : |a + b - cs - ct| ≤ b - a := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith [abs_nonneg (cs - ct), abs_nonneg (a + b - cs - ct)]

/-- Helper for `thm18_3` (§18.3, S2). `|E_ab| ≤ b − a`. -/
theorem gl18_earthquakeVF_bound {a b : ℝ} (hab : a < b) (t : ℝ) : |earthquakeVF a b t| ≤ b - a := by
  rw [gl18_earthquakeVF_eq_clamp hab]
  set c := max a (min t b)
  have hc : a ≤ c ∧ c ≤ b := ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hab' : 0 < b - a := by linarith
  have e : (c - a) * (c - b) / (a - b) = (c - a) * (b - c) / (b - a) := by
    have h1 : a - b ≠ 0 := by linarith
    have h2 : b - a ≠ 0 := by linarith
    field_simp
    ring
  rw [e, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hab'.le), div_le_iff₀ hab']
  nlinarith

/-- Helper for `thm18_3` (§18.3, S2). `|∂̄ ex(E_ab)| ≤ 8` on `ℍ` (S1 with the constant `E_ab(x)`, `M = y`). -/
theorem gl18_earthquakeVF_dzbar_le {a b : ℝ} (hab : a < b) {z : ℂ} (hz : 0 < z.im) :
    ‖dzbar (beurlingAhlfors (earthquakeVF a b) 2) z‖ ≤ 8 := by
  have hL := gl18_earthquakeVF_lipschitz hab
  have h := gl18_ba_dzbar_le hL.continuous hz (c₀ := earthquakeVF a b z.re) (c₁ := 0) (M := z.im) fun t ht => by
    rw [zero_mul, add_zero]
    have := hL.dist_le_mul t z.re
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at this
    exact this.trans (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rwa [mul_div_assoc, div_self hz.ne', mul_one] at h

/-- Helper for `thm18_3` (§18.3, S3). Inequalities pass from `ℍ` to the closed upper half-plane by continuity. -/
theorem gl18_le_of_upperHalf {f g : ℂ → ℝ} (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hg : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (h : ∀ z : ℂ, 0 < z.im → f z ≤ g z) {z : ℂ} (hz : 0 ≤ z.im) :
    f z ≤ g z := by
  set u : ℕ → ℂ := fun n => z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hu
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have him : ∀ n, (u n).im = z.im + 1 / ((n : ℝ) + 1) := fun n => by
    simp only [hu, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hmem : ∀ n, u n ∈ {z : ℂ | 0 ≤ z.im} := fun n => by
    show 0 ≤ (u n).im
    rw [him]
    linarith [hpos n]
  have hlim : Tendsto u atTop (𝓝[{z : ℂ | 0 ≤ z.im}] z) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hmem⟩
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.mul_const I
    have h2 := (tendsto_const_nhds (x := z)).add h1
    rw [add_zero] at h2
    exact h2
  have hfz := (hf z hz).tendsto.comp hlim
  have hgz := (hg z hz).tendsto.comp hlim
  refine le_of_tendsto_of_tendsto' hfz hgz fun n => h _ ?_
  show 0 < (u n).im
  rw [him]
  linarith [hpos n]

/-- Helper for `thm18_3` (§18.3, S3). `(w − c) log(w − c) → 0` as `w → c`. -/
theorem gl18_mul_log_tendsto (c : ℂ) : Tendsto (fun w : ℂ => (w - c) * log (w - c)) (𝓝 c) (𝓝 0) := by
  have hn : Continuous fun w : ℂ => ‖w - c‖ := continuous_norm.comp (continuous_id.sub continuous_const)
  have h3 : Tendsto (fun w : ℂ => |‖w - c‖ * Real.log ‖w - c‖|) (𝓝 c) (𝓝 0) := by
    have := ((Real.continuous_mul_log.comp hn).tendsto c).abs
    simpa using this
  have h4 : Tendsto (fun w : ℂ => ‖w - c‖ * π) (𝓝 c) (𝓝 0) := by
    simpa using (hn.tendsto c).mul_const π
  have h2 : Tendsto (fun w : ℂ => ‖w - c‖ * (|Real.log ‖w - c‖| + π)) (𝓝 c) (𝓝 0) := by
    have := h3.add h4
    rw [add_zero] at this
    refine this.congr fun w => ?_
    rw [abs_mul, abs_norm]
    ring
  refine squeeze_zero_norm (fun w => ?_) h2
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖log (w - c)‖ ≤ |(log (w - c)).re| + |(log (w - c)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖w - c‖| + π := by
        rw [Complex.log_re, Complex.log_im]
        gcongr
        exact Complex.abs_arg_le_pi _

/-- Helper for `thm18_3` (§18.3, S3). `F(z) = (z − a)(z − b)/(a − b) · (log(z − a) − log(z − b))` is holomorphic
on `ℍ`. -/
theorem gl18_F_differentiableOn {a b : ℝ} {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) :
    DifferentiableOn ℂ F upperHalf := by
  subst hF
  intro z hz
  have hz' : 0 < z.im := hz
  have ha : z - a ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hz'.ne'))
  have hb : z - b ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hz'.ne'))
  refine DifferentiableAt.differentiableWithinAt ?_
  have hla := (differentiableAt_id.sub_const (a : ℂ)).clog ha
  have hlb := (differentiableAt_id.sub_const (b : ℂ)).clog hb
  exact (((differentiableAt_id.sub_const _).mul (differentiableAt_id.sub_const _)).div_const _).mul (hla.sub hlb)

/-- Helper for `thm18_3` (§18.3, S3). The boundary values of `F` are `B_ab − iπ E_ab` (the book's
`z log z ≡ B − iπE`, moved to the line joining `a` to `b`). -/
theorem gl18_F_real {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) (t : ℝ) :
    F t = (bendVF a b t : ℂ) - I * π * (earthquakeVF a b t : ℂ) := by
  subst hF
  have e1 : (t : ℂ) - a = ((t - a : ℝ) : ℂ) := by push_cast; ring
  have e2 : (t : ℂ) - b = ((t - b : ℝ) : ℂ) := by push_cast; ring
  have eP : (t : ℂ) - a = ((t - a : ℝ) : ℂ) → ((t : ℂ) - a) * ((t : ℂ) - b) / ((a : ℂ) - b) =
      (((t - a) * (t - b) / (a - b) : ℝ) : ℂ) := fun _ => by push_cast; ring
  simp only
  rw [eP e1, e1, e2]
  set P : ℝ := (t - a) * (t - b) / (a - b) with hP
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, sub_zero,
      mul_zero]
    unfold bendVF
    rw [← hP]
    rcases eq_or_ne t a with rfl | hta
    · simp [hP]
    rcases eq_or_ne t b with rfl | htb
    · simp [hP]
    rw [abs_div, Real.log_div (abs_ne_zero.2 (sub_ne_zero.2 hta)) (abs_ne_zero.2 (sub_ne_zero.2 htb))]
  · simp only [Complex.sub_im, Complex.log_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
    unfold earthquakeVF
    rcases lt_or_ge t a with hta | hta
    · rw [Complex.arg_ofReal_of_neg (by linarith), Complex.arg_ofReal_of_neg (by linarith),
        ite_eq_right (fun h => by linarith [h.1])]
      ring
    rcases lt_or_ge b t with htb | htb
    · rw [Complex.arg_ofReal_of_nonneg (by linarith), Complex.arg_ofReal_of_nonneg (by linarith),
        ite_eq_right (fun h => by linarith [h.2])]
      ring
    rw [ite_eq_left ⟨hta, htb⟩, ← hP]
    rcases eq_or_lt_of_le htb with rfl | htb'
    · simp [hP]
    rw [Complex.arg_ofReal_of_nonneg (by linarith), Complex.arg_ofReal_of_neg (by linarith)]
    ring

/-- Helper for `thm18_3` (§18.3, S3). `F` is continuous on the closed upper half-plane. -/
theorem gl18_F_continuousOn {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) :
    ContinuousOn F {z : ℂ | 0 ≤ z.im} := by
  set S := {z : ℂ | 0 ≤ z.im} with hS
  have hd := gl18_F_differentiableOn hF
  subst hF
  -- `w ↦ log (w − c)` is continuous within `S` off `c`, for real `c`
  have hlog : ∀ c : ℝ, ∀ z ∈ S, z ≠ c → ContinuousWithinAt (fun w : ℂ => log (w - c)) S z := by
    intro c z hz hzc
    have hsub : ContinuousWithinAt (fun w : ℂ => w - c) S z := (continuous_id.sub continuous_const).continuousWithinAt
    have hmap : MapsTo (fun w : ℂ => w - c) S S := fun w hw => by
      have hw' : 0 ≤ w.im := hw
      show 0 ≤ (w - c).im
      simpa using hw'
    have hre' : (z - c).re = z.re - c := by simp
    have him' : (z - c).im = z.im := by simp
    by_cases hsl : z - c ∈ slitPlane
    · exact ContinuousAt.comp_continuousWithinAt (g := log) (f := fun w : ℂ => w - c) (continuousAt_clog hsl) hsub
    · rw [Complex.mem_slitPlane_iff] at hsl
      push Not at hsl
      have hre : (z - c).re < 0 := by
        rcases hsl.1.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hzc
          apply Complex.ext
          · simp only [Complex.ofReal_re]
            linarith
          · simp only [Complex.ofReal_im]
            linarith [hsl.2]
      exact ContinuousWithinAt.comp (g := log) (f := fun w : ℂ => w - c)
        (continuousWithinAt_log_of_re_neg_of_im_zero hre hsl.2) hsub hmap
  intro z hz
  by_cases hzi : 0 < z.im
  · exact (hd.differentiableAt (LiZhongQC.isOpen_upperHalf.mem_nhds hzi)).continuousAt.continuousWithinAt
  have hzi0 : z.im = 0 := le_antisymm (not_lt.1 hzi) hz
  have hpoly : Continuous fun w : ℂ => (w - a) * (w - b) / (a - b) := by fun_prop
  by_cases hza : z = a
  · -- at `a`: `F = [(w − a) log (w − a)] (w − b)/(a − b) − P(w) log (w − b)`, both `→ 0`
    subst hza
    have hab' : ((a : ℂ) - b) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact_mod_cast (sub_neg.2 hab).ne
    have h1 : Tendsto (fun w : ℂ => (w - a) * log (w - a) * ((w - b) / (a - b))) (𝓝[S] (a : ℂ)) (𝓝 0) := by
      have := (gl18_mul_log_tendsto (a : ℂ)).mul
        (((by fun_prop : Continuous fun w : ℂ => (w - b) / (a - b)).continuousAt (x := (a : ℂ))).tendsto)
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun w : ℂ => (w - a) * (w - b) / (a - b) * log (w - b)) (𝓝[S] (a : ℂ)) (𝓝 0) := by
      have hc := hlog b a hz (by exact_mod_cast hab.ne)
      have := ((hpoly.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hc.tendsto)
      simpa using this
    have := h1.sub h2
    rw [sub_zero] at this
    show Tendsto _ _ _
    simp only [sub_self, zero_mul, zero_div]
    refine this.congr fun w => ?_
    field_simp
  by_cases hzb : z = b
  · subst hzb
    have h1 : Tendsto (fun w : ℂ => (w - a) * (w - b) / (a - b) * log (w - a)) (𝓝[S] (b : ℂ)) (𝓝 0) := by
      have hc := hlog a b hz (by exact_mod_cast hab.ne')
      have := ((hpoly.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hc.tendsto)
      simpa using this
    have h2 : Tendsto (fun w : ℂ => (w - b) * log (w - b) * ((w - a) / (a - b))) (𝓝[S] (b : ℂ)) (𝓝 0) := by
      have := (gl18_mul_log_tendsto (b : ℂ)).mul
        (((by fun_prop : Continuous fun w : ℂ => (w - a) / (a - b)).continuousAt (x := (b : ℂ))).tendsto)
      simpa using this.mono_left nhdsWithin_le_nhds
    have := h1.sub h2
    rw [sub_zero] at this
    show Tendsto _ _ _
    simp only [sub_self, mul_zero, zero_div, zero_mul]
    refine this.congr fun w => ?_
    ring
  exact (hpoly.continuousWithinAt).mul ((hlog a z hz hza).sub (hlog b z hz hzb))

/-- Helper for `thm18_3` (§18.3, S4). `log(ζ − a) − log(ζ − b) = ∫_a^b ds/(ζ − s)` for `ζ ∈ ℍ`. -/
theorem gl18_ell_integral {a b : ℝ} {ζ : ℂ} (hζ : 0 < ζ.im) :
    log (ζ - a) - log (ζ - b) = ∫ s in a..b, 1 / (ζ - s) := by
  have hmem : ∀ s : ℝ, ζ - s ∈ slitPlane := fun s =>
    Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))
  have hne : ∀ s : ℝ, ζ - (s : ℂ) ≠ 0 := fun s => slitPlane_ne_zero (hmem s)
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -log (ζ - s)) (1 / (ζ - s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ζ - (s : ℂ)) (-1) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).const_sub ζ
    have h2 := (h1.clog_real (hmem s)).neg
    convert h2 using 1
    rw [neg_div, neg_neg]
  have hc : Continuous fun s : ℝ => 1 / (ζ - s) :=
    continuous_const.div (continuous_const.sub Complex.continuous_ofReal) fun s => hne s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
  ring

/-- Helper for `thm18_3` (§18.3, S4). `|log(ζ − a) − log(ζ − b)| ≤ (b − a)/d` when `d ≤ |ζ − s|` on `[a, b]`. -/
theorem gl18_ell_bound {a b : ℝ} (hab : a < b) {ζ : ℂ} (hζ : 0 < ζ.im) {d : ℝ} (hd0 : 0 < d)
    (hd : ∀ s ∈ Icc a b, d ≤ ‖ζ - s‖) : ‖log (ζ - a) - log (ζ - b)‖ ≤ (b - a) / d := by
  rw [gl18_ell_integral hζ]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1 / d)
    (f := fun s : ℝ => 1 / (ζ - s)) fun s hs => by
      rw [Set.uIoc_of_le hab.le] at hs
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hd0 (hd s ⟨hs.1.le, hs.2⟩)
  rw [abs_of_pos (sub_pos.2 hab)] at this
  calc _ ≤ 1 / d * (b - a) := this
    _ = (b - a) / d := by ring

/-- Helper for `thm18_3` (§18.3, S4). `F' = (2z − a − b)/(a − b) · ℓ + 1` on `ℍ`, `ℓ = log(z − a) − log(z − b)`. -/
theorem gl18_F_hasDerivAt {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt F ((2 * ζ - a - b) / (a - b) * (log (ζ - a) - log (ζ - b)) + 1) ζ := by
  subst hF
  have ha : ζ - a ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))
  have hb : ζ - b ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))
  have hla := ((hasDerivAt_id ζ).sub_const (a : ℂ)).clog ha
  have hlb := ((hasDerivAt_id ζ).sub_const (b : ℂ)).clog hb
  have hP := (((hasDerivAt_id ζ).sub_const (a : ℂ)).mul ((hasDerivAt_id ζ).sub_const (b : ℂ))).div_const
    ((a : ℂ) - b)
  have hza : ζ - a ≠ 0 := slitPlane_ne_zero ha
  have hzb : ζ - b ≠ 0 := slitPlane_ne_zero hb
  have hab' : (a : ℂ) - b ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast (sub_neg.2 hab).ne
  convert hP.mul (hla.sub hlb) using 1
  · funext z
    rfl
  · simp only [id, Pi.sub_apply, Pi.mul_apply]
    field_simp
    ring

/-- Helper for `thm18_3` (§18.3, S4). `F'' = 2ℓ/(a − b) + 1/(z − a) + 1/(z − b)` on `ℍ`. -/
theorem gl18_Fd_hasDerivAt {a b : ℝ} (hab : a < b) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt (fun z : ℂ => (2 * z - a - b) / (a - b) * (log (z - a) - log (z - b)) + 1)
      (2 / (a - b) * (log (ζ - a) - log (ζ - b)) + (1 / (ζ - a) + 1 / (ζ - b))) ζ := by
  have ha : ζ - a ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))
  have hb : ζ - b ∈ slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))
  have hla := ((hasDerivAt_id ζ).sub_const (a : ℂ)).clog ha
  have hlb := ((hasDerivAt_id ζ).sub_const (b : ℂ)).clog hb
  have hP := ((((hasDerivAt_id ζ).const_mul (2 : ℂ)).sub_const (a : ℂ)).sub_const (b : ℂ)).div_const
    ((a : ℂ) - b)
  have hza : ζ - a ≠ 0 := slitPlane_ne_zero ha
  have hzb : ζ - b ≠ 0 := slitPlane_ne_zero hb
  have hab' : (a : ℂ) - b ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast (sub_neg.2 hab).ne
  convert (hP.mul (hla.sub hlb)).add_const 1 using 1
  · funext z
    rfl
  · simp only [id, Pi.sub_apply]
    field_simp
    ring

/-- Helper for `thm18_3` (§18.3, S4). `|F''(ζ)| ≤ 4/Im ζ` on `ℍ`. -/
theorem gl18_Fdd_bound {a b : ℝ} (hab : a < b) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ‖2 / (a - b) * (log (ζ - a) - log (ζ - b)) + (1 / (ζ - a) + 1 / (ζ - b))‖ ≤ 4 / ζ.im := by
  have hd : ∀ c : ℝ, ζ.im ≤ ‖ζ - c‖ := fun c => by
    have := Complex.abs_im_le_norm (ζ - c)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hl := gl18_ell_bound hab hζ hζ fun s _ => hd s
  have hab' : 0 < b - a := sub_pos.2 hab
  have h1 : ‖2 / ((a : ℂ) - b)‖ = 2 / (b - a) := by
    rw [norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    simp
  have h2 : ∀ c : ℝ, ‖1 / (ζ - c)‖ ≤ 1 / ζ.im := fun c => by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hζ (hd c)
  calc _ ≤ ‖2 / ((a : ℂ) - b) * (log (ζ - a) - log (ζ - b))‖ + (‖1 / (ζ - a)‖ + ‖1 / (ζ - b)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 2 / (b - a) * ((b - a) / ζ.im) + (1 / ζ.im + 1 / ζ.im) := by
        rw [norm_mul, h1]
        gcongr
        · exact h2 a
        · exact h2 b
    _ = 4 / ζ.im := by field_simp; ring

/-- Helper for `thm18_3` (§18.3, S4). The Taylor remainder of `F` at `z₀ ∈ ℍ` is `≤ 4|w − z₀|²/Im z₀` on `ℍ̄`
(`F'' = 2ℓ/(a − b) + 1/(z − a) + 1/(z − b)`, `ℓ = ∫_a^b ds/(z − s)`, so `|F''| ≤ 4/Im z`). -/
theorem gl18_F_taylor {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    {w : ℂ} (hw : 0 ≤ w.im) :
    ‖F w - F z₀ - deriv F z₀ * (w - z₀)‖ ≤ 4 * ‖w - z₀‖ ^ 2 / z₀.im := by
  set F' : ℂ → ℂ := fun z => (2 * z - a - b) / (a - b) * (log (z - a) - log (z - b)) + 1 with hF'
  set F'' : ℂ → ℂ := fun z => 2 / (a - b) * (log (z - a) - log (z - b)) + (1 / (z - a) + 1 / (z - b))
    with hF''
  have hFd : ∀ ζ : ℂ, 0 < ζ.im → HasDerivAt F (F' ζ) ζ := fun ζ hζ => gl18_F_hasDerivAt hab hF hζ
  have hF'd : ∀ ζ : ℂ, 0 < ζ.im → HasDerivAt F' (F'' ζ) ζ := fun ζ hζ => gl18_Fd_hasDerivAt hab hζ
  rw [(hFd z₀ hz₀).deriv]
  have hS := gl18_F_continuousOn hab hF
  refine gl18_le_of_upperHalf (f := fun w => ‖F w - F z₀ - F' z₀ * (w - z₀)‖)
    (g := fun w => 4 * ‖w - z₀‖ ^ 2 / z₀.im)
    (((hS.sub continuousOn_const).sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).norm)
    (by fun_prop) (fun w hw' => ?_) hw
  -- `w ∈ ℍ`: the mean value inequality for `φ(τ) = F(σ τ) + (1 − τ) F'(σ τ) (w − z₀)`
  set σ : ℝ → ℂ := fun τ => z₀ + (τ : ℂ) * (w - z₀) with hσ
  have hσim : ∀ τ : ℝ, (σ τ).im = (1 - τ) * z₀.im + τ * w.im := fun τ => by
    simp only [hσ, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.sub_re, zero_mul, add_zero]
    ring
  have hσpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < (σ τ).im := fun τ hτ => by
    rw [hσim]
    rcases eq_or_lt_of_le hτ.2 with h | h
    · rw [h]
      linarith
    · nlinarith [hτ.1]
  have hσd : ∀ τ : ℝ, HasDerivAt σ (w - z₀) τ := fun τ => by
    have := (((hasDerivAt_id τ).ofReal_comp).mul_const (w - z₀)).const_add z₀
    convert this using 1
    · exact hσ
    · simp
  set φ : ℝ → ℂ := fun τ => F (σ τ) + ((1 - τ : ℝ) : ℂ) * (F' (σ τ) * (w - z₀)) with hφ
  have hφd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (((1 - τ : ℝ) : ℂ) * (F'' (σ τ) * (w - z₀) ^ 2))
      (Icc 0 1) τ := by
    intro τ hτ
    have h1 := (hFd (σ τ) (hσpos τ hτ)).comp τ (hσd τ)
    have h2 := (hF'd (σ τ) (hσpos τ hτ)).comp τ (hσd τ)
    have h3 : HasDerivAt (fun τ : ℝ => ((1 - τ : ℝ) : ℂ)) (((-1 : ℝ)) : ℂ) τ :=
      ((hasDerivAt_id τ).const_sub 1).ofReal_comp
    have h4 := h1.add (h3.mul (h2.mul_const (w - z₀)))
    refine HasDerivAt.hasDerivWithinAt ?_
    convert h4 using 1
    · funext τ
      rfl
    · simp only [Function.comp_apply]
      push_cast
      ring
  have hbd : ∀ τ ∈ Ico (0 : ℝ) 1,
      ‖((1 - τ : ℝ) : ℂ) * (F'' (σ τ) * (w - z₀) ^ 2)‖ ≤ 4 * ‖w - z₀‖ ^ 2 / z₀.im := by
    intro τ hτ
    have hpos := hσpos τ (Ico_subset_Icc_self hτ)
    have hb := gl18_Fdd_bound hab hpos
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1τ]
    have hle : (1 - τ) * (4 / (σ τ).im) ≤ 4 / z₀.im := by
      rw [mul_div_assoc', div_le_div_iff₀ hpos hz₀, hσim]
      nlinarith [hτ.1, hw'.le]
    calc (1 - τ) * (‖F'' (σ τ)‖ * ‖w - z₀‖ ^ 2) ≤ (1 - τ) * (4 / (σ τ).im * ‖w - z₀‖ ^ 2) := by gcongr
      _ = (1 - τ) * (4 / (σ τ).im) * ‖w - z₀‖ ^ 2 := by ring
      _ ≤ 4 / z₀.im * ‖w - z₀‖ ^ 2 := by gcongr
      _ = 4 * ‖w - z₀‖ ^ 2 / z₀.im := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hφd hbd 1 ⟨zero_le_one, le_rfl⟩
  have e1 : φ 1 = F w := by simp [hφ, hσ]
  have e0 : φ 0 = F z₀ + F' z₀ * (w - z₀) := by simp [hφ, hσ]
  rw [e1, e0, sub_zero, mul_one] at hmv
  show ‖F w - F z₀ - F' z₀ * (w - z₀)‖ ≤ _
  rwa [show F w - F z₀ - F' z₀ * (w - z₀) = F w - (F z₀ + F' z₀ * (w - z₀)) by ring]

/-- Helper for `thm18_3` (§18.3, S3). `F` grows at most linearly on the closed upper half-plane. -/
theorem gl18_F_growth {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : F = fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b))) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ C * (1 + ‖z‖) := by
  have hc := gl18_F_continuousOn hab hF
  set R₀ : ℝ := 2 * (|a| + |b|) + 1 with hR₀
  have hK : IsCompact (closedBall (0 : ℂ) R₀ ∩ {z : ℂ | 0 ≤ z.im}) :=
    (isCompact_closedBall 0 R₀).inter_right (isClosed_le continuous_const Complex.continuous_im)
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hc.mono inter_subset_right)
  have hM : (5 : ℝ) ≤ max C₁ 5 := le_max_right _ _
  refine ⟨max C₁ 5, fun z hz => gl18_le_of_upperHalf (f := fun z => ‖F z‖)
    (g := fun z => max C₁ 5 * (1 + ‖z‖)) hc.norm (by fun_prop) (fun ζ hζ => ?_) hz⟩
  show ‖F ζ‖ ≤ max C₁ 5 * (1 + ‖ζ‖)
  by_cases hR : ‖ζ‖ ≤ R₀
  · have h1 := hC₁ ζ ⟨mem_closedBall_zero_iff.2 hR, hζ.le⟩
    have h2 : C₁ ≤ max C₁ 5 := le_max_left _ _
    nlinarith [norm_nonneg ζ]
  · push Not at hR
    have hab' : 0 < b - a := sub_pos.2 hab
    have hζ0 : 0 < ‖ζ‖ := by linarith [abs_nonneg a, abs_nonneg b]
    have ha : |a| ≤ ‖ζ‖ / 2 := by linarith [abs_nonneg b]
    have hb : |b| ≤ ‖ζ‖ / 2 := by linarith [abs_nonneg a]
    have hs : ∀ s ∈ Icc a b, ‖ζ‖ / 2 ≤ ‖ζ - s‖ := by
      intro s hs
      have h1 : |s| ≤ ‖ζ‖ / 2 := abs_le.2 ⟨by linarith [neg_abs_le a, hs.1], by linarith [le_abs_self b, hs.2]⟩
      have h2 := norm_sub_norm_le ζ (s : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h2
      linarith
    have hl := gl18_ell_bound hab hζ (by positivity) hs
    have hna : ‖ζ - a‖ ≤ 3 / 2 * ‖ζ‖ := by
      have := norm_sub_le ζ (a : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hnb : ‖ζ - b‖ ≤ 3 / 2 * ‖ζ‖ := by
      have := norm_sub_le ζ (b : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hab2 : ‖(a : ℂ) - b‖ = b - a := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    subst hF
    show ‖(ζ - a) * (ζ - b) / (a - b) * (log (ζ - a) - log (ζ - b))‖ ≤ _
    rw [norm_mul, norm_div, norm_mul, hab2]
    have hP : ‖ζ - a‖ * ‖ζ - b‖ / (b - a) ≤ 9 / 4 * ‖ζ‖ ^ 2 / (b - a) := by
      refine div_le_div_of_nonneg_right ?_ hab'.le
      have := mul_le_mul hna hnb (norm_nonneg _) (by positivity)
      linarith
    calc ‖ζ - a‖ * ‖ζ - b‖ / (b - a) * ‖log (ζ - a) - log (ζ - b)‖
        ≤ 9 / 4 * ‖ζ‖ ^ 2 / (b - a) * ((b - a) / (‖ζ‖ / 2)) :=
          mul_le_mul hP hl (norm_nonneg _) (by positivity)
      _ = 9 / 2 * ‖ζ‖ := by field_simp; ring
      _ ≤ max C₁ 5 * (1 + ‖ζ‖) := by nlinarith [norm_nonneg ζ]

/-- Helper for `thm18_3` (§18.3, S3). `B_ab` is continuous with linear growth (it is `Re F` on `ℝ`). -/
theorem gl18_bendVF_continuous_growth {a b : ℝ} (hab : a < b) :
    Continuous (bendVF a b) ∧ ∃ C : ℝ, ∀ t, |bendVF a b t| ≤ C * (1 + |t|) := by
  set F : ℂ → ℂ := fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b)) with hF
  have hre : ∀ t : ℝ, bendVF a b t = (F t).re := fun t => by
    rw [gl18_F_real hab hF t]
    simp
  have hcF : Continuous fun t : ℝ => F t :=
    (gl18_F_continuousOn hab hF).comp_continuous Complex.continuous_ofReal fun t => by
      show 0 ≤ (t : ℂ).im
      simp
  refine ⟨?_, ?_⟩
  · rw [show bendVF a b = fun t : ℝ => (F (t : ℂ)).re from funext hre]
    exact Complex.continuous_re.comp hcF
  · obtain ⟨C, hC⟩ := gl18_F_growth hab hF
    refine ⟨C, fun t => ?_⟩
    rw [hre]
    calc |(F t).re| ≤ ‖F t‖ := Complex.abs_re_le_norm _
      _ ≤ C * (1 + ‖(t : ℂ)‖) := hC t (by simp)
      _ = C * (1 + |t|) := by rw [Complex.norm_real, Real.norm_eq_abs]

/-- Helper for `thm18_3` (§18.3, S4). `|∂̄ ex(B_ab)| ≤ 64` on `ℍ` (S1 with the real part of the tangent line of `F`
at `z`, `M = 8y`). -/
theorem gl18_bendVF_dzbar_le {a b : ℝ} (hab : a < b) {z : ℂ} (hz : 0 < z.im) :
    ‖dzbar (beurlingAhlfors (bendVF a b) 2) z‖ ≤ 64 := by
  set F : ℂ → ℂ := fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b)) with hF
  obtain ⟨hcont, -⟩ := gl18_bendVF_continuous_growth hab
  have h := gl18_ba_dzbar_le hcont hz (c₀ := (F z - deriv F z * z).re) (c₁ := (deriv F z).re)
    (M := 8 * z.im) fun t ht => by
      have hre : bendVF a b t = (F t).re := by
        rw [gl18_F_real hab hF t]
        simp
      have e : bendVF a b t - ((F z - deriv F z * z).re + (deriv F z).re * t) =
          (F t - F z - deriv F z * (t - z)).re := by
        rw [hre]
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im]
        ring
      rw [e]
      refine (Complex.abs_re_le_norm _).trans ((gl18_F_taylor hab hF hz (by simp : 0 ≤ (t : ℂ).im)).trans ?_)
      have h1 : |t - z.re| ≤ z.im := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : ‖(t : ℂ) - z‖ ^ 2 ≤ 2 * z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
        have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
        nlinarith
      rw [div_le_iff₀ hz]
      nlinarith
  calc _ ≤ 8 * (8 * z.im) / z.im := h
    _ = 64 := by field_simp; ring

/-- Helper for `thm18_3` (§18.3, S5). A bounded `∂̄ ex(V)` pairs integrably with every integrable `φ` on `ℍ`. -/
theorem gl18_pairing_integrable {V : ℝ → ℝ} {C : ℝ} (hC : ∀ z : ℂ, 0 < z.im → ‖dzbar (beurlingAhlfors V 2) z‖ ≤ C)
    {φ : ℂ → ℂ} (hφ : IntegrableOn φ upperHalf) :
    IntegrableOn (fun z => dzbar (beurlingAhlfors V 2) z * φ z) upperHalf := by
  have hm : Measurable (dzbar (beurlingAhlfors V 2)) := by
    show Measurable fun z => (fderiv ℝ (beurlingAhlfors V 2) z 1 + I * fderiv ℝ (beurlingAhlfors V 2) z I) / 2
    exact ((measurable_fderiv_apply_const ℝ _ 1).add
      (measurable_const.mul (measurable_fderiv_apply_const ℝ _ I))).div_const 2
  refine Integrable.bdd_mul (c := C) hφ hm.aestronglyMeasurable ?_
  exact (ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet).2 (Eventually.of_forall fun z hz => hC z hz)

/-- Helper for `thm18_3` (§18.3, S10). For `ψ` holomorphic on a half-plane `Im z > −δ`, the semicircle integral
equals the integral along `[a, b]` (a primitive on a disc containing the closed half-disc). -/
theorem gl18_L_eq_segment {a b : ℝ} (hab : a < b) {ψ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | -δ < z.im}) :
    lFunctionalAB a b ψ = π * ∫ x in a..b, ψ x * (((x : ℂ) - a) * ((x : ℂ) - b) / (a - b)) := by
  set r : ℝ := (b - a) / 2 with hr
  set m : ℝ := (a + b) / 2 with hm
  have hr0 : 0 < r := by rw [hr]; linarith
  set f : ℂ → ℂ := fun z => ψ z * ((z - a) * (z - b) / (a - b)) with hf
  -- a disc inside `Im > −δ` containing the closed half-disc of radius `r` about `m`
  set T : ℝ := r ^ 2 / δ + r with hT
  have hT0 : 0 < T := by positivity
  set c : ℂ := (m : ℂ) + (T : ℂ) * I with hc
  set ρ : ℝ := T + δ / 2 with hρ
  have hcre : c.re = m := by simp [hc]
  have hcim : c.im = T := by simp [hc]
  have hball : ball c ρ ⊆ {z : ℂ | -δ < z.im} := by
    intro z hz
    have h1 : |z.im - T| < ρ := by
      have := (Complex.abs_im_le_norm (z - c)).trans_lt (mem_ball_iff_norm.1 hz)
      rwa [Complex.sub_im, hcim] at this
    show -δ < z.im
    have := (abs_lt.1 h1).1
    rw [hρ] at this
    linarith
  have hmem : ∀ z : ℂ, ‖z - m‖ ≤ r → 0 ≤ z.im → z ∈ ball c ρ := by
    intro z hz1 hz2
    rw [mem_ball_iff_norm]
    have hzr : (z - m).re ^ 2 + (z - m).im ^ 2 ≤ r ^ 2 := by
      have := sq_le_sq' (by linarith [norm_nonneg (z - m)]) hz1
      rw [Complex.sq_norm, Complex.normSq_apply] at this
      nlinarith [this]
    have him : z.im ≤ r := by
      have h1 : (z - m).im = z.im := by simp
      nlinarith [sq_nonneg (z - m).re]
    have hlt : ‖z - c‖ ^ 2 < ρ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have e1 : (z - c).re = (z - m).re := by simp [hcre]
      have e2 : (z - c).im = z.im - T := by simp [hcim]
      have e3 : (z - m).im = z.im := by simp
      rw [e1, e2]
      rw [e3] at hzr
      have hTδ : r ^ 2 < T * δ := by
        rw [hT, add_mul, div_mul_cancel₀ _ hδ.ne']
        nlinarith
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt
  have hfd : DifferentiableOn ℂ f (ball c ρ) :=
    (hψ.mono hball).mul (by fun_prop : Differentiable ℂ fun z : ℂ => (z - a) * (z - b) / (a - b)).differentiableOn
  obtain ⟨G, hG⟩ := hfd.isExactOn_ball
  -- the segment `[a, b]`
  have hsegB : ∀ x ∈ Set.uIcc a b, (x : ℂ) ∈ ball c ρ := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    refine hmem _ ?_ (by simp)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hseg : ∫ x in a..b, f x = G b - G a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => (hG _ (hsegB x hx)).comp_ofReal) ?_
    refine ContinuousOn.intervalIntegrable ?_
    exact hfd.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => hsegB x hx
  -- the semicircle `w(θ) = m + r e^{i(π − θ)}`
  set w : ℝ → ℂ := fun θ => ((a : ℂ) + b) / 2 + ((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ)) with hw
  have hwd : ∀ θ : ℝ, HasDerivAt w (-(I * (((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ))))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => I * ((π : ℂ) - θ)) (I * (-1)) θ :=
      ((hasDerivAt_id θ).ofReal_comp.const_sub (π : ℂ)).const_mul I |>.congr_deriv (by simp)
    have h2 := (h1.cexp.const_mul (((b : ℂ) - a) / 2)).const_add (((a : ℂ) + b) / 2)
    convert h2 using 1
    ring
  have hwB : ∀ θ ∈ Set.uIcc 0 π, w θ ∈ ball c ρ := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have e : w θ - m = (r : ℂ) * Complex.exp (I * (π - θ)) := by
      simp only [hw, hr, hm]
      push_cast
      ring
    refine hmem _ ?_ ?_
    · rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        show I * ((π : ℂ) - θ) = ((π - θ : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
    · have : (w θ).im = r * Real.sin (π - θ) := by
        have h1 : (w θ).im = (w θ - m).im := by simp
        rw [h1, e, show I * ((π : ℂ) - θ) = ((π - θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_mul_I]
        simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.add_im, Complex.add_re, Complex.I_re, Complex.I_im, Complex.mul_re]
        ring
      rw [this]
      exact mul_nonneg hr0.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.2]) (by linarith [hθ.1]))
  have harc : ∫ θ in (0 : ℝ)..π, f (w θ) * (-(I * (((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ))))) =
      G (w π) - G (w 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => (hG _ (hwB θ hθ)).comp θ (hwd θ)) ?_
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (hfd.continuousOn.comp (fun θ _ => (hwd θ).continuousAt.continuousWithinAt)
      fun θ hθ => hwB θ hθ) ?_
    exact Continuous.continuousOn (by fun_prop)
  have hwπ : w π = b := by
    simp only [hw, sub_self, mul_zero, Complex.exp_zero, mul_one]
    ring
  have hw0 : w 0 = a := by
    simp only [hw, Complex.ofReal_zero, sub_zero]
    rw [show I * (π : ℂ) = π * I by ring, Complex.exp_pi_mul_I]
    ring
  unfold lFunctionalAB
  rw [show (∫ x in a..b, ψ x * (((x : ℂ) - a) * ((x : ℂ) - b) / (a - b))) = ∫ x in a..b, f x from rfl, hseg]
  congr 1
  rw [show G (b : ℂ) - G a = G (w π) - G (w 0) by rw [hwπ, hw0], ← harc]

/-- Helper for `thm18_3` (§18.3, S7). The pointwise inequality behind Scheffé's lemma:
`‖u − v‖ ≤ (‖u‖ − ‖v‖) + 2 min(‖u − v‖, ‖v‖)`. -/
theorem gl18_scheffe_pt (u v : ℂ) : ‖u - v‖ ≤ (‖u‖ - ‖v‖) + 2 * min ‖u - v‖ ‖v‖ := by
  have h1 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
    calc ‖v‖ = ‖u - (u - v)‖ := by ring_nf
      _ ≤ ‖u‖ + ‖u - v‖ := norm_sub_le _ _
  have h2 : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
  rcases le_total ‖u - v‖ ‖v‖ with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- Helper for `thm18_3` (§18.3, S7). `|1 − iεz| ≥ (ε/3)(1 + |z|)` on `ℍ̄` for `0 < ε ≤ 1`, and `|1 − iεz| ≥ 1`. -/
theorem gl18_approx_factor {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ} (hz : 0 ≤ z.im) :
    1 ≤ ‖1 - I * ε * z‖ ∧ ε / 3 * (1 + ‖z‖) ≤ ‖1 - I * ε * z‖ := by
  have hre : (1 - I * ε * z).re = 1 + ε * z.im := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.mul_im]
    ring
  have h1 : 1 ≤ ‖1 - I * ε * z‖ := by
    have := Complex.re_le_norm (1 - I * ε * z)
    rw [hre] at this
    nlinarith
  have h2 : ε * ‖z‖ - 1 ≤ ‖1 - I * ε * z‖ := by
    have := norm_sub_norm_le (I * ε * z) 1
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_one,
      one_mul, norm_sub_rev] at this
    linarith
  refine ⟨h1, ?_⟩
  by_cases hz2 : ε * ‖z‖ ≤ 2
  · nlinarith
  · push Not at hz2
    nlinarith

/-- Helper for `thm18_3` (§18.3, S7). Every `φ ∈ A(ℍ)` is an `L¹(ℍ)`-limit of functions holomorphic on some
`Im z > −δ` and `O(|z|⁻⁴)` on `ℍ̄` (`ψ_n(z) = φ(z + i/n)(1 − iz/n)⁻⁴`; Scheffé). -/
theorem gl18_approx {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceOpen (toExt upperHalf)) :
    ∃ ψ : ℕ → ℂ → ℂ, (∀ n, ∃ δ > 0, DifferentiableOn ℂ (ψ n) {z : ℂ | -δ < z.im}) ∧
      (∀ n, ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖ψ n z‖ ≤ C / (1 + ‖z‖) ^ 4) ∧ (∀ n, IntegrableOn (ψ n) upperHalf) ∧
      Tendsto (fun n => ∫ z in upperHalf, ‖ψ n z - φ z‖) atTop (𝓝 0) := by
  obtain ⟨hi, hd⟩ := gl18_aSpace_upperHalf hφ
  have hzero : ∀ z : ℂ, z ∉ upperHalf → φ z = 0 := fun z hz => hφ.2 z fun h => by
    obtain ⟨w, hw, hwz⟩ := h
    rw [OnePoint.coe_eq_coe.1 hwz] at hw
    exact hz hw
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
    simp only [hεdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  set ψ : ℕ → ℂ → ℂ := fun n z => φ (z + (ε n : ℂ) * I) * ((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹ with hψ
  -- the shift `z + iε` maps `Im z > −ε` into `ℍ`
  have hshift : ∀ n z, -ε n < z.im → z + (ε n : ℂ) * I ∈ upperHalf := fun n z hz => by
    show 0 < (z + (ε n : ℂ) * I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    linarith
  have hfac : ∀ n z, -ε n < z.im → 1 - I * (ε n : ℂ) * z ≠ 0 := fun n z hz h => by
    have him : (1 - I * (ε n : ℂ) * z).re = 1 + ε n * z.im := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.mul_im]
      ring
    rw [h, Complex.zero_re] at him
    have h1 : ε n * z.im > -(ε n * ε n) := by nlinarith [hε0 n]
    nlinarith [hε1 n, hε0 n]
  -- the mean value bound for `φ` on `Im ≥ ε`
  have hint : Integrable fun z => ‖φ z‖ := hi.norm
  have hmv : ∀ c : ℂ, ∀ s : ℝ, 0 < s → s < c.im → π * s ^ 2 * ‖φ c‖ ≤ ∫ z, ‖φ z‖ := by
    intro c s hs hsc
    have hsub : closedBall c s ⊆ upperHalf := fun z hz => by
      have h1 := (Complex.abs_im_le_norm (z - c)).trans (mem_closedBall_iff_norm.1 hz)
      rw [Complex.sub_im] at h1
      show 0 < z.im
      linarith [neg_abs_le (z.im - c.im)]
    have h := LiZhongQC.h36p_meanvalue hd hs hsub
    have h2 : ∫⁻ z in ball c s, ENNReal.ofReal ‖φ z‖ ≤ ENNReal.ofReal (∫ z, ‖φ z‖) := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hi]
      refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
      simp only [ofReal_norm]
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => norm_nonneg _)).1 (h.trans h2)
  have hdiffψ : ∀ n, DifferentiableOn ℂ (ψ n) {z : ℂ | -ε n < z.im} := by
    intro n z hz
    have hz' : -ε n < z.im := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun z => φ (z + (ε n : ℂ) * I)) z :=
      (hd.differentiableAt (hU.mem_nhds (hshift n z hz'))).comp z (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹) z :=
      (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).pow 4).inv
        (pow_ne_zero 4 (hfac n z hz'))
    exact h1.mul h2
  have hfac1 : ∀ n, ∀ z : ℂ, 0 ≤ z.im → ‖((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹‖ ≤ 1 := by
    intro n z hz
    obtain ⟨hf1, -⟩ := gl18_approx_factor (hε0 n) ((hε1 n).trans (by norm_num)) hz
    rw [norm_inv, norm_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hf1)
  have hbdψ : ∀ n, ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖ψ n z‖ ≤ C / (1 + ‖z‖) ^ 4 := by
    intro n
    refine ⟨(∫ z, ‖φ z‖) / (π * (ε n / 2) ^ 2) * (3 / ε n) ^ 4, fun z hz => ?_⟩
    obtain ⟨-, hf2⟩ := gl18_approx_factor (hε0 n) ((hε1 n).trans (by norm_num)) hz
    have hc : (ε n / 2) < (z + (ε n : ℂ) * I).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one]
      linarith [hε0 n]
    have h1 := hmv _ _ (by positivity) hc
    have hφb : ‖φ (z + (ε n : ℂ) * I)‖ ≤ (∫ z, ‖φ z‖) / (π * (ε n / 2) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hpos : 0 < ε n / 3 * (1 + ‖z‖) := by positivity
    have hfb : ‖((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹‖ ≤ (3 / ε n) ^ 4 / (1 + ‖z‖) ^ 4 := by
      rw [norm_inv, norm_pow, ← one_div, div_le_div_iff₀ (pow_pos (hpos.trans_le hf2) 4) (by positivity),
        one_mul, ← mul_pow]
      have e : 1 + ‖z‖ = 3 / ε n * (ε n / 3 * (1 + ‖z‖)) := by
        have := (hε0 n).ne'
        field_simp
      calc (1 + ‖z‖) ^ 4 = (3 / ε n * (ε n / 3 * (1 + ‖z‖))) ^ 4 := by rw [← e]
        _ ≤ (3 / ε n * ‖1 - I * ↑(ε n) * z‖) ^ 4 := by gcongr
    calc ‖ψ n z‖ = ‖φ (z + (ε n : ℂ) * I)‖ * ‖((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹‖ := by rw [hψ, norm_mul]
      _ ≤ (∫ z, ‖φ z‖) / (π * (ε n / 2) ^ 2) * ((3 / ε n) ^ 4 / (1 + ‖z‖) ^ 4) := by gcongr
      _ = _ := by ring
  have hintψ : ∀ n, IntegrableOn (ψ n) upperHalf := by
    intro n
    obtain ⟨C, hC⟩ := hbdψ n
    have hm : AEStronglyMeasurable (ψ n) (volume.restrict upperHalf) :=
      ((hdiffψ n).continuousOn.mono fun z (hz : 0 < z.im) => by
        show -ε n < z.im
        linarith [hε0 n]).aestronglyMeasurable hU.measurableSet
    have hg : Integrable (fun z : ℂ => C * (1 + ‖z‖) ^ (-(4 : ℝ))) :=
      (integrable_one_add_norm (by simp; norm_num)).const_mul C
    refine Integrable.mono' hg.integrableOn hm
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun z hz => ?_))
    refine (hC z (le_of_lt hz)).trans (le_of_eq ?_)
    rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
    norm_cast
  -- pointwise convergence on `ℍ`
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp [hεdef]
    ring
  have hpt : ∀ z ∈ upperHalf, Tendsto (fun n => ψ n z) atTop (𝓝 (φ z)) := by
    intro z hz
    have hεc : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp hεlim
      rw [Complex.ofReal_zero] at this
      exact this
    have h1 : Tendsto (fun n => z + (ε n : ℂ) * I) atTop (𝓝 z) := by
      simpa using tendsto_const_nhds.add (hεc.mul_const I)
    have h2 := (hd.continuousOn.continuousAt (hU.mem_nhds hz)).tendsto.comp h1
    have h3 : Tendsto (fun n => ((1 - I * (ε n : ℂ) * z) ^ 4)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℂ))).sub ((tendsto_const_nhds (x := I)).mul hεc |>.mul
        (tendsto_const_nhds (x := z)))).pow 4 |>.inv₀ (by simp)
      simpa using this
    simpa using h2.mul h3
  -- `∫_ℍ |ψ_n| ≤ ∫_ℍ |φ|`: the shift preserves the integral and `φ = 0` off `ℍ`
  have hnorm : ∀ n, ∫ z in upperHalf, ‖ψ n z‖ ≤ ∫ z in upperHalf, ‖φ z‖ := by
    intro n
    have h1 : ∫ z in upperHalf, ‖ψ n z‖ ≤ ∫ z in upperHalf, ‖φ (z + (ε n : ℂ) * I)‖ := by
      refine setIntegral_mono_on (hintψ n).norm (hint.comp_add_right _).integrableOn hU.measurableSet
        fun z hz => ?_
      rw [hψ, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hfac1 n z (le_of_lt hz))
    have h2 : ∫ z in upperHalf, ‖φ (z + (ε n : ℂ) * I)‖ ≤ ∫ z, ‖φ (z + (ε n : ℂ) * I)‖ :=
      setIntegral_le_integral (hint.comp_add_right _) (Eventually.of_forall fun _ => norm_nonneg _)
    have h3 : ∫ z, ‖φ (z + (ε n : ℂ) * I)‖ = ∫ z in upperHalf, ‖φ z‖ := by
      rw [integral_add_right_eq_self (fun z => ‖φ z‖), setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro z hz
      rw [hzero z hz, norm_zero]
    linarith
  -- Scheffé
  have hmin : Tendsto (fun n => ∫ z in upperHalf, min ‖ψ n z - φ z‖ ‖φ z‖) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict upperHalf)
      (F := fun n z => min ‖ψ n z - φ z‖ ‖φ z‖) (f := fun _ => (0 : ℝ)) (fun z => ‖φ z‖)
      (fun n => (((hintψ n).sub hi.integrableOn).norm.aestronglyMeasurable.inf hint.integrableOn.aestronglyMeasurable))
      hint.integrableOn (fun n => Eventually.of_forall fun z => ?_)
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun z hz => ?_))
    · simpa using this
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (norm_nonneg _))]
      exact min_le_right _ _
    · have h1 : Tendsto (fun n => ‖ψ n z - φ z‖) atTop (𝓝 0) := by
        simpa using ((hpt z hz).sub_const (φ z)).norm
      have h2 := h1.min (tendsto_const_nhds (x := ‖φ z‖))
      simpa using h2
  refine ⟨ψ, fun n => ⟨ε n, hε0 n, hdiffψ n⟩, hbdψ, hintψ, ?_⟩
  refine squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hmin.const_mul 2)
  have hi1 := ((hintψ n).sub hi.integrableOn).norm
  have hi2 : IntegrableOn (fun z => min ‖ψ n z - φ z‖ ‖φ z‖) upperHalf :=
    Integrable.mono' hint.integrableOn
      (((hintψ n).sub hi.integrableOn).norm.aestronglyMeasurable.inf hint.integrableOn.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (norm_nonneg _))]
        exact min_le_right _ _)
  calc ∫ z in upperHalf, ‖ψ n z - φ z‖
      ≤ ∫ z in upperHalf, ((‖ψ n z‖ - ‖φ z‖) + 2 * min ‖ψ n z - φ z‖ ‖φ z‖) :=
        setIntegral_mono_on hi1 (((hintψ n).norm.sub hint.integrableOn).add (hi2.const_mul 2))
          hU.measurableSet fun z _ => gl18_scheffe_pt _ _
    _ = (∫ z in upperHalf, ‖ψ n z‖) - (∫ z in upperHalf, ‖φ z‖) +
          2 * ∫ z in upperHalf, min ‖ψ n z - φ z‖ ‖φ z‖ := by
        rw [integral_add (f := fun z => ‖ψ n z‖ - ‖φ z‖) (g := fun z => 2 * min ‖ψ n z - φ z‖ ‖φ z‖)
          ((hintψ n).norm.sub hint.integrableOn) (hi2.const_mul 2),
          integral_sub (f := fun z => ‖ψ n z‖) (g := fun z => ‖φ z‖) (hintψ n).norm hint.integrableOn,
          integral_const_mul]
    _ ≤ 2 * ∫ z in upperHalf, min ‖ψ n z - φ z‖ ‖φ z‖ := by linarith [hnorm n]

/-- Helper for `thm18_3` (§18.3, S8). The set integral over a rectangle is the iterated integral. -/
theorem gl18_rect_integral {g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hg : IntegrableOn g (Icc x₁ x₂ ×ℂ Icc y₁ y₂)) :
    ∫ z in Icc x₁ x₂ ×ℂ Icc y₁ y₂, g z = ∫ x in x₁..x₂, ∫ y in y₁..y₂, g (x + y * I) := by
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' (Icc x₁ x₂ ×ℂ Icc y₁ y₂) = Icc x₁ x₂ ×ˢ Icc y₁ y₂ := by
    ext p
    simp only [Set.mem_preimage, Complex.mem_reProdIm, Set.mem_prod, Complex.measurableEquivRealProd_symm_apply]
  have hg' : IntegrableOn (fun p : ℝ × ℝ => g (Complex.measurableEquivRealProd.symm p))
      (Icc x₁ x₂ ×ˢ Icc y₁ y₂) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hpre]
    exact (hmp.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _)).2 hg
  rw [← hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _), hpre, Measure.volume_eq_prod,
    setIntegral_prod _ hg', intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [intervalIntegral.integral_of_le hy, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  simp only [Complex.measurableEquivRealProd_symm_apply]
  rw [Complex.mk_eq_add_mul_I]

/-- Helper for `thm18_3` (§18.3, S8). Green's formula on `ℍ`: `∬_ℍ ∂̄f = (1/2i) ∫_ℝ f` for `f` continuous on `ℍ̄`,
real differentiable on `ℍ`, with `∂̄f ∈ L¹(ℍ)` and `f = O(|z|⁻³)` (rectangles `[−R, R] × [δ, R]`,
`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, `δ → 0`, `R → ∞`). -/
theorem gl18_green {f : ℂ → ℂ} (hc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hd : DifferentiableOn ℝ f upperHalf)
    (hi : IntegrableOn (dzbar f) upperHalf) {C : ℝ} (hdec : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ C / (1 + ‖z‖) ^ 3) :
    ∫ z in upperHalf, dzbar f z = (2 * I)⁻¹ * ∫ x : ℝ, f x := by
  set S := {z : ℂ | 0 ≤ z.im} with hS
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hdec 0 (by simp))
    have h1 : (0 : ℝ) < (1 + ‖(0 : ℂ)‖) ^ 3 := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 h1)
  set R : ℕ → ℝ := fun n => (n : ℝ) + 2 with hR
  have hR2 : ∀ n, 2 ≤ R n := fun n => by simp [hR]
  have hR0 : ∀ n, 0 < R n := fun n => by linarith [hR2 n]
  have hRinv : ∀ n, 1 / R n < R n := fun n => by
    rw [div_lt_iff₀ (hR0 n)]
    nlinarith [hR2 n]
  set Q : ℕ → Set ℂ := fun n => Icc (-R n) (R n) ×ℂ Icc (1 / R n) (R n) with hQ
  have hQH : ∀ n, Q n ⊆ upperHalf := fun n z hz => by
    have : 1 / R n ≤ z.im := hz.2.1
    show 0 < z.im
    linarith [one_div_pos.2 (hR0 n)]
  have hQm : ∀ n, MeasurableSet (Q n) := fun n =>
    (measurableSet_Icc.preimage Complex.measurable_re).inter (measurableSet_Icc.preimage Complex.measurable_im)
  set g : ℂ → ℂ := fun z => 2 * I * dzbar f z with hg
  have hgi : IntegrableOn g upperHalf := hi.const_mul (2 * I)
  -- the rectangle identity
  have hrect : ∀ n, ((∫ x in -R n..R n, f (x + (1 / R n : ℝ) * I)) - (∫ x in -R n..R n, f (x + R n * I))) +
      I • (∫ y in 1 / R n..R n, f ((R n : ℝ) + y * I)) - I • (∫ y in 1 / R n..R n, f ((-R n : ℝ) + y * I)) =
      ∫ z in upperHalf, (Q n).indicator g z := by
    intro n
    set z₁ : ℂ := ⟨-R n, 1 / R n⟩
    set z₂ : ℂ := ⟨R n, R n⟩
    have hle1 : -R n ≤ R n := by linarith [hR0 n]
    have hle2 : 1 / R n ≤ R n := (hRinv n).le
    have hrectS : Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im = Q n := by
      show Set.uIcc (-R n) (R n) ×ℂ Set.uIcc (1 / R n) (R n) = _
      rw [Set.uIcc_of_le hle1, Set.uIcc_of_le hle2]
    have hHd : ∀ z ∈ Ioo (min z₁.re z₂.re) (max z₁.re z₂.re) ×ℂ Ioo (min z₁.im z₂.im) (max z₁.im z₂.im) \ ∅,
        HasFDerivAt f (fderiv ℝ f z) z := by
      intro z hz
      have hmin : (0 : ℝ) < min z₁.im z₂.im := lt_min (one_div_pos.2 (hR0 n)) (hR0 n)
      have hzQ : z ∈ upperHalf := hmin.trans hz.1.2.1
      exact (hd.differentiableAt (LiZhongQC.isOpen_upperHalf.mem_nhds hzQ)).hasFDerivAt
    have hHi : IntegrableOn (fun z => I • fderiv ℝ f z 1 - fderiv ℝ f z I)
        (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) := by
      rw [hrectS]
      refine (hgi.mono_set (hQH n)).congr_fun (fun z _ => ?_) (hQm n)
      simp only [hg, dzbar, smul_eq_mul]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hHc : ContinuousOn f (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) := by
      rw [hrectS]
      exact hc.mono fun z hz => show 0 ≤ z.im from le_of_lt (hQH n hz)
    have h := Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv ℝ f) z₁ z₂ ∅
      Set.countable_empty hHc hHd hHi
    refine h.trans ?_
    rw [setIntegral_indicator (hQm n), Set.inter_eq_right.2 (hQH n)]
    simp only [hQ]
    rw [gl18_rect_integral hle1 hle2 (hgi.mono_set (hQH n))]
    refine intervalIntegral.integral_congr fun x _ => intervalIntegral.integral_congr fun y _ => ?_
    simp only [hg, dzbar, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  -- the area term converges to `∫_ℍ 2i ∂̄f`
  have hA : Tendsto (fun n => ∫ z in upperHalf, (Q n).indicator g z) atTop (𝓝 (∫ z in upperHalf, g z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖g z‖)
      (fun n => (hgi.aestronglyMeasurable.indicator (hQm n))) hgi.norm (fun n => ?_) ?_
    · exact Eventually.of_forall fun z => norm_indicator_le_norm_self _ _
    · refine (ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet).2 (Eventually.of_forall fun z hz => ?_)
      have hz' : 0 < z.im := hz
      refine tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ n : ℕ in atTop, z ∈ Q n := by
        have h1 : Tendsto (fun n : ℕ => 1 / R n) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          refine this.congr fun n => ?_
          simp [hR]
          ring
        have h2 : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        filter_upwards [h1.eventually (gt_mem_nhds hz'), h2.eventually_ge_atTop (|z.re|),
          h2.eventually_ge_atTop z.im] with n hn1 hn2 hn3
        exact ⟨⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩, hn1.le, hn3⟩
      filter_upwards [hev] with n hn
      rw [Set.indicator_of_mem hn]
  -- the decay bound along horizontal and vertical lines
  have hdx : ∀ x y : ℝ, 0 ≤ y → ‖f (x + y * I)‖ ≤ C / (1 + |x|) ^ 3 := fun x y hy => by
    refine (hdec _ (by simpa using hy)).trans ?_
    gcongr
    have := Complex.abs_re_le_norm ((x : ℂ) + y * I)
    simpa using this
  have hdR : ∀ z : ℂ, 0 ≤ z.im → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ‖z‖ → ‖f z‖ ≤ C / (1 + ρ) ^ 3 := fun z hz ρ hρ hρz =>
    (hdec z hz).trans (by gcongr)
  -- the bottom edge converges to `∫_ℝ f`
  have hint : Integrable (fun x : ℝ => C / (1 + |x|) ^ 3) := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by norm_num)).const_mul C
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
    norm_cast
  have hBot : Tendsto (fun n => ∫ x in -R n..R n, f (x + (1 / R n : ℝ) * I)) atTop (𝓝 (∫ x : ℝ, f x)) := by
    have e : ∀ n, ∫ x in -R n..R n, f (x + (1 / R n : ℝ) * I) =
        ∫ x : ℝ, (Ioc (-R n) (R n)).indicator (fun x : ℝ => f (x + (1 / R n : ℝ) * I)) x := fun n => by
      rw [intervalIntegral.integral_of_le (by linarith [hR0 n]), integral_indicator measurableSet_Ioc]
    simp only [e]
    refine tendsto_integral_of_dominated_convergence (fun x => C / (1 + |x|) ^ 3) (fun n => ?_) hint
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have hcont : Continuous fun x : ℝ => f (x + (1 / R n : ℝ) * I) :=
        hc.comp_continuous (by fun_prop) fun x => by
          show 0 ≤ ((x : ℂ) + (1 / R n : ℝ) * I).im
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, zero_add]
          have := hR0 n
          positivity
      exact hcont.aestronglyMeasurable.indicator measurableSet_Ioc
    · rw [norm_indicator_eq_indicator_norm]
      refine (Set.indicator_le_self' (fun _ _ => norm_nonneg _) x).trans ?_
      exact hdx x _ (one_div_pos.2 (hR0 n)).le
    · have h1 : Tendsto (fun n : ℕ => 1 / R n) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp [hR]
        ring
      have h2 : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have hpt : Tendsto (fun n : ℕ => (x : ℂ) + (1 / R n : ℝ) * I) atTop (𝓝[S] (x : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I
          have h3 := (tendsto_const_nhds (x := (x : ℂ))).add this
          simpa using h3
        · show 0 ≤ ((x : ℂ) + (1 / R n : ℝ) * I).im
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, zero_add]
          have := hR0 n
          positivity
      have hlim := (hc (x : ℂ) (by simp [hS])).tendsto.comp hpt
      refine hlim.congr' ?_
      filter_upwards [h2.eventually_gt_atTop (|x|)] with n hn
      rw [Set.indicator_of_mem (show x ∈ Ioc (-R n) (R n) from
        ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩)]
      rfl
  -- the top edge and the two sides tend to `0`
  have hCR : Tendsto (fun n => C / R n) atTop (𝓝 0) := by
    have h2 : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact h2.const_div_atTop C |>.congr fun n => rfl
  have hbd : ∀ n, C / (1 + R n) ^ 3 * (2 * R n) ≤ 2 * (C / R n) := fun n => by
    have h0 := hR0 n
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div,
      le_div_iff₀ h0]
    nlinarith [mul_nonneg hC0 h0.le, mul_nonneg (mul_nonneg hC0 h0.le) h0.le]
  have hTop : Tendsto (fun n => ∫ x in -R n..R n, f (x + R n * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hCR.const_mul 2)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R n) (b := R n)
      (C := C / (1 + R n) ^ 3) (f := fun x : ℝ => f (x + R n * I)) fun x _ => by
        refine hdR _ (by simpa using (hR0 n).le) _ (hR0 n).le ?_
        have := Complex.abs_im_le_norm ((x : ℂ) + R n * I)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
        rwa [abs_of_pos (hR0 n)] at this
    refine this.trans ?_
    rw [show |R n - -R n| = 2 * R n by rw [sub_neg_eq_add, abs_of_pos (by linarith [hR0 n])]; ring]
    exact hbd n
  have hSide : ∀ c : ℕ → ℝ, (∀ n, |c n| = R n) →
      Tendsto (fun n => ∫ y in 1 / R n..R n, f ((c n : ℝ) + y * I)) atTop (𝓝 0) := by
    intro c hcR
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hCR.const_mul 2)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 / R n) (b := R n)
      (C := C / (1 + R n) ^ 3) (f := fun y : ℝ => f ((c n : ℝ) + y * I)) fun y hy => by
        rw [Set.uIoc_of_le (hRinv n).le] at hy
        have hy0 : 0 ≤ y := (one_div_pos.2 (hR0 n)).le.trans hy.1.le
        refine hdR _ (by simpa using hy0) _ (hR0 n).le ?_
        have := Complex.abs_re_le_norm (((c n : ℝ) : ℂ) + y * I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
          Complex.I_im, mul_zero, mul_one, sub_self, add_zero, hcR n] at this
        exact this
    refine this.trans ?_
    have h1 : |R n - 1 / R n| ≤ 2 * R n := by
      rw [abs_of_pos (sub_pos.2 (hRinv n))]
      linarith [one_div_pos.2 (hR0 n), hR0 n]
    calc C / (1 + R n) ^ 3 * |R n - 1 / R n| ≤ C / (1 + R n) ^ 3 * (2 * R n) := by gcongr
      _ ≤ 2 * (C / R n) := hbd n
  have hS1 := hSide R fun n => abs_of_pos (hR0 n)
  have hS2 := hSide (fun n => -R n) fun n => by rw [abs_neg, abs_of_pos (hR0 n)]
  -- combine
  have hL := ((hBot.sub hTop).add (hS1.const_smul I)).sub (hS2.const_smul I)
  rw [sub_zero, smul_zero, add_zero, sub_zero] at hL
  have hEq : ∫ x : ℝ, f x = ∫ z in upperHalf, g z :=
    tendsto_nhds_unique (hL.congr fun n => hrect n) hA
  rw [hg, integral_const_mul] at hEq
  rw [hEq, ← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]

/-- Helper for `thm18_3` (§18.3, S11). A function continuous on `ℍ` with `|ψ| ≤ C/(1 + |z|)⁴` is integrable on `ℍ`. -/
theorem gl18_integrableOn_of_decay {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ upperHalf) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖ψ z‖ ≤ C / (1 + ‖z‖) ^ 4) : IntegrableOn ψ upperHalf := by
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  have hg : Integrable (fun z : ℂ => C * (1 + ‖z‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul C
  refine Integrable.mono' hg.integrableOn (hψ.aestronglyMeasurable hU.measurableSet)
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun z hz => ?_))
  refine (hC z (le_of_lt hz)).trans (le_of_eq ?_)
  rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
  norm_cast

/-- Helper for `thm18_3` (§18.3, S11). On `ℝ` the Beurling–Ahlfors extension is the field itself. -/
theorem gl18_ba_real (h : ℝ → ℝ) (x : ℝ) : beurlingAhlfors h 2 x = h x := by
  simp only [beurlingAhlfors, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, sub_zero, sub_self,
    intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

/-- Helper for `thm18_3` (§18.3, S11). The Green step: for a continuous field `V` of linear growth with bounded
`∂̄ ex₂(V)` and a nice `ψ`, `∬_ℍ ∂̄ex₂(V) ψ = (1/2i) ∫_ℝ V ψ`. -/
theorem gl18_pairing_green {V : ℝ → ℝ} (hV : Continuous V) {K : ℝ} (hK : ∀ t, |V t| ≤ K * (1 + |t|)) {M : ℝ}
    (hM : ∀ z : ℂ, 0 < z.im → ‖dzbar (beurlingAhlfors V 2) z‖ ≤ M) {ψ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | -δ < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖ψ z‖ ≤ C / (1 + ‖z‖) ^ 4) :
    ∫ z in upperHalf, dzbar (beurlingAhlfors V 2) z * ψ z = (2 * I)⁻¹ * ∫ x : ℝ, (V x : ℂ) * ψ x := by
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  have hHδ : upperHalf ⊆ {z : ℂ | -δ < z.im} := fun z (hz : 0 < z.im) => by
    show -δ < z.im
    linarith
  have hSδ : {z : ℂ | 0 ≤ z.im} ⊆ {z : ℂ | -δ < z.im} := fun z (hz : 0 ≤ z.im) => by
    show -δ < z.im
    linarith
  have hδo : IsOpen {z : ℂ | -δ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hψint : IntegrableOn ψ upperHalf := gl18_integrableOn_of_decay (hψ.continuousOn.mono hHδ) hC
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hK 0)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0 (by simp))
    simpa using this
  set f : ℂ → ℂ := fun z => beurlingAhlfors V 2 z * ψ z with hf
  have hdz : ∀ z ∈ upperHalf, dzbar f z = dzbar (beurlingAhlfors V 2) z * ψ z := by
    intro z hz
    have h1 : DifferentiableAt ℝ (beurlingAhlfors V 2) z :=
      (gl18_ba_differentiableOn hV).differentiableAt (hU.mem_nhds hz)
    have h2 : DifferentiableAt ℂ ψ z := hψ.differentiableAt (hδo.mem_nhds (hHδ hz))
    rw [hf, LiZhongQC.dzbar_mul h1 (h2.restrictScalars ℝ), (LiZhongQC.cauchyRiemann_iff.1 h2).2, mul_zero,
      zero_add, mul_comm]
  have hG := gl18_green (f := f)
    ((LiZhongQC.ba_f1h_continuous hV 2).continuousOn.mul (hψ.continuousOn.mono hSδ))
    ((gl18_ba_differentiableOn hV).mul ((hψ.restrictScalars ℝ).mono hHδ))
    ((gl18_pairing_integrable hM hψint).congr_fun (fun z hz => (hdz z hz).symm) hU.measurableSet)
    (C := 6 * K * C) fun z hz => by
      rw [hf, norm_mul]
      calc ‖beurlingAhlfors V 2 z‖ * ‖ψ z‖ ≤ 6 * K * (1 + ‖z‖) * (C / (1 + ‖z‖) ^ 4) :=
            mul_le_mul (gl18_ba_growth hV hK z hz) (hC z hz) (norm_nonneg _) (by positivity)
        _ = 6 * K * C / (1 + ‖z‖) ^ 3 := by
            field_simp
  rw [setIntegral_congr_fun hU.measurableSet hdz] at hG
  rw [hG]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hf, gl18_ba_real]

/-- Helper for `thm18_3` (§18.3, S11). `∫_ℝ E_ab ψ = ∫_a^b ψ (x − a)(x − b)/(a − b)`. -/
theorem gl18_integral_E {a b : ℝ} (hab : a < b) (ψ : ℂ → ℂ) :
    ∫ x : ℝ, (earthquakeVF a b x : ℂ) * ψ x = ∫ x in a..b, ψ x * (((x : ℂ) - a) * ((x : ℂ) - b) / (a - b)) := by
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
  · refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    simp only [earthquakeVF, ite_eq_left (show a ≤ x ∧ x ≤ b from hx)]
    push_cast
    ring
  · intro x hx
    simp only [earthquakeVF]
    rw [ite_eq_right (show ¬(a ≤ x ∧ x ≤ b) from hx), Complex.ofReal_zero, zero_mul]

/-- Helper for `thm18_3` (§18.3, S11). The two pairings for nice `ψ`: Green (S8) with `f = ex(V) ψ` reduces them to
`(1/2i) ∫_ℝ V ψ`; Green with `f = F ψ` (holomorphic) gives `∫_ℝ (B − iπE) ψ = 0`; and `∫_ℝ E ψ = L(ψ)/π` (S10). -/
theorem gl18_identity_nice {a b : ℝ} (hab : a < b) {ψ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | -δ < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖ψ z‖ ≤ C / (1 + ‖z‖) ^ 4) :
    ∫ z in upperHalf, dzbar (beurlingAhlfors (bendVF a b) 2) z * ψ z = lFunctionalAB a b ψ / 2 ∧
      ∫ z in upperHalf, dzbar (beurlingAhlfors (earthquakeVF a b) 2) z * ψ z =
        -(I * lFunctionalAB a b ψ) / (2 * π) := by
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  have hHδ : upperHalf ⊆ {z : ℂ | -δ < z.im} := fun z (hz : 0 < z.im) => by
    show -δ < z.im
    linarith
  have hSδ : {z : ℂ | 0 ≤ z.im} ⊆ {z : ℂ | -δ < z.im} := fun z (hz : 0 ≤ z.im) => by
    show -δ < z.im
    linarith
  have hδo : IsOpen {z : ℂ | -δ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0 (by simp))
    simpa using this
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the segment integral is `L/π`
  have hL := gl18_L_eq_segment hab hδ hψ
  have hseg : ∫ x : ℝ, (earthquakeVF a b x : ℂ) * ψ x = lFunctionalAB a b ψ / π := by
    rw [gl18_integral_E hab, hL]
    field_simp
  -- `E`
  have hEL := gl18_earthquakeVF_lipschitz hab
  have hE := gl18_pairing_green hEL.continuous (K := b - a) (fun t => (gl18_earthquakeVF_bound hab t).trans
    (le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg t]))) (M := 8)
    (fun z hz => gl18_earthquakeVF_dzbar_le hab hz) hδ hψ hC
  -- `B`
  obtain ⟨hBc, K, hK⟩ := gl18_bendVF_continuous_growth hab
  have hB := gl18_pairing_green hBc hK (M := 64) (fun z hz => gl18_bendVF_dzbar_le hab hz) hδ hψ hC
  -- `∫_ℝ (B − iπE) ψ = 0`, from Green for the holomorphic `F ψ`
  set F : ℂ → ℂ := fun z => (z - a) * (z - b) / (a - b) * (log (z - a) - log (z - b)) with hF
  obtain ⟨CF, hCF⟩ := gl18_F_growth hab hF
  have hCF0 : 0 ≤ CF := by
    have := (norm_nonneg _).trans (hCF 0 (by simp))
    simpa using this
  have hFd := gl18_F_differentiableOn hF
  have hdz0 : ∀ z ∈ upperHalf, dzbar (fun z => F z * ψ z) z = 0 := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z => F z * ψ z) z :=
      (hFd.differentiableAt (hU.mem_nhds hz)).mul (hψ.differentiableAt (hδo.mem_nhds (hHδ hz)))
    exact (LiZhongQC.cauchyRiemann_iff.1 h1).2
  have hG := gl18_green (f := fun z => F z * ψ z)
    ((gl18_F_continuousOn hab hF).mul (hψ.continuousOn.mono hSδ))
    ((hFd.restrictScalars ℝ).mul ((hψ.restrictScalars ℝ).mono hHδ))
    ((integrableOn_zero (μ := volume) (s := upperHalf)).congr_fun (fun z hz => (hdz0 z hz).symm)
      hU.measurableSet)
    (C := CF * C) fun z hz => by
      rw [norm_mul]
      calc ‖F z‖ * ‖ψ z‖ ≤ CF * (1 + ‖z‖) * (C / (1 + ‖z‖) ^ 4) :=
            mul_le_mul (hCF z hz) (hC z hz) (norm_nonneg _) (by positivity)
        _ = CF * C / (1 + ‖z‖) ^ 3 := by
            field_simp
  rw [setIntegral_congr_fun hU.measurableSet hdz0, integral_zero] at hG
  have hFψ : ∫ x : ℝ, F x * ψ x = 0 := by
    have h2 : (2 * I)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
    exact (mul_eq_zero.1 hG.symm).resolve_left h2
  -- integrability on `ℝ` of `B ψ` and `E ψ`
  have hdecR : ∀ (W : ℝ → ℝ) (KW : ℝ), Continuous W → (∀ t, |W t| ≤ KW * (1 + |t|)) →
      Integrable fun x : ℝ => (W x : ℂ) * ψ x := by
    intro W KW hW hKW
    have hKW0 : 0 ≤ KW := by simpa using (abs_nonneg _).trans (hKW 0)
    have hψR : Continuous fun x : ℝ => ψ x :=
      hψ.continuousOn.comp_continuous Complex.continuous_ofReal fun x => by
        show -δ < (x : ℂ).im
        simp [hδ]
    have hg : Integrable (fun x : ℝ => KW * C * (1 + ‖x‖) ^ (-(3 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul _
    refine Integrable.mono' hg ((Complex.continuous_ofReal.comp hW).mul hψR).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.norm_eq_abs]
    have h1 := hC x (by simp)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    calc |W x| * ‖ψ x‖ ≤ KW * (1 + |x|) * (C / (1 + |x|) ^ 4) :=
          mul_le_mul (hKW x) h1 (norm_nonneg _) (by positivity)
      _ = KW * C * ((1 + |x|) ^ (3 : ℝ))⁻¹ := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          field_simp
  have hBi := hdecR _ K hBc hK
  have hEi := hdecR _ (b - a) hEL.continuous fun t => (gl18_earthquakeVF_bound hab t).trans
    (le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg t]))
  have hsplit : ∫ x : ℝ, F x * ψ x =
      (∫ x : ℝ, (bendVF a b x : ℂ) * ψ x) - I * π * ∫ x : ℝ, (earthquakeVF a b x : ℂ) * ψ x := by
    rw [← integral_const_mul, ← integral_sub hBi (hEi.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [gl18_F_real hab hF x]
    ring
  rw [hsplit, hseg, sub_eq_zero] at hFψ
  have hinv : (2 * I)⁻¹ = -(I / 2) := by
    rw [mul_inv, Complex.inv_I]
    ring
  refine ⟨?_, ?_⟩
  · rw [hB, hFψ, hinv]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [hE, hseg, hinv]
    field_simp

/-- Helper for `thm18_3` (§18.3, S6). The semicircle in coordinates: `w(θ) = m − r cos θ + i r sin θ`. -/
theorem gl18_arc_eq (a b θ : ℝ) :
    ((a : ℂ) + b) / 2 + ((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ)) =
      (((a + b) / 2 - (b - a) / 2 * Real.cos θ : ℝ) : ℂ) + (((b - a) / 2 * Real.sin θ : ℝ) : ℂ) * I := by
  rw [show I * ((π : ℂ) - θ) = ((π - θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub]
  push_cast
  ring

/-- Helper for `thm18_3` (§18.3, S6). On the semicircle `|P(w(θ))| = r sin θ = Im w(θ)`, where
`P(z) = (z − a)(z − b)/(a − b)`. -/
theorem gl18_arc_P {a b : ℝ} (hab : a < b) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    ‖((((a + b) / 2 - (b - a) / 2 * Real.cos θ : ℝ) : ℂ) + (((b - a) / 2 * Real.sin θ : ℝ) : ℂ) * I - a) *
        ((((a + b) / 2 - (b - a) / 2 * Real.cos θ : ℝ) : ℂ) + (((b - a) / 2 * Real.sin θ : ℝ) : ℂ) * I - b) /
        (a - b)‖ = (b - a) / 2 * Real.sin θ := by
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hpy := Real.sin_sq_add_cos_sq θ
  have key : ∀ c s : ℝ, s ^ 2 + c ^ 2 = 1 →
      ((((a + b) / 2 - r * c : ℝ) : ℂ) + ((r * s : ℝ) : ℂ) * I - a) *
        ((((a + b) / 2 - r * c : ℝ) : ℂ) + ((r * s : ℝ) : ℂ) * I - b) / (a - b) =
        ((r * s : ℝ) : ℂ) * ((s : ℂ) + (c : ℂ) * I) := by
    intro c s hcs
    have hab' : (a : ℂ) - b ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact_mod_cast (sub_neg.2 hab).ne
    have hpyc : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    rw [div_eq_iff hab']
    simp only [hr]
    push_cast
    linear_combination (((b : ℂ) - a) / 2) ^ 2 * hpyc + (((b : ℂ) - a) / 2) ^ 2 * (s : ℂ) ^ 2 * Complex.I_sq
  have e := key (Real.cos θ) (Real.sin θ) hpy
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0.le hs)]
  have h1 : ‖(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I‖ = 1 := by
    rw [Complex.norm_add_mul_I, hpy, Real.sqrt_one]
  rw [h1, mul_one]

/-- Helper for `thm18_3` (§18.3, S6). Chords of the semicircle: `|w(θ) − w(θ₀)| ≥ (2r/π)|θ − θ₀|` on `[0, π]`. -/
theorem gl18_arc_chord {a b : ℝ} (hab : a < b) {θ θ₀ : ℝ} (hθ : θ ∈ Icc 0 π) (hθ₀ : θ₀ ∈ Icc 0 π) :
    2 * ((b - a) / 2) / π * |θ - θ₀| ≤
      ‖((((a + b) / 2 - (b - a) / 2 * Real.cos θ : ℝ) : ℂ) + (((b - a) / 2 * Real.sin θ : ℝ) : ℂ) * I) -
        ((((a + b) / 2 - (b - a) / 2 * Real.cos θ₀ : ℝ) : ℂ) + (((b - a) / 2 * Real.sin θ₀ : ℝ) : ℂ) * I)‖ := by
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set u := (θ - θ₀) / 2 with hu
  have hu1 : |u| ≤ π / 2 := by
    rw [hu, abs_div, abs_two, div_le_div_iff_of_pos_right two_pos, abs_le]
    constructor <;> linarith [hθ.1, hθ.2, hθ₀.1, hθ₀.2]
  -- `|w(θ) − w(θ₀)|² = 4r² sin²((θ − θ₀)/2)`
  have hsq : ‖((((a + b) / 2 - r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I) -
      ((((a + b) / 2 - r * Real.cos θ₀ : ℝ) : ℂ) + ((r * Real.sin θ₀ : ℝ) : ℂ) * I)‖ ^ 2 =
      (2 * r * Real.sin u) ^ 2 := by
    rw [show ((((a + b) / 2 - r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I) -
        ((((a + b) / 2 - r * Real.cos θ₀ : ℝ) : ℂ) + ((r * Real.sin θ₀ : ℝ) : ℂ) * I) =
        (((r * (Real.cos θ₀ - Real.cos θ)) : ℝ) : ℂ) + ((r * (Real.sin θ - Real.sin θ₀) : ℝ) : ℂ) * I by
          push_cast; ring,
      Complex.sq_norm, Complex.normSq_add_mul_I]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq θ₀
    have h3 := Real.cos_sub θ θ₀
    have h4 := Real.two_mul_sin_mul_sin u u
    rw [sub_self, Real.cos_zero, show u + u = θ - θ₀ by rw [hu]; ring] at h4
    linear_combination r ^ 2 * h1 + r ^ 2 * h2 + 2 * r ^ 2 * h3 - 2 * r ^ 2 * h4
  -- Jordan: `|sin u| ≥ (2/π)|u|`
  have hj : 2 / π * |u| ≤ |Real.sin u| := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [abs_le.1 hu1,
        Real.pi_pos]))]
      exact Real.mul_le_sin h (by linarith [le_abs_self u])
    · rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [abs_le.1 hu1,
        Real.pi_pos])), ← Real.sin_neg]
      exact Real.mul_le_sin (by linarith) (by linarith [neg_abs_le u])
  have hθu : |θ - θ₀| = 2 * |u| := by
    rw [hu, abs_div, abs_two]
    ring
  rw [hθu, ← sq_le_sq₀ (by positivity) (norm_nonneg _), hsq]
  have := pow_le_pow_left₀ (by positivity) hj 2
  rw [sq_abs] at this
  have hπ := Real.pi_pos
  calc (2 * r / π * (2 * |u|)) ^ 2 = (2 * r) ^ 2 * (2 / π * |u|) ^ 2 := by ring
    _ ≤ (2 * r) ^ 2 * Real.sin u ^ 2 := by gcongr
    _ = (2 * r * Real.sin u) ^ 2 := by ring

/-- Helper for `thm18_3` (§18.3, S6). `L_ab` is a bounded linear functional on `A(ℍ)`, and its defining integral is a
genuine (absolutely convergent) one: on the semicircle `|P(w)| = Im w`, and the area mean value over `B(w, Im w/2)`
plus Tonelli give `∫₀^π |ψ(w(θ)) P(w(θ)) w'(θ)| dθ ≤ K ∬_ℍ |ψ|`. -/
theorem gl18_L_bound {a b : ℝ} (hab : a < b) :
    ∃ K : ℝ, ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ upperHalf → IntegrableOn ψ upperHalf →
      IntervalIntegrable (fun θ : ℝ => ψ ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ))) *
        (((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - a) *
          ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - b) / (a - b)) *
        (-(I * ((b - a) / 2 * Complex.exp (I * (π - θ)))))) volume 0 π ∧
      ‖lFunctionalAB a b ψ‖ ≤ K * ∫ z in upperHalf, ‖ψ z‖ := by
  refine ⟨12 * π, fun ψ hψd hψi => ?_⟩
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  set r : ℝ := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hπ := Real.pi_pos
  set w : ℝ → ℂ := fun θ => ((a : ℂ) + b) / 2 + ((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ)) with hw
  set g : ℝ → ℂ := fun θ => ψ (w θ) * ((w θ - a) * (w θ - b) / (a - b)) *
    (-(I * (((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ))))) with hg
  have hwθ : ∀ θ, w θ = ((((a + b) / 2 - r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I) :=
    fun θ => gl18_arc_eq a b θ
  have hwim : ∀ θ, (w θ).im = r * Real.sin θ := fun θ => by
    rw [hwθ]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hwc : Continuous w := by
    simp only [hw]
    fun_prop
  have hwH : ∀ θ ∈ Ioo 0 π, w θ ∈ upperHalf := fun θ hθ => by
    show 0 < (w θ).im
    rw [hwim]
    exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  -- `|g(θ)| = |ψ(w θ)| · r sin θ · r`
  have hgn : ∀ θ ∈ Icc 0 π, ‖g θ‖ = ‖ψ (w θ)‖ * (r * Real.sin θ) * r := by
    intro θ hθ
    have h1 : ‖(w θ - a) * (w θ - b) / (a - b)‖ = r * Real.sin θ := by
      rw [hwθ]
      exact gl18_arc_P hab hθ
    have h2 : ‖-(I * (((b : ℂ) - a) / 2 * Complex.exp (I * (π - θ))))‖ = r := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, norm_mul,
        show I * ((π : ℂ) - θ) = ((π - θ : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
        mul_one, show ((b : ℂ) - a) / 2 = ((r : ℝ) : ℂ) by rw [hr]; push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
    rw [hg, norm_mul, norm_mul, h1, h2]
  -- the area mean value at `w(θ)`, radius `r sin θ / 2`
  set E : Set (ℝ × ℂ) := {p | dist p.2 (w p.1) < r * Real.sin p.1 / 2} with hE
  have hEo : IsOpen E :=
    isOpen_lt (continuous_snd.dist (hwc.comp continuous_fst))
      ((continuous_const.mul (Real.continuous_sin.comp continuous_fst)).div_const 2)
  set k : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal (4 / (π * Real.sin θ)) with hk
  have hkm : Measurable k := by
    simp only [hk]
    exact ((measurable_const.mul Real.continuous_sin.measurable).const_div 4).ennreal_ofReal
  have hpt : ∀ θ ∈ Ioo 0 π, ‖g θ‖ₑ ≤
      k θ * ∫⁻ ζ in upperHalf, E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    set s := r * Real.sin θ / 2 with hsdef
    have hs0 : 0 < s := by positivity
    have hsub : closedBall (w θ) s ⊆ upperHalf := fun z hz => by
      have h1 := (Complex.abs_im_le_norm (z - w θ)).trans (mem_closedBall_iff_norm.1 hz)
      rw [Complex.sub_im, hwim] at h1
      show 0 < z.im
      linarith [neg_abs_le (z.im - r * Real.sin θ)]
    have hmv := LiZhongQC.h36p_meanvalue hψd hs0 hsub
    have hball : ∫⁻ ζ in upperHalf, E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ) =
        ∫⁻ ζ in ball (w θ) s, ENNReal.ofReal ‖ψ ζ‖ := by
      have e : (fun ζ => E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ)) =
          (ball (w θ) s).indicator fun ζ => ‖ψ ζ‖ₑ := by
        funext ζ
        by_cases h : ζ ∈ ball (w θ) s
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (θ, ζ) ∈ E from h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (θ, ζ) ∉ E from h)]
      rw [e, lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
        Set.inter_eq_left.2 (ball_subset_closedBall.trans hsub)]
      simp only [ofReal_norm]
    rw [hball]
    have hgθ : ‖g θ‖ₑ = ENNReal.ofReal (4 / (π * Real.sin θ)) * (ENNReal.ofReal (π * s ^ 2) *
        ENNReal.ofReal ‖ψ (w θ)‖) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
        hgn θ (Ioo_subset_Icc_self hθ), hsdef]
      congr 1
      field_simp
      ring
    rw [hgθ]
    exact mul_le_mul' le_rfl hmv
  -- Tonelli
  have hψm : AEMeasurable (fun ζ => ‖ψ ζ‖ₑ) (volume.restrict upperHalf) := hψi.aestronglyMeasurable.enorm
  have hFm : AEMeasurable (Function.uncurry fun θ ζ => k θ * E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ))
      ((volume.restrict (Ioo 0 π)).prod (volume.restrict upperHalf)) := by
    refine (hkm.comp measurable_fst).aemeasurable.mul ?_
    exact (hψm.comp_snd).indicator hEo.measurableSet
  have hswap := lintegral_lintegral_swap hFm
  -- the geometric bound on the `θ`-integral
  have hgeo : ∀ ζ ∈ upperHalf, ∫⁻ θ in Ioo 0 π, k θ * E.indicator (fun _ => (1 : ℝ≥0∞)) (θ, ζ) ≤ 12 := by
    intro ζ hζ
    have hζ' : 0 < ζ.im := hζ
    by_cases hne : ∃ θ₀ ∈ Ioo 0 π, (θ₀, ζ) ∈ E
    · obtain ⟨θ₀, hθ₀, hθ₀E⟩ := hne
      set d := π * ζ.im / r with hd
      have hbd : ∀ θ ∈ Ioo 0 π, k θ * E.indicator (fun _ => (1 : ℝ≥0∞)) (θ, ζ) ≤
          (Icc (θ₀ - d) (θ₀ + d)).indicator (fun _ => ENNReal.ofReal (6 * r / (π * ζ.im))) θ := by
        intro θ hθ
        by_cases hθE : (θ, ζ) ∈ E
        · have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
          have hdist : dist ζ (w θ) < r * Real.sin θ / 2 := hθE
          have hdist₀ : dist ζ (w θ₀) < r * Real.sin θ₀ / 2 := hθ₀E
          have him : ∀ t, dist ζ (w t) < r * Real.sin t / 2 → r * Real.sin t / 2 < ζ.im ∧
              ζ.im < 3 * (r * Real.sin t) / 2 := fun t ht => by
            have h1 := (Complex.abs_im_le_norm (ζ - w t)).trans_lt (by rwa [← dist_eq_norm])
            rw [Complex.sub_im, hwim] at h1
            constructor <;> linarith [abs_lt.1 h1]
          obtain ⟨h1, h2⟩ := him θ hdist
          obtain ⟨h1₀, -⟩ := him θ₀ hdist₀
          have hch := gl18_arc_chord hab (Ioo_subset_Icc_self hθ) (Ioo_subset_Icc_self hθ₀)
          rw [← hr, ← hwθ, ← hwθ] at hch
          have htri : ‖w θ - w θ₀‖ < 2 * ζ.im := by
            have := dist_triangle (w θ) ζ (w θ₀)
            rw [dist_comm (w θ) ζ, dist_eq_norm (w θ)] at this
            linarith
          have hθd : |θ - θ₀| ≤ d := by
            rw [hd, le_div_iff₀ hr0]
            have : 2 * r / π * |θ - θ₀| < 2 * ζ.im := hch.trans_lt htri
            rw [div_mul_eq_mul_div, div_lt_iff₀ hπ] at this
            nlinarith
          rw [Set.indicator_of_mem hθE, mul_one, Set.indicator_of_mem
            (show θ ∈ Icc (θ₀ - d) (θ₀ + d) from ⟨by linarith [neg_abs_le (θ - θ₀)],
              by linarith [le_abs_self (θ - θ₀)]⟩)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        · rw [Set.indicator_of_notMem hθE, mul_zero]
          exact bot_le
      calc ∫⁻ θ in Ioo 0 π, k θ * E.indicator (fun _ => (1 : ℝ≥0∞)) (θ, ζ)
          ≤ ∫⁻ θ in Ioo 0 π, (Icc (θ₀ - d) (θ₀ + d)).indicator
              (fun _ => ENNReal.ofReal (6 * r / (π * ζ.im))) θ :=
            setLIntegral_mono' measurableSet_Ioo hbd
        _ ≤ ∫⁻ θ, (Icc (θ₀ - d) (θ₀ + d)).indicator (fun _ => ENNReal.ofReal (6 * r / (π * ζ.im))) θ :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (6 * r / (π * ζ.im)) * ENNReal.ofReal (θ₀ + d - (θ₀ - d)) := by
            rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
        _ = 12 := by
            rw [← ENNReal.ofReal_mul (by positivity), hd]
            rw [show 6 * r / (π * ζ.im) * (θ₀ + π * ζ.im / r - (θ₀ - π * ζ.im / r)) = 12 by
              field_simp
              ring]
            simp
    · push Not at hne
      calc ∫⁻ θ in Ioo 0 π, k θ * E.indicator (fun _ => (1 : ℝ≥0∞)) (θ, ζ) = ∫⁻ θ in Ioo 0 π, 0 :=
            setLIntegral_congr_fun measurableSet_Ioo fun θ hθ => by
              rw [Set.indicator_of_notMem (hne θ hθ), mul_zero]
        _ ≤ 12 := by simp
  -- the bound on `∫⁻ |g|`
  have hlint : ∫⁻ θ in Ioo 0 π, ‖g θ‖ₑ ≤ 12 * ∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ := by
    calc ∫⁻ θ in Ioo 0 π, ‖g θ‖ₑ
        ≤ ∫⁻ θ in Ioo 0 π, ∫⁻ ζ in upperHalf, k θ * E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun θ hθ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact hpt θ hθ
      _ = ∫⁻ ζ in upperHalf, ∫⁻ θ in Ioo 0 π, k θ * E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ) := hswap
      _ ≤ ∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ * 12 := by
          refine setLIntegral_mono' hU.measurableSet fun ζ hζ => ?_
          have e : ∀ θ, k θ * E.indicator (fun p => ‖ψ p.2‖ₑ) (θ, ζ) =
              ‖ψ ζ‖ₑ * (k θ * E.indicator (fun _ => (1 : ℝ≥0∞)) (θ, ζ)) := fun θ => by
            by_cases h : (θ, ζ) ∈ E
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one, mul_comm]
            · simp [Set.indicator_of_notMem h]
          simp only [e]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
          exact mul_le_mul' le_rfl (hgeo ζ hζ)
      _ = 12 * ∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ := by
          rw [lintegral_mul_const' _ _ (by norm_num), mul_comm]
  -- conclusions
  have hfin : ∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ < ⊤ := hψi.2
  have hgc : ContinuousOn g (Ioo 0 π) := by
    have h1 : ContinuousOn (fun θ => ψ (w θ)) (Ioo 0 π) :=
      hψd.continuousOn.comp hwc.continuousOn fun θ hθ => hwH θ hθ
    refine (h1.mul (Continuous.continuousOn ?_)).mul (Continuous.continuousOn ?_)
    · exact ((hwc.sub continuous_const).mul (hwc.sub continuous_const)).div_const _
    · fun_prop
  have hgi : IntegrableOn g (Ioo 0 π) :=
    ⟨hgc.aestronglyMeasurable measurableSet_Ioo, hlint.trans_lt (ENNReal.mul_lt_top (by norm_num) hfin)⟩
  have hgi' : IntervalIntegrable g volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hπ.le).2 hgi
  refine ⟨hgi', ?_⟩
  show ‖(π : ℂ) * ∫ θ in (0 : ℝ)..π, g θ‖ ≤ 12 * π * ∫ z in upperHalf, ‖ψ z‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  have h1 : ‖∫ θ in (0 : ℝ)..π, g θ‖ ≤ ∫ θ in Ioo 0 π, ‖g θ‖ := by
    rw [intervalIntegral.integral_of_le hπ.le, integral_Ioc_eq_integral_Ioo]
    exact norm_integral_le_integral_norm _
  have h2 : ∫ θ in Ioo 0 π, ‖g θ‖ ≤ 12 * ∫ z in upperHalf, ‖ψ z‖ := by
    rw [integral_norm_eq_lintegral_enorm hgi.aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hψi.aestronglyMeasurable]
    calc (∫⁻ θ in Ioo 0 π, ‖g θ‖ₑ).toReal ≤ (12 * ∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfin.ne) hlint
      _ = 12 * (∫⁻ ζ in upperHalf, ‖ψ ζ‖ₑ).toReal := by
          rw [ENNReal.toReal_mul]
          norm_num
  nlinarith

/-- Helper for `thm18_3` (§18.3, S11). `L_ab` is linear on functions whose defining integrands are integrable. -/
theorem gl18_L_sub {a b : ℝ} {ψ₁ ψ₂ : ℂ → ℂ}
    (h₁ : IntervalIntegrable (fun θ : ℝ => ψ₁ ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ))) *
        (((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - a) *
          ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - b) / (a - b)) *
        (-(I * ((b - a) / 2 * Complex.exp (I * (π - θ)))))) volume 0 π)
    (h₂ : IntervalIntegrable (fun θ : ℝ => ψ₂ ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ))) *
        (((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - a) *
          ((a + b) / 2 + (b - a) / 2 * Complex.exp (I * (π - θ)) - b) / (a - b)) *
        (-(I * ((b - a) / 2 * Complex.exp (I * (π - θ)))))) volume 0 π) :
    lFunctionalAB a b ψ₁ - lFunctionalAB a b ψ₂ = lFunctionalAB a b (fun z => ψ₁ z - ψ₂ z) := by
  unfold lFunctionalAB
  rw [← mul_sub, ← intervalIntegral.integral_sub h₁ h₂]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only
  ring

/-- Helper for `thm18_3` (§18.3, S11). The two pairings on all of `A(ℍ)`: S11 on the approximants of S7, and the
limit through the bounds S2/S4 (left sides) and S6 (right sides). -/
theorem gl18_identity {a b : ℝ} (hab : a < b) {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceOpen (toExt upperHalf)) :
    ∫ z in upperHalf, dzbar (beurlingAhlfors (bendVF a b) 2) z * φ z = lFunctionalAB a b φ / 2 ∧
      ∫ z in upperHalf, dzbar (beurlingAhlfors (earthquakeVF a b) 2) z * φ z =
        -(I * lFunctionalAB a b φ) / (2 * π) := by
  have hU : IsOpen upperHalf := LiZhongQC.isOpen_upperHalf
  obtain ⟨hφi, hφd⟩ := gl18_aSpace_upperHalf hφ
  obtain ⟨ψ, hψd, hψb, hψi, hlim⟩ := gl18_approx hφ
  obtain ⟨K, hK⟩ := gl18_L_bound hab
  have hψdH : ∀ n, DifferentiableOn ℂ (ψ n) upperHalf := fun n => by
    obtain ⟨δ, hδ, hd⟩ := hψd n
    exact hd.mono fun z (hz : 0 < z.im) => by
      show -δ < z.im
      linarith
  -- `L(ψ_n) → L(φ)`
  have hLlim : Tendsto (fun n => lFunctionalAB a b (ψ n)) atTop (𝓝 (lFunctionalAB a b φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hlim.const_mul K)
    have h1 := (hK (ψ n) (hψdH n) (hψi n)).1
    have h2 := (hK φ hφd hφi.integrableOn).1
    rw [gl18_L_sub h1 h2]
    exact (hK (fun z => ψ n z - φ z) ((hψdH n).sub hφd) ((hψi n).sub hφi.integrableOn)).2
  -- the pairings converge
  have hpair : ∀ V : ℝ → ℝ, ∀ M : ℝ, (∀ z : ℂ, 0 < z.im → ‖dzbar (beurlingAhlfors V 2) z‖ ≤ M) →
      Tendsto (fun n => ∫ z in upperHalf, dzbar (beurlingAhlfors V 2) z * ψ n z) atTop
        (𝓝 (∫ z in upperHalf, dzbar (beurlingAhlfors V 2) z * φ z)) := by
    intro V M hM
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hlim.const_mul M)
    rw [← integral_sub (gl18_pairing_integrable hM (hψi n)) (gl18_pairing_integrable hM hφi.integrableOn)]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (((hψi n).sub hφi.integrableOn).norm.const_mul M)
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun z hz => ?_))
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM z hz) (norm_nonneg _)
  have hnice : ∀ n, ∫ z in upperHalf, dzbar (beurlingAhlfors (bendVF a b) 2) z * ψ n z =
      lFunctionalAB a b (ψ n) / 2 ∧ ∫ z in upperHalf, dzbar (beurlingAhlfors (earthquakeVF a b) 2) z * ψ n z =
        -(I * lFunctionalAB a b (ψ n)) / (2 * π) := fun n => by
    obtain ⟨δ, hδ, hd⟩ := hψd n
    obtain ⟨C, hC⟩ := hψb n
    exact gl18_identity_nice hab hδ hd hC
  constructor
  · refine tendsto_nhds_unique (hpair _ 64 fun z hz => gl18_bendVF_dzbar_le hab hz) ?_
    exact (hLlim.div_const 2).congr fun n => ((hnice n).1).symm
  · refine tendsto_nhds_unique (hpair _ 8 fun z hz => gl18_earthquakeVF_dzbar_le hab hz) ?_
    exact ((hLlim.const_mul I).neg.div_const (2 * π)).congr fun n => ((hnice n).2).symm

/-- **Theorem 3** (§18.3, l. 13450). `Re L`, `Im L` (and their negatives) represent infinitesimal thinning and left
twisting (fattening and right twisting) along the hyperbolic line joining `a` to `b`: for some `c₁, c₂ > 0`, the
classes of `B_ab` and `E_ab` are `c₁ Re L_ab` and `c₂ Im L_ab`. -/
theorem thm18_3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ a b : ℝ, a < b → ∀ φ ∈ aSpaceOpen (toExt upperHalf),
    (∫ z in upperHalf, dzbar (beurlingAhlfors (bendVF a b) 2) z * φ z).re = c₁ * (lFunctionalAB a b φ).re ∧
      (∫ z in upperHalf, dzbar (beurlingAhlfors (earthquakeVF a b) 2) z * φ z).re =
        c₂ * (lFunctionalAB a b φ).im := by
  refine ⟨1 / 2, 1 / (2 * π), by norm_num, by positivity, fun a b hab φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := gl18_identity hab hφ
  have hc : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, hc, Complex.div_ofReal_re, Complex.div_ofNat_re]
  constructor
  · ring
  · simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg]
    ring

end GardinerLakic2000
