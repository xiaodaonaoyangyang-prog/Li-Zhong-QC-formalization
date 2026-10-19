import LiZhongQC.Lemmas.S36BersRepairW

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **E.** Gluing: `E = W₊` on `Im z ≤ 0` and `-conj W₋(z̄)` on `ℍ` is entire when `W₊ = -conj W₋` on `ℝ` (rectangle
lemma `integral_boundary_rect_eq_zero_of_differentiableAt_off_real_axis` and Morera,
`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`); so is `E'''`, and `E''' = W₊'''` on `𝕃`,
`E'''(z) = -conj W₋'''(z̄)` on `ℍ`. -/
theorem s36b_glue {Wp Wm : ℂ → ℂ} (hcp : ContinuousOn Wp {z : ℂ | z.im ≤ 0})
    (hcm : ContinuousOn Wm {z : ℂ | z.im ≤ 0}) (hdp : DifferentiableOn ℂ Wp lowerHalf)
    (hdm : DifferentiableOn ℂ Wm lowerHalf) (hR : ∀ x : ℝ, Wp (x : ℂ) = -conj (Wm (x : ℂ))) :
    Differentiable ℂ (iteratedDeriv 3 (fun z : ℂ => if z.im ≤ 0 then Wp z else -conj (Wm (conj z)))) ∧
      (∀ z ∈ lowerHalf, iteratedDeriv 3 (fun z : ℂ => if z.im ≤ 0 then Wp z else -conj (Wm (conj z))) z =
        iteratedDeriv 3 Wp z) ∧
      ∀ z ∈ upperHalf, iteratedDeriv 3 (fun z : ℂ => if z.im ≤ 0 then Wp z else -conj (Wm (conj z))) z =
        -conj (iteratedDeriv 3 Wm (conj z)) := by
  set E : ℂ → ℂ := fun z : ℂ => if z.im ≤ 0 then Wp z else -conj (Wm (conj z)) with hE
  have hL : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  have hU : IsOpen upperHalf := isOpen_lt continuous_const continuous_im
  have hEl : ∀ z ∈ lowerHalf, E =ᶠ[𝓝 z] Wp := fun z hz =>
    Filter.eventually_of_mem (hL.mem_nhds hz) fun w hw => by
      have hw' : w.im < 0 := hw
      simp only [hE, if_pos hw'.le]
  have hEu : ∀ z ∈ upperHalf, E =ᶠ[𝓝 z] fun w => -(conj ∘ Wm ∘ conj) w := fun z hz =>
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
      have hw' : 0 < w.im := hw
      simp only [hE, if_neg (not_le.2 hw')]
      rfl
  have hcont : Continuous E := by
    refine continuous_if_le continuous_im continuous_const hcp ?_ ?_
    · refine ContinuousOn.neg (Complex.continuous_conj.comp_continuousOn
        (hcm.comp Complex.continuous_conj.continuousOn fun w hw => ?_))
      show (conj w).im ≤ 0
      rw [Complex.conj_im]
      have : (0 : ℝ) ≤ w.im := hw
      linarith
    · intro x hx
      have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hx])
      rw [hxr, Complex.conj_ofReal]
      exact hR x.re
  have hdiff : ∀ p : ℂ, p.im ≠ 0 → DifferentiableAt ℂ E p := by
    intro p hp
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · exact (hdp.differentiableAt (hL.mem_nhds hlt)).congr_of_eventuallyEq (hEl p hlt)
    · have hpl : conj p ∈ lowerHalf := by
        show (conj p).im < 0
        rw [Complex.conj_im]
        linarith
      have h1 := (hdm.differentiableAt (hL.mem_nhds hpl)).conj_conj
      rw [Complex.conj_conj] at h1
      exact h1.neg.congr_of_eventuallyEq (hEu p hgt)
  have hcons : IsConservativeOn E univ := by
    intro z w _
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    exact integral_boundary_rect_eq_zero_of_differentiableAt_off_real_axis E z w hcont.continuousOn
      (fun p _ hp => hdiff p hp)
  have hEd : DifferentiableOn ℂ E univ :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).1 ⟨hcons, hcont.continuousOn⟩
  have e3 : ∀ f : ℂ → ℂ, iteratedDeriv 3 f = deriv (deriv (deriv f)) := fun f => by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  refine ⟨?_, fun z hz => ?_, fun z hz => ?_⟩
  · rw [e3]
    have h1 := ((hEd.deriv isOpen_univ).deriv isOpen_univ).deriv isOpen_univ
    exact fun z => (h1 z trivial).differentiableAt Filter.univ_mem
  · rw [e3, e3]
    exact (hEl z hz).deriv.deriv.deriv_eq
  · have he : iteratedDeriv 3 E z =
        iteratedDeriv 3 (fun w => -(conj ∘ Wm ∘ conj) w) z := by
      rw [e3, e3]
      exact (hEu z hz).deriv.deriv.deriv_eq
    rw [he, iteratedDeriv_fun_neg, e3, e3]
    simp only [deriv_conj_conj, Function.comp_apply]

/-- Pointwise splitting of the circle-mean integrand: `f(w) r² sin²θ` as a combination of `f(w)`,
`f(w)(w - x)²` and the Cauchy integrand of the second Taylor coefficient. -/
theorem s36b_cm_point (f : ℂ → ℂ) (x : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    f (x + r * exp (θ * I)) * ((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) =
      (r : ℂ) ^ 2 / 2 * f (circleMap x r θ) - 1 / 4 * (f (circleMap x r θ) * (circleMap x r θ - x) ^ 2) +
        I * (r : ℂ) ^ 4 / 4 * (deriv (circleMap x r) θ •
          ((1 / (circleMap x r θ - x)) ^ 2 • (circleMap x r θ - x)⁻¹ • f (circleMap x r θ))) := by
  rw [deriv_circleMap]
  simp only [circleMap, smul_eq_mul, zero_add, add_sub_cancel_left]
  have he : exp (θ * I) ≠ 0 := exp_ne_zero _
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : (Real.sin θ : ℂ) = ((exp (θ * I))⁻¹ - exp (θ * I)) * I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul, Complex.exp_neg]
  rw [hs]
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

/-- The circle mean for `r > 0` (Cauchy power series coefficient `f''(x)/2`, mean value property). -/
theorem s36b_cm_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..2 * π, f (x + r * exp (θ * I)) * ((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2)) =
      2 * (π : ℂ) * ((r : ℂ) ^ 2 / 4 * (2 * f x - iteratedDeriv 2 f x * (r : ℂ) ^ 2 / 2)) := by
  have hRpos : (0 : ℝ≥0) < ⟨r, hr.le⟩ := NNReal.coe_pos.1 hr
  have hps := hf.hasFPowerSeriesOnBall x hRpos
  have h2 := hps.factorial_smul (1 : ℂ) 2
  rw [← iteratedDeriv_eq_iteratedFDeriv, cauchyPowerSeries_apply] at h2
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  change Nat.factorial 2 • (2 * (π : ℂ) * I)⁻¹ • (∮ z in C(x, r), (1 / (z - x)) ^ 2 • (z - x)⁻¹ • f z) =
    iteratedDeriv 2 f x at h2
  have hJ : (∮ z in C(x, r), (1 / (z - x)) ^ 2 • (z - x)⁻¹ • f z) = π * I * iteratedDeriv 2 f x := by
    rw [← h2]
    simp only [Nat.factorial, Nat.succ_eq_add_one, smul_eq_mul, nsmul_eq_mul]
    push_cast
    field_simp
  have h2pi : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hA : (∫ θ in (0 : ℝ)..2 * π, f (circleMap x r θ)) = 2 * π * f x := by
    have := (hf.diffContOnCl (s := ball x |r|)).circleAverage
    rw [Real.circleAverage_def, Complex.real_smul] at this
    rw [← this]
    push_cast
    field_simp
  have hB : (∫ θ in (0 : ℝ)..2 * π, f (circleMap x r θ) * (circleMap x r θ - x) ^ 2) = 0 := by
    have hg : Differentiable ℂ (fun z => f z * (z - x) ^ 2) := hf.mul (by fun_prop)
    have := (hg.diffContOnCl (s := ball x |r|)).circleAverage
    rw [Real.circleAverage_def, Complex.real_smul, sub_self] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by exact_mod_cast inv_ne_zero (by positivity : (2 * π : ℝ) ≠ 0))
    · exact h
  have hci : CircleIntegrable (fun z => (1 / (z - x)) ^ 2 • (z - x)⁻¹ • f z) x r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    have hne : ∀ z ∈ sphere x r, z - x ≠ 0 := fun z hz =>
      sub_ne_zero.2 (ne_of_mem_sphere hz hr.ne')
    refine ContinuousOn.smul (ContinuousOn.pow (continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      hne) 2) (ContinuousOn.smul ((continuousOn_id.sub continuousOn_const).inv₀ hne) hf.continuous.continuousOn)
  have hcA : Continuous fun θ : ℝ => f (circleMap x r θ) := hf.continuous.comp (continuous_circleMap x r)
  have hcB : Continuous fun θ : ℝ => f (circleMap x r θ) * (circleMap x r θ - x) ^ 2 :=
    hcA.mul (((continuous_circleMap x r).sub continuous_const).pow 2)
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => (r : ℂ) ^ 2 / 2 * f (circleMap x r θ) -
      1 / 4 * (f (circleMap x r θ) * (circleMap x r θ - x) ^ 2) +
        I * (r : ℂ) ^ 4 / 4 * (deriv (circleMap x r) θ •
          ((1 / (circleMap x r θ - x)) ^ 2 • (circleMap x r θ - x)⁻¹ • f (circleMap x r θ))))
      (fun θ _ => s36b_cm_point f x hr.ne' θ)]
  rw [intervalIntegral.integral_add ((hcA.intervalIntegrable _ _).const_mul _ |>.sub
      ((hcB.intervalIntegrable _ _).const_mul _)) (hci.out.const_mul _),
    intervalIntegral.integral_sub ((hcA.intervalIntegrable _ _).const_mul _) ((hcB.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hA, hB]
  have hJ' : (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap x r) θ •
      ((1 / (circleMap x r θ - x)) ^ 2 • (circleMap x r θ - x)⁻¹ • f (circleMap x r θ))) =
      π * I * iteratedDeriv 2 f x := hJ
  rw [hJ']
  ring_nf
  rw [I_sq]
  ring

/-- **L1.** Circle mean: for entire `f`, `∫₀^{2π} f(x + re^{iθ}) r² sin²θ dθ = 2π (r²/4)(2f(x) - f''(x) r²/2)`
(`sin²θ = 1/2 - (e^{2iθ} + e^{-2iθ})/4` and the Taylor coefficients `f(x)`, `f''(x)/2`). -/
theorem s36b_circle_mean {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℂ) (r : ℝ) :
    (∫ θ in (0 : ℝ)..2 * π, f (x + r * exp (θ * I)) * ((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2)) =
      2 * (π : ℂ) * ((r : ℂ) ^ 2 / 4 * (2 * f x - iteratedDeriv 2 f x * (r : ℂ) ^ 2 / 2)) := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · -- negative radius: shift `θ ↦ θ + π` (`e^{i(θ+π)} = -e^{iθ}`, `sin²` unchanged)
    have key := s36b_cm_pos hf x (neg_pos.2 hr)
    set G : ℝ → ℂ := fun θ => f (x + ((-r : ℝ) : ℂ) * exp (θ * I)) * ((((-r : ℝ)) : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2)
      with hG
    have hper : Function.Periodic G (2 * π) := by
      intro θ
      simp only [hG]
      have e1 : exp (((θ + 2 * π : ℝ) : ℂ) * I) = exp (θ * I) := by
        rw [show (((θ + 2 * π : ℝ) : ℂ) * I) = θ * I + 2 * π * I by push_cast; ring, exp_add, exp_two_pi_mul_I,
          mul_one]
      rw [e1, Real.sin_add_two_pi]
    have hpt : ∀ θ : ℝ, f (x + r * exp (θ * I)) * ((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) = G (θ + π) := by
      intro θ
      simp only [hG]
      have e1 : exp (((θ + π : ℝ) : ℂ) * I) = -exp (θ * I) := by
        rw [show (((θ + π : ℝ) : ℂ) * I) = θ * I + π * I by push_cast; ring, exp_add, exp_pi_mul_I]
        ring
      rw [e1, Real.sin_add_pi]
      push_cast
      ring
    rw [intervalIntegral.integral_congr (g := fun θ => G (θ + π)) (fun θ _ => hpt θ),
      intervalIntegral.integral_comp_add_right, zero_add,
      show 2 * π + π = π + 2 * π by ring, hper.intervalIntegral_add_eq π 0, zero_add]
    rw [show (∫ θ in (0 : ℝ)..2 * π, G θ) = _ from key]
    push_cast
    ring
  · subst hr
    simp
  · exact s36b_cm_pos hf x hr

/-- **L2.** An entire `f` with `|f(z)| ≤ C/|Im z|²` off `ℝ` vanishes: by `s36b_circle_mean` at real `x` the mean is
bounded by `C`, so `r → ∞` gives `f''(x) = 0` and then `f(x) = 0`; the identity theorem does the rest. -/
theorem s36b_circle_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ}
    (hC : ∀ z : ℂ, z.im ≠ 0 → ‖f z‖ ≤ C / z.im ^ 2) : ∀ z, f z = 0 := by
  have hC0 : 0 ≤ C := by
    have := hC I (by simp)
    simp only [Complex.I_im, one_pow, div_one] at this
    exact (norm_nonneg _).trans this
  -- the bound `‖r² f(x)/2 - r⁴ f''(x)/8‖ ≤ C` for real `x`, `r > 0`
  have hbd : ∀ x : ℝ, ∀ r : ℝ, 0 < r →
      ‖(r : ℂ) ^ 2 / 4 * (2 * f x - iteratedDeriv 2 f x * (r : ℂ) ^ 2 / 2)‖ ≤ C := by
    intro x r hr
    have hm := s36b_circle_mean hf (x : ℂ) r
    have hle : ‖∫ θ in (0 : ℝ)..2 * π, f (x + r * exp (θ * I)) * ((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2)‖ ≤
        C * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs]
      by_cases hs : Real.sin θ = 0
      · rw [hs]
        simp [hC0]
      · have him : ((x : ℂ) + r * exp (θ * I)).im = r * Real.sin θ := by
          rw [add_im, ofReal_im, zero_add, Complex.exp_mul_I]
          simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
        have hne : r * Real.sin θ ≠ 0 := mul_ne_zero hr.ne' hs
        have h1 := hC _ (by rw [him]; exact hne)
        rw [him] at h1
        have hpos : 0 < (r * Real.sin θ) ^ 2 := by positivity
        calc ‖f (x + r * exp (θ * I))‖ * (r ^ 2 * Real.sin θ ^ 2)
            = ‖f (x + r * exp (θ * I))‖ * (r * Real.sin θ) ^ 2 := by ring
          _ ≤ C / (r * Real.sin θ) ^ 2 * (r * Real.sin θ) ^ 2 := mul_le_mul_of_nonneg_right h1 hpos.le
          _ = C := by field_simp
    rw [hm, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hle
    nlinarith [Real.pi_pos, norm_nonneg ((r : ℂ) ^ 2 / 4 * (2 * f x - iteratedDeriv 2 f x * (r : ℂ) ^ 2 / 2))]
  -- `f''(x) = 0`, then `f(x) = 0`, for real `x`
  have hreal : ∀ x : ℝ, f x = 0 := by
    intro x
    set a := ‖f x‖ with ha
    set b := ‖iteratedDeriv 2 f x‖ with hb
    have key : ∀ t : ℝ, 0 < t → b * t ^ 2 / 8 ≤ C + a * t / 2 := by
      intro t ht
      have h := hbd x (Real.sqrt t) (Real.sqrt_pos.2 ht)
      have hst : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
      rw [hst] at h
      have e : (t : ℂ) / 4 * (2 * f x - iteratedDeriv 2 f x * (t : ℂ) / 2) =
          (t : ℂ) / 2 * f x - ((t : ℂ) ^ 2 / 8) * iteratedDeriv 2 f x := by ring
      rw [e] at h
      have h2 := norm_sub_norm_le (((t : ℂ) ^ 2 / 8) * iteratedDeriv 2 f x) ((t : ℂ) / 2 * f x)
      rw [norm_sub_rev] at h
      have n1 : ‖((t : ℂ) ^ 2 / 8) * iteratedDeriv 2 f x‖ = b * t ^ 2 / 8 := by
        rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
        simp [hb]
        ring
      have n2 : ‖(t : ℂ) / 2 * f x‖ = a * t / 2 := by
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
        simp [ha]
        ring
      rw [n1, n2] at h2
      linarith
    have hb0 : b = 0 := by
      by_contra hb0
      have hbpos : 0 < b := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
      set t := 8 * (a + C + 1) / b + 1 with ht
      have ht1 : 1 ≤ t := by
        have : 0 ≤ 8 * (a + C + 1) / b := by positivity
        linarith
      have hbt : a + C + 1 ≤ b * t / 8 := by
        rw [ht]
        field_simp
        nlinarith [norm_nonneg (f x)]
      have := key t (by linarith)
      nlinarith [norm_nonneg (f x)]
    have key2 : ∀ t : ℝ, 0 < t → a * t / 2 ≤ C := by
      intro t ht
      have h := hbd x (Real.sqrt t) (Real.sqrt_pos.2 ht)
      have hst : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
      have hd : iteratedDeriv 2 f x = 0 := norm_eq_zero.1 hb0
      rw [hst, hd] at h
      have e : (t : ℂ) / 4 * (2 * f x - 0 * (t : ℂ) / 2) = (t : ℂ) / 2 * f x := by ring
      rw [e, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h
      have h' : t / 2 * ‖f x‖ ≤ C := by simpa using h
      rw [ha]
      linarith
    by_contra hne
    have hapos : 0 < a := norm_pos_iff.2 hne
    have := key2 (2 * C / a + 1) (by positivity)
    have e : a * (2 * C / a + 1) / 2 = C + a / 2 := by field_simp
    linarith
  -- identity theorem
  have han : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    refine ⟨((ε / 2 : ℝ) : ℂ), hεU ⟨?_, ?_⟩, hreal _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · simp only [mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
      exact (by positivity : (ε / 2 : ℝ) ≠ 0)
  intro z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ 0) hfreq (mem_univ z)

/-- **L3.** `|∬_ℍ κ/(ζ - z)⁴| ≤ π M/(Im z)²` for `z ∈ 𝕃` (`|ζ - z| ≥ |Im z|` and `∬_{|w| ≥ r} |w|⁻⁴ = π/r²`). -/
theorem s36b_kernel4_le {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4‖ ≤ π * M / z.im ^ 2 := by
  have hzi : z.im < 0 := hz
  have hM : 0 ≤ M := by
    by_contra hM
    push Not at hM
    have h0 : ∀ᵐ w ∂(volume.restrict upperHalf), False :=
      hκM.mono fun w hw => by linarith [norm_nonneg (κ w)]
    have hbot : volume.restrict upperHalf = 0 := by
      rw [← ae_eq_bot]
      exact Filter.eventually_false_iff_eq_bot.1 h0
    rw [Measure.restrict_eq_zero] at hbot
    have hpos : 0 < volume upperHalf :=
      (isOpen_lt continuous_const continuous_im : IsOpen {w : ℂ | 0 < w.im}).measure_pos volume ⟨I, by simp⟩
    exact hpos.ne' hbot
  have hle : ∫⁻ ζ in upperHalf, ENNReal.ofReal ‖κ ζ / (ζ - z) ^ 4‖ ≤
      ∫⁻ ζ in upperHalf, ENNReal.ofReal M * ENNReal.ofReal (‖ζ - z‖⁻¹ ^ 4) := by
    refine lintegral_mono_ae (hκM.mono fun ζ hζ => ?_)
    rw [← ENNReal.ofReal_mul hM, norm_div, norm_pow, div_eq_mul_inv, ← inv_pow]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hζ (by positivity))
  rw [lintegral_const_mul _ (by fun_prop), h36p_c_kernel_area hz] at hle
  have hvol : (volume (ball (0 : ℂ) 1)).toReal = π := by
    rw [Complex.volume_ball]
    simp
  have hfin : ENNReal.ofReal M * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * z.im ^ 2)⁻¹)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top)
  have him2 : 0 < z.im ^ 2 := by nlinarith
  calc ‖∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4‖
      ≤ (∫⁻ ζ in upperHalf, ENNReal.ofReal ‖κ ζ / (ζ - z) ^ 4‖).toReal := norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal M * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * z.im ^ 2)⁻¹))).toReal :=
        ENNReal.toReal_mono hfin hle
    _ = M * (π * (4 * z.im ^ 2)⁻¹) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, hvol,
          ENNReal.toReal_ofReal (by positivity)]
    _ ≤ π * M / z.im ^ 2 := by
        rw [div_eq_mul_inv, mul_inv]
        have h1 : 0 ≤ π * M * (z.im ^ 2)⁻¹ := mul_nonneg (mul_nonneg Real.pi_pos.le hM) (by positivity)
        nlinarith [Real.pi_pos]

/-- **Core.** If `G₊(t) + conj G₋(t) = 0` on a dense set, then `κ₊` and `κ₋` annihilate the kernels `(ζ - z)⁻⁴`,
`z ∈ 𝕃` (the hypothesis of `h36p_orth_integrable`). -/
theorem s36b_core {κp κm : ℂ → ℂ} (hmp : AEStronglyMeasurable κp (volume.restrict upperHalf))
    (hmm : AEStronglyMeasurable κm (volume.restrict upperHalf)) {M : ℝ}
    (hbp : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κp z‖ ≤ M) (hbm : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κm z‖ ≤ M)
    {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {D : Set ℝ} (hD : Dense D)
    (h : ∀ t ∈ D, t ≠ a → t ≠ b → t ≠ c →
      (∫ ζ in upperHalf, κp ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) +
        conj (∫ ζ in upperHalf, κm ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) = 0) :
    ∀ z ∈ lowerHalf, (∫ ζ in upperHalf, κp ζ / (ζ - z) ^ 4) = 0 ∧ (∫ ζ in upperHalf, κm ζ / (ζ - z) ^ 4) = 0 := by
  obtain ⟨hdp, h3p⟩ := s36b_W_deriv hmp hbp hab hac hbc
  obtain ⟨hdm, h3m⟩ := s36b_W_deriv hmm hbm hab hac hbc
  obtain ⟨hE, hEl, hEu⟩ := s36b_glue (s36b_W_cont hmp hbp hab hac hbc) (s36b_W_cont hmm hbm hab hac hbc) hdp hdm
    (s36b_W_bdry hmp hmm hbp hbm hab hac hbc hD h)
  have hbd : ∀ z : ℂ, z.im ≠ 0 →
      ‖iteratedDeriv 3 (fun z : ℂ => if z.im ≤ 0 then (fun z : ℂ => (z - a) * (z - b) * (z - c) *
          ∫ ζ in upperHalf, κp ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) z
        else -conj ((fun z : ℂ => (z - a) * (z - b) * (z - c) *
          ∫ ζ in upperHalf, κm ζ * (1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - z)))) (conj z))) z‖ ≤
        6 * π * M / z.im ^ 2 := by
    intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have hzl : z ∈ lowerHalf := hlt
      rw [hEl z hzl, h3p z hzl, norm_mul]
      have := s36b_kernel4_le hmp hbp hzl
      calc ‖(6 : ℂ)‖ * ‖∫ ζ in upperHalf, κp ζ / (ζ - z) ^ 4‖ ≤ 6 * (π * M / z.im ^ 2) := by
            rw [show ‖(6 : ℂ)‖ = 6 by norm_num]
            exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 6 * π * M / z.im ^ 2 := by ring
    · have hzu : z ∈ upperHalf := hgt
      have hzl : conj z ∈ lowerHalf := by
        show (conj z).im < 0
        rw [Complex.conj_im]
        linarith
      rw [hEu z hzu, norm_neg, Complex.norm_conj, h3m _ hzl, norm_mul]
      have := s36b_kernel4_le hmm hbm hzl
      rw [Complex.conj_im, neg_sq] at this
      calc ‖(6 : ℂ)‖ * ‖∫ ζ in upperHalf, κm ζ / (ζ - conj z) ^ 4‖ ≤ 6 * (π * M / z.im ^ 2) := by
            rw [show ‖(6 : ℂ)‖ = 6 by norm_num]
            exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 6 * π * M / z.im ^ 2 := by ring
  have h0 := s36b_circle_zero hE hbd
  intro z hz
  constructor
  · have e := h0 z
    rw [hEl z hz, h3p z hz] at e
    exact (mul_eq_zero.1 e).resolve_left (by norm_num)
  · have hzu : conj z ∈ upperHalf := by
      show 0 < (conj z).im
      rw [Complex.conj_im]
      have : z.im < 0 := hz
      linarith
    have e := h0 (conj z)
    rw [hEu _ hzu, Complex.conj_conj, h3m z hz, neg_eq_zero, map_eq_zero] at e
    exact (mul_eq_zero.1 e).resolve_left (by norm_num)

/-- **(C) Two-sided Bers approximation** (精英下属4; GL Thm 10 on `ℍ ∪ ℍ*`, 4-pole kernel with finite base points
`a, b, c`): `φ ∈ A(Γ, F)` is approximated on `F` by a finite sum of Poincaré series of rational kernels with poles in
`D ∪ {a, b, c}`, which is small on the mirror domain `conj F`. -/
theorem s36b_bers_two_sided (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {D : Set ℝ}
    (hD : Dense D) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (T : Finset ℝ) (w : ℝ → ℂ), (∀ t ∈ T, t ∈ D ∧ t ≠ a ∧ t ≠ b ∧ t ≠ c) ∧
      phiArea (fun z => φ z - ∑ t ∈ T, w t *
        h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z) F < ε ∧
      phiArea (fun z => ∑ t ∈ T, w t *
        h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z) ((starRingEnd ℂ) '' F) < ε := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hφi : Integrable φ (volume.restrict F) := h36p_b_integrableOn_A hFH hFm hφ
  refine s36b_hb (D := {t : ℝ | t ∈ D ∧ t ≠ a ∧ t ≠ b ∧ t ≠ c})
    (ψ := fun t => h36p_theta Γ (fun ζ : ℂ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) hFm hFH
    (fun t ht => s36b_theta_integrable hΓ hF hab hac hbc ht.2.1 ht.2.2.1 ht.2.2.2) hφi ?_ hε
  intro ν₁ ν₂ hν₁ hν₂ M hb₁ hb₂ hann
  obtain ⟨κp, κm, hmp, hbp, hmm, hbm, hU⟩ := s36b_unfold hΓ hF hν₁ hν₂ (le_max_right M 0)
    (hb₁.mono fun z hz => hz.trans (le_max_left M 0)) (hb₂.mono fun z hz => hz.trans (le_max_left M 0))
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have hcore := s36b_core hmp hmm hbp hbm hab hac hbc hD (fun t ht hta htb htc => by
    have hk := s36b_kernel_mem hΓ hF hab hac hbc hta htb htc
    have h0 := hann t ⟨ht, hta, htb, htc⟩
    rw [(hU _ hk.1 hk.2.1).1, (hU _ hk.1 hk.2.1).2 (s36b_kernel_conj a b c t), ← mul_add] at h0
    exact (mul_eq_zero.1 h0).resolve_left hm)
  obtain ⟨f, hfd, hfA, hfφ⟩ := h36p_theta_surj hΓ hF φ hφ
  have hzero : ∫ ζ in upperHalf, κp ζ * f ζ = 0 :=
    h36p_orth_integrable hmp hbp (fun z hz => (hcore z hz).1) hfd hfA
  have e : ∫ z in F, ν₁ z * φ z = ∫ z in F, ν₁ z * h36p_theta Γ f z :=
    setIntegral_congr_fun hFm (fun z hz => by simp only [hfφ z (hFH hz)])
  rw [e, (hU f hfd hfA).1, hzero, mul_zero]

end LiZhongQC
