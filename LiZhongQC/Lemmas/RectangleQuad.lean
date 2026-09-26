import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Lemmas.SchwarzChristoffelRect

/-!
# Rectangles are topological quadrilaterals

DRAFT skeleton by -93 (not installed). Target leaf: `LiZhongQC/Lemmas/RectangleQuad.lean`. It imports S01
(where `IsTopQuad` lives) and the Schwarz–Christoffel leaf, and is imported by S09 (§9.1 and §9.4 apply
Definition 7.1 to small rectangles regarded as quadrilaterals).

Route. For `0 < k < 1` the Schwarz–Christoffel map `scMap k` sends `ℍ` conformally onto
`R(0, a_k, a_k + i b_k, i b_k)`, homeomorphically on the closures, with `-1/k, -1, 1, 1/k ↦` the four
vertices.
- The ratio `a_k / b_k = K(k') / (2 K(k))` is continuous on `(0, 1)`, tends to `∞` as `k → 0⁺` and to
  `0` as `k → 1⁻`. By the intermediate value theorem every `m > 0` is attained.
- For `R(0, a, a+ib, ib)` pick `k` with `a_k / b_k = a / b`. The scaling `w ↦ (a / a_k) w` then maps
  `R(a_k, b_k)` onto `R(a, b)`, and inverting gives the conformal map of the rectangle onto `ℍ` that
  `IsTopQuad` asks for.
-/

set_option autoImplicit false

open Complex Set Filter Topology

noncomputable section

namespace LiZhongQC

/-! ### The side lengths as functions of `k` -/

/-! ### Helpers: the integrals `∫₀¹ dt/√(t(1-t) P(k,t))`

Both side lengths are transformed by affine substitutions into integrals over `(0,1)` of
`1/√(t(1-t) P(k,t))` with `P` a positive polynomial in `t`:
`x = 2t - 1` gives `b_k = ∫₀¹ dt/√(t(1-t) P_B(k,t))`, `P_B = (1 - k(2t-1))(1 + k(2t-1))`, and
`x = 1 + (1/k - 1) t` gives `a_k = ∫₀¹ dt/√(t(1-t) P_A(k,t))`, `P_A = ((1-k)t + 2k)(1+k+(1-k)t)`.
The integrable majorant `1/√(t(1-t))` (the derivative of `arcsin (2t-1)`) gives integrability,
positivity, dominated continuity in `k`, and the elementary bounds behind the two limits. -/

open MeasureTheory

/-- `t ↦ 1/√(t(1-t))` is integrable on `(0, 1]`: it is the derivative of `arcsin (2t - 1)`. -/
theorem rq_integrableOn_sqrt_weight :
    IntegrableOn (fun t : ℝ => 1 / Real.sqrt (t * (1 - t))) (Ioc 0 1) := by
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun t => Real.arcsin (2 * t - 1))
    ?_ ?_ ?_
  · exact Real.continuous_arcsin.comp_continuousOn
      ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
  · intro t ht
    have h1 : 2 * t - 1 ≠ -1 := by
      intro h
      linarith [ht.1]
    have h2 : 2 * t - 1 ≠ 1 := by
      intro h
      linarith [ht.2]
    have hd : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const 1
    have h0 := (Real.hasDerivAt_arcsin h1 h2).comp t hd
    have h : HasDerivAt (fun t : ℝ => Real.arcsin (2 * t - 1))
        (1 / Real.sqrt (1 - (2 * t - 1) ^ 2) * 2) t := h0
    refine h.congr_deriv ?_
    have e : 1 - (2 * t - 1) ^ 2 = 4 * (t * (1 - t)) := by ring
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hpos : 0 < Real.sqrt (t * (1 - t)) :=
      Real.sqrt_pos.2 (mul_pos ht.1 (by linarith [ht.2]))
    rw [e, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    field_simp
  · intro t _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

/-- The majorant: for `t ∈ [0,1]` and `p ≥ m > 0`, `1/√(t(1-t)p) ≤ (1/√m) · 1/√(t(1-t))`. -/
theorem rq_bound {t p m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hm : 0 < m) (hp : m ≤ p) :
    1 / Real.sqrt (t * (1 - t) * p) ≤ (1 / Real.sqrt m) * (1 / Real.sqrt (t * (1 - t))) := by
  have h0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.2 ht.2)
  have e : 1 / (Real.sqrt (t * (1 - t)) * Real.sqrt p) =
      (1 / Real.sqrt (t * (1 - t))) * (1 / Real.sqrt p) := by
    rw [div_mul_div_comm, one_mul]
  rw [Real.sqrt_mul h0, e, mul_comm (1 / Real.sqrt m)]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (Real.sqrt_pos.2 hm) (Real.sqrt_le_sqrt hp))
    (div_nonneg zero_le_one (Real.sqrt_nonneg _))

theorem rq_measurable {P : ℝ → ℝ} (hP : Measurable P) :
    Measurable fun t : ℝ => 1 / Real.sqrt (t * (1 - t) * P t) :=
  measurable_const.div (Real.continuous_sqrt.measurable.comp
    ((measurable_id.mul (measurable_const.sub measurable_id)).mul hP))

/-- Integrability of `1/√(t(1-t) P t)` on `[0,1]` when `P ≥ m > 0` is measurable. -/
theorem rq_intervalIntegrable {P : ℝ → ℝ} {m : ℝ} (hm : 0 < m) (hmeas : Measurable P)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ P t) :
    IntervalIntegrable (fun t => 1 / Real.sqrt (t * (1 - t) * P t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine (rq_integrableOn_sqrt_weight.const_mul (1 / Real.sqrt m)).mono'
    (rq_measurable hmeas).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  rw [Real.norm_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
  exact rq_bound ⟨ht.1.le, ht.2⟩ hm (hP t ⟨ht.1.le, ht.2⟩)

/-- Positivity of `∫₀¹ dt/√(t(1-t) P t)`. -/
theorem rq_integral_pos {P : ℝ → ℝ} {m : ℝ} (hm : 0 < m) (hmeas : Measurable P)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ P t) :
    0 < ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * P t) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (rq_intervalIntegrable hm hmeas hP)
    (fun t ht => ?_) one_pos
  refine div_pos one_pos (Real.sqrt_pos.2 ?_)
  exact mul_pos (mul_pos ht.1 (by linarith [ht.2])) (hm.trans_le (hP t ⟨ht.1.le, ht.2.le⟩))

/-- Dominated continuity in the parameter: if `P(·, t)` is continuous within `s` at `k₀` and
`P ≥ m > 0` on `[0,1]` for `k` near `k₀`, then `k ↦ ∫₀¹ dt/√(t(1-t) P(k,t))` is continuous
within `s` at `k₀`. -/
theorem rq_continuousWithinAt_integral {P : ℝ → ℝ → ℝ} {s : Set ℝ} {k₀ : ℝ} (hk₀ : k₀ ∈ s)
    (hmeas : ∀ k, Measurable (P k))
    (hcont : ∀ t ∈ Ioc (0 : ℝ) 1, ContinuousWithinAt (fun k => P k t) s k₀)
    (hbd : ∃ m : ℝ, 0 < m ∧ ∀ᶠ k in 𝓝[s] k₀, ∀ t ∈ Icc (0 : ℝ) 1, m ≤ P k t) :
    ContinuousWithinAt (fun k => ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * P k t)) s k₀ := by
  obtain ⟨m, hm, hev⟩ := hbd
  have hk₀m : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ P k₀ t := mem_of_mem_nhdsWithin hk₀ hev
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun t => (1 / Real.sqrt m) * (1 / Real.sqrt (t * (1 - t)))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun k => (rq_measurable (hmeas k)).aestronglyMeasurable
  · filter_upwards [hev] with k hk
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
    exact rq_bound ⟨ht.1.le, ht.2⟩ hm (hk t ⟨ht.1.le, ht.2⟩)
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact rq_integrableOn_sqrt_weight.const_mul _
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · have : (fun k => 1 / Real.sqrt (t * (1 - t) * P k t)) = fun _ => 0 := by
        funext k
        rw [h1]
        simp
      rw [this]
      exact continuousWithinAt_const
    · have hpos : 0 < t * (1 - t) * P k₀ t :=
        mul_pos (mul_pos ht.1 (by linarith)) (hm.trans_le (hk₀m t ⟨ht.1.le, ht.2⟩))
      refine continuousWithinAt_const.div ?_ (Real.sqrt_pos.2 hpos).ne'
      exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
        (continuousWithinAt_const.mul (hcont t ht))

/-- `P_A(k,t) = ((1-k)t + 2k)(1 + k + (1-k)t)`: `a_k = ∫₀¹ dt/√(t(1-t) P_A(k,t))`. -/
def rq_PA (k t : ℝ) : ℝ := ((1 - k) * t + 2 * k) * (1 + k + (1 - k) * t)

/-- `P_B(k,t) = (1 - k(2t-1))(1 + k(2t-1))`: `b_k = ∫₀¹ dt/√(t(1-t) P_B(k,t))`. -/
def rq_PB (k t : ℝ) : ℝ := (1 - k * (2 * t - 1)) * (1 + k * (2 * t - 1))

theorem rq_continuous_PA (t : ℝ) : Continuous fun k => rq_PA k t := by
  unfold rq_PA
  fun_prop

theorem rq_continuous_PB (t : ℝ) : Continuous fun k => rq_PB k t := by
  unfold rq_PB
  fun_prop

theorem rq_measurable_PA (k : ℝ) : Measurable (rq_PA k) :=
  (by unfold rq_PA; fun_prop : Continuous (rq_PA k)).measurable

theorem rq_measurable_PB (k : ℝ) : Measurable (rq_PB k) :=
  (by unfold rq_PB; fun_prop : Continuous (rq_PB k)).measurable

theorem rq_PA_ge {k t : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    2 * k * (1 + k) ≤ rq_PA k t := by
  unfold rq_PA
  have h1 : 0 ≤ (1 - k) * t := mul_nonneg (by linarith) ht.1
  nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 1 + k), mul_nonneg h1 h1,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * k) h1]

theorem rq_PA_le {k t : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    rq_PA k t ≤ 2 * (t + 2 * k) := by
  unfold rq_PA
  have h1 : (1 - k) * t + 2 * k ≤ t + 2 * k := by nlinarith [ht.1]
  have h2 : 1 + k + (1 - k) * t ≤ 2 := by nlinarith [ht.2]
  calc ((1 - k) * t + 2 * k) * (1 + k + (1 - k) * t) ≤ (t + 2 * k) * 2 :=
        mul_le_mul h1 h2 (by nlinarith [ht.1]) (by linarith [ht.1])
    _ = 2 * (t + 2 * k) := by ring

theorem rq_PB_ge {k t : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - k) ^ 2 ≤ rq_PB k t := by
  unfold rq_PB
  have h1 : 1 - k ≤ 1 - k * (2 * t - 1) := by nlinarith [ht.2]
  have h2 : 1 - k ≤ 1 + k * (2 * t - 1) := by nlinarith [ht.1]
  calc (1 - k) ^ 2 = (1 - k) * (1 - k) := sq _
    _ ≤ _ := mul_le_mul h1 h2 (by linarith) (by linarith)

theorem rq_PB_le {k t : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    rq_PB k t ≤ 2 * ((1 - k) + 2 * (1 - t)) := by
  unfold rq_PB
  have h1 : 1 - k * (2 * t - 1) ≤ (1 - k) + 2 * (1 - t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk₁) (sub_nonneg.2 ht.2)]
  have h2 : 1 + k * (2 * t - 1) ≤ 2 := by
    nlinarith [mul_le_mul hk₁ (by linarith [ht.2] : 2 * t - 1 ≤ 1) (by linarith [ht.1]) zero_le_one]
  calc (1 - k * (2 * t - 1)) * (1 + k * (2 * t - 1)) ≤ ((1 - k) + 2 * (1 - t)) * 2 :=
        mul_le_mul h1 h2 (by nlinarith [ht.1]) (by linarith [ht.2])
    _ = 2 * ((1 - k) + 2 * (1 - t)) := by ring

/-- `b_k = ∫₀¹ dt/√(t(1-t) P_B(k,t))` (substitution `x = 2t - 1`). -/
theorem rq_scSideB_eq (k : ℝ) :
    scSideB k = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * rq_PB k t) := by
  unfold scSideB
  set f : ℝ → ℝ := fun x => 1 / Real.sqrt ((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)) with hf
  have h := intervalIntegral.integral_comp_mul_add f (a := 0) (b := 1) (c := 2) two_ne_zero (-1)
  rw [show (2 : ℝ) * 0 + -1 = -1 by norm_num, show (2 : ℝ) * 1 + -1 = 1 by norm_num] at h
  rw [show (∫ x in (-1 : ℝ)..1, f x) = (2 : ℝ) • ∫ t in (0 : ℝ)..1, f (2 * t + -1) by
    rw [h, smul_inv_smul₀ two_ne_zero], smul_eq_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hf]
  have e : (1 - (2 * t + -1) ^ 2) * (1 - k ^ 2 * (2 * t + -1) ^ 2) =
      4 * (t * (1 - t) * rq_PB k t) := by
    unfold rq_PB
    ring
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4, mul_one_div, div_mul_eq_div_div,
    div_self two_ne_zero]

/-- `a_k = ∫₀¹ dt/√(t(1-t) P_A(k,t))` (substitution `x = 1 + (1/k - 1) t`). -/
theorem rq_scSideA_eq {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * rq_PA k t) := by
  have hk : k ≠ 0 := hk₀.ne'
  set c : ℝ := 1 / k - 1 with hc
  have hcpos : 0 < c := by
    rw [hc]
    linarith [one_lt_one_div hk₀ hk₁]
  unfold scSideA
  set f : ℝ → ℝ := fun x => 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) with hf
  have h := intervalIntegral.integral_comp_mul_add f (a := 0) (b := 1) hcpos.ne' 1
  rw [show c * 0 + 1 = 1 by ring, show c * 1 + 1 = 1 / k by rw [hc]; ring] at h
  rw [show (∫ x in (1 : ℝ)..(1 / k), f x) = c • ∫ t in (0 : ℝ)..1, f (c * t + 1) by
    rw [h, smul_inv_smul₀ hcpos.ne'], smul_eq_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hf]
  have e : ((c * t + 1) ^ 2 - 1) * (1 - k ^ 2 * (c * t + 1) ^ 2) =
      c ^ 2 * (t * (1 - t) * rq_PA k t) := by
    unfold rq_PA
    rw [hc]
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hcpos.le, mul_one_div, div_mul_eq_div_div,
    div_self hcpos.ne']

theorem rq_scSideA_pos {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) : 0 < scSideA k := by
  rw [rq_scSideA_eq hk₀ hk₁]
  exact rq_integral_pos (by positivity) (rq_measurable_PA k) fun t ht => rq_PA_ge hk₀ hk₁ ht

theorem rq_scSideB_pos {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) : 0 < scSideB k := by
  rw [rq_scSideB_eq]
  exact rq_integral_pos (pow_pos (by linarith) 2) (rq_measurable_PB k) fun t ht =>
    rq_PB_ge hk₀.le hk₁ ht

/-- The reference integral `J = ∫₀¹ dt/√(t(1-t))` (in fact `J = π`, not needed). -/
theorem rq_J_pos : 0 < ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t)) := by
  have h := rq_integral_pos (P := fun _ => 1) one_pos measurable_const fun _ _ => le_rfl
  simpa only [mul_one] using h

theorem rq_intervalIntegrable_weight :
    IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (t * (1 - t))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact rq_integrableOn_sqrt_weight

/-- `a_k ≥ (1/√2) · log ((1+2k)/(2k))` (compare the integrand with `1/(√2 (t + 2k))`). -/
theorem rq_scSideA_ge {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    (1 / Real.sqrt 2) * Real.log ((1 + 2 * k) / (2 * k)) ≤ scSideA k := by
  rw [rq_scSideA_eq hk₀ hk₁]
  have hint : ∫ t in (0 : ℝ)..1, 1 / (Real.sqrt 2 * (t + 2 * k)) =
      (1 / Real.sqrt 2) * Real.log ((1 + 2 * k) / (2 * k)) := by
    have e : (fun t : ℝ => 1 / (Real.sqrt 2 * (t + 2 * k))) =
        fun t => (1 / Real.sqrt 2) * (t + 2 * k)⁻¹ := by
      funext t
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹) (2 * k), zero_add,
      integral_inv_of_pos (by positivity) (by positivity)]
  rw [← hint]
  have hcont : ContinuousOn (fun t : ℝ => 1 / (Real.sqrt 2 * (t + 2 * k))) (uIcc 0 1) := by
    refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.add continuousOn_const))
      fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have : 0 < t + 2 * k := by linarith [ht.1]
    positivity
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hcont.intervalIntegrable
    (rq_intervalIntegrable (by positivity) (rq_measurable_PA k) fun t ht => rq_PA_ge hk₀ hk₁ ht)
    fun t ht => ?_
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hpos : 0 < t * (1 - t) * rq_PA k t :=
    mul_pos (mul_pos ht.1 (by linarith [ht.2]))
      ((show (0 : ℝ) < 2 * k * (1 + k) by positivity).trans_le (rq_PA_ge hk₀ hk₁ ht'))
  have hle : t * (1 - t) * rq_PA k t ≤ 2 * (t + 2 * k) ^ 2 := by
    have hP0 : 0 ≤ rq_PA k t :=
      le_trans (show (0 : ℝ) ≤ 2 * k * (1 + k) by positivity) (rq_PA_ge hk₀ hk₁ ht')
    have h1 : t * (1 - t) ≤ t * 1 := mul_le_mul_of_nonneg_left (by linarith [ht.1]) ht.1.le
    have h2 : t * (1 - t) * rq_PA k t ≤ t * 1 * (2 * (t + 2 * k)) :=
      mul_le_mul h1 (rq_PA_le hk₀ hk₁ ht') hP0 (by linarith [ht.1])
    nlinarith [h2, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * k) (by linarith [ht.1] : (0 : ℝ) ≤ t + 2 * k)]
  have hsq : Real.sqrt (t * (1 - t) * rq_PA k t) ≤ Real.sqrt 2 * (t + 2 * k) := by
    calc Real.sqrt (t * (1 - t) * rq_PA k t) ≤ Real.sqrt (2 * (t + 2 * k) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = Real.sqrt 2 * (t + 2 * k) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith [ht.1])]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hpos) hsq

/-- `b_k ≤ J / (1 - k)`. -/
theorem rq_scSideB_le {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideB k ≤ (1 / (1 - k)) * ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t)) := by
  rw [rq_scSideB_eq, ← intervalIntegral.integral_const_mul]
  have hm : 0 < (1 - k) ^ 2 := pow_pos (by linarith) 2
  refine intervalIntegral.integral_mono_on zero_le_one
    (rq_intervalIntegrable hm (rq_measurable_PB k) fun t ht => rq_PB_ge hk₀.le hk₁ ht)
    (rq_intervalIntegrable_weight.const_mul _) fun t ht => ?_
  have h := rq_bound ht hm (rq_PB_ge hk₀.le hk₁ ht)
  rwa [Real.sqrt_sq (by linarith)] at h

/-- `a_k ≤ J / √(2k(1+k))`. -/
theorem rq_scSideA_le {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k ≤ (1 / Real.sqrt (2 * k * (1 + k))) * ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t)) := by
  rw [rq_scSideA_eq hk₀ hk₁, ← intervalIntegral.integral_const_mul]
  have hm : 0 < 2 * k * (1 + k) := by positivity
  exact intervalIntegral.integral_mono_on zero_le_one
    (rq_intervalIntegrable hm (rq_measurable_PA k) fun t ht => rq_PA_ge hk₀ hk₁ ht)
    (rq_intervalIntegrable_weight.const_mul _) fun t ht => rq_bound ht hm (rq_PA_ge hk₀ hk₁ ht)

/-- `b_k ≥ (1/2) · log ((2-k)/(1-k))` (compare the integrand on `[1/2, 1]` with
`1/((1-k) + 2(1-t))`). -/
theorem rq_scSideB_ge {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    (1 / 2) * Real.log ((2 - k) / (1 - k)) ≤ scSideB k := by
  rw [rq_scSideB_eq]
  have hm : 0 < (1 - k) ^ 2 := pow_pos (by linarith) 2
  have hfi : IntervalIntegrable (fun t => 1 / Real.sqrt (t * (1 - t) * rq_PB k t)) volume 0 1 :=
    rq_intervalIntegrable hm (rq_measurable_PB k) fun t ht => rq_PB_ge hk₀.le hk₁ ht
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hfi.mono_set (uIcc_subset_uIcc_left (by norm_num : (1 / 2 : ℝ) ∈ uIcc 0 1)))
    (hfi.mono_set (uIcc_subset_uIcc_right (by norm_num : (1 / 2 : ℝ) ∈ uIcc 0 1)))
  have hleft : 0 ≤ ∫ t in (0 : ℝ)..(1 / 2), 1 / Real.sqrt (t * (1 - t) * rq_PB k t) :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ =>
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
  -- the explicit integral on `[1/2, 1]`
  have hint : ∫ t in (1 / 2 : ℝ)..1, 1 / ((1 - k) + 2 * (1 - t)) =
      (1 / 2) * Real.log ((2 - k) / (1 - k)) := by
    have e : (fun t : ℝ => 1 / ((1 - k) + 2 * (1 - t))) = fun t => (-2 * t + (3 - k))⁻¹ := by
      funext t
      rw [one_div]
      congr 1
      ring
    rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x⁻¹) (by norm_num : (-2 : ℝ) ≠ 0)
      (3 - k), show (-2 : ℝ) * (1 / 2) + (3 - k) = 2 - k by ring,
      show (-2 : ℝ) * 1 + (3 - k) = 1 - k by ring, intervalIntegral.integral_symm,
      integral_inv_of_pos (by linarith) (by linarith), smul_eq_mul]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / ((1 - k) + 2 * (1 - t))) (uIcc (1 / 2) 1) := by
    refine continuousOn_const.div
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
      fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    have : 0 < (1 - k) + 2 * (1 - t) := by linarith [ht.2]
    exact this.ne'
  have hmono : ∫ t in (1 / 2 : ℝ)..1, 1 / ((1 - k) + 2 * (1 - t)) ≤
      ∫ t in (1 / 2 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * rq_PB k t) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hcont.intervalIntegrable
      (hfi.mono_set (uIcc_subset_uIcc_right (by norm_num : (1 / 2 : ℝ) ∈ uIcc 0 1)))
      fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
    have ht'' : t ∈ Icc (1 / 2 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hpos : 0 < t * (1 - t) * rq_PB k t :=
      mul_pos (mul_pos (by linarith [ht.1]) (by linarith [ht.2]))
        (hm.trans_le (rq_PB_ge hk₀.le hk₁ ht'))
    have hle : t * (1 - t) * rq_PB k t ≤ ((1 - k) + 2 * (1 - t)) ^ 2 := by
      have hP0 : 0 ≤ rq_PB k t := hm.le.trans (rq_PB_ge hk₀.le hk₁ ht')
      have h1 : t * (1 - t) ≤ 1 * (1 - t) :=
        mul_le_mul_of_nonneg_right ht.2.le (by linarith [ht.2])
      have h2 : t * (1 - t) * rq_PB k t ≤ 1 * (1 - t) * (2 * ((1 - k) + 2 * (1 - t))) :=
        mul_le_mul h1 (rq_PB_le hk₀.le hk₁.le ht'') hP0 (by linarith [ht.2])
      nlinarith [h2, mul_nonneg (by linarith [ht.2, hk₁] : (0 : ℝ) ≤ (1 - k) + 2 * (1 - t))
        (by linarith : (0 : ℝ) ≤ 1 - k)]
    have hsq : Real.sqrt (t * (1 - t) * rq_PB k t) ≤ (1 - k) + 2 * (1 - t) := by
      calc Real.sqrt (t * (1 - t) * rq_PB k t) ≤ Real.sqrt (((1 - k) + 2 * (1 - t)) ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = (1 - k) + 2 * (1 - t) := Real.sqrt_sq (by linarith [ht.2])
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hpos) hsq
  rw [← hsplit, ← hint]
  linarith

theorem continuousOn_scSideA : ContinuousOn scSideA (Ioo 0 1) := by
  intro k₀ hk₀
  have hcongr : EqOn scSideA
      (fun k => ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * rq_PA k t)) (Ioo 0 1) :=
    fun k hk => rq_scSideA_eq hk.1 hk.2
  refine (rq_continuousWithinAt_integral hk₀ rq_measurable_PA
    (fun t _ => (rq_continuous_PA t).continuousWithinAt) ?_).congr hcongr (hcongr hk₀)
  refine ⟨2 * (k₀ / 2) * (1 + k₀ / 2), by have := hk₀.1; positivity, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (isOpen_Ioo.mem_nhds ⟨half_lt_self hk₀.1, hk₀.2⟩ : Ioo (k₀ / 2) 1 ∈ 𝓝 k₀)] with k hk t ht
  have hk0 : 0 < k := by linarith [hk.1, hk₀.1]
  refine le_trans ?_ (rq_PA_ge hk0 hk.2 ht)
  nlinarith [hk.1, hk₀.1]

theorem continuousOn_scSideB : ContinuousOn scSideB (Ioo 0 1) := by
  intro k₀ hk₀
  have hcongr : EqOn scSideB
      (fun k => ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t) * rq_PB k t)) (Ioo 0 1) :=
    fun k _ => rq_scSideB_eq k
  refine (rq_continuousWithinAt_integral hk₀ rq_measurable_PB
    (fun t _ => (rq_continuous_PB t).continuousWithinAt) ?_).congr hcongr (hcongr hk₀)
  refine ⟨(1 - (k₀ + 1) / 2) ^ 2, pow_pos (by linarith [hk₀.2]) 2, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (isOpen_Ioo.mem_nhds ⟨hk₀.1, by linarith [hk₀.2]⟩ : Ioo 0 ((k₀ + 1) / 2) ∈ 𝓝 k₀)]
    with k hk t ht
  refine le_trans ?_ (rq_PB_ge hk.1.le (by linarith [hk.2, hk₀.2]) ht)
  exact pow_le_pow_left₀ (by linarith [hk₀.2]) (by linarith [hk.2]) 2

/-- `a_k / b_k → ∞` as `k → 0⁺` (`a_k ~ log (4/k)`, `b_k → π`). -/
theorem tendsto_scSideRatio_zero :
    Tendsto (fun k => scSideA k / scSideB k) (𝓝[>] 0) atTop := by
  set J := ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t)) with hJ
  have hJpos : 0 < J := rq_J_pos
  -- `a_k ≥ (1/√2)(-log 2 - log k)` and `b_k ≤ 2J` for `k < 1/2`
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ),
      ((1 / Real.sqrt 2) * (-Real.log 2 - Real.log k)) / (2 * J) ≤ scSideA k / scSideB k := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with k hk
    have hk0 : 0 < k := hk.1
    have hk₁ : k < 1 := by linarith [hk.2]
    have hB : scSideB k ≤ 2 * J := by
      refine (rq_scSideB_le hk.1 hk₁).trans (mul_le_mul_of_nonneg_right ?_ hJpos.le)
      rw [div_le_iff₀ (by linarith [hk.2])]
      linarith [hk.2]
    have hA : (1 / Real.sqrt 2) * (-Real.log 2 - Real.log k) ≤ scSideA k := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (rq_scSideA_ge hk.1 hk₁)
      have h1 : Real.log (1 / (2 * k)) ≤ Real.log ((1 + 2 * k) / (2 * k)) :=
        Real.log_le_log (by positivity)
          (div_le_div_of_nonneg_right (by linarith [hk.1]) (by positivity))
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hk.1.ne'] at h1
      linarith
    calc ((1 / Real.sqrt 2) * (-Real.log 2 - Real.log k)) / (2 * J)
        ≤ scSideA k / (2 * J) := div_le_div_of_nonneg_right hA (by positivity)
      _ ≤ scSideA k / scSideB k :=
          div_le_div_of_nonneg_left (rq_scSideA_pos hk.1 hk₁).le (rq_scSideB_pos hk.1 hk₁) hB
  refine tendsto_atTop_mono' _ hev ?_
  refine Tendsto.atTop_div_const (by positivity) (Tendsto.const_mul_atTop (by positivity) ?_)
  have h2 : Tendsto (fun k : ℝ => -Real.log k) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact (tendsto_atTop_add_const_left _ (-Real.log 2) h2).congr fun k => by ring

/-- `a_k / b_k → 0` as `k → 1⁻` (`a_k → π/2`, `b_k → ∞`). -/
theorem tendsto_scSideRatio_one :
    Tendsto (fun k => scSideA k / scSideB k) (𝓝[<] 1) (𝓝 0) := by
  set J := ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (t * (1 - t)) with hJ
  have hJpos : 0 < J := rq_J_pos
  -- the majorant `J / ((1/2)(-log (1-k)))` tends to `0`
  have hM : Tendsto (fun k : ℝ => J / ((1 / 2) * (-Real.log (1 - k)))) (𝓝[<] 1) (𝓝 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop (by norm_num) ?_)
    have h1 : Tendsto (fun k : ℝ => 1 - k) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun k : ℝ => 1 - k) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with k hk
        exact sub_pos.2 (mem_Iio.1 hk)
    exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with k hk
    have hk₀ : 0 < k := by linarith [hk.1]
    exact div_nonneg (rq_scSideA_pos hk₀ hk.2).le (rq_scSideB_pos hk₀ hk.2).le
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with k hk
    have hk₀ : 0 < k := by linarith [hk.1]
    have hA : scSideA k ≤ J := by
      refine (rq_scSideA_le hk₀ hk.2).trans ?_
      have h1 : 1 ≤ Real.sqrt (2 * k * (1 + k)) := Real.one_le_sqrt.2 (by nlinarith [hk.1])
      calc (1 / Real.sqrt (2 * k * (1 + k))) * J ≤ 1 * J :=
            mul_le_mul_of_nonneg_right (by rw [div_le_one (by linarith)]; exact h1) hJpos.le
        _ = J := one_mul J
    have hlog : Real.log (1 - k) < 0 := Real.log_neg (by linarith [hk.2]) (by linarith [hk.1])
    have hM' : 0 < (1 / 2) * (-Real.log (1 - k)) := by linarith
    have hB : (1 / 2) * (-Real.log (1 - k)) ≤ scSideB k := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (rq_scSideB_ge hk₀ hk.2)
      have h1 : Real.log (1 / (1 - k)) ≤ Real.log ((2 - k) / (1 - k)) :=
        Real.log_le_log (div_pos one_pos (by linarith [hk.2]))
          (div_le_div_of_nonneg_right (by linarith [hk.2]) (by linarith [hk.2]))
      rw [one_div, Real.log_inv] at h1
      exact h1
    exact div_le_div₀ hJpos.le hA hM' hB

/-- Every ratio is attained. -/
theorem exists_scSideRatio_eq {m : ℝ} (hm : 0 < m) :
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧ scSideA k / scSideB k = m := by
  have hcont : ContinuousOn (fun k => scSideA k / scSideB k) (Ioo 0 1) :=
    continuousOn_scSideA.div continuousOn_scSideB fun k hk => (rq_scSideB_pos hk.1 hk.2).ne'
  -- a point with ratio `> m` near `0` and a point with ratio `< m` near `1`
  obtain ⟨k₁, hk₁, hm₁⟩ : ∃ k₁ ∈ Ioo (0 : ℝ) 1, m < scSideA k₁ / scSideB k₁ := by
    obtain ⟨k, hk1, hk2⟩ := ((tendsto_scSideRatio_zero.eventually (eventually_gt_atTop m)).and
      (Ioo_mem_nhdsGT zero_lt_one)).exists
    exact ⟨k, hk2, hk1⟩
  obtain ⟨k₂, hk₂, hm₂⟩ : ∃ k₂ ∈ Ioo (0 : ℝ) 1, scSideA k₂ / scSideB k₂ < m := by
    obtain ⟨k, hk1, hk2⟩ := ((tendsto_scSideRatio_one.eventually (gt_mem_nhds hm)).and
      (Ioo_mem_nhdsLT zero_lt_one)).exists
    exact ⟨k, hk2, hk1⟩
  have hsub : uIcc k₁ k₂ ⊆ Ioo 0 1 := ordConnected_Ioo.uIcc_subset hk₁ hk₂
  have hmem : m ∈ uIcc (scSideA k₁ / scSideB k₁) (scSideA k₂ / scSideB k₂) := by
    rw [uIcc_of_ge (hm₂.trans hm₁).le]
    exact ⟨hm₂.le, hm₁.le⟩
  obtain ⟨k, hk, hkm⟩ := intermediate_value_uIcc (hcont.mono hsub) hmem
  exact ⟨k, (hsub hk).1, (hsub hk).2, hkm⟩

/-! ### Rectangles as quadrilaterals -/

/-! ### Helpers: transporting the Schwarz–Christoffel data to `R(0, a, a+bi, bi)` -/

/-- The scaling `w ↦ c w`, `c > 0`, maps `R(a', b')` onto `R(c a', c b')`. -/
theorem rq_image_scale {c a' b' : ℝ} (hc : 0 < c) :
    (fun w : ℂ => (c : ℂ) * w) '' rectangle a' b' = rectangle (c * a') (c * b') := by
  ext u
  simp only [mem_image, rectangle, mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    exact ⟨mul_pos hc h1, mul_lt_mul_of_pos_left h2 hc, mul_pos hc h3,
      mul_lt_mul_of_pos_left h4 hc⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hci : 0 < c⁻¹ := inv_pos.2 hc
    refine ⟨((c⁻¹ : ℝ) : ℂ) * u, ?_, ?_⟩
    · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, add_zero]
      refine ⟨mul_pos hci h1, ?_, mul_pos hci h3, ?_⟩
      · rw [inv_mul_lt_iff₀ hc]
        exact h2
      · rw [inv_mul_lt_iff₀ hc]
        exact h4
    · rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_mul]

theorem rq_isConformalOnto_scale {c a' b' : ℝ} (hc : 0 < c) :
    IsConformalOnto (fun w : ℂ => (c : ℂ) * w) (rectangle a' b') (rectangle (c * a') (c * b')) :=
  ⟨(differentiable_id.const_mul _).differentiableOn,
    fun _ _ _ _ h => mul_left_cancel₀ (by exact_mod_cast hc.ne') h, rq_image_scale hc⟩

/-- A boundary extension of a conformal map `f : U → V` maps `∂U` onto `∂V` in `ℂ̄` (copy of
`IsHomeoExtension.image_frontier` from `Lemmas/Quadrilateral.lean`, which is not imported here). -/
theorem rq_image_frontier {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hU : IsOpen U) (hV : IsOpen V) (hfUV : f '' U = V) (hF : IsHomeoExtension f U V F) :
    F '' frontier (toExt U) = frontier (toExt V) := by
  obtain ⟨hFf, -, hinj, himg⟩ := hF
  have hUo : IsOpen (toExt U) := OnePoint.isOpen_image_coe.2 hU
  have hVo : IsOpen (toExt V) := OnePoint.isOpen_image_coe.2 hV
  have hFU : F '' toExt U = toExt V := by
    rw [← hfUV]
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, mem_image_of_mem f hz, (hFf z hz).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, hFf z hz⟩
  rw [hUo.frontier_eq, hVo.frontier_eq, hinj.image_diff_subset subset_closure, himg, hFU]

/-- The Schwarz–Christoffel map onto `R(0, a, a+bi, bi)`: for `k` with `a_k/b_k = a/b` and
`c = a/a_k`, `G = (c ·) ∘ scMap k` is conformal `ℍ → R(a,b)`, extends to a homeomorphism
`Gext = mobiusExt c 0 0 1 ∘ scMapExt k` of the closures, and sends the prevertices to the vertices
`0, a, a+bi, bi`. -/
theorem rq_exists_scMap_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (k : ℝ) (G : ℂ → ℂ) (Gext : ExtPlane → ExtPlane), 0 < k ∧ k < 1 ∧
      IsConformalOnto G upperHalf (rectangle a b) ∧
      IsHomeoExtension G upperHalf (rectangle a b) Gext ∧
      ∀ j : Fin 4, Gext (((scPrevertex k j : ℝ) : ℂ) : ExtPlane) = rectVert a b j := by
  obtain ⟨k, hk₀, hk₁, hk⟩ := exists_scSideRatio_eq (div_pos ha hb)
  have hA := rq_scSideA_pos hk₀ hk₁
  have hB := rq_scSideB_pos hk₀ hk₁
  set c : ℝ := a / scSideA k with hc
  have hcpos : 0 < c := div_pos ha hA
  have hca : c * scSideA k = a := div_mul_cancel₀ a hA.ne'
  have hcb : c * scSideB k = b := by
    rw [div_eq_div_iff hB.ne' hb.ne'] at hk
    rw [hc]
    field_simp
    linear_combination -hk
  have hca' : (c : ℂ) * (scSideA k : ℂ) = a := by rw [← Complex.ofReal_mul, hca]
  have hcb' : (c : ℂ) * (scSideB k : ℂ) = b := by rw [← Complex.ofReal_mul, hcb]
  -- the conformal map
  have hGc : IsConformalOnto ((fun w : ℂ => (c : ℂ) * w) ∘ scMap k) upperHalf (rectangle a b) := by
    have h := (rq_isConformalOnto_scale (a' := scSideA k) (b' := scSideB k) hcpos).comp
      (isConformalOnto_scMap hk₀ hk₁)
    rwa [hca, hcb] at h
  -- the scaling as a homeomorphism of `ℂ̄`
  have hdet : (c : ℂ) * 1 - 0 * 0 ≠ 0 := by simpa using hcpos.ne'
  set e := mobiusHomeomorph (c : ℂ) 0 0 1 hdet with he
  have he_coe : ∀ w : ℂ, e (w : ExtPlane) = (((c : ℂ) * w : ℂ) : ExtPlane) := fun w => by
    rw [he, mobiusHomeomorph_apply, mobiusExt_coe (by simp : (0 : ℂ) * w + 1 ≠ 0)]
    simp [mobiusFn]
  have himg : e '' toExt (rectangle (scSideA k) (scSideB k)) = toExt (rectangle a b) := by
    rw [← hca, ← hcb, ← rq_image_scale hcpos]
    unfold toExt
    rw [image_image, image_image]
    exact image_congr fun w _ => he_coe w
  have hGext : IsHomeoExtension ((fun w : ℂ => (c : ℂ) * w) ∘ scMap k) upperHalf (rectangle a b)
      (e ∘ scMapExt k) :=
    (isHomeoExtension_scMap hk₀ hk₁).comp_homeomorph (mapsTo_scMap hk₀ hk₁) e
      (fun w _ => he_coe w) himg
  refine ⟨k, _, _, hk₀, hk₁, hGc, hGext, fun j => ?_⟩
  rw [Function.comp_apply, scMapExt_prevertices hk₀ hk₁ j]
  fin_cases j
  · simp [rectVert, he_coe]
  · simp [rectVert, he_coe, hca']
  · simp [rectVert, he_coe, hca', hcb', mul_add, ← mul_assoc]
  · simp [rectVert, he_coe, hcb', ← mul_assoc]

theorem isJordanDomain_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsJordanDomain (rectangle a b) := by
  obtain ⟨k, G, Gext, hk₀, hk₁, hGc, hGext, -⟩ := rq_exists_scMap_rectangle ha hb
  have hfr := rq_image_frontier scExt_isOpen_upperHalf (scExt_isOpen_rectangle a b) hGc.2.2 hGext
  obtain ⟨-, hGcont, hGinj, -⟩ := hGext
  refine ⟨scExt_isOpen_rectangle a b, (scExt_convex_rectangle a b).isConnected ?_, ?_⟩
  · exact ⟨G I, hGc.2.2 ▸ ⟨I, by simp [upperHalf], rfl⟩⟩
  · obtain ⟨γ, hγc, hγi, hγr⟩ := scExt_isJordanCurve_frontier_upperHalf
    have hsub : ∀ w, γ w ∈ closure (toExt upperHalf) := fun w =>
      frontier_subset_closure (hγr ▸ mem_range_self w)
    refine ⟨Gext ∘ γ, hGcont.comp_continuous hγc hsub, fun w₁ w₂ h => ?_, ?_⟩
    · exact hγi (hGinj (hsub w₁) (hsub w₂) h)
    · rw [range_comp, hγr, hfr]

/-- **Rectangles are topological quadrilaterals**: `R(0, a, a+bi, bi)` with the vertices
`0, a, a+bi, bi` in this order. -/
theorem isTopQuad_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsTopQuad (rectangle a b) (rectVert a b) := by
  obtain ⟨k, G, Gext, hk₀, hk₁, hGc, hGext, hvert⟩ := rq_exists_scMap_rectangle ha hb
  have hfr := rq_image_frontier scExt_isOpen_upperHalf (scExt_isOpen_rectangle a b) hGc.2.2 hGext
  obtain ⟨hGf, hGcont, hGinj, hGimg⟩ := hGext
  have hprev : ∀ j : Fin 4,
      (((scPrevertex k j : ℝ) : ℂ) : ExtPlane) ∈ frontier (toExt upperHalf) :=
    fun j => scExt_ofReal_mem_frontier_toExt_upperHalf _
  have hprev' : ∀ j : Fin 4,
      (((scPrevertex k j : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
    fun j => frontier_subset_closure (hprev j)
  refine ⟨isJordanDomain_rectangle ha hb, fun j => ?_, Function.invFunOn G upperHalf,
    Function.invFunOn Gext (closure (toExt upperHalf)), scPrevertex k, ?_, ?_, ?_, ?_⟩
  · rw [← hvert j, ← hfr]
    exact mem_image_of_mem _ (hprev j)
  · exact hGc.symm scExt_isOpen_upperHalf
  · -- the inverse map and its inverse extension
    have hK : IsCompact (closure (toExt upperHalf)) := isClosed_closure.isCompact
    refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
    · rw [← hGc.2.2] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [hGc.2.1.leftInvOn_invFunOn hz, ← hGf z hz,
        hGinj.leftInvOn_invFunOn (subset_closure ⟨z, hz, rfl⟩)]
    · rw [← hGimg]
      exact continuousOn_invFunOn_image_of_isCompact hK hGcont hGinj
    · rw [← hGimg]
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ h
      rw [hGinj.leftInvOn_invFunOn hp, hGinj.leftInvOn_invFunOn hq] at h
      rw [h]
    · rw [← hGimg]
      exact hGinj.leftInvOn_invFunOn.image_image
  · -- the prevertices are in increasing order
    refine ⟨0, ?_⟩
    simp only [add_zero]
    rw [Fin.strictMono_iff_lt_succ]
    obtain ⟨h01, h12, h23⟩ := scPrevertex_lt hk₀ hk₁
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
  · intro j
    rw [← hvert j, hGinj.leftInvOn_invFunOn (hprev' j)]

/-- The rectangle `R(0, a, a+bi, bi)` as a bundled quadrilateral. -/
def rectQuad {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : TopQuad :=
  ⟨rectangle a b, rectVert a b, isTopQuad_rectangle ha hb⟩

/-- Its conformal modulus is `a / b`. -/
theorem modulus_rectQuad {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (rectQuad ha hb).modulus = a / b := by
  exact modulus_eq_of_equivRect _
    ⟨id, ha, hb, isConformalOnto_id _, id, scExt_isHomeoExtension_id _, fun _ => rfl⟩

end LiZhongQC
