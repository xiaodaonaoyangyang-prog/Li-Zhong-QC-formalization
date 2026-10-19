import References.GardinerLakic2000.Ch08.S07_NonsmoothnessOfTheNorm

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.8 Isometry theorem for genus zero

Source `teichmuller.txt`, lines 6901–7067 (Chapter 8, §8.8).

* Definition 3 (the order `ord(R) = m − n` of a rational function, pole at `∞` when `ord = −3`, l. 6902) — exists:
  `RatFunc.intDegree` (Mathlib; the degree of the numerator minus that of the denominator)
* Definition (`R(Λ)`, the integrable rational functions holomorphic in `ℂ ∖ Λ`, l. 6904) — exists:
  `GardinerLakic2000.ratSpace` (applied to Λ ∪ {∞}: the book's R(Λ) has no condition at ∞ beyond integrability)
* Unlabelled (properties (1)–(3) of `R(Λ)`, l. 6905–6913; used as "property (2)", "(3)" at l. 6972–6974, 7013) —
  `para8_8_rat_a`, `para8_8_rat_b`, `para8_8_rat_c`, `para8_8_rat_d`
* Theorem 12 (Bers' approximation theorem, `Λ` dense in `Xᶜ`, l. 6917; cited six times) — `thm8_12`
* Lemma 4 (l. 6923) — `lemma8_4`
* Definition 4 (the sets `F` and `V`, l. 6943) — `nonsimpleZeroSetPlane`, `vSetPlane`

Not items: the Steps I–VII of the proof of Theorem 11 for plane domains (l. 6958–7066). Modelling: rational functions
are Mathlib's `RatFunc ℂ` (evaluated by `RatFunc.eval (RingHom.id ℂ)`); "nonsimple zero at `a`" is
`rootMultiplicity a num ≥ 2`, "pole at `p`" is `denom(p) = 0`; property (1) includes `r = 0` [reading]; property (1)'s
local statement is `para8_8_rat_b`. In Theorem 12, `X` is a plane domain, `A(X)` is A's `aSpaceOpen` of `X`, and
`R(Λ)` consists of integrable rational functions with poles in `Λ`; near miss A: `thm3_9` (poles in all of `Xᶜ`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane toExt phiArea)

/-- Helper for `para8_8_rat_b`: if `f` is holomorphic in `0 < |z − p| < ε` and integrable on `B(p, ε)`, then
`(z − p) f(z) = o(1/(z − p))` as `z → p` (area mean value on `B(z, |z − p|/2)` and absolute continuity of the
integral). -/
theorem gl8_rat_b_littleO {f : ℂ → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε) (hf : DifferentiableOn ℂ f (ball p ε \ {p}))
    (hint : IntegrableOn f (ball p ε)) :
    (fun z => (z - p) * f z - (p - p) * f p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
  set F : ℂ → ℝ≥0∞ := (ball p ε).indicator fun z => ENNReal.ofReal ‖f z‖ with hFdef
  have hFfin : ∫⁻ z, F z ≠ ⊤ := by
    rw [hFdef, lintegral_indicator measurableSet_ball]
    have h := hint.hasFiniteIntegral
    simp only [HasFiniteIntegral] at h
    simp only [ofReal_norm]
    exact h.ne
  have hvol : Tendsto (volume ∘ fun ρ : ℝ => ball p ρ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ ^ 2 * (NNReal.pi : ℝ≥0∞)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal 0 ^ 2 * (NNReal.pi : ℝ≥0∞))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.coe_ne_top)
      exact (((ENNReal.continuous_pow 2).tendsto _).comp (ENNReal.continuous_ofReal.tendsto 0)).mono_left
        nhdsWithin_le_nhds
    simp only [ENNReal.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h1
    refine h1.congr fun ρ => ?_
    simp [Function.comp]
  have hT := tendsto_setLIntegral_zero hFfin hvol
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hc' : 0 < π * c / 4 := by positivity
  have hev := hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hc'))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hηJ⟩ := hev
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨min (η / 2) (ε / 2), by positivity, fun z hz hzp => ?_⟩
  rw [dist_eq_norm] at hz
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  set δ := ‖z - p‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 hzp'
  have hδη : δ < η / 2 := hz.trans_le (min_le_left _ _)
  have hδε : δ < ε / 2 := hz.trans_le (min_le_right _ _)
  -- the mean value bound on `B(z, δ/2)`
  have hsub : closedBall z (δ / 2) ⊆ ball p ε \ {p} := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 := norm_sub_le (y - z) (p - z)
    have h2 := norm_sub_le (z - p) (z - y)
    rw [sub_sub_sub_cancel_right] at h1
    rw [sub_sub_sub_cancel_left] at h2
    rw [norm_sub_rev p z] at h1
    rw [norm_sub_rev z y] at h2
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      linarith
    · intro hyp
      have hyp' : y = p := hyp
      rw [hyp', norm_sub_rev] at hy
      linarith
  have hmv := LiZhongQC.h36p_meanvalue hf (by positivity : 0 < δ / 2) hsub
  have hball : ball z (δ / 2) ⊆ ball p (2 * δ) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have h1 := norm_sub_le (y - z) (p - z)
    rw [sub_sub_sub_cancel_right, norm_sub_rev p z] at h1
    linarith
  have hcongr : ∫⁻ y in ball z (δ / 2), ENNReal.ofReal ‖f y‖ = ∫⁻ y in ball z (δ / 2), F y := by
    refine setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
    have hyp : y ∈ ball p ε := (hsub (ball_subset_closedBall hy)).1
    rw [hFdef, indicator_of_mem hyp]
  have hJ := hηJ (show dist (2 * δ) 0 < η by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith) (show (0 : ℝ) < 2 * δ by positivity)
  have hlt : ENNReal.ofReal (π * (δ / 2) ^ 2) * ENNReal.ofReal ‖f z‖ < ENNReal.ofReal (π * c / 4) :=
    (hmv.trans (hcongr.le.trans (lintegral_mono_set hball))).trans_lt hJ
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_ofReal_iff hc'] at hlt
  rw [sub_self, zero_mul, sub_zero, norm_mul, norm_inv, ← hδ]
  rw [le_mul_inv_iff₀ hδ0]
  nlinarith [norm_nonneg (f z), Real.pi_pos]

/-- Helper for `para8_8_rat_d`: `ofReal |w|⁻¹ ≤ |w|^{-1}` in `ℝ≥0∞` (equality off `0`). -/
theorem gl8_ofReal_inv_le (w : ℂ) : ENNReal.ofReal ‖w‖⁻¹ ≤ ‖w‖ₑ ^ (-1 : ℝ) := by
  by_cases hw : w = 0
  · simp [hw]
  rw [ENNReal.rpow_neg_one, ← ofReal_norm, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hw)]

/-- Helper for `para8_8_rat_d`: `ofReal |w|⁻³ ≤ |w|^{-3}` in `ℝ≥0∞`. -/
theorem gl8_ofReal_inv_pow_three_le (w : ℂ) : ENNReal.ofReal (‖w‖⁻¹ ^ 3) ≤ ‖w‖ₑ ^ (-3 : ℝ) := by
  by_cases hw : w = 0
  · simp [hw]
  rw [ENNReal.ofReal_pow (inv_nonneg.2 (norm_nonneg _)), ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hw),
    ofReal_norm, ENNReal.rpow_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.inv_pow]

/-- Helper for `para8_8_rat_d`: `∬_{|z − p| ≥ η} |z − c|⁻¹ |z − p|⁻² < ∞` (near `c` the integrand is
`≤ η⁻² |z − c|⁻¹`; elsewhere `u v² ≤ u³ + v³`). -/
theorem gl8_lintegral_compl_ne_top (c p : ℂ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ z in (ball p η)ᶜ, ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) ≠ ⊤ := by
  set S₁ : Set ℂ := ball c 1 with hS₁
  set S₂ : Set ℂ := {z : ℂ | 1 / 2 < ‖z - c‖} with hS₂
  set S₃ : Set ℂ := {z : ℂ | η / 2 < ‖z - p‖} with hS₃
  have hm₂ : MeasurableSet S₂ := measurableSet_lt measurable_const (measurable_id'.sub_const c).norm
  have hm₃ : MeasurableSet S₃ := measurableSet_lt measurable_const (measurable_id'.sub_const p).norm
  set g₁ : ℂ → ℝ≥0∞ := S₁.indicator fun z => ENNReal.ofReal (η⁻¹ ^ 2) * ‖z - c‖ₑ ^ (-1 : ℝ) with hg₁
  set g₂ : ℂ → ℝ≥0∞ := S₂.indicator fun z => ‖z - c‖ₑ ^ (-3 : ℝ) with hg₂
  set g₃ : ℂ → ℝ≥0∞ := S₃.indicator fun z => ‖z - p‖ₑ ^ (-3 : ℝ) with hg₃
  have hmeas₁ : Measurable g₁ :=
    (measurable_const.mul ((measurable_id'.sub_const c).enorm.pow_const _)).indicator measurableSet_ball
  have hmeas₂ : Measurable g₂ := ((measurable_id'.sub_const c).enorm.pow_const _).indicator hm₂
  have hmeas₃ : Measurable g₃ := ((measurable_id'.sub_const p).enorm.pow_const _).indicator hm₃
  have hle : ∀ z ∈ (ball p η)ᶜ, ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) ≤ g₁ z + g₂ z + g₃ z := by
    intro z hz
    have hzp : η ≤ ‖z - p‖ := by
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hzp0 : 0 < ‖z - p‖ := hη.trans_le hzp
    have hv : ‖z - p‖⁻¹ ≤ η⁻¹ := inv_anti₀ hη hzp
    have hv0 : 0 ≤ ‖z - p‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    have hu0 : 0 ≤ ‖z - c‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    by_cases hzc : ‖z - c‖ < 1
    · have h1 : z ∈ S₁ := by rw [hS₁, mem_ball, dist_eq_norm]; exact hzc
      have hle1 : ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) ≤ g₁ z := by
        rw [hg₁, indicator_of_mem h1]
        calc ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) ≤ ENNReal.ofReal (η⁻¹ ^ 2 * ‖z - c‖⁻¹) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv0 hv 2) hu0
          _ = ENNReal.ofReal (η⁻¹ ^ 2) * ENNReal.ofReal ‖z - c‖⁻¹ :=
              ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hη.le) 2)
          _ ≤ ENNReal.ofReal (η⁻¹ ^ 2) * ‖z - c‖ₑ ^ (-1 : ℝ) := by gcongr; exact gl8_ofReal_inv_le _
      exact hle1.trans (le_add_right (le_add_right le_rfl))
    · rw [not_lt] at hzc
      have h2 : z ∈ S₂ := by rw [hS₂, mem_ofPred_eq]; linarith
      have h3 : z ∈ S₃ := by rw [hS₃, mem_ofPred_eq]; linarith
      have hu : ‖z - c‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hzc
      have hamgm : ‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2 ≤ ‖z - c‖⁻¹ ^ 3 + ‖z - p‖⁻¹ ^ 3 := by
        rcases le_total ‖z - c‖⁻¹ ‖z - p‖⁻¹ with h | h
        · nlinarith [pow_nonneg hu0 3, mul_nonneg (sq_nonneg ‖z - p‖⁻¹) (sub_nonneg.2 h)]
        · nlinarith [mul_nonneg hu0 (mul_nonneg (sub_nonneg.2 h) (add_nonneg hu0 hv0)), pow_nonneg hv0 3]
      rw [hg₂, hg₃, indicator_of_mem h2, indicator_of_mem h3]
      calc ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) ≤ ENNReal.ofReal (‖z - c‖⁻¹ ^ 3 + ‖z - p‖⁻¹ ^ 3) :=
            ENNReal.ofReal_le_ofReal hamgm
        _ = ENNReal.ofReal (‖z - c‖⁻¹ ^ 3) + ENNReal.ofReal (‖z - p‖⁻¹ ^ 3) :=
            ENNReal.ofReal_add (pow_nonneg hu0 3) (pow_nonneg hv0 3)
        _ ≤ ‖z - c‖ₑ ^ (-3 : ℝ) + ‖z - p‖ₑ ^ (-3 : ℝ) :=
            add_le_add (gl8_ofReal_inv_pow_three_le _) (gl8_ofReal_inv_pow_three_le _)
        _ ≤ g₁ z + ‖z - c‖ₑ ^ (-3 : ℝ) + ‖z - p‖ₑ ^ (-3 : ℝ) := by
            rw [add_assoc]; exact le_add_left le_rfl
  have hbound := (setLIntegral_mono' (μ := volume) measurableSet_ball.compl hle).trans
    (setLIntegral_le_lintegral _ fun z => g₁ z + g₂ z + g₃ z)
  refine ne_top_of_le_ne_top ?_ hbound
  rw [lintegral_add_right _ hmeas₃, lintegral_add_left hmeas₁, hg₁, hg₂, hg₃,
    lintegral_indicator measurableSet_ball, lintegral_indicator hm₂, lintegral_indicator hm₃,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) one_pos,
    LiZhongQC.lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) one_half_pos,
    LiZhongQC.lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) (half_pos hη)]
  simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, and_false, false_and,
    or_self, not_false_eq_true]

/-- Helper for `para8_8_rat_d`: off `B(p, η)`, for `|q − p| < η/2`,
`|A_q − A_p| ≤ (2|q − p|/|a − b|)(|z − a|⁻¹ + |z − b|⁻¹)|z − p|⁻²`, `A_q(z) = 1/((z − a)(z − b)(z − q))`. -/
theorem gl8_diff_bound {a b p q z : ℂ} (hab : a ≠ b) {η : ℝ} (hη : 0 < η) (hq : ‖q - p‖ < η / 2)
    (hz : η ≤ ‖z - p‖) :
    ‖((z - a) * (z - b) * (z - q))⁻¹ - ((z - a) * (z - b) * (z - p))⁻¹‖ ≤
      2 * ‖q - p‖ / ‖a - b‖ * (‖z - a‖⁻¹ * ‖z - p‖⁻¹ ^ 2 + ‖z - b‖⁻¹ * ‖z - p‖⁻¹ ^ 2) := by
  have hd : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hR : 0 ≤ 2 * ‖q - p‖ / ‖a - b‖ * (‖z - a‖⁻¹ * ‖z - p‖⁻¹ ^ 2 + ‖z - b‖⁻¹ * ‖z - p‖⁻¹ ^ 2) := by
    positivity
  by_cases hza : z = a
  · have h1 : (z - a) * (z - b) * (z - q) = 0 := by rw [hza, sub_self, zero_mul, zero_mul]
    have h2 : (z - a) * (z - b) * (z - p) = 0 := by rw [hza, sub_self, zero_mul, zero_mul]
    rw [h1, h2, inv_zero, sub_zero, norm_zero]
    exact hR
  by_cases hzb : z = b
  · have h1 : (z - a) * (z - b) * (z - q) = 0 := by rw [hzb, sub_self, mul_zero, zero_mul]
    have h2 : (z - a) * (z - b) * (z - p) = 0 := by rw [hzb, sub_self, mul_zero, zero_mul]
    rw [h1, h2, inv_zero, sub_zero, norm_zero]
    exact hR
  have hr : 0 < ‖z - p‖ := hη.trans_le hz
  have hwq : ‖z - p‖ ≤ 2 * ‖z - q‖ := by
    have := norm_sub_le (z - q) (p - q)
    rw [sub_sub_sub_cancel_right, norm_sub_rev p q] at this
    linarith
  have hw : 0 < ‖z - q‖ := by linarith
  have hx : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
  have hy : 0 < ‖z - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hzb)
  have hdxy : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
    have := norm_sub_le (z - b) (z - a)
    rw [sub_sub_sub_cancel_left] at this
    linarith
  have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
  have hzb' : z - b ≠ 0 := sub_ne_zero.2 hzb
  have hzq' : z - q ≠ 0 := norm_pos_iff.1 hw
  have hzp' : z - p ≠ 0 := norm_pos_iff.1 hr
  have heq : ((z - a) * (z - b) * (z - q))⁻¹ - ((z - a) * (z - b) * (z - p))⁻¹ =
      (q - p) / ((z - a) * (z - b) * (z - q) * (z - p)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_mul]
  set x := ‖z - a‖
  set y := ‖z - b‖
  set w := ‖z - q‖
  set r := ‖z - p‖
  set δ := ‖q - p‖
  set d := ‖a - b‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have e1 : δ / (x * y * w * r) ≤ 2 * δ / (x * y * r ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hwq (by positivity : 0 ≤ δ * x * y * r)
    nlinarith
  have e2 : 2 * δ / (x * y * r ^ 2) ≤ 2 * δ / d * (x⁻¹ * r⁻¹ ^ 2 + y⁻¹ * r⁻¹ ^ 2) := by
    have : 2 * δ / d * (x⁻¹ * r⁻¹ ^ 2 + y⁻¹ * r⁻¹ ^ 2) = 2 * δ * ((x + y) / d) / (x * y * r ^ 2) := by
      field_simp
      ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 : 1 ≤ (x + y) / d := (one_le_div hd).2 hdxy
    nlinarith
  exact e1.trans e2

/-- Helper for `para8_8_rat_a`: `|z − s|^{-a}` is integrable on a disc around `s` if and only if `a < 2` (polar
coordinates, Mathlib `integrableOn_fun_norm_addHaar`). -/
theorem gl8_integrableOn_ball_iff (s : ℂ) {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z - s‖ ^ (-a)) (ball s δ) ↔ a < 2 := by
  have hkey : ∀ z, (ball s δ).indicator (fun z : ℂ => ‖z - s‖ ^ (-a)) z =
      (ball (0 : ℂ) δ).indicator (fun z : ℂ => ‖z‖ ^ (-a)) (z - s) := by
    intro z
    by_cases hz : z ∈ ball s δ
    · have hz' : z - s ∈ ball (0 : ℂ) δ := by
        rw [mem_ball, dist_eq_norm, sub_zero]
        rwa [mem_ball, dist_eq_norm] at hz
      rw [indicator_of_mem hz, indicator_of_mem hz']
    · have hz' : z - s ∉ ball (0 : ℂ) δ := by
        rw [mem_ball, dist_eq_norm, sub_zero]
        rwa [mem_ball, dist_eq_norm] at hz
      rw [indicator_of_notMem hz, indicator_of_notMem hz']
  have htr : IntegrableOn (fun z : ℂ => ‖z - s‖ ^ (-a)) (ball s δ) ↔
      IntegrableOn (fun z : ℂ => ‖z‖ ^ (-a)) (ball 0 δ) := by
    rw [← integrable_indicator_iff measurableSet_ball, ← integrable_indicator_iff measurableSet_ball]
    constructor
    · intro h
      refine (h.comp_add_right s).congr (Eventually.of_forall fun z => ?_)
      simp only [hkey, add_sub_cancel_right]
    · intro h
      exact (h.comp_sub_right s).congr (Eventually.of_forall fun z => (hkey z).symm)
  rw [htr, integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ (-a)) (r := δ),
    Complex.finrank_real_complex]
  have hcongr : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • y ^ (-a)) (Ioo 0 δ) ↔
      IntegrableOn (fun y : ℝ => y ^ (1 - a)) (Ioo 0 δ) := by
    refine integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [smul_eq_mul]
    rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, sub_eq_add_neg, Real.rpow_add hy.1, Real.rpow_one]
  rw [hcongr, intervalIntegral.integrableOn_Ioo_rpow_iff hδ]
  constructor <;> intro h <;> linarith

/-- Helper for `para8_8_rat_a`: `|z|^{-a}` is integrable outside a disc if and only if `a > 2`. -/
theorem gl8_integrableOn_compl_iff {R : ℝ} (hR : 0 < R) (a : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-a)) {z : ℂ | R < ‖z‖} ↔ 2 < a := by
  have hm : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integrable_indicator_iff hm]
  have hkey : ({z : ℂ | R < ‖z‖}).indicator (fun z : ℂ => ‖z‖ ^ (-a)) =
      fun z => (Ioi R).indicator (fun y : ℝ => y ^ (-a)) ‖z‖ := by
    funext z
    by_cases hz : R < ‖z‖
    · rw [indicator_of_mem (show z ∈ {z : ℂ | R < ‖z‖} from hz), indicator_of_mem (show ‖z‖ ∈ Ioi R from hz)]
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | R < ‖z‖} from hz),
        indicator_of_notMem (show ‖z‖ ∉ Ioi R from hz)]
  rw [hkey, integrable_fun_norm_addHaar volume (f := (Ioi R).indicator fun y : ℝ => y ^ (-a)),
    Complex.finrank_real_complex]
  have hcongr : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • (Ioi R).indicator (fun y : ℝ => y ^ (-a)) y) (Ioi 0) ↔
      IntegrableOn ((Ioi R).indicator fun y : ℝ => y ^ (1 - a)) (Ioi 0) := by
    refine integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioi
    by_cases hyR : y ∈ Ioi R
    · simp only [indicator_of_mem hyR, smul_eq_mul]
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, sub_eq_add_neg, Real.rpow_add (show (0 : ℝ) < y from hy),
        Real.rpow_one]
    · simp only [indicator_of_notMem hyR, smul_zero]
  rw [hcongr, integrableOn_indicator_iff measurableSet_Ioi,
    show Ioi R ∩ Ioi (0 : ℝ) = Ioi R from inter_eq_left.2 (Ioi_subset_Ioi hR.le), integrableOn_Ioi_rpow_iff hR]
  constructor <;> intro h <;> linarith

/-- Helper for `para8_8_rat_a`: growth of a nonzero polynomial at `∞`:
`|c|/2 |z|^d ≤ |P(z)| ≤ 2|c| |z|^d` for `|z| ≥ R`, `c` the leading coefficient, `d` the degree. -/
theorem gl8_poly_growth (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖P.leadingCoeff‖ / 2 * ‖z‖ ^ P.natDegree ≤ ‖P.eval z‖ ∧
        ‖P.eval z‖ ≤ 2 * ‖P.leadingCoeff‖ * ‖z‖ ^ P.natDegree := by
  set d := P.natDegree with hd
  set K := ∑ i ∈ Finset.range d, ‖P.coeff i‖ with hK
  have hlc : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hP)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨max 1 (2 * K / ‖P.leadingCoeff‖), le_max_left _ _, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hzK : 2 * K / ‖P.leadingCoeff‖ ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hsplit : P.eval z = (∑ i ∈ Finset.range d, P.coeff i * z ^ i) + P.leadingCoeff * z ^ d := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
    rfl
  have hlow : ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖ ≤ ‖P.leadingCoeff‖ / 2 * ‖z‖ ^ d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · rw [hd0, Finset.range_zero, Finset.sum_empty, norm_zero]
      positivity
    calc ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖ ≤ ∑ i ∈ Finset.range d, ‖P.coeff i‖ * ‖z‖ ^ (d - 1) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hz1 (Nat.le_sub_one_of_lt (Finset.mem_range.1 hi))) (norm_nonneg _)
      _ = K * ‖z‖ ^ (d - 1) := by rw [hK, Finset.sum_mul]
      _ ≤ ‖P.leadingCoeff‖ / 2 * ‖z‖ ^ d := by
          have hzd : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [hzd]
          have h1 : K ≤ ‖P.leadingCoeff‖ / 2 * ‖z‖ := by
            rw [div_le_iff₀ hlc] at hzK
            linarith
          have h2 : 0 ≤ ‖z‖ ^ (d - 1) := by positivity
          nlinarith
  have hlead : ‖P.leadingCoeff * z ^ d‖ = ‖P.leadingCoeff‖ * ‖z‖ ^ d := by rw [norm_mul, norm_pow]
  have hpos : 0 ≤ ‖P.leadingCoeff‖ * ‖z‖ ^ d := by positivity
  rw [hsplit]
  constructor
  · have h := norm_sub_le ((∑ i ∈ Finset.range d, P.coeff i * z ^ i) + P.leadingCoeff * z ^ d)
      (∑ i ∈ Finset.range d, P.coeff i * z ^ i)
    rw [add_sub_cancel_left, hlead] at h
    linarith
  · have h := norm_add_le (∑ i ∈ Finset.range d, P.coeff i * z ^ i) (P.leadingCoeff * z ^ d)
    rw [hlead] at h
    linarith

/-- Helper for `para8_8_rat_a`: `P/Q` is measurable. -/
theorem gl8_aesm_div (P Q : Polynomial ℂ) (μ : Measure ℂ) :
    AEStronglyMeasurable (fun z : ℂ => P.eval z / Q.eval z) μ :=
  (P.continuous.measurable.div Q.continuous.measurable).aestronglyMeasurable

open Polynomial in
/-- Helper for `para8_8_rat_a`: a pole of order `≥ 2` (the numerator coprime to the denominator) makes `P/Q`
non-integrable: near it `|P/Q| ≥ c |z − s|⁻²`. -/
theorem gl8_not_integrable_of_double_root {P Q : ℂ[X]} (hcop : IsCoprime P Q) {s : ℂ}
    (hs : 2 ≤ Q.rootMultiplicity s) : ¬ Integrable (fun z : ℂ => P.eval z / Q.eval z) := by
  intro hint
  have hQ : Q ≠ 0 := by
    rintro rfl
    rw [rootMultiplicity_zero] at hs
    omega
  obtain ⟨D, hQD, -⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ s
  set m := Q.rootMultiplicity s with hm
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQD
    exact hQ hQD
  have hPs : P.eval s ≠ 0 := by
    intro h0
    have h1 : X - C s ∣ P := dvd_iff_isRoot.2 h0
    have h2 : X - C s ∣ Q := hQD ▸ (dvd_pow_self _ (by omega)).mul_right D
    exact not_isUnit_X_sub_C s (hcop.isUnit_of_dvd' h1 h2)
  have hPs0 : 0 < ‖P.eval s‖ := norm_pos_iff.2 hPs
  obtain ⟨δ, hδ, hδP⟩ := Metric.continuous_iff.1 P.continuous s (‖P.eval s‖ / 2) (half_pos hPs0)
  obtain ⟨δ', hδ', hδD⟩ := Metric.continuous_iff.1 D.continuous s 1 one_pos
  set M := ‖D.eval s‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set ρ := min (min δ δ') 1 with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hδ hδ') one_pos
  set c := ‖P.eval s‖ / (2 * M) with hc
  have hc0 : 0 < c := by positivity
  have hfin : ({z : ℂ | D.eval z = 0} ∪ {s}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hD0).union (finite_singleton s)
  have hbound : ∀ᵐ z ∂(volume.restrict (ball s ρ)), ‖c * ‖z - s‖ ^ (-(2 : ℝ))‖ ≤ ‖P.eval z / Q.eval z‖ := by
    have hnull : volume ({z : ℂ | D.eval z = 0} ∪ {s}) = 0 := hfin.measure_zero volume
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with z hz hzn
    simp only [mem_union, mem_singleton_iff, not_or] at hzn
    obtain ⟨hDz, hzs⟩ := hzn
    rw [mem_ball] at hz
    have hzδ : dist z s < δ := hz.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hzδ' : dist z s < δ' := hz.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hz1 : dist z s < 1 := hz.trans_le (min_le_right _ _)
    have hPz : ‖P.eval s‖ / 2 ≤ ‖P.eval z‖ := by
      have h := hδP z hzδ
      rw [dist_eq_norm] at h
      have := norm_sub_norm_le (P.eval s) (P.eval z)
      rw [norm_sub_rev] at this
      linarith
    have hDz' : ‖D.eval z‖ ≤ M := by
      have h := hδD z hzδ'
      rw [dist_eq_norm] at h
      have := norm_le_norm_add_norm_sub' (D.eval z) (D.eval s)
      rw [hM]
      linarith
    have hDz0 : 0 < ‖D.eval z‖ := norm_pos_iff.2 hDz
    set t := ‖z - s‖ with ht
    have ht0 : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 hzs)
    have ht1 : t ≤ 1 := by rw [ht, ← dist_eq_norm]; exact hz1.le
    have htm : t ^ m ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1 hs
    have hQz : Q.eval z = (z - s) ^ m * D.eval z := by
      rw [hQD, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    have hlhs : ‖c * t ^ (-(2 : ℝ))‖ = c * (t ^ 2)⁻¹ := by
      rw [norm_mul, Real.norm_of_nonneg hc0.le, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
        Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hrhs : ‖P.eval z / Q.eval z‖ = ‖P.eval z‖ / (t ^ m * ‖D.eval z‖) := by
      rw [norm_div, hQz, norm_mul, norm_pow]
    rw [hlhs, hrhs]
    calc c * (t ^ 2)⁻¹ = ‖P.eval s‖ / 2 / (t ^ 2 * M) := by rw [hc]; field_simp
      _ ≤ ‖P.eval z‖ / (t ^ m * ‖D.eval z‖) :=
          div_le_div₀ (norm_nonneg _) hPz (by positivity) (mul_le_mul htm hDz' hDz0.le (by positivity))
  have hmeas : AEStronglyMeasurable (fun z : ℂ => c * ‖z - s‖ ^ (-(2 : ℝ))) (volume.restrict (ball s ρ)) :=
    (((measurable_id'.sub_const s).norm.pow_const _).const_mul c).aestronglyMeasurable
  have hint2 : IntegrableOn (fun z : ℂ => c * ‖z - s‖ ^ (-(2 : ℝ))) (ball s ρ) :=
    Integrable.mono' hint.integrableOn.norm hmeas hbound
  have hint3 : IntegrableOn (fun z : ℂ => ‖z - s‖ ^ (-(2 : ℝ))) (ball s ρ) := by
    refine IntegrableOn.congr_fun (hint2.const_mul c⁻¹) (fun z _ => ?_) measurableSet_ball
    rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  exact lt_irrefl 2 ((gl8_integrableOn_ball_iff s hρ0 2).1 hint3)

/-- Helper for `para8_8_rat_a`: if `deg Q ≤ deg P + 2` (`P, Q ≠ 0`), then `|P/Q| ≥ c |z|⁻²` near `∞` and `P/Q` is not
integrable. -/
theorem gl8_not_integrable_of_degree {P Q : Polynomial ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ P.natDegree + 2) : ¬ Integrable (fun z : ℂ => P.eval z / Q.eval z) := by
  intro hint
  obtain ⟨R₁, hR₁, hgP⟩ := gl8_poly_growth P hP
  obtain ⟨R₂, hR₂, hgQ⟩ := gl8_poly_growth Q hQ
  set R := max R₁ R₂ with hR
  have hR1 : 1 ≤ R := hR₁.trans (le_max_left _ _)
  have hlP : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hP)
  have hlQ : 0 < ‖Q.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hQ)
  set c := ‖P.leadingCoeff‖ / 2 / (2 * ‖Q.leadingCoeff‖) with hc
  have hc0 : 0 < c := by positivity
  have hm : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hbound : ∀ᵐ z ∂(volume.restrict {z : ℂ | R < ‖z‖}), ‖c * ‖z‖ ^ (-(2 : ℝ))‖ ≤ ‖P.eval z / Q.eval z‖ := by
    filter_upwards [ae_restrict_mem hm] with z hz
    have hz : R < ‖z‖ := hz
    set t := ‖z‖ with ht
    have ht1 : 1 ≤ t := hR1.trans hz.le
    have ht0 : 0 < t := by linarith
    obtain ⟨hP1, -⟩ := hgP z ((le_max_left _ _).trans hz.le)
    obtain ⟨hQ1, hQ2⟩ := hgQ z ((le_max_right _ _).trans hz.le)
    have hQpos : 0 < ‖Q.eval z‖ := lt_of_lt_of_le (by positivity) hQ1
    rw [norm_div, Real.norm_of_nonneg (by positivity), Real.rpow_neg ht0.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpow : t ^ Q.natDegree ≤ t ^ P.natDegree * t ^ 2 := by
      rw [← pow_add]
      exact pow_le_pow_right₀ ht1 hdeg
    calc c * (t ^ 2)⁻¹ = ‖P.leadingCoeff‖ / 2 * t ^ P.natDegree /
          (2 * ‖Q.leadingCoeff‖ * (t ^ P.natDegree * t ^ 2)) := by rw [hc]; field_simp
      _ ≤ ‖P.leadingCoeff‖ / 2 * t ^ P.natDegree / (2 * ‖Q.leadingCoeff‖ * t ^ Q.natDegree) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ ≤ ‖P.eval z‖ / ‖Q.eval z‖ := div_le_div₀ (norm_nonneg _) hP1 hQpos hQ2
  have hmeas : AEStronglyMeasurable (fun z : ℂ => c * ‖z‖ ^ (-(2 : ℝ)))
      (volume.restrict {z : ℂ | R < ‖z‖}) :=
    ((measurable_norm.pow_const _).const_mul c).aestronglyMeasurable
  have hint2 : IntegrableOn (fun z : ℂ => c * ‖z‖ ^ (-(2 : ℝ))) {z : ℂ | R < ‖z‖} :=
    Integrable.mono' hint.integrableOn.norm hmeas hbound
  have hint3 : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(2 : ℝ))) {z : ℂ | R < ‖z‖} := by
    refine IntegrableOn.congr_fun (hint2.const_mul c⁻¹) (fun z _ => ?_) hm
    rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  exact lt_irrefl 2 ((gl8_integrableOn_compl_iff (by linarith) 2).1 hint3)

/-- Helper for `para8_8_rat_a`: if `deg P + 3 ≤ deg Q`, then `|P/Q| ≤ C |z|⁻³` near `∞` and `P/Q` is integrable outside
a large disc. -/
theorem gl8_integrableOn_far {P Q : Polynomial ℂ} (hQ : Q ≠ 0) (hdeg : P.natDegree + 3 ≤ Q.natDegree) :
    ∃ R > 0, IntegrableOn (fun z : ℂ => P.eval z / Q.eval z) {z : ℂ | R < ‖z‖} := by
  by_cases hP : P = 0
  · refine ⟨1, one_pos, ?_⟩
    simp only [hP, Polynomial.eval_zero, zero_div]
    exact integrableOn_zero
  obtain ⟨R₁, hR₁, hgP⟩ := gl8_poly_growth P hP
  obtain ⟨R₂, hR₂, hgQ⟩ := gl8_poly_growth Q hQ
  set R := max R₁ R₂ with hR
  have hR1 : 1 ≤ R := hR₁.trans (le_max_left _ _)
  have hlP : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hP)
  have hlQ : 0 < ‖Q.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hQ)
  set C := 2 * ‖P.leadingCoeff‖ / (‖Q.leadingCoeff‖ / 2) with hC
  have hm : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine ⟨R, by linarith, Integrable.mono' (((gl8_integrableOn_compl_iff (by linarith) 3).2 (by norm_num)).const_mul C)
    (gl8_aesm_div P Q _) ?_⟩
  filter_upwards [ae_restrict_mem hm] with z hz
  have hz : R < ‖z‖ := hz
  set t := ‖z‖ with ht
  have ht1 : 1 ≤ t := hR1.trans hz.le
  have ht0 : 0 < t := by linarith
  obtain ⟨-, hP2⟩ := hgP z ((le_max_left _ _).trans hz.le)
  obtain ⟨hQ1, -⟩ := hgQ z ((le_max_right _ _).trans hz.le)
  have hQpos : 0 < ‖Q.leadingCoeff‖ / 2 * t ^ Q.natDegree := by positivity
  rw [norm_div, Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpow : t ^ P.natDegree * t ^ 3 ≤ t ^ Q.natDegree := by
    rw [← pow_add]
    exact pow_le_pow_right₀ ht1 hdeg
  calc ‖P.eval z‖ / ‖Q.eval z‖ ≤ 2 * ‖P.leadingCoeff‖ * t ^ P.natDegree / (‖Q.leadingCoeff‖ / 2 * t ^ Q.natDegree) :=
        div_le_div₀ (by positivity) hP2 hQpos hQ1
    _ ≤ 2 * ‖P.leadingCoeff‖ * t ^ P.natDegree / (‖Q.leadingCoeff‖ / 2 * (t ^ P.natDegree * t ^ 3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = C * (t ^ 3)⁻¹ := by rw [hC]; field_simp

open Polynomial in
/-- Helper for `para8_8_rat_a`: if all roots of `Q ≠ 0` are simple, `P/Q` is locally integrable (near a root
`|P/Q| ≤ C |z − s|⁻¹`, elsewhere `P/Q` is locally bounded). -/
theorem gl8_locallyIntegrable_simple {P Q : ℂ[X]} (hQ : Q ≠ 0) (hsimple : ∀ s, Q.rootMultiplicity s ≤ 1) :
    LocallyIntegrable (fun z : ℂ => P.eval z / Q.eval z) := by
  intro z₀
  by_cases hz : Q.eval z₀ = 0
  · obtain ⟨D, hQD, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ z₀
    have hm : Q.rootMultiplicity z₀ = 1 := le_antisymm (hsimple z₀) ((rootMultiplicity_pos hQ).2 hz)
    rw [hm, pow_one] at hQD
    have hDz : D.eval z₀ ≠ 0 := fun h => hnd (dvd_iff_isRoot.2 h)
    have hD0 : 0 < ‖D.eval z₀‖ := norm_pos_iff.2 hDz
    obtain ⟨δ, hδ, hδD⟩ := Metric.continuous_iff.1 D.continuous z₀ (‖D.eval z₀‖ / 2) (half_pos hD0)
    obtain ⟨δ', hδ', hδP⟩ := Metric.continuous_iff.1 P.continuous z₀ 1 one_pos
    set ρ := min δ δ' with hρ
    have hρ0 : 0 < ρ := lt_min hδ hδ'
    set C := (‖P.eval z₀‖ + 1) / (‖D.eval z₀‖ / 2) with hC
    refine ⟨ball z₀ ρ, ball_mem_nhds z₀ hρ0, Integrable.mono'
      (((gl8_integrableOn_ball_iff z₀ hρ0 1).2 (by norm_num)).const_mul C) (gl8_aesm_div P Q _) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz'
    rw [mem_ball] at hz'
    have hPz : ‖P.eval z‖ ≤ ‖P.eval z₀‖ + 1 := by
      have h := hδP z (hz'.trans_le (min_le_right _ _))
      rw [dist_eq_norm] at h
      have := norm_le_norm_add_norm_sub' (P.eval z) (P.eval z₀)
      linarith
    have hDz' : ‖D.eval z₀‖ / 2 ≤ ‖D.eval z‖ := by
      have h := hδD z (hz'.trans_le (min_le_left _ _))
      rw [dist_eq_norm] at h
      have := norm_sub_norm_le (D.eval z₀) (D.eval z)
      rw [norm_sub_rev] at this
      linarith
    have hQz : Q.eval z = (z - z₀) * D.eval z := by rw [hQD, eval_mul, eval_sub, eval_X, eval_C]
    by_cases hzz : z = z₀
    · subst hzz
      rw [hQz, sub_self, zero_mul, div_zero, norm_zero, Real.zero_rpow (by norm_num), mul_zero]
    have ht0 : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hzz)
    rw [norm_div, hQz, norm_mul, Real.rpow_neg_one]
    calc ‖P.eval z‖ / (‖z - z₀‖ * ‖D.eval z‖) ≤ (‖P.eval z₀‖ + 1) / (‖z - z₀‖ * (‖D.eval z₀‖ / 2)) :=
          div_le_div₀ (by positivity) hPz (by positivity) (mul_le_mul_of_nonneg_left hDz' ht0.le)
      _ = C * ‖z - z₀‖⁻¹ := by rw [hC]; field_simp
  · have hQ0 : 0 < ‖Q.eval z₀‖ := norm_pos_iff.2 hz
    obtain ⟨δ, hδ, hδQ⟩ := Metric.continuous_iff.1 Q.continuous z₀ (‖Q.eval z₀‖ / 2) (half_pos hQ0)
    obtain ⟨δ', hδ', hδP⟩ := Metric.continuous_iff.1 P.continuous z₀ 1 one_pos
    set ρ := min δ δ' with hρ
    have hρ0 : 0 < ρ := lt_min hδ hδ'
    refine ⟨ball z₀ ρ, ball_mem_nhds z₀ hρ0, Integrable.mono'
      (integrableOn_const (C := (‖P.eval z₀‖ + 1) / (‖Q.eval z₀‖ / 2)) measure_ball_lt_top.ne)
      (gl8_aesm_div P Q _) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz'
    rw [mem_ball] at hz'
    have hPz : ‖P.eval z‖ ≤ ‖P.eval z₀‖ + 1 := by
      have h := hδP z (hz'.trans_le (min_le_right _ _))
      rw [dist_eq_norm] at h
      have := norm_le_norm_add_norm_sub' (P.eval z) (P.eval z₀)
      linarith
    have hQz : ‖Q.eval z₀‖ / 2 ≤ ‖Q.eval z‖ := by
      have h := hδQ z (hz'.trans_le (min_le_left _ _))
      rw [dist_eq_norm] at h
      have := norm_sub_norm_le (Q.eval z₀) (Q.eval z)
      rw [norm_sub_rev] at this
      linarith
    rw [norm_div]
    exact div_le_div₀ (by positivity) hPz (half_pos hQ0) hQz

/-- **Unlabelled** (§8.8, l. 6905), property (1). A rational function belongs to `L¹(ℂ)` if and only if all its poles
are simple and `ord(r) ≤ −3` (or `r = 0`). -/
theorem para8_8_rat_a (r : RatFunc ℂ) :
    Integrable (fun z => RatFunc.eval (RingHom.id ℂ) z r) ↔
      r = 0 ∨ ((∀ a : ℂ, r.denom.rootMultiplicity a ≤ 1) ∧ r.intDegree ≤ -3) := by
  -- the evaluated function is `num/denom` (with `x/0 = 0` at the poles)
  have hfun : (fun z => RatFunc.eval (RingHom.id ℂ) z r) = fun z => r.num.eval z / r.denom.eval z := rfl
  rw [hfun]
  constructor
  · intro hint
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hnum : r.num ≠ 0 := fun h => hr (RatFunc.num_eq_zero_iff.1 h)
    refine ⟨fun s => ?_, ?_⟩
    · by_contra h
      push Not at h
      exact gl8_not_integrable_of_double_root (RatFunc.isCoprime_num_denom r) h hint
    · by_contra h
      push Not at h
      unfold RatFunc.intDegree at h
      exact gl8_not_integrable_of_degree hnum (RatFunc.denom_ne_zero r) (by omega) hint
  · rintro (hr | ⟨hs, hdeg⟩)
    · subst hr
      simp
    · unfold RatFunc.intDegree at hdeg
      obtain ⟨R, hR, hfar⟩ := gl8_integrableOn_far (P := r.num) (RatFunc.denom_ne_zero r) (by omega)
      have hnear := (gl8_locallyIntegrable_simple (P := r.num) (RatFunc.denom_ne_zero r) hs).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R)
      have hU : closedBall (0 : ℂ) R ∪ {z : ℂ | R < ‖z‖} = univ := by
        ext z
        simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
        exact le_or_gt _ _
      rw [← integrableOn_univ, ← hU]
      exact hnear.union hfar

/-- **Unlabelled** (§8.8, l. 6905), property (1), the local statement. If `f` is holomorphic in a punctured disc
`0 < |z − p| < ε` and integrable on the disc, the singularity at `p` is removable or a simple pole. -/
theorem para8_8_rat_b {f : ℂ → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε) (hf : DifferentiableOn ℂ f (ball p ε \ {p}))
    (hint : IntegrableOn f (ball p ε)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ((∀ᶠ z in 𝓝[≠] p, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] p, f z = g z / (z - p)) := by
  -- `f` has at most a simple pole: `(z − p) f(z)` has a removable singularity
  set h : ℂ → ℂ := fun z => (z - p) * f z with hhdef
  have hd : DifferentiableOn ℂ h (ball p ε \ {p}) :=
    ((differentiableOn_id.sub_const p).mul hf)
  have hs : ball p ε ∈ 𝓝 p := ball_mem_nhds p hε
  have hH := Complex.differentiableOn_update_limUnder_of_isLittleO hs hd (gl8_rat_b_littleO hε hf hint)
  refine ⟨Function.update h p (limUnder (𝓝[≠] p) h), hH.analyticAt hs, Or.inr ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hz
  rw [Function.update_of_ne hz, hhdef, mul_div_cancel_left₀ _ hzp]

/-- Helper for `para8_8_rat_c`: a quotient `p/q` of polynomials (`q ≠ 0`) agrees, wherever `q ≠ 0`, with a quotient
`p'/q'` of coprime polynomials (`p' = p/gcd`, `q' = q/gcd`). -/
theorem gl8_rat_reduce (p q : Polynomial ℂ) (hq : q ≠ 0) :
    ∃ p' q' : Polynomial ℂ, q' ≠ 0 ∧ IsCoprime p' q' ∧
      ∀ z : ℂ, q.eval z ≠ 0 → q'.eval z ≠ 0 ∧ p.eval z / q.eval z = p'.eval z / q'.eval z := by
  set g := GCDMonoid.gcd p q with hg
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hq
  have hp : g * (p / g) = p := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have hq' : g * (q / g) = q := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)
  refine ⟨p / g, q / g, ?_, isCoprime_div_gcd_div_gcd hq, fun z hz => ?_⟩
  · intro h
    rw [h, mul_zero] at hq'
    exact hq hq'.symm
  · rw [← hq', Polynomial.eval_mul] at hz
    have hgz : g.eval z ≠ 0 := left_ne_zero_of_mul hz
    have hqz : (q / g).eval z ≠ 0 := right_ne_zero_of_mul hz
    refine ⟨hqz, ?_⟩
    conv_lhs => rw [← hp, ← hq', Polynomial.eval_mul, Polynomial.eval_mul]
    exact mul_div_mul_left _ _ hgz

open Polynomial in
/-- Helper for `para8_8_rat_c`: if `r = P/Q` almost everywhere (`P, Q` coprime) and `r` is continuous at `s`, then `s`
is not a root of `Q` (near a root `|P/Q| ≥ c |z − s|⁻¹` is unbounded). -/
theorem gl8_not_root_of_continuousAt {r : ℂ → ℂ} {P Q : ℂ[X]} (hcop : IsCoprime P Q) (hQ : Q ≠ 0) {s : ℂ}
    (hr : ContinuousAt r s) (hae : ∀ᵐ z, r z = P.eval z / Q.eval z) : Q.eval s ≠ 0 := by
  intro hs
  have hPs : P.eval s ≠ 0 := fun h0 => not_isUnit_X_sub_C s
    (hcop.isUnit_of_dvd' (dvd_iff_isRoot.2 h0) (dvd_iff_isRoot.2 hs))
  obtain ⟨D, hQD⟩ := dvd_iff_isRoot.2 hs
  have hPs0 : 0 < ‖P.eval s‖ := norm_pos_iff.2 hPs
  obtain ⟨δ₁, hδ₁, hr1⟩ := Metric.continuousAt_iff.1 hr 1 one_pos
  obtain ⟨δ₂, hδ₂, hP2⟩ := Metric.continuous_iff.1 P.continuous s (‖P.eval s‖ / 2) (half_pos hPs0)
  obtain ⟨δ₃, hδ₃, hD3⟩ := Metric.continuous_iff.1 D.continuous s 1 one_pos
  set M := ‖r s‖ + 1 with hM
  set N := ‖D.eval s‖ + 1 with hN
  have hM0 : 0 < M := by positivity
  have hN0 : 0 < N := by positivity
  set ρ := min (min δ₁ δ₂) (min δ₃ (‖P.eval s‖ / (2 * N * (M + 1)))) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (by positivity))
  have hfin : ({z : ℂ | Q.eval z = 0}).Finite := Polynomial.finite_setOfPred_isRoot hQ
  have hgood : ∀ᵐ z ∂(volume.restrict (ball s ρ)), z ∈ ball s ρ ∧ Q.eval z ≠ 0 ∧ r z = P.eval z / Q.eval z := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume))] with z h1 h2 h3
    exact ⟨h1, h3, h2⟩
  have hne : (ae (volume.restrict (ball s ρ))).NeBot :=
    ae_restrict_neBot.2 (measure_ball_pos volume s hρ0).ne'
  obtain ⟨z, hz, hQz, hrz⟩ := hgood.exists
  rw [mem_ball] at hz
  have hzs : z ≠ s := by
    rintro rfl
    rw [hQD, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at hQz
    exact hQz rfl
  have hrb : ‖r z‖ < M := by
    have h := hr1 (hz.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (r z) (r s)
    rw [hM]
    linarith
  have hPz : ‖P.eval s‖ / 2 ≤ ‖P.eval z‖ := by
    have h := hP2 z (hz.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (P.eval s) (P.eval z)
    rw [norm_sub_rev] at this
    linarith
  have hDz : ‖D.eval z‖ ≤ N := by
    have h := hD3 z (hz.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (D.eval z) (D.eval s)
    rw [hN]
    linarith
  have hQz' : Q.eval z = (z - s) * D.eval z := by rw [hQD, eval_mul, eval_sub, eval_X, eval_C]
  have ht0 : 0 < ‖z - s‖ := norm_pos_iff.2 (sub_ne_zero.2 hzs)
  have htρ : ‖z - s‖ < ‖P.eval s‖ / (2 * N * (M + 1)) := by
    rw [← dist_eq_norm]
    exact hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hDz0 : 0 < ‖D.eval z‖ := by
    rw [hQz'] at hQz
    exact norm_pos_iff.2 (right_ne_zero_of_mul hQz)
  have hlow : M + 1 ≤ ‖r z‖ := by
    rw [hrz, norm_div, hQz', norm_mul, le_div_iff₀ (by positivity)]
    have h1 : ‖z - s‖ * (2 * N * (M + 1)) ≤ ‖P.eval s‖ := by
      rw [lt_div_iff₀ (by positivity)] at htρ
      linarith
    have h2 : (M + 1) * (‖z - s‖ * ‖D.eval z‖) ≤ (M + 1) * (‖z - s‖ * N) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDz ht0.le) (by positivity)
    nlinarith
  linarith

open Polynomial in
/-- Helper for `para8_8_rat_c`: interpolation on the nodes `P`: a polynomial `U` of degree `< #P` is
`∑_{q ∈ P} c_q ∏_{j ∈ P ∖ {q}} (X − j)` with `c_q = U(q)/∏_{j ≠ q} (q − j)`. -/
theorem gl8_interpolate (P : Finset ℂ) {U : ℂ[X]} (hU : U.degree < P.card) :
    U = ∑ q ∈ P, C (U.eval q / ∏ j ∈ P.erase q, (q - j)) * ∏ j ∈ P.erase q, (X - C j) := by
  classical
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq P ?_ fun x hx => ?_
  · refine (degree_sub_le _ _).trans_lt (max_lt hU ?_)
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro q hq
    refine (degree_mul_le _ _).trans_lt ?_
    have h1 : (∏ j ∈ P.erase q, (X - C j)).degree = ((P.erase q).card : WithBot ℕ) := by
      rw [degree_prod]
      simp
    rw [h1]
    have h2 : (C (U.eval q / ∏ j ∈ P.erase q, (q - j))).degree ≤ 0 := degree_C_le
    refine (add_le_add h2 le_rfl).trans_lt ?_
    rw [zero_add, Finset.card_erase_of_mem hq]
    exact_mod_cast Nat.sub_lt (Finset.card_pos.2 ⟨q, hq⟩) one_pos
  · rw [eval_finsetSum, Finset.sum_eq_single x]
    · rw [eval_mul, eval_C, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      have hne : ∏ j ∈ P.erase x, (x - j) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm
      rw [div_mul_cancel₀ _ hne]
    · intro q hq hqx
      rw [eval_mul, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hqx, hx⟩) (sub_self x), mul_zero]
    · intro h
      exact absurd hx h

open Polynomial in
/-- Helper for `para8_8_rat_c`: a polynomial `Q ≠ 0` whose roots are simple and lie in the finite set `S` divides
`T = ∏_{s ∈ S} (X − s)`. -/
theorem gl8_dvd_prod_of_roots {Q : ℂ[X]} (hQ : Q ≠ 0) (hsimple : ∀ s, Q.rootMultiplicity s ≤ 1)
    (S : Finset ℂ) (hS : ∀ s, Q.eval s = 0 → s ∈ S) : Q ∣ ∏ s ∈ S, (X - C s) := by
  classical
  have hnodup : Q.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro s
    rw [count_roots]
    exact hsimple s
  have hQe : C Q.leadingCoeff * (Q.roots.map fun a => X - C a).prod = Q :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hsub : Q.roots.toFinset ⊆ S := by
    intro s hs
    rw [Multiset.mem_toFinset, mem_roots hQ] at hs
    exact hS s hs
  have hprod : (Q.roots.map fun a => X - C a).prod = ∏ s ∈ Q.roots.toFinset, (X - C s) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ
  set rf := Q.roots.toFinset with hrf
  set L := Q.leadingCoeff with hL
  have hQ' : Q = C L * ∏ s ∈ rf, (X - C s) := by rw [← hprod]; exact hQe.symm
  refine ⟨C L⁻¹ * ∏ s ∈ S \ rf, (X - C s), ?_⟩
  calc ∏ s ∈ S, (X - C s) = (∏ s ∈ S \ rf, (X - C s)) * ∏ s ∈ rf, (X - C s) := (Finset.prod_sdiff hsub).symm
    _ = (C L * ∏ s ∈ rf, (X - C s)) * (C L⁻¹ * ∏ s ∈ S \ rf, (X - C s)) := by
        rw [mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul, mul_comm]
    _ = Q * (C L⁻¹ * ∏ s ∈ S \ rf, (X - C s)) := by rw [← hQ']

/-- **Unlabelled** (§8.8, l. 6906–6912), property (2). If `Λ` consists of `n ≥ 3` points `p₁, …, p_{n−2}, a, b`, the
functions `r_j(z) = 1/((z − a)(z − b)(z − p_j))` form a basis of `R(Λ)`. -/
theorem para8_8_rat_c {a b : ℂ} (hab : a ≠ b) {P : Finset ℂ} (hP : P.Nonempty) (ha : a ∉ P) (hb : b ∉ P) :
    ∀ r ∈ ratSpace (toExt (↑P ∪ {a, b}) ∪ {OnePoint.infty}),
      ∃! c : P → ℂ, ∀ z : ℂ, z ∉ (↑P ∪ {a, b} : Set ℂ) →
        r z = ∑ q : P, c q / ((z - a) * (z - b) * (z - q)) := by
  classical
  intro r hr
  obtain ⟨⟨hint, hdiff, -⟩, p, q, hq, hrep⟩ := hr
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℂ, S = insert a (insert b P) := ⟨_, rfl⟩
  have haS : a ∈ S := by rw [hSdef]; exact Finset.mem_insert_self a _
  have hbS : b ∈ S := by rw [hSdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
  have hPS : ∀ j ∈ P, j ∈ S := fun j hj => by
    rw [hSdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
  have haS' : a ∉ insert b P := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, ha⟩
  have hmemS : ∀ z : ℂ, z ∉ (↑P ∪ {a, b} : Set ℂ) ↔ z ∉ S := by
    intro z
    simp only [hSdef, mem_union, Finset.mem_coe, mem_insert_iff, mem_singleton_iff,
      Finset.mem_insert]
    tauto
  have hcard : S.card = P.card + 2 := by
    rw [hSdef, Finset.card_insert_of_notMem haS', Finset.card_insert_of_notMem hb]
  -- `r` is holomorphic off `S`
  have hopen : IsOpen ((S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hdiffS : DifferentiableOn ℂ r ((S : Set ℂ)ᶜ) := by
    refine hdiff.mono fun z hz => ?_
    simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := OnePoint.coe_injective hwz
    subst hwz'
    exact hz (by rw [Finset.mem_coe]; exact not_not.1 ((hmemS w).not.1 (not_not.2 hw)))
  -- uniqueness of coefficients
  have huniq : ∀ e : P → ℂ, (∀ z : ℂ, z ∉ S → ∑ q : P, e q / ((z - a) * (z - b) * (z - q)) = 0) → e = 0 := by
    intro e he
    set V : Polynomial ℂ := ∑ q : P, Polynomial.C (e q) * ∏ j ∈ P.erase q, (Polynomial.X - Polynomial.C j) with hV
    have hVz : ∀ z : ℂ, z ∉ S → V.eval z = 0 := by
      intro z hz
      have hza : z - a ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ haS)
      have hzb : z - b ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ hbS)
      have hzP : ∀ j ∈ P, z - j ≠ 0 := fun j hj => sub_ne_zero.2 fun h =>
        hz (h ▸ hPS j hj)
      have hT : (z - a) * (z - b) * ∏ j ∈ P, (z - j) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hza hzb) (Finset.prod_ne_zero_iff.2 hzP)
      have h := he z hz
      rw [hV, Polynomial.eval_finsetSum]
      have hterm : ∀ q : P, (Polynomial.C (e q) * ∏ j ∈ P.erase q, (Polynomial.X - Polynomial.C j)).eval z =
          (z - a) * (z - b) * (∏ j ∈ P, (z - j)) * (e q / ((z - a) * (z - b) * (z - q))) := by
        intro q
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
          ← Finset.mul_prod_erase P (fun j => z - j) q.2]
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        field_simp [hzP q q.2]
      simp only [hterm]
      rw [← Finset.mul_sum, h, mul_zero]
    have hV0 : V = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot V ?_
      refine (Set.infinite_univ.sdiff S.finite_toSet).mono fun z hz => ?_
      exact hVz z hz.2
    funext q
    have h := congrArg (fun f => f.eval (q : ℂ)) hV0
    simp only [hV, Polynomial.eval_finsetSum, Polynomial.eval_zero] at h
    rw [Finset.sum_eq_single q] at h
    · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at h
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
      have hne : ∏ j ∈ P.erase q, ((q : ℂ) - j) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm
      exact (mul_eq_zero.1 h).resolve_right hne
    · intro q' _ hq'
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hq' (Subtype.ext h).symm, q.2⟩) (sub_self _), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ q) h
  -- existence
  obtain ⟨p', q', hq', hcop, hred⟩ := gl8_rat_reduce p q hq
  have hfinq : ({z : ℂ | q.eval z = 0}).Finite := Polynomial.finite_setOfPred_isRoot hq
  have hae : ∀ᵐ z, r z = p'.eval z / q'.eval z := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hfinq.measure_zero volume)] with z hz
    exact (hrep z hz).trans (hred z hz).2
  have hint' : Integrable (fun z : ℂ => p'.eval z / q'.eval z) := hint.congr hae
  -- a representation `r = U/T` off `S` with `deg U < #P` gives the coefficients
  have hfromU : ∀ U : Polynomial ℂ, U.degree < P.card →
      (∀ z : ℂ, z ∉ S → r z = U.eval z / ∏ s ∈ S, (z - s)) →
      ∃ c : P → ℂ, ∀ z : ℂ, z ∉ S → r z = ∑ q : P, c q / ((z - a) * (z - b) * (z - q)) := by
    intro U hU hrU
    refine ⟨fun q => U.eval (q : ℂ) / ∏ j ∈ P.erase q, ((q : ℂ) - j), fun z hz => ?_⟩
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ haS)
    have hzb : z - b ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ hbS)
    have hzP : ∀ j ∈ P, z - j ≠ 0 := fun j hj => sub_ne_zero.2 fun h =>
      hz (h ▸ hPS j hj)
    rw [hrU z hz]
    conv_lhs => rw [gl8_interpolate P hU, Polynomial.eval_finsetSum, Finset.sum_div]
    rw [← Finset.sum_coe_sort P]
    refine Finset.sum_congr rfl fun q _ => ?_
    beta_reduce
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, hSdef, Finset.prod_insert haS',
      Finset.prod_insert hb, ← Finset.mul_prod_erase P (fun j => z - j) q.2]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hE : ∏ j ∈ P.erase q, (z - j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => hzP j (Finset.mem_of_mem_erase hj)
    field_simp [hzP q q.2]
  have hex : ∃ c : P → ℂ, ∀ z : ℂ, z ∉ S → r z = ∑ q : P, c q / ((z - a) * (z - b) * (z - q)) := by
    by_cases hp' : p' = 0
    · -- `r = 0` a.e., hence on the open set `ℂ ∖ S`
      refine hfromU 0 (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _) fun z hz => ?_
      have heq : EqOn r (fun _ => (0 : ℂ)) ((S : Set ℂ)ᶜ) := by
        refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hopen hdiffS.continuousOn continuousOn_const
        refine ae_restrict_of_ae ?_
        filter_upwards [hae] with w hw
        rw [hw, hp', Polynomial.eval_zero, zero_div]
      rw [heq (by simpa using hz), Polynomial.eval_zero, zero_div]
    -- `q'` has simple roots, all in `S`, and `deg p' + 3 ≤ deg q'`
    have hsimple : ∀ s, q'.rootMultiplicity s ≤ 1 := by
      intro s
      by_contra h
      push Not at h
      exact gl8_not_integrable_of_double_root hcop h hint'
    have hdeg : p'.natDegree + 3 ≤ q'.natDegree := by
      by_contra h
      push Not at h
      exact gl8_not_integrable_of_degree hp' hq' (by omega) hint'
    have hroots : ∀ s, q'.eval s = 0 → s ∈ S := by
      intro s hs
      by_contra hsS
      exact gl8_not_root_of_continuousAt hcop hq'
        ((hdiffS s (by simpa using hsS)).differentiableAt (hopen.mem_nhds (by simpa using hsS))).continuousAt
        hae hs
    obtain ⟨W, hW⟩ := gl8_dvd_prod_of_roots hq' hsimple S hroots
    set T : Polynomial ℂ := ∏ s ∈ S, (Polynomial.X - Polynomial.C s) with hT
    have hTdeg : T.natDegree = S.card := by
      rw [hT, Polynomial.natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s]
      simp
    have hW0 : W ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hW
      exact (Polynomial.monic_prod_X_sub_C (fun s => s) S).ne_zero hW
    refine hfromU (p' * W) ?_ fun z hz => ?_
    · by_cases hpW : p' * W = 0
      · rw [hpW, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      rw [Polynomial.degree_eq_natDegree hpW, Polynomial.natDegree_mul hp' hW0]
      have h1 : q'.natDegree + W.natDegree = S.card := by
        rw [← Polynomial.natDegree_mul hq' hW0, ← hW, hTdeg]
      have h2 := Finset.card_pos.2 hP
      exact_mod_cast (show p'.natDegree + W.natDegree < P.card by omega)
    · -- `r = p'/q' = p'W/T` a.e. on `ℂ ∖ S`, both continuous there
      have hTz : ∀ w : ℂ, w ∉ S → T.eval w ≠ 0 := by
        intro w hw
        rw [hT, Polynomial.eval_prod]
        exact Finset.prod_ne_zero_iff.2 fun s hs => by
          simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          exact sub_ne_zero.2 fun h => hw (h ▸ hs)
      have hcont : ContinuousOn (fun w : ℂ => (p' * W).eval w / ∏ s ∈ S, (w - s)) ((S : Set ℂ)ᶜ) := by
        refine (p' * W).continuous.continuousOn.div (continuousOn_finsetProd _ fun s _ =>
          (continuous_id.sub continuous_const).continuousOn) fun w hw => ?_
        have := hTz w (by simpa using hw)
        simpa [hT, Polynomial.eval_prod] using this
      have heq : EqOn r (fun w : ℂ => (p' * W).eval w / ∏ s ∈ S, (w - s)) ((S : Set ℂ)ᶜ) := by
        refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hopen hdiffS.continuousOn hcont
        rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet]
        filter_upwards [hae] with w hw hwS
        have hTw := hTz w (by simpa using hwS)
        have hTw' : T.eval w = ∏ s ∈ S, (w - s) := by
          rw [hT, Polynomial.eval_prod]
          simp
        rw [hW, Polynomial.eval_mul] at hTw hTw'
        rw [hw, ← hTw', Polynomial.eval_mul, mul_div_mul_right _ _ (right_ne_zero_of_mul hTw)]
      exact heq (by simpa using hz)
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun z hz => hc z ((hmemS z).1 hz), fun c' hc' => ?_⟩
  have h0 := huniq (c' - c) fun z hz => by
    have h1 := hc z hz
    have h2 := hc' z ((hmemS z).2 hz)
    simp only [Pi.sub_apply, sub_div, Finset.sum_sub_distrib]
    rw [← h1, ← h2, sub_self]
  exact sub_eq_zero.1 h0

/-- **Unlabelled** (§8.8, l. 6913), property (3). If `pₙ → p ∉ {a, b}`, then
`1/(P(z)(z − pₙ)) → 1/(P(z)(z − p))` in `L¹(ℂ)`, `P(z) = (z − a)(z − b)`. -/
theorem para8_8_rat_d {a b p : ℂ} (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) {q : ℕ → ℂ}
    (hq : ∀ n, q n ≠ a ∧ q n ≠ b) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => phiArea (fun z => ((z - a) * (z - b) * (z - q n))⁻¹ - ((z - a) * (z - b) * (z - p))⁻¹) univ)
      atTop (𝓝 0) := by
  -- `hq` is not needed: at `z = a, b` both terms are `0` (`0⁻¹ = 0`) and the bounds below hold there
  have _ := hq
  have ha : 0 < ‖p - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hpa)
  have hb : 0 < ‖p - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hpb)
  set m : ℝ := ‖p - a‖ / 2 * (‖p - b‖ / 2) with hm
  have hm0 : 0 < m := by positivity
  set η₀ : ℝ := min (‖p - a‖ / 2) (‖p - b‖ / 2) with hη₀
  have hη₀0 : 0 < η₀ := lt_min (half_pos ha) (half_pos hb)
  -- the contribution of `B(p, η)`
  set Bd : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal m⁻¹ *
    (ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * η) + ENNReal.ofReal (2 * π) * ENNReal.ofReal η) with hBd
  have hBdt : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have t1 : Tendsto (fun η : ℝ => ENNReal.ofReal (2 * η)) (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (2 : ℝ))
      rw [mul_zero, ENNReal.ofReal_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (fun η : ℝ => ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))
      rw [ENNReal.ofReal_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have t3 := ENNReal.Tendsto.const_mul
      ((ENNReal.Tendsto.const_mul t1 (Or.inr (ENNReal.ofReal_ne_top (r := 2 * π)))).add
        (ENNReal.Tendsto.const_mul t2 (Or.inr (ENNReal.ofReal_ne_top (r := 2 * π)))))
      (Or.inr (ENNReal.ofReal_ne_top (r := m⁻¹)))
    rw [mul_zero, add_zero, mul_zero] at t3
    rw [hBd]
    exact t3
  have hball : ∀ q' : ℂ, ∀ η : ℝ, 0 < η → η ≤ η₀ → ‖q' - p‖ < η →
      ∫⁻ z in ball p η, ENNReal.ofReal ‖((z - a) * (z - b) * (z - q'))⁻¹ - ((z - a) * (z - b) * (z - p))⁻¹‖ ≤
        Bd η := by
    intro q' η hη hηη₀ hq'
    -- on `B(p, η)`: `|z − a||z − b| ≥ m`
    have hP : ∀ z ∈ ball p η, ∀ c : ℂ,
        ENNReal.ofReal ‖((z - a) * (z - b) * (z - c))⁻¹‖ ≤ ENNReal.ofReal m⁻¹ * ‖z - c‖ₑ ^ (-1 : ℝ) := by
      intro z hz c
      rw [mem_ball, dist_eq_norm] at hz
      have hza : ‖p - a‖ / 2 ≤ ‖z - a‖ := by
        have := norm_sub_le (z - a) (z - p)
        rw [sub_sub_sub_cancel_left] at this
        have := min_le_left (‖p - a‖ / 2) (‖p - b‖ / 2)
        linarith
      have hzb : ‖p - b‖ / 2 ≤ ‖z - b‖ := by
        have := norm_sub_le (z - b) (z - p)
        rw [sub_sub_sub_cancel_left] at this
        have := min_le_right (‖p - a‖ / 2) (‖p - b‖ / 2)
        linarith
      have hprod : m ≤ ‖z - a‖ * ‖z - b‖ := by
        rw [hm]
        exact mul_le_mul hza hzb (by positivity) (norm_nonneg _)
      rw [norm_inv, norm_mul, norm_mul, mul_inv]
      calc ENNReal.ofReal ((‖z - a‖ * ‖z - b‖)⁻¹ * ‖z - c‖⁻¹) ≤ ENNReal.ofReal (m⁻¹ * ‖z - c‖⁻¹) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (inv_anti₀ hm0 hprod)
              (inv_nonneg.2 (norm_nonneg _)))
        _ = ENNReal.ofReal m⁻¹ * ENNReal.ofReal ‖z - c‖⁻¹ := ENNReal.ofReal_mul (inv_nonneg.2 hm0.le)
        _ ≤ ENNReal.ofReal m⁻¹ * ‖z - c‖ₑ ^ (-1 : ℝ) := by gcongr; exact gl8_ofReal_inv_le _
    have hle : ∀ z ∈ ball p η,
        ENNReal.ofReal ‖((z - a) * (z - b) * (z - q'))⁻¹ - ((z - a) * (z - b) * (z - p))⁻¹‖ ≤
          ENNReal.ofReal m⁻¹ * ‖z - q'‖ₑ ^ (-1 : ℝ) + ENNReal.ofReal m⁻¹ * ‖z - p‖ₑ ^ (-1 : ℝ) := by
      intro z hz
      refine (ENNReal.ofReal_le_ofReal (norm_sub_le _ _)).trans ?_
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact add_le_add (hP z hz q') (hP z hz p)
    have hmeas : Measurable fun z : ℂ => ENNReal.ofReal m⁻¹ * ‖z - q'‖ₑ ^ (-1 : ℝ) :=
      measurable_const.mul ((measurable_id'.sub_const q').enorm.pow_const _)
    have hsub : ball p η ⊆ ball q' (2 * η) := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz ⊢
      have := norm_sub_le (z - p) (q' - p)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    refine (setLIntegral_mono' measurableSet_ball hle).trans ?_
    rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add, hBd]
    beta_reduce
    gcongr
    · calc ∫⁻ z in ball p η, ‖z - q'‖ₑ ^ (-1 : ℝ) ≤ ∫⁻ z in ball q' (2 * η), ‖z - q'‖ₑ ^ (-1 : ℝ) :=
            lintegral_mono_set hsub
        _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * η) := by
            rw [LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) (by linarith)]
            norm_num
    · rw [LiZhongQC.lintegral_ball_sub_enorm_rpow_neg (by norm_num) hη]
      norm_num
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- choose `η`
  obtain ⟨η, hBη, hη⟩ := ((hBdt.eventually (gt_mem_nhds hε2)).and
    (Ioo_mem_nhdsGT hη₀0)).exists
  obtain ⟨hη0, hηη₀⟩ := hη
  -- the contribution of the complement
  set C : ℝ≥0∞ := (∫⁻ z in (ball p η)ᶜ, ENNReal.ofReal (‖z - a‖⁻¹ * ‖z - p‖⁻¹ ^ 2)) +
    ∫⁻ z in (ball p η)ᶜ, ENNReal.ofReal (‖z - b‖⁻¹ * ‖z - p‖⁻¹ ^ 2) with hC
  have hCfin : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.add_ne_top.2 ⟨gl8_lintegral_compl_ne_top a p hη0, gl8_lintegral_compl_ne_top b p hη0⟩
  have hqt : Tendsto (fun n => ‖q n - p‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim
  have hTt : Tendsto (fun n => ENNReal.ofReal (2 * ‖q n - p‖ / ‖a - b‖) * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (2 * ‖q n - p‖ / ‖a - b‖)) atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal (by simpa using (hqt.const_mul 2).div_const ‖a - b‖)
    rw [ENNReal.ofReal_zero] at h1
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hCfin)
  filter_upwards [hTt.eventually (gt_mem_nhds hε2), hqt.eventually (gt_mem_nhds (half_pos hη0))] with n hTn hqn
  have hηle : η ≤ η₀ := hηη₀.le
  rw [phiArea, Measure.restrict_univ, ← lintegral_add_compl _ measurableSet_ball]
  have h1 := hball (q n) η hη0 hηle (by linarith)
  have hmeas : ∀ c : ℂ, Measurable fun z : ℂ => ENNReal.ofReal (‖z - c‖⁻¹ * ‖z - p‖⁻¹ ^ 2) := fun c =>
    (((measurable_id'.sub_const c).norm.inv).mul (((measurable_id'.sub_const p).norm.inv).pow_const 2)).ennreal_ofReal
  have h2 : ∫⁻ z in (ball p η)ᶜ, ENNReal.ofReal ‖((z - a) * (z - b) * (z - q n))⁻¹ -
      ((z - a) * (z - b) * (z - p))⁻¹‖ ≤ ENNReal.ofReal (2 * ‖q n - p‖ / ‖a - b‖) * C := by
    have hle : ∀ z ∈ (ball p η)ᶜ, ENNReal.ofReal ‖((z - a) * (z - b) * (z - q n))⁻¹ -
        ((z - a) * (z - b) * (z - p))⁻¹‖ ≤ ENNReal.ofReal (2 * ‖q n - p‖ / ‖a - b‖) *
          (ENNReal.ofReal (‖z - a‖⁻¹ * ‖z - p‖⁻¹ ^ 2) + ENNReal.ofReal (‖z - b‖⁻¹ * ‖z - p‖⁻¹ ^ 2)) := by
      intro z hz
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hz
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (gl8_diff_bound hab hη0 hqn hz)
    refine (setLIntegral_mono' measurableSet_ball.compl hle).trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hmeas a), hC]
  calc _ ≤ Bd η + ENNReal.ofReal (2 * ‖q n - p‖ / ‖a - b‖) * C := add_le_add h1 h2
    _ ≤ ε / 2 + ε / 2 := add_le_add hBη.le hTn.le
    _ = ε := ENNReal.add_halves ε

/-- **Theorem 12** (Bers' approximation theorem, §8.8, l. 6917). If `X` is a plane domain and `Λ` is dense in `Xᶜ`,
then the integrable rational functions with poles in `Λ` are dense in `A(X)`. -/
theorem thm8_12 {X : Set ℂ} (hX : IsOpen X) (hXc : IsConnected X) {Λ : Set ℂ} (hΛ : Λ ⊆ Xᶜ)
    (hdense : Xᶜ ⊆ closure Λ) {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceOpen (toExt X)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : RatFunc ℂ, (∀ z : ℂ, r.denom.eval z = 0 → z ∈ Λ) ∧
      Integrable (fun z => RatFunc.eval (RingHom.id ℂ) z r) ∧
      ∫⁻ z in X, ENNReal.ofReal ‖φ z - RatFunc.eval (RingHom.id ℂ) z r‖ < ε := by
  sorry

open Polynomial in
/-- Helper for `lemma8_4`: at a point `p`, `rootMult_p(tA + B) = min(rootMult_p A, rootMult_p B)` for all `t` but `0`
and one exceptional value (the leading terms at `p` cancel only for one ratio). -/
theorem gl8_mult_generic {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) (p : ℂ) :
    ∃ t₀ : ℂ, ∀ t : ℂ, t ≠ 0 → t ≠ t₀ →
      (C t * A + B).rootMultiplicity p ≤ min (A.rootMultiplicity p) (B.rootMultiplicity p) := by
  obtain ⟨A₀, hA₀, hndA⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd A hA p
  obtain ⟨B₀, hB₀, hndB⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd B hB p
  have hA₀p : A₀.eval p ≠ 0 := fun h => hndA (dvd_iff_isRoot.2 h)
  have hB₀p : B₀.eval p ≠ 0 := fun h => hndB (dvd_iff_isRoot.2 h)
  set α := A.rootMultiplicity p with hα
  set β := B.rootMultiplicity p with hβ
  refine ⟨-B₀.eval p / A₀.eval p, fun t ht0 ht1 => ?_⟩
  set m := min α β with hm
  set R : ℂ[X] := C t * (X - C p) ^ (α - m) * A₀ + (X - C p) ^ (β - m) * B₀ with hR
  have hsplit : C t * A + B = R * (X - C p) ^ m := by
    rw [hR, hA₀, hB₀]
    have e1 : (X - C p) ^ α = (X - C p) ^ (α - m) * (X - C p) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (min_le_left α β)]
    have e2 : (X - C p) ^ β = (X - C p) ^ (β - m) * (X - C p) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (min_le_right α β)]
    rw [e1, e2]
    ring
  have hRp : R.eval p ≠ 0 := by
    rw [hR]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rcases lt_trichotomy α β with h | h | h
    · have h1 : α - m = 0 := by omega
      have h2 : β - m ≠ 0 := by omega
      rw [h1, pow_zero, zero_pow h2, mul_one, zero_mul, add_zero]
      exact mul_ne_zero ht0 hA₀p
    · have h1 : α - m = 0 := by omega
      have h2 : β - m = 0 := by omega
      rw [h1, h2, pow_zero, mul_one, one_mul]
      intro h0
      apply ht1
      rw [eq_div_iff hA₀p]
      linear_combination h0
    · have h1 : α - m ≠ 0 := by omega
      have h2 : β - m = 0 := by omega
      rw [h2, zero_pow h1, pow_zero, mul_zero, zero_mul, one_mul, zero_add]
      exact hB₀p
  have hR0 : R ≠ 0 := fun h => hRp (by rw [h, eval_zero])
  rw [hsplit, rootMultiplicity_mul_X_sub_C_pow hR0, rootMultiplicity_eq_zero hRp, zero_add]

open Polynomial in
/-- Helper for `lemma8_4`: `deg(tA + B) = max(deg A, deg B)` and `tA + B ≠ 0` for all `t` but `0` and one exceptional
value. -/
theorem gl8_deg_generic {A B : ℂ[X]} (hA : A ≠ 0) :
    ∃ t₁ : ℂ, ∀ t : ℂ, t ≠ 0 → t ≠ t₁ →
      C t * A + B ≠ 0 ∧ (C t * A + B).natDegree = max A.natDegree B.natDegree := by
  have hlA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hA
  refine ⟨-B.leadingCoeff / A.leadingCoeff, fun t ht0 ht1 => ?_⟩
  have hdA : (C t * A).natDegree = A.natDegree := natDegree_C_mul ht0
  rcases lt_trichotomy B.natDegree A.natDegree with h | h | h
  · have hdeg : (C t * A + B).natDegree = A.natDegree := by
      rw [natDegree_add_eq_left_of_natDegree_lt (by rw [hdA]; exact h), hdA]
    refine ⟨fun h0 => ?_, by rw [hdeg, max_eq_left h.le]⟩
    rw [h0, natDegree_zero] at hdeg
    omega
  · have hcoeff : (C t * A + B).coeff A.natDegree = t * A.leadingCoeff + B.leadingCoeff := by
      rw [coeff_add, coeff_C_mul, Polynomial.leadingCoeff, Polynomial.leadingCoeff, h]
    have hne : t * A.leadingCoeff + B.leadingCoeff ≠ 0 := by
      intro h0
      apply ht1
      rw [eq_div_iff hlA]
      linear_combination h0
    have hne0 : C t * A + B ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at hcoeff
      exact hne hcoeff.symm
    refine ⟨hne0, le_antisymm ?_ ?_⟩
    · exact (natDegree_add_le _ _).trans (le_of_eq (by rw [hdA]))
    · rw [h, max_self]
      exact le_natDegree_of_ne_zero (by rw [hcoeff]; exact hne)
  · have hdeg : (C t * A + B).natDegree = B.natDegree :=
      natDegree_add_eq_right_of_natDegree_lt (by rw [hdA]; exact h)
    refine ⟨fun h0 => ?_, by rw [hdeg, max_eq_right h.le]⟩
    rw [h0, natDegree_zero] at hdeg
    omega

open Polynomial in
/-- Helper for `lemma8_4`: if the Wronskian `AB′ − A′B` of two nonzero polynomials vanishes, `A` is a constant
multiple of `B` (with `A = g a`, `B = g b`, `a, b` coprime: `a ∣ a′`, so `a′ = 0`, then `b′ = 0`). -/
theorem gl8_wronskian_zero {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hW : A * derivative B = derivative A * B) : ∃ c : ℂ, c ≠ 0 ∧ A = C c * B := by
  set g := GCDMonoid.gcd A B with hg
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hB
  have hAa : g * (A / g) = A := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have hBb : g * (B / g) = B := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)
  have hcop : IsCoprime (A / g) (B / g) := isCoprime_div_gcd_div_gcd hB
  set a := A / g with ha
  set b := B / g with hb
  have ha0 : a ≠ 0 := fun h => hA (by rw [← hAa, h, mul_zero])
  have hb0 : b ≠ 0 := fun h => hB (by rw [← hBb, h, mul_zero])
  have hW' : a * derivative b = derivative a * b := by
    rw [← hAa, ← hBb, derivative_mul, derivative_mul] at hW
    have h : g * g * (a * derivative b - derivative a * b) = 0 := by linear_combination hW
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (mul_ne_zero hg0 hg0)
    · exact sub_eq_zero.1 h
  have hda : derivative a = 0 := by
    by_contra hne
    have hdvd : a ∣ derivative a := hcop.dvd_of_dvd_mul_right ⟨derivative b, by rw [hW']⟩
    have h1 := natDegree_le_of_dvd hdvd hne
    have hdeg : a.natDegree ≠ 0 := fun h0 => hne (derivative_eq_zero.2 h0)
    have h2 := natDegree_derivative_lt hdeg
    omega
  have hdb : derivative b = 0 := by
    rw [hda, zero_mul] at hW'
    exact (mul_eq_zero.1 hW').resolve_left ha0
  have hac := eq_C_of_derivative_eq_zero hda
  have hbc := eq_C_of_derivative_eq_zero hdb
  set a₀ := a.coeff 0 with ha₀def
  set b₀ := b.coeff 0 with hb₀def
  have ha₀ : a₀ ≠ 0 := fun h => ha0 (by rw [hac, h, C_0])
  have hb₀ : b₀ ≠ 0 := fun h => hb0 (by rw [hbc, h, C_0])
  refine ⟨a₀ / b₀, div_ne_zero ha₀ hb₀, ?_⟩
  rw [← hAa, ← hBb, hac, hbc, ← mul_assoc, mul_comm (C _) g, mul_assoc, ← C_mul, div_mul_cancel₀ _ hb₀]

open Polynomial in
/-- Helper for `lemma8_4`: if `A, B ≠ 0` have no common double root outside `S₀`, then only finitely many `t` give
`tA + B` a double root outside `S₀` (a double root `p` forces the Wronskian `AB′ − A′B` to vanish at `p` and fixes
`t`; if the Wronskian vanishes identically, `A = cB`). -/
theorem gl8_bad_finite {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) (S₀ : Set ℂ)
    (hS₀ : ∀ p, p ∉ S₀ → ¬ (2 ≤ A.rootMultiplicity p ∧ 2 ≤ B.rootMultiplicity p)) :
    {t : ℂ | ∃ p, p ∉ S₀ ∧ 2 ≤ (C t * A + B).rootMultiplicity p}.Finite := by
  by_cases hW : A * derivative B = derivative A * B
  · obtain ⟨c, hc, hAc⟩ := gl8_wronskian_zero hA hB hW
    refine Set.finite_empty.subset ?_
    rintro t ⟨p, hp, h2⟩
    exfalso
    have hrw : C t * A + B = C (t * c + 1) * B := by
      rw [hAc, C_add, C_mul, C_1]
      ring
    rw [hrw] at h2
    by_cases hk : t * c + 1 = 0
    · rw [hk, C_0, zero_mul, rootMultiplicity_zero] at h2
      omega
    · have hmB : (C (t * c + 1) * B).rootMultiplicity p = B.rootMultiplicity p := by
        rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hk) hB), rootMultiplicity_C, zero_add]
      have hmA : A.rootMultiplicity p = B.rootMultiplicity p := by
        rw [hAc, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hc) hB), rootMultiplicity_C, zero_add]
      rw [hmB] at h2
      exact hS₀ p hp ⟨by rw [hmA]; exact h2, h2⟩
  · set W := A * derivative B - derivative A * B with hWdef
    have hW0 : W ≠ 0 := sub_ne_zero.2 hW
    set cand : ℂ → ℂ := fun p => if A.eval p ≠ 0 then -B.eval p / A.eval p
      else -(derivative B).eval p / (derivative A).eval p with hcand
    refine ((Polynomial.finite_setOfPred_isRoot hW0).image cand).subset ?_
    rintro t ⟨p, hp, h2⟩
    have hne : C t * A + B ≠ 0 := by
      intro h0
      rw [h0, rootMultiplicity_zero] at h2
      omega
    obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hne).1 h2
    rw [IsRoot, eval_add, eval_mul, eval_C] at hr
    rw [derivative_add, derivative_C_mul, IsRoot, eval_add, eval_mul, eval_C] at hd
    refine ⟨p, ?_, ?_⟩
    · show W.eval p = 0
      rw [hWdef, eval_sub, eval_mul, eval_mul]
      linear_combination A.eval p * hd - (derivative A).eval p * hr
    · by_cases hAp : A.eval p = 0
      · by_cases hA'p : (derivative A).eval p = 0
        · exfalso
          have hBp : B.eval p = 0 := by rw [hAp, mul_zero, zero_add] at hr; exact hr
          have hB'p : (derivative B).eval p = 0 := by rw [hA'p, mul_zero, zero_add] at hd; exact hd
          have hmA : 1 < A.rootMultiplicity p := (one_lt_rootMultiplicity_iff_isRoot hA).2 ⟨hAp, hA'p⟩
          have hmB : 1 < B.rootMultiplicity p := (one_lt_rootMultiplicity_iff_isRoot hB).2 ⟨hBp, hB'p⟩
          exact hS₀ p hp ⟨hmA, hmB⟩
        · simp only [hcand, hAp, ne_eq, not_true_eq_false, ite_false]
          rw [div_eq_iff hA'p]
          linear_combination -hd
      · simp only [hcand, ne_eq, hAp, not_false_eq_true, ite_true]
        rw [div_eq_iff hAp]
        linear_combination -hr

/-- Helper for `lemma8_4`: if `S = N/M` in `ℂ(X)` (`M ≠ 0`), then `num S · M = N · denom S`. -/
theorem gl8_ratfunc_cross {S : RatFunc ℂ} {N M : Polynomial ℂ} (hM : M ≠ 0)
    (hS : S = algebraMap (Polynomial ℂ) (RatFunc ℂ) N / algebraMap (Polynomial ℂ) (RatFunc ℂ) M) :
    S.num * M = N * S.denom := by
  have hinj := RatFunc.algebraMap_injective ℂ
  have hM' : algebraMap (Polynomial ℂ) (RatFunc ℂ) M ≠ 0 := (map_ne_zero_iff _ hinj).2 hM
  have hD' : algebraMap (Polynomial ℂ) (RatFunc ℂ) S.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (RatFunc.denom_ne_zero S)
  have h := (RatFunc.num_div_denom S).trans hS
  rw [div_eq_div_iff hD' hM'] at h
  apply hinj
  rw [map_mul, map_mul, h]

/-- **Lemma 4** (§8.8, l. 6923). If `R₁ ≠ 0` and `R₂ ≠ 0` are rational functions with no nonsimple zeros in common,
there are constants `C₁`, `C₂` such that (a) `C₁R₁ + C₂R₂` has no nonsimple zeros, (b) every pole of `R₁` or `R₂` is a
pole of `C₁R₁ + C₂R₂`, and (c) `ord(C₁R₁ + C₂R₂) = max {ord R₁, ord R₂}`. -/
theorem lemma8_4 {R₁ R₂ : RatFunc ℂ} (h₁ : R₁ ≠ 0) (h₂ : R₂ ≠ 0)
    (hcommon : ∀ a : ℂ, ¬ (2 ≤ R₁.num.rootMultiplicity a ∧ 2 ≤ R₂.num.rootMultiplicity a)) :
    ∃ C₁ C₂ : ℂ, (∀ a : ℂ, (C₁ • R₁ + C₂ • R₂).num.rootMultiplicity a ≤ 1) ∧
      (∀ p : ℂ, R₁.denom.eval p = 0 ∨ R₂.denom.eval p = 0 → (C₁ • R₁ + C₂ • R₂).denom.eval p = 0) ∧
      (C₁ • R₁ + C₂ • R₂).intDegree = max R₁.intDegree R₂.intDegree := by
  classical
  set P₁ := R₁.num with hP₁def
  set Q₁ := R₁.denom with hQ₁def
  set P₂ := R₂.num with hP₂def
  set Q₂ := R₂.denom with hQ₂def
  have hP₁ : P₁ ≠ 0 := fun h => h₁ (RatFunc.num_eq_zero_iff.1 h)
  have hP₂ : P₂ ≠ 0 := fun h => h₂ (RatFunc.num_eq_zero_iff.1 h)
  have hQ₁ : Q₁ ≠ 0 := RatFunc.denom_ne_zero R₁
  have hQ₂ : Q₂ ≠ 0 := RatFunc.denom_ne_zero R₂
  set A := P₁ * Q₂ with hAdef
  set B := P₂ * Q₁ with hBdef
  set M := Q₁ * Q₂ with hMdef
  have hA : A ≠ 0 := mul_ne_zero hP₁ hQ₂
  have hB : B ≠ 0 := mul_ne_zero hP₂ hQ₁
  have hM : M ≠ 0 := mul_ne_zero hQ₁ hQ₂
  -- coprimality: a pole of `Rᵢ` is not a zero of its numerator
  have hcop₁ : ∀ p, Q₁.eval p = 0 → P₁.eval p ≠ 0 := fun p hq hp =>
    Polynomial.not_isUnit_X_sub_C p ((RatFunc.isCoprime_num_denom R₁).isUnit_of_dvd'
      (Polynomial.dvd_iff_isRoot.2 hp) (Polynomial.dvd_iff_isRoot.2 hq))
  have hcop₂ : ∀ p, Q₂.eval p = 0 → P₂.eval p ≠ 0 := fun p hq hp =>
    Polynomial.not_isUnit_X_sub_C p ((RatFunc.isCoprime_num_denom R₂).isUnit_of_dvd'
      (Polynomial.dvd_iff_isRoot.2 hp) (Polynomial.dvd_iff_isRoot.2 hq))
  have hmultA : ∀ p, A.rootMultiplicity p = P₁.rootMultiplicity p + Q₂.rootMultiplicity p := fun p =>
    Polynomial.rootMultiplicity_mul hA
  have hmultB : ∀ p, B.rootMultiplicity p = P₂.rootMultiplicity p + Q₁.rootMultiplicity p := fun p =>
    Polynomial.rootMultiplicity_mul hB
  have hmultM : ∀ p, M.rootMultiplicity p = Q₁.rootMultiplicity p + Q₂.rootMultiplicity p := fun p =>
    Polynomial.rootMultiplicity_mul hM
  -- the finite set of bad coefficients `t`
  obtain ⟨t₁, ht₁⟩ := gl8_deg_generic (B := B) hA
  choose t₀ ht₀ using fun p => gl8_mult_generic hA hB p
  have hS₀ : ∀ p, p ∉ {p : ℂ | M.IsRoot p} →
      ¬ (2 ≤ A.rootMultiplicity p ∧ 2 ≤ B.rootMultiplicity p) := by
    intro p hp h
    have hMp : M.eval p ≠ 0 := hp
    rw [hMdef, Polynomial.eval_mul] at hMp
    have hq₁ : Q₁.rootMultiplicity p = 0 := Polynomial.rootMultiplicity_eq_zero (left_ne_zero_of_mul hMp)
    have hq₂ : Q₂.rootMultiplicity p = 0 := Polynomial.rootMultiplicity_eq_zero (right_ne_zero_of_mul hMp)
    rw [hmultA, hmultB, hq₁, hq₂, add_zero, add_zero] at h
    exact hcommon p h
  have hbad := gl8_bad_finite hA hB {p : ℂ | M.IsRoot p} hS₀
  have hEfin : (({0, t₁} : Set ℂ) ∪ t₀ '' {p : ℂ | M.IsRoot p} ∪
      {t : ℂ | ∃ p, p ∉ {p : ℂ | M.IsRoot p} ∧
        2 ≤ (Polynomial.C t * A + B).rootMultiplicity p}).Finite :=
    ((Set.toFinite _).union ((Polynomial.finite_setOfPred_isRoot hM).image t₀)).union hbad
  obtain ⟨t, ht⟩ := hEfin.exists_notMem
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_image, mem_ofPred_eq, not_or, not_exists,
    not_and] at ht
  obtain ⟨⟨⟨ht0, ht1⟩, ht0'⟩, htbad⟩ := ht
  refine ⟨t, 1, ?_⟩
  set N := Polynomial.C t * A + B with hNdef
  obtain ⟨hN, hNdeg⟩ := ht₁ t ht0 ht1
  -- `t R₁ + R₂ = N/M`
  have hinj := RatFunc.algebraMap_injective ℂ
  have hQ₁' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ ≠ 0 := (map_ne_zero_iff _ hinj).2 hQ₁
  have hQ₂' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₂ ≠ 0 := (map_ne_zero_iff _ hinj).2 hQ₂
  have e₁ : algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁ = R₁ * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ :=
    (div_eq_iff hQ₁').1 (RatFunc.num_div_denom R₁)
  have e₂ : algebraMap (Polynomial ℂ) (RatFunc ℂ) P₂ = R₂ * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₂ :=
    (div_eq_iff hQ₂').1 (RatFunc.num_div_denom R₂)
  have hsmul : t • R₁ = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C t) * R₁ := by
    rw [Algebra.smul_def, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hS : t • R₁ + (1 : ℂ) • R₂ =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) N / algebraMap (Polynomial ℂ) (RatFunc ℂ) M := by
    rw [eq_div_iff ((map_ne_zero_iff _ hinj).2 hM), hsmul, one_smul, hNdef, hAdef, hBdef, hMdef, map_add, map_mul,
      map_mul, map_mul, map_mul, e₁, e₂]
    ring
  set S := t • R₁ + (1 : ℂ) • R₂ with hSdef
  have hcross := gl8_ratfunc_cross hM hS
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, eq_comm, div_eq_zero_iff] at hS
    rcases hS with h | h
    · exact hN ((map_eq_zero_iff _ hinj).1 h)
    · exact hM ((map_eq_zero_iff _ hinj).1 h)
  have hnum0 : S.num ≠ 0 := fun h => hS0 (RatFunc.num_eq_zero_iff.1 h)
  have hden0 : S.denom ≠ 0 := RatFunc.denom_ne_zero S
  have hmult : ∀ p, S.num.rootMultiplicity p + M.rootMultiplicity p =
      N.rootMultiplicity p + S.denom.rootMultiplicity p := by
    intro p
    rw [← Polynomial.rootMultiplicity_mul (mul_ne_zero hnum0 hM),
      ← Polynomial.rootMultiplicity_mul (mul_ne_zero hN hden0), hcross]
  have hcopS : ∀ p, S.num.eval p = 0 → S.denom.eval p ≠ 0 := fun p hp hq =>
    Polynomial.not_isUnit_X_sub_C p ((RatFunc.isCoprime_num_denom S).isUnit_of_dvd'
      (Polynomial.dvd_iff_isRoot.2 hp) (Polynomial.dvd_iff_isRoot.2 hq))
  -- at a pole `p` of `R₁` or `R₂`: `rootMult_p N < rootMult_p M`
  have hpole : ∀ p, M.IsRoot p → N.rootMultiplicity p < M.rootMultiplicity p := by
    intro p hp
    have hle : N.rootMultiplicity p ≤ min (A.rootMultiplicity p) (B.rootMultiplicity p) :=
      ht₀ p t ht0 (fun h => ht0' p hp h.symm)
    rw [hmultM p]
    have hMp : M.eval p = 0 := hp
    rw [hMdef, Polynomial.eval_mul, mul_eq_zero] at hMp
    by_cases hq₁ : Q₁.eval p = 0
    · have hm₁ : 0 < Q₁.rootMultiplicity p := (Polynomial.rootMultiplicity_pos hQ₁).2 hq₁
      have hp₁ : P₁.rootMultiplicity p = 0 := Polynomial.rootMultiplicity_eq_zero (hcop₁ p hq₁)
      have := hmultA p
      have := min_le_left (A.rootMultiplicity p) (B.rootMultiplicity p)
      omega
    · have hq₂ : Q₂.eval p = 0 := hMp.resolve_left hq₁
      have hm₂ : 0 < Q₂.rootMultiplicity p := (Polynomial.rootMultiplicity_pos hQ₂).2 hq₂
      have hm₁ : Q₁.rootMultiplicity p = 0 := Polynomial.rootMultiplicity_eq_zero hq₁
      have hp₂ : P₂.rootMultiplicity p = 0 := Polynomial.rootMultiplicity_eq_zero (hcop₂ p hq₂)
      have := hmultB p
      have := min_le_right (A.rootMultiplicity p) (B.rootMultiplicity p)
      omega
  refine ⟨fun a => ?_, fun p hp => ?_, ?_⟩
  · -- (a) no nonsimple zeros
    by_contra h
    push Not at h
    have hnuma : S.num.eval a = 0 := by
      have := (Polynomial.rootMultiplicity_pos hnum0 (x := a)).1 (by omega)
      exact this
    have hdena : S.denom.rootMultiplicity a = 0 := Polynomial.rootMultiplicity_eq_zero (hcopS a hnuma)
    have hma := hmult a
    by_cases hMa : M.IsRoot a
    · have := hpole a hMa
      omega
    · have hMa0 : M.rootMultiplicity a = 0 := Polynomial.rootMultiplicity_eq_zero hMa
      exact htbad a hMa (show 2 ≤ N.rootMultiplicity a by omega)
  · -- (b) the poles of `R₁`, `R₂` are poles of `t R₁ + R₂`
    have hMp : M.IsRoot p := by
      show M.eval p = 0
      rw [hMdef, Polynomial.eval_mul]
      rcases hp with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    have h1 := hpole p hMp
    have h2 := hmult p
    have h3 : 0 < S.denom.rootMultiplicity p := by omega
    exact (Polynomial.rootMultiplicity_pos hden0).1 h3
  · -- (c) the order at `∞`
    have hdeg := congrArg Polynomial.natDegree hcross
    rw [Polynomial.natDegree_mul hnum0 hM, Polynomial.natDegree_mul hN hden0, hNdeg, hMdef,
      Polynomial.natDegree_mul hQ₁ hQ₂, hAdef, hBdef, Polynomial.natDegree_mul hP₁ hQ₂,
      Polynomial.natDegree_mul hP₂ hQ₁] at hdeg
    simp only [RatFunc.intDegree]
    rw [← hP₁def, ← hQ₁def, ← hP₂def, ← hQ₂def]
    rcases le_total (P₁.natDegree + Q₂.natDegree) (P₂.natDegree + Q₁.natDegree) with h | h
    · rw [max_eq_right h] at hdeg
      rw [max_eq_right (by omega)]
      omega
    · rw [max_eq_left h] at hdeg
      rw [max_eq_left (by omega)]
      omega

/-- **Definition 4** (§8.8, l. 6943), the set `F`. The differentials of `A(X)` with a nonsimple zero at `a`. -/
def nonsimpleZeroSetPlane (X : Set ℂ) (a : ℂ) : Set (ℂ → ℂ) :=
  {φ | φ ∈ aSpaceOpen (toExt X) ∧ φ a = 0 ∧ deriv φ a = 0}

/-- **Definition 4** (§8.8, l. 6943–6950), the set `V`. The `ψ ∈ A(X)` for which `ψ²/φ` is integrable on `X` for some
`φ ∈ F`.
Remark (AUDIT5_GL N1): as written `F` contains `φ = 0`, and Lean's `ψ²/0 = 0` then puts every `ψ ∈ A(X)` in `V`. The
book means `φ ≢ 0`. No statement uses `F` or `V`; a user must add `φ ≠ 0`. -/
def vSetPlane (X : Set ℂ) (a : ℂ) : Set (ℂ → ℂ) :=
  {ψ | ψ ∈ aSpaceOpen (toExt X) ∧ ∃ φ ∈ nonsimpleZeroSetPlane X a, ∫⁻ z in X, ENNReal.ofReal ‖ψ z ^ 2 / φ z‖ < ⊤}

end GardinerLakic2000
