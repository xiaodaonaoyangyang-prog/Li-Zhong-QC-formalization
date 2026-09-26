import Mathlib

/-!
# The Kraus–Nehari coefficient bound

For `F` holomorphic and injective in the unit disc with `F 0 = 0` and `F' 0 = 1`, write
`F z = z + a₂ z² + a₃ z³ + ⋯`. Then `|a₃ - a₂²| ≤ 1`, equivalently
`‖F'''(0) - (3/2) F''(0)²‖ ≤ 6`. With `F'(0) = 1` the left-hand side is the Schwarzian
derivative `S_F(0)`, so this is the core of Kraus's theorem `|S_f(z)|(1 - |z|²)² ≤ 6`
(`LiZhongQC.thm19_2_nehari`, Theorem 19.2 of the book). The book cites the result without proof.

This file depends on Mathlib only. It is imported by `Ch05/S19_Schwarzian.lean`, which carries
out the reductions (omitted value, disc automorphism, affine normalization).

Route (no degree theory, no Jordan curve theorem). Put `Φ = 1/F = 1/w + g₁ + g₂ w + ⋯` on the
punctured disc, so that `S_F(0) = -6 g₂`.
* On the circle `|w| = s`, `Φ'` contains the Fourier modes `-s⁻² e^{-2iθ}` and `g₂`.
  Bessel's inequality with these two modes gives `∫|Φ'|² dθ ≥ 2π (|g₂|² + s⁻⁴)`.
* By the change-of-variables formula (injective, Jacobian `|Φ'|²`),
  `area Φ(ε < |w| < ρ) ≥ π|g₂|²(ρ² - ε²) + π(ε⁻² - ρ⁻²)`.
* For small `ε` that image lies pointwise in `g₁ + A_ε(closedBall 0 (1/ε + Cε²))`, where
  `A_ε ζ = ζ + g₂ ε² conj ζ`. Its area is `πε⁻² + O(ε)`.
* Letting `ε → 0` gives `|g₂| ≤ ρ⁻²`, and then `ρ → 1` gives `|g₂| ≤ 1`.

The bound is sharp: the Koebe function `z/(1-z)²` has `F''(0) = 4` and `F'''(0) = 18`.
-/

open Complex Metric

noncomputable section

namespace LiZhongQC

open Set Filter Topology intervalIntegral
open MeasureTheory (volume)
open scoped Real ComplexConjugate

/-! ### `kn_` helpers, part 1: the normalised map and its reciprocal

`D = dslope F 0` (so `F w = w · D w`, `D 0 = 1`), `G = 1/D = w/F(w)`, `Φ = G/w = 1/F`.  The quantity
`F'''(0) - (3/2) F''(0)²` equals `-6 g₂`, where `g₂ = (dslope G 0)'(0) = G''(0)/2` is the coefficient
of `w²` in `G`, i.e. of `w` in the Laurent expansion `Φ = 1/w + g₁ + g₂ w + ⋯`. -/

theorem kn_analyticAt_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem kn_analyticAt_dslope_of_ne {f : ℂ → ℂ} {a b : ℂ} (hf : AnalyticAt ℂ f b) (hb : b ≠ a) :
    AnalyticAt ℂ (dslope f a) b := by
  have e : slope f a = fun z => (f z - f a) / (z - a) := funext fun z => slope_def_field f a z
  refine AnalyticAt.congr ?_ (dslope_eventuallyEq_slope_of_ne f hb).symm
  rw [e]
  exact (hf.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hb)

theorem kn_analyticAt_dslope {f : ℂ → ℂ} {r : ℝ} (hf : ∀ z ∈ ball (0 : ℂ) r, AnalyticAt ℂ f z)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) r) : AnalyticAt ℂ (dslope f 0) b := by
  rcases eq_or_ne b 0 with rfl | h
  · exact kn_analyticAt_dslope_same (hf 0 hb)
  · exact kn_analyticAt_dslope_of_ne (hf b hb) h

/-- `n`-th derivative at the centre in terms of the power series coefficient. -/
theorem kn_iteratedDeriv_eq {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {a : ℂ}
    (hp : HasFPowerSeriesAt f p a) (n : ℕ) : iteratedDeriv n f a = n.factorial • p.coeff n := by
  obtain ⟨r, hpr⟩ := hp
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hpr.factorial_smul (y := 1) n,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul]

theorem kn_deriv2_eq {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {a : ℂ}
    (hp : HasFPowerSeriesAt f p a) : deriv (deriv f) a = 2 * p.coeff 2 := by
  have h := kn_iteratedDeriv_eq hp 2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  have e2 : (2 : ℕ).factorial = 2 := rfl
  rw [h, e2, nsmul_eq_mul]
  norm_num

theorem kn_deriv3_eq {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {a : ℂ}
    (hp : HasFPowerSeriesAt f p a) : deriv (deriv (deriv f)) a = 6 * p.coeff 3 := by
  have h := kn_iteratedDeriv_eq hp 3
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
  have e3 : (3 : ℕ).factorial = 6 := rfl
  rw [h, e3, nsmul_eq_mul]
  norm_num

/-- `(dslope f a)'(a) = f''(a)/2`. -/
theorem kn_deriv_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    deriv (dslope f a) a = deriv (deriv f) a / 2 := by
  obtain ⟨p, hp⟩ := hf
  have h1 : deriv (dslope f a) a = p.coeff 2 := by
    rw [hp.has_fpower_series_dslope_fslope.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      one_pow, one_smul, FormalMultilinearSeries.coeff_fslope]
  rw [h1, kn_deriv2_eq hp]
  ring

/-- `(dslope f a)''(a) = f'''(a)/3`. -/
theorem kn_deriv2_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    deriv (deriv (dslope f a)) a = deriv (deriv (deriv f)) a / 3 := by
  obtain ⟨p, hp⟩ := hf
  rw [kn_deriv2_eq hp.has_fpower_series_dslope_fslope, FormalMultilinearSeries.coeff_fslope,
    kn_deriv3_eq hp]
  ring

/-- The hypotheses of the Kraus–Nehari coefficient bound. -/
structure knHyp (F : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1)
  inj : Set.InjOn F (ball (0 : ℂ) 1)
  zero : F 0 = 0
  one : deriv F 0 = 1

/-- `G = w / F(w)`, with `G 0 = 1`. -/
def knG (F : ℂ → ℂ) (w : ℂ) : ℂ := (dslope F 0 w)⁻¹

/-- `Φ = 1 / F(w)` on the punctured disc, written as `G(w)/w`. -/
def knPhi (F : ℂ → ℂ) (w : ℂ) : ℂ := knG F w / w

/-- The derivative of `Φ` away from `0`. -/
def knPhi' (F : ℂ → ℂ) (w : ℂ) : ℂ := (deriv (knG F) w * w - knG F w) / w ^ 2

/-- `g₁ = G'(0)`: the constant term of `Φ`. -/
def knG1 (F : ℂ → ℂ) : ℂ := deriv (knG F) 0

/-- `g₂ = (dslope G 0)'(0) = G''(0)/2`: the coefficient of `w` in `Φ`. -/
def knG2 (F : ℂ → ℂ) : ℂ := deriv (dslope (knG F) 0) 0

/-- `G₂ = dslope (dslope G 0) 0`, so that `G w = 1 + g₁ w + w² G₂ w`. -/
def knG₂ (F : ℂ → ℂ) : ℂ → ℂ := dslope (dslope (knG F) 0) 0

/-- `G₃ = dslope G₂ 0`, so that `G w = 1 + g₁ w + g₂ w² + w³ G₃ w`. -/
def knG₃ (F : ℂ → ℂ) : ℂ → ℂ := dslope (knG₂ F) 0

namespace knHyp

variable {F : ℂ → ℂ} (h : knHyp F)
include h

theorem analyticAt {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : AnalyticAt ℂ F w :=
  h.diff.analyticAt (isOpen_ball.mem_nhds hw)

theorem mul_dslope (w : ℂ) : F w = w * dslope F 0 w := by
  have e := sub_smul_dslope F 0 w
  rw [sub_zero, h.zero, sub_zero, smul_eq_mul] at e
  exact e.symm

theorem dslope_zero : dslope F 0 0 = 1 := by rw [dslope_same, h.one]

theorem analyticAt_dslope {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : AnalyticAt ℂ (dslope F 0) w :=
  kn_analyticAt_dslope (fun _ hz => h.analyticAt hz) hw

theorem dslope_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : dslope F 0 w ≠ 0 := by
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [h.dslope_zero]
    exact one_ne_zero
  · intro hcon
    have hFw : F w = 0 := by rw [h.mul_dslope w, hcon, mul_zero]
    exact hw0 (h.inj hw (mem_ball_self one_pos) (hFw.trans h.zero.symm))

theorem F_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hw0 : w ≠ 0) : F w ≠ 0 := by
  rw [h.mul_dslope w]
  exact mul_ne_zero hw0 (h.dslope_ne_zero hw)

theorem analyticAt_G {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : AnalyticAt ℂ (knG F) w :=
  (h.analyticAt_dslope hw).inv (h.dslope_ne_zero hw)

theorem G_zero : knG F 0 = 1 := by rw [knG, h.dslope_zero, inv_one]

theorem analyticAt_G₂ {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : AnalyticAt ℂ (knG₂ F) w :=
  kn_analyticAt_dslope (fun _ hz => kn_analyticAt_dslope (fun _ hy => h.analyticAt_G hy) hz) hw

theorem analyticAt_G₃ {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : AnalyticAt ℂ (knG₃ F) w :=
  kn_analyticAt_dslope (fun _ hz => h.analyticAt_G₂ hz) hw

theorem phi_eq (w : ℂ) : knPhi F w = (F w)⁻¹ := by
  rw [knPhi, knG, h.mul_dslope w, mul_inv, div_eq_mul_inv, mul_comm]

theorem phi_injOn : Set.InjOn (knPhi F) (ball (0 : ℂ) 1 \ {0}) := by
  intro w₁ hw₁ w₂ hw₂ heq
  rw [h.phi_eq w₁, h.phi_eq w₂, inv_inj] at heq
  exact h.inj hw₁.1 hw₂.1 heq

theorem hasDerivAt_phi {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hw0 : w ≠ 0) :
    HasDerivAt (knPhi F) (knPhi' F w) w := by
  have hG := (h.analyticAt_G hw).differentiableAt.hasDerivAt
  have := hG.div (hasDerivAt_id w) hw0
  convert this using 1
  · rfl
  · simp [knPhi']

theorem continuousOn_phi' : ContinuousOn (knPhi' F) (ball (0 : ℂ) 1 \ {0}) := by
  intro w hw
  have hw0 : w ≠ 0 := hw.2
  have hG := h.analyticAt_G hw.1
  exact ((((hG.deriv.continuousAt.mul continuousAt_id).sub hG.continuousAt).div
    (continuousAt_id.pow 2) (pow_ne_zero 2 hw0)).continuousWithinAt)

/-- `G w = 1 + g₁ w + w² G₂ w`. -/
theorem G_expand2 (w : ℂ) : knG F w = 1 + knG1 F * w + w ^ 2 * knG₂ F w := by
  have e1 := sub_smul_dslope (knG F) 0 w
  have e2 := sub_smul_dslope (dslope (knG F) 0) 0 w
  simp only [sub_zero, smul_eq_mul, dslope_same] at e1 e2
  rw [h.G_zero] at e1
  unfold knG1 knG₂
  linear_combination -e1 - w * e2

/-- `G w = 1 + g₁ w + g₂ w² + w³ G₃ w`. -/
theorem G_expand3 (w : ℂ) :
    knG F w = 1 + knG1 F * w + knG2 F * w ^ 2 + w ^ 3 * knG₃ F w := by
  have e : w * knG₃ F w = knG₂ F w - knG₂ F 0 := by
    have e0 := sub_smul_dslope (knG₂ F) 0 w
    simp only [sub_zero, smul_eq_mul] at e0
    exact e0
  have hG20 : knG₂ F 0 = knG2 F := by
    simp only [knG₂, knG2, dslope_same]
  rw [hG20] at e
  have e2 := h.G_expand2 w
  linear_combination e2 - w ^ 2 * e

/-- `Φ w = 1/w + g₁ + g₂ w + w² G₃ w` for `w ≠ 0`. -/
theorem phi_expand {w : ℂ} (hw0 : w ≠ 0) :
    knPhi F w = w⁻¹ + knG1 F + knG2 F * w + w ^ 2 * knG₃ F w := by
  rw [knPhi, h.G_expand3 w]
  field_simp

/-- `g₂ = G''(0)/2`. -/
theorem G2_eq : knG2 F = deriv (deriv (knG F)) 0 / 2 :=
  kn_deriv_dslope_same (h.analyticAt_G (mem_ball_self one_pos))

/-- **`S_F(0) = -6 g₂`**: `F'''(0) - (3/2) F''(0)² = -6 g₂`. -/
theorem schwarzian_eq :
    deriv (deriv (deriv F)) 0 - (3 / 2) * deriv (deriv F) 0 ^ 2 = -6 * knG2 F := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hD0 := h.dslope_zero
  have hD1 : deriv (dslope F 0) 0 = deriv (deriv F) 0 / 2 := kn_deriv_dslope_same (h.analyticAt h0)
  have hD2 : deriv (deriv (dslope F 0)) 0 = deriv (deriv (deriv F)) 0 / 3 :=
    kn_deriv2_dslope_same (h.analyticAt h0)
  have hDa : AnalyticAt ℂ (dslope F 0) 0 := h.analyticAt_dslope h0
  have hne : dslope F 0 0 ≠ 0 := by rw [hD0]; exact one_ne_zero
  -- `G' = -D'/D²` near `0`
  have hev : deriv (knG F) =ᶠ[𝓝 0] fun w => -(deriv (dslope F 0) w / dslope F 0 w ^ 2) := by
    filter_upwards [hDa.eventually_analyticAt, hDa.continuousAt.eventually_ne hne] with w hw hne'
    have hG : knG F = (dslope F 0)⁻¹ := rfl
    rw [hG, (hw.differentiableAt.hasDerivAt.inv hne').deriv, neg_div]
  have hG2 : deriv (deriv (knG F)) 0 =
      2 * deriv (dslope F 0) 0 ^ 2 - deriv (deriv (dslope F 0)) 0 := by
    rw [hev.deriv_eq]
    have hd1 := hDa.deriv.differentiableAt.hasDerivAt
    have hd2 := hDa.differentiableAt.hasDerivAt.pow 2
    have h1 : HasDerivAt (fun w => -(deriv (dslope F 0) w / dslope F 0 w ^ 2)) _ 0 :=
      (hd1.div hd2 (pow_ne_zero 2 hne)).neg
    rw [h1.deriv]
    simp only [Pi.pow_apply, hD0]
    norm_num
    ring
  rw [h.G2_eq, hG2, hD1, hD2]
  ring

/-- A bound for the remainder `G₃` on a closed disc. -/
theorem exists_bound_G₃ {ρ : ℝ} (hρ : ρ < 1) :
    ∃ C : ℝ, ∀ w ∈ closedBall (0 : ℂ) ρ, ‖knG₃ F w‖ ≤ C := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball 0 1 := fun w hw =>
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
  have hc : ContinuousOn (fun w => ‖knG₃ F w‖) (closedBall (0 : ℂ) ρ) := fun w hw =>
    (h.analyticAt_G₃ (hsub hw)).continuousAt.norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image hc
  exact ⟨C, fun w hw => hC (Set.mem_image_of_mem _ hw)⟩

end knHyp

/-! ### `kn_` helpers, part 1 (continued): circle integrals and the two-mode Bessel inequality

On the circle `|w| = s` the derivative `Φ'` has Fourier coefficients `g₂` (constant mode) and
`-s⁻²` (mode `e^{-2iθ}`), computed by integration by parts and the mean value property; Bessel's
inequality for these two modes bounds `∫|Φ'|²` from below. -/

theorem kn_circleMap_mem {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (θ : ℝ) :
    circleMap 0 s θ ∈ ball (0 : ℂ) 1 ∧ circleMap 0 s θ ≠ 0 :=
  ⟨by rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hs]; exact hs1,
    circleMap_ne_center hs.ne'⟩

theorem kn_circleMap_eq (s θ : ℝ) : circleMap 0 s θ = s * exp (θ * I) := by
  simp [circleMap]

/-- The mean value property on circles, from the Cauchy integral formula. -/
theorem kn_mean_value {f : ℂ → ℂ} {s : ℝ} (hs : 0 < s)
    (hf : ∀ z ∈ closedBall (0 : ℂ) s, AnalyticAt ℂ f z) :
    ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 s θ) = 2 * π * f 0 := by
  have hc : ContinuousOn f (closedBall 0 s) := fun z hz =>
    (hf z hz).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ ball (0 : ℂ) s \ (∅ : Set ℂ), DifferentiableAt ℂ f z := fun z hz =>
    (hf z (ball_subset_closedBall hz.1)).differentiableAt
  have key := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty (mem_ball_self hs) hc hd
  unfold circleIntegral at key
  simp only [sub_zero, deriv_circleMap, smul_eq_mul] at key
  have e : ∀ θ : ℝ, circleMap 0 s θ * I * ((circleMap 0 s θ)⁻¹ * f (circleMap 0 s θ)) =
      I * f (circleMap 0 s θ) := by
    intro θ
    have hne : circleMap 0 s θ ≠ 0 := circleMap_ne_center hs.ne'
    field_simp
  simp_rw [e] at key
  rw [integral_const_mul] at key
  have h2 : I * ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 s θ) = I * (2 * π * f 0) := by
    rw [key]
    ring
  exact mul_left_cancel₀ I_ne_zero h2

theorem kn_integral_exp (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp ((k : ℂ) * I * θ) = 0 := by
  have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) I_ne_zero
  rw [integral_exp_mul_complex hc]
  push_cast
  rw [show (k : ℂ) * I * (2 * π) = k * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I, mul_zero,
    exp_zero, sub_self, zero_div]

theorem kn_hasDerivAt_exp (k : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => exp (θ * k)) (exp (θ * k) * k) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * k) k θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const k
  exact h1.cexp

theorem kn_continuous_exp (k : ℂ) : Continuous fun θ : ℝ => exp (θ * k) :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

namespace knHyp

variable {F : ℂ → ℂ} (h : knHyp F)
include h

theorem continuous_phi'_circle {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Continuous fun θ : ℝ => knPhi' F (circleMap 0 s θ) := by
  exact continuousOn_univ.1 (h.continuousOn_phi'.comp (continuous_circleMap 0 s).continuousOn
    fun θ _ => kn_circleMap_mem hs hs1 θ)

theorem hasDerivAt_u {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => knPhi F (circleMap 0 s θ))
      (knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I)) θ :=
  (h.hasDerivAt_phi (kn_circleMap_mem hs hs1 θ).1 (kn_circleMap_mem hs hs1 θ).2).comp θ
    (hasDerivAt_circleMap 0 s θ)

theorem analyticAt_G_closedBall {s : ℝ} (hs1 : s < 1) :
    ∀ z ∈ closedBall (0 : ℂ) s, AnalyticAt ℂ (knG F) z := fun _ hz =>
  h.analyticAt_G (closedBall_subset_ball hs1 hz)

/-- The mode `e^{-2iθ}` of `Φ'`: `∫₀^{2π} Φ'(s e^{iθ}) e^{2iθ} dθ = -2π/s²`. -/
theorem int_alpha {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) * exp (2 * θ * I) = -(2 * π) / s ^ 2 := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hu : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => knPhi F (circleMap 0 s θ))
      (knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I)) θ := fun θ _ => h.hasDerivAt_u hs hs1 θ
  have hv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => exp (θ * I))
      (exp (θ * I) * I) θ := fun θ _ => kn_hasDerivAt_exp I θ
  have hu'i : IntervalIntegrable
      (fun θ : ℝ => knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I)) volume 0 (2 * π) :=
    ((h.continuous_phi'_circle hs hs1).mul
      ((continuous_circleMap 0 s).mul continuous_const)).intervalIntegrable _ _
  have hv'i : IntervalIntegrable (fun θ : ℝ => exp (θ * I) * I) volume 0 (2 * π) :=
    ((kn_continuous_exp I).mul continuous_const).intervalIntegrable _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  -- boundary terms
  have hper : circleMap 0 s (2 * π) = circleMap 0 s 0 := (periodic_circleMap 0 s).eq
  rw [hper] at hibp
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, exp_two_pi_mul_I, Complex.ofReal_zero,
    zero_mul, exp_zero, mul_one, sub_self, zero_sub] at hibp
  -- `∫ u v' = (I/s) ∫ G = (I/s) 2π`
  have e1 : ∀ θ : ℝ, knPhi F (circleMap 0 s θ) * (exp (θ * I) * I) =
      I / s * knG F (circleMap 0 s θ) := by
    intro θ
    rw [knPhi, kn_circleMap_eq]
    have := Complex.exp_ne_zero (θ * I)
    field_simp
  have hint1 : ∫ θ in (0 : ℝ)..2 * π, knPhi F (circleMap 0 s θ) * (exp (θ * I) * I) =
      I / s * (2 * π) := by
    simp_rw [e1]
    rw [integral_const_mul, kn_mean_value hs (h.analyticAt_G_closedBall hs1), h.G_zero, mul_one]
  -- `∫ u' v = s I ∫ Φ' e^{2iθ}`
  have e2 : ∀ θ : ℝ, knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I) * exp (θ * I) =
      s * I * (knPhi' F (circleMap 0 s θ) * exp (2 * θ * I)) := by
    intro θ
    rw [kn_circleMap_eq, show exp (2 * (θ : ℂ) * I) = exp (θ * I) * exp (θ * I) by
      rw [← Complex.exp_add]; ring_nf]
    ring
  have hint2 : ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I) *
      exp (θ * I) = s * I * ∫ θ in (0 : ℝ)..2 * π,
        knPhi' F (circleMap 0 s θ) * exp (2 * θ * I) := by
    simp_rw [e2]
    rw [integral_const_mul]
  rw [hint1, hint2] at hibp
  -- solve for the integral
  have key : (∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) * exp (2 * θ * I)) *
      (s * I) = -(I / s * (2 * π)) := by
    linear_combination hibp
  rw [eq_div_of_mul_eq (mul_ne_zero hs0 I_ne_zero) key]
  field_simp

/-- The constant mode of `Φ'`: `∫₀^{2π} Φ'(s e^{iθ}) dθ = 2π g₂`. -/
theorem int_beta {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) = 2 * π * knG2 F := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hu : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => knPhi F (circleMap 0 s θ))
      (knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I)) θ := fun θ _ => h.hasDerivAt_u hs hs1 θ
  have hv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => exp (θ * -I))
      (exp (θ * -I) * -I) θ := fun θ _ => kn_hasDerivAt_exp (-I) θ
  have hu'i : IntervalIntegrable
      (fun θ : ℝ => knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I)) volume 0 (2 * π) :=
    ((h.continuous_phi'_circle hs hs1).mul
      ((continuous_circleMap 0 s).mul continuous_const)).intervalIntegrable _ _
  have hv'i : IntervalIntegrable (fun θ : ℝ => exp (θ * -I) * -I) volume 0 (2 * π) :=
    ((kn_continuous_exp (-I)).mul continuous_const).intervalIntegrable _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  have hper : circleMap 0 s (2 * π) = circleMap 0 s 0 := (periodic_circleMap 0 s).eq
  rw [hper] at hibp
  have hexp : exp (((2 * π : ℝ) : ℂ) * -I) = 1 := by
    rw [show ((2 * π : ℝ) : ℂ) * -I = (-1 : ℤ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I]
  simp only [hexp, Complex.ofReal_zero, zero_mul, exp_zero, mul_one, sub_self, zero_sub] at hibp
  have hE' : ∀ θ : ℝ, exp (θ * -I) = (exp (θ * I))⁻¹ := fun θ => by
    rw [mul_neg, Complex.exp_neg]
  simp_rw [hE'] at hibp
  -- `∫ u v' = -(I/s²) ∫ G(s e^{iθ}) e^{-2iθ}`, and the latter integral is `2π s² g₂`
  have e1 : ∀ θ : ℝ, knPhi F (circleMap 0 s θ) * ((exp (θ * I))⁻¹ * -I) =
      -(I / s) * (knG F (circleMap 0 s θ) * ((exp (θ * I))⁻¹ * (exp (θ * I))⁻¹)) := by
    intro θ
    rw [knPhi, kn_circleMap_eq]
    have h1 := Complex.exp_ne_zero (θ * I)
    field_simp
  have hG₂on : ContinuousOn (knG₂ F) (ball (0 : ℂ) 1) := fun z hz =>
    (h.analyticAt_G₂ hz).continuousAt.continuousWithinAt
  have hG₂c : Continuous fun θ : ℝ => knG₂ F (circleMap 0 s θ) :=
    continuousOn_univ.1 (hG₂on.comp (continuous_circleMap 0 s).continuousOn
      fun θ _ => (kn_circleMap_mem hs hs1 θ).1)
  have hexpand : ∀ θ : ℝ, knG F (circleMap 0 s θ) * ((exp (θ * I))⁻¹ * (exp (θ * I))⁻¹) =
      exp ((-2 : ℤ) * I * θ) + knG1 F * s * exp ((-1 : ℤ) * I * θ) +
        s ^ 2 * knG₂ F (circleMap 0 s θ) := by
    intro θ
    rw [h.G_expand2 (circleMap 0 s θ), kn_circleMap_eq]
    have h3 : exp ((-2 : ℤ) * I * θ) = (exp (θ * I))⁻¹ * (exp (θ * I))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h4 : exp ((-1 : ℤ) * I * θ) = (exp (θ * I))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [h3, h4]
    have h1 := Complex.exp_ne_zero (θ * I)
    field_simp
  have hint0 : ∫ θ in (0 : ℝ)..2 * π,
      knG F (circleMap 0 s θ) * ((exp (θ * I))⁻¹ * (exp (θ * I))⁻¹) =
        2 * π * s ^ 2 * knG2 F := by
    simp_rw [hexpand]
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
      kn_integral_exp (-2) (by norm_num), kn_integral_exp (-1) (by norm_num),
      kn_mean_value hs (fun z hz => h.analyticAt_G₂ (closedBall_subset_ball hs1 hz))]
    · simp only [knG₂, dslope_same, knG2]
      ring
    · exact ((kn_continuous_exp ((-2 : ℤ) * I)).congr fun θ => by congr 1; ring).intervalIntegrable _ _
    · exact (continuous_const.mul ((kn_continuous_exp ((-1 : ℤ) * I)).congr fun θ => by congr 1; ring)).intervalIntegrable _ _
    · exact (((kn_continuous_exp ((-2 : ℤ) * I)).congr fun θ => by congr 1; ring).add
        (continuous_const.mul ((kn_continuous_exp ((-1 : ℤ) * I)).congr fun θ => by congr 1; ring))).intervalIntegrable _ _
    · exact (continuous_const.mul hG₂c).intervalIntegrable _ _
  have hint1 : ∫ θ in (0 : ℝ)..2 * π, knPhi F (circleMap 0 s θ) * ((exp (θ * I))⁻¹ * -I) =
      -(I / s) * (2 * π * s ^ 2 * knG2 F) := by
    simp_rw [e1]
    rw [integral_const_mul, hint0]
  -- `∫ u' v = s I ∫ Φ'`
  have e2 : ∀ θ : ℝ, knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I) * (exp (θ * I))⁻¹ =
      s * I * knPhi' F (circleMap 0 s θ) := by
    intro θ
    rw [kn_circleMap_eq]
    have h1 := Complex.exp_ne_zero (θ * I)
    field_simp
  have hint2 : ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) * (circleMap 0 s θ * I) *
      (exp (θ * I))⁻¹ = s * I * ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ) := by
    simp_rw [e2]
    rw [integral_const_mul]
  rw [hint1, hint2] at hibp
  have key : (∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 s θ)) * (s * I) =
      I / s * (2 * π * s ^ 2 * knG2 F) := by
    linear_combination hibp
  rw [eq_div_of_mul_eq (mul_ne_zero hs0 I_ne_zero) key]
  field_simp

end knHyp

/-- **Bessel's inequality with two modes** on `[0, 2π]`: if `f` has Fourier coefficients `c₀`
(constant mode) and `c₁` (mode `e^{-2iθ}`), then `2π(|c₀|² + |c₁|²) ≤ ∫ |f|²`. -/
theorem kn_bessel {f : ℝ → ℂ} (hf : Continuous f) {c₀ c₁ : ℂ}
    (h0 : ∫ θ in (0 : ℝ)..2 * π, f θ = 2 * π * c₀)
    (h1 : ∫ θ in (0 : ℝ)..2 * π, f θ * exp (2 * θ * I) = 2 * π * c₁) :
    2 * π * (‖c₀‖ ^ 2 + ‖c₁‖ ^ 2) ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2 := by
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  -- the mode `e θ = e^{-2iθ}` and the truncation `k = c₀ + c₁ e`
  set e : ℝ → ℂ := fun θ => exp (θ * (-2 * I)) with he_def
  have he_cont : Continuous e := kn_continuous_exp _
  have he_norm : ∀ θ, ‖e θ‖ = 1 := by
    intro θ
    simp only [he_def]
    rw [show (θ : ℂ) * (-2 * I) = ((-2 * θ : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have he_conj : ∀ θ, conj (e θ) = exp (2 * θ * I) := by
    intro θ
    simp only [he_def]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  set k : ℝ → ℂ := fun θ => c₀ + c₁ * e θ with hk_def
  have hk_cont : Continuous k := continuous_const.add (continuous_const.mul he_cont)
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f θ - k θ‖ ^ 2 :=
    integral_nonneg hpi fun θ _ => sq_nonneg _
  -- pointwise expansion
  have hpt : ∀ θ, ‖f θ - k θ‖ ^ 2 =
      ‖f θ‖ ^ 2 - 2 * (f θ * conj (k θ)).re + ‖k θ‖ ^ 2 := by
    intro θ
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_sub]
    ring
  -- the cross term
  have hcross_pt : ∀ θ, f θ * conj (k θ) = conj c₀ * f θ + conj c₁ * (f θ * exp (2 * θ * I)) := by
    intro θ
    simp only [hk_def, map_add, map_mul, he_conj]
    ring
  have hfi : IntervalIntegrable f volume 0 (2 * π) := hf.intervalIntegrable _ _
  have hfe : IntervalIntegrable (fun θ => f θ * exp (2 * θ * I)) volume 0 (2 * π) :=
    (hf.mul ((kn_continuous_exp (2 * I)).congr fun θ => by congr 1; ring)).intervalIntegrable _ _
  have hcross : ∫ θ in (0 : ℝ)..2 * π, (f θ * conj (k θ)).re = 2 * π * (‖c₀‖ ^ 2 + ‖c₁‖ ^ 2) := by
    have hint : IntervalIntegrable (fun θ => f θ * conj (k θ)) volume 0 (2 * π) :=
      (hf.mul (Complex.continuous_conj.comp hk_cont)).intervalIntegrable _ _
    have := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    rw [this]
    simp_rw [hcross_pt]
    rw [integral_add (hfi.const_mul _) (hfe.const_mul _), integral_const_mul, integral_const_mul,
      h0, h1]
    have e0 : conj c₀ * (2 * π * c₀) = (2 * π * ‖c₀‖ ^ 2 : ℝ) := by
      rw [show conj c₀ * (2 * π * c₀) = 2 * π * (conj c₀ * c₀) by ring, Complex.conj_mul']
      push_cast
      ring
    have e1 : conj c₁ * (2 * π * c₁) = (2 * π * ‖c₁‖ ^ 2 : ℝ) := by
      rw [show conj c₁ * (2 * π * c₁) = 2 * π * (conj c₁ * c₁) by ring, Complex.conj_mul']
      push_cast
      ring
    rw [e0, e1, ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  -- the truncation term
  have hk_pt : ∀ θ, ‖k θ‖ ^ 2 = ‖c₀‖ ^ 2 + ‖c₁‖ ^ 2 + 2 * (c₀ * conj c₁ * exp (2 * θ * I)).re := by
    intro θ
    simp only [hk_def, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_add, Complex.normSq_mul, map_mul, he_conj,
      show normSq (e θ) = 1 by rw [Complex.normSq_eq_norm_sq, he_norm, one_pow]]
    ring_nf
  have hk_int : ∫ θ in (0 : ℝ)..2 * π, ‖k θ‖ ^ 2 = 2 * π * (‖c₀‖ ^ 2 + ‖c₁‖ ^ 2) := by
    simp_rw [hk_pt]
    have hexp_cont : Continuous fun θ : ℝ => c₀ * conj c₁ * exp (2 * θ * I) :=
      continuous_const.mul ((kn_continuous_exp (2 * I)).congr fun θ => by congr 1; ring)
    have hre_int : IntervalIntegrable
        (fun θ : ℝ => 2 * (c₀ * conj c₁ * exp (2 * θ * I)).re) volume 0 (2 * π) :=
      (continuous_const.mul (Complex.continuous_re.comp hexp_cont)).intervalIntegrable _ _
    rw [integral_add intervalIntegrable_const hre_int, integral_const,
      integral_const_mul]
    have hre := Complex.reCLM.intervalIntegral_comp_comm
      (hexp_cont.intervalIntegrable (μ := volume) 0 (2 * π))
    simp only [Complex.reCLM_apply] at hre
    rw [hre, integral_const_mul]
    have hz : ∫ θ in (0 : ℝ)..2 * π, exp (2 * θ * I) = 0 := by
      rw [← kn_integral_exp 2 (by norm_num)]
      refine integral_congr fun θ _ => ?_
      push_cast
      ring_nf
    rw [hz, mul_zero, Complex.zero_re, mul_zero, add_zero, smul_eq_mul, sub_zero]
  -- expand the nonnegative integral
  have hfk : ∫ θ in (0 : ℝ)..2 * π, ‖f θ - k θ‖ ^ 2 =
      (∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2) - 2 * (2 * π * (‖c₀‖ ^ 2 + ‖c₁‖ ^ 2)) +
        2 * π * (‖c₀‖ ^ 2 + ‖c₁‖ ^ 2) := by
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun θ => ‖f θ‖ ^ 2) volume 0 (2 * π) :=
      (hf.norm.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => 2 * (f θ * conj (k θ)).re) volume 0 (2 * π) :=
      (continuous_const.mul (Complex.continuous_re.comp
        (hf.mul (Complex.continuous_conj.comp hk_cont)))).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun θ => ‖k θ‖ ^ 2) volume 0 (2 * π) :=
      (hk_cont.norm.pow 2).intervalIntegrable _ _
    rw [integral_add (i1.sub i2) i3, integral_sub i1 i2, integral_const_mul, hcross, hk_int]
  linarith [hnonneg, hfk]

open MeasureTheory

/-! ### `kn_` helpers, part 2: the area of `Φ(ε < |w| < ρ)`

By the change of variables formula (injective `Φ`, Jacobian `|Φ'|²`) and polar coordinates,
`area Φ(ε < |w| < ρ) = ∫_ε^ρ ∫ |Φ'(r e^{iθ})|² r dθ dr ≥ π|g₂|²(ρ² - ε²) + π(ε⁻² - ρ⁻²)`. -/

/-- The real determinant of multiplication by `c` on `ℂ` is `‖c‖²`. -/
theorem kn_det_smulRight (c : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
    Complex.sq_norm, Complex.normSq_apply]

theorem kn_annulus_subset {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ < 1) :
    ball (0 : ℂ) ρ \ closedBall 0 ε ⊆ ball (0 : ℂ) 1 \ {0} := fun w hw =>
  ⟨ball_subset_ball hρ.le hw.1, fun h0 => hw.2 (by
    rw [Set.mem_singleton_iff.1 h0]
    exact mem_closedBall_self hε.le)⟩

theorem kn_polar_symm_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, kn_circleMap_eq, Complex.exp_mul_I]
  push_cast
  ring

/-- `∫_ε^ρ 2π r (n² + r⁻⁴) dr = π n² (ρ² - ε²) + π (ε⁻² - ρ⁻²)`. -/
theorem kn_ftc {n ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    ∫ r in ε..ρ, 2 * π * r * (n ^ 2 + ((r ^ 2)⁻¹) ^ 2) =
      π * n ^ 2 * (ρ ^ 2 - ε ^ 2) + π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) := by
  have hpos : ∀ r ∈ uIcc ε ρ, 0 < r := by
    intro r hr
    rw [uIcc_of_le hερ.le] at hr
    linarith [hr.1]
  have hderiv : ∀ r ∈ uIcc ε ρ, HasDerivAt (fun r : ℝ => π * n ^ 2 * r ^ 2 - π * (r ^ 2)⁻¹)
      (2 * π * r * (n ^ 2 + ((r ^ 2)⁻¹) ^ 2)) r := by
    intro r hr
    have hr0 := hpos r hr
    have h1 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have h2 := h1.inv (pow_ne_zero 2 hr0.ne')
    have := (h1.const_mul (π * n ^ 2)).sub (h2.const_mul π)
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun r : ℝ => 2 * π * r * (n ^ 2 + ((r ^ 2)⁻¹) ^ 2)) (uIcc ε ρ) := by
    refine (continuousOn_const.mul continuousOn_id).mul
      (continuousOn_const.add (((continuousOn_id.pow 2).inv₀ ?_).pow 2))
    intro r hr
    exact pow_ne_zero 2 (hpos r hr).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

namespace knHyp

variable {F : ℂ → ℂ} (h : knHyp F)
include h

/-- The change of variables formula: `area Φ(A) = ∫_A |Φ'|²` for the annulus `A`. -/
theorem volume_image_annulus {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ < 1) :
    volume (knPhi F '' (ball (0 : ℂ) ρ \ closedBall 0 ε)) =
      ∫⁻ w in ball (0 : ℂ) ρ \ closedBall 0 ε, ENNReal.ofReal (‖knPhi' F w‖ ^ 2) := by
  have hAm : MeasurableSet (ball (0 : ℂ) ρ \ closedBall 0 ε) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hAsub := kn_annulus_subset hε hρ
  have hf' : ∀ w ∈ ball (0 : ℂ) ρ \ closedBall 0 ε, HasFDerivWithinAt (knPhi F)
      (((1 : ℂ →L[ℂ] ℂ).smulRight (knPhi' F w)).restrictScalars ℝ)
      (ball (0 : ℂ) ρ \ closedBall 0 ε) w := fun w hw =>
    ((h.hasDerivAt_phi (hAsub hw).1 (hAsub hw).2).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm hf'
    (h.phi_injOn.mono hAsub) (fun _ => 1)
  rw [setLIntegral_one] at key
  rw [key]
  refine setLIntegral_congr_fun hAm fun w _ => ?_
  rw [kn_det_smulRight, mul_one, abs_of_nonneg (by positivity)]

/-- `∫_{-π}^{π} |Φ'(r e^{iθ})|² dθ ≥ 2π(|g₂|² + r⁻⁴)`. -/
theorem circle_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    2 * π * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2) ≤
      ∫ θ in Ioo (-π) π, ‖knPhi' F (circleMap 0 r θ)‖ ^ 2 := by
  have hc := h.continuous_phi'_circle hr hr1
  have hper : Function.Periodic (fun θ : ℝ => ‖knPhi' F (circleMap 0 r θ)‖ ^ 2) (2 * π) :=
    (periodic_circleMap 0 r).comp fun z => ‖knPhi' F z‖ ^ 2
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    hshift]
  have hα : ∫ θ in (0 : ℝ)..2 * π, knPhi' F (circleMap 0 r θ) * exp (2 * θ * I) =
      2 * π * (-(((r : ℂ) ^ 2)⁻¹)) := by
    rw [h.int_alpha hr hr1]
    have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    field_simp
  have hb := kn_bessel hc (h.int_beta hr hr1) hα
  have hn : ‖-(((r : ℂ) ^ 2)⁻¹)‖ = (r ^ 2)⁻¹ := by
    rw [norm_neg, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hn] at hb
  exact hb

/-- **The area lower bound**: `area Φ(ε < |w| < ρ) ≥ π|g₂|²(ρ² - ε²) + π(ε⁻² - ρ⁻²)`. -/
theorem area_lower {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ : ρ < 1) :
    ENNReal.ofReal (π * ‖knG2 F‖ ^ 2 * (ρ ^ 2 - ε ^ 2) + π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹)) ≤
      volume (knPhi F '' (ball (0 : ℂ) ρ \ closedBall 0 ε)) := by
  rw [h.volume_image_annulus hε hρ]
  have hAm : MeasurableSet (ball (0 : ℂ) ρ \ closedBall 0 ε) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hAsub := kn_annulus_subset hε hρ
  -- polar coordinates
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((ball (0 : ℂ) ρ \ closedBall 0 ε).indicator fun w => ENNReal.ofReal (‖knPhi' F w‖ ^ 2))
  rw [lintegral_indicator hAm] at hpolar
  rw [← hpolar]
  -- the rectangle `(ε, ρ) × (-π, π)` inside the polar target
  have hrect : Ioo ε ρ ×ˢ Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun x hx => lt_trans hε hx.1) le_rfl
  have hrectm : MeasurableSet (Ioo ε ρ ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have hmem : ∀ p ∈ Ioo ε ρ ×ˢ Ioo (-π) π,
      Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ \ closedBall 0 ε := by
    intro p hp
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_trans hε hp.1.1)]
    constructor
    · rw [mem_ball_zero_iff, hn]
      exact hp.1.2
    · rw [mem_closedBall_zero_iff, hn]
      exact not_le.2 hp.1.1
  -- on the rectangle the integrand is `ofReal (r · |Φ'(r e^{iθ})|²)`
  have hcongr : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ \ closedBall 0 ε).indicator
        (fun w => ENNReal.ofReal (‖knPhi' F w‖ ^ 2)) (Complex.polarCoord.symm p) =
      ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ‖knPhi' F (circleMap 0 p.1 p.2)‖ ^ 2) := by
    refine setLIntegral_congr_fun hrectm fun p hp => ?_
    rw [Set.indicator_of_mem (hmem p hp), smul_eq_mul, kn_polar_symm_eq,
      ENNReal.ofReal_mul (lt_trans hε hp.1.1).le]
  have hmono : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal (p.1 * ‖knPhi' F (circleMap 0 p.1 p.2)‖ ^ 2) ≤
      ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ \ closedBall 0 ε).indicator
        (fun w => ENNReal.ofReal (‖knPhi' F w‖ ^ 2)) (Complex.polarCoord.symm p) := by
    rw [← hcongr]
    exact lintegral_mono_set hrect
  refine le_trans ?_ hmono
  -- Tonelli on the rectangle
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Ioo ε ρ ×ˢ Ioo (-π) π) =
      ((volume : Measure ℝ).restrict (Ioo ε ρ)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖knPhi' F (circleMap 0 p.1 p.2)‖ ^ 2)
      (Ioo ε ρ ×ˢ Ioo (-π) π) := by
    have hmaps : ∀ p ∈ Ioo ε ρ ×ˢ Ioo (-π) π, circleMap 0 p.1 p.2 ∈ ball (0 : ℂ) 1 \ {0} :=
      fun p hp => by rw [← kn_polar_symm_eq]; exact hAsub (hmem p hp)
    have hcm : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
      simp only [kn_circleMap_eq]
      fun_prop
    exact continuousOn_fst.mul ((h.continuousOn_phi'.comp hcm.continuousOn hmaps).norm.pow 2)
  have hae : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 * ‖knPhi' F (circleMap 0 p.1 p.2)‖ ^ 2))
      (((volume : Measure ℝ).restrict (Ioo ε ρ)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π))) := by
    rw [← hprod]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable hrectm)
  have htonelli : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal (p.1 * ‖knPhi' F (circleMap 0 p.1 p.2)‖ ^ 2) =
      ∫⁻ r in Ioo ε ρ, ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (r * ‖knPhi' F (circleMap 0 r θ)‖ ^ 2) := by
    rw [hprod, lintegral_prod _ hae]
  rw [htonelli]
  -- the inner integral, for each radius
  have hinner : ∀ r ∈ Ioo ε ρ,
      ENNReal.ofReal (2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)) ≤
        ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (r * ‖knPhi' F (circleMap 0 r θ)‖ ^ 2) := by
    intro r hr
    have hr0 : 0 < r := lt_trans hε hr.1
    have hr1 : r < 1 := lt_trans hr.2 hρ
    have hc : Continuous fun θ : ℝ => r * ‖knPhi' F (circleMap 0 r θ)‖ ^ 2 :=
      continuous_const.mul ((h.continuous_phi'_circle hr0 hr1).norm.pow 2)
    have hint : Integrable (fun θ : ℝ => r * ‖knPhi' F (circleMap 0 r θ)‖ ^ 2)
        (volume.restrict (Ioo (-π) π)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).1
        (hc.intervalIntegrable _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [MeasureTheory.integral_const_mul]
    calc 2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)
        = r * (2 * π * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)) := by ring
      _ ≤ r * ∫ θ in Ioo (-π) π, ‖knPhi' F (circleMap 0 r θ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (h.circle_lower hr0 hr1) hr0.le
  -- the outer integral
  have hcont2 : ContinuousOn (fun r : ℝ => 2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2))
      (uIcc ε ρ) := by
    refine (continuousOn_const.mul continuousOn_id).mul
      (continuousOn_const.add (((continuousOn_id.pow 2).inv₀ ?_).pow 2))
    intro r hr
    rw [uIcc_of_le hερ.le] at hr
    exact pow_ne_zero 2 (by linarith [hr.1] : r ≠ 0)
  have hint2 : Integrable (fun r : ℝ => 2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2))
      (volume.restrict (Ioo ε ρ)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hερ.le).1 hcont2.intervalIntegrable
  calc ENNReal.ofReal (π * ‖knG2 F‖ ^ 2 * (ρ ^ 2 - ε ^ 2) + π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹))
      = ENNReal.ofReal (∫ r in Ioo ε ρ, 2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hερ.le,
          kn_ftc hε hερ]
    _ = ∫⁻ r in Ioo ε ρ, ENNReal.ofReal (2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)) := by
        refine ofReal_integral_eq_lintegral_ofReal hint2 ?_
        show ∀ᵐ r ∂(volume.restrict (Ioo ε ρ)),
          (0 : ℝ) ≤ 2 * π * r * (‖knG2 F‖ ^ 2 + ((r ^ 2)⁻¹) ^ 2)
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun r hr => ?_
        have : 0 < r := lt_trans hε hr.1
        positivity
    _ ≤ ∫⁻ r in Ioo ε ρ, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (r * ‖knPhi' F (circleMap 0 r θ)‖ ^ 2) :=
        setLIntegral_mono' measurableSet_Ioo hinner

end knHyp

/-! ### `kn_` helpers, part 3: the ellipse containment and the limits

For small `ε`, `Φ(ε < |w| < ρ)` lies in `g₁ + A_ε(closedBall 0 (ε⁻¹ + K ε²))` with
`A_ε ζ = ζ + g₂ ε² conj ζ`, a set of area `(1 - |g₂|²ε⁴) π (ε⁻¹ + K ε²)²`.  Comparing with the
area lower bound and letting `ε → 0`, then `ρ → 1`, gives `|g₂| ≤ 1`. -/

/-- The real-linear map `A_a ζ = ζ + a conj ζ`. -/
def knA (a : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun ζ := ζ + a * conj ζ
  map_add' ζ η := by
    simp only [map_add]
    ring
  map_smul' r ζ := by
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
    ring

theorem knA_apply (a ζ : ℂ) : knA a ζ = ζ + a * conj ζ := rfl

theorem kn_det_knA (a : ℂ) : LinearMap.det (knA a) = 1 - ‖a‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, knA_apply,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The inverse of `A_a` for `‖a‖ < 1`: `A_a ((v - a conj v)/(1 - ‖a‖²)) = v`. -/
theorem knA_inv_apply {a : ℂ} (ha : ‖a‖ < 1) (v : ℂ) :
    knA a ((v - a * conj v) / ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) = v := by
  have hpos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hne : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  rw [knA_apply, map_div₀, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  push_cast
  linear_combination (-v) * Complex.mul_conj' a

/-- The area of the ellipse `g + A_a(closedBall 0 R)`. -/
theorem kn_volume_ellipse {a : ℂ} (ha : ‖a‖ < 1) (g : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    volume ((fun ζ => g + knA a ζ) '' closedBall (0 : ℂ) R) =
      ENNReal.ofReal ((1 - ‖a‖ ^ 2) * (π * R ^ 2)) := by
  have hpos : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have e : (fun ζ => g + knA a ζ) '' closedBall (0 : ℂ) R =
      (fun ζ => g + ζ) '' (knA a '' closedBall 0 R) := by
    rw [Set.image_image]
  rw [e, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, kn_det_knA,
    abs_of_nonneg hpos, Complex.volume_closedBall, ENNReal.ofReal_mul hpos,
    ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal, mul_comm (ENNReal.ofReal R ^ 2)]

/-- The elementary inequality behind the containment, for `ε ≤ t ≤ ρ ≤ 1` and small `ε`. -/
theorem kn_key_ineq {n C ρ ε t M K : ℝ} (hn : 0 ≤ n) (hC : 0 ≤ C) (hρ : ρ ≤ 1) (hε : 0 < ε)
    (hεt : ε ≤ t) (htρ : t ≤ ρ) (hε1 : ε ≤ 1) (hε2 : ε * (2 * ρ * (n + C)) ≤ 1)
    (hM : M = n ^ 2 * ρ + n * C * ρ ^ 2) (hK : K = C + M + 2 * n ^ 2) (hε3 : ε * K ≤ 1) :
    t⁻¹ + n * (t ^ 2 - ε ^ 2) / t + C * t ^ 2 + n ^ 2 * ε ^ 2 * t + n * C * ε ^ 2 * t ^ 2 ≤
      (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) := by
  have ht : 0 < t := lt_of_lt_of_le hε hεt
  have hρ0 : 0 < ρ := lt_of_lt_of_le ht htρ
  have htε : 0 ≤ t - ε := sub_nonneg.2 hεt
  have hq : 0 < (ρ * ε)⁻¹ := by positivity
  -- (A) `1/t ≤ 1/ε - (t - ε)/(ρ ε)`
  have hA : t⁻¹ ≤ ε⁻¹ - (t - ε) * (ρ * ε)⁻¹ := by
    have e1 : ε⁻¹ - t⁻¹ = (t - ε) * (t * ε)⁻¹ := by
      field_simp
    have e2 : (t - ε) * (ρ * ε)⁻¹ ≤ (t - ε) * (t * ε)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) htε
    linarith
  -- (B) `n (t² - ε²)/t ≤ 2 n (t - ε)`
  have hB : n * (t ^ 2 - ε ^ 2) / t ≤ 2 * n * (t - ε) := by
    have e : n * (t ^ 2 - ε ^ 2) / t = n * (t - ε) * ((t + ε) / t) := by
      field_simp
      ring
    have h2 : (t + ε) / t ≤ 2 := by
      rw [div_le_iff₀ ht]
      linarith
    rw [e]
    calc n * (t - ε) * ((t + ε) / t) ≤ n * (t - ε) * 2 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hn htε)
      _ = 2 * n * (t - ε) := by ring
  -- (C) `C t² ≤ 2 C (t - ε) + C ε²`
  have hCt : C * t ^ 2 ≤ 2 * C * (t - ε) + C * ε ^ 2 := by
    have h1 : t ^ 2 - ε ^ 2 ≤ 2 * (t - ε) := by
      have := mul_nonneg htε (show 0 ≤ 2 - (t + ε) by linarith)
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 hC
    linarith
  -- (D), (E)
  have hD : n ^ 2 * ε ^ 2 * t ≤ n ^ 2 * ε ^ 2 * ρ :=
    mul_le_mul_of_nonneg_left htρ (by positivity)
  have hE : n * C * ε ^ 2 * t ^ 2 ≤ n * C * ε ^ 2 * ρ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le htρ 2) (by positivity)
  -- (F) the bracket is nonpositive
  have hF : (t - ε) * (2 * n + 2 * C - (ρ * ε)⁻¹) ≤ 0 := by
    have h1 : 2 * n + 2 * C ≤ (ρ * ε)⁻¹ := by
      have h2 : (2 * n + 2 * C) * (ρ * ε) ≤ 1 := by linarith
      calc 2 * n + 2 * C = (2 * n + 2 * C) * (ρ * ε) * (ρ * ε)⁻¹ := by
            field_simp
        _ ≤ 1 * (ρ * ε)⁻¹ := mul_le_mul_of_nonneg_right h2 hq.le
        _ = (ρ * ε)⁻¹ := one_mul _
    have := mul_nonneg htε (sub_nonneg.2 h1)
    linarith
  -- (G) the factor `1 - n²ε⁴`
  have hG : ε⁻¹ + K * ε ^ 2 - 2 * n ^ 2 * ε ^ 3 ≤ (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) := by
    have e : (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) =
        ε⁻¹ + K * ε ^ 2 - n ^ 2 * ε ^ 3 - K * n ^ 2 * ε ^ 6 := by
      field_simp
      ring
    rw [e]
    have hKε : K * ε ^ 3 ≤ 1 := by
      have h2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
      have hK0 : 0 ≤ K := by
        rw [hK, hM]
        positivity
      calc K * ε ^ 3 = (ε * K) * ε ^ 2 := by ring
        _ ≤ 1 * 1 := mul_le_mul hε3 h2 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    have := mul_le_mul_of_nonneg_left hKε (by positivity : 0 ≤ n ^ 2 * ε ^ 3)
    linarith
  -- (H) `(C + M) ε² ≤ K ε² - 2 n² ε³`
  have hH : (C + M) * ε ^ 2 ≤ K * ε ^ 2 - 2 * n ^ 2 * ε ^ 3 := by
    have := mul_le_mul_of_nonneg_left hε1 (by positivity : 0 ≤ n ^ 2 * ε ^ 2)
    rw [hK]
    linarith
  -- assemble
  have hsum : t⁻¹ + n * (t ^ 2 - ε ^ 2) / t + C * t ^ 2 + n ^ 2 * ε ^ 2 * t +
      n * C * ε ^ 2 * t ^ 2 ≤
        ε⁻¹ + (t - ε) * (2 * n + 2 * C - (ρ * ε)⁻¹) + (C + M) * ε ^ 2 := by
    rw [hM]
    linarith [hA, hB, hCt, hD, hE]
  linarith [hsum, hF, hG, hH]

namespace knHyp

variable {F : ℂ → ℂ} (h : knHyp F)
include h

/-- **Containment**: for small `ε`, `Φ(ε < |w| < ρ)` lies in the ellipse
`g₁ + A_{g₂ ε²}(closedBall 0 (ε⁻¹ + K ε²))`. -/
theorem containment {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1) :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ w ∈ ball (0 : ℂ) ρ \ closedBall 0 ε, knPhi F w ∈
        (fun ζ => knG1 F + knA (knG2 F * ε ^ 2) ζ) '' closedBall 0 (ε⁻¹ + K * ε ^ 2) := by
  obtain ⟨C₀, hC₀⟩ := h.exists_bound_G₃ hρ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max C₀ 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ le_max_right _ _
  have hCb : ∀ w ∈ closedBall (0 : ℂ) ρ, ‖knG₃ F w‖ ≤ C := fun w hw =>
    (hC₀ w hw).trans (hC ▸ le_max_left _ _)
  obtain ⟨n, hn⟩ : ∃ n : ℝ, ‖knG2 F‖ = n := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ norm_nonneg _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = n ^ 2 * ρ + n * C * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C + M + 2 * n ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K, min (min 1 (1 / (2 * ρ * (n + C) + 1))) (1 / (K + n + 1)), hK0, by positivity, ?_⟩
  intro ε hε hεε₀ w hw
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεε₀ (min_le_left _ _)).le.trans (min_le_left _ _)
  have hε2 : ε * (2 * ρ * (n + C)) ≤ 1 := by
    have h1 : ε < 1 / (2 * ρ * (n + C) + 1) :=
      lt_of_lt_of_le hεε₀ ((min_le_left _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hε3 : ε * (K + n + 1) < 1 := by
    have h1 : ε < 1 / (K + n + 1) := lt_of_lt_of_le hεε₀ (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at h1
  have hε3' : ε * K ≤ 1 := by nlinarith
  -- the point `w`
  have hw0 : w ≠ 0 := (kn_annulus_subset hε hρ hw).2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖w‖ = t := ⟨_, rfl⟩
  have ht1 : ε < t := ht ▸ not_le.1 fun hle => hw.2 (mem_closedBall_zero_iff.2 hle)
  have ht2 : t < ρ := ht ▸ mem_ball_zero_iff.1 hw.1
  have ht0 : 0 < t := lt_trans hε ht1
  -- `a = g₂ ε²`, with `‖a‖ = n ε² < 1`
  have hna : ‖knG2 F * (ε : ℂ) ^ 2‖ = n * ε ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le, hn]
  have ha1 : ‖knG2 F * (ε : ℂ) ^ 2‖ < 1 := by
    rw [hna]
    have : n * ε ^ 2 ≤ n * ε := mul_le_mul_of_nonneg_left (by nlinarith) hn0
    nlinarith
  -- the decomposition of `v - a conj v`, `v = Φ w - g₁`
  have hconjw : conj w = ((t ^ 2 : ℝ) : ℂ) / w := by
    rw [eq_div_iff hw0, ← ht, ← Complex.normSq_eq_norm_sq, mul_comm, Complex.mul_conj]
  have hdecomp : (knPhi F w - knG1 F) - knG2 F * (ε : ℂ) ^ 2 * conj (knPhi F w - knG1 F) =
      w⁻¹ + knG2 F * w * (((t ^ 2 - ε ^ 2) / t ^ 2 : ℝ) : ℂ) +
        (w ^ 2 * knG₃ F w - knG2 F * (ε : ℂ) ^ 2 * conj (knG2 F * w) -
          knG2 F * (ε : ℂ) ^ 2 * conj (w ^ 2 * knG₃ F w)) := by
    rw [h.phi_expand hw0]
    simp only [map_add, map_sub, map_mul, map_inv₀, map_pow, hconjw]
    have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    have hε0' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
    push_cast
    field_simp
    ring
  have hG₃ : ‖knG₃ F w‖ ≤ C := hCb w (mem_closedBall_zero_iff.2 (ht ▸ ht2.le))
  -- the norm estimate
  have hnorm : ‖(knPhi F w - knG1 F) - knG2 F * (ε : ℂ) ^ 2 * conj (knPhi F w - knG1 F)‖ ≤
      t⁻¹ + n * (t ^ 2 - ε ^ 2) / t + C * t ^ 2 + n ^ 2 * ε ^ 2 * t + n * C * ε ^ 2 * t ^ 2 := by
    rw [hdecomp]
    have h1 : ‖w⁻¹‖ = t⁻¹ := by rw [norm_inv, ht]
    have h2 : ‖knG2 F * w * (((t ^ 2 - ε ^ 2) / t ^ 2 : ℝ) : ℂ)‖ = n * (t ^ 2 - ε ^ 2) / t := by
      have hnn : 0 ≤ (t ^ 2 - ε ^ 2) / t ^ 2 :=
        div_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hε.le ht1.le 2)) (by positivity)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, hn, ht]
      field_simp
    have h3 : ‖w ^ 2 * knG₃ F w‖ ≤ C * t ^ 2 := by
      rw [norm_mul, norm_pow, ht]
      calc t ^ 2 * ‖knG₃ F w‖ ≤ t ^ 2 * C := mul_le_mul_of_nonneg_left hG₃ (by positivity)
        _ = C * t ^ 2 := mul_comm _ _
    have h4 : ‖knG2 F * (ε : ℂ) ^ 2 * conj (knG2 F * w)‖ = n ^ 2 * ε ^ 2 * t := by
      rw [norm_mul, hna, Complex.norm_conj, norm_mul, hn, ht]
      ring
    have h5 : ‖knG2 F * (ε : ℂ) ^ 2 * conj (w ^ 2 * knG₃ F w)‖ ≤ n * C * ε ^ 2 * t ^ 2 := by
      rw [norm_mul, hna, Complex.norm_conj, norm_mul, norm_pow, ht]
      calc n * ε ^ 2 * (t ^ 2 * ‖knG₃ F w‖) ≤ n * ε ^ 2 * (t ^ 2 * C) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG₃ (by positivity))
              (by positivity)
        _ = n * C * ε ^ 2 * t ^ 2 := by ring
    calc ‖w⁻¹ + knG2 F * w * (((t ^ 2 - ε ^ 2) / t ^ 2 : ℝ) : ℂ) +
          (w ^ 2 * knG₃ F w - knG2 F * (ε : ℂ) ^ 2 * conj (knG2 F * w) -
            knG2 F * (ε : ℂ) ^ 2 * conj (w ^ 2 * knG₃ F w))‖
        ≤ ‖w⁻¹‖ + ‖knG2 F * w * (((t ^ 2 - ε ^ 2) / t ^ 2 : ℝ) : ℂ)‖ +
          (‖w ^ 2 * knG₃ F w‖ + ‖knG2 F * (ε : ℂ) ^ 2 * conj (knG2 F * w)‖ +
            ‖knG2 F * (ε : ℂ) ^ 2 * conj (w ^ 2 * knG₃ F w)‖) := by
          refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ t⁻¹ + n * (t ^ 2 - ε ^ 2) / t + C * t ^ 2 + n ^ 2 * ε ^ 2 * t +
          n * C * ε ^ 2 * t ^ 2 := by
          rw [h1, h2, h4]
          linarith
  have hineq := kn_key_ineq hn0 hC0 hρ.le hε ht1.le ht2.le hε1 hε2 hM hK hε3'
  have h1a : 0 < 1 - ‖knG2 F * (ε : ℂ) ^ 2‖ ^ 2 := by nlinarith [norm_nonneg (knG2 F * (ε : ℂ) ^ 2)]
  refine ⟨((knPhi F w - knG1 F) - knG2 F * (ε : ℂ) ^ 2 * conj (knPhi F w - knG1 F)) /
    ((1 - ‖knG2 F * (ε : ℂ) ^ 2‖ ^ 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg h1a.le,
      div_le_iff₀ h1a, hna]
    calc ‖(knPhi F w - knG1 F) - knG2 F * (ε : ℂ) ^ 2 * conj (knPhi F w - knG1 F)‖
        ≤ t⁻¹ + n * (t ^ 2 - ε ^ 2) / t + C * t ^ 2 + n ^ 2 * ε ^ 2 * t +
          n * C * ε ^ 2 * t ^ 2 := hnorm
      _ ≤ (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) := hineq
      _ = (ε⁻¹ + K * ε ^ 2) * (1 - (n * ε ^ 2) ^ 2) := mul_comm _ _
  · show knG1 F + knA (knG2 F * (ε : ℂ) ^ 2) _ = knPhi F w
    rw [knA_inv_apply ha1]
    ring

/-- For every `ρ < 1`: `|g₂|² ρ² ≤ ρ⁻²`. -/
theorem sq_norm_G2_mul_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1) :
    ‖knG2 F‖ ^ 2 * ρ ^ 2 ≤ (ρ ^ 2)⁻¹ := by
  obtain ⟨K, ε₀, hK, hε₀, hcont⟩ := h.containment hρ0 hρ
  obtain ⟨n, hn⟩ : ∃ n : ℝ, ‖knG2 F‖ = n := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ norm_nonneg _
  rw [hn]
  -- the comparison of areas, for small `ε`
  have key : ∀ ε, 0 < ε → ε < ε₀ → ε < ρ → n * ε ^ 2 < 1 →
      n ^ 2 * ρ ^ 2 ≤ (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 := by
    intro ε hε hε₀' hερ hna
    have hlow := h.area_lower hε hερ hρ
    rw [hn] at hlow
    have hsub : knPhi F '' (ball (0 : ℂ) ρ \ closedBall 0 ε) ⊆
        (fun ζ => knG1 F + knA (knG2 F * ε ^ 2) ζ) '' closedBall 0 (ε⁻¹ + K * ε ^ 2) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hcont ε hε hε₀' w hw
    have ha : ‖knG2 F * (ε : ℂ) ^ 2‖ = n * ε ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le, hn]
    have hup := measure_mono (μ := volume) hsub
    rw [kn_volume_ellipse (by rw [ha]; exact hna) _ (by positivity), ha] at hup
    have hR : 0 ≤ (1 - (n * ε ^ 2) ^ 2) * (π * (ε⁻¹ + K * ε ^ 2) ^ 2) := by
      have : (n * ε ^ 2) ^ 2 < 1 := by nlinarith [mul_nonneg hn0 (sq_nonneg ε)]
      positivity
    have hreal := (ENNReal.ofReal_le_ofReal_iff hR).1 (hlow.trans hup)
    -- divide by `π` and expand
    have h3 : (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) ^ 2 =
        (ε ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 - n ^ 2 * ε ^ 2 - 2 * K * n ^ 2 * ε ^ 5 -
          K ^ 2 * n ^ 2 * ε ^ 8 := by
      field_simp
      ring
    have h4 : n ^ 2 * (ρ ^ 2 - ε ^ 2) + ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) ≤
        (1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) ^ 2 := by
      have e : π * n ^ 2 * (ρ ^ 2 - ε ^ 2) + π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) =
          π * (n ^ 2 * (ρ ^ 2 - ε ^ 2) + ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹)) := by ring
      have e' : (1 - (n * ε ^ 2) ^ 2) * (π * (ε⁻¹ + K * ε ^ 2) ^ 2) =
          π * ((1 - (n * ε ^ 2) ^ 2) * (ε⁻¹ + K * ε ^ 2) ^ 2) := by ring
      rw [e, e'] at hreal
      exact le_of_mul_le_mul_left hreal Real.pi_pos
    rw [h3] at h4
    have hp1 : 0 ≤ 2 * K * n ^ 2 * ε ^ 5 := by positivity
    have hp2 : 0 ≤ K ^ 2 * n ^ 2 * ε ^ 8 := by positivity
    linarith
  -- let `ε → 0⁺`
  have hlim : Filter.Tendsto (fun ε : ℝ => (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4)
      (𝓝[>] 0) (𝓝 ((ρ ^ 2)⁻¹ + 2 * K * 0 + K ^ 2 * 0 ^ 4)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_id.pow 4))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), n ^ 2 * ρ ^ 2 ≤ (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 := by
    have hδ : (0 : ℝ) < min (min ε₀ ρ) (1 / (n + 1)) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε1 : ε < ε₀ := lt_of_lt_of_le hε.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hε2 : ε < ρ := lt_of_lt_of_le hε.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hε3 : ε < 1 / (n + 1) := lt_of_lt_of_le hε.2 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at hε3
    have hna : n * ε ^ 2 < 1 := by
      have : ε < 1 := by nlinarith
      nlinarith [mul_nonneg hn0 hε.1.le]
    exact key ε hε.1 hε1 hε2 hna
  have := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  simpa using this

/-- **`|g₂| ≤ 1`**: let `ρ → 1` in `|g₂|² ρ⁴ ≤ 1`. -/
theorem norm_G2_le_one : ‖knG2 F‖ ≤ 1 := by
  have hsq : ‖knG2 F‖ ^ 2 * (1 : ℝ) ^ 4 ≤ 1 := by
    have hρ : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖knG2 F‖ ^ 2 * ρ ^ 4 ≤ 1 := by
      intro ρ h0 h1
      have := h.sq_norm_G2_mul_le h0 h1
      have hρ2 : 0 < ρ ^ 2 := by positivity
      have h2 := mul_le_mul_of_nonneg_right this hρ2.le
      rw [inv_mul_cancel₀ hρ2.ne'] at h2
      calc ‖knG2 F‖ ^ 2 * ρ ^ 4 = ‖knG2 F‖ ^ 2 * ρ ^ 2 * ρ ^ 2 := by ring
        _ ≤ 1 := h2
    refine le_of_tendsto (f := fun ρ : ℝ => ‖knG2 F‖ ^ 2 * ρ ^ 4) (x := 𝓝[<] (1 : ℝ)) ?_ ?_
    · exact (continuous_const.mul (continuous_id.pow 4)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with ρ hρ'
      exact hρ ρ hρ'.1 hρ'.2
  nlinarith [norm_nonneg (knG2 F)]

end knHyp

/-- **Kraus–Nehari coefficient bound**: a univalent `F` in the unit disc normalized by
`F 0 = 0` and `F' 0 = 1` satisfies `‖F'''(0) - (3/2) F''(0)²‖ ≤ 6`, i.e. `|a₃ - a₂²| ≤ 1`. -/
theorem kraus_nehari_coeff {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : Set.InjOn F (ball (0 : ℂ) 1)) (h0 : F 0 = 0) (h1 : deriv F 0 = 1) :
    ‖deriv (deriv (deriv F)) 0 - (3 / 2) * deriv (deriv F) 0 ^ 2‖ ≤ 6 := by
  have hk : knHyp F := ⟨hF, hinj, h0, h1⟩
  rw [hk.schwarzian_eq, norm_mul, norm_neg, Complex.norm_ofNat]
  have := hk.norm_G2_le_one
  linarith

end LiZhongQC
