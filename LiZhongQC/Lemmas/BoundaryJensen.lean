import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import LiZhongQC.Lemmas.PoissonExtension
import LiZhongQC.Lemmas.CaratheodoryJordan
import LiZhongQC.Ch02.S13_Representation

/-!
# Boundary uniqueness in Jensen form (the BU-Jensen layer of Lemma 35.1)

A holomorphic `φ` on `Δ` with `φ ≢ 0` cannot have **arbitrarily short crossings of a sector near the boundary**:
sector cuts `τₙ` (arcs from one side of a sector to the other, near `∂Δ`) whose `√|φ|`-lengths tend to `0`, while
the two sides of the sector have finite `√|φ|`-length (`buj_no_short_crossings`).  This is the analytic core of
Lemma 35.1 (Strebel); the book's route through `E^{1/2}`, Hardy spaces and Privalov's theorem is replaced by
Jensen's formula on Riemann maps.

## The argument (for the `n`-th cut)
1. The cut and the two sides bound a Jordan domain `Dₙ` (`buj_inside_isJordanDomain`). Its Riemann map
   `ρₙ : Δ̄ → D̄ₙ` has `ρₙ(0) = z₀` and `|ρₙ'(0)| ≥ δ` (`buj_sector_uniformizer`), and its boundary map has an
   arclength measure `dVₙ` (`buj_sector_boundary_measure`).
2. The harmonic measure of the cut seen from `z₀` is bounded below uniformly (`buj_harmonic_measure_lb`).
3. Jensen's formula for `G = (φ ∘ ρₙ) ρₙ'²` (`buj_log_norm_le_circleAverage`) is combined with the tangent bound
   (`buj_log_le_tangent`) and with the level-curve length estimate LC (`buj_poisson_diff_le`, `buj_LC_r`, `buj_LC`).
   This gives `2π(log|φ(z₀)| + 2 log δ) ≤ 2m log(ℓₙ/m) + 2M` (`buj_JL`), where `ℓₙ → 0` is the length of the cut.
4. `buj_close` concludes.

## Status
Everything in this file is proved and axiom-clean (s21u P2b, 2026-09-27): the pieces named above, the Poisson
lemmas, `buj_LC_r` (LC at a fixed radius), `buj_LC`, `buj_JL`, `buj_sector_uniformizer`,
`buj_sector_boundary_measure` and `buj_no_short_crossings`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped Real ENNReal

noncomputable section

namespace LiZhongQC

/-! ## Jensen, the tangent bound, the inside of a Jordan curve, and lemma LC at a fixed radius -/

/-- **(J1) Sub-mean value for `log ‖G‖`** (from Mathlib's Jensen formula): for `G` analytic on a
neighbourhood of `closedBall 0 r` with `G 0 ≠ 0`, `log ‖G 0‖ ≤ ⨍_{|z| = r} log ‖G‖`. -/
theorem buj_log_norm_le_circleAverage {G : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hG : AnalyticOnNhd ℂ G (closedBall 0 |r|)) (hG0 : G 0 ≠ 0) :
    Real.log ‖G 0‖ ≤ Real.circleAverage (fun z => Real.log ‖G z‖) 0 r := by
  rw [hG.circleAverage_log_norm hr.ne' hG0]
  refine le_add_of_nonneg_left (finsum_nonneg fun u => ?_)
  have hd : (0 : ℤ) ≤ MeromorphicOn.divisor G (closedBall 0 |r|) u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hG u
  by_cases hu0 : u = 0
  · subst hu0
    simp
  by_cases hu : u ∈ closedBall (0 : ℂ) |r|
  · refine mul_nonneg (by exact_mod_cast hd) (Real.log_nonneg ?_)
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have hur : ‖u‖ ≤ r := by
      have := mem_closedBall_zero_iff.1 hu
      rwa [abs_of_pos hr] at this
    rw [zero_sub, norm_neg, ← div_eq_mul_inv, le_div_iff₀ hun, one_mul]
    exact hur
  · rw [(MeromorphicOn.divisor G (closedBall 0 |r|)).apply_eq_zero_of_notMem hu]
    simp

/-- **(J2) Tangent-line bound for `log`**: for `x > 0` and `a > 0`,
`log x ≤ 2 (log a + √x / a - 1)`. Integrated over the `τ`-arc it replaces Jensen's inequality
for the concave `log`; with `a = ℓ_φ(τ)/m` it gives the term `2 m log(ℓ_φ(τ)/m)`. -/
theorem buj_log_le_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ 2 * (Real.log a + Real.sqrt x / a - 1) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hx.le]
  have h2 : Real.log (Real.sqrt x / a) ≤ Real.sqrt x / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hs ha)
  rw [Real.log_div hs.ne' ha.ne'] at h2
  rw [h1]
  linarith

/-- **(JD) The inside of a Jordan curve is a Jordan domain with frontier the curve.** -/
theorem buj_inside_isJordanDomain {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    ∃ A : Set ℂ, IsJordanDomain A ∧ Bornology.IsBounded A ∧ frontier A = C ∧ Disjoint A C ∧
      ∃ B : Set ℂ, IsOpen B ∧ IsConnected B ∧ ¬ Bornology.IsBounded B ∧ Disjoint A B ∧
        Disjoint B C ∧ A ∪ B ∪ C = univ := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩ :=
    jordan_curve_theorem_complex_bounded hC
  obtain ⟨hfrA, -⟩ :=
    frontier_pieces_eq_of_jordan_curve_theorem_complex hC hA hB hAc hBc hAB hAC hBC huniv
  refine ⟨A, ⟨hA, hAc, ?_⟩, hAb, hfrA, hAC, B, hB, hBc, hBb, hAB, hBC, huniv⟩
  rw [frontier_toExt_of_isBounded' hAb hA, hfrA]
  exact hC

/-- The Poisson kernel is invariant under a common rotation of its two arguments. -/
theorem buj_poissonKernel_rot {w z e : ℂ} (he : ‖e‖ = 1) :
    poissonKernel 0 (w * e) (z * e) = poissonKernel 0 w z := by
  simp only [poissonKernel, sub_zero, norm_mul, he, mul_one, ← sub_mul]

/-- The Poisson kernel is non-negative on the unit circle for `w` in the disc. -/
theorem buj_poissonKernel_nonneg {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ = 1) :
    0 ≤ poissonKernel 0 w z := by
  simp only [poissonKernel, sub_zero, hz]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (sq_nonneg _)

/-- `circleMap 0 1 (θ + h) = circleMap 0 1 θ * exp (h I)`. -/
theorem buj_circleMap_add (θ h : ℝ) :
    circleMap 0 1 (θ + h) = circleMap 0 1 θ * exp (h * I) := by
  simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul,
    Complex.exp_add]

/-- **(LC1) The Poisson difference quotient bound.** For `f` holomorphic in `Δ` and continuous
on `Δ̄`, `w ∈ Δ` and a rotation angle `h`,
`‖f(w e^{ih}) - f(w)‖ ≤ ⨍_{|z|=1} P(w, z) ‖f(z e^{ih}) - f(z)‖`.
With `w = r e^{it}`, integrated against a weight in `t` and divided by `h → 0`, this bounds the
weighted length of the level curve `f(|w| = r)` by the Poisson-smoothed weight integrated
against the boundary length measure. -/
theorem buj_poisson_diff_le {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball 0 1)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) (h : ℝ) :
    ‖f (w * exp (h * I)) - f w‖ ≤
      Real.circleAverage (fun z => poissonKernel 0 w z * ‖f (z * exp (h * I)) - f z‖) 0 1 := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have he : ‖exp (h * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I h
  have hw' : w * exp (h * I) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, he, mul_one]; exact hwn
  -- continuity of the boundary integrands
  have hfc : ContinuousOn f (closedBall 0 1) := by
    have := hf.continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hsph : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  have hsph' : ∀ θ : ℝ, circleMap 0 1 θ * exp (h * I) ∈ closedBall (0 : ℂ) 1 := fun θ => by
    rw [← buj_circleMap_add]; exact hsph _
  have hcf : Continuous fun θ : ℝ => f (circleMap 0 1 θ) :=
    hfc.comp_continuous (continuous_circleMap 0 1) hsph
  have hcf' : Continuous fun θ : ℝ => f (circleMap 0 1 θ * exp (h * I)) :=
    hfc.comp_continuous ((continuous_circleMap 0 1).mul continuous_const) hsph'
  have hne : ∀ θ : ℝ, circleMap 0 1 θ - w ≠ 0 := fun θ h0 => by
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp [circleMap_zero]
    rw [sub_eq_zero] at h0
    rw [h0] at h1
    linarith
  have hcP : Continuous fun θ : ℝ => poissonKernel 0 w (circleMap 0 1 θ) := by
    simp only [poissonKernel, sub_zero]
    refine Continuous.div (by fun_prop) (by fun_prop) fun θ => ?_
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hne θ))
  -- the two Poisson representations, the second one rotated by `h`
  have hrep₀ := (hf.circleAverage_poissonKernel_smul (c := 0) hw).symm
  have hrep₁ := (hf.circleAverage_poissonKernel_smul (c := 0) hw').symm
  rw [Real.circleAverage_eq_integral_add h] at hrep₁
  have hrot : ∀ θ : ℝ, (poissonKernel 0 (w * exp (h * I)) • f) (circleMap 0 1 (θ + h)) =
      poissonKernel 0 w (circleMap 0 1 θ) • f (circleMap 0 1 θ * exp (h * I)) := by
    intro θ
    simp only [Pi.smul_apply', buj_circleMap_add, buj_poissonKernel_rot he]
  simp only [hrot] at hrep₁
  rw [Real.circleAverage_def] at hrep₀
  rw [hrep₁, hrep₀, ← smul_sub, ← intervalIntegral.integral_sub]
  rotate_left
  · exact (hcP.smul hcf').intervalIntegrable _ _
  · exact (hcP.smul hcf).intervalIntegrable _ _
  rw [Real.circleAverage_def, norm_smul]
  have h2π : ‖(2 * π)⁻¹‖ = (2 * π)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 Real.two_pi_pos)]
  rw [h2π, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 Real.two_pi_pos).le
  refine (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le).trans
    (le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_))
  have hP : 0 ≤ poissonKernel 0 w (circleMap 0 1 θ) :=
    buj_poissonKernel_nonneg hwn (by simp [circleMap_zero])
  show ‖poissonKernel 0 w (circleMap 0 1 θ) • f (circleMap 0 1 θ * exp (h * I)) -
      poissonKernel 0 w (circleMap 0 1 θ) • f (circleMap 0 1 θ)‖ =
    poissonKernel 0 w (circleMap 0 1 θ) * ‖f (circleMap 0 1 θ * exp (h * I)) - f (circleMap 0 1 θ)‖
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hP]

/-- `circleMap 0 r (t + h) = circleMap 0 r t * exp (h I)`. -/
theorem buj_circleMap_add_r (r t h : ℝ) :
    circleMap 0 r (t + h) = circleMap 0 r t * exp (h * I) := by
  simp only [circleMap_zero, Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]

/-- **LC at a fixed radius.** For a weight `W`, the `W`-weighted length of the level curve
`t ↦ f(r e^{it})` is at most the `liminf` over `h → 0⁺` of
`∫ W̃_r(θ) (V(θ + h) - V(θ))/h dθ`, where `W̃_r(θ) = ∫ W(t) P(re^{it}, e^{iθ}) dt / 2π` and `V`
dominates the boundary increments. -/
theorem buj_LC_r {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball 0 1)) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) {W : ℝ → ℝ≥0∞} (hW : Measurable W) (hWt : ∀ t, W t ≠ ⊤) {V : ℝ → ℝ}
    (hV : Monotone V)
    (hinc : ∀ θ h : ℝ, 0 ≤ h → ‖f (circleMap 0 1 (θ + h)) - f (circleMap 0 1 θ)‖ ≤ V (θ + h) - V θ) :
    ∫⁻ t in Ioc 0 (2 * π), W t * ‖deriv (fun s => f (circleMap 0 r s)) t‖ₑ ≤
      liminf (fun h : ℝ => ∫⁻ θ in Ioc 0 (2 * π),
        (∫⁻ t in Ioc 0 (2 * π), W t * ENNReal.ofReal ((2 * π)⁻¹ *
          poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ))) *
          ENNReal.ofReal ((V (θ + h) - V θ) / h)) (𝓝[>] 0) := by
  set F : ℝ → ℂ := fun s => f (circleMap 0 r s) with hFdef
  have hball : ∀ t : ℝ, circleMap 0 r t ∈ ball (0 : ℂ) 1 := fun t => by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hr1
  have hfd : ∀ t : ℝ, DifferentiableAt ℂ f (circleMap 0 r t) := fun t =>
    (hf.differentiableOn _ (hball t)).differentiableAt (isOpen_ball.mem_nhds (hball t))
  have hFd : ∀ t : ℝ, HasDerivAt F (deriv f (circleMap 0 r t) * (circleMap 0 r t * I)) t :=
    fun t => (hfd t).hasDerivAt.comp t (hasDerivAt_circleMap 0 r t)
  have hfc : ContinuousOn f (closedBall 0 1) := by
    have := hf.continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hFd t).continuousAt
  -- the difference quotients converge to the derivative
  set g : ℝ → ℝ → ℝ≥0∞ := fun h t => ENNReal.ofReal (‖F (t + h) - F t‖ / h) with hgdef
  have hlim : ∀ t, Tendsto (fun h => g h t) (𝓝[>] 0) (𝓝 ‖deriv F t‖ₑ) := by
    intro t
    have hs := (hasDerivAt_iff_tendsto_slope.1 (hFd t)).norm
    have hmap : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
        exact ne_of_gt hh
    have hc := hs.comp hmap
    rw [(hFd t).deriv, ← ofReal_norm]
    refine (ENNReal.tendsto_ofReal hc).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < h from hh), hgdef]
    rw [inv_mul_eq_div]
  -- Fatou
  have hgm : ∀ h : ℝ, Measurable fun t => W t * g h t := fun h =>
    hW.mul (ENNReal.measurable_ofReal.comp
      (((hFc.comp (continuous_id.add continuous_const)).sub hFc).norm.div_const h).measurable)
  have hstep1 : ∫⁻ t in Ioc 0 (2 * π), W t * ‖deriv F t‖ₑ ≤
      liminf (fun h => ∫⁻ t in Ioc 0 (2 * π), W t * g h t) (𝓝[>] 0) := by
    refine le_trans (le_of_eq ?_) (lintegral_liminf_le fun h => hgm h)
    refine lintegral_congr fun t => ?_
    exact ((ENNReal.Tendsto.const_mul (hlim t) (Or.inr (hWt t))).liminf_eq).symm
  refine hstep1.trans (liminf_le_liminf ?_)
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (0 : ℝ) < h := hh
  -- the kernel `A` and the boundary quotient `B`
  set A : ℝ → ℝ → ℝ := fun t θ => (2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ)
    with hAdef
  have hne : ∀ t θ : ℝ, circleMap 0 1 θ - circleMap 0 r t ≠ 0 := fun t θ h0 => by
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp [circleMap_zero]
    have h2 : ‖circleMap 0 r t‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
    rw [sub_eq_zero] at h0
    rw [h0, h2] at h1
    linarith
  have hPc : Continuous fun p : ℝ × ℝ =>
      poissonKernel 0 (circleMap 0 r p.1) (circleMap 0 1 p.2) := by
    simp only [poissonKernel, sub_zero]
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hne p.1 p.2))
  have hP0 : ∀ t θ, 0 ≤ poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) := fun t θ =>
    buj_poissonKernel_nonneg (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr1)
      (by simp [circleMap_zero])
  have hA0 : ∀ t θ, 0 ≤ A t θ := fun t θ =>
    mul_nonneg (inv_pos.2 Real.two_pi_pos).le (hP0 t θ)
  have hAc : Continuous fun p : ℝ × ℝ => A p.1 p.2 := continuous_const.mul hPc
  set B : ℝ → ℝ := fun θ => (V (θ + h) - V θ) / h with hBdef
  have hB0 : ∀ θ, 0 ≤ B θ := fun θ =>
    div_nonneg (sub_nonneg.2 (hV (by linarith))) hh0.le
  have hVs : Monotone fun θ : ℝ => V (θ + h) := hV.comp fun a b hab => by linarith
  have hBm : Measurable B := (hVs.measurable.sub hV.measurable).div_const h
  have hΔi : IntervalIntegrable (fun θ => V (θ + h) - V θ) volume 0 (2 * π) :=
    hVs.intervalIntegrable.sub hV.intervalIntegrable
  -- pointwise: LC1 and the increment bound
  have hpt : ∀ t, g h t ≤ ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (A t θ) * ENNReal.ofReal (B θ) := by
    intro t
    have h1 := buj_poisson_diff_le hf (hball t) h
    rw [← buj_circleMap_add_r, Real.circleAverage_def, smul_eq_mul] at h1
    have hPt : Continuous fun θ => poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) := by
      simp only [poissonKernel, sub_zero]
      refine Continuous.div (by fun_prop) (by fun_prop) fun θ => ?_
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hne t θ))
    have hAt : Continuous fun θ => A t θ := continuous_const.mul hPt
    have hfb : Continuous fun θ => ‖f (circleMap 0 1 θ * exp (h * I)) - f (circleMap 0 1 θ)‖ := by
      have hsph : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := fun θ =>
        sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
      have hsph' : ∀ θ : ℝ, circleMap 0 1 θ * exp (h * I) ∈ closedBall (0 : ℂ) 1 := fun θ => by
        rw [← buj_circleMap_add]; exact hsph _
      exact ((hfc.comp_continuous ((continuous_circleMap 0 1).mul continuous_const) hsph').sub
        (hfc.comp_continuous (continuous_circleMap 0 1) hsph)).norm
    have h2 : ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) *
          ‖f (circleMap 0 1 θ * exp (h * I)) - f (circleMap 0 1 θ)‖ ≤
        ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) *
          (V (θ + h) - V θ) := by
      refine intervalIntegral.integral_mono_on Real.two_pi_pos.le
        ((hPt.mul hfb).intervalIntegrable _ _) (hΔi.continuousOn_mul hPt.continuousOn)
        fun θ _ => mul_le_mul_of_nonneg_left ?_ (hP0 t θ)
      rw [← buj_circleMap_add]
      exact hinc θ h hh0.le
    have h3 : ‖F (t + h) - F t‖ / h ≤ ∫ θ in (0 : ℝ)..2 * π, A t θ * B θ := by
      have heq : ∫ θ in (0 : ℝ)..2 * π, A t θ * B θ = (2 * π)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) *
            (V (θ + h) - V θ)) / h := by
        rw [mul_div_assoc, ← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [hAdef, hBdef]
        ring
      rw [heq, div_le_div_iff_of_pos_right hh0]
      calc ‖F (t + h) - F t‖ ≤ _ := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (inv_pos.2 Real.two_pi_pos).le
    have hABi : IntegrableOn (fun θ => A t θ * B θ) (Ioc 0 (2 * π)) := by
      have := (hΔi.div_const h).continuousOn_mul hAt.continuousOn
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).1 this
    calc g h t = ENNReal.ofReal (‖F (t + h) - F t‖ / h) := rfl
      _ ≤ ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, A t θ * B θ) := ENNReal.ofReal_le_ofReal h3
      _ = ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (A t θ * B θ) := by
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
        exact ofReal_integral_eq_lintegral_ofReal hABi
          (Eventually.of_forall fun θ => mul_nonneg (hA0 t θ) (hB0 θ))
      _ = _ := lintegral_congr fun θ => ENNReal.ofReal_mul (hA0 t θ)
  -- Tonelli
  have hmeasAB : Measurable fun p : ℝ × ℝ =>
      W p.1 * (ENNReal.ofReal (A p.1 p.2) * ENNReal.ofReal (B p.2)) :=
    (hW.comp measurable_fst).mul ((ENNReal.measurable_ofReal.comp hAc.measurable).mul
      (ENNReal.measurable_ofReal.comp (hBm.comp measurable_snd)))
  calc ∫⁻ t in Ioc 0 (2 * π), W t * g h t
      ≤ ∫⁻ t in Ioc 0 (2 * π), W t * ∫⁻ θ in Ioc 0 (2 * π),
          ENNReal.ofReal (A t θ) * ENNReal.ofReal (B θ) :=
        lintegral_mono fun t => mul_le_mul_right (hpt t) _
    _ = ∫⁻ t in Ioc 0 (2 * π), ∫⁻ θ in Ioc 0 (2 * π),
          W t * (ENNReal.ofReal (A t θ) * ENNReal.ofReal (B θ)) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ (hWt t)]
    _ = ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
          W t * (ENNReal.ofReal (A t θ) * ENNReal.ofReal (B θ)) :=
        lintegral_lintegral_swap hmeasAB.aemeasurable
    _ = ∫⁻ θ in Ioc 0 (2 * π), (∫⁻ t in Ioc 0 (2 * π), W t * ENNReal.ofReal (A t θ)) *
          ENNReal.ofReal (B θ) := by
        refine lintegral_congr fun θ => ?_
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun t => by ring

/-! ## The harmonic-measure lower bound -/

/-- `Im (z ^ β) = exp (β log ‖z‖) sin (β arg z)` for `z ≠ 0` and real `β`. -/
theorem buj_im_cpow {z : ℂ} (hz : z ≠ 0) (β : ℝ) :
    (z ^ (β : ℂ)).im = Real.exp (β * Real.log ‖z‖) * Real.sin (β * arg z) := by
  rw [cpow_def_of_ne_zero hz, exp_im]
  congr 2
  · simp [Complex.mul_re, log_re, log_im]; ring
  · simp [Complex.mul_im, log_re, log_im]; ring

/-- `Im (z^{π/α}) ≤ 1` for `‖z‖ ≤ 1` (`α > 0`). -/
theorem buj_im_cpow_le_one {α : ℝ} (hα0 : 0 < α) {z : ℂ} (hz1 : ‖z‖ ≤ 1) :
    (z ^ ((π / α : ℝ) : ℂ)).im ≤ 1 := by
  by_cases hz : z = 0
  · subst hz
    have hβ : ((π / α : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos Real.pi_pos hα0).ne'
    rw [zero_cpow hβ]
    simp
  rw [buj_im_cpow hz]
  have hexp : Real.exp (π / α * Real.log ‖z‖) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (div_pos Real.pi_pos hα0).le (Real.log_nonpos (norm_nonneg z) hz1)
  calc Real.exp (π / α * Real.log ‖z‖) * Real.sin (π / α * arg z)
      ≤ Real.exp (π / α * Real.log ‖z‖) * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one _) (Real.exp_pos _).le
    _ ≤ 1 := by rw [mul_one]; exact hexp

/-- `Im (z^{π/α}) = 0` on the two sides `arg z ∈ {0, α}` of the closed sector (and at `0`). -/
theorem buj_im_cpow_eq_zero {α : ℝ} (hα0 : 0 < α) {z : ℂ} (harg0 : 0 ≤ arg z) (hargα : arg z ≤ α)
    (hn : ¬ (z ≠ 0 ∧ 0 < arg z ∧ arg z < α)) : (z ^ ((π / α : ℝ) : ℂ)).im = 0 := by
  by_cases hz : z = 0
  · subst hz
    have hβ : ((π / α : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos Real.pi_pos hα0).ne'
    rw [zero_cpow hβ]
    simp
  rw [buj_im_cpow hz]
  have hcase : arg z = 0 ∨ arg z = α := by
    push Not at hn
    rcases harg0.eq_or_lt with h0 | h0
    · exact Or.inl h0.symm
    · exact Or.inr (le_antisymm hargα (hn hz h0))
  rcases hcase with h | h
  · simp [h]
  · rw [h, div_mul_cancel₀ π hα0.ne', Real.sin_pi, mul_zero]

/-- **(H) Harmonic-measure lower bound.** Setting:
* `ρ` is holomorphic in `Δ` and continuous on `Δ̄`;
* `ρ` sends `Δ` into the open sector `{0 < arg < α}` (`α < π`) and `∂Δ` into the closed unit sector.

Claim: the set of boundary angles mapped into the open sector has measure `≥ 2π Im (ρ(0)^{π/α})`. This is the
mean-value property of the harmonic `Im (ρ^{π/α})`, which vanishes on the two sides and is `≤ 1`. -/
theorem buj_harmonic_measure_lb {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {ρ : ℂ → ℂ}
    (hρ : DiffContOnCl ℂ ρ (ball 0 1))
    (hin : ∀ z ∈ ball (0 : ℂ) 1, ρ z ≠ 0 ∧ 0 < arg (ρ z) ∧ arg (ρ z) < α)
    (hcl : ∀ z ∈ sphere (0 : ℂ) 1, ‖ρ z‖ ≤ 1 ∧ 0 ≤ arg (ρ z) ∧ arg (ρ z) ≤ α) :
    ((ρ 0) ^ ((π / α : ℝ) : ℂ)).im ≤ (2 * π)⁻¹ * (volume (Ioc (0 : ℝ) (2 * π) ∩
      {θ | ρ (circleMap 0 1 θ) ≠ 0 ∧ 0 < arg (ρ (circleMap 0 1 θ)) ∧
        arg (ρ (circleMap 0 1 θ)) < α})).toReal := by
  set β : ℂ := ((π / α : ℝ) : ℂ) with hβ
  have hβre : 0 < β.re := by rw [hβ, ofReal_re]; exact div_pos Real.pi_pos hα0
  set g : ℂ → ℂ := fun z => ρ z ^ β with hg
  have hslit : ∀ z ∈ ball (0 : ℂ) 1, ρ z ∈ slitPlane := fun z hz => by
    obtain ⟨h0, h1, h2⟩ := hin z hz
    exact mem_slitPlane_iff_arg.2 ⟨fun h => by linarith, h0⟩
  have hρc : ContinuousOn ρ (closedBall 0 1) := by
    have := hρ.continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hgc : DiffContOnCl ℂ g (ball 0 |(1 : ℝ)|) := by
    rw [abs_one]
    refine ⟨fun z hz => (hρ.differentiableOn z hz).differentiableAt
      (isOpen_ball.mem_nhds hz) |>.cpow_const (hslit z hz) |>.differentiableWithinAt, ?_⟩
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro z hz
    have hcpow : ContinuousAt (fun u : ℂ => u ^ β) (ρ z) := by
      by_cases h0 : ρ z = 0
      · rw [h0]
        exact (continuousAt_cpow_zero_of_re_pos hβre).comp_of_eq
          ((continuous_id.prodMk continuous_const).continuousAt) rfl
      · refine continuousAt_cpow_const (mem_slitPlane_iff_arg.2 ⟨?_, h0⟩)
        rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with h | h
        · have := (hin z (mem_ball_zero_iff.2 h)).2.2; intro hπ; linarith
        · have := (hcl z (mem_sphere_zero_iff_norm.2 h)).2.2; intro hπ; linarith
    exact hcpow.comp_continuousWithinAt (hρc z hz)
  have hmv := hgc.circleAverage
  have hgcont : Continuous fun θ : ℝ => g (circleMap 0 1 θ) := by
    have hc := hgc.continuousOn
    rw [abs_one, closure_ball (0 : ℂ) one_ne_zero] at hc
    exact hc.comp_continuous (continuous_circleMap 0 1)
      fun θ => sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  have hci : CircleIntegrable g 0 1 := (hgcont.intervalIntegrable _ _)
  have him : (ρ 0 ^ β).im = Real.circleAverage (fun z => (g z).im) 0 1 := by
    have := (Complex.imCLM.circleAverage_comp_comm hci)
    rw [hmv] at this
    exact this.symm
  rw [him, Real.circleAverage_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 Real.two_pi_pos).le
  set E : Set ℝ := {θ | ρ (circleMap 0 1 θ) ≠ 0 ∧ 0 < arg (ρ (circleMap 0 1 θ)) ∧
    arg (ρ (circleMap 0 1 θ)) < α} with hE
  have hρcirc : Continuous fun θ : ℝ => ρ (circleMap 0 1 θ) :=
    hρc.comp_continuous (continuous_circleMap 0 1)
      fun θ => sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  have hEm : MeasurableSet E := by
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact (measurableSet_singleton (0 : ℂ)).compl.preimage hρcirc.measurable
    · exact measurableSet_lt measurable_const (measurable_arg.comp hρcirc.measurable)
    · exact measurableSet_lt (measurable_arg.comp hρcirc.measurable) measurable_const
  have hpt : ∀ θ : ℝ, (g (circleMap 0 1 θ)).im ≤ E.indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    have hmem : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one θ
    obtain ⟨h1, h2, h3⟩ := hcl _ hmem
    by_cases hθ : ρ (circleMap 0 1 θ) ≠ 0 ∧ 0 < arg (ρ (circleMap 0 1 θ)) ∧
        arg (ρ (circleMap 0 1 θ)) < α
    · rw [indicator_of_mem (show θ ∈ E from hθ)]
      exact buj_im_cpow_le_one hα0 h1
    · rw [indicator_of_notMem (show θ ∉ E from hθ)]
      exact (buj_im_cpow_eq_zero hα0 h2 h3 hθ).le
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc ∫ θ in Ioc 0 (2 * π), (g (circleMap 0 1 θ)).im
      ≤ ∫ θ in Ioc 0 (2 * π), E.indicator (fun _ => (1 : ℝ)) θ := by
        refine integral_mono ?_ ?_ hpt
        · exact (continuous_im.comp hgcont).integrableOn_Ioc
        · exact (continuous_const.integrableOn_Ioc (a := (0 : ℝ)) (b := 2 * π)).indicator hEm
    _ = (volume (Ioc (0 : ℝ) (2 * π) ∩ E)).toReal := by
        rw [integral_indicator_const _ hEm, smul_eq_mul, mul_one, Measure.real,
          Measure.restrict_apply hEm, inter_comm]

/-- **The closing step.** With a fixed left side `K`, a fixed `m > 0`, a fixed `M`, and `ℓₙ → 0⁺`, the inequalities
`K ≤ 2m log(ℓₙ/m) + 2M` are contradictory. -/
theorem buj_close {K m M : ℝ} (hm : 0 < m) {ℓ : ℕ → ℝ} (hℓ0 : ∀ n, 0 < ℓ n)
    (hℓ : Tendsto ℓ atTop (𝓝 0))
    (hJL : ∀ n, K ≤ 2 * m * Real.log (ℓ n / m) + 2 * M) : False := by
  have hdiv : Tendsto (fun n => ℓ n / m) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => div_pos (hℓ0 n) hm⟩
    simpa using hℓ.div_const m
  have hlog : Tendsto (fun n => Real.log (ℓ n / m)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hdiv
  have hrhs : Tendsto (fun n => 2 * m * Real.log (ℓ n / m) + 2 * M) atTop atBot :=
    tendsto_atBot_add_const_right _ _ (hlog.const_mul_atBot (by linarith))
  obtain ⟨n, hn⟩ := (hrhs.eventually (eventually_lt_atBot K)).exists
  linarith [hJL n]

/-! ## Sector cuts: the Jordan domains of the BU-Jensen argument -/

/-- The open sector `{z | 0 < arg (z / ξ) < α}` with vertex `0`, whose first side is the ray through `ξ` (in use `ξ` is
a unit vector and `0 < α < π`). -/
def buj_openSector (ξ : ℂ) (α : ℝ) : Set ℂ :=
  {z | z / ξ ≠ 0 ∧ 0 < arg (z / ξ) ∧ arg (z / ξ) < α}

/-- The closed curve `[0, aξ] ∪ τ([s, t]) ∪ [0, bξe^{iα}]`: a sector cut `τ` closed up by the two sides of the
sector. -/
def buj_cutCurve (ξ : ℂ) (α a b : ℝ) (τ : ℝ → ℂ) (s t : ℝ) : Set ℂ :=
  segment ℝ 0 ((a : ℂ) * ξ) ∪ τ '' Icc s t ∪ segment ℝ 0 ((b : ℂ) * (ξ * exp (α * I)))

/-- `τ|[s, t]` is a **sector cut at height `r₀`**:
* `0 < α < π`, `‖ξ‖ = 1`, `0 < r₀`, `0 < a`, `0 < b` and `s < t`;
* `τ` is an arc (continuous and injective on `[s, t]`) from `aξ` on the first side to `bξe^{iα}` on the second
  side, with its interior in the open sector;
* `r₀ < ‖τ‖ < 1` on `[s, t]`;
* `τ` is differentiable on `(s, t)` with integrable derivative (so it is absolutely continuous and rectifiable). -/
def buj_IsSectorCut (ξ : ℂ) (α a b r₀ : ℝ) (τ : ℝ → ℂ) (s t : ℝ) : Prop :=
  (0 < α ∧ α < π ∧ ‖ξ‖ = 1 ∧ 0 < r₀ ∧ 0 < a ∧ 0 < b ∧ s < t) ∧
    (ContinuousOn τ (Icc s t) ∧ InjOn τ (Icc s t) ∧ τ s = (a : ℂ) * ξ ∧
      τ t = (b : ℂ) * (ξ * exp (α * I))) ∧
    (∀ u ∈ Ioo s t, τ u ∈ buj_openSector ξ α) ∧ (∀ u ∈ Icc s t, r₀ < ‖τ u‖ ∧ ‖τ u‖ < 1) ∧
    (∀ u ∈ Ioo s t, DifferentiableAt ℝ τ u) ∧ IntervalIntegrable (deriv τ) volume s t

/-! ## LC, Jensen–length, the sector uniformizer and its boundary measure -/

/-- The distance between `r e^{it}` and `e^{it}` is `|r - 1|`. -/
theorem buj_a_dist_circleMap (r t : ℝ) : dist (circleMap 0 r t) (circleMap 0 1 t) = |r - 1| := by
  rw [dist_eq_norm, circleMap_zero, circleMap_zero, ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The Poisson kernel of the unit circle is symmetric in the two angles:
`P(r e^{it}, e^{iθ}) = P(r e^{iθ}, e^{it})`. -/
theorem buj_a_poissonKernel_symm (r t θ : ℝ) :
    poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) =
      poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) := by
  simp only [poissonKernel, sub_zero, norm_circleMap_zero]
  congr 1
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, circleMap_zero_re, circleMap_zero_im, one_mul]
  linear_combination (1 - r ^ 2) * Real.sin_sq_add_cos_sq θ - (1 - r ^ 2) * Real.sin_sq_add_cos_sq t

/-- A continuous `2π`-periodic function descends to a continuous function on `Real.Angle`. -/
theorem buj_a_continuous_lift {W : ℝ → ℝ} (hW : Continuous W) (hWp : Function.Periodic W (2 * π)) :
    Continuous (fun θ : Real.Angle => hWp.lift θ) := by
  exact hW.quotient_liftOn' _

/-- **The Poisson smoothing of a continuous periodic weight is eventually at most the weight plus `ε`**,
uniformly in the angle: `W̃_r(θ) = ∫ W(t) P(re^{it}, e^{iθ}) dt / 2π ≤ W(θ) + ε` for `r` close to `1`. Here
`W̃_r(θ)` is the value at `re^{iθ}` of the harmonic extension `u` of `W` (`PoissonExtension`), and `u` is uniformly
continuous on `Δ̄`. -/
theorem buj_a_poisson_smooth_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : ∀ θ, 0 ≤ W θ)
    (hWp : Function.Periodic W (2 * π)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 ∧ ∀ θ : ℝ,
      (∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) *
        ENNReal.ofReal ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ))) ≤
          ENNReal.ofReal (W θ + ε) := by
  -- the boundary datum `W ∘ arg` on the unit circle
  set g : ℂ → ℝ := fun z => hWp.lift (arg z : Real.Angle) with hgdef
  have hgc : ContinuousOn g (sphere 0 1) := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
      exact zero_ne_one hz
    exact ((buj_a_continuous_lift hW hWp).continuousAt.comp
      (continuousAt_arg_coe_angle hz0)).continuousWithinAt
  obtain ⟨u, hu, huc, hug⟩ := exists_harmonicOnNhd_continuousOn_closedBall_eqOn_sphere (c := 0) one_pos hgc
  have huW : ∀ θ : ℝ, u (circleMap 0 1 θ) = W θ := fun θ => by
    rw [hug (circleMap_mem_sphere 0 zero_le_one θ)]
    show hWp.lift (arg (circleMap 0 1 θ) : Real.Angle) = W θ
    rw [circleMap_zero, Complex.ofReal_one, one_mul, arg_exp_mul_I, Real.Angle.coe_toIocMod]
    rfl
  have hUC := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous huc
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
  filter_upwards [Ioo_mem_nhdsLT (show max 0 (1 - δ) < 1 from max_lt one_pos (by linarith))] with r hr
  have hr0 : 0 < r := (le_max_left _ _).trans_lt hr.1
  have hrδ : 1 - δ < r := (le_max_right _ _).trans_lt hr.1
  have hr1 : r < 1 := hr.2
  refine ⟨hr0, hr1, fun θ => ?_⟩
  have hw : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hr1
  have hHC : InnerProductSpace.HarmonicContOnCl u (ball 0 1) :=
    InnerProductSpace.HarmonicContOnCl.mk_ball hu huc
  have hrep := hHC.circleAverage_poissonKernel_smul hw
  have hne : ∀ t : ℝ, circleMap 0 1 θ - circleMap 0 r t ≠ 0 := fun t h0 => by
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp [circleMap_zero]
    have h2 : ‖circleMap 0 r t‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
    rw [sub_eq_zero] at h0
    rw [h0, h2] at h1
    linarith
  have hPc : Continuous fun t : ℝ => poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) := by
    simp only [poissonKernel, sub_zero]
    refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hne t))
  have hP0 : ∀ t : ℝ, 0 ≤ poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ) := fun t =>
    buj_poissonKernel_nonneg (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr1)
      (by simp [circleMap_zero])
  have hint : Integrable (fun t => W t * ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ)))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (hW.mul (continuous_const.mul hPc)).integrableOn_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))]
      fun t => W t * ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ)) :=
    ae_of_all _ fun t => mul_nonneg (hW0 t) (mul_nonneg (inv_pos.2 Real.two_pi_pos).le (hP0 t))
  have heq : ∫ t in Ioc 0 (2 * π), W t * ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ)) =
      u (circleMap 0 r θ) := by
    rw [← hrep, Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Pi.smul_apply', smul_eq_mul, huW, buj_a_poissonKernel_symm r t θ]
    ring
  have hclose : u (circleMap 0 r θ) ≤ W θ + ε := by
    have hd : dist (circleMap 0 r θ) (circleMap 0 1 θ) < δ := by
      rw [buj_a_dist_circleMap, abs_of_neg (by linarith)]; linarith
    have h1 := hδu _ (ball_subset_closedBall hw) _
      (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)) hd
    rw [Real.dist_eq, huW] at h1
    linarith [(abs_lt.1 h1).2]
  calc (∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) *
        ENNReal.ofReal ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ)))
      = ∫⁻ t in Ioc 0 (2 * π),
          ENNReal.ofReal (W t * ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ))) :=
        lintegral_congr fun t => (ENNReal.ofReal_mul (hW0 t)).symm
    _ = ENNReal.ofReal (u (circleMap 0 r θ)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, heq]
    _ ≤ ENNReal.ofReal (W θ + ε) := ENNReal.ofReal_le_ofReal hclose

/-- **One Stieltjes step (Tonelli).** If `F θ ≤ G v` whenever `θ ∈ (0, 2π]` and `v ∈ (θ, θ + h]`, then the
difference quotients `(V(θ + h) - V θ)/h` integrated against `F` over `(0, 2π]` are at most `∫_{(0, 2π + h]} G dV`. -/
theorem buj_a_stieltjes_step (V : StieltjesFunction ℝ) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) {h : ℝ}
    (hh : 0 < h) (hFG : ∀ θ ∈ Ioc 0 (2 * π), ∀ v ∈ Ioc θ (θ + h), F θ ≤ G v) :
    ∫⁻ θ in Ioc 0 (2 * π), F θ * ENNReal.ofReal ((V (θ + h) - V θ) / h) ≤
      ∫⁻ v in Ioc 0 (2 * π + h), G v ∂V.measure := by
  set S : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 ≤ p.1 + h} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const h))
  have hind : ∀ θ v : ℝ, (Ioc θ (θ + h)).indicator (1 : ℝ → ℝ≥0∞) v = S.indicator 1 (θ, v) := by
    intro θ v
    by_cases hv : θ < v ∧ v ≤ θ + h
    · rw [indicator_of_mem (show v ∈ Ioc θ (θ + h) from hv), indicator_of_mem (show (θ, v) ∈ S from hv)]
      rfl
    · rw [indicator_of_notMem (show v ∉ Ioc θ (θ + h) from hv),
        indicator_of_notMem (show (θ, v) ∉ S from hv)]
  have h1 : ∀ θ, F θ * ENNReal.ofReal ((V (θ + h) - V θ) / h) =
      ENNReal.ofReal h⁻¹ * ∫⁻ v, F θ * S.indicator 1 (θ, v) ∂V.measure := by
    intro θ
    have hθh : V θ ≤ V (θ + h) := V.mono (by linarith)
    simp_rw [← hind]
    rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Ioc),
      lintegral_indicator_one measurableSet_Ioc, StieltjesFunction.measure_Ioc, div_eq_mul_inv,
      ENNReal.ofReal_mul (sub_nonneg.2 hθh)]
    ring
  have hmeas : Measurable (Function.uncurry fun θ v : ℝ => F θ * S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (θ, v)) :=
    (hF.comp measurable_fst).mul (measurable_one.indicator hS)
  have hpt : ∀ v : ℝ, ∫⁻ θ in Ioc 0 (2 * π), F θ * S.indicator 1 (θ, v) ≤
      (Ioc 0 (2 * π + h)).indicator G v * ENNReal.ofReal h := by
    intro v
    calc ∫⁻ θ in Ioc 0 (2 * π), F θ * S.indicator 1 (θ, v)
        ≤ ∫⁻ θ in Ioc 0 (2 * π), (Ioc 0 (2 * π + h)).indicator G v * (Ico (v - h) v).indicator 1 θ := by
          refine setLIntegral_mono' measurableSet_Ioc fun θ hθ => ?_
          by_cases hθv : (θ, v) ∈ S
          · have hv : v ∈ Ioc 0 (2 * π + h) := ⟨hθ.1.trans hθv.1, by linarith [hθ.2, hθv.2]⟩
            have hθ' : θ ∈ Ico (v - h) v := ⟨by linarith [hθv.2], hθv.1⟩
            rw [indicator_of_mem hθv, indicator_of_mem hv, indicator_of_mem hθ']
            simp only [Pi.one_apply, mul_one]
            exact hFG θ hθ v hθv
          · rw [indicator_of_notMem hθv]
            simp
      _ = (Ioc 0 (2 * π + h)).indicator G v * volume (Ico (v - h) v ∩ Ioc 0 (2 * π)) := by
          rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Ico),
            lintegral_indicator_one measurableSet_Ico, Measure.restrict_apply measurableSet_Ico]
      _ ≤ (Ioc 0 (2 * π + h)).indicator G v * ENNReal.ofReal h := by
          gcongr
          calc volume (Ico (v - h) v ∩ Ioc 0 (2 * π)) ≤ volume (Ico (v - h) v) :=
                measure_mono inter_subset_left
            _ = ENNReal.ofReal h := by rw [Real.volume_Ico, sub_sub_cancel]
  calc ∫⁻ θ in Ioc 0 (2 * π), F θ * ENNReal.ofReal ((V (θ + h) - V θ) / h)
      = ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal h⁻¹ * ∫⁻ v, F θ * S.indicator 1 (θ, v) ∂V.measure :=
        lintegral_congr fun θ => h1 θ
    _ = ENNReal.ofReal h⁻¹ * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, F θ * S.indicator 1 (θ, v) ∂V.measure :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal h⁻¹ * ∫⁻ v, (∫⁻ θ in Ioc 0 (2 * π), F θ * S.indicator 1 (θ, v)) ∂V.measure := by
        congr 1
        exact lintegral_lintegral_swap (μ := volume.restrict (Ioc 0 (2 * π))) (ν := V.measure)
          hmeas.aemeasurable
    _ ≤ ENNReal.ofReal h⁻¹ * ∫⁻ v, (Ioc 0 (2 * π + h)).indicator G v * ENNReal.ofReal h ∂V.measure := by
        exact mul_le_mul_of_nonneg_left (lintegral_mono fun v => hpt v) (zero_le)
    _ = ∫⁻ v in Ioc 0 (2 * π + h), G v ∂V.measure := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioc, mul_comm,
          mul_assoc, ← ENNReal.ofReal_mul hh.le, mul_inv_cancel₀ hh.ne', ENNReal.ofReal_one, mul_one]

/-- The right tail of a Stieltjes function at `2π`: `V(2π + h) - V(2π) → 0` as `h → 0⁺`. -/
theorem buj_a_tendsto_tail (V : StieltjesFunction ℝ) :
    Tendsto (fun h : ℝ => ENNReal.ofReal (V (2 * π + h) - V (2 * π))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun h : ℝ => 2 * π + h) (𝓝[>] 0) (𝓝[≥] (2 * π)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun h : ℝ => 2 * π + h) (𝓝 0) (𝓝 (2 * π + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact le_add_of_nonneg_right (Set.mem_Ioi.1 hh).le
  have h2 := ((V.right_continuous (2 * π)).tendsto.comp h1).sub_const (V (2 * π))
  rw [sub_self] at h2
  have h3 := ENNReal.tendsto_ofReal h2
  rw [ENNReal.ofReal_zero] at h3
  exact h3

/-- **LC: the level curves of a Riemann map are asymptotically no longer, weighted, than its rectifiable
boundary.**

Setting:
* `ρ` is holomorphic in `Δ` and continuous on `Δ̄`;
* `W ≥ 0` is a continuous, `2π`-periodic weight;
* `V` is a Stieltjes function with `2π`-periodic increments that dominates the increments of the boundary map
  `θ ↦ ρ(e^{iθ})`.

Claim: the `W`-weighted lengths of the level curves `t ↦ ρ(re^{it})` have `limsup_{r → 1⁻}` at most `∫ W dV`.

*Truth:* TRUE (this is the easy half of the F. and M. Riesz theorem; no absolute continuity of the boundary map is
needed).

*Route:*
1. `buj_LC_r` bounds the level-curve integral at each `r` by `liminf_{h → 0⁺} ∫ W̃_r(θ) (V(θ + h) - V θ)/h dθ`, where
   `W̃_r(θ) = ∫ W(t) P(re^{it}, e^{iθ}) dt / 2π`.
2. By Tonelli, `(1/h) ∫ W̃_r(θ) μ_V (θ, θ + h] dθ = ∫ ((1/h) ∫_{v-h}^{v} W̃_r) dμ_V(v)`, using the `2π`-invariance of
   `μ_V`. This tends to `∫ W̃_r dV` by dominated convergence.
3. `W̃_r → W` uniformly as `r → 1⁻`. By `HarmonicContOnCl.circleAverage_poissonKernel_smul`, `W̃_r(θ)` is the value
   at `re^{iθ}` of the harmonic extension of `W` from
   `Lemmas/PoissonExtension.exists_harmonicOnNhd_continuousOn_closedBall_eqOn_sphere`, which is uniformly continuous
   on `Δ̄`.
4. `V.measure (Ioc 0 (2π)) < ∞`. -/
theorem buj_LC (ρ : ℂ → ℂ) (V : StieltjesFunction ℝ) (W : ℝ → ℝ) (hρ : DiffContOnCl ℂ ρ (ball 0 1))
    (hW : Continuous W) (hW0 : ∀ θ, 0 ≤ W θ) (hWp : Function.Periodic W (2 * π))
    (hinc : ∀ θ h : ℝ, 0 ≤ h → ‖ρ (circleMap 0 1 (θ + h)) - ρ (circleMap 0 1 θ)‖ ≤ V (θ + h) - V θ)
    (hper : ∀ θ : ℝ, V (θ + 2 * π) = V θ + (V (2 * π) - V 0)) :
    limsup (fun r : ℝ => ∫⁻ t in Ioc 0 (2 * π),
        ENNReal.ofReal (W t) * ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ₑ) (𝓝[<] 1) ≤
      ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure := by
  have _ := hper
  set L : ℝ := V (2 * π) - V 0 with hLdef
  have hL : 0 ≤ L := sub_nonneg.2 (V.mono Real.two_pi_pos.le)
  have hμ : V.measure (Ioc 0 (2 * π)) = ENNReal.ofReal L := V.measure_Ioc 0 (2 * π)
  -- a bound and uniform continuity for `W` on `[0, 2π + 1]`
  obtain ⟨C, hC⟩ : ∃ C, ∀ v ∈ Icc (0 : ℝ) (2 * π + 1), W v ≤ C :=
    (isCompact_Icc.bddAbove_image hW.continuousOn).imp fun C hC v hv => hC (mem_image_of_mem W hv)
  have hUC := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π + 1)).uniformContinuousOn_of_continuous hW.continuousOn
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
  set ε : ℝ := ε' / (2 * (L + 1)) with hεdef
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  have hε : 0 < ε := div_pos (by exact_mod_cast hε') (by linarith)
  have hεL : ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) ≤ ε' := by
    rw [hμ, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2ε : 2 * ε * (L + 1) = (ε' : ℝ) := by
      rw [hεdef]
      field_simp
    nlinarith
  obtain ⟨δ₁, hδ₁, hδu⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [buj_a_poisson_smooth_le hW hW0 hWp hε] with r hr
  obtain ⟨hr0, hr1, hsm⟩ := hr
  refine (buj_LC_r hρ hr0 hr1 (W := fun t => ENNReal.ofReal (W t)) (ENNReal.measurable_ofReal.comp hW.measurable)
    (fun _ => ENNReal.ofReal_ne_top) V.mono hinc).trans ?_
  -- the first piece of the Stieltjes bound
  have hfirst : ∫⁻ v in Ioc 0 (2 * π), ENNReal.ofReal (W v + 2 * ε) ∂V.measure =
      (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
        ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) := by
    calc ∫⁻ v in Ioc 0 (2 * π), ENNReal.ofReal (W v + 2 * ε) ∂V.measure
        = ∫⁻ v in Ioc 0 (2 * π), (ENNReal.ofReal (W v) + ENNReal.ofReal (2 * ε)) ∂V.measure :=
          lintegral_congr fun v => ENNReal.ofReal_add (hW0 v) (by linarith)
      _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  -- the tail
  have htail : Tendsto (fun h : ℝ => (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
      ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) +
        ENNReal.ofReal (C + 2 * ε) * ENNReal.ofReal (V (2 * π + h) - V (2 * π))) (𝓝[>] 0)
      (𝓝 ((∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
        ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)))) := by
    have h3 := ENNReal.Tendsto.const_mul (buj_a_tendsto_tail V) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (C + 2 * ε))
    rw [mul_zero] at h3
    have h4 := (tendsto_const_nhds (x := (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
      ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)))).add h3
    rw [add_zero] at h4
    exact h4
  calc liminf (fun h : ℝ => ∫⁻ θ in Ioc 0 (2 * π), (∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) *
          ENNReal.ofReal ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ))) *
            ENNReal.ofReal ((V (θ + h) - V θ) / h)) (𝓝[>] 0)
      ≤ liminf (fun h : ℝ => (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
          ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) +
            ENNReal.ofReal (C + 2 * ε) * ENNReal.ofReal (V (2 * π + h) - V (2 * π))) (𝓝[>] 0) := by
        refine liminf_le_liminf ?_
        filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁ one_pos)] with h hh
        have hh0 : 0 < h := hh.1
        have hhδ : h < δ₁ := hh.2.trans_le (min_le_left _ _)
        have hh1 : h < 1 := hh.2.trans_le (min_le_right _ _)
        calc ∫⁻ θ in Ioc 0 (2 * π), (∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) *
              ENNReal.ofReal ((2 * π)⁻¹ * poissonKernel 0 (circleMap 0 r t) (circleMap 0 1 θ))) *
                ENNReal.ofReal ((V (θ + h) - V θ) / h)
            ≤ ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ + ε) * ENNReal.ofReal ((V (θ + h) - V θ) / h) :=
              lintegral_mono fun θ => by gcongr; exact hsm θ
          _ ≤ ∫⁻ v in Ioc 0 (2 * π + h), ENNReal.ofReal (W v + 2 * ε) ∂V.measure := by
              refine buj_a_stieltjes_step V (ENNReal.measurable_ofReal.comp (hW.measurable.add_const ε)) hh0 ?_
              intro θ hθ v hv
              refine ENNReal.ofReal_le_ofReal ?_
              have hθI : θ ∈ Icc (0 : ℝ) (2 * π + 1) := ⟨hθ.1.le, by linarith [hθ.2]⟩
              have hvI : v ∈ Icc (0 : ℝ) (2 * π + 1) := ⟨by linarith [hθ.1, hv.1], by linarith [hθ.2, hv.2]⟩
              have hd : dist θ v < δ₁ := by
                rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hv.1])]
                linarith [hv.2]
              have h1 := hδu θ hθI v hvI hd
              rw [Real.dist_eq] at h1
              linarith [(abs_lt.1 h1).2]
          _ ≤ ∫⁻ v in Ioc 0 (2 * π), ENNReal.ofReal (W v + 2 * ε) ∂V.measure +
                ∫⁻ v in Ioc (2 * π) (2 * π + h), ENNReal.ofReal (W v + 2 * ε) ∂V.measure := by
              rw [← Ioc_union_Ioc_eq_Ioc Real.two_pi_pos.le (by linarith)]
              exact lintegral_union_le _ _ _
          _ ≤ (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
                ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) +
                  ENNReal.ofReal (C + 2 * ε) * ENNReal.ofReal (V (2 * π + h) - V (2 * π)) := by
              rw [hfirst]
              gcongr
              rw [← V.measure_Ioc, ← setLIntegral_const]
              refine setLIntegral_mono measurable_const fun v hv => ENNReal.ofReal_le_ofReal ?_
              have := hC v ⟨by linarith [hv.1, Real.two_pi_pos], by linarith [hv.2]⟩
              linarith
    _ = (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) +
          ENNReal.ofReal (2 * ε) * V.measure (Ioc 0 (2 * π)) := htail.liminf_eq
    _ ≤ (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W θ) ∂V.measure) + ε' := by gcongr

/-- `cos ψ ≤ cos H` for `H ≤ ψ ≤ 2π - H` (and `0 ≤ H`). -/
theorem buj_a_cos_le {H ψ : ℝ} (hH : 0 ≤ H) (hψ1 : H ≤ ψ) (hψ2 : ψ ≤ 2 * π - H) :
    Real.cos ψ ≤ Real.cos H := by
  rcases le_or_gt ψ π with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hH h hψ1
  · rw [← Real.cos_two_pi_sub ψ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hH (by linarith) (by linarith)

/-- **A periodic cut-off for an arc.** For `0 ≤ u₁`, `u₂ ≤ 2π` and `0 < m < u₂ - u₁` there is a continuous
`2π`-periodic `χ` with `0 ≤ χ ≤ 1`, vanishing at the points of `(0, 2π]` outside `(u₁, u₂)`, with `∫_{(0,2π]} χ ≥ m`.
It is `min 1 (K max 0 (cos(θ - c) - cos H))`, where `c` and `H` are the centre and half-width of the arc. -/
theorem buj_a_cutoff {u₁ u₂ m : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : u₂ ≤ 2 * π) (hm : 0 < m) (hmu : m < u₂ - u₁) :
    ∃ χ : ℝ → ℝ, Continuous χ ∧ Function.Periodic χ (2 * π) ∧ (∀ θ, 0 ≤ χ θ ∧ χ θ ≤ 1) ∧
      (∀ θ ∈ Ioc 0 (2 * π), θ ∉ Ioo u₁ u₂ → χ θ = 0) ∧ m ≤ ∫ θ in Ioc 0 (2 * π), χ θ := by
  set c : ℝ := (u₁ + u₂) / 2 with hc
  set H : ℝ := (u₂ - u₁) / 2 with hHdef
  set H' : ℝ := (m / 2 + H) / 2 with hH'def
  have hH : 0 < H := by rw [hHdef]; linarith
  have hHπ : H ≤ π := by rw [hHdef]; linarith
  have hH'H : H' < H := by rw [hH'def]; linarith
  have hH'0 : 0 < H' := by rw [hH'def]; linarith
  have hcos : Real.cos H < Real.cos H' := Real.cos_lt_cos_of_nonneg_of_le_pi hH'0.le hHπ hH'H
  set K : ℝ := (Real.cos H' - Real.cos H)⁻¹ with hKdef
  have hK : 0 < K := inv_pos.2 (sub_pos.2 hcos)
  set χ : ℝ → ℝ := fun θ => min 1 (K * max 0 (Real.cos (θ - c) - Real.cos H)) with hχdef
  have h01 : ∀ θ, 0 ≤ χ θ ∧ χ θ ≤ 1 := fun θ =>
    ⟨le_min zero_le_one (mul_nonneg hK.le (le_max_left _ _)), min_le_left _ _⟩
  have hχc : Continuous χ :=
    continuous_const.min (continuous_const.mul (continuous_const.max
      ((Real.continuous_cos.comp (continuous_id.sub continuous_const)).sub continuous_const)))
  refine ⟨χ, hχc, fun θ => ?_, h01, fun θ hθ hθu => ?_, ?_⟩
  · show min 1 (K * max 0 (Real.cos (θ + 2 * π - c) - Real.cos H)) =
      min 1 (K * max 0 (Real.cos (θ - c) - Real.cos H))
    rw [show θ + 2 * π - c = (θ - c) + 2 * π by ring, Real.cos_add_two_pi]
  · have hcle : Real.cos (θ - c) ≤ Real.cos H := by
      rcases le_or_gt θ u₁ with h | h
      · rw [← Real.cos_neg (θ - c), neg_sub]
        exact buj_a_cos_le hH.le (by linarith) (by linarith [hθ.1])
      · have h2 : u₂ ≤ θ := by
          by_contra h2
          exact hθu ⟨h, lt_of_not_ge h2⟩
        exact buj_a_cos_le hH.le (by linarith) (by linarith [hθ.2])
    show min 1 (K * max 0 (Real.cos (θ - c) - Real.cos H)) = 0
    rw [max_eq_left (sub_nonpos.2 hcle), mul_zero, min_eq_right zero_le_one]
  · have hsub : Icc (c - H') (c + H') ⊆ Ioc 0 (2 * π) := fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hone : ∀ θ ∈ Icc (c - H') (c + H'), χ θ = 1 := by
      intro θ hθ
      have habs : |θ - c| ≤ H' := abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      have hcos1 : Real.cos H' ≤ Real.cos (θ - c) := by
        rw [← Real.cos_abs (θ - c)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
      have hK1 : 1 ≤ K * max 0 (Real.cos (θ - c) - Real.cos H) := by
        calc (1 : ℝ) = K * (Real.cos H' - Real.cos H) := by
              rw [hKdef, inv_mul_cancel₀ (sub_pos.2 hcos).ne']
          _ ≤ K * max 0 (Real.cos (θ - c) - Real.cos H) := by
              gcongr
              exact le_max_of_le_right (by linarith)
      exact min_eq_left hK1
    calc m ≤ 2 * H' := by rw [hH'def]; linarith
      _ = ∫ θ in Icc (c - H') (c + H'), (1 : ℝ) := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
          ring
      _ = ∫ θ in Icc (c - H') (c + H'), χ θ :=
          setIntegral_congr_fun measurableSet_Icc fun θ hθ => (hone θ hθ).symm
      _ ≤ ∫ θ in Ioc 0 (2 * π), χ θ :=
          setIntegral_mono_set hχc.integrableOn_Ioc (ae_of_all _ fun θ => (h01 θ).1) hsub.eventuallyLE

/-- **The pointwise bound behind Jensen–length.** For `x > 0`, `a > 0` and `0 ≤ χ ≤ 1`:
`log x ≤ 2 (log a - 1) χ + 2 χ (√x / a) + 2 (1 - χ) √x` (the tangent bound on `χ`, `log x ≤ 2√x` on `1 - χ`). -/
theorem buj_a_log_le_mix {x a χ : ℝ} (hx : 0 < x) (ha : 0 < a) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    Real.log x ≤ 2 * (Real.log a - 1) * χ + 2 * χ * (Real.sqrt x / a) + 2 * (1 - χ) * Real.sqrt x := by
  have h1 := buj_log_le_tangent hx ha
  have h2 := buj_log_le_tangent hx one_pos
  rw [Real.log_one, div_one] at h2
  have h3 := mul_le_mul_of_nonneg_left h1 hχ0
  have h4 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hχ1)
  nlinarith [Real.sqrt_nonneg x]

/-- **A zero-free circle near the boundary.** For `G` holomorphic in `Δ` with `G 0 ≠ 0` and any `r₀ < 1`, some
`r ∈ (r₀, 1)`, `r > 0`, has no zero of `G` on `|z| = r` (the zeros in a smaller closed disc are finite). -/
theorem buj_a_exists_radius_ne_zero {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hG0 : G 0 ≠ 0)
    {r₀ : ℝ} (hr₀ : r₀ < 1) : ∃ r ∈ Ioo r₀ 1, 0 < r ∧ ∀ t : ℝ, G (circleMap 0 r t) ≠ 0 := by
  set r₁ : ℝ := max r₀ 0 with hr₁def
  have hr₁ : r₁ < 1 := max_lt hr₀ one_pos
  set r' : ℝ := (r₁ + 1) / 2 with hr'def
  have hr'1 : r' < 1 := by rw [hr'def]; linarith
  have hr₁r' : r₁ < r' := by rw [hr'def]; linarith
  set Z : Set ℂ := closedBall (0 : ℂ) r' ∩ {z | G z = 0} with hZdef
  have hZ : Z.Finite := by
    by_contra hinf
    obtain ⟨x, hxK, hx⟩ :=
      Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall (0 : ℂ) r') inter_subset_left
    have hxB : x ∈ ball (0 : ℂ) 1 := closedBall_subset_ball hr'1 hxK
    have hfreq : ∃ᶠ z in 𝓝[≠] x, G z = 0 := (accPt_iff_frequently_nhdsNE.1 hx).mono fun z hz => hz.2
    have h0 := hG.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected hxB hfreq
    exact hG0 (h0 (mem_ball_self one_pos))
  obtain ⟨r, hr, hrR⟩ := ((Set.Ioo_infinite hr₁r').sdiff (hZ.image fun z : ℂ => ‖z‖)).nonempty
  have hr0 : 0 < r := (le_max_right _ _).trans_lt hr.1
  refine ⟨r, ⟨(le_max_left _ _).trans_lt hr.1, hr.2.trans hr'1⟩, hr0, fun t ht => hrR ⟨circleMap 0 r t, ⟨?_, ht⟩, ?_⟩⟩
  · rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hr0]
    exact hr.2.le
  · simp only [norm_circleMap_zero, abs_of_pos hr0]

/-- **JL: the per-domain Jensen–length inequality.**

Setting:
* `ρ` is holomorphic in `Δ`, continuous on `Δ̄`, with `ρ'(0) ≠ 0`;
* `φ` is holomorphic on an open `U ⊇ ρ(Δ̄)`, with `φ(ρ 0) ≠ 0`;
* `V` is as in `buj_LC`;
* the boundary arc `θ ∈ (u₁, u₂)` has `√|φ|`-length `≤ ℓ` with `0 < ℓ ≤ m < u₂ - u₁`, and the whole boundary has
  `√|φ|`-length `≤ M` (`M ≥ 0`).

Claim: `2π (log |φ(ρ 0)| + 2 log |ρ'(0)|) ≤ 2m log(ℓ/m) + 2M`.

*Truth:* TRUE.

*Route:*
1. Put `G = (φ ∘ ρ) ρ'²` (analytic on `Δ`, `G 0 ≠ 0`). For `r < 1`, `buj_log_norm_le_circleAverage` gives
   `2π log |G(0)| ≤ ∫₀^{2π} log |G(re^{it})| dt`.
2. Take a continuous `2π`-periodic cut-off `0 ≤ χ ≤ 𝟙_(u₁,u₂)` with `∫ χ ≥ m` (a trapezoid; possible since
   `m < u₂ - u₁`).
3. Almost everywhere (the zeros of `G` on the circle are finite) use `buj_log_le_tangent` with `a = ℓ/m` on `χ`, and
   `log x ≤ 2√x` on `1 - χ`.
4. Note `|G(re^{it})|^{1/2} = |φ(ρ(re^{it}))|^{1/2} |ρ'(re^{it})|`. By uniform continuity of `|φ ∘ ρ|^{1/2}` on `Δ̄`,
   replace the weight by its boundary value, then let `r → 1⁻` with `buj_LC`, applied to
   `W = χ |φ(ρ(e^{i·}))|^{1/2}` and `W = (1 - χ) |φ(ρ(e^{i·}))|^{1/2}`.
5. Since `log(ℓ/m) - 1 < 0` and `∫ χ ≥ m`, the bound collapses to `2m log(ℓ/m) + 2M`. -/
theorem buj_JL (ρ φ : ℂ → ℂ) (U : Set ℂ) (V : StieltjesFunction ℝ) (u₁ u₂ m ℓ M : ℝ)
    (hρ : DiffContOnCl ℂ ρ (ball 0 1)) (hU : IsOpen U) (hρU : ρ '' closedBall 0 1 ⊆ U)
    (hφ : DifferentiableOn ℂ φ U) (hφ0 : φ (ρ 0) ≠ 0) (hρ0 : deriv ρ 0 ≠ 0)
    (hinc : ∀ θ h : ℝ, 0 ≤ h → ‖ρ (circleMap 0 1 (θ + h)) - ρ (circleMap 0 1 θ)‖ ≤ V (θ + h) - V θ)
    (hper : ∀ θ : ℝ, V (θ + 2 * π) = V θ + (V (2 * π) - V 0))
    (hu₁ : 0 ≤ u₁) (hu₂ : u₂ ≤ 2 * π) (hm : 0 < m) (hmu : m < u₂ - u₁) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (hM : 0 ≤ M)
    (harc : ∫⁻ θ in Ioo u₁ u₂, ENNReal.ofReal (Real.sqrt ‖φ (ρ (circleMap 0 1 θ))‖) ∂V.measure ≤
      ENNReal.ofReal ℓ)
    (htot : ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.sqrt ‖φ (ρ (circleMap 0 1 θ))‖) ∂V.measure ≤
      ENNReal.ofReal M) :
    2 * π * (Real.log ‖φ (ρ 0)‖ + 2 * Real.log ‖deriv ρ 0‖) ≤ 2 * m * Real.log (ℓ / m) + 2 * M := by
  -- analyticity and `G = (φ ∘ ρ) ρ'²`
  have hρan : AnalyticOnNhd ℂ ρ (ball 0 1) := hρ.differentiableOn.analyticOnNhd isOpen_ball
  have hρ'an : AnalyticOnNhd ℂ (deriv ρ) (ball 0 1) := hρan.deriv
  have hφan : AnalyticOnNhd ℂ φ U := hφ.analyticOnNhd hU
  have hρc : ContinuousOn ρ (closedBall 0 1) := by
    have := hρ.continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  have hρU' : ∀ z ∈ closedBall (0 : ℂ) 1, ρ z ∈ U := fun z hz => hρU (mem_image_of_mem ρ hz)
  set G : ℂ → ℂ := fun z => φ (ρ z) * deriv ρ z ^ 2 with hGdef
  have hGan : AnalyticOnNhd ℂ G (ball 0 1) := fun z hz =>
    ((hφan _ (hρU' z (ball_subset_closedBall hz))).comp (hρan z hz)).mul ((hρ'an z hz).pow 2)
  have hG0 : G 0 ≠ 0 := mul_ne_zero hφ0 (pow_ne_zero 2 hρ0)
  have hlogG : Real.log ‖G 0‖ = Real.log ‖φ (ρ 0)‖ + 2 * Real.log ‖deriv ρ 0‖ := by
    simp only [hGdef, norm_mul, norm_pow]
    rw [Real.log_mul (norm_ne_zero_iff.2 hφ0) (pow_ne_zero 2 (norm_ne_zero_iff.2 hρ0)), Real.log_pow]
    push_cast
    ring
  -- constants
  have ha : 0 < ℓ / m := div_pos hℓ hm
  have ha1 : ℓ / m ≤ 1 := (div_le_one hm).2 hℓm
  have hloga : Real.log (ℓ / m) - 1 < 0 := by linarith [Real.log_nonpos ha.le ha1]
  set L : ℝ := V (2 * π) - V 0 with hLdef
  have hL : 0 ≤ L := sub_nonneg.2 (V.mono Real.two_pi_pos.le)
  have hμ : V.measure (Ioc 0 (2 * π)) = ENNReal.ofReal L := V.measure_Ioc 0 (2 * π)
  obtain ⟨χ, hχc, hχp, hχ01, hχ0, hχm⟩ := buj_a_cutoff hu₁ hu₂ hm hmu
  -- the boundary weight `w = √|φ ∘ ρ|` on the circle
  have hφρc : ContinuousOn (fun z => Real.sqrt ‖φ (ρ z)‖) (closedBall 0 1) :=
    Real.continuous_sqrt.comp_continuousOn (hφ.continuousOn.comp hρc hρU').norm
  have hsph : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  set w : ℝ → ℝ := fun θ => Real.sqrt ‖φ (ρ (circleMap 0 1 θ))‖ with hwdef
  have hwc : Continuous w := hφρc.comp_continuous (continuous_circleMap 0 1) hsph
  have hwp : Function.Periodic w (2 * π) := fun θ => by
    show Real.sqrt ‖φ (ρ (circleMap 0 1 (θ + 2 * π)))‖ = Real.sqrt ‖φ (ρ (circleMap 0 1 θ))‖
    rw [periodic_circleMap 0 1 θ]
  have hw0 : ∀ θ, 0 ≤ w θ := fun θ => Real.sqrt_nonneg _
  -- the estimate for a fixed `η ∈ (0, 1]`
  have key : ∀ η : ℝ, 0 < η → η ≤ 1 →
      2 * π * Real.log ‖G 0‖ ≤ 2 * (Real.log (ℓ / m) - 1) * m +
        2 / (ℓ / m) * ((1 + η) * (ℓ + η * (L + 1))) + 2 * ((1 + η) * (M + η * (L + 1))) := by
    intro η hη hη1
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hφρc) η hη
    -- the two weights and their `dV`-integrals
    set W₁ : ℝ → ℝ := fun θ => χ θ * (w θ + η) with hW₁def
    set W₂ : ℝ → ℝ := fun θ => (1 - χ θ) * (w θ + η) with hW₂def
    have hW₁c : Continuous W₁ := hχc.mul (hwc.add continuous_const)
    have hW₂c : Continuous W₂ := (continuous_const.sub hχc).mul (hwc.add continuous_const)
    have hW₁0 : ∀ θ, 0 ≤ W₁ θ := fun θ => mul_nonneg (hχ01 θ).1 (add_nonneg (hw0 θ) hη.le)
    have hW₂0 : ∀ θ, 0 ≤ W₂ θ := fun θ => mul_nonneg (sub_nonneg.2 (hχ01 θ).2) (add_nonneg (hw0 θ) hη.le)
    have hW₁p : Function.Periodic W₁ (2 * π) := fun θ => by
      show χ (θ + 2 * π) * (w (θ + 2 * π) + η) = χ θ * (w θ + η)
      rw [hχp θ, hwp θ]
    have hW₂p : Function.Periodic W₂ (2 * π) := fun θ => by
      show (1 - χ (θ + 2 * π)) * (w (θ + 2 * π) + η) = (1 - χ θ) * (w θ + η)
      rw [hχp θ, hwp θ]
    have hB₁ : ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W₁ θ) ∂V.measure ≤ ENNReal.ofReal (ℓ + η * L) := by
      calc ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W₁ θ) ∂V.measure
          ≤ ∫⁻ θ in Ioc 0 (2 * π),
              (Ioo u₁ u₂).indicator (fun θ => ENNReal.ofReal (w θ) + ENNReal.ofReal η) θ ∂V.measure := by
            refine setLIntegral_mono' measurableSet_Ioc fun θ hθ => ?_
            by_cases hθu : θ ∈ Ioo u₁ u₂
            · rw [indicator_of_mem hθu, ← ENNReal.ofReal_add (hw0 θ) hη.le]
              exact ENNReal.ofReal_le_ofReal
                (mul_le_of_le_one_left (add_nonneg (hw0 θ) hη.le) (hχ01 θ).2)
            · rw [indicator_of_notMem hθu]
              show ENNReal.ofReal (χ θ * (w θ + η)) ≤ 0
              rw [hχ0 θ hθ hθu, zero_mul, ENNReal.ofReal_zero]
        _ ≤ ∫⁻ θ, (Ioo u₁ u₂).indicator (fun θ => ENNReal.ofReal (w θ) + ENNReal.ofReal η) θ ∂V.measure :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ θ in Ioo u₁ u₂, ENNReal.ofReal (w θ) ∂V.measure +
              ENNReal.ofReal η * V.measure (Ioo u₁ u₂) := by
            rw [lintegral_indicator measurableSet_Ioo, lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ENNReal.ofReal ℓ + ENNReal.ofReal η * ENNReal.ofReal L := by
            refine add_le_add harc ?_
            rw [← hμ]
            exact mul_le_mul_of_nonneg_left (measure_mono (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc hu₁ hu₂)))
              zero_le
        _ = ENNReal.ofReal (ℓ + η * L) := by
            rw [← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add hℓ.le (mul_nonneg hη.le hL)]
    have hB₂ : ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W₂ θ) ∂V.measure ≤ ENNReal.ofReal (M + η * L) := by
      calc ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (W₂ θ) ∂V.measure
          ≤ ∫⁻ θ in Ioc 0 (2 * π), (ENNReal.ofReal (w θ) + ENNReal.ofReal η) ∂V.measure := by
            refine lintegral_mono fun θ => ?_
            rw [← ENNReal.ofReal_add (hw0 θ) hη.le]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_of_le_one_left (add_nonneg (hw0 θ) hη.le) (by linarith [(hχ01 θ).1]))
        _ = ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (w θ) ∂V.measure +
              ENNReal.ofReal η * V.measure (Ioc 0 (2 * π)) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ENNReal.ofReal M + ENNReal.ofReal η * ENNReal.ofReal L := by
            rw [hμ]
            exact add_le_add htot le_rfl
        _ = ENNReal.ofReal (M + η * L) := by
            rw [← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add hM (mul_nonneg hη.le hL)]
    -- LC for the two weights
    have hℓη : 0 < ℓ + η * (L + 1) := add_pos_of_pos_of_nonneg hℓ (mul_nonneg hη.le (by linarith))
    have hMη : 0 < M + η * (L + 1) := add_pos_of_nonneg_of_pos hM (mul_pos hη (by linarith))
    have hE₁ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W₁ t) *
        ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ₑ < ENNReal.ofReal (ℓ + η * (L + 1)) :=
      eventually_lt_of_limsup_lt ((buj_LC ρ V W₁ hρ hW₁c hW₁0 hW₁p hinc hper).trans_lt
        (hB₁.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hℓη).2 (by nlinarith))))
    have hE₂ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W₂ t) *
        ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ₑ < ENNReal.ofReal (M + η * (L + 1)) :=
      eventually_lt_of_limsup_lt ((buj_LC ρ V W₂ hρ hW₂c hW₂0 hW₂p hinc hper).trans_lt
        (hB₂.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hMη).2 (by nlinarith))))
    have hEr : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (max (1 - δ) (1 / (1 + η))) 1 :=
      Ioo_mem_nhdsLT (max_lt (by linarith) ((div_lt_one (by linarith)).2 (by linarith)))
    -- a good radius
    obtain ⟨r₀, hr₀1, hr₀⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hE₁.and (hE₂.and hEr))
    obtain ⟨r, hr, hr0, hGr⟩ := buj_a_exists_radius_ne_zero hGan hG0 hr₀1
    obtain ⟨hr₁, hr₂, hr₃⟩ := hr₀ hr
    have hr1 : r < 1 := hr₃.2
    have hrδ : 1 - δ < r := (le_max_left _ _).trans_lt hr₃.1
    have hrη : 1 < r * (1 + η) := (div_lt_iff₀ (by linarith)).1 ((le_max_right _ _).trans_lt hr₃.1)
    have hzball : ∀ t : ℝ, circleMap 0 r t ∈ ball (0 : ℂ) 1 := fun t => by
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hr1
    have hDc : Continuous fun t : ℝ => ‖deriv ρ (circleMap 0 r t)‖ :=
      (hρ'an.continuousOn.comp_continuous (continuous_circleMap 0 r) hzball).norm
    have hGc : Continuous fun t : ℝ => G (circleMap 0 r t) :=
      hGan.continuousOn.comp_continuous (continuous_circleMap 0 r) hzball
    have hderiv : ∀ t : ℝ, ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ = r * ‖deriv ρ (circleMap 0 r t)‖ := by
      intro t
      have hFd : HasDerivAt (fun s => ρ (circleMap 0 r s))
          (deriv ρ (circleMap 0 r t) * (circleMap 0 r t * I)) t :=
        (hρan _ (hzball t)).differentiableAt.hasDerivAt.comp t (hasDerivAt_circleMap 0 r t)
      rw [hFd.deriv, norm_mul, norm_mul, norm_circleMap_zero, abs_of_pos hr0, Complex.norm_I, mul_one,
        mul_comm]
    -- LC in real form at the radius `r`
    have hconv : ∀ W : ℝ → ℝ, Continuous W → (∀ t, 0 ≤ W t) → ∀ B : ℝ, 0 ≤ B →
        ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) * ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ₑ <
          ENNReal.ofReal B →
        ∫ t in Ioc 0 (2 * π), W t * ‖deriv ρ (circleMap 0 r t)‖ ≤ (1 + η) * B := by
      intro W hWc hW0 B hB hlt
      have hlint : ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t) * ‖deriv (fun s => ρ (circleMap 0 r s)) t‖ₑ =
          ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t * (r * ‖deriv ρ (circleMap 0 r t)‖)) := by
        refine lintegral_congr fun t => ?_
        rw [← ofReal_norm, hderiv t, ENNReal.ofReal_mul (hW0 t)]
      have hreal : ∫ t in Ioc 0 (2 * π), W t * (r * ‖deriv ρ (circleMap 0 r t)‖) =
          (∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (W t * (r * ‖deriv ρ (circleMap 0 r t)‖))).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun t => mul_nonneg (hW0 t) (mul_nonneg hr0.le (norm_nonneg _)))
          (hWc.mul (continuous_const.mul hDc)).aestronglyMeasurable
      have hrJ : r * ∫ t in Ioc 0 (2 * π), W t * ‖deriv ρ (circleMap 0 r t)‖ ≤ B := by
        rw [← integral_const_mul]
        have h1 : ∫ t in Ioc 0 (2 * π), r * (W t * ‖deriv ρ (circleMap 0 r t)‖) =
            ∫ t in Ioc 0 (2 * π), W t * (r * ‖deriv ρ (circleMap 0 r t)‖) :=
          integral_congr_ae (Eventually.of_forall fun t => by ring)
        rw [h1, hreal, ← hlint]
        exact ENNReal.toReal_le_of_le_ofReal hB hlt.le
      have hJ0 : 0 ≤ ∫ t in Ioc 0 (2 * π), W t * ‖deriv ρ (circleMap 0 r t)‖ :=
        setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hW0 t) (norm_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left hrη.le hJ0,
        mul_le_mul_of_nonneg_right hrJ (by linarith : (0 : ℝ) ≤ 1 + η)]
    have hI₁ := hconv W₁ hW₁c hW₁0 _ hℓη.le hr₁
    have hI₂ := hconv W₂ hW₂c hW₂0 _ hMη.le hr₂
    -- Jensen at the radius `r`
    have hJ := buj_log_norm_le_circleAverage hr0
      (hGan.mono (by rw [abs_of_pos hr0]; exact closedBall_subset_ball hr1)) hG0
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le] at hJ
    have hJ' : 2 * π * Real.log ‖G 0‖ ≤ ∫ t in Ioc 0 (2 * π), Real.log ‖G (circleMap 0 r t)‖ := by
      have := mul_le_mul_of_nonneg_left hJ Real.two_pi_pos.le
      rwa [← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul] at this
    -- the pointwise bound
    have hsq : ∀ t : ℝ, Real.sqrt ‖G (circleMap 0 r t)‖ ≤ (w t + η) * ‖deriv ρ (circleMap 0 r t)‖ := by
      intro t
      have hz : circleMap 0 r t ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall (hzball t)
      have hd : dist (circleMap 0 r t) (circleMap 0 1 t) < δ := by
        rw [buj_a_dist_circleMap, abs_of_neg (by linarith)]; linarith
      have h1 : |Real.sqrt ‖φ (ρ (circleMap 0 r t))‖ - Real.sqrt ‖φ (ρ (circleMap 0 1 t))‖| < η := by
        have := hδu _ hz _ (hsph t) hd
        rwa [Real.dist_eq] at this
      have h2 : Real.sqrt ‖φ (ρ (circleMap 0 r t))‖ ≤ Real.sqrt ‖φ (ρ (circleMap 0 1 t))‖ + η := by
        linarith [(abs_lt.1 h1).2]
      have h3 : Real.sqrt ‖G (circleMap 0 r t)‖ =
          Real.sqrt ‖φ (ρ (circleMap 0 r t))‖ * ‖deriv ρ (circleMap 0 r t)‖ := by
        simp only [hGdef, norm_mul, norm_pow]
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have hpt : ∀ t : ℝ, Real.log ‖G (circleMap 0 r t)‖ ≤ 2 * (Real.log (ℓ / m) - 1) * χ t +
        2 / (ℓ / m) * (W₁ t * ‖deriv ρ (circleMap 0 r t)‖) + 2 * (W₂ t * ‖deriv ρ (circleMap 0 r t)‖) := by
      intro t
      have hx : 0 < ‖G (circleMap 0 r t)‖ := norm_pos_iff.2 (hGr t)
      have h1 := buj_a_log_le_mix hx ha (hχ01 t).1 (hχ01 t).2
      have h3 : χ t * Real.sqrt ‖G (circleMap 0 r t)‖ ≤ W₁ t * ‖deriv ρ (circleMap 0 r t)‖ := by
        calc χ t * Real.sqrt ‖G (circleMap 0 r t)‖
            ≤ χ t * ((w t + η) * ‖deriv ρ (circleMap 0 r t)‖) :=
              mul_le_mul_of_nonneg_left (hsq t) (hχ01 t).1
          _ = W₁ t * ‖deriv ρ (circleMap 0 r t)‖ := by
              show _ = χ t * (w t + η) * _
              ring
      have h4 : (1 - χ t) * Real.sqrt ‖G (circleMap 0 r t)‖ ≤ W₂ t * ‖deriv ρ (circleMap 0 r t)‖ := by
        calc (1 - χ t) * Real.sqrt ‖G (circleMap 0 r t)‖
            ≤ (1 - χ t) * ((w t + η) * ‖deriv ρ (circleMap 0 r t)‖) :=
              mul_le_mul_of_nonneg_left (hsq t) (sub_nonneg.2 (hχ01 t).2)
          _ = W₂ t * ‖deriv ρ (circleMap 0 r t)‖ := by
              show _ = (1 - χ t) * (w t + η) * _
              ring
      have h5 : 2 * χ t * (Real.sqrt ‖G (circleMap 0 r t)‖ / (ℓ / m)) =
          2 / (ℓ / m) * (χ t * Real.sqrt ‖G (circleMap 0 r t)‖) := by ring
      have h6 := mul_le_mul_of_nonneg_left h3 (div_pos two_pos ha).le
      rw [h5] at h1
      linarith
    -- integrate
    have hlogc : Continuous fun t : ℝ => Real.log ‖G (circleMap 0 r t)‖ :=
      hGc.norm.log fun t => norm_ne_zero_iff.2 (hGr t)
    have iχ : Integrable (fun t => 2 * (Real.log (ℓ / m) - 1) * χ t) (volume.restrict (Ioc 0 (2 * π))) :=
      (continuous_const.mul hχc).integrableOn_Ioc
    have i₁ : Integrable (fun t => 2 / (ℓ / m) * (W₁ t * ‖deriv ρ (circleMap 0 r t)‖))
        (volume.restrict (Ioc 0 (2 * π))) := (continuous_const.mul (hW₁c.mul hDc)).integrableOn_Ioc
    have i₂ : Integrable (fun t => 2 * (W₂ t * ‖deriv ρ (circleMap 0 r t)‖))
        (volume.restrict (Ioc 0 (2 * π))) := (continuous_const.mul (hW₂c.mul hDc)).integrableOn_Ioc
    have hint : ∫ t in Ioc 0 (2 * π), Real.log ‖G (circleMap 0 r t)‖ ≤
        ∫ t in Ioc 0 (2 * π), (2 * (Real.log (ℓ / m) - 1) * χ t +
          2 / (ℓ / m) * (W₁ t * ‖deriv ρ (circleMap 0 r t)‖) + 2 * (W₂ t * ‖deriv ρ (circleMap 0 r t)‖)) :=
      integral_mono hlogc.integrableOn_Ioc ((iχ.add i₁).add i₂) hpt
    have iχ₁ : Integrable (fun t => 2 * (Real.log (ℓ / m) - 1) * χ t +
        2 / (ℓ / m) * (W₁ t * ‖deriv ρ (circleMap 0 r t)‖)) (volume.restrict (Ioc 0 (2 * π))) := iχ.add i₁
    rw [integral_add iχ₁ i₂, integral_add iχ i₁, integral_const_mul, integral_const_mul,
      integral_const_mul] at hint
    have h1 : 2 * (Real.log (ℓ / m) - 1) * ∫ t in Ioc 0 (2 * π), χ t ≤ 2 * (Real.log (ℓ / m) - 1) * m :=
      mul_le_mul_of_nonpos_left hχm (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hI₁ (div_pos two_pos ha).le
    have h3 := mul_le_mul_of_nonneg_left hI₂ (zero_le_two : (0 : ℝ) ≤ 2)
    linarith
  -- let `η → 0⁺`
  have hc : Continuous fun η : ℝ => 2 * (Real.log (ℓ / m) - 1) * m +
      2 / (ℓ / m) * ((1 + η) * (ℓ + η * (L + 1))) + 2 * ((1 + η) * (M + η * (L + 1))) := by
    fun_prop
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 2 * π * Real.log ‖G 0‖ ≤ 2 * (Real.log (ℓ / m) - 1) * m +
      2 / (ℓ / m) * ((1 + η) * (ℓ + η * (L + 1))) + 2 * ((1 + η) * (M + η * (L + 1))) := by
    filter_upwards [Ioc_mem_nhdsGT one_pos] with η hη
    exact key η hη.1 hη.2
  have hle := ge_of_tendsto ((hc.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have h2m : 2 / (ℓ / m) * ℓ = 2 * m := by
    field_simp
  simp only [zero_mul, add_zero, one_mul] at hle
  rw [hlogG] at hle
  linarith

/-- `Im (w / e^{iα}) = ‖w‖ sin (arg w - α)`. -/
theorem buj_b_im_div_exp (w : ℂ) (α : ℝ) :
    (w / exp (α * I)).im = ‖w‖ * Real.sin (arg w - α) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_div_assoc, ← Complex.exp_sub, ← sub_mul, ← Complex.ofReal_sub, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- `Im w = ‖w‖ sin (arg w)`. -/
theorem buj_b_im_eq (w : ℂ) : w.im = ‖w‖ * Real.sin (arg w) := by
  have h := buj_b_im_div_exp w 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, div_one, sub_zero] at h
  exact h

/-- For `0 < α < π`: `w ≠ 0 ∧ 0 < arg w < α` iff `0 < Im w` and `Im (w / e^{iα}) < 0`. -/
theorem buj_b_sector_iff {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) (w : ℂ) :
    (w ≠ 0 ∧ 0 < arg w ∧ arg w < α) ↔ (0 < w.im ∧ (w / exp (α * I)).im < 0) := by
  rw [buj_b_im_div_exp, buj_b_im_eq]
  have hpi := Complex.arg_le_pi w
  have hnpi := Complex.neg_pi_lt_arg w
  constructor
  · rintro ⟨hw, h1, h2⟩
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    exact ⟨mul_pos hn (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)),
      mul_neg_of_pos_of_neg hn (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))⟩
  · rintro ⟨h1, h2⟩
    have hw : w ≠ 0 := by
      rintro rfl
      simp at h1
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hs : 0 < Real.sin (arg w) := pos_of_mul_pos_right h1 hn.le
    have ha0 : 0 < arg w := by
      by_contra h
      push Not at h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le h hnpi.le
      linarith
    refine ⟨hw, ha0, ?_⟩
    by_contra h
    push Not at h
    have h3 : 0 ≤ Real.sin (arg w - α) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have h4 : 0 ≤ ‖w‖ * Real.sin (arg w - α) := mul_nonneg hn.le h3
    linarith

/-- Membership in the open sector through the two imaginary parts. -/
theorem buj_b_mem_openSector_iff {ξ : ℂ} {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) (z : ℂ) :
    z ∈ buj_openSector ξ α ↔ 0 < (z / ξ).im ∧ (z / ξ / exp (α * I)).im < 0 :=
  buj_b_sector_iff hα0 hαπ (z / ξ)

/-- A point of the closed sector (in the two imaginary parts) has `0 ≤ arg ≤ α`. -/
theorem buj_b_arg_of_closed {α : ℝ} (hα0 : 0 < α) {w : ℂ} (h1 : 0 ≤ w.im)
    (h2 : (w / exp (α * I)).im ≤ 0) : 0 ≤ arg w ∧ arg w ≤ α := by
  refine ⟨Complex.arg_nonneg_iff.2 h1, ?_⟩
  by_cases hw : w = 0
  · rw [hw, Complex.arg_zero]
    exact hα0.le
  by_contra h
  push Not at h
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [buj_b_im_div_exp] at h2
  have hpi := Complex.arg_le_pi w
  have h3 : 0 < Real.sin (arg w - α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h4 : 0 < ‖w‖ * Real.sin (arg w - α) := mul_pos hn h3
  linarith

/-- `(r ξ) / ξ = r`. -/
theorem buj_b_side1_div {ξ : ℂ} (hξ : ξ ≠ 0) (r : ℝ) : (r : ℂ) * ξ / ξ = r :=
  mul_div_cancel_right₀ _ hξ

/-- `(r ξ e^{iα}) / ξ = r e^{iα}`. -/
theorem buj_b_side2_div {ξ : ℂ} (hξ : ξ ≠ 0) (α r : ℝ) :
    (r : ℂ) * (ξ * exp (α * I)) / ξ = r * exp (α * I) := by
  rw [mul_left_comm, mul_div_cancel_left₀ _ hξ]

/-- Points of the first side are not in the open sector. -/
theorem buj_b_side1_notMem {ξ : ℂ} {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hξ : ξ ≠ 0) (r : ℝ) :
    (r : ℂ) * ξ ∉ buj_openSector ξ α := by
  rw [buj_b_mem_openSector_iff hα0 hαπ, buj_b_side1_div hξ, Complex.ofReal_im]
  exact fun h => lt_irrefl _ h.1

/-- Points of the second side are not in the open sector. -/
theorem buj_b_side2_notMem {ξ : ℂ} {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) (hξ : ξ ≠ 0) (r : ℝ) :
    (r : ℂ) * (ξ * exp (α * I)) ∉ buj_openSector ξ α := by
  rw [buj_b_mem_openSector_iff hα0 hαπ, buj_b_side2_div hξ,
    mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), Complex.ofReal_im]
  exact fun h => lt_irrefl _ h.2

/-- A point of a segment `[0, a v]` is `r v` with `r ∈ [0, a]`. -/
theorem buj_b_mem_segment_iff {v z : ℂ} {a : ℝ} (ha : 0 < a) :
    z ∈ segment ℝ 0 ((a : ℂ) * v) ↔ ∃ r ∈ Icc 0 a, z = (r : ℂ) * v := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨θ * a, ⟨mul_nonneg hθ.1 ha.le, by nlinarith [hθ.2]⟩, ?_⟩
    simp only [smul_zero, zero_add, Complex.real_smul, Complex.ofReal_mul]
    ring
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r / a, ⟨div_nonneg hr.1 ha.le, (div_le_one ha).2 hr.2⟩, ?_⟩
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [smul_zero, zero_add, Complex.real_smul, Complex.ofReal_div]
    field_simp

/-- The closed loop of a sector cut on `[0, a + (t - s) + b]`: the first side `x ↦ x ξ` on `[0, a]`, the cut `τ`
(translated) on `[a, a + (t - s)]`, and the second side back to `0`. -/
def buj_b_loop (ξ : ℂ) (α a b : ℝ) (τ : ℝ → ℂ) (s t x : ℝ) : ℂ :=
  if x ≤ a then (x : ℂ) * ξ else if x ≤ a + (t - s) then τ (x + (s - a))
  else ((a + (t - s) + b - x : ℝ) : ℂ) * (ξ * exp (α * I))

/-- The loop on the first side. -/
theorem buj_b_loop_left {ξ : ℂ} {α a b s t x : ℝ} {τ : ℝ → ℂ} (hx : x ≤ a) :
    buj_b_loop ξ α a b τ s t x = (x : ℂ) * ξ := ite_eq_left hx

/-- The loop on the cut. -/
theorem buj_b_loop_mid {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t)
    {x : ℝ} (hx : x ∈ Icc a (a + (t - s))) : buj_b_loop ξ α a b τ s t x = τ (x + (s - a)) := by
  obtain ⟨-, ⟨-, -, hτs, -⟩, -⟩ := hcut
  unfold buj_b_loop
  by_cases h : x ≤ a
  · have hxa : x = a := le_antisymm h hx.1
    rw [ite_eq_left h, hxa, hτs.symm]
    congr 1
    ring
  · rw [ite_eq_right h, ite_eq_left hx.2]

/-- The loop on the second side. -/
theorem buj_b_loop_right {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t)
    {x : ℝ} (hx : a + (t - s) ≤ x) :
    buj_b_loop ξ α a b τ s t x = ((a + (t - s) + b - x : ℝ) : ℂ) * (ξ * exp (α * I)) := by
  obtain ⟨⟨-, -, -, -, -, -, hst⟩, ⟨-, -, -, hτt⟩, -⟩ := hcut
  unfold buj_b_loop
  have h1 : ¬ x ≤ a := by intro h; linarith
  rw [ite_eq_right h1]
  by_cases h : x ≤ a + (t - s)
  · have hxc : x = a + (t - s) := le_antisymm h hx
    rw [ite_eq_left h, hxc, show a + (t - s) + (s - a) = t by ring, hτt]
    congr 2
    ring
  · rw [ite_eq_right h]

/-- The loop is continuous on `[0, L]`. -/
theorem buj_b_loop_continuousOn {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    ContinuousOn (buj_b_loop ξ α a b τ s t) (Icc 0 (a + (t - s) + b)) := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, ha, hb, hst⟩, ⟨hτc, -⟩, -⟩ := hc
  have h1 : ContinuousOn (buj_b_loop ξ α a b τ s t) (Icc 0 a) :=
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn).congr fun x hx =>
      buj_b_loop_left hx.2
  have h2 : ContinuousOn (buj_b_loop ξ α a b τ s t) (Icc a (a + (t - s))) := by
    have hadd : Continuous fun x : ℝ => x + (s - a) := continuous_id.add continuous_const
    refine (hτc.comp hadd.continuousOn ?_).congr fun x hx => buj_b_loop_mid hcut hx
    intro x hx
    exact ⟨show s ≤ x + (s - a) by linarith [hx.1], show x + (s - a) ≤ t by linarith [hx.2]⟩
  have h3 : ContinuousOn (buj_b_loop ξ α a b τ s t) (Icc (a + (t - s)) (a + (t - s) + b)) := by
    have hc3 : Continuous fun x : ℝ => ((a + (t - s) + b - x : ℝ) : ℂ) * (ξ * exp (α * I)) :=
      (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const
    exact hc3.continuousOn.congr fun x hx => buj_b_loop_right hcut hx.1
  refine ((h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).union_of_isClosed h3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc).mono ?_
  intro x hx
  by_cases hxa : x ≤ a
  · exact Or.inl (Or.inl ⟨hx.1, hxa⟩)
  by_cases hxc : x ≤ a + (t - s)
  · exact Or.inl (Or.inr ⟨(not_le.1 hxa).le, hxc⟩)
  · exact Or.inr ⟨(not_le.1 hxc).le, hx.2⟩

/-- The loop starts at `0`. -/
theorem buj_b_loop_zero {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    buj_b_loop ξ α a b τ s t 0 = 0 := by
  obtain ⟨⟨-, -, -, -, ha, -⟩, -⟩ := hcut
  rw [buj_b_loop_left ha.le]
  simp

/-- The loop ends at `0`. -/
theorem buj_b_loop_L {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    buj_b_loop ξ α a b τ s t (a + (t - s) + b) = 0 := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, -, hb, -⟩, -⟩ := hc
  rw [buj_b_loop_right hcut (by linarith)]
  simp

/-- The loop traces the cut curve. -/
theorem buj_b_loop_image {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    buj_b_loop ξ α a b τ s t '' Icc 0 (a + (t - s) + b) = buj_cutCurve ξ α a b τ s t := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, ha, hb, hst⟩, -⟩ := hc
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x ≤ a
    · refine Or.inl (Or.inl ((buj_b_mem_segment_iff ha).2 ⟨x, ⟨hx.1, hxa⟩, buj_b_loop_left hxa⟩))
    by_cases hxc : x ≤ a + (t - s)
    · refine Or.inl (Or.inr ⟨x + (s - a), ⟨by linarith [not_le.1 hxa], by linarith⟩, ?_⟩)
      exact (buj_b_loop_mid hcut ⟨(not_le.1 hxa).le, hxc⟩).symm
    · refine Or.inr ((buj_b_mem_segment_iff hb).2 ⟨a + (t - s) + b - x, ⟨by linarith [hx.2], by
        linarith [not_le.1 hxc]⟩, buj_b_loop_right hcut (not_le.1 hxc).le⟩)
  · rintro ((hz | ⟨u, hu, rfl⟩) | hz)
    · obtain ⟨r, hr, rfl⟩ := (buj_b_mem_segment_iff ha).1 hz
      exact ⟨r, ⟨hr.1, by linarith [hr.2]⟩, buj_b_loop_left hr.2⟩
    · refine ⟨u - (s - a), ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [buj_b_loop_mid hcut ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring
    · obtain ⟨r, hr, rfl⟩ := (buj_b_mem_segment_iff hb).1 hz
      refine ⟨a + (t - s) + b - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
      rw [buj_b_loop_right hcut (by linarith [hr.2])]
      congr 2
      ring

/-- The loop is injective on `[0, L)`. -/
theorem buj_b_loop_injOn {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    InjOn (buj_b_loop ξ α a b τ s t) (Ico 0 (a + (t - s) + b)) := by
  have hc := hcut
  obtain ⟨⟨hα0, hαπ, hξ, -, -, -, -⟩, ⟨-, hτi, -, -⟩, hτO, -⟩ := hc
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp at hξ
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hl1_left : ∀ x, x ≤ a → (buj_b_loop ξ α a b τ s t x / ξ).im = 0 := fun x hx => by
    rw [buj_b_loop_left hx, buj_b_side1_div hξ0, Complex.ofReal_im]
  have hl1_pos : ∀ x, a < x → x < a + (t - s) + b → 0 < (buj_b_loop ξ α a b τ s t x / ξ).im := by
    intro x hx1 hx2
    by_cases hxc : x < a + (t - s)
    · rw [buj_b_loop_mid hcut ⟨hx1.le, hxc.le⟩]
      exact ((buj_b_mem_openSector_iff hα0 hαπ _).1 (hτO _ ⟨by linarith, by linarith⟩)).1
    · rw [buj_b_loop_right hcut (not_lt.1 hxc), buj_b_side2_div hξ0, Complex.im_ofReal_mul,
        Complex.exp_ofReal_mul_I_im]
      exact mul_pos (by linarith) hsin
  have hl2_right : ∀ x, a + (t - s) ≤ x → (buj_b_loop ξ α a b τ s t x / ξ / exp (α * I)).im = 0 :=
    fun x hx => by
      rw [buj_b_loop_right hcut hx, buj_b_side2_div hξ0, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _),
        Complex.ofReal_im]
  have hl2_mid : ∀ x, a < x → x < a + (t - s) → (buj_b_loop ξ α a b τ s t x / ξ / exp (α * I)).im < 0 :=
    fun x hx1 hx2 => by
      rw [buj_b_loop_mid hcut ⟨hx1.le, hx2.le⟩]
      exact ((buj_b_mem_openSector_iff hα0 hαπ _).1 (hτO _ ⟨by linarith, by linarith⟩)).2
  intro x hx y hy hxy
  rcases le_or_gt x a with hxa | hxa <;> rcases le_or_gt y a with hya | hya
  · rw [buj_b_loop_left hxa, buj_b_loop_left hya] at hxy
    exact_mod_cast mul_right_cancel₀ hξ0 hxy
  · exfalso
    have h1 := hl1_left x hxa
    have h2 := hl1_pos y hya hy.2
    rw [hxy] at h1
    linarith
  · exfalso
    have h1 := hl1_left y hya
    have h2 := hl1_pos x hxa hx.2
    rw [hxy] at h2
    linarith
  · rcases lt_or_ge x (a + (t - s)) with hxc | hxc <;> rcases lt_or_ge y (a + (t - s)) with hyc | hyc
    · rw [buj_b_loop_mid hcut ⟨hxa.le, hxc.le⟩, buj_b_loop_mid hcut ⟨hya.le, hyc.le⟩] at hxy
      have := hτi ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxy
      linarith
    · exfalso
      have h1 := hl2_mid x hxa hxc
      have h2 := hl2_right y hyc
      rw [hxy] at h1
      linarith
    · exfalso
      have h1 := hl2_mid y hya hyc
      have h2 := hl2_right x hxc
      rw [hxy] at h2
      linarith
    · rw [buj_b_loop_right hcut hxc, buj_b_loop_right hcut hyc] at hxy
      have hne : ξ * exp (α * I) ≠ 0 := mul_ne_zero hξ0 (Complex.exp_ne_zero _)
      have h1 := mul_right_cancel₀ hne hxy
      have h2 : a + (t - s) + b - x = a + (t - s) + b - y := by exact_mod_cast h1
      linarith

/-- The cut curve is a Jordan curve. -/
theorem buj_b_isJordanCurve {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    IsJordanCurve (toExt (buj_cutCurve ξ α a b τ s t)) := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, ha, hb, hst⟩, -⟩ := hc
  have hL0 : 0 < a + (t - s) + b := by linarith
  have hFimg : (fun u : ℝ => buj_b_loop ξ α a b τ s t ((a + (t - s) + b) * u)) '' Icc 0 1 =
      buj_cutCurve ξ α a b τ s t := by
    rw [← buj_b_loop_image hcut]
    have h : (fun u : ℝ => (a + (t - s) + b) * u) '' Icc 0 1 = Icc 0 (a + (t - s) + b) := by
      rw [image_mul_left_Icc hL0.le zero_le_one, mul_zero, mul_one]
    rw [← h, image_image]
  rw [← hFimg]
  refine isJordanCurve_of_loop ?_ ?_ ?_
  · exact (buj_b_loop_continuousOn hcut).comp (continuous_const.mul continuous_id).continuousOn
      (fun u hu => ⟨mul_nonneg hL0.le hu.1, mul_le_of_le_one_right hL0.le hu.2⟩)
  · intro u hu v hv huv
    have h := buj_b_loop_injOn hcut ⟨mul_nonneg hL0.le hu.1, mul_lt_of_lt_one_right hL0 hu.2⟩
      ⟨mul_nonneg hL0.le hv.1, mul_lt_of_lt_one_right hL0 hv.2⟩ huv
    exact mul_left_cancel₀ hL0.ne' h
  · simp only [mul_zero, mul_one]
    rw [buj_b_loop_zero hcut, buj_b_loop_L hcut]

/-- The points of the cut curve: the closed-sector inequalities, `‖z‖ < 1`, and `‖z‖ > r₀` on the open sector. -/
theorem buj_b_cutCurve_props {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t)
    {z : ℂ} (hz : z ∈ buj_cutCurve ξ α a b τ s t) :
    0 ≤ (z / ξ).im ∧ (z / ξ / exp (α * I)).im ≤ 0 ∧ ‖z‖ < 1 ∧ (z ∈ buj_openSector ξ α → r₀ < ‖z‖) := by
  have hc := hcut
  obtain ⟨⟨hα0, hαπ, hξ, -, ha, hb, hst⟩, ⟨-, -, hτs, hτt⟩, hτO, hτn, -⟩ := hc
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp at hξ
  have hξe : ‖ξ * exp (α * I)‖ = 1 := by rw [norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have ha1 : a < 1 := by
    have h := (hτn s ⟨le_rfl, hst.le⟩).2
    rwa [hτs, norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at h
  have hb1 : b < 1 := by
    have h := (hτn t ⟨hst.le, le_rfl⟩).2
    rwa [hτt, norm_mul, hξe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at h
  rw [← buj_b_loop_image hcut] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rcases le_or_gt x a with hxa | hxa
  · rw [buj_b_loop_left hxa]
    refine ⟨?_, ?_, ?_, fun h => absurd h (buj_b_side1_notMem hα0 hαπ hξ0 x)⟩
    · rw [buj_b_side1_div hξ0, Complex.ofReal_im]
    · rw [buj_b_side1_div hξ0, buj_b_im_div_exp, Complex.arg_ofReal_of_nonneg hx.1, zero_sub, Real.sin_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (by linarith)
    · rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      linarith
  rcases lt_or_ge x (a + (t - s)) with hxc | hxc
  · rw [buj_b_loop_mid hcut ⟨hxa.le, hxc.le⟩]
    have hu : x + (s - a) ∈ Ioo s t := ⟨by linarith, by linarith⟩
    have hO := (buj_b_mem_openSector_iff hα0 hαπ _).1 (hτO _ hu)
    have hn := hτn _ (Ioo_subset_Icc_self hu)
    exact ⟨hO.1.le, hO.2.le, hn.2, fun _ => hn.1⟩
  · rw [buj_b_loop_right hcut hxc]
    refine ⟨?_, ?_, ?_, fun h => absurd h (buj_b_side2_notMem hα0 hαπ hξ0 _)⟩
    · rw [buj_b_side2_div hξ0, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      exact mul_nonneg (by linarith [hx.2]) hsin.le
    · rw [buj_b_side2_div hξ0, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), Complex.ofReal_im]
    · rw [norm_mul, hξe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.2])]
      linarith

/-- `z ↦ Im (z / ζ)` is `ℝ`-linear. -/
theorem buj_b_isLinearMap_im_div (ζ : ℂ) : IsLinearMap ℝ (fun z : ℂ => (z / ζ).im) := by
  refine ⟨fun x y => by simp only [add_div, Complex.add_im], fun c x => ?_⟩
  simp only [Complex.real_smul, smul_eq_mul, mul_div_assoc, Complex.im_ofReal_mul]

/-- The open sector is convex. -/
theorem buj_b_openSector_convex {ξ : ℂ} {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) :
    Convex ℝ (buj_openSector ξ α) := by
  have heq : buj_openSector ξ α = {z | 0 < (z / ξ).im} ∩ {z | (z / (ξ * exp (α * I))).im < 0} := by
    ext z
    rw [buj_b_mem_openSector_iff hα0 hαπ, div_div]
    rfl
  rw [heq]
  exact (convex_halfSpace_gt (buj_b_isLinearMap_im_div ξ) 0).inter
    (convex_halfSpace_lt (buj_b_isLinearMap_im_div _) 0)

/-- A preconnected unbounded set missing `J` lies in the outside `B`. -/
theorem buj_b_subset_outside {D B J S : Set ℂ} (hDo : IsOpen D) (hBo : IsOpen B) (hDB : Disjoint D B)
    (hcover : D ∪ B ∪ J = univ) (hDb : Bornology.IsBounded D) (hS : IsPreconnected S)
    (hSb : ¬ Bornology.IsBounded S) (hSJ : ∀ z ∈ S, z ∉ J) : S ⊆ B := by
  have hsub : S ⊆ D ∪ B := by
    intro z hz
    have h : z ∈ D ∪ B ∪ J := hcover ▸ mem_univ z
    rcases h with h | h
    · exact h
    · exact absurd h (hSJ z hz)
  rcases hS.subset_or_subset hDo hBo hDB hsub with h | h
  · exact absurd (hDb.subset h) hSb
  · exact h

/-- If `J` lies in the closed half-plane `Im (z / ζ) ≥ 0`, the inside lies in the open half-plane. -/
theorem buj_b_halfplane {D B J : Set ℂ} (hDo : IsOpen D) (hBo : IsOpen B) (hDB : Disjoint D B)
    (hcover : D ∪ B ∪ J = univ) (hDb : Bornology.IsBounded D) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hJ : ∀ z ∈ J, 0 ≤ (z / ζ).im) : ∀ z ∈ D, 0 < (z / ζ).im := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  set H : Set ℂ := {z | (z / ζ).im < 0} with hH
  have hHb : ¬ Bornology.IsBounded H := by
    intro hbd
    obtain ⟨R, hR⟩ := hbd.subset_closedBall 0
    have hwH : -(((|R| + 1 : ℝ) : ℂ) * I * ζ) ∈ H := by
      show (-(((|R| + 1 : ℝ) : ℂ) * I * ζ) / ζ).im < 0
      rw [neg_div, mul_div_cancel_right₀ _ hζ0, Complex.neg_im, Complex.mul_I_im, Complex.ofReal_re]
      linarith [abs_nonneg R]
    have h := hR hwH
    rw [mem_closedBall_zero_iff, norm_neg, norm_mul, norm_mul, Complex.norm_I, hζ, mul_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
    linarith [le_abs_self R]
  have hHB : H ⊆ B := buj_b_subset_outside hDo hBo hDB hcover hDb
    (convex_halfSpace_lt (buj_b_isLinearMap_im_div ζ) 0).isPreconnected hHb
    (fun z hz hzJ => absurd hz (not_lt.2 (hJ z hzJ)))
  intro z hz
  have h0 : 0 ≤ (z / ζ).im := by
    by_contra h
    exact Set.disjoint_left.1 hDB hz (hHB (not_le.1 h))
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo z hz
  have hwD : z - ((ε / 2 : ℝ) : ℂ) * I * ζ ∈ D := hball (by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, norm_mul, Complex.norm_I, hζ,
      mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  have hwH : z - ((ε / 2 : ℝ) : ℂ) * I * ζ ∈ H := by
    show ((z - ((ε / 2 : ℝ) : ℂ) * I * ζ) / ζ).im < 0
    rw [sub_div, mul_div_cancel_right₀ _ hζ0, Complex.sub_im, ← h, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  exact Set.disjoint_left.1 hDB hwD (hHB hwH)

/-- If `J` lies in the open unit disc, so does the inside. -/
theorem buj_b_inside_disc {D B J : Set ℂ} (hDo : IsOpen D) (hBo : IsOpen B) (hDB : Disjoint D B)
    (hcover : D ∪ B ∪ J = univ) (hDb : Bornology.IsBounded D) (hJ : ∀ z ∈ J, ‖z‖ < 1) :
    ∀ z ∈ D, ‖z‖ < 1 := by
  intro z hz
  by_contra h
  push Not at h
  set R : Set ℂ := (fun u : ℝ => (u : ℂ) * z) '' Ici 1 with hR
  have hRc : IsPreconnected R :=
    isPreconnected_Ici.image _ ((Complex.continuous_ofReal.mul continuous_const).continuousOn)
  have hRb : ¬ Bornology.IsBounded R := by
    intro hbd
    obtain ⟨M, hM⟩ := hbd.subset_closedBall 0
    have hmem : ((max 1 (|M| + 1) : ℝ) : ℂ) * z ∈ R := ⟨max 1 (|M| + 1), mem_Ici.2 (le_max_left _ _), rfl⟩
    have h1 := hM hmem
    have hm1 : 1 ≤ max 1 (|M| + 1) := le_max_left _ _
    have hm2 : |M| + 1 ≤ max 1 (|M| + 1) := le_max_right _ _
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)] at h1
    nlinarith [le_abs_self M, mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ max 1 (|M| + 1))]
  have hRJ : ∀ w ∈ R, w ∉ J := by
    rintro _ ⟨u, hu, rfl⟩ hJw
    have h1 := hJ _ hJw
    have hu1 : (1 : ℝ) ≤ u := hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
    nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h)]
  have hRB := buj_b_subset_outside hDo hBo hDB hcover hDb hRc hRb hRJ
  have hzR : z ∈ R := ⟨1, mem_Ici.2 le_rfl, by simp⟩
  exact Set.disjoint_left.1 hDB hz (hRB hzR)

/-- A preconnected set `S` missing `J`, such that the inside lies in `S ∪ {‖z‖ ≥ r₀}`, lies in the inside
(because `0 ∈ J` is a frontier point of the inside). -/
theorem buj_b_sectorBall_subset {D B J S : Set ℂ} (hDo : IsOpen D) (hBo : IsOpen B) (hDB : Disjoint D B)
    (hcover : D ∪ B ∪ J = univ) (hDfr : frontier D = J) (hJ0 : (0 : ℂ) ∈ J) (hS : IsPreconnected S)
    (hSJ : ∀ z ∈ S, z ∉ J) {r₀ : ℝ} (hr₀ : 0 < r₀) (hDS : ∀ z ∈ D, z ∈ S ∨ r₀ ≤ ‖z‖) : S ⊆ D := by
  have hsub : S ⊆ D ∪ B := by
    intro z hz
    have h : z ∈ D ∪ B ∪ J := hcover ▸ mem_univ z
    rcases h with h | h
    · exact h
    · exact absurd h (hSJ z hz)
  rcases hS.subset_or_subset hDo hBo hDB hsub with h | h
  · exact h
  exfalso
  have hD : D ⊆ {z | r₀ ≤ ‖z‖} := fun z hz =>
    (hDS z hz).resolve_left (fun hzS => Set.disjoint_left.1 hDB hz (h hzS))
  have hcl : closure D ⊆ {z | r₀ ≤ ‖z‖} := closure_minimal hD (isClosed_le continuous_const continuous_norm)
  have h0 : (0 : ℂ) ∈ closure D := frontier_subset_closure (hDfr ▸ hJ0)
  have h1 : r₀ ≤ ‖(0 : ℂ)‖ := hcl h0
  rw [norm_zero] at h1
  linarith

/-- **The Riemann map of a sector cut.**

Setting: a sector cut `τ` at height `r₀`, and a point `z₀` of the open sector with `‖z₀‖ < r₀`.

Claim: there is `ρ`, holomorphic in `Δ` and injective and continuous on `Δ̄`, with:
* `ρ 0 = z₀` and `ρ 1 = 0` (the vertex);
* `ρ(Δ)` in the open sector and `ρ(Δ̄) ⊆ Δ`;
* `ρ(∂Δ)` equal to the cut curve, with `0 ≤ arg(ρ/ξ) ≤ α` on `∂Δ`;
* `‖ρ'(0)‖ ≥ δ` whenever `B(z₀, δ)` lies in the open sector ∩ `B(0, r₀)`.

*Truth:* TRUE.
1. The cut curve `J` is a Jordan curve. The two sides meet only at `0` (`0 < α < π`); `τ` is an arc whose interior
   lies in the open sector, off both sides; its endpoints are `aξ`, `bξe^{iα}`.
2. Let `D` be the bounded component of `ℂ ∖ J`. By `buj_inside_isJordanDomain`, `D` is an `IsJordanDomain` with
   `frontier D = J`.
3. `D` ⊆ open sector ∩ `Δ`: the complement of the compact convex set (closed sector ∩ `B̄(0, max ‖J‖)`) is
   connected, unbounded and misses `J`, so it lies in the unbounded component. Hence `D` lies in the interior of
   that convex set.
4. Open sector ∩ `B(0, r₀)` ⊆ `D`: this set is connected and misses `J` (`τ` stays in `‖z‖ > r₀`). If it lay in the
   unbounded component, then `D ⊆ {‖z‖ ≥ r₀}`, contradicting `0 ∈ J = frontier D`.

*Route:*
1. `s13x_th_exists_disc_uniformizer` gives a conformal `D → Δ` with a homeomorphic extension.
2. Compose with the disc automorphism sending `z₀ ↦ 0` (`Lemmas/DiscAutomorphism`) and a rotation sending the
   preimage of `0` to `1`. Then invert with `uq_isHomeoExtension_invFunOn` (S13) and
   `differentiableOn_invFunOn_of_injOn` (`RiemannMapping`) to get `ρ` with the stated boundary behaviour.
   (S35's `m35_isHomeoExtension_invFunOn` is downstream and not available here.)
3. Schwarz (`Complex.norm_deriv_le_div_of_mapsTo_ball`) for `ρ⁻¹ ∘ (z₀ + δ ·)` gives `‖(ρ⁻¹)'(z₀)‖ ≤ 1/δ`, hence
   `‖ρ'(0)‖ ≥ δ`. -/
theorem buj_sector_uniformizer {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) {z₀ : ℂ} (hz₀ : z₀ ∈ buj_openSector ξ α) (hz₀r : ‖z₀‖ < r₀) :
    ∃ ρ : ℂ → ℂ, DiffContOnCl ℂ ρ (ball 0 1) ∧ InjOn ρ (closedBall 0 1) ∧ ρ 0 = z₀ ∧ ρ 1 = 0 ∧
      MapsTo ρ (ball 0 1) (buj_openSector ξ α) ∧ MapsTo ρ (closedBall 0 1) unitDisc ∧
      ρ '' sphere 0 1 = buj_cutCurve ξ α a b τ s t ∧
      (∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ arg (ρ z / ξ) ∧ arg (ρ z / ξ) ≤ α) ∧
      ∀ δ : ℝ, 0 < δ → ball z₀ δ ⊆ buj_openSector ξ α ∩ ball 0 r₀ → δ ≤ ‖deriv ρ 0‖ := by
  have hc := hcut
  obtain ⟨⟨hα0, hαπ, hξ, hr₀, -, -, hst⟩, -⟩ := hc
  obtain ⟨D, hDJ, hDb, hDfr, hDJd, B, hBo, -, -, hDB, -, hcover⟩ :=
    buj_inside_isJordanDomain (buj_b_isJordanCurve hcut)
  have hDo : IsOpen D := hDJ.1
  have hDc : IsConnected D := hDJ.2.1
  have hJp : ∀ z ∈ buj_cutCurve ξ α a b τ s t, 0 ≤ (z / ξ).im ∧ (z / ξ / exp (α * I)).im ≤ 0 ∧ ‖z‖ < 1 ∧
      (z ∈ buj_openSector ξ α → r₀ < ‖z‖) := fun z hz => buj_b_cutCurve_props hcut hz
  -- the inside lies in the sector and in the disc
  have hξe : ‖-(ξ * exp (α * I))‖ = 1 := by
    rw [norm_neg, norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hD1 : ∀ z ∈ D, 0 < (z / ξ).im :=
    buj_b_halfplane hDo hBo hDB hcover hDb hξ (fun z hz => (hJp z hz).1)
  have hD2 : ∀ z ∈ D, 0 < (z / -(ξ * exp (α * I))).im :=
    buj_b_halfplane hDo hBo hDB hcover hDb hξe (fun z hz => by
      rw [div_neg, Complex.neg_im, ← div_div]
      linarith [(hJp z hz).2.1])
  have hDO : ∀ z ∈ D, z ∈ buj_openSector ξ α := fun z hz => by
    refine (buj_b_mem_openSector_iff hα0 hαπ z).2 ⟨hD1 z hz, ?_⟩
    have h := hD2 z hz
    rw [div_neg, Complex.neg_im, ← div_div] at h
    linarith
  have hDΔ : ∀ z ∈ D, ‖z‖ < 1 := buj_b_inside_disc hDo hBo hDB hcover hDb (fun z hz => (hJp z hz).2.2.1)
  have hJ0 : (0 : ℂ) ∈ buj_cutCurve ξ α a b τ s t := by
    have hc2 := hcut
    obtain ⟨⟨-, -, -, -, ha, hb, -⟩, -⟩ := hc2
    rw [← buj_b_loop_image hcut]
    exact ⟨0, ⟨le_rfl, by linarith⟩, buj_b_loop_zero hcut⟩
  have hSD : buj_openSector ξ α ∩ ball 0 r₀ ⊆ D := by
    refine buj_b_sectorBall_subset hDo hBo hDB hcover hDfr hJ0
      ((buj_b_openSector_convex hα0 hαπ).inter (convex_ball 0 r₀)).isPreconnected ?_ hr₀ ?_
    · rintro z ⟨hzO, hzr⟩ hzJ
      have h := (hJp z hzJ).2.2.2 hzO
      rw [mem_ball_zero_iff] at hzr
      linarith
    · intro z hz
      by_cases h : ‖z‖ < r₀
      · exact Or.inl ⟨hDO z hz, mem_ball_zero_iff.2 h⟩
      · exact Or.inr (not_lt.1 h)
  have hz₀D : z₀ ∈ D := hSD ⟨hz₀, mem_ball_zero_iff.2 hz₀r⟩
  -- the Riemann map `f : Δ → D` with `f 0 = z₀`
  have hDne : Dᶜ.Nonempty := ⟨0, fun h0 => Set.disjoint_left.1 hDJd h0 hJ0⟩
  have hH := hasHolomorphicSqrt_of_isConnected_compl hDo hDc
    (isConnected_compl_toExt_of_isJordanDomain hDJ hDb)
  obtain ⟨g, hg, hgb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hDo hDc hDne hH hz₀D
  obtain ⟨hfd, hfb⟩ := RMT.invFunOn_riemannMap hDo hg.diff hg.injOn hgb
  set f : ℂ → ℂ := Function.invFunOn g D with hfdef
  have hfconf : IsConformalOnto f unitDisc D := ⟨hfd, hfb.injOn, hfb.image_eq⟩
  have hf0 : f 0 = z₀ := by
    have h := hg.injOn.leftInvOn_invFunOn hz₀D
    rw [hg.center] at h
    exact h
  have hgf : ∀ w ∈ unitDisc, g (f w) = w := fun w hw => Function.invFunOn_eq (hgb.surjOn hw)
  -- the homeomorphic extension `G` of `f` to the closed disc
  have hJ' : IsJordanCurve (toExt (frontier D)) := by
    rw [hDfr]
    exact buj_b_isJordanCurve hcut
  obtain ⟨G, hGc, hGf, hGs, hGimg⟩ := exists_continuousOn_extension_of_isJordanCurve_frontier hDb hfconf hJ'
  have hGi := injOn_extension_of_isJordanCurve_frontier hDb hfconf hJ' hGc hGf hGs
  have hGsph : G '' sphere 0 1 = buj_cutCurve ξ α a b τ s t := by
    refine subset_antisymm (hDfr ▸ hGs) ?_
    intro w hw
    have hwcl : w ∈ closure D := frontier_subset_closure (hDfr.symm ▸ hw)
    rw [← hGimg] at hwcl
    obtain ⟨z, hz, rfl⟩ := hwcl
    refine ⟨z, ?_, rfl⟩
    rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with h | h
    · exfalso
      have hzD : G z ∈ D := by
        rw [hGf (mem_ball_zero_iff.2 h)]
        exact hfconf.mapsTo (mem_ball_zero_iff.2 h)
      exact Set.disjoint_left.1 hDJd hzD hw
    · exact mem_sphere_zero_iff_norm.2 h
  have h0img : (0 : ℂ) ∈ G '' sphere (0 : ℂ) 1 := by
    rw [hGsph]
    exact hJ0
  obtain ⟨ζ₀, hζ₀, hGζ₀⟩ := h0img
  have hζ₀n : ‖ζ₀‖ = 1 := mem_sphere_zero_iff_norm.1 hζ₀
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    simp at hζ₀n
  have hmapB : MapsTo (fun z => ζ₀ * z) (ball 0 1) unitDisc := fun z hz => by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hζ₀n, one_mul]
    exact mem_ball_zero_iff.1 hz
  have hmapCl : MapsTo (fun z => ζ₀ * z) (closedBall 0 1) (closedBall 0 1) := fun z hz => by
    rw [mem_closedBall_zero_iff, norm_mul, hζ₀n, one_mul]
    exact mem_closedBall_zero_iff.1 hz
  have hmapS : MapsTo (fun z => ζ₀ * z) (sphere 0 1) (sphere 0 1) := fun z hz => by
    rw [mem_sphere_zero_iff_norm, norm_mul, hζ₀n, one_mul]
    exact mem_sphere_zero_iff_norm.1 hz
  have hρimg : (fun z => G (ζ₀ * z)) '' sphere 0 1 = buj_cutCurve ξ α a b τ s t := by
    rw [← hGsph]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ζ₀ * z, hmapS hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨ζ₀⁻¹ * z, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, hζ₀n, inv_one, one_mul]
        exact mem_sphere_zero_iff_norm.1 hz
      · show G (ζ₀ * (ζ₀⁻¹ * z)) = G z
        rw [← mul_assoc, mul_inv_cancel₀ hζ₀0, one_mul]
  refine ⟨fun z => G (ζ₀ * z), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hρimg, ?_, ?_⟩
  · refine (hfd.comp (differentiableOn_id.const_mul ζ₀) hmapB).congr fun z hz => ?_
    exact hGf (hmapB hz)
  · rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hGc.comp (continuous_const.mul continuous_id).continuousOn hmapCl
  · intro z hz w hw hzw
    exact mul_left_cancel₀ hζ₀0 (hGi (hmapCl hz) (hmapCl hw) hzw)
  · show G (ζ₀ * 0) = z₀
    rw [mul_zero, hGf (mem_ball_self one_pos), hf0]
  · show G (ζ₀ * 1) = 0
    rw [mul_one, hGζ₀]
  · intro z hz
    show G (ζ₀ * z) ∈ buj_openSector ξ α
    rw [hGf (hmapB hz)]
    exact hDO _ (hfconf.mapsTo (hmapB hz))
  · intro z hz
    have hmem : G (ζ₀ * z) ∈ closure D := hGimg ▸ mem_image_of_mem G (hmapCl hz)
    rw [closure_eq_interior_union_frontier, hDo.interior_eq, hDfr] at hmem
    show G (ζ₀ * z) ∈ unitDisc
    rw [unitDisc, mem_ball_zero_iff]
    rcases hmem with h | h
    · exact hDΔ _ h
    · exact (hJp _ h).2.2.1
  · intro z hz
    have hmem : G (ζ₀ * z) ∈ buj_cutCurve ξ α a b τ s t := hρimg ▸ mem_image_of_mem _ hz
    exact buj_b_arg_of_closed hα0 (hJp _ hmem).1 (hJp _ hmem).2.1
  · intro δ hδ hball
    have hballD : ball z₀ δ ⊆ D := hball.trans hSD
    have hgd : DifferentiableOn ℂ g (ball z₀ δ) := hg.diff.mono hballD
    have hgmap : MapsTo g (ball z₀ δ) (closedBall (g z₀) 1) := fun w hw => by
      rw [hg.center, mem_closedBall_zero_iff]
      exact (mem_ball_zero_iff.1 (hg.mapsTo (hballD hw))).le
    have hsch := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgmap hδ
    rw [le_div_iff₀ hδ] at hsch
    have hfda : DifferentiableAt ℂ f 0 := hfd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    have hgda : DifferentiableAt ℂ g (f 0) := by
      rw [hf0]
      exact hg.diff.differentiableAt (hDo.mem_nhds hz₀D)
    have hcomp : deriv (g ∘ f) 0 = deriv g (f 0) * deriv f 0 := deriv_comp (0 : ℂ) hgda hfda
    have hid : deriv (g ∘ f) 0 = 1 := by
      have heq : g ∘ f =ᶠ[𝓝 0] id := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
        exact hgf w hw
      rw [heq.deriv_eq, deriv_id]
    have hprod : deriv g z₀ * deriv f 0 = 1 := by
      rw [← hf0, ← hcomp, hid]
    have hρd : deriv (fun z => G (ζ₀ * z)) 0 = deriv f 0 * ζ₀ := by
      have heq : (fun z => G (ζ₀ * z)) =ᶠ[𝓝 0] (fun z => f (ζ₀ * z)) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
        exact hGf (hmapB hw)
      rw [heq.deriv_eq]
      have h1 : HasDerivAt (fun z => ζ₀ * z) ζ₀ 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul ζ₀
      have h2 : HasDerivAt f (deriv f 0) (ζ₀ * 0) := by
        rw [mul_zero]
        exact hfda.hasDerivAt
      exact (h2.comp 0 h1).deriv
    rw [hρd, norm_mul, hζ₀n, mul_one]
    have hn : ‖deriv g z₀‖ * ‖deriv f 0‖ = 1 := by rw [← norm_mul, hprod, norm_one]
    have hpos : 0 ≤ ‖deriv f 0‖ := norm_nonneg _
    calc δ = δ * (‖deriv g z₀‖ * ‖deriv f 0‖) := by rw [hn, mul_one]
      _ = (‖deriv g z₀‖ * δ) * ‖deriv f 0‖ := by ring
      _ ≤ 1 * ‖deriv f 0‖ := mul_le_mul_of_nonneg_right hsch hpos
      _ = ‖deriv f 0‖ := one_mul _

/-- The arclength density of `buj_b_loop`: `1` on the sides and `‖τ'‖` on the cut. -/
def buj_b_dens (a : ℝ) (τ : ℝ → ℂ) (s t x : ℝ) : ℝ≥0∞ :=
  if x ≤ a then 1 else if x ≤ a + (t - s) then ‖deriv τ (x + (s - a))‖ₑ else 1

/-- The density on the first side. -/
theorem buj_b_dens_left {a s t x : ℝ} {τ : ℝ → ℂ} (hx : x ≤ a) : buj_b_dens a τ s t x = 1 := ite_eq_left hx

/-- The density on the cut. -/
theorem buj_b_dens_mid {a s t x : ℝ} {τ : ℝ → ℂ} (hx : x ∈ Ioc a (a + (t - s))) :
    buj_b_dens a τ s t x = ‖deriv τ (x + (s - a))‖ₑ := by
  unfold buj_b_dens
  rw [ite_eq_right (not_le.2 hx.1), ite_eq_left hx.2]

/-- The density on the second side. -/
theorem buj_b_dens_right {a s t x : ℝ} {τ : ℝ → ℂ} (hst : s ≤ t) (hx : a + (t - s) < x) :
    buj_b_dens a τ s t x = 1 := by
  unfold buj_b_dens
  rw [ite_eq_right (by intro h; linarith), ite_eq_right (not_le.2 hx)]

/-- The density is measurable. -/
theorem buj_b_dens_measurable (a s t : ℝ) (τ : ℝ → ℂ) : Measurable (buj_b_dens a τ s t) := by
  unfold buj_b_dens
  refine Measurable.ite measurableSet_Iic measurable_const (Measurable.ite measurableSet_Iic ?_ measurable_const)
  exact (measurable_deriv τ).comp (measurable_id.add_const _) |>.enorm

/-- The loop lies in the open sector exactly on the cut `(a, a + (t - s))`. -/
theorem buj_b_loop_mem_openSector_iff {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) {x : ℝ} :
    buj_b_loop ξ α a b τ s t x ∈ buj_openSector ξ α ↔ x ∈ Ioo a (a + (t - s)) := by
  have hc := hcut
  obtain ⟨⟨hα0, hαπ, hξ, -, -, -, -⟩, -, hτO, -⟩ := hc
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp at hξ
  constructor
  · intro h
    by_contra hn
    rcases le_or_gt x a with hxa | hxa
    · rw [buj_b_loop_left hxa] at h
      exact buj_b_side1_notMem hα0 hαπ hξ0 x h
    · have hxc : a + (t - s) ≤ x := by
        by_contra h'
        exact hn ⟨hxa, not_le.1 h'⟩
      rw [buj_b_loop_right hcut hxc] at h
      exact buj_b_side2_notMem hα0 hαπ hξ0 _ h
  · intro h
    rw [buj_b_loop_mid hcut ⟨h.1.le, h.2.le⟩]
    exact hτO _ ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Chaining increment bounds across a junction point `q`. -/
theorem buj_b_chain {h : ℝ → ℂ} {d : ℝ → ℝ≥0∞} {p q r : ℝ}
    (h1 : ∀ x y, p ≤ x → x ≤ y → y ≤ q → edist (h x) (h y) ≤ ∫⁻ u in Ioo x y, d u)
    (h2 : ∀ x y, q ≤ x → x ≤ y → y ≤ r → edist (h x) (h y) ≤ ∫⁻ u in Ioo x y, d u) :
    ∀ x y, p ≤ x → x ≤ y → y ≤ r → edist (h x) (h y) ≤ ∫⁻ u in Ioo x y, d u := by
  intro x y hx hxy hy
  by_cases hyq : y ≤ q
  · exact h1 x y hx hxy hyq
  by_cases hqx : q ≤ x
  · exact h2 x y hqx hxy hy
  push Not at hyq hqx
  have hdisj : Disjoint (Ioo x q) (Ioo q y) :=
    Set.disjoint_left.2 fun u hu1 hu2 => lt_irrefl u (hu1.2.trans hu2.1)
  calc edist (h x) (h y) ≤ edist (h x) (h q) + edist (h q) (h y) := edist_triangle _ _ _
    _ ≤ (∫⁻ u in Ioo x q, d u) + ∫⁻ u in Ioo q y, d u :=
        add_le_add (h1 x q hx hqx.le le_rfl) (h2 q y le_rfl hyq.le hy)
    _ = ∫⁻ u in Ioo x q ∪ Ioo q y, d u := (lintegral_union measurableSet_Ioo hdisj).symm
    _ ≤ ∫⁻ u in Ioo x y, d u :=
        lintegral_mono_set (union_subset (Ioo_subset_Ioo_right hyq.le) (Ioo_subset_Ioo_left hqx.le))

/-- The fundamental theorem of calculus bound for an absolutely continuous `τ`. -/
theorem buj_b_edist_le_of_deriv {τ : ℝ → ℂ} {s t : ℝ} (hτc : ContinuousOn τ (Icc s t))
    (hτd : ∀ u ∈ Ioo s t, DifferentiableAt ℝ τ u) (hτint : IntervalIntegrable (deriv τ) volume s t)
    {x y : ℝ} (hx : s ≤ x) (hxy : x ≤ y) (hy : y ≤ t) :
    edist (τ x) (τ y) ≤ ∫⁻ u in Ioo x y, ‖deriv τ u‖ₑ := by
  have hint : IntervalIntegrable (deriv τ) volume x y := hτint.mono_set (by
    rw [uIcc_of_le hxy, uIcc_of_le (hx.trans (hxy.trans hy))]
    exact Icc_subset_Icc hx hy)
  have hftc : ∫ u in x..y, deriv τ u = τ y - τ x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy (hτc.mono (Icc_subset_Icc hx hy))
      (fun u hu => (hτd u ⟨hx.trans_lt hu.1, hu.2.trans_le hy⟩).hasDerivAt) hint
  rw [edist_comm, edist_eq_enorm_sub, ← hftc, intervalIntegral.integral_of_le hxy]
  calc ‖∫ u in Ioc x y, deriv τ u‖ₑ ≤ ∫⁻ u in Ioc x y, ‖deriv τ u‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ u in Ioo x y, ‖deriv τ u‖ₑ := setLIntegral_congr Ioo_ae_eq_Ioc.symm

/-- Translation of a set lintegral over an open interval. -/
theorem buj_b_lintegral_Ioo_add (f : ℝ → ℝ≥0∞) (p q d : ℝ) :
    ∫⁻ x in Ioo p q, f (x + d) = ∫⁻ y in Ioo (p + d) (q + d), f y := by
  rw [(measurePreserving_add_right volume d).setLIntegral_comp_emb (measurableEmbedding_addRight d) f
    (Ioo p q), image_add_const_Ioo]

/-- Reflection of a set lintegral over an open interval. -/
theorem buj_b_lintegral_Ioo_sub (f : ℝ → ℝ≥0∞) (p q L : ℝ) :
    ∫⁻ x in Ioo p q, f (L - x) = ∫⁻ y in Ioo (L - q) (L - p), f y := by
  rw [(Measure.measurePreserving_sub_left volume L).setLIntegral_comp_emb
    (MeasurableEquiv.subLeft L).measurableEmbedding f (Ioo p q)]
  exact congrArg (fun S => ∫⁻ y in S, f y) (image_const_sub_Ioo L p q)

/-- `edist (x v) (y v) = y - x` for a unit vector `v` and `x ≤ y`. -/
theorem buj_b_edist_side {v : ℂ} (hv : ‖v‖ = 1) {x y : ℝ} (hxy : x ≤ y) :
    edist ((x : ℂ) * v) ((y : ℂ) * v) = ENNReal.ofReal (y - x) := by
  rw [edist_dist, dist_eq_norm, ← sub_mul, norm_mul, hv, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]

/-- The increments of the loop are bounded by the integral of its density. -/
theorem buj_b_loop_edist_le {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ} (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    ∀ x y, 0 ≤ x → x ≤ y → y ≤ a + (t - s) + b →
      edist (buj_b_loop ξ α a b τ s t x) (buj_b_loop ξ α a b τ s t y) ≤
        ∫⁻ u in Ioo x y, buj_b_dens a τ s t u := by
  have hc := hcut
  obtain ⟨⟨-, -, hξ, -, -, -, hst⟩, ⟨hτc, -⟩, -, -, hτd, hτint⟩ := hc
  have hξe : ‖ξ * exp (α * I)‖ = 1 := by rw [norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, mul_one]
  have P1 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ a → edist (buj_b_loop ξ α a b τ s t x) (buj_b_loop ξ α a b τ s t y) ≤
      ∫⁻ u in Ioo x y, buj_b_dens a τ s t u := by
    intro x y _ hxy hy
    rw [buj_b_loop_left (hxy.trans hy), buj_b_loop_left hy, buj_b_edist_side hξ hxy,
      setLIntegral_congr_fun measurableSet_Ioo (fun u hu => buj_b_dens_left (hu.2.le.trans hy)),
      setLIntegral_one, Real.volume_Ioo]
  have P2 : ∀ x y, a ≤ x → x ≤ y → y ≤ a + (t - s) →
      edist (buj_b_loop ξ α a b τ s t x) (buj_b_loop ξ α a b τ s t y) ≤
        ∫⁻ u in Ioo x y, buj_b_dens a τ s t u := by
    intro x y hx hxy hy
    rw [buj_b_loop_mid hcut ⟨hx, hxy.trans hy⟩, buj_b_loop_mid hcut ⟨hx.trans hxy, hy⟩,
      setLIntegral_congr_fun measurableSet_Ioo
        (fun u hu => buj_b_dens_mid ⟨hx.trans_lt hu.1, hu.2.le.trans hy⟩),
      buj_b_lintegral_Ioo_add (fun u => ‖deriv τ u‖ₑ)]
    exact buj_b_edist_le_of_deriv hτc hτd hτint (by linarith) (by linarith) (by linarith)
  have P3 : ∀ x y, a + (t - s) ≤ x → x ≤ y → y ≤ a + (t - s) + b →
      edist (buj_b_loop ξ α a b τ s t x) (buj_b_loop ξ α a b τ s t y) ≤
        ∫⁻ u in Ioo x y, buj_b_dens a τ s t u := by
    intro x y hx hxy hy
    rw [buj_b_loop_right hcut hx, buj_b_loop_right hcut (hx.trans hxy), edist_comm,
      buj_b_edist_side hξe (by linarith),
      setLIntegral_congr_fun measurableSet_Ioo (fun u hu => buj_b_dens_right hst.le (hx.trans_lt hu.1)),
      setLIntegral_one, Real.volume_Ioo]
    apply le_of_eq
    congr 1
    ring
  exact buj_b_chain (buj_b_chain P1 P2) P3

/-- The weighted loop integral over the cut part is the weighted integral over `τ`. -/
theorem buj_b_lintegral_loop_cut {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) (F : ℂ → ℝ≥0∞) :
    ∫⁻ x in Ioo a (a + (t - s)), F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x =
      ∫⁻ x in Ioo s t, F (τ x) * ‖deriv τ x‖ₑ := by
  rw [setLIntegral_congr_fun measurableSet_Ioo
      (g := fun x => F (τ (x + (s - a))) * ‖deriv τ (x + (s - a))‖ₑ)
      (fun x hx => by rw [buj_b_loop_mid hcut ⟨hx.1.le, hx.2.le⟩, buj_b_dens_mid ⟨hx.1, hx.2.le⟩]),
    buj_b_lintegral_Ioo_add (fun y => F (τ y) * ‖deriv τ y‖ₑ),
    show a + (s - a) = s by ring, show a + (t - s) + (s - a) = t by ring]

/-- The weighted loop integral splits into the cut and the two sides. -/
theorem buj_b_lintegral_loop_le {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) (F : ℂ → ℝ≥0∞) :
    ∫⁻ x in Ioo 0 (a + (t - s) + b), F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x ≤
      (∫⁻ x in Ioo s t, F (τ x) * ‖deriv τ x‖ₑ) + (∫⁻ r in Ioo 0 a, F ((r : ℂ) * ξ)) +
        ∫⁻ r in Ioo 0 b, F ((r : ℂ) * (ξ * exp (α * I))) := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, -, -, hst⟩, -⟩ := hc
  set G : ℝ → ℝ≥0∞ := fun x => F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x with hG
  have h1 : ∫⁻ x in Ioo 0 a, G x = ∫⁻ r in Ioo 0 a, F ((r : ℂ) * ξ) :=
    setLIntegral_congr_fun measurableSet_Ioo fun x hx => by
      simp only [hG, buj_b_loop_left hx.2.le, buj_b_dens_left hx.2.le, mul_one]
  have h2 : ∫⁻ x in Icc a (a + (t - s)), G x = ∫⁻ x in Ioo s t, F (τ x) * ‖deriv τ x‖ₑ := by
    rw [setLIntegral_congr Ioo_ae_eq_Icc.symm]
    exact buj_b_lintegral_loop_cut hcut F
  have h3 : ∫⁻ x in Ioo (a + (t - s)) (a + (t - s) + b), G x =
      ∫⁻ r in Ioo 0 b, F ((r : ℂ) * (ξ * exp (α * I))) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo
        (g := fun x => F (((a + (t - s) + b - x : ℝ) : ℂ) * (ξ * exp (α * I))))
        (fun x hx => by
          simp only [hG, buj_b_loop_right hcut hx.1.le, buj_b_dens_right hst.le hx.1, mul_one]),
      buj_b_lintegral_Ioo_sub (fun r => F ((r : ℂ) * (ξ * exp (α * I)))),
      show a + (t - s) + b - (a + (t - s) + b) = 0 by ring, show a + (t - s) + b - (a + (t - s)) = b by ring]
  have hsub : Ioo 0 (a + (t - s) + b) ⊆
      (Ioo 0 a ∪ Icc a (a + (t - s))) ∪ Ioo (a + (t - s)) (a + (t - s) + b) := by
    intro x hx
    by_cases hxa : x < a
    · exact Or.inl (Or.inl ⟨hx.1, hxa⟩)
    by_cases hxc : x ≤ a + (t - s)
    · exact Or.inl (Or.inr ⟨not_lt.1 hxa, hxc⟩)
    · exact Or.inr ⟨not_le.1 hxc, hx.2⟩
  calc ∫⁻ x in Ioo 0 (a + (t - s) + b), G x
      ≤ ∫⁻ x in (Ioo 0 a ∪ Icc a (a + (t - s))) ∪ Ioo (a + (t - s)) (a + (t - s) + b), G x :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ x in Ioo 0 a ∪ Icc a (a + (t - s)), G x) +
          ∫⁻ x in Ioo (a + (t - s)) (a + (t - s) + b), G x := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ x in Ioo 0 a, G x) + ∫⁻ x in Icc a (a + (t - s)), G x) +
          ∫⁻ x in Ioo (a + (t - s)) (a + (t - s) + b), G x :=
        add_le_add_left (lintegral_union_le _ _ _) _
    _ = _ := by
        rw [h1, h2, h3]
        ring

/-- The part of the weighted loop integral inside the open sector is at most the weighted integral over
`τ`. -/
theorem buj_b_lintegral_loop_sector_le {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) (F : ℂ → ℝ≥0∞) :
    ∫⁻ x in Ioo 0 (a + (t - s) + b),
        (buj_openSector ξ α).indicator F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x ≤
      ∫⁻ x in Ioo s t, F (τ x) * ‖deriv τ x‖ₑ := by
  set G : ℝ → ℝ≥0∞ := fun x => F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x with hG
  have heq : ∀ x, (buj_openSector ξ α).indicator F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x =
      (Ioo a (a + (t - s))).indicator G x := by
    intro x
    by_cases hx : x ∈ Ioo a (a + (t - s))
    · rw [indicator_of_mem ((buj_b_loop_mem_openSector_iff hcut).2 hx), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h => hx ((buj_b_loop_mem_openSector_iff hcut).1 h)),
        indicator_of_notMem hx, zero_mul]
  calc ∫⁻ x in Ioo 0 (a + (t - s) + b),
        (buj_openSector ξ α).indicator F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x
      = ∫⁻ x in Ioo 0 (a + (t - s) + b), (Ioo a (a + (t - s))).indicator G x := lintegral_congr heq
    _ ≤ ∫⁻ x, (Ioo a (a + (t - s))).indicator G x := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x in Ioo a (a + (t - s)), G x := lintegral_indicator measurableSet_Ioo _
    _ = _ := buj_b_lintegral_loop_cut hcut F

/-- The loop density has a finite integral. -/
theorem buj_b_lintegral_dens_lt_top {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) :
    ∫⁻ x in Ioo 0 (a + (t - s) + b), buj_b_dens a τ s t x < ⊤ := by
  have hc := hcut
  obtain ⟨⟨-, -, -, -, -, -, hst⟩, -, -, -, -, hτint⟩ := hc
  have h := buj_b_lintegral_loop_le hcut (fun _ => 1)
  simp only [one_mul] at h
  refine h.trans_lt ?_
  have hτ : ∫⁻ x in Ioo s t, ‖deriv τ x‖ₑ < ⊤ :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hst.le).1 hτint).2
  rw [setLIntegral_one, setLIntegral_one, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hτ, ENNReal.ofReal_lt_top⟩, ENNReal.ofReal_lt_top⟩

/-- The open sector is measurable. -/
theorem buj_b_openSector_measurableSet {ξ : ℂ} {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) :
    MeasurableSet (buj_openSector ξ α) := by
  have heq : buj_openSector ξ α = {z | 0 < (z / ξ).im} ∩ {z | (z / ξ / exp (α * I)).im < 0} := by
    ext z
    exact buj_b_mem_openSector_iff hα0 hαπ z
  rw [heq]
  refine MeasurableSet.inter (measurableSet_lt measurable_const ?_) (measurableSet_lt ?_ measurable_const)
  · exact (Complex.continuous_im.comp (continuous_id.div_const ξ)).measurable
  · exact (Complex.continuous_im.comp ((continuous_id.div_const ξ).div_const _)).measurable

/-- A function `κ` with values in a compact `K` and `γ ∘ κ = bf`, where `γ` is continuous on `K` and the
`γ`-preimages in `K` of the values of `bf` are unique, is continuous. -/
theorem buj_b_continuousOn_of_unique {κ : ℝ → ℝ} {γ bf : ℝ → ℂ} {K S : Set ℝ} (hK : IsCompact K)
    (hγ : ContinuousOn γ K) (hbf : ContinuousOn bf S) (hκK : ∀ θ ∈ S, κ θ ∈ K)
    (hκγ : ∀ θ ∈ S, γ (κ θ) = bf θ) (huniq : ∀ θ ∈ S, ∀ y ∈ K, γ y = bf θ → y = κ θ) :
    ContinuousOn κ S := by
  intro θ₀ hθ₀
  have hev : ∀ᶠ θ in 𝓝[S] θ₀, κ θ ∈ K := Filter.eventually_of_mem self_mem_nhdsWithin hκK
  refine hK.tendsto_nhds_of_unique_mapClusterPt hev fun y hyK hy => huniq θ₀ hθ₀ y hyK ?_
  have hmapK : map κ (𝓝[S] θ₀) ≤ 𝓟 K := by
    rw [le_principal_iff]
    exact hev
  have h1 : MapClusterPt (γ y) (𝓝[S] θ₀) (γ ∘ κ) :=
    hy.tendsto_comp' ((hγ y hyK).tendsto.mono_left (inf_le_inf_left _ hmapK))
  have h2 : Tendsto (γ ∘ κ) (𝓝[S] θ₀) (𝓝 (bf θ₀)) :=
    (hbf θ₀ hθ₀).tendsto.congr'
      (Filter.eventually_of_mem self_mem_nhdsWithin fun θ hθ => (hκγ θ hθ).symm)
  exact eq_of_nhds_neBot (ClusterPt.mono h1 h2)

/-- A continuous injective function on an open interval is strictly monotone or strictly antitone. -/
theorem buj_b_strictMonoOn_Ioo {f : ℝ → ℝ} {p q : ℝ} (hf : ContinuousOn f (Ioo p q))
    (hfi : InjOn f (Ioo p q)) : StrictMonoOn f (Ioo p q) ∨ StrictAntiOn f (Ioo p q) := by
  rcases le_or_gt q p with hpq | hpq
  · left
    intro x hx
    exact absurd (hx.1.trans hx.2) (not_lt.2 hpq)
  have key : ∀ m M, p < m → M < q → m ≤ M → StrictMonoOn f (Icc m M) ∨ StrictAntiOn f (Icc m M) :=
    fun m M hm hM hmM => ContinuousOn.strictMonoOn_of_injOn_Icc' hmM (hf.mono (Icc_subset_Ioo hm hM))
      (hfi.mono (Icc_subset_Ioo hm hM))
  have h12 : (2 * p + q) / 3 < (p + 2 * q) / 3 := by linarith
  have hp1 : p < (2 * p + q) / 3 := by linarith
  have h2q : (p + 2 * q) / 3 < q := by linarith
  have hext : ∀ x ∈ Ioo p q, ∀ y ∈ Ioo p q, x < y →
      (2 * p + q) / 3 ∈ Icc (min x ((2 * p + q) / 3)) (max y ((p + 2 * q) / 3)) ∧
      (p + 2 * q) / 3 ∈ Icc (min x ((2 * p + q) / 3)) (max y ((p + 2 * q) / 3)) ∧
      x ∈ Icc (min x ((2 * p + q) / 3)) (max y ((p + 2 * q) / 3)) ∧
      y ∈ Icc (min x ((2 * p + q) / 3)) (max y ((p + 2 * q) / 3)) ∧
      p < min x ((2 * p + q) / 3) ∧ max y ((p + 2 * q) / 3) < q ∧
      min x ((2 * p + q) / 3) ≤ max y ((p + 2 * q) / 3) := by
    intro x hx y hy hxy
    exact ⟨⟨min_le_right _ _, h12.le.trans (le_max_right _ _)⟩,
      ⟨(min_le_right _ _).trans h12.le, le_max_right _ _⟩,
      ⟨min_le_left _ _, hxy.le.trans (le_max_left _ _)⟩, ⟨(min_le_left _ _).trans hxy.le, le_max_left _ _⟩,
      lt_min hx.1 hp1, max_lt hy.2 h2q, (min_le_left _ _).trans (hxy.le.trans (le_max_left _ _))⟩
  rcases key _ _ hp1 h2q h12.le with hmono | hanti
  · left
    intro x hx y hy hxy
    obtain ⟨e1, e2, ex, ey, hm, hM, hmM⟩ := hext x hx y hy hxy
    rcases key _ _ hm hM hmM with h | h
    · exact h ex ey hxy
    · exfalso
      have a1 := h e1 e2 h12
      have a2 := hmono (left_mem_Icc.2 h12.le) (right_mem_Icc.2 h12.le) h12
      linarith
  · right
    intro x hx y hy hxy
    obtain ⟨e1, e2, ex, ey, hm, hM, hmM⟩ := hext x hx y hy hxy
    rcases key _ _ hm hM hmM with h | h
    · exfalso
      have a1 := h e1 e2 h12
      have a2 := hanti (left_mem_Icc.2 h12.le) (right_mem_Icc.2 h12.le) h12
      linarith
    · exact h ex ey hxy

/-- Extending a strictly monotone `κ₀ : (0, P) → (0, L)` by `0` and `L` at the ends. -/
theorem buj_b_extend_strictMono {κ₀ : ℝ → ℝ} {P L : ℝ} (hmono : StrictMonoOn κ₀ (Ioo 0 P))
    (hmaps : MapsTo κ₀ (Ioo 0 P) (Ioo 0 L)) :
    StrictMonoOn (fun θ => if θ ≤ 0 then 0 else if P ≤ θ then L else κ₀ θ) (Icc 0 P) := by
  intro x hx y hy hxy
  have hP : 0 < P := hx.1.trans_lt (hxy.trans_le hy.2)
  have hL : 0 < L := (hmaps ⟨half_pos hP, half_lt_self hP⟩).1.trans (hmaps ⟨half_pos hP, half_lt_self hP⟩).2
  have hx' : ¬ P ≤ x := fun h => absurd (hxy.trans_le hy.2) (not_lt.2 h)
  have hy' : ¬ y ≤ 0 := fun h => absurd (hx.1.trans_lt hxy) (not_lt.2 h)
  show (if x ≤ 0 then 0 else if P ≤ x then L else κ₀ x) < (if y ≤ 0 then 0 else if P ≤ y then L else κ₀ y)
  rw [ite_eq_right hy']
  by_cases hx0 : x ≤ 0
  · rw [ite_eq_left hx0]
    by_cases hyP : P ≤ y
    · rw [ite_eq_left hyP]
      exact hL
    · rw [ite_eq_right hyP]
      exact (hmaps ⟨not_le.1 hy', not_le.1 hyP⟩).1
  · rw [ite_eq_right hx0, ite_eq_right hx']
    by_cases hyP : P ≤ y
    · rw [ite_eq_left hyP]
      exact (hmaps ⟨not_le.1 hx0, not_le.1 hx'⟩).2
    · rw [ite_eq_right hyP]
      exact hmono ⟨not_le.1 hx0, not_le.1 hx'⟩ ⟨not_le.1 hy', not_le.1 hyP⟩ hxy

/-- **Reparametrization of a loop.** Two parametrizations `bf` on `[0, P]` and `γ` on `[0, L]` of the same Jordan
loop, both starting at the same point, differ by a strictly monotone (or antitone) homeomorphism `κ` of the
parameter intervals: `γ ∘ κ = bf`. -/
theorem buj_b_loop_reparam {bf γ : ℝ → ℂ} {P L : ℝ} (hP : 0 < P)
    (hbc : ContinuousOn bf (Icc 0 P)) (hbi : InjOn bf (Ico 0 P)) (hbP : bf P = bf 0)
    (hγc : ContinuousOn γ (Icc 0 L)) (hγi : InjOn γ (Ico 0 L)) (hγL : γ L = γ 0) (hγ0 : γ 0 = bf 0)
    (himg : bf '' Icc 0 P = γ '' Icc 0 L) :
    ∃ κ : ℝ → ℝ, ((StrictMonoOn κ (Icc 0 P) ∧ κ 0 = 0 ∧ κ P = L) ∨
        (StrictAntiOn κ (Icc 0 P) ∧ κ 0 = L ∧ κ P = 0)) ∧
      MapsTo κ (Ioo 0 P) (Ioo 0 L) ∧ SurjOn κ (Ioo 0 P) (Ioo 0 L) ∧ ∀ θ ∈ Icc 0 P, γ (κ θ) = bf θ := by
  have hne0 : ∀ θ ∈ Ioo 0 P, bf θ ≠ bf 0 := fun θ hθ h =>
    (ne_of_gt hθ.1) (hbi ⟨hθ.1.le, hθ.2⟩ ⟨le_rfl, hP⟩ h)
  have hpre : ∀ θ ∈ Ioo 0 P, bf θ ∈ γ '' Ioo 0 L := by
    intro θ hθ
    have h : bf θ ∈ γ '' Icc 0 L := himg ▸ mem_image_of_mem bf (Ioo_subset_Icc_self hθ)
    obtain ⟨x, hx, hxθ⟩ := h
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hxθ⟩
    · rintro rfl
      exact hne0 θ hθ (hxθ.symm.trans hγ0)
    · rintro rfl
      exact hne0 θ hθ (hxθ.symm.trans (hγL.trans hγ0))
  set κ₀ : ℝ → ℝ := fun θ => Function.invFunOn γ (Ioo 0 L) (bf θ) with hκ₀
  have hκ₀mem : ∀ θ ∈ Ioo 0 P, κ₀ θ ∈ Ioo 0 L := fun θ hθ => Function.invFunOn_mem (hpre θ hθ)
  have hκ₀γ : ∀ θ ∈ Ioo 0 P, γ (κ₀ θ) = bf θ := fun θ hθ => Function.invFunOn_eq (hpre θ hθ)
  have hκ₀i : InjOn κ₀ (Ioo 0 P) := fun θ hθ θ' hθ' h => by
    have h' : bf θ = bf θ' := by rw [← hκ₀γ θ hθ, ← hκ₀γ θ' hθ', h]
    exact hbi ⟨hθ.1.le, hθ.2⟩ ⟨hθ'.1.le, hθ'.2⟩ h'
  have hκ₀c : ContinuousOn κ₀ (Ioo 0 P) := by
    refine buj_b_continuousOn_of_unique isCompact_Icc hγc (hbc.mono Ioo_subset_Icc_self)
      (fun θ hθ => Ioo_subset_Icc_self (hκ₀mem θ hθ)) hκ₀γ ?_
    intro θ hθ y hy hyθ
    have hyL : y ≠ L := by
      rintro rfl
      exact hne0 θ hθ (hyθ.symm.trans (hγL.trans hγ0))
    exact hγi ⟨hy.1, lt_of_le_of_ne hy.2 hyL⟩ (Ioo_subset_Ico_self (hκ₀mem θ hθ))
      (hyθ.trans (hκ₀γ θ hθ).symm)
  have hsurj : SurjOn κ₀ (Ioo 0 P) (Ioo 0 L) := by
    intro x hx
    have h : γ x ∈ bf '' Icc 0 P := himg.symm ▸ mem_image_of_mem γ (Ioo_subset_Icc_self hx)
    obtain ⟨θ, hθ, hθx⟩ := h
    have hγne : γ x ≠ γ 0 := fun h' =>
      (ne_of_gt hx.1) (hγi (Ioo_subset_Ico_self hx) ⟨le_rfl, hx.1.trans hx.2⟩ h')
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      exact hγne (hθx.symm.trans hγ0.symm)
    have hθP : θ ≠ P := by
      rintro rfl
      exact hγne (hθx.symm.trans (hbP.trans hγ0.symm))
    have hθ' : θ ∈ Ioo 0 P := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθP⟩
    exact ⟨θ, hθ', hγi (Ioo_subset_Ico_self (hκ₀mem θ hθ')) (Ioo_subset_Ico_self hx) ((hκ₀γ θ hθ').trans hθx)⟩
  have hend : ∀ κ : ℝ → ℝ, (κ 0 = 0 ∨ κ 0 = L) → (κ P = 0 ∨ κ P = L) → EqOn κ κ₀ (Ioo 0 P) →
      ∀ θ ∈ Icc 0 P, γ (κ θ) = bf θ := by
    intro κ h0 hP' heq θ hθ
    by_cases hθ0 : θ = 0
    · rw [hθ0]
      rcases h0 with h | h <;> rw [h]
      · exact hγ0
      · exact hγL.trans hγ0
    by_cases hθP : θ = P
    · rw [hθP, hbP]
      rcases hP' with h | h <;> rw [h]
      · exact hγ0
      · exact hγL.trans hγ0
    have hθ' : θ ∈ Ioo 0 P := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθP⟩
    rw [heq hθ']
    exact hκ₀γ θ hθ'
  have hPn : ¬ P ≤ 0 := not_le.2 hP
  rcases buj_b_strictMonoOn_Ioo hκ₀c hκ₀i with hm | hm
  · set κ : ℝ → ℝ := fun θ => if θ ≤ 0 then 0 else if P ≤ θ then L else κ₀ θ with hκ
    have hκ0 : κ 0 = 0 := ite_eq_left le_rfl
    have hκP : κ P = L := by
      show (if P ≤ 0 then 0 else if P ≤ P then L else κ₀ P) = L
      rw [ite_eq_right hPn, ite_eq_left le_rfl]
    have heq : EqOn κ κ₀ (Ioo 0 P) := fun θ hθ => by
      show (if θ ≤ 0 then 0 else if P ≤ θ then L else κ₀ θ) = κ₀ θ
      rw [ite_eq_right (not_le.2 hθ.1), ite_eq_right (not_le.2 hθ.2)]
    exact ⟨κ, Or.inl ⟨buj_b_extend_strictMono hm hκ₀mem, hκ0, hκP⟩,
      fun θ hθ => (heq hθ) ▸ hκ₀mem θ hθ, hsurj.congr heq.symm,
      hend κ (Or.inl hκ0) (Or.inr hκP) heq⟩
  · have hm' : StrictMonoOn (fun θ => L - κ₀ θ) (Ioo 0 P) := fun x hx y hy hxy => by
      have := hm hx hy hxy
      show L - κ₀ x < L - κ₀ y
      linarith
    have hmaps' : MapsTo (fun θ => L - κ₀ θ) (Ioo 0 P) (Ioo 0 L) := fun θ hθ => by
      have h := hκ₀mem θ hθ
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    set κ : ℝ → ℝ := fun θ => L - (if θ ≤ 0 then 0 else if P ≤ θ then L else L - κ₀ θ) with hκ
    have hκ0 : κ 0 = L := by
      show L - (if (0 : ℝ) ≤ 0 then 0 else if P ≤ 0 then L else L - κ₀ 0) = L
      rw [ite_eq_left le_rfl, sub_zero]
    have hκP : κ P = 0 := by
      show L - (if P ≤ 0 then 0 else if P ≤ P then L else L - κ₀ P) = 0
      rw [ite_eq_right hPn, ite_eq_left le_rfl, sub_self]
    have heq : EqOn κ κ₀ (Ioo 0 P) := fun θ hθ => by
      show L - (if θ ≤ 0 then 0 else if P ≤ θ then L else L - κ₀ θ) = κ₀ θ
      rw [ite_eq_right (not_le.2 hθ.1), ite_eq_right (not_le.2 hθ.2), sub_sub_cancel]
    have hanti : StrictAntiOn κ (Icc 0 P) := fun x hx y hy hxy => by
      have := buj_b_extend_strictMono hm' hmaps' hx hy hxy
      show L - _ < L - _
      linarith
    exact ⟨κ, Or.inr ⟨hanti, hκ0, hκP⟩, fun θ hθ => (heq hθ) ▸ hκ₀mem θ hθ, hsurj.congr heq.symm,
      hend κ (Or.inr hκ0) (Or.inl hκP) heq⟩

/-- `⌊x / P⌋ P ≤ x < (⌊x / P⌋ + 1) P`. -/
theorem buj_b_floor_bounds {P : ℝ} (hP : 0 < P) (x : ℝ) :
    (⌊x / P⌋ : ℝ) * P ≤ x ∧ x < ((⌊x / P⌋ : ℝ) + 1) * P :=
  ⟨(le_div_iff₀ hP).1 (Int.floor_le (x / P)), (div_lt_iff₀ hP).1 (Int.lt_floor_add_one (x / P))⟩

/-- **A Stieltjes function with periodic increments** whose measure on `(0, P]` is a given finite measure `μ₀`
carried by `(0, P)`. -/
theorem buj_b_stieltjes_periodic {μ₀ : Measure ℝ} [IsFiniteMeasure μ₀] {P : ℝ} (hP : 0 < P)
    (hsupp : μ₀ (Ioo 0 P)ᶜ = 0) :
    ∃ V : StieltjesFunction ℝ, (∀ x (k : ℤ), V (x + k * P) = V x + k * (V P - V 0)) ∧
      V.measure.restrict (Ioc 0 P) = μ₀ ∧
      ∀ x y, 0 ≤ x → x ≤ y → y ≤ P → V y - V x = (μ₀ (Ioc x y)).toReal := by
  set v : ℝ → ℝ := fun x => (μ₀ (Iic x)).toReal with hv
  set ℓ : ℝ := (μ₀ univ).toReal with hℓ
  have hfin : ∀ s, μ₀ s ≠ ⊤ := fun s => measure_ne_top μ₀ s
  have hv0 : ∀ x ≤ 0, v x = 0 := by
    intro x hx
    have h : μ₀ (Iic x) = 0 :=
      measure_mono_null (show Iic x ⊆ (Ioo 0 P)ᶜ from fun y hy h' =>
        absurd (h'.1.trans_le ((mem_Iic.1 hy).trans hx)) (lt_irrefl 0)) hsupp
    simp only [hv, h, ENNReal.toReal_zero]
  have hvP : ∀ x, P ≤ x → v x = ℓ := by
    intro x hx
    have h1 : μ₀ (Iic x)ᶜ = 0 :=
      measure_mono_null (show (Iic x)ᶜ ⊆ (Ioo 0 P)ᶜ from fun y hy h' => hy (mem_Iic.2 (h'.2.le.trans hx)))
        hsupp
    have h2 : μ₀ (Iic x) = μ₀ univ := by
      rw [← measure_add_measure_compl (measurableSet_Iic : MeasurableSet (Iic x)), h1, add_zero]
    simp only [hv, hℓ, h2]
  have hvmono : Monotone v := fun x y hxy =>
    ENNReal.toReal_mono (hfin _) (measure_mono (Iic_subset_Iic.2 hxy))
  have hvnn : ∀ x, 0 ≤ v x := fun x => ENNReal.toReal_nonneg
  have hvle : ∀ x, v x ≤ ℓ := fun x => ENNReal.toReal_mono (hfin _) (measure_mono (subset_univ _))
  have hvdiff : ∀ x y, x ≤ y → v y - v x = (μ₀ (Ioc x y)).toReal := by
    intro x y hxy
    have h : μ₀ (Iic y) = μ₀ (Iic x) + μ₀ (Ioc x y) := by
      rw [← Iic_union_Ioc_eq_Iic hxy, measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    simp only [hv, h, ENNReal.toReal_add (hfin _) (hfin _)]
    ring
  have hvrc : ∀ x, ContinuousWithinAt v (Ici x) x := by
    intro x
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h := tendsto_measure_biInter_gt (μ := μ₀) (s := Iic) (a := x)
      (fun r _ => measurableSet_Iic.nullMeasurableSet) (fun i j _ hij => Iic_subset_Iic.2 hij)
      ⟨x + 1, by linarith, hfin _⟩
    have hint : ⋂ r > x, Iic r = Iic x := by
      ext y
      simp only [mem_iInter, mem_Iic]
      exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense h, fun h r hr => h.trans hr.le⟩
    rw [hint] at h
    exact (ENNReal.tendsto_toReal (hfin _)).comp h
  -- the periodic extension
  set V : ℝ → ℝ := fun x => ℓ * ⌊x / P⌋ + v (x - ⌊x / P⌋ * P) with hV
  have hVeq : ∀ x ∈ Icc 0 P, V x = v x := by
    intro x hx
    rcases hx.2.lt_or_eq with h | h
    · have hfl : ⌊x / P⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨div_nonneg hx.1 hP.le, (div_lt_one hP).2 h⟩
      simp only [hV, hfl, Int.cast_zero, mul_zero, zero_mul, sub_zero, zero_add]
    · rw [h]
      have hfl : ⌊P / P⌋ = 1 := by rw [div_self hP.ne', Int.floor_one]
      simp only [hV, hfl, Int.cast_one, mul_one, one_mul, sub_self]
      rw [hv0 0 le_rfl, hvP P le_rfl, add_zero]
  have hV0 : V 0 = 0 := by rw [hVeq 0 ⟨le_rfl, hP.le⟩, hv0 0 le_rfl]
  have hVP : V P = ℓ := by rw [hVeq P ⟨hP.le, le_rfl⟩, hvP P le_rfl]
  have hVshift : ∀ x (k : ℤ), V (x + k * P) = V x + k * ℓ := by
    intro x k
    have hfl : ⌊(x + k * P) / P⌋ = ⌊x / P⌋ + k := by
      rw [add_div, mul_div_cancel_right₀ _ hP.ne', Int.floor_add_intCast]
    simp only [hV, hfl, Int.cast_add]
    rw [show x + k * P - (⌊x / P⌋ + k) * P = x - ⌊x / P⌋ * P by ring]
    ring
  have hVmono : Monotone V := by
    intro x y hxy
    have hmn : ⌊x / P⌋ ≤ ⌊y / P⌋ := Int.floor_mono (div_le_div_of_nonneg_right hxy hP.le)
    have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
    rcases hmn.lt_or_eq with h | h
    · have h' : (⌊x / P⌋ : ℝ) + 1 ≤ ⌊y / P⌋ := by exact_mod_cast Int.add_one_le_of_lt h
      have e1 := hvle (x - ⌊x / P⌋ * P)
      have e2 := hvnn (y - ⌊y / P⌋ * P)
      have e3 := mul_le_mul_of_nonneg_left h' hℓ0
      show ℓ * ⌊x / P⌋ + v (x - ⌊x / P⌋ * P) ≤ ℓ * ⌊y / P⌋ + v (y - ⌊y / P⌋ * P)
      nlinarith
    · show ℓ * ⌊x / P⌋ + v (x - ⌊x / P⌋ * P) ≤ ℓ * ⌊y / P⌋ + v (y - ⌊y / P⌋ * P)
      rw [h]
      have := hvmono (show x - ⌊y / P⌋ * P ≤ y - ⌊y / P⌋ * P by linarith)
      linarith
  have hVrc : ∀ x, ContinuousWithinAt V (Ici x) x := by
    intro x
    obtain ⟨h1, h2⟩ := buj_b_floor_bounds hP x
    have hloc : ∀ y ∈ Ico x (((⌊x / P⌋ : ℝ) + 1) * P), V y = ℓ * ⌊x / P⌋ + v (y - ⌊x / P⌋ * P) := by
      intro y hy
      have hfl : ⌊y / P⌋ = ⌊x / P⌋ := by
        rw [Int.floor_eq_iff]
        exact ⟨(le_div_iff₀ hP).2 (h1.trans hy.1), (div_lt_iff₀ hP).2 hy.2⟩
      simp only [hV, hfl]
    have hg : ContinuousWithinAt (fun y : ℝ => y - ⌊x / P⌋ * P) (Ici x) x :=
      (continuous_id.sub continuous_const).continuousWithinAt
    have hvc : ContinuousWithinAt (fun y => v (y - ⌊x / P⌋ * P)) (Ici x) x :=
      ContinuousWithinAt.comp (f := fun y : ℝ => y - ⌊x / P⌋ * P) (hvrc _) hg (fun y hy => by
        simp only [mem_Ici] at hy ⊢
        linarith)
    have hc : ContinuousWithinAt (fun y => ℓ * ⌊x / P⌋ + v (y - ⌊x / P⌋ * P)) (Ici x) x :=
      continuousWithinAt_const.add hvc
    refine hc.congr_of_eventuallyEq ?_ (hloc x ⟨le_rfl, h2⟩)
    filter_upwards [Ico_mem_nhdsGE h2] with y hy
    exact hloc y hy
  set W : StieltjesFunction ℝ := ⟨V, hVmono, hVrc⟩ with hW
  have hWV : ∀ x, W x = V x := fun x => rfl
  have hdiff : ∀ x y, 0 ≤ x → x ≤ y → y ≤ P → W y - W x = (μ₀ (Ioc x y)).toReal := by
    intro x y hx hxy hy
    rw [hWV, hWV, hVeq x ⟨hx, hxy.trans hy⟩, hVeq y ⟨hx.trans hxy, hy⟩]
    exact hvdiff x y hxy
  have hmeas : ∀ x y, 0 ≤ x → y ≤ P → W.measure (Ioc x y) = μ₀ (Ioc x y) := by
    intro x y hx hy
    rw [StieltjesFunction.measure_Ioc]
    by_cases hxy : x ≤ y
    · rw [hdiff x y hx hxy hy, ENNReal.ofReal_toReal (hfin _)]
    · rw [Ioc_eq_empty (fun h => hxy h.le), measure_empty]
      exact ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (W.mono (not_le.1 hxy).le))
  refine ⟨W, fun x k => ?_, ?_, hdiff⟩
  · rw [hWV, hWV, hWV, hWV, hVshift, hV0, hVP, sub_zero]
  · have hμres : μ₀.restrict (Ioc 0 P) = μ₀ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      exact measure_mono_null (show {y | ¬ y ∈ Ioc 0 P} ⊆ (Ioo 0 P)ᶜ from
        fun y hy h' => hy (Ioo_subset_Ioc_self h')) hsupp
    conv_rhs => rw [← hμres]
    refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b _ => ?_)
    · rw [Measure.restrict_apply measurableSet_Ioc]
      exact ((measure_mono inter_subset_left).trans_lt (by
        rw [StieltjesFunction.measure_Ioc]
        exact ENNReal.ofReal_lt_top)).ne
    · rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc]
      exact hmeas _ _ le_sup_right inf_le_right

/-- **Periodic chaining**: an increment bound on one period `[0, P]` extends to all of `ℝ`. -/
theorem buj_b_periodic_chain {f : ℝ → ℂ} {V : ℝ → ℝ} {P c : ℝ} (hP : 0 < P)
    (hf : ∀ x (k : ℤ), f (x + k * P) = f x) (hV : ∀ x (k : ℤ), V (x + k * P) = V x + k * c)
    (hbase : ∀ x y, 0 ≤ x → x ≤ y → y ≤ P → ‖f y - f x‖ ≤ V y - V x) :
    ∀ x y, x ≤ y → ‖f y - f x‖ ≤ V y - V x := by
  have hbase' : ∀ (k : ℤ) x y, k * P ≤ x → x ≤ y → y ≤ (k + 1) * P → ‖f y - f x‖ ≤ V y - V x := by
    intro k x y hx hxy hy
    have h := hbase (x - k * P) (y - k * P) (by linarith) (by linarith) (by linarith)
    have ex := hf (x - k * P) k
    have ey := hf (y - k * P) k
    have vx := hV (x - k * P) k
    have vy := hV (y - k * P) k
    rw [sub_add_cancel] at ex ey vx vy
    rw [ex, ey, vx, vy]
    linarith
  have key : ∀ N : ℕ, ∀ x y, x ≤ y → y ≤ ((⌊x / P⌋ : ℝ) + 1 + N) * P → ‖f y - f x‖ ≤ V y - V x := by
    intro N
    induction N with
    | zero =>
      intro x y hxy hy
      exact hbase' ⌊x / P⌋ x y (buj_b_floor_bounds hP x).1 hxy (by simpa using hy)
    | succ N ih =>
      intro x y hxy hy
      by_cases hy1 : y ≤ ((⌊x / P⌋ : ℝ) + 1) * P
      · exact hbase' ⌊x / P⌋ x y (buj_b_floor_bounds hP x).1 hxy hy1
      · push Not at hy1
        have hz : ⌊(((⌊x / P⌋ : ℝ) + 1) * P) / P⌋ = ⌊x / P⌋ + 1 := by
          rw [mul_div_cancel_right₀ _ hP.ne', Int.floor_add_one, Int.floor_intCast]
        have h1 := hbase' ⌊x / P⌋ x (((⌊x / P⌋ : ℝ) + 1) * P) (buj_b_floor_bounds hP x).1
          (buj_b_floor_bounds hP x).2.le le_rfl
        have h2 := ih (((⌊x / P⌋ : ℝ) + 1) * P) y hy1.le (by
          rw [hz]
          push_cast at hy ⊢
          linarith)
        calc ‖f y - f x‖ = ‖(f y - f (((⌊x / P⌋ : ℝ) + 1) * P)) + (f (((⌊x / P⌋ : ℝ) + 1) * P) - f x)‖ := by
              rw [sub_add_sub_cancel]
          _ ≤ ‖f y - f (((⌊x / P⌋ : ℝ) + 1) * P)‖ + ‖f (((⌊x / P⌋ : ℝ) + 1) * P) - f x‖ := norm_add_le _ _
          _ ≤ (V y - V (((⌊x / P⌋ : ℝ) + 1) * P)) + (V (((⌊x / P⌋ : ℝ) + 1) * P) - V x) := add_le_add h2 h1
          _ = V y - V x := by ring
  intro x y hxy
  obtain ⟨N, hN⟩ := exists_nat_ge (y / P - ⌊x / P⌋ - 1)
  refine key N x y hxy ?_
  have h : y / P ≤ (⌊x / P⌋ : ℝ) + 1 + N := by linarith
  exact (div_le_iff₀ hP).1 h

/-- **The boundary length measure of a reparametrized loop** (generic form). Let `bf` be continuous,
`2π`-periodic and injective on `[0, 2π)`, and let `γ` be a second parametrization of the same Jordan loop on
`[0, L]`, starting at the same point, whose increments are dominated by the integrals of a finite density `g`.
Then there is a Stieltjes function `V` with `2π`-periodic increments dominating the increments of `bf`, such
that `bf` pushes `dV` on `(0, 2π]` forward to `g dx` along `γ`; the reparametrization `κ` (`γ ∘ κ = bf`) is
strictly monotone or strictly antitone. -/
theorem buj_b_boundary_measure_generic {bf γ : ℝ → ℂ} {g : ℝ → ℝ≥0∞} {L : ℝ}
    (hbc : Continuous bf) (hbper : ∀ x (k : ℤ), bf (x + k * (2 * π)) = bf x)
    (hbi : InjOn bf (Ico 0 (2 * π)))
    (hγc : ContinuousOn γ (Icc 0 L)) (hγi : InjOn γ (Ico 0 L)) (hγL : γ L = γ 0) (hγ0 : γ 0 = bf 0)
    (himg : bf '' Icc 0 (2 * π) = γ '' Icc 0 L) (hg : Measurable g) (hgfin : ∫⁻ x in Ioo 0 L, g x ≠ ⊤)
    (hinc : ∀ x y, 0 ≤ x → x ≤ y → y ≤ L → edist (γ x) (γ y) ≤ ∫⁻ u in Ioo x y, g u) :
    ∃ (V : StieltjesFunction ℝ) (κ : ℝ → ℝ),
      (∀ θ h : ℝ, 0 ≤ h → ‖bf (θ + h) - bf θ‖ ≤ V (θ + h) - V θ) ∧
      (∀ θ : ℝ, V (θ + 2 * π) = V θ + (V (2 * π) - V 0)) ∧
      (∀ F : ℂ → ℝ≥0∞, Measurable F →
        ∫⁻ θ in Ioc 0 (2 * π), F (bf θ) ∂V.measure = ∫⁻ x in Ioo 0 L, F (γ x) * g x) ∧
      (StrictMonoOn κ (Icc 0 (2 * π)) ∨ StrictAntiOn κ (Icc 0 (2 * π))) ∧
      MapsTo κ (Ioo 0 (2 * π)) (Ioo 0 L) ∧ SurjOn κ (Ioo 0 (2 * π)) (Ioo 0 L) ∧
      ∀ θ ∈ Ioo 0 (2 * π), γ (κ θ) = bf θ := by
  have hP : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hbP : bf (2 * π) = bf 0 := by
    have h := hbper 0 1
    rwa [Int.cast_one, one_mul, zero_add] at h
  obtain ⟨κ, hκmono, hκmaps, hκsurj, hκγ⟩ :=
    buj_b_loop_reparam hP hbc.continuousOn hbi hbP hγc hγi hγL hγ0 himg
  -- the inverse `lam` of `κ` on `(0, L)`
  set lam : ℝ → ℝ := fun x => Function.invFunOn κ (Ioo 0 (2 * π)) x with hlamdef
  have hlam : ∀ x ∈ Ioo 0 L, lam x ∈ Ioo 0 (2 * π) ∧ κ (lam x) = x := fun x hx =>
    ⟨Function.invFunOn_mem (hκsurj hx), Function.invFunOn_eq (hκsurj hx)⟩
  have hκIcc : ∀ θ ∈ Icc 0 (2 * π), κ θ ∈ Icc 0 L := by
    intro θ hθ
    rcases hκmono with ⟨hm, h0, hPe⟩ | ⟨hm, h0, hPe⟩
    · have h1 := hm.monotoneOn ⟨le_rfl, hP.le⟩ hθ hθ.1
      have h2 := hm.monotoneOn hθ ⟨hP.le, le_rfl⟩ hθ.2
      rw [h0] at h1
      rw [hPe] at h2
      exact ⟨h1, h2⟩
    · have h1 := hm.antitoneOn hθ ⟨hP.le, le_rfl⟩ hθ.2
      have h2 := hm.antitoneOn ⟨le_rfl, hP.le⟩ hθ hθ.1
      rw [hPe] at h1
      rw [h0] at h2
      exact ⟨h1, h2⟩
  have hlam_mono : MonotoneOn lam (Ioo 0 L) ∨ AntitoneOn lam (Ioo 0 L) := by
    rcases hκmono with ⟨hm, -, -⟩ | ⟨hm, -, -⟩
    · left
      intro x hx y hy hxy
      by_contra h
      push Not at h
      have h' := hm (Ioo_subset_Icc_self (hlam y hy).1) (Ioo_subset_Icc_self (hlam x hx).1) h
      rw [(hlam x hx).2, (hlam y hy).2] at h'
      linarith
    · right
      intro x hx y hy hxy
      by_contra h
      push Not at h
      have h' := hm (Ioo_subset_Icc_self (hlam x hx).1) (Ioo_subset_Icc_self (hlam y hy).1) h
      rw [(hlam x hx).2, (hlam y hy).2] at h'
      linarith
  have hlam_meas : AEMeasurable lam (volume.restrict (Ioo 0 L)) :=
    hlam_mono.elim (aemeasurable_restrict_of_monotoneOn measurableSet_Ioo)
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioo)
  -- the measure `ν = g dx` on `(0, L)` and its push-forward `μ₀` to the circle parameter
  set ν : Measure ℝ := (volume.restrict (Ioo 0 L)).withDensity g with hν
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_withDensity hgfin
  have hlam_ν : AEMeasurable lam ν := hlam_meas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hνS : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Ioo 0 L → ν S = ∫⁻ x in S, g x := by
    intro S hS hSL
    rw [hν, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.2 hSL]
  have hνc : ν (Ioo 0 L)ᶜ = 0 := by
    rw [hν, withDensity_apply _ measurableSet_Ioo.compl, Measure.restrict_restrict measurableSet_Ioo.compl,
      compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]
  set μ₀ : Measure ℝ := ν.map lam with hμ₀
  have hμ₀fin : IsFiniteMeasure μ₀ := by
    rw [hμ₀]
    infer_instance
  have hsupp : μ₀ (Ioo 0 (2 * π))ᶜ = 0 := by
    rw [hμ₀, Measure.map_apply_of_aemeasurable hlam_ν measurableSet_Ioo.compl]
    refine measure_mono_null ?_ hνc
    intro x hx hxL
    exact hx (hlam x hxL).1
  obtain ⟨V, hVshift, hVres, hVdiff⟩ := buj_b_stieltjes_periodic (μ₀ := μ₀) hP hsupp
  -- the increment bound on one period
  have hbase : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 2 * π → ‖bf y - bf x‖ ≤ V y - V x := by
    intro x y hx hxy hy
    rw [hVdiff x y hx hxy hy]
    have hxI : x ∈ Icc 0 (2 * π) := ⟨hx, hxy.trans hy⟩
    have hyI : y ∈ Icc 0 (2 * π) := ⟨hx.trans hxy, hy⟩
    have hle : ENNReal.ofReal ‖bf y - bf x‖ ≤ μ₀ (Ioc x y) := by
      rw [hμ₀, Measure.map_apply_of_aemeasurable hlam_ν measurableSet_Ioc]
      have hed : ENNReal.ofReal ‖bf y - bf x‖ = edist (γ (κ x)) (γ (κ y)) := by
        rw [hκγ x hxI, hκγ y hyI, edist_dist, dist_eq_norm, norm_sub_rev]
      rw [hed]
      rcases hκmono with ⟨hm, -, -⟩ | ⟨hm, -, -⟩
      · have hsub : Ioo (κ x) (κ y) ⊆ lam ⁻¹' Ioc x y := by
          intro u hu
          have huL : u ∈ Ioo 0 L := ⟨(hκIcc x hxI).1.trans_lt hu.1, hu.2.trans_le (hκIcc y hyI).2⟩
          obtain ⟨hl1, hl2⟩ := hlam u huL
          refine ⟨?_, ?_⟩
          · by_contra h
            push Not at h
            have h' := hm.monotoneOn (Ioo_subset_Icc_self hl1) hxI h
            rw [hl2] at h'
            linarith [hu.1]
          · by_contra h
            push Not at h
            have h' := hm hyI (Ioo_subset_Icc_self hl1) h
            rw [hl2] at h'
            linarith [hu.2]
        calc edist (γ (κ x)) (γ (κ y)) ≤ ∫⁻ u in Ioo (κ x) (κ y), g u :=
              hinc _ _ (hκIcc x hxI).1 (hm.monotoneOn hxI hyI hxy) (hκIcc y hyI).2
          _ = ν (Ioo (κ x) (κ y)) :=
              (hνS _ measurableSet_Ioo (Ioo_subset_Ioo (hκIcc x hxI).1 (hκIcc y hyI).2)).symm
          _ ≤ ν (lam ⁻¹' Ioc x y) := measure_mono hsub
      · have hsub : Ioo (κ y) (κ x) ⊆ lam ⁻¹' Ioc x y := by
          intro u hu
          have huL : u ∈ Ioo 0 L := ⟨(hκIcc y hyI).1.trans_lt hu.1, hu.2.trans_le (hκIcc x hxI).2⟩
          obtain ⟨hl1, hl2⟩ := hlam u huL
          refine ⟨?_, ?_⟩
          · by_contra h
            push Not at h
            have h' := hm.antitoneOn (Ioo_subset_Icc_self hl1) hxI h
            rw [hl2] at h'
            linarith [hu.2]
          · by_contra h
            push Not at h
            have h' := hm hyI (Ioo_subset_Icc_self hl1) h
            rw [hl2] at h'
            linarith [hu.1]
        calc edist (γ (κ x)) (γ (κ y)) = edist (γ (κ y)) (γ (κ x)) := edist_comm _ _
          _ ≤ ∫⁻ u in Ioo (κ y) (κ x), g u :=
              hinc _ _ (hκIcc y hyI).1 (hm.antitoneOn hxI hyI hxy) (hκIcc x hxI).2
          _ = ν (Ioo (κ y) (κ x)) :=
              (hνS _ measurableSet_Ioo (Ioo_subset_Ioo (hκIcc y hyI).1 (hκIcc x hxI).2)).symm
          _ ≤ ν (lam ⁻¹' Ioc x y) := measure_mono hsub
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hle
  have hchain := buj_b_periodic_chain hP hbper hVshift hbase
  refine ⟨V, κ, fun θ h hh => hchain θ (θ + h) (by linarith), fun θ => ?_, fun F hF => ?_,
    hκmono.imp (fun h => h.1) (fun h => h.1), hκmaps, hκsurj, fun θ hθ => hκγ θ (Ioo_subset_Icc_self hθ)⟩
  · have h := hVshift θ 1
    simp only [Int.cast_one, one_mul] at h
    exact h
  · have hFb : Measurable fun θ => F (bf θ) := hF.comp hbc.measurable
    calc ∫⁻ θ in Ioc 0 (2 * π), F (bf θ) ∂V.measure = ∫⁻ θ, F (bf θ) ∂μ₀ := by rw [hVres]
      _ = ∫⁻ x, F (bf (lam x)) ∂ν := by
          rw [hμ₀]
          exact lintegral_map' hFb.aemeasurable hlam_ν
      _ = ∫⁻ x in Ioo 0 L, g x * F (bf (lam x)) := by
          rw [hν]
          exact lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable (hFb.comp_aemeasurable hlam_meas)
      _ = ∫⁻ x in Ioo 0 L, F (γ x) * g x := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
          have h1 := hκγ (lam x) (Ioo_subset_Icc_self (hlam x hx).1)
          rw [(hlam x hx).2] at h1
          rw [← h1, mul_comm]

/-- **The boundary length measure of a sector cut.**

Setting: `ρ` is continuous and injective on `Δ̄`, with `ρ 1 = 0` and `ρ(∂Δ)` equal to the cut curve.

Claim: there are a Stieltjes function `V` and `0 ≤ u₁ < u₂ ≤ 2π` such that:
* `V` is the (periodically extended) arclength of `θ ↦ ρ(e^{iθ})`: it dominates the increments and has
  `2π`-periodic increments;
* the points of the circle mapped into the open sector are exactly `θ ∈ (u₁, u₂)`;
* integrals against `dV` are bounded by the lengths of the pieces: `τ` over `(u₁, u₂)`, and `τ` plus the two
  sides over the whole circle.

*Truth:* TRUE.
1. On `(0, 2π)`, `θ ↦ ρ(e^{iθ})` is a continuous bijection onto `J ∖ {0}`. So `κ = γ⁻¹ ∘ ρ(e^{i·})` is a strictly
   monotone homeomorphism onto the parameter interval of the concatenated loop `γ` (side, `τ`, side), with either
   orientation. A continuous injection between intervals is strictly monotone.
2. `(u₁, u₂) = κ⁻¹(τ-part)`.
3. `V = ∫|γ'| ∘ κ`, extended by `V(θ + 2π) = V θ + length(J)`. `V` is continuous, so it has no atoms.
4. `‖γ(y) - γ(x)‖ ≤ ∫_x^y |γ'|` by the FTC for the absolutely continuous `τ` (differentiable on `(s, t)` with
   integrable derivative) and for the segments.
5. The two integral bounds are equalities, by the change of variables `κ_* μ_V = |γ'| dx`: the two measures agree on
   intervals.

*Route:* `ContinuousOn.strictMonoOn_of_injOn`-type monotonicity, `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`StieltjesFunction.measure_Ioc`, `Measure.ext_of_Ioc`, and `lintegral_map`. -/
theorem buj_sector_boundary_measure {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) {ρ : ℂ → ℂ} (hρ : DiffContOnCl ℂ ρ (ball 0 1))
    (hinj : InjOn ρ (closedBall 0 1)) (hρ1 : ρ 1 = 0)
    (himg : ρ '' sphere 0 1 = buj_cutCurve ξ α a b τ s t) :
    ∃ (V : StieltjesFunction ℝ) (u₁ u₂ : ℝ), 0 ≤ u₁ ∧ u₁ < u₂ ∧ u₂ ≤ 2 * π ∧
      (∀ θ h : ℝ, 0 ≤ h → ‖ρ (circleMap 0 1 (θ + h)) - ρ (circleMap 0 1 θ)‖ ≤ V (θ + h) - V θ) ∧
      (∀ θ : ℝ, V (θ + 2 * π) = V θ + (V (2 * π) - V 0)) ∧
      (∀ θ ∈ Ioc 0 (2 * π), ρ (circleMap 0 1 θ) ∈ buj_openSector ξ α ↔ θ ∈ Ioo u₁ u₂) ∧
      (∀ f : ℂ → ℝ≥0∞, Measurable f →
        ∫⁻ θ in Ioo u₁ u₂, f (ρ (circleMap 0 1 θ)) ∂V.measure ≤
          ∫⁻ x in Ioo s t, f (τ x) * ‖deriv τ x‖ₑ) ∧
      ∀ f : ℂ → ℝ≥0∞, Measurable f →
        ∫⁻ θ in Ioc 0 (2 * π), f (ρ (circleMap 0 1 θ)) ∂V.measure ≤
          (∫⁻ x in Ioo s t, f (τ x) * ‖deriv τ x‖ₑ) + (∫⁻ r in Ioo 0 a, f ((r : ℂ) * ξ)) +
            ∫⁻ r in Ioo 0 b, f ((r : ℂ) * (ξ * exp (α * I))) := by
  have hc := hcut
  obtain ⟨⟨hα0, hαπ, -, -, ha, hb, hst⟩, -⟩ := hc
  have hρc : ContinuousOn ρ (closedBall 0 1) := by
    have h := hρ.continuousOn
    rwa [closure_ball (0 : ℂ) one_ne_zero] at h
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  have hbc : Continuous fun θ => ρ (circleMap 0 1 θ) :=
    hρc.comp_continuous (continuous_circleMap 0 1) hcm
  have hbper : ∀ x (k : ℤ), ρ (circleMap 0 1 (x + k * (2 * π))) = ρ (circleMap 0 1 x) := fun x k => by
    rw [(periodic_circleMap 0 1).int_mul k x]
  have hbi : InjOn (fun θ => ρ (circleMap 0 1 θ)) (Ico 0 (2 * π)) := fun x hx y hy hxy =>
    injOn_circleMap_of_abs_sub_le' one_ne_zero (by linarith) hx hy (hinj (hcm x) (hcm y) hxy)
  have hb0 : ρ (circleMap 0 1 0) = 0 := by
    rw [show circleMap (0 : ℂ) 1 0 = 1 by simp [circleMap], hρ1]
  have hcirc : circleMap (0 : ℂ) 1 '' Icc 0 (2 * π) = sphere 0 1 := by
    apply subset_antisymm
    · rintro _ ⟨θ, -, rfl⟩
      exact circleMap_mem_sphere 0 zero_le_one θ
    · have h := image_circleMap_Ioc (0 : ℂ) 1
      rw [abs_one] at h
      rw [← h]
      exact image_mono Ioc_subset_Icc_self
  have himgb : (fun θ => ρ (circleMap 0 1 θ)) '' Icc 0 (2 * π) =
      buj_b_loop ξ α a b τ s t '' Icc 0 (a + (t - s) + b) := by
    rw [buj_b_loop_image hcut, ← himg, ← hcirc, image_image]
  obtain ⟨V, κ, hinc, hper, hint, hκm, -, hκsurj, hκγ⟩ :=
    buj_b_boundary_measure_generic hbc hbper hbi (buj_b_loop_continuousOn hcut) (buj_b_loop_injOn hcut)
      (by rw [buj_b_loop_L hcut, buj_b_loop_zero hcut]) (by rw [buj_b_loop_zero hcut]; exact hb0.symm) himgb
      (buj_b_dens_measurable a s t τ) (buj_b_lintegral_dens_lt_top hcut).ne (buj_b_loop_edist_le hcut)
  -- the parameter interval of the cut
  obtain ⟨θa, hθa, hκa⟩ := hκsurj (show a ∈ Ioo 0 (a + (t - s) + b) from ⟨ha, by linarith⟩)
  obtain ⟨θc, hθc, hκc⟩ :=
    hκsurj (show a + (t - s) ∈ Ioo 0 (a + (t - s) + b) from ⟨by linarith, by linarith⟩)
  have hθaI := Ioo_subset_Icc_self hθa
  have hθcI := Ioo_subset_Icc_self hθc
  have hchar : ∃ u₁ u₂, 0 < u₁ ∧ u₁ < u₂ ∧ u₂ < 2 * π ∧
      ∀ θ ∈ Ioo 0 (2 * π), κ θ ∈ Ioo a (a + (t - s)) ↔ θ ∈ Ioo u₁ u₂ := by
    rcases hκm with hm | hm
    · refine ⟨θa, θc, hθa.1, (hm.lt_iff_lt hθaI hθcI).1 (by rw [hκa, hκc]; linarith), hθc.2,
        fun θ hθ => ?_⟩
      have hθI := Ioo_subset_Icc_self hθ
      rw [mem_Ioo, mem_Ioo, ← hm.lt_iff_lt hθaI hθI, ← hm.lt_iff_lt hθI hθcI, hκa, hκc]
    · refine ⟨θc, θa, hθc.1, (hm.lt_iff_gt hθaI hθcI).1 (by rw [hκa, hκc]; linarith), hθa.2,
        fun θ hθ => ?_⟩
      have hθI := Ioo_subset_Icc_self hθ
      rw [mem_Ioo, mem_Ioo, ← hm.lt_iff_gt hθI hθcI, ← hm.lt_iff_gt hθaI hθI, hκa, hκc]
      exact and_comm
  obtain ⟨u₁, u₂, hu₁, hu₁₂, hu₂, hu⟩ := hchar
  have hE : ∀ θ ∈ Ioc 0 (2 * π), ρ (circleMap 0 1 θ) ∈ buj_openSector ξ α ↔ θ ∈ Ioo u₁ u₂ := by
    intro θ hθ
    rcases hθ.2.lt_or_eq with h | h
    · have hθ' : θ ∈ Ioo 0 (2 * π) := ⟨hθ.1, h⟩
      rw [← hu θ hθ', ← buj_b_loop_mem_openSector_iff hcut, hκγ θ hθ']
    · have h0 : ρ (circleMap 0 1 θ) = 0 := by
        have hp := (periodic_circleMap (0 : ℂ) 1) 0
        rw [zero_add] at hp
        rw [h, hp]
        exact hb0
      rw [h0]
      constructor
      · intro hO
        exact absurd (zero_div ξ) hO.1
      · intro h'
        have h2 := h'.2
        rw [h] at h2
        linarith
  have hint' : ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∫⁻ θ in Ioc 0 (2 * π), F (ρ (circleMap 0 1 θ)) ∂V.measure =
        ∫⁻ x in Ioo 0 (a + (t - s) + b), F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x := hint
  refine ⟨V, u₁, u₂, hu₁.le, hu₁₂, hu₂.le, hinc, hper, hE, fun F hF => ?_, fun F hF => ?_⟩
  · have hOm := buj_b_openSector_measurableSet (ξ := ξ) hα0 hαπ
    have hFO : Measurable ((buj_openSector ξ α).indicator F) := hF.indicator hOm
    calc ∫⁻ θ in Ioo u₁ u₂, F (ρ (circleMap 0 1 θ)) ∂V.measure
        = ∫⁻ θ in Ioc 0 (2 * π), (Ioo u₁ u₂).indicator (fun θ => F (ρ (circleMap 0 1 θ))) θ ∂V.measure := by
          rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            inter_eq_left.2 (show Ioo u₁ u₂ ⊆ Ioc 0 (2 * π) from
              fun θ hθ => ⟨hu₁.trans hθ.1, hθ.2.le.trans hu₂.le⟩)]
      _ = ∫⁻ θ in Ioc 0 (2 * π), (buj_openSector ξ α).indicator F (ρ (circleMap 0 1 θ)) ∂V.measure := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
          by_cases h : θ ∈ Ioo u₁ u₂
          · rw [indicator_of_mem h, indicator_of_mem ((hE θ hθ).2 h)]
          · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hE θ hθ).1 h'))]
      _ = ∫⁻ x in Ioo 0 (a + (t - s) + b),
            (buj_openSector ξ α).indicator F (buj_b_loop ξ α a b τ s t x) * buj_b_dens a τ s t x :=
          hint' _ hFO
      _ ≤ _ := buj_b_lintegral_loop_sector_le hcut F
  · rw [hint' F hF]
    exact buj_b_lintegral_loop_le hcut F

/-! ## Proved glue: no short crossings -/

/-- `Im (w^{π/α}) > 0` in the open sector `0 < arg w < α`. -/
theorem buj_im_cpow_pos {α : ℝ} (hα0 : 0 < α) {w : ℂ} (hw : w ≠ 0) (h1 : 0 < arg w) (h2 : arg w < α) :
    0 < (w ^ ((π / α : ℝ) : ℂ)).im := by
  rw [buj_im_cpow hw]
  have hβ : 0 < π / α := div_pos Real.pi_pos hα0
  refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hβ h1) ?_)
  calc π / α * arg w < π / α * α := mul_lt_mul_of_pos_left h2 hβ
    _ = π := div_mul_cancel₀ π hα0.ne'

/-- A function continuous on `Δ`, extended by `0`, is measurable. -/
theorem buj_measurable_indicator_unitDisc {g : ℂ → ℝ≥0∞} (hg : ContinuousOn g unitDisc) :
    Measurable (unitDisc.indicator g) := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  rw [← Set.piecewise_eq_indicator]
  exact hg.measurable_piecewise continuousOn_const hD

/-- `‖(a : ℂ) * ξ‖ = a` for `a > 0` and `‖ξ‖ = 1`. -/
theorem buj_norm_ofReal_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {a : ℝ} (ha : 0 < a) : ‖(a : ℂ) * ξ‖ = a := by
  rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

/-- The side lengths of a sector cut are `< 1`. -/
theorem buj_cut_side_lt_one {ξ : ℂ} {α a b r₀ s t : ℝ} {τ : ℝ → ℂ}
    (hcut : buj_IsSectorCut ξ α a b r₀ τ s t) : a < 1 ∧ b < 1 := by
  obtain ⟨⟨-, -, hξ, -, ha, hb, hst⟩, ⟨-, -, hτs, hτt⟩, -, hn, -⟩ := hcut
  have h1 := (hn s ⟨le_rfl, hst.le⟩).2
  have h2 := (hn t ⟨hst.le, le_rfl⟩).2
  rw [hτs, buj_norm_ofReal_mul hξ ha] at h1
  have hξ' : ‖ξ * exp (α * I)‖ = 1 := by rw [norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hτt, buj_norm_ofReal_mul hξ' hb] at h2
  exact ⟨h1, h2⟩

/-- **No short crossings.**

Setting: `φ` is holomorphic in `Δ`; there is a base point `z₀` with `φ(z₀) ≠ 0` and `B(z₀, δ)` in the open sector ∩
`B(0, r₀)`; the two sides of the sector have finite `√|φ|`-length.

Claim: sector cuts at height `r₀` cannot have `√|φ|`-lengths tending to `0`.

This is the boundary-uniqueness (BU) step of `lemma35_1` in Jensen form. For the `n`-th cut, with
`m = π Im((z₀/ξ)^{π/α})`:
1. `buj_sector_uniformizer` and `buj_sector_boundary_measure` produce the Riemann map and its boundary length measure;
2. `buj_harmonic_measure_lb` gives `u₂ - u₁ > m`;
3. `buj_JL` gives `2π(log |φ z₀| + 2 log δ) ≤ 2m log(ℓₙ/m) + 2M`;
4. `buj_close` finishes. -/
theorem buj_no_short_crossings {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {ξ z₀ : ℂ} {α r₀ δ : ℝ}
    (hδ : 0 < δ) (hz₀ : φ z₀ ≠ 0) (hball : ball z₀ δ ⊆ buj_openSector ξ α ∩ ball 0 r₀)
    (hL₁ : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * ξ)‖) < ⊤)
    (hL₂ : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * (ξ * exp (α * I)))‖) < ⊤)
    {a b s t : ℕ → ℝ} {τ : ℕ → ℝ → ℂ}
    (hcut : ∀ n, buj_IsSectorCut ξ α (a n) (b n) r₀ (τ n) (s n) (t n))
    (hlen : Tendsto (fun n => ∫⁻ x in Ioo (s n) (t n),
      ENNReal.ofReal (Real.sqrt ‖φ (τ n x)‖) * ‖deriv (τ n) x‖ₑ) atTop (𝓝 0)) : False := by
  obtain ⟨⟨hα0, hαπ, hξ, -, -, -, -⟩, -⟩ := hcut 0
  have hz₀mem := hball (mem_ball_self hδ)
  have hz₀S : z₀ ∈ buj_openSector ξ α := hz₀mem.1
  have hz₀r : ‖z₀‖ < r₀ := mem_ball_zero_iff.1 hz₀mem.2
  -- the harmonic-measure constant `c₀` and `m = π c₀`
  set c₀ : ℝ := ((z₀ / ξ) ^ ((π / α : ℝ) : ℂ)).im with hc₀def
  have hc₀ : 0 < c₀ := buj_im_cpow_pos hα0 hz₀S.1 hz₀S.2.1 hz₀S.2.2
  set m : ℝ := π * c₀ with hmdef
  have hm : 0 < m := mul_pos Real.pi_pos hc₀
  set η : ℝ := min 1 m with hηdef
  have hη : 0 < η := lt_min one_pos hm
  -- the weight `√|φ|` and its measurable version `f`
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt ‖φ z‖) with hgdef
  have hgc : ContinuousOn g unitDisc :=
    ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hφ.continuousOn.norm)
  set f : ℂ → ℝ≥0∞ := unitDisc.indicator g with hfdef
  have hfm : Measurable f := buj_measurable_indicator_unitDisc hgc
  have hfg : ∀ z, f z ≤ g z := fun z => indicator_le_self unitDisc g z
  -- the lengths
  set L₁ : ℝ≥0∞ := ∫⁻ r in Ioo (0 : ℝ) 1, g ((r : ℂ) * ξ) with hL₁def
  set L₂ : ℝ≥0∞ := ∫⁻ r in Ioo (0 : ℝ) 1, g ((r : ℂ) * (ξ * exp (α * I))) with hL₂def
  set M : ℝ := 1 + L₁.toReal + L₂.toReal with hMdef
  set Λ : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in Ioo (s n) (t n), g (τ n x) * ‖deriv (τ n) x‖ₑ with hΛdef
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, Λ n < ENNReal.ofReal (η / 2) :=
    eventually_atTop.1 (hlen.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hη))))
  have hΛlt : ∀ n, Λ (n + N) < ENNReal.ofReal (η / 2) := fun n => hN _ (Nat.le_add_left N n)
  have hΛfin : ∀ n, Λ (n + N) ≠ ⊤ := fun n => ne_top_of_lt (hΛlt n)
  have hΛle : ∀ n, (Λ (n + N)).toReal ≤ η / 2 := fun n =>
    ENNReal.toReal_le_of_le_ofReal (half_pos hη).le (hΛlt n).le
  set ℓ : ℕ → ℝ := fun n => (Λ (n + N)).toReal + η / 4 * (1 / ((n : ℝ) + 1)) with hℓdef
  have hfrac : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    ⟨by positivity, (div_le_one (by positivity)).2 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])⟩
  have hℓ0 : ∀ n, 0 < ℓ n := fun n =>
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (mul_pos (by linarith) (hfrac n).1)
  have hℓm : ∀ n, ℓ n ≤ m := by
    intro n
    have h1 := hΛle n
    have h2 : η / 4 * (1 / ((n : ℝ) + 1)) ≤ η / 4 := mul_le_of_le_one_right (by linarith) (hfrac n).2
    have h3 : η ≤ m := min_le_right _ _
    simp only [hℓdef]
    linarith
  have hℓlim : Tendsto ℓ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (Λ (n + N)).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ((tendsto_add_atTop_iff_nat N).2 hlen)
      rw [ENNReal.toReal_zero] at h
      exact h
    have h2 : Tendsto (fun n : ℕ => η / 4 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (η / 4)
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  -- the per-cut Jensen–length inequalities
  refine buj_close (K := 2 * π * (Real.log ‖φ z₀‖ + 2 * Real.log δ)) (M := M) hm hℓ0 hℓlim fun n => ?_
  have hcn := hcut (n + N)
  obtain ⟨ha1, hb1⟩ := buj_cut_side_lt_one hcn
  obtain ⟨ρ, hρ, hinj, hρ0, hρ1, hmapB, hmapCl, himg, harg, hsch⟩ :=
    buj_sector_uniformizer hcn hz₀S hz₀r
  obtain ⟨V, u₁, u₂, hu₁, hu₁₂, hu₂, hinc, hper, hE, hτpart, htot⟩ :=
    buj_sector_boundary_measure hcn hρ hinj hρ1 himg
  have hder : δ ≤ ‖deriv ρ 0‖ := hsch δ hδ hball
  have hder0 : deriv ρ 0 ≠ 0 := norm_pos_iff.1 (hδ.trans_le hder)
  have hon : ∀ θ : ℝ, ρ (circleMap 0 1 θ) ∈ unitDisc := fun θ =>
    hmapCl (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ))
  -- harmonic measure: `m < u₂ - u₁`
  have hdiv : Differentiable ℂ (fun w : ℂ => w / ξ) := differentiable_id.div_const ξ
  have hρξ : DiffContOnCl ℂ (fun z => ρ z / ξ) (ball 0 1) := hdiv.comp_diffContOnCl hρ
  have hin : ∀ z ∈ ball (0 : ℂ) 1, ρ z / ξ ≠ 0 ∧ 0 < arg (ρ z / ξ) ∧ arg (ρ z / ξ) < α :=
    fun z hz => hmapB hz
  have hcl : ∀ z ∈ sphere (0 : ℂ) 1, ‖ρ z / ξ‖ ≤ 1 ∧ 0 ≤ arg (ρ z / ξ) ∧ arg (ρ z / ξ) ≤ α := by
    intro z hz
    have hzD : ρ z ∈ unitDisc := hmapCl (sphere_subset_closedBall hz)
    refine ⟨?_, harg z hz⟩
    rw [norm_div, hξ, div_one]
    exact (mem_ball_zero_iff.1 hzD).le
  have hH := buj_harmonic_measure_lb hα0 hαπ hρξ hin hcl
  have hset : Ioc (0 : ℝ) (2 * π) ∩ {θ | ρ (circleMap 0 1 θ) / ξ ≠ 0 ∧ 0 < arg (ρ (circleMap 0 1 θ) / ξ) ∧
      arg (ρ (circleMap 0 1 θ) / ξ) < α} = Ioo u₁ u₂ := by
    ext θ
    constructor
    · rintro ⟨hθ, hθE⟩
      exact (hE θ hθ).1 hθE
    · intro hθ
      have hθI : θ ∈ Ioc (0 : ℝ) (2 * π) := ⟨hu₁.trans_lt hθ.1, hθ.2.le.trans hu₂⟩
      exact ⟨hθI, (hE θ hθI).2 hθ⟩
  rw [hset, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), hρ0] at hH
  have hgap : m < u₂ - u₁ := by
    have h2 : c₀ * (2 * π) ≤ u₂ - u₁ := by
      rw [← div_eq_inv_mul, le_div_iff₀ Real.two_pi_pos] at hH
      exact hH
    have h3 : c₀ * (2 * π) = 2 * (π * c₀) := by ring
    have h4 : 0 < π * c₀ := hm
    linarith
  -- the two length hypotheses of JL
  have hcongr : ∀ S : Set ℝ, ∫⁻ θ in S, g (ρ (circleMap 0 1 θ)) ∂V.measure =
      ∫⁻ θ in S, f (ρ (circleMap 0 1 θ)) ∂V.measure := fun S =>
    lintegral_congr fun θ => (indicator_of_mem (hon θ) g).symm
  have hτΛ : ∫⁻ x in Ioo (s (n + N)) (t (n + N)), f (τ (n + N) x) * ‖deriv (τ (n + N)) x‖ₑ ≤ Λ (n + N) :=
    lintegral_mono fun x => by gcongr; exact hfg _
  have harc : ∫⁻ θ in Ioo u₁ u₂, g (ρ (circleMap 0 1 θ)) ∂V.measure ≤ ENNReal.ofReal (ℓ n) := by
    rw [hcongr]
    refine ((hτpart f hfm).trans hτΛ).trans ?_
    rw [← ENNReal.ofReal_toReal (hΛfin n)]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_pos (by linarith) (hfrac n).1).le)
  have hrad₁ : ∫⁻ r in Ioo 0 (a (n + N)), f ((r : ℂ) * ξ) ≤ L₁ :=
    (lintegral_mono fun r => hfg _).trans (lintegral_mono_set (Ioo_subset_Ioo_right ha1.le))
  have hrad₂ : ∫⁻ r in Ioo 0 (b (n + N)), f ((r : ℂ) * (ξ * exp (α * I))) ≤ L₂ :=
    (lintegral_mono fun r => hfg _).trans (lintegral_mono_set (Ioo_subset_Ioo_right hb1.le))
  have htot' : ∫⁻ θ in Ioc 0 (2 * π), g (ρ (circleMap 0 1 θ)) ∂V.measure ≤ ENNReal.ofReal M := by
    rw [hcongr]
    refine (htot f hfm).trans ?_
    have hηle : ENNReal.ofReal (η / 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [min_le_left 1 m])
    have hM : ENNReal.ofReal M = 1 + L₁ + L₂ := by
      rw [hMdef, ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
        ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal hL₁.ne, ENNReal.ofReal_toReal hL₂.ne]
    rw [hM]
    exact add_le_add (add_le_add ((hτΛ.trans (hΛlt n).le).trans hηle) hrad₁) hrad₂
  -- Jensen–length for the `n`-th cut
  have hM0 : 0 ≤ M := by simp only [hMdef]; positivity
  have hJ := buj_JL ρ φ unitDisc V u₁ u₂ m (ℓ n) M hρ isOpen_ball hmapCl.image_subset hφ
    (by rw [hρ0]; exact hz₀) hder0 hinc hper hu₁ hu₂ hm hgap (hℓ0 n) (hℓm n) hM0 harc htot'
  rw [hρ0] at hJ
  have hlog : Real.log δ ≤ Real.log ‖deriv ρ 0‖ := Real.log_le_log hδ hder
  have hπ : 0 < 2 * π := Real.two_pi_pos
  nlinarith

end LiZhongQC
