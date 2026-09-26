import Mathlib
import LiZhongQC.Lemmas.KrausNehari

/-! Koebe foundations — development file for the NEW `LiZhongQC/Lemmas/Koebe.lean` (leader -a7, 2026-09-24).
Infrastructure (not book statements): Bieberbach's `|a₂| ≤ 2`, the Koebe 1/4 theorem and the growth theorem for
univalent functions in the unit disc, plus the Koebe function.  Used by S05 `thm5_3_teichmuller_modulus_theorem`
(the book's proof uses exactly Koebe 1/4 + growth), later by Mori's theorem and §15.

Route.  `|a₂| ≤ 2`: apply `kraus_nehari_coeff` (`Lemmas/KrausNehari.lean`, the area theorem for one coefficient) to
the odd square-root transform `h(z) = z √(f(z²)/z²)` (`f(z²)/z²` is holomorphic and zero-free on `Δ`, so it has a
holomorphic square root with value `1` at `0`; `h` is univalent and odd, `h‴(0) = 3 f″(0)/2`… i.e. `h‴(0) = 3a₂`,
`h″(0) = 0`, so `‖3a₂‖ ≤ 6`).  Koebe 1/4: for `w ∉ f(Δ)`, `f_w = w f/(w - f)` is univalent and normalized with
second coefficient `a₂ + 1/w`, so `|1/w| ≤ 4`.  Growth: Koebe transform `F(ζ) = (f((ζ+z)/(1+z̄ζ)) - f(z))/((1-|z|²) f'(z))`
gives `|z f''/f' - 2|z|²/(1-|z|²)| ≤ 4|z|/(1-|z|²)`, hence `|f'(z)| ≤ (1+r)/(1-r)³` and `|f(z)| ≤ r/(1-r)²`. -/

open Complex Set Metric Filter Topology

noncomputable section

namespace LiZhongQC

/-! ### `kb_` helpers: logarithms and square roots on a disc, nonvanishing derivative -/

/-- A zero-free holomorphic function on a disc has a holomorphic logarithm there. -/
theorem kb_exists_log {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball c r))
    (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c r) ∧ ∀ z ∈ ball c r, exp (L z) = g z := by
  rcases lt_or_ge 0 r with hr | hr
  · have hhd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) :=
      (hg.deriv isOpen_ball).div hg hne
    obtain ⟨L₀, hL₀⟩ := hhd.isExactOn_ball
    have hL₀d : DifferentiableOn ℂ L₀ (ball c r) := fun z hz =>
      (hL₀ z hz).differentiableAt.differentiableWithinAt
    -- `g · exp (-L₀)` has zero derivative, hence is constant on the disc
    have hφ : ∀ z ∈ ball c r, HasDerivAt (fun z => g z * exp (-L₀ z)) 0 z := by
      intro z hz
      have hgz := (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      have hexp : HasDerivAt (fun z => exp (-L₀ z)) (exp (-L₀ z) * -(deriv g z / g z)) z :=
        (hL₀ z hz).neg.cexp
      have hmul := hgz.mul hexp
      convert hmul using 1
      field_simp [hne z hz]
      ring
    have hc : c ∈ ball c r := mem_ball_self hr
    have hconst : ∀ z ∈ ball c r, g z * exp (-L₀ z) = g c * exp (-L₀ c) := fun z hz =>
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
        (fun z hz => (hφ z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hφ z hz).deriv) hz hc
    have hc0 : g c * exp (-L₀ c) ≠ 0 := mul_ne_zero (hne c hc) (exp_ne_zero _)
    refine ⟨fun z => L₀ z + log (g c * exp (-L₀ c)), hL₀d.add_const _, fun z hz => ?_⟩
    rw [exp_add, exp_log hc0, ← hconst z hz, mul_comm (g z), ← mul_assoc, ← exp_add,
      add_neg_cancel, exp_zero, one_mul]
  · refine ⟨fun _ => 0, differentiableOn_const _, fun z hz => ?_⟩
    rw [ball_eq_empty.2 hr] at hz
    exact absurd hz (Set.notMem_empty z)

/-- A zero-free holomorphic function on a disc has a holomorphic square root there. -/
theorem kb_exists_sqrt {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball c r))
    (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball c r) ∧ ∀ z ∈ ball c r, q z ^ 2 = g z := by
  obtain ⟨L, hL, hLg⟩ := kb_exists_log hg hne
  refine ⟨fun z => exp (L z / 2), (hL.div_const 2).cexp, fun z hz => ?_⟩
  have h2 : exp (L z / 2) ^ 2 = exp (L z) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h2, hLg z hz]

/-- A non-vanishing analytic function has an analytic `n`-th root near a point.  (Copied from
`RMT.exists_analyticAt_pow_eq`, which this Mathlib-only file does not import.) -/
theorem kb_exists_analyticAt_pow_eq {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k z₀ ∧ k z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, k z ^ n = h z := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hc
    exact h0 hc.symm
  have hu : AnalyticAt ℂ (fun z => h z / h z₀) z₀ := hh.div_const
  have hu1 : (fun z => h z / h z₀) z₀ ∈ slitPlane := by
    simp only [div_self h0]
    exact one_mem_slitPlane
  refine ⟨fun z => c * exp (log (h z / h z₀) / n), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hu.clog hu1).div_const.cexp)
  · exact mul_ne_zero hc0 (exp_ne_zero _)
  · have hev : ∀ᶠ z in 𝓝 z₀, h z ≠ 0 := hh.continuousAt.eventually_ne h0
    filter_upwards [hev] with z hz
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : (n : ℂ) * (log (h z / h z₀) / n) = log (h z / h z₀) := by
      field_simp
    rw [mul_pow, ← exp_nat_mul, e, exp_log (div_ne_zero hz h0), hc]
    field_simp

/-- Injective holomorphic maps have nonvanishing derivative.  (Copied from
`RMT.deriv_ne_zero_of_injOn`, which this Mathlib-only file does not import.) -/
theorem kb_deriv_ne_zero_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z : ℂ} (hz : z ∈ U) :
    deriv f z ≠ 0 := by
  revert z
  intro z₀ hz₀ hd
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt (hU.mem_nhds hz₀)
  have hga : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hfa.sub analyticAt_const
  -- the order of `f - f z₀` at `z₀` is finite
  have htop : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ ⊤ := by
    intro htop
    have hev := analyticOrderAt_eq_top.1 htop
    have hev' : ∀ᶠ z in 𝓝[≠] z₀, (f z - f z₀ = 0 ∧ z ∈ U) ∧ z ∈ ({z₀}ᶜ : Set ℂ) :=
      ((hev.and (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hgz, hzU⟩, hzne⟩ := hev'.exists
    exact hzne (hinj hzU hz₀ (sub_eq_zero.1 hgz))
  -- the order is at least two, since `f' (z₀) = 0`
  have hge : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z₀) z₀ := by
    have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) z₀ := by
      rw [Order.one_le_iff_ne_zero]
      exact hfa.deriv.analyticOrderAt_ne_zero.2 hd
    rw [← hfa.analyticOrderAt_deriv_add_one]
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by gcongr
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hn2 : 2 ≤ n := by
    rw [← hn] at hge
    exact_mod_cast hge
  obtain ⟨h, hha, hh0, hgev⟩ := hga.analyticOrderAt_eq_natCast.1 hn.symm
  obtain ⟨k, hka, hk0, hkev⟩ := kb_exists_analyticAt_pow_eq hha hh0 (by omega : 0 < n)
  -- `f - f z₀ = φⁿ` with `φ = (z - z₀) k` a local diffeomorphism at `z₀`
  set φ : ℂ → ℂ := fun z => (z - z₀) * k z with hφ
  have hφa : AnalyticAt ℂ φ z₀ := (analyticAt_id.sub analyticAt_const).mul hka
  have hφ0 : φ z₀ = 0 := by simp [hφ]
  have hφd : deriv φ z₀ = k z₀ := by
    have hder : HasDerivAt (fun z => (z - z₀) * k z) (1 * k z₀ + (z₀ - z₀) * deriv k z₀) z₀ :=
      ((hasDerivAt_id' z₀).sub_const z₀).mul hka.differentiableAt.hasDerivAt
    exact hder.deriv.trans (by ring)
  have hmap : map φ (𝓝 z₀) = 𝓝 (φ z₀) :=
    hφa.hasStrictDerivAt.map_nhds_eq (by rw [hφd]; exact hk0)
  have hSmem : {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 z₀ := by
    filter_upwards [hgev, hkev, hU.mem_nhds hz₀] with z hz hkz hzU
    refine ⟨?_, hzU⟩
    rw [hz]
    simp only [hφ, smul_eq_mul, mul_pow, hkz]
  have himg : φ '' {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 (0 : ℂ) := by
    rw [← hφ0, ← hmap]
    exact image_mem_map hSmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  -- two distinct points with the same `n`-th power
  have hprim : IsPrimitiveRoot (exp (2 * Real.pi * I / n)) n :=
    Complex.isPrimitiveRoot_exp n (by omega)
  have hω1 : exp (2 * Real.pi * I / n) ≠ 1 := hprim.ne_one (by omega)
  have hωn : exp (2 * Real.pi * I / n) ^ n = 1 := hprim.pow_eq_one
  have hωnorm : ‖exp (2 * Real.pi * I / n)‖ = 1 := hprim.norm'_eq_one (by omega)
  have hw0 : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hε).ne'
  have hnorm : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hw₁ : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := mem_ball_zero_iff.2 hnorm
  have hw₂ : ((ε / 2 : ℝ) : ℂ) * exp (2 * Real.pi * I / n) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_mul, hωnorm, mul_one]
    exact hnorm
  obtain ⟨z₁, ⟨hz₁, hz₁U⟩, hφz₁⟩ := hball hw₁
  obtain ⟨z₂, ⟨hz₂, hz₂U⟩, hφz₂⟩ := hball hw₂
  have hne : z₁ ≠ z₂ := by
    rintro rfl
    apply hω1
    have e : ((ε / 2 : ℝ) : ℂ) * exp (2 * Real.pi * I / n) = ((ε / 2 : ℝ) : ℂ) * 1 := by
      rw [mul_one, ← hφz₂, hφz₁]
    exact mul_left_cancel₀ hw0 e
  apply hne
  apply hinj hz₁U hz₂U
  have e₁ : f z₁ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₁, hφz₁]
  have e₂ : f z₂ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₂, hφz₂, mul_pow, hωn, mul_one]
  linear_combination e₁ - e₂

/-- The Koebe function `k(ζ) = ζ/(1-ζ)²`. -/
def koebeFn (ζ : ℂ) : ℂ := ζ / (1 - ζ) ^ 2

/-- A point of the open unit disc is not `1`: `1 - ζ ≠ 0` when `‖ζ‖ < 1`. -/
theorem kb_ka_one_sub_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : (1 : ℂ) - ζ ≠ 0 := by
  intro h
  have h1 : ζ = 1 := by linear_combination -h
  rw [h1, norm_one] at hζ
  exact lt_irrefl _ hζ

/-- The Koebe function is univalent in the unit disc. -/
theorem koebeFn_injOn : InjOn koebeFn (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  have hab1 : (1 : ℂ) - a * b ≠ 0 := by
    have hn : ‖a * b‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg a, norm_nonneg b]
    exact kb_ka_one_sub_ne_zero hn
  have e : a * (1 - b) ^ 2 = b * (1 - a) ^ 2 := by
    have h := hab
    simp only [koebeFn] at h
    rwa [div_eq_div_iff (pow_ne_zero 2 (kb_ka_one_sub_ne_zero ha'))
      (pow_ne_zero 2 (kb_ka_one_sub_ne_zero hb'))] at h
  have key : (a - b) * (1 - a * b) = 0 := by linear_combination e
  rcases mul_eq_zero.1 key with h | h
  · linear_combination h
  · exact absurd h hab1

/-- Componentwise form of `w (1-ζ)² = ζ`: real and imaginary parts. -/
theorem kb_ka_components {w ζ : ℂ} (h : w * (1 - ζ) ^ 2 = ζ) :
    w.re * ((1 - ζ.re) ^ 2 - ζ.im ^ 2) + 2 * w.im * (1 - ζ.re) * ζ.im = ζ.re ∧
      -2 * w.re * (1 - ζ.re) * ζ.im + w.im * ((1 - ζ.re) ^ 2 - ζ.im ^ 2) = ζ.im := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hre him
  constructor
  · linear_combination hre
  · linear_combination him

/-- Squared norm in coordinates: `‖ζ‖² = (Re ζ)² + (Im ζ)²`. -/
theorem kb_ka_sq_norm_eq (ζ : ℂ) : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- If `w (1-r)² = r` with `‖r‖ = 1`, then `w` is real and `≤ -1/4`. -/
theorem kb_ka_real_of_norm_one {w r : ℂ} (h : w * (1 - r) ^ 2 = r) (hr : ‖r‖ = 1) :
    w.im = 0 ∧ w.re ≤ -1 / 4 := by
  obtain ⟨R, I⟩ := kb_ka_components h
  have hn : r.re ^ 2 + r.im ^ 2 = 1 := by
    rw [← kb_ka_sq_norm_eq, hr, one_pow]
  have hx : |r.re| ≤ 1 := hr ▸ Complex.abs_re_le_norm r
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have hA : 2 * w.re * (r.re - 1) = 1 := by
    linear_combination r.re * R + r.im * I + (1 + w.im * r.im - w.re * (r.re - 2)) * hn
  have hB : 2 * w.im * (r.re - 1) = 0 := by
    linear_combination -r.im * R + r.re * I - (w.re * r.im + w.im * (r.re - 2)) * hn
  have hx1' : r.re - 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hA
    exact zero_ne_one hA
  have hb : w.im = 0 := by
    have : w.im * (2 * (r.re - 1)) = 0 := by linear_combination hB
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linear_combination h / 2) hx1'
  refine ⟨hb, ?_⟩
  have hlt : r.re - 1 < 0 := lt_of_le_of_ne (by linarith) hx1'
  have ha : w.re < 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hcon (by linarith : (0 : ℝ) ≤ 1 - r.re)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -w.re) (by linarith : (0 : ℝ) ≤ r.re + 1)]

/-- The Koebe function omits the slit `(-∞, -1/4]`. -/
theorem kb_ka_image_subset :
    koebeFn '' ball (0 : ℂ) 1 ⊆ {w : ℂ | ¬ (w.im = 0 ∧ w.re ≤ -1 / 4)} := by
  rintro _ ⟨ζ, hζ, rfl⟩ ⟨him, hre⟩
  have hζ' : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have h1 : (1 : ℂ) - ζ ≠ 0 := kb_ka_one_sub_ne_zero hζ'
  have hq : koebeFn ζ * (1 - ζ) ^ 2 = ζ := by
    simp only [koebeFn]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
  obtain ⟨R, I⟩ := kb_ka_components hq
  rw [him] at R I
  have hn : ζ.re ^ 2 + ζ.im ^ 2 < 1 := by
    rw [← kb_ka_sq_norm_eq]
    nlinarith [norm_nonneg ζ]
  have hx : |ζ.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm ζ) hζ'
  obtain ⟨hx1, hx2⟩ := abs_lt.1 hx
  by_cases hy : ζ.im = 0
  · rw [hy] at R
    have R' : (koebeFn ζ).re * (1 - ζ.re) ^ 2 = ζ.re := by linear_combination R
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -1 / 4 - (koebeFn ζ).re) (sq_nonneg (1 - ζ.re)),
      mul_pos (by linarith : (0 : ℝ) < 1 + ζ.re) (by linarith : (0 : ℝ) < 1 + ζ.re)]
  · have hI : -2 * (koebeFn ζ).re * (1 - ζ.re) = 1 := by
      have : (-2 * (koebeFn ζ).re * (1 - ζ.re) - 1) * ζ.im = 0 := by linear_combination I
      rcases mul_eq_zero.1 this with h | h
      · linear_combination h
      · exact absurd h hy
    have ha : (koebeFn ζ).re ≠ 0 := by
      intro h0
      rw [h0] at hI
      norm_num at hI
    have h4 : 4 * (koebeFn ζ).re ^ 2 * (ζ.re ^ 2 + ζ.im ^ 2 - 1) = 0 := by
      linear_combination (-4 * (koebeFn ζ).re) * R + (4 * (koebeFn ζ).re * ζ.re) * hI
    have h5 : ζ.re ^ 2 + ζ.im ^ 2 - 1 = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
          (by linear_combination h / 4)) ha
      · exact h
    linarith

/-- The Koebe function attains every value off the slit `(-∞, -1/4]`. -/
theorem kb_ka_image_supset :
    {w : ℂ | ¬ (w.im = 0 ∧ w.re ≤ -1 / 4)} ⊆ koebeFn '' ball (0 : ℂ) 1 := by
  intro w hw
  by_cases hw0 : w = 0
  · exact ⟨0, mem_ball_self one_pos, by simp [koebeFn, hw0]⟩
  -- a root of `w (1-r)² = r` in the closed disc is in the open disc and is a preimage
  have hkey : ∀ r : ℂ, w * (1 - r) ^ 2 = r → ‖r‖ ≤ 1 → w ∈ koebeFn '' ball (0 : ℂ) 1 := by
    intro r hr hr1
    have hlt : ‖r‖ < 1 := lt_of_le_of_ne hr1 (fun h => hw (kb_ka_real_of_norm_one hr h))
    refine ⟨r, mem_ball_zero_iff.2 hlt, ?_⟩
    simp only [koebeFn]
    exact ((eq_div_iff (pow_ne_zero 2 (kb_ka_one_sub_ne_zero hlt))).2 hr).symm
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1 + 4 * w) (by norm_num : 0 < 2)
  have h2w : (2 : ℂ) * w ≠ 0 := mul_ne_zero two_ne_zero hw0
  have hroot : ∀ r : ℂ, r * (2 * w) = 1 + 2 * w + s ∨ r * (2 * w) = 1 + 2 * w - s →
      w * (1 - r) ^ 2 = r := by
    intro r hr
    have h4 : (2 * w) ^ 2 * (w * (1 - r) ^ 2 - r) = 0 := by
      rcases hr with hr | hr
      · linear_combination (w * (r * (2 * w) + (1 + 2 * w + s) - 4 * w - 2)) * hr + w * hs
      · linear_combination (w * (r * (2 * w) + (1 + 2 * w - s) - 4 * w - 2)) * hr + w * hs
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) h2w
    · linear_combination h
  set r₁ : ℂ := (1 + 2 * w + s) / (2 * w) with hr₁
  set r₂ : ℂ := (1 + 2 * w - s) / (2 * w) with hr₂
  have e₁ : r₁ * (2 * w) = 1 + 2 * w + s := div_mul_cancel₀ _ h2w
  have e₂ : r₂ * (2 * w) = 1 + 2 * w - s := div_mul_cancel₀ _ h2w
  have hprod : r₁ * r₂ = 1 := by
    have h4 : (2 * w) ^ 2 * (r₁ * r₂ - 1) = 0 := by
      linear_combination (r₂ * (2 * w)) * e₁ + (1 + 2 * w + s) * e₂ - hs
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) h2w
    · linear_combination h
  have hnorm : ‖r₁‖ * ‖r₂‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  rcases le_or_gt ‖r₁‖ 1 with h | h
  · exact hkey r₁ (hroot r₁ (Or.inl e₁)) h
  · refine hkey r₂ (hroot r₂ (Or.inr e₂)) ?_
    nlinarith [norm_nonneg r₂]

/-- The Koebe function maps the unit disc onto `ℂ ∖ (-∞, -1/4]`. -/
theorem koebeFn_image : koebeFn '' ball (0 : ℂ) 1 = {w : ℂ | ¬ (w.im = 0 ∧ w.re ≤ -1 / 4)} := by
  exact Subset.antisymm kb_ka_image_subset kb_ka_image_supset

/-- The square of a point of the unit disc lies in the unit disc. -/
theorem kb_kb_sq_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_pow]
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

/-- A zero-free holomorphic `g` on the unit disc with `g 0 = 1` has a holomorphic square root `q`
there with `q 0 = 1`. -/
theorem kb_kb_exists_sqrt_one {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) (hg0 : g 0 = 1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball (0 : ℂ) 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, q z ^ 2 = g z) ∧
      q 0 = 1 := by
  obtain ⟨q₀, hq₀, hq₀g⟩ := kb_exists_sqrt hg hne
  have h00 : q₀ 0 ^ 2 = 1 := by rw [hq₀g 0 (mem_ball_self one_pos), hg0]
  refine ⟨fun z => q₀ 0 * q₀ z, hq₀.const_mul (q₀ 0), fun z hz => ?_, ?_⟩
  · show (q₀ 0 * q₀ z) ^ 2 = g z
    rw [mul_pow, h00, one_mul, hq₀g z hz]
  · show q₀ 0 * q₀ 0 = 1
    rw [← sq, h00]

/-- First derivative of the odd transform `z ↦ z q(z²)` on the unit disc. -/
theorem kb_kb_hasDerivAt_odd {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun z => z * q (z ^ 2)) (q (z ^ 2) + 2 * z ^ 2 * deriv q (z ^ 2)) z := by
  have hz2 := kb_kb_sq_mem_ball hz
  have hqd : HasDerivAt q (deriv q (z ^ 2)) (z ^ 2) :=
    (hq.differentiableAt (isOpen_ball.mem_nhds hz2)).hasDerivAt
  have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z :=
    (hasDerivAt_pow 2 z).congr_deriv (by norm_num)
  have hcomp : HasDerivAt (fun z => q (z ^ 2)) (deriv q (z ^ 2) * (2 * z)) z := hqd.comp z hsq
  have hmul := (hasDerivAt_id' z).fun_mul hcomp
  exact hmul.congr_deriv (by ring)

/-- Second derivative of the odd transform: the derivative of `z ↦ q(z²) + 2z² q'(z²)`. -/
theorem kb_kb_hasDerivAt_odd' {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun z => q (z ^ 2) + 2 * z ^ 2 * deriv q (z ^ 2))
      (6 * z * deriv q (z ^ 2) + 4 * z ^ 3 * deriv (deriv q) (z ^ 2)) z := by
  have hz2 := kb_kb_sq_mem_ball hz
  have hqd : HasDerivAt q (deriv q (z ^ 2)) (z ^ 2) :=
    (hq.differentiableAt (isOpen_ball.mem_nhds hz2)).hasDerivAt
  have hq'd : HasDerivAt (deriv q) (deriv (deriv q) (z ^ 2)) (z ^ 2) :=
    ((hq.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz2)).hasDerivAt
  have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z :=
    (hasDerivAt_pow 2 z).congr_deriv (by norm_num)
  have h1 : HasDerivAt (fun z => q (z ^ 2)) (deriv q (z ^ 2) * (2 * z)) z := hqd.comp z hsq
  have h2 : HasDerivAt (deriv q ∘ fun z : ℂ => z ^ 2) (deriv (deriv q) (z ^ 2) * (2 * z)) z :=
    hq'd.comp z hsq
  have h3 : HasDerivAt (fun z : ℂ => 2 * z ^ 2) (2 * (2 * z)) z := hsq.const_mul 2
  have h4 := h1.fun_add (h3.fun_mul h2)
  exact h4.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- Third derivative of the odd transform at `0`: the derivative at `0` of
`z ↦ 6z q'(z²) + 4z³ q''(z²)` is `6 q'(0)`. -/
theorem kb_kb_hasDerivAt_odd'' {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball (0 : ℂ) 1)) :
    HasDerivAt (fun z => 6 * z * deriv q (z ^ 2) + 4 * z ^ 3 * deriv (deriv q) (z ^ 2))
      (6 * deriv q 0) 0 := by
  have h0 : (0 : ℂ) ^ 2 ∈ ball (0 : ℂ) 1 := by simp
  have hq'd : HasDerivAt (deriv q) (deriv (deriv q) ((0 : ℂ) ^ 2)) ((0 : ℂ) ^ 2) :=
    ((hq.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hq''d : HasDerivAt (deriv (deriv q)) (deriv (deriv (deriv q)) ((0 : ℂ) ^ 2))
      ((0 : ℂ) ^ 2) :=
    (((hq.deriv isOpen_ball).deriv isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * 0) 0 :=
    (hasDerivAt_pow 2 (0 : ℂ)).congr_deriv (by norm_num)
  have h1 : HasDerivAt (deriv q ∘ fun z : ℂ => z ^ 2)
      (deriv (deriv q) ((0 : ℂ) ^ 2) * (2 * 0)) 0 :=
    hq'd.comp (0 : ℂ) hsq
  have h2 : HasDerivAt (deriv (deriv q) ∘ fun z : ℂ => z ^ 2)
      (deriv (deriv (deriv q)) ((0 : ℂ) ^ 2) * (2 * 0)) 0 :=
    hq''d.comp (0 : ℂ) hsq
  have h3 : HasDerivAt (fun z : ℂ => 6 * z) (6 * 1) 0 := (hasDerivAt_id' 0).const_mul 6
  have h4 : HasDerivAt (fun z : ℂ => 4 * z ^ 3) (4 * ((3 : ℕ) * (0 : ℂ) ^ (3 - 1))) 0 :=
    (hasDerivAt_pow 3 0).const_mul 4
  have h5 := (h3.fun_mul h1).fun_add (h4.fun_mul h2)
  exact h5.congr_deriv (by simp)

/-- **Bieberbach**: a normalized univalent `f` has `|a₂| ≤ 2`, i.e. `|f''(0)| ≤ 4`. -/
theorem koebe_bieberbach {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hinj : InjOn f (ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖deriv (deriv f) 0‖ ≤ 4 := by
  have hk : knHyp f := ⟨hf, hinj, h0, h1⟩
  have hb0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hDd : DifferentiableOn ℂ (dslope f 0) (ball (0 : ℂ) 1) := fun z hz =>
    (hk.analyticAt_dslope hz).differentiableAt.differentiableWithinAt
  obtain ⟨q, hq, hqD, hq0⟩ :=
    kb_kb_exists_sqrt_one hDd (fun z hz => hk.dslope_ne_zero hz) hk.dslope_zero
  have hqne : ∀ w ∈ ball (0 : ℂ) 1, q w ≠ 0 := by
    intro w hw hqw
    apply hk.dslope_ne_zero hw
    rw [← hqD w hw, hqw]
    ring
  -- `q'(0) = f''(0)/4`, from `2 q q' = (dslope f 0)'` and `(dslope f 0)'(0) = f''(0)/2`
  have hq'0 : deriv q 0 = deriv (deriv f) 0 / 4 := by
    have hev : (fun z => q z ^ 2) =ᶠ[𝓝 0] dslope f 0 :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hb0) hqD
    have hqd0 : HasDerivAt q (deriv q 0) 0 :=
      (hq.differentiableAt (isOpen_ball.mem_nhds hb0)).hasDerivAt
    have e1 : deriv (fun z => q z ^ 2) 0 = deriv (dslope f 0) 0 := hev.deriv_eq
    have e2 : deriv (fun z => q z ^ 2) 0 = 2 * q 0 * deriv q 0 := by
      rw [(hqd0.fun_pow 2).deriv]
      norm_num
    have e3 : deriv (dslope f 0) 0 = deriv (deriv f) 0 / 2 :=
      kn_deriv_dslope_same (hk.analyticAt hb0)
    rw [e2, hq0, e3] at e1
    linear_combination e1 / 2
  -- the odd square-root transform `h z = z q(z²)`, with `h(z)² = f(z²)`
  have hhd : DifferentiableOn ℂ (fun z => z * q (z ^ 2)) (ball (0 : ℂ) 1) := fun z hz =>
    (kb_kb_hasDerivAt_odd hq hz).differentiableAt.differentiableWithinAt
  have hh0 : (fun z : ℂ => z * q (z ^ 2)) 0 = 0 := by simp
  have hh1 : deriv (fun z => z * q (z ^ 2)) 0 = 1 := by
    rw [(kb_kb_hasDerivAt_odd hq hb0).deriv]
    simp [hq0]
  have hsq : ∀ z ∈ ball (0 : ℂ) 1, (z * q (z ^ 2)) ^ 2 = f (z ^ 2) := by
    intro z hz
    rw [mul_pow, hqD _ (kb_kb_sq_mem_ball hz), hk.mul_dslope (z ^ 2)]
  have hhinj : InjOn (fun z => z * q (z ^ 2)) (ball (0 : ℂ) 1) := by
    intro a ha b hb hab
    have hab' : a * q (a ^ 2) = b * q (b ^ 2) := hab
    have hf2 : f (a ^ 2) = f (b ^ 2) := by rw [← hsq a ha, ← hsq b hb, hab']
    have hab2 : a ^ 2 = b ^ 2 :=
      hinj (kb_kb_sq_mem_ball ha) (kb_kb_sq_mem_ball hb) hf2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hab2 with h | h
    · exact h
    · rw [h, neg_sq] at hab'
      have hb0' : b * q (b ^ 2) = 0 := by linear_combination (-1 / 2 : ℂ) * hab'
      rcases mul_eq_zero.1 hb0' with hb00 | hq00
      · rw [h, hb00, neg_zero]
      · exact absurd hq00 (hqne _ (kb_kb_sq_mem_ball hb))
  -- derivatives of `h`: `h''(0) = 0`, `h'''(0) = 6 q'(0)`
  have hdh : ∀ z ∈ ball (0 : ℂ) 1,
      deriv (fun z => z * q (z ^ 2)) z = q (z ^ 2) + 2 * z ^ 2 * deriv q (z ^ 2) :=
    fun z hz => (kb_kb_hasDerivAt_odd hq hz).deriv
  have hd2h : ∀ z ∈ ball (0 : ℂ) 1, deriv (deriv (fun z => z * q (z ^ 2))) z =
      6 * z * deriv q (z ^ 2) + 4 * z ^ 3 * deriv (deriv q) (z ^ 2) := by
    intro z hz
    have hev : deriv (fun z => z * q (z ^ 2)) =ᶠ[𝓝 z]
        fun z => q (z ^ 2) + 2 * z ^ 2 * deriv q (z ^ 2) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hdh
    rw [hev.deriv_eq]
    exact (kb_kb_hasDerivAt_odd' hq hz).deriv
  have hd2h0 : deriv (deriv (fun z => z * q (z ^ 2))) 0 = 0 := by
    rw [hd2h 0 hb0]
    simp
  have hd3h0 : deriv (deriv (deriv (fun z => z * q (z ^ 2)))) 0 = 6 * deriv q 0 := by
    have hev : deriv (deriv (fun z => z * q (z ^ 2))) =ᶠ[𝓝 0]
        fun z => 6 * z * deriv q (z ^ 2) + 4 * z ^ 3 * deriv (deriv q) (z ^ 2) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hb0) hd2h
    rw [hev.deriv_eq]
    exact (kb_kb_hasDerivAt_odd'' hq).deriv
  -- Kraus–Nehari for `h`: `‖(3/2) f''(0)‖ ≤ 6`
  have hKN := kraus_nehari_coeff hhd hhinj hh0 hh1
  rw [hd3h0, hd2h0, hq'0] at hKN
  have e : (3 : ℂ) * deriv (deriv f) 0 =
      2 * (6 * (deriv (deriv f) 0 / 4) - 3 / 2 * 0 ^ 2) := by ring
  have hn := congrArg norm e
  rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at hn
  linarith

/-- The omitted-value transform `w f/(w - f)` is holomorphic on the disc when `f` omits `w` there. -/
theorem kb_kc_transform_differentiableOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    {w : ℂ} (hw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w) :
    DifferentiableOn ℂ (fun z => w * f z / (w - f z)) (ball (0 : ℂ) 1) :=
  (hf.const_mul w).fun_div (hf.const_sub w) (fun z hz => sub_ne_zero.2 (hw z hz).symm)

/-- The omitted-value transform `w f/(w - f)` is injective on the disc when `f` is, `w ≠ 0`
and `f` omits `w` there. -/
theorem kb_kc_transform_injOn {f : ℂ → ℂ} (hinj : InjOn f (ball (0 : ℂ) 1))
    {w : ℂ} (hw0 : w ≠ 0) (hw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w) :
    InjOn (fun z => w * f z / (w - f z)) (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  apply hinj ha hb
  have hna : w - f a ≠ 0 := sub_ne_zero.2 (hw a ha).symm
  have hnb : w - f b ≠ 0 := sub_ne_zero.2 (hw b hb).symm
  have hab' : w * f a / (w - f a) = w * f b / (w - f b) := hab
  rw [div_eq_div_iff hna hnb] at hab'
  have h2 : w ^ 2 * (f a - f b) = 0 := by linear_combination hab'
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hw0
  · exact sub_eq_zero.1 h

/-- Derivative of the omitted-value transform: `(w f/(w - f))' = w² f'/(w - f)²` on the disc. -/
theorem kb_kc_transform_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    {w : ℂ} (hw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    deriv (fun z => w * f z / (w - f z)) z = w ^ 2 * deriv f z / (w - f z) ^ 2 := by
  have hfz : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hn : w - f z ≠ 0 := sub_ne_zero.2 (hw z hz).symm
  have hd := (hfz.const_mul w).fun_div (hfz.const_sub w) hn
  rw [hd.deriv]
  congr 1
  ring

/-- Second derivative of the omitted-value transform at `0`: it is `f''(0) + 2/w` when
`f 0 = 0` and `f' 0 = 1`. -/
theorem kb_kc_transform_deriv2 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {w : ℂ} (hw0 : w ≠ 0)
    (hw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w) :
    deriv (deriv (fun z => w * f z / (w - f z))) 0 = deriv (deriv f) 0 + 2 / w := by
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hev : deriv (fun z => w * f z / (w - f z)) =ᶠ[𝓝 0]
      fun z => w ^ 2 * deriv f z / (w - f z) ^ 2 := by
    filter_upwards [isOpen_ball.mem_nhds h0mem] with z hz
    exact kb_kc_transform_deriv hf hw hz
  rw [hev.deriv_eq]
  have hf0 : HasDerivAt f (deriv f 0) 0 :=
    (hf.differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
  have hf'0 : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
    ((hf.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
  have hden : HasDerivAt (fun z => (w - f z) ^ 2)
      (((2 : ℕ) : ℂ) * (w - f 0) ^ (2 - 1) * -deriv f 0) 0 :=
    (hf0.const_sub w).fun_pow 2
  have hn : (w - f 0) ^ 2 ≠ 0 := by
    rw [h0, sub_zero]
    exact pow_ne_zero 2 hw0
  have hd := (hf'0.const_mul (w ^ 2)).fun_div hden hn
  rw [hd.deriv, h0, h1]
  field_simp
  ring

/-- **Koebe 1/4 theorem** (normalized form). -/
theorem koebe_quarter {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hinj : InjOn f (ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ball (0 : ℂ) (1 / 4) ⊆ f '' ball (0 : ℂ) 1 := by
  intro w hw
  by_contra hwn
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hwn ⟨0, h0mem, h0⟩
  have hfw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w := fun z hz hfz => hwn ⟨z, hz, hfz⟩
  have hg0 : (fun z => w * f z / (w - f z)) 0 = 0 := by
    simp only [h0, mul_zero, zero_div]
  have hg1 : deriv (fun z => w * f z / (w - f z)) 0 = 1 := by
    rw [kb_kc_transform_deriv hf hfw h0mem, h0, h1, sub_zero, mul_one,
      div_self (pow_ne_zero 2 hw0)]
  have hB := koebe_bieberbach (kb_kc_transform_differentiableOn hf hfw)
    (kb_kc_transform_injOn hinj hw0 hfw) hg0 hg1
  rw [kb_kc_transform_deriv2 hf h0 h1 hw0 hfw] at hB
  have hA := koebe_bieberbach hf hinj h0 h1
  have hwlt : ‖w‖ < 1 / 4 := mem_ball_zero_iff.1 hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have h2w : ‖(2 : ℂ) / w‖ ≤ 8 := by
    calc ‖(2 : ℂ) / w‖ = ‖(deriv (deriv f) 0 + 2 / w) - deriv (deriv f) 0‖ := by
          rw [add_sub_cancel_left]
      _ ≤ ‖deriv (deriv f) 0 + 2 / w‖ + ‖deriv (deriv f) 0‖ := norm_sub_le _ _
      _ ≤ 4 + 4 := add_le_add hB hA
      _ = 8 := by norm_num
  rw [norm_div, Complex.norm_two, div_le_iff₀ hwpos] at h2w
  linarith

/-- The denominator `1 + z̄ζ` of the disc automorphism does not vanish for `|z|, |ζ| < 1`. -/
theorem kb_d1_denom_ne_zero {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) :
    1 + (starRingEnd ℂ) z * ζ ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) z * ζ = -1 := by linear_combination h
  have h2 : ‖(starRingEnd ℂ) z * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖z‖ * ‖ζ‖ ≤ ‖z‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [h1] at h2
  simp at h2

/-- The identity `|1 + z̄ζ|² - |ζ + z|² = (1 - |z|²)(1 - |ζ|²)`. -/
theorem kb_d1_norm_sq_identity (z ζ : ℂ) :
    ‖1 + (starRingEnd ℂ) z * ζ‖ ^ 2 - ‖ζ + z‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- The disc automorphism `ζ ↦ (ζ + z)/(1 + z̄ζ)` maps the unit disc into itself. -/
theorem kb_d1_mapsTo {z : ℂ} (hz : ‖z‖ < 1) :
    MapsTo (fun ζ => (ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro ζ hζ
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have hd := kb_d1_denom_ne_zero hz hζ1
  have hdpos : 0 < ‖1 + (starRingEnd ℂ) z * ζ‖ := norm_pos_iff.2 hd
  have hid := kb_d1_norm_sq_identity z ζ
  have hpos : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg z, norm_nonneg ζ]
  have hlt : ‖ζ + z‖ < ‖1 + (starRingEnd ℂ) z * ζ‖ := by
    have : ‖ζ + z‖ ^ 2 < ‖1 + (starRingEnd ℂ) z * ζ‖ ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  rw [mem_ball_zero_iff, norm_div, div_lt_one hdpos]
  exact hlt

/-- The disc automorphism `ζ ↦ (ζ + z)/(1 + z̄ζ)` is injective on the unit disc. -/
theorem kb_d1_injOn {z : ℂ} (hz : ‖z‖ < 1) :
    InjOn (fun ζ => (ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) (ball (0 : ℂ) 1) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ h
  have hd₁ := kb_d1_denom_ne_zero hz (mem_ball_zero_iff.1 hζ₁)
  have hd₂ := kb_d1_denom_ne_zero hz (mem_ball_zero_iff.1 hζ₂)
  simp only at h
  rw [div_eq_div_iff hd₁ hd₂] at h
  have hzz : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hne : (1 : ℂ) - (starRingEnd ℂ) z * z ≠ 0 := by
    rw [hzz]
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast this
  have hmul : (ζ₁ - ζ₂) * (1 - (starRingEnd ℂ) z * z) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hmul with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hne

/-- Derivative of the disc automorphism `T ζ = (ζ + z)/(1 + z̄ζ)`: `T'(ζ) = (1 - z̄z)/(1 + z̄ζ)²`. -/
theorem kb_d1_hasDerivAt_T (z ζ : ℂ) (hd : 1 + (starRingEnd ℂ) z * ζ ≠ 0) :
    HasDerivAt (fun ζ => (ζ + z) / (1 + (starRingEnd ℂ) z * ζ))
      ((1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2) ζ := by
  have h1 : HasDerivAt (fun ζ => ζ + z) 1 ζ := (hasDerivAt_id' ζ).add_const z
  have h2 : HasDerivAt (fun ζ => 1 + (starRingEnd ℂ) z * ζ) ((starRingEnd ℂ) z) ζ := by
    have := ((hasDerivAt_id' ζ).const_mul ((starRingEnd ℂ) z)).const_add 1
    simpa using this
  convert h1.div h2 hd using 1
  ring

/-- Derivative at `0` of `T'(ζ) = (1 - z̄z)/(1 + z̄ζ)²`: it is `-2 z̄ (1 - z̄z)`. -/
theorem kb_d1_hasDerivAt_T' (z : ℂ) :
    HasDerivAt (fun ζ => (1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2)
      (-(2 * (starRingEnd ℂ) z) * (1 - (starRingEnd ℂ) z * z)) 0 := by
  have h2 : HasDerivAt (fun ζ => 1 + (starRingEnd ℂ) z * ζ) ((starRingEnd ℂ) z) 0 := by
    have := ((hasDerivAt_id' (0 : ℂ)).const_mul ((starRingEnd ℂ) z)).const_add 1
    simpa using this
  have h3 := h2.pow 2
  have hd : (fun ζ => 1 + (starRingEnd ℂ) z * ζ) 0 ^ 2 ≠ 0 := by simp
  convert (hasDerivAt_const (0 : ℂ) (1 - (starRingEnd ℂ) z * z)).div h3 hd using 1
  simp
  ring

/-- **Koebe transform inequality**: for univalent `f` in the unit disc and `|z| < 1`,
`|(1 - |z|²) f''(z)/f'(z) - 2 z̄| ≤ 4` (Bieberbach's `|a₂| ≤ 2` for the Koebe transform
`F(ζ) = (f((ζ+z)/(1+z̄ζ)) - f(z))/((1-|z|²) f'(z))`, whose `F''(0)` is the left-hand side). -/
theorem kb_koebe_transform_ineq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hinj : InjOn f (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * (starRingEnd ℂ) z‖ ≤ 4 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hs_eq : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - (starRingEnd ℂ) z * z := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hs0 : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast this
  have hf'z : deriv f z ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj hz
  have hc0 : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z ≠ 0 := mul_ne_zero hs0 hf'z
  -- the disc automorphism `T` and its derivative
  have hTmaps := kb_d1_mapsTo hz1
  have hTinj := kb_d1_injOn hz1
  have hTd : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt (fun ζ => (ζ + z) / (1 + (starRingEnd ℂ) z * ζ))
      ((1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2) ζ := fun ζ hζ =>
    kb_d1_hasDerivAt_T z ζ (kb_d1_denom_ne_zero hz1 (mem_ball_zero_iff.1 hζ))
  have hT0 : ((0 : ℂ) + z) / (1 + (starRingEnd ℂ) z * 0) = z := by simp
  have hT'0 : (1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * 0) ^ 2
      = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs_eq]
    simp
  -- the Koebe transform
  have hTdiff : DifferentiableOn ℂ (fun ζ => (ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) (ball 0 1) :=
    fun ζ hζ => (hTd ζ hζ).differentiableAt.differentiableWithinAt
  have hFd : DifferentiableOn ℂ (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) (ball 0 1) :=
    ((hf.comp hTdiff hTmaps).sub_const (f z)).div_const _
  have hFinj : InjOn (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) (ball 0 1) := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ h
    have h' : f ((ζ₁ + z) / (1 + (starRingEnd ℂ) z * ζ₁))
        = f ((ζ₂ + z) / (1 + (starRingEnd ℂ) z * ζ₂)) := by
      simp only at h
      rw [div_left_inj' hc0] at h
      linear_combination h
    exact hTinj hζ₁ hζ₂ (hinj (hTmaps hζ₁) (hTmaps hζ₂) h')
  have hF0 : (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) 0 = 0 := by simp
  have hFder : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt (fun ζ => (f ((ζ + z) /
      (1 + (starRingEnd ℂ) z * ζ)) - f z) / (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z))
      (deriv f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) *
        ((1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2) /
        (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) ζ := by
    intro ζ hζ
    have hfT : HasDerivAt f (deriv f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)))
        ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) :=
      (hf.differentiableAt (isOpen_ball.mem_nhds (hTmaps hζ))).hasDerivAt
    exact ((hfT.comp ζ (hTd ζ hζ)).sub_const (f z)).div_const _
  have hF1 : deriv (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) 0 = 1 := by
    rw [(hFder 0 h0mem).deriv, hT0, hT'0, mul_comm]
    exact div_self hc0
  -- the second derivative at `0`
  have hev : deriv (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) =ᶠ[𝓝 0]
      fun ζ => deriv f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) *
        ((1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2) /
        (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z) := by
    filter_upwards [isOpen_ball.mem_nhds h0mem] with ζ hζ
    exact (hFder ζ hζ).deriv
  have hf'd : HasDerivAt (deriv f) (deriv (deriv f) z)
      (((0 : ℂ) + z) / (1 + (starRingEnd ℂ) z * 0)) := by
    rw [hT0]
    exact ((hf.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hG : HasDerivAt (fun ζ => deriv f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) *
        ((1 - (starRingEnd ℂ) z * z) / (1 + (starRingEnd ℂ) z * ζ) ^ 2) /
        (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) _ 0 :=
    ((hf'd.comp (0 : ℂ) (hTd 0 h0mem)).mul (kb_d1_hasDerivAt_T' z)).div_const _
  have hF2 : deriv (deriv (fun ζ => (f ((ζ + z) / (1 + (starRingEnd ℂ) z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z))) 0
      = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * (starRingEnd ℂ) z := by
    rw [hev.deriv_eq, hG.deriv]
    simp only [Function.comp_apply]
    rw [hT0, hT'0, ← hs_eq]
    field_simp
    ring
  rw [← hF2]
  exact koebe_bieberbach hFd hFinj hF0 hF1

/-- A zero-free holomorphic `f'` on the unit disc has a holomorphic logarithm `G`
(`exp ∘ G = f'`) with `G' = f''/f'`. -/
theorem kb_d2_log_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0) :
    ∃ G : ℂ → ℂ, (∀ w ∈ ball (0 : ℂ) 1, HasDerivAt G (deriv (deriv f) w / deriv f w) w) ∧
      ∀ w ∈ ball (0 : ℂ) 1, exp (G w) = deriv f w := by
  have hd : DifferentiableOn ℂ (deriv f) (ball (0 : ℂ) 1) := hf.deriv isOpen_ball
  obtain ⟨G, hG, hGe⟩ := kb_exists_log hd hne
  refine ⟨G, fun w hw => ?_, hGe⟩
  have hGw : HasDerivAt G (deriv G w) w :=
    (hG.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hexp : HasDerivAt (fun x => exp (G x)) (exp (G w) * deriv G w) w := hGw.cexp
  have hev : deriv f =ᶠ[𝓝 w] fun x => exp (G x) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with x hx
    exact (hGe x hx).symm
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) w) w :=
    (hd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have huniq : exp (G w) * deriv G w = deriv (deriv f) w :=
    (hexp.congr_of_eventuallyEq hev).unique hdf
  rw [hGe w hw] at huniq
  have hval : deriv (deriv f) w / deriv f w = deriv G w := by
    rw [← huniq]
    exact mul_div_cancel_left₀ _ (hne w hw)
  rw [hval]
  exact hGw

/-- Pointwise radial estimate: if `w = s z` with `0 ≤ s`, `s‖z‖ < 1` and
`‖(1 - ‖w‖²) a/b - 2 w̄‖ ≤ 4`, then `Re(a/b · z) ≤ ‖z‖/(1 + s‖z‖) + 3‖z‖/(1 - s‖z‖)`. -/
theorem kb_d2_re_bound {a b z : ℂ} {s : ℝ} (hs : 0 ≤ s) (hsr : s * ‖z‖ < 1)
    (h : ‖((1 - ‖(s : ℂ) * z‖ ^ 2 : ℝ) : ℂ) * a / b - 2 * (starRingEnd ℂ) ((s : ℂ) * z)‖ ≤ 4) :
    (a / b * z).re ≤ ‖z‖ / (1 + s * ‖z‖) + 3 * ‖z‖ / (1 - s * ‖z‖) := by
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hw : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hs]
  rw [hw, mul_div_assoc] at h
  have hr2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * (starRingEnd ℂ) ((s : ℂ) * z))).re
      = (1 - (s * ‖z‖) ^ 2) * (a / b * z).re - 2 * s * ‖z‖ ^ 2 := by
    rw [hr2]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hle : (z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * (starRingEnd ℂ) ((s : ℂ) * z))).re
      ≤ ‖z‖ * 4 := by
    calc _ ≤ ‖z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * (starRingEnd ℂ) ((s : ℂ) * z))‖ :=
          Complex.re_le_norm _
      _ = ‖z‖ * ‖((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * (starRingEnd ℂ) ((s : ℂ) * z)‖ :=
          norm_mul _ _
      _ ≤ ‖z‖ * 4 := mul_le_mul_of_nonneg_left h hr0
  have h1 : 0 < 1 + s * ‖z‖ := by have := mul_nonneg hs hr0; linarith
  have h2 : 0 < 1 - s * ‖z‖ := by linarith
  rw [div_add_div _ _ h1.ne' h2.ne', le_div_iff₀ (mul_pos h1 h2)]
  have e1 : (a / b * z).re * ((1 + s * ‖z‖) * (1 - s * ‖z‖))
      = (1 - (s * ‖z‖) ^ 2) * (a / b * z).re := by ring
  have e2 : ‖z‖ * (1 - s * ‖z‖) + (1 + s * ‖z‖) * (3 * ‖z‖) = ‖z‖ * 4 + 2 * s * ‖z‖ ^ 2 := by ring
  rw [e1, e2]
  linarith
/-- Radial integration of the log-derivative bound (via the logarithm `G` of `f'`):
`‖f'(s z)‖ ≤ (1 + s‖z‖)/(1 - s‖z‖)³` for `s ∈ [0,1]`. -/
theorem kb_d2_deriv_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h1 : deriv f 0 = 1) (hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hineq : ∀ z ∈ ball (0 : ℂ) 1,
      ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * (starRingEnd ℂ) z‖ ≤ 4)
    {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖deriv f ((s : ℂ) * z)‖ ≤ (1 + s * ‖z‖) / (1 - s * ‖z‖) ^ 3 := by
  obtain ⟨G, hGd, hGe⟩ := kb_d2_log_deriv hf hne
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hsr : ∀ t ∈ Icc (0 : ℝ) 1, t * ‖z‖ < 1 := fun t ht => by
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 hr0
      _ < 1 := by rw [one_mul]; exact hz
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ ball (0 : ℂ) 1 := fun t ht => by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_of_nonneg ht.1]
    exact hsr t ht
  -- `u(t) = Re G(t z)` has derivative `Re(z f''(tz)/f'(tz))`
  have hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (G ((t : ℂ) * z)).re)
      ((deriv (deriv f) ((t : ℂ) * z) / deriv f ((t : ℂ) * z) * z).re) t := fun t ht =>
    ((hGd _ (hmem t ht)).comp (t : ℂ) (hasDerivAt_mul_const z)).real_of_complex
  -- `φ(t) = log(1 + t r) - 3 log(1 - t r)` has derivative `r/(1 + t r) + 3 r/(1 - t r)`
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => Real.log (1 + t * ‖z‖) - 3 * Real.log (1 - t * ‖z‖))
      (‖z‖ / (1 + t * ‖z‖) + 3 * ‖z‖ / (1 - t * ‖z‖)) t := by
    intro t ht
    have ha : 0 < 1 + t * ‖z‖ := by have := mul_nonneg ht.1 hr0; linarith
    have hb : 0 < 1 - t * ‖z‖ := by linarith [hsr t ht]
    have d1 : HasDerivAt (fun t : ℝ => 1 + t * ‖z‖) ‖z‖ t :=
      (hasDerivAt_mul_const ‖z‖).const_add 1
    have d2 : HasDerivAt (fun t : ℝ => 1 - t * ‖z‖) (-‖z‖) t :=
      (hasDerivAt_mul_const ‖z‖).const_sub 1
    have := (d1.log ha.ne').fun_sub ((d2.log hb.ne').const_mul 3)
    convert this using 1
    ring
  -- the starting value `u(0) = log ‖f'(0)‖ = 0`
  have hG0 : (G 0).re = 0 := by
    have e := hGe 0 (mem_ball_self one_pos)
    rw [h1] at e
    have hn := congrArg (fun w : ℂ => ‖w‖) e
    simp only [Complex.norm_exp, norm_one] at hn
    exact Real.exp_eq_one_iff _ |>.1 hn
  have hstart : (fun t : ℝ => (G ((t : ℂ) * z)).re) 0 ≤
      (fun t : ℝ => Real.log (1 + t * ‖z‖) - 3 * Real.log (1 - t * ‖z‖)) 0 := by
    simp [hG0]
  have hfence := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun t : ℝ => (G ((t : ℂ) * z)).re)
    (f' := fun t => (deriv (deriv f) ((t : ℂ) * z) / deriv f ((t : ℂ) * z) * z).re)
    (B := fun t => Real.log (1 + t * ‖z‖) - 3 * Real.log (1 - t * ‖z‖))
    (B' := fun t => ‖z‖ / (1 + t * ‖z‖) + 3 * ‖z‖ / (1 - t * ‖z‖))
    (fun t ht => (hu t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hstart
    (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => kb_d2_re_bound (Ico_subset_Icc_self ht).1 (hsr t (Ico_subset_Icc_self ht))
      (hineq _ (hmem t (Ico_subset_Icc_self ht))))
  have hus := hfence hs
  have ha : 0 < 1 + s * ‖z‖ := by have := mul_nonneg hs.1 hr0; linarith
  have hb : 0 < 1 - s * ‖z‖ := by linarith [hsr s hs]
  have hexp : Real.exp (Real.log (1 + s * ‖z‖) - 3 * Real.log (1 - s * ‖z‖))
      = (1 + s * ‖z‖) / (1 - s * ‖z‖) ^ 3 := by
    have e3 : 3 * Real.log (1 - s * ‖z‖) = Real.log ((1 - s * ‖z‖) ^ 3) := by
      rw [Real.log_pow]; norm_num
    rw [Real.exp_sub, e3, Real.exp_log ha, Real.exp_log (pow_pos hb 3)]
  calc ‖deriv f ((s : ℂ) * z)‖ = Real.exp (G ((s : ℂ) * z)).re := by
        rw [← hGe _ (hmem s hs), Complex.norm_exp]
    _ ≤ Real.exp (Real.log (1 + s * ‖z‖) - 3 * Real.log (1 - s * ‖z‖)) := Real.exp_le_exp.2 hus
    _ = (1 + s * ‖z‖) / (1 - s * ‖z‖) ^ 3 := hexp

/-- **Growth from the distortion inequality**: if `f` is holomorphic in the unit disc with `f 0 = 0`,
`f' 0 = 1`, `f'` zero-free and `|(1 - |z|²) f''/f' - 2 z̄| ≤ 4` throughout the disc, then
`|f z| ≤ |z|/(1-|z|)²` (integrate `Re(z f''(sz)/f'(sz)) ≤ (2sr² + 4r)/(1 - s²r²)` along the radius to get
`|f'(sz)| ≤ (1+sr)/(1-sr)³`, then integrate `|f'|`). -/
theorem kb_growth_of_ineq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hineq : ∀ z ∈ ball (0 : ℂ) 1,
      ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * (starRingEnd ℂ) z‖ ≤ 4)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hsr : ∀ t ∈ Icc (0 : ℝ) 1, t * ‖z‖ < 1 := fun t ht => by
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 hr0
      _ < 1 := by rw [one_mul]; exact hz
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ ball (0 : ℂ) 1 := fun t ht => by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_of_nonneg ht.1]
    exact hsr t ht
  -- `F(t) = f(t z)` has derivative `f'(t z) z`
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => f ((t : ℂ) * z))
      (deriv f ((t : ℂ) * z) * z) t := fun t ht =>
    (((hf.differentiableAt (isOpen_ball.mem_nhds (hmem t ht))).hasDerivAt).comp (t : ℂ)
      (hasDerivAt_mul_const z)).comp_ofReal
  -- `B(t) = t r/(1 - t r)²` has derivative `r (1 + t r)/(1 - t r)³`
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t * ‖z‖ / (1 - t * ‖z‖) ^ 2)
      (‖z‖ * (1 + t * ‖z‖) / (1 - t * ‖z‖) ^ 3) t := by
    intro t ht
    have hb : 0 < 1 - t * ‖z‖ := by linarith [hsr t ht]
    have d1 : HasDerivAt (fun t : ℝ => t * ‖z‖) ‖z‖ t := hasDerivAt_mul_const ‖z‖
    have d2 : HasDerivAt (fun t : ℝ => (1 - t * ‖z‖) ^ 2)
        (((2 : ℕ) : ℝ) * (1 - t * ‖z‖) ^ (2 - 1) * (-‖z‖)) t :=
      ((hasDerivAt_mul_const ‖z‖).const_sub 1).fun_pow 2
    have := d1.fun_div d2 (pow_pos hb 2).ne'
    convert this using 1
    have hb' : 1 - t * ‖z‖ ≠ 0 := hb.ne'
    norm_num
    field_simp
    ring
  have hstart : ‖(fun t : ℝ => f ((t : ℂ) * z)) 0‖ ≤
      (fun t : ℝ => t * ‖z‖ / (1 - t * ‖z‖) ^ 2) 0 := by
    simp [h0]
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := 0) (b := 1)
    (f := fun t : ℝ => f ((t : ℂ) * z)) (f' := fun t => deriv f ((t : ℂ) * z) * z)
    (B := fun t : ℝ => t * ‖z‖ / (1 - t * ‖z‖) ^ 2)
    (B' := fun t => ‖z‖ * (1 + t * ‖z‖) / (1 - t * ‖z‖) ^ 3)
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hF t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hstart
    (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      have hd := kb_d2_deriv_bound hf h1 hne hineq hz (Ico_subset_Icc_self ht)
      rw [norm_mul]
      calc ‖deriv f ((t : ℂ) * z)‖ * ‖z‖ ≤ (1 + t * ‖z‖) / (1 - t * ‖z‖) ^ 3 * ‖z‖ :=
            mul_le_mul_of_nonneg_right hd hr0
        _ = ‖z‖ * (1 + t * ‖z‖) / (1 - t * ‖z‖) ^ 3 := by ring)
  have h := hfence (right_mem_Icc.2 zero_le_one)
  simpa using h


/-- **Growth theorem** (normalized form): `|f(z)| ≤ |z|/(1-|z|)²`. -/
theorem koebe_growth {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hinj : InjOn f (ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  exact kb_growth_of_ineq hf h0 h1 (fun w hw => kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj hw)
    (fun w hw => kb_koebe_transform_ineq hf hinj hw) hz

/-- Normalization of a univalent `ψ` with `ψ 0 = 0`: `ψ'(0) ≠ 0`, and `ψ / ψ'(0)` is holomorphic,
univalent and normalized (`0 ↦ 0`, derivative `1` at `0`) in the unit disc. -/
theorem kb_ka_normalize {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    (hinj : InjOn ψ (ball (0 : ℂ) 1)) (h0 : ψ 0 = 0) :
    deriv ψ 0 ≠ 0 ∧ DifferentiableOn ℂ (fun z => ψ z / deriv ψ 0) (ball (0 : ℂ) 1) ∧
      InjOn (fun z => ψ z / deriv ψ 0) (ball (0 : ℂ) 1) ∧ (fun z => ψ z / deriv ψ 0) 0 = 0 ∧
      deriv (fun z => ψ z / deriv ψ 0) 0 = 1 := by
  have ha : deriv ψ 0 ≠ 0 :=
    kb_deriv_ne_zero_of_injOn isOpen_ball hψ hinj (mem_ball_self one_pos)
  refine ⟨ha, hψ.div_const _, ?_, by simp only [h0, zero_div], ?_⟩
  · intro z hz z' hz' h
    exact hinj hz hz' ((div_left_inj' ha).1 h)
  · rw [deriv_div_const, div_self ha]

/-- Koebe 1/4, unnormalized: a univalent `ψ` with `ψ 0 = 0` omitting `w` has `|ψ'(0)| ≤ 4|w|`. -/
theorem koebe_quarter_of_not_mem {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    (hinj : InjOn ψ (ball (0 : ℂ) 1)) (h0 : ψ 0 = 0) {w : ℂ} (hw : w ∉ ψ '' ball (0 : ℂ) 1) :
    ‖deriv ψ 0‖ ≤ 4 * ‖w‖ := by
  obtain ⟨ha, hf, hfinj, hf0, hf1⟩ := kb_ka_normalize hψ hinj h0
  have hmem : w / deriv ψ 0 ∉ ball (0 : ℂ) (1 / 4) := by
    intro hball
    obtain ⟨z, hz, hfz⟩ := koebe_quarter hf hfinj hf0 hf1 hball
    exact hw ⟨z, hz, (div_left_inj' ha).1 hfz⟩
  rw [mem_ball_zero_iff, not_lt, norm_div, le_div_iff₀ (norm_pos_iff.2 ha)] at hmem
  linarith

/-- Growth theorem, unnormalized: `|ψ(ζ)| ≤ |ψ'(0)| |ζ|/(1-|ζ|)²` for univalent `ψ` with `ψ 0 = 0`. -/
theorem koebe_growth_scaled {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    (hinj : InjOn ψ (ball (0 : ℂ) 1)) (h0 : ψ 0 = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖ψ ζ‖ ≤ ‖deriv ψ 0‖ * ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := by
  obtain ⟨ha, hf, hfinj, hf0, hf1⟩ := kb_ka_normalize hψ hinj h0
  have hg := koebe_growth hf hfinj hf0 hf1 hζ
  simp only [norm_div] at hg
  rw [div_le_iff₀ (norm_pos_iff.2 ha)] at hg
  calc ‖ψ ζ‖ ≤ ‖ζ‖ / (1 - ‖ζ‖) ^ 2 * ‖deriv ψ 0‖ := hg
    _ = ‖deriv ψ 0‖ * ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := by ring

end LiZhongQC
