import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Value distribution of the Weierstrass `℘` function

For a period pair `L` normalized by `L.ω₁ = 1` and `0 < L.ω₂.im`, this file proves that the
Weierstrass function `℘ = ℘[L]` (Mathlib's `PeriodPair.weierstrassP`) takes each value exactly
at the points `±z` modulo `L`, and that its three half-period values are pairwise distinct.

## Main results

* `LiZhongQC.weierstrassP_eq_iff_of_one`: for `z, z' ∉ L`,
  `℘ z = ℘ z' ↔ z - z' ∈ L ∨ z + z' ∈ L`.  The lattice points have to be excluded, because
  Mathlib's `℘` takes the junk value `0` on `L` (`PeriodPair.weierstrassP_coe`).
* `LiZhongQC.half_period_values_ne`: `℘(ω₁/2)`, `℘(ω₂/2)` and `℘((ω₁+ω₂)/2)` are pairwise
  distinct.

## Proof outline

1. *The rectangle residue primitive* (`wv_integral_boundary_rect_inv_sub`): if `p` lies inside
   an axis-parallel rectangle, the boundary integral of `(ζ - p)⁻¹` is `2πi`; each side is
   integrated with an explicit branch of `Complex.log`.
2. *The argument principle on a rectangle* (`wv_rectBdry_logDeriv`): if `f` is meromorphic on a
   closed rectangle and analytic and zero-free on its frame, the boundary integral of `f'/f` is
   `2πi` times the sum of the divisor of `f` on the rectangle.  The zeros and poles are factored
   out (`MeromorphicOn.extract_zeros_poles`), the remaining factor is handled by Cauchy's theorem
   (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), and the logarithmic
   derivative `n (ζ - p)⁻¹` of each factor `(ζ - p) ^ n` by the residue primitive.
3. *Periodicity*: the boundary integral of a doubly periodic function over a fundamental
   rectangle vanishes (`wv_rectBdry_periodic`); since the zeros and poles of `℘ - c` form a
   countable set, some fundamental rectangle has a frame avoiding all of them
   (`wv_exists_good_rect`).  Hence the divisor of `℘ - c` on that rectangle sums to `0`.
4. *Counting*: in a half-open fundamental box, `℘ - c` has exactly one pole, a double one, so its
   zeros there have total multiplicity `2`.  For `c = ℘ z`, the representatives of `z` and `-z`
   are zeros (a double zero when they coincide, since `℘'` vanishes there), so a zero `z'` with
   `z - z' ∉ L` and `z + z' ∉ L` would be one zero too many.
5. The half-period values are distinct because the differences and sums of distinct half periods
   are not lattice points (`wv_notMem_lattice_of_rat`).
-/

namespace LiZhongQC

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real Interval

/-! ### The rectangle residue primitive -/

/-- A primitive along a horizontal segment: for `c.im ≠ 0`,
`∫ x in a..b, (x + c)⁻¹ = log (b + c) - log (a + c)`. -/
theorem wv_integral_inv_horizontal {a b : ℝ} {c : ℂ} (hc : c.im ≠ 0) :
    ∫ x in a..b, ((x : ℂ) + c)⁻¹ = log (b + c) - log (a + c) := by
  have hslit : ∀ x : ℝ, (x : ℂ) + c ∈ slitPlane := fun x => by
    rw [mem_slitPlane_iff]; right; simpa using hc
  have hne : ∀ x : ℝ, (x : ℂ) + c ≠ 0 := fun x => slitPlane_ne_zero (hslit x)
  have hderiv : ∀ x ∈ [[a, b]],
      HasDerivAt (fun t : ℝ => log ((t : ℂ) + c)) (((x : ℂ) + c)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + c) 1 x := (hasDerivAt_id x).ofReal_comp.add_const c
    simpa [one_div] using h1.clog_real (hslit x)
  have hcont : Continuous fun x : ℝ => ((x : ℂ) + c)⁻¹ :=
    (continuous_ofReal.add continuous_const).inv₀ hne
  exact integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- A primitive along a vertical segment in the right half-plane: for `0 < c.re`,
`I • ∫ y in a..b, (c + y I)⁻¹ = log (c + b I) - log (c + a I)`. -/
theorem wv_integral_inv_vertical_pos {a b : ℝ} {c : ℂ} (hc : 0 < c.re) :
    I • ∫ y in a..b, (c + (y : ℂ) * I)⁻¹ = log (c + b * I) - log (c + a * I) := by
  have hslit : ∀ y : ℝ, c + (y : ℂ) * I ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]; left; simpa using hc
  have hne : ∀ y : ℝ, c + (y : ℂ) * I ≠ 0 := fun y => slitPlane_ne_zero (hslit y)
  have hderiv : ∀ y ∈ [[a, b]],
      HasDerivAt (fun t : ℝ => log (c + (t : ℂ) * I)) (I * (c + (y : ℂ) * I)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => c + (t : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add c
    simpa [div_eq_mul_inv] using h1.clog_real (hslit y)
  have hcont : Continuous fun y : ℝ => I * (c + (y : ℂ) * I)⁻¹ :=
    continuous_const.mul ((continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  exact integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- A primitive along a vertical segment in the left half-plane: for `c.re < 0`,
`I • ∫ y in a..b, (c + y I)⁻¹ = log (-(c + b I)) - log (-(c + a I))`. -/
theorem wv_integral_inv_vertical_neg {a b : ℝ} {c : ℂ} (hc : c.re < 0) :
    I • ∫ y in a..b, (c + (y : ℂ) * I)⁻¹ = log (-(c + b * I)) - log (-(c + a * I)) := by
  have hslit : ∀ y : ℝ, -(c + (y : ℂ) * I) ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]; left; simp; linarith
  have hne : ∀ y : ℝ, c + (y : ℂ) * I ≠ 0 := fun y h => slitPlane_ne_zero (hslit y) (by simp [h])
  have hderiv : ∀ y ∈ [[a, b]],
      HasDerivAt (fun t : ℝ => log (-(c + (t : ℂ) * I))) (I * (c + (y : ℂ) * I)⁻¹) y := by
    intro y _
    have h0 : HasDerivAt (fun t : ℝ => c + (t : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add c
    have h1 : HasDerivAt (fun t : ℝ => -(c + (t : ℂ) * I)) (-I) y := h0.neg
    have h2 := h1.clog_real (hslit y)
    convert h2 using 1
    field_simp [hne y]
  have hcont : Continuous fun y : ℝ => I * (c + (y : ℂ) * I)⁻¹ :=
    continuous_const.mul ((continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  exact integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- `log D - log (-D) = π I` when `0 < D.im`. -/
theorem wv_log_sub_log_neg_of_im_pos {D : ℂ} (hD : 0 < D.im) : log D - log (-D) = π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hD]

/-- `log A - log (-A) = -(π I)` when `A.im < 0`. -/
theorem wv_log_sub_log_neg_of_im_neg {A : ℂ} (hA : A.im < 0) : log A - log (-A) = -(π * I) := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg hA]

/-- **The residue of `(ζ - p)⁻¹` on a rectangle.**  If `p` lies in the open rectangle with lower
left corner `z` and upper right corner `w`, the boundary integral of `(ζ - p)⁻¹` (in the
convention of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) is `2π I`. -/
theorem wv_integral_boundary_rect_inv_sub {z w p : ℂ} (hre₁ : z.re < p.re) (hre₂ : p.re < w.re)
    (him₁ : z.im < p.im) (him₂ : p.im < w.im) :
    (∫ x : ℝ in z.re..w.re, ((x + z.im * I) - p)⁻¹) -
        (∫ x : ℝ in z.re..w.re, ((x + w.im * I) - p)⁻¹) +
        I • (∫ y : ℝ in z.im..w.im, ((w.re + y * I) - p)⁻¹) -
        I • ∫ y : ℝ in z.im..w.im, ((z.re + y * I) - p)⁻¹ = 2 * π * I := by
  have hB : ∫ x : ℝ in z.re..w.re, ((x + z.im * I) - p)⁻¹ =
      log (w.re + (z.im * I - p)) - log (z.re + (z.im * I - p)) := by
    have := wv_integral_inv_horizontal (a := z.re) (b := w.re) (c := z.im * I - p)
      (by simp; linarith)
    simpa [add_sub_assoc] using this
  have hT : ∫ x : ℝ in z.re..w.re, ((x + w.im * I) - p)⁻¹ =
      log (w.re + (w.im * I - p)) - log (z.re + (w.im * I - p)) := by
    have := wv_integral_inv_horizontal (a := z.re) (b := w.re) (c := w.im * I - p)
      (by simp; linarith)
    simpa [add_sub_assoc] using this
  have hR : I • (∫ y : ℝ in z.im..w.im, ((w.re + y * I) - p)⁻¹) =
      log ((w.re - p) + w.im * I) - log ((w.re - p) + z.im * I) := by
    have := wv_integral_inv_vertical_pos (a := z.im) (b := w.im) (c := w.re - p)
      (by simp; linarith)
    rw [← this]; congr 2; ext y; ring_nf
  have hL : I • (∫ y : ℝ in z.im..w.im, ((z.re + y * I) - p)⁻¹) =
      log (-((z.re - p) + w.im * I)) - log (-((z.re - p) + z.im * I)) := by
    have := wv_integral_inv_vertical_neg (a := z.im) (b := w.im) (c := z.re - p)
      (by simp; linarith)
    rw [← this]; congr 2; ext y; ring_nf
  rw [hB, hT, hR, hL]
  set A : ℂ := (z.re - p) + z.im * I
  set D : ℂ := (z.re - p) + w.im * I
  have hA : A.im < 0 := by simp [A]; linarith
  have hD : 0 < D.im := by simp [D]; linarith
  have e1 : (z.re : ℂ) + (z.im * I - p) = A := by simp only [A]; ring
  have e2 : (z.re : ℂ) + (w.im * I - p) = D := by simp only [D]; ring
  have e3 : (w.re : ℂ) + (z.im * I - p) = (w.re - p) + z.im * I := by ring
  have e4 : (w.re : ℂ) + (w.im * I - p) = (w.re - p) + w.im * I := by ring
  rw [e1, e2, e3, e4]
  have k1 := wv_log_sub_log_neg_of_im_pos hD
  have k2 := wv_log_sub_log_neg_of_im_neg hA
  linear_combination k1 - k2

/-! ### Rectangle boundary integral: notation and linearity -/

/-- The boundary integral of `f` over the rectangle with opposite corners `z` and `w`, in the
convention of Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (positively
oriented when `z.re < w.re` and `z.im < w.im`). -/
noncomputable def wv_rectBdry (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-- The closed rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]` with opposite corners `z` and `w`. -/
def wv_rectK (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The open rectangle `Ioo z.re w.re ×ℂ Ioo z.im w.im`. -/
def wv_rectO (z w : ℂ) : Set ℂ := Ioo z.re w.re ×ℂ Ioo z.im w.im

/-- The frame of the rectangle: the closed rectangle minus the open one (its topological boundary
when `z.re < w.re` and `z.im < w.im`). -/
def wv_rectF (z w : ℂ) : Set ℂ := wv_rectK z w \ wv_rectO z w

/-- The bottom side `x + (z.im) I`, `x ∈ [[z.re, w.re]]`, lies on the frame. -/
theorem wv_bot_mem_rectF {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + z.im * I ∈ wv_rectF z w := by
  refine ⟨?_, ?_⟩
  · simp only [wv_rectK, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hx, left_mem_uIcc⟩
  · intro h
    have := h.2.1
    simp at this

/-- The top side `x + (w.im) I`, `x ∈ [[z.re, w.re]]`, lies on the frame. -/
theorem wv_top_mem_rectF {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + w.im * I ∈ wv_rectF z w := by
  refine ⟨?_, ?_⟩
  · simp only [wv_rectK, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hx, right_mem_uIcc⟩
  · intro h
    have := h.2.2
    simp at this

/-- The right side `w.re + y I`, `y ∈ [[z.im, w.im]]`, lies on the frame. -/
theorem wv_right_mem_rectF {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + y * I ∈ wv_rectF z w := by
  refine ⟨?_, ?_⟩
  · simp only [wv_rectK, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨right_mem_uIcc, hy⟩
  · intro h
    have := h.1.2
    simp at this

/-- The left side `z.re + y I`, `y ∈ [[z.im, w.im]]`, lies on the frame. -/
theorem wv_left_mem_rectF {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + y * I ∈ wv_rectF z w := by
  refine ⟨?_, ?_⟩
  · simp only [wv_rectK, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨left_mem_uIcc, hy⟩
  · intro h
    have := h.1.1
    simp at this

/-- A function continuous on the frame is interval integrable along the bottom side. -/
theorem wv_ii_bot {z w : ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f (wv_rectF z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re :=
  (hf.comp (continuous_ofReal.add continuous_const).continuousOn
    fun _ hx => wv_bot_mem_rectF hx).intervalIntegrable

/-- A function continuous on the frame is interval integrable along the top side. -/
theorem wv_ii_top {z w : ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f (wv_rectF z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (continuous_ofReal.add continuous_const).continuousOn
    fun _ hx => wv_top_mem_rectF hx).intervalIntegrable

/-- A function continuous on the frame is interval integrable along the right side. -/
theorem wv_ii_right {z w : ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f (wv_rectF z w)) :
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    fun _ hy => wv_right_mem_rectF hy).intervalIntegrable

/-- A function continuous on the frame is interval integrable along the left side. -/
theorem wv_ii_left {z w : ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f (wv_rectF z w)) :
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    fun _ hy => wv_left_mem_rectF hy).intervalIntegrable

/-- The rectangle boundary integral only depends on the values of the integrand on the frame. -/
theorem wv_rectBdry_congr {z w : ℂ} {f g : ℂ → ℂ} (h : EqOn f g (wv_rectF z w)) :
    wv_rectBdry f z w = wv_rectBdry g z w := by
  unfold wv_rectBdry
  rw [integral_congr fun x hx => h (wv_bot_mem_rectF hx),
    integral_congr fun x hx => h (wv_top_mem_rectF hx),
    integral_congr fun y hy => h (wv_right_mem_rectF hy),
    integral_congr fun y hy => h (wv_left_mem_rectF hy)]

/-- The rectangle boundary integral is additive on functions continuous on the frame. -/
theorem wv_rectBdry_add {z w : ℂ} {f g : ℂ → ℂ} (hf : ContinuousOn f (wv_rectF z w))
    (hg : ContinuousOn g (wv_rectF z w)) :
    wv_rectBdry (fun ζ => f ζ + g ζ) z w = wv_rectBdry f z w + wv_rectBdry g z w := by
  unfold wv_rectBdry
  rw [integral_add (wv_ii_bot hf) (wv_ii_bot hg), integral_add (wv_ii_top hf) (wv_ii_top hg),
    integral_add (wv_ii_right hf) (wv_ii_right hg),
    integral_add (wv_ii_left hf) (wv_ii_left hg)]
  simp only [smul_add]
  ring

/-- The rectangle boundary integral commutes with multiplication by a constant. -/
theorem wv_rectBdry_const_mul {z w : ℂ} (c : ℂ) (f : ℂ → ℂ) :
    wv_rectBdry (fun ζ => c * f ζ) z w = c * wv_rectBdry f z w := by
  unfold wv_rectBdry
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- The rectangle boundary integral of a finite sum of functions continuous on the frame is the
sum of their boundary integrals. -/
theorem wv_rectBdry_sum {z w : ℂ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (wv_rectF z w)) :
    wv_rectBdry (fun ζ => ∑ i ∈ s, f i ζ) z w = ∑ i ∈ s, wv_rectBdry (f i) z w := by
  unfold wv_rectBdry
  rw [integral_finsetSum fun i hi => wv_ii_bot (hf i hi),
    integral_finsetSum fun i hi => wv_ii_top (hf i hi),
    integral_finsetSum fun i hi => wv_ii_right (hf i hi),
    integral_finsetSum fun i hi => wv_ii_left (hf i hi)]
  simp only [Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-! ### The argument principle on a rectangle -/

/-- The closed rectangle is compact. -/
theorem wv_isCompact_rectK (z w : ℂ) : IsCompact (wv_rectK z w) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- Every point of the frame of a nondegenerate rectangle is an accumulation point of the closed
rectangle. -/
theorem wv_frequently_rectK {z w ζ : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hζ : ζ ∈ wv_rectF z w) : ∃ᶠ x in 𝓝[≠] ζ, x ∈ wv_rectK z w := by
  have hcl : closure (wv_rectO z w) = wv_rectK z w := by
    rw [wv_rectO, closure_reProdIm, closure_Ioo hre.ne, closure_Ioo him.ne]
    simp only [wv_rectK, uIcc_of_le hre.le, uIcc_of_le him.le]
  have h1 : ∃ᶠ x in 𝓝 ζ, x ∈ wv_rectO z w := mem_closure_iff_frequently.mp (hcl ▸ hζ.1)
  rw [frequently_nhdsWithin_iff]
  exact h1.mono fun x hx => ⟨hcl ▸ subset_closure hx, fun hxz => hζ.2 (hxz ▸ hx)⟩

/-- **The argument principle on a rectangle.**  Let `f` be meromorphic on the closed rectangle
`wv_rectK z w` (with `z.re < w.re`, `z.im < w.im`), of finite meromorphic order at every point
of it, and analytic and nonvanishing on the frame.  Then the boundary integral of `logDeriv f` is
`2π I` times the sum of the divisor of `f` on the rectangle (zeros minus poles, counted with
multiplicity). -/
theorem wv_rectBdry_logDeriv {f : ℂ → ℂ} {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hf : MeromorphicOn f (wv_rectK z w))
    (hord : ∀ u ∈ wv_rectK z w, meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ ζ ∈ wv_rectF z w, AnalyticAt ℂ f ζ ∧ f ζ ≠ 0) :
    wv_rectBdry (logDeriv f) z w = 2 * π * I *
      ∑ p ∈ ((MeromorphicOn.divisor f (wv_rectK z w)).finiteSupport
          (wv_isCompact_rectK z w)).toFinset,
        (MeromorphicOn.divisor f (wv_rectK z w) p : ℂ) := by
  set K := wv_rectK z w with hKdef
  set d := MeromorphicOn.divisor f K with hddef
  have hfin : d.support.Finite := d.finiteSupport (wv_isCompact_rectK z w)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hf.extract_zeros_poles (fun u => hord u u.2) hfin
  set s := hfin.toFinset with hsdef
  -- the divisor vanishes on the frame
  have hd_frame : ∀ ζ ∈ wv_rectF z w, d ζ = 0 := by
    intro ζ hζ
    obtain ⟨han, hne⟩ := hbd ζ hζ
    rw [hddef, MeromorphicOn.divisor_apply hf hζ.1, han.meromorphicOrderAt_eq,
      han.analyticOrderAt_eq_zero.mpr hne]
    simp
  -- the support lies in the open rectangle
  have hs_in : ∀ p ∈ s, p ∈ wv_rectO z w := by
    intro p hp
    rw [hsdef, Set.Finite.mem_toFinset] at hp
    have hpK : p ∈ K := d.supportWithinDomain hp
    by_contra hpO
    exact hp (hd_frame p ⟨hpK, hpO⟩)
  have hs_ne : ∀ p ∈ s, ∀ ζ ∈ wv_rectF z w, ζ - p ≠ 0 := by
    intro p hp ζ hζ h
    rw [sub_eq_zero] at h
    exact hζ.2 (h ▸ hs_in p hp)
  set P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ d u with hPdef
  have hP : ∀ x, P x = ∏ p ∈ s, (x - p) ^ d p := by
    intro x
    rw [hPdef, Function.FactorizedRational.finprod_eq_fun hfin]
    exact finprod_eq_prod_of_mulSupport_subset _ fun u hu => by
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      exact hu (by simp [h0])
  -- pointwise identity on the frame
  have hlog : EqOn (logDeriv f) (fun ζ => logDeriv g ζ + ∑ p ∈ s, (d p : ℂ) * (ζ - p)⁻¹)
      (wv_rectF z w) := by
    intro ζ hζ
    have hPan : AnalyticAt ℂ P ζ :=
      Function.FactorizedRational.analyticAt (by rw [hd_frame ζ hζ])
    have hPne : P ζ ≠ 0 := Function.FactorizedRational.ne_zero (hd_frame ζ hζ)
    have hgan : AnalyticAt ℂ g ζ := hg_an ζ hζ.1
    have hgne : g ζ ≠ 0 := hg_ne ⟨ζ, hζ.1⟩
    have hev : f =ᶠ[𝓝 ζ] P * g := by
      have hfreq : ∃ᶠ x in 𝓝[≠] ζ, f x = (P * g) x := by
        have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg ζ hζ.1
        refine (wv_frequently_rectK hre him hζ).mp (Filter.mem_of_superset h1 ?_)
        intro x hx hxK
        rcases hx with hx | hx
        · simpa [Pi.smul_apply', smul_eq_mul] using hx
        · exact absurd hxK hx
      exact ((hbd ζ hζ).1.frequently_eq_iff_eventually_eq (hPan.mul hgan)).mp hfreq
    have h1 : logDeriv f ζ = logDeriv (P * g) ζ := by
      simp only [logDeriv_apply]
      rw [hev.deriv_eq, hev.eq_of_nhds]
    rw [h1, logDeriv_mul ζ hPne hgne hPan.differentiableAt hgan.differentiableAt, add_comm]
    congr 1
    have hPfun : P = fun x => ∏ p ∈ s, (x - p) ^ d p := funext hP
    rw [hPfun, logDeriv_fun_prod]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [logDeriv_fun_zpow (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    · intro p hp
      exact zpow_ne_zero _ (hs_ne p hp ζ hζ)
    · intro p hp
      exact (differentiableAt_id.sub_const p).zpow (Or.inl (hs_ne p hp ζ hζ))
  -- continuity on the frame
  have hg_cont : ContinuousOn (logDeriv g) (wv_rectF z w) := by
    intro ζ hζ
    have hgan : AnalyticAt ℂ g ζ := hg_an ζ hζ.1
    exact ((hgan.deriv.div hgan (hg_ne ⟨ζ, hζ.1⟩)).continuousAt).continuousWithinAt
  have hterm_cont : ∀ p ∈ s, ContinuousOn (fun ζ => (d p : ℂ) * (ζ - p)⁻¹) (wv_rectF z w) := by
    intro p hp
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
      fun ζ hζ => hs_ne p hp ζ hζ)
  have hsum_cont : ContinuousOn (fun ζ => ∑ p ∈ s, (d p : ℂ) * (ζ - p)⁻¹) (wv_rectF z w) :=
    continuousOn_finsetSum _ hterm_cont
  -- Cauchy for `logDeriv g`
  have hcauchy : wv_rectBdry (logDeriv g) z w = 0 := by
    apply integral_boundary_rect_eq_zero_of_differentiableOn
    intro ζ hζ
    have hgan : AnalyticAt ℂ g ζ := hg_an ζ hζ
    exact (hgan.deriv.div hgan (hg_ne ⟨ζ, hζ⟩)).differentiableAt.differentiableWithinAt
  rw [wv_rectBdry_congr hlog, wv_rectBdry_add hg_cont hsum_cont, hcauchy, zero_add,
    wv_rectBdry_sum s hterm_cont, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [wv_rectBdry_const_mul]
  have hpO := hs_in p hp
  have := wv_integral_boundary_rect_inv_sub (z := z) (w := w) (p := p) hpO.1.1 hpO.1.2 hpO.2.1
    hpO.2.2
  rw [show wv_rectBdry (fun ζ => (ζ - p)⁻¹) z w = 2 * π * I from this]
  ring

/-! ### The Weierstrass `℘` function for a period pair `(1, τ)`, `Im τ > 0` -/

section WeierstrassPOne

open PeriodPair

/-- Lattice membership for a period pair with `ω₁ = 1`: `x ∈ L` iff `x = m + n ω₂` for some
integers `m`, `n`. -/
theorem wv_mem_lattice_one {L : PeriodPair} (h1 : L.ω₁ = 1) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * L.ω₂ = x := by
  rw [mem_lattice, h1]; simp

/-- Every class modulo `L` (with `ω₁ = 1`, `0 < ω₂.im`) has a representative in the half-open box
`[x₀, x₀ + 1) × [y₀, y₀ + ω₂.im)`. -/
theorem wv_exists_rep {L : PeriodPair} (h1 : L.ω₁ = 1) (hτ : 0 < L.ω₂.im) (ζ : ℂ) (x₀ y₀ : ℝ) :
    ∃ l ∈ L.lattice, (ζ - l).re ∈ Ico x₀ (x₀ + 1) ∧ (ζ - l).im ∈ Ico y₀ (y₀ + L.ω₂.im) := by
  set v := L.ω₂.im with hv
  set k : ℤ := ⌊(ζ.im - y₀) / v⌋ with hk
  set ζ₁ := ζ - k * L.ω₂ with hζ₁
  set m : ℤ := ⌊ζ₁.re - x₀⌋ with hm
  refine ⟨m + k * L.ω₂, (wv_mem_lattice_one h1).2 ⟨m, k, rfl⟩, ?_, ?_⟩
  · have e : (ζ - (m + k * L.ω₂)).re = ζ₁.re - m := by simp [hζ₁]; ring
    rw [e]
    have h₁ := Int.floor_le (ζ₁.re - x₀)
    have h₂ := Int.lt_floor_add_one (ζ₁.re - x₀)
    rw [← hm] at h₁ h₂
    constructor <;> linarith
  · have e : (ζ - (m + k * L.ω₂)).im = ζ.im - k * v := by simp [hv]
    rw [e]
    have h₁ := Int.floor_le ((ζ.im - y₀) / v)
    have h₂ := Int.lt_floor_add_one ((ζ.im - y₀) / v)
    rw [← hk] at h₁ h₂
    rw [le_div_iff₀ hτ] at h₁
    rw [div_lt_iff₀ hτ] at h₂
    constructor <;> nlinarith

/-- Two points of the half-open box `[x₀, x₀ + 1) × [y₀, y₀ + ω₂.im)` that differ by a lattice
vector are equal (for `ω₁ = 1`, `0 < ω₂.im`). -/
theorem wv_eq_of_sub_mem {L : PeriodPair} (h1 : L.ω₁ = 1) (hτ : 0 < L.ω₂.im) {ζ ζ' : ℂ}
    {x₀ y₀ : ℝ} (hζ : ζ.re ∈ Ico x₀ (x₀ + 1) ∧ ζ.im ∈ Ico y₀ (y₀ + L.ω₂.im))
    (hζ' : ζ'.re ∈ Ico x₀ (x₀ + 1) ∧ ζ'.im ∈ Ico y₀ (y₀ + L.ω₂.im))
    (h : ζ - ζ' ∈ L.lattice) : ζ = ζ' := by
  obtain ⟨m, n, e⟩ := (wv_mem_lattice_one h1).1 h
  have him : (n : ℝ) * L.ω₂.im = ζ.im - ζ'.im := by
    have := congrArg Complex.im e; simpa using this
  have hn : n = 0 := by
    have hlt : (n : ℝ) * L.ω₂.im < 1 * L.ω₂.im := by
      rw [him]; linarith [hζ.2.2, hζ'.2.1]
    have hgt : (-1 : ℝ) * L.ω₂.im < (n : ℝ) * L.ω₂.im := by
      rw [him]; linarith [hζ.2.1, hζ'.2.2]
    have a1 : (n : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hτ.le
    have a2 : (-1 : ℝ) < n := lt_of_mul_lt_mul_right hgt hτ.le
    have b1 : n < 1 := by exact_mod_cast a1
    have b2 : -1 < n := by exact_mod_cast a2
    omega
  subst hn
  have hre : (m : ℝ) = ζ.re - ζ'.re := by
    have := congrArg Complex.re e; simpa using this
  have hm : m = 0 := by
    have a1 : (m : ℝ) < 1 := by rw [hre]; linarith [hζ.1.2, hζ'.1.1]
    have a2 : (-1 : ℝ) < m := by rw [hre]; linarith [hζ.1.1, hζ'.1.2]
    have b1 : m < 1 := by exact_mod_cast a1
    have b2 : -1 < m := by exact_mod_cast a2
    omega
  subst hm
  have : ζ - ζ' = 0 := by rw [← e]; simp
  exact sub_eq_zero.mp this

/-- `℘ - c` is meromorphic on `ℂ`. -/
theorem wv_meromorphic_wpc {L : PeriodPair} (c : ℂ) : Meromorphic (fun z => ℘[L] z - c) := by
  fun_prop

/-- `℘ - c` has a double pole (meromorphic order `-2`) at every lattice point. -/
theorem wv_order_wpc_lattice {L : PeriodPair} (c : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt (fun z => ℘[L] z - c) l = -2 := by
  have h := L.order_weierstrassP l hl
  have e : (fun z => ℘[L] z - c) = ℘[L] + fun _ => -c := by
    ext z; simp [sub_eq_add_neg]
  rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const _ _), h]
  rw [h]
  classical
  rw [meromorphicOrderAt_const]
  split_ifs <;> decide

/-- The meromorphic order of `℘ - c` is never `⊤`: `℘ - c` vanishes identically near no point. -/
theorem wv_order_wpc_ne_top {L : PeriodPair} (c : ℂ) (x : ℂ) :
    meromorphicOrderAt (fun z => ℘[L] z - c) x ≠ ⊤ :=
  (wv_meromorphic_wpc c).exists_meromorphicOrderAt_ne_top_iff_forall.1
    ⟨0, by rw [wv_order_wpc_lattice c (zero_mem _)]; decide⟩ x

/-- `℘ - c` is analytic off the lattice. -/
theorem wv_analyticAt_wpc {L : PeriodPair} (c : ℂ) {x : ℂ} (hx : x ∉ L.lattice) :
    AnalyticAt ℂ (fun z => ℘[L] z - c) x :=
  (L.analyticOnNhd_weierstrassP x hx).sub analyticAt_const

/-- The logarithmic derivative of `℘ - c` is `L`-periodic. -/
theorem wv_logDeriv_wpc_add {L : PeriodPair} (c : ℂ) {l : ℂ} (hl : l ∈ L.lattice) (ζ : ℂ) :
    logDeriv (fun z => ℘[L] z - c) (ζ + l) = logDeriv (fun z => ℘[L] z - c) ζ := by
  have hper : (fun z => ℘[L] (z + l) - c) = fun z => ℘[L] z - c := by
    ext z; rw [L.weierstrassP_add_coe z ⟨l, hl⟩]
  simp only [logDeriv_apply]
  rw [← deriv_comp_add_const (f := fun z => ℘[L] z - c), hper, L.weierstrassP_add_coe ζ ⟨l, hl⟩]

/-- The boundary integral of a function with periods `1` and `τ` over a rectangle of width `1`
and height `τ.im` vanishes. -/
theorem wv_rectBdry_periodic {G : ℂ → ℂ} (τ : ℂ) (hG1 : ∀ ζ, G (ζ + 1) = G ζ)
    (hGτ : ∀ ζ, G (ζ + τ) = G ζ) {z w : ℂ} (hw1 : w.re = z.re + 1) (hw2 : w.im = z.im + τ.im) :
    wv_rectBdry G z w = 0 := by
  unfold wv_rectBdry
  have hH : Function.Periodic (fun x : ℝ => G (x + z.im * I)) 1 := by
    intro x
    simp only [ofReal_add, ofReal_one]
    rw [show (x : ℂ) + 1 + z.im * I = (x + z.im * I) + 1 by ring, hG1]
  have htop : ∫ x : ℝ in z.re..w.re, G (x + w.im * I) =
      ∫ x : ℝ in z.re..w.re, G (x + z.im * I) := by
    have e1 : ∀ x : ℝ, G (x + w.im * I) = G (((x - τ.re : ℝ) : ℂ) + z.im * I) := by
      intro x
      rw [← hGτ (((x - τ.re : ℝ) : ℂ) + z.im * I)]
      congr 1
      apply Complex.ext <;> simp [hw2]
    simp_rw [e1]
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => G (x + z.im * I)), hw1]
    have := hH.intervalIntegral_add_eq (z.re - τ.re) z.re
    rw [show z.re + 1 - τ.re = z.re - τ.re + 1 by ring]
    exact this
  have hright : ∫ y : ℝ in z.im..w.im, G (w.re + y * I) =
      ∫ y : ℝ in z.im..w.im, G (z.re + y * I) := by
    congr 1; ext y
    rw [hw1, show ((z.re + 1 : ℝ) : ℂ) + y * I = (z.re + y * I) + 1 by push_cast; ring, hG1]
  rw [htop, hright]
  ring

/-- The set of zeros and poles of `℘ - c` (the points of nonzero meromorphic order) is
countable. -/
theorem wv_countable_order_ne_zero {L : PeriodPair} (c : ℂ) :
    {p : ℂ | meromorphicOrderAt (fun z => ℘[L] z - c) p ≠ 0}.Countable := by
  have hF := wv_meromorphic_wpc (L := L) c
  have hsub : {p : ℂ | meromorphicOrderAt (fun z => ℘[L] z - c) p ≠ 0} ⊆
      ⋃ n : ℕ, (MeromorphicOn.divisor (fun z => ℘[L] z - c) (Metric.closedBall 0 n)).support := by
    intro p hp
    obtain ⟨n, hn⟩ := exists_nat_ge ‖p‖
    refine mem_iUnion.2 ⟨n, ?_⟩
    have hpB : p ∈ Metric.closedBall (0 : ℂ) n := mem_closedBall_zero_iff.2 hn
    rw [Function.mem_support, MeromorphicOn.divisor_apply (fun x _ => hF x) hpB]
    intro h0
    apply hp
    have hnt := wv_order_wpc_ne_top (L := L) c p
    lift meromorphicOrderAt (fun z => ℘[L] z - c) p to ℤ using hnt with k hk
    simp only [WithTop.untop₀_coe] at h0
    simp [h0]
  exact (countable_iUnion fun n =>
    ((MeromorphicOn.divisor _ _).finiteSupport (isCompact_closedBall _ _)).countable).mono hsub

/-- A countable set of reals misses some real number. -/
theorem wv_exists_notMem_of_countable {A : Set ℝ} (hA : A.Countable) : ∃ x : ℝ, x ∉ A :=
  (hA.dense_compl ℝ).nonempty

/-- A point of the frame of a nondegenerate rectangle lies on one of the four sides. -/
theorem wv_frame_cases {z w ζ : ℂ} (hζ : ζ ∈ wv_rectF z w) (hre : z.re < w.re)
    (him : z.im < w.im) : ζ.re = z.re ∨ ζ.re = w.re ∨ ζ.im = z.im ∨ ζ.im = w.im := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hζ
  rw [uIcc_of_le hre.le] at h1
  rw [uIcc_of_le him.le] at h2
  by_contra hcon
  push Not at hcon
  exact h3 ⟨⟨lt_of_le_of_ne h1.1 (Ne.symm hcon.1), lt_of_le_of_ne h1.2 hcon.2.1⟩,
    ⟨lt_of_le_of_ne h2.1 (Ne.symm hcon.2.2.1), lt_of_le_of_ne h2.2 hcon.2.2.2⟩⟩

/-- Some fundamental rectangle `[x₀, x₀ + 1] × [y₀, y₀ + ω₂.im]` has a frame avoiding all zeros
and poles of `℘ - c`. -/
theorem wv_exists_good_rect {L : PeriodPair} (hτ : 0 < L.ω₂.im) (c : ℂ) :
    ∃ x₀ y₀ : ℝ, ∀ ζ ∈ wv_rectF (x₀ + y₀ * I) ((x₀ + 1 : ℝ) + (y₀ + L.ω₂.im : ℝ) * I),
      meromorphicOrderAt (fun z => ℘[L] z - c) ζ = 0 := by
  set S := {p : ℂ | meromorphicOrderAt (fun z => ℘[L] z - c) p ≠ 0}
  have hS : S.Countable := wv_countable_order_ne_zero c
  obtain ⟨x₀, hx₀⟩ := wv_exists_notMem_of_countable
    ((hS.image Complex.re).union ((hS.image Complex.re).image fun r => r - 1))
  obtain ⟨y₀, hy₀⟩ := wv_exists_notMem_of_countable
    ((hS.image Complex.im).union ((hS.image Complex.im).image fun r => r - L.ω₂.im))
  refine ⟨x₀, y₀, fun ζ hζ => ?_⟩
  by_contra hne
  have hζS : ζ ∈ S := hne
  have hre : (↑x₀ + ↑y₀ * I : ℂ).re < ((x₀ + 1 : ℝ) + (y₀ + L.ω₂.im : ℝ) * I : ℂ).re := by simp
  have him : (↑x₀ + ↑y₀ * I : ℂ).im < ((x₀ + 1 : ℝ) + (y₀ + L.ω₂.im : ℝ) * I : ℂ).im := by
    simp; linarith
  rcases wv_frame_cases hζ hre him with h | h | h | h <;> simp at h
  · exact hx₀ (Or.inl ⟨ζ, hζS, h⟩)
  · exact hx₀ (Or.inr ⟨ζ.re, ⟨ζ, hζS, rfl⟩, by rw [h]; ring⟩)
  · exact hy₀ (Or.inl ⟨ζ, hζS, h⟩)
  · exact hy₀ (Or.inr ⟨ζ.im, ⟨ζ, hζS, rfl⟩, by rw [h]; ring⟩)

/-- A lower bound for the divisor at a point of analyticity: if `f` is analytic at `p ∈ U` and
vanishes there to order at least `n`, then `n ≤ MeromorphicOn.divisor f U p`. -/
theorem wv_le_divisor_of_analyticAt {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) {p : ℂ}
    (hp : p ∈ U) (han : AnalyticAt ℂ f p) (hne : meromorphicOrderAt f p ≠ ⊤) {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt f p) : (n : ℤ) ≤ MeromorphicOn.divisor f U p := by
  rw [MeromorphicOn.divisor_apply hf hp, han.meromorphicOrderAt_eq]
  rw [han.meromorphicOrderAt_eq] at hne
  have hne' : analyticOrderAt f p ≠ ⊤ := by
    intro h; apply hne; simp [h]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne'
  rw [← hm] at hn ⊢
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  exact_mod_cast hn

end WeierstrassPOne

/-! ### Value distribution of `℘` -/

section ValueDistribution

open PeriodPair

/-- `℘'` vanishes at the half periods: if `2 z ∈ L` then `℘' z = 0` (`℘'` is odd and
`L`-periodic). -/
theorem wv_derivWeierstrassP_eq_zero_of_two_mul_mem {L : PeriodPair} {z : ℂ}
    (h : 2 * z ∈ L.lattice) : ℘'[L] z = 0 := by
  have e1 : ℘'[L] (z - 2 * z) = ℘'[L] z := L.derivWeierstrassP_sub_coe z ⟨2 * z, h⟩
  rw [show z - 2 * z = -z by ring, L.derivWeierstrassP_neg] at e1
  linear_combination -e1 / 2

/-- The derivative of `℘ - c` is `℘'`. -/
theorem wv_deriv_wpc (L : PeriodPair) (c p : ℂ) :
    deriv (fun ζ => ℘[L] ζ - c) p = ℘'[L] p := by
  rw [deriv_sub_const, L.deriv_weierstrassP]

/-- **Value distribution of `℘`.**  For a period pair `(1, τ)` with `0 < τ.im` and `z, z' ∉ L`,
`℘ z = ℘ z'` iff `z - z' ∈ L` or `z + z' ∈ L`.  The hypotheses `z, z' ∉ L` cannot be dropped:
Mathlib's `℘` takes the junk value `0` at the lattice points (`PeriodPair.weierstrassP_coe`). -/
theorem weierstrassP_eq_iff_of_one {L : PeriodPair} (h1 : L.ω₁ = 1) (hτ : 0 < L.ω₂.im)
    {z z' : ℂ} (hz : z ∉ L.lattice) (hz' : z' ∉ L.lattice) :
    ℘[L] z = ℘[L] z' ↔ z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
  constructor
  swap
  · rintro (h | h)
    · have := L.weierstrassP_add_coe z' ⟨z - z', h⟩
      simp only [add_sub_cancel] at this
      exact this
    · have := L.weierstrassP_add_coe (-z') ⟨z + z', h⟩
      simp only [L.weierstrassP_neg] at this
      rw [show -z' + (z + z') = z by ring] at this
      exact this
  intro heq
  by_contra hcon
  push Not at hcon
  obtain ⟨hdiff, hsum⟩ := hcon
  set c := ℘[L] z with hc
  set F : ℂ → ℂ := fun ζ => ℘[L] ζ - c with hF
  set v := L.ω₂.im with hv
  obtain ⟨x₀, y₀, hgood⟩ := wv_exists_good_rect hτ c
  set z₀ : ℂ := x₀ + y₀ * I with hz₀
  set z₁ : ℂ := ((x₀ + 1 : ℝ) : ℂ) + ((y₀ + v : ℝ) : ℂ) * I with hz₁
  have hz₀re : z₀.re = x₀ := by simp [hz₀]
  have hz₀im : z₀.im = y₀ := by simp [hz₀]
  have hz₁re : z₁.re = x₀ + 1 := by simp [hz₁]
  have hz₁im : z₁.im = y₀ + v := by simp [hz₁]
  have hre : z₀.re < z₁.re := by rw [hz₀re, hz₁re]; linarith
  have him : z₀.im < z₁.im := by rw [hz₀im, hz₁im]; linarith
  have hmero : MeromorphicOn F (wv_rectK z₀ z₁) := fun x _ => wv_meromorphic_wpc c x
  have hord_ne_top : ∀ p, meromorphicOrderAt F p ≠ ⊤ := fun p => wv_order_wpc_ne_top c p
  -- frame: analytic and nonvanishing
  have hbd : ∀ ζ ∈ wv_rectF z₀ z₁, AnalyticAt ℂ F ζ ∧ F ζ ≠ 0 := by
    intro ζ hζ
    have h0 := hgood ζ hζ
    have hζL : ζ ∉ L.lattice := fun h => by
      rw [wv_order_wpc_lattice c h] at h0; exact absurd h0 (by decide)
    have han := wv_analyticAt_wpc c hζL
    exact ⟨han, han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h0⟩
  -- argument principle + periodicity
  have hAP := wv_rectBdry_logDeriv hre him hmero (fun u _ => hord_ne_top u) hbd
  have hper : wv_rectBdry (logDeriv F) z₀ z₁ = 0 := by
    apply wv_rectBdry_periodic L.ω₂
    · intro ζ
      exact wv_logDeriv_wpc_add c (by rw [← h1]; exact L.ω₁_mem_lattice) ζ
    · intro ζ
      exact wv_logDeriv_wpc_add c L.ω₂_mem_lattice ζ
    · rw [hz₀re, hz₁re]
    · rw [hz₀im, hz₁im]
  rw [hper] at hAP
  set d := MeromorphicOn.divisor F (wv_rectK z₀ z₁) with hd
  set T := (d.finiteSupport (wv_isCompact_rectK z₀ z₁)).toFinset with hT
  have hsumZ : ∑ p ∈ T, d p = 0 := by
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : ∑ p ∈ T, (d p : ℂ) = 0 := by
      rcases mul_eq_zero.mp hAP.symm with h | h
      · exact absurd h h2
      · exact h
    exact_mod_cast this
  -- the half-open box
  let box : ℂ → Prop := fun p => p.re ∈ Ico x₀ (x₀ + 1) ∧ p.im ∈ Ico y₀ (y₀ + v)
  have hbox_K : ∀ p, box p → p ∈ wv_rectK z₀ z₁ := by
    intro p hp
    simp only [wv_rectK, mem_reProdIm, hz₀re, hz₁re, hz₀im, hz₁im]
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact ⟨Ico_subset_Icc_self hp.1, Ico_subset_Icc_self hp.2⟩
  have hT_box : ∀ p ∈ T, box p := by
    intro p hp
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support] at hp
    have hpK : p ∈ wv_rectK z₀ z₁ := d.supportWithinDomain hp
    have hpO : p ∈ wv_rectO z₀ z₁ := by
      by_contra hO
      apply hp
      rw [hd, MeromorphicOn.divisor_apply hmero hpK, hgood p ⟨hpK, hO⟩]
      rfl
    obtain ⟨h₁, h₂⟩ := hpO
    rw [hz₀re, hz₁re] at h₁
    rw [hz₀im, hz₁im] at h₂
    exact ⟨Ioo_subset_Ico_self h₁, Ioo_subset_Ico_self h₂⟩
  -- representatives
  obtain ⟨l₀, hl₀, h₀box⟩ := wv_exists_rep h1 hτ 0 x₀ y₀
  obtain ⟨l₁, hl₁, h₁box⟩ := wv_exists_rep h1 hτ z x₀ y₀
  obtain ⟨l₂, hl₂, h₂box⟩ := wv_exists_rep h1 hτ (-z) x₀ y₀
  obtain ⟨l₃, hl₃, h₃box⟩ := wv_exists_rep h1 hτ z' x₀ y₀
  set p₀ := 0 - l₀ with hp₀
  set a := z - l₁ with ha
  set b := -z - l₂ with hb
  set a' := z' - l₃ with ha'
  have hp₀L : p₀ ∈ L.lattice := sub_mem (zero_mem _) hl₀
  have ha_nl : a ∉ L.lattice := fun h => hz (by simpa [ha] using add_mem h hl₁)
  have hb_nl : b ∉ L.lattice := fun h => hz (by
    have := neg_mem (add_mem h hl₂); simpa [hb] using this)
  have ha'_nl : a' ∉ L.lattice := fun h => hz' (by simpa [ha'] using add_mem h hl₃)
  -- zeros of F
  have hFa : F a = 0 := by
    simp only [hF, ha, L.weierstrassP_sub_coe z ⟨l₁, hl₁⟩, hc, sub_self]
  have hFb : F b = 0 := by
    simp only [hF, hb, L.weierstrassP_sub_coe (-z) ⟨l₂, hl₂⟩, L.weierstrassP_neg, hc, sub_self]
  have hFa' : F a' = 0 := by
    show ℘[L] (z' - l₃) - c = 0
    rw [L.weierstrassP_sub_coe z' ⟨l₃, hl₃⟩, ← heq, sub_self]
  -- divisor bounds
  have hdiv_zero : ∀ p, box p → p ∉ L.lattice → F p = 0 → 1 ≤ d p ∧ p ∈ T := by
    intro p hp hpL hFp
    have han := wv_analyticAt_wpc c hpL
    have h1le : ((1 : ℕ) : ℤ) ≤ d p := by
      apply wv_le_divisor_of_analyticAt hmero (hbox_K p hp) han (hord_ne_top p)
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han]
      intro i hi
      obtain rfl : i = 0 := by omega
      simpa using hFp
    refine ⟨by exact_mod_cast h1le, ?_⟩
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
    omega
  have hdiv_two : ∀ p, box p → p ∉ L.lattice → F p = 0 → ℘'[L] p = 0 → 2 ≤ d p := by
    intro p hp hpL hFp hdp
    have han := wv_analyticAt_wpc c hpL
    have h2le : ((2 : ℕ) : ℤ) ≤ d p := by
      apply wv_le_divisor_of_analyticAt hmero (hbox_K p hp) han (hord_ne_top p)
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han]
      intro i hi
      interval_cases i
      · simpa using hFp
      · simpa [wv_deriv_wpc L c p] using hdp
    exact_mod_cast h2le
  have hp₀T : p₀ ∈ T ∧ d p₀ = -2 := by
    have hK := hbox_K p₀ h₀box
    have hval : d p₀ = -2 := by
      rw [hd, MeromorphicOn.divisor_apply hmero hK, wv_order_wpc_lattice c hp₀L]
      rfl
    refine ⟨?_, hval⟩
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support, hval]
    decide
  have hT_nonneg : ∀ p ∈ T, p ≠ p₀ → 0 ≤ d p := by
    intro p hp hne
    have hpbox := hT_box p hp
    have hpL : p ∉ L.lattice := fun hL =>
      hne (wv_eq_of_sub_mem h1 hτ hpbox h₀box (sub_mem hL hp₀L))
    have := wv_le_divisor_of_analyticAt (n := 0) hmero (hbox_K p hpbox)
      (wv_analyticAt_wpc c hpL) (hord_ne_top p) (by simp)
    exact_mod_cast this
  -- distinctness
  have hne_aa' : a ≠ a' := by
    intro h
    apply hdiff
    have : z - z' = l₁ - l₃ := by rw [ha, ha'] at h; linear_combination h
    rw [this]; exact sub_mem hl₁ hl₃
  have hne_ba' : b ≠ a' := by
    intro h
    apply hsum
    have : z + z' = l₃ - l₂ := by rw [hb, ha'] at h; linear_combination -h
    rw [this]; exact sub_mem hl₃ hl₂
  have hne_p₀ : ∀ q, q ∉ L.lattice → q ≠ p₀ := fun q hq h => hq (h ▸ hp₀L)
  -- the count
  obtain ⟨haT1, haT⟩ := hdiv_zero a h₁box ha_nl hFa
  obtain ⟨hbT1, hbT⟩ := hdiv_zero b h₂box hb_nl hFb
  obtain ⟨ha'T1, ha'T⟩ := hdiv_zero a' h₃box ha'_nl hFa'
  have hsplit : d p₀ + ∑ q ∈ T.erase p₀, d q = ∑ q ∈ T, d q := Finset.add_sum_erase T d hp₀T.1
  have hmono : ∀ Q : Finset ℂ, Q ⊆ T.erase p₀ → ∑ q ∈ Q, d q ≤ ∑ q ∈ T.erase p₀, d q := by
    intro Q hQ
    exact Finset.sum_le_sum_of_subset_of_nonneg hQ fun q hq _ =>
      hT_nonneg q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
  have hmemE : ∀ q, q ∈ T → q ∉ L.lattice → q ∈ T.erase p₀ := fun q hq hqL =>
    Finset.mem_erase.2 ⟨hne_p₀ q hqL, hq⟩
  by_cases hab : a = b
  · -- `a` is a half period: double zero
    have h2z : 2 * z ∈ L.lattice := by
      have : 2 * z = l₁ - l₂ := by rw [ha, hb] at hab; linear_combination hab
      rw [this]; exact sub_mem hl₁ hl₂
    have hda : ℘'[L] a = 0 := by
      rw [ha, L.derivWeierstrassP_sub_coe z ⟨l₁, hl₁⟩]
      exact wv_derivWeierstrassP_eq_zero_of_two_mul_mem h2z
    have ha2 := hdiv_two a h₁box ha_nl hFa hda
    have hQ : ({a, a'} : Finset ℂ) ⊆ T.erase p₀ := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hmemE _ haT ha_nl
      · exact hmemE _ ha'T ha'_nl
    have hQsum : ∑ q ∈ ({a, a'} : Finset ℂ), d q = d a + d a' := Finset.sum_pair hne_aa'
    have := hmono _ hQ
    omega
  · have hQ : ({a, b, a'} : Finset ℂ) ⊆ T.erase p₀ := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hmemE _ haT ha_nl
      · exact hmemE _ hbT hb_nl
      · exact hmemE _ ha'T ha'_nl
    have hQsum : ∑ q ∈ ({a, b, a'} : Finset ℂ), d q = d a + d b + d a' := by
      rw [Finset.sum_insert (by simp [hab, hne_aa']), Finset.sum_pair hne_ba', add_assoc]
    have := hmono _ hQ
    omega

/-- A rational combination `α ω₁ + β ω₂` of the periods with a non-integral coefficient is not a
lattice point. -/
theorem wv_notMem_lattice_of_rat {L : PeriodPair} (α β : ℚ) (h : α.den ≠ 1 ∨ β.den ≠ 1) {x : ℂ}
    (hx : x = α * L.ω₁ + β * L.ω₂) : x ∉ L.lattice := by
  rw [hx, mul_ω₁_add_mul_ω₂_mem_lattice]
  tauto

/-- **The half-period values of `℘` are pairwise distinct.**  For a period pair `(1, τ)` with
`0 < τ.im`, the values `℘(ω₁/2)`, `℘(ω₂/2)` and `℘((ω₁+ω₂)/2)` (classically `e₁`, `e₂`, `e₃`)
are pairwise distinct. -/
theorem half_period_values_ne {L : PeriodPair} (h1 : L.ω₁ = 1) (hτ : 0 < L.ω₂.im) :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) := by
  have n1 : L.ω₁ / 2 ∉ L.lattice := wv_notMem_lattice_of_rat (1 / 2) 0 (by left; simp)
    (by push_cast; ring)
  have n2 : L.ω₂ / 2 ∉ L.lattice := wv_notMem_lattice_of_rat 0 (1 / 2) (by right; simp)
    (by push_cast; ring)
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := wv_notMem_lattice_of_rat (1 / 2) (1 / 2)
    (by left; simp) (by push_cast; ring)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases (weierstrassP_eq_iff_of_one h1 hτ n1 n2).1 h with h' | h'
    · exact wv_notMem_lattice_of_rat (1 / 2) (-(1 / 2)) (by left; simp) (by push_cast; ring) h'
    · exact wv_notMem_lattice_of_rat (1 / 2) (1 / 2) (by left; simp) (by push_cast; ring) h'
  · rcases (weierstrassP_eq_iff_of_one h1 hτ n1 n3).1 h with h' | h'
    · exact wv_notMem_lattice_of_rat 0 (-(1 / 2)) (by right; simp) (by push_cast; ring) h'
    · exact wv_notMem_lattice_of_rat 1 (1 / 2) (by right; simp) (by push_cast; ring) h'
  · rcases (weierstrassP_eq_iff_of_one h1 hτ n2 n3).1 h with h' | h'
    · exact wv_notMem_lattice_of_rat (-(1 / 2)) 0 (by left; simp) (by push_cast; ring) h'
    · exact wv_notMem_lattice_of_rat (1 / 2) 1 (by left; simp) (by push_cast; ring) h'

end ValueDistribution

end LiZhongQC
