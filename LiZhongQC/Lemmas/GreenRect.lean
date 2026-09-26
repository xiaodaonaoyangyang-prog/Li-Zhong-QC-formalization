import LiZhongQC.Ch01.S06_C1Quasiconformal

/-!
# Green's formula on a rectangle, in terms of `∂_z` and `∂_z̄`

Groundwork for §11.2 (the Green and Pompeiu formulas (11.9)–(11.11)).

Mathlib's `Complex.integral_boundary_rect_of_differentiableOn_real` *is* the complex Green
formula on a rectangle: its right-hand integrand `I • f'(1) - f'(I)` is literally `2i ∂_z̄ f`
(its own docstring says so).  This file records that bridge (`two_I_mul_dzbar`) and restates the
formula in the project's `∂_z̄` vocabulary.

* `two_I_mul_dzbar`, `two_mul_dz`,
  `neg_two_I_mul_dz`                     — the algebraic bridge to Mathlib's integrand
* `green_rect_dzbar`                     — (11.9) on a rectangle
* `intervalIntegral_conj`                — `conj` through an interval integral

(11.10) follows from `green_rect_dzbar` applied to `conj ∘ f` by conjugating, using the book's
(6.3) — already available as `eq6_3` in §6 — together with `intervalIntegral_conj`; that
derivation is not carried out here.

## What is *not* done here

The §11 statements `eq11_9_green_dz` / `eq11_10_green_dzbar` are posed on a **disc**.  Passing
from a rectangle to a disc needs an exhaustion argument (Mathlib's divergence theorem is
box-shaped), which is not carried out; these lemmas are the rectangle case, which is the analytic
content, and the bridge any disc proof will also need.
-/

open Complex Set MeasureTheory intervalIntegral

open scoped Interval Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The bridge to Mathlib's Green integrand: `2i ∂_z̄ f = i f'_x - f'_y`. -/
theorem two_I_mul_dzbar (f : ℂ → ℂ) (z : ℂ) :
    2 * I * dzbar f z = I * fderiv ℝ f z 1 - fderiv ℝ f z I := by
  simp only [dzbar]
  linear_combination (fderiv ℝ f z I) * Complex.I_sq

/-- `2 ∂_z f = f'_x - i f'_y`. -/
theorem two_mul_dz (f : ℂ → ℂ) (z : ℂ) :
    2 * dz f z = fderiv ℝ f z 1 - I * fderiv ℝ f z I := by
  simp only [dz]
  ring

/-- `-2i ∂_z f = -i f'_x - f'_y`, the integrand of (11.10). -/
theorem neg_two_I_mul_dz (f : ℂ → ℂ) (z : ℂ) :
    -(2 * I) * dz f z = -(I * fderiv ℝ f z 1) - fderiv ℝ f z I := by
  simp only [dz]
  linear_combination (fderiv ℝ f z I) * Complex.I_sq

/-- **(11.9) on a rectangle.**  For `f` real-differentiable on a closed rectangle with
`2i ∂_z̄ f` integrable, the integral of `f` over the (positively traversed) boundary equals
`∬ 2i ∂_z̄ f`. -/
theorem green_rect_dzbar (f : ℂ → ℂ) (z w : ℂ)
    (Hd : DifferentiableOn ℝ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hi : IntegrableOn (fun ζ => 2 * I * dzbar f ζ) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, 2 * I * dzbar f (x + y * I) := by
  have hb : ∀ ζ : ℂ, I * fderiv ℝ f ζ 1 - fderiv ℝ f ζ I = 2 * I * dzbar f ζ :=
    fun ζ => (two_I_mul_dzbar f ζ).symm
  have hfun : (fun ζ : ℂ => I • fderiv ℝ f ζ 1 - fderiv ℝ f ζ I)
      = fun ζ : ℂ => 2 * I * dzbar f ζ := by
    funext ζ; rw [smul_eq_mul, hb]
  have Hi' : IntegrableOn (fun ζ => I • fderiv ℝ f ζ 1 - fderiv ℝ f ζ I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by rw [hfun]; exact Hi
  have h := Complex.integral_boundary_rect_of_differentiableOn_real f z w Hd Hi'
  simpa only [smul_eq_mul, hb] using h

/-! ## The conjugate formula (11.10) -/

/-- `conj` commutes with interval integrals. -/
theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, conj (f x)) = conj (∫ x in a..b, f x) := by
  unfold intervalIntegral
  rw [integral_conj, integral_conj, ← map_sub]

/-- `conj` preserves integrability (Mathlib has `integral_conj` but no `Integrable.conj`). -/
theorem integrableOn_conj {F : ℂ → ℂ} {s : Set ℂ} (h : IntegrableOn F s) :
    IntegrableOn (fun ζ => conj (F ζ)) s := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable h.1, ?_⟩
  have hn : ∀ ζ : ℂ, ‖conj (F ζ)‖ₑ = ‖F ζ‖ₑ := by
    intro ζ; simp [enorm_eq_nnnorm]
  simpa only [MeasureTheory.HasFiniteIntegral, hn] using h.2

/-- **(11.10) on a rectangle.**  The integral of `f` over the boundary *with respect to `dz̄`*
(the two vertical contributions change sign) equals `∬ -2i ∂_z f`.

Obtained from `green_rect_dzbar` applied to `conj ∘ f` by conjugating, using the book's (6.3)
(`eq6_3`).  The hypothesis is global real differentiability of `f`, which is what the intended
application (11.17) supplies (`T_ω ∈ C¹(ℂ)`); the pointwise identity `∂_z̄(conj∘f) = conj(∂_z f)`
needs `DifferentiableAt`, not `DifferentiableWithinAt`. -/
theorem green_rect_dz (f : ℂ → ℂ) (z w : ℂ) (Hd : ∀ ζ : ℂ, DifferentiableAt ℝ f ζ)
    (Hi : IntegrableOn (fun ζ => -(2 * I) * dz f ζ) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) +
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, -(2 * I) * dz f (x + y * I) := by
  -- the integrand identity `2i ∂_z̄(conj∘f) = conj (-2i ∂_z f)`
  have hpt : ∀ ζ : ℂ, 2 * I * dzbar (fun u => conj (f u)) ζ = conj (-(2 * I) * dz f ζ) := by
    intro ζ
    rw [← (eq6_3 (Hd ζ)).1]
    simp only [map_mul, map_neg, Complex.conj_I, map_ofNat]
    ring
  have hfun : (fun ζ : ℂ => 2 * I * dzbar (fun u => conj (f u)) ζ)
      = fun ζ : ℂ => conj (-(2 * I) * dz f ζ) := funext hpt
  -- `conj ∘ f` is real differentiable
  have hdg : ∀ ζ : ℂ, DifferentiableAt ℝ (fun u => conj (f u)) ζ := fun ζ =>
    ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp ζ (Hd ζ).hasFDerivAt).differentiableAt
  have Hdg : DifferentiableOn ℝ (fun u => conj (f u)) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    fun ζ _ => (hdg ζ).differentiableWithinAt
  have Hig : IntegrableOn (fun ζ => 2 * I * dzbar (fun u => conj (f u)) ζ)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    rw [hfun]; exact integrableOn_conj Hi
  have h := green_rect_dzbar (fun u => conj (f u)) z w Hdg Hig
  simp only [hpt, intervalIntegral_conj] at h
  have h3 := congrArg (starRingEnd ℂ) h
  simp only [map_sub, map_add, map_mul, Complex.conj_I, Complex.conj_conj] at h3
  linear_combination h3

end LiZhongQC
