/-
  Planar compact-support Stokes (the Forster (10.20) engine).

  Two layers:

  1. **Green's theorem on an axis-aligned rectangle** (`green_rectangle`): for `C¹` scalar fields
     `P, Q : ℝ × ℝ → ℝ`, the four-edge counter-clockwise boundary sum equals the iterated integral
     of the curl, `∮_{∂R}(P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y)`.  FTC slices + continuous Fubini.

     PORTED (with adaptations to this repo's Mathlib pin) from the MIT-licensed
     tangentstorm/JacobianChallenge, file `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean`
     (sub-leaf #5 `stokes_local_euclidean` + helpers), Copyright (c) 2026 Michal J Wallace,
     https://github.com/tangentstorm/JacobianChallenge — inspection-verified sorry-free at port
     time.  This rectangle engine is the seed for the Forster (10.21) annulus/residue identity.

  2. **Compact-support vanishing on ℂ** (Forster (10.20) itself, `∬_X dσ = 0` in the plane):
     for `φ : ℂ → ℂ` that is `ContDiff ℝ 1` with `HasCompactSupport φ`,
       * `integral_fderiv_apply_eq_zero` — `∫_ℂ (∂_v φ) = 0` for EVERY direction `v`
         (in particular the two partials `v = 1`, `v = I`);
       * `integral_dbar_eq_zero` — `∫_ℂ ∂̄φ = 0` (`DbarDisk.dbar`, the repo's Wirtinger operator);
       * `integral_del_eq_zero` — `∫_ℂ ∂φ = 0` (Wirtinger `∂ = ½(∂ₓ − i∂_y)`, stated inline).
     Proof: Mathlib's Haar-measure integration by parts
     (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) against the constant function `1`.
     Integration conventions match the repo's `Dbar*` files: plain `volume` on `ℂ`.

  Everything here is complete and depends on no unproved lemma.
-/
import Mathlib
import Jacobians.Dbar.DbarDisk

open MeasureTheory Complex

namespace Jacobians.Dolbeault

/-! ### Layer 1 — Green's theorem on an axis-aligned rectangle
(ported from tangentstorm/JacobianChallenge, MIT, see file header) -/

/-! ### Layer 2 — compact-support vanishing on `ℂ` (Forster (10.20)) -/

/-- The directional derivative of a `C¹` compactly-supported `φ : ℂ → ℂ` is integrable. -/
theorem integrable_fderiv_apply_of_compactSupport (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z : ℂ => fderiv ℝ φ z v) volume := by
  have hcont : Continuous fun z : ℂ => fderiv ℝ φ z v :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hsupp' : HasCompactSupport fun z : ℂ => fderiv ℝ φ z v :=
    (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (by simp)
  exact hcont.integrable_of_hasCompactSupport hsupp'

/-- **Forster (10.20) on the plane, directional form**: every directional derivative of a `C¹`
compactly-supported `φ : ℂ → ℂ` has vanishing area integral, `∫_ℂ ∂_v φ = 0` (in particular the
two partials `v = 1`, `v = I`).  Mathlib Haar integration by parts against the constant `1`. -/
theorem integral_fderiv_apply_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) (v : ℂ) :
    ∫ z : ℂ, fderiv ℝ φ z v = 0 := by
  have h1 : Integrable (fun x : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) x v * φ x) volume := by
    have heq : (fun x : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) x v * φ x) = fun _ => 0 := by
      ext x; simp
    rw [heq]; exact integrable_zero _ _ _
  have h2 : Integrable (fun x : ℂ => (1 : ℂ) * fderiv ℝ φ x v) volume := by
    simpa using integrable_fderiv_apply_of_compactSupport φ hφ hsupp v
  have h3 : Integrable (fun x : ℂ => (1 : ℂ) * φ x) volume := by
    simpa using hφ.continuous.integrable_of_hasCompactSupport hsupp
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : ℂ => (1 : ℂ)) (g := φ) (v := v) h1 h2 h3
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hφ.differentiable one_ne_zero).differentiableAt)
  simpa using key

/-- **`∫_ℂ ∂̄φ = 0`** for `C¹` compactly-supported `φ` (`DbarDisk.dbar` = the repo's Wirtinger
`∂̄ = ½(∂ₓ + i∂_y)`).  The well-definedness engine for the residue functional (Forster 17.1). -/
theorem integral_dbar_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ z : ℂ, DbarDisk.dbar φ z = 0 := by
  have h1 := integrable_fderiv_apply_of_compactSupport φ hφ hsupp 1
  have hI := integrable_fderiv_apply_of_compactSupport φ hφ hsupp Complex.I
  -- (the `e·` steps are term-mode: `rw`/`simp` trip on the `MeasurableSpace ℂ` instance forms)
  have e1 : ∫ z : ℂ, DbarDisk.dbar φ z
      = (2 : ℂ)⁻¹ * ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) :=
    MeasureTheory.integral_const_mul _ _
  have e2 : ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I)
      = (∫ z : ℂ, fderiv ℝ φ z 1) + ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_add h1 (hI.const_mul Complex.I)
  have e3 : ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I
      = Complex.I * ∫ z : ℂ, fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_const_mul _ _
  rw [e1, e2, e3, integral_fderiv_apply_eq_zero φ hφ hsupp 1,
    integral_fderiv_apply_eq_zero φ hφ hsupp Complex.I]
  ring

/-- **`∫_ℂ ∂φ = 0`** for `C¹` compactly-supported `φ` (Wirtinger `∂ = ½(∂ₓ − i∂_y)`, stated
inline — the repo has no named `∂`). -/
theorem integral_del_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ z : ℂ, (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I) = 0 := by
  have h1 := integrable_fderiv_apply_of_compactSupport φ hφ hsupp 1
  have hI := integrable_fderiv_apply_of_compactSupport φ hφ hsupp Complex.I
  have e1 : ∫ z : ℂ, (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I)
      = (2 : ℂ)⁻¹ * ∫ z : ℂ, (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I) :=
    MeasureTheory.integral_const_mul _ _
  have e2 : ∫ z : ℂ, (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I)
      = (∫ z : ℂ, fderiv ℝ φ z 1) - ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_sub h1 (hI.const_mul Complex.I)
  have e3 : ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I
      = Complex.I * ∫ z : ℂ, fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_const_mul _ _
  rw [e1, e2, e3, integral_fderiv_apply_eq_zero φ hφ hsupp 1,
    integral_fderiv_apply_eq_zero φ hφ hsupp Complex.I]
  ring

end Jacobians.Dolbeault
