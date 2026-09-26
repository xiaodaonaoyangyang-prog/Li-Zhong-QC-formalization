import LiZhongQC.Lemmas.GreenRect
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Towards Green's formula on a disc: the radial differentiation identity

§11.2 poses (11.9)/(11.10) on a **disc**, while Mathlib's divergence theorem is box-shaped.
Rather than approximate a disc by rectangles, this file sets up the classical
*differentiate-in-the-radius* proof, which needs no exhaustion:

for `φ(r) = ∮_{|ζ-c|=r} f dζ = ∫₀^{2π} f(c+re^{iθ}) · i r e^{iθ} dθ`, the pointwise identity

  `∂_r [f(c+re^{iθ}) · i r e^{iθ}] - ∂_θ [f(c+re^{iθ}) · e^{iθ}] = 2 i r ∂_z̄ f(c+re^{iθ})`

holds, so integrating in `θ` over a full period kills the `∂_θ` term and gives
`φ'(r) = 2 i r ∫₀^{2π} ∂_z̄ f dθ`; integrating in `r` and using polar coordinates for the area
integral then yields `φ(R) = 2i ∬_{|ζ-c|<R} ∂_z̄ f`.

* `exp_mul_I_mul_conj`, `conj_exp_mul_I`   — `e^{iθ} \overline{e^{iθ}} = 1`
* `hasDerivAt_ray`, `hasDerivAt_circle`    — the two parametrisations
* `hasDerivAt_radial`, `hasDerivAt_angular` — derivatives of `f` along them, via `∂_z`, `∂_z̄`
* `green_disc_key`                          — the identity above

## What remains

Differentiation under the integral sign in `r`, the vanishing of `∫₀^{2π} ∂_θ(…) dθ` by
periodicity, the fundamental theorem of calculus in `r`, and polar coordinates for the area
integral.  Those are the remaining steps to `eq11_9_green_dz`.
-/

open Complex Set MeasureTheory intervalIntegral

open scoped Interval Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- `conj (e^{iθ}) = e^{-iθ}`. -/
theorem conj_exp_mul_I (θ : ℝ) : conj (Complex.exp ((θ : ℂ) * I)) = Complex.exp (-((θ : ℂ) * I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- `e^{iθ} · conj (e^{iθ}) = 1`. -/
theorem exp_mul_I_mul_conj (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) * conj (Complex.exp ((θ : ℂ) * I)) = 1 := by
  rw [conj_exp_mul_I, ← Complex.exp_add]
  simp

/-- The ray `r ↦ c + r e^{iθ}` has derivative `e^{iθ}`. -/
theorem hasDerivAt_ray (c : ℂ) (θ : ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => c + (t : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I)) r := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
    (Complex.exp ((θ : ℂ) * I))).const_add c

/-- The circle `θ ↦ c + r e^{iθ}` has derivative `i r e^{iθ}`. -/
theorem hasDerivAt_circle (c : ℂ) (r : ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => c + (r : ℂ) * Complex.exp ((t : ℂ) * I))
      (I * (r : ℂ) * Complex.exp ((θ : ℂ) * I)) θ := by
  have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) θ := hlin.cexp
  simpa [mul_comm, mul_assoc, mul_left_comm] using (hexp.const_mul (r : ℂ)).const_add c

/-- **The algebraic heart of the disc Green formula.**  With `A = ∂_z f(p)`, `B = ∂_z̄ f(p)`,
`u = e^{iθ}` (so `u · conj u = 1`) and `fp = f(p)`, the radial derivative of `f · i r u` minus the
angular derivative of `f · u` equals `2 i r B`. -/
theorem green_disc_key (A B fp u : ℂ) (r : ℝ) (hu : u * conj u = 1) :
    ((A * u + B * conj u) * (I * (r : ℂ) * u) + fp * (I * u))
        - ((I * (r : ℂ) * (A * u - B * conj u)) * u + fp * (I * u))
      = 2 * I * (r : ℂ) * B := by
  linear_combination (2 * I * (r : ℂ) * B) * hu

/-- The derivative of `f` along the ray `r ↦ c + r e^{iθ}`: `∂_z f · e^{iθ} + ∂_z̄ f · e^{-iθ}`. -/
theorem hasDerivAt_radial {f : ℂ → ℂ} (c : ℂ) (θ : ℝ) (r : ℝ)
    (hf : DifferentiableAt ℝ f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I))) :
    HasDerivAt (fun t : ℝ => f (c + (t : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (dz f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) +
        dzbar f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I)) * conj (Complex.exp ((θ : ℂ) * I))) r := by
  have h := hf.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_ray c θ r)
  rwa [fderiv_eq_dz_dzbar hf] at h

/-- The derivative of `f` along the circle `θ ↦ c + r e^{iθ}`:
`i r (∂_z f · e^{iθ} - ∂_z̄ f · e^{-iθ})`. -/
theorem hasDerivAt_angular {f : ℂ → ℂ} (c : ℂ) (r : ℝ) (θ : ℝ)
    (hf : DifferentiableAt ℝ f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I))) :
    HasDerivAt (fun t : ℝ => f (c + (r : ℂ) * Complex.exp ((t : ℂ) * I)))
      (I * (r : ℂ) *
        (dz f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) -
          dzbar f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I)) * conj (Complex.exp ((θ : ℂ) * I)))) θ := by
  have h := hf.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circle c r θ)
  rw [fderiv_eq_dz_dzbar hf] at h
  convert h using 1
  · rfl
  have hc : conj (I * (r : ℂ) * Complex.exp ((θ : ℂ) * I))
      = -(I * (r : ℂ) * conj (Complex.exp ((θ : ℂ) * I))) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hc]
  ring

/-- **The radial identity, assembled.**  At every `(r, θ)`,
`∂_r [f(c+re^{iθ}) · i r e^{iθ}] - ∂_θ [f(c+re^{iθ}) · e^{iθ}] = 2 i r ∂_z̄ f(c+re^{iθ})`.

Integrating this in `θ` over a full period annihilates the second term, leaving
`φ'(r) = 2 i r ∫₀^{2π} ∂_z̄ f dθ` for the circle integral `φ`; that is the route to
`eq11_9_green_dz` without any rectangle exhaustion. -/
theorem green_disc_radial_sub_angular {f : ℂ → ℂ} (c : ℂ) (r θ : ℝ)
    (hf : DifferentiableAt ℝ f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I))) :
    ∃ a b : ℂ,
      HasDerivAt (fun t : ℝ => f (c + (t : ℂ) * Complex.exp ((θ : ℂ) * I)) *
        (I * (t : ℂ) * Complex.exp ((θ : ℂ) * I))) a r ∧
      HasDerivAt (fun t : ℝ => f (c + (r : ℂ) * Complex.exp ((t : ℂ) * I)) *
        Complex.exp ((t : ℂ) * I)) b θ ∧
      a - b = 2 * I * (r : ℂ) * dzbar f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hfac1 : HasDerivAt (fun t : ℝ => I * (t : ℂ) * Complex.exp ((θ : ℂ) * I))
      (I * Complex.exp ((θ : ℂ) * I)) r := by
    simpa [mul_assoc] using
      ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul I).mul_const (Complex.exp ((θ : ℂ) * I))
  have hfac2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) θ := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact hlin.cexp
  refine ⟨_, _, (hasDerivAt_radial c θ r hf).mul hfac1,
    (hasDerivAt_angular c r θ hf).mul hfac2, ?_⟩
  linear_combination (2 * I * (r : ℂ) * dzbar f (c + (r : ℂ) * Complex.exp ((θ : ℂ) * I))) *
    exp_mul_I_mul_conj θ

/-! ## The radial derivative of the circle integral

Everything below is phrased with Mathlib's `circleMap c r θ = c + r e^{iθ}`, which is the
parametrisation `circleIntegral` (hence `∮ z in C(c, R), f z`) is defined by. -/

/-- `∂_r [f(c+re^{iθ}) · i r e^{iθ}]`, written out through `∂_z` and `∂_z̄`. -/
def radialTerm (f : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  (dz f (circleMap c r θ) * Complex.exp ((θ : ℂ) * I) +
      dzbar f (circleMap c r θ) * conj (Complex.exp ((θ : ℂ) * I))) *
    (I * (r : ℂ) * Complex.exp ((θ : ℂ) * I)) +
    f (circleMap c r θ) * (I * Complex.exp ((θ : ℂ) * I))

/-- `∂_θ [f(c+re^{iθ}) · e^{iθ}]`, written out through `∂_z` and `∂_z̄`. -/
def angularTerm (f : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  (I * (r : ℂ) * (dz f (circleMap c r θ) * Complex.exp ((θ : ℂ) * I) -
      dzbar f (circleMap c r θ) * conj (Complex.exp ((θ : ℂ) * I)))) * Complex.exp ((θ : ℂ) * I) +
    f (circleMap c r θ) * (Complex.exp ((θ : ℂ) * I) * I)

/-- `radialTerm` really is the `r`-derivative of `f(c+re^{iθ}) · i r e^{iθ}`. -/
theorem hasDerivAt_radialTerm {f : ℂ → ℂ} (c : ℂ) (r θ : ℝ)
    (hf : DifferentiableAt ℝ f (circleMap c r θ)) :
    HasDerivAt (fun t : ℝ => f (circleMap c t θ) * (I * (t : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (radialTerm f c r θ) r := by
  have hfac : HasDerivAt (fun t : ℝ => I * (t : ℂ) * Complex.exp ((θ : ℂ) * I))
      (I * Complex.exp ((θ : ℂ) * I)) r := by
    simpa [mul_assoc] using
      ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul I).mul_const (Complex.exp ((θ : ℂ) * I))
  exact (hasDerivAt_radial c θ r hf).mul hfac

/-- `angularTerm` really is the `θ`-derivative of `f(c+re^{iθ}) · e^{iθ}`. -/
theorem hasDerivAt_angularTerm {f : ℂ → ℂ} (c : ℂ) (r θ : ℝ)
    (hf : DifferentiableAt ℝ f (circleMap c r θ)) :
    HasDerivAt (fun t : ℝ => f (circleMap c r t) * Complex.exp ((t : ℂ) * I))
      (angularTerm f c r θ) θ := by
  have hfac : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) θ := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact hlin.cexp
  exact (hasDerivAt_angular c r θ hf).mul hfac

/-- The pointwise identity: `radialTerm - angularTerm = 2 i r ∂_z̄ f`. -/
theorem radialTerm_sub_angularTerm (f : ℂ → ℂ) (c : ℂ) (r θ : ℝ) :
    radialTerm f c r θ - angularTerm f c r θ = 2 * I * (r : ℂ) * dzbar f (circleMap c r θ) := by
  simp only [radialTerm, angularTerm]
  linear_combination (2 * I * (r : ℂ) * dzbar f (circleMap c r θ)) * exp_mul_I_mul_conj θ

/-- **The angular term integrates to zero over a full period**, since
`θ ↦ f(c+re^{iθ}) e^{iθ}` has period `2π`. -/
theorem integral_angularTerm_eq_zero {f : ℂ → ℂ} (c : ℂ) (r : ℝ)
    (hf : ∀ ζ : ℂ, DifferentiableAt ℝ f ζ)
    (hint : IntervalIntegrable (angularTerm f c r) volume 0 (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), angularTerm f c r θ = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_angularTerm c r θ (hf _)) hint]
  have hper : circleMap c r (2 * π) = circleMap c r 0 := by
    simpa using periodic_circleMap c r 0
  rw [hper]
  simp [Complex.exp_two_pi_mul_I]

/-- **The radial derivative of the circle integral.**  Combining the pointwise identity with the
vanishing of the angular term:
`∫₀^{2π} ∂_r[f · i r e^{iθ}] dθ = 2 i r ∫₀^{2π} ∂_z̄ f(c+re^{iθ}) dθ`.

This is `φ'(r) = 2 i r ∫₀^{2π} ∂_z̄ f dθ` once differentiation under the integral sign is
available. -/
theorem integral_radialTerm {f : ℂ → ℂ} (c : ℂ) (r : ℝ)
    (hf : ∀ ζ : ℂ, DifferentiableAt ℝ f ζ)
    (hang : IntervalIntegrable (angularTerm f c r) volume 0 (2 * π))
    (hdz : IntervalIntegrable (fun θ => dzbar f (circleMap c r θ)) volume 0 (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), radialTerm f c r θ
      = 2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ) := by
  have hpt : ∀ θ : ℝ, radialTerm f c r θ
      = angularTerm f c r θ + 2 * I * (r : ℂ) * dzbar f (circleMap c r θ) := by
    intro θ
    linear_combination radialTerm_sub_angularTerm f c r θ
  calc ∫ θ in (0 : ℝ)..(2 * π), radialTerm f c r θ
      = ∫ θ in (0 : ℝ)..(2 * π),
          (angularTerm f c r θ + 2 * I * (r : ℂ) * dzbar f (circleMap c r θ)) := by
        simp only [hpt]
    _ = (∫ θ in (0 : ℝ)..(2 * π), angularTerm f c r θ) +
          ∫ θ in (0 : ℝ)..(2 * π), 2 * I * (r : ℂ) * dzbar f (circleMap c r θ) :=
        intervalIntegral.integral_add hang (hdz.const_mul _)
    _ = 2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ) := by
        rw [integral_angularTerm_eq_zero c r hf hang, zero_add,
          intervalIntegral.integral_const_mul]

/-- The circle integral is the `θ`-integral of the radial product, i.e. `φ(r)` above really is
`∮_{|z-c|=r} f`. -/
theorem circleIntegral_eq_integral_radialProd (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∮ z in C(c, r), f z)
      = ∫ θ in (0 : ℝ)..(2 * π),
          f (circleMap c r θ) * (I * (r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  rw [circleIntegral]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, smul_eq_mul, circleMap, zero_add]
  ring

/-- The circle integral of radius `0` vanishes. -/
theorem circleIntegral_radius_zero (f : ℂ → ℂ) (c : ℂ) : (∮ z in C(c, (0 : ℝ)), f z) = 0 := by
  rw [circleIntegral]
  have hz : ∀ θ : ℝ, deriv (circleMap c 0) θ • f (circleMap c 0 θ) = (0 : ℂ) := fun θ => by
    rw [deriv_circleMap]
    simp [circleMap]
  simp only [hz, intervalIntegral.integral_zero]

/-- **Green's formula on a disc, reduced to differentiation under the integral sign.**

Given that the circle integral `φ(r) = ∮_{|z-c|=r} f` has the expected `r`-derivative — that is
exactly differentiation under the integral sign, applied to
`circleIntegral_eq_integral_radialProd` and `hasDerivAt_radialTerm` — the periodicity argument
and the fundamental theorem of calculus give

  `∮_{|z-c|=R} f = ∫₀^R 2 i r (∫₀^{2π} ∂_z̄ f(c+re^{iθ}) dθ) dr`.

Only polar coordinates then separate this from `eq11_9_green_dz`, whose right-hand side is
`2i ∬_{|z-c|<R} ∂_z̄ f`. -/
theorem circleIntegral_eq_integral_radial {f : ℂ → ℂ} (c : ℂ) {R : ℝ}
    (hf : ∀ ζ : ℂ, DifferentiableAt ℝ f ζ)
    (hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => ∮ z in C(c, t), f z)
        (∫ θ in (0 : ℝ)..(2 * π), radialTerm f c r θ) r)
    (hang : ∀ r : ℝ, IntervalIntegrable (angularTerm f c r) volume 0 (2 * π))
    (hdz : ∀ r : ℝ, IntervalIntegrable (fun θ => dzbar f (circleMap c r θ)) volume 0 (2 * π))
    (hint : IntervalIntegrable
      (fun r : ℝ => 2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ))
      volume 0 R) :
    (∮ z in C(c, R), f z)
      = ∫ r in (0 : ℝ)..R, 2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          dzbar f (circleMap c r θ) := by
  have hderiv' : ∀ r ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => ∮ z in C(c, t), f z)
        (2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ)) r := by
    intro r hr
    have h := hderiv r hr
    rwa [integral_radialTerm c r hf (hang r) (hdz r)] at h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint
  rw [circleIntegral_radius_zero, sub_zero] at hftc
  exact hftc.symm

/-! ## Differentiation under the integral sign -/

/-- For `f ∈ C¹`, `∂_z f` is continuous. -/
theorem continuous_dz {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dz f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have h : Continuous fun z : ℂ => (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 :=
    ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  exact h

/-- For `f ∈ C¹`, `∂_z̄ f` is continuous. -/
theorem continuous_dzbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzbar f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have h : Continuous fun z : ℂ => (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 :=
    ((hfd.clm_apply continuous_const).add
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  exact h

/-- `(r, θ) ↦ c + r e^{iθ}` is jointly continuous. -/
theorem continuous_circleMap_uncurry (c : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap c p.1 p.2 := by
  simp only [circleMap]
  exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))

/-- `(r, θ) ↦ radialTerm f c r θ` is jointly continuous for `f ∈ C¹`. -/
theorem continuous_radialTerm {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) :
    Continuous fun p : ℝ × ℝ => radialTerm f c p.1 p.2 := by
  have hcm := continuous_circleMap_uncurry c
  have he : Continuous fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const)
  have hA : Continuous fun p : ℝ × ℝ =>
      dz f (circleMap c p.1 p.2) * Complex.exp ((p.2 : ℂ) * I) +
        dzbar f (circleMap c p.1 p.2) * conj (Complex.exp ((p.2 : ℂ) * I)) :=
    (((continuous_dz hf).comp hcm).mul he).add
      (((continuous_dzbar hf).comp hcm).mul (Complex.continuous_conj.comp he))
  have hB : Continuous fun p : ℝ × ℝ => I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul he
  have hC : Continuous fun p : ℝ × ℝ =>
      f (circleMap c p.1 p.2) * (I * Complex.exp ((p.2 : ℂ) * I)) :=
    (hf.continuous.comp hcm).mul (continuous_const.mul he)
  simp only [radialTerm]
  exact (hA.mul hB).add hC

/-- **Differentiation under the integral sign.**  For `f ∈ C¹(ℂ)` the circle integral
`r ↦ ∮_{|z-c|=r} f` is differentiable, with the derivative obtained by differentiating the
integrand: `∫₀^{2π} ∂_r[f(c+re^{iθ}) · i r e^{iθ}] dθ`.

The dominating bound comes from continuity of `radialTerm` on the compact set
`closedBall r 1 ×ˢ [0, 2π]`. -/
theorem hasDerivAt_circleIntegral {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => ∮ z in C(c, t), f z)
      (∫ θ in (0 : ℝ)..(2 * π), radialTerm f c r θ) r := by
  have hdif : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcontR := continuous_radialTerm hf c
  -- the integrand and its `r`-derivative
  set F : ℝ → ℝ → ℂ :=
    fun t θ => f (circleMap c t θ) * (I * (t : ℂ) * Complex.exp ((θ : ℂ) * I)) with hF_def
  have hFcont : ∀ t : ℝ, Continuous (F t) := by
    intro t
    have h1 : Continuous fun θ : ℝ => f (circleMap c t θ) :=
      hf.continuous.comp (continuous_circleMap c t)
    have h2 : Continuous fun θ : ℝ => I * (t : ℂ) * Complex.exp ((θ : ℂ) * I) :=
      continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal).mul continuous_const))
    exact h1.mul h2
  have hF'cont : Continuous fun θ : ℝ => radialTerm f c r θ := by
    have : (fun θ : ℝ => radialTerm f c r θ) = (fun p : ℝ × ℝ => radialTerm f c p.1 p.2) ∘
        fun θ : ℝ => (r, θ) := rfl
    rw [this]
    exact hcontR.comp (continuous_const.prodMk continuous_id)
  -- a uniform bound on a compact neighbourhood
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r 1).prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)))
    |>.exists_bound_of_continuousOn hcontR.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun t θ => radialTerm f c t θ) (x₀ := r) (a := 0) (b := 2 * π)
    (bound := fun _ => C) (μ := volume) (s := Metric.ball r 1)
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun t => (hFcont t).aestronglyMeasurable)
    ((hFcont r).intervalIntegrable 0 (2 * π))
    hF'cont.aestronglyMeasurable
    (by
      filter_upwards with θ hθ x hx
      refine hC (x, θ) ⟨Metric.ball_subset_closedBall hx, ?_⟩
      rw [Set.uIoc_of_le Real.two_pi_pos.le] at hθ
      exact ⟨hθ.1.le, hθ.2⟩)
    (_root_.intervalIntegrable_const)
    (by
      filter_upwards with θ _ x _
      exact hasDerivAt_radialTerm c x θ (hdif _))
  have hfun : (fun t : ℝ => ∮ z in C(c, t), f z)
      = fun t : ℝ => ∫ θ in (0 : ℝ)..(2 * π), F t θ := by
    funext t
    exact circleIntegral_eq_integral_radialProd f c t
  rw [hfun]
  exact key.2

/-- `(r, θ) ↦ ∂_z̄ f (c + r e^{iθ})` is jointly continuous for `f ∈ C¹`. -/
theorem continuous_dzbar_circleMap {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) :
    Continuous fun p : ℝ × ℝ => dzbar f (circleMap c p.1 p.2) :=
  (continuous_dzbar hf).comp (continuous_circleMap_uncurry c)

/-- `(r, θ) ↦ angularTerm f c r θ` is jointly continuous for `f ∈ C¹`. -/
theorem continuous_angularTerm {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) :
    Continuous fun p : ℝ × ℝ => angularTerm f c p.1 p.2 := by
  have hcm := continuous_circleMap_uncurry c
  have he : Continuous fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const)
  have hA : Continuous fun p : ℝ × ℝ =>
      I * (p.1 : ℂ) * (dz f (circleMap c p.1 p.2) * Complex.exp ((p.2 : ℂ) * I) -
        dzbar f (circleMap c p.1 p.2) * conj (Complex.exp ((p.2 : ℂ) * I))) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
      ((((continuous_dz hf).comp hcm).mul he).sub
        (((continuous_dzbar hf).comp hcm).mul (Complex.continuous_conj.comp he)))
  have hC : Continuous fun p : ℝ × ℝ =>
      f (circleMap c p.1 p.2) * (Complex.exp ((p.2 : ℂ) * I) * I) :=
    (hf.continuous.comp hcm).mul (he.mul continuous_const)
  simp only [angularTerm]
  exact (hA.mul he).add hC

/-- **Green's formula on a disc, in polar form.**  For `f ∈ C¹(ℂ)`,

  `∮_{|z-c|=R} f = ∫₀^R 2 i r (∫₀^{2π} ∂_z̄ f(c+re^{iθ}) dθ) dr`.

This is `eq11_9_green_dz` up to rewriting the right-hand side as an area integral by polar
coordinates. -/
theorem circleIntegral_eq_integral_polar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z)
      = ∫ r in (0 : ℝ)..R, 2 * I * (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          dzbar f (circleMap c r θ) := by
  have hpar : Continuous fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => dzbar f (circleMap c r θ)) (continuous_dzbar_circleMap hf c) 0 (2 * π)
  refine circleIntegral_eq_integral_radial c (hf.differentiable one_ne_zero)
    (fun r _ => hasDerivAt_circleIntegral hf c r) (fun r => ?_) (fun r => ?_) ?_
  · exact (((continuous_angularTerm hf c).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable 0 (2 * π)
  · exact (((continuous_dzbar_circleMap hf c).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable 0 (2 * π)
  · exact ((continuous_const.mul Complex.continuous_ofReal).mul hpar).intervalIntegrable 0 R

end LiZhongQC
