/-
  The annulus residue integral (Forster (10.21), planar form).

  For a cutoff `χ` that is `≡ 1` near `c` and compactly supported inside a punctured-holomorphy
  ball of a meromorphic `m`, the Forster (10.21) identity computes the area integral of
  `∂̄(χ·m)` — a smooth, annulus-supported integrand (no singular integrals anywhere) — as a
  *residue*:

    `∫_ℂ ∂̄(χ·m) = −π · Res_c m`            (`integral_dbar_cutoff_mul_eq_resAt`)

  with the repo conventions `DbarDisk.dbar = ½(∂ₓ + i∂_y)` and `resAt = (2πi)⁻¹∮` (so for
  `m = (·−c)⁻¹` the integral is exactly `−π`; see the sanity anchor at the bottom).
  Forster's `2πi·Res` shape differs by his use of the 2-form `dz̄∧dz = 2i·dA`:
  `(−π)·dA`-normalisation `= (2πi)/(2i)·(−1)`… i.e. this is the same identity.

  Proof layout:
  * §1 extends `DbarDisk` with the Wirtinger calculus (`dbar_fun_mul` Leibniz, congruence,
    sums) — pointwise statements at points of real differentiability.
  * §2 computes `∂̄` of a *radial* cutoff `η(|w−c|²)`: `∂̄χ = η'(|z−c|²)·(z−c)` (the ½ in `∂̄`
    cancels the 2 from the squared modulus — polynomial-clean, no `‖·‖`-calculus).
  * §3 builds an explicit `C¹` radial profile from `Real.smoothTransition`.
  * §4 the single-term computation `∫ ∂̄(χ·(·−c)^{−k}) = −π·δ_{k,1}` in polar coordinates:
    angular integral `∮ e^{i(1−k)θ}dθ = 2π·δ_{k,1}` (FTC), radial integral `∫ rη'(r²)dr = −½`.
  * §5 cutoff independence: for two admissible cutoffs the difference `(χ₁−χ₂)·m` is `C¹` with
    compact support, so its `∂̄`-integral vanishes by the Forster (10.20) lemma
    (`integral_dbar_eq_zero`, `PlanarCompactSupportStokes`).
  * §6 the principal-part split `m = negTail + G` (`exists_principalPart_meromorphicAt`) with a
    junk-repaired holomorphic complement `G`; the `G`-term again dies by (10.20).
  * §7 `resAt` of the same data (`resAt m c = Σ b_k δ_{k,1}`), and the assembled theorem.

  References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §10 (Lemma 10.20 and the
  computation (10.21)); Miranda §VIII.3 uses the same bump-times-principal-part integrand.
-/
import Mathlib
import Jacobians.Dbar.DbarDisk
import Jacobians.PlanarStokes.PlanarCompactSupportStokes
import Jacobians.ResidueCalculus.Residue
import Jacobians.ResidueCalculus.FormTracePrincipalPart

-- The ℂ-as-ℝ-module diamond fix used across the Dolbeault tree (e.g. `DbarOpenDisk`): without it
-- `DifferentiableAt.restrictScalars ℝ` fails to synthesize `IsScalarTower ℝ ℂ ℂ` here.
set_option backward.isDefEq.respectTransparency false

open Complex Metric MeasureTheory Filter Set Topology
open scoped Real

/-! ### §1 — Wirtinger calculus for `DbarDisk.dbar`

`dbar f z = ½(D1 + i·DI)` with `D = fderiv ℝ f z` is a fixed linear read-off of the real
Fréchet derivative, so it inherits congruence/linearity/Leibniz from `fderiv ℝ` pointwise. -/

namespace DbarDisk

/-- `∂̄` only depends on the germ: functions agreeing near `z` have equal `∂̄` at `z`. -/
theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  unfold dbar
  rw [h.fderiv_eq]

/-- Additivity of `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  unfold dbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Subtraction rule for `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  unfold dbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Finite sums commute with `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dbar (f i) z := by
  unfold dbar
  rw [fderiv_fun_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-- **Wirtinger–Leibniz product rule**: `∂̄(f·g) = f·∂̄g + g·∂̄f` at a common point of real
differentiability (`∂̄` is a derivation, like each directional `fderiv ℝ`). -/
theorem dbar_fun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  unfold dbar
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Constants scale through `∂̄` at points of real differentiability. -/
theorem dbar_fun_const_mul (a : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w => a * f w) z = a * dbar f z := by
  rw [dbar_fun_mul (differentiableAt_const a) hf, dbar_const]
  ring

/-- `∂̄` of a `C¹` function is continuous at points of `C¹`-ness (local statement: only
`ContDiffAt ℝ 1` is assumed, which yields a neighbourhood on which `fderiv ℝ` is continuous). -/
theorem continuousAt_dbar_of_contDiffAt {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 1 f z) :
    ContinuousAt (dbar f) z := by
  obtain ⟨u, hu_mem, hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hvu, hv_open, hzv⟩ := _root_.mem_nhds_iff.mp hu_mem
  have h1 : ContinuousAt (fderiv ℝ f) z :=
    (((hu.mono hvu).continuousOn_fderiv_of_isOpen hv_open le_rfl).continuousAt
      (hv_open.mem_nhds hzv))
  exact continuousAt_const.mul ((h1.clm_apply continuousAt_const).add
    (continuousAt_const.mul (h1.clm_apply continuousAt_const)))

end DbarDisk

namespace Jacobians.Dolbeault

/-! ### §2 — `∂̄` of a radial profile of the squared modulus

For `χ(w) = η(normSq (w − c))` with `η : ℝ → ℝ` of class `C¹`,

  `∂̄χ(z) = η'(normSq (z−c)) · (z − c)`:

the `½` in `∂̄ = ½(∂ₓ + i∂_y)` exactly cancels the `2` from differentiating the squared
modulus, and `(∂ₓ + i∂_y)(x² + y²)/2 = x + iy`.  Using `normSq` (a polynomial in `re`/`im`)
avoids the `‖·‖`-at-zero pathology: the formula holds at **every** `z`, including `z = c`. -/

/-- The shifted squared modulus `w ↦ normSq (w − c)` is real-differentiable, with derivative
`v ↦ 2((z−c).re·v.re + (z−c).im·v.im)` (assembled from `reCLM`/`imCLM`). -/
theorem hasFDerivAt_normSq_sub (c z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq (w - c))
      ((z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + ((z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ)
          + (z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ))) z := by
  have hre : HasFDerivAt (fun w : ℂ => (w - c).re) (Complex.reCLM : ℂ →L[ℝ] ℝ) z := by
    have h := (Complex.reCLM.hasFDerivAt (x := z - c)).comp z (hasFDerivAt_sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have him : HasFDerivAt (fun w : ℂ => (w - c).im) (Complex.imCLM : ℂ →L[ℝ] ℝ) z := by
    have h := (Complex.imCLM.hasFDerivAt (x := z - c)).comp z (hasFDerivAt_sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  refine HasFDerivAt.congr_of_eventuallyEq ((hre.mul hre).add (him.mul him)) ?_
  exact Filter.Eventually.of_forall fun w => by
    simp [Complex.normSq_apply]

/-- **`∂̄` of a complexified radial profile**: `∂̄(η ∘ normSq(·−c))(z) = η'(normSq(z−c))·(z−c)`.
Valid at every `z` (no puncture needed): `normSq` is polynomial. -/
theorem dbar_comp_normSq {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c z : ℂ) :
    DbarDisk.dbar (fun w => (η (Complex.normSq (w - c)) : ℂ)) z
      = Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) := by
  have hη' : HasDerivAt η (deriv η (Complex.normSq (z - c))) (Complex.normSq (z - c)) :=
    ((hη.differentiable one_ne_zero) _).hasDerivAt
  have hcomp := hη'.comp_hasFDerivAt z (hasFDerivAt_normSq_sub c z)
  have hC : HasFDerivAt (fun w : ℂ => (η (Complex.normSq (w - c)) : ℂ))
      (Complex.ofRealCLM.comp (deriv η (Complex.normSq (z - c)) •
        ((z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ)
          + ((z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ)
            + (z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ))))) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hcomp
  rw [DbarDisk.dbar, hC.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  linear_combination (Complex.ofReal (deriv η (Complex.normSq (z - c))))
    * (Complex.re_add_im (z - c))

/-- The radial profile is real-differentiable at every point (needed as a `DifferentiableAt ℝ`
input to the Leibniz rule). -/
theorem differentiableAt_comp_normSq {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c z : ℂ) :
    DifferentiableAt ℝ (fun w => (η (Complex.normSq (w - c)) : ℂ)) z := by
  have hη' : HasDerivAt η (deriv η (Complex.normSq (z - c))) (Complex.normSq (z - c)) :=
    ((hη.differentiable one_ne_zero) _).hasDerivAt
  exact (Complex.ofRealCLM.hasFDerivAt.comp z
    (hη'.comp_hasFDerivAt z (hasFDerivAt_normSq_sub c z))).differentiableAt

/-! ### §3 — an explicit `C¹` radial profile from `Real.smoothTransition` -/

/-- The derivative of a profile that is constant `1` on `(-∞, s₀]` vanishes on the open ray
`(-∞, s₀)` (local constancy). -/
theorem deriv_profile_eq_zero_left {η : ℝ → ℝ} {s₀ : ℝ} (h1 : ∀ s ≤ s₀, η s = 1)
    {s : ℝ} (hs : s < s₀) : deriv η s = 0 := by
  have hev : η =ᶠ[𝓝 s] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact h1 t (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-- The derivative of a profile that is constant `0` on `[s₁, ∞)` vanishes on the open ray
`(s₁, ∞)` (local constancy). -/
theorem deriv_profile_eq_zero_right {η : ℝ → ℝ} {s₁ : ℝ} (h0 : ∀ s, s₁ ≤ s → η s = 0)
    {s : ℝ} (hs : s₁ < s) : deriv η s = 0 := by
  have hev : η =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact h0 t (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-! ### §4 — `resAt` of negative powers and of finite principal parts

Extensions of the `Residue.lean` API: residues of `(z−c)^{−k}` (`= δ_{k,1}`), closure of
`HoloPunctured` under sums, and `resAt` of a finite sum. -/

/-- `(w − c)^n` is holomorphic off `c`. -/
theorem differentiableAt_zpow_sub (c : ℂ) (n : ℤ) {z : ℂ} (hz : z ≠ c) :
    DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
  ((differentiableAt_zpow (m := n)).mpr (Or.inl (sub_ne_zero_of_ne hz))).comp z
    (differentiableAt_id.sub_const c)

/-- Scaled negative powers of `(· − c)` have isolated singularities at `c`. -/
theorem holoPunctured_const_mul_zpow (a c : ℂ) (n : ℤ) :
    HoloPunctured (fun z => a * (z - c) ^ n) c :=
  ⟨1, one_pos, fun _ hz =>
    (differentiableAt_zpow_sub c n (Set.mem_singleton_iff.not.mp hz.2)).const_mul a⟩

/-- `HoloPunctured` is closed under pointwise addition (intersect the two punctured balls). -/
theorem HoloPunctured.add {f g : ℂ → ℂ} {c : ℂ} (hf : HoloPunctured f c)
    (hg : HoloPunctured g c) : HoloPunctured (fun z => f z + g z) c := by
  obtain ⟨ρf, hρf, hf'⟩ := hf
  obtain ⟨ρg, hρg, hg'⟩ := hg
  refine ⟨min ρf ρg, lt_min hρf hρg, fun z hz => ?_⟩
  exact (hf' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩).add
    (hg' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩)

/-- `HoloPunctured` is closed under finite sums. -/
theorem holoPunctured_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ}
    (hf : ∀ i ∈ s, HoloPunctured (f i) c) :
    HoloPunctured (fun z => ∑ i ∈ s, f i z) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pos, fun z _ => ?_⟩
    simp only [Finset.sum_empty]
    exact differentiableAt_const (0 : ℂ)
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine h.imp fun ρ hρ => ⟨hρ.1, fun z hz => ?_⟩
    have := hρ.2 z hz
    simpa [Finset.sum_insert ha] using this

/-- **`resAt` of a finite sum** of functions with isolated singularities. -/
theorem resAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ}
    (hf : ∀ i ∈ s, HoloPunctured (f i) c) :
    resAt (fun z => ∑ i ∈ s, f i z) c = ∑ i ∈ s, resAt (f i) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact resAt_eq_zero_of_differentiableOn_ball one_pos fun z _ => differentiableAt_const 0
  | insert a s ha ih =>
    have hsum : HoloPunctured (fun z => ∑ i ∈ s, f i z) c :=
      holoPunctured_finset_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hone : HoloPunctured (f a) c := hf a (Finset.mem_insert_self a s)
    have hadd := resAt_add hone hsum
    have hfun : (fun z => ∑ i ∈ insert a s, f i z)
        = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z
      exact Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha, ← ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    exact hadd

/-- **`Res_c((·−c)^{−k}) = 0` for `k ≠ 1`** (all small contour integrals vanish:
`circleIntegral.integral_sub_zpow_of_ne`). -/
theorem resAt_zpow_neg_of_ne {c : ℂ} {k : ℕ} (hk : k ≠ 1) :
    resAt (fun z => (z - c) ^ (-(k : ℤ))) c = 0 := by
  have hn : (-(k : ℤ)) ≠ -1 := by
    intro h
    exact hk (by exact_mod_cast neg_inj.mp h)
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), (z - c) ^ (-(k : ℤ))) = 0 :=
    Filter.Eventually.of_forall fun r => circleIntegral.integral_sub_zpow_of_ne hn c c r
  rw [resAt_eq_of_eventuallyEq_circleIntegral h, smul_zero]

/-- **`Res_c((·−c)^{−1}) = 1`** (the `zpow` phrasing of `resAt_sub_inv`). -/
theorem resAt_zpow_neg_one (c : ℂ) :
    resAt (fun z => (z - c) ^ (-(1 : ℕ) : ℤ)) c = 1 := by
  have hfun : (fun z : ℂ => (z - c) ^ (-(1 : ℕ) : ℤ)) = fun z => (z - c)⁻¹ := by
    funext z
    norm_num
  rw [hfun, resAt_sub_inv]

/-- **`resAt` of a single principal-part term**: `Res_c(b·(·−c)^{−k}) = b·δ_{k,1}`. -/
theorem resAt_const_mul_zpow_neg (b c : ℂ) (k : ℕ) :
    resAt (fun z => b * (z - c) ^ (-(k : ℤ))) c = b * (if k = 1 then 1 else 0) := by
  have hsmul : (fun z => b * (z - c) ^ (-(k : ℤ)))
      = b • fun z : ℂ => (z - c) ^ (-(k : ℤ)) := rfl
  rw [hsmul, resAt_smul b ⟨1, one_pos, fun _ hz =>
    differentiableAt_zpow_sub c _ (Set.mem_singleton_iff.not.mp hz.2)⟩]
  by_cases hk : k = 1
  · subst hk
    rw [resAt_zpow_neg_one, if_pos rfl, smul_eq_mul]
  · rw [resAt_zpow_neg_of_ne hk, if_neg hk]
    simp

/-! ### §5 — the single-term integral `∫ ∂̄(χ·(·−c)^{−k}) = −π·δ_{k,1}` (Forster (10.21))

With the radial cutoff `χ = η(normSq(·−c))`, off the centre the integrand is the closed form
`η'(normSq(z−c))·(z−c)^{1−k}` (Leibniz + holomorphy of the power).  In polar coordinates it
separates: the angular factor `∮ e^{i(1−k)θ}dθ` vanishes unless `k = 1` (where it is `2π`),
and the radial factor is the FTC integral `∫_0^∞ r·η'(r²) dr = −½`.  No integrability of the
2-dimensional integrand is ever needed: the polar change of variables and the product-measure
splitting in Mathlib are unconditional. -/

/-- Pointwise closed form off the centre:
`∂̄(η(normSq(·−c))·(·−c)^n)(z) = η'(normSq(z−c))·(z−c)^{n+1}` for `z ≠ c`. -/
theorem dbar_radialProfile_mul_zpow {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c : ℂ) (n : ℤ)
    {z : ℂ} (hz : z ≠ c) :
    DbarDisk.dbar (fun w => (η (Complex.normSq (w - c)) : ℂ) * (w - c) ^ n) z
      = Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) ^ (n + 1) := by
  have hzc : z - c ≠ 0 := sub_ne_zero_of_ne hz
  have hu : DifferentiableAt ℂ (fun w => (w - c) ^ n) z := differentiableAt_zpow_sub c n hz
  rw [DbarDisk.dbar_fun_mul (differentiableAt_comp_normSq hη c z) (hu.restrictScalars ℝ),
    DbarDisk.dbar_eq_zero_of_differentiableAt hu, mul_zero, zero_add,
    dbar_comp_normSq hη c z, zpow_add₀ hzc n 1, zpow_one]
  ring

-- restore default transparency here: under `respectTransparency false` the `HasDerivAt.comp`
-- unifier solves `?h x =?= x ^ 2` through `npowRec` junk instead of `fun r => r ^ 2`
set_option backward.isDefEq.respectTransparency true in
/-- The radial FTC integral: `∫_0^∞ r·η'(r²) dr = ½(η(∞) − η(0)) = −½` for a profile going
`1 → 0`.  (`η'` has compact support, so the improper integral is honest.) -/
theorem integral_rmul_deriv_profile {η : ℝ → ℝ} {s₀ s₁ : ℝ} (hη : ContDiff ℝ 1 η)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (h1 : ∀ s ≤ s₀, η s = 1) (h0 : ∀ s, s₁ ≤ s → η s = 0) :
    ∫ r in Ioi (0 : ℝ), r * deriv η (r ^ 2) = -(1 / 2) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun r => η (r ^ 2) / 2) (x * deriv η (x ^ 2)) x := by
    intro x _
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hd : HasDerivAt η (deriv η (x ^ 2)) (x ^ 2) :=
      ((hη.differentiable one_ne_zero) _).hasDerivAt
    -- pin the inner function by name: positional elaboration commits a garbage `?h x =?= x ^ 2`
    -- higher-order solution before the expected type is consulted
    have hcomp : HasDerivAt (η ∘ fun r : ℝ => r ^ 2) (deriv η (x ^ 2) * (2 * x)) x :=
      HasDerivAt.comp (h := fun r : ℝ => r ^ 2) x hd hsq
    have h3 := hcomp.div_const 2
    convert h3 using 1
    · rfl
    · ring
  have hcont : ContinuousWithinAt (fun r : ℝ => η (r ^ 2) / 2) (Ici 0) 0 :=
    ((hη.continuous.comp (continuous_pow 2)).div_const 2).continuousWithinAt
  have hcont' : Continuous fun r : ℝ => r * deriv η (r ^ 2) :=
    continuous_id.mul ((hη.continuous_deriv le_rfl).comp (continuous_pow 2))
  have hsupp : HasCompactSupport fun r : ℝ => r * deriv η (r ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(max 1 s₁)) (b := max 1 s₁)) ?_
    intro r hr
    have habs : max 1 s₁ < |r| := by
      by_contra h
      push Not at h
      exact hr (by simpa [Set.mem_Icc] using abs_le.mp h)
    have hsq : s₁ < r ^ 2 := by
      nlinarith [sq_abs r, le_max_left (1 : ℝ) s₁, le_max_right (1 : ℝ) s₁, abs_nonneg r]
    rw [deriv_profile_eq_zero_right h0 hsq, mul_zero]
  have hint : IntegrableOn (fun r : ℝ => r * deriv η (r ^ 2)) (Ioi 0) :=
    (hcont'.integrable_of_hasCompactSupport hsupp).integrableOn
  have htends : Tendsto (fun r : ℝ => η (r ^ 2) / 2) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop] fun r => η (r ^ 2) / 2 := by
      filter_upwards [eventually_ge_atTop (max 1 s₁)] with r hr
      have ha : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
      have hb : s₁ ≤ r := (le_max_right _ _).trans hr
      rw [h0 _ (by nlinarith), zero_div]
    exact Tendsto.congr' hev tendsto_const_nhds
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htends]
  rw [show η (0 ^ 2) = 1 from h1 _ (by simpa using hs₀.le)]
  norm_num

/-- The angular integral `∫_{−π}^{π} (e^{iθ})^m dθ` vanishes for `m ≠ 0`: FTC with
antiderivative `e^{imθ}/(im)`, and `e^{±imπ} = (−1)^m` agree. -/
theorem integral_Ioo_exp_mul_I_zpow {m : ℤ} (hm : m ≠ 0) :
    ∫ θ in Ioo (-π) π, Complex.exp (θ * Complex.I) ^ m = 0 := by
  have hC : ((m : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
  have hcongr : EqOn (fun θ : ℝ => Complex.exp (θ * Complex.I) ^ m)
      (fun θ : ℝ => Complex.exp (((m : ℂ) * Complex.I) * θ)) (Set.uIcc (-π) π) := by
    intro θ _
    simp only
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [intervalIntegral.integral_congr hcongr, integral_exp_mul_complex hC]
  have h1 : Complex.exp (((m : ℂ) * Complex.I) * (π : ℝ)) = (-1 : ℂ) ^ m := by
    rw [show ((m : ℂ) * Complex.I) * (π : ℝ) = (m : ℂ) * ((π : ℝ) * Complex.I) by ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have h2 : Complex.exp (((m : ℂ) * Complex.I) * ((-π : ℝ) : ℂ)) = ((-1 : ℂ) ^ m)⁻¹ := by
    rw [show ((m : ℂ) * Complex.I) * ((-π : ℝ) : ℂ) = ((-m : ℤ) : ℂ) * ((π : ℝ) * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_neg]
  have h3 : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact Even.neg_one_zpow ⟨m, rfl⟩
  rw [h1, h2, h3, sub_self, zero_div]

/-- The angular integral for `m = 0`: `∫_{−π}^{π} 1 dθ = 2π`. -/
theorem integral_Ioo_one_complex :
    ∫ _ in Ioo (-π) π, (1 : ℂ) = ((2 * π : ℝ) : ℂ) := by
  rw [MeasureTheory.setIntegral_const, Complex.real_smul, mul_one]
  norm_cast
  rw [measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π - -π)]
  ring

/-- **The Forster (10.21) single-term computation.**  For the radial cutoff
`χ = η(normSq(·−c))` (profile `1 → 0` between `s₀` and `s₁`),

  `∫_ℂ ∂̄(χ·(·−c)^{−k}) = −π·δ_{k,1}`.

Off `c` the integrand is `η'(normSq(z−c))·(z−c)^{1−k}` (supported in the closed annulus
`s₀ ≤ normSq(z−c) ≤ s₁`); in polar coordinates it separates into the radial FTC factor and
the angular character integral. -/
theorem integral_dbar_radialCutoff_zpow (c : ℂ) {η : ℝ → ℝ} {s₀ s₁ : ℝ} (hη : ContDiff ℝ 1 η)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (h1 : ∀ s ≤ s₀, η s = 1) (h0 : ∀ s, s₁ ≤ s → η s = 0)
    (k : ℕ) :
    ∫ z : ℂ, DbarDisk.dbar
        (fun w => (η (Complex.normSq (w - c)) : ℂ) * (w - c) ^ (-(k : ℤ))) z
      = if k = 1 then -(π : ℂ) else 0 := by
  -- (1) replace by the closed form (they agree off the null set `{c}`)
  have h_ae : (fun z => DbarDisk.dbar
        (fun w => (η (Complex.normSq (w - c)) : ℂ) * (w - c) ^ (-(k : ℤ))) z)
      =ᵐ[volume] fun z =>
        Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) ^ (-(k : ℤ) + 1) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
    exact dbar_radialProfile_mul_zpow hη c (-(k : ℤ)) hz
  rw [integral_congr_ae h_ae]
  -- (2) recentre at the origin (translation invariance of planar Lebesgue measure)
  have htrans : (∫ z : ℂ,
        Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) ^ (-(k : ℤ) + 1))
      = ∫ z : ℂ, Complex.ofReal (deriv η (Complex.normSq z)) * z ^ (-(k : ℤ) + 1) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun z : ℂ => Complex.ofReal (deriv η (Complex.normSq z)) * z ^ (-(k : ℤ) + 1)) (-c)]
    congr 1
    funext z
    rw [show -c + z = z - c from by ring]
  rw [htrans]
  -- (3) polar coordinates (unconditional change of variables)
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [polarCoord_target]
  -- (4) on the target the integrand separates into radial × angular
  have hprod := MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
    (fun r : ℝ => (r : ℂ) * Complex.ofReal (deriv η (r ^ 2)) * (r : ℂ) ^ (-(k : ℤ) + 1))
    (fun θ : ℝ => Complex.exp (θ * Complex.I) ^ (-(k : ℤ) + 1))
    (Ioi 0) (Ioo (-π) π)
  rw [← Measure.volume_eq_prod] at hprod
  have hsep : EqOn
      (fun p : ℝ × ℝ => p.1 • (Complex.ofReal
          (deriv η (Complex.normSq (Complex.polarCoord.symm p)))
        * (Complex.polarCoord.symm p) ^ (-(k : ℤ) + 1)))
      (fun p : ℝ × ℝ =>
        (fun r : ℝ => (r : ℂ) * Complex.ofReal (deriv η (r ^ 2)) * (r : ℂ) ^ (-(k : ℤ) + 1)) p.1
        * (fun θ : ℝ => Complex.exp (θ * Complex.I) ^ (-(k : ℤ) + 1)) p.2)
      (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    have hsymm : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp (θ * Complex.I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos,
        Complex.ofReal_sin]
    have hnsq1 : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
      ring_nf
      linear_combination Real.sin_sq_add_cos_sq θ
    -- state the `normSq` value in the post-`hsymm` product form (rewrite order matters)
    have hnormSq : Complex.normSq ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r ^ 2 := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal, hnsq1]
      ring
    simp only
    rw [hsymm, hnormSq, mul_zpow, Complex.real_smul]
    ring
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hsep, hprod]
  -- (5) evaluate
  by_cases hk : k = 1
  · subst hk
    have hexp : (-(1 : ℕ) : ℤ) + 1 = 0 := by norm_num
    simp only [hexp, zpow_zero, mul_one, if_pos]
    have hrad : (∫ r in Ioi (0 : ℝ), (r : ℂ) * Complex.ofReal (deriv η (r ^ 2)))
        = ((-(1 / 2) : ℝ) : ℂ) := by
      have heq : ∀ r : ℝ, (r : ℂ) * Complex.ofReal (deriv η (r ^ 2))
          = ((r * deriv η (r ^ 2) : ℝ) : ℂ) := fun r => by push_cast; ring
      simp_rw [heq]
      -- `exact` tolerates the `RCLike.ofReal`-vs-`Complex.ofReal` coercion heads where `rw` fails
      calc ∫ r in Ioi (0 : ℝ), ((r * deriv η (r ^ 2) : ℝ) : ℂ)
          = ((∫ r in Ioi (0 : ℝ), r * deriv η (r ^ 2) : ℝ) : ℂ) := integral_ofReal
        _ = ((-(1 / 2) : ℝ) : ℂ) := by
            rw [integral_rmul_deriv_profile hη hs₀ hs h1 h0]
    rw [hrad, integral_Ioo_one_complex]
    push_cast
    ring
  · have hm : (-(k : ℤ) + 1) ≠ 0 := by omega
    rw [integral_Ioo_exp_mul_I_zpow hm, mul_zero, if_neg hk]

end Jacobians.Dolbeault
