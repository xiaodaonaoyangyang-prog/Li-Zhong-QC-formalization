import LiZhongQC.Ch05.S19_Schwarzian
import LiZhongQC.Ch04.S18_BoundedTurning

/-!
# §20 Schwarz 区域 — Schwarz domains

* Definition (§20.1): `a`-Schwarz domains and the inner radius of univalence `σ₃(D)`
                                                         — `IsSchwarzDomain`, `innerUnivalenceRadius`
* Theorem 20.1 (`σ₃(Δ) = 1/2`)                          — `thm20_1_*`
* Theorem 20.2 (quasiconformal extension when `‖S_f‖_Δ < 1/2`) — `thm20_2`
* Lemmas 20.1–20.3 (regular quasiconformal reflections)
* Theorem 20.3 (Ahlfors: quasidiscs are Schwarz domains) and (20.20)
* `k`-local connectivity, Theorem 20.4
* Theorem 20.5 (Gehring: Schwarz domains are quasidiscs)
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **Definition** (§20.1).  `D` is an `a`-Schwarz domain: every locally univalent meromorphic `f`
in `D` with `‖S_f‖_D < a` is univalent in `D`. -/
def IsSchwarzDomain (D : Set ℂ) (a : ℝ) : Prop :=
  IsHyperbolicSimplyConnected D ∧ 0 < a ∧
    ∀ f : ℂ → ℂ, IsLocUnivMero f D → schwarzianNorm f D < ENNReal.ofReal a → IsUnivMero f D

/-- The inner radius of univalence (单叶性内径) `σ₃(D)`: the supremum of all `a` for which `D` is an
`a`-Schwarz domain. -/
def innerUnivalenceRadius (D : Set ℂ) : ℝ := sSup {a : ℝ | IsSchwarzDomain D a}

/-! ### Helpers for Theorem 20.1 (`neh_`): Nehari's argument on the diameter

Along the real segment `[0, r]`, `r < 1`, a solution `u` of `u'' + (ψ/2) u = 0` vanishing at both
endpoints satisfies the energy identity `∫ |u'|² = ∫ Re(ψ/2) |u|²` and the Hardy inequality
`∫ |u|²/(1 - x²)² ≤ ∫ |u'|²`; when `|ψ(x)| ≤ 4N/(1 - x²)²` with `N < 1/2` these force `u'(0) = 0`. -/

theorem neh_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

theorem neh_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf

theorem neh_one_sub_sq_pos {r x : ℝ} (hr1 : r < 1) (hx : x ∈ Icc 0 r) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

/-- The Hardy identity on `[0, r]`, `r < 1`, for a real `C¹` function vanishing at the endpoints:
`∫ u'² = ∫ (u' + x u/(1-x²))² + ∫ u²/(1-x²)²`. -/
theorem neh_hardy_identity_real {u u' : ℝ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' (Icc 0 r))
    (h0 : u 0 = 0) (hr : u r = 0) :
    ∫ x in (0 : ℝ)..r, u' x ^ 2 =
      (∫ x in (0 : ℝ)..r, (u' x + x * u x / (1 - x ^ 2)) ^ 2) +
        ∫ x in (0 : ℝ)..r, u x ^ 2 / (1 - x ^ 2) ^ 2 := by
  have hne : ∀ x ∈ Icc (0 : ℝ) r, (1 : ℝ) - x ^ 2 ≠ 0 := fun x hx =>
    (neh_one_sub_sq_pos hr1 hx).ne'
  have hcu : ContinuousOn u (Icc 0 r) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcq : ContinuousOn (fun x : ℝ => 1 - x ^ 2) (Icc 0 r) :=
    continuousOn_const.sub (continuousOn_id.pow 2)
  have hcw : ContinuousOn (fun x : ℝ => x / (1 - x ^ 2)) (Icc 0 r) :=
    continuousOn_id.div hcq hne
  have hcw2 : ContinuousOn (fun x : ℝ => (1 + x ^ 2) / (1 - x ^ 2) ^ 2) (Icc 0 r) :=
    (continuousOn_const.add (continuousOn_id.pow 2)).div (hcq.pow 2)
      (fun x hx => pow_ne_zero 2 (hne x hx))
  -- the antiderivative `F x = x/(1-x²) · u x ^ 2`
  have hF : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt (fun x => x / (1 - x ^ 2) * u x ^ 2)
      ((1 + x ^ 2) / (1 - x ^ 2) ^ 2 * u x ^ 2 + x / (1 - x ^ 2) * (2 * u x * u' x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => x / (1 - x ^ 2)) ((1 + x ^ 2) / (1 - x ^ 2) ^ 2) x := by
      have hq : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
      have := (hasDerivAt_id' x).div hq (hne x hx)
      convert this using 1
      field_simp
      ring
    have h2 : HasDerivAt (fun x => u x ^ 2) (2 * u x * u' x) x := by
      convert (hu x hx).pow 2 using 1
      push_cast
      ring
    exact h1.mul h2
  have hFint : IntervalIntegrable
      (fun x => (1 + x ^ 2) / (1 - x ^ 2) ^ 2 * u x ^ 2 + x / (1 - x ^ 2) * (2 * u x * u' x))
      volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (hcw2.mul (hcu.pow 2)).add (hcw.mul ((continuousOn_const.mul hcu).mul hu'))
  have hint0 : ∫ x in (0 : ℝ)..r,
      ((1 + x ^ 2) / (1 - x ^ 2) ^ 2 * u x ^ 2 + x / (1 - x ^ 2) * (2 * u x * u' x)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hF x (by rwa [uIcc_of_le hr0] at hx)) hFint]
    simp [h0, hr]
  have hpt : EqOn (fun x => u' x ^ 2)
      (fun x => ((u' x + x * u x / (1 - x ^ 2)) ^ 2 + u x ^ 2 / (1 - x ^ 2) ^ 2)
        - ((1 + x ^ 2) / (1 - x ^ 2) ^ 2 * u x ^ 2 + x / (1 - x ^ 2) * (2 * u x * u' x)))
      (uIcc 0 r) := by
    intro x hx
    rw [uIcc_of_le hr0] at hx
    have := hne x hx
    field_simp
    ring
  have hi1 : IntervalIntegrable (fun x => (u' x + x * u x / (1 - x ^ 2)) ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (hu'.add ((continuousOn_id.mul hcu).div hcq hne)).pow 2
  have hi2 : IntervalIntegrable (fun x => u x ^ 2 / (1 - x ^ 2) ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (hcu.pow 2).div (hcq.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub (hi1.add hi2) hFint,
    intervalIntegral.integral_add hi1 hi2, hint0, sub_zero]

/-- The Hardy inequality on `[0, r]`, `r < 1`, real-valued. -/
theorem neh_hardy_real {u u' : ℝ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' (Icc 0 r))
    (h0 : u 0 = 0) (hr : u r = 0) :
    ∫ x in (0 : ℝ)..r, u x ^ 2 / (1 - x ^ 2) ^ 2 ≤ ∫ x in (0 : ℝ)..r, u' x ^ 2 := by
  rw [neh_hardy_identity_real hr0 hr1 hu hu' h0 hr]
  have : 0 ≤ ∫ x in (0 : ℝ)..r, (u' x + x * u x / (1 - x ^ 2)) ^ 2 :=
    intervalIntegral.integral_nonneg hr0 fun x _ => sq_nonneg _
  linarith

/-- The Hardy inequality on `[0, r]`, `r < 1`, for complex-valued functions. -/
theorem neh_hardy {u u' : ℝ → ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' (Icc 0 r))
    (h0 : u 0 = 0) (hr : u r = 0) :
    ∫ x in (0 : ℝ)..r, ‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2 ≤ ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 := by
  have hne : ∀ x ∈ Icc (0 : ℝ) r, (1 : ℝ) - x ^ 2 ≠ 0 := fun x hx =>
    (neh_one_sub_sq_pos hr1 hx).ne'
  have hcu : ContinuousOn u (Icc 0 r) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcq : ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ 2) (Icc 0 r) :=
    (continuousOn_const.sub (continuousOn_id.pow 2)).pow 2
  have hcq' : ∀ x ∈ Icc (0 : ℝ) r, (1 - x ^ 2) ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (hne x hx)
  have hre := neh_hardy_real hr0 hr1 (fun x hx => neh_hasDerivAt_re (hu x hx))
    (Complex.continuous_re.comp_continuousOn hu') (by simp [h0]) (by simp [hr])
  have him := neh_hardy_real hr0 hr1 (fun x hx => neh_hasDerivAt_im (hu x hx))
    (Complex.continuous_im.comp_continuousOn hu') (by simp [h0]) (by simp [hr])
  have e1 : ∀ x, ‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2 =
      (u x).re ^ 2 / (1 - x ^ 2) ^ 2 + (u x).im ^ 2 / (1 - x ^ 2) ^ 2 := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have e2 : ∀ x, ‖u' x‖ ^ 2 = (u' x).re ^ 2 + (u' x).im ^ 2 := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [e1, e2]
  have hi1 : IntervalIntegrable (fun x => (u x).re ^ 2 / (1 - x ^ 2) ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact ((Complex.continuous_re.comp_continuousOn hcu).pow 2).div hcq hcq'
  have hi2 : IntervalIntegrable (fun x => (u x).im ^ 2 / (1 - x ^ 2) ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact ((Complex.continuous_im.comp_continuousOn hcu).pow 2).div hcq hcq'
  have hi3 : IntervalIntegrable (fun x => (u' x).re ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (Complex.continuous_re.comp_continuousOn hu').pow 2
  have hi4 : IntervalIntegrable (fun x => (u' x).im ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (Complex.continuous_im.comp_continuousOn hu').pow 2
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_add hi3 hi4]
  exact add_le_add hre him

/-- The energy identity for a solution of `u'' + (ψ/2) u = 0` on `[0, r]` vanishing at both
endpoints: `∫ |u'|² = ∫ Re(ψ/2) |u|²`. -/
theorem neh_ode_energy {u u' u'' ψ : ℝ → ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hu : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u' (u'' x) x)
    (hψ : ContinuousOn ψ (Icc 0 r)) (hode : ∀ x ∈ Icc (0 : ℝ) r, u'' x = -(ψ x / 2) * u x)
    (h0 : u 0 = 0) (hr : u r = 0) :
    ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 = ∫ x in (0 : ℝ)..r, (ψ x / 2).re * ‖u x‖ ^ 2 := by
  have hcu : ContinuousOn u (Icc 0 r) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcu' : ContinuousOn u' (Icc 0 r) := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
  -- `G x = Re u' · Re u + Im u' · Im u` has derivative `|u'|² - Re(ψ/2) |u|²`
  have hG : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt (fun x => (u' x).re * (u x).re + (u' x).im * (u x).im)
        (‖u' x‖ ^ 2 - (ψ x / 2).re * ‖u x‖ ^ 2) x := by
    intro x hx
    have h1 := (neh_hasDerivAt_re (hu' x hx)).mul (neh_hasDerivAt_re (hu x hx))
    have h2 := (neh_hasDerivAt_im (hu' x hx)).mul (neh_hasDerivAt_im (hu x hx))
    convert h1.add h2 using 1
    rw [hode x hx, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
    ring
  have hi1 : IntervalIntegrable (fun x => ‖u' x‖ ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact hcu'.norm.pow 2
  have hi2 : IntervalIntegrable (fun x => (ψ x / 2).re * ‖u x‖ ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact (Complex.continuous_re.comp_continuousOn (hψ.div_const 2)).mul (hcu.norm.pow 2)
  have hint0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hG x (by rwa [uIcc_of_le hr0] at hx)) (hi1.sub hi2)
  simp only [h0, hr, Complex.zero_re, Complex.zero_im, mul_zero, add_zero, sub_self] at hint0
  rw [intervalIntegral.integral_sub hi1 hi2] at hint0
  linarith

/-- **Nehari's argument on the diameter.**  If `u'' + (ψ/2) u = 0` on `[0, r]` (`0 < r < 1`) with
`|ψ(x)| ≤ 4N/(1 - x²)²`, `N < 1/2`, and `u(0) = u(r) = 0`, then `u'(0) = 0`. -/
theorem neh_core {u u' u'' ψ : ℝ → ℂ} {r N : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hN : N < 1 / 2)
    (hu : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt u' (u'' x) x)
    (hψ : ContinuousOn ψ (Icc 0 r)) (hode : ∀ x ∈ Icc (0 : ℝ) r, u'' x = -(ψ x / 2) * u x)
    (hbound : ∀ x ∈ Icc (0 : ℝ) r, ‖ψ x‖ ≤ 4 * N / (1 - x ^ 2) ^ 2)
    (h0 : u 0 = 0) (hr : u r = 0) : u' 0 = 0 := by
  by_contra hne
  have hcu : ContinuousOn u (Icc 0 r) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcu' : ContinuousOn u' (Icc 0 r) := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
  have hN0 : 0 ≤ N := by
    have := hbound 0 ⟨le_rfl, hr0.le⟩
    have h0' := norm_nonneg (ψ 0)
    simp only [zero_pow two_ne_zero, sub_zero, one_pow, div_one] at this
    linarith
  have hHE := neh_hardy hr0.le hr1 hu hcu' h0 hr
  have hEeq := neh_ode_energy hr0.le hu hu' hψ hode h0 hr
  -- pointwise: `Re(ψ/2) |u|² ≤ 2N · |u|²/(1-x²)²`
  have hpt : ∀ x ∈ Icc (0 : ℝ) r,
      (ψ x / 2).re * ‖u x‖ ^ 2 ≤ 2 * N * (‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2) := by
    intro x hx
    have hpos := neh_one_sub_sq_pos hr1 hx
    have h1 : (ψ x / 2).re ≤ ‖ψ x‖ / 2 := by
      have := Complex.re_le_norm (ψ x / 2)
      rwa [norm_div, Complex.norm_ofNat] at this
    have h2 : ‖ψ x‖ / 2 ≤ 2 * N / (1 - x ^ 2) ^ 2 := by
      have := hbound x hx
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc ‖ψ x‖ ≤ 4 * N / (1 - x ^ 2) ^ 2 := this
        _ = 2 * N / (1 - x ^ 2) ^ 2 * 2 := by ring
    calc (ψ x / 2).re * ‖u x‖ ^ 2 ≤ 2 * N / (1 - x ^ 2) ^ 2 * ‖u x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
      _ = 2 * N * (‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2) := by ring
  have hcq : ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ 2) (Icc 0 r) :=
    (continuousOn_const.sub (continuousOn_id.pow 2)).pow 2
  have hi1 : IntervalIntegrable (fun x => (ψ x / 2).re * ‖u x‖ ^ 2) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0.le]
    exact (Complex.continuous_re.comp_continuousOn (hψ.div_const 2)).mul (hcu.norm.pow 2)
  have hi2 : IntervalIntegrable (fun x => 2 * N * (‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2)) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0.le]
    exact continuousOn_const.mul ((hcu.norm.pow 2).div hcq
      (fun x hx => pow_ne_zero 2 (neh_one_sub_sq_pos hr1 hx).ne'))
  have hle := intervalIntegral.integral_mono_on hr0.le hi1 hi2 hpt
  rw [intervalIntegral.integral_const_mul] at hle
  -- `E > 0` since `u'(0) ≠ 0`
  have hEpos : 0 < ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 := by
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hr0
      (f := fun _ => (0 : ℝ)) continuousOn_const (hcu'.norm.pow 2) (fun x _ => sq_nonneg _)
      ⟨0, ⟨le_rfl, hr0.le⟩, pow_pos (norm_pos_iff.2 hne) 2⟩
    simpa using this
  have hchain : ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 ≤ 2 * N * ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 := by
    calc ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 = ∫ x in (0 : ℝ)..r, (ψ x / 2).re * ‖u x‖ ^ 2 := hEeq
      _ ≤ 2 * N * ∫ x in (0 : ℝ)..r, ‖u x‖ ^ 2 / (1 - x ^ 2) ^ 2 := hle
      _ ≤ 2 * N * ∫ x in (0 : ℝ)..r, ‖u' x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hHE (by linarith)
  nlinarith [mul_pos (show (0 : ℝ) < 1 - 2 * N by linarith) hEpos]

/-! #### The unit disc is a hyperbolic simply connected domain -/

theorem neh_isHyperbolicSimplyConnected_unitDisc : IsHyperbolicSimplyConnected unitDisc := by
  refine ⟨isOpen_ball, ⟨⟨0, mem_ball_self one_pos⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩, ?_, ?_⟩
  · haveI : ContractibleSpace ↥unitDisc :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
    exact SimplyConnectedSpace.ofContractible _
  · intro h
    have h2 : (2 : ℂ) ∈ unitDisc := h ▸ mem_univ _
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_ofNat] at h2
    norm_num at h2

/-! #### Isolated zeros and the germ of `f` at every point -/

theorem neh_eventually_ne_zero {w : ℂ → ℂ} {z : ℂ} (hw : AnalyticAt ℂ w z)
    (h : w z ≠ 0 ∨ deriv w z ≠ 0) : ∀ᶠ y in 𝓝[≠] z, w y ≠ 0 := by
  rcases h with h | h
  · exact (hw.continuousAt.eventually_ne h).filter_mono nhdsWithin_le_nhds
  · refine hw.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => h ?_
    have hz0 : w =ᶠ[𝓝 z] fun _ => (0 : ℂ) := hcon
    rw [hz0.deriv_eq, deriv_const]

theorem neh_eventually_eventuallyEq_nhds {f F : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝[≠] z] F) :
    ∀ᶠ y in 𝓝[≠] z, f =ᶠ[𝓝 y] F := by
  have h' := (eventually_nhdsWithin_iff.1 h).eventually_nhds
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h'] with y hy hyz
  filter_upwards [hy, eventually_ne_nhds hyz] with v hv hvz
  exact hv hvz

/-- A locally univalent meromorphic function is analytic on a punctured neighbourhood of every
point (its poles are simple, hence isolated). -/
theorem neh_eventually_analyticAt {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLocUnivMero f D) {z : ℂ}
    (hz : z ∈ D) : ∀ᶠ y in 𝓝[≠] z, AnalyticAt ℂ f y := by
  rcases hf.2 z hz with ⟨hA, -⟩ | ⟨-, hu, hu'⟩
  · exact hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  · have hfu : f =ᶠ[𝓝[≠] z] fun w => ((fun w => (toMeromorphicNFAt f z w)⁻¹) w)⁻¹ := by
      filter_upwards [(hf.1 z hz).eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [inv_inv]
      exact hw
    have hune := neh_eventually_ne_zero hu (Or.inr hu')
    have hua : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ (fun w => (toMeromorphicNFAt f z w)⁻¹) w :=
      hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
    filter_upwards [neh_eventually_eventuallyEq_nhds hfu, hune, hua] with w hw hne hA
    exact (hA.inv hne).congr hw.symm

/-- The Wronskian of `W₁ = a w₁ + b w₂`, `W₂ = c w₁ + d w₂` is `ad - bc`. -/
theorem neh_wronskian_comb {w₁ w₂ : ℂ → ℂ} {z a b c d : ℂ}
    (hw : w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) :
    (a * w₁ z + b * w₂ z) * (c * deriv w₁ z + d * deriv w₂ z) -
      (c * w₁ z + d * w₂ z) * (a * deriv w₁ z + b * deriv w₂ z) = a * d - b * c := by
  linear_combination (a * d - b * c) * hw

/-- With `f = M ∘ (w₁/w₂)` at the good points (Theorem 19.1, uniqueness), `f` agrees with
`W₁/W₂ = (a w₁ + b w₂)/(c w₁ + d w₂)` on a punctured neighbourhood of every point, and `W₂` does
not vanish there. -/
theorem neh_germ {f w₁ w₂ : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hw₁ : DifferentiableOn ℂ w₁ unitDisc) (hw₂ : DifferentiableOn ℂ w₂ unitDisc)
    (hwr : ∀ z ∈ unitDisc, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hrel : ∀ z ∈ unitDisc, AnalyticAt ℂ f z → AnalyticAt ℂ (fun z => w₁ z / w₂ z) z →
      c * (w₁ z / w₂ z) + d ≠ 0 → f z = (a * (w₁ z / w₂ z) + b) / (c * (w₁ z / w₂ z) + d))
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∀ᶠ y in 𝓝[≠] z, c * w₁ y + d * w₂ y ≠ 0) ∧
      f =ᶠ[𝓝[≠] z] fun y => (a * w₁ y + b * w₂ y) / (c * w₁ y + d * w₂ y) := by
  have hDo : IsOpen unitDisc := isOpen_ball
  have hw₁a : ∀ y ∈ unitDisc, AnalyticAt ℂ w₁ y := fun y hy => hw₁.analyticAt (hDo.mem_nhds hy)
  have hw₂a : ∀ y ∈ unitDisc, AnalyticAt ℂ w₂ y := fun y hy => hw₂.analyticAt (hDo.mem_nhds hy)
  have hW₂a : AnalyticAt ℂ (fun y => c * w₁ y + d * w₂ y) z :=
    (analyticAt_const.mul (hw₁a z hz)).add (analyticAt_const.mul (hw₂a z hz))
  have hW₂' : deriv (fun y => c * w₁ y + d * w₂ y) z = c * deriv w₁ z + d * deriv w₂ z :=
    (((hw₁a z hz).differentiableAt.hasDerivAt.const_mul c).add
      ((hw₂a z hz).differentiableAt.hasDerivAt.const_mul d)).deriv
  have hW₂ne : ∀ᶠ y in 𝓝[≠] z, c * w₁ y + d * w₂ y ≠ 0 := by
    apply neh_eventually_ne_zero hW₂a
    by_cases h0 : c * w₁ z + d * w₂ z = 0
    · right
      rw [hW₂']
      intro h1
      have hw := neh_wronskian_comb (a := a) (b := b) (c := c) (d := d) (hwr z hz)
      apply hdet
      rw [← hw, h0, h1]
      ring
    · exact Or.inl h0
  have hw₂ne : ∀ᶠ y in 𝓝[≠] z, w₂ y ≠ 0 := by
    apply neh_eventually_ne_zero (hw₂a z hz)
    by_cases h0 : w₂ z = 0
    · right
      intro h1
      have hw := hwr z hz
      rw [h0, h1] at hw
      simp at hw
    · exact Or.inl h0
  have hmem : ∀ᶠ y in 𝓝[≠] z, y ∈ unitDisc := (hDo.eventually_mem hz).filter_mono nhdsWithin_le_nhds
  refine ⟨hW₂ne, ?_⟩
  filter_upwards [hmem, neh_eventually_analyticAt hf hz, hw₂ne, hW₂ne] with y hy hfy hw₂y hW₂y
  have hgy : AnalyticAt ℂ (fun z => w₁ z / w₂ z) y := (hw₁a y hy).div (hw₂a y hy) hw₂y
  have hden : c * (w₁ y / w₂ y) + d ≠ 0 := by
    have e : c * (w₁ y / w₂ y) + d = (c * w₁ y + d * w₂ y) / w₂ y := by
      field_simp
    rw [e]
    exact div_ne_zero hW₂y hw₂y
  rw [hrel y hy hfy hgy hden]
  field_simp

/-- At an analytic point `z` of `f`: `W₂ z ≠ 0` and `f z · W₂ z = W₁ z`. -/
theorem neh_dict_analytic {f W₁ W₂ : ℂ → ℂ} {z : ℂ} (hW₁ : AnalyticAt ℂ W₁ z)
    (hW₂ : AnalyticAt ℂ W₂ z) (hne : W₂ z = 0 → W₁ z ≠ 0) (hW₂ne : ∀ᶠ y in 𝓝[≠] z, W₂ y ≠ 0)
    (hgerm : f =ᶠ[𝓝[≠] z] fun y => W₁ y / W₂ y) (hA : AnalyticAt ℂ f z) :
    W₂ z ≠ 0 ∧ f z * W₂ z = W₁ z := by
  have h1 : Tendsto (fun y => f y * W₂ y) (𝓝[≠] z) (𝓝 (f z * W₂ z)) :=
    (hA.continuousAt.mul hW₂.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun y => f y * W₂ y) (𝓝[≠] z) (𝓝 (W₁ z)) := by
    refine (hW₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hgerm, hW₂ne] with y hy hy2
    rw [hy, div_mul_cancel₀ _ hy2]
  have heq : f z * W₂ z = W₁ z := tendsto_nhds_unique h1 h2
  refine ⟨fun h0 => hne h0 ?_, heq⟩
  rw [← heq, h0, mul_zero]

/-- At a pole `z` of `f`: `W₂ z = 0`. -/
theorem neh_dict_pole {f W₁ W₂ : ℂ → ℂ} {D : Set ℂ} (hf : IsLocUnivMero f D) {z : ℂ}
    (hz : z ∈ D) (hW₁ : AnalyticAt ℂ W₁ z) (hW₂ : AnalyticAt ℂ W₂ z)
    (hgerm : f =ᶠ[𝓝[≠] z] fun y => W₁ y / W₂ y) (hA : ¬ AnalyticAt ℂ f z) : W₂ z = 0 := by
  by_contra h0
  rcases hf.2 z hz with ⟨hA', -⟩ | ⟨hord, -, -⟩
  · exact hA hA'
  · rw [meromorphicOrderAt_congr hgerm] at hord
    exact absurd hord (not_lt.2 (hW₁.div hW₂ h0).meromorphicOrderAt_nonneg)

/-! #### The Schwarzian norm bound and the Möbius normalisation -/

theorem neh_schwarzian_bound {f : ℂ → ℂ}
    (hS : schwarzianNorm f unitDisc < ENNReal.ofReal (1 / 2)) :
    ∃ N : ℝ, N < 1 / 2 ∧ ∀ ζ ∈ unitDisc, ‖schwarzian f ζ‖ ≤ 4 * N / (1 - ‖ζ‖ ^ 2) ^ 2 := by
  refine ⟨(schwarzianNorm f unitDisc).toReal, ENNReal.toReal_lt_of_lt_ofReal hS, fun ζ hζ => ?_⟩
  have hfin : schwarzianNorm f unitDisc ≠ ⊤ := hS.ne_top
  have hle : ENNReal.ofReal (‖schwarzian f ζ‖ / poincareDensity unitDisc ζ ^ 2) ≤
      schwarzianNorm f unitDisc := by
    unfold schwarzianNorm
    exact le_iSup₂ (f := fun z (_ : z ∈ unitDisc) =>
      ENNReal.ofReal (‖schwarzian f z‖ / poincareDensity unitDisc z ^ 2)) ζ hζ
  rw [ENNReal.ofReal_le_iff_le_toReal hfin] at hle
  have hn : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hpos : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  rw [poincareDensity_unitDisc hζ, poincareDensityDisc, div_pow, div_div_eq_mul_div,
    div_le_iff₀ (by norm_num)] at hle
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `φ(w) = c̄ M_a(w)` (a rotated Blaschke factor) and its derivative `φ'`. -/
def nehPhi (c a w : ℂ) : ℂ := conj c * blaschke a w

/-- See `nehPhi`. -/
def nehPhi' (c a w : ℂ) : ℂ := conj c * ((1 - a * conj a) / (1 - conj a * w) ^ 2)

theorem neh_phi_mem {c a w : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    nehPhi c a w ∈ unitDisc := by
  rw [unitDisc, mem_ball_zero_iff, nehPhi, norm_mul, Complex.norm_conj, hc, one_mul]
  exact blaschke_mem_unitDisc ha hw

theorem neh_hasDerivAt_phi {c a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    HasDerivAt (nehPhi c a) (nehPhi' c a w) w :=
  (hasDerivAt_blaschke ha hw).const_mul (conj c)

theorem neh_hasDerivAt_s (a w : ℂ) : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) w := by
  simpa using ((hasDerivAt_id w).const_mul (conj a)).const_sub (1 : ℂ)

theorem neh_hasDerivAt_phi' {c a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    HasDerivAt (nehPhi' c a)
      (2 * conj c * (1 - a * conj a) * conj a / (1 - conj a * w) ^ 3) w := by
  have hden := blaschke_den_ne_zero ha hw
  have := ((hasDerivAt_const w (1 - a * conj a)).div ((neh_hasDerivAt_s a w).pow 2)
    (pow_ne_zero 2 hden)).const_mul (conj c)
  convert this using 1
  · rfl
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- `(1 - |φ w|²) = |φ'(w)| (1 - |w|²)`: invariance of the Poincaré density. -/
theorem neh_norm_phi' {c a w : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖nehPhi' c a w‖ = (1 - ‖nehPhi c a w‖ ^ 2) / (1 - ‖w‖ ^ 2) := by
  have hc' : ‖conj c‖ = 1 := by rw [Complex.norm_conj, hc]
  have h := poincareDensityDisc_rotBlaschke hc' ha hw
  have hd : deriv (fun w => conj c * blaschke a w) w = nehPhi' c a w :=
    ((hasDerivAt_blaschke ha hw).const_mul (conj c)).deriv
  rw [hd, poincareDensityDisc, poincareDensityDisc] at h
  change 2 / (1 - ‖nehPhi c a w‖ ^ 2) * ‖nehPhi' c a w‖ = 2 / (1 - ‖w‖ ^ 2) at h
  have h1 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h2 : 0 < 1 - ‖nehPhi c a w‖ ^ 2 := by
    have := mem_ball_zero_iff.1 (neh_phi_mem hc ha hw)
    nlinarith [norm_nonneg (nehPhi c a w)]
  rw [eq_div_iff h1.ne']
  field_simp at h
  linarith

/-- The transported solution `v(w) = W(φ w) (1 - ā w)`: first derivative. -/
theorem neh_hasDerivAt_v {W W' : ℂ → ℂ} (hW : ∀ ζ ∈ unitDisc, HasDerivAt W (W' ζ) ζ)
    {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun w => W (nehPhi c a w) * (1 - conj a * w))
      (W' (nehPhi c a w) * nehPhi' c a w * (1 - conj a * w) + W (nehPhi c a w) * -conj a) w :=
  ((hW _ (neh_phi_mem hc ha hw)).comp w (neh_hasDerivAt_phi ha hw)).mul (neh_hasDerivAt_s a w)

/-- The transported solution satisfies `v'' = -(ψ/2) v` with `ψ = (Φ ∘ φ) φ'²`: the factor
`(φ')^{-1/2}` of a Möbius map is affine, so the transformed equation has no first-order term. -/
theorem neh_hasDerivAt_v' {W W' Φ : ℂ → ℂ} (hW : ∀ ζ ∈ unitDisc, HasDerivAt W (W' ζ) ζ)
    (hW' : ∀ ζ ∈ unitDisc, HasDerivAt W' (-(Φ ζ / 2) * W ζ) ζ) {c a : ℂ} (hc : ‖c‖ = 1)
    (ha : ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun w => W' (nehPhi c a w) * nehPhi' c a w * (1 - conj a * w) +
        W (nehPhi c a w) * -conj a)
      (-(Φ (nehPhi c a w) * nehPhi' c a w ^ 2 / 2) * (W (nehPhi c a w) * (1 - conj a * w))) w := by
  have hφw := neh_phi_mem hc ha hw
  have hden := blaschke_den_ne_zero ha hw
  have hφ := neh_hasDerivAt_phi (c := c) ha hw
  have hφ' := neh_hasDerivAt_phi' (c := c) ha hw
  have h1 := (((hW' _ hφw).comp w hφ).mul hφ').mul (neh_hasDerivAt_s a w)
  have h2 := ((hW _ hφw).comp w hφ).mul_const (-conj a)
  convert h1.add h2 using 1
  · funext y
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  simp only [Pi.mul_apply, Function.comp_apply, nehPhi']
  field_simp
  ring

/-- **Nehari's argument in the disc.**  A non-trivial combination `W = p w₁ + q w₂` of the
fundamental solutions of `w'' + (S_f/2) w = 0` (Wronskian `1`) cannot vanish at two distinct
points when `‖S_f‖_Δ < 1/2`: after a disc automorphism the two zeros lie on a diameter and
`neh_core` applies to the transported solution. -/
theorem neh_no_double_zero {f w₁ w₂ : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : schwarzianNorm f unitDisc < ENNReal.ofReal (1 / 2))
    (hw₁ : DifferentiableOn ℂ w₁ unitDisc) (hw₂ : DifferentiableOn ℂ w₂ unitDisc)
    (hode : ∀ z ∈ unitDisc, deriv (deriv w₁) z + schwarzian f z / 2 * w₁ z = 0 ∧
      deriv (deriv w₂) z + schwarzian f z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    {p q : ℂ} (hpq : ¬ (p = 0 ∧ q = 0)) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc)
    (hne : z₁ ≠ z₂) (h₁ : p * w₁ z₁ + q * w₂ z₁ = 0) (h₂ : p * w₁ z₂ + q * w₂ z₂ = 0) : False := by
  have hDo : IsOpen unitDisc := isOpen_ball
  have hΦ : DifferentiableOn ℂ (schwarzian f) unitDisc := schwarzian_holomorphic hDo hf
  have hw₁a : ∀ z ∈ unitDisc, AnalyticAt ℂ w₁ z := fun z hz => hw₁.analyticAt (hDo.mem_nhds hz)
  have hw₂a : ∀ z ∈ unitDisc, AnalyticAt ℂ w₂ z := fun z hz => hw₂.analyticAt (hDo.mem_nhds hz)
  -- the combination `W`, its derivative `W'`, and the equation `W'' = -(S_f/2) W`
  have hW : ∀ ζ ∈ unitDisc, HasDerivAt (fun z => p * w₁ z + q * w₂ z)
      (p * deriv w₁ ζ + q * deriv w₂ ζ) ζ := fun ζ hζ =>
    ((hw₁a ζ hζ).differentiableAt.hasDerivAt.const_mul p).add
      ((hw₂a ζ hζ).differentiableAt.hasDerivAt.const_mul q)
  have hW' : ∀ ζ ∈ unitDisc, HasDerivAt (fun z => p * deriv w₁ z + q * deriv w₂ z)
      (-(schwarzian f ζ / 2) * (p * w₁ ζ + q * w₂ ζ)) ζ := by
    intro ζ hζ
    have h1 := ((hw₁a ζ hζ).deriv.differentiableAt.hasDerivAt.const_mul p).add
      ((hw₂a ζ hζ).deriv.differentiableAt.hasDerivAt.const_mul q)
    convert h1 using 1
    obtain ⟨e1, e2, -⟩ := hode ζ hζ
    linear_combination (-p) * e1 + (-q) * e2
  -- non-triviality: `W'(z₁) ≠ 0`
  have hW'z₁ : p * deriv w₁ z₁ + q * deriv w₂ z₁ ≠ 0 := by
    intro h0
    obtain ⟨-, -, hwr⟩ := hode z₁ hz₁
    have hp : p = 0 := by linear_combination (deriv w₂ z₁) * h₁ - w₂ z₁ * h0 - p * hwr
    have hq : q = 0 := by linear_combination w₁ z₁ * h0 - deriv w₁ z₁ * h₁ - q * hwr
    exact hpq ⟨hp, hq⟩
  -- the bound on the Schwarzian
  obtain ⟨N, hN, hbound⟩ := neh_schwarzian_bound hS
  -- the disc automorphism `φ = c̄ M_a`, `a = -(c z₁)`, with `φ 0 = z₁`, `φ ρ = z₂`
  have ha1 : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
  have ha2 : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
  obtain ⟨c, hc, hcB⟩ := exists_rot_mul_eq_norm (blaschke z₁ z₂)
  set ρ : ℝ := ‖blaschke z₁ z₂‖ with hρdef
  have hρ1 : ρ < 1 := blaschke_mem_unitDisc ha1 ha2
  have hρ0 : 0 < ρ := by
    refine norm_pos_iff.2 ?_
    show (z₂ - z₁) / (1 - conj z₁ * z₂) ≠ 0
    exact div_ne_zero (sub_ne_zero.2 hne.symm) (blaschke_den_ne_zero ha1 ha2)
  set a : ℂ := -(c * z₁) with hadef
  have ha : ‖a‖ < 1 := by
    rw [hadef, norm_neg, norm_mul, hc, one_mul]
    exact ha1
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hcc : conj c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hφ0 : nehPhi c a 0 = z₁ := by
    simp only [nehPhi, hadef, blaschke, map_neg, map_mul, zero_sub, neg_neg, mul_zero, sub_zero,
      div_one]
    rw [← mul_assoc, hcc, one_mul]
  have hφρ : nehPhi c a ρ = z₂ := by
    rw [nehPhi, hadef, ← hcB, ← blaschke_neg_conj_mul hc, ← mul_assoc, hcc, one_mul,
      blaschke_neg_blaschke ha1 ha2]
  -- real points of `[0, ρ]` lie in the disc
  have hxn : ∀ x ∈ Icc (0 : ℝ) ρ, ‖(x : ℂ)‖ < 1 := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    linarith [hx.2]
  -- continuity of `ψ = (S_f ∘ φ) φ'²` on the disc
  have hφc : ContinuousOn (nehPhi c a) unitDisc := fun w hw =>
    (neh_hasDerivAt_phi ha (mem_ball_zero_iff.1 hw)).continuousAt.continuousWithinAt
  have hφ'c : ContinuousOn (nehPhi' c a) unitDisc := fun w hw =>
    (neh_hasDerivAt_phi' ha (mem_ball_zero_iff.1 hw)).continuousAt.continuousWithinAt
  have hφmaps : MapsTo (nehPhi c a) unitDisc unitDisc := fun w hw =>
    neh_phi_mem hc ha (mem_ball_zero_iff.1 hw)
  have hψc : ContinuousOn (fun w => schwarzian f (nehPhi c a w) * nehPhi' c a w ^ 2) unitDisc :=
    (hΦ.continuousOn.comp hφc hφmaps).mul (hφ'c.pow 2)
  -- Nehari's argument on the diameter, applied to the transported solution
  have key := neh_core (r := ρ) (N := N)
    (u := fun x : ℝ => (p * w₁ (nehPhi c a x) + q * w₂ (nehPhi c a x)) * (1 - conj a * x))
    (u' := fun x : ℝ => (p * deriv w₁ (nehPhi c a x) + q * deriv w₂ (nehPhi c a x)) *
      nehPhi' c a x * (1 - conj a * x) + (p * w₁ (nehPhi c a x) + q * w₂ (nehPhi c a x)) * -conj a)
    (u'' := fun x : ℝ => -((schwarzian f (nehPhi c a x) * nehPhi' c a x ^ 2) / 2) *
      ((p * w₁ (nehPhi c a x) + q * w₂ (nehPhi c a x)) * (1 - conj a * x)))
    (ψ := fun x : ℝ => schwarzian f (nehPhi c a x) * nehPhi' c a x ^ 2) hρ0 hρ1 hN
    (fun x hx => (neh_hasDerivAt_v hW hc ha (hxn x hx)).comp_ofReal)
    (fun x hx => (neh_hasDerivAt_v' hW hW' hc ha (hxn x hx)).comp_ofReal)
    (hψc.comp continuous_ofReal.continuousOn fun x hx => mem_ball_zero_iff.2 (hxn x hx))
    (fun x _ => rfl) ?_ ?_ ?_
  · -- `v'(0) = W'(z₁) φ'(0) = 0` forces `W'(z₁) = 0`
    simp only [Complex.ofReal_zero, hφ0, mul_zero, sub_zero, mul_one] at key
    have hW0 : p * w₁ z₁ + q * w₂ z₁ = 0 := h₁
    rw [hW0, zero_mul, add_zero] at key
    rcases mul_eq_zero.1 key with h | h
    · exact hW'z₁ h
    · simp only [nehPhi', mul_zero, sub_zero, one_pow, div_one] at h
      rcases mul_eq_zero.1 h with h | h
      · exact hc0 ((map_eq_zero _).1 h)
      · exact one_sub_mul_conj_ne_zero ha h
  · -- the bound `|ψ(x)| ≤ 4N/(1 - x²)²`
    intro x hx
    have hxn' := hxn x hx
    have hζ := neh_phi_mem hc ha hxn'
    have hζn : ‖nehPhi c a x‖ < 1 := mem_ball_zero_iff.1 hζ
    have h1 : 0 < 1 - ‖nehPhi c a x‖ ^ 2 := by nlinarith [norm_nonneg (nehPhi c a x)]
    have h2 : 0 < 1 - x ^ 2 := neh_one_sub_sq_pos hρ1 hx
    have hxsq : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hb : ‖schwarzian f (nehPhi c a x)‖ * (1 - ‖nehPhi c a x‖ ^ 2) ^ 2 ≤ 4 * N :=
      (le_div_iff₀ (by positivity)).1 (hbound _ hζ)
    show ‖schwarzian f (nehPhi c a x) * nehPhi' c a x ^ 2‖ ≤ 4 * N / (1 - x ^ 2) ^ 2
    rw [norm_mul, norm_pow, neh_norm_phi' hc ha hxn', hxsq, div_pow, le_div_iff₀ (by positivity)]
    calc ‖schwarzian f (nehPhi c a x)‖ * ((1 - ‖nehPhi c a x‖ ^ 2) ^ 2 / (1 - x ^ 2) ^ 2) *
          (1 - x ^ 2) ^ 2 = ‖schwarzian f (nehPhi c a x)‖ * (1 - ‖nehPhi c a x‖ ^ 2) ^ 2 := by
          field_simp
      _ ≤ 4 * N := hb
  · -- `v(0) = 0`
    simp only [Complex.ofReal_zero, hφ0, mul_zero, sub_zero, mul_one]
    exact h₁
  · -- `v(ρ) = 0`
    simp only [hφρ]
    have hW0 : p * w₁ z₂ + q * w₂ z₂ = 0 := h₂
    rw [hW0, zero_mul]

/-! #### The extremal functions `exp(c(t) h(z))`, `h(z) = log((1-z)/(1+z))`

The book takes `h = log((z-1)/(z+1))`; with the principal branch, `(z-1)/(z+1)` lies on the cut
for real `z ∈ (-1, 1)`, so `h(z) = log((1-z)/(1+z))` (the same function up to an additive
constant) is used instead: `(1-z)/(1+z)` has positive real part on `Δ`. -/

theorem neh_one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) + z ≠ 0 := fun hcon => by
  rw [show z = -1 by linear_combination hcon] at hz
  simp at hz

theorem neh_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) - z ≠ 0 := fun hcon => by
  rw [show z = 1 by linear_combination -hcon] at hz
  simp at hz

theorem neh_one_sub_sq_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) - z ^ 2 ≠ 0 := fun hcon => by
  rcases mul_eq_zero.mp (show ((1 : ℂ) - z) * (1 + z) = 0 by linear_combination hcon) with h | h
  · exact neh_one_sub_ne_zero hz h
  · exact neh_one_add_ne_zero hz h

/-- `(1 - z)/(1 + z)` has positive real part for `|z| < 1`. -/
theorem neh_q_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : (1 - z) / (1 + z) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have hpos : 0 < normSq (1 + z) := normSq_pos.2 (neh_one_add_ne_zero hz)
  have hz' : normSq z < 1 := normSq_lt_one_iff.mpr hz
  have e : ((1 - z) / (1 + z)).re = (1 - normSq z) / normSq (1 + z) := by
    rw [Complex.div_re, ← add_div]
    congr 1
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
      Complex.add_im, zero_sub, zero_add, normSq_apply]
    ring
  rw [e]
  exact div_pos (by linarith) hpos

/-- `h(z) = log((1 - z)/(1 + z))`. -/
def nehH (z : ℂ) : ℂ := Complex.log ((1 - z) / (1 + z))

/-- `c(t) = πi / log((1 - t)/(1 + t))`, so that `c(t) (h(t) - h(-t)) = 2πi`. -/
def nehC (t : ℝ) : ℂ := (π : ℂ) * I / (Real.log ((1 - t) / (1 + t)) : ℂ)

/-- `f_t(z) = exp(c(t) h(z))`. -/
def nehF (t : ℝ) (z : ℂ) : ℂ := Complex.exp (nehC t * nehH z)

theorem neh_log_neg {t : ℝ} (ht : 0 < t ∧ t < 1) : Real.log ((1 - t) / (1 + t)) < 0 :=
  Real.log_neg (div_pos (by linarith [ht.2]) (by linarith [ht.1]))
    ((div_lt_one (by linarith [ht.1])).2 (by linarith [ht.1]))

theorem neh_C_ne_zero {t : ℝ} (ht : 0 < t ∧ t < 1) : nehC t ≠ 0 :=
  div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero)
    (Complex.ofReal_ne_zero.2 (neh_log_neg ht).ne)

theorem neh_hasDerivAt_q {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun z : ℂ => (1 - z) / (1 + z)) (-2 / (1 + z) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id' z).const_sub 1
  have h2 : HasDerivAt (fun w : ℂ => 1 + w) 1 z := (hasDerivAt_id' z).const_add 1
  have hne := neh_one_add_ne_zero hz
  convert h1.div h2 hne using 1
  field_simp
  ring

theorem neh_hasDerivAt_h {z : ℂ} (hz : ‖z‖ < 1) : HasDerivAt nehH (-2 / (1 - z ^ 2)) z := by
  have h := (neh_hasDerivAt_q hz).clog (neh_q_mem_slitPlane hz)
  have h1 := neh_one_add_ne_zero hz
  have h2 := neh_one_sub_ne_zero hz
  have h3 := neh_one_sub_sq_ne_zero hz
  convert h using 1
  · rfl
  field_simp
  ring

theorem neh_analyticAt_f (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (nehF t) z := by
  have hq : AnalyticAt ℂ (fun z : ℂ => (1 - z) / (1 + z)) z :=
    (analyticAt_const.sub analyticAt_id).div (analyticAt_const.add analyticAt_id)
      (neh_one_add_ne_zero hz)
  exact (analyticAt_const.mul (hq.clog (neh_q_mem_slitPlane hz))).cexp'

theorem neh_hasDerivAt_f (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (nehF t) (nehF t z * (nehC t * (-2 / (1 - z ^ 2)))) z :=
  ((neh_hasDerivAt_h hz).const_mul (nehC t)).cexp

theorem neh_hasDerivAt_f' (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun z => nehF t z * (nehC t * (-2 / (1 - z ^ 2))))
      (nehF t z * (nehC t * (-2 / (1 - z ^ 2))) * (nehC t * (-2 / (1 - z ^ 2))) +
        nehF t z * (nehC t * (-4 * z / (1 - z ^ 2) ^ 2))) z := by
  have h3 := neh_one_sub_sq_ne_zero hz
  have hd : HasDerivAt (fun w : ℂ => nehC t * (-2 / (1 - w ^ 2)))
      (nehC t * (-4 * z / (1 - z ^ 2) ^ 2)) z := by
    have h2 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_sub (1 : ℂ)
    have := ((hasDerivAt_const z (-2 : ℂ)).div h2 h3).const_mul (nehC t)
    convert this using 1
    field_simp
    ring
  exact (neh_hasDerivAt_f t hz).mul hd

theorem neh_hasDerivAt_logDeriv (C : ℂ) {z : ℂ} (hz : (1 : ℂ) - z ^ 2 ≠ 0) :
    HasDerivAt (fun w : ℂ => (2 * w - 2 * C) / (1 - w ^ 2))
      ((2 + 2 * z ^ 2 - 4 * C * z) / (1 - z ^ 2) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * w - 2 * C) 2 z := by
    simpa using ((hasDerivAt_id' z).const_mul (2 : ℂ)).sub_const (2 * C)
  have h2 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * z)) z := by
    simpa using (hasDerivAt_pow 2 z).const_sub (1 : ℂ)
  convert h1.div h2 hz using 1
  field_simp
  ring

/-- `S_{f_t}(z) = 2(1 - c(t)²)/(1 - z²)²` (the book writes `2(c² - 1)/(z² - 1)²`; the sign of the
constant is immaterial for the norm). -/
theorem neh_schwarzian_f {t : ℝ} (ht : 0 < t ∧ t < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    schwarzian (nehF t) z = 2 * (1 - nehC t ^ 2) / (1 - z ^ 2) ^ 2 := by
  have hC := neh_C_ne_zero ht
  have hnear : ∀ᶠ w in 𝓝 z, ‖w‖ < 1 := by
    filter_upwards [isOpen_ball.eventually_mem (mem_ball_zero_iff.2 hz)] with w hw
    exact mem_ball_zero_iff.mp hw
  have hd1 : deriv (nehF t) =ᶠ[𝓝 z] fun w => nehF t w * (nehC t * (-2 / (1 - w ^ 2))) := by
    filter_upwards [hnear] with w hw
    exact (neh_hasDerivAt_f t hw).deriv
  have hd2 : deriv (deriv (nehF t)) =ᶠ[𝓝 z] fun w =>
      nehF t w * (nehC t * (-2 / (1 - w ^ 2))) * (nehC t * (-2 / (1 - w ^ 2))) +
        nehF t w * (nehC t * (-4 * w / (1 - w ^ 2) ^ 2)) := by
    filter_upwards [hnear, hd1.eventually_nhds] with w hw hev
    have hev' : deriv (nehF t) =ᶠ[𝓝 w] fun v => nehF t v * (nehC t * (-2 / (1 - v ^ 2))) := hev
    rw [hev'.deriv_eq]
    exact (neh_hasDerivAt_f' t hw).deriv
  -- the logarithmic derivative `f''/f' = (2w - 2c)/(1 - w²)`
  have hq : (fun w => deriv (deriv (nehF t)) w / deriv (nehF t) w) =ᶠ[𝓝 z]
      fun w => (2 * w - 2 * nehC t) / (1 - w ^ 2) := by
    filter_upwards [hnear, hd1, hd2] with w hw e1 e2
    rw [e1, e2]
    have h3 := neh_one_sub_sq_ne_zero hw
    have hf0 : nehF t w ≠ 0 := Complex.exp_ne_zero _
    field_simp
    ring
  have hqz : deriv (deriv (nehF t)) z / deriv (nehF t) z =
      (2 * z - 2 * nehC t) / (1 - z ^ 2) := hq.self_of_nhds
  have h3 := neh_one_sub_sq_ne_zero hz
  rw [schwarzian_of_analyticAt (neh_analyticAt_f t hz)]
  unfold schwarzianHol
  rw [hq.deriv_eq, (neh_hasDerivAt_logDeriv (nehC t) h3).deriv, hqz]
  field_simp
  ring

theorem neh_isLocUnivMero_f {t : ℝ} (ht : 0 < t ∧ t < 1) : IsLocUnivMero (nehF t) unitDisc := by
  refine ⟨fun z hz => (neh_analyticAt_f t (mem_ball_zero_iff.mp hz)).meromorphicAt,
    fun z hz => Or.inl ⟨neh_analyticAt_f t (mem_ball_zero_iff.mp hz), ?_⟩⟩
  have hz := mem_ball_zero_iff.mp hz
  rw [(neh_hasDerivAt_f t hz).deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero (neh_C_ne_zero ht) (div_ne_zero (by norm_num) (neh_one_sub_sq_ne_zero hz)))

theorem neh_H_ofReal {x : ℝ} (hx : |x| < 1) :
    nehH x = (Real.log ((1 - x) / (1 + x)) : ℂ) := by
  have h1 : 0 < 1 - x := by linarith [(abs_lt.1 hx).2]
  have h2 : 0 < 1 + x := by linarith [(abs_lt.1 hx).1]
  rw [nehH, Complex.ofReal_log (div_pos h1 h2).le]
  push_cast
  rfl

/-- `f_t(t) = f_t(-t) = -1`: `f_t` is not injective. -/
theorem neh_f_t_eq {t : ℝ} (ht : 0 < t ∧ t < 1) : nehF t t = nehF t (-(t : ℂ)) := by
  have hℓ0 : (Real.log ((1 - t) / (1 + t)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (neh_log_neg ht).ne
  have ht' : |t| < 1 := by rw [abs_of_pos ht.1]; exact ht.2
  have hmt : |(-t)| < 1 := by rw [abs_neg]; exact ht'
  have e1 : nehC t * nehH t = π * I := by
    rw [neh_H_ofReal ht', nehC, div_mul_cancel₀ _ hℓ0]
  have hH' := neh_H_ofReal hmt
  rw [Complex.ofReal_neg, sub_neg_eq_add, ← sub_eq_add_neg, ← inv_div, Real.log_inv] at hH'
  have e2 : nehC t * nehH (-(t : ℂ)) = -(π * I) := by
    rw [hH', Complex.ofReal_neg, mul_neg, nehC, div_mul_cancel₀ _ hℓ0]
  rw [nehF, nehF, e1, e2, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `‖S_{f_t}‖_Δ ≤ ½ (1 + π²/log²((1-t)/(1+t)))`. -/
theorem neh_schwarzianNorm_le {t : ℝ} (ht : 0 < t ∧ t < 1) :
    schwarzianNorm (nehF t) unitDisc ≤
      ENNReal.ofReal (1 / 2 * (1 + π ^ 2 / Real.log ((1 - t) / (1 + t)) ^ 2)) := by
  refine iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hη : poincareDensity unitDisc z ^ 2 = 4 / (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [poincareDensity_unitDisc hz, poincareDensityDisc, div_pow]
    norm_num
  set ℓ := Real.log ((1 - t) / (1 + t)) with hℓ
  have hℓ0 : ℓ ≠ 0 := (neh_log_neg ht).ne
  have hC2 : nehC t ^ 2 = -((π ^ 2 / ℓ ^ 2 : ℝ) : ℂ) := by
    rw [nehC, div_pow, mul_pow, Complex.I_sq]
    push_cast
    ring
  have h1x : ‖(1 : ℂ) - -((π ^ 2 / ℓ ^ 2 : ℝ) : ℂ)‖ = 1 + π ^ 2 / ℓ ^ 2 := by
    rw [sub_neg_eq_add,
      show (1 : ℂ) + ((π ^ 2 / ℓ ^ 2 : ℝ) : ℂ) = ((1 + π ^ 2 / ℓ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hnormS : ‖schwarzian (nehF t) z‖ = 2 * (1 + π ^ 2 / ℓ ^ 2) / ‖1 - z ^ 2‖ ^ 2 := by
    rw [neh_schwarzian_f ht hz1, hC2, norm_div, norm_mul, norm_pow, Complex.norm_ofNat, h1x]
  have hle : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    rwa [norm_one, norm_pow] at this
  have hsq : (1 - ‖z‖ ^ 2) ^ 2 ≤ ‖1 - z ^ 2‖ ^ 2 := pow_le_pow_left₀ hpos.le hle 2
  have hn0 : 0 < ‖1 - z ^ 2‖ := lt_of_lt_of_le hpos hle
  have e : 2 * (1 + π ^ 2 / ℓ ^ 2) / ‖1 - z ^ 2‖ ^ 2 / (4 / (1 - ‖z‖ ^ 2) ^ 2) =
      1 / 2 * (1 + π ^ 2 / ℓ ^ 2) * ((1 - ‖z‖ ^ 2) ^ 2 / ‖1 - z ^ 2‖ ^ 2) := by
    field_simp
    ring
  rw [hnormS, hη, e]
  have hratio : (1 - ‖z‖ ^ 2) ^ 2 / ‖1 - z ^ 2‖ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hsq
  calc 1 / 2 * (1 + π ^ 2 / ℓ ^ 2) * ((1 - ‖z‖ ^ 2) ^ 2 / ‖1 - z ^ 2‖ ^ 2)
      ≤ 1 / 2 * (1 + π ^ 2 / ℓ ^ 2) * 1 := by gcongr
    _ = 1 / 2 * (1 + π ^ 2 / ℓ ^ 2) := mul_one _

/-- For `a > 1/2` there is `t ∈ (0, 1)` with `½ (1 + π²/log²((1-t)/(1+t))) < a`:
take `(1-t)/(1+t) = e^{-M}` with `M` large. -/
theorem neh_exists_t {a : ℝ} (ha : 1 / 2 < a) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 / 2 * (1 + π ^ 2 / Real.log ((1 - t) / (1 + t)) ^ 2) < a := by
  set s := 2 * a - 1 with hs
  have hs0 : 0 < s := by linarith
  set M := π / s + π + 1 with hM
  have hMpi : π < M := by
    have := div_pos Real.pi_pos hs0
    linarith
  have hM0 : 0 < M := by linarith [Real.pi_pos]
  have hMs : π < M * s := by
    have e : M * s = π + (π + 1) * s := by
      rw [hM, add_mul, add_mul, div_mul_cancel₀ _ hs0.ne']
      ring
    rw [e]
    nlinarith [Real.pi_pos]
  set e := Real.exp (-M) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := by
    have := Real.exp_lt_exp.2 (show -M < 0 by linarith)
    rwa [Real.exp_zero] at this
  refine ⟨(1 - e) / (1 + e), div_pos (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  have hq : (1 - (1 - e) / (1 + e)) / (1 + (1 - e) / (1 + e)) = e := by
    have : (1 : ℝ) + e ≠ 0 := by linarith
    field_simp
    ring
  rw [hq, he, Real.log_exp, neg_sq]
  have key : π ^ 2 < s * M ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hMs hM0, mul_lt_mul_of_pos_right hMpi Real.pi_pos]
  have : π ^ 2 / M ^ 2 < s := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- **Theorem 20.1** (part 1): the unit disc is a `1/2`-Schwarz domain. -/
theorem thm20_1_disc_isSchwarz : IsSchwarzDomain unitDisc (1 / 2) := by
  refine ⟨neh_isHyperbolicSimplyConnected_unitDisc, by norm_num, fun f hf hS => ?_⟩
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDc : IsConnected unitDisc := neh_isHyperbolicSimplyConnected_unitDisc.2.1
  have hDs : IsSimplyConnected unitDisc := neh_isHyperbolicSimplyConnected_unitDisc.2.2.1
  have hΦ : DifferentiableOn ℂ (schwarzian f) unitDisc := schwarzian_holomorphic hDo hf
  -- the fundamental system of `w'' + (S_f/2) w = 0` and the Möbius relation `f = M ∘ (w₁/w₂)`
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hg, hSg⟩ := eq19_2_ode hDo hDc hDs hΦ
  obtain ⟨a, b, c, d, hdet, hrel⟩ := thm19_1_unique hDo hDc hf hg fun z hz => (hSg z hz).symm
  have hrel' : ∀ z ∈ unitDisc, AnalyticAt ℂ f z → AnalyticAt ℂ (fun z => w₁ z / w₂ z) z →
      c * (w₁ z / w₂ z) + d ≠ 0 → f z = (a * (w₁ z / w₂ z) + b) / (c * (w₁ z / w₂ z) + d) := hrel
  have hwr : ∀ z ∈ unitDisc, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1 :=
    fun z hz => (hode z hz).2.2
  have hgerm := fun z (hz : z ∈ unitDisc) => neh_germ hf hw₁ hw₂ hwr hdet hrel' hz
  have hW₁a : ∀ z ∈ unitDisc, AnalyticAt ℂ (fun y => a * w₁ y + b * w₂ y) z := fun z hz =>
    (analyticAt_const.mul (hw₁.analyticAt (hDo.mem_nhds hz))).add
      (analyticAt_const.mul (hw₂.analyticAt (hDo.mem_nhds hz)))
  have hW₂a : ∀ z ∈ unitDisc, AnalyticAt ℂ (fun y => c * w₁ y + d * w₂ y) z := fun z hz =>
    (analyticAt_const.mul (hw₁.analyticAt (hDo.mem_nhds hz))).add
      (analyticAt_const.mul (hw₂.analyticAt (hDo.mem_nhds hz)))
  have hne : ∀ z ∈ unitDisc, c * w₁ z + d * w₂ z = 0 → a * w₁ z + b * w₂ z ≠ 0 := by
    intro z hz h0 h1
    have hw := neh_wronskian_comb (a := a) (b := b) (c := c) (d := d) (hwr z hz)
    apply hdet
    rw [← hw, h0, h1]
    ring
  refine ⟨hf, ?_, ?_⟩
  · -- injectivity at the analytic points: `W₁ - f(z₁) W₂` would vanish at `z₁` and `z₂`
    rintro z₁ ⟨hz₁, hA₁⟩ z₂ ⟨hz₂, hA₂⟩ heq
    by_contra hne12
    obtain ⟨-, e₁⟩ := neh_dict_analytic (hW₁a z₁ hz₁) (hW₂a z₁ hz₁) (hne z₁ hz₁)
      (hgerm z₁ hz₁).1 (hgerm z₁ hz₁).2 hA₁
    obtain ⟨-, e₂⟩ := neh_dict_analytic (hW₁a z₂ hz₂) (hW₂a z₂ hz₂) (hne z₂ hz₂)
      (hgerm z₂ hz₂).1 (hgerm z₂ hz₂).2 hA₂
    refine neh_no_double_zero hf hS hw₁ hw₂ hode (p := a - f z₁ * c) (q := b - f z₁ * d) ?_
      hz₁ hz₂ hne12 ?_ ?_
    · rintro ⟨hp, hq⟩
      apply hdet
      rw [sub_eq_zero.1 hp, sub_eq_zero.1 hq]
      ring
    · linear_combination -e₁
    · rw [heq]
      linear_combination -e₂
  · -- at most one pole: `W₂` would vanish at two poles
    rintro z₁ ⟨hz₁, hA₁⟩ z₂ ⟨hz₂, hA₂⟩
    by_contra hne12
    have h₁ := neh_dict_pole hf hz₁ (hW₁a z₁ hz₁) (hW₂a z₁ hz₁) (hgerm z₁ hz₁).2 hA₁
    have h₂ := neh_dict_pole hf hz₂ (hW₁a z₂ hz₂) (hW₂a z₂ hz₂) (hgerm z₂ hz₂).2 hA₂
    refine neh_no_double_zero hf hS hw₁ hw₂ hode (p := c) (q := d) ?_ hz₁ hz₂ hne12 h₁ h₂
    rintro ⟨rfl, rfl⟩
    simp at hdet

/-- **Theorem 20.1** (part 2): the functions `exp(c(t) ln((z-1)/(z+1)))`,
`c(t) = 2πi/(h(t) - h(-t))`, are not univalent in `Δ` and `‖S_f‖_Δ → 1/2` as `t → 1`; hence `Δ`
is not an `a`-Schwarz domain for any `a > 1/2`.

The proof uses `h(z) = log((1-z)/(1+z))` (the book's `h` up to an additive constant): with the
principal logarithm, `(z-1)/(z+1)` lies on the branch cut for real `z ∈ (-1, 1)`, whereas
`(1-z)/(1+z)` has positive real part on `Δ`.  Then `S_f = 2(1 - c²)/(1 - z²)²` and
`‖S_f‖_Δ ≤ ½(1 + π²/log²((1-t)/(1+t)))`, which is `< a` for `t` close to `1`. -/
theorem thm20_1_not_isSchwarz {a : ℝ} (ha : 1 / 2 < a) : ¬ IsSchwarzDomain unitDisc a := by
  rintro ⟨-, -, hall⟩
  obtain ⟨t, ht0, ht1, hB⟩ := neh_exists_t ha
  have ht : 0 < t ∧ t < 1 := ⟨ht0, ht1⟩
  have huniv := hall (nehF t) (neh_isLocUnivMero_f ht)
    (lt_of_le_of_lt (neh_schwarzianNorm_le ht) ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hB))
  have hmem : ∀ x : ℝ, |x| < 1 → (x : ℂ) ∈ {z ∈ unitDisc | AnalyticAt ℂ (nehF t) z} := by
    intro x hx
    have hx' : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
    exact ⟨mem_ball_zero_iff.2 hx', neh_analyticAt_f t hx'⟩
  have ht' : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  have hmt : |(-t)| < 1 := by rw [abs_neg]; exact ht'
  have h1 := hmem t ht'
  have h2 := hmem (-t) hmt
  rw [Complex.ofReal_neg] at h2
  have heq := huniv.2.1 h1 h2 (neh_f_t_eq ht)
  have : t = -t := by exact_mod_cast heq
  linarith

/-- **Theorem 20.1**: `σ₃(Δ) = 1/2`. -/
theorem thm20_1 : innerUnivalenceRadius unitDisc = 1 / 2 := by
  unfold innerUnivalenceRadius
  refine IsGreatest.csSup_eq ⟨thm20_1_disc_isSchwarz, fun a ha => ?_⟩
  by_contra h
  exact thm20_1_not_isSchwarz (not_le.1 h) ha

open scoped Classical in
/-- The `ℂ̄`-valued map of a meromorphic function (poles are sent to `∞`).

*Correction.*  This branched on `AnalyticAt ℂ f z`, which is the wrong test for "has a pole": a
Lean function may fail `AnalyticAt` at `z` merely because its value there is wrong (a removable
singularity), and such a germ was then sent to `∞`.  With `u w = w` and
`f = Function.update u 0 1`, the old definition gave `meroToExt f 0 = ∞` although `f` has no pole
at `0`.  The test is now the sign of `meromorphicOrderAt`, and the value is read off the normal
form, so the definition depends only on the germ of `f` at `z`.  It agrees with the old one on
every germ already in normal form, in particular on everything analytic at `z`. -/
def meroToExt (f : ℂ → ℂ) (z : ℂ) : ExtPlane :=
  if 0 ≤ meromorphicOrderAt f z then ((toMeromorphicNFAt f z z : ℂ) : ExtPlane) else extInf

/-- `f` (meromorphic in `D`) extends to a `K`-quasiconformal homeomorphism `F` of `ℂ̄`: after a
Möbius transformation `M`, `M ∘ F` is (the extension to `ℂ̄` of) a `K`-q.c. map of `ℂ` onto `ℂ`. -/
def HasQCExtensionExt (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  ∃ F : ExtPlane → ExtPlane, (∀ z ∈ D, F z = meroToExt f z) ∧
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ g : ℂ → ℂ, IsKQC g univ K ∧ g '' univ = univ ∧
      ∀ p, M (F p) = OnePoint.map g p

/-- **Theorem 20.2**: a locally univalent meromorphic `f` in `Δ` with `‖S_f‖_Δ < 1/2` extends to a
quasiconformal map of `ℂ̄`, with maximal dilatation at most
`(1 + ½‖S_f‖_Δ)/(1 - ½‖S_f‖_Δ)`. -/
theorem thm20_2 {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : schwarzianNorm f unitDisc < ENNReal.ofReal (1 / 2)) :
    HasQCExtensionExt f unitDisc
      ((1 + (schwarzianNorm f unitDisc).toReal / 2) / (1 - (schwarzianNorm f unitDisc).toReal / 2)) := by
  sorry

/-- A planar quasiconformal reflection `g : A₁ → A₂` across the common boundary of the plane
domains `A₁`, `A₂`: an injective map of `A₁` onto `A₂`, anti-quasiconformal (`conj ∘ g` is
`K`-q.c.) and tending to the identity at the common boundary. -/
def IsPlanarQCReflection (A₁ A₂ : Set ℂ) (g : ℂ → ℂ) (K : ℝ) : Prop :=
  InjOn g A₁ ∧ g '' A₁ = A₂ ∧ IsKQC (fun z => conj (g z)) A₁ K ∧
    ∀ p ∈ frontier A₁ ∩ frontier A₂, Tendsto g (𝓝[A₁] p) (𝓝 p)

/-! ### S20 lemma track interface (coordinator 553e2d): Lemmas 20.1–20.3

The first four declarations are proved (scout A's probes, renamed); the rest are stubs. -/

/-- A continuous bijection of `ℂ` is a homeomorphism onto `ℂ` (invariance of domain). -/
theorem s20l_homeo_of_bij {G : ℂ → ℂ} (hc : Continuous G) (hi : Function.Injective G)
    (hs : Function.Surjective G) : IsHomeomorphOnto G univ univ := by
  have hopen : IsOpenMap G := fun U hU =>
    isOpen_image_of_continuousOn_injOn hU hc.continuousOn hi.injOn
  set e : ℂ ≃ₜ ℂ := (Equiv.ofBijective G ⟨hi, hs⟩).toHomeomorphOfContinuousOpen hc hopen
  have hinv : ∀ w, Function.invFunOn G univ w = e.symm w := by
    intro w
    apply hi
    have h1 : G (Function.invFunOn G univ w) = w :=
      Function.invFunOn_eq (f := G) (s := univ) ⟨e.symm w, mem_univ _, e.apply_symm_apply w⟩
    rw [h1]
    exact (e.apply_symm_apply w).symm
  refine ⟨hc.continuousOn, hi.injOn, image_univ_of_surjective hs, ?_⟩
  have : Function.invFunOn G univ = e.symm := funext hinv
  rw [this]
  exact e.symm.continuous.continuousOn

/-- The circle-distortion core of Lemma 20.2 and of (20.16): for a `K₁`-q.c. map `G` of the plane with
`G (conj ζ) = g (G ζ)` on `ℍ`, both `|z - y| ≤ λ(K₁) |g z - y|` and `|g z - y| ≤ λ(K₁) |z - y|` hold for `z = G ζ`,
`y = G x` (`tp_a_circle` on the circle about `x` through `ζ` and `conj ζ`). -/
theorem s20l_circle_core {G g : ℂ → ℂ} {K₁ : ℝ} (hG : IsKQC G univ K₁) (hGs : G '' univ = univ)
    (hsym : ∀ ζ ∈ upperHalf, G (conj ζ) = g (G ζ)) {ζ : ℂ} (hζ : ζ ∈ upperHalf) (x : ℝ) :
    ‖G ζ - G x‖ ≤ lambdaInv K₁ * ‖g (G ζ) - G x‖ ∧
      ‖g (G ζ) - G x‖ ≤ lambdaInv K₁ * ‖G ζ - G x‖ := by
  have hζ' : 0 < ζ.im := hζ
  have hr : 0 < ‖ζ - x‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have := congrArg Complex.im h
    rw [ofReal_im] at this
    linarith
  have hconj : ‖conj ζ - x‖ = ‖ζ - x‖ := by
    rw [← Complex.norm_conj, map_sub, conj_conj, conj_ofReal]
  rw [← hsym ζ hζ]
  exact ⟨tp_a_circle hG hGs hr rfl hconj, tp_a_circle hG hGs hr hconj rfl⟩

/-- (20.13): the Poincaré density of `A` at `w` is at most `2/r` when `ball w r ⊆ A` (Schwarz lemma for
`blaschke (φ w) ∘ φ` on the ball). -/
theorem s20l_density_le {A : Set ℂ} (hA : IsOpen A) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ A unitDisc)
    {w : ℂ} (hw : w ∈ A) {r : ℝ} (hr : 0 < r) (hball : ball w r ⊆ A) :
    poincareDensity A w ≤ 2 / r := by
  rw [(poincareDensity_well_defined hA hφ hφ hw).2]
  have hin : ∀ z ∈ A, ‖φ z‖ < 1 := fun z hz =>
    mem_ball_zero_iff.1 (show φ z ∈ unitDisc from hφ.2.2 ▸ mem_image_of_mem φ hz)
  have ha := hin w hw
  have hφd : ∀ z ∈ A, DifferentiableAt ℂ φ z := fun z hz =>
    hφ.1.differentiableAt (hA.mem_nhds hz)
  have hmaps : MapsTo (fun z => blaschke (φ w) (φ z)) (ball w r)
      (closedBall ((fun z => blaschke (φ w) (φ z)) w) 1) := by
    intro z hz
    simp only [blaschke_self, mem_closedBall_zero_iff]
    exact (blaschke_mem_unitDisc ha (hin z (hball hz))).le
  have hd : DifferentiableOn ℂ (fun z => blaschke (φ w) (φ z)) (ball w r) := by
    intro z hz
    exact ((hasDerivAt_blaschke ha (hin z (hball hz))).differentiableAt.comp z
      (hφd z (hball hz))).differentiableWithinAt
  have hS := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps hr
  have hderiv : deriv (fun z => blaschke (φ w) (φ z)) w =
      (1 - φ w * conj (φ w)) / (1 - conj (φ w) * φ w) ^ 2 * deriv φ w :=
    ((hasDerivAt_blaschke ha ha).comp w (hφd w hw).hasDerivAt).deriv
  rw [hderiv] at hS
  have hn : (1 : ℂ) - φ w * conj (φ w) = ((1 - ‖φ w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hn' : (1 : ℂ) - conj (φ w) * φ w = ((1 - ‖φ w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, hn]
  have hpos : 0 < 1 - ‖φ w‖ ^ 2 := by nlinarith [norm_nonneg (φ w)]
  rw [hn, hn', norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le] at hS
  have hS' : ‖deriv φ w‖ / (1 - ‖φ w‖ ^ 2) ≤ 1 / r := by
    have : (1 - ‖φ w‖ ^ 2) / (1 - ‖φ w‖ ^ 2) ^ 2 * ‖deriv φ w‖ = ‖deriv φ w‖ / (1 - ‖φ w‖ ^ 2) := by
      field_simp
    linarith
  calc 2 * ‖deriv φ w‖ / (1 - ‖φ w‖ ^ 2) = 2 * (‖deriv φ w‖ / (1 - ‖φ w‖ ^ 2)) := by ring
    _ ≤ 2 * (1 / r) := by linarith
    _ = 2 / r := by ring

/-- A Jordan domain with `∞` on its boundary has a conformal map onto `ℍ` whose homeomorphic extension fixes `∞`
(`uq_exists_uniformizer`, normalized by a real Möbius map). -/
theorem s20l_uniformizer_inf {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) (hinf : extInf ∈ frontier (toExt Ω)) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ Ω upperHalf ∧
      ∃ Φ : ExtPlane → ExtPlane, IsHomeoExtension φ Ω upperHalf Φ ∧ Φ extInf = extInf := by
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := uq_exists_uniformizer hΩ
  have hHo : IsOpen (toExt upperHalf) := OnePoint.isOpen_image_coe.2 isOpen_upperHalf
  have hmemcl : extInf ∈ closure (toExt Ω) := frontier_subset_closure hinf
  have hΨfr : Ψ extInf ∈ frontier (toExt upperHalf) := by
    refine ⟨hΨ.2.2.2 ▸ mem_image_of_mem Ψ hmemcl, ?_⟩
    rw [hHo.interior_eq]
    rintro ⟨w, hw, hwe⟩
    have hw' : w ∈ ψ '' Ω := hψ.2.2.symm ▸ hw
    obtain ⟨z, hz, rfl⟩ := hw'
    have hzcl : ((z : ℂ) : ExtPlane) ∈ closure (toExt Ω) := subset_closure ⟨z, hz, rfl⟩
    have h1 : Ψ (z : ExtPlane) = Ψ extInf := by rw [hΨ.1 z hz, hwe]
    have h2 := hΨ.2.2.1 hzcl hmemcl h1
    exact OnePoint.coe_ne_infty z h2
  rcases uq_k_frontier_cases hΨfr with ⟨x₀, hx₀⟩ | hx₀
  · have hdet : (0 : ℝ) < 0 * (-x₀) - (-1) * 1 := by norm_num
    obtain ⟨hMc, hMe⟩ := uq_k_mobius_auto hdet
    refine ⟨mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-x₀ : ℝ) : ℂ) ∘ ψ,
      hMc.comp hψ, _, hMe.comp hΨ hψ.mapsTo, ?_⟩
    show mobiusExt _ _ _ _ (Ψ extInf) = extInf
    rw [hx₀]
    exact mobiusExt_coe_of_eq_zero (by push_cast; ring)
  · exact ⟨ψ, hψ, Ψ, hΨ, hx₀⟩

/-- The image of `ℍ` under a homeomorphism `e` of the plane is a Jordan domain with `∞` on its boundary (`e`
extended by `∞ ↦ ∞` carries `∂ℍ ∋ ∞` onto its boundary). -/
theorem s20l_uw_jordan_image (e : ℂ ≃ₜ ℂ) :
    IsJordanDomain (e '' upperHalf) ∧ extInf ∈ frontier (toExt (e '' upperHalf)) := by
  refine ⟨uq_isJordanDomain_image e.onePointCongr isJordanDomain_upperHalf (s13x_de_image_toExt e upperHalf), ?_⟩
  rw [← s13x_de_image_toExt, ← e.onePointCongr.image_frontier]
  exact ⟨extInf, infty_mem_frontier_upperHalf, rfl⟩

/-- **U** (uniformizers): for a quasicircle `C` through `∞` with complementary components `A₁, A₂` there are conformal
maps `φ : A₁ → ℍ` and `ψ : A₂ → 𝕃` whose homeomorphic extensions fix `∞` (`A₁ = g₀(ℍ)`, `A₂ = g₀(𝕃)` by
`wd_normal_form`, so both are Jordan domains with `∞` on the boundary; `ψ = -(uniformizer onto ℍ)`). -/
theorem s20l_uniformizers {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hq : IsQuasicircle C) :
    (∃ φ : ℂ → ℂ, IsConformalOnto φ A₁ upperHalf ∧ ∃ Φ : ExtPlane → ExtPlane,
        IsHomeoExtension φ A₁ upperHalf Φ ∧ Φ extInf = extInf) ∧
      ∃ ψ : ℂ → ℂ, IsConformalOnto ψ A₂ lowerHalf ∧ ∃ Ψ : ExtPlane → ExtPlane,
        IsHomeoExtension ψ A₂ lowerHalf Ψ ∧ Ψ extInf = extInf := by
  obtain ⟨g₀, K, hg₀, hg₀s, -, hA₁, hA₂⟩ := wd_normal_form hinf hC hq
  obtain ⟨e, rfl⟩ := t1_homeomorph hg₀ hg₀s
  have hnU : (Homeomorph.neg ℂ) '' upperHalf = lowerHalf :=
    wd_n_neg_image fun z => by
      show (-z).im < 0 ↔ 0 < z.im
      rw [neg_im, neg_lt_zero]
  have hL : ⇑e '' lowerHalf = ((Homeomorph.neg ℂ).trans e) '' upperHalf := by
    show ⇑e '' lowerHalf = (⇑e ∘ ⇑(Homeomorph.neg ℂ)) '' upperHalf
    rw [image_comp, hnU]
  obtain ⟨hJ₁, hi₁⟩ := s20l_uw_jordan_image e
  obtain ⟨hJ₂, hi₂⟩ := s20l_uw_jordan_image ((Homeomorph.neg ℂ).trans e)
  rw [← hA₁] at hJ₁ hi₁
  rw [← hL, ← hA₂] at hJ₂ hi₂
  refine ⟨s20l_uniformizer_inf hJ₁ hi₁, ?_⟩
  obtain ⟨ψ₀, hψ₀, Ψ₀, hΨ₀, hΨ₀inf⟩ := s20l_uniformizer_inf hJ₂ hi₂
  have hnc : IsConformalOnto (Homeomorph.neg ℂ) upperHalf lowerHalf :=
    ⟨(differentiable_id.neg : Differentiable ℂ fun z : ℂ => -z).differentiableOn,
      (Homeomorph.neg ℂ).injective.injOn, hnU⟩
  have hne : IsHomeoExtension (Homeomorph.neg ℂ) upperHalf lowerHalf (Homeomorph.neg ℂ).onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph (Homeomorph.neg ℂ) upperHalf
    rwa [hnU] at h1
  refine ⟨_, hnc.comp hψ₀, _, hne.comp hΨ₀ hψ₀.mapsTo, ?_⟩
  show (Homeomorph.neg ℂ).onePointCongr (Ψ₀ extInf) = extInf
  rw [hΨ₀inf]
  rfl

/-- For an open `A ⊆ ℂ`, a point of `ℂ` lies in the frontier of `A` iff it lies in the frontier of `A` in `ℂ̄`. -/
theorem s20l_g_mem_frontier_iff {A : Set ℂ} (hA : IsOpen A) (z : ℂ) :
    z ∈ frontier A ↔ (z : ExtPlane) ∈ frontier (toExt A) := by
  have hA' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hA
  have hcl : z ∈ closure A ↔ (z : ExtPlane) ∈ closure (toExt A) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image A]
    exact Iff.rfl
  rw [hA.frontier_eq, hA'.frontier_eq, Set.mem_sdiff, Set.mem_sdiff, hcl, wd_n_coe_mem_toExt]

/-- Extending `g` from an open set `A` by the identity on `∂A`: if `g` is continuous on `A` and tends to `p` at every
frontier point `p` of `A` (within `A`), a map agreeing with `g` on `A` and with the identity on `∂A` is continuous on
the closure of `A`. -/
theorem s20l_g_ext_cont {A : Set ℂ} {g g' : ℂ → ℂ} (hA : IsOpen A) (hgc : ContinuousOn g A)
    (hfr : ∀ p ∈ frontier A, Tendsto g (𝓝[A] p) (𝓝 p)) (hA' : EqOn g' g A) (hfr' : EqOn g' id (frontier A)) :
    ContinuousOn g' (closure A) := by
  intro p hp
  by_cases hpA : p ∈ A
  · have h1 : ContinuousAt g p := hgc.continuousAt (hA.mem_nhds hpA)
    have h2 : g =ᶠ[𝓝 p] g' := by
      filter_upwards [hA.mem_nhds hpA] with z hz
      exact (hA' hz).symm
    exact (h1.congr h2).continuousWithinAt
  · have hpfr : p ∈ frontier A := by
      rw [hA.frontier_eq]
      exact ⟨hp, hpA⟩
    have hp' : g' p = p := hfr' hpfr
    show Tendsto g' (𝓝[closure A] p) (𝓝 (g' p))
    rw [hp', closure_eq_self_union_frontier, nhdsWithin_union, tendsto_sup]
    refine ⟨(hfr p hpfr).congr' ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hA' hz).symm
    · refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hfr' hz).symm

/-- The boundary extension of `φ⁻¹` to the closed upper half-plane: for a conformal `φ : A → ℍ` with homeomorphic
extension `Φ` fixing `∞` and `∂A = C ∋ ∞`, `H = extToC ∘ Φ⁻¹` is continuous and injective on `Im ≥ 0`, equals `φ⁻¹` on
`ℍ` and maps `ℝ` onto `C ∩ ℂ`. -/
theorem s20l_g_half {C : Set ExtPlane} {A : Set ℂ} {φ : ℂ → ℂ} {Φ : ExtPlane → ExtPlane} (hA : IsOpen A)
    (hφ : IsConformalOnto φ A upperHalf) (hΦ : IsHomeoExtension φ A upperHalf Φ) (hΦinf : Φ extInf = extInf)
    (hfr : frontier (toExt A) = C) (hinf : extInf ∈ C) :
    ∃ H : ℂ → ℂ, ContinuousOn H {z : ℂ | 0 ≤ z.im} ∧ InjOn H {z : ℂ | 0 ≤ z.im} ∧
      EqOn H (Function.invFunOn φ A) upperHalf ∧ H '' realLine = {z : ℂ | (z : ExtPlane) ∈ C} := by
  obtain ⟨hΦic, hΦim, hΦr, hΦl⟩ := wd_b_inv isClosed_closure hΦ.2.1 hΦ.2.2.1 hΦ.2.2.2
  set Φi := Function.invFunOn Φ (closure (toExt A)) with hΦi
  have hAo : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hA
  -- the closed upper half-plane lies in the closure of `ℍ` in `ℂ̄`
  have hcu : ∀ z : ℂ, 0 ≤ z.im → (z : ExtPlane) ∈ closure (toExt upperHalf) := by
    intro z hz
    have h1 : z ∈ closure upperHalf := by
      rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
      exact hz
    exact image_closure_subset_closure_image OnePoint.continuous_coe ⟨z, h1, rfl⟩
  -- `Φ⁻¹` is finite there
  have hfin : ∀ z : ℂ, 0 ≤ z.im → ((extToC (Φi z) : ℂ) : ExtPlane) = Φi z := by
    intro z hz
    have hne : Φi z ≠ extInf := by
      intro h
      have h1 := hΦr _ (hcu z hz)
      rw [h, hΦinf] at h1
      exact OnePoint.coe_ne_infty z h1.symm
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.1 hne
    rw [← hw]
    rfl
  refine ⟨fun z => extToC (Φi z), ?_, ?_, ?_, ?_⟩
  · -- continuity
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuousOn_iff]
    refine ContinuousOn.congr (f := Φi ∘ ((↑) : ℂ → ExtPlane)) ?_ ?_
    · exact hΦic.comp OnePoint.continuous_coe.continuousOn fun z hz => hcu z hz
    · intro z hz
      exact hfin z hz
  · -- injectivity
    intro a ha b hb hab
    have h := congrArg ((↑) : ℂ → ExtPlane) hab
    have h' : Φi a = Φi b := by
      rw [← hfin a ha, ← hfin b hb]
      exact h
    have h2 := congrArg Φ h'
    rw [hΦr _ (hcu a ha), hΦr _ (hcu b hb)] at h2
    exact OnePoint.coe_injective h2
  · -- on `ℍ`
    intro z hz
    apply OnePoint.coe_injective
    show ((extToC (Φi z) : ℂ) : ExtPlane) = _
    rw [hfin z (le_of_lt hz)]
    exact (wd_b_invFunOn_coe hΦ hφ.2.2 hz).1
  · -- the real line goes onto `C ∩ ℂ`
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z.im = 0 := hz
      have hz0 : 0 ≤ z.im := hz'.symm.le
      show ((extToC (Φi z) : ℂ) : ExtPlane) ∈ C
      rw [hfin z hz0, ← hfr, hAo.frontier_eq]
      refine ⟨hΦim (hcu z hz0), ?_⟩
      rintro ⟨u, hu, hue⟩
      have h1 := hΦr _ (hcu z hz0)
      rw [← hue, hΦ.1 u hu] at h1
      have h2 : φ u ∈ upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hu
      have h3 : 0 < (φ u).im := h2
      rw [OnePoint.coe_injective h1, hz'] at h3
      exact lt_irrefl 0 h3
    · intro hw
      have hw' : (w : ExtPlane) ∈ C := hw
      have hwcl : (w : ExtPlane) ∈ closure (toExt A) := by
        rw [← hfr] at hw'
        exact frontier_subset_closure hw'
      have hwA : (w : ExtPlane) ∉ toExt A := by
        rw [← hfr, hAo.frontier_eq] at hw'
        exact hw'.2
      have hinfcl : extInf ∈ closure (toExt A) := by
        rw [← hfr] at hinf
        exact frontier_subset_closure hinf
      have hΦw : Φ w ∈ closure (toExt upperHalf) := hΦ.2.2.2 ▸ mem_image_of_mem Φ hwcl
      rcases wd_b_closure_upper_cases hΦw with h | ⟨x, hx⟩ | ⟨v, hv, hve⟩
      · rw [← hΦinf] at h
        exact absurd (hΦ.2.2.1 hwcl hinfcl h) (OnePoint.coe_ne_infty w)
      · refine ⟨x, Complex.ofReal_im x, ?_⟩
        apply OnePoint.coe_injective
        show ((extToC (Φi ((x : ℂ) : ExtPlane)) : ℂ) : ExtPlane) = w
        rw [hfin _ (by rw [Complex.ofReal_im]), ← hx]
        exact hΦl _ hwcl
      · have hv' : v ∈ φ '' A := hφ.2.2.symm ▸ hv
        obtain ⟨u, hu, rfl⟩ := hv'
        have h1 := hΦ.2.2.1 (subset_closure ⟨u, hu, rfl⟩) hwcl (by rw [hΦ.1 u hu, hve])
        exact (hwA ⟨u, hu, h1⟩).elim

/-- **G** (the glued map): a `K₁`-q.c. reflection `g : A₁ → A₂` in a quasicircle `C` through `∞` gives a `K₁`-q.c.
map `G` of the plane onto itself with `G(ℍ) = A₁`, `G(𝕃) = A₂`, `G(ℝ) = C ∩ ℂ` and `G ∘ conj = g ∘ G` on `ℍ`:
`G = φ⁻¹` on `ℍ ∪ ℝ` (`Φ⁻¹` on `ℝ`) and `G = g ∘ φ⁻¹ ∘ conj` on `𝕃`; `G` is continuous across `ℝ` since `g` tends to
the identity at `C ∩ ℂ`, bijective since `ℂ = A₁ ∪ (C ∩ ℂ) ∪ A₂`, hence a homeomorphism (`s20l_homeo_of_bij`), and
`K₁`-q.c. by `wd_glue`. -/
theorem s20l_glue {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hq : IsQuasicircle C) {g : ℂ → ℂ} {K₁ : ℝ}
    (hg : IsPlanarQCReflection A₁ A₂ g K₁) :
    ∃ G : ℂ → ℂ, IsKQC G univ K₁ ∧ G '' univ = univ ∧ G '' upperHalf = A₁ ∧ G '' lowerHalf = A₂ ∧
      G '' realLine = {z : ℂ | (z : ExtPlane) ∈ C} ∧ ∀ ζ ∈ upperHalf, G (conj ζ) = g (G ζ) := by
  classical
  obtain ⟨⟨φ, hφ, Φ, hΦ, hΦinf⟩, ψ, hψ, Ψ, hΨ, -⟩ := s20l_uniformizers hinf hC hq
  obtain ⟨g₀, _K, hg₀, hg₀s, hCeq, hA₁g, hA₂g⟩ := wd_normal_form hinf hC hq
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, hA₁eq, hA₂eq, -⟩ := hC
  obtain ⟨hginj, hgA, hgq, hgt⟩ := hg
  have hK₁ : 1 ≤ K₁ := hgq.2.1
  -- the components are open, with frontier `C`
  have hCo : IsOpen Cᶜ := by
    obtain ⟨γ, hγc, -, hγr⟩ := hJ
    rw [← hγr]
    exact (isCompact_range hγc).isClosed.isOpen_compl
  have hA₁e : IsOpen (toExt A₁) := by
    rw [hA₁eq]
    exact hCo.connectedComponentIn
  have hA₂e : IsOpen (toExt A₂) := by
    rw [hA₂eq]
    exact hCo.connectedComponentIn
  have hA₁o : IsOpen A₁ := OnePoint.isOpen_image_coe.1 hA₁e
  have hA₂o : IsOpen A₂ := OnePoint.isOpen_image_coe.1 hA₂e
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, hA₁eq⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := wd_frontier_eq hJ ⟨p₂, hp₂, hA₂eq⟩ (Or.inr rfl) hψ hΨ
  have hdisj : Disjoint A₁ A₂ := by
    rw [hA₁g, hA₂g, disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := hg₀.2.2.1.2.1 (mem_univ b) (mem_univ a) hab
    have ha' : 0 < a.im := ha
    have hb' : b.im < 0 := hb
    rw [hba] at hb'
    exact lt_asymm ha' hb'
  have hdis : Disjoint (closure A₁) A₂ := hdisj.closure_left hA₂o
  have hCA₁ : ∀ z : ℂ, (z : ExtPlane) ∈ C → z ∉ A₁ := by
    intro z hz hzA
    rw [← hfr₁, hA₁e.frontier_eq] at hz
    exact hz.2 ⟨z, hzA, rfl⟩
  have hfr12 : ∀ p ∈ frontier A₁, p ∈ frontier A₁ ∩ frontier A₂ := fun p hp =>
    ⟨hp, (s20l_g_mem_frontier_iff hA₂o p).2 (by rw [hfr₂, ← hfr₁]; exact (s20l_g_mem_frontier_iff hA₁o p).1 hp)⟩
  -- the half-plane map `H`
  obtain ⟨H, hHc, hHi, hHφ, hHR⟩ := s20l_g_half hA₁o hφ hΦ hΦinf hfr₁ hinf
  have hφi := hφ.symm hA₁o
  have hHU : H '' upperHalf = A₁ := by
    rw [image_congr hHφ, hφi.2.2]
  have hHA : ∀ z : ℂ, 0 < z.im → H z ∈ A₁ := fun z hz => by
    have h1 : H z ∈ H '' upperHalf := mem_image_of_mem H (show z ∈ upperHalf from hz)
    rwa [hHU] at h1
  have hHRC : ∀ z : ℂ, z.im = 0 → ((H z : ℂ) : ExtPlane) ∈ C := fun z hz => by
    have h1 : H z ∈ H '' realLine := mem_image_of_mem H (show z ∈ realLine from hz)
    rw [hHR] at h1
    exact h1
  have hHcl : ∀ z : ℂ, 0 ≤ z.im → H z ∈ closure A₁ := by
    intro z hz
    rcases hz.lt_or_eq with hlt | heq
    · exact subset_closure (hHA z hlt)
    · refine frontier_subset_closure ((s20l_g_mem_frontier_iff hA₁o _).2 ?_)
      rw [hfr₁]
      exact hHRC z heq.symm
  -- `g` is continuous on `A₁`; `g` extended by the identity is continuous on the closure
  have hgc : ContinuousOn g A₁ := by
    have h1 : ContinuousOn (fun z => conj (g z)) A₁ := hgq.2.2.1.1
    refine (Complex.continuous_conj.comp_continuousOn h1).congr fun z _ => ?_
    simp
  obtain ⟨g', hg'A, hg'n⟩ : ∃ g' : ℂ → ℂ, (∀ z ∈ A₁, g' z = g z) ∧ ∀ z ∉ A₁, g' z = z :=
    ⟨fun z => if z ∈ A₁ then g z else z, fun z hz => ite_eq_left hz, fun z hz => ite_eq_right hz⟩
  have hg'c : ContinuousOn g' (closure A₁) := by
    refine s20l_g_ext_cont hA₁o hgc (fun p hp => hgt p (hfr12 p hp)) (fun z hz => hg'A z hz) fun z hz => ?_
    rw [hA₁o.frontier_eq] at hz
    exact hg'n z hz.2
  -- the glued map
  obtain ⟨G, hGup, hGlo⟩ : ∃ G : ℂ → ℂ, (∀ z : ℂ, 0 ≤ z.im → G z = H z) ∧
      ∀ z : ℂ, z.im < 0 → G z = g (H (conj z)) :=
    ⟨fun z => if 0 ≤ z.im then H z else g (H (conj z)), fun z hz => ite_eq_left hz,
      fun z hz => ite_eq_right (not_le.2 hz)⟩
  have hconjU : ∀ z : ℂ, z.im < 0 → 0 < (conj z).im := fun z hz => by
    rw [conj_im]
    linarith
  -- continuity
  have hGc : Continuous G := by
    have hU : ContinuousOn G {z : ℂ | 0 ≤ z.im} := hHc.congr fun z hz => hGup z hz
    have hL : ContinuousOn G {z : ℂ | z.im ≤ 0} := by
      have hmap : MapsTo (fun ζ => conj ζ) {z : ℂ | z.im ≤ 0} {z : ℂ | 0 ≤ z.im} := fun z hz => by
        have hz' : z.im ≤ 0 := hz
        show 0 ≤ (conj z).im
        rw [conj_im]
        linarith
      have h1 : ContinuousOn (fun ζ => H (conj ζ)) {z : ℂ | z.im ≤ 0} :=
        hHc.comp Complex.continuous_conj.continuousOn hmap
      have h2 : MapsTo (fun ζ => H (conj ζ)) {z : ℂ | z.im ≤ 0} (closure A₁) := fun z hz => hHcl _ (hmap hz)
      refine (hg'c.comp h1 h2).congr fun z hz => ?_
      have hz' : z.im ≤ 0 := hz
      rcases hz'.lt_or_eq with hlt | heq
      · rw [hGlo z hlt]
        exact (hg'A _ (hHA _ (hconjU z hlt))).symm
      · have hcz : conj z = z := Complex.conj_eq_iff_im.2 heq
        rw [hGup z heq.symm.le]
        show H z = g' (H (conj z))
        rw [hcz, hg'n _ (hCA₁ _ (hHRC z heq))]
    have hcov : {z : ℂ | 0 ≤ z.im} ∪ {z : ℂ | z.im ≤ 0} = univ :=
      eq_univ_of_forall fun z => le_total 0 z.im
    rw [← continuousOn_univ, ← hcov]
    exact hU.union_of_isClosed hL (isClosed_le continuous_const continuous_im)
      (isClosed_le continuous_im continuous_const)
  -- images
  have hGU : G '' upperHalf = A₁ := by
    rw [← hHU]
    exact image_congr fun z hz => hGup z (le_of_lt hz)
  have hGR : G '' realLine = {z : ℂ | (z : ExtPlane) ∈ C} := by
    rw [← hHR]
    exact image_congr fun z hz => hGup z (show z.im = 0 from hz).symm.le
  have hconjL : (starRingEnd ℂ) '' lowerHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hconjU z hz
    · intro hw
      refine ⟨conj w, ?_, conj_conj w⟩
      show (conj w).im < 0
      rw [conj_im]
      exact neg_neg_of_pos hw
  have hGL : G '' lowerHalf = A₂ := by
    rw [← hgA, ← hHU, ← hconjL, image_image, image_image]
    exact image_congr fun z hz => hGlo z hz
  -- injectivity
  have hGi : Function.Injective G := by
    have hlow : ∀ z : ℂ, z.im < 0 → G z ∈ A₂ := fun z hz => by
      rw [← hGL]
      exact mem_image_of_mem G hz
    have hup : ∀ z : ℂ, 0 ≤ z.im → G z ∈ closure A₁ := fun z hz => by
      rw [hGup z hz]
      exact hHcl z hz
    intro a b hab
    rcases le_or_gt 0 a.im with ha | ha <;> rcases le_or_gt 0 b.im with hb | hb
    · refine hHi ha hb ?_
      rw [← hGup a ha, ← hGup b hb]
      exact hab
    · exact (disjoint_left.1 hdis (hup a ha) (hab ▸ hlow b hb)).elim
    · exact (disjoint_left.1 hdis (hup b hb) (hab.symm ▸ hlow a ha)).elim
    · have h1 : H (conj a) = H (conj b) := by
        refine hginj (hHA _ (hconjU a ha)) (hHA _ (hconjU b hb)) ?_
        rw [← hGlo a ha, ← hGlo b hb]
        exact hab
      have h2 : conj a = conj b := hHi (hconjU a ha).le (hconjU b hb).le h1
      have h3 := congrArg conj h2
      rwa [conj_conj, conj_conj] at h3
  -- surjectivity
  have hGs : Function.Surjective G := by
    intro z
    have hz : z ∈ g₀ '' univ := by
      rw [hg₀s]
      exact mem_univ z
    obtain ⟨w, -, rfl⟩ := hz
    rcases lt_trichotomy w.im 0 with hw | hw | hw
    · have h1 : g₀ w ∈ G '' lowerHalf := by
        rw [hGL, hA₂g]
        exact mem_image_of_mem g₀ hw
      obtain ⟨ζ, -, hζ⟩ := h1
      exact ⟨ζ, hζ⟩
    · have h1 : g₀ w ∈ G '' realLine := by
        rw [hGR]
        show ((g₀ w : ℂ) : ExtPlane) ∈ C
        rw [hCeq]
        exact Or.inl ⟨g₀ w, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨ζ, -, hζ⟩ := h1
      exact ⟨ζ, hζ⟩
    · have h1 : g₀ w ∈ G '' upperHalf := by
        rw [hGU, hA₁g]
        exact mem_image_of_mem g₀ hw
      obtain ⟨ζ, -, hζ⟩ := h1
      exact ⟨ζ, hζ⟩
  -- quasiconformality on `ℍ` and on `𝕃`, then gluing
  have hφiq : IsKQC (Function.invFunOn φ A₁) upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf hφi
  have hGUq : IsKQC G upperHalf K₁ :=
    ad_isKQC_congr (hφiq.mono hK₁) fun z hz => by
      rw [hGup z (le_of_lt hz)]
      exact hHφ hz
  have hGLq : IsKQC G lowerHalf K₁ := by
    have h1 := thm7_1_comp hφiq hgq hφi.2.2.subset
    rw [one_mul] at h1
    have h2 := abR_x_isKQC_conj h1
    have hpre : (starRingEnd ℂ) ⁻¹' upperHalf = lowerHalf := by
      ext z
      show 0 < (conj z).im ↔ z.im < 0
      rw [conj_im, neg_pos]
    rw [hpre] at h2
    refine ad_isKQC_congr h2 fun z hz => ?_
    rw [hGlo z hz]
    show g (H (conj z)) = conj (conj (g (Function.invFunOn φ A₁ (conj z))))
    rw [conj_conj, hHφ (hconjU z hz)]
  have hGh : IsHomeomorphOnto G univ univ := s20l_homeo_of_bij hGc hGi hGs
  have hGimg : G '' univ = univ := hGh.2.2.1
  have hGh' : IsHomeomorphOnto G univ (G '' univ) := by
    rw [hGimg]
    exact hGh
  refine ⟨G, wd_glue hK₁ hGh' hGUq hGLq, hGimg, hGU, hGL, hGR, fun ζ hζ => ?_⟩
  have hc : (conj ζ).im < 0 := by
    rw [conj_im]
    exact neg_neg_of_pos hζ
  rw [hGlo _ hc, conj_conj, hGup ζ (le_of_lt hζ)]

/-- The normal form of a `K`-quasicircle `C` through `∞` with complementary components `A₁, A₂`, keeping `K`:
`C = g₀(ℝ) ∪ {∞}`, `A₁ = g₀(ℍ)`, `A₂ = g₀(𝕃)` for a `K`-q.c. map `g₀` of the plane onto itself
(`tp_quasicircle_through_inf`, then the component argument of `wd_normal_form`; `g₀(-z)` if swapped). -/
theorem s20l_uw_normal_form {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {K : ℝ} (hCK : IsKQuasicircle C K)
    (hinf : extInf ∈ C) (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) :
    ∃ g₀ : ℂ → ℂ, IsKQC g₀ univ K ∧ g₀ '' univ = univ ∧ C = toExt (g₀ '' realLine) ∪ {extInf} ∧
      A₁ = g₀ '' upperHalf ∧ A₂ = g₀ '' lowerHalf := by
  obtain ⟨g, hg, hgs, rfl⟩ := tp_quasicircle_through_inf hCK hinf
  obtain ⟨e, rfl⟩ := t1_homeomorph hg hgs
  obtain ⟨-, p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
  have hinj : Function.Injective toExt := image_injective.2 OnePoint.coe_injective
  rcases wd_n_components e hp₁ with hc₁ | hc₁ <;> rcases wd_n_components e hp₂ with hc₂ | hc₂
  · exact absurd (h₁.trans (hc₁.trans (hc₂.symm.trans h₂.symm))) hne
  · exact ⟨e, hg, hgs, rfl, hinj (h₁.trans hc₁), hinj (h₂.trans hc₂)⟩
  · -- the components are swapped: precompose with `z ↦ -z`
    have hneg : IsKQC (fun z : ℂ => -z) univ 1 :=
      isKQC_one_of_conformal (D' := (fun z : ℂ => -z) '' univ) isOpen_univ
        ⟨differentiable_id.neg.differentiableOn, fun a _ b _ h => neg_injective h, rfl⟩
    have hK' := thm7_1_comp hneg hg (subset_univ _)
    rw [one_mul] at hK'
    have himg : ∀ S : Set ℂ, (fun z : ℂ => e (-z)) '' S = e '' ((fun z : ℂ => -z) '' S) :=
      fun S => (image_image e (fun z : ℂ => -z) S).symm
    have hR : (fun z : ℂ => -z) '' realLine = realLine :=
      wd_n_neg_image fun z => by
        show (-z).im = 0 ↔ z.im = 0
        rw [neg_im, neg_eq_zero]
    have hU : (fun z : ℂ => -z) '' upperHalf = lowerHalf :=
      wd_n_neg_image fun z => by
        show (-z).im < 0 ↔ 0 < z.im
        rw [neg_im, neg_lt_zero]
    have hL : (fun z : ℂ => -z) '' lowerHalf = upperHalf :=
      wd_n_neg_image fun z => by
        show 0 < (-z).im ↔ z.im < 0
        rw [neg_im, neg_pos]
    have huniv : (fun z : ℂ => -z) '' univ = univ := image_univ_of_surjective neg_surjective
    refine ⟨fun z => e (-z), hK', ?_, ?_, ?_, ?_⟩
    · rw [himg, huniv, hgs]
    · rw [himg, hR]
    · rw [himg, hU]
      exact hinj (h₁.trans hc₁)
    · rw [himg, hL]
      exact hinj (h₂.trans hc₂)
  · exact absurd (h₁.trans (hc₁.trans (hc₂.symm.trans h₂.symm))) hne

/-- `wd_forward_core` with the dilatation exposed: the welded self-map `g` of `ℍ` is `(K·1)(K·1)`-q.c. (same proof:
`g = (conj ∘ ψ ∘ g₀ ∘ conj) ∘ (φ ∘ g₀)⁻¹`, each factor `K·1`-q.c.). -/
theorem s20l_uw_forward_core {A₁ A₂ : Set ℂ} {g₀ : ℂ → ℂ} {K : ℝ} (hg₀ : IsKQC g₀ univ K)
    (hg₀s : g₀ '' univ = univ) (hA₁ : A₁ = g₀ '' upperHalf) (hA₂ : A₂ = g₀ '' lowerHalf) {φ ψ : ℂ → ℂ}
    {Φ Ψ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ x : ℝ, ∃ y : ℝ, Φ ((g₀ x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) ∧
      Ψ ((g₀ x : ℂ) : ExtPlane) = (((h y : ℝ) : ℂ) : ExtPlane)) :
    ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane), IsKQC g upperHalf ((K * 1) * (K * 1)) ∧ g '' upperHalf = upperHalf ∧
      IsHomeoExtension g upperHalf upperHalf G ∧ G extInf = extInf ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hg₀ hg₀s
  subst hA₁ hA₂
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  -- `T₁ = φ ∘ g₀ : ℍ → ℍ`
  have hT₁ : IsKQC (φ ∘ ⇑e) upperHalf (K * 1) :=
    thm7_1_comp (ac_t_isKQC_restrict hg₀ isOpen_upperHalf (subset_univ _))
      (isKQC_one_of_conformal (e.isOpenMap _ isOpen_upperHalf) hφ) Subset.rfl
  have hT₁s : (φ ∘ ⇑e) '' upperHalf = upperHalf := by rw [image_comp, hφ.2.2]
  have hT₁m : MapsTo (φ ∘ ⇑e) upperHalf upperHalf := fun z hz => hT₁s ▸ mem_image_of_mem _ hz
  have hT₁e : IsHomeoExtension (φ ∘ ⇑e) upperHalf upperHalf (Φ ∘ e.onePointCongr) :=
    hΦ.comp (s13x_de_isHomeoExtension_homeomorph e upperHalf) (mapsTo_image _ _)
  -- `T₂ = ψ ∘ g₀ : 𝕃 → 𝕃`
  have hT₂ : IsKQC (ψ ∘ ⇑e) lowerHalf (K * 1) :=
    thm7_1_comp (ac_t_isKQC_restrict hg₀ hLo (subset_univ _))
      (isKQC_one_of_conformal (e.isOpenMap _ hLo) hψ) Subset.rfl
  have hT₂s : (ψ ∘ ⇑e) '' lowerHalf = lowerHalf := by rw [image_comp, hψ.2.2]
  have hT₂m : MapsTo (ψ ∘ ⇑e) lowerHalf lowerHalf := fun z hz => hT₂s ▸ mem_image_of_mem _ hz
  have hT₂e : IsHomeoExtension (ψ ∘ ⇑e) lowerHalf lowerHalf (Ψ ∘ e.onePointCongr) :=
    hΨ.comp (s13x_de_isHomeoExtension_homeomorph e lowerHalf) (mapsTo_image _ _)
  -- `T = conj ∘ T₂ ∘ conj : ℍ → ℍ`
  set c : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph
  have hcU : IsHomeoExtension c upperHalf lowerHalf c.onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph c upperHalf
    rwa [wd_w_conj_image_upperHalf] at h1
  have hcL : IsHomeoExtension c lowerHalf upperHalf c.onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph c lowerHalf
    rwa [wd_w_conj_image_lowerHalf] at h1
  have hcm : MapsTo c upperHalf lowerHalf := fun z hz =>
    wd_w_conj_image_upperHalf ▸ mem_image_of_mem _ hz
  have hTe : IsHomeoExtension (c ∘ ((ψ ∘ ⇑e) ∘ c)) upperHalf upperHalf
      (c.onePointCongr ∘ ((Ψ ∘ e.onePointCongr) ∘ c.onePointCongr)) :=
    hcL.comp (hT₂e.comp hcU hcm) (hT₂m.comp hcm)
  have hT : IsKQC (c ∘ ((ψ ∘ ⇑e) ∘ c)) upperHalf (K * 1) := by
    have h1 := abR_x_isKQC_conj hT₂
    have hpre : (starRingEnd ℂ) ⁻¹' lowerHalf = upperHalf := by
      ext z
      show (conj z).im < 0 ↔ 0 < z.im
      rw [conj_im, neg_lt_zero]
    rw [hpre] at h1
    exact h1
  have hTs : (c ∘ ((ψ ∘ ⇑e) ∘ c)) '' upperHalf = upperHalf := by
    rw [image_comp, image_comp, wd_w_conj_image_upperHalf, hT₂s, wd_w_conj_image_lowerHalf]
  -- `g = T ∘ T₁⁻¹`
  have hT₁hom : IsHomeomorphOnto (φ ∘ ⇑e) upperHalf upperHalf := by
    have h1 := hT₁.2.2.1
    rwa [hT₁s] at h1
  have hinv : IsKQC (Function.invFunOn (φ ∘ ⇑e) upperHalf) upperHalf (K * 1) := by
    have h1 := thm7_2_inv hT₁
    rwa [hT₁s] at h1
  have hinvm : MapsTo (Function.invFunOn (φ ∘ ⇑e) upperHalf) upperHalf upperHalf := by
    intro w hw
    rw [← hT₁s] at hw
    exact Function.invFunOn_mem hw
  have hinvs : Function.invFunOn (φ ∘ ⇑e) upperHalf '' upperHalf = upperHalf :=
    Subset.antisymm hinvm.image_subset fun z hz =>
      ⟨(φ ∘ ⇑e) z, hT₁m hz, hT₁hom.2.1.leftInvOn_invFunOn hz⟩
  have hinve := uq_isHomeoExtension_invFunOn isOpen_upperHalf isOpen_upperHalf hT₁hom hT₁e
  have hT₁inj := hT₁e.2.2.1
  refine ⟨(c ∘ ((ψ ∘ ⇑e) ∘ c)) ∘ Function.invFunOn (φ ∘ ⇑e) upperHalf,
    (c.onePointCongr ∘ ((Ψ ∘ e.onePointCongr) ∘ c.onePointCongr)) ∘
      Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)),
    thm7_1_comp hinv hT hinvm.image_subset, by rw [image_comp, hinvs, hTs], hTe.comp hinve hinvm, ?_, ?_⟩
  · -- `G ∞ = ∞`
    have hinfmem : extInf ∈ closure (toExt upperHalf) :=
      frontier_subset_closure infty_mem_frontier_upperHalf
    have h1 : Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) extInf = extInf := by
      have h2 := hT₁inj.leftInvOn_invFunOn hinfmem
      have h3 : (Φ ∘ e.onePointCongr) extInf = extInf := hΦinf
      rwa [h3] at h2
    show c.onePointCongr (Ψ (e.onePointCongr (c.onePointCongr
      (Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) extInf)))) = extInf
    rw [h1]
    show c.onePointCongr (Ψ extInf) = extInf
    rw [hΨinf]
    rfl
  · -- boundary values
    intro y
    obtain ⟨x, hx⟩ := wd_w_real_preimage hT₁e hT₁m hΦinf y
    obtain ⟨y', hy'1, hy'2⟩ := hh x
    have hyy : y' = y := by
      have h1 : Φ ((e x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := hx
      rw [hy'1] at h1
      exact Complex.ofReal_injective (OnePoint.coe_injective h1)
    subst hyy
    have hxmem : ((x : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
      frontier_subset_closure (ofReal_mem_frontier_upperHalf x)
    have h1 : Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf))
        ((y' : ℂ) : ExtPlane) = ((x : ℂ) : ExtPlane) := by
      rw [← hx]
      exact hT₁inj.leftInvOn_invFunOn hxmem
    show c.onePointCongr (Ψ (e.onePointCongr (c.onePointCongr
      (Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) ((y' : ℂ) : ExtPlane))))) = _
    rw [h1]
    have hcx : c.onePointCongr ((x : ℂ) : ExtPlane) = ((x : ℂ) : ExtPlane) := by
      show (((conj (x : ℂ)) : ℂ) : ExtPlane) = _
      rw [conj_ofReal]
    rw [hcx]
    show c.onePointCongr (Ψ ((e x : ℂ) : ExtPlane)) = _
    rw [hy'2]
    show (((conj ((h y' : ℝ) : ℂ)) : ℂ) : ExtPlane) = _
    rw [conj_ofReal]

/-- The welding `h` of `s20l_uw_forward_core` is `λ((K·1)(K·1))`-quasisymmetric (`thm17_1_quasisymmetric`). -/
theorem s20l_uw_qs_core {A₁ A₂ : Set ℂ} {g₀ : ℂ → ℂ} {K : ℝ} (hg₀ : IsKQC g₀ univ K) (hg₀s : g₀ '' univ = univ)
    (hA₁ : A₁ = g₀ '' upperHalf) (hA₂ : A₂ = g₀ '' lowerHalf) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ x : ℝ, ∃ y : ℝ, Φ ((g₀ x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) ∧
      Ψ ((g₀ x : ℂ) : ExtPlane) = (((h y : ℝ) : ℂ) : ExtPlane)) :
    IsQuasisymmetric h (lambdaInv ((K * 1) * (K * 1))) := by
  obtain ⟨g, G, hg, hgs, hG, hGinf, hGx⟩ :=
    s20l_uw_forward_core hg₀ hg₀s hA₁ hA₂ hφ hψ hΦ hΨ hΦinf hΨinf hh
  exact thm17_1_quasisymmetric ⟨hg, hgs, G, hG, hGinf, hGx⟩

/-- A finite boundary point `z ∉ U` of `U` is sent to a real point by a homeomorphic extension `F`, fixing `∞`
(`∞ ∈ ∂U`), of a conformal map of `U` onto `ℍ` or `𝕃`: `F z` lies in the closure of the half-plane, is not `∞`
(injectivity) and is not in the half-plane (`f(U) = V`, injectivity). -/
theorem s20l_uw_real_point {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F)
    (hfUV : f '' U = V) (hV : V = upperHalf ∨ V = lowerHalf) (hFinf : F extInf = extInf)
    (hinfU : extInf ∈ closure (toExt U)) {z : ℂ} (hz : (z : ExtPlane) ∈ closure (toExt U)) (hzU : z ∉ U) :
    ∃ x : ℝ, F z = ((x : ℂ) : ExtPlane) := by
  have hFz : F z ∈ closure (toExt V) := hF.2.2.2 ▸ mem_image_of_mem F hz
  have hni : F z ≠ extInf := fun h => OnePoint.coe_ne_infty z (hF.2.2.1 hz hinfU (h.trans hFinf.symm))
  have hnV : ∀ v ∈ V, F z ≠ (v : ExtPlane) := by
    intro v hv h
    rw [← hfUV] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← hF.1 u hu] at h
    have hzu : (z : ExtPlane) = (u : ExtPlane) := hF.2.2.1 hz (subset_closure ⟨u, hu, rfl⟩) h
    exact hzU (OnePoint.coe_injective hzu ▸ hu)
  rcases wd_b_cases (F z) with h | ⟨x, h⟩ | ⟨w, hw, h⟩ | ⟨w, hw, h⟩
  · exact absurd h hni
  · exact ⟨x, h⟩
  · rcases hV with rfl | rfl
    · exact absurd h (hnV w hw)
    · exact (disjoint_left.1 wd_b_closure_lower_disjoint hFz ⟨w, hw, h.symm⟩).elim
  · rcases hV with rfl | rfl
    · exact (disjoint_left.1 wd_b_closure_upper_disjoint hFz ⟨w, hw, h.symm⟩).elim
    · exact absurd h (hnV w hw)

/-- **W** (the welding is uniformly quasisymmetric): for a `K`-quasicircle through `∞` and uniformizers
`φ : A₁ → ℍ`, `ψ : A₂ → 𝕃` fixing `∞`, the welding `w = ψ ∘ φ⁻¹` on `ℝ` is `λ(K²)`-quasisymmetric (a `K`-explicit
`wd_forward_core`: the welded self-map of `ℍ` is `K²`-q.c., then `thm17_1_quasisymmetric`). -/
theorem s20l_welding_qs {C : Set ExtPlane} {A₁ A₂ : Set ℂ} {K : ℝ} (hCK : IsKQuasicircle C K)
    (hinf : extInf ∈ C) (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ}
    {Φ Ψ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) :
    ∃ w : ℝ → ℝ, IsQuasisymmetric w (lambdaInv (K * K)) ∧
      ∀ z : ℂ, (z : ExtPlane) ∈ C → ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((w x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨g₀, hg₀, hg₀s, hCeq, hA₁, hA₂⟩ := s20l_uw_normal_form hCK hinf hC
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, -⟩ := hC
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, h₁⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := wd_frontier_eq hJ ⟨p₂, hp₂, h₂⟩ (Or.inr rfl) hψ hΨ
  have hcl₁ : C ⊆ closure (toExt A₁) := hfr₁ ▸ frontier_subset_closure
  have hcl₂ : C ⊆ closure (toExt A₂) := hfr₂ ▸ frontier_subset_closure
  have hnot : ∀ (A : Set ℂ) (p : ExtPlane), toExt A = connectedComponentIn Cᶜ p →
      ∀ z : ℂ, (z : ExtPlane) ∈ C → z ∉ A := by
    intro A p hA z hz hzA
    have hmem : (z : ExtPlane) ∈ connectedComponentIn Cᶜ p := hA ▸ ⟨z, hzA, rfl⟩
    exact connectedComponentIn_subset _ _ hmem hz
  set w : ℝ → ℝ := fun x => (extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re
    with hw
  have key : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((w x : ℝ) : ℂ) : ExtPlane) := by
    intro z hz
    obtain ⟨x, hx⟩ :=
      s20l_uw_real_point hΦ hφ.2.2 (Or.inl rfl) hΦinf (hcl₁ hinf) (hcl₁ hz) (hnot A₁ p₁ h₁ z hz)
    obtain ⟨y, hy⟩ :=
      s20l_uw_real_point hΨ hψ.2.2 (Or.inr rfl) hΨinf (hcl₂ hinf) (hcl₂ hz) (hnot A₂ p₂ h₂ z hz)
    refine ⟨x, hx, ?_⟩
    have hinv : Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane) = (z : ExtPlane) := by
      rw [← hx]
      exact hΦ.2.2.1.leftInvOn_invFunOn (hcl₁ hz)
    have hwx : w x = y := by
      rw [hw]
      show (extToC (Ψ (Function.invFunOn Φ (closure (toExt A₁)) ((x : ℂ) : ExtPlane)))).re = y
      rw [hinv, hy]
      exact Complex.ofReal_re y
    rw [hwx, hy]
  refine ⟨w, ?_, key⟩
  have hqs := s20l_uw_qs_core hg₀ hg₀s hA₁ hA₂ hφ hψ hΦ hΨ hΦinf hΨinf (h := w) fun x =>
    key (g₀ x) (by rw [hCeq]; exact Or.inl ⟨g₀ x, ⟨x, Complex.ofReal_im x, rfl⟩, rfl⟩)
  rwa [mul_one] at hqs

/-- **S** ((20.13′), Schwarz): a conformal map `φ : A → ℍ` has `|φ'(z)| ≤ 2 Im φ(z) / r` when `ball z r ⊆ A`
(`η_A(z) = |φ'(z)|/Im φ(z) ≤ η_{ball z r}(z) = 2/r`). -/
theorem s20l_schwarz_upper {A : Set ℂ} (hA : IsOpen A) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ A upperHalf) {z : ℂ}
    (hz : z ∈ A) {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ A) : ‖deriv φ z‖ ≤ 2 * (φ z).im / r := by
  have hf : IsConformalOnto (cayley ∘ φ) A unitDisc := isConformalOnto_cayley.comp hφ
  have hle := s20l_density_le hA hf hz hr hball
  rw [(poincareDensity_well_defined hA hf hf hz).2] at hle
  have hu : 0 < (φ z).im := by
    have hmem : φ z ∈ upperHalf := hφ.mapsTo hz
    exact hmem
  have hden := cayley_den_ne_zero hu
  have hpos : 0 < normSq (φ z + I) := normSq_pos.mpr hden
  have hd : HasDerivAt cayley (2 * I / (φ z + I) ^ 2) (φ z) := by
    have h0 : HasDerivAt (fun v : ℂ => v) 1 (φ z) := hasDerivAt_id (φ z)
    have h1 : HasDerivAt (fun v : ℂ => v - I) 1 (φ z) := by simpa using h0.sub_const I
    have h2 : HasDerivAt (fun v : ℂ => v + I) 1 (φ z) := by simpa using h0.add_const I
    have hfun : cayley = fun v : ℂ => (v - I) / (v + I) := rfl
    rw [hfun]
    convert h1.div h2 hden using 1
    field_simp
    ring
  have hφd : HasDerivAt φ (deriv φ z) z := (hφ.1.differentiableAt (hA.mem_nhds hz)).hasDerivAt
  have hcomp : deriv (cayley ∘ φ) z = 2 * I / (φ z + I) ^ 2 * deriv φ z := (hd.comp z hφd).deriv
  have hdn : ‖deriv (cayley ∘ φ) z‖ = 2 / normSq (φ z + I) * ‖deriv φ z‖ := by
    rw [hcomp, norm_mul, norm_div, norm_mul, norm_pow, Complex.sq_norm]
    simp
  have hval : 1 - ‖(cayley ∘ φ) z‖ ^ 2 = 4 * (φ z).im / normSq (φ z + I) := by
    rw [Function.comp_apply, Complex.sq_norm, cayley, normSq_div, eq_div_iff (ne_of_gt hpos), sub_mul,
      one_mul, div_mul_cancel₀ _ (ne_of_gt hpos)]
    linarith [normSq_cayley_key (φ z)]
  rw [hdn, hval] at hle
  have heq : 2 * (2 / normSq (φ z + I) * ‖deriv φ z‖) / (4 * (φ z).im / normSq (φ z + I)) =
      ‖deriv φ z‖ / (φ z).im := by
    field_simp
    ring
  rw [heq, div_le_div_iff₀ hu hr] at hle
  rw [le_div_iff₀ hr]
  linarith

/-- **Q** ((20.14′), Koebe): a conformal map `ψ : A → 𝕃` has `|Im ψ(w)| ≤ 4 |w' - w| |ψ'(w)|` for every `w' ∉ A`
(Koebe's ¼-theorem for `ψ⁻¹` on the disc about `ψ w` of radius `|Im ψ w|`, which lies in `𝕃`). -/
theorem s20l_koebe_lower {A : Set ℂ} (hA : IsOpen A) {ψ : ℂ → ℂ} (hψ : IsConformalOnto ψ A lowerHalf) {w w' : ℂ}
    (hw : w ∈ A) (hw' : w' ∉ A) : |(ψ w).im| ≤ 4 * ‖w' - w‖ * ‖deriv ψ w‖ := by
  have hψw : (ψ w).im < 0 := by
    have hmem : ψ w ∈ lowerHalf := hψ.mapsTo hw
    exact hmem
  set R : ℝ := -(ψ w).im with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have habs : |(ψ w).im| = R := by rw [hR, abs_of_neg hψw]
  rw [habs]
  have hs : IsConformalOnto (Function.invFunOn ψ A) lowerHalf A := hψ.symm hA
  have hleft : ∀ v ∈ A, Function.invFunOn ψ A (ψ v) = v := fun v hv =>
    hψ.2.1.leftInvOn_invFunOn hv
  have hball : ∀ u ∈ ball (0 : ℂ) 1, ψ w + (R : ℂ) * u ∈ lowerHalf := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    show (ψ w + (R : ℂ) * u).im < 0
    have h1 : ((R : ℂ) * u).im ≤ ‖(R : ℂ) * u‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    have h2 : ‖(R : ℂ) * u‖ < R := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
      calc R * ‖u‖ < R * 1 := by gcongr
        _ = R := mul_one R
    rw [Complex.add_im]
    linarith
  set F : ℂ → ℂ := fun u => Function.invFunOn ψ A (ψ w + (R : ℂ) * u) - w with hF
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    have haff : DifferentiableOn ℂ (fun u : ℂ => ψ w + (R : ℂ) * u) (ball 0 1) := by fun_prop
    exact (hs.1.comp haff (fun u hu => hball u hu)).sub_const w
  have hFinj : InjOn F (ball 0 1) := by
    intro u₁ hu₁ u₂ hu₂ h
    have h' : Function.invFunOn ψ A (ψ w + (R : ℂ) * u₁) =
        Function.invFunOn ψ A (ψ w + (R : ℂ) * u₂) := by
      simp only [hF] at h
      linear_combination h
    have h'' := hs.2.1 (hball u₁ hu₁) (hball u₂ hu₂) h'
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    exact mul_left_cancel₀ hR0 (add_left_cancel h'')
  have hF0 : F 0 = 0 := by
    simp only [hF, mul_zero, add_zero]
    rw [hleft w hw, sub_self]
  have hnot : w' - w ∉ F '' ball 0 1 := by
    rintro ⟨u, hu, hFu⟩
    apply hw'
    have hmem : Function.invFunOn ψ A (ψ w + (R : ℂ) * u) ∈ A := hs.mapsTo (hball u hu)
    have hval : Function.invFunOn ψ A (ψ w + (R : ℂ) * u) = w' := by
      simp only [hF] at hFu
      linear_combination hFu
    rwa [hval] at hmem
  have hK := koebe_quarter_of_not_mem hFd hFinj hF0 hnot
  have hinvd : DifferentiableAt ℂ (Function.invFunOn ψ A) (ψ w) :=
    hψ.differentiableAt_invFunOn hA hw
  have hψd : HasDerivAt ψ (deriv ψ w) w := (hψ.1.differentiableAt (hA.mem_nhds hw)).hasDerivAt
  have haff : HasDerivAt (fun u : ℂ => ψ w + (R : ℂ) * u) (R : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)).const_add (ψ w)
  have hinvd' : HasDerivAt (Function.invFunOn ψ A) (deriv (Function.invFunOn ψ A) (ψ w))
      (ψ w + (R : ℂ) * 0) := by
    rw [mul_zero, add_zero]
    exact hinvd.hasDerivAt
  have hFder : HasDerivAt F (deriv (Function.invFunOn ψ A) (ψ w) * (R : ℂ)) 0 := by
    have h := (hinvd'.comp 0 haff).sub_const w
    exact h
  have hcomp1 : HasDerivAt (Function.invFunOn ψ A ∘ ψ)
      (deriv (Function.invFunOn ψ A) (ψ w) * deriv ψ w) w := hinvd.hasDerivAt.comp w hψd
  have hev : Function.invFunOn ψ A ∘ ψ =ᶠ[𝓝 w] id := by
    filter_upwards [hA.mem_nhds hw] with v hv
    exact hleft v hv
  have hcomp2 : HasDerivAt (Function.invFunOn ψ A ∘ ψ) 1 w :=
    (hasDerivAt_id w).congr_of_eventuallyEq hev
  have hone : deriv (Function.invFunOn ψ A) (ψ w) * deriv ψ w = 1 := hcomp1.unique hcomp2
  have hone' : ‖deriv (Function.invFunOn ψ A) (ψ w)‖ * ‖deriv ψ w‖ = 1 := by
    rw [← norm_mul, hone, norm_one]
  rw [hFder.deriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hRpos.le] at hK
  calc R = ‖deriv (Function.invFunOn ψ A) (ψ w)‖ * R * ‖deriv ψ w‖ := by
        linear_combination (-R) * hone'
    _ ≤ 4 * ‖w' - w‖ * ‖deriv ψ w‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- The Beurling–Ahlfors reflection `z ↦ ψ⁻¹(conj (h(φ z)))`, `h` the Beurling–Ahlfors extension of the welding
`w` with `r = 1`. -/
def s20l_refl (φ ψ : ℂ → ℂ) (A₂ : Set ℂ) (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z)))

/-- Transport of a limit through a homeomorphic extension: if `F` extends `f : U → V` and `q` lies in the closure of
`U` in `ℂ̄`, then `f` sends `z → q` within `U` (in `ℂ̄`) to `f z → F q` within `V`. -/
theorem s20l_r_ext_tendsto {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) (hfUV : MapsTo f U V) {q : ExtPlane} (hq : q ∈ closure (toExt U)) :
    Tendsto f (comap ((↑) : ℂ → ExtPlane) (𝓝 q) ⊓ 𝓟 U)
      (comap ((↑) : ℂ → ExtPlane) (𝓝 (F q)) ⊓ 𝓟 V) := by
  have hcoe : Tendsto ((↑) : ℂ → ExtPlane) (comap ((↑) : ℂ → ExtPlane) (𝓝 q) ⊓ 𝓟 U)
      (𝓝[closure (toExt U)] q) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_comap.mono_left inf_le_left,
      mem_inf_of_right (mem_principal.2 fun z hz => subset_closure (mem_image_of_mem _ hz))⟩
  have hFt : Tendsto (F ∘ ((↑) : ℂ → ExtPlane)) (comap ((↑) : ℂ → ExtPlane) (𝓝 q) ⊓ 𝓟 U)
      (𝓝 (F q)) :=
    (hF.2.1 q hq).tendsto.comp hcoe
  have heq : (F ∘ ((↑) : ℂ → ExtPlane)) =ᶠ[comap ((↑) : ℂ → ExtPlane) (𝓝 q) ⊓ 𝓟 U]
      (((↑) : ℂ → ExtPlane) ∘ f) :=
    mem_inf_of_right (mem_principal.2 fun z hz => hF.1 z hz)
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 (hFt.congr' heq),
    tendsto_principal.2 (mem_inf_of_right (mem_principal.2 fun z hz => hfUV hz))⟩

/-- **R** (the Beurling–Ahlfors reflection): with uniformizers `φ : A₁ → ℍ`, `ψ : A₂ → 𝕃` fixing `∞` and a
`ρ`-quasisymmetric welding `w`, `g = ψ⁻¹ ∘ conj ∘ h ∘ φ` (`h = beurlingAhlfors w 1`, `thm17_2_beurling_ahlfors`) is a
`C¹` `8ρ(ρ+1)`-q.c. reflection of `A₁` onto `A₂`, tends to `∞` at `∞`, and `|dg(z)| ≤ |φ'(z)| |dh(φ z)| / |ψ'(g z)|`
(chain rule; `(ψ⁻¹)' = 1/ψ'`). -/
theorem s20l_ba_reflection {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hq : IsQuasicircle C) {φ ψ : ℂ → ℂ}
    {Φ Ψ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {w : ℝ → ℝ} {ρ : ℝ} (hw : IsQuasisymmetric w ρ)
    (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((w x : ℝ) : ℂ) : ExtPlane)) :
    ContDiffOn ℝ 1 (s20l_refl φ ψ A₂ w) A₁ ∧ IsPlanarQCReflection A₁ A₂ (s20l_refl φ ψ A₂ w) (8 * ρ * (ρ + 1)) ∧
      Tendsto (s20l_refl φ ψ A₂ w) (cocompact ℂ ⊓ 𝓟 A₁) (cocompact ℂ) ∧
      ∀ z ∈ A₁, ‖fderiv ℝ (s20l_refl φ ψ A₂ w) z‖ ≤
        ‖deriv φ z‖ * ‖fderiv ℝ (beurlingAhlfors w 1) (φ z)‖ / ‖deriv ψ (s20l_refl φ ψ A₂ w z)‖ := by
  have _hq := hq
  obtain ⟨hC1, hK, himg, H, hH, hHinf, hHx⟩ := thm17_2_beurling_ahlfors hw
  obtain ⟨hCJ, p₁, hp₁, p₂, hp₂, hA₁, hA₂, -⟩ := hC
  have hCc : IsClosed C := by
    obtain ⟨γ, hγc, -, hγr⟩ := hCJ
    rw [← hγr]
    exact (isCompact_range hγc).isClosed
  have hA₁o : IsOpen A₁ := by
    refine OnePoint.isOpen_image_coe.1 ?_
    change IsOpen (toExt A₁)
    rw [hA₁]
    exact hCc.isOpen_compl.connectedComponentIn
  have hA₂o : IsOpen A₂ := by
    refine OnePoint.isOpen_image_coe.1 ?_
    change IsOpen (toExt A₂)
    rw [hA₂]
    exact hCc.isOpen_compl.connectedComponentIn
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hCJ ⟨p₁, hp₁, hA₁⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := wd_frontier_eq hCJ ⟨p₂, hp₂, hA₂⟩ (Or.inr rfl) hψ hΨ
  have hψs := hψ.symm hA₂o
  have hΨs := isHomeoExtension_invFunOn hψ hΨ
  have hφm : MapsTo φ A₁ upperHalf := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
  have hhm : MapsTo (beurlingAhlfors w 1) upperHalf upperHalf := fun z hz =>
    himg ▸ mem_image_of_mem _ hz
  have hcm : MapsTo (fun z : ℂ => conj z) upperHalf lowerHalf := fun z hz => by
    show (conj z).im < 0
    rw [conj_im]
    exact neg_neg_of_pos hz
  have hψm : MapsTo (Function.invFunOn ψ A₂) lowerHalf A₂ := fun z hz =>
    hψs.2.2.subset (mem_image_of_mem _ hz)
  -- (1) smoothness
  have h1 : ContDiffOn ℝ 1 (s20l_refl φ ψ A₂ w) A₁ := by
    have hφC : ContDiffOn ℝ 1 φ A₁ := (hφ.1.contDiffOn hA₁o).restrict_scalars ℝ
    have hψC : ContDiffOn ℝ 1 (Function.invFunOn ψ A₂) lowerHalf :=
      (hψs.1.contDiffOn hLo).restrict_scalars ℝ
    have hconj : ContDiffOn ℝ 1 (fun z : ℂ => conj z) upperHalf := by
      have h := (Complex.conjCLE.contDiff (n := 1)).contDiffOn (s := upperHalf)
      exact h.congr fun z _ => (Complex.conjCLE_apply z).symm
    exact hψC.comp (hconj.comp (hC1.comp hφC hφm) (hhm.comp hφm)) (hcm.comp (hhm.comp hφm))
  -- (2) the reflection
  have hinj : InjOn (s20l_refl φ ψ A₂ w) A₁ := by
    intro a ha b hb hab
    have h1 := hψs.2.1 (hcm (hhm (hφm ha))) (hcm (hhm (hφm hb))) hab
    have h2 : beurlingAhlfors w 1 (φ a) = beurlingAhlfors w 1 (φ b) := by
      simpa using congrArg (starRingEnd ℂ) h1
    exact hφ.2.1 ha hb (hK.2.2.1.2.1 (hφm ha) (hφm hb) h2)
  have hcimg : (fun z : ℂ => conj z) '' upperHalf = lowerHalf := by
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hcm hz
    · intro hu
      refine ⟨conj u, ?_, conj_conj u⟩
      show 0 < (conj u).im
      rw [conj_im]
      exact neg_pos.2 hu
  have himg' : s20l_refl φ ψ A₂ w '' A₁ = A₂ := by
    show (Function.invFunOn ψ A₂ ∘ (fun z : ℂ => conj z) ∘ beurlingAhlfors w 1 ∘ φ) '' A₁ = A₂
    rw [image_comp, image_comp, image_comp, hφ.2.2, himg, hcimg, hψs.2.2]
  have hKc : IsKQC (fun z => conj (s20l_refl φ ψ A₂ w z)) A₁ (8 * ρ * (ρ + 1)) := by
    have hψK' := abR_x_isKQC_conj (isKQC_one_of_conformal hLo hψs)
    have hpre : (conj ⁻¹' lowerHalf : Set ℂ) = upperHalf := by
      ext z
      show (conj z).im < 0 ↔ 0 < z.im
      rw [conj_im, neg_lt_zero]
    rw [hpre] at hψK'
    have h12 := thm7_1_comp (isKQC_one_of_conformal hA₁o hφ) hK hφ.2.2.le
    have h123 := thm7_1_comp h12 hψK' (by rw [image_comp, hφ.2.2, himg])
    rw [one_mul, mul_one] at h123
    exact h123
  have hbd : ∀ p ∈ frontier A₁ ∩ frontier A₂, Tendsto (s20l_refl φ ψ A₂ w) (𝓝[A₁] p) (𝓝 p) := by
    rintro p ⟨hp1, hp2⟩
    have hpcl1 : (p : ExtPlane) ∈ closure (toExt A₁) :=
      image_closure_subset_closure_image OnePoint.continuous_coe ⟨p, frontier_subset_closure hp1, rfl⟩
    have hpcl2 : (p : ExtPlane) ∈ closure (toExt A₂) :=
      image_closure_subset_closure_image OnePoint.continuous_coe ⟨p, frontier_subset_closure hp2, rfl⟩
    have hpC : (p : ExtPlane) ∈ C := by
      rw [← hfr₁]
      refine ⟨hpcl1, ?_⟩
      have hA₁e : IsOpen (toExt A₁) := OnePoint.isOpen_image_coe.2 hA₁o
      rw [hA₁e.interior_eq]
      rintro ⟨z, hz, hzp⟩
      rw [OnePoint.coe_injective hzp] at hz
      exact hp1.2 (hA₁o.interior_eq.symm ▸ hz)
    obtain ⟨x, hΦx, hΨx⟩ := hh p hpC
    have t1 := s20l_r_ext_tendsto hΦ hφm hpcl1
    rw [hΦx] at t1
    have t2 := s20l_r_ext_tendsto hH hhm (wd_b_real_mem_closure_upper x)
    rw [hHx x] at t2
    have t3 : Tendsto (fun z : ℂ => conj z)
        (comap ((↑) : ℂ → ExtPlane) (𝓝 (((w x : ℝ) : ℂ) : ExtPlane)) ⊓ 𝓟 upperHalf)
        (comap ((↑) : ℂ → ExtPlane) (𝓝 (((w x : ℝ) : ℂ) : ExtPlane)) ⊓ 𝓟 lowerHalf) := by
      rw [OnePoint.comap_coe_nhds]
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hcm))⟩
      have hc := Complex.continuous_conj.tendsto ((w x : ℝ) : ℂ)
      rw [Complex.conj_ofReal] at hc
      exact hc.mono_left inf_le_left
    have t4 := s20l_r_ext_tendsto hΨs hψm (wd_b_real_mem_closure_lower (w x))
    have hΨinv : Function.invFunOn Ψ (closure (toExt A₂)) (((w x : ℝ) : ℂ) : ExtPlane) = (p : ExtPlane) := by
      rw [← hΨx]
      exact hΨ.2.2.1.leftInvOn_invFunOn hpcl2
    rw [hΨinv] at t4
    have t := t4.comp (t3.comp (t2.comp t1))
    rw [OnePoint.comap_coe_nhds] at t
    exact t.mono_right inf_le_left
  -- (3) behaviour at `∞`
  have h3 : Tendsto (s20l_refl φ ψ A₂ w) (cocompact ℂ ⊓ 𝓟 A₁) (cocompact ℂ) := by
    have hinf1 : extInf ∈ closure (toExt A₁) := frontier_subset_closure (hfr₁.symm ▸ hinf)
    have hinf2 : extInf ∈ closure (toExt A₂) := frontier_subset_closure (hfr₂.symm ▸ hinf)
    have s1 := s20l_r_ext_tendsto hΦ hφm hinf1
    rw [hΦinf] at s1
    have s2 := s20l_r_ext_tendsto hH hhm s13x_rf_infty_mem_closure
    rw [hHinf] at s2
    have hLinf : extInf ∈ closure (toExt lowerHalf) := by
      rw [← hΨ.2.2.2, ← hΨinf]
      exact mem_image_of_mem Ψ hinf2
    have s3 : Tendsto (fun z : ℂ => conj z) (comap ((↑) : ℂ → ExtPlane) (𝓝 extInf) ⊓ 𝓟 upperHalf)
        (comap ((↑) : ℂ → ExtPlane) (𝓝 extInf) ⊓ 𝓟 lowerHalf) := by
      rw [OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hcm))⟩
      have hcc : Tendsto (fun z : ℂ => conj z) (cocompact ℂ) (cocompact ℂ) :=
        Filter.tendsto_cocompact_cocompact_of_norm fun ε => ⟨ε, fun z hz => by rwa [Complex.norm_conj]⟩
      exact hcc.mono_left inf_le_left
    have s4 := s20l_r_ext_tendsto hΨs hψm hLinf
    have hΨinv : Function.invFunOn Ψ (closure (toExt A₂)) extInf = extInf := by
      have h := hΨ.2.2.1.leftInvOn_invFunOn hinf2
      rwa [hΨinf] at h
    rw [hΨinv] at s4
    have s := s4.comp (s3.comp (s2.comp s1))
    rw [OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact] at s
    exact s.mono_right inf_le_left
  -- (4) the derivative bound
  have h4 : ∀ z ∈ A₁, ‖fderiv ℝ (s20l_refl φ ψ A₂ w) z‖ ≤
      ‖deriv φ z‖ * ‖fderiv ℝ (beurlingAhlfors w 1) (φ z)‖ / ‖deriv ψ (s20l_refl φ ψ A₂ w z)‖ := by
    intro z hz
    show ‖fderiv ℝ (s20l_refl φ ψ A₂ w) z‖ ≤ ‖deriv φ z‖ * ‖fderiv ℝ (beurlingAhlfors w 1) (φ z)‖ /
      ‖deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z))))‖
    have hvH : φ z ∈ upperHalf := hφm hz
    have huL : conj (beurlingAhlfors w 1 (φ z)) ∈ lowerHalf := hcm (hhm hvH)
    have hφd : HasDerivAt φ (deriv φ z) z := (hφ.1.differentiableAt (hA₁o.mem_nhds hz)).hasDerivAt
    have hhd : HasFDerivAt (beurlingAhlfors w 1) (fderiv ℝ (beurlingAhlfors w 1) (φ z)) (φ z) :=
      ((hC1.differentiableOn one_ne_zero).differentiableAt (isOpen_upperHalf.mem_nhds hvH)).hasFDerivAt
    have hψid : DifferentiableAt ℂ (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z))) :=
      hψs.1.differentiableAt (hLo.mem_nhds huL)
    have hψd : DifferentiableAt ℂ ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z)))) :=
      hψ.1.differentiableAt (hA₂o.mem_nhds (hψm huL))
    have hprod : deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z)))) *
        deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z))) = 1 := by
      have e1 := HasDerivAt.comp (conj (beurlingAhlfors w 1 (φ z))) hψd.hasDerivAt hψid.hasDerivAt
      have e2 : HasDerivAt (ψ ∘ Function.invFunOn ψ A₂) 1 (conj (beurlingAhlfors w 1 (φ z))) := by
        refine (hasDerivAt_id _).congr_of_eventuallyEq ?_
        filter_upwards [hLo.mem_nhds huL] with y hy
        exact Function.invFunOn_eq (show y ∈ ψ '' A₂ from hψ.2.2.symm ▸ hy)
      exact e1.unique e2
    have hconjd : HasFDerivAt (fun y : ℂ => conj y) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (beurlingAhlfors w 1 (φ z)) := Complex.conjCLE.hasFDerivAt
    have hg := (hψid.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp z
      (hconjd.comp z (hhd.comp z (hφd.hasFDerivAt.restrictScalars ℝ)))
    have hg' : HasFDerivAt (s20l_refl φ ψ A₂ w) _ z := hg
    rw [hg'.fderiv]
    have hnψ : ‖deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z))))‖ *
        ‖deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z)))‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    have hpos : 0 < ‖deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z))))‖ := by
      rcases (norm_nonneg (deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z)))))).lt_or_eq
        with h | h
      · exact h
      · rw [← h, zero_mul] at hnψ
        exact absurd hnψ zero_ne_one
    have hinv : ‖deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z)))‖ =
        1 / ‖deriv ψ (Function.invFunOn ψ A₂ (conj (beurlingAhlfors w 1 (φ z))))‖ := by
      rw [eq_div_iff hpos.ne', mul_comm, hnψ]
    refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_).trans_eq
      (show ‖deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z)))‖ *
        ‖fderiv ℝ (beurlingAhlfors w 1) (φ z)‖ * ‖deriv φ z‖ = _ by rw [hinv]; ring)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      smul_eq_mul]
    rw [norm_mul, Complex.norm_conj]
    have hb := (fderiv ℝ (beurlingAhlfors w 1) (φ z)).le_opNorm (y * deriv φ z)
    rw [norm_mul] at hb
    calc ‖fderiv ℝ (beurlingAhlfors w 1) (φ z) (y * deriv φ z)‖ *
          ‖deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z)))‖
        ≤ ‖fderiv ℝ (beurlingAhlfors w 1) (φ z)‖ * (‖y‖ * ‖deriv φ z‖) *
          ‖deriv (Function.invFunOn ψ A₂) (conj (beurlingAhlfors w 1 (φ z)))‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring
  exact ⟨h1, ⟨hinj, himg', hKc, hbd⟩, h3, h4⟩

/-- The arithmetic of the derivative bound in Lemma 20.1: from `a ≤ 2 I / r` ((20.13′)), `b / J ≤ C / I`
((17.20)), `J ≤ 4 e d` ((20.14′)) and `e ≤ λ r` ((20.16)) follows `a b / d ≤ 8 C λ`. -/
theorem s20l_a1_arith {a b d I J e r Cq lam : ℝ} (hr : 0 < r) (hI : 0 < I) (hJ : 0 < J)
    (hb0 : 0 ≤ b) (hd0 : 0 ≤ d) (ha : a ≤ 2 * I / r) (hb : b / J ≤ Cq / I)
    (hQ : J ≤ 4 * e * d) (he : e ≤ lam * r) : a * b / d ≤ 8 * Cq * lam := by
  have hd : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hQ
      linarith
  have hCq : 0 ≤ Cq / I := le_trans (div_nonneg hb0 hJ.le) hb
  have hCq' : 0 ≤ Cq := by
    have := mul_nonneg hCq hI.le
    rwa [div_mul_cancel₀ _ hI.ne'] at this
  have hb' : b ≤ Cq / I * J := (div_le_iff₀ hJ).1 hb
  rw [div_le_iff₀ hd]
  calc a * b ≤ (2 * I / r) * (Cq / I * J) := mul_le_mul ha hb' hb0 (by positivity)
    _ = 2 * Cq * J / r := by field_simp
    _ ≤ 2 * Cq * (4 * e * d) / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        exact mul_le_mul_of_nonneg_left hQ (by linarith)
    _ ≤ 2 * Cq * (4 * (lam * r) * d) / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_right _ hd0
        linarith
    _ = 8 * Cq * lam * d := by field_simp; ring

/-- **Core of Lemma 20.1** (with the behaviour at `∞`, needed for Lemma 20.3): `K₁ = 8ρ(ρ+1)`, `ρ = λ(K²)`, and
`M = 8 C(ρ) λ(K₁)` (`eq17_20_quasi_isometry`; (20.13′) at `z` with `r = dist(z, ∂A₁)`, (20.14′) at `g z` with the
nearest boundary point `y` of `z`, and (20.16) `|g z - y| ≤ λ(K₁) |z - y|` from `s20l_glue` + `s20l_circle_core`). -/
theorem s20l_reflection_core {K : ℝ} (hK : 1 ≤ K) :
    ∃ K₁ M : ℝ, 1 ≤ K₁ ∧ ∀ (C : Set ExtPlane) (A₁ A₂ : Set ℂ), IsKQuasicircle C K → extInf ∈ C →
      AreComplementaryComponents C (toExt A₁) (toExt A₂) →
      ∃ g : ℂ → ℂ, ContDiffOn ℝ 1 g A₁ ∧ IsPlanarQCReflection A₁ A₂ g K₁ ∧ (∀ z ∈ A₁, ‖fderiv ℝ g z‖ ≤ M) ∧
        Tendsto g (cocompact ℂ ⊓ 𝓟 A₁) (cocompact ℂ) := by
  set ρ := lambdaInv (K * K) with hρdef
  have hρ : 1 ≤ ρ := td_one_le_lambdaInv (by nlinarith)
  obtain ⟨Cq, hCq⟩ := eq17_20_quasi_isometry hρ
  refine ⟨8 * ρ * (ρ + 1), 8 * Cq * lambdaInv (8 * ρ * (ρ + 1)), by nlinarith, ?_⟩
  intro C A₁ A₂ hCK hinf hC
  have hq : IsQuasicircle C := ⟨K, hCK⟩
  obtain ⟨⟨φ, hφ, Φ, hΦ, hΦinf⟩, ψ, hψ, Ψ, hΨ, hΨinf⟩ := s20l_uniformizers hinf hC hq
  obtain ⟨w, hw, hh⟩ := s20l_welding_qs hCK hinf hC hφ hψ hΦ hΨ hΦinf hΨinf
  obtain ⟨hC1, hR, htend, hder⟩ := s20l_ba_reflection hinf hC hq hφ hψ hΦ hΨ hΦinf hΨinf hw hh
  refine ⟨s20l_refl φ ψ A₂ w, hC1, hR, ?_, htend⟩
  set g := s20l_refl φ ψ A₂ w with hgdef
  intro z hz
  obtain ⟨G, hG, hGs, hGu, hGl, -, hsym⟩ := s20l_glue hinf hC hq hR
  have hGinj : InjOn G univ := hG.2.2.1.2.1
  have hGc : ContinuousOn G univ := hG.2.2.1.1
  have hA₁o : IsOpen A₁ := hR.2.2.1.1
  have hlo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  have hA₂o : IsOpen A₂ := by
    rw [← hGl]
    exact isOpen_image_of_continuousOn_injOn hlo (hGc.mono (subset_univ _))
      (hGinj.mono (subset_univ _))
  have hdisj : ∀ p ∈ A₁, p ∉ A₂ := by
    intro p hp1 hp2
    rw [← hGu] at hp1
    rw [← hGl] at hp2
    obtain ⟨a, ha, rfl⟩ := hp1
    obtain ⟨b, hb, hab⟩ := hp2
    have := hGinj (mem_univ _) (mem_univ _) hab
    rw [this] at hb
    have ha' : 0 < a.im := ha
    have hb' : a.im < 0 := hb
    linarith
  have hA₁ne : A₁ ≠ univ := by
    intro h
    have hmI : -I ∈ lowerHalf := by
      show (-I).im < 0
      simp
    have h2 : G (-I) ∈ A₂ := hGl ▸ mem_image_of_mem G hmI
    exact hdisj _ (h ▸ mem_univ _) h2
  -- the nearest boundary point `y` of `z`
  obtain ⟨y, hyfr, hry⟩ := exists_mem_frontier_infDist_compl_eq_dist hz hA₁ne
  set r := infDist z A₁ᶜ with hrdef
  have hr : 0 < r := by
    have hne : (A₁ᶜ).Nonempty := nonempty_compl.2 hA₁ne
    exact (hA₁o.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hz)
  have hball : ball z r ⊆ A₁ := ball_infDist_compl_subset
  have hyA₁ : y ∉ A₁ := by
    intro h
    have := hyfr.2
    rw [hA₁o.interior_eq] at this
    exact this h
  have hyA₂ : y ∉ A₂ := by
    intro h
    obtain ⟨p, hp2, hp1⟩ := mem_closure_iff.1 hyfr.1 A₂ hA₂o h
    exact hdisj p hp1 hp2
  obtain ⟨ξ, -, hξ⟩ : y ∈ G '' univ := hGs.symm ▸ mem_univ y
  have hξim : ξ.im = 0 := by
    rcases lt_trichotomy ξ.im 0 with h | h | h
    · exact absurd (hGl ▸ mem_image_of_mem G (show ξ ∈ lowerHalf from h)) (hξ ▸ hyA₂)
    · exact h
    · exact absurd (hGu ▸ mem_image_of_mem G (show ξ ∈ upperHalf from h)) (hξ ▸ hyA₁)
  have hξre : ((ξ.re : ℝ) : ℂ) = ξ := Complex.ext (by simp) (by simp [hξim])
  -- `z = G ζ`, `ζ ∈ ℍ`
  obtain ⟨ζ, hζ, hGζ⟩ : z ∈ G '' upperHalf := hGu.symm ▸ hz
  have hcirc := (s20l_circle_core hG hGs hsym hζ ξ.re).2
  rw [hξre, hξ, hGζ] at hcirc
  have hzy : ‖z - y‖ = r := by rw [hry, dist_eq_norm]
  rw [hzy] at hcirc
  -- `ψ (g z) = conj (h (φ z))`
  have hu : φ z ∈ upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hz
  have hhu : beurlingAhlfors w 1 (φ z) ∈ upperHalf :=
    (thm17_2_beurling_ahlfors hw).2.2.1 ▸ mem_image_of_mem _ hu
  have hhu' : 0 < (beurlingAhlfors w 1 (φ z)).im := hhu
  have hcl : conj (beurlingAhlfors w 1 (φ z)) ∈ ψ '' A₂ := by
    rw [hψ.2.2]
    show (conj (beurlingAhlfors w 1 (φ z))).im < 0
    rw [conj_im]
    linarith
  have hψg : ψ (g z) = conj (beurlingAhlfors w 1 (φ z)) := Function.invFunOn_eq hcl
  have hgzA₂ : g z ∈ A₂ := hR.2.1 ▸ mem_image_of_mem g hz
  have hQ := s20l_koebe_lower hA₂o hψ hgzA₂ hyA₂
  rw [hψg, conj_im, abs_neg, abs_of_pos hhu'] at hQ
  have hS := s20l_schwarz_upper hA₁o hφ hz hr hball
  have hB := hCq w hw (φ z) hu
  refine (hder z hz).trans ?_
  exact s20l_a1_arith hr hu hhu' (norm_nonneg _) (norm_nonneg _) hS hB hQ
    (by rw [norm_sub_rev]; exact hcirc)

/-- Composing a fractional linear transformation with `w ↦ 1/(w - a)`:
`1/(M(w) - a)` for `M = mobiusExt α β κ δ` is `mobiusExt κ δ (α - aκ) (β - aδ)`. -/
theorem s20l_tp_mobius_comp {α β κ δ : ℂ} (a : ℂ) (h : α * δ - β * κ ≠ 0) (w : ExtPlane) :
    mobiusExt 0 1 1 (-a) (mobiusExt α β κ δ w) = mobiusExt κ δ (α - a * κ) (β - a * δ) w := by
  induction w using OnePoint.rec with
  | infty =>
    by_cases hκ : κ = 0
    · have hα : α ≠ 0 := by
        rintro rfl
        apply h
        simp [hκ]
      rw [mobiusExt_infty_of_eq hκ, mobiusExt_infty_of_ne one_ne_zero,
        mobiusExt_infty_of_ne (by rw [hκ, mul_zero, sub_zero]; exact hα)]
      simp [hκ]
    · rw [mobiusExt_infty_of_ne hκ]
      by_cases hp : α - a * κ = 0
      · rw [mobiusExt_infty_of_eq hp, mobiusExt_coe_of_eq_zero]
        field_simp
        linear_combination hp
      · have hq : 1 * (α / κ) + -a ≠ 0 := by
          intro h0
          apply hp
          field_simp at h0
          linear_combination h0
        rw [mobiusExt_infty_of_ne hp, mobiusExt_coe hq]
        congr 1
        simp only [mobiusFn]
        field_simp
        ring
  | coe z =>
    by_cases hz : κ * z + δ = 0
    · have hn : (α - a * κ) * z + (β - a * δ) ≠ 0 := by
        intro h0
        apply h
        linear_combination α * hz - κ * h0 - a * κ * hz
      rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_infty_of_ne one_ne_zero, mobiusExt_coe hn]
      congr 1
      simp [mobiusFn, hz]
    · have hmul := mobiusFn_mul_den (a := α) (b := β) hz
      rw [mobiusExt_coe hz]
      by_cases hp : (α - a * κ) * z + (β - a * δ) = 0
      · rw [mobiusExt_coe_of_eq_zero hp, mobiusExt_coe_of_eq_zero]
        have h0 : (1 * mobiusFn α β κ δ z + -a) * (κ * z + δ) = 0 := by linear_combination hmul + hp
        exact (mul_eq_zero.1 h0).resolve_right hz
      · have hq : 1 * mobiusFn α β κ δ z + -a ≠ 0 := by
          intro h0
          apply hp
          linear_combination (κ * z + δ) * h0 - hmul
        rw [mobiusExt_coe hp, mobiusExt_coe hq]
        congr 1
        show (0 * mobiusFn α β κ δ z + 1) / (1 * mobiusFn α β κ δ z + -a) =
          (κ * z + δ) / ((α - a * κ) * z + (β - a * δ))
        rw [div_eq_div_iff hq hp]
        linear_combination -hmul

/-- Two covers of one set by disjoint pieces: if `S = U ∪ L` and `S = A₁ ∪ A₂` (both disjoint) and `A₂ = U`, then
`A₁ = L`. -/
theorem s20l_tp_other {S U L A₁ A₂ : Set ExtPlane} (hS : S = U ∪ L) (hUL : Disjoint U L) (hA : S = A₁ ∪ A₂)
    (hA₁₂ : Disjoint A₁ A₂) (h : A₂ = U) : A₁ = L := by
  subst h
  apply Subset.antisymm
  · intro p hp
    have hpS : p ∈ S := hA ▸ Or.inl hp
    rw [hS] at hpS
    exact hpS.resolve_left fun h' => disjoint_left.1 hA₁₂ hp h'
  · intro p hp
    have hpS : p ∈ S := hS ▸ Or.inr hp
    rw [hA] at hpS
    exact hpS.resolve_right fun h' => disjoint_left.1 hUL h' hp

/-- The complementary components of a `K`-quasicircle `C` through `∞`, from a cover of `ℂ̄ ∖ C` by two disjoint
nonempty open sets `A₁, A₂` with `A₂` preconnected: `A₁` and `A₂` are the two components (`ℂ̄ ∖ C = g(ℍ) ∪ g(𝕃)`
by `tp_quasicircle_through_inf`, and `A₂` is one of these, so `A₁` is the other). -/
theorem s20l_tp_components {C : Set ExtPlane} {K : ℝ} (hCK : IsKQuasicircle C K) (hinf : extInf ∈ C)
    {A₁ A₂ : Set ExtPlane} (hcov : Cᶜ = A₁ ∪ A₂) (hdisj : Disjoint A₁ A₂) (hA₁ : IsOpen A₁) (hA₂ : IsOpen A₂)
    (hA₂c : IsPreconnected A₂) (hA₁n : A₁.Nonempty) (hA₂n : A₂.Nonempty) :
    ∃ p₁ ∈ Cᶜ, ∃ p₂ ∈ Cᶜ, A₁ = connectedComponentIn Cᶜ p₁ ∧ A₂ = connectedComponentIn Cᶜ p₂ ∧ A₁ ≠ A₂ := by
  obtain ⟨g, hg, hgs, hC⟩ := tp_quasicircle_through_inf hCK hinf
  obtain ⟨e, rfl⟩ := t1_homeomorph hg hgs
  have hS : Cᶜ = toExt (e '' upperHalf) ∪ toExt (e '' lowerHalf) := by
    rw [hC]
    exact wd_n_compl_eq e.bijective
  have hdisjUL : Disjoint (toExt (e '' upperHalf)) (toExt (e '' lowerHalf)) := by
    refine (disjoint_image_iff OnePoint.coe_injective).2 ((disjoint_image_iff e.injective).2 ?_)
    refine disjoint_left.2 fun z (hz : 0 < z.im) (hz' : z.im < 0) => ?_
    linarith
  have hcU : IsPreconnected (toExt (e '' upperHalf)) :=
    (isConnected_upperHalf.isPreconnected.image _ e.continuous.continuousOn).image _
      OnePoint.continuous_coe.continuousOn
  have hcL : IsPreconnected (toExt (e '' lowerHalf)) :=
    ((((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm).isPreconnected).image _
      e.continuous.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  obtain ⟨p₂, hp₂⟩ := hA₂n
  have hp₂S : p₂ ∈ Cᶜ := hcov ▸ Or.inr hp₂
  have hc₂ : connectedComponentIn Cᶜ p₂ = A₂ :=
    wd_n_component_eq (hcov.trans (union_comm _ _)) hA₂ hA₁ hdisj.symm hA₂c hp₂
  have hA₁c : IsPreconnected A₁ := by
    have hp₂' : p₂ ∈ (toExt (e '' realLine) ∪ {extInf})ᶜ := hC ▸ hp₂S
    rcases wd_n_components e hp₂' with h | h
    · rw [← hC, hc₂] at h
      rw [s20l_tp_other hS hdisjUL hcov hdisj h]
      exact hcL
    · rw [← hC, hc₂] at h
      rw [s20l_tp_other (hS.trans (union_comm _ _)) hdisjUL.symm hcov hdisj h]
      exact hcU
  obtain ⟨p₁, hp₁⟩ := hA₁n
  have hc₁ : connectedComponentIn Cᶜ p₁ = A₁ := wd_n_component_eq hcov hA₁ hA₂ hdisj hA₁c hp₁
  refine ⟨p₁, hcov ▸ Or.inl hp₁, p₂, hp₂S, hc₁.symm, hc₂.symm, fun heq => ?_⟩
  exact disjoint_left.1 hdisj hp₁ (heq ▸ hp₁)

/-- **T** (Möbius transport of a bounded quasidisc): for a bounded `K`-quasidisc `D` there is `a ∈ ∂D` such that
`γ(z) = 1/(z - a)` sends `∂D` to a `K`-quasicircle `C` through `∞` whose complementary components are
`γ(ℂ ∖ D̄) ∪ {0}` (`0 = γ(∞)`) and `γ(D)`. -/
theorem s20l_mobius_transport {D : Set ℂ} {K : ℝ} (hD : IsKQuasidisc D K) (hb : Bornology.IsBounded D) :
    ∃ a ∈ frontier D, ∃ C : Set ExtPlane, IsKQuasicircle C K ∧ extInf ∈ C ∧
      AreComplementaryComponents C (toExt (insert 0 ((fun z => (z - a)⁻¹) '' (closure D)ᶜ)))
        (toExt ((fun z => (z - a)⁻¹) '' D)) := by
  obtain ⟨⟨hDo, hDc, hJ⟩, hq⟩ := hD
  obtain ⟨a, ha⟩ : (frontier D).Nonempty :=
    nonempty_frontier_iff.2 ⟨hDc.nonempty, fun h => NormedSpace.unbounded_univ ℂ ℂ (h ▸ hb)⟩
  have haD : a ∉ D := fun h => (hDo.inter_frontier_eq.subset ⟨h, ha⟩ : a ∈ (∅ : Set ℂ))
  have hacl : a ∈ closure D := frontier_subset_closure ha
  have hdet : (0 : ℂ) * (-a) - 1 * 1 ≠ 0 := by norm_num
  have hγbij : Function.Bijective (mobiusExt 0 1 1 (-a)) := (mobiusHomeomorph 0 1 1 (-a) hdet).bijective
  have hγinj : Function.Injective (mobiusExt 0 1 1 (-a)) := hγbij.1
  have hγinf : mobiusExt 0 1 1 (-a) extInf = ((0 : ℂ) : ExtPlane) := by
    rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
  have hγa : mobiusExt 0 1 1 (-a) (a : ExtPlane) = extInf := mobiusExt_coe_of_eq_zero (by ring)
  have hγz : ∀ z : ℂ, z ≠ a → mobiusExt 0 1 1 (-a) (z : ExtPlane) = (((z - a)⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    have hz' : (1 : ℂ) * z + -a ≠ 0 := by
      rw [one_mul, ← sub_eq_add_neg]
      exact sub_ne_zero.mpr hz
    rw [mobiusExt_coe hz']
    congr 1
    simp only [mobiusFn]
    ring
  have hγimg : ∀ S : Set ℂ, a ∉ S →
      mobiusExt 0 1 1 (-a) '' toExt S = toExt ((fun z => (z - a)⁻¹) '' S) := by
    intro S haS
    unfold toExt
    rw [image_image, image_image]
    exact image_congr fun z hz => hγz z fun h => haS (h ▸ hz)
  have hopenE : IsOpen (toExt D) := OnePoint.isOpen_image_coe.2 hDo
  have hclD : closure (toExt D) = toExt (closure D) := closure_toExt_of_isBounded hb
  have hA₂ : mobiusExt 0 1 1 (-a) '' toExt D = toExt ((fun z => (z - a)⁻¹) '' D) := hγimg D haD
  have hA₁ : mobiusExt 0 1 1 (-a) '' (closure (toExt D))ᶜ =
      toExt (insert 0 ((fun z => (z - a)⁻¹) '' (closure D)ᶜ)) := by
    have h1 := scExt_compl_toExt_union_infty (closure D)ᶜ
    rw [compl_compl] at h1
    rw [hclD, ← h1, compl_compl, image_union, image_singleton, hγinf,
      hγimg _ (notMem_compl_iff.2 hacl), union_singleton]
    unfold toExt
    rw [image_insert_eq]
  set C := mobiusExt 0 1 1 (-a) '' frontier (toExt D) with hCdef
  have hCK : IsKQuasicircle C K := by
    obtain ⟨f, hf, hfs, M, ⟨α, β, κ, δ, hdetM, rfl⟩, hC0⟩ := hq
    refine ⟨f, hf, hfs, mobiusExt κ δ (α - a * κ) (β - a * δ), ⟨κ, δ, α - a * κ, β - a * δ, ?_, rfl⟩, ?_⟩
    · intro h0
      apply hdetM
      linear_combination -h0
    · rw [hCdef, hC0, image_image]
      exact image_congr fun w _ => s20l_tp_mobius_comp a hdetM w
  have hinf : extInf ∈ C := ⟨a, by rw [frontier_toExt_of_isBounded hb hDo]; exact ⟨a, ha, rfl⟩, hγa⟩
  have hJC : IsJordanCurve C := by
    obtain ⟨p, hpc, hpi, hpr⟩ := hJ
    exact ⟨mobiusExt 0 1 1 (-a) ∘ p, (continuous_mobiusExt hdet).comp hpc, hγinj.comp hpi,
      by rw [range_comp, hpr]⟩
  refine ⟨a, ha, C, hCK, hinf, hJC, ?_⟩
  rw [← hA₁, ← hA₂]
  refine s20l_tp_components hCK hinf ?_ ((disjoint_image_iff hγinj).2
    ((disjoint_compl_left (a := closure (toExt D))).mono_right subset_closure))
    ((mobiusHomeomorph 0 1 1 (-a) hdet).isOpenMap _ isClosed_closure.isOpen_compl)
    ((mobiusHomeomorph 0 1 1 (-a) hdet).isOpenMap _ hopenE)
    ((hDc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).image _
      (continuous_mobiusExt hdet).continuousOn)
    ⟨_, mem_image_of_mem _ (show extInf ∈ (closure (toExt D))ᶜ by
      rw [hclD]; exact wd_n_infty_notMem_toExt)⟩
    ((hDc.nonempty.image _).image _)
  rw [hCdef, ← image_compl_eq hγbij, ← image_union,
    hopenE.frontier_eq, sdiff_eq, compl_inter, compl_compl]

/-- The image of `D` under `z ↦ 1/(z - a)`, `a ∉ D`, is the set of `u ≠ 0` with `a + 1/u ∈ D`. -/
theorem s20l_tp_image_inv_eq {D : Set ℂ} {a : ℂ} (ha : a ∉ D) :
    (fun z => (z - a)⁻¹) '' D = {0}ᶜ ∩ (fun u : ℂ => a + u⁻¹) ⁻¹' D := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hz)
    refine ⟨inv_ne_zero hza, ?_⟩
    show a + (z - a)⁻¹⁻¹ ∈ D
    rw [inv_inv, add_sub_cancel]
    exact hz
  · rintro ⟨hu, hD⟩
    refine ⟨a + u⁻¹, hD, ?_⟩
    show (a + u⁻¹ - a)⁻¹ = u
    rw [add_sub_cancel_left, inv_inv]

/-- **P** (Möbius invariance of the Poincaré density): for `γ(z) = 1/(z - a)`, `a ∉ D`,
`η_{γ(D)}(γ w) |γ'(w)| = η_D(w)` (`f ∘ γ⁻¹` is a conformal map of `γ(D)` onto `Δ`; `|γ'(w)| = |w - a|⁻²`). -/
theorem s20l_density_mobius {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} (hf : IsConformalOnto f D unitDisc) {a : ℂ}
    (ha : a ∉ D) {w : ℂ} (hw : w ∈ D) :
    poincareDensity ((fun z => (z - a)⁻¹) '' D) (w - a)⁻¹ * ‖(w - a)⁻¹‖ ^ 2 = poincareDensity D w := by
  have hwa : w - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hw)
  have himg := s20l_tp_image_inv_eq ha
  have hopen : IsOpen ((fun z => (z - a)⁻¹) '' D) := by
    rw [himg]
    exact (continuousOn_const.add continuousOn_inv₀).isOpen_inter_preimage isOpen_compl_singleton hD
  have hback : (fun u : ℂ => a + u⁻¹) '' ((fun z => (z - a)⁻¹) '' D) = D := by
    rw [image_image]
    conv_rhs => rw [← image_id D]
    refine image_congr fun z _ => ?_
    show a + (z - a)⁻¹⁻¹ = z
    rw [inv_inv, add_sub_cancel]
  have hF : IsConformalOnto (fun u => f (a + u⁻¹)) ((fun z => (z - a)⁻¹) '' D) unitDisc := by
    refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_, ?_⟩
    · rw [himg] at hu
      have hu0 : u ≠ 0 := hu.1
      exact ((hf.1.differentiableAt (hD.mem_nhds hu.2)).comp u
        ((differentiableAt_inv hu0).const_add a)).differentiableWithinAt
    · rw [himg] at hu hv
      have h1 := hf.2.1 hu.2 hv.2 huv
      exact inv_injective (add_left_cancel h1)
    · calc (fun u => f (a + u⁻¹)) '' ((fun z => (z - a)⁻¹) '' D)
          = f '' ((fun u : ℂ => a + u⁻¹) '' ((fun z => (z - a)⁻¹) '' D)) := (image_image f _ _).symm
        _ = unitDisc := by rw [hback, hf.2.2]
  have hmem : (w - a)⁻¹ ∈ (fun z => (z - a)⁻¹) '' D := mem_image_of_mem _ hw
  have hu0 : a + ((w - a)⁻¹)⁻¹ = w := by rw [inv_inv, add_sub_cancel]
  have hfd : HasDerivAt f (deriv f w) (a + ((w - a)⁻¹)⁻¹) := by
    rw [hu0]
    exact (hf.1.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hg : HasDerivAt (fun u : ℂ => a + u⁻¹) (-(((w - a)⁻¹) ^ 2)⁻¹) (w - a)⁻¹ :=
    (hasDerivAt_inv (inv_ne_zero hwa)).const_add a
  have hder : deriv (fun u => f (a + u⁻¹)) (w - a)⁻¹ = deriv f w * -(((w - a)⁻¹) ^ 2)⁻¹ :=
    (hfd.comp ((w - a)⁻¹) hg).deriv
  rw [(poincareDensity_well_defined hopen hF hF hmem).2, (poincareDensity_well_defined hD hf hf hw).2,
    hder, hu0]
  have hn : ‖w - a‖ ≠ 0 := norm_ne_zero_iff.mpr hwa
  rw [norm_mul, norm_neg, norm_inv, norm_pow, norm_inv]
  field_simp

/-- **Lemma 20.1**: for a `K`-quasicircle `C` through `∞` with complementary components `A₁, A₂`,
there is a `C¹` `K₁`-q.c. reflection `g : A₁ → A₂` with `|dg(z)| ≤ M(K) |dz|`, where `K₁` and
`M(K)` depend only on `K`. -/
theorem lemma20_1 {K : ℝ} (hK : 1 ≤ K) :
    ∃ K₁ M : ℝ, ∀ (C : Set ExtPlane) (A₁ A₂ : Set ℂ), IsKQuasicircle C K → extInf ∈ C →
      AreComplementaryComponents C (toExt A₁) (toExt A₂) →
      ∃ g : ℂ → ℂ, ContDiffOn ℝ 1 g A₁ ∧ IsPlanarQCReflection A₁ A₂ g K₁ ∧
        ∀ z ∈ A₁, ‖fderiv ℝ g z‖ ≤ M := by
  obtain ⟨K₁, M, -, hcore⟩ := s20l_reflection_core hK
  refine ⟨K₁, M, fun C A₁ A₂ hCK hinf hC => ?_⟩
  obtain ⟨g, hg1, hg2, hg3, -⟩ := hcore C A₁ A₂ hCK hinf hC
  exact ⟨g, hg1, hg2, hg3⟩

/-- A conformal map `ψ : A → 𝕃` gives the conformal map `cayley ∘ (-ψ) : A → Δ`. -/
theorem s20l_a2_disc_of_lower {A : Set ℂ} {ψ : ℂ → ℂ} (hψ : IsConformalOnto ψ A lowerHalf) :
    IsConformalOnto (cayley ∘ fun v => -ψ v) A unitDisc := by
  refine isConformalOnto_cayley.comp ⟨hψ.1.neg, fun a ha b hb hab => hψ.2.1 ha hb (neg_injective hab), ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h' : (ψ u).im < 0 := hψ.mapsTo hu
    show 0 < (-ψ u).im
    rw [neg_im]
    linarith
  · intro hv
    have hv0 : 0 < v.im := hv
    have hv' : -v ∈ ψ '' A := by
      rw [hψ.2.2]
      show (-v).im < 0
      rw [neg_im]
      linarith
    obtain ⟨u, hu, hvu⟩ := hv'
    exact ⟨u, hu, by simp [hvu]⟩

/-- The Poincaré density of an open set `A` with a conformal map `φ : A → Δ` is positive on `A`. -/
theorem s20l_a2_density_pos {A : Set ℂ} (hA : IsOpen A) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ A unitDisc)
    {w : ℂ} (hw : w ∈ A) : 0 < poincareDensity A w := by
  rw [(poincareDensity_well_defined hA hφ hφ hw).2]
  have h1 : ‖φ w‖ < 1 := mem_ball_zero_iff.1 (show φ w ∈ unitDisc from hφ.mapsTo hw)
  have h2 : deriv φ w ≠ 0 := deriv_ne_zero_of_injOn hA hφ.1 hφ.2.1 hw
  have h3 : 0 < 1 - ‖φ w‖ ^ 2 := by nlinarith [norm_nonneg (φ w)]
  have h4 : 0 < ‖deriv φ w‖ := norm_pos_iff.2 h2
  exact div_pos (mul_pos two_pos h4) h3

/-- The core of Lemma 20.2 for the glued map `G` of `s20l_glue`: with `z = G ζ`, the nearest boundary point
`y = G x` of `g z` in `A₂` gives `|g z - z| ≤ (1 + λ(K₁)) d` (`s20l_circle_core`), `d = dist(g z, ∂A₂)`, and
`η_{A₂}(g z) ≤ 2/d` (`s20l_density_le`). -/
theorem s20l_a2_core {G g ψ : ℂ → ℂ} {K₁ : ℝ} {A₁ A₂ : Set ℂ} (hG : IsKQC G univ K₁)
    (hGs : G '' univ = univ) (hGU : G '' upperHalf = A₁) (hGL : G '' lowerHalf = A₂)
    (hsym : ∀ ζ ∈ upperHalf, G (conj ζ) = g (G ζ)) (hψ : IsConformalOnto ψ A₂ lowerHalf) {z : ℂ}
    (hz : z ∈ A₁) :
    ‖g z - z‖ ≤ 2 * (1 + lambdaInv K₁) / poincareDensity A₂ (g z) := by
  have hGc : ContinuousOn G univ := hG.2.2.1.1
  have hGi : InjOn G univ := hG.2.2.1.2.1
  have hA₁o : IsOpen A₁ := hGU ▸ isOpen_image_of_continuousOn_injOn isOpen_upperHalf
    (hGc.mono (subset_univ _)) (hGi.mono (subset_univ _))
  have hA₂o : IsOpen A₂ := hGL ▸ isOpen_image_of_continuousOn_injOn
    (isOpen_lt continuous_im continuous_const) (hGc.mono (subset_univ _)) (hGi.mono (subset_univ _))
  have hlow : ∀ u, G u ∈ A₂ → u ∈ lowerHalf := by
    intro u hu
    rw [← hGL] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    rw [hGi (mem_univ v) (mem_univ u) hvu] at hv
    exact hv
  have hdisj : ∀ v ∈ A₁, v ∉ A₂ := by
    intro v hv hv2
    rw [← hGU] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    have h1 : 0 < v'.im := hv'
    have h2 : v'.im < 0 := hlow v' hv2
    linarith
  rw [← hGU] at hz
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hζ0 : 0 < ζ.im := hζ
  have hconjL : conj ζ ∈ lowerHalf := by
    show (conj ζ).im < 0
    rw [conj_im]
    linarith
  have hw : g (G ζ) ∈ A₂ := by
    rw [← hsym ζ hζ, ← hGL]
    exact mem_image_of_mem G hconjL
  have hne : A₂ ≠ univ := fun h => hdisj (G ζ) (hGU ▸ mem_image_of_mem G hζ) (h ▸ mem_univ _)
  obtain ⟨y, hyfr, hyd⟩ := exists_mem_frontier_infDist_compl_eq_dist hw hne
  have hdpos : 0 < infDist (g (G ζ)) A₂ᶜ := by
    refine (infDist_pos_iff_notMem_closure (nonempty_compl.2 hne)).1 ?_
    rw [hA₂o.isClosed_compl.closure_eq]
    exact fun h => h hw
  have hball : ball (g (G ζ)) (infDist (g (G ζ)) A₂ᶜ) ⊆ A₂ := ball_infDist_compl_subset
  obtain ⟨u, -, rfl⟩ : y ∈ G '' univ := by
    rw [hGs]
    exact mem_univ y
  have hu0 : u.im = 0 := by
    rcases lt_trichotomy u.im 0 with h | h | h
    · exfalso
      have hu2 : G u ∈ A₂ := hGL ▸ mem_image_of_mem G (show u ∈ lowerHalf from h)
      exact hyfr.2 (hA₂o.interior_eq.symm ▸ hu2)
    · exact h
    · exfalso
      have hu1 : G u ∈ A₁ := hGU ▸ mem_image_of_mem G (show u ∈ upperHalf from h)
      obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.1 hyfr.1 A₁ hA₁o hu1
      exact hdisj v hv1 hv2
  have hux : ((u.re : ℝ) : ℂ) = u := Complex.ext (by simp) (by simp [hu0])
  have hcore := (s20l_circle_core hG hGs hsym hζ u.re).1
  rw [hux] at hcore
  set d := infDist (g (G ζ)) A₂ᶜ
  set l := lambdaInv K₁
  have hyd' : ‖g (G ζ) - G u‖ = d := by rw [hyd, dist_eq_norm]
  rw [hyd'] at hcore
  have htri : ‖g (G ζ) - G ζ‖ ≤ ‖g (G ζ) - G u‖ + ‖G u - G ζ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [hyd', norm_sub_rev (G u)] at htri
  have hl0 : 0 ≤ l := by
    by_contra hneg
    push Not at hneg
    have : l * d < 0 := mul_neg_of_neg_of_pos hneg hdpos
    linarith [norm_nonneg (G ζ - G u)]
  have hbound : ‖g (G ζ) - G ζ‖ ≤ (1 + l) * d := by nlinarith
  have hf := s20l_a2_disc_of_lower hψ
  have hηle := s20l_density_le hA₂o hf hw hdpos hball
  have hηpos := s20l_a2_density_pos hA₂o hf hw
  set η := poincareDensity A₂ (g (G ζ))
  have hηd : η * d ≤ 2 := (le_div_iff₀ hdpos).1 hηle
  rw [le_div_iff₀ hηpos]
  have h1 := mul_le_mul_of_nonneg_right hbound hηpos.le
  have h2 := mul_le_mul_of_nonneg_left hηd (show 0 ≤ 1 + l by linarith)
  nlinarith

/-- **Lemma 20.2**: for a `K₁`-q.c. reflection `g : A₁ → A₂` in a `K`-quasicircle through `∞`,
`|g(z) - z| ≤ M̃ / η_{A₂}(g(z))`, with `M̃` depending only on `K₁`. -/
theorem lemma20_2 {K₁ : ℝ} (hK₁ : 1 ≤ K₁) :
    ∃ M' : ℝ, ∀ (C : Set ExtPlane) (A₁ A₂ : Set ℂ) (K : ℝ) (g : ℂ → ℂ), IsKQuasicircle C K →
      extInf ∈ C → AreComplementaryComponents C (toExt A₁) (toExt A₂) →
      IsPlanarQCReflection A₁ A₂ g K₁ → ∀ z ∈ A₁, ‖g z - z‖ ≤ M' / poincareDensity A₂ (g z) := by
  have _hK₁ := hK₁
  refine ⟨2 * (1 + lambdaInv K₁), ?_⟩
  intro C A₁ A₂ K g hCK hinf hC hg z hz
  have hq : IsQuasicircle C := ⟨K, hCK⟩
  obtain ⟨G, hG, hGs, hGU, hGL, -, hsym⟩ := s20l_glue hinf hC hq hg
  obtain ⟨-, ψ, hψ, -⟩ := s20l_uniformizers hinf hC hq
  exact s20l_a2_core hG hGs hGU hGL hsym hψ hz

/-- Chain rule bound for the conjugated map `z ↦ a + 1/g̃(1/(z - a))`:
`|dg(z)| ≤ |g̃(ζ)|⁻² |dg̃(ζ)| |ζ|²` at `ζ = 1/(z - a)`. -/
theorem s20l_a3_fderiv_le {gt : ℂ → ℂ} {a z : ℂ} (hz : z ≠ a)
    (hd : DifferentiableAt ℝ gt (z - a)⁻¹) (hne : gt (z - a)⁻¹ ≠ 0) :
    ‖fderiv ℝ (fun w => a + (gt (w - a)⁻¹)⁻¹) z‖ ≤
      ‖(gt (z - a)⁻¹)⁻¹‖ ^ 2 * ‖fderiv ℝ gt (z - a)⁻¹‖ * ‖(z - a)⁻¹‖ ^ 2 := by
  have hza : z - a ≠ 0 := sub_ne_zero.2 hz
  have h1 : HasDerivAt (fun w : ℂ => (w - a)⁻¹) (-1 / (z - a) ^ 2) z :=
    ((hasDerivAt_id' z).sub_const a).fun_inv hza
  have h2 : HasDerivAt (fun y : ℂ => y⁻¹) (-((gt (z - a)⁻¹) ^ 2)⁻¹) (gt (z - a)⁻¹) :=
    hasDerivAt_inv hne
  have H := ((h2.hasFDerivAt.restrictScalars ℝ).comp z
    (hd.hasFDerivAt.comp z (h1.hasFDerivAt.restrictScalars ℝ))).const_add a
  have H' : HasFDerivAt (fun w => a + (gt (w - a)⁻¹)⁻¹) _ z := H
  rw [H'.fderiv]
  refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))).trans (le_of_eq ?_)
  rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_restrictScalars,
    ContinuousLinearMap.norm_toSpanSingleton, ContinuousLinearMap.norm_toSpanSingleton]
  simp only [norm_neg, norm_inv, norm_div, norm_one, norm_pow]
  ring

/-- `a + 1/u - z = (ζ - u)/(u ζ)` for `ζ = 1/(z - a)`: `|g(z) - z| = |u - ζ| |u|⁻¹ |z - a|`. -/
theorem s20l_a3_norm_sub {a z u : ℂ} (hu : u ≠ 0) (hz : z ≠ a) :
    ‖a + u⁻¹ - z‖ = ‖u - (z - a)⁻¹‖ * ‖u⁻¹‖ * ‖z - a‖ := by
  have hza : z - a ≠ 0 := sub_ne_zero.2 hz
  rw [show a + u⁻¹ - z = -((u - (z - a)⁻¹) * u⁻¹ * (z - a)) by field_simp; ring, norm_neg,
    norm_mul, norm_mul]

/-- The real inequality behind (20.18): with `‖g z - z‖ = t r⁻¹ s`, `‖dg z‖ ≤ r⁻² m s⁻²`, `η_D(g z) = η_A r²`,
`t ≤ M'/η_A` and `m ≤ M`, the product `‖g z - z‖² ‖dg z‖ η_D(g z)²` is at most `M'² M`. -/
theorem s20l_a3_real {t m ηA r s d e M M' : ℝ} (ht0 : 0 ≤ t) (hηA : 0 < ηA) (ht : t ≤ M' / ηA)
    (hm0 : 0 ≤ m) (hm : m ≤ M) (hr : 0 < r) (hs : 0 < s) (hd : d = t * r⁻¹ * s)
    (he : e ≤ r⁻¹ ^ 2 * m * s⁻¹ ^ 2) :
    d ^ 2 * e * (ηA * r ^ 2) ^ 2 ≤ M' ^ 2 * M := by
  have htη : t * ηA ≤ M' := (le_div_iff₀ hηA).1 ht
  have h1 : (t * ηA) ^ 2 ≤ M' ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 hηA.le) htη 2
  calc d ^ 2 * e * (ηA * r ^ 2) ^ 2 ≤ d ^ 2 * (r⁻¹ ^ 2 * m * s⁻¹ ^ 2) * (ηA * r ^ 2) ^ 2 := by gcongr
    _ = (t * ηA) ^ 2 * m := by rw [hd]; field_simp
    _ ≤ M' ^ 2 * M := mul_le_mul h1 hm hm0 (sq_nonneg _)

/-- Assembling (20.18) in `ℝ≥0∞`: `S X ≤ c N` from `S/η² ≤ N` and `X η² ≤ c`. -/
theorem s20l_a3_ennreal {S X η c : ℝ} {N : ℝ≥0∞} (hS0 : 0 ≤ S) (hη : 0 < η)
    (hSN : ENNReal.ofReal (S / η ^ 2) ≤ N) (hX : X * η ^ 2 ≤ c) :
    ENNReal.ofReal (S * X) ≤ ENNReal.ofReal c * N := by
  have heq : S * X = S / η ^ 2 * (X * η ^ 2) := by field_simp
  have hq : 0 ≤ S / η ^ 2 := div_nonneg hS0 (sq_nonneg _)
  calc ENNReal.ofReal (S * X) = ENNReal.ofReal (S / η ^ 2 * (X * η ^ 2)) := by rw [heq]
    _ ≤ ENNReal.ofReal (S / η ^ 2 * c) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hX hq)
    _ = ENNReal.ofReal (S / η ^ 2) * ENNReal.ofReal c := ENNReal.ofReal_mul hq
    _ ≤ N * ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal c * N := mul_comm _ _

/-- **Lemma 20.3** (20.18): for a bounded `K`-quasidisc `D` there is a `C¹` quasiconformal
reflection `g` of the exterior `A₁ = ℂ ∖ D̄` onto `D` such that for every locally univalent
meromorphic `f` in `D`, `|S_f(g(z))| |g(z) - z|² |dg(z)| ≤ c(K) ‖S_f‖_D |dz|`, where `c(K)`
depends only on `K`.

In `ℂ` the reflection maps the exterior onto `D ∖ {p}`, `p = g(∞)` in the book's picture on `ℂ̄`
(corrected 2026-09-25: a homeomorphism of the doubly connected exterior onto the simply connected `D`
cannot exist). -/
theorem lemma20_3 {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : Set ℂ, IsKQuasidisc D K → Bornology.IsBounded D →
      ∃ (g : ℂ → ℂ) (K₁ : ℝ), ContDiffOn ℝ 1 g (closure D)ᶜ ∧
        (∃ p ∈ D, IsPlanarQCReflection (closure D)ᶜ (D \ {p}) g K₁) ∧
        ∀ f : ℂ → ℂ, IsLocUnivMero f D → ∀ z ∈ (closure D)ᶜ,
          ENNReal.ofReal (‖schwarzian f (g z)‖ * ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖) ≤
            ENNReal.ofReal c * schwarzianNorm f D := by
  obtain ⟨K₁, M, hK₁, hcore⟩ := s20l_reflection_core hK
  obtain ⟨M', hl2⟩ := lemma20_2 hK₁
  refine ⟨max (M' ^ 2 * M) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun D hD hb => ?_⟩
  obtain ⟨a, haD, C, hCK, hinf, hCC⟩ := s20l_mobius_transport hD hb
  obtain ⟨gt, hC1, hR, hdg, htend⟩ := hcore C _ _ hCK hinf hCC
  have hl2' := hl2 C _ _ K gt hCK hinf hCC hR
  set U := (fun z => (z - a)⁻¹) '' (closure D)ᶜ with hUdef
  set A₂ := (fun z => (z - a)⁻¹) '' D with hA₂def
  -- basic facts about `γ z = 1/(z - a)`
  have hDo : IsOpen D := hD.1.1
  have haD' : a ∉ D := fun h => haD.2 (interior_maximal subset_rfl hDo h)
  have hDco : IsOpen (closure D)ᶜ := isClosed_closure.isOpen_compl
  have hneDc : ∀ z ∈ (closure D)ᶜ, z ≠ a := fun z hz h => hz (h ▸ frontier_subset_closure haD)
  have hneD : ∀ z ∈ D, z ≠ a := fun z hz h => haD' (h ▸ hz)
  have hγ0 : ∀ z : ℂ, z ≠ a → (z - a)⁻¹ ≠ 0 := fun z hz => inv_ne_zero (sub_ne_zero.2 hz)
  have hγinj : ∀ z w : ℂ, (z - a)⁻¹ = (w - a)⁻¹ → z = w := fun z w h =>
    sub_left_injective (inv_inj.1 h)
  have hγinv : ∀ w : ℂ, a + ((w - a)⁻¹)⁻¹ = w := fun w => by rw [inv_inv]; ring
  have hA₁o : IsOpen (insert 0 U) := hR.2.2.1.1
  have hUA : insert 0 U \ {0} = U := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      exact hw.resolve_left hw0
    · intro hw
      refine ⟨mem_insert_of_mem _ hw, ?_⟩
      obtain ⟨z, hz, rfl⟩ := hw
      exact hγ0 z (hneDc z hz)
  have hUo : IsOpen U := hUA ▸ hA₁o.sdiff isClosed_singleton
  have hmemA₁ : ∀ z ∈ (closure D)ᶜ, (z - a)⁻¹ ∈ insert 0 U := fun z hz =>
    mem_insert_of_mem _ (mem_image_of_mem _ hz)
  have himg : gt '' insert 0 U = A₂ := hR.2.1
  have hgtA₂ : ∀ ζ ∈ insert 0 U, gt ζ ∈ A₂ := fun ζ hζ => himg ▸ mem_image_of_mem gt hζ
  have hA₂ : ∀ u ∈ A₂, u ≠ 0 ∧ a + u⁻¹ ∈ D := by
    rintro _ ⟨d, hd, rfl⟩
    show (d - a)⁻¹ ≠ 0 ∧ a + ((d - a)⁻¹)⁻¹ ∈ D
    exact ⟨hγ0 d (hneD d hd), by rw [hγinv]; exact hd⟩
  have hinj : InjOn gt (insert 0 U) := hR.1
  have hC1z : ∀ z ∈ (closure D)ᶜ, ContDiffAt ℝ 1 gt (z - a)⁻¹ := fun z hz =>
    hC1.contDiffAt (hA₁o.mem_nhds (hmemA₁ z hz))
  refine ⟨fun z => a + (gt (z - a)⁻¹)⁻¹, K₁, ?_,
    ⟨a + (gt 0)⁻¹, (hA₂ _ (hgtA₂ 0 (mem_insert _ _))).2, ?_⟩, ?_⟩
  · -- `C¹`
    intro z hz
    have h1 : ContDiffAt ℝ 1 (fun w : ℂ => (w - a)⁻¹) z :=
      (contDiffAt_id.sub contDiffAt_const).fun_inv (sub_ne_zero.2 (hneDc z hz))
    have h3 := ((hC1z z hz).comp z h1).fun_inv (hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).1
    exact (contDiffAt_const.add h3).contDiffWithinAt
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- injective
      intro z₁ hz₁ z₂ hz₂ h
      have h' : gt (z₁ - a)⁻¹ = gt (z₂ - a)⁻¹ := inv_inj.1 (add_left_cancel h)
      exact hγinj z₁ z₂ (hinj (hmemA₁ z₁ hz₁) (hmemA₁ z₂ hz₂) h')
    · -- image `D ∖ {p}`
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).2, fun h => ?_⟩
        have h' : gt (z - a)⁻¹ = gt 0 := inv_inj.1 (add_left_cancel h)
        exact hγ0 z (hneDc z hz) (hinj (hmemA₁ z hz) (mem_insert _ _) h')
      · rintro ⟨hw, hwp⟩
        have hwA₂ : (w - a)⁻¹ ∈ A₂ := mem_image_of_mem _ hw
        rw [← himg] at hwA₂
        obtain ⟨ζ, hζ, hζw⟩ := hwA₂
        rcases hζ with rfl | ⟨z, hz, rfl⟩
        · exact absurd (show w = a + (gt 0)⁻¹ by rw [hζw, hγinv]) hwp
        · have hζw' : gt (z - a)⁻¹ = (w - a)⁻¹ := hζw
          refine ⟨z, hz, ?_⟩
          show a + (gt (z - a)⁻¹)⁻¹ = w
          rw [hζw', hγinv]
    · -- quasiconformality of `conj ∘ g`
      have hγc : IsConformalOnto (fun z : ℂ => (z - a)⁻¹) (closure D)ᶜ U :=
        ⟨fun z hz => (((hasDerivAt_id' z).sub_const a).fun_inv
          (sub_ne_zero.2 (hneDc z hz))).differentiableAt.differentiableWithinAt,
         fun z₁ _ z₂ _ h => hγinj z₁ z₂ h, rfl⟩
      have hq1 : IsKQC (fun z : ℂ => (z - a)⁻¹) (closure D)ᶜ 1 := isKQC_one_of_conformal hDco hγc
      have hq2 : IsKQC (fun z => conj (gt z)) U K₁ :=
        ac_t_isKQC_restrict hR.2.2.1 hUo (subset_insert _ _)
      have hh₂c : IsConformalOnto (fun u : ℂ => conj a + u⁻¹) {0}ᶜ
          ((fun u : ℂ => conj a + u⁻¹) '' {0}ᶜ) :=
        ⟨fun u hu => ((hasDerivAt_inv hu).const_add (conj a)).differentiableAt.differentiableWithinAt,
         fun u₁ _ u₂ _ h => inv_inj.1 (add_left_cancel h), rfl⟩
      have hq3 : IsKQC (fun u : ℂ => conj a + u⁻¹) {0}ᶜ 1 :=
        isKQC_one_of_conformal isOpen_compl_singleton hh₂c
      have s1 := thm7_1_comp hq1 hq2 (subset_refl _)
      have s2 := thm7_1_comp s1 hq3 (by
        rintro _ ⟨z, hz, rfl⟩
        exact (map_ne_zero (starRingEnd ℂ)).2 (hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).1)
      rw [one_mul, mul_one] at s2
      refine ad_isKQC_congr s2 fun z _ => ?_
      show conj (a + (gt (z - a)⁻¹)⁻¹) = conj a + (conj (gt (z - a)⁻¹))⁻¹
      rw [map_add, map_inv₀]
    · -- boundary behaviour
      rintro q ⟨hq1, -⟩
      have hqcl : q ∈ closure (closure D)ᶜ := frontier_subset_closure hq1
      rw [frontier_compl] at hq1
      have hqD : q ∈ frontier D := frontier_closure_subset hq1
      have hqnD : q ∉ D := fun h => hqD.2 (interior_maximal subset_rfl hDo h)
      by_cases hqa : q = a
      · rw [hqa]
        have hsub : Tendsto (fun z : ℂ => z - a) (𝓝[(closure D)ᶜ] a) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
            sub_ne_zero.2 (hneDc z hz)⟩
          have : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 (a - a)) := tendsto_id.sub_const a
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        have hγt : Tendsto (fun z : ℂ => (z - a)⁻¹) (𝓝[(closure D)ᶜ] a)
            (Bornology.cobounded ℂ ⊓ 𝓟 (insert 0 U)) :=
          tendsto_inf.2 ⟨tendsto_inv₀_nhdsNE_zero.comp hsub,
            tendsto_principal.2 (eventually_nhdsWithin_of_forall hmemA₁)⟩
        have htend' : Tendsto gt (Bornology.cobounded ℂ ⊓ 𝓟 (insert 0 U))
            (Bornology.cobounded ℂ) := by
          rw [Metric.cobounded_eq_cocompact]
          exact htend
        have h3 := (tendsto_inv₀_cobounded.comp (htend'.comp hγt)).const_add a
        rw [add_zero] at h3
        exact h3
      · have hqa' : q - a ≠ 0 := sub_ne_zero.2 hqa
        have hcont : ContinuousAt (fun z : ℂ => (z - a)⁻¹) q :=
          (continuousAt_id.sub continuousAt_const).inv₀ hqa'
        have hfr : (q - a)⁻¹ ∈ frontier (insert 0 U) ∩ frontier A₂ := by
          refine ⟨⟨closure_mono (subset_insert _ _) (mem_closure_image hcont hqcl), fun h => ?_⟩,
            ⟨mem_closure_image hcont (frontier_subset_closure hqD), fun h => ?_⟩⟩
          · rcases interior_subset h with h0 | ⟨z, hz, hzq⟩
            · exact hγ0 q hqa h0
            · have hzq' : z = q := hγinj z q hzq
              rw [hzq'] at hz
              exact hz hqD.1
          · obtain ⟨d, hd, hdq⟩ := interior_subset h
            have hdq' : d = q := hγinj d q hdq
            rw [hdq'] at hd
            exact hqnD hd
        have h1 := hR.2.2.2 _ hfr
        have h2 : Tendsto (fun z : ℂ => (z - a)⁻¹) (𝓝[(closure D)ᶜ] q) (𝓝[insert 0 U] (q - a)⁻¹) :=
          tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds,
            eventually_nhdsWithin_of_forall hmemA₁⟩
        have h3 := ((h1.comp h2).inv₀ (hγ0 q hqa)).const_add a
        rw [hγinv q] at h3
        exact h3
  · -- the estimate (20.18)
    intro f _ z hz
    have hza := hneDc z hz
    have hζ := hmemA₁ z hz
    obtain ⟨hu0, hw⟩ := hA₂ _ (hgtA₂ _ hζ)
    obtain ⟨φ, hφ, -⟩ := s13x_th_exists_disc_uniformizer hD.1
    have hP := s20l_density_mobius hDo hφ haD' hw
    rw [← hA₂def, add_sub_cancel_left, inv_inv] at hP
    have hηpos : 0 < poincareDensity D (a + (gt (z - a)⁻¹)⁻¹) := by
      rw [(poincareDensity_well_defined hDo hφ hφ hw).2]
      have h1 := deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hw
      have h2 : ‖φ (a + (gt (z - a)⁻¹)⁻¹)‖ < 1 := mem_ball_zero_iff.1 (hφ.mapsTo hw)
      have h3 : 0 < 1 - ‖φ (a + (gt (z - a)⁻¹)⁻¹)‖ ^ 2 := by
        nlinarith [norm_nonneg (φ (a + (gt (z - a)⁻¹)⁻¹))]
      exact div_pos (mul_pos two_pos (norm_pos_iff.2 h1)) h3
    have hr2 : 0 < ‖gt (z - a)⁻¹‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
    have hηA : 0 < poincareDensity A₂ (gt (z - a)⁻¹) :=
      (mul_pos_iff_of_pos_right hr2).1 (hP ▸ hηpos)
    have hS : ENNReal.ofReal (‖schwarzian f (a + (gt (z - a)⁻¹)⁻¹)‖ /
        poincareDensity D (a + (gt (z - a)⁻¹)⁻¹) ^ 2) ≤ schwarzianNorm f D := by
      unfold schwarzianNorm
      exact le_iSup₂ (f := fun x (_ : x ∈ D) =>
        ENNReal.ofReal (‖schwarzian f x‖ / poincareDensity D x ^ 2)) _ hw
    have hfd := s20l_a3_fderiv_le hza ((hC1z z hz).differentiableAt one_ne_zero) hu0
    simp only [norm_inv] at hfd
    have hdist := s20l_a3_norm_sub hu0 hza
    rw [norm_inv] at hdist
    have hkey := s20l_a3_real (norm_nonneg _) hηA (hl2' _ hζ) (norm_nonneg _) (hdg _ hζ)
      (norm_pos_iff.2 hu0) (norm_pos_iff.2 (sub_ne_zero.2 hza)) hdist hfd
    rw [hP] at hkey
    show ENNReal.ofReal (‖schwarzian f (a + (gt (z - a)⁻¹)⁻¹)‖ * ‖a + (gt (z - a)⁻¹)⁻¹ - z‖ ^ 2 *
      ‖fderiv ℝ (fun w => a + (gt (w - a)⁻¹)⁻¹) z‖) ≤ _
    rw [mul_assoc]
    exact s20l_a3_ennreal (norm_nonneg _) hηpos hS (hkey.trans (le_max_left _ _))

/-! ### Theorem 20.3 track, Stage A interface (coordinator 553e2d)

Proved helpers first (from the scout probes, renamed `t203_`), then the Stage A stubs. -/

/-- A Jordan domain (bounded or not) is a hyperbolic simply connected domain: it is conformally
equivalent to `Δ` (`s13x_th_exists_disc_uniformizer`). -/
theorem t203_hsc_of_isJordanDomain {D : Set ℂ} (hD : IsJordanDomain D) :
    IsHyperbolicSimplyConnected D := by
  obtain ⟨φ, hφ, -⟩ := s13x_th_exists_disc_uniformizer hD
  have hDo : IsOpen D := hD.1
  refine ⟨hDo, hD.2.1, ?_, ?_⟩
  · have hsurj : SurjOn φ D unitDisc := hφ.2.2 ▸ surjOn_image φ D
    have hmaps : MapsTo φ D unitDisc := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
    have hinvmaps : MapsTo (Function.invFunOn φ D) unitDisc D := hsurj.mapsTo_invFunOn
    have hinvc : ContinuousOn (Function.invFunOn φ D) unitDisc :=
      (hφ.symm hDo).1.continuousOn
    let e : D ≃ₜ unitDisc :=
      { toFun := hmaps.restrict φ D unitDisc
        invFun := hinvmaps.restrict (Function.invFunOn φ D) unitDisc D
        left_inv := fun x => Subtype.ext (hφ.2.1.leftInvOn_invFunOn x.2)
        right_inv := fun y => Subtype.ext (hsurj.rightInvOn_invFunOn y.2)
        continuous_toFun := hφ.1.continuousOn.mapsToRestrict hmaps
        continuous_invFun := hinvc.mapsToRestrict hinvmaps }
    have : SimplyConnectedSpace ↥unitDisc := t1_simplyConnected_unitDisc
    exact e.toHomotopyEquiv.simplyConnectedSpace
  · rintro rfl
    have hd : Differentiable ℂ φ := fun z => hφ.1.differentiableAt (isOpen_univ.mem_nhds (mem_univ z))
    have hb : Bornology.IsBounded (range φ) := by
      refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_
      rintro _ ⟨z, rfl⟩
      have : φ z ∈ φ '' univ := mem_image_of_mem φ (mem_univ z)
      rw [hφ.2.2] at this
      exact this
    have h01 := hd.apply_eq_apply_of_bounded hb 0 1
    exact zero_ne_one (hφ.2.1 (mem_univ _) (mem_univ _) h01)

/-- `IsKQuasidisc ⇒ IsHyperbolicSimplyConnected` (the first conjunct of `IsSchwarzDomain` in (i)). -/
theorem t203_hsc_of_isKQuasidisc {D : Set ℂ} {K : ℝ} (hD : IsKQuasidisc D K) :
    IsHyperbolicSimplyConnected D :=
  t203_hsc_of_isJordanDomain hD.1

/-- Core of the global-univalence step (Q7): a proper local homeomorphism from a connected open
`U ⊆ ℂ` (as a subtype) onto `ℂ` is bijective (covering map over the simply connected `ℂ`). -/
theorem t203_bijective_of_isLocalHomeomorph_isProperMap {U : Set ℂ} [PreconnectedSpace U]
    [Nonempty U] {p : U → ℂ} (hloc : IsLocalHomeomorph p) (hprop : IsProperMap p) :
    Function.Bijective p := by
  have hfin : ∀ y, (p ⁻¹' {y}).Finite := fun y => by
    have hdisc : IsDiscrete (p ⁻¹' {y}) :=
      IsDiscrete.of_openPartialHomeomorph p subset_rfl
        (fun e _ => let ⟨φ, hφ, hφe⟩ := hloc e; ⟨φ, hφ, hφe.symm⟩)
    exact (hprop.isCompact_preimage isCompact_singleton).finite hdisc
  have hcov : IsCoveringMap p := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine hprop.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun y _ => hfin y) ?_
    rw [preimage_univ, ← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hloc
  obtain ⟨u₀⟩ := ‹Nonempty U›
  obtain ⟨G, ⟨hG0, hGg⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id ℂ) (p u₀) u₀ rfl
  have hpG : ∀ y, p (G y) = y := fun y => by
    have := congrFun hGg y
    simpa using this
  have hGp : ∀ u, G (p u) = u := by
    have h : (G ∘ p) = (id : U → U) :=
      hcov.eq_of_comp_eq (G.continuous.comp hloc.continuous) continuous_id
        (by funext x; show p (G (p x)) = p x; rw [hpG]) u₀ (by show G (p u₀) = u₀; exact hG0)
    exact fun u => congrFun h u
  exact ⟨fun x y hxy => by rw [← hGp x, ← hGp y, hxy], fun y => ⟨G y, hpG y⟩⟩

/-- Core of the segment lemma: `ψ` vanishes on the closed set `S` (in the ball), is continuous on
`ball p r`, differentiable off `S` there with `‖dψ‖ ≤ ε`, and `p ∈ S`; then `‖ψ z‖ ≤ ε ‖z - p‖` on the
ball (mean value inequality on `[q, z]`, `q` the last point of `S` on the segment `[p, z]`). -/
theorem t203_segment_core {S : Set ℂ} (hS : IsClosed S) {ψ : ℂ → ℂ} {p : ℂ} {r ε : ℝ} (hε : 0 ≤ ε)
    (hp : p ∈ S) (hc : ContinuousOn ψ (ball p r)) (h0 : ∀ z ∈ ball p r ∩ S, ψ z = 0)
    (hd : ∀ z ∈ ball p r \ S, DifferentiableAt ℝ ψ z)
    (hb : ∀ z ∈ ball p r \ S, ‖fderiv ℝ ψ z‖ ≤ ε) {z : ℂ} (hz : z ∈ ball p r) :
    ‖ψ z‖ ≤ ε * ‖z - p‖ := by
  by_cases hzS : z ∈ S
  · rw [h0 z ⟨hz, hzS⟩, norm_zero]
    positivity
  set γ : ℝ → ℂ := fun t => p + (t : ℂ) * (z - p) with hγ
  have hγc : Continuous γ := by fun_prop
  set T : Set ℝ := Icc 0 1 ∩ γ ⁻¹' S with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hS.preimage hγc)
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by simpa [hγ] using hp⟩
  have hTb : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  set t₀ := sSup T with ht₀def
  have ht₀ : t₀ ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hTb
  have ht₀0 : 0 ≤ t₀ := ht₀.1.1
  have ht₀1 : t₀ < 1 := by
    rcases ht₀.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have := ht₀.2
      simp only [mem_preimage, hγ, h, ofReal_one, one_mul, add_sub_cancel] at this
      exact hzS this
  have hlast : ∀ t, t₀ < t → t ≤ 1 → γ t ∉ S := by
    intro t ht1 ht2 hS'
    have : t ∈ T := ⟨⟨ht₀0.trans ht1.le, ht2⟩, hS'⟩
    exact absurd (le_csSup hTb this) (not_le.2 ht1)
  set q := γ t₀ with hqdef
  have hq0 : ψ q = 0 := by
    have hqball : q ∈ ball p r := by
      rw [mem_ball, dist_eq_norm, hqdef, hγ]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht₀0]
      rw [mem_ball, dist_eq_norm] at hz
      calc t₀ * ‖z - p‖ ≤ 1 * ‖z - p‖ := by gcongr
        _ < r := by rwa [one_mul]
    exact h0 q ⟨hqball, ht₀.2⟩
  -- the segment from `z` back to `q`
  set l : ℝ → ℂ := fun s => z + (s : ℂ) * (q - z) with hl
  have hlγ : ∀ s : ℝ, l s = γ (1 - s * (1 - t₀)) := by
    intro s
    simp only [hl, hγ, hqdef]
    push_cast
    ring
  have hlball : ∀ s ∈ Icc (0 : ℝ) 1, l s ∈ ball p r := by
    intro s hs
    rw [hlγ, mem_ball, dist_eq_norm, hγ]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real]
    have h1 : 0 ≤ 1 - s * (1 - t₀) := by nlinarith [hs.1, hs.2]
    have h2 : 1 - s * (1 - t₀) ≤ 1 := by nlinarith [hs.1, hs.2]
    rw [Real.norm_of_nonneg h1]
    rw [mem_ball, dist_eq_norm] at hz
    calc (1 - s * (1 - t₀)) * ‖z - p‖ ≤ 1 * ‖z - p‖ := by gcongr
      _ < r := by rwa [one_mul]
  have hlS : ∀ s ∈ Ico (0 : ℝ) 1, l s ∉ S := by
    intro s hs
    rw [hlγ]
    apply hlast
    · nlinarith [hs.1, hs.2]
    · nlinarith [hs.1, hs.2]
  have hlder : ∀ s : ℝ, HasDerivAt l (q - z) s := by
    intro s
    have := ((hasDerivAt_id (s : ℝ)).ofReal_comp.mul_const (q - z)).const_add z
    simpa [hl] using this
  have hfc : ContinuousOn (ψ ∘ l) (Icc 0 1) :=
    hc.comp (by fun_prop : Continuous l).continuousOn (fun s hs => hlball s hs)
  have hfd : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (ψ ∘ l) (fderiv ℝ ψ (l s) (q - z)) (Ici s) s := by
    intro s hs
    have hd' := (hd (l s) ⟨hlball s (Ico_subset_Icc_self hs), hlS s hs⟩).hasFDerivAt
    exact (hd'.comp_hasDerivAt s (hlder s)).hasDerivWithinAt
  have hqz : ‖q - z‖ ≤ ‖z - p‖ := by
    have : q - z = ((t₀ - 1 : ℝ) : ℂ) * (z - p) := by
      simp only [hqdef, hγ]
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonpos (by linarith)]
    calc -(t₀ - 1) * ‖z - p‖ ≤ 1 * ‖z - p‖ := by gcongr; linarith
      _ = ‖z - p‖ := one_mul _
  have hbd : ∀ s ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ ψ (l s) (q - z)‖ ≤ ε * ‖z - p‖ := by
    intro s hs
    calc ‖fderiv ℝ ψ (l s) (q - z)‖ ≤ ‖fderiv ℝ ψ (l s)‖ * ‖q - z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖z - p‖ :=
          mul_le_mul (hb _ ⟨hlball s (Ico_subset_Icc_self hs), hlS s hs⟩) hqz (norm_nonneg _) hε
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment hfc hfd hbd 1 ⟨zero_le_one, le_rfl⟩
  have hl1 : l 1 = q := by simp [hl]
  have hl0 : l 0 = z := by simp [hl]
  simp only [Function.comp_apply, hl1, hl0, hq0, zero_sub, norm_neg, sub_zero, mul_one] at key
  exact key

/-- The hypothesis at the frontier gives the limit at every point of `U ∩ S` (at interior points of
`S` the filter `𝓝[U \ S] p` is `⊥`). -/
theorem t203_lim_of_frontier {U S : Set ℂ} (hS : IsClosed S) {F : ℂ → (ℂ →L[ℝ] ℂ)}
    (hlim : ∀ p ∈ U ∩ frontier S, Tendsto F (𝓝[U \ S] p) (𝓝 0)) :
    ∀ p ∈ U ∩ S, Tendsto F (𝓝[U \ S] p) (𝓝 0) := by
  intro p hp
  by_cases hpf : p ∈ frontier S
  · exact hlim p ⟨hp.1, hpf⟩
  · have hpi : p ∈ interior S := by
      rw [hS.frontier_eq] at hpf
      by_contra h
      exact hpf ⟨hp.2, h⟩
    have hbot : 𝓝[U \ S] p = ⊥ := by
      rw [← Filter.empty_mem_iff_bot]
      exact mem_nhdsWithin.2 ⟨interior S, isOpen_interior, hpi,
        fun x ⟨hx1, hx2⟩ => hx2.2 (interior_subset hx1)⟩
    rw [hbot]
    exact tendsto_bot

/-- **Segment lemma**: `ψ` continuous on the open `U`, zero on `U ∩ S` (`S` closed), differentiable on
`U \ S`, with `dψ → 0` at the frontier of `S` from `U \ S`; then `ψ` has derivative `0` at every point of
`U ∩ S`. -/
theorem t203_segment {U S : Set ℂ} (hU : IsOpen U) (hS : IsClosed S) {ψ : ℂ → ℂ}
    (hψc : ContinuousOn ψ U) (hψ0 : ∀ z ∈ U ∩ S, ψ z = 0)
    (hψd : ∀ z ∈ U \ S, DifferentiableAt ℝ ψ z)
    (hlim : ∀ p ∈ U ∩ frontier S, Tendsto (fun z => fderiv ℝ ψ z) (𝓝[U \ S] p) (𝓝 0)) :
    ∀ p ∈ U ∩ S, HasFDerivAt ψ (0 : ℂ →L[ℝ] ℂ) p := by
  intro p hp
  have hlim' := t203_lim_of_frontier hS hlim p hp
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  have hev : ∀ᶠ z in 𝓝[U \ S] p, dist (fderiv ℝ ψ z) 0 < c := Metric.tendsto_nhds.1 hlim' c hc
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨r₂, hr₂, hr₂s⟩ := Metric.isOpen_iff.1 hU p hp.1
  set r := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have hballU : ball p r ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hr₂s
  filter_upwards [ball_mem_nhds p hr0] with z hz
  have hcore := t203_segment_core hS hc.le hp.2 (hψc.mono hballU)
    (fun w hw => hψ0 w ⟨hballU hw.1, hw.2⟩) (fun w hw => hψd w ⟨hballU hw.1, hw.2⟩)
    (fun w hw => by
      have := hr₁s ⟨ball_subset_ball (min_le_left _ _) hw.1, hballU hw.1, hw.2⟩
      rw [mem_ofPred_eq, dist_zero_right] at this
      exact this.le) hz
  simpa [hψ0 p hp] using hcore

/-- Corollary: `ψ` is `C¹` on `U` when it is `C¹` on `U \ S`, zero on `U ∩ S`, continuous on `U`, and
`dψ → 0` at the frontier of `S`. -/
theorem t203_contDiffOn {U S : Set ℂ} (hU : IsOpen U) (hS : IsClosed S) {ψ : ℂ → ℂ}
    (hψc : ContinuousOn ψ U) (hψ0 : ∀ z ∈ U ∩ S, ψ z = 0) (hC1 : ContDiffOn ℝ 1 ψ (U \ S))
    (hlim : ∀ p ∈ U ∩ frontier S, Tendsto (fun z => fderiv ℝ ψ z) (𝓝[U \ S] p) (𝓝 0)) :
    ContDiffOn ℝ 1 ψ U := by
  have hUS : IsOpen (U \ S) := hU.sdiff hS
  have hψd : ∀ z ∈ U \ S, DifferentiableAt ℝ ψ z := fun z hz =>
    (hC1.differentiableOn one_ne_zero z hz).differentiableAt (hUS.mem_nhds hz)
  have hseg := t203_segment hU hS hψc hψ0 hψd hlim
  have hlim' := t203_lim_of_frontier hS hlim
  have hdc : ContinuousOn (fun z => fderiv ℝ ψ z) (U \ S) := hC1.continuousOn_fderiv_of_isOpen hUS le_rfl
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun z hz => ?_, by simp, contDiffOn_zero.2 fun z hz => ?_⟩
  · by_cases hzS : z ∈ S
    · exact (hseg z ⟨hz, hzS⟩).differentiableAt.differentiableWithinAt
    · exact (hψd z ⟨hz, hzS⟩).differentiableWithinAt
  · by_cases hzS : z ∈ S
    · have hz0 : fderiv ℝ ψ z = 0 := (hseg z ⟨hz, hzS⟩).fderiv
      show Tendsto _ _ _
      rw [hz0]
      have hsplit : U = (U \ S) ∪ (U ∩ S) := (sdiff_union_inter U S).symm
      rw [hsplit, nhdsWithin_union]
      refine (hlim' z ⟨hz, hzS⟩).sup (tendsto_const_nhds.congr' ?_)
      exact eventually_nhdsWithin_of_forall fun w hw => (hseg w hw).fderiv.symm
    · exact ((hdc z ⟨hz, hzS⟩).continuousAt (hUS.mem_nhds ⟨hz, hzS⟩)).continuousWithinAt

/-- (20.14), Koebe lower bound for the Poincaré density: `η_D(w) ≥ 1/(2 |w' - w|)` for every `w' ∉ D`
(Koebe ¼ for `h⁻¹`, `h = M_{φ w} ∘ φ` the conformal map of `D` onto `Δ` with `h w = 0`). -/
theorem t203_density_ge {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ D unitDisc)
    {w : ℂ} (hw : w ∈ D) {w' : ℂ} (hw' : w' ∉ D) :
    1 / (2 * ‖w' - w‖) ≤ poincareDensity D w := by
  have ha : ‖φ w‖ < 1 := mem_ball_zero_iff.1 (hφ.mapsTo hw)
  set h : ℂ → ℂ := blaschke (φ w) ∘ φ with hhdef
  have hh : IsConformalOnto h D unitDisc := (isConformalOnto_blaschke ha).comp hφ
  have hhw : h w = 0 := by simp [hhdef]
  rw [(poincareDensity_well_defined hD hh hh hw).2, hhw, norm_zero]
  have hs : IsConformalOnto (Function.invFunOn h D) unitDisc D := hh.symm hD
  have hleft : ∀ v ∈ D, Function.invFunOn h D (h v) = v := fun v hv =>
    hh.2.1.leftInvOn_invFunOn hv
  set F : ℂ → ℂ := fun u => Function.invFunOn h D u - w with hF
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hs.1.sub_const w
  have hFinj : InjOn F (ball 0 1) := by
    intro u₁ hu₁ u₂ hu₂ hu
    exact hs.2.1 hu₁ hu₂ (sub_left_injective hu)
  have hF0 : F 0 = 0 := by
    have : Function.invFunOn h D 0 = w := by
      conv_lhs => rw [← hhw]
      exact hleft w hw
    simp only [hF, this, sub_self]
  have hnot : w' - w ∉ F '' ball 0 1 := by
    rintro ⟨u, hu, hFu⟩
    apply hw'
    have hmem : Function.invFunOn h D u ∈ D := hs.mapsTo hu
    have hval : Function.invFunOn h D u = w' := sub_left_injective hFu
    rwa [hval] at hmem
  have hK := koebe_quarter_of_not_mem hFd hFinj hF0 hnot
  have hinvd : DifferentiableAt ℂ (Function.invFunOn h D) (h w) := hh.differentiableAt_invFunOn hD hw
  have hhd : HasDerivAt h (deriv h w) w := (hh.1.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hFder : deriv F 0 = deriv (Function.invFunOn h D) (h w) := by
    have h1 := hinvd.hasDerivAt.sub_const w
    rw [hhw] at h1 ⊢
    exact h1.deriv
  have hcomp1 : HasDerivAt (Function.invFunOn h D ∘ h)
      (deriv (Function.invFunOn h D) (h w) * deriv h w) w := hinvd.hasDerivAt.comp w hhd
  have hev : Function.invFunOn h D ∘ h =ᶠ[𝓝 w] id := by
    filter_upwards [hD.mem_nhds hw] with v hv
    exact hleft v hv
  have hcomp2 : HasDerivAt (Function.invFunOn h D ∘ h) 1 w :=
    (hasDerivAt_id w).congr_of_eventuallyEq hev
  have hone : deriv (Function.invFunOn h D) (h w) * deriv h w = 1 := hcomp1.unique hcomp2
  have hone' : ‖deriv (Function.invFunOn h D) (h w)‖ * ‖deriv h w‖ = 1 := by
    rw [← norm_mul, hone, norm_one]
  rw [hFder] at hK
  have hd : 0 < ‖w' - w‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h' => hw' (h' ▸ hw))
  have h4 : 1 ≤ 4 * ‖w' - w‖ * ‖deriv h w‖ := by
    rw [← hone']
    exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  rw [div_le_iff₀ (by positivity)]
  norm_num
  nlinarith

/-- (20.14) with the distance to the complement (any positive `d ≤ ‖w' - w‖` for all `w' ∉ D`): if
`D ≠ ℂ` then `η_D(w) ≥ 1/(2 infDist w Dᶜ)`. -/
theorem t203_density_ge_infDist {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ D unitDisc)
    {w : ℂ} (hw : w ∈ D) (hne : Dᶜ.Nonempty) :
    1 / (2 * infDist w Dᶜ) ≤ poincareDensity D w := by
  obtain ⟨y, hy, hyd⟩ := hD.isClosed_compl.exists_infDist_eq_dist hne w
  rw [hyd, dist_comm, dist_eq_norm]
  exact t203_density_ge hD hφ hw hy

/-- **P3 + decay**: for the reflection `g` of `(closure D)ᶜ` onto `D ∖ {p}` with the Möbius-invariant bound
`|g z - z|² |dg z| η_D(g z)² ≤ c₀`, at every `q ∈ ∂(closure D)`: `g z → q`, `g z - z → 0`, and
`|g z - z|² |dg z| → 0` as `z → q` from outside (`≤ 4 c₀ |q - g z|²` by (20.14)). -/
theorem t203_decay {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ D unitDisc)
    {g : ℂ → ℂ} {K₁ c₀ : ℝ} {p : ℂ} (hp : p ∈ D)
    (hg : IsPlanarQCReflection (closure D)ᶜ (D \ {p}) g K₁)
    (hc : ∀ z ∈ (closure D)ᶜ, ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ * poincareDensity D (g z) ^ 2 ≤ c₀)
    {q : ℂ} (hq : q ∈ frontier (closure D)) :
    Tendsto g (𝓝[(closure D)ᶜ] q) (𝓝 q) ∧
      Tendsto (fun z => g z - z) (𝓝[(closure D)ᶜ] q) (𝓝 0) ∧
      Tendsto (fun z => ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖) (𝓝[(closure D)ᶜ] q) (𝓝 0) := by
  have hqD : q ∈ frontier D := frontier_closure_subset hq
  have hqnD : q ∉ D := fun h => hqD.2 (hD.interior_eq.symm ▸ h)
  have hqp : q ≠ p := fun h => hqnD (h ▸ hp)
  have hfr : q ∈ frontier (closure D)ᶜ ∩ frontier (D \ {p}) := by
    refine ⟨by rwa [frontier_compl], ?_, fun h => hqnD (interior_subset h).1⟩
    refine closure_sdiff ⟨frontier_subset_closure hqD, ?_⟩
    rw [closure_singleton]
    exact hqp
  have htend : Tendsto g (𝓝[(closure D)ᶜ] q) (𝓝 q) := hg.2.2.2 q hfr
  have hid : Tendsto (fun z : ℂ => z) (𝓝[(closure D)ᶜ] q) (𝓝 q) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hsub : Tendsto (fun z => g z - z) (𝓝[(closure D)ᶜ] q) (𝓝 0) := by
    have := htend.sub hid
    rwa [sub_self] at this
  refine ⟨htend, hsub, ?_⟩
  have hbound : ∀ z ∈ (closure D)ᶜ, ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ ≤ 4 * c₀ * ‖q - g z‖ ^ 2 := by
    intro z hz
    have hgz : g z ∈ D := (hg.2.1 ▸ mem_image_of_mem g hz : g z ∈ D \ {p}).1
    have hη := t203_density_ge hD hφ hgz hqnD
    have hd : 0 < ‖q - g z‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hqnD (h ▸ hgz))
    set X := ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ with hX
    have hX0 : 0 ≤ X := by positivity
    have h1 : X * (1 / (2 * ‖q - g z‖)) ^ 2 ≤ c₀ :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hη 2) hX0) (hc z hz)
    have h2 : X = X * (1 / (2 * ‖q - g z‖)) ^ 2 * (4 * ‖q - g z‖ ^ 2) := by
      field_simp
      ring
    rw [h2]
    calc X * (1 / (2 * ‖q - g z‖)) ^ 2 * (4 * ‖q - g z‖ ^ 2) ≤ c₀ * (4 * ‖q - g z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 4 * c₀ * ‖q - g z‖ ^ 2 := by ring
  have hlim : Tendsto (fun z => 4 * c₀ * ‖q - g z‖ ^ 2) (𝓝[(closure D)ᶜ] q) (𝓝 0) := by
    have h1 : Tendsto (fun z => q - g z) (𝓝[(closure D)ᶜ] q) (𝓝 0) := by
      have := (tendsto_const_nhds (x := q)).sub htend
      rwa [sub_self] at this
    have h2 := ((h1.norm).pow 2).const_mul (4 * c₀)
    simpa using h2
  refine squeeze_zero' (Eventually.of_forall fun z => by positivity)
    (eventually_nhdsWithin_of_forall hbound) hlim

/-- The (20.10) derivative of the Ahlfors extension `F(z) = (w₁(ζ) + u w₁'(ζ)) / (w₂(ζ) + u w₂'(ζ))`,
`ζ = g z`, `u = z - ζ`, with `w'' = -a w` and Wronskian `w₁ w₂' - w₁' w₂ = 1`:
`dF = -1/Dn² · dz - a u²/Dn² · dg` (the `u`-linear terms cancel, the `u⁰` part of the `ζ`-coefficient
vanishes by the ODE). -/
theorem t203_dF {w₁ w₂ w₁' w₂' g : ℂ → ℂ} {G : ℂ →L[ℝ] ℂ} {z a : ℂ}
    (h1 : HasDerivAt w₁ (w₁' (g z)) (g z)) (h2 : HasDerivAt w₂ (w₂' (g z)) (g z))
    (h1' : HasDerivAt w₁' (-a * w₁ (g z)) (g z)) (h2' : HasDerivAt w₂' (-a * w₂ (g z)) (g z))
    (hW : w₁ (g z) * w₂' (g z) - w₁' (g z) * w₂ (g z) = 1)
    (hg : HasFDerivAt g G z) (hD : w₂ (g z) + (z - g z) * w₂' (g z) ≠ 0) :
    HasFDerivAt (fun z => (w₁ (g z) + (z - g z) * w₁' (g z)) / (w₂ (g z) + (z - g z) * w₂' (g z)))
      ((-1 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2) • ContinuousLinearMap.id ℝ ℂ +
        (-a * (z - g z) ^ 2 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2) • G) z := by
  have e1 := (h1.hasFDerivAt.restrictScalars ℝ).comp z hg
  have e1' := (h1'.hasFDerivAt.restrictScalars ℝ).comp z hg
  have e2 := (h2.hasFDerivAt.restrictScalars ℝ).comp z hg
  have e2' := (h2'.hasFDerivAt.restrictScalars ℝ).comp z hg
  have eu : HasFDerivAt (fun z => z - g z) (ContinuousLinearMap.id ℝ ℂ - G) z := (hasFDerivAt_id z).sub hg
  have eN := e1.add (eu.mul e1')
  have eD := e2.add (eu.mul e2')
  have einv := ((hasDerivAt_inv hD).hasFDerivAt.restrictScalars ℝ).comp z eD
  have eF := eN.mul einv
  have hfun : (fun z => (w₁ (g z) + (z - g z) * w₁' (g z)) / (w₂ (g z) + (z - g z) * w₂' (g z))) =
      fun z => (w₁ (g z) + (z - g z) * w₁' (g z)) * (w₂ (g z) + (z - g z) * w₂' (g z))⁻¹ := by
    funext y
    rw [div_eq_mul_inv]
  rw [hfun]
  refine eF.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    sub_apply, smul_eq_mul, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, Pi.add_apply, Pi.mul_apply]
  field_simp
  linear_combination (-(v + a * (z - g z) ^ 2 * G v)) * hW

/-- The limit of `dψ = dF - f' dz` (`f' = -1/w₂²`) at `q ∈ C_n` from outside: with `Dn → w₂ q ≠ 0` and
`|u|² |dg| → 0`, both the `dz` part `-1/Dn² + 1/w₂(z)²` and the `dg` part `-a u²/Dn²` tend to `0`. -/
theorem t203_fderiv_tendsto {w₂ w₂' a g : ℂ → ℂ} {dg : ℂ → (ℂ →L[ℝ] ℂ)} {L : Filter ℂ} {q : ℂ}
    (hw₂ : ContinuousAt w₂ q) (hw₂' : ContinuousAt w₂' q) (ha : ContinuousAt a q) (hq : w₂ q ≠ 0)
    (hz : Tendsto (fun z => z) L (𝓝 q)) (hg : Tendsto g L (𝓝 q))
    (hdec : Tendsto (fun z => ‖z - g z‖ ^ 2 * ‖dg z‖) L (𝓝 0)) :
    Tendsto (fun z => ((-1 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2) • ContinuousLinearMap.id ℝ ℂ +
        (-a (g z) * (z - g z) ^ 2 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2) • dg z) -
        (-1 / w₂ z ^ 2) • ContinuousLinearMap.id ℝ ℂ) L (𝓝 0) := by
  have hu : Tendsto (fun z => z - g z) L (𝓝 0) := by
    have := hz.sub hg
    rwa [sub_self] at this
  have hDn : Tendsto (fun z => w₂ (g z) + (z - g z) * w₂' (g z)) L (𝓝 (w₂ q)) := by
    have := (hw₂.tendsto.comp hg).add (hu.mul (hw₂'.tendsto.comp hg))
    rwa [zero_mul, add_zero] at this
  have hq2 : w₂ q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hA : Tendsto (fun z => -1 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2 - -1 / w₂ z ^ 2) L (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := (-1 : ℂ))).div (hDn.pow 2) hq2
    have h2 := (tendsto_const_nhds (x := (-1 : ℂ))).div ((hw₂.tendsto.comp hz).pow 2) hq2
    have := h1.sub h2
    rwa [sub_self] at this
  have hB : Tendsto (fun z => (-a (g z) * (z - g z) ^ 2 / (w₂ (g z) + (z - g z) * w₂' (g z)) ^ 2) • dg z)
      L (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hc : Tendsto (fun z => ‖a (g z)‖ / ‖w₂ (g z) + (z - g z) * w₂' (g z)‖ ^ 2) L
        (𝓝 (‖a q‖ / ‖w₂ q‖ ^ 2)) :=
      ((ha.tendsto.comp hg).norm).div ((hDn.norm).pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.2 hq))
    have := hc.mul hdec
    rw [mul_zero] at this
    refine this.congr fun z => ?_
    rw [norm_smul, norm_div, norm_mul, norm_neg, norm_pow, norm_pow]
    ring
  have := (hA.smul_const (ContinuousLinearMap.id ℝ ℂ)).add hB
  have h0 : (0 : ℂ) • ContinuousLinearMap.id ℝ ℂ + (0 : ℂ →L[ℝ] ℂ) = 0 := by
    ext v
    simp
  rw [h0] at this
  refine this.congr fun z => ?_
  ext v
  simp only [add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- `∂f` read off from a real derivative `L`: `∂f = (L 1 - i L i)/2`. -/
theorem t203_dz_of_hasFDerivAt {f : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt f L z) :
    dz f z = (L 1 - I * L I) / 2 := by
  rw [dz, h.fderiv]

/-- `∂̄f` read off from a real derivative `L`: `∂̄f = (L 1 + i L i)/2`. -/
theorem t203_dzbar_of_hasFDerivAt {f : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt f L z) :
    dzbar f z = (L 1 + I * L I) / 2 := by
  rw [dzbar, h.fderiv]

/-- Chain rule, holomorphic outer map (restated; `eq6_5` in S06 is the project version). -/
theorem t203_comp_holo {W g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z)
    (hW : DifferentiableAt ℂ W (g z)) :
    dz (fun w => W (g w)) z = deriv W (g z) * dz g z ∧
      dzbar (fun w => W (g w)) z = deriv W (g z) * dzbar g z :=
  eq6_5 hg hW

/-- `∂(z - g) = 1 - ∂g`, `∂̄(z - g) = -∂̄g`. -/
theorem t203_dz_id_sub {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    dz (fun w => w - g w) z = 1 - dz g z ∧ dzbar (fun w => w - g w) z = -dzbar g z := by
  have h : HasFDerivAt (fun w => w - g w) (ContinuousLinearMap.id ℝ ℂ - fderiv ℝ g z) z :=
    (hasFDerivAt_id (𝕜 := ℝ) z).fun_sub hg.hasFDerivAt
  rw [t203_dz_of_hasFDerivAt h, t203_dzbar_of_hasFDerivAt h, dz, dzbar]
  simp only [sub_apply, ContinuousLinearMap.coe_id', id]
  constructor
  · linear_combination (-(1 : ℂ) / 2) * I_sq
  · linear_combination ((1 : ℂ) / 2) * I_sq

/-- The real derivative of `G(w) = A(g w) + (w - g w) B(g w)` when `A' = B` and `B' = -a A` at `g z`. -/
theorem t203_hasFDerivAt_G {A B g : ℂ → ℂ} {z a : ℂ} (hg : DifferentiableAt ℝ g z)
    (hA : HasDerivAt A (B (g z)) (g z)) (hB : HasDerivAt B (-(a * A (g z))) (g z)) :
    HasFDerivAt (fun w => A (g w) + (w - g w) * B (g w))
      (B (g z) • ContinuousLinearMap.id ℝ ℂ - ((z - g z) * a * A (g z)) • fderiv ℝ g z) z := by
  have hgA : HasFDerivAt (fun w => A (g w)) (B (g z) • fderiv ℝ g z) z :=
    hA.comp_hasFDerivAt z hg.hasFDerivAt
  have hgB : HasFDerivAt (fun w => B (g w)) ((-(a * A (g z))) • fderiv ℝ g z) z :=
    hB.comp_hasFDerivAt z hg.hasFDerivAt
  have hu : HasFDerivAt (fun w => w - g w) (ContinuousLinearMap.id ℝ ℂ - fderiv ℝ g z) z :=
    (hasFDerivAt_id (𝕜 := ℝ) z).fun_sub hg.hasFDerivAt
  have hG := hgA.add (hu.fun_mul hgB)
  convert hG using 1
  ext h
  simp only [sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.coe_id', id, smul_eq_mul]
  ring

/-- **Generic (20.10) step**: `∂G = B - u a A ∂g`, `∂̄G = -u a A ∂̄g` with `u = z - g z`. -/
theorem t203_dz_dzbar_G {A B g : ℂ → ℂ} {z a : ℂ} (hg : DifferentiableAt ℝ g z)
    (hA : HasDerivAt A (B (g z)) (g z)) (hB : HasDerivAt B (-(a * A (g z))) (g z)) :
    dz (fun w => A (g w) + (w - g w) * B (g w)) z = B (g z) - (z - g z) * a * A (g z) * dz g z ∧
      dzbar (fun w => A (g w) + (w - g w) * B (g w)) z = -((z - g z) * a * A (g z) * dzbar g z) := by
  have h := t203_hasFDerivAt_G hg hA hB
  rw [t203_dz_of_hasFDerivAt h, t203_dzbar_of_hasFDerivAt h, dz, dzbar]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_id', id, smul_eq_mul]
  constructor
  · linear_combination (-(B (g z)) / 2) * I_sq
  · linear_combination (B (g z) / 2) * I_sq

/-- Quotient rule for `∂`, `∂̄`. -/
theorem t203_dz_div {N D : ℂ → ℂ} {z : ℂ} (hN : DifferentiableAt ℝ N z) (hD : DifferentiableAt ℝ D z)
    (h0 : D z ≠ 0) :
    dz (fun w => N w / D w) z = (D z * dz N z - N z * dz D z) / D z ^ 2 ∧
      dzbar (fun w => N w / D w) z = (D z * dzbar N z - N z * dzbar D z) / D z ^ 2 := by
  have hinv : HasFDerivAt (fun w => (D w)⁻¹) ((-(D z ^ 2)⁻¹) • fderiv ℝ D z) z :=
    (hasDerivAt_inv h0).comp_hasFDerivAt z hD.hasFDerivAt
  have hq := hN.hasFDerivAt.fun_mul hinv
  have he : (fun w => N w / D w) = fun w => N w * (D w)⁻¹ := by
    funext w; rw [div_eq_mul_inv]
  rw [he, t203_dz_of_hasFDerivAt hq, t203_dzbar_of_hasFDerivAt hq, dz, dz, dzbar, dzbar]
  simp only [add_apply, smul_apply, smul_eq_mul]
  constructor <;> field_simp <;> ring

/-- **(20.10), the Wirtinger derivatives of `F = N/D`**, `N = A₁∘g + (z-g)·B₁∘g`, `D = A₂∘g + (z-g)·B₂∘g`,
with `A_i' = B_i`, `B_i' = -a A_i` at `g z` and Wronskian `A₁B₂ - A₂B₁ = 1`. -/
theorem t203_dz_dzbar_F {A₁ B₁ A₂ B₂ g : ℂ → ℂ} {z a : ℂ} (hg : DifferentiableAt ℝ g z)
    (hA₁ : HasDerivAt A₁ (B₁ (g z)) (g z)) (hB₁ : HasDerivAt B₁ (-(a * A₁ (g z))) (g z))
    (hA₂ : HasDerivAt A₂ (B₂ (g z)) (g z)) (hB₂ : HasDerivAt B₂ (-(a * A₂ (g z))) (g z))
    (hW : A₁ (g z) * B₂ (g z) - A₂ (g z) * B₁ (g z) = 1)
    (hD : A₂ (g z) + (z - g z) * B₂ (g z) ≠ 0) :
    dz (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z =
        -(1 + (z - g z) ^ 2 * a * dz g z) / (A₂ (g z) + (z - g z) * B₂ (g z)) ^ 2 ∧
      dzbar (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z =
        -((z - g z) ^ 2 * a * dzbar g z) / (A₂ (g z) + (z - g z) * B₂ (g z)) ^ 2 := by
  have hN := t203_hasFDerivAt_G hg hA₁ hB₁
  have hDn := t203_hasFDerivAt_G hg hA₂ hB₂
  obtain ⟨e1, e2⟩ := t203_dz_div hN.differentiableAt hDn.differentiableAt hD
  obtain ⟨n1, n2⟩ := t203_dz_dzbar_G hg hA₁ hB₁
  obtain ⟨d1, d2⟩ := t203_dz_dzbar_G hg hA₂ hB₂
  rw [e1, e2, n1, n2, d1, d2]
  constructor
  · congr 1
    linear_combination (-(1 + (z - g z) ^ 2 * a * dz g z)) * hW
  · congr 1
    linear_combination (-((z - g z) ^ 2 * a * dzbar g z)) * hW

/-- **(20.10), the complex dilatation**: `μ_F = u² a ∂̄g / (1 + u² a ∂g)` (`u = z - g z`). -/
theorem t203_mu_F {A₁ B₁ A₂ B₂ g : ℂ → ℂ} {z a : ℂ} (hg : DifferentiableAt ℝ g z)
    (hA₁ : HasDerivAt A₁ (B₁ (g z)) (g z)) (hB₁ : HasDerivAt B₁ (-(a * A₁ (g z))) (g z))
    (hA₂ : HasDerivAt A₂ (B₂ (g z)) (g z)) (hB₂ : HasDerivAt B₂ (-(a * A₂ (g z))) (g z))
    (hW : A₁ (g z) * B₂ (g z) - A₂ (g z) * B₁ (g z) = 1)
    (hD : A₂ (g z) + (z - g z) * B₂ (g z) ≠ 0) :
    complexDilatation (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z =
      (z - g z) ^ 2 * a * dzbar g z / (1 + (z - g z) ^ 2 * a * dz g z) := by
  obtain ⟨h1, h2⟩ := t203_dz_dzbar_F hg hA₁ hB₁ hA₂ hB₂ hW hD
  rw [complexDilatation, h1, h2, div_div_div_cancel_right₀ (pow_ne_zero 2 hD), neg_div_neg_eq]

/-- Scalar core: `‖c q‖ < ‖1 + c p‖` and `‖c q/(1 + c p)‖ ≤ t` when `‖c‖(‖p‖ + ‖q‖) ≤ t < 1`. -/
theorem t203_scalar_bound {p q c : ℂ} {t : ℝ} (ht : t < 1) (hc : ‖c‖ * (‖p‖ + ‖q‖) ≤ t) :
    ‖c * q‖ < ‖1 + c * p‖ ∧ ‖c * q / (1 + c * p)‖ ≤ t := by
  have h1 : 1 - ‖c‖ * ‖p‖ ≤ ‖1 + c * p‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(c * p))
    rw [norm_one, norm_neg, norm_mul, sub_neg_eq_add] at this
    linarith
  have hcp : 0 ≤ ‖c‖ * ‖p‖ := by positivity
  have hcq : 0 ≤ ‖c‖ * ‖q‖ := by positivity
  have ht0 : 0 ≤ t := le_trans (by positivity) hc
  have hlt : ‖c * q‖ < ‖1 + c * p‖ := by
    rw [norm_mul]; nlinarith
  refine ⟨hlt, ?_⟩
  have hpos : 0 < ‖1 + c * p‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  rw [norm_div, div_le_iff₀ hpos, norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ht0]

/-- **(Q-c)** at the level of `F`: the Beltrami inequality `‖∂̄F‖ < ‖∂F‖` and `‖μ_F‖ ≤ t`. -/
theorem t203_F_bound {A₁ B₁ A₂ B₂ g : ℂ → ℂ} {z a : ℂ} {t : ℝ} (hg : DifferentiableAt ℝ g z)
    (hA₁ : HasDerivAt A₁ (B₁ (g z)) (g z)) (hB₁ : HasDerivAt B₁ (-(a * A₁ (g z))) (g z))
    (hA₂ : HasDerivAt A₂ (B₂ (g z)) (g z)) (hB₂ : HasDerivAt B₂ (-(a * A₂ (g z))) (g z))
    (hW : A₁ (g z) * B₂ (g z) - A₂ (g z) * B₁ (g z) = 1)
    (hD : A₂ (g z) + (z - g z) * B₂ (g z) ≠ 0) (ht : t < 1)
    (hc : ‖(z - g z) ^ 2 * a‖ * (‖dz g z‖ + ‖dzbar g z‖) ≤ t) :
    ‖dzbar (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ <
        ‖dz (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ ∧
      ‖complexDilatation
          (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ ≤ t := by
  obtain ⟨h1, h2⟩ := t203_dz_dzbar_F hg hA₁ hB₁ hA₂ hB₂ hW hD
  obtain ⟨b1, b2⟩ := t203_scalar_bound (p := dz g z) (q := dzbar g z) ht hc
  have hDp : 0 < ‖(A₂ (g z) + (z - g z) * B₂ (g z)) ^ 2‖ := norm_pos_iff.2 (pow_ne_zero 2 hD)
  refine ⟨?_, ?_⟩
  · rw [h1, h2, norm_div, norm_div, norm_neg, norm_neg]
    refine div_lt_div_of_pos_right ?_ hDp
    simpa [mul_assoc] using b1
  · rw [t203_mu_F hg hA₁ hB₁ hA₂ hB₂ hW hD]
    simpa [mul_assoc] using b2

/-- `‖∂g‖ + ‖∂̄g‖ ≤ ‖dg‖` (in fact equality: the operator norm of `h ↦ p h + q h̄` is `|p| + |q|`). -/
theorem t203_norm_dz_add_dzbar_le {g : ℂ → ℂ} {z : ℂ} :
    ‖dz g z‖ + ‖dzbar g z‖ ≤ ‖fderiv ℝ g z‖ := by
  by_cases hg : DifferentiableAt ℝ g z
  · set p := dz g z
    set q := dzbar g z
    set θ : ℝ := (arg q - arg p) / 2
    set ψ : ℝ := (arg p + arg q) / 2
    have hh : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
    have hconj : conj (exp (θ * I)) = exp (-θ * I) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring_nf
    have hp : p * exp (θ * I) = ‖p‖ * exp (ψ * I) := by
      conv_lhs => rw [← norm_mul_exp_arg_mul_I p]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; simp only [θ, ψ]; push_cast; ring
    have hq : q * exp (-θ * I) = ‖q‖ * exp (ψ * I) := by
      conv_lhs => rw [← norm_mul_exp_arg_mul_I q]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; simp only [θ, ψ]; push_cast; ring
    have hL := fderiv_eq_dz_dzbar hg (exp (θ * I))
    rw [hconj, hp, hq, ← add_mul] at hL
    have hle := (fderiv ℝ g z).le_opNorm (exp (θ * I))
    rw [hL, hh, mul_one, norm_mul, norm_exp_ofReal_mul_I, mul_one, ← ofReal_add, norm_real,
      Real.norm_of_nonneg (by positivity)] at hle
    exact hle
  · simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hg]

/-- The reverse inequality, so `‖dg‖ = ‖∂g‖ + ‖∂̄g‖` exactly. -/
theorem t203_norm_fderiv_le {g : ℂ → ℂ} {z : ℂ} :
    ‖fderiv ℝ g z‖ ≤ ‖dz g z‖ + ‖dzbar g z‖ := by
  by_cases hg : DifferentiableAt ℝ g z
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [fderiv_eq_dz_dzbar hg, add_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
  · rw [fderiv_zero_of_not_differentiableAt hg, norm_zero]; positivity

/-- **(Q-c), book form**: with `a = S/2` and `‖S‖ ‖u‖² ‖dg‖ ≤ t < 2`, the extension satisfies `‖∂̄F‖ < ‖∂F‖`
and `‖μ_F‖ ≤ t/2`. -/
theorem t203_F_bound_book {A₁ B₁ A₂ B₂ g : ℂ → ℂ} {z S : ℂ} {t : ℝ} (hg : DifferentiableAt ℝ g z)
    (hA₁ : HasDerivAt A₁ (B₁ (g z)) (g z)) (hB₁ : HasDerivAt B₁ (-(S / 2 * A₁ (g z))) (g z))
    (hA₂ : HasDerivAt A₂ (B₂ (g z)) (g z)) (hB₂ : HasDerivAt B₂ (-(S / 2 * A₂ (g z))) (g z))
    (hW : A₁ (g z) * B₂ (g z) - A₂ (g z) * B₁ (g z) = 1)
    (hD : A₂ (g z) + (z - g z) * B₂ (g z) ≠ 0) (ht : t < 2)
    (hS : ‖S‖ * ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ ≤ t) :
    ‖dzbar (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ <
        ‖dz (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ ∧
      ‖complexDilatation
          (fun w => (A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w))) z‖ ≤ t / 2 := by
  refine t203_F_bound hg hA₁ hB₁ hA₂ hB₂ hW hD (by linarith) ?_
  have hn := t203_norm_dz_add_dzbar_le (g := g) (z := z)
  rw [norm_mul, norm_pow, norm_div, ← norm_neg (z - g z), neg_sub, Complex.norm_two]
  have h0 : 0 ≤ ‖S‖ * ‖g z - z‖ ^ 2 := by positivity
  calc ‖g z - z‖ ^ 2 * (‖S‖ / 2) * (‖dz g z‖ + ‖dzbar g z‖)
      = (‖S‖ * ‖g z - z‖ ^ 2) * (‖dz g z‖ + ‖dzbar g z‖) / 2 := by ring
    _ ≤ (‖S‖ * ‖g z - z‖ ^ 2) * ‖fderiv ℝ g z‖ / 2 := by gcongr
    _ ≤ t / 2 := by linarith

/-- Bridge from the `eq19_2_ode` form `w'' + (φ/2) w = 0` to the `HasDerivAt` hypotheses. -/
theorem t203_ode_hasDerivAt {w : ℂ → ℂ} {ζ a : ℂ} (hw : DifferentiableAt ℂ w ζ)
    (hw' : DifferentiableAt ℂ (deriv w) ζ) (hode : deriv (deriv w) ζ + a * w ζ = 0) :
    HasDerivAt w (deriv w ζ) ζ ∧ HasDerivAt (deriv w) (-(a * w ζ)) ζ := by
  refine ⟨hw.hasDerivAt, ?_⟩
  have := hw'.hasDerivAt
  rwa [show deriv (deriv w) ζ = -(a * w ζ) by linear_combination hode] at this

/-- Where the denominator vanishes, the numerator does not (Wronskian `1`). -/
theorem t203_num_ne_zero {A₁ B₁ A₂ B₂ u : ℂ} (hW : A₁ * B₂ - A₂ * B₁ = 1) (hD : A₂ + u * B₂ = 0) :
    A₁ + u * B₁ ≠ 0 := by
  intro hN
  have : (1 : ℂ) = 0 := by linear_combination -hW + B₂ * hN - B₁ * hD
  exact one_ne_zero this

/-- `-1/F` has the same form with the pair `(-A₂, -B₂; A₁, B₁)`. -/
theorem t203_neg_inv_F (A₁ B₁ A₂ B₂ g : ℂ → ℂ) :
    (fun w => -1 / ((A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w)))) =
      fun w => ((fun x => -A₂ x) (g w) + (w - g w) * (fun x => -B₂ x) (g w)) /
        (A₁ (g w) + (w - g w) * B₁ (g w)) := by
  funext w
  rw [div_div_eq_mul_div]
  ring

/-- The pair `(-A₂, -B₂; A₁, B₁)` satisfies the same hypotheses (ODE, Wronskian `1`). -/
theorem t203_pole_pair_hyps {A₁ B₁ A₂ B₂ : ℂ → ℂ} {ζ a : ℂ}
    (hA₂ : HasDerivAt A₂ (B₂ ζ) ζ) (hB₂ : HasDerivAt B₂ (-(a * A₂ ζ)) ζ)
    (hW : A₁ ζ * B₂ ζ - A₂ ζ * B₁ ζ = 1) :
    HasDerivAt (fun x => -A₂ x) ((fun x => -B₂ x) ζ) ζ ∧
      HasDerivAt (fun x => -B₂ x) (-(a * (fun x => -A₂ x) ζ)) ζ ∧
      (fun x => -A₂ x) ζ * B₁ ζ - A₁ ζ * (fun x => -B₂ x) ζ = 1 := by
  refine ⟨hA₂.neg, ?_, ?_⟩
  · convert hB₂.neg using 1; ring
  · simp only; linear_combination hW

/-- **(Q-d)** at a pole of `F` (denominator `0`), `-1/F` is a well-defined quotient with the *same* complex
dilatation formula. -/
theorem t203_mu_neg_inv_F {A₁ B₁ A₂ B₂ g : ℂ → ℂ} {z a : ℂ} (hg : DifferentiableAt ℝ g z)
    (hA₁ : HasDerivAt A₁ (B₁ (g z)) (g z)) (hB₁ : HasDerivAt B₁ (-(a * A₁ (g z))) (g z))
    (hA₂ : HasDerivAt A₂ (B₂ (g z)) (g z)) (hB₂ : HasDerivAt B₂ (-(a * A₂ (g z))) (g z))
    (hW : A₁ (g z) * B₂ (g z) - A₂ (g z) * B₁ (g z) = 1)
    (hN : A₁ (g z) + (z - g z) * B₁ (g z) ≠ 0) :
    complexDilatation
        (fun w => -1 / ((A₁ (g w) + (w - g w) * B₁ (g w)) / (A₂ (g w) + (w - g w) * B₂ (g w)))) z =
      (z - g z) ^ 2 * a * dzbar g z / (1 + (z - g z) ^ 2 * a * dz g z) := by
  obtain ⟨p1, p2, p3⟩ := t203_pole_pair_hyps (B₁ := B₁) hA₂ hB₂ hW
  rw [t203_neg_inv_F]
  exact t203_mu_F (A₁ := fun x => -A₂ x) (B₁ := fun x => -B₂ x) (A₂ := A₁) (B₂ := B₁) hg p1 p2 hA₁ hB₁ p3 hN

/-- **Wrapper in the `eq19_2_ode` form** (`w'' + (φ/2) w = 0`, `w₁w₂' - w₂w₁' = 1`): at every `z` with
`‖φ(g z)‖ ‖g z - z‖² ‖dg(z)‖ ≤ t < 2`, either `F` (denominator `≠ 0`) or `-1/F` (denominator `= 0`)
satisfies `‖∂̄‖ < ‖∂‖` and `‖μ‖ ≤ t/2` at `z`. -/
theorem t203_mu_w {w₁ w₂ g φ F : ℂ → ℂ} {z : ℂ} {t : ℝ} (hg : DifferentiableAt ℝ g z)
    (h1 : DifferentiableAt ℂ w₁ (g z)) (h1' : DifferentiableAt ℂ (deriv w₁) (g z))
    (h2 : DifferentiableAt ℂ w₂ (g z)) (h2' : DifferentiableAt ℂ (deriv w₂) (g z))
    (e1 : deriv (deriv w₁) (g z) + φ (g z) / 2 * w₁ (g z) = 0)
    (e2 : deriv (deriv w₂) (g z) + φ (g z) / 2 * w₂ (g z) = 0)
    (hW : w₁ (g z) * deriv w₂ (g z) - w₂ (g z) * deriv w₁ (g z) = 1)
    (hF : F = fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) / (w₂ (g w) + (w - g w) * deriv w₂ (g w)))
    (ht : t < 2) (hS : ‖φ (g z)‖ * ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ ≤ t) :
    (w₂ (g z) + (z - g z) * deriv w₂ (g z) ≠ 0 →
        ‖dzbar F z‖ < ‖dz F z‖ ∧ ‖complexDilatation F z‖ ≤ t / 2) ∧
      (w₂ (g z) + (z - g z) * deriv w₂ (g z) = 0 →
        ‖dzbar (fun w => -1 / F w) z‖ < ‖dz (fun w => -1 / F w) z‖ ∧
          ‖complexDilatation (fun w => -1 / F w) z‖ ≤ t / 2) := by
  obtain ⟨a1, b1⟩ := t203_ode_hasDerivAt h1 h1' e1
  obtain ⟨a2, b2⟩ := t203_ode_hasDerivAt h2 h2' e2
  subst hF
  refine ⟨fun hD => t203_F_bound_book hg a1 b1 a2 b2 hW hD ht hS, fun hD => ?_⟩
  have hN := t203_num_ne_zero hW hD
  obtain ⟨p1, p2, p3⟩ := t203_pole_pair_hyps (B₁ := deriv w₁) a2 b2 hW
  have := t203_neg_inv_F w₁ (deriv w₁) w₂ (deriv w₂) g
  simp only at this ⊢
  rw [this]
  exact t203_F_bound_book (A₁ := fun x => -w₂ x) (B₁ := fun x => -deriv w₂ x) (A₂ := w₁)
    (B₂ := deriv w₁) hg p1 p2 a1 b1 p3 hN ht hS

/-- **A-refl** (Lemma 20.3 with the invariant bound and the behaviour at `∞`; a new helper, the installed `lemma20_3` is
untouched): a bounded `K`-quasidisc `D` has a `C¹` reflection `g` of `ℂ ∖ D̄` onto `D ∖ {p}` with
`‖g z - z‖² ‖dg z‖ η_D(g z)² ≤ c₀` and `g z → p` as `z → ∞` (the proof of `lemma20_3` keeping its key bound, plus the
`∞` clause of `s20l_reflection_core`). -/
theorem t203_reflection {K : ℝ} (hK : 1 ≤ K) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ D : Set ℂ, IsKQuasidisc D K → Bornology.IsBounded D →
      ∃ (g : ℂ → ℂ) (K₁ : ℝ) (p : ℂ), p ∈ D ∧ ContDiffOn ℝ 1 g (closure D)ᶜ ∧
        IsPlanarQCReflection (closure D)ᶜ (D \ {p}) g K₁ ∧
        Tendsto g (cocompact ℂ ⊓ 𝓟 (closure D)ᶜ) (𝓝 p) ∧
        ∀ z ∈ (closure D)ᶜ, ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ * poincareDensity D (g z) ^ 2 ≤ c₀ := by
  obtain ⟨K₁, M, hK₁, hcore⟩ := s20l_reflection_core hK
  obtain ⟨M', hl2⟩ := lemma20_2 hK₁
  refine ⟨max (M' ^ 2 * M) 0, le_max_right _ _, fun D hD hb => ?_⟩
  obtain ⟨a, haD, C, hCK, hinf, hCC⟩ := s20l_mobius_transport hD hb
  obtain ⟨gt, hC1, hR, hdg, htend⟩ := hcore C _ _ hCK hinf hCC
  have hl2' := hl2 C _ _ K gt hCK hinf hCC hR
  set U := (fun z => (z - a)⁻¹) '' (closure D)ᶜ with hUdef
  set A₂ := (fun z => (z - a)⁻¹) '' D with hA₂def
  -- basic facts about `γ z = 1/(z - a)`
  have hDo : IsOpen D := hD.1.1
  have haD' : a ∉ D := fun h => haD.2 (interior_maximal subset_rfl hDo h)
  have hDco : IsOpen (closure D)ᶜ := isClosed_closure.isOpen_compl
  have hneDc : ∀ z ∈ (closure D)ᶜ, z ≠ a := fun z hz h => hz (h ▸ frontier_subset_closure haD)
  have hneD : ∀ z ∈ D, z ≠ a := fun z hz h => haD' (h ▸ hz)
  have hγ0 : ∀ z : ℂ, z ≠ a → (z - a)⁻¹ ≠ 0 := fun z hz => inv_ne_zero (sub_ne_zero.2 hz)
  have hγinj : ∀ z w : ℂ, (z - a)⁻¹ = (w - a)⁻¹ → z = w := fun z w h =>
    sub_left_injective (inv_inj.1 h)
  have hγinv : ∀ w : ℂ, a + ((w - a)⁻¹)⁻¹ = w := fun w => by rw [inv_inv]; ring
  have hA₁o : IsOpen (insert 0 U) := hR.2.2.1.1
  have hUA : insert 0 U \ {0} = U := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      exact hw.resolve_left hw0
    · intro hw
      refine ⟨mem_insert_of_mem _ hw, ?_⟩
      obtain ⟨z, hz, rfl⟩ := hw
      exact hγ0 z (hneDc z hz)
  have hUo : IsOpen U := hUA ▸ hA₁o.sdiff isClosed_singleton
  have hmemA₁ : ∀ z ∈ (closure D)ᶜ, (z - a)⁻¹ ∈ insert 0 U := fun z hz =>
    mem_insert_of_mem _ (mem_image_of_mem _ hz)
  have himg : gt '' insert 0 U = A₂ := hR.2.1
  have hgtA₂ : ∀ ζ ∈ insert 0 U, gt ζ ∈ A₂ := fun ζ hζ => himg ▸ mem_image_of_mem gt hζ
  have hA₂ : ∀ u ∈ A₂, u ≠ 0 ∧ a + u⁻¹ ∈ D := by
    rintro _ ⟨d, hd, rfl⟩
    show (d - a)⁻¹ ≠ 0 ∧ a + ((d - a)⁻¹)⁻¹ ∈ D
    exact ⟨hγ0 d (hneD d hd), by rw [hγinv]; exact hd⟩
  have hinj : InjOn gt (insert 0 U) := hR.1
  have hC1z : ∀ z ∈ (closure D)ᶜ, ContDiffAt ℝ 1 gt (z - a)⁻¹ := fun z hz =>
    hC1.contDiffAt (hA₁o.mem_nhds (hmemA₁ z hz))
  refine ⟨fun z => a + (gt (z - a)⁻¹)⁻¹, K₁, a + (gt 0)⁻¹,
    (hA₂ _ (hgtA₂ 0 (mem_insert _ _))).2, ?_, ?_, ?_, ?_⟩
  · -- `C¹`
    intro z hz
    have h1 : ContDiffAt ℝ 1 (fun w : ℂ => (w - a)⁻¹) z :=
      (contDiffAt_id.sub contDiffAt_const).fun_inv (sub_ne_zero.2 (hneDc z hz))
    have h3 := ((hC1z z hz).comp z h1).fun_inv (hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).1
    exact (contDiffAt_const.add h3).contDiffWithinAt
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- injective
      intro z₁ hz₁ z₂ hz₂ h
      have h' : gt (z₁ - a)⁻¹ = gt (z₂ - a)⁻¹ := inv_inj.1 (add_left_cancel h)
      exact hγinj z₁ z₂ (hinj (hmemA₁ z₁ hz₁) (hmemA₁ z₂ hz₂) h')
    · -- image `D ∖ {p}`
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).2, fun h => ?_⟩
        have h' : gt (z - a)⁻¹ = gt 0 := inv_inj.1 (add_left_cancel h)
        exact hγ0 z (hneDc z hz) (hinj (hmemA₁ z hz) (mem_insert _ _) h')
      · rintro ⟨hw, hwp⟩
        have hwA₂ : (w - a)⁻¹ ∈ A₂ := mem_image_of_mem _ hw
        rw [← himg] at hwA₂
        obtain ⟨ζ, hζ, hζw⟩ := hwA₂
        rcases hζ with rfl | ⟨z, hz, rfl⟩
        · exact absurd (show w = a + (gt 0)⁻¹ by rw [hζw, hγinv]) hwp
        · have hζw' : gt (z - a)⁻¹ = (w - a)⁻¹ := hζw
          refine ⟨z, hz, ?_⟩
          show a + (gt (z - a)⁻¹)⁻¹ = w
          rw [hζw', hγinv]
    · -- quasiconformality of `conj ∘ g`
      have hγc : IsConformalOnto (fun z : ℂ => (z - a)⁻¹) (closure D)ᶜ U :=
        ⟨fun z hz => (((hasDerivAt_id' z).sub_const a).fun_inv
          (sub_ne_zero.2 (hneDc z hz))).differentiableAt.differentiableWithinAt,
         fun z₁ _ z₂ _ h => hγinj z₁ z₂ h, rfl⟩
      have hq1 : IsKQC (fun z : ℂ => (z - a)⁻¹) (closure D)ᶜ 1 := isKQC_one_of_conformal hDco hγc
      have hq2 : IsKQC (fun z => conj (gt z)) U K₁ :=
        ac_t_isKQC_restrict hR.2.2.1 hUo (subset_insert _ _)
      have hh₂c : IsConformalOnto (fun u : ℂ => conj a + u⁻¹) {0}ᶜ
          ((fun u : ℂ => conj a + u⁻¹) '' {0}ᶜ) :=
        ⟨fun u hu => ((hasDerivAt_inv hu).const_add (conj a)).differentiableAt.differentiableWithinAt,
         fun u₁ _ u₂ _ h => inv_inj.1 (add_left_cancel h), rfl⟩
      have hq3 : IsKQC (fun u : ℂ => conj a + u⁻¹) {0}ᶜ 1 :=
        isKQC_one_of_conformal isOpen_compl_singleton hh₂c
      have s1 := thm7_1_comp hq1 hq2 (subset_refl _)
      have s2 := thm7_1_comp s1 hq3 (by
        rintro _ ⟨z, hz, rfl⟩
        exact (map_ne_zero (starRingEnd ℂ)).2 (hA₂ _ (hgtA₂ _ (hmemA₁ z hz))).1)
      rw [one_mul, mul_one] at s2
      refine ad_isKQC_congr s2 fun z _ => ?_
      show conj (a + (gt (z - a)⁻¹)⁻¹) = conj a + (conj (gt (z - a)⁻¹))⁻¹
      rw [map_add, map_inv₀]
    · -- boundary behaviour
      rintro q ⟨hq1, -⟩
      have hqcl : q ∈ closure (closure D)ᶜ := frontier_subset_closure hq1
      rw [frontier_compl] at hq1
      have hqD : q ∈ frontier D := frontier_closure_subset hq1
      have hqnD : q ∉ D := fun h => hqD.2 (interior_maximal subset_rfl hDo h)
      by_cases hqa : q = a
      · rw [hqa]
        have hsub : Tendsto (fun z : ℂ => z - a) (𝓝[(closure D)ᶜ] a) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
            sub_ne_zero.2 (hneDc z hz)⟩
          have : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 (a - a)) := tendsto_id.sub_const a
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        have hγt : Tendsto (fun z : ℂ => (z - a)⁻¹) (𝓝[(closure D)ᶜ] a)
            (Bornology.cobounded ℂ ⊓ 𝓟 (insert 0 U)) :=
          tendsto_inf.2 ⟨tendsto_inv₀_nhdsNE_zero.comp hsub,
            tendsto_principal.2 (eventually_nhdsWithin_of_forall hmemA₁)⟩
        have htend' : Tendsto gt (Bornology.cobounded ℂ ⊓ 𝓟 (insert 0 U))
            (Bornology.cobounded ℂ) := by
          rw [Metric.cobounded_eq_cocompact]
          exact htend
        have h3 := (tendsto_inv₀_cobounded.comp (htend'.comp hγt)).const_add a
        rw [add_zero] at h3
        exact h3
      · have hqa' : q - a ≠ 0 := sub_ne_zero.2 hqa
        have hcont : ContinuousAt (fun z : ℂ => (z - a)⁻¹) q :=
          (continuousAt_id.sub continuousAt_const).inv₀ hqa'
        have hfr : (q - a)⁻¹ ∈ frontier (insert 0 U) ∩ frontier A₂ := by
          refine ⟨⟨closure_mono (subset_insert _ _) (mem_closure_image hcont hqcl), fun h => ?_⟩,
            ⟨mem_closure_image hcont (frontier_subset_closure hqD), fun h => ?_⟩⟩
          · rcases interior_subset h with h0 | ⟨z, hz, hzq⟩
            · exact hγ0 q hqa h0
            · have hzq' : z = q := hγinj z q hzq
              rw [hzq'] at hz
              exact hz hqD.1
          · obtain ⟨d, hd, hdq⟩ := interior_subset h
            have hdq' : d = q := hγinj d q hdq
            rw [hdq'] at hd
            exact hqnD hd
        have h1 := hR.2.2.2 _ hfr
        have h2 : Tendsto (fun z : ℂ => (z - a)⁻¹) (𝓝[(closure D)ᶜ] q) (𝓝[insert 0 U] (q - a)⁻¹) :=
          tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds,
            eventually_nhdsWithin_of_forall hmemA₁⟩
        have h3 := ((h1.comp h2).inv₀ (hγ0 q hqa)).const_add a
        rw [hγinv q] at h3
        exact h3
  · -- the behaviour at `∞`: `γ z → 0 = γ ∞`, `g̃` is continuous at `0`, so `g z → a + (g̃ 0)⁻¹ = p`
    have hγ : Tendsto (fun z : ℂ => (z - a)⁻¹) (cocompact ℂ ⊓ 𝓟 (closure D)ᶜ) (𝓝 0) := by
      have h1 : Tendsto (fun z : ℂ => (z - a)⁻¹) (cocompact ℂ) (𝓝 0) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded a)
      exact h1.mono_left inf_le_left
    have hcont : ContinuousAt gt 0 :=
      (hC1.contDiffAt (hA₁o.mem_nhds (mem_insert _ _))).continuousAt
    exact ((hcont.tendsto.comp hγ).inv₀ (hA₂ _ (hgtA₂ 0 (mem_insert _ _))).1).const_add a
  · -- the Möbius-invariant bound
    intro z hz
    have hza := hneDc z hz
    have hζ := hmemA₁ z hz
    obtain ⟨hu0, hw⟩ := hA₂ _ (hgtA₂ _ hζ)
    obtain ⟨φ, hφ, -⟩ := s13x_th_exists_disc_uniformizer hD.1
    have hP := s20l_density_mobius hDo hφ haD' hw
    rw [← hA₂def, add_sub_cancel_left, inv_inv] at hP
    have hηpos : 0 < poincareDensity D (a + (gt (z - a)⁻¹)⁻¹) := by
      rw [(poincareDensity_well_defined hDo hφ hφ hw).2]
      have h1 := deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hw
      have h2 : ‖φ (a + (gt (z - a)⁻¹)⁻¹)‖ < 1 := mem_ball_zero_iff.1 (hφ.mapsTo hw)
      have h3 : 0 < 1 - ‖φ (a + (gt (z - a)⁻¹)⁻¹)‖ ^ 2 := by
        nlinarith [norm_nonneg (φ (a + (gt (z - a)⁻¹)⁻¹))]
      exact div_pos (mul_pos two_pos (norm_pos_iff.2 h1)) h3
    have hr2 : 0 < ‖gt (z - a)⁻¹‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
    have hηA : 0 < poincareDensity A₂ (gt (z - a)⁻¹) :=
      (mul_pos_iff_of_pos_right hr2).1 (hP ▸ hηpos)
    have hfd := s20l_a3_fderiv_le hza ((hC1z z hz).differentiableAt one_ne_zero) hu0
    simp only [norm_inv] at hfd
    have hdist := s20l_a3_norm_sub hu0 hza
    rw [norm_inv] at hdist
    have hkey := s20l_a3_real (norm_nonneg _) hηA (hl2' _ hζ) (norm_nonneg _) (hdg _ hζ)
      (norm_pos_iff.2 hu0) (norm_pos_iff.2 (sub_ne_zero.2 hza)) hdist hfd
    rw [hP] at hkey
    exact hkey.trans (le_max_left _ _)

/-- Schwarz–Pick for the unit disc: a holomorphic self-map `f` of `Δ` satisfies `|f'(a)| (1 - |a|²) ≤ 1 - |f(a)|²`
(Schwarz's lemma at the centre for `M_{f a} ∘ f ∘ M_{-a}`, which fixes `0`; a copy of the S30 `schwarz_pick_unitDisc`,
which is not imported here). -/
theorem t203_mono_schwarz_pick {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) {a : ℂ} (ha : a ∈ unitDisc) :
    ‖deriv f a‖ * (1 - ‖a‖ ^ 2) ≤ 1 - ‖f a‖ ^ 2 := by
  have hna : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hnna : ‖(-a)‖ < 1 := by rwa [norm_neg]
  have hnb : ‖f a‖ < 1 := mem_ball_zero_iff.mp (hmaps ha)
  have hz0 : ‖(0 : ℂ)‖ < 1 := by norm_num
  have hpa : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hpb : (0 : ℝ) < 1 - ‖f a‖ ^ 2 := by nlinarith [norm_nonneg (f a)]
  have hb0 : blaschke (-a) 0 = a := by simp [blaschke]
  have hbb : blaschke (f a) (f a) = 0 := by simp [blaschke]
  have hsub : ∀ z ∈ unitDisc, blaschke (-a) z ∈ unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hnna (mem_ball_zero_iff.mp hz))
  have hg0 : blaschke (f a) (f (blaschke (-a) 0)) = 0 := by
    rw [hb0]
    exact hbb
  have hmapsg : MapsTo (fun z => blaschke (f a) (f (blaschke (-a) z))) unitDisc unitDisc :=
    fun z hz => mem_ball_zero_iff.mpr
      (blaschke_mem_unitDisc hnb (mem_ball_zero_iff.mp (hmaps (hsub z hz))))
  have hdg : DifferentiableOn ℂ (fun z => blaschke (f a) (f (blaschke (-a) z))) unitDisc :=
    (differentiableOn_blaschke hnb).comp (hf.comp (differentiableOn_blaschke hnna) hsub)
      (fun z hz => hmaps (hsub z hz))
  have hschwarz : ‖deriv (fun z => blaschke (f a) (f (blaschke (-a) z))) 0‖ ≤ 1 := by
    refine Complex.norm_deriv_le_one_of_mapsTo_ball hdg ?_ one_pos
    rw [hg0]
    exact fun z hz => ball_subset_closedBall (hmapsg hz)
  have hfa : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  have h1 : HasDerivAt (blaschke (-a)) (1 - a * conj a) 0 := by
    have h := hasDerivAt_blaschke hnna hz0
    simpa using h
  have hfa' : HasDerivAt f (deriv f a) (blaschke (-a) 0) := by rw [hb0]; exact hfa
  have hk : HasDerivAt (fun z => f (blaschke (-a) z)) (deriv f a * (1 - a * conj a)) 0 :=
    hfa'.comp 0 h1
  have h3 : HasDerivAt (blaschke (f a))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2) (f (blaschke (-a) 0)) := by
    rw [hb0]
    exact hasDerivAt_blaschke hnb hnb
  have hchain0 : HasDerivAt (blaschke (f a) ∘ fun z => f (blaschke (-a) z))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2 *
        (deriv f a * (1 - a * conj a))) 0 := h3.comp 0 hk
  have hchain : HasDerivAt (fun z => blaschke (f a) (f (blaschke (-a) z)))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2 *
        (deriv f a * (1 - a * conj a))) 0 := hchain0
  have hcb : (1 : ℂ) - f a * conj (f a) = ((1 - ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hcb' : (1 : ℂ) - conj (f a) * f a = ((1 - ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm]; exact hcb
  have hca : (1 : ℂ) - a * conj a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hchain.deriv, hcb, hcb', hca, norm_mul, norm_mul, norm_div, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hpa, abs_of_pos hpb, div_mul_eq_mul_div,
    div_le_one (by positivity)] at hschwarz
  nlinarith [hschwarz, hpb, norm_nonneg (deriv f a)]

/-- **A-mono** (Schwarz–Pick): for open `D' ⊆ D`, both conformally equivalent to `Δ`, `η_D ≤ η_{D'}` on `D'`
(`φ ∘ φ'⁻¹ : Δ → Δ` is holomorphic, so it contracts the Poincaré metric of `Δ`). -/
theorem t203_density_mono {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D') (hsub : D' ⊆ D) {φ φ' : ℂ → ℂ}
    (hφ : IsConformalOnto φ D unitDisc) (hφ' : IsConformalOnto φ' D' unitDisc) {w : ℂ} (hw : w ∈ D') :
    poincareDensity D w ≤ poincareDensity D' w := by
  have hwD : w ∈ D := hsub hw
  rw [(poincareDensity_well_defined hD hφ hφ hwD).2, (poincareDensity_well_defined hD' hφ' hφ' hw).2]
  set χ := Function.invFunOn φ' D' with hχdef
  have hχ : IsConformalOnto χ unitDisc D' := hφ'.symm hD'
  have hu : φ' w ∈ unitDisc := hφ'.mapsTo hw
  have hχu : χ (φ' w) = w := hφ'.2.1.leftInvOn_invFunOn hw
  have hright : ∀ z ∈ unitDisc, φ' (χ z) = z := by
    intro z hz
    rw [← hφ'.2.2] at hz
    exact Function.invFunOn_eq hz
  have hχmaps : MapsTo χ unitDisc D' := hχ.mapsTo
  have hhd : DifferentiableOn ℂ (fun z => φ (χ z)) unitDisc :=
    hφ.1.comp hχ.1 (fun z hz => hsub (hχmaps hz))
  have hhmaps : MapsTo (fun z => φ (χ z)) unitDisc unitDisc :=
    fun z hz => hφ.mapsTo (hsub (hχmaps hz))
  have hsp := t203_mono_schwarz_pick hhd hhmaps hu
  -- the chain rule at `u = φ' w`, and `(φ' ∘ χ)' = 1`
  have hχd : HasDerivAt χ (deriv χ (φ' w)) (φ' w) :=
    (hχ.1.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hφd : HasDerivAt φ (deriv φ w) (χ (φ' w)) := by
    rw [hχu]
    exact (hφ.1.differentiableAt (hD.mem_nhds hwD)).hasDerivAt
  have hφ'd : HasDerivAt φ' (deriv φ' w) (χ (φ' w)) := by
    rw [hχu]
    exact (hφ'.1.differentiableAt (hD'.mem_nhds hw)).hasDerivAt
  have hh : deriv (fun z => φ (χ z)) (φ' w) = deriv φ w * deriv χ (φ' w) :=
    (hφd.comp (φ' w) hχd).deriv
  have hid : HasDerivAt (fun z => φ' (χ z)) (deriv φ' w * deriv χ (φ' w)) (φ' w) :=
    hφ'd.comp (φ' w) hχd
  have hev : (fun z => φ' (χ z)) =ᶠ[𝓝 (φ' w)] id := by
    filter_upwards [isOpen_ball.mem_nhds hu] with z hz using hright z hz
  have hbc : deriv φ' w * deriv χ (φ' w) = 1 :=
    (hid.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_id (φ' w))
  have hbc' : ‖deriv φ' w‖ * ‖deriv χ (φ' w)‖ = 1 := by
    rw [← norm_mul, hbc, norm_one]
  rw [hh, hχu, norm_mul] at hsp
  have hp1 : 0 < 1 - ‖φ w‖ ^ 2 := by
    have := mem_ball_zero_iff.1 (show φ w ∈ unitDisc from hφ.mapsTo hwD)
    nlinarith [norm_nonneg (φ w)]
  have hp2 : 0 < 1 - ‖φ' w‖ ^ 2 := by
    have := mem_ball_zero_iff.1 hu
    nlinarith [norm_nonneg (φ' w)]
  have key : ‖deriv φ w‖ * (1 - ‖φ' w‖ ^ 2) ≤ ‖deriv φ' w‖ * (1 - ‖φ w‖ ^ 2) := by
    calc ‖deriv φ w‖ * (1 - ‖φ' w‖ ^ 2)
        = (‖deriv φ' w‖ * ‖deriv χ (φ' w)‖) * (‖deriv φ w‖ * (1 - ‖φ' w‖ ^ 2)) := by
          rw [hbc', one_mul]
      _ = ‖deriv φ' w‖ * (‖deriv φ w‖ * ‖deriv χ (φ' w)‖ * (1 - ‖φ' w‖ ^ 2)) := by ring
      _ ≤ ‖deriv φ' w‖ * (1 - ‖φ w‖ ^ 2) := mul_le_mul_of_nonneg_left hsp (norm_nonneg _)
  rw [div_le_div_iff₀ hp1 hp2]
  linarith

/-- **A-norm** (monotonicity of the Schwarzian norm): for open `D' ⊆ D`, both conformally equivalent to `Δ`,
`‖S_f‖_{D'} ≤ ‖S_f‖_D` (termwise, since `0 < η_D ≤ η_{D'}` on `D'`). -/
theorem t203_schwarzianNorm_mono {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D') (hsub : D' ⊆ D)
    {φ φ' : ℂ → ℂ} (hφ : IsConformalOnto φ D unitDisc) (hφ' : IsConformalOnto φ' D' unitDisc) (f : ℂ → ℂ) :
    schwarzianNorm f D' ≤ schwarzianNorm f D := by
  unfold schwarzianNorm
  refine iSup₂_le fun z hz => le_iSup₂_of_le z (hsub hz) ?_
  apply ENNReal.ofReal_le_ofReal
  have hpos := s20l_a2_density_pos hD hφ (hsub hz)
  have hle := t203_density_mono hD hD' hsub hφ hφ' hz
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)

/-- The point `(a : b)` of `ℂ̄`: `a / b`, or `∞` when `b = 0`. -/
def t203_ratio (a b : ℂ) : ExtPlane := if b = 0 then extInf else ((a / b : ℂ) : ExtPlane)

/-- `neh_germ` on an arbitrary open set `D`: with `f = M ∘ (w₁/w₂)` at the good points (Theorem 19.1,
uniqueness), `f` agrees with `W₁/W₂ = (a w₁ + b w₂)/(c w₁ + d w₂)` on a punctured neighbourhood of every
point of `D`, and `W₂` does not vanish there. -/
theorem t203_ode_germ {D : Set ℂ} (hDo : IsOpen D) {f w₁ w₂ : ℂ → ℂ} (hf : IsLocUnivMero f D)
    (hw₁ : DifferentiableOn ℂ w₁ D) (hw₂ : DifferentiableOn ℂ w₂ D)
    (hwr : ∀ z ∈ D, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hrel : ∀ z ∈ D, AnalyticAt ℂ f z → AnalyticAt ℂ (fun z => w₁ z / w₂ z) z →
      c * (w₁ z / w₂ z) + d ≠ 0 → f z = (a * (w₁ z / w₂ z) + b) / (c * (w₁ z / w₂ z) + d))
    {z : ℂ} (hz : z ∈ D) :
    (∀ᶠ y in 𝓝[≠] z, c * w₁ y + d * w₂ y ≠ 0) ∧
      f =ᶠ[𝓝[≠] z] fun y => (a * w₁ y + b * w₂ y) / (c * w₁ y + d * w₂ y) := by
  have hw₁a : ∀ y ∈ D, AnalyticAt ℂ w₁ y := fun y hy => hw₁.analyticAt (hDo.mem_nhds hy)
  have hw₂a : ∀ y ∈ D, AnalyticAt ℂ w₂ y := fun y hy => hw₂.analyticAt (hDo.mem_nhds hy)
  have hW₂a : AnalyticAt ℂ (fun y => c * w₁ y + d * w₂ y) z :=
    (analyticAt_const.mul (hw₁a z hz)).add (analyticAt_const.mul (hw₂a z hz))
  have hW₂' : deriv (fun y => c * w₁ y + d * w₂ y) z = c * deriv w₁ z + d * deriv w₂ z :=
    (((hw₁a z hz).differentiableAt.hasDerivAt.const_mul c).add
      ((hw₂a z hz).differentiableAt.hasDerivAt.const_mul d)).deriv
  have hW₂ne : ∀ᶠ y in 𝓝[≠] z, c * w₁ y + d * w₂ y ≠ 0 := by
    apply neh_eventually_ne_zero hW₂a
    by_cases h0 : c * w₁ z + d * w₂ z = 0
    · right
      rw [hW₂']
      intro h1
      have hw := neh_wronskian_comb (a := a) (b := b) (c := c) (d := d) (hwr z hz)
      apply hdet
      rw [← hw, h0, h1]
      ring
    · exact Or.inl h0
  have hw₂ne : ∀ᶠ y in 𝓝[≠] z, w₂ y ≠ 0 := by
    apply neh_eventually_ne_zero (hw₂a z hz)
    by_cases h0 : w₂ z = 0
    · right
      intro h1
      have hw := hwr z hz
      rw [h0, h1] at hw
      simp at hw
    · exact Or.inl h0
  have hmem : ∀ᶠ y in 𝓝[≠] z, y ∈ D := (hDo.eventually_mem hz).filter_mono nhdsWithin_le_nhds
  refine ⟨hW₂ne, ?_⟩
  filter_upwards [hmem, neh_eventually_analyticAt hf hz, hw₂ne, hW₂ne] with y hy hfy hw₂y hW₂y
  have hgy : AnalyticAt ℂ (fun z => w₁ z / w₂ z) y := (hw₁a y hy).div (hw₂a y hy) hw₂y
  have hden : c * (w₁ y / w₂ y) + d ≠ 0 := by
    have e : c * (w₁ y / w₂ y) + d = (c * w₁ y + d * w₂ y) / w₂ y := by
      field_simp
    rw [e]
    exact div_ne_zero hW₂y hw₂y
  rw [hrel y hy hfy hgy hden]
  field_simp

/-- The first and second derivatives of a constant-coefficient combination `p v₁ + q v₂` of two
functions holomorphic on an open set `D`, at a point of `D`. -/
theorem t203_ode_comb_deriv {D : Set ℂ} (hDo : IsOpen D) {v₁ v₂ : ℂ → ℂ}
    (hv₁ : DifferentiableOn ℂ v₁ D) (hv₂ : DifferentiableOn ℂ v₂ D) (p q : ℂ) {z : ℂ} (hz : z ∈ D) :
    deriv (fun y => p * v₁ y + q * v₂ y) z = p * deriv v₁ z + q * deriv v₂ z ∧
      deriv (deriv fun y => p * v₁ y + q * v₂ y) z =
        p * deriv (deriv v₁) z + q * deriv (deriv v₂) z := by
  have h1 : ∀ y ∈ D, deriv (fun y => p * v₁ y + q * v₂ y) y = p * deriv v₁ y + q * deriv v₂ y := by
    intro y hy
    exact (((hv₁.differentiableAt (hDo.mem_nhds hy)).hasDerivAt.const_mul p).add
      ((hv₂.differentiableAt (hDo.mem_nhds hy)).hasDerivAt.const_mul q)).deriv
  refine ⟨h1 z hz, ?_⟩
  have hev : deriv (fun y => p * v₁ y + q * v₂ y) =ᶠ[𝓝 z]
      fun y => p * deriv v₁ y + q * deriv v₂ y := by
    filter_upwards [hDo.mem_nhds hz] with y hy
    exact h1 y hy
  rw [hev.deriv_eq]
  exact ((((hv₁.deriv hDo).differentiableAt (hDo.mem_nhds hz)).hasDerivAt.const_mul p).add
    (((hv₂.deriv hDo).differentiableAt (hDo.mem_nhds hz)).hasDerivAt.const_mul q)).deriv

/-- The point of `ℂ̄` of a germ `f = W₁/W₂` (on a punctured neighbourhood of `z`), with `W₁`, `W₂`
analytic at `z` without a common zero there: `meroToExt f z = (W₁ z : W₂ z)`. -/
theorem t203_ode_meroToExt {f W₁ W₂ : ℂ → ℂ} {z : ℂ} (hW₁ : AnalyticAt ℂ W₁ z)
    (hW₂ : AnalyticAt ℂ W₂ z) (hne : W₂ z = 0 → W₁ z ≠ 0) (hW₂ne : ∀ᶠ y in 𝓝[≠] z, W₂ y ≠ 0)
    (hgerm : f =ᶠ[𝓝[≠] z] fun y => W₁ y / W₂ y) :
    meroToExt f z = t203_ratio (W₁ z) (W₂ z) := by
  have hNF := toMeromorphicNFAt_eventuallyEq_nhds_congr hgerm
  unfold meroToExt t203_ratio
  by_cases h0 : W₂ z = 0
  · have hnord : ¬ 0 ≤ meromorphicOrderAt f z := by
      intro hord
      rw [meromorphicOrderAt_congr hgerm] at hord
      have hm : MeromorphicAt (fun y => W₁ y / W₂ y) z := hW₁.meromorphicAt.div hW₂.meromorphicAt
      have hN := hm.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord
      exact (neh_dict_analytic hW₁ hW₂ hne hW₂ne hm.eq_nhdsNE_toMeromorphicNFAt.symm hN).1 h0
    rw [ite_eq_left h0, ite_eq_right hnord]
  · have hA : AnalyticAt ℂ (fun y => W₁ y / W₂ y) z := hW₁.div hW₂ h0
    have hord : 0 ≤ meromorphicOrderAt f z := by
      rw [meromorphicOrderAt_congr hgerm]
      exact hA.meromorphicOrderAt_nonneg
    rw [ite_eq_right h0, ite_eq_left hord, hNF.eq_of_nhds, toMeromorphicNFAt_eq_self.mpr hA.meromorphicNFAt]

/-- **A-ode** (Q4): on a `K`-quasidisc (simply connected), a locally univalent meromorphic `f` is `w₁/w₂` for
solutions of `w'' + (S_f/2) w = 0` with Wronskian `w₁w₂' - w₂w₁' = 1`: `meroToExt f z = (w₁ z : w₂ z)` on `D`
(`eq19_2_ode` with `φ = S_f` (`schwarzian_holomorphic`), `thm19_1_unique`, and a normalized Möbius change of basis of the
solutions, as `neh_germ` does on `Δ`). -/
theorem t203_ode_pair {D : Set ℂ} {K : ℝ} (hD : IsKQuasidisc D K) {f : ℂ → ℂ} (hf : IsLocUnivMero f D) :
    ∃ w₁ w₂ : ℂ → ℂ, DifferentiableOn ℂ w₁ D ∧ DifferentiableOn ℂ w₂ D ∧
      (∀ z ∈ D, deriv (deriv w₁) z + schwarzian f z / 2 * w₁ z = 0 ∧
        deriv (deriv w₂) z + schwarzian f z / 2 * w₂ z = 0 ∧ w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) ∧
      ∀ z ∈ D, meroToExt f z = t203_ratio (w₁ z) (w₂ z) := by
  have hH := t203_hsc_of_isKQuasidisc hD
  have hDo : IsOpen D := hH.1
  have hDc : IsConnected D := hH.2.1
  have hDs : IsSimplyConnected D := hH.2.2.1
  have hΦ : DifferentiableOn ℂ (schwarzian f) D := schwarzian_holomorphic hDo hf
  -- the fundamental system of `v'' + (S_f/2) v = 0` and the Möbius relation `f = M ∘ (v₁/v₂)`
  obtain ⟨v₁, v₂, hv₁, hv₂, hode, hg, hSg⟩ := eq19_2_ode hDo hDc hDs hΦ
  obtain ⟨a, b, c, d, hdet, hrel⟩ := thm19_1_unique hDo hDc hf hg fun z hz => (hSg z hz).symm
  have hrel0 : ∀ z ∈ D, AnalyticAt ℂ f z → AnalyticAt ℂ (fun z => v₁ z / v₂ z) z →
      c * (v₁ z / v₂ z) + d ≠ 0 → f z = (a * (v₁ z / v₂ z) + b) / (c * (v₁ z / v₂ z) + d) := hrel
  have hwr : ∀ z ∈ D, v₁ z * deriv v₂ z - v₂ z * deriv v₁ z = 1 := fun z hz => (hode z hz).2.2
  -- normalize the determinant: `s² = ad - bc`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a * d - b * c) two_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hs]
    ring
  have hdet' : a / s * (d / s) - b / s * (c / s) = 1 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← hs, pow_two]
    exact div_self (mul_ne_zero hs0 hs0)
  have hdet0 : a / s * (d / s) - b / s * (c / s) ≠ 0 := by
    rw [hdet']
    exact one_ne_zero
  have hrel' : ∀ z ∈ D, AnalyticAt ℂ f z → AnalyticAt ℂ (fun z => v₁ z / v₂ z) z →
      c / s * (v₁ z / v₂ z) + d / s ≠ 0 →
        f z = (a / s * (v₁ z / v₂ z) + b / s) / (c / s * (v₁ z / v₂ z) + d / s) := by
    intro z hz hA hB hne
    have e1 : c / s * (v₁ z / v₂ z) + d / s = (c * (v₁ z / v₂ z) + d) / s := by ring
    have e2 : a / s * (v₁ z / v₂ z) + b / s = (a * (v₁ z / v₂ z) + b) / s := by ring
    have hne' : c * (v₁ z / v₂ z) + d ≠ 0 := by
      intro h
      apply hne
      rw [e1, h, zero_div]
    rw [hrel0 z hz hA hB hne', e1, e2, div_div_div_cancel_right₀ hs0]
  have hDw : ∀ p q : ℂ, DifferentiableOn ℂ (fun y => p * v₁ y + q * v₂ y) D := fun p q =>
    (hv₁.const_mul p).add (hv₂.const_mul q)
  refine ⟨fun y => a / s * v₁ y + b / s * v₂ y, fun y => c / s * v₁ y + d / s * v₂ y,
    hDw _ _, hDw _ _, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨e1, e1'⟩ := t203_ode_comb_deriv hDo hv₁ hv₂ (a / s) (b / s) hz
    obtain ⟨e2, e2'⟩ := t203_ode_comb_deriv hDo hv₁ hv₂ (c / s) (d / s) hz
    obtain ⟨o1, o2, -⟩ := hode z hz
    refine ⟨?_, ?_, ?_⟩
    · rw [e1']
      linear_combination (a / s) * o1 + (b / s) * o2
    · rw [e2']
      linear_combination (c / s) * o1 + (d / s) * o2
    · rw [e1, e2]
      exact (neh_wronskian_comb (a := a / s) (b := b / s) (c := c / s) (d := d / s)
        (hwr z hz)).trans hdet'
  · obtain ⟨hne2, hgerm⟩ := t203_ode_germ hDo hf hv₁ hv₂ hwr hdet0 hrel' hz
    have hv₁a := hv₁.analyticAt (hDo.mem_nhds hz)
    have hv₂a := hv₂.analyticAt (hDo.mem_nhds hz)
    refine t203_ode_meroToExt (W₁ := fun y => a / s * v₁ y + b / s * v₂ y)
      (W₂ := fun y => c / s * v₁ y + d / s * v₂ y)
      ((analyticAt_const.mul hv₁a).add (analyticAt_const.mul hv₂a))
      ((analyticAt_const.mul hv₁a).add (analyticAt_const.mul hv₂a)) ?_ hne2 hgerm
    intro h0 h1
    have hw := neh_wronskian_comb (a := a / s) (b := b / s) (c := c / s) (d := d / s) (hwr z hz)
    rw [hdet', h0, h1] at hw
    simp at hw

/-- Every point of `ℂ̄` is sent to a finite point by some homeomorphism of `ℂ̄` (the identity, or the
Möbius inversion `w ↦ 1/w` when the point is `∞`). -/
theorem t203_cov_exists_homeo_ne_inf (y : ExtPlane) :
    ∃ M : ExtPlane ≃ₜ ExtPlane, M y ≠ extInf := by
  by_cases hy : y = extInf
  · refine ⟨mobiusHomeomorph 0 1 1 0 (by norm_num), ?_⟩
    rw [mobiusHomeomorph_apply, hy, mobiusExt_infty_of_ne one_ne_zero]
    exact OnePoint.coe_ne_infty _
  · exact ⟨Homeomorph.refl _, hy⟩

/-- Every point of `ℂ̄` is sent to `∞` by some homeomorphism of `ℂ̄` (the identity, or the Möbius
map `w ↦ 1/(w - a)` when the point is `a ∈ ℂ`). -/
theorem t203_cov_exists_homeo_eq_inf (q : ExtPlane) :
    ∃ M : ExtPlane ≃ₜ ExtPlane, M q = extInf := by
  induction q using OnePoint.rec with
  | infty => exact ⟨Homeomorph.refl _, rfl⟩
  | coe a =>
    refine ⟨mobiusHomeomorph 0 1 1 (-a) (by norm_num), ?_⟩
    rw [mobiusHomeomorph_apply]
    exact mobiusExt_coe_of_eq_zero (by ring)

/-- Openness at finite points: if `F : ℂ̄ → ℂ̄` is continuous and injective near every finite point,
then `F` maps open subsets of `ℂ` to open subsets of `ℂ̄` (invariance of domain in the finite chart
at the image point, moved off `∞` by a Möbius map). -/
theorem t203_cov_isOpen_image {F : ExtPlane → ExtPlane} (hF : Continuous F)
    (hloc : ∀ z : ℂ, ∃ U ∈ 𝓝 (z : ExtPlane), InjOn F U) {W : Set ℂ} (hW : IsOpen W) :
    IsOpen (F '' (((↑) : ℂ → ExtPlane) '' W)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨_, ⟨z, hzW, rfl⟩, rfl⟩
  obtain ⟨M, hM⟩ := t203_cov_exists_homeo_ne_inf (F z)
  obtain ⟨V, hV, hinj⟩ := hloc z
  have hemb : IsOpenEmbedding ((↑) : ℂ → ExtPlane) := OnePoint.isOpenEmbedding_coe
  have hHc : Continuous fun w : ℂ => M (F w) := M.continuous.comp (hF.comp OnePoint.continuous_coe)
  have hO : (fun w : ℂ => M (F w)) ⁻¹' range ((↑) : ℂ → ExtPlane) ∈ 𝓝 z :=
    hHc.continuousAt.preimage_mem_nhds
      (OnePoint.isOpen_range_coe.mem_nhds (OnePoint.ne_infty_iff_exists.mp hM))
  have hV' : ((↑) : ℂ → ExtPlane) ⁻¹' V ∈ 𝓝 z :=
    OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hV
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem (inter_mem (hW.mem_nhds hzW) hO) hV')
  have hcoe : ∀ w ∈ ball z r,
      (((hemb.toOpenPartialHomeomorph _).symm (M (F w)) : ℂ) : ExtPlane) = M (F w) :=
    fun w hw => hemb.toOpenPartialHomeomorph_right_inv _ (hball hw).1.2
  have hhc : ContinuousOn (fun w : ℂ => (hemb.toOpenPartialHomeomorph _).symm (M (F w)))
      (ball z r) := by
    refine (hemb.toOpenPartialHomeomorph _).continuousOn_symm.comp hHc.continuousOn ?_
    intro w hw
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact (hball hw).1.2
  have hhi : InjOn (fun w : ℂ => (hemb.toOpenPartialHomeomorph _).symm (M (F w))) (ball z r) := by
    intro w₁ h₁ w₂ h₂ heq
    have h1 : M (F w₁) = M (F w₂) := by
      rw [← hcoe w₁ h₁, ← hcoe w₂ h₂]
      exact congrArg _ heq
    exact OnePoint.coe_injective (hinj (hball h₁).2 (hball h₂).2 (M.injective h1))
  have hopen := isOpen_image_of_continuousOn_injOn isOpen_ball hhc hhi
  refine Filter.mem_of_superset
    ((M.symm.isOpenMap _ (OnePoint.isOpenMap_coe _ hopen)).mem_nhds ?_) ?_
  · refine ⟨_, ⟨_, ⟨z, mem_ball_self hr, rfl⟩, rfl⟩, ?_⟩
    rw [hcoe z (mem_ball_self hr)]
    exact M.symm_apply_apply _
  · rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    refine ⟨w, ⟨w, (hball hw).1.1, rfl⟩, ?_⟩
    rw [hcoe w hw]
    exact (M.symm_apply_apply _).symm

/-- A fibre `{z ∈ ℂ | F z = q}` of a map injective near every finite point is discrete in `ℂ`, hence
countable (`ℂ` is hereditarily Lindelöf). -/
theorem t203_cov_fiber_countable {F : ExtPlane → ExtPlane}
    (hloc : ∀ z : ℂ, ∃ U ∈ 𝓝 (z : ExtPlane), InjOn F U) (q : ExtPlane) :
    {z : ℂ | F z = q}.Countable := by
  refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (IsDiscrete.of_nhdsWithin fun z hz => ?_)
  obtain ⟨V, hV, hinj⟩ := hloc z
  rw [le_pure_iff]
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨_, OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hV, ?_⟩
  rintro w ⟨hwV, hw⟩
  exact OnePoint.coe_injective (hinj hwV (mem_of_mem_nhds hV) (hw.trans hz.symm))

/-- The case `F ∞ = ∞` of `t203_covering`: off the countable fibre `Z = F⁻¹(∞) ∩ ℂ`, `F` is a proper
local homeomorphism of the connected `U = ℂ ∖ Z` onto `ℂ`, hence bijective
(`t203_bijective_of_isLocalHomeomorph_isProperMap`); and `Z = ∅`, since near a point of `Z` and near `∞`
the values of `F` would fill a punctured neighbourhood of `∞` twice. -/
theorem t203_cov_of_inf {F : ExtPlane → ExtPlane} (hF : Continuous F)
    (hloc : ∀ z : ℂ, ∃ U ∈ 𝓝 (z : ExtPlane), InjOn F U) (hinf : F extInf = extInf) :
    Function.Bijective F := by
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {z : ℂ | F z = extInf}ᶜ := ⟨_, rfl⟩
  have hUmem : ∀ z : ℂ, z ∈ U ↔ F z ≠ extInf := fun z => by rw [hU]; exact Iff.rfl
  have hZc : {z : ℂ | F z = extInf}.Countable := t203_cov_fiber_countable hloc extInf
  have hUconn : IsConnected U := by
    rw [hU]
    exact hZc.isConnected_compl_of_one_lt_rank (by simp)
  have hUo : IsOpen U := by
    rw [hU]
    exact (OnePoint.isClosed_infty.preimage (hF.comp OnePoint.continuous_coe)).isOpen_compl
  have hUd : Dense U := by
    rw [hU]
    exact hZc.dense_compl ℝ
  have hpc : PreconnectedSpace U := Subtype.preconnectedSpace hUconn.isPreconnected
  have hne : Nonempty U := hUconn.nonempty.to_subtype
  choose p hpcoe using fun u : U => OnePoint.ne_infty_iff_exists.mp ((hUmem u).mp u.2)
  have hpcont : Continuous p := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff]
    have : ((↑) : ℂ → ExtPlane) ∘ p = F ∘ ((↑) : ℂ → ExtPlane) ∘ Subtype.val := funext hpcoe
    rw [this]
    exact hF.comp (OnePoint.continuous_coe.comp continuous_subtype_val)
  have hpopen : IsOpenMap p := by
    intro W hW
    have hWo : IsOpen (F '' (((↑) : ℂ → ExtPlane) '' (Subtype.val '' W))) :=
      t203_cov_isOpen_image hF hloc (hUo.isOpenMap_subtype_val W hW)
    have heq : p '' W =
        ((↑) : ℂ → ExtPlane) ⁻¹' (F '' (((↑) : ℂ → ExtPlane) '' (Subtype.val '' W))) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, (hpcoe u).symm⟩
      · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hy⟩
        exact ⟨u, hu, OnePoint.coe_injective ((hpcoe u).trans hy)⟩
    rw [heq]
    exact hWo.preimage OnePoint.continuous_coe
  have hlh : IsLocalHomeomorph p := by
    refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun u => ?_
    obtain ⟨V, hV, hinj⟩ := hloc u
    have hVo : IsOpen ((((↑) : ℂ → ExtPlane) ∘ Subtype.val) ⁻¹' interior V : Set U) :=
      isOpen_interior.preimage (OnePoint.continuous_coe.comp continuous_subtype_val)
    refine ⟨_, hVo.mem_nhds (mem_interior_iff_mem_nhds.mpr hV), ?_⟩
    refine .of_continuous_injective_isOpenMap (hpcont.comp continuous_subtype_val) ?_
      (hpopen.comp hVo.isOpenMap_subtype_val)
    rintro ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ h12
    have h12' : F ((v₁ : ℂ) : ExtPlane) = F ((v₂ : ℂ) : ExtPlane) := by
      rw [← hpcoe v₁, ← hpcoe v₂]
      exact congrArg _ h12
    exact Subtype.ext (Subtype.ext (OnePoint.coe_injective
      (hinj (interior_subset h₁) (interior_subset h₂) h12')))
  have hprop : IsProperMap p := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hpcont, fun K hK => ?_⟩
    have hL : IsCompact (F ⁻¹' (((↑) : ℂ → ExtPlane) '' K)) :=
      ((hK.image OnePoint.continuous_coe).isClosed.preimage hF).isCompact
    have hLr : F ⁻¹' (((↑) : ℂ → ExtPlane) '' K) ⊆ range ((↑) : ℂ → ExtPlane) := by
      intro w hw
      refine OnePoint.ne_infty_iff_exists.mp fun h => ?_
      rw [h, mem_preimage, hinf] at hw
      exact OnePoint.infty_notMem_image_coe hw
    have hL' : IsCompact (((↑) : ℂ → ExtPlane) ⁻¹' (F ⁻¹' (((↑) : ℂ → ExtPlane) '' K))) := by
      rw [OnePoint.isOpenEmbedding_coe.isInducing.isCompact_iff, image_preimage_eq_of_subset hLr]
      exact hL
    rw [Subtype.isCompact_iff]
    convert hL' using 1
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, hpcoe u⟩
    · rintro ⟨k, hk, hkz⟩
      have hz : z ∈ U := (hUmem z).mpr (by rw [← hkz]; exact OnePoint.coe_ne_infty k)
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      have : p ⟨z, hz⟩ = k := OnePoint.coe_injective ((hpcoe _).trans hkz.symm)
      rw [mem_preimage, this]
      exact hk
  have hbij := t203_bijective_of_isLocalHomeomorph_isProperMap hlh hprop
  have hZe : ∀ z₀ : ℂ, F z₀ ≠ extInf := by
    intro z₀ hz₀
    have hN : IsOpen (F '' (((↑) : ℂ → ExtPlane) '' ball z₀ 1)) :=
      t203_cov_isOpen_image hF hloc isOpen_ball
    have hpre : F ⁻¹' (F '' (((↑) : ℂ → ExtPlane) '' ball z₀ 1)) ∈ 𝓝 extInf :=
      hF.continuousAt.preimage_mem_nhds (by
        rw [hinf]
        exact hN.mem_nhds ⟨z₀, ⟨z₀, mem_ball_self one_pos, rfl⟩, hz₀⟩)
    have hA : ((↑) : ℂ → ExtPlane) ⁻¹' (F ⁻¹' (F '' (((↑) : ℂ → ExtPlane) '' ball z₀ 1))) ∩
        (closedBall z₀ 1)ᶜ ∈ cocompact ℂ := by
      refine inter_mem ?_ (isCompact_closedBall z₀ 1).compl_mem_cocompact
      rw [← Filter.coclosedCompact_eq_cocompact]
      exact OnePoint.tendsto_coe_infty hpre
    obtain ⟨K, hK, hKsub⟩ := hasBasis_cocompact.mem_iff.mp hA
    obtain ⟨w, hwK, hwU⟩ := hUd.inter_open_nonempty Kᶜ hK.isClosed.isOpen_compl
      (nonempty_compl.mpr hK.ne_univ)
    obtain ⟨⟨_, ⟨v, hv, rfl⟩, hvw⟩, hwb⟩ := hKsub hwK
    have hvU : v ∈ U := (hUmem v).mpr (by rw [hvw]; exact (hUmem w).mp hwU)
    have heq : p ⟨v, hvU⟩ = p ⟨w, hwU⟩ :=
      OnePoint.coe_injective ((hpcoe ⟨v, hvU⟩).trans (hvw.trans (hpcoe ⟨w, hwU⟩).symm))
    have hvw' : v = w := congrArg Subtype.val (hbij.1 heq)
    exact hwb (hvw' ▸ ball_subset_closedBall hv)
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · induction a using OnePoint.rec with
    | infty =>
      induction b using OnePoint.rec with
      | infty => rfl
      | coe b => exact absurd (hab.symm.trans hinf) (hZe b)
    | coe a =>
      induction b using OnePoint.rec with
      | infty => exact absurd (hab.trans hinf) (hZe a)
      | coe b =>
        have heq : p ⟨a, (hUmem a).mpr (hZe a)⟩ = p ⟨b, (hUmem b).mpr (hZe b)⟩ :=
          OnePoint.coe_injective ((hpcoe _).trans (hab.trans (hpcoe ⟨b, (hUmem b).mpr (hZe b)⟩).symm))
        exact congrArg _ (congrArg Subtype.val (hbij.1 heq))
  · induction y using OnePoint.rec with
    | infty => exact ⟨extInf, hinf⟩
    | coe c =>
      obtain ⟨u, hu⟩ := hbij.2 c
      exact ⟨((u : ℂ) : ExtPlane), (hpcoe u).symm.trans (congrArg _ hu)⟩

/-- **A-cov** (Q7): a continuous self-map of `ℂ̄` which is injective near every finite point is bijective (off the fibre
of `q = F ∞` it is a proper local homeomorphism of the connected `ℂ ∖ F⁻¹(q)` onto `ℂ̄ ∖ {q} ≅ ℂ`, hence bijective;
and no finite point maps to `q`, since near it and near `∞` the values fill a punctured neighbourhood of `q` twice). -/
theorem t203_covering {F : ExtPlane → ExtPlane} (hF : Continuous F)
    (hloc : ∀ z : ℂ, ∃ U ∈ 𝓝 (z : ExtPlane), InjOn F U) : Function.Bijective F := by
  obtain ⟨M, hM⟩ := t203_cov_exists_homeo_eq_inf (F extInf)
  have hG : Function.Bijective (M ∘ F) := by
    refine t203_cov_of_inf (M.continuous.comp hF) (fun z => ?_) hM
    obtain ⟨U, hU, hinj⟩ := hloc z
    exact ⟨U, hU, M.injective.comp_injOn hinj⟩
  exact (M.bijective.of_comp_iff' F).mp hG

/-- The inversion `ι(w) = 1/w` of `ℂ̄` (`mobiusExt 0 1 1 0`) sends `∞` to `0`. -/
theorem t203_exh_inv_infty : mobiusExt 0 1 1 0 extInf = ((0 : ℂ) : ExtPlane) := by
  rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]

/-- The inversion `ι(w) = 1/w` of `ℂ̄` sends `0` to `∞`. -/
theorem t203_exh_inv_zero : mobiusExt 0 1 1 0 ((0 : ℂ) : ExtPlane) = extInf :=
  mobiusExt_coe_of_eq_zero (by ring)

/-- The inversion `ι(w) = 1/w` of `ℂ̄` sends a finite `z ≠ 0` to `z⁻¹`. -/
theorem t203_exh_inv_coe {z : ℂ} (hz : z ≠ 0) :
    mobiusExt 0 1 1 0 (z : ExtPlane) = ((z⁻¹ : ℂ) : ExtPlane) := by
  have h : (1 : ℂ) * z + 0 ≠ 0 := by rw [one_mul, add_zero]; exact hz
  rw [mobiusExt_coe h]
  congr 1
  simp [mobiusFn]

/-- The inversion `ι(w) = 1/w` of `ℂ̄` is an involution. -/
theorem t203_exh_inv_invol : Function.Involutive (mobiusExt 0 1 1 0) := by
  intro w
  induction w using OnePoint.rec with
  | infty => rw [t203_exh_inv_infty, t203_exh_inv_zero]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      rw [t203_exh_inv_zero, t203_exh_inv_infty]
    · rw [t203_exh_inv_coe hz, t203_exh_inv_coe (inv_ne_zero hz), inv_inv]

/-- The inversion maps `toExt Δ` onto the complement of `toExt Δ̄` (the exterior `{|z| > 1} ∪ {∞}`). -/
theorem t203_exh_inv_ball : mobiusExt 0 1 1 0 '' toExt (ball 0 1) = (toExt (closedBall (0 : ℂ) 1))ᶜ := by
  rw [t203_exh_inv_invol.image_eq_preimage_symm]
  ext w
  induction w using OnePoint.rec with
  | infty =>
    rw [mem_preimage, t203_exh_inv_infty, wd_n_coe_mem_toExt]
    exact iff_of_true (mem_ball_self one_pos) wd_n_infty_notMem_toExt
  | coe z =>
    rw [mem_preimage, mem_compl_iff, wd_n_coe_mem_toExt]
    by_cases hz : z = 0
    · subst hz
      rw [t203_exh_inv_zero]
      exact iff_of_false wd_n_infty_notMem_toExt (not_not.2 (mem_closedBall_self zero_le_one))
    · rw [t203_exh_inv_coe hz, wd_n_coe_mem_toExt, mem_ball_zero_iff, mem_closedBall_zero_iff, norm_inv,
        not_le]
      exact inv_lt_one₀ (norm_pos_iff.2 hz)

/-- The inversion maps the circle `toExt (r S¹)` onto `toExt (r⁻¹ S¹)`. -/
theorem t203_exh_inv_sphere {r : ℝ} (hr : 0 < r) :
    mobiusExt 0 1 1 0 '' toExt (sphere 0 r) = toExt (sphere (0 : ℂ) r⁻¹) := by
  rw [t203_exh_inv_invol.image_eq_preimage_symm]
  ext w
  induction w using OnePoint.rec with
  | infty =>
    rw [mem_preimage, t203_exh_inv_infty, wd_n_coe_mem_toExt, mem_sphere_zero_iff_norm, norm_zero]
    exact iff_of_false hr.ne wd_n_infty_notMem_toExt
  | coe z =>
    rw [mem_preimage, wd_n_coe_mem_toExt, mem_sphere_zero_iff_norm]
    by_cases hz : z = 0
    · subst hz
      rw [t203_exh_inv_zero, norm_zero]
      exact iff_of_false wd_n_infty_notMem_toExt (inv_pos.2 hr).ne
    · rw [t203_exh_inv_coe hz, wd_n_coe_mem_toExt, mem_sphere_zero_iff_norm, norm_inv, inv_eq_iff_eq_inv]

/-- `ℂ̄ ∖ S¹ = Δ ∪ (ℂ̄ ∖ Δ̄)`. -/
theorem t203_exh_compl_sphere :
    (toExt (sphere (0 : ℂ) 1))ᶜ = toExt (ball 0 1) ∪ (toExt (closedBall (0 : ℂ) 1))ᶜ := by
  ext w
  induction w using OnePoint.rec with
  | infty => exact iff_of_true wd_n_infty_notMem_toExt (Or.inr wd_n_infty_notMem_toExt)
  | coe z =>
    simp only [mem_compl_iff, mem_union, wd_n_coe_mem_toExt, mem_sphere_zero_iff_norm, mem_ball_zero_iff,
      mem_closedBall_zero_iff]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl h
      · exact Or.inr (not_le.2 h)
    · rintro (h | h) h'
      · exact h.ne h'
      · exact h h'.le

/-- **Components**: if the frontier of an open connected `A ⊆ ℂ̄` is `Φ(S¹)` for a homeomorphism `Φ` of `ℂ̄`, then
`A = Φ(Δ)` or `A = Φ(ι(Δ))` (`ι(w) = 1/w`): `ℂ̄ ∖ ∂A = Φ(Δ) ∪ Φ(ι Δ)` (disjoint, open, connected), `A` lies in one
of them, and that one lies in `A ∪ (ℂ̄ ∖ Ā)`, so equals `A`. -/
theorem t203_exh_components {A : Set ExtPlane} (hAo : IsOpen A) (hAc : IsPreconnected A) (hAn : A.Nonempty)
    (Φ : ExtPlane ≃ₜ ExtPlane) (hfr : frontier A = Φ '' toExt (sphere 0 1)) :
    A = Φ '' toExt (ball 0 1) ∨ A = Φ '' (mobiusExt 0 1 1 0 '' toExt (ball 0 1)) := by
  have hdet : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
  have hbo : IsOpen (toExt (ball (0 : ℂ) 1)) := OnePoint.isOpen_image_coe.2 isOpen_ball
  have hbc : IsPreconnected (toExt (ball (0 : ℂ) 1)) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hco : IsOpen (mobiusExt 0 1 1 0 '' toExt (ball 0 1)) := by
    rw [t203_exh_inv_ball]
    exact (OnePoint.isClosed_image_coe.2 ⟨isClosed_closedBall, isCompact_closedBall 0 1⟩).isOpen_compl
  have hU₁o : IsOpen (Φ '' toExt (ball 0 1)) := Φ.isOpenMap _ hbo
  have hU₂o : IsOpen (Φ '' (mobiusExt 0 1 1 0 '' toExt (ball 0 1))) := Φ.isOpenMap _ hco
  have hU₁c : IsPreconnected (Φ '' toExt (ball 0 1)) := hbc.image _ Φ.continuous.continuousOn
  have hU₂c : IsPreconnected (Φ '' (mobiusExt 0 1 1 0 '' toExt (ball 0 1))) :=
    (hbc.image _ (continuous_mobiusExt hdet).continuousOn).image _ Φ.continuous.continuousOn
  have hdisj : Disjoint (Φ '' toExt (ball 0 1)) (Φ '' (mobiusExt 0 1 1 0 '' toExt (ball 0 1))) := by
    rw [t203_exh_inv_ball]
    exact (disjoint_image_iff Φ.injective).2
      (disjoint_compl_right.mono_left (image_mono ball_subset_closedBall))
  have hcov : (frontier A)ᶜ = Φ '' toExt (ball 0 1) ∪ Φ '' (mobiusExt 0 1 1 0 '' toExt (ball 0 1)) := by
    rw [hfr, ← Φ.image_compl, t203_exh_compl_sphere, image_union, t203_exh_inv_ball]
  have hAsub : A ⊆ (frontier A)ᶜ := by
    intro w hw hfw
    rw [hAo.frontier_eq] at hfw
    exact hfw.2 hw
  have key : ∀ U : Set ExtPlane, IsPreconnected U → U ⊆ (frontier A)ᶜ → A ⊆ U → A = U := by
    intro U hUc hUf hAU
    refine Subset.antisymm hAU (hUc.subset_left_of_subset_union hAo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) ?_ ?_)
    · intro w hw
      by_cases hwA : w ∈ A
      · exact Or.inl hwA
      · refine Or.inr fun hcl => hUf hw ?_
        rw [hAo.frontier_eq]
        exact ⟨hcl, hwA⟩
    · obtain ⟨w, hw⟩ := hAn
      exact ⟨w, hAU hw, hw⟩
  rcases hAc.subset_or_subset hU₁o hU₂o hdisj (hAsub.trans hcov.subset) with h | h
  · refine Or.inl (key _ hU₁c ?_ h)
    rw [hcov]
    exact subset_union_left
  · refine Or.inr (key _ hU₂c ?_ h)
    rw [hcov]
    exact subset_union_right

/-- The image `Ψ(r S¹)` of a circle under a homeomorphism `Ψ` of `ℂ̄` is a Jordan curve. -/
theorem t203_exh_jordan (Ψ : ExtPlane ≃ₜ ExtPlane) {r : ℝ} (hr : 0 < r) :
    IsJordanCurve (Ψ '' toExt (sphere (0 : ℂ) r)) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  refine ⟨fun θ => Ψ (((r : ℂ) * (θ : ℂ) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact Ψ.continuous.comp (OnePoint.continuous_coe.comp (continuous_const.mul continuous_subtype_val))
  · intro a b hab
    exact Circle.coe_injective (mul_left_cancel₀ hr0 (OnePoint.coe_injective (Ψ.injective hab)))
  · apply Subset.antisymm
    · rintro _ ⟨θ, rfl⟩
      refine mem_image_of_mem Ψ (mem_image_of_mem _ ?_)
      rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : ‖z‖ = r := mem_sphere_zero_iff_norm.1 hz
      have hmem : z / r ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_div, hz', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          div_self hr.ne']
      refine ⟨⟨z / r, hmem⟩, ?_⟩
      show Ψ (((r : ℂ) * (z / r) : ℂ) : ExtPlane) = Ψ (z : ExtPlane)
      rw [mul_div_cancel₀ _ hr0]

/-- A scaled circle `r S¹` under the maps defining a `K`-quasicircle is again a `K`-quasicircle
(`f ∘ (r ·)` is `K`-q.c.). -/
theorem t203_exh_quasicircle {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hfs : f '' univ = univ)
    {M : ExtPlane → ExtPlane} (hM : IsMobius M) {s : ℝ} (hs : 0 < s) :
    IsKQuasicircle (M '' (OnePoint.map f '' toExt (sphere 0 s))) K := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
  have hsc : IsKQC (fun z => (s : ℂ) * z) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨(differentiable_id.const_mul _).differentiableOn,
      fun a _ b _ h => mul_left_cancel₀ hs0 h, rfl⟩
  have hsurj : (fun z => (s : ℂ) * z) '' univ = univ :=
    eq_univ_of_forall fun w => ⟨w / s, mem_univ _, mul_div_cancel₀ _ hs0⟩
  have hsph : (fun z => (s : ℂ) * z) '' sphere (0 : ℂ) 1 = sphere 0 s := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hz ⊢
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    · intro hw
      refine ⟨w / s, ?_, mul_div_cancel₀ _ hs0⟩
      rw [mem_sphere_zero_iff_norm] at hw ⊢
      rw [norm_div, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_self hs.ne']
  refine ⟨f ∘ (fun z => (s : ℂ) * z), ?_, ?_, M, hM, ?_⟩
  · have h := thm7_1_comp hsc hf (subset_univ _)
    rwa [one_mul] at h
  · rw [image_comp, hsurj, hfs]
  · congr 1
    unfold toExt
    rw [← hsph]
    simp only [image_image]
    rfl

/-- **One exhaustion step**: for a homeomorphism `Ψ` of `ℂ̄` with `Ψ(Δ) = D` and `0 < r < 1`, the set
`Dᵣ = Ψ(rΔ) ∩ ℂ` is a bounded Jordan domain bounded by `Ψ(r S¹)`, with `D̄ᵣ ⊆ Ψ(r Δ̄) ⊆ D`. -/
theorem t203_exh_piece {D : Set ℂ} {K : ℝ} (Ψ : ExtPlane ≃ₜ ExtPlane) (hΨ : Ψ '' toExt (ball 0 1) = toExt D)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hQ : IsKQuasicircle (Ψ '' toExt (sphere 0 r)) K) :
    IsKQuasidisc ((↑) ⁻¹' (Ψ '' toExt (ball 0 r))) K ∧
      Bornology.IsBounded ((↑) ⁻¹' (Ψ '' toExt (ball 0 r)) : Set ℂ) ∧
      closure ((↑) ⁻¹' (Ψ '' toExt (ball 0 r)) : Set ℂ) ⊆ D := by
  have hBD : Ψ '' toExt (ball 0 r) ⊆ toExt D := hΨ ▸ image_mono (image_mono (ball_subset_ball hr1.le))
  have hBrange : Ψ '' toExt (ball 0 r) ⊆ range ((↑) : ℂ → ExtPlane) := hBD.trans (image_subset_range _ _)
  have hT : toExt ((↑) ⁻¹' (Ψ '' toExt (ball 0 r))) = Ψ '' toExt (ball 0 r) :=
    image_preimage_eq_of_subset hBrange
  have hBo : IsOpen (Ψ '' toExt (ball 0 r)) := Ψ.isOpenMap _ (OnePoint.isOpen_image_coe.2 isOpen_ball)
  have hBc : IsPreconnected (Ψ '' toExt (ball 0 r)) :=
    ((convex_ball (0 : ℂ) r).isPreconnected.image _ OnePoint.continuous_coe.continuousOn).image _
      Ψ.continuous.continuousOn
  have hfr : frontier (toExt ((↑) ⁻¹' (Ψ '' toExt (ball 0 r)))) = Ψ '' toExt (sphere 0 r) := by
    rw [hT, ← Ψ.image_frontier, frontier_toExt_of_isBounded isBounded_ball isOpen_ball,
      frontier_ball 0 hr0.ne']
  have hcl : closure (Ψ '' toExt (ball 0 r)) = Ψ '' toExt (closedBall 0 r) := by
    rw [← Ψ.image_closure, closure_toExt_of_isBounded isBounded_ball, closure_ball 0 hr0.ne']
  have hKcD : Ψ '' toExt (closedBall 0 r) ⊆ toExt D :=
    hΨ ▸ image_mono (image_mono (closedBall_subset_ball hr1))
  have hKcc : IsCompact (Ψ '' toExt (closedBall (0 : ℂ) r)) :=
    ((isCompact_closedBall 0 r).image OnePoint.continuous_coe).image Ψ.continuous
  have hpre : IsCompact ((↑) ⁻¹' (Ψ '' toExt (closedBall (0 : ℂ) r)) : Set ℂ) := by
    have h1 : ((↑) : ℂ → ExtPlane) '' ((↑) ⁻¹' (Ψ '' toExt (closedBall (0 : ℂ) r))) =
        Ψ '' toExt (closedBall (0 : ℂ) r) :=
      image_preimage_eq_of_subset (hKcD.trans (image_subset_range _ _))
    have h2 : IsClosed (((↑) : ℂ → ExtPlane) '' ((↑) ⁻¹' (Ψ '' toExt (closedBall (0 : ℂ) r)))) := by
      rw [h1]
      exact hKcc.isClosed
    exact (OnePoint.isClosed_image_coe.1 h2).2
  have hDnK : ((↑) ⁻¹' (Ψ '' toExt (ball 0 r)) : Set ℂ) ⊆ (↑) ⁻¹' (Ψ '' toExt (closedBall (0 : ℂ) r)) :=
    preimage_mono (hcl ▸ subset_closure)
  refine ⟨⟨⟨hBo.preimage OnePoint.continuous_coe, ⟨?_, ?_⟩, ?_⟩, hfr ▸ hQ⟩, hpre.isBounded.subset hDnK, ?_⟩
  · obtain ⟨w, hw⟩ : (Ψ '' toExt (ball (0 : ℂ) r)).Nonempty :=
      ⟨_, mem_image_of_mem _ (mem_image_of_mem _ (mem_ball_self hr0))⟩
    obtain ⟨z, rfl⟩ := hBrange hw
    exact ⟨z, hw⟩
  · rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image]
    change IsPreconnected (toExt ((↑) ⁻¹' (Ψ '' toExt (ball 0 r))))
    rw [hT]
    exact hBc
  · rw [hfr]
    exact t203_exh_jordan Ψ hr0
  · calc closure ((↑) ⁻¹' (Ψ '' toExt (ball 0 r)) : Set ℂ)
        ⊆ (↑) ⁻¹' (Ψ '' toExt (closedBall (0 : ℂ) r)) := closure_minimal hDnK hpre.isClosed
      _ ⊆ (↑) ⁻¹' toExt D := preimage_mono hKcD
      _ = D := preimage_image_eq D OnePoint.coe_injective

/-- **Exhaustion core**: for a homeomorphism `Ψ` of `ℂ̄` with `Ψ(Δ) = D` whose circles `Ψ(r S¹)`, `0 < r < 1`, are
`K`-quasicircles, the sets `Dₙ = Ψ(rₙ Δ) ∩ ℂ`, `rₙ = 1 - 1/(n+2)`, exhaust `D` by bounded `K`-quasidiscs with
`D̄ₙ ⊆ D`. -/
theorem t203_exh_core {D : Set ℂ} {K : ℝ} (Ψ : ExtPlane ≃ₜ ExtPlane) (hΨ : Ψ '' toExt (ball 0 1) = toExt D)
    (hQ : ∀ r : ℝ, 0 < r → r < 1 → IsKQuasicircle (Ψ '' toExt (sphere 0 r)) K) :
    ∃ Dn : ℕ → Set ℂ, (∀ n, IsKQuasidisc (Dn n) K ∧ Bornology.IsBounded (Dn n) ∧ closure (Dn n) ⊆ D) ∧
      Monotone Dn ∧ ⋃ n, Dn n = D := by
  have hr0 : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) := fun n => by
    have h : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      have := n.cast_nonneg (α := ℝ)
      linarith
    linarith
  have hr1 : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrm : Monotone fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    show 1 - 1 / ((m : ℝ) + 2) ≤ 1 - 1 / ((n : ℝ) + 2)
    linarith
  refine ⟨fun n => (↑) ⁻¹' (Ψ '' toExt (ball 0 (1 - 1 / ((n : ℝ) + 2)))), fun n =>
    t203_exh_piece Ψ hΨ (hr0 n) (hr1 n) (hQ _ (hr0 n) (hr1 n)), ?_, ?_⟩
  · intro m n hmn
    exact preimage_mono (image_mono (image_mono (ball_subset_ball (hrm hmn))))
  · ext z
    simp only [mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨n, hn⟩
      have h : (z : ExtPlane) ∈ toExt D := hΨ ▸ image_mono (image_mono (ball_subset_ball (hr1 n).le)) hn
      exact wd_n_coe_mem_toExt.1 h
    · intro hz
      have h : (z : ExtPlane) ∈ Ψ '' toExt (ball 0 1) := hΨ ▸ wd_n_coe_mem_toExt.2 hz
      obtain ⟨_, ⟨u, hu, rfl⟩, hzu⟩ := h
      have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hu1)
      refine ⟨n, u, ⟨u, mem_ball_zero_iff.2 ?_, rfl⟩, hzu⟩
      have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith

/-- **A-exh** (Q2): a `K`-quasidisc `D` is exhausted by bounded `K`-quasidiscs `Dₙ` with `D̄ₙ ⊆ D`: the images of the
discs `rₙΔ`, `rₙ ↑ 1` (or of the exteriors `{|z| > 1/rₙ} ∪ {∞}`), under the `K`-q.c. map and the Möbius map that
define `∂D`. -/
theorem t203_exhaustion {D : Set ℂ} {K : ℝ} (hD : IsKQuasidisc D K) :
    ∃ Dn : ℕ → Set ℂ, (∀ n, IsKQuasidisc (Dn n) K ∧ Bornology.IsBounded (Dn n) ∧ closure (Dn n) ⊆ D) ∧
      Monotone Dn ∧ ⋃ n, Dn n = D := by
  obtain ⟨⟨hDo, hDc, -⟩, f, hf, hfs, M, hM, hC⟩ := hD
  obtain ⟨e, rfl⟩ := t1_homeomorph hf hfs
  obtain ⟨α, β, κ, δ, hdet, hMeq⟩ := id hM
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ExtPlane ≃ₜ ExtPlane, ∀ S : Set ExtPlane, Φ '' S = M '' (OnePoint.map e '' S) :=
    ⟨e.onePointCongr.trans (mobiusHomeomorph α β κ δ hdet), fun S => by
      rw [hMeq, image_image]
      rfl⟩
  have hQ : ∀ s : ℝ, 0 < s → IsKQuasicircle (Φ '' toExt (sphere 0 s)) K := fun s hs => by
    rw [hΦ]
    exact t203_exh_quasicircle hf hfs hM hs
  have hfr : frontier (toExt D) = Φ '' toExt (sphere 0 1) := by
    rw [hΦ]
    exact hC
  have hAo : IsOpen (toExt D) := OnePoint.isOpen_image_coe.2 hDo
  have hAc : IsPreconnected (toExt D) := hDc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  rcases t203_exh_components hAo hAc (hDc.nonempty.image _) Φ hfr with h | h
  · exact t203_exh_core Φ h.symm fun r hr _ => hQ r hr
  · obtain ⟨ι, hι⟩ : ∃ ι : ExtPlane ≃ₜ ExtPlane, ⇑ι = mobiusExt 0 1 1 0 :=
      ⟨mobiusHomeomorph 0 1 1 0 (by norm_num), rfl⟩
    have himg : ∀ S : Set ExtPlane, (ι.trans Φ) '' S = Φ '' (mobiusExt 0 1 1 0 '' S) := fun S => by
      rw [← hι, image_image]
      rfl
    refine t203_exh_core (ι.trans Φ) ?_ fun r hr _ => ?_
    · rw [himg]
      exact h.symm
    · rw [himg, t203_exh_inv_sphere hr]
      exact hQ _ (inv_pos.2 hr)

/-! ### Theorem 20.3 track, Stage B interface (coordinator 553e2d): the Ahlfors extension on one domain `D'`

Setting: `D'` a bounded quasidisc with `D̄' ⊆ D`, `w₁, w₂` solutions of `w'' + (φ/2) w = 0` on `D` with Wronskian
`1`, a `C¹` reflection `g` of `ℂ ∖ D̄'` onto `D' ∖ {p}` with the invariant bound `c₀`, and `‖φ‖ ≤ s η_{D'}²` on `D'`
with `c₀ s < 1`.  The extension is `(w₁ : w₂)` on `D̄'`, `(w₁(ζ) + (z - ζ)w₁'(ζ) : w₂(ζ) + (z - ζ)w₂'(ζ))`, `ζ = g z`,
off `D̄'`, and `(w₁'(p) : w₂'(p))` at `∞`. -/

/-- The Ahlfors extension on `ℂ̄`. -/
def t203_ext (w₁ w₂ g : ℂ → ℂ) (S : Set ℂ) (p : ℂ) (P : ExtPlane) : ExtPlane :=
  OnePoint.elim P (t203_ratio (deriv w₁ p) (deriv w₂ p)) fun z =>
    @ite ExtPlane (z ∈ S) (Classical.propDecidable _) (t203_ratio (w₁ z) (w₂ z))
      (t203_ratio (w₁ (g z) + (z - g z) * deriv w₁ (g z)) (w₂ (g z) + (z - g z) * deriv w₂ (g z)))

/-- The Stage B setting (see the section docstring); `c₀ s < 2` is what (20.10) needs (sharp: `c₀ = 4` for circles). -/
def t203_Setting (D D' : Set ℂ) (w₁ w₂ φ g : ℂ → ℂ) (p : ℂ) (K₁ c₀ s : ℝ) : Prop :=
  IsOpen D ∧ IsOpen D' ∧ IsCompact (closure D') ∧ closure D' ⊆ D ∧
    (∃ ψ : ℂ → ℂ, IsConformalOnto ψ D' unitDisc) ∧ DifferentiableOn ℂ w₁ D ∧ DifferentiableOn ℂ w₂ D ∧
    (∀ z ∈ D, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) ∧
    p ∈ D' ∧ ContDiffOn ℝ 1 g (closure D')ᶜ ∧ IsPlanarQCReflection (closure D')ᶜ (D' \ {p}) g K₁ ∧
    Tendsto g (cocompact ℂ ⊓ 𝓟 (closure D')ᶜ) (𝓝 p) ∧
    (∀ z ∈ (closure D')ᶜ, ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ * poincareDensity D' (g z) ^ 2 ≤ c₀) ∧
    0 ≤ s ∧ c₀ * s < 2 ∧ ∀ ζ ∈ D', ‖φ ζ‖ ≤ s * poincareDensity D' ζ ^ 2

/-- Scale invariance of `t203_ratio`: `(c a : c b) = (a : b)` for `c ≠ 0`. -/
theorem t203_cont_ratio_mul {c : ℂ} (hc : c ≠ 0) (a b : ℂ) :
    t203_ratio (c * a) (c * b) = t203_ratio a b := by
  by_cases hb : b = 0
  · simp [t203_ratio, hb]
  · simp only [t203_ratio, hb, mul_eq_zero, hc, or_self, ↓reduceIte]
    rw [mul_div_mul_left a b hc]

/-- The inversion `1/w` exchanges the two coordinates of `(a : b)` when `a ≠ 0`. -/
theorem t203_cont_ratio_inv {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    mobiusExt 0 1 1 0 (t203_ratio b a) = t203_ratio a b := by
  by_cases hb : b = 0
  · simp only [t203_ratio, ha, hb, ↓reduceIte, zero_div]
    exact t203_exh_inv_zero
  · simp only [t203_ratio, ha, hb, ↓reduceIte]
    rw [t203_exh_inv_coe (div_ne_zero hb ha), inv_div]

/-- Continuity of `(a : b)`: if `u → a`, `v → b` and `(a, b) ≠ (0, 0)`, then `(u : v) → (a : b)` in `ℂ̄`. -/
theorem t203_cont_ratio_tendsto {α : Type*} {L : Filter α} {u v : α → ℂ} {a b : ℂ}
    (hu : Tendsto u L (𝓝 a)) (hv : Tendsto v L (𝓝 b)) (hab : b = 0 → a ≠ 0) :
    Tendsto (fun y => t203_ratio (u y) (v y)) L (𝓝 (t203_ratio a b)) := by
  have key : ∀ {u v : α → ℂ} {a b : ℂ}, Tendsto u L (𝓝 a) → Tendsto v L (𝓝 b) → b ≠ 0 →
      Tendsto (fun y => t203_ratio (u y) (v y)) L (𝓝 (t203_ratio a b)) := by
    intro u v a b hu hv hb
    have h1 : Tendsto (fun y => ((u y / v y : ℂ) : ExtPlane)) L (𝓝 ((a / b : ℂ) : ExtPlane)) :=
      (OnePoint.continuous_coe.tendsto _).comp (hu.div hv hb)
    have h2 : t203_ratio a b = ((a / b : ℂ) : ExtPlane) := by simp [t203_ratio, hb]
    rw [h2]
    refine h1.congr' ?_
    filter_upwards [hv.eventually_ne hb] with y hy
    simp [t203_ratio, hy]
  by_cases hb : b = 0
  · have ha := hab hb
    have h1 := ((continuous_mobiusExt (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num)).tendsto _).comp
      (key hv hu ha)
    rw [Function.comp_def, t203_cont_ratio_inv ha] at h1
    refine h1.congr' ?_
    filter_upwards [hu.eventually_ne ha] with y hy
    exact t203_cont_ratio_inv hy _
  · exact key hu hv hb

/-- **B-cont**: the extension is continuous on `ℂ̄` (inside: `(w₁ : w₂)` is continuous into `ℂ̄` since `w₁, w₂` have
no common zero; outside: the same for the reflected pair; across `C = ∂D'`: `g → q`, `u = z - g z → 0` (`t203_decay`);
at `∞`: `g → p`, `u → ∞`, so the ratio tends to `(w₁'(p) : w₂'(p))`). -/
theorem t203_ext_continuous {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) : Continuous (t203_ext w₁ w₂ g (closure D') p) := by
  obtain ⟨hDo, hD'o, hK, hsub, ⟨ψ, hψ⟩, hw₁, hw₂, hode, hp, hgC, hrefl, htend, hc₀, -, -, -⟩ := h
  have hSc : IsClosed (closure D') := isClosed_closure
  have hSo : IsOpen (closure D')ᶜ := hSc.isOpen_compl
  have cw₁ : ∀ z ∈ D, ContinuousAt w₁ z := fun z hz =>
    (hw₁.differentiableAt (hDo.mem_nhds hz)).continuousAt
  have cw₂ : ∀ z ∈ D, ContinuousAt w₂ z := fun z hz =>
    (hw₂.differentiableAt (hDo.mem_nhds hz)).continuousAt
  have cd₁ : ∀ z ∈ D, ContinuousAt (deriv w₁) z := fun z hz =>
    ((hw₁.deriv hDo).differentiableAt (hDo.mem_nhds hz)).continuousAt
  have cd₂ : ∀ z ∈ D, ContinuousAt (deriv w₂) z := fun z hz =>
    ((hw₂.deriv hDo).differentiableAt (hDo.mem_nhds hz)).continuousAt
  have hW : ∀ z ∈ D, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1 := fun z hz => (hode z hz).2.2
  have hne : ∀ z ∈ D, w₂ z = 0 → w₁ z ≠ 0 := by
    intro z hz h0 h1
    have h2 := hW z hz
    rw [h0, h1] at h2
    simp at h2
  have hgD : ∀ z ∈ (closure D')ᶜ, g z ∈ D := fun z hz =>
    hsub (subset_closure (hrefl.2.1 ▸ mem_image_of_mem g hz : g z ∈ D' \ {p}).1)
  have hin : ∀ z ∈ closure D', t203_ext w₁ w₂ g (closure D') p (z : ExtPlane) = t203_ratio (w₁ z) (w₂ z) :=
    fun z hz => by
      simp only [t203_ext, OnePoint.elim]
      exact ite_eq_left hz
  have hout : ∀ z ∈ (closure D')ᶜ, t203_ext w₁ w₂ g (closure D') p (z : ExtPlane) =
      t203_ratio (w₁ (g z) + (z - g z) * deriv w₁ (g z)) (w₂ (g z) + (z - g z) * deriv w₂ (g z)) :=
    fun z hz => by
      simp only [t203_ext, OnePoint.elim]
      exact ite_eq_right hz
  rw [continuous_iff_continuousAt]
  intro P
  induction P using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty', Filter.coclosedCompact_eq_cocompact]
    show Tendsto _ _ (𝓝 (t203_ratio (deriv w₁ p) (deriv w₂ p)))
    have hSc' : (closure D')ᶜ ∈ cocompact ℂ := hK.compl_mem_cocompact
    rw [inf_eq_left.2 (le_principal_iff.2 hSc')] at htend
    have hpD : p ∈ D := hsub (subset_closure hp)
    have hnorm : Tendsto (fun y => ‖y - g y‖) (cocompact ℂ) atTop := by
      have h1 : Tendsto (fun y : ℂ => ‖y‖ + -‖g y‖) (cocompact ℂ) atTop :=
        tendsto_norm_cocompact_atTop.atTop_add htend.norm.neg
      exact tendsto_atTop_mono (fun y => by have := norm_sub_norm_le y (g y); linarith) h1
    have hinv : Tendsto (fun y => (y - g y)⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact hnorm.inv_tendsto_atTop.congr fun y => (norm_inv _).symm
    have hne0 : ∀ᶠ y in cocompact ℂ, y - g y ≠ 0 :=
      (hnorm.eventually_gt_atTop 0).mono fun y hy => norm_pos_iff.1 hy
    have hA₁ : Tendsto (fun y => (y - g y)⁻¹ * w₁ (g y) + deriv w₁ (g y)) (cocompact ℂ)
        (𝓝 (deriv w₁ p)) := by
      have := (hinv.mul ((cw₁ p hpD).tendsto.comp htend)).add ((cd₁ p hpD).tendsto.comp htend)
      simpa using this
    have hA₂ : Tendsto (fun y => (y - g y)⁻¹ * w₂ (g y) + deriv w₂ (g y)) (cocompact ℂ)
        (𝓝 (deriv w₂ p)) := by
      have := (hinv.mul ((cw₂ p hpD).tendsto.comp htend)).add ((cd₂ p hpD).tendsto.comp htend)
      simpa using this
    have hab : deriv w₂ p = 0 → deriv w₁ p ≠ 0 := by
      intro h0 h1
      have h2 := hW p hpD
      rw [h0, h1] at h2
      simp at h2
    refine (t203_cont_ratio_tendsto hA₁ hA₂ hab).congr' ?_
    filter_upwards [hne0, hSc'] with y hy hyS
    rw [Function.comp_apply, hout y hyS]
    refine Eq.trans ?_ (t203_cont_ratio_mul (inv_ne_zero hy) _ _)
    congr 1 <;> rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  | coe z =>
    rw [OnePoint.continuousAt_coe, ← continuousWithinAt_univ, ← union_compl_self (closure D')]
    refine ContinuousWithinAt.union ?_ ?_
    · by_cases hz : z ∈ closure D'
      · have hzD : z ∈ D := hsub hz
        have hlim := t203_cont_ratio_tendsto (cw₁ z hzD).tendsto (cw₂ z hzD).tendsto (hne z hzD)
        show Tendsto _ _ (𝓝 (t203_ext w₁ w₂ g (closure D') p (z : ExtPlane)))
        rw [hin z hz]
        exact (hlim.mono_left nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall fun y hy => (hin y hy).symm)
      · exact continuousWithinAt_of_notMem_closure (by rwa [hSc.closure_eq])
    · by_cases hz : z ∈ closure D'
      · by_cases hzc : z ∈ closure (closure D')ᶜ
        · have hq : z ∈ frontier (closure D') := ⟨subset_closure hz, by rwa [closure_compl] at hzc⟩
          obtain ⟨hg1, hg2, -⟩ := t203_decay hD'o hψ hp hrefl hc₀ hq
          have hzD : z ∈ D := hsub hz
          have hu : Tendsto (fun y => y - g y) (𝓝[(closure D')ᶜ] z) (𝓝 0) := by
            simpa using hg2.neg
          have hN : Tendsto (fun y => w₁ (g y) + (y - g y) * deriv w₁ (g y)) (𝓝[(closure D')ᶜ] z)
              (𝓝 (w₁ z)) := by
            simpa using ((cw₁ z hzD).tendsto.comp hg1).add (hu.mul ((cd₁ z hzD).tendsto.comp hg1))
          have hDn : Tendsto (fun y => w₂ (g y) + (y - g y) * deriv w₂ (g y)) (𝓝[(closure D')ᶜ] z)
              (𝓝 (w₂ z)) := by
            simpa using ((cw₂ z hzD).tendsto.comp hg1).add (hu.mul ((cd₂ z hzD).tendsto.comp hg1))
          show Tendsto _ _ (𝓝 (t203_ext w₁ w₂ g (closure D') p (z : ExtPlane)))
          rw [hin z hz]
          exact (t203_cont_ratio_tendsto hN hDn (hne z hzD)).congr'
            (eventually_nhdsWithin_of_forall fun y hy => (hout y hy).symm)
        · exact continuousWithinAt_of_notMem_closure hzc
      · have hgc : ContinuousAt g z := hgC.continuousOn.continuousAt (hSo.mem_nhds hz)
        have hgz := hgD z hz
        have hN : Tendsto (fun y => w₁ (g y) + (y - g y) * deriv w₁ (g y)) (𝓝 z)
            (𝓝 (w₁ (g z) + (z - g z) * deriv w₁ (g z))) :=
          ((cw₁ _ hgz).tendsto.comp hgc).add ((tendsto_id.sub hgc).mul ((cd₁ _ hgz).tendsto.comp hgc))
        have hDn : Tendsto (fun y => w₂ (g y) + (y - g y) * deriv w₂ (g y)) (𝓝 z)
            (𝓝 (w₂ (g z) + (z - g z) * deriv w₂ (g z))) :=
          ((cw₂ _ hgz).tendsto.comp hgc).add ((tendsto_id.sub hgc).mul ((cd₂ _ hgz).tendsto.comp hgc))
        show Tendsto _ _ (𝓝 (t203_ext w₁ w₂ g (closure D') p (z : ExtPlane)))
        rw [hout z hz]
        exact ((t203_cont_ratio_tendsto hN hDn (t203_num_ne_zero (hW _ hgz))).mono_left
          nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun y hy => (hout y hy).symm)

/-- The extension at a finite point of `S`: `(w₁ z : w₂ z)`. -/
theorem t203_c1_ext_in {w₁ w₂ g : ℂ → ℂ} {S : Set ℂ} {p z : ℂ} (hz : z ∈ S) :
    t203_ext w₁ w₂ g S p (z : ExtPlane) = t203_ratio (w₁ z) (w₂ z) := by
  rw [t203_ext, OnePoint.elim_some]
  exact ite_eq_left hz

/-- The extension at a finite point off `S`: the reflected pair `(N : Dn)`. -/
theorem t203_c1_ext_out {w₁ w₂ g : ℂ → ℂ} {S : Set ℂ} {p z : ℂ} (hz : z ∉ S) :
    t203_ext w₁ w₂ g S p (z : ExtPlane) =
      t203_ratio (w₁ (g z) + (z - g z) * deriv w₁ (g z)) (w₂ (g z) + (z - g z) * deriv w₂ (g z)) := by
  rw [t203_ext, OnePoint.elim_some]
  exact ite_eq_right hz

/-- `extToC (x : y) = x / y` for `y ≠ 0`. -/
theorem t203_c1_extToC_ratio {x y : ℂ} (hy : y ≠ 0) : extToC (t203_ratio x y) = x / y := by
  rw [t203_ratio, ite_eq_right hy]
  rfl

/-- `(x : y) ≠ ∞` forces `y ≠ 0`. -/
theorem t203_c1_ratio_ne {x y : ℂ} (h : t203_ratio x y ≠ extInf) : y ≠ 0 := by
  intro hy
  apply h
  rw [t203_ratio, ite_eq_left hy]

/-- A Möbius map acts on `(x : y)` linearly on the pair: `M (x : y) = (a' x + b' y : c' x + d' y)` with
`(a', b', c', d') = (a, b, c, d)/σ`, for `(x, y) ≠ (0, 0)`. -/
theorem t203_c1_mobius_ratio {a b c d σ x y : ℂ} (hσ : σ ≠ 0) (hxy : x ≠ 0 ∨ y ≠ 0) :
    mobiusExt a b c d (t203_ratio x y) = t203_ratio (a / σ * x + b / σ * y) (c / σ * x + d / σ * y) := by
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hxy.resolve_right (not_not.2 hy)
    rw [t203_ratio, ite_eq_left hy, hy]
    by_cases hc : c = 0
    · rw [mobiusExt_infty_of_eq hc, t203_ratio, ite_eq_left (by rw [hc]; ring)]
    · have hne : c / σ * x + d / σ * 0 ≠ 0 := by
        rw [mul_zero, add_zero]
        exact mul_ne_zero (div_ne_zero hc hσ) hx
      rw [mobiusExt_infty_of_ne hc, t203_ratio, ite_eq_right hne]
      congr 1
      field_simp
      ring
  · rw [t203_ratio, ite_eq_right hy]
    by_cases hcd : c * (x / y) + d = 0
    · have h0 : c / σ * x + d / σ * y = 0 := by
        have : c / σ * x + d / σ * y = (c * (x / y) + d) * (y / σ) := by field_simp
        rw [this, hcd, zero_mul]
      rw [mobiusExt_coe_of_eq_zero hcd, t203_ratio, ite_eq_left h0]
    · have h0 : c / σ * x + d / σ * y ≠ 0 := by
        have : c / σ * x + d / σ * y = (c * (x / y) + d) * (y / σ) := by field_simp
        rw [this]
        exact mul_ne_zero hcd (div_ne_zero hy hσ)
      rw [mobiusExt_coe hcd, t203_ratio, ite_eq_right h0, mobiusFn]
      congr 1
      field_simp

/-- `w ∘ g + (z - g) · (w' ∘ g)` is `C¹` at `y` when `g` is and `w` is holomorphic near `g y`. -/
theorem t203_c1_cd_num {D : Set ℂ} (hDo : IsOpen D) {w g : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) {y : ℂ}
    (hg : ContDiffAt ℝ 1 g y) (hgy : g y ∈ D) :
    ContDiffAt ℝ 1 (fun z => w (g z) + (z - g z) * deriv w (g z)) y := by
  have h1 : ContDiffAt ℝ 1 w (g y) :=
    ((hw.analyticAt (hDo.mem_nhds hgy)).contDiffAt (n := 1)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 1 (deriv w) (g y) :=
    (((hw.deriv hDo).analyticAt (hDo.mem_nhds hgy)).contDiffAt (n := 1)).restrict_scalars ℝ
  exact (h1.comp y hg).add ((contDiffAt_id.sub hg).mul (h2.comp y hg))

/-- Off `D̄'` (where the reflected denominator does not vanish) the extension is the plane map `N/Dn`
near `y`, which is `C¹` at `y` with the (20.10) derivative (`t203_dF`). -/
theorem t203_c1_out_pt {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {y : ℂ} (hy : y ∉ closure D')
    (hDn : w₂ (g y) + (y - g y) * deriv w₂ (g y) ≠ 0) :
    ContDiffAt ℝ 1 (fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) /
      (w₂ (g w) + (w - g w) * deriv w₂ (g w))) y ∧
    HasFDerivAt (fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) / (w₂ (g w) + (w - g w) * deriv w₂ (g w)))
      ((-1 / (w₂ (g y) + (y - g y) * deriv w₂ (g y)) ^ 2) • ContinuousLinearMap.id ℝ ℂ +
        (-(φ (g y) / 2) * (y - g y) ^ 2 / (w₂ (g y) + (y - g y) * deriv w₂ (g y)) ^ 2) • fderiv ℝ g y) y ∧
    (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) =ᶠ[𝓝 y]
      fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) / (w₂ (g w) + (w - g w) * deriv w₂ (g w)) := by
  obtain ⟨hDo, -, -, hsub, -, hw₁, hw₂, hode, -, hgC1, hgR, -⟩ := h
  have hSo : IsOpen (closure D')ᶜ := isClosed_closure.isOpen_compl
  have hgy : g y ∈ D := hsub (subset_closure (hgR.2.1 ▸ mem_image_of_mem g hy : g y ∈ D' \ {p}).1)
  have hg : ContDiffAt ℝ 1 g y := hgC1.contDiffAt (hSo.mem_nhds hy)
  have hN := t203_c1_cd_num hDo hw₁ hg hgy
  have hD := t203_c1_cd_num hDo hw₂ hg hgy
  refine ⟨(hN.mul (hD.inv hDn)).congr_of_eventuallyEq (Eventually.of_forall fun w => div_eq_mul_inv _ _),
    ?_, ?_⟩
  · obtain ⟨o1, o2, hW⟩ := hode (g y) hgy
    obtain ⟨a1, b1⟩ := t203_ode_hasDerivAt (hw₁.differentiableAt (hDo.mem_nhds hgy))
      ((hw₁.deriv hDo).differentiableAt (hDo.mem_nhds hgy)) o1
    obtain ⟨a2, b2⟩ := t203_ode_hasDerivAt (hw₂.differentiableAt (hDo.mem_nhds hgy))
      ((hw₂.deriv hDo).differentiableAt (hDo.mem_nhds hgy)) o2
    exact t203_dF (w₁ := w₁) (w₂ := w₂) (w₁' := deriv w₁) (w₂' := deriv w₂) (g := g) (G := fderiv ℝ g y)
      (z := y) (a := φ (g y) / 2) a1 a2 (by rw [neg_mul]; exact b1) (by rw [neg_mul]; exact b2)
      (by linear_combination hW) (hg.differentiableAt one_ne_zero).hasFDerivAt hDn
  · filter_upwards [hSo.mem_nhds hy, hD.continuousAt.eventually_ne hDn] with w hw hw'
    rw [t203_c1_ext_out hw, t203_c1_extToC_ratio hw']

/-- `∂` and `∂̄` only see the germ. -/
theorem t203_c1_dz_congr {f f₁ : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] f₁) :
    dz f z = dz f₁ z ∧ dzbar f z = dzbar f₁ z := by
  have e := h.fderiv_eq (𝕜 := ℝ)
  exact ⟨by rw [dz, dz, e], by rw [dzbar, dzbar, e]⟩

/-- **Case (a)**, off `D̄'` with finite value: `C¹`, `|∂̄| < |∂|` and `|∂̄| ≤ (c₀ s/2)|∂|` (`t203_mu_w` with
`‖φ(g z)‖ ‖g z - z‖² ‖dg‖ ≤ s η² · c₀/η² = c₀ s`). -/
theorem t203_c1_outside {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {z : ℂ} (hzS : z ∉ closure D')
    (hDn : w₂ (g z) + (z - g z) * deriv w₂ (g z) ≠ 0) :
    ContDiffAt ℝ 1 (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z ∧
      ‖dzbar (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ <
        ‖dz (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ ∧
      ‖dzbar (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ ≤
        c₀ * s / 2 * ‖dz (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ := by
  obtain ⟨hC, -, hev⟩ := t203_c1_out_pt h hzS hDn
  obtain ⟨e1, e2⟩ := t203_c1_dz_congr hev
  obtain ⟨hDo, -, -, hsub, -, hw₁, hw₂, hode, -, hgC1, hgR, -, hc₀, hs0, hcs, hφb⟩ := h
  have hSo : IsOpen (closure D')ᶜ := isClosed_closure.isOpen_compl
  have hgzD' : g z ∈ D' := (hgR.2.1 ▸ mem_image_of_mem g hzS : g z ∈ D' \ {p}).1
  have hgz : g z ∈ D := hsub (subset_closure hgzD')
  have hg : DifferentiableAt ℝ g z := (hgC1.contDiffAt (hSo.mem_nhds hzS)).differentiableAt one_ne_zero
  have hS : ‖φ (g z)‖ * ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ ≤ c₀ * s := by
    have hX : 0 ≤ ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ := by positivity
    have h1 := hφb (g z) hgzD'
    have h2 := hc₀ z hzS
    calc ‖φ (g z)‖ * ‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ = ‖φ (g z)‖ * (‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖) := by ring
      _ ≤ (s * poincareDensity D' (g z) ^ 2) * (‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖) :=
          mul_le_mul_of_nonneg_right h1 hX
      _ = s * (‖g z - z‖ ^ 2 * ‖fderiv ℝ g z‖ * poincareDensity D' (g z) ^ 2) := by ring
      _ ≤ s * c₀ := mul_le_mul_of_nonneg_left h2 hs0
      _ = c₀ * s := by ring
  obtain ⟨o1, o2, hW⟩ := hode (g z) hgz
  obtain ⟨hlt, hle⟩ := (t203_mu_w (w₁ := w₁) (w₂ := w₂) (g := g) (φ := φ)
    (F := fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) / (w₂ (g w) + (w - g w) * deriv w₂ (g w)))
    (z := z) (t := c₀ * s) hg (hw₁.differentiableAt (hDo.mem_nhds hgz))
    ((hw₁.deriv hDo).differentiableAt (hDo.mem_nhds hgz)) (hw₂.differentiableAt (hDo.mem_nhds hgz))
    ((hw₂.deriv hDo).differentiableAt (hDo.mem_nhds hgz)) o1 o2 hW rfl (by linarith) hS).1 hDn
  refine ⟨hC.congr_of_eventuallyEq hev, by rw [e1, e2]; exact hlt, ?_⟩
  rw [e1, e2]
  have hdz0 : dz (fun w => (w₁ (g w) + (w - g w) * deriv w₁ (g w)) /
      (w₂ (g w) + (w - g w) * deriv w₂ (g w))) z ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hlt
    exact (norm_nonneg _).not_gt hlt
  rw [← div_mul_cancel₀ (dzbar _ z) hdz0, norm_mul]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- `t203_decay` at every point of `D̄'` (at interior points `𝓝[(D̄')ᶜ] q = ⊥`), with `u = z - g z`. -/
theorem t203_c1_decay {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {q : ℂ} (hq : q ∈ closure D') :
    Tendsto g (𝓝[(closure D')ᶜ] q) (𝓝 q) ∧ Tendsto (fun z => z - g z) (𝓝[(closure D')ᶜ] q) (𝓝 0) ∧
      Tendsto (fun z => ‖z - g z‖ ^ 2 * ‖fderiv ℝ g z‖) (𝓝[(closure D')ᶜ] q) (𝓝 0) := by
  obtain ⟨-, hD'o, -, -, ⟨ψ, hψ⟩, -, -, -, hpD', -, hgR, -, hc₀, -⟩ := h
  by_cases hqf : q ∈ frontier (closure D')
  · obtain ⟨h1, h2, h3⟩ := t203_decay hD'o hψ hpD' hgR hc₀ hqf
    refine ⟨h1, ?_, ?_⟩
    · have := h2.neg
      rw [neg_zero] at this
      exact this.congr fun z => neg_sub _ _
    · exact h3.congr fun z => by rw [norm_sub_rev]
  · have hqi : q ∈ interior (closure D') := by
      rw [isClosed_closure.frontier_eq] at hqf
      by_contra hc
      exact hqf ⟨hq, hc⟩
    have hbot : 𝓝[(closure D')ᶜ] q = ⊥ := by
      rw [← Filter.empty_mem_iff_bot]
      exact mem_nhdsWithin.2 ⟨interior (closure D'), isOpen_interior, hqi,
        fun x ⟨hx1, hx2⟩ => hx2 (interior_subset hx1)⟩
    rw [hbot]
    exact ⟨tendsto_bot, tendsto_bot, tendsto_bot⟩

/-- The reflected numerator/denominator `w(g z) + (z - g z) w'(g z)` tends to `w(q)` when `g → q`, `u → 0`. -/
theorem t203_c1_lim_num {w g : ℂ → ℂ} {q : ℂ} {L : Filter ℂ} (hw : ContinuousAt w q)
    (hw' : ContinuousAt (deriv w) q) (hg : Tendsto g L (𝓝 q)) (hu : Tendsto (fun z => z - g z) L (𝓝 0)) :
    Tendsto (fun z => w (g z) + (z - g z) * deriv w (g z)) L (𝓝 (w q)) := by
  have := (hw.tendsto.comp hg).add (hu.mul (hw'.tendsto.comp hg))
  rwa [zero_mul, add_zero] at this

/-- A complex derivative `c` at `y` is the real derivative `c • id`. -/
theorem t203_c1_hasFDerivAt_of_deriv {f : ℂ → ℂ} {c y : ℂ} (h : HasDerivAt f c y) :
    HasFDerivAt f (c • ContinuousLinearMap.id ℝ ℂ) y := by
  refine (h.hasFDerivAt.restrictScalars ℝ).congr_fderiv ?_
  ext v
  simp [mul_comm]

/-- Inside, `w₁/w₂` has complex derivative `-1/w₂²` (Wronskian `1`) and is `C¹` where `w₂ ≠ 0`. -/
theorem t203_c1_quot {D : Set ℂ} (hDo : IsOpen D) {w₁ w₂ : ℂ → ℂ} (hw₁ : DifferentiableOn ℂ w₁ D)
    (hw₂ : DifferentiableOn ℂ w₂ D) {y : ℂ} (hy : y ∈ D) (hW : w₁ y * deriv w₂ y - w₂ y * deriv w₁ y = 1)
    (h0 : w₂ y ≠ 0) :
    HasFDerivAt (fun w => w₁ w / w₂ w) ((-1 / w₂ y ^ 2) • ContinuousLinearMap.id ℝ ℂ) y ∧
      ContDiffAt ℝ 1 (fun w => w₁ w / w₂ w) y := by
  have a1 := hw₁.analyticAt (hDo.mem_nhds hy)
  have a2 := hw₂.analyticAt (hDo.mem_nhds hy)
  have hd := a1.differentiableAt.hasDerivAt.div a2.differentiableAt.hasDerivAt h0
  have e : (deriv w₁ y * w₂ y - w₁ y * deriv w₂ y) / w₂ y ^ 2 = -1 / w₂ y ^ 2 := by
    congr 1
    linear_combination -hW
  rw [e] at hd
  exact ⟨t203_c1_hasFDerivAt_of_deriv hd, ((a1.div a2 h0).contDiffAt (n := 1)).restrict_scalars ℝ⟩

/-- `0 ≤ c₀`: `D̄'` is compact, so its complement is nonempty and the invariant bound bounds a norm. -/
theorem t203_c1_c0_nonneg {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) : 0 ≤ c₀ := by
  obtain ⟨-, -, hcpt, -, -, -, -, -, -, -, -, -, hc₀, -⟩ := h
  obtain ⟨z, hz⟩ : ((closure D')ᶜ).Nonempty :=
    nonempty_compl.2 fun he => noncompact_univ ℂ (he ▸ hcpt)
  exact le_trans (by positivity) (hc₀ z hz)

/-- **Cases (b), (c)**: at `z ∈ D̄'` with `w₂ z ≠ 0` the extension is `C¹` at `z` with the derivative `-1/w₂²` of
`w₁/w₂`: on a small open `U`, `ψ = F - w₁/w₂` vanishes on `D̄'`, is `C¹` off it with `dψ → 0` at `∂D'`
(`t203_fderiv_tendsto` with `t203_decay`), so `t203_contDiffOn` and `t203_segment` apply. -/
theorem t203_c1_inside {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {z : ℂ} (hzS : z ∈ closure D') (hw₂z : w₂ z ≠ 0) :
    ContDiffAt ℝ 1 (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z ∧
      HasFDerivAt (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w))
        ((-1 / w₂ z ^ 2) • ContinuousLinearMap.id ℝ ℂ) z := by
  have hdec := fun q (hq : q ∈ closure D') => t203_c1_decay h hq
  have hout := fun y (hy : y ∉ closure D') (hD : w₂ (g y) + (y - g y) * deriv w₂ (g y) ≠ 0) =>
    t203_c1_out_pt h hy hD
  obtain ⟨hDo, -, -, hsub, -, hw₁, hw₂, hode, -, -, hgR, -⟩ := h
  obtain ⟨E, hE⟩ : ∃ E : ℂ → ℂ, E = fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w) := ⟨_, rfl⟩
  rw [← hE]
  have hEy : ∀ y : ℂ, E y = extToC (t203_ext w₁ w₂ g (closure D') p y) := fun y => by rw [hE]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = fun w => E w - w₁ w / w₂ w := ⟨_, rfl⟩
  have hψy : ∀ y, ψ y = E y - w₁ y / w₂ y := fun y => by rw [hψ]
  have hzD : z ∈ D := hsub hzS
  have hgD : ∀ y ∉ closure D', g y ∈ D := fun y hy =>
    hsub (subset_closure (hgR.2.1 ▸ mem_image_of_mem g hy : g y ∈ D' \ {p}).1)
  have hc1 : ∀ y ∈ D, ContinuousAt w₁ y := fun y hy =>
    (hw₁.differentiableAt (hDo.mem_nhds hy)).continuousAt
  have hc2 : ∀ y ∈ D, ContinuousAt w₂ y := fun y hy =>
    (hw₂.differentiableAt (hDo.mem_nhds hy)).continuousAt
  have hc1' : ∀ y ∈ D, ContinuousAt (deriv w₁) y := fun y hy =>
    ((hw₁.deriv hDo).differentiableAt (hDo.mem_nhds hy)).continuousAt
  have hc2' : ∀ y ∈ D, ContinuousAt (deriv w₂) y := fun y hy =>
    ((hw₂.deriv hDo).differentiableAt (hDo.mem_nhds hy)).continuousAt
  -- the coefficient `φ/2 = w₁' w₂'' - w₂' w₁''`, continuous on `D`
  obtain ⟨a₀, ha₀c, ha₀e⟩ : ∃ a₀ : ℂ → ℂ, (∀ y ∈ D, ContinuousAt a₀ y) ∧ ∀ y ∈ D, a₀ y = φ y / 2 :=
    ⟨fun ζ => deriv w₁ ζ * deriv (deriv w₂) ζ - deriv w₂ ζ * deriv (deriv w₁) ζ,
      fun y hy => ((hc1' y hy).mul
        (((hw₂.deriv hDo).deriv hDo).differentiableAt (hDo.mem_nhds hy)).continuousAt).sub
        ((hc2' y hy).mul (((hw₁.deriv hDo).deriv hDo).differentiableAt (hDo.mem_nhds hy)).continuousAt),
      fun y hy => by
        obtain ⟨o1, o2, hW⟩ := hode y hy
        linear_combination deriv w₁ y * o2 - deriv w₂ y * o1 + φ y / 2 * hW⟩
  -- the open set `U`
  have hev1 : ∀ᶠ y in 𝓝[(closure D')ᶜ] z, w₂ (g y) + (y - g y) * deriv w₂ (g y) ≠ 0 := by
    obtain ⟨hg, hu, -⟩ := hdec z hzS
    exact (t203_c1_lim_num (hc2 z hzD) (hc2' z hzD) hg hu).eventually_ne hw₂z
  obtain ⟨U, hUP, hUo, hzU⟩ := _root_.eventually_nhds_iff.1 ((hDo.eventually_mem hzD).and
    (((hc2 z hzD).eventually_ne hw₂z).and (eventually_nhdsWithin_iff.1 hev1)))
  have hψ0 : ∀ y ∈ U ∩ closure D', ψ y = 0 := fun y hy => by
    rw [hψy, hEy, t203_c1_ext_in hy.2, t203_c1_extToC_ratio (hUP y hy.1).2.1, sub_self]
  have hout' : ∀ y ∈ U \ closure D', ContDiffAt ℝ 1 ψ y ∧
      HasFDerivAt ψ (((-1 / (w₂ (g y) + (y - g y) * deriv w₂ (g y)) ^ 2) • ContinuousLinearMap.id ℝ ℂ +
        (-(φ (g y) / 2) * (y - g y) ^ 2 / (w₂ (g y) + (y - g y) * deriv w₂ (g y)) ^ 2) • fderiv ℝ g y) -
        (-1 / w₂ y ^ 2) • ContinuousLinearMap.id ℝ ℂ) y := by
    intro y hy
    obtain ⟨hyD, hw₂y, hDy⟩ := hUP y hy.1
    obtain ⟨hC, hF, hev⟩ := hout y hy.2 (hDy hy.2)
    rw [← hE] at hev
    obtain ⟨q1, q2⟩ := t203_c1_quot hDo hw₁ hw₂ hyD (hode y hyD).2.2 hw₂y
    rw [hψ]
    exact ⟨(hC.congr_of_eventuallyEq hev).sub q2, (hF.congr_of_eventuallyEq hev).sub q1⟩
  have hC1 : ContDiffOn ℝ 1 ψ (U \ closure D') := fun y hy => (hout' y hy).1.contDiffWithinAt
  have hψd : ∀ y ∈ U \ closure D', DifferentiableAt ℝ ψ y := fun y hy => (hout' y hy).2.differentiableAt
  have hψc : ContinuousOn ψ U := by
    intro y hyU
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hyS : y ∈ closure D'
    · obtain ⟨hyD, hw₂y, -⟩ := hUP y hyU
      have hsplit : 𝓝 y = 𝓝[closure D'] y ⊔ 𝓝[(closure D')ᶜ] y := by
        rw [← nhdsWithin_union, union_compl_self, nhdsWithin_univ]
      show Tendsto ψ (𝓝 y) (𝓝 (ψ y))
      rw [hψ0 y ⟨hyU, hyS⟩, hsplit]
      refine Tendsto.sup ?_ ?_
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hyU), self_mem_nhdsWithin] with y' h1 h2
        exact (hψ0 y' ⟨h1, h2⟩).symm
      · obtain ⟨hg, hu, -⟩ := hdec y hyS
        have hN := t203_c1_lim_num (hc1 y hyD) (hc1' y hyD) hg hu
        have hD := t203_c1_lim_num (hc2 y hyD) (hc2' y hyD) hg hu
        have hG : Tendsto (fun w => w₁ w / w₂ w) (𝓝[(closure D')ᶜ] y) (𝓝 (w₁ y / w₂ y)) :=
          ((hc1 y hyD).div (hc2 y hyD) hw₂y).tendsto.mono_left nhdsWithin_le_nhds
        have := (hN.div hD hw₂y).sub hG
        rw [sub_self] at this
        refine this.congr' ?_
        filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hyU), self_mem_nhdsWithin] with y' h1 h2
        rw [hψy, hEy, t203_c1_ext_out h2, t203_c1_extToC_ratio ((hUP y' h1).2.2 h2)]
        rfl
    · exact (hout' y ⟨hyU, hyS⟩).1.continuousAt
  have hlim : ∀ q ∈ U ∩ frontier (closure D'),
      Tendsto (fun y => fderiv ℝ ψ y) (𝓝[U \ closure D'] q) (𝓝 0) := by
    rintro q ⟨hqU, hqf⟩
    have hqS : q ∈ closure D' := isClosed_closure.frontier_subset hqf
    obtain ⟨hqD, hw₂q, -⟩ := hUP q hqU
    obtain ⟨hg, -, hd⟩ := hdec q hqS
    have hmono : 𝓝[U \ closure D'] q ≤ 𝓝[(closure D')ᶜ] q := nhdsWithin_mono q fun x hx => hx.2
    have key := t203_fderiv_tendsto (w₂ := w₂) (w₂' := deriv w₂) (a := a₀) (g := g) (dg := fderiv ℝ g)
      (L := 𝓝[U \ closure D'] q) (q := q) (hc2 q hqD) (hc2' q hqD) (ha₀c q hqD) hw₂q
      (tendsto_id.mono_left nhdsWithin_le_nhds) (hg.mono_left hmono) (hd.mono_left hmono)
    refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [(hout' y hy).2.fderiv, ha₀e (g y) (hgD y hy.2)]
  have hψC := t203_contDiffOn hUo isClosed_closure hψc hψ0 hC1 hlim
  have hψ0z := t203_segment hUo isClosed_closure hψc hψ0 hψd hlim z ⟨hzU, hzS⟩
  obtain ⟨q1, q2⟩ := t203_c1_quot hDo hw₁ hw₂ hzD (hode z hzD).2.2 hw₂z
  have hEsum : E = fun w => w₁ w / w₂ w + ψ w := funext fun w => by rw [hψy]; ring
  rw [hEsum]
  refine ⟨q2.add (hψC.contDiffAt (hUo.mem_nhds hzU)), ?_⟩
  have := q1.add hψ0z
  rwa [add_zero] at this

/-- The chart-level statement for the extension itself (`M = id`), at a finite `z` with finite value: case (a)
off `D̄'` (`t203_c1_outside`), cases (b)/(c) on `D̄'` (`t203_c1_inside`, where `∂̄ = 0` and `∂ = -1/w₂² ≠ 0`). -/
theorem t203_c1_core {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {z : ℂ}
    (hz : t203_ext w₁ w₂ g (closure D') p z ≠ extInf) :
    ContDiffAt ℝ 1 (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z ∧
      ‖dzbar (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ <
        ‖dz (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ ∧
      ‖dzbar (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ ≤
        c₀ * s / 2 * ‖dz (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z‖ := by
  by_cases hzS : z ∈ closure D'
  · rw [t203_c1_ext_in hzS] at hz
    have hw₂z := t203_c1_ratio_ne hz
    have hc0 := t203_c1_c0_nonneg h
    have hs0 : 0 ≤ s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨hC, hF⟩ := t203_c1_inside h hzS hw₂z
    have e1 := t203_dz_of_hasFDerivAt hF
    have e2 := t203_dzbar_of_hasFDerivAt hF
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at e1 e2
    have hz1 : dz (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z = -1 / w₂ z ^ 2 := by
      rw [e1]
      linear_combination (-(-1 / w₂ z ^ 2) / 2) * I_sq
    have hz2 : dzbar (fun w : ℂ => extToC (t203_ext w₁ w₂ g (closure D') p w)) z = 0 := by
      rw [e2]
      linear_combination ((-1 / w₂ z ^ 2) / 2) * I_sq
    refine ⟨hC, ?_, ?_⟩
    · rw [hz1, hz2, norm_zero]
      exact norm_pos_iff.2 (div_ne_zero (neg_ne_zero.2 one_ne_zero) (pow_ne_zero 2 hw₂z))
    · rw [hz2, norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg hc0 hs0) two_pos.le) (norm_nonneg _)
  · rw [t203_c1_ext_out hzS] at hz
    exact t203_c1_outside h hzS (t203_c1_ratio_ne hz)

/-- The normalized pair `(a w₁ + b w₂, c w₁ + d w₂)` with `ad - bc = 1` is again a Stage B setting (same ODE,
Wronskian `ad - bc = 1`). -/
theorem t203_c1_setting_comb {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {a b c d : ℂ} (hdet : a * d - b * c = 1) :
    t203_Setting D D' (fun y => a * w₁ y + b * w₂ y) (fun y => c * w₁ y + d * w₂ y) φ g p K₁ c₀ s := by
  obtain ⟨hDo, hD'o, hcpt, hsub, hψ, hw₁, hw₂, hode, hrest⟩ := h
  refine ⟨hDo, hD'o, hcpt, hsub, hψ, (hw₁.const_mul a).add (hw₂.const_mul b),
    (hw₁.const_mul c).add (hw₂.const_mul d), fun z hz => ?_, hrest⟩
  obtain ⟨e1, e1'⟩ := t203_ode_comb_deriv hDo hw₁ hw₂ a b hz
  obtain ⟨e2, e2'⟩ := t203_ode_comb_deriv hDo hw₁ hw₂ c d hz
  obtain ⟨o1, o2, hW⟩ := hode z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [e1']
    linear_combination a * o1 + b * o2
  · rw [e2']
    linear_combination c * o1 + d * o2
  · rw [e1, e2]
    exact (neh_wronskian_comb (a := a) (b := b) (c := c) (d := d) hW).trans hdet

/-- **Normalization**: `M ∘ F` is the extension built from the pair `(a w₁ + b w₂, c w₁ + d w₂)/σ` (at every
finite point; `t203_c1_mobius_ratio`, the pair never vanishes by the Wronskian). -/
theorem t203_c1_mobius_ext {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {a b c d σ : ℂ} (hσ : σ ≠ 0) (w : ℂ) :
    mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w) =
      t203_ext (fun y => a / σ * w₁ y + b / σ * w₂ y) (fun y => c / σ * w₁ y + d / σ * w₂ y) g
        (closure D') p w := by
  obtain ⟨hDo, -, -, hsub, -, hw₁, hw₂, hode, -, -, hgR, -⟩ := h
  by_cases hw : w ∈ closure D'
  · rw [t203_c1_ext_in hw, t203_c1_ext_in hw]
    refine t203_c1_mobius_ratio hσ ?_
    by_cases h1 : w₁ w = 0
    · refine Or.inr fun h2 => ?_
      have := (hode w (hsub hw)).2.2
      rw [h1, h2] at this
      simp at this
    · exact Or.inl h1
  · rw [t203_c1_ext_out hw, t203_c1_ext_out hw]
    have hgw : g w ∈ D := hsub (subset_closure (hgR.2.1 ▸ mem_image_of_mem g hw : g w ∈ D' \ {p}).1)
    obtain ⟨e1, -⟩ := t203_ode_comb_deriv hDo hw₁ hw₂ (a / σ) (b / σ) hgw
    obtain ⟨e2, -⟩ := t203_ode_comb_deriv hDo hw₁ hw₂ (c / σ) (d / σ) hgw
    have hW := (hode (g w) hgw).2.2
    rw [e1, e2, t203_c1_mobius_ratio hσ ?_]
    · congr 1 <;> ring
    · by_cases hD0 : w₂ (g w) + (w - g w) * deriv w₂ (g w) = 0
      · exact Or.inl (t203_num_ne_zero hW hD0)
      · exact Or.inr hD0

/-- **B-C¹** (the chart-level `C¹` and dilatation bound): for every Möbius map `M` and every finite `z` with
`M(F z) ≠ ∞`, the plane map `G = M ∘ F` is `C¹` at `z` with `|∂̄G| < |∂G|` and `|∂̄G| ≤ (c₀ s/2) |∂G|`
(`M ∘ F` is the extension built from the normalized pair `(aw₁ + bw₂, cw₁ + dw₂)/√(ad - bc)`; inside: holomorphic;
outside: (20.10), `t203_F_bound_book`; across `∂D'`: `t203_segment`/`t203_contDiffOn` with `t203_fderiv_tendsto`). -/
theorem t203_ext_contDiffAt {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {z : ℂ}
    (hz : mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p z) ≠ extInf) :
    ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) z ∧
      ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) z‖ <
        ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) z‖ ∧
      ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) z‖ ≤
        c₀ * s / 2 * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) z‖ := by
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (a * d - b * c) two_pos
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hσ]
    ring
  have hdet' : a / σ * (d / σ) - b / σ * (c / σ) = 1 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← hσ, pow_two]
    exact div_self (mul_ne_zero hσ0 hσ0)
  have h' := t203_c1_setting_comb h hdet'
  have hfun : (fun w : ℂ => extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p w))) =
      fun w : ℂ => extToC (t203_ext (fun y => a / σ * w₁ y + b / σ * w₂ y)
        (fun y => c / σ * w₁ y + d / σ * w₂ y) g (closure D') p w) :=
    funext fun w => by rw [t203_c1_mobius_ext h hσ0 w]
  rw [t203_c1_mobius_ext h hσ0 z] at hz
  rw [hfun]
  exact t203_c1_core h' hz

/-- **B-inj** (local injectivity at finite points): at every finite `z` the extension is injective on a neighbourhood
(choose `M` with `M(F z) ≠ ∞`; `M ∘ F` is `C¹` at `z` with positive Jacobian, so it is locally injective by the
inverse function theorem). -/
theorem t203_ext_locInj {D D' : Set ℂ} {w₁ w₂ φ g : ℂ → ℂ} {p : ℂ} {K₁ c₀ s : ℝ}
    (h : t203_Setting D D' w₁ w₂ φ g p K₁ c₀ s) (z : ℂ) :
    ∃ U ∈ 𝓝 (z : ExtPlane), InjOn (t203_ext w₁ w₂ g (closure D') p) U := by
  obtain ⟨a, b, c, d, hdet, hz⟩ : ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p z) ≠ extInf := by
    by_cases hinf : t203_ext w₁ w₂ g (closure D') p z = extInf
    · refine ⟨0, 1, 1, 0, by norm_num, ?_⟩
      rw [hinf, mobiusExt_infty_of_ne one_ne_zero]
      exact OnePoint.coe_ne_infty _
    · obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hinf
      refine ⟨1, 0, 0, 1, by norm_num, ?_⟩
      rw [← hv, mobiusExt_coe (by norm_num)]
      exact OnePoint.coe_ne_infty _
  obtain ⟨hC1, hlt, -⟩ := t203_ext_contDiffAt h hdet hz
  have hJ : LinearMap.det (fderiv ℝ (fun w : ℂ => extToC (mobiusExt a b c d
      (t203_ext w₁ w₂ g (closure D') p w))) z : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    rw [det_fderiv_eq_jacobian (hC1.differentiableAt one_ne_zero), jacobian]
    have h0 := norm_nonneg (dzbar (fun w : ℂ => extToC (mobiusExt a b c d
      (t203_ext w₁ w₂ g (closure D') p w))) z)
    nlinarith
  obtain ⟨V, hV, hinj⟩ := ba_injOn_of_contDiff hC1 hJ
  refine ⟨((↑) : ℂ → ExtPlane) '' V, OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds hV, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [hinj hx hy (show extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p x)) =
    extToC (mobiusExt a b c d (t203_ext w₁ w₂ g (closure D') p y)) by rw [hxy])]

/-! ### Theorem 20.3 track, Stage C interface (coordinator 553e2d): assembly of Theorem 20.3 -/

/-- **C-fam** (the extension family): with `c₀` the invariant bound of `t203_reflection`, a locally univalent
meromorphic `f` in a `K`-quasidisc `D` with `‖S_f‖_D ≤ s`, `c₀ s < 1`, has, on the exhaustion `Dₙ ↑ D`
(`t203_exhaustion`), extensions `Fₙ` of `f|Dₙ` to homeomorphisms of `ℂ̄` which are, in every Möbius chart, `C¹` with
`|∂̄| ≤ (c₀ s/2) |∂| < |∂|` at finite points (`t203_ode_pair`, `t203_reflection` on `Dₙ`, `t203_schwarzianNorm_mono`,
Stage B, and `t203_covering`). -/
theorem t203_family {K : ℝ} (hK : 1 ≤ K) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ D : Set ℂ, IsKQuasidisc D K → ∀ f : ℂ → ℂ, IsLocUnivMero f D → ∀ s : ℝ, 0 ≤ s →
      c₀ * s < 1 → schwarzianNorm f D ≤ ENNReal.ofReal s →
      ∃ (Dn : ℕ → Set ℂ) (F : ℕ → ExtPlane → ExtPlane), Monotone Dn ∧ (∀ n, IsOpen (Dn n)) ∧ ⋃ n, Dn n = D ∧
        ∀ n, Function.Bijective (F n) ∧ Continuous (F n) ∧ (∀ z ∈ Dn n, F n z = meroToExt f z) ∧
          ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ z : ℂ, mobiusExt a b c d (F n z) ≠ extInf →
            ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z ∧
            ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ <
              ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ∧
            ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ≤
              c₀ * s / 2 * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ := by
  obtain ⟨c₀, hc₀, hrefl⟩ := t203_reflection hK
  refine ⟨c₀, hc₀, fun D hD f hf s hs hcs hSf => ?_⟩
  obtain ⟨Dn, hDn, hmono, hU⟩ := t203_exhaustion hD
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hrat⟩ := t203_ode_pair hD hf
  have hDo : IsOpen D := hD.1.1
  obtain ⟨ψD, hψD, -⟩ := uq_exists_uniformizer hD.1
  have hφD : IsConformalOnto (cayley ∘ ψD) D unitDisc := isConformalOnto_cayley.comp hψD
  have hset : ∀ n, ∃ (g : ℂ → ℂ) (K₁ : ℝ) (p : ℂ),
      t203_Setting D (Dn n) w₁ w₂ (schwarzian f) g p K₁ c₀ s := by
    intro n
    obtain ⟨hq, hb, hcl⟩ := hDn n
    obtain ⟨g, K₁, p, hp, hC1, hR, hT, hB⟩ := hrefl (Dn n) hq hb
    have hDno : IsOpen (Dn n) := hq.1.1
    obtain ⟨ψ, hψ, -⟩ := uq_exists_uniformizer hq.1
    have hφ : IsConformalOnto (cayley ∘ ψ) (Dn n) unitDisc := isConformalOnto_cayley.comp hψ
    have hsub : Dn n ⊆ D := subset_closure.trans hcl
    have hnorm := (t203_schwarzianNorm_mono hDo hDno hsub hφD hφ f).trans hSf
    refine ⟨g, K₁, p, hDo, hDno, hb.isCompact_closure, hcl, ⟨_, hφ⟩, hw₁, hw₂, hode, hp, hC1, hR, hT, hB, hs,
      (by linarith), fun ζ hζ => ?_⟩
    have hpos := s20l_a2_density_pos hDno hφ hζ
    have h1 : ENNReal.ofReal (‖schwarzian f ζ‖ / poincareDensity (Dn n) ζ ^ 2) ≤ schwarzianNorm f (Dn n) :=
      le_iSup₂ (f := fun z (_ : z ∈ Dn n) => ENNReal.ofReal (‖schwarzian f z‖ / poincareDensity (Dn n) z ^ 2)) ζ hζ
    have h2 := h1.trans hnorm
    rw [ENNReal.ofReal_le_ofReal_iff hs, div_le_iff₀ (pow_pos hpos 2)] at h2
    exact h2
  choose g K₁ p hSet using hset
  refine ⟨Dn, fun n => t203_ext w₁ w₂ (g n) (closure (Dn n)) (p n), hmono, fun n => (hDn n).1.1.1, hU,
    fun n => ⟨t203_covering (t203_ext_continuous (hSet n)) (t203_ext_locInj (hSet n)),
      t203_ext_continuous (hSet n), fun z hz => ?_, fun a b c d hdet z hz => t203_ext_contDiffAt (hSet n) hdet hz⟩⟩
  have hzc : z ∈ closure (Dn n) := subset_closure hz
  change @ite ExtPlane (z ∈ closure (Dn n)) (Classical.propDecidable _) (t203_ratio (w₁ z) (w₂ z)) _ = _
  rw [ite_eq_left hzc]
  exact (hrat z (subset_closure.trans (hDn n).2.2 hz)).symm

/-- At a point where `f` is analytic, `meroToExt f z` is the finite point `f z`. -/
theorem t203_univ_meroToExt_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    meroToExt f z = ((f z : ℂ) : ExtPlane) := by
  unfold meroToExt
  split_ifs with h
  · rw [toMeromorphicNFAt_eq_self.mpr hf.meromorphicNFAt]
  · exact absurd hf.meromorphicOrderAt_nonneg h

/-- At a point of negative meromorphic order (a pole), `meroToExt f z = ∞`. -/
theorem t203_univ_meroToExt_of_order_neg {f : ℂ → ℂ} {z : ℂ} (hf : meromorphicOrderAt f z < 0) :
    meroToExt f z = extInf := by
  unfold meroToExt
  split_ifs with h
  · exact absurd h (not_le.mpr hf)
  · rfl

/-- If injective maps `Fₙ` agree with `meroToExt f` on `Dₙ ↑ D`, then `meroToExt f` is injective on `D`: two points
of `D` lie in a common `Dₙ`. -/
theorem t203_univ_injOn {D : Set ℂ} {f : ℂ → ℂ} {Dn : ℕ → Set ℂ} (hmono : Monotone Dn)
    (hU : ⋃ n, Dn n = D) {F : ℕ → ExtPlane → ExtPlane} (hinj : ∀ n, Function.Injective (F n))
    (hF : ∀ n, ∀ z ∈ Dn n, F n z = meroToExt f z) : InjOn (meroToExt f) D := by
  intro z hz w hw hzw
  rw [← hU, mem_iUnion] at hz hw
  obtain ⟨i, hi⟩ := hz
  obtain ⟨j, hj⟩ := hw
  have hi' : z ∈ Dn (max i j) := hmono (le_max_left i j) hi
  have hj' : w ∈ Dn (max i j) := hmono (le_max_right i j) hj
  exact OnePoint.coe_injective (hinj (max i j) (by rw [hF _ z hi', hF _ w hj', hzw]))

/-- **C-univ** ((i) of Theorem 20.3): if injective maps `Fₙ` of `ℂ̄` agree with `meroToExt f` on `Dₙ ↑ D`, then `f` is
univalent in `D` (`meroToExt f` is injective on `D`; at holomorphic points it is `f`, at poles `∞`). -/
theorem t203_univalent {D : Set ℂ} {f : ℂ → ℂ} (hf : IsLocUnivMero f D) {Dn : ℕ → Set ℂ} (hmono : Monotone Dn)
    (hU : ⋃ n, Dn n = D) {F : ℕ → ExtPlane → ExtPlane} (hinj : ∀ n, Function.Injective (F n))
    (hF : ∀ n, ∀ z ∈ Dn n, F n z = meroToExt f z) : IsUnivMero f D := by
  have hinjD := t203_univ_injOn hmono hU hinj hF
  have hpole : ∀ x ∈ D, ¬ AnalyticAt ℂ f x → meroToExt f x = extInf := fun x hx hna => by
    rcases hf.2 x hx with h | h
    · exact absurd h.1 hna
    · exact t203_univ_meroToExt_of_order_neg h.1
  refine ⟨hf, fun z hz w hw hzw => ?_, fun z hz w hw => ?_⟩
  · refine hinjD hz.1 hw.1 ?_
    rw [t203_univ_meroToExt_of_analyticAt hz.2, t203_univ_meroToExt_of_analyticAt hw.2, hzw]
  · exact hinjD hz.1 hw.1 (by rw [hpole z hz.1 hz.2, hpole w hw.1 hw.2])

/-- The dilatation quotient bound: `|∂̄f| < |∂f|` and `|∂̄f| ≤ k|∂f|` with `k < 1` give `D_f ≤ (1+k)/(1-k)`. -/
theorem t203_pqc_dilatationQuotient_le {f : ℂ → ℂ} {z : ℂ} {k : ℝ} (hk1 : k < 1)
    (hlt : ‖dzbar f z‖ < ‖dz f z‖) (hle : ‖dzbar f z‖ ≤ k * ‖dz f z‖) :
    dilatationQuotient f z ≤ (1 + k) / (1 - k) := by
  have hp : 0 < ‖dz f z‖ := (norm_nonneg _).trans_lt hlt
  have hm : ‖complexDilatation f z‖ ≤ k := by
    rw [complexDilatation, norm_div, div_le_iff₀ hp]
    exact hle
  rw [dilatationQuotient, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **C-qc** (a homeomorphism of `ℂ̄` fixing `∞`, `C¹` with `|∂̄| ≤ k|∂| < |∂|` at every finite point but one, is
`(1+k)/(1-k)`-q.c. on `ℂ`): `isKQC_of_isC1Quasiconformal` on `ℂ ∖ {z₀}`, then `b4_isKQC_univ_of_punctured`. -/
theorem t203_plane_qc {Φ : ExtPlane → ExtPlane} (hΦ : Function.Bijective Φ) (hc : Continuous Φ)
    (hinf : Φ extInf = extInf) {k K' : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hK' : (1 + k) / (1 - k) ≤ K') {z₀ : ℂ}
    (hC1 : ∀ z : ℂ, z ≠ z₀ → ContDiffAt ℝ 1 (fun w : ℂ => extToC (Φ w)) z ∧
      ‖dzbar (fun w : ℂ => extToC (Φ w)) z‖ < ‖dz (fun w : ℂ => extToC (Φ w)) z‖ ∧
      ‖dzbar (fun w : ℂ => extToC (Φ w)) z‖ ≤ k * ‖dz (fun w : ℂ => extToC (Φ w)) z‖) :
    IsKQC (fun w : ℂ => extToC (Φ w)) univ K' ∧ (fun w : ℂ => extToC (Φ w)) '' univ = univ := by
  have _hk0 := hk0
  obtain ⟨-, hH⟩ := wd_b_plane_homeo hc hΦ.1 hinf
  have hK1 : 1 ≤ K' := by
    have h1 : 1 ≤ (1 + k) / (1 - k) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  have hQC : IsC1Quasiconformal (fun w : ℂ => extToC (Φ w)) {z₀}ᶜ K' :=
    ⟨isOpen_compl_singleton, hK1, fun z hz => (hC1 z hz).1.contDiffWithinAt,
      aqc_isHomeomorphOnto_restrict hH isOpen_univ (subset_univ _) isOpen_compl_singleton,
      fun z hz => ⟨(hC1 z hz).2.1,
        (t203_pqc_dilatationQuotient_le hk1 (hC1 z hz).2.1 (hC1 z hz).2.2).trans hK'⟩⟩
  exact ⟨b4_isKQC_univ_of_punctured hH (isKQC_of_isC1Quasiconformal hQC), hH.2.2.1⟩

/-- **NB** (growth bound; a copy of the downstream S21 `ut2_nb_upper`): a normalized `K`-q.c. map of the plane
satisfies `|f(z)| ≤ λ(K Λ(R))` for `|z| ≤ R` (Theorem 15.3 and the radial lower bound `td_dist_lower` give
`Λ(|f(z)|) ≤ K Λ(|z|)`). -/
theorem t203_lim_nb_upper {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖z‖ ≤ R) : ‖f z‖ ≤ lambdaInv (K * quadLambda R) := by
  obtain ⟨hqc, hs, h0, h1⟩ := hf
  have hK : 1 ≤ K := hqc.2.1
  have hΛR : 0 < quadLambda R := b4_num_quadLambda_pos hR
  have hinj := hqc.2.2.1.2.1
  by_cases hz0 : z = 0
  · rw [hz0, h0, norm_zero]
    exact (td_quadLambda_lambdaInv (mul_pos (by linarith) hΛR)).1.le
  by_cases hz1 : z = 1
  · rw [hz1, norm_one] at hz
    rw [hz1, h1, norm_one]
    refine b4_le_lambdaInv one_pos ?_
    rw [b4_quadLambda_one]
    have hΛR1 : 1 ≤ quadLambda R := by
      rw [← b4_quadLambda_one]
      exact quadLambda_strictMono.1.monotoneOn (mem_Ioi.2 one_pos) hR hz
    exact one_le_mul_of_one_le_of_one_le hK hΛR1
  have hfz0 : f z ≠ 0 := fun h => hz0 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
  have hfz1 : f z ≠ 1 := fun h => hz1 (hinj (mem_univ _) (mem_univ _) (h.trans h1.symm))
  have hteich := thm15_3_teichmuller ⟨hqc, hs, h0, h1⟩ hz0 hz1
  have hlow := td_dist_lower ⟨hz0, hz1⟩ ⟨hfz0, hfz1⟩
  have habs : |Real.log (quadLambda ‖f z‖) - Real.log (quadLambda ‖z‖)| ≤ Real.log K :=
    (ENNReal.ofReal_le_ofReal_iff (Real.log_nonneg hK)).1 (hlow.trans hteich)
  have hs0 : 0 < ‖f z‖ := norm_pos_iff.2 hfz0
  have hz0' : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hΛz : 0 < quadLambda ‖z‖ := b4_num_quadLambda_pos hz0'
  have hlog : Real.log (quadLambda ‖f z‖) ≤ Real.log (K * quadLambda ‖z‖) := by
    rw [Real.log_mul (by linarith) hΛz.ne']
    linarith [le_abs_self (Real.log (quadLambda ‖f z‖) - Real.log (quadLambda ‖z‖))]
  have hle : quadLambda ‖f z‖ ≤ K * quadLambda ‖z‖ :=
    (Real.log_le_log_iff (b4_num_quadLambda_pos hs0) (mul_pos (by linarith) hΛz)).1 hlog
  refine b4_le_lambdaInv hs0 (hle.trans (mul_le_mul_of_nonneg_left ?_ (by linarith)))
  exact quadLambda_strictMono.1.monotoneOn hz0' hR hz

/-- **NB'** (properness; a copy of the downstream S21 `ut2_nb_lower`): `|z| ≤ λ(K Λ(R))` whenever `|f(z)| ≤ R` (NB
for the normalized `K`-q.c. map `f⁻¹`). -/
theorem t203_lim_nb_lower {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖f z‖ ≤ R) : ‖z‖ ≤ lambdaInv (K * quadLambda R) := by
  obtain ⟨hqc, hs, h0, h1⟩ := hf
  have hinv := thm7_2_inv hqc
  rw [hs] at hinv
  have hleft : LeftInvOn (Function.invFunOn f univ) f univ := hqc.2.2.1.2.1.leftInvOn_invFunOn
  have hg0 : Function.invFunOn f univ 0 = 0 := by
    have h := hleft (mem_univ 0)
    rwa [h0] at h
  have hg1 : Function.invFunOn f univ 1 = 1 := by
    have h := hleft (mem_univ 1)
    rwa [h1] at h
  have hgs : Function.invFunOn f univ '' univ = univ :=
    eq_univ_of_forall fun w => ⟨f w, mem_univ _, hleft (mem_univ w)⟩
  have hz' := t203_lim_nb_upper ⟨hinv, hgs, hg0, hg1⟩ hR hz
  rwa [hleft (mem_univ z)] at hz'

/-- **LG** (local to global; a copy of the downstream S21 `ut2_lg`): an injective map of an open set which is
`K`-q.c. near every point is `K`-q.c. there (it is an open map, hence a homeomorphism onto its image; then
`s13x_removable` with `L = ∅`). -/
theorem t203_lim_lg {g : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K) (hinj : InjOn g Ω)
    (hloc : ∀ z ∈ Ω, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K) : IsKQC g Ω K := by
  have hcont : ContinuousOn g Ω := fun z hz => by
    obtain ⟨U, hUo, hzU, -, hgU⟩ := hloc z hz
    exact ((hgU.2.2.1.1 z hzU).continuousAt (hUo.mem_nhds hzU)).continuousWithinAt
  refine s13x_removable (L := ∅) hΩ hK (qcl_f_isHomeomorphOnto_of_injOn hΩ hcont hinj) measure_empty
    (Eventually.of_forall fun x => by simp) (Eventually.of_forall fun y => by simp) fun z hz => hloc z hz.1

/-- **LIM** (Theorem 8.2 on an arbitrary open set; a copy of the downstream S21 `ut2_limit_isKQC`): an injective
locally uniform limit of `K`-q.c. maps of an open set is `K`-q.c. there (Theorem 8.2 on small discs, then LG). -/
theorem t203_lim_limit_isKQC {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω)
    (hqc : ∀ n, IsKQC (Fn n) Ω K) (hlim : TendstoLocallyUniformlyOn Fn F atTop Ω) (hinj : InjOn F Ω) :
    IsKQC F Ω K := by
  refine t203_lim_lg hΩ (hqc 0).2.1 hinj fun z hz => ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ z hz
  refine ⟨ball z r, isOpen_ball, mem_ball_self hr, hball, ?_⟩
  rcases thm8_2_limit isBounded_ball (isConnected_ball hr)
      (fun n => ac_t_isKQC_restrict (hqc n) isOpen_ball hball) (hlim.mono hball) with ⟨c, hc⟩ | h
  · -- a constant limit on the ball contradicts injectivity at the two points `z` and `z + r/2`
    have h1 : z ∈ ball z r := mem_ball_self hr
    have h2 : z + ((r / 2 : ℝ) : ℂ) ∈ ball z r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have heq := hinj (hball h1) (hball h2) ((hc z h1).trans (hc _ h2).symm)
    have h0 : ((r / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w => w - z) heq
      simpa using this.symm
    exact absurd (Complex.ofReal_eq_zero.1 h0) (half_pos hr).ne'
  · exact h

/-- **NF-a helper** (Arzelà–Ascoli on the plane with a pointwise bound; a copy of the downstream S21
`ut2_nfa_subseq`): continuous maps `gn n` of the plane with `‖gn n z‖ ≤ B z` which are equicontinuous at every point
have a locally uniformly convergent subsequence. -/
theorem t203_lim_nfa_subseq {B : ℂ → ℝ} {gn : ℕ → ℂ → ℂ} (hcont : ∀ n, Continuous (gn n))
    (hB : ∀ n z, ‖gn n z‖ ≤ B z)
    (heq : ∀ z₀ : ℂ, ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ ∀ n z, Dist.dist z z₀ < θ →
      Dist.dist (gn n z) (gn n z₀) < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, TendstoLocallyUniformly (fun n => gn (φ n)) f atTop := by
  choose θ hθpos hθ using heq
  set g : ℕ → C(ℂ, ℂ) := fun n => ⟨gn n, hcont n⟩
  set S : Set C(ℂ, ℂ) := {h : C(ℂ, ℂ) | (∀ z, ‖h z‖ ≤ B z) ∧
      ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ), Dist.dist z z₀ < θ z₀ η hη → Dist.dist (h z) (h z₀) ≤ η}
  have hgS : ∀ n, g n ∈ S := fun n => ⟨hB n, fun z₀ η hη z hz => (hθ z₀ η hη n z hz).le⟩
  set T : Set (ℂ → ℂ) := {u : ℂ → ℂ | (∀ z, ‖u z‖ ≤ B z) ∧
      ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ), Dist.dist z z₀ < θ z₀ η hη → Dist.dist (u z) (u z₀) ≤ η}
  have himage : ContinuousMap.toFun '' S = T := by
    apply Subset.antisymm
    · rintro u ⟨h, hhS, rfl⟩
      exact hhS
    · rintro u ⟨huA, huB⟩
      have hucont : Continuous u := by
        rw [Metric.continuous_iff]
        intro z₀ ε hε
        exact ⟨θ z₀ (ε / 2) (half_pos hε), hθpos z₀ (ε / 2) (half_pos hε),
          fun z hz => lt_of_le_of_lt (huB z₀ (ε / 2) (half_pos hε) z hz) (half_lt_self hε)⟩
      exact ⟨⟨u, hucont⟩, ⟨huA, huB⟩, rfl⟩
  have hTclosed : IsClosed T := by
    have hA : IsClosed {u : ℂ → ℂ | ∀ z, ‖u z‖ ≤ B z} := by
      rw [ofPred_forall]
      exact isClosed_iInter fun z => isClosed_le (continuous_apply z).norm continuous_const
    have hE : IsClosed {u : ℂ → ℂ | ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ),
        Dist.dist z z₀ < θ z₀ η hη → Dist.dist (u z) (u z₀) ≤ η} := by
      simp only [ofPred_forall]
      refine isClosed_iInter fun z₀ => isClosed_iInter fun η => isClosed_iInter fun hη =>
        isClosed_iInter fun z => ?_
      by_cases hp : Dist.dist z z₀ < θ z₀ η hη
      · simpa [hp] using isClosed_le ((continuous_apply z).dist (continuous_apply z₀))
          continuous_const
      · simp [hp]
    exact hA.inter hE
  have hTsub : T ⊆ Set.pi univ fun z : ℂ => closedBall (0 : ℂ) (B z) := by
    intro u hu i _
    simpa using hu.1 i
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := by
    rw [himage]
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      hTclosed hTsub
  have hS2 : Equicontinuous ((↑) : S → ℂ → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds x₀ (hθpos x₀ (ε / 2) (half_pos hε))] with x hx s
    calc Dist.dist ((s : C(ℂ, ℂ)) x₀) ((s : C(ℂ, ℂ)) x) = Dist.dist ((s : C(ℂ, ℂ)) x) ((s : C(ℂ, ℂ)) x₀) :=
          dist_comm _ _
      _ ≤ ε / 2 := s.2.2 x₀ (ε / 2) (half_pos hε) x hx
      _ < ε := half_lt_self hε
  obtain ⟨h, -, φ, hφmono, hφtend⟩ :=
    (ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2).tendsto_subseq hgS
  exact ⟨φ, hφmono, h, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hφtend⟩

/-- **NF-a** (normal family, extraction; a copy of the downstream S21 `ut2_nf_extract`): a sequence of normalized
`K`-q.c. maps of the plane has a locally uniformly convergent subsequence (the bound NB and Theorem 8.1's
equicontinuity on unit discs, then Arzelà–Ascoli). -/
theorem t203_lim_nf_extract {F : ℕ → ℂ → ℂ} {K : ℝ} (hF : ∀ n, IsKQCNormalizedPlane (F n) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ, TendstoLocallyUniformly (fun n => F (φ n)) G atTop := by
  refine t203_lim_nfa_subseq (B := fun z => lambdaInv (K * quadLambda (‖z‖ + 1)))
    (fun n => continuousOn_univ.1 (hF n).1.2.2.1.1)
    (fun n z => t203_lim_nb_upper (hF n) (by positivity) (by linarith)) fun z₀ η hη => ?_
  have hM : ∀ n, ∀ z ∈ ball z₀ 1, ‖F n z‖ ≤ lambdaInv (K * quadLambda (‖z₀‖ + 1)) := by
    intro n z hz
    refine t203_lim_nb_upper (hF n) (by positivity) ?_
    have h1 := norm_sub_norm_le z z₀
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  obtain ⟨θ, hθ, h⟩ := nf_f_equicontinuous_of_isKQC
    (fun n => ac_t_isKQC_restrict (hF n).1 isOpen_ball (subset_univ _)) hM (mem_ball_self one_pos) hη
  exact ⟨min θ 1, lt_min hθ one_pos, fun n z hz =>
    h n z (mem_ball.2 (hz.trans_le (min_le_right _ _))) (hz.trans_le (min_le_left _ _))⟩

/-- **NF-b** (normal family, the limit; a copy of the downstream S21 `ut2_nf_limit`): a locally uniform limit of
normalized `K`-q.c. maps of the plane is a normalized `K`-q.c. map of the plane (injective by Theorem 8.2 on large
discs since `G 0 = 0 ≠ 1 = G 1`, `K`-q.c. by LIM, onto since `G(ℂ)` is open and, by NB', closed). -/
theorem t203_lim_nf_limit {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K : ℝ} (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hlim : TendstoLocallyUniformly F G atTop) : IsKQCNormalizedPlane G K := by
  -- the normalization passes to the pointwise limit
  have hpt : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)) := fun z =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)
  have hG0 : G 0 = 0 :=
    tendsto_nhds_unique (hpt 0) (tendsto_const_nhds.congr fun n => ((hF n).2.2.1).symm)
  have hG1 : G 1 = 1 :=
    tendsto_nhds_unique (hpt 1) (tendsto_const_nhds.congr fun n => ((hF n).2.2.2).symm)
  -- `G` is injective: Theorem 8.2 on a disc containing `0, 1, z, w`, where `G` is not constant
  have hinj : InjOn G univ := by
    intro z _ w _ hzw
    have hr : (0 : ℝ) < ‖z‖ + ‖w‖ + 2 := by positivity
    have hmem : ∀ x : ℂ, ‖x‖ < ‖z‖ + ‖w‖ + 2 → x ∈ ball (0 : ℂ) (‖z‖ + ‖w‖ + 2) := fun x hx =>
      mem_ball_zero_iff.2 hx
    rcases thm8_2_limit isBounded_ball (isConnected_ball hr)
      (fun n => ac_t_isKQC_restrict (hF n).1 isOpen_ball (subset_univ _))
      hlim.tendstoLocallyUniformlyOn with ⟨c, hc⟩ | hGqc
    · have h0 := hc 0 (hmem 0 (by simpa using hr))
      have h1 := hc 1 (hmem 1 (by rw [norm_one]; linarith [norm_nonneg z, norm_nonneg w]))
      rw [hG0] at h0
      rw [hG1] at h1
      exact absurd (h0.trans h1.symm) zero_ne_one
    · exact hGqc.2.2.1.2.1 (hmem z (by linarith [norm_nonneg w])) (hmem w (by linarith [norm_nonneg z])) hzw
  have hGqc : IsKQC G univ K :=
    t203_lim_limit_isKQC isOpen_univ (fun n => (hF n).1) (tendstoLocallyUniformlyOn_univ.2 hlim) hinj
  -- properness of `G`, from the lower bound NB' for the `F n`
  have hprop : ∀ R : ℝ, 0 < R → ∀ z, ‖G z‖ < R → ‖z‖ ≤ lambdaInv (K * quadLambda R) := by
    intro R hR z hz
    obtain ⟨n, hn⟩ := ((hpt z).norm.eventually_lt_const hz).exists
    exact t203_lim_nb_lower (hF n) hR hn.le
  -- `G(ℂ)` is closed: near `w ∈ closure G(ℂ)` it is the compact image of a closed disc
  have hclosed : IsClosed (G '' univ) := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have hR : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hcpt : IsCompact (G '' closedBall 0 (lambdaInv (K * quadLambda (‖w‖ + 1)))) :=
      (isCompact_closedBall _ _).image (continuousOn_univ.1 hGqc.2.2.1.1)
    have hsub : ball (0 : ℂ) (‖w‖ + 1) ∩ G '' univ ⊆
        G '' closedBall 0 (lambdaInv (K * quadLambda (‖w‖ + 1))) := by
      rintro _ ⟨hb, z, -, rfl⟩
      exact ⟨z, mem_closedBall_zero_iff.2 (hprop _ hR z (mem_ball_zero_iff.1 hb)), rfl⟩
    have hw' := closure_mono hsub (isOpen_ball.inter_closure ⟨mem_ball_zero_iff.2 (by linarith), hw⟩)
    rw [hcpt.isClosed.closure_eq] at hw'
    exact image_mono (subset_univ _) hw'
  -- `G(ℂ)` is open, closed and nonempty, so it is `ℂ`
  exact ⟨hGqc, IsClopen.eq_univ ⟨hclosed, isOpen_image_of_isKQC hGqc⟩ (univ_nonempty.image G), hG0, hG1⟩

/-- **Three points** (a Möbius map with prescribed values): for distinct `v₁, v₂, v₃ ∈ ℂ̄` there is a Möbius map
sending them to `0, 1, ∞` (the cross ratio, with the three cases where one of the points is `∞`). -/
theorem t203_lim_three {v₁ v₂ v₃ : ExtPlane} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ mobiusExt a b c d v₁ = ((0 : ℂ) : ExtPlane) ∧
      mobiusExt a b c d v₂ = ((1 : ℂ) : ExtPlane) ∧ mobiusExt a b c d v₃ = extInf := by
  induction v₃ using OnePoint.rec with
  | infty =>
    induction v₁ using OnePoint.rec with
    | infty => exact absurd rfl h13
    | coe p =>
      induction v₂ using OnePoint.rec with
      | infty => exact absurd rfl h23
      | coe q =>
        have hqp : q - p ≠ 0 := sub_ne_zero.2 fun h => h12 (by rw [h])
        have hden : ∀ x : ℂ, (0 : ℂ) * x + (q - p) ≠ 0 := fun x => by simpa using hqp
        refine ⟨1, -p, 0, q - p, by simpa using hqp, ?_, ?_, mobiusExt_infty_of_eq rfl⟩
        · rw [mobiusExt_coe (hden p)]
          simp [mobiusFn]
        · rw [mobiusExt_coe (hden q)]
          congr 1
          simp only [mobiusFn]
          rw [div_eq_one_iff_eq (hden q)]
          ring
  | coe s =>
    induction v₁ using OnePoint.rec with
    | infty =>
      induction v₂ using OnePoint.rec with
      | infty => exact absurd rfl h12
      | coe q =>
        have hqs : q - s ≠ 0 := sub_ne_zero.2 fun h => h23 (by rw [h])
        refine ⟨0, q - s, 1, -s, ?_, ?_, ?_, mobiusExt_coe_of_eq_zero (by ring)⟩
        · intro h
          apply hqs
          linear_combination -h
        · rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
        · have hd : (1 : ℂ) * q + -s ≠ 0 := by rw [one_mul, ← sub_eq_add_neg]; exact hqs
          rw [mobiusExt_coe hd]
          congr 1
          simp only [mobiusFn]
          rw [div_eq_one_iff_eq hd]
          ring
    | coe p =>
      have hps : p - s ≠ 0 := sub_ne_zero.2 fun h => h13 (by rw [h])
      induction v₂ using OnePoint.rec with
      | infty =>
        refine ⟨1, -p, 1, -s, ?_, ?_, ?_, mobiusExt_coe_of_eq_zero (by ring)⟩
        · intro h
          apply hps
          linear_combination h
        · rw [mobiusExt_coe (show (1 : ℂ) * p + -s ≠ 0 by rw [one_mul, ← sub_eq_add_neg]; exact hps)]
          simp [mobiusFn]
        · rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
      | coe q =>
        have hqs : q - s ≠ 0 := sub_ne_zero.2 fun h => h23 (by rw [h])
        have hqp : q - p ≠ 0 := sub_ne_zero.2 fun h => h12 (by rw [h])
        refine ⟨q - s, -(q - s) * p, q - p, -(q - p) * s, ?_, ?_, ?_, mobiusExt_coe_of_eq_zero (by ring)⟩
        · have : (q - s) * (-(q - p) * s) - -(q - s) * p * (q - p) = (q - s) * (q - p) * (p - s) := by ring
          rw [this]
          exact mul_ne_zero (mul_ne_zero hqs hqp) hps
        · have hd : (q - p) * p + -(q - p) * s ≠ 0 := by
            rw [show (q - p) * p + -(q - p) * s = (q - p) * (p - s) by ring]
            exact mul_ne_zero hqp hps
          rw [mobiusExt_coe hd]
          congr 1
          simp only [mobiusFn]
          rw [show (q - s) * p + -(q - s) * p = 0 by ring, zero_div]
        · have hd : (q - p) * q + -(q - p) * s ≠ 0 := by
            rw [show (q - p) * q + -(q - p) * s = (q - p) * (q - s) by ring]
            exact mul_ne_zero hqp hqs
          rw [mobiusExt_coe hd]
          congr 1
          simp only [mobiusFn]
          rw [div_eq_one_iff_eq hd]
          ring

/-- **Chart transfer** through a holomorphic map: if `H = g ∘ T'` near `w` with `T'` holomorphic at `w`,
`T'(w) ≠ 0`, and `g` is `C¹` at `T' w` with `|∂̄g| < |∂g|`, `|∂̄g| ≤ k|∂g|` there, then `H` is `C¹` at `w` with the
same bounds (`|∂(g∘T')| = |∂g|·|T''|`, `|∂̄(g∘T')| = |∂̄g|·|T''|` by (6.4)). -/
theorem t203_lim_chart {g T' H : ℂ → ℂ} {w : ℂ} {k : ℝ} (hT : ContDiffAt ℂ 1 T' w) (hτ : deriv T' w ≠ 0)
    (hH : H =ᶠ[𝓝 w] g ∘ T')
    (hg : ContDiffAt ℝ 1 g (T' w) ∧ ‖dzbar g (T' w)‖ < ‖dz g (T' w)‖ ∧
      ‖dzbar g (T' w)‖ ≤ k * ‖dz g (T' w)‖) :
    ContDiffAt ℝ 1 H w ∧ ‖dzbar H w‖ < ‖dz H w‖ ∧ ‖dzbar H w‖ ≤ k * ‖dz H w‖ := by
  obtain ⟨hg1, hlt, hle⟩ := hg
  have hTd : DifferentiableAt ℂ T' w := hT.differentiableAt one_ne_zero
  have hgd : DifferentiableAt ℝ g (T' w) := hg1.differentiableAt one_ne_zero
  obtain ⟨e1, e2⟩ := eq6_4 hTd hgd
  have hdz : dz H w = dz (g ∘ T') w := by simp only [dz, hH.fderiv_eq]
  have hdzbar : dzbar H w = dzbar (g ∘ T') w := by simp only [dzbar, hH.fderiv_eq]
  have hn : 0 < ‖deriv T' w‖ := norm_pos_iff.2 hτ
  refine ⟨(hg1.comp w (hT.restrict_scalars ℝ)).congr_of_eventuallyEq hH, ?_, ?_⟩
  · rw [hdz, hdzbar, e1, e2, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_lt_mul_of_pos_right hlt hn
  · rw [hdz, hdzbar, e1, e2, norm_mul, norm_mul, Complex.norm_conj, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hle hn.le

/-- **Normalized plane maps**: for a continuous bijection `Φ₀` of `ℂ̄` which is `C¹` with `|∂̄| ≤ k|∂| < |∂|` in the
chart of the Möbius map `A = (a, b, c, d)` at every finite point with `A ∘ Φ₀` finite, and with
`A(Φ₀(z₃ + r)) = 0`, `A(Φ₀(z₃ + r/2)) = 1`, `A(Φ₀(z₃)) = ∞`, the plane map of `A ∘ Φ₀ ∘ T`,
`T(w) = z₃ + r/(w + 1)` (`T : 0, 1, ∞ ↦ z₃ + r, z₃ + r/2, z₃`), is a normalized `(1+k)/(1-k)`-q.c. map of the plane
(`t203_plane_qc` with the exceptional point `-1 = T⁻¹(∞)`, and the chart transfer through the conformal `T`). -/
theorem t203_lim_normalized {Φ₀ : ExtPlane → ExtPlane} {a b c d z₃ r : ℂ} {k K' : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hK' : (1 + k) / (1 - k) ≤ K') (hdet : a * d - b * c ≠ 0) (hr : r ≠ 0) (hbij : Function.Bijective Φ₀)
    (hc : Continuous Φ₀) (h0 : mobiusExt a b c d (Φ₀ ((z₃ + r : ℂ) : ExtPlane)) = ((0 : ℂ) : ExtPlane))
    (h1 : mobiusExt a b c d (Φ₀ ((z₃ + r / 2 : ℂ) : ExtPlane)) = ((1 : ℂ) : ExtPlane))
    (hinf : mobiusExt a b c d (Φ₀ (z₃ : ExtPlane)) = extInf)
    (hchart : ∀ z : ℂ, mobiusExt a b c d (Φ₀ z) ≠ extInf →
      ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ w))) z ∧
      ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ w))) z‖ <
        ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ w))) z‖ ∧
      ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ w))) z‖ ≤
        k * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ w))) z‖) :
    IsKQCNormalizedPlane (fun w : ℂ => extToC (mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 w)))) K' := by
  have hTdet : z₃ * 1 - (z₃ + r) * 1 ≠ 0 := by
    intro h
    apply hr
    linear_combination -h
  have hAinj : Function.Injective (mobiusExt a b c d) := (mobiusHomeomorph a b c d hdet).injective
  have hTinj : Function.Injective (mobiusExt z₃ (z₃ + r) 1 1) := (mobiusHomeomorph _ _ _ _ hTdet).injective
  have hbijΦ : Function.Bijective fun p => mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 p)) :=
    ((mobiusHomeomorph a b c d hdet).bijective.comp hbij).comp (mobiusHomeomorph _ _ _ _ hTdet).bijective
  have hcΦ : Continuous fun p => mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 p)) :=
    (continuous_mobiusExt hdet).comp (hc.comp (continuous_mobiusExt hTdet))
  have hTinf : mobiusExt z₃ (z₃ + r) 1 1 extInf = (z₃ : ExtPlane) := by
    rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
  have hΦinf : mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 extInf)) = extInf := by
    rw [hTinf, hinf]
  obtain ⟨hqc, hsurj⟩ := t203_plane_qc hbijΦ hcΦ hΦinf hk0 hk1 hK' (z₀ := -1) fun w hw => by
    have hden : (1 : ℂ) * w + 1 ≠ 0 := by
      intro h
      apply hw
      linear_combination h
    have hne : mobiusExt a b c d (Φ₀ (mobiusFn z₃ (z₃ + r) 1 1 w : ℂ)) ≠ extInf := by
      intro h
      rw [← hinf] at h
      have h2 : mobiusExt z₃ (z₃ + r) 1 1 (w : ExtPlane) = mobiusExt z₃ (z₃ + r) 1 1 extInf := by
        rw [mobiusExt_coe hden, hbij.1 (hAinj h), hTinf]
      exact OnePoint.coe_ne_infty w (hTinj h2)
    have hT : ContDiffAt ℂ 1 (mobiusFn z₃ (z₃ + r) 1 1) w :=
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
        ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) hden
    have hτ : deriv (mobiusFn z₃ (z₃ + r) 1 1) w ≠ 0 := by
      rw [(hasDerivAt_mobiusFn hden).deriv]
      exact div_ne_zero hTdet (pow_ne_zero _ hden)
    have hev : ∀ᶠ w' in 𝓝 w, (1 : ℂ) * w' + 1 ≠ 0 :=
      (show Continuous fun w' : ℂ => (1 : ℂ) * w' + 1 by fun_prop).continuousAt.eventually_ne hden
    refine t203_lim_chart hT hτ ?_ (hchart _ hne)
    filter_upwards [hev] with w' hw'
    simp only [Function.comp_apply, mobiusExt_coe hw']
  refine ⟨hqc, hsurj, ?_, ?_⟩
  · show extToC (mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 ((0 : ℂ) : ExtPlane)))) = 0
    rw [mobiusExt_coe (by norm_num), show mobiusFn z₃ (z₃ + r) 1 1 0 = z₃ + r by simp [mobiusFn], h0]
    rfl
  · show extToC (mobiusExt a b c d (Φ₀ (mobiusExt z₃ (z₃ + r) 1 1 ((1 : ℂ) : ExtPlane)))) = 1
    have h2 : (1 : ℂ) * 1 + 1 ≠ 0 := by norm_num
    rw [mobiusExt_coe h2, show mobiusFn z₃ (z₃ + r) 1 1 1 = z₃ + r / 2 by simp only [mobiusFn]; field_simp; ring,
      h1]
    rfl

/-- **C-lim** (the limit, Q10): normalize the family at three points `z₁, z₂, z₃ ∈ Dₙ` by fixed Möbius maps
(`A` sending `f(zᵢ)` to `0, 1, ∞`, `T` sending `0, 1, ∞` to `zᵢ`), so that the plane maps of `A ∘ Fₙ ∘ T` are normalized
`K'`-q.c. (`t203_plane_qc`, with `T` conformal off `T⁻¹(∞)`); `ut2_nf_extract` / `ut2_nf_limit` give a limit `h`, and
`G = A⁻¹ ∘ ĥ ∘ T⁻¹` agrees with `meroToExt f` on `D` (pointwise limits, `Fₙ = f` on `Dₙ` eventually). -/
theorem t203_limit {D : Set ℂ} {f : ℂ → ℂ} {Dn : ℕ → Set ℂ} {F : ℕ → ExtPlane → ExtPlane} {k K' : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hK' : (1 + k) / (1 - k) ≤ K') (hDne : D.Nonempty) (hDo : IsOpen D)
    (hmono : Monotone Dn) (hopen : ∀ n, IsOpen (Dn n)) (hU : ⋃ n, Dn n = D)
    (hF : ∀ n, Function.Bijective (F n) ∧ Continuous (F n) ∧ (∀ z ∈ Dn n, F n z = meroToExt f z) ∧
      ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ z : ℂ, mobiusExt a b c d (F n z) ≠ extInf →
        ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ <
          ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ∧
        ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ≤
          k * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖) :
    ∃ (G A T : ExtPlane → ExtPlane) (h : ℂ → ℂ), IsMobius A ∧ IsMobius T ∧ IsKQC h univ K' ∧ h '' univ = univ ∧
      (∀ p, A (G (T p)) = OnePoint.map h p) ∧ ∀ z ∈ D, G z = meroToExt f z := by
  have _hopen := hopen
  obtain ⟨z₃, hz₃⟩ := hDne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo z₃ hz₃
  have hε2 : 0 < ε / 2 := half_pos hε
  set r : ℂ := ((ε / 2 : ℝ) : ℂ) with hrdef
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.2 hε2.ne'
  have hnr : ‖r‖ = ε / 2 := by rw [hrdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε2]
  have hz₁D : z₃ + r ∈ D := hball (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnr]; linarith)
  have hz₂D : z₃ + r / 2 ∈ D := hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_div, hnr, Complex.norm_two]
    linarith)
  have hmemU : ∀ z ∈ D, ∃ n, z ∈ Dn n := fun z hz => mem_iUnion.1 (by rw [hU]; exact hz)
  -- the three points lie in one `Dₙ`, and `Fₙ` is `f` there from `N` on
  obtain ⟨N, hN1, hN2, hN3⟩ : ∃ N, z₃ + r ∈ Dn N ∧ z₃ + r / 2 ∈ Dn N ∧ z₃ ∈ Dn N := by
    obtain ⟨N₁, hN₁⟩ := hmemU _ hz₁D
    obtain ⟨N₂, hN₂⟩ := hmemU _ hz₂D
    obtain ⟨N₃, hN₃⟩ := hmemU _ hz₃
    exact ⟨N₁ + N₂ + N₃, hmono (by omega) hN₁, hmono (by omega) hN₂, hmono (by omega) hN₃⟩
  have hF1 : ∀ n, N ≤ n → F n ((z₃ + r : ℂ) : ExtPlane) = meroToExt f (z₃ + r) := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN1)
  have hF2 : ∀ n, N ≤ n → F n ((z₃ + r / 2 : ℂ) : ExtPlane) = meroToExt f (z₃ + r / 2) := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN2)
  have hF3 : ∀ n, N ≤ n → F n (z₃ : ExtPlane) = meroToExt f z₃ := fun n hn =>
    (hF n).2.2.1 _ (hmono hn hN3)
  -- the three values are distinct (`F N` is injective)
  have hne12 : meroToExt f (z₃ + r) ≠ meroToExt f (z₃ + r / 2) := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF1 N le_rfl).trans (h.trans (hF2 N le_rfl).symm)))
    apply hr
    linear_combination 2 * h'
  have hne13 : meroToExt f (z₃ + r) ≠ meroToExt f z₃ := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF1 N le_rfl).trans (h.trans (hF3 N le_rfl).symm)))
    apply hr
    linear_combination h'
  have hne23 : meroToExt f (z₃ + r / 2) ≠ meroToExt f z₃ := by
    intro h
    have h' := OnePoint.coe_injective ((hF N).1.1 ((hF2 N le_rfl).trans (h.trans (hF3 N le_rfl).symm)))
    apply hr
    linear_combination 2 * h'
  obtain ⟨a, b, c, d, hdet, hA0, hA1, hAinf⟩ := t203_lim_three hne12 hne13 hne23
  -- the normalized plane maps of `A ∘ F (m + N) ∘ T`
  set hn : ℕ → ℂ → ℂ := fun m w => extToC (mobiusExt a b c d (F (m + N) (mobiusExt z₃ (z₃ + r) 1 1 w)))
    with hhn
  have hnorm : ∀ m, IsKQCNormalizedPlane (hn m) K' := fun m => by
    have hmN : N ≤ m + N := Nat.le_add_left N m
    exact t203_lim_normalized hk0 hk1 hK' hdet hr (hF (m + N)).1 (hF (m + N)).2.1
      (by rw [hF1 _ hmN, hA0]) (by rw [hF2 _ hmN, hA1]) (by rw [hF3 _ hmN, hAinf])
      fun z hz => (hF (m + N)).2.2.2 a b c d hdet z hz
  -- the limit
  obtain ⟨φ, hφ, h, hlim⟩ := t203_lim_nf_extract hnorm
  have hh := t203_lim_nf_limit (fun m => hnorm (φ m)) hlim
  have hpt : ∀ w, Tendsto (fun m => hn (φ m) w) atTop (𝓝 (h w)) := fun w =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ w)
  have hTdet : z₃ * 1 - (z₃ + r) * 1 ≠ 0 := by
    intro h
    apply hr
    linear_combination -h
  set eA := mobiusHomeomorph a b c d hdet with heA
  set eT := mobiusHomeomorph z₃ (z₃ + r) 1 1 hTdet with heT
  have hTinf : eT extInf = (z₃ : ExtPlane) := by
    show mobiusExt z₃ (z₃ + r) 1 1 extInf = _
    rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
  refine ⟨fun p => eA.symm (OnePoint.map h (eT.symm p)), mobiusExt a b c d, mobiusExt z₃ (z₃ + r) 1 1, h,
    ⟨a, b, c, d, hdet, rfl⟩, ⟨z₃, z₃ + r, 1, 1, hTdet, rfl⟩, hh.1, hh.2.1, fun p => ?_, fun z hz => ?_⟩
  · show eA (eA.symm (OnePoint.map h (eT.symm (eT p)))) = _
    rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  · show eA.symm (OnePoint.map h (eT.symm z)) = meroToExt f z
    rw [Homeomorph.symm_apply_eq]
    have key : ∀ q : ExtPlane, eT.symm (z : ExtPlane) = q → OnePoint.map h q = eA (meroToExt f z) := by
      intro q hq
      induction q using OnePoint.rec with
      | infty =>
        -- `z = T ∞ = z₃`
        have hz3 : z = z₃ := by
          have h1 := (Homeomorph.symm_apply_eq eT).1 hq
          rw [hTinf] at h1
          exact OnePoint.coe_injective h1
        rw [OnePoint.map_infty, hz3]
        exact hAinf.symm
      | coe w =>
        rw [OnePoint.map_some]
        have hzT : (z : ExtPlane) = eT w := (Homeomorph.symm_apply_eq eT).1 hq
        obtain ⟨n₀, hn₀⟩ := hmemU z hz
        have hFz : ∀ m, n₀ ≤ m → F (m + N) (z : ExtPlane) = meroToExt f z := fun m hm =>
          (hF (m + N)).2.2.1 z (hmono (by omega) hn₀)
        -- `A(f z)` is finite: otherwise `F (n₀ + N) z = F (n₀ + N) z₃`, so `z = z₃ = T ∞`
        have hfin : eA (meroToExt f z) ≠ extInf := by
          intro hinf'
          have h1 : eA (F (n₀ + N) (z : ExtPlane)) = eA (F (n₀ + N) (z₃ : ExtPlane)) := by
            rw [hFz n₀ le_rfl, hF3 _ (Nat.le_add_left N n₀), hinf']
            exact hAinf.symm
          have h2 := OnePoint.coe_injective ((hF (n₀ + N)).1.1 (eA.injective h1))
          rw [h2, ← hTinf, Homeomorph.symm_apply_apply] at hq
          exact OnePoint.infty_ne_coe w hq
        obtain ⟨c', hc'⟩ := OnePoint.ne_infty_iff_exists.1 hfin
        -- the plane maps are eventually constant `= c'` at `w`
        have hval : ∀ m, n₀ ≤ m → hn m w = c' := fun m hm => by
          show extToC (mobiusExt a b c d (F (m + N) (eT w))) = c'
          rw [← hzT, hFz m hm]
          show extToC (eA (meroToExt f z)) = c'
          rw [← hc']
          rfl
        have hlimw : h w = c' := tendsto_nhds_unique (hpt w) (tendsto_const_nhds.congr'
          (eventually_atTop.2 ⟨n₀, fun m hm => (hval (φ m) (hm.trans (hφ.id_le m))).symm⟩))
        rw [hlimw]
        exact hc'
    exact key _ rfl

/-- The identity of `ℂ̄` as the fractional linear transformation `mobiusExt 1 0 0 1`. -/
theorem t203_pack_mobius_id (w : ExtPlane) : mobiusExt 1 0 0 1 w = w := by
  induction w using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    rw [mobiusExt_coe (show (0 : ℂ) * z + 1 ≠ 0 by simp)]
    simp [mobiusFn]

/-- A fractional linear transformation maps the complement of its pole conformally onto the complement of the pole of
its inverse `mobiusFn d (-b) (-c) a`. -/
theorem t203_pack_mobius_conformal {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    IsConformalOnto (mobiusFn a b c d) {z | c * z + d ≠ 0} {w | -c * w + a ≠ 0} := by
  have h' : d * a - -b * -c ≠ 0 := by
    rwa [show d * a - -b * -c = a * d - b * c by ring]
  refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, ?_⟩
  · have hnum : DifferentiableAt ℂ (fun z : ℂ => a * z + b) z := by fun_prop
    have hdd : DifferentiableAt ℂ (fun z : ℂ => c * z + d) z := by fun_prop
    exact (hnum.div hdd hz).differentiableWithinAt
  · rw [← mobiusFn_inv_apply h hz₁, ← mobiusFn_inv_apply h hz₂, heq]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mobiusFn_inv_den_ne_zero h hz
    · intro hw
      have hw' : -c * w + a ≠ 0 := hw
      refine ⟨mobiusFn d (-b) (-c) a w, ?_, ?_⟩
      · show c * mobiusFn d (-b) (-c) a w + d ≠ 0
        simpa only [neg_neg] using mobiusFn_inv_den_ne_zero h' hw'
      · simpa only [neg_neg] using mobiusFn_inv_apply h' hw'

/-- A `K`-q.c. map of `ℂ` onto `ℂ` is a homeomorphism of `ℂ`. -/
theorem t203_pack_homeo {h : ℂ → ℂ} {K : ℝ} (hh : IsKQC h univ K) (hhs : h '' univ = univ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = h := by
  obtain ⟨-, -, ⟨hc, hi, -, hinv⟩, -⟩ := hh
  rw [hhs] at hinv
  have hmem : ∀ w : ℂ, ∃ z ∈ (univ : Set ℂ), h z = w := fun w => by
    have hw : w ∈ h '' univ := by
      rw [hhs]
      exact mem_univ w
    exact hw
  refine ⟨
    { toFun := h
      invFun := Function.invFunOn h univ
      left_inv := fun z => hi.leftInvOn_invFunOn (mem_univ z)
      right_inv := fun w => Function.invFunOn_eq (hmem w)
      continuous_toFun := continuousOn_univ.1 hc
      continuous_invFun := continuousOn_univ.1 hinv }, rfl⟩

/-- A fractional linear transformation of `ℂ̄` is injective. -/
theorem t203_pack_mobius_injective {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    Function.Injective (mobiusExt a b c d) := fun x y hxy => by
  rw [← mobiusExt_inv_apply h x, ← mobiusExt_inv_apply h y, hxy]

/-- **Core of C-pack**: if `Φ = N ∘ ĥ ∘ S` with `N, S` fractional linear transformations and `h` a `K'`-q.c. map of `ℂ`
onto `ℂ`, and `Φ` fixes `∞`, then `Φ` is the extension of a `K'`-q.c. map `g` of `ℂ` onto `ℂ`.  Off the pole of `S`,
`g = N ∘ h ∘ S` with `S` conformal there and `N` conformal near the finite values of `h ∘ S` (`Φ` is injective and
fixes `∞`), so `thm7_1_comp` gives `1 · K' · 1`; the pole of `S` is removable (`b4_isKQC_univ_of_punctured`). -/
theorem t203_pack_core {h : ℂ → ℂ} {K' : ℝ} (hh : IsKQC h univ K') (hhs : h '' univ = univ)
    {α β κ δ a b c d : ℂ} (hN : α * δ - β * κ ≠ 0) (hS : a * d - b * c ≠ 0) {Φ : ExtPlane → ExtPlane}
    (hΦ : ∀ p, Φ p = mobiusExt α β κ δ (OnePoint.map h (mobiusExt a b c d p))) (hinf : Φ extInf = extInf) :
    ∃ g : ℂ → ℂ, IsKQC g univ K' ∧ g '' univ = univ ∧ ∀ p, Φ p = OnePoint.map g p := by
  obtain ⟨e, he⟩ := t203_pack_homeo hh hhs
  have hHc : Continuous (OnePoint.map h) := by
    rw [← he]
    exact e.onePointCongr.continuous
  have hHi : Function.Injective (OnePoint.map h) := by
    rw [← he]
    exact e.onePointCongr.injective
  have hΦc : Continuous Φ := by
    have hΦe : Φ = mobiusExt α β κ δ ∘ OnePoint.map h ∘ mobiusExt a b c d := funext hΦ
    rw [hΦe]
    exact (continuous_mobiusExt hN).comp (hHc.comp (continuous_mobiusExt hS))
  have hΦi : Function.Injective Φ := fun x y hxy => by
    rw [hΦ, hΦ] at hxy
    exact t203_pack_mobius_injective hS (hHi (t203_pack_mobius_injective hN hxy))
  obtain ⟨hcoe, hhomeo⟩ := wd_b_plane_homeo hΦc hΦi hinf
  refine ⟨fun z : ℂ => extToC (Φ z), ?_, hhomeo.2.2.1, fun p => ?_⟩
  · have hΩS : IsOpen {z : ℂ | c * z + d ≠ 0} :=
      isOpen_ne_fun (f := fun z : ℂ => c * z + d) (g := fun _ => (0 : ℂ)) (by fun_prop) continuous_const
    have hΩS' : IsOpen {w : ℂ | -c * w + a ≠ 0} :=
      isOpen_ne_fun (f := fun w : ℂ => -c * w + a) (g := fun _ => (0 : ℂ)) (by fun_prop) continuous_const
    have hΩN : IsOpen {w : ℂ | κ * w + δ ≠ 0} :=
      isOpen_ne_fun (f := fun w : ℂ => κ * w + δ) (g := fun _ => (0 : ℂ)) (by fun_prop) continuous_const
    have hSc := t203_pack_mobius_conformal hS
    have q1 : IsKQC (mobiusFn a b c d) {z : ℂ | c * z + d ≠ 0} 1 := isKQC_one_of_conformal hΩS hSc
    have q2 : IsKQC h {w : ℂ | -c * w + a ≠ 0} K' := ac_t_isKQC_restrict hh hΩS' (subset_univ _)
    have q3 : IsKQC (mobiusFn α β κ δ) {w : ℂ | κ * w + δ ≠ 0} 1 :=
      isKQC_one_of_conformal hΩN (t203_pack_mobius_conformal hN)
    have hkey : ∀ z : ℂ, c * z + d ≠ 0 → κ * h (mobiusFn a b c d z) + δ ≠ 0 := by
      intro z hz h0
      have h1 : Φ z = extInf := by
        rw [hΦ, mobiusExt_coe hz, OnePoint.map_some, mobiusExt_coe_of_eq_zero h0]
      exact OnePoint.coe_ne_infty z (hΦi (h1.trans hinf.symm))
    have h12 := thm7_1_comp q1 q2 hSc.2.2.subset
    have h123 := thm7_1_comp h12 q3 (by
      rintro _ ⟨z, hz, rfl⟩
      exact hkey z hz)
    rw [one_mul, mul_one] at h123
    have hgΩ : IsKQC (fun z : ℂ => extToC (Φ z)) {z : ℂ | c * z + d ≠ 0} K' := by
      refine ad_isKQC_congr h123 fun z hz => ?_
      apply OnePoint.coe_injective
      show ((extToC (Φ z) : ℂ) : ExtPlane) = ((mobiusFn α β κ δ (h (mobiusFn a b c d z)) : ℂ) : ExtPlane)
      rw [hcoe z, hΦ, mobiusExt_coe hz, OnePoint.map_some, mobiusExt_coe (hkey z hz)]
    have hpole : ∃ z₃ : ℂ, ({z₃}ᶜ : Set ℂ) ⊆ {z : ℂ | c * z + d ≠ 0} := by
      by_cases hc0 : c = 0
      · have hd : d ≠ 0 := by
          rintro rfl
          apply hS
          simp [hc0]
        refine ⟨0, fun z _ => ?_⟩
        show c * z + d ≠ 0
        simp [hc0, hd]
      · refine ⟨-d / c, fun z hz => ?_⟩
        show c * z + d ≠ 0
        intro h0
        apply hz
        rw [mem_singleton_iff, eq_div_iff hc0]
        linear_combination h0
    obtain ⟨z₃, hz₃⟩ := hpole
    exact b4_isKQC_univ_of_punctured hhomeo (ac_t_isKQC_restrict hgΩ isOpen_compl_singleton hz₃)
  · induction p using OnePoint.rec with
    | infty =>
      rw [hinf]
      rfl
    | coe z => exact (hcoe z).symm

/-- **C-pack** (the `HasQCExtensionExt` form): if `A ∘ G ∘ T = ĥ` for Möbius `A, T` and a `K'`-q.c. homeomorphism `h`
of `ℂ`, then with `M` a Möbius map sending `G(∞)` to `∞`, `M ∘ G` is (the extension of) a `K'`-q.c. map of `ℂ`: locally
`(M ∘ A⁻¹) ∘ h ∘ T⁻¹` with conformal outer and inner maps (`thm7_1_comp`, local-to-global `s23_lg`), and the one point
`T(∞)` is removable (`b4_isKQC_univ_of_punctured`). -/
theorem t203_package {D : Set ℂ} {f : ℂ → ℂ} {K' : ℝ} {G A T : ExtPlane → ExtPlane} {h : ℂ → ℂ}
    (hA : IsMobius A) (hT : IsMobius T) (hh : IsKQC h univ K') (hhs : h '' univ = univ)
    (hG : ∀ p, A (G (T p)) = OnePoint.map h p) (hD : ∀ z ∈ D, G z = meroToExt f z) : HasQCExtensionExt f D K' := by
  obtain ⟨a₁, b₁, c₁, d₁, hdet₁, rfl⟩ := hA
  obtain ⟨a₂, b₂, c₂, d₂, hdet₂, rfl⟩ := hT
  have hdet₁' : d₁ * a₁ - -b₁ * -c₁ ≠ 0 := by
    rwa [show d₁ * a₁ - -b₁ * -c₁ = a₁ * d₁ - b₁ * c₁ by ring]
  have hdet₂' : d₂ * a₂ - -b₂ * -c₂ ≠ 0 := by
    rwa [show d₂ * a₂ - -b₂ * -c₂ = a₂ * d₂ - b₂ * c₂ by ring]
  have hGe : ∀ p, G p = mobiusExt d₁ (-b₁) (-c₁) a₁ (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := by
    intro p
    have h1 := hG (mobiusExt d₂ (-b₂) (-c₂) a₂ p)
    have h2 : mobiusExt a₂ b₂ c₂ d₂ (mobiusExt d₂ (-b₂) (-c₂) a₂ p) = p := by
      simpa only [neg_neg] using mobiusExt_inv_apply hdet₂' p
    rw [h2] at h1
    rw [← h1, mobiusExt_inv_apply hdet₁]
  refine ⟨G, hD, ?_⟩
  by_cases hq : G extInf = extInf
  · have hΦ : ∀ p, mobiusExt 1 0 0 1 (G p) =
        mobiusExt d₁ (-b₁) (-c₁) a₁ (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := fun p => by
      rw [t203_pack_mobius_id, hGe]
    have hinf : mobiusExt 1 0 0 1 (G extInf) = extInf := by
      rw [t203_pack_mobius_id, hq]
    obtain ⟨g, hg, hgs, hgp⟩ := t203_pack_core hh hhs hdet₁' hdet₂' hΦ hinf
    exact ⟨mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, g, hg, hgs, hgp⟩
  · obtain ⟨q, hq'⟩ := OnePoint.ne_infty_iff_exists.1 hq
    have hdet₃ : -c₁ * (-b₁ - q * a₁) - a₁ * (d₁ - q * -c₁) ≠ 0 := by
      intro h0
      apply hdet₁
      linear_combination -h0
    have hΦ : ∀ p, mobiusExt 0 1 1 (-q) (G p) = mobiusExt (-c₁) a₁ (d₁ - q * -c₁) (-b₁ - q * a₁)
        (OnePoint.map h (mobiusExt d₂ (-b₂) (-c₂) a₂ p)) := fun p => by
      rw [hGe, s20l_tp_mobius_comp q hdet₁']
    have hinf : mobiusExt 0 1 1 (-q) (G extInf) = extInf := by
      rw [← hq']
      exact mobiusExt_coe_of_eq_zero (by ring)
    obtain ⟨g, hg, hgs, hgp⟩ := t203_pack_core hh hhs hdet₃ hdet₂' hΦ hinf
    exact ⟨mobiusExt 0 1 1 (-q), ⟨0, 1, 1, -q, by norm_num, rfl⟩, g, hg, hgs, hgp⟩

/-- Arithmetic for Theorem 20.3: with `0 ≤ c₀ ≤ c`, `0 ≤ s` and `c s < 1`, the dilatation bound `k = c₀ s/2`
satisfies `0 ≤ k < 1` and `(1 + k)/(1 - k) ≤ (1 + c s)/(1 - c s)`. -/
theorem t203_t_arith {c₀ c s : ℝ} (hc₀ : 0 ≤ c₀) (hc : c₀ ≤ c) (hs : 0 ≤ s) (hcs : c * s < 1) :
    0 ≤ c₀ * s / 2 ∧ c₀ * s / 2 < 1 ∧ (1 + c₀ * s / 2) / (1 - c₀ * s / 2) ≤ (1 + c * s) / (1 - c * s) := by
  have h1 : c₀ * s ≤ c * s := mul_le_mul_of_nonneg_right hc hs
  have h2 : 0 ≤ c₀ * s := mul_nonneg hc₀ hs
  refine ⟨by linarith, by linarith, ?_⟩
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- For `x < ofReal a` in `ℝ≥0∞`: `x ≤ ofReal x.toReal`, `0 ≤ x.toReal` and `x.toReal < a`. -/
theorem t203_t_toReal {x : ℝ≥0∞} {a : ℝ} (hx : x < ENNReal.ofReal a) :
    x ≤ ENNReal.ofReal x.toReal ∧ 0 ≤ x.toReal ∧ x.toReal < a :=
  ⟨(ENNReal.ofReal_toReal (ne_top_of_lt hx)).ge, ENNReal.toReal_nonneg, ENNReal.toReal_lt_of_lt_ofReal hx⟩

/-- **Theorem 20.3** (Ahlfors).  For every `K ≥ 1` there is `c(K) > 0` such that
(i) every `K`-quasidisc is a `1/c(K)`-Schwarz domain, and
(ii) a locally univalent meromorphic `f` in a `K`-quasidisc `D` with `‖S_f‖_D < 1/c(K)` extends
quasiconformally to `ℂ̄`, with complex dilatation `|μ| ≤ c(K) ‖S_f‖_D`. -/
theorem thm20_3_ahlfors {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : Set ℂ, IsKQuasidisc D K →
      IsSchwarzDomain D (1 / c) ∧
      ∀ f : ℂ → ℂ, IsLocUnivMero f D → schwarzianNorm f D < ENNReal.ofReal (1 / c) →
        HasQCExtensionExt f D ((1 + c * (schwarzianNorm f D).toReal) / (1 - c * (schwarzianNorm f D).toReal)) := by
  obtain ⟨c₀, hc₀, hfam⟩ := t203_family hK
  have hcpos : 0 < max c₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc₀c : c₀ ≤ max c₀ 1 := le_max_left _ _
  refine ⟨max c₀ 1, hcpos, fun D hD => ?_⟩
  have hsc := t203_hsc_of_isKQuasidisc hD
  have key : ∀ f : ℂ → ℂ, schwarzianNorm f D < ENNReal.ofReal (1 / max c₀ 1) →
      schwarzianNorm f D ≤ ENNReal.ofReal (schwarzianNorm f D).toReal ∧ 0 ≤ (schwarzianNorm f D).toReal ∧
        max c₀ 1 * (schwarzianNorm f D).toReal < 1 := by
    intro f hS
    obtain ⟨h1, h2, h3⟩ := t203_t_toReal hS
    refine ⟨h1, h2, ?_⟩
    rw [lt_div_iff₀ hcpos] at h3
    linarith
  refine ⟨⟨hsc, one_div_pos.2 hcpos, fun f hf hS => ?_⟩, fun f hf hS => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := key f hS
    have hc₀s : c₀ * (schwarzianNorm f D).toReal < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc₀c h2) h3
    obtain ⟨Dn, F, hmono, -, hU, hF⟩ := hfam D hD f hf _ h2 hc₀s h1
    exact t203_univalent hf hmono hU (fun n => (hF n).1.1) (fun n => (hF n).2.2.1)
  · obtain ⟨h1, h2, h3⟩ := key f hS
    obtain ⟨hk0, hk1, hK'⟩ := t203_t_arith hc₀ hc₀c h2 h3
    have hc₀s : c₀ * (schwarzianNorm f D).toReal < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc₀c h2) h3
    obtain ⟨Dn, F, hmono, hopen, hU, hF⟩ := hfam D hD f hf _ h2 hc₀s h1
    obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD⟩ :=
      t203_limit hk0 hk1 hK' hsc.2.1.nonempty hsc.1 hmono hopen hU hF
    exact t203_package hA hT hh hhs hG hGD

/-- No domain is an `a`-Schwarz domain for `a > 3`: scale the Schwarzian of a univalent `f₀` with `‖S_{f₀}‖_D ≥ 3/2`
(`lehto_ge_pointwise`) so that `3 < ‖S_g‖_D < a` (`thm19_1_exists`); `g` would be univalent, contradicting
`‖S_g‖_D ≤ 3` for univalent `g` (`thm19_3_cor`). -/
theorem t2020_not_isSchwarz_of_three_lt {D : Set ℂ} {a : ℝ} (ha : 3 < a) : ¬ IsSchwarzDomain D a := by
  rintro ⟨hD, -, hall⟩
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hD
  obtain ⟨z₀, hz₀⟩ := hD.2.1.nonempty
  obtain ⟨f₀, hf₀, hval⟩ := lehto_ge_pointwise hD.1 hφ hz₀
  have hσ2 : ∀ f, IsUnivMero f D → schwarzianNorm f D ≤ 3 := fun f hf =>
    (le_iSup₂_of_le (f := fun f (_ : IsUnivMero f D) => schwarzianNorm f D) f hf le_rfl).trans
      (thm19_3_cor hD)
  set s := schwarzianNorm f₀ D with hs
  have hsle : s ≤ 3 := hσ2 f₀ hf₀
  have hsge : ENNReal.ofReal (3 / 2) ≤ s := by
    refine le_trans ?_ (le_iSup₂ (f := fun z (_ : z ∈ D) =>
      ENNReal.ofReal (‖schwarzian f₀ z‖ / poincareDensity D z ^ 2)) z₀ hz₀)
    apply ENNReal.ofReal_le_ofReal
    rw [hval]
    have : 0 ≤ ‖schwarzian φ z₀‖ / poincareDensity D z₀ ^ 2 := by positivity
    linarith
  have hsfin : s ≠ ⊤ := ne_top_of_le_ne_top (by simp) hsle
  have hσpos : 0 < s.toReal := by
    have h1 : (3 / 2 : ℝ) ≤ s.toReal := by
      rw [← ENNReal.ofReal_le_iff_le_toReal hsfin]
      exact hsge
    linarith
  set t : ℝ := (3 + a) / (2 * s.toReal) with ht
  have htpos : 0 < t := by positivity
  obtain ⟨g, hg, hgS⟩ := thm19_1_exists hD.1 hD.2.1 hD.2.2.1
    ((schwarzian_holomorphic hD.1 hf₀.1).const_mul (t : ℂ))
  have hpt : ∀ z ∈ D, ENNReal.ofReal (‖schwarzian g z‖ / poincareDensity D z ^ 2) =
      ENNReal.ofReal t * ENNReal.ofReal (‖schwarzian f₀ z‖ / poincareDensity D z ^ 2) := by
    intro z hz
    rw [hgS z hz, ← ENNReal.ofReal_mul htpos.le, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg htpos.le, mul_div_assoc]
  have hnorm : schwarzianNorm g D = ENNReal.ofReal ((3 + a) / 2) := by
    have e1 : schwarzianNorm g D = ENNReal.ofReal t * s := by
      rw [hs]
      unfold schwarzianNorm
      rw [ENNReal.mul_iSup]
      refine iSup_congr fun z => ?_
      rw [ENNReal.mul_iSup]
      exact iSup_congr fun hz => hpt z hz
    rw [e1, ← ENNReal.ofReal_toReal hsfin, ← ENNReal.ofReal_mul htpos.le, ht]
    congr 1
    field_simp
  have hlt : schwarzianNorm g D < ENNReal.ofReal a := by
    rw [hnorm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hle := hσ2 g (hall g hg hlt)
  rw [hnorm, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hle
  linarith

/-- The set `{a | D is an a-Schwarz domain}` defining `innerUnivalenceRadius D` is bounded above (by `3`), so its
`sSup` is a genuine supremum. -/
theorem t2020_bddAbove_isSchwarz (D : Set ℂ) : BddAbove {a : ℝ | IsSchwarzDomain D a} :=
  ⟨3, fun _ ha => not_lt.1 fun h => t2020_not_isSchwarz_of_three_lt h ha⟩

/-- (20.20): the inner radius of univalence of a `K`-quasidisc is at least `1/c(K)`. -/
theorem eq20_20 {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : Set ℂ, IsKQuasidisc D K → 1 / c ≤ innerUnivalenceRadius D := by
  obtain ⟨c, hc, h⟩ := thm20_3_ahlfors hK
  exact ⟨c, hc, fun D hD => le_csSup (t2020_bddAbove_isSchwarz D) (h D hD).1⟩

/-- **Definition** (§20.5, `k` 局部连通).  `D` is `k`-locally connected: for every disc
`Δ_r(z)`, (i) any two points of `D ∩ Δ̄_r(z)` can be joined by an arc in `D ∩ Δ̄_{kr}(z)`, and
(ii) any two points of `D ∖ Δ_r(z)` can be joined by an arc in `D ∖ Δ_{r/k}(z)`. -/
def IsKLocallyConnected (D : Set ℂ) (k : ℝ) : Prop :=
  1 ≤ k ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
    (∀ p ∈ D ∩ closedBall z r, ∀ q ∈ D ∩ closedBall z r, JoinedIn (D ∩ closedBall z (k * r)) p q) ∧
      ∀ p ∈ D \ ball z r, ∀ q ∈ D \ ball z r, JoinedIn (D \ ball z (r / k)) p q

/-- §20.5: the strip `{0 < Im z < 1}` is not `k`-locally connected for any `k`. -/
theorem strip_not_kLocallyConnected (k : ℝ) :
    ¬ IsKLocallyConnected {z : ℂ | 0 < z.im ∧ z.im < 1} k := by
  rintro ⟨hk1, hlc⟩
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk1
  set z₀ : ℂ := Complex.I / 2 with hz₀def
  have hz₀re : z₀.re = 0 := by rw [hz₀def]; simp
  have hz₀im : z₀.im = 1 / 2 := by rw [hz₀def]; simp
  -- Clause (ii) at the midline point `i/2` with radius `r = k`, so that `r / k = 1`.
  obtain ⟨-, h2⟩ := hlc z₀ k hk0
  rw [div_self hk0.ne'] at h2
  -- Two points of the strip on the midline, at distance `k + 1 > k` on opposite sides.
  have hcpos : (0 : ℝ) < k + 1 := by linarith
  have hmem : ∀ s : ℝ, |s| = k + 1 →
      ((s : ℂ) + z₀) ∈ {z : ℂ | 0 < z.im ∧ z.im < 1} \ Metric.ball z₀ k := by
    intro s hs
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Complex.add_im, Complex.ofReal_im, hz₀im]
      norm_num
    · rw [Complex.add_im, Complex.ofReal_im, hz₀im]
      norm_num
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, Complex.norm_real,
        Real.norm_eq_abs, hs]
      exact not_lt.2 (by linarith)
  have hp := hmem (-(k + 1)) (by rw [abs_neg, abs_of_pos hcpos])
  have hq := hmem (k + 1) (abs_of_pos hcpos)
  obtain ⟨γ, hγ⟩ := h2 _ hp _ hq
  -- `Re` runs from `-(k+1)` to `k+1` along the path, so it vanishes somewhere.
  have hcont : ContinuousOn (fun t : ℝ => (γ.extend t).re) (Set.Icc 0 1) :=
    (Complex.continuous_re.comp γ.continuous_extend).continuousOn
  have h0 : (fun t : ℝ => (γ.extend t).re) 0 = -(k + 1) := by
    simp only [Path.extend_zero]
    rw [Complex.add_re, Complex.ofReal_re, hz₀re, add_zero]
  have h1 : (fun t : ℝ => (γ.extend t).re) 1 = k + 1 := by
    simp only [Path.extend_one]
    rw [Complex.add_re, Complex.ofReal_re, hz₀re, add_zero]
  have hzero : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => (γ.extend t).re) 0)
      ((fun t : ℝ => (γ.extend t).re) 1) := by
    rw [h0, h1]
    exact ⟨by linarith, hcpos.le⟩
  obtain ⟨t, ht, hre⟩ := intermediate_value_Icc zero_le_one hcont hzero
  have hre' : (γ.extend t).re = 0 := hre
  -- The path stays in the strip, so at that parameter it is a cross-section point,
  -- and every cross-section point of this strip lies within `1/2 < 1` of the midline.
  have hwmem : γ.extend t ∈ {z : ℂ | 0 < z.im ∧ z.im < 1} \ Metric.ball z₀ 1 := by
    rw [Path.extend_extends' γ ⟨t, ht⟩]
    exact hγ ⟨t, ht⟩
  obtain ⟨him0, him1⟩ := hwmem.1
  have hnorm : ‖γ.extend t - z₀‖ < 1 := by
    have hb := Complex.norm_le_abs_re_add_abs_im (γ.extend t - z₀)
    rw [Complex.sub_re, Complex.sub_im, hre', hz₀re, hz₀im, sub_zero, abs_zero,
      zero_add] at hb
    refine lt_of_le_of_lt hb ?_
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  exact hwmem.2 (by rw [Metric.mem_ball, dist_eq_norm]; exact hnorm)

/-- **Theorem 20.4**: an `a`-Schwarz domain is `k`-locally connected with `k = 1 + 15/a`.

Not proved (kept as sorry).  The book's argument needs two things that are available neither
in this development nor in Mathlib: Koebe's ¼-theorem in the form (20.14),
`η_D(z) ≥ 1/(2 dist(z, ∂D))`, and the planar separation step "choose `wⱼ ∈ Aⱼ ∖ D` with
`|wⱼ - z₀| = kr`" for the two sides `A₁, A₂` of the Jordan curve `β ∪ [z₁, z₂]`, which the
book asserts without proof and which requires Janiszewski-type topology. -/
theorem thm20_4 {D : Set ℂ} {a : ℝ} (hD : IsSchwarzDomain D a) : IsKLocallyConnected D (1 + 15 / a) := by
  sorry

/-- **Theorem 20.5** (Gehring): an `a`-Schwarz domain is a `K`-quasidisc with `K` depending only
on `a`. -/
theorem thm20_5_gehring {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, ∀ D : Set ℂ, IsSchwarzDomain D a → IsKQuasidisc D K := by
  sorry

/-- Theorems 20.3 and 20.5: a simply connected hyperbolic domain is a Schwarz domain iff it is a
quasidisc. -/
theorem schwarzDomain_iff_quasidisc {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) :
    (∃ a : ℝ, IsSchwarzDomain D a) ↔ ∃ K : ℝ, IsKQuasidisc D K := by
  sorry

end LiZhongQC
