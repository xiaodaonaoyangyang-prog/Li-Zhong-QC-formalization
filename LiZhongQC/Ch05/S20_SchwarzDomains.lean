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

/-- A planar quasiconformal reflection `g : A₁ → A₂` across the common boundary of the plane
domains `A₁`, `A₂`: an injective map of `A₁` onto `A₂`, anti-quasiconformal (`conj ∘ g` is
`K`-q.c.) and tending to the identity at the common boundary. -/
def IsPlanarQCReflection (A₁ A₂ : Set ℂ) (g : ℂ → ℂ) (K : ℝ) : Prop :=
  InjOn g A₁ ∧ g '' A₁ = A₂ ∧ IsKQC (fun z => conj (g z)) A₁ K ∧
    ∀ p ∈ frontier A₁ ∩ frontier A₂, Tendsto g (𝓝[A₁] p) (𝓝 p)

/-! ### S20 lemma track interface (coordinator 553e2d): Lemmas 20.1–20.3

The first four declarations are scout A's probes (renamed); everything in this block is proved. -/

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

Helpers first (from the scout probes, renamed `t203_`), then the Stage A lemmas; everything here is proved. -/

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

/-! ### Theorem 20.2 (Ahlfors–Weill): the Theorem 20.3 construction with the circle reflection

Theorem 20.2 is the Theorem 20.3 construction (`t203_family`, `t203_limit`, `t203_package`) on the unit disc, with the
explicit reflection `z ↦ r²/z̄` of `{|z| < r}` in place of the reflection of Lemma 20.3. For it the invariant bound
`|g z - z|² |dg z| η(g z)²` equals `4` (the sharp `c₀`), so the dilatation is at most `c₀ s/2 = 2s`. -/

/-- The unit disc is a `1`-quasidisc: its boundary circle is the image of `S¹` under the identity. -/
theorem aw20_unitDisc_isKQuasidisc : IsKQuasidisc unitDisc 1 := by
  have hfr : frontier (toExt unitDisc) = toExt (sphere (0 : ℂ) 1) := by
    unfold unitDisc
    rw [frontier_toExt_of_isBounded' isBounded_ball isOpen_ball, frontier_ball (0 : ℂ) one_ne_zero]
  have hid : IsKQC (fun z : ℂ => z) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨differentiableOn_id, injOn_id _, image_id _⟩
  have hmap : ∀ p : ExtPlane, mobiusExt 1 0 0 1 (OnePoint.map (fun z : ℂ => z) p) = p := by
    intro p
    rw [t203_pack_mobius_id]
    induction p using OnePoint.rec <;> rfl
  refine ⟨⟨isOpen_ball, (convex_ball (0 : ℂ) 1).isConnected (nonempty_ball.2 one_pos), ?_⟩, ?_⟩
  · rw [hfr]
    simpa using t203_exh_jordan (Homeomorph.refl ExtPlane) one_pos
  · rw [hfr]
    refine ⟨fun z : ℂ => z, hid, image_id _, mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
    rw [image_image]
    simp only [hmap, image_id']

/-- `z ↦ z/r` maps the disc `{|z| < r}` conformally onto `Δ`. -/
theorem aw20_conformal_ball {r : ℝ} (hr : 0 < r) : IsConformalOnto (fun z : ℂ => z / r) (ball 0 r) unitDisc := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨(differentiable_id.div_const _).differentiableOn, fun a _ b _ h => ?_, ?_⟩
  · simpa [hr0] using h
  · unfold unitDisc
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_div, hnr, div_lt_one hr]
      exact hz
    · intro hw
      refine ⟨w * r, ?_, mul_div_cancel_right₀ _ hr0⟩
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul, hnr]
      nlinarith

/-- The Poincaré density of the disc `{|z| < r}`: `η(w) = 2r/(r² - |w|²)`. -/
theorem aw20_density_ball {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poincareDensity (ball 0 r) w = 2 * r / (r ^ 2 - ‖w‖ ^ 2) := by
  have hφ := aw20_conformal_ball hr
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hw' : ‖w‖ < r := mem_ball_zero_iff.1 hw
  have hd : deriv (fun z : ℂ => z / r) w = 1 / r := by
    rw [deriv_div_const, deriv_id'']
  rw [(poincareDensity_well_defined isOpen_ball hφ hφ hw).2, hd, norm_div, norm_div, norm_one, hnr]
  have h1 : 0 < r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  field_simp

/-- The reflection `g(z) = r²/z̄` in the circle `|z| = r` is `C¹` off the closed disc, an anti-conformal (so
`1`-quasiconformal) reflection of `ℂ ∖ {|z| ≤ r}` onto `{|z| < r} ∖ {0}`, and `g z → 0` as `z → ∞`. -/
theorem aw20_reflection {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ 1 (fun z : ℂ => (r : ℂ) ^ 2 / conj z) (closure (ball (0 : ℂ) r))ᶜ ∧
      IsPlanarQCReflection (closure (ball (0 : ℂ) r))ᶜ (ball 0 r \ {0}) (fun z : ℂ => (r : ℂ) ^ 2 / conj z) 1 ∧
      Tendsto (fun z : ℂ => (r : ℂ) ^ 2 / conj z) (cocompact ℂ ⊓ 𝓟 (closure (ball (0 : ℂ) r))ᶜ) (𝓝 0) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hr2 : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hA : (closure (ball (0 : ℂ) r))ᶜ = {z : ℂ | r < ‖z‖} := by
    rw [closure_ball 0 hr.ne']
    ext z
    simp [mem_closedBall, dist_zero_right, not_le]
  have hAo : IsOpen (closure (ball (0 : ℂ) r))ᶜ := isClosed_closure.isOpen_compl
  have hne : ∀ z ∈ (closure (ball (0 : ℂ) r))ᶜ, z ≠ 0 := by
    intro z hz h0
    rw [hA, mem_ofPred_eq, h0, norm_zero] at hz
    linarith
  have hconj : ∀ z : ℂ, conj ((r : ℂ) ^ 2 / conj z) = (r : ℂ) ^ 2 / z := by
    intro z
    rw [map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  have hnorm : ∀ z : ℂ, ‖(r : ℂ) ^ 2 / conj z‖ = r ^ 2 / ‖z‖ := by
    intro z
    rw [norm_div, norm_pow, hnr, Complex.norm_conj]
  -- `g` is injective on the exterior (in fact everywhere off `0`)
  have hinj : InjOn (fun z : ℂ => (r : ℂ) ^ 2 / conj z) (closure (ball (0 : ℂ) r))ᶜ := by
    intro a ha b hb h
    have ha0 : conj a ≠ 0 := (map_ne_zero _).2 (hne a ha)
    have hb0 : conj b ≠ 0 := (map_ne_zero _).2 (hne b hb)
    have h' : conj a = conj b := by
      have := h
      simp only at this
      field_simp at this
      exact this.symm
    exact (starRingEnd ℂ).injective h'
  refine ⟨fun z hz => ?_, ⟨hinj, ?_, ?_, fun p hp => ?_⟩, ?_⟩
  · -- `C¹`: `r² · (z̄)⁻¹`
    have hc : conj z ≠ 0 := (map_ne_zero _).2 (hne z hz)
    have h : ContDiffAt ℝ 1 (fun w : ℂ => (r : ℂ) ^ 2 * (conjCLE w)⁻¹) z :=
      (contDiffAt_const (c := (r : ℂ) ^ 2)).mul
        (((conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := 1)).contDiffAt.inv (by simpa using hc))
    simp only [Complex.conjCLE_apply] at h
    simp only [div_eq_mul_inv]
    exact h.contDiffWithinAt
  · -- the image is the punctured disc
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : r < ‖z‖ := by rw [hA] at hz; exact hz
      have hz0 : 0 < ‖z‖ := hr.trans hz'
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, hnorm, div_lt_iff₀ hz0]
        nlinarith
      · rw [mem_singleton_iff]
        exact div_ne_zero hr2 ((map_ne_zero _).2 (norm_pos_iff.1 hz0))
    · rintro ⟨hw, hw0⟩
      have hw0' : w ≠ 0 := hw0
      have hwr : ‖w‖ < r := mem_ball_zero_iff.1 hw
      have hwp : 0 < ‖w‖ := norm_pos_iff.2 hw0'
      refine ⟨(r : ℂ) ^ 2 / conj w, ?_, ?_⟩
      · rw [hA, mem_ofPred_eq, hnorm, lt_div_iff₀ hwp]
        nlinarith
      · simp only
        rw [hconj w]
        field_simp
  · -- `conj ∘ g = r²/z` is conformal on the exterior
    refine isKQC_one_of_conformal hAo ⟨?_, ?_, rfl⟩
    · refine DifferentiableOn.congr (f := fun z : ℂ => (r : ℂ) ^ 2 / z) ?_ fun z _ => hconj z
      exact fun z hz => (differentiableAt_const _).div differentiableAt_id (hne z hz) |>.differentiableWithinAt
    · intro a ha b hb h
      exact hinj ha hb ((starRingEnd ℂ).injective h)
  · -- at the circle `g` is the identity
    have hp1 : p ∈ sphere (0 : ℂ) r := by
      have := hp.1
      rwa [frontier_compl, closure_ball 0 hr.ne', frontier_closedBall (0 : ℂ) hr.ne'] at this
    have hpr : ‖p‖ = r := mem_sphere_zero_iff_norm.1 hp1
    have hp0 : p ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hpr
      linarith
    have hcp : conj p ≠ 0 := (map_ne_zero _).2 hp0
    have hgp : (r : ℂ) ^ 2 / conj p = p := by
      rw [div_eq_iff hcp, Complex.mul_conj', hpr]
    have hcont : ContinuousAt (fun z : ℂ => (r : ℂ) ^ 2 / conj z) p :=
      continuousAt_const.div (Complex.continuous_conj.continuousAt) hcp
    have h := hcont.tendsto
    rw [hgp] at h
    exact h.mono_left nhdsWithin_le_nhds
  · -- `|g z| = r²/|z| → 0`
    refine Tendsto.mono_left ?_ inf_le_left
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul (r ^ 2)
    rw [mul_zero] at h
    refine h.congr fun z => ?_
    simp only [Function.comp]
    rw [hnorm, div_eq_mul_inv]

/-- The invariant bound of the circle reflection (the sharp constant `c₀ = 4` of (20.10)): for `|z| > r` and
`g(z) = r²/z̄`, `|g z - z|² |dg z| η_{rΔ}(g z)² = 4`. -/
theorem aw20_reflection_bound {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ (closure (ball (0 : ℂ) r))ᶜ) :
    ‖(r : ℂ) ^ 2 / conj z - z‖ ^ 2 * ‖fderiv ℝ (fun z : ℂ => (r : ℂ) ^ 2 / conj z) z‖ *
      poincareDensity (ball 0 r) ((r : ℂ) ^ 2 / conj z) ^ 2 ≤ 4 := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hz' : r < ‖z‖ := by
    rw [closure_ball 0 hr.ne'] at hz
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  have ha0 : 0 < ‖z‖ := hr.trans hz'
  have hz0 : z ≠ 0 := norm_pos_iff.1 ha0
  have hcz : conj z ≠ 0 := (map_ne_zero _).2 hz0
  -- the derivative: `dg(v) = -(r²/z̄²) v̄`
  have h1 : HasDerivAt (fun u : ℂ => (r : ℂ) ^ 2 / u) (-((r : ℂ) ^ 2) / conj z ^ 2) (conj z) := by
    have h := (hasDerivAt_inv hcz).const_mul ((r : ℂ) ^ 2)
    convert h using 1
    · ext u
      rw [div_eq_mul_inv]
    · field_simp
  have hd : HasFDerivAt (fun w : ℂ => (r : ℂ) ^ 2 / conj w)
      ((((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((r : ℂ) ^ 2) / conj z ^ 2))).restrictScalars ℝ).comp
        (conjCLE : ℂ →L[ℝ] ℂ)) z :=
    (h1.hasFDerivAt.restrictScalars ℝ).comp z (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hfd : ‖fderiv ℝ (fun w : ℂ => (r : ℂ) ^ 2 / conj w) z‖ ≤ r ^ 2 / ‖z‖ ^ 2 := by
    rw [hd.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul]
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_pow, hnr, Complex.norm_conj, Complex.norm_conj]
    exact le_of_eq (by ring)
  -- `g z - z = (r² - |z|²)/z̄`
  have hsub : ‖(r : ℂ) ^ 2 / conj z - z‖ = (‖z‖ ^ 2 - r ^ 2) / ‖z‖ := by
    have e : (r : ℂ) ^ 2 / conj z - z = ((r ^ 2 - ‖z‖ ^ 2 : ℝ) : ℂ) / conj z := by
      rw [div_sub' hcz, Complex.conj_mul']
      norm_cast
    rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj, abs_of_neg (by nlinarith)]
    ring
  -- `η(g z) = 2|z|²/(r(|z|² - r²))`
  have hgmem : (r : ℂ) ^ 2 / conj z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_div, norm_pow, hnr, Complex.norm_conj, div_lt_iff₀ ha0]
    nlinarith
  have hη : poincareDensity (ball 0 r) ((r : ℂ) ^ 2 / conj z) = 2 * ‖z‖ ^ 2 / (r * (‖z‖ ^ 2 - r ^ 2)) := by
    rw [aw20_density_ball hr hgmem, norm_div, norm_pow, hnr, Complex.norm_conj]
    have h2 : 0 < ‖z‖ ^ 2 - r ^ 2 := by nlinarith
    field_simp
  rw [hsub, hη]
  have h2 : 0 < ‖z‖ ^ 2 - r ^ 2 := by nlinarith
  calc ((‖z‖ ^ 2 - r ^ 2) / ‖z‖) ^ 2 * ‖fderiv ℝ (fun w : ℂ => (r : ℂ) ^ 2 / conj w) z‖ *
        (2 * ‖z‖ ^ 2 / (r * (‖z‖ ^ 2 - r ^ 2))) ^ 2
      ≤ ((‖z‖ ^ 2 - r ^ 2) / ‖z‖) ^ 2 * (r ^ 2 / ‖z‖ ^ 2) * (2 * ‖z‖ ^ 2 / (r * (‖z‖ ^ 2 - r ^ 2))) ^ 2 := by
        gcongr
    _ = 4 := by
        field_simp
        ring

/-- The discs `Dₙ = {|z| < 1 - 1/(n+2)}` increase to `Δ`, with compact closures in `Δ`. -/
theorem aw20_exhaustion :
    Monotone (fun n : ℕ => ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2))) ∧
      (∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) ∧ closure (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2))) ⊆ unitDisc) ∧
      ⋃ n : ℕ, ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)) = unitDisc := by
  have hr1 : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hr0 : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) := fun n => by
    have h : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    linarith
  refine ⟨fun m n hmn => ball_subset_ball ?_, fun n => ⟨hr0 n, ?_⟩, ?_⟩
  · have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · rw [closure_ball 0 (hr0 n).ne']
    exact closedBall_subset_ball (hr1 n)
  · unfold unitDisc
    apply Subset.antisymm
    · exact iUnion_subset fun n => ball_subset_ball (hr1 n).le
    · intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hz1)
      refine mem_iUnion.2 ⟨n, mem_ball_zero_iff.2 ?_⟩
      have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith

/-- **The extension family on `Δ`** (`t203_family` with the circle reflections): a locally univalent meromorphic `f`
in `Δ` with `‖S_f‖_Δ ≤ s < 1/2` has, on the discs `Dₙ ↑ Δ`, extensions `Fₙ` of `f|Dₙ` to homeomorphisms of `ℂ̄`
which are, in every Möbius chart, `C¹` with `|∂̄| ≤ 2s |∂| < |∂|` at finite points (Stage B with `c₀ = 4`). -/
theorem aw20_family {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) {s : ℝ} (hs : 0 ≤ s) (hs2 : s < 1 / 2)
    (hSf : schwarzianNorm f unitDisc ≤ ENNReal.ofReal s) :
    ∃ (Dn : ℕ → Set ℂ) (F : ℕ → ExtPlane → ExtPlane), Monotone Dn ∧ (∀ n, IsOpen (Dn n)) ∧ ⋃ n, Dn n = unitDisc ∧
      ∀ n, Function.Bijective (F n) ∧ Continuous (F n) ∧ (∀ z ∈ Dn n, F n z = meroToExt f z) ∧
        ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ z : ℂ, mobiusExt a b c d (F n z) ≠ extInf →
          ContDiffAt ℝ 1 (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z ∧
          ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ <
            ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ∧
          ‖dzbar (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ ≤
            2 * s * ‖dz (fun w : ℂ => extToC (mobiusExt a b c d (F n w))) z‖ := by
  obtain ⟨hmono, hrad, hU⟩ := aw20_exhaustion
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hrat⟩ := t203_ode_pair aw20_unitDisc_isKQuasidisc hf
  have hDo : IsOpen unitDisc := isOpen_ball
  have hφD : IsConformalOnto (fun z : ℂ => z / ((1 : ℝ) : ℂ)) unitDisc unitDisc := aw20_conformal_ball one_pos
  have hset : ∀ n : ℕ, t203_Setting unitDisc (ball 0 (1 - 1 / ((n : ℝ) + 2))) w₁ w₂ (schwarzian f)
      (fun z : ℂ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) ^ 2 / conj z) 0 1 4 s := by
    intro n
    obtain ⟨hr, hcl⟩ := hrad n
    obtain ⟨hC1, hR, hT⟩ := aw20_reflection hr
    have hφ := aw20_conformal_ball hr
    have hsub : ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)) ⊆ unitDisc := subset_closure.trans hcl
    have hnorm := (t203_schwarzianNorm_mono hDo isOpen_ball hsub hφD hφ f).trans hSf
    refine ⟨hDo, isOpen_ball, ?_, hcl, ⟨_, hφ⟩, hw₁, hw₂, hode, mem_ball_self hr, hC1, hR, hT,
      fun z hz => aw20_reflection_bound hr hz, hs, by linarith, fun ζ hζ => ?_⟩
    · rw [closure_ball 0 hr.ne']
      exact isCompact_closedBall 0 _
    have hpos := s20l_a2_density_pos isOpen_ball hφ hζ
    have h1 : ENNReal.ofReal (‖schwarzian f ζ‖ / poincareDensity (ball 0 (1 - 1 / ((n : ℝ) + 2))) ζ ^ 2) ≤
        schwarzianNorm f (ball 0 (1 - 1 / ((n : ℝ) + 2))) :=
      le_iSup₂ (f := fun z (_ : z ∈ ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2))) =>
        ENNReal.ofReal (‖schwarzian f z‖ / poincareDensity (ball 0 (1 - 1 / ((n : ℝ) + 2))) z ^ 2)) ζ hζ
    have h2 := h1.trans hnorm
    rw [ENNReal.ofReal_le_ofReal_iff hs, div_le_iff₀ (pow_pos hpos 2)] at h2
    exact h2
  refine ⟨fun n => ball 0 (1 - 1 / ((n : ℝ) + 2)), fun n => t203_ext w₁ w₂
      (fun z : ℂ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) ^ 2 / conj z) (closure (ball 0 (1 - 1 / ((n : ℝ) + 2)))) 0,
    hmono, fun n => isOpen_ball, hU,
    fun n => ⟨t203_covering (t203_ext_continuous (hset n)) (t203_ext_locInj (hset n)),
      t203_ext_continuous (hset n), fun z hz => ?_, fun a b c d hdet z hz => ?_⟩⟩
  · have hzc : z ∈ closure (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2))) := subset_closure hz
    change @ite ExtPlane (z ∈ closure (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)))) (Classical.propDecidable _)
      (t203_ratio (w₁ z) (w₂ z)) _ = _
    rw [ite_eq_left hzc]
    exact (hrat z ((hrad n).2 hzc)).symm
  · obtain ⟨h1, h2, h3⟩ := t203_ext_contDiffAt (hset n) hdet hz
    refine ⟨h1, h2, ?_⟩
    calc _ ≤ 4 * s / 2 * _ := h3
      _ = _ := by ring

/-- **Theorem 20.2**: a locally univalent meromorphic `f` in `Δ` with `‖S_f‖_Δ < 1/2` extends to a
quasiconformal map of `ℂ̄`, with maximal dilatation at most
`(1 + 2‖S_f‖_Δ)/(1 - 2‖S_f‖_Δ)`.

**Correction (2026-10-12, user decision).**  The bound was `(1 + ½‖S_f‖_Δ)/(1 - ½‖S_f‖_Δ)`, as
displayed in the book's proof, and the statement was **false**.  With the project's density
`ρ = 2/(1 - |z|²)`, `f(z) = √((1 + z)/(1 - z))` has `S_f(z) = (3/2)/(1 - z²)²`, so
`‖S_f‖_Δ = 3/8` and the old bound is `19/13 < 2`.  But `f(-1 + t) ~ c·t^{1/2}`, while a
`K`-quasiconformal map of `ℂ` is locally Hölder with exponent `1/K` at the interior point `-1`, so every
extension has `K ≥ 2`.  The book's own estimate (20.7), `|μ| ≤ 2‖S_f‖_Δ`, gives the bound
`(1 + 2‖S_f‖_Δ)/(1 - 2‖S_f‖_Δ)` stated here; the printed `½` is a factor-four slip.  (Analysis:
archive `prove/session_20261010_subordinate5/round_20261011_remaining/S20_COUNTEREXAMPLE.md`, independently
reviewed in `prove/session_20261010_subordinate3/round_20261011_remaining/S20_INDEPENDENT_REVIEW.md`.) -/
theorem thm20_2 {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : schwarzianNorm f unitDisc < ENNReal.ofReal (1 / 2)) :
    HasQCExtensionExt f unitDisc
      ((1 + 2 * (schwarzianNorm f unitDisc).toReal) / (1 - 2 * (schwarzianNorm f unitDisc).toReal)) := by
  -- `s = ‖S_f‖_Δ < 1/2`; the family of `aw20_family` has dilatation `≤ 2s`, then the limit and the packaging of
  -- Theorem 20.3 (`t203_limit`, `t203_package`)
  obtain ⟨h1, h2, h3⟩ := t203_t_toReal hS
  obtain ⟨Dn, F, hmono, hopen, hU, hF⟩ := aw20_family hf h2 h3 h1
  obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD⟩ :=
    t203_limit (by linarith) (by linarith) le_rfl ⟨0, mem_ball_self one_pos⟩ isOpen_ball hmono hopen hU hF
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

/-! ### Theorem 20.4 (s21u P2a, coordinator 553e2d, 2026-09-27)

Route (s21u scout U2).  The planar separation step of the book is the winding-number statement `s20v_ps`, proved by
an additive Cousin splitting (`s20v_cousin`) and Dixon's polygon Cauchy theorem.  The analytic step is `s20v_analytic`
(Koebe (20.14) is `t203_density_ge`).  For condition (ii) of `k`-local connectivity the open set `B` is the exterior of
the closed ball of radius `r/k`, with the loop correction `s20v_ext_loop` and the cross-ratio bound `s20v_ext_bound`;
no inversion of `D` is used.  Everything in this block is proved. -/

/-- Smooth Urysohn function on `ℂ`: `0` near the closed set `s`, `1` near the disjoint closed set `t`. -/
theorem s20v_urysohn {s t : Set ℂ} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ᶠ x in 𝓝ˢ s, ψ x = 0) ∧
      (∀ᶠ x in 𝓝ˢ t, ψ x = 1) := by
  obtain ⟨f, h0, h1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (modelWithCornersSelf ℝ ℂ) (n := ⊤) hs ht hst
  exact ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, h0, h1⟩

/-- Path components of an open subset of `ℂ` are open. -/
theorem s20v_pathComponentIn_open {U : Set ℂ} (hU : IsOpen U) (x : ℂ) : IsOpen (pathComponentIn U x) := by
  exact hU.pathComponentIn x

/-- The fundamental theorem of calculus on a segment: `∫_[p,q] G' = G q - G p` for `G` holomorphic on an open set
containing the segment. -/
theorem s20v_segIntegral_deriv {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U) {p q : ℂ}
    (hpq : segment ℝ p q ⊆ U) : segIntegral (deriv G) p q = G q - G p := by
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, p + (t : ℂ) * (q - p) ∈ U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hpq (mem_segment_of_mem_Icc ht)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (p + (t : ℂ) * (q - p)))
      (deriv G (p + (t : ℂ) * (q - p)) * (q - p)) t := by
    intro t ht
    have hG' : HasDerivAt G (deriv G (p + (t : ℂ) * (q - p))) (p + (t : ℂ) * (q - p)) :=
      (hG.differentiableAt (hU.mem_nhds (hmem t ht))).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ => p + (t : ℂ) * (q - p)) (q - p) t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (q - p)).const_add p
    exact hG'.comp t hl
  have hcont : ContinuousOn (fun t : ℝ => deriv G (p + (t : ℂ) * (q - p)) * (q - p)) (uIcc 0 1) := by
    have hd : ContinuousOn (deriv G) U := (hG.deriv hU).continuousOn
    refine ContinuousOn.mul ?_ continuousOn_const
    exact hd.comp (by fun_prop) fun t ht => hmem t ht
  rw [segIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

/-- Telescoping along a polygonal path: `∫_{a, l} G' = G (lastOf a l) - G a` when all segments lie in an open set on
which `G` is holomorphic. -/
theorem s20v_pathIntFrom_deriv {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U) :
    ∀ {a : ℂ} {l : List ℂ}, SegsIn U a l → pathIntFrom (deriv G) a l = G (lastOf a l) - G a := by
  intro a l hl
  induction l generalizing a with
  | nil => simp [pathIntFrom, lastOf]
  | cons b l ih =>
    simp only [pathIntFrom, lastOf]
    rw [s20v_segIntegral_deriv hU hG hl.1, ih hl.2]
    ring

/-- Polygonal connectedness: two points of a preconnected open set are joined by a polygonal path in it (the
reachability argument of `exists_primitive_of_polyIntegral_eq_zero`). -/
theorem s20v_polygon_path {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {a b : ℂ} (ha : a ∈ U)
    (hb : b ∈ U) : ∃ l : List ℂ, SegsIn U a l ∧ lastOf a l = b := by
  have hSopen : IsOpen {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U a l ∧ lastOf a l = z} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, l, hl, hlz⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
    filter_upwards [ball_mem_nhds z hr] with w hw
    refine ⟨hball hw, l ++ [w], ?_, ?_⟩
    · rw [segsIn_append]
      refine ⟨hl, ?_⟩
      simp only [SegsIn, and_true, hlz]
      exact ((convex_ball z r).segment_subset (mem_ball_self hr) hw).trans hball
    · rw [lastOf_append, hlz]
      rfl
  have hVopen : IsOpen (U \ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U a l ∧ lastOf a l = z}) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hzS⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
    filter_upwards [ball_mem_nhds z hr] with w hw
    refine ⟨hball hw, fun hwS => hzS ⟨hzU, ?_⟩⟩
    obtain ⟨-, l, hl, hlw⟩ := hwS
    refine ⟨l ++ [z], ?_, ?_⟩
    · rw [segsIn_append]
      refine ⟨hl, ?_⟩
      simp only [SegsIn, and_true, hlw]
      exact ((convex_ball z r).segment_subset hw (mem_ball_self hr)).trans hball
    · rw [lastOf_append, hlw]
      rfl
  have hsub : U ⊆ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U a l ∧ lastOf a l = z} := by
    refine hUc.subset_left_of_subset_union hSopen hVopen ?_ ?_ ?_
    · exact Set.disjoint_left.2 fun z hz hz' => hz'.2 hz
    · intro z hz
      by_cases hzS : z ∈ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U a l ∧ lastOf a l = z}
      · exact Or.inl hzS
      · exact Or.inr ⟨hz, hzS⟩
    · exact ⟨a, ha, ha, [], trivial, rfl⟩
  exact (hsub hb).2

/-- `SegsIn` is monotone in the set. -/
theorem s20v_segsIn_mono {U V : Set ℂ} (hUV : U ⊆ V) :
    ∀ {a : ℂ} {l : List ℂ}, SegsIn U a l → SegsIn V a l := by
  intro a l hl
  induction l generalizing a with
  | nil => trivial
  | cons b l ih => exact ⟨hl.1.trans hUV, ih hl.2⟩

/-- The trace of the closed polygon `β + c` (`β` in `U` from `p₁` to `p₂`, `c` in `V` back to `p₁`) lies in
`U ∪ V`. -/
theorem s20v_trace_subset {U V : Set ℂ} {p₁ p₂ : ℂ} {lβ lc : List ℂ} (hp₁ : p₁ ∈ U) (hβ : SegsIn U p₁ lβ)
    (hβe : lastOf p₁ lβ = p₂) (hc : SegsIn V p₂ lc) (hce : lastOf p₂ lc = p₁) :
    polyTrace (p₁ :: (lβ ++ lc)) ⊆ U ∪ V := by
  refine polyTrace_cons_subset ?_ ?_
  · rw [segsIn_append]
    refine ⟨s20v_segsIn_mono subset_union_left hβ, ?_⟩
    rw [hβe]
    exact s20v_segsIn_mono subset_union_right hc
  · rw [lastOf_append, hβe, hce, segment_same]
    exact singleton_subset_iff.2 (Or.inl hp₁)

/-- Winding numbers add when a closed loop at the base point is appended to a closed polygon. -/
theorem s20v_polyWinding_append {a w : ℂ} {A L : List ℂ} (hA : lastOf a A = a) (hL : lastOf a L = a) :
    polyWinding (a :: (A ++ L)) w = polyWinding (a :: A) w + polyWinding (a :: L) w := by
  simp only [polyWinding, polyIntegral_cons, pathIntFrom_append, lastOf_append, hA, hL, segIntegral_self]
  ring

/-- The complement of a simply connected hyperbolic domain is unbounded: otherwise a large circle in `D` would carry
`∮ (z - w₀)⁻¹ = 2πi` although `(z - w₀)⁻¹` has a primitive on `D`. -/
theorem s20v_compl_unbounded {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) (R : ℝ) :
    ∃ w, w ∉ D ∧ R < ‖w‖ := by
  by_contra hcon'
  have hcon : ∀ w, w ∉ D → ‖w‖ ≤ R := fun w hw => not_lt.1 fun h => hcon' ⟨w, hw, h⟩
  obtain ⟨hDo, hDc, hDs, hDne⟩ := hD
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ D := by
    by_contra h
    exact hDne (eq_univ_of_forall fun w => by_contra fun hw => h ⟨w, hw⟩)
  have hR' : 0 < |R| + ‖w₀‖ + 1 := by positivity
  have hsph : sphere (0 : ℂ) (|R| + ‖w₀‖ + 1) ⊆ D := by
    intro z hz
    by_contra hzD
    have h1 := hcon z hzD
    rw [mem_sphere_zero_iff_norm] at hz
    have h2 := le_abs_self R
    have h3 := norm_nonneg w₀
    linarith
  have hsc : SimplyConnectedSpace D := hDs
  have hg : DifferentiableOn ℂ (fun ζ => (ζ - w₀)⁻¹) D := by
    intro ζ hζ
    have hne : ζ - w₀ ≠ 0 := sub_ne_zero.2 fun h => hw₀ (h ▸ hζ)
    exact ((differentiableAt_id.sub_const w₀).inv hne).differentiableWithinAt
  obtain ⟨G, hGd, hGder⟩ := RMT.exists_primitive_of_simplyConnected hDo hDc hg
  have h0 : circleIntegral (fun ζ => (ζ - w₀)⁻¹) 0 (|R| + ‖w₀‖ + 1) = 0 := by
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := G) hR'.le fun ζ hζ => ?_
    have hζD := hsph hζ
    have h := (hGd.differentiableAt (hDo.mem_nhds hζD)).hasDerivAt
    rw [hGder ζ hζD] at h
    exact h.hasDerivWithinAt
  have h1 : circleIntegral (fun ζ => (ζ - w₀)⁻¹) 0 (|R| + ‖w₀‖ + 1) = 2 * π * I := by
    refine circleIntegral.integral_sub_inv_of_mem_ball ?_
    rw [mem_ball_zero_iff]
    have := abs_nonneg R
    linarith
  rw [h0] at h1
  exact two_pi_I_ne_zero h1.symm

/-- `∂_z̄` vanishes near a point around which the function is constant. -/
theorem s20v_a_dzbar_eventually_zero {g : ℂ → ℂ} {x c : ℂ} (h : ∀ᶠ y in 𝓝 x, g y = c) :
    ∀ᶠ y in 𝓝 x, dzbar g y = 0 := by
  filter_upwards [h.eventually_nhds] with y hy
  rw [dzbar_congr_of_eventuallyEq (v := fun _ => c) hy]
  simp [dzbar]

/-- Cauchy–Riemann for a difference: if `g` and `u` are real-differentiable at `x` with `∂_z̄ g x = ∂_z̄ u x`, then
`g - u` is complex-differentiable at `x` (`cauchyRiemann_iff`). -/
theorem s20v_a_differentiableAt_sub {g u : ℂ → ℂ} {x : ℂ} (hg : DifferentiableAt ℝ g x)
    (hu : DifferentiableAt ℝ u x) (h : dzbar g x = dzbar u x) :
    DifferentiableAt ℂ (fun y => g y - u y) x := by
  refine cauchyRiemann_iff.2 ⟨hg.sub hu, ?_⟩
  have e : fderiv ℝ (fun y => g y - u y) x = fderiv ℝ g x - fderiv ℝ u x :=
    (hg.hasFDerivAt.sub hu.hasFDerivAt).fderiv
  simp only [dzbar, e, sub_apply] at h ⊢
  linear_combination h

/-- **Additive Cousin splitting near a compact set.**  For open `D`, `B`, a relatively clopen
`V ⊆ D ∩ B` and a compact `K ⊆ D ∪ B` there are an open `W ⊇ K` and `G₁` holomorphic on `D ∩ W`, `G₂` holomorphic on
`B ∩ W`, with `G₁ - G₂ = 1_V` on `D ∩ B ∩ W`.

*Truth.* This is the Mayer–Vietoris splitting of the locally constant function `1_V` on the cover `{D, B}`.  It is
needed only near the compact `K`, so no exhaustion or Runge argument enters: take a compact neighbourhood
`K₁ ⊆ D ∪ B` of `K`, `ψ` smooth with `ψ = 0` near `K₁ \ B` and `ψ = 1` near `K₁ \ D`, `ω := (∂̄ψ) · 1_V`, which is
smooth on `interior K₁` (`ψ` is locally constant off `D ∩ B`, `1_V` is locally constant on `D ∩ B`), a cutoff `φ`
equal to `1` near `K` with support in `interior K₁`, and `u := cauchyT (φ ω)`, so `∂̄u = φ ω`.  Then
`G₁ := ψ 1_V - u` and `G₂ := (ψ - 1) 1_V - u` have `∂̄ = 0` where `φ = 1` and `G₁ - G₂ = 1_V`.

*Route/reuse.* `s20v_urysohn` (this block) for `ψ` and `φ`; `eq11_17` (S11:2268: `cauchyT` of a compactly supported
smooth function is `C¹` with `∂̄ (cauchyT ω) = ω`); `cauchyRiemann_iff` (S06:98) for holomorphy; `W := interior K₁ ∩
interior {φ = 1}`. -/
theorem s20v_cousin {D B V K : Set ℂ} (hD : IsOpen D) (hB : IsOpen B) (hV : IsOpen V) (hVDB : V ⊆ D ∩ B)
    (hV' : IsOpen ((D ∩ B) \ V)) (hK : IsCompact K) (hKDB : K ⊆ D ∪ B) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ G₁ G₂ : ℂ → ℂ, DifferentiableOn ℂ G₁ (D ∩ W) ∧
      DifferentiableOn ℂ G₂ (B ∩ W) ∧ ∀ x ∈ D ∩ B ∩ W, G₁ x - G₂ x = V.indicator (fun _ => (1 : ℂ)) x := by
  have _ := hVDB
  obtain ⟨K₁, hK₁c, hKK₁, hK₁U⟩ := exists_compact_between hK (hD.union hB) hKDB
  obtain ⟨K₂, hK₂c, hKK₂, hK₂K₁⟩ := exists_compact_between hK isOpen_interior hKK₁
  -- the Urysohn function `ψ` of the cover `{D, B}` near `K₁`
  have hA : Disjoint (K₁ \ B) (K₁ \ D) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx, hxB⟩ ⟨_, hxD⟩
    rcases hK₁U hx with h | h
    · exact hxD h
    · exact hxB h
  obtain ⟨ψ, hψs, hψ0, hψ1⟩ := s20v_urysohn (hK₁c.isClosed.sdiff hB) (hK₁c.isClosed.sdiff hD) hA
  -- the cutoff `φ`: `1` near `K`, supported in `K₂`
  have hφd : Disjoint (interior K₂)ᶜ K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    exact (Set.mem_compl_iff _ _).1 hx (hKK₂ hxK)
  obtain ⟨φ, hφs, hφ0, hφ1⟩ := s20v_urysohn isOpen_interior.isClosed_compl hK.isClosed hφd
  have hφK₂ : ∀ x, x ∉ K₂ → φ x = 0 := fun x hx =>
    hφ0.self_of_nhdsSet x (Set.mem_compl fun h => hx (interior_subset h))
  have htsK₂ : tsupport φ ⊆ K₂ :=
    closure_minimal (fun y hy => by
      by_contra h
      exact Function.mem_support.1 hy (hφK₂ y h)) hK₂c.isClosed
  obtain ⟨U, hUo, hKU, hU1⟩ := mem_nhdsSet_iff_exists.1 hφ1
  -- the data `ψ`, `1_V`, `ω = φ · ∂_z̄ψ · 1_V`
  obtain ⟨ψc, hψc⟩ : ∃ g : ℂ → ℂ, g = fun x => (ψ x : ℂ) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ g : ℂ → ℂ, g = V.indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ g : ℂ → ℂ, g = fun x => (φ x : ℂ) * (dzbar ψc x * f x) := ⟨_, rfl⟩
  have hψcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψc := by
    rw [hψc]
    exact Complex.ofRealCLM.contDiff.comp hψs
  have hφcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφs
  have hdψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dzbar ψc) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ψc z 1) :=
      (hψcs.fderiv_right (le_refl _)).clm_apply contDiff_const
    have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ψc z I) :=
      (hψcs.fderiv_right (le_refl _)).clm_apply contDiff_const
    exact (h1.add (contDiff_const.mul hI)).div_const 2
  have hfV : ∀ x ∈ V, f x = 1 := fun x hx => by rw [hf, indicator_of_mem hx]
  have hfV' : ∀ x, x ∉ V → f x = 0 := fun x hx => by rw [hf, indicator_of_notMem hx]
  have hfV1 : ∀ x ∈ V, ∀ᶠ y in 𝓝 x, f y = 1 := fun x hx =>
    Filter.mem_of_superset (hV.mem_nhds hx) fun y hy => hfV y hy
  have hfV0 : ∀ x ∈ (D ∩ B) \ V, ∀ᶠ y in 𝓝 x, f y = 0 := fun x hx =>
    Filter.mem_of_superset (hV'.mem_nhds hx) fun y hy => hfV' y hy.2
  have hψ0' : ∀ x ∈ K₁ \ B, ∀ᶠ y in 𝓝 x, ψc y = 0 := by
    intro x hx
    filter_upwards [hψ0.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [hψc, hy, Complex.ofReal_zero]
  have hψ1' : ∀ x ∈ K₁ \ D, ∀ᶠ y in 𝓝 x, ψc y = 1 := by
    intro x hx
    filter_upwards [hψ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [hψc, hy, Complex.ofReal_one]
  -- `ω` is smooth with compact support
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := by
    have hzero : ∀ x, (∀ᶠ y in 𝓝 x, ω y = 0) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω x :=
      fun x hx => contDiffAt_const.congr_of_eventuallyEq hx
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport φ
    · have hxK₁ : x ∈ K₁ := interior_subset (hK₂K₁ (htsK₂ hx))
      by_cases hxB : x ∈ B
      · by_cases hxD : x ∈ D
        · by_cases hxV : x ∈ V
          · have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (φ y : ℂ) * (dzbar ψc y * 1)) :=
              hφcs.mul (hdψ.mul contDiff_const)
            refine hsm.contDiffAt.congr_of_eventuallyEq ?_
            filter_upwards [hfV1 x hxV] with y hy
            simp only [hω, hy]
          · apply hzero
            filter_upwards [hfV0 x ⟨⟨hxD, hxB⟩, hxV⟩] with y hy
            simp only [hω, hy, mul_zero]
        · apply hzero
          filter_upwards [s20v_a_dzbar_eventually_zero (hψ1' x ⟨hxK₁, hxD⟩)] with y hy
          simp only [hω, hy, zero_mul, mul_zero]
      · apply hzero
        filter_upwards [s20v_a_dzbar_eventually_zero (hψ0' x ⟨hxK₁, hxB⟩)] with y hy
        simp only [hω, hy, zero_mul, mul_zero]
    · apply hzero
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hω, hy]
  have hωc : HasCompactSupport ω := HasCompactSupport.intro hK₂c fun x hx => by simp [hω, hφK₂ x hx]
  obtain ⟨hu1, hdu⟩ := eq11_17 hωs hωc
  have hud : ∀ x, DifferentiableAt ℝ (cauchyT ω) x := fun x => hu1.differentiable one_ne_zero x
  have hψd : ∀ x, DifferentiableAt ℝ ψc x := fun x => hψcs.differentiable (by simp) x
  have hωx : ∀ x ∈ U, dzbar (cauchyT ω) x = dzbar ψc x * f x := by
    intro x hxU
    have hφx : φ x = 1 := hU1 hxU
    rw [(hdu x).1, hω]
    simp [hφx]
  have h0 : ∀ x, x ∉ V → x ∈ U → DifferentiableAt ℂ (fun y => (fun _ => (0 : ℂ)) y - cauchyT ω y) x := by
    intro x hxV hxU
    refine s20v_a_differentiableAt_sub (differentiableAt_const _) (hud x) ?_
    rw [hωx x hxU, hfV' x hxV, mul_zero]
    simp [dzbar]
  refine ⟨U ∩ interior K₁, hUo.inter isOpen_interior, subset_inter hKU hKK₁,
    fun x => ψc x * f x - cauchyT ω x, fun x => (ψc x - 1) * f x - cauchyT ω x, ?_, ?_, ?_⟩
  · rintro x ⟨hxD, hxU, hxK⟩
    have hxK₁ : x ∈ K₁ := interior_subset hxK
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hxV : x ∈ V
    · have h := s20v_a_differentiableAt_sub (hψd x) (hud x) (by rw [hωx x hxU, hfV x hxV, mul_one])
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [hfV1 x hxV] with y hy
      rw [hy, mul_one]
    · refine (h0 x hxV hxU).congr_of_eventuallyEq ?_
      by_cases hxB : x ∈ B
      · filter_upwards [hfV0 x ⟨⟨hxD, hxB⟩, hxV⟩] with y hy
        rw [hy, mul_zero]
      · filter_upwards [hψ0' x ⟨hxK₁, hxB⟩] with y hy
        rw [hy, zero_mul]
  · rintro x ⟨hxB, hxU, hxK⟩
    have hxK₁ : x ∈ K₁ := interior_subset hxK
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hxV : x ∈ V
    · have h := (s20v_a_differentiableAt_sub (hψd x) (hud x)
        (by rw [hωx x hxU, hfV x hxV, mul_one])).sub_const 1
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [hfV1 x hxV] with y hy
      rw [hy, mul_one]
      ring
    · refine (h0 x hxV hxU).congr_of_eventuallyEq ?_
      by_cases hxD : x ∈ D
      · filter_upwards [hfV0 x ⟨⟨hxD, hxB⟩, hxV⟩] with y hy
        rw [hy, mul_zero]
      · filter_upwards [hψ1' x ⟨hxK₁, hxD⟩] with y hy
        rw [hy, sub_self, zero_mul]
  · intro x _
    show ψc x * f x - cauchyT ω x - ((ψc x - 1) * f x - cauchyT ω x) = V.indicator (fun _ => (1 : ℂ)) x
    rw [← hf]
    ring

/-- `SegsIn` into an intersection. -/
theorem s20v_b_segsIn_inter {U V : Set ℂ} :
    ∀ {a : ℂ} {l : List ℂ}, SegsIn U a l → SegsIn V a l → SegsIn (U ∩ V) a l := by
  intro a l hU hV
  induction l generalizing a with
  | nil => trivial
  | cons b l ih => exact ⟨subset_inter hU.1 hV.1, ih hU.2 hV.2⟩

/-- The segments of the open path `a, l` lie in the trace of the closed polygon `a :: l`. -/
theorem s20v_b_segsIn_polyTrace (a : ℂ) (l : List ℂ) : SegsIn (polyTrace (a :: l)) a l := by
  have key : ∀ (c a : ℂ) (l : List ℂ),
      SegsIn (⋃ e ∈ (a :: l).zip (l ++ [c]), segment ℝ e.1 e.2) a l := by
    intro c a l
    induction l generalizing a with
    | nil => trivial
    | cons b l ih =>
      refine ⟨fun x hx => mem_iUnion₂.2 ⟨(a, b), by simp, hx⟩, ?_⟩
      have hsub : (⋃ e ∈ (b :: l).zip (l ++ [c]), segment ℝ e.1 e.2) ⊆
          ⋃ e ∈ (a :: b :: l).zip ((b :: l) ++ [c]), segment ℝ e.1 e.2 := by
        intro x hx
        obtain ⟨e, he, hxe⟩ := mem_iUnion₂.1 hx
        refine mem_iUnion₂.2 ⟨e, ?_, hxe⟩
        rw [List.cons_append, List.zip_cons_cons]
        exact List.mem_cons_of_mem _ he
      exact s20v_segsIn_mono hsub (ih b)
  unfold polyTrace polyEdges
  rw [show (a :: l).rotate 1 = l ++ [a] by
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]]
  exact key a a l

/-- A path integral only sees the values of the integrand on the segments of the path. -/
theorem s20v_b_pathIntFrom_congr {U : Set ℂ} {f g : ℂ → ℂ} (hfg : EqOn f g U) :
    ∀ {a : ℂ} {l : List ℂ}, SegsIn U a l → pathIntFrom f a l = pathIntFrom g a l := by
  intro a l hl
  induction l generalizing a with
  | nil => simp [pathIntFrom]
  | cons b l ih =>
    simp only [pathIntFrom]
    rw [segIntegral_congr (fun x hx => hfg (hl.1 hx)), ih hl.2]

/-- The complement of a path component in an open set is open. -/
theorem s20v_b_diff_pathComponentIn_open {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    IsOpen (U \ pathComponentIn U x) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨pathComponentIn U y, ?_, hU.pathComponentIn y, mem_pathComponentIn_self hy.1⟩
  intro u hu
  refine ⟨pathComponentIn_subset hu, fun hxu => hy.2 ?_⟩
  exact (show JoinedIn U x u from hxu).trans (show JoinedIn U y u from hu).symm

/-- **Planar separation (PS).**  Let `γ = β + c` be a closed polygon with `β` in `D` from `p₁` to
`p₂` and `c` in `B` from `p₂` back to `p₁`.  If `p₁` and `p₂` lie in different path components of `D ∩ B`, then `γ`
winds around some point outside `D ∪ B`.

*Truth.* Suppose that `polyWinding γ w = 0` for every `w ∉ D ∪ B`.  Then the compact set
`Kc := trace γ ∪ {w ∉ trace γ | polyWinding γ w ≠ 0}` lies in `D ∪ B`.  Apply `s20v_cousin` with
`V := pathComponentIn (D ∩ B) p₁` (open, and so is its complement in `D ∩ B`: `s20v_pathComponentIn_open`) and
`K := Kc`.  The function `g := G₁'` on `D`, `G₂'` on `B` is holomorphic on `(D ∪ B) ∩ W`, since `G₁ - G₂` is locally
constant on `D ∩ B`.  Dixon's theorem gives `∮_γ g = 0`, because `γ` winds around no point outside `(D ∪ B) ∩ W`.
Telescoping gives `∮_γ g = (G₁ - G₂) p₂ - (G₁ - G₂) p₁ = 0 - 1`.

*Route/reuse.* `polyIntegral_eq_zero_of_polyWinding_eq_zero` (ConnectedComplement:1096), `polyIntegral_cons` (:822),
`pathIntFrom_append` (:803), `exists_polyWinding_eq_zero_of_norm_gt` (:634) and `eventually_polyWinding_eq` (:622) for
the compactness of `Kc`, `s20v_pathIntFrom_deriv` (this block) for telescoping. -/
theorem s20v_ps {D B : Set ℂ} (hD : IsOpen D) (hB : IsOpen B) {p₁ p₂ : ℂ} (hp₁ : p₁ ∈ D ∩ B)
    (hp₂ : p₂ ∈ D ∩ B) (hsep : ¬ JoinedIn (D ∩ B) p₁ p₂) {lβ lc : List ℂ} (hβ : SegsIn D p₁ lβ)
    (hβe : lastOf p₁ lβ = p₂) (hc : SegsIn B p₂ lc) (hce : lastOf p₂ lc = p₁) :
    ∃ w, w ∉ D ∧ w ∉ B ∧ polyWinding (p₁ :: (lβ ++ lc)) w ≠ 0 := by
  classical
  by_contra hcon
  have hzero : ∀ w, w ∉ D → w ∉ B → polyWinding (p₁ :: (lβ ++ lc)) w = 0 := by
    intro w hwD hwB
    by_contra hne
    exact hcon ⟨w, hwD, hwB, hne⟩
  have hTDB : polyTrace (p₁ :: (lβ ++ lc)) ⊆ D ∪ B := s20v_trace_subset hp₁.1 hβ hβe hc hce
  -- the compact set `trace ∪ {winding ≠ 0}`, with the two base points
  obtain ⟨R, hR⟩ := exists_polyWinding_eq_zero_of_norm_gt (p₁ :: (lβ ++ lc))
  obtain ⟨M, hM⟩ := (isCompact_polyTrace (p₁ :: (lβ ++ lc))).isBounded.subset_closedBall 0
  have hK₀c : IsCompact (polyTrace (p₁ :: (lβ ++ lc)) ∪ {w | polyWinding (p₁ :: (lβ ++ lc)) w ≠ 0}) := by
    refine (isCompact_closedBall (0 : ℂ) (max M R)).of_isClosed_subset ?_ ?_
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro w hw
      have hwT : w ∉ polyTrace (p₁ :: (lβ ++ lc)) := fun h => hw (Or.inl h)
      have hw0 : polyWinding (p₁ :: (lβ ++ lc)) w = 0 := by
        by_contra h
        exact hw (Or.inr h)
      filter_upwards [(isOpen_compl_polyTrace _).mem_nhds hwT, eventually_polyWinding_eq hwT] with y hyT hy
      rintro (h | h)
      · exact hyT h
      · exact h (hy.trans hw0)
    · rintro w (h | h)
      · exact closedBall_subset_closedBall (le_max_left _ _) (hM h)
      · rw [mem_closedBall_zero_iff]
        by_contra hlt
        exact h (hR w (lt_of_le_of_lt (le_max_right _ _) (not_le.1 hlt)))
  have hKc := (hK₀c.insert p₂).insert p₁
  have hKDB : insert p₁ (insert p₂ (polyTrace (p₁ :: (lβ ++ lc)) ∪
      {w | polyWinding (p₁ :: (lβ ++ lc)) w ≠ 0})) ⊆ D ∪ B := by
    rintro w (rfl | rfl | h | h)
    · exact Or.inl hp₁.1
    · exact Or.inl hp₂.1
    · exact hTDB h
    · by_contra hw
      exact h (hzero w (fun h' => hw (Or.inl h')) (fun h' => hw (Or.inr h')))
  -- the Cousin splitting of the indicator of the path component of `p₁`
  have hVo : IsOpen (pathComponentIn (D ∩ B) p₁) := (hD.inter hB).pathComponentIn p₁
  obtain ⟨W, hWo, hKW, G₁, G₂, hG₁, hG₂, hG⟩ := s20v_cousin hD hB hVo pathComponentIn_subset
    (s20v_b_diff_pathComponentIn_open (hD.inter hB) p₁) hKc hKDB
  have hderiv : ∀ y ∈ D ∩ B ∩ W, deriv G₁ y = deriv G₂ y := by
    intro y hy
    have hloc : ∀ᶠ x in 𝓝 y, (pathComponentIn (D ∩ B) p₁).indicator (fun _ => (1 : ℂ)) x =
        (pathComponentIn (D ∩ B) p₁).indicator (fun _ => (1 : ℂ)) y := by
      by_cases hyV : y ∈ pathComponentIn (D ∩ B) p₁
      · filter_upwards [hVo.mem_nhds hyV] with x hx
        rw [indicator_of_mem hx, indicator_of_mem hyV]
      · filter_upwards [(s20v_b_diff_pathComponentIn_open (hD.inter hB) p₁).mem_nhds ⟨hy.1, hyV⟩]
          with x hx
        rw [indicator_of_notMem hx.2, indicator_of_notMem hyV]
    have hev : G₁ =ᶠ[𝓝 y] fun x => G₂ x + (pathComponentIn (D ∩ B) p₁).indicator (fun _ => (1 : ℂ)) y := by
      filter_upwards [((hD.inter hB).inter hWo).mem_nhds hy, hloc] with x hx hxl
      rw [← hxl, ← hG x hx]
      ring
    rw [hev.deriv_eq]
    exact deriv_add_const _
  -- the glued derivative `g`
  have hDWo : IsOpen (D ∩ W) := hD.inter hWo
  have hBWo : IsOpen (B ∩ W) := hB.inter hWo
  set g : ℂ → ℂ := fun x => if x ∈ D then deriv G₁ x else deriv G₂ x with hg
  have hgD : EqOn g (deriv G₁) (D ∩ W) := fun x hx => by simp [hg, hx.1]
  have hgB : EqOn g (deriv G₂) (B ∩ W) := by
    intro x hx
    by_cases hxD : x ∈ D
    · simp only [hg, hxD, ↓reduceIte]
      exact hderiv x ⟨⟨hxD, hx.1⟩, hx.2⟩
    · simp [hg, hxD]
  have hgd : DifferentiableOn ℂ g ((D ∪ B) ∩ W) := by
    intro x hx
    rcases hx.1 with hxD | hxB
    · have h1 : DifferentiableAt ℂ (deriv G₁) x :=
        (hG₁.deriv hDWo).differentiableAt (hDWo.mem_nhds ⟨hxD, hx.2⟩)
      exact (h1.congr_of_eventuallyEq (Filter.eventually_of_mem (hDWo.mem_nhds ⟨hxD, hx.2⟩) hgD))
        |>.differentiableWithinAt
    · have h1 : DifferentiableAt ℂ (deriv G₂) x :=
        (hG₂.deriv hBWo).differentiableAt (hBWo.mem_nhds ⟨hxB, hx.2⟩)
      exact (h1.congr_of_eventuallyEq (Filter.eventually_of_mem (hBWo.mem_nhds ⟨hxB, hx.2⟩) hgB))
        |>.differentiableWithinAt
  -- Dixon's polygon Cauchy theorem
  have hTW : polyTrace (p₁ :: (lβ ++ lc)) ⊆ W := fun w hw =>
    hKW (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_union_left _ hw)))
  have hdix : polyIntegral g (p₁ :: (lβ ++ lc)) = 0 := by
    refine polyIntegral_eq_zero_of_polyWinding_eq_zero ((hD.union hB).inter hWo) hgd
      (fun w hw => ⟨hTDB hw, hTW hw⟩) fun a ha => ?_
    by_contra hne
    have haK : a ∈ insert p₁ (insert p₂ (polyTrace (p₁ :: (lβ ++ lc)) ∪
        {w | polyWinding (p₁ :: (lβ ++ lc)) w ≠ 0})) :=
      mem_insert_of_mem _ (mem_insert_of_mem _ (mem_union_right _ hne))
    exact ha ⟨hKDB haK, hKW haK⟩
  -- telescoping
  have hsegT := s20v_b_segsIn_polyTrace p₁ (lβ ++ lc)
  rw [segsIn_append, hβe] at hsegT
  have hβW : SegsIn (D ∩ W) p₁ lβ := s20v_b_segsIn_inter hβ (s20v_segsIn_mono hTW hsegT.1)
  have hcW : SegsIn (B ∩ W) p₂ lc := s20v_b_segsIn_inter hc (s20v_segsIn_mono hTW hsegT.2)
  have hI1 : pathIntFrom g p₁ lβ = G₁ p₂ - G₁ p₁ := by
    rw [s20v_b_pathIntFrom_congr hgD hβW, s20v_pathIntFrom_deriv hDWo hG₁ hβW, hβe]
  have hI2 : pathIntFrom g p₂ lc = G₂ p₁ - G₂ p₂ := by
    rw [s20v_b_pathIntFrom_congr hgB hcW, s20v_pathIntFrom_deriv hBWo hG₂ hcW, hce]
  have htot : polyIntegral g (p₁ :: (lβ ++ lc)) = (G₁ p₂ - G₁ p₁) + (G₂ p₁ - G₂ p₂) := by
    rw [polyIntegral_cons, pathIntFrom_append, hβe, lastOf_append, hβe, hce, segIntegral_self, hI1, hI2,
      add_zero]
  have hp₁W : p₁ ∈ W := hKW (mem_insert _ _)
  have hp₂W : p₂ ∈ W := hKW (mem_insert_of_mem _ (mem_insert _ _))
  have h1 : G₁ p₁ - G₂ p₁ = 1 := by
    rw [hG p₁ ⟨hp₁, hp₁W⟩]
    exact indicator_of_mem (mem_pathComponentIn_self hp₁) _
  have h2 : G₁ p₂ - G₂ p₂ = 0 := by
    rw [hG p₂ ⟨hp₂, hp₂W⟩]
    exact indicator_of_notMem (show p₂ ∉ pathComponentIn (D ∩ B) p₁ from hsep) _
  rw [hdix] at htot
  have h01 : (0 : ℂ) = -1 := by linear_combination htot + h2 - h1
  norm_num at h01

/-- A segment `[z + 2a, z + 2ωa]` with `ω = ±i` stays at distance `≥ ‖a‖` from `z`. -/
theorem s20v_b_seg_far {z a ω : ℂ} {t : ℝ} (hω : ω = I ∨ ω = -I) (ha : t < ‖a‖) :
    segment ℝ (z + 2 * a) (z + 2 * (ω * a)) ⊆ {ζ | t < ‖ζ - z‖} := by
  rintro ζ ⟨α, β, hα, hβ, hαβ, rfl⟩
  show t < ‖α • (z + 2 * a) + β • (z + 2 * (ω * a)) - z‖
  have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
  have hkey : α • (z + 2 * a) + β • (z + 2 * (ω * a)) - z = 2 * a * ((α : ℂ) + β * ω) := by
    rw [Complex.real_smul, Complex.real_smul]
    linear_combination z * hαβ'
  have hnorm : (1 : ℝ) / 2 ≤ ‖(α : ℂ) + β * ω‖ := by
    have hre : ((α : ℂ) + β * ω).re = α := by rcases hω with rfl | rfl <;> simp
    have him : |((α : ℂ) + β * ω).im| = β := by
      rcases hω with rfl | rfl <;> simp [abs_of_nonneg hβ]
    have h1 := Complex.abs_re_le_norm ((α : ℂ) + β * ω)
    have h2 := Complex.abs_im_le_norm ((α : ℂ) + β * ω)
    rw [hre, abs_of_nonneg hα] at h1
    rw [him] at h2
    linarith
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hkey, norm_mul, norm_mul, h2]
  nlinarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg a)]

/-- The radial segment `[z + d, z + 2d]` stays at distance `≥ ‖d‖` from `z`. -/
theorem s20v_b_seg_radial {z d : ℂ} {t : ℝ} (hd : t < ‖d‖) :
    segment ℝ (z + d) (z + 2 * d) ⊆ {ζ | t < ‖ζ - z‖} := by
  rintro ζ ⟨α, β, hα, hβ, hαβ, rfl⟩
  show t < ‖α • (z + d) + β • (z + 2 * d) - z‖
  have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
  have hkey : α • (z + d) + β • (z + 2 * d) - z = ((α + 2 * β : ℝ) : ℂ) * d := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination z * hαβ'
  rw [hkey, norm_mul, Complex.norm_real, show α + 2 * β = 1 + β by linarith,
    Real.norm_of_nonneg (show (0 : ℝ) ≤ 1 + β by linarith)]
  nlinarith [mul_nonneg hβ (norm_nonneg d)]

/-- The integral of `(ζ - z)⁻¹` along `[z + 2a, z + 2ωa]`, `ω = ±i`, is `log ω`. -/
theorem s20v_b_seg_log {z a ω : ℂ} {t : ℝ} (ht : 0 ≤ t) (hω : ω = I ∨ ω = -I) (ha : t < ‖a‖) :
    segIntegral (fun ζ => (ζ - z)⁻¹) (z + 2 * a) (z + 2 * (ω * a)) = log ω := by
  have hz : z ∉ segment ℝ (z + 2 * a) (z + 2 * (ω * a)) := by
    intro h
    have h' : t < ‖z - z‖ := s20v_b_seg_far hω ha h
    rw [sub_self, norm_zero] at h'
    linarith
  have ha0 : (2 : ℂ) * a ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    rintro rfl
    rw [norm_zero] at ha
    linarith
  rw [segIntegral_inv_sub_eq_log hz, show z + 2 * (ω * a) - z = ω * (2 * a) by ring,
    show z + 2 * a - z = 2 * a by ring, mul_div_assoc, div_self ha0, mul_one]

/-- Repeating a closed loop at `a`: the endpoint. -/
theorem s20v_b_lastOf_rep {a : ℂ} {L : List ℂ} (hL : lastOf a L = a) (n : ℕ) :
    lastOf a (List.replicate n L).flatten = a := by
  induction n with
  | zero => simp [lastOf]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, lastOf_append, hL, ih]

/-- Repeating a closed loop at `a`: the segments. -/
theorem s20v_b_segsIn_rep {U : Set ℂ} {a : ℂ} {L : List ℂ} (hL : lastOf a L = a) (hLU : SegsIn U a L)
    (n : ℕ) : SegsIn U a (List.replicate n L).flatten := by
  induction n with
  | zero => simp [SegsIn]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, segsIn_append, hL]
    exact ⟨hLU, ih⟩

/-- Repeating a closed loop at `a`: the path integral. -/
theorem s20v_b_pathIntFrom_rep (h : ℂ → ℂ) {a : ℂ} {L : List ℂ} (hL : lastOf a L = a) (n : ℕ) :
    pathIntFrom h a (List.replicate n L).flatten = n * pathIntFrom h a L := by
  induction n with
  | zero => simp [pathIntFrom]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, pathIntFrom_append, hL, ih]
    push_cast
    ring

/-- The winding number is constant on a preconnected set missing the trace. -/
theorem s20v_b_polyWinding_const {v : List ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hST : ∀ x ∈ S, x ∉ polyTrace v) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    polyWinding v y = polyWinding v x := by
  have hu : IsOpen {b | b ∉ polyTrace v ∧ polyWinding v b = polyWinding v x} := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    filter_upwards [(isOpen_compl_polyTrace v).mem_nhds hb.1, eventually_polyWinding_eq hb.1] with c hc hcb
    exact ⟨hc, hcb.trans hb.2⟩
  have hv : IsOpen {b | b ∉ polyTrace v ∧ polyWinding v b ≠ polyWinding v x} := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    filter_upwards [(isOpen_compl_polyTrace v).mem_nhds hb.1, eventually_polyWinding_eq hb.1] with c hc hcb
    exact ⟨hc, by rw [hcb]; exact hb.2⟩
  have hsub := hS.subset_left_of_subset_union hu hv (disjoint_left.2 fun b h1 h2 => h2.2 h1.2)
    (fun b hb => by
      by_cases h : polyWinding v b = polyWinding v x
      · exact Or.inl ⟨hST b hb, h⟩
      · exact Or.inr ⟨hST b hb, h⟩)
    ⟨x, hx, hST x hx, rfl⟩
  exact (hsub hy).2

/-- The construction behind `s20v_ext_loop`: a radial segment out, `n` square circuits turning by `ω = ±i`, and
the radial segment back. -/
theorem s20v_b_ext_loop_core {z d ω : ℂ} {t : ℝ} (ht : 0 ≤ t) (hd : t < ‖d‖) (hω : ω = I ∨ ω = -I) (n : ℕ) :
    ∃ l : List ℂ, SegsIn {ζ | t < ‖ζ - z‖} (z + d) l ∧ lastOf (z + d) l = z + d ∧
      ∀ w : ℂ, ‖w - z‖ ≤ t → polyWinding ((z + d) :: l) w = n * (4 * log ω) / (2 * π * I) := by
  have hωn : ‖ω‖ = 1 := by rcases hω with rfl | rfl <;> simp
  have hω4 : ω * (ω * (ω * (ω * d))) = d := by
    have h2 : ω * ω = -1 := by rcases hω with rfl | rfl <;> simp
    linear_combination (ω * ω - 1) * d * h2
  have hn1 : t < ‖ω * d‖ := by rwa [norm_mul, hωn, one_mul]
  have hn2 : t < ‖ω * (ω * d)‖ := by rwa [norm_mul, hωn, one_mul]
  have hn3 : t < ‖ω * (ω * (ω * d))‖ := by rwa [norm_mul, hωn, one_mul]
  obtain ⟨sq, hsqS, hsql, hsqI⟩ : ∃ sq : List ℂ, SegsIn {ζ | t < ‖ζ - z‖} (z + 2 * d) sq ∧
      lastOf (z + 2 * d) sq = z + 2 * d ∧ pathIntFrom (fun ζ => (ζ - z)⁻¹) (z + 2 * d) sq = 4 * log ω := by
    have hlast4 : segment ℝ (z + 2 * (ω * (ω * (ω * d)))) (z + 2 * d) ⊆ {ζ | t < ‖ζ - z‖} := by
      have h := s20v_b_seg_far (z := z) hω hn3
      rwa [hω4] at h
    have hlog4 : segIntegral (fun ζ => (ζ - z)⁻¹) (z + 2 * (ω * (ω * (ω * d)))) (z + 2 * d) = log ω := by
      have h := s20v_b_seg_log (z := z) ht hω hn3
      rwa [hω4] at h
    refine ⟨[z + 2 * (ω * d), z + 2 * (ω * (ω * d)), z + 2 * (ω * (ω * (ω * d))), z + 2 * d],
      ⟨s20v_b_seg_far hω hd, s20v_b_seg_far hω hn1, s20v_b_seg_far hω hn2, hlast4, trivial⟩, rfl, ?_⟩
    simp only [pathIntFrom]
    rw [s20v_b_seg_log ht hω hd, s20v_b_seg_log ht hω hn1, s20v_b_seg_log ht hω hn2, hlog4]
    ring
  have hS : SegsIn {ζ | t < ‖ζ - z‖} (z + d) ((z + 2 * d) :: ((List.replicate n sq).flatten ++ [z + d])) := by
    refine ⟨s20v_b_seg_radial hd, ?_⟩
    rw [segsIn_append, s20v_b_lastOf_rep hsql]
    refine ⟨s20v_b_segsIn_rep hsql hsqS n, ?_, trivial⟩
    rw [segment_symm]
    exact s20v_b_seg_radial hd
  have hlast : lastOf (z + d) ((z + 2 * d) :: ((List.replicate n sq).flatten ++ [z + d])) = z + d := by
    show lastOf (z + 2 * d) ((List.replicate n sq).flatten ++ [z + d]) = z + d
    rw [lastOf_append, s20v_b_lastOf_rep hsql]
    rfl
  have hPI : polyIntegral (fun ζ => (ζ - z)⁻¹) ((z + d) :: ((z + 2 * d) :: ((List.replicate n sq).flatten ++
      [z + d]))) = n * (4 * log ω) := by
    rw [polyIntegral_cons, hlast, segIntegral_self, add_zero]
    simp only [pathIntFrom]
    rw [pathIntFrom_append, s20v_b_lastOf_rep hsql, s20v_b_pathIntFrom_rep _ hsql, hsqI]
    simp only [pathIntFrom, add_zero]
    rw [segIntegral_symm _ (z + d) (z + 2 * d)]
    ring
  refine ⟨(z + 2 * d) :: ((List.replicate n sq).flatten ++ [z + d]), hS, hlast, fun w hw => ?_⟩
  have hT : ∀ x ∈ closedBall z t,
      x ∉ polyTrace ((z + d) :: ((z + 2 * d) :: ((List.replicate n sq).flatten ++ [z + d]))) := by
    intro x hx hxT
    have hq : t < ‖z + d - z‖ := by rwa [add_sub_cancel_left]
    have h := polyTrace_cons_subset hS (by rw [hlast, segment_same]; exact singleton_subset_iff.2 hq) hxT
    rw [mem_closedBall, dist_eq_norm] at hx
    exact not_lt.2 hx h
  have hwB : w ∈ closedBall z t := by rwa [mem_closedBall, dist_eq_norm]
  rw [s20v_b_polyWinding_const (convex_closedBall z t).isPreconnected hT (mem_closedBall_self ht) hwB,
    polyWinding, hPI]

/-- **Exterior loops of prescribed winding number.**  For `‖q - z‖ > t ≥ 0` and any `N : ℤ` there
is a closed polygon at `q`, inside `{t < ‖ζ - z‖}`, winding `N` times around every point of `closedBall z t`.

*Truth.* Pick `R₀ > max t ‖q - z‖` large and put `e := (q - z)/‖q - z‖`.  Go radially from `q` to `q* := z + R₀ e`
(the distance to `z` increases along the way), run `|N|` times around the square with vertices `z + iʲ R₀ e`
(`j = 0, …, 3`), reversed if `N < 0`, and return radially.  The sides of the square are at distance `R₀/√2 > t`
from `z`.  At `w = z`, each square edge contributes `log (±i) = ±iπ/2` and the two radial edges contribute
`log λ + log λ⁻¹ = 0` with `λ > 0`.  The winding number is constant on the convex set `closedBall z t`, which misses
the trace.  For `N = 0`, take `l = []`.

*Route/reuse.* `polyIntegral_inv_sub_eq_sum_log` (ConnectedComplement:548), `eventually_polyWinding_eq` (:622),
`exists_int_polyWinding` (:557), `segsIn_append` (:815), `lastOf_append` (:809). -/
theorem s20v_ext_loop {z q : ℂ} {t : ℝ} (ht : 0 ≤ t) (hq : t < ‖q - z‖) (N : ℤ) :
    ∃ l : List ℂ, SegsIn {ζ | t < ‖ζ - z‖} q l ∧ lastOf q l = q ∧
      ∀ w : ℂ, ‖w - z‖ ≤ t → polyWinding (q :: l) w = N := by
  obtain ⟨d, rfl⟩ : ∃ d, q = z + d := ⟨q - z, by ring⟩
  rw [add_sub_cancel_left] at hq
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · obtain ⟨l, h1, h2, h3⟩ := s20v_b_ext_loop_core (z := z) ht hq (Or.inl rfl) n
    refine ⟨l, h1, h2, fun w hw => ?_⟩
    rw [h3 w hw, log_I, div_eq_iff two_pi_I_ne_zero]
    push_cast
    ring
  · obtain ⟨l, h1, h2, h3⟩ := s20v_b_ext_loop_core (z := z) ht hq (Or.inr rfl) n
    refine ⟨l, h1, h2, fun w hw => ?_⟩
    rw [h3 w hw, log_neg_I, div_eq_iff two_pi_I_ne_zero]
    push_cast
    ring

/-- Telescoping along a polygonal path with an explicit primitive: if `G' = h` at every point of the open set `U`,
then `∫_{a, l} h = G (lastOf a l) - G a` for every path `a, l` whose segments lie in `U`. -/
theorem s20v_a_pathIntFrom_of_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {G h : ℂ → ℂ}
    (hG : ∀ ζ ∈ U, HasDerivAt G (h ζ) ζ) {a : ℂ} {l : List ℂ} (hl : SegsIn U a l) :
    pathIntFrom h a l = G (lastOf a l) - G a := by
  have hGd : DifferentiableOn ℂ G U := fun ζ hζ => (hG ζ hζ).differentiableAt.differentiableWithinAt
  have hcongr : ∀ {b : ℂ} {m : List ℂ}, SegsIn U b m → pathIntFrom h b m = pathIntFrom (deriv G) b m := by
    intro b m hm
    induction m generalizing b with
    | nil => rfl
    | cons c m ih =>
      simp only [pathIntFrom]
      rw [segIntegral_congr (fun ζ hζ => ((hG ζ (hm.1 hζ)).deriv).symm), ih hm.2]
  rw [hcongr hl]
  exact s20v_pathIntFrom_deriv hU hGd hl

/-- For `‖u‖ ≤ r/k`, `‖σ‖ ≤ 1/r` and `k > 1`: `‖σ u‖ ≤ 1/k`, `1 - 1/k ≤ ‖1 - σ u‖` and
`‖u/(1 - σ u)‖ ≤ r/(k - 1)`. -/
theorem s20v_a_term_le {u σ : ℂ} {r k : ℝ} (hr : 0 < r) (hk : 1 < k) (hu : ‖u‖ ≤ r / k)
    (hσ : ‖σ‖ ≤ 1 / r) :
    ‖σ * u‖ ≤ 1 / k ∧ 1 - 1 / k ≤ ‖1 - σ * u‖ ∧ ‖u / (1 - σ * u)‖ ≤ r / (k - 1) := by
  have hk0 : 0 < k := by linarith
  have hr0 : r ≠ 0 := hr.ne'
  have hk0' : k ≠ 0 := hk0.ne'
  have hσu : ‖σ * u‖ ≤ 1 / k := by
    rw [norm_mul]
    calc ‖σ‖ * ‖u‖ ≤ 1 / r * (r / k) := mul_le_mul hσ hu (norm_nonneg _) (by positivity)
      _ = 1 / k := by field_simp
  have h1 : 1 - 1 / k ≤ ‖1 - σ * u‖ := by
    have := norm_sub_norm_le (1 : ℂ) (σ * u)
    rw [norm_one] at this
    linarith
  have hk1 : 0 < 1 - 1 / k := by
    rw [sub_pos, div_lt_one hk0]
    exact hk
  refine ⟨hσu, h1, ?_⟩
  have hpos : 0 < ‖1 - σ * u‖ := lt_of_lt_of_le hk1 h1
  rw [norm_div, div_le_div_iff₀ hpos (by linarith)]
  have h2 : r * (1 - 1 / k) ≤ r * ‖1 - σ * u‖ := mul_le_mul_of_nonneg_left h1 hr.le
  have h3 : r * (1 - 1 / k) = r / k * (k - 1) := by field_simp
  have h4 : ‖u‖ * (k - 1) ≤ r / k * (k - 1) := mul_le_mul_of_nonneg_right hu (by linarith)
  linarith

/-- **The exterior bound (20.23).**  For `k ≥ 6`, `w₁, w₂ ∈ closedBall z (r/k)` and a polygonal
path from `p` to `p'` inside `{r/2 < ‖ζ - z‖}`, where `‖p - z‖, ‖p' - z‖ ≥ r`, the integral of
`(ζ - w₁)⁻¹ - (ζ - w₂)⁻¹` along the path is at most `4/(k - 1)` in norm.

*Truth.* Put `Q ζ := (ζ - w₁)/(ζ - w₂)`.  On the region, `‖Q ζ - 1‖ = ‖w₂ - w₁‖/‖ζ - w₂‖ < (2r/k)/(r/2 - r/k) ≤ 1`, so
`log ∘ Q` is a primitive of the integrand there and the integral equals `log Q p' - log Q p`.  At the endpoints,
`‖Q - 1‖ ≤ 2/(k - 1) ≤ 2/5`, so this number has norm `≤ 2 · 0.52`.

It is congruent mod `2πi` to the book's quantity.  Put `ζ* := 1/(ζ - z)` and `Q* ζ* := (ζ* - w₁*)/(ζ* - w₂*)`.
Then `Q p'/Q p = Q* p'*/Q* p*` (Möbius invariance of the cross-ratio), and the latter is the exponential of the
integral over the segment `[p*, p'*] ⊆ closedBall 0 (1/r)`.  The segment has length `≤ 2/r`, and its integrand is at
most `2r/(k - 1)` since `‖w*‖ ≥ k/r`.  So the segment integral has norm `≤ 4/(k - 1) ≤ 4/5`.  Both numbers are
small, so they are equal.  If `w_j = z`, then `w_j* = ∞` and its term drops.

The direct bound `‖X - 1‖ ≤ 4/(k-1) + 4/(k-1)²` on the cross-ratio `X` is too weak at `k = 6`.

*Route/reuse.* `s20v_pathIntFrom_deriv` (this block) with `G := log ∘ Q`, `segIntegral_inv_sub_eq_log`
(ConnectedComplement:498), `norm_segIntegral_le` (:240). -/
theorem s20v_ext_bound {z w₁ w₂ p : ℂ} {r k : ℝ} (hr : 0 < r) (hk : 6 ≤ k) (hw₁ : ‖w₁ - z‖ ≤ r / k)
    (hw₂ : ‖w₂ - z‖ ≤ r / k) (hp : r ≤ ‖p - z‖) {l : List ℂ} (hl : SegsIn {ζ | r / 2 < ‖ζ - z‖} p l)
    (hle : r ≤ ‖lastOf p l - z‖) :
    ‖pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p l‖ ≤ 4 / (k - 1) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 1 < k := by linarith
  have hrk0 : 0 < r / k := div_pos hr hk0
  have hrk : r / k ≤ r / 6 := div_le_div_of_nonneg_left hr.le (by norm_num) hk
  have hRo : IsOpen {ζ : ℂ | r / 2 < ‖ζ - z‖} := isOpen_lt continuous_const (by fun_prop)
  have hdist : ∀ ζ : ℂ, r / 2 < ‖ζ - z‖ → ∀ w : ℂ, ‖w - z‖ ≤ r / k → r / 2 - r / k < ‖ζ - w‖ := by
    intro ζ hζ w hw
    have h1 := norm_sub_norm_le (ζ - z) (w - z)
    rw [show ζ - z - (w - z) = ζ - w by ring] at h1
    linarith
  have hw12 : ‖w₂ - w₁‖ ≤ 2 * (r / k) := by
    have h1 := norm_sub_le (w₂ - z) (w₁ - z)
    rw [show w₂ - z - (w₁ - z) = w₂ - w₁ by ring] at h1
    linarith
  have h3 : 2 * (r / k) ≤ r / 2 - r / k := by linarith
  -- the primitive `log ((ζ - w₁)/(ζ - w₂))` on the region
  have hG : ∀ ζ ∈ {ζ : ℂ | r / 2 < ‖ζ - z‖},
      HasDerivAt (fun ζ => log ((ζ - w₁) / (ζ - w₂))) ((ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) ζ := by
    intro ζ hζ
    have hd₁ := hdist ζ hζ w₁ hw₁
    have hd₂ := hdist ζ hζ w₂ hw₂
    have hne₁ : ζ - w₁ ≠ 0 := norm_pos_iff.1 (by linarith)
    have hne₂ : ζ - w₂ ≠ 0 := norm_pos_iff.1 (by linarith)
    have hslit : (ζ - w₁) / (ζ - w₂) ∈ slitPlane := by
      have heq : (ζ - w₁) / (ζ - w₂) = 1 + (w₂ - w₁) / (ζ - w₂) := by
        rw [div_eq_iff hne₂, add_mul, div_mul_cancel₀ _ hne₂]
        ring
      rw [heq]
      apply mem_slitPlane_of_norm_lt_one
      rw [norm_div, div_lt_one (norm_pos_iff.2 hne₂)]
      linarith
    have hQ : HasDerivAt (fun y => (y - w₁) / (y - w₂)) ((1 * (ζ - w₂) - (ζ - w₁) * 1) / (ζ - w₂) ^ 2) ζ :=
      ((hasDerivAt_id' ζ).sub_const w₁).div ((hasDerivAt_id' ζ).sub_const w₂) hne₂
    refine (hQ.clog hslit).congr_deriv ?_
    field_simp
  rw [s20v_a_pathIntFrom_of_hasDerivAt hRo hG hl]
  -- the inverted coordinate `σ = 1/(ζ - z)`
  have hpz0 : p - z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hp'z0 : lastOf p l - z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hsub : ∀ ζ w : ℂ, ζ - z ≠ 0 → 1 - (ζ - z)⁻¹ * (w - z) = (ζ - w) / (ζ - z) := by
    intro ζ w hζ
    have hinv : (ζ - z)⁻¹ * (ζ - z) = 1 := inv_mul_cancel₀ hζ
    rw [eq_div_iff hζ]
    linear_combination (-(w - z)) * hinv
  have hconv : ∀ ζ : ℂ, ζ - z ≠ 0 →
      (1 - (ζ - z)⁻¹ * (w₁ - z)) / (1 - (ζ - z)⁻¹ * (w₂ - z)) = (ζ - w₁) / (ζ - w₂) := by
    intro ζ hζ
    rw [hsub ζ w₁ hζ, hsub ζ w₂ hζ, div_div_div_cancel_right₀ hζ]
  have hball : ∀ ζ : ℂ, r ≤ ‖ζ - z‖ → (ζ - z)⁻¹ ∈ closedBall (0 : ℂ) (1 / r) := by
    intro ζ hζ
    rw [mem_closedBall_zero_iff, norm_inv, one_div]
    exact inv_anti₀ hr hζ
  rw [← hconv _ hp'z0, ← hconv _ hpz0]
  have hF : ∀ σ ∈ closedBall (0 : ℂ) (1 / r),
      HasDerivWithinAt (fun σ => log ((1 - σ * (w₁ - z)) / (1 - σ * (w₂ - z))))
        ((w₂ - z) / (1 - σ * (w₂ - z)) - (w₁ - z) / (1 - σ * (w₁ - z))) (closedBall (0 : ℂ) (1 / r)) σ := by
    intro σ hσ
    rw [mem_closedBall_zero_iff] at hσ
    obtain ⟨hσu₁, h1₁, -⟩ := s20v_a_term_le hr hk1 hw₁ hσ
    obtain ⟨hσu₂, h1₂, -⟩ := s20v_a_term_le hr hk1 hw₂ hσ
    have hk' : 0 < 1 - 1 / k := by
      rw [sub_pos, div_lt_one hk0]
      exact hk1
    have hne₁ : 1 - σ * (w₁ - z) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hk' h1₁)
    have hne₂ : 1 - σ * (w₂ - z) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hk' h1₂)
    have hslit : (1 - σ * (w₁ - z)) / (1 - σ * (w₂ - z)) ∈ slitPlane := by
      have heq : (1 - σ * (w₁ - z)) / (1 - σ * (w₂ - z))
          = 1 + (σ * (w₂ - z) - σ * (w₁ - z)) / (1 - σ * (w₂ - z)) := by
        rw [div_eq_iff hne₂, add_mul, div_mul_cancel₀ _ hne₂]
        ring
      rw [heq]
      apply mem_slitPlane_of_norm_lt_one
      rw [norm_div, div_lt_one (norm_pos_iff.2 hne₂)]
      have h4 := norm_sub_le (σ * (w₂ - z)) (σ * (w₁ - z))
      have hk3 : 3 * (1 / k) < 1 := by
        rw [mul_one_div, div_lt_one hk0]
        linarith
      linarith
    have hd : HasDerivAt (fun y => (1 - y * (w₁ - z)) / (1 - y * (w₂ - z)))
        (((0 - 1 * (w₁ - z)) * (1 - σ * (w₂ - z)) - (1 - σ * (w₁ - z)) * (0 - 1 * (w₂ - z))) /
          (1 - σ * (w₂ - z)) ^ 2) σ :=
      ((hasDerivAt_const σ (1 : ℂ)).sub ((hasDerivAt_id' σ).mul_const (w₁ - z))).div
      ((hasDerivAt_const σ (1 : ℂ)).sub ((hasDerivAt_id' σ).mul_const (w₂ - z))) hne₂
    refine ((hd.clog hslit).congr_deriv ?_).hasDerivWithinAt
    generalize 1 - σ * (w₁ - z) = a₁ at hne₁ ⊢
    generalize 1 - σ * (w₂ - z) = a₂ at hne₂ ⊢
    field_simp
    ring
  have hFb : ∀ σ ∈ closedBall (0 : ℂ) (1 / r),
      ‖(w₂ - z) / (1 - σ * (w₂ - z)) - (w₁ - z) / (1 - σ * (w₁ - z))‖ ≤ 2 * r / (k - 1) := by
    intro σ hσ
    rw [mem_closedBall_zero_iff] at hσ
    have hb₁ := (s20v_a_term_le hr hk1 hw₁ hσ).2.2
    have hb₂ := (s20v_a_term_le hr hk1 hw₂ hσ).2.2
    calc _ ≤ ‖(w₂ - z) / (1 - σ * (w₂ - z))‖ + ‖(w₁ - z) / (1 - σ * (w₁ - z))‖ := norm_sub_le _ _
      _ ≤ r / (k - 1) + r / (k - 1) := add_le_add hb₂ hb₁
      _ = 2 * r / (k - 1) := by ring
  have hmvt := (convex_closedBall (0 : ℂ) (1 / r)).norm_image_sub_le_of_norm_hasDerivWithin_le hF hFb
    (hball p hp) (hball _ hle)
  have hlen : ‖(lastOf p l - z)⁻¹ - (p - z)⁻¹‖ ≤ 2 / r := by
    have h1 := norm_sub_le (lastOf p l - z)⁻¹ (p - z)⁻¹
    have h2 := mem_closedBall_zero_iff.1 (hball p hp)
    have h3 := mem_closedBall_zero_iff.1 (hball _ hle)
    calc _ ≤ ‖(lastOf p l - z)⁻¹‖ + ‖(p - z)⁻¹‖ := h1
      _ ≤ 1 / r + 1 / r := add_le_add h3 h2
      _ = 2 / r := by ring
  have hC : 0 ≤ 2 * r / (k - 1) := div_nonneg (by positivity) (by linarith)
  calc _ ≤ 2 * r / (k - 1) * ‖(lastOf p l - z)⁻¹ - (p - z)⁻¹‖ := hmvt
    _ ≤ 2 * r / (k - 1) * (2 / r) := mul_le_mul_of_nonneg_left hlen hC
    _ = 4 / (k - 1) := by
      have hk1' : k - 1 ≠ 0 := by linarith
      field_simp
      ring

/-- The end point of a polygonal path in `U` starting in `U` lies in `U`. -/
theorem s20v_c_lastOf_mem {U : Set ℂ} : ∀ {a : ℂ} {l : List ℂ}, a ∈ U → SegsIn U a l → lastOf a l ∈ U := by
  intro a l ha hl
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    simp only [lastOf]
    exact ih (hl.1 (right_mem_segment ℝ a b)) hl.2

/-- Path integrals along a polygonal path in `U` only see the values of the integrand on `U`. -/
theorem s20v_c_pathIntFrom_congr {U : Set ℂ} {f g : ℂ → ℂ} (hfg : EqOn f g U) :
    ∀ {a : ℂ} {l : List ℂ}, SegsIn U a l → pathIntFrom f a l = pathIntFrom g a l := by
  intro a l hl
  induction l generalizing a with
  | nil => simp [pathIntFrom]
  | cons b l ih =>
    simp only [pathIntFrom]
    rw [segIntegral_congr (hfg.mono hl.1), ih hl.2]

/-- The Schwarzian of `exp (c H)` for a primitive `H` of `(ζ - w₁)⁻¹ - (ζ - w₂)⁻¹`: the map is analytic with
`f' = c H' f`, and `S_f = ½ (1 - c²) H'²` (the book's (20.21); `S_H = ½ H'²` because `exp H` is Möbius). -/
theorem s20v_c_schwarzian {D : Set ℂ} (hD : IsOpen D) {w₁ w₂ c : ℂ} (hw₁ : w₁ ∉ D) (hw₂ : w₂ ∉ D)
    (hw : w₁ ≠ w₂) (hc : c ≠ 0) {H : ℂ → ℂ} (hH : ∀ z ∈ D, HasDerivAt H ((z - w₁)⁻¹ - (z - w₂)⁻¹) z)
    {ζ : ℂ} (hζ : ζ ∈ D) :
    AnalyticAt ℂ (fun z => exp (c * H z)) ζ ∧
      deriv (fun z => exp (c * H z)) ζ = c * ((ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) * exp (c * H ζ) ∧
      schwarzian (fun z => exp (c * H z)) ζ = (1 - c ^ 2) / 2 * ((ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) ^ 2 := by
  set f : ℂ → ℂ := fun z => exp (c * H z) with hfdef
  have hu : ∀ z ∈ D, z - w₁ ≠ 0 := fun z hz h => hw₁ (sub_eq_zero.1 h ▸ hz)
  have hv : ∀ z ∈ D, z - w₂ ≠ 0 := fun z hz h => hw₂ (sub_eq_zero.1 h ▸ hz)
  have hf1 : ∀ z ∈ D, HasDerivAt f (c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) * f z) z := by
    intro z hz
    have h1 := ((hH z hz).const_mul c).cexp
    convert h1 using 1
    simp only [hfdef]
    ring
  have hfd : DifferentiableOn ℂ f D := fun z hz => (hf1 z hz).differentiableAt.differentiableWithinAt
  have han : ∀ z ∈ D, AnalyticAt ℂ f z := fun z hz => hfd.analyticAt (hD.mem_nhds hz)
  have hd1 : ∀ z ∈ D, deriv f z = c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) * f z := fun z hz => (hf1 z hz).deriv
  have hA : ∀ z ∈ D, HasDerivAt (fun y => (y - w₁)⁻¹) (-(z - w₁)⁻¹ ^ 2) z := by
    intro z hz
    convert ((hasDerivAt_id' z).sub_const w₁).fun_inv (hu z hz) using 1
    rw [inv_pow]
    ring
  have hB : ∀ z ∈ D, HasDerivAt (fun y => (y - w₂)⁻¹) (-(z - w₂)⁻¹ ^ 2) z := by
    intro z hz
    convert ((hasDerivAt_id' z).sub_const w₂).fun_inv (hv z hz) using 1
    rw [inv_pow]
    ring
  have hF1d : ∀ z ∈ D, HasDerivAt (fun y => c * ((y - w₁)⁻¹ - (y - w₂)⁻¹) * f y)
      (c * ((-(z - w₁)⁻¹ ^ 2 - -(z - w₂)⁻¹ ^ 2) * f z +
        ((z - w₁)⁻¹ - (z - w₂)⁻¹) * (c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) * f z))) z := by
    intro z hz
    have h1 := (((hA z hz).fun_sub (hB z hz)).fun_mul (hf1 z hz)).const_mul c
    convert h1 using 1
    funext y
    ring
  have hd2 : ∀ z ∈ D, deriv (deriv f) z = c * ((-(z - w₁)⁻¹ ^ 2 - -(z - w₂)⁻¹ ^ 2) * f z +
      ((z - w₁)⁻¹ - (z - w₂)⁻¹) * (c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) * f z)) := by
    intro z hz
    have heq : deriv f =ᶠ[𝓝 z] fun y => c * ((y - w₁)⁻¹ - (y - w₂)⁻¹) * f y := by
      filter_upwards [hD.mem_nhds hz] with y hy using hd1 y hy
    rw [heq.deriv_eq]
    exact (hF1d z hz).deriv
  have hratio : ∀ z ∈ D, deriv (deriv f) z / deriv f z =
      -((z - w₁)⁻¹ + (z - w₂)⁻¹) + c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) := by
    intro z hz
    have hne : c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) * f z ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero hc ?_) (exp_ne_zero _)
      intro h
      apply hw
      have h2 := inv_inj.1 (sub_eq_zero.1 h)
      linear_combination -h2
    rw [hd2 z hz, hd1 z hz, div_eq_iff hne]
    ring
  have hR : (fun w => deriv (deriv f) w / deriv f w) =ᶠ[𝓝 ζ]
      fun z => -((z - w₁)⁻¹ + (z - w₂)⁻¹) + c * ((z - w₁)⁻¹ - (z - w₂)⁻¹) := by
    filter_upwards [hD.mem_nhds hζ] with y hy using hratio y hy
  have hRd : HasDerivAt (fun z => -((z - w₁)⁻¹ + (z - w₂)⁻¹) + c * ((z - w₁)⁻¹ - (z - w₂)⁻¹))
      (-(-(ζ - w₁)⁻¹ ^ 2 + -(ζ - w₂)⁻¹ ^ 2) + c * (-(ζ - w₁)⁻¹ ^ 2 - -(ζ - w₂)⁻¹ ^ 2)) ζ :=
    ((hA ζ hζ).fun_add (hB ζ hζ)).fun_neg.fun_add (((hA ζ hζ).fun_sub (hB ζ hζ)).const_mul c)
  refine ⟨han ζ hζ, hd1 ζ hζ, ?_⟩
  rw [schwarzian_of_analyticAt (han ζ hζ)]
  unfold schwarzianHol
  rw [hR.deriv_eq, hRd.deriv, hratio ζ hζ]
  ring

/-- The constants of (20.22): if `Δ = 2πi m + E` with `m ≠ 0`, `‖E‖ ≤ 4a/15` and `0 < a ≤ 3`, then `‖Δ‖ ≥ 5`
and `c := 2πi m/Δ` has `8 ‖1 - c²‖ < a` (in fact `≤ 0.9216 a`). -/
theorem s20v_c_const {Δ E : ℂ} {m : ℤ} {a : ℝ} (hm : m ≠ 0) (ha0 : 0 < a) (ha3 : a ≤ 3)
    (hE : ‖E‖ ≤ 4 * a / 15) (hΔ : Δ = 2 * π * I * m + E) :
    5 ≤ ‖Δ‖ ∧ 8 * ‖1 - (2 * π * I * m / Δ) ^ 2‖ < a := by
  have hpi := Real.pi_gt_three
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm
  have hnm : ‖2 * π * I * (m : ℂ)‖ = 2 * π * |(m : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast]
    simp [abs_of_pos Real.pi_pos]
  have h1 : ‖2 * π * I * (m : ℂ)‖ ≤ ‖Δ‖ + ‖E‖ := by
    calc ‖2 * π * I * (m : ℂ)‖ = ‖Δ - E‖ := by rw [hΔ, add_sub_cancel_right]
      _ ≤ ‖Δ‖ + ‖E‖ := norm_sub_le _ _
  have hΔ5 : 5 ≤ ‖Δ‖ := by
    rw [hnm] at h1
    nlinarith [mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hΔ0 : Δ ≠ 0 := fun h => by rw [h, norm_zero] at hΔ5; norm_num at hΔ5
  refine ⟨hΔ5, ?_⟩
  set c : ℂ := 2 * π * I * m / Δ with hcdef
  have hc1 : c - 1 = -E / Δ := by
    rw [hcdef, div_sub_one hΔ0]
    congr 1
    rw [hΔ]
    ring
  have hε : ‖c - 1‖ ≤ 4 * a / 75 := by
    rw [hc1, norm_div, norm_neg, div_le_iff₀ (by linarith)]
    nlinarith
  have hsq : ‖1 - c ^ 2‖ ≤ ‖c - 1‖ * (‖c - 1‖ + 2) := by
    rw [show 1 - c ^ 2 = -((c - 1) * ((c - 1) + 2)) by ring, norm_neg, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by simp)) (norm_nonneg _)
  have hε0 := norm_nonneg (c - 1)
  nlinarith [mul_le_mul hε hε hε0 (by positivity : (0 : ℝ) ≤ 4 * a / 75)]

/-- **The analytic half of Theorem 20.4, (20.21)–(20.22).**  Suppose `D` is `a`-Schwarz, `w₁` and
`w₂` lie outside `D`, `γ = β + c` is a closed polygon with `β` in `D` from `p₁` to `p₂`, and `γ` winds differently
around `w₁` and `w₂`.  Then the `c`-part of `∮_γ ((ζ - w₁)⁻¹ - (ζ - w₂)⁻¹)` has norm greater than `4a/15`.

*Truth.* This is the book's (20.21)–(20.22) argument.  Take `H` a primitive of `h := (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹` on the
simply connected `D`.
- Split `∮_γ h = 2πi (n₁ - n₂)` (the definition of `polyWinding`, integer values) into its `β` and `c` parts.  This
  gives `H p₁ - H p₂ = 2πi m + E`, with `m := n₂ - n₁ ≠ 0` and `E := ∫_c h`, `‖E‖ ≤ 4a/15 ≤ 4/5` (`a ≤ 3`).
- Put `c₀ := 2πi m/(H p₁ - H p₂)`.  Then `‖c₀ - 1‖ ≤ 0.049 a` and `‖c₀² - 1‖ ≤ 0.105 a`.
- `f := exp (c₀ H)` is holomorphic with `f' = c₀ H' f ≠ 0`, so it is locally univalent.
- `f p₁ = f p₂` with `p₁ ≠ p₂`: if `p₁ = p₂`, then `‖2πi m‖ ≤ 4/5`, which is false.
- `S_f = ½ (1 - c₀²) H'²`, and Koebe gives `‖H' ζ‖ ≤ 4 η_D(ζ)`.  So `‖S_f‖_D ≤ 8 ‖c₀² - 1‖ < a`.
- The Schwarz property then makes `f` univalent, which contradicts `f p₁ = f p₂`.

*Route/reuse.*
- `RMT.exists_primitive_of_simplyConnected` (RiemannMapping:1272); `s20v_pathIntFrom_deriv` with `segIntegral_congr`
  (ConnectedComplement:163) for `∫_β h = H p₂ - H p₁`; `polyIntegral_cons` (:822), `exists_int_polyWinding` (:557).
- `t2020_not_isSchwarz_of_three_lt` (S20:5992) for `a ≤ 3`.
- `t203_density_ge` (S20:3041, Koebe (20.14)) with a Riemann map from `RMT.exists_riemannMap` (RiemannMapping:1230).
- The Schwarzian computation as in `neh_schwarzian_f` (S20:721) and `schwarzian_of_analyticAt` (S19:43); local
  univalence as in `neh_isLocUnivMero_f` (S20:755); the contradiction pattern of `thm20_1_not_isSchwarz` (S20:920). -/
theorem s20v_analytic {D : Set ℂ} {a : ℝ} (hSD : IsSchwarzDomain D a) {w₁ w₂ p₁ p₂ : ℂ} (hw₁ : w₁ ∉ D)
    (hw₂ : w₂ ∉ D) (hp₁ : p₁ ∈ D) {lβ lc : List ℂ} (hβ : SegsIn D p₁ lβ) (hβe : lastOf p₁ lβ = p₂)
    (hce : lastOf p₂ lc = p₁) (hw₁γ : w₁ ∉ polyTrace (p₁ :: (lβ ++ lc)))
    (hw₂γ : w₂ ∉ polyTrace (p₁ :: (lβ ++ lc)))
    (hwind : polyWinding (p₁ :: (lβ ++ lc)) w₁ ≠ polyWinding (p₁ :: (lβ ++ lc)) w₂)
    (hbound : ‖pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ lc‖ ≤ 4 * a / 15) : False := by
  obtain ⟨hD, ha0, hall⟩ := hSD
  have ha3 : a ≤ 3 := not_lt.1 fun h => t2020_not_isSchwarz_of_three_lt h ⟨hD, ha0, hall⟩
  have hsc : SimplyConnectedSpace D := hD.2.2.1
  have hu : ∀ z ∈ D, z - w₁ ≠ 0 := fun z hz h => hw₁ (sub_eq_zero.1 h ▸ hz)
  have hv : ∀ z ∈ D, z - w₂ ≠ 0 := fun z hz h => hw₂ (sub_eq_zero.1 h ▸ hz)
  have hw12 : w₁ ≠ w₂ := fun h => hwind (by rw [h])
  have hhd : DifferentiableOn ℂ (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) D := fun z hz =>
    (((differentiableAt_id.sub_const w₁).inv (hu z hz)).sub
      ((differentiableAt_id.sub_const w₂).inv (hv z hz))).differentiableWithinAt
  obtain ⟨H, hHd, hHder⟩ := RMT.exists_primitive_of_simplyConnected hD.1 hD.2.1 hhd
  have hH : ∀ z ∈ D, HasDerivAt H ((z - w₁)⁻¹ - (z - w₂)⁻¹) z := by
    intro z hz
    have h1 := (hHd.differentiableAt (hD.1.mem_nhds hz)).hasDerivAt
    rwa [hHder z hz] at h1
  have hp₂ : p₂ ∈ D := hβe ▸ s20v_c_lastOf_mem hp₁ hβ
  -- the winding numbers are integers
  obtain ⟨n₁, hn₁⟩ := exists_int_polyWinding hw₁γ
  obtain ⟨n₂, hn₂⟩ := exists_int_polyWinding hw₂γ
  have hn : n₂ - n₁ ≠ 0 := sub_ne_zero.2 fun h => hwind (by rw [hn₁, hn₂, h])
  have hI : ∀ (w : ℂ) (n : ℤ), polyWinding (p₁ :: (lβ ++ lc)) w = n →
      polyIntegral (fun z => (z - w)⁻¹) (p₁ :: (lβ ++ lc)) = 2 * π * I * n := by
    intro w n hwn
    unfold polyWinding at hwn
    rw [div_eq_iff two_pi_I_ne_zero] at hwn
    rw [hwn]
    ring
  have hcont : ∀ w, w ∉ polyTrace (p₁ :: (lβ ++ lc)) →
      ContinuousOn (fun z => (z - w)⁻¹) (polyTrace (p₁ :: (lβ ++ lc))) := fun w hw =>
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
      sub_ne_zero.2 fun h => hw ((show z = w from h) ▸ hz)
  have hIh : polyIntegral (fun z => (z - w₁)⁻¹ - (z - w₂)⁻¹) (p₁ :: (lβ ++ lc)) = 2 * π * I * (n₁ - n₂) := by
    rw [polyIntegral_sub (hcont w₁ hw₁γ) (hcont w₂ hw₂γ), hI w₁ n₁ hn₁, hI w₂ n₂ hn₂]
    ring
  -- the split `∮_γ h = ∫_β h + ∫_c h = (H p₂ - H p₁) + E`
  have hsplit : polyIntegral (fun z => (z - w₁)⁻¹ - (z - w₂)⁻¹) (p₁ :: (lβ ++ lc)) =
      (H p₂ - H p₁) + pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ lc := by
    rw [polyIntegral_cons, pathIntFrom_append, lastOf_append, hβe, hce, segIntegral_self, add_zero]
    congr 1
    rw [s20v_c_pathIntFrom_congr (g := deriv H) (fun z hz => (hHder z hz).symm) hβ,
      s20v_pathIntFrom_deriv hD.1 hHd hβ, hβe]
  have hΔ : H p₁ - H p₂ = 2 * π * I * ((n₂ - n₁ : ℤ) : ℂ) +
      pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ lc := by
    push_cast
    linear_combination -(hsplit.symm.trans hIh)
  obtain ⟨hΔ5, hcst⟩ := s20v_c_const hn ha0 ha3 hbound hΔ
  have hΔ0 : H p₁ - H p₂ ≠ 0 := fun h => by rw [h, norm_zero] at hΔ5; norm_num at hΔ5
  set c₀ : ℂ := 2 * π * I * ((n₂ - n₁ : ℤ) : ℂ) / (H p₁ - H p₂) with hc₀def
  have hc₀ : c₀ ≠ 0 := div_ne_zero (mul_ne_zero two_pi_I_ne_zero (Int.cast_ne_zero.2 hn)) hΔ0
  have hS := fun z (hz : z ∈ D) => s20v_c_schwarzian hD.1 hw₁ hw₂ hw12 hc₀ hH hz
  have hh0 : ∀ z ∈ D, (z - w₁)⁻¹ - (z - w₂)⁻¹ ≠ 0 := by
    intro z hz h
    apply hw12
    have h2 := inv_inj.1 (sub_eq_zero.1 h)
    linear_combination -h2
  have hloc : IsLocUnivMero (fun z => exp (c₀ * H z)) D := by
    refine ⟨fun z hz => (hS z hz).1.meromorphicAt, fun z hz => Or.inl ⟨(hS z hz).1, ?_⟩⟩
    rw [(hS z hz).2.1]
    exact mul_ne_zero (mul_ne_zero hc₀ (hh0 z hz)) (exp_ne_zero _)
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hD
  have hpt : ∀ z ∈ D, ‖schwarzian (fun z => exp (c₀ * H z)) z‖ / poincareDensity D z ^ 2 ≤
      8 * ‖1 - c₀ ^ 2‖ := by
    intro z hz
    have hη1 := t203_density_ge hD.1 hφ hz hw₁
    have hη2 := t203_density_ge hD.1 hφ hz hw₂
    have hd1 : 0 < ‖w₁ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hw₁ (h ▸ hz))
    have hd2 : 0 < ‖w₂ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hw₂ (h ▸ hz))
    have hη : 0 < poincareDensity D z := lt_of_lt_of_le (div_pos one_pos (mul_pos two_pos hd1)) hη1
    have hA : ‖(z - w₁)⁻¹‖ ≤ 2 * poincareDensity D z := by
      rw [norm_inv, norm_sub_rev, ← one_div, div_le_iff₀ hd1]
      rw [div_le_iff₀ (mul_pos two_pos hd1)] at hη1
      linarith
    have hB : ‖(z - w₂)⁻¹‖ ≤ 2 * poincareDensity D z := by
      rw [norm_inv, norm_sub_rev, ← one_div, div_le_iff₀ hd2]
      rw [div_le_iff₀ (mul_pos two_pos hd2)] at hη2
      linarith
    have hh : ‖(z - w₁)⁻¹ - (z - w₂)⁻¹‖ ≤ 4 * poincareDensity D z :=
      (norm_sub_le _ _).trans (by linarith)
    rw [(hS z hz).2.2, norm_mul, norm_pow, div_le_iff₀ (pow_pos hη 2)]
    have hK : ‖(1 - c₀ ^ 2) / 2‖ = ‖1 - c₀ ^ 2‖ / 2 := by
      rw [norm_div]
      norm_num
    rw [hK]
    have hh2 : ‖(z - w₁)⁻¹ - (z - w₂)⁻¹‖ ^ 2 ≤ (4 * poincareDensity D z) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hh 2
    have hK0 := norm_nonneg (1 - c₀ ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left hh2 hK0]
  have hnorm : schwarzianNorm (fun z => exp (c₀ * H z)) D < ENNReal.ofReal a :=
    lt_of_le_of_lt (iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (hpt z hz))
      ((ENNReal.ofReal_lt_ofReal_iff ha0).2 hcst)
  have hU := hall _ hloc hnorm
  have hfe : exp (c₀ * H p₁) = exp (c₀ * H p₂) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n₂ - n₁, ?_⟩
    have hkey : c₀ * (H p₁ - H p₂) = 2 * π * I * ((n₂ - n₁ : ℤ) : ℂ) := div_mul_cancel₀ _ hΔ0
    linear_combination hkey
  have hp : p₁ = p₂ := hU.2.1 ⟨hp₁, (hS p₁ hp₁).1⟩ ⟨hp₂, (hS p₂ hp₂).1⟩ hfe
  exact hΔ0 (by rw [hp, sub_self])

/-- Case (i) reduction (probe `h21u2_ps_layer`): if `p₁`, `p₂ ∈ D ∩ ball z₀ ρ` are not joined in `D ∩ ball z₀ ρ`,
two points of `ℂ ∖ D` outside `ball z₀ ρ` have different winding numbers for `β + [p₂, p₁]` (by `s20v_ps` and a far
point of the unbounded complement, where the winding number is `0`). -/
theorem s20v_case_i_windings {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) {z₀ p₁ p₂ : ℂ} {ρ : ℝ}
    (hp₁ : p₁ ∈ D ∩ ball z₀ ρ) (hp₂ : p₂ ∈ D ∩ ball z₀ ρ) (hsep : ¬ JoinedIn (D ∩ ball z₀ ρ) p₁ p₂)
    {lβ : List ℂ} (hβ : SegsIn D p₁ lβ) (hβe : lastOf p₁ lβ = p₂) :
    ∃ w₁ w₂, w₁ ∉ D ∧ w₂ ∉ D ∧ ρ ≤ ‖w₁ - z₀‖ ∧ ρ ≤ ‖w₂ - z₀‖ ∧
      polyWinding (p₁ :: (lβ ++ [p₁])) w₁ ≠ polyWinding (p₁ :: (lβ ++ [p₁])) w₂ := by
  have hc : SegsIn (ball z₀ ρ) p₂ [p₁] :=
    ⟨(convex_ball z₀ ρ).segment_subset hp₂.2 hp₁.2, trivial⟩
  obtain ⟨w₁, hw₁D, hw₁B, hw₁⟩ := s20v_ps hD.1 isOpen_ball hp₁ hp₂ hsep hβ hβe hc rfl
  obtain ⟨R, hR⟩ := exists_polyWinding_eq_zero_of_norm_gt (p₁ :: (lβ ++ [p₁]))
  obtain ⟨w₂, hw₂D, hw₂R⟩ := s20v_compl_unbounded hD (max R (‖z₀‖ + ρ))
  refine ⟨w₁, w₂, hw₁D, hw₂D, ?_, ?_, ?_⟩
  · simpa [mem_ball, dist_eq_norm] using hw₁B
  · have h1 : ‖z₀‖ + ρ < ‖w₂‖ := lt_of_le_of_lt (le_max_right _ _) hw₂R
    have h2 : ‖w₂‖ ≤ ‖w₂ - z₀‖ + ‖z₀‖ := by
      simpa using norm_add_le (w₂ - z₀) z₀
    linarith
  · rw [hR w₂ (lt_of_le_of_lt (le_max_left _ _) hw₂R)]
    exact hw₁

/-- Condition (i) of `k`-local connectivity for an `a`-Schwarz domain, `k = 1 + 15/a`: `s20v_case_i_windings`
with `ρ = k r`, the segment bound `‖∫_[p₂, p₁] ...‖ ≤ 2r · 2/((k - 1) r)` of (20.22), and `s20v_analytic`. -/
theorem s20v_case_i {D : Set ℂ} {a : ℝ} (hSD : IsSchwarzDomain D a) {z : ℂ} {r : ℝ} (hr : 0 < r) {p₁ p₂ : ℂ}
    (hp₁ : p₁ ∈ D ∩ closedBall z r) (hp₂ : p₂ ∈ D ∩ closedBall z r) :
    JoinedIn (D ∩ closedBall z ((1 + 15 / a) * r)) p₁ p₂ := by
  have ha : 0 < a := hSD.2.1
  have ha3 : a ≤ 3 := not_lt.1 fun h => t2020_not_isSchwarz_of_three_lt h hSD
  have hD := hSD.1
  have h15 : 5 ≤ 15 / a := by
    rw [le_div_iff₀ ha]
    linarith
  set k : ℝ := 1 + 15 / a with hk
  have hk1 : 0 < k - 1 := by linarith
  have hk15 : k - 1 = 15 / a := by
    rw [hk]
    ring
  have hkr : r < k * r := by nlinarith [mul_pos hk1 hr]
  by_contra hJ
  have hsep : ¬ JoinedIn (D ∩ ball z (k * r)) p₁ p₂ := fun h =>
    hJ (h.mono (inter_subset_inter_right _ ball_subset_closedBall))
  have hq₁ : p₁ ∈ D ∩ ball z (k * r) := ⟨hp₁.1, closedBall_subset_ball hkr hp₁.2⟩
  have hq₂ : p₂ ∈ D ∩ ball z (k * r) := ⟨hp₂.1, closedBall_subset_ball hkr hp₂.2⟩
  obtain ⟨lβ, hβ, hβe⟩ := s20v_polygon_path hD.1 hD.2.1.isPreconnected hp₁.1 hp₂.1
  obtain ⟨w₁, w₂, hw₁D, hw₂D, hw₁z, hw₂z, hwind⟩ := s20v_case_i_windings hD hq₁ hq₂ hsep hβ hβe
  have hseg : segment ℝ p₂ p₁ ⊆ closedBall z r := (convex_closedBall z r).segment_subset hp₂.2 hp₁.2
  have htr : polyTrace (p₁ :: (lβ ++ [p₁])) ⊆ D ∪ closedBall z r :=
    s20v_trace_subset (V := closedBall z r) hp₁.1 hβ hβe ⟨hseg, trivial⟩ rfl
  have hnot : ∀ w, w ∉ D → k * r ≤ ‖w - z‖ → w ∉ polyTrace (p₁ :: (lβ ++ [p₁])) := by
    intro w hwD hwz hw
    rcases htr hw with h | h
    · exact hwD h
    · rw [mem_closedBall, dist_eq_norm] at h
      linarith
  have hbound : ‖pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ [p₁]‖ ≤ 4 * a / 15 := by
    have hpos : 0 < (k - 1) * r := mul_pos hk1 hr
    have hd : ∀ w, k * r ≤ ‖w - z‖ → ∀ ζ, ‖ζ - z‖ ≤ r → (k - 1) * r ≤ ‖ζ - w‖ := by
      intro w hw ζ hζ
      have h1 := norm_sub_norm_le (w - z) (ζ - z)
      rw [show w - z - (ζ - z) = -(ζ - w) by ring, norm_neg] at h1
      linarith
    have hC : ∀ ζ ∈ segment ℝ p₂ p₁, ‖(ζ - w₁)⁻¹ - (ζ - w₂)⁻¹‖ ≤ 2 / ((k - 1) * r) := by
      intro ζ hζ
      have hζz : ‖ζ - z‖ ≤ r := by
        have h := hseg hζ
        rwa [mem_closedBall, dist_eq_norm] at h
      calc ‖(ζ - w₁)⁻¹ - (ζ - w₂)⁻¹‖ ≤ ‖(ζ - w₁)⁻¹‖ + ‖(ζ - w₂)⁻¹‖ := norm_sub_le _ _
        _ = ‖ζ - w₁‖⁻¹ + ‖ζ - w₂‖⁻¹ := by rw [norm_inv, norm_inv]
        _ ≤ ((k - 1) * r)⁻¹ + ((k - 1) * r)⁻¹ :=
          add_le_add (inv_anti₀ hpos (hd w₁ hw₁z ζ hζz)) (inv_anti₀ hpos (hd w₂ hw₂z ζ hζz))
        _ = 2 / ((k - 1) * r) := by ring
    have hlen : ‖p₁ - p₂‖ ≤ 2 * r := by
      have h1 := norm_sub_le (p₁ - z) (p₂ - z)
      rw [show p₁ - z - (p₂ - z) = p₁ - p₂ by ring] at h1
      have h2 := hp₁.2
      have h3 := hp₂.2
      rw [mem_closedBall, dist_eq_norm] at h2 h3
      linarith
    simp only [pathIntFrom, add_zero]
    calc ‖segIntegral (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ p₁‖ ≤ 2 / ((k - 1) * r) * ‖p₁ - p₂‖ :=
          norm_segIntegral_le hC
      _ ≤ 2 / ((k - 1) * r) * (2 * r) := mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 4 / (k - 1) := by
          rw [div_mul_eq_mul_div, div_eq_div_iff hpos.ne' hk1.ne']
          ring
      _ = 4 * a / 15 := by rw [hk15, div_div_eq_mul_div]
  exact s20v_analytic hSD hw₁D hw₂D hp₁.1 hβ hβe rfl (hnot w₁ hw₁D hw₁z) (hnot w₂ hw₂D hw₂z) hwind hbound

/-- Condition (ii) of `k`-local connectivity for an `a`-Schwarz domain, `k = 1 + 15/a`.

Take `B` to be the exterior of `closedBall z ρ`, `ρ = r/k`.  Suppose all points of `ℂ ∖ D` in that ball had the same
winding number `N`.  Appending the loop `s20v_ext_loop` with winding number `-N` would then contradict `s20v_ps`.  So
two complement points have different winding numbers; they feed `s20v_analytic`, and the bound (20.23) comes from
`s20v_ext_bound`. -/
theorem s20v_case_ii {D : Set ℂ} {a : ℝ} (hSD : IsSchwarzDomain D a) {z : ℂ} {r : ℝ} (hr : 0 < r) {p₁ p₂ : ℂ}
    (hp₁ : p₁ ∈ D \ ball z r) (hp₂ : p₂ ∈ D \ ball z r) :
    JoinedIn (D \ ball z (r / (1 + 15 / a))) p₁ p₂ := by
  have ha : 0 < a := hSD.2.1
  have ha3 : a ≤ 3 := not_lt.1 fun h => t2020_not_isSchwarz_of_three_lt h hSD
  have hD := hSD.1
  have h15 : 5 ≤ 15 / a := by
    rw [le_div_iff₀ ha]
    linarith
  set k : ℝ := 1 + 15 / a with hk
  have hk6 : 6 ≤ k := by linarith
  have hk15 : k - 1 = 15 / a := by
    rw [hk]
    ring
  set ρ : ℝ := r / k with hρ
  have hρr : ρ < r / 2 := by
    rw [hρ, div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [mul_pos hr (show (0 : ℝ) < k - 2 by linarith)]
  have hpz : ∀ p ∈ D \ ball z r, r ≤ ‖p - z‖ := by
    intro p hp
    have h := hp.2
    rwa [mem_ball, not_lt, dist_eq_norm] at h
  have hp₁z := hpz p₁ hp₁
  have hp₂z := hpz p₂ hp₂
  have hBo : IsOpen {ζ : ℂ | ρ < ‖ζ - z‖} := isOpen_lt continuous_const (by fun_prop)
  have hRo : IsOpen {ζ : ℂ | r / 2 < ‖ζ - z‖} := isOpen_lt continuous_const (by fun_prop)
  have hRB : {ζ : ℂ | r / 2 < ‖ζ - z‖} ⊆ {ζ : ℂ | ρ < ‖ζ - z‖} := fun ζ hζ => lt_trans hρr hζ
  have hRc : IsPreconnected {ζ : ℂ | r / 2 < ‖ζ - z‖} := by
    have h := (isPreconnected_setOf_lt_norm (r := r / 2) (by positivity)).image (fun ζ => ζ + z)
      (continuous_id.add continuous_const).continuousOn
    convert h using 1
    ext ζ
    constructor
    · intro hζ
      exact ⟨ζ - z, show r / 2 < ‖ζ - z‖ from hζ, sub_add_cancel ζ z⟩
    · rintro ⟨u, hu, rfl⟩
      show r / 2 < ‖u + z - z‖
      simpa using hu
  by_contra hJ
  have hsep : ¬ JoinedIn (D ∩ {ζ | ρ < ‖ζ - z‖}) p₁ p₂ := by
    intro h
    refine hJ (h.mono fun ζ hζ => ⟨hζ.1, ?_⟩)
    rw [mem_ball, dist_eq_norm, not_lt]
    exact le_of_lt (show ρ < ‖ζ - z‖ from hζ.2)
  have hq₁ : p₁ ∈ D ∩ {ζ | ρ < ‖ζ - z‖} := ⟨hp₁.1, by show ρ < ‖p₁ - z‖; linarith⟩
  have hq₂ : p₂ ∈ D ∩ {ζ | ρ < ‖ζ - z‖} := ⟨hp₂.1, by show ρ < ‖p₂ - z‖; linarith⟩
  have hR₁ : p₁ ∈ {ζ : ℂ | r / 2 < ‖ζ - z‖} := by
    show r / 2 < ‖p₁ - z‖
    linarith
  have hR₂ : p₂ ∈ {ζ : ℂ | r / 2 < ‖ζ - z‖} := by
    show r / 2 < ‖p₂ - z‖
    linarith
  obtain ⟨lβ, hβ, hβe⟩ := s20v_polygon_path hD.1 hD.2.1.isPreconnected hp₁.1 hp₂.1
  obtain ⟨lc, hc, hce⟩ := s20v_polygon_path hRo hRc hR₂ hR₁
  have htr : polyTrace (p₁ :: (lβ ++ lc)) ⊆ D ∪ {ζ : ℂ | r / 2 < ‖ζ - z‖} :=
    s20v_trace_subset hp₁.1 hβ hβe hc hce
  have hnot : ∀ w, w ∉ D → ‖w - z‖ ≤ ρ → w ∉ polyTrace (p₁ :: (lβ ++ lc)) := by
    intro w hwD hwz hw
    rcases htr hw with h | h
    · exact hwD h
    · have h' : r / 2 < ‖w - z‖ := h
      linarith
  have hexists : ∃ w₁ w₂, w₁ ∉ D ∧ w₂ ∉ D ∧ ‖w₁ - z‖ ≤ ρ ∧ ‖w₂ - z‖ ≤ ρ ∧
      polyWinding (p₁ :: (lβ ++ lc)) w₁ ≠ polyWinding (p₁ :: (lβ ++ lc)) w₂ := by
    by_contra hall'
    have hall : ∀ w₁ w₂, w₁ ∉ D → w₂ ∉ D → ‖w₁ - z‖ ≤ ρ → ‖w₂ - z‖ ≤ ρ →
        polyWinding (p₁ :: (lβ ++ lc)) w₁ = polyWinding (p₁ :: (lβ ++ lc)) w₂ :=
      fun w₁ w₂ h1 h2 h3 h4 => not_not.1 fun hne => hall' ⟨w₁, w₂, h1, h2, h3, h4, hne⟩
    obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ w, w ∉ D → ‖w - z‖ ≤ ρ → polyWinding (p₁ :: (lβ ++ lc)) w = N := by
      by_cases hE : ∃ w₀, w₀ ∉ D ∧ ‖w₀ - z‖ ≤ ρ
      · obtain ⟨w₀, h0D, h0z⟩ := hE
        obtain ⟨N, hN⟩ := exists_int_polyWinding (hnot w₀ h0D h0z)
        exact ⟨N, fun w hwD hwz => (hall w w₀ hwD h0D hwz h0z).trans hN⟩
      · exact ⟨0, fun w hwD hwz => absurd ⟨w, hwD, hwz⟩ hE⟩
    obtain ⟨lN, hlN, hlNe, hlNw⟩ :=
      s20v_ext_loop (z := z) (q := p₁) (t := r / 2) (by positivity) (by linarith) (-N)
    have hA : lastOf p₁ (lβ ++ lc) = p₁ := by rw [lastOf_append, hβe, hce]
    have hc' : SegsIn {ζ | ρ < ‖ζ - z‖} p₂ (lc ++ lN) := by
      rw [segsIn_append]
      refine ⟨s20v_segsIn_mono hRB hc, ?_⟩
      rw [hce]
      exact s20v_segsIn_mono hRB hlN
    have hce' : lastOf p₂ (lc ++ lN) = p₁ := by rw [lastOf_append, hce, hlNe]
    obtain ⟨w, hwD, hwB, hw⟩ := s20v_ps hD.1 hBo hq₁ hq₂ hsep hβ hβe hc' hce'
    have hwz : ‖w - z‖ ≤ ρ := not_lt.1 hwB
    rw [← List.append_assoc, s20v_polyWinding_append hA hlNe, hN w hwD hwz, hlNw w (by linarith)] at hw
    simp at hw
  obtain ⟨w₁, w₂, hw₁D, hw₂D, hw₁z, hw₂z, hwind⟩ := hexists
  have hbound : ‖pathIntFrom (fun ζ => (ζ - w₁)⁻¹ - (ζ - w₂)⁻¹) p₂ lc‖ ≤ 4 * a / 15 := by
    have h := s20v_ext_bound hr hk6 hw₁z hw₂z hp₂z hc (by rw [hce]; exact hp₁z)
    rw [hk15] at h
    calc _ ≤ 4 / (15 / a) := h
      _ = 4 * a / 15 := by rw [div_div_eq_mul_div]
  exact s20v_analytic hSD hw₁D hw₂D hp₁.1 hβ hβe hce (hnot w₁ hw₁D hw₁z) (hnot w₂ hw₂D hw₂z) hwind hbound

/-- **Theorem 20.4**: an `a`-Schwarz domain is `k`-locally connected with `k = 1 + 15/a`.

Proof: `s20v_case_i` and `s20v_case_ii` (P2a interface, 2026-09-27).  The two steps that were missing on 2026-09-14
are now available: Koebe's ¼-theorem in the form (20.14), `η_D(z) ≥ 1/(2 dist(z, ∂D))`, is `t203_density_ge`, and
the planar separation step (points of `ℂ ∖ D` on both sides of `β ∪ [z₁, z₂]`) is replaced by the winding-number
statement `s20v_ps` (Cousin splitting and Dixon's polygon Cauchy theorem, no Janiszewski-type topology). -/
theorem thm20_4 {D : Set ℂ} {a : ℝ} (hD : IsSchwarzDomain D a) : IsKLocallyConnected D (1 + 15 / a) := by
  have ha : 0 < a := hD.2.1
  refine ⟨?_, fun z r hr => ⟨fun p hp q hq => s20v_case_i hD hr hp hq, fun p hp q hq => s20v_case_ii hD hr hp hq⟩⟩
  have h15 : 0 ≤ 15 / a := by positivity
  linarith

/-! ### Gehring chain (s21u stage P4, coordinator 553e2d): Theorem 20.5

The book's route: `thm20_4` (an `a`-Schwarz domain is `k`-locally connected, `k = 1 + 15/a`) ⇒ **W2** (a `k`-locally
connected hyperbolic simply connected domain is a Jordan domain; the book's footnote) ⇒ `2(2k² + 1)`-bounded turning ⇒
Theorem 18.1 (sufficiency, `thm18_1_quasicircle_of_boundedTurning`, S18).

* **W2, bounded case** (`s20g_jordan_of_qlc`): Carathéodory's argument of `Lemmas/CaratheodoryJordan.lean` with local
  connectivity (`s20g_QLC`) in place of the Jordan hypothesis: the conformal map `f : Δ → Ω` extends continuously
  (`s20g_ext_continuous`, from clause (ii)) and injectively (`s20g_ext_injOn`, from clauses (i) and (ii) through the
  disc crossing theorem `s20g_crossing`).
* **W2, unbounded case** (`s20g_isJordanDomain`): `z ↦ 1/(z - c)` for a point `c` outside the closure
  (`s20g_exists_exterior`) makes the domain bounded and keeps `s20g_QLC` (`s20g_qlc_inv`); the frontier in `ℂ̄`, which
  contains `∞`, is carried back by the Möbius homeomorphism.
* **Bounded turning** (`s20g_boundedTurning`): the crossing argument again, quantitatively, through the disc
  uniformizer of the Jordan domain (`s20g_bt_cross`), and the two arcs of `C ∖ {z₁, z₂}` as its components
  (`s20g_bt_arc_component`). -/

/-- Qualitative local connectivity of `D` at its (finite) boundary points: near `w ∈ ∂D` points of `D` are joined in
`D` near `w` (i′), and points of `D` away from `w` are joined in `D` off a smaller disc about `w` (ii′). -/
def s20g_QLC (D : Set ℂ) : Prop :=
  ∀ w ∈ frontier D,
    (∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ p ∈ D ∩ ball w δ, ∀ q ∈ D ∩ ball w δ, JoinedIn (D ∩ ball w ε) p q) ∧
      ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ p ∈ D \ ball w R, ∀ q ∈ D \ ball w R, JoinedIn (D \ ball w ρ) p q

/-- A `k`-locally connected domain is qualitatively locally connected: `δ = ε/(2k)` in (i′), `ρ = R/k` in (ii′). -/
theorem s20g_qlc_of_kLC {D : Set ℂ} {k : ℝ} (hk : IsKLocallyConnected D k) : s20g_QLC D := by
  obtain ⟨hk1, hlc⟩ := hk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk1
  intro w _
  refine ⟨fun ε hε => ⟨ε / (2 * k), by positivity, fun p hp q hq => ?_⟩,
    fun R hR => ⟨R / k, by positivity, fun p hp q hq => (hlc w R hR).2 p hp q hq⟩⟩
  have hr : 0 < ε / (2 * k) := by positivity
  have hkr : k * (ε / (2 * k)) < ε := by
    rw [mul_div_assoc', mul_comm 2 k, ← div_div, mul_div_cancel_left₀ ε hk0.ne']
    linarith
  exact ((hlc w _ hr).1 p ⟨hp.1, ball_subset_closedBall hp.2⟩ q ⟨hq.1, ball_subset_closedBall hq.2⟩).mono
    (inter_subset_inter_right _ (closedBall_subset_ball hkr))

/-- **Exterior point, one step.**  Let `L` be a continuous logarithm of `z - b` on `D`, and let `p, p'` be joined by
a path in `D` all of whose points `z` satisfy `‖z - (b + u)‖ < 1`, `‖u‖ = 1`.  Then the change of `L` from `p` to
`p'` is the change of the principal logarithm of `(z - b)/u`. -/
theorem s20g_a_log_step {D : Set ℂ} {L : ℂ → ℂ} {b u p p' : ℂ} (hLc : ContinuousOn L D)
    (hLe : EqOn (Complex.exp ∘ L) (fun z => z - b) D) (hu : ‖u‖ = 1) (γ : Path p p')
    (hγD : ∀ t, γ t ∈ D) (hγb : ∀ t, ‖γ t - (b + u)‖ < 1) :
    L p' - L p = Complex.log ((p' - b) / u) - Complex.log ((p - b) / u) := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  have hext : ∀ t : ℝ, ∃ s, γ.extend t = γ s := fun t => ⟨_, rfl⟩
  have hextD : ∀ t : ℝ, γ.extend t ∈ D := fun t => by
    obtain ⟨s, hs⟩ := hext t
    rw [hs]
    exact hγD s
  have h := lift_sub_eq_log_sub_log (γ := fun t => (γ.extend t - b) / u)
    (L := fun t => L (γ.extend t) - Complex.log u) zero_le_one
    ((γ.continuous_extend.sub continuous_const).div_const _).continuousOn
    ((hLc.comp_continuous γ.continuous_extend hextD).sub continuous_const).continuousOn
    (fun t _ => by
      obtain ⟨s, hs⟩ := hext t
      have h1 : (γ.extend t - b) / u = 1 + (γ.extend t - (b + u)) / u := by
        field_simp
        ring
      rw [h1]
      refine mem_slitPlane_of_norm_lt_one ?_
      rw [norm_div, hu, div_one, hs]
      exact hγb s)
    (fun t _ => by
      have h1 := hLe (hextD t)
      simp only [Function.comp_apply] at h1
      rw [Complex.exp_sub, h1, Complex.exp_log hu0])
  simp only [Path.extend_zero, Path.extend_one] at h
  rw [← h]
  ring

/-- **Exterior point** (W2, unbounded case): a `k`-locally connected hyperbolic simply connected domain has a point of
`ℂ` outside its closure.

*Truth*: trivial for bounded `D`.  In general pick `b ∈ ∂D` (`D ≠ ∅, ℂ`); we show `sphere b 1 ⊄ closure D`.  Otherwise
take `N` large, `c_j = b + e^{2πij/N}` and `p_j ∈ D` with `‖p_j - c_j‖ < ε` (`p_N = p_0`).  Clause (i) of `hk` at
`p_j` with radius `d = ‖p_{j+1} - p_j‖` joins `p_j` to `p_{j+1}` inside `D ∩ closedBall p_j (k d) ⊆ ball c_j 1` (`N`
large, `ε` small).  Let `L` be a continuous logarithm of `z - b` on `D` (`b ∉ D`, `D` simply connected) and
`ℓ_j z = log ((z - b)/(c_j - b))` (principal branch; `(z - b)/(c_j - b) ∈ ball 1 1 ⊆ slitPlane` on `ball c_j 1`).  On
the connected image of the joining path `L - ℓ_j` is continuous with values in `log (c_j - b) + 2πiℤ`, hence
constant, so `L p_{j+1} - L p_j = ℓ_j p_{j+1} - ℓ_j p_j`.  Summing over `j` (telescoping) gives
`0 = Σ_j (arg ((p_{j+1} - b)/(c_j - b)) - arg ((p_j - b)/(c_j - b))) = 2π + O(Nε)`: a contradiction for `ε ≪ 1/N`.
No closed loop is built; only the endpoint values of `L` are compared.

*Route*: `Complex.exists_continuousOn_eqOn_exp_comp` (the continuous logarithm, as in
`RMT.exists_holomorphic_log_of_simplyConnected`, RiemannMapping:504), `hD.2.2.1`, `hk.2` (clause (i)),
`JoinedIn.somePath` and the connected range of a path, `Complex.log`/`Complex.arg` bounds near `1`. -/
theorem s20g_exists_exterior {D : Set ℂ} {k : ℝ} (hD : IsHyperbolicSimplyConnected D)
    (hk : IsKLocallyConnected D k) : ∃ c : ℂ, c ∉ closure D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hDo, -, hDsc, hDne⟩ := hD
  obtain ⟨hk1, hlc⟩ := hk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk1
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem D).1 hDne
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hDsc hDo
    (g := fun z : ℂ => z - b) (continuousOn_id.sub continuousOn_const) (by
      rintro ⟨z, hz, hz0⟩
      exact hb (sub_eq_zero.1 hz0 ▸ hz))
  -- the number of points and the angle step
  set N : ℕ := ⌈8 * π * k⌉₊ + 3 with hN
  have hN3 : (3 : ℝ) ≤ N := by
    rw [hN]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈8 * π * k⌉₊]
  have hNk : 8 * π * k ≤ N := by
    rw [hN]
    push_cast
    linarith [Nat.le_ceil (8 * π * k)]
  have hN0 : (0 : ℝ) < N := by linarith
  set a : ℝ := 2 * π / N with ha
  have ha0 : 0 < a := by positivity
  have haπ : a < π := by
    rw [ha, div_lt_iff₀ hN0]
    nlinarith [Real.pi_pos]
  have hka : k * a ≤ 1 / 4 := by
    rw [ha, mul_div_assoc', div_le_iff₀ hN0]
    nlinarith [Real.pi_pos]
  set η : ℝ := π / (2 * N) with hη
  have hη0 : 0 < η := by positivity
  have haη : a - 2 * η = π / N := by
    rw [ha, hη]
    field_simp
    ring
  -- continuity of `arg` at `1` and at `e^{ia}`
  have harg_a : arg (Complex.exp (a * I)) = a := by
    rw [Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).2 ⟨by linarith, by linarith⟩]
  have hslit_a : Complex.exp (a * I) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg, harg_a]
    exact ⟨haπ.ne, Complex.exp_ne_zero _⟩
  obtain ⟨ε₁, hε₁, h1⟩ :=
    Metric.continuousAt_iff.1 (Complex.continuousAt_arg Complex.one_mem_slitPlane) η hη0
  obtain ⟨ε₂, hε₂, h2⟩ := Metric.continuousAt_iff.1 (Complex.continuousAt_arg hslit_a) η hη0
  set ε : ℝ := min (1 / (12 * k)) (min ε₁ ε₂) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min hε₁ hε₂)
  have hεk : 12 * k * ε ≤ 1 := by
    have h3 := min_le_left (1 / (12 * k)) (min ε₁ ε₂)
    rw [← hε, le_div_iff₀ (by positivity)] at h3
    linarith
  have hε1 : ε ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  -- the points `b + u j` of the circle and nearby points `p j` of `D`
  set u : ℕ → ℂ := fun j => Complex.exp (((j : ℝ) * a : ℝ) * I) with hu
  have hu1 : ∀ j, ‖u j‖ = 1 := fun j => Complex.norm_exp_ofReal_mul_I _
  have hu0 : ∀ j, u j ≠ 0 := fun j => Complex.exp_ne_zero _
  have husucc : ∀ j : ℕ, u (j + 1) = u j * Complex.exp (a * I) := by
    intro j
    simp only [hu]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have huN : u N = u 0 := by
    simp only [hu]
    rw [show ((N : ℝ) * a : ℝ) = 2 * π by rw [ha]; field_simp]
    simp
  have hq : ∀ j : ℕ, ∃ q ∈ D, ‖q - (b + u j)‖ < ε := by
    intro j
    obtain ⟨q, hqD, hqd⟩ := Metric.mem_closure_iff.1 (hcon (b + u j)) ε hε0
    exact ⟨q, hqD, by rw [← dist_eq_norm, dist_comm]; exact hqd⟩
  choose q hqD hqε using hq
  set p : ℕ → ℂ := fun j => if j = N then q 0 else q j with hp
  have hpD : ∀ j, p j ∈ D := fun j => by
    simp only [hp]
    split_ifs <;> exact hqD _
  have hpε : ∀ j, ‖p j - (b + u j)‖ < ε := by
    intro j
    simp only [hp]
    split_ifs with h
    · rw [h, huN]
      exact hqε 0
    · exact hqε j
  -- one step: the change of `L` is a principal-log difference
  have step : ∀ j : ℕ, L (p (j + 1)) - L (p j) =
      Complex.log ((p (j + 1) - b) / u j) - Complex.log ((p j - b) / u j) := by
    intro j
    set r : ℝ := a + 2 * ε with hr
    have hr0 : 0 < r := by positivity
    have hdist : ‖p (j + 1) - p j‖ ≤ r := by
      have e1 : p (j + 1) - p j = (p (j + 1) - (b + u (j + 1))) + u j * (Complex.exp (a * I) - 1) -
          (p j - (b + u j)) := by
        rw [husucc]
        ring
      have e2 : ‖u j * (Complex.exp (a * I) - 1)‖ ≤ a := by
        rw [norm_mul, hu1, one_mul, mul_comm]
        have h3 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a)
        rwa [Real.norm_of_nonneg ha0.le] at h3
      rw [e1]
      calc ‖(p (j + 1) - (b + u (j + 1))) + u j * (Complex.exp (a * I) - 1) - (p j - (b + u j))‖
          ≤ ‖p (j + 1) - (b + u (j + 1))‖ + ‖u j * (Complex.exp (a * I) - 1)‖ + ‖p j - (b + u j)‖ :=
            norm_sub_le_of_le (norm_add_le _ _) le_rfl
        _ ≤ ε + a + ε := by linarith [hpε (j + 1), hpε j]
        _ = r := by rw [hr]; ring
    obtain ⟨γ, hγ⟩ := (hlc (p j) r hr0).1 (p j) ⟨hpD j, mem_closedBall_self hr0.le⟩ (p (j + 1))
      ⟨hpD (j + 1), by rw [mem_closedBall, dist_eq_norm]; exact hdist⟩
    refine s20g_a_log_step hLc hLe (hu1 j) γ (fun t => (hγ t).1) fun t => ?_
    have h3 : ‖γ t - p j‖ ≤ k * r := by
      have h4 := (hγ t).2
      rwa [mem_closedBall, dist_eq_norm] at h4
    calc ‖γ t - (b + u j)‖ = ‖(γ t - p j) + (p j - (b + u j))‖ := by ring_nf
      _ ≤ ‖γ t - p j‖ + ‖p j - (b + u j)‖ := norm_add_le _ _
      _ < k * r + ε := add_lt_add_of_le_of_lt h3 (hpε j)
      _ ≤ 1 / 4 + 3 * k * ε := by rw [hr]; nlinarith
      _ < 1 := by linarith
  -- the telescoping sum vanishes, but every term has argument change `> 0`
  have hsum : ∑ j ∈ Finset.range N, (L (p (j + 1)) - L (p j)) = 0 := by
    rw [Finset.sum_range_sub (fun j => L (p j))]
    simp [hp]
  have him : ∑ j ∈ Finset.range N, (arg ((p (j + 1) - b) / u j) - arg ((p j - b) / u j)) = 0 := by
    have h3 := congrArg Complex.im hsum
    rw [Complex.im_sum] at h3
    simp only [step, Complex.sub_im, Complex.log_im, Complex.zero_im] at h3
    exact h3
  have hterm : ∀ j : ℕ, 0 < arg ((p (j + 1) - b) / u j) - arg ((p j - b) / u j) := by
    intro j
    have hj := hu0 j
    have e1 : dist ((p j - b) / u j) 1 < ε₁ := by
      rw [dist_eq_norm, show (p j - b) / u j - 1 = (p j - (b + u j)) / u j by field_simp; ring, norm_div,
        hu1, div_one]
      exact (hpε j).trans_le hε1
    have e2 : dist ((p (j + 1) - b) / u j) (Complex.exp (a * I)) < ε₂ := by
      rw [dist_eq_norm, show (p (j + 1) - b) / u j - Complex.exp (a * I) =
        (p (j + 1) - (b + u (j + 1))) / u j by rw [husucc]; field_simp; ring, norm_div, hu1, div_one]
      exact (hpε (j + 1)).trans_le hε2
    have f1 := h1 e1
    have f2 := h2 e2
    rw [Complex.arg_one, Real.dist_eq] at f1
    rw [harg_a, Real.dist_eq] at f2
    have g1 := abs_lt.1 f1
    have g2 := abs_lt.1 f2
    have h3 : 0 < π / N := by positivity
    linarith
  have hpos := Finset.sum_pos (fun j _ => hterm j) (Finset.nonempty_range_iff.2 (Nat.cast_pos.1 hN0).ne')
  rw [him] at hpos
  exact lt_irrefl _ hpos

/-- `mobiusFn 0 1 1 (-c)` is the inversion `z ↦ (z - c)⁻¹`. -/
theorem s20g_a_mob (c z : ℂ) : mobiusFn 0 1 1 (-c) z = (z - c)⁻¹ := by
  rw [mobiusFn]
  ring

/-- Local Lipschitz bound for the inversion `z ↦ (z - c)⁻¹` near `z₀ ≠ c`: on
`closedBall z₀ (‖z₀ - c‖/2)` it is `2/‖z₀ - c‖²`-Lipschitz at `z₀`. -/
theorem s20g_a_inv_lip {c z z₀ : ℂ} (hz₀ : z₀ ≠ c) (h : ‖z - z₀‖ ≤ ‖z₀ - c‖ / 2) :
    ‖(z - c)⁻¹ - (z₀ - c)⁻¹‖ ≤ 2 * ‖z - z₀‖ / ‖z₀ - c‖ ^ 2 := by
  have hb : 0 < ‖z₀ - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz₀)
  have h1 : ‖z₀ - c‖ ≤ ‖z - c‖ + ‖z - z₀‖ := by
    calc ‖z₀ - c‖ = ‖(z - c) - (z - z₀)‖ := by rw [show (z - c) - (z - z₀) = z₀ - c by ring]
      _ ≤ ‖z - c‖ + ‖z - z₀‖ := norm_sub_le _ _
  have hv : ‖z₀ - c‖ / 2 ≤ ‖z - c‖ := by linarith
  have hv' : 0 < ‖z - c‖ := by linarith
  have hzc : z - c ≠ 0 := norm_pos_iff.1 hv'
  have hz₀c : z₀ - c ≠ 0 := sub_ne_zero.2 hz₀
  rw [show (z - c)⁻¹ - (z₀ - c)⁻¹ = (z₀ - z) / ((z - c) * (z₀ - c)) by field_simp; ring, norm_div,
    norm_mul, norm_sub_rev z₀ z, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (z - z₀)) hb.le) (sub_nonneg.2 hv)]

/-- Pushing a joining path through the inversion `z ↦ (z - c)⁻¹` (continuous off `c`). -/
theorem s20g_a_joined_inv {A B : Set ℂ} {c p q : ℂ} (h : JoinedIn A p q) (hc : ∀ z ∈ A, z ≠ c)
    (hB : ∀ z ∈ A, (z - c)⁻¹ ∈ B) : JoinedIn B ((p - c)⁻¹) ((q - c)⁻¹) := by
  have hcont : ContinuousOn (fun z : ℂ => (z - c)⁻¹) A :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 (hc z hz)
  exact (h.map hcont).mono (image_subset_iff.2 hB)

/-- **Local connectivity after inversion** (W2, unbounded case): for `c ∉ closure D`, the image of a `k`-locally
connected `D` under `z ↦ 1/(z - c)` is qualitatively locally connected.

*Truth*: `T z = 1/(z - c)` is a homeomorphism of `ℂ ∖ {c}` onto `ℂ ∖ {0}`, bi-Lipschitz near each `z₀ ≠ c`
(`‖T z - T z₀‖ = ‖z - z₀‖/(‖z - c‖ ‖z₀ - c‖)`).  A boundary point `w ≠ 0` of `T(D)` is `T z₀` with `z₀ = c + 1/w ∈ ∂D`
(`T` homeomorphism off the poles); balls about `w` and about `z₀` are nested with factors `2/‖w‖²`, `2/‖z₀ - c‖²` once
the radii are below `‖w‖/2`, `‖z₀ - c‖/2`, so (i)/(ii) of `hk` at `z₀` give (i′)/(ii′) at `w` (for (ii′) it suffices
to treat small `R`: the condition is monotone in `R`).  The boundary point `w = 0` occurs when `D` is unbounded:
`‖T z‖ < δ ↔ ‖z - c‖ > 1/δ`, so (i′) at `0` follows from clause (ii) of `hk` at `c` with radius `1/δ`
(`δ = ε/(2k)`), and (ii′) at `0` from clause (i) at `c` with radius `1/R` (`ρ = R/k`).

*Route*: `hk`, `uq_j_isConformalOnto_mobiusInv` (S13:4191, continuity of `T` on `D`), `JoinedIn.map` (the
`ContinuousOn` form) or `Path.map'` to push the joining paths through `T`, `c ∉ closure D` (so `‖z - c‖ ≥ r > 0` on
`D`). -/
theorem s20g_qlc_inv {D : Set ℂ} {k : ℝ} {c : ℂ} (hk : IsKLocallyConnected D k) (hc : c ∉ closure D) :
    s20g_QLC (mobiusFn 0 1 1 (-c) '' D) := by
  obtain ⟨hk1, hlc⟩ := hk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk1
  have hDc : ∀ z ∈ D, z ≠ c := fun z hz h => hc (h ▸ subset_closure hz)
  have hpos : ∀ z ∈ D, 0 < ‖z - c‖ := fun z hz => norm_pos_iff.2 (sub_ne_zero.2 (hDc z hz))
  rw [image_congr fun z _ => s20g_a_mob c z]
  intro w _
  rcases eq_or_ne w 0 with rfl | hw
  · refine ⟨fun ε hε => ⟨ε / (2 * k), by positivity, ?_⟩, fun R hR => ⟨R / k, by positivity, ?_⟩⟩
    · rintro _ ⟨⟨zp, hzp, rfl⟩, hp⟩ _ ⟨⟨zq, hzq, rfl⟩, hq⟩
      have hr : 0 < 2 * k / ε := by positivity
      have key : ∀ z ∈ D, (z - c)⁻¹ ∈ ball (0 : ℂ) (ε / (2 * k)) → z ∈ D \ ball c (2 * k / ε) := by
        intro z hz hzb
        refine ⟨hz, fun hzc => ?_⟩
        rw [mem_ball_zero_iff, norm_inv] at hzb
        rw [mem_ball, dist_eq_norm] at hzc
        have hlt : ‖z - c‖⁻¹ * ‖z - c‖ < ε / (2 * k) * (2 * k / ε) :=
          mul_lt_mul'' hzb hzc (inv_nonneg.2 (norm_nonneg _)) (norm_nonneg _)
        rw [inv_mul_cancel₀ (hpos z hz).ne', div_mul_div_comm, mul_comm ε, div_self (by positivity)] at hlt
        exact lt_irrefl _ hlt
      refine s20g_a_joined_inv ((hlc c _ hr).2 zp (key zp hzp hp) zq (key zq hzq hq))
        (fun z hz => hDc z hz.1) fun z hz => ⟨⟨z, hz.1, rfl⟩, ?_⟩
      have h2 : 2 / ε ≤ ‖z - c‖ := by
        have h3 := hz.2
        rw [mem_ball, dist_eq_norm, not_lt] at h3
        rwa [show 2 * k / ε / k = 2 / ε by field_simp] at h3
      rw [mem_ball_zero_iff, norm_inv]
      calc ‖z - c‖⁻¹ ≤ (2 / ε)⁻¹ := inv_anti₀ (by positivity) h2
        _ = ε / 2 := inv_div 2 ε
        _ < ε := half_lt_self hε
    · rintro _ ⟨⟨zp, hzp, rfl⟩, hp⟩ _ ⟨⟨zq, hzq, rfl⟩, hq⟩
      have hr : 0 < 1 / R := by positivity
      have key : ∀ z ∈ D, (z - c)⁻¹ ∉ ball (0 : ℂ) R → z ∈ D ∩ closedBall c (1 / R) := by
        intro z hz hzb
        refine ⟨hz, ?_⟩
        rw [mem_ball_zero_iff, norm_inv, not_lt, le_inv_comm₀ hR (hpos z hz)] at hzb
        rwa [mem_closedBall, dist_eq_norm, one_div]
      refine s20g_a_joined_inv ((hlc c _ hr).1 zp (key zp hzp hp) zq (key zq hzq hq))
        (fun z hz => hDc z hz.1) fun z hz => ⟨⟨z, hz.1, rfl⟩, ?_⟩
      have h2 : ‖z - c‖ ≤ k * (1 / R) := by
        have h3 := hz.2
        rwa [mem_closedBall, dist_eq_norm] at h3
      rw [mem_ball_zero_iff, norm_inv, not_lt]
      calc R / k = (k * (1 / R))⁻¹ := by field_simp
        _ ≤ ‖z - c‖⁻¹ := inv_anti₀ (hpos z hz.1) h2
  · set z₀ := c + w⁻¹ with hz₀def
    have hz₀c : z₀ - c = w⁻¹ := by rw [hz₀def]; ring
    have hw₀ : (z₀ - c)⁻¹ = w := by rw [hz₀c, inv_inv]
    have ha : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hb : ‖z₀ - c‖ = ‖w‖⁻¹ := by rw [hz₀c, norm_inv]
    have hz₀ne : z₀ ≠ c := fun h => by
      rw [h, sub_self] at hz₀c
      exact inv_ne_zero hw hz₀c.symm
    -- points of the image near `w` come from points near `z₀`
    have back : ∀ z ∈ D, ∀ t : ℝ, t ≤ ‖w‖ / 2 → ‖(z - c)⁻¹ - w‖ ≤ t → ‖z - z₀‖ ≤ 2 * t / ‖w‖ ^ 2 := by
      intro z hz t ht hzt
      have h := s20g_a_inv_lip (c := 0) (z := (z - c)⁻¹) (z₀ := w) hw (by rw [sub_zero]; exact hzt.trans ht)
      simp only [sub_zero, inv_inv] at h
      calc ‖z - z₀‖ = ‖(z - c) - w⁻¹‖ := by rw [hz₀def, sub_sub]
        _ ≤ 2 * ‖(z - c)⁻¹ - w‖ / ‖w‖ ^ 2 := h
        _ ≤ 2 * t / ‖w‖ ^ 2 := by gcongr
    -- points near `z₀` go to points near `w`
    have fwd : ∀ z : ℂ, ∀ t : ℝ, t ≤ ‖w‖⁻¹ / 2 → ‖z - z₀‖ ≤ t → ‖(z - c)⁻¹ - w‖ ≤ 2 * t * ‖w‖ ^ 2 := by
      intro z t ht hzt
      have h := s20g_a_inv_lip (c := c) (z := z) (z₀ := z₀) hz₀ne (by rw [hb]; exact hzt.trans ht)
      rw [hw₀, hb] at h
      calc ‖(z - c)⁻¹ - w‖ ≤ 2 * ‖z - z₀‖ / ‖w‖⁻¹ ^ 2 := h
        _ ≤ 2 * t / ‖w‖⁻¹ ^ 2 := by gcongr
        _ = 2 * t * ‖w‖ ^ 2 := by field_simp
    refine ⟨fun ε hε => ?_, fun R hR => ?_⟩
    · set δ := min (‖w‖ / (4 * k)) (ε / (8 * k)) with hδ
      have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
      have hδ1 : δ ≤ ‖w‖ / (4 * k) := min_le_left _ _
      have hδ2 : δ ≤ ε / (8 * k) := min_le_right _ _
      have hδ1' : 4 * k * δ ≤ ‖w‖ := by
        rw [le_div_iff₀ (by positivity)] at hδ1
        linarith
      have hδ2' : 8 * k * δ ≤ ε := by
        rw [le_div_iff₀ (by positivity)] at hδ2
        linarith
      have hδa : δ ≤ ‖w‖ / 2 := by nlinarith
      refine ⟨δ, hδ0, ?_⟩
      rintro _ ⟨⟨zp, hzp, rfl⟩, hp⟩ _ ⟨⟨zq, hzq, rfl⟩, hq⟩
      set r := 2 * δ / ‖w‖ ^ 2 with hr
      have hr0 : 0 < r := by positivity
      have key : ∀ z ∈ D, (z - c)⁻¹ ∈ ball w δ → z ∈ D ∩ closedBall z₀ r := by
        intro z hz hzb
        rw [mem_ball, dist_eq_norm] at hzb
        exact ⟨hz, by rw [mem_closedBall, dist_eq_norm]; exact back z hz δ hδa hzb.le⟩
      refine s20g_a_joined_inv ((hlc z₀ r hr0).1 zp (key zp hzp hp) zq (key zq hzq hq))
        (fun z hz => hDc z hz.1) fun z hz => ⟨⟨z, hz.1, rfl⟩, ?_⟩
      have hkr : k * r ≤ ‖w‖⁻¹ / 2 := by
        rw [hr, show k * (2 * δ / ‖w‖ ^ 2) = 4 * k * δ / (2 * ‖w‖ ^ 2) by ring,
          show ‖w‖⁻¹ / 2 = ‖w‖ / (2 * ‖w‖ ^ 2) by field_simp]
        gcongr
      have hzr : ‖z - z₀‖ ≤ k * r := by
        have h3 := hz.2
        rwa [mem_closedBall, dist_eq_norm] at h3
      have h := fwd z (k * r) hkr hzr
      rw [mem_ball, dist_eq_norm]
      calc ‖(z - c)⁻¹ - w‖ ≤ 2 * (k * r) * ‖w‖ ^ 2 := h
        _ = 4 * k * δ := by rw [hr]; field_simp; ring
        _ < ε := by nlinarith
    · set r₁ := min (‖w‖⁻¹ / 2) (R / (4 * ‖w‖ ^ 2)) with hr₁
      have hr₁0 : 0 < r₁ := lt_min (by positivity) (by positivity)
      have hr₁a : r₁ ≤ ‖w‖⁻¹ / 2 := min_le_left _ _
      have hr₁b : r₁ ≤ R / (4 * ‖w‖ ^ 2) := min_le_right _ _
      have hr₁b' : 2 * r₁ * ‖w‖ ^ 2 < R := by
        rw [le_div_iff₀ (by positivity)] at hr₁b
        nlinarith
      set s := r₁ / k with hs
      have hs0 : 0 < s := by positivity
      set ρ := min (‖w‖ / 2) (s * ‖w‖ ^ 2 / 4) with hρ
      have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
      have hρa : ρ ≤ ‖w‖ / 2 := min_le_left _ _
      have hρb : ρ ≤ s * ‖w‖ ^ 2 / 4 := min_le_right _ _
      refine ⟨ρ, hρ0, ?_⟩
      rintro _ ⟨⟨zp, hzp, rfl⟩, hp⟩ _ ⟨⟨zq, hzq, rfl⟩, hq⟩
      have key : ∀ z ∈ D, (z - c)⁻¹ ∉ ball w R → z ∈ D \ ball z₀ r₁ := by
        intro z hz hzb
        refine ⟨hz, fun hzr => hzb ?_⟩
        rw [mem_ball, dist_eq_norm] at hzr ⊢
        exact (fwd z r₁ hr₁a hzr.le).trans_lt hr₁b'
      refine s20g_a_joined_inv ((hlc z₀ r₁ hr₁0).2 zp (key zp hzp hp) zq (key zq hzq hq))
        (fun z hz => hDc z hz.1) fun z hz => ⟨⟨z, hz.1, rfl⟩, fun hzb => hz.2 ?_⟩
      rw [mem_ball, dist_eq_norm] at hzb ⊢
      have h := back z hz.1 ρ hρa hzb.le
      calc ‖z - z₀‖ ≤ 2 * ρ / ‖w‖ ^ 2 := h
        _ ≤ 2 * (s * ‖w‖ ^ 2 / 4) / ‖w‖ ^ 2 := by gcongr
        _ = s / 2 := by field_simp; ring
        _ < s := half_lt_self hs0

/-- A point `z ≠ u` of the closed unit disc, `‖u‖ = 1`, has `Re (1 - z conj u) > 0`. -/
theorem s20g_b_re_pos {z u : ℂ} (hz : ‖z‖ ≤ 1) (hu : ‖u‖ = 1) (hne : z ≠ u) : 0 < (1 - z * conj u).re := by
  have hz2 : z.re * z.re + z.im * z.im ≤ 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have hu2 : u.re * u.re + u.im * u.im = 1 := by
    have h := Complex.sq_norm u
    rw [Complex.normSq_apply, hu] at h
    linarith
  have hd := Complex.normSq_pos.2 (sub_ne_zero.2 hne)
  rw [Complex.normSq_apply, sub_re, sub_im] at hd
  simp only [sub_re, one_re, mul_re, conj_re, conj_im]
  nlinarith

/-- `e^{ia} conj (e^{ib}) = e^{i(a - b)}`. -/
theorem s20g_b_exp_mul_conj (a b : ℝ) :
    Complex.exp (a * I) * conj (Complex.exp (b * I)) = Complex.exp (((a - b : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The side lemma of the crossing theorem: along a side the lift change of `z - u` (up to a constant factor `w`)
is a principal-branch difference. -/
theorem s20g_b_side {L z : ℝ → ℂ} {u w : ℂ} (hu : ‖u‖ = 1) (hw : w ≠ 0)
    (hL : ContinuousOn L (Icc 0 1)) (hz : ContinuousOn z (Icc 0 1))
    (hzn : ∀ t ∈ Icc (0 : ℝ) 1, ‖z t‖ ≤ 1) (hzu : ∀ t ∈ Icc (0 : ℝ) 1, z t ≠ u)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) * w = 1 - z t * conj u) :
    (L 1 - L 0).im = arg (1 - z 1 * conj u) - arg (1 - z 0 * conj u) := by
  have hM := lift_sub_eq_log_sub_log (γ := fun t => 1 - z t * conj u) (L := fun t => L t + Complex.log w)
    zero_le_one (continuousOn_const.sub (hz.mul continuousOn_const)) (hL.add continuousOn_const)
    (fun t ht => Complex.mem_slitPlane_iff.2 (Or.inl (s20g_b_re_pos (hzn t ht) hu (hzu t ht))))
    (fun t ht => by rw [Complex.exp_add, Complex.exp_log hw, he t ht])
  have h : L 1 - L 0 = (L 1 + Complex.log w) - (L 0 + Complex.log w) := by ring
  rw [h, hM, sub_im, Complex.log_im, Complex.log_im]

/-- `arg (1 - e^{ia} conj e^{ib}) = (a - b)/2 - π/2` for `0 < a - b < 2π`. -/
theorem s20g_b_arg_pos {a b : ℝ} (h0 : 0 < a - b) (h1 : a - b < 2 * π) :
    arg (1 - Complex.exp (a * I) * conj (Complex.exp (b * I))) = (a - b) / 2 - π / 2 := by
  rw [s20g_b_exp_mul_conj]
  set x := (a - b) / 2 with hx
  have hab : a - b = 2 * x := by rw [hx]; ring
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hrepr : 1 - Complex.exp (((a - b : ℝ) : ℂ) * I) =
      ((2 * Real.sin x : ℝ) : ℂ) *
        (Complex.cos ((x - π / 2 : ℝ) : ℂ) + Complex.sin ((x - π / 2 : ℝ) : ℂ) * I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    apply Complex.ext
    · simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re, mul_re, ofReal_re, ofReal_im, add_re, add_im,
        mul_im, I_re, I_im]
      rw [hab, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq x]
    · simp only [sub_im, one_im, Complex.exp_ofReal_mul_I_im, mul_re, ofReal_re, ofReal_im, add_re, add_im,
        mul_im, I_re, I_im]
      rw [hab, Real.sin_two_mul]
      ring
  rw [hrepr, Complex.arg_mul_cos_add_sin_mul_I (by linarith) ⟨by linarith [Real.pi_pos], by linarith⟩]

/-- `arg (1 - e^{ia} conj e^{ib}) = (a - b)/2 + π/2` for `-2π < a - b < 0`. -/
theorem s20g_b_arg_neg {a b : ℝ} (h0 : a - b < 0) (h1 : -(2 * π) < a - b) :
    arg (1 - Complex.exp (a * I) * conj (Complex.exp (b * I))) = (a - b) / 2 + π / 2 := by
  rw [s20g_b_exp_mul_conj]
  set x := (a - b) / 2 with hx
  have hab : a - b = 2 * x := by rw [hx]; ring
  have hs : 0 < -Real.sin x := by
    rw [← Real.sin_neg]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hrepr : 1 - Complex.exp (((a - b : ℝ) : ℂ) * I) =
      ((-2 * Real.sin x : ℝ) : ℂ) *
        (Complex.cos ((x + π / 2 : ℝ) : ℂ) + Complex.sin ((x + π / 2 : ℝ) : ℂ) * I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    apply Complex.ext
    · simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re, mul_re, ofReal_re, ofReal_im, add_re, add_im,
        mul_im, I_re, I_im]
      rw [hab, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq x]
    · simp only [sub_im, one_im, Complex.exp_ofReal_mul_I_im, mul_re, ofReal_re, ofReal_im, add_re, add_im,
        mul_im, I_re, I_im]
      rw [hab, Real.sin_two_mul]
      ring
  rw [hrepr, Complex.arg_mul_cos_add_sin_mul_I (by linarith) ⟨by linarith, by linarith [Real.pi_pos]⟩]

/-- `e^{ia} conj e^{ia} = 1`. -/
theorem s20g_b_exp_mul_conj_self (a : ℝ) : Complex.exp (a * I) * conj (Complex.exp (a * I)) = 1 := by
  rw [s20g_b_exp_mul_conj, sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero]

/-- **Disc crossing theorem.**  Two paths in the closed unit disc, the first from `e^{iθ₁}` to `e^{iθ₂}`, the second
from `e^{iα}` to `e^{iβ}`, with `θ₁ < α < θ₂ < β < θ₁ + 2π` (alternating endpoints on the circle), each meeting the
circle only at its own endpoints, intersect.

*Truth*: suppose not; then `Φ s t = γ s - η t` never vanishes on `[0,1]²`.  Going around the boundary of the square,
the four sides `γ s - e^{iα}`, `e^{iθ₂} - η t`, `γ s - e^{iβ}` (reversed) and `e^{iθ₁} - η t` (reversed) take values
in the open half-planes `{Re (v conj u) < 0}` resp. `{Re (v conj u) > 0}` for the unit vector `u` involved (a point
`z ≠ u` of the closed disc has `Re (z conj u) < 1`).  So each side's log-lift change is a principal-branch difference
depending only on the corner values, and `e^{ia} - e^{ib} = 2i sin ((a - b)/2) e^{i(a + b)/2}` gives the total
`(θ₂ - θ₁)/2 - π + (β - α)/2 - π + (θ₁ - θ₂)/2 + (α - β)/2 = -2π`.  But the boundary loop contracts inside the square
(`H r t = Φ (r • p t)` for `p` running around `∂[0,1]²`), so its lift change is `0` (W3a).  Contradiction.  (For
non-alternating endpoints the same computation gives `0`, as it must.)

*Route*: `Path.extend`, `exists_continuousOn_log_lift` (W1a, Winding:43), `lift_change_eq_of_homotopy` (W3a,
Winding:197), `lift_sub_eq_log_sub_log` (W1e, Winding:116) after rotating each half-plane onto `{Re > 0}`,
`lift_change_eq_of_lifts` (W1c, Winding:79). -/
theorem s20g_crossing {θ₁ α θ₂ β : ℝ} (h₁ : θ₁ < α) (h₂ : α < θ₂) (h₃ : θ₂ < β) (h₄ : β < θ₁ + 2 * π)
    (γ : Path (Complex.exp (θ₁ * I)) (Complex.exp (θ₂ * I))) (η : Path (Complex.exp (α * I)) (Complex.exp (β * I)))
    (hγ : ∀ t, γ t ∈ unitDisc ∨ γ t = Complex.exp (θ₁ * I) ∨ γ t = Complex.exp (θ₂ * I))
    (hη : ∀ t, η t ∈ unitDisc ∨ η t = Complex.exp (α * I) ∨ η t = Complex.exp (β * I)) :
    ∃ s t, γ s = η t := by
  by_contra hne
  push Not at hne
  have hball : ∀ {a b : ℝ} (p : Path (Complex.exp (a * I)) (Complex.exp (b * I))),
      (∀ t, p t ∈ unitDisc ∨ p t = Complex.exp (a * I) ∨ p t = Complex.exp (b * I)) →
        ∀ s, ‖p.extend s‖ ≤ 1 := by
    intro a b p hp s
    rcases hp (projIcc 0 1 zero_le_one s) with h | h | h
    · exact (mem_ball_zero_iff.1 h).le
    · show ‖p (projIcc 0 1 zero_le_one s)‖ ≤ 1
      rw [h, Complex.norm_exp_ofReal_mul_I]
    · show ‖p (projIcc 0 1 zero_le_one s)‖ ≤ 1
      rw [h, Complex.norm_exp_ofReal_mul_I]
  have hsc : IsSimplyConnected (univ : Set (ℝ × ℝ)) := by
    have : ContractibleSpace ↥(univ : Set (ℝ × ℝ)) := convex_univ.contractibleSpace univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  have hΦc : Continuous fun p : ℝ × ℝ => γ.extend p.1 - η.extend p.2 :=
    (γ.continuous_extend.comp continuous_fst).sub (η.continuous_extend.comp continuous_snd)
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ hΦc.continuousOn
    (by rintro ⟨p, -, hp⟩; exact hne _ _ (sub_eq_zero.1 hp))
  have hL : Continuous L := continuousOn_univ.1 hLc
  have he : ∀ p, Complex.exp (L p) = γ.extend p.1 - η.extend p.2 := fun p => hLe (mem_univ p)
  have hu : ∀ a : ℝ, ‖Complex.exp (a * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have hw : ∀ a : ℝ, conj (Complex.exp (a * I)) ≠ 0 := fun a => (map_ne_zero _).2 (Complex.exp_ne_zero _)
  have S1 : (L (1, 0) - L (0, 0)).im = arg (1 - γ.extend 1 * conj (Complex.exp (α * I))) -
      arg (1 - γ.extend 0 * conj (Complex.exp (α * I))) :=
    s20g_b_side (L := fun s => L (s, 0)) (hu α) (neg_ne_zero.2 (hw α))
      (hL.comp (continuous_id.prodMk continuous_const)).continuousOn γ.continuous_extend.continuousOn
      (fun t _ => hball γ hγ t) (fun t _ h => hne (projIcc 0 1 zero_le_one t) 0 (by rw [η.source]; exact h))
      (fun t _ => by
        rw [he, η.extend_zero]
        linear_combination s20g_b_exp_mul_conj_self α)
  have S2 : (L (1, 1) - L (1, 0)).im = arg (1 - η.extend 1 * conj (Complex.exp (θ₂ * I))) -
      arg (1 - η.extend 0 * conj (Complex.exp (θ₂ * I))) :=
    s20g_b_side (L := fun t => L (1, t)) (hu θ₂) (hw θ₂)
      (hL.comp (continuous_const.prodMk continuous_id)).continuousOn η.continuous_extend.continuousOn
      (fun t _ => hball η hη t)
      (fun t _ h => hne 1 (projIcc 0 1 zero_le_one t) (by rw [γ.target]; exact h.symm))
      (fun t _ => by
        rw [he, γ.extend_one]
        linear_combination s20g_b_exp_mul_conj_self θ₂)
  have S3 : (L (1, 1) - L (0, 1)).im = arg (1 - γ.extend 1 * conj (Complex.exp (β * I))) -
      arg (1 - γ.extend 0 * conj (Complex.exp (β * I))) :=
    s20g_b_side (L := fun s => L (s, 1)) (hu β) (neg_ne_zero.2 (hw β))
      (hL.comp (continuous_id.prodMk continuous_const)).continuousOn γ.continuous_extend.continuousOn
      (fun t _ => hball γ hγ t) (fun t _ h => hne (projIcc 0 1 zero_le_one t) 1 (by rw [η.target]; exact h))
      (fun t _ => by
        rw [he, η.extend_one]
        linear_combination s20g_b_exp_mul_conj_self β)
  have S4 : (L (0, 1) - L (0, 0)).im = arg (1 - η.extend 1 * conj (Complex.exp (θ₁ * I))) -
      arg (1 - η.extend 0 * conj (Complex.exp (θ₁ * I))) :=
    s20g_b_side (L := fun t => L (0, t)) (hu θ₁) (hw θ₁)
      (hL.comp (continuous_const.prodMk continuous_id)).continuousOn η.continuous_extend.continuousOn
      (fun t _ => hball η hη t)
      (fun t _ h => hne 0 (projIcc 0 1 zero_le_one t) (by rw [γ.source]; exact h.symm))
      (fun t _ => by
        rw [he, γ.extend_zero]
        linear_combination s20g_b_exp_mul_conj_self θ₁)
  rw [γ.extend_one, γ.extend_zero, s20g_b_arg_pos (by linarith) (by linarith),
    s20g_b_arg_neg (by linarith) (by linarith)] at S1
  rw [η.extend_one, η.extend_zero, s20g_b_arg_pos (by linarith) (by linarith),
    s20g_b_arg_neg (by linarith) (by linarith)] at S2
  rw [γ.extend_one, γ.extend_zero, s20g_b_arg_neg (a := θ₂) (by linarith) (by linarith),
    s20g_b_arg_neg (a := θ₁) (by linarith) (by linarith)] at S3
  rw [η.extend_one, η.extend_zero, s20g_b_arg_pos (a := β) (by linarith) (by linarith),
    s20g_b_arg_pos (a := α) (by linarith) (by linarith)] at S4
  have key : (L (1, 0) - L (0, 0)).im + (L (1, 1) - L (1, 0)).im - (L (1, 1) - L (0, 1)).im -
      (L (0, 1) - L (0, 0)).im = 0 := by
    simp only [sub_im]
    ring
  rw [S1, S2, S3, S4] at key
  linarith [Real.pi_pos]

/-- **Cluster sets are points** (W2a, the core of `s20g_ext_continuous`).  For a conformal map `f` of `Δ` onto a
bounded domain `Ω` satisfying clause (ii′) of `s20g_QLC`, the cluster set at every `z₀ ∈ ∂Δ` is a singleton.  Wolff's
circles `σ_n = f(Δ ∩ sphere z₀ ρ_n)` shrink to points; the points `f((1 - ρ_n) z₀)` accumulate at some `w* ∈ ∂Ω`, and
(ii′) at `w*` joins a point of `f(Δ ∩ ball z₀ ρ_n)` near a second cluster value to `f 0` off a disc about `w*` that
contains `σ_n`; pulled back by `f⁻¹` this path must cross the circle `sphere z₀ ρ_n`, a contradiction. -/
theorem s20g_a_cluster {Ω : Set ℂ} (hΩbdd : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω)
    (hq : ∀ w ∈ frontier Ω, ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ p ∈ Ω \ ball w R, ∀ q ∈ Ω \ ball w R,
      JoinedIn (Ω \ ball w ρ) p q) {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) :
    ∃ w, clusterSet f unitDisc z₀ = {w} := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  obtain ⟨ρ, -, hρpos, hρtendsto, hℓtendsto⟩ := wolff_length_area hΩbdd hf hz₀
  set σ : ℕ → Set ℂ := fun n => f '' (unitDisc ∩ sphere z₀ (ρ n)) with hσ
  have hσΩ : ∀ n, σ n ⊆ Ω := fun n => by
    rw [hσ, ← hf.2.2]
    exact image_mono inter_subset_left
  -- `diam σ n → 0`
  have hdiamσ0 : Tendsto (fun n => Metric.diam (σ n)) atTop (𝓝 0) := by
    have hev1 : ∀ᶠ n in atTop, ρ n < 1 := hρtendsto.eventually_lt_const one_pos
    have hev2 : ∀ᶠ n in atTop, arcLength f z₀ (ρ n) ≠ ⊤ := by
      filter_upwards [hℓtendsto.eventually_lt_const one_pos] with n hn
      exact hn.ne_top
    have hℓ0 : Tendsto (fun n => (arcLength f z₀ (ρ n)).toReal) atTop (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hℓtendsto
      rw [ENNReal.toReal_zero] at h1
      exact h1
    have hle : ∀ᶠ n in atTop, Metric.diam (σ n) ≤ (arcLength f z₀ (ρ n)).toReal := by
      filter_upwards [hev1, hev2] with n h1 h2
      obtain ⟨-, -, -, -, hd, -⟩ := exists_ends_of_circleArc_image hΩbdd hf hz₀ (hρpos n) h1 h2
      exact hd
    exact squeeze_zero' (Eventually.of_forall fun n => Metric.diam_nonneg) hle hℓ0
  -- the cluster set is nonempty
  have hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hΩbdd
    refine ⟨R, fun z hz => ?_⟩
    have h1 : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    simpa using hR h1
  obtain ⟨hne, -, -⟩ := clusterSet_isCompact_isConnected (mem_sphere_zero_iff_norm.2 hz₀) hf.1.continuousOn hbdd
  suffices hsub : (clusterSet f unitDisc z₀).Subsingleton by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hsub.eq_singleton_of_mem hw⟩
  intro w₁ hw₁ w₂ hw₂
  by_contra hne12
  have hd : 0 < ‖w₁ - w₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne12)
  -- the points `c n = f ((1 - ρ n) z₀)` (for small `ρ n`) accumulate at a boundary point `w*`
  set τ : ℕ → ℝ := fun n => min (ρ n) (1 / 2) with hτ
  have hτ0 : Tendsto τ atTop (𝓝 0) := by
    have h1 := hρtendsto.min (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    rwa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h1
  set z : ℕ → ℂ := fun n => ((1 - τ n : ℝ) : ℂ) * z₀ with hz
  have hτpos : ∀ n, 0 < τ n := fun n => lt_min (hρpos n) (by norm_num)
  have hτhalf : ∀ n, τ n ≤ 1 / 2 := fun n => min_le_right _ _
  have hznorm : ∀ n, ‖z n‖ = 1 - τ n := fun n => by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hτhalf n]), hz₀, mul_one]
  have hzΔ : ∀ n, z n ∈ unitDisc := fun n => by
    rw [unitDisc, mem_ball_zero_iff, hznorm]
    linarith [hτpos n]
  have hzdist : ∀ n, ‖z n - z₀‖ = τ n := fun n => by
    rw [hz, show ((1 - τ n : ℝ) : ℂ) * z₀ - z₀ = ((-τ n : ℝ) : ℂ) * z₀ by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (hτpos n), hz₀, mul_one]
  have hzt : Tendsto z atTop (𝓝 z₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [hzdist] using hτ0
  have hcΩ : ∀ n, f (z n) ∈ closure Ω := fun n => subset_closure (hf.mapsTo (hzΔ n))
  obtain ⟨ws, hwscl, φ, hφ, hφt⟩ := hΩbdd.isCompact_closure.tendsto_subseq hcΩ
  have hwsΩ : ws ∉ Ω := tendsto_boundary_of_isConformalOnto hf hz₀ (fun m => hzΔ (φ m))
    (hzt.comp hφ.tendsto_atTop) hφt
  have hwsfr : ws ∈ frontier Ω := by
    rw [hΩo.frontier_eq]
    exact ⟨hwscl, hwsΩ⟩
  have h0Δ : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hf0Ω : f 0 ∈ Ω := hf.mapsTo h0Δ
  have hf0ws : 0 < ‖f 0 - ws‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hwsΩ (h ▸ hf0Ω))
  set R := min (‖w₁ - w₂‖ / 4) ‖f 0 - ws‖ with hR
  have hR0 : 0 < R := lt_min (by positivity) hf0ws
  obtain ⟨ρ', hρ'0, hjoin⟩ := hq ws hwsfr R hR0
  -- a good index `n = φ m`
  have hev : ∀ᶠ m in atTop, ρ (φ m) < 1 / 2 ∧ Metric.diam (σ (φ m)) < ρ' / 2 ∧
      dist (f (z (φ m))) ws < ρ' / 2 :=
    ((hρtendsto.comp hφ.tendsto_atTop).eventually_lt_const (by norm_num)).and
      (((hdiamσ0.comp hφ.tendsto_atTop).eventually_lt_const (by positivity)).and
        ((tendsto_iff_dist_tendsto_zero.1 hφt).eventually_lt_const (by positivity)))
  obtain ⟨m, hm1, hm2, hm3⟩ := hev.exists
  set n := φ m with hn
  have hτn : τ n = ρ n := min_eq_left hm1.le
  have hcσ : f (z n) ∈ σ n := ⟨z n, ⟨hzΔ n, by rw [mem_sphere, dist_eq_norm, hzdist, hτn]⟩, rfl⟩
  have hσball : σ n ⊆ ball ws ρ' := by
    intro x hx
    have h1 : dist x (f (z n)) ≤ Metric.diam (σ n) :=
      Metric.dist_le_diam_of_mem (hΩbdd.subset (hσΩ n)) hx hcσ
    rw [mem_ball]
    calc dist x ws ≤ dist x (f (z n)) + dist (f (z n)) ws := dist_triangle _ _ _
      _ < ρ' / 2 + ρ' / 2 := add_lt_add_of_le_of_lt (h1.trans hm2.le) hm3
      _ = ρ' := by ring
  -- a second cluster value far from `ws`, approximated inside `f (Δ ∩ ball z₀ (ρ n))`
  obtain ⟨w', hw'cl, hw'far⟩ : ∃ w' ∈ clusterSet f unitDisc z₀, ‖w₁ - w₂‖ / 2 ≤ ‖w' - ws‖ := by
    by_cases h : ‖w₁ - w₂‖ / 2 ≤ ‖w₁ - ws‖
    · exact ⟨w₁, hw₁, h⟩
    · refine ⟨w₂, hw₂, ?_⟩
      have h1 : ‖w₁ - w₂‖ ≤ ‖w₁ - ws‖ + ‖w₂ - ws‖ := by
        calc ‖w₁ - w₂‖ = ‖(w₁ - ws) - (w₂ - ws)‖ := by ring_nf
          _ ≤ ‖w₁ - ws‖ + ‖w₂ - ws‖ := norm_sub_le _ _
      linarith
  have hw'n : w' ∈ closure (f '' (unitDisc ∩ ball z₀ (ρ n))) := mem_iInter₂.1 hw'cl (ρ n) (hρpos n)
  obtain ⟨x, ⟨y, hy, rfl⟩, hxw⟩ := Metric.mem_closure_iff.1 hw'n (‖w₁ - w₂‖ / 4) (by positivity)
  have hxR : f y ∈ Ω \ ball ws R := by
    refine ⟨hf.mapsTo hy.1, fun h => ?_⟩
    rw [mem_ball, dist_eq_norm] at h
    have h1 : ‖w' - ws‖ ≤ ‖w' - f y‖ + ‖f y - ws‖ := by
      calc ‖w' - ws‖ = ‖(w' - f y) + (f y - ws)‖ := by ring_nf
        _ ≤ ‖w' - f y‖ + ‖f y - ws‖ := norm_add_le _ _
    rw [dist_eq_norm] at hxw
    have h2 : R ≤ ‖w₁ - w₂‖ / 4 := min_le_left _ _
    linarith
  have h0R : f 0 ∈ Ω \ ball ws R := by
    refine ⟨hf0Ω, fun h => ?_⟩
    rw [mem_ball, dist_eq_norm] at h
    have h2 : R ≤ ‖f 0 - ws‖ := min_le_right _ _
    linarith
  obtain ⟨γ, hγ⟩ := hjoin (f y) hxR (f 0) h0R
  -- pull back by `g = f⁻¹` and cross the circle `sphere z₀ (ρ n)`
  set g := Function.invFunOn f unitDisc with hg
  have hgconf : IsConformalOnto g Ω unitDisc := hf.symm isOpen_ball
  have hgc : ContinuousOn g Ω := hgconf.1.continuousOn
  have hgf : ∀ v ∈ unitDisc, g (f v) = v := fun v hv => hf.2.1.leftInvOn_invFunOn hv
  have hfg : ∀ v ∈ Ω, f (g v) = v := fun v hv => by
    rw [← hf.2.2] at hv
    exact Function.invFunOn_eq hv
  have hhc : Continuous fun t => ‖g (γ t) - z₀‖ :=
    ((hgc.comp_continuous γ.continuous fun t => (hγ t).1).sub continuous_const).norm
  have h0 : ‖g (γ 0) - z₀‖ ≤ ρ n := by
    rw [γ.source, hgf y hy.1]
    have h1 := hy.2
    rw [mem_ball, dist_eq_norm] at h1
    exact h1.le
  have h1 : ρ n ≤ ‖g (γ 1) - z₀‖ := by
    rw [γ.target, hgf 0 h0Δ, zero_sub, norm_neg, hz₀]
    linarith
  obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hhc ⟨h0, h1⟩
  have hgt : g (γ t) ∈ unitDisc ∩ sphere z₀ (ρ n) :=
    ⟨hgconf.mapsTo (hγ t).1, by rw [mem_sphere, dist_eq_norm]; exact ht⟩
  have hmem : γ t ∈ σ n := ⟨g (γ t), hgt, hfg _ (hγ t).1⟩
  exact (hγ t).2 (hσball hmem)

/-- **W2a: continuous extension.**  A conformal map of `Δ` onto a bounded domain `Ω` satisfying clause (ii′) of
`s20g_QLC` (the only clause used; generalized in place 2026-09-27 so that Theorem C1 can use it) extends
continuously to the closed disc (the conclusion of `exists_continuousOn_extension_of_isJordanCurve_frontier`, C8,
with clause (ii′) in place of the Jordan hypothesis).

*Truth*: fix `ζ ∈ ∂Δ`.  Wolff gives `ρ_n ↓ 0` with `diam σ_n → 0`, `σ_n = f(Δ ∩ sphere ζ ρ_n)`.  If the cluster set at
`ζ` contained `w₁ ≠ w₂`: pick `c_n ∈ σ_n`; `c_n = f z_n` with `z_n → ζ`, so along a subsequence `c_n → w* ∈ ∂Ω`.
`V_n = f(Δ ∩ ball ζ ρ_n)` has `w₁, w₂` in its closure, hence contains `x_n` with `‖x_n - c_n‖ ≥ ‖w₁ - w₂‖/3`, while
`f 0 ∈ f(Δ ∖ closedBall ζ ρ_n)` stays at distance `≥ dist (f 0, ∂Ω)/2`.  (ii′) at `w*` with a fixed small `R` joins
`x_n` to `f 0` in `Ω ∖ ball w* ρ`, which misses `σ_n` for large `n`; pulled back by `f⁻¹` this joins
`Δ ∩ ball ζ ρ_n` to `Δ ∖ closedBall ζ ρ_n` inside `Δ ∖ sphere ζ ρ_n`, impossible (intermediate values of `‖z - ζ‖`).
So every cluster set is a singleton, and the rest of C8's proof applies verbatim.

*Route*: `wolff_length_area` (Lemmas/Caratheodory), `exists_ends_of_circleArc_image` (CaratheodoryJordan:2580, the
diameter bound only), `clusterSet_isCompact_isConnected` (ClusterSets), `tendsto_boundary_of_isConformalOnto`
(CaratheodoryJordan:2042), `continuous_extension_iff_forall_clusterSet_subsingleton` (ClusterSets), the body of
`exists_continuousOn_extension_of_isJordanCurve_frontier` (C8, CaratheodoryJordan:3495). -/
theorem s20g_ext_continuous {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω)
    (hq : ∀ w ∈ frontier Ω, ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ p ∈ Ω \ ball w R, ∀ q ∈ Ω \ ball w R,
      JoinedIn (Ω \ ball w ρ) p q) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧
      F '' sphere (0 : ℂ) 1 ⊆ frontier Ω ∧ F '' closedBall 0 1 = closure Ω := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hall : ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ w, clusterSet f unitDisc ζ = {w} := fun ζ hζ =>
    s20g_a_cluster hΩ hf hq (mem_sphere_zero_iff_norm.1 hζ)
  obtain ⟨F, hFc, hFf⟩ := (continuous_extension_iff_forall_clusterSet_subsingleton hf.1).2 hall
  have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
  rw [hcl] at hFc
  -- `F ζ` is the cluster value at `ζ`
  have hFζeq : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ w, clusterSet f unitDisc ζ = {w} → F ζ = w := by
    intro ζ hζ w hw
    have hζmemcl : ζ ∈ closure unitDisc := hcl ▸ sphere_subset_closedBall hζ
    have hFcont' : ContinuousWithinAt F unitDisc ζ := (hFc ζ (hcl ▸ hζmemcl)).mono (hcl ▸ subset_closure)
    have hftend : Tendsto f (𝓝[unitDisc] ζ) (𝓝 (F ζ)) := by
      refine (show Tendsto F (𝓝[unitDisc] ζ) (𝓝 (F ζ)) from hFcont').congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hFf hz
    have hFζmemcs : F ζ ∈ clusterSet f unitDisc ζ := by
      rw [clusterSet]
      refine mem_iInter₂.2 fun r hr => ?_
      have hftend' : Tendsto f (𝓝[unitDisc ∩ ball ζ r] ζ) (𝓝 (F ζ)) :=
        hftend.mono_left (nhdsWithin_mono ζ inter_subset_left)
      exact mem_closure_image_of_tendsto_nhdsWithin
        (mem_closure_unitDisc_inter_ball (mem_sphere_zero_iff_norm.1 hζ) hr) hftend'
    rw [hw] at hFζmemcs
    exact hFζmemcs
  -- boundary values lie on `frontier Ω`
  have hFζfr : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ frontier Ω := by
    intro ζ hζ
    obtain ⟨w', hw'⟩ := hall ζ hζ
    rw [hFζeq ζ hζ w' hw', hΩo.frontier_eq]
    have hw'memcs : w' ∈ clusterSet f unitDisc ζ := hw' ▸ rfl
    have hw'mem_cl : w' ∈ closure Ω := by
      refine closure_mono ?_ (mem_iInter₂.1 hw'memcs 1 one_pos)
      rw [← hf.2.2]
      exact image_mono inter_subset_left
    have hw'notmem : w' ∉ Ω := by
      have hex : ∀ k : ℕ, ∃ z : ℂ, z ∈ unitDisc ∧ dist z ζ < 1 / ((k : ℝ) + 1) ∧
          dist (f z) w' < 1 / ((k : ℝ) + 1) := by
        intro k
        have hmem := mem_iInter₂.1 hw'memcs (1 / ((k : ℝ) + 1)) (by positivity)
        obtain ⟨y, ⟨z, hz, rfl⟩, hdy⟩ := Metric.mem_closure_iff.1 hmem (1 / ((k : ℝ) + 1)) (by positivity)
        exact ⟨z, hz.1, hz.2, by rwa [dist_comm] at hdy⟩
      choose z hzmem hzdist hfzdist using hex
      have hz0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hzζ : Tendsto z atTop (𝓝 ζ) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => (hzdist k).le) hz0
      have hfzw' : Tendsto (fun k => f (z k)) atTop (𝓝 w') := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => (hfzdist k).le) hz0
      exact tendsto_boundary_of_isConformalOnto hf (mem_sphere_zero_iff_norm.1 hζ) hzmem hzζ hfzw'
    exact ⟨hw'mem_cl, hw'notmem⟩
  refine ⟨F, hFc, hFf, ?_, ?_⟩
  · rintro w ⟨ζ, hζ, rfl⟩
    exact hFζfr ζ hζ
  · apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      rcases eq_or_lt_of_le (mem_closedBall.1 hz) with heq | hlt
      · exact frontier_subset_closure (hFζfr z heq)
      · have hzud : z ∈ unitDisc := hlt
        rw [hFf hzud]
        exact subset_closure (hf.mapsTo hzud)
    · have hwsub : Ω ⊆ F '' closedBall (0 : ℂ) 1 := by
        rw [← hf.2.2]
        rintro y ⟨z, hz, rfl⟩
        exact ⟨z, ball_subset_closedBall hz, hFf hz⟩
      exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hFc).isClosed.closure_subset_iff.2 hwsub

/-- `e^{ia} ≠ e^{ib}` for `0 < b - a < 2π`. -/
theorem s20g_b_exp_ne {a b : ℝ} (h0 : 0 < b - a) (h1 : b - a < 2 * π) :
    Complex.exp (a * I) ≠ Complex.exp (b * I) := by
  intro h
  have h2 : Complex.exp (((b - a : ℝ) : ℂ) * I) = 1 := by
    rw [← s20g_b_exp_mul_conj, ← h, s20g_b_exp_mul_conj_self]
  have h3 : Real.cos (b - a) = 1 := by
    have := congrArg Complex.re h2
    rwa [Complex.exp_ofReal_mul_I_re, one_re] at this
  have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) h1).1 h3
  linarith

/-- Two distinct points of the unit circle are `e^{iθ₁}`, `e^{iθ₂}` with `θ₁ < θ₂ < θ₁ + 2π` (a copy of
`s20g_angles`, which comes later in the file). -/
theorem s20g_b_angles {ζ₁ ζ₂ : ℂ} (h₁ : ‖ζ₁‖ = 1) (h₂ : ‖ζ₂‖ = 1) (hne : ζ₁ ≠ ζ₂) :
    ∃ θ₁ θ₂ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₁ + 2 * π ∧ Complex.exp (θ₁ * I) = ζ₁ ∧ Complex.exp (θ₂ * I) = ζ₂ := by
  have he : ∀ ζ : ℂ, ‖ζ‖ = 1 → Complex.exp ((arg ζ : ℂ) * I) = ζ := fun ζ hζ => by
    have h := Complex.norm_mul_exp_arg_mul_I ζ
    rwa [hζ, Complex.ofReal_one, one_mul] at h
  have hne' : arg ζ₁ ≠ arg ζ₂ := fun h => hne (by rw [← he ζ₁ h₁, ← he ζ₂ h₂, h])
  have hb₁ := Complex.neg_pi_lt_arg ζ₁
  have hb₂ := Complex.arg_le_pi ζ₁
  have hc₁ := Complex.neg_pi_lt_arg ζ₂
  have hc₂ := Complex.arg_le_pi ζ₂
  rcases lt_or_gt_of_ne hne' with h | h
  · exact ⟨arg ζ₁, arg ζ₂, h, by linarith, he ζ₁ h₁, he ζ₂ h₂⟩
  · refine ⟨arg ζ₁, arg ζ₂ + 2 * π, by linarith, by linarith, he ζ₁ h₁, ?_⟩
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, he ζ₂ h₂]
    have : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact Complex.exp_two_pi_mul_I
    rw [this, mul_one]

/-- Radial continuity at a point of the circle: a map continuous on the closed disc stays in an open set `U` about
its value at `e^{ia}` along the radius `[r, 1] e^{ia}` for some `0 ≤ r < 1`. -/
theorem s20g_b_radial {X : Type*} [TopologicalSpace X] {G : ℂ → X} (hG : ContinuousOn G (closedBall 0 1))
    (a : ℝ) {U : Set X} (hU : IsOpen U) (ha : G (Complex.exp (a * I)) ∈ U) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (a * I)) ∈ U := by
  have hζ : Complex.exp (a * I) ∈ closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.2 (Complex.norm_exp_ofReal_mul_I a).le
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 ((hG _ hζ).preimage_mem_nhdsWithin (hU.mem_nhds ha))
  refine ⟨max 0 (1 - ε / 2), le_max_left _ _, max_lt one_pos (by linarith), fun t ht1 ht2 => hsub ⟨?_, ?_⟩⟩
  · have ht : 1 - ε / 2 ≤ t := le_trans (le_max_right _ _) ht1
    rw [mem_ball, dist_eq_norm, show (t : ℂ) * Complex.exp (a * I) - Complex.exp (a * I) =
      ((t - 1 : ℝ) : ℂ) * Complex.exp (a * I) by push_cast; ring, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  · have ht : 0 ≤ t := le_trans (le_max_left _ _) ht1
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht]
    exact ht2

/-- A path from `e^{ia}` to `e^{ib}` through the disc: the radius from `e^{ia}` to `r e^{ia}`, a middle path in the
disc, and the radius from `r e^{ib}` to `e^{ib}`; it meets the circle only at its ends and keeps `G` in `P`. -/
theorem s20g_b_join {X : Type*} [TopologicalSpace X] {G : ℂ → X} {P : Set X} {a b r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (ha : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (a * I)) ∈ P)
    (hb : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (b * I)) ∈ P)
    (hm : JoinedIn (unitDisc ∩ G ⁻¹' P) (r * Complex.exp (a * I)) (r * Complex.exp (b * I))) :
    JoinedIn {z | (z ∈ unitDisc ∨ z = Complex.exp (a * I) ∨ z = Complex.exp (b * I)) ∧ G z ∈ P}
      (Complex.exp (a * I)) (Complex.exp (b * I)) := by
  have rad : ∀ c : ℝ, (∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (c * I)) ∈ P) →
      JoinedIn {z | (z ∈ unitDisc ∨ z = Complex.exp (c * I)) ∧ G z ∈ P} (Complex.exp (c * I))
        (r * Complex.exp (c * I)) := by
    intro c hc
    refine JoinedIn.ofLine (f := fun s : ℝ => ((1 - s + s * r : ℝ) : ℂ) * Complex.exp (c * I))
      (by fun_prop) (by simp) (by simp) ?_
    rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have hl : r ≤ 1 - s + s * r := by nlinarith
    have hu : 1 - s + s * r ≤ 1 := by nlinarith
    refine ⟨?_, hc _ hl hu⟩
    rcases hu.lt_or_eq with h | h
    · left
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact h
    · right
      simp only [h, Complex.ofReal_one, one_mul]
  refine ((rad a ha).mono ?_).trans ((hm.mono ?_).trans ((rad b hb).symm.mono ?_))
  · exact fun z hz => ⟨hz.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hz.2⟩
  · exact fun z hz => ⟨Or.inl hz.1, hz.2⟩
  · exact fun z hz => ⟨hz.1.elim Or.inl (fun h => Or.inr (Or.inr h)), hz.2⟩

/-- The crossing theorem for sets joining alternating points of the circle: they meet. -/
theorem s20g_b_cross_sets {θ₁ α θ₂ β : ℝ} (h₁ : θ₁ < α) (h₂ : α < θ₂) (h₃ : θ₂ < β) (h₄ : β < θ₁ + 2 * π)
    {S T : Set ℂ} (hS : JoinedIn S (Complex.exp (θ₁ * I)) (Complex.exp (θ₂ * I)))
    (hT : JoinedIn T (Complex.exp (α * I)) (Complex.exp (β * I)))
    (hS' : ∀ z ∈ S, z ∈ unitDisc ∨ z = Complex.exp (θ₁ * I) ∨ z = Complex.exp (θ₂ * I))
    (hT' : ∀ z ∈ T, z ∈ unitDisc ∨ z = Complex.exp (α * I) ∨ z = Complex.exp (β * I)) : (S ∩ T).Nonempty := by
  obtain ⟨s, t, hst⟩ := s20g_crossing h₁ h₂ h₃ h₄ hS.somePath hT.somePath
    (fun t => hS' _ (hS.somePath_mem t)) (fun t => hT' _ (hT.somePath_mem t))
  exact ⟨_, hS.somePath_mem s, hst ▸ hT.somePath_mem t⟩

/-- On an open arc of the circle the extension of a conformal map of `Δ` is not constant. -/
theorem s20g_b_arc_ne {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {F : ℂ → ℂ}
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc) {a b : ℝ} (hab : a < b)
    (hba : b < a + 2 * π) (w : ℂ) : ∃ α ∈ Ioo a b, F (Complex.exp (α * I)) ≠ w := by
  by_contra hcon
  push Not at hcon
  have hAs : (fun x : ℝ => Complex.exp (x * I)) '' Ioo a b ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I x)
  have hAn : ((fun x : ℝ => Complex.exp (x * I)) '' Ioo a b).Nontrivial :=
    ⟨_, ⟨a + (b - a) / 3, ⟨by linarith, by linarith⟩, rfl⟩, _,
      ⟨a + 2 * (b - a) / 3, ⟨by linarith, by linarith⟩, rfl⟩, s20g_b_exp_ne (by linarith) (by linarith)⟩
  have hAc : IsPreconnected ((fun x : ℝ => Complex.exp (x * I)) '' Ioo a b) :=
    isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => Complex.exp (x * I)).continuousOn
  have hsub : unitDisc ∪ (fun x : ℝ => Complex.exp (x * I)) '' Ioo a b ⊆ closedBall (0 : ℂ) 1 :=
    union_subset ball_subset_closedBall (hAs.trans sphere_subset_closedBall)
  have hconst := eqOn_const_of_eqOn_const_on_arc hAs hAn hAc (hf.1.congr hFf) (hFc.mono hsub)
    (by rintro _ ⟨x, hx, rfl⟩; exact hcon x hx)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h1 : (1 / 2 : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff]
    norm_num
  have h01 := hf.2.1 h0 h1 (by rw [← hFf h0, ← hFf h1, hconst h0, hconst h1])
  norm_num at h01

/-- **W2b: injectivity of the extension** (the analogue of C9, `injOn_extension_of_isJordanCurve_frontier`, with
`s20g_QLC Ω` in place of the Jordan hypothesis).

*Truth*: interior points go to `Ω`, circle points to `∂Ω`, `f` is injective; so let `F ζ₁ = F ζ₂ = w` with
`ζ_j = e^{iθ_j}`, `θ₁ < θ₂ < θ₁ + 2π`.  `F` is not `≡ w` on either open arc between them (else `f ≡ w` on `Δ` by
`eqOn_const_of_eqOn_const_on_arc`), so there are `α ∈ (θ₁, θ₂)`, `β ∈ (θ₂, θ₁ + 2π)` with `b₁ = F e^{iα} ≠ w`,
`b₂ = F e^{iβ} ≠ w`.  With `R = min ‖b_i - w‖/2`: (ii′) at `w` gives `ρ₀`; (i′) at `w` with `ε = min ρ₀ R` gives
`δ ≤ ε`.  For `r < 1` near `1`, `F (t ζ_j) ∈ ball w δ` and `‖F (t e^{iα}) - w‖, ‖F (t e^{iβ}) - w‖ ≥ R` for
`t ∈ [r, 1]`.  Join `f (r ζ₁)`, `f (r ζ₂)` in `Ω ∩ ball w ε` and `f (r e^{iα})`, `f (r e^{iβ})` in `Ω ∖ ball w ρ₀`;
pulled back by `f⁻¹` and completed by radial segments these are paths as in `s20g_crossing`, whose `F`-images lie in
`ball w ε` resp. outside it.  So they are disjoint: contradiction.

*Route*: `s20g_crossing`, `eqOn_const_of_eqOn_const_on_arc` (ClusterSets), `IsConformalOnto.symm`, `Path.trans`,
`Path.map'`, the case split of C9 (CaratheodoryJordan:4334). -/
theorem s20g_ext_injOn {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hq : s20g_QLC Ω) {F : ℂ → ℂ} (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) (hFs : F '' sphere (0 : ℂ) 1 ⊆ frontier Ω) : InjOn F (closedBall 0 1) := by
  have _hb := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hin : ∀ z : ℂ, ‖z‖ < 1 → F z ∈ Ω := fun z hz => by
    rw [hFf (mem_ball_zero_iff.2 hz)]
    exact hf.mapsTo (mem_ball_zero_iff.2 hz)
  have hon : ∀ z : ℂ, ‖z‖ = 1 → F z ∉ Ω := fun z hz h => by
    have h' := hFs ⟨z, mem_sphere_zero_iff_norm.2 hz, rfl⟩
    rw [hΩo.frontier_eq] at h'
    exact h'.2 h
  intro z₁ hz₁ z₂ hz₂ hF
  by_contra hne
  rcases (mem_closedBall_zero_iff.1 hz₁).lt_or_eq with h₁ | h₁ <;>
    rcases (mem_closedBall_zero_iff.1 hz₂).lt_or_eq with h₂ | h₂
  · refine hne (hf.2.1 (mem_ball_zero_iff.2 h₁) (mem_ball_zero_iff.2 h₂) ?_)
    rw [← hFf (mem_ball_zero_iff.2 h₁), ← hFf (mem_ball_zero_iff.2 h₂), hF]
  · exact hon z₂ h₂ (hF ▸ hin z₁ h₁)
  · exact hon z₁ h₁ (hF.symm ▸ hin z₂ h₂)
  -- both ends on the circle
  obtain ⟨θ₁, θ₂, h12, h21, he₁, he₂⟩ := s20g_b_angles h₁ h₂ hne
  set w := F z₁ with hw_def
  have hw : w ∈ frontier Ω := hFs ⟨z₁, mem_sphere_zero_iff_norm.2 h₁, rfl⟩
  have hFθ₁ : F (Complex.exp (θ₁ * I)) = w := by rw [he₁]
  have hFθ₂ : F (Complex.exp (θ₂ * I)) = w := by rw [he₂, ← hF]
  obtain ⟨α, hα, hFα⟩ := s20g_b_arc_ne hf hFc hFf h12 h21 w
  obtain ⟨β, hβ, hFβ⟩ := s20g_b_arc_ne hf hFc hFf h21 (by linarith) w
  set bα := F (Complex.exp (α * I)) with hbα
  set bβ := F (Complex.exp (β * I)) with hbβ
  have hdα : 0 < ‖bα - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hFα)
  have hdβ : 0 < ‖bβ - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hFβ)
  set R := min ‖bα - w‖ ‖bβ - w‖ / 2 with hR_def
  have hR : 0 < R := div_pos (lt_min hdα hdβ) two_pos
  have hRα : R ≤ ‖bα - w‖ / 2 := by
    have := min_le_left ‖bα - w‖ ‖bβ - w‖
    linarith
  have hRβ : R ≤ ‖bβ - w‖ / 2 := by
    have := min_le_right ‖bα - w‖ ‖bβ - w‖
    linarith
  obtain ⟨hi, hii⟩ := hq w hw
  obtain ⟨ρ, hρ, hρj⟩ := hii R hR
  set ε := min ρ R with hε_def
  have hε : 0 < ε := lt_min hρ hR
  have hερ : ε ≤ ρ := min_le_left _ _
  have hεR : ε ≤ R := min_le_right _ _
  obtain ⟨δ, hδ, hδj⟩ := hi ε hε
  set δ' := min δ ε with hδ'_def
  have hδ' : 0 < δ' := lt_min hδ hε
  have hfar : ∀ b' p : ℂ, R ≤ ‖b' - w‖ / 2 → p ∈ ball b' (‖b' - w‖ / 2) → R ≤ ‖p - w‖ := by
    intro b' p hb' hp
    rw [mem_ball, dist_eq_norm] at hp
    have h1 := norm_sub_le_norm_sub_add_norm_sub b' p w
    rw [norm_sub_rev b' p] at h1
    linarith
  obtain ⟨r₁, hr₁0, hr₁1, hr₁⟩ := s20g_b_radial hFc θ₁ (isOpen_ball (x := w) (ε := δ'))
    (by rw [hFθ₁]; exact mem_ball_self hδ')
  obtain ⟨r₂, -, hr₂1, hr₂⟩ := s20g_b_radial hFc θ₂ (isOpen_ball (x := w) (ε := δ'))
    (by rw [hFθ₂]; exact mem_ball_self hδ')
  obtain ⟨r₃, -, hr₃1, hr₃⟩ := s20g_b_radial hFc α (isOpen_ball (x := bα) (ε := ‖bα - w‖ / 2))
    (mem_ball_self (by linarith))
  obtain ⟨r₄, -, hr₄1, hr₄⟩ := s20g_b_radial hFc β (isOpen_ball (x := bβ) (ε := ‖bβ - w‖ / 2))
    (mem_ball_self (by linarith))
  set r := max (max r₁ r₂) (max r₃ r₄) with hr_def
  have hrr₁ : r₁ ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hrr₂ : r₂ ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
  have hrr₃ : r₃ ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrr₄ : r₄ ≤ r := le_trans (le_max_right _ _) (le_max_right _ _)
  have hr0 : 0 ≤ r := le_trans hr₁0 hrr₁
  have hr1 : r < 1 := max_lt (max_lt hr₁1 hr₂1) (max_lt hr₃1 hr₄1)
  have hrD : ∀ c : ℝ, (r : ℂ) * Complex.exp (c * I) ∈ unitDisc := fun c => by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  -- the inverse of `f`
  have hg : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hgc : ContinuousOn (Function.invFunOn f unitDisc) Ω := hg.1.continuousOn
  have hgf : ∀ z ∈ unitDisc, Function.invFunOn f unitDisc (f z) = z := fun z hz =>
    hf.2.1.leftInvOn_invFunOn hz
  have hFg : ∀ p ∈ Ω, Function.invFunOn f unitDisc p ∈ unitDisc ∧ F (Function.invFunOn f unitDisc p) = p := by
    intro p hp
    have hp' : p ∈ f '' unitDisc := hf.2.2.symm ▸ hp
    refine ⟨hg.mapsTo hp, ?_⟩
    rw [hFf (hg.mapsTo hp)]
    exact Function.invFunOn_eq hp'
  have hfr : ∀ c : ℝ, f ((r : ℂ) * Complex.exp (c * I)) = F ((r : ℂ) * Complex.exp (c * I)) := fun c =>
    (hFf (hrD c)).symm
  -- `Λ`: from `e^{iθ₁}` to `e^{iθ₂}` with `F`-image in `ball w ε`
  have hΛr : ∀ (c r' : ℝ), r' ≤ r → (∀ t : ℝ, r' ≤ t → t ≤ 1 → F (t * Complex.exp (c * I)) ∈ ball w δ') →
      ∀ t : ℝ, r ≤ t → t ≤ 1 → F (t * Complex.exp (c * I)) ∈ ball w ε := fun c r' hr' h t ht1 ht2 =>
    ball_subset_ball (min_le_right _ _) (h t (le_trans hr' ht1) ht2)
  have hΛm : JoinedIn (unitDisc ∩ F ⁻¹' ball w ε) (r * Complex.exp (θ₁ * I)) (r * Complex.exp (θ₂ * I)) := by
    have hm₁ : f ((r : ℂ) * Complex.exp (θ₁ * I)) ∈ Ω ∩ ball w δ :=
      ⟨hf.mapsTo (hrD θ₁), by rw [hfr]; exact ball_subset_ball (min_le_left _ _) (hr₁ r hrr₁ hr1.le)⟩
    have hm₂ : f ((r : ℂ) * Complex.exp (θ₂ * I)) ∈ Ω ∩ ball w δ :=
      ⟨hf.mapsTo (hrD θ₂), by rw [hfr]; exact ball_subset_ball (min_le_left _ _) (hr₂ r hrr₂ hr1.le)⟩
    have hj := (hδj _ hm₁ _ hm₂).map (hgc.mono inter_subset_left)
    rw [hgf _ (hrD θ₁), hgf _ (hrD θ₂)] at hj
    refine hj.mono ?_
    rintro _ ⟨p, ⟨hpΩ, hpB⟩, rfl⟩
    exact ⟨(hFg p hpΩ).1, by rw [mem_preimage, (hFg p hpΩ).2]; exact hpB⟩
  have hΛ := s20g_b_join hr0 hr1 (hΛr θ₁ r₁ hrr₁ hr₁) (hΛr θ₂ r₂ hrr₂ hr₂) hΛm
  -- `Γ`: from `e^{iα}` to `e^{iβ}` with `F`-image outside `ball w ε`
  have hΓr : ∀ (c r' : ℝ), r' ≤ r → R ≤ ‖F (Complex.exp (c * I)) - w‖ / 2 →
      (∀ t : ℝ, r' ≤ t → t ≤ 1 → F (t * Complex.exp (c * I)) ∈
        ball (F (Complex.exp (c * I))) (‖F (Complex.exp (c * I)) - w‖ / 2)) →
      ∀ t : ℝ, r ≤ t → t ≤ 1 → R ≤ ‖F (t * Complex.exp (c * I)) - w‖ := fun c r' hr' hc h t ht1 ht2 =>
    hfar _ _ hc (h t (le_trans hr' ht1) ht2)
  have hout : ∀ p : ℂ, R ≤ ‖p - w‖ → p ∈ (ball w ε)ᶜ := fun p hp h => by
    rw [mem_ball, dist_eq_norm] at h
    linarith
  have hΓm : JoinedIn (unitDisc ∩ F ⁻¹' (ball w ε)ᶜ) (r * Complex.exp (α * I)) (r * Complex.exp (β * I)) := by
    have hm₃ : f ((r : ℂ) * Complex.exp (α * I)) ∈ Ω \ ball w R := by
      refine ⟨hf.mapsTo (hrD α), fun h => ?_⟩
      rw [hfr, mem_ball, dist_eq_norm] at h
      have := hΓr α r₃ hrr₃ hRα hr₃ r le_rfl hr1.le
      linarith
    have hm₄ : f ((r : ℂ) * Complex.exp (β * I)) ∈ Ω \ ball w R := by
      refine ⟨hf.mapsTo (hrD β), fun h => ?_⟩
      rw [hfr, mem_ball, dist_eq_norm] at h
      have := hΓr β r₄ hrr₄ hRβ hr₄ r le_rfl hr1.le
      linarith
    have hj := (hρj _ hm₃ _ hm₄).map (hgc.mono sdiff_subset)
    rw [hgf _ (hrD α), hgf _ (hrD β)] at hj
    refine hj.mono ?_
    rintro _ ⟨p, ⟨hpΩ, hpB⟩, rfl⟩
    refine ⟨(hFg p hpΩ).1, ?_⟩
    rw [mem_preimage, (hFg p hpΩ).2]
    exact fun h => hpB (ball_subset_ball hερ h)
  have hΓ := s20g_b_join hr0 hr1 (fun t ht1 ht2 => hout _ (hΓr α r₃ hrr₃ hRα hr₃ t ht1 ht2))
    (fun t ht1 ht2 => hout _ (hΓr β r₄ hrr₄ hRβ hr₄ t ht1 ht2)) hΓm
  obtain ⟨z, hzΛ, hzΓ⟩ := s20g_b_cross_sets hα.1 hα.2 hβ.1 hβ.2 hΛ hΓ (fun z hz => hz.1) (fun z hz => hz.1)
  exact hzΓ.2 hzΛ.2

/-- **W2, bounded case**: the frontier in `ℂ̄` of a bounded, qualitatively locally connected domain `Ω` which is the
conformal image of `Δ` is a Jordan curve: the extension `F` of `f` (`s20g_ext_continuous`, `s20g_ext_injOn`) maps
the unit circle homeomorphically onto `∂Ω`. -/
theorem s20g_jordan_of_qlc {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hq : s20g_QLC Ω) : IsJordanCurve (frontier (toExt Ω)) := by
  obtain ⟨F, hFc, hFf, hFs, hFi⟩ := s20g_ext_continuous hΩ hf fun w hw => (hq w hw).2
  have hinj := s20g_ext_injOn hΩ hf hq hFc hFf hFs
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfr : frontier Ω = F '' sphere (0 : ℂ) 1 := by
    refine Subset.antisymm (fun w hw => ?_) hFs
    have hwcl : w ∈ F '' closedBall 0 1 := hFi ▸ frontier_subset_closure hw
    obtain ⟨z, hz, rfl⟩ := hwcl
    rcases eq_or_lt_of_le (mem_closedBall_zero_iff.1 hz) with h | h
    · exact ⟨z, mem_sphere_zero_iff_norm.2 h, rfl⟩
    · have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 h
      have hFz : F z ∈ Ω := by
        rw [hFf hzD]
        exact hf.mapsTo hzD
      rw [hΩo.frontier_eq] at hw
      exact absurd hFz hw.2
  have hmem : ∀ ζ : Circle, (ζ : ℂ) ∈ closedBall (0 : ℂ) 1 := fun ζ =>
    mem_closedBall_zero_iff.2 (Circle.norm_coe ζ).le
  rw [frontier_toExt_of_isBounded' hΩ hΩo, hfr]
  refine ⟨fun ζ => ((F ζ : ℂ) : ExtPlane), ?_, fun ζ₁ ζ₂ h => ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp (hFc.comp_continuous continuous_subtype_val hmem)
  · exact Circle.coe_injective (hinj (hmem ζ₁) (hmem ζ₂) (OnePoint.coe_injective h))
  · ext y
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨F ζ, ⟨ζ, mem_sphere_zero_iff_norm.2 (Circle.norm_coe ζ), rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-- **W2** (the book's footnote): a `k`-locally connected hyperbolic simply connected domain is a Jordan domain; for
unbounded `D` its boundary in `ℂ̄` is `∂D ∪ {∞}`.  Bounded `D`: `s20g_jordan_of_qlc`.  Unbounded `D`: move a point
`c ∉ closure D` (`s20g_exists_exterior`) to `∞` by `T z = 1/(z - c)`; `T(D)` is bounded, conformally equivalent to
`Δ` and qualitatively locally connected (`s20g_qlc_inv`), and the Möbius homeomorphism of `ℂ̄` carries the frontier of
`D` onto that of `T(D)`. -/
theorem s20g_isJordanDomain {D : Set ℂ} {k : ℝ} (hD : IsHyperbolicSimplyConnected D)
    (hk : IsKLocallyConnected D k) : IsJordanDomain D := by
  have hDo : IsOpen D := hD.1
  refine ⟨hDo, hD.2.1, ?_⟩
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hD
  have hf : IsConformalOnto (Function.invFunOn φ D) unitDisc D := hφ.symm hDo
  by_cases hb : Bornology.IsBounded D
  · exact s20g_jordan_of_qlc hb hf (s20g_qlc_of_kLC hk)
  · obtain ⟨c, hc⟩ := s20g_exists_exterior hD hk
    have hcD : ∀ z ∈ D, z ≠ c := fun z hz h => hc (h ▸ subset_closure hz)
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl c hc
    have hbd : Bornology.IsBounded (mobiusFn 0 1 1 (-c) '' D) := by
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have hzc : r ≤ ‖z - c‖ := by
        by_contra h
        exact hrD (mem_ball_iff_norm.2 (not_le.1 h)) (subset_closure hz)
      rw [mem_closedBall_zero_iff, mobiusFn, show (0 : ℂ) * z + 1 = 1 by ring,
        show (1 : ℂ) * z + -c = z - c by ring, norm_div, norm_one]
      exact one_div_le_one_div_of_le hr hzc
    have hJ' := s20g_jordan_of_qlc hbd ((uq_j_isConformalOnto_mobiusInv hcD).comp hf) (s20g_qlc_inv hk hc)
    set e := mobiusHomeomorph 0 1 1 (-c) (uq_j_inv_det c)
    have hfr : e '' frontier (toExt D) = frontier (toExt (mobiusFn 0 1 1 (-c) '' D)) := by
      rw [e.image_frontier, uq_j_image_toExt hcD]
    have h := uq_isJordanCurve_image e.symm hJ'
    rw [← hfr, image_image] at h
    simpa only [Homeomorph.symm_apply_apply, image_id'] using h

/-- The frontier of `Δ` in `ℂ̄` is the unit circle (a local copy of `frontier_toExt_unitDisc`, UnitDiscJordan:23,
which S20 does not import). -/
theorem s20g_frontier_toExt_unitDisc : frontier (toExt unitDisc) = toExt (sphere (0 : ℂ) 1) := by
  unfold unitDisc
  rw [frontier_toExt_of_isBounded' isBounded_ball isOpen_ball, frontier_ball (0 : ℂ) one_ne_zero]

/-- The domain of a conformal map onto an open set with a homeomorphic extension to the closures is open
(invariance of domain, applied to the inverse map). -/
theorem s20g_a_isOpen_of_homeoExt {D V : Set ℂ} (hV : IsOpen V) {φ : ℂ → ℂ} (hφ : IsConformalOnto φ D V)
    {Φ : ExtPlane → ExtPlane} (hΦ : IsHomeoExtension φ D V Φ) : IsOpen D := by
  obtain ⟨hΨ1, hΨ2, -, -⟩ := isHomeoExtension_invFunOn hφ hΦ
  set ψ := Function.invFunOn φ D with hψ
  have hVo : IsOpen (toExt V) := OnePoint.isOpenEmbedding_coe.isOpenMap _ hV
  have hcont : ContinuousOn ψ V := by
    intro w hw
    have hK : closure (toExt V) ∈ 𝓝 ((w : ℂ) : ExtPlane) :=
      Filter.mem_of_superset (hVo.mem_nhds (mem_image_of_mem _ hw)) subset_closure
    have h1 : ContinuousAt (Function.invFunOn Φ (closure (toExt D))) (w : ExtPlane) := hΨ2.continuousAt hK
    have h2 : ContinuousAt (((↑) : ℂ → ExtPlane) ∘ ψ) w := by
      have h3 : ContinuousAt ((Function.invFunOn Φ (closure (toExt D))) ∘ ((↑) : ℂ → ExtPlane)) w :=
        h1.comp OnePoint.continuous_coe.continuousAt
      refine h3.congr ?_
      filter_upwards [hV.mem_nhds hw] with w' hw'
      exact hΨ1 w' hw'
    exact (OnePoint.isOpenEmbedding_coe.isInducing.continuousAt_iff.2 h2).continuousWithinAt
  have hinj : InjOn ψ V := fun a ha b hb hab => by
    rw [← hφ.2.2] at ha hb
    have hab' : Function.invFunOn φ D a = Function.invFunOn φ D b := hab
    rw [← Function.invFunOn_eq ha, ← Function.invFunOn_eq hb, hab']
  have himg : ψ '' V = D := by
    rw [← hφ.2.2]
    exact hφ.2.1.leftInvOn_invFunOn.image_image
  rw [← himg]
  exact isOpen_image_of_continuousOn_injOn hV hcont hinj

/-- `e^{ia} ≠ e^{ib}` for `a < b < a + 2π`. -/
theorem s20g_a_exp_ne {a b : ℝ} (hab : a < b) (hba : b < a + 2 * π) :
    Complex.exp (a * I) ≠ Complex.exp (b * I) := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have him := congrArg Complex.im hn
  simp at him
  have h1 : (n : ℝ) * (2 * π) = a - b := by linarith
  have h2 : -1 < (n : ℝ) := by nlinarith [Real.pi_pos]
  have h3 : (n : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have h4 : -1 < n := by exact_mod_cast h2
  have h5 : n < 0 := by exact_mod_cast h3
  omega

/-- The angle `s ∈ (θ, θ + 2π)` of `e^{is}` is `θ + π + arg (-(e^{is} / e^{iθ}))`. -/
theorem s20g_a_ang_exp {θ s : ℝ} (hs : s ∈ Ioo θ (θ + 2 * π)) :
    θ + π + arg (-(Complex.exp (s * I) / Complex.exp (θ * I))) = s := by
  have h : -(Complex.exp (s * I) / Complex.exp (θ * I)) = Complex.exp (((s - θ - π : ℝ) : ℂ) * I) := by
    rw [show ((s - θ - π : ℝ) : ℂ) * I = s * I - θ * I - π * I by push_cast; ring, Complex.exp_sub,
      Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
  rw [h, Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).2 ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  ring

/-- On the unit circle, `u = e^{i(θ + π + arg (-(u / e^{iθ})))}`. -/
theorem s20g_a_exp_ang (θ : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.exp (((θ + π + arg (-(u / Complex.exp (θ * I))) : ℝ) : ℂ) * I) = u := by
  set v := -(u / Complex.exp (θ * I)) with hv
  have hvn : ‖v‖ = 1 := by rw [hv, norm_neg, norm_div, hu, Complex.norm_exp_ofReal_mul_I, div_one]
  have hve : Complex.exp (arg v * I) = v := by
    have h := Complex.norm_mul_exp_arg_mul_I v
    rwa [hvn, Complex.ofReal_one, one_mul] at h
  push_cast
  rw [add_mul, add_mul, Complex.exp_add, Complex.exp_add, hve, Complex.exp_pi_mul_I, hv]
  have he : Complex.exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- For `u ≠ e^{iθ}` on the unit circle, `-(u / e^{iθ})` is in the slit plane. -/
theorem s20g_a_ang_slit (θ : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (hne : u ≠ Complex.exp (θ * I)) :
    -(u / Complex.exp (θ * I)) ∈ slitPlane := by
  set v := -(u / Complex.exp (θ * I)) with hv
  have hvn : ‖v‖ = 1 := by rw [hv, norm_neg, norm_div, hu, Complex.norm_exp_ofReal_mul_I, div_one]
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hsq : ‖v‖ ^ 2 = v.re * v.re + v.im * v.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hvn, him] at hsq
  have hre1 : v.re = -1 := by nlinarith
  have hv1 : v = -1 := Complex.ext (by simp [hre1]) (by simp [him])
  have he : Complex.exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  apply hne
  have h2 : u = -v * Complex.exp (θ * I) := by
    rw [hv]
    field_simp
  rw [h2, hv1]
  ring

/-- **Components of the punctured boundary** (bounded turning).  With a disc uniformizer `Φ` of `D` (homeomorphic on
`closure (toExt D)`), `Φ z₁ = e^{iθ₁}`, `Φ z₂ = e^{iθ₂}`, `θ₁ < θ₂ < θ₁ + 2π`: a point `p` over the open arc
`(θ₁, θ₂)` lies in `∂D ∖ {z₁, z₂}`, and its component there lies over the same arc.

*Truth*: `Φ` restricted to `closure (toExt D)` is a homeomorphism onto the closed disc (compact to Hausdorff) carrying
`frontier (toExt D)` onto the unit circle.  `p ∉ {z₁, z₂}` because `exp (· * I)` is injective on `[θ₁, θ₁ + 2π)`.
The two open arcs are connected, relatively open in the circle minus `{e^{iθ₁}, e^{iθ₂}}`, and partition it, so the
component of `e^{it}` is contained in its own arc; a homeomorphism carries `connectedComponentIn` to
`connectedComponentIn`.

*Route*: `IsHomeoExtension.image_frontier` (Quadrilateral:113), `s20g_frontier_toExt_unitDisc` (above),
`image_connectedComponentIn_of_isEmbedding` (Quadrilateral:38), `Complex.exp_eq_exp_iff_exists_int`,
`isPreconnected_Ioo.image`. -/
theorem s20g_bt_arc_component {D : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ D unitDisc)
    {Φ : ExtPlane → ExtPlane} (hΦ : IsHomeoExtension φ D unitDisc Φ) {θ₁ θ₂ t : ℝ} (h12 : θ₁ < θ₂)
    (h21 : θ₂ < θ₁ + 2 * π) {z₁ z₂ : ℂ} (hz₁ : (z₁ : ExtPlane) ∈ closure (toExt D))
    (hz₂ : (z₂ : ExtPlane) ∈ closure (toExt D)) (hΦ₁ : Φ z₁ = ((Complex.exp (θ₁ * I) : ℂ) : ExtPlane))
    (hΦ₂ : Φ z₂ = ((Complex.exp (θ₂ * I) : ℂ) : ExtPlane)) (ht : t ∈ Ioo θ₁ θ₂) {p : ExtPlane}
    (hp : p ∈ closure (toExt D)) (hΦp : Φ p = ((Complex.exp (t * I) : ℂ) : ExtPlane)) :
    p ∈ frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)} ∧
      ∀ q ∈ connectedComponentIn (frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p,
        q ∈ closure (toExt D) ∧ ∃ s ∈ Ioo θ₁ θ₂, Φ q = ((Complex.exp (s * I) : ℂ) : ExtPlane) := by
  have _ := h12
  have hDo : IsOpen D := s20g_a_isOpen_of_homeoExt isOpen_ball hφ hΦ
  have hfr : Φ '' frontier (toExt D) = toExt (sphere (0 : ℂ) 1) := by
    rw [hΦ.image_frontier hDo isOpen_ball hφ.2.2]
    exact s20g_frontier_toExt_unitDisc
  have hfrK : frontier (toExt D) ⊆ closure (toExt D) := frontier_subset_closure
  set S := frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)} with hSdef
  -- points of `S` go to the circle minus the two marked points
  have hSu : ∀ q ∈ S, ∃ u : ℂ, ‖u‖ = 1 ∧ u ≠ Complex.exp (θ₁ * I) ∧ u ≠ Complex.exp (θ₂ * I) ∧
      Φ q = (u : ExtPlane) := by
    intro q hq
    obtain ⟨u, hu, hΦq⟩ := hfr.subset (mem_image_of_mem Φ hq.1)
    refine ⟨u, mem_sphere_zero_iff_norm.1 hu, fun h => hq.2 (Or.inl ?_), fun h => hq.2 (Or.inr ?_), hΦq.symm⟩
    · exact hΦ.2.2.1 (hfrK hq.1) hz₁ (by rw [hΦ₁, ← hΦq, h])
    · exact hΦ.2.2.1 (hfrK hq.1) hz₂ (by rw [hΦ₂, ← hΦq, h])
  -- `p` lies in `S`
  have hpfr : p ∈ frontier (toExt D) := by
    have hmem : Φ p ∈ Φ '' frontier (toExt D) := by
      rw [hfr, hΦp]
      exact mem_image_of_mem _ (mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I t))
    obtain ⟨p', hp', hpp'⟩ := hmem
    rw [← hΦ.2.2.1 (hfrK hp') hp hpp']
    exact hp'
  have hpS : p ∈ S := by
    refine ⟨hpfr, ?_⟩
    rintro (h | h)
    · rw [h, hΦ₁] at hΦp
      exact s20g_a_exp_ne ht.1 (by linarith [ht.2]) (OnePoint.coe_injective hΦp)
    · rw [h, hΦ₂] at hΦp
      exact s20g_a_exp_ne ht.2 (by linarith [ht.1]) (OnePoint.coe_injective hΦp).symm
  refine ⟨hpS, fun q hq => ?_⟩
  set C := connectedComponentIn S p with hC
  have hCS : C ⊆ S := connectedComponentIn_subset S p
  have hCpre : IsPreconnected (Φ '' C) :=
    isPreconnected_connectedComponentIn.image Φ (hΦ.2.1.mono (hCS.trans (sdiff_subset.trans hfrK)))
  set T : Set ℂ := {u | (u : ExtPlane) ∈ Φ '' C} with hT
  have hTimg : ((↑) : ℂ → ExtPlane) '' T = Φ '' C := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨u, -, -, -, hu⟩ := hSu q' (hCS hq')
      exact ⟨u, show ((u : ℂ) : ExtPlane) ∈ Φ '' C by rw [← hu]; exact ⟨q', hq', rfl⟩, hu.symm⟩
  have hTpre : IsPreconnected T :=
    OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 (hTimg ▸ hCpre)
  have hTu : ∀ u ∈ T, ‖u‖ = 1 ∧ u ≠ Complex.exp (θ₁ * I) ∧ u ≠ Complex.exp (θ₂ * I) := by
    rintro u ⟨q', hq', hqu⟩
    obtain ⟨u', h1, h2, h3, hu'⟩ := hSu q' (hCS hq')
    rw [hu'] at hqu
    rw [← OnePoint.coe_injective hqu]
    exact ⟨h1, h2, h3⟩
  set g : ℂ → ℝ := fun u => θ₁ + π + arg (-(u / Complex.exp (θ₁ * I))) with hg
  have hgc : ContinuousOn g T := by
    intro u hu
    have h1 : ContinuousAt (fun u : ℂ => -(u / Complex.exp (θ₁ * I))) u :=
      (continuous_id.div_const (Complex.exp (θ₁ * I))).neg.continuousAt
    have h2 : ContinuousAt (arg ∘ fun u : ℂ => -(u / Complex.exp (θ₁ * I))) u :=
      ContinuousAt.comp (f := fun u : ℂ => -(u / Complex.exp (θ₁ * I)))
        (Complex.continuousAt_arg (s20g_a_ang_slit θ₁ (hTu u hu).1 (hTu u hu).2.1)) h1
    exact (continuousAt_const.add h2).continuousWithinAt
  have hgT : IsPreconnected (g '' T) := hTpre.image g hgc
  have htT : Complex.exp (t * I) ∈ T := ⟨p, mem_connectedComponentIn hpS, hΦp⟩
  have hgt : g (Complex.exp (t * I)) = t := s20g_a_ang_exp ⟨ht.1, by linarith [ht.2]⟩
  have hθ₂ : θ₂ ∉ g '' T := by
    rintro ⟨u, hu, hgu⟩
    apply (hTu u hu).2.2
    rw [← hgu]
    exact (s20g_a_exp_ang θ₁ (hTu u hu).1).symm
  obtain ⟨u, h1, -, -, hu⟩ := hSu q (hCS hq)
  have huT : u ∈ T := ⟨q, hq, hu⟩
  refine ⟨hfrK (hCS hq).1, g u, ⟨?_, ?_⟩, ?_⟩
  · have h := Complex.neg_pi_lt_arg (-(u / Complex.exp (θ₁ * I)))
    simp only [hg]
    linarith
  · by_contra hle
    push Not at hle
    exact hθ₂ (hgT.Icc_subset ⟨_, htT, hgt⟩ ⟨u, huT, rfl⟩ ⟨ht.2.le, hle⟩)
  · rw [hu]
    exact congrArg _ (s20g_a_exp_ang θ₁ h1).symm

/-- **Bounded turning, the crossing step.**  With a disc uniformizer `Φ` of a `k`-locally connected `D` and
`Φ z_j = e^{iθ_j}` (`θ₁ < θ₂ < θ₁ + 2π`), one of the two arcs of `∂D` between `z₁` and `z₂` lies in
`closedBall z₁ ((2k² + 1) ‖z₁ - z₂‖)` (in particular it avoids `∞`).

*Truth*: `r = ‖z₁ - z₂‖ > 0` (`Φ` injective), `R = (2k² + 1) r`.  Suppose both arcs have points `Ψ e^{iα}`,
`Ψ e^{iβ}` (`Ψ = Φ⁻¹` on the closed disc, `α ∈ (θ₁, θ₂)`, `β ∈ (θ₂, θ₁ + 2π)`) outside `toExt (closedBall z₁ R)`
(possibly `∞`).  Clause (i) of `hk` at `z₁` with radius `2r` joins `x_j = Ψ (s e^{iθ_j})` (`s` near `1`, so
`‖x_j - z_j‖ < r`) in `D ∩ closedBall z₁ (2kr)`; clause (ii) at `z₁` with radius `R` joins `Ψ (s e^{iα})`,
`Ψ (s e^{iβ})` (outside `closedBall z₁ R`, an open condition in `ℂ̄`) in `D ∖ ball z₁ (R/k)`.  Pulled back by `φ` and
completed by radial segments these are paths as in `s20g_crossing`; their `Ψ`-images lie in `closedBall z₁ (2kr)`
resp. outside `ball z₁ (R/k)`, disjoint since `R/k = 2kr + r/k > 2kr`.  Contradiction.

*Route*: `s20g_crossing`, `isHomeoExtension_invFunOn` (ImageQuad:63), `hk.2`, `IsConformalOnto.symm`,
`Path.trans`, `Path.map'`. -/
theorem s20g_bt_cross {D : Set ℂ} {k : ℝ} (hk : IsKLocallyConnected D k) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ D unitDisc) {Φ : ExtPlane → ExtPlane} (hΦ : IsHomeoExtension φ D unitDisc Φ)
    {θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂) (h21 : θ₂ < θ₁ + 2 * π) {z₁ z₂ : ℂ}
    (hz₁ : (z₁ : ExtPlane) ∈ closure (toExt D)) (hz₂ : (z₂ : ExtPlane) ∈ closure (toExt D))
    (hΦ₁ : Φ z₁ = ((Complex.exp (θ₁ * I) : ℂ) : ExtPlane))
    (hΦ₂ : Φ z₂ = ((Complex.exp (θ₂ * I) : ℂ) : ExtPlane)) :
    (∀ p ∈ closure (toExt D), ∀ s ∈ Ioo θ₁ θ₂, Φ p = ((Complex.exp (s * I) : ℂ) : ExtPlane) →
        p ∈ toExt (closedBall z₁ ((2 * k ^ 2 + 1) * ‖z₁ - z₂‖))) ∨
      ∀ p ∈ closure (toExt D), ∀ s ∈ Ioo θ₂ (θ₁ + 2 * π), Φ p = ((Complex.exp (s * I) : ℂ) : ExtPlane) →
        p ∈ toExt (closedBall z₁ ((2 * k ^ 2 + 1) * ‖z₁ - z₂‖)) := by
  have hk1 : 1 ≤ k := hk.1
  have hk0 : 0 < k := by linarith
  -- the inverse extension `Ψ` and `G z = Ψ z` on the closed disc
  have hΨ : IsHomeoExtension (Function.invFunOn φ D) unitDisc D (Function.invFunOn Φ (closure (toExt D))) :=
    isHomeoExtension_invFunOn hφ hΦ
  set Ψ := Function.invFunOn Φ (closure (toExt D)) with hΨ_def
  have hcl : closure (toExt unitDisc) = toExt (closedBall 0 1) := by
    rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_toExt_of_isBounded isBounded_ball,
      closure_ball (0 : ℂ) one_ne_zero]
  set G : ℂ → ExtPlane := fun z => Ψ (z : ExtPlane) with hG_def
  have hGc : ContinuousOn G (closedBall 0 1) :=
    hΨ.2.1.comp OnePoint.continuous_coe.continuousOn (fun z hz => by rw [hcl]; exact ⟨z, hz, rfl⟩)
  have hΨΦ : ∀ p ∈ closure (toExt D), Ψ (Φ p) = p := fun p hp => hΦ.2.2.1.leftInvOn_invFunOn hp
  have hGe : ∀ {p : ExtPlane} {c : ℝ}, p ∈ closure (toExt D) → Φ p = ((Complex.exp (c * I) : ℂ) : ExtPlane) →
      G (Complex.exp (c * I)) = p := fun hp he => by
    show Ψ _ = _
    rw [← he]
    exact hΨΦ _ hp
  have hinv : ∀ z ∈ unitDisc, Function.invFunOn φ D z ∈ D ∧ G z = ((Function.invFunOn φ D z : ℂ) : ExtPlane) := by
    intro z hz
    have hz' : z ∈ φ '' D := hφ.2.2.symm ▸ hz
    exact ⟨Function.invFunOn_mem hz', hΨ.1 z hz⟩
  have hφinv : ∀ z ∈ unitDisc, φ (Function.invFunOn φ D z) = z := fun z hz =>
    Function.invFunOn_eq (hφ.2.2.symm ▸ hz : z ∈ φ '' D)
  have hφD : ∀ y ∈ D, φ y ∈ unitDisc ∧ G (φ y) = (y : ExtPlane) := by
    intro y hy
    refine ⟨hφ.mapsTo hy, ?_⟩
    show Ψ _ = _
    rw [← hΦ.1 y hy]
    exact hΨΦ _ (subset_closure (mem_image_of_mem _ hy))
  -- the two points are distinct
  have hz12 : z₁ ≠ z₂ := by
    rintro rfl
    exact s20g_b_exp_ne (by linarith) (by linarith) (OnePoint.coe_injective (hΦ₁.symm.trans hΦ₂))
  set r₀ := ‖z₁ - z₂‖ with hr₀_def
  have hr₀ : 0 < r₀ := norm_pos_iff.2 (sub_ne_zero.2 hz12)
  set R := (2 * k ^ 2 + 1) * r₀ with hR_def
  have hRpos : 0 < R := by positivity
  have h2kR : k * (2 * r₀) ≤ R := by nlinarith
  have hRk : k * (2 * r₀) < R / k := by
    rw [lt_div_iff₀ hk0]
    nlinarith
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨pα, hpα, α, hα, hΦα, hpαR⟩, pβ, hpβ, β, hβ, hΦβ, hpβR⟩ := hcon
  -- radii
  have hU : ∀ (x : ℂ) (ρ : ℝ), IsOpen (toExt (ball x ρ)) := fun x ρ => OnePoint.isOpen_image_coe.2 isOpen_ball
  have hV : IsOpen (toExt (closedBall z₁ R))ᶜ :=
    ((isCompact_closedBall z₁ R).image OnePoint.continuous_coe).isClosed.isOpen_compl
  obtain ⟨r₁, hr₁0, hr₁1, hr₁⟩ := s20g_b_radial hGc θ₁ (hU z₁ r₀)
    (by rw [hGe hz₁ hΦ₁]; exact mem_image_of_mem _ (mem_ball_self hr₀))
  obtain ⟨r₂, -, hr₂1, hr₂⟩ := s20g_b_radial hGc θ₂ (hU z₂ r₀)
    (by rw [hGe hz₂ hΦ₂]; exact mem_image_of_mem _ (mem_ball_self hr₀))
  obtain ⟨r₃, -, hr₃1, hr₃⟩ := s20g_b_radial hGc α hV (by rw [hGe hpα hΦα]; exact hpαR)
  obtain ⟨r₄, -, hr₄1, hr₄⟩ := s20g_b_radial hGc β hV (by rw [hGe hpβ hΦβ]; exact hpβR)
  set r := max (max r₁ r₂) (max r₃ r₄) with hr_def
  have hrr₁ : r₁ ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hrr₂ : r₂ ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
  have hrr₃ : r₃ ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrr₄ : r₄ ≤ r := le_trans (le_max_right _ _) (le_max_right _ _)
  have hr0 : 0 ≤ r := le_trans hr₁0 hrr₁
  have hr1 : r < 1 := max_lt (max_lt hr₁1 hr₂1) (max_lt hr₃1 hr₄1)
  have hrD : ∀ c : ℝ, (r : ℂ) * Complex.exp (c * I) ∈ unitDisc := fun c => by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  -- `Λ`: from `e^{iθ₁}` to `e^{iθ₂}` with `G`-image in `closedBall z₁ (2kr₀)`
  set P := toExt (closedBall z₁ (k * (2 * r₀))) with hP_def
  have hB₁ : ball z₁ r₀ ⊆ closedBall z₁ (k * (2 * r₀)) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith))
  have hB₂ : ball z₂ r₀ ⊆ closedBall z₁ (2 * r₀) := by
    intro y hy
    rw [mem_ball] at hy
    rw [mem_closedBall]
    have h1 := dist_triangle y z₂ z₁
    rw [dist_eq_norm z₂ z₁, norm_sub_rev] at h1
    linarith
  have hB₂' : closedBall z₁ (2 * r₀) ⊆ closedBall z₁ (k * (2 * r₀)) :=
    closedBall_subset_closedBall (by nlinarith)
  have hΛ₁ : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (θ₁ * I)) ∈ P := fun t ht1 ht2 =>
    image_mono hB₁ (hr₁ t (le_trans hrr₁ ht1) ht2)
  have hΛ₂ : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (θ₂ * I)) ∈ P := fun t ht1 ht2 =>
    image_mono (hB₂.trans hB₂') (hr₂ t (le_trans hrr₂ ht1) ht2)
  have hΛm : JoinedIn (unitDisc ∩ G ⁻¹' P) (r * Complex.exp (θ₁ * I)) (r * Complex.exp (θ₂ * I)) := by
    obtain ⟨hy₁D, hy₁G⟩ := hinv _ (hrD θ₁)
    obtain ⟨hy₂D, hy₂G⟩ := hinv _ (hrD θ₂)
    have hy₁ : Function.invFunOn φ D ((r : ℂ) * Complex.exp (θ₁ * I)) ∈ ball z₁ r₀ := by
      rw [← coe_mem_toExt_iff, ← hy₁G]
      exact hr₁ r hrr₁ hr1.le
    have hy₂ : Function.invFunOn φ D ((r : ℂ) * Complex.exp (θ₂ * I)) ∈ ball z₂ r₀ := by
      rw [← coe_mem_toExt_iff, ← hy₂G]
      exact hr₂ r hrr₂ hr1.le
    have hj := ((hk.2 z₁ (2 * r₀) (by positivity)).1 _
      ⟨hy₁D, (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hy₁⟩ _
      ⟨hy₂D, hB₂ hy₂⟩).map (hφ.1.continuousOn.mono inter_subset_left)
    rw [hφinv _ (hrD θ₁), hφinv _ (hrD θ₂)] at hj
    refine hj.mono ?_
    rintro _ ⟨y, ⟨hyD, hyB⟩, rfl⟩
    refine ⟨(hφD y hyD).1, ?_⟩
    rw [mem_preimage, (hφD y hyD).2]
    exact mem_image_of_mem _ hyB
  have hΛ := s20g_b_join hr0 hr1 hΛ₁ hΛ₂ hΛm
  -- `Γ`: from `e^{iα}` to `e^{iβ}` with `G`-image outside `closedBall z₁ (2kr₀)`
  have hPR : Pᶜ ⊇ (toExt (closedBall z₁ R))ᶜ := compl_subset_compl.2 (image_mono (closedBall_subset_closedBall h2kR))
  have hΓ₃ : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (α * I)) ∈ Pᶜ := fun t ht1 ht2 =>
    hPR (hr₃ t (le_trans hrr₃ ht1) ht2)
  have hΓ₄ : ∀ t : ℝ, r ≤ t → t ≤ 1 → G (t * Complex.exp (β * I)) ∈ Pᶜ := fun t ht1 ht2 =>
    hPR (hr₄ t (le_trans hrr₄ ht1) ht2)
  have hΓm : JoinedIn (unitDisc ∩ G ⁻¹' Pᶜ) (r * Complex.exp (α * I)) (r * Complex.exp (β * I)) := by
    obtain ⟨hy₃D, hy₃G⟩ := hinv _ (hrD α)
    obtain ⟨hy₄D, hy₄G⟩ := hinv _ (hrD β)
    have hy₃ : Function.invFunOn φ D ((r : ℂ) * Complex.exp (α * I)) ∉ ball z₁ R := by
      intro h
      have h' := hr₃ r hrr₃ hr1.le
      rw [hy₃G] at h'
      exact h' (coe_mem_toExt_iff.2 (ball_subset_closedBall h))
    have hy₄ : Function.invFunOn φ D ((r : ℂ) * Complex.exp (β * I)) ∉ ball z₁ R := by
      intro h
      have h' := hr₄ r hrr₄ hr1.le
      rw [hy₄G] at h'
      exact h' (coe_mem_toExt_iff.2 (ball_subset_closedBall h))
    have hj := ((hk.2 z₁ R hRpos).2 _ ⟨hy₃D, hy₃⟩ _ ⟨hy₄D, hy₄⟩).map (hφ.1.continuousOn.mono sdiff_subset)
    rw [hφinv _ (hrD α), hφinv _ (hrD β)] at hj
    refine hj.mono ?_
    rintro _ ⟨y, ⟨hyD, hyB⟩, rfl⟩
    refine ⟨(hφD y hyD).1, ?_⟩
    rw [mem_preimage, (hφD y hyD).2]
    intro h
    have hy := mem_closedBall.1 (coe_mem_toExt_iff.1 h)
    exact hyB (mem_ball.2 (lt_of_le_of_lt hy hRk))
  have hΓ := s20g_b_join hr0 hr1 hΓ₃ hΓ₄ hΓm
  obtain ⟨z, hzΛ, hzΓ⟩ := s20g_b_cross_sets hα.1 hα.2 hβ.1 hβ.2 hΛ hΓ (fun z hz => hz.1) (fun z hz => hz.1)
  exact hzΓ.2 hzΛ.2

/-- Two distinct points of the unit circle are `e^{iθ₁}`, `e^{iθ₂}` with `θ₁ < θ₂ < θ₁ + 2π`. -/
theorem s20g_angles {ζ₁ ζ₂ : ℂ} (h₁ : ‖ζ₁‖ = 1) (h₂ : ‖ζ₂‖ = 1) (hne : ζ₁ ≠ ζ₂) :
    ∃ θ₁ θ₂ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₁ + 2 * π ∧ Complex.exp (θ₁ * I) = ζ₁ ∧ Complex.exp (θ₂ * I) = ζ₂ := by
  have he : ∀ ζ : ℂ, ‖ζ‖ = 1 → Complex.exp ((arg ζ : ℂ) * I) = ζ := fun ζ hζ => by
    have h := Complex.norm_mul_exp_arg_mul_I ζ
    rwa [hζ, Complex.ofReal_one, one_mul] at h
  have hne' : arg ζ₁ ≠ arg ζ₂ := fun h => hne (by rw [← he ζ₁ h₁, ← he ζ₂ h₂, h])
  have hb₁ := Complex.neg_pi_lt_arg ζ₁
  have hb₂ := Complex.arg_le_pi ζ₁
  have hc₁ := Complex.neg_pi_lt_arg ζ₂
  have hc₂ := Complex.arg_le_pi ζ₂
  rcases lt_or_gt_of_ne hne' with h | h
  · exact ⟨arg ζ₁, arg ζ₂, h, by linarith, he ζ₁ h₁, he ζ₂ h₂⟩
  · refine ⟨arg ζ₁, arg ζ₂ + 2 * π, by linarith, by linarith, he ζ₁ h₁, ?_⟩
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, he ζ₂ h₂]
    have : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact Complex.exp_two_pi_mul_I
    rw [this, mul_one]

/-- **Bounded turning** (the book: `k`-locally connected ⇒ `k²`-bounded turning; here with the constant
`2(2k² + 1)`): through a disc uniformizer of the Jordan domain `D`, one arc of `∂D ∖ {z₁, z₂}` lies in
`closedBall z₁ ((2k² + 1) ‖z₁ - z₂‖)` (`s20g_bt_cross`) and is the component of each of its points
(`s20g_bt_arc_component`). -/
theorem s20g_boundedTurning {D : Set ℂ} {k : ℝ} (hJ : IsJordanDomain D) (hk : IsKLocallyConnected D k) :
    IsBoundedTurning (frontier (toExt D)) (2 * (2 * k ^ 2 + 1)) := by
  have hk1 : 1 ≤ k := hk.1
  refine ⟨hJ.2.2, by nlinarith, fun z₁ z₂ h₁ h₂ hne => ?_⟩
  obtain ⟨φ, hφ, Φ, hΦ⟩ := s13x_th_exists_disc_uniformizer hJ
  have hfr : Φ '' frontier (toExt D) = toExt (sphere (0 : ℂ) 1) := by
    rw [hΦ.image_frontier hJ.1 isOpen_ball hφ.2.2]
    exact s20g_frontier_toExt_unitDisc
  have hcl₁ : (z₁ : ExtPlane) ∈ closure (toExt D) := frontier_subset_closure h₁
  have hcl₂ : (z₂ : ExtPlane) ∈ closure (toExt D) := frontier_subset_closure h₂
  obtain ⟨ζ₁, hζ₁, hΦζ₁⟩ : ∃ ζ ∈ sphere (0 : ℂ) 1, Φ z₁ = (ζ : ExtPlane) := by
    obtain ⟨ζ, hζ, h⟩ := hfr.subset (mem_image_of_mem Φ h₁)
    exact ⟨ζ, hζ, h.symm⟩
  obtain ⟨ζ₂, hζ₂, hΦζ₂⟩ : ∃ ζ ∈ sphere (0 : ℂ) 1, Φ z₂ = (ζ : ExtPlane) := by
    obtain ⟨ζ, hζ, h⟩ := hfr.subset (mem_image_of_mem Φ h₂)
    exact ⟨ζ, hζ, h.symm⟩
  have hζne : ζ₁ ≠ ζ₂ := by
    rintro rfl
    exact hne (OnePoint.coe_injective (hΦ.2.2.1 hcl₁ hcl₂ (hΦζ₁.trans hΦζ₂.symm)))
  obtain ⟨θ₁, θ₂, h12, h21, he₁, he₂⟩ :=
    s20g_angles (mem_sphere_zero_iff_norm.1 hζ₁) (mem_sphere_zero_iff_norm.1 hζ₂) hζne
  rw [← he₁] at hΦζ₁
  rw [← he₂] at hΦζ₂
  set R := (2 * k ^ 2 + 1) * ‖z₁ - z₂‖ with hR
  -- a point `p` over the angle `t` exists, since `Φ` maps `closure (toExt D)` onto the closed disc
  have hpt : ∀ t : ℝ, ∃ p ∈ closure (toExt D), Φ p = ((Complex.exp (t * I) : ℂ) : ExtPlane) := by
    intro t
    have hmem : ((Complex.exp (t * I) : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
      apply frontier_subset_closure
      rw [s20g_frontier_toExt_unitDisc]
      exact ⟨_, mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I t), rfl⟩
    rw [← hΦ.2.2.2] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    exact ⟨p, hp, hpe⟩
  -- the conclusion from an arc contained in the ball
  have key : ∀ {a b : ℝ} {w₁ w₂ : ℂ}, a < b → b < a + 2 * π → (w₁ : ExtPlane) ∈ closure (toExt D) →
      (w₂ : ExtPlane) ∈ closure (toExt D) → Φ w₁ = ((Complex.exp (a * I) : ℂ) : ExtPlane) →
      Φ w₂ = ((Complex.exp (b * I) : ℂ) : ExtPlane) →
      ({(w₁ : ExtPlane), (w₂ : ExtPlane)} : Set ExtPlane) = {(z₁ : ExtPlane), (z₂ : ExtPlane)} →
      (∀ p ∈ closure (toExt D), ∀ s ∈ Ioo a b, Φ p = ((Complex.exp (s * I) : ℂ) : ExtPlane) →
        p ∈ toExt (closedBall z₁ R)) →
      ∃ p ∈ frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)},
        extInf ∉ connectedComponentIn (frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p ∧
        Metric.ediam {z : ℂ | (z : ExtPlane) ∈
          connectedComponentIn (frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p} ≤
            ENNReal.ofReal (2 * (2 * k ^ 2 + 1) * ‖z₁ - z₂‖) := by
    intro a b w₁ w₂ hab hba hw₁ hw₂ hΦw₁ hΦw₂ hset hball
    obtain ⟨p, hp, hΦp⟩ := hpt ((a + b) / 2)
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    obtain ⟨hpC, hcomp⟩ := s20g_bt_arc_component hφ hΦ hab hba hw₁ hw₂ hΦw₁ hΦw₂ hmid hp hΦp
    rw [hset] at hpC hcomp
    have hin : ∀ q ∈ connectedComponentIn (frontier (toExt D) \ {(z₁ : ExtPlane), (z₂ : ExtPlane)}) p,
        q ∈ toExt (closedBall z₁ R) := fun q hq => by
      obtain ⟨hqcl, s, hs, hΦq⟩ := hcomp q hq
      exact hball q hqcl s hs hΦq
    refine ⟨p, hpC, fun hinf => ?_, ?_⟩
    · obtain ⟨z, -, hz⟩ := hin extInf hinf
      exact OnePoint.coe_ne_infty z hz
    · refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
      obtain ⟨x', hx', hxx⟩ := hin x hx
      obtain ⟨y', hy', hyy⟩ := hin y hy
      rw [OnePoint.coe_injective hxx] at hx'
      rw [OnePoint.coe_injective hyy] at hy'
      calc dist x y ≤ dist x z₁ + dist y z₁ := dist_triangle_right x y z₁
        _ ≤ R + R := add_le_add (mem_closedBall.1 hx') (mem_closedBall.1 hy')
        _ = 2 * (2 * k ^ 2 + 1) * ‖z₁ - z₂‖ := by rw [hR]; ring
  rcases s20g_bt_cross hk hφ hΦ h12 h21 hcl₁ hcl₂ hΦζ₁ hΦζ₂ with hA | hA
  · exact key h12 h21 hcl₁ hcl₂ hΦζ₁ hΦζ₂ rfl hA
  · have he : Complex.exp (((θ₁ + 2 * π : ℝ) : ℂ) * I) = Complex.exp (θ₁ * I) := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.exp_two_pi_mul_I, mul_one]
    exact key h21 (by linarith) hcl₂ hcl₁ hΦζ₂ (by rw [he]; exact hΦζ₁) (Set.pair_comm _ _) hA

/-- **Theorem 20.5** (Gehring): an `a`-Schwarz domain is a `K`-quasidisc with `K` depending only
on `a`. -/
theorem thm20_5_gehring {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, ∀ D : Set ℂ, IsSchwarzDomain D a → IsKQuasidisc D K := by
  have hk1 : (1 : ℝ) ≤ 1 + 15 / a := le_add_of_nonneg_right (div_nonneg (by norm_num) ha.le)
  obtain ⟨K, hK⟩ := thm18_1_quasicircle_of_boundedTurning (M := 2 * (2 * (1 + 15 / a) ^ 2 + 1)) (by nlinarith)
  refine ⟨K, fun D hD => ?_⟩
  have hlc := thm20_4 hD
  have hJ := s20g_isJordanDomain hD.1 hlc
  exact ⟨hJ, hK _ (s20g_boundedTurning hJ hlc)⟩

/-- Theorems 20.3 and 20.5: a simply connected hyperbolic domain is a Schwarz domain iff it is a
quasidisc. -/
theorem schwarzDomain_iff_quasidisc {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) :
    (∃ a : ℝ, IsSchwarzDomain D a) ↔ ∃ K : ℝ, IsKQuasidisc D K := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨K, hK⟩ := thm20_5_gehring ha.2.1
    exact ⟨K, hK D ⟨hD, ha.2⟩⟩
  · rintro ⟨K, hK⟩
    have hK1 : 1 ≤ K := by
      obtain ⟨-, f, hf, -⟩ := hK
      exact hf.2.1
    obtain ⟨c, -, h⟩ := thm20_3_ahlfors hK1
    exact ⟨1 / c, (h D hK).1⟩

end LiZhongQC
