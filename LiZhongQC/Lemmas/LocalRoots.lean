import LiZhongQC.Basic

/-!
# Local roots, primitives and the descent through the squaring map

Small general facts about analytic functions of one complex variable near a point, used for the
natural parameters of quadratic differentials (`Ch07/S25_QuadraticDifferentials.lean`) and for
the lifted differentials of §32 (`Ch09/S32_FiniteTypeTeichmuller.lean`):

* `cpow_half_sq`, `norm_cpow_half`, `exists_local_sqrt`: the principal square root and a local
  holomorphic branch of the square root near any `w ≠ 0`;
* `analyticAt_of_analyticAt_pow_mul_comp_sq`: **descent through the squaring map** — if
  `ζ ↦ ζ^(2n) φ(ζ²)` is analytic at `0`, so is `z ↦ zⁿ φ z`;
* `exists_analyticAt_sq_eq`: an analytic square root of a non-vanishing analytic function, which
  depends only on the values of the function (so it is even when the function is);
* `exists_primitive_analyticAt`, `eventually_eq_const_of_deriv_eq_zero`: primitives near a point;
* `analyticAt_dslope`, `eq_of_continuousAt_of_eventuallyEq_nhdsNE`;
* `exists_analyticAt_comp_sq_of_even`: an even analytic function is an analytic function of `w²`;
* `exists_factor_of_deriv_eq_pow_mul`: `F 0 = 0` and `F' = wᵏ e` with `e 0 ≠ 0` give
  `F = w^(k+1) g` with `g 0 ≠ 0`.

This is a leaf: it imports only `LiZhongQC.Basic`.
-/

open Complex Set Metric Filter Topology

noncomputable section

namespace LiZhongQC

/-! ### Square roots -/

/-- The principal square root `v ^ (1/2)` squares to `v`. -/
theorem cpow_half_sq (v : ℂ) : (v ^ ((1 / 2 : ℝ) : ℂ)) ^ 2 = v := by
  have : ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
    push_cast
    ring
  rw [this]
  exact Complex.cpow_ofNat_inv_pow v 2

/-- The modulus of the principal square root. -/
theorem norm_cpow_half (v : ℂ) : ‖v ^ ((1 / 2 : ℝ) : ℂ)‖ = Real.sqrt ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [Complex.zero_cpow (by norm_num), norm_zero, Real.sqrt_zero]
  · rw [Complex.norm_cpow_of_ne_zero hv, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Real.exp_zero, div_one, Real.sqrt_eq_rpow]

/-- Near any `w ≠ 0` there is a holomorphic branch of the square root (the principal branch on
the slit plane, `i·√(−v)` on the negative axis) whose values have modulus `√‖v‖`. -/
theorem exists_local_sqrt {w : ℂ} (hw : w ≠ 0) :
    ∃ ρ : ℂ → ℂ, DifferentiableAt ℂ ρ w ∧ ∀ v, ρ v ^ 2 = v ∧ ‖ρ v‖ = Real.sqrt ‖v‖ := by
  by_cases hs : w ∈ slitPlane
  · refine ⟨fun v => v ^ ((1 / 2 : ℝ) : ℂ), ?_, fun v => ⟨cpow_half_sq v, norm_cpow_half v⟩⟩
    exact DifferentiableAt.cpow_const (f := fun v => v) differentiableAt_id hs
  · have hs' : -w ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hs ⊢
      push Not at hs
      left
      rw [neg_re]
      rcases hs.1.lt_or_eq with h | h
      · linarith
      · exact absurd (Complex.ext (by simpa using h) (by simpa using hs.2)) hw
    refine ⟨fun v => I * (-v) ^ ((1 / 2 : ℝ) : ℂ), ?_, fun v => ⟨?_, ?_⟩⟩
    · exact (DifferentiableAt.cpow_const (f := fun v => -v) differentiableAt_id.neg hs').const_mul I
    · rw [mul_pow, Complex.I_sq, cpow_half_sq, neg_one_mul, neg_neg]
    · rw [norm_mul, Complex.norm_I, one_mul, norm_cpow_half, norm_neg]

/-- **Descent through the squaring map.**  If `ζ ↦ ζ^(2n) φ(ζ²)` is analytic at `0`, then
`z ↦ zⁿ φ(z)` is analytic at `0`.

Route: `H z = zⁿ φ z` equals `G ∘ ρ` for any local square root `ρ` (`G ζ = ζ^(2n) φ(ζ²)`), so `H`
is holomorphic on a punctured neighbourhood of `0` and continuous at `0`; conclude by the
removable singularity theorem
(`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`). -/
theorem analyticAt_of_analyticAt_pow_mul_comp_sq {φ : ℂ → ℂ} {n : ℕ}
    (hG : AnalyticAt ℂ (fun ζ => ζ ^ (2 * n) * φ (ζ ^ 2)) 0) :
    AnalyticAt ℂ (fun z => z ^ n * φ z) 0 := by
  set G : ℂ → ℂ := fun ζ => ζ ^ (2 * n) * φ (ζ ^ 2) with hGdef
  set H : ℂ → ℂ := fun z => z ^ n * φ z with hHdef
  have hGH : ∀ ρ z : ℂ, ρ ^ 2 = z → G ρ = H z := by
    intro ρ z hρ
    simp only [hGdef, hHdef, pow_mul, hρ]
  obtain ⟨r, hr, hGan⟩ := Metric.eventually_nhds_iff.1 hG.eventually_analyticAt
  have hcont : ContinuousAt G 0 := hG.continuousAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · -- `H` is holomorphic on a punctured neighbourhood of `0`
    have hball : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ < r ^ 2 := by
      have hb : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ball (0 : ℂ) (r ^ 2) := Metric.ball_mem_nhds (0 : ℂ) (pow_pos hr 2)
      exact hb.mono fun w hw => mem_ball_zero_iff.1 hw
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
    have hw0' : w ≠ 0 := hw0
    obtain ⟨ρ, hρd, hρ⟩ := exists_local_sqrt hw0'
    have hρw : dist (ρ w) 0 < r := by
      rw [dist_zero_right, (hρ w).2]
      calc Real.sqrt ‖w‖ < Real.sqrt (r ^ 2) := Real.sqrt_lt_sqrt (norm_nonneg _) hw
        _ = r := Real.sqrt_sq hr.le
    have hd : DifferentiableAt ℂ (G ∘ ρ) w := ((hGan hρw).differentiableAt).comp w hρd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall fun v => (hGH (ρ v) v (hρ v).1).symm)
  · -- `H` is continuous at `0`
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
    refine ⟨δ ^ 2, pow_pos hδ 2, fun w hw => ?_⟩
    rw [dist_zero_right] at hw
    rcases eq_or_ne w 0 with rfl | hw0
    · rw [dist_self]
      exact hε
    · obtain ⟨ρ, -, hρ⟩ := exists_local_sqrt hw0
      have h1 : dist (ρ w) 0 < δ := by
        rw [dist_zero_right, (hρ w).2]
        calc Real.sqrt ‖w‖ < Real.sqrt (δ ^ 2) := Real.sqrt_lt_sqrt (norm_nonneg _) hw
          _ = δ := Real.sqrt_sq hδ.le
      have h2 := hδε h1
      rw [← hGH (ρ w) w (hρ w).1, ← hGH 0 0 (by norm_num)]
      exact h2

/-- A non-vanishing analytic function `q` has an analytic square root `r` near `a`, with
`r w ^ 2 = q w` for **all** `w`, and whose value at `w` depends only on `q w` (so `r` is even
whenever `q` is). -/
theorem exists_analyticAt_sq_eq {q : ℂ → ℂ} {a : ℂ} (hq : AnalyticAt ℂ q a) (hq0 : q a ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ r a ≠ 0 ∧ (∀ w, r w ^ 2 = q w) ∧
      ∀ w w', q w = q w' → r w = r w' := by
  set c : ℂ := (q a) ^ ((1 / 2 : ℝ) : ℂ) with hc
  have hc2 : c ^ 2 = q a := cpow_half_sq _
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hc2
    exact hq0 hc2.symm
  refine ⟨fun w => c * (q w / q a) ^ ((1 / 2 : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine analyticAt_const.mul ?_
    refine AnalyticAt.cpow (hq.div analyticAt_const hq0) analyticAt_const ?_
    simp [div_self hq0]
  · simp [div_self hq0, hc0]
  · intro w
    rw [mul_pow, hc2, cpow_half_sq, mul_div_cancel₀ _ hq0]
  · intro w w' h
    simp only [h]

/-! ### Primitives -/

/-- An analytic function has an analytic primitive vanishing at the base point. -/
theorem exists_primitive_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ F z₀ = 0 ∧ ∀ᶠ z in 𝓝 z₀, HasDerivAt F (f z) z := by
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff.1 hf.eventually_analyticAt
  have hd : DifferentiableOn ℂ f (ball z₀ r) := fun z hz =>
    (hfr (mem_ball.1 hz)).differentiableAt.differentiableWithinAt
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  refine ⟨fun z => G z - G z₀, ?_, sub_self _, ?_⟩
  · have : DifferentiableOn ℂ (fun z => G z - G z₀) (ball z₀ r) := fun z hz =>
      ((hG z hz).differentiableAt.sub_const _).differentiableWithinAt
    exact this.analyticAt (ball_mem_nhds z₀ hr)
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact (hG z hz).sub_const _

/-- An analytic function with vanishing derivative near a point is constant near it. -/
theorem eventually_eq_const_of_deriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hd : ∀ᶠ z in 𝓝 z₀, deriv f z = 0) : ∀ᶠ z in 𝓝 z₀, f z = f z₀ := by
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff.1 (hf.eventually_analyticAt.and hd)
  have hdiff : DifferentiableOn ℂ f (ball z₀ r) := fun z hz =>
    (hfr (mem_ball.1 hz)).1.differentiableAt.differentiableWithinAt
  obtain ⟨a, ha⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
    hdiff (fun z hz => (hfr (mem_ball.1 hz)).2)
  filter_upwards [ball_mem_nhds z₀ hr] with z hz
  rw [ha z hz, ha z₀ (mem_ball_self hr)]

/-! ### The difference quotient and punctured neighbourhoods -/

/-- The difference quotient `dslope f z₀` of an analytic function is analytic. -/
theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Two functions continuous at `x` which agree on a punctured neighbourhood of `x` agree at `x`. -/
theorem eq_of_continuousAt_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (h : ∀ᶠ z in 𝓝[≠] x, f z = g z) : f x = g x :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ hz => hz.symm))

/-- If `w ^ a * A w = w ^ b * B w` near `0` with `a < b` and `A`, `B` continuous at `0`, then
`A 0 = 0`. -/
theorem eq_zero_of_pow_mul_eq_pow_mul {A B : ℂ → ℂ} {a b : ℕ} (hab : a < b)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (h : ∀ᶠ w in 𝓝 (0 : ℂ), w ^ a * A w = w ^ b * B w) : A 0 = 0 := by
  have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), A w = w ^ (b - a) * B w := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
    have hw0' : w ≠ 0 := hw0
    have hb : w ^ b = w ^ a * w ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [hb, mul_assoc] at hw
    exact mul_left_cancel₀ (pow_ne_zero a hw0') hw
  have hc : ContinuousAt (fun w : ℂ => w ^ (b - a) * B w) 0 :=
    (continuousAt_id.pow (b - a)).mul hB
  have := eq_of_continuousAt_of_eventuallyEq_nhdsNE hA hc h1
  rw [this, zero_pow (Nat.sub_ne_zero_of_lt hab), zero_mul]

/-! ### Even functions and factorizations -/

/-- An even analytic function of `w` near `0` is an analytic function `G` of `u = w²`. -/
theorem exists_analyticAt_comp_sq_of_even {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (heven : ∀ᶠ w in 𝓝 (0 : ℂ), g (-w) = g w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = g 0 ∧ ∀ᶠ w in 𝓝 (0 : ℂ), G (w ^ 2) = g w := by
  set G : ℂ → ℂ := fun u => g (u ^ ((1 / 2 : ℝ) : ℂ)) with hGdef
  have hsq : ∀ w : ℂ, (w ^ 2) ^ ((1 / 2 : ℝ) : ℂ) = w ∨ (w ^ 2) ^ ((1 / 2 : ℝ) : ℂ) = -w :=
    fun w => sq_eq_sq_iff_eq_or_eq_neg.1 (cpow_half_sq (w ^ 2))
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), G (w ^ 2) = g w := by
    filter_upwards [heven] with w hw
    simp only [hGdef]
    rcases hsq w with h | h
    · rw [h]
    · rw [h, hw]
  refine ⟨G, ?_, ?_, hev⟩
  · have h1 : AnalyticAt ℂ (fun w => w ^ (2 * 0) * G (w ^ 2)) 0 := by
      refine hg.congr ?_
      filter_upwards [hev] with w hw
      simp [hw]
    have h2 := analyticAt_of_analyticAt_pow_mul_comp_sq h1
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp
  · simp [hGdef]

/-- If `F` is analytic at `0` with `F 0 = 0` and `F' = wᵏ e` near `0` with `e 0 ≠ 0`, then
`F = w^(k+1) g` near `0` with `g` analytic at `0` and `g 0 ≠ 0`. -/
theorem exists_factor_of_deriv_eq_pow_mul {F e : ℂ → ℂ} {k : ℕ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 0) (he : AnalyticAt ℂ e 0) (he0 : e 0 ≠ 0)
    (hd : ∀ᶠ w in 𝓝 (0 : ℂ), deriv F w = w ^ k * e w) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ w in 𝓝 (0 : ℂ), F w = w ^ (k + 1) * g w := by
  -- `F` is not eventually zero, since its derivative is not
  have hne : ¬ ∀ᶠ w in 𝓝 (0 : ℂ), F w = 0 := by
    intro h
    have h1 : deriv F =ᶠ[𝓝 (0 : ℂ)] deriv (fun _ => (0 : ℂ)) :=
      Filter.EventuallyEq.deriv (h : F =ᶠ[𝓝 (0 : ℂ)] fun _ => 0)
    have h2 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), e w = 0 := by
      filter_upwards [(h1.and hd).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
      have hw0' : w ≠ 0 := hw0
      obtain ⟨hw1, hw2⟩ := hw
      rw [deriv_const] at hw1
      rw [hw1] at hw2
      exact (mul_eq_zero.1 hw2.symm).resolve_left (pow_ne_zero k hw0')
    have h3 : e 0 = 0 :=
      eq_of_continuousAt_of_eventuallyEq_nhdsNE he.continuousAt continuousAt_const h2
    exact he0 h3
  obtain ⟨n, g, hg, hg0, hFg⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.2 hne
  simp only [sub_zero, smul_eq_mul] at hFg
  -- `n ≠ 0` since `F 0 = 0`
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hFg.self_of_nhds
    rw [pow_zero, one_mul, hF0] at this
    exact hg0 this.symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  -- the derivative of `F` computed from the factorization
  have hgd : ∀ᶠ w in 𝓝 (0 : ℂ), deriv F w = w ^ j * ((j + 1 : ℂ) * g w + w * deriv g w) := by
    have h1 : deriv F =ᶠ[𝓝 (0 : ℂ)] deriv (fun w => w ^ (j + 1) * g w) :=
      Filter.EventuallyEq.deriv hFg
    filter_upwards [h1, hg.eventually_analyticAt] with w hw hgw
    have hD : HasDerivAt (fun w => w ^ (j + 1) * g w)
        (((j + 1 : ℕ) : ℂ) * w ^ (j + 1 - 1) * g w + w ^ (j + 1) * deriv g w) w :=
      (hasDerivAt_pow (j + 1) w).mul hgw.differentiableAt.hasDerivAt
    rw [hw, hD.deriv, Nat.add_sub_cancel]
    push_cast
    ring
  have hAc : ContinuousAt (fun w : ℂ => (j + 1 : ℂ) * g w + w * deriv g w) 0 :=
    (continuousAt_const.mul hg.continuousAt).add (continuousAt_id.mul hg.deriv.continuousAt)
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · exfalso
    have h1 := eq_zero_of_pow_mul_eq_pow_mul hjk hAc he.continuousAt
      ((hgd.and hd).mono fun w hw => hw.1.symm.trans hw.2)
    have h1' : (j + 1 : ℂ) * g 0 + 0 * deriv g 0 = 0 := h1
    rw [zero_mul, add_zero] at h1'
    exact hg0 ((mul_eq_zero.1 h1').resolve_left (by exact_mod_cast Nat.succ_ne_zero j))
  · exact ⟨g, hg, hg0, hFg⟩
  · exfalso
    have h1 := eq_zero_of_pow_mul_eq_pow_mul hjk he.continuousAt hAc
      ((hd.and hgd).mono fun w hw => hw.1.symm.trans hw.2)
    exact he0 h1

end LiZhongQC
