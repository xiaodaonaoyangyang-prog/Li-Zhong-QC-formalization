import LiZhongQC.Lemmas.GeodesicContacts
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
/- Archive endpoint foundation. The seven compiled s25fc helpers are unchanged. -/

/-- A genuine zero in the disc has an injective natural coordinate and a holomorphic
inverse on a closed coordinate disc, with the literal cone pullback identity exposed. -/
theorem s25ep_chart_at_zero {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ unitDisc) (hzero : φ z₀ = 0) :
    ∃ (m : ℕ) (ζ ψ : ℂ → ℂ) (r R : ℝ),
      0 < m ∧ 0 < r ∧ 0 < R ∧ closedBall z₀ r ⊆ unitDisc ∧
      ζ z₀ = 0 ∧ ψ 0 = z₀ ∧ InjOn ζ (closedBall z₀ r) ∧
      (∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
        φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) ∧
      ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
        AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w := by
  classical
  have han : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd isOpen_ball
  have hnev : ¬ ∀ᶠ z in 𝓝 z₀, φ z = 0 := by
    intro he
    have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected hz₀ he
    obtain ⟨z, hz, hnz⟩ := hne
    exact hnz (hall hz)
  obtain ⟨m, f, hf, hf0, hfactor⟩ :=
    (han z₀ hz₀).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnev
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have he := hfactor.self_of_nhds
      rw [hm] at he
      simp only [pow_zero, one_smul] at he
      exact False.elim (hf0 (he.symm.trans hzero))
    · exact hm
  obtain ⟨ζ, hζ, hζ0, hζd, hζφ⟩ := eq25_5_natural_parameter_zero hm hf hf0
    (hfactor.mono fun z hz => by simpa only [smul_eq_mul] using hz)
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ᶠ z in 𝓝 z₀, g (ζ z) = z :=
    ⟨_, hζ.hasStrictDerivAt.eventually_left_inverse hζd⟩
  have hdne : ∀ᶠ z in 𝓝 z₀, deriv ζ z ≠ 0 := hζ.deriv.continuousAt.eventually_ne hζd
  have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 ∧
      z ∈ unitDisc ∧ g (ζ z) = z := by
    filter_upwards [hζ.eventually_analyticAt, hdne, hζφ, isOpen_ball.mem_nhds hz₀, hg]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hmem : ∀ z ∈ closedBall z₀ r, dist z z₀ < ε := by
    intro z hz
    have := mem_closedBall.1 hz
    dsimp [r] at this
    linarith
  have hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 := by
    intro z hz
    obtain ⟨h1, h2, h3, -, -⟩ := hball (hmem z hz)
    exact ⟨h1, h2, h3⟩
  have hinj : InjOn ζ (closedBall z₀ r) := by
    intro x hx y hy hxy
    have hx' := (hball (hmem x hx)).2.2.2.2
    have hy' := (hball (hmem y hy)).2.2.2.2
    rw [← hx', ← hy', hxy]
  obtain ⟨hopen, hinv⟩ := psa_inverse hr hinj (fun z hz => ⟨(hchart z hz).1, (hchart z hz).2.1⟩)
  let ψ : ℂ → ℂ := Function.invFunOn ζ (ball z₀ r)
  have h0image : (0 : ℂ) ∈ ζ '' ball z₀ r := ⟨z₀, mem_ball_self hr, hζ0⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen 0 h0image
  let R : ℝ := ρ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRsub : closedBall (0 : ℂ) R ⊆ ζ '' ball z₀ r :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hρsub
  have hψan : AnalyticOnNhd ℂ ψ (ζ '' ball z₀ r) := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro w hw
    exact (hinv w hw).2.2.differentiableAt.differentiableWithinAt
  have hψ0 : ψ 0 = z₀ := by
    apply hinj (ball_subset_closedBall (hinv 0 h0image).1) (mem_closedBall_self hr.le)
    exact (hinv 0 h0image).2.1.trans hζ0.symm
  refine ⟨m, ζ, ψ, r, R, hm, hr, hR,
    fun z hz => (hball (hmem z hz)).2.2.2.1, hζ0, hψ0, hinj, hchart, ?_⟩
  intro w hw
  obtain ⟨hwmem, he, hd⟩ := hinv w (hRsub hw)
  exact ⟨hwmem, he, hψan w (hRsub hw), hd⟩

/-- Exact weighted-speed transport through a natural coordinate at a differentiability point. -/
theorem s25ep_speed_transport {φ ζ c : ℂ → ℂ} {f : ℝ → ℂ} {t : ℝ}
    (hζ : DifferentiableAt ℂ ζ (f t)) (hf : DifferentiableAt ℝ f t)
    (hφ : φ (f t) = c (ζ (f t)) * deriv ζ (f t) ^ 2) :
    phiDensity φ (f t) * ‖deriv f t‖ₑ =
      phiDensity c (ζ (f t)) * ‖deriv (ζ ∘ f) t‖ₑ := by
  have hd : HasDerivAt (ζ ∘ f) (deriv f t • deriv ζ (f t)) t :=
    hζ.hasDerivAt.scomp t hf.hasDerivAt
  have hsqrt : Real.sqrt ‖φ (f t)‖ =
      Real.sqrt ‖c (ζ (f t))‖ * ‖deriv ζ (f t)‖ := by
    rw [hφ, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [phiDensity, phiDensity, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  rw [hd.deriv, norm_smul, hsqrt]
  ring

/-- Exact segment-length transport uses only the actual curve's Lipschitz regularity
and the chart identity, including when the interval has a zero as endpoint. -/
theorem s25ep_segment_transport {φ ζ c : ℂ → ℂ} {γ : LRCurve} {a b : ℝ}
    (hab : a ≤ b) (hγ : ∃ K : ℝ≥0, LipschitzOnWith K γ.toFun (Icc a b))
    (hζ : ∀ t ∈ Icc a b, DifferentiableAt ℂ ζ (γ.toFun t))
    (hφ : ∀ t ∈ Icc a b, φ (γ.toFun t) = c (ζ (γ.toFun t)) * deriv ζ (γ.toFun t) ^ 2) :
    phiSegmentLength φ γ a b =
      ∫⁻ t in Ioo a b, phiDensity c (ζ (γ.toFun t)) * ‖deriv (ζ ∘ γ.toFun) t‖ₑ := by
  obtain ⟨K, hK⟩ := hγ
  have hdiff : ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ γ.toFun t :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rwa [uIcc_of_le hab])
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem measurableSet_Ioo] with t ht htab
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self htab
  exact s25ep_speed_transport (hζ t ht') (ht (by rwa [uIcc_of_le hab])) (hφ t ht')

/-- The inverse natural coordinate parametrizes each radial arm by a C1 regular arc,
including a nonzero ordinary derivative at the zero endpoint. -/
theorem s25ep_inverse_radial_arc {ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0)
    {v : ℂ} (hv : ‖v‖ = 1) :
    let σ : ℝ → ℂ := fun t => ψ (t • v)
    σ 0 = z₀ ∧ ContDiffOn ℝ 1 σ (Icc 0 R) ∧ InjOn σ (Icc 0 R) ∧
      (∀ t ∈ Icc 0 R, σ t ∈ ball z₀ r ∧ ζ (σ t) = t • v ∧
        HasDerivAt σ (v * (deriv ζ (σ t))⁻¹) t ∧ deriv σ t ≠ 0) ∧
      σ '' Icc 0 R = ψ '' ((fun t : ℝ => t • v) '' Icc 0 R) := by
  dsimp only
  have hv0 : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    exact zero_ne_one hv
  have htv : ∀ t ∈ Icc (0 : ℝ) R, t • v ∈ closedBall (0 : ℂ) R := by
    intro t ht
    apply mem_closedBall_zero_iff.2
    rw [norm_smul, Real.norm_of_nonneg ht.1, hv, mul_one]
    exact ht.2
  have hderiv : ∀ t ∈ Icc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => ψ (t • v)) (v * (deriv ζ (ψ (t • v)))⁻¹) t := by
    intro t ht
    simpa only [Function.comp_def, id_eq, one_smul, smul_eq_mul] using
      ((hψ (t • v) (htv t ht)).2.2.2.scomp t ((hasDerivAt_id t).smul_const v))
  refine ⟨by simpa only [zero_smul] using hψ0, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have houter : ContDiffAt ℝ 1 ψ (t • v) :=
      (hψ (t • v) (htv t ht)).2.2.1.contDiffAt.restrict_scalars ℝ
    have hinner : ContDiff ℝ 1 (fun t : ℝ => t • v) := contDiff_id.smul contDiff_const
    exact (houter.comp t hinner.contDiffAt).contDiffWithinAt
  · intro s hs t ht he
    change ψ (s • v) = ψ (t • v) at he
    have hst : s • v = t • v := by
      rw [← (hψ (s • v) (htv s hs)).2.1, ← (hψ (t • v) (htv t ht)).2.1, he]
    exact (smul_left_injective ℝ hv0) hst
  · intro t ht
    refine ⟨(hψ (t • v) (htv t ht)).1, (hψ (t • v) (htv t ht)).2.1, hderiv t ht, ?_⟩
    rw [(hderiv t ht).deriv]
    exact mul_ne_zero hv0 (inv_ne_zero (hd (t • v) (htv t ht)))
  · exact (Set.image_image ψ (fun t : ℝ => t • v) (Icc 0 R)).symm

/-- The inverse radial arm has the exact cone length R^((m+2)/2), with the original
coefficient and the actual inverse-chart parametrization in the integral. -/
theorem s25ep_inverse_radial_length {φ ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    {m : ℕ} (hm : 0 < m) (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    {v : ℂ} (hv : ‖v‖ = 1) :
    (∫⁻ t in Ioo (0 : ℝ) R,
      phiDensity φ (ψ (t • v)) * ‖deriv (fun t : ℝ => ψ (t • v)) t‖ₑ) =
        ENNReal.ofReal (R ^ (((m : ℝ) + 2) / 2)) := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 1 < c := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp [c]
    linarith
  have hc0 : c ≠ 0 := by linarith
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 := by
    intro w hw
    exact (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  have hσ := s25ep_inverse_radial_arc hR hψ0 hψ hd hv
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) R,
      phiDensity φ (ψ (t • v)) * ‖deriv (fun t : ℝ => ψ (t • v)) t‖ₑ =
        ENNReal.ofReal (c * ‖(t : ℂ) * v‖ ^ (c - 1)) *
          ‖deriv (fun t : ℝ => (t : ℂ) * v) t‖ₑ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) R := Ioo_subset_Icc_self ht
    have hσt := hσ.2.2.2.1 t ht'
    have hz := hchart _ (ball_subset_closedBall hσt.1)
    have he : (ζ ∘ fun t : ℝ => ψ (t • v)) =ᶠ[𝓝 t] (fun t : ℝ => t • v) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact (hσ.2.2.2.1 u (Ioo_subset_Icc_self hu)).2.1
    have hderiv : deriv (ζ ∘ fun t : ℝ => ψ (t • v)) t = v := by
      rw [he.deriv_eq]
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).deriv
    have hspeed := s25ep_speed_transport
      (c := fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) hz.1.differentiableAt
      hσt.2.2.1.differentiableAt hz.2.2
    rw [hderiv, hσt.2.1] at hspeed
    rw [hspeed, (hasDerivAt_ofReal_mul v t).deriv]
    congr 1
    change ENNReal.ofReal (Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * (t • v) ^ m‖) = _
    rw [s25e_rho_eq]
    simp only [c, Complex.real_smul]
  rw [setLIntegral_congr_fun measurableSet_Ioo hpoint]
  have hlen := s25e_radial_len (c := c) hc (v := v) (α := 0) (β := 1)
    (t₀ := 0) (t₁ := R) hR.le (by
      intro t ht
      simpa only [zero_add, one_mul] using ht.1)
  simpa only [zero_add, one_mul, hv, Real.one_rpow, Real.zero_rpow hc0,
    sub_zero, abs_of_nonneg (Real.rpow_nonneg hR.le c)] using hlen

/-- Within an injective cone chart the original coefficient can vanish only at the apex. -/
theorem s25ep_chart_regular {φ ζ : ℂ → ℂ} {z₀ z : ℂ} {r : ℝ} {m : ℕ}
    (hr : 0 < r) (hζ0 : ζ z₀ = 0) (hinj : InjOn ζ (closedBall z₀ r))
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hz : z ∈ closedBall z₀ r) (hne : z ≠ z₀) : φ z ≠ 0 := by
  have hζne : ζ z ≠ 0 := by
    intro he
    exact hne (hinj hz (mem_closedBall_self hr.le) (he.trans hζ0.symm))
  have hm2 : (m : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (by omega : m + 2 ≠ 0)
  rw [(hchart z hz).2.2]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (div_ne_zero hm2 (by norm_num))) (pow_ne_zero m hζne))
    (pow_ne_zero 2 (hchart z hz).2.1)

/- Requires the already compiled GeodesicContacts module and CHART_AND_SPEED.lean.inc. -/

/-- The actual non-pausing geodesic has a right-hand zero-free minimizing piece
inside a supplied natural chart at its zero contact. No radiality is assumed. -/
theorem s25ep_actual_right_piece {φ ζ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₀ < 1)
    {r : ℝ} {m : ℕ} (hr : 0 < r) (hζ0 : ζ (γ.toFun t₀) = 0)
    (hinj : InjOn ζ (closedBall (γ.toFun t₀) r))
    (hchart : ∀ z ∈ closedBall (γ.toFun t₀) r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) :
    ∃ ε > 0, t₀ + ε < 1 ∧
      InjOn γ.toFun (Icc t₀ (t₀ + ε)) ∧
      (∀ t ∈ Icc t₀ (t₀ + ε), γ.toFun t ∈ ball (γ.toFun t₀) r) ∧
      (∀ t ∈ Ioc t₀ (t₀ + ε), γ.toFun t ≠ γ.toFun t₀ ∧ φ (γ.toFun t) ≠ 0) ∧
      ∀ s ∈ Icc t₀ (t₀ + ε), ∀ t ∈ Icc t₀ (t₀ + ε), s < t →
        phiSegmentLength φ γ s t = metricDist unitDisc (phiDensity φ) (γ.toFun s) (γ.toFun t) := by
  obtain ⟨δi, hδi, hlocal⟩ := s25fc_locally_injective hφ hne hγ hp ht₀
  obtain ⟨δw, hδw, hwin⟩ := hγ.2.2 t₀ ht₀
  obtain ⟨K, hK⟩ := hγ.1
  obtain ⟨η, hη, hclose⟩ := Metric.continuousWithinAt_iff.1 (hK.continuousOn t₀ ht₀) r hr
  obtain ⟨ε, hε, hεall⟩ := exists_between
    (lt_min (sub_pos.2 ht₁) (lt_min hδi (lt_min hδw hη)))
  have hε1 : ε < 1 - t₀ := hεall.trans_le (min_le_left _ _)
  have hεi : ε < δi := (hεall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hεw : ε < δw :=
    ((hεall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hεη : ε < η :=
    ((hεall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have h01 : ∀ t ∈ Icc t₀ (t₀ + ε), t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ht₀.1.trans ht.1, by linarith [ht.2]⟩
  have hloc : Icc t₀ (t₀ + ε) ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δi) (t₀ + δi) := by
    intro t ht
    exact ⟨h01 t ht, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hpiece : InjOn γ.toFun (Icc t₀ (t₀ + ε)) := hlocal.mono hloc
  have hball : ∀ t ∈ Icc t₀ (t₀ + ε), γ.toFun t ∈ ball (γ.toFun t₀) r := by
    intro t ht
    apply mem_ball.2
    apply hclose (h01 t ht)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht.1)]
    linarith [ht.2]
  refine ⟨ε, hε, by linarith, hpiece, hball, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ Icc t₀ (t₀ + ε) := ⟨ht.1.le, ht.2⟩
    have htn : γ.toFun t ≠ γ.toFun t₀ := by
      intro he
      exact (ne_of_gt ht.1) (hpiece ht' ⟨le_rfl, by linarith⟩ he)
    exact ⟨htn, s25ep_chart_regular hr hζ0 hinj hchart (ball_subset_closedBall (hball t ht')) htn⟩
  · intro s hs t ht hst
    exact hwin s (h01 s hs) t (h01 t ht) (by linarith [hs.1]) hst (by linarith [ht.2])

end LiZhongQC


