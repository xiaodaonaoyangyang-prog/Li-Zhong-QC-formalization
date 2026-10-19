import LiZhongQC.Lemmas.CurvatureDegreeBoundary

open Complex Set Metric Filter Topology MeasureTheory intervalIntegral
open scoped Real Interval

noncomputable section
namespace LiZhongQC

/-- Uniform coefficient bounds give the perimeter bound for the actual
four-edge integral. The bound is valid without an integrability convention. -/
theorem s22sl_rectBoundary_norm_le {α : ℂ → ℂ → ℝ} {z w : ℂ} {C : ℝ}
    (h1 : ∀ ζ ∈ wv_rectF z w, ‖α ζ 1‖ ≤ C)
    (hI : ∀ ζ ∈ wv_rectF z w, ‖α ζ I‖ ≤ C) :
    ‖s22cd_rectBoundary α z w‖ ≤ 2 * C * (|w.re - z.re| + |w.im - z.im|) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => h1 _ (wv_bot_mem_rectF (uIoc_subset_uIcc hx)))
  have ht := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => h1 _ (wv_top_mem_rectF (uIoc_subset_uIcc hx)))
  have hr := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun y hy => hI _ (wv_right_mem_rectF (uIoc_subset_uIcc hy)))
  have hl := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun y hy => hI _ (wv_left_mem_rectF (uIoc_subset_uIcc hy)))
  have key : ∀ B T R L : ℝ, ‖B‖ ≤ C * |w.re - z.re| → ‖T‖ ≤ C * |w.re - z.re| →
      ‖R‖ ≤ C * |w.im - z.im| → ‖L‖ ≤ C * |w.im - z.im| →
      ‖B - T + R - L‖ ≤ 2 * C * (|w.re - z.re| + |w.im - z.im|) := by
    intro B T R L hB hT hR hL
    have e1 := norm_sub_le (B - T + R) L
    have e2 := norm_add_le (B - T) R
    have e3 := norm_sub_le B T
    linarith
  exact key _ _ _ _ hb ht hr hl

/-- Every point in the square of half-side r is at distance at most 2r from
its center. This controls every boundary point at once. -/
theorem s22sl_square_dist_le {c z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ wv_rectK (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) :
    dist z c ≤ 2 * r := by
  change z.re ∈ uIcc (c - (r : ℂ) * (1 + I)).re (c + (r : ℂ) * (1 + I)).re ∧
    z.im ∈ uIcc (c - (r : ℂ) * (1 + I)).im (c + (r : ℂ) * (1 + I)).im at hz
  have hle₁ : c.re - r ≤ c.re + r := by linarith
  have hle₂ : c.im - r ≤ c.im + r := by linarith
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero] at hz
  rw [uIcc_of_le hle₁, uIcc_of_le hle₂] at hz
  have hre : |z.re - c.re| ≤ r := abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |z.im - c.im| ≤ r := abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  rw [dist_eq_norm]
  calc
    ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * r := by simpa only [Complex.sub_re, Complex.sub_im] using
      (show |z.re - c.re| + |z.im - c.im| ≤ 2 * r by linarith)

/-- The center is not on a positive-radius square frame. -/
theorem s22sl_square_frame_ne_center {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ wv_rectF (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) :
    z ≠ c := by
  intro he
  subst z
  apply hz.2
  change ((c - (r : ℂ) * (1 + I)).re < c.re ∧
      c.re < (c + (r : ℂ) * (1 + I)).re) ∧
      ((c - (r : ℂ) * (1 + I)).im < c.im ∧
      c.im < (c + (r : ℂ) * (1 + I)).im)
  simp [Complex.mul_re, Complex.mul_im, hr]

/-- Pointwise continuity at the center suffices to make the smooth boundary
term vanish on shrinking squares. The proof gives an explicit 8Cr bound. -/
theorem s22sl_continuous_boundary_tendsto_zero {α : ℂ → ℂ → ℝ} {c : ℂ}
    (h1 : ContinuousAt (fun z => α z 1) c)
    (hI : ContinuousAt (fun z => α z I) c) :
    Tendsto
      (fun r : ℝ => s22cd_rectBoundary α
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C := ‖α c 1‖ + ‖α c I‖ + 1
  have he1 : ∀ᶠ z in 𝓝 c, ‖α z 1‖ < ‖α c 1‖ + 1 :=
    h1.norm (gt_mem_nhds (lt_add_one _))
  have heI : ∀ᶠ z in 𝓝 c, ‖α z I‖ < ‖α c I‖ + 1 :=
    hI.norm (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (he1.and heI)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ / 3 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))]
      with r hr hlt
    exact ⟨hr, hlt⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun r : ℝ => 8 * C * r)
    (Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [hev] with r hr
    have hbound : ∀ z ∈ wv_rectF
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)),
        ‖α z 1‖ ≤ C ∧ ‖α z I‖ ≤ C := by
      intro z hz
      have hzball : z ∈ ball c δ := by
        rw [mem_ball]
        exact (s22sl_square_dist_le hr.1.le hz.1).trans_lt (by linarith [hr.2])
      obtain ⟨h₁, h₂⟩ := hb hzball
      constructor
      · show ‖α z 1‖ ≤ ‖α c 1‖ + ‖α c I‖ + 1
        linarith [norm_nonneg (α c I)]
      · show ‖α z I‖ ≤ ‖α c 1‖ + ‖α c I‖ + 1
        linarith [norm_nonneg (α c 1)]
    have hnorm := s22sl_rectBoundary_norm_le
      (fun z hz => (hbound z hz).1) (fun z hz => (hbound z hz).2)
    have he : 2 * C *
        (|(c + (r : ℂ) * (1 + I)).re - (c - (r : ℂ) * (1 + I)).re| +
         |(c + (r : ℂ) * (1 + I)).im - (c - (r : ℂ) * (1 + I)).im|) = 8 * C * r := by
      simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero]
      rw [show c.re + r - (c.re - r) = 2 * r by ring,
        show c.im + r - (c.im - r) = 2 * r by ring,
        abs_of_pos (by linarith [hr.1] : 0 < 2 * r)]
      ring
    exact he ▸ hnorm
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (show Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) from
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) :
        Tendsto (fun r : ℝ => (8 * C) * r) (𝓝[>] (0 : ℝ)) (𝓝 ((8 * C) * 0)))

/-- Every punctured neighborhood property holds on every sufficiently small
positive square frame. This transports local analytic regularity to contours. -/
theorem s22sl_eventually_on_square_frame {c : ℂ} {P : ℂ → Prop}
    (hP : ∀ᶠ z in 𝓝[≠] c, P z) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ∀ z ∈
      wv_rectF (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)), P z := by
  rw [eventually_nhdsWithin_iff] at hP
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hP
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))]
    with r hr hlt
  intro z hz
  have hdist : dist z c < δ :=
    (s22sl_square_dist_le (le_of_lt hr) hz.1).trans_lt (by linarith)
  exact hb (mem_ball.mpr hdist) (s22sl_square_frame_ne_center hr hz)

/-- Equality of form germs off the center gives equality of all sufficiently
small square boundary integrals. No interchange of limits and integrals occurs. -/
theorem s22sl_boundary_eventuallyEq_of_punctured_germ
    {α β : ℂ → ℂ → ℝ} {c : ℂ}
    (he : ∀ᶠ z in 𝓝[≠] c, ∀ v, α z v = β z v) :
    (fun r : ℝ => s22cd_rectBoundary α
      (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) =ᶠ[𝓝[>] (0 : ℝ)]
    (fun r : ℝ => s22cd_rectBoundary β
      (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) := by
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp he
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))]
    with r hr hlt
  apply s22cd_rectBoundary_congr
  intro z hz v
  have hdist : dist z c < δ :=
    (s22sl_square_dist_le (le_of_lt hr) hz.1).trans_lt (by linarith)
  exact hb (mem_ball.mpr hdist) (s22sl_square_frame_ne_center hr hz) v

/-- A finite meromorphic order supplies a genuine analytic regular part of
the logarithmic derivative. Poles are handled by integer powers. -/
theorem s22sl_meromorphic_logDeriv_regular_part {f : ℂ → ℂ} {c : ℂ} {m : ℤ}
    (hf : MeromorphicAt f c) (hm : meromorphicOrderAt f c = (m : ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      ∀ᶠ z in 𝓝[≠] c, logDeriv f z = (m : ℂ) / (z - c) + g z := by
  obtain ⟨u, hu, hne, he⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm
  have he' : f =ᶠ[𝓝[≠] c] (fun z => (z - c) ^ m * u z) := by
    simpa only [smul_eq_mul, Filter.EventuallyEq] using he
  refine ⟨logDeriv u, ?_, ?_⟩
  · change AnalyticAt ℂ (fun z => deriv u z / u z) c
    exact hu.deriv.div hu hne
  · filter_upwards [logDeriv_congr_nhdsNE he',
      nhdsWithin_le_nhds hu.eventually_analyticAt,
      nhdsWithin_le_nhds (hu.continuousAt.eventually_ne hne),
      self_mem_nhdsWithin] with z hez huz hun hzc
    rw [hez, logDeriv_fun_mul (f := fun w : ℂ => (w - c) ^ m) (g := u) z (zpow_ne_zero m (sub_ne_zero.mpr hzc)) hun
((differentiableAt_id.sub_const c).zpow (m := m) (Or.inl (sub_ne_zero.mpr hzc)))
      huz.differentiableAt]
    have hp : logDeriv (fun w : ℂ => (w - c) ^ m) z = (m : ℂ) / (z - c) := by
      rw [logDeriv_fun_zpow (f := fun x : ℂ => x - c) (by fun_prop)]
      rw [logDeriv_apply]
      simp only [deriv_sub_const, deriv_id'', mul_one_div]
    rw [hp]

/-- The actual logarithmic-derivative boundary integral of a meromorphic
coefficient converges to 2*pi times its signed order. The analytic remainder
and the singular polar part are constructed from MeromorphicAt itself. -/
theorem s22sl_meromorphic_phase_boundary_limit {f : ℂ → ℂ} {c : ℂ} {m : ℤ}
    (hf : MeromorphicAt f c) (hm : meromorphicOrderAt f c = (m : ℤ)) :
    Tendsto
      (fun r : ℝ => s22cd_rectBoundary (fun z v => (deriv f z / f z * v).im)
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * π * (m : ℝ))) := by
  obtain ⟨g, hg, hfg⟩ := s22sl_meromorphic_logDeriv_regular_part hf hm
  have heform : ∀ᶠ z in 𝓝[≠] c, ∀ v : ℂ,
      (deriv f z / f z * v).im = (((m : ℂ) / (z - c) + g z) * v).im := by
    filter_upwards [hfg] with z hz
    intro v
    change (logDeriv f z * v).im = _
    rw [hz]
  have he := s22sl_boundary_eventuallyEq_of_punctured_germ heform
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hg.eventually_analyticAt
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ / 3 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))]
      with r hr hlt
    exact ⟨hr, hlt⟩
  have heperiod :
      (fun r : ℝ => s22cd_rectBoundary (fun z v => (deriv f z / f z * v).im)
        (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => 2 * π * (m : ℝ) +
        s22cd_rectBoundary (fun z v => (g z * v).im)
          (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) := by
    filter_upwards [he, hsmall] with r her hr
    rw [her]
    have hgc : ContinuousOn g
        (wv_rectF (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) := by
      intro z hz
      have hd : dist z c < δ :=
        (s22sl_square_dist_le hr.1.le hz.1).trans_lt (by linarith [hr.2])
      exact (hball (mem_ball.mpr hd)).continuousAt.continuousWithinAt
    have hpc : ContinuousOn (fun z : ℂ => (m : ℂ) / (z - c))
        (wv_rectF (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) :=
      continuousOn_const.div (continuous_id.sub continuous_const).continuousOn
        (fun z hz => sub_ne_zero.mpr (s22sl_square_frame_ne_center hr.1 hz))
    have hsum : ContinuousOn (fun z : ℂ => (m : ℂ) / (z - c) + g z)
        (wv_rectF (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I))) := hpc.add hgc
    rw [s22cd_rectBoundary_im hsum, wv_rectBdry_add hpc hgc,
      Complex.add_im, ← s22cd_rectBoundary_im hpc,
      ← s22cd_rectBoundary_im hgc]
    rw [s22cd_polar_boundary m
      (by simpa [Complex.mul_re] using hr.1)
      (by simpa [Complex.mul_re] using hr.1)
      (by simpa [Complex.mul_im] using hr.1)
      (by simpa [Complex.mul_im] using hr.1)]
  have hg1 : ContinuousAt (fun z => (g z * 1).im) c :=
    (by have := hg.continuousAt; fun_prop)
  have hgI : ContinuousAt (fun z => (g z * I).im) c :=
    (by have := hg.continuousAt; fun_prop)
  have hg0 := s22sl_continuous_boundary_tendsto_zero (α := fun z v => (g z * v).im) hg1 hgI
  have hlim : Tendsto
      (fun r : ℝ => 2 * π * (m : ℝ) +
        s22cd_rectBoundary (fun z v => (g z * v).im)
          (c - (r : ℂ) * (1 + I)) (c + (r : ℂ) * (1 + I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * π * (m : ℝ))) := by
    simpa only [add_zero] using tendsto_const_nhds.add hg0
  exact hlim.congr' heperiod.symm

end LiZhongQC
