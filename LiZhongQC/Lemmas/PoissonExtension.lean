import Mathlib.Analysis.Complex.Harmonic.Poisson
import LiZhongQC.Basic

/-!
# The Dirichlet problem on a disc

Mathlib's `Mathlib.Analysis.Complex.Harmonic.Poisson` proves the Poisson integral FORMULA: a
harmonic function on a disc equals its own Poisson average on the boundary. This file supplies
the missing converse — the actual solver: continuous boundary data on a circle extends to a
function harmonic inside the disc and continuous up to the closed disc, agreeing with the given
data on the circle.

This is `B1`, the first building block of Stage B of Theorem 2.1 case (iii) (LZ2 Step 3): the
Perron-method construction of barriers for the general Dirichlet problem needs a solver on discs.

The extension is built as the real part of `w ↦ circleAverage (herglotzRieszKernel c w · * g ·) c
R`, a genuinely `ℂ`-analytic function of `w` obtained by differentiating under the integral sign
at `𝕜 = ℂ` (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`); harmonicity of
the real part then follows from `AnalyticAt.harmonicAt_re`. Boundary attainment is the classical
approximate-identity argument for the Poisson kernel, using its explicit formula
`(R² - ‖w-c‖²)/‖z-w‖²` directly rather than the two `Mathlib.Analysis.Complex.Poisson` estimate
lemmas (which bound the kernel by a global ratio, not by distance to the boundary point).
-/

open Complex Set Metric Filter Topology InnerProductSpace MeasureTheory

noncomputable section

namespace LiZhongQC

/-- The derivative in `w` of the Herglotz–Riesz kernel `herglotzRieszKernel c w z`, for `z` off
the pole `w`. -/
theorem hasDerivAt_herglotzRieszKernel (c z w : ℂ) (hzw : z - w ≠ 0) :
    HasDerivAt (fun w : ℂ => herglotzRieszKernel c w z) (2*(z-c)/((z-c)-(w-c))^2) w := by
  unfold herglotzRieszKernel
  have h1 : HasDerivAt (fun w : ℂ => (z - c) + (w - c)) 1 w := by
    have heq : (fun w : ℂ => (z-c)+(w-c)) = fun w => (w - c) + (z-c) := by ext w; ring
    rw [heq]
    simpa using (hasDerivAt_id w).sub_const c |>.add_const (z-c)
  have h2 : HasDerivAt (fun w : ℂ => (z - c) - (w - c)) (-1) w := by
    have hh : HasDerivAt (fun w : ℂ => (w-c)) 1 w := by simpa using (hasDerivAt_id w).sub_const c
    simpa using hh.const_sub (z-c)
  have hne : (z - c) - (w - c) ≠ 0 := by
    intro h; apply hzw; linear_combination h
  have hdiv := h1.div h2 hne
  convert hdiv using 1
  field_simp
  ring

/-- **B1 (Dirichlet problem on a disc)**: continuous boundary data on a circle extends to a
function harmonic inside and continuous on the closed disc. -/
theorem exists_harmonicOnNhd_continuousOn_closedBall_eqOn_sphere {c : ℂ} {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere c R)) :
    ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball c R) ∧ ContinuousOn u (closedBall c R) ∧
      EqOn u g (sphere c R) := by
  set K : ℂ → ℝ → ℂ := fun w θ => herglotzRieszKernel c w (circleMap c R θ) * (g (circleMap c R θ) : ℂ)
    with hK_def
  set Iw : ℂ → ℂ := fun w => ∫ θ in (0:ℝ)..(2*Real.pi), K w θ with hIw_def
  -- boundedness of g on the sphere
  have hspherene : (sphere c R).Nonempty := ⟨c + R, by simp [Complex.dist_eq, abs_of_pos hR]⟩
  have hgbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ sphere c R, |g z| ≤ M := by
    obtain ⟨z₀, hz₀mem, hz₀max⟩ := (isCompact_sphere c R).exists_isMaxOn hspherene hg.abs
    exact ⟨|g z₀|, abs_nonneg _, fun z hz => hz₀max hz⟩
  obtain ⟨M, hM0, hM⟩ := hgbdd
  set Kderiv : ℂ → ℝ → ℂ :=
    fun w θ => (2*(circleMap c R θ - c)/((circleMap c R θ-c)-(w-c))^2) * (g (circleMap c R θ) : ℂ)
    with hKderiv_def
  have hcircmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R := fun θ => by
    rw [mem_sphere, Complex.dist_eq, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
  have hgcirc_cont : Continuous (fun θ : ℝ => g (circleMap c R θ)) :=
    hg.comp_continuous (continuous_circleMap c R) hcircmem
  have hgcirc_cont' : Continuous (fun θ : ℝ => (g (circleMap c R θ) : ℂ)) :=
    Complex.continuous_ofReal.comp hgcirc_cont
  have hKcont : ∀ w, w ∉ sphere c R → Continuous (K w) := by
    intro w hw
    apply Continuous.mul _ hgcirc_cont'
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      intro hcon
      apply hw
      rw [mem_sphere, Complex.dist_eq]
      have : circleMap c R θ - w = 0 := by linear_combination hcon
      have hw' : w = circleMap c R θ := by linear_combination -this
      rw [hw', circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
  have hmain : ∀ w₀ ∈ ball c R, HasDerivAt Iw (∫ θ in (0:ℝ)..(2*Real.pi), Kderiv w₀ θ) w₀ := by
    intro w₀ hw₀
    rw [mem_ball, Complex.dist_eq] at hw₀
    set ρ : ℝ := (R - ‖w₀ - c‖)/2 with hρ_def
    have hρpos : 0 < ρ := by rw [hρ_def]; linarith [hw₀]
    have hballsub : ∀ w ∈ ball w₀ ρ, w ∉ sphere c R := by
      intro w hw hmem
      rw [mem_ball, Complex.dist_eq] at hw
      rw [mem_sphere, Complex.dist_eq] at hmem
      have h1 : ‖w - c‖ ≤ ‖w - w₀‖ + ‖w₀ - c‖ := by
        calc ‖w - c‖ = ‖(w-w₀)+(w₀-c)‖ := by ring_nf
          _ ≤ ‖w-w₀‖+‖w₀-c‖ := norm_add_le _ _
      rw [hmem] at h1
      have : ‖w - w₀‖ = ‖w₀ - w‖ := norm_sub_rev _ _
      rw [this] at h1
      linarith [hw]
    have hboundfn : ∀ θ : ℝ, ∀ w ∈ ball w₀ ρ, ‖Kderiv w θ‖ ≤ (2*R*M)/ρ^2 := by
      intro θ w hwmem
      have heq : (circleMap c R θ - c) - (w - c) = circleMap c R θ - w := by ring
      have hden : ρ < ‖circleMap c R θ - w‖ := by
        rw [mem_ball, Complex.dist_eq] at hwmem
        have h1 : ‖circleMap c R θ - w₀‖ ≥ ‖circleMap c R θ - c‖ - ‖w₀ - c‖ := by
          have := norm_sub_norm_le (circleMap c R θ - c) (w₀ - c)
          have heq2 : (circleMap c R θ - c) - (w₀ - c) = circleMap c R θ - w₀ := by ring
          rwa [heq2] at this
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR] at h1
        have h2 : ‖circleMap c R θ - w‖ ≥ ‖circleMap c R θ - w₀‖ - ‖w₀ - w‖ := by
          have hh := norm_sub_norm_le (circleMap c R θ - w₀) (-(w₀ - w))
          have heq3 : (circleMap c R θ - w₀) - (-(w₀ - w)) = circleMap c R θ - w := by ring
          rw [heq3, norm_neg] at hh
          exact hh
        have h3 : ‖w₀ - w‖ = ‖w - w₀‖ := norm_sub_rev _ _
        rw [hρ_def] at *
        nlinarith [h1, h2, h3, hwmem]
      have hd0 : (0:ℝ) < ‖circleMap c R θ - w‖ := lt_trans hρpos hden
      rw [hKderiv_def]
      simp only [norm_mul]
      rw [heq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖(2:ℂ)*(circleMap c R θ - c)‖ = 2*R := by
        rw [norm_mul, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]; norm_num
      rw [h1]
      have hkey : (2*R)/(‖circleMap c R θ - w‖^2) ≤ (2*R)/(ρ^2) := by
        apply div_le_div_of_nonneg_left (by linarith [hR]) (by positivity)
        nlinarith [hden, hρpos]
      calc (2*R) / ‖circleMap c R θ - w‖^2 * |g (circleMap c R θ)|
          ≤ (2*R/ρ^2) * M := mul_le_mul hkey (hM _ (hcircmem θ)) (abs_nonneg _) (by positivity)
        _ = 2*R*M/ρ^2 := by ring
    have hdiffw : ∀ θ : ℝ, ∀ w ∈ ball w₀ ρ, HasDerivAt (fun w => K w θ) (Kderiv w θ) w := by
      intro θ w hw
      have hwsph : w ∉ sphere c R := hballsub w hw
      have hzw : circleMap c R θ - w ≠ 0 := by
        intro h
        apply hwsph
        have : w = circleMap c R θ := by linear_combination -h
        rw [this]; exact hcircmem θ
      have hd := hasDerivAt_herglotzRieszKernel c (circleMap c R θ) w hzw
      simpa [hK_def, hKderiv_def] using hd.mul_const (g (circleMap c R θ) : ℂ)
    have hcontK : ∀ w, w ∈ ball w₀ ρ → Continuous (K w) := fun w hw => hKcont w (hballsub w hw)
    have hcontKd : ∀ w, w ∈ ball w₀ ρ → Continuous (Kderiv w) := by
      intro w hw
      apply Continuous.mul _ hgcirc_cont'
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro θ
      have hwsph : w ∉ sphere c R := hballsub w hw
      intro hcon
      apply hwsph
      have hcon' : (circleMap c R θ - c) - (w - c) = 0 := by
        have := sq_eq_zero_iff.mp hcon
        exact this
      have : w = circleMap c R θ := by linear_combination -hcon'
      rw [this]; exact hcircmem θ
    have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := K) (F' := Kderiv) (x₀ := w₀) (s := ball w₀ ρ) (bound := fun _ => 2*R*M/ρ^2)
      (μ := volume) (a := 0) (b := 2*Real.pi)
      (Metric.ball_mem_nhds w₀ hρpos)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hρpos)
        (fun w hw => (hcontK w hw).aestronglyMeasurable))
      ((hcontK w₀ (mem_ball_self hρpos)).intervalIntegrable 0 (2*Real.pi))
      (hcontKd w₀ (mem_ball_self hρpos)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ _ => hboundfn θ))
      intervalIntegrable_const
      (Filter.Eventually.of_forall (fun θ _ => hdiffw θ))
    exact this.2
  -- wrap with the (2π)⁻¹ factor to match circleAverage
  set Fw : ℂ → ℂ := fun w => Real.circleAverage (fun z => herglotzRieszKernel c w z * (g z : ℂ)) c R
    with hFw_def
  have hFw_eq : ∀ w, Fw w = ((2*Real.pi:ℝ))⁻¹ • Iw w := by
    intro w
    simp only [hFw_def, hIw_def, hK_def, Real.circleAverage_def]
  have hFwderiv : ∀ w₀ ∈ ball c R,
      HasDerivAt Fw (((2*Real.pi:ℝ))⁻¹ • (∫ θ in (0:ℝ)..(2*Real.pi), Kderiv w₀ θ)) w₀ := by
    intro w₀ hw₀
    have h1 := (hmain w₀ hw₀).const_smul ((2*Real.pi:ℝ)⁻¹)
    have h2 : ((2*Real.pi:ℝ)⁻¹) • Iw = Fw := by
      ext w; exact (hFw_eq w).symm
    rwa [h2] at h1
  have hFwdiffOn : DifferentiableOn ℂ Fw (ball c R) :=
    fun w hw => (hFwderiv w hw).differentiableAt.differentiableWithinAt
  have hFwanalytic : AnalyticOnNhd ℂ Fw (ball c R) := hFwdiffOn.analyticOnNhd isOpen_ball
  -- definition of u
  set u : ℂ → ℝ := fun w => if ‖w - c‖ < R then (Fw w).re else g w with hu_def
  -- harmonicity
  have hharm : HarmonicOnNhd u (ball c R) := by
    intro w hw
    have heq : u =ᶠ[𝓝 w] fun w => (Fw w).re := by
      filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
      rw [hu_def]
      simp only
      rw [ite_eq_left]
      rwa [mem_ball, Complex.dist_eq] at hw'
    rw [harmonicAt_congr_nhds heq]
    exact (hFwanalytic w hw).harmonicAt_re
  -- circleAverage(poissonKernel c w) c R = 1
  have hpoisson_one : ∀ w ∈ ball c R, Real.circleAverage (poissonKernel c w) c R = 1 := by
    intro w hw
    have hharmconst : HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall c R) := by
      intro x _
      have hac : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) x := analyticAt_const
      have hh := hac.harmonicAt_re
      simpa using hh
    have hres := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hharmconst hw
    have heq : (poissonKernel c w • (fun _ : ℂ => (1:ℝ))) = poissonKernel c w := by
      ext z; simp
    rwa [heq] at hres
  -- poissonKernel is nonneg on the sphere for interior w
  have hpoisson_nonneg : ∀ w ∈ ball c R, ∀ z ∈ sphere c R, 0 ≤ poissonKernel c w z := by
    intro w hw z hz
    rw [poissonKernel_def]
    apply div_nonneg _ (sq_nonneg _)
    rw [mem_sphere, Complex.dist_eq] at hz
    rw [mem_ball, Complex.dist_eq] at hw
    rw [hz]
    nlinarith [hw, norm_nonneg (w-c)]
  -- u agrees with the Poisson average of g on the interior
  have huEqPoisson : ∀ w ∈ ball c R, u w = Real.circleAverage (fun z => poissonKernel c w z * g z) c R := by
    intro w hw
    have hwsph : w ∉ sphere c R := by
      intro hmem
      rw [mem_sphere] at hmem; rw [mem_ball] at hw
      rw [hmem] at hw; exact lt_irrefl _ hw
    have hCI : CircleIntegrable (fun z => herglotzRieszKernel c w z * (g z : ℂ)) c R :=
      (hKcont w hwsph).intervalIntegrable 0 (2*Real.pi)
    have hcomm := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hCI
    have hueq : u w = (Fw w).re := by
      rw [hu_def]; simp only; rw [ite_eq_left (by rwa [mem_ball, Complex.dist_eq] at hw)]
    rw [hueq, hFw_def]
    show (Complex.reCLM (Real.circleAverage (fun z => herglotzRieszKernel c w z * (g z:ℂ)) c R)) = _
    rw [← hcomm]
    congr 1
    ext z
    simp only [Function.comp_apply, Complex.reCLM_apply]
    have hre : (herglotzRieszKernel c w z).re = poissonKernel c w z :=
      (congrFun poissonKernel_eq_re_herglotzRieszKernel z).symm
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ← hre]
    ring
  refine ⟨u, hharm, ?_, ?_⟩
  · intro ζ₀ hζ₀
    rw [mem_closedBall] at hζ₀
    rcases lt_or_eq_of_le hζ₀ with hlt | heqR
    · -- interior point: continuity from analyticity of Fw
      have hζ₀ball : ζ₀ ∈ ball c R := by rw [mem_ball]; exact hlt
      apply ContinuousAt.continuousWithinAt
      have heq2 : u =ᶠ[𝓝 ζ₀] fun w => (Fw w).re := by
        filter_upwards [isOpen_ball.mem_nhds hζ₀ball] with w' hw'
        rw [hu_def]; simp only
        rw [ite_eq_left]; rwa [mem_ball, Complex.dist_eq] at hw'
      rw [continuousAt_congr heq2]
      exact Complex.continuous_re.continuousAt.comp
        ((hFwanalytic ζ₀ hζ₀ball).differentiableAt.continuousAt)
    · -- boundary point ζ₀ ∈ sphere c R: approximate identity argument
      have hζ₀sphere : ζ₀ ∈ sphere c R := by
        rw [mem_sphere]; rw [Complex.dist_eq] at heqR ⊢; exact heqR
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
        Metric.continuousWithinAt_iff.mp (hg.continuousWithinAt hζ₀sphere) (ε/2) (by linarith)
      set δ : ℝ := min (δ₁/2) (min R (ε*δ₁^2/(64*(R*M+1)))) with hδ_def
      have hδpos : 0 < δ := by
        rw [hδ_def]
        apply lt_min (by linarith) (lt_min hR (by positivity))
      refine ⟨δ, hδpos, ?_⟩
      intro w hwcb hwdist
      rw [mem_closedBall, Complex.dist_eq] at hwcb
      rw [Complex.dist_eq] at hwdist
      have hζ₀n : ‖ζ₀ - c‖ = R := by
        rw [mem_sphere, Complex.dist_eq] at hζ₀sphere; exact hζ₀sphere
      have hζ₀wn : ‖ζ₀ - w‖ < δ := by
        rw [show ζ₀ - w = -(w - ζ₀) by ring, norm_neg]; exact hwdist
      have hu_ζ₀ : u ζ₀ = g ζ₀ := by
        rw [hu_def]; simp only
        rw [ite_eq_right]; rw [hζ₀n]; exact lt_irrefl R
      rw [Real.dist_eq, hu_ζ₀]
      by_cases hwmem : ‖w - c‖ < R
      · -- interior case: Poisson-average estimate
        have hw' : w ∈ ball c R := by rwa [mem_ball, Complex.dist_eq]
        have hwsph : w ∉ sphere c R := by
          intro hmem; rw [mem_sphere, Complex.dist_eq] at hmem
          rw [hmem] at hwmem; exact lt_irrefl _ hwmem
        have hwne : ∀ z ∈ sphere c R, z - w ≠ 0 := by
          intro z hz hcon
          apply hwsph
          have : z = w := by linear_combination hcon
          rw [← this]; exact hz
        have hpoisCI : ContinuousOn (poissonKernel c w) (sphere c R) := by
          have hfe : poissonKernel c w =
              fun z => (‖z-c‖^2-‖w-c‖^2)/‖(z-c)-(w-c)‖^2 := funext (poissonKernel_def c w)
          rw [hfe]
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro z hzmem
          simp only [ne_eq, sq_eq_zero_iff, norm_eq_zero]
          intro hcon
          exact hwne z hzmem (by linear_combination hcon)
        rw [huEqPoisson w hw']
        have hgz : ∀ z ∈ sphere c R, poissonKernel c w z * |g z - g ζ₀| ≤
            poissonKernel c w z * (ε/2) + 16*R*M*δ/δ₁^2 := by
          intro z hz
          by_cases hnear : dist z ζ₀ < δ₁
          · have hgdiff : |g z - g ζ₀| < ε/2 := by
              have := hδ₁ hz hnear
              rwa [Real.dist_eq] at this
            have h1 : poissonKernel c w z * |g z - g ζ₀| ≤ poissonKernel c w z * (ε/2) :=
              mul_le_mul_of_nonneg_left hgdiff.le (hpoisson_nonneg w hw' z hz)
            have hnn : 0 ≤ 16*R*M*δ/δ₁^2 := by positivity
            linarith [h1, hnn]
          · push Not at hnear
            have h1 : ‖z - ζ₀‖ ≥ δ₁ := by rwa [← Complex.dist_eq]
            have hfar : ‖z - w‖ ≥ δ₁/2 := by
              have h3 : ‖z - w‖ ≥ ‖z-ζ₀‖ - ‖ζ₀-w‖ := by
                have hh := norm_sub_norm_le (z-ζ₀) (-(ζ₀-w))
                have heq3 : (z-ζ₀)-(-(ζ₀-w)) = z - w := by ring
                rw [heq3, norm_neg] at hh
                exact hh
              have hδhalf : δ ≤ δ₁/2 := by rw [hδ_def]; exact min_le_left _ _
              nlinarith [h1, hζ₀wn, h3, hδhalf]
            have hzsphere : ‖z-c‖ = R := by
              rw [mem_sphere, Complex.dist_eq] at hz; exact hz
            have hpois_bound : poissonKernel c w z ≤ 8*R*δ/δ₁^2 := by
              rw [poissonKernel_def, hzsphere]
              rw [mem_ball, Complex.dist_eq] at hw'
              have heqzw : (z - c) - (w - c) = z - w := by ring
              rw [heqzw]
              have hnum : R^2 - ‖w-c‖^2 ≤ 2*R*δ := by
                have h4 : R - ‖w-c‖ ≤ ‖ζ₀-w‖ := by
                  have h5 : ‖ζ₀-c‖ - ‖w-c‖ ≤ ‖ζ₀-w‖ := by
                    have hh := norm_sub_norm_le (ζ₀-c) (w-c)
                    have heq5 : (ζ₀-c)-(w-c) = ζ₀-w := by ring
                    rwa [heq5] at hh
                  rw [hζ₀n] at h5; exact h5
                nlinarith [h4, hζ₀wn]
              have hnumnn : 0 ≤ R^2 - ‖w-c‖^2 := by nlinarith [hw'.le, norm_nonneg (w-c)]
              have hdennn : (δ₁/2)^2 ≤ ‖z-w‖^2 := by
                have h6 : (0:ℝ) ≤ δ₁/2 := by linarith [hδ₁pos]
                nlinarith [hfar, h6]
              have hdenpos : (0:ℝ) < (δ₁/2)^2 := by positivity
              have hzwpos : (0:ℝ) < ‖z-w‖^2 := by nlinarith [hdennn, hdenpos]
              have hstep : (R^2-‖w-c‖^2)/‖z-w‖^2 ≤ (2*R*δ)/(δ₁/2)^2 := by
                calc (R^2-‖w-c‖^2)/‖z-w‖^2 ≤ (2*R*δ)/‖z-w‖^2 := by
                      apply div_le_div_of_nonneg_right hnum hzwpos.le
                  _ ≤ (2*R*δ)/(δ₁/2)^2 := by
                      apply div_le_div_of_nonneg_left (by positivity) hdenpos hdennn
              linarith [hstep, show (2*R*δ)/(δ₁/2)^2 = 8*R*δ/δ₁^2 from by ring]
            have hden_pos : (0:ℝ) < (δ₁/2)^2 := by positivity
            have h7 : poissonKernel c w z ≤ 8*R*δ/δ₁^2 := hpois_bound
            have hgbound : |g z - g ζ₀| ≤ 2*M := by
              have h8 := hM z hz
              have h9 := hM ζ₀ hζ₀sphere
              have htri : |g z - g ζ₀| ≤ |g z| + |g ζ₀| := by
                have h10 := abs_sub_le (g z) 0 (g ζ₀)
                simpa using h10
              linarith [htri, h8, h9]
            have hpnn : 0 ≤ poissonKernel c w z := hpoisson_nonneg w hw' z hz
            calc poissonKernel c w z * |g z-g ζ₀| ≤ (8*R*δ/δ₁^2) * (2*M) := by
                  apply mul_le_mul h7 hgbound (abs_nonneg _) (by positivity)
              _ = 16*R*M*δ/δ₁^2 := by ring
              _ ≤ poissonKernel c w z * (ε/2) + 16*R*M*δ/δ₁^2 := by
                  nlinarith [mul_nonneg hpnn hε.le]
        have hstep1 : |Real.circleAverage (fun z => poissonKernel c w z * g z) c R - g ζ₀|
            ≤ Real.circleAverage (fun z => poissonKernel c w z * (ε/2) + 16*R*M*δ/δ₁^2) c R := by
          have heq1 : Real.circleAverage (fun z => poissonKernel c w z * g z) c R - g ζ₀ =
              Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ₀)) c R := by
            have hexp : (fun z => poissonKernel c w z * (g z - g ζ₀)) =
                (fun z => poissonKernel c w z * g z) - (fun z => poissonKernel c w z * g ζ₀) := by
              ext z; simp [mul_sub]
            rw [hexp]
            have hCI1 : CircleIntegrable (fun z => poissonKernel c w z * g z) c R :=
              ContinuousOn.circleIntegrable hR.le (hpoisCI.mul hg)
            have hCI2 : CircleIntegrable (fun z => poissonKernel c w z * g ζ₀) c R :=
              ContinuousOn.circleIntegrable hR.le (hpoisCI.mul continuousOn_const)
            rw [Real.circleAverage_sub hCI1 hCI2]
            congr 1
            rw [show (fun z => poissonKernel c w z * g ζ₀) = g ζ₀ • poissonKernel c w from by
              ext z; simp [mul_comm]]
            rw [Real.circleAverage_smul, hpoisson_one w hw']
            ring
          rw [heq1]
          calc |Real.circleAverage (fun z => poissonKernel c w z * (g z-g ζ₀)) c R|
              ≤ Real.circleAverage (fun z => |poissonKernel c w z * (g z - g ζ₀)|) c R :=
                Real.abs_circleAverage_le_circleAverage_abs
            _ ≤ Real.circleAverage (fun z => poissonKernel c w z * (ε/2) + 16*R*M*δ/δ₁^2) c R := by
                apply Real.circleAverage_mono
                · exact ContinuousOn.circleIntegrable hR.le
                    ((hpoisCI.mul (hg.sub continuousOn_const)).abs)
                · exact ContinuousOn.circleIntegrable hR.le
                    ((hpoisCI.mul continuousOn_const).add continuousOn_const)
                · intro z hz'
                  have hz : z ∈ sphere c R := by rwa [abs_of_pos hR] at hz'
                  rw [abs_mul, abs_of_nonneg (hpoisson_nonneg w hw' z hz)]
                  exact hgz z hz
        have hstep2 : Real.circleAverage (fun z => poissonKernel c w z * (ε/2) + 16*R*M*δ/δ₁^2) c R
            = ε/2 + 16*R*M*δ/δ₁^2 := by
          have hCI3 : CircleIntegrable (fun z => poissonKernel c w z * (ε/2)) c R :=
            ContinuousOn.circleIntegrable hR.le (hpoisCI.mul continuousOn_const)
          rw [Real.circleAverage_fun_add hCI3 (circleIntegrable_const (16*R*M*δ/δ₁^2) c R)]
          rw [Real.circleAverage_const]
          congr 1
          rw [show (fun z => poissonKernel c w z * (ε/2)) = (ε/2) • poissonKernel c w from by
            ext z; simp [mul_comm]]
          rw [Real.circleAverage_smul, hpoisson_one w hw']
          ring
        have hδbound : 16*R*M*δ/δ₁^2 < ε/2 := by
          have h1 : δ ≤ ε*δ₁^2/(64*(R*M+1)) :=
            (min_le_right _ _).trans (min_le_right _ _)
          have hδ₁sqpos : (0:ℝ) < δ₁^2 := by positivity
          have hRM1pos : (0:ℝ) < 64*(R*M+1) := by positivity
          have h1' : δ * (64*(R*M+1)) ≤ ε*δ₁^2 := (le_div_iff₀ hRM1pos).mp h1
          rw [div_lt_iff₀ hδ₁sqpos]
          nlinarith [h1', mul_nonneg (mul_nonneg hR.le hM0) hδpos.le, hδpos]
        linarith [hstep1, hstep2, hδbound]
      · -- boundary case: w itself is on the sphere
        push Not at hwmem
        have hweq : ‖w-c‖ = R := le_antisymm hwcb hwmem
        have hwsph' : w ∈ sphere c R := by rw [mem_sphere, Complex.dist_eq]; exact hweq
        have hu_w : u w = g w := by
          rw [hu_def]; simp only; rw [ite_eq_right (by linarith [hweq])]
        rw [hu_w]
        have hcl : dist w ζ₀ < δ₁ := by
          rw [dist_eq_norm]
          calc ‖w - ζ₀‖ < δ := hwdist
            _ ≤ δ₁/2 := by rw [hδ_def]; exact min_le_left _ _
            _ < δ₁ := by linarith
        have := hδ₁ hwsph' hcl
        rw [Real.dist_eq] at this
        linarith [this]
  · intro z hz
    rw [hu_def]
    simp only
    rw [ite_eq_right]
    rw [mem_sphere, Complex.dist_eq] at hz
    rw [hz]; exact lt_irrefl R

end LiZhongQC
