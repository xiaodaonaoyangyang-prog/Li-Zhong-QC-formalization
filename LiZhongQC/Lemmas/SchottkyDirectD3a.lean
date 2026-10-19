import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeTeichData

/-!
# thm32_2 direct route, D3a (R82, `SchottkyDirectD3a`)

`s82dx_integrable_admissible`: an area-integrable holomorphic quadratic differential on a finite-type
surface `S₀ = ℍ/Γ₀` of type `(g, n, 0)` is admissible.  Analytic core (sub-mean-value, tail decay, region
transfer through the fundamental domain, simple-pole lemma) plus the chart geometry that produces the
`hpole` hypothesis of `s82dx_extend_qd`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

/-- Sub-mean-value on a circle: `2π ‖f c‖ ≤ ∫_{-π}^{π} ‖f (c + r e^{iθ})‖ dθ`. -/
theorem s82dx_circle_norm {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball c r)) :
    2 * Real.pi * ‖f c‖ ≤ ∫ θ in (-Real.pi)..Real.pi, ‖f (circleMap c r θ)‖ := by
  have hf' : DiffContOnCl ℂ f (ball c |r|) := by rwa [abs_of_pos hr]
  have h1 := hf'.circleAverage
  rw [Real.circleAverage_def] at h1
  have h2 : ‖f c‖ * (2 * Real.pi) ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap c r θ)‖ := by
    have h3 : ‖∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap c r θ)‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap c r θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by positivity)
    have h4 : ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap c r θ) = (2 * Real.pi : ℝ) • f c := by
      have := congrArg (fun x => (2 * Real.pi : ℝ) • x) h1
      simp only [smul_smul] at this
      have h5 : (2 * Real.pi : ℝ) * (2 * Real.pi)⁻¹ = 1 := by
        field_simp
      rw [h5, one_smul] at this
      exact this
    rw [h4, norm_smul, Real.norm_of_nonneg (by positivity)] at h3
    linarith
  have hper : Function.Periodic (fun θ => ‖f (circleMap c r θ)‖) (2 * Real.pi) :=
    fun x => by simp [periodic_circleMap c r x]
  have h6 := hper.intervalIntegral_add_eq (-Real.pi) 0
  have h7 : (-Real.pi + 2 * Real.pi) = Real.pi := by ring
  rw [h7, zero_add] at h6
  rw [h6]
  linarith

/-- **Area sub-mean-value**: `π r² ‖f c‖ ≤ ∬_{B(c,r)} ‖f‖` for `f` holomorphic on the disc. -/
theorem s82dx_submean {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball c r)) :
    ENNReal.ofReal (Real.pi * r ^ 2 * ‖f c‖) ≤ ∫⁻ z in ball c r, ENNReal.ofReal ‖f z‖ := by
  classical
  have hcont : ContinuousOn f (ball c r) := hf.continuousOn.mono subset_closure
  set u : ℂ → ℂ := (ball c r).piecewise f 0 with hu
  have hum : Measurable u :=
    ContinuousOn.measurable_piecewise hcont continuousOn_const measurableSet_ball
  have huf : ∀ z ∈ ball c r, u z = f z := fun z hz => by simp [hu, hz]
  have hu0 : ∀ z ∉ ball c r, u z = 0 := fun z hz => by simp [hu, hz]
  have h1 : ∫⁻ z in ball c r, ENNReal.ofReal ‖f z‖ = ∫⁻ z, ENNReal.ofReal ‖u (c + z)‖ := by
    have e1 : ∫⁻ z in ball c r, ENNReal.ofReal ‖f z‖ = ∫⁻ z in ball c r, ENNReal.ofReal ‖u z‖ :=
      setLIntegral_congr_fun measurableSet_ball fun z hz => by rw [huf z hz]
    have e2 : ∫⁻ z in ball c r, ENNReal.ofReal ‖u z‖ = ∫⁻ z, ENNReal.ofReal ‖u z‖ := by
      apply setLIntegral_eq_of_support_subset
      intro z hz
      by_contra hzb
      apply hz
      simp [hu0 z hzb]
    rw [e1, e2, lintegral_add_left_eq_self (fun z => ENNReal.ofReal ‖u z‖) c]
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm]
  have hcm : ∀ p : ℝ × ℝ, c + (Complex.polarCoord.symm p : ℂ) = circleMap c p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    push_cast
    ring
  simp only [hcm, smul_eq_mul]
  have hc : Continuous fun p : ℝ × ℝ => circleMap c p.1 p.2 := by
    unfold circleMap
    fun_prop
  have hF : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * ENNReal.ofReal ‖u (circleMap c p.1 p.2)‖ :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp ((hum.comp hc.measurable).norm))
  have hsub : Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono Set.Ioo_subset_Ioi_self le_rfl
  have hρ : ∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal ρ = ENNReal.ofReal (r ^ 2 / 2) := by
    have h := ofReal_integral_eq_lintegral_ofReal (f := fun x : ℝ => x)
      (μ := volume.restrict (Ioo (0 : ℝ) r))
      ((continuous_id.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => hx.1.le))
    rw [← h]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    simp
  have hin : ∀ ρ ∈ Ioo (0 : ℝ) r,
      ENNReal.ofReal (2 * Real.pi * ‖f c‖) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal ‖u (circleMap c ρ θ)‖ := by
    intro ρ hρ'
    have hfρ : DiffContOnCl ℂ f (ball c ρ) :=
      ⟨hf.1.mono (ball_subset_ball hρ'.2.le), hf.2.mono (closure_mono (ball_subset_ball hρ'.2.le))⟩
    have hcirc : ∀ θ, u (circleMap c ρ θ) = f (circleMap c ρ θ) := fun θ =>
      huf _ (by
        rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ'.1]
        exact hρ'.2)
    simp only [hcirc]
    have hcl : ∀ θ, circleMap c ρ θ ∈ closure (ball c r) := fun θ =>
      subset_closure (by
        rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ'.1]
        exact hρ'.2)
    have hint : IntervalIntegrable (fun θ => ‖f (circleMap c ρ θ)‖) volume (-Real.pi) Real.pi :=
      (((hf.continuousOn.comp (continuous_circleMap c ρ).continuousOn
        (fun θ _ => hcl θ)).norm).intervalIntegrable)
    have h2 := s82dx_circle_norm hρ'.1 hfρ
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-Real.pi) Real.pi)]
        fun θ => ‖f (circleMap c ρ θ)‖ := ae_of_all _ fun θ => norm_nonneg _
    have hig : Integrable (fun θ => ‖f (circleMap c ρ θ)‖) (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
      have := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).1 hint
      exact this
    rw [← ofReal_integral_eq_lintegral_ofReal hig hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact h2
  calc ENNReal.ofReal (Real.pi * r ^ 2 * ‖f c‖)
      = ∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal ρ * ENNReal.ofReal (2 * Real.pi * ‖f c‖) := by
        rw [lintegral_mul_const _ ENNReal.measurable_ofReal, hρ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ∫⁻ ρ in Ioo (0 : ℝ) r, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ * ENNReal.ofReal ‖u (circleMap c ρ θ)‖ := by
        refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ' => ?_
        have hm : Measurable fun θ => ENNReal.ofReal ‖u (circleMap c ρ θ)‖ :=
          ENNReal.measurable_ofReal.comp ((hum.comp (continuous_circleMap c ρ).measurable).norm)
        rw [lintegral_const_mul _ hm]
        exact mul_le_mul_right (hin ρ hρ') _
    _ = ∫⁻ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * ENNReal.ofReal ‖u (circleMap c p.1 p.2)‖ := by
        rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hF.aemeasurable]
    _ ≤ _ := lintegral_mono_set hsub


/-- Local tail bound: a holomorphic function on a punctured disc whose integral over the ball
`B(w, ‖w‖/2)` is at most `E` satisfies `π (‖w‖/2)² ‖q w‖ ≤ E`. -/
theorem s82dx_decay_bound {q : ℂ → ℂ} {R : ℝ}
    (hq : DifferentiableOn ℂ q (ball (0 : ℂ) R \ {0})) {w : ℂ} (hw0 : w ≠ 0)
    (hwR : 3 / 2 * ‖w‖ < R) {E : ENNReal}
    (hE : ∫⁻ z in ball w (‖w‖ / 2), ENNReal.ofReal ‖q z‖ ≤ E) :
    ENNReal.ofReal (Real.pi * (‖w‖ / 2) ^ 2 * ‖q w‖) ≤ E := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hsub : closedBall w (‖w‖ / 2) ⊆ ball (0 : ℂ) R \ {0} := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
      have := norm_add_le (z - w) w
      simpa [add_comm] using this
    have h2 : ‖w‖ - ‖z - w‖ ≤ ‖z‖ := by
      have := norm_sub_norm_le w (w - z)
      rw [sub_sub_cancel, norm_sub_rev w z] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]; linarith
    · intro h0
      have h00 : z = 0 := h0
      rw [h00, zero_sub, norm_neg] at hz
      linarith
  have hdc : DiffContOnCl ℂ q (ball w (‖w‖ / 2)) := by
    refine ⟨(hq.mono ((ball_subset_closedBall).trans hsub)), ?_⟩
    exact (hq.continuousOn.mono hsub).mono (closure_ball_subset_closedBall)
  exact (s82dx_submean (by positivity) hdc).trans hE


/-- A holomorphic function on a punctured disc with `|w|² |g w| → 0` has at most a simple pole:
`g w = a / w + h w` with `h` holomorphic on the full disc. -/
theorem s82dx_simple_pole {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) R \ {0}))
    (hdec : Filter.Tendsto (fun w : ℂ => ‖w‖ ^ 2 * ‖g w‖) (𝓝[≠] 0) (𝓝 0)) :
    ∃ (a : ℂ) (h : ℂ → ℂ), DifferentiableOn ℂ h (ball (0 : ℂ) R) ∧
      ∀ w ∈ ball (0 : ℂ) R \ {0}, g w = a / w + h w := by
  classical
  by_cases hR : 0 < R
  swap
  · refine ⟨0, 0, differentiableOn_const _, ?_⟩
    intro w hw
    exfalso
    have := hw.1
    rw [mem_ball, dist_zero_right] at this
    linarith [norm_nonneg w]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  set k : ℂ → ℂ := fun w => if w = 0 then 0 else w ^ 2 * g w with hk
  have hkeq : ∀ w, w ≠ 0 → k w = w ^ 2 * g w := fun w hw => by simp [hk, hw]
  have hk0 : k 0 = 0 := by simp [hk]
  have hopen : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hdiffoff : ∀ w ∈ ball (0 : ℂ) R \ {0}, DifferentiableAt ℂ k w := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have hev : k =ᶠ[𝓝 w] fun w => w ^ 2 * g w := by
      filter_upwards [isOpen_ne.mem_nhds hw0] with v hv using hkeq v hv
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact (differentiableAt_id.pow 2).mul (hg.differentiableAt (hopen.mem_nhds hw))
  have hcont0 : ContinuousAt k 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hk0, tendsto_zero_iff_norm_tendsto_zero]
    refine hdec.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hkeq w hw, norm_mul, norm_pow]
  have hpunct : ∀ᶠ w in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ k w := by
    have : ball (0 : ℂ) R \ {0} ∈ 𝓝[≠] (0 : ℂ) := by
      rw [mem_nhdsWithin]
      exact ⟨ball 0 R, isOpen_ball, h0, fun w hw => ⟨hw.1, hw.2⟩⟩
    filter_upwards [this] with w hw using hdiffoff w hw
  have han0 : AnalyticAt ℂ k 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct hcont0
  have hkd : DifferentiableOn ℂ k (ball (0 : ℂ) R) := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]; exact han0.differentiableAt.differentiableWithinAt
    · exact (hdiffoff w ⟨hw, hw0⟩).differentiableWithinAt
  have hH : DifferentiableOn ℂ (dslope k 0) (ball (0 : ℂ) R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h0)).2 hkd
  have hH2 : DifferentiableOn ℂ (dslope (dslope k 0) 0) (ball (0 : ℂ) R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h0)).2 hH
  refine ⟨dslope k 0 0, dslope (dslope k 0) 0, hH2, ?_⟩
  intro w hw
  have hw0 : w ≠ 0 := hw.2
  have e1 : dslope k 0 w = k w / w := by
    rw [dslope_of_ne _ hw0, slope_def_field, hk0, sub_zero, sub_zero]
  have e2 : dslope (dslope k 0) 0 w = (dslope k 0 w - dslope k 0 0) / w := by
    rw [dslope_of_ne _ hw0, slope_def_field, sub_zero]
  rw [e2, e1]
  have : g w = k w / w / w := by
    rw [hkeq w hw0]; field_simp
  rw [this]
  field_simp
  ring


/-- Counting: if `R ⊆ ℍ` injects modulo `Γ`, a point has at most `|Γ ∩ {±1}|` translates in `R`. -/
theorem s82dx_count {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfree : ActsFreely Γ)
    {R : Set ℂ}
    (hRinj : ∀ a b : UpperHalfPlane, (a : ℂ) ∈ R → (b : ℂ) ∈ R → (∃ γ ∈ Γ, γ • a = b) → a = b)
    (τ : UpperHalfPlane) :
    ∑' γ : Γ, {γ : Γ | ((γ.1 • τ : UpperHalfPlane) : ℂ) ∈ R}.indicator (fun _ => (1 : ENNReal)) γ ≤
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) := by
  classical
  set S : Set Γ := {γ : Γ | ((γ.1 • τ : UpperHalfPlane) : ℂ) ∈ R} with hS
  rw [← tsum_subtype S (fun _ => (1 : ENNReal)), ENNReal.tsum_set_one]
  rcases S.eq_empty_or_nonempty with h | ⟨γ1, hγ1⟩
  · rw [h]; simp
  set K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) := Γ ⊓ Subgroup.zpowers (-1) with hK
  have hKfin : Finite K := by
    have h1 : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : Γ ⊓ Subgroup.zpowers (-1) ≤ Subgroup.zpowers (-1)))
  let f : Γ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun γ => (γ1.1)⁻¹ * γ.1
  have hmaps : Set.MapsTo f S (K : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
    intro γ2 hγ2
    refine ⟨Γ.mul_mem (Γ.inv_mem γ1.2) γ2.2, ?_⟩
    have hEq : γ1.1 • τ = γ2.1 • τ := by
      refine hRinj _ _ hγ1 hγ2 ⟨γ2.1 * (γ1.1)⁻¹, Γ.mul_mem γ2.2 (Γ.inv_mem γ1.2), ?_⟩
      rw [mul_smul, inv_smul_smul]
    have hfix : ((γ1.1)⁻¹ * γ2.1) • τ = τ := by
      rw [mul_smul, ← hEq, inv_smul_smul]
    rcases hfree _ (Γ.mul_mem (Γ.inv_mem γ1.2) γ2.2) τ hfix with h | h
    · show (γ1.1)⁻¹ * γ2.1 ∈ Subgroup.zpowers (-1)
      rw [h]; exact one_mem _
    · show (γ1.1)⁻¹ * γ2.1 ∈ Subgroup.zpowers (-1)
      rw [h]; exact Subgroup.mem_zpowers _
  have hinj : Set.InjOn f S := by
    intro a _ b _ hab
    exact Subtype.ext (mul_left_cancel hab)
  have hle : S.encard ≤ (Nat.card K : ENat) := by
   calc S.encard ≤ (K : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).encard :=
         Set.encard_le_encard_of_injOn hmaps hinj
     _ = (Nat.card K : ENat) := by
         rw [← ENat.card_coe_set_eq, ENat.card_eq_coe_natCard]
         rfl
  have := ENat.toENNReal_le.2 hle
  simpa using this


/-- **Region transfer**: if `R ⊆ ℍ` injects modulo `Γ` and all `Γ`-translates of points of `R`... lie
in a set `T` whenever they hit `R`, then `∬_R |φ| ≤ m ∬_{F ∩ T} |φ|` with `m = |Γ ∩ {±1}|`. -/
theorem s82dx_transfer {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {R T : Set ℂ} (hRm : MeasurableSet R)
    (hTm : MeasurableSet T) (hRH : R ⊆ upperHalf)
    (hRinj : ∀ a b : UpperHalfPlane, (a : ℂ) ∈ R → (b : ℂ) ∈ R → (∃ γ ∈ Γ, γ • a = b) → a = b)
    (hT : ∀ (τ : UpperHalfPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ ∈ Γ →
      ((γ • τ : UpperHalfPlane) : ℂ) ∈ R → (τ : ℂ) ∈ T) :
    phiArea φ R ≤ (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) * phiArea φ (F ∩ T) := by
  classical
  obtain ⟨hFH, hFm, hcov, -, -⟩ := hF
  haveI : Countable Γ := (h36p_countable hΓ).to_subtype
  set g : ℂ → ENNReal := fun u => ENNReal.ofReal ‖φ u‖ with hg
  have hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ), w ∈ upperHalf →
      h36p_m γ⁻¹ (h36p_m γ w) = w := by
    intro γ w hw
    have h1 := h36p_m_coe γ ⟨w, hw⟩
    simp only at h1
    rw [h1, h36p_m_coe γ⁻¹ (γ • ⟨w, hw⟩), inv_smul_smul]
  have hcover : R ⊆ ⋃ γ : Γ, (R ∩ h36p_m γ.1 ⁻¹' F) := by
    intro w hw
    obtain ⟨γ, hγ, hγF⟩ := hcov ⟨w, hRH hw⟩
    refine mem_iUnion.2 ⟨⟨γ, hγ⟩, hw, ?_⟩
    show h36p_m γ w ∈ F
    have := h36p_m_coe γ ⟨w, hRH hw⟩
    simp only at this
    rw [this]
    exact hγF
  have hstep : ∀ γ : Γ, ∫⁻ w in R ∩ h36p_m γ.1 ⁻¹' F, g w ≤
      ∫⁻ u in F ∩ T, (h36p_m γ.1⁻¹ ⁻¹' R).indicator g u := by
    intro γ
    have hE : MeasurableSet (R ∩ h36p_m γ.1 ⁻¹' F) := hRm.inter (h36p_m_measurable _ hFm)
    rw [← h36p_lintegral_image_m hφ γ.2 hE (inter_subset_left.trans hRH),
      setLIntegral_indicator (h36p_m_measurable _ hRm)]
    refine lintegral_mono_set ?_
    rintro _ ⟨w, ⟨hwR, hwF⟩, rfl⟩
    have hwH := hRH hwR
    have hback : h36p_m γ.1⁻¹ (h36p_m γ.1 w) = w := hinv _ _ hwH
    refine ⟨by simpa [hback] using hwR, hwF, ?_⟩
    have hmH : h36p_m γ.1 w ∈ upperHalf := h36p_m_mem _ hwH
    refine hT ⟨h36p_m γ.1 w, hmH⟩ γ.1⁻¹ (Γ.inv_mem γ.2) ?_
    have := h36p_m_coe γ.1⁻¹ ⟨h36p_m γ.1 w, hmH⟩
    simp only at this
    rw [← this, hback]
    exact hwR
  have hAE : ∀ γ : Γ, AEMeasurable ((h36p_m γ.1⁻¹ ⁻¹' R).indicator g)
      (volume.restrict (F ∩ T)) := fun γ => by
    refine AEMeasurable.indicator ?_ (h36p_m_measurable _ hRm)
    exact ((hφ.1.continuousOn.mono (inter_subset_left.trans hFH)).aestronglyMeasurable
      (hFm.inter hTm)).aemeasurable.norm.ennreal_ofReal
  have hpt : ∀ u ∈ F ∩ T, ∑' γ : Γ, (h36p_m γ.1⁻¹ ⁻¹' R).indicator g u ≤
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) * g u := by
    intro u hu
    have huH : u ∈ upperHalf := hFH hu.1
    have h1 : ∑' γ : Γ, (h36p_m γ.1⁻¹ ⁻¹' R).indicator g u =
        ∑' γ : Γ, (h36p_m γ.1 ⁻¹' R).indicator g u :=
      (Equiv.inv Γ).tsum_eq (fun γ : Γ => (h36p_m γ.1 ⁻¹' R).indicator g u)
    have h2 : ∀ γ : Γ, (h36p_m γ.1 ⁻¹' R).indicator g u =
        {γ : Γ | ((γ.1 • (⟨u, huH⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ R}.indicator
          (fun _ => (1 : ENNReal)) γ * g u := by
      intro γ
      have hm := h36p_m_coe γ.1 ⟨u, huH⟩
      simp only at hm
      by_cases h : ((γ.1 • (⟨u, huH⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ R
      · rw [indicator_of_mem (show γ ∈ _ from h), indicator_of_mem
          (show u ∈ h36p_m γ.1 ⁻¹' R by show h36p_m γ.1 u ∈ R; rw [hm]; exact h)]
        simp
      · rw [indicator_of_notMem (show γ ∉ {γ : Γ | ((γ.1 • (⟨u, huH⟩ : UpperHalfPlane) :
            UpperHalfPlane) : ℂ) ∈ R} from h), indicator_of_notMem
          (show u ∉ h36p_m γ.1 ⁻¹' R by show h36p_m γ.1 u ∉ R; rw [hm]; exact h)]
        simp
    rw [h1, tsum_congr h2, ENNReal.tsum_mul_right]
    exact mul_le_mul_left (s82dx_count hfree hRinj ⟨u, huH⟩) _
  calc phiArea φ R = ∫⁻ w in R, g w := rfl
    _ ≤ ∫⁻ w in ⋃ γ : Γ, (R ∩ h36p_m γ.1 ⁻¹' F), g w := lintegral_mono_set hcover
    _ ≤ ∑' γ : Γ, ∫⁻ w in R ∩ h36p_m γ.1 ⁻¹' F, g w := lintegral_iUnion_le _ _
    _ ≤ ∑' γ : Γ, ∫⁻ u in F ∩ T, (h36p_m γ.1⁻¹ ⁻¹' R).indicator g u :=
        ENNReal.tsum_le_tsum hstep
    _ = ∫⁻ u in F ∩ T, ∑' γ : Γ, (h36p_m γ.1⁻¹ ⁻¹' R).indicator g u :=
        (lintegral_tsum hAE).symm
    _ ≤ ∫⁻ u in F ∩ T, (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) * g u :=
        setLIntegral_mono' (hFm.inter hTm) hpt
    _ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) * phiArea φ (F ∩ T) :=
        lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)


/-- Local inverse function theorem, packaged: near a point where `Z` is analytic with `Z' ≠ 0`
there is an open neighbourhood on which `Z` is injective and has open image. -/
theorem s82dx_local_inj {Ω : Set ℂ} {Z : ℂ → ℂ} (hΩ : IsOpen Ω) (hZ : DifferentiableOn ℂ Z Ω)
    (hZ' : ∀ τ ∈ Ω, deriv Z τ ≠ 0) {τ : ℂ} (hτ : τ ∈ Ω) :
    ∃ O : Set ℂ, IsOpen O ∧ τ ∈ O ∧ O ⊆ Ω ∧ Set.InjOn Z O ∧ IsOpen (Z '' O) := by
  have hA : AnalyticAt ℂ Z τ := hZ.analyticAt (hΩ.mem_nhds hτ)
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ (hZ' τ hτ))
  have hfd : HasStrictFDerivAt Z i.toContinuousLinearMap τ := hA.hasStrictDerivAt
  let e : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph _
  have hx : τ ∈ e.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hec : ∀ w, e w = Z w := fun w => rfl
  refine ⟨e.source ∩ Ω, e.open_source.inter hΩ, ⟨hx, hτ⟩, inter_subset_right, ?_, ?_⟩
  · intro a ha b hb hab
    exact e.injOn ha.1 hb.1 (by rw [hec, hec]; exact hab)
  · have := e.isOpen_image_of_subset_source (e.open_source.inter hΩ) inter_subset_left
    have heq : e '' (e.source ∩ Ω) = Z '' (e.source ∩ Ω) := by
      ext y; simp [hec]
    rwa [heq] at this

/-- **Measurable sheets**: an open set `B` inside `Z(Ω)` is the bijective image of a measurable
`R ⊆ Ω` on which `Z` is injective. -/
theorem s82dx_selector {Ω B : Set ℂ} {Z : ℂ → ℂ} (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hZ : DifferentiableOn ℂ Z Ω) (hZ' : ∀ τ ∈ Ω, deriv Z τ ≠ 0) (hBsub : B ⊆ Z '' Ω) :
    ∃ R : Set ℂ, R ⊆ Ω ∧ MeasurableSet R ∧ Set.InjOn Z R ∧ Z '' R = B := by
  classical
  choose! O hO using fun τ : ℂ => (fun hτ : τ ∈ Ω => s82dx_local_inj hΩ hZ hZ' hτ)
  rcases Ω.eq_empty_or_nonempty with hempty | ⟨τ₀, hτ₀⟩
  · subst hempty
    have : B = ∅ := by simpa using hBsub
    exact ⟨∅, by simp, MeasurableSet.empty, Set.injOn_empty _, by simp [this]⟩
  have hnhds : ∀ τ ∈ Ω, O τ ∈ 𝓝[Ω] τ := fun τ hτ =>
    mem_nhdsWithin_of_mem_nhds ((hO τ hτ).1.mem_nhds (hO τ hτ).2.1)
  obtain ⟨T, hTsub, hTc, hcov⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin (s := Ω) (f := fun τ => O τ) hnhds
  have hTne : T.Nonempty := by
    obtain ⟨τ, hτ, -⟩ := Set.mem_iUnion₂.1 (hcov hτ₀)
    exact ⟨τ, hτ⟩
  obtain ⟨u, hu⟩ := hTc.exists_eq_range hTne
  set P : ℕ → Set ℂ := fun k => O (u k) with hP
  have hPo : ∀ k, IsOpen (P k) := fun k => (hO (u k) (hTsub (hu ▸ ⟨k, rfl⟩))).1
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => (hO (u k) (hTsub (hu ▸ ⟨k, rfl⟩))).2.2.1
  have hPinj : ∀ k, Set.InjOn Z (P k) := fun k => (hO (u k) (hTsub (hu ▸ ⟨k, rfl⟩))).2.2.2.1
  have hPim : ∀ k, IsOpen (Z '' P k) := fun k => (hO (u k) (hTsub (hu ▸ ⟨k, rfl⟩))).2.2.2.2
  have hPcov : Ω ⊆ ⋃ k, P k := by
    intro τ hτ
    obtain ⟨σ, hσ, hτσ⟩ := Set.mem_iUnion₂.1 (hcov hτ)
    rw [hu] at hσ
    obtain ⟨k, rfl⟩ := hσ
    exact Set.mem_iUnion.2 ⟨k, hτσ⟩
  have hZcont : ContinuousOn Z Ω := hZ.continuousOn
  -- the sets `Ω ∩ Z⁻¹(Z(P j))` are open
  have hbad : ∀ j, IsOpen (Ω ∩ Z ⁻¹' (Z '' P j)) := fun j =>
    hZcont.isOpen_inter_preimage hΩ (hPim j)
  set Rk : ℕ → Set ℂ := fun k =>
    (P k ∩ Z ⁻¹' B) \ ⋃ j ∈ Finset.range k, (Ω ∩ Z ⁻¹' (Z '' P j)) with hRk
  have hRko : ∀ k, IsOpen (P k ∩ Z ⁻¹' B) := fun k =>
    (hZcont.mono (hPΩ k)).isOpen_inter_preimage (hPo k) hB
  have hRkm : ∀ k, MeasurableSet (Rk k) := fun k =>
    (hRko k).measurableSet.diff
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hbad j).measurableSet
  refine ⟨⋃ k, Rk k, ?_, MeasurableSet.iUnion hRkm, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
    exact hPΩ k hk.1.1
  · intro a ha b hb hab
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hb
    rcases lt_trichotomy i k with hik | hik | hik
    · exfalso
      apply hk.2
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hik, hPΩ k hk.1.1, ?_⟩
      exact ⟨a, hi.1.1, hab⟩
    · subst hik
      exact hPinj i hi.1.1 hk.1.1 hab
    · exfalso
      apply hi.2
      refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hik, hPΩ i hi.1.1, ?_⟩
      exact ⟨b, hk.1.1, hab.symm⟩
  · ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
      exact hk.1.2
    · intro hy
      obtain ⟨τ, hτ, rfl⟩ := hBsub hy
      obtain ⟨k0, hk0⟩ := Set.mem_iUnion.1 (hPcov hτ)
      have hex : ∃ k, Z τ ∈ Z '' P k := ⟨k0, τ, hk0, rfl⟩
      obtain ⟨a, haP, haZ⟩ := Nat.find_spec hex
      refine ⟨a, Set.mem_iUnion.2 ⟨Nat.find hex, ⟨haP, ?_⟩, ?_⟩, haZ⟩
      · rw [Set.mem_preimage, haZ]; exact hy
      · intro hbad'
        obtain ⟨j, hj, hjm⟩ := Set.mem_iUnion₂.1 hbad'
        have := Nat.find_min hex (Finset.mem_range.1 hj)
        apply this
        rw [← haZ]
        exact hjm.2


/-- Change of variables for a holomorphic map `Z` on a measurable set `R` where it is injective. -/
theorem s82dx_cov {Ω R : Set ℂ} {Z : ℂ → ℂ} (hΩ : IsOpen Ω) (hZ : DifferentiableOn ℂ Z Ω)
    (hRm : MeasurableSet R) (hRΩ : R ⊆ Ω) (hinj : Set.InjOn Z R) (f : ℂ → ENNReal) :
    ∫⁻ z in Z '' R, f z = ∫⁻ τ in R, f (Z τ) * ENNReal.ofReal (‖deriv Z τ‖ ^ 2) := by
  have hd : ∀ τ ∈ R, HasDerivAt Z (deriv Z τ) τ := fun τ hτ =>
    (hZ.differentiableAt (hΩ.mem_nhds (hRΩ hτ))).hasDerivAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hRm
    (fun τ hτ => ((hd τ hτ).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hRm fun τ hτ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), mul_comm]


/-- **Tails of an integrable function vanish**: for a decreasing sequence of measurable sets whose
intersection misses `F`, `∬_{F ∩ A_k} |φ| → 0`. -/
theorem s82dx_tail {F : Set ℂ} {φ : ℂ → ℂ} (hfin : phiArea φ F < ⊤)
    {A : ℕ → Set ℂ} (hAm : ∀ k, MeasurableSet (A k)) (hAnti : Antitone A)
    (hempty : ∀ z ∈ F, ∃ k, z ∉ A k) :
    Filter.Tendsto (fun k => phiArea φ (F ∩ A k)) Filter.atTop (𝓝 0) := by
  set μ : Measure ℂ := (volume.restrict F).withDensity (fun u => ENNReal.ofReal ‖φ u‖) with hμ
  have hμA : ∀ k, μ (A k) = phiArea φ (F ∩ A k) := fun k => by
    rw [hμ, withDensity_apply _ (hAm k), Measure.restrict_restrict (hAm k), inter_comm]
    rfl
  have hμu : μ univ = phiArea φ F := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := A)
    (fun k => (hAm k).nullMeasurableSet) hAnti
    ⟨0, ne_top_of_le_ne_top (hμu ▸ hfin.ne) (measure_mono (subset_univ _))⟩
  have hint : μ (⋂ k, A k) = 0 := by
    have hm : MeasurableSet (⋂ k, A k) := MeasurableSet.iInter hAm
    have hE : (⋂ k, A k) ∩ F = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_iInter, mem_empty_iff_false, iff_false, not_and]
      intro hz hzF
      obtain ⟨k, hk⟩ := hempty z hzF
      exact hk (hz k)
    rw [hμ, withDensity_apply _ hm, Measure.restrict_restrict hm, hE]
    simp
  rw [hint] at h
  refine h.congr fun k => ?_
  simp [hμA]


/-- **Local `L¹` bound near the puncture**: with `Z` a `Γ`-invariant local biholomorphism on `Ω ⊆ ℍ`
and `E` the local expression of `φ` (`E (Z τ) Z'(τ)² = φ τ`), the integral of `|E|` over a disc
inside `Z(Ω) ∩ B(0, δ)` is at most `m ∬_{F ∩ Z⁻¹B(0,δ)} |φ|`. -/
theorem s82dx_disc_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩH : Ω ⊆ upperHalf)
    {Z E : ℂ → ℂ} {ε₀ : ℝ} (hZ : DifferentiableOn ℂ Z Ω) (hZ' : ∀ τ ∈ Ω, deriv Z τ ≠ 0)
    (hinv : ∀ τ ∈ Ω, ∀ γ ∈ Γ, h36p_m γ τ ∈ Ω ∧ Z (h36p_m γ τ) = Z τ)
    (hrel : ∀ τ ∈ Ω, Z τ ∈ ball (0 : ℂ) ε₀ → E (Z τ) * deriv Z τ ^ 2 = φ τ)
    {B : Set ℂ} (hB : IsOpen B) (hBsub : B ⊆ Z '' Ω) (hBε : B ⊆ ball (0 : ℂ) ε₀) {δ : ℝ}
    (hBδ : B ⊆ ball (0 : ℂ) δ) :
    ∫⁻ z in B, ENNReal.ofReal ‖E z‖ ≤
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ENNReal) *
        phiArea φ (F ∩ {τ | τ ∈ Ω ∧ Z τ ∈ ball (0 : ℂ) δ}) := by
  classical
  obtain ⟨R, hRΩ, hRm, hRinj, hRB⟩ := s82dx_selector hΩo hB hZ hZ' hBsub
  have hcov := s82dx_cov hΩo hZ hRm hRΩ hRinj (fun z => ENNReal.ofReal ‖E z‖)
  rw [hRB] at hcov
  have hphi : ∫⁻ τ in R, ENNReal.ofReal ‖E (Z τ)‖ * ENNReal.ofReal (‖deriv Z τ‖ ^ 2) =
      phiArea φ R := by
    refine setLIntegral_congr_fun hRm fun τ hτ => ?_
    have hZB : Z τ ∈ B := by rw [← hRB]; exact ⟨τ, hτ, rfl⟩
    have := hrel τ (hRΩ hτ) (hBε hZB)
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← norm_pow, ← norm_mul, this]
  rw [hcov, hphi]
  have hTm : MeasurableSet {τ | τ ∈ Ω ∧ Z τ ∈ ball (0 : ℂ) δ} := by
    have := hZ.continuousOn.isOpen_inter_preimage hΩo isOpen_ball (t := ball (0 : ℂ) δ)
    exact this.measurableSet
  refine s82dx_transfer hΓ hfree hF hφ hRm hTm (hRΩ.trans hΩH) ?_ ?_
  · intro a b ha hb ⟨γ, hγ, hab⟩
    have hm := h36p_m_coe γ a
    have hbm : h36p_m γ (a : ℂ) = (b : ℂ) := by
      rw [hm]; simp [hab]
    have h1 := (hinv (a : ℂ) (hRΩ ha) γ hγ).2
    rw [hbm] at h1
    exact UpperHalfPlane.ext (hRinj ha hb h1.symm)
  · intro τ γ hγ hτR
    have h1 := hinv _ (hRΩ hτR) γ⁻¹ (Γ.inv_mem hγ)
    have h2 : h36p_m γ⁻¹ ((γ • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) := by
      rw [h36p_m_coe, inv_smul_smul]
    rw [h2] at h1
    refine ⟨h1.1, ?_⟩
    rw [h1.2]
    exact hBδ (by rw [← hRB]; exact ⟨_, hτR, rfl⟩)


/-- **Pole analysis** (normalised at `0`): `E` has at most a simple pole at `0`. -/
theorem s82dx_pole_analysis {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩH : Ω ⊆ upperHalf) {Z E : ℂ → ℂ} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hZ : DifferentiableOn ℂ Z Ω) (hZ' : ∀ τ ∈ Ω, deriv Z τ ≠ 0)
    (hinv : ∀ τ ∈ Ω, ∀ γ ∈ Γ, h36p_m γ τ ∈ Ω ∧ Z (h36p_m γ τ) = Z τ)
    (hsurj : ∀ z ∈ ball (0 : ℂ) ε₀, z ≠ 0 → z ∈ Z '' Ω) (hne : ∀ τ ∈ Ω, Z τ ≠ 0)
    (hE : DifferentiableOn ℂ E (ball (0 : ℂ) ε₀ \ {0}))
    (hrel : ∀ τ ∈ Ω, Z τ ∈ ball (0 : ℂ) ε₀ → E (Z τ) * deriv Z τ ^ 2 = φ τ) :
    ∃ (a : ℂ) (h : ℂ → ℂ), DifferentiableOn ℂ h (ball (0 : ℂ) ε₀) ∧
      ∀ z ∈ ball (0 : ℂ) ε₀ \ {0}, E z = a / z + h z := by
  classical
  refine s82dx_simple_pole hE ?_
  set M : ℕ := Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) with hM
  have hMpos : 0 < M := by
    haveI : Finite ↥(Γ ⊓ Subgroup.zpowers (-1)) := by
      have h1 : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
        finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
      exact Finite.of_injective _ (Subgroup.inclusion_injective
        (inf_le_right : Γ ⊓ Subgroup.zpowers (-1) ≤ Subgroup.zpowers (-1)))
    exact Nat.card_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  set A : ℕ → Set ℂ := fun k => {τ | τ ∈ Ω ∧ Z τ ∈ ball (0 : ℂ) (ε₀ / ((k : ℝ) + 1))} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (hZ.continuousOn.isOpen_inter_preimage hΩo isOpen_ball
      (t := ball (0 : ℂ) (ε₀ / ((k : ℝ) + 1)))).measurableSet
  have hAanti : Antitone A := by
    intro j k hjk τ hτ
    refine ⟨hτ.1, ?_⟩
    have := hτ.2
    rw [mem_ball, dist_zero_right] at this ⊢
    refine lt_of_lt_of_le this ?_
    apply div_le_div_of_nonneg_left hε₀.le (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  have hAempty : ∀ z ∈ F, ∃ k, z ∉ A k := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · have hpos : 0 < ‖Z z‖ := norm_pos_iff.2 (hne z hzΩ)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hpos hε₀)
      refine ⟨k, fun hzA => ?_⟩
      have := hzA.2
      rw [mem_ball, dist_zero_right] at this
      have h2 : ‖Z z‖ < ε₀ / ((k : ℝ) + 1) := this
      rw [lt_div_iff₀ (by positivity)] at h2
      rw [one_div, inv_eq_one_div, div_lt_div_iff₀ (by positivity) hε₀] at hk
      nlinarith
    · exact ⟨0, fun h => hzΩ h.1⟩
  have htail := s82dx_tail (φ := φ) (F := F) hφ.2.1 hAm hAanti hAempty
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hη : (0 : ENNReal) < ENNReal.ofReal (Real.pi * (ε / 2) / (4 * M)) := by
    apply ENNReal.ofReal_pos.2
    positivity
  obtain ⟨k0, hk0⟩ := ((tendsto_order.1 htail).2 _ hη).exists
  set δ : ℝ := ε₀ / ((k0 : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδε : δ ≤ ε₀ := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0)]
  refine ⟨2 / 3 * δ, by positivity, fun {w} hw0 hwd => ?_⟩
  have hw0' : w ≠ 0 := hw0
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0'
  rw [dist_zero_right] at hwd
  have hwδ : 3 / 2 * ‖w‖ < δ := by linarith
  have hwε : 3 / 2 * ‖w‖ < ε₀ := by linarith
  set B : Set ℂ := ball w (‖w‖ / 2) with hB
  have hBball : ∀ z ∈ B, ‖w‖ / 2 < ‖z‖ ∧ ‖z‖ < 3 / 2 * ‖w‖ := by
    intro z hz
    rw [hB, mem_ball, dist_eq_norm] at hz
    have h1 := norm_sub_norm_le w z
    have h2 := norm_add_le (z - w) w
    rw [norm_sub_rev] at h1
    constructor
    · linarith
    · simp at h2; linarith
  have hBδ : B ⊆ ball (0 : ℂ) δ := fun z hz => by
    rw [mem_ball, dist_zero_right]; linarith [(hBball z hz).2]
  have hBε : B ⊆ ball (0 : ℂ) ε₀ := fun z hz => by
    rw [mem_ball, dist_zero_right]; linarith [(hBball z hz).2]
  have hBsub : B ⊆ Z '' Ω := fun z hz =>
    hsurj z (hBε hz) (norm_pos_iff.1 (by linarith [(hBball z hz).1]))
  have hdisc := s82dx_disc_bound hΓ hfree hF hφ hΩo hΩH hZ hZ' hinv hrel isOpen_ball hBsub hBε hBδ
  have hdec := s82dx_decay_bound hE hw0' hwε (E := (M : ENNReal) * phiArea φ (F ∩ A k0)) hdisc
  have hle : (M : ENNReal) * phiArea φ (F ∩ A k0) ≤
      ENNReal.ofReal (Real.pi * (ε / 2) / 4) := by
    calc (M : ENNReal) * phiArea φ (F ∩ A k0)
        ≤ (M : ENNReal) * ENNReal.ofReal (Real.pi * (ε / 2) / (4 * M)) :=
          mul_le_mul_right hk0.le _
      _ = ENNReal.ofReal (Real.pi * (ε / 2) / 4) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have h3 := ENNReal.ofReal_le_ofReal_iff (by positivity) |>.1 (hdec.trans hle)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (E w), sq_nonneg ‖w‖, Real.pi_pos]

/-- The transfer `T = φ_x ∘ ι ∘ φ_s⁻¹` near `φ_s b`: holomorphic and injective on an open set, with `T' ≠ 0`. -/
theorem s82dx_T_facts {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (x : F₀.X.carrier) (s b : S₀)
    (hbs : b ∈ (chartAt ℂ s).source) (hbx : F₀.ι b ∈ (chartAt ℂ x).source) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ s b ∈ U ∧
      (∀ v ∈ U, v ∈ (chartAt ℂ s).target ∧ F₀.ι ((chartAt ℂ s).symm v) ∈ (chartAt ℂ x).source) ∧
      DifferentiableOn ℂ (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) U ∧
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s b) ≠ 0 := by
  set U : Set ℂ := (chartAt ℂ s).target ∩ (chartAt ℂ s).symm ⁻¹' (F₀.ι ⁻¹' (chartAt ℂ x).source) with hU
  have hUo : IsOpen U := (chartAt ℂ s).isOpen_inter_preimage_symm
    (F₀.embedding.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)
  have hbU : chartAt ℂ s b ∈ U :=
    ⟨(chartAt ℂ s).map_source hbs, by
      show F₀.ι ((chartAt ℂ s).symm (chartAt ℂ s b)) ∈ (chartAt ℂ x).source
      rw [(chartAt ℂ s).left_inv hbs]; exact hbx⟩
  have hd : DifferentiableOn ℂ (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) U := fun v hv =>
    (s32p_T_differentiableAt F₀ x s hv.1 hv.2).differentiableWithinAt
  have hi : InjOn (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) U := by
    intro v hv w hw hvw
    have h1 := (chartAt ℂ x).injOn hv.2 hw.2 hvw
    have h2 := F₀.embedding.injective h1
    rw [← (chartAt ℂ s).right_inv hv.1, ← (chartAt ℂ s).right_inv hw.1, h2]
  exact ⟨U, hUo, hbU, fun v hv => hv, hd, deriv_ne_zero_of_injOn hUo hd hi hbU⟩

/-- Chain rule for a change of the chart of `S₀`: `T_{x,t} = T_{x,s} ∘ (φ_s ∘ φ_t⁻¹)` near `φ_t a`. -/
theorem s82dx_T_chainS {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (x : F₀.X.carrier) (s t a : S₀)
    (has : a ∈ (chartAt ℂ s).source) (hat : a ∈ (chartAt ℂ t).source) (hax : F₀.ι a ∈ (chartAt ℂ x).source) :
    deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ t).symm v))) (chartAt ℂ t a) =
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a) *
        deriv (chartTransition s t) (chartAt ℂ t a) := by
  have hW : (chartAt ℂ t).target ∩ (chartAt ℂ t).symm ⁻¹' (chartAt ℂ s).source ∈ 𝓝 (chartAt ℂ t a) :=
    ((chartAt ℂ t).isOpen_inter_preimage_symm (chartAt ℂ s).open_source).mem_nhds
      ⟨(chartAt ℂ t).map_source hat, by
        show (chartAt ℂ t).symm (chartAt ℂ t a) ∈ (chartAt ℂ s).source
        rw [(chartAt ℂ t).left_inv hat]; exact has⟩
  have hev : (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ t).symm v))) =ᶠ[𝓝 (chartAt ℂ t a)]
      (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) ∘ chartTransition s t := by
    filter_upwards [hW] with v hv
    show _ = chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm (chartAt ℂ s ((chartAt ℂ t).symm v))))
    rw [(chartAt ℂ s).left_inv hv.2]
  have htr : chartTransition s t (chartAt ℂ t a) = chartAt ℂ s a := by
    show chartAt ℂ s ((chartAt ℂ t).symm (chartAt ℂ t a)) = _
    rw [(chartAt ℂ t).left_inv hat]
  have hTd : DifferentiableAt ℂ (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v)))
      (chartTransition s t (chartAt ℂ t a)) := by
    rw [htr]
    exact s32p_T_differentiableAt F₀ x s ((chartAt ℂ s).map_source has) (by
      rw [(chartAt ℂ s).left_inv has]; exact hax)
  have hτd : DifferentiableAt ℂ (chartTransition s t) (chartAt ℂ t a) :=
    s23_transition_differentiableAt s t ((chartAt ℂ t).map_source hat) (by
      rw [(chartAt ℂ t).left_inv hat]; exact has)
  rw [hev.deriv_eq, deriv_comp (chartAt ℂ t a) hTd hτd, htr]

/-- Chain rule for a change of the chart of `X`: `T_{x,s} = (φ_x ∘ φ_y⁻¹) ∘ T_{y,s}` near `φ_s a`. -/
theorem s82dx_T_chainX {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (x y : F₀.X.carrier) (s a : S₀)
    (has : a ∈ (chartAt ℂ s).source) (hax : F₀.ι a ∈ (chartAt ℂ x).source)
    (hay : F₀.ι a ∈ (chartAt ℂ y).source) :
    deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a) =
      deriv (chartTransition x y) (chartAt ℂ y (F₀.ι a)) *
        deriv (fun v => chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a) := by
  have hW : (chartAt ℂ s).target ∩ (chartAt ℂ s).symm ⁻¹' (F₀.ι ⁻¹' (chartAt ℂ y).source) ∈
      𝓝 (chartAt ℂ s a) :=
    ((chartAt ℂ s).isOpen_inter_preimage_symm
      (F₀.embedding.continuous.isOpen_preimage _ (chartAt ℂ y).open_source)).mem_nhds
      ⟨(chartAt ℂ s).map_source has, by
        show F₀.ι ((chartAt ℂ s).symm (chartAt ℂ s a)) ∈ (chartAt ℂ y).source
        rw [(chartAt ℂ s).left_inv has]; exact hay⟩
  have hev : (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) =ᶠ[𝓝 (chartAt ℂ s a)]
      chartTransition x y ∘ (fun v => chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))) := by
    filter_upwards [hW] with v hv
    show _ = chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))))
    rw [(chartAt ℂ y).left_inv hv.2]
  have hTa : (fun v => chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a) = chartAt ℂ y (F₀.ι a) := by
    show chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm (chartAt ℂ s a))) = _
    rw [(chartAt ℂ s).left_inv has]
  have hτd : DifferentiableAt ℂ (chartTransition x y)
      ((fun v => chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a)) := by
    rw [hTa]
    exact s23_transition_differentiableAt x y ((chartAt ℂ y).map_source hay) (by
      rw [(chartAt ℂ y).left_inv hay]; exact hax)
  have hTd : DifferentiableAt ℂ (fun v => chartAt ℂ y (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s a) :=
    s32p_T_differentiableAt F₀ y s ((chartAt ℂ s).map_source has) (by
      rw [(chartAt ℂ s).left_inv has]; exact hay)
  rw [hev.deriv_eq, deriv_comp (chartAt ℂ s a) hτd hTd, (chartAt ℂ s).left_inv has]

/-- **The local law of the extension**: in any chart `t ∋ a` of `S₀` and `x ∋ ι a` of `X`,
`q_t(φ_t a) = (q_a(φ_a a) / T_{x,a}'(φ_a a)²) · T_{x,t}'(φ_t a)²`. -/
theorem s82dx_E_law {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (x : F₀.X.carrier) (t a : S₀) (hat : a ∈ (chartAt ℂ t).source) (hax : F₀.ι a ∈ (chartAt ℂ x).source) :
    q t (chartAt ℂ t a) = q a (chartAt ℂ a a) /
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a).symm v))) (chartAt ℂ a a) ^ 2 *
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ t).symm v))) (chartAt ℂ t a) ^ 2 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hlaw := hq'.1.2 a t (chartAt ℂ t a) ((chartAt ℂ t).map_source hat) (by
    rw [(chartAt ℂ t).left_inv hat]; exact mem_chart_source ℂ a)
  have htr : chartTransition a t (chartAt ℂ t a) = chartAt ℂ a a := by
    show chartAt ℂ a ((chartAt ℂ t).symm (chartAt ℂ t a)) = _
    rw [(chartAt ℂ t).left_inv hat]
  rw [zpow_zero, mul_one, zpow_two, ← pow_two, htr] at hlaw
  obtain ⟨-, -, -, -, -, hne⟩ := s82dx_T_facts F₀ x a a (mem_chart_source ℂ a) hax
  rw [hlaw, s82dx_T_chainS F₀ x a t a (mem_chart_source ℂ a) hat hax]
  field_simp


/-- Chain rule for `Z = φ_X ∘ ι ∘ p̂`: it factors as `T ∘ (φ_s ∘ p̂)` with `T = φ_X ∘ ι ∘ φ_s⁻¹`. -/
theorem s82dx_Z_chain {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (x : F₀.X.carrier) {z : ℂ} (hz : 0 < z.im)
    (hzx : F₀.ι (utm_pext p₀ z) ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun v => chartAt ℂ x (F₀.ι (utm_pext p₀ v))) z ∧
      deriv (fun v => chartAt ℂ x (F₀.ι (utm_pext p₀ v))) z =
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (utm_pext p₀ z)).symm v)))
            (chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ z)) *
          deriv (fun v => chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ v)) z := by
  set s := utm_pext p₀ z with hs
  have hsmem : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
  have hTd : DifferentiableAt ℂ (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s s) :=
    s32p_T_differentiableAt F₀ x s hsmem (by rw [(chartAt ℂ s).left_inv (mem_chart_source ℂ s)]; exact hzx)
  have hhd : DifferentiableAt ℂ (fun v => chartAt ℂ s (utm_pext p₀ v)) z :=
    utm_a_differentiableAt hp₀.2.1 s hz (mem_chart_source ℂ s)
  have hcont : ContinuousAt (utm_pext p₀) z := utm_a_continuousAt hp₀.1.continuous hz
  have hev : (fun v => chartAt ℂ x (F₀.ι (utm_pext p₀ v))) =ᶠ[𝓝 z]
      (fun w => chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm w))) ∘
        (fun v => chartAt ℂ s (utm_pext p₀ v)) := by
    have : (chartAt ℂ s).source ∈ 𝓝 (utm_pext p₀ z) :=
      (chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s)
    filter_upwards [hcont.preimage_mem_nhds this] with v hv
    show _ = chartAt ℂ x (F₀.ι ((chartAt ℂ s).symm (chartAt ℂ s (utm_pext p₀ v))))
    rw [(chartAt ℂ s).left_inv hv]
  refine ⟨(hTd.comp z hhd).congr_of_eventuallyEq hev, ?_⟩
  rw [hev.deriv_eq]
  exact deriv_comp z hTd hhd


/-- Both factors of `Z' = T' · (φ_s ∘ p̂)'` are non-zero, hence so is `Z'`. -/
theorem s82dx_Z_deriv_ne {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (x : F₀.X.carrier) {z : ℂ} (hz : 0 < z.im)
    (hzx : F₀.ι (utm_pext p₀ z) ∈ (chartAt ℂ x).source) :
    deriv (fun v => chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ v)) z ≠ 0 ∧
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (utm_pext p₀ z)).symm v)))
        (chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ z)) ≠ 0 ∧
      deriv (fun v => chartAt ℂ x (F₀.ι (utm_pext p₀ v))) z ≠ 0 := by
  have hpe : utm_pext p₀ z = p₀ ⟨z, hz⟩ := by simp [utm_pext, hz]
  have hs : p₀ ⟨z, hz⟩ ∈ (chartAt ℂ (utm_pext p₀ z)).source := by
    rw [← hpe]; exact mem_chart_source ℂ _
  obtain ⟨U, hUo, hzU, -, hinj, hU⟩ := utm_liftQD_local hq hp₀ ⟨z, hz⟩ (utm_pext p₀ z) hs
  have h1 : deriv (fun v => chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ v)) z ≠ 0 :=
    (hU z hzU).2.2.1
  obtain ⟨-, -, -, -, -, h2⟩ := s82dx_T_facts F₀ x (utm_pext p₀ z) (utm_pext p₀ z)
    (mem_chart_source ℂ _) hzx
  refine ⟨h1, h2, ?_⟩
  rw [(s82dx_Z_chain F₀ hp₀ x hz hzx).2]
  exact mul_ne_zero h2 h1

/-- The local expression `E` of `q` in the chart `x` of `X` satisfies `E (Z z) · Z'(z)² = ψ(z)`,
where `ψ = utm_liftQD q p₀` is the lift of `q` to `ℍ`. -/
theorem s82dx_E_rel {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (x : F₀.X.carrier) {z : ℂ} (hz : 0 < z.im)
    (hzx : F₀.ι (utm_pext p₀ z) ∈ (chartAt ℂ x).source) :
    (q (Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))))
        (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))))
          (Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))))) /
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (Function.invFun F₀.ι
          ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))))).symm v)))
        (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))))
          (Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z))))))
        ^ 2) *
      deriv (fun v => chartAt ℂ x (F₀.ι (utm_pext p₀ v))) z ^ 2 = utm_liftQD q p₀ z := by
  have hinv : Function.invFun F₀.ι ((chartAt ℂ x).symm (chartAt ℂ x (F₀.ι (utm_pext p₀ z)))) =
      utm_pext p₀ z := by
    rw [(chartAt ℂ x).left_inv hzx]
    exact Function.leftInverse_invFun F₀.embedding.injective _
  rw [hinv]
  obtain ⟨-, hT, -⟩ := s82dx_Z_deriv_ne F₀ hq hp₀ x hz hzx
  rw [(s82dx_Z_chain F₀ hp₀ x hz hzx).2, utm_liftQD]
  field_simp


/-- If `Z` is holomorphic with non-vanishing derivative on an open set `Ω ⊆ ℍ` and `Et ∘ Z · Z'² = φ`
on `Ω` with `φ` holomorphic on `ℍ`, then `Et` is holomorphic at every point of `Z(Ω)`. -/
theorem s82dx_Et_diff {Ω : Set ℂ} {Z Et φ : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩH : Ω ⊆ upperHalf)
    (hZ : DifferentiableOn ℂ Z Ω) (hZ' : ∀ τ ∈ Ω, deriv Z τ ≠ 0)
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (hrel : ∀ τ ∈ Ω, Et (Z τ) * deriv Z τ ^ 2 = φ τ) {u₀ : ℂ} (hu₀ : u₀ ∈ Z '' Ω) :
    DifferentiableAt ℂ Et u₀ := by
  obtain ⟨τ₀, hτ₀, rfl⟩ := hu₀
  have hA : AnalyticAt ℂ Z τ₀ := hZ.analyticAt (hΩ.mem_nhds hτ₀)
  set σ : ℂ → ℂ := hA.hasStrictDerivAt.localInverse _ _ _ (hZ' τ₀ hτ₀) with hσ
  have hσA : AnalyticAt ℂ σ (Z τ₀) := hA.analyticAt_localInverse (hZ' τ₀ hτ₀)
  have hσ0 : σ (Z τ₀) = τ₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hright : ∀ᶠ u in 𝓝 (Z τ₀), Z (σ u) = u :=
    HasStrictDerivAt.eventually_right_inverse _ _
  have hσΩ : ∀ᶠ u in 𝓝 (Z τ₀), σ u ∈ Ω := by
    have := hσA.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hΩ.mem_nhds hτ₀)
    exact this
  have hdA : AnalyticAt ℂ (deriv Z) τ₀ := (hZ.analyticAt (hΩ.mem_nhds hτ₀)).deriv
  have hφA : AnalyticAt ℂ φ τ₀ :=
    hφ.analyticAt (isOpen_upperHalf.mem_nhds (hΩH hτ₀))
  have hev : Et =ᶠ[𝓝 (Z τ₀)] fun u => φ (σ u) / deriv Z (σ u) ^ 2 := by
    filter_upwards [hright, hσΩ] with u hu hΩu
    have h := hrel (σ u) hΩu
    rw [hu] at h
    rw [← h]
    have := hZ' (σ u) hΩu
    field_simp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h1 : DifferentiableAt ℂ (fun u => φ (σ u)) (Z τ₀) := by
    have : AnalyticAt ℂ φ (σ (Z τ₀)) := by rw [hσ0]; exact hφA
    exact (this.comp hσA).differentiableAt
  have h2 : DifferentiableAt ℂ (fun u => deriv Z (σ u)) (Z τ₀) := by
    have : AnalyticAt ℂ (deriv Z) (σ (Z τ₀)) := by rw [hσ0]; exact hdA
    exact (this.comp hσA).differentiableAt
  refine h1.div (h2.pow 2) ?_
  rw [hσ0]
  exact pow_ne_zero 2 (hZ' τ₀ hτ₀)


/-- **Stub A (hpole)**: the local expression of a holomorphic quadratic differential `q` on `S₀`
(`S₀` uniformized with integrable lift `φ`) has at most a simple pole at every puncture. -/
theorem s82dx_hpole {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ₀ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ₀ F) {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hqφ : ∀ τ ∈ upperHalf, utm_liftQD q p₀ τ = φ τ) :
    ∀ p ∈ F₀.P, ∀ x : F₀.X.carrier, p ∈ (chartAt ℂ x).source →
      ∃ c : ℂ, ∃ r : ℂ → ℂ, AnalyticAt ℂ r (chartAt ℂ x p) ∧
        ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p),
          q (Function.invFun F₀.ι ((chartAt ℂ x).symm z))
              (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z))
                (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) /
            deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (Function.invFun F₀.ι
              ((chartAt ℂ x).symm z))).symm v)))
              (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z))
                (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) ^ 2
          = c / (z - chartAt ℂ x p) + r z := by
  classical
  intro p hp x hpx
  set χ := chartAt ℂ x with hχ
  set c : ℂ := χ p with hc
  -- the local expression of `q` in the chart `χ`
  set Et : ℂ → ℂ := fun z =>
    q (Function.invFun F₀.ι (χ.symm z))
        (chartAt ℂ (Function.invFun F₀.ι (χ.symm z)) (Function.invFun F₀.ι (χ.symm z))) /
      deriv (fun v => χ (F₀.ι ((chartAt ℂ (Function.invFun F₀.ι (χ.symm z))).symm v)))
        (chartAt ℂ (Function.invFun F₀.ι (χ.symm z)) (Function.invFun F₀.ι (χ.symm z))) ^ 2
    with hEt
  set Z0 : ℂ → ℂ := fun z => χ (F₀.ι (utm_pext p₀ z)) with hZ0
  set Ω : Set ℂ := upperHalf ∩ (fun z => F₀.ι (utm_pext p₀ z)) ⁻¹' χ.source with hΩ
  have hpext : ContinuousOn (fun z => F₀.ι (utm_pext p₀ z)) upperHalf := fun z hz =>
    (F₀.embedding.continuous.continuousAt.comp
      (utm_a_continuousAt hp₀.1.continuous hz)).continuousWithinAt
  have hΩo : IsOpen Ω := hpext.isOpen_inter_preimage isOpen_upperHalf χ.open_source
  have hΩH : Ω ⊆ upperHalf := inter_subset_left
  have hΩim : ∀ z ∈ Ω, 0 < z.im := fun z hz => hz.1
  have hΩx : ∀ z ∈ Ω, F₀.ι (utm_pext p₀ z) ∈ χ.source := fun z hz => hz.2
  have hZ0d : DifferentiableOn ℂ Z0 Ω := fun z hz =>
    ((s82dx_Z_chain F₀ hp₀ x (hΩim z hz) (hΩx z hz)).1).differentiableWithinAt
  have hZ0' : ∀ z ∈ Ω, deriv Z0 z ≠ 0 := fun z hz =>
    (s82dx_Z_deriv_ne F₀ hq hp₀ x (hΩim z hz) (hΩx z hz)).2.2
  have hrel0 : ∀ z ∈ Ω, Et (Z0 z) * deriv Z0 z ^ 2 = φ z := fun z hz => by
    rw [← hqφ z hz.1]
    exact s82dx_E_rel F₀ hq hp₀ x (hΩim z hz) (hΩx z hz)
  have hφd : DifferentiableOn ℂ φ upperHalf := hφ.1
  -- the radius
  have hct : c ∈ χ.target := χ.map_source hpx
  set Sbad : Set ℂ := χ '' (((F₀.P : Set F₀.X.carrier) ∩ χ.source) \ {p}) with hSbad
  have hSfin : Sbad.Finite := ((F₀.P.finite_toSet.inter_of_left _).diff).image _
  have hcS : c ∉ Sbad := by
    rintro ⟨q', ⟨⟨-, hq's⟩, hq'p⟩, hq'c⟩
    exact hq'p (χ.injOn hq's hpx hq'c)
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.1 hSfin.isClosed.isOpen_compl c hcS
  obtain ⟨ε₂, hε₂, hε₂T⟩ := Metric.isOpen_iff.1 χ.open_target c hct
  set ε₀ : ℝ := min ε₁ ε₂ with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε₁ hε₂
  have hballS : ball c ε₀ ⊆ Sbadᶜ := (ball_subset_ball (min_le_left _ _)).trans hε₁S
  have hballT : ball c ε₀ ⊆ χ.target := (ball_subset_ball (min_le_right _ _)).trans hε₂T
  -- surjectivity onto the punctured disc
  have hsurj0 : ∀ u ∈ ball c ε₀, u ≠ c → u ∈ Z0 '' Ω := by
    intro u hu huc
    set w := χ.symm u with hw
    have hws : w ∈ χ.source := χ.map_target (hballT hu)
    have hwu : χ w = u := χ.right_inv (hballT hu)
    have hwP : w ∉ (F₀.P : Set F₀.X.carrier) := by
      intro hwP
      by_cases hwp : w = p
      · exact huc (by rw [← hwu, hwp])
      · exact hballS hu ⟨w, ⟨⟨hwP, hws⟩, hwp⟩, hwu⟩
    have hrange : w ∈ Set.range F₀.ι := by
      rw [F₀.range_ι]
      simpa using hwP
    obtain ⟨s, hs⟩ := hrange
    obtain ⟨τ', hτ'⟩ := hp₀.2.2.1 s
    have hpe : utm_pext p₀ (τ' : ℂ) = s := by
      simp [utm_pext, τ'.im_pos, hτ']
    refine ⟨(τ' : ℂ), ⟨τ'.im_pos, ?_⟩, ?_⟩
    · show F₀.ι (utm_pext p₀ (τ' : ℂ)) ∈ χ.source
      rw [hpe, hs]; exact hws
    · show χ (F₀.ι (utm_pext p₀ (τ' : ℂ))) = u
      rw [hpe, hs, hwu]
  have hne0 : ∀ z ∈ Ω, Z0 z ≠ c := by
    intro z hz hzc
    have hxs : F₀.ι (utm_pext p₀ z) = p := χ.injOn (hΩx z hz) hpx hzc
    have hrp : p ∈ Set.range F₀.ι := ⟨_, hxs⟩
    rw [F₀.range_ι] at hrp
    exact hrp (by simp [hp])
  -- the shifted data for the pole analysis
  set Z : ℂ → ℂ := fun z => Z0 z - c with hZ
  set E : ℂ → ℂ := fun w => Et (c + w) with hE
  have hZd : DifferentiableOn ℂ Z Ω := hZ0d.sub_const c
  have hZder : ∀ z, deriv Z z = deriv Z0 z := fun z => deriv_sub_const c
  have hinv : ∀ τ ∈ Ω, ∀ γ ∈ Γ₀, h36p_m γ τ ∈ Ω ∧ Z (h36p_m γ τ) = Z τ := by
    intro τ hτ γ hγ
    have him : 0 < (h36p_m γ τ).im := utm_b_mob_im_pos γ hτ.1
    have hpe : utm_pext p₀ (h36p_m γ τ) = utm_pext p₀ τ := utm_b_pext_mob hp₀ hγ hτ.1
    refine ⟨⟨him, ?_⟩, ?_⟩
    · show F₀.ι (utm_pext p₀ (h36p_m γ τ)) ∈ χ.source
      rw [hpe]; exact hτ.2
    · show χ (F₀.ι (utm_pext p₀ (h36p_m γ τ))) - c = χ (F₀.ι (utm_pext p₀ τ)) - c
      rw [hpe]
  have hEd : DifferentiableOn ℂ E (ball (0 : ℂ) ε₀ \ {0}) := by
    intro w hw
    have hu : c + w ∈ ball c ε₀ := by
      have := hw.1
      rw [mem_ball, dist_zero_right] at this
      rw [mem_ball, dist_eq_norm]; simpa using this
    have hwc : c + w ≠ c := by
      intro h; exact hw.2 (by simpa using h)
    have hEt := s82dx_Et_diff hΩo hΩH hZ0d hZ0' hφd hrel0 (hsurj0 _ hu hwc)
    exact (hEt.comp w ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hrel : ∀ τ ∈ Ω, Z τ ∈ ball (0 : ℂ) ε₀ → E (Z τ) * deriv Z τ ^ 2 = φ τ := by
    intro τ hτ _
    rw [hZder]
    have : E (Z τ) = Et (Z0 τ) := by simp [hE, hZ]
    rw [this]
    exact hrel0 τ hτ
  have hsurj : ∀ z ∈ ball (0 : ℂ) ε₀, z ≠ 0 → z ∈ Z '' Ω := by
    intro z hz hz0
    have hu : c + z ∈ ball c ε₀ := by
      rw [mem_ball, dist_zero_right] at hz
      rw [mem_ball, dist_eq_norm]; simpa using hz
    obtain ⟨τ, hτ, hτz⟩ := hsurj0 _ hu (by simpa using hz0)
    exact ⟨τ, hτ, by simp [hZ, hτz]⟩
  have hne : ∀ τ ∈ Ω, Z τ ≠ 0 := fun τ hτ h => hne0 τ hτ (by
    simp only [hZ] at h; linear_combination h)
  obtain ⟨a, h, hh, hid⟩ := s82dx_pole_analysis hΓ hfree hF hφ hΩo hΩH hε₀ hZd
    (fun τ hτ => by rw [hZder]; exact hZ0' τ hτ) hinv hsurj hne hEd hrel
  refine ⟨a, fun z => h (z - c), ?_, ?_⟩
  · have hopen : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (fun z => h (z - c)) z := by
      filter_upwards [ball_mem_nhds c hε₀] with z hz
      have hz' : z - c ∈ ball (0 : ℂ) ε₀ := by
        rw [mem_ball, dist_zero_right]; rw [mem_ball, dist_eq_norm] at hz; exact hz
      exact (hh.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
        ((differentiableAt_id).sub_const c)
    exact (Complex.analyticAt_iff_eventually_differentiableAt).2 hopen
  · have hmem : ∀ᶠ z in 𝓝[≠] c, z ∈ ball c ε₀ :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hε₀)
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzc
    have hz' : z - c ∈ ball (0 : ℂ) ε₀ \ {0} := by
      refine ⟨?_, fun h0 => hzc (by simpa [sub_eq_zero] using h0)⟩
      rw [mem_ball, dist_zero_right]; rw [mem_ball, dist_eq_norm] at hz; exact hz
    have := hid _ hz'
    simpa [hE] using this


/-- **[D3a(ii), stub] Extension of a holomorphic differential with simple poles at the punctures.**  Let `q` be a
holomorphic quadratic differential on the finite-type surface `S₀ = X ∖ P` (type `(g, n, 0)`).  Its expression in a
chart `x` of `X` is `E_x(z) = q_s(φ_s s) / T'(φ_s s)²` at `z = φ_x(ι s)`, `T = φ_x ∘ ι ∘ φ_s⁻¹` (the inverse of the
law of `pullbackQD`).  If `E_x` has at most a simple pole `c/(z - φ_x p) + r(z)` at every puncture `p` (in every chart
at `p`), then `q` is admissible: `q̂ x z := E_x z` on `φ_x(ι S₀)`, `0` at the punctures and off the chart target, lies in
`admissibleQDSpace F₀` and `pullbackQD F₀ q̂ = q`. -/
theorem s82dx_extend_qd {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hpole : ∀ p ∈ F₀.P, ∀ x : F₀.X.carrier, p ∈ (chartAt ℂ x).source → ∃ c : ℂ, ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r (chartAt ℂ x p) ∧ ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p),
        q (Function.invFun F₀.ι ((chartAt ℂ x).symm z))
            (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z)) (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) /
          deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z))).symm v)))
            (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z)) (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) ^ 2 =
          c / (z - chartAt ℂ x p) + r z) :
    q ∈ admissibleQDInterior F₀ := by
  classical
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hinj : Function.Injective F₀.ι := F₀.embedding.injective
  have hrange : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
  -- the chart expression `E_x` and the extension `q̂`
  set E : F₀.X.carrier → ℂ → ℂ := fun x z =>
    q (Function.invFun F₀.ι ((chartAt ℂ x).symm z))
        (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z)) (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) /
      deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z))).symm v)))
        (chartAt ℂ (Function.invFun F₀.ι ((chartAt ℂ x).symm z)) (Function.invFun F₀.ι ((chartAt ℂ x).symm z))) ^ 2
    with hE
  set qh : F₀.X.carrier → ℂ → ℂ := fun x z =>
    if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ range F₀.ι then E x z else 0 with hqh
  have hqh_E : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F₀.ι → qh x z = E x z :=
    fun x z h1 h2 => by
      show (if _ then _ else _) = _
      rw [ite_eq_left ⟨h1, h2⟩]
  have hqh_at : ∀ (x : F₀.X.carrier) (a : S₀), F₀.ι a ∈ (chartAt ℂ x).source →
      qh x (chartAt ℂ x (F₀.ι a)) = q a (chartAt ℂ a a) /
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a).symm v))) (chartAt ℂ a a) ^ 2 := by
    intro x a hax
    rw [hqh_E x _ ((chartAt ℂ x).map_source hax) (by rw [(chartAt ℂ x).left_inv hax]; exact ⟨a, rfl⟩)]
    simp only [hE, (chartAt ℂ x).left_inv hax, Function.leftInverse_invFun hinj a]
  -- (1) the transformation law
  have hlaw : IsDiffFamily 2 0 qh := by
    refine ⟨fun x z hz => ?_, fun x y z hz hzx => ?_⟩
    · show (if _ then _ else _) = _
      rw [ite_eq_right fun h => hz h.1]
    · rw [zpow_zero, mul_one, zpow_two, ← pow_two]
      obtain ⟨-, -, hτeq⟩ := s23_transition_mem hz hzx
      by_cases hr : (chartAt ℂ y).symm z ∈ range F₀.ι
      · obtain ⟨a, ha⟩ := hr
        have hay : F₀.ι a ∈ (chartAt ℂ y).source := by rw [ha]; exact (chartAt ℂ y).map_target hz
        have hax : F₀.ι a ∈ (chartAt ℂ x).source := by rw [ha]; exact hzx
        have hz' : chartAt ℂ y (F₀.ι a) = z := by rw [ha, (chartAt ℂ y).right_inv hz]
        have hτz : chartTransition x y z = chartAt ℂ x (F₀.ι a) := by
          show chartAt ℂ x ((chartAt ℂ y).symm z) = _
          rw [ha]
        have hch := s82dx_T_chainX F₀ x y a a (mem_chart_source ℂ a) hax hay
        obtain ⟨-, -, -, -, -, hneX⟩ := s82dx_T_facts F₀ x a a (mem_chart_source ℂ a) hax
        obtain ⟨-, -, -, -, -, hneY⟩ := s82dx_T_facts F₀ y a a (mem_chart_source ℂ a) hay
        rw [hch] at hneX
        have hτ0 := left_ne_zero_of_mul hneX
        rw [hτz, hqh_at x a hax, ← hz', hqh_at y a hay, hch]
        rw [hz'] at hτ0
        rw [hz']
        field_simp
      · have h1 : qh y z = 0 := by
          show (if _ then _ else _) = _
          rw [ite_eq_right fun h => hr h.2]
        have h2 : qh x (chartTransition x y z) = 0 := by
          show (if _ then _ else _) = _
          rw [ite_eq_right fun h => hr (by rw [← hτeq]; exact h.2)]
        rw [h1, h2, zero_mul]
  -- (2) holomorphy off the punctures
  have hhol : ∀ x : F₀.X.carrier,
      DifferentiableOn ℂ (qh x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F₀.ι) := by
    intro x z₀ hz₀
    obtain ⟨hz₀t, a₀, ha₀⟩ := hz₀
    set e := F₀.embedding.toOpenPartialHomeomorph F₀.ι with he
    have he_symm : ∀ b, e.symm (F₀.ι b) = b := fun b => F₀.embedding.toOpenPartialHomeomorph_left_inv F₀.ι
    have he_t : e.target = range F₀.ι := F₀.embedding.toOpenPartialHomeomorph_target
    have he_r : ∀ w ∈ range F₀.ι, F₀.ι (e.symm w) = w := fun w hw =>
      F₀.embedding.toOpenPartialHomeomorph_right_inv F₀.ι hw
    set V : ℂ → ℂ := fun z => chartAt ℂ a₀ (e.symm ((chartAt ℂ x).symm z)) with hV
    have hsz₀ : (chartAt ℂ x).symm z₀ = F₀.ι a₀ := ha₀.symm
    have hN1 : e.symm ⁻¹' (chartAt ℂ a₀).source ∈ 𝓝 (F₀.ι a₀) :=
      (e.continuousAt_symm (by rw [he_t]; exact ⟨a₀, rfl⟩)).preimage_mem_nhds
        ((chartAt ℂ a₀).open_source.mem_nhds (by rw [he_symm]; exact mem_chart_source ℂ a₀))
    have hN2 : range F₀.ι ∈ 𝓝 (F₀.ι a₀) := F₀.embedding.isOpen_range.mem_nhds ⟨a₀, rfl⟩
    have hW : ∀ᶠ z in 𝓝 z₀, z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ range F₀.ι ∧
        e.symm ((chartAt ℂ x).symm z) ∈ (chartAt ℂ a₀).source := by
      have hc := (chartAt ℂ x).continuousAt_symm hz₀t
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz₀t,
        hc.preimage_mem_nhds (by rw [hsz₀]; exact hN2), hc.preimage_mem_nhds (by rw [hsz₀]; exact hN1)]
        with z h1 h2 h3
      exact ⟨h1, h2, h3⟩
    -- on `W`, `q̂_x = (q_{a₀} / T'²) ∘ V`, `T = φ_x ∘ ι ∘ φ_{a₀}⁻¹`, `V = T⁻¹`
    have hEq : qh x =ᶠ[𝓝 z₀] fun z => q a₀ (V z) /
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (V z) ^ 2 := by
      filter_upwards [hW] with z hz
      obtain ⟨hzt, hzr, hzs⟩ := hz
      set b := e.symm ((chartAt ℂ x).symm z) with hb
      have hιb : F₀.ι b = (chartAt ℂ x).symm z := he_r _ hzr
      have hbx : F₀.ι b ∈ (chartAt ℂ x).source := by rw [hιb]; exact (chartAt ℂ x).map_target hzt
      have hzb : chartAt ℂ x (F₀.ι b) = z := by rw [hιb, (chartAt ℂ x).right_inv hzt]
      obtain ⟨-, -, -, -, -, hD⟩ := s82dx_T_facts F₀ x a₀ b hzs hbx
      have hlaw' := s82dx_E_law F₀ hq x a₀ b hzs hbx
      show qh x z = q a₀ (chartAt ℂ a₀ b) /
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (chartAt ℂ a₀ b) ^ 2
      rw [← hzb, hqh_at x b hbx, eq_div_iff (pow_ne_zero 2 hD), hlaw']
    have hV₀ : V z₀ = chartAt ℂ a₀ a₀ := by
      show chartAt ℂ a₀ (e.symm ((chartAt ℂ x).symm z₀)) = _
      rw [hsz₀, he_symm]
    have hax₀ : F₀.ι a₀ ∈ (chartAt ℂ x).source := by rw [← hsz₀]; exact (chartAt ℂ x).map_target hz₀t
    obtain ⟨U, hUo, hcU, -, hTdU, hne⟩ := s82dx_T_facts F₀ x a₀ a₀ (mem_chart_source ℂ a₀) hax₀
    have hVc : ContinuousAt V z₀ := by
      have h1 : ContinuousAt (fun z => e.symm ((chartAt ℂ x).symm z)) z₀ :=
        ContinuousAt.comp_of_eq (e.continuousAt_symm (by rw [he_t, hsz₀]; exact ⟨a₀, rfl⟩))
          ((chartAt ℂ x).continuousAt_symm hz₀t) rfl
      exact ContinuousAt.comp_of_eq ((chartAt ℂ a₀).continuousAt (mem_chart_source ℂ a₀)) h1
        (by rw [hsz₀, he_symm])
    have hTd : DifferentiableAt ℂ (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (V z₀) := by
      rw [hV₀]; exact (hTdU _ hcU).differentiableAt (hUo.mem_nhds hcU)
    have hne' : deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (V z₀) ≠ 0 := by
      rw [hV₀]; exact hne
    have hfg : ∀ᶠ z in 𝓝 z₀, (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (V z) = z := by
      filter_upwards [hW] with z hz
      obtain ⟨hzt, hzr, hzs⟩ := hz
      show chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm (chartAt ℂ a₀ (e.symm ((chartAt ℂ x).symm z))))) = z
      rw [(chartAt ℂ a₀).left_inv hzs, he_r _ hzr, (chartAt ℂ x).right_inv hzt]
    have hVd := HasDerivAt.of_local_left_inverse hVc hTd.hasDerivAt hne' hfg
    have hVt : V z₀ ∈ (chartAt ℂ a₀).target := by rw [hV₀]; exact (chartAt ℂ a₀).map_source (mem_chart_source ℂ a₀)
    have hqd : DifferentiableAt ℂ (q a₀) (V z₀) :=
      (hq'.2 a₀ _ hVt).differentiableAt ((chartAt ℂ a₀).open_target.mem_nhds hVt)
    have hT'd : DifferentiableAt ℂ (deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v)))) (V z₀) := by
      rw [hV₀]; exact ((hTdU.analyticOnNhd hUo) _ hcU).deriv.differentiableAt
    have hR : DifferentiableAt ℂ (fun z => q a₀ (V z) /
        deriv (fun v => chartAt ℂ x (F₀.ι ((chartAt ℂ a₀).symm v))) (V z) ^ 2) z₀ :=
      (hqd.comp z₀ hVd.differentiableAt).div ((hT'd.comp z₀ hVd.differentiableAt).pow 2)
        (pow_ne_zero 2 hne')
    exact (hR.congr_of_eventuallyEq hEq).differentiableWithinAt
  -- (3) the punctures: value `0` and the simple pole form
  have hpoleC : ∀ x : F₀.X.carrier, ∀ p ∈ F₀.P, p ∈ (chartAt ℂ x).source → qh x (chartAt ℂ x p) = 0 ∧
      ∃ c : ℂ, ∃ r : ℂ → ℂ, AnalyticAt ℂ r (chartAt ℂ x p) ∧
        ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p), qh x z = c / (z - chartAt ℂ x p) + r z := by
    intro x p hp hpx
    have hpr : p ∉ range F₀.ι := by rw [hrange]; simpa using hp
    refine ⟨?_, ?_⟩
    · show (if _ then _ else _) = _
      rw [ite_eq_right fun h => hpr (by rw [(chartAt ℂ x).left_inv hpx] at h; exact h.2)]
    · obtain ⟨c, r, hr, hev⟩ := hpole p hp x hpx
      refine ⟨c, r, hr, ?_⟩
      have hP' : ((↑F₀.P : Set F₀.X.carrier) \ {p})ᶜ ∈ 𝓝 p :=
        (F₀.P.finite_toSet.sdiff).isClosed.isOpen_compl.mem_nhds (by simp)
      have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ x p), z ∈ (chartAt ℂ x).target ∧
          (chartAt ℂ x).symm z ∈ ((↑F₀.P : Set F₀.X.carrier) \ {p})ᶜ := by
        filter_upwards [(chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hpx),
          ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hpx)).preimage_mem_nhds
            (by rw [(chartAt ℂ x).left_inv hpx]; exact hP')] with z h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin, hev] with z hz hzne hzE
      have hzr : (chartAt ℂ x).symm z ∈ range F₀.ι := by
        rw [hrange]
        intro hzP
        refine hz.2 ⟨hzP, fun hzp => hzne ?_⟩
        rw [mem_singleton_iff, ← (chartAt ℂ x).right_inv hz.1, mem_singleton_iff.1 hzp]
      rw [hqh_E x z hz.1 hzr]
      exact hzE
  -- (4) `ι^* q̂ = q`
  have hpull : pullbackQD F₀ qh = q := by
    funext t w
    by_cases hw : w ∈ (chartAt ℂ t).target
    · have hat : (chartAt ℂ t).symm w ∈ (chartAt ℂ t).source := (chartAt ℂ t).map_target hw
      have hw' : chartAt ℂ t ((chartAt ℂ t).symm w) = w := (chartAt ℂ t).right_inv hw
      show (chartAt ℂ t).target.indicator _ w = q t w
      rw [indicator_of_mem hw]
      show qh (F₀.ι ((chartAt ℂ t).symm w)) (chartAt ℂ (F₀.ι ((chartAt ℂ t).symm w)) (F₀.ι ((chartAt ℂ t).symm w))) *
        deriv (fun v => chartAt ℂ (F₀.ι ((chartAt ℂ t).symm w)) (F₀.ι ((chartAt ℂ t).symm v))) w ^ 2 = q t w
      rw [hqh_at _ _ (mem_chart_source ℂ _)]
      conv_rhs => rw [← hw', s82dx_E_law F₀ hq (F₀.ι ((chartAt ℂ t).symm w)) t _ hat (mem_chart_source ℂ _)]
      rw [hw']
    · rw [hq'.1.1 t w hw]
      show (chartAt ℂ t).target.indicator _ w = 0
      rw [indicator_of_notMem hw]
  have hadm : qh ∈ admissibleQDSpace F₀ :=
    ⟨hlaw, hhol, hpoleC, fun x j => j.elim0, fun x j => j.elim0, fun x j => j.elim0⟩
  exact Submodule.mem_map.2 ⟨qh, hadm, hpull⟩

/-- **[D3a, stub] Integrable automorphic forms are admissible.**  If the lift `φ` of a holomorphic quadratic
differential `q` on the finite-type surface `S₀ = ℍ/Γ₀` is area integrable over a fundamental domain, then `q`
is an admissible differential (at most a simple pole at each puncture).  Route: `h36p_unfold` transfers
`∫_R |φ| ≤ ∫_F |φ|` for every region `R ⊆ ℍ` injective modulo `Γ₀`; sub-mean-value on the discs
`B(w, |w|/2)` of a puncture chart gives `|w|² |q(w)| → 0`; Riemann's removable singularity theorem gives the
simple pole; extension of `q` over the punctures gives `q̂ ∈ admissibleQDSpace`. No cusp normal form is used. -/
theorem s82dx_integrable_admissible {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (hΓ : IsFuchsian Γ₀) {F : Set ℂ} (hF : IsFundamentalDomainH Γ₀ F)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ₀ F) {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hqφ : ∀ τ ∈ upperHalf, utm_liftQD q p₀ τ = φ τ) : q ∈ admissibleQDInterior F₀ :=
  s82dx_extend_qd F₀ hq (s82dx_hpole F₀ hp₀ hΓ (s27g_actsFreely hp₀) hF hφ hq hqφ)

end LiZhongQC
