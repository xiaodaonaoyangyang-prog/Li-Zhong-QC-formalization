import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.FluxRoute
import LiZhongQC.Lemmas.BoundaryJensen

/-!
# §35 单位圆上的 Teichmüller 映射 — Teichmüller maps of the unit disc

* §35.1 boundary behaviour of the trajectories of a quadratic differential of finite norm in `Δ`:
  Lemma 35.1 (the rays `α⁺`, `α⁻` of a non-critical horizontal trajectory converge to boundary
  points, (35.1)–(35.2)), Lemma 35.2 (the two end points are different), Lemma 35.3 (the
  trajectory is the shortest curve between its end points)
                                            — `IsHorizontalRay`, `lemma35_1`, `lemma35_2`, `lemma35_3`
* §35.2 the stretching function `λ_{g,ω}` (35.4), the Reich–Strebel main inequality (35.3)–(35.5)
  and its simplified form              — `lambdaStretchDisc`, `thm35_2_main_inequality`,
                                            `main_inequality_simplified`
* §35.3 the extremal problem for given boundary values: Theorem 35.1 (existence), Theorem 35.2
  (Reich–Strebel: a Teichmüller map with `‖φ‖ < ∞` is the unique extremal map), the example of the
  stretch of the half-plane           — `thm35_1_exists_extremal`, `thm35_2_reich_strebel`
* §35.4 the functionals `I[κ]`, `H[κ]`, `Δ[κ]`, (35.6)–(35.9); Theorem 35.3; Lemmas 35.4–35.6;
  Theorem 35.4 (`H[κ] = k` ⟹ extremal, (35.12)); Theorem 35.5 (extremal ⟹ `H[κ] = ‖κ‖_∞`)
                                            — `hamiltonI`, `hamiltonH`, `hamiltonDelta`, `thm35_3`,
                                              `lemma35_4`, `lemma35_5`, `lemma35_6`, `thm35_4`, `thm35_5`
* §35.5 Hamilton sequences, degenerate Hamilton sequences, the boundary dilatation `H`;
  Theorem 35.6 (35.13); Theorem 35.7 (35.14); Theorem 35.8 (Strebel's frame mapping criterion)
                                            — `IsHamiltonSequence`, `boundaryDilatation`, `thm35_6`,
                                              `thm35_7`, `thm35_8_strebel`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

/-! ## §35.1 Boundary behaviour of trajectories -/

/-- The norm `‖ω‖ = ∬_Δ |φ| dx dy` of a quadratic differential `φ dz²` in `Δ`. -/
def discQDNorm (φ : ℂ → ℂ) : ℝ≥0∞ := phiArea φ unitDisc

/-- The Banach space `A(Δ)` of holomorphic `φ` in `Δ` with `‖φ‖ = ∬_Δ |φ| < ∞`. -/
def integrableQD : Set (ℂ → ℂ) := {φ | DifferentiableOn ℂ φ unitDisc ∧ phiArea φ unitDisc < ⊤}

/-- §35.1: a ray `α⁺` of a non-critical horizontal trajectory of `φ dz²` in `Δ`, parametrized on
`(0, 1)` (increasing parameter, `c(t) → ∂Δ` as `t → 1`, i.e. `c` leaves every compact subset of
`Δ`); its initial point `c(0⁺)` is irrelevant. -/
def IsHorizontalRay (φ : ℂ → ℂ) (c : ℝ → ℂ) : Prop :=
  IsHorizontalArc φ c 0 1 ∧ c '' Ioo 0 1 ⊆ unitDisc ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in 𝓝[<] (1 : ℝ), c t ∉ K

/-- §35.1: a complete non-critical horizontal trajectory `α = α⁺ ∪ α⁻`, parametrized on `(0, 1)` and
leaving every compact subset of `Δ` at both ends. -/
def IsCompleteTrajectory (φ : ℂ → ℂ) (c : ℝ → ℂ) : Prop :=
  IsHorizontalArc φ c 0 1 ∧ c '' Ioo 0 1 ⊆ unitDisc ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc →
      (∀ᶠ t in 𝓝[<] (1 : ℝ), c t ∉ K) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), c t ∉ K

/-- The `φ`-length of the arc `c|(a, b)`. -/
def rayLength (φ : ℂ → ℂ) (c : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ

/-! ### Length–area estimates for quadratic differentials of finite norm in `Δ` -/

/-- The lower integral of a `2π`-periodic function over `(0, 2π)` equals the one over `(-π, π)`. -/
theorem lintegral_Ioo_zero_two_pi_eq_of_periodic {g : ℝ → ℝ≥0∞}
    (hg : Function.Periodic g (2 * π)) :
    ∫⁻ θ in Ioo 0 (2 * π), g θ = ∫⁻ θ in Ioo (-π) π, g θ := by
  haveI : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have h1 := AddCircle.lintegral_preimage (T := 2 * π) 0 hg.lift
  have h2 := AddCircle.lintegral_preimage (T := 2 * π) (-π) hg.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [zero_add] at h1
  rw [show -π + 2 * π = π by ring] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

/-- A function continuous on `Δ`, extended by `0`, is measurable. -/
theorem measurable_indicator_unitDisc_of_continuousOn {g : ℂ → ℝ≥0∞}
    (hg : ContinuousOn g unitDisc) : Measurable (unitDisc.indicator g) := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  rw [← Set.piecewise_eq_indicator]
  exact hg.measurable_piecewise continuousOn_const hD

/-- `(θ, r) ↦ c + r e^{iθ}` is continuous. -/
theorem continuous_circleMap_swap (c : ℂ) : Continuous fun p : ℝ × ℝ => circleMap c p.2 p.1 := by
  show Continuous fun p : ℝ × ℝ => c + (p.2 : ℂ) * exp ((p.1 : ℂ) * I)
  exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)))

/-- The polar integrand `(θ, r) ↦ r |φ(c + r e^{iθ})|` (extended by `0` off `Δ`) is measurable. -/
theorem measurable_polar_phi_integrand {φ : ℂ → ℂ} (hφ : ContinuousOn φ unitDisc) (c : ℂ) :
    Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.2 * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap c p.2 p.1) := by
  have hm : Measurable (unitDisc.indicator fun z => ENNReal.ofReal ‖φ z‖) :=
    measurable_indicator_unitDisc_of_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn hφ.norm)
  exact measurable_snd.ennreal_ofReal.mul (hm.comp (continuous_circleMap_swap c).measurable)

/-- `∬_Δ |φ|` in polar coordinates centred at an arbitrary point `c`. -/
theorem lintegral_polar_indicator_phiArea {φ : ℂ → ℂ} (hφ : ContinuousOn φ unitDisc) (c : ℂ) :
    ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap c r θ)
      = phiArea φ unitDisc := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hm : Measurable (unitDisc.indicator fun z => ENNReal.ofReal ‖φ z‖) :=
    measurable_indicator_unitDisc_of_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn hφ.norm)
  have h := lintegral_unitDisc_eq_polar c hm
  rw [Set.indicator_indicator, inter_self] at h
  rw [← h]
  unfold phiArea
  rw [← lintegral_indicator hD, Set.indicator_indicator, inter_self, lintegral_indicator hD]

/-- For `φ ∈ A(Δ)`, the radial integrals `∫₀¹ |φ(re^{iθ})| r dr` have finite integral over
`θ ∈ (0, 2π)`. -/
theorem lintegral_radial_phi_lt_top {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) :
    ∫⁻ θ in Ioo 0 (2 * π), ∫⁻ r in Ioo (0 : ℝ) 1,
      ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ) < ⊤ := by
  have hc : ContinuousOn φ unitDisc := hφ.1.continuousOn
  rw [lintegral_Ioo_zero_two_pi_eq_of_periodic ?_]
  swap
  · intro θ
    exact lintegral_congr fun r => by rw [periodic_circleMap 0 r θ]
  calc ∫⁻ θ in Ioo (-π) π, ∫⁻ r in Ioo (0 : ℝ) 1,
        ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ)
      = ∫⁻ r in Ioo (0 : ℝ) 1, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ) :=
        lintegral_lintegral_swap (measurable_polar_phi_integrand hc 0).aemeasurable
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ) :=
        lintegral_mono_set Ioo_subset_Ioi_self
    _ = phiArea φ unitDisc := lintegral_polar_indicator_phiArea hc 0
    _ < ⊤ := hφ.2

/-- (35.1): for `φ ∈ A(Δ)`, `∫₀¹ |φ(re^{iθ})|^{1/2} dr < ∞` for almost every `θ`: almost every radius
has finite `φ`-length (Schwarz's inequality applied to `∬ |φ|`). -/
theorem eq35_1_radii_finite_length {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) (2 * π))),
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖) < ⊤ := by
  have hA := lintegral_radial_phi_lt_top hφ
  have hc : ContinuousOn φ unitDisc := hφ.1.continuousOn
  have hHm : Measurable fun θ : ℝ => ∫⁻ r in Ioo (0 : ℝ) 1,
      ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ) :=
    (measurable_polar_phi_integrand hc 0).lintegral_prod_right'
  have hcm : ∀ r θ : ℝ, circleMap 0 r θ = (r : ℂ) * exp (θ * I) := fun r θ => zero_add _
  -- `φ` is bounded on `|z| ≤ 1/2`
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (hc.mono (closedBall_subset_ball (by norm_num)))
  filter_upwards [ae_lt_top hHm hA.ne] with θ hθ
  have hpt : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖)
      ≤ ENNReal.ofReal (1 + max M 0) + 2 * (ENNReal.ofReal r *
        unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ)) := by
    intro r hr
    have hnorm : ‖(r : ℂ) * exp (θ * I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr.1.le]
    have hz : circleMap 0 r θ ∈ unitDisc := by
      refine mem_ball_zero_iff.mpr ?_
      rw [hcm, hnorm]
      exact hr.2
    rw [indicator_of_mem hz]
    simp only [hcm]
    have hx0 : 0 ≤ ‖φ ((r : ℂ) * exp (θ * I))‖ := norm_nonneg _
    have hbound : ‖φ ((r : ℂ) * exp (θ * I))‖
        ≤ max M 0 + 2 * (r * ‖φ ((r : ℂ) * exp (θ * I))‖) := by
      by_cases hr2 : r ≤ 1 / 2
      · have hmem : (r : ℂ) * exp (θ * I) ∈ closedBall (0 : ℂ) (1 / 2) := by
          rw [mem_closedBall_zero_iff, hnorm]
          exact hr2
        have := hM _ hmem
        linarith [le_max_left M 0, mul_nonneg hr.1.le hx0]
      · replace hr2 : 1 / 2 < r := not_le.1 hr2
        nlinarith [le_max_right M 0, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 2 * r - 1)]
    have hsq : Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖ ≤ 1 + ‖φ ((r : ℂ) * exp (θ * I))‖ := by
      calc Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖
          ≤ Real.sqrt ((1 + ‖φ ((r : ℂ) * exp (θ * I))‖) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 + ‖φ ((r : ℂ) * exp (θ * I))‖ := Real.sqrt_sq (by linarith)
    have hrx : 0 ≤ 2 * (r * ‖φ ((r : ℂ) * exp (θ * I))‖) :=
      mul_nonneg zero_le_two (mul_nonneg hr.1.le hx0)
    calc ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖)
        ≤ ENNReal.ofReal (1 + max M 0 + 2 * (r * ‖φ ((r : ℂ) * exp (θ * I))‖)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
          rw [ENNReal.ofReal_add (by linarith [le_max_right M 0]) hrx,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hr.1.le,
            ENNReal.ofReal_ofNat]
  calc ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖φ ((r : ℂ) * exp (θ * I))‖)
      ≤ ∫⁻ r in Ioo (0 : ℝ) 1, (ENNReal.ofReal (1 + max M 0) + 2 * (ENNReal.ofReal r *
          unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hpt r hr
    _ = ENNReal.ofReal (1 + max M 0) * volume (Ioo (0 : ℝ) 1) + 2 * ∫⁻ r in Ioo (0 : ℝ) 1,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap 0 r θ) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const,
          lintegral_const_mul' _ _ (by norm_num)]
    _ < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
          ENNReal.mul_lt_top (by norm_num) hθ⟩

/-! ### Short circular arcs about a boundary point -/

/-- **Cauchy–Schwarz on a circle**: the `φ`-length `l(r)` of `Δ ∩ {|z - ζ| = r}` satisfies
`l(r)² ≤ 2π r · ∫_{-π}^{π} |φ(ζ + re^{iθ})| r dθ` (the integrand extended by `0` off `Δ`). -/
theorem sq_arc_phiLength_le {φ : ℂ → ℂ} (hφ : ContinuousOn φ unitDisc) (ζ : ℂ) (r : ℝ) :
    (∫⁻ θ in Ioo (0 : ℝ) (2 * π),
        unitDisc.indicator (fun z => phiDensity φ z) (circleMap ζ r θ) * ENNReal.ofReal r) ^ 2
      ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap ζ r θ) := by
  have hDm : Measurable (unitDisc.indicator fun z => phiDensity φ z) :=
    measurable_indicator_unitDisc_of_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hφ.norm))
  have hmeas : AEMeasurable (fun θ : ℝ =>
      unitDisc.indicator (fun z => phiDensity φ z) (circleMap ζ r θ) * ENNReal.ofReal r)
      (volume.restrict (Ioo (0 : ℝ) (2 * π))) :=
    ((hDm.comp (continuous_circleMap ζ r).measurable).mul_const _).aemeasurable
  have h1 := sq_lintegral_le_measure_univ_mul_lintegral_sq (volume.restrict (Ioo (0 : ℝ) (2 * π)))
    hmeas
  rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right (le_of_eq ?_) _
  rw [← lintegral_Ioo_zero_two_pi_eq_of_periodic ?_, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · refine lintegral_congr fun θ => ?_
    by_cases hz : circleMap ζ r θ ∈ unitDisc
    · simp only [indicator_of_mem hz, phiDensity]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _), sq]
      ring
    · simp [indicator_of_notMem hz]
  · intro θ
    simp only [periodic_circleMap ζ r θ]

/-- `∫₀^δ dr/r = ∞`. -/
theorem lintegral_Ioo_zero_inv_eq_top {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal r⁻¹ = ⊤ := by
  by_contra h
  have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo 0 δ) := by
    refine ⟨measurable_inv.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact lt_top_iff_ne_top.2 h
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact inv_nonneg.2 hr.1.le
  have hii : IntervalIntegrable (fun r : ℝ => r⁻¹) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le]
    exact hint
  rcases intervalIntegrable_inv_iff.1 hii with h0 | h0
  · exact hδ.ne h0
  · exact h0 Set.left_mem_uIcc

/-- **The length–area argument at a boundary point**: for every `ε, δ > 0` some circle
`|z - ζ| = r`, `r ∈ (0, δ)`, has `φ`-length `< ε` inside `Δ`. -/
theorem exists_arc_phiLength_lt {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (ζ : ℂ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ r ∈ Ioo 0 δ, ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
      unitDisc.indicator (fun z => phiDensity φ z) (circleMap ζ r θ) * ENNReal.ofReal r
        < ENNReal.ofReal ε := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hc : ContinuousOn φ unitDisc := hφ.1.continuousOn
  have hpt : ∀ r ∈ Ioo (0 : ℝ) δ, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal r⁻¹
      ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap ζ r θ) := by
    intro r hr
    have h := (pow_le_pow_left' (hcon r hr) 2).trans (sq_arc_phiLength_le hc ζ r)
    have hrr : ENNReal.ofReal r * ENNReal.ofReal r⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hr.1.le, mul_inv_cancel₀ hr.1.ne', ENNReal.ofReal_one]
    calc ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal r⁻¹
        = ENNReal.ofReal ε ^ 2 * ENNReal.ofReal r⁻¹ := by rw [ENNReal.ofReal_pow hε.le]
      _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal r * (∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖)
              (circleMap ζ r θ)) * ENNReal.ofReal r⁻¹ := mul_le_mul_left h _
      _ = ENNReal.ofReal (2 * π) * (∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖)
              (circleMap ζ r θ)) * (ENNReal.ofReal r * ENNReal.ofReal r⁻¹) := by ring
      _ = _ := by rw [hrr, mul_one]
  have hint : ∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal r⁻¹
      ≤ ENNReal.ofReal (2 * π) * phiArea φ unitDisc := by
    calc ∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal r⁻¹
        ≤ ∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖)
              (circleMap ζ r θ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact hpt r hr
      _ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioo (0 : ℝ) δ, ∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖)
              (circleMap ζ r θ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖)
              (circleMap ζ r θ) :=
          mul_le_mul_right (lintegral_mono_set Ioo_subset_Ioi_self) _
      _ = ENNReal.ofReal (2 * π) * phiArea φ unitDisc := by
          rw [lintegral_polar_indicator_phiArea hc ζ]
  have hleft : ∫⁻ r in Ioo (0 : ℝ) δ, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal r⁻¹ = ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioo_zero_inv_eq_top hδ]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (pow_pos hε 2)).ne'
  rw [hleft, top_le_iff] at hint
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφ.2.ne hint

/-- §35.1 (in the proof of Lemma 35.2): for `φ ∈ A(Δ)` and `ζ ∈ ∂Δ`,
`∫₀^{ρ₀} l_ω(Γ_r)²/r dr ≤ π² ∬_{Δ ∩ {|z-ζ| < ρ₀}} |φ| < ∞`, `Γ_r = Δ ∩ {|z - ζ| = r}`; hence there are
`rₙ → 0` with `l_ω(Γ_{rₙ}) → 0`. -/
theorem circular_arcs_short {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n < 1) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
        (unitDisc.indicator (fun z => phiDensity φ z) (ζ + r n * exp (θ * I))) * ENNReal.ofReal (r n)) atTop (𝓝 0) := by
  -- the position of `ζ` on `∂Δ` plays no role in the estimate
  have _ := hζ
  have hch : ∀ n : ℕ, ∃ ρ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 2)), ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
      unitDisc.indicator (fun z => phiDensity φ z) (circleMap ζ ρ θ) * ENNReal.ofReal ρ
        < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    exists_arc_phiLength_lt hφ ζ (by positivity) (by positivity)
  choose r hr hL using hch
  have hr1 : ∀ n : ℕ, r n < 1 / ((n : ℝ) + 1) := fun n =>
    (hr n).2.trans_le (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  refine ⟨r, fun n => ⟨(hr n).1, (hr1 n).trans_le (hle1 n)⟩, ?_, ?_⟩
  · exact squeeze_zero (fun n => (hr n).1.le) (fun n => (hr1 n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · have hlim := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ENNReal.ofReal_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      (fun n => (hL n).le)

/-- **(Optional) The geodesic property in S35's vocabulary**: `rayLength φ c a b ≤ phiLength φ β` for a
horizontal arc `c|[a, b]` in `Δ` and a curve `β` in `Δ` with the same end points (the input of
`lemma35_3` / `lemma35_2` together with `circular_arcs_short`). -/
theorem fx_arc_shortest_rayLength {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : IsHorizontalArc φ c a b) (hcc : ContinuousOn c (Icc a b)) (hcD : c '' Icc a b ⊆ unitDisc)
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (c a)))
    (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (c b))) :
    rayLength φ c a b ≤ phiLength φ β :=
  fx_arc_shortest hφ hne hab hc hcc hcD β hβ hβa hβb

/-- The `ρ`-length `∫_a^b ρ(f(t)) |f'(t)| dt` of `f|(a, b)`. -/
def a35_len (ρ : ℂ → ℝ≥0∞) (f : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a b, ρ (f t) * ‖deriv f t‖ₑ

/-- The derivative of `w ↦ f (k + m w)`. -/
theorem a35_deriv_affine (f : ℝ → ℂ) (k m u : ℝ) :
    deriv (fun w => f (k + m * w)) u = m • deriv f (k + m * u) := by
  have h := deriv_comp_mul_left m (fun w => f (k + w)) u
  rw [deriv_comp_const_add] at h
  exact h

/-- Affine change of variables for `a35_len`. -/
theorem a35_len_affine (ρ : ℂ → ℝ≥0∞) {f g : ℝ → ℂ} {k m p q : ℝ} (hm : 0 < m)
    (hfg : ∀ u ∈ Ioo p q, g =ᶠ[𝓝 u] fun w => f (k + m * w)) :
    a35_len ρ g p q = a35_len ρ f (k + m * p) (k + m * q) := by
  unfold a35_len
  have himg : (fun u : ℝ => k + m * u) '' Ioo p q = Ioo (k + m * p) (k + m * q) := by
    ext v
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨hv1, hv2⟩
      refine ⟨(v - k) / m, ⟨?_, ?_⟩, ?_⟩
      · rw [lt_div_iff₀ hm]; linarith
      · rw [div_lt_iff₀ hm]; linarith
      · field_simp; ring
  have hder : ∀ u ∈ Ioo p q, HasDerivWithinAt (fun u : ℝ => k + m * u) m (Ioo p q) u := by
    intro u _
    have h := ((hasDerivAt_id u).const_mul m).const_add k
    simp only [id, mul_one] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => k + m * u) (Ioo p q) := by
    intro x _ y _ h
    have h' : m * x = m * y := by simpa using h
    exact mul_left_cancel₀ hm.ne' h'
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hder hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have h1 : g u = f (k + m * u) := (hfg u hu).eq_of_nhds
  have h2 : deriv g u = m • deriv f (k + m * u) := by
    rw [(hfg u hu).deriv_eq, a35_deriv_affine]
  rw [h1, h2, enorm_smul, Real.enorm_eq_ofReal_abs]
  ring

/-- Gluing Lipschitz bounds on `[a, m]` and `[m, b]` into one on `[a, b]`. -/
theorem a35_lip_glue {f : ℝ → ℂ} {K : ℝ≥0} {a m b : ℝ} (h₁ : LipschitzOnWith K f (Icc a m))
    (h₂ : LipschitzOnWith K f (Icc m b)) (ham : a ≤ m) (hmb : m ≤ b) :
    LipschitzOnWith K f (Icc a b) := by
  have hmix : ∀ x ∈ Icc a m, ∀ y ∈ Icc m b, dist (f x) (f y) ≤ K * dist x y := by
    intro x hx y hy
    have hm1 : m ∈ Icc a m := ⟨ham, le_rfl⟩
    have hm2 : m ∈ Icc m b := ⟨le_rfl, hmb⟩
    calc dist (f x) (f y) ≤ dist (f x) (f m) + dist (f m) (f y) := dist_triangle _ _ _
      _ ≤ K * dist x m + K * dist m y := add_le_add (h₁.dist_le_mul x hx m hm1) (h₂.dist_le_mul m hm2 y hy)
      _ = K * dist x y := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hx.2]),
            abs_of_nonpos (by linarith [hy.1]), abs_of_nonpos (by linarith [hx.2, hy.1])]
          ring
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rcases le_total x m with hxm | hxm <;> rcases le_total y m with hym | hym
  · exact h₁.dist_le_mul x ⟨hx.1, hxm⟩ y ⟨hy.1, hym⟩
  · exact hmix x ⟨hx.1, hxm⟩ y ⟨hym, hy.2⟩
  · rw [dist_comm, dist_comm x]
    exact hmix y ⟨hy.1, hym⟩ x ⟨hxm, hx.2⟩
  · exact h₂.dist_le_mul x ⟨hxm, hx.2⟩ y ⟨hym, hy.2⟩

/-- A Lipschitz bound for `w ↦ f (k + m w)` on `[p, q]`. -/
theorem a35_lip_affine {f : ℝ → ℂ} {K : ℝ≥0} {S : Set ℝ} (hf : LipschitzOnWith K f S) {k m p q : ℝ}
    (hm : 0 ≤ m) (hS : ∀ w ∈ Icc p q, k + m * w ∈ S) :
    LipschitzOnWith (K * Real.toNNReal m) (fun w => f (k + m * w)) (Icc p q) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  refine (hf.dist_le_mul _ (hS x hx) _ (hS y hy)).trans (le_of_eq ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul, Real.coe_toNNReal _ hm,
    show k + m * x - (k + m * y) = m * (x - y) by ring, abs_mul, abs_of_nonneg hm]
  ring

/-- The concatenation of `X|[0, 1]` and `Y|[0, 1]`, parametrized on `[0, 1]`. -/
def a35_join (X Y : ℝ → ℂ) (u : ℝ) : ℂ := if u ≤ 1 / 2 then X (0 + 2 * u) else Y (-1 + 2 * u)

/-- The concatenation agrees with `X (2u)` for `u ≤ 1/2` and (when `X 1 = Y 0`) with `Y (2u - 1)` for
`u ≥ 1/2`. -/
theorem a35_join_eq {X Y : ℝ → ℂ} (hXY : X 1 = Y 0) :
    (∀ u ≤ 1 / 2, a35_join X Y u = X (0 + 2 * u)) ∧ ∀ u, 1 / 2 ≤ u → a35_join X Y u = Y (-1 + 2 * u) := by
  refine ⟨fun u hu => by simp only [a35_join, hu, ite_true], fun u hu => ?_⟩
  rcases hu.lt_or_eq with hu | hu
  · simp only [a35_join, not_le.2 hu, ite_false]
  · subst hu
    simp only [a35_join, le_refl, ite_true]
    norm_num
    exact hXY

/-- Properties of the concatenation of two Lipschitz paths. -/
theorem a35_join_props {X Y : ℝ → ℂ} (hXY : X 1 = Y 0) (hX : ∃ K, LipschitzOnWith K X (Icc 0 1))
    (hY : ∃ K, LipschitzOnWith K Y (Icc 0 1)) :
    (∃ K, LipschitzOnWith K (a35_join X Y) (Icc 0 1)) ∧ a35_join X Y 0 = X 0 ∧ a35_join X Y 1 = Y 1 ∧
      a35_join X Y '' Icc 0 1 ⊆ X '' Icc 0 1 ∪ Y '' Icc 0 1 ∧
      ∀ ρ, a35_len ρ (a35_join X Y) 0 1 ≤ a35_len ρ X 0 1 + a35_len ρ Y 0 1 := by
  obtain ⟨hL, hR⟩ := a35_join_eq hXY
  obtain ⟨K₁, hK₁⟩ := hX
  obtain ⟨K₂, hK₂⟩ := hY
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(K₁ + K₂) * Real.toNNReal 2, a35_lip_glue (m := 1 / 2) ?_ ?_ (by norm_num) (by norm_num)⟩
    · have h := a35_lip_affine (k := 0) (m := 2) (p := 0) (q := 1 / 2)
        (hK₁.weaken (le_self_add : K₁ ≤ K₁ + K₂)) (by norm_num)
        (fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩)
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [hL x hx.2, hL y hy.2]
      exact h.dist_le_mul x hx y hy
    · have h := a35_lip_affine (k := -1) (m := 2) (p := 1 / 2) (q := 1)
        (hK₂.weaken (le_add_self : K₂ ≤ K₁ + K₂)) (by norm_num)
        (fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩)
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [hR x hx.1, hR y hy.1]
      exact h.dist_le_mul x hx y hy
  · rw [hL 0 (by norm_num)]
    norm_num
  · rw [hR 1 (by norm_num)]
    norm_num
  · rintro _ ⟨u, hu, rfl⟩
    rcases le_total u (1 / 2) with h | h
    · left
      rw [hL u h]
      exact ⟨0 + 2 * u, ⟨by linarith [hu.1], by linarith⟩, rfl⟩
    · right
      rw [hR u h]
      exact ⟨-1 + 2 * u, ⟨by linarith, by linarith [hu.2]⟩, rfl⟩
  · intro ρ
    have e1 := a35_len_affine ρ (f := X) (g := a35_join X Y) (k := 0) (m := 2) (p := 0) (q := 1 / 2)
      (by norm_num) fun u hu => Filter.eventually_of_mem (Iio_mem_nhds hu.2) fun w hw => hL w (le_of_lt hw)
    have e2 := a35_len_affine ρ (f := Y) (g := a35_join X Y) (k := -1) (m := 2) (p := 1 / 2) (q := 1)
      (by norm_num) fun u hu => Filter.eventually_of_mem (Ioi_mem_nhds hu.1) fun w hw => hR w (le_of_lt hw)
    rw [show (0 : ℝ) + 2 * 0 = 0 by norm_num, show (0 : ℝ) + 2 * (1 / 2) = 1 by norm_num] at e1
    rw [show (-1 : ℝ) + 2 * (1 / 2) = 0 by norm_num, show (-1 : ℝ) + 2 * 1 = 1 by norm_num] at e2
    unfold a35_len at e1 e2 ⊢
    calc ∫⁻ t in Ioo 0 1, ρ (a35_join X Y t) * ‖deriv (a35_join X Y) t‖ₑ
        ≤ ∫⁻ t in Ioo 0 (1 / 2) ∪ ({1 / 2} ∪ Ioo (1 / 2) 1),
            ρ (a35_join X Y t) * ‖deriv (a35_join X Y) t‖ₑ := by
          refine lintegral_mono_set fun t ht => ?_
          rcases lt_trichotomy t (1 / 2) with h | h | h
          · exact Or.inl ⟨ht.1, h⟩
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨h, ht.2⟩)
      _ ≤ _ + (_ + _) := (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
      _ = _ := by rw [setLIntegral_measure_zero _ _ (Real.volume_singleton), zero_add, e1, e2]

/-- The lower integral of a `2π`-periodic function over `(α - π, α + π)` equals the one over
`(0, 2π)`. -/
theorem a35_lintegral_periodic {g : ℝ → ℝ≥0∞} (hg : Function.Periodic g (2 * π)) (α : ℝ) :
    ∫⁻ θ in Ioo (α - π) (α + π), g θ = ∫⁻ θ in Ioo 0 (2 * π), g θ := by
  have hfact : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have h1 := AddCircle.lintegral_preimage (T := 2 * π) 0 hg.lift
  have h2 := AddCircle.lintegral_preimage (T := 2 * π) (α - π) hg.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [zero_add] at h1
  rw [show α - π + 2 * π = α + π by ring] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

/-- The circular arc `v ↦ ζ + r e^{i(arg(-ζ) + (1 - v)ψ₁ + vψ₂)}` about `ζ`. -/
def a35_arc (ζ : ℂ) (r ψ₁ ψ₂ : ℝ) (v : ℝ) : ℂ :=
  ζ + r * exp (((arg (-ζ) + ((1 - v) * ψ₁ + v * ψ₂) : ℝ) : ℂ) * I)

/-- `e^{i arg(-ζ)} = -ζ` for `|ζ| = 1`. -/
theorem a35_exp_arg_neg {ζ : ℂ} (hζ : ‖ζ‖ = 1) : exp ((arg (-ζ) : ℂ) * I) = -ζ := by
  have h := norm_mul_exp_arg_mul_I (-ζ)
  rw [norm_neg, hζ, ofReal_one, one_mul] at h
  exact h

/-- `|ζ + r e^{i(arg(-ζ) + ψ)}|² = 1 - 2r cos ψ + r²` for `|ζ| = 1`. -/
theorem a35_circle_normSq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r ψ : ℝ) :
    ‖ζ + r * exp (((arg (-ζ) + ψ : ℝ) : ℂ) * I)‖ ^ 2 = 1 - 2 * r * Real.cos ψ + r ^ 2 := by
  have h2 : ζ + r * exp (((arg (-ζ) + ψ : ℝ) : ℂ) * I) = ζ * (1 - r * exp ((ψ : ℂ) * I)) := by
    rw [ofReal_add, add_mul, exp_add, a35_exp_arg_neg hζ]
    ring
  rw [h2, norm_mul, hζ, one_mul, Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
    sub_im, one_im, mul_im]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq ψ

/-- Points of the arc lie in `Δ`. -/
theorem a35_arc_mem {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r ψ₁ ψ₂ : ℝ} (hr : 0 < r)
    (hψ₁ : ψ₁ ∈ Icc (-(π / 2)) (π / 2)) (hψ₂ : ψ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hc₁ : r < 2 * Real.cos ψ₁) (hc₂ : r < 2 * Real.cos ψ₂) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    a35_arc ζ r ψ₁ ψ₂ v ∈ unitDisc := by
  have hcv := strictConcaveOn_cos_Icc.concaveOn.2 hψ₁ hψ₂ (sub_nonneg.2 hv.2) hv.1 (by ring)
  simp only [smul_eq_mul] at hcv
  have hn := a35_circle_normSq hζ r ((1 - v) * ψ₁ + v * ψ₂)
  set δ := min (2 * Real.cos ψ₁ - r) (2 * Real.cos ψ₂ - r) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hm1 := mul_le_mul_of_nonneg_left (min_le_left (2 * Real.cos ψ₁ - r) (2 * Real.cos ψ₂ - r))
    (sub_nonneg.2 hv.2)
  have hm2 := mul_le_mul_of_nonneg_left (min_le_right (2 * Real.cos ψ₁ - r) (2 * Real.cos ψ₂ - r)) hv.1
  have hcos : r < 2 * Real.cos ((1 - v) * ψ₁ + v * ψ₂) := by nlinarith
  rw [unitDisc, mem_ball_zero_iff]
  unfold a35_arc
  have h2 : ‖ζ + r * exp (((arg (-ζ) + ((1 - v) * ψ₁ + v * ψ₂) : ℝ) : ℂ) * I)‖ ^ 2 < 1 := by
    rw [hn]
    nlinarith
  nlinarith [norm_nonneg (ζ + r * exp (((arg (-ζ) + ((1 - v) * ψ₁ + v * ψ₂) : ℝ) : ℂ) * I))]

/-- A point of `Δ` on the circle `|z - ζ| = r` is `ζ + r e^{i(arg(-ζ) + ψ)}` with `|ψ| ≤ π/2` and
`r < 2 cos ψ`. -/
theorem a35_arc_rep {ζ p : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hp : ‖p - ζ‖ = r)
    (hpD : p ∈ unitDisc) :
    ∃ ψ ∈ Icc (-(π / 2)) (π / 2), r < 2 * Real.cos ψ ∧
      ζ + r * exp (((arg (-ζ) + ψ : ℝ) : ℂ) * I) = p := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  set w : ℂ := (p - ζ) / (r * -ζ) with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_div, norm_mul, norm_neg, hζ, hp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, mul_one, div_self hr.ne']
  have hexp : exp ((arg w : ℂ) * I) = w := by
    have h := norm_mul_exp_arg_mul_I w
    rw [hwn, ofReal_one, one_mul] at h
    exact h
  have heq : ζ + r * exp (((arg (-ζ) + arg w : ℝ) : ℂ) * I) = p := by
    rw [ofReal_add, add_mul, exp_add, a35_exp_arg_neg hζ, hexp, hw]
    field_simp
    ring
  have hn := a35_circle_normSq hζ r (arg w)
  rw [heq] at hn
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.1 hpD
  have hcos : r < 2 * Real.cos (arg w) := by nlinarith [norm_nonneg p]
  refine ⟨arg w, ⟨?_, ?_⟩, hcos, heq⟩
  · by_contra h
    have h' := not_le.1 h
    have : Real.cos (arg w) ≤ 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [neg_pi_lt_arg w])
    linarith
  · by_contra h
    have h' := not_le.1 h
    have : Real.cos (arg w) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h'.le (by linarith [arg_le_pi w])
    linarith

/-- The derivative of the arc. -/
theorem a35_arc_hasDerivAt (ζ : ℂ) (r ψ₁ ψ₂ v : ℝ) :
    HasDerivAt (a35_arc ζ r ψ₁ ψ₂)
      (r * exp (((arg (-ζ) + ((1 - v) * ψ₁ + v * ψ₂) : ℝ) : ℂ) * I) * ((ψ₂ - ψ₁ : ℝ) * I)) v := by
  have h1 : HasDerivAt (fun v : ℝ => arg (-ζ) + ((1 - v) * ψ₁ + v * ψ₂)) (ψ₂ - ψ₁) v := by
    have h := ((hasDerivAt_id' v).mul_const (ψ₂ - ψ₁)).const_add (arg (-ζ) + ψ₁)
    convert h using 1
    · ext v
      ring
    · ring
  have h2 := ((h1.ofReal_comp.mul_const I).cexp.const_mul (r : ℂ)).const_add ζ
  convert h2 using 1
  · rfl
  · ring

/-- The speed of the arc: `|A'(v)| = |r| |ψ₂ - ψ₁|`. -/
theorem a35_arc_deriv_norm (ζ : ℂ) (r ψ₁ ψ₂ v : ℝ) :
    ‖deriv (a35_arc ζ r ψ₁ ψ₂) v‖ = |r| * |ψ₂ - ψ₁| := by
  rw [(a35_arc_hasDerivAt ζ r ψ₁ ψ₂ v).deriv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, norm_I, Real.norm_eq_abs, Real.norm_eq_abs]
  ring

/-- The arc is Lipschitz on `[0, 1]`. -/
theorem a35_arc_lip (ζ : ℂ) (r ψ₁ ψ₂ : ℝ) : ∃ K, LipschitzOnWith K (a35_arc ζ r ψ₁ ψ₂) (Icc 0 1) := by
  refine ⟨Real.toNNReal (|r| * |ψ₂ - ψ₁|), (lipschitzWith_of_nnnorm_deriv_le
    (fun v => (a35_arc_hasDerivAt ζ r ψ₁ ψ₂ v).differentiableAt) fun v => ?_).lipschitzOnWith⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity), a35_arc_deriv_norm]

/-- The `ρ`-length of an arc in `Δ` is at most the `ρ`-length of `Δ ∩ {|z - ζ| = r}`. -/
theorem a35_arc_len {ζ : ℂ} {r ψ₁ ψ₂ : ℝ} (hr : 0 < r)
    (hψ₁ : ψ₁ ∈ Icc (-(π / 2)) (π / 2)) (hψ₂ : ψ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hD : ∀ v ∈ Ioo (0 : ℝ) 1, a35_arc ζ r ψ₁ ψ₂ v ∈ unitDisc) (ρ : ℂ → ℝ≥0∞) :
    a35_len ρ (a35_arc ζ r ψ₁ ψ₂) 0 1 ≤ ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
      unitDisc.indicator ρ (ζ + r * exp (θ * I)) * ENNReal.ofReal r := by
  set g : ℝ → ℝ≥0∞ := fun θ => unitDisc.indicator ρ (ζ + r * exp (θ * I)) * ENNReal.ofReal r with hg
  have hE : ∀ θ : ℝ, exp (((θ + 2 * π : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) := by
    intro θ
    push_cast
    rw [add_mul, exp_add, exp_two_pi_mul_I, mul_one]
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    show unitDisc.indicator ρ (ζ + r * exp (((θ + 2 * π : ℝ) : ℂ) * I)) * ENNReal.ofReal r = _
    rw [hE]
  set α := arg (-ζ) with hα
  set θf : ℝ → ℝ := fun v => α + ((1 - v) * ψ₁ + v * ψ₂) with hθf
  have hint : ∀ v ∈ Ioo (0 : ℝ) 1, ρ (a35_arc ζ r ψ₁ ψ₂ v) * ‖deriv (a35_arc ζ r ψ₁ ψ₂) v‖ₑ
      = ENNReal.ofReal |ψ₂ - ψ₁| * g (θf v) := by
    intro v hv
    have hmem := hD v hv
    rw [← ofReal_norm, a35_arc_deriv_norm, abs_of_pos hr, ENNReal.ofReal_mul hr.le]
    show _ = _ * (unitDisc.indicator ρ (a35_arc ζ r ψ₁ ψ₂ v) * _)
    rw [indicator_of_mem hmem]
    ring
  rcases eq_or_ne ψ₁ ψ₂ with h | h
  · have h0 : a35_len ρ (a35_arc ζ r ψ₁ ψ₂) 0 1 = 0 := by
      unfold a35_len
      rw [setLIntegral_congr_fun measurableSet_Ioo hint]
      simp [h]
    rw [h0]
    exact zero_le
  · have hder : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt θf (ψ₂ - ψ₁) (Ioo 0 1) v := by
      intro v _
      have h' := ((hasDerivAt_id' v).mul_const (ψ₂ - ψ₁)).const_add (α + ψ₁)
      have h'' : HasDerivAt θf (ψ₂ - ψ₁) v := by
        convert h' using 1
        · ext v
          simp only [hθf]
          ring
        · ring
      exact h''.hasDerivWithinAt
    have hinj : InjOn θf (Ioo 0 1) := by
      intro x _ y _ hxy
      simp only [hθf] at hxy
      have h2 : (x - y) * (ψ₂ - ψ₁) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · exact absurd (by linarith : ψ₁ = ψ₂) h
    have himg : θf '' Ioo 0 1 ⊆ Ioo (α - π) (α + π) := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 := mul_le_mul_of_nonneg_left hψ₁.1 (sub_nonneg.2 hv.2.le)
      have h2 := mul_le_mul_of_nonneg_left hψ₂.1 hv.1.le
      have h3 := mul_le_mul_of_nonneg_left hψ₁.2 (sub_nonneg.2 hv.2.le)
      have h4 := mul_le_mul_of_nonneg_left hψ₂.2 hv.1.le
      have hπ := Real.pi_pos
      simp only [hθf]
      constructor <;> nlinarith
    calc a35_len ρ (a35_arc ζ r ψ₁ ψ₂) 0 1
        = ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal |ψ₂ - ψ₁| * g (θf v) :=
          setLIntegral_congr_fun measurableSet_Ioo hint
      _ = ∫⁻ θ in θf '' Ioo 0 1, g θ :=
          (lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hder hinj g).symm
      _ ≤ ∫⁻ θ in Ioo (α - π) (α + π), g θ := lintegral_mono_set himg
      _ = _ := a35_lintegral_periodic hper α

/-- Two points of `Δ` on the circle `|z - ζ| = r` (`|ζ| = 1`) are joined in `Δ` by a Lipschitz path
whose `ρ`-length is at most the `ρ`-length of `Δ ∩ {|z - ζ| = r}`. -/
theorem a35_arc_exists {ζ p q : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hp : ‖p - ζ‖ = r)
    (hq : ‖q - ζ‖ = r) (hpD : p ∈ unitDisc) (hqD : q ∈ unitDisc) :
    ∃ A : ℝ → ℂ, (∃ K, LipschitzOnWith K A (Icc 0 1)) ∧ A 0 = p ∧ A 1 = q ∧
      A '' Icc 0 1 ⊆ unitDisc ∧ ∀ ρ : ℂ → ℝ≥0∞, a35_len ρ A 0 1 ≤ ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
        unitDisc.indicator ρ (ζ + r * exp (θ * I)) * ENNReal.ofReal r := by
  obtain ⟨ψ₁, hψ₁, hc₁, rfl⟩ := a35_arc_rep hζ hr hp hpD
  obtain ⟨ψ₂, hψ₂, hc₂, rfl⟩ := a35_arc_rep hζ hr hq hqD
  have hmem : ∀ v ∈ Icc (0 : ℝ) 1, a35_arc ζ r ψ₁ ψ₂ v ∈ unitDisc := fun v hv =>
    a35_arc_mem hζ hr hψ₁ hψ₂ hc₁ hc₂ hv
  refine ⟨a35_arc ζ r ψ₁ ψ₂, a35_arc_lip ζ r ψ₁ ψ₂, ?_, ?_, ?_,
    fun ρ => a35_arc_len hr hψ₁ hψ₂ (fun v hv => hmem v (Ioo_subset_Icc_self hv)) ρ⟩
  · simp [a35_arc]
  · simp [a35_arc]
  · rintro _ ⟨v, hv, rfl⟩
    exact hmem v hv

/-- A point of `Δ` has positive distance from a point of `∂Δ`. -/
theorem a35_dist_pos {x ζ : ℂ} (hx : x ∈ unitDisc) (hζ : ‖ζ‖ = 1) : 0 < ‖x - ζ‖ := by
  rw [unitDisc, mem_ball_zero_iff] at hx
  have h := norm_sub_norm_le ζ x
  rw [norm_sub_rev] at h
  linarith

/-- A path in `Δ` that tends to `ζ` while leaving every compact subset of `Δ` ends on `∂Δ`. -/
theorem a35_norm_eq_one {c : ℝ → ℂ} {F : Filter ℝ} [F.NeBot] {ζ : ℂ}
    (hin : ∀ᶠ t in F, c t ∈ unitDisc)
    (hK : ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in F, c t ∉ K)
    (h : Tendsto c F (𝓝 ζ)) : ‖ζ‖ = 1 := by
  have hle : ‖ζ‖ ≤ 1 := by
    have hcl : ζ ∈ closedBall (0 : ℂ) 1 :=
      isClosed_closedBall.mem_of_tendsto h (hin.mono fun t ht => ball_subset_closedBall ht)
    simpa using hcl
  by_contra hne
  have hlt : ‖ζ‖ < 1 := lt_of_le_of_ne hle hne
  have hεpos : 0 < (1 - ‖ζ‖) / 2 := by linarith
  have hsub : closedBall ζ ((1 - ‖ζ‖) / 2) ⊆ unitDisc := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [unitDisc, mem_ball_zero_iff]
    have h' := norm_sub_norm_le z ζ
    linarith
  have h1 := hK _ (isCompact_closedBall ζ _) hsub
  have h2 : ∀ᶠ t in F, c t ∈ closedBall ζ ((1 - ‖ζ‖) / 2) := h (closedBall_mem_nhds ζ hεpos)
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ht1 ht2

/-- A horizontal arc has positive `φ`-length on every non-degenerate subinterval of `(0, 1)`. -/
theorem a35_rayLength_pos {φ : ℂ → ℂ} (hφ : ContinuousOn φ unitDisc) {c : ℝ → ℂ}
    (hH : IsHorizontalArc φ c 0 1) (hD : c '' Ioo 0 1 ⊆ unitDisc) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) : 0 < rayLength φ c a b := by
  have hsub : Ioo a b ⊆ Ioo 0 1 := Ioo_subset_Ioo ha hb
  have hcc : ContinuousOn c (Ioo a b) := fun t ht =>
    (hH t (hsub ht)).1.continuousAt.continuousWithinAt
  have hρ : ContinuousOn (fun t => phiDensity φ (c t)) (Ioo a b) := by
    have h1 : ContinuousOn (fun t => φ (c t)) (Ioo a b) :=
      hφ.comp hcc fun t ht => hD (mem_image_of_mem c (hsub ht))
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn h1.norm)
  have hmeas : AEMeasurable (fun t => phiDensity φ (c t) * ‖deriv c t‖ₑ)
      (volume.restrict (Ioo a b)) :=
    (hρ.aemeasurable measurableSet_Ioo).mul (measurable_deriv c).enorm.aemeasurable
  have hpos : ∀ t ∈ Ioo a b, 0 < phiDensity φ (c t) * ‖deriv c t‖ₑ := by
    intro t ht
    obtain ⟨_, hd0, hφ0, _, _⟩ := hH t (hsub ht)
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (norm_pos_iff.2 hφ0))).ne'
    · exact (enorm_pos.2 hd0).ne'
  unfold rayLength
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff' hmeas]
  intro h0
  have h1 : ∀ᵐ t ∂volume, t ∈ Ioo a b → phiDensity φ (c t) * ‖deriv c t‖ₑ = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).1 h0
  have h2 : volume (Ioo a b) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h1] with t ht htab
    exact (hpos t htab).ne' (ht htab)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h2
  linarith

/-- A path continuous on `(0, x₀]` and tending to `ζ` at `0` meets every circle `|z - ζ| = r` with
`0 < r ≤ |f(x₀) - ζ|` at some time in `(0, x₀]`. -/
theorem a35_cross_left {f : ℝ → ℂ} {ζ : ℂ} {r x₀ : ℝ} (hx₀ : 0 < x₀) (hf : ContinuousOn f (Ioc 0 x₀))
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 ζ)) (hr : 0 < r) (hx : r ≤ ‖f x₀ - ζ‖) :
    ∃ x ∈ Ioc 0 x₀, ‖f x - ζ‖ = r := by
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖f t - ζ‖ < r :=
    (hlim.eventually (ball_mem_nhds ζ hr)).mono fun t ht => by rwa [dist_eq_norm] at ht
  obtain ⟨t, ht1, ht2⟩ := (h1.and (Ioo_mem_nhdsGT hx₀)).exists
  have hg : ContinuousOn (fun s => ‖f s - ζ‖) (Icc t x₀) :=
    ((hf.mono fun s (hs : s ∈ Icc t x₀) => ⟨ht2.1.trans_le hs.1, hs.2⟩).sub continuousOn_const).norm
  obtain ⟨x, hx', hxr⟩ := intermediate_value_Icc ht2.2.le hg ⟨ht1.le, hx⟩
  exact ⟨x, ⟨ht2.1.trans_le hx'.1, hx'.2⟩, hxr⟩

/-- A path continuous on `[x₀, 1)` and tending to `ζ` at `1` meets every circle `|z - ζ| = r` with
`0 < r ≤ |f(x₀) - ζ|` at some time in `[x₀, 1)`. -/
theorem a35_cross_right {f : ℝ → ℂ} {ζ : ℂ} {r x₀ : ℝ} (hx₀ : x₀ < 1) (hf : ContinuousOn f (Ico x₀ 1))
    (hlim : Tendsto f (𝓝[<] 1) (𝓝 ζ)) (hr : 0 < r) (hx : r ≤ ‖f x₀ - ζ‖) :
    ∃ x ∈ Ico x₀ 1, ‖f x - ζ‖ = r := by
  have h1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), ‖f t - ζ‖ < r :=
    (hlim.eventually (ball_mem_nhds ζ hr)).mono fun t ht => by rwa [dist_eq_norm] at ht
  obtain ⟨t, ht1, ht2⟩ := (h1.and (Ioo_mem_nhdsLT hx₀)).exists
  have hg : ContinuousOn (fun s => ‖f s - ζ‖) (Icc x₀ t) :=
    ((hf.mono fun s (hs : s ∈ Icc x₀ t) => ⟨hs.1, hs.2.trans_lt ht2.2⟩).sub continuousOn_const).norm
  obtain ⟨x, hx', hxr⟩ := intermediate_value_Icc' ht2.1.le hg ⟨ht1.le, hx⟩
  exact ⟨x, ⟨hx'.1, hx'.2.trans_lt ht2.2⟩, hxr⟩

/-- A path Lipschitz on `[0, 1]` is locally Lipschitz on `(0, 1)` and tends to its end values. -/
theorem a35_lip_curve {X : ℝ → ℂ} (hX : ∃ K, LipschitzOnWith K X (Icc 0 1)) :
    LocallyLipschitzOn (Ioo 0 1) X ∧ Tendsto X (𝓝[>] 0) (𝓝 (X 0)) ∧
      Tendsto X (𝓝[<] 1) (𝓝 (X 1)) := by
  obtain ⟨K, hK⟩ := hX
  have hc := hK.continuousOn
  refine ⟨fun x hx => ⟨K, Icc 0 1, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), hK⟩, ?_, ?_⟩
  · exact (hc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Ioo_subset_Icc_self)
  · exact (hc 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Icc_self)

/-- A horizontal arc on `(0, 1)` inside `Δ` restricts to every `[a, b] ⊆ (0, 1)`. -/
theorem a35_sub_arc {φ : ℂ → ℂ} {c : ℝ → ℂ} (hH : IsHorizontalArc φ c 0 1)
    (hD : c '' Ioo 0 1 ⊆ unitDisc) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IsHorizontalArc φ c a b ∧ ContinuousOn c (Icc a b) ∧ c '' Icc a b ⊆ unitDisc := by
  have hsub : Icc a b ⊆ Ioo 0 1 := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  exact ⟨fun t ht => hH t (hsub (Ioo_subset_Icc_self ht)),
    fun t ht => (hH t (hsub ht)).1.continuousAt.continuousWithinAt, (image_mono hsub).trans hD⟩

/-- The key estimate behind Lemma 35.3: for `[a₀, b₀] ⊆ (0, 1)`, `l_φ(c|[a₀, b₀]) ≤ l_φ(β)`.  Close
`β` up with two short circular arcs about `ζ₁`, `ζ₂` to a curve from `c(a)` to `c(b)`, `a ≤ a₀`,
`b ≥ b₀`, and apply the geodesic property. -/
theorem a35_key {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ}
    (hH : IsHorizontalArc φ c 0 1) (hD : c '' Ioo 0 1 ⊆ unitDisc) {ζ₁ ζ₂ : ℂ} (hζ₁ : ‖ζ₁‖ = 1)
    (hζ₂ : ‖ζ₂‖ = 1) (h₁ : Tendsto c (𝓝[>] 0) (𝓝 ζ₁)) (h₂ : Tendsto c (𝓝[<] 1) (𝓝 ζ₂))
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) (hβ₁ : Tendsto β.toFun (𝓝[>] 0) (𝓝 ζ₁))
    (hβ₂ : Tendsto β.toFun (𝓝[<] 1) (𝓝 ζ₂)) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (hb₀ : b₀ < 1) : rayLength φ c a₀ b₀ ≤ phiLength φ β := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hε.ne')
  have hcont : ContinuousOn c (Ioo 0 1) := fun t ht => (hH t ht).1.continuousAt.continuousWithinAt
  have hβc : ContinuousOn β.toFun (Ioo 0 1) := β.locallyLipschitzOn.continuousOn
  have hsub₀ : Icc a₀ b₀ ⊆ Ioo 0 1 := fun t ht => ⟨ha₀.trans_le ht.1, ht.2.trans_lt hb₀⟩
  have hne₀ : (Icc a₀ b₀).Nonempty := nonempty_Icc.2 hab₀.le
  obtain ⟨t₁, ht₁, hmin₁⟩ := isCompact_Icc.exists_isMinOn hne₀
    (((hcont.mono hsub₀).sub (continuousOn_const (c := ζ₁))).norm)
  obtain ⟨t₂, ht₂, hmin₂⟩ := isCompact_Icc.exists_isMinOn hne₀
    (((hcont.mono hsub₀).sub (continuousOn_const (c := ζ₂))).norm)
  have hhalf : β.toFun (1 / 2) ∈ unitDisc := hβ (mem_image_of_mem _ ⟨by norm_num, by norm_num⟩)
  have hm₁ : 0 < min ‖c t₁ - ζ₁‖ ‖β.toFun (1 / 2) - ζ₁‖ :=
    lt_min (a35_dist_pos (hD (mem_image_of_mem c (hsub₀ ht₁))) hζ₁) (a35_dist_pos hhalf hζ₁)
  have hm₂ : 0 < min ‖c t₂ - ζ₂‖ ‖β.toFun (1 / 2) - ζ₂‖ :=
    lt_min (a35_dist_pos (hD (mem_image_of_mem c (hsub₀ ht₂))) hζ₂) (a35_dist_pos hhalf hζ₂)
  obtain ⟨r, hr, hr0, hLr⟩ := circular_arcs_short hφ hζ₁
  obtain ⟨r', hr', hr0', hLr'⟩ := circular_arcs_short hφ hζ₂
  obtain ⟨n, hn1, hn2⟩ :=
    ((hr0.eventually (gt_mem_nhds hm₁)).and (hLr.eventually (gt_mem_nhds hε2))).exists
  obtain ⟨n', hn1', hn2'⟩ :=
    ((hr0'.eventually (gt_mem_nhds hm₂)).and (hLr'.eventually (gt_mem_nhds hε2))).exists
  -- the crossings of `c` and of `β` with the two circles
  obtain ⟨a, ha, har⟩ := a35_cross_left (f := c) ha₀
    (hcont.mono fun t ht => ⟨ht.1, ht.2.trans_lt (hab₀.trans hb₀)⟩) h₁ (hr n).1
    (hn1.le.trans ((min_le_left _ _).trans (isMinOn_iff.1 hmin₁ a₀ ⟨le_rfl, hab₀.le⟩)))
  obtain ⟨b, hb, hbr⟩ := a35_cross_right (f := c) hb₀
    (hcont.mono fun t ht => ⟨(ha₀.trans hab₀).trans_le ht.1, ht.2⟩) h₂ (hr' n').1
    (hn1'.le.trans ((min_le_left _ _).trans (isMinOn_iff.1 hmin₂ b₀ ⟨hab₀.le, le_rfl⟩)))
  obtain ⟨s, hs, hsr⟩ := a35_cross_left (f := β.toFun) (x₀ := 1 / 2) (by norm_num)
    (hβc.mono fun t ht => ⟨ht.1, by linarith [ht.2]⟩) hβ₁ (hr n).1 (hn1.le.trans (min_le_right _ _))
  obtain ⟨t, ht, htr⟩ := a35_cross_right (f := β.toFun) (x₀ := 1 / 2) (by norm_num)
    (hβc.mono fun t ht => ⟨by linarith [ht.1], ht.2⟩) hβ₂ (hr' n').1 (hn1'.le.trans (min_le_right _ _))
  have hst : s < t := by
    rcases hs.2.lt_or_eq with h | h
    · exact h.trans_le ht.1
    · exfalso
      rw [h] at hsr
      linarith [min_le_right ‖c t₁ - ζ₁‖ ‖β.toFun (1 / 2) - ζ₁‖]
  have hca : c a ∈ unitDisc := hD (mem_image_of_mem c ⟨ha.1, ha.2.trans_lt (hab₀.trans hb₀)⟩)
  have hcb : c b ∈ unitDisc := hD (mem_image_of_mem c ⟨(ha₀.trans hab₀).trans_le hb.1, hb.2⟩)
  have hβs : β.toFun s ∈ unitDisc := hβ (mem_image_of_mem _ ⟨hs.1, by linarith [hs.2]⟩)
  have hβt : β.toFun t ∈ unitDisc := hβ (mem_image_of_mem _ ⟨by linarith [ht.1], ht.2⟩)
  -- the three pieces
  obtain ⟨A₁, hA₁lip, hA₁0, hA₁1, hA₁D, hA₁len⟩ := a35_arc_exists hζ₁ (hr n).1 har hsr hca hβs
  obtain ⟨A₂, hA₂lip, hA₂0, hA₂1, hA₂D, hA₂len⟩ := a35_arc_exists hζ₂ (hr' n').1 htr hbr hβt hcb
  have hsub_st : Icc s t ⊆ Ioo 0 1 := fun x hx => ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
  have hst' : ∀ w ∈ Icc (0 : ℝ) 1, s + (t - s) * w ∈ Icc s t := fun w hw =>
    ⟨by nlinarith [mul_nonneg (sub_nonneg.2 hst.le) hw.1],
      by nlinarith [mul_le_of_le_one_right (sub_nonneg.2 hst.le) hw.2]⟩
  obtain ⟨Kβ, hKβ⟩ :=
    (β.locallyLipschitzOn.mono hsub_st).exists_lipschitzOnWith_of_compact isCompact_Icc
  set B : ℝ → ℂ := fun v => β.toFun (s + (t - s) * v) with hB
  have hBlip : ∃ K, LipschitzOnWith K B (Icc 0 1) :=
    ⟨_, a35_lip_affine hKβ (sub_nonneg.2 hst.le) hst'⟩
  have hB0 : B 0 = β.toFun s := by simp [hB]
  have hB1 : B 1 = β.toFun t := by simp [hB]
  have hBD : B '' Icc 0 1 ⊆ unitDisc := by
    rintro _ ⟨w, hw, rfl⟩
    exact hβ (mem_image_of_mem _ (hsub_st (hst' w hw)))
  have hBlen : a35_len (phiDensity φ) B 0 1 ≤ phiLength φ β := by
    have h := a35_len_affine (phiDensity φ) (f := β.toFun) (g := B) (k := s) (m := t - s) (p := 0)
      (q := 1) (sub_pos.2 hst) (fun u _ => Filter.EventuallyEq.rfl)
    rw [show s + (t - s) * 0 = s by ring, show s + (t - s) * 1 = t by ring] at h
    rw [h]
    show a35_len (phiDensity φ) β.toFun s t ≤ a35_len (phiDensity φ) β.toFun 0 1
    exact lintegral_mono_set (Ioo_subset_Ioo hs.1.le ht.2.le)
  -- the closed-up curve
  obtain ⟨hJ₁lip, hJ₁0, hJ₁1, hJ₁img, hJ₁len⟩ := a35_join_props (hA₁1.trans hB0.symm) hA₁lip hBlip
  obtain ⟨hJlip, hJ0, hJ1, hJimg, hJlen⟩ :=
    a35_join_props (hJ₁1.trans (hB1.trans hA₂0.symm)) hJ₁lip hA₂lip
  obtain ⟨hJloc, hJt0, hJt1⟩ := a35_lip_curve hJlip
  have hJD : a35_join (a35_join A₁ B) A₂ '' Icc 0 1 ⊆ unitDisc :=
    hJimg.trans (union_subset (hJ₁img.trans (union_subset hA₁D hBD)) hA₂D)
  obtain ⟨hHab, hcab, hDab⟩ := a35_sub_arc hH hD ha.1 hb.2
  have hab : a < b := (ha.2.trans_lt hab₀).trans_le hb.1
  have hray := fx_arc_shortest_rayLength hφ.1 hne hab hHab hcab hDab ⟨_, hJloc⟩
    (fun z hz => hJD (image_mono Ioo_subset_Icc_self hz))
    (by rw [← hJ0.trans (hJ₁0.trans hA₁0)]; exact hJt0) (by rw [← hJ1.trans hA₂1]; exact hJt1)
  have hlenJ : phiLength φ ⟨_, hJloc⟩ ≤ a35_len (phiDensity φ) A₁ 0 1 +
      a35_len (phiDensity φ) B 0 1 + a35_len (phiDensity φ) A₂ 0 1 :=
    (hJlen (phiDensity φ)).trans (add_le_add (hJ₁len (phiDensity φ)) le_rfl)
  have hA₁ε : a35_len (phiDensity φ) A₁ 0 1 ≤ (ε : ℝ≥0∞) / 2 := (hA₁len (phiDensity φ)).trans hn2.le
  have hA₂ε : a35_len (phiDensity φ) A₂ 0 1 ≤ (ε : ℝ≥0∞) / 2 := (hA₂len (phiDensity φ)).trans hn2'.le
  calc rayLength φ c a₀ b₀ ≤ rayLength φ c a b := lintegral_mono_set (Ioo_subset_Ioo ha.2 hb.1)
    _ ≤ phiLength φ ⟨_, hJloc⟩ := hray
    _ ≤ _ := hlenJ
    _ ≤ (ε : ℝ≥0∞) / 2 + phiLength φ β + (ε : ℝ≥0∞) / 2 := add_le_add (add_le_add hA₁ε hBlen) hA₂ε
    _ = phiLength φ β + ε := by rw [add_comm ((ε : ℝ≥0∞) / 2), add_assoc, ENNReal.add_halves]

/-! ### s21u P2b interface (scout U3): Lemma 35.1 through the Jensen-form boundary uniqueness

A horizontal ray that does not converge crosses a fixed sector near `∂Δ` again and again, and the crossing arcs have
`φ`-length tending to `0` (`s35v_crossing_arcs`). The Jensen-form boundary uniqueness `buj_no_short_crossings`
(`Lemmas/BoundaryJensen`) forbids this. So every ray converges (`s35v_ray_converges`), and `eq35_2_crossing_arcs`,
`lemma35_1` and `trajectory_endpoints` follow. -/

/-! ### Copied from s35h `scout_T/h35_T.lean` (renamed `s35v_c_`) -/

/-- A horizontal arc on `(0, 1)` is continuous on `(0, 1)` (s35h `h35_cont`). -/
theorem s35v_c_cont {φ : ℂ → ℂ} {c : ℝ → ℂ} (hH : IsHorizontalArc φ c 0 1) :
    ContinuousOn c (Ioo 0 1) := fun t ht => (hH t ht).1.continuousAt.continuousWithinAt

/-- **Late crossings** (s35h `h35_cross`). If `c` (continuous on `(0, 1)`) comes arbitrarily late within `r` of `ζ`
and arbitrarily late to distance `≥ δ > r` from `ζ`, it meets the circle `|z - ζ| = r` arbitrarily late. -/
theorem s35v_c_cross {c : ℝ → ℂ} (hc : ContinuousOn c (Ioo 0 1)) {ζ : ℂ} {r δ : ℝ} (hrδ : r < δ)
    (hin : ∃ᶠ t in 𝓝[<] (1 : ℝ), ‖c t - ζ‖ < r) (hout : ∃ᶠ t in 𝓝[<] (1 : ℝ), δ ≤ ‖c t - ζ‖)
    {T : ℝ} (hT : T < 1) : ∃ u ∈ Ioo (max T 0) 1, ‖c u - ζ‖ = r := by
  have hT' : max T 0 < 1 := max_lt hT one_pos
  obtain ⟨t₁, ht₁, ht₁T⟩ := (hin.and_eventually (Ioo_mem_nhdsLT hT')).exists
  obtain ⟨t₂, ht₂, ht₂T⟩ := (hout.and_eventually (Ioo_mem_nhdsLT ht₁T.2)).exists
  have hsub : Icc t₁ t₂ ⊆ Ioo 0 1 := fun x hx =>
    ⟨(le_max_right T 0).trans_lt (ht₁T.1.trans_le hx.1), hx.2.trans_lt ht₂T.2⟩
  have hg : ContinuousOn (fun s => ‖c s - ζ‖) (Icc t₁ t₂) :=
    ((hc.mono hsub).sub continuousOn_const).norm
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc ht₂T.1.le hg ⟨ht₁.le, hrδ.le.trans ht₂⟩
  exact ⟨u, ⟨ht₁T.1.trans_le hu.1, hu.2.trans_lt ht₂T.2⟩, hur⟩

/-- Not converging to `ζ` means: frequently at distance `≥ δ` from `ζ`, for some `δ > 0` (s35h
`h35_frequently_far`). -/
theorem s35v_c_frequently_far {c : ℝ → ℂ} {ζ : ℂ} (hnt : ¬ Tendsto c (𝓝[<] 1) (𝓝 ζ)) :
    ∃ δ > 0, ∃ᶠ t in 𝓝[<] (1 : ℝ), δ ≤ ‖c t - ζ‖ := by
  by_contra hcon
  push Not at hcon
  apply hnt
  rw [Metric.tendsto_nhds]
  intro e he
  filter_upwards [hcon e he] with t ht
  rwa [dist_eq_norm]

/-- The `φ`-length of `c|(a, b)` is monotone in the interval (s35h `h35_rayLength_mono`). -/
theorem s35v_c_rayLength_mono (φ : ℂ → ℂ) (c : ℝ → ℂ) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    rayLength φ c a b ≤ rayLength φ c a' b' :=
  lintegral_mono_set (Ioo_subset_Ioo ha hb)

/-- `rayLength φ c u 1` is the supremum of `rayLength φ c u v`, `v < 1`: a bound for all `v < 1` bounds the tail
(s35h `h35_rayLength_tail_le`). -/
theorem s35v_c_rayLength_tail_le {φ : ℂ → ℂ} {c : ℝ → ℂ} {u : ℝ} (hu : u < 1) {B : ℝ≥0∞}
    (hB : ∀ v ∈ Ioo u 1, rayLength φ c u v ≤ B) : rayLength φ c u 1 ≤ B := by
  set w : ℕ → ℝ := fun k => 1 - (1 - u) / ((k : ℝ) + 2) with hw
  have hu0 : 0 < 1 - u := sub_pos.2 hu
  have hw1 : ∀ k : ℕ, u < w k ∧ w k < 1 := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h1 : (1 - u) / ((k : ℝ) + 2) < 1 - u := by
      rw [div_lt_iff₀ hk]
      nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h2 : 0 < (1 - u) / ((k : ℝ) + 2) := div_pos hu0 hk
    constructor <;> simp only [hw] <;> linarith
  have hU : Ioo u 1 = ⋃ k : ℕ, Ioo u (w k) := by
    ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨k, hk⟩ := exists_nat_gt ((1 - u) / (1 - x))
      refine ⟨k, h1, ?_⟩
      have hx0 : 0 < 1 - x := sub_pos.2 h2
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have h3 : 1 - u < (k : ℝ) * (1 - x) := by
        rw [div_lt_iff₀ hx0] at hk
        linarith
      have h4 : (1 - u) / ((k : ℝ) + 2) < 1 - x := by
        rw [div_lt_iff₀ hk2]
        nlinarith
      simp only [hw]
      linarith
    · rintro ⟨k, h1, h2⟩
      exact ⟨h1, h2.trans (hw1 k).2⟩
  have hdir : Directed (· ⊆ ·) fun k : ℕ => Ioo u (w k) := by
    refine Monotone.directed_le fun k l hkl => Ioo_subset_Ioo_right ?_
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hkl' : (k : ℝ) + 2 ≤ (l : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hkl 2
    have := div_le_div_of_nonneg_left hu0.le hk2 hkl'
    simp only [hw]
    linarith
  unfold rayLength
  rw [hU, setLIntegral_iUnion_of_directed _ hdir]
  exact iSup_le fun k => hB (w k) (hw1 k)

/-- **Short tails** (s35h `h35_tail_small`). If a horizontal ray of `φ ∈ A(Δ)` has a boundary cluster point `ζ`
(at `t → 1⁻`) but does not converge to `ζ`, then arbitrarily late tails have arbitrarily small `φ`-length: between
two late crossings of a short circle `|z - ζ| = r` (`circular_arcs_short`) the ray is shorter than the circular arc
(`fx_arc_shortest_rayLength`). -/
theorem s35v_c_tail_small {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hcl : MapClusterPt ζ (𝓝[<] 1) c) (hnt : ¬ Tendsto c (𝓝[<] 1) (𝓝 ζ))
    {ε : ℝ≥0∞} (hε : 0 < ε) {T : ℝ} (hT : T < 1) :
    ∃ t₀ ∈ Ioo (max T 0) 1, rayLength φ c t₀ 1 ≤ ε := by
  obtain ⟨hH, hD, -⟩ := hc
  have hcont := s35v_c_cont hH
  obtain ⟨δ, hδ, hout⟩ := s35v_c_frequently_far hnt
  obtain ⟨r, hr, hr0, hLr⟩ := circular_arcs_short hφ hζ
  obtain ⟨n, hn1, hn2⟩ :=
    ((hr0.eventually (gt_mem_nhds hδ)).and (hLr.eventually (gt_mem_nhds hε))).exists
  have hin : ∃ᶠ t in 𝓝[<] (1 : ℝ), ‖c t - ζ‖ < r n := by
    have h := (mapClusterPt_iff_frequently.1 hcl) _ (ball_mem_nhds ζ (hr n).1)
    exact h.mono fun t ht => by rwa [mem_ball, dist_eq_norm] at ht
  obtain ⟨u₀, hu₀, hu₀r⟩ := s35v_c_cross hcont hn1 hin hout hT
  have hu₀pos : 0 < u₀ := (le_max_right T 0).trans_lt hu₀.1
  have hu₀D : c u₀ ∈ unitDisc := hD (mem_image_of_mem c ⟨hu₀pos, hu₀.2⟩)
  -- between `u₀` and a later crossing `v`, the ray is shorter than the circle
  have hseg : ∀ v ∈ Ioo u₀ 1, ‖c v - ζ‖ = r n → rayLength φ c u₀ v ≤
      ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
        unitDisc.indicator (fun z => phiDensity φ z) (ζ + r n * exp (θ * I)) * ENNReal.ofReal (r n) := by
    intro v hv hvr
    have hvD : c v ∈ unitDisc := hD (mem_image_of_mem c ⟨hu₀pos.trans hv.1, hv.2⟩)
    obtain ⟨A, hAlip, hA0, hA1, hAD, hAlen⟩ := a35_arc_exists hζ (hr n).1 hu₀r hvr hu₀D hvD
    obtain ⟨hAloc, hAt0, hAt1⟩ := a35_lip_curve hAlip
    obtain ⟨hHab, hcab, hDab⟩ := a35_sub_arc hH hD hu₀pos hv.2
    have key := fx_arc_shortest_rayLength hφ.1 hne hv.1 hHab hcab hDab ⟨A, hAloc⟩
      (fun z hz => hAD (image_mono Ioo_subset_Icc_self hz)) (by rw [← hA0]; exact hAt0)
      (by rw [← hA1]; exact hAt1)
    exact key.trans (hAlen (phiDensity φ))
  refine ⟨u₀, hu₀, s35v_c_rayLength_tail_le hu₀.2 fun v hv => ?_⟩
  obtain ⟨w, hw, hwr⟩ := s35v_c_cross hcont hn1 hin hout hv.2
  have hvw : v ≤ w := (le_max_left v 0).trans hw.1.le
  calc rayLength φ c u₀ v ≤ rayLength φ c u₀ w := s35v_c_rayLength_mono φ c le_rfl hvw
    _ ≤ _ := hseg w ⟨hv.1.trans_le hvw, hw.2⟩ hwr
    _ ≤ ε := hn2.le

/-- A horizontal ray lies eventually (as `t → 1⁻`) in `Δ` (s35h `h35_ev_mem`). -/
theorem s35v_c_ev_mem {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) :
    ∀ᶠ t in 𝓝[<] (1 : ℝ), c t ∈ unitDisc := by
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  exact hc.2.1 (mem_image_of_mem c ht)

/-- A cluster point (at `t → 1⁻`) of a horizontal ray lying in `closedBall 0 1` lies on `∂Δ` (s35h
`h35_norm_of_cluster`). -/
theorem s35v_c_norm_of_cluster {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) {ζ : ℂ}
    (hζ : ζ ∈ closedBall (0 : ℂ) 1) (hcl : MapClusterPt ζ (𝓝[<] 1) c) : ‖ζ‖ = 1 := by
  have hle : ‖ζ‖ ≤ 1 := by simpa using hζ
  by_contra hne
  have hlt : ‖ζ‖ < 1 := lt_of_le_of_ne hle hne
  have hεpos : 0 < (1 - ‖ζ‖) / 2 := by linarith
  have hsub : closedBall ζ ((1 - ‖ζ‖) / 2) ⊆ unitDisc := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [unitDisc, mem_ball_zero_iff]
    have h' := norm_sub_norm_le z ζ
    linarith
  have h1 := hc.2.2 _ (isCompact_closedBall ζ _) hsub
  have h2 := (mapClusterPt_iff_frequently.1 hcl) _ (closedBall_mem_nhds ζ hεpos)
  obtain ⟨t, ht1, ht2⟩ := (h2.and_eventually h1).exists
  exact ht2 ht1

/-- A horizontal ray has a cluster point on `∂Δ` at `t → 1⁻` (s35h `h35_cluster_exists`). -/
theorem s35v_c_cluster_exists {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ MapClusterPt ζ (𝓝[<] 1) c := by
  have hfr : ∃ᶠ t in 𝓝[<] (1 : ℝ), c t ∈ closedBall (0 : ℂ) 1 :=
    ((s35v_c_ev_mem hc).mono fun t ht => ball_subset_closedBall ht).frequently
  obtain ⟨ζ, hζ, hcl⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_mapClusterPt_of_frequently hfr
  exact ⟨ζ, s35v_c_norm_of_cluster hc hζ hcl, hcl⟩

/-- A horizontal ray eventually stays in the collar `ρ < |z| < 1` (`ρ < 1`) (s35h `h35_ev_collar`). -/
theorem s35v_c_ev_collar {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ T < (1 : ℝ), ∀ t ∈ Ioo T 1, ρ < ‖c t‖ := by
  have hsub : closedBall (0 : ℂ) (max ρ 0) ⊆ unitDisc :=
    closedBall_subset_ball (max_lt hρ one_pos)
  have hev := hc.2.2 _ (isCompact_closedBall (0 : ℂ) (max ρ 0)) hsub
  obtain ⟨T, hT, hTs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  refine ⟨T, hT, fun t ht => ?_⟩
  have h : c t ∉ closedBall (0 : ℂ) (max ρ 0) := hTs ht
  rw [mem_closedBall, dist_zero_right, not_le] at h
  exact (le_max_left ρ 0).trans_lt h

/-! ### Ray injectivity (copied from s21u scout U3 `h21u3_inj.lean`) -/

/-- The constant curve at `p` as an `LRCurve` (scout U3 `h21u3_constCurve`). -/
def s35v_c_constCurve (p : ℂ) : LRCurve :=
  ⟨fun _ => p, (LipschitzWith.const (α := ℝ) p).locallyLipschitz.locallyLipschitzOn⟩

/-- A constant curve has `φ`-length `0` (scout U3 `h21u3_phiLength_const`). -/
theorem s35v_c_phiLength_const (φ : ℂ → ℂ) (p : ℂ) : phiLength φ (s35v_c_constCurve p) = 0 := by
  simp [phiLength, LRCurve.rhoLength, s35v_c_constCurve]

/-- **A horizontal ray is injective on `(0, 1)`** (scout U3 `h21u3_ray_injOn`): a loop `c a = c b` would be longer
than the constant curve, against the geodesic property `fx_arc_shortest_rayLength` and `a35_rayLength_pos`. -/
theorem s35v_c_ray_injOn {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) : InjOn c (Ioo 0 1) := by
  obtain ⟨hH, hD, -⟩ := hc
  have key : ∀ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a < b → c a ≠ c b := by
    intro a b ha hb hab heq
    obtain ⟨hHab, hcab, hDab⟩ := a35_sub_arc hH hD ha.1 hb.2
    have hca : c a ∈ unitDisc := hD (mem_image_of_mem c ha)
    have hle := fx_arc_shortest_rayLength hφ.1 hne hab hHab hcab hDab (s35v_c_constCurve (c a))
      (by rintro _ ⟨t, -, rfl⟩; exact hca) tendsto_const_nhds
      (by rw [← heq]; exact tendsto_const_nhds)
    rw [s35v_c_phiLength_const] at hle
    have hpos := a35_rayLength_pos hφ.1.continuousOn hH hD ha.1.le hab hb.2.le
    exact absurd (le_antisymm hle zero_le) hpos.ne'
  intro a ha b hb heq
  rcases lt_trichotomy a b with h | h | h
  · exact absurd heq (key a b ha hb h)
  · exact h
  · exact absurd heq.symm (key b a hb ha h)

/-! ### Real-variable lemmas: crossings of two levels, oscillation, good angles -/

/-- **Crossing of two levels.** If `f` is continuous on `[p, q]` with `f p ≤ A < B ≤ f q`, there are `p ≤ s < t ≤ q`
with `f s = A`, `f t = B` and `A < f < B` on `(s, t)`: `t` is the first time `f` reaches `B`, and `s` is the last
time before `t` at which `f ≤ A`. -/
theorem s35v_c_extract {f : ℝ → ℝ} {p q A B : ℝ} (hpq : p ≤ q) (hf : ContinuousOn f (Icc p q)) (hAB : A < B)
    (hp : f p ≤ A) (hq : B ≤ f q) :
    ∃ s t, p ≤ s ∧ s < t ∧ t ≤ q ∧ f s = A ∧ f t = B ∧ ∀ u ∈ Ioo s t, A < f u ∧ f u < B := by
  -- `t`: the first time in `[p, q]` at which `f ≥ B`
  obtain ⟨t, htS, hle⟩ : ∃ t ∈ Icc p q ∩ f ⁻¹' Ici B, ∀ u ∈ Icc p q ∩ f ⁻¹' Ici B, t ≤ u := by
    have hSc : IsClosed (Icc p q ∩ f ⁻¹' Ici B) := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSb : BddBelow (Icc p q ∩ f ⁻¹' Ici B) := ⟨p, fun u hu => hu.1.1⟩
    exact ⟨_, hSc.csInf_mem ⟨q, ⟨hpq, le_rfl⟩, hq⟩ hSb, fun u hu => csInf_le hSb hu⟩
  have hpt : p ≤ t := htS.1.1
  have htq : t ≤ q := htS.1.2
  have hft : f t = B := by
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hpt (hf.mono (Icc_subset_Icc_right htq))
      ⟨hp.trans hAB.le, htS.2⟩
    have hut : t ≤ u := hle u ⟨⟨hu.1, hu.2.trans htq⟩, hfu.ge⟩
    rw [← le_antisymm hu.2 hut]
    exact hfu
  -- `s`: the last time in `[p, t]` at which `f ≤ A`
  obtain ⟨s, hsS, hge⟩ : ∃ s ∈ Icc p t ∩ f ⁻¹' Iic A, ∀ u ∈ Icc p t ∩ f ⁻¹' Iic A, u ≤ s := by
    have hSc : IsClosed (Icc p t ∩ f ⁻¹' Iic A) :=
      (hf.mono (Icc_subset_Icc_right htq)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSb : BddAbove (Icc p t ∩ f ⁻¹' Iic A) := ⟨t, fun u hu => hu.1.2⟩
    exact ⟨_, hSc.csSup_mem ⟨p, ⟨le_rfl, hpt⟩, hp⟩ hSb, fun u hu => le_csSup hSb hu⟩
  have hps : p ≤ s := hsS.1.1
  have hst' : s ≤ t := hsS.1.2
  have hfs : f s = A := by
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hst' (hf.mono (Icc_subset_Icc hps htq))
      ⟨hsS.2, hAB.le.trans hft.ge⟩
    have hus : u ≤ s := hge u ⟨⟨hps.trans hu.1, hu.2⟩, hfu.le⟩
    rw [← le_antisymm hus hu.1]
    exact hfu
  have hst : s < t := lt_of_le_of_ne hst' fun h => by
    rw [h, hft] at hfs
    linarith
  refine ⟨s, t, hps, hst, htq, hfs, hft, fun u hu => ⟨?_, ?_⟩⟩
  · by_contra h
    exact absurd (hge u ⟨⟨hps.trans hu.1.le, hu.2.le⟩, not_lt.1 h⟩) (not_le.2 hu.1)
  · by_contra h
    exact absurd (hle u ⟨⟨hps.trans hu.1.le, hu.2.le.trans htq⟩, not_lt.1 h⟩) (not_le.2 hu.2)

/-- **Oscillation of a non-convergent function modulo `2π`.** If `f` has no limit at `1⁻`, then for `σ = 1` or
`σ = -1` there are levels `A < B` such that arbitrarily late `σ f` passes from `≤ A + 2πk` to `≥ B + 2πk` (for some
`k ∈ ℤ`). Either `f` oscillates between two levels (`k = 0`), or `f` is unbounded above (`σ = 1`) or below
(`σ = -1`), or `f` is eventually bounded and then converges to any of its cluster values. -/
theorem s35v_c_osc {f : ℝ → ℝ} {T : ℝ} (hT : T < 1) (hnc : ∀ L : ℝ, ¬ Tendsto f (𝓝[<] 1) (𝓝 L)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ A B : ℝ, A < B ∧ ∀ t₀ < (1 : ℝ), ∃ p q : ℝ, ∃ k : ℤ,
      max t₀ T < p ∧ p < q ∧ q < 1 ∧ σ * f p ≤ A + 2 * π * k ∧ B + 2 * π * k ≤ σ * f q := by
  have hfr : ∀ P : ℝ → Prop, (∃ᶠ t in 𝓝[<] (1 : ℝ), P t) → ∀ x < (1 : ℝ), ∃ t, x < t ∧ t < 1 ∧ P t := by
    intro P hP x hx
    obtain ⟨t, htP, ht⟩ := (hP.and_eventually (Ioo_mem_nhdsLT hx)).exists
    exact ⟨t, ht.1, ht.2, htP⟩
  by_cases h1 : ∃ A B : ℝ, A < B ∧ (∃ᶠ t in 𝓝[<] (1 : ℝ), f t < A) ∧ ∃ᶠ t in 𝓝[<] (1 : ℝ), B < f t
  · obtain ⟨A, B, hAB, hA, hB⟩ := h1
    refine ⟨1, Or.inl rfl, A, B, hAB, fun t₀ ht₀ => ?_⟩
    obtain ⟨p, hp, hp1, hpA⟩ := hfr _ hA _ (max_lt ht₀ hT)
    obtain ⟨q, hq, hq1, hqB⟩ := hfr _ hB p hp1
    refine ⟨p, q, 0, hp, hq, hq1, ?_, ?_⟩
    · simp only [one_mul, Int.cast_zero, mul_zero, add_zero]
      exact hpA.le
    · simp only [one_mul, Int.cast_zero, mul_zero, add_zero]
      exact hqB.le
  by_cases h2 : ∀ B : ℝ, ∃ᶠ t in 𝓝[<] (1 : ℝ), B < f t
  · refine ⟨1, Or.inl rfl, 0, 1, one_pos, fun t₀ ht₀ => ?_⟩
    obtain ⟨p, hp, hp1⟩ := exists_between (max_lt ht₀ hT)
    have hk := Int.le_ceil (f p / (2 * π))
    rw [div_le_iff₀ Real.two_pi_pos] at hk
    obtain ⟨q, hq, hq1, hqB⟩ := hfr _ (h2 (1 + 2 * π * ⌈f p / (2 * π)⌉)) p hp1
    exact ⟨p, q, ⌈f p / (2 * π)⌉, hp, hq, hq1, by linarith, by linarith⟩
  by_cases h3 : ∀ A : ℝ, ∃ᶠ t in 𝓝[<] (1 : ℝ), f t < A
  · refine ⟨-1, Or.inr rfl, 0, 1, one_pos, fun t₀ ht₀ => ?_⟩
    obtain ⟨p, hp, hp1⟩ := exists_between (max_lt ht₀ hT)
    have hk := Int.le_ceil (-f p / (2 * π))
    rw [div_le_iff₀ Real.two_pi_pos] at hk
    obtain ⟨q, hq, hq1, hqA⟩ := hfr _ (h3 (-(1 + 2 * π * ⌈-f p / (2 * π)⌉))) p hp1
    exact ⟨p, q, ⌈-f p / (2 * π)⌉, hp, hq, hq1, by linarith, by linarith⟩
  -- otherwise `f` is eventually bounded, and converges to a cluster value: a contradiction
  exfalso
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ᶠ t in 𝓝[<] (1 : ℝ), f t ≤ B₀ := by
    by_contra h
    apply h2
    intro B
    by_contra hB
    exact h ⟨B, (not_frequently.1 hB).mono fun t ht => not_lt.1 ht⟩
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, ∀ᶠ t in 𝓝[<] (1 : ℝ), A₀ ≤ f t := by
    by_contra h
    apply h3
    intro A
    by_contra hA
    exact h ⟨A, (not_frequently.1 hA).mono fun t ht => not_lt.1 ht⟩
  have hK : ∃ᶠ t in 𝓝[<] (1 : ℝ), f t ∈ Icc A₀ B₀ :=
    ((hA₀.and hB₀).mono fun t ht => (⟨ht.1, ht.2⟩ : f t ∈ Icc A₀ B₀)).frequently
  obtain ⟨L, -, hL⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently hK
  apply hnc L
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_contra hcon
    exact h1 ⟨(a + L) / 2, (a + 3 * L) / 4, by linarith,
      (not_eventually.1 hcon).mono fun t ht => by linarith [not_lt.1 ht],
      ((mapClusterPt_iff_frequently.1 hL) _ (Ioi_mem_nhds (by linarith))).mono fun t ht => ht⟩
  · by_contra hcon
    exact h1 ⟨(3 * L + b) / 4, (L + b) / 2, by linarith,
      ((mapClusterPt_iff_frequently.1 hL) _ (Iio_mem_nhds (by linarith))).mono fun t ht => ht,
      (not_eventually.1 hcon).mono fun t ht => by linarith [not_lt.1 ht]⟩

/-- `e^{i(θ + 2πk)} = e^{iθ}`. -/
theorem s35v_c_exp_shift (θ : ℝ) (k : ℤ) : exp (((θ + 2 * π * k : ℝ) : ℂ) * I) = exp (θ * I) := by
  have h : (((θ + 2 * π * k : ℝ) : ℂ) * I) = θ * I + k * (2 * π * I) := by push_cast; ring
  rw [h, exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Good angles are dense**: every interval `(x, x + ε)` contains an angle `θ` whose radius has finite `φ`-length
(`eq35_1_radii_finite_length`, moved into `(0, 2π)` by a multiple of `2π`). -/
theorem s35v_c_good_dense {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ ∈ Ioo x (x + ε), ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * exp (θ * I)) < ⊤ := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (n : ℝ) * (2 * π) ≤ x ∧ x < ((n : ℝ) + 1) * (2 * π) :=
    ⟨⌊x / (2 * π)⌋, (le_div_iff₀ hπ).1 (Int.floor_le _), (div_lt_iff₀ hπ).1 (Int.lt_floor_add_one _)⟩
  obtain ⟨ε', hε'0, hε'ε, hε'y⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 2 * π - (x - 2 * π * n) :=
    ⟨min ε (2 * π - (x - 2 * π * n)), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hsub : Ioo (x - 2 * π * n) (x - 2 * π * n + ε') ⊆ Ioo 0 (2 * π) := fun θ hθ =>
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hae := ae_restrict_of_ae_restrict_of_subset hsub (eq35_1_radii_finite_length hφ)
  have hne0 : volume.restrict (Ioo (x - 2 * π * n) (x - 2 * π * n + ε')) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have : (ae (volume.restrict (Ioo (x - 2 * π * n) (x - 2 * π * n + ε')))).NeBot := ae_neBot.2 hne0
  obtain ⟨θ, hθ, hθmem⟩ := (hae.and (ae_restrict_mem measurableSet_Ioo)).exists
  refine ⟨θ + 2 * π * n, ⟨by linarith [hθmem.1], by linarith [hθmem.2]⟩, ?_⟩
  rw [s35v_c_exp_shift]
  exact hθ

/-- `s35v_c_good_dense` for `σ θ`, `σ = ±1`. -/
theorem s35v_c_good_dense_sign {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ ∈ Ioo x (x + ε), ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * exp (((σ * θ : ℝ) : ℂ) * I)) < ⊤ := by
  rcases hσ with rfl | rfl
  · obtain ⟨θ, hθ, hg⟩ := s35v_c_good_dense hφ x hε
    exact ⟨θ, hθ, by rwa [one_mul]⟩
  · obtain ⟨θ, hθ, hg⟩ := s35v_c_good_dense hφ (-x - ε) hε
    exact ⟨-θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩, by rwa [neg_one_mul, neg_neg]⟩

/-! ### The continuous argument of the ray -/

/-- `|c(t)| → 1` as `t → 1⁻` for a horizontal ray. -/
theorem s35v_c_norm_tendsto {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) :
    Tendsto (fun t => ‖c t‖) (𝓝[<] 1) (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hc.2.2 (closedBall 0 a) (isCompact_closedBall 0 a) (closedBall_subset_ball ha)] with t ht
    rwa [mem_closedBall, dist_zero_right, not_le] at ht
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
    have h := hc.2.1 (mem_image_of_mem c ht)
    rw [unitDisc, mem_ball_zero_iff] at h
    linarith

/-- **Continuous argument.** A curve `c ≠ 0`, continuous on `(T, 1)`, has a continuous argument `Θ` there:
`c = |c| e^{iΘ}` (a continuous logarithm on the simply connected `(T, 1)`). -/
theorem s35v_c_lift {c : ℝ → ℂ} {T : ℝ} (hT : T < 1) (hc : ContinuousOn c (Ioo T 1))
    (h0 : ∀ t ∈ Ioo T 1, c t ≠ 0) :
    ∃ Θ : ℝ → ℝ, ContinuousOn Θ (Ioo T 1) ∧ ∀ t ∈ Ioo T 1, c t = ‖c t‖ * exp (Θ t * I) := by
  have hsc : IsSimplyConnected (Ioo T 1) := by
    have : ContractibleSpace ↥(Ioo T 1) := (convex_Ioo T 1).contractibleSpace (nonempty_Ioo.2 hT)
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_Ioo hc
    (by rintro ⟨t, ht, h⟩; exact h0 t ht h)
  refine ⟨fun t => (L t).im, Complex.continuous_im.comp_continuousOn hLc, fun t ht => ?_⟩
  have h1 : exp (L t) = c t := hLe ht
  show c t = ‖c t‖ * exp ((L t).im * I)
  rw [← h1, Complex.norm_exp, Complex.ofReal_exp, ← exp_add, Complex.re_add_im]

/-- The continuous argument of a ray that does not converge does not converge either: `Θ → L` would give
`c → e^{iL}`. -/
theorem s35v_c_lift_not_tendsto {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsHorizontalRay φ c)
    (hnc : ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ Tendsto c (𝓝[<] 1) (𝓝 ζ)) {T : ℝ} (hT : T < 1) {Θ : ℝ → ℝ}
    (hpol : ∀ t ∈ Ioo T 1, c t = ‖c t‖ * exp (Θ t * I)) (L : ℝ) : ¬ Tendsto Θ (𝓝[<] 1) (𝓝 L) := by
  intro hΘ
  refine hnc ⟨exp (L * I), Complex.norm_exp_ofReal_mul_I L, ?_⟩
  have h1 : Tendsto (fun t => ((‖c t‖ : ℝ) : ℂ) * exp (Θ t * I)) (𝓝[<] 1)
      (𝓝 (((1 : ℝ) : ℂ) * exp (L * I))) :=
    ((Complex.continuous_ofReal.tendsto 1).comp (s35v_c_norm_tendsto hc)).mul
      ((Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto L).comp hΘ).mul_const I))
  rw [Complex.ofReal_one, one_mul] at h1
  refine Tendsto.congr' ?_ h1
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht using (hpol t ht).symm

/-! ### Sector cuts -/

/-- The open sector `buj_openSector ξ α` (`α < π`) is open. -/
theorem s35v_c_isOpen_sector {ξ : ℂ} {α : ℝ} (hαπ : α < π) : IsOpen (buj_openSector ξ α) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hz0, hz1, hz2⟩ := hz
  have hslit : z / ξ ∈ slitPlane := mem_slitPlane_iff_arg.2 ⟨(hz2.trans hαπ).ne, hz0⟩
  have hdiv : Continuous fun w : ℂ => w / ξ := continuous_id.div_const ξ
  have harg : ContinuousAt (fun w : ℂ => arg (w / ξ)) z :=
    ContinuousAt.comp (g := arg) (f := fun w : ℂ => w / ξ) (x := z) (continuousAt_arg hslit) hdiv.continuousAt
  filter_upwards [harg.eventually (lt_mem_nhds hz1), harg.eventually (gt_mem_nhds hz2),
    hdiv.continuousAt.eventually_ne hz0] with w h1 h2 h3
  exact ⟨h3, h1, h2⟩

/-- **The base point.** For `φ ≢ 0` holomorphic in `Δ` and a sector with `0 < α < π`, there is a ball `B(z₀, δ)`
inside the open sector ∩ `B(0, 1/2)` with `φ(z₀) ≠ 0` (identity theorem on the connected `Δ`). -/
theorem s35v_c_base {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) :
    ∃ z₀ : ℂ, ∃ δ : ℝ, 0 < δ ∧ φ z₀ ≠ 0 ∧ ball z₀ δ ⊆ buj_openSector ξ α ∩ ball 0 (1 / 2) := by
  have hWo : IsOpen (buj_openSector ξ α ∩ ball 0 (1 / 2)) := (s35v_c_isOpen_sector hαπ).inter isOpen_ball
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξ
    exact zero_ne_one hξ
  -- the point `w₀ = ξ e^{iα/2}/4`
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℂ, w₀ = ξ * (((1 / 4 : ℝ) : ℂ) * exp (((α / 2 : ℝ) : ℂ) * I)) := ⟨_, rfl⟩
  have hw₀ξ : w₀ / ξ = ((1 / 4 : ℝ) : ℂ) * exp (((α / 2 : ℝ) : ℂ) * I) := by
    rw [hw₀, mul_div_cancel_left₀ _ hξ0]
  have harg : arg (w₀ / ξ) = α / 2 := by
    rw [hw₀ξ, exp_mul_I]
    exact arg_mul_cos_add_sin_mul_I (by norm_num) ⟨by linarith [Real.pi_pos], by linarith⟩
  have hw₀W : w₀ ∈ buj_openSector ξ α ∩ ball 0 (1 / 2) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hw₀ξ]
      exact mul_ne_zero (by norm_num) (exp_ne_zero _)
    · rw [harg]
      linarith
    · rw [harg]
      linarith
    · rw [mem_ball_zero_iff, hw₀, norm_mul, norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      norm_num
  by_contra hcon
  have hzero : ∀ z ∈ buj_openSector ξ α ∩ ball 0 (1 / 2), φ z = 0 := by
    intro z hz
    by_contra hz0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hWo z hz
    exact hcon ⟨z, δ, hδ, hz0, hball⟩
  have hsub : buj_openSector ξ α ∩ ball 0 (1 / 2) ⊆ unitDisc := fun z hz =>
    mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz.2).trans (by norm_num))
  have hev : φ =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hWo.mem_nhds hw₀W] with z hz using hzero z hz
  have hA : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd isOpen_ball
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (hsub hw₀W) hev
  obtain ⟨z, hz, hφz⟩ := hne
  exact hφz (hEq hz)

/-- **A crossing of the sector is a sector cut.** Let `τ` be an arc on `[s, t]` (continuous, injective,
differentiable inside, with integrable derivative) in the collar `1/2 < |τ| < 1`, with a continuous argument `Ψ`
(`τ = |τ| e^{iΨ}`) that runs from `θ + 2πk` to `θ + α + 2πk` and stays strictly between. Then `τ|[s, t]` is a
sector cut of the sector `buj_openSector (e^{iθ}) α` at height `1/2`. -/
theorem s35v_c_cut {τ : ℝ → ℂ} {Ψ : ℝ → ℝ} {s t θ α : ℝ} {k : ℤ} (hα0 : 0 < α) (hαπ : α < π) (hst : s < t)
    (hτ : ContinuousOn τ (Icc s t) ∧ InjOn τ (Icc s t) ∧ (∀ u ∈ Ioo s t, DifferentiableAt ℝ τ u) ∧
      IntervalIntegrable (deriv τ) volume s t)
    (hpol : ∀ u ∈ Icc s t, τ u = ‖τ u‖ * exp (Ψ u * I))
    (hnorm : ∀ u ∈ Icc s t, 1 / 2 < ‖τ u‖ ∧ ‖τ u‖ < 1)
    (hΨs : Ψ s = θ + 2 * π * k) (hΨt : Ψ t = θ + α + 2 * π * k)
    (hΨ : ∀ u ∈ Ioo s t, θ + 2 * π * k < Ψ u ∧ Ψ u < θ + α + 2 * π * k) :
    buj_IsSectorCut (exp (θ * I)) α ‖τ s‖ ‖τ t‖ (1 / 2) τ s t := by
  obtain ⟨hcont, hinj, hdiff, hint⟩ := hτ
  have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
  have hpos : ∀ u ∈ Icc s t, 0 < ‖τ u‖ := fun u hu => by linarith [(hnorm u hu).1]
  refine ⟨⟨hα0, hαπ, Complex.norm_exp_ofReal_mul_I θ, by norm_num, hpos s hsI, hpos t htI, hst⟩,
    ⟨hcont, hinj, ?_, ?_⟩, fun u hu => ?_, hnorm, hdiff, hint⟩
  · refine (hpol s hsI).trans ?_
    rw [hΨs, s35v_c_exp_shift]
  · refine (hpol t htI).trans ?_
    rw [hΨt, s35v_c_exp_shift, ← exp_add]
    congr 2
    push_cast
    ring
  · have huI : u ∈ Icc s t := Ioo_subset_Icc_self hu
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = Ψ u - θ - 2 * π * k := ⟨_, rfl⟩
    have hψ0 : 0 < ψ := by linarith [(hΨ u hu).1]
    have hψα : ψ < α := by linarith [(hΨ u hu).2]
    have hexp : exp (Ψ u * I) = exp (ψ * I) * exp (θ * I) := by
      rw [← exp_add, show Ψ u = (ψ + θ) + 2 * π * k by linarith, s35v_c_exp_shift]
      congr 1
      push_cast
      ring
    have heq : τ u / exp (θ * I) = ‖τ u‖ * exp (ψ * I) := by
      calc τ u / exp (θ * I) = ‖τ u‖ * exp (Ψ u * I) / exp (θ * I) := by rw [← hpol u huI]
        _ = ‖τ u‖ * exp (ψ * I) := by
          rw [hexp, ← mul_assoc, mul_div_assoc, div_self (exp_ne_zero _), mul_one]
    have harg : arg ((‖τ u‖ : ℂ) * exp (ψ * I)) = ψ := by
      rw [exp_mul_I]
      exact arg_mul_cos_add_sin_mul_I (hpos u huI) ⟨by linarith [Real.pi_pos], by linarith⟩
    show τ u / exp (θ * I) ≠ 0 ∧ 0 < arg (τ u / exp (θ * I)) ∧ arg (τ u / exp (θ * I)) < α
    rw [heq, harg]
    exact ⟨mul_ne_zero (ofReal_ne_zero.2 (hpos u huI).ne') (exp_ne_zero _), hψ0, hψα⟩

/-- **The arc facts for a ray.** For `0 < s < t < 1` with `rayLength φ c s t < ∞`, the ray `c` is continuous and
injective on `[s, t]`, differentiable inside, and `c'` is integrable on `[s, t]` (`√|φ ∘ c|` is bounded below on the
compact arc). -/
theorem s35v_c_arc_facts {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (ht : t < 1) (hlen : rayLength φ c s t < ⊤) :
    ContinuousOn c (Icc s t) ∧ InjOn c (Icc s t) ∧ (∀ u ∈ Ioo s t, DifferentiableAt ℝ c u) ∧
      IntervalIntegrable (deriv c) volume s t := by
  obtain ⟨hHab, hcc, hcD⟩ := a35_sub_arc hc.1 hc.2.1 hs ht
  have hsub : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨hs.trans_le hu.1, hu.2.trans_lt ht⟩
  have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
  have hne : ∃ z ∈ unitDisc, φ z ≠ 0 :=
    ⟨c s, hcD (mem_image_of_mem c hsI), (hc.1 s (hsub hsI)).2.2.1⟩
  refine ⟨hcc, (s35v_c_ray_injOn hφ hne hc).mono hsub, fun u hu => (hHab u hu).1, ?_⟩
  -- `√|φ ∘ c| ≥ m₀ > 0` on `[s, t]`
  have hg : ContinuousOn (fun u => Real.sqrt ‖φ (c u)‖) (Icc s t) :=
    Real.continuous_sqrt.comp_continuousOn
      ((hφ.1.continuousOn.comp hcc fun u hu => hcD (mem_image_of_mem c hu)).norm)
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hst.le) hg
  have hm₀ : 0 < Real.sqrt ‖φ (c u₀)‖ := Real.sqrt_pos.2 (norm_pos_iff.2 (hc.1 u₀ (hsub hu₀)).2.2.1)
  have hm0' : ENNReal.ofReal (Real.sqrt ‖φ (c u₀)‖) ≠ 0 := (ENNReal.ofReal_pos.2 hm₀).ne'
  have hfin : ∫⁻ u in Ioo s t, ‖deriv c u‖ₑ < ⊤ := by
    calc ∫⁻ u in Ioo s t, ‖deriv c u‖ₑ
        ≤ ∫⁻ u in Ioo s t, (ENNReal.ofReal (Real.sqrt ‖φ (c u₀)‖))⁻¹ *
            (phiDensity φ (c u) * ‖deriv c u‖ₑ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
          calc ‖deriv c u‖ₑ = (ENNReal.ofReal (Real.sqrt ‖φ (c u₀)‖))⁻¹ *
                (ENNReal.ofReal (Real.sqrt ‖φ (c u₀)‖) * ‖deriv c u‖ₑ) := by
                rw [← mul_assoc, ENNReal.inv_mul_cancel hm0' ENNReal.ofReal_ne_top, one_mul]
            _ ≤ _ := by
                gcongr
                exact ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin u (Ioo_subset_Icc_self hu))
      _ = (ENNReal.ofReal (Real.sqrt ‖φ (c u₀)‖))⁻¹ * rayLength φ c s t :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0')
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hm₀)) hlen
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hst.le]
  exact ⟨(measurable_deriv c).aestronglyMeasurable, hfin⟩

/-- The arc facts transfer to the reversal `τ = c (-·)` on `[-t, -s]`. -/
theorem s35v_c_arc_facts_neg {c τ : ℝ → ℂ} (hτ : ∀ u, τ u = c (-u)) {s t : ℝ}
    (h : ContinuousOn c (Icc s t) ∧ InjOn c (Icc s t) ∧ (∀ u ∈ Ioo s t, DifferentiableAt ℝ c u) ∧
      IntervalIntegrable (deriv c) volume s t) :
    ContinuousOn τ (Icc (-t) (-s)) ∧ InjOn τ (Icc (-t) (-s)) ∧
      (∀ u ∈ Ioo (-t) (-s), DifferentiableAt ℝ τ u) ∧ IntervalIntegrable (deriv τ) volume (-t) (-s) := by
  obtain rfl : τ = fun u => c (-u) := funext hτ
  obtain ⟨hcc, hinj, hdiff, hint⟩ := h
  have hmaps : MapsTo (fun u : ℝ => -u) (Icc (-t) (-s)) (Icc s t) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  refine ⟨hcc.comp continuous_neg.continuousOn hmaps,
    fun x hx y hy hxy => neg_injective (hinj (hmaps hx) (hmaps hy) hxy),
    fun u hu => (hdiff (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).comp u differentiableAt_id.neg, ?_⟩
  have hderiv : deriv (fun u => c (-u)) = fun u => -deriv c (-u) := funext fun u => deriv_comp_neg c u
  rw [hderiv]
  exact ((IntervalIntegrable.iff_comp_neg (f := deriv c) (a := s) (b := t)).1 hint).neg.symm

/-- The `φ`-length of the reversal: `rayLength φ (c (-·)) (-t) (-s) = rayLength φ c s t`. -/
theorem s35v_c_rayLength_neg (φ : ℂ → ℂ) {c τ : ℝ → ℂ} (hτ : ∀ u, τ u = c (-u)) (s t : ℝ) :
    rayLength φ τ (-t) (-s) = rayLength φ c s t := by
  obtain rfl : τ = fun u => c (-u) := funext hτ
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioo s t = Ioo (-t) (-s) := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  calc rayLength φ (fun u => c (-u)) (-t) (-s)
      = ∫⁻ x in (Neg.neg : ℝ → ℝ) ⁻¹' Ioo s t, phiDensity φ (c (-x)) * ‖deriv c (-x)‖ₑ := by
        rw [hpre]
        refine lintegral_congr fun x => ?_
        rw [deriv_comp_neg c x, enorm_neg]
    _ = ∫⁻ y in Ioo s t, phiDensity φ (c y) * ‖deriv c y‖ₑ :=
        (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
          measurableEmbedding_neg (fun y => phiDensity φ (c y) * ‖deriv c y‖ₑ) (Ioo s t)

/-- **Assembly.** Sector crossings `τ|[sₙ, tₙ]` of `buj_openSector (e^{iθ}) α` in the collar, with good sides and
`φ`-lengths tending to `0`, give the conclusion of `s35v_crossing_arcs` (the base point by `s35v_c_base`, the cuts by
`s35v_c_cut`). -/
theorem s35v_c_finish {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c τ : ℝ → ℂ}
    (hτc : τ = c ∨ τ = fun u => c (-u)) {Ψ : ℝ → ℝ} {θ β : ℝ} (hβ0 : 0 < β) (hβπ : β < π)
    (hg₁ : ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * exp (θ * I)) < ⊤)
    (hg₂ : ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * exp (((θ + β : ℝ) : ℂ) * I)) < ⊤)
    {s₁ t₁ : ℕ → ℝ} {k : ℕ → ℤ} (hst : ∀ n, s₁ n < t₁ n)
    (hτ : ∀ n, ContinuousOn τ (Icc (s₁ n) (t₁ n)) ∧ InjOn τ (Icc (s₁ n) (t₁ n)) ∧
      (∀ u ∈ Ioo (s₁ n) (t₁ n), DifferentiableAt ℝ τ u) ∧ IntervalIntegrable (deriv τ) volume (s₁ n) (t₁ n))
    (hpol : ∀ n, ∀ u ∈ Icc (s₁ n) (t₁ n), τ u = ‖τ u‖ * exp (Ψ u * I))
    (hnorm : ∀ n, ∀ u ∈ Icc (s₁ n) (t₁ n), 1 / 2 < ‖τ u‖ ∧ ‖τ u‖ < 1)
    (hΨs : ∀ n, Ψ (s₁ n) = θ + 2 * π * k n) (hΨt : ∀ n, Ψ (t₁ n) = θ + β + 2 * π * k n)
    (hΨ : ∀ n, ∀ u ∈ Ioo (s₁ n) (t₁ n), θ + 2 * π * k n < Ψ u ∧ Ψ u < θ + β + 2 * π * k n)
    (hlen : Tendsto (fun n => rayLength φ τ (s₁ n) (t₁ n)) atTop (𝓝 0)) :
    ∃ (ξ z₀ : ℂ) (α δ : ℝ), 0 < δ ∧ φ z₀ ≠ 0 ∧ ball z₀ δ ⊆ buj_openSector ξ α ∩ ball 0 (1 / 2) ∧
      ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * ξ) < ⊤ ∧
      ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * (ξ * exp (α * I))) < ⊤ ∧
      ∃ τ : ℝ → ℂ, (τ = c ∨ τ = fun u => c (-u)) ∧ ∃ a b s t : ℕ → ℝ,
        (∀ n, buj_IsSectorCut ξ α (a n) (b n) (1 / 2) τ (s n) (t n)) ∧
        Tendsto (fun n => rayLength φ τ (s n) (t n)) atTop (𝓝 0) := by
  obtain ⟨z₀, δ, hδ, hz₀, hball⟩ := s35v_c_base hφ.1 hne (Complex.norm_exp_ofReal_mul_I θ) hβ0 hβπ
  have hexp : exp (θ * I) * exp (β * I) = exp (((θ + β : ℝ) : ℂ) * I) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  refine ⟨exp (θ * I), z₀, β, δ, hδ, hz₀, hball, hg₁, by rw [hexp]; exact hg₂, τ, hτc,
    fun n => ‖τ (s₁ n)‖, fun n => ‖τ (t₁ n)‖, s₁, t₁, fun n => ?_, hlen⟩
  exact s35v_c_cut hβ0 hβπ (hst n) (hτ n) (hpol n) (hnorm n) (hΨs n) (hΨt n) (hΨ n)

/-- **Short crossings of a non-convergent ray.**

Setting: a horizontal ray `c` of `φ ∈ A(Δ)` that does not converge.

Claim: there are
* a sector `buj_openSector ξ α` with `0 < α < π`, whose two sides have finite `φ`-length;
* a base point `z₀` with `φ(z₀) ≠ 0` and `B(z₀, δ)` in the open sector ∩ `B(0, 1/2)`;
* sub-arcs `τ|[sₙ, tₙ]` that are sector cuts at height `1/2`, with `φ`-lengths tending to `0`, where the curve `τ`
  is `c` itself or its reversal `u ↦ c (-u)`.

*Orientation.* `buj_IsSectorCut` fixes the direction of a cut (side `ξ` first). A ray that crosses the
sector only clockwise (its continuous argument tends to `-∞`) has no such sub-arcs of `c`; its cuts are sub-arcs of
the reversal `u ↦ c (-u)` on `[-tₙ, -sₙ]`, with the same `φ`-length. Excluding that case would be Lemma 35.1 itself.

*Truth:* TRUE. The only analytic input beyond the installed tools is the short-tail lemma of s35h.

*Route:*
1. **Late behaviour.** The ray eventually lies in `1/2 < |z| < 1`. It is injective: `fx_arc_shortest_rayLength`
   against a constant comparison curve, together with `a35_rayLength_pos` (scout probe `h21u3_ray_injOn`).
2. **Continuous argument.** Take a continuous argument `Θ` of `c` on `[T, 1)` (the log lifts of `Lemmas/Winding`).
   Since `|c| → 1` and `c` does not converge, `Θ` does not converge. Either it is bounded with `liminf < limsup`, or
   it is unbounded.
3. **Good angles.** By `eq35_1_radii_finite_length`, almost every radius has finite `φ`-length. Pick good
   `θ₁ < θ₂ < θ₁ + π` that are crossed infinitely often (modulo `2π` in the unbounded case). Set `ξ = e^{iθ₁}` and
   `α = θ₂ - θ₁`.
4. **Crossing arcs.** `sₙ` is the last time `Θ = θ₁ (+ 2πk)` before the next time `tₙ` with `Θ = θ₂ (+ 2πk)`.
   Between them `Θ` stays strictly between, so the arc lies in the open sector, and `c(sₙ) = |c(sₙ)| ξ`. In the case
   `Θ → -∞` (the only one in which counterclockwise crossings may run out), use the clockwise crossings (`θ₂ (+ 2πk)`
   first, then `θ₁ (+ 2πk)`) and `τ = c (-·)`.
5. **Integrable derivative.** `√|φ ∘ c|` is bounded below on the compact arc and the `φ`-length is finite, so
   `∫ |c'| < ∞` on `[sₙ, tₙ]`.
6. **Short tails.** `h35_tail_small` (s35h `scout_T/h35_T.lean`, via `circular_arcs_short` and
   `fx_arc_shortest_rayLength`) gives `rayLength φ c sₙ tₙ → 0`.
7. **Base point.** Open sector ∩ `B(0, 1/2)` is open and nonempty. `φ ≢ 0` there by the identity theorem
   (`φ(c(t)) ≠ 0`), which gives `z₀` and `δ`. -/
theorem s35v_crossing_arcs {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {c : ℝ → ℂ} (hc : IsHorizontalRay φ c)
    (hnc : ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ Tendsto c (𝓝[<] 1) (𝓝 ζ)) :
    ∃ (ξ z₀ : ℂ) (α δ : ℝ), 0 < δ ∧ φ z₀ ≠ 0 ∧ ball z₀ δ ⊆ buj_openSector ξ α ∩ ball 0 (1 / 2) ∧
      ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * ξ) < ⊤ ∧
      ∫⁻ r in Ioo (0 : ℝ) 1, phiDensity φ ((r : ℂ) * (ξ * exp (α * I))) < ⊤ ∧
      ∃ τ : ℝ → ℂ, (τ = c ∨ τ = fun u => c (-u)) ∧ ∃ a b s t : ℕ → ℝ,
        (∀ n, buj_IsSectorCut ξ α (a n) (b n) (1 / 2) τ (s n) (t n)) ∧
        Tendsto (fun n => rayLength φ τ (s n) (t n)) atTop (𝓝 0) := by
  have h12 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne : ∃ z ∈ unitDisc, φ z ≠ 0 :=
    ⟨c (1 / 2), hc.2.1 (mem_image_of_mem c h12), (hc.1 (1 / 2) h12).2.2.1⟩
  -- the collar `1/2 < |c| < 1` on `(T, 1)`
  obtain ⟨T₀, hT₀, hcol⟩ := s35v_c_ev_collar hc (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨T, hT0, hT1, hTT₀⟩ : ∃ T : ℝ, 0 < T ∧ T < 1 ∧ T₀ ≤ T :=
    ⟨max T₀ (1 / 2), lt_max_of_lt_right (by norm_num), max_lt hT₀ (by norm_num), le_max_left _ _⟩
  have hsubT : Ioo T 1 ⊆ Ioo 0 1 := Ioo_subset_Ioo_left hT0.le
  have hnormT : ∀ u ∈ Ioo T 1, 1 / 2 < ‖c u‖ ∧ ‖c u‖ < 1 := fun u hu =>
    ⟨hcol u ⟨hTT₀.trans_lt hu.1, hu.2⟩, mem_ball_zero_iff.1 (hc.2.1 (mem_image_of_mem c (hsubT hu)))⟩
  -- a continuous argument `Θ` of `c` on `(T, 1)`; it does not converge, so it oscillates (mod `2π`)
  obtain ⟨Θ, hΘc, hpol⟩ := s35v_c_lift hT1 ((s35v_c_cont hc.1).mono hsubT) fun u hu h0 => by
    have h := (hnormT u hu).1
    rw [h0, norm_zero] at h
    linarith
  obtain ⟨σ, hσ, A, B, hAB, hosc⟩ := s35v_c_osc hT1 (s35v_c_lift_not_tendsto hc hnc hT1 hpol)
  -- two good angles `A < θ₁ < θ₂ < B` with `θ₂ - θ₁ < π`
  obtain ⟨ε, hε, hεB, hεπ⟩ : ∃ ε : ℝ, 0 < ε ∧ 3 * ε ≤ B - A ∧ 3 * ε ≤ π :=
    ⟨min (B - A) π / 3, div_pos (lt_min (sub_pos.2 hAB) Real.pi_pos) (by norm_num),
      by linarith [min_le_left (B - A) π], by linarith [min_le_right (B - A) π]⟩
  obtain ⟨θ₁, hθ₁, hg₁⟩ := s35v_c_good_dense_sign hφ hσ A hε
  obtain ⟨θ₂, hθ₂, hg₂⟩ := s35v_c_good_dense_sign hφ hσ (A + ε) hε
  -- short tails
  obtain ⟨ζ, hζ, hcl⟩ := s35v_c_cluster_exists hc
  have hnt : ¬ Tendsto c (𝓝[<] 1) (𝓝 ζ) := fun h => hnc ⟨ζ, hζ, h⟩
  have htail : ∀ n : ℕ, ∃ t₀ ∈ Ioo (max T 0) 1,
      rayLength φ c t₀ 1 ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    s35v_c_tail_small hφ hne hc hζ hcl hnt (ENNReal.ofReal_pos.2 (by positivity)) hT1
  choose t₀ ht₀ ht₀len using htail
  -- crossings of the levels `θ₁ < θ₂` (mod `2π`) by `σ Θ` after `t₀ n`
  have hcross : ∀ n : ℕ, ∃ s t : ℝ, ∃ k : ℤ, t₀ n < s ∧ s < t ∧ t < 1 ∧ T < s ∧
      σ * Θ s = θ₁ + 2 * π * k ∧ σ * Θ t = θ₂ + 2 * π * k ∧
      ∀ u ∈ Ioo s t, θ₁ + 2 * π * k < σ * Θ u ∧ σ * Θ u < θ₂ + 2 * π * k := by
    intro n
    obtain ⟨p, q, k, hp, hpq, hq1, hpA, hqB⟩ := hosc (t₀ n) (ht₀ n).2
    have hpT : T < p := (le_max_right _ _).trans_lt hp
    have hf : ContinuousOn (fun u => σ * Θ u) (Icc p q) :=
      (continuousOn_const.mul hΘc).mono fun u hu => ⟨hpT.trans_le hu.1, hu.2.trans_lt hq1⟩
    have hlev : θ₁ + 2 * π * k < θ₂ + 2 * π * k := by linarith [hθ₁.2, hθ₂.1]
    have hpf : σ * Θ p ≤ θ₁ + 2 * π * k := by linarith [hθ₁.1]
    have hqf : θ₂ + 2 * π * k ≤ σ * Θ q := by linarith [hθ₂.2]
    obtain ⟨s, t, hps, hst, htq, hfs, hft, hmid⟩ :=
      s35v_c_extract (f := fun u => σ * Θ u) hpq.le hf hlev hpf hqf
    exact ⟨s, t, k, (le_max_left _ _).trans_lt (hp.trans_le hps), hst, htq.trans_lt hq1,
      hpT.trans_le hps, hfs, hft, hmid⟩
  choose s t k hs hst ht hsT hfs hft hmid using hcross
  have hsub : ∀ n, Icc (s n) (t n) ⊆ Ioo T 1 := fun n u hu =>
    ⟨(hsT n).trans_le hu.1, hu.2.trans_lt (ht n)⟩
  have hlen : ∀ n, rayLength φ c (s n) (t n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (s35v_c_rayLength_mono φ c (hs n).le (ht n).le).trans (ht₀len n)
  have hlen0 : Tendsto (fun n => rayLength φ c (s n) (t n)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ENNReal.ofReal_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hlen
  have hfacts : ∀ n, ContinuousOn c (Icc (s n) (t n)) ∧ InjOn c (Icc (s n) (t n)) ∧
      (∀ u ∈ Ioo (s n) (t n), DifferentiableAt ℝ c u) ∧ IntervalIntegrable (deriv c) volume (s n) (t n) :=
    fun n => s35v_c_arc_facts hφ hc (hT0.trans (hsT n)) (hst n) (ht n)
      ((hlen n).trans_lt ENNReal.ofReal_lt_top)
  rcases hσ with rfl | rfl
  · -- counterclockwise crossings: the cuts are sub-arcs of `c` itself
    refine s35v_c_finish hφ hne (Or.inl rfl) (Ψ := Θ) (θ := θ₁) (β := θ₂ - θ₁) (k := k)
      (by linarith [hθ₁.2, hθ₂.1]) (by linarith [hθ₁.1, hθ₂.2]) (by simpa only [one_mul] using hg₁) ?_ hst
      hfacts (fun n u hu => hpol u (hsub n hu)) (fun n u hu => hnormT u (hsub n hu))
      (fun n => by linarith [hfs n]) (fun n => by linarith [hft n])
      (fun n u hu => ⟨by linarith [(hmid n u hu).1], by linarith [(hmid n u hu).2]⟩) hlen0
    rw [show θ₁ + (θ₂ - θ₁) = 1 * θ₂ by ring]
    exact hg₂
  · -- clockwise crossings: the cuts are sub-arcs of the reversal `τ = c (-·)` on `[-tₙ, -sₙ]`
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ → ℂ, ∀ u, τ u = c (-u) := ⟨fun u => c (-u), fun _ => rfl⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, ∀ u, Ψ u = Θ (-u) := ⟨fun u => Θ (-u), fun _ => rfl⟩
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ → ℝ, ∀ n, s' n = -t n := ⟨fun n => -t n, fun _ => rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ℕ → ℝ, ∀ n, t' n = -s n := ⟨fun n => -s n, fun _ => rfl⟩
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ → ℤ, ∀ n, (k' n : ℝ) = -(k n : ℝ) :=
      ⟨fun n => -k n, fun n => by push_cast; ring⟩
    have hmemI : ∀ n, ∀ u ∈ Icc (s' n) (t' n), -u ∈ Icc (s n) (t n) := fun n u hu =>
      ⟨by linarith [hu.2, ht' n], by linarith [hu.1, hs' n]⟩
    have hmemO : ∀ n, ∀ u ∈ Ioo (s' n) (t' n), -u ∈ Ioo (s n) (t n) := fun n u hu =>
      ⟨by linarith [hu.2, ht' n], by linarith [hu.1, hs' n]⟩
    refine s35v_c_finish hφ hne (Or.inr (funext hτ)) (Ψ := Ψ) (θ := -θ₂) (β := θ₂ - θ₁)
      (s₁ := s') (t₁ := t') (k := k')
      (by linarith [hθ₁.2, hθ₂.1]) (by linarith [hθ₁.1, hθ₂.2]) (by simpa only [neg_one_mul] using hg₂) ?_
      (fun n => by linarith [hs' n, ht' n, hst n])
      (fun n => by rw [hs' n, ht' n]; exact s35v_c_arc_facts_neg hτ (hfacts n))
      (fun n u hu => by rw [hτ u, hΨ u]; exact hpol (-u) (hsub n (hmemI n u hu)))
      (fun n u hu => by rw [hτ u]; exact hnormT (-u) (hsub n (hmemI n u hu)))
      (fun n => by rw [hΨ, hs' n, neg_neg, hk' n]; linarith [hft n])
      (fun n => by rw [hΨ, ht' n, neg_neg, hk' n]; linarith [hfs n])
      (fun n u hu => by
        rw [hΨ u, hk' n]
        have h := hmid n (-u) (hmemO n u hu)
        constructor <;> linarith [h.1, h.2])
      (hlen0.congr fun n => by rw [hs' n, ht' n, s35v_c_rayLength_neg φ hτ])
    rw [show -θ₂ + (θ₂ - θ₁) = -1 * θ₁ by ring]
    exact hg₁

/-- **Lemma 35.1, core (proved glue).** A horizontal ray of `φ ∈ A(Δ)` converges to a point of `∂Δ`. Otherwise
`s35v_crossing_arcs` would give sector cuts of `φ`-length tending to `0`, which `buj_no_short_crossings` forbids.

This is the statement of `lemma35_1` without its redundant `hne`. It sits here because the book's order puts
`eq35_2_crossing_arcs`, which uses it, before `lemma35_1`. -/
theorem s35v_ray_converges {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {c : ℝ → ℂ} (hc : IsHorizontalRay φ c) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ Tendsto c (𝓝[<] 1) (𝓝 ζ) := by
  by_contra hnc
  obtain ⟨ξ, z₀, α, δ, hδ, hz₀, hball, hL₁, hL₂, τ, _hτ, a, b, s, t, hcut, hlen⟩ := s35v_crossing_arcs hφ hc hnc
  exact buj_no_short_crossings hφ.1 hδ hz₀ hball hL₁ hL₂ (τ := fun _ => τ) hcut hlen

/-- A late sequence with `arg (c sₙ) = θ` and `c sₙ → ζ ∈ ∂Δ` forces `ζ = e^{iθ}` (s35h `h35_limit_of_arg`). -/
theorem s35v_limit_of_arg {c : ℝ → ℂ} {s : ℕ → ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hs : Tendsto (fun n => c (s n)) atTop (𝓝 ζ)) {θ : ℝ} (harg : ∀ n, arg (c (s n)) = θ) :
    ζ = exp (θ * I) := by
  have h1 : Tendsto (fun n => (‖c (s n)‖ : ℂ) * exp (θ * I)) atTop (𝓝 ((‖ζ‖ : ℂ) * exp (θ * I))) :=
    ((Complex.continuous_ofReal.tendsto _).comp hs.norm).mul_const _
  have h2 : (fun n => (‖c (s n)‖ : ℂ) * exp (θ * I)) = fun n => c (s n) := by
    funext n
    rw [← harg n, norm_mul_exp_arg_mul_I]
  rw [h2, hζ, Complex.ofReal_one, one_mul] at h1
  exact tendsto_nhds_unique hs h1

/-- The reversal `t ↦ c (1 - t)` of a complete trajectory is a horizontal ray (s35h `h35_reverse_ray`). -/
theorem s35v_reverse_ray {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsCompleteTrajectory φ c) :
    IsHorizontalRay φ (fun t => c (1 - t)) := by
  obtain ⟨hH, hD, hK⟩ := hc
  refine ⟨fun t ht => ?_, ?_, fun K hK1 hK2 => ?_⟩
  · have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨hd, hd0, hφ0, him, hre⟩ := hH (1 - t) ht'
    have hdiff : DifferentiableAt ℝ (fun t => c (1 - t)) t :=
      hd.comp t ((differentiableAt_const _).sub differentiableAt_id)
    have hderiv : deriv (fun t => c (1 - t)) t = -deriv c (1 - t) :=
      deriv_comp_const_sub c 1 t
    refine ⟨hdiff, ?_, hφ0, ?_, ?_⟩
    · rw [hderiv]; exact neg_ne_zero.2 hd0
    · rw [hderiv, neg_sq]; exact him
    · rw [hderiv, neg_sq]; exact hre
  · rintro _ ⟨t, ht, rfl⟩
    exact hD (mem_image_of_mem c ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  · have h0 := (hK K hK1 hK2).2
    have hmap : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact sub_pos.2 (mem_Iio.1 ht)
    exact hmap.eventually h0

/-- (35.2): if the ray `α⁺` crossed two radii of finite `φ`-length infinitely often, its sub-arcs `τₙ`
between the two radii would have `φ`-length tending to `0`, forcing `φ ∈ E^{1/2}` of the sector with
boundary values `0` a.e., hence `φ ≡ 0`.

**Correction.**  The hypotheses `hne` (`φ ≢ 0`) and `h₁`, `h₂` (the two radii have finite `φ`-length) were
redundant and are dropped: a horizontal ray already forces `φ ≢ 0` (`φ(c) c'² > 0`), and the conclusion
follows from Lemma 35.1 alone (the ray converges to one point of `∂Δ`, which cannot have both arguments
`θ₁` and `θ₂`).  The statement is thereby slightly stronger than the book's (35.2), and still true. -/
theorem eq35_2_crossing_arcs {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {c : ℝ → ℂ}
    (hc : IsHorizontalRay φ c) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) (hθ₂ : θ₂ < θ₁ + 2 * π) :
    ¬ (∀ t₀ < (1 : ℝ), ∃ s t, t₀ < s ∧ s < t ∧ t < 1 ∧ arg (c s) = θ₁ ∧ arg (c t) = θ₂) := by
  intro H
  obtain ⟨ζ, hζ, hlim⟩ := s35v_ray_converges hφ hc
  have H' : ∀ n : ℕ, ∃ s t, 1 - 1 / ((n : ℝ) + 1) < s ∧ s < t ∧ t < 1 ∧
      arg (c s) = θ₁ ∧ arg (c t) = θ₂ := fun n =>
    H _ (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  choose s t hs hst ht hs₁ ht₂ using H'
  have hseq : ∀ u : ℕ → ℝ, (∀ n : ℕ, 1 - 1 / ((n : ℝ) + 1) < u n ∧ u n < 1) →
      Tendsto u atTop (𝓝[<] 1) := by
    intro u hu
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => (hu n).2)
    have hlow : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hu n).1.le) (fun n => (hu n).2.le)
  have hS := hseq s fun n => ⟨hs n, (hst n).trans (ht n)⟩
  have hT := hseq t fun n => ⟨(hs n).trans (hst n), ht n⟩
  have e₁ := s35v_limit_of_arg hζ (hlim.comp hS) hs₁
  have e₂ := s35v_limit_of_arg hζ (hlim.comp hT) ht₂
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (e₁.symm.trans e₂)
  have hk' : θ₁ = θ₂ + k * (2 * π) := by
    have := congrArg Complex.im hk
    simpa using this
  have hπ := Real.pi_pos
  have hk1 : (k : ℝ) * (2 * π) < 0 := by linarith
  have hk2 : -(2 * π) < (k : ℝ) * (2 * π) := by linarith
  have hkneg : (k : ℝ) < 0 := by nlinarith
  have hkgt : (-1 : ℝ) < k := by nlinarith
  have hk0 : k < 0 := by exact_mod_cast hkneg
  have hkm1 : -1 < k := by exact_mod_cast hkgt
  omega

/-- **Lemma 35.1**: let `ω = φ dz²` be a non-zero holomorphic quadratic differential in `Δ` of finite
norm.  Then every ray `α⁺` of a non-critical horizontal trajectory converges to a point of `∂Δ`
(the limit set `A ⊆ ∂Δ` of the ray cannot be an arc). -/
theorem lemma35_1 {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ}
    (hc : IsHorizontalRay φ c) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ Tendsto c (𝓝[<] 1) (𝓝 ζ) := by
  have _ := hne
  exact s35v_ray_converges hφ hc

/-- **Lemma 35.2**: the two rays `α⁺`, `α⁻` of a non-critical horizontal trajectory of a non-zero
`φ dz²` of finite norm cannot converge to the same boundary point. -/
theorem lemma35_2 {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ}
    (hc : IsCompleteTrajectory φ c) {ζ₁ ζ₂ : ℂ} (h₁ : Tendsto c (𝓝[<] 1) (𝓝 ζ₁)) (h₂ : Tendsto c (𝓝[>] 0) (𝓝 ζ₂)) :
    ζ₁ ≠ ζ₂ := by
  intro hζeq
  rw [← hζeq] at h₂
  obtain ⟨hH, hD, hK⟩ := hc
  have hcont : ContinuousOn c (Ioo 0 1) := fun t ht => (hH t ht).1.continuousAt.continuousWithinAt
  have hζ : ‖ζ₁‖ = 1 := a35_norm_eq_one (F := 𝓝[<] (1 : ℝ))
    (by filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht using hD (mem_image_of_mem c ht))
    (fun K hK1 hK2 => (hK K hK1 hK2).1) h₁
  have hI : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Ioo 0 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)) ((hcont.mono hI).sub continuousOn_const).norm
  have hm₀ : 0 < ‖c t₀ - ζ₁‖ := a35_dist_pos (hD (mem_image_of_mem c (hI ht₀))) hζ
  have hL₀ : 0 < rayLength φ c (1 / 4) (3 / 4) :=
    a35_rayLength_pos hφ.1.continuousOn hH hD (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r, hr, hr0, hLr⟩ := circular_arcs_short hφ hζ
  obtain ⟨n, hn1, hn2⟩ := ((hr0.eventually (gt_mem_nhds hm₀)).and (hLr.eventually (gt_mem_nhds hL₀))).exists
  obtain ⟨b, hb, hbr⟩ := a35_cross_right (f := c) (x₀ := 3 / 4) (by norm_num)
    (hcont.mono fun t ht => ⟨by linarith [ht.1], ht.2⟩) h₁ (hr n).1
    (hn1.le.trans (isMinOn_iff.1 hmin (3 / 4) ⟨by norm_num, le_rfl⟩))
  obtain ⟨a, ha, har⟩ := a35_cross_left (f := c) (x₀ := 1 / 4) (by norm_num)
    (hcont.mono fun t ht => ⟨ht.1, by linarith [ht.2]⟩) h₂ (hr n).1
    (hn1.le.trans (isMinOn_iff.1 hmin (1 / 4) ⟨le_rfl, by norm_num⟩))
  have haD : c a ∈ unitDisc := hD (mem_image_of_mem c ⟨ha.1, by linarith [ha.2]⟩)
  have hbD : c b ∈ unitDisc := hD (mem_image_of_mem c ⟨by linarith [hb.1], hb.2⟩)
  obtain ⟨A, hAlip, hA0, hA1, hAD, hAlen⟩ := a35_arc_exists hζ (hr n).1 har hbr haD hbD
  obtain ⟨hAloc, hAt0, hAt1⟩ := a35_lip_curve hAlip
  obtain ⟨hHab, hcab, hDab⟩ := a35_sub_arc hH hD ha.1 hb.2
  have hab : a < b := by linarith [ha.2, hb.1]
  have key := fx_arc_shortest_rayLength hφ.1 hne hab hHab hcab hDab ⟨A, hAloc⟩
    (fun z hz => hAD (image_mono Ioo_subset_Icc_self hz)) (by rw [← hA0]; exact hAt0)
    (by rw [← hA1]; exact hAt1)
  have hmono : rayLength φ c (1 / 4) (3 / 4) ≤ rayLength φ c a b :=
    lintegral_mono_set (Ioo_subset_Ioo ha.2 hb.1)
  have hlen : phiLength φ ⟨A, hAloc⟩ ≤ ∫⁻ θ in Ioo (0 : ℝ) (2 * π),
      unitDisc.indicator (fun z => phiDensity φ z) (ζ₁ + r n * exp (θ * I)) * ENNReal.ofReal (r n) :=
    hAlen (phiDensity φ)
  exact lt_irrefl _ ((hmono.trans (key.trans hlen)).trans_lt hn2)

/-- §35.1: every non-critical horizontal trajectory of a quadratic differential of finite norm has
two (distinct) end points on `∂Δ`. -/
theorem trajectory_endpoints {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ}
    (hc : IsCompleteTrajectory φ c) :
    ∃ ζ₁ ζ₂ : ℂ, ‖ζ₁‖ = 1 ∧ ‖ζ₂‖ = 1 ∧ ζ₁ ≠ ζ₂ ∧ Tendsto c (𝓝[>] 0) (𝓝 ζ₁) ∧ Tendsto c (𝓝[<] 1) (𝓝 ζ₂) := by
  obtain ⟨ζ₂, hζ₂, h₂⟩ := lemma35_1 hφ hne ⟨hc.1, hc.2.1, fun K hK1 hK2 => (hc.2.2 K hK1 hK2).1⟩
  obtain ⟨ζ₁, hζ₁, h₁'⟩ := lemma35_1 hφ hne (s35v_reverse_ray hc)
  have hmap : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_lt_self 1 (mem_Ioi.1 ht)
  have h₁ : Tendsto c (𝓝[>] 0) (𝓝 ζ₁) := by
    have := h₁'.comp hmap
    refine this.congr fun t => ?_
    simp
  exact ⟨ζ₁, ζ₂, hζ₁, hζ₂, (lemma35_2 hφ hne hc h₂ h₁).symm, h₁, h₂⟩

/-- **Lemma 35.3**: let `φ dz² ≢ 0` be holomorphic in `Δ` with finite norm, `α` a non-critical
horizontal trajectory with end points `ζ₁, ζ₂`.  Every curve `β ⊆ Δ` from `ζ₁` to `ζ₂` has
`φ`-length `≥ l_ω(α)`. -/
theorem lemma35_3 {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ}
    (hc : IsCompleteTrajectory φ c) {ζ₁ ζ₂ : ℂ} (h₁ : Tendsto c (𝓝[>] 0) (𝓝 ζ₁)) (h₂ : Tendsto c (𝓝[<] 1) (𝓝 ζ₂))
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) (hβ₁ : Tendsto β.toFun (𝓝[>] 0) (𝓝 ζ₁))
    (hβ₂ : Tendsto β.toFun (𝓝[<] 1) (𝓝 ζ₂)) : rayLength φ c 0 1 ≤ phiLength φ β := by
  obtain ⟨hH, hD, hK⟩ := hc
  have hζ₁ : ‖ζ₁‖ = 1 := a35_norm_eq_one (F := 𝓝[>] (0 : ℝ))
    (by filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht using hD (mem_image_of_mem c ht))
    (fun K hK1 hK2 => (hK K hK1 hK2).2) h₁
  have hζ₂ : ‖ζ₂‖ = 1 := a35_norm_eq_one (F := 𝓝[<] (1 : ℝ))
    (by filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht using hD (mem_image_of_mem c ht))
    (fun K hK1 hK2 => (hK K hK1 hK2).1) h₂
  have hU : Ioo (0 : ℝ) 1 = ⋃ n : ℕ, Ioo (1 / ((n : ℝ) + 3)) (1 - 1 / ((n : ℝ) + 3)) := by
    ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨hx0, hx1⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hx0 (sub_pos.2 hx1))
      have h3 : 1 / ((n : ℝ) + 3) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      refine ⟨n, ?_, ?_⟩
      · linarith [min_le_left x (1 - x)]
      · linarith [min_le_right x (1 - x)]
    · rintro ⟨n, h1, h2⟩
      have h0 : 0 < 1 / ((n : ℝ) + 3) := by positivity
      constructor <;> linarith
  have hdir : Directed (· ⊆ ·) fun n : ℕ => Ioo (1 / ((n : ℝ) + 3)) (1 - 1 / ((n : ℝ) + 3)) := by
    refine Monotone.directed_le fun n m hnm => Ioo_subset_Ioo ?_ ?_
    · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 3)
    · have h := one_div_le_one_div_of_le (a := (n : ℝ) + 3) (b := (m : ℝ) + 3) (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 3)
      linarith
  show ∫⁻ t in Ioo 0 1, phiDensity φ (c t) * ‖deriv c t‖ₑ ≤ phiLength φ β
  rw [hU, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun n => ?_
  have h0 : 0 < 1 / ((n : ℝ) + 3) := by positivity
  have h1 : 1 / ((n : ℝ) + 3) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  exact a35_key hφ hne hH hD hζ₁ hζ₂ h₁ h₂ β hβ hβ₁ hβ₂ h0 (by linarith) (by linarith)

/-! ## §35.2 The Reich–Strebel main inequality -/

/-- (35.4): the stretching function `λ_{g,ω}(z) = lim l_ω(g(τ))/l_ω(τ)` over horizontal arcs `τ ∋ z`
of length `→ 0`; at points of differentiability `λ_{g,ω} = |∂g̃/∂ξ|` in the natural parameter, with the
local expression `|φ(g(z))|^{1/2} |∂_z g + ∂_z̄ g · φ/|φ|| · |φ(z)|^{-1/2}`. -/
def lambdaStretchDisc (φ g : ℂ → ℂ) (z : ℂ) : ℝ := lambdaStretchPlane φ φ g z

/-- (35.3)–(35.5): for `f`, `f₀` quasiconformal self-maps of `Δ` with the same boundary values and
`g = f⁻¹ ∘ f₀`, the image `g(α)` of a non-critical trajectory has the same end points, so
`∫_α |φ|^{1/2}|dz| ≤ ∫_{g(α)} |φ|^{1/2}|dz| = ∫_α λ_{g,ω} |φ|^{1/2}|dz|` (35.5); integrating over the
strips swept by the trajectories gives `∬_Δ |φ| ≤ ∬_Δ |φ| λ_{g,ω}`. -/
theorem eq35_5_integrated {f f₀ : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) (hf₀ : IsQuasiconformal f₀ unitDisc)
    (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc) {F F₀ : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f unitDisc unitDisc F) (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀)
    (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) :
    phiArea φ unitDisc ≤ ∫⁻ z in unitDisc,
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchDisc φ (Function.invFunOn f unitDisc ∘ f₀) z) := by
  exact fx_eq35_5 hf hf₀ hfs hf₀s hF hF₀ hbd hφ

/-- The quantities of the main inequality: `κ = μ_{f₀}`, `κ₁ = μ_{f⁻¹} ∘ f₀`, `τ = conj(∂_z f₀)/∂_z f₀`. -/
def mainIneqKappa (f₀ : ℂ → ℂ) (z : ℂ) : ℂ := complexDilatation f₀ z

/-- `κ₁ = μ_{f⁻¹} ∘ f₀`. -/
def mainIneqKappa₁ (f f₀ : ℂ → ℂ) (z : ℂ) : ℂ := complexDilatation (Function.invFunOn f unitDisc) (f₀ z)

/-- `τ = conj(∂_z f₀)/∂_z f₀`. -/
def mainIneqTau (f₀ : ℂ → ℂ) (z : ℂ) : ℂ := conj (dz f₀ z) / dz f₀ z

/-- §35.2: the pointwise relation behind the main inequality is in fact an **identity**.

Both sides equal `|（1 + κw) + κ₁τw(1 + κ̄w̄)|²/((1 - |κ|²)(1 - |κ₁|²))`: for the left-hand side
because `1 - |μ_g|² = (1 - |κ|²)(1 - |κ₁|²)/|1 + κ̄κ₁τ|²` (the composition identity for complex
dilatations), and for the right-hand side after cancelling `|1 + κw|²`.  The two numerators agree
because `ww̄ = 1` turns `κ̄κ₁τ` into `κ₁τwκ̄w̄`.

The book states only the inequality, which it obtains by bounding the exact denominator below;
the exact form is recorded here because it is what makes the statement provable. -/
theorem main_inequality_pointwise_eq {κ κ₁ τ w : ℂ} (hκ : ‖κ‖ < 1) (hκ₁ : ‖κ₁‖ < 1)
    (hτ : ‖τ‖ = 1) (hw : ‖w‖ = 1) :
    ‖1 + (κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ) * w‖ ^ 2 / (1 - ‖(κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ)‖ ^ 2) =
      (‖1 + κ * w‖ ^ 2 / (1 - ‖κ‖ ^ 2)) *
        (‖1 + κ₁ * τ * w * (1 + conj κ * conj w) / (1 + κ * w)‖ ^ 2 / (1 - ‖κ₁‖ ^ 2)) := by
  -- `|τ| = |w| = 1` in the form needed by `ring`
  have hττ : τ * conj τ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hτ]; norm_num
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  -- the two denominators do not vanish
  have hA : (1 : ℂ) + κ * w ≠ 0 := by
    intro h
    have h1 : ‖κ * w‖ = 1 := by
      rw [show κ * w = -1 by linear_combination h]; simp
    rw [norm_mul, hw, mul_one] at h1
    exact absurd h1 (by linarith)
  have hB : (1 : ℂ) + conj κ * κ₁ * τ ≠ 0 := by
    intro h
    have h1 : ‖conj κ * κ₁ * τ‖ = 1 := by
      rw [show conj κ * κ₁ * τ = -1 by linear_combination h]; simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hτ, mul_one] at h1
    nlinarith [norm_nonneg κ, norm_nonneg κ₁]
  have hB' : (1 : ℂ) + κ₁ * τ * conj κ ≠ 0 := by
    intro h
    exact hB (by linear_combination h)
  have hAn : Complex.normSq (1 + κ * w) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hA
  have hBn : Complex.normSq (1 + conj κ * κ₁ * τ) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hB
  have hBn' : Complex.normSq (1 + κ₁ * τ * conj κ) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hB'
  have hnκ : 1 - Complex.normSq κ ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg κ]
  have hnκ₁ : 1 - Complex.normSq κ₁ ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg κ₁]
  -- the composition identity for complex dilatations
  have key3C : (1 + conj κ * κ₁ * τ) * conj (1 + conj κ * κ₁ * τ)
      - (κ + κ₁ * τ) * conj (κ + κ₁ * τ)
      = (1 - κ * conj κ) * (1 - κ₁ * conj κ₁) := by
    simp only [map_add, map_mul, map_one, Complex.conj_conj]
    linear_combination (κ * conj κ * κ₁ * conj κ₁ - κ₁ * conj κ₁) * hττ
  have key3 : Complex.normSq (1 + conj κ * κ₁ * τ) - Complex.normSq (κ + κ₁ * τ)
      = (1 - Complex.normSq κ) * (1 - Complex.normSq κ₁) := by
    have h := key3C
    rw [Complex.mul_conj, Complex.mul_conj, Complex.mul_conj, Complex.mul_conj] at h
    exact_mod_cast h
  -- the two numerators are the same complex number, because `ww̄ = 1`
  have hcore : (1 + conj κ * κ₁ * τ) + (κ + κ₁ * τ) * w
      = (1 + κ * w) + κ₁ * τ * w * (1 + conj κ * conj w) := by
    linear_combination (-(conj κ * κ₁ * τ)) * hww
  simp only [← Complex.normSq_eq_norm_sq]
  have e1 : (1 : ℂ) + (κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ) * w
      = ((1 + κ * w) + κ₁ * τ * w * (1 + conj κ * conj w)) / (1 + conj κ * κ₁ * τ) := by
    rw [← hcore]
    field_simp
  have e2 : 1 - Complex.normSq ((κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ))
      = (1 - Complex.normSq κ) * (1 - Complex.normSq κ₁)
        / Complex.normSq (1 + conj κ * κ₁ * τ) := by
    rw [Complex.normSq_div, ← key3, sub_div, div_self hBn]
  have e3 : (1 : ℂ) + κ₁ * τ * w * (1 + conj κ * conj w) / (1 + κ * w)
      = ((1 + κ * w) + κ₁ * τ * w * (1 + conj κ * conj w)) / (1 + κ * w) := by
    rw [add_div, div_self hA]
  rw [e1, e2, e3, Complex.normSq_div, Complex.normSq_div]
  field_simp

/-- AM–GM for the split of `|φ| λ`: `p (√q D/√p) ≤ (q J + p D²/J)/2` for `p, q ≥ 0`, `J > 0`. -/
theorem m35_amgm {p q J D : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hJ : 0 < J) :
    p * (Real.sqrt q * D / Real.sqrt p) ≤ (q * J + p * (D ^ 2 / J)) / 2 := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_mul]
    positivity
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hpos
  have hsJ : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hpp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hqq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hJJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ.le
  set x := Real.sqrt q * Real.sqrt J
  set y := Real.sqrt p * D / Real.sqrt J
  have hxy : p * (Real.sqrt q * D / Real.sqrt p) = x * y := by
    calc p * (Real.sqrt q * D / Real.sqrt p) = (p / Real.sqrt p) * Real.sqrt q * D := by ring
      _ = Real.sqrt p * Real.sqrt q * D := by rw [Real.div_sqrt]
      _ = x * y := by
          simp only [x, y]
          field_simp
  have hx2 : x ^ 2 = q * J := by simp only [x]; rw [mul_pow, hqq, hJJ]
  have hy2 : y ^ 2 = p * (D ^ 2 / J) := by
    simp only [y]
    rw [div_pow, mul_pow, hpp, hJJ]
    ring
  rw [hxy, ← hx2, ← hy2]
  nlinarith [sq_nonneg (x - y)]

/-- The pointwise identity behind (35.5) ⟹ (35.3): with `∂g = G(1 + κ̄κ₁τ)`, `∂̄g = G(κ + κ₁τ)`,
`|∂g - ∂̄g v|²/J_g` is the main-inequality integrand (`main_inequality_pointwise_eq` with `w = -v`). -/
theorem m35_E_eq_AB {κ κ₁ τ v G : ℂ} (hκ : ‖κ‖ < 1) (hκ₁ : ‖κ₁‖ < 1) (hτ : ‖τ‖ = 1) (hv : ‖v‖ = 1)
    (hG : G ≠ 0) :
    ‖G * (1 + conj κ * κ₁ * τ) - G * (κ + κ₁ * τ) * v‖ ^ 2 /
        (‖G * (1 + conj κ * κ₁ * τ)‖ ^ 2 - ‖G * (κ + κ₁ * τ)‖ ^ 2) =
      (‖1 - κ * v‖ ^ 2 / (1 - ‖κ‖ ^ 2)) *
        (‖1 - κ₁ * τ * v * (1 - conj κ * conj v) / (1 - κ * v)‖ ^ 2 / (1 - ‖κ₁‖ ^ 2)) := by
  have h1c : (1 : ℂ) + conj κ * κ₁ * τ ≠ 0 := by
    intro h
    have h1 : ‖conj κ * κ₁ * τ‖ = 1 := by
      rw [show conj κ * κ₁ * τ = -1 by linear_combination h]; simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hτ, mul_one] at h1
    nlinarith [norm_nonneg κ, norm_nonneg κ₁]
  have key := main_inequality_pointwise_eq hκ hκ₁ hτ (show ‖-v‖ = 1 by rw [norm_neg, hv])
  have e1 : (1 : ℂ) + κ * -v = 1 - κ * v := by ring
  have e2 : (1 : ℂ) + κ₁ * τ * -v * (1 + conj κ * conj (-v)) / (1 + κ * -v) =
      1 - κ₁ * τ * v * (1 - conj κ * conj v) / (1 - κ * v) := by
    rw [map_neg]
    ring
  rw [e2, e1] at key
  rw [← key]
  set c := (1 : ℂ) + conj κ * κ₁ * τ with hc
  set m := κ + κ₁ * τ with hm
  have hGc : G * c ≠ 0 := mul_ne_zero hG h1c
  have eL : G * c - G * m * v = (G * c) * (1 + m / c * -v) := by
    field_simp
    ring
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 h1c
  have eD : ‖G * c‖ ^ 2 - ‖G * m‖ ^ 2 = ‖G * c‖ ^ 2 * (1 - ‖m / c‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_mul]
    field_simp
  rw [eL, eD, norm_mul, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hGc))]

/-- The chain rule for `g = a ∘ f₀` in main-inequality form: `∂g = G(1 + κ̄κ₁τ)`, `∂̄g = G(κ + κ₁τ)`,
`G = ∂a(f₀ z) ∂f₀(z)`, `κ = μ_{f₀}(z)`, `κ₁ = μ_a(f₀ z)`, `τ = conj ∂f₀/∂f₀`. -/
theorem m35_chain_mainIneq {a f₀ : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ f₀ z)
    (ha : DifferentiableAt ℝ a (f₀ z)) (hd0 : dz f₀ z ≠ 0) (ha0 : dz a (f₀ z) ≠ 0) :
    dz (a ∘ f₀) z = (dz a (f₀ z) * dz f₀ z) * (1 + conj (complexDilatation f₀ z) *
        complexDilatation a (f₀ z) * (conj (dz f₀ z) / dz f₀ z)) ∧
      dzbar (a ∘ f₀) z = (dz a (f₀ z) * dz f₀ z) * (complexDilatation f₀ z +
        complexDilatation a (f₀ z) * (conj (dz f₀ z) / dz f₀ z)) := by
  have h1 := eq6_2_dz_comp hd ha
  have h2 := eq6_2_dzbar_comp hd ha
  obtain ⟨e1, e2⟩ := eq6_3 hd
  rw [← e2] at h1
  rw [← e1] at h2
  have hc0 : conj (dz f₀ z) ≠ 0 := (map_ne_zero _).2 hd0
  constructor
  · rw [h1]
    simp only [complexDilatation, map_div₀]
    field_simp
  · rw [h2]
    simp only [complexDilatation]
    field_simp

/-- `‖μ‖ < 1` and `∂g ≠ 0` where the Jacobian is positive. -/
theorem m35_norm_cd_lt_one {g : ℂ → ℂ} {w : ℂ} (hJ : 0 < jacobian g w) :
    ‖complexDilatation g w‖ < 1 ∧ dz g w ≠ 0 := by
  unfold jacobian at hJ
  have hlt : ‖dzbar g w‖ < ‖dz g w‖ := by
    nlinarith [norm_nonneg (dz g w), norm_nonneg (dzbar g w)]
  have hp : 0 < ‖dz g w‖ := (norm_nonneg _).trans_lt hlt
  refine ⟨?_, norm_pos_iff.1 hp⟩
  rw [complexDilatation, norm_div, div_lt_one hp]
  exact hlt

/-- Transfer of a.e. statements through a q.c. self-map `f₀` of `Δ` (Lusin (N) for `f₀⁻¹`). -/
theorem m35_ae_comp {f₀ : ℂ → ℂ} {K₀ : ℝ} (hK₀ : IsKQC f₀ unitDisc K₀)
    (hf₀s : f₀ '' unitDisc = unitDisc) {P : ℂ → Prop} (hP : ∀ᵐ w ∂(volume.restrict unitDisc), P w) :
    ∀ᵐ z ∂(volume.restrict unitDisc), P (f₀ z) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  rw [ae_restrict_iff' hΔ, ae_iff] at hP
  set N : Set ℂ := {w | ¬ (w ∈ unitDisc → P w)} with hN
  have hNsub : N ⊆ f₀ '' unitDisc := by
    intro w hw'
    rw [hf₀s]
    by_contra h
    exact hw' (fun h' => absurd h' h)
  have hnull : volume (Function.invFunOn f₀ unitDisc '' N) = 0 :=
    ac_n_volume_image_null_of_isKQC (thm7_2_inv hK₀) hNsub hP
  have hleft : LeftInvOn (Function.invFunOn f₀ unitDisc) f₀ unitDisc :=
    hK₀.2.2.1.2.1.leftInvOn_invFunOn
  rw [ae_restrict_iff' hΔ]
  filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzΔ
  have hf₀z : f₀ z ∈ unitDisc := hf₀s ▸ mem_image_of_mem f₀ hzΔ
  by_contra hcon
  exact hz ⟨f₀ z, fun h => hcon (h hf₀z), hleft hzΔ⟩

/-- **§35.2 (Reich–Strebel 主要不等式).**  For quasiconformal self-maps `f`, `f₀` of `Δ` with the same
boundary values, and every holomorphic `φ` of finite norm,
`∬|φ| ≤ ∬ |φ| · |1 - κφ/|φ||²/(1 - |κ|²) · |1 - κ₁τ(φ/|φ|)(1 - κ̄φ̄/|φ|)/(1 - κφ/|φ|)|²/(1 - |κ₁|²)`
with `κ = μ_{f₀}`, `κ₁ = μ_{f⁻¹} ∘ f₀`, `τ = conj ∂_z f₀/∂_z f₀`: the product is exactly
`|1 - μ_g φ/|φ||²/(1 - |μ_g|²)` for `g = f⁻¹ ∘ f₀`, `μ_g = (κ + κ₁τ)/(1 + κ̄κ₁τ)`
(`main_inequality_pointwise_eq` with `w = -φ/|φ|`).

**Correction.**  The `κ₁` term previously lacked the factor `φ/|φ|` (the same omission as the one
corrected in `main_inequality_pointwise`), and the statement was **false**: for `f₀ = id` the
integrand is `|φ| |1 + κ₁|²/(1 - |κ₁|²)`, and for `f⁻¹ = z + εV` (`V` smooth with compact support) its
integral is `∬|φ| - 2ε Re ∬ ∂_z̄|φ| · V + O(ε²)`, which is `< ∬|φ|` for suitable `V` whenever `|φ|` is not
constant. -/
theorem thm35_2_main_inequality {f f₀ : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc)
    (hf₀ : IsQuasiconformal f₀ unitDisc) (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc)
    {F F₀ : ExtPlane → ExtPlane} (hF : IsHomeoExtension f unitDisc unitDisc F)
    (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀) (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableQD) :
    phiArea φ unitDisc ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ *
      (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) *
      (‖1 - mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ z / ‖φ z‖) *
          (1 - conj (mainIneqKappa f₀ z) * conj (φ z) / ‖φ z‖) /
          (1 - mainIneqKappa f₀ z * φ z / ‖φ z‖)‖ ^ 2 / (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2))) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hareaψ : phiArea (fun z => -φ z) unitDisc = phiArea φ unitDisc := by simp [phiArea]
  have hψ : (fun z => -φ z) ∈ integrableQD := ⟨hφ.1.neg, by rw [hareaψ]; exact hφ.2⟩
  have h5 := eq35_5_integrated hf hf₀ hfs hf₀s hF hF₀ hbd hψ
  rw [hareaψ] at h5
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K₀, hK₀⟩ := hf₀
  set a := Function.invFunOn f unitDisc with hadef
  have haK : IsKQC a unitDisc K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hfi : InjOn f unitDisc := hK.2.2.1.2.1
  have hgK : IsKQC (a ∘ f₀) unitDisc (K₀ * K) := thm7_1_comp hK₀ haK hf₀s.subset
  have hgimg : (a ∘ f₀) '' unitDisc = unitDisc := by
    rw [image_comp, hf₀s]
    conv_lhs => rw [← hfs]
    exact hfi.leftInvOn_invFunOn.image_image
  have hgmaps : MapsTo (a ∘ f₀) unitDisc unitDisc := fun z hz => hgimg ▸ mem_image_of_mem _ hz
  set g := a ∘ f₀ with hgdef
  have hφc : ContinuousOn φ unitDisc := hφ.1.continuousOn
  have hφg : ContinuousOn (fun z => φ (g z)) unitDisc := hφc.comp hgK.2.2.1.1 hgmaps
  have hJm : Measurable (jacobian g) :=
    ((measurable_dz g).norm.pow_const 2).sub ((measurable_dzbar g).norm.pow_const 2)
  have hJpos := thm9_6_cor2_jacobian_pos hgK
  set X : ℂ → ℝ := fun z => ‖φ (g z)‖ * jacobian g z with hX
  set Ev : ℂ → ℝ := fun z => ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 / jacobian g z with hEv
  have hXm : AEMeasurable (fun z => ENNReal.ofReal (X z)) (volume.restrict unitDisc) :=
    ((hφg.norm.aestronglyMeasurable hΔ).aemeasurable.mul hJm.aemeasurable).ennreal_ofReal
  -- step 1: AM–GM pointwise
  have hstep1 : ∀ᵐ z ∂(volume.restrict unitDisc),
      2 * (ENNReal.ofReal ‖-φ z‖ * ENNReal.ofReal (lambdaStretchDisc (fun z => -φ z) g z)) ≤
        ENNReal.ofReal (X z) + ENNReal.ofReal (‖φ z‖ * Ev z) := by
    filter_upwards [hJpos] with z hJ
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    have hlam : lambdaStretchDisc (fun z => -φ z) g z =
        Real.sqrt ‖φ (g z)‖ * ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ / Real.sqrt ‖φ z‖ := by
      simp only [lambdaStretchDisc, lambdaStretchPlane, norm_neg]
      congr 3
      ring
    rw [hlam, norm_neg]
    have h := m35_amgm (norm_nonneg (φ z)) (norm_nonneg (φ (g z))) hJ
      (D := ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖)
    have hX0 : 0 ≤ X z := mul_nonneg (norm_nonneg _) hJ.le
    have hE0 : 0 ≤ ‖φ z‖ * Ev z := mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) hJ.le)
    rw [← ENNReal.ofReal_add hX0 hE0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    show 2 * (‖φ z‖ * (Real.sqrt ‖φ (g z)‖ * ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ /
      Real.sqrt ‖φ z‖)) ≤ ‖φ (g z)‖ * jacobian g z +
        ‖φ z‖ * (‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 / jacobian g z)
    linarith
  -- step 2: change of variables in the first half
  have hstep3 : ∫⁻ z in unitDisc, ENNReal.ofReal (X z) = phiArea φ unitDisc := by
    have hcv := fx_lintegral_image_eq hgK (fun w => ENNReal.ofReal ‖φ w‖)
    rw [hgimg] at hcv
    rw [phiArea, hcv]
    refine lintegral_congr_ae ?_
    filter_upwards [hJpos] with z hJ
    show ENNReal.ofReal (‖φ (g z)‖ * jacobian g z) = _
    rw [ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  -- step 3: the second half is the main-inequality integrand (chain rule + pointwise identity)
  have hda := m35_ae_comp hK₀ hf₀s
    ((thm9_3_differentiable_ae haK).and (thm9_6_cor2_jacobian_pos haK))
  have hstep4 : ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ * Ev z) =
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ *
        (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) *
        (‖1 - mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ z / ‖φ z‖) *
            (1 - conj (mainIneqKappa f₀ z) * conj (φ z) / ‖φ z‖) /
            (1 - mainIneqKappa f₀ z * φ z / ‖φ z‖)‖ ^ 2 / (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2))) := by
    refine lintegral_congr_ae ?_
    filter_upwards [thm9_3_differentiable_ae hK₀, thm9_6_cor2_jacobian_pos hK₀, hda]
      with z hdz hJz hdaz
    obtain ⟨hdaz, hJaz⟩ := hdaz
    congr 1
    by_cases hp : φ z = 0
    · simp [hp]
    obtain ⟨hκ, hd0⟩ := m35_norm_cd_lt_one hJz
    obtain ⟨hκ₁, ha0⟩ := m35_norm_cd_lt_one hJaz
    obtain ⟨hdzg, hdbzg⟩ := m35_chain_mainIneq hdz hdaz hd0 ha0
    have hτ : ‖conj (dz f₀ z) / dz f₀ z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hd0)]
    have hv : ‖φ z / (‖φ z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hp).ne']
    have hG : dz a (f₀ z) * dz f₀ z ≠ 0 := mul_ne_zero ha0 hd0
    have key := m35_E_eq_AB hκ hκ₁ hτ hv hG
    have hEz : Ev z = ‖dz g z - dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 /
        (‖dz g z‖ ^ 2 - ‖dzbar g z‖ ^ 2) := rfl
    rw [hEz, hdzg, hdbzg, key]
    have hconjv : conj (φ z / (‖φ z‖ : ℂ)) = conj (φ z) / (‖φ z‖ : ℂ) := by
      rw [map_div₀, Complex.conj_ofReal]
    rw [hconjv]
    simp only [mainIneqKappa, mainIneqKappa₁, mainIneqTau, mul_div_assoc]
    ring
  -- step 4: conclude
  have hPtop : phiArea φ unitDisc ≠ ⊤ := hφ.2.ne
  have hmain : 2 * phiArea φ unitDisc ≤ phiArea φ unitDisc +
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ * Ev z) := by
    calc 2 * phiArea φ unitDisc
        ≤ 2 * ∫⁻ z in unitDisc, ENNReal.ofReal ‖-φ z‖ *
            ENNReal.ofReal (lambdaStretchDisc (fun z => -φ z) g z) := by gcongr
      _ = ∫⁻ z in unitDisc, 2 * (ENNReal.ofReal ‖-φ z‖ *
            ENNReal.ofReal (lambdaStretchDisc (fun z => -φ z) g z)) :=
          (lintegral_const_mul' _ _ (by simp)).symm
      _ ≤ ∫⁻ z in unitDisc, (ENNReal.ofReal (X z) + ENNReal.ofReal (‖φ z‖ * Ev z)) :=
          lintegral_mono_ae hstep1
      _ = phiArea φ unitDisc + ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ * Ev z) := by
          rw [lintegral_add_left' hXm, hstep3]
  rw [hstep4, two_mul] at hmain
  exact (ENNReal.add_le_add_iff_left hPtop).1 hmain

/-- For `f, f₀` q.c. self-maps of `Δ`, `|κ₁| = |μ_{f⁻¹} ∘ f₀| ≤ (K - 1)/(K + 1)` a.e. on `Δ` when `f` is
`K`-q.c.: `f⁻¹` is `K`-q.c. (Theorem 7.2), and the exceptional null set pulls back under `f₀` to the
image of a null set under the q.c. map `f₀⁻¹`, which is null (Lusin (N)). -/
theorem m35_kappa1_ae_le {f f₀ : ℂ → ℂ} {K K₀ : ℝ} (hK : IsKQC f unitDisc K)
    (hK₀ : IsKQC f₀ unitDisc K₀) (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc) :
    ∀ᵐ z ∂(volume.restrict unitDisc), ‖mainIneqKappa₁ f f₀ z‖ ≤ (K - 1) / (K + 1) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hinv : IsKQC (Function.invFunOn f unitDisc) unitDisc K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hw := (isKQC_maxDilatation_le hinv).2
  rw [ae_restrict_iff' hΔ, ae_iff] at hw
  set N : Set ℂ := {w | ¬ (w ∈ unitDisc →
    ‖complexDilatation (Function.invFunOn f unitDisc) w‖ ≤ (K - 1) / (K + 1))} with hN
  have hNsub : N ⊆ f₀ '' unitDisc := by
    intro w hw'
    rw [hf₀s]
    by_contra h
    exact hw' (fun h' => absurd h' h)
  have hnull : volume (Function.invFunOn f₀ unitDisc '' N) = 0 :=
    ac_n_volume_image_null_of_isKQC (thm7_2_inv hK₀) hNsub hw
  have hleft : LeftInvOn (Function.invFunOn f₀ unitDisc) f₀ unitDisc :=
    hK₀.2.2.1.2.1.leftInvOn_invFunOn
  rw [ae_restrict_iff' hΔ]
  filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzΔ
  have hf₀z : f₀ z ∈ unitDisc := hf₀s ▸ mem_image_of_mem f₀ hzΔ
  by_contra hcon
  apply hz
  refine ⟨f₀ z, ?_, hleft hzΔ⟩
  intro h
  exact hcon (h hf₀z)

/-- `|conj a / a| ≤ 1`. -/
theorem m35_norm_conj_div_le_one (a : ℂ) : ‖conj a / a‖ ≤ 1 := by
  rw [norm_div, Complex.norm_conj]
  exact div_self_le_one _

/-- `|a / |a|| ≤ 1`. -/
theorem m35_norm_div_norm_le_one (a : ℂ) : ‖a / (‖a‖ : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

/-- The pointwise bound for the second factor: `|1 - κ₁ u|²/(1 - |κ₁|²) ≤ (1 + c)/(1 - c)` for
`|κ₁| ≤ c < 1`, `|u| ≤ 1`. -/
theorem m35_second_factor_le {κ₁ u : ℂ} {c : ℝ} (hc : c < 1) (hκ₁ : ‖κ₁‖ ≤ c) (hu : ‖u‖ ≤ 1) :
    ‖1 - κ₁ * u‖ ^ 2 / (1 - ‖κ₁‖ ^ 2) ≤ (1 + c) / (1 - c) := by
  have ht0 := norm_nonneg κ₁
  have hc0 : 0 ≤ c := ht0.trans hκ₁
  have hden : 0 < 1 - ‖κ₁‖ ^ 2 := by nlinarith
  have hnum : ‖1 - κ₁ * u‖ ≤ 1 + ‖κ₁‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul]
    nlinarith [norm_nonneg u]
  have hsq : ‖1 - κ₁ * u‖ ^ 2 ≤ (1 + ‖κ₁‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnum 2
  rw [div_le_div_iff₀ hden (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ 1 - c),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖κ₁‖) (sub_nonneg.2 hκ₁)]

/-- The second factor of the main inequality is `≤ (1 + c)/(1 - c)` when `|κ₁| ≤ c < 1`. -/
theorem m35_mainIneq_second_le {κ κ₁ τ p : ℂ} {c : ℝ} (hc : c < 1) (hκ₁ : ‖κ₁‖ ≤ c) (hτ : ‖τ‖ ≤ 1) :
    ‖1 - κ₁ * τ * (p / ‖p‖) * (1 - conj κ * conj p / ‖p‖) / (1 - κ * p / ‖p‖)‖ ^ 2 /
      (1 - ‖κ₁‖ ^ 2) ≤ (1 + c) / (1 - c) := by
  have hconj : (1 - conj κ * conj p / (‖p‖ : ℂ)) = conj (1 - κ * p / (‖p‖ : ℂ)) := by
    simp [map_sub, map_div₀, map_mul, Complex.conj_ofReal]
  have hr : ‖(1 - conj κ * conj p / (‖p‖ : ℂ)) / (1 - κ * p / (‖p‖ : ℂ))‖ ≤ 1 := by
    rw [hconj]
    exact m35_norm_conj_div_le_one _
  have e : κ₁ * τ * (p / ‖p‖) * (1 - conj κ * conj p / ‖p‖) / (1 - κ * p / ‖p‖) =
      κ₁ * (τ * (p / ‖p‖) * ((1 - conj κ * conj p / (‖p‖ : ℂ)) / (1 - κ * p / (‖p‖ : ℂ)))) := by
    ring
  rw [e]
  refine m35_second_factor_le hc hκ₁ ?_
  rw [norm_mul, norm_mul]
  have hv := m35_norm_div_norm_le_one p
  calc ‖τ‖ * ‖p / (‖p‖ : ℂ)‖ * ‖(1 - conj κ * conj p / (‖p‖ : ℂ)) / (1 - κ * p / (‖p‖ : ℂ))‖
      ≤ 1 * 1 * 1 := by
        gcongr
    _ = 1 := by norm_num

/-- §35.2 (the simplified main inequality): `∬|φ| ≤ K[f] ∬ |φ| |1 - κφ/|φ||²/(1 - |κ|²)`. -/
theorem main_inequality_simplified {f f₀ : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc)
    (hf₀ : IsQuasiconformal f₀ unitDisc) (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc)
    {F F₀ : ExtPlane → ExtPlane} (hF : IsHomeoExtension f unitDisc unitDisc F)
    (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀) (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableQD) :
    phiArea φ unitDisc ≤ maxDilatation f unitDisc * ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ *
      (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2))) := by
  have hmain := thm35_2_main_inequality hf hf₀ hfs hf₀s hF hF₀ hbd hφ
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K₀, hK₀⟩ := hf₀
  obtain ⟨hK1, hK1q⟩ := UniversalTeichmuller.ut_md_isKQC_toReal hK ⟨0, by simp [unitDisc]⟩
  have hfin : maxDilatation f unitDisc ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK).1
  set K₁ := (maxDilatation f unitDisc).toReal with hK₁
  have hc1 : (K₁ - 1) / (K₁ + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hcK : (1 + (K₁ - 1) / (K₁ + 1)) / (1 - (K₁ - 1) / (K₁ + 1)) = K₁ := by
    field_simp
    ring
  have hκ₁ := m35_kappa1_ae_le hK1q hK₀ hfs hf₀s
  have hK₀1 : (1 : ℝ) ≤ K₀ := hK₀.2.1
  have hκ : ∀ᵐ z ∂(volume.restrict unitDisc), ‖mainIneqKappa f₀ z‖ < 1 := by
    filter_upwards [(isKQC_maxDilatation_le hK₀).2] with z hz
    exact hz.trans_lt ((div_lt_one (by linarith)).2 (by linarith))
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_toReal hfin, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hκ₁, hκ] with z h1 h2
  rw [← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA : 0 ≤ ‖φ z‖ * (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 /
      (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) :=
    mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _)
      (by nlinarith [norm_nonneg (mainIneqKappa f₀ z)]))
  have hB := m35_mainIneq_second_le (κ := mainIneqKappa f₀ z) (p := φ z) hc1 h1
    (m35_norm_conj_div_le_one (dz f₀ z))
  rw [hcK] at hB
  calc _ ≤ ‖φ z‖ * (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 /
        (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) * K₁ := mul_le_mul_of_nonneg_left hB hA
    _ = _ := by ring

/-- §35.2 (the algebra of the main inequality): for `g = f⁻¹ ∘ f₀` one has
`μ_g = (κ + κ₁τ)/(1 + κ̄κ₁τ)`, and

`|1 + μ_g w|²/(1 - |μ_g|²) ≤ (|1 + κw|²/(1 - |κ|²)) · (|1 + κ₁τw(1 + κ̄w̄)/(1 + κw)|²/(1 - |κ₁|²))`

where `w = φ/|φ|`.  In fact equality holds; see `main_inequality_pointwise_eq`.

**Correction.**  This previously omitted the factor `w` on the `κ₁τ` term, and was **false**: at
`κ = κ₁ = 3/4`, `τ = i`, `w = -i` — all four hypotheses hold — the right-hand side is exactly `1`
while the left-hand side is `≈ 16.18`.  The book (§35.2, the display before 因此) writes that
factor as `κ₁τ(φ/|φ|)(1 + κ̄φ̄/|φ|)/(1 + κφ/|φ|)`, i.e. with `φ/|φ| = w` present; dropping it
shifts one argument, since `LHS(κ,κ₁,τ,w) = RHS(κ,κ₁,τw,w)`.  The two unimodular parameters are
not independent in the Reich–Strebel argument — `τ = ∂_z̄f₀/∂_zf₀` and `w = φ/|φ|` are evaluated at
the same point — which is why quantifying over them separately breaks the statement. -/
theorem main_inequality_pointwise {κ κ₁ τ w : ℂ} (hκ : ‖κ‖ < 1) (hκ₁ : ‖κ₁‖ < 1) (hτ : ‖τ‖ = 1) (hw : ‖w‖ = 1) :
    ‖1 + (κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ) * w‖ ^ 2 / (1 - ‖(κ + κ₁ * τ) / (1 + conj κ * κ₁ * τ)‖ ^ 2) ≤
      (‖1 + κ * w‖ ^ 2 / (1 - ‖κ‖ ^ 2)) *
        (‖1 + κ₁ * τ * w * (1 + conj κ * conj w) / (1 + κ * w)‖ ^ 2 / (1 - ‖κ₁‖ ^ 2)) :=
  le_of_eq (main_inequality_pointwise_eq hκ hκ₁ hτ hw)

/-! ## §35.3 The extremal problem for given boundary values -/

/-- `f` is a quasiconformal self-map of `Δ` with boundary values `h : ∂Δ → ∂Δ` (a homeomorphism of the
circle, given as a map of `ℂ̄`). -/
def HasBoundaryValues (f : ℂ → ℂ) (h : ExtPlane → ExtPlane) : Prop :=
  IsQuasiconformal f unitDisc ∧ f '' unitDisc = unitDisc ∧
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc unitDisc F ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = h ζ

/-- The essential supremum `k = ‖μ_f‖_∞` over `Δ`. -/
def dilatationNorm (f : ℂ → ℂ) : ℝ :=
  (essSup (fun z => (‖complexDilatation f z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc)).toReal

/-- §35.3: the family `F` of quasiconformal self-maps of `Δ` with boundary values `h`; `f₀ ∈ F` is
extremal if `K[f₀] = inf_{f ∈ F} K[f]`. -/
def IsExtremalForBoundary (f : ℂ → ℂ) (h : ExtPlane → ExtPlane) : Prop :=
  HasBoundaryValues f h ∧ ∀ g : ℂ → ℂ, HasBoundaryValues g h → maxDilatation f unitDisc ≤ maxDilatation g unitDisc

/-! ### S35-A track interface (coordinator 553e2d): Theorem 35.1 through the upper half-plane -/

/-- The point `η₀` with `h(1) = η₀` (a point of the unit circle for a boundary correspondence `h`). -/
def s35a_eta (h : ExtPlane → ExtPlane) : ℂ := extToC (h ((1 : ℂ) : ExtPlane))

/-- The Möbius map `N_h(u) = i(η₀ + u)/(η₀ - u)` of `Δ` onto `ℍ` (the inverse Cayley map after the rotation `u ↦ u/η₀`),
sending `η₀ = h(1)` to `∞`. -/
def s35a_N (h : ExtPlane → ExtPlane) : ℂ → ℂ := mobiusFn I (I * s35a_eta h) (-1) (s35a_eta h)

/-- The boundary correspondence `h` transported to `ℝ`: `h̃(x) = N_h(h(C x))`, `C` the Cayley map (a real number for real
`x`, since `C x ≠ 1` lies on the circle and `h(C x) ≠ η₀`). -/
def s35a_hTilde (h : ExtPlane → ExtPlane) (x : ℝ) : ℝ :=
  (extToC (mobiusExt I (I * s35a_eta h) (-1) (s35a_eta h) (h ((cayley x : ℂ) : ExtPlane)))).re

/-- The affine normalization of `h̃` at `0` and `1`: `A(x) = (h̃ x - h̃ 0)/(h̃ 1 - h̃ 0)`. -/
def s35a_A (h : ExtPlane → ExtPlane) (x : ℝ) : ℝ :=
  (s35a_hTilde h x - s35a_hTilde h 0) / (s35a_hTilde h 1 - s35a_hTilde h 0)

/-- A quasiconformal map with `K[g] ≤ K` on an open set is `K`-quasiconformal there (Theorem 10.1: `g` is ACL, and
`(|∂g| + |∂̄g|)/(|∂g| - |∂̄g|) ≤ K` a.e. with a positive Jacobian a.e.). -/
theorem s35a_isKQC_of_maxDilatation_le {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsQuasiconformal g D) (hK : 1 ≤ K)
    (hle : maxDilatation g D ≤ ENNReal.ofReal K) : IsKQC g D K := by
  obtain ⟨K₀, hK₀⟩ := hg
  exact UniversalTeichmuller.ut_md_isKQC_of_le hK₀ hK hle

/-- For `η ≠ 0` the Möbius map `u ↦ i(η + u)/(η - u)` is the inverse Cayley transform after the rotation `u ↦ u/η`
(both sides are `0` at the pole `u = η`). -/
theorem s35a_x_mobiusFn_eq_cayleyInv {η : ℂ} (hη : η ≠ 0) (u : ℂ) :
    mobiusFn I (I * η) (-1) η u = cayleyInv (η⁻¹ * u) := by
  unfold mobiusFn cayleyInv
  by_cases hu : u = η
  · subst hu
    simp [hη]
  · have h1 : -1 * u + η ≠ 0 := by
      intro h
      apply hu
      linear_combination -h
    have h2 : (1 : ℂ) - η⁻¹ * u ≠ 0 := by
      intro h
      apply hu
      have h3 : η * (1 - η⁻¹ * u) = η - u := by
        field_simp
      rw [h, mul_zero] at h3
      linear_combination h3
    rw [div_eq_div_iff h1 h2]
    field_simp
    ring

/-- The inverse Cayley transform maps the unit circle into `ℝ` (the pole `1` goes to the junk value `0`). -/
theorem s35a_x_cayleyInv_im_eq_zero {v : ℂ} (hv : ‖v‖ = 1) : (cayleyInv v).im = 0 := by
  have hre : v.re * v.re + v.im * v.im = 1 := by
    have h := Complex.normSq_apply v
    rw [Complex.normSq_eq_norm_sq, hv] at h
    linarith
  rw [cayleyInv, Complex.div_im, div_sub_div_same]
  apply div_eq_zero_iff.mpr
  left
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  linear_combination -hre

/-- The frontier of the unit disc in `ℂ̄` is the unit circle. -/
theorem s35a_x_frontier_disc : frontier (toExt unitDisc) = toExt (sphere (0 : ℂ) 1) := by
  rw [unitDisc, frontier_toExt_of_isBounded Metric.isBounded_ball Metric.isOpen_ball,
    frontier_ball (0 : ℂ) one_ne_zero]

/-- A point of the unit circle lies in the closure of the unit disc in `ℂ̄`. -/
theorem s35a_x_mem_closure {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ((ζ : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
  apply frontier_subset_closure
  rw [s35a_x_frontier_disc]
  exact ⟨ζ, mem_sphere_zero_iff_norm.2 hζ, rfl⟩

/-- A boundary extension `F` of a self-map `f` of `Δ` maps a point of the unit circle to a point of the unit
circle (`F` maps the frontier onto the frontier). -/
theorem s35a_x_ext_circle {f : ℂ → ℂ} {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f unitDisc unitDisc F)
    (himg : f '' unitDisc = unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ F (ζ : ExtPlane) = (w : ExtPlane) := by
  have hU : IsOpen unitDisc := Metric.isOpen_ball
  have hmem : ((ζ : ℂ) : ExtPlane) ∈ frontier (toExt unitDisc) := by
    rw [s35a_x_frontier_disc]
    exact ⟨ζ, mem_sphere_zero_iff_norm.2 hζ, rfl⟩
  have h2 : F (ζ : ExtPlane) ∈ frontier (toExt unitDisc) := by
    rw [← hF.image_frontier hU hU himg]
    exact mem_image_of_mem F hmem
  rw [s35a_x_frontier_disc] at h2
  obtain ⟨w, hw, hw'⟩ := h2
  exact ⟨w, mem_sphere_zero_iff_norm.1 hw, hw'.symm⟩

/-- The Cayley transform of a real point lies on the unit circle. -/
theorem s35a_x_norm_cayley_ofReal (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 := by
  have hne : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have h1 : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
    rw [← norm_conj ((x : ℂ) + I)]
    congr 1
    simp [sub_eq_add_neg]
  rw [cayley, norm_div, h1, div_self (norm_ne_zero_iff.2 hne)]

/-- The Cayley transform of a real point is not `1` (`1` is the image of `∞`). -/
theorem s35a_x_cayley_ofReal_ne_one (x : ℝ) : cayley (x : ℂ) ≠ 1 := by
  have hne : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  intro h
  rw [cayley, div_eq_one_iff_eq hne] at h
  have h2 : (2 : ℂ) * I = 0 := by linear_combination -h
  simp at h2

/-- **X** (transfer to `ℍ`): a `K`-q.c. `f` with boundary values `h` gives the `K`-q.c. self-map `N_h ∘ f ∘ C` of `ℍ` with
boundary values `h̃` fixing `∞` (the extension `N̂_h ∘ F ∘ Ĉ`; `F(1) = h(1) = η₀ ↦ ∞`, and a point of the circle other than
`η₀` goes to `ℝ`). -/
theorem s35a_transfer {h : ExtPlane → ExtPlane} {f : ℂ → ℂ} {K : ℝ} (hf : HasBoundaryValues f h)
    (hK : IsKQC f unitDisc K) : HasQCExtensionH (s35a_hTilde h) (s35a_N h ∘ f ∘ cayley) K := by
  obtain ⟨-, hfimg, F, hF, hFh⟩ := hf
  obtain ⟨η, hηdef⟩ : ∃ η : ℂ, s35a_eta h = η := ⟨_, rfl⟩
  -- `F(1) = h(1)` is a point `η` of the unit circle
  obtain ⟨w₁, hw₁, hFw₁⟩ := s35a_x_ext_circle hF hfimg (ζ := 1) (by simp)
  have hF1 : F ((1 : ℂ) : ExtPlane) = (η : ExtPlane) := by
    have hh1 : h ((1 : ℂ) : ExtPlane) = (w₁ : ExtPlane) := by rw [← hFh 1 (by simp), hFw₁]
    have hηw : η = w₁ := by
      rw [← hηdef, s35a_eta, hh1]
      rfl
    rw [hFw₁, hηw]
  have hη1 : ‖η‖ = 1 := by
    have hηw : η = w₁ := by
      rw [← hηdef, s35a_eta, ← hFh 1 (by simp), hFw₁]
      rfl
    rw [hηw, hw₁]
  have hη0 : η ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hη1
    exact zero_ne_one hη1
  have hNdef : s35a_N h = mobiusFn I (I * η) (-1) η := by
    unfold s35a_N
    rw [hηdef]
  have hTdef : ∀ x : ℝ, s35a_hTilde h x =
      (extToC (mobiusExt I (I * η) (-1) η (h ((cayley x : ℂ) : ExtPlane)))).re := fun x => by
    unfold s35a_hTilde
    rw [hηdef]
  rw [hNdef]
  -- `N` maps `Δ` conformally onto `ℍ`
  have hNconf : IsConformalOnto (mobiusFn I (I * η) (-1) η) unitDisc upperHalf := by
    have hNeq : mobiusFn I (I * η) (-1) η = cayleyInv ∘ (fun u => η⁻¹ * u) :=
      funext (s35a_x_mobiusFn_eq_cayleyInv hη0)
    rw [hNeq]
    exact s35a_x_isConformalOnto_cayleyInv.comp (isConformalOnto_rot (by rw [norm_inv, hη1, inv_one]))
  -- the Möbius homeomorphisms `Ĉ` and `N̂` of `ℂ̄`
  obtain ⟨eC, heC⟩ : ∃ e : ExtPlane ≃ₜ ExtPlane, ∀ p, e p = mobiusExt 1 (-I) 1 I p :=
    ⟨mobiusHomeomorph 1 (-I) 1 I cayley_inv_det, fun p => rfl⟩
  have hdetN : I * η - I * η * (-1) ≠ 0 := by
    rw [show I * η - I * η * (-1) = 2 * I * η by ring]
    exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hη0
  obtain ⟨eN, heN⟩ : ∃ e : ExtPlane ≃ₜ ExtPlane, ∀ p, e p = mobiusExt I (I * η) (-1) η p :=
    ⟨mobiusHomeomorph I (I * η) (-1) η hdetN, fun p => rfl⟩
  have hC : IsHomeoExtension cayley upperHalf unitDisc eC := by
    refine ⟨fun z hz => ?_, eC.continuous.continuousOn, eC.injective.injOn, ?_⟩
    · rw [heC]
      exact s13x_th_cayleyExt_coe hz
    · rw [eC.image_closure]
      congr 1
      rw [← s13x_th_cayleyExt_image]
      congr 1
      ext p
      exact heC p
  have hdenN : ∀ w : ℂ, w ≠ η → -1 * w + η ≠ 0 := fun w hw h0 => hw (by linear_combination -h0)
  have heNcoe : ∀ w ∈ unitDisc, eN (w : ExtPlane) = ((mobiusFn I (I * η) (-1) η w : ℂ) : ExtPlane) := by
    intro w hw
    have hwη : w ≠ η := by
      rintro rfl
      rw [unitDisc, mem_ball_zero_iff, hη1] at hw
      exact lt_irrefl _ hw
    rw [heN, mobiusExt_coe (hdenN w hwη)]
  have heNimg : eN '' toExt unitDisc = toExt upperHalf := by
    rw [← hNconf.2.2]
    ext p
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [heNcoe z hz]
      exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, heNcoe z hz⟩
  have himgFC : (f ∘ cayley) '' upperHalf = unitDisc := by
    rw [image_comp, isConformalOnto_cayley.2.2, hfimg]
  have hmapsFC : MapsTo (f ∘ cayley) upperHalf unitDisc := fun z hz =>
    himgFC ▸ mem_image_of_mem (f ∘ cayley) hz
  have hG := (hF.comp hC isConformalOnto_cayley.mapsTo).comp_homeomorph hmapsFC eN heNcoe heNimg
  -- quasiconformality
  have hK1 : IsKQC (f ∘ cayley) upperHalf (1 * K) :=
    thm7_1_comp (isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley) hK
      isConformalOnto_cayley.2.2.subset
  have hK2 : IsKQC (mobiusFn I (I * η) (-1) η ∘ (f ∘ cayley)) upperHalf (1 * K * 1) :=
    thm7_1_comp hK1 (isKQC_one_of_conformal Metric.isOpen_ball hNconf) himgFC.subset
  rw [one_mul, mul_one] at hK2
  refine ⟨hK2, by rw [image_comp, himgFC, hNconf.2.2], _, hG, ?_, fun x => ?_⟩
  · -- `∞ ↦ 1 ↦ η ↦ ∞`
    show eN (F (eC extInf)) = extInf
    rw [heC, mobiusExt_infty_of_ne one_ne_zero, div_one, hF1, heN,
      mobiusExt_coe_of_eq_zero (by ring)]
  · -- a real point goes to `C x` on the circle, then to `w ≠ η` on the circle, then to the real point `N w`
    have hxI : (1 : ℂ) * (x : ℂ) + I ≠ 0 := by
      rw [one_mul]
      exact fun h0 => by simpa using congrArg Complex.im h0
    have hCx : eC ((x : ℂ) : ExtPlane) = ((cayley x : ℂ) : ExtPlane) := by
      rw [heC, mobiusExt_coe hxI]
      congr 1
      simp only [mobiusFn, cayley, one_mul, sub_eq_add_neg]
    have hnx := s35a_x_norm_cayley_ofReal x
    obtain ⟨w, hw, hFw⟩ := s35a_x_ext_circle hF hfimg hnx
    have hwη : w ≠ η := by
      rintro rfl
      have h1 : F ((cayley x : ℂ) : ExtPlane) = F ((1 : ℂ) : ExtPlane) := by rw [hFw, hF1]
      have h2 := hF.2.2.1 (s35a_x_mem_closure hnx) (s35a_x_mem_closure (by simp)) h1
      exact s35a_x_cayley_ofReal_ne_one x (OnePoint.coe_injective h2)
    have hhw : h ((cayley x : ℂ) : ExtPlane) = (w : ExtPlane) := by rw [← hFh _ hnx, hFw]
    have hval : mobiusExt I (I * η) (-1) η (w : ExtPlane) = ((mobiusFn I (I * η) (-1) η w : ℂ) : ExtPlane) :=
      mobiusExt_coe (hdenN w hwη)
    have him : (mobiusFn I (I * η) (-1) η w).im = 0 := by
      rw [s35a_x_mobiusFn_eq_cayleyInv hη0]
      apply s35a_x_cayleyInv_im_eq_zero
      rw [norm_mul, norm_inv, hη1, hw, inv_one, one_mul]
    have hreal : (((mobiusFn I (I * η) (-1) η w).re : ℝ) : ℂ) = mobiusFn I (I * η) (-1) η w :=
      Complex.ext (by simp) (by simp [him])
    have hT : s35a_hTilde h x = (mobiusFn I (I * η) (-1) η w).re := by
      rw [hTdef, hhw, hval]
      rfl
    show eN (F (eC ((x : ℂ) : ExtPlane))) = _
    rw [hT, hreal, hCx, hFw, heN, hval]

/-- **Y1** (the normalized reflected map): for a `K`-q.c. self-map `g` of `ℍ` with boundary values `h̃` fixing `∞`, the
reflection (`qc_reflection_extension`) normalized by `A(w) = (w - h̃ 0)/(h̃ 1 - h̃ 0)` is a normalized `K`-q.c. map of the
plane commuting with `conj`, equal to `A ∘ g` on `ℍ` and to `A ∘ h̃` on `ℝ`. -/
theorem s35a_plane {hT : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (hg : HasQCExtensionH hT g K) :
    ∃ P : ℂ → ℂ, IsKQCNormalizedPlane P K ∧ (∀ z, P (conj z) = conj (P z)) ∧
      (∀ z ∈ upperHalf, P z = (g z - hT 0) / (hT 1 - hT 0)) ∧
      ∀ x : ℝ, P x = (((hT x - hT 0) / (hT 1 - hT 0) : ℝ) : ℂ) := by
  have hmono : StrictMono hT := (b4_qs_monotone hg).1
  obtain ⟨hgK, himg, G, hG, hGinf, hGh⟩ := hg
  obtain ⟨g', hg'K, hg's, hg'g, hg'conj⟩ :=
    qc_reflection_extension hgK himg (b4_ext_tendsto_cocompact hG hGinf)
  have hreal : ∀ x : ℝ, g' (x : ℂ) = (hT x : ℂ) := fun x => OnePoint.coe_injective
    ((b4_ext_coe_eq_of_real hG (continuousOn_univ.1 hg'K.2.2.1.1) hg'g x).trans (hGh x))
  have hpos : 0 < hT 1 - hT 0 := sub_pos.2 (hmono zero_lt_one)
  have ha : ((hT 1 - hT 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  obtain ⟨hPK, hPs⟩ := bB_l_affine_isKQC hg'K hg's ((hT 0 : ℝ) : ℂ) ha
  have h0 : g' 0 = (hT 0 : ℂ) := by simpa using hreal 0
  have h1 : g' 1 = (hT 1 : ℂ) := by simpa using hreal 1
  refine ⟨fun z => (g' z - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ), ⟨hPK, hPs, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show (g' 0 - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ) = 0
    rw [h0, sub_self, zero_div]
  · show (g' 1 - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ) = 1
    rw [h1, ← Complex.ofReal_sub]
    exact div_self ha
  · intro z
    show (g' (conj z) - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ)
      = conj ((g' z - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ))
    rw [hg'conj, map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
  · intro z hz
    show (g' z - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ) = _
    rw [hg'g hz]
    push_cast
    rfl
  · intro x
    show (g' (x : ℂ) - (hT 0 : ℂ)) / ((hT 1 - hT 0 : ℝ) : ℂ) = _
    rw [hreal x]
    push_cast
    rfl

/-- **Y2** (the limit): normalized `K₀`-q.c. maps `Pₙ` of the plane commuting with `conj`, all equal to `H` on `ℝ`, which are
eventually `K'`-q.c. on `ℍ` for every `K' > K*`, have a normalized `K₀`-q.c. limit `P` commuting with `conj`, equal to `H`
on `ℝ` and `K'`-q.c. on `ℍ` for every `K' > K*` (`ut2_nf_extract`, `ut2_nf_limit`, `ut2_limit_isKQC`). -/
theorem s35a_limit {P : ℕ → ℂ → ℂ} {K₀ Kstar : ℝ} {H : ℝ → ℂ} (hP : ∀ n, IsKQCNormalizedPlane (P n) K₀)
    (hsym : ∀ n z, P n (conj z) = conj (P n z)) (hH : ∀ n (x : ℝ), P n x = H x)
    (hK : ∀ K' > Kstar, ∀ᶠ n in atTop, IsKQC (P n) upperHalf K') :
    ∃ P₀ : ℂ → ℂ, IsKQCNormalizedPlane P₀ K₀ ∧ (∀ z, P₀ (conj z) = conj (P₀ z)) ∧ (∀ x : ℝ, P₀ x = H x) ∧
      ∀ K' > Kstar, IsKQC P₀ upperHalf K' := by
  obtain ⟨φ, hφ, P₀, hlim⟩ := UniversalTeichmuller.ut2_nf_extract hP
  have hP₀ := UniversalTeichmuller.ut2_nf_limit (fun n => hP (φ n)) hlim
  have hpt : ∀ z, Tendsto (fun n => P (φ n) z) atTop (𝓝 (P₀ z)) := fun z =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)
  refine ⟨P₀, hP₀, fun z => ?_, fun x => ?_, fun K' hK' => ?_⟩
  · -- `conj` is continuous, so the symmetry passes to the pointwise limit
    refine tendsto_nhds_unique (hpt (conj z)) ?_
    exact ((Complex.continuous_conj.tendsto _).comp (hpt z)).congr fun n => (hsym (φ n) z).symm
  · exact tendsto_nhds_unique (hpt x) (tendsto_const_nhds.congr fun n => (hH (φ n) x).symm)
  · -- Theorem 8.2 on `ℍ` along the tail `n ↦ φ (n + N)` of the subsequence
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hK K' hK')
    have hqc : ∀ n, IsKQC (P (φ (n + N))) upperHalf K' := fun n =>
      hN _ ((Nat.le_add_left N n).trans (hφ.id_le (n + N)))
    have hlim' : TendstoLocallyUniformly (fun n => P (φ (n + N))) P₀ atTop := fun u hu x => by
      obtain ⟨t, ht, H⟩ := hlim u hu x
      exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually H⟩
    exact UniversalTeichmuller.ut2_limit_isKQC isOpen_upperHalf hqc hlim'.tendstoLocallyUniformlyOn
      (hP₀.1.2.2.1.2.1.mono (subset_univ _))

/-- `C(C⁻¹ w) = w` off the pole `w = 1` of `C⁻¹` (not only on `Δ`). -/
theorem s35a_z_cayley_cayleyInv {w : ℂ} (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have h2 : cayleyInv w + I = I * 2 / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h3 : cayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h2ne : cayleyInv w + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) h1
  rw [cayley, div_eq_iff h2ne, h3, h2]
  field_simp

/-- `C⁻¹` sends a point of the unit circle other than `1` to a real number. -/
theorem s35a_z_cayleyInv_im {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u ≠ 1) : (cayleyInv u).im = 0 := by
  show cayleyInv u ∈ realLine
  rw [← b4_cayley_image]
  exact ⟨u, ⟨mem_sphere_zero_iff_norm.2 hu, hu1⟩, rfl⟩

/-- For real `x`, `C x` lies on the unit circle and is not `1`. -/
theorem s35a_z_cayley_ofReal (x : ℝ) : ‖cayley x‖ = 1 ∧ cayley x ≠ 1 := by
  have hden : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  refine ⟨?_, fun h1 => ?_⟩
  · have h1 : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
      rw [← norm_conj ((x : ℂ) + I)]
      congr 1
      simp [sub_eq_add_neg]
    rw [cayley, norm_div, h1, div_self (norm_ne_zero_iff.2 hden)]
  · rw [cayley, div_eq_one_iff_eq hden] at h1
    have := congrArg Complex.im h1
    norm_num at this

/-- The boundary data of `h` (from any map with boundary values `h`): `η₀ = h(1)` lies on the unit circle, and for real
`x` the point `h(C x)` is `η₀ C(h̃ x)` (the circle minus `η₀` goes to `ℝ` under `N_h`, and `N_h⁻¹ w = η₀ C w`). -/
theorem s35a_z_boundary {f : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf : HasBoundaryValues f h) :
    ‖s35a_eta h‖ = 1 ∧ h ((1 : ℂ) : ExtPlane) = ((s35a_eta h : ℂ) : ExtPlane) ∧
      ∀ x : ℝ, h ((cayley x : ℂ) : ExtPlane) = ((s35a_eta h * cayley (s35a_hTilde h x) : ℂ) : ExtPlane) := by
  obtain ⟨-, hfs, F, hF, hFh⟩ := hf
  have hfr : F '' frontier (toExt unitDisc) = frontier (toExt unitDisc) :=
    hF.image_frontier isOpen_ball isOpen_ball hfs
  have hfr' : frontier (toExt unitDisc) = toExt (sphere (0 : ℂ) 1) := by
    rw [unitDisc, frontier_toExt_of_isBounded Metric.isBounded_ball isOpen_ball, frontier_ball 0 one_ne_zero]
  rw [hfr'] at hfr
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ w : ℂ, ‖w‖ = 1 ∧ h ζ = w := by
    intro ζ hζ
    have hmem : F ζ ∈ toExt (sphere (0 : ℂ) 1) :=
      hfr ▸ mem_image_of_mem F ⟨ζ, mem_sphere_zero_iff_norm.2 hζ, rfl⟩
    obtain ⟨w, hw, hw'⟩ := hmem
    exact ⟨w, mem_sphere_zero_iff_norm.1 hw, by rw [← hFh ζ hζ, hw']⟩
  have hsub : toExt (sphere (0 : ℂ) 1) ⊆ closure (toExt unitDisc) := by
    rw [← hfr']
    exact frontier_subset_closure
  have hinj : ∀ ζ₁ ζ₂ : ℂ, ‖ζ₁‖ = 1 → ‖ζ₂‖ = 1 → h ζ₁ = h ζ₂ → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2 heq
    rw [← hFh _ h1, ← hFh _ h2] at heq
    exact OnePoint.coe_injective (hF.2.2.1 (hsub ⟨ζ₁, mem_sphere_zero_iff_norm.2 h1, rfl⟩)
      (hsub ⟨ζ₂, mem_sphere_zero_iff_norm.2 h2, rfl⟩) heq)
  obtain ⟨η, hη, hη'⟩ := hcirc 1 (by simp)
  have hηdef : s35a_eta h = η := by
    rw [s35a_eta, hη']
    rfl
  refine ⟨hηdef ▸ hη, hηdef ▸ hη', fun x => ?_⟩
  obtain ⟨hx1, hx2⟩ := s35a_z_cayley_ofReal x
  obtain ⟨w, hw, hw'⟩ := hcirc _ hx1
  have hwη : w ≠ η := by
    rintro rfl
    exact hx2 (hinj _ _ hx1 (by simp) (by rw [hw', hη']))
  have hη0 : η ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hη]; exact one_ne_zero)
  have hu : ‖w / η‖ = 1 := by rw [norm_div, hw, hη, div_one]
  have hu1 : w / η ≠ 1 := fun h1 => hwη ((div_eq_one_iff_eq hη0).1 h1)
  have hden : (-1) * w + η ≠ 0 := by
    intro h0
    apply hwη
    linear_combination -h0
  have hden' : η - w ≠ 0 := by
    intro h0
    apply hwη
    linear_combination -h0
  have hN : mobiusFn I (I * η) (-1) η w = cayleyInv (w / η) := by
    simp only [mobiusFn, cayleyInv]
    rw [show (-1) * w + η = η - w by ring]
    field_simp
    ring
  have htil : ((s35a_hTilde h x : ℝ) : ℂ) = cayleyInv (w / η) := by
    unfold s35a_hTilde
    rw [hηdef, hw', mobiusExt_coe hden, hN]
    exact Complex.ext (by simp [extToC]) (by simp [extToC, s35a_z_cayleyInv_im hu hu1])
  rw [hw', htil, hηdef, s35a_z_cayley_cayleyInv hu1]
  congr 1
  field_simp

/-- For `b > 0` real and `|η| = 1`, the map `w ↦ η C(a + b w)` sends `ℍ` conformally onto `Δ`. -/
theorem s35a_z_isConformalOnto_M {η : ℂ} (hη : ‖η‖ = 1) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    IsConformalOnto (fun w : ℂ => η * cayley ((a : ℂ) + (b : ℂ) * w)) upperHalf unitDisc := by
  have hη0 : η ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hη]; exact one_ne_zero)
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have hmaps : MapsTo (fun w : ℂ => (a : ℂ) + (b : ℂ) * w) upperHalf upperHalf := fun w hw => by
    show 0 < ((a : ℂ) + (b : ℂ) * w).im
    simpa using mul_pos hb hw
  refine ⟨?_, fun w₁ hw₁ w₂ hw₂ heq => ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun w : ℂ => (a : ℂ) + (b : ℂ) * w) upperHalf :=
      (by fun_prop : Differentiable ℂ (fun w : ℂ => (a : ℂ) + (b : ℂ) * w)).differentiableOn
    exact (isConformalOnto_cayley.1.comp hd hmaps).const_mul η
  · have h1 := isConformalOnto_cayley.2.1 (hmaps hw₁) (hmaps hw₂) (mul_left_cancel₀ hη0 heq)
    exact mul_left_cancel₀ hb0 (add_left_cancel h1)
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [unitDisc, mem_ball_zero_iff, norm_mul, hη, one_mul]
      exact mem_ball_zero_iff.1 (cayley_mem_unitDisc (hmaps hw))
    · intro hv
      have hv' : ‖v / η‖ < 1 := by rw [norm_div, hη, div_one]; exact mem_ball_zero_iff.1 hv
      refine ⟨(cayleyInv (v / η) - a) / b, ?_, ?_⟩
      · have := cayleyInv_mem_upperHalf hv'
        show 0 < ((cayleyInv (v / η) - a) / b).im
        rw [Complex.div_ofReal_im]
        simpa using div_pos this hb
      · show η * cayley ((a : ℂ) + (b : ℂ) * ((cayleyInv (v / η) - a) / b)) = v
        rw [show (a : ℂ) + (b : ℂ) * ((cayleyInv (v / η) - a) / b) = cayleyInv (v / η) by field_simp; ring,
          cayley_cayleyInv hv']
        field_simp

/-- The Möbius formula for `w ↦ η C(a + b w)`: it is `(η b w + η(a - i))/(b w + (a + i))`. -/
theorem s35a_z_mobiusFn_M (η : ℂ) (a b : ℝ) (w : ℂ) :
    mobiusFn (η * b) (η * (a - I)) b (a + I) w = η * cayley ((a : ℂ) + (b : ℂ) * w) := by
  simp only [mobiusFn, cayley]
  rw [mul_div_assoc']
  congr 1 <;> ring

/-- The Möbius formula for `C⁻¹`: it is `(i w + i)/(-w + 1)`. -/
theorem s35a_z_mobiusFn_cayleyInv (w : ℂ) : mobiusFn I I (-1) 1 w = cayleyInv w := by
  simp only [mobiusFn, cayleyInv]
  congr 1 <;> ring

/-- A map of `ℂ̄` agreeing with `g` on `U` carries `toExt U` onto `toExt (g '' U)`. -/
theorem s35a_z_image_toExt {E : ExtPlane → ExtPlane} {g : ℂ → ℂ} {U V : Set ℂ}
    (hE : ∀ w ∈ U, E (w : ExtPlane) = ((g w : ℂ) : ExtPlane)) (hg : g '' U = V) : E '' toExt U = toExt V := by
  unfold toExt
  rw [image_image, ← hg, image_image]
  exact image_congr hE

/-- The Möbius extension of `C⁻¹ : Δ → ℍ` to `ℂ̄` is a homeomorphic boundary extension. -/
theorem s35a_z_isHomeoExtension_cayleyInv :
    IsHomeoExtension cayleyInv unitDisc upperHalf (mobiusHomeomorph I I (-1) 1 cayley_det) := by
  have hE : ∀ w ∈ unitDisc, mobiusHomeomorph I I (-1) 1 cayley_det (w : ExtPlane) = ((cayleyInv w : ℂ) : ExtPlane) := by
    intro w hw
    have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
      rw [show (-1 : ℂ) * w + 1 = 1 - w by ring]
      exact cayleyInv_den_ne_zero (mem_ball_zero_iff.1 hw)
    rw [mobiusHomeomorph_apply, mobiusExt_coe hden, s35a_z_mobiusFn_cayleyInv]
  exact (isHomeoExtension_id unitDisc).comp_homeomorph (mapsTo_id _) _ hE
    (s35a_z_image_toExt hE s35a_x_isConformalOnto_cayleyInv.2.2)

/-- The determinant of `w ↦ (η b w + η(a - i))/(b w + (a + i))` is `2iηb ≠ 0`. -/
theorem s35a_z_det_M {η : ℂ} (hη : η ≠ 0) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    η * b * (a + I) - η * (a - I) * b ≠ 0 := by
  rw [show η * b * (a + I) - η * (a - I) * b = 2 * I * η * b by ring]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hη) (ofReal_ne_zero.2 hb)

/-- **Z** (back to `Δ`): from a normalized q.c. map `P` of the plane commuting with `conj` and equal to `A ∘ h̃` on `ℝ`, the
map `f₀ = N_h⁻¹ ∘ A⁻¹ ∘ P ∘ C⁻¹` has boundary values `h` (`P` fixes `∞`; on the circle minus `1`, `C⁻¹` gives real
points), and `K[f₀] ≤ K'` whenever `P` is `K'`-q.c. on `ℍ` (conformal pre/post-composition). -/
theorem s35a_back {h : ExtPlane → ExtPlane} (hh : ∃ f, HasBoundaryValues f h) {P : ℂ → ℂ} {K₀ : ℝ}
    (hP : IsKQCNormalizedPlane P K₀) (hsym : ∀ z, P (conj z) = conj (P z))
    (hPx : ∀ x : ℝ, P x = ((s35a_A h x : ℝ) : ℂ)) :
    ∃ f₀ : ℂ → ℂ, HasBoundaryValues f₀ h ∧
      ∀ K', IsKQC P upperHalf K' → maxDilatation f₀ unitDisc ≤ ENNReal.ofReal K' := by
  obtain ⟨f, hf⟩ := hh
  obtain ⟨hη1, hh1, hhx⟩ := s35a_z_boundary hf
  obtain ⟨Kf, hKf⟩ := hf.1
  have hb : 0 < s35a_hTilde h 1 - s35a_hTilde h 0 :=
    sub_pos.2 ((b4_qs_monotone (s35a_transfer hf hKf)).1 zero_lt_one)
  have hA : ∀ x : ℝ, ((s35a_hTilde h 0 : ℝ) : ℂ) + ((s35a_hTilde h 1 - s35a_hTilde h 0 : ℝ) : ℂ) *
      ((s35a_A h x : ℝ) : ℂ) = ((s35a_hTilde h x : ℝ) : ℂ) := by
    intro x
    have : s35a_hTilde h 0 + (s35a_hTilde h 1 - s35a_hTilde h 0) * s35a_A h x = s35a_hTilde h x := by
      rw [s35a_A]
      field_simp
      ring
    exact_mod_cast this
  set η := s35a_eta h with hηdef
  set a := s35a_hTilde h 0 with hadef
  set b := s35a_hTilde h 1 - s35a_hTilde h 0 with hbdef
  have hη0 : η ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hη1]; exact one_ne_zero)
  obtain ⟨e, he⟩ := t1_homeomorph hP.1 hP.2.1
  have hPH : P '' upperHalf = upperHalf := bg_s_image_upperHalf hP.1 hP.2.1 hP.2.2.1 hP.2.2.2 hsym
  have hC := s35a_x_isConformalOnto_cayleyInv
  have hM := s35a_z_isConformalOnto_M hη1 a hb
  have hKQC : ∀ K', IsKQC P upperHalf K' →
      IsKQC ((fun w : ℂ => η * cayley ((a : ℂ) + (b : ℂ) * w)) ∘ (P ∘ cayleyInv)) unitDisc (1 * K' * 1) := by
    intro K' hK'
    have h1 := thm7_1_comp (isKQC_one_of_conformal isOpen_ball hC) hK' hC.2.2.subset
    exact thm7_1_comp h1 (isKQC_one_of_conformal isOpen_upperHalf hM) (by rw [image_comp, hC.2.2, hPH])
  have hPC : MapsTo (P ∘ cayleyInv) unitDisc upperHalf := fun z hz => by
    rw [← hPH]
    exact mem_image_of_mem P (hC.mapsTo hz)
  have hE2 : IsHomeoExtension (P ∘ cayleyInv) unitDisc upperHalf
      (e.onePointCongr ∘ mobiusHomeomorph I I (-1) 1 cayley_det) :=
    s35a_z_isHomeoExtension_cayleyInv.comp_homeomorph hC.mapsTo e.onePointCongr
      (fun w _ => by rw [← he]; rfl) (by rw [s13x_de_image_toExt, he, hPH])
  have hdet := s35a_z_det_M hη0 a hb.ne'
  have hEM : ∀ w : ℂ, 0 ≤ w.im → mobiusExt (η * b) (η * (a - I)) b (a + I) (w : ExtPlane) =
      ((η * cayley ((a : ℂ) + (b : ℂ) * w) : ℂ) : ExtPlane) := by
    intro w hw
    have hden : (b : ℂ) * w + (a + I) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      nlinarith
    rw [mobiusExt_coe hden, s35a_z_mobiusFn_M]
  have hE3 := hE2.comp_homeomorph (g := fun w : ℂ => η * cayley ((a : ℂ) + (b : ℂ) * w)) hPC
    (mobiusHomeomorph (η * b) (η * (a - I)) b (a + I) hdet) (fun w hw => hEM w (le_of_lt hw))
    (s35a_z_image_toExt (fun w hw => hEM w (le_of_lt hw)) hM.2.2)
  refine ⟨(fun w : ℂ => η * cayley ((a : ℂ) + (b : ℂ) * w)) ∘ (P ∘ cayleyInv),
    ⟨⟨_, hKQC K₀ (ac_t_isKQC_restrict hP.1 isOpen_upperHalf (subset_univ _))⟩, ?_, _, hE3, ?_⟩,
    fun K' hK' => ?_⟩
  · rw [image_comp, image_comp, hC.2.2, hPH, hM.2.2]
  · intro ζ hζ
    by_cases hζ1 : ζ = 1
    · subst hζ1
      rw [hh1]
      simp only [Function.comp_apply, mobiusHomeomorph_apply]
      rw [mobiusExt_coe_of_eq_zero (by norm_num), show e.onePointCongr extInf = extInf from rfl,
        mobiusExt_infty_of_ne (ofReal_ne_zero.2 hb.ne'), mul_div_cancel_right₀ _ (ofReal_ne_zero.2 hb.ne')]
    · have hre : cayleyInv ζ = ((cayleyInv ζ).re : ℂ) :=
        Complex.ext (by simp) (by simp [s35a_z_cayleyInv_im hζ hζ1])
      obtain ⟨x, hx⟩ : ∃ x : ℝ, cayleyInv ζ = x := ⟨_, hre⟩
      have hζx : ζ = cayley x := by rw [← hx, s35a_z_cayley_cayleyInv hζ1]
      have hden : (-1 : ℂ) * ζ + 1 ≠ 0 := by
        intro h0
        apply hζ1
        linear_combination -h0
      have hhζ : h (ζ : ExtPlane) = ((η * cayley (s35a_hTilde h x) : ℂ) : ExtPlane) := by
        rw [hζx]
        exact hhx x
      rw [hhζ]
      simp only [Function.comp_apply, mobiusHomeomorph_apply]
      rw [mobiusExt_coe hden, s35a_z_mobiusFn_cayleyInv, hx,
        show e.onePointCongr ((x : ℂ) : ExtPlane) = ((e x : ℂ) : ExtPlane) from rfl, he, hPx,
        hEM _ (by simp), hA x]
  · have := (isKQC_maxDilatation_le (hKQC K' hK')).1
    rwa [one_mul, mul_one] at this

/-- **Theorem 35.1**: for boundary values `h` admitting a quasiconformal extension, an extremal map
always exists (a limit of a minimizing sequence, which is a normal family). -/
theorem thm35_1_exists_extremal {h : ExtPlane → ExtPlane} (hh : ∃ f, HasBoundaryValues f h) :
    ∃ f₀ : ℂ → ℂ, IsExtremalForBoundary f₀ h := by
  -- `K* = inf {K[g] : g has boundary values h}`
  set M : Set ℝ≥0∞ := {m | ∃ g, HasBoundaryValues g h ∧ maxDilatation g unitDisc = m}
  have hne : unitDisc.Nonempty := ⟨0, by simp [unitDisc]⟩
  have hM1 : 1 ≤ sInf M := by
    refine le_sInf ?_
    rintro m ⟨g, hg, rfl⟩
    obtain ⟨K, hK⟩ := hg.1
    exact UniversalTeichmuller.ut_md_one_le hK hne
  have hMtop : sInf M ≠ ⊤ := by
    obtain ⟨f, hf⟩ := hh
    obtain ⟨K, hK⟩ := hf.1
    exact ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK).1)
      (sInf_le ⟨f, hf, rfl⟩)
  set Kr : ℝ := (sInf M).toReal
  have hKrM : ENNReal.ofReal Kr = sInf M := ENNReal.ofReal_toReal hMtop
  have hKr1 : 1 ≤ Kr := by simpa using ENNReal.toReal_mono hMtop hM1
  have hKr0 : 0 ≤ Kr := by linarith
  -- a minimizing sequence `gₙ` with `K[gₙ] < K* + 1/(n+1)`
  have hseq : ∀ n : ℕ, ∃ g, HasBoundaryValues g h ∧
      maxDilatation g unitDisc < ENNReal.ofReal (Kr + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf M < ENNReal.ofReal (Kr + 1 / ((n : ℝ) + 1)) := by
      rw [← hKrM]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    obtain ⟨m, ⟨g, hg, rfl⟩, hm⟩ := sInf_lt_iff.1 hlt
    exact ⟨g, hg, hm⟩
  choose g hg hgK using hseq
  have hgKQC : ∀ n : ℕ, ∀ K' : ℝ, Kr + 1 / ((n : ℝ) + 1) ≤ K' → IsKQC (g n) unitDisc K' := by
    intro n K' hK'
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact s35a_isKQC_of_maxDilatation_le (hg n).1 (by linarith)
      ((hgK n).le.trans (ENNReal.ofReal_le_ofReal hK'))
  set K₀ : ℝ := Kr + 1
  have hgK₀ : ∀ n : ℕ, IsKQC (g n) unitDisc K₀ := by
    intro n
    refine hgKQC n K₀ ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  -- transfer to `ℍ` and normalize
  have hX : ∀ n : ℕ, HasQCExtensionH (s35a_hTilde h) (s35a_N h ∘ g n ∘ cayley) K₀ :=
    fun n => s35a_transfer (hg n) (hgK₀ n)
  have hmono : StrictMono (s35a_hTilde h) := (b4_qs_monotone (hX 0)).1
  have hb : ((s35a_hTilde h 1 : ℝ) : ℂ) - ((s35a_hTilde h 0 : ℝ) : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (hmono zero_lt_one).ne'
  choose P hPn hPsym hPH hPx using fun n => s35a_plane (hX n)
  have hK : ∀ K' > Kr, ∀ᶠ n in atTop, IsKQC (P n) upperHalf K' := by
    intro K' hK'
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hK')
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : Kr + 1 / ((n : ℝ) + 1) ≤ K' := by
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have hGK : IsKQC (s35a_N h ∘ g n ∘ cayley) upperHalf K' := (s35a_transfer (hg n) (hgKQC n K' hle)).1
    have hA := isKQC_one_of_conformal isOpen_univ
      (nxE_affine_isConformalOnto (b := ((s35a_hTilde h 0 : ℝ) : ℂ)) hb)
    have hcomp := thm7_1_comp hGK hA (subset_univ _)
    rw [mul_one] at hcomp
    exact ad_isKQC_congr hcomp fun z hz => hPH n z hz
  -- the limit and the map back to `Δ`
  obtain ⟨P₀, hP₀, hP₀sym, hP₀x, hP₀K⟩ :=
    s35a_limit (H := fun x : ℝ => ((s35a_A h x : ℝ) : ℂ)) hPn hPsym hPx hK
  obtain ⟨f₀, hf₀, hf₀K⟩ := s35a_back hh hP₀ hP₀sym hP₀x
  have hf₀le : maxDilatation f₀ unitDisc ≤ sInf M := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := hε
    calc maxDilatation f₀ unitDisc ≤ ENNReal.ofReal (Kr + ε) := hf₀K _ (hP₀K _ (by linarith))
      _ = sInf M + ε := by rw [ENNReal.ofReal_add hKr0 ε.coe_nonneg, hKrM, ENNReal.ofReal_coe_nnreal]
  exact ⟨f₀, hf₀, fun g' hg' => hf₀le.trans (sInf_le ⟨g', hg', rfl⟩)⟩

/-- A holomorphic function on `Δ` which is not identically zero is nonzero almost everywhere on `Δ`:
its zero set is discrete, hence countable, hence null. -/
theorem ae_ne_zero_of_differentiableOn_unitDisc {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ¬ EqOn φ 0 unitDisc) : ∀ᵐ z ∂(volume.restrict unitDisc), φ z ≠ 0 := by
  have hΔ : IsOpen unitDisc := isOpen_ball
  have ha : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd hΔ
  have hconn : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h | h
  · exact absurd h hne
  · have hmem : {x | φ x ≠ 0} ∈ codiscreteWithin unitDisc := h
    rw [mem_codiscreteWithin] at hmem
    have hdisc : IsDiscrete (unitDisc \ {x | φ x ≠ 0}) := by
      rw [isDiscrete_iff_nhdsNE]
      intro x hx
      exact disjoint_iff.1 (hmem x hx.1)
    have hcount : (unitDisc \ {x | φ x ≠ 0}).Countable :=
      (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
    have hnull : volume (unitDisc \ {x | φ x ≠ 0}) = 0 := hcount.measure_zero volume
    have hΔm : MeasurableSet unitDisc := measurableSet_ball
    rw [ae_restrict_iff' hΔm]
    filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzF hφz
    exact hz ⟨hzF, fun h' => h' hφz⟩

/-- For `κ = k φ̄/|φ|` a.e. (`0 ≤ k`), `|κ| ≤ k` a.e. -/
theorem m35_rs_norm_le {φ f₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z = k * conj (φ z) / ‖φ z‖) :
    ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation f₀ z‖ ≤ k := by
  filter_upwards [hμ] with z hz
  rw [hz, norm_div, norm_mul, Complex.norm_real, Complex.norm_conj, Complex.norm_real, norm_norm,
    Real.norm_of_nonneg hk₀]
  rcases eq_or_ne ‖φ z‖ 0 with h0 | h0
  · rw [h0, div_zero]
    exact hk₀
  · rw [mul_div_assoc, div_self h0, mul_one]

/-- `K[f] ≤ (1 + k)/(1 - k)` for a q.c. map of `Δ` with `|μ_f| ≤ k < 1` a.e. (Theorem 10.2 (⇐)). -/
theorem m35_maxDilatation_le_of_ae_le {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation f z‖ ≤ k) :
    maxDilatation f unitDisc ≤ ENNReal.ofReal ((1 + k) / (1 - k)) := by
  obtain ⟨K, hK⟩ := hf
  have hb : IsBeltramiCoeff (complexDilatation f) unitDisc k :=
    ⟨((measurable_dzbar f).div (measurable_dz f)).aestronglyMeasurable, hae⟩
  exact (isKQC_maxDilatation_le (thm10_2_isKQC_of_genHomeoSolution isOpen_ball hk₀ hk hb
    (thm10_2_genHomeoSolution_of_isKQC hK).2)).1

/-- The first factor at a point where `κ = k φ̄/|φ|` and `φ ≠ 0`: `κφ/|φ| = k`, `κ̄φ̄/|φ| = k`, `|κ| = k`. -/
theorem m35_rs_point {κ p : ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hp : p ≠ 0) (hκ : κ = k * conj p / ‖p‖) :
    κ * p / ‖p‖ = k ∧ conj κ * conj p / ‖p‖ = k ∧ ‖κ‖ = k := by
  have hn : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hp).ne'
  have h1 : κ * p / ‖p‖ = k := by
    rw [hκ, show (k : ℂ) * conj p / ‖p‖ * p / ‖p‖ = k * (conj p * p) / (‖p‖ ^ 2) by ring,
      Complex.conj_mul', mul_div_assoc, div_self (pow_ne_zero 2 hn), mul_one]
  refine ⟨h1, ?_, ?_⟩
  · have h2 := congrArg conj h1
    simpa [map_div₀, map_mul, Complex.conj_ofReal] using h2
  · rw [hκ, norm_div, norm_mul, Complex.norm_real, Complex.norm_conj, Complex.norm_real, norm_norm,
      Real.norm_of_nonneg hk₀, mul_div_assoc, div_self (norm_pos_iff.2 hp).ne', mul_one]

/-- The first factor equals `(1 - k)/(1 + k)` when `κφ/|φ| = k`, `|κ| = k < 1`. -/
theorem m35_rs_first_factor {κ p : ℂ} {k : ℝ} (hk : k < 1) (h1 : κ * p / ‖p‖ = k) (h3 : ‖κ‖ = k) :
    ‖1 - κ * p / ‖p‖‖ ^ 2 / (1 - ‖κ‖ ^ 2) = (1 - k) / (1 + k) := by
  have hk0 : 0 ≤ k := h3 ▸ norm_nonneg κ
  rw [h1, h3, show (1 : ℂ) - k = ((1 - k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  have h2 : (1 : ℝ) + k ≠ 0 := by linarith
  have h4 : (1 : ℝ) - k ^ 2 ≠ 0 := by nlinarith
  rw [div_eq_div_iff h4 h2]
  ring

/-- **Theorem 35.2**, first half (`K[f₀] ≤ K[f]`), from `main_inequality_simplified`. -/
theorem m35_thm35_2_le {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {f₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hk : k < 1) (hf₀ : IsQuasiconformal f₀ unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc)
    (hμ : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z = k * conj (φ z) / ‖φ z‖)
    {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) (hfs : f '' unitDisc = unitDisc)
    {F F₀ : ExtPlane → ExtPlane} (hF : IsHomeoExtension f unitDisc unitDisc F)
    (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀) (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) :
    maxDilatation f₀ unitDisc ≤ maxDilatation f unitDisc := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hKf₀ := m35_maxDilatation_le_of_ae_le hf₀ hk₀ hk (m35_rs_norm_le hk₀ hμ)
  by_cases hz : EqOn φ 0 unitDisc
  · have hμ0 : ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation f₀ z‖ ≤ 0 := by
      filter_upwards [hμ, ae_restrict_mem hΔ] with z h1 h2
      rw [h1, hz h2]
      simp
    have h1 := m35_maxDilatation_le_of_ae_le hf₀ le_rfl zero_lt_one hμ0
    norm_num at h1
    obtain ⟨K, hK⟩ := hf
    exact h1.trans (UniversalTeichmuller.ut_md_one_le hK ⟨0, by simp [unitDisc]⟩)
  · have hne := ae_ne_zero_of_differentiableOn_unitDisc hφ.1 hz
    have hAtop : phiArea φ unitDisc ≠ ⊤ := hφ.2.ne
    have hA0 : phiArea φ unitDisc ≠ 0 := by
      intro h0
      have hm : AEMeasurable (fun z => ENNReal.ofReal ‖φ z‖) (volume.restrict unitDisc) :=
        (hφ.1.continuousOn.norm.aestronglyMeasurable hΔ).aemeasurable.ennreal_ofReal
      have h1 := (lintegral_eq_zero_iff' hm).1 h0
      have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), False := by
        filter_upwards [h1, hne] with z hz1 hz2
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz1
        exact hz2 (norm_le_zero_iff.1 hz1)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at h2
      exact (measure_ball_pos volume (0 : ℂ) one_pos).ne' h2
    have hmain := main_inequality_simplified hf hf₀ hfs hf₀s hF hF₀ hbd hφ
    have hint : ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ *
        (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2))) =
        ENNReal.ofReal ((1 - k) / (1 + k)) * phiArea φ unitDisc := by
      rw [phiArea, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae ?_
      filter_upwards [hμ, hne] with z h1 h2
      obtain ⟨e1, -, e3⟩ := m35_rs_point hk₀ h2 h1
      have hA := m35_rs_first_factor hk e1 e3
      simp only [mainIneqKappa]
      rw [hA, ← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith)), mul_comm]
    rw [hint] at hmain
    have h1 : 1 ≤ maxDilatation f unitDisc * ENNReal.ofReal ((1 - k) / (1 + k)) := by
      have h2 : 1 * phiArea φ unitDisc ≤
          (maxDilatation f unitDisc * ENNReal.ofReal ((1 - k) / (1 + k))) * phiArea φ unitDisc := by
        rw [one_mul, mul_assoc]
        exact hmain
      exact (ENNReal.mul_le_mul_iff_left hA0 hAtop).1 h2
    have hkk : (1 + k) / (1 - k) * ((1 - k) / (1 + k)) = 1 := by
      have : (1 : ℝ) + k ≠ 0 := by linarith
      have : (1 : ℝ) - k ≠ 0 := by linarith
      field_simp
    calc maxDilatation f₀ unitDisc ≤ ENNReal.ofReal ((1 + k) / (1 - k)) := hKf₀
      _ = ENNReal.ofReal ((1 + k) / (1 - k)) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal ((1 + k) / (1 - k)) *
            (maxDilatation f unitDisc * ENNReal.ofReal ((1 - k) / (1 + k))) := by gcongr
      _ = maxDilatation f unitDisc *
            ENNReal.ofReal ((1 + k) / (1 - k) * ((1 - k) / (1 + k))) := by
          rw [ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
          ring
      _ = maxDilatation f unitDisc := by rw [hkk, ENNReal.ofReal_one, mul_one]

/-- `Δ` is a Jordan domain (inline copy of `Lemmas/UnitDiscJordan.isJordanDomain_unitDisc`, which S35 does
not import). -/
theorem m35_isJordanDomain_unitDisc : IsJordanDomain unitDisc := by
  refine ⟨isOpen_ball, isConnected_ball one_pos, ?_⟩
  rw [s35a_x_frontier_disc]
  refine ⟨fun θ => ((θ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp continuous_subtype_val
  · exact fun a b hab => Circle.coe_injective (OnePoint.coe_injective hab)
  · unfold toExt
    ext w
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨(θ : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-- Three distinct points of the unit circle, as points of `ℂ̄`. -/
theorem m35_three_circle_points :
    ∃ p : Fin 3 → ExtPlane, Function.Injective p ∧ ∀ i, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ p i = (ζ : ExtPlane) := by
  refine ⟨![((1 : ℂ) : ExtPlane), ((-1 : ℂ) : ExtPlane), ((I : ℂ) : ExtPlane)], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd (OnePoint.coe_injective hij) (by norm_num [Complex.ext_iff])
  · intro i
    fin_cases i
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨-1, by simp, rfl⟩
    · exact ⟨I, by simp, rfl⟩

/-- `invFunOn` of a homeomorphic boundary extension (the q.c. version of `isHomeoExtension_invFunOn`,
which assumes conformality but only uses injectivity). -/
theorem m35_isHomeoExtension_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hfi : InjOn f U) (hfimg : f '' U = V) (hF : IsHomeoExtension f U V F) :
    IsHomeoExtension (Function.invFunOn f U) V U (Function.invFunOn F (closure (toExt U))) := by
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwU : w ∈ f '' U := hfimg ▸ hw
    obtain ⟨z, hz, rfl⟩ := hwU
    have hzmem : ((z : ℂ) : ExtPlane) ∈ closure (toExt U) := subset_closure (mem_image_of_mem _ hz)
    have hFz : F ((z : ℂ) : ExtPlane) = ((f z : ℂ) : ExtPlane) := hF1 z hz
    rw [hfi.leftInvOn_invFunOn hz, ← hFz]
    exact hF3.leftInvOn_invFunOn hzmem
  · rw [← hF4]
    exact continuousOn_invFunOn_of_isClosed isClosed_closure hF2 hF3
  · rw [← hF4]
    intro p hp q hq hpq
    calc p = F (Function.invFunOn F (closure (toExt U)) p) := (Function.invFunOn_eq hp).symm
      _ = F (Function.invFunOn F (closure (toExt U)) q) := by rw [hpq]
      _ = q := Function.invFunOn_eq hq
  · rw [← hF4]
    exact hF3.leftInvOn_invFunOn.image_image

/-- The equality case of the second factor: `|κ₁| ≤ k < 1`, `|u| ≤ 1` and
`|1 - κ₁u|²/(1 - |κ₁|²) ≥ (1 + k)/(1 - k)` force `κ₁ u = -k`. -/
theorem m35_second_factor_eq {κ₁ u : ℂ} {k : ℝ} (hk : k < 1) (hκ₁ : ‖κ₁‖ ≤ k) (hu : ‖u‖ ≤ 1)
    (hB : (1 + k) / (1 - k) ≤ ‖1 - κ₁ * u‖ ^ 2 / (1 - ‖κ₁‖ ^ 2)) : κ₁ * u = -k := by
  have ht0 := norm_nonneg κ₁
  have hk0 : 0 ≤ k := ht0.trans hκ₁
  have hx : ‖κ₁ * u‖ ≤ k := by
    rw [norm_mul]
    nlinarith [norm_nonneg u]
  set x := κ₁ * u with hxdef
  have hden : 0 < 1 - ‖κ₁‖ ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by linarith) hden] at hB
  have hsq : (1 + k) ^ 2 ≤ ‖1 - x‖ ^ 2 := by
    have h1 : (1 + k) ^ 2 * (1 - k) ≤ ‖1 - x‖ ^ 2 * (1 - k) := by
      nlinarith [pow_le_pow_left₀ ht0 hκ₁ 2]
    exact le_of_mul_le_mul_right h1 (by linarith)
  have hexp : ‖1 - x‖ ^ 2 = 1 - 2 * x.re + ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_eq_norm_sq]
    simp
    ring
  have hx2 : ‖x‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hre : x.re ≤ -k := by nlinarith
  have hre' : -k ≤ x.re := by
    have := Complex.abs_re_le_norm x
    rw [abs_le] at this
    linarith
  have hxre : x.re = -k := le_antisymm hre hre'
  have him : x.im = 0 := by
    have h := Complex.sq_norm x
    rw [Complex.normSq_apply, hxre] at h
    have h2 : x.im ^ 2 = 0 := by nlinarith [sq_nonneg x.im]
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  exact Complex.ext (by simp [hxre]) (by simp [him])

/-- `|a / |a|| = 1` for `a ≠ 0`. -/
theorem m35_norm_div_eq_one {a : ℂ} (ha : a ≠ 0) : ‖a / (‖a‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 ha).ne']

/-- The Wirtinger algebra of the uniqueness step: `B/A · (d̄/d) = -(e/d)` gives `A e + B d̄ = 0`. -/
theorem m35_dzbar_comp_zero {A B d e : ℂ} (hA : A ≠ 0) (hd : d ≠ 0)
    (h : B / A * (conj d / d) = -(e / d)) : A * e + B * conj d = 0 := by
  field_simp at h
  linear_combination h

/-- **Theorem 35.2 (Reich–Strebel)**: let `φ` be holomorphic in `Δ` with `‖φ‖ = ∬|φ| < ∞`, and
`f₀ : Δ → Δ` a Teichmüller map with complex dilatation `k φ̄/|φ|`.  If `f : Δ → Δ` is quasiconformal
with `f|∂Δ = f₀|∂Δ` then `K[f₀] ≤ K[f]`, with equality only for `f = f₀`. -/
theorem thm35_2_reich_strebel {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) {f₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hf₀ : IsQuasiconformal f₀ unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc)
    (hμ : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z = k * conj (φ z) / ‖φ z‖) {f : ℂ → ℂ}
    (hf : IsQuasiconformal f unitDisc) (hfs : f '' unitDisc = unitDisc) {F F₀ : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f unitDisc unitDisc F) (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀)
    (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) :
    maxDilatation f₀ unitDisc ≤ maxDilatation f unitDisc ∧
      (maxDilatation f unitDisc = maxDilatation f₀ unitDisc → EqOn f f₀ unitDisc) := by
  refine ⟨m35_thm35_2_le hφ hk₀ hk hf₀ hf₀s hμ hf hfs hF hF₀ hbd, fun hEq => ?_⟩
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hmain := thm35_2_main_inequality hf hf₀ hfs hf₀s hF hF₀ hbd hφ
  have hμk := m35_rs_norm_le hk₀ hμ
  have hKf₀ := m35_maxDilatation_le_of_ae_le hf₀ hk₀ hk hμk
  obtain ⟨K₀, hK₀⟩ := hf₀
  obtain ⟨K, hK⟩ := hf
  set K₁ : ℝ := (1 + k) / (1 - k) with hK₁def
  have hK₁1 : 1 ≤ K₁ := (one_le_div (by linarith)).2 (by linarith)
  have hfK : IsKQC f unitDisc K₁ := UniversalTeichmuller.ut_md_isKQC_of_le hK hK₁1 (hEq ▸ hKf₀)
  have hck : (K₁ - 1) / (K₁ + 1) = k := by
    rw [hK₁def]
    have : (1 : ℝ) - k ≠ 0 := by linarith
    field_simp
    ring
  have hκ₁ : ∀ᵐ z ∂(volume.restrict unitDisc), ‖mainIneqKappa₁ f f₀ z‖ ≤ k := by
    have h := m35_kappa1_ae_le hfK hK₀ hfs hf₀s
    rwa [hck] at h
  -- the key identity `κ₁ τ = -κ` a.e.
  have hC : ∀ᵐ z ∂(volume.restrict unitDisc),
      mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z = -mainIneqKappa f₀ z := by
    by_cases hz : EqOn φ 0 unitDisc
    · -- degenerate: `κ = 0` and `f` is `1`-q.c., so `κ₁ = 0`
      have hμ0 : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z = 0 := by
        filter_upwards [hμ, ae_restrict_mem hΔ] with z h1 h2
        rw [h1, hz h2]
        simp
      have hμ0' : ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation f₀ z‖ ≤ 0 := by
        filter_upwards [hμ0] with z hz'
        simp [hz']
      have h1 := m35_maxDilatation_le_of_ae_le ⟨K₀, hK₀⟩ le_rfl zero_lt_one hμ0'
      norm_num at h1
      have hf1 : IsKQC f unitDisc 1 :=
        UniversalTeichmuller.ut_md_isKQC_of_le hK le_rfl (by rw [ENNReal.ofReal_one, hEq]; exact h1)
      have h2 := m35_kappa1_ae_le hf1 hK₀ hfs hf₀s
      filter_upwards [h2, hμ0] with z hz1 hz2
      norm_num at hz1
      simp only [mainIneqKappa]
      rw [hz1, hz2]
      simp
    · have hne := ae_ne_zero_of_differentiableOn_unitDisc hφ.1 hz
      -- pointwise: the integrand of the main inequality is `≤ |φ|`
      set Q : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖φ z‖ *
        (‖1 - mainIneqKappa f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) *
        (‖1 - mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ z / ‖φ z‖) *
            (1 - conj (mainIneqKappa f₀ z) * conj (φ z) / ‖φ z‖) /
            (1 - mainIneqKappa f₀ z * φ z / ‖φ z‖)‖ ^ 2 / (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2))) with hQ
      have hQle : ∀ᵐ z ∂(volume.restrict unitDisc), Q z ≤ ENNReal.ofReal ‖φ z‖ := by
        filter_upwards [hμ, hne, hκ₁] with z h1 h2 h3
        obtain ⟨e1, e2, e3⟩ := m35_rs_point hk₀ h2 h1
        have hA := m35_rs_first_factor hk e1 e3
        have hB := m35_mainIneq_second_le (κ := mainIneqKappa f₀ z) (p := φ z) hk h3
          (m35_norm_conj_div_le_one (dz f₀ z))
        simp only [hQ, mainIneqKappa] at hB ⊢
        rw [hA]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : 0 ≤ (1 - k) / (1 + k) := div_nonneg (by linarith) (by linarith)
        calc _ ≤ ‖φ z‖ * ((1 - k) / (1 + k)) * ((1 + k) / (1 - k)) :=
              mul_le_mul_of_nonneg_left hB (mul_nonneg (norm_nonneg _) hc)
          _ = ‖φ z‖ := by
              have : (1 : ℝ) + k ≠ 0 := by linarith
              have : (1 : ℝ) - k ≠ 0 := by linarith
              field_simp
      have hm : AEMeasurable (fun z => ENNReal.ofReal ‖φ z‖) (volume.restrict unitDisc) :=
        (hφ.1.continuousOn.norm.aestronglyMeasurable hΔ).aemeasurable.ennreal_ofReal
      have hQfin : ∫⁻ z in unitDisc, Q z ≠ ⊤ :=
        ne_top_of_le_ne_top hφ.2.ne (lintegral_mono_ae hQle)
      have hQeq := ae_eq_of_ae_le_of_lintegral_le hQle hQfin hm hmain
      filter_upwards [hQeq, hμ, hne, hκ₁] with z hQz h1 h2 h3
      obtain ⟨e1, e2, e3⟩ := m35_rs_point hk₀ h2 h1
      have hA := m35_rs_first_factor hk e1 e3
      simp only [hQ, mainIneqKappa] at hQz ⊢
      rw [hA, e1, e2] at hQz
      have hk1 : (1 : ℂ) - k ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hsimp : mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ z / ‖φ z‖) * (1 - (k : ℂ)) /
          (1 - k) = mainIneqKappa₁ f f₀ z * (mainIneqTau f₀ z * (φ z / ‖φ z‖)) := by
        rw [mul_div_assoc, div_self hk1, mul_one, mul_assoc]
      rw [hsimp] at hQz
      have hpos : 0 < ‖φ z‖ := norm_pos_iff.2 h2
      have hc : 0 < (1 - k) / (1 + k) := div_pos (by linarith) (by linarith)
      have hden : 0 < 1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2 := by
        nlinarith [norm_nonneg (mainIneqKappa₁ f f₀ z)]
      have hBnn : 0 ≤ ‖1 - mainIneqKappa₁ f f₀ z * (mainIneqTau f₀ z * (φ z / ‖φ z‖))‖ ^ 2 /
          (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2) := div_nonneg (sq_nonneg _) hden.le
      have hreal := (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (mul_nonneg hpos.le hc.le) hBnn)
        hpos.le).1 hQz
      have hBval : (1 + k) / (1 - k) ≤
          ‖1 - mainIneqKappa₁ f f₀ z * (mainIneqTau f₀ z * (φ z / ‖φ z‖))‖ ^ 2 /
            (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2) := by
        have h4 : ‖φ z‖ * ((1 - k) / (1 + k)) * ((1 + k) / (1 - k)) = ‖φ z‖ := by
          have : (1 : ℝ) + k ≠ 0 := by linarith
          have : (1 : ℝ) - k ≠ 0 := by linarith
          field_simp
        have h5 : ‖φ z‖ * ((1 - k) / (1 + k)) *
            (‖1 - mainIneqKappa₁ f f₀ z * (mainIneqTau f₀ z * (φ z / ‖φ z‖))‖ ^ 2 /
              (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2)) =
            ‖φ z‖ * ((1 - k) / (1 + k)) * ((1 + k) / (1 - k)) := by rw [h4, hreal]
        exact (mul_left_cancel₀ (mul_pos hpos hc).ne' h5).ge
      have hu : ‖mainIneqTau f₀ z * (φ z / ‖φ z‖)‖ ≤ 1 := by
        rw [norm_mul]
        calc ‖mainIneqTau f₀ z‖ * ‖φ z / (‖φ z‖ : ℂ)‖ ≤ 1 * 1 := by
              gcongr
              · exact m35_norm_conj_div_le_one (dz f₀ z)
              · exact m35_norm_div_norm_le_one (φ z)
          _ = 1 := one_mul 1
      have hx := m35_second_factor_eq hk h3 hu hBval
      -- multiply by `v̄`, `|v| = 1`
      have hvv : (φ z / (‖φ z‖ : ℂ)) * conj (φ z / (‖φ z‖ : ℂ)) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, m35_norm_div_eq_one h2]
        norm_num
      rw [h1]
      calc mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z
          = mainIneqKappa₁ f f₀ z * (mainIneqTau f₀ z * (φ z / ‖φ z‖)) *
              conj (φ z / (‖φ z‖ : ℂ)) := by
            rw [mul_assoc, mul_assoc, hvv, mul_one]
        _ = -(k * conj (φ z) / ‖φ z‖) := by
            rw [hx, map_div₀, Complex.conj_ofReal]
            ring
  -- `g = f⁻¹ ∘ f₀` has `∂_z̄ g = 0` a.e.
  set a := Function.invFunOn f unitDisc with hadef
  have hfi : InjOn f unitDisc := hK.2.2.1.2.1
  have haK : IsKQC a unitDisc K₁ := by
    have h := thm7_2_inv hfK
    rwa [hfs] at h
  have hda := m35_ae_comp hK₀ hf₀s
    ((thm9_3_differentiable_ae haK).and (thm9_6_cor2_jacobian_pos haK))
  have hμg : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (a ∘ f₀) z = complexDilatation id z := by
    filter_upwards [hC, thm9_3_differentiable_ae hK₀, thm9_6_cor2_jacobian_pos hK₀, hda]
      with z hCz hdz hJz hdaz
    obtain ⟨hdaz, hJaz⟩ := hdaz
    have hd0 : dz f₀ z ≠ 0 := by
      intro h0
      rw [jacobian, h0, norm_zero] at hJz
      nlinarith [norm_nonneg (dzbar f₀ z)]
    have ha0 : dz a (f₀ z) ≠ 0 := by
      intro h0
      rw [jacobian, h0, norm_zero] at hJaz
      nlinarith [norm_nonneg (dzbar a (f₀ z))]
    have hchain := eq6_2_dzbar_comp hdz hdaz
    rw [← (eq6_3 hdz).1] at hchain
    have hzero : dzbar (a ∘ f₀) z = 0 := by
      rw [hchain]
      simp only [mainIneqKappa₁, mainIneqTau, mainIneqKappa, complexDilatation] at hCz
      exact m35_dzbar_comp_zero ha0 hd0 hCz
    rw [complexDilatation, hzero, zero_div]
    simp [complexDilatation, dzbar]
  -- boundary values of `g` are the identity; Theorem 13.4 gives `g = id`
  have hFinv := m35_isHomeoExtension_invFunOn hfi hfs hF
  have hmaps₀ : MapsTo f₀ unitDisc unitDisc := fun z hz => hf₀s ▸ mem_image_of_mem f₀ hz
  have hG := hFinv.comp hF₀ hmaps₀
  have hgK : IsKQC (a ∘ f₀) unitDisc (K₀ * K₁) := thm7_1_comp hK₀ haK hf₀s.subset
  have hgimg : (a ∘ f₀) '' unitDisc = unitDisc := by
    rw [image_comp, hf₀s]
    conv_lhs => rw [← hfs]
    exact hfi.leftInvOn_invFunOn.image_image
  have hbdry : ∀ ζ : ℂ, ‖ζ‖ = 1 →
      (Function.invFunOn F (closure (toExt unitDisc)) ∘ F₀) (ζ : ExtPlane) = id (ζ : ExtPlane) := by
    intro ζ hζ
    simp only [Function.comp_apply, id]
    rw [← hbd ζ hζ]
    exact hF.2.2.1.leftInvOn_invFunOn (s35a_x_mem_closure hζ)
  obtain ⟨p, hpinj, hnorm⟩ := m35_three_circle_points
  have hpD : ∀ i, p i ∈ frontier (toExt unitDisc) := by
    intro i
    obtain ⟨ζ, hζ, hpi⟩ := hnorm i
    rw [hpi, s35a_x_frontier_disc]
    exact ⟨ζ, mem_sphere_zero_iff_norm.2 hζ, rfl⟩
  have hFG : ∀ i, (Function.invFunOn F (closure (toExt unitDisc)) ∘ F₀) (p i) = id (p i) := by
    intro i
    obtain ⟨ζ, hζ, hpi⟩ := hnorm i
    rw [hpi]
    exact hbdry ζ hζ
  have hid : IsQuasiconformal (id : ℂ → ℂ) unitDisc :=
    ⟨1, isKQC_one_of_conformal isOpen_ball ⟨differentiableOn_id, injOn_id _, image_id _⟩⟩
  have heq := thm13_4_uniqueness m35_isJordanDomain_unitDisc m35_isJordanDomain_unitDisc ⟨_, hgK⟩ hid
    hgimg (image_id _) hμg hG (isHomeoExtension_id unitDisc) hpinj hpD hFG
  intro z hz
  have h1 : a (f₀ z) = z := heq hz
  have hmem : f₀ z ∈ f '' unitDisc := hfs.symm ▸ hmaps₀ hz
  calc f z = f (a (f₀ z)) := by rw [h1]
    _ = f₀ z := Function.invFunOn_eq hmem

/-- The stretch `affineStretch 1 K` written as the affine map `z ↦ ((K+1)/2) z + ((K-1)/2) z̄ + 0`. -/
theorem s35a_v_stretch_eq (K : ℝ) :
    affineStretch 1 K = fun z => (((K + 1) / 2 : ℝ) : ℂ) * z + (((K - 1) / 2 : ℝ) : ℂ) * conj z + 0 := by
  funext z
  apply Complex.ext <;> simp [affineStretch] <;> ring

/-- The stretch `affineStretch 1 K` (`K > 1`) is `K`-quasiconformal in the plane, with constant complex dilatation
`(K-1)/(K+1)`. -/
theorem s35a_v_stretch_isKQC {K : ℝ} (hK : 1 < K) :
    IsKQC (affineStretch 1 K) univ K ∧
      ∀ z, complexDilatation (affineStretch 1 K) z = (((K - 1) / (K + 1) : ℝ) : ℂ) := by
  have hA : ‖(((K + 1) / 2 : ℝ) : ℂ)‖ = (K + 1) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hB : ‖(((K - 1) / 2 : ℝ) : ℂ)‖ = (K - 1) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hlt : ‖(((K - 1) / 2 : ℝ) : ℂ)‖ < ‖(((K + 1) / 2 : ℝ) : ℂ)‖ := by rw [hA, hB]; linarith
  obtain ⟨h1, h2⟩ := affine_isC1Quasiconformal (C := 0) hlt
  rw [← s35a_v_stretch_eq] at h1 h2
  have hq : (‖(((K + 1) / 2 : ℝ) : ℂ)‖ + ‖(((K - 1) / 2 : ℝ) : ℂ)‖) /
      (‖(((K + 1) / 2 : ℝ) : ℂ)‖ - ‖(((K - 1) / 2 : ℝ) : ℂ)‖) = K := by
    rw [hA, hB]; ring
  rw [hq] at h1
  refine ⟨isKQC_of_isC1Quasiconformal h1, fun z => ?_⟩
  rw [(h2 z).1]
  have hK1 : ((K : ℂ) + 1) ≠ 0 := by exact_mod_cast (by linarith : K + 1 ≠ 0)
  push_cast
  field_simp

/-- The stretch `affineStretch 1 K` (`K > 0`) maps the right half-plane onto itself and the plane onto itself, and fixes
the imaginary axis pointwise. -/
theorem s35a_v_stretch_image {K : ℝ} (hK : 0 < K) :
    affineStretch 1 K '' {z : ℂ | 0 < z.re} = {z : ℂ | 0 < z.re} ∧ affineStretch 1 K '' univ = univ ∧
      ∀ w : ℂ, w.re = 0 → affineStretch 1 K w = w := by
  have hre : ∀ z, (affineStretch 1 K z).re = K * z.re := fun z => by simp [affineStretch]
  have hinv : ∀ w : ℂ, affineStretch 1 K (((w.re / K : ℝ) : ℂ) + w.im * I) = w := fun w => by
    apply Complex.ext
    · simp [affineStretch]
      field_simp
    · simp [affineStretch]
  refine ⟨?_, eq_univ_of_forall fun w => ⟨_, mem_univ _, hinv w⟩, fun w hw => ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (affineStretch 1 K z).re
      rw [hre]
      exact mul_pos hK hz
    · intro hw
      refine ⟨_, ?_, hinv w⟩
      show 0 < (((w.re / K : ℝ) : ℂ) + w.im * I).re
      have hw' : 0 < w.re := hw
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
      positivity
  · apply Complex.ext <;> simp [affineStretch, hw]

/-- §35.3 (the condition `‖φ‖ < ∞` cannot be dropped): the stretch `x + iy ↦ Kx + iy` (`K > 1`) of
the right half-plane, transported to `Δ`, is a Teichmüller map fixing every boundary point which is
not extremal (the identity has the same boundary values). -/
theorem halfplane_stretch_not_extremal {K : ℝ} (hK : 1 < K) {c : ℂ → ℂ}
    (hc : IsConformalOnto c {z : ℂ | 0 < z.re} unitDisc) {C : ExtPlane → ExtPlane}
    (hC : IsHomeoExtension c {z : ℂ | 0 < z.re} unitDisc C) :
    ∃ f₀ : ℂ → ℂ, (∀ z ∈ unitDisc, f₀ z = c (affineStretch 1 K (Function.invFunOn c {z : ℂ | 0 < z.re} z))) ∧
      HasBoundaryValues f₀ id ∧ (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc ∧ (∃ z ∈ unitDisc, φ z ≠ 0) ∧
        ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z = ((K - 1) / (K + 1)) * conj (φ z) / ‖φ z‖) ∧
      ¬ IsExtremalForBoundary f₀ id := by
  obtain ⟨hSq, hSμ⟩ := s35a_v_stretch_isKQC hK
  obtain ⟨hSRH, hSuniv, hSfix⟩ := s35a_v_stretch_image (by linarith : (0 : ℝ) < K)
  set RH : Set ℂ := {z : ℂ | 0 < z.re}
  set S := affineStretch 1 K
  set ψ := Function.invFunOn c RH
  have hRHo : IsOpen RH := isOpen_lt continuous_const Complex.continuous_re
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hψ : IsConformalOnto ψ unitDisc RH := hc.symm hRHo
  have hψc : ∀ w ∈ RH, ψ (c w) = w := fun w hw => hc.2.1.leftInvOn_invFunOn hw
  have hcψ : ∀ z ∈ unitDisc, c (ψ z) = z := fun z hz =>
    Function.invFunOn_eq (show z ∈ c '' RH from hc.2.2.symm ▸ hz)
  have hψmem : ∀ z ∈ unitDisc, ψ z ∈ RH := fun z hz =>
    Function.invFunOn_mem (show z ∈ c '' RH from hc.2.2.symm ▸ hz)
  have hcmem : ∀ w ∈ RH, c w ∈ unitDisc := fun w hw => hc.2.2 ▸ mem_image_of_mem c hw
  have hSmem : ∀ w ∈ RH, S w ∈ RH := fun w hw => hSRH ▸ mem_image_of_mem S hw
  have hScont : Continuous S := continuousOn_univ.1 hSq.2.2.1.1
  have hd0 : ∀ z ∈ unitDisc, deriv ψ z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hΔo hψ.1 hψ.2.1 hz
  -- boundary values
  have hHBV : HasBoundaryValues (fun z => c (S (ψ z))) id := by
    refine ⟨⟨K, ?_⟩, ?_, ?_⟩
    · have h1 := thm7_1_comp (isKQC_one_of_conformal hΔo hψ) (ac_t_isKQC_restrict hSq hRHo (subset_univ _))
        hψ.2.2.subset
      have h2 := thm7_1_comp h1 (isKQC_one_of_conformal hRHo hc) (by rw [image_comp, hψ.2.2, hSRH])
      rw [one_mul, mul_one] at h2
      exact h2
    · show (c ∘ S ∘ ψ) '' unitDisc = unitDisc
      rw [image_comp, image_comp, hψ.2.2, hSRH, hc.2.2]
    · obtain ⟨e, he⟩ := t1_homeomorph hSq hSuniv
      have hE : IsHomeoExtension S RH RH e.onePointCongr := by
        have := s13x_de_isHomeoExtension_homeomorph e RH
        rwa [he, hSRH] at this
      have hΨ := isHomeoExtension_invFunOn hc hC
      have h1 := hE.comp hΨ hψmem
      have h2 := hC.comp h1 (fun z hz => hSmem _ (hψmem z hz))
      refine ⟨_, h2, fun ζ hζ => ?_⟩
      have hζcl : (ζ : ExtPlane) ∈ closure (toExt unitDisc) := by
        refine image_closure_subset_closure_image OnePoint.continuous_coe ⟨ζ, ?_, rfl⟩
        rw [unitDisc, closure_ball _ one_ne_zero, mem_closedBall, dist_zero_right, hζ]
      rw [← hC.2.2.2] at hζcl
      obtain ⟨hp1, hp2⟩ := Function.invFunOn_pos hζcl
      have hfix : ∀ q ∈ closure (toExt RH), C q = ζ → e.onePointCongr q = q := by
        intro q hq1 hq2
        induction q using OnePoint.rec with
        | infty => rfl
        | coe w =>
          have hw : w ∈ closure RH := by
            rw [OnePoint.isOpenEmbedding_coe.closure_eq_preimage_closure_image]
            exact hq1
          have hnot : w ∉ RH := by
            intro hwR
            rw [hC.1 w hwR] at hq2
            have hcw : c w = ζ := OnePoint.coe_injective hq2
            have := hcmem w hwR
            rw [hcw, unitDisc, mem_ball, dist_zero_right, hζ] at this
            exact lt_irrefl _ this
          have hre : w.re = 0 := le_antisymm (not_lt.1 hnot) (closure_lt_subset_le continuous_const
            Complex.continuous_re hw)
          show ((e w : ℂ) : ExtPlane) = w
          rw [he, hSfix w hre]
      show C (e.onePointCongr (Function.invFunOn C (closure (toExt RH)) ζ)) = ζ
      rw [hfix _ hp1 hp2, hp2]
  -- the complex dilatation
  have hμ : ∀ z ∈ unitDisc, complexDilatation (fun z => c (S (ψ z))) z =
      (((K - 1) / (K + 1) : ℝ) : ℂ) * (conj (deriv ψ z) / deriv ψ z) := by
    intro z hz
    have hzψ : ψ z ∈ RH := hψmem z hz
    have hw : S (ψ z) ∈ RH := hSmem _ hzψ
    have hψz : DifferentiableAt ℂ ψ z := hψ.1.differentiableAt (hΔo.mem_nhds hz)
    have hcont : ContinuousAt (S ∘ ψ) z := hScont.continuousAt.comp hψz.continuousAt
    have h1 := s23_dilatation_comp_left (h := c) (k := ψ) hcont (hc.1.differentiableAt (hRHo.mem_nhds hw))
      (hψ.1.differentiableAt (hΔo.mem_nhds (hcmem _ hw))) (eventually_of_mem (hRHo.mem_nhds hw) hψc)
    have h2 := s23_dilatation_comp_right (g := S) hψz (hc.1.differentiableAt (hRHo.mem_nhds hzψ))
      (eventually_of_mem (hΔo.mem_nhds hz) hcψ) (eventually_of_mem (hRHo.mem_nhds hzψ) hψc)
    show complexDilatation (c ∘ (S ∘ ψ)) z = _
    rw [h1, h2, hSμ]
  have hφeq : ∀ d : ℂ, d ≠ 0 → conj d / d = conj (d ^ 2) / ((‖d ^ 2‖ : ℝ) : ℂ) := by
    intro d hd
    have hn : ((‖d ^ 2‖ : ℝ) : ℂ) = d * conj d := by
      rw [norm_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hc0 : conj d ≠ 0 := (map_ne_zero _).2 hd
    rw [hn, map_pow]
    field_simp
  -- the pointwise dilatation quotient is `K`
  have hq : ∀ z ∈ unitDisc, (‖dz (fun z => c (S (ψ z))) z‖ + ‖dzbar (fun z => c (S (ψ z))) z‖) /
      (‖dz (fun z => c (S (ψ z))) z‖ - ‖dzbar (fun z => c (S (ψ z))) z‖) = K := by
    intro z hz
    have hu : ‖conj (deriv ψ z) / deriv ψ z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (hd0 z hz))]
    have hkpos : 0 < (K - 1) / (K + 1) := div_pos (by linarith) (by linarith)
    have hnμ : ‖complexDilatation (fun z => c (S (ψ z))) z‖ = (K - 1) / (K + 1) := by
      rw [hμ z hz, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkpos]
    have hdz : dz (fun z => c (S (ψ z))) z ≠ 0 := by
      intro h0
      rw [complexDilatation, h0, div_zero, norm_zero] at hnμ
      linarith
    have hpos : 0 < ‖dz (fun z => c (S (ψ z))) z‖ := norm_pos_iff.2 hdz
    have hdzbar : ‖dzbar (fun z => c (S (ψ z))) z‖ = (K - 1) / (K + 1) * ‖dz (fun z => c (S (ψ z))) z‖ := by
      rw [← hnμ, complexDilatation, norm_div, div_mul_cancel₀ _ hpos.ne']
    rw [hdzbar]
    have hK1 : K + 1 ≠ 0 := by linarith
    have hne : ‖dz (fun z => c (S (ψ z))) z‖ - (K - 1) / (K + 1) * ‖dz (fun z => c (S (ψ z))) z‖ ≠ 0 := by
      have : ‖dz (fun z => c (S (ψ z))) z‖ - (K - 1) / (K + 1) * ‖dz (fun z => c (S (ψ z))) z‖ =
          2 / (K + 1) * ‖dz (fun z => c (S (ψ z))) z‖ := by field_simp; ring
      rw [this]
      exact mul_ne_zero (div_ne_zero two_ne_zero hK1) hpos.ne'
    rw [div_eq_iff hne]
    field_simp
    ring
  have hΔ0 : volume.restrict unitDisc ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (measure_ball_pos volume (0 : ℂ) one_pos).ne'
  have hmd : maxDilatation (fun z => c (S (ψ z))) unitDisc = ENNReal.ofReal K := by
    rw [maxDilatation, essSup_congr_ae (g := fun _ => ENNReal.ofReal K)
      (ae_restrict_of_forall_mem (show MeasurableSet unitDisc from measurableSet_ball) fun z hz => by
        dsimp only; rw [hq z hz]),
      essSup_const _ hΔ0]
  have hid : maxDilatation id unitDisc ≤ 1 := by
    have h1 : ∀ z, dz id z = 1 ∧ dzbar id z = 0 := by
      intro z
      simp only [dz, dzbar, fderiv_id, ContinuousLinearMap.id_apply, I_mul_I]
      constructor <;> ring
    refine essSup_le_of_ae_le 1 (Eventually.of_forall fun z => ?_)
    simp [h1 z]
  refine ⟨fun z => c (S (ψ z)), fun z _ => rfl, hHBV, ⟨fun z => deriv ψ z ^ 2, (hψ.1.deriv hΔo).pow 2,
    ⟨0, mem_ball_self one_pos, pow_ne_zero 2 (hd0 0 (mem_ball_self one_pos))⟩,
    ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_⟩, fun hext => ?_⟩
  · dsimp only
    rw [hμ z hz, hφeq _ (hd0 z hz)]
    push_cast
    ring
  · have hidb : HasBoundaryValues id id :=
      ⟨⟨1, isKQC_one_of_conformal hΔo ⟨differentiableOn_id, injOn_id _, image_id _⟩⟩, image_id _, id,
        ⟨fun z _ => rfl, continuousOn_id, injOn_id _, image_id _⟩, fun ζ _ => rfl⟩
    have h := (hext.2 id hidb).trans hid
    rw [hmd, ENNReal.ofReal_le_one] at h
    linarith

/-! ## §35.4 Necessary and sufficient conditions for extremality -/

/-- `I[κ] = sup_{‖φ‖=1} |∬ κφ/(1 - |κ|²)|`. -/
def hamiltonI (κ : ℂ → ℂ) : ℝ :=
  ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1),
    ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖

/-- `H[κ] = sup_{‖φ‖=1} |∬ κφ|`. -/
def hamiltonH (κ : ℂ → ℂ) : ℝ :=
  ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), ‖∫ z in unitDisc, κ z * φ z‖

/-- `Δ[κ] = sup_{‖φ‖=1} ∬ |φ| |κ|²/(1 - |κ|²)`. -/
def hamiltonDelta (κ : ℂ → ℂ) : ℝ :=
  ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1),
    ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)

/-- The essential supremum `‖κ‖_∞` of a Beltrami coefficient on `Δ`. -/
def beltramiNormDisc (κ : ℂ → ℂ) : ℝ :=
  (essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc)).toReal

/-- (35.6): for `f₀` with boundary values `h` and dilatation `κ`, and `K₀` the extremal dilatation for
`h`, `1/K₀ ≤ ∬ |φ| |1 - κφ/|φ||²/(1 - |κ|²)` for all holomorphic `φ` with `‖φ‖ = 1`. -/
theorem eq35_6 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h) {f : ℂ → ℂ}
    (hf : IsExtremalForBoundary f h) {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) (hn : phiArea φ unitDisc = 1) :
    (maxDilatation f unitDisc)⁻¹ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ *
      (‖1 - complexDilatation f₀ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖complexDilatation f₀ z‖ ^ 2))) := by
  obtain ⟨hq₀, hs₀, F₀, hF₀, hF₀h⟩ := hf₀
  obtain ⟨⟨hq, hs, F, hF, hFh⟩, -⟩ := hf
  have hm := main_inequality_simplified hq hq₀ hs hs₀ hF hF₀
    (fun ζ hζ => (hFh ζ hζ).trans (hF₀h ζ hζ).symm) hφ
  rw [hn] at hm
  obtain ⟨K, hK⟩ := hq
  have h1 : 1 ≤ maxDilatation f unitDisc := UniversalTeichmuller.ut_md_one_le hK ⟨0, by simp [unitDisc]⟩
  have hfin : maxDilatation f unitDisc ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK).1
  rw [ENNReal.inv_le_iff_le_mul (fun _ => (zero_lt_one.trans_le h1).ne') (fun h => absurd h hfin)]
  exact hm

/-- Under `‖κ‖_∞ < 1` (in `ℝ≥0∞`), `k = beltramiNormDisc κ` is a genuine bound: `0 ≤ k < 1` and
`|κ| ≤ k` almost everywhere on `Δ`. -/
theorem beltramiNormDisc_facts {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) :
    0 ≤ beltramiNormDisc κ ∧ beltramiNormDisc κ < 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ beltramiNormDisc κ := by
  have hEne : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) ≠ ⊤ :=
    (hκ.trans (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  refine ⟨ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [beltramiNormDisc, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hEne (by norm_num)).2 hκ
  · filter_upwards [ENNReal.ae_le_essSup (fun z => (‖κ z‖₊ : ℝ≥0∞))] with z hz
    rw [beltramiNormDisc, show ‖κ z‖ = ((‖κ z‖₊ : ℝ≥0∞)).toReal by simp]
    exact (ENNReal.toReal_le_toReal (by simp) hEne).2 hz

/-- For an admissible `φ`, `|φ|` is integrable on `Δ` with integral `1`. -/
theorem integrableOn_norm_of_admissible {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) :
    IntegrableOn (fun z => ‖φ z‖) unitDisc ∧ ∫ z in unitDisc, ‖φ z‖ = 1 := by
  have hφm : AEStronglyMeasurable (fun z => ‖φ z‖) (volume.restrict unitDisc) :=
    (hφ.1.1.continuousOn.norm).aestronglyMeasurable measurableSet_ball
  have hφfin : HasFiniteIntegral (fun z => ‖φ z‖) (volume.restrict unitDisc) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have hrw : ∀ z : ℂ, ‖‖φ z‖‖ₑ = ENNReal.ofReal ‖φ z‖ := by
      intro z
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [hrw]
    rw [show (∫⁻ z in unitDisc, ENNReal.ofReal ‖φ z‖) = phiArea φ unitDisc from rfl, hφ.2]
    exact ENNReal.one_lt_top
  have hφint : IntegrableOn (fun z => ‖φ z‖) unitDisc := ⟨hφm, hφfin⟩
  refine ⟨hφint, ?_⟩
  have hnn : (0 : ℂ → ℝ) ≤ᵐ[volume.restrict unitDisc] fun z => ‖φ z‖ :=
    Filter.Eventually.of_forall fun z => by
      simp only [Pi.zero_apply]
      exact norm_nonneg (φ z)
  have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφint hnn
  rw [show (∫⁻ z in unitDisc, ENNReal.ofReal ‖φ z‖) = phiArea φ unitDisc from rfl, hφ.2] at h
  have h1 : ENNReal.ofReal (∫ z in unitDisc, ‖φ z‖) = ENNReal.ofReal 1 := by
    rw [h]
    simp
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun z => norm_nonneg _) zero_le_one).1 h1

/-- Splitting `Δ` along a measurable `B`: if `|F| ≤ w β₁` on `B` and `|F| ≤ w β₂` off `B`, with
`∬_Δ w = 1`, then `|∬_Δ F| ≤ β₁ ∬_{Δ ∩ B} w + β₂`. -/
theorem norm_setIntegral_le_two_level {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} {w : ℂ → ℝ} {B : Set ℂ} (hB : MeasurableSet B)
    (hw1 : ∫⁻ z in unitDisc, ENNReal.ofReal (w z) = 1) {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (h1 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∈ B → ‖F z‖ ≤ w z * β₁)
    (h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ B → ‖F z‖ ≤ w z * β₂) :
    ‖∫ z in unitDisc, F z‖ ≤ β₁ * (∫⁻ z in unitDisc ∩ B, ENNReal.ofReal (w z)).toReal + β₂ := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hsplit_w := lintegral_inter_add_diff (μ := volume) (fun z => ENNReal.ofReal (w z)) unitDisc hB
  rw [hw1] at hsplit_w
  have hsplit_F := lintegral_inter_add_diff (μ := volume) (fun z => ENNReal.ofReal ‖F z‖) unitDisc hB
  rw [ae_restrict_iff' hΔ] at h1 h2
  have hb1 : ∫⁻ z in unitDisc ∩ B, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal β₁ * ∫⁻ z in unitDisc ∩ B, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hΔ.inter hB)]
    filter_upwards [h1] with z hz hzB
    rw [← ENNReal.ofReal_mul hβ₁]
    exact ENNReal.ofReal_le_ofReal (by linarith [hz hzB.1 hzB.2])
  have hb2 : ∫⁻ z in unitDisc \ B, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal β₂ * ∫⁻ z in unitDisc \ B, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hΔ.diff hB)]
    filter_upwards [h2] with z hz hzB
    rw [← ENNReal.ofReal_mul hβ₂]
    exact ENNReal.ofReal_le_ofReal (by linarith [hz hzB.1 hzB.2])
  set a := ∫⁻ z in unitDisc ∩ B, ENNReal.ofReal (w z) with ha_def
  set b := ∫⁻ z in unitDisc \ B, ENNReal.ofReal (w z) with hb_def
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_add_self)
  have hab : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hsplit_w, ENNReal.toReal_one]
  have hFle : ∫⁻ z in unitDisc, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal β₁ * a + ENNReal.ofReal β₂ * b := by
    rw [← hsplit_F]
    exact add_le_add hb1 hb2
  have hRtop : ENNReal.ofReal β₁ * a + ENNReal.ofReal β₂ * b ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb⟩
  have hFr : (∫⁻ z in unitDisc, ENNReal.ofReal ‖F z‖).toReal ≤ β₁ * a.toReal + β₂ * b.toReal := by
    have h := ENNReal.toReal_mono hRtop hFle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hβ₁, ENNReal.toReal_ofReal hβ₂] at h
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict unitDisc) F
  have hbr : b.toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := a)]
  nlinarith [mul_le_mul_of_nonneg_left hbr hβ₂]

/-- Upper bound for the suprema `I[κ]`, `H[κ]`, `Δ[κ]` of §35.4. -/
theorem hamiltonSup_le {G : (ℂ → ℂ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ φ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 → G φ ≤ B) :
    ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ ≤ B :=
  Real.iSup_le (fun φ => Real.iSup_le (fun hφ => hG φ hφ) hB) hB

/-- The suprema of §35.4 of a nonnegative functional are nonnegative. -/
theorem hamiltonSup_nonneg {G : (ℂ → ℂ) → ℝ} (hG : ∀ φ, 0 ≤ G φ) :
    0 ≤ ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ :=
  Real.iSup_nonneg fun φ => Real.iSup_nonneg fun _ => hG φ

/-- Each admissible value lies below the supremum, for a functional bounded on the admissible set. -/
theorem le_hamiltonSup {G : (ℂ → ℂ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ φ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 → G φ ≤ B) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) :
    G φ ≤ ⨆ (ψ : ℂ → ℂ) (_ : ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1), G ψ := by
  have hbdd : BddAbove (range fun ψ : ℂ → ℂ =>
      ⨆ (_ : ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1), G ψ) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact Real.iSup_le (fun hψ => hG ψ hψ) hB
  calc G φ = ⨆ (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ :=
        (ciSup_pos (f := fun _ => G φ) hφ).symm
    _ ≤ _ := le_ciSup hbdd φ

/-- Every complex number is rotated onto its modulus by a unimodular factor. -/
theorem exists_unit_mul_eq_norm (v : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ u * v = (‖v‖ : ℂ) := by
  by_cases hv : v = 0
  · exact ⟨1, norm_one, by simp [hv]⟩
  have hn : (‖v‖ : ℂ) ≠ 0 := by simpa using hv
  refine ⟨conj v / (‖v‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hv)]
  · rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
    ring

/-- A unimodular multiple of an admissible function is admissible. -/
theorem rotate_mem_hamiltonSet {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) {u : ℂ}
    (hu : ‖u‖ = 1) :
    (fun z => u * φ z) ∈ integrableQD ∧ phiArea (fun z => u * φ z) unitDisc = 1 := by
  have harea : phiArea (fun z => u * φ z) unitDisc = phiArea φ unitDisc := by
    simp only [phiArea, norm_mul, hu, one_mul]
  refine ⟨⟨hφ.1.1.const_mul u, ?_⟩, harea.trans hφ.2⟩
  rw [harea]
  exact hφ.1.2

/-- A q.c. map of `Δ` has `‖μ_f‖_∞ < 1` (in `ℝ≥0∞`). -/
theorem m35_essSup_lt_one {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) :
    essSup (fun z => (‖complexDilatation f z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1 := by
  obtain ⟨K, hK⟩ := hf
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hμ := (isKQC_maxDilatation_le hK).2
  have hc1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  calc essSup (fun z => (‖complexDilatation f z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc)
      ≤ ENNReal.ofReal ((K - 1) / (K + 1)) := by
        refine essSup_le_of_ae_le _ ?_
        filter_upwards [hμ] with z hz
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal hz
    _ < 1 := ENNReal.ofReal_lt_one.2 hc1

/-- `K[f] ≤ (1 + k)/(1 - k)` for a q.c. self-map of `Δ`, `k = ‖μ_f‖_∞` (Theorem 10.2 (⇐)). -/
theorem m35_maxDilatation_le {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) :
    maxDilatation f unitDisc ≤ ENNReal.ofReal ((1 + beltramiNormDisc (complexDilatation f)) /
      (1 - beltramiNormDisc (complexDilatation f))) := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf)
  obtain ⟨K, hK⟩ := hf
  have hb : IsBeltramiCoeff (complexDilatation f) unitDisc (beltramiNormDisc (complexDilatation f)) :=
    ⟨((measurable_dzbar f).div (measurable_dz f)).aestronglyMeasurable, hae⟩
  exact (isKQC_maxDilatation_le (thm10_2_isKQC_of_genHomeoSolution isOpen_ball hk0 hk1 hb
    (thm10_2_genHomeoSolution_of_isKQC hK).2)).1

/-- The pointwise expansion behind (35.7): for `|κ| < 1`,
`|φ| |1 - κφ/|φ||²/(1 - |κ|²) = |φ| + 2 |φ||κ|²/(1 - |κ|²) - 2 Re(κφ/(1 - |κ|²))`. -/
theorem m35_expand {κ p : ℂ} (hκ : ‖κ‖ < 1) :
    ‖p‖ * (‖1 - κ * p / ‖p‖‖ ^ 2 / (1 - ‖κ‖ ^ 2)) =
      ‖p‖ + 2 * (‖p‖ * ‖κ‖ ^ 2 / (1 - ‖κ‖ ^ 2)) - 2 * (κ * p / (1 - ‖κ‖ ^ 2)).re := by
  have hd : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hdC : (1 - (‖κ‖ : ℂ) ^ 2) = ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hdC, Complex.div_ofReal_re]
  by_cases hp : p = 0
  · simp [hp]
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  set w : ℂ := κ * p / (‖p‖ : ℂ) with hw
  have hwre : w.re = (κ * p).re / ‖p‖ := by rw [hw, Complex.div_ofReal_re]
  have hwn : ‖w‖ = ‖κ‖ := by
    rw [hw, norm_div, norm_mul, Complex.norm_real, norm_norm]
    field_simp
  have hsq : ‖1 - w‖ ^ 2 = 1 + ‖κ‖ ^ 2 - 2 * w.re := by
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, ← hwn, Complex.normSq_eq_norm_sq]
    simp
  rw [hsq, hwre]
  field_simp
  ring

/-- Integrability bookkeeping for (35.7): for admissible `φ` and measurable `κ` with `|κ| ≤ k < 1` a.e.,
the `Δ`- and `I`-integrands are integrable on `Δ`. -/
theorem m35_integrable_terms {κ φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ k) :
    IntegrableOn (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) unitDisc ∧
      IntegrableOn (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2)) unitDisc := by
  obtain ⟨hφint, -⟩ := integrableOn_norm_of_admissible hφ
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hφm : AEMeasurable φ (volume.restrict unitDisc) :=
    (hφ.1.1.continuousOn.aestronglyMeasurable measurableSet_ball).aemeasurable
  constructor
  · refine Integrable.mono' (hφint.mul_const (k ^ 2 / (1 - k ^ 2))) ?_ ?_
    · exact ((hφm.norm.mul (hκm.aemeasurable.norm.pow_const 2)).div
        (aemeasurable_const.sub (hκm.aemeasurable.norm.pow_const 2))).aestronglyMeasurable
    · filter_upwards [hae] with z hz
      have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
      rw [Real.norm_of_nonneg (div_nonneg (by positivity) hp.le), mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [div_le_div_iff₀ hp hq]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
  · have hκφm : AEMeasurable (fun z => κ z * φ z) (volume.restrict unitDisc) :=
      hκm.aemeasurable.mul hφm
    have hdm : AEMeasurable (fun z => (1 - (‖κ z‖ : ℂ) ^ 2)) (volume.restrict unitDisc) :=
      aemeasurable_const.sub
        ((Complex.measurable_ofReal.comp_aemeasurable hκm.aemeasurable.norm).pow_const 2)
    refine Integrable.mono' (hφint.mul_const (k / (1 - k ^ 2))) (hκφm.div hdm).aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    rw [norm_div, norm_mul, show (1 - (‖κ z‖ : ℂ) ^ 2) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm ‖κ z‖, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_le_div_iff₀ hp hq]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (κ z)) hk0) (sub_nonneg.2 hz)]

/-- (35.7) for one admissible `φ`: `Re ∬ κφ/(1 - |κ|²) ≤ k₀/(1 + k₀) + ∬ |φ||κ|²/(1 - |κ|²)`, from (35.6)
and `K[f] ≤ (1 + k₀)/(1 - k₀)`. -/
theorem m35_eq35_7_re {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h) {f : ℂ → ℂ}
    (hf : IsExtremalForBoundary f h) {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) :
    (∫ z in unitDisc, complexDilatation f₀ z * φ z / (1 - ‖complexDilatation f₀ z‖ ^ 2)).re ≤
      dilatationNorm f / (1 + dilatationNorm f) +
        ∫ z in unitDisc, ‖φ z‖ * ‖complexDilatation f₀ z‖ ^ 2 / (1 - ‖complexDilatation f₀ z‖ ^ 2) := by
  set κ := complexDilatation f₀ with hκdef
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf₀.1)
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) :=
    ((measurable_dzbar f₀).div (measurable_dz f₀)).aestronglyMeasurable
  obtain ⟨hDint, hIint⟩ := m35_integrable_terms hφ hκm hk0 hk1 hae
  obtain ⟨hφint, hφ1⟩ := integrableOn_norm_of_admissible hφ
  obtain ⟨hk₀0, hk₀1, -⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf.1.1)
  have hKle := m35_maxDilatation_le hf.1.1
  have hk₀eq : dilatationNorm f = beltramiNormDisc (complexDilatation f) := rfl
  rw [hk₀eq]
  set k₀ := beltramiNormDisc (complexDilatation f) with hk₀def
  have hpos : 0 < (1 + k₀) / (1 - k₀) := div_pos (by linarith) (by linarith)
  have h6 := eq35_6 hf₀ hf hφ.1 hφ.2
  set P : ℂ → ℝ := fun z => ‖φ z‖ * (‖1 - κ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) with hP
  have hlow : ENNReal.ofReal ((1 - k₀) / (1 + k₀)) ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (P z) := by
    refine le_trans ?_ h6
    rw [show (1 - k₀) / (1 + k₀) = ((1 + k₀) / (1 - k₀))⁻¹ by rw [inv_div],
      ENNReal.ofReal_inv_of_pos hpos]
    exact ENNReal.inv_le_inv.2 hKle
  have hexp : ∀ᵐ z ∂(volume.restrict unitDisc), P z =
      ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) - 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    filter_upwards [hae] with z hz
    exact m35_expand (hz.trans_lt hk1)
  have hre_int : IntegrableOn (fun z => (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) unitDisc := by
    simpa using hIint.re
  have hSint : IntegrableOn (fun z => ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) -
      2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) unitDisc :=
    (hφint.add (hDint.const_mul 2)).sub (hre_int.const_mul 2)
  have hPint : IntegrableOn P unitDisc := hSint.congr (by
    filter_upwards [hexp] with z hz
    exact hz.symm)
  have hP0 : ∀ᵐ z ∂(volume.restrict unitDisc), 0 ≤ P z := by
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    exact mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) hp.le)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hPint hP0] at hlow
  have hreal : (1 - k₀) / (1 + k₀) ≤ ∫ z in unitDisc, P z :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hP0)).1 hlow
  have hre : ∫ z in unitDisc, (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re =
      (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    simpa using integral_re hIint
  have hsplit : ∫ z in unitDisc, P z = 1 + 2 * (∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) -
      2 * (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    have hB2 : IntegrableOn (fun z => 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) unitDisc :=
      hDint.const_mul 2
    have hA1 : IntegrableOn (fun z => ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) unitDisc :=
      hφint.add hB2
    have hA2 : IntegrableOn (fun z => 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) unitDisc :=
      hre_int.const_mul 2
    rw [integral_congr_ae hexp, integral_sub hA1 hA2, integral_add hφint hB2, integral_const_mul,
      integral_const_mul, hφ1, hre]
  have hval : 1 - (1 - k₀) / (1 + k₀) = 2 * (k₀ / (1 + k₀)) := by
    field_simp
    ring
  linarith

/-- (35.7): with `k₀ = (K₀ - 1)/(K₀ + 1)`, (35.6) is equivalent to `I[κ] ≤ k₀/(1 + k₀) + Δ[κ]`.

*Correction.*  The book prints `k₀/(1 - k₀)` in (35.7), but its own derivation ends at
`k₀/(1 + k₀)`: expanding `|1 - κφ/|φ||²` in (35.6) and using `1/K₀ = (1-k₀)/(1+k₀)`,
`‖φ‖ = 1` gives `Re ∬ κφ/(1-|κ|²) ≤ k₀/(1+k₀) + ∬|φ||κ|²/(1-|κ|²)`, and taking the supremum
over the phase of `φ` yields the above.  The sharper constant is the one the book then uses:
(35.9) reads `I[κ] ≤ k₀/(1+k₀) + k²/(1-k²)`, and Theorem 35.3 needs exactly
`k/(1+k) ≤ k₀/(1+k₀)` to conclude `k ≤ k₀`, which `k₀/(1-k₀)` would not give. -/
theorem eq35_7 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h) {f : ℂ → ℂ}
    (hf : IsExtremalForBoundary f h) :
    hamiltonI (complexDilatation f₀) ≤ dilatationNorm f / (1 + dilatationNorm f) + hamiltonDelta (complexDilatation f₀) := by
  set κ := complexDilatation f₀ with hκdef
  have hκ := m35_essSup_lt_one hf₀.1
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  obtain ⟨hk₀0, hk₀1, -⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf.1.1)
  have hk₀eq : dilatationNorm f = beltramiNormDisc (complexDilatation f) := rfl
  have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  have hup : ∀ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 →
      ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤
        beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by
    intro φ hφ
    have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ (∅ : Set ℂ) →
        ‖‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤
          ‖φ z‖ * (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2)) := by
      filter_upwards [hae] with z hz _
      have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
      rw [Real.norm_of_nonneg (div_nonneg (by positivity) hp.le), mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [div_le_div_iff₀ hp hq]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
    have h := norm_setIntegral_le_two_level (F := fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (w := fun z => ‖φ z‖) MeasurableSet.empty hφ.2 le_rfl (div_nonneg (by positivity) hq.le)
      (Filter.Eventually.of_forall fun z hz => hz.elim) h2
    simp only [zero_mul, zero_add, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hΔ0 : 0 ≤ hamiltonDelta κ :=
    hamiltonSup_nonneg (G := fun φ => ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      fun φ => integral_nonneg_of_ae (by
        filter_upwards [hae] with z hz
        have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
        exact div_nonneg (by positivity) hp.le)
  have hB0 : 0 ≤ dilatationNorm f / (1 + dilatationNorm f) + hamiltonDelta κ :=
    add_nonneg (div_nonneg (hk₀eq ▸ hk₀0) (by rw [hk₀eq]; linarith)) hΔ0
  refine hamiltonSup_le hB0 fun φ hφ => ?_
  obtain ⟨u, hu1, hu⟩ := exists_unit_mul_eq_norm (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2))
  have hφ' := rotate_mem_hamiltonSet hφ hu1
  have hre := m35_eq35_7_re hf₀ hf hφ'
  have hI' : ∫ z in unitDisc, κ z * (u * φ z) / (1 - ‖κ z‖ ^ 2) =
      ((‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖ : ℝ) : ℂ) := by
    rw [← hu, ← integral_const_mul]
    congr 1
    funext z
    ring
  have hD' : ∫ z in unitDisc, ‖u * φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) =
      ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
    congr 1
    funext z
    rw [norm_mul, hu1, one_mul]
  have hDle : ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤ hamiltonDelta κ :=
    le_hamiltonSup (G := fun φ => ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (div_nonneg (by positivity) hq.le) hup hφ
  rw [hI', Complex.ofReal_re, hD'] at hre
  linarith

/-- (35.8): `Δ[κ] ≤ k²/(1 - k²)`, `k = ‖κ‖_∞`; (35.9): `I[κ] ≤ k₀/(1 + k₀) + k²/(1 - k²)`.

**Correction.**  This previously took a bare `(κ : ℂ → ℂ)` with no bound on `‖κ‖_∞`, and was
**false**.  The bound needs `t ↦ t²/(1 - t²)` to be monotone, which it is on `[0, 1)` but not
across `1`: it runs to `+∞` as `t → 1⁻` and reappears at `-∞` beyond.  Concretely, let `κ = 0` on
part of `Δ` and `κ = 2` on a set `S` of positive measure; then `k = 2`, the right-hand side is
`4/(1 - 4) = -4/3 < 0`, while the integrand vanishes off `S`, so choosing `φ` with little mass on
`S` makes the integral close to `0`, above `-4/3`.  The `k = 1` case fails separately: `1 - k² = 0`
makes the right-hand side the junk value `0` while the left-hand side is a supremum of
non-negative integrals.  In the book (35.8) appears inside the proof of Theorem 35.3, where `κ` is
the complex dilatation of a quasiconformal `f₀ : Δ → Δ`, so `‖κ‖_∞ < 1` holds ambiently and never
needed stating; its three siblings `lemma35_4`, `lemma35_5`, `lemma35_6` do state it.

The hypothesis is on the essential supremum **in `ℝ≥0∞`**, not `beltramiNormDisc κ < 1`, and that
distinction matters: `beltramiNormDisc` is a `.toReal`, and `(⊤ : ℝ≥0∞).toReal = 0`, so
`beltramiNormDisc κ < 1` is *also satisfied by an unbounded* `κ` — with value `0`, making the
right-hand side `0` while an unbounded `κ` that is `1/2` on a set of positive measure still gives a
positive left-hand side.  So `beltramiNormDisc κ < 1` would not have repaired the statement.  (The
three siblings `lemma35_4`, `lemma35_5`, `lemma35_6` carried that weaker form and are now restated
in the `ℝ≥0∞` form as well.  They are still `sorry`, so nothing false was proved, but `lemma35_5`
and `lemma35_6` would have been genuinely suspect: with `‖κ‖_∞ = ⊤` the junk value makes them
assert something about an unbounded `κ`.  `lemma35_4` was merely vacuous, its two bounds on the
auxiliary constant becoming contradictory.) -/
theorem eq35_8 {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) :
    hamiltonDelta κ ≤ beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by
  have hEne : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) ≠ ⊤ :=
    (hκ.trans (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have hk1 : beltramiNormDisc κ < 1 := by
    rw [beltramiNormDisc, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hEne (by norm_num)).2 hκ
  have hk0 : 0 ≤ beltramiNormDisc κ := ENNReal.toReal_nonneg
  have hden : (0 : ℝ) < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  have hRnn : 0 ≤ beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by positivity
  -- `‖κ z‖ ≤ k` almost everywhere on `Δ`
  have hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ beltramiNormDisc κ := by
    filter_upwards [ENNReal.ae_le_essSup (fun z => (‖κ z‖₊ : ℝ≥0∞))] with z hz
    rw [beltramiNormDisc, show ‖κ z‖ = ((‖κ z‖₊ : ℝ≥0∞)).toReal by simp]
    exact (ENNReal.toReal_le_toReal (by simp) hEne).2 hz
  -- and then `t ↦ t²/(1-t²)` is monotone on `[0, k]`
  have hpt : ∀ z, ‖κ z‖ ≤ beltramiNormDisc κ →
      ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)
        ≤ beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by
    intro z hzk
    have h0 : (0 : ℝ) ≤ ‖κ z‖ := norm_nonneg _
    have hd1 : (0 : ℝ) < 1 - ‖κ z‖ ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hd1 hden]
    nlinarith
  refine Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) hRnn) hRnn
  -- `φ` has area norm one, so `∫_Δ ‖φ‖ = 1`
  have hφcont : ContinuousOn φ unitDisc := hφ.1.1.continuousOn
  have hφm : AEStronglyMeasurable (fun z => ‖φ z‖) (volume.restrict unitDisc) :=
    (hφcont.norm).aestronglyMeasurable measurableSet_ball
  have hφfin : HasFiniteIntegral (fun z => ‖φ z‖) (volume.restrict unitDisc) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have hrw : ∀ z : ℂ, ‖‖φ z‖‖ₑ = ENNReal.ofReal ‖φ z‖ := by
      intro z
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [hrw]
    rw [show (∫⁻ z in unitDisc, ENNReal.ofReal ‖φ z‖) = phiArea φ unitDisc from rfl, hφ.2]
    exact ENNReal.one_lt_top
  have hφint : IntegrableOn (fun z => ‖φ z‖) unitDisc := ⟨hφm, hφfin⟩
  have hφ1 : ∫ z in unitDisc, ‖φ z‖ = 1 := by
    have hnn : (0 : ℂ → ℝ) ≤ᵐ[volume.restrict unitDisc] fun z => ‖φ z‖ :=
      Filter.Eventually.of_forall fun z => by
        simp only [Pi.zero_apply]
        exact norm_nonneg (φ z)
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφint hnn
    rw [show (∫⁻ z in unitDisc, ENNReal.ofReal ‖φ z‖) = phiArea φ unitDisc from rfl, hφ.2] at h
    have h1 : ENNReal.ofReal (∫ z in unitDisc, ‖φ z‖) = ENNReal.ofReal 1 := by
      rw [h]; simp
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun z => norm_nonneg _) zero_le_one).1 h1
  have hIR : IntegrableOn
      (fun z => ‖φ z‖ * (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2))) unitDisc :=
    hφint.mul_const _
  by_cases hint : IntegrableOn
      (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) unitDisc
  · calc ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)
        ≤ ∫ z in unitDisc, ‖φ z‖ * (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2)) := by
          refine MeasureTheory.integral_mono_ae hint hIR ?_
          filter_upwards [hae] with z hz
          calc ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)
              = ‖φ z‖ * (‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) := by ring
            _ ≤ ‖φ z‖ * (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2)) :=
                mul_le_mul_of_nonneg_left (hpt z hz) (norm_nonneg _)
      _ = beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by
          rw [MeasureTheory.integral_mul_const, hφ1, one_mul]
  · rw [MeasureTheory.integral_undef hint]
    exact hRnn

/-- `(1 + k)/(1 - k) ≤ K[f]` for a q.c. map of `Δ`, `k = ‖μ_f‖_∞` (Theorem 9.4 via `K[f]`-q.c.). -/
theorem m35_le_maxDilatation {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc) :
    ENNReal.ofReal ((1 + beltramiNormDisc (complexDilatation f)) /
      (1 - beltramiNormDisc (complexDilatation f))) ≤ maxDilatation f unitDisc := by
  obtain ⟨hk0, hk1, -⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf)
  obtain ⟨K, hK⟩ := hf
  obtain ⟨hK1, hK1q⟩ := UniversalTeichmuller.ut_md_isKQC_toReal hK
    ⟨0, by simp [unitDisc]⟩
  have hfin : maxDilatation f unitDisc ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK).1
  set K₁ := (maxDilatation f unitDisc).toReal with hK₁
  have hμ := (isKQC_maxDilatation_le hK1q).2
  have hc0 : 0 ≤ (K₁ - 1) / (K₁ + 1) := div_nonneg (by linarith) (by linarith)
  have hkle : beltramiNormDisc (complexDilatation f) ≤ (K₁ - 1) / (K₁ + 1) := by
    refine ENNReal.toReal_le_of_le_ofReal hc0 (essSup_le_of_ae_le _ ?_)
    filter_upwards [hμ] with z hz
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hz
  set k := beltramiNormDisc (complexDilatation f)
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by linarith)]
  rw [le_div_iff₀ (by linarith)] at hkle
  nlinarith

/-- **Theorem 35.3**: if the complex dilatation `κ` of `f₀ : Δ → Δ` satisfies `I[κ] = k/(1 - k²)`,
`k = ‖κ‖_∞`, then `f₀` is extremal for its boundary values. -/
theorem thm35_3 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h)
    (hI : hamiltonI (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀) / (1 - beltramiNormDisc (complexDilatation f₀) ^ 2)) :
    IsExtremalForBoundary f₀ h := by
  obtain ⟨f, hf⟩ := thm35_1_exists_extremal ⟨f₀, hf₀⟩
  have h7 := eq35_7 hf₀ hf
  have hκ := m35_essSup_lt_one hf₀.1
  have h8 := eq35_8 hκ
  obtain ⟨hk0, hk1, -⟩ := beltramiNormDisc_facts hκ
  obtain ⟨hk₀0, hk₀1, -⟩ := beltramiNormDisc_facts (m35_essSup_lt_one hf.1.1)
  have hk₀eq : dilatationNorm f = beltramiNormDisc (complexDilatation f) := rfl
  rw [hk₀eq] at h7
  set k := beltramiNormDisc (complexDilatation f₀) with hkdef
  set k₀ := beltramiNormDisc (complexDilatation f) with hk₀def
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hkk : k ≤ k₀ := by
    have h1 : k / (1 - k ^ 2) ≤ k₀ / (1 + k₀) + k ^ 2 / (1 - k ^ 2) := by
      rw [← hI]
      linarith
    have e : k / (1 - k ^ 2) - k ^ 2 / (1 - k ^ 2) = k / (1 + k) := by
      field_simp
      ring
    have h2 : k / (1 + k) ≤ k₀ / (1 + k₀) := by linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at h2
    nlinarith
  refine ⟨hf₀, fun g hg => ?_⟩
  calc maxDilatation f₀ unitDisc ≤ ENNReal.ofReal ((1 + k) / (1 - k)) := m35_maxDilatation_le hf₀.1
    _ ≤ ENNReal.ofReal ((1 + k₀) / (1 - k₀)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
    _ ≤ maxDilatation f unitDisc := m35_le_maxDilatation hf.1.1
    _ ≤ maxDilatation g unitDisc := hf.2 g hg

/-- The splitting estimate behind Lemmas 35.4 and 35.6.  If `|F| = w g(t)` a.e. on `Δ` with
`∬_Δ w = 1`, `0 ≤ t ≤ k` and `g` monotone on `[0, k]`, then
`|∬_Δ F| + (g(k) - g(k')) ∬_{t ≤ k'} w ≤ g(k)`.  No measurability of `t` is assumed: `Δ` is split
along the measurable set `{|F| ≤ w g(k')}` (after a measurable modification), which contains
`{t ≤ k'}` up to a null set; and a non-measurable `F` has the junk integral `0`. -/
theorem hamilton_split_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} {w t : ℂ → ℝ} {g : ℝ → ℝ} {k k' : ℝ}
    (hw : ∀ z, 0 ≤ w z) (hw1 : ∫⁻ z in unitDisc, ENNReal.ofReal (w z) = 1)
    (hwm : AEMeasurable w (volume.restrict unitDisc))
    (hFt : ∀ᵐ z ∂(volume.restrict unitDisc), ‖F z‖ = w z * g (t z) ∧ 0 ≤ t z ∧ t z ≤ k)
    (hg : MonotoneOn g (Icc 0 k)) (hk' : 0 ≤ k') (hk'k : k' ≤ k) (hgk' : 0 ≤ g k') :
    ‖∫ z in unitDisc, F z‖ +
      (g k - g k') * (∫⁻ z in {z ∈ unitDisc | t z ≤ k'}, ENNReal.ofReal (w z)).toReal ≤ g k := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hgk : g k' ≤ g k := hg ⟨hk', hk'k⟩ ⟨hk'.trans hk'k, le_rfl⟩ hk'k
  set m := ∫⁻ z in {z ∈ unitDisc | t z ≤ k'}, ENNReal.ofReal (w z) with hm
  have hm1 : m ≤ 1 := by
    rw [← hw1]
    exact lintegral_mono_set (fun z hz => hz.1)
  have hmr : m.toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hm1
    simpa using h
  have hmr0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  by_cases hF : AEStronglyMeasurable F (volume.restrict unitDisc)
  swap
  · rw [integral_non_aestronglyMeasurable hF, norm_zero, zero_add]
    nlinarith
  -- a measurable version of `{|F| ≤ w g(k')}`
  have hHm : AEMeasurable (fun z => ‖F z‖ - w z * g k') (volume.restrict unitDisc) :=
    hF.norm.aemeasurable.sub (hwm.mul_const _)
  have hHmeas : Measurable (hHm.mk _) := hHm.measurable_mk
  have hHae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖F z‖ - w z * g k' = hHm.mk _ z := hHm.ae_eq_mk
  have hBm : MeasurableSet {z | hHm.mk _ z ≤ 0} := measurableSet_le hHmeas measurable_const
  have hgood : ∀ᵐ z ∂volume, z ∈ unitDisc →
      (‖F z‖ = w z * g (t z) ∧ 0 ≤ t z ∧ t z ≤ k) ∧ ‖F z‖ - w z * g k' = hHm.mk _ z := by
    have h := hFt.and hHae
    rwa [ae_restrict_iff' hΔ] at h
  -- `{t ≤ k'}` lies in `Δ ∩ B` up to a null set
  have hEB : m ≤ ∫⁻ z in unitDisc ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    refine lintegral_mono' (Measure.restrict_mono_ae ?_) le_rfl
    filter_upwards [hgood] with z hz
    intro hzE
    obtain ⟨⟨hF1, ht0, htk⟩, hH⟩ := hz hzE.1
    refine ⟨hzE.1, ?_⟩
    show hHm.mk _ z ≤ 0
    rw [← hH, hF1]
    have hle : g (t z) ≤ g k' := hg ⟨ht0, htk⟩ ⟨hk', hk'k⟩ hzE.2
    nlinarith [mul_nonneg (hw z) (sub_nonneg.2 hle)]
  -- split `Δ` along `B`
  have hsplit_w := lintegral_inter_add_diff (μ := volume) (fun z => ENNReal.ofReal (w z)) unitDisc hBm
  rw [hw1] at hsplit_w
  have hsplit_F := lintegral_inter_add_diff (μ := volume) (fun z => ENNReal.ofReal ‖F z‖) unitDisc hBm
  have h1 : ∫⁻ z in unitDisc ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal (g k') * ∫⁻ z in unitDisc ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hΔ.inter hBm)]
    filter_upwards [hgood] with z hz hzB
    obtain ⟨-, hH⟩ := hz hzB.1
    have hHz : hHm.mk _ z ≤ 0 := hzB.2
    rw [← ENNReal.ofReal_mul hgk']
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h2 : ∫⁻ z in unitDisc \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal (g k) * ∫⁻ z in unitDisc \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hΔ.diff hBm)]
    filter_upwards [hgood] with z hz hzB
    obtain ⟨⟨hF1, ht0, htk⟩, -⟩ := hz hzB.1
    rw [← ENNReal.ofReal_mul (hgk'.trans hgk), hF1]
    have hle : g (t z) ≤ g k := hg ⟨ht0, htk⟩ ⟨hk'.trans hk'k, le_rfl⟩ htk
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (hw z) (sub_nonneg.2 hle)])
  -- real arithmetic
  set a := ∫⁻ z in unitDisc ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) with ha_def
  set b := ∫⁻ z in unitDisc \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) with hb_def
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_add_self)
  have hab : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hsplit_w, ENNReal.toReal_one]
  have hFle : ∫⁻ z in unitDisc, ENNReal.ofReal ‖F z‖ ≤
      ENNReal.ofReal (g k') * a + ENNReal.ofReal (g k) * b := by
    rw [← hsplit_F]
    exact add_le_add h1 h2
  have hRtop : ENNReal.ofReal (g k') * a + ENNReal.ofReal (g k) * b ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb⟩
  have hFr : (∫⁻ z in unitDisc, ENNReal.ofReal ‖F z‖).toReal ≤ g k' * a.toReal + g k * b.toReal := by
    have h := ENNReal.toReal_mono hRtop hFle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hgk', ENNReal.toReal_ofReal (hgk'.trans hgk)] at h
  have hma : m.toReal ≤ a.toReal := ENNReal.toReal_mono ha hEB
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict unitDisc) F
  have hb' : b.toReal = 1 - a.toReal := by linarith
  rw [hb'] at hFr
  nlinarith [mul_nonneg (sub_nonneg.2 hgk) (sub_nonneg.2 hma)]

/-- If `a n + c (m n) ≤ A` with `c > 0`, `m n ≤ 1` and `a n → A`, then `m n → 0`. -/
theorem tendsto_zero_of_add_mul_le {a : ℕ → ℝ} {m : ℕ → ℝ≥0∞} {A c : ℝ} (hc : 0 < c)
    (hm : ∀ n, m n ≤ 1) (hbound : ∀ n, a n + c * (m n).toReal ≤ A)
    (ha : Tendsto a atTop (𝓝 A)) : Tendsto m atTop (𝓝 0) := by
  have hmt : ∀ n, m n ≠ ⊤ := fun n => ne_top_of_le_ne_top ENNReal.one_ne_top (hm n)
  rw [← ENNReal.tendsto_toReal_iff hmt ENNReal.zero_ne_top, ENNReal.toReal_zero]
  have hup : Tendsto (fun n => (A - a n) / c) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := A)).sub ha
    rw [sub_self] at h
    simpa using h.div_const c
  refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hup
  rw [le_div_iff₀ hc]
  linarith [hbound n]

/-- **Lemma 35.4** (35.10): if `‖φₙ‖ = 1` and `∬ κφₙ/(1 - |κ|²) → k/(1 - k²)` (or `∬ κφₙ → k`, or
`∬ |φₙ||κ|²/(1 - |κ|²) → k²/(1 - k²)`), `k = ‖κ‖_∞`, then for every `k' < k`,
`∬_E |φₙ| → 0` where `E = {|κ| ≤ k'}`.

**Correction.**  The bound `‖κ‖_∞ < 1` is stated on the essential supremum **in `ℝ≥0∞`**: the
earlier `beltramiNormDisc κ < 1` is also satisfied by an unbounded `κ`, since
`(⊤ : ℝ≥0∞).toReal = 0`.  See `eq35_8` for the discussion and the counterexample.

Proof: for `g(t) = t/(1 - t²)`, `t` or `t²/(1 - t²)` (matching the three hypotheses) one has
`|Fₙ| = |φₙ| g(|κ|)` a.e., so `hamilton_split_bound` gives
`|∬ Fₙ| + (g(k) - g(k')) ∬_E |φₙ| ≤ g(k)`.  The first term tends to `g(k)` and `g(k') < g(k)`, hence
`∬_E |φₙ| → 0` (`tendsto_zero_of_add_mul_le`).  No measurability of `κ` is needed: the estimate
splits `Δ` along a measurable modification of `{|Fₙ| ≤ |φₙ| g(k')}`, which contains `E` up to a
null set, and a non-measurable `Fₙ` has the junk integral `0`, for which the estimate is trivial. -/
theorem lemma35_4 {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableQD ∧ phiArea (φ n) unitDisc = 1)
    (hlim : Tendsto (fun n => ∫ z in unitDisc, κ z * φ n z / (1 - ‖κ z‖ ^ 2)) atTop
        (𝓝 ((beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) : ℝ) : ℂ)) ∨
      Tendsto (fun n => ∫ z in unitDisc, κ z * φ n z) atTop (𝓝 (beltramiNormDisc κ : ℂ)) ∨
      Tendsto (fun n => ∫ z in unitDisc, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) atTop
        (𝓝 (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2))))
    {k' : ℝ} (hk' : 0 < k') (hk'k : k' < beltramiNormDisc κ) :
    Tendsto (fun n => ∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖) atTop (𝓝 0) := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  set k := beltramiNormDisc κ with hkdef
  have hkk : 0 < 1 - k ^ 2 := by nlinarith
  have hk'k' : 0 < 1 - k' ^ 2 := by nlinarith
  have hw1 : ∀ n, ∫⁻ z in unitDisc, ENNReal.ofReal ‖φ n z‖ = 1 := fun n => (hφ n).2
  have hwm : ∀ n, AEMeasurable (fun z => ‖φ n z‖) (volume.restrict unitDisc) := fun n =>
    ((hφ n).1.1.continuousOn.norm.aestronglyMeasurable measurableSet_ball).aemeasurable
  have hm1 : ∀ n, ∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖ ≤ 1 := fun n => by
    rw [← hw1 n]
    exact lintegral_mono_set (fun z hz => hz.1)
  have hpos : ∀ᵐ z ∂(volume.restrict unitDisc), 0 < 1 - ‖κ z‖ ^ 2 := by
    filter_upwards [hae] with z hz
    nlinarith [norm_nonneg (κ z)]
  rcases hlim with h | h | h
  · -- `g(t) = t/(1 - t²)`
    have hg : MonotoneOn (fun t : ℝ => t / (1 - t ^ 2)) (Icc 0 k) := by
      intro s hs t ht hst
      have hs1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
      have ht1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      show s / (1 - s ^ 2) ≤ t / (1 - t ^ 2)
      rw [div_le_div_iff₀ hs1 ht1]
      nlinarith [mul_nonneg (mul_nonneg hs.1 ht.1) (sub_nonneg.2 hst)]
    have hc : 0 < k / (1 - k ^ 2) - k' / (1 - k' ^ 2) := by
      rw [sub_pos, div_lt_div_iff₀ hk'k' hkk]
      nlinarith [mul_pos (mul_pos hk' (hk'.trans hk'k)) (sub_pos.2 hk'k)]
    have key : ∀ n, ‖∫ z in unitDisc, κ z * φ n z / (1 - ‖κ z‖ ^ 2)‖ +
        (k / (1 - k ^ 2) - k' / (1 - k' ^ 2)) *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal ≤ k / (1 - k ^ 2) := by
      intro n
      have hFt : ∀ᵐ z ∂(volume.restrict unitDisc),
          ‖κ z * φ n z / (1 - ‖κ z‖ ^ 2)‖ = ‖φ n z‖ * (fun t : ℝ => t / (1 - t ^ 2)) ‖κ z‖ ∧
            0 ≤ ‖κ z‖ ∧ ‖κ z‖ ≤ k := by
        filter_upwards [hae, hpos] with z hz hz1
        refine ⟨?_, norm_nonneg _, hz⟩
        have hden : ‖(1 - (‖κ z‖ : ℂ) ^ 2 : ℂ)‖ = 1 - ‖κ z‖ ^ 2 := by
          rw [show (1 - (‖κ z‖ : ℂ) ^ 2 : ℂ) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) by simp, Complex.norm_real,
            Real.norm_of_nonneg hz1.le]
        rw [norm_div, norm_mul, hden]
        ring
      exact hamilton_split_bound (fun z => norm_nonneg _) (hw1 n) (hwm n) hFt hg hk'.le hk'k.le
        (div_nonneg hk'.le hk'k'.le)
    refine tendsto_zero_of_add_mul_le hc hm1 key ?_
    have hn := h.norm
    rwa [Complex.norm_real, Real.norm_of_nonneg (div_nonneg hk0 hkk.le)] at hn
  · -- `g(t) = t`
    have hg : MonotoneOn (fun t : ℝ => t) (Icc 0 k) := fun _ _ _ _ h => h
    have key : ∀ n, ‖∫ z in unitDisc, κ z * φ n z‖ +
        (k - k') * (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal ≤ k := by
      intro n
      have hFt : ∀ᵐ z ∂(volume.restrict unitDisc),
          ‖κ z * φ n z‖ = ‖φ n z‖ * (fun t : ℝ => t) ‖κ z‖ ∧ 0 ≤ ‖κ z‖ ∧ ‖κ z‖ ≤ k := by
        filter_upwards [hae] with z hz
        exact ⟨by rw [norm_mul, mul_comm], norm_nonneg _, hz⟩
      exact hamilton_split_bound (fun z => norm_nonneg _) (hw1 n) (hwm n) hFt hg hk'.le hk'k.le hk'.le
    refine tendsto_zero_of_add_mul_le (sub_pos.2 hk'k) hm1 key ?_
    have hn := h.norm
    rwa [Complex.norm_real, Real.norm_of_nonneg hk0] at hn
  · -- `g(t) = t²/(1 - t²)`
    have hg : MonotoneOn (fun t : ℝ => t ^ 2 / (1 - t ^ 2)) (Icc 0 k) := by
      intro s hs t ht hst
      have hs1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
      have ht1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      show s ^ 2 / (1 - s ^ 2) ≤ t ^ 2 / (1 - t ^ 2)
      rw [div_le_div_iff₀ hs1 ht1]
      nlinarith [mul_le_mul hst hst hs.1 ht.1]
    have hc : 0 < k ^ 2 / (1 - k ^ 2) - k' ^ 2 / (1 - k' ^ 2) := by
      rw [sub_pos, div_lt_div_iff₀ hk'k' hkk]
      nlinarith [mul_lt_mul'' hk'k hk'k hk'.le hk'.le]
    have key : ∀ n, ‖∫ z in unitDisc, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ +
        (k ^ 2 / (1 - k ^ 2) - k' ^ 2 / (1 - k' ^ 2)) *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal ≤
            k ^ 2 / (1 - k ^ 2) := by
      intro n
      have hFt : ∀ᵐ z ∂(volume.restrict unitDisc),
          ‖‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ =
            ‖φ n z‖ * (fun t : ℝ => t ^ 2 / (1 - t ^ 2)) ‖κ z‖ ∧ 0 ≤ ‖κ z‖ ∧ ‖κ z‖ ≤ k := by
        filter_upwards [hae, hpos] with z hz hz1
        refine ⟨?_, norm_nonneg _, hz⟩
        rw [Real.norm_of_nonneg (div_nonneg (by positivity) hz1.le)]
        ring
      exact hamilton_split_bound (fun z => norm_nonneg _) (hw1 n) (hwm n) hFt hg hk'.le hk'k.le
        (div_nonneg (by positivity) hk'k'.le)
    refine tendsto_zero_of_add_mul_le hc hm1 key ?_
    have hn := h.norm
    rwa [Real.norm_of_nonneg (div_nonneg (by positivity) hkk.le)] at hn

/-- The lower bound behind Lemma 35.5: for measurable `κ` with `|κ| ≤ k < 1` a.e. and `0 ≤ k' ≤ k`,
`∬_Δ |φ| |κ|²/(1 - |κ|²) ≥ g(k') - g(k) ∬_{|κ| ≤ k'} |φ|`, `g(t) = t²/(1 - t²)`. -/
theorem integral_phi_kappa_sq_ge {κ φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc)) {k k' : ℝ} (hk1 : k < 1)
    (hk'0 : 0 ≤ k') (hk'k : k' ≤ k) (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ k) :
    k' ^ 2 / (1 - k' ^ 2) - k ^ 2 / (1 - k ^ 2) *
        (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal ≤
      ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hk0 : 0 ≤ k := hk'0.trans hk'k
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hq' : 0 < 1 - k' ^ 2 := by nlinarith
  set s := k ^ 2 / (1 - k ^ 2) with hs_def
  set g' := k' ^ 2 / (1 - k' ^ 2) with hg'_def
  have hs0 : 0 ≤ s := div_nonneg (by positivity) hq.le
  have hgs : g' ≤ s := by
    rw [hg'_def, hs_def, div_le_div_iff₀ hq' hq]
    nlinarith [pow_le_pow_left₀ hk'0 hk'k 2]
  obtain ⟨hφint, hφ1⟩ := integrableOn_norm_of_admissible hφ
  have hφm : AEMeasurable (fun z => ‖φ z‖) (volume.restrict unitDisc) :=
    ((hφ.1.1.continuousOn.norm).aestronglyMeasurable measurableSet_ball).aemeasurable
  have hFm : AEStronglyMeasurable (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (volume.restrict unitDisc) :=
    ((hφm.mul (hκm.aemeasurable.norm.pow_const 2)).div
      (aemeasurable_const.sub (hκm.aemeasurable.norm.pow_const 2))).aestronglyMeasurable
  have hFb : ∀ᵐ z ∂(volume.restrict unitDisc), 0 ≤ ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ∧
      ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤ ‖φ z‖ * s := by
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    refine ⟨div_nonneg (by positivity) hp.le, ?_⟩
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [hs_def, div_le_div_iff₀ hp hq]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
  have hFint : IntegrableOn (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) unitDisc := by
    refine Integrable.mono' (hφint.mul_const s) hFm ?_
    filter_upwards [hFb] with z hz
    rw [Real.norm_of_nonneg hz.1]
    exact hz.2
  have hsplit : ∫ z in unitDisc, (‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) =
      s - ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
    rw [integral_sub (hφint.mul_const s) hFint, integral_mul_const, hφ1, one_mul]
  -- the measurable set `B = {|κ̃| ≤ k'}` for a measurable modification `κ̃`
  have hBm : MeasurableSet {z | ‖hκm.mk κ z‖ ≤ k'} :=
    measurableSet_le hκm.stronglyMeasurable_mk.measurable.norm measurable_const
  have hmk := hκm.ae_eq_mk
  rw [EventuallyEq, ae_restrict_iff' hΔ] at hmk
  have hEB : ({z ∈ unitDisc | ‖κ z‖ ≤ k'} : Set ℂ) =ᵐ[volume]
      (unitDisc ∩ {z | ‖hκm.mk κ z‖ ≤ k'} : Set ℂ) := by
    filter_upwards [hmk] with z hz
    apply propext
    constructor
    · rintro ⟨hzΔ, hzk⟩
      refine ⟨hzΔ, ?_⟩
      show ‖hκm.mk κ z‖ ≤ k'
      rw [← hz hzΔ]
      exact hzk
    · rintro ⟨hzΔ, hzk⟩
      refine ⟨hzΔ, ?_⟩
      show ‖κ z‖ ≤ k'
      rw [hz hzΔ]
      exact hzk
  have h1 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∈ {z | ‖hκm.mk κ z‖ ≤ k'} →
      ‖‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤ ‖φ z‖ * s := by
    filter_upwards [hFb] with z hz _
    rw [Real.norm_of_nonneg (sub_nonneg.2 hz.2)]
    linarith [hz.1]
  have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ {z | ‖hκm.mk κ z‖ ≤ k'} →
      ‖‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤ ‖φ z‖ * (s - g') := by
    filter_upwards [hFb, hae, hκm.ae_eq_mk] with z hz hzk hzm hzB
    have hzk' : k' < ‖κ z‖ := by
      rw [hzm]
      exact lt_of_not_ge hzB
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    have hgt : g' ≤ ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
      rw [hg'_def, div_le_div_iff₀ hq' hp]
      nlinarith [pow_le_pow_left₀ hk'0 hzk'.le 2]
    rw [Real.norm_of_nonneg (sub_nonneg.2 hz.2)]
    have hle : ‖φ z‖ * g' ≤ ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hgt (norm_nonneg _)
    nlinarith
  have hH := norm_setIntegral_le_two_level
    (F := fun z => ‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
    (w := fun z => ‖φ z‖) hBm hφ.2 hs0 (sub_nonneg.2 hgs) h1 h2
  beta_reduce at hH
  rw [← Measure.restrict_congr_set hEB, hsplit, Real.norm_eq_abs] at hH
  have habs := le_abs_self (s - ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
  linarith

/-- **Lemma 35.5**: if `‖φₙ‖ = 1` and `∬_E |φₙ| → 0` (35.10) for every `E = {|κ| ≤ k'}`, `k' < k`,
then `∬ |φₙ| |κ|²/(1 - |κ|²) → k²/(1 - k²)`.

**Correction** (statement).  The book assumes (35.11), `∬_E |φₙ| |κ|²/(1 - |κ|²) → 0`, which does
not suffice: for `κ = ½·1_{Re z > 0}` and `φₙ ≡ 1/π` every such integral over the left half-disc
`E` is `0`, yet `∬ |φₙ| |κ|²/(1 - |κ|²) = 1/6 ≠ 1/3 = k²/(1 - k²)`.  The book's proof in fact uses
(35.10), the conclusion of Lemma 35.4, which is the hypothesis here.  The book also prints the limit
as `k/(1 - k²)`; the correct value is `k²/(1 - k²)`.  Measurability of `κ` (a complex dilatation in
the book) is added, since otherwise the Bochner integral in the conclusion is the junk value `0`.

**Correction.**  The bound `‖κ‖_∞ < 1` is stated on the essential supremum **in `ℝ≥0∞`**: the
earlier `beltramiNormDisc κ < 1` is also satisfied by an unbounded `κ`, since
`(⊤ : ℝ≥0∞).toReal = 0`.  See `eq35_8` for the discussion and the counterexample.

Proof: `≤ k²/(1 - k²)` holds for every `n` (`norm_setIntegral_le_two_level` with `B = ∅`).  For the
lower bound, `integral_phi_kappa_sq_ge` gives `∬ |φₙ| |κ|²/(1 - |κ|²) ≥ g(k') - g(k) ∬_E |φₙ|`
(`g(t) = t²/(1 - t²)`, `E = {|κ| ≤ k'}`), by applying the two-level bound to `|φₙ| g(k) - F`.  With
(35.10) the right-hand side tends to `g(k')`, and `g(k') → g(k)` as `k' → k`.  For `k = 0` the
integrals are nonnegative and bounded by `0`. -/
theorem lemma35_5 {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableQD ∧ phiArea (φ n) unitDisc = 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc))
    (hE : ∀ k' : ℝ, 0 < k' → k' < beltramiNormDisc κ →
      Tendsto (fun n => ∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in unitDisc, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) atTop
      (𝓝 (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2))) := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  -- upper bound `≤ k²/(1 - k²)`
  have hup : ∀ n, ∫ z in unitDisc, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤
      beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2) := by
    intro n
    have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ (∅ : Set ℂ) →
        ‖‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤
          ‖φ n z‖ * (beltramiNormDisc κ ^ 2 / (1 - beltramiNormDisc κ ^ 2)) := by
      filter_upwards [hae] with z hz _
      have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
      rw [Real.norm_of_nonneg (div_nonneg (by positivity) hp.le), mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [div_le_div_iff₀ hp hq]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
    have h := norm_setIntegral_le_two_level (F := fun z => ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (w := fun z => ‖φ n z‖) MeasurableSet.empty (hφ n).2 le_rfl (div_nonneg (by positivity) hq.le)
      (Filter.Eventually.of_forall fun z hz => hz.elim) h2
    simp only [zero_mul, zero_add, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  refine tendsto_order.2 ⟨fun b hb => ?_,
    fun b hb => Filter.Eventually.of_forall fun n => (hup n).trans_lt hb⟩
  set k := beltramiNormDisc κ with hkdef
  rcases hk0.eq_or_lt with hk | hk
  · -- `k = 0`: the integrals are nonnegative
    have hb0 : b < 0 := by
      rw [← hk] at hb
      simpa using hb
    refine Filter.Eventually.of_forall fun n => lt_of_lt_of_le hb0 (integral_nonneg_of_ae ?_)
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    exact div_nonneg (by positivity) hp.le
  · -- choose `k' < k` with `g(k') > b`
    have hgc : ContinuousAt (fun t : ℝ => t ^ 2 / (1 - t ^ 2)) k :=
      (continuousAt_id.pow 2).div (continuousAt_const.sub (continuousAt_id.pow 2)) hq.ne'
    have hδ : Tendsto (fun j : ℕ => k / ((j : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hε : Tendsto (fun j : ℕ => k - k / ((j : ℝ) + 2)) atTop (𝓝 k) := by
      simpa using (tendsto_const_nhds (x := k)).sub hδ
    obtain ⟨j, hj⟩ := ((hgc.tendsto.comp hε).eventually (lt_mem_nhds hb)).exists
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have hk'k : k - k / ((j : ℝ) + 2) < k := by
      have := div_pos hk hj2
      linarith
    have hk'0 : 0 < k - k / ((j : ℝ) + 2) := by
      have : k / ((j : ℝ) + 2) < k := div_lt_self hk (by linarith)
      linarith
    have hj' : b < (k - k / ((j : ℝ) + 2)) ^ 2 / (1 - (k - k / ((j : ℝ) + 2)) ^ 2) := hj
    have hm := hE _ hk'0 hk'k
    have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k - k / ((j : ℝ) + 2)},
        ENNReal.ofReal ‖φ n z‖).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
      rw [ENNReal.toReal_zero] at h
      exact h
    have hlow : Tendsto (fun n => (k - k / ((j : ℝ) + 2)) ^ 2 / (1 - (k - k / ((j : ℝ) + 2)) ^ 2) -
        k ^ 2 / (1 - k ^ 2) * (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k - k / ((j : ℝ) + 2)},
          ENNReal.ofReal ‖φ n z‖).toReal) atTop
        (𝓝 ((k - k / ((j : ℝ) + 2)) ^ 2 / (1 - (k - k / ((j : ℝ) + 2)) ^ 2) - k ^ 2 / (1 - k ^ 2) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hmR)
    rw [mul_zero, sub_zero] at hlow
    filter_upwards [hlow.eventually (lt_mem_nhds hj')] with n hn
    exact hn.trans_le (integral_phi_kappa_sq_ge (hφ n) hκm hk1 hk'0.le hk'k.le hae)

/-- A positive supremum of a bounded functional is the limit along admissible functions. -/
theorem exists_seq_tendsto_hamiltonSup {G : (ℂ → ℂ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ φ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 → G φ ≤ B)
    (hpos : 0 < ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ) :
    ∃ ψ : ℕ → ℂ → ℂ, (∀ n, ψ n ∈ integrableQD ∧ phiArea (ψ n) unitDisc = 1) ∧
      Tendsto (fun n => G (ψ n)) atTop
        (𝓝 (⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ)) := by
  set s := ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1), G φ with hs
  have hex : ∀ n : ℕ, ∃ ψ : ℂ → ℂ, (ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1) ∧
      s - s / ((n : ℝ) + 2) < G ψ := by
    intro n
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hε : 0 < s / ((n : ℝ) + 2) := div_pos hpos hn2
    have hlt : s - s / ((n : ℝ) + 2) < s := by linarith
    obtain ⟨ψ, hψ⟩ := exists_lt_of_lt_ciSup hlt
    by_cases hmem : ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1
    · rw [ciSup_pos hmem] at hψ
      exact ⟨ψ, hmem, hψ⟩
    · rw [ciSup_neg hmem, Real.sSup_empty] at hψ
      have hle : s / ((n : ℝ) + 2) ≤ s := div_le_self hpos.le (by linarith)
      exact absurd hψ (by linarith)
  choose ψ hψS hψ using hex
  refine ⟨ψ, hψS, ?_⟩
  have hε : Tendsto (fun n : ℕ => s / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlow : Tendsto (fun n : ℕ => s - s / ((n : ℝ) + 2)) atTop (𝓝 s) := by
    simpa using (tendsto_const_nhds (x := s)).sub hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => (hψ n).le) (fun n => le_hamiltonSup hB hG (hψS n))

/-- A function of area one does not vanish identically on `Δ`. -/
theorem not_eqOn_zero_of_phiArea_eq_one {φ : ℂ → ℂ} (h : phiArea φ unitDisc = 1) :
    ¬ EqOn φ 0 unitDisc := by
  intro h0
  have h1 : phiArea φ unitDisc = 0 := by
    rw [phiArea]
    exact setLIntegral_eq_zero measurableSet_ball (fun z hz => by simp [h0 hz])
  rw [h] at h1
  exact one_ne_zero h1

/-- If `∬_Δ κφ ≠ 0` for an admissible `φ`, then `κ` is a.e.-strongly measurable on `Δ`. -/
theorem aestronglyMeasurable_of_integral_mul_ne_zero {κ φ : ℂ → ℂ}
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) (h : ∫ z in unitDisc, κ z * φ z ≠ 0) :
    AEStronglyMeasurable κ (volume.restrict unitDisc) := by
  have hF : AEStronglyMeasurable (fun z => κ z * φ z) (volume.restrict unitDisc) := by
    by_contra hc
    exact h (integral_non_aestronglyMeasurable hc)
  have hφm : AEMeasurable φ (volume.restrict unitDisc) :=
    (hφ.1.1.continuousOn.aestronglyMeasurable measurableSet_ball).aemeasurable
  have hne := ae_ne_zero_of_differentiableOn_unitDisc hφ.1.1 (not_eqOn_zero_of_phiArea_eq_one hφ.2)
  have hm : AEMeasurable (fun z => κ z * φ z * (φ z)⁻¹) (volume.restrict unitDisc) :=
    hF.aemeasurable.mul hφm.inv
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hne] with z hz
  exact mul_inv_cancel_right₀ hz (κ z)

/-- `s ↦ 2s/(1 + √(1 + 4s²))` inverts `t ↦ t/(1 - t²)` on `[0, 1)`. -/
theorem two_mul_div_one_add_sqrt_eq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * (t / (1 - t ^ 2)) / (1 + Real.sqrt (1 + 4 * (t / (1 - t ^ 2)) ^ 2)) = t := by
  have hd : 0 < 1 - t ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 + 4 * (t / (1 - t ^ 2)) ^ 2) = (1 + t ^ 2) / (1 - t ^ 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (by positivity) hd)]
    field_simp
    ring
  rw [hsq]
  field_simp
  ring

/-- If `∬_Δ κφ/(1 - |κ|²) ≠ 0` for an admissible `φ` and `|κ| < 1` a.e., then `κ` is a.e.-strongly
measurable on `Δ`: `V = κ/(1 - |κ|²)` is measurable, and `κ = V (1 - τ(|V|)²)` with
`τ(s) = 2s/(1 + √(1 + 4s²))`. -/
theorem aestronglyMeasurable_of_integral_div_ne_zero {κ φ : ℂ → ℂ}
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (hκ1 : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ < 1)
    (h : ∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2) ≠ 0) :
    AEStronglyMeasurable κ (volume.restrict unitDisc) := by
  have hF : AEStronglyMeasurable (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2)) (volume.restrict unitDisc) := by
    by_contra hc
    exact h (integral_non_aestronglyMeasurable hc)
  have hφm : AEMeasurable φ (volume.restrict unitDisc) :=
    (hφ.1.1.continuousOn.aestronglyMeasurable measurableSet_ball).aemeasurable
  have hne := ae_ne_zero_of_differentiableOn_unitDisc hφ.1.1 (not_eqOn_zero_of_phiArea_eq_one hφ.2)
  have hV : AEMeasurable (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2) * (φ z)⁻¹) (volume.restrict unitDisc) :=
    hF.aemeasurable.mul hφm.inv
  have hτ : Continuous fun s : ℝ => 2 * s / (1 + Real.sqrt (1 + 4 * s ^ 2)) :=
    (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_const.add (continuous_const.mul (continuous_pow 2))).sqrt)
      (fun s => by positivity)
  have hm : AEMeasurable (fun z => (κ z * φ z / (1 - ‖κ z‖ ^ 2) * (φ z)⁻¹) *
      (1 - ((2 * ‖κ z * φ z / (1 - ‖κ z‖ ^ 2) * (φ z)⁻¹‖ /
        (1 + Real.sqrt (1 + 4 * ‖κ z * φ z / (1 - ‖κ z‖ ^ 2) * (φ z)⁻¹‖ ^ 2)) : ℝ) : ℂ) ^ 2))
      (volume.restrict unitDisc) :=
    hV.mul (aemeasurable_const.sub
      ((Complex.measurable_ofReal.comp_aemeasurable (hτ.measurable.comp_aemeasurable hV.norm)).pow_const 2))
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hne, hκ1] with z hz hz1
  have ht0 : 0 ≤ ‖κ z‖ := norm_nonneg _
  have hd : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith
  have hcast : (1 - (‖κ z‖ : ℂ) ^ 2) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) := by simp
  have hdc : (1 - (‖κ z‖ : ℂ) ^ 2) ≠ 0 := by
    rw [hcast]
    exact_mod_cast hd.ne'
  have hVz : κ z * φ z / (1 - (‖κ z‖ : ℂ) ^ 2) * (φ z)⁻¹ = κ z / (1 - (‖κ z‖ : ℂ) ^ 2) := by
    field_simp
  have hnV : ‖κ z / (1 - (‖κ z‖ : ℂ) ^ 2)‖ = ‖κ z‖ / (1 - ‖κ z‖ ^ 2) := by
    rw [norm_div, hcast, Complex.norm_real, Real.norm_of_nonneg hd.le]
  rw [hVz, hnV, two_mul_div_one_add_sqrt_eq ht0 hz1]
  field_simp

/-- The comparison of `I` and `H` in the proof of Lemma 35.6: for measurable `κ` with `|κ| ≤ k < 1`
a.e. and `0 ≤ k' ≤ k`,
`|∬ κφ/(1 - |κ|²) - (1 - k²)⁻¹ ∬ κφ| ≤ (1 - k²)⁻² ∬_{|κ| ≤ k'} |φ| + 2(k - k')/(1 - k²)²`. -/
theorem norm_integral_div_sub_le {κ φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc)) {k k' : ℝ} (hk1 : k < 1)
    (hk'0 : 0 ≤ k') (hk'k : k' ≤ k) (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ k) :
    ‖(∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)) -
        (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in unitDisc, κ z * φ z‖ ≤
      1 / (1 - k ^ 2) ^ 2 * (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal +
        2 * (k - k') / (1 - k ^ 2) ^ 2 := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hk0 : 0 ≤ k := hk'0.trans hk'k
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hq' := hq.ne'
  have hφm : AEMeasurable φ (volume.restrict unitDisc) :=
    (hφ.1.1.continuousOn.aestronglyMeasurable measurableSet_ball).aemeasurable
  obtain ⟨hφint, -⟩ := integrableOn_norm_of_admissible hφ
  have hκφm : AEMeasurable (fun z => κ z * φ z) (volume.restrict unitDisc) :=
    hκm.aemeasurable.mul hφm
  have hdm : AEMeasurable (fun z => (1 - (‖κ z‖ : ℂ) ^ 2)) (volume.restrict unitDisc) :=
    aemeasurable_const.sub
      ((Complex.measurable_ofReal.comp_aemeasurable hκm.aemeasurable.norm).pow_const 2)
  have hint2 : IntegrableOn (fun z => κ z * φ z) unitDisc := by
    refine Integrable.mono' (hφint.mul_const k) hκφm.aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have hint1 : IntegrableOn (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2)) unitDisc := by
    refine Integrable.mono' (hφint.mul_const (k / (1 - k ^ 2))) (hκφm.div hdm).aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    rw [norm_div, norm_mul, show (1 - (‖κ z‖ : ℂ) ^ 2) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm ‖κ z‖, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_le_div_iff₀ hp hq]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (κ z)) hk0) (sub_nonneg.2 hz)]
  have hsplit : (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)) -
      (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in unitDisc, κ z * φ z =
      ∫ z in unitDisc, (κ z * φ z / (1 - ‖κ z‖ ^ 2) - (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (κ z * φ z)) := by
    rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul]
  rw [hsplit]
  -- the measurable set `B = {|κ̃| ≤ k'}` for a measurable modification `κ̃`
  have hBm : MeasurableSet {z | ‖hκm.mk κ z‖ ≤ k'} :=
    measurableSet_le hκm.stronglyMeasurable_mk.measurable.norm measurable_const
  have hmk := hκm.ae_eq_mk
  rw [EventuallyEq, ae_restrict_iff' hΔ] at hmk
  have hEB : ({z ∈ unitDisc | ‖κ z‖ ≤ k'} : Set ℂ) =ᵐ[volume]
      (unitDisc ∩ {z | ‖hκm.mk κ z‖ ≤ k'} : Set ℂ) := by
    filter_upwards [hmk] with z hz
    apply propext
    constructor
    · rintro ⟨hzΔ, hzk⟩
      refine ⟨hzΔ, ?_⟩
      show ‖hκm.mk κ z‖ ≤ k'
      rw [← hz hzΔ]
      exact hzk
    · rintro ⟨hzΔ, hzk⟩
      refine ⟨hzΔ, ?_⟩
      show ‖κ z‖ ≤ k'
      rw [hz hzΔ]
      exact hzk
  rw [Measure.restrict_congr_set hEB]
  -- the pointwise identity `|D| = |φ| |κ| ((1 - k²)⁻¹ - (1 - |κ|²)⁻¹)`
  have hpt : ∀ᵐ z ∂(volume.restrict unitDisc),
      ‖κ z * φ z / (1 - ‖κ z‖ ^ 2) - (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (κ z * φ z)‖ =
        ‖φ z‖ * (‖κ z‖ * ((1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹)) ∧ ‖κ z‖ ≤ k ∧
        κ z = hκm.mk κ z := by
    filter_upwards [hae, hκm.ae_eq_mk] with z hz hzm
    refine ⟨?_, hz, hzm⟩
    have hρ : 0 ≤ (1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹ :=
      sub_nonneg.2 (inv_anti₀ hq (by nlinarith [norm_nonneg (κ z)]))
    have heq : κ z * φ z / (1 - ‖κ z‖ ^ 2) - (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (κ z * φ z) =
        -(κ z * φ z * (((1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [heq, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ]
    ring
  refine norm_setIntegral_le_two_level hBm hφ.2 (by positivity)
    (div_nonneg (by linarith) (by positivity)) ?_ ?_
  · filter_upwards [hpt] with z hz _
    obtain ⟨heq, hzk, -⟩ := hz
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    have ht1 : ‖κ z‖ ≤ 1 := by linarith
    have hρ0 : 0 ≤ (1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹ :=
      sub_nonneg.2 (inv_anti₀ hq (by nlinarith [norm_nonneg (κ z)]))
    have hρ1 : (1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹ ≤ 1 / (1 - k ^ 2) ^ 2 := by
      have h1 : (1 - k ^ 2)⁻¹ ≤ 1 / (1 - k ^ 2) ^ 2 := by
        rw [one_div]
        exact inv_anti₀ (pow_pos hq 2) (by nlinarith)
      have h2 : 0 ≤ (1 - ‖κ z‖ ^ 2)⁻¹ := (inv_pos.2 hp).le
      linarith
    calc ‖κ z‖ * ((1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹)
        ≤ 1 * ((1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹) := mul_le_mul_of_nonneg_right ht1 hρ0
      _ ≤ 1 / (1 - k ^ 2) ^ 2 := by rw [one_mul]; exact hρ1
  · filter_upwards [hpt] with z hz hzB
    obtain ⟨heq, hzk, hzm⟩ := hz
    have hzk' : k' < ‖κ z‖ := by
      rw [hzm]
      exact lt_of_not_ge hzB
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    have hp' := hp.ne'
    have hρ : (1 - k ^ 2)⁻¹ - (1 - ‖κ z‖ ^ 2)⁻¹ =
        (k ^ 2 - ‖κ z‖ ^ 2) / ((1 - k ^ 2) * (1 - ‖κ z‖ ^ 2)) := by
      field_simp
      ring
    rw [hρ, ← mul_div_assoc, div_le_div_iff₀ (mul_pos hq hp) (pow_pos hq 2)]
    have ht1 : ‖κ z‖ ≤ 1 := by linarith
    have hkt0 : 0 ≤ k ^ 2 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    have hkt : k ^ 2 - ‖κ z‖ ^ 2 ≤ 2 * (k - k') := by
      have h1 : k' ^ 2 ≤ ‖κ z‖ ^ 2 := pow_le_pow_left₀ hk'0 hzk'.le 2
      nlinarith [mul_le_mul_of_nonneg_left (show k + k' ≤ 2 by linarith) (sub_nonneg.2 hk'k)]
    have hqp : 1 - k ^ 2 ≤ 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    have hA : ‖κ z‖ * (k ^ 2 - ‖κ z‖ ^ 2) ≤ 2 * (k - k') :=
      (mul_le_of_le_one_left hkt0 ht1).trans hkt
    have hB : ‖κ z‖ * (k ^ 2 - ‖κ z‖ ^ 2) * (1 - k ^ 2) ≤ 2 * (k - k') * (1 - ‖κ z‖ ^ 2) :=
      mul_le_mul hA hqp hq.le (by linarith)
    calc ‖κ z‖ * (k ^ 2 - ‖κ z‖ ^ 2) * (1 - k ^ 2) ^ 2
        = (‖κ z‖ * (k ^ 2 - ‖κ z‖ ^ 2) * (1 - k ^ 2)) * (1 - k ^ 2) := by ring
      _ ≤ (2 * (k - k') * (1 - ‖κ z‖ ^ 2)) * (1 - k ^ 2) := mul_le_mul_of_nonneg_right hB hq.le
      _ = 2 * (k - k') * ((1 - k ^ 2) * (1 - ‖κ z‖ ^ 2)) := by ring

/-- `|∬ κφ/(1 - |κ|²)| ≤ k/(1 - k²)` for admissible `φ`; no measurability of `κ` is needed. -/
theorem norm_integral_div_le_of_admissible {κ φ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) :
    ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖ ≤
      beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ (∅ : Set ℂ) →
      ‖κ z * φ z / (1 - ‖κ z‖ ^ 2)‖ ≤ ‖φ z‖ * (beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2)) := by
    filter_upwards [hae] with z hz _
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    rw [norm_div, norm_mul, show (1 - (‖κ z‖ : ℂ) ^ 2) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm ‖κ z‖, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_le_div_iff₀ hp hq]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (κ z)) hk0) (sub_nonneg.2 hz)]
  have h := norm_setIntegral_le_two_level (F := fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2))
    (w := fun z => ‖φ z‖) MeasurableSet.empty hφ.2 le_rfl (div_nonneg hk0 hq.le)
    (Filter.Eventually.of_forall fun z hz => hz.elim) h2
  simpa using h

/-- `|∬ κφ| ≤ k` for admissible `φ`; no measurability of `κ` is needed. -/
theorem norm_integral_mul_le_of_admissible {κ φ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1) :
    ‖∫ z in unitDisc, κ z * φ z‖ ≤ beltramiNormDisc κ := by
  obtain ⟨hk0, -, hae⟩ := beltramiNormDisc_facts hκ
  have h2 : ∀ᵐ z ∂(volume.restrict unitDisc), z ∉ (∅ : Set ℂ) →
      ‖κ z * φ z‖ ≤ ‖φ z‖ * beltramiNormDisc κ := by
    filter_upwards [hae] with z hz _
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have h := norm_setIntegral_le_two_level (F := fun z => κ z * φ z) (w := fun z => ‖φ z‖)
    MeasurableSet.empty hφ.2 le_rfl hk0 (Filter.Eventually.of_forall fun z hz => hz.elim) h2
  simpa using h

/-- If `a - C (k - k') ≤ x` for all `k' ∈ (0, k)`, then `a ≤ x`. -/
theorem le_of_forall_sub_mul_le {a k x C : ℝ} (hk : 0 < k)
    (h : ∀ k', 0 < k' → k' < k → a - C * (k - k') ≤ x) : a ≤ x := by
  have hε : Tendsto (fun n : ℕ => k / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun n : ℕ => a - C * (k / ((n : ℝ) + 2))) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).sub (hε.const_mul C)
  refine le_of_tendsto' hlim fun n => ?_
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : k / ((n : ℝ) + 2) < k := div_lt_self hk (by linarith)
  have h2 := h (k - k / ((n : ℝ) + 2)) (by linarith) (by linarith [div_pos hk hn2])
  rwa [sub_sub_cancel] at h2

/-- Lemma 35.6 (⇒) for `k > 0`: `I[κ] = k/(1 - k²)` implies `H[κ] = k`. -/
theorem hamiltonH_eq_of_hamiltonI_eq {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hk : 0 < beltramiNormDisc κ)
    (hI : hamiltonI κ = beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2)) :
    hamiltonH κ = beltramiNormDisc κ := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  have hs : 0 < beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) := div_pos hk hq
  -- an approximating sequence for `I[κ]`
  obtain ⟨ψ, hψS, hψlim⟩ := exists_seq_tendsto_hamiltonSup
    (G := fun φ => ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖) hs.le
    (fun φ hφ => norm_integral_div_le_of_admissible hκ hφ)
    (show 0 < hamiltonI κ by rw [hI]; exact hs)
  change Tendsto _ atTop (𝓝 (hamiltonI κ)) at hψlim
  rw [hI] at hψlim
  have hκ1 : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ < 1 := by
    filter_upwards [hae] with z hz
    linarith
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) := by
    obtain ⟨N, hN⟩ := (hψlim.eventually (lt_mem_nhds hs)).exists
    exact aestronglyMeasurable_of_integral_div_ne_zero (hψS N) hκ1 (norm_pos_iff.1 hN)
  -- rotate so that the integrals are real and positive
  choose u hu1 hu using fun n =>
    exists_unit_mul_eq_norm (∫ z in unitDisc, κ z * ψ n z / (1 - ‖κ z‖ ^ 2))
  have hφS : ∀ n, (fun z => u n * ψ n z) ∈ integrableQD ∧
      phiArea (fun z => u n * ψ n z) unitDisc = 1 :=
    fun n => rotate_mem_hamiltonSet (hψS n) (hu1 n)
  have hIφ : ∀ n, ∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2) =
      ((‖∫ z in unitDisc, κ z * ψ n z / (1 - ‖κ z‖ ^ 2)‖ : ℝ) : ℂ) := by
    intro n
    rw [← hu n, ← integral_const_mul]
    congr 1
    funext z
    ring
  have hlimφ : Tendsto (fun n => ∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2)) atTop
      (𝓝 ((beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) : ℝ) : ℂ)) := by
    simp only [hIφ]
    exact (Complex.continuous_ofReal.tendsto _).comp hψlim
  have hbH : ∀ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 →
      ‖∫ z in unitDisc, κ z * φ z‖ ≤ beltramiNormDisc κ :=
    fun φ hφ => norm_integral_mul_le_of_admissible hκ hφ
  have hHle : hamiltonH κ ≤ beltramiNormDisc κ := hamiltonSup_le hk0 hbH
  refine le_antisymm hHle (le_of_forall_sub_mul_le (C := 2 / (1 - beltramiNormDisc κ ^ 2)) hk
    fun k' hk' hk'k => ?_)
  have hm := lemma35_4 (φ := fun n z => u n * ψ n z) hκ hφS (Or.inl hlimφ) hk' hk'k
  have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'},
      ENNReal.ofReal ‖u n * ψ n z‖).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
    rw [ENNReal.toReal_zero] at h
    exact h
  have hnormI : Tendsto (fun n => ‖∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2)‖) atTop
      (𝓝 (beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2))) := by
    have h := hlimφ.norm
    rwa [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  set k := beltramiNormDisc κ with hkdef
  have hf : Tendsto (fun n => (1 - k ^ 2) *
      (‖∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2)‖ -
        (1 / (1 - k ^ 2) ^ 2 *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖u n * ψ n z‖).toReal +
          2 * (k - k') / (1 - k ^ 2) ^ 2))) atTop
      (𝓝 ((1 - k ^ 2) * (k / (1 - k ^ 2) -
        (1 / (1 - k ^ 2) ^ 2 * 0 + 2 * (k - k') / (1 - k ^ 2) ^ 2)))) :=
    tendsto_const_nhds.mul (hnormI.sub ((tendsto_const_nhds.mul hmR).add tendsto_const_nhds))
  have hval : (1 - k ^ 2) * (k / (1 - k ^ 2) -
      (1 / (1 - k ^ 2) ^ 2 * 0 + 2 * (k - k') / (1 - k ^ 2) ^ 2)) =
      k - 2 / (1 - k ^ 2) * (k - k') := by
    field_simp
    ring
  rw [hval] at hf
  refine le_of_tendsto' hf fun n => ?_
  have hdiff := norm_integral_div_sub_le (hφS n) hκm hk1 hk'.le hk'k.le hae
  beta_reduce at hdiff
  have hHn : ‖∫ z in unitDisc, κ z * (u n * ψ n z)‖ ≤ hamiltonH κ :=
    le_hamiltonSup (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) hk0 hbH (hφS n)
  have htri := norm_sub_norm_le (∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2))
    ((((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in unitDisc, κ z * (u n * ψ n z))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hq.le)] at htri
  calc (1 - k ^ 2) * (‖∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2)‖ -
        (1 / (1 - k ^ 2) ^ 2 *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖u n * ψ n z‖).toReal +
          2 * (k - k') / (1 - k ^ 2) ^ 2))
      ≤ (1 - k ^ 2) * ((1 - k ^ 2)⁻¹ * ‖∫ z in unitDisc, κ z * (u n * ψ n z)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hq.le
    _ = ‖∫ z in unitDisc, κ z * (u n * ψ n z)‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    _ ≤ hamiltonH κ := hHn

/-- Lemma 35.6 (⇐) for `k > 0`: `H[κ] = k` implies `I[κ] = k/(1 - k²)`. -/
theorem hamiltonI_eq_of_hamiltonH_eq {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hk : 0 < beltramiNormDisc κ) (hH : hamiltonH κ = beltramiNormDisc κ) :
    hamiltonI κ = beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
  have hs : 0 < beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) := div_pos hk hq
  have hbH : ∀ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 →
      ‖∫ z in unitDisc, κ z * φ z‖ ≤ beltramiNormDisc κ :=
    fun φ hφ => norm_integral_mul_le_of_admissible hκ hφ
  have hbI : ∀ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 →
      ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖ ≤
        beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) :=
    fun φ hφ => norm_integral_div_le_of_admissible hκ hφ
  -- an approximating sequence for `H[κ]`
  obtain ⟨ψ, hψS, hψlim⟩ := exists_seq_tendsto_hamiltonSup
    (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) hk0 hbH
    (show 0 < hamiltonH κ by rw [hH]; exact hk)
  change Tendsto _ atTop (𝓝 (hamiltonH κ)) at hψlim
  rw [hH] at hψlim
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) := by
    obtain ⟨N, hN⟩ := (hψlim.eventually (lt_mem_nhds hk)).exists
    exact aestronglyMeasurable_of_integral_mul_ne_zero (hψS N) (norm_pos_iff.1 hN)
  -- rotate so that the integrals are real and positive
  choose u hu1 hu using fun n => exists_unit_mul_eq_norm (∫ z in unitDisc, κ z * ψ n z)
  have hφS : ∀ n, (fun z => u n * ψ n z) ∈ integrableQD ∧
      phiArea (fun z => u n * ψ n z) unitDisc = 1 :=
    fun n => rotate_mem_hamiltonSet (hψS n) (hu1 n)
  have hHφ : ∀ n, ∫ z in unitDisc, κ z * (u n * ψ n z) =
      ((‖∫ z in unitDisc, κ z * ψ n z‖ : ℝ) : ℂ) := by
    intro n
    rw [← hu n, ← integral_const_mul]
    congr 1
    funext z
    ring
  have hlimφ : Tendsto (fun n => ∫ z in unitDisc, κ z * (u n * ψ n z)) atTop
      (𝓝 ((beltramiNormDisc κ : ℝ) : ℂ)) := by
    simp only [hHφ]
    exact (Complex.continuous_ofReal.tendsto _).comp hψlim
  have hIle : hamiltonI κ ≤ beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) :=
    hamiltonSup_le hs.le hbI
  refine le_antisymm hIle (le_of_forall_sub_mul_le (C := 2 / (1 - beltramiNormDisc κ ^ 2) ^ 2) hk
    fun k' hk' hk'k => ?_)
  have hm := lemma35_4 (φ := fun n z => u n * ψ n z) hκ hφS (Or.inr (Or.inl hlimφ)) hk' hk'k
  have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'},
      ENNReal.ofReal ‖u n * ψ n z‖).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
    rw [ENNReal.toReal_zero] at h
    exact h
  have hnormH : Tendsto (fun n => ‖∫ z in unitDisc, κ z * (u n * ψ n z)‖) atTop
      (𝓝 (beltramiNormDisc κ)) := by
    have h := hlimφ.norm
    rwa [Complex.norm_real, Real.norm_of_nonneg hk0] at h
  set k := beltramiNormDisc κ with hkdef
  have hf : Tendsto (fun n => (1 - k ^ 2)⁻¹ * ‖∫ z in unitDisc, κ z * (u n * ψ n z)‖ -
      (1 / (1 - k ^ 2) ^ 2 *
        (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖u n * ψ n z‖).toReal +
        2 * (k - k') / (1 - k ^ 2) ^ 2)) atTop
      (𝓝 ((1 - k ^ 2)⁻¹ * k - (1 / (1 - k ^ 2) ^ 2 * 0 + 2 * (k - k') / (1 - k ^ 2) ^ 2))) :=
    (tendsto_const_nhds.mul hnormH).sub ((tendsto_const_nhds.mul hmR).add tendsto_const_nhds)
  have hval : (1 - k ^ 2)⁻¹ * k - (1 / (1 - k ^ 2) ^ 2 * 0 + 2 * (k - k') / (1 - k ^ 2) ^ 2) =
      k / (1 - k ^ 2) - 2 / (1 - k ^ 2) ^ 2 * (k - k') := by
    field_simp
    ring
  rw [hval] at hf
  refine le_of_tendsto' hf fun n => ?_
  have hdiff := norm_integral_div_sub_le (hφS n) hκm hk1 hk'.le hk'k.le hae
  beta_reduce at hdiff
  have hIn : ‖∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2)‖ ≤ hamiltonI κ :=
    le_hamiltonSup (G := fun φ => ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖) hs.le hbI (hφS n)
  have htri := norm_sub_norm_le ((((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in unitDisc, κ z * (u n * ψ n z))
    (∫ z in unitDisc, κ z * (u n * ψ n z) / (1 - ‖κ z‖ ^ 2))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hq.le), norm_sub_rev] at htri
  linarith

/-- **Lemma 35.6**: `I[κ] = k/(1 - k²)` iff `H[κ] = k` (`k = ‖κ‖_∞`).

**Correction.**  The bound `‖κ‖_∞ < 1` is stated on the essential supremum **in `ℝ≥0∞`**: the
earlier `beltramiNormDisc κ < 1` is also satisfied by an unbounded `κ`, since
`(⊤ : ℝ≥0∞).toReal = 0`.  See `eq35_8` for the discussion and the counterexample.

Proof: both suprema are bounded (`norm_integral_div_le_of_admissible`,
`norm_integral_mul_le_of_admissible`, with no measurability of `κ` needed), and for `k = 0` both
sides hold.  For `k > 0` the given supremum is the limit along admissible `ψₙ`
(`exists_seq_tendsto_hamiltonSup`).  A nonzero integral makes `κ` measurable
(`aestronglyMeasurable_of_integral_div_ne_zero`, `aestronglyMeasurable_of_integral_mul_ne_zero`,
using that the zeros of `ψₙ` form a null set).  Rotating `ψₙ` by unimodular constants makes the
integrals tend to the real supremum, so Lemma 35.4 gives `∬_E |φₙ| → 0`.  The book's estimate
`|∬ κφ/(1 - |κ|²) - (1 - k²)⁻¹ ∬ κφ| ≤ (1 - k²)⁻² ∬_E |φ| + 2(k - k')/(1 - k²)²`
(`norm_integral_div_sub_le`) then bounds the other supremum from below up to `O(k - k')`, and
`k' → k` finishes. -/
theorem lemma35_6 {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) :
    hamiltonI κ = beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) ↔ hamiltonH κ = beltramiNormDisc κ := by
  obtain ⟨hk0, hk1, -⟩ := beltramiNormDisc_facts hκ
  rcases hk0.eq_or_lt with hk | hk
  · have hq : 0 < 1 - beltramiNormDisc κ ^ 2 := by nlinarith
    have hI : hamiltonI κ = beltramiNormDisc κ / (1 - beltramiNormDisc κ ^ 2) :=
      le_antisymm
        (hamiltonSup_le (div_nonneg hk0 hq.le) fun φ hφ => norm_integral_div_le_of_admissible hκ hφ)
        (by
          rw [← hk, zero_div]
          exact hamiltonSup_nonneg (G := fun φ => ‖∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)‖)
            fun _ => norm_nonneg _)
    have hH : hamiltonH κ = beltramiNormDisc κ :=
      le_antisymm (hamiltonSup_le hk0 fun φ hφ => norm_integral_mul_le_of_admissible hκ hφ)
        (by
          rw [← hk]
          exact hamiltonSup_nonneg (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) fun _ => norm_nonneg _)
    exact ⟨fun _ => hH, fun _ => hI⟩
  · exact ⟨hamiltonH_eq_of_hamiltonI_eq hκ hk, hamiltonI_eq_of_hamiltonH_eq hκ hk⟩

/-- **Theorem 35.4 (Reich–Strebel)** (35.12): if the complex dilatation `κ` of `f₀ : Δ → Δ` satisfies
`H[κ] = sup_{‖φ‖=1} |∬ κφ| = ‖κ‖_∞`, then `f₀` is extremal for its boundary values. -/
theorem thm35_4 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h)
    (hH : hamiltonH (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀)) :
    IsExtremalForBoundary f₀ h := by
  exact thm35_3 hf₀ ((lemma35_6 (m35_essSup_lt_one hf₀.1)).2 hH)

/-! ### Helpers for `thm35_5` (s35h frame): Hamilton's theorem for the disc

Copies of S36 §36.3 (S36 imports S35), statements and bodies unchanged up to the prefix `h35_pd_`: the
Poincaré distance `h35_pd_discPoincareDist` of two points of `Δ` and its pointwise estimates.  Then the
duality lemma `h35_duality` (`h35a_`), Teichmüller's lemma `h35_trivial` (`h35b_`, with the S36 part-Q
copies `h35_pd_q_`) and scout H's assembly `h35_thm35_5_of_AB`. -/

/-- §36.3: the Poincaré distance `d(z, w) = ½ ln((1 + r)/(1 - r))`, `r = |(z - w)/(1 - z̄w)|`, of two
points of the unit disc (the values of Beltrami coefficients). -/
def h35_pd_discPoincareDist (z w : ℂ) : ℝ :=
  (1 / 2) * Real.log ((1 + ‖(z - w) / (1 - conj z * w)‖) / (1 - ‖(z - w) / (1 - conj z * w)‖))

/-- `|(a - b)/(1 - ā b)| = |(a - b)/(1 - b̄ a)|`: the two denominators are complex conjugate. -/
theorem h35_pd_b_norm_conj_denom (a b : ℂ) :
    ‖(a - b) / (1 - conj a * b)‖ = ‖(a - b) / (1 - conj b * a)‖ := by
  rw [norm_div, norm_div, ← Complex.norm_conj (1 - conj a * b)]
  congr 2
  rw [map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]

/-- §36.3: `d(z, 0) = artanh |z|`, since `(z - 0)/(1 - z̄·0) = z`. -/
theorem h35_pd_discPoincareDist_zero {z : ℂ} (hz : ‖z‖ < 1) :
    h35_pd_discPoincareDist z 0 = Real.artanh ‖z‖ := by
  have hsimp : ((z - 0) / (1 - conj z * 0) : ℂ) = z := by simp
  rw [h35_pd_discPoincareDist, hsimp,
    Real.artanh_eq_half_log ⟨by linarith [norm_nonneg z], hz.le⟩]

/-- The algebraic step behind `discPoincareDist_sub_le`: writing `A = |1 - z̄w|`, `B = |z - w|`
and `r = |z|`, one has `A - 1 ≤ r (B - r)`.

Both sides of `A ≤ 1 - r² + rB` are non-negative, and squaring reduces the claim to
`2(1 - r²)(Re(z̄w) - r² + rB) ≥ 0`, i.e. to `Re(z̄(z - w)) ≤ |z̄(z - w)|` — which is just
`Complex.re_le_norm`. -/
theorem h35_pd_norm_one_sub_conj_mul_sub_one_le {z w : ℂ} (hz : ‖z‖ < 1) :
    ‖1 - conj z * w‖ - 1 ≤ ‖z‖ * (‖z - w‖ - ‖z‖) := by
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hr2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
  -- `Re(z̄(z-w)) ≤ |z̄(z-w)| = ‖z‖ ‖z-w‖`, i.e. `r² - Re(z̄w) ≤ r B`
  have hzz : (conj z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hkey : ‖z‖ ^ 2 - (conj z * w).re ≤ ‖z‖ * ‖z - w‖ := by
    have h1 : (conj z * (z - w)).re ≤ ‖conj z * (z - w)‖ := Complex.re_le_norm _
    rw [norm_mul, RCLike.norm_conj, mul_sub, Complex.sub_re, hzz] at h1
    exact h1
  -- expand the two squared norms
  have hA2 : ‖1 - conj z * w‖ ^ 2 = 1 - 2 * (conj z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, one_mul,
      Complex.conj_re]
    ring
  have hB2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (conj z * w).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.conj_re (conj z * w), map_mul, Complex.conj_conj]
  -- square and compare
  have hCnn : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖ := by positivity
  have hsq : ‖1 - conj z * w‖ ^ 2 ≤ (1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖) ^ 2 := by
    nlinarith [hA2, hB2, hkey, hr2, norm_nonneg (z - w), mul_nonneg hr0 (norm_nonneg (z - w))]
  have hle : ‖1 - conj z * w‖ ≤ 1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hCnn] at h
  nlinarith [hle]

/-- `|1 - z̄w|² - |z - w|² = (1 - |z|²)(1 - |w|²)`: the identity behind the invariance of the
pseudo-hyperbolic distance. -/
theorem h35_pd_normSq_one_sub_conj_mul_sub_normSq_sub (z w : ℂ) :
    ‖1 - conj z * w‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  have hA2 : ‖1 - conj z * w‖ ^ 2 = 1 - 2 * (conj z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, one_mul,
      Complex.conj_re]
    ring
  have hB2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (conj z * w).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.conj_re (conj z * w), map_mul, Complex.conj_conj]
  rw [hA2, hB2]
  ring

/-- §36.3: the pointwise inequality with the explicit constant.  The sharp bound is
`-½log(1 - |w|²)`; `|w|²/(1 - |w|²)` is a convenient majorant, since `-log(1-u) ≤ u/(1-u)`.

Stated separately from `discPoincareDist_sub_le` because the `∃ α` there yields an *opaque* `α`,
and the `L∞` version (`lemma36_3`) needs `t ↦ α(t) t` to be **monotone** in order to bound it by its
value at `‖π‖_∞`; the explicit `t²/(1 - t²)` is. -/
theorem h35_pd_discPoincareDist_sub_le_explicit {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    h35_pd_discPoincareDist z w - h35_pd_discPoincareDist z 0
      ≤ ‖z - w‖ - ‖z‖ + ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hq0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hB0 : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
  have hr2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
  have hq2 : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith
  have hr1 : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hAB := h35_pd_normSq_one_sub_conj_mul_sub_normSq_sub z w
  have hA2pos : (0 : ℝ) < ‖1 - conj z * w‖ ^ 2 := by
    nlinarith [mul_pos hr2 hq2, sq_nonneg ‖z - w‖]
  have hA0 : (0 : ℝ) < ‖1 - conj z * w‖ := by
    rcases (norm_nonneg (1 - conj z * w)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hA2pos; norm_num at hA2pos
  have hBA : ‖z - w‖ < ‖1 - conj z * w‖ := by
    have h1 : ‖z - w‖ ^ 2 < ‖1 - conj z * w‖ ^ 2 := by nlinarith [mul_pos hr2 hq2]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  -- `d(z, 0) = log(1 + |z|) - ½ log(1 - |z|²)`
  have hd0 : h35_pd_discPoincareDist z 0 = Real.log (1 + ‖z‖) - (1 / 2) * Real.log (1 - ‖z‖ ^ 2) := by
    have hsimp : ((z - 0) / (1 - conj z * 0) : ℂ) = z := by simp
    rw [h35_pd_discPoincareDist, hsimp]
    have e : (1 + ‖z‖) / (1 - ‖z‖) = (1 + ‖z‖) ^ 2 / (1 - ‖z‖ ^ 2) := by
      rw [div_eq_div_iff hr1.ne' hr2.ne']
      ring
    rw [e, Real.log_div (by positivity) hr2.ne', Real.log_pow]
    push_cast
    ring
  -- `d(z, w) = log(A + B) - ½ log(1 - |z|²) - ½ log(1 - |w|²)`
  have hdw : h35_pd_discPoincareDist z w
      = Real.log (‖1 - conj z * w‖ + ‖z - w‖) - (1 / 2) * Real.log (1 - ‖z‖ ^ 2)
        - (1 / 2) * Real.log (1 - ‖w‖ ^ 2) := by
    rw [h35_pd_discPoincareDist, norm_div]
    have hden1 : (0 : ℝ) < 1 - ‖z - w‖ / ‖1 - conj z * w‖ := by
      rw [sub_pos, div_lt_one hA0]
      exact hBA
    have hsub : ‖1 - conj z * w‖ - ‖z - w‖ ≠ 0 := (sub_pos.2 hBA).ne'
    have e1 : (1 + ‖z - w‖ / ‖1 - conj z * w‖) / (1 - ‖z - w‖ / ‖1 - conj z * w‖)
        = (‖1 - conj z * w‖ + ‖z - w‖) / (‖1 - conj z * w‖ - ‖z - w‖) := by
      have hnum : 1 + ‖z - w‖ / ‖1 - conj z * w‖
          = (‖1 - conj z * w‖ + ‖z - w‖) / ‖1 - conj z * w‖ := by
        rw [add_div, div_self hA0.ne']
      have hden : 1 - ‖z - w‖ / ‖1 - conj z * w‖
          = (‖1 - conj z * w‖ - ‖z - w‖) / ‖1 - conj z * w‖ := by
        rw [sub_div, div_self hA0.ne']
      rw [hnum, hden, div_div_div_cancel_right₀ hA0.ne']
    have e2 : (‖1 - conj z * w‖ + ‖z - w‖) / (‖1 - conj z * w‖ - ‖z - w‖)
        = (‖1 - conj z * w‖ + ‖z - w‖) ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
      rw [div_eq_div_iff hsub (mul_pos hr2 hq2).ne', ← hAB]
      ring
    rw [e1, e2, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul hr2.ne' hq2.ne']
    push_cast
    ring
  -- `log((A + B)/(1 + |z|)) ≤ B - |z|`
  have hlog : Real.log (‖1 - conj z * w‖ + ‖z - w‖) - Real.log (1 + ‖z‖)
      ≤ ‖z - w‖ - ‖z‖ := by
    have h1 : Real.log ((‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖))
        ≤ (‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : (‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖) - 1 ≤ ‖z - w‖ - ‖z‖ := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [h35_pd_norm_one_sub_conj_mul_sub_one_le (w := w) hz]
    linarith
  -- `-½ log(1 - |w|²) ≤ |w|²/(1 - |w|²)`
  have hlogq : -((1 / 2) * Real.log (1 - ‖w‖ ^ 2)) ≤ ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
    have h1 : Real.log (1 / (1 - ‖w‖ ^ 2)) ≤ 1 / (1 - ‖w‖ ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero hq2.ne', Real.log_one, zero_sub] at h1
    have h2 : 1 / (1 - ‖w‖ ^ 2) - 1 = ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (0 : ℝ) ≤ ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by positivity
    linarith
  rw [hdw, hd0]
  linarith

/-- The analytic input behind `h35_pd_artanh_sub_self_monotoneOn`: `x ↦ log(1 + x) - log(1 - x) - 2x` is
monotone on `(-1, 1)`, its derivative being `1/(1 + x) + 1/(1 - x) - 2 = 2x²/(1 - x²) ≥ 0`.

Mathlib develops `Real.artanh` purely order-theoretically and gives it no derivative, so the
logarithmic form is the one differentiated here; `Real.artanh_eq_half_log` transports the result. -/
theorem h35_pd_monotoneOn_log_sub_log_sub_two_mul :
    MonotoneOn (fun x : ℝ => Real.log (1 + x) - Real.log (1 - x) - 2 * x)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hderiv : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
        (1 / (1 + x) - -1 / (1 - x) - 2) x := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    have d1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).log h1.ne'
    have d2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).log h2.ne'
    have d3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    exact (d1.sub d2).sub d3
  refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
    (fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt) ?_ ?_
  · rw [isOpen_Ioo.interior_eq]
    exact fun x hx => ((hderiv x hx).differentiableAt).differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    rw [(hderiv x hx).deriv]
    have key : 1 / (1 + x) - -1 / (1 - x) - 2 = 2 * x ^ 2 / ((1 + x) * (1 - x)) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by positivity) (mul_pos h1 h2).le

/-- `x ↦ artanh x - x` is monotone on `(-1, 1)`: in the language of §36.3, `|z| ↦ d(z, 0) - |z|`
is increasing.  This is the second ingredient of Lemma 36.3, the first being
`h35_pd_discPoincareDist_sub_le_explicit`. -/
theorem h35_pd_artanh_sub_self_monotoneOn :
    MonotoneOn (fun x : ℝ => Real.artanh x - x) (Set.Ioo (-1 : ℝ) 1) := by
  have key : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Real.artanh x - x = 1 / 2 * (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, Real.log_div h1.ne' h2.ne']
    ring
  intro s hs t ht hst
  have h : Real.log (1 + s) - Real.log (1 - s) - 2 * s
      ≤ Real.log (1 + t) - Real.log (1 - t) - 2 * t :=
    h35_pd_monotoneOn_log_sub_log_sub_two_mul hs ht hst
  show Real.artanh s - s ≤ Real.artanh t - t
  rw [key s hs, key t ht]
  linarith

/-- `t ↦ t²/(1 - t²)` is monotone on `[0, 1)` — the `α(t) t` of `discPoincareDist_sub_le`. -/
theorem h35_pd_sq_div_one_sub_sq_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    s ^ 2 / (1 - s ^ 2) ≤ t ^ 2 / (1 - t ^ 2) := by
  have ht0 : (0 : ℝ) ≤ t := le_trans hs hst
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hds : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hdt : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hds hdt]
  nlinarith [mul_nonneg (sub_nonneg.2 hst) (by linarith : (0 : ℝ) ≤ t + s)]

/-! ### s35h Stage 1, track HA: the duality lemma (`h35_duality`, Hahn–Banach and `L¹(Δ)* = L∞(Δ)`) -/

/-- On a finite measure space, the inclusion `L² ⊆ L¹` as a continuous `ℂ`-linear map. -/
theorem h35a_exists_L2_to_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    ∃ ι : Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ, ∀ f : Lp ℂ 2 μ, (ι f : α → ℂ) =ᵐ[μ] f := by
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  let ιₗ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 1 μ :=
    { toFun := fun f => ((Lp.memLp f).mono_exponent h12).toLp f
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_exponent h12), Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).mono_exponent h12).toLp f)
            (((Lp.memLp g).mono_exponent h12).toLp g),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h12),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent h12)] with x h1 h2 h3 h4 h5
        rw [h1, h2, h3, Pi.add_apply, Pi.add_apply, h4, h5]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent h12), Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).mono_exponent h12).toLp f),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h12)] with x h1 h2 h3 h4
        rw [h1, h2, RingHom.id_apply, h3, Pi.smul_apply, Pi.smul_apply, h4] }
  have hC : ∀ f : Lp ℂ 2 μ,
      ‖ιₗ f‖ ≤ (μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal * ‖f‖ := by
    intro f
    change ‖((Lp.memLp f).mono_exponent h12).toLp f‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def, mul_comm, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top ?_)
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h12 (Lp.aestronglyMeasurable f))
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  refine ⟨LinearMap.mkContinuous ιₗ _ hC, fun f => ?_⟩
  exact MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h12)

/-- Riesz step: a bounded functional on `L¹` of a finite measure, tested on `L²` functions, is
integration against a strongly measurable `L²` function. -/
theorem h35a_riesz_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (L : StrongDual ℂ (Lp ℂ 1 μ)) :
    ∃ g : α → ℂ, StronglyMeasurable g ∧ MemLp g 2 μ ∧
      ∀ f : α → ℂ, MemLp f 2 μ → ∀ hf : Integrable f μ,
        L (hf.toL1 f) = ∫ x, conj (g x) * f x ∂μ := by
  obtain ⟨ι, hι⟩ := h35a_exists_L2_to_L1 (μ := μ)
  set G := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm (L.comp ι) with hG
  refine ⟨G, Lp.stronglyMeasurable G, Lp.memLp G, fun f hf2 hf => ?_⟩
  have h1 : hf.toL1 f = ι (hf2.toLp f) := by
    refine Lp.ext ?_
    filter_upwards [hf.coeFn_toL1, hι (hf2.toLp f), hf2.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3]
  have h2 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := hf2.toLp f) (y := L.comp ι)
  rw [h1, ← ContinuousLinearMap.comp_apply, ← h2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp] with x hx
  rw [RCLike.inner_apply, hx, mul_comm]

/-- The Riesz representative of a bounded functional `L` on `L¹` (tested on `L²`) is bounded by
`‖L‖` almost everywhere: test `L` on `1_E g/|g|` with `E = {|g| > ‖L‖ + ε}`. -/
theorem h35a_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (L : StrongDual ℂ (Lp ℂ 1 μ)) {g : α → ℂ} (hgm : StronglyMeasurable g) (hg2 : MemLp g 2 μ)
    (hrep : ∀ f : α → ℂ, MemLp f 2 μ → ∀ hf : Integrable f μ,
      L (hf.toL1 f) = ∫ x, conj (g x) * f x ∂μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖L‖ := by
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hε : ∀ ε : ℝ, 0 < ε → ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖L‖ + ε := by
    intro ε hε
    set E := {x | ‖L‖ + ε < ‖g x‖} with hE
    have hEm : MeasurableSet E := measurableSet_lt measurable_const hgm.measurable.norm
    set u : α → ℂ := E.indicator (fun x => g x / (‖g x‖ : ℂ)) with hu
    have hu1 : ∀ x, ‖u x‖ ≤ E.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ E
      · rw [hu, indicator_of_mem hx, indicator_of_mem hx, norm_div, Complex.norm_real, norm_norm]
        exact div_self_le_one _
      · rw [hu, indicator_of_notMem hx, indicator_of_notMem hx, norm_zero]
    have hu1' : ∀ x, ‖u x‖ ≤ 1 := fun x =>
      (hu1 x).trans (indicator_le_self' (fun _ _ => zero_le_one) x)
    have hum : AEStronglyMeasurable u μ :=
      ((hgm.measurable.div (Complex.measurable_ofReal.comp hgm.measurable.norm)).indicator
        hEm).aestronglyMeasurable
    have hu2 : MemLp u 2 μ := MemLp.of_bound hum 1 (ae_of_all _ hu1')
    have hui : Integrable u μ := hu2.integrable h12
    have hgi : IntegrableOn (fun x => ‖g x‖) E μ := (hg2.integrable h12).norm.integrableOn
    have hval : L (hui.toL1 u) = ((∫ x in E, ‖g x‖ ∂μ : ℝ) : ℂ) := by
      rw [hrep u hu2 hui, ← integral_complex_ofReal, ← integral_indicator hEm]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ E
      · have hg0 : (‖g x‖ : ℂ) ≠ 0 := by
          have : 0 < ‖g x‖ := lt_of_le_of_lt (by positivity) hx
          exact_mod_cast this.ne'
        simp only [hu, indicator_of_mem hx]
        rw [← mul_div_assoc, Complex.conj_mul', pow_two, mul_div_assoc, div_self hg0, mul_one]
      · simp only [hu, indicator_of_notMem hx, mul_zero]
    have hlow : μ.real E • (‖L‖ + ε) ≤ ∫ x in E, ‖g x‖ ∂μ :=
      setIntegral_ge_of_const_le hEm (measure_ne_top μ E) (fun x hx => hx.le) hgi
    have hup : ‖L (hui.toL1 u)‖ ≤ ‖L‖ * μ.real E := by
      refine (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [L1.norm_of_fun_eq_integral_norm, ← integral_indicator_one hEm]
      exact integral_mono (hui.norm) ((integrable_const 1).indicator hEm) hu1
    have hnn : 0 ≤ ∫ x in E, ‖g x‖ ∂μ := setIntegral_nonneg hEm (fun x _ => norm_nonneg _)
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hnn] at hup
    rw [smul_eq_mul] at hlow
    have hm0 : μ.real E = 0 := by
      have hm : 0 ≤ μ.real E := measureReal_nonneg
      nlinarith
    have hμE : μ E = 0 := (measureReal_eq_zero_iff (measure_ne_top μ E)).1 hm0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμE] with x hx
    exact not_lt.1 hx
  have hall := ae_all_iff.2 (fun n : ℕ => hε (1 / ((n : ℝ) + 1)) (by positivity))
  filter_upwards [hall] with x hx
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hx n]

/-- `L¹(μ)* = L∞(μ)` for a finite measure (the representation half): every bounded functional `L`
on `L¹(μ)` is integration against a function `ν` with `|ν| ≤ ‖L‖` a.e. -/
theorem h35a_L1_dual_repr {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (L : StrongDual ℂ (Lp ℂ 1 μ)) :
    ∃ ν : α → ℂ, AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ ≤ ‖L‖) ∧
      ∀ f : α → ℂ, ∀ hf : Integrable f μ, L (hf.toL1 f) = ∫ x, ν x * f x ∂μ := by
  obtain ⟨g, hgm, hg2, hrep⟩ := h35a_riesz_L2 L
  have hb := h35a_bound L hgm hg2 hrep
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  set ν : α → ℂ := fun x => conj (g x) with hν
  have hνm : AEStronglyMeasurable ν μ :=
    (Complex.continuous_conj.comp_stronglyMeasurable hgm).aestronglyMeasurable
  have hνb : ∀ᵐ x ∂μ, ‖ν x‖ ≤ ‖L‖ := by
    filter_upwards [hb] with x hx
    rwa [hν, Complex.norm_conj]
  refine ⟨ν, hνm, hνb, fun f hf => ?_⟩
  set T : ℕ → α → ℂ := fun n => {x | ‖f x‖ ≤ (n : ℝ)}.indicator f with hT
  have hTm : ∀ n : ℕ, NullMeasurableSet {x | ‖f x‖ ≤ (n : ℝ)} μ := fun n =>
    hf.1.norm.nullMeasurableSet_le aestronglyMeasurable_const
  have hTb : ∀ (n : ℕ) x, ‖T n x‖ ≤ n := by
    intro n x
    by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)}
    · simp only [hT, indicator_of_mem hx]
      exact hx
    · simp only [hT, indicator_of_notMem hx, norm_zero]
      exact Nat.cast_nonneg n
  have hT2 : ∀ n : ℕ, MemLp (T n) 2 μ := fun n =>
    MemLp.of_bound (hf.1.indicator₀ (hTm n)) n (ae_of_all _ (hTb n))
  have hTi : ∀ n : ℕ, Integrable (T n) μ := fun n => (hT2 n).integrable h12
  have hdb : ∀ (n : ℕ) x, ‖f x - T n x‖ ≤ ‖f x‖ := by
    intro n x
    by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)}
    · simp only [hT, indicator_of_mem hx, sub_self, norm_zero]
      exact norm_nonneg _
    · simp only [hT, indicator_of_notMem hx, sub_zero, le_refl]
  have hlim : Tendsto (fun n : ℕ => ∫ x, ‖f x - T n x‖ ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => ‖f x‖)
      (F := fun (n : ℕ) x => ‖f x - T n x‖) (f := fun _ => (0 : ℝ))
      (fun n => (hf.sub (hTi n)).norm.1) hf.norm
      (fun n => ae_of_all _ fun x => by rw [norm_norm]; exact hdb n x)
      (ae_of_all _ fun x => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_ge ‖f x‖
        filter_upwards [eventually_ge_atTop N] with n hn
        have hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} := hN.trans (by exact_mod_cast hn)
        rw [hT]
        simp only [indicator_of_mem hx, sub_self, norm_zero])
    simpa using h
  have hνf : Integrable (fun x => ν x * f x) μ := hf.bdd_mul hνm hνb
  have hle : ∀ n : ℕ, ‖L (hf.toL1 f) - ∫ x, ν x * f x ∂μ‖ ≤
      2 * ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ := by
    intro n
    have hD : Integrable (f - T n) μ := hf.sub (hTi n)
    have e1 : L (hf.toL1 f) = L (hD.toL1 (f - T n)) + ∫ x, ν x * T n x ∂μ := by
      rw [Integrable.toL1_sub f (T n) hf (hTi n), map_sub, hrep (T n) (hT2 n) (hTi n)]
      ring
    have hνT : Integrable (fun x => ν x * T n x) μ := (hTi n).bdd_mul hνm hνb
    have hνD : Integrable (fun x => ν x * (f x - T n x)) μ := hD.bdd_mul hνm hνb
    have e2 : ∫ x, ν x * f x ∂μ = ∫ x, ν x * (f x - T n x) ∂μ + ∫ x, ν x * T n x ∂μ := by
      rw [← integral_add hνD hνT]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
    have b1 : ‖L (hD.toL1 (f - T n))‖ ≤ ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ := by
      refine (L.le_opNorm _).trans (le_of_eq ?_)
      rw [L1.norm_of_fun_eq_integral_norm]
      rfl
    have b2 : ‖∫ x, ν x * (f x - T n x) ∂μ‖ ≤ ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le ((hD.norm).const_mul _) ?_
      filter_upwards [hνb] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    rw [e1, e2, add_sub_add_right_eq_sub]
    calc ‖L (hD.toL1 (f - T n)) - ∫ x, ν x * (f x - T n x) ∂μ‖
        ≤ ‖L (hD.toL1 (f - T n))‖ + ‖∫ x, ν x * (f x - T n x) ∂μ‖ := norm_sub_le _ _
      _ ≤ ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ + ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ := add_le_add b1 b2
      _ = 2 * ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ := by ring
  have hlim2 : Tendsto (fun n : ℕ => 2 * ‖L‖ * ∫ x, ‖f x - T n x‖ ∂μ) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 * ‖L‖)
  have h0 : ‖L (hf.toL1 f) - ∫ x, ν x * f x ∂μ‖ ≤ 0 := ge_of_tendsto' hlim2 hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- Integration against an essentially bounded `κ` as a bounded functional on `L¹(μ)`. -/
theorem h35a_exists_mul_functional {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : α → ℂ}
    {C : ℝ} (hκm : AEStronglyMeasurable κ μ) (hκ : ∀ᵐ x ∂μ, ‖κ x‖ ≤ C) :
    ∃ ℓ : StrongDual ℂ (Lp ℂ 1 μ), ∀ F : Lp ℂ 1 μ, ℓ F = ∫ x, κ x * F x ∂μ := by
  have hint : ∀ F : Lp ℂ 1 μ, Integrable (fun x => κ x * F x) μ := fun F =>
    (L1.integrable_coeFn F).bdd_mul hκm hκ
  let ℓₗ : Lp ℂ 1 μ →ₗ[ℂ] ℂ :=
    { toFun := fun F => ∫ x, κ x * F x ∂μ
      map_add' := fun F G => by
        rw [← integral_add (hint F) (hint G)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        rw [hx, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨LinearMap.mkContinuous ℓₗ C (fun F => ?_), fun F => rfl⟩
  change ‖∫ x, κ x * F x ∂μ‖ ≤ C * ‖F‖
  rw [L1.norm_eq_integral_norm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn F).norm.const_mul C) ?_
  filter_upwards [hκ] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- An element of `A(Δ)` is integrable on `Δ`. -/
theorem h35a_integrableOn_of_mem {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD) : IntegrableOn φ unitDisc :=
  ⟨hφ.1.continuousOn.aestronglyMeasurable measurableSet_ball, (hasFiniteIntegral_iff_norm φ).2 hφ.2⟩

/-- A holomorphic function integrable on `Δ` belongs to `A(Δ)`. -/
theorem h35a_mem_of_integrableOn {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ unitDisc)
    (hi : IntegrableOn φ unitDisc) : φ ∈ integrableQD :=
  ⟨hd, (hasFiniteIntegral_iff_norm φ).1 hi.2⟩

/-- `A(Δ)` as a subspace of `L¹(Δ)`: the classes of the elements of `integrableQD`. -/
def h35a_qdSub : Submodule ℂ (Lp ℂ 1 (volume.restrict unitDisc)) where
  carrier := {F | ∃ φ ∈ integrableQD, (F : ℂ → ℂ) =ᵐ[volume.restrict unitDisc] φ}
  add_mem' := by
    rintro F G ⟨φ, hφ, hF⟩ ⟨ψ, hψ, hG⟩
    refine ⟨φ + ψ, h35a_mem_of_integrableOn (hφ.1.add hψ.1)
      ((h35a_integrableOn_of_mem hφ).add (h35a_integrableOn_of_mem hψ)), ?_⟩
    filter_upwards [Lp.coeFn_add F G, hF, hG] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]
  zero_mem' := ⟨0, h35a_mem_of_integrableOn (differentiableOn_const 0) integrableOn_zero,
    Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c F ⟨φ, hφ, hF⟩
    refine ⟨c • φ, h35a_mem_of_integrableOn (hφ.1.const_smul c)
      ((h35a_integrableOn_of_mem hφ).smul c), ?_⟩
    filter_upwards [Lp.coeFn_smul c F, hF] with z h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply]

/-- `|∬_Δ κφ| ≤ H[κ] ∬_Δ |φ|` for every `φ ∈ A(Δ)` (rescale `φ` to norm `1`). -/
theorem h35a_norm_integral_le {κ φ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) (hφ : φ ∈ integrableQD) :
    ‖∫ z in unitDisc, κ z * φ z‖ ≤ hamiltonH κ * ∫ z in unitDisc, ‖φ z‖ := by
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hφi := h35a_integrableOn_of_mem hφ
  have hbH : ∀ ψ : ℂ → ℂ, ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1 →
      ‖∫ z in unitDisc, κ z * ψ z‖ ≤ beltramiNormDisc κ :=
    fun ψ hψ => norm_integral_mul_le_of_admissible hκ hψ
  set a := ∫ z in unitDisc, ‖φ z‖ with ha
  have ha0 : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  rcases ha0.lt_or_eq with hapos | ha0'
  · have hareaφ : phiArea φ unitDisc = ENNReal.ofReal a := by
      rw [ha, ofReal_integral_eq_lintegral_ofReal hφi.norm (ae_of_all _ fun _ => norm_nonneg _)]
      rfl
    set ψ : ℂ → ℂ := fun z => (a : ℂ)⁻¹ * φ z with hψdef
    have hnψ : ∀ z, ENNReal.ofReal ‖ψ z‖ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal ‖φ z‖ := by
      intro z
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 ha0), hψdef, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg ha0]
    have hareaψ : phiArea ψ unitDisc = 1 := by
      simp only [phiArea, hnψ]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      change ENNReal.ofReal a⁻¹ * phiArea φ unitDisc = 1
      rw [hareaφ, ← ENNReal.ofReal_mul (inv_nonneg.2 ha0), inv_mul_cancel₀ hapos.ne',
        ENNReal.ofReal_one]
    have hψ : ψ ∈ integrableQD ∧ phiArea ψ unitDisc = 1 :=
      ⟨⟨hφ.1.const_mul _, by rw [hareaψ]; exact ENNReal.one_lt_top⟩, hareaψ⟩
    have h1 : ‖∫ z in unitDisc, κ z * ψ z‖ ≤ hamiltonH κ :=
      le_hamiltonSup (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) hk0 hbH hψ
    have e : ∫ z in unitDisc, κ z * ψ z = (a : ℂ)⁻¹ * ∫ z in unitDisc, κ z * φ z := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hψdef]
      ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 ha0
    rw [← mul_assoc, mul_inv_cancel₀ hapos.ne', one_mul] at h2
    linarith
  · have hle : ‖∫ z in unitDisc, κ z * φ z‖ ≤ a := by
      refine norm_integral_le_of_norm_le hφi.norm ?_
      filter_upwards [hae] with z hz
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hz.trans hk1.le)
    rw [← ha0'] at hle ⊢
    rw [mul_zero]
    exact hle

/-- **(A) Duality.**  For a measurable `κ` with `‖κ‖_∞ < 1` on `Δ` there is a bounded `ν`
with `|ν| ≤ H[κ]` a.e. and `κ - ν ⊥ A(Δ)`.  (Hahn–Banach + `L¹(Δ)* = L∞(Δ)`.) -/
theorem h35_duality {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc))
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) :
    ∃ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict unitDisc) ∧
      (∀ᵐ z ∂(volume.restrict unitDisc), ‖ν z‖ ≤ hamiltonH κ) ∧
      ∀ φ ∈ integrableQD, ∫ z in unitDisc, (κ z - ν z) * φ z = 0 := by
  obtain ⟨-, -, hae⟩ := beltramiNormDisc_facts hκ
  have hfin : IsFiniteMeasure (volume.restrict unitDisc) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨ℓ, hℓ⟩ := h35a_exists_mul_functional hκm hae
  have hH0 : 0 ≤ hamiltonH κ := hamiltonSup_nonneg (fun _ => norm_nonneg _)
  have hbd : ‖ℓ.comp h35a_qdSub.subtypeL‖ ≤ hamiltonH κ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hH0 (fun F => ?_)
    obtain ⟨φ, hφ, hFφ⟩ := F.2
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hℓ, ← Submodule.norm_coe,
      L1.norm_eq_integral_norm]
    have e1 : ∫ z in unitDisc, κ z * (F : Lp ℂ 1 (volume.restrict unitDisc)) z =
        ∫ z in unitDisc, κ z * φ z := by
      refine integral_congr_ae ?_
      filter_upwards [hFφ] with z hz
      rw [hz]
    have e2 : ∫ z in unitDisc, ‖(F : Lp ℂ 1 (volume.restrict unitDisc)) z‖ =
        ∫ z in unitDisc, ‖φ z‖ := by
      refine integral_congr_ae ?_
      filter_upwards [hFφ] with z hz
      rw [hz]
    rw [e1, e2]
    exact h35a_norm_integral_le hκ hφ
  obtain ⟨L, hLext, hLnorm⟩ := exists_extension_norm_eq h35a_qdSub (ℓ.comp h35a_qdSub.subtypeL)
  obtain ⟨ν, hνm, hνb, hνrep⟩ := h35a_L1_dual_repr L
  refine ⟨ν, hνm, ?_, fun φ hφ => ?_⟩
  · filter_upwards [hνb] with z hz
    exact hz.trans (hLnorm ▸ hbd)
  · have hφi := h35a_integrableOn_of_mem hφ
    have hmem : hφi.toL1 φ ∈ h35a_qdSub := ⟨φ, hφ, hφi.coeFn_toL1⟩
    have h1 := hLext ⟨hφi.toL1 φ, hmem⟩
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hℓ, hνrep φ hφi] at h1
    have e1 : ∫ z in unitDisc, κ z * (hφi.toL1 φ : ℂ → ℂ) z = ∫ z in unitDisc, κ z * φ z := by
      refine integral_congr_ae ?_
      filter_upwards [hφi.coeFn_toL1] with z hz
      rw [hz]
    have hκφ : IntegrableOn (fun z => κ z * φ z) unitDisc := hφi.bdd_mul hκm hae
    have hνφ : IntegrableOn (fun z => ν z * φ z) unitDisc := hφi.bdd_mul hνm hνb
    have e2 : (fun z => (κ z - ν z) * φ z) = fun z => κ z * φ z - ν z * φ z :=
      funext fun z => sub_mul _ _ _
    rw [e2, integral_sub hκφ hνφ, ← e1, ← h1, sub_self]

/-! ### s35h Stage 1, track HB: Teichmüller's lemma (`h35_trivial`)

Copies of S36 part Q (`b36_q_*`, S36 l.1418-1480 and l.1508-1682, statements and bodies unchanged up to the
prefix `h35_pd_q_`): the family `t ↦ tκ` in `M` and the first variation `∂_t φ_{tκ}(z)|₀ = V[κ]‴(z)`. -/

open scoped Classical in
/-- The affine family `t ↦ μ + t ν` in `M`, defaulting to `μ` where `μ + t ν` is not admissible. -/
def h35_pd_q_fam (μ ν : BeltramiH) (t : ℂ) : BeltramiH :=
  if h : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → μ.1 z + t * ν.1 z = 0 then ⟨fun w => μ.1 w + t * ν.1 w, h⟩ else μ

/-- A radius `r > 0` and a bound `k < 1` with `‖μ + t ν‖_∞ ≤ k` for `|t| < r`
(`|μ + t ν| ≤ k_μ + |t| k_ν`, `r = (1 - k_μ)/(2(k_ν + 1))`). -/
theorem h35_pd_q_small (μ ν : BeltramiH) :
    ∃ r > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k := by
  obtain ⟨⟨k₁, hk₁0, hk₁1, hm₁, hb₁⟩, -⟩ := μ.2
  obtain ⟨⟨k₂, hk₂0, hk₂1, hm₂, hb₂⟩, -⟩ := ν.2
  have hr : 0 < (1 - k₁) / (2 * (k₂ + 1)) := div_pos (by linarith) (by positivity)
  have hrk : (1 - k₁) / (2 * (k₂ + 1)) * k₂ ≤ (1 - k₁) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨(1 - k₁) / (2 * (k₂ + 1)), hr, k₁ + (1 - k₁) / (2 * (k₂ + 1)) * k₂,
    add_nonneg hk₁0 (mul_nonneg hr.le hk₂0), by linarith, fun t ht => ⟨hm₁.add (hm₂.const_mul t), ?_⟩⟩
  filter_upwards [hb₁, hb₂] with w h1 h2
  have htn : ‖t‖ ≤ (1 - k₁) / (2 * (k₂ + 1)) := (mem_ball_zero_iff.mp ht).le
  calc ‖μ.1 w + t * ν.1 w‖ ≤ ‖μ.1 w‖ + ‖t‖ * ‖ν.1 w‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ k₁ + (1 - k₁) / (2 * (k₂ + 1)) * k₂ :=
        add_le_add h1 (mul_le_mul htn h2 (norm_nonneg _) hr.le)

/-- On the ball of `h35_pd_q_small`, `h35_pd_q_fam μ ν t` is `μ + t ν`. -/
theorem h35_pd_q_fam_val (μ ν : BeltramiH) {r k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) r) : (h35_pd_q_fam μ ν t).1 = fun w => μ.1 w + t * ν.1 w := by
  have hc : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → μ.1 z + t * ν.1 z = 0 :=
    ⟨⟨k, hk0, hk1, hb t ht⟩, fun z hz => by rw [μ.2.2 z hz, ν.2.2 z hz, mul_zero, add_zero]⟩
  unfold h35_pd_q_fam
  exact congrArg Subtype.val (dite_eq_left hc)

/-- `bB_schwarzian_holo` over an arbitrary open parameter set `P` with a uniform bound `k < 1`:
`t ↦ S_{f_{ν t}}(z)` is holomorphic on `P` for each `z ∈ 𝕃`. -/
theorem h35_pd_q_schwarzian_holo {ν : ℂ → BeltramiH} {P : Set ℂ} (hP : IsOpen P) {k : ℝ} (hk₀ : 0 ≤ k)
    (hk1 : k < 1) (hkP : ∀ t ∈ P, IsBeltramiCoeff (ν t).1 univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => (ν t).1 z) P) {z : ℂ} (hz : z ∈ lowerHalf) :
    DifferentiableOn ℂ (fun t => schwarzian (normalizedSolution (ν t).1) z) P := by
  have hconf := fun t => ut_conformal_lowerHalf (ν t)
  have ha : ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun t => normalizedSolution (ν t).1 w) P :=
    fun w _ => thm13_8_ahlfors_bers_holomorphic (μ := fun t => (ν t).1)
      (f := fun t => normalizedSolution (ν t).1) hP hk₀ hk1 hkP hhol (fun t _ => ut_spec (ν t)) w
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := fun t => normalizedSolution (ν t).1)
    isOpen_lowerHalf ha (fun t _ => (hconf t).1) (bB_hs_bound hP hk₀ hk1 hkP) z hz
  have hne : ∀ t, deriv (normalizedSolution (ν t).1) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  refine ((((hd3.mul hd1).sub (hd2.mul hd2)).div (hd1.pow 2) fun t _ => pow_ne_zero 2 (hne t)).sub
    (((hd2.div hd1 fun t _ => hne t).pow 2).const_mul (1 / 2))).congr fun t _ => ?_
  exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)

/-- The hypotheses of `thm13_8`/`bB_hs_bound` for the family `h35_pd_q_fam μ ν` on the ball of `h35_pd_q_small`. -/
theorem h35_pd_q_fam_hyps (μ ν : BeltramiH) {r k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) :
    (∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (h35_pd_q_fam μ ν t).1 univ k) ∧
      ∀ w, DifferentiableOn ℂ (fun t => (h35_pd_q_fam μ ν t).1 w) (ball 0 r) := by
  refine ⟨fun t ht => by rw [h35_pd_q_fam_val μ ν hk0 hk1 hb ht]; exact hb t ht, fun w => ?_⟩
  exact (by fun_prop : DifferentiableOn ℂ (fun t : ℂ => μ.1 w + t * ν.1 w) (ball 0 r)).congr
    fun t ht => by rw [h35_pd_q_fam_val μ ν hk0 hk1 hb ht]

/-- The zero Beltrami coefficient as an element of `M`. -/
def h35_pd_q_zero : BeltramiH := ⟨0, bB_l_zero_mem⟩

/-- `f_{0 + 0·ν} = id`. -/
theorem h35_pd_q_F0 (ν : BeltramiH) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => h35_pd_q_zero.1 w + t * ν.1 w) univ k) :
    normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν 0).1 = id := by
  rw [h35_pd_q_fam_val h35_pd_q_zero ν hk0 hk1 hb (mem_ball_self hr)]
  have h : (fun w => h35_pd_q_zero.1 w + 0 * ν.1 w) = (0 : ℂ → ℂ) := by
    funext w
    simp [h35_pd_q_zero]
  rw [h]
  exact bB_l_normalizedSolution_zero

/-- First variation along `t ↦ t ν` at `t = 0`: `∂_t f_{tν}(w)|₀ = V[ν](w)` (`ahT_hasDerivAt` at `t₀ = 0`,
where `f₀ = id` and the coefficient derivative is `ν`). -/
theorem h35_pd_q_first_var (ν : BeltramiH) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => h35_pd_q_zero.1 w + t * ν.1 w) univ k) (w : ℂ) :
    HasDerivAt (fun t => normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν t).1 w) (ahVar ν.1 w) 0 := by
  obtain ⟨hkP, hhol⟩ := h35_pd_q_fam_hyps h35_pd_q_zero ν hk0 hk1 hb
  have h := ahT_hasDerivAt (μ := fun t => (h35_pd_q_fam h35_pd_q_zero ν t).1)
    (f := fun t => normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν t).1) isOpen_ball hk0 hk1 hkP hhol
    (fun t _ => ut_spec _) (mem_ball_self hr) w
  have hF0 := h35_pd_q_F0 ν hr hk0 hk1 hb
  have hval0 := h35_pd_q_fam_val h35_pd_q_zero ν hk0 hk1 hb (mem_ball_self hr)
  have hdot : ahT_dot (fun ζ => deriv (fun s => (h35_pd_q_fam h35_pd_q_zero ν s).1 ζ) 0)
      (h35_pd_q_fam h35_pd_q_zero ν 0).1 (normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν 0).1) = ν.1 := by
    funext ζ
    have hinv : Function.invFunOn (id : ℂ → ℂ) univ ζ = ζ :=
      (injOn_id univ).leftInvOn_invFunOn (mem_univ ζ)
    have hdz : dz id ζ = 1 := by
      simp only [dz, fderiv_id, ContinuousLinearMap.id_apply]
      rw [I_mul_I]
      ring
    have hder : deriv (fun s => (h35_pd_q_fam h35_pd_q_zero ν s).1 ζ) 0 = ν.1 ζ := by
      have hev : (fun s => (h35_pd_q_fam h35_pd_q_zero ν s).1 ζ) =ᶠ[𝓝 0]
          fun s => h35_pd_q_zero.1 ζ + s * ν.1 ζ :=
        eventually_of_mem (ball_mem_nhds 0 hr) fun s hs => by
          beta_reduce
          rw [h35_pd_q_fam_val h35_pd_q_zero ν hk0 hk1 hb hs]
      rw [hev.deriv_eq]
      simp
    rw [hF0, hval0]
    simp only [ahT_dot, hinv, hdz, hder]
    simp [h35_pd_q_zero]
  rw [hdot, hF0] at h
  exact h

/-- `iteratedDeriv 3 id = 0`. -/
theorem h35_pd_q_iteratedDeriv3_id (z : ℂ) : iteratedDeriv 3 (fun w : ℂ => w) z = 0 := by
  simp [iteratedDeriv_succ, deriv_id'']

/-- The third derivative is linear on functions holomorphic near `z`:
`(f - id - h V)‴(z) = f‴(z) - h V‴(z)`. -/
theorem h35_pd_q_iteratedDeriv3_lin {f V : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) (hV : DifferentiableOn ℂ V U) (h : ℂ) :
    iteratedDeriv 3 (fun w => f w - w - h * V w) z = iteratedDeriv 3 f z - h * iteratedDeriv 3 V z := by
  have hn : U ∈ 𝓝 z := hU.mem_nhds hz
  have c1 : ContDiffAt ℂ 3 f z := (hf.contDiffOn hU).contDiffAt hn
  have c2 : ContDiffAt ℂ 3 (fun w : ℂ => w) z := contDiffAt_id
  have c3 : ContDiffAt ℂ 3 V z := (hV.contDiffOn hU).contDiffAt hn
  rw [iteratedDeriv_fun_sub (c1.sub c2) ((contDiffAt_const (c := h)).mul c3), iteratedDeriv_fun_sub c1 c2,
    iteratedDeriv_const_mul_field, h35_pd_q_iteratedDeriv3_id, sub_zero]

/-- The commutation `∂_t ∂_w³ f_{tν}(z)|₀ = V[ν]‴(z)`: the uniform second-order Taylor bound in `t`
(`bB_h0_taylor_le`, uniform on a ball in `w`) and Cauchy's estimate for the third `w`-derivative. -/
theorem h35_pd_q_d3 (ν : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k)
    (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => h35_pd_q_zero.1 w + t * ν.1 w) univ k) :
    HasDerivAt (fun t => iteratedDeriv 3 (normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν t).1) z)
      (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
  obtain ⟨hkP, hhol⟩ := h35_pd_q_fam_hyps h35_pd_q_zero ν hk0 hk1 hb
  set F : ℂ → ℂ → ℂ := fun t => normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν t).1 with hFdef
  have ha : ∀ w, DifferentiableOn ℂ (fun t => F t w) (ball 0 r) :=
    thm13_8_ahlfors_bers_holomorphic (μ := fun t => (h35_pd_q_fam h35_pd_q_zero ν t).1) (f := F) isOpen_ball
      hk0 hk1 hkP hhol (fun t _ => ut_spec _)
  have hbU : ∀ t, DifferentiableOn ℂ (F t) lowerHalf := fun t => (ut_conformal_lowerHalf _).1
  have hc := bB_hs_bound (ν := h35_pd_q_fam h35_pd_q_zero ν) isOpen_ball hk0 hk1 hkP
  have hF0 : F 0 = id := h35_pd_q_F0 ν hr hk0 hk1 hb
  have hV : ∀ w, HasDerivAt (fun t => F t w) (ahVar ν.1 w) 0 := h35_pd_q_first_var ν hr hk0 hk1 hb
  -- `V[ν]` is holomorphic on `𝕃` (`bB_h0_deriv_holo` with the roles of `t` and `w` swapped)
  have hVd : DifferentiableOn ℂ (ahVar ν.1) lowerHalf := by
    have h := bB_h0_deriv_holo (P := lowerHalf) (U := ball (0 : ℂ) r) (F := fun w t => F t w)
      (fun t _ => hbU t) (fun w _ => ha w)
      (fun w₀ hw₀ t₀ ht₀ => by
        obtain ⟨ε, hε, h1, h2, M, hM⟩ := hc t₀ ht₀ w₀ hw₀
        exact ⟨ε, hε, h2, h1, M, fun w hw t ht => hM t ht w hw⟩) 0 (mem_ball_self hr)
    exact h.congr fun w _ => (hV w).deriv.symm
  obtain ⟨ε, hε, hPε, hUε, M, hM⟩ := hc 0 (mem_ball_self hr) z hz
  -- uniform Taylor bound
  have htay : ∀ h : ℂ, ‖h‖ < ε / 2 → ∀ w ∈ ball z ε,
      ‖F h w - w - h * ahVar ν.1 w‖ ≤ 8 * M / ε ^ 2 * ‖h‖ ^ 2 := by
    intro h hh w hw
    have hg : DifferentiableOn ℂ (fun t => F t w) (ball 0 ε) := (ha w).mono hPε
    have := bB_h0_taylor_le hε hg (fun t ht => hM t ht w hw) hh
    rw [zero_add, (hV w).deriv, hF0] at this
    exact this
  -- Cauchy estimate for the third derivative
  set C : ℝ := (Nat.factorial 3 : ℝ) * (8 * M / ε ^ 2) / (ε / 2) ^ 3 with hCdef
  have hd3 : ∀ h : ℂ, ‖h‖ < ε / 2 →
      ‖iteratedDeriv 3 (F h) z - h * iteratedDeriv 3 (ahVar ν.1) z‖ ≤ C * ‖h‖ ^ 2 := by
    intro h hh
    have hE : DifferentiableOn ℂ (fun w => F h w - w - h * ahVar ν.1 w) lowerHalf :=
      ((hbU h).sub differentiableOn_id).sub (hVd.const_mul h)
    have hsub : closedBall z (ε / 2) ⊆ lowerHalf :=
      (closedBall_subset_ball (by linarith)).trans hUε
    have hbd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 (by linarith : 0 < ε / 2)
      (hE.diffContOnCl_ball hsub) (fun w hw => htay h hh w
        (closedBall_subset_ball (by linarith) (sphere_subset_closedBall hw)))
    rw [h35_pd_q_iteratedDeriv3_lin isOpen_lowerHalf hz (hbU h) hVd h] at hbd
    calc _ ≤ _ := hbd
      _ = C * ‖h‖ ^ 2 := by rw [hCdef]; ring
  have h0 : iteratedDeriv 3 (F 0) z = 0 := by
    rw [hF0]
    exact h35_pd_q_iteratedDeriv3_id z
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hε) z (mem_ball_self hε))
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min (ε / 2) (c / (C + 1)) := lt_min (by linarith) (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
  rw [mem_ball_zero_iff, lt_min_iff] at ht
  rw [h0, sub_zero, sub_zero, smul_eq_mul]
  calc ‖iteratedDeriv 3 (F t) z - t * iteratedDeriv 3 (ahVar ν.1) z‖ ≤ C * ‖t‖ ^ 2 := hd3 t ht.1
    _ ≤ c * ‖t‖ := by
      have h1 : C * ‖t‖ ≤ c := by
        have := ht.2
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith [norm_nonneg t]
      nlinarith [norm_nonneg t]

/-- **Part 2** (up to target 3): `∂_t φ_{tν}(z)|₀ = V[ν]‴(z)` for `z ∈ 𝕃` (linearization of
`S = (f‴ f′ - f″²)/f′² - ½(f″/f′)²` at `f₀ = id`, plus `h35_pd_q_d3`). -/
theorem h35_pd_q_part2 (ν : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    HasDerivAt (fun t : ℂ => bersFunction (fun w => t * ν.1 w) z) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := h35_pd_q_small h35_pd_q_zero ν
  obtain ⟨hkP, hhol⟩ := h35_pd_q_fam_hyps h35_pd_q_zero ν hk0 hk1 hb
  set F : ℂ → ℂ → ℂ := fun t => normalizedSolution (h35_pd_q_fam h35_pd_q_zero ν t).1 with hFdef
  have ha : ∀ w, DifferentiableOn ℂ (fun t => F t w) (ball 0 r) :=
    thm13_8_ahlfors_bers_holomorphic (μ := fun t => (h35_pd_q_fam h35_pd_q_zero ν t).1) (f := F) isOpen_ball
      hk0 hk1 hkP hhol (fun t _ => ut_spec _)
  have hconf := fun t => ut_conformal_lowerHalf (h35_pd_q_fam h35_pd_q_zero ν t)
  have hc := bB_hs_bound (ν := h35_pd_q_fam h35_pd_q_zero ν) isOpen_ball hk0 hk1 hkP
  have hF0 : F 0 = id := h35_pd_q_F0 ν hr hk0 hk1 hb
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := F) isOpen_lowerHalf (fun w _ => ha w)
    (fun t _ => (hconf t).1) hc z hz
  have hb0 : ball (0 : ℂ) r ∈ 𝓝 0 := ball_mem_nhds 0 hr
  have e1 := (hd1.differentiableAt hb0).hasDerivAt
  have e2 := (hd2.differentiableAt hb0).hasDerivAt
  have e3 : HasDerivAt (fun t => deriv (deriv (deriv (F t))) z) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
    have h := h35_pd_q_d3 ν hz hr hk0 hk1 hb
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h ⊢
    exact h
  have v1 : deriv (F 0) z = 1 := by rw [hF0, deriv_id]
  have v2 : deriv (deriv (F 0)) z = 0 := by rw [hF0, deriv_id', deriv_const]
  have v3 : deriv (deriv (deriv (F 0))) z = 0 := by rw [hF0, deriv_id', deriv_const', deriv_const]
  have hne : ∀ t, deriv (F t) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  have hS := (((e3.mul e1).sub (e2.mul e2)).div (e1.pow 2) (pow_ne_zero 2 (hne 0))).sub
    (((e2.div e1 (hne 0)).pow 2).const_mul (1 / 2))
  have hS' : HasDerivAt (fun t => (deriv (deriv (deriv (F t))) z * deriv (F t) z -
      deriv (deriv (F t)) z * deriv (deriv (F t)) z) / deriv (F t) z ^ 2 -
      1 / 2 * (deriv (deriv (F t)) z / deriv (F t) z) ^ 2) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
    convert hS using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, v1, v2, v3]
    ring
  refine hS'.congr_of_eventuallyEq ?_
  filter_upwards [hb0] with t ht
  have hfun : (fun w => t * ν.1 w) = (h35_pd_q_fam h35_pd_q_zero ν t).1 := by
    rw [h35_pd_q_fam_val h35_pd_q_zero ν hk0 hk1 hb ht]
    funext w
    simp [h35_pd_q_zero]
  simp only [bersFunction, hfun, indicator_of_mem hz]
  exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)

/-! #### B2–B4: `V[κ]‴ = 0`, the second-order Schwarz lemma, Ahlfors–Weill at `0` -/

/-- For `Im z < 0 ≤ Im ζ`: `c_z (1 + |ζ|) ≤ |ζ - z|` with `c_z = -Im z / (-Im z + |z| + 1)`. -/
theorem h35b_norm_sub_ge {z ζ : ℂ} (hz : z.im < 0) (hζ : 0 ≤ ζ.im) :
    -z.im / (-z.im + ‖z‖ + 1) * (1 + ‖ζ‖) ≤ ‖ζ - z‖ := by
  have hD : 0 < -z.im + ‖z‖ + 1 := by have := norm_nonneg z; linarith
  have h1 : -z.im ≤ ‖ζ - z‖ := by
    have h := Complex.abs_im_le_norm (ζ - z)
    rw [Complex.sub_im, abs_of_nonneg (by linarith)] at h
    linarith
  have h2 : ‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖ := norm_sub_norm_le ζ z
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt (neg_pos.2 hz)),
    mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ‖z‖ + 1)]

/-- The constant `c_z = -Im z / (-Im z + |z| + 1)` is positive for `Im z < 0`. -/
theorem h35b_cz_pos {z : ℂ} (hz : z.im < 0) : 0 < -z.im / (-z.im + ‖z‖ + 1) :=
  div_pos (neg_pos.2 hz) (by have := norm_nonneg z; linarith)

/-- Integrability of `κ g` for a bounded measurable `κ` vanishing on `Im ≤ 0` and `g = O((1 + |ζ|)⁻ⁿ)` on `ℍ`,
`n > 2`. -/
theorem h35b_integrable_of_decay {κ g : ℂ → ℂ} {k A : ℝ} {n : ℕ} (hn : 2 < n)
    (hκm : AEStronglyMeasurable κ volume) (hκb : ∀ᵐ ζ ∂volume, ‖κ ζ‖ ≤ k)
    (hκ0 : ∀ ζ : ℂ, ζ.im ≤ 0 → κ ζ = 0) (hgm : AEStronglyMeasurable g volume) (hA : 0 ≤ A)
    (hg : ∀ ζ : ℂ, 0 < ζ.im → ‖g ζ‖ ≤ A * ((1 + ‖ζ‖) ^ n)⁻¹) :
    Integrable (fun ζ => κ ζ * g ζ) := by
  have hint : Integrable (fun ζ : ℂ => (1 + ‖ζ‖) ^ (-(n : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]
    exact_mod_cast hn
  refine Integrable.mono' (hint.const_mul (k * A)) (hκm.mul hgm) ?_
  filter_upwards [hκb] with ζ hζ
  have hk : 0 ≤ k := (norm_nonneg _).trans hζ
  have hpos : 0 < 1 + ‖ζ‖ := by have := norm_nonneg ζ; linarith
  have hrp : (1 + ‖ζ‖) ^ (-(n : ℝ)) = ((1 + ‖ζ‖) ^ n)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  rw [hrp, norm_mul]
  by_cases him : ζ.im ≤ 0
  · rw [hκ0 ζ him, norm_zero, zero_mul]
    positivity
  · have h := hg ζ (not_le.1 him)
    calc ‖κ ζ‖ * ‖g ζ‖ ≤ k * (A * ((1 + ‖ζ‖) ^ n)⁻¹) :=
          mul_le_mul hζ h (norm_nonneg _) hk
      _ = k * A * ((1 + ‖ζ‖) ^ n)⁻¹ := by ring

/-- The decay `|(ζ - z)⁻³| ≤ c_z⁻³ (1 + |ζ|)⁻³` on `ℍ` (`z ∈ 𝕃`). -/
theorem h35b_decay3 {z ζ : ℂ} (hz : z.im < 0) (hζ : 0 < ζ.im) :
    ‖1 / (ζ - z) ^ 3‖ ≤ ((-z.im / (-z.im + ‖z‖ + 1)) ^ 3)⁻¹ * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have hc := h35b_cz_pos hz
  have hge := h35b_norm_sub_ge hz hζ.le
  have hp : 0 < 1 + ‖ζ‖ := by have := norm_nonneg ζ; linarith
  rw [norm_div, norm_one, norm_pow, ← mul_inv, ← mul_pow]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hge 3) |>.trans_eq
    (by rw [one_div])

/-- The decay `|(ζ - z)⁻³ (ζ - w)⁻¹| ≤ (c_z³ c_w)⁻¹ (1 + |ζ|)⁻⁴` on `ℍ` (`z, w ∈ 𝕃`). -/
theorem h35b_decay4 {z w ζ : ℂ} (hz : z.im < 0) (hw : w.im < 0) (hζ : 0 < ζ.im) :
    ‖1 / ((ζ - z) ^ 3 * (ζ - w))‖ ≤
      ((-z.im / (-z.im + ‖z‖ + 1)) ^ 3 * (-w.im / (-w.im + ‖w‖ + 1)))⁻¹ * ((1 + ‖ζ‖) ^ 4)⁻¹ := by
  have hcz := h35b_cz_pos hz
  have hcw := h35b_cz_pos hw
  have hgz := h35b_norm_sub_ge hz hζ.le
  have hgw := h35b_norm_sub_ge hw hζ.le
  have hp : 0 < 1 + ‖ζ‖ := by have := norm_nonneg ζ; linarith
  rw [norm_div, norm_one, norm_mul, norm_pow, ← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc (-z.im / (-z.im + ‖z‖ + 1)) ^ 3 * (-w.im / (-w.im + ‖w‖ + 1)) * (1 + ‖ζ‖) ^ 4
      = ((-z.im / (-z.im + ‖z‖ + 1)) * (1 + ‖ζ‖)) ^ 3 * ((-w.im / (-w.im + ‖w‖ + 1)) * (1 + ‖ζ‖)) := by ring
    _ ≤ ‖ζ - z‖ ^ 3 * ‖ζ - w‖ :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hgz 3) hgw (by positivity) (by positivity)

/-- **Orthogonality ⟹ `V[κ]‴ = 0`.**  If `∬ κ(ζ)/((ζ - z)³(ζ - w)) = 0` for all `w ∈ 𝕃`, then `V[κ]` is a quadratic
polynomial on `𝕃` (Taylor expansion of the kernel `ahKer` at `z` with an exact remainder), so `V[κ]‴(z) = 0`. -/
theorem h35b_ahVar_d3_eq_zero (κ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf)
    (horth : ∀ w ∈ lowerHalf, ∫ ζ, κ.1 ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0) :
    iteratedDeriv 3 (ahVar κ.1) z = 0 := by
  obtain ⟨⟨k, -, -, hm', hb'⟩, h0⟩ := κ.2
  rw [Measure.restrict_univ] at hm' hb'
  have hz' : z.im < 0 := hz
  set bz : ℂ → ℂ := fun ζ => 1 / (ζ - z) ^ 2 - 1 / (ζ * (ζ - 1)) with hbz
  -- the exact Taylor identity of the kernel
  have hid : ∀ w : ℂ, w.im < 0 → ∀ ζ : ℂ, κ.1 ζ * ahKer w ζ = κ.1 ζ * ahKer z ζ + (w - z) * (κ.1 ζ * bz ζ) +
      (w - z) ^ 2 * (κ.1 ζ * (1 / (ζ - z) ^ 3)) + (w - z) ^ 3 * (κ.1 ζ * (1 / ((ζ - z) ^ 3 * (ζ - w)))) := by
    intro w hw ζ
    by_cases hζ : ζ.im ≤ 0
    · rw [h0 ζ hζ]
      ring
    · have hζ' : 0 < ζ.im := not_le.1 hζ
      have n0 : ζ ≠ 0 := fun h => by rw [h, Complex.zero_im] at hζ'; exact lt_irrefl _ hζ'
      have n1 : ζ - 1 ≠ 0 := fun h => by
        have := congrArg Complex.im h
        simp at this
        linarith
      have nz : ζ - z ≠ 0 := fun h => by
        have := congrArg Complex.im h
        simp at this
        linarith
      have nw : ζ - w ≠ 0 := fun h => by
        have := congrArg Complex.im h
        simp at this
        linarith
      simp only [ahKer, hbz]
      field_simp
      ring
  -- integrability of the four pieces
  have hI1 : ∀ w : ℂ, Integrable (fun ζ => κ.1 ζ * ahKer w ζ) := fun w =>
    (ah_ker_integrable w).bdd_mul hm' hb'
  have hIc : Integrable (fun ζ => κ.1 ζ * (1 / (ζ - z) ^ 3)) :=
    h35b_integrable_of_decay (n := 3) (by norm_num) hm' hb' h0 (by fun_prop : Measurable _).aestronglyMeasurable
      (by have := h35b_cz_pos hz'; positivity) fun ζ hζ => h35b_decay3 hz' hζ
  have hIR : ∀ w : ℂ, w.im < 0 → Integrable (fun ζ => κ.1 ζ * (1 / ((ζ - z) ^ 3 * (ζ - w)))) := fun w hw =>
    h35b_integrable_of_decay (n := 4) (by norm_num) hm' hb' h0 (by fun_prop : Measurable _).aestronglyMeasurable
      (by have := h35b_cz_pos hz'; have := h35b_cz_pos hw; positivity) fun ζ hζ => h35b_decay4 hz' hw hζ
  have hw₀ : (z - I).im < 0 := by simp; linarith
  have hIb : Integrable (fun ζ => κ.1 ζ * bz ζ) := by
    have h := ((((hI1 (z - I)).sub (hI1 z)).sub (hIc.const_mul ((z - I - z) ^ 2))).sub
      ((hIR (z - I) hw₀).const_mul ((z - I - z) ^ 3))).const_mul (z - I - z)⁻¹
    refine h.congr (Eventually.of_forall fun ζ => ?_)
    simp only [Pi.sub_apply]
    rw [hid (z - I) hw₀ ζ]
    have hne : z - I - z ≠ 0 := by simp
    field_simp
    ring
  -- `V[κ]` is a quadratic polynomial on `𝕃`
  set A : ℂ := ∫ ζ, κ.1 ζ * ahKer z ζ
  set B : ℂ := ∫ ζ, κ.1 ζ * bz ζ
  set Γ : ℂ := ∫ ζ, κ.1 ζ * (1 / (ζ - z) ^ 3)
  have hquad : ∀ w : ℂ, w.im < 0 → ahVar κ.1 w = -(1 / π : ℂ) * (A + (w - z) * B + (w - z) ^ 2 * Γ) := by
    intro w hw
    have hR0 : ∫ ζ, κ.1 ζ * (1 / ((ζ - z) ^ 3 * (ζ - w))) = 0 :=
      (integral_congr_ae (Eventually.of_forall fun ζ => mul_one_div _ _)).trans (horth w hw)
    rw [ahVar, integral_congr_ae (Eventually.of_forall (hid w hw)), integral_add, integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_const_mul, hR0, mul_zero, add_zero]
    · exact hI1 z
    · exact hIb.const_mul _
    · exact (hI1 z).add (hIb.const_mul _)
    · exact hIc.const_mul _
    · exact ((hI1 z).add (hIb.const_mul _)).add (hIc.const_mul _)
    · exact (hIR w hw).const_mul _
  set p : ℂ → ℂ := fun w => -(1 / π : ℂ) * (A + (w - z) * B + (w - z) ^ 2 * Γ) with hpdef
  have hev : ahVar κ.1 =ᶠ[𝓝 z] p :=
    Filter.eventually_of_mem (isOpen_lowerHalf.mem_nhds hz) fun w hw => hquad w hw
  have hp1 : deriv p = fun w => -(1 / π : ℂ) * (B + 2 * (w - z) * Γ) := by
    funext w
    have h1 := (((hasDerivAt_id' w).sub_const z).mul_const B).const_add A
    have h2 := (((hasDerivAt_id' w).sub_const z).pow 2).mul_const Γ
    have h := (h1.add h2).const_mul (-(1 / π : ℂ))
    refine (h.congr_deriv ?_).deriv
    push_cast
    ring
  have hp2 : deriv (deriv p) = fun _ => -(1 / π : ℂ) * (2 * Γ) := by
    rw [hp1]
    funext w
    have h := (((((hasDerivAt_id' w).sub_const z).const_mul 2).mul_const Γ).const_add B).const_mul
      (-(1 / π : ℂ))
    refine (h.congr_deriv ?_).deriv
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hev.deriv.deriv.deriv_eq, hp2, deriv_const]

/-- Second-order Schwarz lemma: `F` holomorphic on `B(0, r)` with `|F| ≤ A` and `F(0) = F'(0) = 0` satisfies
`|F(t)| ≤ A |t|²/r²` (the Schwarz lemma `norm_dslope_le_div_of_mapsTo_ball` applied to `F` and to `dslope F 0`). -/
theorem h35b_schwarz2 {F : ℂ → ℂ} {r A : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball 0 r))
    (hA : ∀ t ∈ ball (0 : ℂ) r, ‖F t‖ ≤ A) (h0 : F 0 = 0) (h1 : deriv F 0 = 0) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) r) : ‖F t‖ ≤ A * ‖t‖ ^ 2 / r ^ 2 := by
  have hn : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  set G : ℂ → ℂ := dslope F 0 with hG
  have hGd : DifferentiableOn ℂ G (ball 0 r) := (differentiableOn_dslope hn).2 hF
  have hG0 : G 0 = 0 := by rw [hG, dslope_same, h1]
  have hmF : MapsTo F (ball 0 r) (closedBall (F 0) A) := fun s hs => by
    rw [mem_closedBall, h0, dist_zero_right]
    exact hA s hs
  have hGb : ∀ s ∈ ball (0 : ℂ) r, ‖G s‖ ≤ A / r := fun s hs =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hF hmF hs
  have hmG : MapsTo G (ball 0 r) (closedBall (G 0) (A / r)) := fun s hs => by
    rw [mem_closedBall, hG0, dist_zero_right]
    exact hGb s hs
  have hGG : ‖dslope G 0 t‖ ≤ A / r / r := Complex.norm_dslope_le_div_of_mapsTo_ball hGd hmG ht
  have e1 : F t = t * G t := by
    have h := sub_smul_dslope F 0 t
    rw [h0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  have e2 : G t = t * dslope G 0 t := by
    have h := sub_smul_dslope G 0 t
    rw [hG0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  rw [e1, e2, norm_mul, norm_mul]
  calc ‖t‖ * (‖t‖ * ‖dslope G 0 t‖) ≤ ‖t‖ * (‖t‖ * (A / r / r)) := by gcongr
    _ = A * ‖t‖ ^ 2 / r ^ 2 := by field_simp

/-- `f_{0 + tκ}` is `f_{tκ}` (the family `h35_pd_q_fam` through `0`, on the ball of `h35_pd_q_small`). -/
theorem h35b_fam_eq (κ : BeltramiH) {r k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => h35_pd_q_zero.1 w + t * κ.1 w) univ k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) r) : (h35_pd_q_fam h35_pd_q_zero κ t).1 = fun w => t * κ.1 w := by
  rw [h35_pd_q_fam_val h35_pd_q_zero κ hk0 hk1 hb ht]
  funext w
  simp [h35_pd_q_zero]

/-- **B2–B3.**  For `κ ∈ M` orthogonal to the kernels `(ζ - z)⁻³(ζ - w)⁻¹` (`z, w ∈ 𝕃`) there is `r > 0` with
`|S_{f_{tκ}}(z)| (Im z)² ≤ (3/2)|t|²/r²` for `|t| < r`, `z ∈ 𝕃`: `t ↦ S_{f_{tκ}}(z) (Im z)²` is holomorphic, bounded
by `3/2` (Kraus), and vanishes to second order at `0` (`f₀ = id`, and its derivative is `V[κ]‴(z) = 0`). -/
theorem h35b_bers_small (κ : BeltramiH)
    (horth : ∀ z ∈ lowerHalf, ∀ w ∈ lowerHalf, ∫ ζ, κ.1 ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0) :
    ∃ r > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      (∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => h35_pd_q_zero.1 w + t * κ.1 w) univ k) ∧
      ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ lowerHalf,
        ‖schwarzian (normalizedSolution (h35_pd_q_fam h35_pd_q_zero κ t).1) z‖ * z.im ^ 2 ≤
          3 / 2 * ‖t‖ ^ 2 / r ^ 2 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := h35_pd_q_small h35_pd_q_zero κ
  obtain ⟨hkP, hhol⟩ := h35_pd_q_fam_hyps h35_pd_q_zero κ hk0 hk1 hb
  refine ⟨r, hr, k, hk0, hk1, hb, fun t ht z hz => ?_⟩
  set F : ℂ → ℂ := fun s => schwarzian (normalizedSolution (h35_pd_q_fam h35_pd_q_zero κ s).1) z *
    ((z.im ^ 2 : ℝ) : ℂ) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 r) :=
    (h35_pd_q_schwarzian_holo isOpen_ball hk0 hk1 hkP hhol hz).mul_const _
  have hFb : ∀ s ∈ ball (0 : ℂ) r, ‖F s‖ ≤ 3 / 2 := fun s _ => by
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact bB_sd_kraus_pt _ hz
  have hF0 : F 0 = 0 := by
    rw [hF]
    simp only
    rw [h35_pd_q_F0 κ hr hk0 hk1 hb, bB_l_schwarzian_id, zero_mul]
  have hF1 : deriv F 0 = 0 := by
    have hd := h35_pd_q_part2 κ hz
    rw [h35b_ahVar_d3_eq_zero κ hz (horth z hz)] at hd
    have hev : F =ᶠ[𝓝 0] fun s => bersFunction (fun w => s * κ.1 w) z * ((z.im ^ 2 : ℝ) : ℂ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr] with s hs
      rw [hF]
      simp only [bersFunction, indicator_of_mem hz, h35b_fam_eq κ hk0 hk1 hb hs]
    rw [hev.deriv_eq, (hd.mul_const _).deriv, zero_mul]
  have h := h35b_schwarz2 hr hFd hFb hF0 hF1 ht
  rw [hF] at h
  simp only at h
  rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h

/-- **B4** (Ahlfors–Weill at the origin of `T`): there is `c > 0` such that every `φ ∈ A(𝕃)` with `‖φ‖ ≤ s < 1/c` is
the Schwarzian on `𝕃` of a normalized q.c. map `H` of the plane, holomorphic on `𝕃` and `(1 + cs)/(1 - cs)`-q.c. on
`ℍ` (the proof of `aw_core` at `μ = 0`, where `f_0 = id`). -/
theorem h35b_aw_zero : ∃ c : ℝ, 0 < c ∧ ∀ φ ∈ bersSpaceL, ∀ s : ℝ, 0 ≤ s → bersNormL φ ≤ ENNReal.ofReal s →
    s < 1 / c → ∃ (H : ℂ → ℂ) (K₂ : ℝ), IsKQC H univ K₂ ∧ H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧
      DifferentiableOn ℂ H lowerHalf ∧ (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      IsKQC H upperHalf ((1 + c * s) / (1 - c * s)) := by
  set μ₀ : BeltramiH := ⟨0, bB_l_zero_mem⟩ with hμ₀
  have hf0 : normalizedSolution μ₀.1 = id := bB_l_normalizedSolution_zero
  obtain ⟨K, hK1, -, hQD⟩ := aw_quasidisc μ₀
  obtain ⟨c, hc, hcD⟩ := thm20_3_ahlfors hK1
  refine ⟨c, hc, fun φ hφ s hs0 hsN hs1 => ?_⟩
  obtain ⟨hSD, hext⟩ := hcD _ hQD
  obtain ⟨ψ, hψd, hψid, hψN⟩ := aw_transport μ₀ hφ
  obtain ⟨hDo, hDc, hDs, -⟩ := t203_hsc_of_isKQuasidisc hQD
  obtain ⟨g, hgl, hgS⟩ := thm19_1_exists hDo hDc hDs hψd
  have hbf0 : bersFunction μ₀.1 = 0 := by
    funext z
    by_cases hz : z ∈ lowerHalf
    · rw [bersFunction, indicator_of_mem hz, hf0, bB_l_schwarzian_id]
      rfl
    · rw [bersFunction, indicator_of_notMem hz]
      rfl
  have hgN : schwarzianNorm g (normalizedSolution μ₀.1 '' lowerHalf) =
      hyperbolicSupNorm ψ (normalizedSolution μ₀.1 '' lowerHalf) := by
    unfold schwarzianNorm hyperbolicSupNorm
    refine biSup_congr fun z hz => ?_
    rw [hgS z hz]
  have hgs : schwarzianNorm g (normalizedSolution μ₀.1 '' lowerHalf) ≤ ENNReal.ofReal s := by
    rw [hgN, hψN, hbf0, sub_zero]
    exact hsN
  have hgs' : schwarzianNorm g (normalizedSolution μ₀.1 '' lowerHalf) < ENNReal.ofReal (1 / c) :=
    lt_of_le_of_lt hgs ((ENNReal.ofReal_lt_ofReal_iff (one_div_pos.2 hc)).2 hs1)
  have hgU := hSD.2.2 g hgl hgs'
  have hgE := hext g hgl hgs'
  have hS : ∀ z ∈ lowerHalf, schwarzian g (normalizedSolution μ₀.1 z) *
      deriv (normalizedSolution μ₀.1) z ^ 2 = φ z - schwarzian (normalizedSolution μ₀.1) z := by
    intro z hz
    rw [hgS _ (mem_image_of_mem _ hz)]
    exact hψid z hz
  obtain ⟨H, K₂, hH, hHs, hH0, hH1, hHd, hHS, hK'⟩ := aw_extend μ₀ hgU hgE hS
  refine ⟨H, K₂, hH, hHs, hH0, hH1, hHd, hHS, ?_⟩
  set S : ℝ := (schwarzianNorm g (normalizedSolution μ₀.1 '' lowerHalf)).toReal with hSdef
  have hinv : Function.invFunOn (id : ℂ → ℂ) univ = id := by
    funext w
    exact (injOn_id univ).leftInvOn_invFunOn (mem_univ w)
  rw [hf0, image_id, hinv, Function.comp_id] at hK'
  refine hK'.mono ?_
  have hc1 : c * s < 1 := by
    rw [lt_div_iff₀ hc] at hs1
    linarith
  have ht0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hts : S ≤ s := ENNReal.toReal_le_of_le_ofReal hs0 hgs
  have hct : c * S ≤ c * s := mul_le_mul_of_nonneg_left hts hc.le
  have hct0 : 0 ≤ c * S := mul_nonneg hc.le ht0
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **B5a.**  A normalized q.c. map `H` of the plane, holomorphic on `𝕃` with the Schwarzian of `f_ν` there, agrees
with `f_ν` on `ℝ` (`H = f_{ν'}` for `ν' = 1_ℍ μ_H` by `thm13_5_uniqueness_plane`, then `bA_equiv_of_schwarzian_eq`). -/
theorem h35b_eq_on_real (ν : BeltramiH) {H : ℂ → ℂ} {K₂ : ℝ} (hH : IsKQC H univ K₂) (hHs : H '' univ = univ)
    (hH0 : H 0 = 0) (hH1 : H 1 = 1) (hHd : DifferentiableOn ℂ H lowerHalf)
    (hHS : ∀ z ∈ lowerHalf, schwarzian H z = schwarzian (normalizedSolution ν.1) z) :
    ∀ x : ℝ, H x = normalizedSolution ν.1 x := by
  set ν' : BeltramiH := ⟨upperHalf.indicator (complexDilatation H), ut_rg_indicator_mem hH⟩ with hν'
  have hnorm : normalizedSolution ν'.1 = H := by
    obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ν'
    refine thm13_5_uniqueness_plane hq ⟨K₂, hH⟩ hs hHs ?_ hq0 hq1 hH0 hH1
    filter_upwards [hd, aw_nu_indicator_ae_eq hHd] with z h1 h2
    exact h1.trans h2
  have h := bA_equiv_of_schwarzian_eq (μ := ν') (ν := ν) fun z hz => by
    rw [hnorm]
    exact hHS z hz
  intro x
  have hx := h x
  rwa [hnorm] at hx

/-- The complex dilatation only depends on the germ of the map. -/
theorem h35b_cd_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    complexDilatation f z = complexDilatation g z := by
  simp only [complexDilatation, dz, dzbar, h.fderiv_eq]

/-- Pull back an a.e. statement through a q.c. map: if `P` holds a.e. on `f(D)`, then `P ∘ f` holds a.e. on `D`
(Lusin (N) for the `K`-q.c. inverse `f⁻¹`). -/
theorem h35b_ae_comp_of_ae {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {P : ℂ → Prop}
    (hP : ∀ᵐ w ∂(volume.restrict (f '' D)), P w) : ∀ᵐ z ∂(volume.restrict D), P (f z) := by
  have hfi := thm7_2_inv hf
  have hD : MeasurableSet D := hf.1.measurableSet
  have hfD : MeasurableSet (f '' D) := hfi.1.measurableSet
  rw [ae_restrict_iff' hfD, ae_iff] at hP
  set N : Set ℂ := {w | ¬ (w ∈ f '' D → P w)} with hN
  have hNnull : volume (Function.invFunOn f D '' (N ∩ f '' D)) = 0 :=
    ac_n_volume_image_null_of_isKQC hfi inter_subset_right (measure_mono_null inter_subset_left hP)
  rw [ae_restrict_iff' hD]
  filter_upwards [compl_mem_ae_iff.2 hNnull] with z hz hzD
  by_contra hPz
  exact hz ⟨f z, ⟨fun h => hPz (h (mem_image_of_mem f hzD)), mem_image_of_mem f hzD⟩,
    hf.2.2.1.2.1.leftInvOn_invFunOn hzD⟩

/-- The algebra of B5: if `m = (p - a)/(1 - ā p) u` with `|p|, |a| < 1`, `|u| = 1`, `|m| ≤ ε`, then `|p - a| ≤ 2ε`. -/
theorem h35b_alg {p a u m : ℂ} {ε : ℝ} (hp : ‖p‖ < 1) (ha : ‖a‖ < 1) (hu : ‖u‖ = 1)
    (hm : m = (p - a) / (1 - conj a * p) * u) (hmε : ‖m‖ ≤ ε) : ‖p - a‖ ≤ 2 * ε := by
  have hlt : ‖conj a * p‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg p]
  have hden : 1 - conj a * p ≠ 0 := by
    intro h
    have h1 : conj a * p = 1 := by linear_combination -h
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hdn : ‖1 - conj a * p‖ ≤ 2 := by
    calc ‖1 - conj a * p‖ ≤ ‖(1 : ℂ)‖ + ‖conj a * p‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hdpos : 0 < ‖1 - conj a * p‖ := norm_pos_iff.2 hden
  have hmn : ‖m‖ = ‖p - a‖ / ‖1 - conj a * p‖ := by
    rw [hm, norm_mul, hu, mul_one, norm_div]
  have hε : 0 ≤ ε := (norm_nonneg _).trans hmε
  rw [hmn, div_le_iff₀ hdpos] at hmε
  nlinarith

/-- **B5b.**  For `ν ∈ M` and a `K₂`-q.c. map `H` of the plane onto itself which is `K'`-q.c. on `ℍ` and equals `f_ν`
on `ℝ`, the map `P = H⁻¹ ∘ f_ν` is a q.c. homeomorphism of the plane fixing `ℝ` pointwise with `|μ_P - ν| ≤
2 (K' - 1)/(K' + 1)` a.e. on `ℍ` (`ahQ_comp_inv_dilatation` for `P ∘ f_ν⁻¹ = H⁻¹` on `f_ν(ℍ) = H(ℍ)`, the bound for
`H⁻¹` there, Lusin (N)). -/
theorem h35b_P (ν : BeltramiH) {H : ℂ → ℂ} {K₂ K' : ℝ} (hH : IsKQC H univ K₂) (hHs : H '' univ = univ)
    (hHK : IsKQC H upperHalf K') (hx : ∀ x : ℝ, H x = normalizedSolution ν.1 x) :
    (∃ K, IsKQC (Function.invFunOn H univ ∘ normalizedSolution ν.1) univ K) ∧
      (Function.invFunOn H univ ∘ normalizedSolution ν.1) '' univ = univ ∧
      (∀ x : ℝ, (Function.invFunOn H univ ∘ normalizedSolution ν.1) x = x) ∧
      ∀ᵐ ζ ∂(volume.restrict upperHalf),
        ‖complexDilatation (Function.invFunOn H univ ∘ normalizedSolution ν.1) ζ - ν.1 ζ‖ ≤
          2 * ((K' - 1) / (K' + 1)) := by
  obtain ⟨⟨KB, hB⟩, hBs, -, -, hBμ⟩ := ut_spec ν
  obtain ⟨⟨kν, -, hkν1, -, hkνb⟩, -⟩ := ν.2
  rw [Measure.restrict_univ] at hkνb
  set B : ℂ → ℂ := normalizedSolution ν.1 with hBdef
  set Hi : ℂ → ℂ := Function.invFunOn H univ with hHidef
  have hHi : IsKQC Hi univ K₂ := by
    have h := thm7_2_inv hH
    rwa [hHs] at h
  have hleft : ∀ z, Hi (H z) = z := fun z => hH.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, H (Hi w) = w := fun w =>
    Function.invFunOn_eq (show w ∈ H '' univ by rw [hHs]; exact mem_univ w)
  have hP : IsKQC (Hi ∘ B) univ (KB * K₂) := thm7_1_comp hB hHi (subset_univ _)
  have hPs : (Hi ∘ B) '' univ = univ := by
    rw [image_comp, hBs]
    exact eq_univ_of_forall fun z => ⟨H z, mem_univ _, hleft z⟩
  have hfix : ∀ x : ℝ, (Hi ∘ B) x = x := fun x => by
    rw [Function.comp_apply, ← hx x, hleft]
  refine ⟨⟨_, hP⟩, hPs, hfix, ?_⟩
  have hPH : (Hi ∘ B) '' upperHalf = upperHalf := (ut_preserves_halves hP hPs hfix).1
  have hBH : B '' upperHalf = H '' upperHalf := by
    have h : H '' ((Hi ∘ B) '' upperHalf) = B '' upperHalf := by
      rw [image_comp, image_image]
      simp only [hright, image_id']
    rw [hPH] at h
    exact h.symm
  have hBU : IsKQC B upperHalf KB := ac_t_isKQC_restrict hB isOpen_upperHalf (subset_univ _)
  have hPU : IsKQC (Hi ∘ B) upperHalf (KB * K₂) := ac_t_isKQC_restrict hP isOpen_upperHalf (subset_univ _)
  have hBinv : IsKQC (Function.invFunOn B upperHalf) (B '' upperHalf) KB := thm7_2_inv hBU
  have hBo : IsOpen (B '' upperHalf) := hBinv.1
  -- `P ∘ f_ν⁻¹ = H⁻¹` on `f_ν(ℍ)`
  have hcd1 : ∀ w ∈ B '' upperHalf,
      complexDilatation ((Hi ∘ B) ∘ Function.invFunOn B upperHalf) w = complexDilatation Hi w := by
    intro w hw
    refine h35b_cd_congr (Filter.eventually_of_mem (hBo.mem_nhds hw) fun v hv => ?_)
    show Hi (B (Function.invFunOn B upperHalf v)) = Hi v
    rw [Function.invFunOn_eq hv]
  -- `|μ_{H⁻¹}| ≤ (K' - 1)/(K' + 1)` a.e. on `H(ℍ)`
  have hHinv : IsKQC (Function.invFunOn H upperHalf) (H '' upperHalf) K' := thm7_2_inv hHK
  have hcd2 : ∀ w ∈ H '' upperHalf, complexDilatation (Function.invFunOn H upperHalf) w = complexDilatation Hi w := by
    intro w hw
    refine h35b_cd_congr (Filter.eventually_of_mem (hHinv.1.mem_nhds hw) fun v hv => ?_)
    have e1 : H (Function.invFunOn H upperHalf v) = v := Function.invFunOn_eq hv
    exact hH.2.2.1.2.1 (mem_univ _) (mem_univ _) (e1.trans (hright v).symm)
  have hbd : ∀ᵐ w ∂(volume.restrict (B '' upperHalf)), w ∈ B '' upperHalf →
      ‖complexDilatation Hi w‖ ≤ (K' - 1) / (K' + 1) := by
    rw [hBH]
    filter_upwards [(isKQC_maxDilatation_le hHinv).2] with w hw hwD
    rwa [← hcd2 w hwD]
  have hbd' := h35b_ae_comp_of_ae hBU hbd
  filter_upwards [ahQ_comp_inv_dilatation hPU hBU, hbd', ae_restrict_of_ae hBμ, ae_restrict_of_ae hkνb,
    (isKQC_maxDilatation_le hPU).2, thm9_6_cor2_jacobian_pos hBU, ae_restrict_mem isOpen_upperHalf.measurableSet]
    with ζ h1 h2 h3 h4 h5 h6 hζ
  have hBζ : B ζ ∈ B '' upperHalf := mem_image_of_mem B hζ
  rw [hcd1 _ hBζ, h3] at h1
  have hK1 : 1 ≤ KB * K₂ := hPU.2.1
  have hp : ‖complexDilatation (Hi ∘ B) ζ‖ < 1 :=
    lt_of_le_of_lt h5 (by rw [div_lt_one (by linarith)]; linarith)
  have hdz : dz B ζ ≠ 0 := by
    intro h0
    unfold jacobian at h6
    rw [h0, norm_zero] at h6
    nlinarith [norm_nonneg (dzbar B ζ)]
  have hu : ‖dz B ζ / conj (dz B ζ)‖ = 1 := by
    rw [norm_div, norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
  exact h35b_alg hp (lt_of_le_of_lt h4 hkν1) hu h1 (h2 hBζ)

/-- The derivative of the inverse Cayley map: `(C⁻¹)'(u) = 2i/(1 - u)²` for `u ≠ 1`. -/
theorem h35b_hasDerivAt_cayleyInv {u : ℂ} (hu : (1 : ℂ) - u ≠ 0) :
    HasDerivAt cayleyInv (2 * I / (1 - u) ^ 2) u := by
  have h := (((hasDerivAt_id' u).const_add 1).const_mul I).div ((hasDerivAt_id' u).const_sub 1) hu
  have hfun : cayleyInv = fun v : ℂ => I * (1 + v) / (1 - v) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **B6b** (back to `Δ`): for a q.c. homeomorphism `P` of the plane fixing `ℝ` pointwise, `C ∘ P ∘ C⁻¹` (`C` the
Cayley map) is a q.c. self-map of `Δ` whose boundary extension `Ĉ ∘ P̂ ∘ Ĉ⁻¹` is the identity on the circle. -/
theorem h35b_back {P : ℂ → ℂ} {K : ℝ} (hP : IsKQC P univ K) (hPs : P '' univ = univ)
    (hfix : ∀ x : ℝ, P x = x) : HasBoundaryValues (cayley ∘ (P ∘ cayleyInv)) id := by
  obtain ⟨e, he⟩ := t1_homeomorph hP hPs
  have hPH : P '' upperHalf = upperHalf := (ut_preserves_halves hP hPs hfix).1
  have hC := s35a_x_isConformalOnto_cayleyInv
  have hM := isConformalOnto_cayley
  have hKQC : IsKQC (cayley ∘ (P ∘ cayleyInv)) unitDisc (1 * K * 1) := by
    have h1 := thm7_1_comp (isKQC_one_of_conformal isOpen_ball hC)
      (ac_t_isKQC_restrict hP isOpen_upperHalf (subset_univ _)) hC.2.2.subset
    exact thm7_1_comp h1 (isKQC_one_of_conformal isOpen_upperHalf hM) (by rw [image_comp, hC.2.2, hPH])
  have hPC : MapsTo (P ∘ cayleyInv) unitDisc upperHalf := fun z hz => by
    rw [← hPH]
    exact mem_image_of_mem P (hC.mapsTo hz)
  have hE2 : IsHomeoExtension (P ∘ cayleyInv) unitDisc upperHalf
      (e.onePointCongr ∘ mobiusHomeomorph I I (-1) 1 cayley_det) :=
    s35a_z_isHomeoExtension_cayleyInv.comp_homeomorph hC.mapsTo e.onePointCongr
      (fun w _ => by rw [← he]; rfl) (by rw [s13x_de_image_toExt, he, hPH])
  have hdet : (1 : ℂ) * I - (-I) * 1 ≠ 0 := by
    rw [show (1 : ℂ) * I - (-I) * 1 = 2 * I by ring]
    exact mul_ne_zero two_ne_zero I_ne_zero
  have hEM : ∀ w : ℂ, 0 ≤ w.im → mobiusExt 1 (-I) 1 I (w : ExtPlane) = ((cayley w : ℂ) : ExtPlane) := by
    intro w hw
    have hden : (1 : ℂ) * w + I ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    rw [mobiusExt_coe hden]
    simp only [mobiusFn, cayley, one_mul, sub_eq_add_neg]
  have hE3 := hE2.comp_homeomorph (g := cayley) hPC (mobiusHomeomorph 1 (-I) 1 I hdet)
    (fun w hw => by rw [mobiusHomeomorph_apply]; exact hEM w (le_of_lt hw))
    (s35a_z_image_toExt (fun w hw => by rw [mobiusHomeomorph_apply]; exact hEM w (le_of_lt hw)) hM.2.2)
  refine ⟨⟨_, hKQC⟩, ?_, _, hE3, ?_⟩
  · rw [image_comp, image_comp, hC.2.2, hPH, hM.2.2]
  · intro ζ hζ
    by_cases hζ1 : ζ = 1
    · subst hζ1
      simp only [Function.comp_apply, mobiusHomeomorph_apply, id]
      rw [mobiusExt_coe_of_eq_zero (by norm_num), show e.onePointCongr extInf = extInf from rfl,
        mobiusExt_infty_of_ne one_ne_zero, div_one]
    · have hre : cayleyInv ζ = ((cayleyInv ζ).re : ℂ) :=
        Complex.ext (by simp) (by simp [s35a_z_cayleyInv_im hζ hζ1])
      obtain ⟨x, hx⟩ : ∃ x : ℝ, cayleyInv ζ = x := ⟨_, hre⟩
      have hden : (-1 : ℂ) * ζ + 1 ≠ 0 := by
        intro h0
        apply hζ1
        linear_combination -h0
      simp only [Function.comp_apply, mobiusHomeomorph_apply, id]
      rw [mobiusExt_coe hden, s35a_z_mobiusFn_cayleyInv, hx,
        show e.onePointCongr ((x : ℂ) : ExtPlane) = ((e x : ℂ) : ExtPlane) from rfl, he, hfix,
        hEM _ (by simp), ← hx, s35a_z_cayley_cayleyInv hζ1]

/-- **B6c.**  A.e. on `Δ`, `μ_{C ∘ P ∘ C⁻¹}(u) = μ_P(C⁻¹ u) conj(C⁻¹'(u))/C⁻¹'(u)` (conformal pre- and
post-composition, at the a.e. points where `P` is differentiable, transported by Lusin (N)). -/
theorem h35b_back_dil {P : ℂ → ℂ} {K : ℝ} (hP : IsKQC P univ K) (hPH : P '' upperHalf = upperHalf) :
    ∀ᵐ u ∂(volume.restrict unitDisc), complexDilatation (cayley ∘ (P ∘ cayleyInv)) u =
      complexDilatation P (cayleyInv u) * (conj (deriv cayleyInv u) / deriv cayleyInv u) := by
  have hT := s35a_x_isConformalOnto_cayleyInv
  have hM := isConformalOnto_cayley
  have hdU : ∀ᵐ z ∂(volume.restrict (cayleyInv '' unitDisc)), DifferentiableAt ℝ P z := by
    have h := thm9_3_differentiable_ae hP
    rw [Measure.restrict_univ] at h
    exact ae_restrict_of_ae h
  filter_upwards [h35b_ae_comp_of_ae (isKQC_one_of_conformal isOpen_ball hT) hdU,
    ae_restrict_mem isOpen_ball.measurableSet] with u hu huD
  have hTd : DifferentiableAt ℂ cayleyInv u := hT.1.differentiableAt (isOpen_ball.mem_nhds huD)
  have hT' : deriv cayleyInv u ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hT.1 hT.2.1 huD
  have hw : P (cayleyInv u) ∈ upperHalf := by
    rw [← hPH]
    exact mem_image_of_mem P (hT.mapsTo huD)
  have hCd : DifferentiableAt ℂ cayley (P (cayleyInv u)) := hM.1.differentiableAt (isOpen_upperHalf.mem_nhds hw)
  have hC' : deriv cayley (P (cayleyInv u)) ≠ 0 := deriv_ne_zero_of_injOn isOpen_upperHalf hM.1 hM.2.1 hw
  have hPT : DifferentiableAt ℝ (P ∘ cayleyInv) u := hu.comp u (hTd.restrictScalars ℝ)
  rw [complexDilatation_comp_conformal_left hPT hCd hC', complexDilatation_comp_conformal_right hTd hT' hu]

/-- **B6a** (orthogonality through the Cayley map): for `μ₂ ⊥ A(Δ)` and `ψ` holomorphic on `ℍ` with
`|ψ(ζ)| ≤ C (1 + |ζ|)⁻⁴` there, `∬_ℍ μ₂(Cζ) θ(Cζ) ψ(ζ) = 0` with `θ = T'/conj T'`, `T = C⁻¹` (the change of
variables `ζ = T u` gives `∬_Δ μ₂ φ` with `φ = T'² ψ ∘ T ∈ A(Δ)`, `|φ| ≤ C/4`). -/
theorem h35b_orth {μ₂ : ℂ → ℂ} (hμ : ∀ φ ∈ integrableQD, ∫ u in unitDisc, μ₂ u * φ u = 0) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ upperHalf) {C : ℝ} (hC : 0 ≤ C)
    (hψb : ∀ ζ ∈ upperHalf, ‖ψ ζ‖ ≤ C * ((1 + ‖ζ‖) ^ 4)⁻¹) :
    ∫ ζ in upperHalf, μ₂ (cayley ζ) * (deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))) * ψ ζ =
      0 := by
  have hT := s35a_x_isConformalOnto_cayleyInv
  have hb : ∀ u ∈ unitDisc, ‖deriv cayleyInv u ^ 2 * ψ (cayleyInv u)‖ ≤ C / 4 := by
    intro u hu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
    have hne : (1 : ℂ) - u ≠ 0 := cayleyInv_den_ne_zero hu1
    have hd : deriv cayleyInv u = 2 * I / (1 - u) ^ 2 := (h35b_hasDerivAt_cayleyInv hne).deriv
    have hψu := hψb _ (cayleyInv_mem_upperHalf hu1)
    have ha : 0 < ‖1 - u‖ := norm_pos_iff.2 hne
    have hab : 2 ≤ ‖1 - u‖ + ‖1 + u‖ := by
      calc (2 : ℝ) = ‖(1 - u) + (1 + u)‖ := by
            rw [show (1 - u) + (1 + u) = (2 : ℂ) by ring]
            simp
        _ ≤ ‖1 - u‖ + ‖1 + u‖ := norm_add_le _ _
    have hnT : ‖cayleyInv u‖ = ‖1 + u‖ / ‖1 - u‖ := by
      rw [cayleyInv, norm_div, norm_mul, norm_I, one_mul]
    have hnd : ‖deriv cayleyInv u‖ = 2 / ‖1 - u‖ ^ 2 := by
      rw [hd, norm_div, norm_mul, norm_pow, norm_I, mul_one]
      norm_num
    rw [hnT] at hψu
    rw [norm_mul, norm_pow, hnd]
    have hb0 : 0 ≤ ‖1 + u‖ := norm_nonneg _
    calc (2 / ‖1 - u‖ ^ 2) ^ 2 * ‖ψ (cayleyInv u)‖
        ≤ (2 / ‖1 - u‖ ^ 2) ^ 2 * (C * ((1 + ‖1 + u‖ / ‖1 - u‖) ^ 4)⁻¹) := by gcongr
      _ = C * 4 / (‖1 - u‖ + ‖1 + u‖) ^ 4 := by
          field_simp
          ring
      _ ≤ C / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have h16 : (2 : ℝ) ^ 4 ≤ (‖1 - u‖ + ‖1 + u‖) ^ 4 := pow_le_pow_left₀ (by norm_num) hab 4
          nlinarith
  have hφ : (fun u => deriv cayleyInv u ^ 2 * ψ (cayleyInv u)) ∈ integrableQD := by
    refine ⟨((hT.1.deriv isOpen_ball).pow 2).mul (hψd.comp hT.1 hT.mapsTo), ?_⟩
    unfold phiArea
    calc ∫⁻ u in unitDisc, ENNReal.ofReal ‖deriv cayleyInv u ^ 2 * ψ (cayleyInv u)‖
        ≤ ∫⁻ _ in unitDisc, ENNReal.ofReal (C / 4) :=
          setLIntegral_mono measurable_const fun u hu => ENNReal.ofReal_le_ofReal (hb u hu)
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  rw [← hT.2.2, ahP_integral_image (U := unitDisc) isOpen_ball hT.1 hT.2.1, ← hμ _ hφ]
  refine setIntegral_congr_fun isOpen_ball.measurableSet fun u hu => ?_
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
  have hd0 : deriv cayleyInv u ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hT.1 hT.2.1 hu
  have hc0 : conj (deriv cayleyInv u) ≠ 0 := (map_ne_zero _).2 hd0
  have hn : ((‖deriv cayleyInv u‖ ^ 2 : ℝ) : ℂ) = deriv cayleyInv u * conj (deriv cayleyInv u) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [cayley_cayleyInv hu1, Complex.real_smul, hn]
  field_simp

/-- A measurable representative of a bounded `μ` on `Δ`, bounded everywhere by `|M| + 1`. -/
theorem h35b_rep {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ (volume.restrict unitDisc)) {M : ℝ}
    (hM : ∀ᵐ z ∂(volume.restrict unitDisc), ‖μ z‖ ≤ M) :
    ∃ μ₂ : ℂ → ℂ, Measurable μ₂ ∧ (∀ z, ‖μ₂ z‖ ≤ |M| + 1) ∧ ∀ᵐ z ∂(volume.restrict unitDisc), μ z = μ₂ z := by
  have hμ₁m : Measurable (hμm.mk μ) := hμm.stronglyMeasurable_mk.measurable
  refine ⟨fun z => if ‖hμm.mk μ z‖ ≤ |M| + 1 then hμm.mk μ z else 0,
    Measurable.ite (measurableSet_le hμ₁m.norm measurable_const) hμ₁m measurable_const, fun z => ?_, ?_⟩
  · beta_reduce
    by_cases h : ‖hμm.mk μ z‖ ≤ |M| + 1
    · rw [ite_eq_left h]
      exact h
    · rw [ite_eq_right h, norm_zero]
      positivity
  · filter_upwards [hμm.ae_eq_mk, hM] with z h1 h2
    have h : ‖hμm.mk μ z‖ ≤ |M| + 1 := by
      rw [← h1]
      linarith [le_abs_self M]
    rw [ite_eq_left h]
    exact h1

/-- **B1 + B6a.**  From a bounded measurable `μ₂ ⊥ A(Δ)` (`|μ₂| ≤ M'`), the coefficient
`κ = 1_ℍ (1/(2M')) (μ₂ ∘ C) θ ∘ C ∈ M` (`θ = T'/conj T'`, `T = C⁻¹`) is orthogonal to the kernels
`(ζ - z)⁻³ (ζ - w)⁻¹` (`z, w ∈ 𝕃`). -/
theorem h35b_kappa {μ₂ : ℂ → ℂ} {M' : ℝ} (hM' : 0 < M') (hm : Measurable μ₂) (hb : ∀ z, ‖μ₂ z‖ ≤ M')
    (hμ : ∀ φ ∈ integrableQD, ∫ u in unitDisc, μ₂ u * φ u = 0) :
    ∃ κ : BeltramiH, (∀ ζ ∈ upperHalf, κ.1 ζ = ((1 / (2 * M') : ℝ) : ℂ) *
        (μ₂ (cayley ζ) * (deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))))) ∧
      ∀ z ∈ lowerHalf, ∀ w ∈ lowerHalf, ∫ ζ, κ.1 ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0 := by
  have hU : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℂ → ℂ, κ₀ = upperHalf.indicator (fun ζ => ((1 / (2 * M') : ℝ) : ℂ) *
      (μ₂ (cayley ζ) * (deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))))) := ⟨_, rfl⟩
  have hcay : Measurable cayley := by
    have h : cayley = fun z : ℂ => (z - I) / (z + I) := rfl
    rw [h]
    fun_prop
  have hθm : Measurable fun u => deriv cayleyInv u / conj (deriv cayleyInv u) :=
    (measurable_deriv cayleyInv).div (Complex.continuous_conj.measurable.comp (measurable_deriv cayleyInv))
  have hκm : Measurable κ₀ := by
    rw [hκ₀]
    exact (((hm.comp hcay).mul (hθm.comp hcay)).const_mul _).indicator hU
  have hκb : ∀ ζ, ‖κ₀ ζ‖ ≤ 1 / 2 := by
    intro ζ
    rw [hκ₀]
    by_cases hζ : ζ ∈ upperHalf
    · rw [indicator_of_mem hζ, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have hθ : ‖deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))‖ ≤ 1 := by
        rw [norm_div, norm_conj]
        exact div_self_le_one _
      calc 1 / (2 * M') * (‖μ₂ (cayley ζ)‖ *
            ‖deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))‖)
          ≤ 1 / (2 * M') * (M' * 1) := by gcongr; exact hb _
        _ = 1 / 2 := by field_simp
    · rw [indicator_of_notMem hζ, norm_zero]
      norm_num
  have h0 : ∀ z : ℂ, z.im ≤ 0 → κ₀ z = 0 := fun z hz => by
    rw [hκ₀]
    exact indicator_of_notMem (show z ∉ upperHalf from not_lt.2 hz) _
  have hκB : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff κ₀ univ k) ∧ ∀ z : ℂ, z.im ≤ 0 → κ₀ z = 0 :=
    ⟨⟨1 / 2, by norm_num, by norm_num, ⟨hκm.aestronglyMeasurable, Eventually.of_forall hκb⟩⟩, h0⟩
  refine ⟨⟨κ₀, hκB⟩, fun ζ hζ => by show κ₀ ζ = _; rw [hκ₀, indicator_of_mem hζ], fun z hz w hw => ?_⟩
  have hz' : z.im < 0 := hz
  have hw' : w.im < 0 := hw
  have hψd : DifferentiableOn ℂ (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf := by
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun ζ hζ => ?_
    have hζ' : 0 < ζ.im := hζ
    have n1 : ζ - z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have n2 : ζ - w ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    exact mul_ne_zero (pow_ne_zero 3 n1) n2
  have hC : 0 ≤ ((-z.im / (-z.im + ‖z‖ + 1)) ^ 3 * (-w.im / (-w.im + ‖w‖ + 1)))⁻¹ := by
    have := h35b_cz_pos hz'
    have := h35b_cz_pos hw'
    positivity
  have hO := h35b_orth hμ hψd hC fun ζ hζ => h35b_decay4 hz' hw' hζ
  show ∫ ζ, κ₀ ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0
  calc ∫ ζ, κ₀ ζ / ((ζ - z) ^ 3 * (ζ - w))
      = ∫ ζ in upperHalf, ((1 / (2 * M') : ℝ) : ℂ) * (μ₂ (cayley ζ) *
          (deriv cayleyInv (cayley ζ) / conj (deriv cayleyInv (cayley ζ))) * (1 / ((ζ - z) ^ 3 * (ζ - w)))) := by
        rw [← integral_indicator hU]
        congr 1
        funext ζ
        by_cases hζ : ζ ∈ upperHalf
        · rw [hκ₀, indicator_of_mem hζ, indicator_of_mem hζ]
          ring
        · rw [hκ₀, indicator_of_notMem hζ, indicator_of_notMem hζ, zero_div]
    _ = 0 := by rw [integral_const_mul, hO, mul_zero]

/-- **(B) Teichmüller's lemma** ("infinitesimally trivial ⟹ trivial to second order").  For a
bounded measurable `μ` on `Δ` annihilating `A(Δ)` there are `C ≥ 0`, `t₀ > 0` and, for `0 < t < t₀`,
q.c. self-maps `g` of `Δ` with identity boundary values and `|μ_g - tμ| ≤ C t²` a.e. -/
theorem h35_trivial {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ (volume.restrict unitDisc)) {M : ℝ}
    (hM : ∀ᵐ z ∂(volume.restrict unitDisc), ‖μ z‖ ≤ M)
    (hμ : ∀ φ ∈ integrableQD, ∫ z in unitDisc, μ z * φ z = 0) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ∃ g : ℂ → ℂ, HasBoundaryValues g id ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation g z - t * μ z‖ ≤ C * t ^ 2 := by
  obtain ⟨μ₂, hμ₂m, hμ₂b, hμ₂ae⟩ := h35b_rep hμm hM
  have hM' : 0 < |M| + 1 := by positivity
  have hμ₂orth : ∀ φ ∈ integrableQD, ∫ u in unitDisc, μ₂ u * φ u = 0 := fun φ hφ => by
    rw [← hμ φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hμ₂ae] with z hz
    rw [hz]
  obtain ⟨κ, hκval, horth⟩ := h35b_kappa hM' hμ₂m hμ₂b hμ₂orth
  obtain ⟨r, hr, k, hk0, hk1, hb, hS⟩ := h35b_bers_small κ horth
  obtain ⟨c, hc, hAW⟩ := h35b_aw_zero
  set lam : ℝ := 1 / (2 * (|M| + 1)) with hlam
  have hlam0 : 0 < lam := by positivity
  set s₀ : ℝ := r / (2 * (c + 1)) with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  refine ⟨3 * c / (r ^ 2 * lam ^ 2), lam * s₀, by positivity, by positivity, fun t ht0 ht1 => ?_⟩
  set s : ℝ := t / lam with hsdef
  have hs0 : 0 < s := div_pos ht0 hlam0
  have hss₀ : s < s₀ := by
    rw [hsdef, div_lt_iff₀ hlam0]
    linarith
  have h2s : 2 * (c + 1) * s < r := by
    rw [hs₀, lt_div_iff₀ (by positivity)] at hss₀
    linarith
  have hsr : s < r := by nlinarith
  have hsb : (s : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact hsr
  set ν : BeltramiH := h35_pd_q_fam h35_pd_q_zero κ (s : ℂ) with hνdef
  have hνval : ν.1 = fun w => (s : ℂ) * κ.1 w := h35b_fam_eq κ hk0 hk1 hb hsb
  -- the Bers function of `ν` is `O(s²)`
  set s' : ℝ := 3 / 2 * s ^ 2 / r ^ 2 with hs'def
  have hs'0 : 0 ≤ s' := by positivity
  have hφN : bersNormL (bersFunction ν.1) ≤ ENNReal.ofReal s' := by
    refine iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_
    rw [bersFunction, indicator_of_mem hz]
    have h := hS (s : ℂ) hsb z hz
    rwa [Complex.norm_real, Real.norm_of_nonneg hs0.le] at h
  have hconf := ut_conformal_lowerHalf ν
  have hφmem : bersFunction ν.1 ∈ bersSpaceL :=
    ⟨(schwarzian_holomorphic isOpen_lowerHalf (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hconf)).congr
      fun z hz => indicator_of_mem hz _, lt_of_le_of_lt hφN ENNReal.ofReal_lt_top⟩
  have hcs : c * s' < 1 / 2 := by
    have h3 : 3 * c * s ^ 2 < r ^ 2 := by
      have hsq := mul_self_lt_mul_self (by positivity) h2s
      nlinarith [mul_nonneg (sq_nonneg (c - 1)) (sq_nonneg s), sq_nonneg s]
    rw [hs'def, show c * (3 / 2 * s ^ 2 / r ^ 2) = 3 * c * s ^ 2 / (2 * r ^ 2) by ring,
      div_lt_iff₀ (by positivity)]
    linarith
  have hs'c : s' < 1 / c := by
    rw [lt_div_iff₀ hc]
    linarith
  obtain ⟨H, K₂, hH, hHs, hH0, hH1, hHd, hHS, hHK⟩ := hAW _ hφmem s' hs'0 hφN hs'c
  have hx := h35b_eq_on_real ν hH hHs hH0 hH1 hHd fun z hz => by
    rw [hHS z hz, bersFunction, indicator_of_mem hz]
  obtain ⟨⟨KP, hP⟩, hPs, hfix, hdil⟩ := h35b_P ν hH hHs hHK hx
  have hPH := (ut_preserves_halves hP hPs hfix).1
  refine ⟨_, h35b_back hP hPs hfix, ?_⟩
  have hT := s35a_x_isConformalOnto_cayleyInv
  have hdil' := h35b_ae_comp_of_ae (isKQC_one_of_conformal (D := unitDisc) isOpen_ball hT)
    (by rw [hT.2.2]; exact hdil)
  filter_upwards [h35b_back_dil hP hPH, hdil', hμ₂ae, ae_restrict_mem isOpen_ball.measurableSet]
    with u h1 h2 h3 hu
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
  have hTu : cayleyInv u ∈ upperHalf := cayleyInv_mem_upperHalf hu1
  have hd0 : deriv cayleyInv u ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hT.1 hT.2.1 hu
  have hc0 : conj (deriv cayleyInv u) ≠ 0 := (map_ne_zero _).2 hd0
  have hνu : ν.1 (cayleyInv u) =
      (s : ℂ) * ((lam : ℂ) * (μ₂ u * (deriv cayleyInv u / conj (deriv cayleyInv u)))) := by
    rw [hνval]
    beta_reduce
    rw [hκval _ hTu, cayley_cayleyInv hu1]
  rw [hνu] at h2
  rw [h1, h3]
  have hts : (t : ℂ) = (s : ℂ) * (lam : ℂ) := by
    have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0.ne'
    rw [hsdef, Complex.ofReal_div, div_mul_cancel₀ _ hlamC]
  have key : complexDilatation (Function.invFunOn H univ ∘ normalizedSolution ν.1) (cayleyInv u) *
      (conj (deriv cayleyInv u) / deriv cayleyInv u) - (t : ℂ) * μ₂ u =
      (complexDilatation (Function.invFunOn H univ ∘ normalizedSolution ν.1) (cayleyInv u) -
        (s : ℂ) * ((lam : ℂ) * (μ₂ u * (deriv cayleyInv u / conj (deriv cayleyInv u))))) *
        (conj (deriv cayleyInv u) / deriv cayleyInv u) := by
    rw [hts]
    field_simp
  have hunit : ‖conj (deriv cayleyInv u) / deriv cayleyInv u‖ = 1 := by
    rw [norm_div, norm_conj, div_self (norm_ne_zero_iff.2 hd0)]
  rw [key, norm_mul, hunit, mul_one]
  refine h2.trans (le_of_eq ?_)
  have hne : 1 - c * s' ≠ 0 := by linarith
  have hK : ((1 + c * s') / (1 - c * s') - 1) / ((1 + c * s') / (1 - c * s') + 1) = c * s' := by
    rw [div_sub_one hne, div_add_one hne, div_div_div_cancel_right₀ hne]
    ring
  rw [hK, hs'def, hsdef]
  field_simp

/-! ### Scout H's `thm35_5` core: Hamilton's theorem from (A) `h35_duality` and (B) `h35_trivial` -/

/-! ### The pointwise hyperbolic estimate -/

/-- Pointwise: if `|κ| ≤ k < 1`, `|ν| ≤ H`, `0 ≤ t ≤ 1`, `|pz - t(κ - ν)| ≤ C t²` and
`t(k + H + C) ≤ 1/2`, then `d(κ, pz) ≤ artanh k - t(k - H) + (C + 2(k + H + C)²) t²`
(`h35_pd_discPoincareDist_sub_le_explicit`, and monotonicity of `x ↦ artanh x - t x`). -/
theorem h35_pt_hyp {κ ν pz : ℂ} {k H C t : ℝ} (hk1 : k < 1) (hκ : ‖κ‖ ≤ k) (hν : ‖ν‖ ≤ H)
    (hC : 0 ≤ C) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hpz : ‖pz - t * (κ - ν)‖ ≤ C * t ^ 2)
    (hs : t * (k + H + C) ≤ 1 / 2) :
    h35_pd_discPoincareDist κ pz ≤ Real.artanh k - t * (k - H) + (C + 2 * (k + H + C) ^ 2) * t ^ 2 := by
  have hH0 : 0 ≤ H := (norm_nonneg ν).trans hν
  have hk0 : 0 ≤ k := (norm_nonneg κ).trans hκ
  have hκ1 : ‖κ‖ < 1 := hκ.trans_lt hk1
  have ht2 : t ^ 2 ≤ t := by nlinarith
  set A := k + H + C with hA
  have hA0 : 0 ≤ A := by positivity
  -- `|pz| ≤ t A ≤ 1/2`
  have hpzn : ‖pz‖ ≤ t * A := by
    have h1 : ‖t * (κ - ν)‖ ≤ t * (k + H) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hκ hν)) ht0
    calc ‖pz‖ = ‖(pz - t * (κ - ν)) + t * (κ - ν)‖ := by rw [sub_add_cancel]
      _ ≤ ‖pz - t * (κ - ν)‖ + ‖t * (κ - ν)‖ := norm_add_le _ _
      _ ≤ C * t ^ 2 + t * (k + H) := add_le_add hpz h1
      _ ≤ C * t + t * (k + H) := by nlinarith
      _ = t * A := by rw [hA]; ring
  have hpz1 : ‖pz‖ < 1 := by linarith
  -- `|κ - pz| ≤ (1 - t)|κ| + t H + C t²`
  have hdiff : ‖κ - pz‖ ≤ (1 - t) * ‖κ‖ + t * H + C * t ^ 2 := by
    have h1 : ‖κ - t * (κ - ν)‖ ≤ (1 - t) * ‖κ‖ + t * H := by
      have e : κ - t * (κ - ν) = ((1 - t : ℝ) : ℂ) * κ + (t : ℂ) * ν := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hν ht0)
    calc ‖κ - pz‖ = ‖(κ - t * (κ - ν)) - (pz - t * (κ - ν))‖ := by ring_nf
      _ ≤ ‖κ - t * (κ - ν)‖ + ‖pz - t * (κ - ν)‖ := norm_sub_le _ _
      _ ≤ (1 - t) * ‖κ‖ + t * H + C * t ^ 2 := add_le_add h1 hpz
  -- `|pz|²/(1 - |pz|²) ≤ 2 (tA)²`
  have hsq : ‖pz‖ ^ 2 / (1 - ‖pz‖ ^ 2) ≤ 2 * A ^ 2 * t ^ 2 := by
    have h1 := h35_pd_sq_div_one_sub_sq_le (norm_nonneg pz) hpzn (by linarith)
    have h2 : (t * A) ^ 2 / (1 - (t * A) ^ 2) ≤ 2 * A ^ 2 * t ^ 2 := by
      have htA0 : 0 ≤ t * A := mul_nonneg ht0 hA0
      have hd : (1 : ℝ) / 2 ≤ 1 - (t * A) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg (t * A)]
    linarith
  -- `artanh |κ| - t |κ| ≤ artanh k - t k`
  have hmono : Real.artanh ‖κ‖ - t * ‖κ‖ ≤ Real.artanh k - t * k := by
    have h1 : Real.artanh ‖κ‖ - ‖κ‖ ≤ Real.artanh k - k :=
      h35_pd_artanh_sub_self_monotoneOn ⟨by linarith [norm_nonneg κ], hκ1⟩ ⟨by linarith, hk1⟩ hκ
    nlinarith [mul_le_mul_of_nonneg_left hκ (by linarith : (0 : ℝ) ≤ 1 - t)]
  have hmain := h35_pd_discPoincareDist_sub_le_explicit hκ1 hpz1
  rw [h35_pd_discPoincareDist_zero hκ1] at hmain
  nlinarith

/-! ### Transfer of a.e. statements along `g` -/

/-- If `P (g z)` holds for a.e. `z ∈ Δ` and `g` is a q.c. self-map of `Δ`, then `P w` holds for a.e.
`w ∈ Δ` (Lusin (N) for `g`). -/
theorem h35_ae_of_ae_comp {g : ℂ → ℂ} {K : ℝ} (hg : IsKQC g unitDisc K)
    (hgs : g '' unitDisc = unitDisc) {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict unitDisc), P (g z)) :
    ∀ᵐ w ∂(volume.restrict unitDisc), P w := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  rw [ae_restrict_iff' hΔ, ae_iff] at hP
  set N : Set ℂ := {z | ¬ (z ∈ unitDisc → P (g z))} with hN
  have hNnull : volume (g '' (N ∩ unitDisc)) = 0 :=
    ac_n_volume_image_null_of_isKQC hg inter_subset_right (measure_mono_null inter_subset_left hP)
  rw [ae_restrict_iff' hΔ]
  filter_upwards [compl_mem_ae_iff.2 hNnull] with w hw hwΔ
  by_contra hPw
  obtain ⟨z, hz, rfl⟩ : w ∈ g '' unitDisc := by rw [hgs]; exact hwΔ
  exact hw ⟨z, ⟨fun h => hPw (h hz), hz⟩, rfl⟩

/-! ### The assembly -/

/-- **Theorem 35.5 from (A) and (B)** (axiom-clean conditional core): Hamilton's theorem for the disc,
given the duality lemma `hA` and Teichmüller's lemma `hB` as hypotheses (their statements are those
of `h35_ax_duality`, `h35_ax_trivial` in `h35_probe_thm35_5_ax.lean`). -/
theorem h35_thm35_5_of_AB
    (hA : ∀ {κ : ℂ → ℂ}, AEStronglyMeasurable κ (volume.restrict unitDisc) →
      essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1 →
      ∃ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict unitDisc) ∧
        (∀ᵐ z ∂(volume.restrict unitDisc), ‖ν z‖ ≤ hamiltonH κ) ∧
        ∀ φ ∈ integrableQD, ∫ z in unitDisc, (κ z - ν z) * φ z = 0)
    (hB : ∀ {μ : ℂ → ℂ}, AEStronglyMeasurable μ (volume.restrict unitDisc) → ∀ {M : ℝ},
      (∀ᵐ z ∂(volume.restrict unitDisc), ‖μ z‖ ≤ M) →
      (∀ φ ∈ integrableQD, ∫ z in unitDisc, μ z * φ z = 0) →
      ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ∃ g : ℂ → ℂ, HasBoundaryValues g id ∧
        ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation g z - t * μ z‖ ≤ C * t ^ 2)
    {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : IsExtremalForBoundary f₀ h) :
    hamiltonH (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  set κ := complexDilatation f₀ with hκdef
  have hκ := m35_essSup_lt_one hf₀.1.1
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  set k := beltramiNormDisc κ with hkdef
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) :=
    ((measurable_dzbar f₀).div (measurable_dz f₀)).aestronglyMeasurable
  have hHle : hamiltonH κ ≤ k :=
    hamiltonSup_le hk0 fun φ hφ => norm_integral_mul_le_of_admissible hκ hφ
  refine le_antisymm hHle (not_lt.1 fun hlt => ?_)
  set H := hamiltonH κ with hHdef
  have hH0 : 0 ≤ H := hamiltonSup_nonneg (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) fun _ => norm_nonneg _
  have hkpos : 0 < k := lt_of_le_of_lt hH0 hlt
  -- (A): `ν` with `|ν| ≤ H` and `κ - ν ⊥ A(Δ)`
  obtain ⟨ν, hνm, hνH, hνorth⟩ := hA hκm hκ
  have hμM : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z - ν z‖ ≤ k + H := by
    filter_upwards [hae, hνH] with z h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  -- (B): the trivial deformations
  obtain ⟨C, t₀, hC, ht₀, htriv⟩ := hB (hκm.sub hνm) hμM hνorth
  set A := k + H + C with hA
  have hA0 : 0 ≤ A := by positivity
  set E := C + 2 * A ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  -- choose `t`
  set t : ℝ := min (min (t₀ / 2) (1 / 2)) (min (1 / (2 * A + 2)) ((k - H) / (2 * (E + 1)))) with ht
  have hkH : 0 < k - H := by linarith
  have htpos : 0 < t := by
    refine lt_min (lt_min (by linarith) (by norm_num)) (lt_min (by positivity) (by positivity))
  have htt₀ : t < t₀ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  have htA : t * A ≤ 1 / 2 := by
    have h1 : t ≤ 1 / (2 * A + 2) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : t * (2 * A + 2) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      exact h1
    nlinarith
  have htE : t * E < k - H := by
    have h1 : t ≤ (k - H) / (2 * (E + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set δ := t * (k - H) - E * t ^ 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : E * t ^ 2 = (t * E) * t := by ring
    rw [this]
    nlinarith
  obtain ⟨g, hgb, hgμ⟩ := htriv t htpos htt₀
  -- the maps
  obtain ⟨⟨Kg, hKg⟩, hgs, G, hG, hGid⟩ := hgb
  obtain ⟨⟨K₀, hK₀⟩, hf₀s, F₀, hF₀, hF₀h⟩ := hf₀.1
  set gi := Function.invFunOn g unitDisc with hgi
  have hgiK : IsKQC gi unitDisc Kg := by
    have h' := thm7_2_inv hKg
    rwa [hgs] at h'
  have hleft : LeftInvOn gi g unitDisc := hKg.2.2.1.2.1.leftInvOn_invFunOn
  have hgiimg : gi '' unitDisc = unitDisc := by
    have h' := hleft.image_image
    rw [hgs] at h'
    exact h'
  set F := f₀ ∘ gi with hFdef
  have hFK : IsKQC F unitDisc (Kg * K₀) := thm7_1_comp hgiK hK₀ hgiimg.le
  have hFs : F '' unitDisc = unitDisc := by rw [hFdef, image_comp, hgiimg, hf₀s]
  -- `F` has the boundary values `h`
  have hGi := m35_isHomeoExtension_invFunOn hKg.2.2.1.2.1 hgs hG
  have hFext : IsHomeoExtension F unitDisc unitDisc
      (F₀ ∘ Function.invFunOn G (closure (toExt unitDisc))) :=
    hF₀.comp hGi fun z hz => hgiimg ▸ mem_image_of_mem gi hz
  have hFb : HasBoundaryValues F h := by
    refine ⟨⟨Kg * K₀, hFK⟩, hFs, _, hFext, fun ζ hζ => ?_⟩
    have hmem := s35a_x_mem_closure hζ
    have hGζ : G ζ = ζ := hGid ζ hζ
    have hinv : Function.invFunOn G (closure (toExt unitDisc)) ζ = ζ := by
      have h1 := hG.2.2.1.leftInvOn_invFunOn hmem
      rwa [hGζ] at h1
    simp only [Function.comp_apply, hinv]
    exact hF₀h ζ hζ
  -- the dilatation of `F`: `artanh |μ_F (g z)| ≤ artanh k - δ`
  set c := Real.tanh (Real.artanh k - δ) with hc
  have hcI : c ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hkI : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hk1⟩
  have hck : c < k := by
    rw [← Real.artanh_lt_artanh_iff hcI hkI, hc, Real.artanh_tanh]
    linarith
  have hpt : ∀ᵐ z ∂(volume.restrict unitDisc), ‖complexDilatation F (g z)‖ ≤ c := by
    filter_upwards [ahQ_comp_inv_dilatation hK₀ hKg, thm9_6_cor2_jacobian_pos hKg, hae, hνH, hgμ,
      (isKQC_maxDilatation_le hKg).2] with z hCz hJz hκz hνz hgz hgbd
    have hdz : dz g z ≠ 0 := by
      intro h0
      unfold jacobian at hJz
      rw [h0, norm_zero] at hJz
      nlinarith [norm_nonneg (dzbar g z)]
    set pz := complexDilatation g z with hpzdef
    have hpz' : ‖pz - t * (κ z - ν z)‖ ≤ C * t ^ 2 := hgz
    have hρeq : ‖complexDilatation F (g z)‖ = ‖(κ z - pz) / (1 - conj (κ z) * pz)‖ := by
      rw [hFdef, hgi, hCz, norm_mul, norm_div (dz g z), Complex.norm_conj,
        div_self (norm_ne_zero_iff.2 hdz), mul_one, h35_pd_b_norm_conj_denom]
    -- `ρ < 1`
    have hpz1 : ‖pz‖ < 1 := by
      have hKg1 : (1 : ℝ) ≤ Kg := hKg.2.1
      exact lt_of_le_of_lt hgbd ((div_lt_one (by linarith)).2 (by linarith))
    set ρ := ‖(κ z - pz) / (1 - conj (κ z) * pz)‖ with hρ
    have hρ1 : ρ < 1 := by
      set m := max ‖κ z‖ ‖pz‖ with hm
      have hm1 : m < 1 := max_lt (hκz.trans_lt hk1) hpz1
      have hm0 : 0 ≤ m := le_max_of_le_left (norm_nonneg _)
      have h := ahQ_pseudo_bound hm0 hm1 (le_max_left _ _) (le_max_right _ _)
      rw [← h35_pd_b_norm_conj_denom] at h
      refine lt_of_le_of_lt h ?_
      rw [div_lt_one (by positivity)]
      nlinarith [sq_nonneg (1 - m)]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hρI : ρ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hρ1⟩
    -- `d(κ, pz) = artanh ρ ≤ artanh k - δ = artanh c`
    have hd := h35_pt_hyp hk1 hκz hνz hC htpos.le ht1 hpz' htA
    have hdρ : h35_pd_discPoincareDist (κ z) pz = Real.artanh ρ := by
      rw [h35_pd_discPoincareDist, Real.artanh_eq_half_log ⟨by linarith, hρ1.le⟩]
    rw [hdρ] at hd
    have hle : Real.artanh ρ ≤ Real.artanh c := by
      rw [hc, Real.artanh_tanh, hδ]
      linarith
    rw [hρeq]
    exact (Real.artanh_le_artanh_iff hρI hcI).1 hle
  -- transfer to a.e. `w ∈ Δ`, and bound `K[F]`
  have hpt' : ∀ᵐ w ∂(volume.restrict unitDisc), ‖complexDilatation F w‖ ≤ max c 0 := by
    filter_upwards [h35_ae_of_ae_comp (P := fun w => ‖complexDilatation F w‖ ≤ c) hKg hgs hpt]
      with w hw
    exact hw.trans (le_max_left _ _)
  have hc'1 : max c 0 < 1 := max_lt (hcI.2) one_pos
  have hc'k : max c 0 < k := max_lt hck hkpos
  have hKF := m35_maxDilatation_le_of_ae_le ⟨Kg * K₀, hFK⟩ (le_max_right _ _) hc'1 hpt'
  have hK₀ := m35_le_maxDilatation hf₀.1.1
  have hlt' : ENNReal.ofReal ((1 + max c 0) / (1 - max c 0)) < ENNReal.ofReal ((1 + k) / (1 - k)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) (by linarith)),
      div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hext := hf₀.2 F hFb
  have : maxDilatation F unitDisc < maxDilatation f₀ unitDisc :=
    lt_of_le_of_lt hKF (lt_of_lt_of_le hlt' hK₀)
  exact absurd hext (not_le.2 this)

/-- **Theorem 35.5** (a special case of Hamilton's theorem, §36): if `f₀ : Δ → Δ` is extremal for its
boundary values, then its complex dilatation satisfies `H[κ] = ‖κ‖_∞`. -/
theorem thm35_5 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : IsExtremalForBoundary f₀ h) :
    hamiltonH (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀) := by
  exact h35_thm35_5_of_AB h35_duality h35_trivial hf₀

/-- §35.4: `f₀` is extremal for its boundary values iff `H[κ] = ‖κ‖_∞` (Theorems 35.4 and 35.5). -/
theorem extremal_iff_hamilton {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : HasBoundaryValues f₀ h) :
    IsExtremalForBoundary f₀ h ↔ hamiltonH (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀) := by
  exact ⟨thm35_5, thm35_4 hf₀⟩

/-! ## §35.5 Existence of extremal Teichmüller maps -/

/-- §35.5 (Hamilton 序列): a sequence `φₙ` of holomorphic functions with `‖φₙ‖ = 1` and
`∬ κφₙ → ‖κ‖_∞` is a Hamilton sequence for `κ`. -/
def IsHamiltonSequence (κ : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop :=
  (∀ n, φ n ∈ integrableQD ∧ phiArea (φ n) unitDisc = 1) ∧
    Tendsto (fun n => ∫ z in unitDisc, κ z * φ n z) atTop (𝓝 (beltramiNormDisc κ : ℂ))

/-- §35.5 (退化的 Hamilton 序列): a Hamilton sequence converging to `0` uniformly on compact subsets
of `Δ`. -/
def IsDegenerateHamiltonSequence (κ : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop :=
  IsHamiltonSequence κ φ ∧ TendstoLocallyUniformlyOn φ 0 atTop unitDisc

/-- §35.5 (边界对应的最大伸缩商): the boundary dilatation `H` of `h`: the infimum of `K[h̃]` over all
quasiconformal extensions `h̃` of `h` to annuli `B_r = {r < |z| < 1}`, `0 < r < 1`. -/
def boundaryDilatation (h : ExtPlane → ExtPlane) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (g : ℂ → ℂ) (_ : 0 < r ∧ r < 1 ∧ IsQuasiconformal g (annulus r 1) ∧ g '' annulus r 1 ⊆ unitDisc ∧
      ∃ G : ExtPlane → ExtPlane, IsHomeoExtension g (annulus r 1) (g '' annulus r 1) G ∧
        ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ = h ζ),
    maxDilatation g (annulus r 1)

/-! ### Helpers for `annulus_extension_extends` (`h35c_`): measurable Riemann mapping, reflection, cone fill-in -/

/-- `exp` maps the strip `log ρ₀ < Re ζ < -log ρ₀` into the annulus `ρ₀ < |z| < 1/ρ₀`. -/
theorem h35c_exp_mem_annulus {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ζ : ℂ} (h1 : Real.log ρ₀ < ζ.re)
    (h2 : ζ.re < -Real.log ρ₀) : exp ζ ∈ annulus ρ₀ ρ₀⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [Complex.norm_exp]
    calc ρ₀ = Real.exp (Real.log ρ₀) := (Real.exp_log hρ₀).symm
      _ < Real.exp ζ.re := Real.exp_lt_exp.2 h1
  · rw [Complex.norm_exp]
    calc Real.exp ζ.re < Real.exp (-Real.log ρ₀) := Real.exp_lt_exp.2 h2
      _ = ρ₀⁻¹ := by rw [Real.exp_neg, Real.exp_log hρ₀]

/-- **Logarithm of `τ ∘ exp` on a strip.**  A nonvanishing holomorphic `τ` on the annulus `ρ₀ < |z| < 1/ρ₀` has
`τ ∘ exp = exp ∘ L` on the strip `log ρ₀ < Re ζ < -log ρ₀`, with `L' = e^ζ τ'(e^ζ)/τ(e^ζ)` (a primitive of the
logarithmic derivative on the convex strip, corrected by a constant). -/
theorem h35c_exists_log {τ : ℂ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) (hne : ∀ z ∈ annulus ρ₀ ρ₀⁻¹, τ z ≠ 0) :
    ∃ L : ℂ → ℂ, ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ →
      exp (L ζ) = τ (exp ζ) ∧ HasDerivAt L (exp ζ * deriv τ (exp ζ) / τ (exp ζ)) ζ := by
  set S : Set ℂ := {ζ : ℂ | Real.log ρ₀ < ζ.re ∧ ζ.re < -Real.log ρ₀} with hSdef
  have hlog : Real.log ρ₀ < 0 := Real.log_neg hρ₀ hρ₀1
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hSconv : Convex ℝ S := by
    have h1 : Convex ℝ {ζ : ℂ | Real.log ρ₀ < ζ.re} := convex_halfSpace_re_gt _
    have h2 : Convex ℝ {ζ : ℂ | ζ.re < -Real.log ρ₀} := convex_halfSpace_re_lt _
    exact h1.inter h2
  have h0S : (0 : ℂ) ∈ S := ⟨by simpa using hlog, by simpa using hlog⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hSc : IsConnected S := ⟨hSne, hSconv.isPreconnected⟩
  have : ContractibleSpace ↥S := hSconv.contractibleSpace hSne
  have : SimplyConnectedSpace ↥S := SimplyConnectedSpace.ofContractible _
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hmaps : MapsTo exp S (annulus ρ₀ ρ₀⁻¹) := fun ζ hζ => h35c_exp_mem_annulus hρ₀ hζ.1 hζ.2
  have hτe : DifferentiableOn ℂ (fun ζ => τ (exp ζ)) S :=
    hd.comp differentiable_exp.differentiableOn hmaps
  have hτ'e : DifferentiableOn ℂ (fun ζ => deriv τ (exp ζ)) S :=
    (hd.deriv hA).comp differentiable_exp.differentiableOn hmaps
  have hQd : DifferentiableOn ℂ (fun ζ => exp ζ * deriv τ (exp ζ) / τ (exp ζ)) S :=
    (differentiable_exp.differentiableOn.mul hτ'e).div hτe fun ζ hζ => hne _ (hmaps hζ)
  obtain ⟨P, hP, hP'⟩ := RMT.exists_primitive_of_simplyConnected hSo hSc hQd
  have hPat : ∀ ζ ∈ S, HasDerivAt P (exp ζ * deriv τ (exp ζ) / τ (exp ζ)) ζ := fun ζ hζ => by
    rw [← hP' ζ hζ]
    exact (hP.differentiableAt (hSo.mem_nhds hζ)).hasDerivAt
  -- `E = τ ∘ exp · exp (-P)` is constant on `S`
  set E : ℂ → ℂ := fun ζ => τ (exp ζ) * exp (-P ζ) with hEdef
  have hEat : ∀ ζ ∈ S, HasDerivAt E 0 ζ := fun ζ hζ => by
    have hτd : HasDerivAt τ (deriv τ (exp ζ)) (exp ζ) :=
      (hd.differentiableAt (hA.mem_nhds (hmaps hζ))).hasDerivAt
    have h1 : HasDerivAt (fun ζ => τ (exp ζ)) (deriv τ (exp ζ) * exp ζ) ζ :=
      hτd.comp ζ (hasDerivAt_exp ζ)
    have h2 : HasDerivAt (fun ζ => exp (-P ζ)) (exp (-P ζ) * -(exp ζ * deriv τ (exp ζ) / τ (exp ζ))) ζ :=
      (hPat ζ hζ).neg.cexp
    have h3 := h1.mul h2
    convert h3 using 1
    have hne' := hne _ (hmaps hζ)
    field_simp
    ring
  have hEd : DifferentiableOn ℂ E S := fun ζ hζ => (hEat ζ hζ).differentiableAt.differentiableWithinAt
  have hEc : ∀ ζ ∈ S, E ζ = E 0 := fun ζ hζ =>
    hSo.is_const_of_deriv_eq_zero hSconv.isPreconnected hEd (fun x hx => (hEat x hx).deriv) hζ h0S
  have hc : E 0 ≠ 0 := by
    simp only [hEdef]
    exact mul_ne_zero (hne _ (hmaps h0S)) (exp_ne_zero _)
  refine ⟨fun ζ => P ζ + log (E 0), fun ζ h1 h2 => ⟨?_, (hPat ζ ⟨h1, h2⟩).add_const _⟩⟩
  have hE := hEc ζ ⟨h1, h2⟩
  rw [exp_add, exp_log hc, ← hE, hEdef]
  simp only [exp_neg]
  field_simp

/-- A function with a left local maximum at `a` has nonnegative derivative there. -/
theorem h35c_deriv_nonneg_of_left {f : ℝ → ℝ} {f' a b : ℝ} (hab : b < a) (hf : HasDerivAt f f' a)
    (hlt : ∀ x ∈ Ioo b a, f x ≤ f a) : 0 ≤ f' := by
  have ht : Tendsto (slope f a) (𝓝[<] a) (𝓝 f') :=
    (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsLT_le_nhdsNE a)
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (by linarith [hlt x hx]) (by linarith [hx.2])

/-- **The logarithmic derivative is positive on the circle.**  If `τ` is holomorphic and injective near the unit
circle, maps it into itself and the inside collar into the disc, then `L'(iθ) = e^{iθ} τ'(e^{iθ})/τ(e^{iθ})` is a
positive real number: it is real because `Re L = log |τ ∘ exp| = 0` on the imaginary axis, nonnegative because
`Re L < 0` to its left, and nonzero because `τ' ≠ 0`. -/
theorem h35c_q_pos {τ : ℂ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) (hi : InjOn τ (annulus ρ₀ ρ₀⁻¹))
    (hne : ∀ z ∈ annulus ρ₀ ρ₀⁻¹, τ z ≠ 0) (hin : ∀ z : ℂ, ρ₀ < ‖z‖ → ‖z‖ < 1 → ‖τ z‖ < 1)
    (hon : ∀ z : ℂ, ‖z‖ = 1 → ‖τ z‖ = 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 < (z * deriv τ z / τ z).re := by
  obtain ⟨L, hL⟩ := h35c_exists_log hρ₀ hρ₀1 hd hne
  have hlog : Real.log ρ₀ < 0 := Real.log_neg hρ₀ hρ₀1
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  set θ : ℝ := arg z with hθ
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have hze : exp (θ * I) = z := by
    have h := exp_log hz0
    rwa [Complex.log, hz, Real.log_one, ofReal_zero, zero_add] at h
  have hzA : z ∈ annulus ρ₀ ρ₀⁻¹ := ⟨by rw [hz]; exact hρ₀1, by rw [hz]; exact one_lt_inv₀ hρ₀ |>.2 hρ₀1⟩
  set Q : ℂ := z * deriv τ z / τ z with hQ
  -- `L` on the imaginary axis has real part `0`
  have hre0 : ∀ t : ℝ, (L (t * I)).re = 0 := fun t => by
    have h := (hL (t * I) (by simpa using hlog) (by simpa using hlog)).1
    have hn : ‖exp (L (t * I))‖ = 1 := by rw [h, hon _ (norm_exp_ofReal_mul_I t)]
    rw [Complex.norm_exp] at hn
    exact Real.exp_eq_one_iff _ |>.1 hn
  have hLθ : HasDerivAt L Q (θ * I) := by
    have h := (hL (θ * I) (by simpa using hlog) (by simpa using hlog)).2
    rwa [hze] at h
  -- `Q` is real
  have him : Q.im = 0 := by
    have h1 : HasDerivAt (fun w : ℂ => L (w * I)) (Q * I) (θ : ℂ) :=
      hLθ.comp (θ : ℂ) (hasDerivAt_mul_const I)
    have h2 := h1.real_of_complex
    have h3 : (fun x : ℝ => (L (x * I)).re) = fun _ => 0 := funext hre0
    rw [h3] at h2
    have h4 := h2.unique (hasDerivAt_const (θ : ℝ) (0 : ℝ))
    simpa using h4
  -- `Q` has nonnegative real part
  have hre : 0 ≤ Q.re := by
    have h1 : HasDerivAt (fun w : ℂ => L (w + θ * I)) Q ((0 : ℝ) : ℂ) := by
      have h0 : HasDerivAt L Q (((0 : ℝ) : ℂ) + θ * I) := by simpa using hLθ
      exact h0.comp_add_const _ _
    have h2 := h1.real_of_complex
    refine h35c_deriv_nonneg_of_left hlog h2 fun x hx => ?_
    simp only [ofReal_zero, zero_add, hre0 θ]
    have hmem : Real.log ρ₀ < ((x : ℂ) + θ * I).re := by simpa using hx.1
    have hmem' : ((x : ℂ) + θ * I).re < -Real.log ρ₀ := by simp; linarith [hx.2]
    have h := (hL _ hmem hmem').1
    have hn1 : ‖exp ((x : ℂ) + θ * I)‖ = Real.exp x := by rw [Complex.norm_exp]; simp
    have hlt : ‖τ (exp ((x : ℂ) + θ * I))‖ < 1 := by
      refine hin _ ?_ ?_
      · rw [hn1]
        calc ρ₀ = Real.exp (Real.log ρ₀) := (Real.exp_log hρ₀).symm
          _ < Real.exp x := Real.exp_lt_exp.2 hx.1
      · rw [hn1]
        exact Real.exp_lt_one_iff.2 hx.2
    rw [← h, Complex.norm_exp] at hlt
    exact (Real.exp_lt_one_iff.1 hlt).le
  -- `Q ≠ 0`
  have hQ0 : Q ≠ 0 := by
    rw [hQ]
    exact div_ne_zero (mul_ne_zero hz0 (deriv_ne_zero_of_injOn hA hd hi hzA)) (hne z hzA)
  rcases hre.lt_or_eq with h | h
  · exact h
  · exact absurd (Complex.ext h.symm him) hQ0

/-- **Choice of the cone radius.**  A continuous `q` on the annulus `ρ₀ < |z| < 1/ρ₀` with `Re q > 0` on the unit
circle has `Re q > 0` on a closed collar `ρ ≤ |z| ≤ 1` (compactness of the circle). -/
theorem h35c_choose_rho {q : ℂ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hq : ContinuousOn q (annulus ρ₀ ρ₀⁻¹)) (hpos : ∀ z : ℂ, ‖z‖ = 1 → 0 < (q z).re) :
    ∃ ρ : ℝ, ρ₀ < ρ ∧ ρ < 1 ∧ ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → 0 < (q z).re := by
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hU : IsOpen (annulus ρ₀ ρ₀⁻¹ ∩ q ⁻¹' {w : ℂ | 0 < w.re}) :=
    hq.isOpen_inter_preimage hA (isOpen_lt continuous_const continuous_re)
  have hsub : sphere (0 : ℂ) 1 ⊆ annulus ρ₀ ρ₀⁻¹ ∩ q ⁻¹' {w : ℂ | 0 < w.re} := fun z hz => by
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    exact ⟨⟨by rw [hz1]; exact hρ₀1, by rw [hz1]; exact (one_lt_inv₀ hρ₀).2 hρ₀1⟩, hpos z hz1⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hU hsub
  refine ⟨max ((ρ₀ + 1) / 2) (1 - δ / 2), lt_max_of_lt_left (by linarith),
    max_lt (by linarith) (by linarith), fun z hz1 hz2 => ?_⟩
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (lt_max_of_lt_left (by linarith)) hz1
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hmem : z ∈ thickening δ (sphere (0 : ℂ) 1) := by
    rw [mem_thickening_iff]
    refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self hzpos.ne']
    · rw [dist_eq_norm]
      have hc : z - z / (‖z‖ : ℂ) = ((1 - 1 / ‖z‖ : ℝ) : ℂ) * z := by
        push_cast
        field_simp
      rw [hc, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · have hle : max ((ρ₀ + 1) / 2) (1 - δ / 2) ≥ 1 - δ / 2 := le_max_right _ _
        have h1 : -(1 - 1 / ‖z‖) * ‖z‖ = 1 - ‖z‖ := by field_simp; ring
        rw [h1]
        linarith
      · have : 1 ≤ 1 / ‖z‖ := by rw [le_div_iff₀ hzpos]; linarith
        linarith
  exact (hδU hmem).2

/-- **Noshiro–Warschawski on a strip.**  If `Re L' > 0` on the closed strip `a ≤ Re ζ ≤ 0`, then
`Re (conj (ζ₂ - ζ₁) (L ζ₂ - L ζ₁)) > 0` for distinct `ζ₁, ζ₂` in it (mean value theorem along the segment). -/
theorem h35c_nw {L L' : ℂ → ℂ} {a : ℝ}
    (hL : ∀ ζ : ℂ, a ≤ ζ.re → ζ.re ≤ 0 → HasDerivAt L (L' ζ) ζ)
    (hpos : ∀ ζ : ℂ, a ≤ ζ.re → ζ.re ≤ 0 → 0 < (L' ζ).re) {ζ₁ ζ₂ : ℂ} (h1 : a ≤ ζ₁.re)
    (h1' : ζ₁.re ≤ 0) (h2 : a ≤ ζ₂.re) (h2' : ζ₂.re ≤ 0) (hne : ζ₁ ≠ ζ₂) :
    0 < (conj (ζ₂ - ζ₁) * (L ζ₂ - L ζ₁)).re := by
  set w : ℂ := ζ₂ - ζ₁ with hw
  have hw0 : w ≠ 0 := sub_ne_zero.2 hne.symm
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → a ≤ (ζ₁ + t * w).re ∧ (ζ₁ + t * w).re ≤ 0 := by
    intro t ht
    have hre : (ζ₁ + t * w).re = (1 - t) * ζ₁.re + t * ζ₂.re := by
      simp [hw]; ring
    rw [hre]
    constructor <;> nlinarith [ht.1, ht.2]
  set ψ : ℝ → ℝ := fun t => (conj w * L (ζ₁ + t * w)).re with hψ
  set ψ' : ℝ → ℝ := fun t => (conj w * (L' (ζ₁ + t * w) * w)).re with hψ'
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have hLt := hL _ (hseg t ht).1 (hseg t ht).2
    have h1 : HasDerivAt (fun s : ℂ => ζ₁ + s * w) w (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const w).const_add ζ₁
    have h2 : HasDerivAt (fun s : ℂ => conj w * L (ζ₁ + s * w)) (conj w * (L' (ζ₁ + t * w) * w)) (t : ℂ) :=
      (hLt.comp (t : ℂ) h1).const_mul _
    exact h2.real_of_complex
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope ψ ψ' zero_lt_one
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t (Ioo_subset_Icc_self ht))
  have hpc : 0 < ψ' c := by
    have hc' : conj w * (L' (ζ₁ + c * w) * w) = (normSq w : ℂ) * L' (ζ₁ + c * w) := by
      rw [← mul_conj w]; ring
    simp only [hψ', hc', re_ofReal_mul]
    exact mul_pos (normSq_pos.2 hw0) (hpos _ (hseg c (Ioo_subset_Icc_self hc)).1
      (hseg c (Ioo_subset_Icc_self hc)).2)
  rw [hc', sub_zero, div_one] at hpc
  have h0 : ψ 0 = (conj w * L ζ₁).re := by simp [hψ]
  have h1e : ψ 1 = (conj w * L ζ₂).re := by simp [hψ, hw]
  rw [h0, h1e] at hpc
  rw [mul_sub, sub_re]
  exact sub_pos.2 (by linarith)

/-- On the imaginary axis the logarithm `L` of `τ ∘ exp` has real part `0` when `|τ| = 1` on the circle. -/
theorem h35c_re_L_axis {τ L : ℂ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hL : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ → exp (L ζ) = τ (exp ζ))
    (hon : ∀ z : ℂ, ‖z‖ = 1 → ‖τ z‖ = 1) (t : ℝ) : (L (t * I)).re = 0 := by
  have hlog : Real.log ρ₀ < 0 := Real.log_neg hρ₀ hρ₀1
  have h := hL (t * I) (by simpa using hlog) (by simpa using hlog)
  have hn : ‖exp (L (t * I))‖ = 1 := by rw [h, hon _ (norm_exp_ofReal_mul_I t)]
  rw [Complex.norm_exp] at hn
  exact Real.exp_eq_one_iff _ |>.1 hn

/-- **Degree one.**  The logarithm `L` of `τ ∘ exp` satisfies `L (ζ + 2πi) = L ζ + 2πi`: the jump is a constant
`2πin` (its derivative vanishes); `n > 0` by Noshiro–Warschawski, and `n ≥ 2` would make `τ` take the value `τ 1`
twice on the circle (intermediate value theorem for `Im L` on the imaginary axis). -/
theorem h35c_period {τ L : ℂ → ℂ} {ρ₀ u : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) (hu0 : u ≤ 0)
    (hL : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ →
      exp (L ζ) = τ (exp ζ) ∧ HasDerivAt L (exp ζ * deriv τ (exp ζ) / τ (exp ζ)) ζ)
    (hi : InjOn τ (annulus ρ₀ ρ₀⁻¹)) (hon : ∀ z : ℂ, ‖z‖ = 1 → ‖τ z‖ = 1)
    (hnw : ∀ ζ₁ ζ₂ : ℂ, u ≤ ζ₁.re → ζ₁.re ≤ 0 → u ≤ ζ₂.re → ζ₂.re ≤ 0 → ζ₁ ≠ ζ₂ →
      0 < (conj (ζ₂ - ζ₁) * (L ζ₂ - L ζ₁)).re) {ζ : ℂ} (hζ1 : Real.log ρ₀ < ζ.re)
    (hζ2 : ζ.re < -Real.log ρ₀) : L (ζ + 2 * π * I) = L ζ + 2 * π * I := by
  set S : Set ℂ := {ζ : ℂ | Real.log ρ₀ < ζ.re ∧ ζ.re < -Real.log ρ₀} with hSdef
  have hlog : Real.log ρ₀ < 0 := Real.log_neg hρ₀ hρ₀1
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hSconv : Convex ℝ S := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have h0S : (0 : ℂ) ∈ S := ⟨by simpa using hlog, by simpa using hlog⟩
  have hre2 : (2 * (π : ℂ) * I).re = 0 := by simp
  have hshift : ∀ ζ ∈ S, ζ + 2 * π * I ∈ S := fun ζ hζ => by
    refine ⟨?_, ?_⟩ <;> rw [add_re, hre2, add_zero]
    exacts [hζ.1, hζ.2]
  set D : ℂ → ℂ := fun ζ => L (ζ + 2 * π * I) - L ζ with hDdef
  have hDat : ∀ ζ ∈ S, HasDerivAt D 0 ζ := fun ζ hζ => by
    have h1 := (hL _ (hshift ζ hζ).1 (hshift ζ hζ).2).2
    rw [exp_periodic ζ] at h1
    have h2 := (hL _ hζ.1 hζ.2).2
    have h3 := (h1.comp_add_const ζ (2 * π * I)).sub h2
    rwa [sub_self] at h3
  have hDd : DifferentiableOn ℂ D S := fun ζ hζ => (hDat ζ hζ).differentiableAt.differentiableWithinAt
  have hDc : ∀ ζ ∈ S, D ζ = D 0 := fun ζ hζ =>
    hSo.is_const_of_deriv_eq_zero hSconv.isPreconnected hDd (fun x hx => (hDat x hx).deriv) hζ h0S
  -- `D 0 = 2πin`
  have hτ1 : τ 1 ≠ 0 := by
    intro h
    have := hon 1 norm_one
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hexpD : exp (D 0) = 1 := by
    have e1 := (hL _ (hshift 0 h0S).1 (hshift 0 h0S).2).1
    have e0 := (hL 0 h0S.1 h0S.2).1
    rw [hDdef]
    simp only [exp_sub, e1, e0, exp_periodic 0, exp_zero, div_self hτ1]
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 hexpD
  have hL2 : L (2 * π * I) = L 0 + n * (2 * π * I) := by
    have : D 0 = L (2 * π * I) - L 0 := by simp [hDdef]
    rw [this] at hn
    linear_combination hn
  -- `n > 0`
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hn0 : 0 < n := by
    have h2piI : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have h := hnw 0 (2 * π * I) (by simpa using hu0) (by simp) (by rw [hre2]; exact hu0)
      (le_of_eq hre2) (Ne.symm h2piI)
    rw [hL2] at h
    have hcalc : (conj (2 * π * I - 0) * (L 0 + n * (2 * π * I) - L 0)).re = 4 * π ^ 2 * n := by
      simp [Complex.conj_ofReal]
      ring
    rw [hcalc] at h
    have : (0 : ℝ) < n := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith [sq_nonneg π]
    exact_mod_cast this
  -- `n < 2`
  have hn1 : n = 1 := by
    by_contra hne1
    have hn2 : 2 ≤ n := by omega
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    set Y : ℝ → ℝ := fun t => (L (t * I)).im with hY
    have hLat : ∀ t : ℝ, ContinuousAt L (t * I) := fun t =>
      (hL (t * I) (by simpa using hlog) (by simpa using hlog)).2.continuousAt
    have hYc : ContinuousOn Y (Icc 0 (2 * π)) := fun t _ => by
      have h1 : ContinuousAt (fun s : ℝ => (s : ℂ) * I) t := by fun_prop
      have h2 : ContinuousAt (fun s : ℝ => L ((s : ℂ) * I)) t := ContinuousAt.comp (g := L) (hLat t) h1
      exact (continuous_im.continuousAt.comp h2).continuousWithinAt
    have hY2 : Y (2 * π) = Y 0 + 2 * π * n := by
      simp only [hY]
      have : ((2 * π : ℝ) : ℂ) * I = 2 * π * I := by push_cast; ring
      rw [this, hL2]
      simp
      ring
    have hmem : Y 0 + 2 * π ∈ Icc (Y 0) (Y (2 * π)) := by
      rw [hY2]
      constructor <;> nlinarith
    obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc (by positivity) hYc hmem
    have hre0 := h35c_re_L_axis hρ₀ hρ₀1 (fun ζ h1 h2 => (hL ζ h1 h2).1) hon
    have hLt : L (t * I) = L ((0 : ℝ) * I) + 2 * π * I := by
      apply Complex.ext
      · simp only [add_re, hre0, hre2, add_zero]
      · simp only [hY] at hYt
        simp [hYt]
    have hτeq : τ (exp (t * I)) = τ (exp ((0 : ℝ) * I)) := by
      rw [← (hL _ (by simpa using hlog) (by simpa using hlog)).1,
        ← (hL _ (by simpa using hlog) (by simpa using hlog)).1, hLt, exp_periodic]
    have hmemA : ∀ s : ℝ, exp (s * I) ∈ annulus ρ₀ ρ₀⁻¹ := fun s => by
      refine ⟨?_, ?_⟩ <;> rw [norm_exp_ofReal_mul_I]
      exacts [hρ₀1, (one_lt_inv₀ hρ₀).2 hρ₀1]
    have heq := hi (hmemA t) (hmemA 0) hτeq
    rw [ofReal_zero, zero_mul, exp_zero] at heq
    obtain ⟨m, hm⟩ := exp_eq_one_iff.1 heq
    have htm : t = 2 * π * m := by
      have := congrArg Complex.im hm
      simp at this
      linarith
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0] at hYt
      linarith
    have ht2 : t ≠ 2 * π := by
      intro h2
      rw [h2, hY2] at hYt
      have : (n : ℝ) = 1 := by
        have := hpi
        nlinarith
      exact hne1 (by exact_mod_cast this)
    have hm0 : (0 : ℝ) < m := by
      have : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [htm] at this
      nlinarith
    have hm1 : (m : ℝ) < 1 := by
      have : t < 2 * π := lt_of_le_of_ne ht.2 ht2
      rw [htm] at this
      nlinarith
    have hm0' : 0 < m := by exact_mod_cast hm0
    have hm1' : m < 1 := by exact_mod_cast hm1
    omega
  have h := hDc ζ ⟨hζ1, hζ2⟩
  rw [hn, hn1] at h
  simp only [hDdef, Int.cast_one, one_mul] at h
  linear_combination h

/-- The cone fill-in in logarithmic coordinates `ζ = log z`: the log-lift `L` of `τ ∘ exp` for `Re ζ > u`, and the
translate `(Re ζ - u) + L (u + i Im ζ)` of its values on the line `Re ζ = u` for `Re ζ ≤ u`. -/
def h35c_M (L : ℂ → ℂ) (u : ℝ) (ζ : ℂ) : ℂ :=
  if ζ.re ≤ u then ((ζ.re - u : ℝ) : ℂ) + L ((u : ℂ) + (ζ.im : ℂ) * I) else L ζ

/-- **Injectivity of the logarithmic cone fill-in** on the half-plane `Re ζ ≤ 0`, from the Noshiro–Warschawski
inequality on the closed strip `u ≤ Re ζ ≤ 0`. -/
theorem h35c_M_inj {L : ℂ → ℂ} {u : ℝ} (hu : u ≤ 0)
    (hnw : ∀ ζ₁ ζ₂ : ℂ, u ≤ ζ₁.re → ζ₁.re ≤ 0 → u ≤ ζ₂.re → ζ₂.re ≤ 0 → ζ₁ ≠ ζ₂ →
      0 < (conj (ζ₂ - ζ₁) * (L ζ₂ - L ζ₁)).re) {ζ₁ ζ₂ : ℂ} (h1 : ζ₁.re ≤ 0) (h2 : ζ₂.re ≤ 0)
    (heq : h35c_M L u ζ₁ = h35c_M L u ζ₂) : ζ₁ = ζ₂ := by
  by_contra hne
  unfold h35c_M at heq
  split_ifs at heq with ha hb hb
  · by_cases hy : ζ₁.im = ζ₂.im
    · rw [hy] at heq
      have hre : ζ₁.re = ζ₂.re := by
        have := congrArg Complex.re (add_right_cancel heq)
        simp at this
        linarith
      exact hne (Complex.ext hre hy)
    · have hw : (u : ℂ) + (ζ₁.im : ℂ) * I ≠ (u : ℂ) + (ζ₂.im : ℂ) * I := by
        intro h
        apply hy
        have := congrArg Complex.im h
        simpa using this
      have h := hnw _ _ (by simp) (by simpa using hu) (by simp) (by simpa using hu) hw
      have hdiff : L ((u : ℂ) + (ζ₂.im : ℂ) * I) - L ((u : ℂ) + (ζ₁.im : ℂ) * I) =
          ((ζ₁.re - u : ℝ) : ℂ) - ((ζ₂.re - u : ℝ) : ℂ) := by linear_combination -heq
      rw [hdiff] at h
      simp at h
  · have hw : (u : ℂ) + (ζ₁.im : ℂ) * I ≠ ζ₂ := by
      intro h
      apply hb
      rw [← h]
      simp
    have hb' : u < ζ₂.re := lt_of_not_ge hb
    have h := hnw _ _ (by simp) (by simpa using hu) hb'.le h2 hw
    have hdiff : L ζ₂ - L ((u : ℂ) + (ζ₁.im : ℂ) * I) = ((ζ₁.re - u : ℝ) : ℂ) := by
      linear_combination -heq
    rw [hdiff] at h
    simp at h
    nlinarith
  · have hw : (u : ℂ) + (ζ₂.im : ℂ) * I ≠ ζ₁ := by
      intro h
      apply ha
      rw [← h]
      simp
    have ha' : u < ζ₁.re := lt_of_not_ge ha
    have h := hnw _ _ (by simp) (by simpa using hu) ha'.le h1 hw
    have hdiff : L ζ₁ - L ((u : ℂ) + (ζ₂.im : ℂ) * I) = ((ζ₂.re - u : ℝ) : ℂ) := by
      linear_combination heq
    rw [hdiff] at h
    simp at h
    nlinarith
  · have h := hnw _ _ (le_of_lt (lt_of_not_ge ha)) h1 (le_of_lt (lt_of_not_ge hb)) h2 hne
    rw [heq, sub_self, mul_zero, zero_re] at h
    exact lt_irrefl _ h

/-- The cone fill-in of `τ` inside the circle `|z| = ρ`: `z ↦ (|z|/ρ) τ(ρ z/|z|)` for `|z| ≤ ρ`, and `τ` outside. -/
def h35c_cone (τ : ℂ → ℂ) (ρ : ℝ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ ρ then ((‖z‖ / ρ : ℝ) : ℂ) * τ (((ρ / ‖z‖ : ℝ) : ℂ) * z) else τ z

/-- In logarithmic coordinates the cone fill-in is `exp ∘ h35c_M`. -/
theorem h35c_cone_exp {τ L : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hL : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ → exp (L ζ) = τ (exp ζ)) {ζ : ℂ}
    (hζ : ζ.re ≤ 0) : h35c_cone τ ρ (exp ζ) = exp (h35c_M L (Real.log ρ) ζ) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hlog0 : Real.log ρ₀ < 0 := Real.log_neg hρ₀ (hρ₀ρ.trans hρ1)
  have hlogρ : Real.log ρ₀ < Real.log ρ := Real.log_lt_log hρ₀ hρ₀ρ
  have hlogρ0 : Real.log ρ < 0 := Real.log_neg hρ hρ1
  have hn : ‖exp ζ‖ = Real.exp ζ.re := Complex.norm_exp ζ
  unfold h35c_cone h35c_M
  by_cases h : ζ.re ≤ Real.log ρ
  · have hle : ‖exp ζ‖ ≤ ρ := by
      rw [hn]
      calc Real.exp ζ.re ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.2 h
        _ = ρ := Real.exp_log hρ
    rw [ite_eq_left hle, ite_eq_left h, exp_add, (hL _ (by simpa using hlogρ) (by simp; linarith)), hn]
    have hζe : exp ζ = ((Real.exp ζ.re : ℝ) : ℂ) * exp ((ζ.im : ℂ) * I) := by
      rw [ofReal_exp, ← exp_add, Complex.re_add_im]
    have hpt : (((ρ / Real.exp ζ.re : ℝ)) : ℂ) * exp ζ = exp ((Real.log ρ : ℂ) + (ζ.im : ℂ) * I) := by
      rw [hζe, exp_add, ← ofReal_exp, Real.exp_log hρ]
      have : Real.exp ζ.re ≠ 0 := (Real.exp_pos _).ne'
      push_cast
      field_simp
    rw [hpt, ← ofReal_exp, Real.exp_sub, Real.exp_log hρ]
  · have hlt : ¬ ‖exp ζ‖ ≤ ρ := by
      rw [hn, not_le]
      calc ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
        _ < Real.exp ζ.re := Real.exp_lt_exp.2 (lt_of_not_ge h)
    rw [ite_eq_right hlt, ite_eq_right h, hL _ (by linarith [lt_of_not_ge h]) (by linarith)]

/-- Iterating `L (ζ + 2πi) = L ζ + 2πi` along the strip. -/
theorem h35c_L_int_period {L : ℂ → ℂ} {a b : ℝ}
    (hper : ∀ ζ : ℂ, a < ζ.re → ζ.re < b → L (ζ + 2 * π * I) = L ζ + 2 * π * I) (k : ℤ) {ζ : ℂ}
    (h1 : a < ζ.re) (h2 : ζ.re < b) : L (ζ + k * (2 * π * I)) = L ζ + k * (2 * π * I) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih ⊢
    have e : ζ + ((n : ℂ) + 1) * (2 * π * I) = (ζ + (n : ℂ) * (2 * π * I)) + 2 * π * I := by ring
    have hre' : (ζ + (n : ℂ) * (2 * π * I)).re = ζ.re := by simp
    rw [e, hper _ (by rw [hre']; exact h1) (by rw [hre']; exact h2), ih]
    ring
  | pred n ih =>
    push_cast at ih ⊢
    have hre' : (ζ + (-(n : ℂ) - 1) * (2 * π * I)).re = ζ.re := by simp
    have h := hper (ζ + (-(n : ℂ) - 1) * (2 * π * I)) (by rw [hre']; exact h1) (by rw [hre']; exact h2)
    have e : ζ + (-(n : ℂ) - 1) * (2 * π * I) + 2 * π * I = ζ + -(n : ℂ) * (2 * π * I) := by ring
    rw [e, ih] at h
    linear_combination -h

/-- The logarithmic cone fill-in commutes with the translations `ζ ↦ ζ + 2πik`. -/
theorem h35c_M_shift {L : ℂ → ℂ} {a u : ℝ} (hau : a < u) (hu : u ≤ 0)
    (hper : ∀ ζ : ℂ, a < ζ.re → ζ.re < -a → L (ζ + 2 * π * I) = L ζ + 2 * π * I) (k : ℤ) {ζ : ℂ}
    (hζ : ζ.re ≤ 0) : h35c_M L u (ζ + k * (2 * π * I)) = h35c_M L u ζ + k * (2 * π * I) := by
  have ha : a < 0 := hau.trans_le hu
  have hre : (ζ + k * (2 * π * I)).re = ζ.re := by simp
  have him : (ζ + k * (2 * π * I)).im = ζ.im + 2 * π * k := by simp; ring
  unfold h35c_M
  rw [hre]
  split_ifs with h
  · have e : (u : ℂ) + ((ζ.im + 2 * π * k : ℝ) : ℂ) * I = ((u : ℂ) + (ζ.im : ℂ) * I) + k * (2 * π * I) := by
      push_cast; ring
    rw [him, e, h35c_L_int_period hper k (by simpa using hau) (by simp; linarith)]
    ring
  · exact h35c_L_int_period hper k (by linarith [lt_of_not_ge h]) (by linarith)

/-- The cone fill-in vanishes at the origin. -/
theorem h35c_cone_zero (τ : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : h35c_cone τ ρ 0 = 0 := by
  unfold h35c_cone
  rw [ite_eq_left (by simpa using hρ.le)]
  simp

/-- The cone fill-in agrees with `τ` outside the circle `|z| = ρ`. -/
theorem h35c_cone_eq_of_lt (τ : ℂ → ℂ) {ρ : ℝ} {z : ℂ} (hz : ρ < ‖z‖) : h35c_cone τ ρ z = τ z := by
  unfold h35c_cone
  rw [ite_eq_right (not_le.2 hz)]

/-- **Injectivity of the cone fill-in** on the closed disc. -/
theorem h35c_cone_injOn {τ L : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hL : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ → exp (L ζ) = τ (exp ζ))
    (hper : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ → L (ζ + 2 * π * I) = L ζ + 2 * π * I)
    (hnw : ∀ ζ₁ ζ₂ : ℂ, Real.log ρ ≤ ζ₁.re → ζ₁.re ≤ 0 → Real.log ρ ≤ ζ₂.re → ζ₂.re ≤ 0 → ζ₁ ≠ ζ₂ →
      0 < (conj (ζ₂ - ζ₁) * (L ζ₂ - L ζ₁)).re) :
    InjOn (h35c_cone τ ρ) (closedBall 0 1) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hlogρ : Real.log ρ₀ < Real.log ρ := Real.log_lt_log hρ₀ hρ₀ρ
  have hlogρ0 : Real.log ρ ≤ 0 := (Real.log_neg hρ hρ1).le
  have hlogre : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) 1 → (log z).re ≤ 0 := fun z hz => by
    rw [log_re]
    exact Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 hz)
  have hval : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) 1 → z ≠ 0 →
      h35c_cone τ ρ z = exp (h35c_M L (Real.log ρ) (log z)) := fun z hz hz0 => by
    rw [← h35c_cone_exp hρ₀ hρ₀ρ hρ1 hL (hlogre z hz), exp_log hz0]
  intro z₁ hz₁ z₂ hz₂ heq
  by_cases h1 : z₁ = 0
  · by_contra hne
    have h2 : z₂ ≠ 0 := fun h => hne (h1.trans h.symm)
    rw [h1, h35c_cone_zero τ hρ, hval z₂ hz₂ h2] at heq
    exact exp_ne_zero _ heq.symm
  by_cases h2 : z₂ = 0
  · rw [h2, h35c_cone_zero τ hρ, hval z₁ hz₁ h1] at heq
    exact absurd heq (exp_ne_zero _)
  rw [hval z₁ hz₁ h1, hval z₂ hz₂ h2] at heq
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 heq
  rw [← h35c_M_shift hlogρ hlogρ0 hper k (hlogre z₂ hz₂)] at hk
  have hζ := h35c_M_inj hlogρ0 hnw (hlogre z₁ hz₁) (by simpa using hlogre z₂ hz₂) hk
  rw [← exp_log h1, ← exp_log h2, hζ, (exp_periodic.int_mul k) (log z₂)]

/-- The point `ρ z/|z|` lies on the circle `|v| = ρ`. -/
theorem h35c_norm_scale {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : z ≠ 0) : ‖((ρ / ‖z‖ : ℝ) : ℂ) * z‖ = ρ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_mul, norm_real, Real.norm_of_nonneg (div_nonneg hρ hz'.le), div_mul_cancel₀ _ hz'.ne']

/-- **Continuity of the cone fill-in** on the disc `|z| < 1/ρ₀`. -/
theorem h35c_cone_continuousOn {τ : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hc : ContinuousOn τ (annulus ρ₀ ρ₀⁻¹)) (hb : ∀ z : ℂ, ‖z‖ = ρ → ‖τ z‖ ≤ 1) :
    ContinuousOn (h35c_cone τ ρ) (ball 0 ρ₀⁻¹) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρinv : ρ < ρ₀⁻¹ := hρ1.trans ((one_lt_inv₀ hρ₀).2 (hρ₀ρ.trans hρ1))
  have hvA : ∀ z : ℂ, z ≠ 0 → ((ρ / ‖z‖ : ℝ) : ℂ) * z ∈ annulus ρ₀ ρ₀⁻¹ := fun z hz => by
    refine ⟨?_, ?_⟩ <;> rw [h35c_norm_scale hρ.le hz]
    exacts [hρ₀ρ, hρinv]
  unfold h35c_cone
  refine ContinuousOn.if ?_ ?_ ?_
  · intro a ha
    have h := frontier_le_subset_eq continuous_norm continuous_const ha.2
    simp only [Set.mem_ofPred_eq] at h
    rw [h, div_self hρ.ne', ofReal_one, one_mul, one_mul]
  · intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hz0 : z = 0
    · subst hz0
      have hf0 : ((‖(0 : ℂ)‖ / ρ : ℝ) : ℂ) * τ (((ρ / ‖(0 : ℂ)‖ : ℝ) : ℂ) * 0) = 0 := by simp
      rw [ContinuousAt, hf0]
      refine squeeze_zero_norm (a := fun w : ℂ => ‖w‖ / ρ) (fun w => ?_) ?_
      · by_cases hw : w = 0
        · subst hw; simp
        · rw [norm_mul, norm_real, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hρ.le)]
          calc ‖w‖ / ρ * ‖τ (((ρ / ‖w‖ : ℝ) : ℂ) * w)‖ ≤ ‖w‖ / ρ * 1 :=
                mul_le_mul_of_nonneg_left (hb _ (h35c_norm_scale hρ.le hw))
                  (div_nonneg (norm_nonneg _) hρ.le)
            _ = ‖w‖ / ρ := mul_one _
      · have : Continuous fun w : ℂ => ‖w‖ / ρ := continuous_norm.div_const ρ
        simpa using this.tendsto 0
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
      have h1 : ContinuousAt (fun w : ℂ => ((‖w‖ / ρ : ℝ) : ℂ)) z :=
        (continuous_ofReal.comp (continuous_norm.div_const ρ)).continuousAt
      have h2 : ContinuousAt (fun w : ℂ => ((ρ / ‖w‖ : ℝ) : ℂ) * w) z :=
        (continuous_ofReal.continuousAt.comp (continuousAt_const.div continuous_norm.continuousAt hn)).mul
          continuousAt_id
      have h3 : ContinuousAt τ (((ρ / ‖z‖ : ℝ) : ℂ) * z) := hc.continuousAt (hA.mem_nhds (hvA z hz0))
      exact h1.mul (ContinuousAt.comp (g := τ) h3 h2)
  · intro z hz
    have hz' : ρ ≤ ‖z‖ := by
      have h := closure_lt_subset_le continuous_const continuous_norm
        (by simpa only [not_le] using hz.2)
      simpa using h
    have hzA : z ∈ annulus ρ₀ ρ₀⁻¹ := ⟨hρ₀ρ.trans_le hz', mem_ball_zero_iff.1 hz.1⟩
    exact (hc.continuousAt (hA.mem_nhds hzA)).continuousWithinAt

/-- **Smoothness of the cone fill-in** off the origin inside the circle `|z| = ρ`. -/
theorem h35c_cone_contDiffAt {τ : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) {z : ℂ} (hz0 : z ≠ 0) (hzρ : ‖z‖ < ρ) :
    ContDiffAt ℝ 1 (h35c_cone τ ρ) z := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρinv : ρ < ρ₀⁻¹ := hρ1.trans ((one_lt_inv₀ hρ₀).2 (hρ₀ρ.trans hρ1))
  have hvA : ((ρ / ‖z‖ : ℝ) : ℂ) * z ∈ annulus ρ₀ ρ₀⁻¹ := by
    refine ⟨?_, ?_⟩ <;> rw [h35c_norm_scale hρ.le hz0]
    exacts [hρ₀ρ, hρinv]
  have hev : h35c_cone τ ρ =ᶠ[𝓝 z] fun w => ((‖w‖ / ρ : ℝ) : ℂ) * τ (((ρ / ‖w‖ : ℝ) : ℂ) * w) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hzρ] with w hw
    unfold h35c_cone
    exact ite_eq_left (le_of_lt hw)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hn : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℂ hz0
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  have h1 : ContDiffAt ℝ 1 (fun w : ℂ => ((‖w‖ / ρ : ℝ) : ℂ)) z :=
    ofRealCLM.contDiff.contDiffAt.comp z (hn.div_const ρ)
  have h2 : ContDiffAt ℝ 1 (fun w : ℂ => ((ρ / ‖w‖ : ℝ) : ℂ) * w) z :=
    (ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.div hn hn0)).mul contDiffAt_id
  have h3 : ContDiffAt ℝ 1 τ (((ρ / ‖z‖ : ℝ) : ℂ) * z) :=
    ((hd.contDiffOn hA).contDiffAt (hA.mem_nhds hvA)).restrict_scalars ℝ
  exact h1.mul (ContDiffAt.comp (g := τ) z h3 h2)

/-- The formal derivatives of a map whose real derivative is `h ↦ A h + B conj h`. -/
theorem h35c_dz_of_fderiv {f : ℂ → ℂ} {z A B : ℂ} (h : ∀ w : ℂ, fderiv ℝ f z w = A * w + B * conj w) :
    dz f z = A ∧ dzbar f z = B := by
  unfold dz dzbar
  rw [h 1, h I]
  simp only [map_one, conj_I, mul_one]
  constructor
  · ring_nf; rw [I_sq]; ring
  · ring_nf; rw [I_sq]; ring

/-- **Formal derivatives of the cone fill-in.**  With `v = ρ z/|z|` and `c = |z|/ρ`,
`∂_z = c (τ v + v τ'(v))/(2 z)` and `∂_{z̄} = c (τ v - v τ'(v))/(2 z̄)`: the radial derivative is `c τ(v)`, the
angular one `c v τ'(v) i`. -/
theorem h35c_cone_dz {τ : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) {z : ℂ} (hz0 : z ≠ 0) (hzρ : ‖z‖ < ρ) {v c : ℂ}
    (hv : v = ((ρ / ‖z‖ : ℝ) : ℂ) * z) (hc : c = ((‖z‖ / ρ : ℝ) : ℂ)) :
    dz (h35c_cone τ ρ) z = c * (τ v + v * deriv τ v) / (2 * z) ∧
      dzbar (h35c_cone τ ρ) z = c * (τ v - v * deriv τ v) / (2 * conj z) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρinv : ρ < ρ₀⁻¹ := hρ1.trans ((one_lt_inv₀ hρ₀).2 (hρ₀ρ.trans hρ1))
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set T := h35c_cone τ ρ with hTdef
  have hT : HasFDerivAt T (fderiv ℝ T z) z :=
    ((h35c_cone_contDiffAt hρ₀ hρ₀ρ hρ1 hd hz0 hzρ).differentiableAt one_ne_zero).hasFDerivAt
  -- radial derivative
  have hrad : fderiv ℝ T z z = c * τ v := by
    have hp : HasDerivAt (fun t : ℝ => z + (t : ℂ) * z) z 0 := by
      have h := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const z).const_add z).comp_ofReal
      simpa using h
    have h1 := hT.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hp (by simp)
    have hg : HasDerivAt (fun t : ℝ => (((1 + t) * (‖z‖ / ρ) : ℝ) : ℂ) * τ v) (c * τ v) 0 := by
      have h := ((((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (‖z‖ / ρ)).ofReal_comp).mul_const (τ v)
      simpa [hc] using h
    refine h1.unique (hg.congr_of_eventuallyEq ?_)
    have hδ : 0 < (ρ - ‖z‖) / ‖z‖ := div_pos (by linarith) hnz
    filter_upwards [Ioo_mem_nhds (show -1 < (0 : ℝ) by norm_num) hδ] with t ht
    have h1t : 0 < 1 + t := by linarith [ht.1]
    have hnorm : ‖z + (t : ℂ) * z‖ = (1 + t) * ‖z‖ := by
      rw [show z + (t : ℂ) * z = ((1 + t : ℝ) : ℂ) * z by push_cast; ring, norm_mul, norm_real,
        Real.norm_of_nonneg h1t.le]
    have hle : ‖z + (t : ℂ) * z‖ ≤ ρ := by
      rw [hnorm]
      have := ht.2
      rw [lt_div_iff₀ hnz] at this
      nlinarith
    show h35c_cone τ ρ (z + (t : ℂ) * z) = _
    unfold h35c_cone
    rw [ite_eq_left hle, hnorm]
    have hv' : (((ρ / ((1 + t) * ‖z‖) : ℝ)) : ℂ) * (z + (t : ℂ) * z) = v := by
      rw [hv, show z + (t : ℂ) * z = ((1 + t : ℝ) : ℂ) * z by push_cast; ring, ← mul_assoc, ← ofReal_mul]
      congr 2
      field_simp
    rw [hv']
    congr 2
    ring
  -- angular derivative
  have hang : fderiv ℝ T z (z * I) = c * (deriv τ v * (v * I)) := by
    have hp : HasDerivAt (fun t : ℝ => z * exp ((t : ℂ) * I)) (z * I) 0 := by
      have h := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const I).cexp.const_mul z).comp_ofReal
      simpa using h
    have h1 := hT.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hp (by simp)
    have hvA : v ∈ annulus ρ₀ ρ₀⁻¹ := by
      refine ⟨?_, ?_⟩ <;> rw [hv, h35c_norm_scale hρ.le hz0]
      exacts [hρ₀ρ, hρinv]
    have hτv : HasDerivAt τ (deriv τ v) (v * exp (((0 : ℝ) : ℂ) * I)) := by
      simpa using (hd.differentiableAt (hA.mem_nhds hvA)).hasDerivAt
    have hq : HasDerivAt (fun t : ℝ => v * exp ((t : ℂ) * I)) (v * I) 0 := by
      have h := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const I).cexp.const_mul v).comp_ofReal
      simpa using h
    have hg : HasDerivAt (fun t : ℝ => c * τ (v * exp ((t : ℂ) * I))) (c * (deriv τ v * (v * I))) 0 :=
      (hτv.comp (0 : ℝ) hq).const_mul c
    refine h1.unique (hg.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    have hnorm : ‖z * exp ((t : ℂ) * I)‖ = ‖z‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    show h35c_cone τ ρ (z * exp ((t : ℂ) * I)) = c * τ (v * exp ((t : ℂ) * I))
    unfold h35c_cone
    rw [ite_eq_left (hnorm.le.trans hzρ.le), hnorm, hc, hv, mul_assoc]
  -- the full derivative
  have hfd : ∀ w : ℂ, fderiv ℝ T z w =
      c * (τ v + v * deriv τ v) / (2 * z) * w + c * (τ v - v * deriv τ v) / (2 * conj z) * conj w := by
    intro w
    set k : ℂ := w / z with hk
    have hw : w = ((k.re : ℝ) : ℂ) * z + ((k.im : ℝ) : ℂ) * (z * I) := by
      have : w = k * z := by rw [hk]; field_simp
      conv_lhs => rw [this, ← re_add_im k]
      ring
    have hlin : fderiv ℝ T z w = (k.re : ℂ) * (c * τ v) + (k.im : ℂ) * (c * (deriv τ v * (v * I))) := by
      rw [hw, ← Complex.real_smul, ← Complex.real_smul, map_add, map_smul, map_smul, hrad, hang,
        Complex.real_smul, Complex.real_smul]
    rw [hlin]
    have hzc : conj z ≠ 0 := (map_ne_zero _).2 hz0
    have hwc : conj w = ((k.re : ℝ) : ℂ) * conj z - ((k.im : ℝ) : ℂ) * (conj z * I) := by
      rw [hw]; simp [conj_ofReal]; ring
    rw [hwc, hw]
    field_simp
    ring_nf
  exact h35c_dz_of_fderiv hfd

/-- `Re (p/t) > 0` means `|t - p| < |t + p|`. -/
theorem h35c_norm_sub_lt_add {t p : ℂ} (ht : t ≠ 0) (hq : 0 < (p / t).re) : ‖t - p‖ < ‖t + p‖ := by
  have hn : 0 < normSq t := normSq_pos.2 ht
  rw [div_re] at hq
  have hq' : 0 < p.re * t.re + p.im * t.im := by
    have : (p.re * t.re + p.im * t.im) / normSq t > 0 := by rw [add_div]; exact hq
    exact (div_pos_iff_of_pos_right hn).1 this
  have h1 : ‖t - p‖ ^ 2 < ‖t + p‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [sub_re, sub_im, add_re, add_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- **Dilatation of the cone fill-in**: at `0 < |z| < ρ` it is orientation preserving and its dilatation quotient
is that of `(t, p) = (τ v, v τ'(v))`, `v = ρ z/|z|`. -/
theorem h35c_cone_dilat {τ : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) (hne : ∀ z ∈ annulus ρ₀ ρ₀⁻¹, τ z ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) (hzρ : ‖z‖ < ρ) {v : ℂ} (hv : v = ((ρ / ‖z‖ : ℝ) : ℂ) * z)
    (hq : 0 < (v * deriv τ v / τ v).re) :
    ‖dzbar (h35c_cone τ ρ) z‖ < ‖dz (h35c_cone τ ρ) z‖ ∧
      dilatationQuotient (h35c_cone τ ρ) z =
        (1 + ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) /
          (1 - ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hρinv : ρ < ρ₀⁻¹ := hρ1.trans ((one_lt_inv₀ hρ₀).2 (hρ₀ρ.trans hρ1))
  have hvA : v ∈ annulus ρ₀ ρ₀⁻¹ := by
    refine ⟨?_, ?_⟩ <;> rw [hv, h35c_norm_scale hρ.le hz0]
    exacts [hρ₀ρ, hρinv]
  obtain ⟨h1, h2⟩ := h35c_cone_dz hρ₀ hρ₀ρ hρ1 hd hz0 hzρ hv rfl
  have hlt := h35c_norm_sub_lt_add (hne v hvA) hq
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hc : 0 < ‖((‖z‖ / ρ : ℝ) : ℂ)‖ := by
    rw [norm_real, Real.norm_of_nonneg (div_nonneg hnz.le hρ.le)]; exact div_pos hnz hρ
  have hdz : ‖dz (h35c_cone τ ρ) z‖ = ‖((‖z‖ / ρ : ℝ) : ℂ)‖ * ‖τ v + v * deriv τ v‖ / (2 * ‖z‖) := by
    rw [h1, norm_div, norm_mul, norm_mul, Complex.norm_two]
  have hdzb : ‖dzbar (h35c_cone τ ρ) z‖ =
      ‖((‖z‖ / ρ : ℝ) : ℂ)‖ * ‖τ v - v * deriv τ v‖ / (2 * ‖z‖) := by
    rw [h2, norm_div, norm_mul, norm_mul, Complex.norm_two, Complex.norm_conj]
  have hpos : 0 < ‖τ v + v * deriv τ v‖ := (norm_nonneg _).trans_lt hlt
  refine ⟨?_, ?_⟩
  · rw [hdz, hdzb]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt hc) (by positivity)
  · have hmu : ‖complexDilatation (h35c_cone τ ρ) z‖ = ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖ := by
      rw [complexDilatation, norm_div, hdz, hdzb]
      field_simp
    rw [dilatationQuotient, hmu]

/-- **Uniform dilatation bound for the cone fill-in** (compactness of the circle `|v| = ρ`). -/
theorem h35c_cone_K {τ : ℂ → ℂ} {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) (hne : ∀ z ∈ annulus ρ₀ ρ₀⁻¹, τ z ≠ 0)
    (hq : ∀ v : ℂ, ‖v‖ = ρ → 0 < (v * deriv τ v / τ v).re) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ v : ℂ, ‖v‖ = ρ →
      (1 + ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) /
        (1 - ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) ≤ K := by
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρinv : ρ < ρ₀⁻¹ := hρ1.trans ((one_lt_inv₀ hρ₀).2 (hρ₀ρ.trans hρ1))
  have hsub : sphere (0 : ℂ) ρ ⊆ annulus ρ₀ ρ₀⁻¹ := fun v hv => by
    have := mem_sphere_zero_iff_norm.1 hv
    exact ⟨by rw [this]; exact hρ₀ρ, by rw [this]; exact hρinv⟩
  have hlt : ∀ v ∈ sphere (0 : ℂ) ρ, ‖τ v - v * deriv τ v‖ < ‖τ v + v * deriv τ v‖ := fun v hv =>
    h35c_norm_sub_lt_add (hne v (hsub hv)) (hq v (mem_sphere_zero_iff_norm.1 hv))
  have hτc : ContinuousOn τ (sphere (0 : ℂ) ρ) := hd.continuousOn.mono hsub
  have hτ'c : ContinuousOn (deriv τ) (sphere (0 : ℂ) ρ) := (hd.deriv hA).continuousOn.mono hsub
  have hP : ContinuousOn (fun v => v * deriv τ v) (sphere (0 : ℂ) ρ) := continuousOn_id.mul hτ'c
  have hr : ContinuousOn (fun v => ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) (sphere (0 : ℂ) ρ) :=
    ((hτc.sub hP).norm).div ((hτc.add hP).norm) fun v hv => ((norm_nonneg _).trans_lt (hlt v hv)).ne'
  have hr1 : ∀ v ∈ sphere (0 : ℂ) ρ, ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖ < 1 := fun v hv =>
    (div_lt_one ((norm_nonneg _).trans_lt (hlt v hv))).2 (hlt v hv)
  have hΦ : ContinuousOn (fun v => (1 + ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖) /
      (1 - ‖τ v - v * deriv τ v‖ / ‖τ v + v * deriv τ v‖)) (sphere (0 : ℂ) ρ) :=
    (continuousOn_const.add hr).div (continuousOn_const.sub hr) fun v hv => (sub_pos.2 (hr1 v hv)).ne'
  obtain ⟨v₀, -, hv₀⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hρ.le) hΦ
  refine ⟨max 1 ((1 + ‖τ v₀ - v₀ * deriv τ v₀‖ / ‖τ v₀ + v₀ * deriv τ v₀‖) /
    (1 - ‖τ v₀ - v₀ * deriv τ v₀‖ / ‖τ v₀ + v₀ * deriv τ v₀‖)), le_max_left _ _, fun v hv => ?_⟩
  exact (hv₀ (mem_sphere_zero_iff_norm.2 hv)).trans (le_max_right _ _)

/-- A line meets a circle (together with the origin) in a countable set. -/
theorem h35c_countable (ρ a : ℝ) : {y : ℝ | y ^ 2 + a ^ 2 = ρ ^ 2 ∨ y = 0}.Countable := by
  refine (((countable_singleton (√(ρ ^ 2 - a ^ 2))).insert (-√(ρ ^ 2 - a ^ 2))).insert 0).mono ?_
  rintro y (hy | hy)
  · have hy' : y ^ 2 = ρ ^ 2 - a ^ 2 := by linarith
    have h0 : 0 ≤ ρ ^ 2 - a ^ 2 := by rw [← hy']; exact sq_nonneg y
    have h2 : y ^ 2 = (√(ρ ^ 2 - a ^ 2)) ^ 2 := by rw [Real.sq_sqrt h0, hy']
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact Or.inr (Or.inr (mem_singleton_iff.2 h))
    · exact Or.inr (Or.inl h)
  · exact Or.inl hy

/-- `|x + iy|² = x² + y²`. -/
theorem h35c_norm_sq_xy (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

/-- **The fill-in lemma.**  Let `τ` be holomorphic, injective and nonvanishing on the annulus `ρ₀ < |z| < 1/ρ₀`,
with `|τ| < 1` inside the unit circle and `|τ| = 1` on it.  Then some `T` is a quasiconformal self-map of `Δ`, equal
to `τ` on a collar `ρ < |z| < 1`, with a homeomorphic extension to `Δ̄` equal to `τ` on the circle: the cone
`z ↦ (|z|/ρ) τ(ρ z/|z|)` fills in the star-shaped curve `τ(|z| = ρ)`. -/
theorem h35c_fill {τ : ℂ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hd : DifferentiableOn ℂ τ (annulus ρ₀ ρ₀⁻¹)) (hi : InjOn τ (annulus ρ₀ ρ₀⁻¹))
    (hne : ∀ z ∈ annulus ρ₀ ρ₀⁻¹, τ z ≠ 0) (hin : ∀ z : ℂ, ρ₀ < ‖z‖ → ‖z‖ < 1 → ‖τ z‖ < 1)
    (hon : ∀ z : ℂ, ‖z‖ = 1 → ‖τ z‖ = 1) :
    ∃ (T : ℂ → ℂ) (ρ K : ℝ), ρ₀ < ρ ∧ ρ < 1 ∧ IsKQC T unitDisc K ∧ T '' unitDisc = unitDisc ∧
      EqOn T τ (annulus ρ 1) ∧ ∃ F : ExtPlane → ExtPlane, IsHomeoExtension T unitDisc unitDisc F ∧
        ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = ((τ ζ : ℂ) : ExtPlane) := by
  have hA : IsOpen (annulus ρ₀ ρ₀⁻¹) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρ₀inv : 1 < ρ₀⁻¹ := (one_lt_inv₀ hρ₀).2 hρ₀1
  -- the radius of the cone
  have hqc : ContinuousOn (fun z => z * deriv τ z / τ z) (annulus ρ₀ ρ₀⁻¹) :=
    (continuousOn_id.mul (hd.deriv hA).continuousOn).div hd.continuousOn hne
  obtain ⟨ρ, hρ₀ρ, hρ1, hqρ⟩ := h35c_choose_rho hρ₀ hρ₀1 hqc
    (fun z hz => h35c_q_pos hρ₀ hρ₀1 hd hi hne hin hon hz)
  have hρ : 0 < ρ := hρ₀.trans hρ₀ρ
  -- the logarithm and its properties
  obtain ⟨L, hL⟩ := h35c_exists_log hρ₀ hρ₀1 hd hne
  have hlogρ : Real.log ρ₀ < Real.log ρ := Real.log_lt_log hρ₀ hρ₀ρ
  have hlogρ0 : Real.log ρ < 0 := Real.log_neg hρ hρ1
  have hnw : ∀ ζ₁ ζ₂ : ℂ, Real.log ρ ≤ ζ₁.re → ζ₁.re ≤ 0 → Real.log ρ ≤ ζ₂.re → ζ₂.re ≤ 0 → ζ₁ ≠ ζ₂ →
      0 < (conj (ζ₂ - ζ₁) * (L ζ₂ - L ζ₁)).re := by
    intro ζ₁ ζ₂ h1 h1' h2 h2' hne'
    refine h35c_nw (L' := fun ζ => exp ζ * deriv τ (exp ζ) / τ (exp ζ)) (a := Real.log ρ)
      (fun ζ ha hb => (hL ζ (by linarith) (by linarith)).2) (fun ζ ha hb => ?_) h1 h1' h2 h2' hne'
    apply hqρ
    · rw [Complex.norm_exp]
      calc ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
        _ ≤ Real.exp ζ.re := Real.exp_le_exp.2 ha
    · rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.2 hb
  have hper : ∀ ζ : ℂ, Real.log ρ₀ < ζ.re → ζ.re < -Real.log ρ₀ → L (ζ + 2 * π * I) = L ζ + 2 * π * I :=
    fun ζ h1 h2 => h35c_period hρ₀ hρ₀1 hlogρ0.le hL hi hon hnw h1 h2
  -- the cone fill-in
  set T := h35c_cone τ ρ with hTdef
  have hinj : InjOn T (closedBall 0 1) :=
    h35c_cone_injOn hρ₀ hρ₀ρ hρ1 (fun ζ h1 h2 => (hL ζ h1 h2).1) hper hnw
  have hcont : ContinuousOn T (ball 0 ρ₀⁻¹) :=
    h35c_cone_continuousOn hρ₀ hρ₀ρ hρ1 hd.continuousOn
      (fun z hz => (hin z (by rw [hz]; exact hρ₀ρ) (by rw [hz]; exact hρ1)).le)
  have hcl : closedBall (0 : ℂ) 1 ⊆ ball 0 ρ₀⁻¹ := closedBall_subset_ball hρ₀inv
  have hΔcl : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hTon : ∀ z : ℂ, ‖z‖ = 1 → T z = τ z := fun z hz =>
    h35c_cone_eq_of_lt τ (by rw [hz]; exact hρ1)
  have hTin : ∀ z ∈ unitDisc, ‖T z‖ < 1 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    rw [hTdef]
    by_cases h : ‖z‖ ≤ ρ
    · by_cases hz0 : z = 0
      · rw [hz0, h35c_cone_zero τ hρ, norm_zero]; exact one_pos
      · have hv := h35c_norm_scale hρ.le hz0
        have hτv := hin _ (by rw [hv]; exact hρ₀ρ) (by rw [hv]; exact hρ1)
        unfold h35c_cone
        rw [ite_eq_left h, norm_mul, norm_real, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hρ.le)]
        calc ‖z‖ / ρ * ‖τ (((ρ / ‖z‖ : ℝ) : ℂ) * z)‖ ≤ 1 * ‖τ (((ρ / ‖z‖ : ℝ) : ℂ) * z)‖ :=
              mul_le_mul_of_nonneg_right ((div_le_one hρ).2 h) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hτv
    · rw [h35c_cone_eq_of_lt τ (lt_of_not_ge h)]
      exact hin z (hρ₀ρ.trans (lt_of_not_ge h)) hz1
  -- `T` maps `Δ` onto `Δ`
  have hopen : IsOpen (T '' unitDisc) :=
    isOpen_image_of_continuousOn_injOn isOpen_ball (hcont.mono (hΔcl.trans hcl)) (hinj.mono hΔcl)
  have himg : T '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.2 (hTin z hz)
    · have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
      refine (isPreconnected_ball (x := (0 : ℂ)) (r := 1)).subset_of_closure_inter_subset hopen
        ⟨0, h0, 0, h0, h35c_cone_zero τ hρ⟩ ?_
      rintro y ⟨hy, hyΔ⟩
      have hK : IsCompact (T '' closedBall 0 1) :=
        (isCompact_closedBall 0 1).image_of_continuousOn (hcont.mono hcl)
      have hy' : y ∈ T '' closedBall 0 1 := closure_minimal (image_mono hΔcl) hK.isClosed hy
      obtain ⟨x, hx, rfl⟩ := hy'
      refine ⟨x, ?_, rfl⟩
      rcases (mem_closedBall_zero_iff.1 hx).lt_or_eq with h | h
      · exact mem_ball_zero_iff.2 h
      · exfalso
        have := mem_ball_zero_iff.1 hyΔ
        rw [hTon x h, hon x h] at this
        exact lt_irrefl _ this
  -- quasiconformality
  obtain ⟨K, hK1, hK⟩ := h35c_cone_K hρ₀ hρ₀ρ hρ1 hd hne
    (fun v hv => hqρ v (by rw [hv]) (by rw [hv]; exact hρ1.le))
  have hhom : IsHomeomorphOnto T unitDisc (T '' unitDisc) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_ball (hcont.mono (hΔcl.trans hcl)) (hinj.mono hΔcl)
  have hLnull : volume (sphere (0 : ℂ) ρ ∪ {0}) = 0 :=
    measure_union_null (Measure.addHaar_sphere volume 0 ρ) (measure_singleton 0)
  have hLv : ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) ρ ∪ {0}}.Countable :=
    Eventually.of_forall fun x => (h35c_countable ρ x).mono fun y hy => by
      rcases hy with hy | hy
      · left
        have h := h35c_norm_sq_xy x y
        rw [mem_sphere_zero_iff_norm.1 hy] at h
        linarith
      · right
        have := congrArg Complex.im (mem_singleton_iff.1 hy)
        simpa using this
  have hLh : ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) ρ ∪ {0}}.Countable :=
    Eventually.of_forall fun y => (h35c_countable ρ y).mono fun x hx => by
      rcases hx with hx | hx
      · left
        have h := h35c_norm_sq_xy x y
        rw [mem_sphere_zero_iff_norm.1 hx] at h
        linarith
      · right
        have := congrArg Complex.re (mem_singleton_iff.1 hx)
        simpa using this
  have hqc' : IsKQC T unitDisc K := by
    refine s13x_removable isOpen_ball hK1 hhom hLnull hLv hLh fun z hz => ?_
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz.1
    have hzρ : ‖z‖ ≠ ρ := fun h => hz.2 (Or.inl (mem_sphere_zero_iff_norm.2 h))
    have hz0 : z ≠ 0 := fun h => hz.2 (Or.inr (mem_singleton_iff.2 h))
    rcases lt_or_gt_of_ne hzρ with h | h
    · have hUo : IsOpen (annulus 0 ρ) :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      have hUΔ : annulus 0 ρ ⊆ unitDisc := fun w hw => mem_ball_zero_iff.2 (hw.2.trans hρ1)
      refine ⟨annulus 0 ρ, hUo, ⟨norm_pos_iff.2 hz0, h⟩, hUΔ, isKQC_of_isC1Quasiconformal
        ⟨hUo, hK1, fun w hw => ?_, qcl_f_isHomeomorphOnto_of_injOn hUo
          (hcont.mono (hUΔ.trans (hΔcl.trans hcl))) (hinj.mono (hUΔ.trans hΔcl)), fun w hw => ?_⟩⟩
      · exact (h35c_cone_contDiffAt hρ₀ hρ₀ρ hρ1 hd (norm_pos_iff.1 hw.1) hw.2).contDiffWithinAt
      · have hw0 : w ≠ 0 := norm_pos_iff.1 hw.1
        have hv := h35c_norm_scale hρ.le hw0
        obtain ⟨h1, h2⟩ := h35c_cone_dilat hρ₀ hρ₀ρ hρ1 hd hne hw0 hw.2 rfl
          (hqρ _ (by rw [hv]) (by rw [hv]; exact hρ1.le))
        exact ⟨h1, h2 ▸ hK _ hv⟩
    · have hUo : IsOpen (annulus ρ 1) :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      have hUΔ : annulus ρ 1 ⊆ unitDisc := fun w hw => mem_ball_zero_iff.2 hw.2
      have hUA : annulus ρ 1 ⊆ annulus ρ₀ ρ₀⁻¹ := fun w hw => ⟨hρ₀ρ.trans hw.1, hw.2.trans hρ₀inv⟩
      have hconf : IsConformalOnto T (annulus ρ 1) (T '' annulus ρ 1) :=
        ⟨(hd.mono hUA).congr fun w hw => h35c_cone_eq_of_lt τ hw.1,
          hinj.mono (hUΔ.trans hΔcl), rfl⟩
      exact ⟨annulus ρ 1, hUo, ⟨h, hz1⟩, hUΔ, (isKQC_one_of_conformal hUo hconf).mono hK1⟩
  refine ⟨T, ρ, K, hρ₀ρ, hρ1, hqc', himg, fun z hz => h35c_cone_eq_of_lt τ hz.1, ?_⟩
  obtain ⟨F, hF⟩ := s13x_disc_extension ⟨K, hqc'⟩ himg
  refine ⟨F, hF, fun ζ hζ => ?_⟩
  -- boundary values along the radius to `ζ`
  have hγU : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), ((t : ℂ) * ζ) ∈ unitDisc := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [unitDisc, mem_ball_zero_iff, norm_mul, norm_real, Real.norm_of_nonneg ht.1.le, hζ, mul_one]
    exact ht.2
  have hγ : Tendsto (fun t : ℝ => (t : ℂ) * ζ) (𝓝[<] (1 : ℝ)) (𝓝 ζ) := by
    have h := ((continuous_ofReal.mul continuous_const).tendsto (1 : ℝ) (f := fun t : ℝ => (t : ℂ) * ζ))
    simp only [ofReal_one, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h1 := hF.tendsto_comp (s35a_x_mem_closure hζ) hγU
    ((OnePoint.continuous_coe.tendsto ζ).comp hγ)
  have hζA : ζ ∈ annulus ρ₀ ρ₀⁻¹ := ⟨by rw [hζ]; exact hρ₀1, by rw [hζ]; exact hρ₀inv⟩
  have h2 : Tendsto (fun t : ℝ => ((T ((t : ℂ) * ζ) : ℂ) : ExtPlane)) (𝓝[<] (1 : ℝ))
      (𝓝 ((τ ζ : ℂ) : ExtPlane)) := by
    have hτ : Tendsto (fun t : ℝ => ((τ ((t : ℂ) * ζ) : ℂ) : ExtPlane)) (𝓝[<] (1 : ℝ))
        (𝓝 ((τ ζ : ℂ) : ExtPlane)) :=
      (OnePoint.continuous_coe.tendsto _).comp
        ((hd.continuousOn.continuousAt (hA.mem_nhds hζA)).tendsto.comp hγ)
    refine hτ.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hρ1] with t ht
    rw [hTdef, h35c_cone_eq_of_lt τ]
    rw [norm_mul, norm_real, Real.norm_of_nonneg (hρ.le.trans ht.1.le), hζ, mul_one]
    exact ht.1
  exact tendsto_nhds_unique h1 h2

/-- **Reflection and fill-in.**  Let `τ₀` be holomorphic on the collar `ρ₁ < |z| < 1`, continuous, injective and
nonvanishing on `ρ₁ < |z| ≤ 1`, with `|τ₀| < 1` inside and `|τ₀| = 1` on the unit circle.  Then some `T` is a
quasiconformal self-map of `Δ`, equal to `τ₀` on a collar `ρ < |z| < 1`, with a homeomorphic extension equal to `τ₀`
on the circle.  (Schwarz reflection `1/conj τ₀(1/z̄)` makes `τ₀` holomorphic and injective across the circle, and
`h35c_fill` applies.) -/
theorem h35c_reflect_fill {τ₀ : ℂ → ℂ} {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hdiff : DifferentiableOn ℂ τ₀ (annulus ρ₁ 1)) (hcont : ContinuousOn τ₀ {y : ℂ | ρ₁ < ‖y‖ ∧ ‖y‖ ≤ 1})
    (hinj : InjOn τ₀ {y : ℂ | ρ₁ < ‖y‖ ∧ ‖y‖ ≤ 1}) (hne : ∀ y : ℂ, ρ₁ < ‖y‖ → ‖y‖ ≤ 1 → τ₀ y ≠ 0)
    (hin : ∀ y : ℂ, ρ₁ < ‖y‖ → ‖y‖ < 1 → ‖τ₀ y‖ < 1) (hon : ∀ y : ℂ, ‖y‖ = 1 → ‖τ₀ y‖ = 1) :
    ∃ (T : ℂ → ℂ) (ρ K : ℝ), ρ₁ < ρ ∧ ρ < 1 ∧ IsKQC T unitDisc K ∧ T '' unitDisc = unitDisc ∧
      EqOn T τ₀ (annulus ρ 1) ∧ ∃ F : ExtPlane → ExtPlane, IsHomeoExtension T unitDisc unitDisc F ∧
        ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = ((τ₀ ζ : ℂ) : ExtPlane) := by
  set τ : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then τ₀ z else circleReflect (τ₀ (circleReflect z)) with hτdef
  set U : Set ℂ := annulus ρ₁ ρ₁⁻¹ with hUdef
  have hρ₁inv : 1 < ρ₁⁻¹ := (one_lt_inv₀ hρ₁).2 hρ₁1
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hτin : ∀ z : ℂ, ‖z‖ ≤ 1 → τ z = τ₀ z := fun z hz => ite_eq_left hz
  have hτout : ∀ z : ℂ, 1 < ‖z‖ → τ z = circleReflect (τ₀ (circleReflect z)) := fun z hz =>
    ite_eq_right (not_le.2 hz)
  -- reflection of the outer half of `U` into the collar
  have hcr : ∀ z ∈ U, 1 < ‖z‖ → ρ₁ < ‖circleReflect z‖ ∧ ‖circleReflect z‖ < 1 := fun z hz h1 => by
    rw [norm_circleReflect]
    refine ⟨?_, inv_lt_one_of_one_lt₀ h1⟩
    have := hz.2
    rw [lt_inv_comm₀ (by linarith) hρ₁] at this
    exact this
  have hcr0 : ∀ z : ℂ, 1 < ‖z‖ → z ≠ 0 := fun z h h0 => by rw [h0, norm_zero] at h; linarith
  have hnorm_out : ∀ z ∈ U, 1 < ‖z‖ → 1 < ‖τ z‖ := fun z hz h1 => by
    obtain ⟨h2, h3⟩ := hcr z hz h1
    rw [hτout z h1, norm_circleReflect]
    exact one_lt_inv₀ (norm_pos_iff.2 (hne _ h2 h3.le)) |>.2 (hin _ h2 h3)
  -- holomorphy of the reflected map
  have hUA : IsCircleSymmetricNbhd U (sphere (0 : ℂ) 1) := by
    refine ⟨hUo, ?_, fun z hz => ?_⟩
    · ext z
      constructor
      · exact fun h => h.2
      · intro h
        have h1 := mem_sphere_zero_iff_norm.1 h
        exact ⟨⟨by rw [h1]; exact hρ₁1, by rw [h1]; exact hρ₁inv⟩, h⟩
    · have hz0 : z ≠ 0 := fun h => by
        have := hz.1; rw [h, norm_zero] at this; linarith
      refine ⟨?_, ?_⟩ <;> rw [norm_circleReflect]
      · have := hz.2
        rw [lt_inv_comm₀ (hρ₁.trans hz.1) hρ₁] at this
        exact this
      · exact (inv_lt_inv₀ (hρ₁.trans hz.1) hρ₁).2 hz.1
  have hUΔ : U ∩ unitDisc ⊆ annulus ρ₁ 1 := fun z hz => ⟨hz.1.1, mem_ball_zero_iff.1 hz.2⟩
  have hdiffΔ : DifferentiableOn ℂ τ₀ (U ∩ unitDisc) := hdiff.mono hUΔ
  have hcontΔ : ContinuousOn τ₀ ((U ∩ unitDisc) ∪ sphere (0 : ℂ) 1) := hcont.mono fun z hz => by
    rcases hz with hz | hz
    · exact ⟨hz.1.1, (mem_ball_zero_iff.1 hz.2).le⟩
    · have := mem_sphere_zero_iff_norm.1 hz
      exact ⟨by rw [this]; exact hρ₁1, this.le⟩
  have hAo : IsOpen (annulus ρ₁ 1) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hd : DifferentiableOn ℂ τ U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · have hzA : z ∈ annulus ρ₁ 1 := ⟨hz.1, hlt⟩
      refine (hdiff.differentiableAt (hAo.mem_nhds hzA)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hlt] with w hw
      exact hτin w (le_of_lt hw)
    · exact differentiableAt_circleReflectExtend_norm_one_of_mem_arc hUA hdiffΔ hcontΔ
        (fun w hw => hon w (mem_sphere_zero_iff_norm.1 hw)) (mem_sphere_zero_iff_norm.2 heq)
    · have hz0 := hcr0 z hgt
      obtain ⟨h2, h3⟩ := hcr z hz hgt
      have hcrA : conj (1 / z) ∈ annulus ρ₁ 1 := by
        have : circleReflect z = conj (1 / z) := by rw [circleReflect, map_div₀, map_one]
        rw [← this]; exact ⟨h2, h3⟩
      have hfd : DifferentiableAt ℂ τ₀ (conj (1 / z)) := hdiff.differentiableAt (hAo.mem_nhds hcrA)
      have hcc := hfd.conj_conj
      rw [conj_conj] at hcc
      have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / w) z :=
        (differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0
      have hd1 : DifferentiableAt ℂ ((conj ∘ τ₀ ∘ conj) ∘ fun w : ℂ => 1 / w) z := hcc.comp z hinv
      have hne' : ((conj ∘ τ₀ ∘ conj) ∘ fun w : ℂ => 1 / w) z ≠ 0 := by
        show conj (τ₀ (conj (1 / z))) ≠ 0
        rw [map_ne_zero]
        exact hne _ hcrA.1 hcrA.2.le
      have hinv2 : DifferentiableAt ℂ (fun v : ℂ => 1 / v) (((conj ∘ τ₀ ∘ conj) ∘ fun w : ℂ => 1 / w) z) :=
        (differentiableAt_const (1 : ℂ)).div differentiableAt_id hne'
      have hdz : DifferentiableAt ℂ ((fun v : ℂ => 1 / v) ∘ ((conj ∘ τ₀ ∘ conj) ∘ fun w : ℂ => 1 / w)) z :=
        hinv2.comp z hd1
      refine hdz.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hgt] with w hw
      rw [hτout w hw, circleReflect, circleReflect]
      simp only [Function.comp_apply, map_div₀, map_one]
  -- injectivity
  have hi : InjOn τ U := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_cases h1 : ‖z₁‖ ≤ 1 <;> by_cases h2 : ‖z₂‖ ≤ 1
    · rw [hτin z₁ h1, hτin z₂ h2] at heq
      exact hinj ⟨hz₁.1, h1⟩ ⟨hz₂.1, h2⟩ heq
    · exfalso
      have a := hnorm_out z₂ hz₂ (lt_of_not_ge h2)
      rw [← heq, hτin z₁ h1] at a
      rcases h1.lt_or_eq with h | h
      · linarith [hin z₁ hz₁.1 h]
      · linarith [hon z₁ h]
    · exfalso
      have a := hnorm_out z₁ hz₁ (lt_of_not_ge h1)
      rw [heq, hτin z₂ h2] at a
      rcases h2.lt_or_eq with h | h
      · linarith [hin z₂ hz₂.1 h]
      · linarith [hon z₂ h]
    · have g1 := lt_of_not_ge h1
      have g2 := lt_of_not_ge h2
      rw [hτout z₁ g1, hτout z₂ g2] at heq
      obtain ⟨a1, b1⟩ := hcr z₁ hz₁ g1
      obtain ⟨a2, b2⟩ := hcr z₂ hz₂ g2
      have e1 := congrArg circleReflect heq
      rw [circleReflect_circleReflect (hne _ a1 b1.le), circleReflect_circleReflect (hne _ a2 b2.le)] at e1
      have e2 := hinj ⟨a1, b1.le⟩ ⟨a2, b2.le⟩ e1
      have e3 := congrArg circleReflect e2
      rwa [circleReflect_circleReflect (hcr0 z₁ g1), circleReflect_circleReflect (hcr0 z₂ g2)] at e3
  have hne' : ∀ z ∈ U, τ z ≠ 0 := by
    intro z hz
    by_cases h : ‖z‖ ≤ 1
    · rw [hτin z h]; exact hne z hz.1 h
    · have := hnorm_out z hz (lt_of_not_ge h)
      intro h0
      rw [h0, norm_zero] at this
      linarith
  obtain ⟨T, ρ, K, hρ₁ρ, hρ1, hK, himg, heq, F, hF, hFb⟩ := h35c_fill hρ₁ hρ₁1 hd hi hne'
    (fun z h1 h2 => by rw [hτin z h2.le]; exact hin z h1 h2)
    (fun z h => by rw [hτin z h.le]; exact hon z h)
  refine ⟨T, ρ, K, hρ₁ρ, hρ1, hK, himg, fun z hz => by rw [heq hz, hτin z hz.2.le], F, hF,
    fun ζ hζ => by rw [hFb ζ hζ, hτin ζ hζ.le]⟩

/-- `extToC` is continuous at every finite point of `ℂ̄`. -/
theorem h35c_continuousAt_extToC (c : ℂ) : ContinuousAt extToC (c : ExtPlane) := by
  rw [OnePoint.continuousAt_coe]
  have h : (extToC ∘ ((↑) : ℂ → ExtPlane)) = id := funext fun _ => rfl
  rw [h]
  exact continuousAt_id

/-- A point of the unit circle lies in the closure (in `ℂ̄`) of every collar `r < |z| < 1`. -/
theorem h35c_mem_closure_annulus {r : ℝ} (hr : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (ζ : ExtPlane) ∈ closure (toExt (annulus r 1)) := by
  have hγ : Tendsto (fun t : ℝ => (((t : ℂ) * ζ : ℂ) : ExtPlane)) (𝓝[<] (1 : ℝ)) (𝓝 (ζ : ExtPlane)) := by
    have h := ((continuous_ofReal.mul continuous_const).tendsto (1 : ℝ) (f := fun t : ℝ => (t : ℂ) * ζ))
    simp only [ofReal_one, one_mul] at h
    exact (OnePoint.continuous_coe.tendsto ζ).comp (h.mono_left nhdsWithin_le_nhds)
  refine mem_closure_of_tendsto hγ ?_
  filter_upwards [Ioo_mem_nhdsLT (show max r 0 < 1 from max_lt hr one_pos)] with t ht
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have hn : ‖(t : ℂ) * ζ‖ = t := by rw [norm_mul, norm_real, Real.norm_of_nonneg ht0.le, hζ, mul_one]
  exact ⟨(t : ℂ) * ζ, ⟨by rw [hn]; exact lt_of_le_of_lt (le_max_left _ _) ht.1, by rw [hn]; exact ht.2⟩, rfl⟩

/-- §35.5: a quasiconformal extension `h̃` of `h` to an annulus `B_r` extends to a quasiconformal
self-map `f` of `Δ` with `f = h̃` on `B_{r₀}`, `r < r₀ < 1` (Beurling–Ahlfors).  Here `h` is a boundary
correspondence of `Δ` (the boundary values of some quasiconformal self-map of `Δ`).

**Correction.**  The hypothesis `hh` was missing, and the statement was **false**: nothing forced `h`
to map the unit circle onto itself (`r = 1/2`, `g z = z/2`, `h = G = ẑ/2` satisfy every other
hypothesis, but `HasBoundaryValues f h` needs `h 1` on the circle). -/
theorem annulus_extension_extends {h : ExtPlane → ExtPlane} (hh : ∃ f : ℂ → ℂ, HasBoundaryValues f h)
    {r : ℝ} (hr₀ : 0 < r) (hr : r < 1) {g : ℂ → ℂ}
    (hg : IsQuasiconformal g (annulus r 1)) (hgs : g '' annulus r 1 ⊆ unitDisc) {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g (annulus r 1) (g '' annulus r 1) G) (hGh : ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ = h ζ) :
    ∃ (f : ℂ → ℂ) (r₀ : ℝ), r < r₀ ∧ r₀ < 1 ∧ HasBoundaryValues f h ∧ EqOn f g (annulus r₀ 1) := by
  have _ := hr₀
  -- `h` maps the unit circle into itself
  obtain ⟨f₁, -, hf₁img, F₁, hF₁, hF₁h⟩ := hh
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ h ζ = u := fun ζ hζ => by
    obtain ⟨u, hu, hFu⟩ := s35a_x_ext_circle hF₁ hf₁img hζ
    exact ⟨u, hu, (hF₁h ζ hζ).symm.trans hFu⟩
  have hAo : IsOpen (annulus r 1) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAΔ : annulus r 1 ⊆ unitDisc := fun z hz => mem_ball_zero_iff.2 hz.2
  -- the measurable Riemann mapping theorem for `μ_g` on the collar, `0` inside
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨hμg, hgsol⟩ := thm10_2_genHomeoSolution_of_isKQC hKg
  have hKg1 : 1 ≤ Kg := hKg.2.1
  have hk0 : 0 ≤ (Kg - 1) / (Kg + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (Kg - 1) / (Kg + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  set ν : ℂ → ℂ := (annulus r 1).indicator (complexDilatation g) with hνdef
  have hν : IsBeltramiCoeff ν unitDisc ((Kg - 1) / (Kg + 1)) := by
    refine ⟨(((measurable_dzbar g).div (measurable_dz g)).indicator
      hAo.measurableSet).aestronglyMeasurable, ?_⟩
    have h1 : ∀ᵐ z ∂volume, z ∈ annulus r 1 → ‖complexDilatation g z‖ ≤ (Kg - 1) / (Kg + 1) :=
      (ae_restrict_iff' hAo.measurableSet).1 hμg.2
    filter_upwards [ae_restrict_of_ae h1] with z hz
    by_cases hzA : z ∈ annulus r 1
    · rw [hνdef, indicator_of_mem hzA]
      exact hz hzA
    · rw [hνdef, indicator_of_notMem hzA, norm_zero]
      exact hk0
  obtain ⟨w, hwK, hwimg, -, hwμ⟩ := thm13_6_riemann_mapping (D := unitDisc) isOpen_ball (isConnected_ball one_pos)
    neh_isHyperbolicSimplyConnected_unitDisc.2.2.1 neh_isHyperbolicSimplyConnected_unitDisc.2.2.2 hk0 hk1
    hν (mem_ball_self one_pos : (0 : ℂ) ∈ unitDisc)
  -- `g = φ ∘ w` on the collar with `φ` conformal
  have hwsol : IsGenHomeoSolution w (complexDilatation g) (annulus r 1) 2 := by
    obtain ⟨-, hhom, gg, hh', hpart, heq⟩ := thm10_2_genHomeoSolution_of_isKQC
      (ac_t_isKQC_restrict hwK hAo hAΔ)
    refine ⟨hhom, gg, hh', hpart, ?_⟩
    have hwμA : ∀ᵐ z ∂(volume.restrict (annulus r 1)), complexDilatation w z = complexDilatation g z := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hAΔ hwμ, ae_restrict_mem hAo.measurableSet]
        with z h1 h2
      rw [h1, hνdef, indicator_of_mem h2]
    filter_upwards [heq, hwμA] with z h1 h2
    rw [h1, h2]
  obtain ⟨φ, hφ, hφg⟩ := same_dilatation_conformal hAo hk1 hμg hwsol hgsol
  -- the boundary extension of `w` and of its inverse
  obtain ⟨W, hW⟩ := s13x_disc_extension ⟨_, hwK⟩ hwimg
  have hwinj : InjOn w unitDisc := hwK.2.2.1.2.1
  have hWinv := m35_isHomeoExtension_invFunOn hwinj hwimg hW
  set Wi := Function.invFunOn W (closure (toExt unitDisc)) with hWidef
  set wi := Function.invFunOn w unitDisc with hwidef
  have hwiimg : wi '' unitDisc = unitDisc := by
    conv_lhs => rw [← hwimg]
    exact hwinj.invFunOn_image subset_rfl
  -- a collar `ρ₀ < |y| < 1` inside `w(B_r)`
  have hwc : ContinuousOn w unitDisc := hwK.2.2.1.1
  have hsub1 : w '' closedBall 0 r ⊆ ball 0 1 := by
    rw [← unitDisc, ← hwimg]
    exact image_mono (closedBall_subset_ball hr)
  obtain ⟨ρa, hρa1, hρa⟩ := exists_lt_subset_ball
    ((isCompact_closedBall 0 r).image_of_continuousOn (hwc.mono (closedBall_subset_ball hr))).isClosed hsub1
  set ρ₀ : ℝ := max ρa (1 / 2) with hρ₀def
  have hρ₀1 : ρ₀ < 1 := max_lt hρa1 (by norm_num)
  have hρ₀pos : 0 < ρ₀ := lt_max_of_lt_right (by norm_num)
  have hcollar : ∀ y : ℂ, ρ₀ < ‖y‖ → ‖y‖ < 1 → y ∈ w '' annulus r 1 := by
    intro y h1 h2
    have hyΔ : y ∈ unitDisc := mem_ball_zero_iff.2 h2
    rw [← hwimg] at hyΔ
    obtain ⟨x, hx, rfl⟩ := hyΔ
    refine ⟨x, ⟨?_, mem_ball_zero_iff.1 hx⟩, rfl⟩
    by_contra hxr
    have := mem_ball_zero_iff.1 (hρa ⟨x, mem_closedBall_zero_iff.2 (not_lt.1 hxr), rfl⟩)
    linarith [le_max_left ρa (1 / 2)]
  have hwi_mem : ∀ y ∈ w '' annulus r 1, wi y ∈ annulus r 1 ∧ w (wi y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hwidef, hwinj.leftInvOn_invFunOn (hAΔ hx)]
    exact ⟨hx, rfl⟩
  -- the conformal map `τ₀ = g ∘ w⁻¹` on the collar, with its boundary values `G ∘ W⁻¹`
  set τ₀ : ℂ → ℂ := fun y => extToC (G (Wi (y : ExtPlane))) with hτ₀def
  have hτ₀φ : ∀ y ∈ w '' annulus r 1, τ₀ y = φ y := by
    intro y hy
    obtain ⟨hxA, hwx⟩ := hwi_mem y hy
    have hyΔ : y ∈ unitDisc := by rw [← hwimg]; exact image_mono hAΔ hy
    have h1 : Wi (y : ExtPlane) = ((wi y : ℂ) : ExtPlane) := hWinv.1 y hyΔ
    rw [hτ₀def]
    dsimp only
    rw [h1, hG.1 _ hxA, hφg _ hxA, hwx]
    rfl
  have hWcirc : ∀ ξ : ℂ, ‖ξ‖ = 1 → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ Wi (ξ : ExtPlane) = (ζ : ExtPlane) :=
    fun ξ hξ => s35a_x_ext_circle hWinv hwiimg hξ
  set Kc : Set ℂ := {y : ℂ | ρ₀ < ‖y‖ ∧ ‖y‖ ≤ 1} with hKcdef
  have hWiKc : ∀ y ∈ Kc, Wi (y : ExtPlane) ∈ closure (toExt (annulus r 1)) := by
    intro y hy
    rcases hy.2.lt_or_eq with h | h
    · obtain ⟨hxA, -⟩ := hwi_mem y (hcollar y hy.1 h)
      rw [hWinv.1 y (mem_ball_zero_iff.2 h)]
      exact subset_closure ⟨_, hxA, rfl⟩
    · obtain ⟨ζ, hζ, hWζ⟩ := hWcirc y h
      rw [hWζ]
      exact h35c_mem_closure_annulus hr hζ
  have hKcl : ∀ y ∈ Kc, (y : ExtPlane) ∈ closure (toExt unitDisc) := fun y hy => by
    rw [abN_closure_toExt_unitDisc]
    exact ⟨y, mem_closedBall_zero_iff.2 hy.2, rfl⟩
  have hGfin : ∀ y ∈ Kc, G (Wi (y : ExtPlane)) = ((τ₀ y : ℂ) : ExtPlane) := by
    intro y hy
    have hmem : G (Wi (y : ExtPlane)) ∈ closure (toExt unitDisc) := by
      have : G (Wi (y : ExtPlane)) ∈ closure (toExt (g '' annulus r 1)) :=
        hG.2.2.2 ▸ mem_image_of_mem G (hWiKc y hy)
      exact closure_mono (image_mono hgs) this
    rw [abN_closure_toExt_unitDisc] at hmem
    obtain ⟨c, -, hc⟩ := hmem
    rw [hτ₀def]
    dsimp only
    rw [← hc]
    rfl
  have hτ₀cont : ContinuousOn τ₀ Kc := by
    intro y hy
    have h1 : ContinuousWithinAt (fun y : ℂ => Wi (y : ExtPlane)) Kc y :=
      (hWinv.2.1 _ (hKcl y hy)).comp OnePoint.continuous_coe.continuousWithinAt (fun y hy => hKcl y hy)
    have h2 : ContinuousWithinAt (fun y : ℂ => G (Wi (y : ExtPlane))) Kc y :=
      ContinuousWithinAt.comp (f := fun y : ℂ => Wi (y : ExtPlane)) (hG.2.1 _ (hWiKc y hy)) h1
        (fun y hy => hWiKc y hy)
    have h3 := h35c_continuousAt_extToC (τ₀ y)
    rw [← hGfin y hy] at h3
    exact ContinuousAt.comp_continuousWithinAt (f := fun y : ℂ => G (Wi (y : ExtPlane))) h3 h2
  have hτ₀inj : InjOn τ₀ Kc := by
    intro y₁ hy₁ y₂ hy₂ heq
    have e1 : G (Wi (y₁ : ExtPlane)) = G (Wi (y₂ : ExtPlane)) := by
      rw [hGfin y₁ hy₁, hGfin y₂ hy₂, heq]
    have e2 := hG.2.2.1 (hWiKc y₁ hy₁) (hWiKc y₂ hy₂) e1
    have e3 := hWinv.2.2.1 (hKcl y₁ hy₁) (hKcl y₂ hy₂) e2
    exact OnePoint.coe_injective e3
  have hτ₀in : ∀ y : ℂ, ρ₀ < ‖y‖ → ‖y‖ < 1 → ‖τ₀ y‖ < 1 := by
    intro y h1 h2
    have hy := hcollar y h1 h2
    obtain ⟨hxA, hwx⟩ := hwi_mem y hy
    rw [hτ₀φ y hy, ← hwx, ← hφg _ hxA]
    exact mem_ball_zero_iff.1 (hgs ⟨_, hxA, rfl⟩)
  have hτ₀on : ∀ y : ℂ, ‖y‖ = 1 → ‖τ₀ y‖ = 1 := by
    intro y hy
    obtain ⟨ζ, hζ, hWζ⟩ := hWcirc y hy
    obtain ⟨u, hu, hhu⟩ := hcirc ζ hζ
    have := hGfin y ⟨by rw [hy]; exact hρ₀1, hy.le⟩
    rw [hWζ, hGh ζ hζ, hhu] at this
    rw [← OnePoint.coe_injective this]
    exact hu
  have hτ₀diff : DifferentiableOn ℂ τ₀ (annulus ρ₀ 1) := by
    have hwAo : annulus ρ₀ 1 ⊆ w '' annulus r 1 := fun y hy => hcollar y hy.1 hy.2
    exact (hφ.1.mono hwAo).congr fun y hy => hτ₀φ y (hwAo hy)
  -- a smaller collar on which `τ₀` does not vanish
  obtain ⟨ρ₁, hρ₀ρ₁, hρ₁1, hne₁⟩ : ∃ ρ₁ : ℝ, ρ₀ < ρ₁ ∧ ρ₁ < 1 ∧
      ∀ y : ℂ, ρ₁ < ‖y‖ → ‖y‖ ≤ 1 → τ₀ y ≠ 0 := by
    by_cases hz : ∃ y₀ : ℂ, ρ₀ < ‖y₀‖ ∧ ‖y₀‖ < 1 ∧ τ₀ y₀ = 0
    · obtain ⟨y₀, h1, h2, h3⟩ := hz
      refine ⟨(‖y₀‖ + 1) / 2, by linarith, by linarith, fun y hy1 hy2 h0 => ?_⟩
      have := hτ₀inj ⟨by linarith, hy2⟩ ⟨h1, h2.le⟩ (h0.trans h3.symm)
      rw [this] at hy1
      linarith
    · refine ⟨(ρ₀ + 1) / 2, by linarith, by linarith, fun y hy1 hy2 h0 => ?_⟩
      rcases hy2.lt_or_eq with h | h
      · exact hz ⟨y, by linarith, h, h0⟩
      · have := hτ₀on y h
        rw [h0, norm_zero] at this
        exact zero_ne_one this
  have hρ₁ : 0 < ρ₁ := hρ₀pos.trans hρ₀ρ₁
  have hKc₁ : {y : ℂ | ρ₁ < ‖y‖ ∧ ‖y‖ ≤ 1} ⊆ Kc := fun y hy => ⟨hρ₀ρ₁.trans hy.1, hy.2⟩
  -- reflection and cone fill-in
  obtain ⟨T, ρ, KT, -, hρ1, hTK, hTimg, hTeq, FT, hFT, hFTb⟩ := h35c_reflect_fill hρ₁ hρ₁1
    (hτ₀diff.mono fun y hy => ⟨hρ₀ρ₁.trans hy.1, hy.2⟩) (hτ₀cont.mono hKc₁) (hτ₀inj.mono hKc₁)
    hne₁ (fun y h1 h2 => hτ₀in y (hρ₀ρ₁.trans h1) h2) hτ₀on
  -- the radius `r₀`
  have hwic : ContinuousOn wi unitDisc := by
    have := hwK.2.2.1.2.2.2
    rwa [hwimg] at this
  have hwiΔ : ∀ y ∈ unitDisc, wi y ∈ unitDisc := fun y hy => by
    rw [← hwiimg]
    exact mem_image_of_mem wi hy
  have hsub2 : wi '' closedBall 0 ρ ⊆ ball 0 1 := image_subset_iff.2 fun y hy =>
    hwiΔ y (closedBall_subset_ball hρ1 hy)
  obtain ⟨rb, hrb1, hrb⟩ := exists_lt_subset_ball
    ((isCompact_closedBall 0 ρ).image_of_continuousOn (hwic.mono (closedBall_subset_ball hρ1))).isClosed hsub2
  have hwmaps : MapsTo w unitDisc unitDisc := fun z hz => hwimg ▸ mem_image_of_mem w hz
  refine ⟨T ∘ w, max rb ((r + 1) / 2), lt_max_of_lt_right (by linarith), max_lt hrb1 (by linarith), ?_, ?_⟩
  · refine ⟨⟨_, thm7_1_comp hwK hTK hwimg.subset⟩, by rw [image_comp, hwimg, hTimg], FT ∘ W,
      hFT.comp hW hwmaps, fun ζ hζ => ?_⟩
    obtain ⟨ξ, hξ, hWξ⟩ := s35a_x_ext_circle hW hwimg hζ
    have hWiξ : Wi (ξ : ExtPlane) = (ζ : ExtPlane) := by
      rw [← hWξ]
      exact hW.2.2.1.leftInvOn_invFunOn (s35a_x_mem_closure hζ)
    show FT (W ζ) = h ζ
    rw [hWξ, hFTb ξ hξ, ← hGfin ξ ⟨by rw [hξ]; exact hρ₀1, hξ.le⟩, hWiξ, hGh ζ hζ]
  · intro x hx
    have hxA : x ∈ annulus r 1 :=
      ⟨by linarith [le_max_right rb ((r + 1) / 2), hx.1], hx.2⟩
    have hwxΔ : w x ∈ unitDisc := hwmaps (hAΔ hxA)
    have hwxρ : ρ < ‖w x‖ := by
      by_contra hle
      have hmem : x ∈ wi '' closedBall 0 ρ :=
        ⟨w x, mem_closedBall_zero_iff.2 (not_lt.1 hle), hwinj.leftInvOn_invFunOn (hAΔ hxA)⟩
      have := mem_ball_zero_iff.1 (hrb hmem)
      linarith [le_max_left rb ((r + 1) / 2), hx.1]
    have hwx1 : ‖w x‖ < 1 := mem_ball_zero_iff.1 hwxΔ
    show T (w x) = g x
    rw [hTeq ⟨hwxρ, hwx1⟩, hτ₀φ (w x) ⟨x, hxA, rfl⟩, hφg x hxA]

/-! ### Helpers for `thm35_6` (`h35_`): Strebel's frame argument -/

/-- A homeomorphic boundary extension restricts to subdomains: `F` extends `f|_A : A → f(A)`. -/
theorem h35_homeoExt_restrict {f : ℂ → ℂ} {U V A : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) (hA : A ⊆ U) : IsHomeoExtension f A (f '' A) F := by
  obtain ⟨hFf, hFc, hFi, -⟩ := hF
  have hcl : closure (toExt A) ⊆ closure (toExt U) := closure_mono (image_mono hA)
  have himg : F '' toExt A = toExt (f '' A) := by
    ext p
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, ⟨z, hz, rfl⟩, (hFf z (hA hz)).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, hFf z (hA hz)⟩
  refine ⟨fun z hz => hFf z (hA hz), hFc.mono hcl, hFi.mono hcl, ?_⟩
  apply le_antisymm
  · rw [← himg]
    exact (hFc.mono hcl).image_closure
  · have hK : IsCompact (F '' closure (toExt A)) :=
      isClosed_closure.isCompact.image_of_continuousOn (hFc.mono hcl)
    rw [← himg]
    exact closure_minimal (image_mono subset_closure) hK.isClosed

/-- The annulus `B_r = {r < |z| < 1}` is open. -/
theorem h35_isOpen_annulus (r₁ r₂ : ℝ) : IsOpen (annulus r₁ r₂) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- `B_r ⊆ Δ`. -/
theorem h35_annulus_subset (r : ℝ) : annulus r 1 ⊆ unitDisc := fun z hz => by
  rw [unitDisc, mem_ball_zero_iff]
  exact hz.2

/-- **`H ≤ K₀`**: the boundary dilatation of `h` is at most `K[f₀]` for every q.c. self-map `f₀` of
`Δ` with boundary values `h` (restrict `f₀` to `B_{1/2}`). -/
theorem h35_boundaryDilatation_le {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane}
    (hf₀ : HasBoundaryValues f₀ h) : boundaryDilatation h ≤ maxDilatation f₀ unitDisc := by
  obtain ⟨⟨K, hK⟩, hs, F₀, hF₀, hF₀h⟩ := hf₀
  have hA := h35_annulus_subset (1 / 2)
  have hq : IsQuasiconformal f₀ (annulus (1 / 2) 1) :=
    ⟨K, ac_t_isKQC_restrict hK (h35_isOpen_annulus _ _) hA⟩
  have himg : f₀ '' annulus (1 / 2) 1 ⊆ unitDisc := (image_mono hA).trans hs.subset
  have hG := h35_homeoExt_restrict hF₀ hA
  calc boundaryDilatation h ≤ maxDilatation f₀ (annulus (1 / 2) 1) := by
        unfold boundaryDilatation
        exact iInf_le_of_le (1 / 2) (iInf_le_of_le f₀ (iInf_le_of_le
          ⟨by norm_num, by norm_num, hq, himg, F₀, hG, hF₀h⟩ le_rfl))
    _ ≤ maxDilatation f₀ unitDisc := by
        unfold maxDilatation
        exact essSup_mono_measure
          (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume hA))

/-! ### The Hamilton estimate for the first factor -/

/-- Upper bound for `∬ |φ| |1 - κφ/|φ||²/(1 - |κ|²)` along admissible `φ`: with `J = ∬ κφ` and
`m = ∬_{|κ| ≤ k'} |φ|`,
`∬ |φ| |1 - κφ/|φ||²/(1 - |κ|²) ≤ (1 - k)/(1 + k) + 2|Re J - k|/(1 - k²) + 2m/(1 - k²)² + 4(k - k')/(1 - k²)²`
(expansion `m35_expand`, `Δ`-bound `k²/(1 - k²)`, and `norm_integral_div_sub_le`). -/
theorem h35_first_factor_bound {κ φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc)) {k k' : ℝ} (hk1 : k < 1)
    (hk'0 : 0 ≤ k') (hk'k : k' ≤ k) (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ k) :
    ∫ z in unitDisc, ‖φ z‖ * (‖1 - κ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) ≤
      (1 - k) / (1 + k) + 2 / (1 - k ^ 2) * |(∫ z in unitDisc, κ z * φ z).re - k| +
        2 * (1 / (1 - k ^ 2) ^ 2 *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal +
          2 * (k - k') / (1 - k ^ 2) ^ 2) := by
  have hk0 : 0 ≤ k := hk'0.trans hk'k
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  obtain ⟨hDint, hIint⟩ := m35_integrable_terms hφ hκm hk0 hk1 hae
  obtain ⟨hφint, hφ1⟩ := integrableOn_norm_of_admissible hφ
  set P : ℂ → ℝ := fun z => ‖φ z‖ * (‖1 - κ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) with hP
  have hexp : ∀ᵐ z ∂(volume.restrict unitDisc), P z =
      ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) - 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    filter_upwards [hae] with z hz
    exact m35_expand (hz.trans_lt hk1)
  have hre_int : IntegrableOn (fun z => (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) unitDisc := by
    simpa using hIint.re
  have hre : ∫ z in unitDisc, (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re =
      (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    simpa using integral_re hIint
  have hsplit : ∫ z in unitDisc, P z = 1 + 2 * (∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) -
      2 * (∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    have hB2 : IntegrableOn (fun z => 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) unitDisc :=
      hDint.const_mul 2
    have hA1 : IntegrableOn (fun z => ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) unitDisc :=
      hφint.add hB2
    have hA2 : IntegrableOn (fun z => 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) unitDisc :=
      hre_int.const_mul 2
    rw [integral_congr_ae hexp, integral_sub hA1 hA2, integral_add hφint hB2, integral_const_mul,
      integral_const_mul, hφ1, hre]
  -- the `Δ`-term is at most `k²/(1 - k²)`
  have hD : ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤ k ^ 2 / (1 - k ^ 2) := by
    calc ∫ z in unitDisc, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)
        ≤ ∫ z in unitDisc, ‖φ z‖ * (k ^ 2 / (1 - k ^ 2)) := by
          refine integral_mono_ae hDint (hφint.mul_const _) ?_
          filter_upwards [hae] with z hz
          have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [div_le_div_iff₀ hp hq]
          nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
      _ = k ^ 2 / (1 - k ^ 2) := by rw [integral_mul_const, hφ1, one_mul]
  -- the `I`-term is at least `k/(1 - k²)` up to the errors
  have hI := norm_integral_div_sub_le hφ hκm hk1 hk'0 hk'k hae
  set I := ∫ z in unitDisc, κ z * φ z / (1 - ‖κ z‖ ^ 2) with hIdef
  set J := ∫ z in unitDisc, κ z * φ z with hJdef
  set E := 1 / (1 - k ^ 2) ^ 2 *
      (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal +
      2 * (k - k') / (1 - k ^ 2) ^ 2 with hEdef
  have hre1 : ((1 - k ^ 2)⁻¹ : ℝ) * J.re - E ≤ I.re := by
    have h1 := Complex.re_le_norm (((((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * J) - I)
    have h2 : ((((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * J - I).re = ((1 - k ^ 2)⁻¹ : ℝ) * J.re - I.re := by
      rw [Complex.sub_re, Complex.re_ofReal_mul]
    rw [h2, norm_sub_rev] at h1
    linarith
  have hre2 : k - |J.re - k| ≤ J.re := by
    have := neg_abs_le (J.re - k)
    linarith
  have hre3 : ((1 - k ^ 2)⁻¹ : ℝ) * (k - |J.re - k|) ≤ ((1 - k ^ 2)⁻¹ : ℝ) * J.re :=
    mul_le_mul_of_nonneg_left hre2 (inv_nonneg.2 hq.le)
  have hval : 1 + 2 * (k ^ 2 / (1 - k ^ 2)) - 2 * ((1 - k ^ 2)⁻¹ * k) = (1 - k) / (1 + k) := by
    field_simp
    ring
  have hval2 : 2 / (1 - k ^ 2) * |J.re - k| = 2 * ((1 - k ^ 2)⁻¹ * |J.re - k|) := by
    field_simp
  rw [hsplit, hval2]
  nlinarith

/-! ### The collar and its compact complement -/

/-- If `f₀, f` are q.c. self-maps of `Δ` and `0 < r₀ < 1`, the set of `z ∈ Δ` with `f₀(z) ∉ f(B_{r₀})`
lies in the compact set `f₀⁻¹(f(|w| ≤ r₀)) ⊆ Δ`. -/
theorem h35_collar_complement {f f₀ : ℂ → ℂ} {K K₀ : ℝ} (hK : IsKQC f unitDisc K)
    (hK₀ : IsKQC f₀ unitDisc K₀) (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc)
    {r₀ : ℝ} (hr₀ : r₀ < 1) :
    ∃ Kc : Set ℂ, IsCompact Kc ∧ Kc ⊆ unitDisc ∧
      ∀ z ∈ unitDisc, f₀ z ∉ f '' annulus r₀ 1 → z ∈ Kc := by
  have hcb : closedBall (0 : ℂ) r₀ ⊆ unitDisc := closedBall_subset_ball hr₀
  have hc1 : IsCompact (f '' closedBall (0 : ℂ) r₀) :=
    (isCompact_closedBall 0 r₀).image_of_continuousOn (hK.2.2.1.1.mono hcb)
  have hc1Δ : f '' closedBall (0 : ℂ) r₀ ⊆ unitDisc := (image_mono hcb).trans hfs.subset
  have hinv : ContinuousOn (Function.invFunOn f₀ unitDisc) unitDisc := by
    have h := hK₀.2.2.1.2.2.2
    rwa [hf₀s] at h
  refine ⟨Function.invFunOn f₀ unitDisc '' (f '' closedBall (0 : ℂ) r₀),
    hc1.image_of_continuousOn (hinv.mono hc1Δ), ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ f₀ '' unitDisc := by
      rw [hf₀s]
      exact hc1Δ hw
    exact Function.invFunOn_mem hw'
  · intro z hz hnot
    have hf₀z : f₀ z ∈ unitDisc := hf₀s ▸ mem_image_of_mem f₀ hz
    obtain ⟨x, hx, hxz⟩ : f₀ z ∈ f '' unitDisc := by rw [hfs]; exact hf₀z
    have hxr : x ∈ closedBall (0 : ℂ) r₀ := by
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      push Not at hlt
      have hx1 : ‖x‖ < 1 := by simpa [unitDisc] using hx
      exact hnot ⟨x, ⟨hlt, hx1⟩, hxz⟩
    refine ⟨f₀ z, ⟨x, hxr, hxz⟩, ?_⟩
    exact hK₀.2.2.1.2.1.leftInvOn_invFunOn hz

/-- A locally uniformly null sequence has vanishing integrals of `|φₙ|` over a compact `Kc ⊆ Δ`. -/
theorem h35_integral_compact_tendsto_zero {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcΔ : Kc ⊆ unitDisc)
    {φ : ℕ → ℂ → ℂ} (hφ : TendstoLocallyUniformlyOn φ 0 atTop unitDisc) :
    Tendsto (fun n => ∫ z in unitDisc, Kc.indicator (fun z => ‖φ n z‖) z) atTop (𝓝 0) := by
  have hKm : MeasurableSet Kc := hKc.isClosed.measurableSet
  have hunif : TendstoUniformlyOn φ 0 atTop Kc :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 hφ Kc hKcΔ hKc
  have hvol : volume Kc < ⊤ := hKc.measure_lt_top
  have heq : ∀ n, ∫ z in unitDisc, Kc.indicator (fun z => ‖φ n z‖) z = ∫ z in Kc, ‖φ n z‖ := by
    intro n
    rw [integral_indicator hKm, Measure.restrict_restrict hKm, inter_eq_left.2 hKcΔ]
  simp only [heq]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := volume.real Kc with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.1 hunif) (ε / (M + 1)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hb : ∀ z ∈ Kc, ‖‖φ n z‖‖ ≤ ε / (M + 1) := by
    intro z hz
    have h := hN n hn z hz
    rw [Pi.zero_apply, dist_zero_left] at h
    rw [norm_norm]
    exact h.le
  calc ‖∫ z in Kc, ‖φ n z‖‖ ≤ ε / (M + 1) * volume.real Kc :=
        norm_setIntegral_le_of_norm_le_const hvol hb
    _ = ε * (M / (M + 1)) := by rw [← hM]; ring
    _ < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one (by linarith)]
        linarith
    _ = ε := mul_one ε

/-! ### The dilatation of `f⁻¹` on the collar -/

/-- If `f` is `K`-q.c. on `B ⊆ Δ` (open) and injective on `Δ`, then `|μ_{f⁻¹}(f₀ z)| ≤ (K-1)/(K+1)`
for a.e. `z ∈ Δ` with `f₀(z) ∈ f(B)`, where `f⁻¹ = invFunOn f Δ` (it agrees with `invFunOn f B`
near every point of the open set `f(B)`) and the null exceptional set is pulled back by Lusin (N)
for `f₀⁻¹`. -/
theorem h35_kappa1_collar {f f₀ : ℂ → ℂ} {B : Set ℂ} {K K₀ : ℝ} (hBΔ : B ⊆ unitDisc)
    (hKB : IsKQC f B K) (hinj : InjOn f unitDisc) (hK₀ : IsKQC f₀ unitDisc K₀)
    (hf₀s : f₀ '' unitDisc = unitDisc) (hfB : f '' B ⊆ unitDisc) :
    ∀ᵐ z ∂(volume.restrict unitDisc), f₀ z ∈ f '' B → ‖mainIneqKappa₁ f f₀ z‖ ≤ (K - 1) / (K + 1) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hinvB : IsKQC (Function.invFunOn f B) (f '' B) K := thm7_2_inv hKB
  have hVo : IsOpen (f '' B) := hinvB.1
  -- `invFunOn f Δ = invFunOn f B` on `f(B)`
  have hagree : ∀ w ∈ f '' B, Function.invFunOn f unitDisc w = Function.invFunOn f B w := by
    rintro w ⟨x, hx, rfl⟩
    have h1 : Function.invFunOn f unitDisc (f x) = x := hinj.leftInvOn_invFunOn (hBΔ hx)
    have h2 : Function.invFunOn f B (f x) = x := (hinj.mono hBΔ).leftInvOn_invFunOn hx
    rw [h1, h2]
  have hcd : ∀ w ∈ f '' B, complexDilatation (Function.invFunOn f unitDisc) w =
      complexDilatation (Function.invFunOn f B) w := by
    intro w hw
    have hev : Function.invFunOn f unitDisc =ᶠ[𝓝 w] Function.invFunOn f B :=
      Filter.eventually_of_mem (hVo.mem_nhds hw) hagree
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]
  have hw := (isKQC_maxDilatation_le hinvB).2
  have hVm : MeasurableSet (f '' B) := hVo.measurableSet
  rw [ae_restrict_iff' hVm, ae_iff] at hw
  set N : Set ℂ := {w | ¬ (w ∈ f '' B →
    ‖complexDilatation (Function.invFunOn f B) w‖ ≤ (K - 1) / (K + 1))} with hN
  have hNsub : N ⊆ f₀ '' unitDisc := by
    intro w hw'
    rw [hf₀s]
    by_contra h
    exact hw' (fun h' => absurd (hfB h') h)
  have hnull : volume (Function.invFunOn f₀ unitDisc '' N) = 0 :=
    ac_n_volume_image_null_of_isKQC (thm7_2_inv hK₀) hNsub hw
  have hleft : LeftInvOn (Function.invFunOn f₀ unitDisc) f₀ unitDisc :=
    hK₀.2.2.1.2.1.leftInvOn_invFunOn
  rw [ae_restrict_iff' hΔ]
  filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzΔ hzV
  rw [mainIneqKappa₁, hcd _ hzV]
  by_contra hcon
  exact hz ⟨f₀ z, fun h => hcon (h hzV), hleft hzΔ⟩

/-! ### Strebel's frame argument -/

/-- **`thm35_6` from the annulus extension lemma** (axiom-clean core).  For an extremal `f₀` whose
dilatation has a degenerate Hamilton sequence, the boundary dilatation equals `K[f₀]`, provided every
q.c. collar extension of `h` extends to a q.c. self-map of `Δ` agreeing with it near `∂Δ` (`hext`,
the conclusion of `annulus_extension_extends` for this `h`). -/
theorem h35_thm35_6_of_ext {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : IsExtremalForBoundary f₀ h)
    {φ : ℕ → ℂ → ℂ} (hφ : IsDegenerateHamiltonSequence (complexDilatation f₀) φ)
    (hext : ∀ {r : ℝ}, 0 < r → r < 1 → ∀ {g : ℂ → ℂ}, IsQuasiconformal g (annulus r 1) →
      g '' annulus r 1 ⊆ unitDisc → ∀ {G : ExtPlane → ExtPlane},
      IsHomeoExtension g (annulus r 1) (g '' annulus r 1) G → (∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ = h ζ) →
      ∃ (f : ℂ → ℂ) (r₀ : ℝ), r < r₀ ∧ r₀ < 1 ∧ HasBoundaryValues f h ∧ EqOn f g (annulus r₀ 1)) :
    boundaryDilatation h = maxDilatation f₀ unitDisc := by
  refine le_antisymm (h35_boundaryDilatation_le hf₀.1) (not_lt.1 fun hlt => ?_)
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  set κ := complexDilatation f₀ with hκdef
  have hκ := m35_essSup_lt_one hf₀.1.1
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  set k := beltramiNormDisc κ with hkdef
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) :=
    ((measurable_dzbar f₀).div (measurable_dz f₀)).aestronglyMeasurable
  -- `K₀ = (1 + k)/(1 - k)`
  have hK₀eq : maxDilatation f₀ unitDisc = ENNReal.ofReal ((1 + k) / (1 - k)) :=
    le_antisymm (m35_maxDilatation_le hf₀.1.1) (m35_le_maxDilatation hf₀.1.1)
  -- a collar map `g` with `K[g] < K₀`
  unfold boundaryDilatation at hlt
  obtain ⟨r, hr⟩ := iInf_lt_iff.1 hlt
  obtain ⟨g, hg⟩ := iInf_lt_iff.1 hr
  obtain ⟨⟨hr0, hr1, hgq, hgs, G, hG, hGh⟩, hgK⟩ := iInf_lt_iff.1 hg
  obtain ⟨f, r₀, hrr₀, hr₀1, hfb, hfg⟩ := hext hr0 hr1 hgq hgs hG hGh
  have hAne : (annulus r 1).Nonempty := by
    refine ⟨(((r + 1) / 2 : ℝ) : ℂ), ?_⟩
    show r < ‖(((r + 1) / 2 : ℝ) : ℂ)‖ ∧ ‖(((r + 1) / 2 : ℝ) : ℂ)‖ < 1
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    constructor <;> linarith
  obtain ⟨Kg₀, hgKg₀⟩ := hgq
  have hmd1 : 1 ≤ maxDilatation g (annulus r 1) := UniversalTeichmuller.ut_md_one_le hgKg₀ hAne
  have hmdfin : maxDilatation g (annulus r 1) ≠ ⊤ := ne_top_of_lt hgK
  set Kg := (maxDilatation g (annulus r 1)).toReal with hKgdef
  have hKg1 : 1 ≤ Kg := by
    have := ENNReal.toReal_mono hmdfin hmd1
    rwa [ENNReal.toReal_one] at this
  have hKgeq : maxDilatation g (annulus r 1) = ENNReal.ofReal Kg := (ENNReal.ofReal_toReal hmdfin).symm
  have hKglt : Kg < (1 + k) / (1 - k) := by
    rw [hKgeq, hK₀eq] at hgK
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) (by linarith))).1 hgK
  -- `k > 0` (otherwise `K₀ = 1 ≤ K[g]`)
  have hkpos : 0 < k := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0] at hKglt
      norm_num at hKglt
      linarith
    · exact h0
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  -- `g` is `Kg`-q.c. on `B_r`, so `f` is `Kg`-q.c. on `B_{r₀}`
  have hgKQC : IsKQC g (annulus r 1) Kg :=
    s35a_isKQC_of_maxDilatation_le ⟨Kg₀, hgKg₀⟩ hKg1 hKgeq.le
  have hB₀sub : annulus r₀ 1 ⊆ annulus r 1 := fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hfKB : IsKQC f (annulus r₀ 1) Kg :=
    ad_isKQC_congr (ac_t_isKQC_restrict hgKQC (h35_isOpen_annulus _ _) hB₀sub) hfg
  -- the two maps
  obtain ⟨⟨Kf, hKf⟩, hfs, F, hF, hFh⟩ := hfb
  obtain ⟨⟨K₀', hK₀'⟩, hf₀s, F₀, hF₀, hF₀h⟩ := hf₀.1
  have hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ := fun ζ hζ => (hFh ζ hζ).trans (hF₀h ζ hζ).symm
  have hfBΔ : f '' annulus r₀ 1 ⊆ unitDisc :=
    (image_mono (h35_annulus_subset r₀)).trans hfs.subset
  -- the collar estimate for `κ₁` and its compact complement
  set c₁ := (Kg - 1) / (Kg + 1) with hc₁
  have hc₁1 : c₁ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hc₁K : (1 + c₁) / (1 - c₁) = Kg := by
    rw [hc₁]
    field_simp
    ring
  have hcol := h35_kappa1_collar (h35_annulus_subset r₀) hfKB hKf.2.2.1.2.1 hK₀' hf₀s hfBΔ
  set cf := (Kf - 1) / (Kf + 1) with hcf
  have hKf1 : 1 ≤ Kf := hKf.2.1
  have hcf1 : cf < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hcf0 : 0 ≤ cf := div_nonneg (by linarith) (by linarith)
  have hk1all := m35_kappa1_ae_le hKf hK₀' hfs hf₀s
  obtain ⟨Kc, hKc, hKcΔ, hKcmem⟩ := h35_collar_complement hKf hK₀' hfs hf₀s hr₀1
  have hKcm : MeasurableSet Kc := hKc.isClosed.measurableSet
  set C : ℝ := (1 + k) / (1 - k) * ((1 + cf) / (1 - cf)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (div_nonneg (by linarith) (by linarith))
    (div_nonneg (by linarith) (by linarith))
  -- per `n`: `1 ≤ Kg Pₙ + C Eₙ`
  obtain ⟨⟨hadm, hlim⟩, hloc⟩ := hφ
  set P : ℕ → ℝ := fun n => ∫ z in unitDisc,
    ‖φ n z‖ * (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) with hPdef
  set E : ℕ → ℝ := fun n => ∫ z in unitDisc, Kc.indicator (fun z => ‖φ n z‖) z with hEdef
  have hmain : ∀ n, 1 ≤ Kg * P n + C * E n := by
    intro n
    have hφn := hadm n
    have hmi := thm35_2_main_inequality ⟨Kf, hKf⟩ ⟨K₀', hK₀'⟩ hfs hf₀s hF hF₀ hbd hφn.1
    rw [hφn.2] at hmi
    obtain ⟨hDint, hIint⟩ := m35_integrable_terms hφn hκm hk0 hk1 hae
    obtain ⟨hφint, -⟩ := integrableOn_norm_of_admissible hφn
    have hre_int : IntegrableOn (fun z => (κ z * φ n z / (1 - ‖κ z‖ ^ 2)).re) unitDisc := by
      simpa using hIint.re
    have hPint : IntegrableOn (fun z => ‖φ n z‖ *
        (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) unitDisc := by
      refine ((hφint.add (hDint.const_mul 2)).sub (hre_int.const_mul 2)).congr ?_
      filter_upwards [hae] with z hz
      exact (m35_expand (hz.trans_lt hk1)).symm
    have hEint : IntegrableOn (fun z => Kc.indicator (fun z => ‖φ n z‖) z) unitDisc :=
      hφint.indicator hKcm
    have hRint : IntegrableOn (fun z => Kg * (‖φ n z‖ *
        (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) +
        C * Kc.indicator (fun z => ‖φ n z‖) z) unitDisc :=
      (hPint.const_mul Kg).add (hEint.const_mul C)
    have hpt : ∀ᵐ z ∂(volume.restrict unitDisc),
        ENNReal.ofReal (‖φ n z‖ *
          (‖1 - mainIneqKappa f₀ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖mainIneqKappa f₀ z‖ ^ 2)) *
          (‖1 - mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ n z / ‖φ n z‖) *
              (1 - conj (mainIneqKappa f₀ z) * conj (φ n z) / ‖φ n z‖) /
              (1 - mainIneqKappa f₀ z * φ n z / ‖φ n z‖)‖ ^ 2 / (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2))) ≤
        ENNReal.ofReal (Kg * (‖φ n z‖ *
          (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) +
          C * Kc.indicator (fun z => ‖φ n z‖) z) := by
      filter_upwards [hae, hcol, hk1all, ae_restrict_mem hΔ] with z hz hzcol hzall hzΔ
      refine ENNReal.ofReal_le_ofReal ?_
      have hτ : ‖mainIneqTau f₀ z‖ ≤ 1 := m35_norm_conj_div_le_one _
      set A := ‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2) with hA
      set Bf := ‖1 - mainIneqKappa₁ f f₀ z * mainIneqTau f₀ z * (φ n z / ‖φ n z‖) *
              (1 - conj (κ z) * conj (φ n z) / ‖φ n z‖) /
              (1 - κ z * φ n z / ‖φ n z‖)‖ ^ 2 / (1 - ‖mainIneqKappa₁ f f₀ z‖ ^ 2) with hBf
      have hA0 : 0 ≤ A := div_nonneg (sq_nonneg _) (by nlinarith [norm_nonneg (κ z)])
      have hAle : A ≤ (1 + k) / (1 - k) := by
        rw [hA, mul_div_assoc]
        exact m35_second_factor_le hk1 hz (m35_norm_div_norm_le_one _)
      have hB0 : 0 ≤ Bf := div_nonneg (sq_nonneg _)
        (by nlinarith [norm_nonneg (mainIneqKappa₁ f f₀ z), hzall, hcf1])
      have hBle : Bf ≤ (1 + cf) / (1 - cf) := m35_mainIneq_second_le hcf1 hzall hτ
      have hφA : 0 ≤ ‖φ n z‖ * A := mul_nonneg (norm_nonneg _) hA0
      show ‖φ n z‖ * A * Bf ≤ Kg * (‖φ n z‖ * A) + C * Kc.indicator (fun z => ‖φ n z‖) z
      by_cases hV : f₀ z ∈ f '' annulus r₀ 1
      · have hBg : Bf ≤ Kg := by
          rw [← hc₁K]
          exact m35_mainIneq_second_le hc₁1 (hzcol hV) hτ
        have hind : 0 ≤ Kc.indicator (fun z => ‖φ n z‖) z :=
          indicator_nonneg (fun _ _ => norm_nonneg _) z
        nlinarith [mul_le_mul_of_nonneg_left hBg hφA]
      · have hzK : z ∈ Kc := hKcmem z hzΔ hV
        rw [indicator_of_mem hzK]
        have h1 : ‖φ n z‖ * A * Bf ≤ ‖φ n z‖ * ((1 + k) / (1 - k)) * ((1 + cf) / (1 - cf)) := by
          have := mul_le_mul hAle hBle hB0 (div_nonneg (by linarith) (by linarith))
          calc ‖φ n z‖ * A * Bf = ‖φ n z‖ * (A * Bf) := by ring
            _ ≤ ‖φ n z‖ * ((1 + k) / (1 - k) * ((1 + cf) / (1 - cf))) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
        have h2 : ‖φ n z‖ * ((1 + k) / (1 - k)) * ((1 + cf) / (1 - cf)) = C * ‖φ n z‖ := by
          rw [hC]; ring
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Kg) hφA]
    have hR0 : ∀ᵐ z ∂(volume.restrict unitDisc), 0 ≤ Kg * (‖φ n z‖ *
        (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) +
        C * Kc.indicator (fun z => ‖φ n z‖) z := by
      filter_upwards [hae] with z hz
      have hA0 : 0 ≤ ‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2) :=
        div_nonneg (sq_nonneg _) (by nlinarith [norm_nonneg (κ z)])
      have hind : 0 ≤ Kc.indicator (fun z => ‖φ n z‖) z :=
        indicator_nonneg (fun _ _ => norm_nonneg _) z
      positivity
    have hle := hmi.trans (lintegral_mono_ae hpt)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hRint hR0, integral_add
      (hPint.const_mul Kg) (hEint.const_mul C), integral_const_mul, integral_const_mul,
      ← ENNReal.ofReal_one] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have := integral_nonneg_of_ae hR0
      rwa [integral_add (hPint.const_mul Kg) (hEint.const_mul C), integral_const_mul,
        integral_const_mul] at this)).1 hle
  -- the error terms
  have hEn : Tendsto E atTop (𝓝 0) := h35_integral_compact_tendsto_zero hKc hKcΔ hloc
  have hJre : Tendsto (fun n => |(∫ z in unitDisc, κ z * φ n z).re - k|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (∫ z in unitDisc, κ z * φ n z).re) atTop (𝓝 k) := by
      have h := (Complex.continuous_re.tendsto _).comp hlim
      rw [Complex.ofReal_re] at h
      exact h
    have h2 := (h1.sub_const k).abs
    simpa using h2
  -- for each `k' ∈ (0, k)`: `1 ≤ Kg ((1 - k)/(1 + k) + 4(k - k')/(1 - k²)²)`
  have hkey : ∀ k', 0 < k' → k' < k →
      1 - 4 * Kg / (1 - k ^ 2) ^ 2 * (k - k') ≤ Kg * ((1 - k) / (1 + k)) := by
    intro k' hk'0 hk'k
    have hm := lemma35_4 hκ hadm (Or.inr (Or.inl hlim)) hk'0 hk'k
    have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'},
        ENNReal.ofReal ‖φ n z‖).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
      rw [ENNReal.toReal_zero] at h
      exact h
    have hbound : ∀ n, 1 ≤ Kg * ((1 - k) / (1 + k) + 2 / (1 - k ^ 2) *
        |(∫ z in unitDisc, κ z * φ n z).re - k| + 2 * (1 / (1 - k ^ 2) ^ 2 *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal +
          2 * (k - k') / (1 - k ^ 2) ^ 2)) + C * E n := by
      intro n
      have h1 := hmain n
      have h2 := h35_first_factor_bound (hadm n) hκm hk1 hk'0.le hk'k.le hae
      nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ Kg)]
    have hL : Tendsto (fun n => Kg * ((1 - k) / (1 + k) + 2 / (1 - k ^ 2) *
        |(∫ z in unitDisc, κ z * φ n z).re - k| + 2 * (1 / (1 - k ^ 2) ^ 2 *
          (∫⁻ z in {z ∈ unitDisc | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal +
          2 * (k - k') / (1 - k ^ 2) ^ 2)) + C * E n) atTop
        (𝓝 (Kg * ((1 - k) / (1 + k) + 2 / (1 - k ^ 2) * 0 + 2 * (1 / (1 - k ^ 2) ^ 2 * 0 +
          2 * (k - k') / (1 - k ^ 2) ^ 2)) + C * 0)) := by
      refine ((((tendsto_const_nhds.add (tendsto_const_nhds.mul hJre)).add
        (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hmR).add tendsto_const_nhds)))).const_mul
        Kg).add (tendsto_const_nhds.mul hEn)
    have hlimle := ge_of_tendsto' hL hbound
    have e : Kg * ((1 - k) / (1 + k) + 2 / (1 - k ^ 2) * 0 + 2 * (1 / (1 - k ^ 2) ^ 2 * 0 +
          2 * (k - k') / (1 - k ^ 2) ^ 2)) + C * 0 =
        Kg * ((1 - k) / (1 + k)) + 4 * Kg / (1 - k ^ 2) ^ 2 * (k - k') := by
      field_simp
      ring
    rw [e] at hlimle
    linarith
  have hfinal : 1 ≤ Kg * ((1 - k) / (1 + k)) := le_of_forall_sub_mul_le hkpos hkey
  -- contradiction with `Kg < (1 + k)/(1 - k)`
  have h1k : 0 < 1 - k := by linarith
  have h1k' : 0 < 1 + k := by linarith
  have : Kg * ((1 - k) / (1 + k)) < 1 := by
    rw [mul_div_assoc', div_lt_one h1k']
    rw [lt_div_iff₀ h1k] at hKglt
    linarith
  linarith


/-- **Theorem 35.6** (35.13): if the complex dilatation `κ` of the extremal map for `h` has a
degenerate Hamilton sequence, then `H = K₀` (the boundary dilatation equals the extremal
dilatation). -/
theorem thm35_6 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : IsExtremalForBoundary f₀ h) {φ : ℕ → ℂ → ℂ}
    (hφ : IsDegenerateHamiltonSequence (complexDilatation f₀) φ) :
    boundaryDilatation h = maxDilatation f₀ unitDisc := by
  exact h35_thm35_6_of_ext hf₀ hφ fun {_} hr0 hr1 {_} hg hgs {_} hG hGh =>
    annulus_extension_extends ⟨f₀, hf₀.1⟩ hr0 hr1 hg hgs hG hGh

/-! ### Stage 0 (coordinator 553e2d): (35.14) for Hamilton sequences -/

/-- For `g` continuous on `Δ` with `phiArea g Δ < ⊤`, `‖g‖` is integrable on `Δ` and
`phiArea g Δ = ofReal ∫_Δ ‖g‖`. -/
theorem m35_integrableOn_norm_of_phiArea_lt_top {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc)
    (hA : phiArea g unitDisc < ⊤) :
    IntegrableOn (fun z => ‖g z‖) unitDisc ∧
      phiArea g unitDisc = ENNReal.ofReal (∫ z in unitDisc, ‖g z‖) := by
  have hm : AEStronglyMeasurable (fun z => ‖g z‖) (volume.restrict unitDisc) :=
    hg.norm.aestronglyMeasurable measurableSet_ball
  have hfin : HasFiniteIntegral (fun z => ‖g z‖) (volume.restrict unitDisc) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have hrw : ∀ z : ℂ, ‖‖g z‖‖ₑ = ENNReal.ofReal ‖g z‖ := by
      intro z
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [hrw]
    exact hA
  have hint : IntegrableOn (fun z => ‖g z‖) unitDisc := ⟨hm, hfin⟩
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => norm_nonneg _)]
  rfl

/-- (35.14): for a non-degenerate Hamilton sequence `φₙ → φ` (locally uniformly), `‖φ‖ ≤ 1` and
`lim ‖φₙ - φ‖ = 1 - ‖φ‖`; if `‖φ‖ < 1` then `(φₙ - φ)/‖φₙ - φ‖` is a degenerate Hamilton sequence.

**Correction.**  The bound `‖κ‖_∞ < 1` is stated on the essential supremum **in `ℝ≥0∞`**: the
earlier `beltramiNormDisc κ < 1` is also satisfied by an unbounded `κ`, since
`(⊤ : ℝ≥0∞).toReal = 0`.  See `eq35_8` for the discussion and the counterexample. -/
theorem eq35_14 {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1) {φn : ℕ → ℂ → ℂ}
    (hφ : IsHamiltonSequence κ φn)
    {φ : ℂ → ℂ} (hconv : TendstoLocallyUniformlyOn φn φ atTop unitDisc) :
    DifferentiableOn ℂ φ unitDisc ∧ phiArea φ unitDisc ≤ 1 ∧
      Tendsto (fun n => phiArea (fun z => φn n z - φ z) unitDisc) atTop (𝓝 (1 - phiArea φ unitDisc)) ∧
      (phiArea φ unitDisc < 1 → IsDegenerateHamiltonSequence κ
        fun n z => (φn n z - φ z) / ((phiArea (fun w => φn n w - φ w) unitDisc).toReal : ℂ)) := by
  obtain ⟨hadm, hlim⟩ := hφ
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hΔo : IsOpen unitDisc := isOpen_ball
  -- (1) the limit is holomorphic
  have hdiff : DifferentiableOn ℂ φ unitDisc :=
    hconv.differentiableOn (Filter.Eventually.of_forall fun n => (hadm n).1.1) hΔo
  have hcont : ContinuousOn φ unitDisc := hdiff.continuousOn
  have hpt : ∀ z ∈ unitDisc, Tendsto (fun n => φn n z) atTop (𝓝 (φ z)) := fun z hz =>
    hconv.tendsto_at hz
  -- (2) Fatou
  have hle1 : phiArea φ unitDisc ≤ 1 := by
    have hmeas : ∀ n, AEMeasurable (fun z => ENNReal.ofReal ‖φn n z‖) (volume.restrict unitDisc) :=
      fun n => ((hadm n).1.1.continuousOn.norm.aestronglyMeasurable hΔ).aemeasurable.ennreal_ofReal
    have h1 : ∀ n, ∫⁻ z in unitDisc, ENNReal.ofReal ‖φn n z‖ = 1 := fun n => (hadm n).2
    calc phiArea φ unitDisc
        = ∫⁻ z in unitDisc, liminf (fun n => ENNReal.ofReal ‖φn n z‖) atTop := by
          show ∫⁻ z in unitDisc, ENNReal.ofReal ‖φ z‖ = _
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem hΔ] with z hz
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            ((continuous_norm.tendsto _).comp (hpt z hz))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ z in unitDisc, ENNReal.ofReal ‖φn n z‖) atTop :=
          lintegral_liminf_le' hmeas
      _ = 1 := by
          simp only [h1]
          exact liminf_const 1
  -- (3) Brezis–Lieb
  obtain ⟨hint, hAeq⟩ :=
    m35_integrableOn_norm_of_phiArea_lt_top hcont (hle1.trans_lt ENNReal.one_lt_top)
  set a : ℝ := ∫ z in unitDisc, ‖φ z‖ with ha
  have ha0 : 0 ≤ a := integral_nonneg fun z => norm_nonneg _
  have hintn : ∀ n, IntegrableOn (fun z => ‖φn n z‖) unitDisc := fun n =>
    (integrableOn_norm_of_admissible (hadm n)).1
  have hint1 : ∀ n, ∫ z in unitDisc, ‖φn n z‖ = 1 := fun n =>
    (integrableOn_norm_of_admissible (hadm n)).2
  have hcontd : ∀ n, ContinuousOn (fun z => φn n z - φ z) unitDisc := fun n =>
    (hadm n).1.1.continuousOn.sub hcont
  have hintd : ∀ n, IntegrableOn (fun z => ‖φn n z - φ z‖) unitDisc := fun n =>
    Integrable.mono' ((hintn n).add hint) ((hcontd n).norm.aestronglyMeasurable hΔ)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact norm_sub_le _ _)
  have hAd : ∀ n, phiArea (fun z => φn n z - φ z) unitDisc =
      ENNReal.ofReal (∫ z in unitDisc, ‖φn n z - φ z‖) := fun n => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hintd n)
      (Filter.Eventually.of_forall fun z => norm_nonneg _)]
    rfl
  have hBL : Tendsto (fun n => ∫ z in unitDisc, ‖φn n z - φ z‖) atTop (𝓝 (1 - a)) := by
    have hG : Tendsto (fun n => ∫ z in unitDisc, (‖φn n z‖ - ‖φn n z - φ z‖)) atTop
        (𝓝 (∫ z in unitDisc, ‖φ z‖)) := by
      refine tendsto_integral_of_dominated_convergence (fun z => ‖φ z‖) (fun n => ?_) hint
        (fun n => ?_) ?_
      · exact ((hadm n).1.1.continuousOn.norm.sub (hcontd n).norm).aestronglyMeasurable hΔ
      · refine Filter.Eventually.of_forall fun z => ?_
        rw [Real.norm_eq_abs]
        calc |‖φn n z‖ - ‖φn n z - φ z‖| ≤ ‖φn n z - (φn n z - φ z)‖ := abs_norm_sub_norm_le _ _
          _ = ‖φ z‖ := by rw [sub_sub_cancel]
      · filter_upwards [ae_restrict_mem hΔ] with z hz
        have h1 := (continuous_norm.tendsto _).comp (hpt z hz)
        have h2 : Tendsto (fun n => ‖φn n z - φ z‖) atTop (𝓝 0) := by
          have h3 := (hpt z hz).sub_const (φ z)
          rw [sub_self] at h3
          simpa using h3.norm
        simpa using h1.sub h2
    have heq : ∀ n, ∫ z in unitDisc, ‖φn n z - φ z‖ =
        1 - ∫ z in unitDisc, (‖φn n z‖ - ‖φn n z - φ z‖) := fun n => by
      rw [integral_sub (hintn n) (hintd n), hint1 n]
      ring
    simp only [heq]
    exact tendsto_const_nhds.sub hG
  have hlimA : Tendsto (fun n => phiArea (fun z => φn n z - φ z) unitDisc) atTop
      (𝓝 (1 - phiArea φ unitDisc)) := by
    simp only [hAd]
    rw [hAeq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 ha0]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hBL
  refine ⟨hdiff, hle1, hlimA, fun hlt => ?_⟩
  -- (4) the degenerate Hamilton sequence
  have ha1 : a < 1 := by
    have h : ENNReal.ofReal a < ENNReal.ofReal 1 := by
      rw [← hAeq, ENNReal.ofReal_one]
      exact hlt
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).1 h
  set c : ℕ → ℝ := fun n => (phiArea (fun w => φn n w - φ w) unitDisc).toReal with hc
  have hcn : ∀ n, c n = ∫ z in unitDisc, ‖φn n z - φ z‖ := fun n => by
    simp only [hc]
    rw [hAd n, ENNReal.toReal_ofReal (integral_nonneg fun z => norm_nonneg _)]
  have hclow : ∀ n, 1 - a ≤ c n := fun n => by
    rw [hcn n, ← hint1 n, ha, ← integral_sub (hintn n) hint]
    exact integral_mono ((hintn n).sub hint) (hintd n) fun z => norm_sub_norm_le (φn n z) (φ z)
  have hcpos : ∀ n, 0 < c n := fun n => lt_of_lt_of_le (by linarith) (hclow n)
  have hclim : Tendsto c atTop (𝓝 (1 - a)) := by
    have e : c = fun n => ∫ z in unitDisc, ‖φn n z - φ z‖ := funext hcn
    rw [e]
    exact hBL
  -- admissibility of the normalized differences
  have hψadm : ∀ n, (fun z => (φn n z - φ z) / ((c n : ℝ) : ℂ)) ∈ integrableQD ∧
      phiArea (fun z => (φn n z - φ z) / ((c n : ℝ) : ℂ)) unitDisc = 1 := by
    intro n
    have harea : phiArea (fun z => (φn n z - φ z) / ((c n : ℝ) : ℂ)) unitDisc = 1 := by
      have hpw : ∀ z, ENNReal.ofReal ‖(φn n z - φ z) / ((c n : ℝ) : ℂ)‖ =
          ENNReal.ofReal ‖φn n z - φ z‖ * ENNReal.ofReal (c n)⁻¹ := fun z => by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hcpos n).le, div_eq_mul_inv,
          ENNReal.ofReal_mul (norm_nonneg _)]
      show ∫⁻ z in unitDisc, ENNReal.ofReal ‖(φn n z - φ z) / ((c n : ℝ) : ℂ)‖ = 1
      rw [lintegral_congr hpw, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      change phiArea (fun z => φn n z - φ z) unitDisc * _ = 1
      rw [hAd n, ← ENNReal.ofReal_mul (integral_nonneg fun z => norm_nonneg _), ← hcn n,
        mul_inv_cancel₀ (hcpos n).ne', ENNReal.ofReal_one]
    exact ⟨⟨((hadm n).1.1.sub hdiff).div_const _, harea ▸ ENNReal.one_lt_top⟩, harea⟩
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  -- the Hamilton property of the normalized differences
  have hHam : Tendsto (fun n => ∫ z in unitDisc, κ z * ((φn n z - φ z) / ((c n : ℝ) : ℂ))) atTop
      (𝓝 ((beltramiNormDisc κ : ℝ) : ℂ)) := by
    rcases hk0.eq_or_lt with hk | hk
    · -- `k = 0`: every integral vanishes
      have h0 : ∀ n, ∫ z in unitDisc, κ z * ((φn n z - φ z) / ((c n : ℝ) : ℂ)) = 0 := fun n => by
        have h := norm_integral_mul_le_of_admissible hκ (hψadm n)
        rw [← hk] at h
        exact norm_le_zero_iff.1 h
      simp only [h0, ← hk, Complex.ofReal_zero]
      exact tendsto_const_nhds
    · -- `k > 0`: `κ` is measurable and `∬ κφ = k‖φ‖`
      have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) := by
        have hne : ((beltramiNormDisc κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_ne.mem_nhds hne)).exists
        exact aestronglyMeasurable_of_integral_mul_ne_zero (hadm N) hN
      set k := beltramiNormDisc κ with hkdef
      have hφm : AEStronglyMeasurable φ (volume.restrict unitDisc) := hcont.aestronglyMeasurable hΔ
      have hκφ : IntegrableOn (fun z => κ z * φ z) unitDisc := by
        refine Integrable.mono' (hint.const_mul k) (hκm.mul hφm) ?_
        filter_upwards [hae] with z hz
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      have hκφn : ∀ n, IntegrableOn (fun z => κ z * φn n z) unitDisc := fun n => by
        refine Integrable.mono' ((hintn n).const_mul k)
          (hκm.mul ((hadm n).1.1.continuousOn.aestronglyMeasurable hΔ)) ?_
        filter_upwards [hae] with z hz
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      set B : ℂ := ∫ z in unitDisc, κ z * φ z with hB
      have hIφ : ∀ n, ∫ z in unitDisc, κ z * ((φn n z - φ z) / ((c n : ℝ) : ℂ)) =
          ((∫ z in unitDisc, κ z * φn n z) - B) / ((c n : ℝ) : ℂ) := fun n => by
        rw [hB, ← integral_sub (hκφn n) hκφ, ← integral_div]
        congr 1
        funext z
        ring
      have hbd : ∀ n, ‖(∫ z in unitDisc, κ z * φn n z) - B‖ ≤ k * c n := fun n => by
        rw [hB, ← integral_sub (hκφn n) hκφ, hcn n, ← integral_const_mul]
        refine norm_integral_le_of_norm_le ((hintd n).const_mul k) ?_
        filter_upwards [hae] with z hz
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      have hBle : ‖B‖ ≤ k * a := by
        rw [hB, ha, ← integral_const_mul]
        refine norm_integral_le_of_norm_le (hint.const_mul k) ?_
        filter_upwards [hae] with z hz
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      have hlimB : ‖(k : ℂ) - B‖ ≤ k * (1 - a) :=
        le_of_tendsto_of_tendsto' (hlim.sub_const B).norm (hclim.const_mul k) hbd
      -- equality in the triangle inequality: `B = k a`
      have hre1 : k - B.re ≤ k * (1 - a) := by
        have h := Complex.re_le_norm ((k : ℂ) - B)
        rw [Complex.sub_re, Complex.ofReal_re] at h
        linarith
      have hre2 : B.re ≤ ‖B‖ := Complex.re_le_norm B
      have hBre : B.re = k * a := by linarith
      have hBim : B.im = 0 := by
        have h1 : |B.re| = ‖B‖ := by
          refine le_antisymm (Complex.abs_re_le_norm B) ?_
          rw [hBre, abs_of_nonneg (mul_nonneg hk0 ha0)]
          exact hBle
        exact (Complex.abs_re_eq_norm).1 h1
      have hBeq : B = ((k * a : ℝ) : ℂ) := Complex.ext (by simp [hBre]) (by simp [hBim])
      simp only [hIφ]
      have hc' : Tendsto (fun n => ((c n : ℝ) : ℂ)) atTop (𝓝 ((1 - a : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp hclim
      have ha1' : ((1 - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 ha1).ne'
      have hfin := (hlim.sub_const B).div hc' ha1'
      have hval : ((k : ℂ) - B) / ((1 - a : ℝ) : ℂ) = (k : ℂ) := by
        rw [hBeq, div_eq_iff ha1']
        push_cast
        ring
      rw [hval] at hfin
      exact hfin
  -- local uniform convergence to `0`
  have hloc : TendstoLocallyUniformlyOn (fun n z => (φn n z - φ z) / ((c n : ℝ) : ℂ)) 0 atTop
      unitDisc := by
    rw [Metric.tendstoLocallyUniformlyOn_iff] at hconv ⊢
    intro ε hε z hz
    obtain ⟨t, ht, hev⟩ := hconv (ε * (1 - a)) (mul_pos hε (sub_pos.2 ha1)) z hz
    refine ⟨t, ht, hev.mono fun n hn y hy => ?_⟩
    have h1 := hn y hy
    rw [dist_comm, dist_eq_norm] at h1
    rw [Pi.zero_apply, dist_zero_left, norm_div, Complex.norm_real, Real.norm_of_nonneg (hcpos n).le,
      div_lt_iff₀ (hcpos n)]
    calc ‖φn n y - φ y‖ < ε * (1 - a) := h1
      _ ≤ ε * c n := mul_le_mul_of_nonneg_left (hclow n) hε.le
  exact ⟨⟨hψadm, hHam⟩, hloc⟩

/-! ### Helpers for `thm35_7` (`h35_`): Hamilton sequences, Montel, the equality case -/

/-! ### The mean value bound `π s² |φ(c)| ≤ ∬_Δ |φ|` -/

/-- For `φ` holomorphic on `Δ` and `‖c‖ + r < 1`, `2π |φ(c)| ≤ ∫_{-π}^{π} |φ(c + r e^{iθ})| dθ`
(the mean value property on the circle of radius `r` about `c`, as a lower integral). -/
theorem h35_circle_mean_le {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hcr : ‖c‖ + r < 1) :
    ENNReal.ofReal (2 * π * ‖φ c‖) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ‖φ (circleMap c r θ)‖ := by
  have hsub : closedBall c r ⊆ unitDisc := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [unitDisc, mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hdc : DiffContOnCl ℂ φ (ball c |r|) := by
    rw [abs_of_pos hr]
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hr.ne']
    exact hφ.mono hsub
  have hmv : Real.circleAverage φ c r = φ c := hdc.circleAverage
  have hle : ‖φ c‖ ≤ Real.circleAverage (fun z => ‖φ z‖) c r := by
    rw [← hmv]
    exact Real.norm_circleAverage_le_circleAverage_norm
  -- the circle is inside `Δ`, so `θ ↦ ‖φ(c + r e^{iθ})‖` is continuous
  have hcont : Continuous fun θ : ℝ => ‖φ (circleMap c r θ)‖ := by
    refine (continuous_norm.comp_continuousOn (hφ.continuousOn.mono hsub)).comp_continuous
      (continuous_circleMap c r) fun θ => ?_
    exact sphere_subset_closedBall (circleMap_mem_sphere c hr.le θ)
  have hint : ∫ θ in (0 : ℝ)..2 * π, ‖φ (circleMap c r θ)‖ =
      2 * π * Real.circleAverage (fun z => ‖φ z‖) c r := by
    rw [Real.circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]
  have h2pi : 0 ≤ 2 * π := Real.two_pi_pos.le
  -- `ofReal (∫₀^{2π}) = ∫⁻ over (0, 2π)`, then shift to `(-π, π)`
  have hlin : ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, ‖φ (circleMap c r θ)‖) =
      ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal ‖φ (circleMap c r θ)‖ := by
    rw [intervalIntegral.integral_of_le h2pi,
      ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun θ => norm_nonneg _)]
    exact setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hper : Function.Periodic (fun θ : ℝ => ENNReal.ofReal ‖φ (circleMap c r θ)‖) (2 * π) :=
    fun θ => by simp only [periodic_circleMap c r θ]
  rw [← lintegral_Ioo_zero_two_pi_eq_of_periodic hper, ← hlin, hint]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

/-- **Mean value bound**: for `φ` holomorphic on `Δ`, `0 < s`, `‖c‖ + s < 1`,
`π s² |φ(c)| ≤ ∬_Δ |φ|`. -/
theorem h35_meanvalue_bound {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hcs : ‖c‖ + s < 1) :
    ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖φ c‖ ≤ phiArea φ unitDisc := by
  rw [← lintegral_polar_indicator_phiArea hφ.continuousOn c]
  have hpt : ∀ r ∈ Ioo (0 : ℝ) s, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖φ c‖) ≤
      ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap c r θ) := by
    intro r hr
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (h35_circle_mean_le hφ hr.1 (by linarith [hr.2])).trans (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    have hmem : circleMap c r θ ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff]
      calc ‖circleMap c r θ‖ = ‖(circleMap c r θ - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖circleMap c r θ - c‖ + ‖c‖ := norm_add_le _ _
        _ = r + ‖c‖ := by
            rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr.1]
        _ < 1 := by linarith [hr.2]
    rw [indicator_of_mem hmem]
  calc ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖φ c‖
      = (∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r) * ENNReal.ofReal (2 * π * ‖φ c‖) := by
        have hr : ∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r = ENNReal.ofReal (s ^ 2 / 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((Continuous.integrableOn_Icc (f := fun r : ℝ => r) (a := 0) (b := s) continuous_id).mono_set
              Ioo_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r hr => hr.1.le))]
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le, integral_id]
          ring_nf
        rw [hr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖φ c‖) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) s, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap c r θ) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * unitDisc.indicator (fun z => ENNReal.ofReal ‖φ z‖) (circleMap c r θ) :=
        lintegral_mono_set Ioo_subset_Ioi_self

/-! ### Montel for locally bounded families -/

/-- A locally bounded family of holomorphic functions is equicontinuous at every point: scale by the
local bound to land in the unit disc and apply `RMT.equicontinuousAt_of_mapsTo_disc`. -/
theorem h35_equicontinuousAt_of_bound {U : Set ℂ} (f : ℕ → ℂ → ℂ)
    (hdiff : ∀ n, DifferentiableOn ℂ (f n) U) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδU : ball z δ ⊆ U)
    {M : ℝ} (hM : ∀ n, ∀ w ∈ ball z δ, ‖f n w‖ ≤ M) : EquicontinuousAt f z := by
  set C : ℝ := |M| + 1 with hC
  have hC0 : 0 < C := by positivity
  have hmap : ∀ n, MapsTo (fun w => f n w / (C : ℂ)) (ball z δ) RMT.disc := by
    intro n w hw
    rw [RMT.disc, mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hC0.le,
      div_lt_one hC0]
    linarith [hM n w hw, le_abs_self M]
  have he := RMT.equicontinuousAt_of_mapsTo_disc isOpen_ball (fun n w => f n w / (C : ℂ))
    (fun n => ((hdiff n).mono hδU).div_const _) hmap (mem_ball_self hδ)
  rw [Metric.equicontinuousAt_iff] at he ⊢
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := he (ε / C) (div_pos hε hC0)
  refine ⟨η, hη, fun w hw n => ?_⟩
  have h := hηε w hw n
  -- (beta-reduced form)
  rw [dist_eq_norm, ← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hC0.le,
    div_lt_div_iff_of_pos_right hC0] at h
  rw [dist_eq_norm]
  exact h

/-- **Montel** (locally bounded form): a locally uniformly bounded sequence of holomorphic functions
on an open `U` has a locally uniformly convergent subsequence with holomorphic limit.  (The proof of
`RMT.montel`, with the unit-disc bound replaced by local bounds.) -/
theorem h35_montel_loc {U : Set ℂ} (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hdiff : ∀ n, DifferentiableOn ℂ (f n) U)
    (hbd : ∀ z ∈ U, ∃ δ > 0, ball z δ ⊆ U ∧ ∃ M : ℝ, ∀ n, ∀ w ∈ ball z δ, ‖f n w‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun k => f (φ k)) g atTop U := by
  have hequi : ∀ z ∈ U, EquicontinuousAt f z := by
    intro z hz
    obtain ⟨δ, hδ, hδU, M, hM⟩ := hbd z hz
    exact h35_equicontinuousAt_of_bound f hdiff hδ hδU hM
  have hptb : ∀ z ∈ U, ∃ M : ℝ, ∀ n, ‖f n z‖ ≤ M := by
    intro z hz
    obtain ⟨δ, hδ, -, M, hM⟩ := hbd z hz
    exact ⟨M, fun n => hM n z (mem_ball_self hδ)⟩
  choose! Mb hMb using hptb
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hDc : (D₀ ∩ U).Countable := hD₀c.mono inter_subset_left
  have : Countable ↥(D₀ ∩ U) := hDc.to_subtype
  have hcpt : IsCompact (Set.pi (univ : Set ↥(D₀ ∩ U)) fun d => closedBall (0 : ℂ) (Mb d)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 _
  have hmem : ∀ n, (fun d : ↥(D₀ ∩ U) => f n d) ∈
      Set.pi (univ : Set ↥(D₀ ∩ U)) fun d => closedBall (0 : ℂ) (Mb d) := by
    intro n
    rw [Set.mem_univ_pi]
    intro d
    rw [mem_closedBall_zero_iff]
    exact hMb d d.2.2 n
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  rw [tendsto_pi_nhds] at hlim
  have hconv : ∀ z ∈ U, ∃ l : ℂ, Tendsto (fun k => f (φ k) z) atTop (𝓝 l) := by
    intro z hz
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.equicontinuousAt_iff.1 (hequi z hz) (ε / 3) (by positivity)
    obtain ⟨d, hdD, hdz, hdU⟩ : ∃ d ∈ D₀, d ∈ ball z δ ∧ d ∈ U := by
      obtain ⟨d, hd, hd2⟩ :=
        hD₀d.exists_mem_open (isOpen_ball.inter hU) ⟨z, mem_ball_self hδ, hz⟩
      exact ⟨d, hd, hd2.1, hd2.2⟩
    have hd : Tendsto (fun k => f (φ k) d) atTop (𝓝 (a ⟨d, hdD, hdU⟩)) := hlim ⟨d, hdD, hdU⟩
    rw [Metric.tendsto_atTop] at hd
    obtain ⟨N, hN⟩ := hd (ε / 6) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist (f (φ n) z) (f (φ n) d) < ε / 3 := hδε d (mem_ball.1 hdz) (φ n)
    have h3 : dist (f (φ N) d) (f (φ N) z) < ε / 3 := by
      rw [dist_comm]
      exact hδε d (mem_ball.1 hdz) (φ N)
    have h2 : dist (f (φ n) d) (f (φ N) d) < ε / 3 := by
      have hn2 : dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) < ε / 6 := hN n hn
      have hN2 : dist (f (φ N) d) (a ⟨d, hdD, hdU⟩) < ε / 6 := hN N le_rfl
      calc dist (f (φ n) d) (f (φ N) d)
          ≤ dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) + dist (a ⟨d, hdD, hdU⟩) (f (φ N) d) :=
            dist_triangle _ _ _
        _ = dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) + dist (f (φ N) d) (a ⟨d, hdD, hdU⟩) := by
            rw [dist_comm (a ⟨d, hdD, hdU⟩)]
        _ < ε / 6 + ε / 6 := add_lt_add hn2 hN2
        _ = ε / 3 := by ring
    calc dist (f (φ n) z) (f (φ N) z)
        ≤ dist (f (φ n) z) (f (φ n) d) + dist (f (φ n) d) (f (φ N) d)
            + dist (f (φ N) d) (f (φ N) z) := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
      _ = ε := by ring
  choose! g hg using hconv
  have hloc : TendstoLocallyUniformlyOn (fun k => f (φ k)) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    have hKeqAt : ∀ z ∈ K, EquicontinuousAt (fun k => f (φ k)) z := fun z hz V hV =>
      (hequi z (hKU hz) V hV).mono fun x hx i => hx (φ i)
    have hKeq : EquicontinuousOn (fun k => f (φ k)) K := fun z hz =>
      (hKeqAt z hz).equicontinuousWithinAt K
    have hpt : Tendsto (fun k => K.domRestrict (f (φ k))) atTop (𝓝 (K.domRestrict g)) := by
      rw [tendsto_pi_nhds]
      intro z
      exact hg z (hKU z.2)
    have hK1 : ∀ K' ∈ ({K} : Set (Set ℂ)), IsCompact K' := fun K' hK' =>
      (mem_singleton_iff.1 hK') ▸ hK
    have hK2 : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn (fun k => f (φ k)) K' :=
      fun K' hK' => (mem_singleton_iff.1 hK') ▸ hKeq
    have hunif := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' hK1 hK2 atTop g).2 (by
      rw [sUnion_singleton]
      exact hpt)
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hunif
    exact hunif K (mem_singleton K)
  have hgd : DifferentiableOn ℂ g U :=
    hloc.differentiableOn (Eventually.of_forall fun k => hdiff (φ k)) hU
  exact ⟨φ, hφ, g, hgd, hloc⟩

/-- Local bound for admissible `φ` (`∬_Δ |φ| = 1`): `|φ(w)| ≤ 1/(π s²)` whenever `‖w‖ + s < 1`. -/
theorem h35_norm_le_of_admissible {φ : ℂ → ℂ} (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    {w : ℂ} {s : ℝ} (hs : 0 < s) (hws : ‖w‖ + s < 1) : ‖φ w‖ ≤ 1 / (π * s ^ 2) := by
  have h := h35_meanvalue_bound hφ.1.1 hs hws
  rw [hφ.2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff zero_le_one] at h
  have hp : 0 < π * s ^ 2 := by positivity
  rw [le_div_iff₀ hp]
  linarith

/-- Admissible sequences are locally uniformly bounded on `Δ`. -/
theorem h35_admissible_locBounded {φn : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φn n ∈ integrableQD ∧ phiArea (φn n) unitDisc = 1) :
    ∀ z ∈ unitDisc, ∃ δ > 0, ball z δ ⊆ unitDisc ∧ ∃ M : ℝ, ∀ n, ∀ w ∈ ball z δ, ‖φn n w‖ ≤ M := by
  intro z hz
  rw [unitDisc, mem_ball_zero_iff] at hz
  set δ : ℝ := (1 - ‖z‖) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨δ, hδ0, fun w hw => ?_, 1 / (π * δ ^ 2), fun n w hw => ?_⟩
  · rw [mem_ball, dist_eq_norm] at hw
    rw [unitDisc, mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ < 1 := by linarith
  · rw [mem_ball, dist_eq_norm] at hw
    refine h35_norm_le_of_admissible (hφ n) hδ0 ?_
    calc ‖w‖ + δ = ‖(w - z) + z‖ + δ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ + δ := by linarith [norm_add_le (w - z) z]
      _ < 1 := by linarith

/-! ### Hamilton sequences and the equality case -/

/-- If `H[κ] = ‖κ‖_∞ = k > 0`, a Hamilton sequence exists: the supremum is a limit along admissible
`ψₙ` (`exists_seq_tendsto_hamiltonSup`), and rotating `ψₙ` by unimodular constants makes the
integrals `∬ κψₙ` real and equal to their moduli. -/
theorem h35_exists_hamiltonSeq {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hk : 0 < beltramiNormDisc κ) (hH : hamiltonH κ = beltramiNormDisc κ) :
    ∃ φ : ℕ → ℂ → ℂ, IsHamiltonSequence κ φ := by
  obtain ⟨hk0, -, -⟩ := beltramiNormDisc_facts hκ
  have hpos : 0 < ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1),
      ‖∫ z in unitDisc, κ z * φ z‖ := by
    change 0 < hamiltonH κ
    rw [hH]
    exact hk
  obtain ⟨ψ, hψS, hψlim⟩ := exists_seq_tendsto_hamiltonSup
    (G := fun φ => ‖∫ z in unitDisc, κ z * φ z‖) hk0
    (fun φ hφ => norm_integral_mul_le_of_admissible hκ hφ) hpos
  change Tendsto _ atTop (𝓝 (hamiltonH κ)) at hψlim
  rw [hH] at hψlim
  choose u hu1 hu using fun n => exists_unit_mul_eq_norm (∫ z in unitDisc, κ z * ψ n z)
  refine ⟨fun n z => u n * ψ n z, fun n => rotate_mem_hamiltonSet (hψS n) (hu1 n), ?_⟩
  have e : ∀ n, ∫ z in unitDisc, κ z * (u n * ψ n z) =
      ((‖∫ z in unitDisc, κ z * ψ n z‖ : ℝ) : ℂ) := by
    intro n
    rw [← hu n, ← integral_const_mul]
    congr 1
    funext z
    ring
  simp only [e]
  exact (Complex.continuous_ofReal.tendsto _).comp hψlim

/-- The equality case: if `|κ| ≤ k` a.e., `∬_Δ |φ| = 1` and `∬_Δ κφ = k`, then `κ = k φ̄/|φ|` a.e. -/
theorem h35_eq_case {κ φ : ℂ → ℂ} {k : ℝ} (_hk0 : 0 ≤ k)
    (hae : ∀ᵐ z ∂(volume.restrict unitDisc), ‖κ z‖ ≤ k)
    (hκm : AEStronglyMeasurable κ (volume.restrict unitDisc))
    (hφ : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1)
    (heq : ∫ z in unitDisc, κ z * φ z = (k : ℂ)) :
    ∀ᵐ z ∂(volume.restrict unitDisc), κ z = k * conj (φ z) / ‖φ z‖ := by
  obtain ⟨hφint, hφ1⟩ := integrableOn_norm_of_admissible hφ
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hφm : AEStronglyMeasurable φ (volume.restrict unitDisc) :=
    hφ.1.1.continuousOn.aestronglyMeasurable hΔ
  have hκφ : IntegrableOn (fun z => κ z * φ z) unitDisc := by
    refine Integrable.mono' (hφint.const_mul k) (hκm.mul hφm) ?_
    filter_upwards [hae] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  set g : ℂ → ℝ := fun z => k * ‖φ z‖ - (κ z * φ z).re with hg
  have hgint : IntegrableOn g unitDisc := (hφint.const_mul k).sub hκφ.re
  have hg0 : 0 ≤ᵐ[volume.restrict unitDisc] g := by
    filter_upwards [hae] with z hz
    simp only [Pi.zero_apply, hg, sub_nonneg]
    calc (κ z * φ z).re ≤ ‖κ z * φ z‖ := Complex.re_le_norm _
      _ = ‖κ z‖ * ‖φ z‖ := norm_mul _ _
      _ ≤ k * ‖φ z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hre_int : IntegrableOn (fun z => (κ z * φ z).re) unitDisc := hκφ.re
  have hgI : ∫ z in unitDisc, g z = 0 := by
    have e1 : ∫ z in unitDisc, g z =
        (∫ z in unitDisc, k * ‖φ z‖) - ∫ z in unitDisc, (κ z * φ z).re :=
      integral_sub (hφint.const_mul k) hre_int
    have e2 : ∫ z in unitDisc, (κ z * φ z).re = (∫ z in unitDisc, κ z * φ z).re :=
      integral_re hκφ
    rw [e1, e2, integral_const_mul, hφ1, heq]
    simp
  have hgae := (integral_eq_zero_iff_of_nonneg_ae hg0 hgint).1 hgI
  have hne := ae_ne_zero_of_differentiableOn_unitDisc hφ.1.1 (not_eqOn_zero_of_phiArea_eq_one hφ.2)
  filter_upwards [hgae, hae, hne] with z hz hzk hz0
  simp only [Pi.zero_apply, hg, sub_eq_zero] at hz
  -- `κφ = k|φ|`
  have hre : (κ z * φ z).re = k * ‖φ z‖ := hz.symm
  have hnorm : ‖κ z * φ z‖ ≤ k * ‖φ z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hzk (norm_nonneg _)
  have him : (κ z * φ z).im = 0 := by
    have h1 : (κ z * φ z).re ^ 2 + (κ z * φ z).im ^ 2 = ‖κ z * φ z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h2 : ‖κ z * φ z‖ ^ 2 ≤ (k * ‖φ z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [hre] at h1
    nlinarith [sq_nonneg (κ z * φ z).im]
  have hprod : κ z * φ z = ((k * ‖φ z‖ : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
  have hn : (‖φ z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hz0).ne'
  have hconj : φ z * conj (φ z) = ((‖φ z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  field_simp
  calc κ z * ↑‖φ z‖ = κ z * ↑‖φ z‖ * (φ z * conj (φ z)) / (↑‖φ z‖ ^ 2) := by
        rw [hconj]
        field_simp
    _ = (κ z * φ z) * conj (φ z) / ↑‖φ z‖ := by
        field_simp
    _ = ↑k * conj (φ z) := by
        rw [hprod]
        push_cast
        field_simp

/-- **The Teichmüller form (`k > 0`).**  If `H[κ] = ‖κ‖_∞ = k > 0` and `κ` has no degenerate
Hamilton sequence, then `κ = k φ̄/|φ|` for some `φ ∈ A(Δ)` with `‖φ‖ = 1`: a Hamilton sequence has a
locally uniformly convergent subsequence (Montel), whose limit has norm `1` by `eq35_14`, is its
norm limit, and so realizes `∬ κφ = k`; then the equality case applies. -/
theorem h35_teich_of_hamilton {κ : ℂ → ℂ}
    (hκ : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict unitDisc) < 1)
    (hk : 0 < beltramiNormDisc κ) (hH : hamiltonH κ = beltramiNormDisc κ)
    (hnd : ¬ ∃ φ : ℕ → ℂ → ℂ, IsDegenerateHamiltonSequence κ φ) :
    ∃ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), κ z = beltramiNormDisc κ * conj (φ z) / ‖φ z‖ := by
  obtain ⟨hk0, -, hae⟩ := beltramiNormDisc_facts hκ
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨ψ, hψadm, hψlim⟩ := h35_exists_hamiltonSeq hκ hk hH
  obtain ⟨σ, hσ, φ, hφd, hconv⟩ := h35_montel_loc isOpen_ball ψ (fun n => (hψadm n).1.1)
    (h35_admissible_locBounded hψadm)
  have hHam : IsHamiltonSequence κ (fun n => ψ (σ n)) :=
    ⟨fun n => hψadm (σ n), hψlim.comp hσ.tendsto_atTop⟩
  obtain ⟨-, hle1, hlimA, hdeg⟩ := eq35_14 hκ hHam hconv
  have h1 : phiArea φ unitDisc = 1 := by
    by_contra hne
    exact hnd ⟨_, hdeg (lt_of_le_of_ne hle1 hne)⟩
  have hφQD : φ ∈ integrableQD := ⟨hφd, by rw [h1]; exact ENNReal.one_lt_top⟩
  have hφadm : φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 := ⟨hφQD, h1⟩
  rw [h1, tsub_self] at hlimA
  set k := beltramiNormDisc κ with hkdef
  -- `κ` is measurable (a nonzero integral)
  have hκm : AEStronglyMeasurable κ (volume.restrict unitDisc) := by
    have hne : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    obtain ⟨N, hN⟩ := (hHam.2.eventually (isOpen_ne.mem_nhds hne)).exists
    exact aestronglyMeasurable_of_integral_mul_ne_zero (hψadm (σ N)) hN
  obtain ⟨hφint, -⟩ := integrableOn_norm_of_admissible hφadm
  have hintn : ∀ n, IntegrableOn (fun z => ‖ψ (σ n) z‖) unitDisc := fun n =>
    (integrableOn_norm_of_admissible (hψadm (σ n))).1
  have hκφ : IntegrableOn (fun z => κ z * φ z) unitDisc := by
    refine Integrable.mono' (hφint.const_mul k)
      (hκm.mul (hφd.continuousOn.aestronglyMeasurable hΔ)) ?_
    filter_upwards [hae] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hκφn : ∀ n, IntegrableOn (fun z => κ z * ψ (σ n) z) unitDisc := fun n => by
    refine Integrable.mono' ((hintn n).const_mul k)
      (hκm.mul ((hψadm (σ n)).1.1.continuousOn.aestronglyMeasurable hΔ)) ?_
    filter_upwards [hae] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hintd : ∀ n, IntegrableOn (fun z => ‖ψ (σ n) z - φ z‖) unitDisc := fun n =>
    Integrable.mono' ((hintn n).add hφint)
      (((hψadm (σ n)).1.1.continuousOn.sub hφd.continuousOn).norm.aestronglyMeasurable hΔ)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact norm_sub_le _ _)
  have hAd : ∀ n, phiArea (fun z => ψ (σ n) z - φ z) unitDisc =
      ENNReal.ofReal (∫ z in unitDisc, ‖ψ (σ n) z - φ z‖) := fun n => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hintd n)
      (Filter.Eventually.of_forall fun z => norm_nonneg _)]
    rfl
  have hdlim : Tendsto (fun n => ∫ z in unitDisc, ‖ψ (σ n) z - φ z‖) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlimA
    rw [ENNReal.toReal_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hAd n]
    exact ENNReal.toReal_ofReal (integral_nonneg fun z => norm_nonneg _)
  -- `∬ κφ = k`
  have hbd : ∀ n, ‖(∫ z in unitDisc, κ z * ψ (σ n) z) - ∫ z in unitDisc, κ z * φ z‖ ≤
      k * ∫ z in unitDisc, ‖ψ (σ n) z - φ z‖ := fun n => by
    rw [← integral_sub (hκφn n) hκφ, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hintd n).const_mul k) ?_
    filter_upwards [hae] with z hz
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hlim2 : Tendsto (fun n => ∫ z in unitDisc, κ z * ψ (σ n) z) atTop
      (𝓝 (∫ z in unitDisc, κ z * φ z)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
    simpa using hdlim.const_mul k
  have heq : ∫ z in unitDisc, κ z * φ z = (k : ℂ) := tendsto_nhds_unique hlim2 hHam.2
  exact ⟨φ, hφQD, h1, h35_eq_case hk0 hae hκm hφadm heq⟩

/-- **`thm35_7` from the Hamilton condition** (axiom-clean core): an extremal `f₀` with
`H[κ] = ‖κ‖_∞` whose dilatation has no degenerate Hamilton sequence is a Teichmüller map of finite
norm, and is the unique extremal map.  For `k = 0` the constant `φ = 1/π` serves. -/
theorem h35_thm35_7_of_hamilton {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane}
    (hf₀ : IsExtremalForBoundary f₀ h)
    (hH : hamiltonH (complexDilatation f₀) = beltramiNormDisc (complexDilatation f₀))
    (hnd : ¬ ∃ φ : ℕ → ℂ → ℂ, IsDegenerateHamiltonSequence (complexDilatation f₀) φ) :
    (∃ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        complexDilatation f₀ z = beltramiNormDisc (complexDilatation f₀) * conj (φ z) / ‖φ z‖) ∧
      ∀ f : ℂ → ℂ, IsExtremalForBoundary f h → EqOn f f₀ unitDisc := by
  have hκ := m35_essSup_lt_one hf₀.1.1
  obtain ⟨hk0, hk1, hae⟩ := beltramiNormDisc_facts hκ
  have hT : ∃ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f₀ z =
        beltramiNormDisc (complexDilatation f₀) * conj (φ z) / ‖φ z‖ := by
    rcases hk0.eq_or_lt with hk | hk
    · -- `k = 0`: `κ = 0` a.e., and `φ = 1/π` has norm `1`
      have harea : phiArea (fun _ : ℂ => ((π⁻¹ : ℝ) : ℂ)) unitDisc = 1 := by
        rw [phiArea, setLIntegral_const, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 Real.pi_pos.le), unitDisc, Complex.volume_ball,
          ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le), inv_mul_cancel₀ Real.pi_pos.ne',
          ENNReal.ofReal_one]
      refine ⟨fun _ => ((π⁻¹ : ℝ) : ℂ),
        ⟨differentiableOn_const _, by rw [harea]; exact ENNReal.one_lt_top⟩, harea, ?_⟩
      filter_upwards [hae] with z hz
      rw [← hk] at hz ⊢
      rw [norm_le_zero_iff.1 hz]
      simp
    · exact h35_teich_of_hamilton hκ hk hH hnd
  obtain ⟨φ, hφ, hφ1, hμ⟩ := hT
  refine ⟨⟨φ, hφ, hφ1, hμ⟩, fun f hf => ?_⟩
  obtain ⟨hq₀, hs₀, F₀, hF₀, hF₀h⟩ := hf₀.1
  obtain ⟨hq, hs, F, hF, hFh⟩ := hf.1
  have hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ := fun ζ hζ => (hFh ζ hζ).trans (hF₀h ζ hζ).symm
  have hRS := thm35_2_reich_strebel hφ hk0 hk1 hq₀ hs₀ hμ hq hs hF hF₀ hbd
  exact hRS.2 (le_antisymm (hf.2 f₀ hf₀.1) (hf₀.2 f hf.1))

/-- **Theorem 35.7**: if `f₀ : Δ → Δ` is extremal for the boundary values `h`, with complex
dilatation `κ`, and `κ` has no degenerate Hamilton sequence, then `f₀` is the unique extremal map
and it is a Teichmüller map: `κ = k φ̄/|φ|` with `φ` holomorphic, `‖φ‖ = 1`. -/
theorem thm35_7 {f₀ : ℂ → ℂ} {h : ExtPlane → ExtPlane} (hf₀ : IsExtremalForBoundary f₀ h)
    (hnd : ¬ ∃ φ : ℕ → ℂ → ℂ, IsDegenerateHamiltonSequence (complexDilatation f₀) φ) :
    (∃ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        complexDilatation f₀ z = beltramiNormDisc (complexDilatation f₀) * conj (φ z) / ‖φ z‖) ∧
      ∀ f : ℂ → ℂ, IsExtremalForBoundary f h → EqOn f f₀ unitDisc := by
  exact h35_thm35_7_of_hamilton hf₀ (thm35_5 hf₀) hnd

/-- **Theorem 35.8 (Strebel 标架准则)**: if the boundary dilatation of `h : ∂Δ → ∂Δ` satisfies `H < K₀`,
`K₀` the extremal dilatation, then the extremal map is a Teichmüller map and it is unique. -/
theorem thm35_8_strebel {h : ExtPlane → ExtPlane} {f₀ : ℂ → ℂ} (hf₀ : IsExtremalForBoundary f₀ h)
    (hlt : boundaryDilatation h < maxDilatation f₀ unitDisc) :
    (∃ φ : ℂ → ℂ, φ ∈ integrableQD ∧ phiArea φ unitDisc = 1 ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        complexDilatation f₀ z = beltramiNormDisc (complexDilatation f₀) * conj (φ z) / ‖φ z‖) ∧
      ∀ f : ℂ → ℂ, IsExtremalForBoundary f h → EqOn f f₀ unitDisc := by
  exact thm35_7 hf₀ fun ⟨_, hφ⟩ => hlt.ne (thm35_6 hf₀ hφ)

end LiZhongQC
