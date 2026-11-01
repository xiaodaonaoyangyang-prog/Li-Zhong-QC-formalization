import LiZhongQC.Lemmas.Conformal

/-!
# Carathéodory's extension theorem and prime ends

A formalization of the supplementary write-up `D:/lean/LZ3.txt` (not part of the book): the
boundary behaviour of a conformal map `f : Δ → Ω` of the unit disc onto a bounded simply
connected domain.  The book needs this in §2.1, where the strip map of Theorem 2.1 case (iii)
is normalized at prime ends.

**Part I.**
* `wolff_length_area` (Step 1): along suitable circles `|z - z₀| = ρₙ → 0` centred at a
  boundary point, the length `∫ |f'| |dz|` of the image arc tends to `0`.
* `tendsto_diam_image_circleShortArc` (Step 2): on a Jordan curve, points that come together
  are joined by arcs of vanishing diameter.
* the converse of Theorem C2, `isJordanCurve_frontier_of_isHomeoExtension`.  Theorem C2 itself
  (`caratheodory_jordan`) is proved in `Lemmas/CaratheodoryJordan.lean` (moved there 2026-09-25).
* Theorem C1, `caratheodory_continuous_iff`, is stated and proved in `Lemmas/PrimeEnds.lean` (moved there
  2026-09-27: its proof uses §20).

**Part II.** Crosscuts (`IsCrosscut`), null-chains (`IsNullChain`, with ends `chainEnd`),
their equivalence, prime ends (`PrimeEnd`), impressions (`chainImpression_isCompact_isConnected`) and principal
points.  `crosscut_separates` (proved with the Jordan curve theorem through `Lemmas/CaratheodoryJordan.lean`,
which is downstream of this file) and the open `principalPoints_isCompact_isConnected`, `caratheodory_primeEnd`
(prime ends correspond bijectively to boundary points of the disc, with impression equal to the cluster set) and
`locallyConnectedSpace_frontier_iff` are stated in `Lemmas/PrimeEnds.lean` (moved there 2026-09-27, so that the
proofs can use §20).

Deviations from the write-up, all for correctness:
* The end `Vₙ` of a null-chain is the component of `Ω ∖ Cₙ` containing `Cₙ₊₁` (the write-up's
  "component not containing `C₀`" is undefined for `n = 0`); separation of `C₀` from `Cₙ₊₁`
  includes that `C₀` is disjoint from `Cₙ`.
* Part II assumes `Ω` bounded: crosscuts here end at finite points and shrink in the Euclidean
  metric, so for unbounded domains the prime ends at `∞` would be missing.
* Not formalized: the topology on `Ω ∪ ∂_P Ω` (the correspondence is stated through the
  impression instead), the "four kinds" table (a case split once
  `principalPoints_isCompact_isConnected` is known), Collingwood's symmetry theorem, and the
  examples.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal Real

noncomputable section

namespace LiZhongQC

/-! ## Part I, Step 1: the length–area lemma (Wolff) -/

/-- The length `ℓ(ρ) = ∫_{C_ρ} |f'(z)| |dz|` of the image under `f` of the arc
`C_ρ = {z ∈ Δ : |z - z₀| = ρ}`, parametrized by `θ ↦ z₀ + ρ e^{iθ}`, `θ ∈ (-π, π]`. -/
def arcLength (f : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
    ‖deriv f (circleMap z₀ ρ θ)‖ₑ * ENNReal.ofReal ρ

/-! ### Cauchy–Schwarz on an arc -/

/-- `(∫ g)² ≤ μ(univ) · ∫ g²` — Cauchy–Schwarz with `1` as the other factor. -/
theorem sq_lintegral_le_measure_univ_mul_lintegral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    (∫⁻ a, g a ∂μ) ^ 2 ≤ μ univ * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hg
  simp only [Pi.mul_apply, one_mul, one_pow, lintegral_one, ENNReal.rpow_two] at h
  have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, g a ∂μ) ^ 2
      ≤ (μ univ ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = μ univ * ∫⁻ a, g a ^ 2 ∂μ := by rw [mul_pow, e, e]

/-- **Cauchy–Schwarz on an arc**: `ℓ(ρ)² ≤ 2πρ · ∫_{A_ρ} |f'|² ρ dθ`. -/
theorem sq_arcLength_le (f : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) :
    arcLength f z₀ ρ ^ 2 ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
      ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
        ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
  unfold arcLength
  have hmeas : AEMeasurable (fun θ : ℝ => ‖deriv f (circleMap z₀ ρ θ)‖ₑ * ENNReal.ofReal ρ)
      (volume.restrict {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc}) :=
    (((measurable_deriv f).comp (continuous_circleMap z₀ ρ).measurable).enorm.mul_const _).aemeasurable
  have h1 := sq_lintegral_le_measure_univ_mul_lintegral_sq (volume.restrict _) hmeas
  rw [Measure.restrict_apply_univ] at h1
  have hA : volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc}
      ≤ ENNReal.ofReal (2 * π) := by
    calc volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc} ≤ volume (Ioc (-π) π) :=
          measure_mono fun θ hθ => hθ.1
      _ = ENNReal.ofReal (2 * π) := by
          rw [Real.volume_Ioc]
          congr 1
          ring
  refine h1.trans ?_
  have h2 : ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
      (‖deriv f (circleMap z₀ ρ θ)‖ₑ * ENNReal.ofReal ρ) ^ 2
      = ENNReal.ofReal ρ * ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
          ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun θ => ?_
    ring
  rw [h2, ← mul_assoc]
  exact mul_le_mul_left (mul_le_mul_left hA _) _

/-! ### The area of the disc in polar coordinates about `z₀` -/

/-- Polar coordinates centred at `z₀`, for the indicator of the unit disc. -/
theorem lintegral_unitDisc_eq_polar (z₀ : ℂ) {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z in unitDisc, G z
      = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal ρ * unitDisc.indicator G (circleMap z₀ ρ θ) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  rw [← lintegral_indicator hD, ← lintegral_add_right_eq_self (unitDisc.indicator G) z₀]
  have hpolar := Complex.lintegral_comp_polarCoord_symm (fun w => unitDisc.indicator G (w + z₀))
  rw [← hpolar]
  simp_rw [smul_eq_mul]
  have hcont : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * unitDisc.indicator G (Complex.polarCoord.symm p + z₀))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    (measurable_fst.ennreal_ofReal.mul
      ((hG.indicator hD).comp (hcont.measurable.add_const z₀))).aemeasurable
  rw [show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  refine lintegral_congr fun ρ => lintegral_congr fun θ => ?_
  congr 2
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  push_cast
  ring

/-- The inner (angular) integral, rewritten as an integral over the arc `A_ρ` with the `(-π, π]`
convention of `arcLength`. -/
theorem lintegral_Ioo_indicator_eq_arc (z₀ : ℂ) (ρ : ℝ) (G : ℂ → ℝ≥0∞) :
    ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * unitDisc.indicator G (circleMap z₀ ρ θ)
      = ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
          G (circleMap z₀ ρ θ) * ENNReal.ofReal ρ := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hpt : ∀ θ : ℝ, ENNReal.ofReal ρ * unitDisc.indicator G (circleMap z₀ ρ θ)
      = (circleMap z₀ ρ ⁻¹' unitDisc).indicator
          (fun θ => G (circleMap z₀ ρ θ) * ENNReal.ofReal ρ) θ := by
    intro θ
    by_cases h : circleMap z₀ ρ θ ∈ unitDisc
    · rw [indicator_of_mem h, indicator_of_mem (show θ ∈ circleMap z₀ ρ ⁻¹' unitDisc from h),
        mul_comm]
    · rw [indicator_of_notMem h,
        indicator_of_notMem (show θ ∉ circleMap z₀ ρ ⁻¹' unitDisc from h), mul_zero]
  rw [lintegral_congr hpt, lintegral_indicator (hD.preimage (continuous_circleMap z₀ ρ).measurable),
    Measure.restrict_restrict (hD.preimage (continuous_circleMap z₀ ρ).measurable)]
  refine setLIntegral_congr ?_
  rw [inter_comm]
  exact ae_eq_set_inter Ioo_ae_eq_Ioc (ae_eq_refl _)

/-! ### The length–area estimate on `(δ, √δ)` -/

/-- **The length–area estimate.**  If `δ ∈ (0, 1)` and `b` exceeds `4π · Area(Ω) / log(1/δ)`, some
radius `ρ ∈ (δ, √δ)` has `ℓ(ρ)² < b`. -/
theorem exists_radius_sq_arcLength_lt {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (z₀ : ℂ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {b : ℝ}
    (hb : (volume Ω).toReal * (4 * π) / Real.log (1 / δ) < b) :
    ∃ ρ ∈ Ioo δ (Real.sqrt δ), arcLength f z₀ ρ ^ 2 < ENNReal.ofReal b := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  -- the area of `Ω` is finite and equals `∫_Δ |f'|²`
  have hDo : IsOpen unitDisc := by
    unfold unitDisc
    exact isOpen_ball
  have harea : ∫⁻ z in unitDisc, ‖deriv f z‖ₑ ^ 2 = volume Ω := by
    have h := lintegral_image_conformal hDo hf (fun _ => 1)
    simp only [mul_one, setLIntegral_one] at h
    exact h.symm
  have hfin : volume Ω < ⊤ := by
    obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : ℂ)
    exact lt_of_le_of_lt (measure_mono hR) measure_closedBall_lt_top
  -- polar coordinates: `Area = ∫₀^∞ J(ρ) dρ`
  have hpolar := lintegral_unitDisc_eq_polar z₀ ((measurable_deriv f).enorm.pow_const 2)
  simp_rw [lintegral_Ioo_indicator_eq_arc] at hpolar
  rw [harea] at hpolar
  -- the interval `(δ, √δ)`
  have hsqrt : δ < Real.sqrt δ := by
    rw [Real.lt_sqrt hδ0.le]
    nlinarith
  have hlog : 0 < Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_pos (one_lt_inv₀ hδ0 |>.2 hδ1)
  -- pointwise: `ofReal b · ofReal (1/ρ) ≤ ofReal (2π) · J ρ` on the interval
  have hpt : ∀ ρ ∈ Ioo δ (Real.sqrt δ),
      ENNReal.ofReal b * ENNReal.ofReal (1 / ρ) ≤ ENNReal.ofReal (2 * π) *
        ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
          ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hδ0.trans hρ.1
    have h := (hcon ρ hρ).trans (sq_arcLength_le f z₀ ρ)
    have hρρ : ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ) = 1 := by
      rw [← ENNReal.ofReal_mul hρ0.le, mul_one_div_cancel hρ0.ne', ENNReal.ofReal_one]
    calc ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
        ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) * ENNReal.ofReal (1 / ρ) :=
          mul_le_mul_left h _
      _ = ENNReal.ofReal (2 * π) *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) *
            (ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ)) := by ring
      _ = _ := by rw [hρρ, mul_one]
  -- integrate over `(δ, √δ)`
  have hint : ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
      ≤ ENNReal.ofReal (2 * π) * volume Ω := by
    calc ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
        ≤ ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal (2 * π) *
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
          exact hpt ρ hρ
      _ = ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioo δ (Real.sqrt δ),
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioi (0 : ℝ),
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ :=
          mul_le_mul_right (lintegral_mono_set fun ρ (hρ : ρ ∈ Ioo δ (Real.sqrt δ)) => hδ0.trans hρ.1) _
      _ = ENNReal.ofReal (2 * π) * volume Ω := by rw [← hpolar]
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  -- the left side is `ofReal b · log(√δ/δ) = ofReal (b · log(1/δ) / 2)`
  have hleft : ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
      = ENNReal.ofReal (b * (Real.log (1 / δ) / 2)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hInt : IntegrableOn (fun ρ : ℝ => 1 / ρ) (Ioo δ (Real.sqrt δ)) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
      exact continuousOn_const.div continuousOn_id fun ρ hρ => (hδ0.trans_le hρ.1).ne'
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo δ (Real.sqrt δ))] fun ρ => 1 / ρ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
      exact (one_div_pos.2 (hδ0.trans hρ.1)).le
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, ← ENNReal.ofReal_mul ?_]
    · congr 1
      rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hsqrt.le]
      simp_rw [one_div]
      rw [integral_inv (Set.notMem_uIcc_of_lt hδ0 (Real.sqrt_pos.2 hδ0)), Real.log_div
        (Real.sqrt_pos.2 hδ0).ne' hδ0.ne', Real.log_sqrt hδ0.le, Real.log_inv]
      ring
    · exact hb0
  -- conclude in `ℝ`
  have hRHS : ENNReal.ofReal (2 * π) * volume Ω = ENNReal.ofReal (2 * π * (volume Ω).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π), ENNReal.ofReal_toReal hfin.ne]
  rw [hleft, hRHS, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
  -- `b · log(1/δ)/2 ≤ 2π · Area`, i.e. `b ≤ 4π · Area / log(1/δ)`, contradicting `hb`
  have : b ≤ (volume Ω).toReal * (4 * π) / Real.log (1 / δ) := by
    rw [le_div_iff₀ hlog]
    nlinarith [hint]
  exact absurd hb (not_lt.2 this)

/-- **Wolff's length–area lemma** (LZ3, Part I, Step 1).  For a conformal map `f` of the disc onto
a bounded domain and a boundary point `z₀`, there are radii `ρₙ ↓ 0` along which the image arcs
have length tending to `0`. -/
theorem wolff_length_area {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {z₀ : ℂ} (_hz₀ : ‖z₀‖ = 1) :
    ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ (∀ n, 0 < ρ n) ∧ Tendsto ρ atTop (𝓝 0) ∧
      Tendsto (fun n => arcLength f z₀ (ρ n)) atTop (𝓝 0) := by
  -- the normalisation `‖z₀‖ = 1` plays no role in the estimate
  clear _hz₀
  -- `δₙ := exp(-2^(n+1))`, so that `√δₙ₊₁ = δₙ`; the bound `bₙ → 0`
  have hchoice : ∀ n : ℕ, ∃ ρ ∈ Ioo (Real.exp (-(2 : ℝ) ^ (n + 1)))
      (Real.sqrt (Real.exp (-(2 : ℝ) ^ (n + 1)))),
      arcLength f z₀ ρ ^ 2 < ENNReal.ofReal
        ((volume Ω).toReal * (4 * π) / (2 : ℝ) ^ (n + 1) + 1 / ((n : ℝ) + 1)) := by
    intro n
    refine exists_radius_sq_arcLength_lt hΩ hf z₀ (Real.exp_pos _) ?_ ?_
    · exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (by positivity))
    · rw [one_div, Real.exp_neg, inv_inv, Real.log_exp]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  choose ρ hρmem hρlt using hchoice
  have hsq : ∀ n : ℕ, Real.sqrt (Real.exp (-(2 : ℝ) ^ (n + 1))) = Real.exp (-(2 : ℝ) ^ n) := by
    intro n
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt fun n => ?_
    have h1 := (hρmem (n + 1)).2
    rw [hsq (n + 1)] at h1
    exact h1.trans (hρmem n).1
  · exact fun n => (Real.exp_pos _).trans (hρmem n).1
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => ((Real.exp_pos _).trans (hρmem n).1).le) (fun n => (hρmem n).2.le)
    simp_rw [hsq]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  · have hb : Tendsto (fun n : ℕ => (volume Ω).toReal * (4 * π) / (2 : ℝ) ^ (n + 1) +
        1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (volume Ω).toReal * (4 * π) / (2 : ℝ) ^ (n + 1)) atTop
          (𝓝 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
        have h' := h.const_mul ((volume Ω).toReal * (4 * π))
        rw [mul_zero] at h'
        refine h'.congr fun n => ?_
        simp only [Function.comp_apply, one_div, inv_pow]
        rw [div_eq_mul_inv]
      simpa using h1.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hle : ∀ n, arcLength f z₀ (ρ n) ≤ ENNReal.ofReal (Real.sqrt
        ((volume Ω).toReal * (4 * π) / (2 : ℝ) ^ (n + 1) + 1 / ((n : ℝ) + 1))) := by
      intro n
      by_contra hlt
      rw [not_le] at hlt
      have hbn : 0 ≤ (volume Ω).toReal * (4 * π) / (2 : ℝ) ^ (n + 1) + 1 / ((n : ℝ) + 1) := by
        positivity
      have h2 := ENNReal.pow_lt_pow_left two_ne_zero hlt
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hbn] at h2
      exact absurd (hρlt n) (not_lt.2 h2.le)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    have h := ENNReal.tendsto_ofReal hb.sqrt
    simpa using h

/-! ## Part I, Step 2: small arcs of a Jordan curve -/

/-- The shorter arc of the unit circle from `a` to `b`: `t ↦ a e^{i t arg(b/a)}`, `t ∈ [0, 1]`. -/
def circleShortArc (a b : Circle) : Set Circle :=
  (fun t : ℝ => a * Circle.exp (t * arg ((b : ℂ) / a))) '' Icc 0 1

/-- **LZ3, Part I, Step 2.**  If `φ` parametrizes a Jordan curve and `φ(aₙ)`, `φ(bₙ)` come
together, then the image of the shorter arc between `aₙ` and `bₙ` has diameter tending to `0`. -/
theorem tendsto_diam_image_circleShortArc {φ : Circle → ℂ} (hφ : Continuous φ)
    (hinj : Function.Injective φ) {a b : ℕ → Circle}
    (hab : Tendsto (fun n => dist (φ (a n)) (φ (b n))) atTop (𝓝 0)) :
    Tendsto (fun n => Metric.diam (φ '' circleShortArc (a n) (b n))) atTop (𝓝 0) := by
  -- `φ` is a homeomorphism onto its compact range, so its inverse is uniformly continuous
  set e : Circle ≃ range φ := Equiv.ofInjective φ hinj with he
  have hec : Continuous e := by
    have h : Continuous fun x : Circle => (⟨φ x, Set.mem_range_self x⟩ : range φ) :=
      hφ.subtype_mk _
    exact h
  have : CompactSpace (range φ) := isCompact_iff_compactSpace.mp (isCompact_range hφ)
  set H : Circle ≃ₜ range φ := hec.homeoOfEquivCompactToT2 with hH
  have hHuc : UniformContinuous H.symm :=
    CompactSpace.uniformContinuous_of_continuous H.symm.continuous
  -- hence `aₙ` and `bₙ` come together on the circle
  have hdist : Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp hHuc ε hε
    filter_upwards [hab.eventually_lt_const hδ] with n hn
    rw [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg]
    have h2 := hδε (show dist (H (a n)) (H (b n)) < δ by rw [Subtype.dist_eq]; exact hn)
    rwa [H.symm_apply_apply, H.symm_apply_apply] at h2
  -- so the arguments `arg (bₙ / aₙ)` tend to `0`
  have hθ : Tendsto (fun n => arg ((b n : ℂ) / a n)) atTop (𝓝 0) := by
    have hq : Tendsto (fun n => ((b n : ℂ) / a n)) atTop (𝓝 1) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hdist.eventually_lt_const hε] with n hn
      have ha : (a n : ℂ) ≠ 0 := by
        intro h0
        have h1 := Circle.norm_coe (a n)
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hsub : (b n : ℂ) / a n - 1 = ((b n : ℂ) - a n) / a n := by
        rw [sub_div, div_self ha]
      rw [dist_eq_norm, hsub, norm_div, Circle.norm_coe, div_one, norm_sub_rev]
      have hn' : dist (a n : ℂ) (b n : ℂ) < ε := hn
      rw [dist_eq_norm] at hn'
      exact hn'
    have hcont : ContinuousAt arg (1 : ℂ) := Complex.continuousAt_arg Complex.one_mem_slitPlane
    have h := hcont.tendsto.comp hq
    rwa [Complex.arg_one] at h
  -- every point of the short arc is within `2 |arg (bₙ / aₙ)|` of `aₙ`
  have harc : ∀ n, |arg ((b n : ℂ) / a n)| ≤ 1 →
      ∀ p ∈ circleShortArc (a n) (b n), dist p (a n) ≤ 2 * |arg ((b n : ℂ) / a n)| := by
    intro n hθn p hp
    obtain ⟨t, ht, rfl⟩ := hp
    set θ : ℝ := arg ((b n : ℂ) / a n) with hθdef
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    show dist ((a n * Circle.exp (t * θ) : Circle) : ℂ) (a n : ℂ) ≤ 2 * |θ|
    rw [Circle.coe_mul, Circle.coe_exp, dist_eq_norm]
    have hsplit : (a n : ℂ) * exp (↑(t * θ) * I) - a n
        = (a n : ℂ) * (exp (↑(t * θ) * I) - 1) := by ring
    rw [hsplit, norm_mul, Circle.norm_coe, one_mul]
    have hnorm : ‖(↑(t * θ) * I : ℂ)‖ = |t| * |θ| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hle : ‖(↑(t * θ) * I : ℂ)‖ ≤ 1 := by
      rw [hnorm]
      exact (mul_le_of_le_one_left (abs_nonneg θ) ht1).trans hθn
    calc ‖exp (↑(t * θ) * I) - 1‖ ≤ 2 * ‖(↑(t * θ) * I : ℂ)‖ := Complex.norm_exp_sub_one_le hle
      _ = 2 * (|t| * |θ|) := by rw [hnorm]
      _ ≤ 2 * |θ| := by
          have := mul_le_of_le_one_left (abs_nonneg θ) ht1
          linarith
  -- uniform continuity of `φ` then makes the image arcs small
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hφ) (ε / 2) (by positivity)
  have hmin : (0 : ℝ) < min (δ / 4) 1 := lt_min (by positivity) one_pos
  filter_upwards [(Metric.tendsto_nhds.mp hθ) _ hmin] with n hn
  rw [Real.dist_0_eq_abs] at hn
  have hθ1 : |arg ((b n : ℂ) / a n)| ≤ 1 := (hn.trans_le (min_le_right _ _)).le
  have hθδ : |arg ((b n : ℂ) / a n)| < δ / 4 := hn.trans_le (min_le_left _ _)
  rw [Real.dist_0_eq_abs, abs_of_nonneg Metric.diam_nonneg]
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (C := ε / 2) (by positivity) ?_)
    (by linarith)
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hp' := harc n hθ1 p hp
  have hq' := harc n hθ1 q hq
  have hpq : dist p q < δ := by
    calc dist p q ≤ dist p (a n) + dist (a n) q := dist_triangle _ _ _
      _ = dist p (a n) + dist q (a n) := by rw [dist_comm (a n) q]
      _ < δ := by linarith
  exact (hδε hpq).le

/-! ## Part I: the converse of Theorem C2 (Theorem C1 is in `Lemmas/PrimeEnds.lean`) -/

/-- **Theorem C2, converse.**  If a conformal map of the disc onto `Ω` extends to a homeomorphism
of the closures in `ℂ̄`, the boundary of `Ω` in `ℂ̄` is a Jordan curve. -/
theorem isJordanCurve_frontier_of_isHomeoExtension {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f unitDisc Ω F) : IsJordanCurve (frontier (toExt Ω)) := by
  obtain ⟨hFf, hFc, hFi, hFimg⟩ := hF
  have hΔ : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔ
  have hΔo : IsOpen (toExt unitDisc) := OnePoint.isOpen_image_coe.mpr hΔ
  have hΩo' : IsOpen (toExt Ω) := OnePoint.isOpen_image_coe.mpr hΩo
  -- the closure of the disc in `ℂ̄` is the closed disc
  have hclos : closure (toExt unitDisc) = toExt (closedBall 0 1) := by
    apply Subset.antisymm
    · refine closure_minimal (Set.image_mono ball_subset_closedBall) ?_
      exact ((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed
    · have h := image_closure_subset_closure_image (s := unitDisc) OnePoint.continuous_coe
      rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero] at h
      exact h
  -- so its frontier is the image of the circle
  have hfr : frontier (toExt unitDisc) = toExt (sphere 0 1) := by
    rw [hΔo.frontier_eq, hclos]
    simp only [toExt, unitDisc]
    rw [← Set.image_sdiff OnePoint.coe_injective, Metric.closedBall_sdiff_ball]
  -- `F` maps the disc onto `Ω` and hence the frontier onto the frontier
  have hFΔ : F '' toExt unitDisc = toExt Ω := by
    rw [← hf.2.2]
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, ⟨z, hz, rfl⟩, (hFf z hz).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, hFf z hz⟩
  have hFfr : F '' frontier (toExt unitDisc) = frontier (toExt Ω) := by
    rw [hΔo.frontier_eq, hΩo'.frontier_eq, hFi.image_sdiff, hFimg,
      Set.inter_eq_right.mpr subset_closure, hFΔ]
  have hmem : ∀ ζ : Circle, ((ζ : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
    intro ζ
    rw [hclos]
    exact ⟨ζ, mem_closedBall_zero_iff.mpr (Circle.norm_coe ζ).le, rfl⟩
  refine ⟨fun ζ => F ((ζ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact hFc.comp_continuous (OnePoint.continuous_coe.comp continuous_subtype_val) hmem
  · intro ζ₁ ζ₂ h
    have h1 := hFi (hmem ζ₁) (hmem ζ₂) h
    exact Circle.coe_injective (OnePoint.coe_injective h1)
  · rw [← hFfr, hfr]
    ext y
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨((ζ : ℂ) : ExtPlane), ⟨ζ, mem_sphere_zero_iff_norm.mpr (Circle.norm_coe ζ), rfl⟩,
        rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-! ## Part II: crosscuts, null-chains and prime ends -/

/-- A **crosscut** of `Ω`: an open Jordan arc in `Ω` whose closure adds two (possibly equal)
boundary points of `Ω`. -/
def IsCrosscut (Ω C : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 = C ∧ C ⊆ Ω ∧
    γ 0 ∈ frontier Ω ∧ γ 1 ∈ frontier Ω

/-- The `n`-th **end** of a chain of crosscuts: the component of `Ω ∖ Cₙ` containing `Cₙ₊₁`. -/
def chainEnd (Ω : Set ℂ) (C : ℕ → Set ℂ) (n : ℕ) : Set ℂ :=
  ⋃ y ∈ C (n + 1), connectedComponentIn (Ω \ C n) y

/-- A **null-chain** of `Ω`: crosscuts with pairwise disjoint consecutive closures, each `Cₙ`
(`n ≥ 1`) separating `C₀` from `Cₙ₊₁`, and diameters tending to `0`. -/
def IsNullChain (Ω : Set ℂ) (C : ℕ → Set ℂ) : Prop :=
  (∀ n, IsCrosscut Ω (C n)) ∧
    (∀ n, Disjoint (closure (C n)) (closure (C (n + 1)))) ∧
    (∀ n, 1 ≤ n → Disjoint (C 0) (C n) ∧
      ∀ x ∈ C 0, ∀ y ∈ C (n + 1),
        connectedComponentIn (Ω \ C n) x ≠ connectedComponentIn (Ω \ C n) y) ∧
    Tendsto (fun n => Metric.diam (C n)) atTop (𝓝 0)

/-- Two null-chains are **equivalent** if the ends of each are eventually inside the ends of the
other. -/
def NullChainEquiv (Ω : Set ℂ) (C C' : ℕ → Set ℂ) : Prop :=
  (∀ m, ∃ n, chainEnd Ω C n ⊆ chainEnd Ω C' m) ∧ (∀ m, ∃ n, chainEnd Ω C' n ⊆ chainEnd Ω C m)

/-- The **prime ends** of `Ω`: null-chains up to equivalence. -/
def PrimeEnd (Ω : Set ℂ) : Type :=
  Quot fun c c' : {C : ℕ → Set ℂ // IsNullChain Ω C} => NullChainEquiv Ω c.1 c'.1

/-- The **impression** of a null-chain, `⋂ₙ closure Vₙ`. -/
def chainImpression (Ω : Set ℂ) (C : ℕ → Set ℂ) : Set ℂ :=
  ⋂ n, closure (chainEnd Ω C n)

/-- The **cluster set** of `f` at `ζ` from within `U`: `⋂_{r > 0} closure f(U ∩ B(ζ, r))`. -/
def clusterSet (f : ℂ → ℂ) (U : Set ℂ) (ζ : ℂ) : Set ℂ :=
  ⋂ r > (0 : ℝ), closure (f '' (U ∩ ball ζ r))

/-- Equivalent null-chains have the same impression, so the impression of a prime end is well
defined. -/
theorem chainImpression_eq_of_nullChainEquiv {Ω : Set ℂ} {C C' : ℕ → Set ℂ}
    (h : NullChainEquiv Ω C C') : chainImpression Ω C = chainImpression Ω C' := by
  obtain ⟨h1, h2⟩ := h
  unfold chainImpression
  apply Subset.antisymm
  · rw [Set.subset_iInter_iff]
    intro m
    obtain ⟨n, hn⟩ := h1 m
    exact (Set.iInter_subset _ n).trans (closure_mono hn)
  · rw [Set.subset_iInter_iff]
    intro m
    obtain ⟨n, hn⟩ := h2 m
    exact (Set.iInter_subset _ n).trans (closure_mono hn)

/-- The intersection of a decreasing sequence of compact preconnected subsets of a Hausdorff space
is preconnected. -/
theorem isPreconnected_iInter_of_antitone_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : ℕ → Set X} (hd : ∀ n, K (n + 1) ⊆ K n) (hc : ∀ n, IsCompact (K n))
    (hp : ∀ n, IsPreconnected (K n)) : IsPreconnected (⋂ n, K n) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsuv hdisj
  set S : Set X := ⋂ n, K n with hS
  have hSc : IsCompact S :=
    (hc 0).of_isClosed_subset (isClosed_iInter fun n => (hc n).isClosed) (Set.iInter_subset _ 0)
  have hAc : IsCompact (S ∩ u) := hSc.inter_right hu
  have hBc : IsCompact (S ∩ v) := hSc.inter_right hv
  have hAB : Disjoint (S ∩ u) (S ∩ v) := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    have h : x ∈ S ∩ (u ∩ v) := ⟨hxu.1, hxu.2, hxv.2⟩
    rw [hdisj] at h
    exact h
  by_cases hA : (S ∩ u).Nonempty
  · by_cases hB : (S ∩ v).Nonempty
    · exfalso
      obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact hAc hBc hAB
      -- no `Kₙ` lies in `U ∪ V`, so the sets `Kₙ \ (U ∪ V)` form a decreasing sequence of
      -- nonempty compact sets
      have hT : ∀ n, (K n \ (U ∪ V)).Nonempty := by
        intro n
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
        rcases (hp n).subset_or_subset hU hV hUV hcon with h | h
        · obtain ⟨x, hx⟩ := hB
          exact Set.disjoint_left.mp hUV (h (Set.iInter_subset _ n hx.1)) (hBV hx)
        · obtain ⟨x, hx⟩ := hA
          exact Set.disjoint_left.mp hUV (hAU hx) (h (Set.iInter_subset _ n hx.1))
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        (fun n => K n \ (U ∪ V)) (fun n => Set.sdiff_subset_sdiff_left (hd n)) hT
        ((hc 0).diff (hU.union hV)) (fun n => (hc n).isClosed.sdiff (hU.union hV))
      rw [Set.mem_iInter] at hx
      have hxS : x ∈ S := Set.mem_iInter.mpr fun n => (hx n).1
      have hxUV : x ∉ U ∪ V := (hx 0).2
      rcases hsuv hxS with hxu | hxv
      · exact hxUV (Or.inl (hAU ⟨hxS, hxu⟩))
      · exact hxUV (Or.inr (hBV ⟨hxS, hxv⟩))
    · left
      intro x hx
      rcases hsuv hx with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ hB
  · right
    intro x hx
    rcases hsuv hx with h | h
    · exact absurd ⟨x, hx, h⟩ hA
    · exact h

/-- The closure of a crosscut adds only frontier points of `Ω`: `closure C ⊆ C ∪ ∂Ω`. -/
theorem car3_closure_crosscut_subset {Ω C : Set ℂ} (h : IsCrosscut Ω C) :
    closure C ⊆ C ∪ frontier Ω := by
  obtain ⟨γ, hγc, -, hγC, -, h0, h1⟩ := h
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hγc
  have hsub : C ⊆ γ '' Icc 0 1 := hγC ▸ image_mono Ioo_subset_Icc_self
  intro x hx
  obtain ⟨t, ht, rfl⟩ := closure_minimal hsub hK.isClosed hx
  rcases eq_or_lt_of_le ht.1 with h | h
  · right
    rw [← h]
    exact h0
  · rcases eq_or_lt_of_le ht.2 with h' | h'
    · right
      rw [h']
      exact h1
    · left
      rw [← hγC]
      exact ⟨t, ⟨h, h'⟩, rfl⟩

/-- A crosscut of `Ω` lies in `Ω`. -/
theorem car3_crosscut_subset {Ω C : Set ℂ} (h : IsCrosscut Ω C) : C ⊆ Ω := by
  obtain ⟨γ, -, -, -, hCΩ, -⟩ := h
  exact hCΩ

/-- Removing a crosscut from an open set leaves an open set. -/
theorem car3_isOpen_diff_crosscut {Ω C : Set ℂ} (hΩo : IsOpen Ω) (h : IsCrosscut Ω C) :
    IsOpen (Ω \ C) := by
  have e : Ω \ C = Ω \ closure C := by
    apply Subset.antisymm
    · rintro x ⟨hxΩ, hxC⟩
      refine ⟨hxΩ, fun hcl => ?_⟩
      rcases car3_closure_crosscut_subset h hcl with h1 | h1
      · exact hxC h1
      · rw [hΩo.frontier_eq] at h1
        exact h1.2 hxΩ
    · exact Set.sdiff_subset_sdiff_right subset_closure
  rw [e]
  exact hΩo.sdiff isClosed_closure

/-- A crosscut is preconnected (a continuous image of `(0, 1)`). -/
theorem car3_crosscut_isPreconnected {Ω C : Set ℂ} (h : IsCrosscut Ω C) : IsPreconnected C := by
  obtain ⟨γ, hγc, -, hγC, -⟩ := h
  rw [← hγC]
  exact isPreconnected_Ioo.image γ (hγc.mono Ioo_subset_Icc_self)

/-- A crosscut is nonempty. -/
theorem car3_crosscut_nonempty {Ω C : Set ℂ} (h : IsCrosscut Ω C) : C.Nonempty := by
  obtain ⟨γ, -, -, hγC, -⟩ := h
  rw [← hγC]
  exact (nonempty_Ioo.2 zero_lt_one).image γ

/-- The closure of a component of `Ω ∖ C` meets the crosscut `C` (else the component is clopen in
`Ω`). -/
theorem car3_closure_cc_inter {Ω C : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (h : IsCrosscut Ω C) {x : ℂ} (hx : x ∈ Ω \ C) :
    (closure (connectedComponentIn (Ω \ C) x) ∩ C).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  have hO := car3_isOpen_diff_crosscut hΩo h
  set W := connectedComponentIn (Ω \ C) x with hWdef
  have hWo : IsOpen W := hO.connectedComponentIn
  have hWcl : ∀ z ∈ Ω, z ∈ closure W → z ∈ W := by
    intro z hzΩ hzcl
    have hzC : z ∉ C := fun hzC => by
      have : z ∈ closure W ∩ C := ⟨hzcl, hzC⟩
      rw [hcon] at this
      exact this
    have hzo : IsOpen (connectedComponentIn (Ω \ C) z) := hO.connectedComponentIn
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.1 hzcl _ hzo (mem_connectedComponentIn ⟨hzΩ, hzC⟩)
    have e1 := connectedComponentIn_eq hu1
    have e2 := connectedComponentIn_eq hu2
    rw [hWdef, e2, ← e1]
    exact mem_connectedComponentIn ⟨hzΩ, hzC⟩
  obtain ⟨c, hc⟩ := car3_crosscut_nonempty h
  have hcW : c ∉ closure W := fun hcW => by
    have : c ∈ closure W ∩ C := ⟨hcW, hc⟩
    rw [hcon] at this
    exact this
  have hcov : Ω ⊆ W ∪ (closure W)ᶜ := by
    intro z hz
    by_cases hzcl : z ∈ closure W
    · exact Or.inl (hWcl z hz hzcl)
    · exact Or.inr hzcl
  obtain ⟨z, -, hzW, hzW'⟩ := hΩc W (closure W)ᶜ hWo isClosed_closure.isOpen_compl hcov
    ⟨x, hx.1, mem_connectedComponentIn hx⟩ ⟨c, car3_crosscut_subset h hc, hcW⟩
  exact hzW' (subset_closure hzW)

/-- A chain end is a single component: that of any point of the next crosscut. -/
theorem car3_chainEnd_eq {Ω : Set ℂ} {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) {y : ℂ}
    (hy : y ∈ C (n + 1)) : chainEnd Ω C n = connectedComponentIn (Ω \ C n) y := by
  obtain ⟨hcc, hdisj, -, -⟩ := hC
  have hsub : C (n + 1) ⊆ Ω \ C n := fun z hz =>
    ⟨car3_crosscut_subset (hcc (n + 1)) hz,
      fun hzn => disjoint_left.1 (hdisj n) (subset_closure hzn) (subset_closure hz)⟩
  have hcomp : C (n + 1) ⊆ connectedComponentIn (Ω \ C n) y :=
    (car3_crosscut_isPreconnected (hcc (n + 1))).subset_connectedComponentIn hy hsub
  apply Subset.antisymm
  · intro z hz
    simp only [chainEnd, mem_iUnion] at hz
    obtain ⟨y', hy', hz⟩ := hz
    rw [connectedComponentIn_eq (hcomp hy')]
    exact hz
  · intro z hz
    exact mem_iUnion₂.2 ⟨y, hy, hz⟩

/-- A point of the crosscut `Cₙ₊₁` of a null-chain lies in `Ω ∖ Cₙ`. -/
theorem car3_mem_diff_of_succ {Ω : Set ℂ} {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) {y : ℂ}
    (hy : y ∈ C (n + 1)) : y ∈ Ω \ C n :=
  ⟨car3_crosscut_subset (hC.1 (n + 1)) hy,
    fun hyn => disjoint_left.1 (hC.2.1 n) (subset_closure hyn) (subset_closure hy)⟩

/-- **Nesting of the ends** of a null-chain of an open connected `Ω`, `Vₙ₊₁ ⊆ Vₙ`, from the null-chain clauses alone
(no crosscut separation theorem). -/
theorem car3_chainEnd_succ_subset {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) : chainEnd Ω C (n + 1) ⊆ chainEnd Ω C n := by
  have hC' := hC
  obtain ⟨hcc, hdisj, hsep, -⟩ := hC
  obtain ⟨y1, hy1⟩ := car3_crosscut_nonempty (hcc (n + 1))
  obtain ⟨y2, hy2⟩ := car3_crosscut_nonempty (hcc (n + 2))
  obtain ⟨x0, hx0⟩ := car3_crosscut_nonempty (hcc 0)
  rw [car3_chainEnd_eq hC' (n + 1) hy2, car3_chainEnd_eq hC' n hy1]
  set V₁ := connectedComponentIn (Ω \ C (n + 1)) y2 with hV₁
  have hy2' : y2 ∈ Ω \ C (n + 1) := car3_mem_diff_of_succ hC' (n + 1) hy2
  have hsep1 := (hsep (n + 1) (by omega)).2
  -- `V₁` misses `C n`
  have hmiss : ∀ x ∈ C n, x ∉ V₁ := by
    intro x hxn hxV
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact hsep1 x hxn y2 hy2 (connectedComponentIn_eq hxV).symm
    · have hsep0 := (hsep n hpos)
      have hx0n : x0 ∈ Ω \ C n := ⟨car3_crosscut_subset (hcc 0) hx0, disjoint_left.1 hsep0.1 hx0⟩
      set W0 := connectedComponentIn (Ω \ C n) x0 with hW0
      obtain ⟨c, hcW, hcn⟩ := car3_closure_cc_inter hΩo hΩc (hcc n) hx0n
      have hT : IsPreconnected ((W0 ∪ {c}) ∪ C n) := by
        have h1 : IsPreconnected (W0 ∪ {c}) :=
          isPreconnected_connectedComponentIn.subset_closure subset_union_left
            (union_subset subset_closure (singleton_subset_iff.2 hcW))
        exact h1.union' ⟨c, Or.inr rfl, hcn⟩ (car3_crosscut_isPreconnected (hcc n))
      have hC1comp : C (n + 1) ⊆ connectedComponentIn (Ω \ C n) y1 :=
        (car3_crosscut_isPreconnected (hcc (n + 1))).subset_connectedComponentIn hy1
          (fun z hz => car3_mem_diff_of_succ hC' n hz)
      have hTsub : (W0 ∪ {c}) ∪ C n ⊆ Ω \ C (n + 1) := by
        rintro z ((hz | hz) | hz)
        · refine ⟨(connectedComponentIn_subset _ _ hz).1, fun hz1 => ?_⟩
          have e1 : W0 = connectedComponentIn (Ω \ C n) z := connectedComponentIn_eq hz
          have e2 := connectedComponentIn_eq (hC1comp hz1)
          exact hsep0.2 x0 hx0 y1 hy1 (by rw [← hW0, e1, e2])
        · rw [mem_singleton_iff.1 hz]
          exact ⟨car3_crosscut_subset (hcc n) hcn,
            fun h1 => disjoint_left.1 (hdisj n) (subset_closure hcn) (subset_closure h1)⟩
        · exact ⟨car3_crosscut_subset (hcc n) hz,
            fun h1 => disjoint_left.1 (hdisj n) (subset_closure hz) (subset_closure h1)⟩
      have hTcc :=
        hT.subset_connectedComponentIn (Or.inl (Or.inl (mem_connectedComponentIn hx0n))) hTsub
      have hxT : x ∈ connectedComponentIn (Ω \ C (n + 1)) x0 := hTcc (Or.inr hxn)
      have e1 := connectedComponentIn_eq hxT
      have e2 := connectedComponentIn_eq hxV
      exact hsep1 x0 hx0 y2 hy2 (by rw [e1, ← e2])
  -- `V₁` meets `V₀` near `C (n+1)`
  have hV₀o : IsOpen (connectedComponentIn (Ω \ C n) y1) :=
    (car3_isOpen_diff_crosscut hΩo (hcc n)).connectedComponentIn
  have hC1comp : C (n + 1) ⊆ connectedComponentIn (Ω \ C n) y1 :=
    (car3_crosscut_isPreconnected (hcc (n + 1))).subset_connectedComponentIn hy1
      (fun z hz => car3_mem_diff_of_succ hC' n hz)
  obtain ⟨c', hc'cl, hc'⟩ := car3_closure_cc_inter hΩo hΩc (hcc (n + 1)) hy2'
  obtain ⟨u, hu0, hu1⟩ := mem_closure_iff.1 hc'cl _ hV₀o (hC1comp hc')
  have hV₁sub : V₁ ⊆ Ω \ C n := fun z hz =>
    ⟨(connectedComponentIn_subset _ _ hz).1, fun hzn => hmiss z hzn hz⟩
  have h := isPreconnected_connectedComponentIn.subset_connectedComponentIn hu1 hV₁sub
  rw [← connectedComponentIn_eq hu0] at h
  exact h

/-- The impression of a null-chain of a bounded simply connected domain is a nonempty compact
connected subset of `∂Ω`.

Proof (s21r, 2026-09-27): the null-chain clauses alone give the nesting `chainEnd (n+1) ⊆ chainEnd n`
(a clopen argument in the connected `Ω`), so the impression is a decreasing intersection of continua
(`isPreconnected_iInter_of_antitone_isCompact`); it misses `Ω`: a point `z ∈ Ω` of the impression is joined to `C₀`
by a path in `Ω`, which a late crosscut `Cₙ` (small diameter, endpoints on `∂Ω`) misses, so `C₀` would meet the end
`Vₙ`, against the separation clause.  No crosscut separation theorem is needed. -/
theorem chainImpression_isCompact_isConnected {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) :
    IsCompact (chainImpression Ω C) ∧ IsConnected (chainImpression Ω C) ∧
      chainImpression Ω C ⊆ frontier Ω := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩc : IsPreconnected Ω := by
    rw [← hf.2.2]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image f hf.1.continuousOn
  set K : ℕ → Set ℂ := fun n => closure (chainEnd Ω C n) with hK
  have hEsub : ∀ n, chainEnd Ω C n ⊆ Ω := fun n =>
    iUnion₂_subset fun y _ => (connectedComponentIn_subset _ _).trans Set.sdiff_subset
  have hKc : ∀ n, IsCompact (K n) := fun n => (hΩ.subset (hEsub n)).isCompact_closure
  have hKd : ∀ n, K (n + 1) ⊆ K n := fun n => closure_mono (car3_chainEnd_succ_subset hΩo hΩc hC n)
  have hKne : ∀ n, (K n).Nonempty := fun n => by
    obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hC.1 (n + 1))
    refine ⟨y, subset_closure ?_⟩
    rw [car3_chainEnd_eq hC n hy]
    exact mem_connectedComponentIn (car3_mem_diff_of_succ hC n hy)
  have hKp : ∀ n, IsPreconnected (K n) := fun n => by
    obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hC.1 (n + 1))
    show IsPreconnected (closure (chainEnd Ω C n))
    rw [car3_chainEnd_eq hC n hy]
    exact isPreconnected_connectedComponentIn.closure
  have hI : chainImpression Ω C = ⋂ n, K n := rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hI]
    exact (hKc 0).of_isClosed_subset (isClosed_iInter fun n => isClosed_closure) (iInter_subset _ 0)
  · rw [hI]
    exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKd hKne (hKc 0)
      (fun n => isClosed_closure)
  · rw [hI]
    exact isPreconnected_iInter_of_antitone_isCompact hKd hKc hKp
  · intro z hz
    rw [hI, mem_iInter] at hz
    have hzcl : z ∈ closure Ω := closure_mono (hEsub 0) (hz 0)
    rw [hΩo.frontier_eq]
    refine ⟨hzcl, fun hzΩ => ?_⟩
    have hcc := hC.1
    have hsep := hC.2.2.1
    have hdiam := hC.2.2.2
    obtain ⟨x0, hx0⟩ := car3_crosscut_nonempty (hcc 0)
    have hx0Ω : x0 ∈ Ω := car3_crosscut_subset (hcc 0) hx0
    -- a path from `z` to `x0` in `Ω`, and a margin `δ` around it
    have hΩconn : IsConnected Ω := ⟨⟨z, hzΩ⟩, hΩc⟩
    have hJ : JoinedIn Ω z x0 :=
      (hΩo.isConnected_iff_isPathConnected.1 hΩconn).joinedIn z hzΩ x0 hx0Ω
    set P := hJ.somePath with hP
    have hPΩ : ∀ t, P t ∈ Ω := hJ.somePath_mem
    have hPc : IsCompact (range P) := isCompact_range P.continuous
    obtain ⟨δ, hδ, hδsub⟩ := hPc.exists_cthickening_subset_open hΩo (range_subset_iff.2 hPΩ)
    -- a late crosscut misses the path
    obtain ⟨n, hn1, hnd⟩ : ∃ n, 1 ≤ n ∧ Metric.diam (C n) < δ := by
      obtain ⟨N, hN⟩ := (hdiam.eventually_lt_const hδ).exists_forall_of_atTop
      exact ⟨max N 1, le_max_right _ _, hN _ (le_max_left _ _)⟩
    have hmiss : ∀ t, P t ∉ C n := by
      intro t hPt
      obtain ⟨γ, hγc, -, hγC, -, h0, -⟩ := hcc n
      have hγ0 : γ 0 ∈ closure (C n) := by
        have hc : ContinuousOn γ (closure (Ioo (0 : ℝ) 1)) := by rwa [closure_Ioo zero_ne_one]
        rw [← hγC]
        exact hc.image_closure ⟨0, by rw [closure_Ioo zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩, rfl⟩
      have hbd : Bornology.IsBounded (C n) := hΩ.subset (car3_crosscut_subset (hcc n))
      have hd : dist (P t) (γ 0) ≤ Metric.diam (C n) := by
        rw [← Metric.diam_closure]
        exact Metric.dist_le_diam_of_mem hbd.closure (subset_closure hPt) hγ0
      have hmem : γ 0 ∈ cthickening δ (range P) :=
        mem_cthickening_of_dist_le _ _ δ _ ⟨t, rfl⟩ (by rw [dist_comm]; linarith)
      have h0Ω := hδsub hmem
      rw [hΩo.frontier_eq] at h0
      exact h0.2 h0Ω
    have hrange : range P ⊆ Ω \ C n := range_subset_iff.2 fun t => ⟨hPΩ t, hmiss t⟩
    have hx0cc : x0 ∈ connectedComponentIn (Ω \ C n) z := by
      have := (isPreconnected_range P.continuous).subset_connectedComponentIn (x := z)
        ⟨0, P.source⟩ hrange
      exact this ⟨1, P.target⟩
    obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hcc (n + 1))
    have hzK : z ∈ closure (chainEnd Ω C n) := hz n
    rw [car3_chainEnd_eq hC n hy] at hzK
    have hzn : z ∈ Ω \ C n := ⟨hzΩ, by have := hmiss 0; rwa [P.source] at this⟩
    have hzo : IsOpen (connectedComponentIn (Ω \ C n) z) :=
      (car3_isOpen_diff_crosscut hΩo (hcc n)).connectedComponentIn
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.1 hzK _ hzo (mem_connectedComponentIn hzn)
    have e1 := connectedComponentIn_eq hu1
    have e2 := connectedComponentIn_eq hu2
    have e3 := connectedComponentIn_eq hx0cc
    exact (hsep n hn1).2 x0 hx0 y hy (by rw [← e3, e1, ← e2])

/-- A **principal point** of a prime end `p`: the limit of some null-chain representing `p`, i.e.
the crosscuts of that chain eventually lie in every ball around `w`.

Correction (2026-09-27, user-approved): the earlier definition asked, for each `ε`, only for ONE
crosscut (of any index, `n = 0` included) of some representing chain inside `B(w, ε)`.  That
makes every point of the impression principal (put a small pocket crosscut of a comb domain at
index `0` or `1`), so `caratheodory_primeEnd_principal` was false. -/
def IsPrincipalPoint (Ω : Set ℂ) (p : PrimeEnd Ω) (w : ℂ) : Prop :=
  ∃ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = p ∧
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, c.1 n ⊆ ball w ε

end LiZhongQC
