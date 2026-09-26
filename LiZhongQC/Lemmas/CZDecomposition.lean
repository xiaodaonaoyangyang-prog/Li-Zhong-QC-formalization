import Mathlib

/-!
# The Calderón–Zygmund decomposition for the Beurling kernel on `ℂ`

Mathlib-only leaf (no dependence on the project's Hilbert-transform machinery, no import
cycle risk). Provides:

* `czKernel`, the (rescaled) Beurling kernel `K(ζ, z) = -1/(π(ζ-z)²)`, its off-diagonal norm and
  derivative, an exact algebraic difference identity, and the Hörmander condition
  (`czKernel_hormander`) — via a pure algebraic route, no mean-value machinery.
* A dyadic-square Calderón–Zygmund decomposition of any `f ∈ L¹(ℂ)` at height `lam`
  (`exists_czDecomposition`): `f = g + b`, `g` bounded by `4·lam` a.e., `b` supported on
  countably many pairwise disjoint measurable pieces with mean zero on each, each piece engulfed
  by a ball with a doubling bound, and the total measure and `L¹` norm of `b` controlled by `f`'s.
  The a.e. bound on `g` off the "bad" pieces is proved via a Lebesgue differentiation argument,
  through a custom `VitaliFamily` of closed dyadic squares.
-/

open Complex Set Metric Filter Topology MeasureTheory Classical
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## S1: kernel estimates -/

/-- The (rescaled) Beurling kernel `K(ζ, z) = -1/(π(ζ-z)²)`, the integrand of `hilbertHSmooth`. -/
noncomputable def czKernel (ζ z : ℂ) : ℂ := -(1 / π : ℂ) / (ζ - z) ^ 2

theorem czKernel_norm_eq {ζ z : ℂ} (h : ζ ≠ z) :
    ‖czKernel ζ z‖ = 1 / (π * ‖ζ - z‖ ^ 2) := by
  unfold czKernel
  rw [norm_div, norm_neg, norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, norm_pow, div_div]

/-- Complex derivative of the kernel in `ζ`, off the diagonal. -/
theorem hasDerivAt_czKernel (z : ℂ) {ζ : ℂ} (h : ζ ≠ z) :
    HasDerivAt (fun ζ' => czKernel ζ' z) (2 * (1 / π : ℂ) / (ζ - z) ^ 3) ζ := by
  have hne : ζ - z ≠ 0 := sub_ne_zero.mpr h
  have hpow2 : ((ζ - z) ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hne
  have hc : HasDerivAt (fun _ : ℂ => -(1 / π : ℂ)) 0 ζ := hasDerivAt_const ζ _
  have hd1 : HasDerivAt (fun ζ' : ℂ => ζ' - z) 1 ζ := (hasDerivAt_id ζ).sub_const z
  have hd : HasDerivAt (fun ζ' : ℂ => (ζ' - z) ^ 2) (2 * (ζ - z) ^ (2 - 1) * 1) ζ := hd1.pow 2
  have hdiv := hc.div hd hpow2
  -- `HasDerivAt.div`/`.inv` state their conclusion using Mathlib's pointwise `Pi.div`/`Pi.inv`
  -- (`f / g` as a whole function), not the applied `fun y => f y / g y` form. Bridging back to a
  -- plain lambda is a function-level `rfl` (`Pi.div` unfolds definitionally) — `funext` + `ring`
  -- fails here because the two sides aren't syntactically a pointwise equation to begin with.
  have heq : ((fun _ : ℂ => -(1 / π : ℂ)) / fun ζ' : ℂ => (ζ' - z) ^ 2) =
      fun ζ' => czKernel ζ' z := rfl
  rw [heq] at hdiv
  convert hdiv using 1
  field_simp
  ring

/-- Exact algebraic difference identity: `K(ζ,z) - K(ζ,z') = -(1/π)(z-z')(2ζ-z-z') /
((ζ-z)²(ζ-z')²)`.  Avoids any mean-value/derivative machinery — pure `field_simp`/`ring`. -/
theorem czKernel_diff_eq {ζ z z' : ℂ} (hζz : ζ ≠ z) (hζz' : ζ ≠ z') :
    czKernel ζ z - czKernel ζ z' =
      -(1 / π : ℂ) * ((z - z') * (2 * ζ - z - z')) / ((ζ - z) ^ 2 * (ζ - z') ^ 2) := by
  have h1 : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
  have h2 : ζ - z' ≠ 0 := sub_ne_zero.mpr hζz'
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold czKernel
  field_simp
  ring

/-- Pointwise bound on the far region `2‖z-z'‖ < ‖ζ-z‖`: the difference kernel is
`≤ 10 ‖z-z'‖ / (π ‖ζ-z‖³)`. -/
theorem czKernel_diff_norm_le_far {ζ z z' : ℂ} (hzz' : z ≠ z')
    (hζ : 2 * ‖z - z'‖ < ‖ζ - z‖) :
    ‖czKernel ζ z - czKernel ζ z'‖ ≤ 10 * ‖z - z'‖ / (π * ‖ζ - z‖ ^ 3) := by
  have hd : 0 < ‖z - z'‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hzz'
  have hζz0 : 0 < ‖ζ - z‖ := by linarith
  have hζz : ζ ≠ z := by
    intro h; rw [h] at hζz0; simp at hζz0
  have hζz'_far : ‖ζ - z‖ / 2 < ‖ζ - z'‖ := by
    have htri : ‖ζ - z‖ ≤ ‖ζ - z'‖ + ‖z' - z‖ := by
      calc ‖ζ - z‖ = ‖(ζ - z') + (z' - z)‖ := by ring_nf
        _ ≤ ‖ζ - z'‖ + ‖z' - z‖ := norm_add_le _ _
    have hrev : ‖z' - z‖ = ‖z - z'‖ := norm_sub_rev z' z
    linarith
  have hζz'0 : 0 < ‖ζ - z'‖ := by
    have : (0:ℝ) < ‖ζ - z‖ / 2 := by positivity
    linarith
  have hζz' : ζ ≠ z' := by
    intro h; rw [h] at hζz'0; simp at hζz'0
  have hnum : ‖2 * ζ - z - z'‖ ≤ 5 / 2 * ‖ζ - z‖ := by
    have heq : (2 : ℂ) * ζ - z - z' = (ζ - z) + (ζ - z') := by ring
    have hb1 : ‖ζ - z'‖ < 3 / 2 * ‖ζ - z‖ := by
      have htri : ‖ζ - z'‖ ≤ ‖ζ - z‖ + ‖z - z'‖ := by
        calc ‖ζ - z'‖ = ‖(ζ - z) + (z - z')‖ := by ring_nf
          _ ≤ ‖ζ - z‖ + ‖z - z'‖ := norm_add_le _ _
      linarith
    calc ‖2 * ζ - z - z'‖ = ‖(ζ - z) + (ζ - z')‖ := by rw [heq]
      _ ≤ ‖ζ - z‖ + ‖ζ - z'‖ := norm_add_le _ _
      _ ≤ 5 / 2 * ‖ζ - z‖ := by linarith
  rw [czKernel_diff_eq hζz hζz', norm_div, norm_mul, norm_mul, norm_neg, norm_div, norm_one,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_mul, norm_pow, norm_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow2 : ‖ζ - z‖ ^ 2 / 4 ≤ ‖ζ - z'‖ ^ 2 := by
    have h1 : (0:ℝ) ≤ ‖ζ - z‖ / 2 := by positivity
    have h2 := pow_le_pow_left₀ h1 hζz'_far.le 2
    rw [div_pow] at h2
    norm_num at h2
    linarith [h2]
  have hπ0 : (0:ℝ) < π := Real.pi_pos
  have step1 : ‖2 * ζ - z - z'‖ * ‖ζ - z‖ ^ 3 ≤ 5 / 2 * ‖ζ - z‖ * ‖ζ - z‖ ^ 3 :=
    mul_le_mul_of_nonneg_right hnum (by positivity)
  have step2 : (10 : ℝ) * ‖ζ - z‖ ^ 2 * (‖ζ - z‖ ^ 2 / 4) ≤ 10 * ‖ζ - z‖ ^ 2 * ‖ζ - z'‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hpow2 (by positivity)
  have hcombine : 5 / 2 * ‖ζ - z‖ * ‖ζ - z‖ ^ 3 = 10 * ‖ζ - z‖ ^ 2 * (‖ζ - z‖ ^ 2 / 4) := by ring
  have hstep : ‖2 * ζ - z - z'‖ * ‖ζ - z‖ ^ 3 ≤ 10 * ‖ζ - z‖ ^ 2 * ‖ζ - z'‖ ^ 2 := by
    calc ‖2 * ζ - z - z'‖ * ‖ζ - z‖ ^ 3 ≤ 5 / 2 * ‖ζ - z‖ * ‖ζ - z‖ ^ 3 := step1
      _ = 10 * ‖ζ - z‖ ^ 2 * (‖ζ - z‖ ^ 2 / 4) := hcombine
      _ ≤ 10 * ‖ζ - z‖ ^ 2 * ‖ζ - z'‖ ^ 2 := step2
  calc 1 / π * (‖z - z'‖ * ‖2 * ζ - z - z'‖) * (π * ‖ζ - z‖ ^ 3)
      = ‖z - z'‖ * (‖2 * ζ - z - z'‖ * ‖ζ - z‖ ^ 3) := by field_simp
    _ ≤ ‖z - z'‖ * (10 * ‖ζ - z‖ ^ 2 * ‖ζ - z'‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep hd.le
    _ = 10 * ‖z - z'‖ * (‖ζ - z‖ ^ 2 * ‖ζ - z'‖ ^ 2) := by ring

/-- The target of the polar coordinate chart of `ℂ`, as a product of intervals. -/
theorem cz_polarCoord_target_eq :
    (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl

/-- The radial integral outside a disc: `∬_{|w| > ρ} |w|^{-a} dξ dη = 2π (-ρ^{2-a})/(2-a)`
for `a > 2` (the right-hand side is positive, since `2 - a < 0`). -/
theorem cz_lintegral_compl_ball_enorm_rpow_neg {a : ℝ} (ha : 2 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ w in {w : ℂ | ρ < ‖w‖}, ‖w‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - a) / (2 - a)) := by
  have hset : MeasurableSet {w : ℂ | ρ < ‖w‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • ({w : ℂ | ρ < ‖w‖}).indicator (fun w : ℂ => ‖w‖ₑ ^ (-a))
          (Complex.polarCoord.symm p)
        = (Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) p.1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hr0
    by_cases hrρ : ρ < r
    · have hmem : Complex.polarCoord.symm (r, θ) ∈ {w : ℂ | ρ < ‖w‖} := by
        simp only [mem_setOf_eq, hnorm]
        exact hrρ
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show r ∈ Ioi ρ from hrρ),
        smul_eq_mul, ← ofReal_norm (Complex.polarCoord.symm (r, θ)), hnorm,
        ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_mul hr0.le]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
    · have hmem : Complex.polarCoord.symm (r, θ) ∉ {w : ℂ | ρ < ‖w‖} := by
        simp only [mem_setOf_eq, hnorm]
        exact hrρ
      have hmem' : r ∉ Ioi ρ := hrρ
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', smul_zero]
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - a)) (Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi ρ)] fun r : ℝ => r ^ (1 - a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hρ.trans hr).le _
  have hexp : (1 : ℝ) - a + 1 = 2 - a := by ring
  have hval : ∫ r in Ioi ρ, r ^ (1 - a) = -ρ ^ (2 - a) / (2 - a) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : (1 : ℝ) - a < -1) hρ, hexp]
  have hmeas : AEMeasurable (fun x : ℝ × ℝ =>
      (Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) x.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    ((((measurable_id.pow_const (1 - a)).ennreal_ofReal).indicator
      measurableSet_Ioi).comp measurable_fst).aemeasurable
  rw [← lintegral_indicator hset, ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key, cz_polarCoord_target_eq,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [show (π : ℝ) - -π = 2 * π from by ring]
  have hsub : Ioi ρ ∩ Ioi (0 : ℝ) = Ioi ρ :=
    Set.inter_eq_self_of_subset_left fun x hx => hρ.trans hx
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    setLIntegral_indicator measurableSet_Ioi, hsub,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- The translated form of `cz_lintegral_compl_ball_enorm_rpow_neg`, centred at `z` instead of `0`. -/
theorem cz_lintegral_compl_ball_sub_enorm_rpow_neg {a : ℝ} (ha : 2 < a) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) :
    (∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - a) / (2 - a)) := by
  have hemb : MeasurableEmbedding (fun w : ℂ => w + z) :=
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
  have hpre : (fun w : ℂ => w + z) ⁻¹' {ζ : ℂ | ρ < ‖ζ - z‖} = {w : ℂ | ρ < ‖w‖} := by
    ext w
    simp
  have h := (measurePreserving_add_right volume z).setLIntegral_comp_preimage_emb hemb
    (fun ζ => ‖ζ - z‖ₑ ^ (-a)) {ζ : ℂ | ρ < ‖ζ - z‖}
  rw [hpre] at h
  simp only [add_sub_cancel_right] at h
  rw [← h]
  exact cz_lintegral_compl_ball_enorm_rpow_neg ha hρ

/-- Hörmander's condition, with an unspecified uniform constant. -/
theorem czKernel_hormander :
    ∃ C : ℝ, ∀ z z' : ℂ, z ≠ z' →
      (∫⁻ ζ in {ζ : ℂ | 2 * ‖z - z'‖ < ‖ζ - z‖}, ‖czKernel ζ z - czKernel ζ z'‖ₑ) ≤
        ENNReal.ofReal C := by
  refine ⟨10, fun z z' hzz' => ?_⟩
  have hd : 0 < ‖z - z'‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hzz'
  have h2d : 0 < 2 * ‖z - z'‖ := by linarith
  set S : Set ℂ := {ζ : ℂ | 2 * ‖z - z'‖ < ‖ζ - z‖} with hS
  have hpt : ∀ ζ ∈ S, ‖czKernel ζ z - czKernel ζ z'‖ₑ ≤
      ENNReal.ofReal (10 * ‖z - z'‖ / π) * ‖ζ - z‖ₑ ^ (-(3 : ℝ)) := by
    intro ζ hζ
    simp only [hS, mem_setOf_eq] at hζ
    have hζz0 : 0 < ‖ζ - z‖ := by linarith
    have hb := czKernel_diff_norm_le_far hzz' hζ
    have hrw : (10 : ℝ) * ‖z - z'‖ / (π * ‖ζ - z‖ ^ 3)
        = 10 * ‖z - z'‖ / π * (‖ζ - z‖ ^ 3)⁻¹ := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [hrw] at hb
    have hcube : ‖ζ - z‖ₑ ^ (-(3 : ℝ)) = ENNReal.ofReal ((‖ζ - z‖ ^ 3)⁻¹) := by
      rw [ENNReal.rpow_neg, ← ofReal_norm (ζ - z),
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [← ofReal_norm (czKernel ζ z - czKernel ζ z'), hcube, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  have hSmeas : MeasurableSet S := by
    have hSeq : S = (Metric.closedBall z (2 * ‖z - z'‖))ᶜ := by
      ext ζ
      simp only [hS, mem_setOf_eq, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
    rw [hSeq]
    exact measurableSet_closedBall.compl
  have hmono : (∫⁻ ζ in S, ‖czKernel ζ z - czKernel ζ z'‖ₑ) ≤
      ∫⁻ ζ in S, ENNReal.ofReal (10 * ‖z - z'‖ / π) * ‖ζ - z‖ₑ ^ (-(3 : ℝ)) :=
    lintegral_mono_ae (ae_restrict_of_forall_mem hSmeas hpt)
  have hpull : (∫⁻ ζ in S, ENNReal.ofReal (10 * ‖z - z'‖ / π) * ‖ζ - z‖ₑ ^ (-(3 : ℝ)))
      = ENNReal.ofReal (10 * ‖z - z'‖ / π) * ∫⁻ ζ in S, ‖ζ - z‖ₑ ^ (-(3 : ℝ)) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hradial : (∫⁻ ζ in S, ‖ζ - z‖ₑ ^ (-(3 : ℝ)))
      = ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(2 * ‖z - z'‖) ^ (2 - (3 : ℝ)) / (2 - 3)) :=
    cz_lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) h2d z
  have hval : -(2 * ‖z - z'‖) ^ (2 - (3 : ℝ)) / (2 - 3) = (2 * ‖z - z'‖)⁻¹ := by
    rw [show (2 : ℝ) - 3 = -(1 : ℝ) by norm_num, Real.rpow_neg h2d.le, Real.rpow_one]
    ring
  calc (∫⁻ ζ in S, ‖czKernel ζ z - czKernel ζ z'‖ₑ)
      ≤ ∫⁻ ζ in S, ENNReal.ofReal (10 * ‖z - z'‖ / π) * ‖ζ - z‖ₑ ^ (-(3 : ℝ)) := hmono
    _ = ENNReal.ofReal (10 * ‖z - z'‖ / π) * ∫⁻ ζ in S, ‖ζ - z‖ₑ ^ (-(3 : ℝ)) := hpull
    _ = ENNReal.ofReal (10 * ‖z - z'‖ / π) *
          (ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * ‖z - z'‖)⁻¹) := by rw [hradial, hval]
    _ = ENNReal.ofReal (10 * ‖z - z'‖ / π * (2 * π * (2 * ‖z - z'‖)⁻¹)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal 10 := by
        congr 1
        have hπ0 : (0 : ℝ) < π := Real.pi_pos
        field_simp

/-! ## S2: Calderón–Zygmund decomposition on `ℂ` (dyadic squares) -/

/-! ### Dyadic square infrastructure -/

/-- The dyadic square of scale `n : ℤ` (side length `2^n`) at grid position `(i, j)`. -/
noncomputable def dyadicSquare (n i j : ℤ) : Set ℂ :=
  {z : ℂ | (i : ℝ) * (2 : ℝ) ^ n ≤ z.re ∧ z.re < ((i : ℝ) + 1) * (2 : ℝ) ^ n ∧
    (j : ℝ) * (2 : ℝ) ^ n ≤ z.im ∧ z.im < ((j : ℝ) + 1) * (2 : ℝ) ^ n}

theorem dyadicSquare_eq_preimage (n i j : ℤ) :
    dyadicSquare n i j =
      Complex.measurableEquivRealProd ⁻¹'
        (Set.Ico ((i : ℝ) * (2 : ℝ) ^ n) (((i : ℝ) + 1) * (2 : ℝ) ^ n) ×ˢ
          Set.Ico ((j : ℝ) * (2 : ℝ) ^ n) (((j : ℝ) + 1) * (2 : ℝ) ^ n)) := by
  ext z
  simp only [dyadicSquare, Complex.measurableEquivRealProd_apply, Set.mem_Ico, Set.mem_prod,
    Set.mem_preimage, Set.mem_setOf_eq, and_assoc]

theorem dyadicSquare_measurableSet (n i j : ℤ) : MeasurableSet (dyadicSquare n i j) := by
  rw [dyadicSquare_eq_preimage]
  exact Complex.measurableEquivRealProd.measurable
    (measurableSet_Ico.prod measurableSet_Ico)

theorem dyadicSquare_volume (n i j : ℤ) :
    volume (dyadicSquare n i j) = ENNReal.ofReal ((2 : ℝ) ^ n) ^ 2 := by
  rw [dyadicSquare_eq_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  rw [show ((i : ℝ) + 1) * (2 : ℝ) ^ n - (i : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ n by ring,
    show ((j : ℝ) + 1) * (2 : ℝ) ^ n - (j : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ n by ring,
    sq]

theorem dyadicSquare_volume_pos (n i j : ℤ) : 0 < volume (dyadicSquare n i j) := by
  rw [dyadicSquare_volume]
  positivity

theorem dyadicSquare_volume_ne_top (n i j : ℤ) : volume (dyadicSquare n i j) ≠ ⊤ := by
  rw [dyadicSquare_volume]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- Two dyadic squares of the SAME scale with different grid position are disjoint. -/
theorem dyadicSquare_disjoint_same_scale {n i j i' j' : ℤ} (h : (i, j) ≠ (i', j')) :
    Disjoint (dyadicSquare n i j) (dyadicSquare n i' j') := by
  rw [Set.disjoint_left]
  rintro z ⟨hzre1, hzre2, hzim1, hzim2⟩ ⟨hzre1', hzre2', hzim1', hzim2'⟩
  have h2n : (0:ℝ) < (2:ℝ) ^ n := by positivity
  apply h
  have hi : i = i' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (i:ℝ) + 1 ≤ (i':ℝ) := by
        have : i + 1 ≤ i' := hlt
        exact_mod_cast this
      nlinarith
    · have : (i':ℝ) + 1 ≤ (i:ℝ) := by
        have : i' + 1 ≤ i := hgt
        exact_mod_cast this
      nlinarith
  have hj : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (j:ℝ) + 1 ≤ (j':ℝ) := by
        have : j + 1 ≤ j' := hlt
        exact_mod_cast this
      nlinarith
    · have : (j':ℝ) + 1 ≤ (j:ℝ) := by
        have : j' + 1 ≤ j := hgt
        exact_mod_cast this
      nlinarith
  rw [hi, hj]

/-- One-coordinate version of the parent-containment fact: if `x` lies in the scale-`(n-1)`
interval at index `i`, it lies in the scale-`n` interval at index `i / 2`. -/
theorem dyadic_one_coord_subset_parent {n i : ℤ} {x : ℝ}
    (h1 : (i : ℝ) * (2 : ℝ) ^ (n - 1) ≤ x) (h2 : x < ((i : ℝ) + 1) * (2 : ℝ) ^ (n - 1)) :
    ((i / 2 : ℤ) : ℝ) * (2 : ℝ) ^ n ≤ x ∧ x < (((i / 2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ n := by
  have h2n1 : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n / 2 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  rw [h2n1] at h1 h2
  have hi_eq : i = 2 * (i / 2) + i % 2 := by omega
  have hi_eq' : (i : ℝ) = 2 * ((i / 2 : ℤ) : ℝ) + ((i % 2 : ℤ) : ℝ) := by exact_mod_cast hi_eq
  have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have h2n0 : (0:ℝ) < (2:ℝ) ^ n := by positivity
  rcases hmod with hm | hm
  · rw [hm] at hi_eq'
    push_cast at hi_eq'
    constructor <;> nlinarith
  · rw [hm] at hi_eq'
    push_cast at hi_eq'
    constructor <;> nlinarith

/-- A dyadic square of scale `n - 1` is contained in its parent, scale `n`, position
`(i / 2, j / 2)`. -/
theorem dyadicSquare_subset_parent (n i j : ℤ) :
    dyadicSquare (n - 1) i j ⊆ dyadicSquare n (i / 2) (j / 2) := by
  intro z ⟨hzre1, hzre2, hzim1, hzim2⟩
  obtain ⟨hre1, hre2⟩ := dyadic_one_coord_subset_parent hzre1 hzre2
  obtain ⟨him1, him2⟩ := dyadic_one_coord_subset_parent hzim1 hzim2
  exact ⟨hre1, hre2, him1, him2⟩

/-- Iterating "divide index by 2" `d` times: the grid position `d` generations coarser. -/
def ancestorIdx : ℕ → ℤ → ℤ
  | 0, i => i
  | (d + 1), i => ancestorIdx d (i / 2)

theorem dyadicSquare_subset_ancestor (n : ℤ) :
    ∀ (d : ℕ) (i j : ℤ),
      dyadicSquare (n - d) i j ⊆ dyadicSquare n (ancestorIdx d i) (ancestorIdx d j) := by
  intro d
  induction d with
  | zero => intro i j; simp [ancestorIdx]
  | succ d ih =>
      intro i j
      have hstep : dyadicSquare ((n - d) - 1) i j ⊆ dyadicSquare (n - d) (i / 2) (j / 2) :=
        dyadicSquare_subset_parent (n - d) i j
      have heq : (n : ℤ) - (↑(d + 1)) = (n - d) - 1 := by push_cast; ring
      calc dyadicSquare (n - (↑(d + 1) : ℤ)) i j = dyadicSquare ((n - d) - 1) i j := by rw [heq]
        _ ⊆ dyadicSquare (n - d) (i / 2) (j / 2) := hstep
        _ ⊆ dyadicSquare n (ancestorIdx d (i / 2)) (ancestorIdx d (j / 2)) := ih (i / 2) (j / 2)
        _ = dyadicSquare n (ancestorIdx (d + 1) i) (ancestorIdx (d + 1) j) := rfl

/-- Average of `‖f‖` over a measurable set of positive, finite measure. -/
noncomputable def avgAbs (f : ℂ → ℂ) (Q : Set ℂ) : ℝ := (∫ ζ in Q, ‖f ζ‖) / (volume Q).toReal

/-- `Reachable f lam N k i j`: every ancestor of the scale-`(N-k)` square at grid position
`(i, j)`, from scale `N` down to (but not including) scale `N - k`, has average `≤ lam`.
Stated directly as a `∀` over the ancestor distance `t` (rather than a `k`-recursive peeling)
so that both the disjointness argument (instantiate at the right `t`) and the "never selected ⟹
bounded average at every level" argument (induction on `k`) read off the definition directly. -/
def Reachable (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (k : ℕ) (i j : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ k →
    avgAbs f (dyadicSquare (N - (k - t : ℕ)) (ancestorIdx t i) (ancestorIdx t j)) ≤ lam

/-- `Selected f lam N k i j`: the scale-`(N-k)` square at `(i, j)` is reachable and its own
average exceeds `lam` — a maximal dyadic square with average `> lam`. -/
def Selected (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (k : ℕ) (i j : ℤ) : Prop :=
  Reachable f lam N k i j ∧ lam < avgAbs f (dyadicSquare (N - k) i j)

/-- Two distinct selected squares are disjoint. -/
theorem selected_disjoint {f : ℂ → ℂ} {lam : ℝ} {N : ℤ} {k₁ k₂ : ℕ} {i₁ j₁ i₂ j₂ : ℤ}
    (h1 : Selected f lam N k₁ i₁ j₁) (h2 : Selected f lam N k₂ i₂ j₂)
    (hne : (k₁, i₁, j₁) ≠ (k₂, i₂, j₂)) :
    Disjoint (dyadicSquare (N - k₁) i₁ j₁) (dyadicSquare (N - k₂) i₂ j₂) := by
  -- Reduce to the case `k₁ ≤ k₂` by symmetry.
  wlog hk : k₁ ≤ k₂ generalizing k₁ k₂ i₁ j₁ i₂ j₂ with H
  · exact (H h2 h1 (Ne.symm hne) (by omega)).symm
  rcases eq_or_lt_of_le hk with hk' | hk'
  · -- Same scale: different index ⟹ disjoint directly.
    subst hk'
    have hij : (i₁, j₁) ≠ (i₂, j₂) := by
      intro heq
      exact hne (by rw [heq])
    exact dyadicSquare_disjoint_same_scale hij
  · -- `k₁ < k₂`: the ancestor of square 2 at scale `N - k₁` either equals square 1 (ruled out
    -- by selectedness) or is a different same-scale square (giving disjointness by containment).
    set d := k₂ - k₁ with hd_def
    have hd1 : 1 ≤ d := by omega
    have hdk2 : d ≤ k₂ := by omega
    have hk1_eq : k₂ - d = k₁ := by omega
    have hcontain : dyadicSquare (N - (k₂ : ℤ)) i₂ j₂ ⊆
        dyadicSquare (N - (k₁ : ℤ)) (ancestorIdx d i₂) (ancestorIdx d j₂) := by
      have hsub := dyadicSquare_subset_ancestor (N - (k₁ : ℤ)) d i₂ j₂
      have heq : (N - (k₁ : ℤ)) - (d : ℤ) = N - (k₂ : ℤ) := by
        have : (k₁ : ℤ) + d = k₂ := by exact_mod_cast (by omega : k₁ + d = k₂)
        omega
      rwa [heq] at hsub
    by_cases hcase : ancestorIdx d i₂ = i₁ ∧ ancestorIdx d j₂ = j₁
    · exfalso
      have hreach := h2.1 d hd1 hdk2
      rw [hk1_eq, hcase.1, hcase.2] at hreach
      exact absurd hreach (not_le.mpr h1.2)
    · have hneq : (ancestorIdx d i₂, ancestorIdx d j₂) ≠ (i₁, j₁) := by
        intro heq
        exact hcase ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      have hdisj := dyadicSquare_disjoint_same_scale (n := N - (k₁ : ℤ)) (Ne.symm hneq)
      exact Set.disjoint_left.mpr fun z hz1 hz2 => Set.disjoint_left.mp hdisj hz1 (hcontain hz2)

/-- A starting scale `N` coarse enough that EVERY level-`N` grid square already has average
`≤ lam` — the base of the stopping time (no level-`N` square is ever selected). -/
theorem exists_valid_start_scale (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ N : ℤ, ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∫ z, ‖f z‖) / lam) (by norm_num : (1:ℝ) < 2)
  refine ⟨(n : ℤ), fun i j => ?_⟩
  unfold avgAbs
  have hvol : volume (dyadicSquare (n:ℤ) i j) = ENNReal.ofReal ((2:ℝ) ^ n) ^ 2 := by
    rw [dyadicSquare_volume, zpow_natCast]
  have hvolToReal : (volume (dyadicSquare (n:ℤ) i j)).toReal = ((2:ℝ) ^ n) ^ 2 := by
    rw [hvol, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  have hbound : (∫ ζ in dyadicSquare (n:ℤ) i j, ‖f ζ‖) ≤ ∫ z, ‖f z‖ :=
    setIntegral_le_integral hf.norm (Eventually.of_forall fun z => norm_nonneg (f z))
  rw [hvolToReal]
  have h2pow : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have h2ge1 : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have hn' : (∫ z, ‖f z‖) / lam < ((2:ℝ)^n)^2 := by
    calc (∫ z, ‖f z‖) / lam < (2:ℝ)^n := hn
      _ ≤ ((2:ℝ)^n)^2 := by nlinarith
  have hn'' : (∫ z, ‖f z‖) < lam * ((2:ℝ)^n)^2 := by
    rw [div_lt_iff₀ hlam] at hn'
    linarith [hn']
  calc (∫ ζ in dyadicSquare (n:ℤ) i j, ‖f ζ‖) ≤ ∫ z, ‖f z‖ := hbound
    _ ≤ lam * (((2:ℝ)^n)^2) := hn''.le

/-! ### The grid index of a point, and the "never selected" consequence -/

/-- The grid position at scale `n` containing `z`. -/
noncomputable def gridIdx (n : ℤ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re / (2:ℝ) ^ n⌋, ⌊z.im / (2:ℝ) ^ n⌋)

theorem mem_dyadicSquare_gridIdx (n : ℤ) (z : ℂ) :
    z ∈ dyadicSquare n (gridIdx n z).1 (gridIdx n z).2 := by
  have h2n : (0:ℝ) < (2:ℝ) ^ n := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ h2n).mp (Int.floor_le _)
  · exact (div_lt_iff₀ h2n).mp (Int.lt_floor_add_one _)
  · exact (le_div_iff₀ h2n).mp (Int.floor_le _)
  · exact (div_lt_iff₀ h2n).mp (Int.lt_floor_add_one _)

theorem gridIdx_unique {n i j : ℤ} {z : ℂ} (hz : z ∈ dyadicSquare n i j) :
    (i, j) = gridIdx n z := by
  by_contra hne
  have hzg := mem_dyadicSquare_gridIdx n z
  exact Set.disjoint_left.mp (dyadicSquare_disjoint_same_scale hne) hz hzg

/-- The grid position at scale `n - 1` containing `z`, halved, is the grid position at scale
`n`. -/
theorem gridIdx_parent (n : ℤ) (z : ℂ) :
    ((gridIdx (n - 1) z).1 / 2, (gridIdx (n - 1) z).2 / 2) = gridIdx n z := by
  have hsub := dyadicSquare_subset_parent n (gridIdx (n-1) z).1 (gridIdx (n-1) z).2
  have hmem := mem_dyadicSquare_gridIdx (n-1) z
  exact gridIdx_unique (hsub hmem)

/-- Iterated: the grid position at scale `n - t`, ancestored `t` steps, is the grid position at
scale `n`. -/
theorem gridIdx_ancestor (n : ℤ) (t : ℕ) (z : ℂ) :
    (ancestorIdx t (gridIdx (n - t) z).1, ancestorIdx t (gridIdx (n - t) z).2) = gridIdx n z := by
  induction t with
  | zero => simp [ancestorIdx]
  | succ t ih =>
      have hpar := gridIdx_parent (n - t) z
      have hpar1 : (gridIdx ((n - t) - 1) z).1 / 2 = (gridIdx (n - t) z).1 := congrArg Prod.fst hpar
      have hpar2 : (gridIdx ((n - t) - 1) z).2 / 2 = (gridIdx (n - t) z).2 := congrArg Prod.snd hpar
      have heq : n - (↑(t+1) : ℤ) = (n - t) - 1 := by push_cast; ring
      rw [heq]
      have h1 : ancestorIdx (t+1) (gridIdx ((n - t) - 1) z).1 = ancestorIdx t (gridIdx (n-t) z).1 := by
        show ancestorIdx t ((gridIdx ((n-t)-1) z).1 / 2) = ancestorIdx t (gridIdx (n-t) z).1
        rw [hpar1]
      have h2 : ancestorIdx (t+1) (gridIdx ((n - t) - 1) z).2 = ancestorIdx t (gridIdx (n-t) z).2 := by
        show ancestorIdx t ((gridIdx ((n-t)-1) z).2 / 2) = ancestorIdx t (gridIdx (n-t) z).2
        rw [hpar2]
      rw [h1, h2]
      exact ih

/-- If `z` is never in a selected square (at any level `k`), then `z`'s containing square at
EVERY level `k` has average `≤ lam` — the source of the a.e. bound `‖g‖ ≤ lam` outside the
union of selected squares. -/
theorem never_selected_avg_le {f : ℂ → ℂ} {lam : ℝ} {N : ℤ} {z : ℂ}
    (hns : ∀ k : ℕ, ¬ Selected f lam N k (gridIdx (N - (k:ℤ)) z).1 (gridIdx (N - (k:ℤ)) z).2)
    (k : ℕ) :
    avgAbs f (dyadicSquare (N - (k:ℤ)) (gridIdx (N - (k:ℤ)) z).1 (gridIdx (N - (k:ℤ)) z).2) ≤
      lam := by
  suffices main : ∀ K : ℕ, ∀ m ≤ K,
      avgAbs f (dyadicSquare (N - (m:ℤ)) (gridIdx (N - (m:ℤ)) z).1
        (gridIdx (N - (m:ℤ)) z).2) ≤ lam from main k k le_rfl
  intro K
  induction K with
  | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      have hreach0 : Reachable f lam N 0 (gridIdx (N - (0:ℤ)) z).1 (gridIdx (N - (0:ℤ)) z).2 :=
        fun t ht1 ht2 => absurd ht2 (by omega)
      have hsel := hns 0
      unfold Selected at hsel
      push_neg at hsel
      simpa using hsel hreach0
  | succ K ih =>
      intro m hm
      rcases Nat.lt_or_ge m (K + 1) with hlt | hge
      · exact ih m (by omega)
      · have hmeq : m = K + 1 := by omega
        subst hmeq
        have hreach : Reachable f lam N (K + 1) (gridIdx (N - ((K+1:ℕ):ℤ)) z).1
            (gridIdx (N - ((K+1:ℕ):ℤ)) z).2 := by
          intro t ht1 ht2
          set mm : ℕ := (K + 1) - t with hmm_def
          have hmmk : mm ≤ K := by omega
          have hsum : mm + t = K + 1 := by omega
          have hcast : (mm : ℤ) + (t : ℤ) = ((K + 1 : ℕ) : ℤ) := by exact_mod_cast hsum
          have hanc := gridIdx_ancestor (N - (mm : ℤ)) t z
          have hbase : N - (mm : ℤ) - (t : ℤ) = N - ((K + 1 : ℕ) : ℤ) := by omega
          rw [hbase] at hanc
          have h1 : ancestorIdx t (gridIdx (N - ((K + 1 : ℕ) : ℤ)) z).1 =
              (gridIdx (N - (mm : ℤ)) z).1 := congrArg Prod.fst hanc
          have h2 : ancestorIdx t (gridIdx (N - ((K + 1 : ℕ) : ℤ)) z).2 =
              (gridIdx (N - (mm : ℤ)) z).2 := congrArg Prod.snd hanc
          rw [h1, h2]
          exact ih mm hmmk
        have hsel := hns (K + 1)
        unfold Selected at hsel
        push_neg at hsel
        exact hsel hreach

/-- No level-`N` (`k = 0`) square is ever selected, given `N` is a valid starting scale. -/
theorem selected_k_pos {f : ℂ → ℂ} {lam : ℝ} {N : ℤ} {k : ℕ} {i j : ℤ}
    (hstart : ∀ i j, avgAbs f (dyadicSquare N i j) ≤ lam) (hsel : Selected f lam N k i j) :
    0 < k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exfalso
    unfold Selected at hsel
    have heq : N - ((k:ℕ):ℤ) = N := by rw [hk0]; norm_num
    rw [heq] at hsel
    exact absurd (hstart i j) (not_le.mpr hsel.2)
  · exact hkpos

theorem dyadicSquare_volume_parent_eq (n i j : ℤ) :
    volume (dyadicSquare n (i / 2) (j / 2)) = 4 * volume (dyadicSquare (n - 1) i j) := by
  rw [dyadicSquare_volume, dyadicSquare_volume]
  have h2n1 : (2:ℝ) ^ n = 2 * (2:ℝ) ^ (n - 1) := by
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
    ring
  rw [h2n1, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_pow]
  congr 1
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- A selected square's average is `≤ 4·lam`: its parent (one level up) is not selected — every
`Reachable` square's parent has average `≤ lam` — and the parent's volume is `4×` the child's. -/
theorem selected_avg_le_four {f : ℂ → ℂ} (hf : Integrable f volume) {lam : ℝ} {N : ℤ} {k : ℕ}
    {i j : ℤ} (hstart : ∀ i j, avgAbs f (dyadicSquare N i j) ≤ lam)
    (hsel : Selected f lam N k i j) :
    avgAbs f (dyadicSquare (N - (k:ℤ)) i j) ≤ 4 * lam := by
  have hkpos := selected_k_pos hstart hsel
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
  subst hk'
  have hparent : avgAbs f (dyadicSquare (N - (k':ℤ)) (i / 2) (j / 2)) ≤ lam := by
    have h1 := hsel.1 1 (le_refl 1) (by omega)
    have heq : (N - ((k' + 1 - 1 : ℕ):ℤ)) = N - (k':ℤ) := by norm_num
    rw [heq] at h1
    simpa [ancestorIdx] using h1
  have hcontain : dyadicSquare (N - (k'+1:ℕ):ℤ) i j ⊆ dyadicSquare (N - (k':ℤ)) (i / 2) (j / 2) := by
    have h := dyadicSquare_subset_parent (N - (k':ℤ)) i j
    have heq : (N - (k':ℤ)) - 1 = N - ((k'+1:ℕ):ℤ) := by push_cast; ring
    rwa [heq] at h
  have hvolrel : volume (dyadicSquare (N - (k':ℤ)) (i / 2) (j / 2)) =
      4 * volume (dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j) := by
    have := dyadicSquare_volume_parent_eq (N - (k':ℤ)) i j
    have heq : (N - (k':ℤ)) - 1 = N - ((k'+1:ℕ):ℤ) := by push_cast; ring
    rwa [heq] at this
  have hintbound : (∫ ζ in dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j, ‖f ζ‖) ≤
      ∫ ζ in dyadicSquare (N - (k':ℤ)) (i / 2) (j / 2), ‖f ζ‖ :=
    setIntegral_mono_set hf.norm.integrableOn (Eventually.of_forall fun z => norm_nonneg (f z))
      (Eventually.of_forall hcontain)
  have hchildpos := dyadicSquare_volume_pos (N - ((k'+1:ℕ):ℤ)) i j
  have hchildnetop := dyadicSquare_volume_ne_top (N - ((k'+1:ℕ):ℤ)) i j
  have hparentpos := dyadicSquare_volume_pos (N - (k':ℤ)) (i/2) (j/2)
  have hparentnetop := dyadicSquare_volume_ne_top (N - (k':ℤ)) (i/2) (j/2)
  have hchildToReal : 0 < (volume (dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j)).toReal :=
    ENNReal.toReal_pos hchildpos.ne' hchildnetop
  have hparentToReal : 0 < (volume (dyadicSquare (N - (k':ℤ)) (i/2) (j/2))).toReal :=
    ENNReal.toReal_pos hparentpos.ne' hparentnetop
  have hvolrelReal : (volume (dyadicSquare (N - (k':ℤ)) (i/2) (j/2))).toReal
      = 4 * (volume (dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j)).toReal := by
    rw [hvolrel, ENNReal.toReal_mul]
    norm_num
  unfold avgAbs at hparent ⊢
  rw [div_le_iff₀ hparentToReal] at hparent
  rw [div_le_iff₀ hchildToReal]
  calc (∫ ζ in dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j, ‖f ζ‖)
      ≤ ∫ ζ in dyadicSquare (N - (k':ℤ)) (i / 2) (j / 2), ‖f ζ‖ := hintbound
    _ ≤ lam * (volume (dyadicSquare (N - (k':ℤ)) (i/2) (j/2))).toReal := hparent
    _ = lam * (4 * (volume (dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j)).toReal) := by rw [hvolrelReal]
    _ = 4 * lam * (volume (dyadicSquare (N - ((k'+1:ℕ):ℤ)) i j)).toReal := by ring

/-! ### The selected index set, its measure-sum bound -/

/-- The (countable, as a subtype of `ℕ × ℤ × ℤ`) index set of selected squares. -/
def SelIdx (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) : Type :=
  {p : ℕ × ℤ × ℤ // Selected f lam N p.1 p.2.1 p.2.2}

instance instCountableSelIdx (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) : Countable (SelIdx f lam N) :=
  Subtype.countable

/-- The square itself, at a selected index. -/
noncomputable def SelQ (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (p : SelIdx f lam N) : Set ℂ :=
  dyadicSquare (N - (p.1.1 : ℤ)) p.1.2.1 p.1.2.2

theorem selQ_pairwise_disjoint (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) :
    Pairwise (Function.onFun Disjoint (SelQ f lam N)) := by
  intro p q hpq
  refine selected_disjoint p.2 q.2 (fun h => hpq (Subtype.ext ?_))
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simpa using h

theorem selQ_measurableSet (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (p : SelIdx f lam N) :
    MeasurableSet (SelQ f lam N p) :=
  dyadicSquare_measurableSet _ _ _

/-- The measure-sum bound: `Σ volume (SelQ p) ≤ ‖f‖₁ / lam`. -/
theorem selQ_measure_sum_le (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    (N : ℤ) :
    ENNReal.ofReal lam * (∑' p : SelIdx f lam N, volume (SelQ f lam N p)) ≤
      ENNReal.ofReal (∫ z, ‖f z‖) := by
  have hstep : ∀ p : SelIdx f lam N, ENNReal.ofReal lam * volume (SelQ f lam N p) ≤
      ∫⁻ ζ in SelQ f lam N p, ‖f ζ‖ₑ := by
    intro p
    have hsel := p.2
    unfold Selected avgAbs at hsel
    have hvolpos : 0 < volume (SelQ f lam N p) := dyadicSquare_volume_pos _ _ _
    have hvolnetop : volume (SelQ f lam N p) ≠ ⊤ := dyadicSquare_volume_ne_top _ _ _
    have hvolToRealPos : 0 < (volume (SelQ f lam N p)).toReal :=
      ENNReal.toReal_pos hvolpos.ne' hvolnetop
    have hlt : lam * (volume (SelQ f lam N p)).toReal ≤ ∫ ζ in SelQ f lam N p, ‖f ζ‖ := by
      rw [← le_div_iff₀ hvolToRealPos]
      exact hsel.2.le
    have hint_nonneg : (0:ℝ) ≤ ∫ ζ in SelQ f lam N p, ‖f ζ‖ :=
      setIntegral_nonneg (selQ_measurableSet f lam N p) (fun z _ => norm_nonneg _)
    have hconv : (∫⁻ ζ in SelQ f lam N p, ‖f ζ‖ₑ) = ENNReal.ofReal (∫ ζ in SelQ f lam N p, ‖f ζ‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hf.norm.integrableOn)
        (Eventually.of_forall fun z => norm_nonneg (f z))]
      simp only [ofReal_norm]
    rw [hconv, ← ENNReal.ofReal_toReal hvolnetop, ← ENNReal.ofReal_mul hlam.le]
    exact ENNReal.ofReal_le_ofReal hlt
  have hsum : ∑' p : SelIdx f lam N, ENNReal.ofReal lam * volume (SelQ f lam N p) ≤
      ∑' p : SelIdx f lam N, ∫⁻ ζ in SelQ f lam N p, ‖f ζ‖ₑ :=
    ENNReal.tsum_le_tsum hstep
  rw [ENNReal.tsum_mul_left] at hsum
  calc ENNReal.ofReal lam * (∑' p : SelIdx f lam N, volume (SelQ f lam N p))
      ≤ ∑' p : SelIdx f lam N, ∫⁻ ζ in SelQ f lam N p, ‖f ζ‖ₑ := hsum
    _ = ∫⁻ ζ in ⋃ p, SelQ f lam N p, ‖f ζ‖ₑ :=
        (lintegral_iUnion (selQ_measurableSet f lam N) (selQ_pairwise_disjoint f lam N)
          (fun ζ => ‖f ζ‖ₑ)).symm
    _ ≤ ∫⁻ ζ, ‖f ζ‖ₑ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (∫ z, ‖f z‖) := by
        rw [ofReal_integral_eq_lintegral_ofReal hf.norm
          (Eventually.of_forall fun z => norm_nonneg (f z))]
        simp only [ofReal_norm]

/-! ### Defining `g, b` from the selected squares -/

/-- The average of `f` over a set. -/
noncomputable def czAvg (f : ℂ → ℂ) (Q : Set ℂ) : ℂ := ((volume Q).toReal)⁻¹ • (∫ ζ in Q, f ζ)

open Classical in
/-- The `n`-th term of the (ℕ-indexed, via a `Denumerable` bijection with `ℕ × ℤ × ℤ`) countable
sum defining `czB`: nonzero exactly when the `n`-th triple is selected and contains `z`. -/
noncomputable def czTerm (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (n : ℕ) (z : ℂ) : ℂ :=
  let t := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n
  if Selected f lam N t.1 t.2.1 t.2.2 ∧ z ∈ dyadicSquare (N - (t.1 : ℤ)) t.2.1 t.2.2
  then f z - czAvg f (dyadicSquare (N - (t.1 : ℤ)) t.2.1 t.2.2)
  else 0

noncomputable def czB (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (z : ℂ) : ℂ := ∑' n : ℕ, czTerm f lam N n z

noncomputable def czG (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (z : ℂ) : ℂ := f z - czB f lam N z

/-- Only `AEStronglyMeasurable f` is available at the export boundary (`Integrable f volume`
gives no more), so this — not `Measurable` — is the level every measurability fact in the `g, b`
construction is built at. -/
theorem czTerm_aestronglyMeasurable (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume) (lam : ℝ)
    (N : ℤ) (n : ℕ) :
    AEStronglyMeasurable (czTerm f lam N n) volume := by
  unfold czTerm
  set t := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n
  by_cases hsel : Selected f lam N t.1 t.2.1 t.2.2
  · have hfun : (fun z => if Selected f lam N t.1 t.2.1 t.2.2 ∧
        z ∈ dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2
        then f z - czAvg f (dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2) else 0) =
        (dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2).indicator
          (fun z => f z - czAvg f (dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2)) := by
      funext z
      by_cases hz : z ∈ dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2
      · rw [if_pos ⟨hsel, hz⟩, Set.indicator_of_mem hz]
      · rw [if_neg (fun h => hz h.2), Set.indicator_of_notMem hz]
    rw [hfun]
    exact (hf.sub aestronglyMeasurable_const).indicator (dyadicSquare_measurableSet _ _ _)
  · have hfun : (fun z => if Selected f lam N t.1 t.2.1 t.2.2 ∧
        z ∈ dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2
        then f z - czAvg f (dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2) else 0) = fun _ => (0:ℂ) := by
      funext z
      rw [if_neg (fun h => hsel h.1)]
    rw [hfun]
    exact aestronglyMeasurable_const

/-- The unique-term identity: if `z` lies in a selected square `(k, i, j)`, `czB` reduces to the
single term for that square's index. -/
theorem czB_eq_of_mem {f : ℂ → ℂ} {lam : ℝ} {N : ℤ} {k : ℕ} {i j : ℤ} {z : ℂ}
    (hsel : Selected f lam N k i j) (hz : z ∈ dyadicSquare (N - (k : ℤ)) i j) :
    czB f lam N z = f z - czAvg f (dyadicSquare (N - (k : ℤ)) i j) := by
  set n₀ := Denumerable.eqv (ℕ × ℤ × ℤ) (k, i, j) with hn₀_def
  have ht0 : (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n₀ = (k, i, j) := by
    rw [hn₀_def, Equiv.symm_apply_apply]
  unfold czB
  rw [tsum_eq_single n₀ (fun n hn => ?_)]
  · show czTerm f lam N n₀ z = _
    unfold czTerm
    rw [ht0]
    simp only [hsel, hz, and_self, if_true]
  · show czTerm f lam N n z = 0
    unfold czTerm
    set t := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n with ht_def
    by_cases hcond : Selected f lam N t.1 t.2.1 t.2.2 ∧ z ∈ dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2
    · exfalso
      have htriv : t = (k, i, j) := by
        by_contra hne
        exact Set.disjoint_left.mp (selected_disjoint hcond.1 hsel hne) hcond.2 hz
      apply hn
      calc n = Denumerable.eqv (ℕ × ℤ × ℤ) ((Denumerable.eqv (ℕ × ℤ × ℤ)).symm n) :=
            (Equiv.apply_symm_apply _ n).symm
        _ = Denumerable.eqv (ℕ × ℤ × ℤ) (k, i, j) := by rw [← ht_def, htriv]
        _ = n₀ := hn₀_def.symm
    · simp [hcond]

/-- `czB` vanishes off the union of selected squares. -/
theorem czB_eq_zero_of_not_mem {f : ℂ → ℂ} {lam : ℝ} {N : ℤ} {z : ℂ}
    (hz : ∀ k : ℕ, ∀ i j : ℤ, Selected f lam N k i j → z ∉ dyadicSquare (N - (k:ℤ)) i j) :
    czB f lam N z = 0 := by
  unfold czB
  have hall : ∀ n : ℕ, czTerm f lam N n z = 0 := by
    intro n
    unfold czTerm
    set t := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n
    by_cases hcond : Selected f lam N t.1 t.2.1 t.2.2 ∧ z ∈ dyadicSquare (N - (t.1:ℤ)) t.2.1 t.2.2
    · exact absurd hcond.2 (hz t.1 t.2.1 t.2.2 hcond.1)
    · simp [hcond]
  simp only [hall, tsum_zero]

/-- At most one `n` gives a nonzero term at a given `z` (by disjointness): the term's support
in `n` is contained in a singleton (if `z` lies in a selected square) or empty. -/
theorem czTerm_support_subsingleton (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (z : ℂ) :
    (Function.support (fun n => czTerm f lam N n z)).Subsingleton := by
  intro n₁ hn₁ n₂ hn₂
  simp only [Function.mem_support] at hn₁ hn₂
  set t₁ := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n₁ with ht₁_def
  set t₂ := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm n₂ with ht₂_def
  have hcond₁ : Selected f lam N t₁.1 t₁.2.1 t₁.2.2 ∧
      z ∈ dyadicSquare (N - (t₁.1:ℤ)) t₁.2.1 t₁.2.2 := by
    by_contra hc; exact hn₁ (by unfold czTerm; rw [← ht₁_def]; simp [hc])
  have hcond₂ : Selected f lam N t₂.1 t₂.2.1 t₂.2.2 ∧
      z ∈ dyadicSquare (N - (t₂.1:ℤ)) t₂.2.1 t₂.2.2 := by
    by_contra hc; exact hn₂ (by unfold czTerm; rw [← ht₂_def]; simp [hc])
  have ht12 : t₁ = t₂ := by
    by_contra hne
    exact Set.disjoint_left.mp (selected_disjoint hcond₁.1 hcond₂.1 hne) hcond₁.2 hcond₂.2
  calc n₁ = Denumerable.eqv (ℕ × ℤ × ℤ) t₁ := (Equiv.apply_symm_apply _ n₁).symm
    _ = Denumerable.eqv (ℕ × ℤ × ℤ) t₂ := by rw [ht12]
    _ = n₂ := Equiv.apply_symm_apply _ n₂

theorem czTerm_summable (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) (z : ℂ) :
    Summable (fun n => czTerm f lam N n z) :=
  summable_of_hasFiniteSupport ((czTerm_support_subsingleton f lam N z).finite)

/-- `czB` is `AEStronglyMeasurable`, given `f` is: the countable sum's partial sums are eventually
constant at every point (at most one nonzero term), so they converge everywhere (hence a.e.), and
an a.e. limit of `AEStronglyMeasurable` functions is `AEStronglyMeasurable`. -/
theorem czB_aestronglyMeasurable (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume) (lam : ℝ)
    (N : ℤ) :
    AEStronglyMeasurable (czB f lam N) volume := by
  have hpartial : ∀ m : ℕ,
      AEStronglyMeasurable (fun z => ∑ n ∈ Finset.range m, czTerm f lam N n z) volume := by
    intro m
    rw [← Finset.sum_fn]
    exact Finset.aestronglyMeasurable_sum _ (fun n _ => czTerm_aestronglyMeasurable f hf lam N n)
  refine aestronglyMeasurable_of_tendsto_ae atTop hpartial (Eventually.of_forall fun z => ?_)
  have hsum : HasSum (fun n => czTerm f lam N n z) (czB f lam N z) :=
    (czTerm_summable f lam N z).hasSum
  exact hsum.tendsto_sum_nat

/-- `czB` has mean zero on each selected square. -/
theorem czB_integral_selQ_eq_zero (f : ℂ → ℂ) (hf : Integrable f volume) (lam : ℝ) (N : ℤ)
    (p : SelIdx f lam N) :
    ∫ ζ in SelQ f lam N p, czB f lam N ζ = 0 := by
  obtain ⟨⟨k, i, j⟩, hsel⟩ := p
  have hQ : SelQ f lam N ⟨(k, i, j), hsel⟩ = dyadicSquare (N - (k:ℤ)) i j := rfl
  have heq : Set.EqOn (czB f lam N) (fun ζ => f ζ - czAvg f (dyadicSquare (N - (k:ℤ)) i j))
      (dyadicSquare (N - (k:ℤ)) i j) := fun ζ hζ => czB_eq_of_mem hsel hζ
  rw [hQ, setIntegral_congr_fun (dyadicSquare_measurableSet _ _ _) heq]
  have hvolnetop := dyadicSquare_volume_ne_top (N - (k:ℤ)) i j
  rw [integral_sub hf.integrableOn (integrableOn_const hvolnetop),
    setIntegral_const, czAvg, smul_smul]
  have hvolpos := dyadicSquare_volume_pos (N - (k:ℤ)) i j
  have hvolToRealPos : 0 < (volume (dyadicSquare (N - (k:ℤ)) i j)).toReal :=
    ENNReal.toReal_pos hvolpos.ne' hvolnetop
  have hreal_eq : volume.real (dyadicSquare (N - (k:ℤ)) i j) =
      (volume (dyadicSquare (N - (k:ℤ)) i j)).toReal := rfl
  rw [hreal_eq, mul_inv_cancel₀ hvolToRealPos.ne', one_smul, sub_self]

/-- The support of `czB` is contained in the union of the selected squares. -/
theorem czB_support_subset (f : ℂ → ℂ) (lam : ℝ) (N : ℤ) :
    Function.support (czB f lam N) ⊆ ⋃ p : SelIdx f lam N, SelQ f lam N p := by
  intro z hz
  by_contra hz'
  simp only [Set.mem_iUnion, not_exists] at hz'
  apply hz
  apply czB_eq_zero_of_not_mem
  intro k i j hsel
  exact hz' ⟨(k, i, j), hsel⟩

/-- Jensen: the norm of the average is at most the average of the norm. -/
theorem norm_czAvg_le_avgAbs (f : ℂ → ℂ) (Q : Set ℂ) :
    ‖czAvg f Q‖ ≤ avgAbs f Q := by
  unfold czAvg avgAbs
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg ENNReal.toReal_nonneg, div_eq_inv_mul]
  rcases eq_or_ne (volume Q).toReal 0 with h0 | h0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm f) (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- `czB`'s `L¹` norm on each selected square is at most twice `f`'s. -/
theorem czB_norm_integral_selQ_le (f : ℂ → ℂ) (hf : Integrable f volume) (lam : ℝ) (N : ℤ)
    (p : SelIdx f lam N) :
    (∫ ζ in SelQ f lam N p, ‖czB f lam N ζ‖) ≤ 2 * ∫ ζ in SelQ f lam N p, ‖f ζ‖ := by
  obtain ⟨⟨k, i, j⟩, hsel⟩ := p
  have hQ : SelQ f lam N ⟨(k, i, j), hsel⟩ = dyadicSquare (N - (k:ℤ)) i j := rfl
  set Q := dyadicSquare (N - (k:ℤ)) i j with hQdef
  rw [hQ]
  have hmeas : MeasurableSet Q := dyadicSquare_measurableSet _ _ _
  have hvolnetop : volume Q ≠ ⊤ := dyadicSquare_volume_ne_top _ _ _
  have heq : Set.EqOn (fun ζ => ‖czB f lam N ζ‖) (fun ζ => ‖f ζ - czAvg f Q‖) Q :=
    fun ζ hζ => by show ‖czB f lam N ζ‖ = ‖f ζ - czAvg f Q‖; rw [czB_eq_of_mem hsel hζ]
  rw [setIntegral_congr_fun hmeas heq]
  have hintf : IntegrableOn f Q volume := hf.integrableOn
  have hintconst : IntegrableOn (fun _ : ℂ => czAvg f Q) Q volume := integrableOn_const hvolnetop
  have hbound : (∫ ζ in Q, ‖f ζ - czAvg f Q‖) ≤ ∫ ζ in Q, ‖f ζ‖ + ‖czAvg f Q‖ := by
    apply setIntegral_mono_on (hintf.sub hintconst).norm (hintf.norm.add hintconst.norm) hmeas
    intro ζ _
    exact norm_sub_le _ _
  rw [integral_add hintf.norm hintconst.norm, setIntegral_const] at hbound
  have hJensen := norm_czAvg_le_avgAbs f Q
  have havgeq : avgAbs f Q * volume.real Q = ∫ ζ in Q, ‖f ζ‖ := by
    unfold avgAbs
    rcases eq_or_ne (volume Q).toReal 0 with h0 | h0
    · have hreal_eq : volume.real Q = (volume Q).toReal := rfl
      rw [hreal_eq, h0, mul_zero]
      have hvol0 : volume Q = 0 := by
        rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hvolnetop] at h0
      exact (setIntegral_measure_zero _ hvol0).symm
    · have hreal_eq : volume.real Q = (volume Q).toReal := rfl
      rw [hreal_eq, div_mul_cancel₀ _ h0]
  calc (∫ ζ in Q, ‖f ζ - czAvg f Q‖) ≤ (∫ ζ in Q, ‖f ζ‖) + volume.real Q • ‖czAvg f Q‖ := hbound
    _ ≤ (∫ ζ in Q, ‖f ζ‖) + volume.real Q * avgAbs f Q := by
        have hvolnn : (0:ℝ) ≤ volume.real Q := by
          have : volume.real Q = (volume Q).toReal := rfl
          rw [this]; exact ENNReal.toReal_nonneg
        have := mul_le_mul_of_nonneg_left hJensen hvolnn
        simp only [smul_eq_mul]
        linarith [this]
    _ = (∫ ζ in Q, ‖f ζ‖) + ∫ ζ in Q, ‖f ζ‖ := by rw [mul_comm, havgeq]
    _ = 2 * ∫ ζ in Q, ‖f ζ‖ := by ring

/-- A crude pointwise bound, uniform in `ζ`: `‖czB ζ‖ ≤ ‖f ζ‖` off the union of selected squares,
and `≤ ‖f ζ‖ + 4·lam` on it. Packaged with the indicator of the union so integrating gives a
FINITE bound (the union has finite measure), unlike the uniform bound `‖f ζ‖ + 4·lam` alone. -/
theorem czB_norm_le_pointwise {f : ℂ → ℂ} (hf : Integrable f volume) {lam : ℝ} {N : ℤ}
    (hstart : ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam) (ζ : ℂ) :
    ‖czB f lam N ζ‖ ≤
      ‖f ζ‖ + 4 * lam * (⋃ p : SelIdx f lam N, SelQ f lam N p).indicator (fun _ => (1:ℝ)) ζ := by
  by_cases hζ : ζ ∈ ⋃ p : SelIdx f lam N, SelQ f lam N p
  · rw [Set.indicator_of_mem hζ]
    obtain ⟨p, hζp⟩ := Set.mem_iUnion.mp hζ
    obtain ⟨⟨k, i, j⟩, hsel⟩ := p
    have hζQ : ζ ∈ dyadicSquare (N - (k:ℤ)) i j := hζp
    rw [czB_eq_of_mem hsel hζQ, mul_one]
    calc ‖f ζ - czAvg f (dyadicSquare (N - (k:ℤ)) i j)‖
        ≤ ‖f ζ‖ + ‖czAvg f (dyadicSquare (N - (k:ℤ)) i j)‖ := norm_sub_le _ _
      _ ≤ ‖f ζ‖ + avgAbs f (dyadicSquare (N - (k:ℤ)) i j) := by
          linarith [norm_czAvg_le_avgAbs f (dyadicSquare (N - (k:ℤ)) i j)]
      _ ≤ ‖f ζ‖ + 4 * lam := by
          linarith [selected_avg_le_four hf hstart hsel]
  · rw [Set.indicator_of_notMem hζ, mul_zero, add_zero]
    rw [czB_eq_zero_of_not_mem (fun k i j hsel hmem => hζ (Set.mem_iUnion.mpr ⟨⟨(k,i,j), hsel⟩, hmem⟩))]
    simpa using norm_nonneg (f ζ)

/-- The union of selected squares has finite measure. -/
theorem selQ_iUnion_volume_lt_top (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) (N : ℤ) :
    volume (⋃ p : SelIdx f lam N, SelQ f lam N p) ≠ ⊤ := by
  rw [measure_iUnion (selQ_pairwise_disjoint f lam N) (selQ_measurableSet f lam N)]
  have hbound := selQ_measure_sum_le f hf hlam N
  intro htop
  rw [htop, ENNReal.mul_top (by positivity : ENNReal.ofReal lam ≠ 0)] at hbound
  exact (lt_irrefl _ (hbound.trans_lt (by finiteness) : (⊤:ℝ≥0∞) < ⊤))

/-- `czB` is integrable, given `f` is, dominated by the (integrable) function
`‖f ζ‖ + 4·lam·1_U ζ`. -/
theorem czB_integrable (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) {N : ℤ}
    (hstart : ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam) :
    Integrable (czB f lam N) volume := by
  set U : Set ℂ := ⋃ p : SelIdx f lam N, SelQ f lam N p with hU_def
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion (fun p => selQ_measurableSet f lam N p)
  have hUvolFin : volume U ≠ ⊤ := selQ_iUnion_volume_lt_top f hf hlam N
  have hIndInt : Integrable (U.indicator (fun _ : ℂ => (1:ℝ))) volume :=
    (integrable_indicator_iff hUmeas).mpr (integrableOn_const hUvolFin)
  have hDomInt : Integrable (fun ζ => ‖f ζ‖ + 4 * lam * U.indicator (fun _ => (1:ℝ)) ζ) volume :=
    hf.norm.add (hIndInt.const_mul (4 * lam))
  exact Integrable.mono' hDomInt (czB_aestronglyMeasurable f hf.aestronglyMeasurable lam N)
    (Eventually.of_forall (czB_norm_le_pointwise hf hstart))

/-- The global `L¹` bound: `∫‖czB‖ ≤ 2∫‖f‖`. -/
theorem czB_norm_integral_le (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    {N : ℤ} (hstart : ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam) :
    (∫ ζ, ‖czB f lam N ζ‖) ≤ 2 * ∫ ζ, ‖f ζ‖ := by
  have hbint := czB_integrable f hf hlam hstart
  set U : Set ℂ := ⋃ p : SelIdx f lam N, SelQ f lam N p with hU_def
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion (fun p => selQ_measurableSet f lam N p)
  have hzero_off : Set.EqOn (fun ζ => ‖czB f lam N ζ‖) 0 Uᶜ := by
    intro ζ hζ
    have hnotmem : ζ ∉ Function.support (czB f lam N) := fun h =>
      hζ (czB_support_subset f lam N h)
    simp only [Function.mem_support, not_not] at hnotmem
    simp [hnotmem]
  have hcompl0 : (∫ ζ in Uᶜ, ‖czB f lam N ζ‖) = 0 := by
    rw [setIntegral_congr_fun hUmeas.compl hzero_off]
    simp
  have hsplit : (∫ ζ in U, ‖czB f lam N ζ‖) + ∫ ζ in Uᶜ, ‖czB f lam N ζ‖ = ∫ ζ, ‖czB f lam N ζ‖ :=
    integral_add_compl hUmeas hbint.norm
  rw [hcompl0, add_zero] at hsplit
  rw [← hsplit]
  have hsum_b : HasSum (fun p : SelIdx f lam N => ∫ ζ in SelQ f lam N p, ‖czB f lam N ζ‖)
      (∫ ζ in U, ‖czB f lam N ζ‖) :=
    hasSum_integral_iUnion (selQ_measurableSet f lam N) (selQ_pairwise_disjoint f lam N)
      hbint.norm.integrableOn
  have hsum_f : HasSum (fun p : SelIdx f lam N => ∫ ζ in SelQ f lam N p, ‖f ζ‖)
      (∫ ζ in U, ‖f ζ‖) :=
    hasSum_integral_iUnion (selQ_measurableSet f lam N) (selQ_pairwise_disjoint f lam N)
      hf.norm.integrableOn
  have hle : (∫ ζ in U, ‖czB f lam N ζ‖) ≤ 2 * ∫ ζ in U, ‖f ζ‖ :=
    hasSum_mono hsum_b (hsum_f.mul_left 2) (fun p => czB_norm_integral_selQ_le f hf lam N p)
  refine hle.trans ?_
  have : (∫ ζ in U, ‖f ζ‖) ≤ ∫ ζ, ‖f ζ‖ := setIntegral_le_integral hf.norm
    (Eventually.of_forall fun z => norm_nonneg (f z))
  linarith

/-! ### Engulfing balls -/

/-- The centre of the dyadic square `(n, i, j)`. -/
noncomputable def dyadicCenter (n i j : ℤ) : ℂ :=
  ⟨(i:ℝ) * (2:ℝ) ^ n + (2:ℝ) ^ n / 2, (j:ℝ) * (2:ℝ) ^ n + (2:ℝ) ^ n / 2⟩

/-- Any point whose coordinates satisfy the (possibly non-strict) dyadic-square bounds is within
`2^n/√2` of the square's centre. Stated with `≤` throughout so it covers both the half-open
`dyadicSquare` and a closed variant. -/
theorem dist_dyadicCenter_le {n i j : ℤ} {z : ℂ}
    (h1 : (i:ℝ) * (2:ℝ) ^ n ≤ z.re) (h2 : z.re ≤ ((i:ℝ) + 1) * (2:ℝ) ^ n)
    (h3 : (j:ℝ) * (2:ℝ) ^ n ≤ z.im) (h4 : z.im ≤ ((j:ℝ) + 1) * (2:ℝ) ^ n) :
    dist z (dyadicCenter n i j) ≤ (2:ℝ) ^ n / Real.sqrt 2 := by
  set s : ℝ := (2:ℝ) ^ n with hs_def
  set c : ℂ := dyadicCenter n i j with hc_def
  set r : ℝ := s / Real.sqrt 2 with hr_def
  rw [Complex.dist_eq]
  have hre : |z.re - c.re| ≤ s / 2 := by
    rw [hc_def, dyadicCenter]; simp only; rw [abs_le]; constructor <;> linarith
  have him : |z.im - c.im| ≤ s / 2 := by
    rw [hc_def, dyadicCenter]; simp only; rw [abs_le]; constructor <;> linarith
  have hnormsq : Complex.normSq (z - c) ≤ r ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    have h1' : (z.re - c.re) ^ 2 ≤ (s / 2) ^ 2 :=
      sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
    have h2' : (z.im - c.im) ^ 2 ≤ (s / 2) ^ 2 :=
      sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    have hrsq : r ^ 2 = (s / 2) ^ 2 + (s / 2) ^ 2 := by
      rw [hr_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    nlinarith [h1', h2', hrsq]
  rw [Complex.norm_def]
  rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt hnormsq

/-- Every dyadic square is engulfed by a ball centred at its midpoint, with radius the
half-diagonal, and satisfies the doubling bound with `C₀ = 2π`. -/
theorem dyadicSquare_engulf (n i j : ℤ) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ dyadicSquare n i j ⊆ closedBall c r ∧
      volume (closedBall c (2 * r)) ≤ ENNReal.ofReal (2 * π) * volume (dyadicSquare n i j) := by
  set s : ℝ := (2:ℝ) ^ n with hs_def
  have hspos : 0 < s := by positivity
  set r : ℝ := s / Real.sqrt 2 with hr_def
  refine ⟨dyadicCenter n i j, r, by positivity, ?_, ?_⟩
  · intro z hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    exact dist_dyadicCenter_le hz1 hz2.le hz3 hz4.le
  · rw [Complex.volume_closedBall, dyadicSquare_volume]
    have h2r : (2 * r) ^ 2 = 2 * s ^ 2 := by
      rw [hr_def, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    have hcast : ENNReal.ofReal (2 * r) ^ 2 = ENNReal.ofReal ((2 * r) ^ 2) :=
      (ENNReal.ofReal_pow (by positivity) 2).symm
    rw [hcast, h2r]
    have hpi_eq : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    rw [hpi_eq, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * s ^ 2),
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (2:ℝ) ^ n) 2,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * π)]
    apply ENNReal.ofReal_le_ofReal
    rw [hs_def]
    nlinarith

/-! ### The Lebesgue differentiation step, via a Vitali family of closed dyadic squares -/

/-- The closed dyadic square: same as `dyadicSquare` with `≤` in place of `<` on the upper
bounds. Needed because the Vitali family requires closed members. -/
def dyadicSquareClosed (n i j : ℤ) : Set ℂ :=
  {z : ℂ | (i : ℝ) * (2 : ℝ) ^ n ≤ z.re ∧ z.re ≤ ((i : ℝ) + 1) * (2 : ℝ) ^ n ∧
    (j : ℝ) * (2 : ℝ) ^ n ≤ z.im ∧ z.im ≤ ((j : ℝ) + 1) * (2 : ℝ) ^ n}

theorem dyadicSquare_subset_closed (n i j : ℤ) :
    dyadicSquare n i j ⊆ dyadicSquareClosed n i j :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2.le, h3, h4.le⟩

theorem dyadicSquareClosed_isClosed (n i j : ℤ) : IsClosed (dyadicSquareClosed n i j) := by
  have heq : dyadicSquareClosed n i j =
      (fun z : ℂ => z.re) ⁻¹' (Set.Icc ((i:ℝ) * (2:ℝ)^n) (((i:ℝ)+1) * (2:ℝ)^n)) ∩
      (fun z : ℂ => z.im) ⁻¹' (Set.Icc ((j:ℝ) * (2:ℝ)^n) (((j:ℝ)+1) * (2:ℝ)^n)) := by
    ext z; simp [dyadicSquareClosed, Set.mem_Icc, and_assoc]
  rw [heq]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

theorem dyadicSquareClosed_interior_nonempty (n i j : ℤ) :
    (interior (dyadicSquareClosed n i j)).Nonempty := by
  refine ⟨dyadicCenter n i j, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hspos : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hopen : IsOpen {z : ℂ | (i:ℝ) * (2:ℝ)^n < z.re ∧ z.re < ((i:ℝ)+1) * (2:ℝ)^n ∧
      (j:ℝ) * (2:ℝ)^n < z.im ∧ z.im < ((j:ℝ)+1) * (2:ℝ)^n} := by
    have : {z : ℂ | (i:ℝ) * (2:ℝ)^n < z.re ∧ z.re < ((i:ℝ)+1) * (2:ℝ)^n ∧
        (j:ℝ) * (2:ℝ)^n < z.im ∧ z.im < ((j:ℝ)+1) * (2:ℝ)^n} =
        (fun z : ℂ => z.re) ⁻¹' (Set.Ioo ((i:ℝ) * (2:ℝ)^n) (((i:ℝ)+1) * (2:ℝ)^n)) ∩
        (fun z : ℂ => z.im) ⁻¹' (Set.Ioo ((j:ℝ) * (2:ℝ)^n) (((j:ℝ)+1) * (2:ℝ)^n)) := by
      ext z; simp [Set.mem_Ioo, and_assoc]
    rw [this]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  refine mem_of_superset (hopen.mem_nhds ⟨by simp [dyadicCenter]; linarith,
    by simp [dyadicCenter]; linarith, by simp [dyadicCenter]; linarith,
    by simp [dyadicCenter]; linarith⟩) (fun z ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩)

theorem dyadicSquareClosed_eq_preimage (n i j : ℤ) :
    dyadicSquareClosed n i j =
      Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc ((i : ℝ) * (2 : ℝ) ^ n) (((i : ℝ) + 1) * (2 : ℝ) ^ n) ×ˢ
          Set.Icc ((j : ℝ) * (2 : ℝ) ^ n) (((j : ℝ) + 1) * (2 : ℝ) ^ n)) := by
  ext z
  simp only [dyadicSquareClosed, Complex.measurableEquivRealProd_apply, Set.mem_Icc, Set.mem_prod,
    Set.mem_preimage, Set.mem_setOf_eq, and_assoc]

theorem dyadicSquareClosed_volume (n i j : ℤ) :
    volume (dyadicSquareClosed n i j) = ENNReal.ofReal ((2 : ℝ) ^ n) ^ 2 := by
  rw [dyadicSquareClosed_eq_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  rw [show ((i : ℝ) + 1) * (2 : ℝ) ^ n - (i : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ n by ring,
    show ((j : ℝ) + 1) * (2 : ℝ) ^ n - (j : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ n by ring, sq]

theorem dyadicSquareClosed_volume_eq (n i j : ℤ) :
    volume (dyadicSquareClosed n i j) = volume (dyadicSquare n i j) := by
  rw [dyadicSquareClosed_volume, dyadicSquare_volume]

/-- The doubling constant for the Vitali family: large enough for both the trivial ball-doubling
(`9`) and the dyadic-square engulfing doubling (`18π`, computed below). -/
noncomputable def Cvit : ℝ≥0 := 18 * NNReal.pi

theorem volume_closedBall_three_le (x : ℂ) (r : ℝ) :
    volume (closedBall x (3 * r)) ≤ (Cvit : ℝ≥0∞) * volume (closedBall x r) := by
  rw [Complex.volume_closedBall, Complex.volume_closedBall,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
    show ENNReal.ofReal (3:ℝ) = 3 by norm_num, mul_pow]
  have hpi_eq : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  rw [show Cvit = (18 * NNReal.pi : ℝ≥0) from rfl, ENNReal.coe_mul,
    show ((18:ℝ≥0):ℝ≥0∞) = 18 by norm_num, hpi_eq]
  have h9le : (9:ℝ≥0∞) ≤ 18 * ENNReal.ofReal π := by
    rw [show (9:ℝ≥0∞) = ENNReal.ofReal 9 by norm_num,
      show (18:ℝ≥0∞) = ENNReal.ofReal 18 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 18)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_gt_three])
  calc (3:ℝ≥0∞) ^ 2 * ENNReal.ofReal r ^ 2 * ENNReal.ofReal π
      = 9 * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal π) := by ring
    _ ≤ (18 * ENNReal.ofReal π) * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal π) := by gcongr
    _ = 18 * ENNReal.ofReal π * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal π) := by ring

theorem hVitCond : ∀ x : ℂ, ∃ᶠ r in 𝓝[>] (0:ℝ),
    volume (closedBall x (3 * r)) ≤ (Cvit : ℝ≥0∞) * volume (closedBall x r) :=
  fun x => Filter.Frequently.of_forall (fun r => volume_closedBall_three_le x r)

/-- The Vitali family of closed sets doubling relative to `Cvit`, on `ℂ` with Lebesgue measure. -/
noncomputable def vitFam : VitaliFamily (volume : Measure ℂ) :=
  Vitali.vitaliFamily volume Cvit hVitCond

/-- Two points both satisfying the (non-strict) dyadic-square-`(n,i,j)` coordinate bounds are
within `2^n·√2` of each other (both within `2^n/√2` of the common centre, then triangle
inequality). -/
theorem dist_le_of_dyadic_coords {n i j : ℤ} {x z : ℂ}
    (hx1 : (i:ℝ) * (2:ℝ)^n ≤ x.re) (hx2 : x.re ≤ ((i:ℝ)+1) * (2:ℝ)^n)
    (hx3 : (j:ℝ) * (2:ℝ)^n ≤ x.im) (hx4 : x.im ≤ ((j:ℝ)+1) * (2:ℝ)^n)
    (hz1 : (i:ℝ) * (2:ℝ)^n ≤ z.re) (hz2 : z.re ≤ ((i:ℝ)+1) * (2:ℝ)^n)
    (hz3 : (j:ℝ) * (2:ℝ)^n ≤ z.im) (hz4 : z.im ≤ ((j:ℝ)+1) * (2:ℝ)^n) :
    dist z x ≤ (2:ℝ) ^ n * Real.sqrt 2 := by
  set s : ℝ := (2:ℝ) ^ n with hs_def
  have hxc : dist x (dyadicCenter n i j) ≤ s / Real.sqrt 2 := dist_dyadicCenter_le hx1 hx2 hx3 hx4
  have hzc : dist z (dyadicCenter n i j) ≤ s / Real.sqrt 2 := dist_dyadicCenter_le hz1 hz2 hz3 hz4
  calc dist z x ≤ dist z (dyadicCenter n i j) + dist (dyadicCenter n i j) x := dist_triangle _ _ _
    _ = dist z (dyadicCenter n i j) + dist x (dyadicCenter n i j) := by
        rw [dist_comm (dyadicCenter n i j) x]
    _ ≤ s / Real.sqrt 2 + s / Real.sqrt 2 := add_le_add hzc hxc
    _ = s * Real.sqrt 2 := by
        have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hne : Real.sqrt 2 ≠ 0 := by positivity
        field_simp
        nlinarith [h2]

/-- Every closed dyadic square containing `x` belongs to `vitFam.setsAt x`. -/
theorem dyadicSquareClosed_mem_setsAt {n i j : ℤ} {x : ℂ} (hx : x ∈ dyadicSquareClosed n i j) :
    dyadicSquareClosed n i j ∈ vitFam.setsAt x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  set s : ℝ := (2:ℝ) ^ n with hs_def
  have hspos : 0 < s := by positivity
  refine ⟨dyadicSquareClosed_isClosed n i j, dyadicSquareClosed_interior_nonempty n i j,
    s * Real.sqrt 2, ?_, ?_⟩
  · -- dyadicSquareClosed n i j ⊆ closedBall x (s√2)
    intro z hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    rw [mem_closedBall]
    exact dist_le_of_dyadic_coords hx1 hx2 hx3 hx4 hz1 hz2 hz3 hz4
  · -- volume (closedBall x (3*(s√2))) ≤ Cvit * volume (dyadicSquareClosed n i j)
    rw [Complex.volume_closedBall, dyadicSquareClosed_volume, ← hs_def]
    have hpi_eq : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    have h3sr2 : (3 * (s * Real.sqrt 2)) ^ 2 = 18 * s ^ 2 := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [h2]
    have hLHS : ENNReal.ofReal (3 * (s * Real.sqrt 2)) ^ 2 * (NNReal.pi : ℝ≥0∞) =
        ENNReal.ofReal (18 * s ^ 2 * π) := by
      rw [← ENNReal.ofReal_pow (by positivity) 2, h3sr2, hpi_eq,
        ← ENNReal.ofReal_mul (by positivity)]
    have hRHS : Cvit * ENNReal.ofReal s ^ 2 = ENNReal.ofReal (18 * s ^ 2 * π) := by
      rw [show Cvit = (18 * NNReal.pi : ℝ≥0) from rfl, ENNReal.coe_mul,
        show ((18:ℝ≥0):ℝ≥0∞) = ENNReal.ofReal 18 by norm_num, hpi_eq,
        ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ s) 2,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 18),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 18 * π)]
      congr 1
      ring
    rw [hLHS, hRHS]

/-- The closed dyadic squares (at scale `N - k`, containing `x`, via `gridIdx`) tend to `x` along
`vitFam`'s filter as `k → ∞`. -/
theorem dyadicSquareClosed_tendsto_filterAt (N : ℤ) (x : ℂ) :
    Tendsto (fun k : ℕ => dyadicSquareClosed (N - k) (gridIdx (N - k) x).1 (gridIdx (N - k) x).2)
      atTop (vitFam.filterAt x) := by
  rw [vitFam.tendsto_filterAt_iff]
  constructor
  · refine Eventually.of_forall (fun k => ?_)
    exact dyadicSquareClosed_mem_setsAt
      (dyadicSquare_subset_closed _ _ _ (mem_dyadicSquare_gridIdx (N - (k:ℤ)) x))
  · intro ε hε
    have hpow0 : Tendsto (fun k : ℕ => (2:ℝ) ^ (N - (k:ℤ))) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => (2:ℝ) ^ (N - (k:ℤ))) atTop
          (𝓝 (0 : ℝ)) := by
        have heq : ∀ k : ℕ, (2:ℝ) ^ (N - (k:ℤ)) = (2:ℝ) ^ N * (2:ℝ) ^ (-(k:ℤ)) := by
          intro k; rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring_nf
        simp_rw [heq]
        have h2 : Tendsto (fun k : ℕ => (2:ℝ) ^ (-(k:ℤ))) atTop (𝓝 0) := by
          have heq2 : ∀ k : ℕ, (2:ℝ) ^ (-(k:ℤ)) = ((2:ℝ)⁻¹) ^ k := by
            intro k; rw [zpow_neg, zpow_natCast, inv_pow]
          simp_rw [heq2]
          exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa using h2.const_mul ((2:ℝ) ^ N)
      exact this
    have hev : ∀ᶠ k : ℕ in atTop, (2:ℝ) ^ (N - (k:ℤ)) * Real.sqrt 2 < ε := by
      have hcont : Tendsto (fun k : ℕ => (2:ℝ) ^ (N - (k:ℤ)) * Real.sqrt 2) atTop (𝓝 0) := by
        simpa using hpow0.mul_const (Real.sqrt 2)
      exact hcont.eventually_lt_const hε
    filter_upwards [hev] with k hk
    intro z hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    obtain ⟨hx1, hx2, hx3, hx4⟩ := dyadicSquare_subset_closed _ _ _ (mem_dyadicSquare_gridIdx (N - (k:ℤ)) x)
    exact le_of_lt (lt_of_le_of_lt (dist_le_of_dyadic_coords hx1 hx2 hx3 hx4 hz1 hz2 hz3 hz4) hk)

/-- The closed and half-open dyadic squares differ by a null set, so integrals over them agree,
for any integrable `g` (valued in any Banach space, so this covers both `f` itself and `‖f ·‖`). -/
theorem integral_dyadicSquareClosed_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℂ → E} (hg : Integrable g volume) (n i j : ℤ) :
    ∫ z in dyadicSquareClosed n i j, g z = ∫ z in dyadicSquare n i j, g z := by
  have hsub : dyadicSquare n i j ⊆ dyadicSquareClosed n i j := dyadicSquare_subset_closed n i j
  have hmeasclosed : MeasurableSet (dyadicSquareClosed n i j) :=
    (dyadicSquareClosed_isClosed n i j).measurableSet
  have hmeassquare : MeasurableSet (dyadicSquare n i j) := dyadicSquare_measurableSet n i j
  have hdiffmeas : MeasurableSet (dyadicSquareClosed n i j \ dyadicSquare n i j) :=
    hmeasclosed.diff hmeassquare
  have hdiff0 : volume (dyadicSquareClosed n i j \ dyadicSquare n i j) = 0 := by
    rw [measure_diff hsub hmeassquare.nullMeasurableSet (dyadicSquare_volume_ne_top n i j),
      dyadicSquareClosed_volume_eq]
    exact tsub_self _
  have hunion : dyadicSquareClosed n i j = dyadicSquare n i j ∪
      (dyadicSquareClosed n i j \ dyadicSquare n i j) := (Set.union_diff_cancel hsub).symm
  rw [hunion, setIntegral_union disjoint_sdiff_self_right hdiffmeas hg.integrableOn hg.integrableOn,
    setIntegral_measure_zero _ hdiff0, add_zero]

theorem czAvg_dyadicSquareClosed_eq {g : ℂ → ℂ} (hg : Integrable g volume) (n i j : ℤ) :
    czAvg g (dyadicSquareClosed n i j) = czAvg g (dyadicSquare n i j) := by
  unfold czAvg
  rw [dyadicSquareClosed_volume_eq, integral_dyadicSquareClosed_eq hg]

theorem avgAbs_dyadicSquareClosed_eq {g : ℂ → ℂ} (hg : Integrable g volume) (n i j : ℤ) :
    avgAbs g (dyadicSquareClosed n i j) = avgAbs g (dyadicSquare n i j) := by
  unfold avgAbs
  rw [dyadicSquareClosed_volume_eq, integral_dyadicSquareClosed_eq hg.norm]

theorem setAverage_eq_czAvg (g : ℂ → ℂ) (s : Set ℂ) : ⨍ z in s, g z ∂volume = czAvg g s := by
  rw [setAverage_eq]
  rfl

/-- The a.e. bound `‖g‖ ≤ 4·lam`: on selected squares via `selected_avg_le_four`, and off the
union via the Vitali-family Lebesgue differentiation theorem applied to the closed dyadic
squares, combined with `never_selected_avg_le`. -/
theorem czG_norm_le_ae (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) {N : ℤ}
    (hstart : ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam) :
    ∀ᵐ x ∂volume, ‖czG f lam N x‖ ≤ 4 * lam := by
  have hae := vitFam.ae_tendsto_average hf.locallyIntegrable
  filter_upwards [hae] with x hx
  by_cases hsel : ∃ k : ℕ, ∃ i j : ℤ, Selected f lam N k i j ∧ x ∈ dyadicSquare (N - (k:ℤ)) i j
  · obtain ⟨k, i, j, hselkij, hxmem⟩ := hsel
    unfold czG
    rw [czB_eq_of_mem hselkij hxmem, show f x - (f x - czAvg f (dyadicSquare (N-(k:ℤ)) i j)) =
      czAvg f (dyadicSquare (N-(k:ℤ)) i j) by ring]
    calc ‖czAvg f (dyadicSquare (N-(k:ℤ)) i j)‖ ≤ avgAbs f (dyadicSquare (N-(k:ℤ)) i j) :=
          norm_czAvg_le_avgAbs f _
      _ ≤ 4 * lam := selected_avg_le_four hf hstart hselkij
  · push_neg at hsel
    have hzero : czB f lam N x = 0 := czB_eq_zero_of_not_mem hsel
    unfold czG
    rw [hzero, sub_zero]
    have hns : ∀ k : ℕ, ¬ Selected f lam N k (gridIdx (N - (k:ℤ)) x).1 (gridIdx (N - (k:ℤ)) x).2 :=
      fun k hSel => hsel k _ _ hSel (mem_dyadicSquare_gridIdx (N - (k:ℤ)) x)
    have hcomp := hx.comp (dyadicSquareClosed_tendsto_filterAt N x)
    have hbdd : ∀ k : ℕ, ‖⨍ z in dyadicSquareClosed (N - (k:ℤ))
        (gridIdx (N - (k:ℤ)) x).1 (gridIdx (N - (k:ℤ)) x).2, f z ∂volume‖ ≤ lam := by
      intro k
      rw [setAverage_eq_czAvg,
        czAvg_dyadicSquareClosed_eq hf (N - (k:ℤ)) (gridIdx (N - (k:ℤ)) x).1
          (gridIdx (N - (k:ℤ)) x).2]
      calc ‖czAvg f (dyadicSquare (N - (k:ℤ)) (gridIdx (N - (k:ℤ)) x).1
          (gridIdx (N - (k:ℤ)) x).2)‖
          ≤ avgAbs f (dyadicSquare (N - (k:ℤ)) (gridIdx (N - (k:ℤ)) x).1
              (gridIdx (N - (k:ℤ)) x).2) := norm_czAvg_le_avgAbs f _
        _ ≤ lam := never_selected_avg_le hns k
    have hlam4 : lam ≤ 4 * lam := by linarith
    refine le_trans ?_ hlam4
    exact le_of_tendsto' (hcomp.norm) hbdd

theorem czG_integrable (f : ℂ → ℂ) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) {N : ℤ}
    (hstart : ∀ i j : ℤ, avgAbs f (dyadicSquare N i j) ≤ lam) :
    Integrable (czG f lam N) volume :=
  hf.sub (czB_integrable f hf hlam hstart)

/-- A Calderón–Zygmund decomposition of `f ∈ L¹(ℂ)` at height `lam`: `f = g + b`, `g` bounded
by (a fixed multiple of) `lam`, `b` supported on countably many pairwise disjoint measurable
pieces `Q i` on each of which it has mean zero, with the pieces' total measure controlled by
`‖f‖₁ / lam`.  Each `Q i` is engulfed by a ball `closedBall (c i) (r i)` with a doubling bound
(the far-region condition and the enlarged-ball measure bound needed downstream), and `b`'s `L¹`
norm is controlled by `f`'s.  (Internally built from dyadic squares, engulfed by balls since
squares themselves don't tile as balls.) -/
theorem exists_czDecomposition {f : ℂ → ℂ} (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (g b : ℂ → ℂ) (ι : Type) (_ : Countable ι) (Q : ι → Set ℂ) (c : ι → ℂ) (r : ι → ℝ),
      (∀ i, MeasurableSet (Q i)) ∧
      (∀ i, 0 < volume (Q i)) ∧
      Pairwise (Function.onFun Disjoint Q) ∧
      (∀ i, 0 < r i ∧ Q i ⊆ closedBall (c i) (r i) ∧
        volume (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (2 * π) * volume (Q i)) ∧
      (∀ z, f z = g z + b z) ∧
      Integrable g volume ∧ Integrable b volume ∧
      (∀ᵐ z ∂volume, ‖g z‖ ≤ 4 * lam) ∧
      (∫ z, ‖b z‖) ≤ 2 * ∫ z, ‖f z‖ ∧
      (∀ i, ∫ ζ in Q i, b ζ = 0) ∧
      ((Function.support b : Set ℂ) ⊆ ⋃ i, Q i) ∧
      (∑' i, volume (Q i)) ≤ ENNReal.ofReal ((4 / lam) * ∫ z, ‖f z‖) := by
  obtain ⟨N, hstart⟩ := exists_valid_start_scale f hf hlam
  choose c r hrpos hsub hdoubling using
    fun p : SelIdx f lam N => dyadicSquare_engulf (N - (p.1.1:ℤ)) p.1.2.1 p.1.2.2
  refine ⟨czG f lam N, czB f lam N, SelIdx f lam N, inferInstance, SelQ f lam N, c, r,
    selQ_measurableSet f lam N, fun p => dyadicSquare_volume_pos _ _ _,
    selQ_pairwise_disjoint f lam N, fun p => ⟨hrpos p, hsub p, hdoubling p⟩,
    fun z => by unfold czG; ring, czG_integrable f hf hlam hstart, czB_integrable f hf hlam hstart,
    czG_norm_le_ae f hf hlam hstart, czB_norm_integral_le f hf hlam hstart,
    czB_integral_selQ_eq_zero f hf lam N, czB_support_subset f lam N, ?_⟩
  have hfnn : (0:ℝ) ≤ ∫ z, ‖f z‖ := integral_nonneg (fun z => norm_nonneg _)
  calc (∑' p : SelIdx f lam N, volume (SelQ f lam N p))
      ≤ ENNReal.ofReal (∫ z, ‖f z‖) / ENNReal.ofReal lam := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity : ENNReal.ofReal lam ≠ 0))
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact selQ_measure_sum_le f hf hlam N
    _ = ENNReal.ofReal ((∫ z, ‖f z‖) / lam) := by rw [ENNReal.ofReal_div_of_pos hlam]
    _ ≤ ENNReal.ofReal ((4 / lam) * ∫ z, ‖f z‖) := by
        apply ENNReal.ofReal_le_ofReal
        have heq : (4:ℝ) / lam * ∫ z, ‖f z‖ = 4 * ((∫ z, ‖f z‖) / lam) := by ring
        rw [heq]
        have hY : (0:ℝ) ≤ (∫ z, ‖f z‖) / lam := div_nonneg hfnn hlam.le
        linarith

end LiZhongQC
