import LiZhongQC.Ch01.S04_ModulusExtremalLength
import LiZhongQC.Lemmas.GreenPolar
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The Dirichlet-principle form of the modulus

This file formalizes the one piece of the supplementary writeup `D:/lean/LZ2.txt` (a proof of the
classification of doubly connected domains, Theorem 2.1 of the book) that is both **new** relative
to the book's statement and **provable** with what Mathlib has: the identity
`mod(Ω) · D[u] = 2π` between the modulus of a doubly connected domain and the Dirichlet integral
`D[u] = ∬_Ω |∇u|²` of its harmonic measure `u` (the harmonic function that is `0` on the inner
boundary and `1` on the outer one), verified on the model annulus.

* `dirichletIntegral u D = ∫_D ‖∇u‖²`;
* `annulusHarmonicMeasure r₁ r₂ = ln(|z|/r₁)/ln(r₂/r₁)` — harmonic on `ℂ ∖ {0}`, `0` on `|z| = r₁`,
  `1` on `|z| = r₂`, with `|∇u| = 1/(|z| ln(r₂/r₁))`;
* `dirichletIntegral_annulusHarmonicMeasure`: `D[u] = 2π / ln(r₂/r₁)`;
* `annulus_dcModulus_mul_dirichletIntegral`: `mod · D[u] = 2π` on the annulus — the boxed identity
  of `LZ2.txt` in this project's normalization (the book's `mod = ln(r₂/r₁)`; the writeup's is
  `ln(1/r)/(2π)`, which makes its version read `mod = 1/D[u]`);
* `dcModulus_mul_dirichletIntegral`: the general identity for a bounded `B`, proved through the annulus
  uniformization `thm2_1_canonical_form_annulus` (the writeup's Step 7).

The uniqueness half of the writeup (its Step 6) is proved and axiom-clean in this project:
`thm2_1_canonical_unique_plane_disc`, `thm2_1_canonical_unique_plane_annulus`,
`thm2_1_canonical_unique_disc_annulus` (§2) and `annulus_conformallyEquivalent_iff` (§4).  So is
the existence half, `thm2_1_canonical_form` (§2, case (iii) `thm2_1_canonical_form_annulus`); the
writeup's Steps 2–5 are not needed.
-/

open Complex Set MeasureTheory Filter InnerProductSpace
open scoped Real Topology ENNReal

noncomputable section

namespace LiZhongQC

/-! ### The Dirichlet integral -/

/-- The Dirichlet integral `D[u] = ∬_D |∇u|²`.  `fderiv ℝ u` is the junk `0` where `u` is not
differentiable, so this is meaningful only for `u` differentiable on `D` — which the harmonic
functions it is applied to are. -/
def dirichletIntegral (u : ℂ → ℝ) (D : Set ℂ) : ℝ := ∫ z in D, ‖fderiv ℝ u z‖ ^ 2

/-! ### The harmonic measure of an annulus -/

/-- The harmonic measure of the annulus `{r₁ < |z| < r₂}`: `u(z) = ln(|z|/r₁) / ln(r₂/r₁)`.
(Written as `ln ‖z / r₁‖` so that harmonicity is `AnalyticAt.harmonicAt_log_norm` verbatim.) -/
def annulusHarmonicMeasure (r₁ r₂ : ℝ) (z : ℂ) : ℝ :=
  Real.log ‖z / (r₁ : ℂ)‖ / Real.log (r₂ / r₁)

theorem annulusHarmonicMeasure_eq {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (z : ℂ) :
    annulusHarmonicMeasure r₁ r₂ z = Real.log (‖z‖ / r₁) / Real.log (r₂ / r₁) := by
  simp [annulusHarmonicMeasure, Complex.norm_real, abs_of_pos h₁]

theorem log_ratio_pos {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) : 0 < Real.log (r₂ / r₁) :=
  Real.log_pos (by rw [lt_div_iff₀ h₁, one_mul]; exact h₂)

/-- `u = 0` on the inner circle. -/
theorem annulusHarmonicMeasure_inner {r₁ r₂ : ℝ} (h₁ : 0 < r₁) {z : ℂ} (hz : ‖z‖ = r₁) :
    annulusHarmonicMeasure r₁ r₂ z = 0 := by
  rw [annulusHarmonicMeasure_eq h₁, hz, div_self h₁.ne', Real.log_one, zero_div]

/-- `u = 1` on the outer circle. -/
theorem annulusHarmonicMeasure_outer {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {z : ℂ}
    (hz : ‖z‖ = r₂) : annulusHarmonicMeasure r₁ r₂ z = 1 := by
  rw [annulusHarmonicMeasure_eq h₁, hz]
  exact div_self (log_ratio_pos h₁ h₂).ne'

/-- `u` is harmonic on `ℂ ∖ {0}`, in particular on the annulus. -/
theorem harmonicOnNhd_annulusHarmonicMeasure {r₁ r₂ : ℝ} (h₁ : 0 < r₁) :
    HarmonicOnNhd (annulusHarmonicMeasure r₁ r₂) {0}ᶜ := by
  intro z hz
  have hz0 : z ≠ 0 := hz
  have hg : AnalyticAt ℂ (fun w : ℂ => w / (r₁ : ℂ)) z := by fun_prop
  have hne : (fun w : ℂ => w / (r₁ : ℂ)) z ≠ 0 :=
    div_ne_zero hz0 (by exact_mod_cast h₁.ne')
  have h := (hg.harmonicAt_log_norm hne).const_smul (c := (Real.log (r₂ / r₁))⁻¹)
  have heq : annulusHarmonicMeasure r₁ r₂
      = (Real.log (r₂ / r₁))⁻¹ • (fun w : ℂ => Real.log ‖w / (r₁ : ℂ)‖) := by
    funext w
    simp [annulusHarmonicMeasure, div_eq_inv_mul]
  rw [heq]
  exact h

/-! ### The gradient -/

/-- `∇ ln‖z‖ = z/|z|²` as a real Fréchet derivative: `⟪z, ·⟫ / ‖z‖²`. -/
theorem hasFDerivAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ => Real.log ‖w‖) ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
  have h2 : HasFDerivAt (fun w : ℂ => Real.log (‖w‖ ^ 2))
      ((‖z‖ ^ 2)⁻¹ • (2 : ℕ) • innerSL ℝ z) z := h1.log hpos.ne'
  have h3 := h2.const_mul (1 / 2 : ℝ)
  have heq : (fun w : ℂ => Real.log ‖w‖) = fun w : ℂ => (1 / 2 : ℝ) * Real.log (‖w‖ ^ 2) := by
    funext w
    rw [Real.log_pow]
    push_cast
    ring
  rw [heq]
  convert h3 using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- `|∇ ln‖z‖| = 1/|z|`. -/
theorem norm_fderiv_log_norm {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (fun w : ℂ => Real.log ‖w‖) z‖ = ‖z‖⁻¹ := by
  rw [(hasFDerivAt_log_norm hz).fderiv, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

/-- The gradient of the harmonic measure: `|∇u| = 1/(|z| ln(r₂/r₁))`. -/
theorem norm_fderiv_annulusHarmonicMeasure {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {z : ℂ}
    (hz : z ≠ 0) :
    ‖fderiv ℝ (annulusHarmonicMeasure r₁ r₂) z‖ = (Real.log (r₂ / r₁))⁻¹ * ‖z‖⁻¹ := by
  -- near `z`, `u = L⁻¹ (ln‖w‖ - ln r₁)`
  have hev : annulusHarmonicMeasure r₁ r₂ =ᶠ[𝓝 z]
      fun w : ℂ => (Real.log (r₂ / r₁))⁻¹ * (Real.log ‖w‖ - Real.log r₁) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    rw [annulusHarmonicMeasure_eq h₁, Real.log_div hw0 h₁.ne', div_eq_inv_mul]
  have hd : HasFDerivAt (fun w : ℂ => (Real.log (r₂ / r₁))⁻¹ * (Real.log ‖w‖ - Real.log r₁))
      ((Real.log (r₂ / r₁))⁻¹ • (‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z :=
    ((hasFDerivAt_log_norm hz).sub_const _).const_mul _
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hsq : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
  rw [hev.fderiv_eq, hd.fderiv, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (log_ratio_pos h₁ h₂)), abs_of_pos (inv_pos.mpr hsq)]
  field_simp

/-! ### Polar coordinates on the annulus (mirrors `polarCoord_target_inter_ball`) -/

theorem polarCoord_target_inter_annulus {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) :
    _root_.polarCoord.target ∩
        ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' annulus r₁ r₂)
      = Set.Ioo r₁ r₂ ×ˢ Set.Ioo (-π) π := by
  ext p
  simp only [show _root_.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π from rfl,
    Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, annulus, Set.mem_setOf_eq,
    Complex.norm_polarCoord_symm, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [abs_of_pos h1] at h3 h4
    exact ⟨⟨h3, h4⟩, h2⟩
  · rintro ⟨⟨h3, h4⟩, h2⟩
    have h1 : 0 < p.1 := lt_of_le_of_lt h₁ h3
    exact ⟨⟨h1, h2⟩, by rwa [abs_of_pos h1], by rwa [abs_of_pos h1]⟩

/-- **Polar coordinates on an annulus centred at `0`** (real-valued integrand). -/
theorem setIntegral_annulus_polar (G : ℂ → ℝ) {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) :
    ∫ w in annulus r₁ r₂, G w
      = ∫ p in Set.Ioo r₁ r₂ ×ˢ Set.Ioo (-π) π, p.1 * G (Complex.polarCoord.symm p) := by
  have hmeas : MeasurableSet (annulus r₁ r₂) := (isOpen_annulus r₁ r₂).measurableSet
  have hpolar := Complex.integral_comp_polarCoord_symm ((annulus r₁ r₂).indicator G)
  rw [MeasureTheory.integral_indicator hmeas] at hpolar
  rw [← hpolar]
  have hpt : ∀ p : ℝ × ℝ,
      p.1 • ((annulus r₁ r₂).indicator G) (Complex.polarCoord.symm p)
        = (Complex.polarCoord.symm ⁻¹' annulus r₁ r₂).indicator
            (fun q : ℝ × ℝ => q.1 * G (Complex.polarCoord.symm q)) p := by
    intro p
    by_cases h : Complex.polarCoord.symm p ∈ annulus r₁ r₂
    · have hp : p ∈ Complex.polarCoord.symm ⁻¹' annulus r₁ r₂ := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hp, smul_eq_mul]
    · have hp : p ∉ Complex.polarCoord.symm ⁻¹' annulus r₁ r₂ := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hp, smul_zero]
  have hc : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  simp only [hpt]
  rw [MeasureTheory.setIntegral_indicator (hmeas.preimage hc.measurable)]
  rw [polarCoord_target_inter_annulus h₁]

/-! ### The Dirichlet integral of the harmonic measure -/

/-- `∫_{r₁}^{r₂} dr/r = ln(r₂/r₁)` over the open interval. -/
theorem setIntegral_Ioo_inv {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    ∫ r in Set.Ioo r₁ r₂, r⁻¹ = Real.log (r₂ / r₁) := by
  rw [← intervalIntegral.integral_of_le h₂.le |>.trans (setIntegral_congr_set Ioo_ae_eq_Ioc).symm]
  exact integral_inv_of_pos h₁ (h₁.trans h₂)

/-- **The Dirichlet integral of the harmonic measure of the annulus**: `D[u] = 2π / ln(r₂/r₁)`.
(The writeup's sanity check, `D[u] = 2π/\ln(1/ρ)` on `A_ρ`.) -/
theorem dirichletIntegral_annulusHarmonicMeasure {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    dirichletIntegral (annulusHarmonicMeasure r₁ r₂) (annulus r₁ r₂)
      = 2 * π / Real.log (r₂ / r₁) := by
  set L := Real.log (r₂ / r₁) with hLdef
  have hL : 0 < L := log_ratio_pos h₁ h₂
  -- the integrand on the annulus is `1/(L² |z|²)`
  have hint : ∫ z in annulus r₁ r₂, ‖fderiv ℝ (annulusHarmonicMeasure r₁ r₂) z‖ ^ 2
      = ∫ z in annulus r₁ r₂, (L ^ 2 * ‖z‖ ^ 2)⁻¹ := by
    refine setIntegral_congr_fun (isOpen_annulus r₁ r₂).measurableSet fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have h1' : r₁ < ‖z‖ := hz.1
      rw [h, norm_zero] at h1'
      exact absurd h1' (not_lt.mpr h₁.le)
    rw [norm_fderiv_annulusHarmonicMeasure h₁ h₂ hz0, ← hLdef]
    have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    field_simp
  -- pass to polar coordinates: the integrand becomes `1/(L² r)`
  rw [dirichletIntegral, hint, setIntegral_annulus_polar _ h₁.le]
  have hpt : ∀ p ∈ Set.Ioo r₁ r₂ ×ˢ Set.Ioo (-π) π,
      p.1 * (L ^ 2 * ‖Complex.polarCoord.symm p‖ ^ 2)⁻¹ = (L ^ 2)⁻¹ * (p.1)⁻¹ := by
    rintro p ⟨hp1, -⟩
    have hpos : 0 < p.1 := h₁.trans hp1.1
    rw [Complex.norm_polarCoord_symm, abs_of_pos hpos]
    field_simp
  rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) hpt]
  -- Fubini on the rectangle
  have hintg : IntegrableOn (fun p : ℝ × ℝ => (L ^ 2)⁻¹ * (p.1)⁻¹)
      (Set.Ioo r₁ r₂ ×ˢ Set.Ioo (-π) π) := by
    refine (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
    refine continuousOn_const.mul (continuousOn_inv₀.comp continuousOn_fst fun p hp => ?_)
    exact (h₁.trans_le hp.1.1).ne'
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ hintg]
  simp only [MeasureTheory.setIntegral_const, smul_eq_mul]
  have hvol : (volume : Measure ℝ).real (Set.Ioo (-π) π) = 2 * π := by
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [hvol, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    setIntegral_Ioo_inv h₁ h₂, ← hLdef]
  field_simp

/-- **The Dirichlet-principle form of the modulus, on the annulus**: `mod(A) · D[u] = 2π`.
This is the boxed identity of `LZ2.txt` (`mod = 1/D[u]` in its normalization `mod = ln(1/r)/2π`)
in the book's normalization `mod = ln(r₂/r₁)`. -/
theorem annulus_dcModulus_mul_dirichletIntegral {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    (dcModulus (annulus r₁ r₂)).toReal
      * dirichletIntegral (annulusHarmonicMeasure r₁ r₂) (annulus r₁ r₂) = 2 * π := by
  rw [dcModulus_annulus h₁ h₂, ENNReal.toReal_ofReal (log_ratio_pos h₁ h₂).le,
    dirichletIntegral_annulusHarmonicMeasure h₁ h₂, mul_div_assoc',
    mul_div_cancel_left₀ _ (log_ratio_pos h₁ h₂).ne']

/-! ### The general identity -/

/-- A real harmonic function is locally constant at a local maximum (the maximum modulus principle
applied to `exp ∘ F`, where `F` is a local holomorphic function with real part `u`).  A copy of
`eventually_eq_of_harmonicAt_of_isLocalMax` from `LiZhongQC.ClusterSets`, which is not imported here. -/
theorem dmq_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {c : ℂ}
    (hu : ∀ᶠ z in 𝓝 c, HarmonicAt u z) (hc : IsLocalMax u c) :
    ∀ᶠ y in 𝓝 c, u y = u c := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hu : {z | HarmonicAt u z} ∈ 𝓝 c)
  obtain ⟨F, hF, hFu⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun y hy => hball hy)
  have hnorm : ∀ z ∈ Metric.ball c ρ, ‖Complex.exp (F z)‖ = Real.exp (u z) := by
    intro z hz
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hFu hz)
  have hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [Metric.ball_mem_nhds c hρ] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) c := by
    have hc' : ∀ᶠ z in 𝓝 c, u z ≤ u c := hc
    show ∀ᶠ z in 𝓝 c, (norm ∘ fun z => Complex.exp (F z)) z ≤
      (norm ∘ fun z => Complex.exp (F z)) c
    filter_upwards [Metric.ball_mem_nhds c hρ, hc'] with z hz hzc
    show ‖Complex.exp (F z)‖ ≤ ‖Complex.exp (F c)‖
    rw [hnorm z hz, hnorm c (Metric.mem_ball_self hρ)]
    exact Real.exp_le_exp.2 hzc
  filter_upwards [Complex.norm_eventually_eq_of_isLocalMax hd hmax, Metric.ball_mem_nhds c hρ]
    with y hy hyb
  rw [hnorm y hyb, hnorm c (Metric.mem_ball_self hρ)] at hy
  exact Real.exp_eq_exp.1 hy

/-- **Maximum principle** (a copy of `le_zero_of_harmonicOnNhd_of_tendsto_frontier` from
`LiZhongQC.ClusterSets`): a harmonic function on a bounded connected open set which tends to `0` at
every boundary point is nonpositive. -/
theorem dmq_le_zero_of_tendsto_frontier {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u U)
    (hbd : ∀ ζ ∈ frontier U, Tendsto u (𝓝[U] ζ) (𝓝 0)) :
    ∀ z ∈ U, u z ≤ 0 := by
  classical
  -- the extension of `u` by `0` to the closure
  set ũ : ℂ → ℝ := fun z => if z ∈ U then u z else 0 with hũ
  have hũU : ∀ z ∈ U, ũ z = u z := fun z hz => by simp [hũ, hz]
  have hũF : ∀ z ∈ frontier U, ũ z = 0 := by
    intro z hz
    rw [hUo.frontier_eq] at hz
    simp [hũ, hz.2]
  have hcont : ContinuousOn ũ (closure U) := by
    intro z hz
    by_cases hzU : z ∈ U
    · have h1 : ContinuousAt u z := (HarmonicAt.analyticAt (hu z hzU)).continuousAt
      have h2 : ũ =ᶠ[𝓝 z] u := by
        filter_upwards [hUo.mem_nhds hzU] with y hy
        exact hũU y hy
      exact (h1.congr_of_eventuallyEq h2).continuousWithinAt
    · have hzF : z ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨hz, hzU⟩
      have hsplit : closure U ⊆ U ∪ (closure U \ U) := fun y hy => by
        by_cases h : y ∈ U
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩
      show Tendsto ũ (𝓝[closure U] z) (𝓝 (ũ z))
      rw [hũF z hzF]
      refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsplit)
      rw [nhdsWithin_union]
      refine Tendsto.sup ?_ ?_
      · exact (hbd z hzF).congr' (eventually_nhdsWithin_of_forall fun y hy => (hũU y hy).symm)
      · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
        simp [hũ, hy.2]
  rcases U.eq_empty_or_nonempty with hU | hUne
  · intro z hz
    rw [hU] at hz
    exact absurd hz (notMem_empty z)
  have hcpt : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨c, hcU, hcmax⟩ := hcpt.exists_isMaxOn hUne.closure hcont
  have hcmax' : ∀ y ∈ closure U, ũ y ≤ ũ c := isMaxOn_iff.1 hcmax
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨z₀, hz₀, hz₀pos⟩ := hcon
  have hM : 0 < ũ c := by
    have := hcmax' z₀ (subset_closure hz₀)
    rw [hũU z₀ hz₀] at this
    exact lt_of_lt_of_le hz₀pos this
  -- the maximum is attained at an interior point
  have hcU' : c ∈ U := by
    by_contra h
    have hcF : c ∈ frontier U := by
      rw [hUo.frontier_eq]
      exact ⟨hcU, h⟩
    rw [hũF c hcF] at hM
    exact lt_irrefl _ hM
  -- the set where the maximum is attained is open
  have hSo : IsOpen {z ∈ U | u z = ũ c} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hloc : IsLocalMax u z := by
      show ∀ᶠ y in 𝓝 z, u y ≤ u z
      filter_upwards [hUo.mem_nhds hz.1] with y hy
      rw [hz.2, ← hũU y hy]
      exact hcmax' y (subset_closure hy)
    have hev := dmq_eventually_eq_of_isLocalMax
      (Filter.eventually_of_mem (hUo.mem_nhds hz.1) fun y hy => hu y hy) hloc
    filter_upwards [hev, hUo.mem_nhds hz.1] with y hy hyU
    exact ⟨hyU, by rw [hy, hz.2]⟩
  -- its complement in `U` is open too
  have hSc : IsOpen (U \ {z ∈ U | u z = ũ c}) := by
    have heq : U \ {z ∈ U | u z = ũ c} = U ∩ u ⁻¹' (Iio (ũ c)) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, not_and]
      constructor
      · rintro ⟨hz, h⟩
        refine ⟨hz, lt_of_le_of_ne ?_ (h hz)⟩
        rw [← hũU z hz]
        exact hcmax' z (subset_closure hz)
      · rintro ⟨hz, h⟩
        exact ⟨hz, fun _ h' => (ne_of_lt h) h'⟩
    rw [heq]
    exact (InnerProductSpace.HarmonicOnNhd.continuousOn hu).isOpen_inter_preimage hUo isOpen_Iio
  -- hence `u ≡ ũ c` on the connected set `U`
  have hall : U ⊆ {z ∈ U | u z = ũ c} := by
    refine IsPreconnected.subset_left_of_subset_union hSo hSc disjoint_sdiff_right ?_
      ⟨c, hcU', hcU', (hũU c hcU').symm⟩ hUc
    intro z hz
    by_cases h : z ∈ {z ∈ U | u z = ũ c}
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  -- but `u → 0` at a boundary point, which exists since `U` is bounded and nonempty
  have hfr : (frontier U).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · exact hUne.ne_empty h
    · rw [h] at hUb
      exact NormedSpace.unbounded_univ ℝ ℂ hUb
  obtain ⟨ζ, hζ⟩ := hfr
  have h1 : Tendsto u (𝓝[U] ζ) (𝓝 0) := hbd ζ hζ
  have h2 : Tendsto u (𝓝[U] ζ) (𝓝 (ũ c)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => ((hall hy).2).symm)
  have hne : NeBot (𝓝[U] ζ) := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hζ)
  have h3 := tendsto_nhds_unique' hne h1 h2
  rw [← h3] at hM
  exact lt_irrefl _ hM

/-- **Uniqueness for the Dirichlet problem** (a copy of `eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier`
from `LiZhongQC.ClusterSets`): a harmonic function on a bounded connected open set which tends to `0`
at every boundary point vanishes. -/
theorem dmq_eqOn_zero_of_tendsto_frontier {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u U)
    (hbd : ∀ ζ ∈ frontier U, Tendsto u (𝓝[U] ζ) (𝓝 0)) :
    ∀ z ∈ U, u z = 0 := by
  intro z hz
  have h1 := dmq_le_zero_of_tendsto_frontier hUo hUb hUc hu hbd z hz
  have h2 := dmq_le_zero_of_tendsto_frontier hUo hUb hUc hu.neg
    (fun ζ hζ => by
      have h := (hbd ζ hζ).neg
      rw [neg_zero] at h
      exact h) z hz
  simp only [Pi.neg_apply, neg_nonpos] at h2
  exact le_antisymm h1 h2

/-- A compact subset of the annulus `{r₁ < |w| < r₂}` keeps a distance `δ > 0` from both boundary
circles. -/
theorem dmq_exists_delta_of_isCompact {S : Set ℂ} {r₁ r₂ : ℝ} (hS : IsCompact S)
    (hSA : S ⊆ annulus r₁ r₂) : ∃ δ > 0, ∀ w ∈ S, r₁ + δ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂ - δ := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun w hw => ?_⟩
    rw [hSe] at hw
    exact absurd hw (notMem_empty w)
  have hc : Continuous fun w : ℂ => min (‖w‖ - r₁) (r₂ - ‖w‖) :=
    (continuous_norm.sub continuous_const).min (continuous_const.sub continuous_norm)
  obtain ⟨w₀, hw₀, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  have h₀ : w₀ ∈ annulus r₁ r₂ := hSA hw₀
  have h01 : r₁ < ‖w₀‖ := h₀.1
  have h02 : ‖w₀‖ < r₂ := h₀.2
  refine ⟨min (‖w₀‖ - r₁) (r₂ - ‖w₀‖), lt_min (by linarith) (by linarith), fun w hw => ?_⟩
  have h : min (‖w₀‖ - r₁) (r₂ - ‖w₀‖) ≤ min (‖w‖ - r₁) (r₂ - ‖w‖) := isMinOn_iff.1 hmin w hw
  have h1 := min_le_left (‖w‖ - r₁) (r₂ - ‖w‖)
  have h2 := min_le_right (‖w‖ - r₁) (r₂ - ‖w‖)
  constructor <;> linarith

/-- For `u` continuous on the compact `closure B` with values in `{0, 1}` on `frontier B`, the set
where `u` is `ε`-far from both `0` and `1` is a compact subset of `B`. -/
theorem dmq_isCompact_far {B : Set ℂ} (hBo : IsOpen B) (hBb : Bornology.IsBounded B) {u : ℂ → ℝ}
    (huc : ContinuousOn u (closure B)) (hfr : ∀ z ∈ frontier B, u z = 0 ∨ u z = 1) {ε : ℝ}
    (hε : 0 < ε) :
    IsCompact (closure B ∩ u ⁻¹' ({t : ℝ | ε ≤ |t|} ∩ {t : ℝ | ε ≤ |t - 1|})) ∧
      closure B ∩ u ⁻¹' ({t : ℝ | ε ≤ |t|} ∩ {t : ℝ | ε ≤ |t - 1|}) ⊆ B := by
  have hcl : IsClosed ({t : ℝ | ε ≤ |t|} ∩ {t : ℝ | ε ≤ |t - 1|}) :=
    (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))
  refine ⟨Metric.isCompact_of_isClosed_isBounded
    (huc.preimage_isClosed_of_isClosed isClosed_closure hcl) (hBb.closure.subset inter_subset_left), ?_⟩
  rintro z ⟨hz, h1, h2⟩
  by_contra hzB
  have hzF : z ∈ frontier B := by
    rw [hBo.frontier_eq]
    exact ⟨hz, hzB⟩
  have h1' : ε ≤ |u z| := h1
  have h2' : ε ≤ |u z - 1| := h2
  rcases hfr z hzF with h | h
  · rw [h, abs_zero] at h1'
    linarith
  · rw [h, sub_self, abs_zero] at h2'
    linarith

/-- Near both boundary circles of the annulus `φ(B)`, `u` is `ε`-close to `0` or to `1`: the points where
it is `ε`-far from both form a compact subset of `B`, whose `φ`-image avoids collars of the circles. -/
theorem dmq_near_zero_one {B : Set ℂ} (hBo : IsOpen B) (hBb : Bornology.IsBounded B) {u : ℂ → ℝ}
    (huc : ContinuousOn u (closure B)) (hfr : ∀ z ∈ frontier B, u z = 0 ∨ u z = 1)
    {φ : ℂ → ℂ} {r₁ r₂ : ℝ} (hφ : IsConformalOnto φ B (annulus r₁ r₂)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ B, (‖φ z‖ < r₁ + δ ∨ r₂ - δ < ‖φ z‖) → |u z| < ε ∨ |u z - 1| < ε := by
  obtain ⟨hKc, hKB⟩ := dmq_isCompact_far hBo hBb huc hfr hε
  have hKA : φ '' (closure B ∩ u ⁻¹' ({t : ℝ | ε ≤ |t|} ∩ {t : ℝ | ε ≤ |t - 1|}))
      ⊆ annulus r₁ r₂ := by
    rw [← hφ.2.2]
    exact image_mono hKB
  obtain ⟨δ, hδ, hδK⟩ := dmq_exists_delta_of_isCompact
    (hKc.image_of_continuousOn (hφ.1.continuousOn.mono hKB)) hKA
  refine ⟨δ, hδ, fun z hz hzφ => ?_⟩
  by_contra hcon
  rcases not_or.1 hcon with ⟨h1, h2⟩
  have hK := hδK (φ z) (mem_image_of_mem φ ⟨subset_closure hz, not_lt.1 h1, not_lt.1 h2⟩)
  rcases hzφ with h | h
  · linarith [hK.1]
  · linarith [hK.2]

/-- **The limit on a collar.**  If the images `f '' P δ` of a monotone family of collars are
preconnected and `f` is eventually `ε`-close to `{0, 1}` on them, then `f` tends to `0` or to `1`
along the collars. -/
theorem dmq_collar_limit {P : ℝ → Set ℂ} {f : ℂ → ℝ}
    (hmono : ∀ δ₁ δ₂, δ₁ ≤ δ₂ → P δ₁ ⊆ P δ₂) (hconn : ∀ δ > 0, IsPreconnected (f '' P δ))
    (hnear : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ P δ, |f z| < ε ∨ |f z - 1| < ε) :
    ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ ∀ ε > 0, ∃ δ > 0, ∀ z ∈ P δ, |f z - a| < ε := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := hnear (1 / 3) (by norm_num)
  have hsub : f '' P δ₀ ⊆ {t : ℝ | |t| < 1 / 3} ∪ {t : ℝ | |t - 1| < 1 / 3} := by
    rintro _ ⟨z, hz, rfl⟩
    exact h₀ z hz
  have hdisj : Disjoint {t : ℝ | |t| < 1 / 3} {t : ℝ | |t - 1| < 1 / 3} := by
    rw [Set.disjoint_left]
    intro t h1 h2
    have h1' : |t| < 1 / 3 := h1
    have h2' : |t - 1| < 1 / 3 := h2
    rw [abs_lt] at h1' h2'
    linarith [h1'.2, h2'.1]
  have ho1 : IsOpen {t : ℝ | |t| < 1 / 3} := isOpen_lt (by fun_prop) (by fun_prop)
  have ho2 : IsOpen {t : ℝ | |t - 1| < 1 / 3} := isOpen_lt (by fun_prop) (by fun_prop)
  have key : ∀ a : ℝ, (a = 0 ∨ a = 1) → (∀ z ∈ P δ₀, |f z - a| < 1 / 3) →
      ∀ ε > 0, ∃ δ > 0, ∀ z ∈ P δ, |f z - a| < ε := by
    intro a ha hza ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hnear (min ε (1 / 3)) (lt_min hε (by norm_num))
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun z hz => ?_⟩
    have hz₀ := hza z (hmono _ _ (min_le_left _ _) hz)
    have hz₁ := h₁ z (hmono _ _ (min_le_right _ _) hz)
    have hm1 := min_le_left ε (1 / 3)
    have hm2 := min_le_right ε (1 / 3)
    rcases ha with rfl | rfl
    · rw [sub_zero] at hz₀ ⊢
      rcases hz₁ with h | h
      · linarith
      · rw [abs_lt] at hz₀ h
        linarith [hz₀.2, h.1]
    · rcases hz₁ with h | h
      · rw [abs_lt] at hz₀ h
        linarith [hz₀.1, h.2]
      · linarith
  rcases (hconn δ₀ hδ₀).subset_or_subset ho1 ho2 hdisj hsub with h | h
  · refine ⟨0, Or.inl rfl, key 0 (Or.inl rfl) fun z hz => ?_⟩
    rw [sub_zero]
    exact h (mem_image_of_mem f hz)
  · exact ⟨1, Or.inr rfl, key 1 (Or.inr rfl) fun z hz => h (mem_image_of_mem f hz)⟩

/-- **The inner limit value**: `u` tends to `a ∈ {0, 1}` as `φ(z)` tends to the inner circle, because
the inner collars `ψ(r₁ < |w| < r₁ + δ)` are connected. -/
theorem dmq_inner_limit {B : Set ℂ} (hBo : IsOpen B) (hBb : Bornology.IsBounded B) {u : ℂ → ℝ}
    (huc : ContinuousOn u (closure B)) (hfr : ∀ z ∈ frontier B, u z = 0 ∨ u z = 1)
    {φ ψ : ℂ → ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (hφ : IsConformalOnto φ B (annulus r₁ r₂))
    (hψ : IsConformalOnto ψ (annulus r₁ r₂) B) (hφψ : ∀ w ∈ annulus r₁ r₂, φ (ψ w) = w)
    (hψφ : ∀ z ∈ B, ψ (φ z) = z) :
    ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ ∀ ε > 0, ∃ δ > 0, ∀ z ∈ B, ‖φ z‖ < r₁ + δ → |u z - a| < ε := by
  have hφA : ∀ z ∈ B, φ z ∈ annulus r₁ r₂ := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
  have hψB : ∀ w ∈ annulus r₁ r₂, ψ w ∈ B := fun w hw => hψ.2.2 ▸ mem_image_of_mem ψ hw
  have hconn : ∀ δ > 0, IsPreconnected (u '' {z ∈ B | ‖φ z‖ < r₁ + δ}) := by
    intro δ _
    have hsub : annulus r₁ (min r₂ (r₁ + δ)) ⊆ annulus r₁ r₂ :=
      fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 (min_le_left _ _)⟩
    have heq : {z ∈ B | ‖φ z‖ < r₁ + δ} = ψ '' annulus r₁ (min r₂ (r₁ + δ)) := by
      ext z
      constructor
      · rintro ⟨hz, hzδ⟩
        exact ⟨φ z, ⟨(hφA z hz).1, lt_min (hφA z hz).2 hzδ⟩, hψφ z hz⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨hψB w (hsub hw), ?_⟩
        rw [hφψ w (hsub hw)]
        exact lt_of_lt_of_le hw.2 (min_le_right _ _)
    rw [heq, ← image_comp]
    exact (isPreconnected_annulus h₁.le).image _
      ((huc.mono subset_closure).comp (hψ.1.continuousOn.mono hsub) fun w hw => hψB w (hsub hw))
  have hnear : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ {z ∈ B | ‖φ z‖ < r₁ + δ}, |u z| < ε ∨ |u z - 1| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := dmq_near_zero_one hBo hBb huc hfr hφ hε
    exact ⟨δ, hδ, fun z hz => h z hz.1 (Or.inl hz.2)⟩
  obtain ⟨a, ha01, ha⟩ := dmq_collar_limit (P := fun δ => {z ∈ B | ‖φ z‖ < r₁ + δ}) (f := u)
    (fun δ₁ δ₂ hδ z hz => ⟨hz.1, lt_of_lt_of_le hz.2 (by linarith)⟩) hconn hnear
  refine ⟨a, ha01, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := ha ε hε
  exact ⟨δ, hδ, fun z hz hzδ => h z ⟨hz, hzδ⟩⟩

/-- **The outer limit value**: `u` tends to `b ∈ {0, 1}` as `φ(z)` tends to the outer circle, because
the outer collars `ψ(r₂ - δ < |w| < r₂)` are connected. -/
theorem dmq_outer_limit {B : Set ℂ} (hBo : IsOpen B) (hBb : Bornology.IsBounded B) {u : ℂ → ℝ}
    (huc : ContinuousOn u (closure B)) (hfr : ∀ z ∈ frontier B, u z = 0 ∨ u z = 1)
    {φ ψ : ℂ → ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (hφ : IsConformalOnto φ B (annulus r₁ r₂))
    (hψ : IsConformalOnto ψ (annulus r₁ r₂) B) (hφψ : ∀ w ∈ annulus r₁ r₂, φ (ψ w) = w)
    (hψφ : ∀ z ∈ B, ψ (φ z) = z) :
    ∃ b : ℝ, (b = 0 ∨ b = 1) ∧ ∀ ε > 0, ∃ δ > 0, ∀ z ∈ B, r₂ - δ < ‖φ z‖ → |u z - b| < ε := by
  have hφA : ∀ z ∈ B, φ z ∈ annulus r₁ r₂ := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
  have hψB : ∀ w ∈ annulus r₁ r₂, ψ w ∈ B := fun w hw => hψ.2.2 ▸ mem_image_of_mem ψ hw
  have hconn : ∀ δ > 0, IsPreconnected (u '' {z ∈ B | r₂ - δ < ‖φ z‖}) := by
    intro δ _
    have hsub : annulus (max r₁ (r₂ - δ)) r₂ ⊆ annulus r₁ r₂ :=
      fun w hw => ⟨lt_of_le_of_lt (le_max_left _ _) hw.1, hw.2⟩
    have heq : {z ∈ B | r₂ - δ < ‖φ z‖} = ψ '' annulus (max r₁ (r₂ - δ)) r₂ := by
      ext z
      constructor
      · rintro ⟨hz, hzδ⟩
        exact ⟨φ z, ⟨max_lt (hφA z hz).1 hzδ, (hφA z hz).2⟩, hψφ z hz⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨hψB w (hsub hw), ?_⟩
        rw [hφψ w (hsub hw)]
        exact lt_of_le_of_lt (le_max_right _ _) hw.1
    rw [heq, ← image_comp]
    exact (isPreconnected_annulus (le_max_of_le_left h₁.le)).image _
      ((huc.mono subset_closure).comp (hψ.1.continuousOn.mono hsub) fun w hw => hψB w (hsub hw))
  have hnear : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ {z ∈ B | r₂ - δ < ‖φ z‖}, |u z| < ε ∨ |u z - 1| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := dmq_near_zero_one hBo hBb huc hfr hφ hε
    exact ⟨δ, hδ, fun z hz => h z hz.1 (Or.inr hz.2)⟩
  obtain ⟨b, hb01, hb⟩ := dmq_collar_limit (P := fun δ => {z ∈ B | r₂ - δ < ‖φ z‖}) (f := u)
    (fun δ₁ δ₂ hδ z hz => ⟨hz.1, lt_of_le_of_lt (by linarith) hz.2⟩) hconn hnear
  refine ⟨b, hb01, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hb ε hε
  exact ⟨δ, hδ, fun z hz hzδ => h z ⟨hz, hzδ⟩⟩

/-- The harmonic measure of the annulus tends to `0` at the inner circle and to `1` at the outer
one, uniformly: `0 < ln(|w|/r₁) ≤ |w|/r₁ - 1` and `0 < ln(r₂/|w|) ≤ r₂/|w| - 1`. -/
theorem dmq_annulusHarmonicMeasure_bdry {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ w ∈ annulus r₁ r₂, (‖w‖ < r₁ + δ → |annulusHarmonicMeasure r₁ r₂ w| < ε) ∧
      (r₂ - δ < ‖w‖ → |annulusHarmonicMeasure r₁ r₂ w - 1| < ε) := by
  have hL : 0 < Real.log (r₂ / r₁) := log_ratio_pos h₁ h₂
  refine ⟨ε * Real.log (r₂ / r₁) * r₁, by positivity, fun w hw => ⟨fun hw1 => ?_, fun hw2 => ?_⟩⟩
  · have hw0 : r₁ < ‖w‖ := hw.1
    have hx : 1 < ‖w‖ / r₁ := by
      rw [lt_div_iff₀ h₁, one_mul]
      exact hw0
    have hlog0 : 0 < Real.log (‖w‖ / r₁) := Real.log_pos hx
    have hlog1 : Real.log (‖w‖ / r₁) ≤ ‖w‖ / r₁ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hexp : (ε * Real.log (r₂ / r₁) + 1) * r₁ = r₁ + ε * Real.log (r₂ / r₁) * r₁ := by ring
    have hq : ‖w‖ / r₁ < ε * Real.log (r₂ / r₁) + 1 := by
      rw [div_lt_iff₀ h₁, hexp]
      exact hw1
    rw [annulusHarmonicMeasure_eq h₁, abs_of_pos (div_pos hlog0 hL), div_lt_iff₀ hL]
    linarith
  · have hw0 : r₁ < ‖w‖ := hw.1
    have hw3 : ‖w‖ < r₂ := hw.2
    have hwpos : 0 < ‖w‖ := h₁.trans hw0
    have hy : 1 < r₂ / ‖w‖ := by
      rw [lt_div_iff₀ hwpos, one_mul]
      exact hw3
    have hlog0 : 0 < Real.log (r₂ / ‖w‖) := Real.log_pos hy
    have hlog1 : Real.log (r₂ / ‖w‖) ≤ r₂ / ‖w‖ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hmul : ε * Real.log (r₂ / r₁) * r₁ < ε * Real.log (r₂ / r₁) * ‖w‖ :=
      mul_lt_mul_of_pos_left hw0 (by positivity)
    have hexp : (ε * Real.log (r₂ / r₁) + 1) * ‖w‖ = ε * Real.log (r₂ / r₁) * ‖w‖ + ‖w‖ := by ring
    have hq : r₂ / ‖w‖ < ε * Real.log (r₂ / r₁) + 1 := by
      rw [div_lt_iff₀ hwpos, hexp]
      linarith
    have hsplit : Real.log (‖w‖ / r₁) = Real.log (r₂ / r₁) - Real.log (r₂ / ‖w‖) := by
      rw [Real.log_div hwpos.ne' h₁.ne', Real.log_div (h₁.trans h₂).ne' hwpos.ne',
        Real.log_div (h₁.trans h₂).ne' h₁.ne']
      ring
    have heq : Real.log (‖w‖ / r₁) / Real.log (r₂ / r₁) - 1
        = -(Real.log (r₂ / ‖w‖) / Real.log (r₂ / r₁)) := by
      rw [hsplit, sub_div, div_self hL.ne']
      ring
    rw [annulusHarmonicMeasure_eq h₁, heq, abs_neg, abs_of_pos (div_pos hlog0 hL), div_lt_iff₀ hL]
    linarith

/-- `a + c · h ∘ φ` is harmonic on `B`, for `h` the harmonic measure of the annulus `φ(B)`:
`h ∘ φ = ln|φ/r₁| / ln(r₂/r₁)` with `φ` holomorphic and nonvanishing. -/
theorem dmq_harmonicOnNhd_comp {B : Set ℂ} (hBo : IsOpen B) {φ : ℂ → ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (hφ : IsConformalOnto φ B (annulus r₁ r₂)) (a c : ℝ) :
    HarmonicOnNhd (fun z => a + c * annulusHarmonicMeasure r₁ r₂ (φ z)) B := by
  intro z hz
  have hφz : φ z ∈ annulus r₁ r₂ := hφ.2.2 ▸ mem_image_of_mem φ hz
  have hφ0 : φ z ≠ 0 := by
    intro h
    have h' : r₁ < ‖φ z‖ := hφz.1
    rw [h, norm_zero] at h'
    linarith
  have hne : φ z / (r₁ : ℂ) ≠ 0 := div_ne_zero hφ0 (by exact_mod_cast h₁.ne')
  have hg : AnalyticAt ℂ (fun w => φ w / (r₁ : ℂ)) z :=
    (hφ.1.analyticAt (hBo.mem_nhds hz)).div_const
  have h := (harmonicAt_const a).add
    ((hg.harmonicAt_log_norm hne).const_smul (c := c * (Real.log (r₂ / r₁))⁻¹))
  have heq : (fun z => a + c * annulusHarmonicMeasure r₁ r₂ (φ z))
      = (fun _ : ℂ => a) + (c * (Real.log (r₂ / r₁))⁻¹) • fun w : ℂ => Real.log ‖φ w / (r₁ : ℂ)‖ := by
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, annulusHarmonicMeasure]
    ring
  rw [heq]
  exact h

/-- The harmonic measure of the annulus is differentiable on the annulus. -/
theorem dmq_differentiableAt {r₁ r₂ : ℝ} (h₁ : 0 < r₁) {w : ℂ} (hw : w ∈ annulus r₁ r₂) :
    DifferentiableAt ℝ (annulusHarmonicMeasure r₁ r₂) w := by
  have hw0 : w ≠ 0 := by
    intro h
    have h' : r₁ < ‖w‖ := hw.1
    rw [h, norm_zero] at h'
    linarith
  exact (harmonicOnNhd_annulusHarmonicMeasure (r₂ := r₂) h₁ w hw0).1.differentiableAt two_ne_zero

/-- **The boundary behaviour of `u - (a + (b - a) h ∘ φ)`**: it tends to `0` at every boundary point
of `B`, since off the compact set `ψ(r₁ + δ ≤ |w| ≤ r₂ - δ)` both `u` and `a + (b - a) h ∘ φ` are
close to `a` (near the inner circle) or to `b` (near the outer one). -/
theorem dmq_tendsto_frontier {B : Set ℂ} (hBo : IsOpen B) {φ ψ : ℂ → ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : r₁ < r₂) (hφ : IsConformalOnto φ B (annulus r₁ r₂))
    (hψ : IsConformalOnto ψ (annulus r₁ r₂) B) (hψφ : ∀ z ∈ B, ψ (φ z) = z) {u : ℂ → ℝ} {a b : ℝ}
    (ha01 : a = 0 ∨ a = 1) (hb01 : b = 0 ∨ b = 1)
    (ha : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ B, ‖φ z‖ < r₁ + δ → |u z - a| < ε)
    (hb : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ B, r₂ - δ < ‖φ z‖ → |u z - b| < ε) {ζ : ℂ}
    (hζ : ζ ∈ frontier B) :
    Tendsto (u - fun z => a + (b - a) * annulusHarmonicMeasure r₁ r₂ (φ z)) (𝓝[B] ζ) (𝓝 0) := by
  have hφA : ∀ z ∈ B, φ z ∈ annulus r₁ r₂ := fun z hz => hφ.2.2 ▸ mem_image_of_mem φ hz
  have hψB : ∀ w ∈ annulus r₁ r₂, ψ w ∈ B := fun w hw => hψ.2.2 ▸ mem_image_of_mem ψ hw
  have hζB : ζ ∉ B := by
    rw [hBo.frontier_eq] at hζ
    exact hζ.2
  have hba : |b - a| ≤ 1 := by
    rcases ha01 with rfl | rfl <;> rcases hb01 with rfl | rfl <;> norm_num
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δa, hδa, hua⟩ := ha (ε / 2) (half_pos hε)
  obtain ⟨δb, hδb, hub⟩ := hb (ε / 2) (half_pos hε)
  obtain ⟨δh, hδh, hh⟩ := dmq_annulusHarmonicMeasure_bdry h₁ h₂ (half_pos hε)
  obtain ⟨δ, hδ, hδa', hδb', hδh'⟩ : ∃ δ > 0, δ ≤ δa ∧ δ ≤ δb ∧ δ ≤ δh :=
    ⟨min (min δa δb) δh, lt_min (lt_min hδa hδb) hδh,
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  have hSA : {w : ℂ | r₁ + δ ≤ ‖w‖} ∩ {w : ℂ | ‖w‖ ≤ r₂ - δ} ⊆ annulus r₁ r₂ := by
    intro w hw
    have hw1 : r₁ + δ ≤ ‖w‖ := hw.1
    have hw2 : ‖w‖ ≤ r₂ - δ := hw.2
    exact ⟨by linarith, by linarith⟩
  have hSc : IsCompact ({w : ℂ | r₁ + δ ≤ ‖w‖} ∩ {w : ℂ | ‖w‖ ≤ r₂ - δ}) := by
    refine Metric.isCompact_of_isClosed_isBounded
      (((isClosed_Ici (a := r₁ + δ)).preimage continuous_norm).inter
        ((isClosed_Iic (a := r₂ - δ)).preimage continuous_norm)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r₂)).subset fun w hw => ?_
    have hw2 : ‖w‖ ≤ r₂ - δ := hw.2
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hKc : IsCompact (ψ '' ({w : ℂ | r₁ + δ ≤ ‖w‖} ∩ {w : ℂ | ‖w‖ ≤ r₂ - δ})) :=
    hSc.image_of_continuousOn (hψ.1.continuousOn.mono hSA)
  have hζK : ζ ∉ ψ '' ({w : ℂ | r₁ + δ ≤ ‖w‖} ∩ {w : ℂ | ‖w‖ ≤ r₂ - δ}) := by
    rintro ⟨w, hw, hwζ⟩
    exact hζB (hwζ ▸ hψB w (hSA hw))
  filter_upwards [inter_mem_nhdsWithin B (hKc.isClosed.isOpen_compl.mem_nhds hζK)] with z hz
  obtain ⟨hzB, hzK⟩ := hz
  have hφz := hφA z hzB
  show dist (u z - (a + (b - a) * annulusHarmonicMeasure r₁ r₂ (φ z))) 0 < ε
  rw [Real.dist_eq, sub_zero]
  have hcase : ‖φ z‖ < r₁ + δ ∨ r₂ - δ < ‖φ z‖ := by
    by_contra hc
    rcases not_or.1 hc with ⟨hc1, hc2⟩
    exact hzK ⟨φ z, ⟨not_lt.1 hc1, not_lt.1 hc2⟩, hψφ z hzB⟩
  rcases hcase with hc | hc
  · have h1 := hua z hzB (by linarith)
    have h2 := (hh (φ z) hφz).1 (by linarith)
    have h3 : |(b - a) * annulusHarmonicMeasure r₁ r₂ (φ z)| ≤ ε / 2 := by
      rw [abs_mul]
      calc |b - a| * |annulusHarmonicMeasure r₁ r₂ (φ z)| ≤ 1 * (ε / 2) :=
            mul_le_mul hba h2.le (abs_nonneg _) zero_le_one
        _ = ε / 2 := one_mul _
    rw [abs_lt] at h1 ⊢
    rw [abs_le] at h3
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  · have h1 := hub z hzB (by linarith)
    have h2 := (hh (φ z) hφz).2 (by linarith)
    have h3 : |(b - a) * (annulusHarmonicMeasure r₁ r₂ (φ z) - 1)| ≤ ε / 2 := by
      rw [abs_mul]
      calc |b - a| * |annulusHarmonicMeasure r₁ r₂ (φ z) - 1| ≤ 1 * (ε / 2) :=
            mul_le_mul hba h2.le (abs_nonneg _) zero_le_one
        _ = ε / 2 := one_mul _
    rw [abs_lt] at h1 ⊢
    rw [abs_le] at h3
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

/-- Every component of `ℂ̄ ∖ B` that contains a finite point meets `frontier B` (else its finite part
would be a nonempty clopen subset of `ℂ` missing `B`). -/
theorem dmq_exists_frontier_mem_component {B : Set ℂ} (hBo : IsOpen B) (hBne : B.Nonempty) {x : ℂ}
    (hx : (x : ExtPlane) ∈ (toExt B)ᶜ) :
    ∃ z ∈ frontier B, (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane) := by
  by_contra hcon
  have hcon' : ∀ z ∈ frontier B, (z : ExtPlane) ∉ connectedComponentIn (toExt B)ᶜ (x : ExtPlane) :=
    fun z hz hzE => hcon ⟨z, hz, hzE⟩
  have hCB : ∀ z : ℂ, (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane) → z ∉ B :=
    fun z hz => coe_mem_compl_toExt_iff.1 (connectedComponentIn_subset _ _ hz)
  have hCc : IsClosed {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane)} :=
    (isClosed_connectedComponentIn_compl_toExt hBo _).preimage OnePoint.continuous_coe
  have hCo : IsOpen {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane)} := by
    rw [Metric.isOpen_iff]
    intro z hz
    have hz' : (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane) := hz
    have hzcl : z ∉ closure B := by
      intro hcl
      refine hcon' z ?_ hz'
      rw [hBo.frontier_eq]
      exact ⟨hcl, hCB z hz'⟩
    obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hzcl
    refine ⟨r, hr, fun y hy => ?_⟩
    have hpre : IsPreconnected (((↑) : ℂ → ExtPlane) '' Metric.ball z r) :=
      (convex_ball z r).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    have hsub : ((↑) : ℂ → ExtPlane) '' Metric.ball z r ⊆ (toExt B)ᶜ := by
      rintro _ ⟨y', hy', rfl⟩
      exact coe_mem_compl_toExt_iff.2 fun hyB => hrB hy' (subset_closure hyB)
    have h := hpre.subset_connectedComponentIn ⟨z, Metric.mem_ball_self hr, rfl⟩ hsub
    rw [← connectedComponentIn_eq hz'] at h
    exact h ⟨y, hy, rfl⟩
  have huniv := IsClopen.eq_univ ⟨hCc, hCo⟩ ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨y, hy⟩ := hBne
  have hy' : y ∈ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ (x : ExtPlane)} := by
    rw [huniv]
    exact mem_univ y
  exact hCB y hy' hy

/-- `frontier B` meets both the component of `∞` in `ℂ̄ ∖ B` and the other component (which exists
since `B` is doubly connected); the component of `∞` has a finite point since it is nondegenerate. -/
theorem dmq_exists_frontier_inner_outer {B : Set ℂ} (hB : IsDoublyConnected B)
    (hnd : ∀ p ∈ (toExt B)ᶜ, (connectedComponentIn (toExt B)ᶜ p).Nontrivial) :
    (∃ z ∈ frontier B, (z : ExtPlane) ∉ connectedComponentIn (toExt B)ᶜ extInf) ∧
      ∃ z ∈ frontier B, (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf := by
  have hBne : B.Nonempty := hB.2.1.nonempty
  constructor
  · obtain ⟨p, hp, hne, -⟩ := exists_compl_eq_union_components hB
    have hp' : p ≠ extInf := fun h => hne (by rw [h])
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hp'
    obtain ⟨z, hz, hzE⟩ := dmq_exists_frontier_mem_component hB.1 hBne hp
    refine ⟨z, hz, fun hz' => hne ?_⟩
    rw [connectedComponentIn_eq hzE, connectedComponentIn_eq hz']
  · obtain ⟨q, hq, hqne⟩ := (hnd extInf (extInf_mem_compl_toExt B)).exists_ne extInf
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hqne
    obtain ⟨z, hz, hzE⟩ :=
      dmq_exists_frontier_mem_component hB.1 hBne (connectedComponentIn_subset _ _ hq)
    refine ⟨z, hz, ?_⟩
    rw [connectedComponentIn_eq hq]
    exact hzE

/-- `‖L ∘ M‖ = ‖L‖ ‖c‖` when `M` is the multiplication by `c` (for a real-linear functional `L` on
`ℂ`). -/
theorem dmq_norm_comp_mul (L : ℂ →L[ℝ] ℝ) {M : ℂ →L[ℝ] ℂ} {c : ℂ} (hM : ∀ x, M x = x * c) :
    ‖L.comp M‖ = ‖L‖ * ‖c‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [ContinuousLinearMap.comp_apply, hM]
    calc ‖L (x * c)‖ ≤ ‖L‖ * ‖x * c‖ := L.le_opNorm _
      _ = ‖L‖ * ‖c‖ * ‖x‖ := by rw [norm_mul]; ring
  · rcases eq_or_ne c 0 with hc | hc
    · rw [hc, norm_zero, mul_zero]
      exact norm_nonneg _
    · have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
      rw [← le_div_iff₀ hcn]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      have hy : M (y / c) = y := by rw [hM, div_mul_cancel₀ y hc]
      calc ‖L y‖ = ‖(L.comp M) (y / c)‖ := by rw [ContinuousLinearMap.comp_apply, hy]
        _ ≤ ‖L.comp M‖ * ‖y / c‖ := (L.comp M).le_opNorm _
        _ = ‖L.comp M‖ / ‖c‖ * ‖y‖ := by rw [norm_div]; ring

/-- **Conformal invariance of the Dirichlet integral**: if `u = H ∘ φ` on `B` for a conformal map `φ`
of `B` onto `V` and `H` differentiable on `V`, then `D_B[u] = D_V[H]`
(`|∇u|² = |∇H ∘ φ|² |φ'|²` and the change of variables `w = φ(z)`). -/
theorem dmq_dirichletIntegral_eq {B V : Set ℂ} (hBo : IsOpen B) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ B V) {u H : ℂ → ℝ} (huH : ∀ z ∈ B, u z = H (φ z))
    (hH : ∀ w ∈ V, DifferentiableAt ℝ H w) :
    dirichletIntegral u B = dirichletIntegral H V := by
  have hφd : ∀ z ∈ B, HasFDerivAt φ
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ z)).restrictScalars ℝ) z := fun z hz =>
    (hφ.1.differentiableAt (hBo.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  unfold dirichletIntegral
  rw [← hφ.2.2, integral_image_eq_integral_abs_det_fderiv_smul volume hBo.measurableSet
    (fun z hz => (hφd z hz).hasFDerivWithinAt) hφ.2.1 (fun w => ‖fderiv ℝ H w‖ ^ 2)]
  refine setIntegral_congr_fun hBo.measurableSet fun z hz => ?_
  have hφz : φ z ∈ V := hφ.2.2 ▸ mem_image_of_mem φ hz
  have hcomp := (hH (φ z) hφz).hasFDerivAt.comp z (hφd z hz)
  have hev : u =ᶠ[𝓝 z] H ∘ φ := by
    filter_upwards [hBo.mem_nhds hz] with y hy
    exact huH y hy
  have hnorm : ‖(fderiv ℝ H (φ z)).comp
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ z)).restrictScalars ℝ)‖
      = ‖fderiv ℝ H (φ z)‖ * ‖deriv φ z‖ := dmq_norm_comp_mul _ fun x => by simp
  show ‖fderiv ℝ u z‖ ^ 2 = |((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ z)).restrictScalars ℝ).det|
    • ‖fderiv ℝ H (φ z)‖ ^ 2
  rw [hev.fderiv_eq, hcomp.fderiv, hnorm, det_restrictScalars_toSpanSingleton,
    abs_of_nonneg (sq_nonneg _), smul_eq_mul]
  ring

/-- The Dirichlet integral of `a + c h` equals that of `h` when `|c| = 1`, for `h` the harmonic
measure of the annulus. -/
theorem dmq_dirichletIntegral_affine {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (a c : ℝ) (hc : |c| = 1) :
    dirichletIntegral (fun w => a + c * annulusHarmonicMeasure r₁ r₂ w) (annulus r₁ r₂)
      = dirichletIntegral (annulusHarmonicMeasure r₁ r₂) (annulus r₁ r₂) := by
  unfold dirichletIntegral
  refine setIntegral_congr_fun (isOpen_annulus r₁ r₂).measurableSet fun w hw => ?_
  rw [fderiv_const_add, fderiv_const_mul (dmq_differentiableAt h₁ hw), norm_smul,
    Real.norm_eq_abs, hc, one_mul]

/-- **The Dirichlet-principle form of the modulus** (from `LZ2.txt`, not the book): for a doubly
connected domain `B ⊆ ℂ` both of whose complementary components in `ℂ̂` are nondegenerate, and a
harmonic measure `u` — harmonic on `B`, continuous on `closure B`, `1` on the outer boundary (the
boundary points lying in the component of `∞`) and `0` on the inner one — `mod(B) · D[u] = 2π`.
The model case is `annulus_dcModulus_mul_dirichletIntegral`.

Proof: a conformal map `φ` of `B` onto an annulus (`thm2_1_canonical_form_annulus`) carries `u` to
the harmonic measure `h` of the annulus or to `1 - h` (the maximum principle, after reading off the
boundary values of `u` on the connected collars of the two circles), and both the modulus and the
Dirichlet integral are conformally invariant.

**Correction (2026-09-27):** the hypothesis `hBb : Bornology.IsBounded B` was added, since without it
the identity is FALSE for unbounded `B`: for `B = ℍ ∖ closedBall (c i) ρ` (`c > ρ > 0`) the true
harmonic measure `u₀` plus the Poisson kernel of the boundary point `∞` satisfies every other
hypothesis but has infinite Dirichlet integral, so the left side is the junk value `0`. -/
theorem dcModulus_mul_dirichletIntegral {B : Set ℂ} (hB : IsDoublyConnected B) (hBb : Bornology.IsBounded B)
    (hnd : ∀ p ∈ (toExt B)ᶜ, (connectedComponentIn (toExt B)ᶜ p).Nontrivial)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u B) (huc : ContinuousOn u (closure B))
    (hinner : ∀ z ∈ frontier B,
      (z : ExtPlane) ∉ connectedComponentIn (toExt B)ᶜ extInf → u z = 0)
    (houter : ∀ z ∈ frontier B,
      (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf → u z = 1) :
    (dcModulus B).toReal * dirichletIntegral u B = 2 * π := by
  have hBo : IsOpen B := hB.1
  -- a conformal map `φ` of `B` onto an annulus, and its inverse `ψ`
  obtain ⟨r₁, r₂, h₁, h₂, φ, hφ⟩ :=
    thm2_1_canonical_form_annulus hB fun x hx => (hnd x hx).ne_singleton
  obtain ⟨ψ, hψ, hφψ, hψφ⟩ : ∃ ψ : ℂ → ℂ, IsConformalOnto ψ (annulus r₁ r₂) B ∧
      (∀ w ∈ annulus r₁ r₂, φ (ψ w) = w) ∧ ∀ z ∈ B, ψ (φ z) = z := by
    refine ⟨Function.invFunOn φ B, hφ.symm hBo, fun w hw => ?_,
      fun z hz => hφ.2.1.leftInvOn_invFunOn hz⟩
    rw [← hφ.2.2] at hw
    exact Function.invFunOn_eq hw
  -- the boundary values of `u` are `0` and `1`
  have hfr : ∀ z ∈ frontier B, u z = 0 ∨ u z = 1 := by
    intro z hz
    by_cases h : (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf
    · exact Or.inr (houter z hz h)
    · exact Or.inl (hinner z hz h)
  -- the limits `a` and `b` of `u` at the inner and the outer circle
  obtain ⟨a, ha01, ha⟩ := dmq_inner_limit hBo hBb huc hfr h₁ hφ hψ hφψ hψφ
  obtain ⟨b, hb01, hb⟩ := dmq_outer_limit hBo hBb huc hfr h₁ hφ hψ hφψ hψφ
  -- `u = a + (b - a) h ∘ φ` by the maximum principle
  have hzero := dmq_eqOn_zero_of_tendsto_frontier hBo hBb hB.2.1.isPreconnected
    (hu.sub (dmq_harmonicOnNhd_comp hBo h₁ hφ a (b - a)))
    fun ζ hζ => dmq_tendsto_frontier hBo h₁ h₂ hφ hψ hψφ ha01 hb01 ha hb hζ
  have huG : ∀ z ∈ B, u z = a + (b - a) * annulusHarmonicMeasure r₁ r₂ (φ z) := by
    intro z hz
    have h := hzero z hz
    simp only [Pi.sub_apply] at h
    linarith
  -- `a ≠ b`, since `u` takes both values `0` and `1` on `frontier B`
  have hab : a ≠ b := by
    intro hab
    have hconst : EqOn u (fun _ => a) (closure B) := by
      refine EqOn.of_subset_closure (fun z hz => ?_) huc continuousOn_const subset_closure subset_rfl
      show u z = a
      rw [huG z hz, hab, sub_self, zero_mul, add_zero]
    obtain ⟨⟨z₀, hz₀, hz₀E⟩, z₁, hz₁, hz₁E⟩ := dmq_exists_frontier_inner_outer hB hnd
    have e₀ : a = 0 := (hconst (frontier_subset_closure hz₀)).symm.trans (hinner z₀ hz₀ hz₀E)
    have e₁ : a = 1 := (hconst (frontier_subset_closure hz₁)).symm.trans (houter z₁ hz₁ hz₁E)
    exact zero_ne_one (e₀.symm.trans e₁)
  have hba : |b - a| = 1 := by
    rcases ha01 with rfl | rfl <;> rcases hb01 with rfl | rfl
    all_goals first | exact absurd rfl hab | norm_num
  -- the modulus and the Dirichlet integral are conformal invariants
  have hdiff : ∀ w ∈ annulus r₁ r₂,
      DifferentiableAt ℝ (fun w => a + (b - a) * annulusHarmonicMeasure r₁ r₂ w) w :=
    fun w hw => ((dmq_differentiableAt h₁ hw).const_mul (b - a)).const_add a
  rw [thm2_2_dcModulus_conformal_invariant hB ⟨φ, hφ⟩,
    dmq_dirichletIntegral_eq hBo hφ (H := fun w => a + (b - a) * annulusHarmonicMeasure r₁ r₂ w)
      huG hdiff, dmq_dirichletIntegral_affine h₁ a (b - a) hba]
  exact annulus_dcModulus_mul_dirichletIntegral h₁ h₂

end LiZhongQC
