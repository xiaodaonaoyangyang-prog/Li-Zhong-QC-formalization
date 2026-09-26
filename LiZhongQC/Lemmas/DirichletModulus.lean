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
* `dcModulus_mul_dirichletIntegral`: the general identity, **stated only**.

The uniqueness half of the writeup (its Step 6) is already proved and axiom-clean in this project:
`thm2_1_canonical_unique_plane_disc`, `thm2_1_canonical_unique_plane_annulus`,
`thm2_1_canonical_unique_disc_annulus` (§2) and `annulus_conformallyEquivalent_iff` (§4).  The
existence half (`thm2_1_canonical_form`, the writeup's Steps 2–5, or its Step 7) is out of reach;
see the docstring of `dcModulus_mul_dirichletIntegral` for exactly which ingredients are missing.
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

/-! ### The general identity (statement only) -/

/-- **The Dirichlet-principle form of the modulus** (from `LZ2.txt`, not the book): for a doubly
connected domain `B ⊆ ℂ` both of whose complementary components in `ℂ̂` are nondegenerate, and a
harmonic measure `u` — harmonic on `B`, continuous on `closure B`, `1` on the outer boundary (the
boundary points lying in the component of `∞`) and `0` on the inner one — `mod(B) · D[u] = 2π`.
The model case is `annulus_dcModulus_mul_dirichletIntegral`.

Not proved (kept as `sorry`): the writeup's argument (its Steps 3–5) needs, in this order, the
Perron solution of the Dirichlet problem with boundary regularity (to *produce* `u` — here `u` is
instead taken as a hypothesis, which sidesteps that), Green's identity on the level-set domains
`{s < u < t}` — Mathlib's divergence theorem is on rectangles and this project's on discs — a
single-valued harmonic conjugate up to a period on a non-simply-connected domain, and the
argument principle to see that the resulting map onto an annulus has degree one.  Mathlib has none
of the last three; the argument principle is the same winding-number gap that blocks §4.6 and
Theorem 1.1.  The alternative route through uniformization (the writeup's Step 7) needs the
uniformization theorem, also absent. -/
theorem dcModulus_mul_dirichletIntegral {B : Set ℂ} (hB : IsDoublyConnected B)
    (hnd : ∀ p ∈ (toExt B)ᶜ, (connectedComponentIn (toExt B)ᶜ p).Nontrivial)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u B) (huc : ContinuousOn u (closure B))
    (hinner : ∀ z ∈ frontier B,
      (z : ExtPlane) ∉ connectedComponentIn (toExt B)ᶜ extInf → u z = 0)
    (houter : ∀ z ∈ frontier B,
      (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf → u z = 1) :
    (dcModulus B).toReal * dirichletIntegral u B = 2 * π := by
  sorry

end LiZhongQC
