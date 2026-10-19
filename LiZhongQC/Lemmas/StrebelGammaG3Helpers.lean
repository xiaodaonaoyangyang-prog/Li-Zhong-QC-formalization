import LiZhongQC.Ch11.S36_Hamilton

/-!
# Helpers for `strebel_hamilton_sufficient` (R83 S36, piece G3, 下属1)

The Γ/F copies of S35 `lemma35_4`–`lemma35_6` (limits along a Hamilton sequence of unit `φₙ ∈ A(Γ, F)`
with `∬_F κφₙ → k`) and the glue used to deduce extremality from a Hamilton sequence and the Γ main
inequality `str_gamma_main_inequality` (G2). The deduction itself (`strebel_hamilton_sufficient`) is assembled
once G2 is registered.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- G3 glue: an element of `BeltramiH` is a.e. strongly measurable on every set. -/
theorem s36g_meas (μ : BeltramiH) (F : Set ℂ) : AEStronglyMeasurable μ.1 (volume.restrict F) := by
  obtain ⟨⟨c, -, -, hc⟩, -⟩ := μ.2
  have h := hc.1
  rw [Measure.restrict_univ] at h
  exact h.restrict

/-- G3 glue: without unit elements of `A(Γ, F)` the Hamilton norm is the empty supremum `0`. -/
theorem s36g_hamiltonNorm_eq_zero {F : Set ℂ} {κ : ℂ → ℂ}
    (hA : ¬ ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1) : hamiltonNorm Γ F κ = 0 := by
  unfold hamiltonNorm
  have h0 : ∀ φ : ℂ → ℂ,
      (⨆ (_ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1), ‖beltramiPairing F κ φ‖) = 0 := by
    intro φ
    have : IsEmpty (φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1) :=
      ⟨fun hφ => hA ⟨φ, hφ.1, hφ.2⟩⟩
    exact Real.iSup_of_isEmpty _
  simp only [h0, ciSup_const]

/-- Copy of S35 `norm_setIntegral_le_two_level` for a measurable set `D` in place of `Δ`: if `|G| ≤ w β₁` on
`B` and `|G| ≤ w β₂` off `B`, with `∬_D w = 1`, then `|∬_D G| ≤ β₁ ∬_{D ∩ B} w + β₂`. -/
theorem s36g_two_level {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {D : Set ℂ} (hD : MeasurableSet D)
    {G : ℂ → E} {w : ℂ → ℝ} {B : Set ℂ} (hB : MeasurableSet B)
    (hw1 : ∫⁻ z in D, ENNReal.ofReal (w z) = 1) {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (h1 : ∀ᵐ z ∂(volume.restrict D), z ∈ B → ‖G z‖ ≤ w z * β₁)
    (h2 : ∀ᵐ z ∂(volume.restrict D), z ∉ B → ‖G z‖ ≤ w z * β₂) :
    ‖∫ z in D, G z‖ ≤ β₁ * (∫⁻ z in D ∩ B, ENNReal.ofReal (w z)).toReal + β₂ := by
  have hsplit_w := lintegral_inter_add_sdiff (μ := volume) (fun z => ENNReal.ofReal (w z)) D hB
  rw [hw1] at hsplit_w
  have hsplit_F := lintegral_inter_add_sdiff (μ := volume) (fun z => ENNReal.ofReal ‖G z‖) D hB
  rw [ae_restrict_iff' hD] at h1 h2
  have hb1 : ∫⁻ z in D ∩ B, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal β₁ * ∫⁻ z in D ∩ B, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hD.inter hB)]
    filter_upwards [h1] with z hz hzB
    rw [← ENNReal.ofReal_mul hβ₁]
    exact ENNReal.ofReal_le_ofReal (by linarith [hz hzB.1 hzB.2])
  have hb2 : ∫⁻ z in D \ B, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal β₂ * ∫⁻ z in D \ B, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hD.diff hB)]
    filter_upwards [h2] with z hz hzB
    rw [← ENNReal.ofReal_mul hβ₂]
    exact ENNReal.ofReal_le_ofReal (by linarith [hz hzB.1 hzB.2])
  set a := ∫⁻ z in D ∩ B, ENNReal.ofReal (w z) with ha_def
  set b := ∫⁻ z in D \ B, ENNReal.ofReal (w z) with hb_def
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_add_self)
  have hab : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hsplit_w, ENNReal.toReal_one]
  have hFle : ∫⁻ z in D, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal β₁ * a + ENNReal.ofReal β₂ * b := by
    rw [← hsplit_F]
    exact add_le_add hb1 hb2
  have hRtop : ENNReal.ofReal β₁ * a + ENNReal.ofReal β₂ * b ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb⟩
  have hFr : (∫⁻ z in D, ENNReal.ofReal ‖G z‖).toReal ≤ β₁ * a.toReal + β₂ * b.toReal := by
    have h := ENNReal.toReal_mono hRtop hFle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hβ₁, ENNReal.toReal_ofReal hβ₂] at h
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict D) G
  have hbr : b.toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := a)]
  nlinarith [mul_le_mul_of_nonneg_left hbr hβ₂]

/-- Copy of S35 `hamilton_split_bound` for a measurable set `D` in place of `Δ`: if `|G| = w g(t)` a.e. on `D`
with `∬_D w = 1`, `0 ≤ t ≤ k` and `g` monotone on `[0, k]`, then
`|∬_D G| + (g(k) - g(k')) ∬_{t ≤ k'} w ≤ g(k)`. -/
theorem s36g_split_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {D : Set ℂ} (hD : MeasurableSet D)
    {G : ℂ → E} {w t : ℂ → ℝ} {g : ℝ → ℝ} {k k' : ℝ}
    (hw : ∀ z, 0 ≤ w z) (hw1 : ∫⁻ z in D, ENNReal.ofReal (w z) = 1)
    (hwm : AEMeasurable w (volume.restrict D))
    (hFt : ∀ᵐ z ∂(volume.restrict D), ‖G z‖ = w z * g (t z) ∧ 0 ≤ t z ∧ t z ≤ k)
    (hg : MonotoneOn g (Icc 0 k)) (hk' : 0 ≤ k') (hk'k : k' ≤ k) (hgk' : 0 ≤ g k') :
    ‖∫ z in D, G z‖ +
      (g k - g k') * (∫⁻ z in {z ∈ D | t z ≤ k'}, ENNReal.ofReal (w z)).toReal ≤ g k := by
  have hgk : g k' ≤ g k := hg ⟨hk', hk'k⟩ ⟨hk'.trans hk'k, le_rfl⟩ hk'k
  set m := ∫⁻ z in {z ∈ D | t z ≤ k'}, ENNReal.ofReal (w z) with hm
  have hm1 : m ≤ 1 := by
    rw [← hw1]
    exact lintegral_mono_set (fun z hz => hz.1)
  have hmr : m.toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hm1
    simpa using h
  have hmr0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  by_cases hF : AEStronglyMeasurable G (volume.restrict D)
  swap
  · rw [integral_non_aestronglyMeasurable hF, norm_zero, zero_add]
    nlinarith
  have hHm : AEMeasurable (fun z => ‖G z‖ - w z * g k') (volume.restrict D) :=
    hF.norm.aemeasurable.sub (hwm.mul_const _)
  have hHmeas : Measurable (hHm.mk _) := hHm.measurable_mk
  have hHae : ∀ᵐ z ∂(volume.restrict D), ‖G z‖ - w z * g k' = hHm.mk _ z := hHm.ae_eq_mk
  have hBm : MeasurableSet {z | hHm.mk _ z ≤ 0} := measurableSet_le hHmeas measurable_const
  have hgood : ∀ᵐ z ∂volume, z ∈ D →
      (‖G z‖ = w z * g (t z) ∧ 0 ≤ t z ∧ t z ≤ k) ∧ ‖G z‖ - w z * g k' = hHm.mk _ z := by
    have h := hFt.and hHae
    rwa [ae_restrict_iff' hD] at h
  have hEB : m ≤ ∫⁻ z in D ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    refine lintegral_mono' (Measure.restrict_mono_ae ?_) le_rfl
    filter_upwards [hgood] with z hz
    intro hzE
    obtain ⟨⟨hF1, ht0, htk⟩, hH⟩ := hz hzE.1
    refine ⟨hzE.1, ?_⟩
    show hHm.mk _ z ≤ 0
    rw [← hH, hF1]
    have hle : g (t z) ≤ g k' := hg ⟨ht0, htk⟩ ⟨hk', hk'k⟩ hzE.2
    nlinarith [mul_nonneg (hw z) (sub_nonneg.2 hle)]
  have hsplit_w := lintegral_inter_add_sdiff (μ := volume) (fun z => ENNReal.ofReal (w z)) D hBm
  rw [hw1] at hsplit_w
  have hsplit_F := lintegral_inter_add_sdiff (μ := volume) (fun z => ENNReal.ofReal ‖G z‖) D hBm
  have h1 : ∫⁻ z in D ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal (g k') * ∫⁻ z in D ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hD.inter hBm)]
    filter_upwards [hgood] with z hz hzB
    obtain ⟨-, hH⟩ := hz hzB.1
    have hHz : hHm.mk _ z ≤ 0 := hzB.2
    rw [← ENNReal.ofReal_mul hgk']
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h2 : ∫⁻ z in D \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal (g k) * ∫⁻ z in D \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' (hD.diff hBm)]
    filter_upwards [hgood] with z hz hzB
    obtain ⟨⟨hF1, ht0, htk⟩, -⟩ := hz hzB.1
    rw [← ENNReal.ofReal_mul (hgk'.trans hgk), hF1]
    have hle : g (t z) ≤ g k := hg ⟨ht0, htk⟩ ⟨hk'.trans hk'k, le_rfl⟩ htk
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (hw z) (sub_nonneg.2 hle)])
  set a := ∫⁻ z in D ∩ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) with ha_def
  set b := ∫⁻ z in D \ {z | hHm.mk _ z ≤ 0}, ENNReal.ofReal (w z) with hb_def
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit_w ▸ le_add_self)
  have hab : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hsplit_w, ENNReal.toReal_one]
  have hFle : ∫⁻ z in D, ENNReal.ofReal ‖G z‖ ≤
      ENNReal.ofReal (g k') * a + ENNReal.ofReal (g k) * b := by
    rw [← hsplit_F]
    exact add_le_add h1 h2
  have hRtop : ENNReal.ofReal (g k') * a + ENNReal.ofReal (g k) * b ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb⟩
  have hFr : (∫⁻ z in D, ENNReal.ofReal ‖G z‖).toReal ≤ g k' * a.toReal + g k * b.toReal := by
    have h := ENNReal.toReal_mono hRtop hFle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hgk', ENNReal.toReal_ofReal (hgk'.trans hgk)] at h
  have hma : m.toReal ≤ a.toReal := ENNReal.toReal_mono ha hEB
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict D) G
  have hb' : b.toReal = 1 - a.toReal := by linarith
  rw [hb'] at hFr
  nlinarith [mul_nonneg (sub_nonneg.2 hgk) (sub_nonneg.2 hma)]

/-- Copy of S35 `m35_integrable_terms` on `F`: for a unit `φ ∈ A(Γ, F)` and measurable `κ` with `|κ| ≤ k < 1`
a.e. on `F`, the integrands `|φ||κ|²/(1 - |κ|²)` and `κφ/(1 - |κ|²)` are integrable on `F`. -/
theorem s36g_terms {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) :
    IntegrableOn (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) F ∧
      IntegrableOn (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2)) F := by
  obtain ⟨hφi, -⟩ := h36p_integrableOn_of_unit hFH hFm hφ hn
  have hφint := hφi.norm
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hφm : AEMeasurable φ (volume.restrict F) := hφi.aestronglyMeasurable.aemeasurable
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
  · have hκφm : AEMeasurable (fun z => κ z * φ z) (volume.restrict F) :=
      hκm.aemeasurable.mul hφm
    have hdm : AEMeasurable (fun z => (1 - (‖κ z‖ : ℂ) ^ 2)) (volume.restrict F) :=
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

/-- Copy of S35 `integral_phi_kappa_sq_ge` on `F`: for a unit `φ ∈ A(Γ, F)`, measurable `κ` with
`|κ| ≤ k < 1` a.e. on `F` and `0 ≤ k' ≤ k`,
`∬_F |φ| |κ|²/(1 - |κ|²) ≥ g(k') - g(k) ∬_{F ∩ {|κ| ≤ k'}} |φ|`, `g(t) = t²/(1 - t²)`. -/
theorem s36g_sq_ge {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k k' : ℝ} (hk1 : k < 1)
    (hk'0 : 0 ≤ k') (hk'k : k' ≤ k) (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) :
    k' ^ 2 / (1 - k' ^ 2) - k ^ 2 / (1 - k ^ 2) *
        (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal ≤
      ∫ z in F, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
  have hk0 : 0 ≤ k := hk'0.trans hk'k
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hq' : 0 < 1 - k' ^ 2 := by nlinarith
  set s := k ^ 2 / (1 - k ^ 2) with hs_def
  set g' := k' ^ 2 / (1 - k' ^ 2) with hg'_def
  have hs0 : 0 ≤ s := div_nonneg (by positivity) hq.le
  have hgs : g' ≤ s := by
    rw [hg'_def, hs_def, div_le_div_iff₀ hq' hq]
    nlinarith [pow_le_pow_left₀ hk'0 hk'k 2]
  obtain ⟨hφi, hφ1⟩ := h36p_integrableOn_of_unit hFH hFm hφ hn
  have hφint := hφi.norm
  have hφm : AEMeasurable (fun z => ‖φ z‖) (volume.restrict F) := hφi.aestronglyMeasurable.norm.aemeasurable
  have hFm' : AEStronglyMeasurable (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (volume.restrict F) :=
    ((hφm.mul (hκm.aemeasurable.norm.pow_const 2)).div
      (aemeasurable_const.sub (hκm.aemeasurable.norm.pow_const 2))).aestronglyMeasurable
  have hFb : ∀ᵐ z ∂(volume.restrict F), 0 ≤ ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ∧
      ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤ ‖φ z‖ * s := by
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    refine ⟨div_nonneg (by positivity) hp.le, ?_⟩
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [hs_def, div_le_div_iff₀ hp hq]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
  have hFint : IntegrableOn (fun z => ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) F := by
    refine Integrable.mono' (hφint.mul_const s) hFm' ?_
    filter_upwards [hFb] with z hz
    rw [Real.norm_of_nonneg hz.1]
    exact hz.2
  have hsplit : ∫ z in F, (‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) =
      s - ∫ z in F, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) := by
    rw [integral_sub (hφint.mul_const s) hFint, integral_mul_const, hφ1, one_mul]
  have hBm : MeasurableSet {z | ‖hκm.mk κ z‖ ≤ k'} :=
    measurableSet_le hκm.stronglyMeasurable_mk.measurable.norm measurable_const
  have hmk := hκm.ae_eq_mk
  rw [EventuallyEq, ae_restrict_iff' hFm] at hmk
  have hEB : ({z ∈ F | ‖κ z‖ ≤ k'} : Set ℂ) =ᵐ[volume]
      (F ∩ {z | ‖hκm.mk κ z‖ ≤ k'} : Set ℂ) := by
    filter_upwards [hmk] with z hz
    apply propext
    constructor
    · rintro ⟨hzF, hzk⟩
      refine ⟨hzF, ?_⟩
      show ‖hκm.mk κ z‖ ≤ k'
      rw [← hz hzF]
      exact hzk
    · rintro ⟨hzF, hzk⟩
      refine ⟨hzF, ?_⟩
      show ‖κ z‖ ≤ k'
      rw [hz hzF]
      exact hzk
  have h1 : ∀ᵐ z ∂(volume.restrict F), z ∈ {z | ‖hκm.mk κ z‖ ≤ k'} →
      ‖‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤ ‖φ z‖ * s := by
    filter_upwards [hFb] with z hz _
    rw [Real.norm_of_nonneg (sub_nonneg.2 hz.2)]
    linarith [hz.1]
  have h2 : ∀ᵐ z ∂(volume.restrict F), z ∉ {z | ‖hκm.mk κ z‖ ≤ k'} →
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
  have hH := s36g_two_level hFm
    (G := fun z => ‖φ z‖ * s - ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
    (w := fun z => ‖φ z‖) hBm hn hs0 (sub_nonneg.2 hgs) h1 h2
  beta_reduce at hH
  rw [← Measure.restrict_congr_set hEB, hsplit, Real.norm_eq_abs] at hH
  have habs := le_abs_self (s - ∫ z in F, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
  linarith

/-- Copy of S35 `norm_integral_div_sub_le` on `F`: for a unit `φ ∈ A(Γ, F)`, measurable `κ` with
`|κ| ≤ k < 1` a.e. on `F` and `0 ≤ k' ≤ k`,
`|∬_F κφ/(1 - |κ|²) - (1 - k²)⁻¹ ∬_F κφ| ≤ (1 - k²)⁻² ∬_{F ∩ {|κ| ≤ k'}} |φ| + 2(k - k')/(1 - k²)²`. -/
theorem s36g_div_sub_le {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k k' : ℝ} (hk1 : k < 1)
    (hk'0 : 0 ≤ k') (hk'k : k' ≤ k) (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) :
    ‖(∫ z in F, κ z * φ z / (1 - ‖κ z‖ ^ 2)) -
        (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in F, κ z * φ z‖ ≤
      1 / (1 - k ^ 2) ^ 2 * (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ z‖).toReal +
        2 * (k - k') / (1 - k ^ 2) ^ 2 := by
  have hk0 : 0 ≤ k := hk'0.trans hk'k
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  obtain ⟨hφi, -⟩ := h36p_integrableOn_of_unit hFH hFm hφ hn
  have hφint := hφi.norm
  have hφm : AEMeasurable φ (volume.restrict F) := hφi.aestronglyMeasurable.aemeasurable
  have hκφm : AEMeasurable (fun z => κ z * φ z) (volume.restrict F) :=
    hκm.aemeasurable.mul hφm
  have hint2 : IntegrableOn (fun z => κ z * φ z) F := by
    refine Integrable.mono' (hφint.mul_const k) hκφm.aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have hint1 : IntegrableOn (fun z => κ z * φ z / (1 - ‖κ z‖ ^ 2)) F :=
    (s36g_terms hFH hFm hφ hn hκm hk0 hk1 hae).2
  have hsplit : (∫ z in F, κ z * φ z / (1 - ‖κ z‖ ^ 2)) -
      (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in F, κ z * φ z =
      ∫ z in F, (κ z * φ z / (1 - ‖κ z‖ ^ 2) - (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (κ z * φ z)) := by
    rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul]
  rw [hsplit]
  have hBm : MeasurableSet {z | ‖hκm.mk κ z‖ ≤ k'} :=
    measurableSet_le hκm.stronglyMeasurable_mk.measurable.norm measurable_const
  have hmk := hκm.ae_eq_mk
  rw [EventuallyEq, ae_restrict_iff' hFm] at hmk
  have hEB : ({z ∈ F | ‖κ z‖ ≤ k'} : Set ℂ) =ᵐ[volume]
      (F ∩ {z | ‖hκm.mk κ z‖ ≤ k'} : Set ℂ) := by
    filter_upwards [hmk] with z hz
    apply propext
    constructor
    · rintro ⟨hzF, hzk⟩
      refine ⟨hzF, ?_⟩
      show ‖hκm.mk κ z‖ ≤ k'
      rw [← hz hzF]
      exact hzk
    · rintro ⟨hzF, hzk⟩
      refine ⟨hzF, ?_⟩
      show ‖κ z‖ ≤ k'
      rw [hz hzF]
      exact hzk
  rw [Measure.restrict_congr_set hEB]
  have hpt : ∀ᵐ z ∂(volume.restrict F),
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
  refine s36g_two_level hFm hBm hn (by positivity)
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

/-- Γ-copy of `lemma35_4` (second case): along unit `φₙ ∈ A(Γ, F)` with `∬_F κφₙ → k`, `|κ| ≤ k` a.e. on `F`,
the mass of `|φₙ|` on `{|κ| ≤ k'}` tends to `0` for every `k' < k`. -/
theorem s36g_lim_E {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1)
    (hlim : Tendsto (fun n => beltramiPairing F κ (φ n)) atTop (𝓝 (k : ℂ)))
    {k' : ℝ} (hk' : 0 ≤ k') (hk'k : k' < k) :
    Tendsto (fun n => ∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖) atTop (𝓝 0) := by
  -- `hκm` and `hk1` are not needed: as in `lemma35_4`, the split bound needs no measurability of `κ`;
  -- the statement stays true without them.
  have _hκm := hκm
  have _hk1 := hk1
  have hw1 : ∀ n, ∫⁻ z in F, ENNReal.ofReal ‖φ n z‖ = 1 := fun n => (hφ n).2
  have hwm : ∀ n, AEMeasurable (fun z => ‖φ n z‖) (volume.restrict F) := fun n =>
    (((hφ n).1.1.continuousOn.mono hFH).norm.aestronglyMeasurable hFm).aemeasurable
  have hm1 : ∀ n, ∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖ ≤ 1 := fun n => by
    rw [← hw1 n]
    exact lintegral_mono_set (fun z hz => hz.1)
  have hg : MonotoneOn (fun t : ℝ => t) (Icc 0 k) := fun _ _ _ _ h => h
  have key : ∀ n, ‖∫ z in F, κ z * φ n z‖ +
      (k - k') * (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖).toReal ≤ k := by
    intro n
    have hFt : ∀ᵐ z ∂(volume.restrict F),
        ‖κ z * φ n z‖ = ‖φ n z‖ * (fun t : ℝ => t) ‖κ z‖ ∧ 0 ≤ ‖κ z‖ ∧ ‖κ z‖ ≤ k := by
      filter_upwards [hae] with z hz
      exact ⟨by rw [norm_mul, mul_comm], norm_nonneg _, hz⟩
    exact s36g_split_bound hFm (fun z => norm_nonneg _) (hw1 n) (hwm n) hFt hg hk' hk'k.le hk'
  refine tendsto_zero_of_add_mul_le (sub_pos.2 hk'k) hm1 key ?_
  have hn := hlim.norm
  unfold beltramiPairing at hn
  rwa [Complex.norm_real, Real.norm_of_nonneg hk0] at hn

/-- Γ-copy of `lemma35_5`: along a Hamilton sequence, `∬_F |φₙ| |κ|²/(1 - |κ|²) → k²/(1 - k²)`. -/
theorem s36g_lim_sq {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1)
    (hlim : Tendsto (fun n => beltramiPairing F κ (φ n)) atTop (𝓝 (k : ℂ))) :
    Tendsto (fun n => ∫ z in F, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) atTop (𝓝 (k ^ 2 / (1 - k ^ 2))) := by
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hE : ∀ k' : ℝ, 0 < k' → k' < k →
      Tendsto (fun n => ∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k'}, ENNReal.ofReal ‖φ n z‖) atTop (𝓝 0) :=
    fun k' hk' hk'k => s36g_lim_E hFH hFm hκm hk0 hk1 hae hφ hlim hk'.le hk'k
  -- upper bound `≤ k²/(1 - k²)`
  have hup : ∀ n, ∫ z in F, ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ≤ k ^ 2 / (1 - k ^ 2) := by
    intro n
    have h2 : ∀ᵐ z ∂(volume.restrict F), z ∉ (∅ : Set ℂ) →
        ‖‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)‖ ≤ ‖φ n z‖ * (k ^ 2 / (1 - k ^ 2)) := by
      filter_upwards [hae] with z hz _
      have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
      rw [Real.norm_of_nonneg (div_nonneg (by positivity) hp.le), mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [div_le_div_iff₀ hp hq]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hz 2]
    have h := s36g_two_level hFm (G := fun z => ‖φ n z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))
      (w := fun z => ‖φ n z‖) MeasurableSet.empty (hφ n).2 le_rfl (div_nonneg (by positivity) hq.le)
      (Filter.Eventually.of_forall fun z hz => hz.elim) h2
    simp only [zero_mul, zero_add, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  refine tendsto_order.2 ⟨fun b hb => ?_,
    fun b hb => Filter.Eventually.of_forall fun n => (hup n).trans_lt hb⟩
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
    have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k - k / ((j : ℝ) + 2)},
        ENNReal.ofReal ‖φ n z‖).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
      rw [ENNReal.toReal_zero] at h
      exact h
    have hlow : Tendsto (fun n => (k - k / ((j : ℝ) + 2)) ^ 2 / (1 - (k - k / ((j : ℝ) + 2)) ^ 2) -
        k ^ 2 / (1 - k ^ 2) * (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k - k / ((j : ℝ) + 2)},
          ENNReal.ofReal ‖φ n z‖).toReal) atTop
        (𝓝 ((k - k / ((j : ℝ) + 2)) ^ 2 / (1 - (k - k / ((j : ℝ) + 2)) ^ 2) - k ^ 2 / (1 - k ^ 2) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hmR)
    rw [mul_zero, sub_zero] at hlow
    filter_upwards [hlow.eventually (lt_mem_nhds hj')] with n hn
    exact hn.trans_le (s36g_sq_ge hFH hFm (hφ n).1 (hφ n).2 hκm hk1 hk'0.le hk'k.le hae)

/-- Γ-copy of the `lemma35_6` estimate: along a Hamilton sequence, `∬_F κφₙ/(1 - |κ|²) → k/(1 - k²)`. -/
theorem s36g_lim_div {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1)
    (hlim : Tendsto (fun n => beltramiPairing F κ (φ n)) atTop (𝓝 (k : ℂ))) :
    Tendsto (fun n => ∫ z in F, κ z * φ n z / (1 - ‖κ z‖ ^ 2)) atTop (𝓝 ((k / (1 - k ^ 2) : ℝ) : ℂ)) := by
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  rcases hk0.eq_or_lt with hk | hk
  · -- `k = 0`: `κ = 0` a.e. on `F`
    have hz : ∀ n, ∫ z in F, κ z * φ n z / (1 - ‖κ z‖ ^ 2) = 0 := fun n => by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with z hz
      have h0 : κ z = 0 := norm_le_zero_iff.1 (hk ▸ hz)
      simp [h0]
    simp only [hz]
    rw [← hk]
    simp
  have hP : Tendsto (fun n => (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in F, κ z * φ n z) atTop
      (𝓝 ((((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (k : ℂ))) := tendsto_const_nhds.mul hlim
  have hval : (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (k : ℂ) = ((k / (1 - k ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval] at hP
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set δ := min k (ε * (1 - k ^ 2) ^ 2 / 8) with hδ_def
  have hδ0 : 0 < δ := lt_min hk (by positivity)
  have hδk : δ ≤ k := min_le_left _ _
  have hδε : δ ≤ ε * (1 - k ^ 2) ^ 2 / 8 := min_le_right _ _
  have hm := s36g_lim_E hFH hFm hκm hk0 hk1 hae hφ hlim (k' := k - δ) (by linarith) (by linarith)
  have hmR : Tendsto (fun n => (∫⁻ z in {z ∈ F | ‖κ z‖ ≤ k - δ}, ENNReal.ofReal ‖φ n z‖).toReal) atTop
      (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
    rw [ENNReal.toReal_zero] at h
    exact h
  have hC : 0 < 1 / (1 - k ^ 2) ^ 2 := by positivity
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hmR (ε / 4 / (1 / (1 - k ^ 2) ^ 2)) (by positivity)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hP (ε / 4) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_of_max_le_left hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg, lt_div_iff₀ hC] at h1
  have h2 := hN2 n (le_of_max_le_right hn)
  have h3 := s36g_div_sub_le hFH hFm (hφ n).1 (hφ n).2 hκm hk1 (k' := k - δ) (by linarith) (by linarith) hae
  rw [dist_eq_norm] at h2 ⊢
  have h4 : 2 * (k - (k - δ)) / (1 - k ^ 2) ^ 2 ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc ‖(∫ z in F, κ z * φ n z / (1 - ‖κ z‖ ^ 2)) - ((k / (1 - k ^ 2) : ℝ) : ℂ)‖
      ≤ ‖(∫ z in F, κ z * φ n z / (1 - ‖κ z‖ ^ 2)) - (((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z in F, κ z * φ n z‖ +
        ‖(((1 - k ^ 2)⁻¹ : ℝ) : ℂ) * (∫ z in F, κ z * φ n z) - ((k / (1 - k ^ 2) : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-- G3 glue: expanding `|1 - κw|² = 1 - 2 Re(κw) + |κ|²` (`w = φ/|φ|`, `|w| = 1` a.e.) for a unit `φ ∈ A(Γ, F)`:
`∬_F |φ| |1 - κφ/|φ||²/(1 - |κ|²) = 1 + 2 ∬_F |φ||κ|²/(1 - |κ|²) - 2 Re ∬_F κφ/(1 - |κ|²)`. -/
theorem s36g_expand {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) :
    ∫⁻ z in F, ENNReal.ofReal (‖φ z‖ * (‖1 - κ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) =
      ENNReal.ofReal (1 + 2 * (∫ z in F, ‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) -
        2 * (∫ z in F, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) := by
  have hae' : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ max k 0 := hae.mono fun z hz => hz.trans (le_max_left _ _)
  obtain ⟨hDint, hIint⟩ := s36g_terms hFH hFm hφ hn hκm (le_max_right k 0) (max_lt hk1 one_pos) hae'
  obtain ⟨hφi, hφ1⟩ := h36p_integrableOn_of_unit hFH hFm hφ hn
  have hφint := hφi.norm
  set P : ℂ → ℝ := fun z => ‖φ z‖ * (‖1 - κ z * φ z / ‖φ z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) with hP
  have hexp : ∀ᵐ z ∂(volume.restrict F), P z =
      ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) - 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    filter_upwards [hae] with z hz
    exact m35_expand (hz.trans_lt hk1)
  have hre_int : IntegrableOn (fun z => (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) F := by
    simpa using hIint.re
  have hSint : IntegrableOn (fun z => ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2)) -
      2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) F :=
    (hφint.add (hDint.const_mul 2)).sub (hre_int.const_mul 2)
  have hPint : IntegrableOn P F := hSint.congr (by
    filter_upwards [hexp] with z hz
    exact hz.symm)
  have hP0 : ∀ᵐ z ∂(volume.restrict F), 0 ≤ P z := by
    filter_upwards [hae] with z hz
    have hp : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    exact mul_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) hp.le)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hPint hP0]
  congr 1
  have hre : ∫ z in F, (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re =
      (∫ z in F, κ z * φ z / (1 - ‖κ z‖ ^ 2)).re := by
    simpa using integral_re hIint
  have hB2 : IntegrableOn (fun z => 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) F :=
    hDint.const_mul 2
  have hA1 : IntegrableOn (fun z => ‖φ z‖ + 2 * (‖φ z‖ * ‖κ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2))) F :=
    hφint.add hB2
  have hA2 : IntegrableOn (fun z => 2 * (κ z * φ z / (1 - ‖κ z‖ ^ 2)).re) F :=
    hre_int.const_mul 2
  rw [integral_congr_ae hexp, integral_sub hA1 hA2, integral_add hφint hB2, integral_const_mul,
    integral_const_mul, hφ1, hre]

/-- G3 glue: along a Hamilton sequence the right side of the main inequality (without `K[ν]`) tends to
`1 + 2k²/(1 - k²) - 2k/(1 - k²) = (1 - k)/(1 + k)`. -/
theorem s36g_lim_main {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict F)) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hae : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1)
    (hlim : Tendsto (fun n => beltramiPairing F κ (φ n)) atTop (𝓝 (k : ℂ))) :
    Tendsto (fun n => (∫⁻ z in F, ENNReal.ofReal (‖φ n z‖ *
      (‖1 - κ z * φ n z / ‖φ n z‖‖ ^ 2 / (1 - ‖κ z‖ ^ 2)))).toReal) atTop (𝓝 ((1 - k) / (1 + k))) := by
  have hq : 0 < 1 - k ^ 2 := by nlinarith
  have hS := s36g_lim_sq hFH hFm hκm hk0 hk1 hae hφ hlim
  have hD := s36g_lim_div hFH hFm hκm hk0 hk1 hae hφ hlim
  have hre : Tendsto (fun n => (∫ z in F, κ z * φ n z / (1 - ‖κ z‖ ^ 2)).re) atTop
      (𝓝 (k / (1 - k ^ 2))) := by
    have h := (Complex.continuous_re.tendsto _).comp hD
    rw [Complex.ofReal_re] at h
    exact h
  have hx := (tendsto_const_nhds (x := (1 : ℝ)).add (hS.const_mul 2)).sub (hre.const_mul 2)
  have hval : 1 + 2 * (k ^ 2 / (1 - k ^ 2)) - 2 * (k / (1 - k ^ 2)) = (1 - k) / (1 + k) := by
    have h1 : (1 + k) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hx
  have hpos : 0 ≤ (1 - k) / (1 + k) := div_nonneg (by linarith) (by linarith)
  have hm := hx.max (tendsto_const_nhds (x := (0 : ℝ)))
  rw [max_eq_left hpos] at hm
  refine hm.congr fun n => ?_
  rw [s36g_expand hFH hFm hκm hk1 hae (hφ n).1 (hφ n).2, ENNReal.toReal_ofReal']

/-- G3 glue: `1 ≤ ofReal K * L` with `L < ⊤` and `0 ≤ K` gives `1 ≤ K * L.toReal`. -/
theorem s36g_toReal_step {K : ℝ} (hK : 0 ≤ K) {L : ℝ≥0∞} (hL : L ≠ ⊤) (h : 1 ≤ ENNReal.ofReal K * L) :
    1 ≤ K * L.toReal := by
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h
  rwa [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at h2

/-- G3 glue (the final algebra): if `1 ≤ (1 + k')/(1 - k') · xₙ` and `xₙ → (1 - k)/(1 + k)`, then `k ≤ k'`. -/
theorem s36g_final {k k' : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hk'0 : 0 ≤ k') (hk'1 : k' < 1) {x : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 ((1 - k) / (1 + k)))) (hK : ∀ n, 1 ≤ (1 + k') / (1 - k') * x n) : k ≤ k' := by
  -- `hk1` and `hk'0` are not needed (the limit inequality and `k' < 1` suffice); the statement stays true
  -- without them.
  have _hk1 := hk1
  have _hk'0 := hk'0
  have hlim := hx.const_mul ((1 + k') / (1 - k'))
  have h1 : 1 ≤ (1 + k') / (1 - k') * ((1 - k) / (1 + k)) := ge_of_tendsto' hlim hK
  have hd : 0 < (1 - k') * (1 + k) := mul_pos (by linarith) (by linarith)
  rw [div_mul_div_comm, le_div_iff₀ hd, one_mul] at h1
  nlinarith

end LiZhongQC
