import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.StrebelGammaTransport
import LiZhongQC.Lemmas.StrebelGammaMapFacts

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Retained predecessor B1 proof: str_inv. -/
theorem str_inv {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    (upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖)) (h36p_m γ z) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      (upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖)) z := by
  have hdet := b33_d_det γ
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hz))
  have hA := hφ.2.2 γ hγ z hz
  have hφm : φ (h36p_m γ z) = φ z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
    rw [← hA, div_mul_cancel₀ _ (pow_ne_zero _ hden)]
    rfl
  rw [indicator_of_mem (h36p_m_mem γ hz), indicator_of_mem hz, hφm, norm_mul, norm_pow,
    ENNReal.ofReal_mul (norm_nonneg _), mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  rw [show ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 4 * ‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 = 1 by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow], ENNReal.ofReal_one, mul_one]

/-- Retained predecessor B1 proof: str_count. -/
theorem str_count (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ᵐ w ∂(volume.restrict upperHalf),
      ∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => (1 : ℝ≥0∞)) γ =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
  have hF' := hF
  obtain ⟨hFH, hFm, hcov, -, -⟩ := hF
  filter_upwards [h36p_ae_unique hΓ hF', ae_restrict_mem isOpen_upperHalf.measurableSet]
    with w hu hw
  have hinv : ∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => (1 : ℝ≥0∞)) γ =
      ∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => (1 : ℝ≥0∞)) γ := rfl
  obtain ⟨γ₀, hγ₀, hγ₀F⟩ := hcov ⟨w, hw⟩
  have hγ₀F' : h36p_m γ₀ w ∈ F := by
    have e := h36p_m_coe γ₀ ⟨w, hw⟩
    simp only at e
    rw [e]
    exact hγ₀F
  have := h36p_a_count (P := fun γ => h36p_m γ w ∈ F) hγ₀
    (fun γ hγ => ⟨fun h => hu γ hγ γ₀ hγ₀ h hγ₀F', ?_⟩) 1
  · rw [mul_one] at this
    exact this
  · rintro (rfl | rfl)
    · exact hγ₀F'
    · show h36p_m (-γ₀) w ∈ F
      rw [h36p_a_m_neg]
      exact hγ₀F'

/-- Retained predecessor B1 proof: str_fdi. -/
theorem str_fdi (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {E : Set ℂ} (hEm : MeasurableSet E) (hEH : E ⊆ upperHalf)
    (hcnt : ∀ᵐ w ∂(volume.restrict upperHalf),
      ∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) γ =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞)) :
    ∫⁻ z in E, ENNReal.ofReal ‖φ z‖ = ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  set G := upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖) with hG
  have hGm : Measurable G := str_meas hφ.1
  have hun := h36p_unfold hΓ hF' (g := E.indicator G) (hGm.indicator hEm)
  have hR : ∫⁻ z in upperHalf, E.indicator G z = ∫⁻ z in E, ENNReal.ofReal ‖φ z‖ := by
    rw [setLIntegral_indicator hEm, inter_eq_left.2 hEH]
    exact setLIntegral_congr_fun hEm fun z hz => indicator_of_mem (hEH hz) _
  have hΦ : AEMeasurable (fun z => ENNReal.ofReal ‖φ z‖) (volume.restrict F) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (hφ.1.continuousOn.mono hFH).norm).aemeasurable hFm
  have h1 : ∀ γ : Γ, ∫⁻ z in F, E.indicator G (h36p_m γ.1 z) *
      ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) =
      ∫⁻ z in F, (h36p_m γ.1 ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) z * ENNReal.ofReal ‖φ z‖ := by
    intro γ
    refine setLIntegral_congr_fun hFm fun z hz => ?_
    have hinv := str_inv hφ γ.2 (hFH hz)
    by_cases hE : h36p_m γ.1 z ∈ E
    · rw [indicator_of_mem hE, indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' E from hE), one_mul, hinv,
        indicator_of_mem (hFH hz)]
    · rw [indicator_of_notMem hE, indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' E from hE)]
      simp
  have hcF : ∀ᵐ z ∂(volume.restrict F),
      ∑' γ : Γ, (h36p_m γ.1 ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) z =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH hcnt] with z hz
    rw [← hz]
    refine tsum_congr fun γ => ?_
    by_cases hE : h36p_m γ.1 z ∈ E
    · rw [indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' E from hE),
        indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 z ∈ E} from hE)]
    · rw [indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' E from hE),
        indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 z ∈ E} from hE)]
  have hL : ∑' γ : Γ, ∫⁻ z in F, E.indicator G (h36p_m γ.1 z) *
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ := by
    rw [tsum_congr h1, ← lintegral_tsum]
    · rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr_ae ?_
      filter_upwards [hcF] with z hz
      rw [ENNReal.tsum_mul_right, hz]
    · intro γ
      exact (measurable_const.indicator ((h36p_m_measurable γ.1) hEm)).aemeasurable.mul hΦ
  rw [hL, hR] at hun
  have h0 : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≠ 0 := by
    have := h36p_mult_pos (Γ := Γ)
    exact_mod_cast this.ne'
  exact ((ENNReal.mul_right_inj h0 (ENNReal.natCast_ne_top _)).1 hun).symm

/-- Retained predecessor B1 proof: str_ae_comp. -/
theorem str_ae_comp {f₀ : ℂ → ℂ} {K₀ : ℝ} (hK₀ : IsKQC f₀ upperHalf K₀)
    (hf₀s : f₀ '' upperHalf = upperHalf) {P : ℂ → Prop}
    (hP : ∀ᵐ w ∂(volume.restrict upperHalf), P w) :
    ∀ᵐ z ∂(volume.restrict upperHalf), P (f₀ z) := by
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  rw [ae_restrict_iff' hΔ, ae_iff] at hP
  set N : Set ℂ := {w | ¬ (w ∈ upperHalf → P w)} with hN
  have hNsub : N ⊆ f₀ '' upperHalf := by
    intro w hw'
    rw [hf₀s]
    by_contra h
    exact hw' (fun h' => absurd h' h)
  have hnull : volume (Function.invFunOn f₀ upperHalf '' N) = 0 :=
    ac_n_volume_image_null_of_isKQC (thm7_2_inv hK₀) hNsub hP
  have hleft : LeftInvOn (Function.invFunOn f₀ upperHalf) f₀ upperHalf :=
    hK₀.2.2.1.2.1.leftInvOn_invFunOn
  rw [ae_restrict_iff' hΔ]
  filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzΔ
  have hf₀z : f₀ z ∈ upperHalf := hf₀s ▸ mem_image_of_mem f₀ hzΔ
  by_contra hcon
  exact hz ⟨f₀ z, fun h => hcon (h hf₀z), hleft hzΔ⟩

/-- Retained predecessor B1 proof: str_neg. -/
theorem str_neg {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    (fun z => -φ z) ∈ integrableAutomorphicQD Γ F := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨h1.neg, ?_, fun γ hγ z hz => ?_⟩
  · simpa [phiArea] using h2
  · have := h3 γ hγ z hz
    simp only [neg_div, this]

/-- Retained predecessor B1 proof: str_area. -/
theorem str_area (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    (hcomm : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, g (h36p_m γ z) = h36p_m γ (g z)) :
    ∫⁻ z in F, ENNReal.ofReal (‖φ (g z)‖ * jacobian g z) = phiArea φ F := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hinj : InjOn g upperHalf := hgK.2.2.1.2.1
  have hEm : MeasurableSet (g '' F) :=
    hFm.image_of_continuousOn_injOn (hgK.2.2.1.1.mono hFH) (hinj.mono hFH)
  have hEH : g '' F ⊆ upperHalf := hgimg ▸ image_mono hFH
  -- the count for `g(F)`
  have hcF := str_count hΓ hF'
  have hN : volume {w | w ∈ upperHalf ∧ ¬ (∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator
      (fun _ => (1 : ℝ≥0∞)) γ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞))} = 0 := by
    have := hcF
    rw [ae_restrict_iff' hΔ, ae_iff] at this
    convert this using 2
    ext w
    simp [and_comm]
  have hgN : volume (g '' {w | w ∈ upperHalf ∧ ¬ (∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator
      (fun _ => (1 : ℝ≥0∞)) γ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞))}) = 0 :=
    ac_n_volume_image_null_of_isKQC hgK (fun w hw => hw.1) hN
  have hcnt : ∀ᵐ z ∂(volume.restrict upperHalf),
      ∑' γ : Γ, {γ : Γ | h36p_m γ.1 z ∈ g '' F}.indicator (fun _ => (1 : ℝ≥0∞)) γ =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
    rw [ae_restrict_iff' hΔ]
    filter_upwards [compl_mem_ae_iff.2 hgN] with z hz hzH
    obtain ⟨w, hw, rfl⟩ : z ∈ g '' upperHalf := by rw [hgimg]; exact hzH
    have hwN : ∑' γ : Γ, {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => (1 : ℝ≥0∞)) γ =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
      by_contra hne
      exact hz ⟨w, ⟨hw, hne⟩, rfl⟩
    rw [← hwN]
    refine tsum_congr fun γ => ?_
    have hx : h36p_m γ.1 w ∈ upperHalf := h36p_m_mem _ hw
    have hiff : h36p_m γ.1 (g w) ∈ g '' F ↔ h36p_m γ.1 w ∈ F := by
      rw [← hcomm γ.1 γ.2 w hw]
      exact hinj.mem_image_iff hFH hx
    by_cases h : h36p_m γ.1 w ∈ F
    · rw [indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 (g w) ∈ g '' F} from hiff.2 h),
        indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
    · rw [indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 (g w) ∈ g '' F} from fun h' => h (hiff.1 h')),
        indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
  have hfdi := str_fdi hΓ hF' hφ hEm hEH hcnt
  -- change of variables
  have hcv := fx_lintegral_image_eq hgK ((g '' F).indicator (fun w => ENNReal.ofReal ‖φ w‖))
  rw [hgimg, setLIntegral_indicator hEm, inter_eq_left.2 hEH, hfdi] at hcv
  rw [phiArea, hcv]
  have hind : ∀ z ∈ upperHalf, ENNReal.ofReal (jacobian g z) *
      (g '' F).indicator (fun w => ENNReal.ofReal ‖φ w‖) (g z) =
      F.indicator (fun z => ENNReal.ofReal (‖φ (g z)‖ * jacobian g z)) z := by
    intro z hz
    by_cases hzF : z ∈ F
    · rw [indicator_of_mem (show g z ∈ g '' F from mem_image_of_mem g hzF), indicator_of_mem hzF,
        ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
    · have : g z ∉ g '' F := fun h => hzF ((hinj.mem_image_iff hFH hz).1 h)
      rw [indicator_of_notMem this, indicator_of_notMem hzF, mul_zero]
  rw [setLIntegral_congr_fun hΔ hind, setLIntegral_indicator hFm, inter_eq_left.2 hFH]

/-- Retained predecessor B1 proof: s36g_sqrt_form. -/
theorem s36g_sqrt_form (a b : ℂ) {y t : ℂ} (ht : t ^ 2 = y) :
    ‖a + b * (y / ((‖y‖ : ℝ) : ℂ))‖ * Real.sqrt ‖y‖ = ‖a * conj t + b * t‖ := by
  rcases eq_or_ne t 0 with h0 | ht0
  · subst h0
    rw [← ht]
    simp
  · have hy : ‖y‖ = ‖t‖ ^ 2 := by rw [← ht, norm_pow]
    have hsq : Real.sqrt ‖y‖ = ‖conj t‖ := by
      rw [hy, Real.sqrt_sq (norm_nonneg _), Complex.norm_conj]
    have hconj : conj t ≠ 0 := (map_ne_zero _).2 ht0
    have e : y / ((‖y‖ : ℝ) : ℂ) = t / conj t := by
      have h1 : ((‖y‖ : ℝ) : ℂ) = t * conj t := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hy]
      rw [h1, ← ht, div_eq_div_iff (mul_ne_zero ht0 hconj) hconj]
      ring
    rw [e, hsq, ← norm_mul, add_mul, mul_assoc b, div_mul_cancel₀ _ hconj]

/-- Retained predecessor B1 proof: s36g_sqrt_exists. -/
theorem s36g_sqrt_exists (y : ℂ) : ∃ t : ℂ, t ^ 2 = y :=
  IsAlgClosed.exists_pow_nat_eq y (by norm_num)

/-- Retained predecessor B1 proof: s36g_branch. -/
theorem s36g_branch {x y s t : ℂ} (hs : s ^ 2 = x) (ht : t ^ 2 = y) :
    ∃ t' : ℂ, t' ^ 2 = y ∧ ‖t' - s‖ ≤ Real.sqrt ‖y - x‖ := by
  have hprod : ‖t - s‖ * ‖t + s‖ = ‖y - x‖ := by
    rw [← norm_mul, ← ht, ← hs]
    congr 1
    ring
  rcases le_total ‖t - s‖ ‖t + s‖ with h | h
  · refine ⟨t, ht, ?_⟩
    have h2 : ‖t - s‖ ^ 2 ≤ ‖y - x‖ := by
      rw [← hprod, sq]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h2
  · refine ⟨-t, by rw [neg_sq, ht], ?_⟩
    have he : ‖-t - s‖ = ‖t + s‖ := by
      rw [← norm_neg]
      congr 1
      ring
    have h2 : ‖-t - s‖ ^ 2 ≤ ‖y - x‖ := by
      rw [he, ← hprod, sq, mul_comm ‖t - s‖]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h2

/-- Retained predecessor B1 proof: s36g_N_le. -/
theorem s36g_N_le (a b x y : ℂ) :
    ‖a + b * (y / ((‖y‖ : ℝ) : ℂ))‖ * Real.sqrt ‖y‖ ≤
      ‖a + b * (x / ((‖x‖ : ℝ) : ℂ))‖ * Real.sqrt ‖x‖ + (‖a‖ + ‖b‖) * Real.sqrt ‖y - x‖ := by
  obtain ⟨s, hs⟩ := s36g_sqrt_exists x
  obtain ⟨t, ht⟩ := s36g_sqrt_exists y
  obtain ⟨t', ht', hd⟩ := s36g_branch hs ht
  rw [s36g_sqrt_form a b ht', s36g_sqrt_form a b hs]
  have e : a * conj t' + b * t' = (a * conj s + b * s) + (a * conj (t' - s) + b * (t' - s)) := by
    rw [map_sub]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  calc ‖a * conj (t' - s) + b * (t' - s)‖ ≤ ‖a * conj (t' - s)‖ + ‖b * (t' - s)‖ := norm_add_le _ _
    _ = (‖a‖ + ‖b‖) * ‖t' - s‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]; ring
    _ ≤ (‖a‖ + ‖b‖) * Real.sqrt ‖y - x‖ :=
      mul_le_mul_of_nonneg_left hd (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Retained predecessor B1 proof: s36g_N_bound. -/
theorem s36g_N_bound (a b x : ℂ) :
    ‖a + b * (x / ((‖x‖ : ℝ) : ℂ))‖ * Real.sqrt ‖x‖ ≤ (‖a‖ + ‖b‖) * Real.sqrt ‖x‖ := by
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have hu : ‖x / ((‖x‖ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  calc ‖a + b * (x / ((‖x‖ : ℝ) : ℂ))‖ ≤ ‖a‖ + ‖b‖ * ‖x / ((‖x‖ : ℝ) : ℂ)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ ‖a‖ + ‖b‖ := by
        have := mul_le_mul_of_nonneg_left hu (norm_nonneg b)
        linarith

/-- Retained predecessor B1 proof: s36g_sqrt_tri. -/
theorem s36g_sqrt_tri (u v : ℂ) : Real.sqrt ‖v‖ ≤ Real.sqrt ‖u‖ + Real.sqrt ‖u - v‖ := by
  have h1 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
    have := norm_sub_le u (u - v)
    rwa [sub_sub_cancel] at this
  have hp := Real.sqrt_nonneg ‖u‖
  have hq := Real.sqrt_nonneg ‖u - v‖
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg hp hq, ?_⟩
  nlinarith [Real.sq_sqrt (norm_nonneg u), Real.sq_sqrt (norm_nonneg (u - v)), mul_nonneg hp hq]

/-- Retained predecessor B1 proof: s36g_T_eq. -/
theorem s36g_T_eq (φ g : ℂ → ℂ) (z : ℂ) :
    ‖φ z‖ * lambdaStretchPlane φ φ g z =
      Real.sqrt ‖φ (g z)‖ * (‖dz g z + dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ))‖ * Real.sqrt ‖φ z‖) := by
  unfold lambdaStretchPlane
  calc ‖φ z‖ * (Real.sqrt ‖φ (g z)‖ * ‖dz g z + dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ))‖ / Real.sqrt ‖φ z‖)
      = Real.sqrt ‖φ (g z)‖ * ‖dz g z + dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ))‖ *
          (‖φ z‖ / Real.sqrt ‖φ z‖) := by ring
    _ = _ := by rw [Real.div_sqrt]; ring

/-- Retained predecessor B1 proof: s36g_T_le. -/
theorem s36g_T_le (φ χ g : ℂ → ℂ) (z : ℂ) :
    ‖χ z‖ * lambdaStretchPlane χ χ g z ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z +
      (‖dz g z‖ + ‖dzbar g z‖) * (Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖φ z - χ z‖ +
        Real.sqrt ‖φ (g z) - χ (g z)‖ * Real.sqrt ‖φ z‖ +
        Real.sqrt ‖φ (g z) - χ (g z)‖ * Real.sqrt ‖φ z - χ z‖) := by
  rw [s36g_T_eq, s36g_T_eq]
  set D := ‖dz g z‖ + ‖dzbar g z‖ with hD
  set A' := Real.sqrt ‖χ (g z)‖
  set A := Real.sqrt ‖φ (g z)‖
  set e1 := Real.sqrt ‖φ (g z) - χ (g z)‖
  set e2 := Real.sqrt ‖φ z - χ z‖
  set f := Real.sqrt ‖φ z‖
  set Nχ := ‖dz g z + dzbar g z * (χ z / ((‖χ z‖ : ℝ) : ℂ))‖ * Real.sqrt ‖χ z‖
  set Nφ := ‖dz g z + dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ))‖ * f
  have hA' : A' ≤ A + e1 := s36g_sqrt_tri _ _
  have hN : Nχ ≤ Nφ + D * e2 := by
    have := s36g_N_le (dz g z) (dzbar g z) (φ z) (χ z)
    rwa [norm_sub_rev (χ z)] at this
  have hNφ : Nφ ≤ D * f := s36g_N_bound _ _ _
  have hD0 : 0 ≤ D := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have he1 : 0 ≤ e1 := Real.sqrt_nonneg _
  have he2 : 0 ≤ e2 := Real.sqrt_nonneg _
  have hNχ0 : 0 ≤ Nχ := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  calc A' * Nχ ≤ (A + e1) * (Nφ + D * e2) :=
        mul_le_mul hA' hN hNχ0 (add_nonneg hA0 he1)
    _ = A * Nφ + D * (A * e2) + e1 * Nφ + D * (e1 * e2) := by ring
    _ ≤ A * Nφ + D * (A * e2) + e1 * (D * f) + D * (e1 * e2) := by
        have := mul_le_mul_of_nonneg_left hNφ he1
        linarith
    _ = A * Nφ + D * (A * e2 + e1 * f + e1 * e2) := by ring

/-- Retained predecessor B1 proof: s36g_D_meas. -/
theorem s36g_D_meas (g : ℂ → ℂ) : Measurable (fun z => ‖dz g z‖ + ‖dzbar g z‖) := by
  have h1 : Measurable (fun z => fderiv ℝ g z 1) := measurable_fderiv_apply_const ℝ g 1
  have hI : Measurable (fun z => fderiv ℝ g z I) := measurable_fderiv_apply_const ℝ g I
  have hdz : Measurable (fun z => dz g z) := by
    unfold dz
    exact (h1.sub (measurable_const.mul hI)).div_const 2
  have hdzb : Measurable (fun z => dzbar g z) := by
    unfold dzbar
    exact (h1.add (measurable_const.mul hI)).div_const 2
  exact hdz.norm.add hdzb.norm

/-- Retained predecessor B1 proof: s36g_holder. -/
theorem s36g_holder (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {g : ℂ → ℂ} {K : ℝ}
    (hgK : IsKQC g upperHalf K) (hgimg : g '' upperHalf = upperHalf)
    (hcomm : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, g (h36p_m γ z) = h36p_m γ (g z))
    {α β : ℂ → ℂ} (hα : α ∈ integrableAutomorphicQD Γ F) (hβ : DifferentiableOn ℂ β upperHalf) :
    ∫⁻ z in F, ENNReal.ofReal ((‖dz g z‖ + ‖dzbar g z‖) * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖) ≤
      ENNReal.ofReal (Real.sqrt K) * phiArea α F ^ (1 / 2 : ℝ) * phiArea β F ^ (1 / 2 : ℝ) := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hK0 : 0 ≤ K := zero_le_one.trans hgK.2.1
  have hmono : volume.restrict F ≤ volume.restrict upperHalf := Measure.restrict_mono hFH le_rfl
  set D : ℂ → ℝ := fun z => ‖dz g z‖ + ‖dzbar g z‖ with hDdef
  have hDm : Measurable D := s36g_D_meas g
  have hgc : ContinuousOn g upperHalf := hgK.2.2.1.1
  have hmaps : MapsTo g upperHalf upperHalf := fun z hz => hgimg ▸ mem_image_of_mem g hz
  have hαg : AEMeasurable (fun z => Real.sqrt ‖α (g z)‖) (volume.restrict F) := by
    have hc : ContinuousOn (fun z => Real.sqrt ‖α (g z)‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn (hα.1.continuousOn.comp hgc hmaps)
    exact (hc.aemeasurable hΔ).mono_measure hmono
  have hβm : AEMeasurable (fun z => Real.sqrt ‖β z‖) (volume.restrict F) := by
    have hc : ContinuousOn (fun z => Real.sqrt ‖β z‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn hβ.continuousOn
    exact (hc.aemeasurable hΔ).mono_measure hmono
  set f1 : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖) with hf1
  set f2 : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt ‖β z‖) with hf2
  have hf1m : AEMeasurable f1 (volume.restrict F) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hDm.aemeasurable.mul hαg)
  have hf2m : AEMeasurable f2 (volume.restrict F) := ENNReal.measurable_ofReal.comp_aemeasurable hβm
  have hsplit : ∀ z, ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖) = (f1 * f2) z := by
    intro z
    simp only [hf1, hf2, Pi.mul_apply]
    rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _))]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict F) Real.HolderConjugate.two_two hf1m hf2m
  have e2 : ∫⁻ z in F, f2 z ^ (2 : ℝ) = phiArea β F := by
    unfold phiArea
    refine lintegral_congr fun z => ?_
    simp only [hf2]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (norm_nonneg _)]
  have hsq : ∀ᵐ z ∂(volume.restrict F), D z ^ 2 ≤ K * jacobian g z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH (thm9_4_dilatation_ae hgK)] with z hz
    have h0 : 0 ≤ D z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    simp only [hDdef]
    unfold jacobian
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have e1 : ∫⁻ z in F, f1 z ^ (2 : ℝ) ≤ ENNReal.ofReal K * phiArea α F := by
    rw [← str_area hΓ hF hα hgK hgimg hcomm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hsq] with z hz
    simp only [hf1]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.sqrt_nonneg _)) (by norm_num), Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right hz (norm_nonneg (α (g z)))
    nlinarith [norm_nonneg (α (g z))]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc ∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖)
      = ∫⁻ z in F, (f1 * f2) z := lintegral_congr hsplit
    _ ≤ (∫⁻ z in F, f1 z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ z in F, f2 z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hH
    _ ≤ (ENNReal.ofReal K * phiArea α F) ^ (1 / (2 : ℝ)) * phiArea β F ^ (1 / (2 : ℝ)) := by
        rw [e2]
        exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow e1 hhalf) (by positivity)
    _ = ENNReal.ofReal (Real.sqrt K) * phiArea α F ^ (1 / 2 : ℝ) * phiArea β F ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ENNReal.ofReal_rpow_of_nonneg hK0 hhalf,
          ← Real.sqrt_eq_rpow]

/-- Retained predecessor B1 proof: s36g_half_mul. -/
theorem s36g_half_mul (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- Retained predecessor B1 proof: s36g_sub. -/
theorem s36g_sub {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ χ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hχ : χ ∈ integrableAutomorphicQD Γ F) :
    phiArea (φ - χ) F ≤ phiArea φ F + phiArea χ F ∧ (φ - χ) ∈ integrableAutomorphicQD Γ F := by
  have hFH : F ⊆ upperHalf := hF.1
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hmono : volume.restrict F ≤ volume.restrict upperHalf := Measure.restrict_mono hFH le_rfl
  have hle : phiArea (φ - χ) F ≤ phiArea φ F + phiArea χ F := by
    unfold phiArea
    have hm : AEMeasurable (fun z => ENNReal.ofReal ‖χ z‖) (volume.restrict F) := by
      have hc : ContinuousOn (fun z => ‖χ z‖) upperHalf := continuous_norm.comp_continuousOn hχ.1.continuousOn
      exact ENNReal.measurable_ofReal.comp_aemeasurable ((hc.aemeasurable hΔ).mono_measure hmono)
    rw [← lintegral_add_right' _ hm]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
  refine ⟨hle, hφ.1.sub hχ.1, lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hφ.2.1, hχ.2.1⟩), ?_⟩
  intro γ hγ z hz
  simp only [Pi.sub_apply]
  rw [sub_div, hφ.2.2 γ hγ z hz, hχ.2.2 γ hγ z hz]

/-- Retained predecessor B1 proof: s36g_lam_bound. -/
theorem s36g_lam_bound (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ χ ∈ integrableAutomorphicQD Γ F,
      ∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal
        (lambdaStretchPlane χ χ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) ≤
      C * phiArea χ F := by
  obtain ⟨K, hgK, hgimg, hcomm⟩ := str_g_facts μ ν hrel
  set g := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1 with hg
  refine ⟨ENNReal.ofReal (Real.sqrt K), ENNReal.ofReal_ne_top, fun χ hχ => ?_⟩
  have hH := s36g_holder hΓ hF hgK hgimg hcomm hχ hχ.1
  rw [mul_assoc, s36g_half_mul] at hH
  refine le_trans (lintegral_mono fun z => ?_) hH
  rw [← ENNReal.ofReal_mul (norm_nonneg _), s36g_T_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := s36g_N_bound (dz g z) (dzbar g z) (χ z)
  have := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg ‖χ (g z)‖)
  nlinarith [Real.sqrt_nonneg ‖χ (g z)‖, Real.sqrt_nonneg ‖χ z‖]

/-- Retained predecessor B1 proof: s36g_lam_cont. -/
theorem s36g_lam_cont (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ ∈ integrableAutomorphicQD Γ F, ∀ χ ∈ integrableAutomorphicQD Γ F,
      ∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal
        (lambdaStretchPlane χ χ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) ≤
      (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
        (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z)) +
      C * (phiArea φ F + phiArea χ F) ^ (1 / 2 : ℝ) * phiArea (φ - χ) F ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hgK, hgimg, hcomm⟩ := str_g_facts μ ν hrel
  set g := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1 with hg
  refine ⟨3 * ENNReal.ofReal (Real.sqrt K), ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
    fun φ hφ χ hχ => ?_⟩
  have hFH : F ⊆ upperHalf := hF.1
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hmono : volume.restrict F ≤ volume.restrict upperHalf := Measure.restrict_mono hFH le_rfl
  obtain ⟨hδle, hδ⟩ := s36g_sub hF hφ hχ
  set δ := φ - χ with hδdef
  set D : ℂ → ℝ := fun z => ‖dz g z‖ + ‖dzbar g z‖ with hDdef
  have hDm : Measurable D := s36g_D_meas g
  have hgc : ContinuousOn g upperHalf := hgK.2.2.1.1
  have hmaps : MapsTo g upperHalf upperHalf := fun z hz => hgimg ▸ mem_image_of_mem g hz
  -- a.e.-measurability of the three error terms
  have haem : ∀ α β : ℂ → ℂ, DifferentiableOn ℂ α upperHalf → DifferentiableOn ℂ β upperHalf →
      AEMeasurable (fun z => ENNReal.ofReal (D z * Real.sqrt ‖α (g z)‖ * Real.sqrt ‖β z‖))
        (volume.restrict F) := by
    intro α β hα hβ
    have h1 : ContinuousOn (fun z => Real.sqrt ‖α (g z)‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn (hα.continuousOn.comp hgc hmaps)
    have h2 : ContinuousOn (fun z => Real.sqrt ‖β z‖) upperHalf :=
      (Real.continuous_sqrt.comp continuous_norm).comp_continuousOn hβ.continuousOn
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((hDm.aemeasurable.mul
      ((h1.aemeasurable hΔ).mono_measure hmono)).mul ((h2.aemeasurable hΔ).mono_measure hmono))
  have hpt : ∀ z, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal (lambdaStretchPlane χ χ g z) ≤
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) +
        (ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) := by
    intro z
    have hD0 : 0 ≤ D z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hφl : 0 ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z := by
      rw [s36g_T_eq]
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_add hφl (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
        (mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := s36g_T_le φ χ g z
    simp only [hδdef, Pi.sub_apply]
    simp only [hDdef] at *
    linarith
  have hφd := hφ.1
  have hδd := hδ.1
  have hI1 := s36g_holder hΓ hF hgK hgimg hcomm hφ hδd
  have hI2 := s36g_holder hΓ hF hgK hgimg hcomm hδ hφd
  have hI3 := s36g_holder hΓ hF hgK hgimg hcomm hδ hδd
  set S := phiArea φ F + phiArea χ F with hS
  set c := ENNReal.ofReal (Real.sqrt K) with hc
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have ha : phiArea φ F ^ (1 / 2 : ℝ) ≤ S ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow le_self_add hhalf
  have hd : phiArea δ F ^ (1 / 2 : ℝ) ≤ S ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hδle hhalf
  calc ∫⁻ z in F, ENNReal.ofReal ‖χ z‖ * ENNReal.ofReal (lambdaStretchPlane χ χ g z)
      ≤ ∫⁻ z in F, (ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) +
        (ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
          ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖))) := lintegral_mono hpt
    _ = (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        ((∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖)) +
          (∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖)) +
          ∫⁻ z in F, ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) := by
        have hsum : AEMeasurable (fun z => ENNReal.ofReal (D z * Real.sqrt ‖φ (g z)‖ * Real.sqrt ‖δ z‖) +
            ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖φ z‖) +
            ENNReal.ofReal (D z * Real.sqrt ‖δ (g z)‖ * Real.sqrt ‖δ z‖)) (volume.restrict F) :=
          ((haem _ _ hφd hδd).add (haem _ _ hδd hφd)).add (haem _ _ hδd hδd)
        rw [lintegral_add_right' _ hsum, lintegral_add_right' _ (haem _ _ hδd hδd),
          lintegral_add_right' _ (haem _ _ hδd hφd)]
    _ ≤ (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        (c * phiArea φ F ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ) +
          c * phiArea δ F ^ (1 / 2 : ℝ) * phiArea φ F ^ (1 / 2 : ℝ) +
          c * phiArea δ F ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ)) :=
        add_le_add le_rfl (add_le_add (add_le_add hI1 hI2) hI3)
    _ ≤ (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        (c * S ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ) +
          c * phiArea δ F ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) +
          c * S ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = (∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z)) +
        3 * c * S ^ (1 / 2 : ℝ) * phiArea δ F ^ (1 / 2 : ℝ) := by ring

/-- Retained predecessor B1 proof: s36a_ordinary_dense. -/
theorem s36a_ordinary_dense (hΓ : IsFuchsian Γ) (hsecond : (ordinarySet Γ).Nonempty) :
    Dense {x : ℝ | (((x : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ} := by
  -- `hΓ` is not needed: the argument uses only the definition of the limit set (orbit limits) and the
  -- reality of `Γ`; the statement stays true without it.
  have _hΓ := hΓ
  -- every limit point is a limit of the orbit of an ordinary point `x₀ ∈ ℝ̂` (possibly `∞`); that orbit
  -- lies in `ℝ̂`, is ordinary, and eventually lies in any real interval around the limit point
  obtain ⟨x₀, hx₀R, hx₀Λ⟩ := hsecond
  have hx₀Λ' : x₀ ∉ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := hx₀Λ
  rw [Metric.dense_iff]
  intro x r hr
  by_contra hcon
  have hall : ∀ y : ℝ, dist y x < r → (((y : ℂ)) : ExtPlane) ∈ fuchsianLimitSet Γ := by
    intro y hy
    by_contra h
    exact hcon ⟨y, mem_ball.2 hy, h⟩
  have hxΛ : (((x : ℂ)) : ExtPlane) ∈ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) :=
    hall x (by simpa using hr)
  obtain ⟨γs, -, hlim⟩ := k22_t_limitSet_subset_orbitLim hx₀Λ' hxΛ
  have hU : IsOpen (((↑) : ℂ → ExtPlane) '' Metric.ball (x : ℂ) r) :=
    OnePoint.isOpenMap_coe _ Metric.isOpen_ball
  have hmem : (((x : ℂ)) : ExtPlane) ∈ ((↑) : ℂ → ExtPlane) '' Metric.ball (x : ℂ) r :=
    ⟨x, mem_ball_self hr, rfl⟩
  obtain ⟨n, w, hw, hweq⟩ := (hlim.eventually (hU.mem_nhds hmem)).exists
  obtain ⟨γr, -, hγr⟩ := Subgroup.mem_map.1 (γs n).2
  have hR : mobiusSL (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) x₀ ∈ extRealLine := by
    rw [← hγr]
    exact k24_real_mapsTo_extRealLine γr hx₀R
  have hO : mobiusSL (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) x₀ ∉
      limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) :=
    fun h => hx₀Λ' (k22_t_mem_limitSet_of_smul (γs n).2 h)
  rw [← hweq] at hR hO
  have hwR : w.im = 0 := by
    rcases hR with ⟨z, hz, hzw⟩ | h
    · rw [← OnePoint.coe_injective hzw]
      exact hz
    · exact absurd h (OnePoint.coe_ne_infty w)
  have hwre : ((w.re : ℝ) : ℂ) = w := Complex.ext rfl (by simp [hwR])
  refine hO ?_
  rw [← hwre]
  refine hall w.re ?_
  rw [Real.dist_eq]
  have h1 := mem_ball.1 hw
  rw [Complex.dist_eq, ← hwre, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  exact h1

end LiZhongQC
