import LiZhongQC.Lemmas.Mobius

/-!
# Injective holomorphic maps

Classical facts about conformal maps used throughout the book, which are not (yet) in Mathlib:

* a non-vanishing analytic function has a local analytic `n`-th root — `exists_analyticAt_pow_eq`;
* an injective holomorphic map on an open set has non-vanishing derivative
                                                             — `deriv_ne_zero_of_injOn`;
* the inverse of a conformal map is conformal                — `IsConformalOnto.symm`;
* conformal equivalence is reflexive, symmetric and transitive.
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

namespace LiZhongQC

/-- A non-vanishing analytic function has an analytic `n`-th root near a point. -/
theorem exists_analyticAt_pow_eq {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k z₀ ∧ k z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, k z ^ n = h z := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hc
    exact h0 hc.symm
  have hu : AnalyticAt ℂ (fun z => h z / h z₀) z₀ := hh.div_const
  have hu1 : (fun z => h z / h z₀) z₀ ∈ slitPlane := by
    simp only [div_self h0]
    exact one_mem_slitPlane
  refine ⟨fun z => c * exp (log (h z / h z₀) / n), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hu.clog hu1).div_const.cexp)
  · exact mul_ne_zero hc0 (exp_ne_zero _)
  · have hev : ∀ᶠ z in 𝓝 z₀, h z ≠ 0 := hh.continuousAt.eventually_ne h0
    filter_upwards [hev] with z hz
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : (n : ℂ) * (log (h z / h z₀) / n) = log (h z / h z₀) := by
      field_simp
    rw [mul_pow, ← exp_nat_mul, e, exp_log (div_ne_zero hz h0), hc]
    field_simp

/-- An injective holomorphic map on an open set has non-vanishing derivative. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    deriv f z₀ ≠ 0 := by
  intro hd
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt (hU.mem_nhds hz₀)
  have hga : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hfa.sub analyticAt_const
  -- the order of `f - f z₀` at `z₀` is finite
  have htop : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ ⊤ := by
    intro htop
    have hev := analyticOrderAt_eq_top.1 htop
    have hev' : ∀ᶠ z in 𝓝[≠] z₀, (f z - f z₀ = 0 ∧ z ∈ U) ∧ z ∈ ({z₀}ᶜ : Set ℂ) :=
      ((hev.and (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hgz, hzU⟩, hzne⟩ := hev'.exists
    exact hzne (hinj hzU hz₀ (sub_eq_zero.1 hgz))
  -- the order is at least two, since `f' (z₀) = 0`
  have hge : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z₀) z₀ := by
    have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) z₀ := by
      rw [Order.one_le_iff_ne_zero]
      exact hfa.deriv.analyticOrderAt_ne_zero.2 hd
    rw [← hfa.analyticOrderAt_deriv_add_one]
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by gcongr
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hn2 : 2 ≤ n := by
    rw [← hn] at hge
    exact_mod_cast hge
  obtain ⟨h, hha, hh0, hgev⟩ := hga.analyticOrderAt_eq_natCast.1 hn.symm
  obtain ⟨k, hka, hk0, hkev⟩ := exists_analyticAt_pow_eq hha hh0 (by omega : 0 < n)
  -- `f - f z₀ = φⁿ` with `φ = (z - z₀) k` a local diffeomorphism at `z₀`
  set φ : ℂ → ℂ := fun z => (z - z₀) * k z with hφ
  have hφa : AnalyticAt ℂ φ z₀ := (analyticAt_id.sub analyticAt_const).mul hka
  have hφ0 : φ z₀ = 0 := by simp [hφ]
  have hφd : deriv φ z₀ = k z₀ := by
    have hder : HasDerivAt (fun z => (z - z₀) * k z) (1 * k z₀ + (z₀ - z₀) * deriv k z₀) z₀ :=
      ((hasDerivAt_id' z₀).sub_const z₀).mul hka.differentiableAt.hasDerivAt
    exact hder.deriv.trans (by ring)
  have hmap : map φ (𝓝 z₀) = 𝓝 (φ z₀) :=
    hφa.hasStrictDerivAt.map_nhds_eq (by rw [hφd]; exact hk0)
  have hSmem : {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 z₀ := by
    filter_upwards [hgev, hkev, hU.mem_nhds hz₀] with z hz hkz hzU
    refine ⟨?_, hzU⟩
    rw [hz]
    simp only [hφ, smul_eq_mul, mul_pow, hkz]
  have himg : φ '' {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 (0 : ℂ) := by
    rw [← hφ0, ← hmap]
    exact image_mem_map hSmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  -- two distinct points with the same `n`-th power
  have hprim : IsPrimitiveRoot (exp (2 * π * I / n)) n := Complex.isPrimitiveRoot_exp n (by omega)
  have hω1 : exp (2 * π * I / n) ≠ 1 := hprim.ne_one (by omega)
  have hωn : exp (2 * π * I / n) ^ n = 1 := hprim.pow_eq_one
  have hωnorm : ‖exp (2 * π * I / n)‖ = 1 := hprim.norm'_eq_one (by omega)
  have hw0 : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hε).ne'
  have hnorm : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hw₁ : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := mem_ball_zero_iff.2 hnorm
  have hw₂ : ((ε / 2 : ℝ) : ℂ) * exp (2 * π * I / n) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_mul, hωnorm, mul_one]
    exact hnorm
  obtain ⟨z₁, ⟨hz₁, hz₁U⟩, hφz₁⟩ := hball hw₁
  obtain ⟨z₂, ⟨hz₂, hz₂U⟩, hφz₂⟩ := hball hw₂
  have hne : z₁ ≠ z₂ := by
    rintro rfl
    apply hω1
    have e : ((ε / 2 : ℝ) : ℂ) * exp (2 * π * I / n) = ((ε / 2 : ℝ) : ℂ) * 1 := by
      rw [mul_one, ← hφz₂, hφz₁]
    exact mul_left_cancel₀ hw0 e
  apply hne
  apply hinj hz₁U hz₂U
  have e₁ : f z₁ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₁, hφz₁]
  have e₂ : f z₂ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₂, hφz₂, mul_pow, hωn, mul_one]
  linear_combination e₁ - e₂

/-- The inverse of a conformal map is conformal. -/
theorem IsConformalOnto.symm {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) : IsConformalOnto (Function.invFunOn f U) V U := by
  obtain ⟨hd, hinj, himg⟩ := hf
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ V, Function.invFunOn f U w ∈ U ∧ f (Function.invFunOn f U w) = w := by
    intro w hw
    rw [← himg] at hw
    exact ⟨Function.invFunOn_mem hw, Function.invFunOn_eq hw⟩
  refine ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, ?_⟩
  · rw [← himg] at hw
    obtain ⟨z₀, hz₀, rfl⟩ := hw
    have hfa : AnalyticAt ℂ f z₀ := hd.analyticAt (hU.mem_nhds hz₀)
    have hder := deriv_ne_zero_of_injOn hU hd hinj hz₀
    have hs : HasStrictDerivAt f (deriv f z₀) z₀ := hfa.hasStrictDerivAt
    have hinv : HasStrictDerivAt (hs.localInverse f (deriv f z₀) z₀ hder) (deriv f z₀)⁻¹ (f z₀) :=
      hs.to_localInverse hder
    have hleftloc := hs.eventually_left_inverse hder
    have hrightloc := hs.eventually_right_inverse hder
    have hg0 : hs.localInverse f (deriv f z₀) z₀ hder (f z₀) = z₀ := hleftloc.self_of_nhds
    have hU' : ∀ᶠ y in 𝓝 (f z₀), hs.localInverse f (deriv f z₀) z₀ hder y ∈ U :=
      (HasStrictDerivAt.hasDerivAt hinv).continuousAt.preimage_mem_nhds
        (by rw [hg0]; exact hU.mem_nhds hz₀)
    have hev : Function.invFunOn f U =ᶠ[𝓝 (f z₀)] hs.localInverse f (deriv f z₀) z₀ hder := by
      filter_upwards [hrightloc, hU'] with y hy1 hy2
      have hyV : y ∈ f '' U := ⟨_, hy2, hy1⟩
      exact hinj (Function.invFunOn_mem hyV) hy2 ((Function.invFunOn_eq hyV).trans hy1.symm)
    exact ((HasStrictDerivAt.hasDerivAt hinv).differentiableAt.congr_of_eventuallyEq
      hev).differentiableWithinAt
  · rw [← (hright w₁ hw₁).2, ← (hright w₂ hw₂).2, h]
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hright w hw).1
    · intro hz
      exact ⟨f z, himg ▸ mem_image_of_mem f hz, hleft z hz⟩

/-- A conformal map sends neighbourhoods to neighbourhoods. -/
theorem IsConformalOnto.image_mem_nhds {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) {z : ℂ} (hz : z ∈ U) {s : Set ℂ} (hs : s ∈ 𝓝 z) :
    f '' s ∈ 𝓝 (f z) := by
  have hfa : AnalyticAt ℂ f z := hf.1.analyticAt (hU.mem_nhds hz)
  have hder := deriv_ne_zero_of_injOn hU hf.1 hf.2.1 hz
  rw [← hfa.hasStrictDerivAt.map_nhds_eq hder]
  exact image_mem_map hs

/-- The image of an open set under a conformal map is open. -/
theorem IsConformalOnto.isOpen {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) : IsOpen V := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  rw [← hf.2.2] at hw ⊢
  obtain ⟨z, hz, rfl⟩ := hw
  exact hf.image_mem_nhds hU hz (hU.mem_nhds hz)

/-- The inverse of a conformal map is complex differentiable at every image point. -/
theorem IsConformalOnto.differentiableAt_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ (Function.invFunOn f U) (f z) := by
  have hfz : f z ∈ V := hf.2.2 ▸ mem_image_of_mem f hz
  exact (hf.symm hU).1.differentiableAt ((hf.isOpen hU).mem_nhds hfz)

/-- Chain rule for a (real) curve `γ` followed by a conformal map `f`; when `γ` is not
differentiable at `t`, neither is `f ∘ γ`, since `γ = f⁻¹ ∘ (f ∘ γ)` near `t`. -/
theorem IsConformalOnto.deriv_comp {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) {γ : ℝ → ℂ} {t : ℝ} (hγt : ∀ᶠ s in 𝓝 t, γ s ∈ U) :
    deriv (f ∘ γ) t = deriv f (γ t) * deriv γ t := by
  have hγU : γ t ∈ U := hγt.self_of_nhds
  have hfd : DifferentiableAt ℂ f (γ t) := hf.1.differentiableAt (hU.mem_nhds hγU)
  by_cases hγ : DifferentiableAt ℝ γ t
  · exact (hfd.hasDerivAt.comp t hγ.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hγ, mul_zero]
    apply deriv_zero_of_not_differentiableAt
    intro hcomp
    apply hγ
    have hinv := hf.differentiableAt_invFunOn hU hγU
    have heq : Function.invFunOn f U ∘ (f ∘ γ) =ᶠ[𝓝 t] γ := by
      filter_upwards [hγt] with s hs
      exact hf.2.1.leftInvOn_invFunOn hs
    exact ((hinv.restrictScalars ℝ).comp t hcomp).congr_of_eventuallyEq heq.symm

section Jacobian

open MeasureTheory
open scoped ENNReal

/-- The real Jacobian determinant of the complex-linear map `w ↦ a w` is `|a|²`. -/
theorem det_restrictScalars_toSpanSingleton (a : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).det = ‖a‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

/-- Change of variables under a conformal map: `∬_V g = ∬_U g(f(z)) |f'(z)|²`. -/
theorem lintegral_image_conformal {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in V, g w = ∫⁻ z in U, ‖deriv f z‖ₑ ^ 2 * g (f z) := by
  rw [← hf.2.2, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
    (fun z hz => ((hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hf.2.1 g]
  refine setLIntegral_congr_fun hU.measurableSet fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end Jacobian

/-- The identity is a conformal map of any set onto itself. -/
theorem isConformalOnto_id (U : Set ℂ) : IsConformalOnto id U U :=
  ⟨differentiableOn_id, injOn_id U, image_id U⟩

/-- Conformal equivalence is reflexive. -/
theorem ConformallyEquivalent.refl (U : Set ℂ) : ConformallyEquivalent U U :=
  ⟨id, isConformalOnto_id U⟩

/-- Conformal equivalence of open sets is symmetric. -/
theorem ConformallyEquivalent.symm {U V : Set ℂ} (h : ConformallyEquivalent U V) (hU : IsOpen U) :
    ConformallyEquivalent V U := by
  obtain ⟨f, hf⟩ := h
  exact ⟨_, hf.symm hU⟩

/-- Conformal equivalence is transitive. -/
theorem ConformallyEquivalent.trans {U V W : Set ℂ} (h₁ : ConformallyEquivalent U V)
    (h₂ : ConformallyEquivalent V W) : ConformallyEquivalent U W := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨g ∘ f, hg.comp hf⟩

end LiZhongQC
