import References.GardinerLakic2000.Ch11.S02_ExtremalProblem

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.3 Weyl's lemma

Source `teichmuller.txt`, lines 8411–8456 (Chapter 11, §11.3).

* Formula (11.6) (`f_z̄ = (f_x + i f_y)/2`, l. 8420) — exists: `LiZhongQC.dzbar`
* Formula (11.8) (`f_z̄ = h` in the sense of distributions, l. 8436) — `HasDistribDzbar`
* Theorem 2 (Weyl's lemma, l. 8443) — `thm11_2`
* Corollary 1 (l. 8445) — `cor11_2_1`

Not items: (11.7) (integration by parts for `C¹` functions, l. 8428, the motivation of (11.8)); the convention on
domains of integration (l. 8433). Modelling: test functions are `C¹` with compact support in `D`, extended by `0`, and
the integrals are over the plane; `f` and `h` are locally integrable on `D`. Near misses: A's `HasDistribPartials`
(both partial derivatives, `C^∞` tests) and `LiZhongQC.sp_w_weyl` (continuous `F`, `C²` tests). In Corollary 1,
`L₁`-quadratic differentials are A's `integrableQDSet`, the local coordinates are the charts of `R`, and the
conclusion compares `φ` with a holomorphic quadratic differential (`LiZhongQC.holQuadDiffSubmodule`) almost
everywhere in every chart.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (dzbar holQuadDiffSubmodule)

/-- **Formula (11.8)** (§11.3, l. 8436). `f_z̄ = h` in `D` in the sense of distributions: `f`, `h` are locally
integrable on `D` and `∬ h ψ = −∬ f ψ_z̄` for every `C¹` function `ψ` with compact support in `D`. -/
def HasDistribDzbar (f h : ℂ → ℂ) (D : Set ℂ) : Prop :=
  LocallyIntegrableOn f D ∧ LocallyIntegrableOn h D ∧
    ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ z, h z * ψ z = -∫ z, f z * dzbar ψ z

/-- Helper for `thm11_2`: the cut-off `1_{Kₙ} f` of an `f ∈ L¹(D)` to the compact exhaustion set `Kₙ ⊆ D` is
integrable. -/
theorem gl11_integrable_indicator {D : Set ℂ} {f : ℂ → ℂ} (hf : IntegrableOn f D) (n : ℕ) :
    Integrable ((LiZhongQC.lemma92Exhaust D n).indicator f) volume :=
  (integrable_indicator_iff (LiZhongQC.isCompact_lemma92Exhaust D n).measurableSet).2
    (hf.mono_set (LiZhongQC.lemma92Exhaust_subset D n))

/-- Helper for `thm11_2`: the mollified approximant `fₙ = ρₙ ⋆ 1_{Kₙ} f` is `C¹`
(`LiZhongQC.contDiff_lemma92Approx` with integrability in place of continuity). -/
theorem gl11_contDiff_approx {D : Set ℂ} {f : ℂ → ℂ} (hf : IntegrableOn f D) (n : ℕ) :
    ContDiff ℝ 1 (LiZhongQC.lemma92Approx D f n) :=
  (LiZhongQC.lemma92Bump n).hasCompactSupport_normed.contDiff_convolution_left _
    (LiZhongQC.lemma92Bump n).contDiff_normed (gl11_integrable_indicator hf n).locallyIntegrable

/-- Helper for `thm11_2`: the derivative of the approximant (`LiZhongQC.fderiv_lemma92Approx_apply` with
integrability in place of continuity). -/
theorem gl11_fderiv_approx_apply {D : Set ℂ} {f : ℂ → ℂ} (hf : IntegrableOn f D) (n : ℕ) (z v : ℂ) :
    fderiv ℝ (LiZhongQC.lemma92Approx D f n) z v =
      ∫ t, fderiv ℝ ((LiZhongQC.lemma92Bump n).normed volume) t v •
        (LiZhongQC.lemma92Exhaust D n).indicator f (z - t) := by
  have hg := (gl11_integrable_indicator hf n).locallyIntegrable
  have hd := (LiZhongQC.lemma92Bump n).hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((LiZhongQC.lemma92Bump n).contDiff_normed (μ := volume) (n := 1)) hg z
  have hex := ((LiZhongQC.lemma92Bump n).hasCompactSupport_normed.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
    (((LiZhongQC.lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).continuous_fderiv one_ne_zero) hg z
  unfold LiZhongQC.lemma92Approx
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp

/-- Helper for `thm11_2`: if `∬ f ψ_z̄ = 0` for all `C¹` test functions with compact support in `D`, the approximant
`fₙ` satisfies `∂_z̄ fₙ(z) = 0` wherever the mollification disc stays in `Kₙ` (`LiZhongQC.sp_w_dzbar_approx_eq_zero`
for `f ∈ L¹(D)`). -/
theorem gl11_dzbar_approx_eq_zero {D : Set ℂ} {f : ℂ → ℂ} (hf : IntegrableOn f D)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ D → ∫ y, f y * dzbar ψ y = 0)
    {n : ℕ} {z : ℂ} (hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ LiZhongQC.lemma92Exhaust D n) :
    dzbar (LiZhongQC.lemma92Approx D f n) z = 0 := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ,
      ψ = fun y : ℂ => ((((LiZhongQC.lemma92Bump n).normed volume) (z - y) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hρD : Differentiable ℝ ((LiZhongQC.lemma92Bump n).normed volume) :=
    ((LiZhongQC.lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hshift : ContDiff ℝ 1 (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hψ1 : ContDiff ℝ 1 ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((LiZhongQC.lemma92Bump n).contDiff_normed (μ := volume) (n := 1))).comp hshift
  have hψder : ∀ y v : ℂ, fderiv ℝ ψ y v
      = -((fderiv ℝ ((LiZhongQC.lemma92Bump n).normed volume) (z - y) v : ℝ) : ℂ) := by
    rw [hψdef]
    exact LiZhongQC.sp_w_fderiv_shift hρD z
  have hψ0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, not_le] at hy
    have h : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hy.le
    rw [hψdef]
    simp [LiZhongQC.lemma92Bump_normed_eq_zero h]
  have hcψ : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall z _) hψ0
  have hsψ : tsupport ψ ⊆ closedBall z (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hψ0 y h)
  have hballD : closedBall z (1 / ((n : ℝ) + 1)) ⊆ D := hball.trans (LiZhongQC.lemma92Exhaust_subset D n)
  have hdz0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), dzbar ψ y = 0 := by
    intro y hy
    have h : y ∉ tsupport ψ := fun h' => hy (hsψ h')
    show (fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 = 0
    rw [LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport h 1, LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport h I]
    ring
  have hw : ∫ y, f y * dzbar ψ y = 0 := hweak ψ hψ1 hcψ (hsψ.trans hballD)
  have hderaux : ∀ v : ℂ, fderiv ℝ (LiZhongQC.lemma92Approx D f n) z v
      = ∫ y, fderiv ℝ ((LiZhongQC.lemma92Bump n).normed volume) (z - y) v •
          (LiZhongQC.lemma92Exhaust D n).indicator f y := by
    intro v
    rw [gl11_fderiv_approx_apply hf n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((LiZhongQC.lemma92Bump n).normed volume) (z - y) v •
          (LiZhongQC.lemma92Exhaust D n).indicator f y) volume z]
    simp
  have hder : ∀ v : ℂ, fderiv ℝ (LiZhongQC.lemma92Approx D f n) z v
      = -∫ y, fderiv ℝ ψ y v * (LiZhongQC.lemma92Exhaust D n).indicator f y := by
    intro v
    rw [hderaux v, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show fderiv ℝ ((LiZhongQC.lemma92Bump n).normed volume) (z - y) v •
      (LiZhongQC.lemma92Exhaust D n).indicator f y =
        -(fderiv ℝ ψ y v * (LiZhongQC.lemma92Exhaust D n).indicator f y)
    rw [Complex.real_smul, ← neg_mul]
    congr 1
    rw [hψder y v, neg_neg]
  rw [LiZhongQC.sp_w_dzbar_combine (gl11_integrable_indicator hf n) hψ1 hcψ hder]
  have hGF : ∀ y, dzbar ψ y * (LiZhongQC.lemma92Exhaust D n).indicator f y = f y * dzbar ψ y := by
    intro y
    by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
    · rw [Set.indicator_of_mem (hball hy)]; ring
    · rw [hdz0 y hy]; ring
  rw [integral_congr_ae (Eventually.of_forall hGF), hw, neg_zero]

/-- Helper for `thm11_2`: mollification does not increase the `L¹` norm: `∫ |ρ ⋆ g| ≤ ∫ |g|` for a normalized bump
`ρ ≥ 0`, `∫ ρ = 1` (Tonelli and translation invariance). -/
theorem gl11_lintegral_conv_le (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℂ} (hg : Integrable g volume) :
    ∫⁻ x, ‖convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ := by
  have hpt : ∀ x, ‖convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (φ.normed volume t) * ‖g (x - t)‖ₑ := by
    intro x
    rw [convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
    rw [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_eq_ofReal (φ.nonneg_normed t)]
  have hmeas : AEMeasurable (Function.uncurry fun x t : ℂ =>
      ENNReal.ofReal (φ.normed volume t) * ‖g (x - t)‖ₑ) (volume.prod volume) := by
    refine ((ENNReal.measurable_ofReal.comp (φ.continuous_normed.measurable)).comp
      measurable_snd).aemeasurable.mul ?_
    exact hg.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  calc ∫⁻ x, ‖convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ.normed volume t) * ‖g (x - t)‖ₑ := lintegral_mono hpt
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ.normed volume t) * ‖g (x - t)‖ₑ := lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ENNReal.ofReal (φ.normed volume t) * ∫⁻ x, ‖g x‖ₑ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
    _ = ∫⁻ x, ‖g x‖ₑ := by
        rw [lintegral_mul_const' _ _ ?_]
        · rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
            (Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one, one_mul]
        · exact hg.hasFiniteIntegral.ne

/-- Helper for `thm11_2`: the local form. Around every point of `D` there is a disc on which `f` agrees a.e. with a
holomorphic function: the approximants `fₙ` are holomorphic there for large `n`, locally bounded by the area mean value
and `∫ |fₙ| ≤ ∫_D |f|`, so Montel gives a locally uniform limit `H`; and `fₙ → f` a.e. (Lebesgue differentiation). -/
theorem gl11_local {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} (hf : IntegrableOn f D)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ D → ∫ y, f y * dzbar ψ y = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ r > 0, ball z₀ r ⊆ D ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball z₀ r) ∧
      f =ᵐ[volume.restrict (ball z₀ r)] H := by
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.1 hD z₀ hz₀
  set r := R / 2 with hr
  have hr0 : 0 < r := half_pos hR
  have hCD : closedBall z₀ r ⊆ D := (closedBall_subset_ball (by linarith)).trans hRD
  have hUD : ball z₀ r ⊆ D := ball_subset_closedBall.trans hCD
  obtain ⟨δ, hδ, -, hev⟩ := LiZhongQC.lemma92_eventually hD (isCompact_closedBall z₀ r) hCD
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hballK : ∀ n ≥ N, ∀ z ∈ closedBall z₀ r,
      closedBall z (1 / ((n : ℝ) + 1)) ⊆ LiZhongQC.lemma92Exhaust D n := by
    intro n hn z hz y hy
    obtain ⟨hnδ, hnK⟩ := hN n hn
    exact hnK (mem_cthickening_of_dist_le y z δ _ hz ((mem_closedBall.1 hy).trans hnδ.le))
  set G : ℕ → ℂ → ℂ := fun k => LiZhongQC.lemma92Approx D f (N + k) with hG
  have hdiff : ∀ k, DifferentiableOn ℂ (G k) (ball z₀ r) := by
    intro k z hz
    refine (LiZhongQC.cauchyRiemann_iff.2 ⟨(gl11_contDiff_approx hf (N + k)).differentiable one_ne_zero z,
      gl11_dzbar_approx_eq_zero hf hweak (hballK (N + k) (Nat.le_add_right N k) z
        (ball_subset_closedBall hz))⟩).differentiableWithinAt
  -- the uniform `L¹` bound
  set M : ℝ≥0∞ := ∫⁻ x in D, ‖f x‖ₑ with hM
  have hMfin : M ≠ ⊤ := hf.hasFiniteIntegral.ne
  have hL1 : ∀ k, ∫⁻ x, ‖G k x‖ₑ ≤ M := by
    intro k
    refine (gl11_lintegral_conv_le _ (gl11_integrable_indicator hf (N + k))).trans ?_
    simp_rw [enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator (LiZhongQC.isCompact_lemma92Exhaust D (N + k)).measurableSet]
    exact lintegral_mono_set (LiZhongQC.lemma92Exhaust_subset D (N + k))
  have hbd : ∀ w ∈ ball z₀ r, ∃ s > 0, ball w s ⊆ ball z₀ r ∧ ∃ B : ℝ, ∀ k, ∀ w' ∈ ball w s, ‖G k w'‖ ≤ B := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    set s := (r - ‖w - z₀‖) / 3 with hs
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsub : ∀ w' ∈ ball w s, closedBall w' s ⊆ ball z₀ r := by
      intro w' hw' y hy
      rw [mem_ball, dist_eq_norm] at hw' ⊢
      rw [mem_closedBall, dist_eq_norm] at hy
      have h1 := norm_add_le (y - w') (w' - z₀)
      have h2 := norm_add_le (w' - w) (w - z₀)
      rw [sub_add_sub_cancel] at h1 h2
      linarith
    refine ⟨s, hs0, fun y hy => hsub w (mem_ball_self hs0) (ball_subset_closedBall hy),
      M.toReal / (π * s ^ 2), fun k w' hw' => ?_⟩
    have hmv := LiZhongQC.h36p_meanvalue (hdiff k) hs0 (hsub w' hw')
    have h1 : ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖G k w'‖ ≤ M := by
      refine hmv.trans ((setLIntegral_le_lintegral _ _).trans ?_)
      simp_rw [ofReal_norm]
      exact hL1 k
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_iff_le_toReal hMfin] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨φ, hφ, H, hH, hconv⟩ := LiZhongQC.h35_montel_loc isOpen_ball G hdiff hbd
  refine ⟨r, hr0, hUD, H, hH, ?_⟩
  -- `fₙ → f` a.e.
  have hgl : LocallyIntegrable (D.indicator f) volume :=
    (hf.integrable_indicator hD.measurableSet).locallyIntegrable
  have hrOut : Tendsto (fun n : ℕ => (LiZhongQC.lemma92Bump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ n : ℕ in atTop, (LiZhongQC.lemma92Bump n).rOut ≤ 2 * (LiZhongQC.lemma92Bump n).rIn := by
    refine Eventually.of_forall fun n => le_of_eq ?_
    show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
    field_simp
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrOut hratio hgl
  have heqconv : ∀ n ≥ N, ∀ x ∈ ball z₀ r, LiZhongQC.lemma92Approx D f n x =
      convolution ((LiZhongQC.lemma92Bump n).normed volume) (D.indicator f) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume x := by
    intro n hn x hx
    unfold LiZhongQC.lemma92Approx
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : (LiZhongQC.lemma92Bump n).normed volume t = 0
    · simp [ht]
    · have htn : ‖t‖ < 1 / ((n : ℝ) + 1) := by
        by_contra h
        exact ht (LiZhongQC.lemma92Bump_normed_eq_zero (not_lt.1 h))
      have hxt : x - t ∈ LiZhongQC.lemma92Exhaust D n := by
        refine hballK n hn x (ball_subset_closedBall hx) ?_
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact htn.le
      show (ContinuousLinearMap.lsmul ℝ ℝ) _ _ = (ContinuousLinearMap.lsmul ℝ ℝ) _ _
      rw [indicator_of_mem hxt, indicator_of_mem (LiZhongQC.lemma92Exhaust_subset D n hxt)]
  have hsubseq : Tendsto (fun k => N + φ k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left (φ k) N) hφ.tendsto_atTop
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae] with x hx hxlim
  have h1 : Tendsto (fun k => G (φ k) x) atTop (𝓝 (D.indicator f x)) := by
    refine (hxlim.comp hsubseq).congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp, hG]
    exact (heqconv (N + φ k) (Nat.le_add_right N _) x hx).symm
  rw [indicator_of_mem (hUD hx)] at h1
  exact tendsto_nhds_unique h1 (hconv.tendsto_at hx)

/-- **Theorem 2** (Weyl's lemma, §11.3, l. 8443). If `f` is an `L₁`-function in a domain `D` with `f_z̄ ≡ 0` in the
sense of distributions, there is a function holomorphic in `D` equal to `f` almost everywhere. -/
theorem thm11_2 {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {f : ℂ → ℂ} (hf : IntegrableOn f D)
    (hdist : HasDistribDzbar f 0 D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g D ∧ f =ᵐ[volume.restrict D] g := by
  -- connectedness of `D` is not needed (the statement is local)
  have _ := hDc
  have hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ y, f y * dzbar ψ y = 0 := by
    intro ψ h1 h2 h3
    have h := hdist.2.2 ψ h1 h2 h3
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h
    exact neg_eq_zero.1 h.symm
  have hloc : ∀ z ∈ D, ∃ r > 0, ball z r ⊆ D ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball z r) ∧
      f =ᵐ[volume.restrict (ball z r)] H := fun z hz => gl11_local hD hf hweak hz
  choose! r hr hrD H hH hHae using hloc
  -- two local representatives agree on the overlap of their discs
  have hagree : ∀ z ∈ D, ∀ w ∈ D, EqOn (H z) (H w) (ball z (r z) ∩ ball w (r w)) := by
    intro z hz w hw
    have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left (t := ball w (r w))) (hHae z hz)
    have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_right (s := ball z (r z))) (hHae w hw)
    exact Measure.eqOn_open_of_ae_eq (h1.mp (h2.mono fun x hx2 hx1 => hx1.symm.trans hx2))
      (isOpen_ball.inter isOpen_ball)
      ((hH z hz).continuousOn.mono inter_subset_left) ((hH w hw).continuousOn.mono inter_subset_right)
  have hloc_eq : ∀ z ∈ D, ∀ w ∈ ball z (r z), H w w = H z w := by
    intro z hz w hw
    exact (hagree z hz w (hrD z hz hw) ⟨hw, mem_ball_self (hr w (hrD z hz hw))⟩).symm
  refine ⟨fun w => H w w, fun z hz => ?_, ?_⟩
  · have hev : (fun w => H w w) =ᶠ[𝓝 z] H z :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr z hz))) (hloc_eq z hz)
    exact (((hH z hz) z (mem_ball_self (hr z hz))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq hev |>.differentiableWithinAt
  · obtain ⟨T, hTD, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable D (fun z => ball z (r z))
      fun z _ => isOpen_ball
    have hDU : D = ⋃ z ∈ T, ball z (r z) := by
      rw [hTU]
      refine Subset.antisymm (fun z hz => mem_biUnion hz (mem_ball_self (hr z hz))) ?_
      exact iUnion₂_subset fun z hz => hrD z hz
    rw [hDU]
    refine (ae_restrict_biUnion_iff _ hTc _).2 fun z hz => ?_
    filter_upwards [hHae z (hTD hz), ae_restrict_mem measurableSet_ball] with w hw hwb
    show f w = H w w
    rw [hw, hloc_eq z (hTD hz) w hwb]

/-- Helper for **Corollary 1** (§11.3). The integral of `|φ|` over one chart target is at most the norm of an
`L₁`-quadratic differential (a chart partition whose first piece is the chart source, and the partition independence
`gl31_surfaceIntegral_eq_tsum_ae` for the a.e. law). -/
theorem gl113_chart_integral_le {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R) (x : R) :
    ∫⁻ z in (chartAt ℂ x).target, ENNReal.ofReal ‖φ x z‖ ≤ LiZhongQC.quadDiffNorm φ := by
  classical
  rcases eq_or_ne (LiZhongQC.quadDiffNorm φ) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  obtain ⟨x', P, hP⟩ := gl31_exists_partition_of_ne_top hne
  -- the partition `Q`: the source of the chart at `x` first, then the pieces of `P` with that source removed
  have hQP : LiZhongQC.IsChartPartition R (fun i => Nat.casesOn (motive := fun _ => R) i x x')
      (fun i => Nat.casesOn (motive := fun _ => Set R) i (chartAt ℂ x).source
        fun j => P j \ (chartAt ℂ x).source) := by
    refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
    · rcases i with _ | j
      · exact ⟨subset_rfl, by
          show MeasurableSet (chartAt ℂ x '' (chartAt ℂ x).source)
          rw [(chartAt ℂ x).image_source_eq_target]
          exact (chartAt ℂ x).open_target.measurableSet⟩
      · refine ⟨sdiff_subset.trans (hP.1 j).1, ?_⟩
        show MeasurableSet (chartAt ℂ (x' j) '' (P j \ (chartAt ℂ x).source))
        have heq : chartAt ℂ (x' j) '' (P j \ (chartAt ℂ x).source) = chartAt ℂ (x' j) '' P j \
            ((chartAt ℂ (x' j)).target ∩ (chartAt ℂ (x' j)).symm ⁻¹' (chartAt ℂ x).source) := by
          ext z
          constructor
          · rintro ⟨q, ⟨hq, hqy⟩, rfl⟩
            refine ⟨⟨q, hq, rfl⟩, fun hz => hqy ?_⟩
            have h2 := hz.2
            rwa [mem_preimage, (chartAt ℂ (x' j)).left_inv ((hP.1 j).1 hq)] at h2
          · rintro ⟨⟨q, hq, rfl⟩, hz⟩
            refine ⟨q, ⟨hq, fun hqy => hz ⟨(chartAt ℂ (x' j)).map_source ((hP.1 j).1 hq), ?_⟩⟩, rfl⟩
            rw [mem_preimage, (chartAt ℂ (x' j)).left_inv ((hP.1 j).1 hq)]
            exact hqy
        rw [heq]
        exact (hP.1 j).2.diff ((chartAt ℂ (x' j)).isOpen_inter_preimage_symm
          (chartAt ℂ x).open_source).measurableSet
    · rcases i with _ | i <;> rcases j with _ | j
      · exact absurd rfl hij
      · exact Set.disjoint_left.2 fun q hq hq' => hq'.2 hq
      · exact Set.disjoint_left.2 fun q hq hq' => hq.2 hq'
      · exact (hP.2.1 fun h => hij (by rw [h])).mono sdiff_subset sdiff_subset
    · refine eq_univ_of_forall fun q => ?_
      by_cases hq : q ∈ (chartAt ℂ x).source
      · exact mem_iUnion.2 ⟨0, hq⟩
      · have hq' : q ∈ ⋃ j, P j := by
          rw [hP.2.2]
          exact mem_univ q
        obtain ⟨j, hj⟩ := mem_iUnion.1 hq'
        exact mem_iUnion.2 ⟨j + 1, hj, hq⟩
  rw [gl31_surfaceIntegral_eq_tsum_ae hφ.1 hQP]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
  show ∫⁻ z in (chartAt ℂ x).target, ENNReal.ofReal ‖φ x z‖ =
    ∫⁻ z in chartAt ℂ x '' (chartAt ℂ x).source, ENNReal.ofReal ‖φ x z‖
  rw [(chartAt ℂ x).image_source_eq_target]

/-- Helper for **Corollary 1** (§11.3). Weyl's lemma in the preferred chart at every point: where `φ_p` is a weak
solution of `∂̄ f = 0` on a neighbourhood `N` of the chart point of `p`, a small disc `B ⊆ N` carries a holomorphic
function equal to `φ_p` almost everywhere (`thm11_2` on `B`, with `φ_p` integrable on `B` by
`gl113_chart_integral_le`). -/
theorem gl113_local_rep {R : Type u} [TopologicalSpace R] [T2Space R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R)
    (hloc : ∀ p : R, ∃ N : Set ℂ, IsOpen N ∧ chartAt ℂ p p ∈ N ∧ N ⊆ (chartAt ℂ p).target ∧
      HasDistribDzbar (φ p) 0 N) :
    ∀ p : R, ∃ r > (0 : ℝ), ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (chartAt ℂ p p) r) ∧ φ p =ᵐ[volume.restrict (ball (chartAt ℂ p p) r)] H := by
  intro p
  obtain ⟨N, hNo, hcN, hNt, hdist⟩ := hloc p
  obtain ⟨r, hr, hrN⟩ := Metric.isOpen_iff.1 hNo _ hcN
  refine ⟨r, hr, (hrN.trans hNt), ?_⟩
  have hBt : ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target := hrN.trans hNt
  have hmeas : AEStronglyMeasurable (φ p) (volume.restrict (ball (chartAt ℂ p p) r)) :=
    (hφ.2.1 p).mono_measure (Measure.restrict_mono hBt le_rfl)
  have hint : IntegrableOn (φ p) (ball (chartAt ℂ p p) r) := by
    refine ⟨hmeas, ?_⟩
    show ∫⁻ z in ball (chartAt ℂ p p) r, ‖φ p z‖ₑ < ⊤
    calc ∫⁻ z in ball (chartAt ℂ p p) r, ‖φ p z‖ₑ
        ≤ ∫⁻ z in (chartAt ℂ p).target, ‖φ p z‖ₑ := lintegral_mono_set hBt
      _ = ∫⁻ z in (chartAt ℂ p).target, ENNReal.ofReal ‖φ p z‖ := by simp only [ofReal_norm]
      _ ≤ LiZhongQC.quadDiffNorm φ := gl113_chart_integral_le hφ p
      _ < ⊤ := hφ.2.2
  have hdistB : HasDistribDzbar (φ p) 0 (ball (chartAt ℂ p p) r) :=
    ⟨hdist.1.mono_set hrN, hdist.2.1.mono_set hrN, fun ψ h1 h2 h3 => hdist.2.2 ψ h1 h2 (h3.trans hrN)⟩
  obtain ⟨g, hg, hae⟩ := thm11_2 isOpen_ball ((convex_ball _ r).isConnected ⟨_, mem_ball_self hr⟩) hint hdistB
  exact ⟨g, hg, hae⟩

/-- Helper for `gl113_glue` (§11.3). The cocycle of chart transitions and its derivative: near `z`,
`τ_{qy} = τ_{qx} ∘ τ_{xy}`, so `τ_{qy}′(z) = τ_{qx}′(τ_{xy} z) τ_{xy}′(z)`. -/
theorem gl113_cocycle {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R] (q x y : R)
    {z : ℂ} (hz : z ∈ (chartAt ℂ y).target) (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source)
    (hzq : (chartAt ℂ y).symm z ∈ (chartAt ℂ q).source) :
    deriv (LiZhongQC.chartTransition q y) z = deriv (LiZhongQC.chartTransition q x)
      (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z := by
  have hxy : DifferentiableAt ℂ (LiZhongQC.chartTransition x y) z :=
    LiZhongQC.s23_transition_differentiableAt x y hz hzx
  have hu : LiZhongQC.chartTransition x y z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hzx
  have hs : (chartAt ℂ x).symm (LiZhongQC.chartTransition x y z) = (chartAt ℂ y).symm z :=
    (chartAt ℂ x).left_inv hzx
  have hqx : DifferentiableAt ℂ (LiZhongQC.chartTransition q x) (LiZhongQC.chartTransition x y z) :=
    LiZhongQC.s23_transition_differentiableAt q x hu (hs ▸ hzq)
  have hO : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' ((chartAt ℂ x).source ∩ (chartAt ℂ q).source) ∈ 𝓝 z :=
    (((chartAt ℂ y).isOpen_inter_preimage_symm ((chartAt ℂ x).open_source.inter (chartAt ℂ q).open_source)).mem_nhds
      ⟨hz, hzx, hzq⟩)
  have hev : LiZhongQC.chartTransition q y =ᶠ[𝓝 z]
      (LiZhongQC.chartTransition q x) ∘ (LiZhongQC.chartTransition x y) := by
    filter_upwards [hO] with w hw
    have hl : (chartAt ℂ x).symm (LiZhongQC.chartTransition x y w) = (chartAt ℂ y).symm w :=
      (chartAt ℂ x).left_inv hw.2.1
    show chartAt ℂ q ((chartAt ℂ y).symm w) = chartAt ℂ q ((chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm w)))
    rw [(chartAt ℂ x).left_inv hw.2.1]
  rw [hev.deriv_eq]
  exact deriv_comp z hqx hxy

/-- Helper for `gl113_glue` (§11.3). The transition `τ_{qy}` pulls null sets back to null sets on its domain: it has the
holomorphic inverse `τ_{yq}`, which maps null sets to null sets. -/
theorem gl113_null_preimage {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R] (q y : R)
    {N : Set ℂ} (hN : volume N = 0) :
    volume ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ q).source ∩
      (LiZhongQC.chartTransition q y) ⁻¹' N) = 0 := by
  refine measure_mono_null (t := (LiZhongQC.chartTransition y q) ''
    (N ∩ ((chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' (chartAt ℂ y).source))) ?_ ?_
  · rintro w ⟨⟨hw, hws⟩, hwN⟩
    have hmem : LiZhongQC.chartTransition q y w ∈ (chartAt ℂ q).target := (chartAt ℂ q).map_source hws
    have hl : (chartAt ℂ q).symm (LiZhongQC.chartTransition q y w) = (chartAt ℂ y).symm w :=
      (chartAt ℂ q).left_inv hws
    refine ⟨LiZhongQC.chartTransition q y w, ⟨hwN, hmem, ?_⟩, ?_⟩
    · rw [mem_preimage, hl]
      exact (chartAt ℂ y).map_target hw
    · show chartAt ℂ y ((chartAt ℂ q).symm (LiZhongQC.chartTransition q y w)) = w
      rw [hl]
      exact (chartAt ℂ y).right_inv hw
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun u hu => ?_) ?_
    · exact (LiZhongQC.s23_transition_differentiableAt y q hu.2.1 hu.2.2).restrictScalars ℝ |>.differentiableWithinAt
    · exact measure_mono_null inter_subset_left hN

/-- Helper for `gl113_glue` (§11.3). Consistency of two local holomorphic representatives: if `H₁`, `H₂` are a.e. equal
to `φ_{p₁}`, `φ_{p₂}` on discs around the chart points, then at a point `u` of the first disc whose transition image
lies in the second disc, `H₁ u = H₂(τ u) τ′(u)²` (both sides are holomorphic and a.e. equal near `u` by the a.e. law
of `φ`, the null-set preimage `gl113_null_preimage`, and the identity theorem for continuous functions). -/
theorem gl113_consistency {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R) {p₁ p₂ : R} {r₁ r₂ : ℝ}
    (hr₁ : ball (chartAt ℂ p₁ p₁) r₁ ⊆ (chartAt ℂ p₁).target)
    {H₁ H₂ : ℂ → ℂ} (hH₁ : DifferentiableOn ℂ H₁ (ball (chartAt ℂ p₁ p₁) r₁))
    (hH₂ : DifferentiableOn ℂ H₂ (ball (chartAt ℂ p₂ p₂) r₂))
    (hae₁ : φ p₁ =ᵐ[volume.restrict (ball (chartAt ℂ p₁ p₁) r₁)] H₁)
    (hae₂ : φ p₂ =ᵐ[volume.restrict (ball (chartAt ℂ p₂ p₂) r₂)] H₂)
    {u : ℂ} (hu : u ∈ ball (chartAt ℂ p₁ p₁) r₁) (hs : (chartAt ℂ p₁).symm u ∈ (chartAt ℂ p₂).source)
    (hv : LiZhongQC.chartTransition p₂ p₁ u ∈ ball (chartAt ℂ p₂ p₂) r₂) :
    H₁ u = H₂ (LiZhongQC.chartTransition p₂ p₁ u) * deriv (LiZhongQC.chartTransition p₂ p₁) u ^ 2 := by
  classical
  set τ := LiZhongQC.chartTransition p₂ p₁ with hτ
  set D : Set ℂ := (chartAt ℂ p₁).target ∩ (chartAt ℂ p₁).symm ⁻¹' (chartAt ℂ p₂).source with hD
  have hDo : IsOpen D := (chartAt ℂ p₁).isOpen_inter_preimage_symm (chartAt ℂ p₂).open_source
  have hτD : DifferentiableOn ℂ τ D := fun w hw =>
    (LiZhongQC.s23_transition_differentiableAt p₂ p₁ hw.1 hw.2).differentiableWithinAt
  have hdτ : DifferentiableOn ℂ (deriv τ) D :=
    ((hτD.analyticOnNhd hDo).deriv_of_isOpen hDo).differentiableOn
  set W : Set ℂ := (D ∩ τ ⁻¹' ball (chartAt ℂ p₂ p₂) r₂) ∩ ball (chartAt ℂ p₁ p₁) r₁ with hW
  have hWo : IsOpen W := (hτD.continuousOn.isOpen_inter_preimage hDo isOpen_ball).inter isOpen_ball
  have huW : u ∈ W := ⟨⟨⟨hr₁ hu, hs⟩, hv⟩, hu⟩
  have hWD : W ⊆ D := fun w hw => by exact hw.1.1
  set B : ℂ → ℂ := fun w => H₂ (τ w) * deriv τ w ^ 2 with hB
  have hBd : DifferentiableOn ℂ B W := by
    refine DifferentiableOn.mul ?_ ((hdτ.mono hWD).pow 2)
    exact hH₂.comp (hτD.mono hWD) fun w hw => by exact hw.1.2
  -- a.e. equality on `W`
  have hM : volume {v : ℂ | v ∈ ball (chartAt ℂ p₂ p₂) r₂ ∧ φ p₂ v ≠ H₂ v} = 0 := by
    have := (ae_restrict_iff' measurableSet_ball).1 hae₂
    rw [ae_iff] at this
    refine measure_mono_null (fun v hv => ?_) this
    exact fun h => hv.2 (h hv.1)
  have hnull := gl113_null_preimage p₂ p₁ hM
  have h3 : ∀ᵐ w ∂(volume.restrict W), φ p₂ (τ w) = H₂ (τ w) := by
    refine (ae_restrict_iff' hWo.measurableSet).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with w hw hwW
    by_contra hne
    exact hw ⟨⟨hwW.1.1.1, hwW.1.1.2⟩, ⟨hwW.1.2, hne⟩⟩
  have h1 : H₁ =ᵐ[volume.restrict W] φ p₁ :=
    (ae_restrict_of_ae_restrict_of_subset (fun w hw => by exact hw.2) hae₁).mono fun w hw => hw.symm
  have h2 : ∀ᵐ w ∂(volume.restrict W), φ p₁ w = φ p₂ (τ w) * deriv τ w ^ (2 : ℤ) * conj (deriv τ w) ^ (0 : ℤ) :=
    ae_restrict_of_ae_restrict_of_subset hWD (hφ.1 p₂ p₁)
  have hab : H₁ =ᵐ[volume.restrict W] B := by
    filter_upwards [h1, h2, h3] with w e1 e2 e3
    rw [e1, e2, e3]
    simp [hB]
  have heq := Measure.eqOn_open_of_ae_eq hab hWo (hH₁.continuousOn.mono fun w hw => by exact hw.2) hBd.continuousOn
  exact heq huW

/-- Helper for **Corollary 1** (§11.3). Gluing: if the coefficient of an `L₁`-quadratic differential in the preferred
chart at every point is almost everywhere equal to a holomorphic function on a disc around the chart point, then the
differential is almost everywhere equal to a holomorphic one. Define `ψ_y(z) = H_q(c_q) · τ′(z)²` with `q = φ_y⁻¹(z)`,
`τ = φ_q ∘ φ_y⁻¹` (the representative at the point's own chart), check that it obeys the exact law (the cocycle
`τ_{qy} = τ_{qx} ∘ τ_{xy}`), is holomorphic (representatives agree on overlaps by continuity, a.e. equality being
transported through the holomorphic transitions, `gl31_null_preimage`) and equals `φ_y` a.e. (countable cover of the
target, Lindelöf). -/
theorem gl113_glue {R : Type u} [TopologicalSpace R] [T2Space R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R)
    (hrep : ∀ p : R, ∃ r > (0 : ℝ), ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (chartAt ℂ p p) r) ∧ φ p =ᵐ[volume.restrict (ball (chartAt ℂ p p) r)] H) :
    ∃ ψ ∈ holQuadDiffSubmodule R, ∀ x : R, φ x =ᵐ[volume.restrict (chartAt ℂ x).target] ψ x := by
  classical
  choose r hr hrt H hH hae using hrep
  set ψ : R → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator fun z =>
    H ((chartAt ℂ y).symm z) (chartAt ℂ ((chartAt ℂ y).symm z) ((chartAt ℂ y).symm z)) *
      deriv (LiZhongQC.chartTransition ((chartAt ℂ y).symm z) y) z ^ 2 with hψ
  have hψt : ∀ y z, z ∈ (chartAt ℂ y).target → ψ y z =
      H ((chartAt ℂ y).symm z) (chartAt ℂ ((chartAt ℂ y).symm z) ((chartAt ℂ y).symm z)) *
        deriv (LiZhongQC.chartTransition ((chartAt ℂ y).symm z) y) z ^ 2 := fun y z hz =>
    indicator_of_mem hz _
  -- the local form of `ψ` and of `φ` near a point of a chart target
  have hlocal : ∀ y : R, ∀ z0 ∈ (chartAt ℂ y).target, ∃ U : Set ℂ, ∃ F : ℂ → ℂ, IsOpen U ∧ z0 ∈ U ∧
      U ⊆ (chartAt ℂ y).target ∧ DifferentiableOn ℂ F U ∧ (∀ w ∈ U, ψ y w = F w) ∧
      φ y =ᵐ[volume.restrict U] F := by
    intro y z0 hz0
    set q0 : R := (chartAt ℂ y).symm z0 with hq0
    set τ := LiZhongQC.chartTransition q0 y with hτ
    set D : Set ℂ := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ q0).source with hD
    have hDo : IsOpen D := (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ q0).open_source
    have hq0s : q0 ∈ (chartAt ℂ q0).source := mem_chart_source ℂ q0
    have hτD : DifferentiableOn ℂ τ D := fun w hw =>
      (LiZhongQC.s23_transition_differentiableAt q0 y hw.1 hw.2).differentiableWithinAt
    have hdτ : DifferentiableOn ℂ (deriv τ) D :=
      ((hτD.analyticOnNhd hDo).deriv_of_isOpen hDo).differentiableOn
    set U : Set ℂ := D ∩ τ ⁻¹' ball (chartAt ℂ q0 q0) (r q0) with hU
    have hUo : IsOpen U := hτD.continuousOn.isOpen_inter_preimage hDo isOpen_ball
    have hτz0 : τ z0 = chartAt ℂ q0 q0 := rfl
    have hz0U : z0 ∈ U := ⟨⟨hz0, hq0s⟩, by rw [mem_preimage, hτz0]; exact mem_ball_self (hr q0)⟩
    set F : ℂ → ℂ := fun w => H q0 (τ w) * deriv τ w ^ 2 with hF
    have hUD : U ⊆ D := fun w hw => by exact hw.1
    have hFd : DifferentiableOn ℂ F U := by
      refine DifferentiableOn.mul ?_ ((hdτ.mono hUD).pow 2)
      exact (hH q0).comp (hτD.mono hUD) fun w hw => by exact hw.2
    refine ⟨U, F, hUo, hz0U, fun w hw => by exact hw.1.1, hFd, ?_, ?_⟩
    · intro w hw
      have hwt : w ∈ (chartAt ℂ y).target := hw.1.1
      set q : R := (chartAt ℂ y).symm w with hq
      have hqsrc : q ∈ (chartAt ℂ q0).source := hw.1.2
      have hqq : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
      have hs : (chartAt ℂ q).symm (chartAt ℂ q q) ∈ (chartAt ℂ q0).source := by
        rw [(chartAt ℂ q).left_inv hqq]
        exact hqsrc
      have e : LiZhongQC.chartTransition q0 q (chartAt ℂ q q) = τ w := by
        show chartAt ℂ q0 ((chartAt ℂ q).symm (chartAt ℂ q q)) = chartAt ℂ q0 ((chartAt ℂ y).symm w)
        rw [(chartAt ℂ q).left_inv hqq]
      have hv : LiZhongQC.chartTransition q0 q (chartAt ℂ q q) ∈ ball (chartAt ℂ q0 q0) (r q0) := by
        rw [e]
        exact hw.2
      have hCL := gl113_consistency hφ (hrt q) (hH q) (hH q0) (hae q) (hae q0) (mem_ball_self (hr q)) hs hv
      have hcoc : deriv τ w = deriv (LiZhongQC.chartTransition q0 q) (chartAt ℂ q q) *
          deriv (LiZhongQC.chartTransition q y) w :=
        gl113_cocycle q0 q y hwt hqq hqsrc
      rw [hψt y w hwt]
      show H q (chartAt ℂ q q) * deriv (LiZhongQC.chartTransition q y) w ^ 2 = H q0 (τ w) * deriv τ w ^ 2
      rw [hCL, e, hcoc]
      ring
    · have hM : volume {v : ℂ | v ∈ ball (chartAt ℂ q0 q0) (r q0) ∧ φ q0 v ≠ H q0 v} = 0 := by
        have := (ae_restrict_iff' measurableSet_ball).1 (hae q0)
        rw [ae_iff] at this
        refine measure_mono_null (fun v hv => ?_) this
        exact fun h => hv.2 (h hv.1)
      have hnull := gl113_null_preimage q0 y hM
      have h3 : ∀ᵐ w ∂(volume.restrict U), φ q0 (τ w) = H q0 (τ w) := by
        refine (ae_restrict_iff' hUo.measurableSet).2 ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with w hw hwU
        by_contra hne
        exact hw ⟨⟨hwU.1.1, hwU.1.2⟩, ⟨hwU.2, hne⟩⟩
      have h2 : ∀ᵐ w ∂(volume.restrict U), φ y w = φ q0 (τ w) * deriv τ w ^ (2 : ℤ) *
          conj (deriv τ w) ^ (0 : ℤ) := ae_restrict_of_ae_restrict_of_subset hUD (hφ.1 q0 y)
      filter_upwards [h2, h3] with w e2 e3
      rw [e2, e3]
      simp [hF]
  have hlaw : LiZhongQC.IsDiffFamily 2 0 ψ := by
    refine ⟨fun x z hz => indicator_of_notMem hz _, fun x y z hz hzs => ?_⟩
    have hTz : LiZhongQC.chartTransition x y z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hzs
    have hs : (chartAt ℂ x).symm (LiZhongQC.chartTransition x y z) = (chartAt ℂ y).symm z :=
      (chartAt ℂ x).left_inv hzs
    have hcoc := gl113_cocycle ((chartAt ℂ y).symm z) x y hz hzs (mem_chart_source ℂ _)
    rw [hψt y z hz, hψt x _ hTz, hs, hcoc, zpow_zero, mul_one, zpow_two]
    ring
  refine ⟨ψ, ⟨hlaw, fun y z0 hz0 => ?_⟩, fun x => ?_⟩
  · obtain ⟨U, F, hUo, hz0U, hUt, hFd, hψF, -⟩ := hlocal y z0 hz0
    have hev : ψ y =ᶠ[𝓝 z0] F := Filter.eventuallyEq_of_mem (hUo.mem_nhds hz0U) hψF
    exact (((hFd z0 hz0U).differentiableAt (hUo.mem_nhds hz0U)).congr_of_eventuallyEq hev).differentiableWithinAt
  · have hloc' : ∀ z0 ∈ (chartAt ℂ x).target, ∃ U : Set ℂ, IsOpen U ∧ z0 ∈ U ∧ U ⊆ (chartAt ℂ x).target ∧
        φ x =ᵐ[volume.restrict U] ψ x := by
      intro z0 hz0
      obtain ⟨U, F, hUo, hz0U, hUt, hFd, hψF, hae'⟩ := hlocal x z0 hz0
      refine ⟨U, hUo, hz0U, hUt, ?_⟩
      refine (ae_restrict_iff' hUo.measurableSet).2 ?_
      filter_upwards [(ae_restrict_iff' hUo.measurableSet).1 hae'] with w hw hwU
      exact (hw hwU).trans (hψF w hwU).symm
    choose! U hU using hloc'
    obtain ⟨T, hTs, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (chartAt ℂ x).target U
      (fun z hz => (hU z hz).1)
    have hcov : (chartAt ℂ x).target = ⋃ z ∈ T, U z := by
      rw [hTU]
      exact Subset.antisymm (fun z hz => mem_biUnion hz (hU z hz).2.1)
        (iUnion₂_subset fun z hz => (hU z hz).2.2.1)
    rw [hcov]
    exact (ae_restrict_biUnion_iff _ hTc _).2 fun z hz => (hU z (hTs hz)).2.2.2

/-- **Corollary 1** (§11.3, l. 8445). Let `φ` be an `L₁`-quadratic differential on `R` such that every point has a
coordinate neighbourhood `N` with `∬ φ g_z̄ = 0` for all `C¹` functions `g` with compact support in `z(N)` (11.9).
Then `φ` is equal almost everywhere to a holomorphic quadratic differential. -/
theorem cor11_2_1 {R : Type u} [TopologicalSpace R] [T2Space R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R)
    (hloc : ∀ p : R, ∃ N : Set ℂ, IsOpen N ∧ chartAt ℂ p p ∈ N ∧ N ⊆ (chartAt ℂ p).target ∧
      HasDistribDzbar (φ p) 0 N) :
    ∃ ψ ∈ holQuadDiffSubmodule R, ∀ x : R, φ x =ᵐ[volume.restrict (chartAt ℂ x).target] ψ x := by
  exact gl113_glue hφ (gl113_local_rep hφ hloc)

end GardinerLakic2000
