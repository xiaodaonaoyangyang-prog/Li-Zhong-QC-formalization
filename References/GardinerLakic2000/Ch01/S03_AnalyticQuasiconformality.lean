import References.GardinerLakic2000.Ch01.S02_LinearQuasiconformality

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.3 Analytic quasiconformality

Source `teichmuller.txt`, lines 550–676 (Chapter 1, §1.3).

* Definition (complex partial derivatives `f_z`, `f_z̄`, l. 575) — exists: `LiZhongQC.dz` `LiZhongQC.dzbar`
* Definition 1 (distributional partial derivatives, locally integrable, l. 593–601) — `HasDistribPartials`
* Definition 2 (analytic definition of `K`-quasiconformality, l. 603–607) — `IsKQCAnalytic`
* Definition (`K(f)`, the least `K`, l. 607) — exists: `LiZhongQC.maxDilatation` (ess sup of the pointwise
  dilatation, the same number)
* Remark (complex dilatation `μ = f_z̄/f_z` and pointwise dilatation `K_z(f)`, l. 609) — exists:
  `LiZhongQC.complexDilatation` `LiZhongQC.dilatationQuotient`
* Proposition 1 (l. 613) — `prop1_1_a`, `prop1_1_b`, `prop1_1_c`
* Definition 3 (ACL, l. 634) — exists: `LiZhongQC.IsACL` (absolutely continuous on almost every horizontal and
  vertical segment of every closed rectangle in the domain)
* Proposition 2 (l. 636) — `prop1_2`

Not items: the Remark at l. 611 (quasiconformal maps are differentiable a.e.; not cited, U−; it is Li Zhong's
Theorem 9.3). Modelling: Definition 1 is stated with test functions as printed, so the project's
`LiZhongQC.HasGenPartials` (Li Zhong's Definition 9.2, by smooth approximation) is a near miss, and Proposition 2 is
new (near miss `LiZhongQC.lemma9_2_isACL_of_genPartials`). In Proposition 2 `f` is continuous [reading]: the proof uses
it (l. 661), and ACL needs a continuous representative.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsHomeomorphOnto IsConformalOnto IsACL maxDilatation)

/-- **Definition 1** (§1.3, l. 593–601). `g` and `h` are the distributional partial derivatives `u_x`, `u_y` of `u` on
the open set `Ω`, and they are locally integrable: `∬ u φ_x = −∬ g φ` and `∬ u φ_y = −∬ h φ` for every `C^∞` test
function `φ` with compact support in `Ω`. Local integrability of `u` itself is part of the reading (the integrals on
the left must make sense). -/
def HasDistribPartials (u g h : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  (∀ C ⊆ Ω, IsCompact C → IntegrableOn u C ∧ IntegrableOn g C ∧ IntegrableOn h C) ∧
    ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ z, u z * fderiv ℝ φ z 1) = -∫ z, g z * φ z ∧ (∫ z, u z * fderiv ℝ φ z I) = -∫ z, h z * φ z

/-- **Definition 2** (analytic definition, §1.3, l. 603–607). A homeomorphism `f` of the plane domain `Ω` onto the
plane domain `f(Ω)` is `K`-quasiconformal (`K ≥ 1`, `k = (K − 1)/(K + 1)`) if (i) it has locally integrable
distributional derivatives, and (ii) `|f_z̄| ≤ k |f_z|` almost everywhere, where `f_z = (f_x − i f_y)/2` and
`f_z̄ = (f_x + i f_y)/2` are formed from the distributional derivatives. -/
def IsKQCAnalytic (f : ℂ → ℂ) (Ω : Set ℂ) (K : ℝ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ 1 ≤ K ∧ IsHomeomorphOnto f Ω (f '' Ω) ∧ IsOpen (f '' Ω) ∧
    ∃ g h : ℂ → ℂ, HasDistribPartials f g h Ω ∧
      ∀ᵐ z ∂(volume.restrict Ω), ‖(g z + I * h z) / 2‖ ≤ (K - 1) / (K + 1) * ‖(g z - I * h z) / 2‖

open LiZhongQC in
/-- Auxiliary: `u * v` is integrable when `u` is integrable on the (compact) support of `φ` and
`v` is continuous and vanishes off it. -/
theorem p11a_integrable_of_support {u v : ℂ → ℂ} {φ : ℂ → ℂ}
    (hu : IntegrableOn u (tsupport φ)) (hcφ : HasCompactSupport φ)
    (hv0 : ∀ z ∉ tsupport φ, v z = 0) (hv : Continuous v) :
    Integrable fun z => u z * v z :=
  sp_ibp_integrable_of_support (isClosed_tsupport φ).measurableSet
    (hu.mul_continuousOn hv.continuousOn hcφ.isCompact)
    (fun z hz => by rw [hv0 z hz, mul_zero])

open LiZhongQC in
/-- Auxiliary: `u * v` integrable variant with `u` only continuous on `Ω ⊇ tsupport φ`. -/
theorem p11a_integrable_of_support' {u v : ℂ → ℂ} {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hu : ContinuousOn u Ω) (hsφ : tsupport φ ⊆ Ω) (hcφ : HasCompactSupport φ)
    (hv0 : ∀ z ∉ tsupport φ, v z = 0) (hv : Continuous v) :
    Integrable fun z => u z * v z :=
  sp_ibp_integrable_of_support (isClosed_tsupport φ).measurableSet
    (((hu.mono hsφ).mul hv.continuousOn).integrableOn_compact hcφ.isCompact)
    (fun z hz => by rw [hv0 z hz, mul_zero])

open LiZhongQC in
/-- The mollifier step of Weyl's lemma with `C∞` test functions
(`LiZhongQC.sp_w_dzbar_approx_eq_zero` with the weaker hypothesis). -/
theorem p11a_dzbar_approx_eq_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ w in U, F w * dzbar ψ w = 0) {n : ℕ} {z : ℂ}
    (hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n) :
    dzbar (lemma92Approx U F n) z = 0 := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ,
      ψ = fun y : ℂ => ((((lemma92Bump n).normed volume) (z - y) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hρD : Differentiable ℝ ((lemma92Bump n).normed volume) :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hshift : ContDiff ℝ 1 (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hshifto : ContDiff ℝ ∞ (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hψ1 : ContDiff ℝ 1 ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1))).comp hshift
  have hψo : ContDiff ℝ ∞ ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))).comp hshifto
  have hψder : ∀ y v : ℂ, fderiv ℝ ψ y v
      = -((fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v : ℝ) : ℂ) := by
    rw [hψdef]
    exact sp_w_fderiv_shift hρD z
  have hψ0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, not_le] at hy
    have h : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hy.le
    rw [hψdef]
    simp [lemma92Bump_normed_eq_zero h]
  have hcψ : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall z _) hψ0
  have hsψ : tsupport ψ ⊆ closedBall z (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hψ0 y h)
  have hballU : closedBall z (1 / ((n : ℝ) + 1)) ⊆ U := hball.trans (lemma92Exhaust_subset U n)
  have hdz0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), dzbar ψ y = 0 := by
    intro y hy
    have h : y ∉ tsupport ψ := fun h' => hy (hsψ h')
    show (fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 = 0
    rw [sp_fderiv_eq_zero_of_notMem_tsupport h 1, sp_fderiv_eq_zero_of_notMem_tsupport h I]
    ring
  have hw : ∫ y, F y * dzbar ψ y = 0 := by
    rw [← sp_setIntegral_eq_integral (h := fun y => F y * dzbar ψ y) hU.measurableSet hballU
      fun y hy => by rw [hdz0 y hy, mul_zero]]
    exact hweak ψ hψo hcψ (hsψ.trans hballU)
  have hderaux : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = ∫ y, fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [fderiv_lemma92Approx_apply hF n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y) volume z]
    simp
  have hder : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = -∫ y, fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [hderaux v, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
      (lemma92Exhaust U n).indicator F y = -(fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y)
    rw [Complex.real_smul, ← neg_mul]
    congr 1
    rw [hψder y v, neg_neg]
  rw [sp_w_dzbar_combine (integrable_indicator_lemma92Exhaust hF n) hψ1 hcψ hder]
  have hGF : ∀ y, dzbar ψ y * (lemma92Exhaust U n).indicator F y = F y * dzbar ψ y := by
    intro y
    by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
    · rw [Set.indicator_of_mem (hball hy)]; ring
    · rw [hdz0 y hy]; ring
  rw [integral_congr_ae (Eventually.of_forall hGF), hw, neg_zero]

open LiZhongQC in
/-- Weyl's lemma with `C∞` test functions (replica of `LiZhongQC.sp_w_weyl`). -/
theorem p11a_weyl {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ w in U, F w * dzbar ψ w = 0) :
    DifferentiableOn ℂ F U := by
  have step : ∀ C : Set ℂ, IsCompact C → C ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ C, DifferentiableAt ℂ (lemma92Approx U F n) z := by
    intro C hC hCU
    obtain ⟨δ, hδ, hδU, hev⟩ := lemma92_eventually hU hC hCU
    filter_upwards [hev] with n hn z hz
    obtain ⟨hnδ, hnK⟩ := hn
    have hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n := fun y hy =>
      hnK (mem_cthickening_of_dist_le y z δ C hz ((mem_closedBall.1 hy).trans hnδ.le))
    exact cauchyRiemann_iff.2
      ⟨(contDiff_lemma92Approx hF n).differentiable one_ne_zero z,
        p11a_dzbar_approx_eq_zero hU hF hweak hball⟩
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hCU : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hVC : ball z₀ (r / 2) ⊆ closedBall z₀ (r / 2) := ball_subset_closedBall
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (lemma92Approx U F n) (ball z₀ (r / 2)) := by
    filter_upwards [step (closedBall z₀ (r / 2)) (isCompact_closedBall _ _) hCU] with n hn z hz
    exact (hn z (hVC hz)).differentiableWithinAt
  have hFV : DifferentiableOn ℂ F (ball z₀ (r / 2)) :=
    ((tendstoLocallyUniformlyOn_lemma92Approx hU hF).mono (hVC.trans hCU)).differentiableOn
      hdiff isOpen_ball
  exact (hFV.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))).differentiableWithinAt

open LiZhongQC in
/-- From distributional partials with `g + I h = 0` a.e., the weak `∂̄`-equation for `C∞` tests. -/
theorem p11a_weak_dzbar_eq_zero {f g h : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hdist : HasDistribPartials f g h Ω)
    (hgh : ∀ᵐ z ∂(volume.restrict Ω), g z + I * h z = 0)
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω) :
    ∫ w in Ω, f w * dzbar ψ w = 0 := by
  have hK : IsCompact (tsupport ψ) := hcψ.isCompact
  have hIf : IntegrableOn f (tsupport ψ) := (hdist.1 _ hsψ hK).1
  have hIg : IntegrableOn g (tsupport ψ) := (hdist.1 _ hsψ hK).2.1
  have hIh : IntegrableOn h (tsupport ψ) := (hdist.1 _ hsψ hK).2.2
  have hψcont : Continuous ψ := hψ.continuous
  have hfxcont : Continuous fun z => fderiv ℝ ψ z 1 :=
    ((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfycont : Continuous fun z => fderiv ℝ ψ z I :=
    ((hψ.of_le (by simp)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hIfx : Integrable fun z => f z * fderiv ℝ ψ z 1 :=
    p11a_integrable_of_support hIf hcψ
      (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz 1) hfxcont
  have hIfy : Integrable fun z => f z * fderiv ℝ ψ z I :=
    p11a_integrable_of_support hIf hcψ
      (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz I) hfycont
  have hψ0 : ∀ z ∉ tsupport ψ, ψ z = 0 := fun z hz =>
    Function.notMem_support.1 (fun hs => hz (subset_closure hs))
  have hIgψ : Integrable fun z => g z * ψ z := p11a_integrable_of_support hIg hcψ hψ0 hψcont
  have hIhψ : Integrable fun z => h z * ψ z := p11a_integrable_of_support hIh hcψ hψ0 hψcont
  have E1 : (∫ z, f z * fderiv ℝ ψ z 1) = -∫ z, g z * ψ z := (hdist.2 ψ hψ hcψ hsψ).1
  have E2 : (∫ z, f z * fderiv ℝ ψ z I) = -∫ z, h z * ψ z := (hdist.2 ψ hψ hcψ hsψ).2
  have hsupp0 : ∀ z ∉ tsupport ψ, f z * dzbar ψ z = 0 := fun z hz => by
    have e1 := sp_fderiv_eq_zero_of_notMem_tsupport hz 1
    have e2 := sp_fderiv_eq_zero_of_notMem_tsupport hz I
    rw [dzbar, e1, e2]
    simp
  rw [sp_setIntegral_eq_integral hΩ.measurableSet hsψ hsupp0]
  have hsplit : ∀ z, f z * dzbar ψ z =
      (f z * fderiv ℝ ψ z 1 + I * (f z * fderiv ℝ ψ z I)) / 2 := fun z => by
    rw [dzbar]; ring
  rw [integral_congr_ae (Eventually.of_forall hsplit)]
  rw [integral_div, integral_add hIfx (hIfy.const_mul I), integral_const_mul, E1, E2]
  have H : (∫ z, g z * ψ z) + I * (∫ z, h z * ψ z) = 0 := by
    rw [← integral_const_mul, ← integral_add hIgψ (hIhψ.const_mul I)]
    have hcongr : (fun z => g z * ψ z + I * (h z * ψ z)) = fun z => (g z + I * h z) * ψ z := by
      funext z; ring
    rw [hcongr]
    have h0 : ∀ z ∉ tsupport ψ, (g z + I * h z) * ψ z = 0 := fun z hz => by
      rw [hψ0 z hz, mul_zero]
    rw [← sp_setIntegral_eq_integral hΩ.measurableSet hsψ h0]
    apply integral_eq_zero_of_ae
    filter_upwards [hgh] with z hz
    simp [hz]
  have hneg : (-∫ z, g z * ψ z) + I * (-∫ z, h z * ψ z) = 0 := by linear_combination -H
  rw [hneg]
  simp

open LiZhongQC in
/-- A holomorphic function on `Ω` has distributional partials (its real partial derivatives). -/
theorem p11a_hasDistribPartials_of_differentiableOn {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hd : DifferentiableOn ℂ f Ω) :
    HasDistribPartials f (fun z => fderiv ℝ f z 1) (fun z => fderiv ℝ f z I) Ω := by
  have hC1 : ContDiffOn ℝ 1 f Ω :=
    (((hd.analyticOnNhd hΩ).contDiffOn hΩ.uniqueDiffOn).restrict_scalars ℝ).of_le le_top
  have hfdcont : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ f z v) Ω := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp_continuousOn
      (hC1.continuousOn_fderiv_of_isOpen hΩ (le_refl 1))
  constructor
  · intro C hC hCc
    exact ⟨(hd.continuousOn.mono hC).integrableOn_compact hCc,
      ((hfdcont 1).mono hC).integrableOn_compact hCc, ((hfdcont I).mono hC).integrableOn_compact hCc⟩
  · intro φ hφ hcφ hsφ
    have hφcont : Continuous φ := hφ.continuous
    have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hF1 : ContDiff ℝ 1 (fun z => f z * φ z) := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ tsupport φ
      · have hO : ContDiffOn ℝ 1 (fun z => f z * φ z) Ω :=
          hC1.mul (hφ.of_le (by simp)).contDiffOn
        exact hO.contDiffAt (hΩ.mem_nhds (hsφ hz))
      · have h0 : (fun z => f z * φ z) =ᶠ[𝓝 z] 0 := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with w hw
          have hww : φ w = 0 := Function.notMem_support.1 (fun hs => hw (subset_closure hs))
          show f w * φ w = 0
          rw [hww, mul_zero]
        exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq h0
    have hFsupp : HasCompactSupport (fun z => f z * φ z) := by
      have hsub : Function.support (fun z => f z * φ z) ⊆ tsupport φ := fun z hz => by
        by_contra hzc
        have hz0 : φ z = 0 := Function.notMem_support.1 (fun hs => hzc (subset_closure hs))
        exact hz (by simp [hz0])
      exact hcφ.isCompact.of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal hsub (isClosed_tsupport φ))
    have hFder : ∀ (e : ℂ) (z : ℂ),
        fderiv ℝ (fun w => f w * φ w) z e = fderiv ℝ f z e * φ z + f z * fderiv ℝ φ z e := by
      intro e z
      by_cases hz : z ∈ tsupport φ
      · have hfd : DifferentiableAt ℝ f z :=
          (hC1.contDiffAt (hΩ.mem_nhds (hsφ hz))).differentiableAt one_ne_zero
        have hm : fderiv ℝ (fun w => f w * φ w) z =
            f z • fderiv ℝ φ z + φ z • fderiv ℝ f z :=
          fderiv_mul hfd (hφdiff z)
        rw [hm]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      · have hφ0 : φ =ᶠ[𝓝 z] 0 := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with w hw
          exact Function.notMem_support.1 (fun hs => hw (subset_closure hs))
        have hF0 : (fun w => f w * φ w) =ᶠ[𝓝 z] 0 := by
          filter_upwards [hφ0] with w hw
          show f w * φ w = 0
          simp [hw]
        rw [hF0.fderiv_eq, hφ0.fderiv_eq]
        simp [hφ0.eq_of_nhds]
    have hIBP : ∀ e : ℂ, e = 1 ∨ e = I →
        (∫ z, f z * fderiv ℝ φ z e) = -∫ z, fderiv ℝ f z e * φ z := by
      intro e he
      have hIfφ : Integrable fun z => f z * fderiv ℝ φ z e :=
        p11a_integrable_of_support' hd.continuousOn hsφ hcφ
          (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz e)
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      have hIfxφ : Integrable fun z => fderiv ℝ f z e * φ z :=
        p11a_integrable_of_support' (hfdcont e) hsφ hcφ
          (fun z hz => Function.notMem_support.1 (fun hs => hz (subset_closure hs))) hφcont
      have h0 : (∫ z, fderiv ℝ (fun w => f w * φ w) z e) = 0 := by
        rcases he with rfl | rfl
        · exact (sp_integral_fderiv_eq_zero hF1 hFsupp).1
        · exact (sp_integral_fderiv_eq_zero hF1 hFsupp).2
      rw [integral_congr_ae (Eventually.of_forall (fun z => hFder e z))] at h0
      rw [integral_add hIfxφ hIfφ] at h0
      exact eq_neg_of_add_eq_zero_right h0
    exact ⟨hIBP 1 (Or.inl rfl), hIBP I (Or.inr rfl)⟩

/-- **Proposition 1** (§1.3, l. 613), first part. A map of a plane domain is `1`-quasiconformal if and only if it is
conformal. -/
theorem prop1_1_a {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) :
    IsKQCAnalytic f Ω 1 ↔ IsConformalOnto f Ω (f '' Ω) := by
  constructor
  · intro hf
    obtain ⟨-, -, -, hhomeo, -, g, h, hdist, hbound⟩ := hf
    have hgh : ∀ᵐ z ∂(volume.restrict Ω), g z + I * h z = 0 := by
      filter_upwards [hbound] with z hz
      rw [show ((1 : ℝ) - 1) / (1 + 1) = 0 by norm_num, zero_mul] at hz
      have h0 : (g z + I * h z) / 2 = 0 := norm_le_zero_iff.1 hz
      exact (div_eq_zero_iff.1 h0).resolve_right two_ne_zero
    have hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        ∫ w in Ω, f w * LiZhongQC.dzbar ψ w = 0 :=
      fun ψ hψ hcψ hsψ => p11a_weak_dzbar_eq_zero hΩ hdist hgh hψ hcψ hsψ
    have hdiff : DifferentiableOn ℂ f Ω := p11a_weyl hΩ hhomeo.1 hweak
    exact ⟨hdiff, hhomeo.2.1, rfl⟩
  · intro hf
    have hhomeo : IsHomeomorphOnto f Ω (f '' Ω) :=
      ⟨hf.1.continuousOn, hf.2.1, rfl, (hf.symm hΩ).1.continuousOn⟩
    have himgopen : IsOpen (f '' Ω) := hf.isOpen hΩ
    refine ⟨hΩ, hc, le_refl 1, hhomeo, himgopen, _, _,
      p11a_hasDistribPartials_of_differentiableOn hΩ hf.1, ?_⟩
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    rw [show ((1 : ℝ) - 1) / (1 + 1) = 0 by norm_num, zero_mul]
    have hdz : DifferentiableAt ℂ f z := hf.1.differentiableAt (hΩ.mem_nhds hz)
    have hdzbar0 : LiZhongQC.dzbar f z = 0 := (LiZhongQC.cauchyRiemann_iff.1 hdz).2
    show ‖LiZhongQC.dzbar f z‖ ≤ 0
    rw [hdzbar0]
    simp

open LiZhongQC in
/-- The rectangle IBP feeding `LiZhongQC.fderiv_lemma92Approx_eq`, discharged from a distributional
equation `∫ f φᵥ = −∫ dF φ` (one direction `v`). -/
theorem p12_ibp_rect {f dF : ℂ → ℂ} {Ω : Set ℂ} (v : ℂ)
    (hdistrib : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ w, f w * fderiv ℝ φ w v) = -∫ w, dF w * φ w)
    {δ : ℝ} {n : ℕ} (hn : 1 / ((n : ℝ) + 1) < δ) {z : ℂ}
    (hzΩ : closedBall z (1 / ((n : ℝ) + 1)) ⊆ Ω) :
    ∫ w in openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ),
        fderiv ℝ (fun w => (lemma92Bump n).normed volume (z - w)) w v • f w =
      -∫ w in openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ),
        (lemma92Bump n).normed volume (z - w) • dF w := by
  obtain ⟨φz, hφzdef⟩ : ∃ φz : ℂ → ℂ,
      φz = fun w : ℂ => ((((lemma92Bump n).normed volume) (z - w) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hφz_smooth : ContDiff ℝ ∞ φz := by
    rw [hφzdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := ⊤))).comp (contDiff_const.sub contDiff_id)
  have hφz0 : ∀ w ∉ closedBall z (1 / ((n : ℝ) + 1)), φz w = 0 := by
    intro w hw
    rw [mem_closedBall, not_le] at hw
    have h : 1 / ((n : ℝ) + 1) ≤ ‖z - w‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hw.le
    rw [hφzdef]
    simp [lemma92Bump_normed_eq_zero h]
  have hcφz : HasCompactSupport φz := HasCompactSupport.intro (isCompact_closedBall z _) hφz0
  have hsφz : tsupport φz ⊆ closedBall z (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun w hw => ?_) isClosed_closedBall
    by_contra h
    exact hw (hφz0 w h)
  -- the rectangle contains the support
  set R := openRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ) with hRdef
  have hSR : closedBall z (1 / ((n : ℝ) + 1)) ⊆ R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have he : ‖w - z‖ < δ := lt_of_le_of_lt hw hn
    have h1 : |w.re - z.re| < δ := lt_of_le_of_lt (Complex.abs_re_le_norm (w - z)) he
    have h2 : |w.im - z.im| < δ := lt_of_le_of_lt (Complex.abs_im_le_norm (w - z)) he
    rw [abs_lt] at h1 h2
    rw [hRdef]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hRm : MeasurableSet R := by
    have e : R = Complex.re ⁻¹' Ioo (z.re - δ) (z.re + δ) ∩
        Complex.im ⁻¹' Ioo (z.im - δ) (z.im + δ) := by
      ext w
      simp [hRdef, openRect, and_assoc]
    rw [e]
    exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
      (measurableSet_Ioo.preimage Complex.measurable_im)
  -- the distributional equation applied to the shifted bump
  have E := hdistrib φz hφz_smooth hcφz (hsφz.trans hzΩ)
  have hLv0' : ∀ w ∉ closedBall z (1 / ((n : ℝ) + 1)),
      fderiv ℝ (fun w => (lemma92Bump n).normed volume (z - w)) w v • f w = 0 := fun w hw => by
    have h0 : fderiv ℝ (fun w => (lemma92Bump n).normed volume (z - w)) w = 0 := by
      have hev0 : (fun w => (lemma92Bump n).normed volume (z - w)) =ᶠ[𝓝 w] 0 := by
        filter_upwards [(isClosed_closedBall.isOpen_compl).mem_nhds hw] with y hy
        have hy' : ¬ dist y z ≤ 1 / ((n : ℝ) + 1) := by simpa [mem_closedBall] using hy
        show (lemma92Bump n).normed volume (z - y) = 0
        exact lemma92Bump_normed_eq_zero (by
          rw [norm_sub_rev, ← dist_eq_norm]
          exact (not_le.1 hy').le)
      rw [hev0.fderiv_eq]
      simp
    rw [h0]
    simp
  have hRv0' : ∀ w ∉ closedBall z (1 / ((n : ℝ) + 1)),
      (lemma92Bump n).normed volume (z - w) • dF w = 0 := fun w hw => by
    rw [mem_closedBall, not_le] at hw
    rw [lemma92Bump_normed_eq_zero (by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hw.le)]
    simp
  rw [sp_setIntegral_eq_integral hRm hSR hLv0', sp_setIntegral_eq_integral hRm hSR hRv0']
  -- now over the plane; rewrite to E's form
  have hdu : Differentiable ℝ (fun w' => (lemma92Bump n).normed volume (z - w')) :=
    (((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero).comp
      ((contDiff_const.sub contDiff_id).differentiable one_ne_zero)
  have hderφ : ∀ w, fderiv ℝ φz w v =
      ((fderiv ℝ (fun w' => (lemma92Bump n).normed volume (z - w')) w v : ℝ) : ℂ) := by
    intro w
    have hfφ : HasFDerivAt φz
        (Complex.ofRealCLM.comp (fderiv ℝ (fun w' => (lemma92Bump n).normed volume (z - w')) w)) w := by
      rw [hφzdef]
      exact (Complex.ofRealCLM.hasFDerivAt).comp w (hdu w).hasFDerivAt
    rw [hfφ.fderiv]
    simp
  have hpt1 : ∀ w, fderiv ℝ (fun w => (lemma92Bump n).normed volume (z - w)) w v • f w =
      f w * fderiv ℝ φz w v := fun w => by
    rw [Complex.real_smul, hderφ w]
    ring
  have hpt2 : ∀ w, dF w * φz w = (lemma92Bump n).normed volume (z - w) • dF w := fun w => by
    rw [hφzdef, Complex.real_smul]
    exact mul_comm _ _
  rw [integral_congr_ae (Eventually.of_forall hpt1), E,
    integral_congr_ae (Eventually.of_forall hpt2)]

open LiZhongQC in
/-- The `L¹`-on-compacts convergence of the mollified derivatives to a distributional derivative. -/
theorem p12_tendsto_eLpNorm {f dF : ℂ → ℂ} {Ω C : Set ℂ} (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω)
    (hdFint : ∀ K ⊆ Ω, IsCompact K → IntegrableOn dF K)
    (v : ℂ)
    (hdistrib : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ w, f w * fderiv ℝ φ w v) = -∫ w, dF w * φ w)
    (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (lemma92Approx Ω f n) z v - dF z) 1
        (volume.restrict C)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδU, hev⟩ := lemma92_eventually hΩ hC hCΩ
  have hKc : IsCompact (cthickening δ C) := hC.cthickening
  have hsubΩ : cthickening δ C ⊆ Ω :=
    (cthickening_mono (by linarith : δ ≤ 2 * δ) _).trans hδU
  have hFi : Integrable ((cthickening δ C).indicator dF) :=
    (hdFint _ hsubΩ hKc).integrable_indicator isClosed_cthickening.measurableSet
  have hFmem : MemLp ((cthickening δ C).indicator dF) 1 volume := memLp_one_iff_integrable.2 hFi
  have hfun : (fun n => (lemma92Bump n).rOut) = fun n : ℕ => 1 / ((n : ℝ) + 1) :=
    funext fun n => rfl
  have hb : Tendsto (fun n => (lemma92Bump n).rOut) atTop (𝓝 0) := by
    rw [hfun]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hCv : volume C ≠ ⊤ := hC.measure_lt_top.ne
  have hkey := tendsto_eLpNorm_convolution_normed_sub hb (le_refl 1) ENNReal.one_ne_top hFmem hCv
  refine hkey.congr' ?_
  filter_upwards [hev] with n hn
  obtain ⟨hnδ, hnK⟩ := hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
  have hzball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ Ω := fun w hw =>
    lemma92Exhaust_subset Ω n
      (hnK (mem_cthickening_of_dist_le w z δ C hz ((mem_closedBall.1 hw).trans hnδ.le)))
  rw [fderiv_lemma92Approx_eq hcont hnδ hnK hz v (p12_ibp_rect v hdistrib hnδ hzball),
    Set.indicator_of_mem (self_subset_cthickening C hz)]

/-- Helper for `prop1_1_b` and `prop1_3` (§1.3–1.4), the analytic ⇒ geometric bridge: a `K`-quasiconformal map in
the sense of Definition 2 is `K`-quasiconformal in the geometric sense (`LiZhongQC.IsKQC`). The distributional
partials are generalized partials (the construction of `prop1_2`), so `f` is ACL with classical partials `g`, `h` a.e.
(`LiZhongQC.lemma9_2_isACL_of_genPartials`) and differentiable a.e. (Menchoff, `LiZhongQC.lemma9_1_menchoff`); the
bound `|f_z̄| ≤ k |f_z|` is then Theorem 10.1's analytic condition (`LiZhongQC.thm10_1_isKQC_iff`). -/
theorem gl1_acl_isKQC {f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hf : IsKQCAnalytic f Ω K) : LiZhongQC.IsKQC f Ω K := by
  obtain ⟨hΩ, -, hK, hhom, -, g, h, hd, hb⟩ := hf
  have hcont : ContinuousOn f Ω := hhom.1
  have hgen : LiZhongQC.HasGenPartials f g h Ω 1 := by
    refine ⟨fun C hCΩ hC => ⟨memLp_one_iff_integrable.2 ((hd.1 C hCΩ hC).2.1),
        memLp_one_iff_integrable.2 ((hd.1 C hCΩ hC).2.2)⟩,
      LiZhongQC.lemma92Approx Ω f, fun n => (LiZhongQC.contDiff_lemma92Approx hcont n).contDiffOn,
      LiZhongQC.tendstoLocallyUniformlyOn_lemma92Approx hΩ hcont, fun C hCΩ hC => ⟨
        p12_tendsto_eLpNorm hΩ hcont (fun K hKΩ hK => (hd.1 K hKΩ hK).2.1) 1
          (fun φ hφ hcφ hsφ => (hd.2 φ hφ hcφ hsφ).1) hC hCΩ,
        p12_tendsto_eLpNorm hΩ hcont (fun K hKΩ hK => (hd.1 K hKΩ hK).2.2) I
          (fun φ hφ hcφ hsφ => (hd.2 φ hφ hcφ hsφ).2) hC hCΩ⟩⟩
  obtain ⟨hacl, hgx, hhy⟩ := LiZhongQC.lemma9_2_isACL_of_genPartials hΩ le_rfl hgen
  have hdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ f z :=
    LiZhongQC.lemma9_1_menchoff hΩ hhom (LiZhongQC.cr_p_partials_ae_of_isACL hΩ hacl)
  refine (LiZhongQC.thm10_1_isKQC_iff hΩ hK hhom).2 ⟨hacl, ?_⟩
  filter_upwards [hdiff, hgx, hhy, hb] with z hzd hzx hzy hzb
  have e1 : fderiv ℝ f z 1 = g z := by rw [← LiZhongQC.partialX_eq_of_differentiableAt hzd, hzx]
  have e2 : fderiv ℝ f z I = h z := by rw [← LiZhongQC.partialY_eq_of_differentiableAt hzd, hzy]
  have hdz : LiZhongQC.dz f z = (g z - I * h z) / 2 := by rw [LiZhongQC.dz, e1, e2]
  have hdzbar : LiZhongQC.dzbar f z = (g z + I * h z) / 2 := by rw [LiZhongQC.dzbar, e1, e2]
  rw [hdz, hdzbar]
  -- `|f_z̄| ≤ ((K − 1)/(K + 1)) |f_z|` is `|f_z| + |f_z̄| ≤ K (|f_z| − |f_z̄|)`
  have hK1 : 0 < K + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1] at hzb
  nlinarith

/-- **Proposition 1** (§1.3, l. 613), second part. If `g` and `f` are quasiconformal and the image of `g` lies in the
domain of `f`, then `K(f ∘ g) ≤ K(f) K(g)`. (The book writes "the image of `f` … domain of `g`, `K(f ∘ g)`"; the
composition is read in the only order that makes sense.) -/
theorem prop1_1_b {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ} (hf : ∃ K, IsKQCAnalytic f Ω₂ K) (hg : ∃ K, IsKQCAnalytic g Ω₁ K)
    (hsub : g '' Ω₁ ⊆ Ω₂) :
    maxDilatation (f ∘ g) Ω₁ ≤ maxDilatation f Ω₂ * maxDilatation g Ω₁ := by
  -- both maps are geometrically quasiconformal (`gl1_acl_isKQC`), hence `K[·]`-q.c. with finite `K[·] ≥ 1`
  -- (`LiZhongQC.UniversalTeichmuller.ut_md_isKQC_toReal`); compose (Theorem 7.1) and bound `K[f ∘ g]`
  obtain ⟨Kf, hf⟩ := hf
  obtain ⟨Kg, hg⟩ := hg
  have hfK := gl1_acl_isKQC hf
  have hgK := gl1_acl_isKQC hg
  obtain ⟨-, hf'⟩ := LiZhongQC.UniversalTeichmuller.ut_md_isKQC_toReal hfK hf.2.1.nonempty
  obtain ⟨-, hg'⟩ := LiZhongQC.UniversalTeichmuller.ut_md_isKQC_toReal hgK hg.2.1.nonempty
  have hfin_f : maxDilatation f Ω₂ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (LiZhongQC.isKQC_maxDilatation_le hfK).1
  have hfin_g : maxDilatation g Ω₁ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (LiZhongQC.isKQC_maxDilatation_le hgK).1
  have hcomp := LiZhongQC.thm7_1_comp hg' hf' hsub
  calc maxDilatation (f ∘ g) Ω₁
      ≤ ENNReal.ofReal ((maxDilatation g Ω₁).toReal * (maxDilatation f Ω₂).toReal) :=
        (LiZhongQC.isKQC_maxDilatation_le hcomp).1
    _ = maxDilatation g Ω₁ * maxDilatation f Ω₂ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin_g, ENNReal.ofReal_toReal hfin_f]
    _ = maxDilatation f Ω₂ * maxDilatation g Ω₁ := mul_comm _ _

/-- **Proposition 1** (§1.3, l. 613), third part. If `f` is `K`-quasiconformal and `g`, `h` are conformal, then
`g ∘ f ∘ h` is `K`-quasiconformal. -/
theorem prop1_1_c {f g h : ℂ → ℂ} {Ω₀ Ω : Set ℂ} {K : ℝ} (hf : IsKQCAnalytic f Ω K) (hΩ₀ : IsOpen Ω₀)
    (hΩ₀c : IsConnected Ω₀) (hh : IsConformalOnto h Ω₀ Ω) (hg : IsConformalOnto g (f '' Ω) (g '' (f '' Ω))) :
    IsKQCAnalytic (g ∘ f ∘ h) Ω₀ K := by
  sorry

/-- **Proposition 2** (§1.3, l. 636). A (continuous) map with locally integrable first partial derivatives in the
sense of Definition 1 is ACL. -/
theorem prop1_2 {f g h : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcont : ContinuousOn f Ω)
    (hf : HasDistribPartials f g h Ω) : IsACL f Ω := by
  have hgen : LiZhongQC.HasGenPartials f g h Ω 1 := by
    refine ⟨fun C hCΩ hC => ⟨memLp_one_iff_integrable.2 ((hf.1 C hCΩ hC).2.1),
        memLp_one_iff_integrable.2 ((hf.1 C hCΩ hC).2.2)⟩,
      LiZhongQC.lemma92Approx Ω f, fun n => (LiZhongQC.contDiff_lemma92Approx hcont n).contDiffOn,
      LiZhongQC.tendstoLocallyUniformlyOn_lemma92Approx hΩ hcont, fun C hCΩ hC => ⟨
        p12_tendsto_eLpNorm hΩ hcont (fun K hKΩ hK => (hf.1 K hKΩ hK).2.1) 1
          (fun φ hφ hcφ hsφ => (hf.2 φ hφ hcφ hsφ).1) hC hCΩ,
        p12_tendsto_eLpNorm hΩ hcont (fun K hKΩ hK => (hf.1 K hKΩ hK).2.2) I
          (fun φ hφ hcφ hsφ => (hf.2 φ hφ hcφ hsφ).2) hC hCΩ⟩⟩
  exact (LiZhongQC.lemma9_2_isACL_of_genPartials hΩ le_rfl hgen).1

end GardinerLakic2000
