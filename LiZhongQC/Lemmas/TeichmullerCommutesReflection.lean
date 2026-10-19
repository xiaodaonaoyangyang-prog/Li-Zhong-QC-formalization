import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDDimension
import LiZhongQC.Lemmas.FiniteTypePunctRefl
import LiZhongQC.Lemmas.S32wFoldPush
import LiZhongQC.Lemmas.S32wHalvesSelfmap
import LiZhongQC.Lemmas.S32wSymmExtPunctured
import LiZhongQC.Lemmas.S32wSymmetricExtension
import LiZhongQC.Lemmas.Thm321

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u


/-- `conj ∘ f ∘ conj` is analytic at `conj a` with derivative `conj (f' a)` when `f` is analytic at `a`. -/
theorem s82rc_analyticAt_conj_conj {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (fun u => conj (f (conj u))) (conj a) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have h : ∀ᶠ u in 𝓝 (conj a), DifferentiableAt ℂ f (conj u) :=
    (Complex.continuous_conj.tendsto (conj a)).eventually (p := fun y => DifferentiableAt ℂ f y)
      (by rw [conj_conj]; exact hf)
  filter_upwards [h] with u hu
  have := hu.conj_conj
  rw [conj_conj] at this
  exact this

/-- At the centre of a chart, the conjugated local expression of an anticonformal map is analytic with non-zero
derivative. -/
theorem s82rc_anti_local {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {J : X ≃ₜ Y}
    (hJ : ∀ x : X, DifferentiableOn ℂ (fun z => conj (localMapExpr J x z)) (localMapDomain J x)) (p : X) :
    AnalyticAt ℂ (fun z => conj (localMapExpr J p z)) (chartAt ℂ p p) ∧
      deriv (fun z => conj (localMapExpr J p z)) (chartAt ℂ p p) ≠ 0 := by
  have hps : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hdom : chartAt ℂ p p ∈ localMapDomain J p :=
    ⟨(chartAt ℂ p).map_source hps, by
      show J ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (J p)).source
      rw [(chartAt ℂ p).left_inv hps]
      exact mem_chart_source ℂ (J p)⟩
  have hopen := s23_localMapDomain_isOpen J.continuous p
  refine ⟨(hJ p).analyticAt (hopen.mem_nhds hdom), deriv_ne_zero_of_injOn hopen (hJ p) ?_ hdom⟩
  intro a ha b hb hab
  exact s23_c1_injOn_localMapExpr J.injective p ha hb (by simpa using congrArg conj hab)

/-- A chart transition is analytic with non-zero derivative where it is defined. -/
theorem s82rc_transition_analytic {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (a b : X) {z : ℂ} (hz : z ∈ (chartAt ℂ b).target) (hzx : (chartAt ℂ b).symm z ∈ (chartAt ℂ a).source) :
    AnalyticAt ℂ (chartTransition a b) z ∧ deriv (chartTransition a b) z ≠ 0 := by
  refine ⟨?_, (s23_transition a b hz hzx).2⟩
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [((chartAt ℂ b).isOpen_inter_preimage_symm (chartAt ℂ a).open_source).mem_nhds ⟨hz, hzx⟩]
    with w hw
  exact s23_transition_differentiableAt a b hw.1 hw.2

/-- **Sandwich lemma.**  Conjugating a `K`-quasiconformal map by two anticonformal homeomorphisms gives a
`K`-quasiconformal map: `J₁ ∘ f ∘ J₀`. -/
theorem s82rc_sandwich_qc {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B] {J₀ : A ≃ₜ A} {J₁ : B ≃ₜ B}
    (hJ₀ : ∀ x : A, DifferentiableOn ℂ (fun z => conj (localMapExpr J₀ x z)) (localMapDomain J₀ x))
    (hJ₁ : ∀ x : B, DifferentiableOn ℂ (fun z => conj (localMapExpr J₁ x z)) (localMapDomain J₁ x))
    {f : A ≃ₜ B} {K : ℝ} (hf : IsKQCRS f K) : IsKQCRS ((J₀.trans f).trans J₁) K := by
  refine ⟨hf.1, fun x => s23_lg (s23_localMapDomain_isOpen ((J₀.trans f).trans J₁).continuous x) hf.1
    (s23_c1_injOn_localMapExpr ((J₀.trans f).trans J₁).injective x) fun z0 hz0 => ?_⟩
  set p0 : A := (chartAt ℂ x).symm z0 with hp0
  set y : A := J₀ p0 with hy
  set w : B := f y with hw
  set v : B := J₁ w with hv
  have hz0t : z0 ∈ (chartAt ℂ x).target := hz0.1
  have hft : ((J₀.trans f).trans J₁) p0 = v := rfl
  have hv_src : v ∈ (chartAt ℂ (((J₀.trans f).trans J₁) x)).source := hz0.2
  have hp0src : p0 ∈ (chartAt ℂ p0).source := mem_chart_source ℂ p0
  -- the centres
  have hc0 : chartTransition p0 x z0 = chartAt ℂ p0 p0 := rfl
  obtain ⟨hB'an, hB'd⟩ := s82rc_anti_local hJ₀ p0
  obtain ⟨hA'an, hA'd⟩ := s82rc_anti_local hJ₁ w
  have hBc : localMapExpr J₀ p0 (chartAt ℂ p0 p0) = chartAt ℂ y y := by
    simp only [localMapExpr, (chartAt ℂ p0).left_inv hp0src]
    try rfl
  have hLc : localMapExpr f y (chartAt ℂ y y) = chartAt ℂ w w := by
    simp only [localMapExpr, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    try rfl
  have hAc : localMapExpr J₁ w (chartAt ℂ w w) = chartAt ℂ v v := by
    simp only [localMapExpr, (chartAt ℂ w).left_inv (mem_chart_source ℂ w)]
    try rfl
  obtain ⟨hT2an, hT2d⟩ := s82rc_transition_analytic p0 x hz0t (by rw [← hp0]; exact hp0src)
  obtain ⟨hT1an, hT1d⟩ := s82rc_transition_analytic (((J₀.trans f).trans J₁) x) v
    ((chartAt ℂ v).map_source (mem_chart_source ℂ v))
    (by rw [(chartAt ℂ v).left_inv (mem_chart_source ℂ v)]; exact hv_src)
  have hdomf : chartAt ℂ y y ∈ localMapDomain f y := (s23_h_center f y).1
  -- the three factors
  set τ : ℂ → ℂ := fun z => conj (localMapExpr J₀ p0 (chartTransition p0 x z)) with hτ
  set F : ℂ → ℂ := fun u => conj (localMapExpr f y (conj u)) with hF
  set σ : ℂ → ℂ := fun u => chartTransition (((J₀.trans f).trans J₁) x) v (localMapExpr J₁ w (conj u))
    with hσ
  have hτz : τ z0 = conj (chartAt ℂ y y) := by simp only [hτ, hc0, hBc]
  have hFz : F (τ z0) = conj (chartAt ℂ w w) := by
    simp only [hF, hτz, conj_conj, hLc]
  have hσz : σ (F (τ z0)) = chartTransition (((J₀.trans f).trans J₁) x) v (chartAt ℂ v v) := by
    simp only [hσ, hFz, conj_conj, hAc]
  have hτan : AnalyticAt ℂ τ z0 := by
    have h1 : AnalyticAt ℂ (fun z => conj (localMapExpr J₀ p0 z)) (chartTransition p0 x z0) := by
      rw [hc0]; exact hB'an
    exact h1.comp hT2an
  have hτd : deriv τ z0 ≠ 0 := by
    have h1 : DifferentiableAt ℂ (fun z => conj (localMapExpr J₀ p0 z)) (chartTransition p0 x z0) := by
      rw [hc0]; exact hB'an.differentiableAt
    have := deriv_comp z0 h1 hT2an.differentiableAt
    show deriv ((fun z => conj (localMapExpr J₀ p0 z)) ∘ chartTransition p0 x) z0 ≠ 0
    rw [this, hc0]
    exact mul_ne_zero hB'd hT2d
  -- σ
  have hHan : AnalyticAt ℂ (fun u => localMapExpr J₁ w (conj u)) (F (τ z0)) := by
    have h := s82rc_analyticAt_conj_conj hA'an
    rw [hFz]
    convert h using 1
    funext u
    simp
  have hσan : AnalyticAt ℂ σ (F (τ z0)) := by
    have h1 : AnalyticAt ℂ (chartTransition (((J₀.trans f).trans J₁) x) v)
        ((fun u => localMapExpr J₁ w (conj u)) (F (τ z0))) := by
      show AnalyticAt ℂ _ (localMapExpr J₁ w (conj (F (τ z0))))
      rw [hFz, conj_conj, hAc]; exact hT1an
    exact AnalyticAt.comp (g := chartTransition (((J₀.trans f).trans J₁) x) v)
      (f := fun u => localMapExpr J₁ w (conj u)) h1 hHan
  have hσd : deriv σ (F (τ z0)) ≠ 0 := by
    have hHd : deriv (fun u => localMapExpr J₁ w (conj u)) (F (τ z0)) ≠ 0 := by
      have h := (deriv_conj_conj (f := fun z => conj (localMapExpr J₁ w z)))
      have h2 := congrFun h (F (τ z0))
      simp only [Function.comp_apply] at h2
      have h3 : (fun u => conj (conj (localMapExpr J₁ w (conj u)))) = fun u => localMapExpr J₁ w (conj u) := by
        funext u; simp
      have h4 : (conj ∘ (fun z => conj (localMapExpr J₁ w z)) ∘ conj) = fun u => localMapExpr J₁ w (conj u) := by
        funext u; simp
      rw [h4] at h2
      rw [h2, hFz, conj_conj]
      simpa using hA'd
    have h1 : DifferentiableAt ℂ (chartTransition (((J₀.trans f).trans J₁) x) v)
        ((fun u => localMapExpr J₁ w (conj u)) (F (τ z0))) := by
      show DifferentiableAt ℂ _ (localMapExpr J₁ w (conj (F (τ z0))))
      rw [hFz, conj_conj, hAc]; exact hT1an.differentiableAt
    have := deriv_comp (F (τ z0)) h1 hHan.differentiableAt
    show deriv ((chartTransition (((J₀.trans f).trans J₁) x) v) ∘ (fun u => localMapExpr J₁ w (conj u))) (F (τ z0)) ≠ 0
    rw [this]
    refine mul_ne_zero ?_ hHd
    show deriv (chartTransition (((J₀.trans f).trans J₁) x) v) (localMapExpr J₁ w (conj (F (τ z0)))) ≠ 0
    rw [hFz, conj_conj, hAc]; exact hT1d
  have hFK : IsKQC F (conj ⁻¹' localMapDomain f y) K := abR_x_isKQC_conj (hf.2 y)
  have hτV : τ z0 ∈ conj ⁻¹' localMapDomain f y := by
    show conj (τ z0) ∈ localMapDomain f y
    rw [hτz, conj_conj]; exact hdomf
  have hN : localMapDomain (((J₀.trans f).trans J₁)) x ∈ 𝓝 z0 :=
    (s23_localMapDomain_isOpen ((J₀.trans f).trans J₁).continuous x).mem_nhds hz0
  have hsymm : ContinuousAt (chartAt ℂ x).symm z0 := (chartAt ℂ x).continuousAt_symm hz0t
  have e1 : ∀ᶠ z in 𝓝 z0, z ∈ (chartAt ℂ x).target := (chartAt ℂ x).open_target.mem_nhds hz0t
  have e2 : ∀ᶠ z in 𝓝 z0, (chartAt ℂ x).symm z ∈ (chartAt ℂ p0).source :=
    hsymm.eventually_mem ((chartAt ℂ p0).open_source.mem_nhds hp0src)
  have e3 : ∀ᶠ z in 𝓝 z0, J₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source :=
    (J₀.continuous.continuousAt.comp hsymm).eventually_mem
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
  have e4 : ∀ᶠ z in 𝓝 z0, f (J₀ ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ w).source :=
    (f.continuous.continuousAt.comp (J₀.continuous.continuousAt.comp hsymm)).eventually_mem
      ((chartAt ℂ w).open_source.mem_nhds (mem_chart_source ℂ w))
  have e5 : ∀ᶠ z in 𝓝 z0, J₁ (f (J₀ ((chartAt ℂ x).symm z))) ∈ (chartAt ℂ v).source :=
    (J₁.continuous.continuousAt.comp (f.continuous.continuousAt.comp
      (J₀.continuous.continuousAt.comp hsymm))).eventually_mem
      ((chartAt ℂ v).open_source.mem_nhds (mem_chart_source ℂ v))
  have hg : ∀ᶠ z in 𝓝 z0, localMapExpr ((J₀.trans f).trans J₁) x z = σ (F (τ z)) := by
    filter_upwards [e1, e2, e3, e4, e5] with z h1 h2 h3 h4 h5
    set p : A := (chartAt ℂ x).symm z with hp
    have s1 : chartTransition p0 x z = chartAt ℂ p0 p := rfl
    have s2 : localMapExpr J₀ p0 (chartAt ℂ p0 p) = chartAt ℂ y (J₀ p) := by
      simp only [localMapExpr, (chartAt ℂ p0).left_inv h2]
      rfl
    have s3 : localMapExpr f y (chartAt ℂ y (J₀ p)) = chartAt ℂ w (f (J₀ p)) := by
      simp only [localMapExpr, (chartAt ℂ y).left_inv h3]
      rfl
    have s4 : localMapExpr J₁ w (chartAt ℂ w (f (J₀ p))) = chartAt ℂ v (J₁ (f (J₀ p))) := by
      simp only [localMapExpr, (chartAt ℂ w).left_inv h4]
      rfl
    have s5 : chartTransition (((J₀.trans f).trans J₁) x) v (chartAt ℂ v (J₁ (f (J₀ p)))) =
        chartAt ℂ (((J₀.trans f).trans J₁) x) (J₁ (f (J₀ p))) := by
      simp only [chartTransition, (chartAt ℂ v).left_inv h5]
    have s6 : σ (F (τ z)) = chartAt ℂ (((J₀.trans f).trans J₁) x) (J₁ (f (J₀ p))) := by
      simp only [hσ, hF, hτ, s1, s2, conj_conj, s3, s4, s5]
    rw [s6]
    rfl
  exact s26w_isKQC_local_comp (g := localMapExpr ((J₀.trans f).trans J₁) x) hFK hτV hτan hτd hσan hσd hg hN


section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Conjunct 1 of (32.3).**  A Teichmüller map `f₀` of the punctured doubles (admissible differential) homotopic
to a map `fdp` commuting with the reflections commutes with the reflections: `J₁ ∘ f₀ ∘ J₀` is quasiconformal with
the same maximal dilatation and homotopic to `f₀`, hence equal to `f₀` by the uniqueness theorem 32.1. -/
theorem s82rc_commutes {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0)
    {fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁}
    (hfdpJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (fdp y' : Xd₁.carrier) = J₁ (fdp y))
    {f₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} {q : puncturedOpens Pd₀ → ℂ → ℂ}
    {q' : puncturedOpens Pd₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap Fd₀ f₀ q q' k)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (f₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₁))) :
    ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₀ y' : Xd₁.carrier) = J₁ (f₀ y) := by
  classical
  have hexd := s82cmp_hex_double hm hex
  obtain ⟨Jd₀, hJd₀⟩ := s82cmp_punct_J Pd₀ J₀ hd₀.involution.1 hd₀.Pd_invariant
  obtain ⟨Jd₁, hJd₁⟩ := s82cmp_punct_J Pd₁ J₁ hd₁.involution.1 hd₁.Pd_invariant
  have hA₀ := s82cmp_opens_involution (puncturedOpens Pd₀) hd₀.involution Jd₀ hJd₀
  have hA₁ := s82cmp_opens_involution (puncturedOpens Pd₁) hd₁.involution Jd₁ hJd₁
  obtain ⟨Fd₁⟩ := s31dm_punctured_fts Pd₁ hd₁.genus hd₁.card_Pd
  haveI : Nonempty S₀ := inferInstance
  haveI : Nonempty (puncturedOpens Pd₀) := by
    obtain ⟨x⟩ : Nonempty S₀ := inferInstance
    exact ⟨⟨ιd₀ x, s32w_double_range_off_Pd F₀ hd₀ x⟩⟩
  have hqc := hf₀.2.qc
  have hK := s29_m_isKQCRS_maxDil hqc
  set ft : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁ := (Jd₀.trans f₀).trans Jd₁ with hft
  have hftK := s82rc_sandwich_qc hA₀.2 hA₁.2 hK
  have hftqc : IsQCRS ft := ⟨_, hftK⟩
  have hmax : maxDilatationRS ft ≤ maxDilatationRS f₀ := by
    have h3 := maxDilatationRS_le hftK
    rwa [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hqc)] at h3
  have hback : f₀ = (Jd₀.trans ft).trans Jd₁ := by
    refine Homeomorph.ext fun y => ?_
    show f₀ y = Jd₁ (Jd₁ (f₀ (Jd₀ (Jd₀ y))))
    rw [hA₀.1, hA₁.1]
  have hmax' : maxDilatationRS f₀ ≤ maxDilatationRS ft := by
    have h3 := maxDilatationRS_le (s82rc_sandwich_qc hA₀.2 hA₁.2 (s29_m_isKQCRS_maxDil hftqc))
    rw [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hftqc)] at h3
    rwa [← hback] at h3
  -- homotopy
  have hfdpeq : (Jd₁ : C(puncturedOpens Pd₁, puncturedOpens Pd₁)).comp
      ((fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁)).comp (Jd₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₀))) =
      (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) := by
    ext y
    show (Jd₁ (fdp (Jd₀ y)) : Xd₁.carrier) = (fdp y : Xd₁.carrier)
    rw [hJd₁, hfdpJ y (Jd₀ y) (by rw [hJd₀])]
    exact hd₁.involution.1 _
  have hh1 : ContinuousMap.Homotopic
      ((Jd₁ : C(puncturedOpens Pd₁, puncturedOpens Pd₁)).comp
        ((fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁)).comp (Jd₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₀))))
      ((Jd₁ : C(puncturedOpens Pd₁, puncturedOpens Pd₁)).comp
        ((f₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₁)).comp (Jd₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₀)))) :=
    (ContinuousMap.Homotopic.refl _).comp (hhom.comp (ContinuousMap.Homotopic.refl _))
  rw [hfdpeq] at hh1
  have hhom2 : ContinuousMap.Homotopic (f₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (ft : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) := hhom.symm.trans hh1
  haveI := s32w_punctured_connectedSpace Pd₀
  haveI := s32w_punctured_connectedSpace Pd₁
  obtain ⟨-, huniq⟩ := s82lc_thm32_1_uniqueness_gn hexd Fd₀ Fd₁ hf₀ hftqc hhom2
  have hfe : ⇑ft = ⇑f₀ := huniq (le_antisymm hmax hmax')
  intro y y' hy'
  have hy : y' = Jd₀ y := Subtype.ext (by rw [hJd₀]; exact hy')
  subst hy
  have h1 : Jd₁ (f₀ (Jd₀ y)) = f₀ y := congrFun hfe y
  have h2 : f₀ (Jd₀ y) = Jd₁ (f₀ y) := by
    rw [← h1, hA₁.1]
  rw [h2, hJd₁]

end

section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- (32.3), amended by the user decision of 2026-10-17 with `(hf : IsQCRS f)`: the Teichmüller map `f₀ : S₀^d → S₁^d`
of the (punctured) doubles, of type `(2g + m - 1, 2n, 0)`, in the class of `f^d` commutes with the reflections,
`g₁ ∘ f₀ = f₀ ∘ g₀` (uniqueness, Theorem 32.1, applied to `g₁ ∘ f₀ ∘ g₀⁻¹`, which is again a quasiconformal map
homotopic to `f^d` with the same dilatation); hence `f₀` maps the boundary curves of `S₀` onto those of `S₁`, so
`f₀(S₀) = S₁`. -/
theorem s82rc_eq32_3_teichmuller_commutes_reflection {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0) (f : S₀ ≃ₜ S) (hf : IsQCRS f)
    {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd)
    {fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hfdp : ∀ y, (fdp y : Xd₁.carrier) = fd y)
    {f₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} {q : puncturedOpens Pd₀ → ℂ → ℂ}
    {q' : puncturedOpens Pd₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap Fd₀ f₀ q q' k)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (f₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₁))) :
    (∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₀ y' : Xd₁.carrier) = J₁ (f₀ y)) ∧
      (fun y : puncturedOpens Pd₀ => (f₀ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} = range ιd₁ := by
  classical
  have hfdpJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y →
      (fdp y' : Xd₁.carrier) = J₁ (fdp y) := by
    intro y y' hy'
    rw [hfdp, hfdp, hy']
    exact hfd.2 _
  have hc1 := s82rc_commutes hm hex F₀ F₁ hd₀ hd₁ Fd₀ hfdpJ hf₀ hhom
  refine ⟨hc1, ?_⟩
  obtain ⟨K, hK⟩ := s29_m_isKQCRS_maxDil hf |> fun h => (⟨_, h⟩ : ∃ K, IsKQCRS f K)
  have hfdqc : IsQCRS fd := ⟨K, s32w_se_isKQCRS F₀ F₁ hd₀ hd₁ hK hfd⟩
  have hfdpqc : IsQCRS fdp := s32w_isQCRS_restrict_punctured hfdp hfdqc
  have hvA : ∀ y : puncturedOpens Pd₀, (y : Xd₀.carrier) ∈ range ιd₀ →
      (fdp y : Xd₁.carrier) ∈ range ιd₁ := by
    rintro y ⟨x, hx⟩
    refine ⟨f x, ?_⟩
    rw [hfdp, ← hx]
    exact (hfd.1 x).symm
  have hhalf := s32w_orientation_halves hm hex F₀ F₁ hd₀ hd₁ hfdpqc hf₀.2.qc hhom hvA hfdpJ hc1
  have hoff₀ := s32w_double_range_off_Pd F₀ hd₀
  have hoff₁ := s32w_double_range_off_Pd F₁ hd₁
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hhalf y hy
  · rintro ⟨s, rfl⟩
    set z' : puncturedOpens Pd₁ := ⟨ιd₁ s, hoff₁ s⟩ with hz'
    refine ⟨f₀.symm z', ?_, by simp [hz']⟩
    set y : puncturedOpens Pd₀ := f₀.symm z' with hy
    have hfy : f₀ y = z' := f₀.apply_symm_apply z'
    have hfy' : (f₀ y : Xd₁.carrier) = ιd₁ s := by rw [hfy]
    have hcov : (y : Xd₀.carrier) ∈ range ιd₀ ∪ range (J₀ ∘ ιd₀) ∪ {x | J₀ x = x} ∪ ↑Pd₀ := by
      rw [hd₀.cover]; trivial
    rcases hcov with ((h | h) | h) | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := h
      set y₁ : puncturedOpens Pd₀ := ⟨ιd₀ x, hoff₀ x⟩
      have h1 := hc1 y₁ y (by simpa [y₁] using hx.symm)
      obtain ⟨t, ht⟩ := hhalf y₁ ⟨x, rfl⟩
      rw [hfy', ← ht] at h1
      exact Set.disjoint_left.1 hd₁.disjoint ⟨s, rfl⟩ ⟨t, h1.symm⟩
    · exfalso
      have h1 := hc1 y y (h.symm)
      rw [hfy'] at h1
      exact Set.disjoint_left.1 hd₁.disjoint ⟨s, rfl⟩ ⟨s, h1.symm⟩
    · exact absurd h y.2

end

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- (32.3): the Teichmüller map `f₀ : S₀^d → S₁^d` of the (punctured) doubles, of type `(2g + m - 1, 2n, 0)`, in the
class of `f^d` commutes with the reflections, `g₁ ∘ f₀ = f₀ ∘ g₀` (uniqueness, Theorem 32.1, applied to
`g₁ ∘ f₀ ∘ g₀⁻¹`, which is again a quasiconformal map homotopic to `f^d` with the same dilatation); hence `f₀` maps
the boundary curves of `S₀` (the fixed curves of `g₀`) onto those of `S₁`, so `f₀(S₀) = S₁`.

**Correction (2026-09-27).**  The Teichmüller map now lives on the punctured doubles of type
`(2g + m - 1, 2n, 0)` with an admissible differential, as in the book: on the closed doubles it forgot
the punctures and the old statement was false for `n ≥ 1` (refuted in Lean, s31t).

**Correction (2026-10-17).**  The hypothesis `(hf : IsQCRS f)` was added right after `(f : S₀ ≃ₜ S)`: the
book's context in §32.2 is a quasiconformal map `f`, and conjunct 2 (`f₀(S₀) = S₁`, by the orientation detection of
the half in the punctured double) needs the quasiconformality of `f`; a quasiconformality-free version would need
the limit-set geometry of the lifted Fuchsian actions. Conjunct 1 does not use `hf`. -/
theorem eq32_3_teichmuller_commutes_reflection {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0) (f : S₀ ≃ₜ S) (hf : IsQCRS f)
    {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd)
    {fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hfdp : ∀ y, (fdp y : Xd₁.carrier) = fd y)
    {f₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} {q : puncturedOpens Pd₀ → ℂ → ℂ}
    {q' : puncturedOpens Pd₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap Fd₀ f₀ q q' k)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (f₀ : C(puncturedOpens Pd₀, puncturedOpens Pd₁))) :
    (∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₀ y' : Xd₁.carrier) = J₁ (f₀ y)) ∧
      (fun y : puncturedOpens Pd₀ => (f₀ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} = range ιd₁ := by
  exact s82rc_eq32_3_teichmuller_commutes_reflection hm hex F₀ F₁ hd₀ hd₁ Fd₀ f hf hfd hfdp hf₀ hhom

end RelocatedS32

end LiZhongQC
