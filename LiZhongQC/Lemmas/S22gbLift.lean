import LiZhongQC.Lemmas.HurwitzProofChain
import LiZhongQC.Lemmas.HyperbolicAreaFundamentalDomain
import LiZhongQC.Lemmas.CanonicalBoundaryLimit
import LiZhongQC.Lemmas.ChartPartitionStokes

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetLift

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- (P2a) Local analytic lifts of the chart inverses through the uniformization:
`p ∘ ψ = (chart x)⁻¹` near `z`, `ψ` analytic, unramified, valued in the upper half plane. -/
theorem s22gb_local_lift {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (x : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 ∧ ψ z ∈ upperHalf ∧
      (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w := by
  obtain ⟨τ, hτ⟩ := hp.2.2.1 ((chartAt ℂ x).symm z)
  have hsrc : p τ ∈ (chartAt ℂ x).source := by
    rw [hτ]; exact (chartAt ℂ x).map_target hz
  obtain ⟨e, hτe, hpe⟩ := hp.1.isLocalHomeomorph τ
  set W : Set UpperHalfPlane := e.source ∩ p ⁻¹' (chartAt ℂ x).source with hWdef
  have hWo : IsOpen W := e.open_source.inter
    (hp.1.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)
  set U : Set ℂ := upperHalf ∩ UpperHalfPlane.ofComplex ⁻¹' W with hUdef
  have hsrcU : UpperHalfPlane.ofComplex.source = upperHalf := by
    ext w
    simp [UpperHalfPlane.ofComplex, upperHalf]
  have hUo : IsOpen U := by
    have h := UpperHalfPlane.ofComplex.isOpen_inter_preimage hWo
    rwa [hsrcU] at h
  have hτU : (τ : ℂ) ∈ U := by
    refine ⟨τ.coe_im_pos, ?_⟩
    show UpperHalfPlane.ofComplex (τ : ℂ) ∈ W
    rw [UpperHalfPlane.ofComplex_apply]
    exact ⟨hτe, hsrc⟩
  set f : ℂ → ℂ := fun w => chartAt ℂ x (p (UpperHalfPlane.ofComplex w)) with hfdef
  have hfd : DifferentiableOn ℂ f U := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f w :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hw.2.2).comp w
        ((hp.2.1 _).comp w (UpperHalfPlane.mdifferentiableAt_ofComplex hw.1))
    exact (mdifferentiableAt_iff_differentiableAt.1 h1).differentiableWithinAt
  have hfi : InjOn f U := by
    intro w hw w' hw' hww
    have h1 : p (UpperHalfPlane.ofComplex w) = p (UpperHalfPlane.ofComplex w') :=
      (chartAt ℂ x).injOn hw.2.2 hw'.2.2 hww
    rw [hpe] at h1
    have h2 := e.injOn hw.2.1 hw'.2.1 h1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw.1,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw'.1] at h2
    exact congrArg UpperHalfPlane.coe h2
  have hfz : f (τ : ℂ) = z := by
    show chartAt ℂ x (p (UpperHalfPlane.ofComplex (τ : ℂ))) = z
    rw [UpperHalfPlane.ofComplex_apply, hτ]
    exact (chartAt ℂ x).right_inv hz
  have hder : deriv f (τ : ℂ) ≠ 0 := deriv_ne_zero_of_injOn hUo hfd hfi hτU
  have hfan : AnalyticAt ℂ f (τ : ℂ) := hfd.analyticAt (hUo.mem_nhds hτU)
  have hs : HasStrictDerivAt f (deriv f (τ : ℂ)) (τ : ℂ) := hfan.hasStrictDerivAt
  have hL := hs.to_localInverse hder
  have hLl := hs.eventually_left_inverse hder
  have hLr := hs.eventually_right_inverse hder
  have hψτ : hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder (f (τ : ℂ)) = (τ : ℂ) :=
    hLl.self_of_nhds
  have hψan : AnalyticAt ℂ (hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder) (f (τ : ℂ)) :=
    hfan.analyticAt_localInverse hder
  rw [hfz] at hψτ hψan hLr hL
  refine ⟨hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder, hψan, ?_, ?_, ?_⟩
  · rw [hL.hasDerivAt.deriv]
    exact inv_ne_zero hder
  · rw [hψτ]
    exact τ.coe_im_pos
  · have hUev : ∀ᶠ w in 𝓝 z, hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder w ∈ U :=
      hψan.continuousAt.preimage_mem_nhds (by rw [hψτ]; exact hUo.mem_nhds hτU)
    filter_upwards [hLr, hUev] with w hw1 hw2
    have hmem : p (UpperHalfPlane.ofComplex
        (hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder w)) ∈ (chartAt ℂ x).source := hw2.2.2
    have hc : chartAt ℂ x (p (UpperHalfPlane.ofComplex
        (hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder w))) = w := hw1
    change p (UpperHalfPlane.ofComplex
        (hs.localInverse f (deriv f (τ : ℂ)) (τ : ℂ) hder w)) = (chartAt ℂ x).symm w
    exact ((chartAt ℂ x).left_inv hmem).symm.trans (congrArg (chartAt ℂ x).symm hc)

/-- The phase form of an analytic nonvanishing coefficient is smooth. -/
theorem s22gb_phase_contDiffAt {h : ℂ → ℂ} {z : ℂ} (hh : AnalyticAt ℂ h z) (hn : h z ≠ 0)
    (v : ℂ) : ContDiffAt ℝ 1 (fun w => s22gt_phaseForm h w v) z := by
  have hF : AnalyticAt ℂ (fun w => deriv h w / h w) z := hh.deriv.div hh hn
  have h1 : ContDiffAt ℝ 1 (fun w => deriv h w / h w) z :=
    (hF.contDiffAt (n := 1)).restrict_scalars ℝ
  exact Complex.imCLM.contDiff.comp_contDiffAt z (h1.mul contDiffAt_const)

/-- The coordinate connection of an analytic unramified lift is smooth. -/
theorem s22gb_chartConnection_contDiffAt {ψ : ℂ → ℂ} {z : ℂ} (hψ : AnalyticAt ℂ ψ z)
    (hd : deriv ψ z ≠ 0) (hy : (ψ z).im ≠ 0) (v : ℂ) :
    ContDiffAt ℝ 1 (fun w => s22gt_chartConnection ψ w v) z := by
  have h1 : ContDiffAt ℝ 1 ψ z := (hψ.contDiffAt (n := 1)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 1 (deriv ψ) z := (hψ.deriv.contDiffAt (n := 1)).restrict_scalars ℝ
  have hnum : ContDiffAt ℝ 1 (fun w => (deriv ψ w * v).re) z :=
    Complex.reCLM.contDiff.comp_contDiffAt z (h2.mul contDiffAt_const)
  have hden : ContDiffAt ℝ 1 (fun w => (ψ w).im) z := Complex.imCLM.contDiff.comp_contDiffAt z h1
  exact (hnum.div hden hy).add (s22gb_phase_contDiffAt hψ.deriv hd v)

/-- The canonical gauge of an analytic lift and an analytic nonvanishing coefficient is smooth. -/
theorem s22gb_canonicalGauge_contDiffAt {ψ f : ℂ → ℂ} {z : ℂ} (hψ : AnalyticAt ℂ ψ z)
    (hd : deriv ψ z ≠ 0) (hy : (ψ z).im ≠ 0) (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0) (v : ℂ) :
    ContDiffAt ℝ 1 (fun w => s22cd_canonicalGauge ψ f w v) z :=
  (s22gb_chartConnection_contDiffAt hψ hd hy v).sub (s22gb_phase_contDiffAt hf hn v)

/-- The canonical gauge does not depend on the choice of the lift. -/
theorem s22gb_canonicalGauge_lift_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {ψ χ f : ℂ → ℂ} {w : ℂ}
    (hψ : AnalyticAt ℂ ψ w) (hd : deriv ψ w ≠ 0) (hχ : ContinuousAt χ w)
    (hψH : ψ w ∈ upperHalf) (hχH : χ w ∈ upperHalf)
    (he : (fun u => s22gm_projectionExtension p (ψ u)) =ᶠ[𝓝 w]
      (fun u => s22gm_projectionExtension p (χ u))) (v : ℂ) :
    s22cd_canonicalGauge χ f w v = s22cd_canonicalGauge ψ f w v := by
  unfold s22cd_canonicalGauge
  rw [s22gt_lift_chartConnection_eq hp hψ hd hχ hψH hχH he v]

/-- (P2a) The canonical gauge as a family of real one-forms in the preferred charts. It is the
phase-corrected connection of ANY local lift off the zeros and poles of `q`; the family is
independent of the lift (overlap law of `s22cd_surface_canonicalGauge_overlap`). The extra
conjunct says it is `C¹` at every point where `q x` is meromorphic of order `0` (the normal
form removes isolated junk values of `q x`). -/
theorem s22gb_gauge_exists {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q) :
    ∃ α : S → ℂ → ℂ → ℝ,
      (∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
        AnalyticAt ℂ (q x) z → q x z ≠ 0 →
        ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
          (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
          α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x)) ∧
      (∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
        meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z) := by
  classical
  have _hq := hq
  have hex : ∀ (x : S) (z : ℂ), (z ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) z ∧
      meromorphicOrderAt (q x) z = 0) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 ∧ ψ z ∈ upperHalf ∧
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w :=
    fun x z h => s22gb_local_lift hp x h.1
  have hopen := isOpen_upperHalf'
  -- normal-form facts at an order-zero point
  have hnf : ∀ (x : S) (z : ℂ), MeromorphicAt (q x) z → meromorphicOrderAt (q x) z = 0 →
      AnalyticAt ℂ (toMeromorphicNFAt (q x) z) z ∧ toMeromorphicNFAt (q x) z z ≠ 0 ∧
        q x =ᶠ[𝓝[≠] z] toMeromorphicNFAt (q x) z := by
    intro x z hm ho
    exact ⟨(hm.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).1 (ho ▸ le_rfl),
      (hm.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).1 ho,
      hm.eq_nhdsNE_toMeromorphicNFAt⟩
  obtain ⟨α, hαdef⟩ : ∃ α : S → ℂ → ℂ → ℝ, ∀ x z v, α x z v =
      if h : z ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) z ∧
          meromorphicOrderAt (q x) z = 0 then
        s22cd_canonicalGauge (Classical.choose (hex x z h)) (toMeromorphicNFAt (q x) z) z v
      else 0 := ⟨_, fun _ _ _ => rfl⟩
  -- the key germ identity at an order-zero point
  have hgerm : ∀ (x : S) (z : ℂ) (h : z ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) z ∧
      meromorphicOrderAt (q x) z = 0),
      α x =ᶠ[𝓝 z] s22cd_canonicalGauge (Classical.choose (hex x z h))
        (toMeromorphicNFAt (q x) z) := by
    intro x z h
    obtain ⟨hψan, hψd, hψH, hψe⟩ := Classical.choose_spec (hex x z h)
    generalize hψz : Classical.choose (hex x z h) = ψz at hψan hψd hψH hψe
    obtain ⟨hgan, hgne, hgeq⟩ := hnf x z h.2.1 h.2.2
    generalize hg : toMeromorphicNFAt (q x) z = g at hgan hgne hgeq
    have hψev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ ψz w ∧ deriv ψz w ≠ 0 ∧ ψz w ∈ upperHalf := by
      filter_upwards [hψan.eventually_analyticAt, hψan.deriv.continuousAt.eventually_ne hψd,
        hψan.continuousAt.preimage_mem_nhds (hopen.mem_nhds hψH)] with w h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hgev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g w ∧ g w ≠ 0 := by
      filter_upwards [hgan.eventually_analyticAt, hgan.continuousAt.eventually_ne hgne]
        with w h1 h2
      exact ⟨h1, h2⟩
    have htev : ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).open_target.mem_nhds h.1
    have hgeq' : ∀ᶠ w in 𝓝 z, w ≠ z → q x =ᶠ[𝓝 w] g := by
      obtain ⟨t, ht, hto, hzt⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hgeq)
      filter_upwards [hto.mem_nhds hzt] with w hw hwz
      filter_upwards [(hto.sdiff isClosed_singleton).mem_nhds ⟨hw, hwz⟩] with u hu
      exact ht u hu.1 hu.2
    filter_upwards [hψev, hgev, htev, hψe.eventually_nhds, hgeq'] with w hψw hgw htw hew hqw
    by_cases hwz : w = z
    · subst hwz
      funext v
      rw [hαdef, dif_pos h, hψz, hg]
    · have hqe := hqw hwz
      have hmer : MeromorphicAt (q x) w :=
        hgw.1.meromorphicAt.congr (hqe.symm.filter_mono nhdsWithin_le_nhds)
      have hord : meromorphicOrderAt (q x) w = 0 := by
        rw [meromorphicOrderAt_congr (hqe.filter_mono nhdsWithin_le_nhds)]
        exact (hgw.1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hgw.2
      have hw' : w ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) w ∧
          meromorphicOrderAt (q x) w = 0 := ⟨htw, hmer, hord⟩
      have hnfe : toMeromorphicNFAt (q x) w =ᶠ[𝓝 w] g := by
        have h1 := toMeromorphicNFAt_eventuallyEq_nhds_congr
          (f := q x) (g := g) (x := w) (hqe.filter_mono nhdsWithin_le_nhds)
        rwa [toMeromorphicNFAt_eq_self.2 hgw.1.meromorphicNFAt] at h1
      obtain ⟨hχan, hχd, hχH, hχe⟩ := Classical.choose_spec (hex x w hw')
      have hew' : (fun u => s22gm_projectionExtension p (ψz u)) =ᶠ[𝓝 w]
          fun u => (chartAt ℂ x).symm u := hew
      funext v
      rw [hαdef, dif_pos hw']
      rw [s22cd_canonicalGauge_germ_congr (Filter.EventuallyEq.refl _ _) hnfe v]
      exact s22gb_canonicalGauge_lift_eq hp hψw.1 hψw.2.1 hχan.continuousAt hψw.2.2 hχH
        (hew'.trans hχe.symm) v
  refine ⟨α, ?_, ?_⟩
  · intro x z hz hqa hqn ψ hψ hdψ hψH he
    have hmer : MeromorphicAt (q x) z := hqa.meromorphicAt
    have hord : meromorphicOrderAt (q x) z = 0 :=
      (hqa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hqn
    have h : z ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0 :=
      ⟨hz, hmer, hord⟩
    have hself : toMeromorphicNFAt (q x) z = q x := toMeromorphicNFAt_eq_self.2 hqa.meromorphicNFAt
    have hg := hgerm x z h
    rw [hself] at hg
    obtain ⟨hψan, hψd, hψH', hψe⟩ := Classical.choose_spec (hex x z h)
    generalize hψz : Classical.choose (hex x z h) = ψz at hg hψan hψd hψH' hψe
    have hψev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ ψ w ∧ deriv ψ w ≠ 0 ∧ ψ w ∈ upperHalf := by
      filter_upwards [hψ.eventually_analyticAt, hψ.deriv.continuousAt.eventually_ne hdψ,
        hψ.continuousAt.preimage_mem_nhds (hopen.mem_nhds hψH)] with w h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hzev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ ψz w ∧ ψz w ∈ upperHalf := by
      filter_upwards [hψan.eventually_analyticAt,
        hψan.continuousAt.preimage_mem_nhds (hopen.mem_nhds hψH')] with w h1 h3
      exact ⟨h1, h3⟩
    refine hg.trans ?_
    filter_upwards [hψev, hzev, he.eventually_nhds, hψe.eventually_nhds] with w hw1 hw2 hw3 hw4
    funext v
    have he1 : (fun u => s22gm_projectionExtension p (ψ u)) =ᶠ[𝓝 w]
        fun u => (chartAt ℂ x).symm u := hw3
    have he2 : (fun u => s22gm_projectionExtension p (ψz u)) =ᶠ[𝓝 w]
        fun u => (chartAt ℂ x).symm u := hw4
    exact s22gb_canonicalGauge_lift_eq hp hw1.1 hw1.2.1 hw2.1.continuousAt hw1.2.2 hw2.2
      (he1.trans he2.symm) v
  · intro x z hz hmer hord v
    have h : z ∈ (chartAt ℂ x).target ∧ MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0 :=
      ⟨hz, hmer, hord⟩
    obtain ⟨hgan, hgne, -⟩ := hnf x z hmer hord
    have hg := hgerm x z h
    obtain ⟨hψan, hψd, hψH, -⟩ := Classical.choose_spec (hex x z h)
    have hsm := s22gb_canonicalGauge_contDiffAt hψan hψd (ne_of_gt hψH) hgan hgne v
    exact hsm.congr_of_eventuallyEq (hg.mono fun w hw => by simp only [hw])

end GaussBonnetLift

end LiZhongQC
