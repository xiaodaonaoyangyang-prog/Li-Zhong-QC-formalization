import LiZhongQC.Lemmas.S22gbTransport

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetPoint

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

theorem s22gb_deriv_line {f : ℂ → ℝ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (d : ℂ) :
    deriv (fun t : ℝ => f (z + (t : ℂ) * d)) 0 = fderiv ℝ f z d := by
  have h := td_hasDerivAt_line z d 0
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h (by simp)
  exact h2.deriv

theorem s22gb_deriv_line_one {f : ℂ → ℝ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    deriv (fun t : ℝ => f (z + (t : ℂ))) 0 = fderiv ℝ f z 1 := by
  have := s22gb_deriv_line hf 1
  simpa only [mul_one] using this

/-- Near an order-zero point `z`, all other points are honest. -/
theorem s22gb_honest_nhdsNE {f : ℂ → ℂ} {z : ℂ} (hm : MeromorphicAt f z)
    (ho : meromorphicOrderAt f z = 0) :
    ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w ∧ f w ≠ 0 := by
  have h1 : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := hm.eventually_analyticAt
  have h2 : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).1 (by rw [ho]; exact WithTop.coe_ne_top)
  filter_upwards [h1, h2] with w a b
  exact ⟨a, b⟩

/-- The exterior derivative of the canonical gauge family at an order-zero point equals the area
density of any lift (honest points by the local calculation, the order-zero point by continuity). -/
theorem s22gb_exterior_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (x : S) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) (hm : MeromorphicAt (q x) z)
    (ho : meromorphicOrderAt (q x) z = 0) {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ z)
    (hd : deriv ψ z ≠ 0) (hH : ψ z ∈ upperHalf)
    (he : (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w) :
    fderiv ℝ (fun w => α x w I) z 1 - fderiv ℝ (fun w => α x w 1) z I =
      s22gc_areaDensity ψ z := by
  have hopen := isOpen_upperHalf'
  -- smoothness of the two components near `z`
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ x).target := (chartAt ℂ x).open_target.mem_nhds hz
  have hsmooth : ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z := hsm x z hz hm ho
  -- the difference is continuous at `z`
  have hcont : ContinuousAt (fun w => fderiv ℝ (fun w => α x w I) w 1 -
      fderiv ℝ (fun w => α x w 1) w I) z := by
    have h1 := ((hsmooth I).fderiv_right (m := 0) (by simp)).continuousAt
    have h2 := ((hsmooth 1).fderiv_right (m := 0) (by simp)).continuousAt
    exact (h1.clm_apply continuousAt_const).sub (h2.clm_apply continuousAt_const)
  have hcont2 : ContinuousAt (s22gc_areaDensity ψ) z :=
    s22gc_areaDensity_continuousAt hψ (show 0 < (ψ z).im from hH)
  -- agreement on the punctured neighbourhood
  have hagree : ∀ᶠ w in 𝓝[≠] z, fderiv ℝ (fun w => α x w I) w 1 -
      fderiv ℝ (fun w => α x w 1) w I = s22gc_areaDensity ψ w := by
    have hhon := s22gb_honest_nhdsNE hm ho
    have hψev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ ψ w ∧ deriv ψ w ≠ 0 ∧ ψ w ∈ upperHalf := by
      filter_upwards [hψ.eventually_analyticAt, hψ.deriv.continuousAt.eventually_ne hd,
        hψ.continuousAt.preimage_mem_nhds (hopen.mem_nhds hH)] with w h1 h2 h3
      exact ⟨h1, h2, h3⟩
    filter_upwards [hhon, nhdsWithin_le_nhds hψev, nhdsWithin_le_nhds hnear,
      nhdsWithin_le_nhds he.eventually_nhds] with w hw hψw htw hew
    have hew' : (fun u => s22gm_projectionExtension p (ψ u)) =ᶠ[𝓝 w]
        fun u => (chartAt ℂ x).symm u := hew
    have hg := hα x w htw hw.1 hw.2 ψ hψw.1 hψw.2.1 hψw.2.2 hew'
    have hy : (ψ w).im ≠ 0 := ne_of_gt (show 0 < (ψ w).im from hψw.2.2)
    have hcgI := (s22gb_canonicalGauge_contDiffAt hψw.1 hψw.2.1 hy hw.1 hw.2 I).differentiableAt
      one_ne_zero
    have hcg1 := (s22gb_canonicalGauge_contDiffAt hψw.1 hψw.2.1 hy hw.1 hw.2 1).differentiableAt
      one_ne_zero
    have hext := s22cd_exterior_canonicalGauge hψw.1 hψw.2.1 hy hw.1 hw.2 1 I
    have e1 : deriv (fun t : ℝ => s22cd_canonicalGauge ψ (q x) (w + (t : ℂ)) I) 0 =
        fderiv ℝ (fun u => s22cd_canonicalGauge ψ (q x) u I) w 1 := s22gb_deriv_line_one hcgI
    have e2 : deriv (fun t : ℝ => s22cd_canonicalGauge ψ (q x) (w + (t : ℂ) * I) 1) 0 =
        fderiv ℝ (fun u => s22cd_canonicalGauge ψ (q x) u 1) w I := s22gb_deriv_line hcg1 I
    rw [s22gc_exteriorDerivative, e1, e2] at hext
    simp only [s22gc_areaForm, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, sub_zero] at hext
    have fe : ∀ v, fderiv ℝ (fun u => α x u v) w =
        fderiv ℝ (fun u => s22cd_canonicalGauge ψ (q x) u v) w := fun v =>
      Filter.EventuallyEq.fderiv_eq (hg.mono fun u hu => congrFun hu v)
    rw [fe I, fe 1]
    exact hext
  have h1 : Tendsto (fun w => fderiv ℝ (fun w => α x w I) w 1 -
      fderiv ℝ (fun w => α x w 1) w I) (𝓝[≠] z) _ := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (s22gc_areaDensity ψ) (𝓝[≠] z) _ := hcont2.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq h1 h2 hagree

end GaussBonnetPoint

end LiZhongQC
