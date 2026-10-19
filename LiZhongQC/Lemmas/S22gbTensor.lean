import LiZhongQC.Lemmas.S22gbPoint

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetTensor

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The canonical gauge is real-linear in its vector argument. -/
theorem s22gb_cG_linear (ψ f : ℂ → ℂ) (w v : ℂ) :
    s22cd_canonicalGauge ψ f w v =
      v.re * s22cd_canonicalGauge ψ f w 1 + v.im * s22cd_canonicalGauge ψ f w I := by
  simp only [s22cd_canonicalGauge, s22gt_chartConnection, s22gc_connectionForm, s22gt_phaseForm,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_zero]
  ring

/-- Tensor law of the gauge family at an order-zero point, for two charts. The right-hand side
uses the real-linear expansion in the basis `1, I` (the family is only constrained on these two
directions at junk points). -/
theorem s22gb_tensor_law {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    (hq : IsDiffFamily 1 0 q) {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (x y : S) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source)
    (hm : MeromorphicAt (q x) z) (ho : meromorphicOrderAt (q x) z = 0)
    (hmy : MeromorphicAt (q y) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z))
    (hoy : meromorphicOrderAt (q y) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) = 0) (v : ℂ) :
    α x z v = (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z * v).re *
        α y ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) 1 +
      (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z * v).im *
        α y ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) I := by
  set τ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm with hτ
  set u := (chartAt ℂ x).symm z with hu
  have hux : u ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hzc : chartAt ℂ x u = z := (chartAt ℂ x).right_inv hz
  have hτan : AnalyticAt ℂ τ z := by
    have := Jacobians.Dolbeault.transition_analyticAt_of_mem hux hzy
    rwa [hzc] at this
  have hτd : deriv τ z ≠ 0 := by
    have := Jacobians.Dolbeault.transition_deriv_ne_zero hux hzy
    rwa [hzc] at this
  have hmap : Tendsto τ (𝓝[≠] z) (𝓝[≠] (τ z)) :=
    tendsto_nhdsWithin_iff.2 ⟨hτan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hτan.differentiableAt.hasDerivAt.eventually_ne hτd⟩
  have hhx := s22gb_honest_nhdsNE hm ho
  have hhy := hmap.eventually (s22gb_honest_nhdsNE hmy hoy)
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source ∧ deriv τ w ≠ 0 ∧ AnalyticAt ℂ τ w := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz,
      ((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds
        ((chartAt ℂ y).open_source.mem_nhds hzy),
      hτan.deriv.continuousAt.eventually_ne hτd, hτan.eventually_analyticAt] with w a b c d
    exact ⟨a, b, c, d⟩
  have hlawG : ∀ᶠ ζ in 𝓝 z, q x ζ = q y (τ ζ) * deriv τ ζ := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz,
      ((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds
        ((chartAt ℂ y).open_source.mem_nhds hzy)] with ζ h1 h2
    have h := hq.2 y x ζ h1 h2
    rw [h]
    simp only [zpow_one, zpow_zero, mul_one]
    show q y (chartTransition y x ζ) * deriv (chartTransition y x) ζ =
      q y (chartTransition y x ζ) * deriv (chartTransition y x) ζ
    rfl
  -- pointwise law at honest points
  have hpt : ∀ᶠ w in 𝓝[≠] z, α x w v = (deriv τ w * v).re * α y (τ w) 1 +
      (deriv τ w * v).im * α y (τ w) I := by
    filter_upwards [hhx, hhy, nhdsWithin_le_nhds hnear.eventually_nhds,
      nhdsWithin_le_nhds hlawG.eventually_nhds, nhdsWithin_le_nhds hnear] with w hw hwy hn1 hl hn
    obtain ⟨hwt, hws, hwd, hwan⟩ := hn
    have hτw : τ w ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hws
    obtain ⟨ψy, hψan, hψd, hψH, hψe⟩ := s22gb_local_lift hp y hτw
    have hψ'an : AnalyticAt ℂ (ψy ∘ τ) w := hψan.comp hwan
    have hψ'd : deriv (ψy ∘ τ) w ≠ 0 := by
      rw [deriv_comp w hψan.differentiableAt hwan.differentiableAt]
      exact mul_ne_zero hψd hwd
    have hψ'e : (fun ζ => s22gm_projectionExtension p ((ψy ∘ τ) ζ)) =ᶠ[𝓝 w]
        fun ζ => (chartAt ℂ x).symm ζ := by
      have h1 := hwan.continuousAt.tendsto.eventually hψe
      filter_upwards [h1, hn1] with ζ a b
      have hs : (chartAt ℂ x).symm ζ ∈ (chartAt ℂ y).source := b.2.1
      have : (chartAt ℂ y).symm (τ ζ) = (chartAt ℂ x).symm ζ := (chartAt ℂ y).left_inv hs
      exact a.trans this
    have hαx := hα x w hwt hw.1 hw.2 (ψy ∘ τ) hψ'an hψ'd hψH hψ'e
    have hαy := hα y (τ w) hτw hwy.1 hwy.2 ψy hψan hψd hψH hψe
    have hl' : q x =ᶠ[𝓝 w] fun ζ => q y (τ ζ) * deriv τ ζ := hl
    have hxw : α x w v = s22cd_canonicalGauge ψy (q y) (τ w) (deriv τ w * v) := by
      have e1 : α x w v = s22cd_canonicalGauge (ψy ∘ τ) (q x) w v :=
        congrFun hαx.self_of_nhds v
      rw [e1, s22cd_canonicalGauge_germ_congr (Filter.EventuallyEq.refl _ _) hl' v]
      exact s22cd_canonicalGauge_comp hψan hwy.1 hwan hψd hwy.2 hwd v
    have hyw : α y (τ w) = s22cd_canonicalGauge ψy (q y) (τ w) := hαy.self_of_nhds
    rw [hxw, hyw, s22gb_cG_linear ψy (q y) (τ w) (deriv τ w * v)]
  -- pass to the limit at `z`
  have hc1 : ContinuousAt (fun w => α x w v) z := (hsm x z hz hm ho v).continuousAt
  have hτy : τ z ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hzy
  have hcy : ∀ v' : ℂ, ContinuousAt (fun w => α y (τ w) v') z := by
    intro v'
    have h := (hsm y (τ z) hτy hmy hoy v').continuousAt
    exact ContinuousAt.comp (f := τ) (g := fun w => α y w v') h hτan.continuousAt
  have hc2 : ContinuousAt (fun w => (deriv τ w * v).re * α y (τ w) 1 +
      (deriv τ w * v).im * α y (τ w) I) z := by
    have hd : ContinuousAt (fun w => deriv τ w * v) z := hτan.deriv.continuousAt.mul continuousAt_const
    exact ((Complex.continuous_re.continuousAt.comp hd).mul (hcy 1)).add
      ((Complex.continuous_im.continuousAt.comp hd).mul (hcy I))
  exact tendsto_nhds_unique_of_eventuallyEq (hc1.tendsto.mono_left nhdsWithin_le_nhds)
    (hc2.tendsto.mono_left nhdsWithin_le_nhds) hpt

end GaussBonnetTensor

end LiZhongQC
