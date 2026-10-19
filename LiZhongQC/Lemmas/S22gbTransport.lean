import LiZhongQC.Lemmas.S22gbLift

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetTransport

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The transition `chart_y ∘ chart_x⁻¹` is analytic and unramified at the image of `y`; the
coefficient of a differential transforms by the derivative: `q_x = (q_y ∘ τ) τ'` near `z`. -/
theorem s22gb_transport_eq {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q) (x : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    AnalyticAt ℂ (chartAt ℂ ((chartAt ℂ x).symm z) ∘ (chartAt ℂ x).symm) z ∧
      deriv (chartAt ℂ ((chartAt ℂ x).symm z) ∘ (chartAt ℂ x).symm) z ≠ 0 ∧
      (chartAt ℂ ((chartAt ℂ x).symm z) ∘ (chartAt ℂ x).symm) z =
        chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z) ∧
      q x =ᶠ[𝓝 z] fun w =>
        deriv (chartAt ℂ ((chartAt ℂ x).symm z) ∘ (chartAt ℂ x).symm) w *
          q ((chartAt ℂ x).symm z) ((chartAt ℂ ((chartAt ℂ x).symm z) ∘ (chartAt ℂ x).symm) w) := by
  set y := (chartAt ℂ x).symm z with hy
  have hysrc : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hzc : chartAt ℂ x y = z := (chartAt ℂ x).right_inv hz
  have han : AnalyticAt ℂ (chartAt ℂ y ∘ (chartAt ℂ x).symm) z := by
    have := Jacobians.Dolbeault.transition_analyticAt_of_mem hysrc (mem_chart_source ℂ y)
    rwa [hzc] at this
  have hd : deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z ≠ 0 := by
    have := Jacobians.Dolbeault.transition_deriv_ne_zero hysrc (mem_chart_source ℂ y)
    rwa [hzc] at this
  refine ⟨han, hd, rfl, ?_⟩
  have hpre : ∀ᶠ w in 𝓝 z, (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source :=
    ((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz, hpre] with w hw hws
  have h := hq.2 y x w hw hws
  rw [h]
  simp only [zpow_one, zpow_zero, mul_one]
  show q y (chartTransition y x w) * deriv (chartTransition y x) w =
    deriv (chartTransition y x) w * q y (chartTransition y x w)
  ring

/-- Meromorphy and order of the coefficient at an arbitrary point of a chart are those at the
centre of the preferred chart of that point. -/
theorem s22gb_order_transport {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q)
    (hmer : ∀ x, MeromorphicAt (q x) (chartAt ℂ x x)) (x : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z =
      meromorphicOrderAt (q ((chartAt ℂ x).symm z))
        (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) := by
  obtain ⟨han, hd, hτz, hev⟩ := s22gb_transport_eq hq x hz
  set y := (chartAt ℂ x).symm z with hy
  set τ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm with hτ
  have hm1 : MeromorphicAt (q y ∘ τ) z := by
    refine MeromorphicAt.comp_analyticAt ?_ han
    rw [hτz]
    exact hmer y
  have hm2 : MeromorphicAt (deriv τ * (q y ∘ τ)) z := han.deriv.meromorphicAt.mul hm1
  have hcongr : q x =ᶠ[𝓝[≠] z] deriv τ * (q y ∘ τ) :=
    (hev.filter_mono nhdsWithin_le_nhds)
  refine ⟨hm2.congr hcongr.symm, ?_⟩
  rw [meromorphicOrderAt_congr hcongr,
    meromorphicOrderAt_mul_of_ne_zero han.deriv hd,
    meromorphicOrderAt_comp_of_deriv_ne_zero han hd, hτz]

end GaussBonnetTransport

end LiZhongQC
