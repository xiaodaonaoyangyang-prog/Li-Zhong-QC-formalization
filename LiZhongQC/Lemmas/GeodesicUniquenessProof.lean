import LiZhongQC.Lemmas.GeodesicBigonExclusion
import LiZhongQC.Lemmas.GeodesicSimpleLoop
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Actual geodesic injectivity and actual bigon exclusion imply trace
containment. All smooth-side and corner data are produced by the consumers;
the statement has only the book's original geodesic hypotheses. -/
theorem s25bg_trace_subset {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (h₁ : IsPhiGeodesic φ unitDisc γ₁) (h₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1) :
    γ₁.closedTrace ⊆ γ₂.closedTrace := by
  have hi₁ := s25sl_geodesic_injective hφ hne h₁ hp₁
  have hi₂ := s25sl_geodesic_injective hφ hne h₂ hp₂
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  intro z hz
  by_contra hoffz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨a, b, u, v, ha, hab, hb, hu, hv, huv, he0, he1, hoff⟩ :=
    s25gb_bigon_parameters hK₁.continuousOn hK₂.continuousOn hi₁ h0 h1 ⟨x, hx, hoffz⟩
  exact s25bg_bigon_excluded hφ hne h₁ h₂ hp₁ hp₂ hi₁ hi₂ ha hab hb hu hv huv he0 he1 hoff


end LiZhongQC

