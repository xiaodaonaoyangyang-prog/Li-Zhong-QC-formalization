import LiZhongQC.Lemmas.GeodesicLift
/-! Pairwise covering-lift data for the uniqueness half of 25.4.
This module contains no use of the unproved planar uniqueness theorem. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

namespace LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Equality of the closed planar traces of two lifts descends to equality of the
original path ranges. Every parameter in the closed interval is retained. -/
theorem s25w_range_eq_of_lift_closedTrace_eq
    {p : UpperHalfPlane → S} {a b : S} (γ₁ γ₂ : Path a b)
    (γ₁' γ₂' : C(unitInterval, UpperHalfPlane))
    (h₁ : ∀ t, p (γ₁' t) = γ₁ t) (h₂ : ∀ t, p (γ₂' t) = γ₂ t)
    (c₁ c₂ : LRCurve)
    (hc₁ : ∀ t : ℝ, c₁.toFun t = (γ₁' (Set.projIcc 0 1 zero_le_one t) : ℂ))
    (hc₂ : ∀ t : ℝ, c₂.toFun t = (γ₂' (Set.projIcc 0 1 zero_le_one t) : ℂ))
    (htrace : c₁.closedTrace = c₂.closedTrace) :
    range γ₁ = range γ₂ := by
  have hsub : ∀ (α β : Path a b) (α' β' : C(unitInterval, UpperHalfPlane))
      (d e : LRCurve),
      (∀ t, p (α' t) = α t) → (∀ t, p (β' t) = β t) →
      (∀ t : ℝ, d.toFun t = (α' (Set.projIcc 0 1 zero_le_one t) : ℂ)) →
      (∀ t : ℝ, e.toFun t = (β' (Set.projIcc 0 1 zero_le_one t) : ℂ)) →
      d.closedTrace ⊆ e.closedTrace → range α ⊆ range β := by
    intro α β α' β' d e hα hβ hd he hde
    rintro _ ⟨t, rfl⟩
    have hmem : d.toFun (t : ℝ) ∈ e.closedTrace :=
      hde ⟨(t : ℝ), t.property, rfl⟩
    rcases hmem with ⟨s, _hs, hst⟩
    have hcoe :
        (β' (Set.projIcc 0 1 zero_le_one s) : ℂ) = (α' t : ℂ) := by
      have h := (he s).symm.trans (hst.trans (hd (t : ℝ)))
      rw [Set.projIcc_val] at h
      exact h
    have hproj := congrArg p (UpperHalfPlane.coe_injective hcoe)
    rw [hα, hβ] at hproj
    exact ⟨Set.projIcc 0 1 zero_le_one s, hproj⟩
  exact subset_antisymm
    (hsub γ₁ γ₂ γ₁' γ₂' c₁ c₂ h₁ h₂ hc₁ hc₂ htrace.subset)
    (hsub γ₂ γ₁ γ₂' γ₁' c₂ c₁ h₂ h₁ hc₂ hc₁ htrace.symm.subset)

/-- Two homotopic non-pausing surface geodesics have actual upper-half-plane
geodesic lifts with the same endpoints. Equality of their planar traces is the
only conclusion still needed to identify their surface traces. -/
theorem s25w_pair_lifts_of_uniformization
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} (γ₁ γ₂ : Path a b)
    (hhom : γ₁.Homotopic γ₂)
    (hgeo₁ : IsPhiGeodesicRS q γ₁) (hgeo₂ : IsPhiGeodesicRS q γ₂)
    (hno₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s)
    (hno₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) :
    ∃ c₁ c₂ : LRCurve,
      IsPhiGeodesic (utm_liftQD q p) upperHalf c₁ ∧
      IsPhiGeodesic (utm_liftQD q p) upperHalf c₂ ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, c₁.toFun u ≠ c₁.toFun s) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, c₂.toFun u ≠ c₂.toFun s) ∧
      c₁.toFun 0 = c₂.toFun 0 ∧ c₁.toFun 1 = c₂.toFun 1 ∧
      (c₁.closedTrace = c₂.closedTrace → range γ₁ = range γ₂) := by
  obtain ⟨z, hz⟩ := hp.2.2.1 a
  obtain ⟨γ₁', c₁, h10, h₁, hc₁, hGe₁, _hL₁⟩ :=
    s25v_exists_geodesic_lift hq hne hp hgeo₁ z hz
  obtain ⟨γ₂', c₂, h20, h₂, hc₂, hGe₂, _hL₂⟩ :=
    s25v_exists_geodesic_lift hq hne hp hgeo₂ z hz
  have hstart : γ₁' 0 = γ₂' 0 := h10.trans h20.symm
  have hend : γ₁' 1 = γ₂' 1 :=
    s25v_homotopic_lift_endpoints hp γ₁ γ₂ hhom γ₁' γ₂' h₁ h₂ hstart
  refine ⟨c₁, c₂, hGe₁, hGe₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hs hst ht
    obtain ⟨u, hu, hne⟩ := s25v_lift_no_pause γ₁ γ₁' h₁ hno₁ s t hs hst ht
    exact ⟨u, hu, by simpa only [hc₁] using hne⟩
  · intro s t hs hst ht
    obtain ⟨u, hu, hne⟩ := s25v_lift_no_pause γ₂ γ₂' h₂ hno₂ s t hs hst ht
    exact ⟨u, hu, by simpa only [hc₂] using hne⟩
  · rw [hc₁, hc₂, Set.projIcc_left]
    exact congrArg (fun w : UpperHalfPlane => (w : ℂ)) hstart
  · rw [hc₁, hc₂, Set.projIcc_right]
    exact congrArg (fun w : UpperHalfPlane => (w : ℂ)) hend
  · exact s25w_range_eq_of_lift_closedTrace_eq γ₁ γ₂ γ₁' γ₂' h₁ h₂ c₁ c₂ hc₁ hc₂

/-- Hyperbolic uniformization supplies all the preceding lift data from exactly
the genus and geometric hypotheses appearing in the book's 25.4 corollary. -/
theorem s25w_surface_pair_lifts
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (γ₁ γ₂ : Path a b) (hhom : γ₁.Homotopic γ₂)
    (hgeo₁ : IsPhiGeodesicRS q γ₁) (hgeo₂ : IsPhiGeodesicRS q γ₂)
    (hno₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s)
    (hno₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) :
    ∃ (ψ : ℂ → ℂ) (c₁ c₂ : LRCurve),
      DifferentiableOn ℂ ψ upperHalf ∧ (∃ z ∈ upperHalf, ψ z ≠ 0) ∧
      IsPhiGeodesic ψ upperHalf c₁ ∧ IsPhiGeodesic ψ upperHalf c₂ ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, c₁.toFun u ≠ c₁.toFun s) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, c₂.toFun u ≠ c₂.toFun s) ∧
      c₁.toFun 0 = c₂.toFun 0 ∧ c₁.toFun 1 = c₂.toFun 1 ∧
      (c₁.closedTrace = c₂.closedTrace → range γ₁ = range γ₂) := by
  obtain ⟨Γ, p, _hΓ, _hfree, hp⟩ := s22hg_exists_fuchsian_uniformization (S := S) hg hS
  obtain ⟨c₁, c₂, h₁, h₂, hn₁, hn₂, h0, h1, hdesc⟩ :=
    s25w_pair_lifts_of_uniformization hq hne hp γ₁ γ₂ hhom hgeo₁ hgeo₂ hno₁ hno₂
  exact ⟨utm_liftQD q p, c₁, c₂, utm_liftQD_differentiableOn hq hp,
    utm_liftQD_ne hq hne hp, h₁, h₂, hn₁, hn₂, h0, h1, hdesc⟩

end LiZhongQC

