import LiZhongQC.Lemmas.SurfaceGeodesicReduction
import LiZhongQC.Lemmas.CayleyGeodesicTransport
import LiZhongQC.Lemmas.SurfaceGeodesicExistence
/-! Conditional assembly of the book's 25.4 corollary.
The sole additional premise is exactly the proposition of the original 25.3 theorem.
No call to its still-unproved installed declaration is made. -/

open Set
open scoped ENNReal Manifold ContDiff

namespace LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Conditional uniqueness on the surface. All covering, length, local geodesic,
non-pausing and Cayley transport facts are proved helpers; only planar 25.3 is a parameter. -/
theorem s25w_unique_of_thm25_3
    (h25_3 : ∀ {φ : ℂ → ℂ}, DifferentiableOn ℂ φ unitDisc →
      (∃ z ∈ unitDisc, φ z ≠ 0) →
      ∀ {c₁ c₂ : LRCurve},
        IsPhiGeodesic φ unitDisc c₁ → IsPhiGeodesic φ unitDisc c₂ →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          ∃ u ∈ Icc s t, c₁.toFun u ≠ c₁.toFun s) →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          ∃ u ∈ Icc s t, c₂.toFun u ≠ c₂.toFun s) →
        c₁.toFun 0 = c₂.toFun 0 → c₁.toFun 1 = c₂.toFun 1 →
        c₁.closedTrace = c₂.closedTrace)
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g)
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (γ₁ γ₂ : Path a b) (hhom : γ₁.Homotopic γ₂)
    (hgeo₁ : IsPhiGeodesicRS q γ₁) (hgeo₂ : IsPhiGeodesicRS q γ₂)
    (hno₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s)
    (hno₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) :
    range γ₁ = range γ₂ := by
  obtain ⟨ψ, c₁, c₂, hψ, hψne, hc₁, hc₂, hn₁, hn₂, h0, h1, hdesc⟩ :=
    s25w_surface_pair_lifts hg hS hq hne γ₁ γ₂ hhom hgeo₁ hgeo₂ hno₁ hno₂
  obtain ⟨β₁, β₂, _he₁, _he₂, hφ, hφne, hβ₁, hβ₂, hp₁, hp₂, hβ0, hβ1, htrace⟩ :=
    s25ct_transport_pair_to_disc hψ hψne hc₁ hc₂ hn₁ hn₂ h0 h1
  exact hdesc (htrace.mp (h25_3 hφ hφne hβ₁ hβ₂ hp₁ hp₂ hβ0 hβ1))

/-- The full 25.4 corollary conditional only on the original 25.3 proposition.
The existence half reuses the leader's independent construction. -/
theorem s25w_cor_unique_geodesic_of_thm25_3
    (h25_3 : ∀ {φ : ℂ → ℂ}, DifferentiableOn ℂ φ unitDisc →
      (∃ z ∈ unitDisc, φ z ≠ 0) →
      ∀ {c₁ c₂ : LRCurve},
        IsPhiGeodesic φ unitDisc c₁ → IsPhiGeodesic φ unitDisc c₂ →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          ∃ u ∈ Icc s t, c₁.toFun u ≠ c₁.toFun s) →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          ∃ u ∈ Icc s t, c₂.toFun u ≠ c₂.toFun s) →
        c₁.toFun 0 = c₂.toFun 0 → c₁.toFun 1 = c₂.toFun 1 →
        c₁.closedTrace = c₂.closedTrace)
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {p₁ p₂ : S} (α : Path p₁ p₂) :
    (∃ γ : Path p₁ p₂, γ.Homotopic α ∧ IsPhiGeodesicRS q γ) ∧
      ∀ γ₁ γ₂ : Path p₁ p₂, γ₁.Homotopic α → γ₂.Homotopic α → IsPhiGeodesicRS q γ₁ →
        IsPhiGeodesicRS q γ₂ → (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s) →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) → range γ₁ = range γ₂ := by
  letI : CompactSpace S := hS.1
  constructor
  · obtain ⟨γ, hγα, hγ, _hfin⟩ := s25u_geodesic_exists hq hne α
    exact ⟨γ, hγα, hγ⟩
  · intro γ₁ γ₂ hγα₁ hγα₂ hgeo₁ hgeo₂ hno₁ hno₂
    exact s25w_unique_of_thm25_3 h25_3 hg hS hq hne γ₁ γ₂
      (hγα₁.trans hγα₂.symm) hgeo₁ hgeo₂ hno₁ hno₂

end LiZhongQC

