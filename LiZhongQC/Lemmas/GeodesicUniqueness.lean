import LiZhongQC.Lemmas.GeodesicUniquenessProof
import LiZhongQC.Lemmas.SurfaceGeodesicAssembly

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- **Theorem 25.3** (uniqueness of geodesics).  Let `φ ≢ 0` be holomorphic in the unit disc (the
universal covering of a Riemann surface with hyperbolic universal covering, to which a
quadratic differential and homotopic curves with common end points are lifted).  Two
`φ`-geodesics with the same end points have the same trace.

**Correction.**  The geodesics are assumed not to pause (`hp₁`, `hp₂`).  Without this the statement was
**false**: `IsPhiGeodesic` only constrains short windows around each time, so a curve may go out, pause,
and come back — such a spike from `0` to `0` and the constant curve at `0` are both geodesics, with
different traces. -/
theorem thm25_3_unique_geodesic {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {γ₁ γ₂ : LRCurve} (h₁ : IsPhiGeodesic φ unitDisc γ₁)
    (h₂ : IsPhiGeodesic φ unitDisc γ₂) (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1) :
    γ₁.closedTrace = γ₂.closedTrace := by
  exact Set.Subset.antisymm (s25bg_trace_subset hφ hne h₁ h₂ hp₁ hp₂ h0 h1)
    (s25bg_trace_subset hφ hne h₂ h₁ hp₂ hp₁ h0.symm h1.symm)

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- **Corollary of Theorems 25.3 and 25.4**: on a closed Riemann surface of genus `g > 1`, every
homotopy class of curves with given end points contains exactly one `φ`-geodesic (up to
reparametrization: two geodesics in the class have the same trace).

**Correction.**  In the uniqueness half the geodesics are assumed not to pause; without this it was
**false**, for the same reason as Theorem 25.3 (`IsPhiGeodesicRS` allows a curve to go out, pause and
come back).  The existence half is unchanged. -/
theorem thm25_4_cor_unique_geodesic [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {p₁ p₂ : S} (α : Path p₁ p₂) :
    (∃ γ : Path p₁ p₂, γ.Homotopic α ∧ IsPhiGeodesicRS q γ) ∧
      ∀ γ₁ γ₂ : Path p₁ p₂, γ₁.Homotopic α → γ₂.Homotopic α → IsPhiGeodesicRS q γ₁ →
        IsPhiGeodesicRS q γ₂ → (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s) →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) → range γ₁ = range γ₂ := by
  exact s25w_cor_unique_geodesic_of_thm25_3 thm25_3_unique_geodesic hg hS hq hne α

end LiZhongQC
