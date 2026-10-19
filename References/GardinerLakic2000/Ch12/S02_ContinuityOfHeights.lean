import References.GardinerLakic2000.Ch12.S01_MeasuredFoliations

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.2 Continuity of the heights mapping

Source `teichmuller.txt`, lines 8998–9050.

* Theorem (Strebel, quoted without proof, l. 9001) — `para12_2_strebel`
* Theorem 4 (l. 9023) — `thm12_4`

Not items (DESIGN §3): the elementary half `limsup h_{φₙ}[γ] ≤ h_φ[γ]` (l. 9007, inside the discussion of Strebel's
theorem), the annulus example (l. 9019), Steps I–IV (proof).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop IsHolQuadDiff quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem** (Strebel [Str84], §12.2, l. 9001). Let `φₙ` be holomorphic quadratic differentials on an arbitrary
Riemann surface `R` converging locally uniformly to `φ`. Then `h_{φₙ}[γ] → h_φ[γ]` for every homotopy class of closed
loops `γ`. Modelling: locally uniform convergence in every chart. -/
theorem para12_2_strebel {φs : ℕ → R → ℂ → ℂ} {φ : R → ℂ → ℂ} (hφs : ∀ m, IsHolQuadDiff (φs m))
    (hφ : IsHolQuadDiff φ)
    (hconv : ∀ x : R, TendstoLocallyUniformlyOn (fun m => φs m x) (φ x) atTop (chartAt ℂ x).target)
    (β : Loop R) : Tendsto (fun m => qdHeight (φs m) β) atTop (𝓝 (qdHeight φ β)) := by
  sorry

/-- **Theorem 4** (§12.2, l. 9023). Let `Ṙ` be compact except for finitely many punctures, `γ ∈ 𝒮`, and
`φₙ → φ` in `A(Ṙ)`. Then `h_{φₙ}[γ] → h_φ[γ]`. Modelling: convergence in the norm of `A(Ṙ)`. -/
theorem thm12_4 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φs : ℕ → R → ℂ → ℂ} {φ : R → ℂ → ℂ}
    (hφs : ∀ m, φs m ∈ integrableHolQDSet R) (hφ : φ ∈ integrableHolQDSet R)
    (hconv : Tendsto (fun m => quadDiffNorm (φs m - φ)) atTop (𝓝 0)) {β : Loop R} (hβ : IsEssentialLoop β) :
    Tendsto (fun m => qdHeight (φs m) β) atTop (𝓝 (qdHeight φ β)) := by
  sorry

end GardinerLakic2000
