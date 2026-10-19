import References.GardinerLakic2000.Ch12.S02_ContinuityOfHeights

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.3 Convergence

Source `teichmuller.txt`, lines 9051–9078.

* Lemma 1 (l. 9060) — `lemma12_1`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Lemma 1** (§12.3, l. 9060). If `φₙ ∈ A(Ṙ)` and for every `γ ∈ 𝒮` the sequence `h_{φₙ}[γ]` converges, then
`φₙ` converges (in `A(Ṙ)`). Modelling: convergence of the heights to finite limits. -/
theorem lemma12_1 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φs : ℕ → R → ℂ → ℂ}
    (hφs : ∀ m, φs m ∈ integrableHolQDSet R)
    (hconv : ∀ β : Loop R, IsEssentialLoop β → ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      Tendsto (fun m => qdHeight (φs m) β) atTop (𝓝 L)) :
    ∃ φ ∈ integrableHolQDSet R, Tendsto (fun m => quadDiffNorm (φs m - φ)) atTop (𝓝 0) := by
  sorry

end GardinerLakic2000
