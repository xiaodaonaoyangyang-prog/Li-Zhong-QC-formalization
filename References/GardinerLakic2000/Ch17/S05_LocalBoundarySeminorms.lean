import References.GardinerLakic2000.Ch17.S04_InfinitesimallySubstantialPoints

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.5 Local boundary seminorms

Source `teichmuller.txt`, lines 12977–13025 (Chapter 17, §17.5).

* Theorem 4 (l. 12980) — `thm17_4`

Not items: the proof. Modelling: as §17.4 (`Λ` with at least three points).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (toExt)

/-- **Theorem 4** (§17.5, l. 12980). For `v ∈ Z(Ω)`, `b_p(v) = β_p(v)` for all `p ∈ ∂Ω`. -/
theorem thm17_4 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {V : (ℂ → ℂ) → ℂ}
    (hV : V ∈ zSpaceOpen (toExt Ω)) {p : ℂ} (hp : p ∈ frontier Ω) : bp Ω p V = betaP Ω p V := by
  sorry

end GardinerLakic2000
