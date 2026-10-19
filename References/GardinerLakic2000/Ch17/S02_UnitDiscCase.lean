import References.GardinerLakic2000.Ch17.S01_LocalDilatation

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.2 Unit disc case

Source `teichmuller.txt`, lines 12747–12870 (Chapter 17, §17.2).

* Theorem 1 (Fehlmann, l. 12748) — `thm17_1`

Not items: the proof, including (17.5) (the Beurling–Ahlfors extension of `V_i`, l. 12804; it is
`LiZhongQC.beurlingAhlfors`). Modelling: as §17.1, with `Ω = Δ` (`LiZhongQC.unitDisc`); "`max`" is a supremum over
`∂Δ` that is attained.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (toExt unitDisc)

/-- **Theorem 1** (§17.2, l. 12748). `b(v) = max_{p ∈ ∂Δ} b_p(v)` for all `v ∈ Z(Δ)`. -/
theorem thm17_1 {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceOpen (toExt unitDisc)) :
    ∃ p ∈ sphere (0 : ℂ) 1, bp unitDisc p V = bPlane unitDisc V ∧
      ∀ q ∈ sphere (0 : ℂ) 1, bp unitDisc q V ≤ bp unitDisc p V := by
  sorry

end GardinerLakic2000
