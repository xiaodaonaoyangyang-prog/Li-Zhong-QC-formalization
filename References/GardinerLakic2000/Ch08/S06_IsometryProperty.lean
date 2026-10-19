import References.GardinerLakic2000.Ch08.S05_IsometriesOfTeichmullerSpaces

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.6 The isometry property

Source `teichmuller.txt`, lines 6785–6802 (Chapter 8, §8.6).

* Theorem 11 (l. 6786; proved in §8.8–§8.9) — `thm8_11`

Not items: (8.2) `f(t) = ‖φ + tψ‖` (l. 6792; it appears inside Proposition 8.1); "finite analytic type is equivalent
to `A(R)` finite dimensional", "zeros of order at most `4g − 4 + n`" (l. 6796, U−); the outline l. 6798–6801.
Modelling: "`R` is a subset of a compact Riemann surface" is `EmbedsInClosedRS R`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

/-- **Theorem 11** (§8.6, l. 6786). If `R` is a subset of a compact Riemann surface and is of nonexceptional type,
then `R` has the isometry property. -/
theorem thm8_11 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hR : EmbedsInClosedRS R) (hex : ¬ IsExceptionalGL R) : HasIsometryProperty R := by
  sorry

end GardinerLakic2000
