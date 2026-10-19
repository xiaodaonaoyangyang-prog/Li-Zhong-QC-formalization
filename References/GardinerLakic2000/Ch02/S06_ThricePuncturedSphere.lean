import References.GardinerLakic2000.Ch02.S05_ConstantCurvature

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.6 Thrice-punctured spheres

Source `teichmuller.txt`, lines 1567–1613 (Chapter 2, §2.6).

* Proposition 3 (Agard's formula, l. 1604; cited in Ch. 3, l. 2470, 3204, 3387) — `prop2_3`

Not items: the properties 1–3 of `f(t) = f^{t|φ|/φ}(z₀)` and the extremal property (l. 1582–1602), steps of the proof
(they use Teichmüller's theorem of Ch. 4); the Remark relating Agard's formula to Slodkowski's theorem (l. 1612).
Modelling: the thrice-punctured sphere `ℂ̄ ∖ {0, 1, ∞}` is the plane domain `ℂ ∖ {0, 1}`, and its Poincaré density
is `poincareDensityGL` of §2.5 (curvature −4).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

/-- **Proposition 3** (Agard's formula, §2.6, l. 1604). The Poincaré density of `ℂ̄ ∖ {0, 1, ∞}` satisfies
`ρ_{01∞}(z₀)⁻¹ = (1/π) ∬_ℂ |z₀(z₀ − 1)| / |ζ(ζ − 1)(ζ − z₀)| dξ dη`. -/
theorem prop2_3 {z₀ : ℂ} (h0 : z₀ ≠ 0) (h1 : z₀ ≠ 1) :
    (poincareDensityGL {w : ℂ | w ≠ 0 ∧ w ≠ 1} z₀)⁻¹ =
      1 / π * ∫ ζ : ℂ, ‖z₀ * (z₀ - 1)‖ / ‖ζ * (ζ - 1) * (ζ - z₀)‖ := by
  sorry

end GardinerLakic2000
