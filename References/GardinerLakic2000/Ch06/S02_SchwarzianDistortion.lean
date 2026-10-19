import References.GardinerLakic2000.Ch06.S01_CrossRatiosSchwarzian
import References.Gehring1978.S1_Introduction

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.2 Schwarzian distortion

Source `teichmuller.txt`, lines 5569–5652.

* Formula (6.9) (the area theorem of Gronwall and Bieberbach, l. 5578–5582) — exists: `Pommerenke1992.area_theorem`
  (for the class Σ; the book's normalization b₀ = 0 is a subclass)
* Formula (6.10) (`|S f(z₀)| (1 − |z₀|²)² ≤ 6` for univalent `f` in `Δ`, l. 5633) — exists:
  `LiZhongQC.thm19_2_nehari` [misprint: the book prints (1 − |z₀|²), also GL8:5499; the computation
  A′(0)² = (1 − |z₀|²)² (l. 5626–5629) gives the square]
* Proposition 1 (`|S f| ρ_D⁻² ≤ 12`, `ρ_D` of curvature −4, l. 5637) — `prop6_1`

Not items (DESIGN §3): `|S(f)(0)| ≤ 6` (l. 5572, 5622), the case `z₀ = 0` of (6.10).

**Conventions.** `ρ_D` is the hyperbolic density of curvature −4, `Gehring1978.hypDensity` (Part A §0). Near miss:
`LiZhongQC.thm19_3_cor` (the same bound in the density `η_D = 2ρ_D`, constant `3`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

/-- **Proposition 1** (§6.2, l. 5637). Let `f` be univalent in a simply connected domain `D` conformal to the unit
disc, and `ρ_D` the infinitesimal Poincaré metric of `D` of curvature −4. Then `|S f(z)| ρ_D(z)⁻² ≤ 12`. -/
theorem prop6_1 {D : Set ℂ} (hD : LiZhongQC.IsHyperbolicSimplyConnected D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) {z : ℂ} (hz : z ∈ D) :
    ‖LiZhongQC.schwarzian f z‖ * Gehring1978.hypDensity (LiZhongQC.toExt D) z ^ (-2 : ℤ) ≤ 12 := by
  sorry

end GardinerLakic2000
