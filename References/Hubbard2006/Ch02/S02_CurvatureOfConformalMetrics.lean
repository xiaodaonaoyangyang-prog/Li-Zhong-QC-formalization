import References.GardinerLakic2000.Ch02.S05_ConstantCurvature

/-!
# Hubbard 2006, Chapter 2 §2.2: Curvature of conformal metrics (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 1150–1300.

* Thm 2.2.1 (curvature of a conformal metric `ρ |dz|` is `−Δ ln ρ / ρ²`) — exists:
  `GardinerLakic2000.gaussCurvature` (Formula (2.5) there is this formula as a definition; Hubbard's geometric
  definition of curvature through areas of discs is not modelled)
* The `(1/d)`-metric of an open set (definition) — `invDistDensity`
* Thm 2.2.9 (the `(1/d)`-metric of an open set `U ≠ ℂ` has nonpositive curvature) — `thm2_2_9_a`, `thm2_2_9_b`
* Exercises 2.2.2–2.2.8, 2.2.10–2.2.12 — omitted: exercise
-/

open Set Metric MeasureTheory
open scoped Real

namespace Hubbard2006

/-- **The `(1/d)`-metric density** (H1:1262, §2.2): for an open set `U ⊊ ℂ` the conformal metric
`|dz| / d(z, ℂ ∖ U)`. *Junk:* for `U = ℂ` the distance to the empty complement is `0` in Mathlib and the density
is `0⁻¹ = 0`; every statement assumes `U ≠ univ`. -/
noncomputable def invDistDensity (U : Set ℂ) (z : ℂ) : ℝ := 1 / infDist z Uᶜ

/-- **Theorem 2.2.9 (as in the proof, equation (2.2.13))** (H1:1285). For an open `U ≠ ℂ` the function `ln ρ`,
`ρ = 1 / d(·, ℂ ∖ U)`, satisfies the sub-mean-value inequality on every circle in `U`:
`ln ρ(z) ≤ (1 / 2π) ∫₀^{2π} ln ρ(z + r e^{iθ}) dθ` whenever the closed disc `D̄(z, r) ⊂ U`. This is
`Δ ln ρ ≥ 0` in the sense of the limit (2.2.13) (curvature `−Δ ln ρ / ρ² ≤ 0`), since `ln d` is superharmonic as an
infimum of the harmonic functions `ln |z − w|`, `w ∉ U`. -/
theorem thm2_2_9_a {U : Set ℂ} (hU : IsOpen U) (hne : U ≠ univ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : closedBall z r ⊆ U) :
    Real.log (invDistDensity U z) ≤
      (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π,
        Real.log (invDistDensity U (z + r * Complex.exp (θ * Complex.I))) := by
  sorry

/-- **Theorem 2.2.9 (b)** (H1:1285). At every point `z ∈ U` where the `(1/d)`-density is `C²`, the curvature
(`GardinerLakic2000.gaussCurvature`) is nonpositive. -/
theorem thm2_2_9_b {U : Set ℂ} (hU : IsOpen U) (hne : U ≠ univ) {z : ℂ} (hz : z ∈ U)
    (hC2 : ContDiffAt ℝ 2 (invDistDensity U) z) :
    GardinerLakic2000.gaussCurvature (invDistDensity U) z ≤ 0 := by
  sorry

end Hubbard2006
