import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 2 §2.4: The hyperboloid model (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 1674–1760.

**Conventions.** `E^{2,1} = ℝ³` (coordinates `x₀, x₁, x₂`) carries the pseudo inner product
`⟨x, y⟩ = −x₀ y₀ + x₁ y₁ + x₂ y₂` (`lorentz`).

* Def. 2.4.1 (the hyperboloid model `ℍ = {⟨x, x⟩ = −1, x₀ > 0}`) — `lorentz`, `hyperboloidH`
* Prop. 2.4.6 (projection from `a = (−1, 0, 0)` is an isometry onto `𝔻` with the hyperbolic metric) —
  `hyperboloidProj`, `prop2_4_6_a`, `prop2_4_6_b`
* Prop. 2.4.7 (cosine law for hyperbolic triangles) — exists: `Katok1992.thm1_5_2_ii`
* Prop. 2.4.10 (second cosine law) — exists: `Katok1992.thm1_5_2_iii`
* Prop. 2.4.13 (sine law) — exists: `Katok1992.thm1_5_2_i`
* Prop. 2.4.15 (area of a hyperbolic triangle `π − (α + β + γ)`) — exists: `Katok1992.thm1_4_2`
* Exercises 2.4.2–2.4.5, 2.4.8–2.4.9, 2.4.11–2.4.12, 2.4.14 — omitted: exercise
-/

open Set
open LiZhongQC

namespace Hubbard2006

/-- **The pseudo inner product of `E^{2,1}`** (H1:1674): `⟨x, y⟩ = −x₀ y₀ + x₁ y₁ + x₂ y₂`. -/
def lorentz (x y : Fin 3 → ℝ) : ℝ := -(x 0 * y 0) + x 1 * y 1 + x 2 * y 2

/-- **Definition 2.4.1: the hyperboloid model `ℍ` of the hyperbolic plane**: the component `x₀ > 0` of the surface
`⟨x, x⟩ = −1`. -/
def hyperboloidH : Set (Fin 3 → ℝ) := {x | lorentz x x = -1 ∧ 0 < x 0}

/-- **The projection from `a = (−1, 0, 0)` onto the unit disc** (equation (2.4.6), H1:1726):
`x ↦ (x₁ / (1 + x₀), x₂ / (1 + x₀))`, read in `ℂ`. -/
noncomputable def hyperboloidProj (x : Fin 3 → ℝ) : ℂ := ⟨x 1 / (1 + x 0), x 2 / (1 + x 0)⟩

/-- **Proposition 2.4.6 (a)** (H1:1720). The projection is a bijection of the hyperboloid model onto the unit disc. -/
theorem prop2_4_6_a : BijOn hyperboloidProj hyperboloidH unitDisc := by
  sorry

/-- **Proposition 2.4.6 (b)** (H1:1720). The projection is an infinitesimal isometry: for a tangent vector `u` to
`ℍ` at `x` (`⟨x, u⟩ = 0`), the length `√⟨u, u⟩` equals the hyperbolic length `ρ_𝔻(p x) |Dp(x) u|` of its image
(`ρ_𝔻 = 2 / (1 − |z|²)`, `LiZhongQC.poincareDensityDisc`), in squared form. Together with (a) this makes `p` an
isometry of the length metrics. -/
theorem prop2_4_6_b {x : Fin 3 → ℝ} (hx : x ∈ hyperboloidH) {u : Fin 3 → ℝ} (hu : lorentz x u = 0) :
    lorentz u u = (poincareDensityDisc (hyperboloidProj x) * ‖fderiv ℝ hyperboloidProj x u‖) ^ 2 := by
  sorry

end Hubbard2006
