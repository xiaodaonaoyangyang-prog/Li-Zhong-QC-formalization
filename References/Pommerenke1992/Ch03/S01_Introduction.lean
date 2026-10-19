import References.Pommerenke1992.Ch02.S06_CountabilityTheorems
import References.LehtoVirtanen1973.Ch01.S04_ModuleExtremalLength
import Mathlib.Analysis.Complex.Poisson

/-!
# Pommerenke 1992, Ch. 3 §3.1 Introduction

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 3 *Smoothness and Corners*, §3.1; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1708–1804.

* Definition (analytic curve, §3.1) — exists: `LehtoVirtanen1973.IsAnalyticCurve` (applied to toExt C for C in the
  plane: the image of a circle under a conformal map of a neighbourhood of it; the book's parametrization by a map
  univalent in an annulus around the unit circle gives the same class, since the neighbourhood can be shrunk to a thin
  annulus on which the map is finite and composed with an affine map onto the unit circle)
* Proposition 3.1 — `prop3_1`
* Definition (the class `C^∞` of curves, §3.1) — `IsJordanCurveCInfty`
* Kellogg–Warschawski theorem (the `C^∞` form, quoted in §3.1 and restated at l. 2141) — `kellogg_warschawski`
* Formula (3.1.1) (the Schwarz–Christoffel formula, quoted; cited at l. 2748) — `eq3_1_1`
* Formula (3.1.2) (the Schwarz integral formula; cited in the proofs of Theorem 3.2, Proposition 3.8, Theorem 3.15
  and at l. 3335; its extension to `g ∈ H¹`, asserted inside the proof of Proposition 3.8, l. 2224, is a proof step) —
  `eq3_1_2`
* Definition (the Poisson kernel `p(z, ζ)`, (3.1.4)) — exists: `poissonKernel` (Mathlib: poissonKernel c w z is
  (|z - c|² - |w - c|²)/|z - w|², so for |ζ| = 1 the book's p(z, ζ) = (1 - |z|²)/(2π |ζ - z|²) is poissonKernel 0 z ζ
  divided by 2π; the statements that use the kernel write this factor, so that their constants are the book's)
* Formula (3.1.5) (quoted from Ahlfors; cited in the proofs of Theorems 3.2, 3.7, 3.15) — `eq3_1_5`
* Formula (3.1.6) (cited at l. 2009, 2065, 2381, 6704, 7579) — `eq3_1_6`

The helper definition `IsPeriodicParam` (a `2π`-periodic parametrization of a Jordan curve) is used for all the
curve classes of Chapter 3.

Not items (DESIGN §3): the displays of l. 1723–1733 and the corner preview of l. 1741–1743 (previews of Theorems
3.2, 3.5 and of §3.4); the preview of
regulated domains (l. 1753; §3.5 and `convex_isRegulated` in §3.6 state it); the Poisson integral formula (3.1.3) (the
imaginary part of (3.1.2), not cited by number); the remarks on numerical methods and on circular-arc polygons.

**Conventions.** In this chapter `f` maps `𝔻` conformally onto the inner domain `G` of a Jordan curve `C ⊆ ℂ`
(`LiZhongQC.IsConformalOnto f unitDisc G`); `f` has a continuous extension to `𝔻̄` (Theorem 2.6), written `F`. The
integrals over `𝕋` are written through the parameter `t ∈ [0, 2π]`, `ζ = e^{it}`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve IsConformalOnto)

/-- A `2π`-periodic parametrization `w(τ)` of the Jordan curve `C ⊆ ℂ` (§3.1–§3.3, helper): `w` is continuous and
`2π`-periodic, injective on `[0, 2π)`, and `w([0, 2π)) = C`. -/
def IsPeriodicParam (C : Set ℂ) (w : ℝ → ℂ) : Prop :=
  Continuous w ∧ Function.Periodic w (2 * π) ∧ InjOn w (Ico 0 (2 * π)) ∧ w '' Ico 0 (2 * π) = C

/-- **Proposition 3.1** (§3.1). Let `f` map `𝔻` conformally onto the inner domain of the Jordan curve `C ⊆ ℂ`. Then
`C` is an analytic curve if and only if `f` is analytic and univalent in `{|z| < r}` for some `r > 1`.
Modelling: an analytic curve is `LehtoVirtanen1973.IsAnalyticCurve` (the book's definition by a parametrization
`φ(ζ)`, `ζ ∈ 𝕋`, with `φ` analytic and univalent in `{1/ρ < |z| < ρ}`, `ρ > 1`, gives the same class; see the file
header); "`f` is analytic and univalent in `{|z| < r}`" means that `f` has such an extension. -/
theorem prop3_1 {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) :
    LehtoVirtanen1973.IsAnalyticCurve (toExt C) ↔
      ∃ r > (1 : ℝ), ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 r) ∧ InjOn g (ball 0 r) ∧ EqOn g f unitDisc := by
  sorry

/-- **Definition** (§3.1). The class `C^∞`: the Jordan curves `C ⊆ ℂ` with an infinitely differentiable
(`2π`-periodic) parametrization `w` with `w' ≠ 0` ("the smooth curves with some infinitely differentiable
parametrization"; smoothness is defined in §3.2). -/
def IsJordanCurveCInfty (C : Set ℂ) : Prop :=
  ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ContDiff ℝ ∞ w ∧ ∀ τ, deriv w τ ≠ 0

/-- **Kellogg–Warschawski theorem** (§3.1, quoted; the form with "class `C^n` for all `n`" is restated at the end
of §3.3, l. 2141, `thm3_6_cinfty`). Let `f` map `𝔻` conformally onto the inner domain of the Jordan curve `C ⊆ ℂ`.
Then `C ∈ C^∞` if and only if all derivatives of `f` are continuous in `𝔻̄`.
Modelling: "`f^{(n)}` is continuous in `𝔻̄`" means that `f^{(n)}` has a continuous extension to the closed disc.
[CORRECTION] On the right-hand side the extension of `f'` is also required to be `≠ 0` on `𝔻̄`. As printed the
converse ("trivial because we can choose the conformal parametrization", l. 2141) is false: `f(z) = z - z²/2` is
injective on `𝔻̄` and all its derivatives are continuous, but `f'(1) = 0` and `∂f(𝔻)` has a cusp at `f(1)`, so it is
not smooth; the conformal parametrization is regular only where `f' ≠ 0` (the mechanism of Exercise 3.1.2: a zero
of `f'` on `𝕋` produces an inward-pointing zero-angle cusp). -/
theorem kellogg_warschawski {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) :
    IsJordanCurveCInfty C ↔
      (∀ n : ℕ, ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F (iteratedDeriv n f) unitDisc) ∧
        ∃ F₁ : ℂ → ℂ, ContinuousOn F₁ (closedBall 0 1) ∧ EqOn F₁ (deriv f) unitDisc ∧
          ∀ z ∈ closedBall (0 : ℂ) 1, F₁ z ≠ 0 := by
  sorry

/-- **Formula (3.1.1)** (§3.1; the Schwarz–Christoffel formula, quoted; cited at l. 2748). If `f` maps `𝔻`
conformally onto a polygonal domain with inner angles `πα_k` at the corners `w_k = f(z_k)` (`k = 1, …, n`), then
`f'(z) = f'(0) ∏_{k=1}^n (1 - z̄_k z)^{α_k - 1}` for `z ∈ 𝔻`.
Modelling:
- The polygon is the Jordan curve `P = ⋃_k [w_k, w_{k+1}]` (indices mod `n`), and `G` is its inner domain. The
  points `z_k = e^{it_k} ∈ 𝕋` are in counterclockwise order (`t` strictly increasing, `t_n < t_1 + 2π`), and
  `F(z_k) = w_k` for the continuous extension `F` of `f` to `𝔻̄`.
- The inner angle `πα_k ∈ (0, 2π)` at `w_k`: `(w_{k-1} - w_k)/(w_{k+1} - w_k)` has the direction `e^{iπα_k}`.
- `(1 - z̄_k z)^{α_k - 1}` is the principal power (`Re(1 - z̄_k z) > 0` in `𝔻`).
- Bounded Jordan polygons only (`0 < α_k < 2`); slit and unbounded polygons are covered by Corollary 3.17. -/
theorem eq3_1_1 {n : ℕ} {w : Fin n → ℂ} {t α : Fin n → ℝ} (ht : StrictMono t)
    (ht' : ∀ k, t k < t ⟨0, Fin.pos k⟩ + 2 * π)
    (hP : IsJordanCurve (toExt (⋃ k, segment ℝ (w k) (w (finRotate n k)))))
    {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (innerDomain (⋃ k, segment ℝ (w k) (w (finRotate n k)))))
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc)
    (hFw : ∀ k, F (exp (t k * I)) = w k) (hα : ∀ k, α k ∈ Ioo (0 : ℝ) 2)
    (hangle : ∀ k, (w ((finRotate n).symm k) - w k) / (w (finRotate n k) - w k) /
      ‖(w ((finRotate n).symm k) - w k) / (w (finRotate n k) - w k)‖ = exp (π * α k * I)) :
    ∀ z ∈ unitDisc, deriv f z =
      deriv f 0 * ∏ k, (1 - conj (exp (t k * I)) * z) ^ ((α k : ℂ) - 1) := by
  sorry

/-- **Formula (3.1.2)** (§3.1; the Schwarz integral formula; cited in the proofs of Theorem 3.2, Proposition 3.8,
Theorem 3.15). If `g` is analytic in `𝔻` and if `v = Im g` has a continuous extension to `𝔻̄`, then
`g(z) = Re g(0) + (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) v(e^{it}) dt` for `z ∈ 𝔻`. -/
theorem eq3_1_2 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {v : ℂ → ℝ}
    (hv : ContinuousOn v (closedBall 0 1)) (hvg : ∀ z ∈ unitDisc, v z = (g z).im) :
    ∀ z ∈ unitDisc, g z = ((g 0).re : ℂ) +
      I / (2 * π) * ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * (v (exp (t * I)) : ℂ) := by
  sorry

/-- **Formula (3.1.5)** (§3.1, quoted from Ahlfors; cited in the proofs of Theorems 3.2, 3.7 and 3.15). If `g` is
given by (3.1.2), `g(z) = Re g(0) + (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) v(e^{it}) dt`, and if `v` is continuous at
`ζ ∈ 𝕋`, then `Im g(z) → v(ζ)` as `z → ζ`, `z ∈ 𝔻`.
Modelling: `v` is a real function on `𝕋`, written as the `2π`-periodic function `t ↦ v(e^{it})`, integrable on
`[0, 2π]`; the real constant `Re g(0)` does not affect `Im g` and is left out; `ζ = e^{iϑ}`. -/
theorem eq3_1_5 {v : ℝ → ℝ} (hper : Function.Periodic v (2 * π)) (hint : IntervalIntegrable v volume 0 (2 * π))
    {ϑ : ℝ} (hcont : ContinuousAt v ϑ) :
    Tendsto (fun z : ℂ => (I / (2 * π) *
        ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * (v t : ℂ)).im)
      (𝓝[unitDisc] (exp (ϑ * I))) (𝓝 (v ϑ)) := by
  sorry

/-- **Formula (3.1.6)** (§3.1; cited at l. 2009, 2065, 2381, 6704, 7579). For `0 ≤ r ≤ 1` and `|t - ϑ| ≤ π`,
`|e^{it} - r e^{iϑ}| ≥ max(|t - ϑ|/π, 1 - r)`. -/
theorem eq3_1_6 {r t ϑ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (htϑ : |t - ϑ| ≤ π) :
    max (|t - ϑ| / π) (1 - r) ≤ ‖exp (t * I) - r * exp (ϑ * I)‖ := by
  sorry

end Pommerenke1992
