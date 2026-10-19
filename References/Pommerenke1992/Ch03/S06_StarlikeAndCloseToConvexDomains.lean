import References.Pommerenke1992.Ch03.S05_RegulatedDomains

/-!
# Pommerenke 1992, Ch. 3 §3.6 Starlike and Close-to-Convex Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §3.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 2768–2961.

* Definition (convex domain, §3.6) — exists: `Convex` (Mathlib, Convex ℝ G: the segment between two points of G lies
  in G)
* Definition (convex function, §3.6) — `IsConvexFunction`
* Unlabelled (§3.6, l. 2770: every convex domain is regulated and of bounded boundary rotation, with `β` increasing and
  `β(2π) - β(0) = 2π`; used for (3.6.1)) — `convex_isRegulated`
* Formula (3.6.1) (cited in the proof of Theorem 3.18) — `eq3_6_1`
* Formula (3.6.2) (cited for (3.6.6)) — `eq3_6_2`
* Unlabelled (§3.6, l. 2784: conversely, `f' ≠ 0` and (3.6.2) imply that `f` is convex, quoted; used for (3.6.6)) —
  `convex_iff`
* Formula (3.6.3) (quoted from Sheil-Small and Suffridge; cited in the proof of Theorem 3.21) — `eq3_6_3`
* Definition (starlike domain, §3.6) — exists: `StarConvex` (Mathlib, StarConvex ℝ 0 G: the segment from 0 to each
  point of G lies in G)
* Definition (starlike function, §3.6) — `IsStarlikeFunction`
* Formula (3.6.5) (quoted; cited at l. 6744, 7663 and in the proof of Theorem 3.18) — `eq3_6_5`
* Formula (3.6.6) (cited in the proof of Theorem 3.18 and in the definition of close-to-convex functions) —
  `eq3_6_6`
* Theorem 3.18 — `thm3_18_a`, `thm3_18_b`
* Formula (3.6.10) (stated in the proof of Theorem 3.18; cited as a result, by number, at l. 6744) — `eq3_6_10`
* Proposition 3.19 — `prop3_19`
* Definition (close-to-convex function, (3.6.14); Kaplan; cited at l. 7663) — `IsCloseToConvex`
* Proposition 3.20 — `prop3_20`
* Theorem 3.21 — `thm3_21`

Not items (DESIGN §3): the Hadamard convolution (3.6.4) (quoted, not cited); the example (3.6.11); the growth (3.6.13)
and "`β` continuous if and only if `g(𝔻)` contains no infinite sector" (quoted / immediate, not cited); the equivalent
form of (3.6.14) with a starlike function and "every starlike function is close-to-convex" (immediate from (3.6.5)
and (3.6.6)); the example (3.6.15); the consequences of Theorem 3.21 on halflines and Lewandowski's characterization
(quoted, not cited).

**Conventions.** As in §3.5. The functions are analytic in `𝔻` (`DifferentiableOn ℂ · unitDisc`). The argument of a
starlike function is the continuous branch `arg g(z) = arg z + Im L(z)` with a holomorphic logarithm `L` of `g(z)/z`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsJordanCurve IsConformalOnto)
open LehtoVirtanen1973 (IsConformalMap)

/-- **Definition** (§3.6). The analytic function `f` is convex in `𝔻`: it maps `𝔻` conformally onto a convex domain. -/
def IsConvexFunction (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ Convex ℝ (f '' unitDisc)

/-- **Unlabelled claim** (§3.6, l. 2770; used for (3.6.1)). Every convex domain `G ≠ ℂ` is regulated and of bounded
boundary rotation; the direction angle `β(t)` of the forward tangent is increasing and satisfies
`β(2π) - β(0) = 2π`.
Modelling: the last two properties are stated for every forward tangent of a conformal parametrization with the
normalization of `IsRegulatedFor`. -/
theorem convex_isRegulated {G : Set ℂ} (hGo : IsOpen G) (hGne : G.Nonempty) (hGc : Convex ℝ G) (hG : G ≠ univ) :
    IsRegulatedDomain G ∧ IsBoundedBoundaryRotation G ∧
      ∀ (f : ℂ → ℂ) (F : ℂ → ExtPlane) (β : ℝ → ℝ), IsBoundarySetting f G F → IsRegulatedFor F β →
        Monotone β ∧ β (2 * π) - β 0 = 2 * π := by
  sorry

/-- **Formula (3.6.1)** (§3.6; cited in the proof of Theorem 3.18). If `f` is convex, then
`1 + z f''(z)/f'(z) = (1/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) dβ(t)` for `z ∈ 𝔻` (a Stieltjes integral), with `β`
the forward tangent of `∂f(𝔻)`.
Modelling: `2π(1 + z f''(z)/f'(z))` is the Riemann–Stieltjes integral `∫ (e^{it} + z)/(e^{it} - z) dβ(t)`. -/
theorem eq3_6_1 {f : ℂ → ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f (f '' unitDisc) F)
    (hconv : Convex ℝ (f '' unitDisc)) {β : ℝ → ℝ} (hβ : IsRegulatedFor F β) :
    ∀ z ∈ unitDisc, HasRSIntegral (fun t : ℝ => (exp (t * I) + z) / (exp (t * I) - z)) β 0 (2 * π)
      (2 * π * (1 + z * deriv (deriv f) z / deriv f z)) := by
  sorry

/-- **Formula (3.6.2)** (§3.6; cited for (3.6.6)). If `f` is convex, then `Re[1 + z f''(z)/f'(z)] > 0` for `z ∈ 𝔻`. -/
theorem eq3_6_2 {f : ℂ → ℂ} (hf : IsConvexFunction f) :
    ∀ z ∈ unitDisc, 0 < (1 + z * deriv (deriv f) z / deriv f z).re := by
  sorry

/-- **Unlabelled claim** (§3.6, l. 2784, quoted from Pom75 and Duren; used for (3.6.6)). For `f` analytic in `𝔻`:
`f` is convex if and only if `f'(z) ≠ 0` and (3.6.2) `Re[1 + z f''(z)/f'(z)] > 0` for `z ∈ 𝔻`. -/
theorem convex_iff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) :
    IsConvexFunction f ↔
      (∀ z ∈ unitDisc, deriv f z ≠ 0) ∧ ∀ z ∈ unitDisc, 0 < (1 + z * deriv (deriv f) z / deriv f z).re := by
  sorry

/-- **Formula (3.6.3)** (§3.6, quoted from Sheil-Small and Suffridge; cited in the proof of Theorem 3.21). If `f` is
convex, then `Re(2z f'(z)/(f(z) - f(ζ)) - (z + ζ)/(z - ζ)) ≥ 0` for `z, ζ ∈ 𝔻`.
Modelling: for `z ≠ ζ`, where the expression is defined. -/
theorem eq3_6_3 {f : ℂ → ℂ} (hf : IsConvexFunction f) :
    ∀ z ∈ unitDisc, ∀ ζ ∈ unitDisc, z ≠ ζ →
      0 ≤ (2 * z * deriv f z / (f z - f ζ) - (z + ζ) / (z - ζ)).re := by
  sorry

/-- **Definition** (§3.6). The analytic function `g` is starlike in `𝔻`: it maps `𝔻` conformally onto a domain that is
starlike with respect to `0` (`w ∈ G ⇒ [0, w] ⊆ G`), with `g(0) = 0`. -/
def IsStarlikeFunction (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g unitDisc ∧ InjOn g unitDisc ∧ g 0 = 0 ∧ StarConvex ℝ 0 (g '' unitDisc)

/-- **Formula (3.6.5)** (§3.6, quoted from Pom75 and Duren; cited at l. 6744, 7663 and in the proof of Theorem 3.18).
For `g` analytic in `𝔻` with `g(0) = 0`: `g` is starlike if and only if `g'(0) ≠ 0` and (3.6.5)
`Re[z g'(z)/g(z)] > 0` for `z ∈ 𝔻`.
Modelling: at `z = 0` the quotient is `1` by continuity; the condition is stated for `z ≠ 0`. -/
theorem eq3_6_5 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hg0 : g 0 = 0) :
    IsStarlikeFunction g ↔ deriv g 0 ≠ 0 ∧ ∀ z ∈ unitDisc, z ≠ 0 → 0 < (z * deriv g z / g z).re := by
  sorry

/-- **Formula (3.6.6)** (§3.6; cited in the proof of Theorem 3.18 and in the definition of close-to-convex
functions). `f(z)` is convex if and only if `g(z) = z f'(z)` is starlike. -/
theorem eq3_6_6 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) :
    IsConvexFunction f ↔ IsStarlikeFunction (fun z => z * deriv f z) := by
  sorry

/-- **Theorem 3.18** (§3.6), first part. If `g` is starlike, then the limits (3.6.7)
`β(t) = lim_{r → 1-} arg g(re^{it})` and `g(e^{it}) = lim_{r → 1-} g(re^{it}) ∈ Ĉ` exist for all `t`, and (3.6.8)
`g(z) = z g'(0) exp(-(1/π) ∫₀^{2π} log(1 - e^{-it} z) dβ(t))` for `z ∈ 𝔻`.
Modelling: `arg g(z) = arg z + Im L(z)` with a holomorphic logarithm `L` of `g(z)/z` (a continuous branch on
`𝔻 ∖ {0}`); the Stieltjes integral is `HasRSIntegral`, the logarithm principal. The function `β` is increasing with
`β(t + 2π) = β(t) + 2π` (from the proof; cited at l. 6386 as "the increasing function β" of Theorem 3.18). -/
theorem thm3_18_a {g : ℂ → ℂ} (hg : IsStarlikeFunction g) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ (∀ z ∈ unitDisc, z ≠ 0 → z * exp (L z) = g z) ∧
      ∃ β : ℝ → ℝ, (∀ t : ℝ, Tendsto (fun r : ℝ => t + (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (β t))) ∧
        Monotone β ∧ (∀ t : ℝ, β (t + 2 * π) = β t + 2 * π) ∧
        (∀ t : ℝ, ∃ w : ExtPlane, Tendsto (fun r : ℝ => (g (r * exp (t * I)) : ExtPlane)) (𝓝[<] 1) (𝓝 w)) ∧
        ∀ z ∈ unitDisc, ∃ J : ℂ, HasRSIntegral (fun t : ℝ => log (1 - exp (-(t * I)) * z)) β 0 (2 * π) J ∧
          g z = z * deriv g 0 * exp (-(1 / π) * J) := by
  sorry

/-- **Theorem 3.18** (§3.6), second part. Conversely, if `β(t)` is increasing and `β(2π) - β(0) = 2π`, then (3.6.8)
represents a starlike function.
Modelling: `g'(0)` in (3.6.8) is a constant `c ≠ 0`, and `β` is increasing on `[0, 2π]`. -/
theorem thm3_18_b {β : ℝ → ℝ} (hβ : MonotoneOn β (Icc 0 (2 * π))) (hβ2 : β (2 * π) - β 0 = 2 * π) {c : ℂ}
    (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : ∀ z ∈ unitDisc, ∃ J : ℂ, HasRSIntegral (fun t : ℝ => log (1 - exp (-(t * I)) * z)) β 0 (2 * π) J ∧
      g z = z * c * exp (-(1 / π) * J)) :
    IsStarlikeFunction g := by
  sorry

/-- **Formula (3.6.10)** (§3.6; stated in the proof of Theorem 3.18, cited at l. 6744). If `g` is starlike and `β` is
the function (3.6.7), then `z g'(z)/g(z) = (1/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) dβ(t)` for `z ∈ 𝔻`.
Modelling: `β` as in `thm3_18_a` (the radial limits of `t + Im L`, `L` a holomorphic logarithm of `g(z)/z`); the
Stieltjes integral is `HasRSIntegral`; for `z ≠ 0` (at `0` the quotient is `1` by continuity). -/
theorem eq3_6_10 {g : ℂ → ℂ} (hg : IsStarlikeFunction g) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLg : ∀ z ∈ unitDisc, z ≠ 0 → z * exp (L z) = g z) {β : ℝ → ℝ}
    (hβ : ∀ t : ℝ, Tendsto (fun r : ℝ => t + (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (β t))) :
    ∀ z ∈ unitDisc, z ≠ 0 →
      HasRSIntegral (fun t : ℝ => (exp (t * I) + z) / (exp (t * I) - z)) β 0 (2 * π)
        (2 * π * (z * deriv g z / g z)) := by
  sorry

/-- **Proposition 3.19** (§3.6; Sheil-Small). Let `g` be starlike and `0 ≤ ϑ ≤ 2π`. If
`β(ϑ+) - β(ϑ-) = πσ > 0`, then (3.6.12) `|g(re^{iϑ})| ≥ r |g'(0)| 2^{-2+σ} (1 - r)^{-σ}` for `0 ≤ r < 1`, and `g(𝔻)`
contains the infinite sector `{β(ϑ-) < arg w < β(ϑ+)}`, which cannot be replaced by a larger infinite sector.
Modelling: `β` is the function of (3.6.7) (the branch of `thm3_18_a`); a sector `{a < arg w < b}` is the set of
`w ≠ 0` with an argument in `(a, b)`; a larger sector is `{α⁻ < arg w < α⁺}` with `α⁻ ≤ β(ϑ-)`, `β(ϑ+) ≤ α⁺` and one
inequality strict. -/
theorem prop3_19 {g : ℂ → ℂ} (hg : IsStarlikeFunction g) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLg : ∀ z ∈ unitDisc, z ≠ 0 → z * exp (L z) = g z) {β : ℝ → ℝ}
    (hβ : ∀ t : ℝ, Tendsto (fun r : ℝ => t + (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (β t))) {ϑ : ℝ}
    (hϑ : ϑ ∈ Icc 0 (2 * π)) {lp lm σ : ℝ} (hlp : Tendsto β (𝓝[>] ϑ) (𝓝 lp)) (hlm : Tendsto β (𝓝[<] ϑ) (𝓝 lm))
    (hσ : lp - lm = π * σ) (hσ0 : 0 < σ) :
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      r * ‖deriv g 0‖ * (2 : ℝ) ^ (-2 + σ) * (1 - r) ^ (-σ) ≤ ‖g (r * exp (ϑ * I))‖) ∧
    {w : ℂ | w ≠ 0 ∧ ∃ φ ∈ Ioo lm lp, w = (‖w‖ : ℂ) * exp (φ * I)} ⊆ g '' unitDisc ∧
    ∀ αm αp : ℝ, αm ≤ lm → lp ≤ αp → (αm < lm ∨ lp < αp) →
      ¬ {w : ℂ | w ≠ 0 ∧ ∃ φ ∈ Ioo αm αp, w = (‖w‖ : ℂ) * exp (φ * I)} ⊆ g '' unitDisc := by
  sorry

/-- **Definition (3.6.14)** (§3.6; Kaplan; cited at l. 7663). The function `f` is close-to-convex in `𝔻`: it is
analytic and there is a convex (univalent) function `h` with `Re[f'(z)/h'(z)] > 0` for `z ∈ 𝔻`. -/
def IsCloseToConvex (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f unitDisc ∧ ∃ h : ℂ → ℂ, IsConvexFunction h ∧ ∀ z ∈ unitDisc, 0 < (deriv f z / deriv h z).re

/-- **Proposition 3.20** (§3.6). Every close-to-convex function `f` is univalent in `𝔻`, and if (3.6.14) holds with
the convex function `h`, then (3.6.16) `Re[(f(z₁) - f(z₂))/(h(z₁) - h(z₂))] > 0` for `z₁, z₂ ∈ 𝔻`.
Modelling: for `z₁ ≠ z₂`. -/
theorem prop3_20 {f : ℂ → ℂ} (hf : IsCloseToConvex f) :
    InjOn f unitDisc ∧
      ∀ h : ℂ → ℂ, IsConvexFunction h → (∀ z ∈ unitDisc, 0 < (deriv f z / deriv h z).re) →
        ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ z₂ → 0 < ((f z₁ - f z₂) / (h z₁ - h z₂)).re := by
  sorry

/-- **Theorem 3.21** (§3.6). Let `f` be close-to-convex, with (3.6.14) for the convex `h`, and let `β(t)` be the
tangent direction angle of the convex curve `∂h(𝔻)` (the forward tangent (3.5.4)). Let `G = f(𝔻)`, `0 ≤ t < 2π`, and
`I(t)` the impression of the prime end `f̂(e^{it})`. If `I(t)` contains finite points, then there exists
`b(t) ∈ I(t)` such that (3.6.17)
`S(t) = {w : |arg(w - b(t)) - (β(t+) + β(t-))/2 + π/2| ≤ (β(t+) - β(t-))/2}` lies in `ℂ ∖ G` and contains `I(t)`.
The radial limit `f(e^{it}) ∈ Ĉ` exists unless `β(t+) - β(t-) = π`.
Modelling:
- `h` has the boundary setting `IsBoundarySetting h (h(𝔻)) H` with forward tangent `β`; `β(t+) = β(t)`
  (Proposition 3.13) and `β(t-)` is the left limit `l`.
- `f` enters the prime-end notions of §2.4–2.5 as the map `OnePoint.map f` of `Ĉ`, conformal on `𝔻`; `f̂` is a prime
  end correspondence (Theorem 2.15).
- `S(t)` contains `b(t)` itself; "contains `I(t)`" is for the finite points of `I(t)`. -/
theorem thm3_21 {f h : ℂ → ℂ} (hf : IsCloseToConvex f) (hh : IsConvexFunction h)
    (hfh : ∀ z ∈ unitDisc, 0 < (deriv f z / deriv h z).re) {H : ℂ → ExtPlane}
    (hH : IsBoundarySetting h (h '' unitDisc) H) {β : ℝ → ℝ} (hβ : IsRegulatedFor H β)
    (hfc : IsConformalMap (OnePoint.map f) (toExt unitDisc)) {fhat : ℂ → Set (ℕ → Set ExtPlane)}
    (hfhat : IsPrimeEndCorrespondence (toExt (f '' unitDisc)) (OnePoint.map f) fhat) {t l : ℝ}
    (ht : t ∈ Ico 0 (2 * π)) (hl : Tendsto β (𝓝[<] t) (𝓝 l)) :
    ((∃ b : ℂ, (b : ExtPlane) ∈ impression (toExt (f '' unitDisc)) (fhat (exp (t * I)))) →
      ∃ b : ℂ, (b : ExtPlane) ∈ impression (toExt (f '' unitDisc)) (fhat (exp (t * I))) ∧
        {w : ℂ | w = b ∨ ∃ φ : ℝ, |φ - (β t + l) / 2 + π / 2| ≤ (β t - l) / 2 ∧
          w - b = (‖w - b‖ : ℂ) * exp (φ * I)} ⊆ (f '' unitDisc)ᶜ ∧
        ∀ w : ℂ, (w : ExtPlane) ∈ impression (toExt (f '' unitDisc)) (fhat (exp (t * I))) →
          w = b ∨ ∃ φ : ℝ, |φ - (β t + l) / 2 + π / 2| ≤ (β t - l) / 2 ∧ w - b = (‖w - b‖ : ℂ) * exp (φ * I)) ∧
    (β t - l ≠ π → ∃ w : ExtPlane, HasRadialLimit (fun z : ℂ => (f z : ExtPlane)) (exp (t * I)) w) := by
  sorry

end Pommerenke1992
