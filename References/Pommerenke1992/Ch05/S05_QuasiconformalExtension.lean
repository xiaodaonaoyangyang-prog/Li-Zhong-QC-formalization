import References.Pommerenke1992.Ch05.S04_QuasidisksAndQuasisymmetricFunctions
import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC

/-!
# Pommerenke 1992, Ch. 5 §5.5 Quasiconformal Extension

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §5.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 4766–5189.

* Definition (real-analytic, §5.5) — exists: `AnalyticOnNhd` (Mathlib, over the reals with the complex plane as a
  real normed space: real and imaginary parts are real-analytic functions of x and y)
* Definition (sense-preserving homeomorphism of `𝕋` onto `𝕋`, written `φ(e^{it}) = e^{iu(t)}` as in Lemma 5.18) —
  `IsSensePreservingCircleHomeo`
* Definition (the function `F_φ(z, w)`, (5.5.7), and the Douady–Earle (barycentric) extension, (5.5.29), (5.5.30)) —
  `douadyEarleF`, `douadyEarleExt`
* Theorem 5.15 with (5.5.1) — `thm5_15`, `thm5_15_ii`
* Formula (5.5.2) (cited in the proof of Theorem 5.17) — `eq5_5_2`
* Theorem 5.16 — `thm5_16`
* Theorem 5.17 (Ahl63, DoEa86) — `thm5_17`
* Definition (the Fourier coefficients of `φ`, (5.5.11)) — `circleFourierCoeff`
* Formulas (5.5.21), (5.5.22), with the bound `1 - |b|² ≥ δ²/4` of (5.5.19) (cited at l. 7158) — `eq5_5_21`,
  `eq5_5_22`
* Lemma 5.18 — `lemma5_18`
* Lemma 5.19 — `lemma5_19`
* Lemma 5.20 — `lemma5_20`
* Proposition 5.21 — `prop5_21`
* Unlabelled (§5.5, l. 5078–5120, part (b) of the proof of Theorem 5.15: (5.5.23) holds with an `α` depending only on
  the increasing `λ*` of (5.4.8) when `φ̃(0) = 0`; applied outside the proof at l. 7158) — `thm5_15_partB`
* Unlabelled (§5.5, l. 5128: Proposition 5.21 rests only on the Möbius-invariant condition (5.4.8), so `r₀` depends
  only on the function `λ*` of (5.4.8); used at l. 7126 for the Möbius conjugates `σ⁻¹ ∘ φ ∘ τ`) —
  `prop5_21_crossRatio`

Not items (DESIGN §3): the Beurling–Ahlfors extension (quoted); the uniqueness of the Douady–Earle extension under (i)
and (5.5.2) (l. 4786, not cited); (5.5.4) and the removability of `𝕋` (l. 4802–4808, not cited); (5.5.5), (5.5.6)
(steps of the proof of Theorem 5.16; the construction (5.5.6) is recalled at l. 7118); (5.5.8)–(5.5.20) except the
bound of (5.5.19) (the local analysis of `F` at `(0, 0)`, the argument for Theorem 5.15 (leader decision Q8); (5.5.8)
is cited at l. 5024 and 5056, (5.5.10) and (5.5.19) in the proofs of Lemma 5.20 and Theorem 5.15 (a), (5.5.18) in the
proof of Lemma 5.18, l. 4990); "(5.5.23) holds for some `α > 0`" (l. 4964, clear); (5.5.26),
(5.5.28) (proof steps); the Poincaré–Hopf special case (Mil65, quoted inside the proof of Lemma 5.20); the complex
harmonic extension `φ*`, its continuity on `𝔻̄` (a step of the proof of Theorem 5.15 (a)) and Choquet's theorem
(l. 5048–5054); (5.5.31)–(5.5.33), (5.5.36)–(5.5.38) (proof steps); the estimate of part (b) of the proof of Theorem
5.15 beyond `thm5_15_partB` (at l. 7158 it is reused through `thm5_15_partB`, Lemma 5.18 and the items (5.5.21),
(5.5.22)).

**Conventions.** As in §5.4. Integrals over `𝕋` with respect to `|dζ|` are integrals over `t ∈ [0, 2π]`,
`ζ = e^{it}`. The Poisson kernel is `p(z, ζ) = poissonKernel 0 z ζ / (2π)` for `|ζ| = 1` (§3.1, Q10), so that
`∫_𝕋 p(z, ζ)|dζ| = 1`. A conformal self-map `τ ∈ Möb(𝔻)` is `c(z - a)/(1 - āz)`, `|c| = 1`, `|a| < 1`; on `Ĉ` it is
`mobiusExt c (-(c a)) (-ā) 1`. The Möbius transformations of `Ĉ` are `LiZhongQC.IsMobius`. A quasiconformal map of `Ĉ`
onto `Ĉ` is `LehtoVirtanen1973.IsQuasiconformalMap F univ` (leader decision Q3). The derivatives `∂/∂z`, `∂/∂z̄` are
`LiZhongQC.dz`, `LiZhongQC.dzbar`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsMobius mobiusExt dz dzbar)
open LehtoVirtanen1973 (IsQuasiconformalMap)

/-- **Definition** (§5.5; the form of Lemma 5.18). `φ` is a sense-preserving homeomorphism of `𝕋` onto `𝕋`:
`φ(e^{it}) = e^{iu(t)}` with `u` real, continuous and strictly increasing, `u(t + 2π) = u(t) + 2π`. -/
def IsSensePreservingCircleHomeo (φ : ℂ → ℂ) : Prop :=
  ∃ u : ℝ → ℝ, Continuous u ∧ StrictMono u ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
    ∀ t : ℝ, φ (exp (t * I)) = exp (u t * I)

/-- **Definition (5.5.7)** (§5.5). `F_φ(z, w) = ∫_𝕋 (w - φ(ζ))/(1 - w̄φ(ζ)) p(z, ζ) |dζ|` (`z, w ∈ 𝔻`), where `p(z, ζ)`
is the Poisson kernel (3.1.4). -/
def douadyEarleF (φ : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..2 * π, (w - φ (exp (t * I))) / (1 - conj w * φ (exp (t * I))) *
    ((poissonKernel 0 z (exp (t * I)) / (2 * π) : ℝ) : ℂ)

open Classical in
/-- **Definition (5.5.29), (5.5.30)** (§5.5; DoEa86). The Douady–Earle (barycentric) extension of `φ`:
`φ̃(z) = φ(z)` for `z ∈ 𝕋` and `φ̃(z) = w`, where `F_φ(z, w) = 0`, for `z ∈ 𝔻`.
Modelling (leader decision Q8): for `z ∈ 𝔻` the value is chosen by `Classical.epsilon` among the zeros `w ∈ 𝔻` of
`F_φ(z, ·)`. The definition rests on Lemma 5.20 (`lemma5_20`): for a sense-preserving homeomorphism `φ` of `𝕋` onto
`𝕋` the zero exists and is unique, so the choice is the book's `φ̃(z)`; every statement using `douadyEarleExt φ`
assumes `IsSensePreservingCircleHomeo φ`. Off `𝔻̄` the value `φ(z)` is irrelevant. -/
def douadyEarleExt (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ unitDisc then Classical.epsilon (fun w : ℂ => w ∈ unitDisc ∧ douadyEarleF φ z w = 0) else φ z

/-- **Theorem 5.15** (§5.5; BeuAh56, DoEa86), the extension and part (i). The sense-preserving homeomorphism `φ` of
`𝕋` onto `𝕋` can be extended to a homeomorphism `φ̃` of `𝔻̄` onto `𝔻̄` that is real-analytic in `𝔻` and has the
property: (i) if `σ, τ ∈ Möb(𝔻)`, then the extension of `σ ∘ φ ∘ τ` is given by `σ ∘ φ̃ ∘ τ`.
Modelling: `φ̃` is the Douady–Earle extension (constructed in the proof); "homeomorphism of `𝔻̄` onto `𝔻̄`" is a
continuous bijection of the compact `𝔻̄`; the identity in (i) holds on `𝔻̄`. -/
theorem thm5_15 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ) :
    EqOn (douadyEarleExt φ) φ (sphere 0 1) ∧ ContinuousOn (douadyEarleExt φ) (closedBall 0 1) ∧
      InjOn (douadyEarleExt φ) (closedBall 0 1) ∧ douadyEarleExt φ '' closedBall 0 1 = closedBall 0 1 ∧
      AnalyticOnNhd ℝ (douadyEarleExt φ) unitDisc ∧
      ∀ c₁ a₁ c₂ a₂ : ℂ, ‖c₁‖ = 1 → ‖a₁‖ < 1 → ‖c₂‖ = 1 → ‖a₂‖ < 1 →
        EqOn (douadyEarleExt (fun z => c₁ * (φ (c₂ * (z - a₂) / (1 - conj a₂ * z)) - a₁) /
            (1 - conj a₁ * φ (c₂ * (z - a₂) / (1 - conj a₂ * z)))))
          (fun z => c₁ * (douadyEarleExt φ (c₂ * (z - a₂) / (1 - conj a₂ * z)) - a₁) /
            (1 - conj a₁ * douadyEarleExt φ (c₂ * (z - a₂) / (1 - conj a₂ * z))))
          (closedBall 0 1) := by
  sorry

/-- **Theorem 5.15** (§5.5), part (ii), with (5.5.1). If `φ` is quasisymmetric, then `φ̃` is quasiconformal in `𝔻`:
(5.5.1) `|∂φ̃/∂z̄ / ∂φ̃/∂z| ≤ κ < 1` for `z ∈ 𝔻`, where the constant `κ` depends only on the function `λ` in the
definition (5.4.4) of quasisymmetry.
Modelling: "quasiconformal in `𝔻`" is the dilatation bound (5.5.1) for the real-analytic homeomorphism `φ̃`
(`thm5_15`), which is what the book proves; `∂φ̃/∂z ≠ 0` makes the quotient defined. -/
theorem thm5_15_ii (lam : ℝ → ℝ) :
    ∃ κ : ℝ, κ < 1 ∧ ∀ φ : ℂ → ℂ, IsSensePreservingCircleHomeo φ → IsQuasisymmetricWith φ lam →
      ∀ z ∈ unitDisc, dz (douadyEarleExt φ) z ≠ 0 ∧ ‖dzbar (douadyEarleExt φ) z‖ ≤ κ * ‖dz (douadyEarleExt φ) z‖ := by
  sorry

/-- **Unlabelled claim** (§5.5, part (b) of the proof of Theorem 5.15, l. 5078–5120; applied outside the proof at
l. 7158, "as in part (b) of the proof of Theorem 5.15", to `χ = γ ∘ φ ∘ τ`). If `φ` is a sense-preserving
homeomorphism of `𝕋` onto `𝕋` that satisfies (5.4.8) with an increasing function `λ*`, and `φ̃(0) = 0`, then (5.5.23)
`u(t + s) - u(t) ≥ α` (`π/3 ≤ s ≤ 2π/3`, `t ∈ ℝ`) holds for the lift `u` of `φ` with an `α ∈ (0, π/3]` that depends
only on `λ*` ("Note that `M₅` depends only on `λ*`").
Modelling: (5.4.8) for `z₁ ≠ z₄`, `z₂ ≠ z₃`, as in `prop5_14`; `u` is any continuous lift, `φ(e^{it}) = e^{iu(t)}`,
`u(t + 2π) = u(t) + 2π` (lifts differ by constants `2πk`). -/
theorem thm5_15_partB (lamStar : ℝ → ℝ) (hmono : MonotoneOn lamStar (Ici 0)) :
    ∃ α : ℝ, 0 < α ∧ α ≤ π / 3 ∧ ∀ φ : ℂ → ℂ, IsSensePreservingCircleHomeo φ →
      (∀ z₁ ∈ sphere (0 : ℂ) 1, ∀ z₂ ∈ sphere (0 : ℂ) 1, ∀ z₃ ∈ sphere (0 : ℂ) 1, ∀ z₄ ∈ sphere (0 : ℂ) 1,
        z₁ ≠ z₄ → z₂ ≠ z₃ →
          ‖φ z₁ - φ z₃‖ * ‖φ z₂ - φ z₄‖ / (‖φ z₁ - φ z₄‖ * ‖φ z₂ - φ z₃‖) ≤
            lamStar (‖z₁ - z₃‖ * ‖z₂ - z₄‖ / (‖z₁ - z₄‖ * ‖z₂ - z₃‖))) →
      douadyEarleExt φ 0 = 0 →
      ∀ u : ℝ → ℝ, Continuous u → (∀ t, u (t + 2 * π) = u t + 2 * π) →
        (∀ t : ℝ, φ (exp (t * I)) = exp (u t * I)) →
        ∀ t s : ℝ, π / 3 ≤ s → s ≤ 2 * π / 3 → α ≤ u (t + s) - u t := by
  sorry

/-- **Formula (5.5.2)** (§5.5; cited in the proof of Theorem 5.17). `∫_𝕋 φ(ζ)|dζ| = 0 ⇒ φ̃(0) = 0`. -/
theorem eq5_5_2 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ)
    (h0 : ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) = 0) : douadyEarleExt φ 0 = 0 := by
  sorry

/-- **Theorem 5.16** (§5.5; BeuAh56, Tuk81, DoEa86). Every quasisymmetric map `h` of `𝕋` into `ℂ` can be extended to a
quasiconformal map `h̃` of `Ĉ` onto `Ĉ` such that the extension of (5.5.3) `σ ∘ h ∘ τ`, `σ ∈ Möb`, `τ ∈ Möb(𝔻)`, is
given by `σ ∘ h̃ ∘ τ`.
Modelling: the extension is an operator `E` on the quasisymmetric maps; `σ ∘ h ∘ τ` is any map `hs` of `𝕋` into `ℂ`
with these values on `𝕋` (`σ` has its pole off `h(τ(𝕋))`), and the identity of the extensions holds on `Ĉ`. -/
theorem thm5_16 :
    ∃ E : (ℂ → ℂ) → ExtPlane → ExtPlane, ∀ h : ℂ → ℂ, IsQuasisymmetric h →
      IsQuasiconformalMap (E h) univ ∧ E h '' univ = univ ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, E h ζ = (h ζ : ExtPlane)) ∧
      ∀ σ : ExtPlane → ExtPlane, IsMobius σ → ∀ c a : ℂ, ‖c‖ = 1 → ‖a‖ < 1 → ∀ hs : ℂ → ℂ,
        (∀ ζ ∈ sphere (0 : ℂ) 1, (hs ζ : ExtPlane) = σ (h (c * (ζ - a) / (1 - conj a * ζ)))) →
          E hs = σ ∘ E h ∘ mobiusExt c (-(c * a)) (-(conj a)) 1 := by
  sorry

/-- **Theorem 5.17** (§5.5; Ahl63, DoEa86). Every conformal map `f` of `𝔻` onto a quasidisk can be extended to a
quasiconformal map `f̃` of `Ĉ` onto `Ĉ`. The extension of `σ ∘ f ∘ τ` with `σ ∈ Möb` and `τ ∈ Möb(𝔻)` is given by
`σ ∘ f̃ ∘ τ`.
Modelling: the extension is an operator `E` on the conformal maps onto quasidisks; `σ ∘ f ∘ τ` is any map `fs` with
these values on `𝔻` that again maps onto a quasidisk (the domain of `E`), and the identity holds on `Ĉ`. -/
theorem thm5_17 :
    ∃ E : (ℂ → ℂ) → ExtPlane → ExtPlane, ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc (f '' unitDisc) →
      IsQuasidisk (f '' unitDisc) →
      IsQuasiconformalMap (E f) univ ∧ E f '' univ = univ ∧ (∀ z ∈ unitDisc, E f z = (f z : ExtPlane)) ∧
      ∀ σ : ExtPlane → ExtPlane, IsMobius σ → ∀ c a : ℂ, ‖c‖ = 1 → ‖a‖ < 1 → ∀ fs : ℂ → ℂ,
        (∀ z ∈ unitDisc, (fs z : ExtPlane) = σ (f (c * (z - a) / (1 - conj a * z)))) → IsQuasidisk (fs '' unitDisc) →
          E fs = σ ∘ E f ∘ mobiusExt c (-(c * a)) (-(conj a)) 1 := by
  sorry

/-- **Definition (5.5.11)** (§5.5). The Fourier coefficients of `φ`: `a_n = (1/2π) ∫_𝕋 ζ̄ⁿ φ(ζ) |dζ|` (`n ∈ ℤ`). -/
def circleFourierCoeff (φ : ℂ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, exp (-(n * t * I)) * φ (exp (t * I))

/-- **Formula (5.5.21)** (§5.5; cited at l. 7158). Assume (5.5.12) `a₀ = 0`. Then
`φ̃_z(0) = (a₁ - ā₋₁ b)/(1 - |b|²)` and `φ̃_z̄(0) = (a₋₁ - ā₁ b)/(1 - |b|²)`, where (5.5.16)
`b = -(1/2π) ∫_𝕋 φ(ζ)² |dζ|`. -/
theorem eq5_5_21 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ) (ha₀ : circleFourierCoeff φ 0 = 0) :
    dz (douadyEarleExt φ) 0 =
        (circleFourierCoeff φ 1 - conj (circleFourierCoeff φ (-1)) *
          -((1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2)) /
        (1 - ‖(1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2‖ ^ 2) ∧
      dzbar (douadyEarleExt φ) 0 =
        (circleFourierCoeff φ (-1) - conj (circleFourierCoeff φ 1) *
          -((1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2)) /
        (1 - ‖(1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2‖ ^ 2) := by
  sorry

/-- **Formula (5.5.22)** (§5.5; cited at l. 7158). Under (5.5.12) `a₀ = 0`,
`|φ̃_z(0)|² - |φ̃_z̄(0)|² = (|a₁|² - |a₋₁|²)/(1 - |b|²) ≥ δ`, where (5.5.17) `δ = |a₁|² - |a₋₁|²`; and, from (5.5.19),
`1 - |b|² ≥ δ²/4` (used with (5.5.21) for the upper bounds at l. 7158). -/
theorem eq5_5_22 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ) (ha₀ : circleFourierCoeff φ 0 = 0) :
    ‖dz (douadyEarleExt φ) 0‖ ^ 2 - ‖dzbar (douadyEarleExt φ) 0‖ ^ 2 =
        (‖circleFourierCoeff φ 1‖ ^ 2 - ‖circleFourierCoeff φ (-1)‖ ^ 2) /
          (1 - ‖(1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2‖ ^ 2) ∧
      ‖circleFourierCoeff φ 1‖ ^ 2 - ‖circleFourierCoeff φ (-1)‖ ^ 2 ≤
        ‖dz (douadyEarleExt φ) 0‖ ^ 2 - ‖dzbar (douadyEarleExt φ) 0‖ ^ 2 ∧
      (‖circleFourierCoeff φ 1‖ ^ 2 - ‖circleFourierCoeff φ (-1)‖ ^ 2) ^ 2 / 4 ≤
        1 - ‖(1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, φ (exp (t * I)) ^ 2‖ ^ 2 := by
  sorry

/-- **Lemma 5.18** (§5.5). Write `φ(e^{it}) = e^{iu(t)}`, where `u` is real and continuous with
`u(t + 2π) = u(t) + 2π`, and suppose that (5.5.23) `u(t + s) - u(t) ≥ α` for `π/3 ≤ s ≤ 2π/3`, `t ∈ ℝ`, with
`0 < α ≤ π/3`. Then (5.5.24) `δ = |a₁|² - |a₋₁|² ≥ 2π⁻¹ sin³α > 0` and (5.5.25)
`|φ̃_z̄(0)/φ̃_z(0)| ≤ 1 - (1/125) sin⁹α`.
Modelling: `φ` is a sense-preserving homeomorphism of `𝕋` onto `𝕋` (the standing assumption of this part of §5.5);
(5.5.25) is stated under (5.5.12) `a₀ = 0`, the standing assumption of (5.5.21), from which the proof derives it,
without a quotient (`φ̃_z(0) ≠ 0` and `|φ̃_z̄(0)| ≤ (1 - sin⁹α/125)|φ̃_z(0)|`); the OCR splits the display numbers
"(24)" and (25). -/
theorem lemma5_18 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ) {u : ℝ → ℝ} (hu : Continuous u)
    (hu2π : ∀ t, u (t + 2 * π) = u t + 2 * π) (hφu : ∀ t : ℝ, φ (exp (t * I)) = exp (u t * I)) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ π / 3) (h23 : ∀ t s : ℝ, π / 3 ≤ s → s ≤ 2 * π / 3 → α ≤ u (t + s) - u t) :
    (2 * π⁻¹ * Real.sin α ^ 3 ≤ ‖circleFourierCoeff φ 1‖ ^ 2 - ‖circleFourierCoeff φ (-1)‖ ^ 2 ∧
      0 < 2 * π⁻¹ * Real.sin α ^ 3) ∧
    (circleFourierCoeff φ 0 = 0 → dz (douadyEarleExt φ) 0 ≠ 0 ∧
      ‖dzbar (douadyEarleExt φ) 0‖ ≤ (1 - 1 / 125 * Real.sin α ^ 9) * ‖dz (douadyEarleExt φ) 0‖) := by
  sorry

/-- **Lemma 5.19** (§5.5). If `x_j ≥ α > 0` (`j = 1, 2, 3, 4`) and `x₁ + x₂ + x₃ + x₄ = 2π`, then (5.5.27)
`σ = sin x₁ + sin x₂ + sin x₃ + sin x₄ ≥ 4 sin³α` if `α ≤ π/3`, and `≥ 0` otherwise. -/
theorem lemma5_19 {α x₁ x₂ x₃ x₄ : ℝ} (hα : 0 < α) (h₁ : α ≤ x₁) (h₂ : α ≤ x₂) (h₃ : α ≤ x₃) (h₄ : α ≤ x₄)
    (hsum : x₁ + x₂ + x₃ + x₄ = 2 * π) :
    (α ≤ π / 3 → 4 * Real.sin α ^ 3 ≤ Real.sin x₁ + Real.sin x₂ + Real.sin x₃ + Real.sin x₄) ∧
      (π / 3 < α → 0 ≤ Real.sin x₁ + Real.sin x₂ + Real.sin x₃ + Real.sin x₄) := by
  -- `σ = 4 sin A sin B sin C` with the half sums `A, B, C`, since `sin x₄ = −sin(x₁ + x₂ + x₃)`
  have hid : Real.sin x₁ + Real.sin x₂ + Real.sin x₃ + Real.sin x₄ =
      4 * Real.sin ((x₁ + x₂) / 2) * Real.sin ((x₂ + x₃) / 2) * Real.sin ((x₁ + x₃) / 2) := by
    have e1 : Real.sin x₁ = Real.sin ((x₁ + x₂) / 2 + (x₁ + x₃) / 2 - (x₂ + x₃) / 2) := by congr 1; ring
    have e2 : Real.sin x₂ = Real.sin ((x₁ + x₂) / 2 + (x₂ + x₃) / 2 - (x₁ + x₃) / 2) := by congr 1; ring
    have e3 : Real.sin x₃ = Real.sin ((x₂ + x₃) / 2 + (x₁ + x₃) / 2 - (x₁ + x₂) / 2) := by congr 1; ring
    have e4 : Real.sin x₄ = -Real.sin ((x₁ + x₂) / 2 + (x₂ + x₃) / 2 + (x₁ + x₃) / 2) := by
      rw [show x₄ = 2 * π - ((x₁ + x₂) / 2 + (x₂ + x₃) / 2 + (x₁ + x₃) / 2) by linarith, Real.sin_two_pi_sub]
    rw [e1, e2, e3, e4]
    generalize (x₁ + x₂) / 2 = A
    generalize (x₂ + x₃) / 2 = B
    generalize (x₁ + x₃) / 2 = C
    simp only [Real.sin_add, Real.sin_sub, Real.cos_add]
    ring
  rw [hid]
  -- each half sum lies in `[α, π − α]`
  have hA : α ≤ (x₁ + x₂) / 2 ∧ (x₁ + x₂) / 2 ≤ π - α := ⟨by linarith, by linarith⟩
  have hB : α ≤ (x₂ + x₃) / 2 ∧ (x₂ + x₃) / 2 ≤ π - α := ⟨by linarith, by linarith⟩
  have hC : α ≤ (x₁ + x₃) / 2 ∧ (x₁ + x₃) / 2 ≤ π - α := ⟨by linarith, by linarith⟩
  have hnn : ∀ t : ℝ, α ≤ t → t ≤ π - α → 0 ≤ Real.sin t := fun t ht1 ht2 =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  refine ⟨fun hα3 => ?_, fun _ => ?_⟩
  · -- `sin t ≥ sin α` on `[α, π − α]`
    have hge : ∀ t : ℝ, α ≤ t → t ≤ π - α → Real.sin α ≤ Real.sin t := fun t ht1 ht2 => by
      rcases le_total t (π / 2) with ht | ht
      · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht ht1
      · rw [← Real.sin_pi_sub t]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    have hs0 : 0 ≤ Real.sin α := hnn α le_rfl (by linarith [Real.pi_pos])
    have hsA := hge _ hA.1 hA.2
    have hsB := hge _ hB.1 hB.2
    have hsC := hge _ hC.1 hC.2
    have h1 : Real.sin α * Real.sin α ≤ Real.sin ((x₁ + x₂) / 2) * Real.sin ((x₂ + x₃) / 2) :=
      mul_le_mul hsA hsB hs0 (hs0.trans hsA)
    have h2 : Real.sin α * Real.sin α * Real.sin α ≤
        Real.sin ((x₁ + x₂) / 2) * Real.sin ((x₂ + x₃) / 2) * Real.sin ((x₁ + x₃) / 2) :=
      mul_le_mul h1 hsC hs0 (mul_nonneg (hs0.trans hsA) (hs0.trans hsB))
    nlinarith [h2]
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hnn _ hA.1 hA.2)) (hnn _ hB.1 hB.2))
      (hnn _ hC.1 hC.2)

/-- **Lemma 5.20** (§5.5). Let `φ` be a sense-preserving homeomorphism of `𝕋` onto `𝕋`. For each `z ∈ 𝔻` there exists
a unique `w ∈ 𝔻` with `F_φ(z, w) = 0`. -/
theorem lemma5_20 {φ : ℂ → ℂ} (hφ : IsSensePreservingCircleHomeo φ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃! w : ℂ, w ∈ unitDisc ∧ douadyEarleF φ z w = 0 := by
  sorry

/-- **Proposition 5.21** (§5.5; (5.5.34), (5.5.35) cited at l. 7126). Let `φ` be a sense-preserving quasisymmetric
map of `𝕋` onto `𝕋` and suppose that (5.5.34) `ω_ν = e^{iϑ + 2πiν/3}`, `φ(ω_ν) = ω_ν` for `ν = 1, 2, 3`. Then the
Douady–Earle extension `φ̃` of `φ` satisfies (5.5.35) `|φ̃(0)| ≤ r₀ < 1`, where the constant `r₀` depends only on `λ`.
-/
theorem prop5_21 (lam : ℝ → ℝ) :
    ∃ r₀ : ℝ, r₀ < 1 ∧ ∀ φ : ℂ → ℂ, IsSensePreservingCircleHomeo φ → IsQuasisymmetricWith φ lam → ∀ ϑ : ℝ,
      (∀ ν : ℕ, 1 ≤ ν → ν ≤ 3 →
        φ (exp ((ϑ + 2 * π * ν / 3) * I)) = exp ((ϑ + 2 * π * ν / 3) * I)) →
      ‖douadyEarleExt φ 0‖ ≤ r₀ := by
  sorry

/-- **Unlabelled claim** (§5.5, l. 5128, "again we use the Möbius invariant condition (5.4.8)"; used at l. 7126,
"Using the Möbius-invariant condition (5.4.8) of Proposition 5.14, we conclude from Proposition 5.21"). The
conclusion of Proposition 5.21 holds with `r₀` depending only on the function `λ*` of (5.4.8): for every
sense-preserving homeomorphism `φ` of `𝕋` onto `𝕋` that satisfies (5.4.8) with `λ*` and fixes the three points
`ω_ν = e^{iϑ + 2πiν/3}`, `|φ̃(0)| ≤ r₀ < 1`.
Modelling: (5.4.8) for `z₁ ≠ z₄`, `z₂ ≠ z₃`, as in `prop5_14`; the Möbius conjugates of a `λ`-quasisymmetric map
satisfy (5.4.8) with the same `λ*` (cross-ratios are Möbius invariant), which is the use at l. 7126. -/
theorem prop5_21_crossRatio (lamStar : ℝ → ℝ) :
    ∃ r₀ : ℝ, r₀ < 1 ∧ ∀ φ : ℂ → ℂ, IsSensePreservingCircleHomeo φ →
      (∀ z₁ ∈ sphere (0 : ℂ) 1, ∀ z₂ ∈ sphere (0 : ℂ) 1, ∀ z₃ ∈ sphere (0 : ℂ) 1, ∀ z₄ ∈ sphere (0 : ℂ) 1,
        z₁ ≠ z₄ → z₂ ≠ z₃ →
          ‖φ z₁ - φ z₃‖ * ‖φ z₂ - φ z₄‖ / (‖φ z₁ - φ z₄‖ * ‖φ z₂ - φ z₃‖) ≤
            lamStar (‖z₁ - z₃‖ * ‖z₂ - z₄‖ / (‖z₁ - z₄‖ * ‖z₂ - z₃‖))) →
      ∀ ϑ : ℝ, (∀ ν : ℕ, 1 ≤ ν → ν ≤ 3 →
        φ (exp ((ϑ + 2 * π * ν / 3) * I)) = exp ((ϑ + 2 * π * ν / 3) * I)) →
      ‖douadyEarleExt φ 0‖ ≤ r₀ := by
  sorry

end Pommerenke1992
