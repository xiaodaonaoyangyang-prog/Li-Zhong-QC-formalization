import References.Pommerenke1992.Ch03.S02_SmoothJordanCurves

/-!
# Pommerenke 1992, Ch. 3 §3.3 The Continuity of the Derivatives

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §3.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1929–2168.

* Definition (modulus of continuity, (3.3.1); cited at l. 2275) — `modulusOfContinuity`
* Formula (3.3.2) (cited in the proofs of Proposition 3.4 and Theorem 3.5) — `eq3_3_2`
* Definition (Dini-continuous, (3.3.4); `ω*`, (3.3.5)) — `IsDiniContinuous`, `omegaStar`
* Proposition 3.4 — `prop3_4`
* Definition (Hölder-continuous, (3.3.9); cited at l. 3903) — exists: `HolderOnWith` (Mathlib: the same inequality,
  with the constant M and the exponent α as non-negative reals; the book's range 0 < α ≤ 1 is imposed in the
  statements)
* Unlabelled (§3.3, l. 1989: Hölder-continuous functions are Dini-continuous, `ω*(δ) = O(δ^α)` for `α < 1` and
  `O(δ log 1/δ)` for `α = 1`, and Proposition 3.4 then makes `g` Hölder-continuous in `𝔻̄` for `α < 1`; used in the
  proof of Theorem 3.6) — `prop3_4_holder`, `prop3_4_holder_g`
* Definition (Dini-smooth curve, §3.3) — `IsDiniSmoothJordanCurve`
* Theorem 3.5 — `thm3_5`
* Definition (the classes `C^n`, `C^{n,α}` of curves, (3.3.17)) — `IsJordanCurveCn`, `IsJordanCurveCnAlpha`
* Theorem 3.6 (Kellogg–Warschawski) — `thm3_6`
* Unlabelled (§3.3, l. 2141: all derivatives of `f` are continuous in `𝔻̄` if the Jordan curve is of class `C^n` for
  all `n`, and conversely) — `thm3_6_cinfty`

Not items (DESIGN §3): "`ω` is increasing and continuous with `ω(0) = 0`" (l. 1937, not cited); "the limit `π` in
(3.3.4) could be replaced by any positive constant" (l. 1951, immediate); (3.3.3) (quoted from RuShTa75, not cited);
the remark that the conformal parametrization cannot always be taken for `α = 1` (l. 2101).

**Conventions.** As in §3.1. Moduli of continuity and the Dini integrals are `ℝ≥0∞`-valued (lower integrals), so that
no junk value arises; `ω(t)/t` is `ω t / ENNReal.ofReal t`. The functions of Proposition 3.4 are complex-valued
`2π`-periodic functions on `ℝ`, whose modulus of continuity is taken on `ℝ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve IsConformalOnto)

/-- **Definition (3.3.1)** (§3.3; cited at l. 2275). The modulus of continuity
`ω(δ) = ω(δ, φ, A) = sup{|φ(z₁) - φ(z₂)| : z₁, z₂ ∈ A, |z₁ - z₂| ≤ δ}` (`δ ≥ 0`; the OCR prints `δ ≤ 0`).
Modelling: for a function on a subset of a metric space (the book's `A ⊆ ℂ`, and `ℝ` for functions of `t`), with
values in `ℝ≥0∞`. -/
def modulusOfContinuity {X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E] (φ : X → E) (A : Set X)
    (δ : ℝ) : ℝ≥0∞ :=
  ⨆ z₁ ∈ A, ⨆ z₂ ∈ A, ⨆ (_ : dist z₁ z₂ ≤ δ), ENNReal.ofReal ‖φ z₁ - φ z₂‖

/-- **Formula (3.3.2)** (§3.3; cited in the proofs of Proposition 3.4 and Theorem 3.5). If `φ` is uniformly
continuous on the convex set `A`, then `ω(nδ) ≤ n ω(δ)` for `δ ≥ 0`, `n = 1, 2, …`.
Modelling: for a convex set of a real normed space (the book's `A ⊆ ℂ`; the cited uses are on `ℝ`). -/
theorem eq3_3_2 {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup E] {A : Set X}
    (hA : Convex ℝ A) {φ : X → E} (hφ : UniformContinuousOn φ A) {δ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} (hn : 1 ≤ n) :
    modulusOfContinuity φ A (n * δ) ≤ n * modulusOfContinuity φ A δ := by
  sorry

/-- **Definition (3.3.4)** (§3.3). The uniformly continuous function `φ` is Dini-continuous on `A`:
`∫₀^π ω(t)/t dt < ∞`. -/
def IsDiniContinuous {X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E] (φ : X → E) (A : Set X) :
    Prop :=
  UniformContinuousOn φ A ∧ ∫⁻ t in Ioc 0 π, modulusOfContinuity φ A t / ENNReal.ofReal t < ⊤

/-- **Definition (3.3.5)** (§3.3). For Dini-continuous `φ` and `0 < δ < π`,
`ω*(δ) = ∫₀^δ ω(t)/t dt + δ ∫_δ^π ω(t)/t² dt`. -/
def omegaStar {X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E] (φ : X → E) (A : Set X) (δ : ℝ) :
    ℝ≥0∞ :=
  (∫⁻ t in Ioc 0 δ, modulusOfContinuity φ A t / ENNReal.ofReal t) +
    ENNReal.ofReal δ * ∫⁻ t in Ioc δ π, modulusOfContinuity φ A t / ENNReal.ofReal (t ^ 2)

/-- **Proposition 3.4** (§3.3). Let `φ` be `2π`-periodic and Dini-continuous in `ℝ`. Then
(3.3.6) `g(z) = (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) φ(t) dt` (`z ∈ 𝔻`) has a continuous extension to `𝔻̄`;
furthermore (3.3.7) `|g'(z)| ≤ (2/π) ω(1 - r)/(1 - r) + 2π ∫_{1-r}^π ω(t)/t² dt ≤ 2π ω*(1 - r)/(1 - r)` for
`|z| ≤ r < 1`, and (3.3.8) `|g(z₁) - g(z₂)| ≤ 20 ω*(δ)` for `z₁, z₂ ∈ 𝔻̄`, `|z₁ - z₂| ≤ δ < 1`.
Modelling: `g` on `𝔻̄` in (3.3.8) is the continuous extension `G`; the inequalities are in `ℝ≥0∞`. -/
theorem prop3_4 {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) (hD : IsDiniContinuous φ univ) :
    (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ z : ℂ, ‖z‖ ≤ r →
      ENNReal.ofReal ‖deriv (fun z : ℂ => I / (2 * π) *
          ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * φ t) z‖ ≤
        ENNReal.ofReal (2 / π) * (modulusOfContinuity φ univ (1 - r) / ENNReal.ofReal (1 - r)) +
          ENNReal.ofReal (2 * π) *
            ∫⁻ t in Ioc (1 - r) π, modulusOfContinuity φ univ t / ENNReal.ofReal (t ^ 2) ∧
      ENNReal.ofReal (2 / π) * (modulusOfContinuity φ univ (1 - r) / ENNReal.ofReal (1 - r)) +
          ENNReal.ofReal (2 * π) *
            ∫⁻ t in Ioc (1 - r) π, modulusOfContinuity φ univ t / ENNReal.ofReal (t ^ 2) ≤
        ENNReal.ofReal (2 * π) * (omegaStar φ univ (1 - r) / ENNReal.ofReal (1 - r))) ∧
    ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧
      EqOn G (fun z : ℂ => I / (2 * π) *
        ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * φ t) unitDisc ∧
      ∀ z₁ ∈ closedBall (0 : ℂ) 1, ∀ z₂ ∈ closedBall (0 : ℂ) 1, ∀ δ : ℝ, ‖z₁ - z₂‖ ≤ δ → δ < 1 →
        ENNReal.ofReal ‖G z₁ - G z₂‖ ≤ 20 * omegaStar φ univ δ := by
  sorry

/-- **Unlabelled claim** (§3.3, l. 1989; used in the proof of Theorem 3.6, "Applying Proposition 3.4"). If `φ` is
Hölder-continuous with exponent `α` (`0 < α ≤ 1`), then `φ` is Dini-continuous, `ω*(δ) = O(δ^α)` if `α < 1`, and only
`ω*(δ) = O(δ log 1/δ)` if `α = 1`.
Modelling: on any set `A` of a metric space (the book's `A ⊆ ℂ`, and `ℝ` for the functions of Proposition 3.4); the
`O`-bounds are stated with constants on `(0, π)`, resp. `(0, 1/2)`; the sharpness in "only `O(δ log 1/δ)`" is not
stated. -/
theorem prop3_4_holder {X E : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E] {φ : X → E} {A : Set X}
    {M α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hH : HolderOnWith M α φ A) :
    IsDiniContinuous φ A ∧
      (α < 1 → ∃ K : ℝ, ∀ δ ∈ Ioo (0 : ℝ) π, omegaStar φ A δ ≤ ENNReal.ofReal (K * δ ^ (α : ℝ))) ∧
      (α = 1 → ∃ K : ℝ, ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), omegaStar φ A δ ≤ ENNReal.ofReal (K * δ * Real.log (1 / δ))) := by
  sorry

/-- **Unlabelled claim** (§3.3, l. 1989, continued). Thus Proposition 3.4 implies that `g` is Hölder-continuous in
`𝔻̄` if `φ` is Hölder-continuous with exponent `α`, `0 < α < 1`.
Modelling: `φ` is complex-valued and `2π`-periodic on `ℝ` as in Proposition 3.4; the Hölder exponent of `g` is `α`.
-/
theorem prop3_4_holder_g {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) {M α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hH : HolderWith M α φ) :
    ∃ (G : ℂ → ℂ) (K : ℝ≥0), ContinuousOn G (closedBall 0 1) ∧
      EqOn G (fun z : ℂ => I / (2 * π) *
        ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * φ t) unitDisc ∧
      HolderOnWith K α G (closedBall 0 1) := by
  sorry

/-- **Definition** (§3.3). The Jordan curve `C` is Dini-smooth: it has a parametrization `w(τ)`, `0 ≤ τ ≤ 2π`, such
that `w'(τ)` is Dini-continuous and `≠ 0`.
Modelling: `w` is `2π`-periodic and continuously differentiable, and `w'` is Dini-continuous on `ℝ`. -/
def IsDiniSmoothJordanCurve (C : Set ℂ) : Prop :=
  ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ContDiff ℝ 1 w ∧ (∀ τ, deriv w τ ≠ 0) ∧ IsDiniContinuous (deriv w) univ

/-- **Theorem 3.5** (§3.3). Let `f` map `𝔻` conformally onto the inner domain of the Dini-smooth Jordan curve `C`.
Then `f'` has a continuous extension to `𝔻̄` and (3.3.12) `(f(ζ) - f(z))/(ζ - z) → f'(z) ≠ 0` for `ζ → z`,
`ζ, z ∈ 𝔻̄`; (3.3.13) `|f'(z₁) - f'(z₂)| ≤ M₁ ω*(δ)` for `z₁, z₂ ∈ 𝔻̄`, `|z₁ - z₂| ≤ δ`, where (3.3.14) `ω` is the
modulus of continuity of `w'` for the Dini-smooth parametrization `w` of `C`.
Modelling: `F` is the continuous extension of `f` and `F'` that of `f'`; `M₁` depends on `f` and `w`; `δ ∈ (0, π)`,
the range of the definition of `ω*` (every pair of points of `𝔻̄` has `|z₁ - z₂| ≤ 2 < π`). -/
theorem thm3_5 {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {w : ℝ → ℂ} (hw : IsPeriodicParam C w)
    (hw1 : ContDiff ℝ 1 w) (hw0 : ∀ τ, deriv w τ ≠ 0) (hwD : IsDiniContinuous (deriv w) univ) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) :
    ∃ F' : ℂ → ℂ, ContinuousOn F' (closedBall 0 1) ∧ EqOn F' (deriv f) unitDisc ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, F' z ≠ 0 ∧
        Tendsto (fun ζ => (F ζ - F z) / (ζ - z)) (𝓝[closedBall 0 1 \ {z}] z) (𝓝 (F' z))) ∧
      ∃ M₁ : ℝ, ∀ z₁ ∈ closedBall (0 : ℂ) 1, ∀ z₂ ∈ closedBall (0 : ℂ) 1, ∀ δ ∈ Ioo (0 : ℝ) π, ‖z₁ - z₂‖ ≤ δ →
        ENNReal.ofReal ‖F' z₁ - F' z₂‖ ≤ ENNReal.ofReal M₁ * omegaStar (deriv w) univ δ := by
  sorry

/-- **Definition** (§3.3). The Jordan curve `C` is of class `C^n` (`n = 1, 2, …`): it has an `n` times continuously
differentiable parametrization `w(τ)`, `0 ≤ τ ≤ 2π`, with `w'(τ) ≠ 0`.
Modelling: `w` is `2π`-periodic; the book's range is `n ≥ 1` (the statements use only these `n`). -/
def IsJordanCurveCn (C : Set ℂ) (n : ℕ) : Prop :=
  ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ContDiff ℝ n w ∧ ∀ τ, deriv w τ ≠ 0

/-- **Definition (3.3.17)** (§3.3). The Jordan curve `C` is of class `C^{n,α}` (`0 < α ≤ 1`): of class `C^n` by a
parametrization with (3.3.17) `|w^{(n)}(τ₁) - w^{(n)}(τ₂)| ≤ M₁₀ |τ₁ - τ₂|^α`. -/
def IsJordanCurveCnAlpha (C : Set ℂ) (n : ℕ) (α : ℝ) : Prop :=
  ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ContDiff ℝ n w ∧ (∀ τ, deriv w τ ≠ 0) ∧
    ∃ M : ℝ, ∀ τ₁ τ₂ : ℝ, ‖iteratedDeriv n w τ₁ - iteratedDeriv n w τ₂‖ ≤ M * |τ₁ - τ₂| ^ α

/-- **Theorem 3.6** (§3.3; Kellogg–Warschawski). Let `f` map `𝔻` conformally onto the inner domain of the Jordan
curve `C` of class `C^{n,α}`, where `n = 1, 2, …` and `0 < α < 1`. Then `f^{(n)}` has a continuous extension to `𝔻̄`
and (3.3.18) `|f^{(n)}(z₁) - f^{(n)}(z₂)| ≤ M₁₁ |z₁ - z₂|^α` for `z₁, z₂ ∈ 𝔻̄`.
Modelling: `M₁₁` depends on `f` and `C`. -/
theorem thm3_6 {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hCn : IsJordanCurveCnAlpha C n α) {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (innerDomain C)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F (iteratedDeriv n f) unitDisc ∧
      ∃ M : ℝ, ∀ z₁ ∈ closedBall (0 : ℂ) 1, ∀ z₂ ∈ closedBall (0 : ℂ) 1, ‖F z₁ - F z₂‖ ≤ M * ‖z₁ - z₂‖ ^ α := by
  sorry

/-- **Unlabelled claim** (§3.3, l. 2141). It follows at once from Theorem 3.6 that all derivatives `f^{(n)}` are
continuous in `𝔻̄` if the Jordan curve `C` is of class `C^∞`, i.e. of class `C^n` for all `n`. The converse is trivial
because we can choose the conformal parametrization.
Modelling: "of class `C^n` for all `n`" allows a different parametrization for each `n` (unlike `IsJordanCurveCInfty`
of §3.1).
[CORRECTION] As for `kellogg_warschawski`, the right-hand side also requires the extension of `f'` to be `≠ 0` on
`𝔻̄`; without it the converse fails (`f(z) = z - z²/2`, the mechanism of Exercise 3.1.2). -/
theorem thm3_6_cinfty {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) :
    (∀ n : ℕ, 1 ≤ n → IsJordanCurveCn C n) ↔
      (∀ n : ℕ, ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F (iteratedDeriv n f) unitDisc) ∧
        ∃ F₁ : ℂ → ℂ, ContinuousOn F₁ (closedBall 0 1) ∧ EqOn F₁ (deriv f) unitDisc ∧
          ∀ z ∈ closedBall (0 : ℂ) 1, F₁ z ≠ 0 := by
  sorry

end Pommerenke1992
