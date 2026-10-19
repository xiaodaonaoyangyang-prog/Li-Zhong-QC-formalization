import References.Pommerenke1992.Ch08.S02_UnivalentFunctions

/-!
# Pommerenke 1992, Ch. 8 §8.3 Derivatives of Univalent Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…` (P1), lines 7585–7915.

* Definition (`β_f(p)`, (8.3.1); cited at P1 l. 7661, 7970 and P2 l. 2090, 2560, 2570) — `integralMeansSpectrum`
* Formula (8.3.2) (cited at P1 l. 7856; its infimum form is used at P2 l. 2090) — `eq8_3_2`
* Proposition 8.3 ((8.3.3); cited at P1 l. 7661, 7729, 7735, 7970 and P2 l. 2594) — `prop8_3_a`, `prop8_3_b`
* Formula (8.3.5) (the example `f_α`; its claim is cited at P1 l. 7729 and 7735) — `eq8_3_5`
* Theorem 8.4 (Feng–MacGregor, FeMG76; (8.3.6), (8.3.7); cited at P1 l. 7721, 7735, 7746 and P2 l. 2136, 2578) —
  `thm8_4_a`, `thm8_4_b`
* Theorem 8.5 (ClPo67, Pom85; (8.3.11), (8.3.12); cited at P1 l. 7735, 7754, 7970 and P2 l. 2136, 2594) —
  `thm8_5_a`, `thm8_5_b`
* Unlabelled (§8.3, P1 l. 7713: the right-hand side of (8.3.11) is `< 3p²` for `p < 0` and `< 3p² + 7p³` for
  `p > 0`; used at P2 l. 2133 and 2597) — `thm8_5_rhs_bound`
* Theorem 8.6 (Mak86, Roh89; (8.3.13); cited at P1 l. 7735; proved in §8.6, P2 l. 247–253) — `thm8_6`
* Formula (8.3.15) (cited at P1 l. 7746) — `eq8_3_15`
* Proposition 8.7 (BeBe65, Her72; (8.3.17)–(8.3.19); cited at P1 l. 7850, 7888) — `prop8_7`

Not items (DESIGN §3): (8.3.4), the convexity inequality, and the bound
`|f'(0)|(1 - |z|)/8 ≤ |f'(z)| ≤ 2|f'(0)|(1 - |z|)^{-3}` (steps of the proof of Proposition 8.3; the bound is
Theorem 1.3); the remark that sharp estimates (FeMG76) are known only for `p > 2/5` and for close-to-convex functions
(P1 l. 7635); (8.3.8)–(8.3.10) and Littlewood's subordination theorem (Dur70; quoted inside the proof of Theorem 8.4
only); "a miracle happens for `p = -1`", also for `f` with a pole (P1 l. 7713; not cited); "(6) need not hold for
`p = 1/3`" (P1 l. 7721; immediate from Theorem 8.6 and the convexity in Proposition 8.3, not cited); (8.3.14), the
Brennan conjecture (Bre78), "sharp by (5) with `α = 2`" and its equivalence with `β_f(-2) ≤ 1` (a conjecture,
recorded and not formalized; the equivalence is immediate from (8.3.3)); Fig. 8.1; (8.3.16), `f' ∈ Lᵖ(𝔻)` for
`-1.399 ≤ p < 2/3`, and its Brennan version (not cited); (8.3.20), the case `n = 2` of Proposition 8.7 (omitted,
U−: the special case of the hypotheses, cited at P1 l. 7850 as a hypothesis check); (8.3.21)–(8.3.27), the equations
(24), (25) and
`λ(λ + 1)(λ + 2)(λ + 3) = 9.01` (proof of Theorem 8.5, which also uses Exercise 8.2.1, Proposition 1.2 and
Exercise 1.3.6); Exercises 8.3.1–8.3.5 (Exercise 8.3.4 is cited by Exercise 10.5.4, P2 l. 2687).

**Conventions.** As in §8.1, §8.2. The integral `∫_𝕋 |f'(rζ)|^p |dζ| = ∫₀^{2π} |f'(re^{it})|^p dt` is
`2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r`; `f'` has no zeros for a conformal `f`, so the power is
never the junk `0 ^ p`. `β_f(p)` is `EReal`-valued, and inequalities for it are stated in `EReal` against coerced real
numbers; its finiteness is part of Proposition 8.3 (`prop8_3_a`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc IsConformalOnto)

/-- **Definition (8.3.1)** (§8.3; P1 l. 7587–7591; cited at P1 l. 7661, 7970 and P2 l. 2090, 2560, 2570). For a
conformal map `f` of `𝔻` into `ℂ` and `p ∈ ℝ`,
`β(p) = β_f(p) = limsup_{r→1-} (log ∫_𝕋 |f'(rζ)|^p |dζ|)/log(1/(1 - r))`.
Modelling: `∫_𝕋 … |dζ| = 2π · circleAverage`; the `limsup` over `𝓝[<] 1` is taken in `EReal`, so that it always has
a value (no real-`limsup` junk). For `0 < r < 1` the quotient is a genuine real number: the integral is positive
(`f'` has no zeros) and `log(1/(1 - r)) > 0`; the `limsup` does not see `r` away from `1`. For `f` that is not
conformal the value is junk (through `deriv`); every statement assumes `f` conformal. The Lean name follows GM's term
"integral means spectrum" (GM (VIII.4.2) is the O-form (8.3.2)). -/
def integralMeansSpectrum (f : ℂ → ℂ) (p : ℝ) : EReal :=
  limsup (fun r : ℝ => ((Real.log (2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r) /
    Real.log (1 / (1 - r)) : ℝ) : EReal)) (𝓝[<] 1)

/-- **Formula (8.3.2)** (§8.3; P1 l. 7593–7597; cited at P1 l. 7856; the infimum form is used as the definition of
`β_f(-q)` at P2 l. 2090, "as in (8.3.1)"). Let `f` map `𝔻` conformally into `ℂ`. Thus `β(p)` is the smallest number
such that, for every `ε > 0`, `∫₀^{2π} |f'(re^{it})|^p dt = O(1/(1 - r)^{β(p)+ε})` as `r → 1-`.
Modelling: first conjunct: for every real `b`, `β_f(p) ≤ b` if and only if `b` has the property (for every `ε > 0`
the mean is `O(1/(1 - r)^{b+ε})`); so the real numbers with the property are exactly those `≥ β_f(p)`, and `β_f(p)`
(finite by `prop8_3_a`) is the smallest of them. Second conjunct: the equivalent infimum form
`β_f(p) = inf {β ∈ ℝ : ∫₀^{2π} |f'(re^{it})|^p dt = O((1 - r)^{-β})}` of P2 l. 2090 and GM (VIII.4.2), an infimum in
`EReal`. -/
theorem eq8_3_2 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) (p : ℝ) :
    (∀ b : ℝ, integralMeansSpectrum f p ≤ (b : EReal) ↔ ∀ ε > (0 : ℝ),
      Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r)
        (fun r : ℝ => 1 / (1 - r) ^ (b + ε))) ∧
    integralMeansSpectrum f p = sInf ((fun β : ℝ => (β : EReal)) '' {β : ℝ |
      Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r)
        (fun r : ℝ => (1 - r) ^ (-β))}) := by
  sorry

/-- **Proposition 8.3** (§8.3; P1 l. 7599–7603; cited at P1 l. 7661, 7729, 7735, 7970 and P2 l. 2594), first part.
Let `f` map `𝔻` conformally into `ℂ`. The function `β_f` is continuous and convex in `ℝ`.
Modelling: `β_f` takes finite values (implicit in "continuous and convex in `ℝ`"): it is a real function `β` that is
convex on `ℝ` and continuous. -/
theorem prop8_3_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∃ β : ℝ → ℝ, (∀ p : ℝ, integralMeansSpectrum f p = (β p : EReal)) ∧ ConvexOn ℝ univ β ∧ Continuous β := by
  sorry

/-- **Proposition 8.3** (§8.3), second part, (8.3.3). Let `f` map `𝔻` conformally into `ℂ`. Then
`β(p + q) ≤ β(p) + 3q` if `q > 0`, and `β(p + q) ≤ β(p) + |q|` if `q < 0`. -/
theorem prop8_3_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) (p q : ℝ) :
    (0 < q → integralMeansSpectrum f (p + q) ≤ integralMeansSpectrum f p + ((3 * q : ℝ) : EReal)) ∧
      (q < 0 → integralMeansSpectrum f (p + q) ≤ integralMeansSpectrum f p + ((|q| : ℝ) : EReal)) := by
  sorry

/-- **Formula (8.3.5)** (§8.3; P1 l. 7623–7633; the claim of this example is cited at P1 l. 7729, "sharp by (5) with
`α = 2`", and P1 l. 7735). Consider the conformal map `f_α(z) = ((1 + z)/(1 - z))^α`,
`f_α'(z) = 2α (1 + z)^{α-1}/(1 - z)^{α+1}`, where `1 < α ≤ 2`. Then (by (8.2.10)) `β_{f_α}(p) = (α + 1)p - 1` if
`1/(α + 1) < p < +∞`, `β_{f_α}(p) = (α - 1)|p| - 1` if `-∞ < p < -1/(α - 1)`, and `β_{f_α}(p) = 0` otherwise.
Modelling: `f_α` is the principal power (`cpow`) of `(1 + z)/(1 - z)`, which lies in the right half-plane for
`z ∈ 𝔻`, so `f_α` is analytic there; it maps `𝔻` conformally onto the sector `|arg w| < απ/2` (`απ ≤ 2π`). -/
theorem eq8_3_5 {α : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) (p : ℝ) :
    integralMeansSpectrum (fun z => ((1 + z) / (1 - z)) ^ (α : ℂ)) p =
      if 1 / (α + 1) < p then (((α + 1) * p - 1 : ℝ) : EReal)
      else if p < -1 / (α - 1) then (((α - 1) * |p| - 1 : ℝ) : EReal) else 0 := by
  sorry

/-- **Theorem 8.4** (§8.3; Feng–MacGregor, FeMG76; P1 l. 7637–7647; cited at P1 l. 7721, 7735, 7746 and P2 l. 2136,
2578), first part. Let `f` map `𝔻` conformally into `ℂ`. Then (8.3.6) `β_f(p) ≤ 3p - 1` for `2/5 ≤ p < +∞`. -/
theorem thm8_4_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {p : ℝ}
    (hp : 2 / 5 ≤ p) :
    integralMeansSpectrum f p ≤ ((3 * p - 1 : ℝ) : EReal) := by
  sorry

/-- **Theorem 8.4** (§8.3), second part. If `f` is close-to-convex, then (8.3.7) `β_f(p) ≤ |p| - 1` for
`-∞ < p < -1`, `β_f(p) ≤ 0` for `-1 ≤ p ≤ 1/3`, and `β_f(p) ≤ 3p - 1` for `1/3 < p < ∞`.
Modelling: close-to-convex is `IsCloseToConvex` ((3.6.14)); such an `f` is univalent (Proposition 3.20), hence a
conformal map of `𝔻` into `ℂ` as the theorem assumes. -/
theorem thm8_4_b {f : ℂ → ℂ} (hf : IsCloseToConvex f) (p : ℝ) :
    (p < -1 → integralMeansSpectrum f p ≤ ((|p| - 1 : ℝ) : EReal)) ∧
      (-1 ≤ p → p ≤ 1 / 3 → integralMeansSpectrum f p ≤ 0) ∧
      (1 / 3 < p → integralMeansSpectrum f p ≤ ((3 * p - 1 : ℝ) : EReal)) := by
  sorry

/-- **Theorem 8.5** (§8.3; ClPo67, Pom85; P1 l. 7699–7711; cited at P1 l. 7735, 7754, 7970 and P2 l. 2136, 2594),
first part. If `f` maps `𝔻` conformally into `ℂ`, then (8.3.11) `β_f(p) ≤ p - 1/2 + (4p² - p + 1/4)^{1/2}` for
`p ∈ ℝ`.
Modelling: `4p² - p + 1/4 = (2p - 1/4)² + 3/16 > 0`, so `Real.sqrt` sees no junk. -/
theorem thm8_5_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) (p : ℝ) :
    integralMeansSpectrum f p ≤ ((p - 1 / 2 + Real.sqrt (4 * p ^ 2 - p + 1 / 4) : ℝ) : EReal) := by
  sorry

/-- **Theorem 8.5** (§8.3), second part. If `f` maps `𝔻` conformally into `ℂ`, then (8.3.12) `β_f(-1) < 0.601`. -/
theorem thm8_5_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    integralMeansSpectrum f (-1) < ((0.601 : ℝ) : EReal) := by
  sorry

/-- **Unlabelled claim** (§8.3, P1 l. 7713; used at P2 l. 2133 and 2597, in the proofs of Theorem 10.9 and
Corollary 10.19). The right-hand side of (8.3.11), `p - 1/2 + (4p² - p + 1/4)^{1/2}`, is `< 3p²` for `p < 0` and
`< 3p² + 7p³` for `p > 0`. -/
theorem thm8_5_rhs_bound (p : ℝ) :
    (p < 0 → p - 1 / 2 + Real.sqrt (4 * p ^ 2 - p + 1 / 4) < 3 * p ^ 2) ∧
      (0 < p → p - 1 / 2 + Real.sqrt (4 * p ^ 2 - p + 1 / 4) < 3 * p ^ 2 + 7 * p ^ 3) := by
  sorry

/-- **Theorem 8.6** (§8.3; Mak86, Roh89; P1 l. 7715–7719; cited at P1 l. 7735; proved in §8.6, P2 l. 247–253). There
exists a conformal map `f` of `𝔻` onto a quasidisk such that `β_f(-1) > 0.109` and (8.3.13) `β_f(p) ≥ 0.117p²` for
small `|p|`.
Modelling: one `f` for both claims; "for small `|p|`" is `∃ δ > 0, ∀ p, |p| < δ → …`; "onto a quasidisk" is the form
of `cor5_23`. -/
theorem thm8_6 :
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc (f '' unitDisc) ∧ IsQuasidisk (f '' unitDisc) ∧
      ((0.109 : ℝ) : EReal) < integralMeansSpectrum f (-1) ∧
      ∃ δ > (0 : ℝ), ∀ p : ℝ, |p| < δ → ((0.117 * p ^ 2 : ℝ) : EReal) ≤ integralMeansSpectrum f p := by
  sorry

/-- **Formula (8.3.15)** (§8.3; P1 l. 7729–7733; cited at P1 l. 7746). If `f` maps `𝔻` conformally into `ℂ`, then
`β_f(p) < |p| - 0.399` for `-∞ < p ≤ -1` ("which follows from (12) and (3)"). -/
theorem eq8_3_15 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {p : ℝ}
    (hp : p ≤ -1) :
    integralMeansSpectrum f p < ((|p| - 0.399 : ℝ) : EReal) := by
  sorry

/-- **Proposition 8.7** (§8.3; BeBe65, p. 139, Her72; P1 l. 7754–7772; cited at P1 l. 7850, 7888). Let `n ≥ 2` and let
`a_k(r)` (`k = 0, …, n - 1`) be continuous in `r₀ ≤ r < 1`. Assume (8.3.17) `a_k(r) ≥ 0` for `k = 0, …, n - 2`. Let
`u` and `v` be `n` times differentiable in `[r₀, 1)` and (8.3.18) `u⁽ⁿ⁾ < Σ_{k=0}^{n-1} a_k u⁽ᵏ⁾`,
`v⁽ⁿ⁾ = Σ_{k=0}^{n-1} a_k v⁽ᵏ⁾`. If `u⁽ᵏ⁾(r₀) < v⁽ᵏ⁾(r₀)` for `k = 0, …, n - 1`, then (8.3.19) `u(r) < v(r)` for
`r₀ ≤ r < 1`.
Modelling: the derivatives are `iteratedDerivWithin k · (Ico r₀ 1)` (one-sided at `r₀`); "`n` times differentiable in
`[r₀, 1)`" is the differentiability on `[r₀, 1)` of the derivatives of the orders `k < n`; (8.3.17) and (8.3.18) hold
on `[r₀, 1)`; `r₀ < 1`. As the book notes, `a_{n-1}` may have any sign. -/
theorem prop8_7 {n : ℕ} (hn : 2 ≤ n) {r₀ : ℝ} (hr₀ : r₀ < 1) {a : ℕ → ℝ → ℝ}
    (ha : ∀ k < n, ContinuousOn (a k) (Ico r₀ 1)) (ha0 : ∀ k, k + 2 ≤ n → ∀ r ∈ Ico r₀ 1, 0 ≤ a k r)
    {u v : ℝ → ℝ} (hu : ∀ k < n, DifferentiableOn ℝ (iteratedDerivWithin k u (Ico r₀ 1)) (Ico r₀ 1))
    (hv : ∀ k < n, DifferentiableOn ℝ (iteratedDerivWithin k v (Ico r₀ 1)) (Ico r₀ 1))
    (hun : ∀ r ∈ Ico r₀ 1, iteratedDerivWithin n u (Ico r₀ 1) r <
      ∑ k ∈ Finset.range n, a k r * iteratedDerivWithin k u (Ico r₀ 1) r)
    (hvn : ∀ r ∈ Ico r₀ 1, iteratedDerivWithin n v (Ico r₀ 1) r =
      ∑ k ∈ Finset.range n, a k r * iteratedDerivWithin k v (Ico r₀ 1) r)
    (h₀ : ∀ k < n, iteratedDerivWithin k u (Ico r₀ 1) r₀ < iteratedDerivWithin k v (Ico r₀ 1) r₀) :
    ∀ r ∈ Ico r₀ 1, u r < v r := by
  sorry

end Pommerenke1992
