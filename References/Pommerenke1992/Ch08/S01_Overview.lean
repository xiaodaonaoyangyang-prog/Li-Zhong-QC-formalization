import References.Pommerenke1992.Ch07.S05_MuckenhouptConditionsAndBMOA
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Pommerenke 1992, Ch. 8 §8.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…` (P1), lines 7405–7460. The chapter
continues in `full.md` of `…-798face3…` (P2): the seam lies in §8.5 (P1 l. 8120 is the last line of book p. 186, P2
l. 1 is the display (8.5.6) at the top of p. 187; nothing is lost), and §8.6 is P2 l. 87–390. The chapter heading is
lost in the OCR; the title is that of the table of contents.

**Summary.** The chapter studies the growth of the integral means `∫₀^{2π} |f(re^{it})|^p dt` (`0 < r < 1`) of a
conformal map `f` as `r → 1-`, and above all those of `f'`: `β_f(p)` is the smallest number such that
`∫₀^{2π} |f'(re^{it})|^p dt = O((1 - r)^{-β_f(p)-ε})` for every `ε > 0` (8.1.1). It is shown that
`sup_f β_f(p) = 3p - 1` for `p ≥ 2/5` (8.1.2) and `0.117p² < sup_f β_f(p) < 3.001p²` for small `p` (8.1.3)
(Feng–MacGregor, Clunie, Makarov and others); the Brennan conjecture `β_f(-2) ≤ 1` (8.1.4) is open, and only
`β_f(-2) < 1.601` is known. The proofs use differential inequalities. The case `p = 1` is connected with the growth of
the coefficients (§8.4). Section 8.5 bounds the integral means of Bloch functions and deduces the Makarov law of the
iterated logarithm (8.1.5); Section 8.6 treats lacunary series such as `g(z) = Σ_{k≥1} b_k z^{q^k}` (8.1.6), which lie
in `B` when `(b_k)` is bounded, give the lower bound in (8.1.3) and show that (8.1.5) is essentially best possible.
Chapter 10 applies these results to Hausdorff measure under conformal maps.

This section has no items of its own, so the file has no declarations: its one notion, the integral means, is
Mathlib's circle average (the `exists` bullet below), and its claims are previews of the labelled items of §8.2–§8.6
(see `Ch08/S02_UnivalentFunctions`, `Ch08/S03_DerivativesOfUnivalentFunctions`, `Ch08/S04_CoefficientProblems`,
`Ch08/S05_GrowthOfBlochFunctions`, `Ch08/S06_LacunarySeries`).

* Definition (the integral means of the conformal map `f`, P1 l. 7407–7411, and of `f'` in (8.1.1); used throughout
  the chapter) — exists: `Real.circleAverage` (the book's mean ∫₀^{2π} |g(re^{it})|^p dt, 0 < r < 1, is 2π times the
  average of |g|^p over the circle of radius r about 0; the factor 2π is written in each statement where the book has
  ∫₀^{2π} … dt or ∫ over 𝕋 with |dζ|, and the book's (1/2π)∫ is the circle average itself)
* Formula (8.1.1) (the first description of `β_f(p)`) — not an item: a preview of the definition (8.3.1) and of its
  O-form (8.3.2), both stated in §8.3; (8.1.1) is never cited
* Formulas (8.1.2), (8.1.3) (OCR: the tag "(2)" stands alone at P1 l. 7421 and the tag "(3)" sits on the first
  display) — not items: previews of Theorems 8.4–8.6 and of the example (8.3.5); (8.1.3) is cited only in §8.1
  (P1 l. 7457, "the lower bound in (3)")
* Formula (8.1.4), the Brennan conjecture, with "it is only known that `β_f(-2) < 1.601`" — not items: a conjecture
  (recorded, not formalized); the known bound is the case p = -2 of (8.3.15) in §8.3
* The remark on the case `p = 1` and the coefficients (P1 l. 7439) — not an item: a survey remark (see §8.4)
* Makarov Law of the Iterated Logarithm (named, (8.1.5), P1 l. 7441–7447) — not an item here: the identical statement
  is Theorem 8.10, (8.5.3), in §8.5, whose first part carries the name
* Formula (8.1.6), the lacunary series, "if `(b_k)` is bounded then `g ∈ B`", the connection with probability theory
  and the remarks on (8.1.3), (8.1.5) and Chapter 10 (P1 l. 7449–7459) — not items: previews of (8.6.1) and of
  Proposition 8.12, and remarks

**Conventions of Chapter 8** (the later files refer to them as "as in §8.1").
- "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc` (the Ch. 1 convention);
  "onto a quasidisk" is `IsConformalOnto f unitDisc (f '' unitDisc) ∧ IsQuasidisk (f '' unitDisc)`, the form of
  `cor5_23`; the class `S` is `LiZhongQC.knHyp`; a bounded univalent function is a conformal map of `𝔻` into `ℂ` with
  bounded image.
- Integral means: the book writes `∫₀^{2π} … dt` and `∫_𝕋 … |dζ|` (total mass `2π`, no `1/2π`) in (8.1.1),
  (8.2.4)–(8.2.8), (8.3.1), (8.3.2), (8.4.2)–(8.4.6), (8.6.9), and `(1/2π) ∫` in (8.2.9), (8.2.10), (8.5.2). The first
  is `2 * π * Real.circleAverage (fun z => …) 0 r`, the second `Real.circleAverage (fun z => …) 0 r`. The constants
  that depend on this normalization, (8.2.4) `2πp`, (8.4.2) `e/2π`, (8.2.10) and (8.5.2) `n!`, are stated as printed.
- `|g|^p` is `‖g z‖ ^ p` (`Real.rpow`); a negative exponent occurs only where the base has no zeros: `g = f'`, the
  powers `|f|^{p-2}` of Proposition 8.1 on the circles `|z| = r ≥ 1/2` (`f(0) = 0`, `f` univalent), `|g|^{p-2}` of
  Hardy's identity (under its hypotheses) and `|1 - z|^{-q}` of (8.2.10) on `|z| = r < 1`; so the junk value of
  `0 ^ p` is never seen.
- "`r → 1`" is `𝓝[<] 1`; `O(…)` is `Asymptotics.IsBigO` (along `𝓝[<] 1`, along `|z| → 1` in `𝔻`, that is
  `comap ‖·‖ (𝓝[<] 1)`, or along `atTop` for coefficients); "`∼`" is `Asymptotics.IsEquivalent`. Every `limsup` is
  taken in `EReal`, so it has a value (no real-`limsup` junk); the quotients inside are real numbers for `r` near `1`.
- "For almost all `ζ ∈ 𝕋`" is `∀ᵐ t : ℝ, P (exp (t * I))` (the `thm1_7` convention); "a set of positive measure" is
  `0 < circleMeasure A` (§4.4).
- `log f'` is any holomorphic `L` in `𝔻` with `exp ∘ L = f'` on `𝔻` (the `cor4_5` pattern); the statements hold for
  every branch.
- Bloch functions: `IsBloch`, `blochSeminorm` (`ℝ≥0∞`-valued; `.toReal` in inequalities), `IsLittleBloch` (§4.2);
  asymptotic values `HasAsymptoticValue` (§4.2); radial limits `HasRadialLimit` (§2.5).
- `Hᵖ` membership is `GarnettMarshall2005.MemHardy (ENNReal.ofReal p) f` (GM's (A.1), without `1/2π`; only
  membership is used, which does not depend on the factor).
- Constants: "`K(p)` depending only on `p`" is `∀ p, ∃ K, ∀ f …`; "for small `|p|`" is `∃ δ > 0, ∀ p, |p| < δ → …`.
-/

namespace Pommerenke1992

end Pommerenke1992
