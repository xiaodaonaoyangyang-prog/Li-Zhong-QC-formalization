import References.Pommerenke1992.Ch08.S04_CoefficientProblems

/-!
# Pommerenke 1992, Ch. 8 §8.5 The Growth of Bloch Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…` (P1), lines 8060–8120, continued in
`full.md` of `…-798face3…` (P2), lines 1–86 (the seam: P1 l. 8120 ends book p. 186 with "We can write (3) as", P2 l. 1
is (8.5.6) at the top of p. 187; nothing is lost).

* Definition (the class `B` and `‖g‖_B`, (8.5.1), restated from §4.2; cited in the proof of Theorem 8.9) — exists:
  `Pommerenke1992.blochSeminorm`, `Pommerenke1992.IsBloch` ((4.2.1), the same normalization)
* Theorem 8.9 (Mak85; (8.5.2); cited at P1 l. 8120, P2 l. 13, 2363 and in Exercise 8.5.3) — `thm8_9`
* Theorem 8.10 (the Makarov law of the iterated logarithm, Mak85; (8.5.3); named at P1 l. 7443 and 8098; cited at
  P2 l. 5, 65, 1705, 2369, by name at P2 l. 2022; the second part is proved at P2 l. 357–373) — `thm8_10_a`,
  `thm8_10_b`
* Corollary 8.11 (Mak85; (8.5.10); cited at P2 l. 2048, 2939) — `cor8_11_a`, `cor8_11_b`

Helper definition: `lilScale`, the normalizing function `√(log(1/(1 - r)) log log log(1/(1 - r)))` of (8.5.3) and
(8.5.10).

Not items (DESIGN §3): the probabilistic interpretation (8.5.4)–(8.5.6) (P1 l. 8108 – P2 l. 5): the process
`Z_t(ζ) = g((1 - e^{-t})ζ)` on `(𝕋, (2π)^{-1}Λ)` (printed "`(z ∈ 𝕋)`", read `ζ ∈ 𝕋`), its expectation `g(0)`, the
variance bound (8.5.5) (Theorem 8.9 with `n = 1`) and the one-sided law (8.5.6) (Theorem 8.10 with
`t = log 1/(1 - r)`), with the references Bin86, Bañ86, Lyo90, Mak89d (reformulations, not cited; no probability
library is used); (8.5.7)–(8.5.9), the Hardy–Littlewood maximal theorem (Dur70, p. 12) and Stirling's formula (proof
of Theorem 8.10); Exercises 8.5.1–8.5.4 (Exercise 8.5.1 is cited in the proof of Proposition 8.12, P2 l. 107).

**Conventions.** As in §8.1–§8.4. The book's `(1/2π) ∫_𝕋 … |dζ|` in (8.5.2) is `Real.circleAverage` itself.
`‖g‖_B` is `(blochSeminorm g).toReal`, finite for `g ∈ B`. "For almost all `ζ ∈ 𝕋`" is `∀ᵐ t : ℝ` with
`ζ = e^{it}`; `limsup_{r→1}` is the `EReal` `limsup` over `𝓝[<] 1`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc)

/-- **Theorem 8.9** (§8.5; Mak85; P1 l. 8070–8076; cited at P1 l. 8120, P2 l. 13, 2363 and in Exercise 8.5.3). If
`g ∈ B` and `g(0) = 0`, then (8.5.2) `(1/2π) ∫_𝕋 |g(rζ)|^{2n} |dζ| ≤ n! ‖g‖_B^{2n} (log 1/(1 - r²))ⁿ` for `0 < r < 1`
and `n = 0, 1, …`.
Modelling: the book's `(1/2π) ∫_𝕋 … |dζ|` is literally `circleAverage`, so the constant `n!` is stated as printed;
the powers are natural-number powers. -/
theorem thm8_9 {g : ℂ → ℂ} (hg : IsBloch g) (hg0 : g 0 = 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    Real.circleAverage (fun z => ‖g z‖ ^ (2 * n)) 0 r ≤
      (n.factorial : ℝ) * (blochSeminorm g).toReal ^ (2 * n) * Real.log (1 / (1 - r ^ 2)) ^ n := by
  sorry

/-- The normalizing function `√(log(1/(1 - r)) · log log log(1/(1 - r)))` of the laws of the iterated logarithm
(8.5.3) and (8.5.10) (helper). It is positive for `1 - e^{-e} < r < 1` (where `log log log(1/(1 - r)) > 0`) and is used
only as `r → 1-`; for other `r` the value is junk (`Real.log`, `Real.sqrt` of negative numbers) and no statement sees
it. -/
def lilScale (r : ℝ) : ℝ :=
  Real.sqrt (Real.log (1 / (1 - r)) * Real.log (Real.log (Real.log (1 / (1 - r)))))

/-- **Theorem 8.10** (§8.5; the Makarov law of the iterated logarithm, Mak85; named at P1 l. 7443 and 8098;
P1 l. 8100–8106; cited at P2 l. 5, 65, 1705, 2369, by name at P2 l. 2022), first part. If `g ∈ B`, then, for almost
all `ζ ∈ 𝕋`, (8.5.3) `limsup_{r→1} |g(rζ)|/√(log(1/(1 - r)) log log log(1/(1 - r))) ≤ ‖g‖_B`.
Modelling: `ζ = e^{it}` for almost every `t ∈ ℝ` (the `thm1_7` convention); the `limsup` over `r → 1-` is taken in
`EReal`; the denominator is `lilScale r`, positive for `r` near `1`. -/
theorem thm8_10_a {g : ℂ → ℂ} (hg : IsBloch g) :
    ∀ᵐ t : ℝ, limsup (fun r : ℝ => ((‖g (r * exp (t * I))‖ / lilScale r : ℝ) : EReal)) (𝓝[<] 1) ≤
      ((blochSeminorm g).toReal : EReal) := by
  sorry

/-- **Theorem 8.10** (§8.5), second part (proved at the end of §8.6, P2 l. 357–373). There exists `g ∈ B` such that
this `limsup` is `> 0.685 ‖g‖_B` for almost all `ζ ∈ 𝕋`.
Modelling: as in `thm8_10_a`; the strict inequality excludes `g` constant (for which both sides are `0`). -/
theorem thm8_10_b :
    ∃ g : ℂ → ℂ, IsBloch g ∧ ∀ᵐ t : ℝ, ((0.685 * (blochSeminorm g).toReal : ℝ) : EReal) <
      limsup (fun r : ℝ => ((‖g (r * exp (t * I))‖ / lilScale r : ℝ) : EReal)) (𝓝[<] 1) := by
  sorry

/-- **Corollary 8.11** (§8.5; Mak85; P2 l. 57–65; cited at P2 l. 2048, 2939), first part. If `f` maps `𝔻` conformally
into `ℂ`, then (8.5.10) `limsup_{r→1} |log f'(rζ)|/√(log(1/(1 - r)) log log log(1/(1 - r))) ≤ 6` for almost all
`ζ ∈ 𝕋` ("from Theorem 8.10 and `‖log f'‖_B ≤ 6` by Proposition 4.1").
Modelling: `log f'` is any holomorphic logarithm `L` of `f'` in `𝔻` (branches differ by constants `2πik`, which the
`limsup` does not see); the `limsup` as in `thm8_10_a`. -/
theorem cor8_11_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L unitDisc) (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) :
    ∀ᵐ t : ℝ, limsup (fun r : ℝ => ((‖L (r * exp (t * I))‖ / lilScale r : ℝ) : EReal)) (𝓝[<] 1) ≤
      ((6 : ℝ) : EReal) := by
  sorry

/-- **Corollary 8.11** (§8.5), second part. If `f` maps `𝔻` conformally into `ℂ`, then in particular
`f'(rζ) = O((1 - r)^{-ε})` as `r → 1` for `ε > 0` and almost all `ζ ∈ 𝕋`.
Modelling: one null set for all `ε > 0` (`∀ᵐ t, ∀ ε > 0`), as (8.5.10) gives; this is stronger than
`∀ ε > 0, ∀ᵐ t`. -/
theorem cor8_11_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∀ᵐ t : ℝ, ∀ ε > (0 : ℝ), Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => deriv f (r * exp (t * I)))
      (fun r : ℝ => (1 - r) ^ (-ε)) := by
  sorry

end Pommerenke1992
