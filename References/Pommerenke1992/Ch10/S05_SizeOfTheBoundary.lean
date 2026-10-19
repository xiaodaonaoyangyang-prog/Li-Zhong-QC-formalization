import References.Pommerenke1992.Ch10.S04_ZygmundMeasuresAndTheAngularDerivative

/-!
# Pommerenke 1992, Ch. 10 §10.5 The Size of the Boundary

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 10 *Hausdorff Measure*, §10.5; source `full.md`
of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 2504–2688.

* Definition (`N(ε, E)`, the minimal number of disks of diameter `ε` that are needed to cover the bounded set `E`,
  l. 2508; used in (10.5.1)–(10.5.5); index "`N(ε,E)` 240") — exists: `Metric.externalCoveringNumber` (at the radius
  ε/2, leader ruling QD3: the minimal number, in ℕ∞, of closed discs of radius ε/2, that is of diameter ε, with
  centres anywhere, covering E; written with Real.toNNReal (ε/2), which is ε/2 for ε > 0)
* Definition (the (upper) Minkowski dimension, (10.5.1), l. 2508–2514; index "Minkowski dimension 223, 240–242, 244",
  "mdim E 240", "box dimension 223", "entropy dimension 223"; used in Proposition 10.16, Corollaries 10.18, 10.19 and
  Exercises 10.5) — `minkowskiDim`
* Proposition 10.16 ((10.5.2), l. 2516–2520) — `prop10_16`
* Theorem 10.17 (Pom89; (10.5.3)–(10.5.5), l. 2540–2558; cited at l. 2560, 2576 and 2594) — `thm10_17_a`,
  `thm10_17_b`
* Corollary 10.18 (l. 2562–2568; cited at l. 1731) — `cor10_18`
* Corollary 10.19 (Pom89; (10.5.6), (10.5.7), l. 2580–2590; cited at P1 l. 7952, "see also Corollary 10.19") —
  `cor10_19_a`, `cor10_19_b`

Not items (DESIGN §3): "For many purposes coverings by sets (e.g. disks) of the same size is more natural" (l. 2506;
motivation); "Up to bounded multiples it is the same as the number of squares of a grid of mesh size `ε` that
intersect `E`" (l. 2508; U−, used only in proofs); the Example of the comb continuum
`[0, 1] ∪ ⋃_n ⋃_{ν ≤ n^{3/4}} [ν/n, (1 + i)ν/n]` with σ-finite linear measure, `dim E = 1` and `mdim E ≥ 3/2`, and
the remark on Hut81, MaVu87 (l. 2530–2538); "(5) is slightly weaker than (3)", "every (bounded) quasidisk is a John
domain" (the recall of Theorem 5.9) and "Let `β_f(p)` be defined by (8.3.1)" (l. 2560; a remark, a recall and a
pointer); the proof of Corollary 10.18 (Theorem 5.2 (iii)) and the example of a bounded starlike domain with
`area ∂G > 0` ("mdim `E` = 2" [misprint? mdim `∂G`], `β_f(p) ≤ p − 1`, "see the proof of Theorem 8.4";
l. 2570–2578); "This statement is more precise than (8.4.5) which corresponds to `p = 2`; see also CaJo91" (l. 2592;
a remark); the proofs of Corollary 10.19 and Theorem 10.17 ((10.5.8)–(10.5.13), Fig. 10.4, l. 2594–2671; Proposition
8.3, Theorem 8.5 with the Part C bound `thm8_5_rhs_bound`, (8.4.2), Corollary 1.6, Theorem 5.2 (iii), Corollary 5.3,
and "Corollary 4.19", which is Proposition 4.19, P1 l. 3709 [misprint?]); Exercises 10.5.1–10.5.4 (Exercise 10.5.4
cites Exercise 8.3.4 and the Lehto majorant principle).

**Conventions.** As in §10.2. `N(ε, E)` is `externalCoveringNumber (Real.toNNReal (ε / 2)) E` (in `ℕ∞`); for a
bounded nonempty `E` and `ε > 0` it is finite and at least `1`. The `O`-statements for `N` are phrased in `[0, ∞]`,
`∃ C < ∞, ∀ᶠ ε in 𝓝[>] 0, N(ε, E) ≤ C · bound(ε)` (no cast from `ℕ∞` to `ℝ`; Q10.14(c)); the other `O`-statements are
`Asymptotics.IsBigO`. Open or closed discs, or disc covers against grid squares, change `N` only by bounded
multiples, which neither `mdim` nor any `O`-statement sees. `mdim` is `EReal`-valued, as `β_f` (`integralMeansSpectrum`,
Chapter 8); `dim E` is compared in `EReal` through the coercion from `[0, ∞]`. A John domain is `IsJohnDomain` (§5.2),
and the coefficients `a_n` of `f(z) = Σ a_n zⁿ` are `sCoeff f n` ((1.3.1)).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc IsConformalOnto)

/-- **Definition (10.5.1)** (§10.5; P2 l. 2508–2514; used in Proposition 10.16, Corollaries 10.18, 10.19 and
Exercises 10.5). For a bounded set `E` in `ℂ`, the (upper) Minkowski dimension of `E` is
`mdim E = limsup_{ε→0} log N(ε, E)/log(1/ε)`.
Modelling: the `limsup` over `ε → 0+` of the real quotient, taken in `EReal` (so it always has a value); `N(ε, E)` is
`Metric.externalCoveringNumber` at the radius `ε/2` (see the file header). The definition is used only for bounded
nonempty `E`: there `N(ε, E)` is finite and at least `1` for `ε > 0`, so neither `ENat.toNat ⊤ = 0` nor
`Real.log 0 = 0` is seen, and `log(1/ε) > 0` for `ε < 1`; for other `E` the value is junk that no statement uses.
Mathlib has no box dimension. -/
def minkowskiDim (E : Set ℂ) : EReal :=
  limsup (fun ε : ℝ => ((Real.log ((externalCoveringNumber (Real.toNNReal (ε / 2)) E).toNat : ℝ) /
    Real.log (1 / ε) : ℝ) : EReal)) (𝓝[>] 0)

/-- **Proposition 10.16** (§10.5; (10.5.2); P2 l. 2516–2520). If `E` is any bounded set in `ℂ`, then (2)
`dim E ≤ liminf_{ε→0} log N(ε, E)/log(1/ε) ≤ mdim E`.
Modelling: `E` is nonempty (Q10.14(b): for `E = ∅` the book's `log N(ε, ∅) = log 0` is undefined); the `liminf`
over `ε → 0+` is taken in `EReal`, like the `limsup` of `minkowskiDim`, and `dim E` is `dimH E` coerced to
`EReal`. -/
theorem prop10_16 {E : Set ℂ} (hE : Bornology.IsBounded E) (hne : E.Nonempty) :
    ((dimH E : ℝ≥0∞) : EReal) ≤ liminf (fun ε : ℝ => ((Real.log
        ((externalCoveringNumber (Real.toNNReal (ε / 2)) E).toNat : ℝ) / Real.log (1 / ε) : ℝ) : EReal)) (𝓝[>] 0) ∧
      liminf (fun ε : ℝ => ((Real.log ((externalCoveringNumber (Real.toNNReal (ε / 2)) E).toNat : ℝ) /
        Real.log (1 / ε) : ℝ) : EReal)) (𝓝[>] 0) ≤ minkowskiDim E := by
  sorry

/-- **Theorem 10.17** (§10.5; Pom89; (10.5.3), (10.5.4); P2 l. 2540–2552; cited at P2 l. 2560, in the proof of
Corollary 10.18, l. 2576, and in the proof of Corollary 10.19, l. 2594), first part. Let `f` map `𝔻` conformally onto
a bounded domain `G` and let `1 ≤ p ≤ 2`. If (3) `N(ε, ∂G) = O(ε^{−p})` as `ε → 0`, then (4)
`∫_𝕋 |f'(rζ)|^p |dζ| = O((1 − r)^{−(p−1)} log 1/(1 − r))` as `r → 1`.
Modelling: `∂G` is `frontier G`; (3) is `∃ C < ∞, ∀ᶠ ε → 0+, N(ε, ∂G) ≤ C ε^{−p}` in `[0, ∞]` (Q10.14(c)); (4) is
`Asymptotics.IsBigO` along `r → 1−`, with the integral written `2π · circleAverage` (Chapter 8); both are
`O`-statements, so the normalization of `N` does not matter. -/
theorem thm10_17_a {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hG : Bornology.IsBounded G)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (h3 : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (externalCoveringNumber (Real.toNNReal (ε / 2)) (frontier G) : ℝ≥0∞) ≤ C * ENNReal.ofReal (ε ^ (-p))) :
    Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r)
      (fun r : ℝ => (1 - r) ^ (1 - p) * Real.log (1 / (1 - r))) := by
  sorry

/-- **Theorem 10.17** (§10.5; (10.5.4), (10.5.5); P2 l. 2554–2558), second part. In the setting of `thm10_17_a`, if
(4) holds and if `G` is a John domain, then (5) `N(ε, ∂G) = O(ε^{−p} (log 1/ε)²)` as `ε → 0`.
Modelling: as in `thm10_17_a`; a John domain is `IsJohnDomain` (§5.2). -/
theorem thm10_17_b {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hG : Bornology.IsBounded G)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (h4 : Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r)
      (fun r : ℝ => (1 - r) ^ (1 - p) * Real.log (1 / (1 - r))))
    (hJ : IsJohnDomain G) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (externalCoveringNumber (Real.toNNReal (ε / 2)) (frontier G) : ℝ≥0∞) ≤
        C * ENNReal.ofReal (ε ^ (-p) * Real.log (1 / ε) ^ 2) := by
  sorry

/-- **Corollary 10.18** (§10.5; P2 l. 2562–2568; cited at P2 l. 1731, §10.1). If `f` maps `𝔻` conformally onto a John
domain `G`, then `mdim ∂G = p`, where `p` is the unique solution of `β_f(p) = p − 1`.
Modelling (Q10.16: one declaration, as the book states one sentence): the equation `β_f(p′) = p′ − 1`, in `EReal`
with `β_f = integralMeansSpectrum f`, has exactly one real solution `p`, and `minkowskiDim (frontier G) = p`. -/
theorem cor10_18 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hJ : IsJohnDomain G) :
    ∃ p : ℝ, (∀ p' : ℝ, integralMeansSpectrum f p' = ((p' - 1 : ℝ) : EReal) ↔ p' = p) ∧
      minkowskiDim (frontier G) = (p : EReal) := by
  sorry

/-- **Corollary 10.19** (§10.5; Pom89; (10.5.6); P2 l. 2580–2584; cited at P1 l. 7952, §8.4, "see also
Corollary 10.19"), first part. Let `f(z) = Σ a_n zⁿ` map `𝔻` conformally onto a bounded domain `G` with
`mdim ∂G = p`. If `p = 1`, then (6) `a_n = O(n^{ε−1})` (`n → ∞`) for every `ε > 0`.
Modelling: `a_n` is `sCoeff f n` (the Taylor coefficients at `0`, (1.3.1)); `O` as `n → ∞` is
`Asymptotics.IsBigO atTop`, with a constant that may depend on `f` and `ε`; `mdim ∂G` is
`minkowskiDim (frontier G)`; the OCR's "map D" is `𝔻`. -/
theorem cor10_19_a {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hG : Bornology.IsBounded G)
    (hmdim : minkowskiDim (frontier G) = 1) {ε : ℝ} (hε : 0 < ε) :
    Asymptotics.IsBigO atTop (fun n : ℕ => sCoeff f n) (fun n : ℕ => (n : ℝ) ^ (ε - 1)) := by
  sorry

/-- **Corollary 10.19** (§10.5; (10.5.7); P2 l. 2586–2590), second part. In the setting of `cor10_19_a`, if `p > 1`,
then there is `η = η(p) > 0` such that (7) `a_n = O(n^{−η−1/p})` as `n → ∞`.
Modelling: `η` depends only on `p` (`∀ p > 1, ∃ η > 0, ∀ f G`); the `O`-constant may depend on `f`; otherwise as in
`cor10_19_a`. -/
theorem cor10_19_b {p : ℝ} (hp : 1 < p) :
    ∃ η : ℝ, 0 < η ∧ ∀ (f : ℂ → ℂ) (G : Set ℂ), IsConformalOnto f unitDisc G → Bornology.IsBounded G →
      minkowskiDim (frontier G) = (p : EReal) →
        Asymptotics.IsBigO atTop (fun n : ℕ => sCoeff f n) (fun n : ℕ => (n : ℝ) ^ (-η - 1 / p)) := by
  sorry

end Pommerenke1992
