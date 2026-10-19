import References.Pommerenke1992.Ch08.S03_DerivativesOfUnivalentFunctions

/-!
# Pommerenke 1992, Ch. 8 §8.4 Coefficient Problems

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 8 *Integral Means*, §8.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…` (P1), lines 7916–8059.

* Formula (8.4.1) (the coefficients `aₙ` of `f(z) = Σ aₙ zⁿ`) — exists: `Pommerenke1992.sCoeff` (aₙ = f⁽ⁿ⁾(0)/n!,
  the Taylor coefficients of (1.3.1), the same coefficients)
* Formula (8.4.2) (cited at P1 l. 7962 and P2 l. 2600) — `eq8_4_2`
* Theorem 8.8 (LiPa32; ClPo67, Pom85; (8.4.3)–(8.4.5); (8.4.5) cited at P2 l. 2592) — `thm8_8_a`, `thm8_8_b`
* Formula (8.4.7) (CaJo91, quoted; cited at P1 l. 7984 and 7998) — `eq8_4_7`
* Formula (8.4.9) (the class `Σ` and its coefficients `bₙ`, restated from §1.3) — exists:
  `Pommerenke1992.IsClassSigma`, `Pommerenke1992.sigmaCoeff` (the class and the coefficients of (1.3.2))
* Definition (the class `S`, restated at P1 l. 8012) — exists: `LiZhongQC.knHyp` (as in §1.3)
* Formula (8.4.12) (de Branges' theorem, deB85; cited at P1 l. 8038) — exists: `Pommerenke1992.eq1_3_11`
  `LiZhongQC.knHyp.one` ((1.3.11), stated for n ≥ 2; for n = 1 the equality a₁ = f′(0) = 1 is the normalization
  field of the class S)

Not items (DESIGN §3): the remarks after Theorem 8.8 (sharpness by `(1 - z)^{-α}`, multivalent functions Hay58b,
"see also Corollary 10.19", Bae86 for `α ≥ 0.497`, the unclear range `0 < α ≤ 1/2`; P1 l. 7950–7954; quoted, not
cited); (8.4.6), `β_f(2) ≤ 1` and the JoMa92 remark (proof of Theorem 8.8); `γ > 0.17` (Pom75, Dur83),
(8.4.8) `0.23 < γ < 0.491` (CoJo91; cited only by Exercise 8.6.1, P2 l. 377) and the Carleson–Jones conjecture
`γ = 1/4` (quoted numerical results; a conjecture, recorded and not formalized); (8.4.10) (OCR `lim`; the print
has `limsup`) and (8.4.11) (CaJo91; quoted, not cited); the remark on the Koebe transform (1.3.12) (P1 l. 8010; the
transform is `Pommerenke1992.koebeTransform`); the Bieberbach history, (8.4.13)–(8.4.17) (Jen60, FeSz33, deB85),
`|b₂| ≤ 2/3` (Schi38), `|b₃| ≤ 1/2 + e^{-6}` (GaSch55b) and the Lebedev–Milin remark ("some further sharp bounds
without proof"; quoted, not cited); Exercises 8.4.1, 8.4.2.

**Conventions.** As in §8.1–§8.3. The coefficients `aₙ` are `sCoeff f n`; `aₙ = O(n^{α-1})` is
`Asymptotics.IsBigO atTop` on `ℕ`. A bounded univalent function is a conformal map of `𝔻` into `ℂ` with bounded image
(`Bornology.IsBounded (f '' unitDisc)`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc)

/-- **Formula (8.4.2)** (§8.4; P1 l. 7924–7928; cited at P1 l. 7962 and P2 l. 2600). Let `f(z) = Σ aₙ zⁿ` be analytic
in `𝔻` (8.4.1). If `n = 2, 3, …` and `rₙ = 1 - 1/n`, then
`n|aₙ| = |(2π rₙ^{n-1})^{-1} ∫₀^{2π} f'(rₙe^{it}) e^{-i(n-1)t} dt| ≤ (e/2π) ∫₀^{2π} |f'(rₙe^{it})| dt`.
Modelling: `aₙ = sCoeff f n`; the factor `e/2π` belongs to the book's `∫₀^{2π} dt`, which is written
`2π · circleAverage` in the integral mean on the right; the middle term is an interval integral (a Fourier
coefficient, not an integral mean). -/
theorem eq8_4_2 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * ‖sCoeff f n‖ =
        ‖((2 * π * (1 - 1 / (n : ℝ)) ^ (n - 1))⁻¹ : ℝ) *
          ∫ t in (0 : ℝ)..2 * π, deriv f ((1 - 1 / (n : ℝ)) * exp (t * I)) * exp (-(((n : ℂ) - 1) * t * I))‖ ∧
      ‖((2 * π * (1 - 1 / (n : ℝ)) ^ (n - 1))⁻¹ : ℝ) *
          ∫ t in (0 : ℝ)..2 * π, deriv f ((1 - 1 / (n : ℝ)) * exp (t * I)) * exp (-(((n : ℂ) - 1) * t * I))‖ ≤
        Real.exp 1 / (2 * π) * (2 * π * Real.circleAverage (fun z => ‖deriv f z‖) 0 (1 - 1 / (n : ℝ))) := by
  sorry

/-- **Theorem 8.8** (§8.4; LiPa32; P1 l. 7932–7948), first part. Let `f` map `𝔻` conformally into `ℂ` and suppose that
(8.4.3) `f(z) = O((1 - |z|)^{-α})` as `|z| → 1`. If `1/2 < α ≤ 2`, then, as `r → 1` and `n → ∞`, (8.4.4)
`∫₀^{2π} |f'(re^{it})| dt = O(1/(1 - r)^α)` and `aₙ = O(n^{α-1})`.
Modelling: the growth condition along `|z| → 1` in `𝔻`, as in `thm8_2_a`. -/
theorem thm8_8_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {α : ℝ}
    (hα1 : 1 / 2 < α) (hα2 : α ≤ 2)
    (hgr : Asymptotics.IsBigO (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) f (fun z => (1 - ‖z‖) ^ (-α))) :
    Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖) 0 r)
        (fun r : ℝ => 1 / (1 - r) ^ α) ∧
      Asymptotics.IsBigO atTop (fun n : ℕ => sCoeff f n) (fun n : ℕ => (n : ℝ) ^ (α - 1)) := by
  sorry

/-- **Theorem 8.8** (§8.4; ClPo67, Pom85; (8.4.5) cited at P2 l. 2592), second part. Let `f` map `𝔻` conformally into
`ℂ`. If `f` is bounded, i.e. if `α = 0`, then (8.4.5) `∫₀^{2π} |f'(re^{it})| dt = O(1/(1 - r)^{0.491})` and
`aₙ = O(n^{0.491-1})`. -/
theorem thm8_8_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hb : Bornology.IsBounded (f '' unitDisc)) :
    Asymptotics.IsBigO (𝓝[<] 1) (fun r : ℝ => 2 * π * Real.circleAverage (fun z => ‖deriv f z‖) 0 r)
        (fun r : ℝ => 1 / (1 - r) ^ (0.491 : ℝ)) ∧
      Asymptotics.IsBigO atTop (fun n : ℕ => sCoeff f n) (fun n : ℕ => (n : ℝ) ^ ((0.491 : ℝ) - 1)) := by
  sorry

/-- **Formula (8.4.7)** (§8.4; CaJo91, quoted; P1 l. 7978–7982; cited at P1 l. 7984, "using (7)", and P1 l. 7998,
"defined by (7)"). `γ ≡ sup_f β_f(1) = sup_f limsup_{n→∞} log(n|aₙ|)/log n`, where the suprema are taken over all
bounded univalent functions.
Modelling: both suprema are taken in `EReal` over the conformal maps of `𝔻` into `ℂ` with bounded image (both
quantities are unchanged by `f ↦ c f + d`, `c ≠ 0`); `log(n|aₙ|)` is `ENNReal.log`, which is `⊥` when `aₙ = 0` (not
the junk `Real.log 0 = 0`), divided by `log n > 0` (`n ≥ 2`; the `limsup` does not see `n = 0, 1`). -/
theorem eq8_4_7 :
    (⨆ (f : ℂ → ℂ) (_ : DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ Bornology.IsBounded (f '' unitDisc)),
        integralMeansSpectrum f 1) =
      ⨆ (f : ℂ → ℂ) (_ : DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ Bornology.IsBounded (f '' unitDisc)),
        limsup (fun n : ℕ => ENNReal.log (ENNReal.ofReal (n * ‖sCoeff f n‖)) / ((Real.log n : ℝ) : EReal)) atTop := by
  sorry

end Pommerenke1992
