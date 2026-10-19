import References.Pommerenke1992.Ch06.S06_JordanCurvesAndHarmonicMeasure
import References.GarnettMarshall2005.Ch02.S03_ConjugateFunctions
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Pommerenke 1992, Ch. 7 §7.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 7 *Smirnov and Lavrentiev Domains*, §7.1;
source `full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 6592–6635.
The chapter heading is lost in the OCR (l. 6591 goes from Exercise 6.6.5 to `## 7.1 An Overview`); the title is
that of the table of contents (l. 131).

**No items; see §7.3–§7.5.** The overview states no labelled result. It considers the conformal map `f` of `𝔻`
onto the inner domain `G` of a Jordan curve `J`, where `J` is rectifiable if and only if `f' ∈ H¹` (§6.3), and
previews the notions and results of the chapter, each of which is restated in general form, with its label, later:
the Smirnov domain ((7.1.1), `f'` an outer function; §7.3, `IsSmirnovDomain`, for all `G` with `Λ(∂G) < ∞`),
Ahlfors-regularity ((7.1.2) = (7.3.12), `IsAhlforsRegular`) and Zinsmeister's Theorem 7.6, the Lavrentiev domain
((7.1.3) = (7.4.1), `IsLavrentievDomain`), "Lavrentiev domains are the Ahlfors-regular quasidisks" (Proposition 7.7),
Tukia's characterization by bilipschitz images of circles (Theorem 7.9), the characterization of Jerison and Kenig
(Theorem 7.11, stated there with "linearly connected" in place of "quasidisk"), the Coifman–Fefferman, Muckenhoupt and
`(B_q)` conditions and BMOA (§7.5), and the condition (7.1.4) `(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^q |dζ| ≤ M₃ |f'(z)|^q`
(`z ∈ 𝔻`) with its consequences a)–c).

This file holds only this module docstring (leader's structural ruling on `Ch07/S01`, 2026-09-28): one file per book
section; the chapter conventions below apply to `Ch07/S02`–`Ch07/S05`.

Not items (DESIGN §3), all previews of later items: the Smirnov condition (7.1.1) for Jordan domains (the Jordan
special case of the definition of §7.3); (7.1.2) (the definition (7.3.12)); (7.1.3) (the definition (7.4.1)); the
condition (7.1.4) (the condition (7.3.10) of Proposition 7.5, `HasArcMeanBound` of §7.3); a) (Propositions 7.5 and
7.13), b) (Theorem 7.6), c) (Theorem 7.8, Corollary 7.12 and the quoted result (7.5.7) of Gehring); the
characterizations quoted with Proposition 7.7, Theorems 7.9 and 7.11. Omitted (U−, remarks, not cited): "`f'` is
an outer function"; the significance for approximation theory (Dur70, p. 173); "the Smirnov condition has not been
completely understood from the geometrical point of view"; David's work on the Cauchy integral operator; "BMOA is the
dual space of `H¹` by a famous result of Fefferman" (the duality (7.5.18), U− in §7.5); the references Gar81, Durr84.

**Conventions (Chapter 7).**
- "`f` maps `𝔻` conformally onto `G ⊆ ℂ`" is `LiZhongQC.IsConformalOnto f unitDisc G`; "conformally into `ℂ`" is
  `DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc` (Ch. 1).
- The linear measure `Λ` of plane sets is Mathlib's `μH[1]` (the one-dimensional Hausdorff measure, which is (6.2.7)
  with no normalizing factor; the pointer belongs to Ch. 6). `Λ(∂G)` is `μH[1] (frontier G)`: a simply connected
  `G ⊆ ℂ`, `G ≠ ℂ`, whose boundary in `ℂ` has finite length is bounded, so the frontier in `ℂ` is the book's `∂G`. A
  rectifiable Jordan curve `J ⊆ ℂ` is `LehtoVirtanen1973.IsRectifiableJordanCurve J`, as in Ch. 6 (a Jordan curve
  of finite linear measure; its length is `Λ(J)`, Prop. 6.2).
- Integrals over `𝕋` are written through the parameter, `ζ = e^{it}`, `|dζ| = dt`. An arc `I ⊆ 𝕋` is the parameter
  interval `Icc t₁ t₂` with `t₁ < t₂ ≤ t₁ + 2π` (the arc `arcT t₁ t₂` of Ch. 4), `Λ(I) = t₂ - t₁`; the arc `I(z)` of
  (7.3.8) (`arcI z`, Ch. 5) is the parameter interval from `arg z - π(1 - |z|)` to `arg z + π(1 - |z|)`, of length
  `Λ(I(z)) = 2π(1 - |z|)` (`I(0) = 𝕋`). The means `(1/Λ(I)) ∫_I … |dζ|` are Mathlib's set averages over the parameter
  interval: `⨍⁻` (lower integrals, values in `ℝ≥0∞`) for non-negative integrands such as `|f'|^q` and weights, and
  `⨍` for real or complex integrands whose integrability is part of the hypotheses. `ℝ≥0∞`-powers give the book's
  conventions `0^{-a} = ∞`, `∞^{-a} = 0` (`a > 0`).
- The boundary values `f'(ζ)` are the angular limits of `f'` (§1.2 `HasAngularLimit`), carried by a witness `φ` with
  `IsAngularBoundaryFun (deriv f) φ` (§7.3): `φ(e^{it})` is the angular limit for almost every `t`, so `φ` is
  determined almost everywhere. Every integral and every condition on `φ` is insensitive to null sets, so the
  statements "for some such `φ`" and "for every such `φ`" agree once one exists; conclusions assert the existence.
- `log f'` is a holomorphic branch `L` with `exp ∘ L = f'` on `𝔻` (`f' ≠ 0` on the simply connected `𝔻`); branches
  differ by constants in `2πiℤ`.
- The Poisson kernel `p(z, ζ) = (1 - |z|²)/(2π|ζ - z|²)` is Mathlib's `poissonKernel 0 z ζ / (2π)` (Ch. 3, (3.1.4));
  `(ζ + z)/(ζ - z)` is Mathlib's `herglotzRieszKernel 0 z ζ`.
- Measures on `𝕋` are finite measures on `ℂ` with `μ(ℂ ∖ 𝕋) = 0`; "singular" is mutual singularity with the arc
  length `GarnettMarshall2005.arcMeasure`.
- `Hᵖ` is `GarnettMarshall2005.MemHardy (ENNReal.ofReal p)` (GM App. A; `sup_r ∫ |g(re^{it})|^p dt < ∞` without the
  factor `1/2π`, which for `p = 1` is (6.3.5)); every use in Ch. 7 is membership only.
- Constants: `K₁, K₂, …` are absolute (`∃ K, ∀ f`); `M₁, M₂, …` "may depend on `f` and other parameters"
  (`∀ f, ∃ M`, l. 6828). The standing assumption of §7.3 (`f` maps `𝔻` conformally onto `G` with `Λ(∂G) < ∞`,
  l. 6770) is explicit in every §7.3 statement.
-/

namespace Pommerenke1992

end Pommerenke1992
