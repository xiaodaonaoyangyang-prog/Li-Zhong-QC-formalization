import References.Pommerenke1992.Ch10.S03_LowerBoundsForCompression

/-!
# Pommerenke 1992, Ch. 10 §10.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 10 *Hausdorff Measure*, §10.1; source `full.md`
of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 1665–1736. The chapter
heading is lost in the OCR (P2 l. 1663 is Exercise 9.5.6 and l. 1665 is the heading of §10.1); the title is that of
the table of contents (P1 l. 150–156).

* Formula (10.1.3) ("`Λ′_α(E) ≤ K (cap E)^α` (Theorem 10.3)", l. 1681–1685; cited "(10.1.3)" at P2 l. 1105, §9.3) —
  exists: `Pommerenke1992.thm10_3_pow` (the "in particular" after Theorem 10.3, P2 l. 1833–1837: the same inequality
  for Borel sets E, the sets of (10.1.1), with the constant M₂ of §10.2 in place of K)
* Makarov Dimension Theorem (named, with (10.1.5), l. 1697–1703; index "Makarov dimension theorem 222, 229, 231,
  235") — exists: `Pommerenke1992.thm10_9_a` `Pommerenke1992.thm10_9_b` `Pommerenke1992.eq10_3_13` ("dim A > 0
  implies dim f(A) > (dim A)/2" in three cases: Theorem 10.9 (a) for 0 < dim A ≤ 11/12; Theorem 10.9 (b) for
  11/12 < dim A < 1, whose bound α/(1 + √(12(1 − α))) exceeds α/2 there since 12(1 − α) < 1; and (10.3.13), which is
  also (10.1.5), for dim A = 1; all stated, as Theorem 10.9, for Borel sets A on which the angular limits exist, the
  standing assumption of §10.3: the overview's "A ⊂ 𝕋" omits "Borel" (Q10.6), and the proof, through
  Proposition 10.10, Theorem 9.24 and Theorem 10.3, needs Borel sets; the literal statement for arbitrary A ⊂ 𝕋 is
  not asserted anywhere)
* Anderson–Pitt Theorem (named, (10.1.7), l. 1715–1719; index "Anderson-Pitt theorem 223, 237") —
  `anderson_pitt_theorem`

**Import order** (the exception of Chapter 6 §6.1, leader ruling QD7). The overview names results that are stated in
§10.2 and §10.3, so this file imports the file of §10.3; no other file imports it.

Not items (DESIGN §3): (10.1.1), the `α`-dimensional Hausdorff measure of a Borel set, and "In particular `Λ₁` is the
linear measure `Λ` discussed in Section 6.2" (l. 1667–1673; a preview of (10.2.1) with `φ(t) = t^α`); (10.1.2), `Λ′_α`,
"behaves more like a capacity than a measure" (l. 1675–1681; a preview of (10.2.5)); (10.1.4)
`dim E = inf {α : Λ_α(E) = 0} = inf {α : Λ′_α(E) = 0}` (l. 1687–1691; a preview of (10.2.3) and (10.2.7));
"fractals", "Theorem 10.5 (due to Hungerford in its final form)", the Hausdorff measure `Λ_φ` "with respect to any
continuous increasing function `φ` with `φ(0) = 0`", Fal85, Rog70 (l. 1693–1695; terminology, pointers and a preview of
(10.2.1); `φ(0) = 0` enters `IsHausdorffGauge`); Carleson's earlier result `Λ(A) > 0 ⟹ dim f(A) > 1/2` and the pointers
to Theorems 10.6, 8.10, 10.8, Sections 8.3, 6.5 and Mak89d (l. 1705; history, U−); (10.1.6), Hamilton's analogue of
Löwner's lemma (for `α`-capacity), `f(𝔻) ⊂ 𝔻`, `f(A) ⊂ 𝕋 ⟹ dim f(A) ≥ dim A`, with the pointer to Theorem 10.11
(l. 1707–1713; a preview of (10.3.24), itself U−; `α`-capacity is never defined in the book); "Makarov's Theorem 10.14
gives the best possible bound for the size of the set where the angular derivative exists" (l. 1721; a pointer to
§10.4); `N(ε, E)`, (10.1.8) `mdim E = inf {α : N(ε, E) = O(ε^{−α})}`, "so that `dim E ≤ mdim E`", the names "box
dimension", "upper entropy dimension" and KoTi61, Haw74, Fal90 (l. 1723–1729; previews of `N(ε, E)`, of (10.5.1) and of
Proposition 10.16; the `O`-form (10.1.8) equals the `limsup` form (10.5.1) for bounded `E`, and it is never cited, U−);
"If `f` is a conformal map of `𝔻` onto a quasidisk `G` then (Corollary 10.18) `mdim ∂G = inf α` where
`∫₀^{2π} |f'(re^{it})|^α dt = O((1 − r)^{−α+1})`" (l. 1731–1735; a preview of Corollary 10.18 through Theorem 5.9,
every bounded quasidisk being a John domain).

**Conventions.** As in §10.2–§10.5 (the chapter conventions are in `Ch10/S02_HausdorffMeasures`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc)

/-- **Anderson–Pitt Theorem** (§10.1, named; (10.1.7); P2 l. 1715–1719; index "Anderson-Pitt theorem 223, 237"). If
`f` maps `𝔻` conformally into `ℂ`, then (7) `dim {ζ ∈ 𝕋 : f'(ζ) exists finitely} = 1`.
Modelling: "`f'(ζ)` exists finitely" is the existence of a finite angular derivative (§4.3: `HasAngularDerivative f ζ a`
with `a ∈ ℂ`, the value `0` allowed; the crop of (10.1.7) was checked). The item is new: Theorem 10.13 gives a set of
positive `Λ_ψ`-measure, which has dimension `1` by Proposition 10.2 (`ψ(t) ≤ t^α` near `0` for `α < 1`), but the
statements differ. -/
theorem anderson_pitt_theorem {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    dimH {ζ ∈ sphere (0 : ℂ) 1 | ∃ a : ℂ, HasAngularDerivative f ζ a} = 1 := by
  sorry

end Pommerenke1992
