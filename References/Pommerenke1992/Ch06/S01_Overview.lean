import References.Pommerenke1992.Ch06.S06_JordanCurvesAndHarmonicMeasure

/-!
# Pommerenke 1992, Ch. 6 §6.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 6 *Linear Measure*, §6.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 5380–5459. The chapter heading
is lost in the OCR; the title is that of the table of contents.

* Riesz–Privalov Theorem (named, §6.1, with (6.1.1); index "126, 134") — exists: `Pommerenke1992.thm6_8_a`
  `Pommerenke1992.thm6_8_c` (Theorem 6.8, (6.3.1) and (6.3.3): G is bounded by a rectifiable Jordan curve J, that is,
  G is the inner domain of a Jordan curve of finite length, which is finite linear measure by Proposition 6.2; then
  f' belongs to H¹ by (6.3.1), and (6.1.1) is (6.3.3))
* Plessner's Theorem (named, §6.1) — exists: `Pommerenke1992.thm6_13` (Theorem 6.13; the image of a Stolz angle is
  dense in the sphere if and only if its finite part is dense in the plane, the form of Theorem 6.13 (ii))
* Privalov Uniqueness Theorem (named, §6.1; cited by name at P2 l. 305) — exists: `Pommerenke1992.cor6_14`
  (Corollary 6.14 is the contrapositive: a meromorphic function that is not identically zero has the angular limit 0
  only on a set of outer measure zero, "positive measure" being positive outer measure)
* McMillan Twist Theorem (named, §6.1) — exists: `Pommerenke1992.thm6_18` (Theorem 6.18, the same statement)
* McMillan Sector Theorem (named, §6.1), with "the image of `Sect(f)` has σ-finite linear measure" (l. 5420) —
  exists: `Pommerenke1992.thm6_24` `Pommerenke1992.eq6_5_3` (Theorem 6.24 and (6.5.3))
* Makarov Compression Theorem (named, §6.1) — exists: `Pommerenke1992.thm6_25` (Theorem 6.25, stated with pairwise
  disjoint pieces as the word "partition" says)
* Definition (the union `C(w)` of the halflines of the limit directions of `E` at `w`, l. 5438) — `halflineCone`
* Kolmogoroff–Verčenko Theorem (named, §6.1, quoted from Sak64; used in Exercises 6.2.5, 6.5.2, 6.5.3; index
  "127, 134") — `kolmogoroff_vercenko_theorem`

Helper definitions: `IsStraightLine`, `IsClosedHalfplane` (the types of `C(w)` in the Kolmogoroff–Verčenko
theorem).

**Import order** (the exception of Ch. 2 §2.1 and Ch. 4 §4.1, leader ruling). The overview names results that are
stated in §6.3–§6.5, so this file imports the file of §6.6; no other file imports it.

Not items (DESIGN §3): the preview of the linear measure and of `≗` (l. 5382; (6.2.7), (6.2.8)); "the angular limit
`f(ζ)` exists and is finite for almost all `ζ ∈ 𝕋`" (l. 5384, a restatement of l. 1540 by Theorem 1.7 and Corollary
2.17; used at l. 6151 as "`Λ(A) = 2π`"); the remark on Fatou's theorem (l. 5394; Fatou's theorem is stated in §6.4,
`fatou_theorem`); (6.1.2), "conformal at `ζ`" (the recall of §4.3), and the informal description of twisting (a
preview of (6.4.9)); the informal description of `Sect(f)` and "`Sect(f) ≗ {ζ : f conformal at ζ}` by the twist
theorem" (l. 5412, a preview of the definition of §6.5 and of Proposition 6.22); the crowding remark, Øksendal's
conjecture and the forward reference to Theorem 10.6 (l. 5428–5430, remarks); (6.1.3) (BiCaGaJo89, a preview of
Theorem 6.30 (6.6.9)); the example `E = [0, 1] ∪ ⋃ [0, e^{i/n}]` (l. 5452–5458).

**Conventions.** As in §6.2–§6.6: `f` maps `𝔻` conformally onto `G ⊆ ℂ` (l. 5384); the linear measure is `μH[1]`;
"σ-finite linear measure" is "the union of countably many sets of finite linear measure" (l. 5420), written
`SigmaFinite ((μH[1] : Measure ℂ).restrict E)` (the equivalence is in the §6.2 bullet); the projection onto `ℝ` is
`Re`, measured by Lebesgue measure.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

/-- **Definition** (§6.1, l. 5438). For `w ∈ E`, `C(w)` is the union of all halflines `L : w + e^{iϑ}s`,
`0 ≤ s < +∞`, such that there exist `w_n ∈ E`, `w_n ≠ w`, with `arg(w_n - w) → ϑ` and `w_n → w` as `n → ∞`.
Modelling: `arg(w_n - w) → ϑ` is the convergence of the directions `(w_n - w)/|w_n - w| → e^{iϑ}` (it does not depend
on a branch of `arg`); the union is empty when `w` is not an accumulation point of `E`. Mathlib's `tangentConeAt`,
translated by `w`, differs at isolated points (`{w}` instead of `∅`), so the book's notion is defined literally
(Q6.4(a)). -/
def halflineCone (E : Set ℂ) (w : ℂ) : Set ℂ :=
  {z | ∃ ϑ s : ℝ, 0 ≤ s ∧ z = w + s * exp (ϑ * I) ∧ ∃ u : ℕ → ℂ, (∀ n, u n ∈ E ∧ u n ≠ w) ∧
    Tendsto u atTop (𝓝 w) ∧ Tendsto (fun n => (u n - w) / (‖u n - w‖ : ℂ)) atTop (𝓝 (exp (ϑ * I)))}

/-- `C ⊆ ℂ` is a (complete) straight line (helper): `C = {a + tb : t ∈ ℝ}` with `b ≠ 0`. -/
def IsStraightLine (C : Set ℂ) : Prop :=
  ∃ a b : ℂ, b ≠ 0 ∧ C = {z | ∃ t : ℝ, z = a + t * b}

/-- `C ⊆ ℂ` is a halfplane (helper): `C = {z : Re(b̄(z - a)) ≥ 0}` with `b ≠ 0`.
Modelling: closed halfplanes; `C(w)` is a closed set (a union of closed halflines over a closed set of directions),
so a halfplane equal to `C(w)` is closed. -/
def IsClosedHalfplane (C : Set ℂ) : Prop :=
  ∃ a b : ℂ, b ≠ 0 ∧ C = {z | 0 ≤ (conj b * (z - a)).re}

/-- **Kolmogoroff–Verčenko Theorem** (§6.1, named; quoted from Sak64, Chapt. IX; used in Exercises 6.2.5, 6.5.2,
6.5.3). For every set `E ⊆ ℂ` there is a canonical partition `E = E₀ ∪ E₁ ∪ E₂ ∪ E₃` with (0) `Λ(E₀) = 0`; (i) `C(w)`
is a (complete) straight line for `w ∈ E₁`; (ii) `C(w)` is a halfplane for `w ∈ E₂`; (iii) `C(w) = ℂ` for `w ∈ E₃`.
Furthermore `E₁ ∪ E₂` has σ-finite linear measure. If `B ⊆ E₁ ∪ E₂` and if `∂C(w)` is orthogonal to `ℝ` for all
`w ∈ B`, then the projection of `B` onto `ℝ` has zero measure.
Modelling: the canonical partition is the partition by the type of `C(w)`: `E₁`, `E₂`, `E₃` are the points of `E`
where `C(w)` is a line, a halfplane, all of `ℂ`, and `E₀` is the rest (the three types exclude each other), so (0)
says that the rest is null; `∂C(w)` orthogonal to `ℝ` means that the boundary of `C(w)` (the line itself for `E₁`, the
boundary line for `E₂`) is a vertical line. -/
theorem kolmogoroff_vercenko_theorem (E : Set ℂ) :
    μH[1] {w ∈ E | ¬ (IsStraightLine (halflineCone E w) ∨ IsClosedHalfplane (halflineCone E w) ∨
        halflineCone E w = univ)} = 0 ∧
      SigmaFinite ((μH[1] : Measure ℂ).restrict
        {w ∈ E | IsStraightLine (halflineCone E w) ∨ IsClosedHalfplane (halflineCone E w)}) ∧
      ∀ B ⊆ {w ∈ E | IsStraightLine (halflineCone E w) ∨ IsClosedHalfplane (halflineCone E w)},
        (∀ w ∈ B, ∃ x : ℝ, frontier (halflineCone E w) = {z | z.re = x}) →
          volume ((fun z : ℂ => z.re) '' B) = 0 := by
  sorry

end Pommerenke1992
