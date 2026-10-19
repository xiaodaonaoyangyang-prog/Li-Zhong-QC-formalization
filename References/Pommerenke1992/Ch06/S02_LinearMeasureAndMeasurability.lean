import References.Pommerenke1992.Ch05.S06_AnalyticFamiliesOfInjections
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Pommerenke 1992, Ch. 6 §6.2 Linear Measure and Measurability

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 6 *Linear Measure*, §6.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 5460–5739.

* Definition (outer measure, §6.2.1, with (6.2.1) monotonicity and (6.2.2) subadditivity; cited "by (6.2.1) and
  (6.2.2)" at l. 5808; the OCR splits the tags) — exists: `MeasureTheory.OuterMeasure` `MeasureTheory.measure_mono`
  `MeasureTheory.measure_iUnion_le` (the same axioms: the empty set has measure zero, the outer measure is monotone
  and countably subadditive)
* Definition (metric outer measure, (6.2.3); used at P2 l. 1755, 1819) — exists:
  `MeasureTheory.OuterMeasure.IsMetric` (additivity for two sets at positive distance, which is Mathlib's metric
  separation of the two sets)
* Definition (`μ`-measurable set, (6.2.4)) — exists: `MeasureTheory.OuterMeasure.IsCaratheodory` (literally (6.2.4):
  every test set X splits additively)
* Definition (Borel sets, §6.2.1) — exists: `borel` `MeasurableSet` (the plane carries its Borel sigma-algebra; on the
  sphere the Borel sets are the sets measurable for the Borel sigma-algebra of the extended plane, as in Ch. 4)
* Definition (`ε`-cover, (6.2.6); outer linear measure `Λ`, (6.2.7); cited "(6.2.7)" at P2 l. 1751) — exists:
  `MeasureTheory.Measure.hausdorffMeasure` `MeasureTheory.Measure.hausdorffMeasure_apply` (the one-dimensional
  Hausdorff measure of the plane: the supremum over r > 0 of the infimum, over countable covers by sets of diameter at
  most r, of the sum of the diameters; this is (6.2.6)–(6.2.7) with no normalization factor, and its value on every
  set is the outer measure)
* Proposition 6.1 (cited at l. 5628 and P2 l. 1753) — exists: `MeasureTheory.OuterMeasure.mkMetric'_isMetric`
  `MeasureTheory.Measure.mkMetric_toOuterMeasure` `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`
  `MeasureTheory.OuterMeasure.caratheodory` `MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory` (the outer
  measure of the one-dimensional Hausdorff measure is the metric outer measure built from the diameters, hence metric;
  its Carathéodory-measurable sets form a sigma-algebra containing the Borel sets, on which it is countably additive)
* Definition (linearly measurable, l. 5514) — `IsLinearlyMeasurable`
* Unlabelled (§6.2, l. 5534: on `ℝ` and on `𝕋` the outer linear measure is the outer Lebesgue measure; used as the
  identification at l. 5742, in Proposition 6.4, P2 l. 415, 1885) — `linearMeasure_eq_lebesgue`
* Definition (sigma-finite linear measure, "i.e. is the union of countably many sets of finite linear measure", §6.1
  l. 5420 and l. 5538; used in the Kolmogoroff–Verčenko theorem, (6.5.3), l. 6299, 6480 and P2 l. 2536) — exists:
  `MeasureTheory.SigmaFinite` `MeasureTheory.Measure.restrict` (E has sigma-finite linear measure when the restriction
  of the one-dimensional Hausdorff measure to E is sigma-finite, the form of Lehto–Virtanen and Garnett–Marshall; this
  is equivalent to the book's wording for every E ⊆ ℂ: if the restriction is sigma-finite, take measurable sets T_n
  covering ℂ with finite measure on E and put A_n = T_n ∩ E; conversely, the measurable hulls of the A_n together with
  the complement of their union, of restricted measure 0, form a cover of finite restricted measure)
* Definition (`E ≗ E'`, (6.2.8); used at l. 5412, 6343, 6383, 6469, (6.6.7), (6.6.8)) — exists: `Filter.EventuallyEq`
  `MeasureTheory.ae` `MeasureTheory.ae_eq_set` (E and E' are equal almost everywhere for the linear measure, which is
  the form "both differences are null" of (6.2.8); the statements write the two differences)
* Definition (contraction, (6.2.9); used at P2 l. 820, 1029) and formula (6.2.10) (cited twice in the proof of
  Proposition 6.2) — exists: `LipschitzOnWith` `LipschitzOnWith.hausdorffMeasure_image_le` (a contraction of E is a
  map that is Lipschitz on E with constant 1; with d = 1 the image estimate is (6.2.10))
* Proposition 6.2 (cited at l. 5742) — `prop6_2`
* Proposition 6.3 (cited at l. 5628, 5824) — `prop6_3_i`, `prop6_3_ii`
* Definition (`F_σ`-set, l. 5616; used in (6.5.3), l. 6204, P2 l. 1312) — `IsFSigma`
* Proposition 6.4 (HeSt69; cited at l. 6122, 6380) with the definition of a point of density ((6.2.15)) —
  `IsDensityPoint`, `prop6_4`
* Proposition 6.5 with the notation `f⁻¹(B)` of (6.2.16) — `radialPreimage`, `prop6_5`
* Proposition 6.6 (cited at l. 5716) — `prop6_6`
* Definition (Souslin set or analytic set, (6.2.19); used in Theorem 9.12, P2 l. 1075) — exists:
  `MeasureTheory.AnalyticSet` (the empty set or a continuous image of the Baire space of sequences of natural numbers;
  in the Polish spaces of the plane and of the sphere this is the class of the Souslin sets (6.2.19) formed with
  compact sets, a classical theorem of descriptive set theory)
* Definition (the notation `f(A)` of (6.2.20), the set of radial limits on `A`) — `radialImage`
* Proposition 6.7 (cited at l. 5824) — `prop6_7_a`, `prop6_7_b`

Not items (DESIGN §3): "`≤` always holds" and "every set of outer measure `0` is `μ`-measurable" (l. 5486,
immediate); the basic fact quoted from Fal85 (l. 5490–5496: the `μ`-measurable sets form a sigma-algebra, (6.2.5), a
metric outer measure makes the Borel sets measurable; quoted, used in the proof of Proposition 6.1 and "in the same
way" for Proposition 10.1; Mathlib's `caratheodory` construction); "countable sets have linear measure `0`", "null sets
are linearly measurable", "open sets have infinite linear measure", "linear measure is not sigma-finite" (l.
5536–5538, not cited); "`≗` is an equivalence relation" and `Λ(aE + b) = |a|Λ(E)` (l. 5546–5552, immediate); the
projection estimate `Λ(P) ≤ Λ(E)` (l. 5566, immediate from (6.2.10)); "the notation agrees with §1.1" and the
irregular sets of Bes38 (l. 5574); "`Λ` is a regular outer measure", `G_δ`-sets and (6.2.14) (l. 5610–5616, a remark,
immediate from Proposition 6.3, not cited by number); (6.2.17) (a step of the proof of Proposition 6.5); "Borel sets
and continuous images of Borel sets are Souslin sets, Souslin sets are linearly measurable" (l. 5690, quoted from
Kur52, Rog70, not cited); "`f(A)` is a Souslin set for Borel or Souslin `A`" (McM66) and the converse construction
of BerNi92 (l. 5692–5698, quoted, not cited); Exercises 6.2.1–6.2.5.

**Conventions** (Chapter 6).
- `Λ` of a plane set is Mathlib's one-dimensional Hausdorff measure `μH[1]`, an outer measure on all sets (leader
  ruling QC1). For sets on `𝕋` the book's `Λ` is arc length (l. 5534); the statements measure subsets of `𝕋` by the
  arc length `circleMeasure` of Ch. 4 (the outer Lebesgue measure of the parameter set in `[0, 2π)`), and the two are
  identified by `linearMeasure_eq_lebesgue`. "For almost all `ζ ∈ 𝕋`" is `∀ᵐ t : ℝ` for `ζ = e^{it}` (a set of outer
  measure `0`, as in `thm1_7`); `E ≗ E'` is written as the two null differences.
- "Measurable" means linearly measurable, `IsLinearlyMeasurable` (the index: "measurable 128 see linearly measurable";
  leader ruling QC2); for subsets of `𝕋` this is Lebesgue measurability. "Borel" is written only where the book says
  so (Proposition 6.5; `MeasurableSet`).
- Functions "continuous in `𝔻`" of Propositions 6.5–6.7 take values in `Ĉ` (`f : ℂ → Ĉ`, `ContinuousOn f 𝔻`); the
  radial limit `f(ζ)` is `HasRadialLimit` of Ch. 2. The book's `f(A)` and `f⁻¹(B)` are the sets of radial limits
  `radialImage f A` and `radialPreimage f B`; the linear measure of a set of `Ĉ` is that of its finite part
  (`References.finitePart`; the point `∞` has linear measure `0`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc)
open References (finitePart)

/-- **Definition** (§6.2, l. 5514). A set `E ⊆ ℂ` is linearly measurable: it is `Λ`-measurable in the sense of (6.2.4),
`Λ(X) = Λ(X ∩ E) + Λ(X ∖ E)` for all `X ⊆ ℂ`.
Modelling: a thin wrapper around Mathlib's Carathéodory measurability for the outer measure of `μH[1]` (leader ruling
QC2). It is not Borel measurability: Proposition 6.7(b) builds a null (hence linearly measurable) set `A` whose image
`f(A)` is not linearly measurable; if "measurable" meant Borel, `f(A)` would be a Souslin set for Borel `A` (McM66,
l. 5692), hence linearly measurable (l. 5690), and Proposition 6.7(b) would be false. -/
def IsLinearlyMeasurable (E : Set ℂ) : Prop :=
  (μH[1] : Measure ℂ).toOuterMeasure.IsCaratheodory E

/-- **Unlabelled claim** (§6.2, l. 5534; used as the identification of `Λ` with arc length at l. 5742, in Proposition
6.4 ("`Λ` is the outer measure" on `𝕋`), P2 l. 415, 1885). For sets on `ℝ` the outer linear measure is the outer
Lebesgue measure, and the same is true for sets on the unit circle `𝕋`.
Modelling: `ℝ` is the real axis of `ℂ`; on `𝕋` the outer Lebesgue measure is the arc length `circleMeasure`; both
identities hold for all sets (outer measures). The half for `ℝ` follows from Mathlib (`Isometry.hausdorffMeasure_image`
for `Complex.isometry_ofReal`, then `MeasureTheory.hausdorffMeasure_real`); only the half for `𝕋` is new. -/
theorem linearMeasure_eq_lebesgue :
    (∀ E : Set ℝ, μH[1] ((fun x : ℝ => (x : ℂ)) '' E) = volume E) ∧
      ∀ A ⊆ sphere (0 : ℂ) 1, μH[1] A = circleMeasure A := by
  sorry

/-- **Proposition 6.2** (§6.2; cited at l. 5742). Let `J` be a Jordan arc. Then `Λ(J)` is equal to the length of `J`.
If `Λ(J) < ∞` and if `J : ψ(s)`, `0 ≤ s ≤ Λ(J)`, is the arc length parametrization of `J`, then (6.2.11)
`Λ(ψ(A)) = Λ(A)` for measurable `A ⊆ [0, Λ(J)]`.
Modelling: `J = φ([a, b])` with `φ` continuous and injective on `[a, b]`, `a < b`; its length (1.1.7) is
`eVariationOn φ [a, b]`. The arc length parametrization is a continuous injective `ψ` of `[0, L]` onto `J`,
`L = Λ(J)`, whose length on `[0, s]` is `s`. `A ⊆ [0, L] ⊆ ℝ ⊆ ℂ` is a plane set: "measurable" is linear
measurability and `Λ(A)` is its linear measure. -/
theorem prop6_2 {φ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hφc : ContinuousOn φ (Icc a b))
    (hφi : InjOn φ (Icc a b)) :
    μH[1] (φ '' Icc a b) = eVariationOn φ (Icc a b) ∧
      ∀ (L : ℝ) (ψ : ℝ → ℂ), μH[1] (φ '' Icc a b) = ENNReal.ofReal L → ContinuousOn ψ (Icc 0 L) →
        InjOn ψ (Icc 0 L) → ψ '' Icc 0 L = φ '' Icc a b →
        (∀ s ∈ Icc 0 L, eVariationOn ψ (Icc 0 s) = ENNReal.ofReal s) →
        ∀ A ⊆ Icc 0 L, IsLinearlyMeasurable ((fun x : ℝ => (x : ℂ)) '' A) →
          μH[1] (ψ '' A) = μH[1] ((fun x : ℝ => (x : ℂ)) '' A) := by
  sorry

/-- **Proposition 6.3** (§6.2; Bes38, Fal85; cited at l. 5628), part (i). If `E` is any set in `ℂ`, then there are
open sets `H_n ⊇ E` such that (6.2.12) `Λ(E) = Λ(⋂_{n ≥ 1} H_n)`. -/
theorem prop6_3_i (E : Set ℂ) :
    ∃ H : ℕ → Set ℂ, (∀ n, IsOpen (H n) ∧ E ⊆ H n) ∧ μH[1] E = μH[1] (⋂ n, H n) := by
  sorry

/-- **Proposition 6.3** (§6.2; cited at l. 5824), part (ii). If `E ⊆ ℂ` is linearly measurable and `Λ(E) < ∞`, then
there are closed sets `A_n ⊆ E` such that (6.2.13) `Λ(E) = Λ(⋃_{n ≥ 1} A_n)`. -/
theorem prop6_3_ii {E : Set ℂ} (hE : IsLinearlyMeasurable E) (hfin : μH[1] E < ⊤) :
    ∃ A : ℕ → Set ℂ, (∀ n, IsClosed (A n) ∧ A n ⊆ E) ∧ μH[1] E = μH[1] (⋃ n, A n) := by
  sorry

/-- **Definition** (§6.2, l. 5616; used in (6.5.3), l. 6204, and P2 l. 1312). An `F_σ`-set: the union of countably
many closed sets.
Modelling: a countable family is indexed by `ℕ` (repetitions allowed; the empty set is the union of empty sets). -/
def IsFSigma (E : Set ℂ) : Prop :=
  ∃ A : ℕ → Set ℂ, (∀ n, IsClosed (A n)) ∧ E = ⋃ n, A n

/-- **Definition (6.2.15)** (§6.2, l. 5626). `ζ ∈ 𝕋` is a point of density of the set `A ⊆ 𝕋`:
`Λ(A ∩ I)/Λ(I) → 1` as `Λ(I) → 0`, where `I` runs through the arcs of `𝕋` with `ζ ∈ I`.
Modelling: `Λ` is the outer measure (l. 5626), the arc length `circleMeasure`; the arcs are `arcT t₁ t₂`,
`t₁ < t₂ ≤ t₁ + 2π`, with `Λ(arcT t₁ t₂) = t₂ - t₁`; the limit is written with `ε` and `δ` (the quotient is finite,
the arcs having positive length). -/
def IsDensityPoint (A : Set ℂ) (ζ : ℂ) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π → t₂ - t₁ < δ →
    ζ ∈ arcT t₁ t₂ → |(circleMeasure (A ∩ arcT t₁ t₂)).toReal / (t₂ - t₁) - 1| < ε

/-- **Proposition 6.4** (§6.2; HeSt69; cited at l. 6122, 6380). Let `A` be any set on `𝕋` with `Λ(A) > 0`. Then there
exists `ζ ∈ A` such that (6.2.15) holds, that is, `ζ` is a point of density of `A`.
Modelling: `Λ` is the outer measure (l. 5626: "Here `Λ` is the outer measure"), so `A` need not be measurable. -/
theorem prop6_4 {A : Set ℂ} (hAT : A ⊆ sphere (0 : ℂ) 1) (hA : 0 < circleMeasure A) :
    ∃ ζ ∈ A, IsDensityPoint A ζ := by
  sorry

/-- **Definition (6.2.16)** (§6.2). For `f` in `𝔻` with values in `Ĉ` and `B ⊆ Ĉ`,
`f⁻¹(B) = {ζ ∈ 𝕋 : f(ζ) exists, f(ζ) ∈ B}`, where `f(ζ)` is the radial limit. -/
def radialPreimage (f : ℂ → ExtPlane) (B : Set ExtPlane) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | ∃ w ∈ B, HasRadialLimit f ζ w}

/-- **Proposition 6.5** (§6.2). Let `f` be a continuous map of `𝔻` into `Ĉ`. Then the points `ζ ∈ 𝕋` where the radial
limit `f(ζ)` exists form a Borel set, and if `B ⊆ Ĉ` is a Borel set, then (6.2.16) `f⁻¹(B)` is also a Borel set.
Modelling: the set where the radial limit exists is `f⁻¹(Ĉ)`; Borel sets of `Ĉ` are the sets measurable for
`borel ExtPlane` (as in Ch. 4); the OCR's "from a Borel set" is read "form a Borel set". -/
theorem prop6_5 {f : ℂ → ExtPlane} (hf : ContinuousOn f unitDisc) :
    MeasurableSet (radialPreimage f univ) ∧
      ∀ B : Set ExtPlane, MeasurableSet[borel ExtPlane] B → MeasurableSet (radialPreimage f B) := by
  sorry

/-- **Definition (6.2.20)** (§6.2; used in every later statement on `f(E)`). For `f` in `𝔻` with values in `Ĉ` and
`A ⊆ 𝕋`, `f(A) = {f(ζ) : ζ ∈ A, f(ζ) exists}`, the set of radial limits.
Modelling: every statement takes `A ⊆ 𝕋`. -/
def radialImage (f : ℂ → ExtPlane) (A : Set ℂ) : Set ExtPlane :=
  {w | ∃ ζ ∈ A, HasRadialLimit f ζ w}

/-- **Proposition 6.6** (§6.2; cited at l. 5716). Let `f` be continuous in `𝔻` and let the radial limit `f(ζ)` exist
for all `ζ` in the measurable set `A ⊆ 𝕋`. Then there are closed sets `A_n ⊆ A` such that `f(A_n)` is closed for
`n = 1, 2, …` and (6.2.18) `A = E ∪ ⋃_{n ≥ 1} A_n`, `Λ(E) = 0`.
Modelling: `f` takes values in `Ĉ` and `f(A_n)` is closed in `Ĉ` (Q6.11); (6.2.18) is `Λ(A ∖ ⋃ A_n) = 0`, `E` being
any set with `A ∖ ⋃ A_n ⊆ E ⊆ A`. -/
theorem prop6_6 {f : ℂ → ExtPlane} (hf : ContinuousOn f unitDisc) {A : Set ℂ} (hAT : A ⊆ sphere (0 : ℂ) 1)
    (hA : IsLinearlyMeasurable A) (hlim : ∀ ζ ∈ A, ∃ w, HasRadialLimit f ζ w) :
    ∃ An : ℕ → Set ℂ, (∀ n, IsClosed (An n) ∧ An n ⊆ A ∧ IsClosed (radialImage f (An n))) ∧
      circleMeasure (A \ ⋃ n, An n) = 0 := by
  sorry

/-- **Proposition 6.7** (§6.2; cited at l. 5824), first part. Let `f` be continuous in `𝔻` and let `B ⊆ 𝕋` be
measurable. If the radial limit `f(ζ)` exists for `ζ ∈ B` and if (6.2.21) `E ⊆ B, Λ(E) = 0 ⇒ Λ(f(E)) = 0`, then
(6.2.22) `A ⊆ B, A measurable ⇒ f(A) linearly measurable`.
Modelling: `f` takes values in `Ĉ`; `Λ(f(E))` and the linear measurability of `f(A)` refer to the finite parts (Q6.11);
the OCR prints (6.2.22) inline as "(22) …". -/
theorem prop6_7_a {f : ℂ → ExtPlane} (hf : ContinuousOn f unitDisc) {B : Set ℂ} (hBT : B ⊆ sphere (0 : ℂ) 1)
    (hB : IsLinearlyMeasurable B) (hlim : ∀ ζ ∈ B, ∃ w, HasRadialLimit f ζ w)
    (h21 : ∀ E ⊆ B, circleMeasure E = 0 → μH[1] (finitePart (radialImage f E)) = 0) :
    ∀ A ⊆ B, IsLinearlyMeasurable A → IsLinearlyMeasurable (finitePart (radialImage f A)) := by
  sorry

/-- **Proposition 6.7** (§6.2), second part. If `f(B) ⊆ 𝕋` and if (6.2.21) is false, then (6.2.22) is false.
Modelling: as in `prop6_7_a`; "measurable" is linear measurability, not Borel (see `IsLinearlyMeasurable`): in the
proof, `A` is a (null, hence measurable) subset of a null set `E ⊆ B` with `Λ(f(E)) > 0`, and `f(A)` is a
non-measurable subset of `f(E) ⊆ 𝕋`. -/
theorem prop6_7_b {f : ℂ → ExtPlane} (hf : ContinuousOn f unitDisc) {B : Set ℂ} (hBT : B ⊆ sphere (0 : ℂ) 1)
    (hB : IsLinearlyMeasurable B) (hlim : ∀ ζ ∈ B, ∃ w, HasRadialLimit f ζ w)
    (hfB : radialImage f B ⊆ toExt (sphere (0 : ℂ) 1))
    (hn21 : ¬ ∀ E ⊆ B, circleMeasure E = 0 → μH[1] (finitePart (radialImage f E)) = 0) :
    ¬ ∀ A ⊆ B, IsLinearlyMeasurable A → IsLinearlyMeasurable (finitePart (radialImage f A)) := by
  sorry

end Pommerenke1992
