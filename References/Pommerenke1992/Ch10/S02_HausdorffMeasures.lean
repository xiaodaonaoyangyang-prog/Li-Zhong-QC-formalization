import References.Pommerenke1992.Ch09.S05_ApplicationsToConformalMapping
import References.GarnettMarshall2005.Ch03.S04_EquilibriumDistribution
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Pommerenke 1992, Ch. 10 §10.2 Hausdorff Measures

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 10 *Hausdorff Measure*, §10.2; source `full.md`
of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 1737–1995. The chapter
(P2 l. 1665–2688, book pp. 222–244) lies inside P2 with no seam; its heading is lost in the OCR, and the title is that
of the table of contents. This is the first file of the chapter; the overview §10.1 (`Ch10/S01_Overview`) comes last
in the import order.

* Standing assumption (§10.2, P2 l. 1739: `φ` positive, continuous and increasing in `(0, +∞)` with `φ(t) → 0` as
  `t → 0`; with `φ(0) = 0` of §10.1, l. 1695; helper) — `IsHausdorffGauge`
* Definition (the `ε`-covers and the Hausdorff measure `Λ_φ` with respect to `φ`, (10.2.1), l. 1739–1751, 1763; cited
  "(1)" at l. 1767, 1805, 1959; index "ε-cover 223", "`Λ_φ(E)` 223–226, 229, 236, 237, 239") —
  `hausdorffMeasureGauge`, `gaugeFn`
* Definition (`Λ_α ≡ Λ_{t^α}`, the `α`-dimensional Hausdorff measure, `α > 0`, l. 1751, 1763; used in Theorem 10.5,
  (10.3.3) and Exercises 10.2.1, 10.3.4, 10.3.6) — exists: `MeasureTheory.Measure.hausdorffMeasure` (μH[α]: covers
  by arbitrary sets, the diameter to the power α, no normalizing factor, as in the book; gaugeFn of t ↦ t^α is
  r ↦ r^α for α > 0, so μH[α] is hausdorffMeasureGauge of t ↦ t^α on the nose; the LV Ch. III pointer)
* Proposition 10.1 ((10.2.2), l. 1753–1761) — exists: `MeasureTheory.OuterMeasure.mkMetric'_isMetric`
  `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` `MeasureTheory.OuterMeasure.caratheodory`
  `MeasureTheory.measure_iUnion` `MeasureTheory.Measure.mkMetric_toOuterMeasure` (for hausdorffMeasureGauge φ, the
  measure of Measure.mkMetric of gaugeFn φ, whose value on every set is that of the outer measure
  OuterMeasure.mkMetric of gaugeFn φ: that outer measure is metric, its Carathéodory-measurable sets form a σ-algebra
  containing the Borel sets, and (10.2.2) is countable additivity on disjoint Borel sets; the Part C pointers of
  Proposition 6.1 with a general gauge)
* Proposition 10.2, first assertion (l. 1765; cited at l. 1787) — exists: `MeasureTheory.Measure.mkMetric_mono`
  `MeasureTheory.Measure.le_iff'` (φ ≤ ψ gives gaugeFn φ ≤ gaugeFn ψ, hence Λ_φ ≤ Λ_ψ as measures and on every
  set; the Mathlib hypothesis, an inequality of the gauges near 0 only, is weaker)
* Proposition 10.2, second assertion (l. 1765; cited at l. 1787, 2331 and 2401) — `prop10_2_b`
* Definition (the Hausdorff dimension `dim E = inf {α : Λ_α(E) = 0}`, (10.2.3), l. 1781–1785; cited "(3)" at
  l. 1813; index "Hausdorff dimension 153, 222, 224, 225, 228, 229, 231, 235, 238–240, 249", "dim E 222") —
  exists: `dimH` (Mathlib's supremum form over the exponents d with μH[d] E = ∞; the same number by (10.2.4), which is
  Mathlib's hausdorffMeasure_of_lt_dimH and hausdorffMeasure_of_dimH_lt; the exponents range over α ≥ 0; the LV
  Ch. III and GM App. D rulings)
* Definition (`Λ′_φ`, (10.2.5), and `Λ′_α`, l. 1799–1811; cited "(5)" at l. 1875; index "`Λ′_α(E)` 134, 222, 225,
  232", "`Λ′_φ(E)` 225, 234") — `hausdorffContent`
* Formula (10.2.6) (§10.2, P2 l. 1807–1809, U+: "Hence … and (6)"; cited "(6)" at l. 1813) — `eq10_2_6`
* Theorem 10.3 ((10.2.8), (10.2.9); cited at l. 1681, 2182 and 2277) — `thm10_3`
* Unlabelled (§10.2, P2 l. 1833–1837: "In particular we see that `Λ′_α(E) ≤ M₂ (cap E)^α`", the display (10.1.3) of
  the overview; cited "(10.1.3)" at P2 l. 1105 and used at l. 2182) — `thm10_3_pow`
* Unlabelled (§10.2, P2 l. 1839: "so that cap `E = 0` implies dim `E = 0`"; used at l. 1998, 2461 and P2 l. 1105) —
  `thm10_3_cap_zero`
* Proposition 10.4 (Fro35; (10.2.12), l. 1877–1883; (10.2.12) is used by Exercise 10.2.5) — `prop10_4`
* Theorem 10.5 (Hun88; (10.2.13)–(10.2.15), l. 1885–1899; cited at l. 1693, 1957, 1965) — `thm10_5`

Not items (DESIGN §3): "it is clear that only the behaviour of `φ(t)` near `t = 0` matters" (l. 1751; U−, Mathlib's
`MeasureTheory.Measure.mkMetric_mono` in both directions; it justifies the germ modelling of (10.3.1) and (10.4.1));
"`Λ₁ = Λ`" by (6.2.7) and "the 1-dimensional measure is thus the linear measure" (l. 1751, 1763; U−: `Λ` is `μH[1]`,
Part C); the remark that different Hausdorff measures make a very fine distinction and that `Λ_φ` is not σ-finite
(l. 1779); (10.2.4) and "`0 ≤ Λ_{dim E}(E) ≤ ∞`" (l. 1787–1793; U−, not cited by number; Mathlib's
`hausdorffMeasure_of_lt_dimH`, `hausdorffMeasure_of_dimH_lt`); "`0 ≤ dim E ≤ 2` for `E ⊂ ℂ`, `dim E ≤ 1` for
`E ⊂ 𝕋`, `Λ₁(E) > 0` implies `dim E = 1` but not vice versa" (l. 1795; U−, immediate); the snowflake curve has
dimension `log 4/log 3` (l. 1797; an example, Fal85); "hence `0 ≤ Λ′_φ(E) ≤ Λ_φ(E) ≤ ∞`" (l. 1805; U−, immediate);
"`Λ′_φ` is finite for bounded sets" and (10.2.7) `dim E = inf {α : Λ′_α(E) = 0}` (l. 1813–1817; U−: immediate from
(10.2.6) and (10.2.3), not cited by number, used implicitly at l. 2225); "`Λ′_φ` is an outer measure but not a
metric outer measure (Exercise 6.2.4)", "behaves more like a capacity" and the convention on `M₁, M₂, …` (l. 1819;
remarks); "we cannot replace `Λ′_α` by `Λ_α`" (l. 1839; Lan72, Nev70, HayKe76; a remark); the proof of Theorem 10.3
((10.2.10), (10.2.11), Fekete points, black squares; l. 1841–1875; its "which implies (8)" is (9) [misprint?]); the
proof of Theorem 10.5 ((10.2.16), l. 1901–1955); "upper estimates by covers together with Theorem 10.5 give the
dimension" (l. 1957; a remark); the Example of the Cantor-type sets with Fig. 10.1 (l. 1959–1968); Exercises
10.2.1–10.2.6 (Exercise 10.2.2 is cited in the proof of Theorem 10.15, Exercise 10.2.3 uses Corollary 9.13).

**Conventions of Chapter 10** (the later files of the chapter refer to them as "as in §10.2").
- "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc`; "onto `G`" is
  `IsConformalOnto f unitDisc G`; "into `𝔻`" adds `MapsTo f unitDisc unitDisc` (as in Chapters 6–8). "A Borel set on
  `𝕋`" is `MeasurableSet A ∧ A ⊆ sphere 0 1`.
- The linear measure `Λ` is `μH[1]` for plane sets (Part C), `circleMeasure` for sets on `𝕋` (§4.4, Part C) and
  `volume` on `[0, 1] ⊆ ℝ` (Theorem 10.5).
- A gauge `φ` is a real function with `IsHausdorffGauge φ` (the §10.2 standing assumption, explicit in every
  statement). `Λ_φ` is `hausdorffMeasureGauge φ`, applied to arbitrary sets (its values are those of the outer
  measure); `Λ_α` is `μH[α]` (the same as `hausdorffMeasureGauge (fun t => t ^ α)`); `Λ′_φ` is `hausdorffContent φ`
  and `Λ′_α` is `hausdorffContent (fun t => t ^ α)`. "`E` has σ-finite outer `Λ_ψ`-measure" is
  `SigmaFinite ((hausdorffMeasureGauge ψ).restrict E)`, the form of the leader ruling for σ-finite linear measure.
- `dim` is `dimH` (in `[0, ∞]`); real bounds are compared through `ENNReal.ofReal`, and for `A ⊆ 𝕋`,
  `dimH A ≤ 1`, so `(dimH A).toReal` is the book's number.
- Capacity is `GarnettMarshall2005.capacity` (QD1 (B)): the inner capacity (the supremum over compact subsets) of an
  arbitrary set, in `[0, ∞]`; on compact sets it is Pommerenke's transfinite diameter (9.1.3) by the Fekete–Szegő
  equality, which Chapter 9 states as (9.3.7). No Chapter 9 definition is used here.
- Boundary values (the standing assumption of §10.3, P2 l. 1998: "the angular limit `f(ζ)` exists and is finite for
  `ζ ∈ A`"): a witness `F : ℂ → ℂ` with `HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)` for `ζ ∈ A`, and
  `f(A)` is `F '' A` (determined by `f` and `A`, since angular limits are unique). The same reading is used for the
  §10.1 statements and for Theorem 10.11.
- Constants: "`M₁, M₂, …` suitable positive constants" (l. 1819, 2317) are existential after the data they depend on;
  "`K₁, K₂, …` absolute constants" (l. 2022, 2144, 2483) are `∃ K, ∀ f …`.
- `r → 1` is `𝓝[<] 1`, `ε → 0` is `𝓝[>] 0`; `O` is `Asymptotics.IsBigO`; for the covering numbers of §10.5 it is
  phrased in `[0, ∞]`. "Almost nowhere on `𝕋`" is `∀ᵐ t : ℝ, ¬ …` at `e^{it}` (the `thm1_7` convention). The integral
  `∫_𝕋 |f'(rζ)|^p |dζ|` is `2 * π * Real.circleAverage (fun z => ‖deriv f z‖ ^ p) 0 r` (Chapter 8).
- The special gauges `φ` of (10.3.1) and `ψ` of (10.4.1) are given by formulas valid only near `0`; the statements
  that use them hold for every gauge equal to the formula on some interval `(0, t₀)` (`=ᶠ[𝓝[>] 0]`), since only the
  germ at `0` matters (P2 l. 1751; Q10.8).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

/-- **Standing assumption** (§10.2, P2 l. 1739, with §10.1, l. 1695; helper). `φ` is a gauge: a positive, continuous
and increasing function in `(0, +∞)` with `φ(t) → 0` as `t → 0`, and `φ(0) = 0`.
Modelling: `φ : ℝ → ℝ` is read on `[0, ∞)`; continuity on `[0, ∞)` together with `φ(0) = 0` is "`φ(t) → 0` as
`t → 0`"; "increasing" is non-decreasing (`MonotoneOn`; at P2 l. 2423 the book calls a non-decreasing distribution
function "increasing"). For `α > 0` the power `t ↦ t^α` is a gauge. -/
def IsHausdorffGauge (φ : ℝ → ℝ) : Prop :=
  φ 0 = 0 ∧ ContinuousOn φ (Ici 0) ∧ MonotoneOn φ (Ici 0) ∧ ∀ t : ℝ, 0 < t → 0 < φ t

/-- The gauge `φ` as a function on `[0, ∞]` (helper for (10.2.1) and (10.2.5)): `0 ↦ 0`, `∞ ↦ ∞`, and `r ↦ φ(r)`
otherwise.
Modelling: a set of infinite diameter is not admissible in a cover (it costs `∞`; the book's `φ` is defined on
`(0, ∞)` only); `gaugeFn φ 0 = 0` is `φ(0) = 0` of a gauge. For `α > 0`, `gaugeFn (fun t => t ^ α)` is `r ↦ r ^ α`,
so `Λ_{t^α}` is `μH[α]` on the nose. -/
def gaugeFn (φ : ℝ → ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = 0 then 0 else if r = ⊤ then ⊤ else ENNReal.ofReal (φ r.toReal)

/-- **Definition (10.2.1)** (§10.2; P2 l. 1739–1751, 1763; cited "(1)" at P2 l. 1767, 1805, 1959). For any set
`E ⊆ ℂ`, `Λ_φ(E) = lim_{ε→0+} inf_{(B_k)} Σ_k φ(diam B_k) ≤ +∞`, where `(B_k)` runs through all `ε`-covers of `E`,
that is, `E ⊆ ⋃_k B_k` and `diam B_k ≤ ε` for `k = 1, 2, …`. `Λ_φ` is called the Hausdorff measure with respect to
`φ` (l. 1763).
Modelling (leader ruling QD3): a thin definition, Mathlib's `Measure.mkMetric` of `gaugeFn φ`.
`MeasureTheory.Measure.mkMetric_apply` is (10.2.1) literally: countable covers by arbitrary sets of diameter at most
`ε`, the sums of `φ(diam B_k)`, and the supremum over `ε > 0`, which is the book's limit of a function increasing as
`ε ↓ 0`; empty members cost nothing, as `φ(0) = 0` gives in the book. Its value on every set, not only on Borel
sets, is the book's, since the measure agrees with the outer measure `OuterMeasure.mkMetric (gaugeFn φ)` everywhere
(`MeasureTheory.Measure.mkMetric_toOuterMeasure`). Only the germ of `φ` at `0` enters (P2 l. 1751). -/
def hausdorffMeasureGauge (φ : ℝ → ℝ) : Measure ℂ :=
  Measure.mkMetric (gaugeFn φ)

/-- **Proposition 10.2** (§10.2; P2 l. 1765; cited at P2 l. 1787, 2331 and, in the proof of Theorem 10.13, 2401),
second assertion. If `φ(x)/ψ(x) → 0` as `x → 0`, then `Λ_φ(E) = 0` whenever `E` has σ-finite outer
`Λ_ψ`-measure.
Modelling: `φ` and `ψ` are gauges (the standing assumption); `x → 0` is `x → 0+` (the gauges live on `[0, ∞)`),
and the quotient has no junk there (`ψ(x) > 0` for `x > 0`); "`E` has σ-finite outer `Λ_ψ`-measure" is
`SigmaFinite ((hausdorffMeasureGauge ψ).restrict E)`, which for an arbitrary `E ⊆ ℂ` says that `E` is covered by
countably many sets of finite outer `Λ_ψ`-measure (measurable hulls of the same measure exist). The first assertion
is Mathlib's `mkMetric_mono` (see the file header). -/
theorem prop10_2_b {φ ψ : ℝ → ℝ} (hφ : IsHausdorffGauge φ) (hψ : IsHausdorffGauge ψ)
    (hlim : Tendsto (fun x : ℝ => φ x / ψ x) (𝓝[>] 0) (𝓝 0)) {E : Set ℂ}
    (hE : SigmaFinite ((hausdorffMeasureGauge ψ).restrict E)) :
    hausdorffMeasureGauge φ E = 0 := by
  sorry

/-- **Definition (10.2.5)** (§10.2; P2 l. 1799–1811; cited "(5)" at P2 l. 1875). For `E ⊆ ℂ`,
`Λ′_φ(E) = inf_{(B_k)} Σ_k φ(diam B_k)`, where `(B_k)` runs through all covers of `E`, not only through the
`ε`-covers as in (10.2.1). `Λ′_α` is `Λ′_φ` for `φ(t) = t^α`, `α > 0` (l. 1811).
Modelling: `OuterMeasure.boundedBy` of `s ↦ gaugeFn φ (diam s)`, whose value on `E` is the infimum, over the
countable covers of `E` (finite covers included, empty members cost nothing), of `Σ_k φ(diam B_k)`
(`MeasureTheory.OuterMeasure.boundedBy_apply`); a set of infinite diameter costs `∞`. Mathlib has no Hausdorff
content; its internal `OuterMeasure.mkMetric'.pre … ⊤` is the same infimum. An outer measure, as the book says
(l. 1819). `Λ′_α` is written `hausdorffContent (fun t => t ^ α)`. -/
def hausdorffContent (φ : ℝ → ℝ) : OuterMeasure ℂ :=
  OuterMeasure.boundedBy fun s => gaugeFn φ (ediam s)

/-- **Formula (10.2.6)** (§10.2; P2 l. 1805–1809; cited "(6)" at P2 l. 1813, "By (6) it has the same nullsets"). For
every `E ⊆ ℂ`, `Λ′_φ(E) = 0 ⟺ Λ_φ(E) = 0`.
Modelling: `φ` is a gauge (the standing assumption); `E` is arbitrary, as in the book ("For `E ⊂ ℂ`"). -/
theorem eq10_2_6 {φ : ℝ → ℝ} (hφ : IsHausdorffGauge φ) (E : Set ℂ) :
    hausdorffContent φ E = 0 ↔ hausdorffMeasureGauge φ E = 0 := by
  sorry

/-- **Theorem 10.3** (§10.2; (10.2.8), (10.2.9); P2 l. 1821–1831; cited at P2 l. 1681, and in the proofs of
Proposition 10.10, l. 2182, and Theorem 10.11, l. 2277). Suppose that (8) `φ(xt) ≤ M₁ x^α φ(t)` (`0 < x ≤ 2`,
`t > 0`) for some `α > 0`. If `E` is a Borel set in `ℂ`, then (9) `Λ′_φ(E) ≤ M₂ φ(cap E)`.
Modelling: `φ` is a gauge (the standing assumption); `M₂` is a suitable positive constant (l. 1819) depending only on
`α` and `M₁` (the proof builds it from them: `M₃` by iterating (8)): `∀ α M₁, ∃ M₂ > 0, ∀ φ E` (Q10.3(a)). `cap` is
`GarnettMarshall2005.capacity`, the inner capacity of arbitrary sets (QD1 (B)); `φ(cap E)` is `gaugeFn φ (cap E)`,
so `φ(0) = 0`. For `cap E = ∞` (e.g. `E = ℝ`) the right side is `∞` (`gaugeFn φ ⊤ = ⊤`, `M₂ > 0`), so that case is
trivially true and no finiteness hypothesis is added. For `M₁ < 1` the hypothesis (8) fails for every gauge
(take `x = 1`), which only makes those instances of the statement trivial. -/
theorem thm10_3 {α : ℝ} (hα : 0 < α) (M₁ : ℝ) :
    ∃ M₂ : ℝ, 0 < M₂ ∧ ∀ φ : ℝ → ℝ, IsHausdorffGauge φ →
      (∀ x t : ℝ, 0 < x → x ≤ 2 → 0 < t → φ (x * t) ≤ M₁ * x ^ α * φ t) →
      ∀ E : Set ℂ, MeasurableSet E →
        hausdorffContent φ E ≤ ENNReal.ofReal M₂ * gaugeFn φ (GarnettMarshall2005.capacity E) := by
  sorry

/-- **Unlabelled claim** (§10.2, P2 l. 1833–1837, the display (10.1.3) of the overview, P2 l. 1681–1685; cited
"(10.1.3)" at P2 l. 1105, §9.3, and used as "Theorem 10.3" in the proof of Proposition 10.10, P2 l. 2182). In
particular (`φ(t) = t^α` in Theorem 10.3) `Λ′_α(E) ≤ M₂ (cap E)^α` for Borel sets `E ⊆ ℂ`.
Modelling: `M₂` depends on `α` only (the literal `∀ α > 0, ∃ M₂`, Q10.3(b); the book states no uniformity in `α`,
although the proof of Proposition 10.10 uses one constant for `0 < α ≤ 1`); `(cap E)^α` is the power in `[0, ∞]`, so
no finiteness hypothesis is needed (for `cap E = ∞` the right side is `∞`). -/
theorem thm10_3_pow {α : ℝ} (hα : 0 < α) :
    ∃ M₂ : ℝ, 0 < M₂ ∧ ∀ E : Set ℂ, MeasurableSet E →
      hausdorffContent (fun t => t ^ α) E ≤ ENNReal.ofReal M₂ * GarnettMarshall2005.capacity E ^ α := by
  sorry

/-- **Unlabelled claim** (§10.2, P2 l. 1839; used in the standing assumption of §10.3, P2 l. 1998, in the proof of
Theorem 10.15, P2 l. 2461, and at P2 l. 1105, §9.3: "a set of capacity zero has … `α`-dimensional Hausdorff measure
zero for every `α > 0`"). For a Borel set `E ⊆ ℂ`, `cap E = 0` implies `dim E = 0`. -/
theorem thm10_3_cap_zero {E : Set ℂ} (hE : MeasurableSet E) (hcap : GarnettMarshall2005.capacity E = 0) :
    dimH E = 0 := by
  sorry

/-- **Proposition 10.4** (§10.2; Frostman, Fro35, proof in HayKe76, p. 223; (10.2.12); P2 l. 1877–1883; (10.2.12) is
used by Exercise 10.2.5). If `E ⊂ ℂ` is compact and `Λ_φ(E) > 0`, then there exists a measure `μ` on `E` with
`0 < μ(E) < ∞` such that (12) `μ(D(a, r)) ≤ φ(r)` for `a ∈ ℂ`, `0 < r ≤ 1`.
Modelling: `φ` is a gauge (the standing assumption); a measure on `E` is a finite Borel measure on `ℂ` carried by `E`
(`μ(ℂ ∖ E) = 0`); `D(a, r)` is the open disc `ball a r`. The radius in (12) against the diameter in `Λ_φ` is the
book's (Q10.7): in `ℂ`, `Λ_φ` and `Λ_{φ(c·)}` have the same null sets for every gauge, and `μ` may be rescaled, so the
printed statement is the Frostman lemma. -/
theorem prop10_4 {φ : ℝ → ℝ} (hφ : IsHausdorffGauge φ) {E : Set ℂ} (hE : IsCompact E)
    (hpos : 0 < hausdorffMeasureGauge φ E) :
    ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ Eᶜ = 0 ∧ 0 < μ E ∧
      ∀ a : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → μ (ball a r) ≤ ENNReal.ofReal (φ r) := by
  sorry

/-- **Theorem 10.5** (§10.2; Hun88, proof Roh89; (10.2.13)–(10.2.15); P2 l. 1885–1899; cited at P2 l. 1693, 1957 and
in the Example, l. 1965). For `k = 0, 1, …` let `A_k ⊂ [0, 1]` be a union of finitely many disjoint closed sets
`B_{k,n}` such that `Λ(A₀) > 0` and `A_k ⊃ A_{k+1}`. We assume that `0 < a < b < 1` and (13)
`B_{k+1,n} ∩ B_{k,m} ≠ ∅ ⟹ B_{k+1,n} ⊂ B_{k,m}`, `diam B_{k+1,n} ≤ a diam B_{k,m}`, (14)
`Λ(A_{k+1} ∩ B_{k,m}) ≥ b Λ(B_{k,m})` for all `m`. Then (15) `Λ_α(⋂_{k=0}^∞ A_k) > 0`,
`α = log(b/a)/log(1/a)`.
Modelling: sets of `ℝ` (the book's `A_k ⊂ [0, 1]`), `Λ` is `volume` and `Λ_α` is `μH[α]` on `ℝ` (Q10.10); the
finite families are `B k : Fin (N k) → Set ℝ`, pairwise disjoint and closed, with `A k = ⋃ n, B k n`; (13) and (14)
hold for all `k, n, m`; `diam` is `Metric.diam` (the sets are bounded). OCR: (13) is a text line that begins with its
tag "(13)" (l. 1889); the crops of (14) (`ca0e1123…`) and (15) (`0b1ba33a…`) were checked. -/
theorem thm10_5 {N : ℕ → ℕ} {B : (k : ℕ) → Fin (N k) → Set ℝ} {A : ℕ → Set ℝ}
    (hAB : ∀ k, A k = ⋃ n, B k n) (hA01 : ∀ k, A k ⊆ Icc 0 1) (hBc : ∀ k n, IsClosed (B k n))
    (hBd : ∀ k, ∀ n m : Fin (N k), n ≠ m → Disjoint (B k n) (B k m)) (hA0 : 0 < volume (A 0))
    (hAmono : ∀ k, A (k + 1) ⊆ A k) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (h13 : ∀ k, ∀ n : Fin (N (k + 1)), ∀ m : Fin (N k), (B (k + 1) n ∩ B k m).Nonempty →
      B (k + 1) n ⊆ B k m ∧ diam (B (k + 1) n) ≤ a * diam (B k m))
    (h14 : ∀ k, ∀ m : Fin (N k), ENNReal.ofReal b * volume (B k m) ≤ volume (A (k + 1) ∩ B k m)) :
    0 < μH[Real.log (b / a) / Real.log (1 / a)] (⋂ k, A k) := by
  sorry

end Pommerenke1992
