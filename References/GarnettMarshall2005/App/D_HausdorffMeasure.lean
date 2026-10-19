import References.GarnettMarshall2005.Ch03.S04_EquilibriumDistribution
import LiZhongQC.Lemmas.CZDecomposition

/-!
# Garnett–Marshall, Appendix D: Hausdorff measure

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix D (pp. 456–466;
`full.md` P3:3185–3668: the main text to P3:3466, Exercises D.1–D.2 at P3:3467–3667).

Conventions. `B(z, r)` is the open disc `Metric.ball z r` (P1:780), with `r > 0`. A cover `E ⊂ ⋃ B(z_j, r_j)` is a
countable family of discs (finite families included). The contents `M_h`, `m_h` and the measure `Λ_h` are defined on
all sets `E ⊆ ℂ`: `M_h` and `m_h` are outer measures, `OuterMeasure.boundedBy` of a gauge that charges `h(r)` to
an open disc of radius `r`, resp. `h(ℓ(Q))` to a dyadic square `Q`, and `∞` to every other set (empty members of a
cover cost nothing); `Λ_h` is a `Measure` on the Borel sets of `ℂ`, Mathlib's metric-outer-measure construction
`Measure.mkMetric'` of the disc gauge (leader ruling F1), whose value on every set is the book's. Only the germ of `h`
at `0⁺` enters `Λ_h`, since the radii of the covers tend to `0`. `Λ_α` and `M_{r^α}` are written inline,
`hausdorffMeasureGM (fun r => r ^ α)` and `hausdorffContentGM (fun r => r ^ α)` (`Real.rpow`, so `r⁰ = 1`). `dim` is
Mathlib's `dimH`. The dyadic square `Q = [j/2ⁿ, (j+1)/2ⁿ) × [k/2ⁿ, (k+1)/2ⁿ)`, `ℓ(Q) = 2^{−n}`, is
`LiZhongQC.dyadicSquare (−n) j k`: the project indexes the squares by the scale `m` of the side `2^m`, the book by `n`
with side `2^{−n}`, so the scale index is negated. `Cap` is `capacity` of (III.4.8) (leader ruling B1; for compact sets
it is (III.1.3)) and `diam` is `Metric.diam`. The linear measure `Λ₁` of Chapters VI–X is arc length, `μH[1]` (leader
ruling C2), not the App. D normalization. This file compiles right after Ch. III §4 and is imported by Ch. VI §5
(leader ruling C3).

* Formula (D.1) and the first definition `Λ₂(E) = (1/π) Area(E)` (App. D, P3:3187–3191) — omitted: the infimum of
  the sums of π r_j² over disc covers is the area, Lebesgue measure (volume); (D.1) serves only as the template of
  (D.2) (P3:3193), and the general definition (P3:3219) gives Λ₂ as the Hausdorff measure of the gauge r²
* Definition (measure function, App. D, P3:3193) — `IsMeasureFunction`
* Definition ((D.2), the Hausdorff content `M_h(E)` with respect to a measure function `h`, App. D, P3:3193–3197) —
  `hausdorffContentGM`, `discGaugeGM` (helper)
* Definition (`Λ_h^δ(E) = inf {Σ h(r_j) : E ⊂ ⋃ B(z_j, r_j), r_j ≤ δ}`, App. D, P3:3205–3209; introduced by "we
  change the definition (M.2)", which is (D.2) [misprint], a text-layer span, not OCR output) — exists:
  `MeasureTheory.OuterMeasure.mkMetric'.pre`
  (at the gauge discGaugeGM h and the diameter bound 2δ: a nonempty open disc of radius r has diameter 2r, so the
  admissible members are exactly the open discs with r ≤ δ; the monotonicity in δ and the existence of the limit,
  P3:3211–3217, are built in)
* Definition (the h-Hausdorff measure `Λ_h(E) = lim_{δ→0} Λ_h^δ(E)`, and the α-dimensional Hausdorff measure
  `Λ_α = Λ_h` for `h(r) = r^α`, App. D, P3:3213–3219) — `hausdorffMeasureGM`
* Formula (D.3) (App. D, P3:3227–3237) — `eqD_3`
* Definition (the Hausdorff dimension `dim(E) = inf {α : Λ_α(E) = 0}`, App. D, P3:3239–3243) — exists: `dimH`
  (Mathlib; for α ≥ 0, Λ_α ≤ μH[α] ≤ 2^α Λ_α: a disc of radius r has diameter 2r, and a set of diameter d ≤ δ lies in
  an open disc of radius d + ε; so Λ_α and μH[α] have the same null sets and inf {α ≥ 0 : Λ_α(E) = 0} is dimH E, by
  Mathlib's dimH_eq_iInf; α ranges over [0, ∞) [reading], so that dim of the empty set is 0)
* Formula (D.4) (App. D, P3:3253–3257) — `eqD_4`
* Formula (D.5) (App. D, P3:3259–3263) — `eqD_5`
* Definition (dyadic square `Q = [j/2ⁿ, (j+1)/2ⁿ) × [k/2ⁿ, (k+1)/2ⁿ)` with side length `ℓ(Q) = 2^{−n}`, App. D,
  P3:3265–3273) — exists: `LiZhongQC.dyadicSquare` (the same half-open squares: the book's Q with side 2^{−n} and
  lower left corner (j2^{−n}, k2^{−n}) is the project's square at scale −n and grid position (j, k), of side 2 to
  the power of the scale; the scale index is negated, and ℓ(Q) is 2^m at the project's scale m)
* Unlabelled (App. D, P3:3273–3279, "this important property"): if `Q₁` and `Q₂` are dyadic squares, then
  `Q₁ ⊂ Q₂`, `Q₂ ⊂ Q₁` or `Q₁ ∩ Q₂ = ∅` — `dyadicSquare_trichotomy`
* Definition (the dyadic Hausdorff content `m_h(E) = inf {Σ h(ℓ(Q_p)) : E ⊂ ⋃ Q_p dyadic}`, App. D, P3:3281–3283) —
  `dyadicContentGM`, `dyadicGaugeGM` (helper)
* Formula (D.6) (App. D, P3:3285–3291) — `eqD_6`
* Theorem D.1 (Frostman, App. D; (D.7), (D.8)) — `thmD_1_a`, `thmD_1_b`
* Corollary D.2 (App. D; (D.10), (D.11)) — `corD_2`
* Corollary D.3 (App. D; (D.12)) — `corD_3`
* Theorem D.4 (Erdős–Gillis, App. D; (D.13)) — `thmD_4`

Not stated (inventory U−, remarks, examples and proof steps): the remark that `M_h` is finite on bounded sets but
usually not finitely additive, with the example `h(r) = 2r`, `M_h([0, 1]) = M_h([0, 1] + iε) = 1`,
`M_h([0, 1] ∪ ([0, 1] + iε)) = √(1 + ε²)` (P3:3199–3203); the examples `Λ₂(E) = (1/π) Area(E)`, `Λ₀(E)` = the
number of points of `E`, and `Λ₁(E)` = half the arc length of `E` when `E` lies on a rectifiable curve (P3:3219; the
last is App. D's side of the book's inconsistency on `Λ₁`, which Chapters VI–X use as arc length, `μH[1]`: leader
ruling C2, recorded in the root's Corrections list); the claim that `Λ_h` is a metric outer measure,
`Λ_h(A ∪ B) = Λ_h(A) + Λ_h(B)` if `dist(A, B) > 0`, hence a countably additive measure on the Borel sets
(P3:3219–3225; built into the definition: `MeasureTheory.OuterMeasure.mkMetric'_isMetric`); the display
`δ^{β−α} Λ_α^δ(E) ≥ Λ_β^δ(E)` for `α < β` (P3:3227–3231, the derivation of (D.3)); the dichotomy `Λ_α(E) = 0` for
`α > dim(E)`, `= ∞` for `α < dim(E)` (P3:3245–3249; for `μH` it is Mathlib's `hausdorffMeasure_of_dimH_lt` and
`hausdorffMeasure_of_lt_dimH`, transported through the comparison `Λ_α ≤ μH[α] ≤ 2^α Λ_α` of the `dimH` bullet);
"Exercise D.1 shows that `dim(E)` can be any number in `[0, 2]`" (P3:3251); "clearly `M_h(E) ≤ Λ_h(E)`" and the
argument for (D.4) (P3:3253); "(D.4) and (D.5) also hold with `m_h` in place of `M_h`" (P3:3291); `dim(E) ≤ 2` for
every `E ⊂ ℂ` and `Λ_α(ℂ) = 0` for `α > 2` (P3:3293–3299; Mathlib's `Real.dimH_univ_eq_finrank` with `dimH_mono`);
"Corollary D.2 shows that `Cap(E)` is positive if `dim(E) > 0`" (P3:3409); the remark after Theorem D.4 that it is
almost a converse to Corollary D.2, with the gauge `(log 1/r)^{−1} (log log 1/r)^{−p}`, `p > 1`, satisfying (D.10)
(P3:3433). Inside items: the monotonicity of `Λ_h^δ` in `δ` and the existence of the limit (P3:3211–3217;
`MeasureTheory.OuterMeasure.mkMetric'.mono_pre`, `MeasureTheory.OuterMeasure.mkMetric'.tendsto_pre`); the paving and
parent facts of dyadic squares (P3:3273; in the project `LiZhongQC.dyadicSquare_disjoint_same_scale`,
`LiZhongQC.mem_dyadicSquare_gridIdx`, `LiZhongQC.dyadicSquare_subset_parent`); the two covering facts behind (D.6)
(P3:3285); the step (D.9) of the proof of Theorem D.1; Egoroff's theorem, quoted in the proof of Theorem D.4 (Mathlib
`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`). Exercises D.1–D.2 ((D.14)–(D.18), Figure D.1) are not items; the
misreferences in their hints are recorded only: P3:3633 "(D.15)" is (D.16), P3:3641 "(D.17)" is (D.18), P3:3651
"(D.9)" is (D.18), and P3:3649 "Corollary A.2" is Corollary D.2 [misprint] (a text-layer span; root Corrections
list).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (dyadicSquare)

/-- **Definition** (measure function, App. D, P3:3193; cited at P3:3253, 3303, 3377, in VI §5, P2:1128, 1146, in
VIII §2, P2:3675, 4038, 4050, and in IX §3, P2:6889). A measure function is a continuous and increasing function
`h(r)` on `[0, ∞)`.
Modelling (leader ruling F2): `h : ℝ → ℝ`, read on `[0, ∞)` only: `ContinuousOn` and `MonotoneOn` on `Ici 0`.
"Increasing" is non-decreasing [reading]: App. D's own example `h(r) = r⁰ ≡ 1`, whose `Λ₀` counts points (P3:3219),
is not strictly increasing, and every App. D statement stays true under the weaker hypothesis. `0 ≤ h 0` [reading]:
a measure function assigns masses, and with it `ENNReal.ofReal (h r)` never truncates for `r ≥ 0`. The notion does
not contain `h(0) = 0` (again `r⁰`); Ch. VIII §2 adds it as a hypothesis, and (D.10) forces it in Corollary D.2. -/
def IsMeasureFunction (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Ici 0) ∧ MonotoneOn h (Ici 0) ∧ 0 ≤ h 0

/-- The disc gauge (helper, not a book notion; App. D, (D.2) and `Λ_h^δ`, P3:3193–3209): an open disc `B(z, r)`,
`r > 0`, is charged `h(r)`, and every other set is charged `∞`.
Modelling: a nonempty open disc of `ℂ` determines its centre and its radius, so the infimum has at most one term.
Inside `OuterMeasure.boundedBy` and `mkMetric'.pre` the empty set costs `0`, so the admissible covers are the
countable families (finite ones included) of open discs of positive radius. -/
def discGaugeGM (h : ℝ → ℝ) (s : Set ℂ) : ℝ≥0∞ :=
  ⨅ (z : ℂ) (r : ℝ) (_ : 0 < r) (_ : s = ball z r), ENNReal.ofReal (h r)

/-- **Definition** ((D.2), the Hausdorff content, App. D, P3:3193–3197; cited at P3:3253–3262, 3288, 3315, 3386,
3414, and in IX §3, P2:6889–6925, "the Hausdorff content `M_h` defined in Appendix D"). With respect to the measure
function `h`, the Hausdorff content of a set `E` is `M_h(E) = inf {Σ h(r_j) : E ⊂ ⋃ B(z_j, r_j)}`.
Modelling: `OuterMeasure.boundedBy (discGaugeGM h)`, whose value on `E` is the infimum, over the countable covers of
`E` by open discs, of the sums `Σ h(r_j)` (`MeasureTheory.OuterMeasure.boundedBy_apply`; empty members cost `0`, so
finite covers are included). An outer measure, as the book's `M_h` is only subadditive ("usually not finitely
additive", P3:3199). Defined for every `h`; for a measure function no value `ofReal (h r)`, `r > 0`, truncates.
(D.2) was checked against the equation image. -/
def hausdorffContentGM (h : ℝ → ℝ) : OuterMeasure ℂ :=
  OuterMeasure.boundedBy (discGaugeGM h)

/-- **Definition** (the h-Hausdorff measure `Λ_h` and, for `h(r) = r^α`, the α-dimensional Hausdorff measure `Λ_α`, App.
D, P3:3205–3225; used in VI §5, VIII §2, IX and App. K). For `δ > 0`,
`Λ_h^δ(E) = inf {Σ h(r_j) : E ⊂ ⋃ B(z_j, r_j) and r_j ≤ δ}`; `Λ_h^δ(E)` increases as `δ` decreases, the limit
`Λ_h(E) = lim_{δ→0} Λ_h^δ(E)` exists in `[0, ∞]`, and `Λ_h(E)` is the h-Hausdorff measure of `E`. `Λ_h` is a countably
additive measure for which all Borel sets are measurable.
Modelling (leader ruling F1): `Measure.mkMetric' (discGaugeGM h)`. Mathlib's `OuterMeasure.mkMetric' m` is
`⨆ r > 0, mkMetric'.pre m r`, where `mkMetric'.pre m r` is the infimum of `Σ m(s_j)` over the countable covers by sets
of diameter `≤ r`; for the disc gauge these are the covers by open discs `B(z_j, r_j)` with `2 r_j ≤ r`, charged
`h(r_j)`. (1) Diameter versus radius: `mkMetric'.pre (discGaugeGM h) (2δ)` is the book's `Λ_h^δ`, and since
`mkMetric'.pre` is antitone in the bound, the supremum over the diameter bounds `r > 0` is the book's limit over the
radius bounds `δ → 0` (the same limit). (2) The value on every set is the book's `Λ_h(E)`, not only on Borel sets: a
`Measure` evaluates as the trim of its outer measure (`MeasureTheory.Measure.mkMetric'_toOuterMeasure`), and the trim
changes nothing here, because every cover consists of open discs: for `δ = 1/m` the union `G_m ⊇ E` of a cover that is
optimal up to `ε` is open with `Λ_h^{1/m}(G_m) ≤ Λ_h^{1/m}(E) + ε`, and the `G_δ` hull `⋂_m G_m ⊇ E` has
`Λ_h(⋂_m G_m) ≤ Λ_h(E) + ε`. (3) This is not `Measure.mkMetric` of `h(diam/2)` over arbitrary sets (Mathlib's standard
form, for `h = r^α` equal to `2^{−α} μH[α]`): the book's stated constants on `Λ_h` (the constant `1` in Theorem D.1's
`μ(E) ≤ Λ_h(E)`, `4A` in VIII Lemma 2.3, `2^{−α}` and `1/36` in Exercise D.1) are those of covers by discs charged by
their radius (the constants `25`, `225` of (D.6), (D.8), (D.11) concern the content `M_h`, whose disc normalization is
(D.2) itself). It stays in this work's namespace: Pommerenke's `Λ_φ` (§10.2) charges `φ(diam)`, a different gauge. Only
the germ of `h` at `0⁺` enters, so a gauge given by a formula valid only near `0` is used as it stands (Theorem D.4
here, VIII §2, App. K). The book's `Λ_h^δ` is `mkMetric'.pre (discGaugeGM h) (2δ)` (not a separate declaration). The
displays were checked against the equation images. -/
def hausdorffMeasureGM (h : ℝ → ℝ) : Measure ℂ :=
  Measure.mkMetric' (discGaugeGM h)

/-- **Formula (D.3)** (App. D, P3:3227–3237; cited at P3:3245, "By (D.3) we have"). If `α < β`, then
`Λ_α(E) < ∞ ⟹ Λ_β(E) = 0` (the book derives it from `δ^{β−α} Λ_α^δ(E) ≥ Λ_β^δ(E)`).
Modelling: `Λ_α` is `hausdorffMeasureGM (fun r => r ^ α)`; `E` is any set (`Λ_α` is defined on all sets). No sign
condition on `α`, as printed: for `α < 0` every nonempty set has `Λ_α = ∞` (a disc of radius `r ≤ δ` costs
`r^α ≥ δ^α`), so the implication is harmless there. Near miss: Mathlib's
`MeasureTheory.Measure.hausdorffMeasure_zero_or_top` is the same dichotomy for `μH`, a different measure. (D.3) was
checked against the equation image. -/
theorem eqD_3 {α β : ℝ} (hαβ : α < β) (E : Set ℂ) (hE : hausdorffMeasureGM (fun r => r ^ α) E < ⊤) :
    hausdorffMeasureGM (fun r => r ^ β) E = 0 := by
  sorry

/-- **Formula (D.4)** (App. D, P3:3253–3257; cited at P3:3291, in the proof of Corollary D.2, P3:3389, "by (D.4)",
and in the last step of the proof of Theorem IX.3.1, P2:6925). For any measure function `h`, (D.4) `M_h(E) = 0` if
and only if `Λ_h(E) = 0`.
Modelling: `E` is any set. The statement also holds in the degenerate cases that `IsMeasureFunction` admits: if
`h ≡ 0` near `0` both sides vanish for every `E`; if `h(0) > 0` both vanish only for `E = ∅`. (D.4) was checked
against the equation image. -/
theorem eqD_4 {h : ℝ → ℝ} (hh : IsMeasureFunction h) (E : Set ℂ) :
    hausdorffContentGM h E = 0 ↔ hausdorffMeasureGM h E = 0 := by
  sorry

/-- **Formula (D.5)** (App. D, P3:3259–3263; cited at P3:3291). (D.5) `dim(E) = inf {α : M_{r^α}(E) = 0}`.
Modelling: `dim` is `dimH` (the `exists` bullet of the definition of `dim`); `M_{r^α}` is
`hausdorffContentGM (fun r => r ^ α)`. `α` ranges over `[0, ∞)` [reading], as in the definition of `dim`: over all
real `α` the infimum would be `−∞` for every `E`, since for `α < 0` countably many discs of radii `R_k → ∞` with
`Σ R_k^α` small cover `ℂ`, so `M_{r^α}(E) = 0`. The shape is that of Mathlib's `dimH_eq_iInf`, with values in
`[0, ∞]`. (D.5) was checked against the equation image. -/
theorem eqD_5 (E : Set ℂ) :
    dimH E = ⨅ (α : ℝ≥0) (_ : hausdorffContentGM (fun r => r ^ (α : ℝ)) E = 0), (α : ℝ≥0∞) := by
  sorry

/-- **Unlabelled** (App. D, P3:3273–3279, "this important property" of dyadic squares; used in the proofs of (D.6)
and of Theorem D.1, invoked in IX §2, P2:6184, "Like dyadic squares, the cubes `Q_{n,j}` have the property (2.12)",
and in the maximal-dyadic-square arguments of X §2–§4 and §10). If `Q₁` and `Q₂` are two dyadic squares, then
`Q₁ ⊂ Q₂`, `Q₂ ⊂ Q₁`, or `Q₁ ∩ Q₂ = ∅`.
Modelling: dyadic squares of all scales are `dyadicSquare m i j` (`m, i, j ∈ ℤ`; the book's `n` is `−m`). Near
misses in the project, special cases: `LiZhongQC.dyadicSquare_disjoint_same_scale` (one scale) and
`LiZhongQC.dyadicSquare_subset_parent` (parent squares). The display was checked against the equation image. -/
theorem dyadicSquare_trichotomy (m i j m' i' j' : ℤ) :
    dyadicSquare m i j ⊆ dyadicSquare m' i' j' ∨ dyadicSquare m' i' j' ⊆ dyadicSquare m i j ∨
      Disjoint (dyadicSquare m i j) (dyadicSquare m' i' j') := by
  sorry

/-- The dyadic gauge (helper, not a book notion; App. D, P3:3281–3283): a dyadic square `Q` is charged `h(ℓ(Q))`,
and every other set is charged `∞`.
Modelling: the square `dyadicSquare m i j` has side `ℓ(Q) = 2^m` (the book's `2^{−n}` with `n = −m`); a dyadic square
determines its scale and grid position, so the infimum has at most one term. Inside `OuterMeasure.boundedBy` the empty
set costs `0`. -/
def dyadicGaugeGM (h : ℝ → ℝ) (s : Set ℂ) : ℝ≥0∞ :=
  ⨅ (m : ℤ) (i : ℤ) (j : ℤ) (_ : s = dyadicSquare m i j), ENNReal.ofReal (h ((2 : ℝ) ^ m))

/-- **Definition** (the dyadic Hausdorff content, App. D, P3:3281–3283; cited at P3:3288–3299 and in the proof of
Theorem D.1, P3:3371). `m_h(E) = inf {Σ h(ℓ(Q_p)) : E ⊂ ⋃ Q_p, and each Q_p is a dyadic square}`.
Modelling: `OuterMeasure.boundedBy (dyadicGaugeGM h)`: the infimum over the countable covers of `E` by dyadic squares
(every family of dyadic squares is countable, and repeated members never lower the infimum) of `Σ h(ℓ(Q_p))`. -/
def dyadicContentGM (h : ℝ → ℝ) : OuterMeasure ℂ :=
  OuterMeasure.boundedBy (dyadicGaugeGM h)

/-- **Formula (D.6)** (App. D, P3:3285–3291; cited in the proof of Theorem D.1, P3:3349, 3369). Every dyadic square
of side `r` is contained in a ball of radius `r`, while each ball of radius `r` is contained in 25 dyadic squares `Q`
with `r/2 < ℓ(Q) ≤ r`. Therefore (D.6) `M_h(E) ≤ m_h(E) ≤ 25 M_h(E)`.
Modelling: `h` is a measure function (the monotonicity gives `h(ℓ(Q)) ≤ h(r)` in the second step); `E` is any set;
the two covering facts are the book's proof and are not stated. The constant `25` was checked against the equation
image. -/
theorem eqD_6 {h : ℝ → ℝ} (hh : IsMeasureFunction h) (E : Set ℂ) :
    hausdorffContentGM h E ≤ dyadicContentGM h E ∧ dyadicContentGM h E ≤ 25 * hausdorffContentGM h E := by
  sorry

/-- **Theorem D.1** (Frostman; App. D, P3:3301–3318; cited in the proofs of Corollaries D.2 and D.3, P3:3389, 3417,
and in Ch. X, Exercise 8, P3:2085, "Frostman's Theorem D.1"), first part. Let `h` be a measure function. If `μ` is a
positive measure such that (D.7) `μ(B(z, r)) ≤ h(r)` for all `z` and `r`, then `μ(E) ≤ Λ_h(E)` for every Borel set
`E`.
Modelling: "positive measure" is a `Measure ℂ` (a Borel measure); "for all `z` and `r`" is all `z ∈ ℂ` and `r > 0`
(the disc of radius `0` is empty); the comparison is in `[0, ∞]`. (D.7) and the conclusion were checked against the
equation images. -/
theorem thmD_1_a {h : ℝ → ℝ} (hh : IsMeasureFunction h) (μ : Measure ℂ)
    (hμ : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (h r)) {E : Set ℂ} (hE : MeasurableSet E) :
    μ E ≤ hausdorffMeasureGM h E := by
  sorry

/-- **Theorem D.1** (Frostman; App. D, P3:3301–3318), second part. Let `h` be a measure function. Conversely, if `E`
is a compact set, and if `M_h(E) > 0`, then there exists a positive measure `μ`, supported on `E`, such that (D.7)
holds for all `z` and `r` and such that (D.8) `μ(E) ≥ M_h(E)/225`.
Modelling: "positive measure" is a `Measure ℂ`; "supported on `E`" is `μ(ℂ \ E) = 0` (`E` is compact, hence closed);
(D.7) for all `z ∈ ℂ` and `r > 0`; (D.8) in `[0, ∞]` (`M_h(E)` is finite, `E` being bounded). The finiteness of `μ`
is not asserted separately: it follows from (D.7) for one disc containing `E`. The constant `225` was checked against
the equation image. Notes on the proof: "we obtain (D.6) for the new measure `μ/225`" (P3:3349) means (D.7)
[misprint]; in `μ(E) = lim μ_n^{(0)}(E) ≥ m_h(E) ≥ M_h(E)` (P3:3371, checked against the equation image) the masses
are read as total masses (`μ_n^{(0)}` is spread over squares and may give `E` itself mass `0`). -/
theorem thmD_1_b {h : ℝ → ℝ} (hh : IsMeasureFunction h) {E : Set ℂ} (hE : IsCompact E)
    (hM : 0 < hausdorffContentGM h E) :
    ∃ μ : Measure ℂ, μ Eᶜ = 0 ∧ (∀ z : ℂ, ∀ r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (h r)) ∧
      hausdorffContentGM h E / 225 ≤ μ E := by
  sorry

/-- **Corollary D.2** (App. D, P3:3377–3407; cited at P3:3409, 3433, in Exercise D.2, P3:3649 (printed "Corollary
A.2" [misprint]) and P3:3659, and in the proof of Theorem IX.3.1, P2:6901, "By (3.1) and (D.11) from Appendix D").
Let `h` be a measure function such that (D.10) `∫₀¹ h(r)/r dr < ∞`. If `E` is a compact set such that
`Λ_h(E) > 0`, then (D.11) `Cap(E) ≥ diam(E) exp(−(225/M_h(E)) ∫₀^{diam(E)} h(r)/r dr)`.
Modelling: `Cap` is `capacity` (III.4.8) (for compact `E` the capacity (III.1.3)); the right side is a real number,
compared with `Cap(E) ∈ [0, ∞]` through `ENNReal.ofReal`. (D.10) is the lower integral `∫⁻` of `h(r)/r` over
`(0, 1]` (no junk: `h ≥ 0`); it makes `∫₀^{diam(E)} h(r)/r dr` a convergent integral (`h` is continuous), and it forces
`h(0) = 0`, so that `Λ_h(E) > 0` forces `diam(E) > 0`. `M_h(E)` is finite (`E` is bounded) and positive (from
`Λ_h(E) > 0` by (D.4), the book's own step), so its real value `(M_h(E)).toReal` is the book's number and `225/M_h(E)`
reads no junk. [OCR] "measurefunction", "supported on `E_{:}`", "m `r(r)`" (P3:3377, 3389) are "measure function",
"supported on `E`", "`m(r)`"; "a compact set such that if `Λ_h(E) > 0`" is read "such that `Λ_h(E) > 0`" [reading].
(D.10) and (D.11) (the constant `225`, the upper limit `diam(E)`) were checked against the equation images. -/
theorem corD_2 {h : ℝ → ℝ} (hh : IsMeasureFunction h)
    (h10 : ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (h r / r) < ⊤) {E : Set ℂ} (hE : IsCompact E)
    (hΛ : 0 < hausdorffMeasureGM h E) :
    ENNReal.ofReal (Metric.diam E *
        Real.exp (-(225 / (hausdorffContentGM h E).toReal) * ∫ r in (0 : ℝ)..Metric.diam E, h r / r)) ≤
      capacity E := by
  sorry

/-- **Corollary D.3** (App. D, P3:3411–3423; cited in Ch. III, P1:4556, "See Corollary 7.4 and Corollary D.3 of
Appendix D for other proofs that every point of the Cantor set K is regular", and in Ch. VIII, Exercise 5, P2:5321).
If `0 < α ≤ 2`, there is a constant `C = C_α > 0` such that if `E` is compact then (D.12)
`Cap(E) ≥ C (M_{r^α}(E))^{1/α}`.
Modelling: the quantifiers are `∀ α, ∃ C > 0, ∀ E` (the constant depends only on `α`); `Cap` is `capacity`
(III.4.8); `M_{r^α}` is `hausdorffContentGM (fun r => r ^ α)`, finite for compact `E`, and the power `1/α` is taken
in `[0, ∞]`. The range `α ≤ 2` is kept as printed (for `α > 2`, `M_{r^α}` vanishes on bounded sets, which explains the
book's range). [OCR] "H 0 < α ≤ 2" (P3:3411) is "If `0 < α ≤ 2`". Note on the proof (P3:3423): "`γ(E) ≤ 225α`" and
"`C_α ≥ e^{−225α}`" should be `225/α` and `e^{−225/α}` [misprint?] (the display before them gives
`U_μ(z) ≤ ∫₀¹ r^{α−1} dr = 1/α`, checked against the equation image); the statement only asserts some `C_α > 0` and
is unaffected. (D.12) was checked against the equation image. -/
theorem corD_3 {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set ℂ, IsCompact E →
      ENNReal.ofReal C * hausdorffContentGM (fun r => r ^ α) E ^ (1 / α) ≤ capacity E := by
  sorry

/-- **Theorem D.4** (Erdős and Gillis [1937], attributed at P3:3433; App. D, P3:3425–3465). Let (D.13)
`h(r) = (log 1/r)^{−1}`. If `Cap(E) > 0`, then `Λ_h(E) = ∞`.
Modelling: `E` is a Borel set, the sets for which (III.4.8) defines `Cap` (the proof's compact `J ⊂ E` and the
equilibrium distribution `μ_E` are proof-internal); `Cap` is `capacity`. The gauge is (D.13) as it stands,
`fun r => (Real.log (1 / r))⁻¹`: it is a measure function only on `(0, 1)` (positive, continuous, increasing, with
limit `0` at `0⁺`); in Lean its value is `0` at `r = 1` (`(log 1)⁻¹ = 0⁻¹ = 0`) and negative for `r > 1` (charged `0`
by `ENNReal.ofReal`), but these values never enter `Λ_h`, which reads only the germ of `h` at `0⁺`: the covers use
discs of radii `≤ δ → 0`, and `mkMetric'.pre` is antitone in the diameter bound, so the supremum defining
`hausdorffMeasureGM` is the limit over small bounds (the same reading as for the gauges given near `0` only in VIII
§2 and App. K, leader ruling D6). (D.13) was checked against the equation image. Notes on the proof: "`≤ M ≤ ∞`"
(P3:3450, checked against the equation image) means `M < ∞` [misprint]; Egoroff's theorem (P3:3441) is Mathlib's
`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`. -/
theorem thmD_4 {E : Set ℂ} (hE : MeasurableSet E) (hcap : 0 < capacity E) :
    hausdorffMeasureGM (fun r => (Real.log (1 / r))⁻¹) E = ⊤ := by
  sorry

end GarnettMarshall2005
