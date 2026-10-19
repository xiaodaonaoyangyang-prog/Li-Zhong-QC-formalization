import References.Pommerenke1992.Ch10.S02_HausdorffMeasures

/-!
# Pommerenke 1992, Ch. 10 §10.3 Lower Bounds for Compression

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 10 *Hausdorff Measure*, §10.3; source `full.md`
of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 1996–2314.

* Definition (the gauge `φ` of (10.3.1), in Theorem 10.6, l. 2003; cited "(1)" at l. 2020, 2080, 2088) —
  `makarovPhi`
* Theorem 10.6 (Mak85; (10.3.2); cited at P1 l. 5428 and P2 l. 1705, 2022, 2128, 2331) — `thm10_6`
* Lemma 10.7 ((10.3.4); cited twice at l. 2080) — `lemma10_7`
* Definition (`β_f(-q)`, (10.3.9), "as in (8.3.1)", l. 2090–2094; cited "(9)" at l. 2213) — exists:
  `Pommerenke1992.integralMeansSpectrum` `Pommerenke1992.eq8_3_2` (β_f at the exponent −q; the infimum of the β with
  the O-bound (10.3.9) is the second conjunct of the Part C formula (8.3.2))
* Theorem 10.8 (Mak87; (10.3.10); cited at l. 1705, 2102, 2136, 2138, 2144) — `thm10_8`
* Theorem 10.9 (Mak87; (10.3.11), (10.3.12); cited at l. 2122, 2128, 2130, 2136) — `thm10_9_a`, `thm10_9_b`,
  `thm10_9_c`, `thm10_9_d`
* Formula (10.3.13) (§10.3, P2 l. 2122–2126, U+: "Taking the limit `α → 1` in (11)"; = (10.1.5), the second half of
  the Makarov Dimension Theorem of §10.1; index "Makarov dimension theorem … 231") — `eq10_3_13`
* Definition (`d_f(z) = dist(f(z), ∂G)`, l. 2144; used in Proposition 10.10 and in the proof of Theorem 10.17) —
  exists: `Pommerenke1992.distToBoundary` ((1.3.16), the same function)
* Definition (the dyadic points (10.3.14) and the corresponding dyadic arcs `I(z)`, "see (6.5.15)", l. 2144–2150;
  cited "(14)" at l. 2207) — exists: `Pommerenke1992.dyadicPoint` `Pommerenke1992.arcI` (the Part C formula (6.5.14),
  the same points for n ≥ 1, 1 ≤ ν ≤ 2^n; the dyadic arc of the dyadic point z is the arc (5.2.4) of z)
* Proposition 10.10 (Mak87; (10.3.15)–(10.3.17); cited at l. 2227 and in Exercise 10.3.4) — `prop10_10`
* Theorem 10.11 (Mak89b; (10.3.23); cited at P2 l. 1479, 1713, 2435) — `thm10_11`

Not items (DESIGN §3): the recall of Corollary 6.26 and the tacit assumption that "the angular limit `f(ζ)` exists and
is finite for `ζ ∈ A`", "true except possibly for a set of zero capacity (Theorem 9.19)" (l. 1998; the standing
assumption, made explicit, see below); (10.3.3) `α < 1`, `Λ(A) > 0 ⟹ Λ_α(f(A)) > 0` with its history (Beurling,
Mat64, Car73, Mak89d; l. 2012–2018; U−: immediate from Theorem 10.6 and the first assertion of Proposition 10.2, since
`φ(t) ≤ t^α` near `0`, and not cited by number); the sharpness remark (Mak85: the map (8.6.6) and the law of the
iterated logarithm (8.6.22) give `A` with `Λ(A) = 2π` and `Λ_{φ₁}(f(A)) = 0`; PrUrZd89, Mak89d; l. 2020; quoted, not
cited); the proofs of Lemma 10.7 and Theorem 10.6 ((10.3.5)–(10.3.8), l. 2032–2086; they use (1.3.18) and
Corollary 8.11); the Remark (Mak89c) on non-Smirnov domains and the singular measure of (7.3.1) (l. 2088; quoted, not
cited); "(13) is stronger than (2) … but is also weaker", "(11) is not sharp" and the derivations of (11) from (10)
and Theorem 8.5 (`β_f(−q) < 3q²`, `q = √((1 − α)/3)`) and of (12) from Theorem 8.4 (`β_f(−1) = 0`) (l. 2128–2136;
remarks that are the proof of Theorem 10.9 (b), (c); re-derived: exact); "`dim f(A) ≥ α/2` is not difficult to
establish (Mat64, see Exercise 4)", Carleson's method and the consequence `dim f(A) ≥ 2α/(4 − α)` of the Brennan
conjecture (l. 2138–2142; an exercise and a consequence of a conjecture); the proofs of Proposition 10.10 and
Theorem 10.8 ((10.3.18)–(10.3.22), Fig. 10.2, l. 2170–2257; they use Proposition 2.13, Theorem 9.24, Theorem 10.3,
the Gehring–Hayman theorem (4.5.6) and Corollaries 1.5, 1.6); (10.3.24) (Ham88, = (10.1.6); l. 2269–2275; U−:
Theorem 10.11 with `φ(t) = t^α` and (10.2.7), after composing with a disc automorphism sending `f(0)` to `0`, which is
bi-Lipschitz on `𝕋` and leaves dimensions unchanged; not cited by number); the proof of Theorem 10.11 (l. 2277–2289;
Theorems 10.3 and 9.21); Exercises 10.3.1–10.3.6 (Exercise 10.3.4 is cited at l. 2138).

**Conventions.** As in §10.2. The standing assumption of §10.3 (P2 l. 1998) is explicit in every statement that uses
`f(ζ)`: a witness `F` with `HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)` for `ζ ∈ A`, and `f(A) = F '' A`.
"`K₁, K₂, …` suitable absolute constants" (l. 2022, 2144) are `∃ K, ∀ f …`. `Λ_φ` for the gauge (10.3.1) is
`hausdorffMeasureGauge φ` for every gauge `φ` with `φ =ᶠ[𝓝[>] 0] makarovPhi` (Q10.8).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane unitDisc IsConformalOnto)

/-- **Definition (10.3.1)** (§10.3, in Theorem 10.6; P2 l. 2003; cited "(1)" at P2 l. 2020, 2080 and 2088, "the
measure `Λ_φ` defined by (1)"). `φ(t) = t exp(30 √(log(1/t) · log log log(1/t)))` for `0 < t ≤ exp(−e^e)`.
Modelling: the book's formula as a real function; the book defines it for `0 < t ≤ exp(−e^e)`, where every logarithm
is positive, and its values elsewhere are junk that no statement sees: statements use `makarovPhi` only through
gauges equal to it on some interval `(0, t₀)`. The printed `φ` is not increasing on its whole printed interval: with
`L = log(1/t)`, `d log φ/dL = −1 + 15(log log L + 1/log L)/√(L log log L)` is positive for `L` below about `486`, so
`φ` decreases in `t` on about `e^{−486} < t ≤ e^{−e^e}` (Q10.8). It is positive, continuous and increasing near `0`
with limit `0`, and only its germ at `0` matters (P2 l. 1751); the crop of (10.3.1) was checked. -/
def makarovPhi (t : ℝ) : ℝ :=
  t * Real.exp (30 * Real.sqrt (Real.log (1 / t) * Real.log (Real.log (Real.log (1 / t)))))

/-- **Theorem 10.6** (§10.3; Mak85; (10.3.2); P2 l. 2000–2010; cited at P1 l. 5428 and P2 l. 1705, 2022, 2128 and
2331; proved at l. 2048–2086). Let `φ` be given by (10.3.1). If `f` maps `𝔻` conformally into `ℂ` then, for all
Borel sets `A ⊂ 𝕋`, (2) `Λ(A) > 0 ⟹ Λ_φ(f(A)) > 0`.
Modelling: `Λ_φ` is `hausdorffMeasureGauge φ` for any gauge `φ` equal to `makarovPhi` on some `(0, t₀)` (Q10.8;
such gauges exist, and all of them give the same `Λ_φ` by `MeasureTheory.Measure.mkMetric_mono`); `Λ(A)` is
`circleMeasure A`; the angular limits `f(ζ)`, `ζ ∈ A`, are the witness `F` of the standing assumption (P2 l. 1998),
and `f(A) = F '' A`. -/
theorem thm10_6 {φ : ℝ → ℝ} (hφ : IsHausdorffGauge φ) (hφM : φ =ᶠ[𝓝[>] 0] makarovPhi) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {A : Set ℂ} (hAm : MeasurableSet A)
    (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ} (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ))
    (hA : 0 < circleMeasure A) :
    0 < hausdorffMeasureGauge φ (F '' A) := by
  sorry

/-- **Lemma 10.7** (§10.3; P2 l. 2022–2030; cited twice at P2 l. 2080, in the proof of Theorem 10.6). Let
`0 < δ < ε`, `1/2 ≤ r < 1` and `A ⊂ 𝕋`. If `diam f(A) ≤ ε` and (4) `|f(rζ) − f(ζ)| ≤ ε`, `(1 − r)|f'(rζ)| ≥ δ`
for `ζ ∈ A`, then `A` can be covered by at most `K₁(ε/δ)²` sets of diameter at most `1 − r`.
Modelling: `f` maps `𝔻` conformally into `ℂ` (the setting of Theorem 10.6, l. 2022); `K₁` is absolute
(`∃ K₁, ∀ f δ ε r A`, l. 2022); `f(ζ)` is the witness `F` of the standing assumption; the covering sets are a finite
family `C : Fin n → Set ℂ` with `n ≤ K₁(ε/δ)²`; diameters are `Metric.ediam` in `[0, ∞]`, so an unbounded set never
has "diameter at most `1 − r`" (no `Metric.diam` junk). -/
theorem lemma10_7 :
    ∃ K₁ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ δ ε r : ℝ, 0 < δ → δ < ε → 1 / 2 ≤ r → r < 1 → ∀ A : Set ℂ, A ⊆ sphere 0 1 →
      ∀ F : ℂ → ℂ, (∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) →
        ediam (F '' A) ≤ ENNReal.ofReal ε →
        (∀ ζ ∈ A, ‖f (r * ζ) - F ζ‖ ≤ ε ∧ δ ≤ (1 - r) * ‖deriv f (r * ζ)‖) →
          ∃ (n : ℕ) (C : Fin n → Set ℂ), (n : ℝ) ≤ K₁ * (ε / δ) ^ 2 ∧ A ⊆ ⋃ i, C i ∧
            ∀ i, ediam (C i) ≤ ENNReal.ofReal (1 - r) := by
  sorry

/-- **Theorem 10.8** (§10.3; Mak87; (10.3.10); P2 l. 2096–2100; cited at P2 l. 1705, 2102, 2136, 2138 and 2144;
proved at l. 2201–2257). Let `f` map `𝔻` conformally into `ℂ`. If `A` is a Borel set on `𝕋`, then (10)
`dim f(A) ≥ q dim A/(β_f(−q) + q + 1 − dim A)` for `q > 0`.
Modelling: `β_f(−q)` is `integralMeansSpectrum f (−q)` (in `EReal`), and the bound is stated for every real
`β ≥ β_f(−q)` (Q10.11); this is equivalent, since `β_f(−q)` is finite (Proposition 8.3) and the right side is
continuous and decreasing in `β`. The denominator is at least `q > 0`: `dim A ≤ 1`, and `β ≥ β_f(−q) ≥ 0` (the
integral means of the subharmonic function `|f'|^{−q}` increase with `r`), so no division junk is seen. `dim A` is
`(dimH A).toReal` (finite, `≤ 1`); `f(A)` is `F '' A` for the witness `F` of the standing assumption. -/
theorem thm10_8 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {A : Set ℂ}
    (hAm : MeasurableSet A) (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) {q : ℝ} (hq : 0 < q) {β : ℝ}
    (hβ : integralMeansSpectrum f (-q) ≤ (β : EReal)) :
    ENNReal.ofReal (q * (dimH A).toReal / (β + q + 1 - (dimH A).toReal)) ≤ dimH (F '' A) := by
  sorry

/-- **Theorem 10.9** (§10.3; Mak87; (10.3.11); P2 l. 2104–2112; cited at P2 l. 2122, 2128, 2130, 2136; with (10.3.13)
the Makarov Dimension Theorem of §10.1), first part. Let `f` map `𝔻` conformally into `ℂ`. Let `A ⊂ 𝕋` be a Borel
set and `α = dim A`. Then (11) `dim f(A) > α/2` for `0 < α ≤ 11/12`.
Modelling: `α` is a real number with `dim A = α`; `f(A)` is `F '' A` for the witness `F` of the standing
assumption. -/
theorem thm10_9_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {A : Set ℂ}
    (hAm : MeasurableSet A) (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) {α : ℝ}
    (hαA : dimH A = ENNReal.ofReal α) (hα0 : 0 < α) (hα1 : α ≤ 11 / 12) :
    ENNReal.ofReal (α / 2) < dimH (F '' A) := by
  sorry

/-- **Theorem 10.9** (§10.3; (10.3.11), second display; P2 l. 2110–2112; its derivation from (10.3.10) and
Theorem 8.5 is given at l. 2130–2136), second part. In the setting of `thm10_9_a`,
`dim f(A) > α/(1 + √(12(1 − α)))` for `11/12 < α < 1`.
Modelling: as in `thm10_9_a`; `12(1 − α) > 0`, so `Real.sqrt` sees no junk. The display carries no tag of its own;
"(11)" covers both ranges of `α`. -/
theorem thm10_9_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {A : Set ℂ}
    (hAm : MeasurableSet A) (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) {α : ℝ}
    (hαA : dimH A = ENNReal.ofReal α) (hα1 : 11 / 12 < α) (hα2 : α < 1) :
    ENNReal.ofReal (α / (1 + Real.sqrt (12 * (1 - α)))) < dimH (F '' A) := by
  sorry

/-- **Theorem 10.9** (§10.3; (10.3.12); P2 l. 2114–2118; derived from (10.3.10) and Theorem 8.4 at l. 2136), third
part. If `f` is close-to-convex then (12) `dim f(A) ≥ α/(2 − α)` for `0 < α ≤ 1`.
Modelling: close-to-convex is `IsCloseToConvex` ((3.6.14)); such an `f` is univalent (Proposition 3.20), hence a
conformal map of `𝔻` into `ℂ` as the theorem assumes (the form of `thm8_4_b`); `A`, `α`, `F` as in `thm10_9_a`. -/
theorem thm10_9_c {f : ℂ → ℂ} (hf : IsCloseToConvex f) {A : Set ℂ} (hAm : MeasurableSet A)
    (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ} (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ))
    {α : ℝ} (hαA : dimH A = ENNReal.ofReal α) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (α / (2 - α)) ≤ dimH (F '' A) := by
  sorry

/-- **Theorem 10.9** (§10.3; P2 l. 2120, "and this estimate is best possible"; the construction of a starlike
function for which (12) is sharp is referred to Mak87, p. 63, at l. 2136), fourth part. The estimate (12) is best
possible.
Modelling (Q10.12, the weakest faithful reading; the Part A precedent of Becker's Theorem 1.11 (b)): for every
`0 < α ≤ 1` and every `c > α/(2 − α)` there are a close-to-convex `f` and a Borel set `A ⊂ 𝕋` with `dim A = α`, at
whose points the angular limits `f(ζ)` exist, such that `dim f(A) < c`. The book does not say whether one function
serves all `α`. -/
theorem thm10_9_d {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {c : ℝ} (hc : α / (2 - α) < c) :
    ∃ f : ℂ → ℂ, IsCloseToConvex f ∧ ∃ A : Set ℂ, MeasurableSet A ∧ A ⊆ sphere 0 1 ∧
      dimH A = ENNReal.ofReal α ∧ ∃ F : ℂ → ℂ, (∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) ∧
        dimH (F '' A) < ENNReal.ofReal c := by
  sorry

/-- **Formula (10.3.13)** (§10.3; P2 l. 2122–2126; = (10.1.5), the second half of the Makarov Dimension Theorem of
§10.1; index "Makarov dimension theorem … 231"). Taking the limit `α → 1` in (11) we obtain that, for all conformal
maps, (13) `dim A = 1 ⟹ dim f(A) ≥ 1`.
Modelling: `f` maps `𝔻` conformally into `ℂ` and `A` is a Borel set on `𝕋`, as in Theorem 10.9; `f(A)` is `F '' A`
for the witness `F` of the standing assumption. It is an item (U+, Q10.6): it is not immediate from (10.3.11), which
needs `α < 1`; one passes to Borel subsets of dimension `< 1`. -/
theorem eq10_3_13 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {A : Set ℂ}
    (hAm : MeasurableSet A) (hAT : A ⊆ sphere 0 1) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) (hA1 : dimH A = 1) :
    1 ≤ dimH (F '' A) := by
  sorry

/-- **Proposition 10.10** (§10.3; Mak87; (10.3.15)–(10.3.17); P2 l. 2152–2168; cited in the proof of Theorem 10.8,
l. 2227, and in Exercise 10.3.4). Let `f` map `𝔻` conformally onto `G` and let `0 < α ≤ 1`. If `A ⊂ 𝕋` is a Borel set
with (15) `diam f(A) ≤ ε < min(α, d_f(0))/4`, then there are dyadic points `z₁, …, z_N` with (16)
`N ≤ (K₁/α) log(1/ε)`, `d_f(z_j) ≤ K₂ ε` (`j = 1, …, N`), and a set `E ⊂ 𝕋` with `Λ′_α(E) < ε²` such that (17)
`A ⊂ E ∪ I(z₁) ∪ … ∪ I(z_N)`.
Modelling: `K₁, K₂` are absolute (l. 2144: `∃ K₁ K₂, ∀ f G α A ε`); `ε > 0` is implicit in `log(1/ε)` and in
`Λ′_α(E) < ε²` (and `ε < 1/4` follows from (15)); the dyadic points are `dyadicPoint n ν` (`n ≥ 1`, `1 ≤ ν ≤ 2ⁿ`),
given by their indices `p j = (n, ν)`, and `I(z)` is `arcI z`; `d_f` is `distToBoundary f`; `f(A)` is `F '' A` for
the witness `F` of the standing assumption, with its diameter `Metric.ediam`; `Λ′_α` is
`hausdorffContent (fun t => t ^ α)`, Pommerenke's own normalization (`(diam B_k)^α`, no factor), on which the stated
bound `ε²` depends (QD3). -/
theorem prop10_10 :
    ∃ K₁ K₂ : ℝ, ∀ (f : ℂ → ℂ) (G : Set ℂ), IsConformalOnto f unitDisc G →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ A : Set ℂ, MeasurableSet A → A ⊆ sphere 0 1 →
      ∀ F : ℂ → ℂ, (∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) →
      ∀ ε : ℝ, 0 < ε → ediam (F '' A) ≤ ENNReal.ofReal ε → ε < min α (distToBoundary f 0) / 4 →
        ∃ (N : ℕ) (p : Fin N → ℕ × ℕ), (∀ j, 1 ≤ (p j).1 ∧ 1 ≤ (p j).2 ∧ (p j).2 ≤ 2 ^ (p j).1) ∧
          (N : ℝ) ≤ K₁ / α * Real.log (1 / ε) ∧
          (∀ j, distToBoundary f (dyadicPoint (p j).1 (p j).2) ≤ K₂ * ε) ∧
          ∃ E ⊆ sphere (0 : ℂ) 1, hausdorffContent (fun t => t ^ α) E < ENNReal.ofReal (ε ^ 2) ∧
            A ⊆ E ∪ ⋃ j, arcI (dyadicPoint (p j).1 (p j).2) := by
  sorry

/-- **Theorem 10.11** (§10.3; Mak89b; (10.3.23); P2 l. 2259–2267; cited at P2 l. 1479, §9.5, "See Ham88 and
Theorem 10.11 for generalizations", l. 1713, and in the proof of Theorem 10.14, l. 2435). Suppose that
`φ(xt) ≤ M x^α φ(t)` (`0 < x ≤ 2`, `t > 0`) where `α > 0`. If `f` maps `𝔻` conformally into `𝔻` with `f(0) = 0` and
if `A ⊂ 𝕋` is a Borel set such that `f(A) ⊂ 𝕋`, then (23) `Λ′_φ(f(A)) ≥ c Λ′_φ(A)`, where `c` is a positive
constant.
Modelling: `φ` is a gauge (the §10.2 standing assumption); `c > 0` depends on `φ` (the proof takes it from
Theorem 10.3, so through `α` and `M`) but not on `f` or `A` (`∀ φ, (8) → ∃ c > 0, ∀ f A`, Q10.3(d)); the boundary
values `f(ζ)` on `A` are the witness `F` of the standing assumption (the hypothesis `f(A) ⊂ 𝕋` presupposes them, as
in Theorem 9.21). -/
theorem thm10_11 {φ : ℝ → ℝ} (hφ : IsHausdorffGauge φ) {α M : ℝ} (hα : 0 < α)
    (h8 : ∀ x t : ℝ, 0 < x → x ≤ 2 → 0 < t → φ (x * t) ≤ M * x ^ α * φ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      MapsTo f unitDisc unitDisc → f 0 = 0 → ∀ A : Set ℂ, MeasurableSet A → A ⊆ sphere 0 1 →
      ∀ F : ℂ → ℂ, (∀ ζ ∈ A, HasAngularLimit (fun z => (f z : ExtPlane)) ζ (F ζ)) → F '' A ⊆ sphere 0 1 →
        ENNReal.ofReal c * hausdorffContent φ A ≤ hausdorffContent φ (F '' A) := by
  sorry

end Pommerenke1992
