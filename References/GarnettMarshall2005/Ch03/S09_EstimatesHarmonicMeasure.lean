import References.GarnettMarshall2005.Ch03.S08_PolarSetsHarmonicMeasureZero

/-!
# Garnett–Marshall, Chapter III §9: Estimates for harmonic measure

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §9 and the Notes
(pp. 104–112; `full.md` P1:4734–5089).

Conventions as in §5–§8. The section estimates `ω(z, E, 𝔻 \ E)` for a closed subset `E` of the unit disc (P1:4736),
and `ω(z, E, ℍ \ E)` for a compact `E ⊂ ℍ`. Reading of the standing assumption (inventory §B8, "E closed vs Borel"):
`E` is a closed subset of `ℂ` (`IsClosed E`) lying in the closed disc; this is the book's "closed subset of the unit
disc" for the sets of Theorem 9.1, which stay away from `∂𝔻`, and it lets the sets of Theorem 9.2 meet `∂𝔻`, as
`E ⊂ 𝔻̄ \ {0}` there allows; the book's further reduction "by (5.3) we may assume `∂E` consists of finitely many
analytic curves" is a method of proof, not a hypothesis. The harmonic measure `ω(z, E, D \ E)` of a closed set `E`
relative to `D \ E` (`D = 𝔻` or `ℍ`) is Wiener's harmonic measure of the component of `D \ E` containing `z`
(`harmonicMeasureOpen (toExt (D \ E)) z (toExt E)`, leader ruling B5); the harmonic measure `ω(z, ·, ℍ)` of the
half-plane itself is that of Chapter I §1 (`harmonicMeasureUHP`, a measure on `ℝ = ∂ℍ \ {∞}`). `γ(E) = −log Cap(E)`
is `robinConstant` (4.8), in `[−∞, +∞]`, and quotients by `γ` are taken in `[0, ∞]` (`EReal.toENNReal`; `x/∞ = 0` is
the book's convention for polar sets). The circular projection `E* = {|z| : z ∈ E}` is a subset of `ℝ`, seen in `ℂ`
through the coercion where it is a set of the plane. Absolute constants are `∃ C, ∀ E`.

* Theorem 9.1 (§9; (9.1)) — `thm3_9_1`
* Unlabelled (§9, P1:4771, in the proof of Theorem 9.1; cited as a result at P1:4890): formula (9.2) — `eq3_9_2`
* Theorem 9.2 (Beurling; the Beurling projection theorem, §9) — `thm3_9_2`
* Corollary 9.3 (§9) — `cor3_9_3`
* Definition (dyadic Carleson box `Q` in `ℍ`, its side `ℓ(Q)` and its top half `T(Q)`, §9, P1:4850–4856 and
  P1:4872) — `dyadicCarlesonBoxUHP`, `dyadicCarlesonTopUHP`
* Definition (the class `𝒜 = 𝒜_E` of positive measures on `E` satisfying (9.5) and (9.6), §9, P1:4862–4876) —
  `carlesonClassA`
* Theorem 9.4 (§9; (9.4), (9.7)) — `thm3_9_4`
* Hall's lemma (§9, P1:4892–4898, quoted from Hall [1937] with its name) — `hall_lemma`

Not stated (inventory U−): the reduction "by (5.3) we may assume `∂E ⊂ 𝔻` is compact and consists of finitely many
analytic curves" (P1:4736, a method); the Green's-theorem representation (9.3) (P1:4788–4792, a step of the proof of
Theorem 9.2); the remark that in the special case `z = 0`, `E ⊂ {|ζ| > 1/2}`, Beurling's projection theorem with a
larger constant follows from Theorem 9.4 (P1:4884–4890); the remark that a special case of Hall's lemma, with a
different constant, follows from Theorem 9.4 (P1:4898; Exercise 20); (9.8)–(9.12) and the Green potential `G_μ` on
`ℍ` (P1:4900–5042, the proof of Theorem 9.4); the closing remark on Green potentials on `𝔻`, (9.13), minimal Green
energy and the Green capacity `γ_G(E)` (P1:5044–5068; its proofs are Exercise 18, and these notions are used later only
inside proofs). The Notes (P1:5070–5088), with Wiener's original criterion (N.1) (proved in Exercise 9), are not items.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf unitDisc upperHalf)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)

/-- **Theorem 9.1** (Ch. III §9; cited in Exercise 17, P1:5591). Suppose `E ⊂ {z : 0 < δ < |z| < r < 1}` and set
`γ(E) = −log(Cap(E))`. Then there are constants `c₁(r)` and `c₂(δ, r)` such that
(9.1) `c₁(r)/γ(E) ≤ ω(0, E, 𝔻 \ E) ≤ c₂(δ, r)/γ(E)`.
Modelling: `E` closed (the standing assumption of §9, P1:4736), hence compact here; `γ(E)` is `robinConstant E` (4.8),
and `γ(E) ≥ log(1/r) > 0` since `Cap(E) ≤ r`, so the quotients, taken in `[0, ∞]`, have no zero denominator; a polar
`E` has `γ(E) = +∞`, and then all three terms are `0`; `ω(0, E, 𝔻 \ E)` is `harmonicMeasureOpen` of `𝔻 \ E` at `0`.
The quantifiers are `∀ r, ∃ c₁, ∀ δ, ∃ c₂, ∀ E` ("constants `c₁(r)` and `c₂(δ, r)`"), and the constants are positive
(the proof gives `c₁(r) = (log r)²/log(r + 1/r)`; a lower bound with `c₁ = 0` would say nothing; `0 < c₂` is
harmless, the upper bound being monotone in `c₂`). The formula was checked against the equation image. -/
theorem thm3_9_1 :
    ∀ r : ℝ, 0 < r → r < 1 → ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ E : Set ℂ, IsClosed E → E ⊆ {z | δ < ‖z‖ ∧ ‖z‖ < r} →
        ENNReal.ofReal c₁ / (robinConstant E).toENNReal ≤
            harmonicMeasureOpen (toExt (unitDisc \ E)) ((0 : ℂ) : ExtPlane) (toExt E) ∧
          harmonicMeasureOpen (toExt (unitDisc \ E)) ((0 : ℂ) : ExtPlane) (toExt E) ≤
            ENNReal.ofReal c₂ / (robinConstant E).toENNReal := by
  sorry

/-- **Unlabelled** (Ch. III §9, (9.2), P1:4762–4774, in the proof of Theorem 9.1; cited as a result at P1:4890,
"apply the right-hand inequality in (9.2) with `δ = 1 − ℓ(Q)` and `r = (1 + δ)/2`"). For
`E ⊂ {z : 0 < δ < |z| < r < 1}`,
(9.2) `log(1/r)/(γ(E) + log(1 + r²)) ≤ ω(0, E, 𝔻 \ E) ≤ log(1/δ)/(γ(E) + log(1 − r²))`, provided that
`γ(E) + log(1 − r²) > 0`.
Modelling: as in `thm3_9_1` (`E` closed, `γ = robinConstant`, `ω(0, E, 𝔻 \ E)` by `harmonicMeasureOpen`); the sums
`γ(E) + log(1 ± r²)` are taken in `[−∞, +∞]` and the quotients in `[0, ∞]`; under the proviso both denominators are
positive, and a polar `E` gives `0` on both sides. The constants were checked against the equation image. -/
theorem eq3_9_2 {δ r : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr : r < 1) {E : Set ℂ} (hE : IsClosed E)
    (hEsub : E ⊆ {z | δ < ‖z‖ ∧ ‖z‖ < r}) (hprov : 0 < robinConstant E + (Real.log (1 - r ^ 2) : EReal)) :
    ENNReal.ofReal (Real.log (1 / r)) / (robinConstant E + (Real.log (1 + r ^ 2) : EReal)).toENNReal ≤
        harmonicMeasureOpen (toExt (unitDisc \ E)) ((0 : ℂ) : ExtPlane) (toExt E) ∧
      harmonicMeasureOpen (toExt (unitDisc \ E)) ((0 : ℂ) : ExtPlane) (toExt E) ≤
        ENNReal.ofReal (Real.log (1 / δ)) / (robinConstant E + (Real.log (1 - r ^ 2) : EReal)).toENNReal := by
  sorry

/-- **Theorem 9.2** (Beurling; "the Beurling projection theorem", Ch. III §9; cited by name at P1:4884 and later at
P2:1136 (through "Corollary III.9.3"), P2:1187, 1374, 3319, 4128, 5591, P3:1416, 1833, 5810). If `E ⊂ 𝔻̄ \ {0}`, and
`E* = {|z| : z ∈ E}` is the circular projection of `E`, then `ω(z, E, 𝔻 \ E) ≥ ω(−|z|, E*, 𝔻 \ E*)`.
Modelling: `E` closed (the standing assumption of §9; `E` may meet `∂𝔻`), `z ∈ 𝔻 \ E`; `E* ⊆ (0, 1]` is the plane set
`Es` of real points (`hEs`), so `−|z| ∈ 𝔻 \ E*`; both harmonic measures are Wiener's, of the component containing the
point (`harmonicMeasureOpen`), compared in `[0, ∞]`. A relatively closed `E ⊂ 𝔻` reduces to compact `E` by
exhaustion (`E ∩ B̄(0, r)`, `r ↑ 1`). The formula was checked against the equation image. -/
theorem thm3_9_2 {E : Set ℂ} (hE : IsClosed E) (hEsub : E ⊆ closedBall 0 1 \ {0}) {Es : Set ℂ}
    (hEs : Es = ((↑) : ℝ → ℂ) '' ((fun w : ℂ => ‖w‖) '' E)) {z : ℂ} (hz : z ∈ unitDisc \ E) :
    harmonicMeasureOpen (toExt (unitDisc \ Es)) (((-‖z‖ : ℝ) : ℂ) : ExtPlane) (toExt Es) ≤
      harmonicMeasureOpen (toExt (unitDisc \ E)) (z : ExtPlane) (toExt E) := by
  sorry

/-- **Corollary 9.3** (Ch. III §9; cited at P2:1136, "By Beurling's projection theorem (see Corollary III.9.3)
`ω ≪ Λ_{1/2}`", where `Λ_{1/λ}` is printed [OCR]). Let `Ω` be a simply connected domain, let `z ∈ Ω` and let
`ζ ∈ ∂Ω`. Then for `r` sufficiently small, `ω(z, B(ζ, r) ∩ ∂Ω, Ω) ≤ C r^{1/2}`.
Modelling: `Ω` a simply connected domain of `ℂ*` (`LehtoVirtanen1973.IsSimplyConnectedDomain`); `Cap(ℂ* \ Ω) > 0` is
added (meaning): harmonic measure is defined only then (P1:4120), and for a simply connected domain this excludes only
`ℂ*` itself (no boundary) and `ℂ*` minus a point; `ζ` a finite point (the discs are euclidean); `C` and the threshold
`r₀` depend on `Ω`, `z` and `ζ` (the book's "for `r` sufficiently small" with an unspecified `C`; after the
normalization `ζ = 0`, `z = −1` the proof gives `C = 4/π`); `ω` is Wiener's harmonic measure, compared in `[0, ∞]`.
The exponent `1/2` was checked against the equation image. -/
theorem cor3_9_3 {Ω : Set ExtPlane} (hΩ : IsSimplyConnectedDomain Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {z : ExtPlane} (hz : z ∈ Ω) {ζ : ℂ} (hζ : (ζ : ExtPlane) ∈ frontier Ω) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      harmonicMeasureWiener Ω z (toExt (ball ζ r) ∩ frontier Ω) ≤ ENNReal.ofReal (C * r ^ (1 / 2 : ℝ)) := by
  sorry

/-- **Definition** (dyadic Carleson box in `ℍ`, Ch. III §9, P1:4850–4856). A dyadic Carleson box is a set of the form
`Q = {j 2^{−k} ≤ x ≤ (j + 1) 2^{−k}; 0 < y ≤ 2^{−k}}`, and `ℓ(Q) = 2^{−k}`.
Modelling: `j, k ∈ ℤ` (boxes of every dyadic size); the side `ℓ(Q)` is written `2^{−k}` in the statements. -/
def dyadicCarlesonBoxUHP (j k : ℤ) : Set ℂ :=
  {z | (j : ℝ) * (2 : ℝ) ^ (-k) ≤ z.re ∧ z.re ≤ ((j : ℝ) + 1) * (2 : ℝ) ^ (-k) ∧ 0 < z.im ∧ z.im ≤ (2 : ℝ) ^ (-k)}

/-- **Definition** (the top half of a dyadic Carleson box, Ch. III §9, P1:4872). The top half of the dyadic Carleson
box `Q` is `T(Q) = Q ∩ {y ≥ ℓ(Q)/2}`. -/
def dyadicCarlesonTopUHP (j k : ℤ) : Set ℂ :=
  dyadicCarlesonBoxUHP j k ∩ {z | (2 : ℝ) ^ (-k) / 2 ≤ z.im}

/-- **Definition** (the class `𝒜 = 𝒜_E`, Ch. III §9, P1:4862–4876). Let `𝒜 = 𝒜_E` be the set of positive measures
`σ` on `E` such that (i) `σ` is a Carleson measure with constant `1`, (9.5) `σ(Q) ≤ ℓ(Q)` for every dyadic Carleson box
`Q`, and (ii) the top half `T(Q)` of every dyadic Carleson box `Q` satisfies
(9.6) `σ(T(Q))/ℓ(Q) ≤ 1/(1 + γ(E ∩ T(Q)) − γ(T(Q))) = 1/(1 + log(Cap T(Q)/Cap(E ∩ T(Q))))`.
Modelling: Borel measures on `ℂ` with `σ(ℂ \ E) = 0`; (9.5) in `[0, ∞]`; (9.6) multiplied out,
`σ(T(Q)) · (1 + γ(E ∩ T(Q)) − γ(T(Q))) ≤ ℓ(Q)`, with `γ = robinConstant` (4.8) in `[−∞, +∞]`: `T(Q)` is a rectangle,
so `γ(T(Q))` is finite, and `γ(E ∩ T(Q)) ≥ γ(T(Q))`, so the factor lies in `[1, ∞]`; for polar `E ∩ T(Q)` it is `∞`,
and (9.6) forces `σ(T(Q)) = 0`, the book's `1/(1 + ∞) = 0`. The second expression of (9.6) is the same number by
`γ = −log Cap`. "Carleson measure" is Exercise I.19, an exercise, so (9.5) is written out (leader ruling Q8). The
formulas were checked against the equation images. -/
def carlesonClassA (E : Set ℂ) : Set (Measure ℂ) :=
  {σ | σ Eᶜ = 0 ∧ (∀ j k : ℤ, σ (dyadicCarlesonBoxUHP j k) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-k))) ∧
    ∀ j k : ℤ, σ (dyadicCarlesonTopUHP j k) *
        ((1 : EReal) + robinConstant (E ∩ dyadicCarlesonTopUHP j k) -
          robinConstant (dyadicCarlesonTopUHP j k)).toENNReal ≤ ENNReal.ofReal ((2 : ℝ) ^ (-k))}

/-- **Theorem 9.4** (Ch. III §9; from Carleson [1982], Notes P1:5086; cited at P1:4884, 4898, and in Exercise 20,
P1:5672). Fix `z₀ = i` and assume `E` is compact and (9.4) `E ⊂ {0 ≤ x ≤ 1, 0 < y ≤ 1/2}`. Then there are constants
`C₁` and `C₂` such that (9.7) `C₁ ω(i, E, ℍ \ E) ≤ sup {σ(E) : σ ∈ 𝒜_E} ≤ C₂ ω(i, E, ℍ \ E)`.
Modelling: absolute constants (`∃ C₁ C₂, ∀ E`), positive (a lower bound with `C₁ = 0` would say nothing; `0 < C₂` is
harmless, since the upper bound only becomes harder as `C₂` decreases);
`ω(i, E, ℍ \ E)` is Wiener's harmonic measure of the component of `ℍ \ E` containing `i` (`harmonicMeasureOpen`); the
supremum and the comparisons are in `[0, ∞]`. The formula was checked against the equation image. -/
theorem thm3_9_4 :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧ ∀ E : Set ℂ, IsCompact E →
      E ⊆ {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 1 / 2} →
        (C₁ : ℝ≥0∞) * harmonicMeasureOpen (toExt (upperHalf \ E)) ((I : ℂ) : ExtPlane) (toExt E) ≤
            (⨆ σ ∈ carlesonClassA E, σ E) ∧
          (⨆ σ ∈ carlesonClassA E, σ E) ≤
            (C₂ : ℝ≥0∞) * harmonicMeasureOpen (toExt (upperHalf \ E)) ((I : ℂ) : ExtPlane) (toExt E) := by
  sorry

/-- **Hall's lemma** (Ch. III §9, P1:4892–4898, quoted from Hall [1937] with its name; restated in Exercise 20,
P1:5663). When `E ⊂ ℍ` we still write `E* = {|z| : z ∈ E}` for the circular projection of `E`, and for `z = x + iy ∈ ℍ`
we define `z* = −|x| + iy`. The estimate `ω(z, E, ℍ \ E) ≥ (2/3) ω(z*, E*, ℍ)` is known as Hall's lemma.
Modelling: `E` compact (the hypothesis of Exercise 20, which restates the lemma; the main text does not say which sets
`E` are meant), `z ∈ ℍ \ E`; `z*` as printed in the main text (Exercise 20 writes `z* = −z̄`, which differs when
`Re z < 0`, and is then false: `E = [1, 2] + iε`, `z = −1 + i` give `ω(z, E, ℍ \ E) → 0.045`, while
`(2/3) ω(1 + i, [1, 2], ℍ) = 1/6`); `E* ⊆ (0, ∞)` is a subset of `ℝ ⊆ ∂ℍ` and `ω(z*, E*, ℍ)` is the harmonic measure of
`ℍ` of Chapter I §1 (`harmonicMeasureUHP`, a measure on `ℝ`: the half-plane is the explicit setting of Chapter I);
`ω(z, E, ℍ \ E)` is Wiener's, of the component of `ℍ \ E` containing `z` (`harmonicMeasureOpen`); compared in `[0, ∞]`.
The constant `2/3` was checked against the equation image. -/
theorem hall_lemma {E : Set ℂ} (hE : IsCompact E) (hEH : E ⊆ upperHalf) {z : ℂ} (hz : z ∈ upperHalf \ E) :
    ENNReal.ofReal (2 / 3) * harmonicMeasureUHP (((-|z.re| : ℝ) : ℂ) + (z.im : ℂ) * I) ((fun w : ℂ => ‖w‖) '' E) ≤
      harmonicMeasureOpen (toExt (upperHalf \ E)) (z : ExtPlane) (toExt E) := by
  sorry

end GarnettMarshall2005
