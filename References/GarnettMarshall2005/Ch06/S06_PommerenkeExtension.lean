import References.GarnettMarshall2005.Ch06.S05_CompressionExpansion

/-!
# Garnett–Marshall, Chapter VI §6: Pommerenke's extension

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §6 (pp. 216–222;
`full.md` of the second part, P2:1294–1531).

Conventions of the section, as modelled here (Chapter VI conventions, leader ruling C6; §4 for `G`, `B` and `K`).
`Ω ⊆ ℂ` is a plane simply connected domain (`Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`), `φ : 𝔻 → Ω` a conformal
map (`LiZhongQC.IsConformalOnto φ unitDisc Ω`); `G = angDerivSet φ`, `B = zeroLiminfSet φ`, and the set `K` of cone
points is `Pommerenke1992.triangleVertexSet (toExt Ω) (frontier Ω)` (§4); `φ(S)` is `bdryImage φ S` (§3). For a
general simply connected domain `ω` is Wiener's harmonic measure `ω(z, ·, Ω)`, pulled back to `ℂ` by `.comap (↑)` (the
point `∞` carries no harmonic measure), for every `z ∈ Ω` (the null sets do not depend on `z`); "`ω(X) = 1`" is stated
as "`ω(ℂ ∖ X) = 0`" (leader ruling C12(d): the sets are not shown to be Borel, and a measure is an outer measure on all
sets). For a Jordan curve `Γ` of `ℂ*` with complementary components `Ω₁`, `Ω₂`, `ω_j = ω(z_j, ·, Ω_j)` is the
Jordan-domain harmonic measure `harmonicMeasureJordan` (leader rulings B5, C6); the two components are two disjoint
Jordan domains of `ℂ*` with boundary `Γ`, and "Borel subset of `Γ`" is `MeasurableSet` in `ℂ*` (the Borel structure of
`References.Common.ExtPlaneBorel`). `Λ₁` is `μH[1]` (leader ruling C2), and `Tn(Γ)` is `tangentPoints Γ` (§4). `|E|`
refers to `arcMeasure`.

* Unlabelled (§6, P2:1296–1314): the recall of `G`, `B`, `K` and of "`G ∩ B = ∅`, `|G ∪ B| = 2π`, `φ(G) ⊂ K`" —
  omitted: a recall of Theorem 4.1 and of the claim `φ(G) ⊂ K` of §4 (thm6_4_1, bdryImage_angDerivSet_subset_conePoints)
* Theorem 6.1 (Pommerenke, §6; (6.1), (6.2)) — `thm6_6_1_a`, `thm6_6_1_b`
* Unlabelled (§6, P2:1394): "by McMillan's twist point theorem, `ω`-almost every `w ∈ S` is a twist point" — omitted: a
  remark combining Theorem 6.1 with the twist point theorem (App. I), not cited
* Corollary 6.2 (§6) — `cor6_6_2_a`, `cor6_6_2_b`
* Theorem 6.3 (§6) — `thm6_6_3` (B-cand. Pommerenke1992.thm6_30, the partition of the curve into the tangent points
  and two sets null for the harmonic measures of the two sides, with Pommerenke's boundary harmonic measure)
* Unlabelled (§6, P2:1422): the examples of Browder–Wermer, Gamelin–Garnett and McMillan–Piranian — omitted: quoted
  examples
* Unlabelled (§6, P2:1442–1469): (6.4), (6.5) and the Cauchy–Schwarz step of the proof of Theorem 6.3 — omitted:
  steps of a proof; (6.4) reappears only in the derivation of (6.6)
* Formula (6.6) (§6, P2:1490–1506; the geometric result that the proof of Theorem 6.3 yields; cited at P2:1508) —
  `eq6_6_6`
* Corollary 6.4 (§6; (6.7)) — `cor6_6_4`
* Unlabelled (§6, P2:1516): Carleson's conjecture and the result of Bishop and Jones — omitted: a conjecture and a
  quoted result
* Unlabelled (§6, P2:1518–1528): the set `E = φ(G₁) ∪ S₁ ∪ φ(G₂) ∪ S₂`, its decomposition and the table of measures
  (including `φ(G₁) ∩ φ(G₂) ⊂ Tn(Γ)`) — omitted: a summary of Theorems 6.1 and 6.3, not cited; the table's first row
  prints φ(G₁) ∩ φ(G₁) for φ(G₁) ∩ φ(G₂) [OCR]
* Unlabelled (§6, P2:1530): "Examples that limit these results can be found in Exercises 8, 9 and 10" — omitted: a
  pointer to exercises

Helper (not a book notion): `IsAdmissibleCircleArcs` (the arcs `J_j(t)` of the proof of Theorem 6.3, separating
`z_j` from a given set `A`: `A = Γ ∩ B(w, r)` in the corrected (6.6), `A = {w}` as printed in Corollary 6.4).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto IsJordanCurve)
open References (IsJordanDomainExt finitePart)
open Gehring1978 (IsHypSimplyConnectedExt)
open Pommerenke1992 (triangleVertexSet)

/-- **Theorem 6.1** (Pommerenke, Ch. VI §6), first part, (6.1) and (6.2) (cited at P2:941, 973, 1394, 1396, 1472,
1518, in Chapter X §9, P3:1228, "By Theorem VI.6.1 we already know", and in App. I, P3:4929). Let `Ω` be a simply
connected domain and let `φ : 𝔻 → Ω` [be a conformal map]. Then there is a subset `S ⊂ φ(B) ∖ K` such that
(6.1) `Λ₁(S) = 0` and (6.2) `ω(S ∪ φ(G)) = 1`. In particular, the set `P = φ(G) ∪ S` has σ-finite `Λ₁` measure and
`ω(P) = 1`.
Modelling: the book's "let `φ : 𝔻 → Ω`" is a conformal map [omission] (inventory C11(11)); `ω(X) = 1` is
`ω(ℂ ∖ X) = 0` (module docstring) for every `z ∈ Ω` with the same `S` (the null sets of `ω(z, ·, Ω)` do not depend
on `z`, by Harnack's inequality); the "in particular" speaks of the same `S` and is kept inside the existential
(`ω(P) = 1` is (6.2)); σ-finite `Λ₁` measure is `SigmaFinite (μH[1].restrict P)`. -/
theorem thm6_6_1_a {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) :
    ∃ S ⊆ bdryImage φ (zeroLiminfSet φ) \ triangleVertexSet (toExt Ω) (frontier Ω), μH[1] S = 0 ∧
      (∀ z ∈ Ω, (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane)
        (S ∪ bdryImage φ (angDerivSet φ))ᶜ = 0) ∧
      SigmaFinite ((μH[1] : Measure ℂ).restrict (bdryImage φ (angDerivSet φ) ∪ S)) := by
  sorry

/-- **Theorem 6.1** (Pommerenke, Ch. VI §6), second part. Consequently, `Λ₁(K ∖ φ(G)) = ω(K ∖ φ(G)) = 0`.
Modelling: as in `thm6_6_1_a`; `ω(K ∖ φ(G)) = 0` for every `z ∈ Ω`. -/
theorem thm6_6_1_b {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) :
    μH[1] (triangleVertexSet (toExt Ω) (frontier Ω) \ bdryImage φ (angDerivSet φ)) = 0 ∧
      ∀ z ∈ Ω, (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane)
        (triangleVertexSet (toExt Ω) (frontier Ω) \ bdryImage φ (angDerivSet φ)) = 0 := by
  sorry

/-- **Corollary 6.2** (Ch. VI §6), first part (cited in Chapter VIII, P2:3681, "the situation is explained by
Corollary VI.6.2"). Let `Ω` be a simply connected domain and let `S ⊂ ∂Ω` be the set given in Theorem 6.1. Then
`ω ≪ Λ₁ ⟺ ω(S) = 0 ⟺ |G| = 2π`.
Modelling: `G` and `S` refer to a conformal map `φ : 𝔻 → Ω`; "the set given in Theorem 6.1" is any set with the
properties of Theorem 6.1: `S ⊆ φ(B) ∖ K`, `Λ₁(S) = 0` and `ω(S ∪ φ(G)) = 1` (such a set is not unique); `ω` is
`ω(z, ·, Ω)` for a given `z ∈ Ω`, pulled back to `ℂ`; the chain of equivalences is `List.TFAE`. -/
theorem cor6_6_2_a {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) {S : Set ℂ}
    (hS : S ⊆ bdryImage φ (zeroLiminfSet φ) \ triangleVertexSet (toExt Ω) (frontier Ω)) (hS0 : μH[1] S = 0)
    (hS1 : ∀ z ∈ Ω, (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane)
      (S ∪ bdryImage φ (angDerivSet φ))ᶜ = 0) {z : ℂ} (hz : z ∈ Ω) :
    List.TFAE [(harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane) ≪ μH[1],
      (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane) S = 0,
      arcMeasure (angDerivSet φ) = ENNReal.ofReal (2 * π)] := by
  sorry

/-- **Corollary 6.2** (Ch. VI §6), second part. `ω ⊥ Λ₁ ⟺ |G| = 0`.
Modelling: as in `cor6_6_2_a`; this part does not involve `S`. -/
theorem cor6_6_2_b {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) {z : ℂ} (hz : z ∈ Ω) :
    (harmonicMeasureWiener (toExt Ω) (z : ExtPlane)).comap ((↑) : ℂ → ExtPlane) ⟂ₘ μH[1] ↔
      arcMeasure (angDerivSet φ) = 0 := by
  sorry

/-- **Theorem 6.3** (Ch. VI §6; cited at P2:1087 and in the table P2:1526). Suppose `Γ` is a Jordan curve, and let
`Ω₁` and `Ω₂` be the two components of the complement `ℂ* ∖ Γ`. Let `E` be a Borel subset of `Γ` such that
`ω(z_j, E, Ω_j) > 0` for `z_j ∈ Ω_j`, `j = 1, 2`, and let `ω_j|_E` be the restriction of `ω_j = ω(z_j, ·, Ω_j)` to
`E`. Then `ω₁|_E ⊥ ω₂|_E` if and only if `Λ₁(Tn(Γ) ∩ E) = 0`, where `Tn(Γ)` is the set of tangent points of `Γ`.
Modelling: the OCR prints `ω(z_j, E, Ω)`, read `Ω_j` [OCR] (inventory C11(5)); the components are two disjoint Jordan
domains of `ℂ*` with boundary `Γ` (module docstring); `z_j ∈ Ω_j` may be `∞`; `ω_j` is `harmonicMeasureJordan Ω_j z_j`,
a measure on `ℂ*`, restricted to `E`; `Λ₁(Tn(Γ) ∩ E)` measures the finite part of `E`. -/
theorem thm6_6_3 {Γ : Set ExtPlane} (hΓ : IsJordanCurve Γ) {Ω₁ Ω₂ : Set ExtPlane}
    (hΩ₁ : IsJordanDomainExt Ω₁ ∧ frontier Ω₁ = Γ) (hΩ₂ : IsJordanDomainExt Ω₂ ∧ frontier Ω₂ = Γ)
    (h12 : Disjoint Ω₁ Ω₂) {E : Set ExtPlane} (hEΓ : E ⊆ Γ) (hE : MeasurableSet E) {z₁ z₂ : ExtPlane}
    (hz₁ : z₁ ∈ Ω₁) (hz₂ : z₂ ∈ Ω₂) (hω₁ : 0 < harmonicMeasureJordan Ω₁ z₁ E)
    (hω₂ : 0 < harmonicMeasureJordan Ω₂ z₂ E) :
    (harmonicMeasureJordan Ω₁ z₁).restrict E ⟂ₘ (harmonicMeasureJordan Ω₂ z₂).restrict E ↔
      μH[1] (tangentPoints Γ ∩ finitePart E) = 0 := by
  sorry

/-- Admissible circle arcs (helper, Ch. VI §6, proof of Theorem 6.3, P2:1432–1436; used by (6.6) and Corollary 6.4).
At every `t ∈ T`, `J(t)` is an arc in `Ω ∩ {z : |z − w| = t}` that separates `z` from the set `A` in `Ω`, and its
length `ℓ(J(t))` is a measurable function of `t` on `T` (the hypothesis of Theorem IV.6.2, through which the proof
passes). The book's "let `J_j(t)` be any arc in `Ω_j ∩ {z : |z − w| = t}` such that `J_j` separates `z_j` from `w`"
is the case `A = {w}` (used by `cor6_6_4`); the corrected (6.6) uses `A = Γ ∩ B(w, r)` (`eq6_6_6`, [CORRECTION]).
Modelling: `Ω ⊆ ℂ*` and the arcs lie in its finite part; an arc is a Jordan arc (`LehtoVirtanen1973.IsJordanArc`, any
kind of parameter interval; kept as printed, since `cor6_6_4` quantifies over every choice of arcs); "separates" is
`IsSeparatingIn` (Ch. IV §1); the length is `μH[1]` (leader ruling C2). -/
def IsAdmissibleCircleArcs (Ω : Set ExtPlane) (z w : ℂ) (A : Set ℂ) (J : ℝ → Set ℂ) (T : Set ℝ) : Prop :=
  (∀ t ∈ T, J t ⊆ finitePart Ω ∩ sphere w t ∧ LehtoVirtanen1973.IsJordanArc (toExt (J t)) ∧
    IsSeparatingIn (finitePart Ω) (J t) {z} A) ∧
    AEMeasurable (fun t => μH[1] (J t)) (volume.restrict T)

/-- **Formula (6.6)** (Ch. VI §6, P2:1490–1506; "the proof of Theorem 6.3 yields a purely geometric result"; cited at
P2:1508 for Corollary 6.4). Let `Γ`, `Ω₁`, `Ω₂` be as in Theorem 6.3, with `z_j ∈ Ω_j`, `dist(z_j, Γ) ≥ 1`. Let
`w ∈ Γ`, take `θ_j(t)` as in that proof (`tθ_j(t) = ℓ(J_j(t))` for arcs `J_j(t)` of `Ω_j ∩ {|z − w| = t}` separating
`z_j` from `w`, `0 < t < 1`; corrected below), and set `ε(w, t) = max {|π − θ_j(t)| : j = 1, 2}`. Then
`(ω₁(B(w, r))/r)(ω₂(B(w, r))/r) ≤ (64/π²) exp(−(2/π²) ∫_r^1 ε²(w, t) dt/t)`.
Modelling: the normalization `dist(z_j, Γ) ≥ 1` of the proof ("We may assume") is a hypothesis, with `z_j` finite and
`dist` to the finite part of `Γ`; `w` is a finite point of `Γ` and `0 < r < 1`; `B(w, r)` is `ball w r`; the arcs are
any admissible choice on `(r, 1)` separating `z_j` from `Γ ∩ B(w, r)` (`IsAdmissibleCircleArcs` with
`A = finitePart Γ ∩ ball w r`, the corrected sense; the proof works for every choice, and `ε` depends on it);
`θ_j(t) = ℓ(J_j(t))/t` with `ℓ = μH[1]` finite (an arc of a circle of radius `t` has length `≤ 2πt`), so
`0 ≤ ε ≤ π` and the integrand is bounded and measurable on `[r, 1]`: the interval integral is a genuine integral,
not a junk value; `ω_j(B(w, r))` is
`harmonicMeasureJordan Ω_j z_j` of the disc, read as a real number since a quotient follows. The constant `64/π²`
and the exponent were checked against the equation image.
[CORRECTION] The book says "`J_j` separates `z_j` from `w`" (P2:1432). With that condition (6.6) is false. The
proof applies Theorem IV.6.2 (`thm4_6_2`, P1:6482), which needs `J` to separate `z_j` from the estimated set
`∂Ω_j ∩ B(w, r)`; so here `J(t)` separates `z_j` from `Γ ∩ B(w, r)` for each `t ∈ (r, 1)`, in the finite part.
With this separation the book's proof (Cauchy–Schwarz / Taylor with `θ₁ + θ₂ ≤ 2π`) gives (6.6).
Counterexample to the book's condition: take `w = 0`, `dist(z_j, Γ) ≥ 1`; near `0`, `Ω₁` is a thin wedge
`{|arg z − π/2| < δ}`, and `Ω₁` also has a fat lower region whose boundary piece `Γ′` is a segment of length about
`r` at distance `r/2` below `0`, not touching `0` (a thin `Ω₂` layer inside `B(0, r/2)` lies between `Γ′` and `0`);
`Ω₂` near `0` is the sector `S = {−π/4 < arg z < π/2 − δ}` joined to `z₂`, plus that layer. For `t ∈ (r, 1)` the
wedge arc `J₁(t)` (length `2δt`) separates `z₁` from `0` and the `S`-arc `J₂(t)` (length about `(3π/4 − δ)t`)
separates `z₂` from `0`, so `ε(0, t) = π − 2δ` and the right side of (6.6) is about `r^{2(1 − 2δ/π)²}`, nearly `r²`.
But `ω₁(B(0, r)) ≥ ω₁(Γ′) ≈ c·r` (`Γ′` is reached from `z₁` without crossing `J₁`) and, by domain monotonicity in
`S`, `ω₂(B(0, r)) ≳ r^{4/3}` (up to `δ`), so the left side is `≳ r^{1/3}` (up to `δ`), far above the right
side when `r` is small. -/
theorem eq6_6_6 {Γ : Set ExtPlane} (hΓ : IsJordanCurve Γ) {Ω₁ Ω₂ : Set ExtPlane}
    (hΩ₁ : IsJordanDomainExt Ω₁ ∧ frontier Ω₁ = Γ) (hΩ₂ : IsJordanDomainExt Ω₂ ∧ frontier Ω₂ = Γ)
    (h12 : Disjoint Ω₁ Ω₂) {z₁ z₂ : ℂ} (hz₁ : (z₁ : ExtPlane) ∈ Ω₁) (hz₂ : (z₂ : ExtPlane) ∈ Ω₂)
    (hd₁ : 1 ≤ infDist z₁ (finitePart Γ)) (hd₂ : 1 ≤ infDist z₂ (finitePart Γ)) {w : ℂ} (hw : (w : ExtPlane) ∈ Γ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {J₁ J₂ : ℝ → Set ℂ}
    (hJ₁ : IsAdmissibleCircleArcs Ω₁ z₁ w (finitePart Γ ∩ ball w r) J₁ (Ioo r 1))
    (hJ₂ : IsAdmissibleCircleArcs Ω₂ z₂ w (finitePart Γ ∩ ball w r) J₂ (Ioo r 1)) :
    (harmonicMeasureJordan Ω₁ (z₁ : ExtPlane) (toExt (ball w r))).toReal / r *
        ((harmonicMeasureJordan Ω₂ (z₂ : ExtPlane) (toExt (ball w r))).toReal / r) ≤
      64 / π ^ 2 * Real.exp (-(2 / π ^ 2) * ∫ t in r..1,
        (max |π - (μH[1] (J₁ t)).toReal / t| |π - (μH[1] (J₂ t)).toReal / t|) ^ 2 / t) := by
  sorry

/-- **Corollary 6.4** (Ch. VI §6; cited in Chapter X, P2:8159, "Theorem 2.5 is an improvement of Corollary VI.6.4",
and P2:8177). If `Γ` is a Jordan curve, then at `Λ₁` almost every tangent point `w` of `Γ`, (6.7)
`∫_0^1 ε²(w, t) dt/t < ∞`.
Modelling: `ε(w, t)` is that of (6.6) with the book's arcs: `J_j(t)` separates `z_j` from `w`
(`IsAdmissibleCircleArcs` with `A = {w}`, as printed; the [CORRECTION] of (6.6) is not used here, since with the
separation from `Γ ∩ B(w, r)` admissible arcs need not exist near `w` when `Γ` wiggles, and the claim would be
vacuous; Chapter X, P2:8159–8177, derives this version). `ε` depends on reference points `z_j ∈ Ω_j` (finite; the
components as in Theorem 6.3) and on the choice of the arcs, and the claim holds for every choice. The book
normalizes `dist(z_j, Γ) ≥ 1` and integrates over `(0, 1)`; here only small `t` are used: for every
`δ ∈ (0, t₀]`, `t₀ = min(dist(z₁, Γ), dist(z₂, Γ))`, and all arcs admissible on `(0, δ)`, the integral over `(0, δ)`
is finite; since `ε ≤ π`, finiteness does not depend on the upper limit, and this replaces the normalization. The
integral of the non-negative integrand is taken in `[0, ∞]` (`∫⁻`), so "`< ∞`" is literal. "Almost every tangent
point" is for `μH[1]` restricted to `Tn(Γ)`. -/
theorem cor6_6_4 {Γ : Set ExtPlane} (hΓ : IsJordanCurve Γ) {Ω₁ Ω₂ : Set ExtPlane}
    (hΩ₁ : IsJordanDomainExt Ω₁ ∧ frontier Ω₁ = Γ) (hΩ₂ : IsJordanDomainExt Ω₂ ∧ frontier Ω₂ = Γ)
    (h12 : Disjoint Ω₁ Ω₂) {z₁ z₂ : ℂ} (hz₁ : (z₁ : ExtPlane) ∈ Ω₁) (hz₂ : (z₂ : ExtPlane) ∈ Ω₂) :
    ∀ᵐ w ∂((μH[1] : Measure ℂ).restrict (tangentPoints Γ)),
      ∀ δ ∈ Ioc 0 (min (infDist z₁ (finitePart Γ)) (infDist z₂ (finitePart Γ))), ∀ J₁ J₂ : ℝ → Set ℂ,
      IsAdmissibleCircleArcs Ω₁ z₁ w {w} J₁ (Ioo 0 δ) → IsAdmissibleCircleArcs Ω₂ z₂ w {w} J₂ (Ioo 0 δ) →
        ∫⁻ t in Ioo 0 δ,
          ENNReal.ofReal ((max |π - (μH[1] (J₁ t)).toReal / t| |π - (μH[1] (J₂ t)).toReal / t|) ^ 2 / t) < ⊤ := by
  sorry

end GarnettMarshall2005
