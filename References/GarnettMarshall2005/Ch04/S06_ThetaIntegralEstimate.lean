import References.GarnettMarshall2005.Ch04.S05_ExtremalDistanceHarmonicMeasure

/-!
# Garnett–Marshall, Chapter IV §6: The `∫ dx/θ(x)` estimate

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §6 (pp. 146–149;
`full.md` P1:6392–6497).

Conventions of Chapter IV as in §1 and §5. The crosscut sets `I_x ⊆ {Re z = x}` and `J_r ⊆ {|z| = r}` are arbitrary
subsets of the plane (not necessarily connected); their length is the linear measure `μH[1]`, and "`I_x` separates
`A` from `B`" is `IsSeparatingIn` in (the finite part of) `Ω`: no component of `Ω \ I_x` has points of both `A` and
`B` in its closure (the reading of §1). "`θ` is measurable" is read as Lebesgue measurability on the interval of
integration (`AEMeasurable` for Lebesgue measure restricted to it). The integrals `∫ dx/θ(x)` are lower Lebesgue
integrals in `[0, ∞]` (`1/0 = ∞`: a set of zero length does not separate when both sets are non-empty, so this
value is never relevant (for `F = ∅` in Theorem 6.1, or `E = ∅` in Theorem 6.2, the conclusion `ω = 0` holds
anyway), and no junk value is read). Harmonic measure is the Jordan-domain harmonic measure (Theorems 6.1, 6.2 are
for Jordan domains, leader ruling B5); since `exp(−π · ∞) = 0`, the bounds (6.3) and (6.4) are stated in two cases, the
integral being infinite (then `ω = 0`) or finite (then the printed bound, with real numbers).

* Formula (6.2) (§6) — `eq4_6_2`
* Theorem 6.1 (§6; (6.3)) — `thm4_6_1`
* Theorem 6.2 (§6; (6.4)) — `thm4_6_2`

Not stated (inventory U−): the heuristics for a strip domain `{|y − m(x)| < θ(x)/2, a < x < b}` (P1:6394–6444: the
serial-rule sum, the approximating rectangles, the non-analytic map `Φ` of (6.1), the metric `1/θ(x)` and the bound
`d_Ω(σ₀, σ_n) ≥ ∫_a^b dx/θ(x)`, a special case of (6.2)); the metric `ρ_A` (P1:6448–6452, 6490–6494, devices of
the proofs); the remark that for `I_x = {z ∈ Ω : Re z = x}` the function `θ` is lower semicontinuous and measurable
(P1:6468); the remarks after Theorem 6.1 (P1:6478: the variant with `ℓ({z ∈ Ω : Re z = x})`, which only increases
the right side of (6.3); sharper versions in App. G; Theorem H.8, the finitely connected version); the sentence
introducing Theorem 6.2 (P1:6480).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt)
open LehtoVirtanen1973 (IsJordanArc)
open References (IsJordanDomainExt finitePart)

/-- **Formula (6.2)** (Ch. IV §6; cited at P1:6476, in the Notes, P1:6500, in Chapter V, P2:72 "by (IV.6.2) and
(2.2)", and in App. H, P3:4819). Let `Ω` be a finitely connected Jordan domain and assume
`E ⊆ {z : Re z ≤ a} ∩ ∂Ω` and `F ⊆ {z : Re z ≥ b} ∩ ∂Ω` are finite unions of arcs. Suppose `I_x ⊆ {z : Re z = x}`
separates `E` from `F` and let `θ(x)` be the length of `I_x`, `a < x < b`. Assume that `θ(x)` is measurable (but not
that `I_x = Ω ∩ {Re z = x}` or that `I_x` is connected). Then (6.2) `d_Ω(E, F) ≥ ∫_a^b dx/θ(x)`.
Modelling: `Ω` is a finitely connected Jordan domain of `ℂ*` (Ch. II §1, `IsFCJordanDomain`) and `d_Ω` is taken on
its finite part; `E` and `F` are unions of finitely many, at least one, Jordan arcs of the plane contained in `∂Ω`;
`I_x` need not lie in `Ω` (only `I_x ∩ Ω` separates, and a longer `I_x` weakens the bound); `θ(x) = μH[1](I_x)`. -/
theorem eq4_6_2 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {a b : ℝ} {E F : Set ℂ}
    (hE : IsFiniteUnionOf (fun s : Set ℂ => IsJordanArc (toExt s) ∧ toExt s ⊆ frontier Ω) E)
    (hEa : ∀ z ∈ E, z.re ≤ a)
    (hF : IsFiniteUnionOf (fun s : Set ℂ => IsJordanArc (toExt s) ∧ toExt s ⊆ frontier Ω) F)
    (hFb : ∀ z ∈ F, b ≤ z.re) {I : ℝ → Set ℂ}
    (hI : ∀ x ∈ Ioo a b, I x ⊆ {z : ℂ | z.re = x} ∧ IsSeparatingIn (finitePart Ω) (I x) E F)
    (hθ : AEMeasurable (fun x => μH[1] (I x)) (volume.restrict (Ioo a b))) :
    ∫⁻ x in Ioo a b, (μH[1] (I x))⁻¹ ≤ extremalDistGM (finitePart Ω) E F := by
  sorry

/-- **Theorem 6.1** (Ch. IV §6), (6.3) (cited at P1:6478, 6496, in Chapter V, P1:6751, 6851, 6921, 6943, in Chapter VI,
P2:1662, Chapter X, P3:243, and App. G, P3:4376, 4384, 4534, 4546, App. H, P3:4798, 4913). Let `Ω` be a Jordan domain
and let `z₀ ∈ Ω`. Let `b > x₀ = Re z₀` and suppose `F ⊆ {z ∈ ∂Ω : Re z ≥ b}`. Assume that for `x₀ < x < b` there exists
`I_x ⊆ Ω ∩ {Re z = x}` separating `z₀` from `F` [OCR or misprint?: "separating z from F", a text-layer span] and set
`θ(x) ≡ ℓ(I_x)`. Then (6.3) `ω(z₀, F) ≤ (8/π) exp(−π ∫_{x₀}^b dx/θ(x))`.
Modelling: `z₀` is a finite point of the Jordan domain `Ω` of `ℂ*` and `F` a set of the plane with `F ⊆ ∂Ω`;
`ω(z₀, F) = ω(z₀, F, Ω)` is `harmonicMeasureJordan Ω z₀ F`; `θ(x) = μH[1](I_x)`. Added hypothesis: `θ` is measurable (it
is stated in (6.2), from which the theorem is proved, and in Theorem 6.2, and the book's integral needs it (Lean's `∫⁻`
exists for any `θ`); the book's remark P1:6468 supplies it for `I_x = Ω ∩ {Re z = x}`). (6.3) in two cases, as in the
module docstring; the constant was checked against the equation image. -/
theorem thm4_6_1 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ Ω) {b : ℝ}
    (hb : z₀.re < b) {F : Set ℂ} (hF : toExt F ⊆ frontier Ω) (hFb : ∀ z ∈ F, b ≤ z.re) {I : ℝ → Set ℂ}
    (hI : ∀ x ∈ Ioo z₀.re b, I x ⊆ finitePart Ω ∩ {z : ℂ | z.re = x} ∧ IsSeparatingIn (finitePart Ω) (I x) {z₀} F)
    (hθ : AEMeasurable (fun x => μH[1] (I x)) (volume.restrict (Ioo z₀.re b))) :
    (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹ = ⊤ → harmonicMeasureJordan Ω z₀ (toExt F) = 0) ∧
      (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹ < ⊤ →
        harmonicMeasureJordan Ω z₀ (toExt F) ≤
          ENNReal.ofReal (8 / π * Real.exp (-π * (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹).toReal))) := by
  sorry

/-- **Theorem 6.2** (Ch. IV §6), (6.4) (cited in the Exercises of Chapter III, P1:5521, in Chapter V, P1:6751, 6799,
6805, P2:419, and in Chapter VI, P2:1436, 1830). Let `Ω` be a Jordan domain and let `E ⊆ Ω̄ ∩ {|z| ≥ R}`. Suppose
`z₀ ∈ Ω` satisfies `r₀ = max(|z₀|, dist(0, ∂Ω)) < R`. Suppose that `J_r ⊆ {z ∈ Ω : |z| = r}` separates `z₀` from `E`,
`r₀ < r < R`, and let `rΘ(r)` be the length of `J_r`. Then (6.4) `ω(z₀, E) ≤ (8/π) exp(−π ∫_{r₀}^R dr/(rΘ(r)))`, if
`Θ(r)` is measurable.
Modelling: `z₀` finite, `E` a set of the plane with `E ⊆ Ω̄` (closure in `ℂ*`); `dist(0, ∂Ω)` is the distance from `0`
to the finite part of `∂Ω`; `ω(z₀, E)` is the Jordan-domain harmonic measure of `E` (a measure on `∂Ω`, so it measures
`E ∩ ∂Ω`; this is how Chapter VI uses it, P2:1436: `ω_j(B(w, r))`; the alternative reading `ω(z₀, E, Ω \ E)` is not
needed: the uses at P1:5521 and P1:6799 follow through the truncated Jordan domain); `Θ` is given with
`rΘ(r) = μH[1](J_r)` for `r₀ < r < R`; (6.4) in two cases, as in the module docstring; the constant was checked against
the equation image. -/
theorem thm4_6_2 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {R : ℝ} {E : Set ℂ} (hE : toExt E ⊆ closure Ω)
    (hER : ∀ z ∈ E, R ≤ ‖z‖) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ Ω) {r₀ : ℝ}
    (hr₀ : r₀ = max ‖z₀‖ (infDist 0 (finitePart (frontier Ω)))) (hr₀R : r₀ < R) {J : ℝ → Set ℂ}
    {Θ : ℝ → ℝ≥0∞}
    (hJ : ∀ r ∈ Ioo r₀ R, J r ⊆ finitePart Ω ∩ sphere 0 r ∧ IsSeparatingIn (finitePart Ω) (J r) {z₀} E ∧
      ENNReal.ofReal r * Θ r = μH[1] (J r))
    (hΘ : AEMeasurable Θ (volume.restrict (Ioo r₀ R))) :
    (∫⁻ r in Ioo r₀ R, (ENNReal.ofReal r * Θ r)⁻¹ = ⊤ → harmonicMeasureJordan Ω z₀ (toExt E) = 0) ∧
      (∫⁻ r in Ioo r₀ R, (ENNReal.ofReal r * Θ r)⁻¹ < ⊤ →
        harmonicMeasureJordan Ω z₀ (toExt E) ≤
          ENNReal.ofReal (8 / π * Real.exp (-π * (∫⁻ r in Ioo r₀ R, (ENNReal.ofReal r * Θ r)⁻¹).toReal))) := by
  sorry

end GarnettMarshall2005
