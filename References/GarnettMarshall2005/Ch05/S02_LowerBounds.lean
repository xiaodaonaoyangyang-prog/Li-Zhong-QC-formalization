import References.GarnettMarshall2005.Ch05.S01_AsymptoticValuesEntireFunctions

/-!
# Garnett–Marshall, Chapter V §2: Lower bounds

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V §2 (pp. 158–161;
`full.md` P1:6843–6950).

Conventions of Chapter V §2, as modelled here. The domains of this section are plane sets
`Ω = {(x, y) : |y − m(x)| < θ(x)/2, x ∈ I}` for an interval `I` (`stripDomain m θ I`), with `θ > 0` on `I` (`θ(x)` is
the width of the vertical section of `Ω` over `x`). "Jordan domain" is a Jordan domain of `ℂ*`
(`References.IsJordanDomainExt (toExt Ω)`; for the unbounded `Ω` of Corollary 2.2 its boundary curve passes through
`∞`); extremal distances are taken in the plane, as in Chapter IV. "`m` and `θ` are absolutely continuous on
`(a, b)`" is read as absolute continuity on every compact subinterval of the open interval (Mathlib
`AbsolutelyContinuousOnInterval`; leader ruling C12(a)); then `m'` and `θ'` exist almost everywhere, and `m'(x)`,
`θ'(x)` are `deriv m x`, `deriv θ x`, whose junk value `0` off the points of differentiability sits on a null set
that the integrals do not see. The integrals of the bounds are lower Lebesgue integrals in `[0, ∞]` of nonnegative
integrands (a bound `+∞` is allowed); where the book exponentiates them, the statement assumes them finite or proves
nothing new otherwise (the book's right side is then `0`). Harmonic measure is the Jordan-domain harmonic measure
`harmonicMeasureJordan` of Ch. I §3 (the results are stated for Jordan domains, leader rulings B5, C6), compared with
numbers in `[0, ∞]`.

* Formula (2.2) (§2) — `eq5_2_2` (with the helper `stripDomain`)
* Theorem 2.1 (§2; (2.3)) — `thm5_2_1`
* Corollary 2.2 (§2) — `cor5_2_2`

Helper (not a book notion): `stripDomain` (the domain `{|y − m(x)| < θ(x)/2, x ∈ I}`).

Not stated (inventory U−): the motivation that (IV.6.3) is not sharp for these domains because the map `Φ` of
(IV.6.1) is not conformal (P1:6845); Beurling's metric `ρ_B` of (2.1), its length bound `∫_γ ρ_B |dz| ≥ 1` and its
area `A(Ω, ρ_B)` (P1:6851–6869: the derivation of (2.2); `ρ_B` is a device of proofs, reused in Section 6 only as a
method, P2:212); the remark that Theorem 2.1 makes Theorem IV.6.1 best possible for smooth boundaries (P1:6921); the
remark on metrics of the form `ρ = |∇u|` (P1:6943–6949).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt)
open References (IsJordanDomainExt)

/-- The domain `{(x, y) : |y − m(x)| < θ(x)/2, x ∈ I}` (helper, Ch. V §2, P1:6845, 6877, 6923): the points `z` with
`Re z ∈ I` and `|Im z − m(Re z)| < θ(Re z)/2`. -/
def stripDomain (m θ : ℝ → ℝ) (I : Set ℝ) : Set ℂ :=
  {z | z.re ∈ I ∧ |z.im - m z.re| < θ z.re / 2}

/-- **Formula (2.2)** (Ch. V §2, P1:6871–6875; cited at P1:6919 in the proof of Theorem 2.1, in the proof of
Corollary 5.8, P2:72 "by (IV.6.2) and (2.2)", in the Notes, P2:419, and in Exercise 8, P2:625, 627). For a domain
`Ω = {(x, y) : |y − m(x)| < θ(x)/2, a < x < b}` (with minor smoothness assumptions on `m` and `θ`), let
`E = ∂Ω ∩ {x = a}` and `F = ∂Ω ∩ {x = b}`. Then
(2.2) `d_Ω(E, F) = 1/d*_Ω(E, F) ≤ ∫_a^b dx/θ(x) + ∫_a^b (m'(x)² + θ'(x)²/12)/θ(x) dx`.
Modelling: the "minor smoothness assumptions" are those of Theorem 2.1 (`Ω` a Jordan domain, `m` and `θ` absolutely
continuous on `(a, b)`, module docstring), so that `E` and `F` are the two ends of `Ω` and `d = 1/d*` is (IV.1.7);
`θ > 0` on `(a, b)` (the width of `Ω`; the integrands would otherwise be clamped); `∂Ω` is the boundary in the plane;
`1/d*` is the inverse in `[0, ∞]`; the integrals are lower integrals in `[0, ∞]`. The constant `1/12` was checked
against the equation image. -/
theorem eq5_2_2 {a b : ℝ} {m θ : ℝ → ℝ} (hθ : ∀ x ∈ Ioo a b, 0 < θ x)
    (hm : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval m c d)
    (hθac : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval θ c d) {Ω E F : Set ℂ}
    (hΩ : Ω = stripDomain m θ (Ioo a b)) (hJ : IsJordanDomainExt (toExt Ω))
    (hE : E = frontier Ω ∩ {z | z.re = a}) (hF : F = frontier Ω ∩ {z | z.re = b}) :
    extremalDistGM Ω E F = (conjExtremalDistGM Ω E F)⁻¹ ∧
      extremalDistGM Ω E F ≤ (∫⁻ x in Ioo a b, ENNReal.ofReal (1 / θ x)) +
        ∫⁻ x in Ioo a b, ENNReal.ofReal ((deriv m x ^ 2 + deriv θ x ^ 2 / 12) / θ x) := by
  sorry

/-- **Theorem 2.1** (Ch. V §2), (2.3) (Beurling's converse to Theorem IV.6.1; cited at P1:6921, 6943, and with
Corollary 2.2 as "the estimates in Sections 2 and IV.6", P2:32). Suppose
`Ω = {(x, y) : |y − m(x)| < θ(x)/2, a < x < b}` is a Jordan domain and suppose `θ` and `m` are absolutely continuous
on `(a, b)`. Suppose further that `{(x, y) : |x − x₀| < δ, |y − y₀| < δ} ⊂ Ω`, and set `z₀ = x₀ + iy₀`. If
`F = ∂Ω ∩ {(x, y) : x = b}`, then
(2.3) `ω(z₀, F) ≥ C(δ) exp{−π ∫_{x₀}^b (1 + m'(x)² + θ'(x)²/12)/θ(x) dx}`, where
`C(δ) = exp(−(π/δ²) ∫_{x₀−δ}^{x₀+δ} θ(x) dx)` depends only on `δ` and `θ(x)` for `x ∈ (x₀ − δ, x₀ + δ)`.
Modelling: as in (2.2) (`eq5_2_2`); `δ > 0` (a square; for `δ ≤ 0` the square is empty and `π/δ²` is junk);
`z₀ = x₀ + iy₀` is the complex number `z₀` with `x₀ = Re z₀`, `y₀ = Im z₀`; `ω(z₀, F)` is
`harmonicMeasureJordan (toExt Ω) z₀ (toExt F)` (module docstring). The two integrals are lower integrals in `[0, ∞]`;
the hypotheses that they are finite only remove the case in which the book's right side is `exp(−∞) = 0` (then (2.3)
says nothing), so that the integrals are read as real numbers. The dependence of `C(δ)` is explicit (a formula). The
constants `1/12` and `π/δ²` were checked against the equation images. -/
theorem thm5_2_1 {a b : ℝ} {m θ : ℝ → ℝ} (hθ : ∀ x ∈ Ioo a b, 0 < θ x)
    (hm : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval m c d)
    (hθac : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval θ c d) {Ω : Set ℂ}
    (hΩ : Ω = stripDomain m θ (Ioo a b)) (hJ : IsJordanDomainExt (toExt Ω)) {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsq : Ioo (z₀.re - δ) (z₀.re + δ) ×ℂ Ioo (z₀.im - δ) (z₀.im + δ) ⊆ Ω) {F : Set ℂ}
    (hF : F = frontier Ω ∩ {z | z.re = b})
    (hI : ∫⁻ x in Ioo z₀.re b, ENNReal.ofReal ((1 + deriv m x ^ 2 + deriv θ x ^ 2 / 12) / θ x) < ⊤)
    (hC : ∫⁻ x in Ioo (z₀.re - δ) (z₀.re + δ), ENNReal.ofReal (θ x) < ⊤) :
    ENNReal.ofReal (Real.exp (-(π / δ ^ 2) * (∫⁻ x in Ioo (z₀.re - δ) (z₀.re + δ), ENNReal.ofReal (θ x)).toReal) *
        Real.exp (-π * (∫⁻ x in Ioo z₀.re b,
          ENNReal.ofReal ((1 + deriv m x ^ 2 + deriv θ x ^ 2 / 12) / θ x)).toReal)) ≤
      harmonicMeasureJordan (toExt Ω) z₀ (toExt F) := by
  sorry

/-- **Corollary 2.2** (Ch. V §2; with Theorem 2.1 "the estimates in Sections 2 and IV.6", P2:32). Suppose
`Ω = {(x, y) : |y − m(x)| < θ(x)/2, x > a}` is a Jordan domain and suppose
`{(x, y) : |x − x₀| < δ, |y − y₀| < δ} ⊂ Ω`. Set `z₀ = x₀ + iy₀`. If
`∫_a^∞ (m'(x)² + θ'(x)²)/θ(x) dx = A < ∞`, then whenever `b > x₀` and `F = {z ∈ Ω̄ : Re z ≥ b}`,
`C exp(−π ∫_{x₀}^b dx/θ(x)) ≤ ω(z₀, F) ≤ (8/π) exp(−π ∫_{x₀}^b dx/θ(x))`, where `C` is a constant depending only on
`A` and `θ(x)` for `x ∈ (x₀ − δ, x₀ + δ)`.
Modelling: the dependence of `C` is the quantifier order (DESIGN §5): for all `A`, `δ > 0`, `x₀` and a function `θ₀`
(the values of `θ` on `(x₀ − δ, x₀ + δ)`) there is `C > 0` (a positive constant: the lower bound is the content)
which works for every `a`, `y₀`, `m`, `θ` with `θ = θ₀` on `(x₀ − δ, x₀ + δ)`. The smoothness of Theorem 2.1 is
assumed on `(a, ∞)` (the derivatives `m'`, `θ'` presuppose it), with `θ > 0` there (module docstring). `Ω` is
unbounded, and its closure `Ω̄` is taken in `ℂ*`, so `F` contains `∞` (a point of harmonic measure zero; harmonic
measure only sees `F ∩ ∂Ω`). `∫_{x₀}^b dx/θ(x)` is a real integral: `θ` is continuous and positive on `[x₀, b]`, since
`x₀ > a`. `A` is given by `∫_a^∞ … = A` in `[0, ∞]`. The constant `8/π` was checked against the equation image. -/
theorem cor5_2_2 (A δ x₀ : ℝ) (θ₀ : ℝ → ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (m θ : ℝ → ℝ) (Ω : Set ℂ) (z₀ : ℂ), z₀.re = x₀ →
      EqOn θ θ₀ (Ioo (x₀ - δ) (x₀ + δ)) → (∀ x ∈ Ioi a, 0 < θ x) →
      (∀ c ∈ Ioi a, ∀ d ∈ Ioi a, AbsolutelyContinuousOnInterval m c d) →
      (∀ c ∈ Ioi a, ∀ d ∈ Ioi a, AbsolutelyContinuousOnInterval θ c d) →
      Ω = stripDomain m θ (Ioi a) → IsJordanDomainExt (toExt Ω) →
      Ioo (x₀ - δ) (x₀ + δ) ×ℂ Ioo (z₀.im - δ) (z₀.im + δ) ⊆ Ω →
      ∫⁻ x in Ioi a, ENNReal.ofReal ((deriv m x ^ 2 + deriv θ x ^ 2) / θ x) = ENNReal.ofReal A →
      ∀ b : ℝ, x₀ < b →
        ENNReal.ofReal (C * Real.exp (-π * ∫ x in x₀..b, 1 / θ x)) ≤
            harmonicMeasureJordan (toExt Ω) z₀ (closure (toExt Ω) \ toExt {z | z.re < b}) ∧
          harmonicMeasureJordan (toExt Ω) z₀ (closure (toExt Ω) \ toExt {z | z.re < b}) ≤
            ENNReal.ofReal (8 / π * Real.exp (-π * ∫ x in x₀..b, 1 / θ x)) := by
  sorry

end GarnettMarshall2005
