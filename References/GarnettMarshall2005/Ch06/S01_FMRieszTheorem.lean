import References.GarnettMarshall2005.Ch05.S06_ConditionsMoreGeometric
import References.GarnettMarshall2005.App.A_HardySpaces

/-!
# Garnett–Marshall, Chapter VI §1: The F. and M. Riesz theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §1 (pp. 200–202;
`full.md` of the second part, P2:681–808; the chapter introduction is P2:681–689).

Conventions of Chapter VI, as modelled here (leader ruling C6). Chapter VI is planar: a domain is `Ω ⊆ ℂ`, "simply
connected domain" is `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`, and a conformal map `φ : 𝔻 → Ω` is
`LiZhongQC.IsConformalOnto φ unitDisc Ω`. The boundary function `φ(ζ)` of a conformal map is a nontangential limit
(`HasNontangentialLimit`, Ch. I §2; see §3), never a junk-valued map; in the Jordan setting of this section it is the
value `Φ(ζ)` of the continuous extension `Φ` of `φ` to `𝔻̄` (Carathéodory's theorem, used by the book's proofs), and
`φ(E)` is `Φ(E)`. "Let `Ω` be a domain such that `∂Ω = Γ` is a Jordan curve and `φ` a conformal map from `𝔻` onto
`Ω`" is the standing assumption `IsJordanDiscMap Ω φ Φ` of Ch. II §4 (a bounded plane Jordan domain, `φ`, and its
continuous extension `Φ`), or in Theorem 1.1 the same without `Φ`. `Ω` is bounded (leader ruling C12(c)): the book's
rectifiable `Γ` and `φ′ ∈ H¹` belong to planar curves (`φ′ ∈ H¹` makes `φ` bounded, and a Jordan curve through `∞` is
not rectifiable), and `jordanCurveLength` has the junk value `0` on curves through `∞`. `Λ₁` is linear measure,
Mathlib's `μH[1]` on `ℂ` (leader ruling C2: in Chapter VI `Λ₁` is arc length, `(1.1)`, `(1.3)` and Theorem 1.2
were checked against the equation images, while App. D's `Λ₁` is half the arc length, P3:3219, a book inconsistency
recorded in the root's Corrections list; the equality `(1.1)` and Theorem 1.2(a) would change by the factor `2` under
App. D's normalization, the null-set statement `(1.4)` and Corollary 1.3 would not). `|E|` and "almost every
`ζ ∈ ∂𝔻`" refer to `arcMeasure` (`dθ`, total mass `2π`). The Hardy space `Hᵖ` and its norm are those of App. A
(`MemHardy`, `hardyNorm`), with the normalization recalled at P2:693–699. `φ′` on `∂𝔻` is the nontangential limit
of `φ′`, which exists almost everywhere when `φ′ ∈ H¹` (Theorem A.1). Harmonic measure is the Jordan-domain harmonic
measure `harmonicMeasureJordan` of Ch. I §3 (the results are stated for Jordan domains, leader rulings D1, B5, C6);
"`ω(A)`" without a point is stated for every `z ∈ Ω` (the null sets do not depend on `z`).

* Definition (the Hardy space `Hᵖ` and its norm, recalled, §1, P2:693–699) — exists:
  `GarnettMarshall2005.MemHardy` `GarnettMarshall2005.hardyNorm` (App. A, (A.1): the same definition with the same
  normalization, the supremum over r of the integral of the p-th power of the modulus on the circle of radius r with
  respect to d theta, without the factor 1/2π)
* Definition (length `ℓ(Γ)` of a Jordan curve; rectifiable, §1, P2:715) — `jordanCurveLength` (B-cand.
  LehtoVirtanen1973.IsRectifiableJordanCurve with the length measured by the linear measure; the two notions agree
  only through the theorem length = linear measure, leader ruling C7)
* Theorem 1.1 (§1; (1.1)) — `thm6_1_1_a`, `thm6_1_1_b`
* Theorem 1.2 (F. and M. Riesz, §1; (1.4)) — `thm6_1_2_a`, `thm6_1_2_b`
* Corollary 1.3 (§1) — `cor6_1_3`

Helper (not a book notion): `HasTangentAtPoint` (a Jordan curve of `ℂ*` has a tangent, in the sense of (II.4.1),
(II.4.2), at a finite point; used by Corollary 1.3 and by the set `Tn(Γ)` of §4).

Near misses in Pommerenke1992 Ch. 6 (installed; not pointers): Theorem 6.8 (Pommerenke1992.thm6_8_a to thm6_8_d,
the Riesz–Privalov theorem) states "rectifiable" as finite linear measure (not the partition length `ℓ(Γ)`, leader
ruling C7), the equality (6.3.2) for linearly measurable sets through angular limits of `f′`, and (6.3.3) as a
pull-back to the circle rather than harmonic measure of `Ω`; so Theorem 1.1(a) (hypothesis on `ℓ(Γ)`), (1.1) (not in
Pommerenke), Theorem 1.2 (a different notion of rectifiability in the hypothesis, and `ω` of `Ω` in (1.4)) and
Corollary 1.3 (tangents; Pommerenke's (6.3.4) has the unrestricted difference quotient) are new. Likewise
Pommerenke1992.eq6_3_10 (arbitrary `G`, linear measure of `∂G`).

Not stated (inventory U−): the chapter introduction (P2:683–689: `ω ⊥ Λ_α`, `α > 1`, and Pommerenke's extension, the
content of §5–§6); the independence of `ℓ(Γ)` from the parametrization (part of the definition's docstring); the
derivation "Theorem 1.1 is equivalent to a theorem about harmonic measure" (P2:747–783: `ω(z₀, A, Ω) = |E|/2π`,
(1.3) for arcs and Borel sets, and `ω ≪ Λ₁ ≪ ω`; (1.3) is Theorem 1.2(a) and the mutual absolute continuity is
(1.4)); "Theorem 1.2 is equivalent to Theorem 1.1", Lavrentiev's quantitative version of (1.4) and the example of
Exercise 4 (P2:797–799, remarks); the derivation of Corollary 1.3 (P2:801: "`φ′` has a non-zero nontangential limit
at almost all `ζ`", by Fatou's theorem, Theorem 1.1 and Corollary A.2, and "by calculus" a non-zero angular
derivative, which is Lemma V.5.4; the later citations of this claim "by the F. and M. Riesz theorem", P2:7253, 7651,
are Corollary 1.3 together with Lemma V.5.4); Bishop's example of a non-rectifiable Jordan domain conformal almost
everywhere without tangents, and "at most two `ζ ∈ φ⁻¹(w)` at which `φ` is conformal" (P2:805–807, remarks, not
cited).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open References (IsJordanDomainExt)

/-- **Definition** (length of a Jordan curve; rectifiable, Ch. VI §1, P2:715, recalled in the proof of Theorem 1.1;
used in Theorems 1.1, 1.2, Corollary 1.3, in (VI.5.1) and in Chapter X). The length `ℓ(Γ)` of the Jordan curve `Γ`
is the supremum, over all partitions `0 = θ₀ < θ₁ < … < θₙ = 2π`, of `Σ |γ(θⱼ) − γ(θⱼ₋₁)|` for a parametrization
`γ` of `Γ`; `Γ` is rectifiable if `ℓ(Γ) < ∞`.
Modelling (leader ruling C7): `Γ ⊆ ℂ*`; the parametrizations are the loop parametrizations
`LehtoVirtanen1973.IsLoopParam` with finite values (`γ : ℝ → ℂ`, period `1`), and the partition supremum is the
variation `eVariationOn γ (Icc 0 1)` in `[0, ∞]`. It does not depend on the parametrization (inventory U−), so the
value is written as the supremum of the set of these variations, a one-point set for a Jordan curve of `ℂ` (the
registered "value over all maps" pattern). "Rectifiable" is `jordanCurveLength Γ < ⊤`. Junk: `0` when `Γ` is not a
Jordan curve of the finite plane (for example a curve through `∞`, which the book would call non-rectifiable); every
statement using it assumes `Γ` bounded (module docstring). -/
def jordanCurveLength (Γ : Set ExtPlane) : ℝ≥0∞ :=
  sSup {L : ℝ≥0∞ | ∃ γ : ℝ → ℂ, LehtoVirtanen1973.IsLoopParam Γ (fun t => (γ t : ExtPlane)) ∧
    L = eVariationOn γ (Icc 0 1)}

/-- `Γ` has a tangent at the finite point `w` (helper, Ch. VI §1 and §4; the notion of (II.4.1), (II.4.2) for a
Jordan curve): some loop parametrization `γ` of the Jordan curve `Γ ⊆ ℂ*` (`LehtoVirtanen1973.IsLoopParam`) passes
through `w` at the parameter `t₀`, has finite values `g(t)` near `t₀`, and `g` has a tangent at `t₀` in the sense of
`HasTangentAt` (Ch. II §4). A reparametrization preserves the two one-sided direction limits (up to exchanging them,
which replaces `e^{iτ}` by `−e^{iτ}`), so "some parametrization" is "every parametrization". -/
def HasTangentAtPoint (Γ : Set ExtPlane) (w : ℂ) : Prop :=
  ∃ (γ : ℝ → ExtPlane) (g : ℝ → ℂ) (t₀ τ : ℝ), LehtoVirtanen1973.IsLoopParam Γ γ ∧ γ t₀ = (w : ExtPlane) ∧
    (∀ᶠ t in 𝓝 t₀, γ t = (g t : ExtPlane)) ∧ HasTangentAt g t₀ τ

/-- **Theorem 1.1** (Ch. VI §1), part (a) (cited at P2:747, 797, 801). Let `Ω` be a domain such that `∂Ω = Γ` is a
Jordan curve and let `φ` be a conformal map from `𝔻` onto `Ω`. Then the curve `Γ` is rectifiable if and only if
`φ′ ∈ H¹`.
Modelling: `Ω ⊆ ℂ` a Jordan domain of `ℂ*` (`References.IsJordanDomainExt (toExt Ω)`), bounded (module docstring:
added because `jordanCurveLength` has the junk value `0` on a curve through `∞`, which the book calls
non-rectifiable); `Γ = ∂Ω` is `toExt (frontier Ω)`; `φ′` is `deriv φ`; `H¹` is `MemHardy 1` (App. A). -/
theorem thm6_1_1_a {Ω : Set ℂ} (hΩ : IsJordanDomainExt (toExt Ω)) (hb : Bornology.IsBounded Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) :
    jordanCurveLength (toExt (frontier Ω)) < ⊤ ↔ MemHardy 1 (deriv φ) := by
  sorry

/-- **Theorem 1.1** (Ch. VI §1), part (b), (1.1) (cited at P2:753, and by name, "by the F. and M. Riesz theorem,
`‖φ′‖_{H¹} = ℓ(Γ)`", at P3:494). In the setting of part (a), if `φ′ ∈ H¹`, then
(1.1) `‖φ′‖_{H¹} = ℓ(Γ) = Λ₁(Γ)`.
Modelling: as in part (a); `Λ₁` is `μH[1]` (module docstring, leader ruling C2); the norm and the length are compared
in `[0, ∞]`. The formula (1.1) was checked against the equation image. -/
theorem thm6_1_1_b {Ω : Set ℂ} (hΩ : IsJordanDomainExt (toExt Ω)) (hb : Bornology.IsBounded Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) (hH : MemHardy 1 (deriv φ)) :
    hardyNorm 1 (deriv φ) = jordanCurveLength (toExt (frontier Ω)) ∧
      jordanCurveLength (toExt (frontier Ω)) = μH[1] (frontier Ω) := by
  sorry

/-- **Theorem 1.2** (F. and M. Riesz, Ch. VI §1), first part (cited by name at P2:838, 859, 998, 1047, 1114, in
Chapter X, P2:7253, 7651, 8219, P3:1310, and in Exercise VI.3, P2:1632). Let `Ω` be a simply connected plane domain
such that `Γ = ∂Ω` is a rectifiable Jordan curve and let `φ : 𝔻 → Ω` be conformal. Then `φ′ ∈ L¹(∂𝔻)`, and for any
Borel set `E ⊆ ∂𝔻`, `Λ₁(φ(E)) = ∫_E |φ′| dθ`.
Modelling: `IsJordanDiscMap Ω φ Φ` (module docstring; a Jordan domain is simply connected, and `Ω` is bounded because
a rectifiable `Γ` is), `Γ` rectifiable as `jordanCurveLength`; `φ(E)` is `Φ(E)`; `φ′` on `∂𝔻` is a function `g` that
is the nontangential limit of `φ′` almost everywhere (any two such functions agree almost everywhere, so the integral
does not depend on the choice); `φ′ ∈ L¹(∂𝔻)` is the integrability of `g` for `dθ`; the integral is the lower
integral of `|g|` in `[0, ∞]`; `Λ₁` is `μH[1]`. The formula was checked against the equation image. -/
theorem thm6_1_2_a {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ)
    (hrect : jordanCurveLength (toExt (frontier Ω)) < ⊤) :
    ∃ g : ℂ → ℂ, (∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit (deriv φ) ζ (g ζ)) ∧ Integrable g arcMeasure ∧
      ∀ E ⊆ sphere (0 : ℂ) 1, MeasurableSet E → μH[1] (Φ '' E) = ∫⁻ ζ in E, ‖g ζ‖ₑ ∂arcMeasure := by
  sorry

/-- **Theorem 1.2** (F. and M. Riesz, Ch. VI §1), second part, (1.4) (cited "by (1.4)" at P2:859 and by name at
P2:998, 1047, 1114). In the setting of the first part, for any Borel set `A ⊆ ∂Ω`,
(1.4) `ω(A) = 0 ⟺ Λ₁(A) = 0`.
Modelling: as in the first part; `ω(A)` is `harmonicMeasureJordan (toExt Ω) z (toExt A)` for every `z ∈ Ω` (module
docstring); `Λ₁` is `μH[1]`; Borel is `MeasurableSet` in `ℂ`. The formula (1.4) was checked against the equation
image. -/
theorem thm6_1_2_b {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ)
    (hrect : jordanCurveLength (toExt (frontier Ω)) < ⊤) :
    ∀ z ∈ Ω, ∀ A ⊆ frontier Ω, MeasurableSet A →
      (harmonicMeasureJordan (toExt Ω) (z : ExtPlane) (toExt A) = 0 ↔ μH[1] A = 0) := by
  sorry

/-- **Corollary 1.3** (Ch. VI §1; its first half is cited "by the F. and M. Riesz theorem" at P2:7253, 7651, with
Lemma V.5.4). Let `Ω` be a domain such that `∂Ω = Γ` is a rectifiable Jordan curve and let `φ` be a conformal map
from `𝔻` onto `Ω`. Then `φ` has a non-zero angular derivative at `ζ` and `Γ` has a tangent at `φ(ζ)`, both for
Lebesgue almost every `ζ ∈ ∂𝔻` and for `Λ₁` almost every `φ(ζ) ∈ Γ`.
Modelling: `IsJordanDiscMap Ω φ Φ` and `Γ` rectifiable (as in Theorem 1.2); the angular derivative is Definition V.5.3
for `Ω = 𝔻` with the inner normal `−ζ` (`θ = arg(−ζ)`), non-zero as `L ≠ 0`; the tangent is `HasTangentAtPoint` at
`φ(ζ) = Φ(ζ)`; "for `Λ₁` almost every `φ(ζ) ∈ Γ`": for `μH[1]`-almost every `w ∈ Γ`, every `ζ ∈ ∂𝔻` with
`Φ(ζ) = w` (there is exactly one) has both properties. -/
theorem cor6_1_3 {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ)
    (hrect : jordanCurveLength (toExt (frontier Ω)) < ⊤) :
    (∀ᵐ ζ ∂arcMeasure, (∃ w L : ℂ, L ≠ 0 ∧ HasAngularDerivGM φ unitDisc ζ (arg (-ζ)) w L) ∧
        HasTangentAtPoint (toExt (frontier Ω)) (Φ ζ)) ∧
      ∀ᵐ w ∂(μH[1].restrict (frontier Ω)), ∀ ζ ∈ sphere (0 : ℂ) 1, Φ ζ = w →
        (∃ w' L : ℂ, L ≠ 0 ∧ HasAngularDerivGM φ unitDisc ζ (arg (-ζ)) w' L) ∧
          HasTangentAtPoint (toExt (frontier Ω)) (Φ ζ) := by
  sorry

end GarnettMarshall2005
