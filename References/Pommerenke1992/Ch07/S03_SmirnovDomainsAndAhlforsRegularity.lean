import References.Pommerenke1992.Ch07.S02_IntegralsOfBlochFunctions

/-!
# Pommerenke 1992, Ch. 7 §7.3 Smirnov Domains and Ahlfors-Regularity

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 7 *Smirnov and Lavrentiev Domains*, §7.3;
source `full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 6768–7001.

* Definition (the Hardy spaces `H¹`, (6.3.5), and `Hᵖ`; used at l. 6770, 6798, 7317, 7319) — exists:
  `GarnettMarshall2005.MemHardy` (GM App. A: an analytic function in the disc whose integral means of the p-th power
  of its modulus over the circles of radius r, without the factor 1/2π, stay bounded, which is (6.3.5) for p = 1;
  every use in Ch. 7 is membership only, so the normalization does not matter; membership in Hᵖ is MemHardy applied to
  ENNReal.ofReal p)
* Definition (the boundary values `f'(ζ)` as angular limits, l. 6770, used in (7.3.1)–(7.3.11); helper) —
  `IsAngularBoundaryFun`
* Formula (7.3.1) (Dur70, p. 24; cited at P2 l. 2088, "the singular measure in (7.3.1)") — `eq7_3_1`
* Definition (singular measure, l. 6776: "the corresponding increasing function has derivative zero almost
  everywhere") — exists: `MeasureTheory.Measure.MutuallySingular` (a finite measure on the circle is singular if it
  is mutually singular with the arc-length measure GarnettMarshall2005.arcMeasure; by the Lebesgue decomposition this
  is the book's condition on its distribution function)
* Formula (7.3.2) (cited in the proof of Proposition 7.5, l. 6904) — `eq7_3_2`
* Definition (the Smirnov condition, (7.3.3); used at l. 6796, 6798, 6826, 7333) — `HasSmirnovCondition`
* Formula (7.3.4) (Gar81, p. 15; cited in the proof of Proposition 7.4, l. 6852) — `eq7_3_4`
* Definition (Smirnov domain, l. 6796; used in Propositions 7.4, 7.5, Theorems 7.6, 7.11 and at P2 l. 2088) —
  `IsSmirnovDomain`
* Unlabelled (§7.3, l. 6798: the Smirnov condition holds if `log f' ∈ H¹`; used in the proof of Proposition 7.13,
  l. 7333) — `hasSmirnovCondition_of_log_mem_H1`
* Formula (7.3.8) (the arc `I(z)`; cited at l. 7029) — exists: `Pommerenke1992.arcI` (Ch. 5, (5.2.4), the same set;
  the statements integrate over its parameter interval from arg z − π(1 − |z|) to arg z + π(1 − |z|), of length
  Λ(I(z)) = 2π(1 − |z|))
* Proposition 7.4 ((7.3.9); cited in the proof of Theorem 7.11, l. 7237, 7245) — `prop7_4`
* Condition (7.3.10) (= (7.1.4); with `q = 1` it is (7.4.2), and it is (7.5.8), (7.5.9), (7.5.13); cited in the
  statement of Theorem 7.6; helper) — `HasArcMeanBound`
* Proposition 7.5 ((7.3.10), (7.3.11); cited in the proofs of Theorems 7.6, 7.11 and Exercise 7.4.2) — `prop7_5_a`,
  `prop7_5_b`
* Definition (Ahlfors-regular curve, (7.3.12) = (7.1.2); cited in the proofs of Proposition 7.7, l. 7016, and Theorem
  7.8, l. 7045) — `IsAhlforsRegular`
* Definition (Ahlfors-regular domain, l. 6932; used in Theorem 7.6, Proposition 7.7) — `IsAhlforsRegularDomain`
* Theorem 7.6 (Zinsmeister; cited at l. 7233, 7325, 7335) — `thm7_6`

Not items (DESIGN §3): "`f' ∈ H¹` by (6.3.10), so that `f` has a finite nonzero angular derivative almost everywhere"
(l. 6770; U−, a consequence of Ch. 6 facts; the existence of the boundary function is part of the conclusion of
`eq7_3_1` and of `HasSmirnovCondition`); "i.e. if the singular measure `μ` is zero" (the reading of (7.3.3) through
(7.3.1)); "but not vice versa (Dur72)" and "then (3) holds even with `f'` in place of `|f'|`" (l. 6798, not cited);
the example (7.3.5)–(7.3.7) of a non-Smirnov quasidisk (DuShSh66, KeLa37, Pir66's "Zygmund smooth" measure; an
example, cited only in the remark after Theorem 7.11; (7.3.7) prints "`z ∈ 𝕋`" for `ζ ∈ 𝕋` [misprint?]); "no geometric
characterization of the Smirnov condition is known" (a remark); the example `f(z) = (1 - z)²` after Proposition 7.5
(cited only in the remark after Theorem 7.8); the reformulation of (7.3.12) through `τ(z) = az + b`, (7.3.13) (Meyer,
Dav84) and "(7.3.12) implies `Λ(E) < ∞` for bounded `E`, not conversely" with its example (quoted or immediate, not
cited); "the weakest known geometric condition for Smirnov domains (Zin84)" (a remark); (7.3.14), (7.3.15) (steps of
the proof of Theorem 7.6); the problem (7.3.16) and its solution (BiJo90), and the literature (HayWu81, FeHa87,
FeZi87, FeHeMa89, Bae89, Dav84, Jo90) (quoted, not cited).

**Conventions.** As in §7.1. Standing assumption of §7.3 (l. 6770): `f` maps `𝔻` conformally onto `G ⊆ ℂ` with
`Λ(∂G) < ∞` (`G` need not be a Jordan domain); it is explicit in every statement. The boundary function `φ` of `f'`
(`IsAngularBoundaryFun (deriv f) φ`) stands for `f'(ζ)`; the integrals of `log |f'(ζ)|` are Bochner integrals whose
integrability, with `f'(ζ) ≠ 0` almost everywhere, is stated or follows from the hypotheses (the integrand is
`2π`-periodic, so integrability over `[0, 2π]` gives integrability over every arc), so that neither `Real.log 0 = 0`
nor the value `0` of a non-integrable integral enters; the integrals of `|f'(ζ)|^q` are lower integrals. `log f'` in
(7.3.1) is any branch `L`, with `b = arg f'(0) = Im L(0)`. "`G` is a Smirnov domain" in a hypothesis about a given `f`
is `Λ(∂G) < ∞` together with `HasSmirnovCondition f`, the book's reading (the definition refers to the given `f`;
its independence of `f` is Exercise 7.3.1); in conclusions it is `IsSmirnovDomain G`, which asks it for every `f`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- The boundary function of an analytic function `g` in `𝔻` (§7.3, l. 6770; helper): `φ(e^{it})` is the angular limit
of `g` at `e^{it}` for almost every `t` (Pommerenke's `HasAngularLimit` of §1.2, with a finite value).
Modelling: this is how the book's `f'(ζ)` (`ζ ∈ 𝕋`) enters Chapter 7, with `g = f'`; `φ` is determined almost
everywhere on `𝕋`, and its values on the remaining null set are free (no `limUnder`). -/
def IsAngularBoundaryFun (g φ : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) (φ (exp (t * I)) : ExtPlane)

/-- **Formula (7.3.1)** (§7.3; Dur70, p. 24; cited at P2 l. 2088). Let `f` map `𝔻` conformally onto `G ⊆ ℂ` with
`Λ(∂G) < ∞`. Since `f'` has no zeros there is a representation
`log f'(z) = ib + (1/2π) ∫_𝕋 (ζ + z)/(ζ - z) log |f'(ζ)| |dζ| - (1/2π) ∫_𝕋 (ζ + z)/(ζ - z) dμ(ζ)` for `z ∈ 𝔻`, where
`b = arg f'(0)` and where `μ` is a non-negative singular measure.
Modelling: the boundary values `f'(ζ)` are a boundary function `φ` (their existence almost everywhere, with
`f'(ζ) ≠ 0`, and the integrability of `log |f'(ζ)|` are part of the conclusion); `μ` is a finite measure on `𝕋`,
singular with respect to arc length; `log f'` is any holomorphic branch `L` of the logarithm of `f'` on `𝔻`, and
`b = arg f'(0)` is `Im L(0)` for that branch; `(ζ + z)/(ζ - z)` is `herglotzRieszKernel 0 z ζ`. -/
theorem eq7_3_1 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤) :
    ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ (∀ᵐ t : ℝ, φ (exp (t * I)) ≠ 0) ∧
      IntervalIntegrable (fun t : ℝ => Real.log ‖φ (exp (t * I))‖) volume 0 (2 * π) ∧
      ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ (sphere 0 1)ᶜ = 0 ∧ μ ⟂ₘ GarnettMarshall2005.arcMeasure ∧
        ∀ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc → (∀ z ∈ unitDisc, exp (L z) = deriv f z) →
          ∀ z ∈ unitDisc, L z = ((L 0).im : ℂ) * I +
            (1 / (2 * π) : ℂ) *
              (∫ t in (0 : ℝ)..2 * π, herglotzRieszKernel 0 z (exp (t * I)) * (Real.log ‖φ (exp (t * I))‖ : ℂ)) -
            (1 / (2 * π) : ℂ) * ∫ ζ, herglotzRieszKernel 0 z ζ ∂μ := by
  sorry

/-- **Formula (7.3.2)** (§7.3; cited in the proof of Proposition 7.5, l. 6904). Under the hypotheses of (7.3.1), it
follows that `log |f'(z)| = ∫_𝕋 p(z, ζ) log |f'(ζ)| |dζ| - ∫_𝕋 p(z, ζ) dμ(ζ)` for `z ∈ 𝔻`, where `p` is the Poisson
kernel.
Modelling: as in `eq7_3_1`; `p(z, ζ) = poissonKernel 0 z ζ / (2π)`. The measure `μ` is that of (7.3.1): it is
determined by this identity, since a measure on `𝕋` is determined by its Poisson integral. -/
theorem eq7_3_2 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤) :
    ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ (∀ᵐ t : ℝ, φ (exp (t * I)) ≠ 0) ∧
      IntervalIntegrable (fun t : ℝ => Real.log ‖φ (exp (t * I))‖) volume 0 (2 * π) ∧
      ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ (sphere 0 1)ᶜ = 0 ∧ μ ⟂ₘ GarnettMarshall2005.arcMeasure ∧
        ∀ z ∈ unitDisc, Real.log ‖deriv f z‖ =
          (∫ t in (0 : ℝ)..2 * π, poissonKernel 0 z (exp (t * I)) / (2 * π) * Real.log ‖φ (exp (t * I))‖) -
            ∫ ζ, poissonKernel 0 z ζ / (2 * π) ∂μ := by
  sorry

/-- **Definition (7.3.3)** (§7.3; used at l. 6796, 6798, 6826 and in the proof of Proposition 7.13, l. 7333). `f`
satisfies the Smirnov condition: `log |f'(z)| = ∫_𝕋 p(z, ζ) log |f'(ζ)| |dζ|` for `z ∈ 𝔻`.
Modelling: `f'(ζ)` is a boundary function `φ` of `f'` (`IsAngularBoundaryFun`), with `f'(ζ) ≠ 0` almost everywhere
and `log |f'(ζ)|` integrable over a period, so that the integral is genuine; `p(z, ζ) = poissonKernel 0 z ζ / (2π)`.
In the book's setting (`f` conformal, `Λ(∂G) < ∞`, so `f' ∈ H¹`) these side conditions always hold (they are part of
`eq7_3_1`), and the condition says that the singular measure `μ` of (7.3.1) is zero. The condition is applied to
conformal maps `f`, for which `f'(z) ≠ 0` in `𝔻`. -/
def HasSmirnovCondition (f : ℂ → ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ (∀ᵐ t : ℝ, φ (exp (t * I)) ≠ 0) ∧
    IntervalIntegrable (fun t : ℝ => Real.log ‖φ (exp (t * I))‖) volume 0 (2 * π) ∧
    ∀ z ∈ unitDisc, Real.log ‖deriv f z‖ =
      ∫ t in (0 : ℝ)..2 * π, poissonKernel 0 z (exp (t * I)) / (2 * π) * Real.log ‖φ (exp (t * I))‖

/-- **Formula (7.3.4)** (§7.3; Gar81, p. 15; cited in the proof of Proposition 7.4, l. 6852). If `f` satisfies the
Smirnov condition, then `∫_𝕋 |log |f'(ρz)| - log |f'(z)|| |dz| → 0` as `ρ → 1-`.
Modelling: under the standing assumption of §7.3; `f'(z)` on `𝕋` is any boundary function `φ` of `f'` (all agree
almost everywhere); the integral is a lower integral in `ℝ≥0∞` over the parameter interval `[0, 2π]`. -/
theorem eq7_3_4 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤)
    (hS : HasSmirnovCondition f) {φ : ℂ → ℂ} (hφ : IsAngularBoundaryFun (deriv f) φ) :
    Tendsto (fun ρ : ℝ => ∫⁻ t in Icc 0 (2 * π),
        ‖Real.log ‖deriv f (ρ * exp (t * I))‖ - Real.log ‖φ (exp (t * I))‖‖ₑ) (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Definition** (§7.3, l. 6796; used in Propositions 7.4, 7.5, Theorems 7.6, 7.11 and at P2 l. 2088). `G` is a
Smirnov domain: `Λ(∂G) < ∞` and the Smirnov condition (7.3.3) is satisfied.
Modelling: the book states (7.3.3) for the map `f` of `𝔻` onto `G` of the standing assumption; that it does not
depend on the choice of `f` is Exercise 7.3.1 (not an item). The definition asks for a conformal map of `𝔻` onto `G`
and requires the condition for every such map (the leader-approved form, Q7.2); a hypothesis about a given `f` is
stated with `HasSmirnovCondition f` instead (see the file header). -/
def IsSmirnovDomain (G : Set ℂ) : Prop :=
  μH[1] (frontier G) < ⊤ ∧ (∃ f : ℂ → ℂ, IsConformalOnto f unitDisc G) ∧
    ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc G → HasSmirnovCondition f

/-- **Unlabelled claim** (§7.3, l. 6798; used in the proof of Proposition 7.13, l. 7333). The Smirnov condition holds
if `log f' ∈ H¹`.
Modelling: under the standing assumption of §7.3; `log f'` is a holomorphic branch `L` of the logarithm of `f'`
(membership in `H¹` does not depend on the branch); `H¹` is `GarnettMarshall2005.MemHardy 1`. -/
theorem hasSmirnovCondition_of_log_mem_H1 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G)
    (hΛ : μH[1] (frontier G) < ⊤) {L : ℂ → ℂ} (hL : GarnettMarshall2005.MemHardy 1 L)
    (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) : HasSmirnovCondition f := by
  sorry

/-- **Proposition 7.4** (§7.3; (7.3.9); cited in the proof of Theorem 7.11, l. 7237, 7245). If `f` maps `𝔻`
conformally onto a Smirnov domain then, for `z ∈ 𝔻`,
`|(1/Λ(I(z))) ∫_{I(z)} log |f'(ζ)| |dζ| - log |f'(z)|| ≤ K₁`.
Modelling: `K₁` is absolute (`∃ K₁, ∀ f z`); "onto a Smirnov domain" is `Λ(∂G) < ∞` with the Smirnov condition for the
given `f` (see the file header); `f'(ζ)` is any boundary function `φ` of `f'`; the mean over `I(z)` is the average
over its parameter interval (length `Λ(I(z)) = 2π(1 - |z|)`), a Bochner average of an integrable function (the
Smirnov condition gives the integrability of `log |f'(ζ)|`). -/
theorem prop7_4 : ∃ K₁ : ℝ, ∀ (f : ℂ → ℂ) (G : Set ℂ), IsConformalOnto f unitDisc G → μH[1] (frontier G) < ⊤ →
    HasSmirnovCondition f → ∀ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ → ∀ z ∈ unitDisc,
      |(⨍ t in Icc (arg z - π * (1 - ‖z‖)) (arg z + π * (1 - ‖z‖)), Real.log ‖φ (exp (t * I))‖) -
        Real.log ‖deriv f z‖| ≤ K₁ := by
  sorry

/-- **Condition (7.3.10)** (§7.3; = (7.1.4); with `q = 1` it is (7.4.2), and it is (7.5.8), (7.5.9), (7.5.13); cited
in the statement of Theorem 7.6; helper). For some constant `M₁`,
`(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^q |dζ| ≤ M₁ |f'(z)|^q` for `z ∈ 𝔻`.
Modelling: `f'(ζ)` is a boundary function `φ` of `f'` (`IsAngularBoundaryFun`; the mean does not see the choice);
the mean over `I(z)` is the `ℝ≥0∞`-average over its parameter interval, and the powers are `ℝ≥0∞`-powers, so that a
negative exponent `q = -δ` gives the book's (7.5.9), `(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^{-δ} |dζ| ≤ M₇ |f'(z)|^{-δ}`, with
`0^{-δ} = ∞` (for a conformal `f`, `f'(z) ≠ 0` in `𝔻`, so the right side is finite). `M₁` depends on `f` and `q`. -/
def HasArcMeanBound (f : ℂ → ℂ) (q : ℝ) : Prop :=
  ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ ∃ M₁ : ℝ, ∀ z ∈ unitDisc,
    ⨍⁻ t in Icc (arg z - π * (1 - ‖z‖)) (arg z + π * (1 - ‖z‖)), ‖φ (exp (t * I))‖ₑ ^ q ∂volume ≤
      ENNReal.ofReal M₁ * ‖deriv f z‖ₑ ^ q

/-- **Proposition 7.5** (§7.3; (7.3.10); cited in the proofs of Theorems 7.6, 7.11 and Exercise 7.4.2), first part.
Let `f` map `𝔻` conformally onto `G` with `Λ(∂G) < ∞`. Suppose that `q > 0` and
`(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)|^q |dζ| ≤ M₁ |f'(z)|^q` for `z ∈ 𝔻`. Then `G` is a Smirnov domain.
Modelling: the conclusion `IsSmirnovDomain G` is the form "for every conformal map onto `G`", which is equivalent to
the book's condition for the given `f` by Exercise 7.3.1 (see `IsSmirnovDomain`). -/
theorem prop7_5_a {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤)
    {q : ℝ} (hq : 0 < q) (h10 : HasArcMeanBound f q) : IsSmirnovDomain G := by
  sorry

/-- **Proposition 7.5** (§7.3; (7.3.11); cited in the proofs of Theorems 7.6, 7.11 and Exercise 7.4.2), second part.
Under the hypotheses of `prop7_5_a`, if `0 < q < 1` then furthermore
`∫_𝕋 p(z, ζ) |f'(ζ)|^q |dζ| ≤ M₂ |f'(z)|^q` for `z ∈ 𝔻`; if `G` is in addition linearly connected, then (7.3.10)
implies (7.3.11) for `0 < q ≤ 1`.
Modelling: `f'(ζ)` is a boundary function `φ` of `f'`; the integral is a lower integral over the parameter interval,
with `p(z, ζ) = poissonKernel 0 z ζ / (2π)`; `M₂` depends on `f` and `q`. -/
theorem prop7_5_b {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤)
    {q : ℝ} (hq : 0 < q) (h10 : HasArcMeanBound f q) (hq1 : q < 1 ∨ (IsLinearlyConnected G ∧ q ≤ 1)) :
    ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ ∃ M₂ : ℝ, ∀ z ∈ unitDisc,
      ∫⁻ t in Icc 0 (2 * π), ENNReal.ofReal (poissonKernel 0 z (exp (t * I)) / (2 * π)) * ‖φ (exp (t * I))‖ₑ ^ q ≤
        ENNReal.ofReal M₂ * ‖deriv f z‖ₑ ^ q := by
  sorry

/-- **Definition (7.3.12)** (§7.3; = (7.1.2); cited in the proofs of Proposition 7.7, l. 7016, and Theorem 7.8,
l. 7045). The curve `C ⊆ ℂ` is Ahlfors-regular: `Λ(C ∩ D(w, r)) ≤ M₁ r` for `w ∈ ℂ`, `0 < r < ∞`.
Modelling: stated for any set `C ⊆ ℂ` (only the point set enters, and it is applied to `∂G`, which need not be a
curve); `D(w, r)` is the open disc `ball w r`; `Λ` is `μH[1]`; `M₁` depends on `C`. -/
def IsAhlforsRegular (C : Set ℂ) : Prop :=
  ∃ M₁ : ℝ, ∀ w : ℂ, ∀ r : ℝ, 0 < r → μH[1] (C ∩ ball w r) ≤ ENNReal.ofReal (M₁ * r)

/-- **Definition** (§7.3, l. 6932; used in Theorem 7.6 and Proposition 7.7). `G` is an Ahlfors-regular domain: `∂G`
is (locally connected and) Ahlfors-regular.
Modelling: `G` is a domain of `ℂ` (open and connected); local connectedness of the closed set `∂G` is `IsLocConn` of
§2.2. -/
def IsAhlforsRegularDomain (G : Set ℂ) : Prop :=
  IsOpen G ∧ IsConnected G ∧ IsLocConn (frontier G) ∧ IsAhlforsRegular (frontier G)

/-- **Theorem 7.6** (§7.3; Zinsmeister; cited at l. 7233, 7325, 7335). Let `f` map `𝔻` conformally onto an
Ahlfors-regular domain `G`. Then (7.3.10) holds for `q < 1/3` so that `G` is a Smirnov domain.
Standing assumption of §7.3 (l. 6770, "let the linear measure `Λ(∂G)` be finite"): `hΛ`, explicit here as in every
§7.3 statement; Theorem 7.6 lies in §7.3, and its proof uses the boundary values `f'(ζ)`, which exist by it. It
cannot be dropped: the upper half-plane is an Ahlfors-regular domain (`∂G = ℝ` is locally connected and
`Λ(ℝ ∩ D(w, r)) ≤ 2r`) with `Λ(∂G) = ∞`, whereas a Smirnov domain has `Λ(∂G) < ∞` by definition.
Modelling: "for `q < 1/3`" is for every `0 < q < 1/3` (the exponents of (7.3.10) in Proposition 7.5 are positive). -/
theorem thm7_6 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) (hΛ : μH[1] (frontier G) < ⊤)
    (hG : IsAhlforsRegularDomain G) :
    (∀ q : ℝ, 0 < q → q < 1 / 3 → HasArcMeanBound f q) ∧ IsSmirnovDomain G := by
  sorry

end Pommerenke1992
