import References.Pommerenke1992.Ch07.S01_Overview

/-!
# Pommerenke 1992, Ch. 7 §7.2 Integrals of Bloch Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 7 *Smirnov and Lavrentiev Domains*, §7.2;
source `full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 6636–6767.

* Definition (the integral `h` of a Bloch function `g`, (7.2.1); cited at l. 6840, 6846 and P2 l. 2897, restated as
  (11.2.8)) — `blochIntegral`
* Proposition 7.1 ((7.2.2); cited in the proofs of Theorem 7.2, l. 6686, and Proposition 7.4, l. 6840) — `prop7_1`
* Theorem 7.2 (Zyg45; (7.2.4); cited in the proof of Proposition 7.3, l. 6750, and as a method at P2 l. 2903) —
  `thm7_2`
* Remark after Theorem 7.2 (l. 6712; cited in the proof of Proposition 7.3, "the remark after its proof") —
  `thm7_2_im`
* Definition (Zygmund measure, (7.2.6); cited at l. 6808, P2 l. 2317, in the statement of Theorem 10.12 and in the
  proof of Theorem 10.14; the increasing function `μ*`, helper) — `IsZygmundMeasure`, `measureDistFn`
* Formula (7.2.7) (cited in the proof of Proposition 7.3, l. 6750, and at l. 6808) — `eq7_2_7`
* Proposition 7.3 (DuShSh66; (7.2.8); cited at l. 6808 and P2 l. 2333, 2419) — `prop7_3`

Not items (DESIGN §3): (7.2.3) (a step of the proof of Proposition 7.1); the facts quoted inside proofs (`h` is
Hölder-continuous, Dur70 p. 74; the Herglotz representation of functions of positive real part, Dur70 p. 3); the
Zygmund class `Λ_*` and (7.2.5) (U−: "we easily obtain", not cited; the class, used only there, is the Zygmund class
`GarnettMarshall2005.MemZygmund` of GM Ch. II §3); "these will also be needed in Section 10.4" (a remark).

**Conventions.** As in §7.1. Functions analytic in `𝔻` are `g : ℂ → ℂ` with `DifferentiableOn ℂ g unitDisc`;
`‖g‖_B` is `blochSeminorm g` (Ch. 4, `ℝ≥0∞`-valued; `(blochSeminorm g).toReal` for a Bloch function). "`h` is
continuous in `𝔻̄`" is the existence of a continuous extension `H` of `h` from `𝔻` to `𝔻̄` (`ContinuousOn H
(closedBall 0 1)`, `EqOn H h unitDisc`; it is unique, `𝔻` being dense in `𝔻̄`), so that no value of the integral on `𝕋`
enters (Q7.11). The constants `K₁, K₂, …` are absolute (`∃ K, ∀ g`); `M₁, M₂, …` depend on the data. A measure on `𝕋`
is a measure `μ` on `ℂ` with `μ(ℂ ∖ 𝕋) = 0`; the adjacent arcs of equal length `t` at `e^{iϑ}` are `arcT ϑ (ϑ + t)` and
`arcT (ϑ - t) ϑ` (`0 < t ≤ π`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- **Definition (7.2.1)** (§7.2; cited at l. 6840, 6846 and P2 l. 2897). For `g` analytic in `𝔻`,
`h(z) = ∫₀^z (g(ζ) - g(0)) ζ⁻¹ dζ` (`z ∈ 𝔻`).
Modelling: the integral along the segment `[0, z]`, `ζ = tz`: `h(z) = ∫₀¹ (g(tz) - g(0))/t dt` (the integrand tends
to `g'(0) z` as `t → 0`; its value at `t = 0` is irrelevant). Junk: the values for `|z| ≥ 1`, where the integral need
not converge; the statements use the continuous extension `H` of `h` to `𝔻̄` instead (see the file header). -/
def blochIntegral (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (g (t * z) - g 0) / t

/-- **Proposition 7.1** (§7.2; (7.2.2); cited in the proofs of Theorem 7.2, l. 6686, and Proposition 7.4, l. 6840).
If `g ∈ B` then `h` is continuous in `𝔻̄` and, for `|z| ≤ 1`, `0 < |t| ≤ π`,
`|(h(e^{it}z) - h(z))/(it) - g((1 - |t|/π)z) + g(0)| ≤ K₁ ‖g‖_B`.
Modelling: `K₁` is absolute (`∃ K₁, ∀ g`); `h` on `𝔻̄` is its continuous extension `H`. For `|z| ≤ 1` and
`0 < |t| ≤ π` the point `(1 - |t|/π)z` lies in `𝔻`. -/
theorem prop7_1 : ∃ K₁ : ℝ, ∀ g : ℂ → ℂ, IsBloch g →
    ∃ H : ℂ → ℂ, ContinuousOn H (closedBall 0 1) ∧ EqOn H (blochIntegral g) unitDisc ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, ∀ t : ℝ, 0 < |t| → |t| ≤ π →
        ‖(H (exp (t * I) * z) - H z) / (t * I) - g ((1 - |t| / π) * z) + g 0‖ ≤
          K₁ * (blochSeminorm g).toReal := by
  sorry

/-- **Theorem 7.2** (§7.2; Zyg45; (7.2.4); cited in the proof of Proposition 7.3, l. 6750). Let `g` be analytic in
`𝔻`. Then `g ∈ B` if and only if `h` is continuous in `𝔻̄` and
`max_{|z|=1} |h(e^{it}z) + h(e^{-it}z) - 2h(z)| ≤ M₁ t` for `t > 0`.
Modelling: `h` on `𝔻̄` is its continuous extension `H` (see the file header); the maximum over `|z| = 1` is a bound
for every `z ∈ 𝕋`; `M₁` depends on `g`. -/
theorem thm7_2 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) :
    IsBloch g ↔ ∃ H : ℂ → ℂ, ContinuousOn H (closedBall 0 1) ∧ EqOn H (blochIntegral g) unitDisc ∧
      ∃ M₁ : ℝ, ∀ z ∈ sphere (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        ‖H (exp (t * I) * z) + H (exp (-(t * I)) * z) - 2 * H z‖ ≤ M₁ * t := by
  sorry

/-- **Remark after Theorem 7.2** (§7.2, l. 6712; cited in the proof of Proposition 7.3, "the remark after its
proof"). Let `g` be analytic in `𝔻`. If we only assume the condition of Theorem 7.2 with `h` replaced by `Im h`
(`Im h` continuous in `𝔻̄` and (7.2.4) for `Im h`), then `(1 - r²)|Im[e^{iϑ} g'(re^{iϑ})]| ≤ K₅ M₁` (`0 < r < 1`),
and this is enough to conclude that `g ∈ B` (Exercise 4.2.6).
Modelling: `K₅` is absolute (`∃ K₅, ∀ g V M₁`); `Im h` on `𝔻̄` is its continuous extension `V : ℂ → ℝ`. Only `Im h` is
assumed continuous in `𝔻̄`: in the one use, the proof of Proposition 7.3 (l. 6750), `Im h(e^{it}) = a + 2πμ*(t) - t`
is continuous, while the continuity of `Re h` is not known before `g ∈ B` is established. -/
theorem thm7_2_im : ∃ K₅ : ℝ, ∀ (g : ℂ → ℂ) (V : ℂ → ℝ) (M₁ : ℝ), DifferentiableOn ℂ g unitDisc →
    ContinuousOn V (closedBall 0 1) → EqOn V (fun z => (blochIntegral g z).im) unitDisc →
    (∀ z ∈ sphere (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      |V (exp (t * I) * z) + V (exp (-(t * I)) * z) - 2 * V z| ≤ M₁ * t) →
    (∀ r ϑ : ℝ, 0 < r → r < 1 → (1 - r ^ 2) * |(exp (ϑ * I) * deriv g (r * exp (ϑ * I))).im| ≤ K₅ * M₁) ∧
      IsBloch g := by
  sorry

/-- **Definition (7.2.6)** (§7.2; cited at l. 6808, P2 l. 2317, in the statement of Theorem 10.12 and in the proof of
Theorem 10.14). The non-negative finite measure `μ` on `𝕋` is a Zygmund measure: `|μ(I) - μ(I')| ≤ M₂ Λ(I)`, where
`I` and `I'` are adjacent arcs of equal length.
Modelling: `μ` is a finite measure on `ℂ` with `μ(ℂ ∖ 𝕋) = 0`; the adjacent arcs of length `t` at the common endpoint
`e^{iϑ}` are the closed arcs `arcT ϑ (ϑ + t)` and `arcT (ϑ - t) ϑ`, `0 < t ≤ π` (two adjacent arcs of equal length
fit into `𝕋`). The condition excludes atoms, so open or closed arcs give the same notion. `M₂` depends on `μ`. -/
def IsZygmundMeasure (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ μ (sphere 0 1)ᶜ = 0 ∧ ∃ M₂ : ℝ, ∀ ϑ t : ℝ, 0 < t → t ≤ π →
    |(μ (arcT ϑ (ϑ + t))).toReal - (μ (arcT (ϑ - t) ϑ)).toReal| ≤ M₂ * t

/-- The increasing function `μ*(t) = μ({e^{iτ} : 0 ≤ τ ≤ t})` of a finite measure `μ` on `𝕋` (§7.2, l. 6718; helper
for (7.2.7)).
Modelling: the book's formula for `0 ≤ t < 2π`, extended to all `t ∈ ℝ` by `μ*(t + 2π) = μ*(t) + μ(𝕋)`, since (7.2.7)
evaluates `μ*(ϑ ± t)` for all `ϑ` and `t > 0`: `μ*(t) = ⌊t/2π⌋ μ(𝕋) + μ(arcT 0 (t - 2π⌊t/2π⌋))`. -/
def measureDistFn (μ : Measure ℂ) (t : ℝ) : ℝ :=
  (⌊t / (2 * π)⌋ : ℝ) * (μ (sphere 0 1)).toReal + (μ (arcT 0 (t - 2 * π * ⌊t / (2 * π)⌋))).toReal

/-- **Formula (7.2.7)** (§7.2; cited in the proof of Proposition 7.3, l. 6750, and at l. 6808). For a Zygmund measure
`μ` the increasing function `μ*` is continuous, and (7.2.6) can be written as
`|μ*(ϑ + t) + μ*(ϑ - t) - 2μ*(ϑ)| ≤ M₂ t` for `t > 0`.
Modelling: for a finite measure `μ` on `𝕋`: `μ` is a Zygmund measure if and only if `μ*` is continuous and satisfies
(7.2.7) (for all `ϑ ∈ ℝ`) with some constant; this contains both claims. -/
theorem eq7_2_7 {μ : Measure ℂ} (hμ : IsFiniteMeasure μ) (hμT : μ (sphere 0 1)ᶜ = 0) :
    IsZygmundMeasure μ ↔ Continuous (measureDistFn μ) ∧ ∃ M₂ : ℝ, ∀ ϑ t : ℝ, 0 < t →
      |measureDistFn μ (ϑ + t) + measureDistFn μ (ϑ - t) - 2 * measureDistFn μ ϑ| ≤ M₂ * t := by
  sorry

/-- **Proposition 7.3** (§7.2; DuShSh66; (7.2.8); cited at l. 6808 and P2 l. 2333, 2419). The function `g` belongs to
`B` and satisfies `Re g(z) > 0` (`z ∈ 𝔻`) if and only if it can be represented as
`g(z) = ib + ∫_𝕋 (ζ + z)/(ζ - z) dμ(ζ)` (`z ∈ 𝔻`), where `μ` is a Zygmund measure and `b ∈ ℝ`.
[CORRECTION] `μ ≠ 0` is added on the right: the zero measure is a Zygmund measure by (7.2.6) and gives `g = ib`, with
`Re g = 0`, so the literal "if" direction fails. The uses are unaffected: the example (7.3.6) has a nonzero measure;
the proof of Theorem 10.12 (P2 l. 2333) applies "if" to an arbitrary Zygmund measure, and for `μ = 0` its conclusion
`μ(E) = 0` is trivial; the proof of Theorem 10.14 (P2 l. 2419) uses "only if".
Modelling: `(ζ + z)/(ζ - z)` is Mathlib's `herglotzRieszKernel 0 z ζ`, integrated against `μ` on `ℂ` (bounded on `𝕋`
for `z ∈ 𝔻`, and `μ` lives on `𝕋`); only the values of `g` on `𝔻` enter. -/
theorem prop7_3 {g : ℂ → ℂ} :
    (IsBloch g ∧ ∀ z ∈ unitDisc, 0 < (g z).re) ↔
      ∃ μ : Measure ℂ, IsZygmundMeasure μ ∧ μ ≠ 0 ∧ ∃ b : ℝ, ∀ z ∈ unitDisc,
        g z = b * I + ∫ ζ, herglotzRieszKernel 0 z ζ ∂μ := by
  sorry

end Pommerenke1992
