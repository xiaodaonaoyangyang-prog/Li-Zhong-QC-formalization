import References.GarnettMarshall2005.Ch04.S06_ThetaIntegralEstimate
import References.GarnettMarshall2005.Ch03.S09_EstimatesHarmonicMeasure

/-!
# Garnett–Marshall, Chapter V §1: Asymptotic values of entire functions

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V, introduction and
§1 (pp. 156–158; `full.md` P1:6749–6842).

Conventions of Chapter V §1, as modelled here. An entire function is a map `f : ℂ → ℂ` that is complex
differentiable everywhere. A Jordan arc tending to `∞` is the image `γ([0, 1))` of a continuous one-to-one map
`γ : [0, 1) → ℂ` with `|γ(t)| → ∞` as `t → 1` (`IsArcToInfty`; such a map is proper, hence a closed embedding, so the
image is a Jordan arc). The limit `lim_{Γ ∋ z → ∞} f(z) = a` is the limit along the filter of the points of `Γ`
tending to `∞` (the cocompact filter of `ℂ` restricted to `Γ`), with values in `ℂ*`: an asymptotic value may be `∞`,
which is why Theorem 1.1 speaks of "finite" asymptotic values (as in Pommerenke's definition,
Pommerenke1992.HasAsymptoticValue, which is the notion for functions on the disc along curves ending on the unit
circle, not this one). `M(r) = sup_{|z| = r} |f(z)|` is `maxModulus f r`.

* Definition (asymptotic value of an entire function, §1, P1:6755–6759) — `HasAsymptoticValue` (with the helper
  `IsArcToInfty`)
* Notation (`M(r)`, the maximum of `|f(z)|` on `{|z| = r}`, §1, P1:6769–6773) — `maxModulus`
* Theorem 1.1 (§1; (1.1)) — `thm5_1_1`

Helpers (not book notions): `IsArcToInfty` (a Jordan arc of the plane tending to `∞`), `maxModulus` (the notation
`M(r)`).

Not stated (inventory U−): the chapter introduction (P1:6751, an overview of §1–§6); the example
`f(z) = ∫_0^z e^{−wⁿ} dw` with `n` distinct asymptotic values, one along each ray `arg z = 2πj/n` (P1:6761–6767, not
cited later).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane)

/-- A Jordan arc of the plane tending to `∞` (helper, Ch. V §1, P1:6755): `Γ = γ([0, 1))` for a continuous
one-to-one map `γ : [0, 1) → ℂ` with `|γ(t)| → ∞` as `t → 1⁻`. -/
def IsArcToInfty (Γ : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Ico 0 1) ∧ InjOn γ (Ico 0 1) ∧ Tendsto (fun t => ‖γ t‖) (𝓝[<] 1) atTop ∧
    Γ = γ '' Ico 0 1

/-- **Definition** (asymptotic value, Ch. V §1, P1:6755–6759). An entire function `f(z)` has asymptotic value `a`
if there is a Jordan arc `Γ` tending to `∞` such that `lim_{Γ ∋ z → ∞} f(z) = a`.
Modelling: `a ∈ ℂ*` (the value `∞` is allowed; Theorem 1.1 counts the finite asymptotic values `a = ↑c`); the limit
is taken along the points of `Γ` tending to `∞` (`cocompact ℂ ⊓ 𝓟 Γ`), with `f(z)` read in `ℂ*`. The function need
not be entire for the definition; every statement assumes it. -/
def HasAsymptoticValue (f : ℂ → ℂ) (a : ExtPlane) : Prop :=
  ∃ Γ : Set ℂ, IsArcToInfty Γ ∧ Tendsto (fun z => (f z : ExtPlane)) (cocompact ℂ ⊓ 𝓟 Γ) (𝓝 a)

/-- The maximum modulus (helper for the notation of Ch. V §1, P1:6769–6773): `M(r) = sup_{|z| = r} |f(z)|`, the
maximum of `|f(z)|` on `{|z| = r}`. A real supremum, attained for continuous `f` and `r ≥ 0`; junk `0` for `r < 0`
(empty circle), never used: only `r → ∞` is read. -/
def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere 0 r)

/-- **Theorem 1.1** (Ch. V §1), (1.1) (Denjoy's conjecture, Ahlfors' theorem; cited at P1:6841, in the Notes, P2:419,
in Exercise 1, P2:429, 447, as a template in Chapter VI, P2:1430, and in App. G, P3:4558). If the non-constant
entire function `f(z)` has `n` distinct finite asymptotic values, then
(1.1) `liminf_{r→∞} log M(r) / r^{n/2} > 0`.
Modelling: "`n` distinct finite asymptotic values" is an injective family `a : Fin n → ℂ` of asymptotic values (so
at least `n`; for `n = 0` the claim is `log M(r) ≥ c` for large `r`, true for non-constant `f`); "non-constant" is
`∃ z w, f z ≠ f w`. The liminf, which may be `+∞`, is positive exactly when `log M(r) ≥ c r^{n/2}` for some `c > 0`
and all large `r`: this form reads no `Filter.liminf` junk, and `M(r) > 0` for large `r` (`f` is not constant), so
no `log 0` is read either. The exponent was checked against the equation image. -/
theorem thm5_1_1 {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnc : ∃ z w, f z ≠ f w) {n : ℕ} {a : Fin n → ℂ}
    (ha : Function.Injective a) (hav : ∀ j, HasAsymptoticValue f (a j)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ ((n : ℝ) / 2) ≤ Real.log (maxModulus f r) := by
  sorry

end GarnettMarshall2005
