import References.GarnettMarshall2005.Ch04.S04_ExtremalMetricsExtremalDistance
import References.Common.ExtPlaneBorel

/-!
# Garnett–Marshall, Chapter IV §5: Extremal distance and harmonic measure

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §5 (pp. 143–146;
`full.md` P1:6260–6391).

Conventions of Chapter IV as in §1. The results of §5 are stated for Jordan domains ("Let `Ω` be a Jordan domain"),
so harmonic measure is the Jordan-domain harmonic measure of Ch. I §3, `harmonicMeasureJordan Ω z₀ : Measure ℂ*`
(leader ruling B5: the explicit earlier setting); the rectangle `R_L` of Lemma 5.1 is a Jordan domain. The number
`ω(z₀, E, Ω)` is `(harmonicMeasureJordan Ω z₀ E).toReal` (a finite measure), since real arithmetic with `exp`
follows. Extremal distances of a Jordan domain are taken on finite parts. `λ(z₀, E)` is `extremalDistPointArc`,
with values in `[0, ∞]`; the statements prove or assume `λ(z₀, E) < ∞` before reading it as a real number.

* Lemma 5.1 (§5; (5.1), (5.2)) — `lemma4_5_1_a`, `lemma4_5_1_b`
* Definition (`λ(z₀, E)` for an arc `E` of `∂Ω`, P1:6320–6326, and for a finite union of arcs, P1:6370–6374, §5) —
  `extremalDistPointArc`
* Theorem 5.2 (§5) — `thm4_5_2_a`, `thm4_5_2_b`
* Theorem 5.3 (§5; (5.5)) — `thm4_5_3`

Not stated (inventory U−): the improvement of the lower bound in (5.1) to `(.93)(8/π) e^{−πL/2}` for `L ≥ 1` and the
better bounds for `L < 1` via `ω(0, E_{1/L}, R_{1/L}) = 1 − ω(0, E_L, R_L)` (P1:6280, a remark pointing to
Exercise 10); the conformal invariance and the strict monotonicity of `λ(z₀, E)` and `ω(z₀, E, Ω)` in `E`
(P1:6331, a remark; the monotonicity of `λ` is the extension rule); the remark after Theorem 5.2 that every arc `σ`
and every metric `ρ` give an upper bound for `ω(z₀, E, Ω)` (P1:6345, Beurling's idea); the remark that Theorem 5.3
has no lower bound (P1:6390, Exercise 12). (5.3), (5.4) are steps of the proof of Lemma 5.1.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt)
open LehtoVirtanen1973 (IsJordanArc IsArcFromTo)
open References (IsJordanDomainExt finitePart)

/-- **Lemma 5.1** (Ch. IV §5), (5.1) (cited at P1:6364, in the Notes, P1:6500, and in Exercises 10, 11). Set
`R_L = {z : |Re z| < L and |Im z| < 1}`. If `E_L = {z ∈ ∂R_L : |Re z| = L}` is the union of the vertical edges of
`R_L`, then (5.1) `e^{−(π/2)L} ≤ ω(0, E_L, R_L) ≤ (8/π) e^{−(π/2)L}`.
Modelling: `L > 0` (for `L ≤ 0` the rectangle is empty); `R_L` is the Jordan domain `toExt R_L` of `ℂ*` and `ω` is
`harmonicMeasureJordan` at the point `0`; the constants were checked against the equation image. -/
theorem lemma4_5_1_a {L : ℝ} (hL : 0 < L) {R_L E_L : Set ℂ} (hR : R_L = Ioo (-L) L ×ℂ Ioo (-1) 1)
    (hE : E_L = {-L, L} ×ℂ Icc (-1) 1) :
    Real.exp (-(π / 2) * L) ≤ (harmonicMeasureJordan (toExt R_L) ((0 : ℂ) : ExtPlane) (toExt E_L)).toReal ∧
      (harmonicMeasureJordan (toExt R_L) ((0 : ℂ) : ExtPlane) (toExt E_L)).toReal ≤
        8 / π * Real.exp (-(π / 2) * L) := by
  sorry

/-- **Lemma 5.1** (Ch. IV §5), (5.2). The estimates in (5.1) are sharp, because
(5.2) `lim_{L→∞} ω(0, E_L, R_L) e^{(π/2)L} = 8/π` and `lim_{L→0} ω(0, E_L, R_L) e^{(π/2)L} = 1`.
Modelling: `ω(0, E_L, R_L)` as in `lemma4_5_1_a`, as a function of `L`; `L → 0` is `L → 0⁺` (`R_L` is defined for
`L > 0`), and both filters see only `L > 0`; (5.2) is part of the lemma's statement block (P1:6274–6278). -/
theorem lemma4_5_1_b :
    Tendsto (fun L : ℝ => (harmonicMeasureJordan (toExt (Ioo (-L) L ×ℂ Ioo (-1) 1)) ((0 : ℂ) : ExtPlane)
        (toExt ({-L, L} ×ℂ Icc (-1) 1))).toReal * Real.exp (π / 2 * L)) atTop (𝓝 (8 / π)) ∧
      Tendsto (fun L : ℝ => (harmonicMeasureJordan (toExt (Ioo (-L) L ×ℂ Ioo (-1) 1)) ((0 : ℂ) : ExtPlane)
        (toExt ({-L, L} ×ℂ Icc (-1) 1))).toReal * Real.exp (π / 2 * L)) (𝓝[>] 0) (𝓝 1) := by
  sorry

/-- **Definition** (`λ(z₀, E)`, Ch. IV §5, P1:6320–6326 and P1:6370–6374). Let `Ω` be a Jordan domain, let `E` be
an arc (or a finite union of arcs) on `∂Ω` and let `z₀ ∈ Ω`. Consider all Jordan arcs `σ ⊆ Ω` that join `z₀` to
`∂Ω \ E`, and define `λ(z₀, E) = sup_σ d_{Ω \ σ}(σ, E)`, the supremum being taken over all such Jordan arcs.
Modelling: `σ = C \ {p}` for a closed Jordan arc `C` of `ℂ*` from `z₀` to `p ∈ ∂Ω \ E` (LV `IsArcFromTo`) with
`C \ {p} ⊆ Ω`, so that `Ω \ σ = Ω \ C`; `d_{Ω \ σ}(σ, E)` is taken on finite parts (Chapter IV is planar). The
supremum over no arcs is `0` (e.g. for `E = ∂Ω`); outside the book's setting (`z₀ ∉ Ω`) the value is not used. -/
def extremalDistPointArc (Ω : Set ExtPlane) (z₀ : ExtPlane) (E : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (C : Set ExtPlane) (p : ExtPlane) (_ : IsArcFromTo C z₀ p ∧ p ∈ frontier Ω \ E ∧ C \ {p} ⊆ Ω),
    extremalDistGM (finitePart (Ω \ C)) (finitePart (C \ {p})) (finitePart E)

/-- **Theorem 5.2** (Ch. IV §5), the two-sided estimate (cited at P1:6345, 6382, in Chapter V, P1:6919 "the
result now follows from Theorem IV.5.2", and P2:519). Let `Ω` be a Jordan domain, let `E` be a
subarc of `∂Ω` and let `z₀ ∈ Ω`. Then `e^{−πλ(z₀, E)} ≤ ω(z₀, E, Ω) ≤ (8/π) e^{−πλ(z₀, E)}`.
Modelling: `E` is a Jordan arc of `ℂ*` (LV `IsJordanArc`, any kind of parameter interval) contained in `∂Ω`;
`λ(z₀, E) < ∞` is part of the conclusion: it follows from the upper bound, since `ω(z₀, E, Ω) > 0` for an arc, so
reading `λ` as a real number is faithful. The constants were checked against the equation image. -/
theorem thm4_5_2_a {Ω E : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) (hE : IsJordanArc E) (hEΩ : E ⊆ frontier Ω)
    {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    extremalDistPointArc Ω z₀ E < ⊤ ∧
      Real.exp (-π * (extremalDistPointArc Ω z₀ E).toReal) ≤ (harmonicMeasureJordan Ω z₀ E).toReal ∧
      (harmonicMeasureJordan Ω z₀ E).toReal ≤ 8 / π * Real.exp (-π * (extremalDistPointArc Ω z₀ E).toReal) := by
  sorry

/-- **Theorem 5.2** (Ch. IV §5), the limits. Moreover
`lim_{λ→∞} ω(z₀, E, Ω) e^{πλ(z₀, E)} = 8/π` and `lim_{λ→0} ω(z₀, E, Ω) e^{πλ(z₀, E)} = 1`.
Modelling: both quantities are conformally invariant and `ω` is a function of `λ` ("there is a function connecting
`λ` to `ω`", P1:6331), and the limits are those of this function; they are stated uniformly over all configurations
`(Ω, E, z₀)` of the theorem (equivalently, along every sequence of configurations with `λ → ∞`, resp. `λ → 0`). The
hypothesis `λ(z₀, E) < ∞` holds for every configuration (`thm4_5_2_a`) and is repeated so that `λ` is read as a real
number only where it is finite. -/
theorem thm4_5_2_b :
    (∀ ε > 0, ∃ Λ : ℝ, ∀ (Ω E : Set ExtPlane) (z₀ : ExtPlane), IsJordanDomainExt Ω → IsJordanArc E →
      E ⊆ frontier Ω → z₀ ∈ Ω → extremalDistPointArc Ω z₀ E < ⊤ →
        Λ ≤ (extremalDistPointArc Ω z₀ E).toReal →
          |(harmonicMeasureJordan Ω z₀ E).toReal * Real.exp (π * (extremalDistPointArc Ω z₀ E).toReal) - 8 / π| <
            ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ (Ω E : Set ExtPlane) (z₀ : ExtPlane), IsJordanDomainExt Ω → IsJordanArc E →
      E ⊆ frontier Ω → z₀ ∈ Ω → extremalDistPointArc Ω z₀ E < ⊤ →
        (extremalDistPointArc Ω z₀ E).toReal < δ →
          |(harmonicMeasureJordan Ω z₀ E).toReal * Real.exp (π * (extremalDistPointArc Ω z₀ E).toReal) - 1| <
            ε) := by
  sorry

/-- **Theorem 5.3** (Ch. IV §5), (5.5) (cited at P1:6390, in Theorem 6.1's proof, P1:6476, in the Notes, P1:6500, in
Chapter VI, P2:1690, Chapter VIII, P2:3958, 4196, and App. H, P3:4790, 4798). Let `Ω` be a Jordan domain, let `z₀ ∈ Ω`,
and let `E` be a finite union of arcs contained in `∂Ω`. Then (5.5) `ω(z₀, E, Ω) ≤ (8/π) e^{−πλ(z₀, E)}`.
Modelling: `E` is a union of finitely many, at least one, Jordan arcs of `ℂ*` contained in `∂Ω`; `λ(z₀, E)` is the
definition of P1:6370–6374 (`extremalDistPointArc`); `λ(z₀, E) < ∞` is part of the conclusion (with `e^{−π·∞} = 0`,
(5.5) would give `ω(z₀, E, Ω) = 0`, impossible for a union of arcs), so that `λ` is read as a real number only where it
is finite. For `E = ∂Ω` there is no arc `σ`, `λ = 0` and `ω = 1 ≤ 8/π`. -/
theorem thm4_5_3 {Ω E : Set ExtPlane} (hΩ : IsJordanDomainExt Ω)
    (hE : IsFiniteUnionOf (fun s => IsJordanArc s ∧ s ⊆ frontier Ω) E) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    extremalDistPointArc Ω z₀ E < ⊤ ∧
      (harmonicMeasureJordan Ω z₀ E).toReal ≤ 8 / π * Real.exp (-π * (extremalDistPointArc Ω z₀ E).toReal) := by
  sorry

end GarnettMarshall2005
