import References.Pommerenke1992.Ch03.S01_Introduction

/-!
# Pommerenke 1992, Ch. 3 §3.2 Smooth Jordan Curves

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §3.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1805–1928.

* Definition (smooth Jordan curve, §3.2) — `IsSmoothJordanCurve`
* Definition (tangent direction angle `β`, (3.2.1)) — `IsTangentDirection`
* Unlabelled (§3.2, l. 1809: a Jordan curve is smooth if and only if it has a continuously varying tangent, (3.2.1);
  cited at l. 2184 and in the proof of Theorem 3.2) — `eq3_2_1`
* Theorem 3.2 (Lindelöf) — `thm3_2_a`, `thm3_2_b`
* Proposition 3.3 (Warschawski) — `prop3_3`

Not items (DESIGN §3): the conformal parametrization (3.2.2) (notation, written out in the statements); the example
after Theorem 3.2 showing that smoothness does not imply the continuity of `f'` in `𝔻̄` (an example; recalled at
l. 3387, "we have seen in Section 3.2 that the converse does not hold").

**Conventions.** As in §3.1. A continuous branch of `arg f'` is the imaginary part of a holomorphic logarithm `L` of
`f'` in `𝔻` (`e^L = f'`). Limits of `arg` are limits of directions: `arg w → β` is `w/|w| → e^{iβ}`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve IsConformalOnto)

/-- **Definition** (§3.2). The Jordan curve `C ⊆ ℂ` is smooth: it has a parametrization `w(τ)`, `0 ≤ τ ≤ 2π`, with
`w'` continuous and `≠ 0`.
Modelling: `w` is extended `2π`-periodically, as in the book, so `w'` is continuous on `ℝ` (continuously
differentiable, `C¹`). -/
def IsSmoothJordanCurve (C : Set ℂ) : Prop :=
  ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ContDiff ℝ 1 w ∧ ∀ τ, deriv w τ ≠ 0

/-- **Definition** (§3.2, (3.2.1)). `β` is a tangent direction angle of the parametrized curve `w`:
`arg[w(τ) - w(t)] → β(t)` as `τ → t+` and `→ β(t) + π` as `τ → t-`, for all `t`.
Modelling: limits of directions, `(w(τ) - w(t))/|w(τ) - w(t)| → e^{iβ(t)}`, resp. `→ -e^{iβ(t)}`. -/
def IsTangentDirection (w : ℝ → ℂ) (β : ℝ → ℝ) : Prop :=
  ∀ t, Tendsto (fun τ => (w τ - w t) / (‖w τ - w t‖ : ℂ)) (𝓝[>] t) (𝓝 (exp (β t * I))) ∧
    Tendsto (fun τ => (w τ - w t) / (‖w τ - w t‖ : ℂ)) (𝓝[<] t) (𝓝 (-exp (β t * I)))

/-- **Unlabelled claim** (§3.2, l. 1809, (3.2.1); cited at l. 2184, "compare (3.2.1)", and in the proof of
Theorem 3.2). The Jordan curve `C` is smooth if and only if it has a continuously varying tangent, that is, a
parametrization `w` with a continuous tangent direction angle `β`.
Modelling: the parametrization is any `2π`-periodic parametrization (the tangent characterization does not depend on
it, l. 1817). -/
theorem eq3_2_1 {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    IsSmoothJordanCurve C ↔
      ∃ w : ℝ → ℂ, IsPeriodicParam C w ∧ ∃ β : ℝ → ℝ, Continuous β ∧ IsTangentDirection w β := by
  sorry

/-- **Theorem 3.2** (§3.2; Lindelöf), first part. Let `f` map `𝔻` conformally onto the inner domain of the Jordan
curve `C`. Then `C` is smooth if and only if `arg f'` has a continuous extension to `𝔻̄`.
Modelling: `arg f'` is `Im L` for a holomorphic logarithm `L` of `f'` in `𝔻`. -/
theorem thm3_2_a {C : Set ℂ} (hC : IsJordanCurve (toExt C)) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) :
    IsSmoothJordanCurve C ↔
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ (∀ z ∈ unitDisc, exp (L z) = deriv f z) ∧
        ∃ V : ℂ → ℝ, ContinuousOn V (closedBall 0 1) ∧ ∀ z ∈ unitDisc, V z = (L z).im := by
  sorry

/-- **Theorem 3.2** (§3.2; Lindelöf), second part. If `C` is smooth, then for the conformal parametrization
(3.2.2) `w(t) = f(e^{it})` with tangent direction angle `β`, (3.2.3) `arg f'(e^{it}) = β(t) - t - π/2` (`t ∈ ℝ`), and
(3.2.4) `log f'(z) = log |f'(0)| + (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) (β(t) - t - π/2) dt` for `z ∈ 𝔻`.
Modelling: `β` is a continuous tangent direction angle of `t ↦ F(e^{it})` (one exists, and the statement is made
for each of them); `log f'` is a holomorphic logarithm `L` of `f'`, and (3.2.3) says that `Im L(z) → β(t) - t - π/2`
as `z → e^{it}`, `z ∈ 𝔻`. -/
theorem thm3_2_b {C : Set ℂ} (hC : IsJordanCurve (toExt C)) (hs : IsSmoothJordanCurve C) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) :
    (∃ β : ℝ → ℝ, Continuous β ∧ IsTangentDirection (fun t => F (exp (t * I))) β) ∧
    ∀ β : ℝ → ℝ, Continuous β → IsTangentDirection (fun t => F (exp (t * I))) β →
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ (∀ z ∈ unitDisc, exp (L z) = deriv f z) ∧
        (∀ t : ℝ, Tendsto (fun z => (L z).im) (𝓝[unitDisc] (exp (t * I))) (𝓝 (β t - t - π / 2))) ∧
        ∀ z ∈ unitDisc, L z = (Real.log ‖deriv f 0‖ : ℂ) + I / (2 * π) *
          ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * ((β t - t - π / 2 : ℝ) : ℂ) := by
  sorry

/-- **Proposition 3.3** (§3.2; Warschawski). Let `C` be smooth. Then `C` is rectifiable and
(3.2.9) `Λ({f(e^{iϑ}) : t₁ ≤ ϑ ≤ t₂}) ≤ M (t₂ - t₁)^{1/2}` for `t₁ ≤ t₂ ≤ t₁ + 2π`, where `M` is a constant.
Modelling: the length of the arc is the variation of the conformal parametrization `ϑ ↦ F(e^{iϑ})` on `[t₁, t₂]`;
`M` depends on `f`. -/
theorem prop3_3 {C : Set ℂ} (hC : IsJordanCurve (toExt C)) (hs : IsSmoothJordanCurve C) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain C)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) :
    eVariationOn (fun ϑ : ℝ => F (exp (ϑ * I))) (Icc 0 (2 * π)) < ⊤ ∧
      ∃ M : ℝ, ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → t₂ ≤ t₁ + 2 * π →
        eVariationOn (fun ϑ : ℝ => F (exp (ϑ * I))) (Icc t₁ t₂) ≤ ENNReal.ofReal (M * (t₂ - t₁) ^ (1 / 2 : ℝ)) := by
  sorry

end Pommerenke1992
