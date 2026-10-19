import References.GardinerLakic2000.Ch15.S01_WeightedBeltramiDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 15 §15.2 Asymptotic Beltrami differentials

Source `teichmuller.txt`, lines 11378–11476 (Chapter 15, §15.2).

* Theorem 1 (l. 11379) — `thm15_1`
* Proposition 1 (l. 11471) — `prop15_1`
* Corollary 1 (l. 11473) — `cor15_1_1`

Not items: (15.5), (15.6) (proof of Theorem 1); the remark comparing `η` with the harmonic representative `h(v)` of
Lemma 14.1 (l. 11475). Modelling: as §15.1; "`η` represents `v`" is `pairingRS φ η = v(φ)` on `A(R)`; `‖v‖` is batch
B's `zNorm`; a vanishing representative has `b*(η) = 0` (A: `boundaryDilatationStar`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 1** (§15.2, l. 11379). Every vector of `Z/Z₀` has an asymptotically extremal representative. -/
theorem thm15_1 {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) : ∃ μ : R → ℂ → ℂ, IsInfAsymExtremal V μ := by
  sorry

/-- **Proposition 1** (§15.2, l. 11471). For every `v ∈ Z` and `ε > 0` there is a representative `η` of `v` with
`‖η‖∞ < ‖v‖ + ε` and `b*(η) = b(v)`. -/
theorem prop15_1 {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) {ε : ℝ} (hε : 0 < ε) :
    ∃ η ∈ beltramiSpace R, (∀ φ ∈ integrableHolQDSet R, pairingRS φ η = V φ) ∧
      (beltramiNormRS η).toReal < zNorm V + ε ∧ boundaryDilatationStar η = infBoundaryDilatation V := by
  sorry

/-- **Corollary 1** (§15.2, l. 11473). For every `v ∈ Z₀` and `ε > 0` there is a vanishing representative `η` of `v`
with `‖η‖∞ < ‖v‖ + ε`. -/
theorem cor15_1_1 {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zZeroSpace R) {ε : ℝ} (hε : 0 < ε) :
    ∃ η ∈ beltramiSpace R, (∀ φ ∈ integrableHolQDSet R, pairingRS φ η = V φ) ∧
      (beltramiNormRS η).toReal < zNorm V + ε ∧ boundaryDilatationStar η = 0 := by
  sorry

end GardinerLakic2000
