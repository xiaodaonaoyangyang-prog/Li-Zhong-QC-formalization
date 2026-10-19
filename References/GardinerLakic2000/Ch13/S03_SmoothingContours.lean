import References.GardinerLakic2000.Ch13.S02_ExtremalProblemSurface

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.3 Smoothing the contours

Source `teichmuller.txt`, lines 9604–9620.

* Definition (obstacle sets whose components are bounded by closed analytic curves, l. 9605, 9619) —
  `HasAnalyticBoundary`
* Definition (the conclusion of Theorem 1 for given `φ`, `E`) — `HasSlitExtremal`
* Proposition 1 (l. 9619) — `prop13_1`

Not items (DESIGN §3): the classical smoothing by repeated Riemann maps (l. 9605) and the embedding `ι` into `S′`
(l. 9607–9617), steps of the argument.

**Modelling.** Proposition 1 ("to prove Theorem 1 it suffices to consider obstacle sets bounded by closed analytic
curves") is stated as the implication it asserts: Theorem 1 for all such obstacle sets implies Theorem 1 for all
obstacle sets, on a given surface and differential `φ` [reading]. A boundary is analytic if near each of its points it
is, in a chart, the image of an open interval under a real-analytic regular injective curve.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- **Definition** (§13.3, l. 9605, 9619). The components of `E` are bounded by closed analytic curves: near every
point of `∂E`, in a chart, `∂E` is the image of `(−1, 1)` under a regular injective real-analytic curve. -/
def HasAnalyticBoundary (E : Set S) : Prop :=
  ∀ x ∈ frontier E, ∃ (V : Set S) (c : ℝ → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ (chartAt ℂ x).source ∧
    AnalyticOnNhd ℝ c univ ∧ (∀ t, deriv c t ≠ 0) ∧ InjOn c (Ioo (-1) 1) ∧
    chartAt ℂ x '' (frontier E ∩ V) = c '' Ioo (-1) 1

/-- The conclusion of Theorem 1 for `φ` and `E`: an extremal pair for (13.1) whose slits lie on horizontal arcs and
critical points. -/
def HasSlitExtremal (φ : S → ℂ → ℂ) (E : Set S) : Prop :=
  ∃ (Y : RSBundle.{u}) (f : S → Y.carrier) (G : S ≃ₜ Y.carrier) (φ' : Y.carrier → ℂ → ℂ),
    IsObstacleFamilyMember E f G ∧ IsHeightTransport φ G φ' ∧ quadDiffNorm φ' = obstacleSup φ E ∧
      IsSlitSet φ' (slitImage E f)

variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Proposition 1** (§13.3, l. 9619). To prove Theorem 1 it suffices to consider obstacle sets whose components are
bounded by closed analytic curves. -/
theorem prop13_1 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S)
    (hφ0 : φ ≠ 0) (h : ∀ E : Set S, IsObstacleSet E → HasAnalyticBoundary E → HasSlitExtremal φ E) :
    ∀ E : Set S, IsObstacleSet E → HasSlitExtremal φ E := by
  sorry

end GardinerLakic2000
