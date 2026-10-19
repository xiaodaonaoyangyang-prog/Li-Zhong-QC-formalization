import References.GardinerLakic2000.Ch05.S03_IsotopiesOverPlaneDomains

/-!
# Gardiner–Lakic 2000, Ch. 5 §5.4 Proof of Lemma 2

Source `teichmuller.txt`, lines 5144–5233.

* Definition (harmonic measure `ω(z, E)` of a set `E ⊆ Δ̄` in the unit disc, l. 5145) — `IsHarmonicMeasureFn`
* Lemma 3 (estimates of `ω(0, E)` for small continua, l. 5150) — `lemma5_3_a`, `lemma5_3_b`

Not items (DESIGN §3): the inequalities (5.21) (Beurling) and (5.22) (Fitzgerald–Rodin–Warschawski), l. 5186–5196:
named, but stated inside the proof sketch of Lemma 3 and not cited elsewhere (U−); the steps i)–iii) of the proof of
Lemma 2 (l. 5218–5232). Near miss for the definition: `GarnettMarshall2005.harmonicMeasureOpen`, which is for closed
sets inside the domain, whereas here `E` may meet `∂Δ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

/-- **Definition** (harmonic measure, §5.4, l. 5145). `u = ω(·, E)` is the harmonic measure of `E ⊆ Δ̄` in the unit
disc: harmonic in `Δ ∖ E`, continuous on `Δ̄` except possibly at the points of `∂Δ` in the closure of both `E` and
`∂Δ ∖ E`, equal to `1` on `E` and to `0` on `∂Δ ∖ E`. Modelling: the book's definition ("if such a function exists");
`ω(z₀, E)` is `u z₀` for any such `u`.
[CORRECTION, AUDIT4 G5] The bound `0 ≤ u ≤ 1` is part of the definition (harmonic measure is the bounded solution): without it
`u + c ·` (Poisson kernel at an endpoint of an arc `E ⊆ ∂Δ`, extended by `0` and by `1` at the endpoint) also qualifies, and Lemma 3 fails. -/
def IsHarmonicMeasureFn (E : Set ℂ) (u : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u (LiZhongQC.unitDisc \ E) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ u z ∧ u z ≤ 1) ∧
    ContinuousOn u (closedBall 0 1 \ (closure E ∩ closure (sphere 0 1 \ E))) ∧
    (∀ z ∈ E, u z = 1) ∧ ∀ z ∈ sphere (0 : ℂ) 1 \ E, u z = 0

/-- **Lemma 3** (§5.4, l. 5150), first estimate. Let `E` be a compact connected subset of `Δ̄` outside the disc
`|z| ≤ 2ε₀`. Then `ω(0, E) ≤ O(1/log(1/diam E))`. Modelling: `∀ ε₀ > 0 ∃ C δ`, for `diam E < δ`. -/
theorem lemma5_3_a {ε₀ : ℝ} (hε₀ : 0 < ε₀) : ∃ C δ : ℝ, 0 < δ ∧ ∀ (E : Set ℂ) (u : ℂ → ℝ), IsCompact E →
    IsConnected E → E ⊆ closedBall 0 1 → Disjoint E (closedBall 0 (2 * ε₀)) → Metric.diam E < δ →
    IsHarmonicMeasureFn E u → u 0 ≤ C / Real.log (1 / Metric.diam E) := by
  sorry

/-- **Lemma 3** (§5.4, l. 5156), converse estimate. Under the same assumptions, `diam E ≤ O(ω(0, E))`. -/
theorem lemma5_3_b {ε₀ : ℝ} (hε₀ : 0 < ε₀) : ∃ C δ : ℝ, 0 < δ ∧ ∀ (E : Set ℂ) (u : ℂ → ℝ), IsCompact E →
    IsConnected E → E ⊆ closedBall 0 1 → Disjoint E (closedBall 0 (2 * ε₀)) → Metric.diam E < δ →
    IsHarmonicMeasureFn E u → Metric.diam E ≤ C * u 0 := by
  sorry

end GardinerLakic2000
