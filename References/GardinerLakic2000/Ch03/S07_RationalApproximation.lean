import References.GardinerLakic2000.Ch03.S06_CrossRatioNorm

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.7 Approximation by rational functions

Source `teichmuller.txt`, lines 2785–2968 (Chapter 3, §3.7).

* Definition (`Rat(Λ)`, the rational functions in `A(Λ)`, l. 2786, 3112) — `ratSpace`
* Theorem 9 (Bers' approximation theorem, l. 2788; cited eleven times, Ch. 4, 6, 8, 16) — `thm3_9`

Not items: (3.29)–(3.36), steps of the proof (Ahlfors' mollifier (3.31) included). Note: (3.29) prints `(w − z)` for
`(ζ − z)` [misprint; so also GL8:2708]. Modelling: a rational function is a quotient `p/q` of polynomials (its values at
the zeros of `q`, a finite set, are irrelevant in `L¹`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane phiArea)

/-- **Definition** (§3.7, l. 2786; §3.9, l. 3112). `Rat(Λ)`: the integrable rational quadratic differentials
holomorphic on `ℂ̄ ∖ Λ`, i.e. the rational elements of `A(Λ)`. -/
def ratSpace (Λ : Set ExtPlane) : Set (ℂ → ℂ) :=
  {φ | φ ∈ aSpaceClosed Λ ∧ ∃ p q : Polynomial ℂ, q ≠ 0 ∧ ∀ z : ℂ, q.eval z ≠ 0 → φ z = p.eval z / q.eval z}

/-- **Theorem 9** (Bers' approximation theorem, §3.7, l. 2788). Rational functions are dense in `A(Λ)`. -/
theorem thm3_9 {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceClosed Λ) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ ψ ∈ ratSpace Λ, phiArea (φ - ψ) univ < ε := by
  sorry

end GardinerLakic2000
