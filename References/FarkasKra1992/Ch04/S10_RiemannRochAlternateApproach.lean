import References.FarkasKra1992.Ch03.S04_DivisorsAndRiemannRoch

/-!
# Farkas–Kra, Chapter IV §10: Riemann–Roch, an alternate approach

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §10 (`full.md` FK2:2289–2548).

Conventions: as in `Ch03/S04_DivisorsAndRiemannRoch` (divisors additive, `dimL`, genus by `LiZhongQC.HasGenus`). In the
Riemann–Roch theorem IV.10.3, `r(DZ⁻¹) = dim L(D Z⁻¹)` is a space of meromorphic *functions* (`Z` a canonical divisor), which is
the form of `LiZhongQC.thm22_4_riemann_roch` (`ℓ(α) - ℓ(K - α) = deg α - g + 1`).

* Proposition IV.10.1 (`deg D = q(2g - 2)` for a `q`-canonical divisor `D`) — `prop4_10_1` in the sibling file
  `Ch04/S10b_QCanonicalDivisors`
* Lemma IV.10.2 (`r(D⁻¹) ≥ deg D - g + 1`) — `lemma4_10_2`
* Theorem IV.10.3 (Riemann–Roch) — exists: `LiZhongQC.thm22_4_riemann_roch`
* Remark after Theorem IV.10.3 (consequences of Riemann–Roch) — omitted: remark without a labelled claim
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace FarkasKra1992

open Forster1981 (H0 modOD divDeg)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Lemma IV.10.2** (Ch. IV §10.2). Let `D ∈ Div(M)` on a compact Riemann surface of genus `g`. Then
`r(D⁻¹) ≥ deg D - g + 1` (the space `L(D⁻¹)` is finite dimensional). -/
theorem lemma4_10_2 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (D : Function.locallyFinsupp M ℤ) :
    FiniteDimensional ℂ (H0 (modOD M D)) ∧ divDeg D - g + 1 ≤ (dimL (-D) : ℤ) := by
  sorry

end FarkasKra1992
