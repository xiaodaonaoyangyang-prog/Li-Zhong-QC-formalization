import References.FarkasKra1992.Ch03.S04_DivisorsAndRiemannRoch
import References.FarkasKra1992.Ch02.S05_MeromorphicFunctionsAndDifferentials

/-!
# Farkas–Kra, Chapter IV §10 (continued): the degree of a `q`-canonical divisor

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §10.1 (`full.md` FK2:2293–2330).

Sibling of `Ch04/S10_RiemannRochAlternateApproach`. A *`q`-canonical divisor* is the divisor of a meromorphic `q`-differential
that is not zero: `IsMeroQDiff q c` (`Ch02/S05`) with the order `ordQDiff c P` finite at every point (on a connected surface
a `q`-differential vanishing identically has order `⊤` everywhere); the divisor `D` has `D P = ord_P c`. Divisors are additive.

* Proposition IV.10.1 (`deg D = q(2g - 2)` for a `q`-canonical divisor `D`) — `IsQCanonicalDivisor`, `prop4_10_1`
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace FarkasKra1992

open Forster1981 (divDeg)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **`q`-canonical divisor** (Ch. IV §10.1): the divisor `D` of a non-zero meromorphic `q`-differential `c`, i.e. `D P = ord_P c`
with every order finite. -/
def IsQCanonicalDivisor (q : ℤ) (D : Function.locallyFinsupp M ℤ) : Prop :=
  ∃ c : M → ℂ → ℂ, IsMeroQDiff q c ∧ ∀ x, ordQDiff c x = ((D x : ℤ) : WithTop ℤ)

/-- **Proposition IV.10.1** (Ch. IV §10.1). Let `M` be a compact Riemann surface of genus `g` and `D` a `q`-canonical divisor
on `M`. Then `deg D = q(2g - 2)`. -/
theorem prop4_10_1 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) {q : ℤ} {D : Function.locallyFinsupp M ℤ}
    (hD : IsQCanonicalDivisor q D) : divDeg D = q * (2 * (g : ℤ) - 2) := by
  sorry

end FarkasKra1992
