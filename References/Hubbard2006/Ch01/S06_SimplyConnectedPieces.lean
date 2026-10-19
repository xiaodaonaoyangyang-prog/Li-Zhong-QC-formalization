import References.Hubbard2006.Ch01.S01_TwoStatements
import References.Hubbard2006.Ch01.S05_GreenFunctions

/-!
# Hubbard 2006, Chapter 1 §1.6: Simply connected compact pieces

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 702–729.

**Conventions.** As in `S01`, `S02`.

* Proposition 1.6.1 (a compact piece with `H¹ = 0` is a closed disc, analytic inside) — `prop1_6_1`
-/

open Set Metric
open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Proposition 1.6.1** (Ch. 1 §1.6, H1:706). A connected compact `C^∞` piece `X_n` of a Riemann surface with
non-empty
boundary and `H¹(X_n, ℝ) = 0` admits a homeomorphism `φ_n : X_n → 𝔻̄` onto the closed unit disc that is analytic on the
interior of `X_n`. Modelling: the book states it for the pieces of Prop. 1.4.1; the general form is what its proof
uses (connected, `H¹ = 0`, non-empty boundary; without a boundary the statement fails for the sphere). The homeomorphism
is
a function `φ : X → ℂ` that is continuous and injective on `K` with `φ '' K = 𝔻̄` (a continuous bijection of a compact
space onto a Hausdorff space is a homeomorphism) and holomorphic on the interior of `K`. -/
theorem prop1_6_1 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {K : Set X} (hK : IsCompactSmoothPiece K) (hconn : IsConnected K)
    (hfr : (frontier K).Nonempty) (h : HasTrivialH1 K) :
    ∃ φ : X → ℂ, ContinuousOn φ K ∧ InjOn φ K ∧ φ '' K = closedBall (0 : ℂ) 1 ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ (interior K) := by
  sorry

end Hubbard2006
