import References.Hubbard2006.Ch01.S01_TwoStatements
import References.Hubbard2006.Ch01.S02_SubharmonicHarmonic

/-!
# Hubbard 2006, Chapter 1 §1.4: An exhaustion of `X`

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 558–668.

**Conventions.** As in `S01`, `S02`. "Compact `C^∞` piece" is `Hubbard2006.IsCompactSmoothPiece`; `H¹(X_n, ℝ) = 0` is
`HasTrivialH1` of the subtype `↥(X n)` (the piece as a space with the subspace topology).

* Proposition 1.4.1 (a nice exhaustion) — `prop1_4_1`
* Example 1.4.2 — omitted: example (a three-dimensional remark on the Whitehead continuum)
* Lemma 1.4.3 — omitted: proof step (its conclusion `H¹(X_n, ℝ) = 0` is conclusion 4 of Prop. 1.4.1)
* Exercise 1.4.4 — omitted: exercise
-/

open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Proposition 1.4.1** (a nice exhaustion of `X`, Ch. 1 §1.4, H1:562). Let `X` be a connected noncompact Riemann
surface with `H¹(X, ℝ) = 0` and `x₀ ∈ X`. Then there is an increasing sequence `X₀ ⊆ X₁ ⊆ ⋯` of connected compact `C^∞`
pieces of `X` such that (1) `x₀ ∈ X₀`, (2) `X_n` lies in the interior of `X_{n+1}`, (3) `⋃ X_n = X`, (4)
`H¹(X_n, ℝ) = 0`. -/
theorem prop1_4_1 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (hX : ¬ CompactSpace X) (h : HasTrivialH1 X) (x₀ : X) :
    ∃ Xn : ℕ → Set X, (∀ n, IsCompactSmoothPiece (Xn n)) ∧ (∀ n, IsConnected (Xn n)) ∧ x₀ ∈ Xn 0 ∧
      (∀ n, Xn n ⊆ interior (Xn (n + 1))) ∧ (⋃ n, Xn n) = Set.univ ∧ ∀ n, HasTrivialH1 (Xn n) := by
  sorry

end Hubbard2006
