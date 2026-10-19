import References.Hubbard2006.Ch01.S02_SubharmonicHarmonic

/-!
# Hubbard 2006, Chapter 1 §1.5: Green's functions

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 669–701.

**Conventions.** As in `S02`. Hubbard's Green function of a compact `C^∞` piece (Prop. and Def. 1.5.1: continuous,
harmonic in the interior, vanishing on the boundary, with a logarithmic pole at `x₀`) is **not** the global minimal
Green
function of Farkas–Kra IV.3.6 (`References.IsGreenFunction`, shared): it is a different notion and is defined here as
`IsGreenFunctionOn`.

* Definition (Green's function of a compact piece with pole `x₀`, 1.5.1) — `IsGreenFunctionOn`
* Proposition and Definition 1.5.1 (existence and uniqueness of the Green function of a compact piece) — `prop1_5_1`
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Green's function of a compact piece** `K` with pole `x₀` and local coordinate `ζ` centred at `x₀` (Prop. and
Def. 1.5.1, H1:673): `G : K ∖ {x₀} → ℝ₊` is continuous (1), harmonic on the interior of `K ∖ {x₀}` (2), vanishes on the
boundary of `K` (3), and `G + ln |ζ|` extends to a continuous function on a neighbourhood of `x₀` (4).
Modelling: `ζ` is a chart of the maximal analytic atlas with `x₀ ∈ ζ.source` and `ζ x₀ = 0`; the extension in (4) is an
`∃ H` continuous on an open neighbourhood `V ⊆ interior K` of `x₀` with `H = G + ln ‖ζ‖` on `V ∖ {x₀}` (not `limUnder`,
and `ln ‖ζ‖` is never evaluated at `0`). "Positive" `ℝ₊` is read as `0 ≤ G` on `K ∖ {x₀}`, because strict positivity on
the boundary would contradict (3); `G > 0` in the interior follows from the maximum principle. -/
def IsGreenFunctionOn {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (K : Set X) (x₀ : X)
    (ζ : OpenPartialHomeomorph X ℂ) (G : X → ℝ) : Prop :=
  ζ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X ∧ x₀ ∈ ζ.source ∧ ζ x₀ = 0 ∧
    ContinuousOn G (K \ {x₀}) ∧ (∀ x ∈ K \ {x₀}, 0 ≤ G x) ∧
    References.IsHarmonicRS (interior K \ {x₀}) G ∧ (∀ x ∈ frontier K, G x = 0) ∧
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ interior K ∩ ζ.source ∧ ∃ H : X → ℝ, ContinuousOn H V ∧
      ∀ x ∈ V, x ≠ x₀ → H x = G x + Real.log ‖ζ x‖

/-- **Proposition and Definition 1.5.1** (Green's functions, Ch. 1 §1.5, H1:673). Let `K` be a connected compact `C^∞`
piece of a Riemann surface `X` with non-empty boundary, `x₀` an interior point of `K` and `ζ` a local coordinate
centred at `x₀`. Then there exists a unique function `G : K ∖ {x₀} → ℝ₊` with the properties of `IsGreenFunctionOn`.
Modelling: connectedness and non-empty boundary are the standing situation of the book (the pieces `X_n` of Prop. 1.4.1
of a noncompact surface); for a compact surface without boundary no such function exists. Uniqueness is on `K ∖ {x₀}`.
-/
theorem prop1_5_1 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {K : Set X} (hK : IsCompactSmoothPiece K) (hconn : IsConnected K)
    (hfr : (frontier K).Nonempty) {x₀ : X} (hx₀ : x₀ ∈ interior K) {ζ : OpenPartialHomeomorph X ℂ}
    (hζ : ζ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X) (hζx : x₀ ∈ ζ.source) (hζ0 : ζ x₀ = 0) :
    ∃ G : X → ℝ, IsGreenFunctionOn K x₀ ζ G ∧
      ∀ G' : X → ℝ, IsGreenFunctionOn K x₀ ζ G' → EqOn G G' (K \ {x₀}) := by
  sorry

end Hubbard2006
