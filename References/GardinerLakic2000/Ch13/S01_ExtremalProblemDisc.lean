import References.GardinerLakic2000.Ch12.S07_VariationDirichletNorm

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.1 Extremal problem for the disc (with the chapter introduction)

Chapter 13 *Obstacle problems*; source `teichmuller.txt`, lines 9510–9576.

* Definition (`A_σ`, l. 9555) — `aSigma`
* Definition (crosscut, l. 9561; its sides, l. 9873) — `circleSide`, `IsCrosscut`
* Definition (admissible system of crosscuts, l. 9563) — `IsAdmissibleCrosscuts`

Not items (DESIGN §3): the introduction (the transportation-cost problem, l. 9512–9552, motivation), the claim that
the elements of `A_σ` are Jenkins–Strebel differentials (l. 9565, explanation), the family `𝓕` of the disc and the
statement "the maximum exists and is realized by a unique pair" (l. 9567–9573, restated as Theorems 1–2 for surfaces).

**Modelling.** `σ` is a finite subset of the unit circle with at least four points. A side of the polygon is a
component of `∂Δ ∖ σ` (`circleSide`). "`φ(z) dz²` real along `∂Δ ∖ σ`" is `Im(φ(z)(iz)²) = 0`, the tangent at `z` being
`iz`. A crosscut is a path with its end points (`IsCrosscut`), because §13.9 measures its `ψ`-length; the
set-level `LiZhongQC.IsCrosscut` and `Pommerenke1992.IsCrosscut` do not carry the parametrization. "Holomorphic in
`ℂ̄ ∖ σ`" includes `∞`: `w ↦ φ(1/w)/w⁴` is holomorphic at `0`. Admissibility of crosscuts
is read through the reflected closed curves on `ℂ̄ ∖ σ` (C: `IsAdmissibleSystem`), in the book's combinatorial form
(l. 9873: two crosscuts are homotopic if they join the same two sides): the crosscuts are disjoint, join two
different non-adjacent sides (so that the reflected curve is neither trivial nor peripheral), and no two join the
same pair of sides [reading].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc phiArea)

/-- **Definition** (`A_σ`, §13.1, l. 9555). The quadratic differentials `φ` holomorphic in `ℂ̄ ∖ σ`, with
`φ(z) dz²` real along `∂Δ ∖ σ` and `∬_Δ |φ| < ∞` (`σ` a finite set of at least four points of `∂Δ`). Holomorphy at
`∞`: `φ(1/w) w⁻⁴` has a removable singularity at `w = 0`.
[CORRECTION] (AUDIT5_GL P3) The former `AnalyticAt ℂ (fun w => φ w⁻¹ / w ^ 4) 0` read the junk value `φ 0 / 0 = 0` at
`0`. It forced `φ(z) z⁴ → 0`, i.e. `φ(0) = 0`, and excluded e.g. `σ = {±1, ±i}`, `φ = i/(z⁴ − 1)`. -/
def aSigma (σ : Finset ℂ) : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ (↑σ)ᶜ ∧ (∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ w in 𝓝[≠] (0 : ℂ), φ w⁻¹ / w ^ 4 = g w) ∧
    (∀ z ∈ sphere (0 : ℂ) 1 \ ↑σ, (φ z * (I * z) ^ 2).im = 0) ∧ phiArea φ unitDisc < ⊤}

/-- **Definition** (side of a conformal polygon, §13.1, §13.9 l. 9873). The side of `(Δ, σ)` containing `z`: the
component of `∂Δ ∖ σ` through `z`. -/
def circleSide (σ : Finset ℂ) (z : ℂ) : Set ℂ := connectedComponentIn (sphere (0 : ℂ) 1 \ ↑σ) z

/-- **Definition** (crosscut, §13.1, l. 9561). A simple curve in `Δ` with end points in `∂Δ ∖ σ`. -/
def IsCrosscut (σ : Finset ℂ) {a b : ℂ} (c : Path a b) : Prop :=
  Function.Injective c ∧ (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → c t ∈ unitDisc) ∧
    a ∈ sphere (0 : ℂ) 1 \ ↑σ ∧ b ∈ sphere (0 : ℂ) 1 \ ↑σ

/-- **Definition** (admissible system of crosscuts, §13.1, l. 9563). Disjoint crosscuts `γₖ`, each joining two
different, non-adjacent sides, no two joining the same pair of sides (see the module docstring). -/
def IsAdmissibleCrosscuts (σ : Finset ℂ) {m : ℕ} (a b : Fin m → ℂ) (γ : ∀ k, Path (a k) (b k)) : Prop :=
  (∀ k, IsCrosscut σ (γ k)) ∧ (∀ k l, k ≠ l → Disjoint (range (γ k)) (range (γ l))) ∧
    (∀ k, Disjoint (closure (circleSide σ (a k))) (closure (circleSide σ (b k)))) ∧
    ∀ k l, k ≠ l → ¬ ((circleSide σ (a k) = circleSide σ (a l) ∧ circleSide σ (b k) = circleSide σ (b l)) ∨
      (circleSide σ (a k) = circleSide σ (b l) ∧ circleSide σ (b k) = circleSide σ (a l)))

end GardinerLakic2000
