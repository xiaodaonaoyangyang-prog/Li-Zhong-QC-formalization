import References.GardinerLakic2000.Ch03.S04_ClosedSets

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.5 The Teichmüller infinitesimal norm

Source `teichmuller.txt`, lines 2612–2634 (Chapter 3, §3.5).

* Definition 6 (the infinitesimal Teichmüller norm on `Z(R)`, l. 2615; used in Ch. 4, 6, 7) — `teichNormRS`
* Definition 7 (the infinitesimal Teichmüller norm on `Z(Λ)`, l. 2623) — `teichNormClosed`

Not items: the map `I` (`I(μ)` = the restriction of `V_μ` to `Λ`, l. 2629) and its well-definedness (U−); the
announcements of Theorems 9 and 11 (l. 2631–2633). The Teichmüller norm of a vector field on `Λ` (through `I`) is
`teichNormVF` of §3.9.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (ExtPlane beltramiPairing IsBeltramiCoeff)

/-- **Definition 6** (§3.5, l. 2615). `‖V‖_T = inf {‖μ‖∞ : V(φ) = (φ, μ) for every φ ∈ A(R)}` for `V ∈ Z(R)`. -/
def teichNormRS {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] (V : (R → ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : R → ℂ → ℂ) (_ : μ ∈ beltramiSpace R ∧ ∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ μ),
    beltramiNormRS μ

/-- **Definition 7** (§3.5, l. 2623). `‖V‖_T = inf {‖μ‖∞ : V(φ) = (φ, μ) for every φ ∈ A(Λ)}` for `V ∈ Z(Λ)`. -/
def teichNormClosed (Λ : Set ExtPlane) (V : (ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : ℂ → ℂ) (_ : (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧ ∀ φ ∈ aSpaceClosed Λ, V φ = beltramiPairing univ μ φ),
    eLpNorm μ ⊤ volume

end GardinerLakic2000
