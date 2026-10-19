import References.GardinerLakic2000.Ch04.S03_MinimalNormProperty
import References.GardinerLakic2000.Ch02.S04_TeichmullerSpace

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.4 The Reich–Strebel inequality

Source `teichmuller.txt`, lines 3956–4016.

* Theorem 3 (the Reich–Strebel inequality (4.15), finite analytic type, l. 3959) — `thm4_3`

Near misses: `LiZhongQC.lemma26_2` (closed surfaces of genus `> 1`, with the stretching function) and
`LiZhongQC.thm35_2_main_inequality` (the disc).

**Conventions.** The Beltrami coefficient of `f` is Part A's `beltramiCoeffRS f` (chart family); the integrand
`|φ| |1 + μφ/|φ||² / (1 − |μ|²)` is chart invariant and is integrated with `LiZhongQC.surfaceIntegral φ` (which
supplies the factor `|φ| dx dy`). At zeros of `φ` the quotient `φ/|φ|` has a junk value multiplied by `|φ| = 0`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

/-- Helper. The surface `R` itself as a Part A bundle (`RSBundle`), so that self-maps of `R` can be compared with
maps to other surfaces. -/
def selfBundle (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] : RSBundle.{u} :=
  ⟨R, ⟨‹_›, ‹_›, ‹_›⟩⟩

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 3** (the Reich–Strebel inequality (4.15), §4.4, l. 3959). Let `R` be of finite analytic type, `φ` a
holomorphic quadratic differential on `R` with `‖φ‖ < ∞`, `f` a quasiconformal self-map of `R` homotopic to the
identity, and `μ = f_z̄/f_z`. Then `‖φ‖ ≤ ∬_R |φ| |1 + μ φ/|φ||² / (1 − |μ|²) dx dy`. Modelling: homotopy as in
Lemma 2 (B0.2). [CORRECTION, AUDIT4 G9: the coefficient is a family `μ ∈ M(R)` with `HasBeltramiCoeff f μ` (chart-invariant), not
`beltramiCoeffRS f x z`, which is junk off the local domain of `f`'s expression and made the partition infimum of `surfaceIntegral` junk-dependent.] -/
theorem thm4_3 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    (hφn : LiZhongQC.quadDiffNorm φ < ⊤) (f : R ≃ₜ R) (hf : LiZhongQC.IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f : C(R, R)) (ContinuousMap.id R)) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiBall R)
    (hfμ : HasBeltramiCoeff f μ) :
    LiZhongQC.quadDiffNorm φ ≤ LiZhongQC.surfaceIntegral φ fun x z =>
      ENNReal.ofReal (‖1 + μ x z * (φ x z / ‖φ x z‖)‖ ^ 2 /
        (1 - ‖μ x z‖ ^ 2)) := by
  sorry

end GardinerLakic2000
