import LiZhongQC

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.1 Horizontal trajectories

F. P. Gardiner, N. Lakic, *Quasiconformal Teichmüller Theory* (2000), Chapter 4 *Quadratic differentials, part II*,
§4.1 (and the chapter introduction, which has no items besides (4.1), stated in §4.5); source `teichmuller.txt`,
lines 3643–3738.

* Definition (surface of finite analytic type, punctures, `R̄`, l. 3686, with the standing assumption
  `3g − 3 + n > 0` or `(g, n) = (1, 0)`) — `IsFiniteAnalyticType`
* Definition (finite analytic type, the structure `R = R̄ ∖ P`, l. 3686) — exists: `LiZhongQC.FiniteTypeStructure`
  (type (g, n, 0): no discs removed)
* Definition (order of a zero, regular point, l. 3688–3698) — exists: `LiZhongQC.IsZeroOfOrder`
  `LiZhongQC.IsRegularPoint`
* Definition (natural parameter (4.4), l. 3700–3708) — exists: `LiZhongQC.IsNaturalParameterAt`
* Definition (horizontal trajectory, l. 3717) — exists: `LiZhongQC.IsHorizontalArcRS`
* Definition (norm `‖φ‖ = ∬_R |φ| dx dy`, l. 3729–3733) — exists: `LiZhongQC.quadDiffNorm`
* Definition (`φ`-length `ℓ_φ(γ) = ∫_γ |φ|^{1/2} |dz|`, l. 3737) — exists: `LiZhongQC.phiLengthPath`
* Unlabelled (§4.1, l. 3735; used in the proof of Lemma 2, l. 3807) — `para4_1_simple_poles`

Not items (DESIGN §3): vertical trajectories (used only in proofs), the transition rule (4.5) and the curvature
remarks (l. 3712, 3737), all U−.

**Conventions.** A Riemann surface is the Part A bundle (`References/Common/RiemannSurface.lean`); quadratic
differentials are chart families `q : R → ℂ → ℂ` (`LiZhongQC.IsDiffFamily 2 0`), as in the project.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

/-- **Definition** (surface of finite analytic type, §4.1, l. 3686). `R` is obtained from a compact surface of genus
`g` by removing `n` points (the punctures), and the book's standing assumption `3g − 3 + n > 0`, except that `n = 0`
is allowed when `g = 1`, holds (so that `A(R)` has positive dimension). Modelling: the project's
`LiZhongQC.IsFiniteType R g n 0` (a closed surface `R̄` of genus `g`, a set `P` of `n` points, `R ≅ R̄ ∖ P`
holomorphically). -/
def IsFiniteAnalyticType (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] (g n : ℕ) : Prop :=
  LiZhongQC.IsFiniteType R g n 0 ∧ (0 < 3 * (g : ℤ) - 3 + n ∨ (g = 1 ∧ n = 0))

/-- **Unlabelled** (§4.1, l. 3735; used in the proof of Lemma 2, l. 3807). On a surface `R = R̄ ∖ P` of finite
analytic type, a holomorphic quadratic differential `φ` on `R` has finite norm if and only if it extends to a
meromorphic quadratic differential on `R̄` with at most simple poles at the punctures. Modelling: "extends with at
most simple poles" is "is the pull-back of an admissible quadratic differential of `R̄`"
(`LiZhongQC.admissibleQDInterior`, type `(g, n, 0)`). -/
theorem para4_1_simple_poles {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {g n : ℕ} (hR : 0 < 3 * (g : ℤ) - 3 + n ∨ (g = 1 ∧ n = 0))
    (F : LiZhongQC.FiniteTypeStructure R g n 0) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ) :
    LiZhongQC.quadDiffNorm φ < ⊤ ↔ φ ∈ LiZhongQC.admissibleQDInterior F := by
  sorry

end GardinerLakic2000
