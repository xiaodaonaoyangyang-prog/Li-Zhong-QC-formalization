import References.GardinerLakic2000.Ch09.S02_ConstantAbsoluteValue

/-!
# Gardiner–Lakic 2000, Ch. 9 §9.3 Teichmüller differentials

Source `teichmuller.txt`, lines 7463–7582 (Chapter 9, §9.3).

* Theorem 3 (l. 7466) — `thm9_3`
* Definition 1 (weak uniform convexity, l. 7517) — `IsWeakUniformConvex`
* Definition (`b_E(μ)`, the infinitesimal boundary dilatation on `A(E)`, l. 7529) — exists:
  `GardinerLakic2000.infBoundaryDilatation` (batch A, §3.3, on the subsurface E with the restricted coefficient)
* Lemma 3 (l. 7531) — `lemma9_3`

Not items: (9.11), (9.12) and the argument after Lemma 3 (l. 7569–7581, proof). Modelling: surface level; `φ` in
Theorem 3 is a holomorphic quadratic differential on `R` (not necessarily integrable, `LiZhongQC.holQuadDiffSubmodule`)
and "`f` uniquely extremal" is `IsUniquelyExtremalRS` of its coefficient `μ = k|φ|/φ`; in Definition 1 and Lemma 3 the
set `E` is a Riemann surface in its own right (an open subset, `A(E)` its integrable holomorphic differentials); the
Beltrami differential `|φ|/φ` is `φ̄/|φ|`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm holQuadDiffSubmodule)

/-- **Theorem 3** (§9.3, l. 7466). Let `φ ≠ 0` be a holomorphic quadratic differential on `R` and `f` quasiconformal
with Beltrami coefficient `μ = k|φ|/φ`, `0 < k < 1`. Then `f` is uniquely extremal if and only if there are `φₙ ∈ A(R)`
with (1) `φₙ → φ` uniformly on compact subsets and (2) `k‖φₙ‖ − Re ∫ φₙμ → 0`. -/
theorem thm9_3 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p) {φ : R → ℂ → ℂ}
    (hφ : φ ∈ holQuadDiffSubmodule R) (hφ0 : φ ≠ 0) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {μ : beltramiBall R}
    (hμ : ∀ x : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target), μ.1 x z = k * (conj (φ x z) / ‖φ x z‖)) :
    IsUniquelyExtremalRS p μ ↔ ∃ ψ : ℕ → R → ℂ → ℂ, (∀ n, ψ n ∈ integrableHolQDSet R) ∧
      (∀ x : R, TendstoLocallyUniformlyOn (fun n => ψ n x) (φ x) atTop (chartAt ℂ x).target) ∧
      Tendsto (fun n => k * (quadDiffNorm (ψ n)).toReal - (pairingRS (ψ n) μ.1).re) atTop (𝓝 0) := by
  sorry

/-- **Definition 1** (weak uniform convexity, §9.3, l. 7517). A point `φ` of the unit sphere of `A(E)` is weakly
uniformly convex if, for unit vectors `φₙ`, `Re ∫_E φₙ |φ|/φ → 1` implies `∫_E |φₙ − φ| → 0`. -/
def IsWeakUniformConvex {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E] (φ : E → ℂ → ℂ) : Prop :=
  φ ∈ integrableHolQDSet E ∧ quadDiffNorm φ = 1 ∧
    ∀ ψ : ℕ → E → ℂ → ℂ, (∀ n, ψ n ∈ integrableHolQDSet E ∧ quadDiffNorm (ψ n) = 1) →
      Tendsto (fun n => (pairingRS (ψ n) (fun x z => conj (φ x z) / ‖φ x z‖)).re) atTop (𝓝 1) →
        Tendsto (fun n => quadDiffNorm (ψ n - φ)) atTop (𝓝 0)

/-- **Lemma 3** (§9.3, l. 7531). A point `φ` of the unit sphere of `A(E)` is weakly uniformly convex if and only if
`b_E(|φ|/φ) < 1`. -/
theorem lemma9_3 {E : Type u} [TopologicalSpace E] [T2Space E] [ConnectedSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ω E] {φ : E → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet E) (hφ1 : quadDiffNorm φ = 1) :
    IsWeakUniformConvex φ ↔
      infBoundaryDilatation (fun ψ => pairingRS ψ (fun x z => conj (φ x z) / ‖φ x z‖)) < 1 := by
  sorry

end GardinerLakic2000
