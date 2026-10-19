import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.6: The mapping theorem (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 4241–4371.

**Conventions.** A solution of the Beltrami equation `∂f/∂z̄ = μ ∂f/∂z` on `U` is read through the complex
dilatation `LiZhongQC.complexDilatation f = f_z̄ / f_z` (the real derivative exists almost everywhere for a
quasiconformal map, and agrees with the distributional one): `complexDilatation f z = μ z` almost everywhere on `U`.

* Thm 4.6.1 (1) (the mapping theorem: existence of a quasiconformal solution on every open set) — `thm4_6_1_a`
* Thm 4.6.1 (2) (any other quasiconformal solution is `φ ∘ f` with `φ` injective analytic) — `thm4_6_1_b`
* Prop. 4.6.2, Lemma 4.6.3 (real analytic coefficients; the passage to the limit in the proof) — omitted: proof step
-/

open Set MeasureTheory

namespace Hubbard2006

open LiZhongQC

/-- **Theorem 4.6.1 (1)** (The mapping theorem, H1:4252). Let `U ⊂ ℂ` be open and `μ ∈ L^∞(U)` with `‖μ‖_∞ ≤ k < 1`.
Then there is a quasiconformal map `f : U → ℂ` solving the Beltrami equation `∂f/∂z̄ = μ ∂f/∂z`. (The installed
`LiZhongQC.thm13_6_riemann_mapping` is for simply connected `D ≠ ℂ` with `f(D) = 𝔻`, a near miss.) -/
theorem thm4_6_1_a {U : Set ℂ} (hU : IsOpen U) {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ U k) :
    ∃ f : ℂ → ℂ, IsQuasiconformal f U ∧ ∀ᵐ z ∂(volume.restrict U), complexDilatation f z = μ z := by
  sorry

/-- **Theorem 4.6.1 (2)** (H1:4252). If `f` and `g` are quasiconformal solutions of the Beltrami equation with
coefficient `μ` on `U`, there is an injective analytic function `φ : f(U) → ℂ` with `g = φ ∘ f` on `U`. -/
theorem thm4_6_1_b {U : Set ℂ} (hU : IsOpen U) {μ : ℂ → ℂ} {f g : ℂ → ℂ} (hf : IsQuasiconformal f U)
    (hg : IsQuasiconformal g U) (hfμ : ∀ᵐ z ∂(volume.restrict U), complexDilatation f z = μ z)
    (hgμ : ∀ᵐ z ∂(volume.restrict U), complexDilatation g z = μ z) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (f '' U) ∧ InjOn φ (f '' U) ∧ EqOn g (φ ∘ f) U := by
  sorry

end Hubbard2006
