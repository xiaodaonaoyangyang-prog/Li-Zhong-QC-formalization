import References.Forster1981.Ch02.S12_CohomologyGroups

/-!
# Forster, Chapter 2 §13: Dolbeault's lemma

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §13 (`full.md` F1:4391–4656).

Conventions: `C^∞` is `ContDiff ℝ ∞` (the scoped `∞` of `ContDiff`, i.e. smooth, not analytic); `∂/∂z̄` is
`LiZhongQC.dzbar`. The disc `{|z| < R}`, `0 < R ≤ ∞`, is `Metric.eball 0 R` for `R : ℝ≥0∞`, and as a Riemann surface the
open subset `discOpen R` of `ℂ`. The Laplacian is Mathlib's `Laplacian.laplacian` (`Δ = 4 ∂²/∂z∂z̄`). The sheaf `𝒪` is the
sheaf of ℂ-modules of holomorphic functions built by `localRepPresheaf`.

* Lemma 13.1 (F1:4395) — `lemma13_1`
* Theorem 13.2 (F1:4477) — `thm13_2`
* Corollary 13.3 (F1:4555) — `cor13_3`
* Definition (the sheaf `𝒪`, F1:4571) — `IsHolFunAt`, `holOn`, `modO`
* Theorem 13.4 (F1:4571) — `discOpen`, `thm13_4`
* Theorem 13.5 (F1:4593) — `thm13_5`

Omitted (U−): the remark after 13.2, `Δ = 4 ∂²/∂z∂z̄` (13.3).
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace

namespace Forster1981

section Sheaf

/-- Holomorphic at a point. -/
def IsHolFunAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] (a : X → ℂ) (x : X) : Prop :=
  MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) a x

/-- The global space `𝒪(Y)` of holomorphic functions (representatives). -/
def holOn (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (X → ℂ) :=
  repSpan IsHolFunAt Y

/-- **The sheaf `𝒪`** of holomorphic functions, as a sheaf of ℂ-modules (Ch. 2 §13, F1:4571). -/
abbrev modO (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := X → ℂ) IsHolFunAt VanishesAt

/-- **The disc** `{|z| < R}`, `0 < R ≤ ∞`, as an open subset of `ℂ` (Ch. 2 §13, F1:4477). -/
noncomputable def discOpen (R : ENNReal) : Opens ℂ := ⟨Metric.eball 0 R, Metric.isOpen_eball⟩

end Sheaf

/-- **Lemma 13.1** (Dolbeault's lemma, Ch. 2 §13, F1:4395). For `g ∈ 𝓔(ℂ)` with compact support there is `f ∈ 𝓔(ℂ)` with
`∂f/∂z̄ = g`. -/
theorem lemma13_1 {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧ ∀ z, LiZhongQC.dzbar f z = g z := by
  sorry

/-- **Theorem 13.2** (Ch. 2 §13, F1:4477). Let `D = {|z| < R}`, `0 < R ≤ ∞`, and `g ∈ 𝓔(D)`. Then there is `f ∈ 𝓔(D)` with
`∂f/∂z̄ = g`. -/
theorem thm13_2 {R : ENNReal} (hR : 0 < R) {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g (Metric.eball 0 R)) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f (Metric.eball 0 R) ∧ ∀ z ∈ Metric.eball (0 : ℂ) R, LiZhongQC.dzbar f z = g z := by
  sorry

/-- **Corollary 13.3** (Ch. 2 §13, F1:4555). For `g ∈ 𝓔(D)`, `D` a disc, the equation `Δf = g` has a solution `f ∈ 𝓔(D)`. -/
theorem cor13_3 {R : ENNReal} (hR : 0 < R) {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g (Metric.eball 0 R)) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f (Metric.eball 0 R) ∧
      ∀ z ∈ Metric.eball (0 : ℂ) R, Laplacian.laplacian f z = g z := by
  sorry

/-- **Theorem 13.4** (Ch. 2 §13, F1:4571). For a disc `D`, `H¹(D, 𝒪) = 0`. -/
theorem thm13_4 {R : ENNReal} (hR : 0 < R) : Subsingleton (H1 (modO ↥(discOpen R)) ⊤) := by
  sorry

/-- **Theorem 13.5** (Ch. 2 §13, F1:4593). `H¹(ℙ¹, 𝒪) = 0`. -/
theorem thm13_5 : Subsingleton (H1 (modO References.RiemannSphere) ⊤) := by
  sorry

end Forster1981
