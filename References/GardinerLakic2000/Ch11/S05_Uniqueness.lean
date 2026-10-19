import References.GardinerLakic2000.Ch11.S04_PrescribingHeights

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.5 Uniqueness

Source `teichmuller.txt`, lines 8587–8649 (Chapter 11, §11.5).

* Theorem 4 (l. 8590) — `thm11_4`

Not items: (11.21)–(11.25) (proof: the length–area argument and Schwarz's inequality). Modelling: as §11.4; the
quadratic differentials are compared in the charts; "the associated holomorphic quadratic differential is uniquely
determined by the curve system `α_j` and the heights `b_j`" is read for any two differentials with properties (a)–(e)
for `{α_j}` and `{b_j}` (`HasJSProperties`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop)

/-- **Theorem 4** (§11.5, l. 8590). The annuli solving the extremal problem (11.5) for the admissible system `{α_j}` and
the constants `b_j > 0` are unique, and so is the associated holomorphic quadratic differential. -/
theorem thm11_4 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {ι : Type*} [Countable ι] {α : ι → Loop R} (hα : IsAdmissibleSystem α) {b : ι → ℝ}
    (hb : ∀ j, 0 < b j) :
    (∀ A A' : ι → Set R, IsCompatibleAnnuli α A → annuliFunctional b A = annuliInf α b →
      IsCompatibleAnnuli α A' → annuliFunctional b A' = annuliInf α b → annuliInf α b < ⊤ → A = A') ∧
    ∀ (φ φ' : R → ℂ → ℂ) (A A' : ι → Set R), HasJSProperties φ α b A → HasJSProperties φ' α b A' →
      ∀ x : R, EqOn (φ x) (φ' x) (chartAt ℂ x).target := by
  sorry

end GardinerLakic2000
