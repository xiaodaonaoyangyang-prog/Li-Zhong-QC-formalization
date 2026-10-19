import References.GardinerLakic2000.Ch01.S06_HolomorphicMotions

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.7 Lebesgue measure and Hausdorff dimension

Source `teichmuller.txt`, lines 907–939 (Chapter 1, §1.7).

* Definition 7 (Hausdorff dimension via disc covers, (1.18), l. 908–916) — exists: `dimH` (Mathlib; the same number,
  covers by discs of radius r instead of sets of diameter 2r, leader ruling A0.3)
* Definition 8 (Hausdorff measure `HM(Λ)` with the gauge `(π r)^d`, l. 920) — `hausdorffMeasureGL`
* Theorem 5 (Astala, l. 926) — `thm1_5`
* Theorem 6 (Astala, l. 932; cited in the bibliography note [Ast94]) — `thm1_6`

Not items: "the Hausdorff dimension of a bounded set is at most 2" (l. 918, U−). Modelling: "a quasiconformal
self-map of the plane with dilatation `K`" is `LiZhongQC.IsKQC f univ K` onto `ℂ` (the inequalities are monotone in
`K`); in Theorem 5 `0 < d` [reading: the formula has `1/d`]; in Theorem 6 `m` and `m′` are Lebesgue outer measures
(`volume` is an outer measure on all sets).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC)

/-- **Definition 8** (§1.7, l. 920). The Hausdorff measure of `Λ` in dimension `d` (the book takes `d = HD(Λ)`):
`HM(Λ) = liminf_{ε → 0} inf {Σ_j [π radius(B_j)]^d : {B_j} a countable cover of Λ by discs, radius(B_j) ≤ ε}`. No
relation to Mathlib's `μH` is claimed (leader ruling, change 1). -/
def hausdorffMeasureGL (d : ℝ) (Λ : Set ℂ) : ℝ≥0∞ :=
  Filter.liminf (fun ε : ℝ => ⨅ (c : ℕ → ℂ) (r : ℕ → ℝ)
      (_ : (∀ j, 0 < r j ∧ r j ≤ ε) ∧ Λ ⊆ ⋃ j, ball (c j) (r j)),
      ∑' j, ENNReal.ofReal ((π * r j) ^ d)) (𝓝[>] 0)

/-- **Theorem 5** (Astala, §1.7, l. 926). If `f` is a `K`-quasiconformal self-map of the plane fixing `0` and `1`, `d`
is the Hausdorff dimension of a compact set `Λ` and `d′` that of `f(Λ)`, then
`(1/K)(1/d − 1/2) ≤ 1/d′ − 1/2 ≤ K(1/d − 1/2)`. -/
theorem thm1_5 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (honto : f '' univ = univ) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {Λ : Set ℂ} (hΛ : IsCompact Λ) (hd : 0 < (dimH Λ).toReal) :
    (1 / K) * (1 / (dimH Λ).toReal - 1 / 2) ≤ 1 / (dimH (f '' Λ)).toReal - 1 / 2 ∧
      1 / (dimH (f '' Λ)).toReal - 1 / 2 ≤ K * (1 / (dimH Λ).toReal - 1 / 2) := by
  sorry

/-- **Theorem 6** (Astala, §1.7, l. 932). There is a constant `C = C(K, R)` such that for every `K`-quasiconformal
self-map `f` of the plane fixing `0` and `1` and every set `Λ ⊆ {|z| ≤ R}`, the outer measures satisfy
`m(f(Λ)) ≤ C m(Λ)^{1/K}`. -/
theorem thm1_6 {K R : ℝ} (hK : 1 ≤ K) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℂ → ℂ, IsKQC f univ K → f '' univ = univ → f 0 = 0 → f 1 = 1 →
      ∀ Λ ⊆ closedBall (0 : ℂ) R, volume (f '' Λ) ≤ C * volume Λ ^ (1 / K) := by
  sorry

end GardinerLakic2000
