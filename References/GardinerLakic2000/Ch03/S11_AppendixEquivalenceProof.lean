import References.GardinerLakic2000.Ch03.S10_VanishingElements

/-!
# Gardiner–Lakic 2000, Ch. 3 Appendix: proof of the equivalence theorem

Source `teichmuller.txt`, lines 3262–3571 (Chapter 3, Appendix).

* Lemma 7 (l. 3270) — `lemma37Expr`, `lemma3_7_a`, `lemma3_7_b`

Not items: the reduction to finite sets, the three-point and circle cases ((3.47)–(3.49)), the four-point extension
((3.50)) and the thick–thin construction ((3.51), (3.52)), all steps of the proof of Theorem 11. Modelling: "`V` has
bounded cross-ratio norm on a set containing `∞`, where `V` vanishes" is `crNorm Λ V ≤ B` together with the bound `B`
on the distortions `V(a, b, c, ∞)` of the three-point form `crDistortionInf` (l. 3284), which the proof uses; in part
(b) "`V` has the vanishing cross-ratio property" includes the quadruples with `∞` (the proof applies it to
`V(a, b, c, ∞)`, l. 3305), written out as the hypothesis `hvanInf`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane)

/-- Helper for **Lemma 7** (l. 3274, (3.44)). The quantity
`(1/|b − a|) |((z − a)/(b − a) V(b) − (z − b)/(b − a) V(a)) − ((z − c)/(d − c) V(d) − (z − d)/(d − c) V(c))|`: the
difference of the affine interpolations of `V` through `a, b` and through `c, d`, at `z`, scaled by `|b − a|`. -/
def lemma37Expr (V : ℂ → ℂ) (a b c d z : ℂ) : ℝ :=
  ‖((z - a) / (b - a) * V b - (z - b) / (b - a) * V a) - ((z - c) / (d - c) * V d - (z - d) / (d - c) * V c)‖ /
    ‖b - a‖

/-- **Lemma 7** (§3 Appendix, l. 3270), (3.44). If `V` has bounded cross-ratio norm on `Λ ∋ ∞` and vanishes at `∞`,
`a, b, c, d ∈ Λ ∖ {∞}` are distinct and `|z − a|/|b − a|`, `|z − c|/|d − c|`, `|d − c|/|b − a| ≤ M`, then the quantity
(3.44) is at most `C`, `C` depending only on `M` and `‖V‖_cr`. -/
theorem lemma3_7_a (M B : ℝ) :
    ∃ C : ℝ, ∀ (Λ : Set ExtPlane) (V : ℂ → ℂ), (OnePoint.infty : ExtPlane) ∈ Λ → crNorm Λ V ≤ ENNReal.ofReal B →
      (∀ a b c : ℂ, (a : ExtPlane) ∈ Λ → (b : ExtPlane) ∈ Λ → (c : ExtPlane) ∈ Λ → a ≠ b → b ≠ c → a ≠ c →
        ‖crDistortionInf V a b c‖ ≤ B) →
      ∀ a b c d z : ℂ, (a : ExtPlane) ∈ Λ → (b : ExtPlane) ∈ Λ → (c : ExtPlane) ∈ Λ → (d : ExtPlane) ∈ Λ →
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        ‖z - a‖ / ‖b - a‖ ≤ M → ‖z - c‖ / ‖d - c‖ ≤ M → ‖d - c‖ / ‖b - a‖ ≤ M →
          lemma37Expr V a b c d z ≤ C := by
  sorry

/-- **Lemma 7** (§3 Appendix, l. 3278), the vanishing case. If moreover `V` has the vanishing cross-ratio property and
`a, b` tend to the same point of `Λ ∖ {∞}` (with the bounds of (3.44) kept), the quantity (3.44) tends to `0`. -/
theorem lemma3_7_b {Λ : Set ExtPlane} (hinf : (OnePoint.infty : ExtPlane) ∈ Λ) {V : ℂ → ℂ}
    (hvan : HasVanishingCrDistortion Λ V)
    (hvanInf : ∀ (p : ℂ) (a b c : ℕ → ℂ), (p : ExtPlane) ∈ Λ →
      (∀ n, (a n : ExtPlane) ∈ Λ ∧ (b n : ExtPlane) ∈ Λ ∧ (c n : ExtPlane) ∈ Λ) →
      (∀ n, a n ≠ b n ∧ b n ≠ c n ∧ a n ≠ c n) →
      Tendsto a atTop (𝓝 p) → Tendsto b atTop (𝓝 p) → Tendsto c atTop (𝓝 p) →
        Tendsto (fun n => crDistortionInf V (a n) (b n) (c n)) atTop (𝓝 0))
    {M : ℝ} {p : ℂ} (hp : (p : ExtPlane) ∈ Λ) {a b c d z : ℕ → ℂ}
    (hmem : ∀ n, (a n : ExtPlane) ∈ Λ ∧ (b n : ExtPlane) ∈ Λ ∧ (c n : ExtPlane) ∈ Λ ∧ (d n : ExtPlane) ∈ Λ)
    (hdist : ∀ n, a n ≠ b n ∧ a n ≠ c n ∧ a n ≠ d n ∧ b n ≠ c n ∧ b n ≠ d n ∧ c n ≠ d n)
    (hM : ∀ n, ‖z n - a n‖ / ‖b n - a n‖ ≤ M ∧ ‖z n - c n‖ / ‖d n - c n‖ ≤ M ∧ ‖d n - c n‖ / ‖b n - a n‖ ≤ M)
    (ha : Tendsto a atTop (𝓝 p)) (hb : Tendsto b atTop (𝓝 p)) :
    Tendsto (fun n => lemma37Expr V (a n) (b n) (c n) (d n) (z n)) atTop (𝓝 0) := by
  sorry

end GardinerLakic2000
