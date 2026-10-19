import References.GardinerLakic2000.Ch02.S09_FundamentalDomains

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.10 Dimension of quadratic differentials

Source `teichmuller.txt`, lines 1927–1958 (Chapter 2, §2.10).

* Definition (the space `A(R)` of holomorphic quadratic differentials of a surface of type `(g, m, n)`: real on the
  border, at most simple poles at the punctures, l. 1928–1930) — exists: `LiZhongQC.admissibleQDSpace` (Li Zhong's
  admissible differentials of a surface of type (g, n, m) — the order of m and n is swapped there)
* Theorem 4 (l. 1932), the generic case `dim_ℝ A(R) = 6g − 6 + 3m + 2n` — exists:
  `LiZhongQC.thm31_1_admissibleQD_finrank` (non-exceptional types)
* Theorem 4 (l. 1937–1948), the exceptional table — `thm2_4_b`
* Theorem 4 (l. 1950–1956), `m = 0`: `dim_ℂ A(R) = 3g − 3 + n` — `thm2_4_c`

Modelling: the book's `(g, m, n)` (genus, discs, points) is the project's `(g, n, m)` (genus, points, discs). The
book's table lists the types where the formula fails. [CORRECTION, book error, AUDIT4 G12: the table omits the annulus `(g, m, n) = (0, 2, 0)`,
project type `(0, 0, 2)`. There `A(R)` is spanned by `dz²/z²` (`z² φ` real on both circles forces only the constant Laurent coefficient), so
`dim_ℝ A(R) = 1`, while the formula gives `0`. The project's `LiZhongQC.IsExceptionalType` excludes `(0, 0, 2)`, so `thm31_1` says nothing about
it; no statement of this file asserts the false value.]
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (FiniteTypeStructure admissibleQDSpace)

/-- **Theorem 4** (§2.10, l. 1937–1948), the table: for `(g, m, n) = (0, 0, n ≤ 2)` and `(0, 1, n ≤ 1)` the dimension
is `0`, for `(1, 0, 0)` it is `2`. (Project order `(g, n, m)`.) -/
theorem thm2_4_b {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (g = 0 ∧ m = 0 ∧ n ≤ 2 → Module.finrank ℝ (admissibleQDSpace F) = 0) ∧
      (g = 0 ∧ m = 1 ∧ n ≤ 1 → Module.finrank ℝ (admissibleQDSpace F) = 0) ∧
      (g = 1 ∧ m = 0 ∧ n = 0 → Module.finrank ℝ (admissibleQDSpace F) = 2) := by
  sorry

/-- **Theorem 4** (§2.10, l. 1950–1956). For `m = 0`, `A(R)` is a complex vector space and
`dim_ℂ A(R) = 3g − 3 + n` for `g ≥ 2`, for `g = 1`, `n ≥ 1`, and for `g = 0`, `n ≥ 3`. -/
theorem thm2_4_c {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (F : FiniteTypeStructure S g n 0)
    (hgn : 2 ≤ g ∨ (g = 1 ∧ 1 ≤ n) ∨ (g = 0 ∧ 3 ≤ n)) :
    (Module.finrank ℂ (Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ))) : ℤ) =
      3 * g - 3 + n := by
  sorry

end GardinerLakic2000
