/-
  Riemann–Roch, first form (Miranda Ch. VI Thm. 3.1, p. 185):

      `l(D) − h¹(D) = deg D + 1 − h¹(0)`,

  where `h¹(D) = dim H¹(D)` is the Laurent-tail (Mittag-Leffler) obstruction dimension and
  `l(D)` the linear-system dimension `lDim`.  Proof: `l(D) − h¹(D) − deg D` is constant in `D` —
  for `D₁ ≤ D₂` this is Lemma 2.3 (`finrank_ker_mittagLefflerTruncate`) plus rank–nullity on
  the (now finite-dimensional, Prop. 2.7) surjection `H¹(D₁) ↠ H¹(D₂)`; an arbitrary pair is
  compared through the common upper bound `D₁ ⊔ D₂`.  Evaluating at `D = 0` (`l(0) = 1`,
  `deg 0 = 0`) gives the theorem.

  This is Riemann–Roch with `h¹` in its Laurent-tail incarnation; Serre duality
  (`h¹(D) = l(K − D)`, Miranda Ch. VI §3) converts it into the
  `exists_riemannRoch_divisor` form.
-/
import Jacobians.LaurentTail.Finiteness

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The **Euler characteristic** `l(D) − h¹(D) − deg D` **is monotone-invariant**: equal for
`D₁ ≤ D₂`.  Lemma 2.3 computes `dim ker (H¹(D₁) ↠ H¹(D₂))`, and rank–nullity on the
finite-dimensional `H¹`s (Prop. 2.7) reads the same kernel as `h¹(D₁) − h¹(D₂)`. -/
theorem lDim_sub_h1TailDim_sub_deg_eq_of_le {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    (lDim (X := X) D₁ : ℤ) - h1TailDim (X := X) D₁ - Divisor.deg X D₁
      = (lDim (X := X) D₂ : ℤ) - h1TailDim (X := X) D₂ - Divisor.deg X D₂ := by
  have hdim := finrank_ker_mittagLefflerTruncate h
  have hrn := LinearMap.finrank_range_add_finrank_ker (mittagLefflerTruncate (X := X) h)
  rw [LinearMap.range_eq_top.mpr (mittagLefflerTruncate_surjective h),
    finrank_top] at hrn
  rw [show h1TailDim (X := X) D₁ = finrank ℂ (mittagLefflerH1 (X := X) D₁) from rfl,
    show h1TailDim (X := X) D₂ = finrank ℂ (mittagLefflerH1 (X := X) D₂) from rfl]
  omega

/-- `l(D) − h¹(D) − deg D` is **constant in `D`** (compare any two divisors through their
common upper bound `D₁ ⊔ D₂`). -/
theorem lDim_sub_h1TailDim_sub_deg_const (D₁ D₂ : Divisor X) :
    (lDim (X := X) D₁ : ℤ) - h1TailDim (X := X) D₁ - Divisor.deg X D₁
      = (lDim (X := X) D₂ : ℤ) - h1TailDim (X := X) D₂ - Divisor.deg X D₂ :=
  (lDim_sub_h1TailDim_sub_deg_eq_of_le (le_sup_left : D₁ ≤ D₁ ⊔ D₂)).trans
    (lDim_sub_h1TailDim_sub_deg_eq_of_le (le_sup_right : D₂ ≤ D₁ ⊔ D₂)).symm

/-- **Riemann–Roch, first form** (Miranda Ch. VI Thm. 3.1, p. 185):

    `l(D) − h¹(D) = deg D + 1 − h¹(0)`

for every divisor `D` on the compact Riemann surface `X`, with `h¹` the Laurent-tail
Mittag-Leffler obstruction dimension. -/
theorem riemannRoch_tailForm (D : Divisor X) :
    (lDim (X := X) D : ℤ) - h1TailDim (X := X) D
      = Divisor.deg X D + 1 - h1TailDim (X := X) 0 := by
  have h := lDim_sub_h1TailDim_sub_deg_const D (0 : Divisor X)
  rw [lDim_zero_eq_one, Divisor.deg_zero] at h
  omega

end Jacobians.LaurentTail
