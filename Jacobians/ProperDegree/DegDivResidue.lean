/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Meromorphic.Abel
/-!
# Degree-route arithmetic for `deg_div`

Helper lemmas for the residue theorem `MeromorphicFunction.deg_div` (every
principal divisor on a compact Riemann surface has degree `0`, Forster Cor.
4.25), which lives in `Jacobians.RiemannRoch`.

The degree route writes `deg (div f) = zerosCount f - polesCount f` (pure
`Finset` book-keeping), where `zerosCount` and `polesCount` count zeros and
poles with multiplicity.  Both equal a common proper-map degree `d`
(conservation of number), so the difference is `0`.

## References

* Forster, *Lectures on Riemann Surfaces*, §§4 (the degree), Cor. 4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset

namespace Jacobians


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The order function on the divisor support

`f.div` is `Finsupp.ofSupportFinite (orderAtPoint f) _`, so its value at `x` is
`orderAtPoint f x` and its degree is `∑_{x ∈ support} orderAtPoint f x`.  We
record the value lemma and the degree-as-support-sum identity. -/

/-- The value of `f.div` at `x` is `orderAtPoint f x`. -/
@[simp] lemma div_apply (f : MeromorphicFunction X) (x : X) :
    (f.div : Divisor X) x = f.orderAtPoint x := rfl

/-- The degree of `f.div` is the support sum of the order function. -/
lemma deg_div_eq_support_sum (f : MeromorphicFunction X) :
    Divisor.deg X f.div = ∑ x ∈ (f.div : Divisor X).support, f.orderAtPoint x := by
  show Finsupp.degree (f.div : Divisor X) = _
  rw [Finsupp.degree_apply]
  exact Finset.sum_congr rfl (fun x _ => div_apply f x)

/-! ### Splitting the support sum into zeros and poles

On the support, the order is nonzero, so each point is either a **zero**
(`0 < order`) or a **pole** (`order < 0`).  We split the support sum
accordingly. -/

/-- The support sum splits as the zero-part plus the pole-part. -/
lemma deg_div_eq_zeros_add_poles (f : MeromorphicFunction X) :
    Divisor.deg X f.div =
      (∑ x ∈ (f.div : Divisor X).support with 0 < f.orderAtPoint x, f.orderAtPoint x)
      + (∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, f.orderAtPoint x) := by
  classical
  rw [deg_div_eq_support_sum]
  rw [← Finset.sum_filter_add_sum_filter_not (f.div : Divisor X).support
    (fun x => 0 < f.orderAtPoint x) f.orderAtPoint]
  congr 1
  -- On the support, `order ≠ 0`, so `¬ (0 < order)` ↔ `order < 0`.
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, div_apply]
  constructor
  · rintro ⟨hx, hnpos⟩
    exact ⟨hx, lt_of_le_of_ne (not_lt.mp hnpos) hx⟩
  · rintro ⟨hx, hneg⟩
    exact ⟨hx, not_lt.mpr hneg.le⟩

/-! ### Zeros, poles, and the proper-map degree

`zerosCount f` is the number of zeros of `f` counted with multiplicity (the sum
of the *positive* orders), `polesCount f` the number of poles counted with
multiplicity (the sum of the *absolute values* of the negative orders).  Both
are `≥ 0` by construction. -/

/-- The number of **zeros** of `f`, counted with multiplicity: the sum of the
positive orders over the divisor support. -/
def zerosCount (f : MeromorphicFunction X) : ℤ :=
  ∑ x ∈ (f.div : Divisor X).support with 0 < f.orderAtPoint x, f.orderAtPoint x

/-- The number of **poles** of `f`, counted with multiplicity: the sum of the
absolute values of the negative orders over the divisor support. -/
def polesCount (f : MeromorphicFunction X) : ℤ :=
  ∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, (-f.orderAtPoint x)

/-- The pole-part of the support sum is `−polesCount`. -/
lemma poles_part_eq_neg_polesCount (f : MeromorphicFunction X) :
    (∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, f.orderAtPoint x)
      = -polesCount f := by
  rw [polesCount, ← Finset.sum_neg_distrib]
  simp

/-- `deg (div f) = zerosCount f − polesCount f`: the divisor degree is the
number of zeros minus the number of poles, each with multiplicity. -/
lemma deg_div_eq_zeros_sub_poles (f : MeromorphicFunction X) :
    Divisor.deg X f.div = zerosCount f - polesCount f := by
  rw [deg_div_eq_zeros_add_poles, poles_part_eq_neg_polesCount, ← sub_eq_add_neg]
  rfl

/-! ### Nonnegativity of the two counts, and the reduction to `zerosCount = polesCount`

Both `zerosCount f` and `polesCount f` are sums of *nonnegative* integers (the
positive orders, resp. the absolute values of the negative orders), so both are
`≥ 0`.  Consequently the proper-map-degree existential (a single `d : ℕ`
with `zerosCount f = d = polesCount f`) is **equivalent** to the bare equality
`zerosCount f = polesCount f`: given the equality, both sides are a common
nonnegative integer, which is the cast of some `d : ℕ`.  This isolates the analytic content as the
**argument-principle equality** `zerosCount f = polesCount f`
(Forster Cor. 4.25), stripping away the `∃ d : ℕ` packaging. -/

/-- `zerosCount f ≥ 0`: it is a sum of positive orders. -/
lemma zerosCount_nonneg (f : MeromorphicFunction X) : 0 ≤ zerosCount f := by
  rw [zerosCount]
  apply Finset.sum_nonneg
  intro x hx
  rw [Finset.mem_filter] at hx
  exact hx.2.le

/-- **Reduction to the argument-principle equality.**
Since both counts are nonnegative (`zerosCount_nonneg`, `polesCount_nonneg`), the
existence of a common natural-number degree `d` with `zerosCount f = d` and
`polesCount f = d` is exactly the equality `zerosCount f = polesCount f`.  The
common `d` is the natural number whose cast is the (nonnegative) shared value. -/
theorem exists_properMapDegree_of_zerosCount_eq_polesCount (f : MeromorphicFunction X)
    (h : zerosCount f = polesCount f) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (zerosCount_nonneg f)
  exact ⟨d, hd, h ▸ hd⟩

/-- The degree-route conclusion in the trivial case `f.div = 0` (constant or
germ-zero `f`): both counts vanish, witnessed by `d = 0`. -/
theorem exists_properMapDegree_of_div_eq_zero (f : MeromorphicFunction X)
    (h : (f.div : Divisor X) = 0) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  refine ⟨0, ?_, ?_⟩
  · simp only [zerosCount, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h] at hx
    simp at hx
  · simp only [polesCount, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h] at hx
    simp at hx

end Jacobians
