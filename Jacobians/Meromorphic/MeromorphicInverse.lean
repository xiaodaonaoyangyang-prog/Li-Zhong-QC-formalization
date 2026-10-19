/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Meromorphic.LinearSystem

/-!
# The reciprocal `f⁻¹` of a meromorphic function

A meromorphic function has a meromorphic pointwise reciprocal (Mathlib `MeromorphicAt.inv`), with
the order negated at every point (`orderW_inv`/`orderAtPoint_inv`). This is the algebraic step
behind Miranda's simple-`∞` reduction (Miranda §VIII.3 p. 254): for a generic value `a`, the
reciprocal `f' := (f₀ − a·1)⁻¹` has its `∞`-poles exactly at the *zeros* of `f₀ − a`, which are
**simple** when `a` is not a critical value of `f₀` (so `orderAtPoint f' = −1` there).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* Mathlib `MeromorphicAt.inv`, `meromorphicOrderAt_inv`.
-/

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace MeromorphicFunction

-- The reciprocal uses only the charted-space structure (no compactness/connectedness), matching the
-- footprint of the other `MeromorphicFunction` algebra (so it applies to open submanifolds `↥U`
-- too).

/-- The pointwise reciprocal of a meromorphic function is meromorphic (Mathlib `MeromorphicAt.inv`,
applied in each chart — composition with the chart inverse commutes with pointwise `⁻¹`). -/
theorem _root_.Jacobians.IsMeromorphic.inv {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X f⁻¹ := fun x => by
  have h := (hf x).inv
  -- `(f ∘ chart.symm)⁻¹ = f⁻¹ ∘ chart.symm` (pointwise reciprocal commutes with composition).
  have heq : (f ∘ (chartAt (H := ℂ) x).symm)⁻¹ = (f⁻¹ ∘ (chartAt (H := ℂ) x).symm) := rfl
  rwa [heq] at h

/-- The reciprocal `f⁻¹` of a meromorphic function — `(f⁻¹).toFun = f.toFun⁻¹` (pointwise). -/
noncomputable instance : Inv (MeromorphicFunction X) :=
  ⟨fun f => ⟨f.toFun⁻¹, IsMeromorphic.inv f.meromorphic⟩⟩

@[simp] theorem inv_toFun (f : MeromorphicFunction X) : (f⁻¹).toFun = f.toFun⁻¹ := rfl

/-- **The germ-order of a reciprocal is the negation:** `(f⁻¹).orderW x = −(f.orderW x)` (Mathlib
`meromorphicOrderAt_inv`, read in the chart at `x`).  A pole of order `n` of `f` becomes a zero of
order `n` of `f⁻¹` and vice versa. -/
theorem orderW_inv (f : MeromorphicFunction X) (x : X) :
    (f⁻¹).orderW x = -(f.orderW x) := by
  show meromorphicOrderAt ((f.toFun⁻¹) ∘ (chartAt (H := ℂ) x).symm) _
    = -meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) _
  have heq : (f.toFun⁻¹) ∘ (chartAt (H := ℂ) x).symm
      = (f.toFun ∘ (chartAt (H := ℂ) x).symm)⁻¹ := rfl
  rw [heq, meromorphicOrderAt_inv]

end MeromorphicFunction

end Jacobians
