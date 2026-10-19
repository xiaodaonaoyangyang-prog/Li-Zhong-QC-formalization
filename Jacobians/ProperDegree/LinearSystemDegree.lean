/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Degree consequences for linear systems: `deg_div` and negative-degree vanishing

The two residue-theorem consequences that sit *below* Riemann–Roch:

* `MeromorphicFunction.deg_div` — every principal divisor has degree `0` (Forster Cor. 4.25 /
  the argument principle), via the proven proper-map degree route.
* `lDim_eq_zero_of_deg_neg` — a linear system of negative degree is trivial.

Extracted from `Jacobians/RiemannRoch.lean` so the Laurent-tail duality ladder
(`Jacobians/LaurentTail/*`) can be imported by `RiemannRoch.lean` without an import cycle.
-/
import Jacobians.ProperDegree.ProperMapDegreeSheets

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Every principal divisor has degree `0` (Forster Cor. 4.25 / the argument principle),
via the **degree route**: `deg (div f) = zerosCount f − polesCount f`, and both counts equal a
common proper-map degree `d` (conservation of number), so the difference is `0`. -/
theorem MeromorphicFunction.deg_div (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  obtain ⟨d, hz, hp⟩ := Jacobians.ProperMapDegreeSheets.exists_properMapDegree_proven f
  rw [deg_div_eq_zeros_sub_poles, hz, hp, sub_self]

/-- `l(D) = 0` when `deg D < 0`. Any `f ∈ L(D)` with nonzero germ would give (by faithfulness) a
divisor `div f ≥ −D` with `deg(div f) = 0 ≥ −deg D > 0`, impossible; so every `f ∈ L(D)` is germ-
zero, the quotient `L(D)/germZero` is trivial, and its dimension is `0`. -/
theorem lDim_eq_zero_of_deg_neg (D : Divisor X) (hD : Divisor.deg X D < 0) :
    lDim (X := X) D = 0 := by
  have hsub : linearSystem (X := X) D ≤ germZeroSubmodule := by
    intro f hf
    by_contra hng
    have hex : ∃ x₀, f.orderW x₀ ≠ ⊤ := by
      by_contra h; push Not at h; exact hng h
    have hfaith : ∀ z : X, f.orderW z ≠ ⊤ := fun z =>
      MeromorphicFunction.orderW_ne_top_of_exists f hex z
    have hdiv : ∀ x, -(D x) ≤ (f.div : Divisor X) x := by
      intro x
      have hmem : (-(D x) : WithTop ℤ) ≤ f.orderW x := hf x
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfaith x)
      rw [← hn] at hmem
      have hdivx : (f.div : Divisor X) x = n := by
        show (f.orderW x).untop₀ = n
        rw [← hn]; rfl
      rw [hdivx]; exact WithTop.coe_le_coe.mp hmem
    have heff : ∀ x, 0 ≤ (f.div + D) x := fun x => by
      rw [Finsupp.add_apply]; linarith [hdiv x]
    have hdeg_eff : (0 : ℤ) ≤ Divisor.deg X (f.div + D) := by
      change (0 : ℤ) ≤ ∑ i ∈ (f.div + D).support, (f.div + D) i
      exact Finset.sum_nonneg fun i _ => heff i
    rw [map_add, MeromorphicFunction.deg_div f] at hdeg_eff
    omega
  rw [lDim]
  have htop : (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr hsub
  rw [htop]
  haveI : Subsingleton (↥(linearSystem (X := X) D) ⧸
      (⊤ : Submodule ℂ ↥(linearSystem (X := X) D))) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
      (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top⟩
  exact Module.finrank_zero_of_subsingleton

end Jacobians
