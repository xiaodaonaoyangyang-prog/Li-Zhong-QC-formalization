/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Riemann–Roch, unconditional (Miranda Ch. VI Thm 3.11 / Forster 16.9 — every genus)

The Miranda-route final assembly in the meromorphic pair frame, combining

* **RR-I** `riemannRoch_tailForm` (`l(D) − h¹(D) = deg D + 1 − h¹(0)`),
* **Serre duality for the tail `H¹`** `h1TailDim_eq_lDim_pairCanonical_sub`
  (`h¹(D) = l(K − D)`, `K = div (dg₀)` — every genus, by the genus-free residue theorem), and
* **`l(K) = genus`** — the Forster §17.4 canonical-form isomorphism
  (`hKgenus_unconditional`), applied to the datum `ω₀ = dg₀`,
  `K = pairCanonicalDivisor g₀ hg₀` (the divisor is the form divisor of `dg₀` by
  construction),

into the headline `l(D) − l(K − D) = deg D + 1 − g` for every divisor `D`, with `g₀` the
nonconstant meromorphic function of `exists_nonconstant_meromorphic`.  Unlike the genus ≥ 1
assembly (`RiemannRochGenusPos`), nothing here needs a nonzero *holomorphic* 1-form, so there
is no genus hypothesis — this is the exact statement shape of
`Jacobians.exists_riemannRoch_divisor`, which it discharges.
-/
import Jacobians.TailDuality.PairDualitySurjective
import Jacobians.CanonicalForms.FormRemovableSingularity

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 `l(K) = genus` for the pair-frame canonical divisor -/

/-- **`l(K) = genus`** for the pair-frame canonical divisor `K = div (dg₀)` (Forster §17.4 at
`D = 0`): `pairCanonicalDivisor` is by construction the form divisor of the §17.4 datum
`ω₀ = dg₀`. -/
theorem lDim_pairCanonicalDivisor_eq_genus (g₀ : MeromorphicFunction X)
    (hg₀ : ¬ IsGermConstant g₀) :
    lDim (X := X) (pairCanonicalDivisor g₀ hg₀) = genus X :=
  (canonicalForm17DataOfDivisor g₀ hg₀ (pairCanonicalDivisor g₀ hg₀)
    (formOrderW_pairCanonicalDivisor g₀ hg₀)).hKgenus_unconditional

/-! ### §2 The three-genera identity and Riemann–Roch -/

/-- **`h¹(0) = genus`** (Miranda's "three genera", arithmetic = analytic) — every genus: Serre
duality at `D = 0` reads `h¹(0) = l(K)`, and `l(K) = genus` by §17.4. -/
theorem h1TailDim_zero_eq_genus_unconditional : h1TailDim (X := X) 0 = genus X := by
  obtain ⟨_D, g₀, _hmem, hg₀⟩ := exists_nonconstant_meromorphic (X := X)
  rw [h1TailDim_eq_lDim_pairCanonical_sub g₀ hg₀ 0, sub_zero,
    lDim_pairCanonicalDivisor_eq_genus g₀ hg₀]

/-- **Riemann–Roch, unconditional** (Forster Thm 16.9 / Miranda Ch. VI Thm 3.11): a canonical
divisor `K` with `l(D) − l(K−D) = deg D + 1 − g` for every divisor `D` — every genus.  This is
the exact statement shape of `Jacobians.exists_riemannRoch_divisor`. -/
theorem exists_riemannRoch_divisor_unconditional :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (genus X : ℤ) := by
  obtain ⟨_D, g₀, _hmem, hg₀⟩ := exists_nonconstant_meromorphic (X := X)
  refine ⟨pairCanonicalDivisor g₀ hg₀, fun D => ?_⟩
  have hRR := riemannRoch_tailForm (X := X) D
  rw [h1TailDim_eq_lDim_pairCanonical_sub g₀ hg₀ D, h1TailDim_zero_eq_genus_unconditional] at hRR
  omega

end Jacobians.LaurentTail
