/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The dimension count `h¹(𝔘, 𝒪) = genus X` (Forster 19.x / Miranda Ch. X §2)

The key step of the Abel-converse route: the Čech `H¹` of the structure sheaf on any locally
realizable finite cover has dimension exactly the genus.

*Proof (vanishing at a large divisor + the two Riemann–Rochs).*

1. **`H¹(𝒪_A) = 0` for a suitable effective `A`.**  Pick a basis of the finite-dimensional
   `H¹(𝒪)`; the kill lemma (`exists_effective_h1Incl_eq_zero`, the cup-multiplication
   pigeonhole) provides an effective `Aᵢ` killing the `i`-th basis class.  For
   `A := ∑ᵢ Aᵢ + m·P` (any `m ≥ 0`) every basis class dies in `H¹(𝒪_A)` (functoriality
   `h1Incl_comp`), so the inclusion-induced map `H¹(𝒪) → H¹(𝒪_A)` is zero — and it is also
   **surjective** (`h1Incl_surjective`, Forster 16.8 via the skyscraper LES).  Hence
   `H¹(𝒪_A) = 0`.
2. **Tail vanishing.**  Choosing `m > deg K` for the pair-frame canonical divisor
   `K = div (dg₀)` makes `deg (K − A) < 0`, so by tail Serre duality
   (`h1TailDim_eq_lDim_pairCanonical_sub`, Miranda VI.3.3) the Laurent-tail obstruction also
   vanishes: `h¹_tail(A) = l(K − A) = 0`.
3. **Subtract the two Riemann–Rochs at `A`.**  Cohomological RR (`cohomological_riemannRoch`,
   the skyscraper-χ induction) gives `l(A) = deg A + 1 − h¹(0)` and tail RR
   (`riemannRoch_tailForm` + `h1TailDim_zero_eq_genus_unconditional`, Miranda VI.3.1/3.11)
   gives `l(A) = deg A + 1 − g`; hence `h¹(0) = g`.

This is Miranda's Proposition X.2.6 (`dim H¹(X, 𝒪) = g`, p. 316) — proven here without GAGA:
the Zariski/algebraic detour is replaced by the kill lemma on the fixed analytic cover.

References: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. X §2 (pp. 313–316);
Forster, *Lectures on Riemann Surfaces* (GTM 81), §16.
-/
import Jacobians.H1Genus.CechH1CupKill
import Jacobians.TailDuality.RiemannRochUnconditional

open scoped Manifold ContDiff Topology
open Module


namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`H¹(𝔘, 𝒪_A)` vanishes for a suitable effective `A` of arbitrarily large degree** —
step 1 of the dimension count: kill a basis of `H¹(𝒪)` with the cup-multiplication lemma, then
use surjectivity of the inclusion-induced map (Forster 16.8). The lower-degree parameter `m`
adds `m·P` to push `deg A` past any prescribed bound. -/
theorem exists_effective_h1Dim_eq_zero (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (m : ℕ) :
    ∃ A : Divisor X, 0 ≤ A ∧ (m : ℤ) ≤ Divisor.deg X A ∧ 𝔘.h1Dim A = 0 := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  haveI := finiteDimensional_cechH1_general 𝔘 (0 : Divisor X)
  -- a basis of H¹(𝒪) and a killing divisor for each basis class.
  set b := Module.finBasis ℂ (𝔘.cechH1 (0 : Divisor X)) with hb
  choose Ak hAk hAkzero using fun i => exists_effective_h1Incl_eq_zero 𝔘 hR (b i)
  -- the total divisor.
  set A : Divisor X := (∑ i, Ak i) + Finsupp.single P (m : ℤ) with hA
  -- effectivity and degree bookkeeping.
  have hsum_nonneg : ∀ x, (0 : ℤ) ≤ (∑ i, Ak i) x := by
    intro x
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun i _ => by
      have := Finsupp.le_def.mp (hAk i) x
      simpa using this
  have h0A : (0 : Divisor X) ≤ A := by
    rw [Finsupp.le_def]
    intro x
    rw [Finsupp.coe_zero, Pi.zero_apply, hA, Finsupp.add_apply, Finsupp.single_apply]
    have := hsum_nonneg x
    by_cases hPx : P = x
    · rw [if_pos hPx]; omega
    · rw [if_neg hPx]; omega
  have hAk_le : ∀ i, Ak i ≤ A := by
    intro i
    rw [Finsupp.le_def]
    intro x
    rw [hA, Finsupp.add_apply, Finsupp.single_apply, Finsupp.finsetSum_apply]
    have hle : Ak i x ≤ ∑ j, Ak j x := by
      refine Finset.single_le_sum (f := fun j => Ak j x) (fun j _ => ?_) (Finset.mem_univ i)
      have := Finsupp.le_def.mp (hAk j) x
      simpa using this
    by_cases hPx : P = x
    · rw [if_pos hPx]; omega
    · rw [if_neg hPx]; omega
  have hdegA : (m : ℤ) ≤ Divisor.deg X A := by
    rw [hA, Divisor.deg_add, Divisor.deg_single]
    have hdegsum : (0 : ℤ) ≤ Divisor.deg X (∑ i, Ak i) := by
      refine FiniteCover.deg_nonneg_of_effective ?_
      rw [Finsupp.le_def]
      intro x
      rw [Finsupp.coe_zero, Pi.zero_apply]
      exact hsum_nonneg x
    omega
  -- every basis class dies in H¹(𝒪_A) (functoriality through Ak i ≤ A).
  have himg : ∀ i, 𝔘.h1Incl h0A (b i) = 0 := by
    intro i
    have hcomp := 𝔘.h1Incl_comp (hAk i) (hAk_le i) (b i)
    rw [hAkzero i, map_zero] at hcomp
    exact hcomp.symm
  -- the inclusion-induced map is zero on a basis, hence zero; and it is surjective.
  have hmap : 𝔘.h1Incl h0A = 0 := b.ext fun i => by rw [himg i]; rfl
  have hall : ∀ y : 𝔘.cechH1 A, y = 0 := by
    intro y
    obtain ⟨ξ, rfl⟩ := 𝔘.h1Incl_surjective hR h0A y
    rw [hmap]
    rfl
  haveI hsub : Subsingleton (𝔘.cechH1 A) := ⟨fun y z => by rw [hall y, hall z]⟩
  exact ⟨A, h0A, hdegA, Module.finrank_zero_iff.mpr hsub⟩

/-- **The dimension count `h¹(𝔘, 𝒪) = genus X`** (Miranda Prop. X.2.6 / the `D = 0` Dolbeault
anchor, GAGA-free): on any locally realizable finite cover, the Čech `H¹` of the structure
sheaf has dimension the genus.  Proven by vanishing at a large effective `A`
(`exists_effective_h1Dim_eq_zero` Čech-side, tail Serre duality tail-side) and subtracting
cohomological Riemann–Roch from tail Riemann–Roch at `A`. -/
theorem FiniteCover.h1Dim_zero_eq_genus (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable) :
    𝔘.h1Dim 0 = genus X := by
  classical
  -- the pair-frame canonical divisor.
  obtain ⟨D₀, g₀, _hmem, hg₀⟩ := exists_nonconstant_meromorphic (X := X)
  set Kc : Divisor X := Jacobians.LaurentTail.pairCanonicalDivisor g₀ hg₀ with hKc
  -- the Čech-vanishing divisor, of degree > deg Kc.
  obtain ⟨A, _h0A, hdegA, h1A⟩ :=
    exists_effective_h1Dim_eq_zero 𝔘 hR ((Divisor.deg X Kc).toNat + 1)
  -- tail vanishing at A: h¹_tail(A) = l(Kc − A) = 0 since deg (Kc − A) < 0.
  have hTA : Jacobians.LaurentTail.h1TailDim (X := X) A = 0 := by
    rw [Jacobians.LaurentTail.h1TailDim_eq_lDim_pairCanonical_sub g₀ hg₀ A]
    refine lDim_eq_zero_of_deg_neg _ ?_
    rw [Divisor.deg_sub]
    have htop : Divisor.deg X Kc ≤ ((Divisor.deg X Kc).toNat : ℤ) := Int.self_le_toNat _
    rw [← hKc] at *
    omega
  -- the two Riemann–Rochs at A.
  have hC := cohomological_riemannRoch 𝔘 hR A
  rw [𝔘.h0Dim_eq_lDim A, h1A] at hC
  have hT := Jacobians.LaurentTail.riemannRoch_tailForm (X := X) A
  rw [hTA, Jacobians.LaurentTail.h1TailDim_zero_eq_genus_unconditional] at hT
  omega

end Jacobians.Dolbeault
