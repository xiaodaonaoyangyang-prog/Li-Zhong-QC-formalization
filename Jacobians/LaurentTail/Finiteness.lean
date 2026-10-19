/-
  Finite-dimensionality of the Mittag-Leffler obstruction spaces `H¹(D)` (Miranda Ch. VI §2,
  Lemmas 2.5–2.7, pp. 182–184), with Miranda's algebraicity input replaced by the
  Riemann–Roch inequality.

  * **M-bound** (`exists_deg_sub_lDim_bound`): `deg A − l(A) ≤ M` uniformly in `A` — Miranda
    gets this from Lemmas 1.18/2.4–2.5 (the only use of algebraicity in his Ch. VI); here it
    falls out of `riemannRoch_inequality` over a realizable Leray cover, with
    `M = h¹_Čech(0) − 1`.
  * **Maximizer** (`exists_maximizer`): the integers `deg A − l(A)` are bounded above and
    nonempty, so some `A₀` attains the maximum (`Int.exists_greatest_of_bdd`).
  * **Miranda Lemma 2.6** (`mittagLefflerH1_subsingleton_of_maximizer`): `H¹(A₀) = 0` — any
    tail `Z` dies under a deep enough truncation (`tailCutoff`), so its class lies in a relative
    kernel of dimension `(deg B − l(B)) − (deg A₀ − l(A₀)) ≤ 0` by maximality.
  * **Miranda Prop. 2.7** (`instFiniteDimensionalMittagLefflerH1`): `H¹(D)` is finite-
    dimensional for *every* `D`: with `E := A₀ ⊓ D`, `H¹(E)` equals the (finite-dimensional)
    relative kernel of `H¹(E) → H¹(A₀) = 0`, and `H¹(E) ↠ H¹(D)` by surjectivity of the
    induced truncation.
-/
import Jacobians.CanonicalForms.SerreOmega0
import Jacobians.LaurentTail.DimensionBookkeeping

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The uniform bound and its maximizer -/

/-- **The M-bound**: `deg A − l(A)` is bounded above, uniformly in the divisor `A`.  This is
the Riemann–Roch inequality (`deg A + 1 − h¹(0) ≤ l(A)` over a locally-realizable cover),
substituting for Miranda's algebraicity Lemmas 1.18/2.4–2.5. -/
theorem exists_deg_sub_lDim_bound :
    ∃ M : ℤ, ∀ A : Divisor X, Divisor.deg X A - (lDim (X := X) A : ℤ) ≤ M := by
  obtain ⟨𝔘, _, hR⟩ := exists_realizableLerayCover (X := X)
  refine ⟨(𝔘.h1Dim 0 : ℤ) - 1, fun A => ?_⟩
  have h := riemannRoch_inequality hR A
  linarith

/-- A divisor `A₀` **maximizing `deg − l`** exists (a nonempty, bounded-above set of integers
attains its supremum). -/
theorem exists_maximizer :
    ∃ A₀ : Divisor X, ∀ A : Divisor X,
      Divisor.deg X A - (lDim (X := X) A : ℤ)
        ≤ Divisor.deg X A₀ - (lDim (X := X) A₀ : ℤ) := by
  obtain ⟨M, hM⟩ := exists_deg_sub_lDim_bound (X := X)
  obtain ⟨z₀, ⟨A₀, hA₀⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ A : Divisor X, Divisor.deg X A - (lDim (X := X) A : ℤ) = z)
    ⟨M, fun z ⟨A, hA⟩ => hA ▸ hM A⟩
    ⟨Divisor.deg X (0 : Divisor X) - (lDim (X := X) 0 : ℤ), 0, rfl⟩
  exact ⟨A₀, fun A => hA₀ ▸ hmax _ ⟨A, rfl⟩⟩

/-! ### Miranda Lemma 2.6: the maximizer kills the obstruction space -/

/-- **Miranda Lemma 2.6** (Ch. VI §2, p. 183): at a maximizer `A₀` of `deg − l`, every Laurent
tail divisor is realized by a global meromorphic function — `H¹(A₀) = 0`.  Proof: a given tail
`Z` truncates to `0` in `𝒯[B]` for the deep cutoff `B = tailCutoff A₀ Z ≥ A₀`, so its class
lies in `ker (H¹(A₀) → H¹(B))`, whose dimension `(deg B − l(B)) − (deg A₀ − l(A₀))` is `≤ 0`
by maximality. -/
theorem mittagLefflerH1_subsingleton_of_maximizer {A₀ : Divisor X}
    (hmax : ∀ A : Divisor X, Divisor.deg X A - (lDim (X := X) A : ℤ)
      ≤ Divisor.deg X A₀ - (lDim (X := X) A₀ : ℤ)) :
    Subsingleton (mittagLefflerH1 (X := X) A₀) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro Z
  set B := tailCutoff A₀ (Z : TailSpace X) with hB
  have hAB : A₀ ≤ B := le_tailCutoff A₀ _
  -- the class of `Z` lies in the relative kernel for `A₀ ≤ B`
  have hker : (Submodule.Quotient.mk Z : mittagLefflerH1 (X := X) A₀)
      ∈ LinearMap.ker (mittagLefflerTruncate hAB) := by
    rw [LinearMap.mem_ker, mittagLefflerTruncate_mk]
    have hZ0 : tailTruncate A₀ B Z = 0 := by
      apply Subtype.ext
      rw [tailTruncate_coe]
      exact truncateRaw_tailCutoff A₀ (Z : TailSpace X)
    rw [hZ0]
    exact Submodule.Quotient.mk_zero _
  -- the relative kernel is trivial: its dimension is `≤ 0` by maximality
  haveI := finiteDimensional_ker_mittagLefflerTruncate hAB
  have hdim := finrank_ker_mittagLefflerTruncate hAB
  have h0 : finrank ℂ ↥(LinearMap.ker (mittagLefflerTruncate (X := X) hAB)) = 0 := by
    have := hmax B
    omega
  have hbot : LinearMap.ker (mittagLefflerTruncate (X := X) hAB) = ⊥ := by
    haveI : Subsingleton ↥(LinearMap.ker (mittagLefflerTruncate (X := X) hAB)) :=
      finrank_zero_iff.mp h0
    exact Submodule.eq_bot_of_subsingleton
  rw [hbot, Submodule.mem_bot] at hker
  rwa [Submodule.Quotient.mk_eq_zero] at hker

/-! ### Miranda Prop. 2.7: `H¹(D)` is finite-dimensional for every `D` -/

/-- **Miranda Prop. 2.7** (Ch. VI §2, p. 184): `H¹(D)` is finite-dimensional for every divisor.
With `E := A₀ ⊓ D`: `H¹(E)` *is* its relative kernel against `H¹(A₀) = 0` (finite by Lemma
2.3), and the truncation `H¹(E) ↠ H¹(D)` is surjective. -/
instance instFiniteDimensionalMittagLefflerH1 (D : Divisor X) :
    FiniteDimensional ℂ (mittagLefflerH1 (X := X) D) := by
  obtain ⟨A₀, hmax⟩ := exists_maximizer (X := X)
  haveI hSub := mittagLefflerH1_subsingleton_of_maximizer hmax
  have hEA : A₀ ⊓ D ≤ A₀ := inf_le_left
  have hED : A₀ ⊓ D ≤ D := inf_le_right
  -- the relative kernel against the trivial `H¹(A₀)` is everything
  have hker : LinearMap.ker (mittagLefflerTruncate (X := X) hEA) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  haveI hfinE : FiniteDimensional ℂ (mittagLefflerH1 (X := X) (A₀ ⊓ D)) := by
    have hfin := finiteDimensional_ker_mittagLefflerTruncate hEA
    rw [hker] at hfin
    exact Module.Finite.equiv (Submodule.topEquiv)
  exact Module.Finite.of_surjective (mittagLefflerTruncate hED)
    (mittagLefflerTruncate_surjective hED)

end Jacobians.LaurentTail
