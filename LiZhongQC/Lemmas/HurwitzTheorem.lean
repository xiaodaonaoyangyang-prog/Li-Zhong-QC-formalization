import LiZhongQC.Lemmas.HurwitzProofChain

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §30.5 (Hurwitz's theorem): a compact Riemann surface of genus `g > 1` has at most `84(g - 1)`
conformal automorphisms.  (The finiteness conjunct stays here: `Set.ncard` of an infinite set is `0` in Lean, so the
bound alone would not say that the automorphism group is finite.  It is also stated on its own as
`hurwitz_finite`.) -/
theorem hurwitz {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.Finite ∧ {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.ncard ≤ 84 * (g - 1) := by
  classical
  have hfin := hurwitz_finite hg hS
  let A : Subgroup (S₀ ≃ₜ S₀) :=
    { carrier := {φ | IsBiholomorphic φ}
      one_mem' := by
        change IsBiholomorphic (id : S₀ → S₀)
        exact ⟨mdifferentiable_id, id, mdifferentiable_id, fun _ => rfl, fun _ => rfl⟩
      mul_mem' := by
        intro φ ψ hφ hψ
        change IsBiholomorphic ((φ : S₀ → S₀) ∘ (ψ : S₀ → S₀))
        exact IsBiholomorphic.comp (h := (φ : S₀ → S₀)) (f := (ψ : S₀ → S₀)) hφ hψ
      inv_mem' := by
        intro φ hφ
        exact IsBiholomorphic.homeomorph_symm hφ }
  letI : Fintype A := hfin.fintype
  have hHol : ∀ a : A, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (A.subtype a) := by
    intro a
    exact k22u_mdifferentiable_contMDiff a.property.1
  have hgenus : genus S₀ = g := k22rr_genus_eq hS
  have hgA : 1 < genus S₀ := by rw [hgenus]; exact hg
  have hbound := h77d_finite_analytic_action_bound A.subtype Subtype.val_injective hHol hgA
  rw [hgenus] at hbound
  refine ⟨hfin, ?_⟩
  change Nat.card A ≤ 84 * (g - 1)
  exact hbound

end LiZhongQC
